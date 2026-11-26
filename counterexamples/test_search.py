"""Regression tests for the bounded cycle search and its emitted proof witnesses."""

import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import search


CATALOG = json.loads((search.HERE / "catalog.json").read_text(encoding="utf-8"))


def brute_force_burning_number(n):
    """Breadth-first search over burned vertex sets, independent of block schedules."""
    full = (1 << n) - 1
    states = {0}
    for rounds in range(1, n + 1):
        following = set()
        for seen in states:
            clockwise = (seen << 1) & full | (seen >> (n - 1))
            anticlockwise = (seen >> 1) | ((seen & 1) << (n - 1))
            spread = seen | clockwise | anticlockwise
            for i in range(n):
                if seen & (1 << i) == 0:
                    following.add(spread | (1 << i))
        if full in following:
            return rounds
        states = following
    raise ArithmeticError("no complete burning schedule found")


class CycleSearchTests(unittest.TestCase):
    def test_small_exact_burning_numbers(self):
        for n in range(4, 14):
            with self.subTest(n=n):
                sources = search.burning_schedule(n)
                self.assertEqual(len(sources), brute_force_burning_number(n))
                edges = search.check_certificate(n, sources)
                self.assertEqual(len(edges), n)
                self.assertIn([n - 1, 0], edges)

    def test_schedules_on_either_side_of_squares(self):
        for n in range(4, 150):
            with self.subTest(n=n):
                sources = search.burning_schedule(n)
                search.check_certificate(n, sources)
                for v in range(n):
                    self.assertTrue(any(search.cycle_distance(n, v, u) <= len(sources) - i - 1
                                        for i, u in enumerate(sources)))

    def test_rejects_illegal_schedules(self):
        for sources in ([0, 0], [0, 9], [1], [1, 6, 2]):
            with self.subTest(sources=sources), self.assertRaises(ValueError):
                search.check_certificate(9, sources)

    def test_first_witness_and_adjacent_windows(self):
        report, witnesses = search.search(CATALOG, 4, 46)
        self.assertEqual(
            [(r["source_id"], r["order"], r["vertex_clique_cover_lower_bound"],
              r["rhs_upper_bound"]) for r in report["results"]],
            [("c5b13d43", 23, 12, 11), ("31b3af5f", 33, 17, 16),
             ("a1136330", 41, 21, 20)],
        )
        for row in CATALOG["candidates"]:
            key = row["id"]
            first = witnesses[key]["graph"]["order"]
            _, earlier = search.search(CATALOG, 4, first - 4)
            self.assertNotIn(key, earlier)
            _, single = search.search(CATALOG, first, 1)
            self.assertEqual(single[key], witnesses[key])

    def test_unknown_semantics_fail_closed(self):
        for change in ({"a": -1}, {"lhs": "edge_clique_cover_number"},
                       {"hypotheses": ["bipartite"]}, {"id": "../escape"}):
            variant = copy.deepcopy(CATALOG)
            variant["candidates"][0].update(change)
            with self.subTest(change=change), self.assertRaises(ValueError):
                search.search(variant, 4, 0)

    def test_empty_and_out_of_bounds_windows(self):
        for start, count in ((4, 0), (4, 19)):
            report, witnesses = search.search(CATALOG, start, count)
            self.assertFalse(witnesses)
            self.assertTrue(all(r["status"] == "no_witness_in_window" for r in report["results"]))
        for start, count in ((3, 1), (4, -1), (4, search.MAX_COUNT + 1),
                             (search.MAX_ORDER, 2)):
            with self.subTest(start=start, count=count), self.assertRaises(ValueError):
                search.search(CATALOG, start, count)

    def test_cli_artifacts_and_retry(self):
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp) / "run"
            command = [sys.executable, str(search.HERE / "search.py"),
                       "--start", "4", "--count", "46", "--output", str(out)]
            subprocess.run(command, check=True, capture_output=True)
            first = {p.name: p.read_bytes() for p in out.iterdir()}
            subprocess.run(command, check=True, capture_output=True)
            self.assertEqual(first, {p.name: p.read_bytes() for p in out.iterdir()})
            report = json.loads(first["report.json"])
            for row in report["results"]:
                proof = first[row["lean"]].decode("utf-8")
                witness = json.loads(first[row["certificate"]])
                self.assertIn(f"CycleCertificate.refute {row['order']} {witness['burning_sources']}", proof)
                self.assertIn("CycleCertificate.IsCliqueCoverNumber", proof)
                self.assertIn("CycleCertificate.IsBurningNumber", proof)
                self.assertIn(f"CycleCertificate.CycleGraphHypotheses {row['order']} ∧", proof)
                self.assertIn("∃ burning cover : Nat", proof)
                self.assertIn("CycleCertificate.exists_optima_violation", proof)
            command[5] = "0"
            failed = subprocess.run(command, capture_output=True)
            self.assertNotEqual(failed.returncode, 0)
            self.assertEqual(first, {p.name: p.read_bytes() for p in out.iterdir()})
            command[-1] = str(Path(temp) / "empty")
            subprocess.run(command, check=True, capture_output=True)
            self.assertEqual(sorted(p.name for p in Path(command[-1]).iterdir()), ["report.json"])


if __name__ == "__main__":
    unittest.main()

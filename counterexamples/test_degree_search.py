"""Independent checks for degree/clique/cover counterexample certificates."""

from itertools import combinations
import json
from pathlib import Path
import tempfile
import unittest

import degree_search as degree


CAT = json.loads((degree.HERE / "degree_catalog.json").read_text(encoding="utf-8"))


def exhaustive(n, edges):
    pairs = {tuple(sorted(e)) for e in edges}
    clique = 0
    cover = n
    for mask in range(1 << n):
        selected = {u for u in range(n) if mask & (1 << u)}
        if all((u, v) in pairs for u, v in combinations(sorted(selected), 2)):
            clique = max(clique, len(selected))
        if all(u in selected or v in selected for u, v in pairs):
            cover = min(cover, len(selected))
    return clique, cover


class DegreeSearchTests(unittest.TestCase):
    def test_clique_and_cover_independently(self):
        n = 4
        pairs = list(combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            edges = [edge for i, edge in enumerate(pairs) if mask & (1 << i)]
            features, _ = degree.invariants(n, edges)
            self.assertEqual((features["clique_number"], features["vertex_cover_number"]),
                             exhaustive(n, edges))

    def test_graph_classes(self):
        fixtures = {name: (n, edges) for name, n, edges in degree.fixtures()}
        for name, expected in {
            "complete_4": {"regular": True, "cubic": True, "claw_free": True, "triangle_free": False},
            "cycle_5": {"eulerian": True, "regular": True, "triangle_free": True},
            "star_4": {"claw_free": False, "subcubic": True, "regular": False, "connected": True},
            "star_5": {"subcubic": False},
        }.items():
            _, classes = degree.invariants(*fixtures[name])
            for key, value in expected.items():
                self.assertEqual(classes[key], value, (name, key))
        _, classes = degree.invariants(4, [(0, 1), (2, 3)])
        self.assertFalse(classes["connected"])

    def test_connected_seeded_fixtures(self):
        batch = list(degree.random_graphs(81, 60))
        self.assertEqual(batch, list(degree.random_graphs(81, 60)))
        self.assertNotEqual(batch, list(degree.random_graphs(82, 60)))
        for _, n, edges in batch:
            self.assertTrue(4 <= n <= 12)
            self.assertTrue(degree.invariants(n, edges)[1]["connected"])
            self.assertEqual(edges, degree.canonical_edges(n, edges))

    def test_positive_and_negative_controls(self):
        cat = {"source_url": "local-test", "git_blob_sha": "test", "candidates": [
            {"id": "false", "statement": "clique <= 1", "source_url": "test",
             "hypotheses": ["connected"], "linear": {"constant": 1, "clique_number": -1}},
            {"id": "true", "statement": "clique <= order", "source_url": "test",
             "hypotheses": ["connected"], "linear": {"order": 1, "clique_number": -1}},
        ]}
        run = degree.search(cat, 3, 0)
        false, true = run["results"]
        self.assertEqual(false["status"], "witness_found")
        self.assertLess(false["witness"]["value"], 0)
        self.assertEqual(true["status"], "no_witness_in_sample")
        self.assertTrue(true["eligible_graphs"] > 0)
        self.assertEqual(run["regression_control"]["value"], -3)
        self.assertIn("theorem candidate_0", degree.render(run))

    def test_catalog_and_output_replay(self):
        self.assertEqual(len(CAT["candidates"]), 19)
        run = degree.search(CAT, 7, 6)
        self.assertEqual(len(run["results"]), len(CAT["candidates"]))
        self.assertEqual([x["id"] for x in run["results"]], [r["id"] for r in CAT["candidates"]])
        for row in run["results"]:
            if "witness" in row:
                w = row["witness"]
                features, classes = degree.invariants(w["order"], w["edges"])
                self.assertTrue(all(classes[c] for c in w["hypotheses"]))
                self.assertLess(degree.evaluate(w["linear"], features), 0)
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "run"
            degree.publish(out, run)
            first = {p.name: p.read_bytes() for p in out.iterdir()}
            degree.publish(out, run)
            self.assertEqual(first, {p.name: p.read_bytes() for p in out.iterdir()})
            self.assertIn(b"theorem regression_control", first["DegreeWitnesses.lean"])
            self.assertNotIn("regression_control", [r["id"] for r in run["results"]])
            with self.assertRaises(ValueError):
                degree.publish(out, degree.search(CAT, 8, 6))

    def test_fail_closed(self):
        for change in ({"linear": {"typo": 1}}, {"linear": {"order": 0.25}}, {"hypotheses": ["typo"]}):
            import copy
            cat = copy.deepcopy(CAT)
            cat["candidates"][0].update(change)
            with self.assertRaises(ValueError):
                degree.search(cat, 3, 0)
        with self.assertRaises(ValueError):
            degree.search(CAT, 3, -1)


if __name__ == "__main__":
    unittest.main()

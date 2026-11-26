import json
import unittest
from pathlib import Path

import import_catalog


HERE = Path(__file__).resolve().parent


class SourceLanguageTests(unittest.TestCase):
    def test_degree_coefficients_follow_the_source_inequality(self):
        data = json.loads((HERE / "degree_catalog.json").read_text(encoding="utf-8"))
        for row in data["candidates"]:
            with self.subTest(row=row["id"]):
                hypotheses, linear = import_catalog.normalize(row["statement"])
                self.assertEqual(hypotheses, row["hypotheses"])
                self.assertEqual(linear, row["linear"])

    def test_burning_bounds_match_signed_coefficients_and_graph_classes(self):
        data = json.loads((HERE / "catalog.json").read_text(encoding="utf-8"))
        for row in data["candidates"]:
            with self.subTest(row=row["id"]):
                hypotheses, linear = import_catalog.normalize(
                    row["statement"], {row["lhs"], row["rhs_invariant"]}
                )
                self.assertEqual(hypotheses, row["hypotheses"])
                expected = {row["lhs"]: -1, row["rhs_invariant"]: row["a"], "constant": row["b"]}
                self.assertEqual(linear, {k: v for k, v in expected.items() if v})

    def test_public_certificates_reproduce_from_catalog(self):
        import search

        catalog = json.loads((HERE / "catalog.json").read_text(encoding="utf-8"))
        _, witnesses = search.search(catalog, 4, 46)
        examples = HERE / "examples"
        generated = {
            f"Witness_{key}.lean": search.render_lean(witness).encode("utf-8")
            for key, witness in witnesses.items()
        }
        self.assertEqual({p.name: p.read_bytes() for p in examples.glob("*.lean")}, generated)

    def test_rejects_nonlinear_or_unsupported_sources(self):
        for statement in ("(tree) ⇒ size ≤ order",
                          "(regular) ⇒ maximum_degree · order ≤ size",
                          "(regular) ⇒ size ≤ compute(order)",
                          "((connected) | (regular)) ⇒ size ≤ order"):
            with self.subTest(statement=statement), self.assertRaises(ValueError):
                import_catalog.normalize(statement)


if __name__ == "__main__":
    unittest.main()

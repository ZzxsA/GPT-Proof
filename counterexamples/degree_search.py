"""Reproducible counterexample search on finite undirected graphs (Python standard library)."""

import argparse
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path
import random
import re
import tempfile


HERE = Path(__file__).resolve().parent
CLASSES = {
    "nontrivial": "nontrivial", "claw_free": "clawFree", "subcubic": "subcubic",
    "eulerian": "eulerian", "triangle_free": "triangleFree", "regular": "regular",
    "connected": "connected", "cubic": "cubic",
}
FEATURES = {
    "constant": "constant", "order": "order", "size": "size",
    "clique_number": "cliqueNumber", "vertex_cover_number": "vertexCoverNumber",
    "maximum_degree": "maximumDegree", "minimum_degree": "minimumDegree",
}


def canonical_edges(n, edges):
    result = set()
    for u, v in edges:
        if u == v or min(u, v) < 0 or max(u, v) >= n:
            raise ValueError("invalid undirected edge")
        result.add((min(u, v), max(u, v)))
    return sorted(result)


def fixtures():
    for n in range(4, 13):
        path = [(i, i + 1) for i in range(n - 1)]
        yield f"path_{n}", n, path
        yield f"cycle_{n}", n, path + [(0, n - 1)]
        yield f"star_{n}", n, [(0, i) for i in range(1, n)]
        yield f"complete_{n}", n, list(combinations(range(n), 2))
        for split in sorted({2, n // 2}):
            edges = [(u, v) for u in range(split) for v in range(split, n)]
            yield f"complete_bipartite_{split}_{n-split}", n, edges
        clique = n // 2
        tail = [(v, v+1) for v in range(clique-1, n-1)]
        yield f"lollipop_{n}", n, list(combinations(range(clique), 2)) + tail


def random_graphs(seed, count):
    rng = random.Random(seed)
    for i in range(count):
        n = rng.randrange(4, 13)
        labels = list(range(n))
        rng.shuffle(labels)
        tree = set()
        for j in range(1, n):
            link = sorted((labels[j], labels[rng.randrange(j)]))
            tree.add(tuple(link))
        density = (0.0, 0.1, 0.25, 0.5, 0.8)[i % 5]
        edges = [e for e in combinations(range(n), 2) if e in tree or rng.random() < density]
        yield f"random_{i}", n, edges


def clique_number(adj):
    @lru_cache(None)
    def best(mask):
        if not mask:
            return 0
        bit = mask & -mask
        rest = mask ^ bit
        nbr = adj[bit.bit_length()-1]
        return max(best(rest), 1 + best(rest & nbr))
    return best((1 << len(adj)) - 1)


def invariants(n, edges):
    edges = canonical_edges(n, edges)
    adj = [0] * n
    for u, v in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    full = (1 << n) - 1
    seen, pending = 0, 1
    while pending:
        bit = pending & -pending
        seen |= bit
        pending = (pending | adj[bit.bit_length()-1]) & ~seen
    degrees = [x.bit_count() for x in adj]
    maximum, minimum = max(degrees), min(degrees)
    comp = [full ^ ((1 << i) | nbr) for i, nbr in enumerate(adj)]
    omega = clique_number(adj)
    claw = any(not ((adj[a] & (1 << b)) or (adj[a] & (1 << c)) or (adj[b] & (1 << c)))
               for nbr in adj for a, b, c in combinations((v for v in range(n) if nbr & (1 << v)), 3))
    features = {"constant": 1, "order": n, "size": len(edges), "maximum_degree": maximum,
                "minimum_degree": minimum, "clique_number": omega,
                "vertex_cover_number": n - clique_number(comp)}
    classes = {"nontrivial": n >= 2, "connected": seen == full, "claw_free": not claw,
               "cubic": minimum == maximum == 3, "regular": maximum == minimum,
               "subcubic": maximum <= 3, "triangle_free": omega <= 2,
               "eulerian": seen == full and all(d % 2 == 0 for d in degrees)}
    return features, classes


def validate(catalog):
    seen = set()
    for row in catalog["candidates"]:
        key = row["id"]
        if not re.fullmatch(r"[A-Za-z0-9_-]+", key) or key in seen:
            raise ValueError(f"invalid or duplicate candidate identifier: {key}")
        seen.add(key)
        if not set(row["hypotheses"]) <= CLASSES.keys():
            raise ValueError(f"unsupported graph class in {key}")
        if not row["linear"] or not row["linear"].keys() <= FEATURES.keys():
            raise ValueError(f"unsupported invariant in {key}")
        if any(type(value) is not int for value in row["linear"].values()):
            raise ValueError(f"nonintegral coefficient in {key}")


def evaluate(linear, features):
    return sum(coefficient * features[key] for key, coefficient in linear.items())


def witness(row, label, n, edges, features, classes):
    return {"id": row["id"], "label": label, "order": n, "edges": canonical_edges(n, edges),
            "hypotheses": row["hypotheses"], "linear": row["linear"],
            "features": features, "classes": classes, "value": evaluate(row["linear"], features)}


def search(catalog, seed, count):
    if not 0 <= count <= 5000:
        raise ValueError("--graphs must be between 0 and 5000")
    validate(catalog)
    rows = catalog["candidates"]
    results = {r["id"]: {"id": r["id"], "statement": r["statement"], "source_url": r["source_url"],
                          "eligible_graphs": 0, "status": "no_witness_in_sample"} for r in rows}
    fixture_count = 0
    for graphs, is_fixture in ((fixtures(), True), (random_graphs(seed, count), False)):
        for label, n, edges in graphs:
            fixture_count += int(is_fixture)
            features, classes = invariants(n, edges)
            for row in rows:
                result = results[row["id"]]
                if not all(classes[key] for key in row["hypotheses"]):
                    continue
                result["eligible_graphs"] += 1
                if "witness" not in result and evaluate(row["linear"], features) < 0:
                    result["status"] = "witness_found"
                    result["witness"] = witness(row, label, n, edges, features, classes)
    control = {"id": "regression_control", "hypotheses": ["connected"],
               "linear": {"constant": 1, "clique_number": -1}}
    edges = list(combinations(range(4), 2))
    features, classes = invariants(4, edges)
    regression = witness(control, "synthetic_control_K4", 4, edges, features, classes)
    if regression["value"] != -3:
        raise ArithmeticError("the synthetic regression check failed")
    return {"source_url": catalog["source_url"], "git_blob_sha": catalog["git_blob_sha"],
            "seed": seed, "random_graphs": count, "fixture_graphs": fixture_count,
            "results": list(results.values()), "regression_control": regression}


def render(report):
    lines = ["import DegreeCertificate", "", "open DegreeCertificate", "",
             "namespace DegreeWitnesses", "", "set_option maxRecDepth 100000",
             "set_option maxHeartbeats 0", ""]
    records = [("regression_control", report["regression_control"], "Synthetic regression control; excluded from discoveries.")]
    for i, row in enumerate(report["results"]):
        if "witness" in row:
            records.append((f"candidate_{i}", row["witness"], f"{row['id']} {row['source_url']}"))
    for name, w, comment in records:
        classes = ", ".join("." + CLASSES[k] for k in w["hypotheses"])
        terms = ", ".join(f"(.{FEATURES[k]}, {v})" for k, v in sorted(w["linear"].items()))
        edges = ", ".join(f"({u}, {v})" for u, v in w["edges"])
        lines += [f"-- {comment}", f"theorem {name} :",
                  f"    ∃ g : Graph, Witness g [{classes}] [{terms}] :=",
                  f"  ⟨⟨{w['order']}, [{edges}]⟩, by decide⟩", ""]
    return "\n".join(lines + ["end DegreeWitnesses", ""])


def publish(output, report):
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=output.parent) as td:
        stage = Path(td) / "run"
        stage.mkdir()
        (stage / "report.json").write_bytes((json.dumps(report, indent=2, ensure_ascii=False) + "\n").encode())
        (stage / "DegreeWitnesses.lean").write_bytes(render(report).encode())
        if output.is_dir():
            try:
                output.rmdir()
            except OSError:
                pass
        try:
            stage.rename(output)
        except OSError:
            if not output.is_dir():
                raise
            if {p.name for p in stage.iterdir()} != {p.name for p in output.iterdir()}:
                raise ValueError("use a fresh output directory") from None
            if any(p.read_bytes() != (output/p.name).read_bytes() for p in stage.iterdir()):
                raise ValueError("output already holds a different run") from None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20261126)
    parser.add_argument("--graphs", type=int, default=200)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        catalog = json.loads((HERE / "degree_catalog.json").read_text(encoding="utf-8"))
        report = search(catalog, args.seed, args.graphs)
        publish(args.output, report)
    except (KeyError, ValueError, OSError) as error:
        parser.exit(2, f"{parser.prog}: {error}\n")
    hits = sum(r["status"] == "witness_found" for r in report["results"])
    print(f"{hits} catalog witness(es); report: {args.output / 'report.json'}")


if __name__ == "__main__":
    main()

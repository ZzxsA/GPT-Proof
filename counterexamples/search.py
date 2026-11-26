"""Search published affine bounds on clique cover and graph burning on cycles."""

import argparse
import json
import math
from pathlib import Path
import re
import shutil
import tempfile


HERE = Path(__file__).resolve().parent
MAX_COUNT = 256
MAX_ORDER = 10000
CYCLE_PROPERTIES = {"nontrivial", "regular", "claw_free", "subcubic", "eulerian"}


def validate_catalog(catalog):
    candidates = catalog["candidates"]
    seen = set()
    for row in candidates:
        key = row["id"]
        if not isinstance(key, str) or not re.fullmatch(r"[0-9a-f]{8}", key) or key in seen:
            raise ValueError(f"invalid or duplicate source ID: {key}")
        seen.add(key)
        if row["lhs"] != "vertex_clique_cover_number" or row["rhs_invariant"] != "burning_number":
            raise ValueError(f"unsupported invariants in {key}")
        if type(row["a"]) is not int or row["a"] < 0 or type(row["b"]) is not int:
            raise ValueError(f"expected a nonnegative integer slope and integer intercept in {key}")
        if not set(row["hypotheses"]).issubset(CYCLE_PROPERTIES):
            raise ValueError(f"unsupported hypothesis in {key}")
        if not row["statement"] or not row["source_url"].startswith("https://"):
            raise ValueError(f"missing source text or URL in {key}")
    return candidates


def validate_window(start, count):
    if start < 4 or start > MAX_ORDER:
        raise ValueError(f"--start must be between 4 and {MAX_ORDER}")
    if not 0 <= count <= MAX_COUNT:
        raise ValueError(f"--count must be between 0 and {MAX_COUNT}")
    if count and start + count - 1 > MAX_ORDER:
        raise ValueError(f"window exceeds the maximum cycle order {MAX_ORDER}")


def burning_schedule(n):
    """Partition the cycle into centered blocks of decreasing admissible radii."""
    if n < 4:
        raise ValueError("expected a cycle on at least four vertices")
    k = math.isqrt(n - 1) + 1
    radii = range(k - 1, -1, -1)
    lengths = [max(1, 2 * radius - 1) for radius in radii]
    remaining = n - sum(lengths)
    sources = []
    offset = 0
    for radius, length in zip(radii, lengths):
        extra = min(remaining, 2 * radius + 1 - length)
        remaining -= extra
        length += extra
        sources.append(offset + (length - 1) // 2)
        offset += length
    if offset != n:
        raise ArithmeticError("cycle partition does not exhaust the vertices")
    return sources


def cycle_distance(n, u, v):
    gap = abs(u - v)
    return min(gap, n - gap)


def check_certificate(n, sources):
    """Check the clique-size bound and replay all burning rounds on explicit edges."""
    edges = [[v, (v + 1) % n] for v in range(n)]
    neighbors = [set() for _ in range(n)]
    for u, v in edges:
        neighbors[u].add(v)
        neighbors[v].add(u)
    if any(len(s) != 2 for s in neighbors) or any(neighbors[u] & neighbors[v] for u, v in edges):
        raise ValueError("the graph must be a triangle-free cycle")
    if any(x < 0 or x >= n for x in sources):
        raise ValueError("source outside the cycle")
    for j, later in enumerate(sources):
        if any(cycle_distance(n, earlier, later) < j - i for i, earlier in enumerate(sources[:j])):
            raise ValueError("burning sources are insufficiently separated")
    burned = set()
    for source in sources:
        if source in burned:
            raise ValueError("new source already burned")
        spread = {v for u in burned for v in neighbors[u]}
        burned.update(spread)
        burned.add(source)
    if len(burned) != n:
        raise ValueError("schedule leaves a vertex unburned")
    return edges


def make_witness(row, n):
    sources = burning_schedule(n)
    edges = check_certificate(n, sources)
    lower = (n + 1) // 2
    rhs_upper = row["a"] * len(sources) + row["b"]
    if lower <= rhs_upper:
        raise ValueError("bounds do not give a strict counterexample")
    return {
        "source_id": row["id"], "rank": row["rank"], "source_url": row["source_url"],
        "statement": row["statement"], "hypotheses": row["hypotheses"],
        "graph": {"family": "cycle", "order": n, "edges": edges},
        "burning_sources": sources, "burning_upper_bound": len(sources),
        "maximum_clique_size": 2, "vertex_clique_cover_lower_bound": lower,
        "rhs_coefficients": {"a": row["a"], "b": row["b"]},
        "rhs_upper_bound": rhs_upper,
    }


def render_lean(witness):
    n = witness["graph"]["order"]
    key = witness["source_id"]
    sources = witness["burning_sources"]
    a = witness["rhs_coefficients"]["a"]
    b = witness["rhs_coefficients"]["b"]
    operator = "+" if b >= 0 else "-"
    expression = f"{a} * k {operator} {abs(b)}"
    return (
        "import CycleCertificate\n\n"
        f"-- Source {key}, rank {witness['rank']}: {witness['source_url']}\n"
        "set_option maxRecDepth 100000\n"
        "set_option maxHeartbeats 0\n\n"
        f"private theorem burns_{key} :\n"
        f"    CycleCertificate.successful {n} {sources} = true := by decide\n\n"
        f"theorem counterexample_{key} :\n"
        f"    ¬ CycleCertificate.BoundAt {n} (fun k => {expression}) :=\n"
        f"  CycleCertificate.refute {n} {sources} (fun k => {expression})\n"
        f"    (by decide) burns_{key} (by decide)\n\n"
        f"-- The cycle satisfies the source hypotheses: {', '.join(witness['hypotheses'])}.\n"
        f"theorem violates_{key} :\n"
        f"    CycleCertificate.CycleGraphHypotheses {n} ∧\n"
        "      ∃ burning cover : Nat,\n"
        f"        CycleCertificate.IsBurningNumber {n} burning ∧\n"
        f"        CycleCertificate.IsCliqueCoverNumber {n} cover ∧\n"
        f"        {a} * (burning : Int) {operator} {abs(b)} < (cover : Int) := by\n"
        "  refine ⟨CycleCertificate.cycle_graph_hypotheses (by decide), ?_⟩\n"
        "  obtain ⟨burning, cover, hb, hc, hgap⟩ :=\n"
        f"    CycleCertificate.exists_optima_violation {n} {sources} (fun k => {expression})\n"
        f"      (by decide) burns_{key} (by decide) (by intro x y hxy; change {a} * x {operator} {abs(b)} ≤ {a} * y {operator} {abs(b)}; omega)\n"
        "  refine ⟨burning, cover, hb, hc, ?_⟩\n"
        f"  change {a} * burning {operator} {abs(b)} < cover at hgap\n"
        "  omega\n"
    )


def search(catalog, start, count):
    validate_window(start, count)
    rows = validate_catalog(catalog)
    witnesses = {}
    for n in range(start, start + count):
        k = math.isqrt(n - 1) + 1
        for row in rows:
            key = row["id"]
            if key not in witnesses and (n + 1) // 2 > row["a"] * k + row["b"]:
                witnesses[key] = make_witness(row, n)
    results = []
    for row in rows:
        key = row["id"]
        entry = {"source_id": key, "source_url": row["source_url"], "rank": row["rank"]}
        if key in witnesses:
            w = witnesses[key]
            entry.update(status="witness_found", order=w["graph"]["order"],
                         burning_sources=w["burning_sources"], burning_upper_bound=w["burning_upper_bound"],
                         vertex_clique_cover_lower_bound=w["vertex_clique_cover_lower_bound"],
                         rhs_upper_bound=w["rhs_upper_bound"],
                         certificate=f"witness_{key}.json", lean=f"Witness_{key}.lean")
        else:
            entry["status"] = "no_witness_in_window"
        results.append(entry)
    report = {"schema_version": 1, "family": "cycle",
              "window": {"start": start, "count": count, "stop_exclusive": start + count},
              "results": results}
    return report, witnesses


def write_json(path, data):
    path.write_bytes((json.dumps(data, indent=2, ensure_ascii=False) + "\n").encode("utf-8"))


def publish(output, report, witnesses):
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=output.parent) as temp:
        stage = Path(temp) / "run"
        stage.mkdir()
        if witnesses:
            shutil.copyfile(HERE / "CycleCertificate.lean", stage / "CycleCertificate.lean")
        for key, witness in witnesses.items():
            write_json(stage / f"witness_{key}.json", witness)
            (stage / f"Witness_{key}.lean").write_bytes(render_lean(witness).encode("utf-8"))
        write_json(stage / "report.json", report)
        # Windows requires an absent target for a directory rename. rmdir only
        # succeeds on an empty directory and cannot remove an existing run.
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
            if {p.name for p in output.iterdir()} != {p.name for p in stage.iterdir()}:
                raise ValueError(f"{output} contains different files; choose a fresh output directory") from None
            for path in stage.iterdir():
                previous = output / path.name
                if not previous.is_file() or previous.read_bytes() != path.read_bytes():
                    raise ValueError(f"{output} contains different files; choose a fresh output directory") from None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, default=4, help="first cycle order (inclusive)")
    parser.add_argument("--count", type=int, default=46, help="number of consecutive orders to search")
    parser.add_argument("--output", type=Path, required=True, help="new or matching result directory")
    args = parser.parse_args()
    try:
        catalog = json.loads((HERE / "catalog.json").read_text(encoding="utf-8"))
        report, witnesses = search(catalog, args.start, args.count)
        publish(args.output, report, witnesses)
    except (ValueError, KeyError, OSError) as exc:
        parser.exit(2, f"{parser.prog}: {exc}\n")
    print(f"{len(witnesses)} witness(es); report: {args.output / 'report.json'}")


if __name__ == "__main__":
    main()

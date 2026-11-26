"""Import the supported affine graph conjectures from a pinned AutoGraphForge snapshot."""

import argparse
import ast
import hashlib
import json
import re
from fractions import Fraction
from functools import reduce
from math import gcd
from pathlib import Path


UPSTREAM = "https://github.com/JanPastorek/AutoGraphForge"
SOURCE_PATH = "results/survivors_by_touch_normalised.txt"
METRICS = {"order", "size", "minimum_degree", "maximum_degree",
           "clique_number", "vertex_cover_number"}
CLASSES = {"nontrivial", "connected", "regular", "subcubic", "eulerian",
           "triangle_free", "claw_free", "cubic"}


class Unsupported(ValueError):
    """The row is outside the graph language checked by DegreeCertificate."""


def predicates(node):
    if isinstance(node, ast.Name) and node.id in CLASSES:
        return [node.id]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitAnd):
        return predicates(node.left) + predicates(node.right)
    raise Unsupported("unsupported graph predicate")


def add(left, right, sign=1):
    result = left.copy()
    for key, value in right.items():
        result[key] = result.get(key, 0) + sign * value
    return result


def scale(poly, scalar):
    return {key: scalar * value for key, value in poly.items()}


def affine(node, metrics):
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return {"constant": Fraction(node.value)}
    if isinstance(node, ast.Name) and node.id in metrics:
        return {node.id: Fraction(1)}
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return scale(affine(node.operand, metrics), -1)
    if isinstance(node, ast.BinOp):
        left, right = affine(node.left, metrics), affine(node.right, metrics)
        if isinstance(node.op, (ast.Add, ast.Sub)):
            return add(left, right, -1 if isinstance(node.op, ast.Sub) else 1)
        if isinstance(node.op, ast.Div) and set(right) == {"constant"} and right["constant"]:
            return scale(left, 1 / right["constant"])
        if isinstance(node.op, ast.Mult):
            if set(left) == {"constant"}:
                return scale(right, left["constant"])
            if set(right) == {"constant"}:
                return scale(left, right["constant"])
    raise Unsupported("outside the supported affine language")


def parse_expression(text):
    return ast.parse(text.strip().replace("·", "*").replace("∧", "&"), mode="eval").body


def normalize(statement, metrics=METRICS):
    premise, comparison = statement.split("⇒")
    left, right = comparison.split("≤")
    hypotheses = predicates(parse_expression(premise))
    difference = add(affine(parse_expression(right), metrics), affine(parse_expression(left), metrics), -1)
    nonzero = {k: v for k, v in difference.items() if v}
    if not nonzero:
        raise Unsupported("identity")
    denominator = 1
    for v in nonzero.values():
        denominator = denominator * v.denominator // gcd(denominator, v.denominator)
    integers = {k: int(v * denominator) for k, v in nonzero.items()}
    divisor = reduce(gcd, (abs(i) for i in integers.values()))
    return hypotheses, {k: v // divisor for k, v in sorted(integers.items())}


def catalog(data, revision):
    if not re.fullmatch(r"[a-f0-9]{40}", revision):
        raise ValueError("Supply a full upstream commit SHA.")
    url = f"{UPSTREAM}/blob/{revision}/{SOURCE_PATH}"
    blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    candidates = []
    for line_no, line in enumerate(data.decode("utf-8").splitlines(), 1):
        match = re.fullmatch(r"\[\s*\d+\] (.*?)\s+-- promising:(class|universal)", line)
        if not match:
            continue
        statement = match.group(1).strip()
        try:
            hypotheses, linear = normalize(statement)
        except (SyntaxError, ValueError):
            continue
        candidates.append({
            "id": f"agf-{revision[:8]}-L{line_no}",
            "source_url": f"{url}#L{line_no}",
            "statement": statement, "hypotheses": hypotheses, "linear": linear,
        })
    return {"source_url": url, "git_blob_sha": blob, "candidates": candidates}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--snapshot", required=True, type=Path)
    ap.add_argument("--revision", required=True)
    ap.add_argument("--output", required=True, type=Path)
    ap.add_argument("--expect-blob", help="Optional expected Git blob SHA of the input.")
    args = ap.parse_args()
    result = catalog(args.snapshot.read_bytes(), args.revision)
    if args.expect_blob and result["git_blob_sha"] != args.expect_blob:
        ap.error("The source bytes do not match --expect-blob.")
    if not result["candidates"]:
        ap.error("No compatible records found; check the source format.")
    with args.output.open("w", encoding="utf-8", newline="\n") as out:
        json.dump(result, out, ensure_ascii=False, indent=2)
        out.write("\n")
    print(f"Imported {len(result['candidates'])} source statements.")


if __name__ == "__main__":
    main()

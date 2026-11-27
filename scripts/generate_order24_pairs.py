# SPDX-License-Identifier: Apache-2.0
"""Generate denominator-cleared pair certificates; Lean checks every assertion."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import sys
from generate_order24_terminal import MASKS

ROOT = Path(__file__).resolve().parents[1]


def generate(i, j, destination=None):
    retained = [k for k in range(16) if k not in (i, j)]
    full = [[Q(-1 if m >> k & 1 else 1) for k in range(24)] for m in MASKS]
    reduced = [full[k][:] for k in retained]
    transform = [[Q(s == t) for t in range(14)] for s in range(14)]
    pivots = []
    for col in range(24):
        rank = len(pivots)
        pivot = next((k for k in range(rank, 14) if reduced[k][col]), None)
        if pivot is None:
            continue
        reduced[rank], reduced[pivot] = reduced[pivot], reduced[rank]
        transform[rank], transform[pivot] = transform[pivot], transform[rank]
        scale = reduced[rank][col]
        reduced[rank] = [v / scale for v in reduced[rank]]
        transform[rank] = [v / scale for v in transform[rank]]
        for k in range(14):
            if k != rank:
                scale = reduced[k][col]
                reduced[k] = [x - scale*y for x, y in zip(reduced[k], reduced[rank])]
                transform[k] = [x - scale*y for x, y in zip(transform[k], transform[rank])]
        pivots.append(col)
        if len(pivots) == 14:
            break
    assert len(pivots) == 14
    free = [k for k in range(24) if k not in pivots]
    left = [[Q(0)]*14 for _ in range(24)]
    inverse = [[Q(0)]*10 for _ in range(24)]
    for k, col in enumerate(pivots):
        left[col] = transform[k]
        inverse[col] = [-reduced[k][c] for c in free]
    for k, col in enumerate(free):
        inverse[col][k] = Q(1)
    candidates = []
    for seed in product((-1, 1), repeat=10):
        x = [sum(v*s for v, s in zip(row, seed)) for row in inverse]
        if all(v in (-1, 1) for v in x):
            candidates.append(tuple(sum(v*w for v, w in zip(full[k], x)) for k in (i, j)))
    def pattern(s, u, v):
        return (u == 0 and abs(v) == 24) or (v == 0 and abs(u) == 24) or (abs(u) == 12 and v == s*u)
    sigma = next(s for s in (1, -1) if all(pattern(s, u, v) for u, v in candidates))
    from integer_pair_codegen import source_for_pair
    pairs = [(s, t) for s in range(16) for t in range(s+1, 16)]
    position = pairs.index((i, j))
    previous_module = None
    if position and destination is None:
        previous = position-1 if position < 15 else max(14, position-4)
        s, t = pairs[previous]
        previous_module = f"CompletionTheory.Order24Pairs.P{s:02}_{t:02}"
    source = source_for_pair(i, j, retained, free, left, inverse, sigma, previous_module)
    dest = destination or ROOT / f"CompletionTheory/Order24Pairs/P{i:02}_{j:02}.lean"
    dest.parent.mkdir(exist_ok=True)
    dest.write_text(source, encoding="utf-8")
    print(f"Generated pair {i},{j}: {len(candidates)} sign seeds, sigma={sigma}")


if __name__ == "__main__":
    if sys.argv[1:] == ["--all"]:
        pairs = [(i, j) for i in range(16) for j in range(i+1, 16)]
        for i, j in pairs:
            generate(i, j)
        source = "/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/\nmodule\n"
        source += "".join(f"public import CompletionTheory.Order24Pairs.P{i:02}_{j:02}\n"
                          for i, j in pairs[-4:])
        (ROOT / "CompletionTheory/Order24AllPairs.lean").write_text(source, encoding="utf-8")
    elif len(sys.argv) == 3:
        i, j = map(int, sys.argv[1:])
        if not 0 <= i < j < 16:
            raise SystemExit("Require 0 <= i < j < 16")
        generate(i, j)
    else:
        raise SystemExit("Usage: generate_order24_pairs.py --all | i j")

# SPDX-License-Identifier: Apache-2.0
"""Emit denominator-cleared proof data, checked independently by Lean."""
from math import lcm


def source_for_pair(i, j, retained, free, left, inverse, sigma, previous=None):
    denominator = lcm(*(v.denominator for matrix in (left, inverse) for row in matrix for v in row))
    left = [[int(v * denominator) for v in row] for row in left]
    inverse = [[int(v * denominator) for v in row] for row in inverse]
    prefix = f"pair24_{i:02}_{j:02}"
    def matrix(name, values):
        return f"def {prefix}{name} : Matrix (Fin 24) (Fin {len(values[0])}) ℤ :=\n  !![" + ";\n     ".join(", ".join(map(str, row)) for row in values) + "]\n\n"
    dependency = previous or "CompletionTheory.IntegerPairCertificates"
    source = f'''/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import {dependency}
@[expose] public section
namespace CompletionTheory

'''
    source += f"def {prefix}Rows : Fin 14 → Fin 16 := ![" + ", ".join(map(str, retained)) + "]\n"
    source += f"def {prefix}Free : Fin 10 → Fin 24 := ![" + ", ".join(map(str, free)) + "]\n\n"
    source += matrix("Left", left) + matrix("Inverse", inverse)
    source += f'''set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem {prefix}_certificate :
    {prefix}Left * (encodedIntFrame (n := 24) base24Masks).submatrix {prefix}Rows id +
      {prefix}Inverse * integerInformationSelector {prefix}Free = ({denominator} : ℤ) • 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem {prefix}_finite : ∀ b : Fin 10 → Bool,
    (∀ k, {prefix}Inverse.mulVec (fun t => if b t then 1 else -1) k = {denominator} ∨
      {prefix}Inverse.mulVec (fun t => if b t then 1 else -1) k = -{denominator}) →
    IntegerScaledHalfPattern {denominator} ({sigma})
      (∑ k, encodedIntFrame base24Masks {i} k * {prefix}Inverse.mulVec (fun t => if b t then 1 else -1) k)
      (∑ k, encodedIntFrame base24Masks {j} k * {prefix}Inverse.mulVec (fun t => if b t then 1 else -1) k) := by
  unfold IntegerScaledHalfPattern
  decide +kernel

theorem {prefix}_correlations : ∀ x : Fin 24 → ℝ,
    OriginalCandidate base24Frame {{{i}, {j}}} x →
    HalfCorrelationPattern 24 (rationalRealCast ({sigma}))
      (∑ k, base24Frame {i} k * x k) (∑ k, base24Frame {j} k * x k) := by
  have h := order24_integer_pair_lift {i} {j} {prefix}Rows {prefix}Free
    {prefix}Left {prefix}Inverse {denominator} ({sigma}) (by norm_num) (by decide +kernel)
    {prefix}_certificate {prefix}_finite
  norm_num [rationalRealCast] at h ⊢
  exact h

end CompletionTheory
'''
    return source

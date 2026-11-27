# SPDX-License-Identifier: Apache-2.0
"""Original exact reconstruction data for the paper's twelve-row code trap."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MASKS = [0, 965904, 1003736, 902980, 730036, 501868,
         412530, 210762, 649754, 358790, 694982, 250934]


def main():
    original = [[Q(-1 if m >> j & 1 else 1) for j in range(20)] for m in MASKS]
    reduced = [row[:] for row in original]
    transform = [[Q(i == j) for j in range(12)] for i in range(12)]
    pivots = []
    for col in range(20):
        rank = len(pivots)
        pivot = next((i for i in range(rank, 12) if reduced[i][col]), None)
        if pivot is None:
            continue
        reduced[rank], reduced[pivot] = reduced[pivot], reduced[rank]
        transform[rank], transform[pivot] = transform[pivot], transform[rank]
        scale = reduced[rank][col]
        reduced[rank] = [v / scale for v in reduced[rank]]
        transform[rank] = [v / scale for v in transform[rank]]
        for i in range(12):
            if i != rank:
                scale = reduced[i][col]
                reduced[i] = [x - scale*y for x, y in zip(reduced[i], reduced[rank])]
                transform[i] = [x - scale*y for x, y in zip(transform[i], transform[rank])]
        pivots.append(col)
        if len(pivots) == 12:
            break
    assert len(pivots) == 12
    free = [j for j in range(20) if j not in pivots]
    left = [[Q(0)]*12 for _ in range(20)]
    inverse = [[Q(0)]*8 for _ in range(20)]
    for i, col in enumerate(pivots):
        left[col] = transform[i]
        inverse[col] = [-reduced[i][j] for j in free]
    for i, col in enumerate(free):
        inverse[col][i] = Q(1)
    for seed in product((-1, 1), repeat=8):
        values = [sum(v*x for v, x in zip(row, seed)) for row in inverse]
        assert not all(v in (-1, 1) for v in values)
    def lit(v):
        return str(v.numerator) if v.denominator == 1 else f"({v.numerator} / {v.denominator})"
    def matrix(name, values):
        return f"def {name} : Matrix (Fin 20) (Fin {len(values[0])}) ℚ :=\n  !![" + ";\n     ".join(", ".join(map(lit, row)) for row in values) + "]\n\n"
    source = '''/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.RationalSignCertificates
public import CompletionTheory.EncodedFrames
@[expose] public section
namespace CompletionTheory

'''
    source += "def codeTrap20Masks : Fin 12 → ℕ := ![" + ", ".join(map(str, MASKS)) + "]\n\n"
    source += '''def codeTrap20RationalFrame : Matrix (Fin 12) (Fin 20) ℚ :=
  (encodedIntFrame codeTrap20Masks).map (Int.castRingHom ℚ)

def codeTrap20Frame : Matrix (Fin 12) (Fin 20) ℝ := encodedRealFrame codeTrap20Masks

'''
    source += "def codeTrap20Free : Fin 8 → Fin 20 := ![" + ", ".join(map(str, free)) + "]\n\n"
    source += matrix("codeTrap20Left", left) + matrix("codeTrap20Inverse", inverse)
    source += '''set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem codeTrap20_certificate :
    codeTrap20Left * codeTrap20RationalFrame +
      codeTrap20Inverse * informationSelector codeTrap20Free = 1 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem codeTrap20_no_sign_seed : ∀ b : Fin 8 → Bool,
    ¬ IsCubeVector (codeTrap20Inverse.mulVec (fun j => if b j then 1 else -1)) := by
  unfold IsCubeVector
  decide +kernel

set_option maxRecDepth 20000 in
theorem codeTrap20_int_gram :
    encodedIntFrame (n := 20) codeTrap20Masks * (encodedIntFrame codeTrap20Masks).transpose =
      (20 : ℤ) • (1 : Matrix (Fin 12) (Fin 12) ℤ) := by decide +kernel

theorem codeTrap20_partialHadamard : IsPartialHadamard codeTrap20Frame :=
  encodedRealFrame_partialHadamard codeTrap20Masks codeTrap20_int_gram

theorem codeTrap20RationalFrame_cast :
    codeTrap20RationalFrame.map rationalRealCast = codeTrap20Frame := by
  ext i j
  simp [codeTrap20RationalFrame, codeTrap20Frame, encodedRealFrame, Matrix.map_apply]

theorem codeTrap20_noSignExtension : NoSignExtension codeTrap20Frame := by
  rintro ⟨x, hx, horth⟩
  have hzero : (codeTrap20RationalFrame.map rationalRealCast).mulVec x = 0 := by
    rw [codeTrap20RationalFrame_cast]
    funext i
    exact horth i
  have hrec := rational_reconstruction_complete codeTrap20RationalFrame codeTrap20Left
    codeTrap20Inverse codeTrap20Free codeTrap20_certificate x hzero
  obtain ⟨b, hb⟩ := rational_seed_has_signs codeTrap20Inverse codeTrap20Free x hx hrec
  exact codeTrap20_no_sign_seed b hb

theorem codeTrap20_tensor_partialHadamard {τ : Type*} [Fintype τ] [DecidableEq τ]
    (H : Matrix τ τ ℝ) (hH : IsHadamard H) : IsPartialHadamard (tensorFrame codeTrap20Frame H) :=
  tensorFrame_partialHadamard codeTrap20Frame H codeTrap20_partialHadamard hH

theorem codeTrap20_tensor_noSignExtension {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (H : Matrix τ τ ℝ) (hH : IsHadamard H) : NoSignExtension (tensorFrame codeTrap20Frame H) :=
  tensor_noSignExtension codeTrap20Frame H hH codeTrap20_noSignExtension

end CompletionTheory
'''
    (ROOT / "CompletionTheory/Order20Terminal.lean").write_text(source, encoding="utf-8")
    print("Generated original exact order-20 terminality certificate.")


if __name__ == "__main__":
    main()

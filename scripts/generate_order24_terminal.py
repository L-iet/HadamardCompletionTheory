# SPDX-License-Identifier: Apache-2.0
"""Generate exact rational data; Lean independently checks every assertion."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MASKS = [0, 16773120, 16519104, 10359454, 7684730, 5820908, 9389414,
         1547504, 6736278, 11838780, 3701846, 13790378, 10646512,
         2963882, 12892774, 5974836]


def main():
    original = [[Q(-1 if m >> j & 1 else 1) for j in range(24)] for m in MASKS]
    reduced = [row[:] for row in original]
    transform = [[Q(i == j) for j in range(16)] for i in range(16)]
    pivots = []
    rank = 0
    for col in range(24):
        pivot = next((i for i in range(rank, 16) if reduced[i][col]), None)
        if pivot is None:
            continue
        reduced[rank], reduced[pivot] = reduced[pivot], reduced[rank]
        transform[rank], transform[pivot] = transform[pivot], transform[rank]
        scale = reduced[rank][col]
        reduced[rank] = [v / scale for v in reduced[rank]]
        transform[rank] = [v / scale for v in transform[rank]]
        for i in range(16):
            if i != rank:
                scale = reduced[i][col]
                reduced[i] = [x - scale * y for x, y in zip(reduced[i], reduced[rank])]
                transform[i] = [x - scale * y for x, y in zip(transform[i], transform[rank])]
        pivots.append(col)
        rank += 1
        if rank == 16:
            break
    assert rank == 16
    free = [j for j in range(24) if j not in pivots]
    left = [[Q(0) for _ in range(16)] for _ in range(24)]
    inverse = [[Q(0) for _ in free] for _ in range(24)]
    for i, col in enumerate(pivots):
        left[col] = transform[i]
        inverse[col] = [-reduced[i][j] for j in free]
    for i, col in enumerate(free):
        inverse[col][i] = Q(1)
    for i in range(24):
        for j in range(24):
            value = sum(left[i][k] * original[k][j] for k in range(16))
            value += sum(inverse[i][k] * (free[k] == j) for k in range(8))
            assert value == (i == j)
    # This is generation-time sanity checking, not proof evidence.
    for seed in product((-1, 1), repeat=8):
        values = [sum(v * x for v, x in zip(row, seed)) for row in inverse]
        assert not all(v in (-1, 1) for v in values)

    def literal(v):
        return str(v.numerator) if v.denominator == 1 else f"({v.numerator} / {v.denominator})"

    def matrix(name, values):
        rows = [", ".join(literal(v) for v in row) for row in values]
        return (f"def {name} : Matrix (Fin {len(values)}) (Fin {len(values[0])}) ℚ :=\n"
                + "  !![" + ";\n     ".join(rows) + "]\n\n")

    source = '''/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory.RationalSignCertificates
public import CompletionTheory.Order24Exchange
/-! # Kernel-checked terminality of the explicit sixteen-row frame
Generated exact coefficients are proof data, not an external proof oracle.
The exclusion of one- and two-row exchanges remains a separate obligation. -/
@[expose] public section
namespace CompletionTheory

def base24RationalFrame : Matrix (Fin 16) (Fin 24) ℚ :=
  (encodedIntFrame base24Masks).map (Int.castRingHom ℚ)

'''
    source += "def base24FreeCoordinates : Fin 8 → Fin 24 := ![" + ", ".join(map(str, free)) + "]\n\n"
    source += matrix("base24TerminalLeft", left) + matrix("base24TerminalInverse", inverse)
    source += '''set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem base24_terminal_reconstruction_certificate :
    base24TerminalLeft * base24RationalFrame +
      base24TerminalInverse * informationSelector base24FreeCoordinates =
        (1 : Matrix (Fin 24) (Fin 24) ℚ) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem base24_terminal_no_sign_seed : ∀ b : Fin 8 → Bool,
    ¬ IsCubeVector (base24TerminalInverse.mulVec (fun j => if b j then 1 else -1)) := by
  unfold IsCubeVector
  decide +kernel

theorem base24RationalFrame_cast : base24RationalFrame.map (rationalRealCast) = base24Frame := by
  ext i j
  simp [base24RationalFrame, base24Frame, encodedRealFrame, Matrix.map_apply]

theorem base24Frame_noSignExtension : NoSignExtension base24Frame := by
  rintro ⟨x, hx, horth⟩
  have hzero : (base24RationalFrame.map (rationalRealCast)).mulVec x = 0 := by
    rw [base24RationalFrame_cast]
    funext i
    exact horth i
  have hrec := rational_reconstruction_complete base24RationalFrame base24TerminalLeft
    base24TerminalInverse base24FreeCoordinates base24_terminal_reconstruction_certificate x hzero
  obtain ⟨b, hb⟩ := rational_seed_has_signs base24TerminalInverse base24FreeCoordinates x hx hrec
  exact base24_terminal_no_sign_seed b hb

theorem base24_tensor_partialHadamard {τ : Type*} [Fintype τ] [DecidableEq τ]
    (H : Matrix τ τ ℝ) (hH : IsHadamard H) : IsPartialHadamard (tensorFrame base24Frame H) :=
  tensorFrame_partialHadamard base24Frame H base24Frame_partialHadamard hH

theorem base24_tensor_noSignExtension {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (H : Matrix τ τ ℝ) (hH : IsHadamard H) : NoSignExtension (tensorFrame base24Frame H) :=
  tensor_noSignExtension base24Frame H hH base24Frame_noSignExtension

theorem base24_tensor_exchangeCost_le_three {τ : Type*}
    [Fintype τ] [DecidableEq τ] [Nonempty τ] (H : Matrix τ τ ℝ) (hH : IsHadamard H) :
    exchangeCost (tensorFrame base24Frame H) ≤ (3 : WithTop ℕ) :=
  (tensor_exchangeCost_le base24Frame H hH).trans base24_exchangeCost_le_three

end CompletionTheory
'''
    (ROOT / "CompletionTheory/Order24Terminal.lean").write_text(source, encoding="utf-8")
    print("Generated exact reconstruction certificate and 256-seed terminality obligation.")


if __name__ == "__main__":
    main()

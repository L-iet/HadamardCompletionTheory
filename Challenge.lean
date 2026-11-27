/-
Copyright (c) 2026 Joshua Mark. Released under Apache 2.0; see LICENSE.
Independent target specifications. The intentional proof placeholders below
are not proof dependencies and are isolated from every solution entry point.
All imports are mathlib-only; Solution imports the completed proof module.
The switch criterion and support-motion targets together verify CT-25-01.
Exact proved and pending principal coverage is recorded in paper/ALIGNMENT.json.
-/
module
public import Mathlib.Analysis.Asymptotics.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Finset.Powerset
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Basic.Real.Star
public import Mathlib.Tactic.FinCases
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Tactic.Choose
public import Mathlib.NumberTheory.SumFourSquares
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Rat.BigOperators
@[expose] public section
namespace CompletionTheory
open Matrix
def IsSign (x : ℝ) : Prop := x = 1 ∨ x = -1
def IsSignMatrix {ι κ : Type*} (A : Matrix ι κ ℝ) : Prop :=
  ∀ i j, IsSign (A i j)
def IsPartialHadamard {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix ι κ ℝ) : Prop :=
  IsSignMatrix A ∧ A * Aᵀ = (Fintype.card κ : ℝ) • (1 : Matrix ι ι ℝ)
def IsHadamard {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Prop := IsPartialHadamard A
def IsWeighing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (weight : ℝ) : Prop :=
  (∀ i j, A i j = 0 ∨ IsSign (A i j)) ∧ A * Aᵀ = weight • 1
def concatenate {ι κ ν : Type*} (A : Matrix ι κ ℝ) (B : Matrix ι ν ℝ) :
    Matrix ι (κ ⊕ ν) ℝ := fun i j => Sum.elim (A i) (B i) j
noncomputable def walshFour : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(1/2:ℝ), 1/2, 1/2, 1/2;
      1/2, -1/2, 1/2, -1/2;
      1/2, 1/2, -1/2, -1/2;
      1/2, -1/2, -1/2, 1/2]
def WalshAdmissible (v : Fin 4 → ℝ) : Prop :=
  (v 0 = 0 ∧ v 1 = 0 ∧ IsSign (v 2) ∧ IsSign (v 3)) ∨
  (IsSign (v 0) ∧ IsSign (v 1) ∧ v 2 = 0 ∧ v 3 = 0) ∨
  ((∀ i, IsSign (v i)) ∧ (∏ i, v i) = -1)
noncomputable def walshLift (ν : Type*) [DecidableEq ν] :
    Matrix (Fin 4 ⊕ ν) (Fin 4 ⊕ ν) ℝ :=
  Matrix.fromBlocks walshFour 0 0 1
noncomputable def flattenTwo (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(a+b)/2, (b-a)/2; (a-b)/2, (a+b)/2]
def seedFour : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,1,1,1; 1,-1,1,-1; 1,1,-1,-1; 1,-1,-1,1]
def seedTwelve : Matrix (Fin 12) (Fin 12) ℝ :=
  !![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1;
      -1, 1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1;
      -1, -1, 1, 1, -1, 1, 1, 1, -1, -1, -1, 1;
      -1, 1, -1, 1, 1, -1, 1, 1, 1, -1, -1, -1;
      -1, -1, 1, -1, 1, 1, -1, 1, 1, 1, -1, -1;
      -1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1, -1;
      -1, -1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1;
      -1, 1, -1, -1, -1, 1, -1, 1, 1, -1, 1, 1;
      -1, 1, 1, -1, -1, -1, 1, -1, 1, 1, -1, 1;
      -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, 1, -1;
      -1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, 1;
      -1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1]
def retainAndInsert {ι κ τ : Type*} (P : Matrix ι κ ℝ) (Q : Matrix τ κ ℝ)
    (S : Finset ι) : Matrix (↥S ⊕ τ) κ ℝ :=
  fun i j => Sum.elim (fun k : S => P k.val j) (fun k => Q k j) i
def witnessBudget {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (f : κ → ℤ) : ℝ :=
  (Fintype.card κ : ℝ) * (∑ j, (f j : ℝ)^2) -
    ∑ i, (∑ j, P i j * (f j : ℝ))^2
def signTetrahedron : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1,1,-1,-1; 1,-1,1,-1; 1,-1,-1,1]
def columnSwitch {ι κ : Type*} (P : Matrix ι κ ℝ) (e : κ → ℝ) : Matrix ι κ ℝ :=
  fun i j => P i j * e j
theorem walshLift_switch_iff {ν : Type*} [Fintype ν] [DecidableEq ν] (W : Matrix (Fin 4 ⊕ ν) (Fin 4 ⊕ ν) ℝ) (weight : ℝ) (Z : (Fin 4 ⊕ ν) → Prop) (hW : IsWeighing W weight) (hzero : ∀ j, Z j → (W (Sum.inl 0) j = 0 ∧ W
    (Sum.inl 1) j = 0 ∧ IsSign (W (Sum.inl 2) j) ∧ IsSign (W (Sum.inl 3) j)) ∨ (IsSign (W (Sum.inl 0) j) ∧ IsSign (W (Sum.inl 1) j) ∧ W (Sum.inl 2) j = 0 ∧ W (Sum.inl 3) j = 0)) (hfull : ∀ j, ¬ Z j → ∀ i : Fin 4, IsSign
    (W (Sum.inl i) j)) : IsWeighing (walshLift ν * W) weight ↔ ∀ j, ¬ Z j → (∏ i : Fin 4, W (Sum.inl i) j) = -1 := by
  sorry
theorem walshLift_support_motion {ν : Type*} [Fintype ν] [DecidableEq ν] (W : Matrix (Fin 4 ⊕ ν) (Fin 4 ⊕ ν) ℝ) (Z : (Fin 4 ⊕ ν) → Prop) (hfull : ∀ j, ¬ Z j → ∀ i : Fin 4, IsSign (W (Sum.inl i) j)) (hprod : ∀ j, ¬ Z j →
    (∏ i : Fin 4, W (Sum.inl i) j) = -1) : ∀ i j, ¬ (∃ k : Fin 4, i = Sum.inl k ∧ Z j) → ((walshLift ν * W) i j = 0 ↔ W i j = 0) := by
  sorry
theorem repetition_partialHadamard {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] (K : Matrix ι ι ℝ) (hK : IsHadamard K) : IsPartialHadamard (fun i (j : ι × κ) => K i j.1) := by
  sorry
theorem odd_repetition_unextendible {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ] (hodd : Odd (Fintype.card κ)) (K : Matrix ι ι ℝ) (hK : IsHadamard K) : ¬ ∃ f : (ι × κ) → ℝ, (∀ j, IsSign (f j)) ∧ (∀
    i, ∑ j : ι × κ, K i j.1 * f j = 0) := by
  sorry
theorem seedTwelve_hadamard : Matrix.IsHadamard seedTwelve := by
  sorry
theorem eight_missing_rows_obstruction : (∃ X : Matrix (Fin 4) (Fin 4 × Fin 3) ℝ, IsPartialHadamard X ∧ ¬ ∃ f : (Fin 4 × Fin 3) → ℝ, (∀ j, IsSign (f j)) ∧ (∀ i, ∑ j : Fin 4 × Fin 3, X i j * f j = 0)) ∧ (∃ H : Matrix (Fin
    12) (Fin 12) ℝ, Matrix.IsHadamard H) := by
  sorry
theorem witnessBudget_eq_residual {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (P : Matrix ι κ ℝ) (f : κ → ℤ) : witnessBudget P f = dotProduct (fun j => (f j : ℝ)) (((Fintype.card κ : ℝ) • (1 : Matrix κ κ ℝ) -
    Pᵀ * P).mulVec (fun j => (f j : ℝ))) := by
  sorry
theorem weighted_odd_witness_budget {ι κ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] [Fintype τ] [DecidableEq τ] (P : Matrix ι κ ℝ) (Q : Matrix τ κ ℝ) (S : Finset ι) (hP : IsPartialHadamard P) (hA :
    IsPartialHadamard (retainAndInsert P Q S)) (f : κ → ℤ) (hf : Odd (∑ j, f j)) : 0 ≤ witnessBudget P f ∧ (Fintype.card τ : ℝ) ≤ witnessBudget P f + ∑ i ∈ Sᶜ, (∑ j, P i j * (f j : ℝ))^2 ∧ (S.card + Fintype.card τ =
    Fintype.card κ → (Fintype.card κ : ℝ) - Fintype.card ι - witnessBudget P f ≤ ∑ i ∈ Sᶜ, ((∑ j, P i j * (f j : ℝ))^2 - 1)) := by
  sorry
theorem codimension_three_completion_of_card {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (hcard : Fintype.card κ = Fintype.card ι + 3) (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (hdiv : 4 ∣
    Fintype.card κ) : ∃ (L : Matrix κ κ ℝ) (rows : ι ↪ κ), Matrix.IsHadamard L ∧ ∀ i j, L (rows i) j = P i j := by
  sorry
theorem codimension_le_three_completion {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ] (r : ℕ) (hr : r ≤ 3) (hcard : Fintype.card κ = Fintype.card ι+r) (hdiv : 4 ∣ Fintype.card κ) (P :
    Matrix ι κ ℝ) (hP : IsPartialHadamard P) : ∃ (L : Matrix κ κ ℝ) (rows : ι ↪ κ), Matrix.IsHadamard L ∧ ∀ i j, L (rows i) j = P i j := by
  sorry
theorem odd_block_exchange_budget {ι κ τ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ] [Fintype τ] [DecidableEq τ] (hodd : Odd (Fintype.card κ)) (hs : 1 < Fintype.card κ) (K : Matrix ι ι ℝ) (hK :
    IsHadamard K) (Q : Matrix τ (ι × κ) ℝ) (S : Finset ι) (hA : IsPartialHadamard (retainAndInsert (fun i (j : ι × κ) => K i j.1) Q S)) : (Fintype.card τ : ℝ) ≤ (Sᶜ.card : ℝ) * (Fintype.card κ : ℝ)^2 ∧ (S.card +
    Fintype.card τ = Fintype.card ι * Fintype.card κ → ⌈(Fintype.card ι : ℝ) / ((Fintype.card κ : ℝ)+1)⌉₊ ≤ Sᶜ.card) := by
  sorry
theorem witnessBudget_mod_eight {ι κ : Type*} [Fintype ι] [Fintype κ] (P : Matrix ι κ ℝ) (hP : IsSignMatrix P) (f : κ → ℤ) (hf : Odd (∑ j, f j)) (hdiv : 4 ∣ Fintype.card κ) : ∃ t : ℤ, witnessBudget P f = (Fintype.card κ
    : ℝ)-Fintype.card ι+8*t := by
  sorry
theorem small_defect_budget {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (f : κ → ℤ) (hf : Odd (∑ j, f j)) (hdiv : 4 ∣ Fintype.card κ) (d : ℕ) (hd : d ≤
    7) (hcard : Fintype.card κ=Fintype.card ι+d) : (d : ℝ) ≤ witnessBudget P f := by
  sorry
theorem defect_eight_zero : ∃ (P : Matrix (Fin 4) (Fin 4 × Fin 3) ℝ) (f : (Fin 4 × Fin 3) → ℤ), IsPartialHadamard P ∧ Odd (∑ j, f j) ∧ witnessBudget P f=0 := by
  sorry
theorem even_order_defect_two_completion {n : ℕ} (hn : 2 ≤ n) (heven : Even n) (P : Matrix (Fin (n - 2)) (Fin n) ℝ) (hP : IsPartialHadamard P) : ∃ (H : Matrix (Fin n) (Fin n) ℝ) (rows : Fin (n - 2) ↪ Fin n),
    Matrix.IsHadamard H ∧ ∀ i j, H (rows i) j = P i j := by
  sorry
def residualGram {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ ℝ) : Matrix κ κ ℝ :=
  (Fintype.card κ : ℝ) • 1 - P.transpose * P
theorem residual_factor_completion_iff {δ ι : Type*} [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [Nonempty δ] (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsSignMatrix P) : (∃ B : Matrix δ (δ ⊕ ι) ℝ, IsSignMatrix B ∧
    B.transpose * B = residualGram P) ↔ ∃ H : Matrix (δ ⊕ ι) (δ ⊕ ι) ℝ, Matrix.IsHadamard H ∧ ∀ i j, H (Sum.inr i) j = P i j := by
  sorry
theorem residualGram_structure {δ ι : Type*} [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [Nonempty δ] (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P) : (residualGram P).PosSemidef ∧ (residualGram P).rank
    = Fintype.card δ ∧ residualGram P * residualGram P = (Fintype.card (δ ⊕ ι) : ℝ) • residualGram P := by
  sorry
theorem residualGram_diagonal {δ ι : Type*} [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsSignMatrix P) (j : δ ⊕ ι) : residualGram P j j = Fintype.card δ := by
  sorry
theorem residualGram_offDiagonal_parity {δ ι : Type*} [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsSignMatrix P) (heven : Even (Fintype.card (δ ⊕ ι))) (i j : δ ⊕ ι) (hij : i ≠
    j) : ∃ z : ℤ, residualGram P i j = (Fintype.card δ : ℝ) + 2 * z := by
  sorry
def quaternionMix {G : Type*} (a b c d : ℤ) (A : Fin 4 → G → ℤ) : Fin 4 → G → ℤ :=
  ![fun x => a * A 0 x + b * A 1 x + c * A 2 x + d * A 3 x,
    fun x => -b * A 0 x + a * A 1 x - d * A 2 x + c * A 3 x,
    fun x => -c * A 0 x + d * A 1 x + a * A 2 x - b * A 3 x,
    fun x => -d * A 0 x - c * A 1 x + b * A 2 x + a * A 3 x]
def cyclicNorm {G : Type*} [Fintype G] [Sub G] (A : Fin 4 → G → ℤ) (k : G) : ℤ :=
  ∑ x, ∑ i, A i x * A i (x - k)
def CyclicNormSolution (m : ℕ) [NeZero m] (t : ℤ) : Prop :=
  ∃ A : Fin 4 → ZMod m → ℤ, (∀ i x, (A i x : ZMod 2) = 1) ∧
    ∀ k, cyclicNorm A k = if k = 0 then 4 * t else 0
theorem cyclicNorm_odd_multiplier {m : ℕ} [NeZero m] {t : ℤ} (h : CyclicNormSolution m t) (s : ℕ) (hs : (s : ZMod 2) = 1) : CyclicNormSolution m ((s : ℤ) * t) := by
  sorry
def characterAnsatz {G : Type*} [Zero G] [DecidableEq G] (L : G → ℤ)
    (u v w : Fin 4 → ℤ) (i : Fin 4) (x : G) : ℤ :=
  u i * L x + (if x = 0 then v i else 0) + 2 * w i
theorem odd_character_scalar_equation_impossible {m : ℕ} (hm : (m : ZMod 2) = 1) (u v w : Fin 4 → ℤ) (hu : ∀ i, (u i : ZMod 2) = 1) (hv : ∀ i, (v i : ZMod 2) = 1) : (∑ i, u i ^ 2) ≠ 4 * ∑ i, (w i * v i + (m : ℤ) * w i ^
    2) := by
  sorry
theorem zero_aligned_character_ansatz_impossible {m : ℕ} [NeZero m] (hm : 1 < m) (hodd : (m : ZMod 2) = 1) (L : ZMod m → ℤ) (hzero : L 0 = 0) (hL : ∑ x, L x = 0) (henergy : ∑ x, L x ^ 2 = (m : ℤ) - 1) (u v w : Fin 4 → ℤ)
    (hu : ∀ i, (u i : ZMod 2) = 1) (hv : ∀ i, (v i : ZMod 2) = 1) : ¬ ∃ c : ℤ, ∀ k, cyclicNorm (characterAnsatz L u v w) k = if k = 0 then c else 0 := by
  sorry
theorem zero_aligned_norm_obstruction {m : ℕ} [NeZero m] (hm : 1 < m) (hodd : (m : ZMod 2) = 1) (L : ZMod m → ℤ) (hzero : L 0 = 0) (hcharacter : ∀ k, (∑ x, L x * L (x - k)) = (m : ℤ) * (if k = 0 then 1 else 0) - 1) (u v
    w : Fin 4 → ℤ) (hu : ∀ i, (u i : ZMod 2) = 1) (hv : ∀ i, (v i : ZMod 2) = 1) : ¬ ∃ c : ℤ, ∀ k, cyclicNorm (characterAnsatz L u v w) k = if k = 0 then c else 0 := by
  sorry
def tensorFrame {ι κ τ : Type*} (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) :
    Matrix (ι × τ) (κ × τ) ℝ := fun i j => P i.1 j.1 * H i.2 j.2
def fiberLift {ι κ τ : Type*} (P : Matrix ι κ ℝ) (h : τ → ℝ) : Matrix ι (κ × τ) ℝ :=
  fun i j => P i j.1 * h j.2
def HasAugmentingExchange {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (k : ℕ) : Prop :=
  ∃ D : Finset ι, D.card = k ∧ ∃ V : Matrix (Fin (k + 1)) κ ℝ,
    IsPartialHadamard V ∧ ∀ i, i ∉ D → ∀ a, ∑ j, P i j * V a j = 0
noncomputable def exchangeCost {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : Matrix ι κ ℝ) : WithTop ℕ :=
  ⨅ k : {k : ℕ // HasAugmentingExchange P k}, (k.val : WithTop ℕ)
def exchangeFrame {ι κ : Type*} [DecidableEq ι] (P : Matrix ι κ ℝ)
    (D : Finset ι) {k : ℕ} (V : Matrix (Fin (k + 1)) κ ℝ) :
    Matrix ({i : ι // i ∉ D} ⊕ Fin (k + 1)) κ ℝ :=
  Sum.elim (fun i => P i.val) V
def NoSignExtension {ι κ : Type*} [Fintype κ] (P : Matrix ι κ ℝ) : Prop :=
  ¬ ∃ f : κ → ℝ, (∀ j, IsSign (f j)) ∧ ∀ i, ∑ j, P i j * f j = 0
theorem tensor_exchangeCost_le {ι κ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype τ] [DecidableEq τ] [Nonempty τ] (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H) : exchangeCost (tensorFrame P H) ≤
    exchangeCost P := by
  sorry
theorem tensor_noSignExtension {ι κ τ : Type*} [Fintype κ] [Fintype τ] [DecidableEq τ] [Nonempty τ] (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H) (hP : NoSignExtension P) : NoSignExtension (tensorFrame P H) := by
  sorry
def coordinateFunctional {K ι : Type*} [Field K] (V : Submodule K (ι → K)) (i : ι) :
    Module.Dual K V := (LinearMap.proj i).comp V.subtype
def IsCubeVector {K ι : Type*} [One K] [Neg K] (v : ι → K) : Prop :=
  ∀ i, v i = 1 ∨ v i = -1
noncomputable def cubeCandidates {K ι : Type*} [Field K] [Fintype ι]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K)) : Finset V := by
  classical
  exact (Finset.univ.image (fun b : I → Bool => e.symm (fun j => if b j then 1 else -1))).filter
    (fun v => IsCubeVector v.val)
noncomputable def normalizedCubeCandidates {K ι : Type*} [Field K] [Fintype ι]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K)) (j : I) : Finset V := by
  classical
  exact (cubeCandidates e).filter (fun v => v.val j.val = 1)
noncomputable def normalizedInformationSeed {K ι : Type*} [Field K]
    {I : Finset ι} (j : I) (b : {k : I // k ≠ j} → Bool) : I → K := by
  classical
  exact fun k => if h : k = j then 1 else if b ⟨k, h⟩ then 1 else -1
noncomputable def normalizedInformationSearch {K ι : Type*} [Field K] [Fintype ι]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K)) (j : I) : Finset V := by
  classical
  exact (Finset.univ.image (fun b : {k : I // k ≠ j} → Bool =>
    e.symm (normalizedInformationSeed j b))).filter (fun v => IsCubeVector v.val)
noncomputable def informationMatrix {K ι : Type*} [Field K]
    {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K)) :
    Matrix ι I K := by
  classical
  exact fun i j => (e.symm (Pi.single j 1)).val i
theorem exists_information_coordinates.{u, v} {K : Type u} {ι : Type v} [Field K] [Fintype ι] (V : Submodule K (ι → K)) : ∃ (J : Type v) (_ : Fintype J) (a : J → ι), Function.Injective a ∧ Fintype.card J = Module.finrank
    K V ∧ Function.Injective (fun v : V => fun j : J => v.val (a j)) := by
  sorry
theorem normalizedCubeCandidates_cover {K ι : Type*} [Field K] [Fintype ι] {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K)) (he : ∀ v j, e v j = v.val j.val) (j : I) (v : V) (hv : IsCubeVector v.val) : v ∈
    normalizedCubeCandidates e j ∨ -v ∈ normalizedCubeCandidates e j := by
  sorry
theorem normalizedCubeCandidates_card_le {K ι : Type*} [Field K] [CharZero K] [Fintype ι] {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K)) (he : ∀ v j, e v j = v.val j.val) (j : I) :
    (normalizedCubeCandidates e j).card ≤ 2 ^ (I.card - 1) := by
  sorry
theorem normalizedInformationSearch_eq {K ι : Type*} [Field K] [Fintype ι] {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K)) (he : ∀ v j, e v j = v.val j.val) (j : I) : normalizedInformationSearch e j =
    normalizedCubeCandidates e j := by
  sorry
theorem normalizedInformationSearch_card_le {K ι : Type*} [Field K] [Fintype ι] {V : Submodule K (ι → K)} {I : Finset ι} (e : V ≃ₗ[K] (I → K)) (j : I) : (normalizedInformationSearch e j).card ≤ 2 ^ (I.card - 1) := by
  sorry
theorem exists_cube_enumeration {K ι : Type*} [Field K] [Fintype ι] (V : Submodule K (ι → K)) : ∃ C : Finset V, (∀ v : V, v ∈ C ↔ IsCubeVector v.val) ∧ C.card ≤ 2 ^ Module.finrank K V := by
  sorry
theorem information_coordinate_enumeration {K ι : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι] (V : Submodule K (ι → K)) : ∃ I : Finset ι, I.card = Module.finrank K V ∧ ∃ e : V ≃ₗ[K] (I → K), (∀ v j, e v j =
    v.val j.val) ∧ (∀ v : V, v ∈ cubeCandidates e ↔ IsCubeVector v.val) ∧ (cubeCandidates e).card ≤ 2 ^ Module.finrank K V ∧ (∀ j : I, Fintype.card ({k : I // k ≠ j} → Bool) = 2 ^ (Module.finrank K V - 1) ∧
    (normalizedInformationSearch e j).card ≤ 2 ^ (Module.finrank K V - 1) ∧ ∀ v : V, IsCubeVector v.val → v ∈ normalizedInformationSearch e j ∨ -v ∈ normalizedInformationSearch e j) ∧ (∀ b i, (e.symm b).val i = ∑ j,
    informationMatrix e i j * b j) := by
  sorry
def duplicationMap {ι J : Type*} (a : ι → J) (s : ι → ℝ) : (J → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun x i := s i * x (a i)
  map_add' x y := by funext i; simp [mul_add]
  map_smul' c x := by funext i; simp [smul_eq_mul]; ring
theorem cubeCandidates_saturated {ι : Type*} [Fintype ι] {V : Submodule ℝ (ι → ℝ)} {I : Finset ι} (e : V ≃ₗ[ℝ] (I → ℝ)) (hcard : (cubeCandidates e).card = 2 ^ I.card) : ∀ x : I → ℝ, IsCubeVector x → IsCubeVector (e.symm
    x).val := by
  sorry
theorem maximum_cube_signed_coordinates {ι : Type*} [Fintype ι] {V : Submodule ℝ (ι → ℝ)} {I : Finset ι} (e : V ≃ₗ[ℝ] (I → ℝ)) (he : ∀ v j, e v j = v.val j.val) (hcard : (cubeCandidates e).card = 2 ^ I.card) : ∃ a : ι →
    I, Function.Surjective a ∧ ∃ s : ι → ℝ, IsCubeVector s ∧ ∀ x : I → ℝ, ∀ i, (e.symm x).val i = s i * x (a i) := by
  sorry
theorem duplication_space_dimension {ι J : Type*} [Fintype J] (a : ι → J) (s : ι → ℝ) (ha : Function.Surjective a) (hs : IsCubeVector s) : Module.finrank ℝ (LinearMap.range (duplicationMap a s)) = Fintype.card J := by
  sorry
theorem duplication_space_maximum {ι J : Type*} [Fintype ι] [Fintype J] (V : Submodule ℝ (ι → ℝ)) (a : ι → J) (s : ι → ℝ) (ha : Function.Surjective a) (hs : IsCubeVector s) (hV : V = LinearMap.range (duplicationMap a s))
    {I : Finset ι} (e : V ≃ₗ[ℝ] (I → ℝ)) (he : ∀ v j, e v j = v.val j.val) : (cubeCandidates e).card = 2 ^ Module.finrank ℝ V := by
  sorry
theorem maximum_cube_iff_signed_duplication {ι : Type*} [Fintype ι] (V : Submodule ℝ (ι → ℝ)) : (∃ I : Finset ι, I.card = Module.finrank ℝ V ∧ ∃ e : V ≃ₗ[ℝ] (I → ℝ), (∀ v j, e v j = v.val j.val) ∧ (cubeCandidates e).card
    = 2 ^ I.card) ↔ (∃ I : Finset ι, I.card = Module.finrank ℝ V ∧ ∃ a : ι → I, Function.Surjective a ∧ ∃ s : ι → ℝ, IsCubeVector s ∧ V = LinearMap.range (duplicationMap a s)) := by
  sorry
noncomputable def blockIndicator {κ J : Type*} (a : κ → J) (s : κ → ℝ) (j : J) : κ → ℝ := by
  classical
  exact fun i => if a i = j then s i else 0
noncomputable def blockSize {κ J : Type*} [Fintype κ] (a : κ → J) (j : J) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => a i = j)).card
theorem residual_blocks_equal_size {δ ι J : Type*} [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [Nonempty δ] [DecidableEq J] (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P) (a : (δ ⊕ ι) → J) (s : (δ ⊕ ι) →
    ℝ) (ha : Function.Surjective a) (hs : IsCubeVector s) (hspace : LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s)) (j k : J) : blockSize a j = blockSize a k := by
  sorry
theorem residual_block_size_quotient {δ ι J : Type*} [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [Nonempty δ] [DecidableEq J] (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P) (a : (δ ⊕ ι) → J) (s : (δ ⊕ ι)
    → ℝ) (ha : Function.Surjective a) (hs : IsCubeVector s) (hspace : LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s)) (j : J) : (blockSize a j : ℝ) = (Fintype.card (δ ⊕ ι) : ℝ) / (Fintype.card δ : ℝ) := by
  sorry
theorem duplication_residual_completion_iff {δ ι J : Type*} [Fintype δ] [Fintype ι] [Fintype J] [DecidableEq δ] [DecidableEq ι] [DecidableEq J] [Nonempty δ] (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P) (a : (δ ⊕
    ι) → J) (s : (δ ⊕ ι) → ℝ) (ha : Function.Surjective a) (hs : IsCubeVector s) (hspace : LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s)) : (∃ H : Matrix (δ ⊕ ι) (δ ⊕ ι) ℝ, Matrix.IsHadamard H ∧ ∀ i j,
    H (Sum.inr i) j = P i j) ↔ ∃ Q : Matrix J J ℝ, Matrix.IsHadamard Q := by
  sorry
theorem partial_kernel_dimension_sum {δ ι : Type*} [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [Nonempty (δ ⊕ ι)] (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P) : Module.finrank ℝ (LinearMap.ker
    P.mulVecLin) = Fintype.card δ := by
  sorry
theorem maximum_residual_cube_completion {δ ι : Type*} [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [Nonempty (δ ⊕ ι)] (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P) (hmax : ∃ T : Finset (δ ⊕ ι), T.card =
    Module.finrank ℝ (LinearMap.ker P.mulVecLin) ∧ ∃ e : (LinearMap.ker P.mulVecLin) ≃ₗ[ℝ] (T → ℝ), (∀ v j, e v j = v.val j.val) ∧ (cubeCandidates e).card = 2 ^ T.card) : ∃ I : Finset (δ ⊕ ι), I.card = Module.finrank ℝ
    (LinearMap.ker P.mulVecLin) ∧ I.card = Fintype.card δ ∧ ∃ a : (δ ⊕ ι) → I, Function.Surjective a ∧ ∃ s : (δ ⊕ ι) → ℝ, IsCubeVector s ∧ LinearMap.ker P.mulVecLin = LinearMap.range (duplicationMap a s) ∧ (∀ j : I,
    (blockSize a j : ℝ) = (Fintype.card (δ ⊕ ι) : ℝ) / (I.card : ℝ)) ∧ ((∃ H : Matrix (δ ⊕ ι) (δ ⊕ ι) ℝ, Matrix.IsHadamard H ∧ ∀ i j, H (Sum.inr i) j = P i j) ↔ ∃ Q : Matrix I I ℝ, Matrix.IsHadamard Q) := by
  sorry
def SpanRigidThrough {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (P : Matrix ι κ ℝ) (c : ℕ) : Prop :=
  NoSignExtension P ∧ ∀ I : Finset ι, I.card ≤ c → ∀ f : κ → ℝ,
    IsCubeVector f → (∀ i, i ∉ I → ∑ j, P i j * f j = 0) →
      f ∈ Submodule.span ℝ (P '' (I : Set ι))
theorem tensor_row_range_of_columns {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq τ] [Nonempty τ] (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H) (f : (κ × τ) → ℝ) (hcol : ∀ b : τ, (fun j =>
    f (j, b)) ∈ LinearMap.range P.transpose.mulVecLin) : f ∈ LinearMap.range (tensorFrame P H).transpose.mulVecLin := by
  sorry
theorem tensor_fiber_orthogonal_columns {ι κ τ : Type*} [Fintype κ] [Fintype τ] [DecidableEq τ] [Nonempty τ] (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H) (f : (κ × τ) → ℝ) (i : ι) (horth : ∀ a : τ, ∑ j : κ ×
    τ, tensorFrame P H (i, a) j * f j = 0) : ∀ b : τ, (∑ j, P i j * f (j, b)) = 0 := by
  sorry
theorem span_rigid_tensor_candidate_confined {ι κ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] [Fintype τ] [DecidableEq τ] [Nonempty τ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (H : Matrix τ τ ℝ)
    (hH : IsHadamard H) (c : ℕ) (hrigid : SpanRigidThrough P c) (D : Finset (ι × τ)) (hD : D.card ≤ c) (f : (κ × τ) → ℝ) (hf : IsCubeVector f) (horth : ∀ i, i ∉ D → ∑ j, tensorFrame P H i j * f j = 0) : f ∈
    LinearMap.range ((tensorFrame P H).submatrix (fun i : D => i.val) id).transpose.mulVecLin := by
  sorry
theorem span_rigidity_excludes_tensor_exchange {ι κ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] [Fintype τ] [DecidableEq τ] [Nonempty τ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (H : Matrix τ τ
    ℝ) (hH : IsHadamard H) (c : ℕ) (hrigid : SpanRigidThrough P c) (k : ℕ) (hk : k ≤ c) : ¬ HasAugmentingExchange (tensorFrame P H) k := by
  sorry
theorem span_rigidity_tensor_cost_lower {ι κ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] [Fintype τ] [DecidableEq τ] [Nonempty τ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (H : Matrix τ τ ℝ) (hH :
    IsHadamard H) (c : ℕ) (hrigid : SpanRigidThrough P c) : (c : WithTop ℕ) < exchangeCost (tensorFrame P H) := by
  sorry
noncomputable def halfOverlapWitness {κ : Type*} (u v : κ → ℝ) (σ : ℝ) : κ → ℝ :=
  fun j => (u j + σ * v j) / 2
def HalfCorrelationPattern (N σ u v : ℝ) : Prop :=
  (u = 0 ∧ |v| = N) ∨ (v = 0 ∧ |u| = N) ∨ (|u| = N / 2 ∧ v = σ * u)
theorem shared_half_projection_card_le_two {ν κ : Type*} [Fintype ν] [DecidableEq ν] [Fintype κ] (V : Matrix ν κ ℝ) (N : ℝ) (hN : 0 < N) (hV : V * V.transpose = N • 1) (w : κ → ℝ) (hw : ∑ j, w j ^ 2 = N / 2) (hproj : ∀
    i, |∑ j, V i j * w j| = N / 2) : Fintype.card ν ≤ 2 := by
  sorry
theorem partial_row_pair_witness_norm {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (i j : ι) (hij : i ≠ j) (σ : ℝ) (hσ : IsSign σ) : (∑ k, halfOverlapWitness (P i)
    (P j) σ k ^ 2) = (Fintype.card κ : ℝ) / 2 := by
  sorry
theorem halfCorrelationPattern_flat_rows {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ] (H : Matrix τ τ ℝ) (hH : IsHadamard H) (a b : τ) (N σ α β : ℝ) (hN : 0 < N) (hσ : IsSign σ) (hpattern : ∀ k,
    HalfCorrelationPattern N σ (α * H a k) (β * H b k)) : |α + σ * β| = N := by
  sorry
theorem tensor_fiber_correlation {ι κ τ : Type*} [Fintype κ] [Fintype τ] [DecidableEq τ] (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H) (f : (κ × τ) → ℝ) (i : ι) (a : τ) (α : ℝ) (hcol : ∀ b, (∑ j, P i j * f
    (j, b)) = α * H a b) : (∑ j : κ × τ, tensorFrame P H (i, a) j * f j) = α * Fintype.card τ := by
  sorry
theorem hadamard_single_fiber_reconstruction {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ] (H : Matrix τ τ ℝ) (hH : IsHadamard H) (a : τ) (u : τ → ℝ) (horth : ∀ c, c ≠ a → ∑ d, H c d * u d = 0) : ∃ α : ℝ, ∀ d, u d
    = α * H a d := by
  sorry
theorem tensor_correlation_as_fiber {ι κ τ : Type*} [Fintype κ] [Fintype τ] (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (f : (κ × τ) → ℝ) (i : ι) (a : τ) : (∑ j : κ × τ, tensorFrame P H (i, a) j * f j) = ∑ b, H a b * ∑ j, P i
    j * f (j, b) := by
  sorry
theorem tensor_single_deleted_fiber {ι κ τ : Type*} [Fintype κ] [Fintype τ] [DecidableEq τ] [Nonempty τ] (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H) (f : (κ × τ) → ℝ) (i : ι) (a : τ) (horth : ∀ c, c ≠ a → ∑
    j, tensorFrame P H (i, c) j * f j = 0) : ∃ α : ℝ, ∀ d, (∑ j, P i j * f (j, d)) = α * H a d := by
  sorry
theorem two_deleted_tensor_correlations {ι κ τ : Type*} [Fintype κ] [Fintype τ] [DecidableEq ι] [DecidableEq τ] [Nonempty τ] (P : Matrix ι κ ℝ) (H : Matrix τ τ ℝ) (hH : IsHadamard H) (f : (κ × τ) → ℝ) (i j : ι) (hij : i
    ≠ j) (a b : τ) (horth : ∀ r, r ∉ ({(i, a), (j, b)} : Finset (ι × τ)) → ∑ k, tensorFrame P H r k * f k = 0) : ∃ α β : ℝ, (∀ d, (∑ k, P i k * f (k, d)) = α * H a d) ∧ (∀ d, (∑ k, P j k * f (k, d)) = β * H b d) := by
  sorry
theorem two_distinct_rows_half_overlap_bound {ι κ τ ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] [Fintype τ] [DecidableEq τ] [Nonempty τ] [Fintype ν] [DecidableEq ν] (P : Matrix ι κ ℝ) (hP :
    IsPartialHadamard P) (H : Matrix τ τ ℝ) (hH : IsHadamard H) (i j : ι) (hij : i ≠ j) (a b : τ) (σ : ℝ) (hσ : IsSign σ) (hpattern : ∀ x : κ → ℝ, IsCubeVector x → (∀ r, r ≠ i → r ≠ j → ∑ k, P r k * x k = 0) →
    HalfCorrelationPattern (Fintype.card κ) σ (∑ k, P i k * x k) (∑ k, P j k * x k)) (V : Matrix ν (κ × τ) ℝ) (hV : IsPartialHadamard V) (hret : ∀ r, r ∉ ({(i, a), (j, b)} : Finset (ι × τ)) → ∀ v, ∑ k, tensorFrame P H r
    k * V v k = 0) : Fintype.card ν ≤ 2 := by
  sorry
def OriginalCandidate {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (P : Matrix ι κ ℝ) (I : Finset ι) (x : κ → ℝ) : Prop :=
  IsCubeVector x ∧ ∀ i, i ∉ I → ∑ j, P i j * x j = 0
def SameSignLine {κ : Type*} (x y : κ → ℝ) : Prop := x = y ∨ x = -y
def HalfOverlapCorrelationConditions {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (P : Matrix ι κ ℝ) : Prop :=
  NoSignExtension P ∧
    (∀ i x, OriginalCandidate P {i} x → x ∈ LinearMap.range P.transpose.mulVecLin) ∧
    ∀ i j, i ≠ j → ∃ σ : ℝ, IsSign σ ∧ ∀ x, OriginalCandidate P {i, j} x →
      HalfCorrelationPattern (Fintype.card κ) σ (∑ k, P i k * x k) (∑ k, P j k * x k)
def HalfOverlapExtraLines {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (P : Matrix ι κ ℝ) (i j : ι) : Prop :=
  ∃ x y : κ → ℝ, ∃ σ : ℝ, OriginalCandidate P {i, j} x ∧ OriginalCandidate P {i, j} y ∧
    IsSign σ ∧ (∑ k, x k * y k) = 0 ∧
    (∑ k, P i k * x k) = (Fintype.card κ : ℝ) / 2 ∧
    (∑ k, P j k * x k) = σ * ((Fintype.card κ : ℝ) / 2) ∧
    (∑ k, P i k * y k) = (Fintype.card κ : ℝ) / 2 ∧
    (∑ k, P j k * y k) = σ * ((Fintype.card κ : ℝ) / 2) ∧
    ∀ z, OriginalCandidate P {i, j} z →
      SameSignLine z (P i) ∨ SameSignLine z (P j) ∨ SameSignLine z x ∨ SameSignLine z y
def HalfOverlapPairStructure {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (P : Matrix ι κ ℝ) : Prop :=
  NoSignExtension P ∧
    (∀ i x, OriginalCandidate P {i} x → SameSignLine x (P i)) ∧
    ∀ i j, i ≠ j →
      (∀ x, OriginalCandidate P {i, j} x → SameSignLine x (P i) ∨ SameSignLine x (P j)) ∨
        HalfOverlapExtraLines P i j
theorem sameSignLine_correlation_pattern {ι κ : Type*} [Fintype κ] (P : Matrix ι κ ℝ) (i j : ι) (N σ : ℝ) (x y : κ → ℝ) (hline : SameSignLine x y) (hpattern : HalfCorrelationPattern N σ (∑ k, P i k * y k) (∑ k, P j k * y
    k)) : HalfCorrelationPattern N σ (∑ k, P i k * x k) (∑ k, P j k * x k) := by
  sorry
theorem half_overlap_structure_implies_correlations {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (hstruct : HalfOverlapPairStructure P) :
    HalfOverlapCorrelationConditions P := by
  sorry
theorem single_original_deletion_card_bound {ι κ τ ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] [Fintype τ] [DecidableEq τ] [Nonempty τ] [Fintype ν] [DecidableEq ν] (P : Matrix ι κ ℝ) (hP :
    IsPartialHadamard P) (H : Matrix τ τ ℝ) (hH : IsHadamard H) (i : ι) (D : Finset (ι × τ)) (hD : ∀ r ∈ D, r.1 = i) (hsingle : ∀ x, OriginalCandidate P {i} x → x ∈ LinearMap.range P.transpose.mulVecLin) (V : Matrix ν (κ
    × τ) ℝ) (hV : IsPartialHadamard V) (hret : ∀ r, r ∉ D → ∀ v, ∑ k, tensorFrame P H r k * V v k = 0) : Fintype.card ν ≤ D.card := by
  sorry
theorem half_overlap_correlation_excludes_exchange {ι κ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] [Fintype τ] [DecidableEq τ] [Nonempty τ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (H : Matrix τ
    τ ℝ) (hH : IsHadamard H) (hcond : HalfOverlapCorrelationConditions P) (k : ℕ) (hk : k ≤ 2) : ¬ HasAugmentingExchange (tensorFrame P H) k := by
  sorry
theorem half_overlap_pair_structure_excludes_exchange {ι κ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] [Fintype τ] [DecidableEq τ] [Nonempty τ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (H :
    Matrix τ τ ℝ) (hH : IsHadamard H) (hstruct : HalfOverlapPairStructure P) (k : ℕ) (hk : k ≤ 2) : ¬ HasAugmentingExchange (tensorFrame P H) k := by
  sorry
theorem half_overlap_tensor_cost_three {ι κ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] [Fintype τ] [DecidableEq τ] [Nonempty τ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (H : Matrix τ τ ℝ) (hH :
    IsHadamard H) (hstruct : HalfOverlapPairStructure P) (hcost : exchangeCost P = 3) : exchangeCost (tensorFrame P H) = 3 := by
  sorry
def encodedSign (m j : ℕ) : ℤ := if m.testBit j then -1 else 1
def encodedIntFrame {r n : ℕ} (masks : Fin r → ℕ) : Matrix (Fin r) (Fin n) ℤ :=
  fun i j => encodedSign (masks i) j.val
def encodedRealFrame {r n : ℕ} (masks : Fin r → ℕ) : Matrix (Fin r) (Fin n) ℝ :=
  (encodedIntFrame masks).map (Int.castRingHom ℝ)
theorem encodedRealFrame_partialHadamard {r n : ℕ} (masks : Fin r → ℕ) (hgram : (encodedIntFrame masks : Matrix (Fin r) (Fin n) ℤ) * (encodedIntFrame masks).transpose = (n : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) :
    IsPartialHadamard (encodedRealFrame masks : Matrix (Fin r) (Fin n) ℝ) := by
  sorry
def base24Masks : Fin 16 → ℕ :=
  ![0, 16773120, 16519104, 10359454, 7684730, 5820908, 9389414, 1547504,
    6736278, 11838780, 3701846, 13790378, 10646512, 2963882, 12892774, 5974836]
def insert24Masks : Fin 4 → ℕ := ![353924, 1104648, 2786850, 4759768]
def completion24Masks : Fin 24 → ℕ :=
  ![16773120, 16519104, 10359454, 7684730, 1547504, 6736278, 11838780,
    3701846, 13790378, 10646512, 2963882, 12892774, 5974836,
    353924, 1104648, 2786850, 4759768,
    5133676, 7583694, 9432922, 10076646, 10684492, 12653842, 15326908]
def delete24Rows : Finset (Fin 16) := {0, 5, 6}
def retained24Position : Fin 16 → Fin 24 :=
  ![0, 0, 1, 2, 3, 0, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12]
def insert24Position (i : Fin 4) : Fin 24 := ⟨13 + i.val, by omega⟩
def base24Frame : Matrix (Fin 16) (Fin 24) ℝ := encodedRealFrame base24Masks
def insert24Frame : Matrix (Fin 4) (Fin 24) ℝ := encodedRealFrame insert24Masks
def completion24Frame : Matrix (Fin 24) (Fin 24) ℝ := encodedRealFrame completion24Masks
def order24RepairIndex : ({i : Fin 16 // i ∉ delete24Rows} ⊕ Fin 4) → Fin 24 :=
  Sum.elim (fun i => retained24Position i.val) insert24Position
theorem base24Frame_partialHadamard : IsPartialHadamard base24Frame := by
  sorry
theorem insert24Frame_partialHadamard : IsPartialHadamard insert24Frame := by
  sorry
theorem completion24Frame_hadamard : Matrix.IsHadamard completion24Frame := by
  sorry
theorem base24_exchange_with_completion : HasAugmentingExchange base24Frame 3 ∧ ∃ H : Matrix (Fin 24) (Fin 24) ℝ, Matrix.IsHadamard H ∧ ∃ e : ({i : Fin 16 // i ∉ delete24Rows} ⊕ Fin 4) ↪ Fin 24, ∀ r j, H (e r) j =
    exchangeFrame base24Frame delete24Rows insert24Frame r j := by
  sorry
noncomputable def rationalRealCast : ℚ →+* ℝ :=
  @Rat.castHom ℝ inferInstance (IsStrictOrderedRing.toCharZero (R := ℝ))
def informationSelector {n q : ℕ} (a : Fin q → Fin n) : Matrix (Fin q) (Fin n) ℚ :=
  fun i j => if a i = j then 1 else 0
def base24RationalFrame : Matrix (Fin 16) (Fin 24) ℚ :=
  (encodedIntFrame base24Masks).map (Int.castRingHom ℚ)
theorem base24_tensor_partialHadamard {τ : Type*} [Fintype τ] [DecidableEq τ] (H : Matrix τ τ ℝ) (hH : IsHadamard H) : IsPartialHadamard (tensorFrame base24Frame H) := by
  sorry
theorem base24_tensor_noSignExtension {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ] (H : Matrix τ τ ℝ) (hH : IsHadamard H) : NoSignExtension (tensorFrame base24Frame H) := by
  sorry
theorem base24_tensor_exchangeCost_le_three {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ] (H : Matrix τ τ ℝ) (hH : IsHadamard H) : exchangeCost (tensorFrame base24Frame H) ≤ (3 : WithTop ℕ) := by
  sorry
theorem correlation_conditions_tensor_cost_three{ι κ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] [Fintype τ] [DecidableEq τ] [Nonempty τ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (H : Matrix τ τ
    ℝ) (hH : IsHadamard H) (hcond : HalfOverlapCorrelationConditions P) (hupper : exchangeCost P ≤ 3) : exchangeCost (tensorFrame P H) = 3 := by
  sorry
theorem correlation_conditions_exclude_base_exchange{ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (hcond : HalfOverlapCorrelationConditions P) (k : ℕ)
    (hk : k ≤ 2) : ¬ HasAugmentingExchange P k := by
  sorry
theorem correlation_conditions_base_cost_three{ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (hcond : HalfOverlapCorrelationConditions P) (hupper :
    exchangeCost P ≤ 3) : exchangeCost P = 3 := by
  sorry
def codeTrap20Masks : Fin 12 → ℕ := ![0, 965904, 1003736, 902980, 730036, 501868, 412530, 210762, 649754, 358790, 694982, 250934]
def codeTrap20Frame : Matrix (Fin 12) (Fin 20) ℝ := encodedRealFrame codeTrap20Masks
theorem codeTrap20_partialHadamard : IsPartialHadamard codeTrap20Frame := by
  sorry
theorem codeTrap20_noSignExtension : NoSignExtension codeTrap20Frame := by
  sorry
theorem codeTrap20_tensor_partialHadamard {τ : Type*} [Fintype τ] [DecidableEq τ] (H : Matrix τ τ ℝ) (hH : IsHadamard H) : IsPartialHadamard (tensorFrame codeTrap20Frame H) := by
  sorry
theorem codeTrap20_tensor_noSignExtension {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ] (H : Matrix τ τ ℝ) (hH : IsHadamard H) : NoSignExtension (tensorFrame codeTrap20Frame H) := by
  sorry
noncomputable def supportedSigns {κ : Type*} [DecidableEq κ]
    (w : κ → ℝ) (T : Finset κ) : κ → ℝ := fun j => if j ∈ T then w j else 0
noncomputable def roundedSign {κ : Type*} (v : κ → ℝ) : κ → ℝ :=
  fun j => if 0 < v j then 1 else -1
noncomputable def tripleCoordinates {κ : Type*} [Fintype κ] (v : κ → ℝ) : Finset κ :=
  Finset.univ.filter (fun j => v j = 3 ∨ v j = -3)
noncomputable def roundingBadRows {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι κ ℝ) (v : κ → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => (∑ j, P i j * roundedSign v j) ≠ 0)
theorem rounding_defect {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (v : κ → ℝ) (hv : ∀ j, v j = 1 ∨ v j = -1 ∨ v j = 3 ∨ v j = -3)
    (hker : P.mulVec v = 0) : IsCubeVector (roundedSign v) ∧ (∀ j, v j = roundedSign v j + 2 * supportedSigns (roundedSign v) (tripleCoordinates v) j) ∧ (∀ i, (∑ j, P i j * roundedSign v j) = -2 * (∑ j, P i j *
    supportedSigns (roundedSign v) (tripleCoordinates v) j)) ∧ (Odd (tripleCoordinates v).card → ∀ i, (∑ j, P i j * roundedSign v j) ≠ 0) ∧ (Even (tripleCoordinates v).card → 4 * ((roundingBadRows P v).card : ℝ) ≤
    (Fintype.card κ : ℝ) * (tripleCoordinates v).card) ∧ (roundingBadRows P v).card ≤ Fintype.card ι ∧ (∀ i, i ∉ roundingBadRows P v → (∑ j, P i j * roundedSign v j) = 0) := by
  sorry
theorem rounded_row_repair {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (v : κ → ℝ) : IsPartialHadamard (exchangeFrame P (roundingBadRows P v) (fun (_i : Fin 1) j =>
    roundedSign v j)) := by
  sorry
theorem rounding_defect_bound {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ] (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) (v : κ → ℝ) (hv : ∀ j, v j = 1 ∨ v j = -1 ∨ v j = 3 ∨ v j =
    -3) (hker : P.mulVec v = 0) (ht : Even (tripleCoordinates v).card) : ((roundingBadRows P v).card : ℝ) ≤ min (Fintype.card ι : ℝ) ((Fintype.card κ : ℝ) * (tripleCoordinates v).card / 4) := by
  sorry
theorem base24_no_exchange_le_two (k : ℕ) (hk : k ≤ 2) : ¬ HasAugmentingExchange base24Frame k := by
  sorry
theorem base24_exchangeCost_eq_three : exchangeCost base24Frame = 3 := by
  sorry
theorem base24_tensor_exchangeCost_eq_three {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ] (H : Matrix τ τ ℝ) (hH : IsHadamard H) : exchangeCost (tensorFrame base24Frame H) = 3 := by
  sorry
theorem base24_sylvester_family (a : ℕ) : ∃ H : Matrix (Fin (2 ^ a)) (Fin (2 ^ a)) ℝ, IsHadamard H ∧ IsPartialHadamard (tensorFrame base24Frame H) ∧ NoSignExtension (tensorFrame base24Frame H) ∧ exchangeCost (tensorFrame
    base24Frame H) = 3 := by
  sorry
theorem exists_hadamard_power_two (a : ℕ) : ∃ H : Matrix (Fin (2 ^ a)) (Fin (2 ^ a)) ℝ, IsHadamard H := by
  sorry
end CompletionTheory
namespace PhaseGeometry
open scoped ComplexConjugate Matrix
def IsFourthRoot (z : ℂ) : Prop := z=1 ∨ z= -1 ∨ z=Complex.I ∨ z= -Complex.I
def complexRowGram {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) : ℂ := ∑ j,M i j*conj (M k j)
def IsQuaternaryHadamard {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) : Prop := (∀ i j,IsFourthRoot (Q i j)) ∧ ∀ i k,complexRowGram Q i k=if i=k then (n : ℂ) else 0
def phaseTransform {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (r c : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i j => r i*F i j*c j
def permuteMatrix {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s t : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ := fun i j => F (s i) (t j)
def rowRoundingError {n : ℕ} (F Q : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : ℝ := ∑ j,Complex.normSq (Q i j-F i j)
def totalRoundingError {n : ℕ} (F Q : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i,rowRoundingError F Q i
noncomputable def euclideanOperatorNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A‖
def fourthPowerMatrix {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i j => (F i j)^4
noncomputable def rhoFourth {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) : ℝ := euclideanOperatorNorm (fourthPowerMatrix F)/(n : ℝ)
def signPermutationMatrix {ι : Type*} [DecidableEq ι] (s : Equiv.Perm ι) (e : ι → ℝ) : Matrix ι ι ℝ := fun i j => if j=s i then e i else 0
def IsSignedPermutation {ι : Type*} [DecidableEq ι] (J : Matrix ι ι ℝ) : Prop := ∃ s : Equiv.Perm ι,∃ e : ι → ℝ,(∀ i,e i=1 ∨ e i= -1) ∧ J=signPermutationMatrix s e
def complexRealification {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ := Matrix.fromBlocks (fun i j => (Z i j).re) (fun i j => -(Z i j).im) (fun i j => (Z i j).im) (fun i j => (Z i j).re)
def IsQuaternaryRealificationEquivalent {m : ℕ} (H : Matrix (Fin (2*m)) (Fin (2*m)) ℝ) : Prop := ∃ P Q : Matrix (Fin (2*m)) (Fin (2*m)) ℝ,IsSignedPermutation P ∧ IsSignedPermutation Q ∧ ∃ fr fc : (Fin m ⊕ Fin m) ≃ Fin (2*m),∃ B : Matrix (Fin m) (Fin m) ℂ, IsQuaternaryHadamard B ∧ (P*H*Q).submatrix fr fc=complexRealification ((1+Complex.I) • B)
theorem signed_complex_structure_criterion {m : ℕ} (H : Matrix (Fin (2*m)) (Fin (2*m)) ℝ) (hH : Matrix.IsHadamard H) : IsQuaternaryRealificationEquivalent H ↔ ∃ Jr Jc : Matrix (Fin (2*m)) (Fin (2*m)) ℝ,IsSignedPermutation Jr ∧ IsSignedPermutation Jc ∧ Jr*Jr= -1 ∧ Jc*Jc= -1 ∧ H*Jc=Jr*H := by sorry
theorem rhoFourth_le_one {n : ℕ} (hn : 0<n) (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1) : rhoFourth F ≤ 1 := by sorry
theorem rhoFourth_one_iff_quaternary_phase_equivalent {n : ℕ} (hn : 0<n) (F : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1) (horth : ∀ i k,complexRowGram F i k=if i=k then (n : ℂ) else 0) : rhoFourth F=1 ↔ ∃ r c : Fin n → ℂ,(∀ i,‖r i‖=1) ∧ (∀ j,‖c j‖=1) ∧ IsQuaternaryHadamard (phaseTransform F r c) := by sorry
theorem equivalent_quaternary_distance_lower {n : ℕ} (hn : 0<n) (F Q : Matrix (Fin n) (Fin n) ℂ) (hF : ∀ i j, ‖F i j‖=1) (hQ : ∀ i j,IsFourthRoot (Q i j)) (s t : Equiv.Perm (Fin n)) (r c : Fin n → ℂ) (hr : ∀ i,‖r i‖=1) (hc : ∀ j,‖c j‖=1) : (1-rhoFourth F)/8 ≤ totalRoundingError (phaseTransform (permuteMatrix F s t) r c) Q/(n : ℝ)^2 := by sorry
end PhaseGeometry
namespace CompletionTheory
open scoped ComplexConjugate Matrix
def complexifyRealMatrix {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ := fun i j => (Z i j : ℂ)
noncomputable def nearestSignMatrix {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j => if 0 ≤ Z i j then 1 else -1
def quarticFlatness {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i,∑ j,(Z i j^2-1)^2
noncomputable def realFlatnessThreshold (n : ℕ) : ℝ := (Real.sqrt ((n : ℝ)+2)-Real.sqrt (n : ℝ))^2
theorem real_flatness_rounding_hadamard {n : ℕ} (hn : 0<n) (hfour : 4 ∣ n) (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z*Zᵀ=(n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) (hflat : quarticFlatness Z<realFlatnessThreshold n) : Matrix.IsHadamard (nearestSignMatrix Z) := by sorry
theorem quarticFlatness_identity {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z*Zᵀ=(n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) : quarticFlatness Z=(∑ i,∑ j,Z i j^4)-(n : ℝ)^2 := by sorry
theorem realFlatnessThreshold_lower (n : ℕ) : 1/((n : ℝ)+2)<realFlatnessThreshold n := by sorry
theorem noncompletable_real_flatness_gap {n : ℕ} (hn : 0<n) (hfour : 4 ∣ n) {ι : Type*} (P : Matrix ι (Fin n) ℝ) (hP : IsSignMatrix P) (e : ι → Fin n) (hno : ¬ ∃ H : Matrix (Fin n) (Fin n) ℝ,Matrix.IsHadamard H ∧ ∀ i j,H (e i) j=P i j) (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z*Zᵀ=(n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) (hret : ∀ i j,Z (e i) j=P i j) : realFlatnessThreshold n ≤ quarticFlatness Z ∧ 1/((n : ℝ)+2)<realFlatnessThreshold n := by sorry
end CompletionTheory
namespace CompletionTheory
open scoped Matrix
def dilationCandidate {ι κ : Type*} (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (D : Matrix κ κ ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := Matrix.fromBlocks A B Bᵀ D
noncomputable def dilationParameterBlock {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ] (b : ℝ) (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (E : Matrix δ κ ℝ) (V : Matrix δ δ ℝ) : Matrix κ κ ℝ := b⁻¹ • (-(Bᵀ*Aᵀ*B)+Eᵀ*V*E)
def frameTopBlock {ι δ : Type*} (T : Matrix (ι ⊕ δ) (ι ⊕ δ) ℝ) : Matrix ι (ι ⊕ δ) ℝ := T.submatrix Sum.inl id
def frameResidualBlock {ι δ : Type*} (T : Matrix (ι ⊕ δ) (ι ⊕ δ) ℝ) : Matrix δ (ι ⊕ δ) ℝ := T.submatrix Sum.inr id
def realOfRationalMatrix {ι κ : Type*} (A : Matrix ι κ ℚ) : Matrix ι κ ℝ := fun i j => (A i j : ℝ)
theorem hadamard_seed_dilation_iff {a d : ℕ} (ha : 0<a) (A : Matrix (Fin a) (Fin a) ℝ) (hA : Matrix.IsHadamard A) (T : Matrix (Fin a ⊕ Fin d) (Fin a ⊕ Fin d) ℝ) (hT : Matrix.IsHadamard T) (D : Matrix (Fin a ⊕ Fin d) (Fin a ⊕ Fin d) ℝ) : dilationCandidate A (frameTopBlock T) D*(dilationCandidate A (frameTopBlock T) D)ᵀ= ((a+(a+d) : ℕ) : ℝ) • 1 ↔ ∃ V : Matrix (Fin d) (Fin d) ℝ,V*Vᵀ=((a+(a+d) : ℕ) : ℝ) • 1 ∧ D=dilationParameterBlock ((a+d : ℕ) : ℝ) A (frameTopBlock T) (frameResidualBlock T) V := by sorry
def modularBitSign (b : Bool) : ℤ := if b then -1 else 1
def modularRowCode {r N : ℕ} (P : Matrix (Fin r) (Fin N) ℤ) (i : Fin r) : Fin N → Bool := fun j => decide (P i j= -1)
def positiveFirstBit {N : ℕ} (x : Fin N → Bool) : Prop := ∀ j,j.val=0 → x j=false
noncomputable def modularSignCandidates {r : ℕ} (q : ℕ) (P : Matrix (Fin r) (Fin (4*q)) ℤ) :
    Finset (Fin (4*q) → Bool) := by
  classical
  exact Finset.univ.filter (fun x => positiveFirstBit x ∧
      ∀ i,(q : ℤ)∣∑ j,P i j*modularBitSign (x j))
noncomputable def exactSignCandidates {r N : ℕ} (P : Matrix (Fin r) (Fin N) ℤ) :
    Finset (Fin N → Bool) := by
  classical
  exact Finset.univ.filter (fun x => positiveFirstBit x ∧
      ∀ i,(∑ j,P i j*modularBitSign (x j))=0)
def normalizeModularRows {r q : ℕ} (hq : 0<q) (P : Matrix (Fin r) (Fin (4*q)) ℤ) : Matrix (Fin r) (Fin (4*q)) ℤ := fun i j => P i ⟨0,by omega⟩*P i j
theorem modular_row_correction {r q : ℕ} (hr : 5≤r) (hq : 0<q) (hodd : q%2=1) (P : Matrix (Fin r) (Fin (4*q)) ℤ) (hs : ∀ i j,P i j=1 ∨ P i j= -1) (hg : ∀ i j,(∑ k,P i k*P j k)=if i=j then (4*q : ℤ) else 0) : (exactSignCandidates P).card=(modularSignCandidates q P).card-r ∧ ∀ x∈modularSignCandidates q P,x∉exactSignCandidates P ↔ ∃! i : Fin r,x=modularRowCode (normalizeModularRows hq P) i := by sorry
open Module Submodule
def IsSelfOrthogonalModularCode {q N : ℕ} (C : Submodule (ZMod q) (Fin N → ZMod q)) : Prop := ∀ u∈C,∀ v∈C,(∑ j,u j*v j)=0
noncomputable def codeSignCandidates {q N : ℕ} (C : Submodule (ZMod q) (Fin N → ZMod q)) :
    Finset (Fin N → Bool) := by
  classical
  exact Finset.univ.filter (fun x => positiveFirstBit x ∧
    (fun j => (modularBitSign (x j) : ZMod q))∈C)
noncomputable def signParityClass {N : ℕ} (S : Finset (Fin N → Bool)) (ε : ℤ) :
    Finset (Fin N → Bool) := by
  classical
  exact S.filter (fun x => (∏ j,modularBitSign (x j))=ε)
def bilinearPivotHyperplane {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (B : LinearMap.BilinForm K V) (C : Submodule K V) (v : V) : Submodule K V := C ⊓ LinearMap.ker (B v)
def bilinearCodePivot {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (B : LinearMap.BilinForm K V) (C : Submodule K V) (v : V) : Submodule K V := bilinearPivotHyperplane B C v ⊔ K ∙ v
def coordinateDotForm (K : Type*) [Field K] (N : ℕ) : LinearMap.BilinForm K (Fin N → K) := dotProductBilin K K
noncomputable def signCodePivot {p : ℕ} [Fact p.Prime] (C : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (v : Fin (4*p) → Bool) : Submodule (ZMod p) (Fin (4*p) → ZMod p) := bilinearCodePivot (coordinateDotForm (ZMod p) (4*p)) C (fun j => (modularBitSign (v j) : ZMod p))
theorem five_rows_remove_code_compatibility {q : ℕ} (hq : 0<q) (hodd : q%2=1) (C : Submodule (ZMod q) (Fin (4*q) → ZMod q)) (hC : IsSelfOrthogonalModularCode C) (a : Fin 5 → Fin (4*q) → Bool) (ha : ∀ i,a i∈codeSignCandidates C) (hgram : ∀ i j,(∑ k,modularBitSign (a i k)*modularBitSign (a j k))= if i=j then (4*q : ℤ) else 0) : (∀ x∈codeSignCandidates C,∀ y∈codeSignCandidates C,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) ∧ 5≤(codeSignCandidates C).card ∧ (codeSignCandidates C).card≤4*q := by sorry
theorem modular_two_parity_bounds {q : ℕ} (hq : 3≤q) (hodd : q%2=1) (S : Finset (Fin (4*q) → Bool)) (hfirst : ∀ x∈S,positiveFirstBit x) (hmod : ∀ x∈S,∀ y∈S,(q : ℤ)∣∑ j,modularBitSign (x j)*modularBitSign (y j)) : (∀ x∈S,∀ y∈S,x≠y → (∏ j,modularBitSign (x j))=(∏ j,modularBitSign (y j)) → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) ∧ ((∃ x∈S,∃ y∈S,(∏ j,modularBitSign (x j))≠∏ j,modularBitSign (y j)) → (∀ ε : ℤ,(signParityClass S ε).card≤4) ∧ S.card≤8) ∧ (9≤S.card → ∀ x∈S,∀ y∈S,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) ∧ S.card≤4*q := by sorry
theorem modular_two_parity_bound_sharp (q : ℕ) (hq : 0<q) (hodd : q%2=1) : ∃ S : Finset (Fin (4*q) → Bool),S.card=8 ∧ (∀ x∈S,positiveFirstBit x) ∧ (∀ x∈S,∀ y∈S,(q : ℤ)∣∑ j,modularBitSign (x j)*modularBitSign (y j)) ∧ (signParityClass S 1).card=4 ∧ (signParityClass S (-1)).card=4 := by sorry
theorem self_dual_sign_code_pivot {p : ℕ} [Fact p.Prime] (C : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (v : Fin (4*p) → Bool) (hfirst : positiveFirstBit v) (hv : (fun j => (modularBitSign (v j) : ZMod p))∉C) (horth : ∀ x∈codeSignCandidates C,(∑ j,modularBitSign (x j)*modularBitSign (v j))=0) : signCodePivot C v=(coordinateDotForm (ZMod p) (4*p)).orthogonal (signCodePivot C v) ∧ Module.finrank (ZMod p) ↥(C ⊓ signCodePivot C v)=2*p-1 ∧ codeSignCandidates C ⊂ codeSignCandidates (signCodePivot C v) := by sorry
theorem terminal_code_preserving_no_new_signs {q : ℕ} (hq : 0<q) (hodd : q%2=1) (C : Submodule (ZMod q) (Fin (4*q) → ZMod q)) (a : Fin 5 → Fin (4*q) → Bool) (ha : ∀ i,a i∈codeSignCandidates C) (hgram : ∀ i j,(∑ k,modularBitSign (a i k)*modularBitSign (a j k))= if i=j then (4*q : ℤ) else 0) (hterminal : ¬∃ v : Fin (4*q) → Bool,positiveFirstBit v ∧ v∉codeSignCandidates C ∧ ∀ x∈codeSignCandidates C,(∑ j,modularBitSign (x j)*modularBitSign (v j))=0) : ∀ D : Submodule (ZMod q) (Fin (4*q) → ZMod q),IsSelfOrthogonalModularCode D → codeSignCandidates C⊆codeSignCandidates D → codeSignCandidates D=codeSignCandidates C := by sorry
def closedFourRows {N : ℕ} (P : Matrix (Fin 4) (Fin N) ℤ) : Prop := ∀ j,(∏ i,P i j)=1
def halfQuadRowCode {N : ℕ} (P : Matrix (Fin 4) (Fin N) ℤ) (i : Fin 4) : Fin N → Bool := fun j => decide ((∑ k,P k j)-2*P i j= -2)
def closedSignQuadruple {N : ℕ} (P : Matrix (Fin 4) (Fin N) ℤ) : Prop := ∃ c : ℤ,∀ j,(∏ i,P i j)=c
noncomputable def closedSignQuadrupleIndicator {N : ℕ} (P : Matrix (Fin 4) (Fin N) ℤ) : ℕ := by
  classical
  exact if closedSignQuadruple P then 1 else 0
theorem four_row_boundary_correction {q : ℕ} (hq : 0<q) (hodd : q%2=1) (P : Matrix (Fin 4) (Fin (4*q)) ℤ) (hs : ∀ i j,P i j=1 ∨ P i j= -1) (hg : ∀ i j,(∑ k,P i k*P j k)=if i=j then (4*q : ℤ) else 0) : (exactSignCandidates P).card=(modularSignCandidates q P).card-4-4*closedSignQuadrupleIndicator P := by sorry
theorem halfQuadRowCode_sign {N : ℕ} (P : Matrix (Fin 4) (Fin N) ℤ) (hs : ∀ i j,P i j=1 ∨ P i j= -1) (hclosed : closedFourRows P) (i : Fin 4) (j : Fin N) : 2*modularBitSign (halfQuadRowCode P i j)=(∑ k,P k j)-2*P i j := by sorry
def coordinateFlipSign {N : ℕ} (T : Finset (Fin N)) (j : Fin N) : ℤ := if j∈T then -1 else 1
def flipSignVector {N : ℕ} (T : Finset (Fin N)) (u : Fin N → ℤ) : Fin N → ℤ := fun j => u j*coordinateFlipSign T j
def normalizeSignCode {N : ℕ} (hN : 0<N) (u : Fin N → ℤ) : Fin N → Bool := fun j => decide (u j*u ⟨0,hN⟩= -1)
noncomputable def modularCandidatesAt {r N : ℕ} (q : ℕ) (P : Matrix (Fin r) (Fin N) ℤ) :
    Finset (Fin N → Bool) := by
  classical
  exact Finset.univ.filter (fun x => positiveFirstBit x ∧ ∀ i,(q : ℤ)∣∑ j,P i j*modularBitSign (x j))
noncomputable def columnPairCandidates {r N : ℕ} (P : Matrix (Fin r) (Fin N) ℤ) :
    Finset (Finset (Fin N)) := by
  classical
  exact (Finset.univ.powersetCard 2).filter (fun T => |∑ i,∏ j∈T,P i j|=(r : ℤ)-2)
theorem column_pair_modular_correction {r q : ℕ} (hr : 4*(q+1)^2<r*q^2) (hq : 3≤q) (hodd : q%2=1) (P : Matrix (Fin r) (Fin (4*(q+1))) ℤ) (hs : ∀ i j,P i j=1 ∨ P i j= -1) (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (4*(q+1) : ℤ) else 0) : (exactSignCandidates P).card=(modularCandidatesAt q P).card-(columnPairCandidates P).card ∧ ∃ e : ↥(columnPairCandidates P) ≃ ↥(modularCandidatesAt q P \ exactSignCandidates P), ∀ T : columnPairCandidates P,∃ i : Fin r, (∀ k,k≠i → (∏ j∈T.val,P k j)= -(∏ j∈T.val,P i j)) ∧ (e T).val=normalizeSignCode (show 0<4*(q+1) from Nat.mul_pos (Nat.zero_lt_succ 3) (Nat.succ_pos q)) (flipSignVector T.val (P i)) := by sorry
theorem near_modular_spurious_unique_row {r q : ℕ} (hr : 4*(q+1)^2<r*q^2) (hq : 3≤q) (hodd : q%2=1) (P : Matrix (Fin r) (Fin (4*(q+1))) ℤ) (hs : ∀ i j,P i j=1 ∨ P i j= -1) (hg : ∀ i k,(∑ j,P i j*P k j)=if i=k then (4*(q+1) : ℤ) else 0) (x : Fin (4*(q+1)) → Bool) (hx : x∈modularCandidatesAt q P) (hne : x∉exactSignCandidates P) : ∃! i : Fin r,∃ T : Finset (Fin (4*(q+1))),T.card=2 ∧ x=normalizeSignCode (show 0<4*(q+1) from Nat.mul_pos (Nat.zero_lt_succ 3) (Nat.succ_pos q)) (flipSignVector T (P i)) := by sorry
noncomputable def rationalSignMatrix {ι κ : Type*} (A : Matrix ι κ ℝ) : Matrix ι κ ℚ := fun i j => if A i j=1 then 1 else -1
def IsBinaryMatrix {K δ κ : Type*} [One K] [Neg K] (B : Matrix δ κ K) : Prop := ∀ i j,B i j=1 ∨ B i j= -1
def signAnchorMatrix {K δ : Type*} [One K] [Neg K] (σ : δ×δ → Bool) : Matrix δ δ K := fun i j => if σ (i,j) then -1 else 1
noncomputable def anchorSolve {K δ κ : Type*} [Field K] [Fintype δ] [DecidableEq δ] (C : Matrix κ κ K) (a : δ → κ) (S : Matrix δ δ K) : Matrix δ κ K := (Sᵀ)⁻¹*C.submatrix a id
noncomputable def residualCorrelationTypes (δ : Type*) [Fintype δ] [DecidableEq δ] : Finset (δ → ℝ) := by
  classical
  exact Finset.univ.image (fun k : δ → Fin (Fintype.card δ+1) =>
    fun i => (Fintype.card δ : ℝ)-2*(k i).val)
noncomputable def rationalResidualGram {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (P : Matrix ι κ ℝ) : Matrix κ κ ℚ := (Fintype.card κ : ℚ) • 1-(rationalSignMatrix P)ᵀ*rationalSignMatrix P
theorem residual_anchor_enumeration {δ ι : Type*} [Fintype δ] [Fintype ι] [DecidableEq δ] [DecidableEq ι] [Nonempty δ] (P : Matrix ι (δ ⊕ ι) ℝ) (hP : IsPartialHadamard P) (heven : Even (Fintype.card (δ ⊕ ι))) : ∃ a : δ → (δ ⊕ ι),Function.Injective a ∧ ((rationalResidualGram P).submatrix a a).det≠0 ∧ ((∃ H : Matrix (δ ⊕ ι) (δ ⊕ ι) ℝ,Matrix.IsHadamard H ∧ ∀ i j,H (Sum.inr i) j=P i j) ↔ ∃ σ : δ×δ → Bool,(signAnchorMatrix (K := ℚ) σ).det≠0 ∧ IsBinaryMatrix (anchorSolve (rationalResidualGram P) a (signAnchorMatrix σ)) ∧ (anchorSolve (rationalResidualGram P) a (signAnchorMatrix σ))ᵀ* anchorSolve (rationalResidualGram P) a (signAnchorMatrix σ)=rationalResidualGram P) ∧ Fintype.card (δ×δ → Bool)=2^(Fintype.card δ*Fintype.card δ) ∧ (residualCorrelationTypes δ).card≤(Fintype.card δ+1)^(Fintype.card δ) ∧ ∀ j : δ ⊕ ι,(fun i => residualGram P (a i) j)∈residualCorrelationTypes δ := by sorry
def IsBilinearCodeNeighbor {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (B : LinearMap.BilinForm K V) (C D : Submodule K V) : Prop := D=B.orthogonal D ∧ D≠C ∧ finrank K ↥(C ⊓ D)+1=finrank K C
noncomputable def selfDualCodeNeighbors {p : ℕ} [Fact p.Prime]
    (C : Submodule (ZMod p) (Fin (4*p) → ZMod p)) :
    Finset (Submodule (ZMod p) (Fin (4*p) → ZMod p)) := by
  classical
  letI : Fintype (Submodule (ZMod p) (Fin (4*p) → ZMod p)) :=
    Fintype.ofInjective (fun E => (E : Set (Fin (4*p) → ZMod p))) SetLike.coe_injective
  exact Finset.univ.filter (IsBilinearCodeNeighbor (coordinateDotForm (ZMod p) (4*p)) C)
noncomputable def normalizedSignCube (N : ℕ) : Finset (Fin N → Bool) := by
  classical
  exact Finset.univ.filter positiveFirstBit
theorem hyperplane_two_self_dual_spaces {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (htwo : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate) (C H : Submodule K V) (hC : C=B.orthogonal C) (hHC : H≤C) (hcodim : finrank K H+1=finrank K C) : ∃ D : Submodule K V,D=B.orthogonal D ∧ D≠C ∧ C ⊓ D=H ∧ (∀ w : V,B w w=0 → (w∈B.orthogonal H ↔ w∈C ∨ w∈D)) ∧ ∀ E : Submodule K V,E=B.orthogonal E → H≤E → E≠C → E=D := by sorry
theorem two_code_sign_pool {p : ℕ} [Fact p.Prime] (hodd : p%2=1) (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C) (hcodim : finrank (ZMod p) G+1=finrank (ZMod p) C) : ∃ D : Submodule (ZMod p) (Fin (4*p) → ZMod p), D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ D≠C ∧ C ⊓ D=G ∧ (∀ E : Submodule (ZMod p) (Fin (4*p) → ZMod p), E=(coordinateDotForm (ZMod p) (4*p)).orthogonal E → G≤E → E≠C → E=D) ∧ codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)= codeSignCandidates C ∪ codeSignCandidates D ∧ codeSignCandidates C ∩ codeSignCandidates D=codeSignCandidates G ∧ (codeSignCandidates D).card+(codeSignCandidates C).card= (codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)).card+ (codeSignCandidates G).card := by sorry
def signFamilyMatrix {N : ℕ} (S : Finset (Fin N → Bool)) : Matrix S (Fin N) ℝ := fun x j => (modularBitSign (x.val j) : ℝ)
theorem pivot_hyperplane_syndrome_label {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (C : Submodule K V) (hC : C=B.orthogonal C) (b : Basis ι K C) (v w : V) (hv : v∉C) (hw : w∉C) : bilinearPivotHyperplane B C v=bilinearPivotHyperplane B C w ↔ ∃ a : K,a≠0 ∧ ∀ i,B w (b i)=a*B v (b i) := by sorry
theorem sign_vector_unique_code_neighbor {p : ℕ} [Fact p.Prime] (hodd : p%2=1) (C : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (x : Fin (4*p) → Bool) (hx : (fun j => (modularBitSign (x j) : ZMod p))∉C) : ∃! D : Submodule (ZMod p) (Fin (4*p) → ZMod p), IsBilinearCodeNeighbor (coordinateDotForm (ZMod p) (4*p)) C D ∧ (fun j => (modularBitSign (x j) : ZMod p))∈D := by sorry
theorem syndrome_neighbor_census {p : ℕ} [Fact p.Prime] (hodd : p%2=1) (C : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) : (∑ D∈selfDualCodeNeighbors C,(codeSignCandidates D \ codeSignCandidates C).card)= (normalizedSignCube (4*p) \ codeSignCandidates C).card ∧ (∀ D∈selfDualCodeNeighbors C,(codeSignCandidates D).card= (codeSignCandidates (C ⊓ D)).card+(codeSignCandidates D \ codeSignCandidates C).card) ∧ (∀ D∈selfDualCodeNeighbors C,codeSignCandidates D \ codeSignCandidates C=∅ → (codeSignCandidates D).card≤(codeSignCandidates C).card) := by sorry
noncomputable def restrictedCodeNeighbors {p : ℕ} [Fact p.Prime]
    (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) :
    Finset (Submodule (ZMod p) (Fin (4*p) → ZMod p)) := by
  classical
  exact (selfDualCodeNeighbors C).filter (fun D => G≤D)
theorem restricted_neighbor_incidence_and_improvement {p : ℕ} [Fact p.Prime] (hodd : p%2=1) (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C) : (restrictedCodeNeighbors C G).card= (p ^ (finrank (ZMod p) C-finrank (ZMod p) G)-1)/(p-1) ∧ (∑ D∈restrictedCodeNeighbors C G, (((codeSignCandidates D).card : ℤ)-(codeSignCandidates C).card))= ((codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)).card : ℤ)- (codeSignCandidates C).card- ((codeSignCandidates C).card-(codeSignCandidates G).card : ℤ)* (p : ℤ) ^ (finrank (ZMod p) C-finrank (ZMod p) G-1) ∧ (0<((codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)).card : ℤ)- (codeSignCandidates C).card- ((codeSignCandidates C).card-(codeSignCandidates G).card : ℤ)* (p : ℤ) ^ (finrank (ZMod p) C-finrank (ZMod p) G-1) → ∃ D∈restrictedCodeNeighbors C G,(codeSignCandidates C).card<(codeSignCandidates D).card) := by sorry
theorem weighted_code_grid_classification {p : ℕ} [Fact p.Prime] (hodd : p%2=1) (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C) (hcodim : Module.finrank (ZMod p) G+2=Module.finrank (ZMod p) C) : let U := codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G); let A := codeSignCandidates G; ∃ e : (Fin (p+1) ⊕ Fin (p+1)) ≃ {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D}, ∃ w : Fin (p+1) → Fin (p+1) → ℕ, U.card=A.card+(∑ a,∑ b,w a b) ∧ (∀ a,(codeSignCandidates (e (Sum.inl a)).val).card=A.card+(∑ b,w a b)) ∧ (∀ b,(codeSignCandidates (e (Sum.inr b)).val).card=A.card+(∑ a,w a b)) ∧ ∃ label : ↥(U \ A) → Fin (p+1)×Fin (p+1), (∀ x a,x.val∈codeSignCandidates (e (Sum.inl a)).val ↔ (label x).1=a) ∧ (∀ x b,x.val∈codeSignCandidates (e (Sum.inr b)).val ↔ (label x).2=b) ∧ ∀ a b,w a b=Nat.card {x // label x=(a,b)} := by sorry
theorem weighted_grid_optimal_repair {p : ℕ} [Fact p.Prime] (hodd : p%2=1) (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C) (hcodim : finrank (ZMod p) G+2=finrank (ZMod p) C) (a : Fin 5 → Fin (4*p) → Bool) (ha : ∀ i,a i∈codeSignCandidates G) (hgram : ∀ i j,(∑ k,modularBitSign (a i k)*modularBitSign (a j k))= if i=j then (4*p : ℤ) else 0) : let U := codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G); let A := codeSignCandidates G; ∃ e : (Fin (p+1) ⊕ Fin (p+1)) ≃ {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D}, ∃ w : Fin (p+1) → Fin (p+1) → ℕ, (∀ i,(codeSignCandidates (e (Sum.inl i)).val).card=A.card+(∑ j,w i j)) ∧ (∀ j,(codeSignCandidates (e (Sum.inr j)).val).card=A.card+(∑ i,w i j)) ∧ let M := A.card+max (Finset.univ.sup (fun i => ∑ j,w i j)) (Finset.univ.sup (fun j => ∑ i,w i j)); M≤4*p ∧ (∀ T : Finset (Fin (4*p) → Bool),T⊆U → (∀ x∈T,∀ y∈T,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) → ∃ k,T⊆codeSignCandidates (e k).val) ∧ (∀ T : Finset (Fin (4*p) → Bool),T⊆U → (∀ x∈T,∀ y∈T,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) → T.card≤M) ∧ (∃ T : Finset (Fin (4*p) → Bool),A⊆T ∧ T⊆U ∧ (∀ x∈T,∀ y∈T,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) ∧ T.card=M) ∧ ((∃ T : Finset (Fin (4*p) → Bool),A⊆T ∧ T⊆U ∧ (∀ x∈T,∀ y∈T,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) ∧ T.card=4*p) ↔ (∃ i,(∑ j,w i j)=4*p-A.card) ∨ (∃ j,(∑ i,w i j)=4*p-A.card)) := by sorry
theorem full_sign_family_gives_hadamard {N : ℕ} (hN : 0<N) (S : Finset (Fin N → Bool)) (hcard : S.card=N) (horth : ∀ x∈S,∀ y∈S,x≠y → (∑ j,modularBitSign (x j)*modularBitSign (y j))=0) : ∃ H : Matrix (Fin N) (Fin N) ℝ,Matrix.IsHadamard H ∧ (∀ x∈S,∃ i : Fin N,∀ j,H i j=(modularBitSign (x j) : ℝ)) ∧ ∀ i : Fin N,∃ x∈S,∀ j,H i j=(modularBitSign (x j) : ℝ) := by sorry
def splitGeneratorCount (q : ℕ) : ℕ → ℕ
  | 0 => 1
  | h+1 => (q^h+1)*splitGeneratorCount q h
def selfDualSubspaces {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (B : LinearMap.BilinForm K V) := {D : Submodule K V // D=B.orthogonal D}
theorem split_form_self_dual_subspace_count {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (htwo : (2 : K)≠0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate) (C : Submodule K V) (hC : C=B.orthogonal C) : Nat.card (selfDualSubspaces B)=splitGeneratorCount (Nat.card K) (finrank K C) := by sorry
theorem split_form_retained_subspace_count {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (htwo : (2 : K)≠0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate) (C G : Submodule K V) (hC : C=B.orthogonal C) (hG : G≤B.orthogonal G) : Nat.card {D : Submodule K V // D=B.orthogonal D ∧ G≤D}= splitGeneratorCount (Nat.card K) (finrank K C-finrank K G) := by sorry
noncomputable def finiteNeighborAverage {α : Type*} (N : α → Finset α) (f : α → ℝ) (x : α) : ℝ :=
  (∑ y∈N x,f y)/((N x).card : ℝ)
noncomputable def finiteWalkExpectation {α : Type*} (N : α → Finset α) (f : α → ℝ) : ℕ → α → ℝ
  | 0 => f
  | t+1 => fun x => finiteNeighborAverage N (finiteWalkExpectation N f t) x
def retainedCodeState {p : ℕ} [Fact p.Prime]
    (G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) :=
  {C : Submodule (ZMod p) (Fin (4*p) → ZMod p) // C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C ∧ G≤C}
noncomputable def retainedCodeNeighbors {p : ℕ} [Fact p.Prime]
    (G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (C : retainedCodeState G) :
    Finset (retainedCodeState G) := by
  classical
  let S := restrictedCodeNeighbors C.val G
  let lift : S ↪ retainedCodeState G := {
    toFun := fun D => ⟨D.val,(Finset.mem_filter.mp (Finset.mem_filter.mp D.property).1).2.1,
      (Finset.mem_filter.mp D.property).2⟩
    inj' := by
      intro D E hDE
      exact Subtype.ext (congrArg (fun H : retainedCodeState G => H.val) hDE) }
  exact S.attach.map lift
noncomputable def retainedCodeSignCount {p : ℕ} [Fact p.Prime]
    (G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (C : retainedCodeState G) : ℝ :=
  (codeSignCandidates C.val).card
theorem retained_code_walk_exact_expectation {p : ℕ} [Fact p.Prime] (hodd : p%2=1) (G : Submodule (ZMod p) (Fin (4*p) → ZMod p)) (h : ℕ) (hrank : finrank (ZMod p) G+h=2*p) (hh : 2≤h) (C₀ : retainedCodeState G) : let U := codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G); let A := codeSignCandidates G; let W := (U \ A).card; let d : ℝ := ((p^h-1)/(p-1) : ℕ); let μ : ℝ := (A.card : ℝ)+(W : ℝ)/(1+(p : ℝ)^(h-1)); let ρ : ℝ := (d-1-(p : ℝ)^(h-1))/d; (∀ t : ℕ,finiteWalkExpectation (retainedCodeNeighbors G) (retainedCodeSignCount G) t C₀= μ+ρ^t*(retainedCodeSignCount G C₀-μ)) ∧ (h=2 → ρ=0) ∧ (3≤h → 0<ρ ∧ ρ<1/(p : ℝ)) := by sorry
open scoped Classical
def tupleVectorSpan {K V α : Type*} [Field K] [AddCommGroup V] [Module K V] (v : α → V) {k : ℕ} (t : Fin k → α) : Submodule K V := Submodule.span K (Set.range (fun i => v (t i)))
theorem retained_actual_sign_first_two_moments {p : ℕ} [Fact p.Prime] (hodd : p%2=1) (G C : Submodule (ZMod p) (Fin (4*p) → ZMod p)) [Fintype {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D}] (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C) (h : ℕ) (hrank : finrank (ZMod p) G+h=2*p) (hh : 2≤h) : let B := coordinateDotForm (ZMod p) (4*p); let U := codeSignCandidates (B.orthogonal G); let A := codeSignCandidates G; let S := U \ A; let v : S → (Fin (4*p) → ZMod p) := fun x j => (modularBitSign (x.val j) : ZMod p); let S₂ := Nat.card {z : S×S // v z.2∈G ⊔ Submodule.span (ZMod p) {v z.1}}; let T := Nat.card {z : S×S // v z.2∉G ⊔ Submodule.span (ZMod p) {v z.1} ∧ B (v z.1) (v z.2)=0}; let Ω := {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=B.orthogonal D ∧ G≤D}; let Y : Ω → ℕ := fun D => (codeSignCandidates D.val).card-A.card; (((∑ D : Ω,Y D : ℕ) : ℝ)/(Nat.card Ω : ℝ)=(S.card : ℝ)/((p : ℝ)^(h-1)+1)) ∧ (((∑ D : Ω,(Y D)^2 : ℕ) : ℝ)/(Nat.card Ω : ℝ)= (S₂ : ℝ)/((p : ℝ)^(h-1)+1)+(T : ℝ)/(((p : ℝ)^(h-1)+1)*((p : ℝ)^(h-2)+1))) := by sorry
theorem retained_actual_sign_second_moment_certificate {p : ℕ} [Fact p.Prime] (hodd : p%2=1) (G C : Submodule (ZMod p) (Fin (4*p) → ZMod p)) [Fintype {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D}] (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C) (h : ℕ) (hrank : finrank (ZMod p) G+h=2*p) (hh : 2≤h) : let B := coordinateDotForm (ZMod p) (4*p); let U := codeSignCandidates (B.orthogonal G); let A := codeSignCandidates G; let S := U \ A; let v : S → (Fin (4*p) → ZMod p) := fun x j => (modularBitSign (x.val j) : ZMod p); let S₂ := Nat.card {z : S×S // v z.2∈G ⊔ Submodule.span (ZMod p) {v z.1}}; let T := Nat.card {z : S×S // v z.2∉G ⊔ Submodule.span (ZMod p) {v z.1} ∧ B (v z.1) (v z.2)=0}; 0<S.card → ∃ D : {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=B.orthogonal D ∧ G≤D}, A.card+Nat.ceil (((S₂ : ℝ)+(T : ℝ)/((p : ℝ)^(h-2)+1))/(S.card : ℝ))≤(codeSignCandidates D.val).card := by sorry
theorem retained_line_weight_pair_identities {K V α : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype α] [Fintype (Submodule K V)] (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (G : Submodule K V) (hG : G≤B.orthogonal G) (v : α → V) (hvG : ∀ a,v a∈B.orthogonal G) (hv : ∀ a,v a∉G) (hvv : ∀ a,B (v a) (v a)=0) : let label : α → Submodule K V := fun a => G ⊔ Submodule.span K {v a}; let w : Submodule K V → ℕ := fun L => Nat.card {a : α // label a=L}; (∑ L : Submodule K V,w L^2)=Nat.card {z : α×α // v z.2∈G ⊔ Submodule.span K {v z.1}} ∧ (∑ L : Submodule K V,∑ M : Submodule K V,if L≠M ∧ L≤B.orthogonal M then w L*w M else 0)= Nat.card {z : α×α // v z.2∉G ⊔ Submodule.span K {v z.1} ∧ B (v z.1) (v z.2)=0} := by sorry
def orthogonalQuotientCode {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (B : LinearMap.BilinForm K V) (C G : Submodule K V) : Submodule K ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype) := (C.comap (B.orthogonal G).subtype).map (G.comap (B.orthogonal G).subtype).mkQ
theorem retained_line_quotient_rank_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (G : Submodule K V) (hG : G≤B.orthogonal G) (x : V) (hxG : x∈B.orthogonal G) (hx : x∉G) : finrank K (orthogonalQuotientCode B (G ⊔ Submodule.span K {x}) G)=1 := by sorry
noncomputable def retainedTupleRank {K V α : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (G : Submodule K V) (v : α → V) {k : ℕ} (t : Fin k → α) : ℕ := finrank K ↥(G ⊔ tupleVectorSpan (K := K) v t)-finrank K G
noncomputable def retainedTupleMomentCount {K V α : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (G : Submodule K V) (v : α → V) (k r : ℕ) : ℕ := Nat.card {t : Fin k → α // (G ⊔ tupleVectorSpan (K := K) v t)≤B.orthogonal (G ⊔ tupleVectorSpan (K := K) v t) ∧ retainedTupleRank G v t=r}
theorem actual_sign_third_moment_formulas {p : ℕ} [Fact p.Prime] (hodd : p%2=1) (G C : Submodule (ZMod p) (Fin (4*p) → ZMod p)) [Fintype {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D}] (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C) (h : ℕ) (hrank : finrank (ZMod p) G+h=2*p) : let B := coordinateDotForm (ZMod p) (4*p); let U := codeSignCandidates (B.orthogonal G); let A := codeSignCandidates G; let S := U \ A; let v : S → (Fin (4*p) → ZMod p) := fun x j => (modularBitSign (x.val j) : ZMod p); let R : ℕ → ℕ := fun r => retainedTupleMomentCount B G v 3 r; let Ω := {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=B.orthogonal D ∧ G≤D}; let Y : Ω → ℕ := fun D => (codeSignCandidates D.val).card-A.card; (3≤h → (((∑ D : Ω,Y D^3 : ℕ) : ℝ)/(Nat.card Ω : ℝ))= (R 1 : ℝ)/((p : ℝ)^(h-1)+1)+(R 2 : ℝ)/(((p : ℝ)^(h-1)+1)*((p : ℝ)^(h-2)+1))+ (R 3 : ℝ)/(((p : ℝ)^(h-1)+1)*((p : ℝ)^(h-2)+1)*((p : ℝ)^(h-3)+1))) ∧ (h=2 → R 3=0 ∧ (((∑ D : Ω,Y D^3 : ℕ) : ℝ)/(Nat.card Ω : ℝ))= (R 1 : ℝ)/((p : ℝ)+1)+(R 2 : ℝ)/(((p : ℝ)+1)*2)) := by sorry
theorem actual_sign_third_moment_certificate {p : ℕ} [Fact p.Prime] (G C : Submodule (ZMod p) (Fin (4*p) → ZMod p)) [Fintype {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D}] (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C) : let Ω := {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) // D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D}; let b := (codeSignCandidates G).card; let Y : Ω → ℕ := fun D => (codeSignCandidates D.val).card-b; 0<(((∑ D : Ω,Y D^2 : ℕ) : ℝ)/(Nat.card Ω : ℝ)) → ∃ D : Ω,b+Nat.ceil ((((∑ E : Ω,Y E^3 : ℕ) : ℝ)/(Nat.card Ω : ℝ))/ (((∑ E : Ω,Y E^2 : ℕ) : ℝ)/(Nat.card Ω : ℝ)))≤(codeSignCandidates D.val).card := by sorry
theorem retained_tuple_count_as_weighted_points {K V α : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype α] [Fintype (Submodule K V)] (B : LinearMap.BilinForm K V) (G : Submodule K V) (v : α → V) (k r : ℕ) : let label : α → Submodule K V := fun a => G ⊔ Submodule.span K {v a}; let w : Submodule K V → ℕ := fun L => Nat.card {a : α // label a=L}; retainedTupleMomentCount B G v (k+1) r= ∑ u : Fin (k+1) → Submodule K V, if (⨆ i,u i)≤B.orthogonal (⨆ i,u i) ∧ finrank K ↥(⨆ i,u i)-finrank K G=r then ∏ i,w (u i) else 0 := by sorry
def IsFourthRoot (z : ℂ) : Prop := z=1 ∨ z= -1 ∨ z=Complex.I ∨ z= -Complex.I
noncomputable def realifiedMatrix {ι κ : Type*} (V : Matrix ι κ ℂ) : Matrix (ι⊕ι) (κ⊕κ) ℝ := Matrix.fromBlocks (fun i j => (V i j).re) (fun i j => -(V i j).im) (fun i j => (V i j).im) (fun i j => (V i j).re)
theorem quaternary_realification_gate {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ) (hV : ∀ i j,IsFourthRoot (V i j)) (hgram : V.conjTranspose*V=(n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) : let A := realifiedMatrix (((1+Complex.I) : ℂ) • V); (∀ i j,A i j=1 ∨ A i j= -1) ∧ A.transpose*A=(2*(n : ℝ)) • (1 : Matrix (Fin m⊕Fin m) (Fin m⊕Fin m) ℝ) ∧ ((∃ z : Fin n → ℂ,(∀ i,IsFourthRoot (z i)) ∧ V.conjTranspose.mulVec z=0) ↔ ∃ w : Fin n⊕Fin n → ℝ,IsCubeVector w ∧ A.transpose.mulVec w=0) := by sorry
def ternaryRepairCode (i : Fin 9) (j : Fin 4) : ℕ := ![i.val%3,i.val/3,(i.val%3+i.val/3)%3,(i.val%3+3-i.val/3)%3] j
def affineRepairInt : Matrix (Fin 9) (Fin 4×Fin 3) ℤ := fun i j => if j.2.val=ternaryRepairCode i j.1 then -1 else 1
noncomputable def affineRepair : Matrix (Fin 9) (Fin 4×Fin 3) ℝ := fun i j => (affineRepairInt i j : ℝ)
noncomputable def repeatedTensorSeed {τ : Type*} (T : Matrix τ τ ℝ) : Matrix (Fin 4×τ) ((Fin 4×τ)×Fin 3) ℝ := fun i j => seedFour i.1 j.1.1*T i.2 j.1.2
noncomputable def insertedFiberRows {τ : Type*} (T : Matrix τ τ ℝ) (F : Finset τ) : Matrix (Fin 9×F) ((Fin 4×τ)×Fin 3) ℝ := fun a j => affineRepair a.1 (j.1.1,j.2)*T a.2.val j.1.2
def fiberDeletedRows {τ : Type*} (F : Finset τ) : Finset (Fin 4×τ) := ({0} : Finset (Fin 4)).product F
def HasRetainedHadamardCompletion {ι κ : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ] (P : Matrix ι κ ℝ) (S : Finset ι) : Prop := ∃ H : Matrix κ κ ℝ,Matrix.IsHadamard H ∧ ∃ e : S ↪ κ,∀ i j,H (e i) j=P i.val j
theorem cheap_augmentation_exact_completion_cost {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ] (T : Matrix τ τ ℝ) (hT : IsHadamard T) : IsPartialHadamard (repeatedTensorSeed T) ∧ NoSignExtension (repeatedTensorSeed T) ∧ exchangeCost (repeatedTensorSeed T)=(1 : WithTop ℕ) ∧ (∀ S : Finset (Fin 4×τ),HasRetainedHadamardCompletion (repeatedTensorSeed T) S → Fintype.card τ≤Sᶜ.card) ∧ (∃ S : Finset (Fin 4×τ),Sᶜ.card=Fintype.card τ ∧ HasRetainedHadamardCompletion (repeatedTensorSeed T) S) ∧ ∀ k : ℕ,k≤Fintype.card τ → ∃ F : Finset τ,F.card=k ∧ (fiberDeletedRows F).card=k ∧ Fintype.card (Fin 9×F)=9*k ∧ Fintype.card (↥((fiberDeletedRows F)ᶜ) ⊕ (Fin 9×F))=4*Fintype.card τ+8*k ∧ IsPartialHadamard (retainAndInsert (repeatedTensorSeed T) (insertedFiberRows T F) (fiberDeletedRows F)ᶜ) ∧ NoSignExtension (retainAndInsert (repeatedTensorSeed T) (insertedFiberRows T F) (fiberDeletedRows F)ᶜ) := by sorry
end CompletionTheory
namespace CompletionTheory
open Matrix
abbrev SignedTwoState := Bool×Bool×Bool
def signedTwoInt (d : SignedTwoState) : Matrix (Fin 2) (Fin 2) ℤ := fun i j => if j=(if d.1 then Fin.rev i else i) then (if (if i=0 then d.2.1 else d.2.2) then -1 else 1) else 0
def walshTwoInt : Matrix (Fin 2) (Fin 2) ℤ := !![1,1;1,-1]
def twoBlock {ι : Type*} (M : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (i j : ι) : Matrix (Fin 2) (Fin 2) ℝ := fun a b => M (a,i) (b,j)
def normalizedTwoInt {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState) : Matrix (Fin 2×ι) (Fin 2×ι) ℤ := fun i j => if i.2=j.2 then 0 else (signedTwoInt (A i.2 j.2)*walshTwoInt) i.1 j.1
noncomputable def normalizedTwoReal {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState) : Matrix (Fin 2×ι) (Fin 2×ι) ℝ := (normalizedTwoInt A).map (Int.castRingHom ℝ)
def IsNormalizedTwoZeroWeighing {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) : Prop := (∀ i,twoBlock W i i=0) ∧ (∀ i j,i≠j → IsSignMatrix (twoBlock W i j) ∧ twoBlock W i j*(twoBlock W i j).transpose=(2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧ W*W.transpose=((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ)
inductive IntegerCircuit where
  | lit : ℤ → IntegerCircuit
  | add : IntegerCircuit → IntegerCircuit → IntegerCircuit
  | mul : IntegerCircuit → IntegerCircuit → IntegerCircuit
  | neg : IntegerCircuit → IntegerCircuit
  | divTwo : IntegerCircuit → IntegerCircuit
def IntegerCircuit.eval : IntegerCircuit → ℤ
  | .lit a => a
  | .add a b => a.eval+b.eval
  | .mul a b => a.eval*b.eval
  | .neg a => -a.eval
  | .divTwo a => a.eval/2
def IntegerCircuit.opCount : IntegerCircuit → ℕ
  | .lit _ => 0
  | .add a b => a.opCount+b.opCount+1
  | .mul a b => a.opCount+b.opCount+1
  | .neg a => a.opCount+1
  | .divTwo a => a.opCount+1
abbrev TwoCircuit := Matrix (Fin 2) (Fin 2) IntegerCircuit
def twoCircuitLit (M : Matrix (Fin 2) (Fin 2) ℤ) : TwoCircuit := fun i j => .lit (M i j)
def twoCircuitAdd (A B : TwoCircuit) : TwoCircuit := fun i j => .add (A i j) (B i j)
def twoCircuitNeg (A : TwoCircuit) : TwoCircuit := fun i j => .neg (A i j)
def twoCircuitMul (A B : TwoCircuit) : TwoCircuit := fun i j => .add (.mul (A i 0) (B 0 j)) (.mul (A i 1) (B 1 j))
def forcedTwoCircuit {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState) (root : ι) (d : SignedTwoState) (i : ι) : TwoCircuit := if i=root then twoCircuitLit (signedTwoInt d) else twoCircuitMul (twoCircuitMul (twoCircuitNeg (twoCircuitLit (signedTwoInt (A i root)))) (twoCircuitLit (signedTwoInt d)).transpose) (twoCircuitLit (signedTwoInt (A root i)))
def crossTwoCircuit {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState) (root : ι) (d : SignedTwoState) (i j : ι) : TwoCircuit := twoCircuitAdd (twoCircuitMul (twoCircuitLit (signedTwoInt (A i j))) (forcedTwoCircuit A root d j).transpose) (twoCircuitMul (forcedTwoCircuit A root d i) (twoCircuitLit (signedTwoInt (A j i))).transpose)
def filledEntryCircuit {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState) (root : ι) (d : SignedTwoState) (p q : Fin 2×ι) : IntegerCircuit := .add (if p.2=q.2 then .lit 0 else twoCircuitMul (twoCircuitLit (signedTwoInt (A p.2 q.2))) (twoCircuitLit walshTwoInt) p.1 q.1) (if p.2=q.2 then twoCircuitMul (forcedTwoCircuit A root d p.2) (twoCircuitLit walshTwoInt) p.1 q.1 else .lit 0)
def acceptedTwoCircuitRoots {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → ι → SignedTwoState) (root : ι) : Finset SignedTwoState := Finset.univ.filter (fun d => ∀ i j,i≠j → ∀ a b : Fin 2,(crossTwoCircuit A root d i j a b).eval=0)
def twoZeroCircuitCandidates {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → ι → SignedTwoState) (root : ι) : Finset (Matrix (Fin 2×ι) (Fin 2×ι) ℤ) := (acceptedTwoCircuitRoots A root).image (fun d => fun p q => (filledEntryCircuit A root d p q).eval)
def intTwoBlock {ι : Type*} (M : Matrix (Fin 2×ι) (Fin 2×ι) ℤ) (i j : ι) : Matrix (Fin 2) (Fin 2) ℤ := fun a b => M (a,i) (b,j)
def normalizationEntryCircuit (B : Matrix (Fin 2) (Fin 2) ℤ) (a b : Fin 2) : IntegerCircuit := .divTwo (twoCircuitMul (twoCircuitLit B) (twoCircuitLit walshTwoInt.transpose) a b)
def crossTwoCircuitBlockCost {ι : Type*} [DecidableEq ι] (A : ι → ι → SignedTwoState) (root : ι) (d : SignedTwoState) (i j : ι) : ℕ := ∑ a : Fin 2,∑ b : Fin 2,(crossTwoCircuit A root d i j a b).opCount
def twoRootCrossArithmeticCost {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → ι → SignedTwoState) (root : ι) : ℕ := ∑ d : SignedTwoState,∑ i : ι,∑ j : ι,crossTwoCircuitBlockCost A root d i j
def twoRootOutputArithmeticCost {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → ι → SignedTwoState) (root : ι) : ℕ := ∑ d : SignedTwoState,∑ p : Fin 2×ι,∑ q : Fin 2×ι,(filledEntryCircuit A root d p q).opCount
def twoRootNormalizationArithmeticCost {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → ι → SignedTwoState) : ℕ := ∑ i : ι,∑ j : ι,∑ a : Fin 2,∑ b : Fin 2, (normalizationEntryCircuit (intTwoBlock (normalizedTwoInt A) i j) a b).opCount
def IsEntryPreservingHadamardFilling {ι : Type*} [Fintype ι] [DecidableEq ι] (W H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) : Prop := Matrix.IsHadamard H ∧ ∀ p q,W p q≠0 → H p q=W p q
theorem all_sign_fillings_quadratic_time {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) (hW : IsNormalizedTwoZeroWeighing W) (root : ι) : ∃ A : ι → ι → SignedTwoState,normalizedTwoReal A=W ∧ (twoZeroCircuitCandidates A root).card≤8 ∧ (∀ H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ,IsEntryPreservingHadamardFilling W H ↔ ∃ K∈twoZeroCircuitCandidates A root,H=K.map (Int.castRingHom ℝ)) ∧ (∀ i j,i≠j → ∀ a b : Fin 2, (normalizationEntryCircuit (intTwoBlock (normalizedTwoInt A) i j) a b).eval=signedTwoInt (A i j) a b) ∧ Fintype.card (SignedTwoState×ι×ι)=8*(Fintype.card ι)^2 ∧ twoRootNormalizationArithmeticCost A+twoRootCrossArithmeticCost A root+twoRootOutputArithmeticCost A root≤ 740*(Fintype.card (Fin 2×ι))^2 := by sorry
end CompletionTheory
namespace CompletionTheory
open Matrix
noncomputable def zeroRowSet {ι : Type*} [Fintype ι] (W : Matrix ι ι ℝ) (i : ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun j => W i j=0)
noncomputable def zeroBlockSet {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℝ) : Finset (Finset ι) :=
  Finset.univ.image (zeroRowSet W)
def ZeroBlockIndex {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℝ) := ↥(zeroBlockSet W)
noncomputable instance zeroBlockIndexFintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) : Fintype (ZeroBlockIndex W) :=
  inferInstanceAs (Fintype ↥(zeroBlockSet W))
noncomputable instance zeroBlockIndexDecidableEq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) : DecidableEq (ZeroBlockIndex W) := Classical.decEq _
noncomputable def signedTwoReal (d : SignedTwoState) : Matrix (Fin 2) (Fin 2) ℝ :=
  (signedTwoInt d).map (Int.castRingHom ℝ)
noncomputable def walshTwoReal : Matrix (Fin 2) (Fin 2) ℝ :=
  walshTwoInt.map (Int.castRingHom ℝ)
noncomputable def pairedWalshReal {ι : Type*} [DecidableEq ι] :
    Matrix (Fin 2×ι) (Fin 2×ι) ℝ := Matrix.blockDiagonal (fun _ : ι => walshTwoReal)
theorem forced_two_zero_block_structure {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℝ) (hW : IsWeighing W ((Fintype.card ι : ℝ)-2)) (hn : 4∣Fintype.card ι) (hnpos : 0<Fintype.card ι) : ∃ r c : (Fin 2×ZeroBlockIndex W) ≃ ι, let V := W.submatrix r c; let A := (1/2 : ℝ) • (V*pairedWalshReal); IsNormalizedTwoZeroWeighing V ∧ (∀ a b : Fin 2,∀ i j : ZeroBlockIndex W,V (a,i) (b,j)=0 ↔ i=j) ∧ 2*Fintype.card (ZeroBlockIndex W)=Fintype.card ι ∧ (∀ i,twoBlock A i i=0) ∧ (∀ i j,i≠j → ∃ d : SignedTwoState,twoBlock A i j=signedTwoReal d) ∧ A*A.transpose=((Fintype.card (ZeroBlockIndex W) : ℝ)-1) • (1 : Matrix (Fin 2×ZeroBlockIndex W) (Fin 2×ZeroBlockIndex W) ℝ) := by sorry
end CompletionTheory

namespace CompletionTheory
open Matrix
noncomputable section
inductive TwoPlaneSectionKind where
  | zero | full | horizontal | vertical | diagonal | antidiagonal
  deriving DecidableEq
def twoPlaneSectionCondition (k : TwoPlaneSectionKind) (x y : ℝ) : Prop :=
  match k with
  | .zero => x=0 ∧ y=0
  | .full => (0:ℝ)=0 ∧ (0:ℝ)=0
  | .horizontal => (0:ℝ)=0 ∧ y=0
  | .vertical => x=0 ∧ (0:ℝ)=0
  | .diagonal => x=y ∧ (0:ℝ)=0
  | .antidiagonal => x= -y ∧ (0:ℝ)=0
def twoPlaneMatrix {R : Type*} [Ring R] (p : Bool) (x y : R) : Matrix (Fin 2) (Fin 2) R :=
  if p then !![x,y;y,-x] else !![x,y;-y,x]
noncomputable def forcedRealTwo {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ) (i : ι) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  if i=root then R else -signedTwoReal (A i root)*R.transpose*signedTwoReal (A root i)
noncomputable def realRootConsistency {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ i j, i≠j → signedTwoReal (A i j)*(forcedRealTwo A root R j).transpose+
    forcedRealTwo A root R i*(signedTwoReal (A j i)).transpose=0
theorem real_root_original_component_sections {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (p : Bool) :
    ∃ k : TwoPlaneSectionKind, ∀ x y : ℝ,
      realRootConsistency A root (twoPlaneMatrix p x y) ↔ twoPlaneSectionCondition k x y := by sorry
end
end CompletionTheory

namespace CompletionTheory
theorem real_diagonal_root_forces_full_plane {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (p e : Bool)
    (hR : realRootConsistency A root (twoPlaneMatrix p 1 (if e then -1 else 1)))
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι)) :
    ∀ x y : ℝ, realRootConsistency A root (twoPlaneMatrix p x y) := by sorry
end CompletionTheory

namespace CompletionTheory
open scoped Matrix.Norms.Elementwise
noncomputable def realRootCompletion {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2×ι) (Fin 2×ι) ℝ :=
  normalizedTwoReal A+Matrix.blockDiagonal (fun i => forcedRealTwo A root R i*walshTwoReal)
def IsRealRootSolution {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (R : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  R*R.transpose=1 ∧ realRootConsistency A root R
def IsRealBlockCompletion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) : Prop :=
  H*H.transpose=(Fintype.card (Fin 2×ι) : ℝ) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) ∧
    ∀ p q, p.2≠q.2 → H p q=normalizedTwoReal A p q
def reducedCircleCondition (k : TwoPlaneSectionKind) (x y : ℝ) : Prop :=
  match k with
  | .zero => False
  | .full => x^2+y^2=1
  | .horizontal => y=0 ∧ (x=1 ∨ x= -1)
  | .vertical => x=0 ∧ (y=1 ∨ y= -1)
  | .diagonal => False
  | .antidiagonal => False
def componentSignedPoints (k : TwoPlaneSectionKind) : Finset (ℤ×ℤ) :=
  match k with
  | .zero => ∅
  | .full => {(1,0),(-1,0),(0,1),(0,-1)}
  | .horizontal => {(1,0),(-1,0)}
  | .vertical => {(0,1),(0,-1)}
  | .diagonal => ∅
  | .antidiagonal => ∅
noncomputable def componentSignCompletions {ι : Type*} [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι) (p : Bool) (k : TwoPlaneSectionKind) :
    Finset (Matrix (Fin 2×ι) (Fin 2×ι) ℝ) := by
  classical
  exact (componentSignedPoints k).image (fun z => realRootCompletion A root (twoPlaneMatrix p (z.1 : ℝ) (z.2 : ℝ)))
set_option autoImplicit false
def IsZeroBlockHadamardFilling {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ) : Prop :=
  Matrix.IsHadamard H ∧ ∀ p q,p.2≠q.2 → H p q=W p q
def componentSignCount (k : TwoPlaneSectionKind) : ℕ :=
  match k with
  | .full => 4
  | .horizontal => 2
  | .vertical => 2
  | _ => 0

theorem real_feasibility_and_solution_topology {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι)) :
    ((∃ H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ, IsRealBlockCompletion A H) ↔
      ∃ K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ, IsZeroBlockHadamardFilling (normalizedTwoReal A) K) ∧
    Nonempty ({R : Matrix (Fin 2) (Fin 2) ℝ // IsRealRootSolution A root R} ≃ₜ
      {H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ // IsRealBlockCompletion A H}) ∧
    (∃ k : Bool → TwoPlaneSectionKind,
      (∀ p, k p=.zero ∨ k p=.full ∨ k p=.horizontal ∨ k p=.vertical) ∧
      (∀ R, IsRealRootSolution A root R ↔
        ∃ p x y, R=twoPlaneMatrix p x y ∧ reducedCircleCondition (k p) x y) ∧
      ∀ p,
        (∀ x y, realRootConsistency A root (twoPlaneMatrix p x y) ↔ twoPlaneSectionCondition (k p) x y) ∧
        (∀ K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ,
          K∈componentSignCompletions A root p (k p) ↔
            ∃ x y : ℝ, K=realRootCompletion A root (twoPlaneMatrix p x y) ∧
              IsRealRootSolution A root (twoPlaneMatrix p x y) ∧ Matrix.IsHadamard K) ∧
        (componentSignCompletions A root p (k p)).card=
          componentSignCount (k p) ∧
        ((k p=.horizontal ∨ k p=.vertical) → ∀ x y : ℝ,
          IsRealRootSolution A root (twoPlaneMatrix p x y) →
          ∃ δ : ℝ, 0<δ ∧ ∀ K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ,
            IsRealBlockCompletion A K → dist K (realRootCompletion A root (twoPlaneMatrix p x y))<δ →
            K=realRootCompletion A root (twoPlaneMatrix p x y)) ∧
        (k p=.full → ∀ x y : ℝ, x^2+y^2=1 → ∀ ε : ℝ, 0<ε →
          ∃ K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ, IsRealBlockCompletion A K ∧
            K≠realRootCompletion A root (twoPlaneMatrix p x y) ∧
            dist K (realRootCompletion A root (twoPlaneMatrix p x y))<ε)) ∧
    (∀ H : Matrix (Fin 2×ι) (Fin 2×ι) ℝ, IsRealBlockCompletion A H → ¬Matrix.IsHadamard H →
      ∀ ε : ℝ, 0<ε → ∃ K : Matrix (Fin 2×ι) (Fin 2×ι) ℝ,
        IsRealBlockCompletion A K ∧ K≠H ∧ dist K H<ε) := by sorry
end CompletionTheory

namespace CompletionTheory
set_option autoImplicit false
def fourConferenceInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0,1,1,1; -1,0,-1,1; -1,1,0,-1; -1,-1,1,0]
def conferenceEightStates (i j : Fin 4) : SignedTwoState :=
  if fourConferenceInt i j= -1 then (false,true,true) else (false,false,false)
theorem sharp_zero_preserving_fill_cardinalities {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → SignedTwoState) (root : ι)
    (hW : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hn : 4∣Fintype.card (Fin 2×ι)) :
    (3≤Fintype.card ι → ∃ F : Finset (Matrix (Fin 2×ι) (Fin 2×ι) ℝ),
      (∀ H, H∈F ↔ IsZeroBlockHadamardFilling (normalizedTwoReal A) H) ∧
      (F.card=0 ∨ F.card=2 ∨ F.card=4 ∨ F.card=6)) ∧
    (normalizedTwoReal conferenceEightStates*(normalizedTwoReal conferenceEightStates).transpose=
      ((Fintype.card (Fin 2×Fin 4) : ℝ)-2) • (1 : Matrix (Fin 2×Fin 4) (Fin 2×Fin 4) ℝ) ∧
      ∃ F : Finset (Matrix (Fin 2×Fin 4) (Fin 2×Fin 4) ℝ),
        (∀ H, H∈F ↔ IsZeroBlockHadamardFilling (normalizedTwoReal conferenceEightStates) H) ∧ F.card=6) ∧
    (Fintype.card ι=2 → ∃ F : Finset (Matrix (Fin 2×ι) (Fin 2×ι) ℝ),
      (∀ H, H∈F ↔ IsZeroBlockHadamardFilling (normalizedTwoReal A) H) ∧ F.card=8) := by sorry
end CompletionTheory

namespace HadamardMultibase
set_option autoImplicit false
def HadamardOrder (n : ℕ) : Prop :=
  0 < n ∧ ∃ H : Matrix (Fin n) (Fin n) ℤ, H.IsHadamard
def HasExponent (p : ℕ) : Prop := ∃ t : ℕ, HadamardOrder (2 ^ t * p)
noncomputable def tau (p : ℕ) (h : HasExponent p) : ℕ := by
  classical
  exact Nat.find h
noncomputable def logScale (n : ℕ) : ℝ := Real.log n / Real.log (Real.log n)

end HadamardMultibase
namespace CompletionTheory
open HadamardMultibase
theorem unconditional_uniform_power_buffer :
    ∃ T : ℕ → ℕ, (∀ n, 2≤T n) ∧
      Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (T n : ℝ)) (fun n : ℕ => logScale n) ∧
      (∀ n q : ℕ, Odd q → q≤n → ∀ h : HasExponent q, tau q h≤T n) ∧
      (∀ n k : ℕ, 1≤k → k≤n → HadamardOrder (2^(T n)*k)) ∧
      (∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in Filter.atTop, (2:ℝ)^(T n)≤(n:ℝ)^ε) := by sorry
end CompletionTheory

namespace CompletionTheory
set_option autoImplicit false
noncomputable def signedTwoBlockDiagonal {ι : Type*} [DecidableEq ι] (T : ι → SignedTwoState) :
    Matrix (Fin 2×ι) (Fin 2×ι) ℝ := Matrix.blockDiagonal (fun i => signedTwoReal (T i))
theorem two_fixed_support_pairs_preserve_feasibility {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (A B : ι → ι → SignedTwoState) (r s : ι)
    (hA : normalizedTwoReal A*(normalizedTwoReal A).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hB : normalizedTwoReal B*(normalizedTwoReal B).transpose=
      ((Fintype.card (Fin 2×ι) : ℝ)-2) • (1 : Matrix (Fin 2×ι) (Fin 2×ι) ℝ))
    (hRet : ∀ i, i≠r → i≠s → ∀ a : Fin 2, ∀ q,
      normalizedTwoReal B (a,i) q=normalizedTwoReal A (a,i) q) :
    ∃ T : ι → SignedTwoState,
      normalizedTwoReal B=signedTwoBlockDiagonal T*normalizedTwoReal A ∧
      (∀ i, i≠r → i≠s → signedTwoReal (T i)=1) ∧
      ((∃ H, IsZeroBlockHadamardFilling (normalizedTwoReal A) H) ↔
        ∃ K, IsZeroBlockHadamardFilling (normalizedTwoReal B) K) := by sorry
end CompletionTheory

namespace CompletionTheory
def RealSmallDefectExtension : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ),
    4 ∣ Fintype.card ι → Fintype.card κ < Fintype.card ι →
    Fintype.card ι-Fintype.card κ ≤ 7 →
    (∀ i j,A i j=1 ∨ A i j= -1) →
    A.transpose*A=(Fintype.card ι : ℝ) • (1 : Matrix κ κ ℝ) →
    ∃ w : ι → ℝ,IsCubeVector w ∧ A.transpose.mulVec w=0
def HasQuaternaryCompletion {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ) : Prop :=
  ∃ (hm : m≤n) (H : Matrix (Fin n) (Fin n) ℂ),
    (∀ i j,IsFourthRoot (H i j)) ∧
    H.conjTranspose*H=(n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ∧
    ∀ i j,H i (Fin.castLE hm j)=V i j
theorem small_defect_quaternary_completion (hClassical : RealSmallDefectExtension)
    {n m : ℕ} (hn : Even n) (hm : m≤n) (hr : n-m≤3)
    (V : Matrix (Fin n) (Fin m) ℂ)
    (hV : ∀ i j,IsFourthRoot (V i j))
    (hgram : V.conjTranspose*V=(n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) :
    ∃ H : Matrix (Fin n) (Fin n) ℂ,
      (∀ i j,IsFourthRoot (H i j)) ∧
      H.conjTranspose*H=(n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ∧
      ∀ i j,H i (Fin.castLE hm j)=V i j := by sorry
theorem quaternary_defect_four_completion_gate (hClassical : RealSmallDefectExtension)
    {n m : ℕ} (hn : Even n) (hr : n-m=4)
    (V : Matrix (Fin n) (Fin m) ℂ)
    (hV : ∀ i j,IsFourthRoot (V i j))
    (hgram : V.conjTranspose*V=(n : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) :
    (HasQuaternaryCompletion V ↔
      ∃ z : Fin n → ℂ,(∀ i,IsFourthRoot (z i)) ∧ V.conjTranspose.mulVec z=0) ∧
    ∃ C : Finset (LinearMap.ker V.conjTranspose.mulVecLin),
      C.card≤64 ∧ (∀ v∈C,∀ i,IsFourthRoot (v.val i)) ∧
      (C.Nonempty ↔ HasQuaternaryCompletion V) := by sorry
end CompletionTheory

/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Card
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Lean.Elab.Tactic.Decide
@[expose] public section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
open Matrix Module Submodule
instance trapFivePrime : Fact (Nat.Prime 5) := ⟨by decide⟩

def IsSign (x : ℝ) : Prop := x = 1 ∨ x = -1

def IsSignMatrix {ι κ : Type*} (A : Matrix ι κ ℝ) : Prop :=
  ∀ i j, IsSign (A i j)

def IsPartialHadamard {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix ι κ ℝ) : Prop :=
  IsSignMatrix A ∧ A * Aᵀ = (Fintype.card κ : ℝ) • (1 : Matrix ι ι ℝ)

def NoSignExtension {ι κ : Type*} [Fintype κ] (P : Matrix ι κ ℝ) : Prop :=
  ¬ ∃ f : κ → ℝ, (∀ j, IsSign (f j)) ∧ ∀ i, ∑ j, P i j * f j = 0

def encodedSign (m j : ℕ) : ℤ := if m.testBit j then -1 else 1

def encodedIntFrame {r n : ℕ} (masks : Fin r → ℕ) : Matrix (Fin r) (Fin n) ℤ :=
  fun i j => encodedSign (masks i) j.val

def encodedRealFrame {r n : ℕ} (masks : Fin r → ℕ) : Matrix (Fin r) (Fin n) ℝ :=
  (encodedIntFrame masks).map (Int.castRingHom ℝ)

def modularBitSign (b : Bool) : ℤ := if b then -1 else 1

def positiveFirstBit {N : ℕ} (x : Fin N → Bool) : Prop := ∀ j,j.val=0 → x j=false

noncomputable def codeSignCandidates {q N : ℕ} (C : Submodule (ZMod q) (Fin N → ZMod q)) :
    Finset (Fin N → Bool) := by
  classical
  exact Finset.univ.filter (fun x => positiveFirstBit x ∧
    (fun j => (modularBitSign (x j) : ZMod q))∈C)

def bilinearPivotHyperplane {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (C : Submodule K V) (v : V) : Submodule K V :=
  C ⊓ LinearMap.ker (B v)

def bilinearCodePivot {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (C : Submodule K V) (v : V) : Submodule K V :=
  bilinearPivotHyperplane B C v ⊔ K ∙ v

def coordinateDotForm (K : Type*) [Field K] (N : ℕ) : LinearMap.BilinForm K (Fin N → K) :=
  dotProductBilin K K

def codeTrapOldMasks : Fin 12 → ℕ := ![0,965904,1003736,902980,730036,501868,412530,210762,649754,358790,694982,250934]

def codeTrapOldIntegerMatrix : Matrix (Fin 12) (Fin 20) ℤ := fun i j => if (codeTrapOldMasks i).testBit j.val then -1 else 1

noncomputable def trapMatrixCode {K : Type*} [Field K] {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) K) : Submodule K (Fin N → K) :=
  LinearMap.range (Matrix.toLin' B.transpose)

def trapOldBasis : Matrix (Fin 10) (Fin 20) (ZMod 5) := ![
  ![1,0,0,0,0,0,0,0,0,0,3,2,2,4,4,0,0,1,3,0],
  ![0,1,0,0,0,0,0,0,0,0,4,3,0,1,0,1,4,0,1,0],
  ![0,0,1,0,0,0,0,0,0,0,1,2,3,0,3,1,1,0,0,3],
  ![0,0,0,1,0,0,0,0,0,0,2,4,4,0,2,4,2,1,3,2],
  ![0,0,0,0,1,0,0,0,0,0,1,2,0,3,3,4,2,4,0,0],
  ![0,0,0,0,0,1,0,0,0,0,0,3,3,1,0,0,4,2,4,2],
  ![0,0,0,0,0,0,1,0,0,0,2,2,0,0,0,1,4,3,4,3],
  ![0,0,0,0,0,0,0,1,0,0,0,2,2,2,1,1,3,3,4,1],
  ![0,0,0,0,0,0,0,0,1,0,0,4,1,3,2,2,3,2,1,1],
  ![0,0,0,0,0,0,0,0,0,1,3,2,1,2,1,2,3,0,1,4]
]

def trapNewBasis : Matrix (Fin 10) (Fin 20) (ZMod 5) := ![
  ![1,0,0,0,0,0,0,0,0,3,2,0,3,1,1,3,0,1,0,0],
  ![0,1,0,0,0,0,0,0,0,3,3,0,2,0,0,3,1,0,1,1],
  ![0,0,1,0,0,0,0,0,0,3,0,0,4,2,0,4,1,0,2,3],
  ![0,0,0,1,0,0,0,0,0,4,4,0,0,2,2,0,3,1,3,0],
  ![0,0,0,0,1,0,0,0,0,1,4,0,0,3,1,2,3,4,3,3],
  ![0,0,0,0,0,1,0,0,0,3,4,0,0,0,0,2,1,2,4,3],
  ![0,0,0,0,0,0,1,0,0,0,2,0,2,4,1,4,3,3,0,0],
  ![0,0,0,0,0,0,0,1,0,0,0,0,4,1,2,4,2,3,0,3],
  ![0,0,0,0,0,0,0,0,1,4,2,0,2,0,2,3,4,2,1,4],
  ![0,0,0,0,0,0,0,0,0,0,0,1,4,3,2,1,3,0,2,4]
]

def trapOldInformation : Fin 10 → Fin 20 := ![0,1,2,3,4,5,6,7,8,9]

def trapCompletedMasks : Fin 20 → ℕ := ![0,965904,1003736,730036,501868,412530,210762,358790,694982,250934,7676,126672,307898,444300,581982,645928,683178,816740,855582,886242]

def trapCompletedIntegerMatrix : Matrix (Fin 20) (Fin 20) ℤ := encodedIntFrame trapCompletedMasks

def trapCompletedFieldMatrix : Matrix (Fin 20) (Fin 20) (ZMod 5) :=
  trapCompletedIntegerMatrix.map (Int.castRingHom (ZMod 5))

def trapOldFieldMatrix : Matrix (Fin 12) (Fin 20) (ZMod 5) :=
  codeTrapOldIntegerMatrix.map (Int.castRingHom (ZMod 5))

def trapTenToTwenty (i : Fin 10) : Fin 20 := ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩

noncomputable def trapOldCode : Submodule (ZMod 5) (Fin 20 → ZMod 5) := trapMatrixCode trapOldBasis

noncomputable def trapNewSpanCode : Submodule (ZMod 5) (Fin 20 → ZMod 5) := trapMatrixCode trapNewBasis

def trapPivotVector : Fin 20 → ZMod 5 := trapCompletedFieldMatrix 10

noncomputable def trapCompletedRealMatrix : Matrix (Fin 20) (Fin 20) ℝ := encodedRealFrame trapCompletedMasks

def trapRetainedOldIndex : Fin 10 → Fin 12 := ![0,1,2,4,5,6,7,9,10,11]

noncomputable def trapOldRealMatrix : Matrix (Fin 12) (Fin 20) ℝ := encodedRealFrame codeTrapOldMasks

def trapOldWord (i : Fin 12) (j : Fin 20) : Bool := (codeTrapOldMasks i).testBit j.val

def trapNewWord (i : Fin 20) (j : Fin 20) : Bool := (trapCompletedMasks i).testBit j.val

noncomputable def trapRetainedOldRealClasses (H : Matrix (Fin 20) (Fin 20) ℝ) : Finset (Fin 12) := by
  classical
  exact Finset.univ.filter (fun i => ∃ j : Fin 20,H j=trapOldRealMatrix i ∨ H j= -trapOldRealMatrix i)

noncomputable def trapOldRealRowLoss (H : Matrix (Fin 20) (Fin 20) ℝ) : ℕ :=
  12-(trapRetainedOldRealClasses H).card

attribute [local irreducible] codeSignCandidates
theorem finite_self_dual_code_trap :
    Module.finrank (ZMod 5) trapOldCode=10 ∧
    trapOldCode=(coordinateDotForm (ZMod 5) 20).orthogonal trapOldCode ∧
    (codeSignCandidates trapOldCode).card=12 ∧
    codeSignCandidates trapOldCode=Finset.univ.image trapOldWord ∧
    (∀ i : Fin 12,positiveFirstBit (trapOldWord i)) ∧
    trapOldCode=Submodule.span (ZMod 5) (Set.range trapOldFieldMatrix) ∧
    IsPartialHadamard trapOldRealMatrix ∧ NoSignExtension trapOldRealMatrix ∧
    (∀ z : Fin 20 → ℤ,(∀ j,z j=1 ∨ z j= -1) →
      (∀ i,z≠codeTrapOldIntegerMatrix i ∧ z≠ -codeTrapOldIntegerMatrix i) →
      (Finset.univ.filter (fun i : Fin 12 => (∑ j,codeTrapOldIntegerMatrix i j*z j)=0)).card≤10) ∧
    (∀ i : Fin 10,trapRetainedOldIndex i≠3 ∧ trapRetainedOldIndex i≠8 ∧
      ∀ j,trapCompletedRealMatrix (trapTenToTwenty i) j=trapOldRealMatrix (trapRetainedOldIndex i) j) ∧
    (∀ i : Fin 12,i≠3 → i≠8 → ∃ j,trapRetainedOldIndex j=i) ∧
    Matrix.IsHadamard trapCompletedRealMatrix ∧
    trapNewSpanCode=Submodule.span (ZMod 5) (Set.range trapCompletedFieldMatrix) ∧
    Module.finrank (ZMod 5) trapNewSpanCode=10 ∧
    trapNewSpanCode=(coordinateDotForm (ZMod 5) 20).orthogonal trapNewSpanCode ∧
    trapNewSpanCode=bilinearCodePivot (coordinateDotForm (ZMod 5) 20) trapOldCode trapPivotVector ∧
    Module.finrank (ZMod 5) ↥(trapOldCode ⊓ trapNewSpanCode)=9 ∧
    Module.finrank (ZMod 5) ↥(trapOldCode ⊔ trapNewSpanCode)=11 ∧
    trapNewSpanCode≠trapOldCode ∧
    (codeSignCandidates trapNewSpanCode).card=20 ∧
    codeSignCandidates trapNewSpanCode=Finset.univ.image trapNewWord ∧
    (∀ i : Fin 20,positiveFirstBit (trapNewWord i)) ∧
    (∀ H : Matrix (Fin 20) (Fin 20) ℝ,Matrix.IsHadamard H → 2≤trapOldRealRowLoss H) ∧
    trapOldRealRowLoss trapCompletedRealMatrix=2 := by sorry
end CompletionTheory

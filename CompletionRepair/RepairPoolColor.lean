/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Choose
public import Lean.Elab.Tactic.Decide
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CompletionTheory

def repairPoolMasks : Fin 16 → ℕ := ![3198332,3313468,3859816,6777512,6782212,8735670,8847106,8993716,9397154,10996370,11139280,11254416,13957672,14512420,16111636,16773120]
def repairPoolColor : Fin 16 → Fin 5 := ![4,2,3,0,0,3,1,3,4,4,2,4,1,4,4,0]
def repairPoolRow (i : Fin 16) (j : Fin 24) : ℤ :=
  if (repairPoolMasks i).testBit j.val then -1 else 1

theorem repair_pool_same_color_nonorthogonal : ∀ i j : Fin 16,
    repairPoolColor i=repairPoolColor j →
      (∑ k,repairPoolRow i k*repairPoolRow j k)≠0 := by
  decide +kernel

theorem repair_colored_pool_family_bound {r : ℕ} (A : Fin r → Fin 24 → ℤ)
    (horth : ∀ i j,i≠j → (∑ k,A i k*A j k)=0)
    (hcover : ∀ i,∃ v : Fin 16,(∀ k,A i k=repairPoolRow v k) ∨
      (∀ k,A i k= -repairPoolRow v k)) : r≤5 := by
  classical
  choose v hv using hcover
  let f : Fin r → Fin 5 := fun i => repairPoolColor (v i)
  have hf : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hp := repair_pool_same_color_nonorthogonal (v x) (v y) hxy
    have hz := horth x y hne
    rcases hv x with hx|hx <;> rcases hv y with hy|hy <;>
      simp only [hx,hy,mul_neg,neg_mul,neg_mul_neg,neg_neg,
        Finset.sum_neg_distrib,neg_eq_zero] at hz <;> exact hp hz
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin] using hh

def repairFiveWitnessIndices : Fin 5 → Fin 16 := ![0,4,5,10,12]

theorem repair_five_pool_rows_orthogonal : ∀ i j : Fin 5,
    (∑ k,repairPoolRow (repairFiveWitnessIndices i) k*
      repairPoolRow (repairFiveWitnessIndices j) k)=if i=j then 24 else 0 := by
  decide +kernel
end CompletionTheory

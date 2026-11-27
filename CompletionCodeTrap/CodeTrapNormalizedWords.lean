/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapFieldSeedBoolean
public import CompletionCodeTrap.CodeTrapFiniteFieldFacts
@[expose] public section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory

def trapBitFieldVector (x : Fin 20 → Bool) : Fin 20 → ZMod 5 :=
  fun j => (modularBitSign (x j) : ZMod 5)

theorem trapBitFieldVector_injective : Function.Injective trapBitFieldVector := by
  intro x y h
  funext j
  have hh := congrFun h j
  cases hx : x j <;> cases hy : y j <;>
    norm_num [trapBitFieldVector,modularBitSign,hx,hy] at hh ⊢
  all_goals
    have hn : (1 : ZMod 5)≠ -1 := by decide +kernel
    exact hn (by first | exact hh | exact hh.symm)

theorem trap_seed_mask_complete (n : ℕ) (f : Fin n → Bool) :
    ∃ b : Fin (2^n),∀ j : Fin n,b.val.testBit j.val=f j := by
  let d : Fin n → Fin 2 := fun j => if f j then 1 else 0
  let b : Fin (2^n) := finFunctionFinEquiv d
  refine ⟨b,?_⟩
  intro j
  have hh := congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply d) j)
  change b.val/2^j.val%2=(d j).val at hh
  rw [Nat.testBit_eq_decide_div_mod_eq,hh]
  cases h : f j <;> simp [d,h]

theorem trapInformationSelector_mulVec (J : Fin 10 → Fin 20) (z : Fin 20 → ZMod 5) :
    (trapInformationSelector J).mulVec z=fun k => z (J k) := by
  funext k
  simp [Matrix.mulVec,dotProduct,trapInformationSelector,ite_mul]

theorem trapMatrixCode_normalized_seed_complete
    (B : Matrix (Fin 10) (Fin 20) (ZMod 5)) (J : Fin 10 → Fin 20)
    (hinfo : (trapInformationSelector J)*B.transpose=1) (hzero : J 0=0)
    (x : Fin 20 → Bool) (hfirst : positiveFirstBit x) (hx : trapBitFieldVector x∈trapMatrixCode B) :
    ∃ b : Fin 512,B.transpose.mulVec (trapNormalizedCoefficient b.val)=trapBitFieldVector x := by
  obtain ⟨u,hu⟩ := hx
  have hi : u=(trapInformationSelector J).mulVec (trapBitFieldVector x) := by
    have hh := congrArg (fun z => (trapInformationSelector J).mulVec z) hu
    change (trapInformationSelector J).mulVec (B.transpose.mulVec u)=
      (trapInformationSelector J).mulVec (trapBitFieldVector x) at hh
    rw [Matrix.mulVec_mulVec,hinfo,Matrix.one_mulVec] at hh
    exact hh
  rw [trapInformationSelector_mulVec] at hi
  have hux (j : Fin 10) : u j=trapBitFieldVector x (J j) := congrFun hi j
  obtain ⟨b,hb⟩ := trap_seed_mask_complete 9 (fun k => x (J k.succ))
  have h0 : x 0=false := hfirst 0 rfl
  have he : ∀ j,u j=trapNormalizedCoefficient b.val j := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · rw [hux,hzero]
      simp [trapBitFieldVector,modularBitSign,h0,trapNormalizedCoefficient]
    · rw [hux]
      have hh := hb k
      cases hbit : x (J k.succ) <;>
        simp [trapBitFieldVector,modularBitSign,trapNormalizedCoefficient,Fin.val_succ,hh,hbit]
  refine ⟨b,?_⟩
  have heq : u=trapNormalizedCoefficient b.val := funext he
  rw [← heq]
  exact hu

theorem trapOld_word_seed (x : Fin 20 → Bool) (hfirst : positiveFirstBit x)
    (hx : trapBitFieldVector x∈trapOldCode) :
    ∃ b : Fin 512,trapOldSeedVector b.val=trapBitFieldVector x :=
  trapMatrixCode_normalized_seed_complete trapOldBasis trapOldInformation
    trapOldBasis_information rfl x hfirst hx

theorem trapNew_word_seed (x : Fin 20 → Bool) (hfirst : positiveFirstBit x)
    (hx : trapBitFieldVector x∈trapNewSpanCode) :
    ∃ b : Fin 512,trapNewSeedVector b.val=trapBitFieldVector x :=
  trapMatrixCode_normalized_seed_complete trapNewBasis trapNewInformation
    trapNewBasis_information rfl x hfirst hx
end CompletionTheory

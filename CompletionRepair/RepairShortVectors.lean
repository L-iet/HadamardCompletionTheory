/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionRepair.RepairBooleanEnergy
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.ByContra
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace CompletionTheory

theorem repair_odd_square_one (z : ℤ) (hz : z%2=1) : 1≤z^2 := by
  have hne : z≠0 := by intro h; simp [h] at hz
  have hh : 0<z^2 := sq_pos_of_ne_zero hne
  omega

theorem repair_odd_coordinate_floor {n : ℕ} (z : Fin n → ℤ)
    (hz : ∀ i,z i%2=1) (i : Fin n) :
    z i^2+(n : ℤ)-1≤∑ j,z j^2 := by
  have hdelta : ∀ j,0≤z j^2-1 := fun j => by have h := repair_odd_square_one _ (hz j); omega
  have hh := Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin n))) => hdelta j) (Finset.mem_univ i)
  have hs : (∑ j,(z j^2-1))=(∑ j,z j^2)-(n : ℤ) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hs] at hh
  omega

theorem repair_short_odd_alphabet (z : Fin 24 → ℤ) (hz : ∀ i,z i%2=1)
    (hshort : (∑ i,z i^2)<40) :
    ∀ i,z i=1 ∨ z i= -1 ∨ z i=3 ∨ z i= -3 := by
  intro i
  have hh := repair_odd_coordinate_floor z hz i
  have hs : z i^2≤16 := by omega
  have hlo : -4≤z i := by
    by_contra h
    have hle : z i≤ -5 := by omega
    nlinarith [sq_nonneg (z i+5)]
  have hhi : z i≤4 := by
    by_contra h
    have hle : 5≤z i := by omega
    nlinarith [sq_nonneg (z i-5)]
  have hmod := hz i
  omega

theorem repair_short_at_most_one_three (z : Fin 24 → ℤ) (hz : ∀ i,z i%2=1)
    (hshort : (∑ i,z i^2)<40) (i j : Fin 24)
    (hi : z i^2=9) (hj : z j^2=9) : i=j := by
  by_contra hij
  have hdelta : ∀ k,0≤z k^2-1 := fun k => by have h := repair_odd_square_one _ (hz k); omega
  have hp : ∀ k,(if k=i then (8 : ℤ) else 0)+(if k=j then 8 else 0)≤z k^2-1 := by
    intro k
    by_cases hki : k=i
    · subst k
      simp [hij,hi]
    · by_cases hkj : k=j
      · subst k
        simp [hki,hj]
      · simpa [hki,hkj] using hdelta k
  have hh := Finset.sum_le_sum (fun k (_ : k∈(Finset.univ : Finset (Fin 24))) => hp k)
  simp only [Finset.sum_add_distrib] at hh
  simp at hh
  omega

theorem repair_bool_mask_complete (f : Fin 11 → Bool) :
    ∃ b : Fin 2048,∀ j : Fin 11,b.val.testBit j.val=f j := by
  let d : Fin 11 → Fin 2 := fun j => if f j then 1 else 0
  let b : Fin 2048 := finFunctionFinEquiv d
  refine ⟨b,?_⟩
  intro j
  have hh := congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply d) j)
  change b.val/2^j.val%2=(d j).val at hh
  rw [Nat.testBit_eq_decide_div_mod_eq,hh]
  cases h : f j <;> simp [d,h]


theorem repair_four_value_shape (u : Fin 12 → ℤ)
    (hval : ∀ j,u j=1 ∨ u j= -1 ∨ u j=3 ∨ u j= -3)
    (hsingle : ∀ i j,u i^2=9 → u j^2=9 → i=j) :
    ∃ e : Fin 13,∀ j,if e.val=j.val+1 then u j=3 ∨ u j= -3 else u j=1 ∨ u j= -1 := by
  by_cases hex : ∃ j,u j^2=9
  · obtain ⟨j,hj⟩ := hex
    let e : Fin 13 := ⟨j.val+1,by have hh := j.isLt; omega⟩
    refine ⟨e,?_⟩
    intro k
    by_cases he : e.val=k.val+1
    · rw [if_pos he]
      have hkj : k=j := Fin.ext (by dsimp [e] at he; omega)
      subst k
      rcases hval j with h|h|h|h
      · norm_num [h] at hj
      · norm_num [h] at hj
      · exact Or.inl h
      · exact Or.inr h
    · rw [if_neg he]
      have hkj : k≠j := by intro hh; subst k; simp [e] at he
      have hnot : u k^2≠9 := fun hk => hkj (hsingle k j hk hj)
      rcases hval k with h|h|h|h
      · exact Or.inl h
      · exact Or.inr h
      · apply False.elim; apply hnot; norm_num [h]
      · apply False.elim; apply hnot; norm_num [h]
  · refine ⟨0,?_⟩
    intro k
    have he : (0 : Fin 13).val≠k.val+1 := by omega
    rw [if_neg he]
    have hnot : u k^2≠9 := fun hk => hex ⟨k,hk⟩
    rcases hval k with h|h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · apply False.elim; apply hnot; norm_num [h]
    · apply False.elim; apply hnot; norm_num [h]

theorem repair_positive_shape_encoding (u : Fin 12 → ℤ) (hpos : 0<u 0)
    (e : Fin 13)
    (hshape : ∀ j,if e.val=j.val+1 then u j=3 ∨ u j= -3 else u j=1 ∨ u j= -1) :
    ∃ b : Fin 2048,∀ j,u j=repairBooleanU e.val b.val j.val := by
  obtain ⟨b,hb⟩ := repair_bool_mask_complete (fun k => decide (u k.succ<0))
  refine ⟨b,?_⟩
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · have hs := hshape 0
    by_cases he : e.val=1
    · have hu : u 0=3 := by simp [he] at hs; omega
      simp [repairBooleanU,he,hu]
    · have hu : u 0=1 := by simp [he] at hs; omega
      simp [repairBooleanU,he,hu]
  · have hs := hshape k.succ
    have hbit := hb k
    by_cases he : e.val=k.succ.val+1
    · have hc : u k.succ=3 ∨ u k.succ= -3 := by simpa only [if_pos he] using hs
      have he' : e.val=(k.val+1)+1 := by simpa only [Fin.val_succ] using he
      by_cases hn : u k.succ<0
      · have hu : u k.succ= -3 := by omega
        simp [repairBooleanU,Fin.val_succ,hbit,he',hu]
      · have hu : u k.succ=3 := by omega
        simp [repairBooleanU,Fin.val_succ,hbit,he',hu]
    · have hc : u k.succ=1 ∨ u k.succ= -1 := by simpa only [if_neg he] using hs
      have he' : e.val≠(k.val+1)+1 := by simpa only [Fin.val_succ] using he
      by_cases hn : u k.succ<0
      · have hu : u k.succ= -1 := by omega
        simp [repairBooleanU,Fin.val_succ,hbit,he',hu]
      · have hu : u k.succ=1 := by omega
        simp [repairBooleanU,Fin.val_succ,hbit,he',hu]

end CompletionTheory

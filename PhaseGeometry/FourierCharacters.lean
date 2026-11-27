/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import PhaseGeometry.FourPhaseSeparation
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.LinearAlgebra.Matrix.Rank
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PhaseGeometry
open scoped ComplexConjugate Matrix

noncomputable def characterMatrix {n : ℕ} [NeZero n] (a : ZMod n) : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j => ZMod.stdAddChar (a*i*j)

theorem standard_character_sum {n : ℕ} [NeZero n] (t : ZMod n) :
    (∑ j : ZMod n,ZMod.stdAddChar (t*j))=if t=0 then (n : ℂ) else 0 := by
  by_cases ht : t=0
  · simp [ht,ZMod.card]
  · rw [if_neg ht]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n ht)

theorem characterMatrix_unit {n : ℕ} [NeZero n] (a i j : ZMod n) :
    ‖characterMatrix a i j‖=1 := AddChar.norm_apply _ _

theorem characterMatrix_gram {n : ℕ} [NeZero n] (a i k : ZMod n) :
    (∑ j,characterMatrix a i j*conj (characterMatrix a k j))=
      if a*(i-k)=0 then (n : ℂ) else 0 := by
  have he (j : ZMod n) : characterMatrix a i j*conj (characterMatrix a k j)=
      ZMod.stdAddChar (a*(i-k)*j) := by
    simp only [characterMatrix,← AddChar.map_neg_eq_conj,← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [he]
  exact standard_character_sum _

theorem fourier_fourth_power {n : ℕ} [NeZero n] (i j : ZMod n) :
    (characterMatrix (1 : ZMod n) i j)^4=characterMatrix (4 : ZMod n) i j := by
  rw [characterMatrix,← AddChar.map_nsmul_eq_pow]
  congr 1
  simp only [nsmul_eq_mul,one_mul]
  ring

theorem fourier_character_gram_matrix {n : ℕ} [NeZero n] :
    characterMatrix (1 : ZMod n)*(characterMatrix (1 : ZMod n))ᴴ=(n : ℂ) • (1 : Matrix (ZMod n) (ZMod n) ℂ) := by
  classical
  ext i k
  change (∑ j,characterMatrix (1 : ZMod n) i j*conj (characterMatrix (1 : ZMod n) k j))=_
  rw [characterMatrix_gram]
  by_cases hik : i=k
  · subst k; simp
  · simp [one_mul,sub_eq_zero,hik,Matrix.one_apply]

theorem fourier_character_rows_independent {n : ℕ} [NeZero n] :
    LinearIndependent ℂ (characterMatrix (1 : ZMod n)).row := by
  classical
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hd := congrArg Matrix.det (fourier_character_gram_matrix (n := n))
  rw [Matrix.det_mul,Matrix.det_smul,Matrix.det_one,mul_one,ZMod.card] at hd
  change LinearIndependent ℂ (fun i : ZMod n => characterMatrix (1 : ZMod n) i)
  apply Matrix.linearIndependent_rows_of_det_ne_zero (A := characterMatrix (1 : ZMod n))
  intro hh
  rw [hh,zero_mul] at hd
  exact (pow_ne_zero n hn) hd.symm

theorem characterMatrix_rank_image {n : ℕ} [NeZero n] (a : ZMod n) :
    (characterMatrix a).rank=(Finset.univ.image (fun i : ZMod n => a*i)).card := by
  classical
  let R : Finset (ZMod n) := Finset.univ.image (fun i : ZMod n => a*i)
  let v : R → (ZMod n → ℂ) := fun r => (characterMatrix (1 : ZMod n)).row r.val
  have hind : LinearIndependent ℂ v := (fourier_character_rows_independent (n := n)).comp
    (fun r : R => r.val) Subtype.val_injective
  have hrange : Set.range (characterMatrix a).row=Set.range v := by
    ext w
    constructor
    · rintro ⟨i,rfl⟩
      refine ⟨⟨a*i,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩,?_⟩
      funext j
      simp only [v,Matrix.row,characterMatrix,one_mul]
    · rintro ⟨r,rfl⟩
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp r.property
      refine ⟨i,?_⟩
      funext j
      simp only [v,Matrix.row,characterMatrix,one_mul]
      rw [← he]
  rw [Matrix.rank_eq_finrank_span_row,hrange,finrank_span_eq_card hind]
  exact Fintype.card_coe R

theorem zmod_mul_image_card {n : ℕ} [NeZero n] (a : ZMod n) :
    (Finset.univ.image (fun i : ZMod n => a*i)).card=addOrderOf a := by
  classical
  let R : Finset (ZMod n) := Finset.univ.image (fun i : ZMod n => a*i)
  have hs : (R : Set (ZMod n))=(AddSubgroup.zmultiples a : Set (ZMod n)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      apply AddSubgroup.mem_zmultiples_iff.mpr
      refine ⟨(i.val : ℤ),?_⟩
      simp [zsmul_eq_mul,ZMod.natCast_zmod_val,mul_comm]
    · intro hx
      obtain ⟨k,hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
      apply Finset.mem_image.mpr
      refine ⟨(k : ZMod n),Finset.mem_univ _,?_⟩
      simpa [zsmul_eq_mul,mul_comm] using hk
  calc
    _ = Nat.card R := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    _ = Nat.card (AddSubgroup.zmultiples a) := Nat.card_congr (Equiv.cast (congrArg (fun S : Set (ZMod n) => ↥S) hs))
    _ = addOrderOf a := Nat.card_zmultiples a

theorem powered_fourier_character_rank {n : ℕ} [NeZero n] (b : ℕ) :
    (characterMatrix (b : ZMod n)).rank=n/Nat.gcd n b := by
  rw [characterMatrix_rank_image,zmod_mul_image_card,ZMod.addOrderOf_coe b (NeZero.ne n)]

theorem fourth_fourier_character_rank {n : ℕ} [NeZero n] :
    Matrix.rank (fun i j : ZMod n => (characterMatrix (1 : ZMod n) i j)^4 : Matrix (ZMod n) (ZMod n) ℂ)=
      n/Nat.gcd n 4 := by
  have he : (fun i j : ZMod n => (characterMatrix (1 : ZMod n) i j)^4 : Matrix (ZMod n) (ZMod n) ℂ)=
      characterMatrix (4 : ZMod n) := by ext i j; exact fourier_fourth_power i j
  rw [he]
  exact powered_fourier_character_rank 4
end PhaseGeometry

/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.FieldTheory.Finiteness
public import CompletionTheory.CodeNeighbors
public import CompletionTheory.NeighborIncidence
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
@[expose] public section
set_option maxHeartbeats 2000000
namespace CompletionTheory
open Matrix

def rankOneTwo {K : Type*} [Mul K] (u v : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => u i*v j

theorem two_by_two_minor {K : Type*} [Field K] (M : Matrix (Fin 2) (Fin 2) K)
    (hM : M.det=0) (i j p q : Fin 2) : M i j*M p q=M i q*M p j := by
  have hd : M 0 0*M 1 1-M 0 1*M 1 0=0 := by simpa [Matrix.det_fin_two] using hM
  have heq := sub_eq_zero.mp hd
  fin_cases i <;> fin_cases j <;> fin_cases p <;> fin_cases q <;> dsimp <;>
    first | (solve | ring) | (solve | simpa only [mul_comm] using heq) |
      (solve | simpa only [mul_comm] using heq.symm)

theorem det_zero_nonzero_rank_one {K : Type*} [Field K] (M : Matrix (Fin 2) (Fin 2) K)
    (hM : M.det=0) (hne : M≠0) :
    ∃ u v : Fin 2 → K,u≠0 ∧ v≠0 ∧ M=rankOneTwo u v := by
  classical
  obtain ⟨p,q,hpq⟩ : ∃ p q,M p q≠0 := by
    by_contra hn
    apply hne
    ext i j
    by_contra hij
    exact hn ⟨i,j,hij⟩
  let u := fun i => M i q
  let v := fun j => M p j/M p q
  refine ⟨u,v,?_,?_,?_⟩
  · intro hu
    have hh := congrFun hu p
    exact hpq hh
  · intro hv
    have hh := congrFun hv q
    change M p q/M p q=0 at hh
    rw [div_self hpq] at hh
    exact one_ne_zero hh
  · ext i j
    change M i j=M i q*(M p j/M p q)
    rw [← mul_div_assoc]
    apply (eq_div_iff hpq).mpr
    simpa only [mul_div_assoc] using two_by_two_minor M hM i j p q

theorem rankOneTwo_det_add {K : Type*} [CommRing K] (u v s t : Fin 2 → K) :
    (rankOneTwo u v+rankOneTwo s t).det=
      (u 0*s 1-u 1*s 0)*(v 0*t 1-v 1*t 0) := by
  simp only [Matrix.det_fin_two,Matrix.add_apply,rankOneTwo]
  ring

theorem grid_pair_compatibility {K : Type*} [Field K] (u v s t : Fin 2 → K) :
    (rankOneTwo u v+rankOneTwo s t).det=0 ↔
      u 0*s 1-u 1*s 0=0 ∨ v 0*t 1-v 1*t 0=0 := by
  rw [rankOneTwo_det_add,mul_eq_zero]

theorem finite_grid_clique_on_line {α β : Type*} (S : Set (α×β))
    (hS : ∀ x∈S,∀ y∈S,x.1=y.1 ∨ x.2=y.2) :
    (∀ x∈S,∀ y∈S,x.1=y.1) ∨ (∀ x∈S,∀ y∈S,x.2=y.2) := by
  classical
  by_cases h : ∀ x∈S,∀ y∈S,x.1=y.1
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨x,hx,y,hy,hxy⟩ := h
    have hxy2 := (hS x hx y hy).resolve_left hxy
    have all (z) (hz : z∈S) : z.2=x.2 := by
      rcases hS z hz x hx with hzx|hzx
      · rcases hS z hz y hy with hzy|hzy
        · exact (hxy (hzx.symm.trans hzy)).elim
        · exact hzy.trans hxy2.symm
      · exact hzx
    intro z hz w hw
    exact (all z hz).trans (all w hw).symm

theorem two_vector_det_zero_iff {K : Type*} [Field K] (u s : Fin 2 → K) (hu : u≠0) :
    u 0*s 1-u 1*s 0=0 ↔ ∃ a : K,s=a • u := by
  classical
  constructor
  · intro hdet
    by_cases hu0 : u 0=0
    · have hu1 : u 1≠0 := by
        intro hz
        apply hu
        ext i
        fin_cases i <;> assumption
      have hs0 : s 0=0 := by
        rw [hu0,zero_mul,zero_sub,neg_eq_zero] at hdet
        exact (mul_eq_zero.mp hdet).resolve_left hu1
      refine ⟨s 1/u 1,?_⟩
      funext i
      fin_cases i
      · simp [hu0,hs0]
      · simp [hu1]
    · refine ⟨s 0/u 0,?_⟩
      funext i
      fin_cases i
      · simp [hu0]
      · change s 1=(s 0/u 0)*u 1
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hu0).mpr
        linear_combination hdet
  · rintro ⟨a,rfl⟩
    simp only [Pi.smul_apply,smul_eq_mul]
    ring

theorem rankOneTwo_ne_zero {K : Type*} [Field K] (u v : Fin 2 → K) (hu : u≠0) (hv : v≠0) :
    rankOneTwo u v≠0 := by
  intro heq
  obtain ⟨i,hi⟩ : ∃ i,u i≠0 := by
    by_contra hn
    apply hu
    ext i
    by_contra h
    exact hn ⟨i,h⟩
  apply hv
  ext j
  have hh := congrArg (fun M => M i j) heq
  change u i*v j=0 at hh
  exact (mul_eq_zero.mp hh).resolve_left hi

theorem rankOneTwo_det {K : Type*} [CommRing K] (u v : Fin 2 → K) :
    (rankOneTwo u v).det=0 := by
  simp only [Matrix.det_fin_two,rankOneTwo]
  ring

theorem projective_line_card {K : Type*} [Field K] [Fintype K] :
    Nat.card (Projectivization K (Fin 2 → K))=Nat.card K+1 := by
  rw [Projectivization.card'',Nat.card_fun,Nat.card_fin]
  have hq : 2≤Nat.card K := by
    rw [← Fintype.card_eq_nat_card]
    exact Fintype.one_lt_card
  rw [← Nat.geomSum_eq hq]
  simp [Finset.sum_range_succ,Nat.add_comm]

theorem rankOneTwo_factor_lines {K : Type*} [Field K] (u v s t : Fin 2 → K)
    (hu : u≠0) (hv : v≠0) (heq : rankOneTwo u v=rankOneTwo s t) :
    (∃ a : K,a≠0 ∧ u=a • s) ∧ (∃ b : K,b≠0 ∧ v=b • t) := by
  classical
  obtain ⟨p,hp⟩ : ∃ p,u p≠0 := by
    by_contra hn
    apply hu
    ext i
    by_contra hi
    exact hn ⟨i,hi⟩
  obtain ⟨q,hq⟩ : ∃ q,v q≠0 := by
    by_contra hn
    apply hv
    ext i
    by_contra hi
    exact hn ⟨i,hi⟩
  have hcoord (i j) : u i*v j=s i*t j := congrArg (fun M => M i j) heq
  have hprod : s p*t q≠0 := by rw [← hcoord p q];exact mul_ne_zero hp hq
  have hsp : s p≠0 := (mul_ne_zero_iff.mp hprod).1
  have htq : t q≠0 := (mul_ne_zero_iff.mp hprod).2
  constructor
  · refine ⟨t q/v q,div_ne_zero htq hq,?_⟩
    funext i
    change u i=(t q/v q)*s i
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hq).mpr
    linear_combination hcoord i q
  · refine ⟨s p/u p,div_ne_zero hsp hp,?_⟩
    funext j
    change v j=(s p/u p)*t j
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hp).mpr
    linear_combination hcoord p j

def rankOneQuadricPoints (K : Type*) [Field K] :=
  {P : Projectivization K (Matrix (Fin 2) (Fin 2) K) // P.rep.det=0}

noncomputable def gridQuadricPoint {K : Type*} [Field K]
    (x : Projectivization K (Fin 2 → K) × Projectivization K (Fin 2 → K)) : rankOneQuadricPoints K := by
  let M := rankOneTwo x.1.rep x.2.rep
  have hM : M≠0 := rankOneTwo_ne_zero _ _ x.1.rep_nonzero x.2.rep_nonzero
  refine ⟨Projectivization.mk K M hM,?_⟩
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep K M hM
  rw [← hc,Units.smul_def,Matrix.det_smul,rankOneTwo_det,mul_zero]

theorem gridQuadricPoint_bijective {K : Type*} [Field K] :
    Function.Bijective (gridQuadricPoint (K := K)) := by
  constructor
  · rintro ⟨u,v⟩ ⟨s,t⟩ heq
    have hmk := congrArg Subtype.val heq
    change Projectivization.mk K (rankOneTwo u.rep v.rep) _=
      Projectivization.mk K (rankOneTwo s.rep t.rep) _ at hmk
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp hmk
    have hout : rankOneTwo u.rep v.rep=rankOneTwo (a • s.rep) t.rep := by
      rw [← ha]
      ext i j
      simp [rankOneTwo,smul_eq_mul,mul_assoc]
    obtain ⟨⟨b,hb,hbu⟩,⟨c,hc,hcv⟩⟩ :=
      rankOneTwo_factor_lines _ _ _ _ u.rep_nonzero v.rep_nonzero hout
    have hus : u=s := by
      have hh := (Projectivization.mk_eq_mk_iff' K u.rep s.rep u.rep_nonzero s.rep_nonzero).mpr
        ⟨b*a,by simpa only [smul_smul] using hbu.symm⟩
      simpa only [Projectivization.mk_rep] using hh
    have hvt : v=t := by
      have hh := (Projectivization.mk_eq_mk_iff' K v.rep t.rep v.rep_nonzero t.rep_nonzero).mpr
        ⟨c,hcv.symm⟩
      simpa only [Projectivization.mk_rep] using hh
    exact Prod.ext hus hvt
  · intro P
    obtain ⟨u,v,hu,hv,hM⟩ := det_zero_nonzero_rank_one P.val.rep P.property P.val.rep_nonzero
    refine ⟨⟨Projectivization.mk K u hu,Projectivization.mk K v hv⟩,?_⟩
    apply Subtype.ext
    change Projectivization.mk K (rankOneTwo (Projectivization.mk K u hu).rep
      (Projectivization.mk K v hv).rep) _=P.val
    obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K u hu
    obtain ⟨b,hb⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
    rw [← P.val.mk_rep]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨(a : K)*(b : K),?_⟩
    rw [hM]
    ext i j
    rw [← ha,← hb]
    simp [rankOneTwo,Units.smul_def,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm]

theorem finite_rank_one_quadric_card {K : Type*} [Field K] [Fintype K] :
    Nat.card (rankOneQuadricPoints K)=(Nat.card K+1)^2 := by
  rw [← Nat.card_congr (Equiv.ofBijective gridQuadricPoint
    (gridQuadricPoint_bijective (K := K))),Nat.card_prod,projective_line_card]
  ring

def columnDetFunctional {K : Type*} [CommRing K] (u : Fin 2 → K) (j : Fin 2) :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] K where
  toFun M := u 0*M 1 j-u 1*M 0 j
  map_add' M N := by simp only [Matrix.add_apply];ring
  map_smul' a M := by simp only [Matrix.smul_apply,smul_eq_mul,RingHom.id_apply];ring

def columnLineSpace {K : Type*} [CommRing K] (u : Fin 2 → K) :
    Submodule K (Matrix (Fin 2) (Fin 2) K) := ⨅ j,LinearMap.ker (columnDetFunctional u j)

def rowDetFunctional {K : Type*} [CommRing K] (v : Fin 2 → K) (i : Fin 2) :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] K where
  toFun M := v 0*M i 1-v 1*M i 0
  map_add' M N := by simp only [Matrix.add_apply];ring
  map_smul' a M := by simp only [Matrix.smul_apply,smul_eq_mul,RingHom.id_apply];ring

def rowLineSpace {K : Type*} [CommRing K] (v : Fin 2 → K) :
    Submodule K (Matrix (Fin 2) (Fin 2) K) := ⨅ i,LinearMap.ker (rowDetFunctional v i)

theorem mem_columnLineSpace_iff {K : Type*} [Field K] (u : Fin 2 → K) (hu : u≠0)
    (M : Matrix (Fin 2) (Fin 2) K) : M∈columnLineSpace u ↔ ∃ v,M=rankOneTwo u v := by
  classical
  constructor
  · intro hM
    have hcols (j : Fin 2) : ∃ a : K,(fun i => M i j)=a • u := by
      apply (two_vector_det_zero_iff u _ hu).mp
      exact (Submodule.mem_iInf _).mp hM j
    choose v hv using hcols
    refine ⟨v,?_⟩
    ext i j
    have hh := congrFun (hv j) i
    simpa only [Pi.smul_apply,smul_eq_mul,mul_comm,rankOneTwo] using hh
  · rintro ⟨v,rfl⟩
    apply (Submodule.mem_iInf _).mpr
    intro j
    change u 0*(u 1*v j)-u 1*(u 0*v j)=0
    ring

theorem mem_rowLineSpace_iff {K : Type*} [Field K] (v : Fin 2 → K) (hv : v≠0)
    (M : Matrix (Fin 2) (Fin 2) K) : M∈rowLineSpace v ↔ ∃ u,M=rankOneTwo u v := by
  classical
  constructor
  · intro hM
    have hrows (i : Fin 2) : ∃ a : K,M i=a • v := by
      apply (two_vector_det_zero_iff v _ hv).mp
      exact (Submodule.mem_iInf _).mp hM i
    choose u hu using hrows
    refine ⟨u,?_⟩
    ext i j
    exact congrFun (hu i) j
  · rintro ⟨u,rfl⟩
    apply (Submodule.mem_iInf _).mpr
    intro i
    change v 0*(u i*v 1)-v 1*(u i*v 0)=0
    ring

theorem determinant_zero_subspace_in_one_ruling {K : Type*} [Field K]
    (W : Submodule K (Matrix (Fin 2) (Fin 2) K)) (hW : ∀ M∈W,M.det=0)
    (A : Matrix (Fin 2) (Fin 2) K) (hA : A∈W) (hA0 : A≠0) :
    ∃ u v : Fin 2 → K,u≠0 ∧ v≠0 ∧ A=rankOneTwo u v ∧
      (W≤columnLineSpace u ∨ W≤rowLineSpace v) := by
  classical
  obtain ⟨u,v,hu,hv,hAv⟩ := det_zero_nonzero_rank_one A (hW A hA) hA0
  have hpool (M) (hM : M∈W) : M∈columnLineSpace u ∨ M∈rowLineSpace v := by
    by_cases hz : M=0
    · left;rw [hz];exact Submodule.zero_mem _
    obtain ⟨s,t,hs,ht,hst⟩ := det_zero_nonzero_rank_one M (hW M hM) hz
    have hh := hW (A+M) (W.add_mem hA hM)
    rw [hAv,hst,grid_pair_compatibility] at hh
    rcases hh with hcol|hrow
    · obtain ⟨a,ha⟩ := (two_vector_det_zero_iff u s hu).mp hcol
      left
      apply (mem_columnLineSpace_iff u hu M).mpr
      refine ⟨a • t,?_⟩
      rw [hst,ha]
      ext i j
      simp only [rankOneTwo,Pi.smul_apply,smul_eq_mul]
      ring
    · obtain ⟨a,ha⟩ := (two_vector_det_zero_iff v t hv).mp hrow
      right
      apply (mem_rowLineSpace_iff v hv M).mpr
      refine ⟨a • s,?_⟩
      rw [hst,ha]
      ext i j
      simp only [rankOneTwo,Pi.smul_apply,smul_eq_mul]
      ring
  refine ⟨u,v,hu,hv,hAv,?_⟩
  by_cases hle : W≤columnLineSpace u
  · exact Or.inl hle
  · right
    obtain ⟨E,hEW,hEn⟩ := SetLike.not_le_iff_exists.mp hle
    have hEr := (hpool E hEW).resolve_left hEn
    intro M hM
    by_contra hMr
    have hMc := (hpool M hM).resolve_right hMr
    rcases hpool (M+E) (W.add_mem hM hEW) with hsumc|hsumr
    · exact hEn (by simpa using (columnLineSpace u).sub_mem hsumc hMc)
    · exact hMr (by simpa using (rowLineSpace v).sub_mem hsumr hEr)

def rankOneTwoColumnMap {K : Type*} [CommRing K] (u : Fin 2 → K) :
    (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun := rankOneTwo u
  map_add' v w := by ext i j;simp [rankOneTwo,mul_add]
  map_smul' a v := by ext i j;simp [rankOneTwo,smul_eq_mul,mul_left_comm]

def rankOneTwoRowMap {K : Type*} [CommRing K] (v : Fin 2 → K) :
    (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun u := rankOneTwo u v
  map_add' u w := by ext i j;simp [rankOneTwo,add_mul]
  map_smul' a u := by ext i j;simp [rankOneTwo,smul_eq_mul,mul_assoc]

theorem columnLineSpace_finrank {K : Type*} [Field K] (u : Fin 2 → K) (hu : u≠0) :
    Module.finrank K (columnLineSpace u)=2 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i,u i≠0 := by
    by_contra hn
    apply hu
    ext j
    by_contra hj
    exact hn ⟨j,hj⟩
  have hinj : Function.Injective (rankOneTwoColumnMap u) := by
    intro v w h
    funext j
    have hh := congrArg (fun M => M i j) h
    exact mul_left_cancel₀ hi hh
  have hrange : LinearMap.range (rankOneTwoColumnMap u)=columnLineSpace u := by
    ext M
    rw [mem_columnLineSpace_iff u hu]
    constructor
    · rintro ⟨v,hv⟩
      exact ⟨v,hv.symm⟩
    · rintro ⟨v,hv⟩
      exact ⟨v,hv.symm⟩
  rw [← hrange,LinearMap.finrank_range_of_inj hinj]
  simp

theorem rowLineSpace_finrank {K : Type*} [Field K] (v : Fin 2 → K) (hv : v≠0) :
    Module.finrank K (rowLineSpace v)=2 := by
  classical
  obtain ⟨j,hj⟩ : ∃ j,v j≠0 := by
    by_contra hn
    apply hv
    ext i
    by_contra hi
    exact hn ⟨i,hi⟩
  have hinj : Function.Injective (rankOneTwoRowMap v) := by
    intro u w h
    funext i
    have hh := congrArg (fun M => M i j) h
    exact mul_right_cancel₀ hj hh
  have hrange : LinearMap.range (rankOneTwoRowMap v)=rowLineSpace v := by
    ext M
    rw [mem_rowLineSpace_iff v hv]
    constructor
    · rintro ⟨u,hu⟩
      exact ⟨u,hu.symm⟩
    · rintro ⟨u,hu⟩
      exact ⟨u,hu.symm⟩
  rw [← hrange,LinearMap.finrank_range_of_inj hinj]
  simp

theorem determinant_zero_plane_ruling_classification {K : Type*} [Field K]
    (W : Submodule K (Matrix (Fin 2) (Fin 2) K)) (hW : ∀ M∈W,M.det=0)
    (hdim : Module.finrank K W=2) :
    (∃ u : Fin 2 → K,u≠0 ∧ W=columnLineSpace u) ∨
      (∃ v : Fin 2 → K,v≠0 ∧ W=rowLineSpace v) := by
  have hne : W≠⊥ := by intro hz;rw [hz,finrank_bot] at hdim;omega
  obtain ⟨A,hA,hA0⟩ := (Submodule.ne_bot_iff W).mp hne
  obtain ⟨u,v,hu,hv,hAv,hle⟩ := determinant_zero_subspace_in_one_ruling W hW A hA hA0
  rcases hle with hcol|hrow
  · left
    refine ⟨u,hu,Submodule.eq_of_le_of_finrank_le hcol ?_⟩
    rw [columnLineSpace_finrank u hu,hdim]
  · right
    refine ⟨v,hv,Submodule.eq_of_le_of_finrank_le hrow ?_⟩
    rw [rowLineSpace_finrank v hv,hdim]

theorem self_dual_iff_isotropic_half_dimension {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (L : Submodule K V) (hhalf : Module.finrank K L+Module.finrank K L=Module.finrank K V) :
    L=B.orthogonal L ↔ ∀ x∈L,B x x=0 := by
  constructor
  · intro hL x hx
    exact ((SetLike.ext_iff.mp hL x).mp hx) x hx
  · intro hz
    have hle : L≤B.orthogonal L := by
      intro x hx y hy
      have hsum := hz (x+y) (L.add_mem hx hy)
      have hxx := hz x hx
      have hyy := hz y hy
      simp only [map_add,LinearMap.add_apply] at hsum
      rw [hB.eq x y] at hsum
      have hh : 2*B y x=0 := by linear_combination hsum-hxx-hyy
      exact (mul_eq_zero.mp hh).resolve_left htwo
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [B.finrank_orthogonal hnd L]
    omega

theorem determinant_model_self_dual_iff {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (E : V ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) (hnorm : ∀ x,B x x=2*(E x).det)
    (hV : Module.finrank K V=4) (L : Submodule K V) :
    L=B.orthogonal L ↔
      Module.finrank K (L.map E.toLinearMap)=2 ∧ ∀ M∈L.map E.toLinearMap,M.det=0 := by
  constructor
  · intro hL
    have hdim := B.finrank_add_finrank_orthogonal' L
    rw [← hL,hnd.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero,hV] at hdim
    refine ⟨?_,?_⟩
    · rw [E.finrank_map_eq]
      omega
    · rintro M ⟨x,hx,rfl⟩
      have hz : B x x=0 := ((SetLike.ext_iff.mp hL x).mp hx) x hx
      rw [hnorm] at hz
      exact (mul_eq_zero.mp hz).resolve_left htwo
  · rintro ⟨hdim,hdet⟩
    rw [E.finrank_map_eq] at hdim
    have hhalf : Module.finrank K L+Module.finrank K L=Module.finrank K V := by omega
    apply (self_dual_iff_isotropic_half_dimension htwo B hB hnd L hhalf).mpr
    intro x hx
    rw [hnorm,hdet (E x) ⟨x,hx,rfl⟩,mul_zero]

theorem determinant_model_self_dual_rulings {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (E : V ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) (hnorm : ∀ x,B x x=2*(E x).det)
    (hV : Module.finrank K V=4) (L : Submodule K V) :
    L=B.orthogonal L ↔
      (∃ u : Fin 2 → K,u≠0 ∧ L.map E.toLinearMap=columnLineSpace u) ∨
        (∃ v : Fin 2 → K,v≠0 ∧ L.map E.toLinearMap=rowLineSpace v) := by
  rw [determinant_model_self_dual_iff htwo B hB hnd E hnorm hV L]
  constructor
  · rintro ⟨hdim,hdet⟩
    exact determinant_zero_plane_ruling_classification _ hdet hdim
  · rintro (⟨u,hu,heq⟩|⟨v,hv,heq⟩)
    · rw [heq]
      refine ⟨columnLineSpace_finrank u hu,?_⟩
      intro M hM
      obtain ⟨v,rfl⟩ := (mem_columnLineSpace_iff u hu M).mp hM
      exact rankOneTwo_det u v
    · rw [heq]
      refine ⟨rowLineSpace_finrank v hv,?_⟩
      intro M hM
      obtain ⟨u,rfl⟩ := (mem_rowLineSpace_iff v hv M).mp hM
      exact rankOneTwo_det u v

end CompletionTheory

namespace CompletionTheory
open Module Submodule

def orthogonalQuotientForm {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (G : Submodule K V) :
    LinearMap.BilinForm K ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype) := by
  let H := B.orthogonal G
  have hleft : G.comap H.subtype≤LinearMap.ker (B.restrict H) := by
    intro x hx
    ext y
    exact y.property x.val hx
  have hright : G.comap H.subtype≤LinearMap.ker (B.restrict H).flip := by
    intro x hx
    ext y
    change B y.val x.val=0
    rw [hB.eq y.val x.val]
    exact y.property x.val hx
  exact LinearMap.liftQ₂ _ _ (B.restrict H) hleft hright

theorem orthogonalQuotientForm_mk {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (G : Submodule K V)
    (x y : B.orthogonal G) :
    orthogonalQuotientForm B hB G (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)=B x.val y.val := rfl

theorem orthogonalQuotientForm_symm {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (G : Submodule K V) :
    (orthogonalQuotientForm B hB G).IsSymm := by
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with | _ x =>
  induction y using Submodule.Quotient.induction_on with | _ y =>
  exact hB.eq _ _

theorem orthogonalQuotientForm_nondegenerate {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (G : Submodule K V) :
    (orthogonalQuotientForm B hB G).Nondegenerate := by
  have horth := B.orthogonal_orthogonal hnd hB.isRefl G
  have left (x : (B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype)
      (hx : ∀ y,orthogonalQuotientForm B hB G x y=0) : x=0 := by
    induction x using Submodule.Quotient.induction_on with | _ x =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change x.val∈G
    have hm : x.val∈B.orthogonal (B.orthogonal G) := by
      intro y hy
      have hh := hx (Submodule.Quotient.mk (⟨y,hy⟩ : B.orthogonal G))
      change B x.val y=0 at hh
      rw [hB.eq y x.val]
      exact hh
    exact (SetLike.ext_iff.mp horth x.val).mp hm
  constructor
  · exact left
  · intro x hx
    apply left x
    intro y
    rw [(orthogonalQuotientForm_symm B hB G).eq x y]
    exact hx y

theorem orthogonal_quotient_finrank {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (G : Submodule K V) (hG : G≤B.orthogonal G) :
    finrank K ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype)+2*finrank K G=
      finrank K V := by
  have hh := (G.comap (B.orthogonal G).subtype).finrank_quotient_add_finrank
  have hm : (G.comap (B.orthogonal G).subtype).map (B.orthogonal G).subtype=G := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,hG hx⟩,hx,rfl⟩
  have hr := Submodule.finrank_map_subtype_eq (B.orthogonal G) (G.comap (B.orthogonal G).subtype)
  rw [hm] at hr
  rw [← hr] at hh
  have hdim := B.finrank_add_finrank_orthogonal' G
  rw [hnd.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hdim
  omega

def orthogonalQuotientCode {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (C G : Submodule K V) :
    Submodule K ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype) :=
  (C.comap (B.orthogonal G).subtype).map (G.comap (B.orthogonal G).subtype).mkQ

theorem orthogonalQuotientCode_mk_mem_iff {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (C G : Submodule K V) (hGC : G≤C) (x : B.orthogonal G) :
    Submodule.Quotient.mk x∈orthogonalQuotientCode B C G ↔ x.val∈C := by
  let H := B.orthogonal G
  let T := G.comap H.subtype
  have hTC : T≤C.comap H.subtype := fun y hy => hGC hy
  have heq : (orthogonalQuotientCode B C G).comap T.mkQ=C.comap H.subtype := by
    change ((C.comap H.subtype).map T.mkQ).comap T.mkQ=C.comap H.subtype
    rw [Submodule.comap_map_mkQ,sup_eq_right.mpr hTC]
  change x∈(orthogonalQuotientCode B C G).comap T.mkQ ↔ x∈C.comap H.subtype
  rw [heq]

theorem orthogonalQuotientCode_self_dual {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (C G : Submodule K V)
    (hC : C=B.orthogonal C) (hGC : G≤C) :
    orthogonalQuotientCode B C G=(orthogonalQuotientForm B hB G).orthogonal
      (orthogonalQuotientCode B C G) := by
  have hCH : C≤B.orthogonal G := by
    intro x hx y hy
    exact (hC ▸ hx) y (hGC hy)
  ext q
  induction q using Submodule.Quotient.induction_on with | _ x =>
  rw [orthogonalQuotientCode_mk_mem_iff B C G hGC x]
  constructor
  · intro hx q hq
    induction q using Submodule.Quotient.induction_on with | _ y =>
    have hy := (orthogonalQuotientCode_mk_mem_iff B C G hGC y).mp hq
    exact (hC ▸ hx) y.val hy
  · intro hx
    have hxorth : x.val∈B.orthogonal C := by
      intro y hy
      have hq := (orthogonalQuotientCode_mk_mem_iff B C G hGC (⟨y,hCH hy⟩ : B.orthogonal G)).mpr hy
      exact hx _ hq
    exact hC ▸ hxorth

theorem orthogonalQuotientCode_finrank {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (C G : Submodule K V)
    (hC : C=B.orthogonal C) (hGC : G≤C) :
    finrank K (orthogonalQuotientCode B C G)+finrank K G=finrank K C := by
  let H := B.orthogonal G
  let T := G.comap H.subtype
  let A := C.comap H.subtype
  have hTA : T≤A := fun x hx => hGC hx
  have hCH : C≤H := by
    intro x hx y hy
    exact (hC ▸ hx) y (hGC hy)
  have hh := submodule_quotient_image_finrank T A hTA
  have hT := Submodule.finrank_map_subtype_eq H T
  have hA := Submodule.finrank_map_subtype_eq H A
  rw [ambient_submodule_map_comap H G (le_trans hGC hCH)] at hT
  rw [ambient_submodule_map_comap H C hCH] at hA
  change finrank K (orthogonalQuotientCode B C G)+finrank K T=finrank K A at hh
  rw [← hT,← hA] at hh
  exact hh

theorem codimension_two_quotient_dimensions {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (C G : Submodule K V) (hC : C=B.orthogonal C)
    (hGC : G≤C) (hcodim : finrank K G+2=finrank K C) :
    finrank K ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype)=4 ∧
      finrank K (orthogonalQuotientCode B C G)=2 := by
  have hGG : G≤B.orthogonal G := by
    intro x hx y hy
    exact (hC ▸ hGC hx) y (hGC hy)
  have hqdim := orthogonal_quotient_finrank B hB hnd G hGG
  have hcdim := orthogonalQuotientCode_finrank B C G hC hGC
  have hdim := B.finrank_add_finrank_orthogonal' C
  rw [← hC,hnd.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hdim
  omega

end CompletionTheory

namespace CompletionTheory
open Module Submodule

theorem nondegenerate_bilinear_surjective_dual {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hnd : B.Nondegenerate) :
    Function.Surjective B := by
  have hi : Function.Injective B := LinearMap.ker_eq_bot.mp hnd.ker_eq_bot
  have hr : LinearMap.range B=⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hi,Subspace.dual_finrank_eq]
  exact LinearMap.range_eq_top.mp hr

theorem lagrangian_dual_vectors {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq ι] (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (L : Submodule K V) (b : Basis ι K L) :
    ∃ g : ι → V,∀ i j,B (b i) (g j)=if i=j then 1 else 0 := by
  classical
  have hs := nondegenerate_bilinear_surjective_dual B hnd
  have hg (i : ι) : ∃ v : V,B v=Subspace.dualLift L (b.coord i) := hs _
  choose g hg using hg
  refine ⟨g,?_⟩
  intro i j
  rw [hB.eq (b i) (g j),hg j,Subspace.dualLift_of_subtype]
  simp [Basis.coord_apply,Finsupp.single_apply,eq_comm]

theorem lagrangian_basis_isotropic {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (L : Submodule K V) (hL : L=B.orthogonal L)
    (b : Basis ι K L) (i j : ι) : B (b i) (b j)=0 :=
  ((SetLike.ext_iff.mp hL (b j : V)).mp (b j).property) (b i) (b i).property

noncomputable def correctedDualVector {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] (B : LinearMap.BilinForm K V) (L : Submodule K V) (b : Basis ι K L)
    (g : ι → V) (i : ι) : V :=
  g i-(2 : K)⁻¹ • ∑ j,B (g i) (g j) • (b j : V)

theorem correctedDualVector_basis_pair {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (B : LinearMap.BilinForm K V) (L : Submodule K V)
    (hL : L=B.orthogonal L) (b : Basis ι K L) (g : ι → V)
    (hpair : ∀ i j,B (b i) (g j)=if i=j then 1 else 0) (i j : ι) :
    B (b i) (correctedDualVector B L b g j)=if i=j then 1 else 0 := by
  classical
  have hz (k : ι) : B (b i) (b k)=0 := lagrangian_basis_isotropic B L hL b i k
  simp [correctedDualVector,map_sub,map_smul,map_sum,hz,hpair]

theorem correctedDualVector_reverse_pair {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (L : Submodule K V) (hL : L=B.orthogonal L) (b : Basis ι K L) (g : ι → V)
    (hpair : ∀ i j,B (b i) (g j)=if i=j then 1 else 0) (i j : ι) :
    B (correctedDualVector B L b g i) (b j)=if i=j then 1 else 0 := by
  rw [hB.eq,correctedDualVector_basis_pair B L hL b g hpair]
  simp only [eq_comm]

theorem correctedDualVector_old_pair {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (L : Submodule K V) (b : Basis ι K L) (g : ι → V)
    (hpair : ∀ i j,B (b i) (g j)=if i=j then 1 else 0) (i j : ι) :
    B (correctedDualVector B L b g i) (g j)=(2 : K)⁻¹*B (g i) (g j) := by
  classical
  simp only [correctedDualVector,map_sub,map_smul,map_sum,
    LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.sum_apply,smul_eq_mul,hpair]
  try simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  field_simp [htwo]
  <;> ring

theorem correctedDualVector_isotropic {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (L : Submodule K V) (hL : L=B.orthogonal L) (b : Basis ι K L) (g : ι → V)
    (hpair : ∀ i j,B (b i) (g j)=if i=j then 1 else 0) (i j : ι) :
    B (correctedDualVector B L b g i) (correctedDualVector B L b g j)=0 := by
  classical
  change B (correctedDualVector B L b g i)
    (g j-(2 : K)⁻¹ • ∑ k,B (g j) (g k) • (b k : V))=0
  simp only [map_sub,map_smul,map_sum,smul_eq_mul]
  rw [correctedDualVector_old_pair htwo B L b g hpair]
  simp_rw [correctedDualVector_reverse_pair B hB L hL b g hpair i]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [hB.eq (g j) (g i)]
  ring

theorem lagrangian_hyperbolic_dual_exists {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι] [DecidableEq ι] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (L : Submodule K V) (hL : L=B.orthogonal L) (b : Basis ι K L) :
    ∃ f : ι → V,(∀ i j,B (b i) (b j)=0) ∧
      (∀ i j,B (b i) (f j)=if i=j then 1 else 0) ∧
      (∀ i j,B (f i) (b j)=if i=j then 1 else 0) ∧
      ∀ i j,B (f i) (f j)=0 := by
  obtain ⟨g,hg⟩ := lagrangian_dual_vectors B hB hnd L b
  refine ⟨correctedDualVector B L b g,lagrangian_basis_isotropic B L hL b,
    correctedDualVector_basis_pair B L hL b g hg,
    correctedDualVector_reverse_pair B hB L hL b g hg,
    correctedDualVector_isotropic htwo B hB L hL b g hg⟩

noncomputable def hyperbolicCoordinateMap {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] (L : Submodule K V) (b : Basis ι K L) (f : ι → V) :
    ((ι → K)×(ι → K)) →ₗ[K] V where
  toFun x := (∑ i,x.1 i • (b i : V))+(∑ i,x.2 i • f i)
  map_add' x y := by
    simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,add_smul,Finset.sum_add_distrib]
    abel
  map_smul' a x := by
    simp only [Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,smul_eq_mul,
      smul_add,Finset.smul_sum,smul_smul,RingHom.id_apply]

theorem hyperbolicCoordinateMap_basis_pair {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (B : LinearMap.BilinForm K V) (L : Submodule K V)
    (b : Basis ι K L) (f : ι → V) (hee : ∀ i j,B (b i) (b j)=0)
    (hef : ∀ i j,B (b i) (f j)=if i=j then 1 else 0)
    (x : (ι → K)×(ι → K)) (j : ι) :
    B (b j) (hyperbolicCoordinateMap L b f x)=x.2 j := by
  classical
  simp [hyperbolicCoordinateMap,map_add,map_sum,map_smul,smul_eq_mul,hee,hef,mul_ite]

theorem hyperbolicCoordinateMap_dual_pair {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (B : LinearMap.BilinForm K V) (L : Submodule K V)
    (b : Basis ι K L) (f : ι → V) (hfe : ∀ i j,B (f i) (b j)=if i=j then 1 else 0)
    (hff : ∀ i j,B (f i) (f j)=0) (x : (ι → K)×(ι → K)) (j : ι) :
    B (f j) (hyperbolicCoordinateMap L b f x)=x.1 j := by
  classical
  simp [hyperbolicCoordinateMap,map_add,map_sum,map_smul,smul_eq_mul,hfe,hff,mul_ite]

theorem hyperbolicCoordinateMap_injective {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (B : LinearMap.BilinForm K V) (L : Submodule K V)
    (b : Basis ι K L) (f : ι → V) (hee : ∀ i j,B (b i) (b j)=0)
    (hef : ∀ i j,B (b i) (f j)=if i=j then 1 else 0)
    (hfe : ∀ i j,B (f i) (b j)=if i=j then 1 else 0)
    (hff : ∀ i j,B (f i) (f j)=0) : Function.Injective (hyperbolicCoordinateMap L b f) := by
  intro x y hxy
  apply Prod.ext
  · funext j
    have hh := congrArg (fun z => B (f j) z) hxy
    simpa only [hyperbolicCoordinateMap_dual_pair B L b f hfe hff] using hh
  · funext j
    have hh := congrArg (fun z => B (b j) z) hxy
    simpa only [hyperbolicCoordinateMap_basis_pair B L b f hee hef] using hh

theorem hyperbolicCoordinateMap_bijective {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K V) (hnd : B.Nondegenerate)
    (L : Submodule K V) (hL : L=B.orthogonal L) (b : Basis ι K L) (f : ι → V)
    (hee : ∀ i j,B (b i) (b j)=0)
    (hef : ∀ i j,B (b i) (f j)=if i=j then 1 else 0)
    (hfe : ∀ i j,B (f i) (b j)=if i=j then 1 else 0)
    (hff : ∀ i j,B (f i) (f j)=0) : Function.Bijective (hyperbolicCoordinateMap L b f) := by
  have hi := hyperbolicCoordinateMap_injective B L b f hee hef hfe hff
  have hdim : finrank K L+finrank K L=finrank K V := by
    have hh := B.finrank_add_finrank_orthogonal' L
    rw [← hL,hnd.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hh
    exact hh
  have hcard := Module.finrank_eq_card_basis b
  have hdom : finrank K ((ι → K)×(ι → K))=finrank K V := by
    simp only [Module.finrank_prod,Module.finrank_pi_fintype,Module.finrank_self,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Nat.cast_id]
    try simp only [Nat.card_eq_fintype_card,Nat.cast_id] at hcard
    omega
  have hr : LinearMap.range (hyperbolicCoordinateMap L b f)=⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hi,hdom]
  exact ⟨hi,LinearMap.range_eq_top.mp hr⟩

theorem hyperbolicCoordinateMap_pair_formula {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (L : Submodule K V) (b : Basis ι K L) (f : ι → V)
    (hee : ∀ i j,B (b i) (b j)=0)
    (hef : ∀ i j,B (b i) (f j)=if i=j then 1 else 0)
    (hfe : ∀ i j,B (f i) (b j)=if i=j then 1 else 0)
    (hff : ∀ i j,B (f i) (f j)=0) (x y : (ι → K)×(ι → K)) :
    B (hyperbolicCoordinateMap L b f x) (hyperbolicCoordinateMap L b f y)=
      ∑ i,(x.1 i*y.2 i+x.2 i*y.1 i) := by
  classical
  have he (i) : B (hyperbolicCoordinateMap L b f x) (b i)=x.2 i := by
    rw [hB.eq,hyperbolicCoordinateMap_basis_pair B L b f hee hef]
  have hf (i) : B (hyperbolicCoordinateMap L b f x) (f i)=x.1 i := by
    rw [hB.eq,hyperbolicCoordinateMap_dual_pair B L b f hfe hff]
  change B (hyperbolicCoordinateMap L b f x)
    ((∑ i,y.1 i • (b i : V))+(∑ i,y.2 i • f i))=_
  simp only [map_add,map_sum,map_smul,smul_eq_mul,he,hf]
  rw [Finset.sum_add_distrib]
  simp only [mul_comm,add_comm]

theorem hyperbolicCoordinateMap_mem_lagrangian {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (B : LinearMap.BilinForm K V)
    (L : Submodule K V) (hL : L=B.orthogonal L) (b : Basis ι K L) (f : ι → V)
    (hee : ∀ i j,B (b i) (b j)=0)
    (hef : ∀ i j,B (b i) (f j)=if i=j then 1 else 0)
    (x : (ι → K)×(ι → K)) : hyperbolicCoordinateMap L b f x∈L ↔ x.2=0 := by
  constructor
  · intro hx
    funext j
    have hz := ((SetLike.ext_iff.mp hL (hyperbolicCoordinateMap L b f x)).mp hx) (b j) (b j).property
    rw [hyperbolicCoordinateMap_basis_pair B L b f hee hef] at hz
    exact hz
  · intro hx
    change ((∑ i,x.1 i • (b i : V))+(∑ i,x.2 i • f i))∈L
    rw [hx]
    simp only [Pi.zero_apply,zero_smul,Finset.sum_const_zero,add_zero]
    exact L.sum_mem (fun i _ => L.smul_mem _ (b i).property)

theorem lagrangian_hyperbolic_coordinates {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι] [DecidableEq ι] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (L : Submodule K V) (hL : L=B.orthogonal L) (b : Basis ι K L) :
    ∃ e : ((ι → K)×(ι → K)) ≃ₗ[K] V,
      (∀ x y,B (e x) (e y)=∑ i,(x.1 i*y.2 i+x.2 i*y.1 i)) ∧
      ∀ x,e x∈L ↔ x.2=0 := by
  obtain ⟨f,hee,hef,hfe,hff⟩ := lagrangian_hyperbolic_dual_exists htwo B hB hnd L hL b
  let e := LinearEquiv.ofBijective (hyperbolicCoordinateMap L b f)
    (hyperbolicCoordinateMap_bijective B hnd L hL b f hee hef hfe hff)
  exact ⟨e,hyperbolicCoordinateMap_pair_formula B hB L b f hee hef hfe hff,
    hyperbolicCoordinateMap_mem_lagrangian B L hL b f hee hef⟩

def splitCoordinatesMatrixEquiv {K : Type*} [Field K] :
    ((Fin 2 → K)×(Fin 2 → K)) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun x := !![x.1 0,x.1 1;-x.2 1,x.2 0]
  invFun M := (![M 0 0,M 0 1],![M 1 1,-M 1 0])
  left_inv x := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [neg_add,add_comm]
  map_smul' a x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [smul_eq_mul]

theorem splitCoordinatesMatrix_norm {K : Type*} [Field K]
    (x : (Fin 2 → K)×(Fin 2 → K)) :
    (∑ i : Fin 2,(x.1 i*x.2 i+x.2 i*x.1 i))=2*(splitCoordinatesMatrixEquiv x).det := by
  simp [splitCoordinatesMatrixEquiv,Matrix.det_fin_two,Fin.sum_univ_two]
  ring

theorem split_four_dimensional_determinant_model {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (L : Submodule K V) (hL : L=B.orthogonal L) (hdim : finrank K L=2) :
    ∃ E : V ≃ₗ[K] Matrix (Fin 2) (Fin 2) K,
      (∀ v,B v v=2*(E v).det) ∧
      ∀ v,v∈L ↔ (E v) 1 0=0 ∧ (E v) 1 1=0 := by
  classical
  let b : Basis (Fin 2) K L := (Module.finBasis K L).reindex (finCongr hdim)
  obtain ⟨e,he,hLcoord⟩ := lagrangian_hyperbolic_coordinates htwo B hB hnd L hL b
  let E := e.symm.trans splitCoordinatesMatrixEquiv
  refine ⟨E,?_,?_⟩
  · intro v
    obtain ⟨x,rfl⟩ := e.surjective v
    change B (e x) (e x)=2*(splitCoordinatesMatrixEquiv (e.symm (e x))).det
    rw [e.symm_apply_apply,he,splitCoordinatesMatrix_norm]
  · intro v
    obtain ⟨x,rfl⟩ := e.surjective v
    change e x∈L ↔ (splitCoordinatesMatrixEquiv (e.symm (e x))) 1 0=0 ∧
      (splitCoordinatesMatrixEquiv (e.symm (e x))) 1 1=0
    rw [e.symm_apply_apply,hLcoord]
    change x.2=0 ↔ -x.2 1=0 ∧ x.2 0=0
    constructor
    · intro hx
      simp [hx]
    · rintro ⟨hx1,hx0⟩
      funext i
      fin_cases i
      · exact hx0
      · exact neg_eq_zero.mp hx1

theorem code_quotient_determinant_model {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C G : Submodule K V) (hC : C=B.orthogonal C) (hGC : G≤C)
    (hcodim : Module.finrank K G+2=Module.finrank K C) :
    ∃ E : ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K,
      (∀ v,orthogonalQuotientForm B hB G v v=2*(E v).det) ∧
      ∀ v,v∈orthogonalQuotientCode B C G ↔ (E v) 1 0=0 ∧ (E v) 1 1=0 := by
  exact split_four_dimensional_determinant_model htwo (orthogonalQuotientForm B hB G)
    (orthogonalQuotientForm_symm B hB G) (orthogonalQuotientForm_nondegenerate B hB hnd G)
      (orthogonalQuotientCode B C G) (orthogonalQuotientCode_self_dual B hB C G hC hGC)
        (codimension_two_quotient_dimensions B hB hnd C G hC hGC hcodim).2

def liftOrthogonalQuotientCode {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (G : Submodule K V)
    (D : Submodule K ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype)) : Submodule K V :=
  (D.comap (G.comap (B.orthogonal G).subtype).mkQ).map (B.orthogonal G).subtype

theorem liftOrthogonalQuotientCode_le_orthogonal {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (G : Submodule K V)
    (D : Submodule K ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype)) :
    liftOrthogonalQuotientCode B G D≤B.orthogonal G := by
  rintro x ⟨y,hy,rfl⟩
  exact y.property

theorem liftOrthogonalQuotientCode_contains {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (G : Submodule K V) (hG : G≤B.orthogonal G)
    (D : Submodule K ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype)) :
    G≤liftOrthogonalQuotientCode B G D := by
  intro x hx
  refine ⟨⟨x,hG hx⟩,?_,rfl⟩
  change Submodule.Quotient.mk (⟨x,hG hx⟩ : B.orthogonal G)∈D
  have hz : Submodule.Quotient.mk (⟨x,hG hx⟩ : B.orthogonal G)=
      (0 : (B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype) :=
    (Submodule.Quotient.mk_eq_zero _).mpr hx
  rw [hz]
  exact D.zero_mem

theorem liftOrthogonalQuotientCode_mem_iff {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (G : Submodule K V)
    (D : Submodule K ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype))
    (x : B.orthogonal G) :
    x.val∈liftOrthogonalQuotientCode B G D ↔ Submodule.Quotient.mk x∈D := by
  constructor
  · rintro ⟨y,hy,heq⟩
    have hh : y=x := Subtype.ext heq
    exact hh ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem lift_orthogonal_quotient_code {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (G D : Submodule K V) (hGD : G≤D) (hDH : D≤B.orthogonal G) :
    liftOrthogonalQuotientCode B G (orthogonalQuotientCode B D G)=D := by
  ext x
  constructor
  · intro hx
    have hxH := liftOrthogonalQuotientCode_le_orthogonal B G _ hx
    have hq := (liftOrthogonalQuotientCode_mem_iff B G _ (⟨x,hxH⟩ : B.orthogonal G)).mp hx
    exact (orthogonalQuotientCode_mk_mem_iff B D G hGD _).mp hq
  · intro hx
    apply (liftOrthogonalQuotientCode_mem_iff B G _ (⟨x,hDH hx⟩ : B.orthogonal G)).mpr
    exact (orthogonalQuotientCode_mk_mem_iff B D G hGD _).mpr hx

theorem orthogonal_quotient_lift_code {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (G : Submodule K V)
    (D : Submodule K ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype)) :
    orthogonalQuotientCode B (liftOrthogonalQuotientCode B G D) G=D := by
  let H := B.orthogonal G
  let T := G.comap H.subtype
  have heq : (liftOrthogonalQuotientCode B G D).comap H.subtype=D.comap T.mkQ := by
    ext x
    exact liftOrthogonalQuotientCode_mem_iff B G D x
  change ((liftOrthogonalQuotientCode B G D).comap H.subtype).map T.mkQ=D
  rw [heq]
  exact Submodule.map_comap_eq_self (by simp)

theorem quotient_code_self_dual_iff {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (G D : Submodule K V)
    (hGD : G≤D) (hDH : D≤B.orthogonal G) :
    orthogonalQuotientCode B D G=(orthogonalQuotientForm B hB G).orthogonal
      (orthogonalQuotientCode B D G) ↔ D=B.orthogonal D := by
  constructor
  · intro hq
    ext x
    constructor
    · intro hx y hy
      let xx : B.orthogonal G := ⟨x,hDH hx⟩
      let yy : B.orthogonal G := ⟨y,hDH hy⟩
      have hxq := (orthogonalQuotientCode_mk_mem_iff B D G hGD xx).mpr hx
      have hyq := (orthogonalQuotientCode_mk_mem_iff B D G hGD yy).mpr hy
      have hxorth := (SetLike.ext_iff.mp hq (Submodule.Quotient.mk xx)).mp hxq
      exact hxorth _ hyq
    · intro hx
      have hxH : x∈B.orthogonal G := fun y hy => hx y (hGD hy)
      let xx : B.orthogonal G := ⟨x,hxH⟩
      have hxq : Submodule.Quotient.mk xx∈(orthogonalQuotientForm B hB G).orthogonal
          (orthogonalQuotientCode B D G) := by
        intro q hqq
        induction q using Submodule.Quotient.induction_on with | _ y =>
        have hy := (orthogonalQuotientCode_mk_mem_iff B D G hGD y).mp hqq
        exact hx y.val hy
      have hxmem := (SetLike.ext_iff.mp hq (Submodule.Quotient.mk xx)).mpr hxq
      exact (orthogonalQuotientCode_mk_mem_iff B D G hGD xx).mp hxmem
  · intro hD
    exact orthogonalQuotientCode_self_dual B hB D G hD hGD

theorem actual_code_quotient_ruling_classification {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (C G : Submodule K V) (hC : C=B.orthogonal C) (hGC : G≤C)
    (hcodim : Module.finrank K G+2=Module.finrank K C) :
    ∃ E : ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K,
      (∀ v,orthogonalQuotientForm B hB G v v=2*(E v).det) ∧
      ∀ D : Submodule K V,G≤D →
        (D=B.orthogonal D ↔ D≤B.orthogonal G ∧
          ((∃ u : Fin 2 → K,u≠0 ∧ (orthogonalQuotientCode B D G).map E.toLinearMap=columnLineSpace u) ∨
            (∃ v : Fin 2 → K,v≠0 ∧ (orthogonalQuotientCode B D G).map E.toLinearMap=rowLineSpace v))) := by
  obtain ⟨E,hnorm,hbase⟩ := code_quotient_determinant_model htwo B hB hnd C G hC hGC hcodim
  have hqdim := (codimension_two_quotient_dimensions B hB hnd C G hC hGC hcodim).1
  have hqsym := orthogonalQuotientForm_symm B hB G
  have hqnd := orthogonalQuotientForm_nondegenerate B hB hnd G
  refine ⟨E,hnorm,?_⟩
  intro D hGD
  have hclass := determinant_model_self_dual_rulings htwo (orthogonalQuotientForm B hB G)
    hqsym hqnd E hnorm hqdim (orthogonalQuotientCode B D G)
  constructor
  · intro hD
    have hDH : D≤B.orthogonal G := by
      intro x hx y hy
      exact ((SetLike.ext_iff.mp hD x).mp hx) y (hGD hy)
    exact ⟨hDH,hclass.mp (orthogonalQuotientCode_self_dual B hB D G hD hGD)⟩
  · rintro ⟨hDH,hruling⟩
    exact (quotient_code_self_dual_iff B hB G D hGD hDH).mp (hclass.mpr hruling)

theorem column_ruling_projective_injective {K : Type*} [Field K] :
    Function.Injective (fun u : Projectivization K (Fin 2 → K) => columnLineSpace u.rep) := by
  intro u s hus
  let z : Fin 2 → K := ![1,0]
  have hz : z≠0 := by intro h;have hh := congrFun h 0;exact one_ne_zero hh
  have huM : rankOneTwo u.rep z∈columnLineSpace u.rep :=
    (mem_columnLineSpace_iff u.rep u.rep_nonzero _).mpr ⟨z,rfl⟩
  have hsM : rankOneTwo u.rep z∈columnLineSpace s.rep :=
    (SetLike.ext_iff.mp hus _).mp huM
  obtain ⟨v,hv⟩ := (mem_columnLineSpace_iff s.rep s.rep_nonzero _).mp hsM
  obtain ⟨⟨a,ha,hrep⟩,_⟩ := rankOneTwo_factor_lines _ _ _ _ u.rep_nonzero hz hv
  have hh := (Projectivization.mk_eq_mk_iff' K u.rep s.rep u.rep_nonzero s.rep_nonzero).mpr
    ⟨a,hrep.symm⟩
  simpa only [Projectivization.mk_rep] using hh

theorem row_ruling_projective_injective {K : Type*} [Field K] :
    Function.Injective (fun v : Projectivization K (Fin 2 → K) => rowLineSpace v.rep) := by
  intro v t hvt
  let z : Fin 2 → K := ![1,0]
  have hz : z≠0 := by intro h;have hh := congrFun h 0;exact one_ne_zero hh
  have hvM : rankOneTwo z v.rep∈rowLineSpace v.rep :=
    (mem_rowLineSpace_iff v.rep v.rep_nonzero _).mpr ⟨z,rfl⟩
  have htM : rankOneTwo z v.rep∈rowLineSpace t.rep :=
    (SetLike.ext_iff.mp hvt _).mp hvM
  obtain ⟨u,hu⟩ := (mem_rowLineSpace_iff t.rep t.rep_nonzero _).mp htM
  obtain ⟨_,⟨a,ha,hrep⟩⟩ := rankOneTwo_factor_lines _ _ _ _ hz v.rep_nonzero hu
  have hh := (Projectivization.mk_eq_mk_iff' K v.rep t.rep v.rep_nonzero t.rep_nonzero).mpr
    ⟨a,hrep.symm⟩
  simpa only [Projectivization.mk_rep] using hh

theorem column_ruling_ne_row_ruling {K : Type*} [Field K]
    (u v : Projectivization K (Fin 2 → K)) : columnLineSpace u.rep≠rowLineSpace v.rep := by
  intro heq
  obtain ⟨i,hi⟩ : ∃ i,u.rep i≠0 := by
    by_contra hn
    apply u.rep_nonzero
    ext j
    by_contra hj
    exact hn ⟨j,hj⟩
  have hrow (t : Fin 2 → K) : rankOneTwo u.rep t∈rowLineSpace v.rep :=
    (SetLike.ext_iff.mp heq _).mp ((mem_columnLineSpace_iff u.rep u.rep_nonzero _).mpr ⟨t,rfl⟩)
  have hz0 := (Submodule.mem_iInf _).mp (hrow ![1,0]) i
  have hz1 := (Submodule.mem_iInf _).mp (hrow ![0,1]) i
  change v.rep 0*(u.rep i*0)-v.rep 1*(u.rep i*1)=0 at hz0
  change v.rep 0*(u.rep i*1)-v.rep 1*(u.rep i*0)=0 at hz1
  simp only [mul_zero,mul_one,zero_sub,neg_eq_zero] at hz0
  simp only [mul_zero,mul_one,sub_zero] at hz1
  have hv1 : v.rep 1=0 := (mul_eq_zero.mp hz0).resolve_right hi
  have hv0 : v.rep 0=0 := (mul_eq_zero.mp hz1).resolve_right hi
  apply v.rep_nonzero
  ext j
  fin_cases j <;> assumption

theorem columnLineSpace_smul {K : Type*} [Field K] (a : K) (ha : a≠0) (u : Fin 2 → K) :
    columnLineSpace (a • u)=columnLineSpace u := by
  ext M
  have hscale (j) : columnDetFunctional (a • u) j M=a*columnDetFunctional u j M := by
    change (a*u 0)*M 1 j-(a*u 1)*M 0 j=a*(u 0*M 1 j-u 1*M 0 j)
    ring
  simp only [columnLineSpace,Submodule.mem_iInf,LinearMap.mem_ker,hscale,mul_eq_zero,ha,false_or]

theorem rowLineSpace_smul {K : Type*} [Field K] (a : K) (ha : a≠0) (v : Fin 2 → K) :
    rowLineSpace (a • v)=rowLineSpace v := by
  ext M
  have hscale (i) : rowDetFunctional (a • v) i M=a*rowDetFunctional v i M := by
    change (a*v 0)*M i 1-(a*v 1)*M i 0=a*(v 0*M i 1-v 1*M i 0)
    ring
  simp only [rowLineSpace,Submodule.mem_iInf,LinearMap.mem_ker,hscale,mul_eq_zero,ha,false_or]

theorem columnLineSpace_projective_rep {K : Type*} [Field K] (u : Fin 2 → K) (hu : u≠0) :
    columnLineSpace (Projectivization.mk K u hu).rep=columnLineSpace u := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K u hu
  rw [← ha,Units.smul_def,columnLineSpace_smul _ (Units.ne_zero a)]

theorem rowLineSpace_projective_rep {K : Type*} [Field K] (v : Fin 2 → K) (hv : v≠0) :
    rowLineSpace (Projectivization.mk K v hv).rep=rowLineSpace v := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  rw [← ha,Units.smul_def,rowLineSpace_smul _ (Units.ne_zero a)]

noncomputable def matrixRulingSpace {K : Type*} [Field K]
    (a : Projectivization K (Fin 2 → K) ⊕ Projectivization K (Fin 2 → K)) :
    Submodule K (Matrix (Fin 2) (Fin 2) K) :=
  Sum.elim (fun u => columnLineSpace u.rep) (fun v => rowLineSpace v.rep) a

theorem matrixRulingSpace_injective {K : Type*} [Field K] :
    Function.Injective (matrixRulingSpace (K := K)) := by
  rintro (u|v) (s|t) h
  · exact congrArg Sum.inl (column_ruling_projective_injective h)
  · exact (column_ruling_ne_row_ruling u t h).elim
  · exact (column_ruling_ne_row_ruling s v h.symm).elim
  · exact congrArg Sum.inr (row_ruling_projective_injective h)

theorem matrixRulingSpace_finrank {K : Type*} [Field K]
    (a : Projectivization K (Fin 2 → K) ⊕ Projectivization K (Fin 2 → K)) :
    Module.finrank K (matrixRulingSpace a)=2 := by
  rcases a with u|v
  · exact columnLineSpace_finrank u.rep u.rep_nonzero
  · exact rowLineSpace_finrank v.rep v.rep_nonzero

theorem matrixRulingSpace_det {K : Type*} [Field K]
    (a : Projectivization K (Fin 2 → K) ⊕ Projectivization K (Fin 2 → K)) :
    ∀ M∈matrixRulingSpace a,M.det=0 := by
  intro M hM
  rcases a with u|v
  · obtain ⟨v,rfl⟩ := (mem_columnLineSpace_iff u.rep u.rep_nonzero M).mp hM
    exact rankOneTwo_det _ _
  · obtain ⟨u,rfl⟩ := (mem_rowLineSpace_iff v.rep v.rep_nonzero M).mp hM
    exact rankOneTwo_det _ _

theorem matrixRulingSpace_exhaustive {K : Type*} [Field K]
    (W : Submodule K (Matrix (Fin 2) (Fin 2) K))
    (hdim : Module.finrank K W=2) (hdet : ∀ M∈W,M.det=0) :
    ∃ a : Projectivization K (Fin 2 → K) ⊕ Projectivization K (Fin 2 → K),W=matrixRulingSpace a := by
  rcases determinant_zero_plane_ruling_classification W hdet hdim with ⟨u,hu,hW⟩|⟨v,hv,hW⟩
  · exact ⟨Sum.inl (Projectivization.mk K u hu),hW.trans (columnLineSpace_projective_rep u hu).symm⟩
  · exact ⟨Sum.inr (Projectivization.mk K v hv),hW.trans (rowLineSpace_projective_rep v hv).symm⟩

noncomputable def quotientRulingCode {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (G : Submodule K V)
    (E : ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (a : Projectivization K (Fin 2 → K) ⊕ Projectivization K (Fin 2 → K)) : Submodule K V :=
  liftOrthogonalQuotientCode B G ((matrixRulingSpace a).comap E.toLinearMap)

theorem quotientRulingCode_projected {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (G : Submodule K V)
    (E : ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (a : Projectivization K (Fin 2 → K) ⊕ Projectivization K (Fin 2 → K)) :
    (orthogonalQuotientCode B (quotientRulingCode B G E a) G).map E.toLinearMap=matrixRulingSpace a := by
  rw [quotientRulingCode,orthogonal_quotient_lift_code]
  apply Submodule.map_comap_eq_self
  rw [LinearMap.range_eq_top.mpr E.surjective]
  exact le_top

theorem quotientRulingCode_self_dual {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (G : Submodule K V) (hG : G≤B.orthogonal G)
    (E : ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hnorm : ∀ x,orthogonalQuotientForm B hB G x x=2*(E x).det)
    (hqdim : Module.finrank K ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype)=4)
    (a : Projectivization K (Fin 2 → K) ⊕ Projectivization K (Fin 2 → K)) :
    quotientRulingCode B G E a=B.orthogonal (quotientRulingCode B G E a) ∧ G≤quotientRulingCode B G E a := by
  have hGD := liftOrthogonalQuotientCode_contains B G hG ((matrixRulingSpace a).comap E.toLinearMap)
  have hDH := liftOrthogonalQuotientCode_le_orthogonal B G ((matrixRulingSpace a).comap E.toLinearMap)
  have hqself := (determinant_model_self_dual_iff htwo (orthogonalQuotientForm B hB G)
    (orthogonalQuotientForm_symm B hB G) (orthogonalQuotientForm_nondegenerate B hB hnd G)
      E hnorm hqdim (orthogonalQuotientCode B (quotientRulingCode B G E a) G)).mpr (by
        rw [quotientRulingCode_projected]
        exact ⟨matrixRulingSpace_finrank a,matrixRulingSpace_det a⟩)
  exact ⟨(quotient_code_self_dual_iff B hB G _ hGD hDH).mp hqself,hGD⟩

theorem quotientRulingCode_injective {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (G : Submodule K V)
    (E : ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :
    Function.Injective (quotientRulingCode B G E) := by
  intro a b hab
  apply matrixRulingSpace_injective
  rw [← quotientRulingCode_projected B G E a,← quotientRulingCode_projected B G E b,hab]

theorem quotientRulingCode_bijection {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (htwo : (2 : K)≠0)
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (G : Submodule K V) (hG : G≤B.orthogonal G)
    (E : ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hnorm : ∀ x,orthogonalQuotientForm B hB G x x=2*(E x).det)
    (hqdim : Module.finrank K ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype)=4) :
    ∃ e : (Projectivization K (Fin 2 → K) ⊕ Projectivization K (Fin 2 → K)) ≃
      {D : Submodule K V // D=B.orthogonal D ∧ G≤D},
      ∀ a,(e a).val=quotientRulingCode B G E a := by
  let f := fun a => (⟨quotientRulingCode B G E a,
    quotientRulingCode_self_dual htwo B hB hnd G hG E hnorm hqdim a⟩ :
      {D : Submodule K V // D=B.orthogonal D ∧ G≤D})
  have hfb : Function.Bijective f := by
    constructor
    · intro a b hab
      exact quotientRulingCode_injective B G E (congrArg Subtype.val hab)
    · intro D
      have hDH : D.val≤B.orthogonal G := by
        intro x hx y hy
        exact ((SetLike.ext_iff.mp D.property.1 x).mp hx) y (D.property.2 hy)
      have hq := orthogonalQuotientCode_self_dual B hB D.val G D.property.1 D.property.2
      have hshape := (determinant_model_self_dual_iff htwo (orthogonalQuotientForm B hB G)
        (orthogonalQuotientForm_symm B hB G) (orthogonalQuotientForm_nondegenerate B hB hnd G)
          E hnorm hqdim (orthogonalQuotientCode B D.val G)).mp hq
      obtain ⟨a,ha⟩ := matrixRulingSpace_exhaustive _ hshape.1 hshape.2
      have hqeq : orthogonalQuotientCode B D.val G=(matrixRulingSpace a).comap E.toLinearMap := by
        apply Submodule.map_injective_of_injective E.injective
        rw [ha]
        apply Eq.symm
        apply Submodule.map_comap_eq_self
        rw [LinearMap.range_eq_top.mpr E.surjective]
        exact le_top
      have hcode : quotientRulingCode B G E a=D.val := by
        rw [quotientRulingCode,← hqeq]
        exact lift_orthogonal_quotient_code B G D.val D.property.2 hDH
      exact ⟨a,Subtype.ext hcode⟩
  exact ⟨Equiv.ofBijective f hfb,fun _ => rfl⟩

theorem rankOneTwo_mem_column_iff_projective {K : Type*} [Field K]
    (u v s : Fin 2 → K) (hu : u≠0) (hv : v≠0) (hs : s≠0) :
    rankOneTwo u v∈columnLineSpace s ↔ Projectivization.mk K u hu=Projectivization.mk K s hs := by
  constructor
  · intro hM
    obtain ⟨w,hw⟩ := (mem_columnLineSpace_iff s hs _).mp hM
    obtain ⟨⟨a,ha,hrep⟩,_⟩ := rankOneTwo_factor_lines _ _ _ _ hu hv hw
    exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨a,hrep.symm⟩
  · intro h
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
    apply (mem_columnLineSpace_iff s hs _).mpr
    refine ⟨a • v,?_⟩
    rw [← ha]
    ext i j
    simp only [rankOneTwo,Pi.smul_apply,smul_eq_mul]
    ring

theorem rankOneTwo_mem_row_iff_projective {K : Type*} [Field K]
    (u v t : Fin 2 → K) (hu : u≠0) (hv : v≠0) (ht : t≠0) :
    rankOneTwo u v∈rowLineSpace t ↔ Projectivization.mk K v hv=Projectivization.mk K t ht := by
  constructor
  · intro hM
    obtain ⟨s,hs⟩ := (mem_rowLineSpace_iff t ht _).mp hM
    obtain ⟨_,⟨a,ha,hrep⟩⟩ := rankOneTwo_factor_lines _ _ _ _ hu hv hs
    exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨a,hrep.symm⟩
  · intro h
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
    apply (mem_rowLineSpace_iff t ht _).mpr
    refine ⟨a • u,?_⟩
    rw [← ha]
    ext i j
    simp only [rankOneTwo,Pi.smul_apply,smul_eq_mul]
    ring

theorem gridQuadricPoint_column_membership {K : Type*} [Field K]
    (p : Projectivization K (Fin 2 → K) × Projectivization K (Fin 2 → K))
    (a : Projectivization K (Fin 2 → K)) :
    (gridQuadricPoint p).val.rep∈columnLineSpace a.rep ↔ p.1=a := by
  let M := rankOneTwo p.1.rep p.2.rep
  have hM : M≠0 := rankOneTwo_ne_zero _ _ p.1.rep_nonzero p.2.rep_nonzero
  change (Projectivization.mk K M hM).rep∈columnLineSpace a.rep ↔ p.1=a
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep K M hM
  rw [← hc,Units.smul_def,(columnLineSpace a.rep).smul_mem_iff (Units.ne_zero c)]
  exact (rankOneTwo_mem_column_iff_projective _ _ _ p.1.rep_nonzero p.2.rep_nonzero a.rep_nonzero).trans
    (by simp only [Projectivization.mk_rep])

theorem gridQuadricPoint_row_membership {K : Type*} [Field K]
    (p : Projectivization K (Fin 2 → K) × Projectivization K (Fin 2 → K))
    (a : Projectivization K (Fin 2 → K)) :
    (gridQuadricPoint p).val.rep∈rowLineSpace a.rep ↔ p.2=a := by
  let M := rankOneTwo p.1.rep p.2.rep
  have hM : M≠0 := rankOneTwo_ne_zero _ _ p.1.rep_nonzero p.2.rep_nonzero
  change (Projectivization.mk K M hM).rep∈rowLineSpace a.rep ↔ p.2=a
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep K M hM
  rw [← hc,Units.smul_def,(rowLineSpace a.rep).smul_mem_iff (Units.ne_zero c)]
  exact (rankOneTwo_mem_row_iff_projective _ _ _ p.1.rep_nonzero p.2.rep_nonzero a.rep_nonzero).trans
    (by simp only [Projectivization.mk_rep])

def matrixQuadricPoint {K : Type*} [Field K] (M : Matrix (Fin 2) (Fin 2) K) (hM : M≠0) (hdet : M.det=0) :
    rankOneQuadricPoints K := by
  refine ⟨Projectivization.mk K M hM,?_⟩
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K M hM
  rw [← ha,Units.smul_def,Matrix.det_smul,hdet,mul_zero]

noncomputable def matrixGridPoint {K : Type*} [Field K] (M : Matrix (Fin 2) (Fin 2) K)
    (hM : M≠0) (hdet : M.det=0) :
    Projectivization K (Fin 2 → K) × Projectivization K (Fin 2 → K) :=
  (Equiv.ofBijective gridQuadricPoint gridQuadricPoint_bijective).symm (matrixQuadricPoint M hM hdet)

theorem matrixGridPoint_column_membership {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (hM : M≠0) (hdet : M.det=0)
    (a : Projectivization K (Fin 2 → K)) :
    M∈columnLineSpace a.rep ↔ (matrixGridPoint M hM hdet).1=a := by
  have hp : gridQuadricPoint (matrixGridPoint M hM hdet)=matrixQuadricPoint M hM hdet :=
    (Equiv.ofBijective gridQuadricPoint gridQuadricPoint_bijective).apply_symm_apply _
  have hh := gridQuadricPoint_column_membership (matrixGridPoint M hM hdet) a
  rw [hp] at hh
  change (Projectivization.mk K M hM).rep∈columnLineSpace a.rep ↔ _ at hh
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep K M hM
  rw [← hc,Units.smul_def,(columnLineSpace a.rep).smul_mem_iff (Units.ne_zero c)] at hh
  exact hh

theorem matrixGridPoint_row_membership {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (hM : M≠0) (hdet : M.det=0)
    (a : Projectivization K (Fin 2 → K)) :
    M∈rowLineSpace a.rep ↔ (matrixGridPoint M hM hdet).2=a := by
  have hp : gridQuadricPoint (matrixGridPoint M hM hdet)=matrixQuadricPoint M hM hdet :=
    (Equiv.ofBijective gridQuadricPoint gridQuadricPoint_bijective).apply_symm_apply _
  have hh := gridQuadricPoint_row_membership (matrixGridPoint M hM hdet) a
  rw [hp] at hh
  change (Projectivization.mk K M hM).rep∈rowLineSpace a.rep ↔ _ at hh
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep K M hM
  rw [← hc,Units.smul_def,(rowLineSpace a.rep).smul_mem_iff (Units.ne_zero c)] at hh
  exact hh

theorem quotient_isotropic_grid_label {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (htwo : (2 : K)≠0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (G : Submodule K V)
    (E : ((B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hnorm : ∀ x,orthogonalQuotientForm B hB G x x=2*(E x).det)
    (v : B.orthogonal G) (hvG : v.val∉G) (hvv : B v.val v.val=0) :
    ∃ label : Projectivization K (Fin 2 → K) × Projectivization K (Fin 2 → K),
      (∀ a,v.val∈quotientRulingCode B G E (Sum.inl a) ↔ label.1=a) ∧
      ∀ a,v.val∈quotientRulingCode B G E (Sum.inr a) ↔ label.2=a := by
  let q : (B.orthogonal G) ⧸ G.comap (B.orthogonal G).subtype := Submodule.Quotient.mk v
  have hq : q≠0 := by
    intro hz
    have hm : v∈G.comap (B.orthogonal G).subtype :=
      (Submodule.Quotient.mk_eq_zero (G.comap (B.orthogonal G).subtype)).mp hz
    exact hvG hm
  have hM : E q≠0 := by intro hz;exact hq (E.injective (hz.trans E.map_zero.symm))
  have hdet : (E q).det=0 := by
    have hh := hnorm q
    change B v.val v.val=2*(E q).det at hh
    rw [hvv] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left htwo
  refine ⟨matrixGridPoint (E q) hM hdet,?_,?_⟩
  · intro a
    rw [quotientRulingCode,liftOrthogonalQuotientCode_mem_iff]
    exact matrixGridPoint_column_membership (E q) hM hdet a
  · intro a
    rw [quotientRulingCode,liftOrthogonalQuotientCode_mem_iff]
    exact matrixGridPoint_row_membership (E q) hM hdet a

noncomputable def gridFiberWeight {α β γ : Type*} [Fintype α]
    (label : α → β×γ) (a : β) (b : γ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x => label x=(a,b))).card

theorem gridFiberWeight_row {α β γ : Type*} [Fintype α] [Fintype γ]
    (label : α → β×γ) (a : β) :
    (∑ b,gridFiberWeight label a b)=Nat.card {x : α // (label x).1=a} := by
  classical
  have hf (b : γ) : Finset.univ.filter (fun x => label x=(a,b))=
      (Finset.univ.filter (fun x => (label x).1=a)).filter (fun x => (label x).2=b) := by
    ext x
    simp [Prod.ext_iff]
  unfold gridFiberWeight
  simp_rw [hf]
  simpa [Nat.card_eq_fintype_card,Fintype.card_subtype] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ.filter (fun x : α => (label x).1=a)) Finset.univ (fun x => (label x).2))

theorem gridFiberWeight_column {α β γ : Type*} [Fintype α] [Fintype β]
    (label : α → β×γ) (b : γ) :
    (∑ a,gridFiberWeight label a b)=Nat.card {x : α // (label x).2=b} := by
  classical
  have hf (a : β) : Finset.univ.filter (fun x => label x=(a,b))=
      (Finset.univ.filter (fun x => (label x).2=b)).filter (fun x => (label x).1=a) := by
    ext x
    simp [Prod.ext_iff,and_comm]
  unfold gridFiberWeight
  simp_rw [hf]
  simpa [Nat.card_eq_fintype_card,Fintype.card_subtype] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ.filter (fun x : α => (label x).2=b)) Finset.univ (fun x => (label x).1))

theorem gridFiberWeight_total {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (label : α → β×γ) : (∑ a,∑ b,gridFiberWeight label a b)=Fintype.card α := by
  classical
  simp_rw [gridFiberWeight_row]
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
  simpa using (Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset α) (Finset.univ : Finset β) (fun x => (label x).1))

theorem finite_subset_count_via_outside {α : Type*} [DecidableEq α]
    (U A V : Finset α) (hAV : A⊆V) (hVU : V⊆U) :
    Nat.card {x : ↥(U \ A) // x.val∈V}=V.card-A.card := by
  classical
  let e : {x : ↥(U \ A) // x.val∈V} ≃ ↥(V \ A) := {
    toFun := fun x => ⟨x.val.val,Finset.mem_sdiff.mpr
      ⟨x.property,(Finset.mem_sdiff.mp x.val.property).2⟩⟩
    invFun := fun x => ⟨⟨x.val,Finset.mem_sdiff.mpr
      ⟨hVU (Finset.mem_sdiff.mp x.property).1,(Finset.mem_sdiff.mp x.property).2⟩⟩,
        (Finset.mem_sdiff.mp x.property).1⟩
    left_inv := fun x => rfl
    right_inv := fun x => rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe,Finset.card_sdiff_of_subset hAV]

theorem weighted_code_grid_projective {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    [Fintype (Projectivization (ZMod p) (Fin 2 → ZMod p))]
    (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C)
    (hcodim : Module.finrank (ZMod p) G+2=Module.finrank (ZMod p) C) :
    ∃ e : (Projectivization (ZMod p) (Fin 2 → ZMod p) ⊕ Projectivization (ZMod p) (Fin 2 → ZMod p)) ≃
      {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) //
        D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D},
      ∃ w : Projectivization (ZMod p) (Fin 2 → ZMod p) → Projectivization (ZMod p) (Fin 2 → ZMod p) → ℕ,
        (codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)).card=
          (codeSignCandidates G).card+(∑ a,∑ b,w a b) ∧
        (∀ a,(codeSignCandidates (e (Sum.inl a)).val).card=(codeSignCandidates G).card+∑ b,w a b) ∧
        (∀ b,(codeSignCandidates (e (Sum.inr b)).val).card=(codeSignCandidates G).card+∑ a,w a b) ∧
        ∃ label : ↥(codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G) \ codeSignCandidates G) →
            Projectivization (ZMod p) (Fin 2 → ZMod p) × Projectivization (ZMod p) (Fin 2 → ZMod p),
          (∀ x a,x.val∈codeSignCandidates (e (Sum.inl a)).val ↔ (label x).1=a) ∧
          (∀ x b,x.val∈codeSignCandidates (e (Sum.inr b)).val ↔ (label x).2=b) ∧
          ∀ a b,w a b=Nat.card {x // label x=(a,b)} := by
  classical
  let B := coordinateDotForm (ZMod p) (4*p)
  have hp : p.Prime := Fact.out
  have htwo : (2 : ZMod p)≠0 := by
    intro hz
    have hd : p∣2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hp2 : p=2 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one
    omega
  have hG : G≤B.orthogonal G := by
    intro x hx y hy
    exact ((SetLike.ext_iff.mp hC x).mp (hGC hx)) y (hGC hy)
  obtain ⟨E,hnorm,hbase⟩ := code_quotient_determinant_model htwo B (coordinateDotForm_symm _ _)
    (coordinateDotForm_nondegenerate _ _) C G hC hGC hcodim
  have hqdim := (codimension_two_quotient_dimensions B (coordinateDotForm_symm _ _)
    (coordinateDotForm_nondegenerate _ _) C G hC hGC hcodim).1
  obtain ⟨e,he⟩ := quotientRulingCode_bijection htwo B (coordinateDotForm_symm _ _)
    (coordinateDotForm_nondegenerate _ _) G hG E hnorm hqdim
  let U := codeSignCandidates (B.orthogonal G)
  let A := codeSignCandidates G
  let S := U \ A
  have labels (x : S) : ∃ label : Projectivization (ZMod p) (Fin 2 → ZMod p) ×
      Projectivization (ZMod p) (Fin 2 → ZMod p),
      (∀ a,x.val∈codeSignCandidates (e (Sum.inl a)).val ↔ label.1=a) ∧
      ∀ b,x.val∈codeSignCandidates (e (Sum.inr b)).val ↔ label.2=b := by
    obtain ⟨hxU,hxA⟩ := Finset.mem_sdiff.mp x.property
    obtain ⟨hxfirst,hxH⟩ := (Finset.mem_filter.mp hxU).2
    let v : B.orthogonal G := ⟨fun j => (modularBitSign (x.val j) : ZMod p),hxH⟩
    have hvG : v.val∉G := by
      intro hv
      exact hxA (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxfirst,hv⟩)
    obtain ⟨label,hrow,hcol⟩ := quotient_isotropic_grid_label htwo B (coordinateDotForm_symm _ _)
      G E hnorm v hvG (signResidue_isotropic x.val)
    refine ⟨label,?_,?_⟩
    · intro a
      rw [he]
      simpa only [codeSignCandidates,Finset.mem_filter,Finset.mem_univ,true_and,hxfirst] using hrow a
    · intro a
      rw [he]
      simpa only [codeSignCandidates,Finset.mem_filter,Finset.mem_univ,true_and,hxfirst] using hcol a
  choose label hlabel using labels
  refine ⟨e,gridFiberWeight label,?_,?_,?_,?_⟩
  · have hsum := gridFiberWeight_total label
    simp only [Fintype.card_coe] at hsum
    have hAU := codeSignCandidates_mono G (B.orthogonal G) hG
    have hh := Finset.card_sdiff_add_card_eq_card hAU
    change S.card+A.card=U.card at hh
    change U.card=A.card+(∑ a,∑ b,gridFiberWeight label a b)
    omega
  · intro a
    have hs := gridFiberWeight_row label a
    let V := codeSignCandidates (e (Sum.inl a)).val
    have hAV : A⊆V := codeSignCandidates_mono G _ (e (Sum.inl a)).property.2
    have hVU : V⊆U := codeSignCandidates_mono _ _ (by
      rw [he]
      exact liftOrthogonalQuotientCode_le_orthogonal B G _)
    let eqv : {x : S // (label x).1=a} ≃ {x : S // x.val∈V} := {
      toFun := fun x => ⟨x.val,(hlabel x.val).1 a |>.mpr x.property⟩
      invFun := fun x => ⟨x.val,(hlabel x.val).1 a |>.mp x.property⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
    rw [Nat.card_congr eqv,finite_subset_count_via_outside U A V hAV hVU] at hs
    have hh := Finset.card_le_card hAV
    change V.card=A.card+∑ b,gridFiberWeight label a b
    omega
  · intro b
    have hs := gridFiberWeight_column label b
    let V := codeSignCandidates (e (Sum.inr b)).val
    have hAV : A⊆V := codeSignCandidates_mono G _ (e (Sum.inr b)).property.2
    have hVU : V⊆U := codeSignCandidates_mono _ _ (by
      rw [he]
      exact liftOrthogonalQuotientCode_le_orthogonal B G _)
    let eqv : {x : S // (label x).2=b} ≃ {x : S // x.val∈V} := {
      toFun := fun x => ⟨x.val,(hlabel x.val).2 b |>.mpr x.property⟩
      invFun := fun x => ⟨x.val,(hlabel x.val).2 b |>.mp x.property⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
    rw [Nat.card_congr eqv,finite_subset_count_via_outside U A V hAV hVU] at hs
    have hh := Finset.card_le_card hAV
    change V.card=A.card+∑ a,gridFiberWeight label a b
    omega
  · refine ⟨label,(fun x a => (hlabel x).1 a),(fun x b => (hlabel x).2 b),?_⟩
    intro a b
    simp only [gridFiberWeight,Nat.card_eq_fintype_card,Fintype.card_subtype]
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]

theorem weighted_code_grid_classification {p : ℕ} [Fact p.Prime] (hodd : p%2=1)
    (C G : Submodule (ZMod p) (Fin (4*p) → ZMod p))
    (hC : C=(coordinateDotForm (ZMod p) (4*p)).orthogonal C) (hGC : G≤C)
    (hcodim : Module.finrank (ZMod p) G+2=Module.finrank (ZMod p) C) :
    let U := codeSignCandidates ((coordinateDotForm (ZMod p) (4*p)).orthogonal G)
    let A := codeSignCandidates G
    ∃ e : (Fin (p+1) ⊕ Fin (p+1)) ≃ {D : Submodule (ZMod p) (Fin (4*p) → ZMod p) //
        D=(coordinateDotForm (ZMod p) (4*p)).orthogonal D ∧ G≤D},
      ∃ w : Fin (p+1) → Fin (p+1) → ℕ,
        U.card=A.card+(∑ a,∑ b,w a b) ∧
        (∀ a,(codeSignCandidates (e (Sum.inl a)).val).card=A.card+(∑ b,w a b)) ∧
        (∀ b,(codeSignCandidates (e (Sum.inr b)).val).card=A.card+(∑ a,w a b)) ∧
        ∃ label : ↥(U \ A) → Fin (p+1)×Fin (p+1),
          (∀ x a,x.val∈codeSignCandidates (e (Sum.inl a)).val ↔ (label x).1=a) ∧
          (∀ x b,x.val∈codeSignCandidates (e (Sum.inr b)).val ↔ (label x).2=b) ∧
          ∀ a b,w a b=Nat.card {x // label x=(a,b)} := by
  classical
  let J := Projectivization (ZMod p) (Fin 2 → ZMod p)
  letI : Fintype J := Fintype.ofFinite J
  have hcard : Fintype.card J=p+1 := by
    rw [Fintype.card_eq_nat_card]
    change Nat.card (Projectivization (ZMod p) (Fin 2 → ZMod p))=p+1
    rw [projective_line_card,Nat.card_zmod]
  let i : J ≃ Fin (p+1) := (Fintype.equivFin J).trans (finCongr hcard)
  obtain ⟨e,w,ht,hr,hc,label,hlabelr,hlabelc,hw⟩ := weighted_code_grid_projective hodd C G hC hGC hcodim
  let e' := (Equiv.sumCongr i.symm i.symm).trans e
  let w' := fun a b : Fin (p+1) => w (i.symm a) (i.symm b)
  let label' := fun x => (i (label x).1,i (label x).2)
  have hrows (a : Fin (p+1)) : (∑ b,w' a b)=∑ b,w (i.symm a) b :=
    i.symm.sum_comp (fun b => w (i.symm a) b)
  have hcols (b : Fin (p+1)) : (∑ a,w' a b)=∑ a,w a (i.symm b) :=
    i.symm.sum_comp (fun a => w a (i.symm b))
  have htotal : (∑ a,∑ b,w' a b)=∑ a,∑ b,w a b := by
    simp_rw [hrows]
    exact i.symm.sum_comp (fun a => ∑ b,w a b)
  refine ⟨e',w',?_,?_,?_,label',?_,?_,?_⟩
  · simpa only [htotal] using ht
  · intro a
    change (codeSignCandidates (e (Sum.inl (i.symm a))).val).card=
      (codeSignCandidates G).card+(∑ b,w' a b)
    rw [hrows]
    exact hr (i.symm a)
  · intro b
    change (codeSignCandidates (e (Sum.inr (i.symm b))).val).card=
      (codeSignCandidates G).card+(∑ a,w' a b)
    rw [hcols]
    exact hc (i.symm b)
  · intro x a
    change x.val∈codeSignCandidates (e (Sum.inl (i.symm a))).val ↔ i (label x).1=a
    constructor
    · intro hx
      rw [(hlabelr x (i.symm a)).mp hx,i.apply_symm_apply]
    · intro hx
      apply (hlabelr x (i.symm a)).mpr
      exact i.injective (hx.trans (i.apply_symm_apply a).symm)
  · intro x b
    change x.val∈codeSignCandidates (e (Sum.inr (i.symm b))).val ↔ i (label x).2=b
    constructor
    · intro hx
      rw [(hlabelc x (i.symm b)).mp hx,i.apply_symm_apply]
    · intro hx
      apply (hlabelc x (i.symm b)).mpr
      exact i.injective (hx.trans (i.apply_symm_apply b).symm)
  · intro a b
    have hpred (x) : label x=(i.symm a,i.symm b) ↔ label' x=(a,b) := by
      constructor
      · intro hx
        simp [label',hx]
      · intro hx
        have h1 : i (label x).1=a := congrArg Prod.fst hx
        have h2 : i (label x).2=b := congrArg Prod.snd hx
        apply Prod.ext
        · exact i.injective (h1.trans (i.apply_symm_apply a).symm)
        · exact i.injective (h2.trans (i.apply_symm_apply b).symm)
    let eqv : {x // label x=(i.symm a,i.symm b)} ≃ {x // label' x=(a,b)} := {
      toFun := fun x => ⟨x.val,(hpred x.val).mp x.property⟩
      invFun := fun x => ⟨x.val,(hpred x.val).mpr x.property⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
    exact (hw (i.symm a) (i.symm b)).trans (Nat.card_congr eqv)

end CompletionTheory

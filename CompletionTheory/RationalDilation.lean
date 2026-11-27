/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionTheory
public import CompletionTheory.CyclicNorms
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
open scoped Matrix

def dilationCandidate {ι κ : Type*} (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (D : Matrix κ κ ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := Matrix.fromBlocks A B Bᵀ D

theorem dilation_gram_iff {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (D : Matrix κ κ ℝ) (a b : ℝ)
    (hA : A*Aᵀ=a • 1) (hB : B*Bᵀ=b • 1) :
    dilationCandidate A B D*(dilationCandidate A B D)ᵀ=(a+b) • 1 ↔
      A*B+B*Dᵀ=0 ∧ Bᵀ*B+D*Dᵀ=(a+b) • 1 := by
  have hI : (a+b) • (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)=
      Matrix.fromBlocks ((a+b) • (1 : Matrix ι ι ℝ)) 0 0 ((a+b) • (1 : Matrix κ κ ℝ)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
  unfold dilationCandidate
  rw [Matrix.fromBlocks_transpose,Matrix.transpose_transpose,Matrix.fromBlocks_multiply,hI,Matrix.fromBlocks_inj]
  constructor
  · rintro ⟨ht,hc,hr,hb⟩
    exact ⟨hc,hb⟩
  · rintro ⟨hc,hb⟩
    refine ⟨?_,hc,?_,hb⟩
    · rw [hA,hB,← add_smul]
    · have ht := congrArg Matrix.transpose hc
      simpa only [Matrix.transpose_add,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] using ht

theorem dilation_cross_transpose {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (D : Matrix κ κ ℝ)
    (hc : A*B+B*Dᵀ=0) : D*Bᵀ= -(Bᵀ*Aᵀ) := by
  have ht := congrArg Matrix.transpose hc
  simp only [Matrix.transpose_add,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] at ht
  exact eq_neg_of_add_eq_zero_right ht

theorem rectangular_gram_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : Matrix ι κ ℝ) (hF : F*Fᵀ=0) : F=0 := by
  apply Matrix.self_mul_conjTranspose_eq_zero.mp
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hF

theorem dilation_forced_BDB {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (D : Matrix κ κ ℝ) (b : ℝ)
    (hB : B*Bᵀ=b • 1) (hc : A*B+B*Dᵀ=0) : B*D*Bᵀ= -b • Aᵀ := by
  calc
    _ = B*(D*Bᵀ) := Matrix.mul_assoc _ _ _
    _ = -((B*Bᵀ)*Aᵀ) := by rw [dilation_cross_transpose A B D hc]; simp only [Matrix.mul_neg,Matrix.mul_assoc]
    _ = _ := by rw [hB]; simp

theorem dilation_forced_BDE_zero {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq δ]
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (E : Matrix δ κ ℝ) (D : Matrix κ κ ℝ) (a b : ℝ)
    (hA : Aᵀ*A=a • 1) (hB : B*Bᵀ=b • 1) (hTot : Bᵀ*B+Eᵀ*E=b • 1)
    (hc : A*B+B*Dᵀ=0) (hb : Bᵀ*B+D*Dᵀ=(a+b) • 1) : B*D*Eᵀ=0 := by
  have hD : D*Dᵀ=(a+b) • 1-Bᵀ*B := by rw [← hb]; abel
  have hE : Eᵀ*E=b • 1-Bᵀ*B := by rw [← hTot]; abel
  have hSand : B*(D*Dᵀ)*Bᵀ=(a*b) • (1 : Matrix ι ι ℝ) := by
    calc
      _ = (a+b) • (B*Bᵀ)-(B*Bᵀ)*(B*Bᵀ) := by
        rw [hD]
        simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,Matrix.one_mul,Matrix.mul_assoc]
      _ = ((a+b)*b-b*b) • (1 : Matrix ι ι ℝ) := by
        rw [hB]
        simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,smul_smul,← sub_smul]
      _ = _ := by congr 1; ring
  have hBB := dilation_forced_BDB A B D b hB hc
  have hGramBB : (B*D*Bᵀ)*(B*D*Bᵀ)ᵀ=(b*b*a) • (1 : Matrix ι ι ℝ) := by
    rw [hBB]
    simp only [Matrix.transpose_smul,Matrix.transpose_transpose,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    rw [hA,smul_smul]
    congr 1
    ring
  apply rectangular_gram_zero
  calc
    _ = B*D*(Eᵀ*E)*Dᵀ*Bᵀ := by simp only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
    _ = b • (B*(D*Dᵀ)*Bᵀ)-(B*D*Bᵀ)*(B*D*Bᵀ)ᵀ := by
      rw [hE]
      simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,Matrix.one_mul,
        Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
    _ = 0 := by
      rw [hSand,hGramBB,smul_smul,← sub_smul]
      have he : b*(a*b)-b*b*a=0 := by ring
      rw [he,zero_smul]

theorem dilation_parameter_necessity {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq δ]
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (E : Matrix δ κ ℝ) (D : Matrix κ κ ℝ) (a b : ℝ) (hb0 : b ≠ 0)
    (hA : Aᵀ*A=a • 1) (hB : B*Bᵀ=b • 1) (hEE : E*Eᵀ=b • 1) (hBE : B*Eᵀ=0)
    (hTot : Bᵀ*B+Eᵀ*E=b • 1) (hc : A*B+B*Dᵀ=0) (hb : Bᵀ*B+D*Dᵀ=(a+b) • 1) :
    ∃ V : Matrix δ δ ℝ,V*Vᵀ=(a+b) • 1 ∧ D=b⁻¹ • (-(Bᵀ*Aᵀ*B)+Eᵀ*V*E) := by
  let V : Matrix δ δ ℝ := b⁻¹ • (E*D*Eᵀ)
  have hEB : E*Bᵀ=0 := by
    have ht := congrArg Matrix.transpose hBE
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] using ht
  have hDB := dilation_cross_transpose A B D hc
  have hEDB : E*D*Bᵀ=0 := by
    calc
      _ = E*(D*Bᵀ) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hDB]; simp only [Matrix.mul_neg,← Matrix.mul_assoc,hEB,Matrix.zero_mul,neg_zero]
  have hF := dilation_forced_BDE_zero A B E D a b hA hB hTot hc hb
  have hD : D*Dᵀ=(a+b) • 1-Bᵀ*B := by rw [← hb]; abel
  have hE : Eᵀ*E=b • 1-Bᵀ*B := by rw [← hTot]; abel
  have hSand : E*(D*Dᵀ)*Eᵀ=((a+b)*b) • (1 : Matrix δ δ ℝ) := by
    calc
      _ = (a+b) • (E*Eᵀ)-(E*Bᵀ)*(B*Eᵀ) := by
        rw [hD]
        simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,Matrix.mul_assoc]
      _ = _ := by rw [hEB,hBE,hEE]; simp [smul_smul]
  have hGram : (E*D*Eᵀ)*(E*D*Eᵀ)ᵀ=(b*((a+b)*b)) • (1 : Matrix δ δ ℝ) := by
    calc
      _ = E*D*(Eᵀ*E)*Dᵀ*Eᵀ := by simp only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
      _ = b • (E*(D*Dᵀ)*Eᵀ)-(E*D*Bᵀ)*(E*D*Bᵀ)ᵀ := by
        rw [hE]
        simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,
          Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
      _ = _ := by rw [hSand,hEDB]; simp [smul_smul]
  have hVGram : V*Vᵀ=(a+b) • (1 : Matrix δ δ ℝ) := by
    dsimp [V]
    simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,hGram]
    have he : b⁻¹*(b⁻¹*(b*((a+b)*b)))=a+b := by field_simp [hb0]
    rw [he]
  have hEV : E*D*Eᵀ=b • V := by dsimp [V]; rw [smul_smul,mul_inv_cancel₀ hb0,one_smul]
  have hExpand : (b*b) • D=Bᵀ*(B*D*Bᵀ)*B+Bᵀ*(B*D*Eᵀ)*E+
      Eᵀ*(E*D*Bᵀ)*B+Eᵀ*(E*D*Eᵀ)*E := by
    calc
      _ = (b • (1 : Matrix κ κ ℝ))*D*(b • 1) := by simp [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
      _ = (Bᵀ*B+Eᵀ*E)*D*(Bᵀ*B+Eᵀ*E) := by rw [hTot]
      _ = _ := by simp only [Matrix.add_mul,Matrix.mul_add,Matrix.mul_assoc]; abel
  rw [dilation_forced_BDB A B D b hB hc,hF,hEDB,hEV] at hExpand
  have hEq : (b*b) • D=b • (-(Bᵀ*Aᵀ*B)+Eᵀ*V*E) := by
    simpa only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,Matrix.smul_mul,Matrix.mul_smul,
      smul_add,smul_neg,neg_smul,Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_assoc] using hExpand
  have hscale := congrArg (fun M : Matrix κ κ ℝ => (b⁻¹*b⁻¹) • M) hEq
  simp only [smul_smul] at hscale
  have h1 : (b⁻¹*b⁻¹)*(b*b)=1 := by field_simp [hb0]
  have h2 : (b⁻¹*b⁻¹)*b=b⁻¹ := by field_simp [hb0]
  rw [h1,h2,one_smul] at hscale
  exact ⟨V,hVGram,hscale⟩

noncomputable def dilationParameterBlock {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
    (b : ℝ) (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (E : Matrix δ κ ℝ) (V : Matrix δ δ ℝ) : Matrix κ κ ℝ :=
  b⁻¹ • (-(Bᵀ*Aᵀ*B)+Eᵀ*V*E)

theorem dilation_parameter_sufficiency {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq δ]
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (E : Matrix δ κ ℝ) (V : Matrix δ δ ℝ) (a b : ℝ) (hb0 : b ≠ 0)
    (hA : Aᵀ*A=a • 1) (hB : B*Bᵀ=b • 1) (hEE : E*Eᵀ=b • 1) (hBE : B*Eᵀ=0)
    (hTot : Bᵀ*B+Eᵀ*E=b • 1) (hV : V*Vᵀ=(a+b) • 1) :
    A*B+B*(dilationParameterBlock b A B E V)ᵀ=0 ∧
      Bᵀ*B+dilationParameterBlock b A B E V*(dilationParameterBlock b A B E V)ᵀ=(a+b) • 1 := by
  let X : Matrix κ κ ℝ := Bᵀ*Aᵀ*B
  let Y : Matrix κ κ ℝ := Eᵀ*V*E
  let D : Matrix κ κ ℝ := b⁻¹ • (-X+Y)
  have hEB : E*Bᵀ=0 := by
    have ht := congrArg Matrix.transpose hBE
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] using ht
  have hXT : B*Xᵀ=b • (A*B) := by
    calc
      _ = (B*Bᵀ)*A*B := by simp only [X,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
      _ = _ := by rw [hB]; simp
  have hYT : B*Yᵀ=0 := by
    calc
      _ = (B*Eᵀ)*Vᵀ*E := by simp only [Y,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
      _ = _ := by rw [hBE]; simp
  have hcross : B*Dᵀ= -(A*B) := by
    simp only [D,Matrix.transpose_smul,Matrix.transpose_add,Matrix.transpose_neg,Matrix.mul_smul,
      Matrix.mul_add,Matrix.mul_neg,hXT,hYT,add_zero,smul_neg,smul_smul,inv_mul_cancel₀ hb0,one_smul]
  have hXX : X*Xᵀ=(b*a) • (Bᵀ*B) := by
    calc
      _ = Bᵀ*Aᵀ*(B*Bᵀ)*A*B := by simp only [X,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
      _ = b • (Bᵀ*(Aᵀ*A)*B) := by rw [hB]; simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,Matrix.one_mul,Matrix.mul_assoc]
      _ = _ := by rw [hA]; simp [smul_smul]
  have hYY : Y*Yᵀ=(b*(a+b)) • (Eᵀ*E) := by
    calc
      _ = Eᵀ*V*(E*Eᵀ)*Vᵀ*E := by simp only [Y,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
      _ = b • (Eᵀ*(V*Vᵀ)*E) := by rw [hEE]; simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,Matrix.one_mul,Matrix.mul_assoc]
      _ = _ := by rw [hV]; simp [smul_smul]
  have hXY : X*Yᵀ=0 := by
    calc
      _ = Bᵀ*Aᵀ*(B*Eᵀ)*Vᵀ*E := by simp only [X,Y,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
      _ = _ := by rw [hBE]; simp
  have hYX : Y*Xᵀ=0 := by
    calc
      _ = Eᵀ*V*(E*Bᵀ)*A*B := by simp only [X,Y,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
      _ = _ := by rw [hEB]; simp
  have hDG : D*Dᵀ=b⁻¹ • (a • (Bᵀ*B)+(a+b) • (Eᵀ*E)) := by
    have h1 : (b⁻¹*b⁻¹)*(b*a)=b⁻¹*a := by field_simp [hb0]
    have h2 : (b⁻¹*b⁻¹)*(b*(a+b))=b⁻¹*(a+b) := by field_simp [hb0]
    calc
      _ = (b⁻¹*b⁻¹) • ((-X+Y)*(-X+Y)ᵀ) := by
        simp only [D,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
      _ = (b⁻¹*b⁻¹) • (X*Xᵀ-X*Yᵀ-Y*Xᵀ+Y*Yᵀ) := by
        congr 1
        simp only [Matrix.transpose_add,Matrix.transpose_neg,Matrix.add_mul,Matrix.mul_add,Matrix.neg_mul,Matrix.mul_neg,neg_neg]
        abel
      _ = _ := by rw [hXX,hYY,hXY,hYX]; simp only [sub_zero,smul_add,smul_smul,h1,h2]
  have hbottom : Bᵀ*B+D*Dᵀ=(a+b) • 1 := by
    rw [hDG]
    calc
      _ = b⁻¹ • (b • (Bᵀ*B)+a • (Bᵀ*B)+(a+b) • (Eᵀ*E)) := by
        simp only [smul_add,smul_smul,inv_mul_cancel₀ hb0,one_smul]
        abel
      _ = b⁻¹ • ((a+b) • (Bᵀ*B+Eᵀ*E)) := by rw [← add_smul,add_comm b a]; simp only [smul_add]
      _ = _ := by
        rw [hTot,smul_smul,smul_smul]
        have he : b⁻¹*(a+b)*b=a+b := by field_simp [hb0]
        rw [he]
  change A*B+B*Dᵀ=0 ∧ Bᵀ*B+D*Dᵀ=(a+b) • 1
  exact ⟨by rw [hcross]; abel,hbottom⟩

theorem dilation_exact_parameter_iff {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq δ]
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (E : Matrix δ κ ℝ) (D : Matrix κ κ ℝ) (a b : ℝ) (hb0 : b ≠ 0)
    (hAA : A*Aᵀ=a • 1) (hA : Aᵀ*A=a • 1) (hB : B*Bᵀ=b • 1) (hEE : E*Eᵀ=b • 1)
    (hBE : B*Eᵀ=0) (hTot : Bᵀ*B+Eᵀ*E=b • 1) :
    dilationCandidate A B D*(dilationCandidate A B D)ᵀ=(a+b) • 1 ↔
      ∃ V : Matrix δ δ ℝ,V*Vᵀ=(a+b) • 1 ∧ D=dilationParameterBlock b A B E V := by
  rw [dilation_gram_iff A B D a b hAA hB]
  constructor
  · rintro ⟨hc,hbottom⟩
    exact dilation_parameter_necessity A B E D a b hb0 hA hB hEE hBE hTot hc hbottom
  · rintro ⟨V,hV,rfl⟩
    exact dilation_parameter_sufficiency A B E V a b hb0 hA hB hEE hBE hTot hV

def frameTopBlock {ι δ : Type*} (T : Matrix (ι ⊕ δ) (ι ⊕ δ) ℝ) : Matrix ι (ι ⊕ δ) ℝ := T.submatrix Sum.inl id
def frameResidualBlock {ι δ : Type*} (T : Matrix (ι ⊕ δ) (ι ⊕ δ) ℝ) : Matrix δ (ι ⊕ δ) ℝ := T.submatrix Sum.inr id

theorem split_scaled_frame_grams {ι δ : Type*} [Fintype ι] [Fintype δ] [DecidableEq ι] [DecidableEq δ]
    (T : Matrix (ι ⊕ δ) (ι ⊕ δ) ℝ) (b : ℝ)
    (hrow : T*Tᵀ=b • 1) (hcol : Tᵀ*T=b • 1) :
    frameTopBlock T*(frameTopBlock T)ᵀ=b • 1 ∧
      frameResidualBlock T*(frameResidualBlock T)ᵀ=b • 1 ∧
      frameTopBlock T*(frameResidualBlock T)ᵀ=0 ∧
      (frameTopBlock T)ᵀ*frameTopBlock T+(frameResidualBlock T)ᵀ*frameResidualBlock T=b • 1 := by
  refine ⟨?_,?_,?_,?_⟩
  · ext i j
    have hh := congrArg (fun M : Matrix (ι ⊕ δ) (ι ⊕ δ) ℝ => M (Sum.inl i) (Sum.inl j)) hrow
    simpa [frameTopBlock,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul] using hh
  · ext i j
    have hh := congrArg (fun M : Matrix (ι ⊕ δ) (ι ⊕ δ) ℝ => M (Sum.inr i) (Sum.inr j)) hrow
    simpa [frameResidualBlock,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul] using hh
  · ext i j
    have hh := congrArg (fun M : Matrix (ι ⊕ δ) (ι ⊕ δ) ℝ => M (Sum.inl i) (Sum.inr j)) hrow
    simpa [frameTopBlock,frameResidualBlock,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul] using hh
  · have hsplit : T=Matrix.fromRows (frameTopBlock T) (frameResidualBlock T) := by
      ext i j
      cases i <;> rfl
    have hh := hcol
    rw [hsplit,Matrix.transpose_fromRows,Matrix.fromCols_mul_fromRows] at hh
    exact hh

theorem hadamard_seed_dilation_iff {a d : ℕ} (ha : 0<a)
    (A : Matrix (Fin a) (Fin a) ℝ) (hA : Matrix.IsHadamard A)
    (T : Matrix (Fin a ⊕ Fin d) (Fin a ⊕ Fin d) ℝ) (hT : Matrix.IsHadamard T)
    (D : Matrix (Fin a ⊕ Fin d) (Fin a ⊕ Fin d) ℝ) :
    dilationCandidate A (frameTopBlock T) D*(dilationCandidate A (frameTopBlock T) D)ᵀ=
        ((a+(a+d) : ℕ) : ℝ) • 1 ↔
      ∃ V : Matrix (Fin d) (Fin d) ℝ,V*Vᵀ=((a+(a+d) : ℕ) : ℝ) • 1 ∧
        D=dilationParameterBlock ((a+d : ℕ) : ℝ) A (frameTopBlock T) (frameResidualBlock T) V := by
  have hAA : A*Aᵀ=(a : ℝ) • 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Fintype.card_fin] using hA.mul_conjTranspose
  have hA' : Aᵀ*A=(a : ℝ) • 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Fintype.card_fin] using hA.conjTranspose_mul
  have hrow : T*Tᵀ=((a+d : ℕ) : ℝ) • 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Fintype.card_sum,Fintype.card_fin] using hT.mul_conjTranspose
  have hcol : Tᵀ*T=((a+d : ℕ) : ℝ) • 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Fintype.card_sum,Fintype.card_fin] using hT.conjTranspose_mul
  obtain ⟨hB,hEE,hBE,hTot⟩ := split_scaled_frame_grams T ((a+d : ℕ) : ℝ) hrow hcol
  have hb0 : ((a+d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show a+d ≠ 0 by omega)
  simpa only [Nat.cast_add] using dilation_exact_parameter_iff A (frameTopBlock T) (frameResidualBlock T) D
    (a : ℝ) ((a+d : ℕ) : ℝ) hb0 hAA hA' hB hEE hBE hTot

def quaternionBlock (a b c d : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![a,b,c,d; -b,a,-d,c; -c,d,a,-b; -d,-c,b,a]

theorem quaternionBlock_gram (a b c d : ℤ) :
    quaternionBlock a b c d*(quaternionBlock a b c d)ᵀ=
      (a^2+b^2+c^2+d^2) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionBlock,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply] <;> ring

theorem integer_four_frame_exists (n : ℕ) :
    ∃ V : Matrix (Fin 4) (Fin 4) ℤ, V*Vᵀ=(n : ℤ) • 1 := by
  obtain ⟨a,b,c,d,h⟩ := Nat.sum_four_squares n
  refine ⟨quaternionBlock a b c d, ?_⟩
  rw [quaternionBlock_gram]
  congr 1
  exact_mod_cast h

theorem integer_product_frame_exists (n k : ℕ) :
    ∃ V : Matrix (Fin k × Fin 4) (Fin k × Fin 4) ℤ, V*Vᵀ=(n : ℤ) • 1 := by
  obtain ⟨M,hM⟩ := integer_four_frame_exists n
  refine ⟨Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℤ) M, ?_⟩
  have ht : (Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℤ) M)ᵀ =
      Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℤ)ᵀ Mᵀ :=
    (Matrix.kroneckerMap_transpose (fun x y : ℤ => x*y) _ _).symm
  rw [ht]
  have hm : Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℤ) M *
      Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℤ)ᵀ Mᵀ =
      Matrix.kronecker (1 * (1 : Matrix (Fin k) (Fin k) ℤ)ᵀ) (M*Mᵀ) :=
    (Matrix.mul_kronecker_mul _ _ _ _).symm
  rw [hm]
  simp only [Matrix.transpose_one,Matrix.one_mul,hM]
  calc
    _ = (n : ℤ) • Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℤ) (1 : Matrix (Fin 4) (Fin 4) ℤ) := Matrix.kronecker_smul _ _ _
    _ = _ := by rw [show Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℤ) (1 : Matrix (Fin 4) (Fin 4) ℤ) = 1 from Matrix.one_kronecker_one]

theorem integer_frame_exists_of_four_dvd (n d : ℕ) (hd : 4 ∣ d) :
    ∃ V : Matrix (Fin d) (Fin d) ℤ, V*Vᵀ=(n : ℤ) • 1 := by
  obtain ⟨k,rfl⟩ := hd
  obtain ⟨M,hM⟩ := integer_product_frame_exists n k
  let e : Fin (4*k) ≃ Fin k × Fin 4 :=
    (finCongr (Nat.mul_comm 4 k)).trans finProdFinEquiv.symm
  refine ⟨M.submatrix e e, ?_⟩
  have ht : (M.submatrix e e)ᵀ=Mᵀ.submatrix e e := rfl
  rw [ht,Matrix.submatrix_mul_equiv,hM]
  ext i j
  simp [Matrix.submatrix_apply,Matrix.smul_apply,Matrix.one_apply,Matrix.natCast_apply,e.injective.eq_iff]

def integerFrameReal {d : ℕ} (V : Matrix (Fin d) (Fin d) ℤ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (V i j : ℝ)

theorem integerFrameReal_gram {n d : ℕ} (V : Matrix (Fin d) (Fin d) ℤ)
    (hV : V*Vᵀ=(n : ℤ) • 1) :
    integerFrameReal V*(integerFrameReal V)ᵀ=(n : ℝ) • 1 := by
  ext i j
  have hh := congrArg (fun M : Matrix (Fin d) (Fin d) ℤ => M i j) hV
  have hh' := congrArg (fun z : ℤ => (z : ℝ)) hh
  simpa [integerFrameReal,Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,
    Matrix.one_apply,Matrix.natCast_apply,smul_eq_mul] using hh'

noncomputable def rationalSignMatrix {ι κ : Type*} (A : Matrix ι κ ℝ) : Matrix ι κ ℚ :=
  fun i j => if A i j=1 then 1 else -1

def realOfRationalMatrix {ι κ : Type*} (A : Matrix ι κ ℚ) : Matrix ι κ ℝ :=
  fun i j => (A i j : ℝ)

theorem rationalSignMatrix_cast {ι κ : Type*} (A : Matrix ι κ ℝ) (hA : IsSignMatrix A) :
    realOfRationalMatrix (rationalSignMatrix A)=A := by
  ext i j
  rcases hA i j with h|h <;> norm_num [realOfRationalMatrix,rationalSignMatrix,h]

theorem realOfRationalMatrix_mul {ι κ δ : Type*} [Fintype κ]
    (A : Matrix ι κ ℚ) (B : Matrix κ δ ℚ) :
    realOfRationalMatrix (A*B)=realOfRationalMatrix A*realOfRationalMatrix B := by
  ext i j
  simp [realOfRationalMatrix,Matrix.mul_apply]

theorem rational_parameter_cast {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
    (A : Matrix ι ι ℚ) (B : Matrix ι κ ℚ) (E : Matrix δ κ ℚ) (V : Matrix δ δ ℚ) (b : ℚ) :
    realOfRationalMatrix (b⁻¹ • (-Bᵀ*Aᵀ*B+Eᵀ*V*E))=
      dilationParameterBlock (b : ℝ) (realOfRationalMatrix A) (realOfRationalMatrix B)
        (realOfRationalMatrix E) (realOfRationalMatrix V) := by
  simp only [dilationParameterBlock,Matrix.smul_apply,smul_eq_mul]
  ext i j
  simp [realOfRationalMatrix,Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul]

theorem hadamard_seed_rational_dilation {a d : ℕ} (ha : 0<a) (hd : 4 ∣ d)
    (A : Matrix (Fin a) (Fin a) ℝ) (hA : Matrix.IsHadamard A)
    (T : Matrix (Fin a ⊕ Fin d) (Fin a ⊕ Fin d) ℝ) (hT : Matrix.IsHadamard T) :
    ∃ D : Matrix (Fin a ⊕ Fin d) (Fin a ⊕ Fin d) ℚ,
      dilationCandidate A (frameTopBlock T) (realOfRationalMatrix D)*
        (dilationCandidate A (frameTopBlock T) (realOfRationalMatrix D))ᵀ=
          ((a+(a+d) : ℕ) : ℝ) • 1 := by
  obtain ⟨W,hW⟩ := integer_frame_exists_of_four_dvd (a+(a+d)) d hd
  let V : Matrix (Fin d) (Fin d) ℚ := fun i j => (W i j : ℚ)
  have hV : realOfRationalMatrix V=integerFrameReal W := by ext i j; simp [V,realOfRationalMatrix,integerFrameReal]
  let Aq := rationalSignMatrix A
  let Bq := rationalSignMatrix (frameTopBlock T)
  let Eq := rationalSignMatrix (frameResidualBlock T)
  have hAc : realOfRationalMatrix Aq=A := rationalSignMatrix_cast A (fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem i j))
  have hBc : realOfRationalMatrix Bq=frameTopBlock T := rationalSignMatrix_cast _ (fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hT.apply_mem (Sum.inl i) j))
  have hEc : realOfRationalMatrix Eq=frameResidualBlock T := rationalSignMatrix_cast _ (fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hT.apply_mem (Sum.inr i) j))
  refine ⟨((a+d : ℕ) : ℚ)⁻¹ • (-Bqᵀ*Aqᵀ*Bq+Eqᵀ*V*Eq), ?_⟩
  apply (hadamard_seed_dilation_iff ha A hA T hT _).mpr
  refine ⟨integerFrameReal W,integerFrameReal_gram W hW, ?_⟩
  rw [rational_parameter_cast,hAc,hBc,hEc,hV]
  simp only [Rat.cast_natCast]

theorem hadamard_seed_sign_completion_iff {a d : ℕ} (ha : 0<a)
    (A : Matrix (Fin a) (Fin a) ℝ) (hA : Matrix.IsHadamard A)
    (T : Matrix (Fin a ⊕ Fin d) (Fin a ⊕ Fin d) ℝ) (hT : Matrix.IsHadamard T)
    (D : Matrix (Fin a ⊕ Fin d) (Fin a ⊕ Fin d) ℝ) :
    Matrix.IsHadamard (dilationCandidate A (frameTopBlock T) D) ↔
      IsSignMatrix D ∧ ∃ V : Matrix (Fin d) (Fin d) ℝ,
        V*Vᵀ=((a+(a+d) : ℕ) : ℝ) • 1 ∧
        D=dilationParameterBlock ((a+d : ℕ) : ℝ) A (frameTopBlock T) (frameResidualBlock T) V := by
  constructor
  · intro h
    refine ⟨fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mp (h.apply_mem (Sum.inr i) (Sum.inr j)), ?_⟩
    apply (hadamard_seed_dilation_iff ha A hA T hT D).mp
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Fintype.card_sum,Fintype.card_fin] using h.mul_conjTranspose
  · rintro ⟨hD,hV⟩
    letI : Nonempty (Fin a) := ⟨⟨0,ha⟩⟩
    apply isHadamard_mathlib
    constructor
    · intro i j
      cases i with
      | inl i =>
        cases j with
        | inl j => exact Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem i j)
        | inr j => exact Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hT.apply_mem (Sum.inl i) j)
      | inr i =>
        cases j with
        | inl j => exact Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hT.apply_mem (Sum.inl j) i)
        | inr j => exact hD i j
    · simpa only [Fintype.card_sum,Fintype.card_fin] using
        (hadamard_seed_dilation_iff ha A hA T hT D).mpr hV

theorem hadamard_seed_rational_completion {a d : ℕ} (ha : 0<a) (hd : 4 ∣ d)
    (A : Matrix (Fin a) (Fin a) ℝ) (hA : Matrix.IsHadamard A)
    (T : Matrix (Fin a ⊕ Fin d) (Fin a ⊕ Fin d) ℝ) (hT : Matrix.IsHadamard T) :
    ∃ Z : Matrix (Fin a ⊕ (Fin a ⊕ Fin d)) (Fin a ⊕ (Fin a ⊕ Fin d)) ℚ,
      realOfRationalMatrix Z*(realOfRationalMatrix Z)ᵀ=((a+(a+d) : ℕ) : ℝ) • 1 ∧
      (∀ i j,realOfRationalMatrix Z (Sum.inl i) (Sum.inl j)=A i j) ∧
      (∀ i j,realOfRationalMatrix Z (Sum.inl i) (Sum.inr j)=frameTopBlock T i j) ∧
      (∀ i j,realOfRationalMatrix Z (Sum.inr i) (Sum.inl j)=frameTopBlock T j i) := by
  obtain ⟨D,hD⟩ := hadamard_seed_rational_dilation ha hd A hA T hT
  let Aq := rationalSignMatrix A
  let Bq := rationalSignMatrix (frameTopBlock T)
  have hAc : realOfRationalMatrix Aq=A := rationalSignMatrix_cast A (fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem i j))
  have hBc : realOfRationalMatrix Bq=frameTopBlock T := rationalSignMatrix_cast _ (fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hT.apply_mem (Sum.inl i) j))
  let Z : Matrix (Fin a ⊕ (Fin a ⊕ Fin d)) (Fin a ⊕ (Fin a ⊕ Fin d)) ℚ := Matrix.fromBlocks Aq Bq Bqᵀ D
  have hZ : realOfRationalMatrix Z=dilationCandidate A (frameTopBlock T) (realOfRationalMatrix D) := by
    ext i j
    cases i <;> cases j <;>
      simp only [Z,dilationCandidate,realOfRationalMatrix,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.transpose_apply] <;>
      first | exact congrFun (congrFun hAc _) _ | exact congrFun (congrFun hBc _) _ | rfl
  refine ⟨Z,by rw [hZ]; exact hD,?_,?_,?_⟩ <;> intro i j <;> rw [hZ] <;> rfl
end CompletionTheory

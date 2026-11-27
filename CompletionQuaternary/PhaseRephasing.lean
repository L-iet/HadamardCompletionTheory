/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionBloch.BlochAlgebra
@[expose] public section
namespace CompletionTheory.Bloch
noncomputable section
open scoped ComplexConjugate

theorem unit_mul_conj {z : ℂ} (hz : Complex.normSq z=1) : z*conj z=1 := by
  rw [Complex.mul_conj,hz]
  norm_num

theorem unit_conj_mul {z : ℂ} (hz : Complex.normSq z=1) : conj z*z=1 := by
  rw [mul_comm]
  exact unit_mul_conj hz

theorem fourth_ratio_implies_equal_powers {a b : ℂ} (hb : Complex.normSq b=1)
    (h : (a*conj b)^4=1) : a^4=b^4 := by
  calc
    a^4 = a^4*(conj b*b)^4 := by rw [unit_conj_mul hb]; simp
    _ = (a*conj b)^4*b^4 := by ring
    _ = b^4 := by rw [h,one_mul]

theorem equal_powers_implies_fourth_ratio {a b : ℂ} (hb : Complex.normSq b=1)
    (h : a^4=b^4) : (a*conj b)^4=1 := by
  calc
    _ = a^4*(conj b)^4 := by ring
    _ = b^4*(conj b)^4 := by rw [h]
    _ = (b*conj b)^4 := by ring
    _ = 1 := by rw [unit_mul_conj hb]; norm_num

theorem rephase_by_fourth_power {ι : Type*} (a d : ι → ℂ) (K : ι → ι → ℂ)
    (ha : ∀ i,Complex.normSq (a i)=1)
    (hK : ∀ i j,K i j=a i*conj (a j)*(1+d i*conj (d j)))
    (hedge : ∀ i j,K i j≠0 → (a i*conj (a j))^4=1) :
    ∃ b : ι → ℂ,(∀ i,(b i)^4=1) ∧
      ∀ i j,b i*conj (b j)*(1+d i*conj (d j))=K i j := by
  classical
  let C := Set.range (fun i => (a i)^4)
  have hchoose : ∀ c : C,∃ i,(a i)^4=c.val := fun c => c.property
  choose rep hrep using hchoose
  let cl (i : ι) : C := ⟨(a i)^4,⟨i,rfl⟩⟩
  let t (i : ι) : ℂ := a (rep (cl i))
  let b (i : ι) : ℂ := a i*conj (t i)
  have ht (i : ι) : (t i)^4=(a i)^4 := hrep (cl i)
  have htunit (i : ι) : Complex.normSq (t i)=1 := ha (rep (cl i))
  refine ⟨b,fun i => equal_powers_implies_fourth_ratio (htunit i) (ht i).symm,?_⟩
  intro i j
  by_cases he : (a i)^4=(a j)^4
  · have hc : cl i=cl j := Subtype.ext he
    have heq : t i=t j := congrArg (fun c : C => a (rep c)) hc
    have hratio : b i*conj (b j)=a i*conj (a j) := by
      change (a i*conj (t i))*conj (a j*conj (t j))=a i*conj (a j)
      rw [heq]
      calc
        _ = a i*conj (a j)*(conj (t j)*t j) := by simp only [map_mul,Complex.conj_conj]; ring
        _ = _ := by rw [unit_conj_mul (htunit j),mul_one]
    rw [hratio]
    exact (hK i j).symm
  · have hk0 : K i j=0 := by
      by_contra hk
      exact he (fourth_ratio_implies_equal_powers (ha j) (hedge i j hk))
    have hr0 : a i*conj (a j)≠0 := by
      intro hz
      have hn : Complex.normSq (a i*conj (a j))=1 := by
        rw [Complex.normSq_mul,Complex.normSq_conj,ha i,ha j]
        norm_num
      rw [hz] at hn
      norm_num at hn
    have hc0 : 1+d i*conj (d j)=0 :=
      (mul_eq_zero.mp ((hK i j).symm.trans hk0)).resolve_left hr0
    rw [hc0,mul_zero,hk0]

end
end CompletionTheory.Bloch

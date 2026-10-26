import Muon.SignSGD.Defs

/-!
# Appendix I (SignSGD): the batch constant `𝒩_B`

Interface for the label `prop:app-sgd-batch-coefficient`, one theorem per part (i)–(iv).
Source of record: snapshot `cr-2026-10-22`, `sections/08-signsgd/section.tex` l. 162–170.
The constant is `Muon.SignSGD.batchConst` (`eqn:signsgd-Nb`, defined in `Muon.SignSGD.Defs`),
reused here and not redefined. Appendix H consumes the two-sided bound of part (ii) through
`eqn:app-phase-NB`.

Quantifier order: every statement is for all integers `B ≥ 1` (part (iii), (ii)) or is a
limit along `B → ∞` over `ℕ` (part (iv)). The constant `√B` is `Real.sqrt (B : ℝ)`.
-/

open Filter Topology

namespace Muon.SignSGD

open MeasureTheory ProbabilityTheory Set Real

private lemma gb_pdf_even (x : ℝ) : gaussianPDFReal 0 1 x = gaussianPDFReal 0 1 |x| := by
  simp only [gaussianPDFReal_def, sub_zero, sq_abs]

private lemma gb_int_Ioi_one : ∫ t in Ioi (0:ℝ), t * rexp (-(1/2:ℝ) * t ^ 2) = 1 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1/2) (by norm_num)
    (by norm_num) (by norm_num)
  have e1 : ∀ t : ℝ, t ^ (1:ℝ) = t := fun t => Real.rpow_one t
  have e2 : ∀ t : ℝ, t ^ (2:ℝ) = t ^ 2 := fun t => by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  simp only [e1, e2] at h
  rw [h]
  norm_num [Real.Gamma_one]

private lemma gb_abs_moment : ∫ x, |x| ∂(gaussianReal 0 1) = √(2 / π) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hsymm : ∀ x : ℝ, gaussianPDFReal 0 1 x • |x|
      = (fun t : ℝ => gaussianPDFReal 0 1 t * t) |x| := by
    intro x
    rw [smul_eq_mul, gb_pdf_even x]
  simp_rw [hsymm]
  rw [integral_comp_abs (f := fun t => gaussianPDFReal 0 1 t * t)]
  have hpos : ∫ t in Ioi (0:ℝ), gaussianPDFReal 0 1 t * t
      = (√(2 * π * ((1:NNReal):ℝ)))⁻¹ * 1 := by
    rw [← gb_int_Ioi_one, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
    ring_nf
  have h2 : 0 ≤ 2 * (√(2 * π * ((1:NNReal):ℝ)))⁻¹ := by positivity
  rw [hpos, mul_one, ← Real.sqrt_sq h2]
  congr 1
  rw [NNReal.coe_one, mul_one, mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
  field_simp

private lemma gb_int_Ioi_four :
    ∫ t in Ioi (0:ℝ), t ^ 4 * rexp (-(1/2:ℝ) * t ^ 2) = 3 * (√2 * √π) / 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 4) (b := 1/2) (by norm_num)
    (by norm_num) (by norm_num)
  have e1 : ∀ t : ℝ, t ^ (4:ℝ) = t ^ 4 := fun t => by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have e2 : ∀ t : ℝ, t ^ (2:ℝ) = t ^ 2 := fun t => by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  simp only [e1, e2] at h
  rw [h]
  have hG : Real.Gamma ((4 + 1) / 2) = 3 * √Real.pi / 4 := by
    rw [show ((4:ℝ) + 1) / 2 = 1/2 + 1 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  have hA : (1/2:ℝ) ^ (-((4:ℝ) + 1) / 2) = 4 * √2 := by
    rw [show -((4:ℝ) + 1) / 2 = -(2:ℝ) - 1/2 by norm_num, Real.rpow_sub (by norm_num),
      Real.rpow_neg (by norm_num), Real.sqrt_eq_rpow, one_div, Real.inv_rpow (by norm_num)]
    norm_num
    rw [one_div, Real.inv_rpow (by norm_num), div_inv_eq_mul]
  rw [hG, hA]
  ring

private lemma gb_four_moment : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hsymm : ∀ x : ℝ, gaussianPDFReal 0 1 x • x ^ 4
      = (fun t : ℝ => gaussianPDFReal 0 1 t * t ^ 4) |x| := by
    intro x
    rw [smul_eq_mul, gb_pdf_even x, ← Even.pow_abs ⟨2, rfl⟩ x]
  simp_rw [hsymm]
  rw [integral_comp_abs (f := fun t => gaussianPDFReal 0 1 t * t ^ 4)]
  have hpos : ∫ t in Ioi (0:ℝ), gaussianPDFReal 0 1 t * t ^ 4
      = (√(2 * π * ((1:NNReal):ℝ)))⁻¹ * (3 * (√2 * √π) / 2) := by
    rw [← gb_int_Ioi_four, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
    ring_nf
  rw [hpos]
  have h2 : 0 < √2 := by positivity
  have hpi : 0 < √π := by positivity
  rw [NNReal.coe_one, mul_one, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  field_simp

private lemma gb_L2 : MemLp id 2 (gaussianReal 0 1) := by
  simpa using memLp_id_gaussianReal (μ := 0) (v := 1) 2

private lemma gb_sq_moment : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_eq_sub gb_L2
  rw [variance_id_gaussianReal] at h
  simp only [Pi.pow_apply, id, integral_id_gaussianReal] at h
  norm_num at h
  linarith

-- product-measure helpers
private lemma gb_int_coord (B : ℕ) (b : Fin B) (f : ℝ → ℝ) (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun x : Fin B → ℝ => f (x b)) (Measure.pi fun _ : Fin B => gaussianReal 0 1) :=
  (measurePreserving_eval (fun _ : Fin B => gaussianReal 0 1) b).integrable_comp_of_integrable hf

private lemma gb_pair_int (B : ℕ) (b : Fin B) (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) :
    ∫ p : (Fin B → ℝ) × (Fin B → ℝ), f (p.1 b) * g (p.2 b)
      ∂((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1))
      = (∫ x, f x ∂(gaussianReal 0 1)) * ∫ y, g y ∂(gaussianReal 0 1) := by
  rw [integral_prod_mul (fun x : Fin B → ℝ => f (x b)) (fun y : Fin B → ℝ => g (y b))]
  rw [integral_comp_eval (i := b) hf.aestronglyMeasurable,
    integral_comp_eval (i := b) hg.aestronglyMeasurable]

private lemma gb_pair_integrable (B : ℕ) (b : Fin B) (f g : ℝ → ℝ)
    (hf : Integrable f (gaussianReal 0 1)) (hg : Integrable g (gaussianReal 0 1)) :
    Integrable (fun p : (Fin B → ℝ) × (Fin B → ℝ) => f (p.1 b) * g (p.2 b))
      ((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1)) :=
  (gb_int_coord B b f hf).mul_prod (gb_int_coord B b g hg)

private lemma gb_L1 : Integrable id (gaussianReal 0 1) :=
  gb_L2.integrable (by norm_num)

private lemma gb_w_int (B : ℕ) (b : Fin B) :
    ∫ p : (Fin B → ℝ) × (Fin B → ℝ), |p.1 b| * |p.2 b|
      ∂((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1)) = 2 / π := by
  have h := gb_pair_int B b (fun x => |x|) (fun y => |y|) measurable_abs measurable_abs
  simp only at h
  rw [h, gb_abs_moment, Real.mul_self_sqrt (by positivity)]

private lemma gb_T_integrable (B : ℕ) :
    Integrable (fun p : (Fin B → ℝ) × (Fin B → ℝ) => ∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2)
      ((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1)) := by
  refine integrable_finsetSum _ (fun b _ => ?_)
  exact gb_pair_integrable B b (fun x => x ^ 2) (fun x => x ^ 2) gb_L2.integrable_sq gb_L2.integrable_sq

private lemma gb_E_T (B : ℕ) :
    ∫ p : (Fin B → ℝ) × (Fin B → ℝ), ∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2
      ∂((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1)) = B := by
  have h : ∀ b : Fin B, ∫ p : (Fin B → ℝ) × (Fin B → ℝ), p.1 b ^ 2 * p.2 b ^ 2
      ∂((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1)) = 1 := fun b => by
    have := gb_pair_int B b (fun x => x ^ 2) (fun y => y ^ 2) (by fun_prop) (by fun_prop)
    simp only at this
    rw [this, gb_sq_moment]
    norm_num
  rw [integral_finsetSum _ (fun b _ => gb_pair_integrable B b (fun x => x ^ 2) (fun x => x ^ 2) gb_L2.integrable_sq gb_L2.integrable_sq)]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]


private lemma gb_pow4 : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := by
  have hL4 : MemLp id ((4:ℕ):ENNReal) (gaussianReal 0 1) := by
    simpa using memLp_id_gaussianReal' (μ := 0) (v := 1) (4:ENNReal) (by norm_num)
  refine (hL4.integrable_norm_pow').congr (ae_of_all _ (fun x => ?_))
  simp [Real.norm_eq_abs, Even.pow_abs ⟨2, rfl⟩ x]

private lemma gb_prod_two (B : ℕ) (b b' : Fin B) (hne : b ≠ b') (x : Fin B → ℝ) :
    ∏ c : Fin B, (if c = b ∨ c = b' then x c ^ 2 else 1) = x b ^ 2 * x b' ^ 2 := by
  rw [Fintype.prod_eq_mul b b' hne]
  · simp [hne, hne.symm]
  · intro c hc
    simp [hc.1, hc.2]

private lemma gb_cross_eq (B : ℕ) (b b' : Fin B) (hne : b ≠ b') :
    (fun p : (Fin B → ℝ) × (Fin B → ℝ) => (p.1 b ^ 2 * p.2 b ^ 2) * (p.1 b' ^ 2 * p.2 b' ^ 2))
      = fun p => (∏ c, (if c = b ∨ c = b' then p.1 c ^ 2 else 1))
          * (∏ c, (if c = b ∨ c = b' then p.2 c ^ 2 else 1)) := by
  funext p
  rw [gb_prod_two B b b' hne, gb_prod_two B b b' hne]
  ring

private lemma gb_cross_integrable (B : ℕ) (b b' : Fin B) (hne : b ≠ b') :
    Integrable (fun p : (Fin B → ℝ) × (Fin B → ℝ) => (p.1 b ^ 2 * p.2 b ^ 2) * (p.1 b' ^ 2 * p.2 b' ^ 2))
      ((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1)) := by
  rw [gb_cross_eq B b b' hne]
  have hf : ∀ c : Fin B, Integrable (fun x : ℝ => if c = b ∨ c = b' then x ^ 2 else 1)
      (gaussianReal 0 1) := by
    intro c
    by_cases h : c = b ∨ c = b'
    · simp only [h, if_true]
      exact gb_L2.integrable_sq
    · simp only [h, if_false]
      exact integrable_const _
  exact (Integrable.fintype_prod (fun c => hf c)).mul_prod (Integrable.fintype_prod (fun c => hf c))

private lemma gb_aa_integrable (B : ℕ) (b b' : Fin B) :
    Integrable (fun p : (Fin B → ℝ) × (Fin B → ℝ) => (p.1 b ^ 2 * p.2 b ^ 2) * (p.1 b' ^ 2 * p.2 b' ^ 2))
      ((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1)) := by
  by_cases h : b = b'
  · subst h
    exact (gb_pair_integrable B b (fun x => x ^ 4) (fun y => y ^ 4) gb_pow4 gb_pow4).congr
      (ae_of_all _ (fun p => by ring))
  · exact gb_cross_integrable B b b' h

private lemma gb_pi_int (B : ℕ) (F G : Fin B → ℝ → ℝ) :
    ∫ p : (Fin B → ℝ) × (Fin B → ℝ), (∏ c, F c (p.1 c)) * (∏ c, G c (p.2 c))
      ∂((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1))
      = (∏ c, ∫ x, F c x ∂(gaussianReal 0 1)) * ∏ c, ∫ y, G c y ∂(gaussianReal 0 1) := by
  rw [integral_prod_mul (fun x : Fin B → ℝ => ∏ c, F c (x c)) (fun y : Fin B → ℝ => ∏ c, G c (y c)),
    integral_fintype_prod_eq_prod (fun c x => F c x), integral_fintype_prod_eq_prod (fun c x => G c x)]

private lemma gb_cross_value (B : ℕ) (b b' : Fin B) (hne : b ≠ b') :
    ∫ p : (Fin B → ℝ) × (Fin B → ℝ), (p.1 b ^ 2 * p.2 b ^ 2) * (p.1 b' ^ 2 * p.2 b' ^ 2)
      ∂((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1)) = 1 := by
  rw [gb_cross_eq B b b' hne, gb_pi_int B (fun c x => if c = b ∨ c = b' then x ^ 2 else 1)
    (fun c x => if c = b ∨ c = b' then x ^ 2 else 1)]
  have hc : ∀ c : Fin B, ∫ x, (if c = b ∨ c = b' then x ^ 2 else 1) ∂(gaussianReal 0 1) = 1 := by
    intro c
    by_cases h : c = b ∨ c = b'
    · simp only [h, if_true]
      exact gb_sq_moment
    · simp only [h, if_false]
      simp
  simp only [hc, Finset.prod_const_one, mul_one]

private lemma gb_diag_value (B : ℕ) (b : Fin B) :
    ∫ p : (Fin B → ℝ) × (Fin B → ℝ), (p.1 b ^ 2 * p.2 b ^ 2) * (p.1 b ^ 2 * p.2 b ^ 2)
      ∂((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1)) = 9 := by
  have hf : (fun p : (Fin B → ℝ) × (Fin B → ℝ) => (p.1 b ^ 2 * p.2 b ^ 2) * (p.1 b ^ 2 * p.2 b ^ 2))
      = fun p => (fun x : ℝ => x ^ 4) (p.1 b) * (fun y : ℝ => y ^ 4) (p.2 b) := by
    funext p; ring
  rw [hf, gb_pair_int B b (fun x => x ^ 4) (fun y => y ^ 4) (by fun_prop) (by fun_prop),
    gb_four_moment]
  norm_num

private lemma gb_TT_value (B : ℕ) :
    ∫ p : (Fin B → ℝ) × (Fin B → ℝ), (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) * (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2)
      ∂((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1)) = (B:ℝ) ^ 2 + 8 * B := by
  simp only [Finset.sum_mul_sum]
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun b' _ => gb_aa_integrable B b b'))]
  have hinner : ∀ b : Fin B, ∫ p : (Fin B → ℝ) × (Fin B → ℝ), ∑ b' : Fin B,
      (p.1 b ^ 2 * p.2 b ^ 2) * (p.1 b' ^ 2 * p.2 b' ^ 2)
      ∂((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1))
      = ∑ b' : Fin B, (if b = b' then (9:ℝ) else 1) := by
    intro b
    rw [integral_finsetSum _ (fun b' _ => gb_aa_integrable B b b')]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    by_cases h : b = b'
    · subst h
      rw [if_pos rfl, gb_diag_value]
    · rw [if_neg h, gb_cross_value B b b' h]
  simp only [hinner]
  have hsum : ∀ b : Fin B, ∑ b' : Fin B, (if b = b' then (9:ℝ) else 1) = B + 8 := by
    intro b
    have h1 : ∀ b' : Fin B, (if b = b' then (9:ℝ) else 1)
        = 1 + 8 * (if b = b' then 1 else 0) := by
      intro b'
      split_ifs <;> norm_num
    simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  simp only [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma gb_amgm (r T : ℝ) (hr : 0 < r) (hT : 0 ≤ T) :
    √T ≤ (1 / (2 * r)) * T + r / 2 := by
  have hs := Real.sq_sqrt hT
  have key : √T * (2 * r) ≤ T + r ^ 2 := by
    nlinarith [sq_nonneg (√T - r), Real.sqrt_nonneg T]
  have e : (1 / (2 * r)) * T + r / 2 = (T + r ^ 2) / (2 * r) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  exact key

private lemma gb_T_nonneg (B : ℕ) (p : (Fin B → ℝ) × (Fin B → ℝ)) :
    0 ≤ ∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2 :=
  Finset.sum_nonneg (fun b _ => by positivity)

private lemma gb_sqrt_T_integrable (B : ℕ) (r : ℝ) (hr : 0 < r) :
    Integrable (fun p : (Fin B → ℝ) × (Fin B → ℝ) => √(∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2))
      ((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1)) := by
  refine Integrable.mono' (((gb_T_integrable B).const_mul (1 / (2 * r))).add (integrable_const (r / 2)))
    (by fun_prop) (ae_of_all _ (fun p => ?_))
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact gb_amgm r _ hr (gb_T_nonneg B p)

lemma gb_upper (B : ℕ) (hB : 1 ≤ B) : batchConst B ≤ √(B : ℝ) := by
  have hBpos : (0:ℝ) < B := by exact_mod_cast hB
  have hr : 0 < √(B:ℝ) := Real.sqrt_pos.mpr hBpos
  have hdiv : (1 / (2 * √(B:ℝ))) * (B:ℝ) = √(B:ℝ) / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_eq_iff (mul_pos two_pos hr).ne']
    linear_combination (-1:ℝ) * Real.mul_self_sqrt hBpos.le
  have hg : ∫ p : (Fin B → ℝ) × (Fin B → ℝ),
      ((1 / (2 * √(B:ℝ))) * (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) + √(B:ℝ) / 2)
        ∂((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin B => gaussianReal 0 1)) = √(B:ℝ) := by
    rw [integral_add ((gb_T_integrable B).const_mul _) (integrable_const _), integral_const_mul,
      gb_E_T]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [hdiv]
    ring
  have hmono : ∫ p : (Fin B → ℝ) × (Fin B → ℝ), √(∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2)
      ∂((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1))
      ≤ ∫ p : (Fin B → ℝ) × (Fin B → ℝ),
        ((1 / (2 * √(B:ℝ))) * (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) + √(B:ℝ) / 2)
        ∂((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin B => gaussianReal 0 1)) :=
    integral_mono_of_nonneg
      (ae_of_all _ (fun p => Real.sqrt_nonneg (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2)))
      (((gb_T_integrable B).const_mul (1 / (2 * √(B:ℝ)))).add (integrable_const (√(B:ℝ) / 2)))
      (ae_of_all _ (fun p => gb_amgm _ _ hr (gb_T_nonneg B p)))
  unfold batchConst
  exact hmono.trans hg.le

lemma gb_lower_first (B : ℕ) (hB : 1 ≤ B) : (2 / π) * √(B : ℝ) ≤ batchConst B := by
  have hBpos : (0:ℝ) < B := by exact_mod_cast hB
  have hr : 0 < √(B:ℝ) := Real.sqrt_pos.mpr hBpos
  have hr2 : (√(B:ℝ)) ^ 2 = B := Real.sq_sqrt hBpos.le
  have hpt : ∀ p : (Fin B → ℝ) × (Fin B → ℝ),
      (∑ b : Fin B, |p.1 b| * |p.2 b|) / √(B:ℝ)
        ≤ √(∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) := by
    intro p
    have hCS : (∑ b : Fin B, |p.1 b| * |p.2 b|) ^ 2
        ≤ (B:ℝ) * ∑ b : Fin B, (|p.1 b| * |p.2 b|) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun b : Fin B => |p.1 b| * |p.2 b|)
      simpa [Finset.card_univ, Fintype.card_fin] using this
    have hsq : ∑ b : Fin B, (|p.1 b| * |p.2 b|) ^ 2 = ∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2 :=
      Finset.sum_congr rfl (fun b _ => by rw [mul_pow, sq_abs, sq_abs])
    rw [hsq] at hCS
    have h2 : ((∑ b : Fin B, |p.1 b| * |p.2 b|) / √(B:ℝ)) ^ 2
        ≤ ∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2 := by
      rw [div_pow, hr2, div_le_iff₀ hBpos, mul_comm]
      exact hCS
    calc (∑ b : Fin B, |p.1 b| * |p.2 b|) / √(B:ℝ)
        ≤ |(∑ b : Fin B, |p.1 b| * |p.2 b|) / √(B:ℝ)| := le_abs_self _
      _ = √(((∑ b : Fin B, |p.1 b| * |p.2 b|) / √(B:ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ √(∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) := Real.sqrt_le_sqrt h2
  have hWint : Integrable (fun p : (Fin B → ℝ) × (Fin B → ℝ) => ∑ b : Fin B, |p.1 b| * |p.2 b|)
      ((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1)) :=
    integrable_finsetSum _ (fun b _ => gb_pair_integrable B b (fun x => |x|) (fun y => |y|)
      gb_L1.abs gb_L1.abs)
  have hlow := integral_mono (hWint.div_const (√(B:ℝ)))
    (gb_sqrt_T_integrable B _ hr) hpt
  refine le_trans (le_of_eq ?_) hlow
  rw [integral_div, integral_finsetSum _ (fun b _ => gb_pair_integrable B b (fun x => |x|)
    (fun y => |y|) gb_L1.abs gb_L1.abs)]
  have hb : ∀ b : Fin B, ∫ p : (Fin B → ℝ) × (Fin B → ℝ), |p.1 b| * |p.2 b|
      ∂((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1)) = 2 / π := fun b => gb_w_int B b
  simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [eq_div_iff hr.ne']
  linear_combination (2 / π) * Real.mul_self_sqrt hBpos.le

private lemma gb_pt (B : ℕ) (hB : 0 < (B:ℝ)) (T : ℝ) (hT : 0 ≤ T) :
    √(B:ℝ) * (3 * T / (2 * B) - T * T / (2 * B ^ 2)) ≤ √T := by
  have hB0 : (B:ℝ) ≠ 0 := hB.ne'
  set r := √(B:ℝ) with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr hB
  have hr0 : r ≠ 0 := hr.ne'
  have hr2 : r ^ 2 = B := Real.sq_sqrt hB.le
  set u := √T / r with hudef
  have hu0 : 0 ≤ u := div_nonneg (Real.sqrt_nonneg _) hr.le
  have hsT : √T = r * u := by rw [hudef]; field_simp
  have hu2 : u ^ 2 = T / B := by
    rw [hudef, div_pow, Real.sq_sqrt hT, hr2]
  have hTu : T = B * u ^ 2 := by
    rw [hu2]; field_simp
  rw [hsT, hTu]
  have e1 : 3 * ((B:ℝ) * u ^ 2) / (2 * B) = 3 * u ^ 2 / 2 := by
    field_simp
  have e2 : ((B:ℝ) * u ^ 2) * ((B:ℝ) * u ^ 2) / (2 * B ^ 2) = u ^ 4 / 2 := by
    field_simp
  rw [e1, e2]
  apply mul_le_mul_of_nonneg_left _ hr.le
  nlinarith [mul_nonneg hu0 (mul_nonneg (sq_nonneg (u - 1)) (by linarith : (0:ℝ) ≤ u + 2))]

lemma gb_lower_second (B : ℕ) (hB : 1 ≤ B) : √(B : ℝ) - 4 / √(B : ℝ) ≤ batchConst B := by
  have hBpos : (0:ℝ) < B := by exact_mod_cast hB
  set r := √(B:ℝ) with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr hBpos
  have hr2 : r ^ 2 = B := Real.sq_sqrt hBpos.le
  have hTT_int : Integrable (fun p : (Fin B → ℝ) × (Fin B → ℝ) =>
      (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) * (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2))
      ((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1)) := by
    simp only [Finset.sum_mul_sum]
    exact integrable_finsetSum _ (fun b _ => integrable_finsetSum _
      (fun b' _ => gb_aa_integrable B b b'))
  have hfun : (fun p : (Fin B → ℝ) × (Fin B → ℝ) =>
      r * (3 * (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) / (2 * B)
        - (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) * (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) / (2 * B ^ 2)))
      = fun p => (r * (3 / (2 * B))) * (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2)
          - (r / (2 * B ^ 2)) * ((∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2)
            * (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2)) := by
    funext p
    ring
  have hL : Integrable (fun p : (Fin B → ℝ) × (Fin B → ℝ) =>
      r * (3 * (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) / (2 * B)
        - (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) * (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) / (2 * B ^ 2)))
      ((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1)) := by
    rw [hfun]
    exact ((gb_T_integrable B).const_mul _).sub (hTT_int.const_mul _)
  have hmono := integral_mono hL (gb_sqrt_T_integrable B r hr)
    (fun p => gb_pt B hBpos _ (gb_T_nonneg B p))
  have hint : ∫ p : (Fin B → ℝ) × (Fin B → ℝ),
      r * (3 * (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) / (2 * B)
        - (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) * (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) / (2 * B ^ 2))
      ∂((Measure.pi fun _ : Fin B => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin B => gaussianReal 0 1))
      = r - 4 / r := by
    rw [hfun, integral_sub ((gb_T_integrable B).const_mul _) (hTT_int.const_mul _),
      integral_const_mul, integral_const_mul, gb_E_T, gb_TT_value]
    have hB' : (B:ℝ) = r ^ 2 := hr2.symm
    rw [hB']
    have hr0 : r ≠ 0 := hr.ne'
    field_simp
    ring
  simp only [batchConst]
  linarith [hmono, hint]

/-- **prop:app-sgd-batch-coefficient** (part (i)) `Muon.SignSGD.prop_app_sgd_batch_coefficient_i`.

cr-2026-10-22. LaTeX statement (verbatim, whole proposition):
For every integer $B\ge1$, the constant \cref{eqn:signsgd-Nb} satisfies
$\mathcal N_1=2/\pi$ and
\begin{equation}\label{eqn:app-sgd-NB}
\max\Big\{\frac2\pi\sqrt B,\ \sqrt B-\frac4{\sqrt B}\Big\}\le\mathcal N_B\le\sqrt B,\qquad
0\le1-\frac{\mathcal N_B}{\sqrt B}\le\frac4B .
\end{equation}
In particular $\mathcal N_B/\sqrt B\to1$ as $B\to\infty$.
-/
theorem prop_app_sgd_batch_coefficient_i : batchConst 1 = 2 / Real.pi := by
  have hint : ∀ p : (Fin 1 → ℝ) × (Fin 1 → ℝ),
      √(∑ b : Fin 1, p.1 b ^ 2 * p.2 b ^ 2) = |p.1 0| * |p.2 0| := by
    intro p
    rw [Fin.sum_univ_one, show p.1 0 ^ 2 * p.2 0 ^ 2 = (|p.1 0| * |p.2 0|) ^ 2 by
      rw [mul_pow, sq_abs, sq_abs], Real.sqrt_sq (by positivity)]
  simp only [batchConst]
  simp_rw [hint]
  rw [gb_w_int 1 0]

/-- **prop:app-sgd-batch-coefficient** (part (ii)) `Muon.SignSGD.prop_app_sgd_batch_coefficient_ii`.

cr-2026-10-22. LaTeX statement (verbatim, whole proposition):
For every integer $B\ge1$, the constant \cref{eqn:signsgd-Nb} satisfies
$\mathcal N_1=2/\pi$ and
\begin{equation}\label{eqn:app-sgd-NB}
\max\Big\{\frac2\pi\sqrt B,\ \sqrt B-\frac4{\sqrt B}\Big\}\le\mathcal N_B\le\sqrt B,\qquad
0\le1-\frac{\mathcal N_B}{\sqrt B}\le\frac4B .
\end{equation}
In particular $\mathcal N_B/\sqrt B\to1$ as $B\to\infty$.
-/
theorem prop_app_sgd_batch_coefficient_ii (B : ℕ) (hB : 1 ≤ B) :
    max ((2 / Real.pi) * Real.sqrt (B : ℝ)) (Real.sqrt (B : ℝ) - 4 / Real.sqrt (B : ℝ))
        ≤ batchConst B ∧
      batchConst B ≤ Real.sqrt (B : ℝ) :=
  ⟨max_le (gb_lower_first B hB) (gb_lower_second B hB), gb_upper B hB⟩

/-- **prop:app-sgd-batch-coefficient** (part (iii))
`Muon.SignSGD.prop_app_sgd_batch_coefficient_iii`.

cr-2026-10-22. LaTeX statement (verbatim, whole proposition):
For every integer $B\ge1$, the constant \cref{eqn:signsgd-Nb} satisfies
$\mathcal N_1=2/\pi$ and
\begin{equation}\label{eqn:app-sgd-NB}
\max\Big\{\frac2\pi\sqrt B,\ \sqrt B-\frac4{\sqrt B}\Big\}\le\mathcal N_B\le\sqrt B,\qquad
0\le1-\frac{\mathcal N_B}{\sqrt B}\le\frac4B .
\end{equation}
In particular $\mathcal N_B/\sqrt B\to1$ as $B\to\infty$.
-/
theorem prop_app_sgd_batch_coefficient_iii (B : ℕ) (hB : 1 ≤ B) :
    0 ≤ 1 - batchConst B / Real.sqrt (B : ℝ) ∧
      1 - batchConst B / Real.sqrt (B : ℝ) ≤ 4 / (B : ℝ) := by
  have hBpos : (0:ℝ) < B := by exact_mod_cast hB
  have hr : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBpos
  have hr2 : (B : ℝ) = Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) :=
    (Real.mul_self_sqrt hBpos.le).symm
  have hup := gb_upper B hB
  have hlow := gb_lower_second B hB
  have hdiv : batchConst B / Real.sqrt (B : ℝ) ≤ 1 := by
    rw [div_le_one hr]
    exact hup
  have e : 1 - 4 / (B : ℝ) = (Real.sqrt (B : ℝ) - 4 / Real.sqrt (B : ℝ)) / Real.sqrt (B : ℝ) := by
    rw [sub_div, div_self hr.ne', div_div, ← hr2]
  have h1 : 1 - 4 / (B : ℝ) ≤ batchConst B / Real.sqrt (B : ℝ) := by
    rw [e]
    exact div_le_div_of_nonneg_right hlow hr.le
  constructor
  · linarith
  · linarith

/-- **prop:app-sgd-batch-coefficient** (part (iv)) `Muon.SignSGD.prop_app_sgd_batch_coefficient_iv`.

cr-2026-10-22. LaTeX statement (verbatim, whole proposition):
For every integer $B\ge1$, the constant \cref{eqn:signsgd-Nb} satisfies
$\mathcal N_1=2/\pi$ and
\begin{equation}\label{eqn:app-sgd-NB}
\max\Big\{\frac2\pi\sqrt B,\ \sqrt B-\frac4{\sqrt B}\Big\}\le\mathcal N_B\le\sqrt B,\qquad
0\le1-\frac{\mathcal N_B}{\sqrt B}\le\frac4B .
\end{equation}
In particular $\mathcal N_B/\sqrt B\to1$ as $B\to\infty$.
-/
theorem prop_app_sgd_batch_coefficient_iv :
    Tendsto (fun B : ℕ => batchConst B / Real.sqrt (B : ℝ)) atTop (𝓝 1) := by
  have hlim : Tendsto (fun B : ℕ => 1 - 4 / (B : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_const_div_atTop_nhds_zero_nat 4)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · refine Filter.eventually_atTop.2 ⟨1, fun B hB => ?_⟩
    have h := (prop_app_sgd_batch_coefficient_iii B hB).2
    linarith
  · refine Filter.eventually_atTop.2 ⟨1, fun B hB => ?_⟩
    have h := (prop_app_sgd_batch_coefficient_iii B hB).1
    linarith

end Muon.SignSGD

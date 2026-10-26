import Muon.SignSGD.CoordinateMoments

/-!
# Appendix I (SignSGD): sign comparison of a normalized batch sum with a Gaussian

Interface for the label `lem:app-sgd-comparison` (one declaration, no parts). Source of record:
snapshot `cr-2026-10-23`, `sections/08-signsgd/section.tex` l. 391–400 (statement) and l. 401–470
(proof, not formalized here). The decay hypothesis `eqn:app-sgd-decay` is taken from
`Muon.SignSGD.sgdPsi` and `Muon.SignSGD.sgdCch` (`CoordinateMoments.lean`, `eqn:app-sgd-psi`); they
are not redefined here.

Encoding choices (all deliberate, none adds a hypothesis the source does not state):

* The law of `Y` is a probability measure `μ` on `ℝ`. The i.i.d. copies `Y_1, …, Y_B` are the
  product
  `Measure.pi (fun _ : Fin B => μ)`, and the expectations of the statement are integrals against it.
* `Y` centered is `∫ y ∂μ = 0`; variance `1` is `ProbabilityTheory.variance (fun y ↦ y) μ = 1`.
  `E Y^4 ≤ 88208` is the lower Lebesgue integral `∫⁻ ofReal (y^4) ∂μ ≤ ofReal 88208`, so that an
  infinite fourth moment is not silently read as `0` (Bochner integrals of non-integrable functions
  are `0`). The bound makes `Y` integrable, so `∫ y ∂μ` and `∫ y^3 ∂μ` are genuine expectations.
* The characteristic function `φ_Y(t) = E e^{itY}` is written as the explicit integral, the same
  form as `sgdCharFunY`. The decay hypothesis is the whole chain of `eqn:app-sgd-decay`, for
  `t ≠ 0`.
* `C_1 = 4√(2π)/(3π)` is `sgdC1`. The universal constant `C_2` is existentially quantified before
  `B`, `μ` and `x`, as the source's order requires.
* `g` is standard Gaussian: `gaussianReal 0 1`. `Real.sign` is used, with `Real.sign 0 = 0`.

Declaration of record: `Muon.SignSGD.lem_app_sgd_comparison`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Muon.SignSGD

/-- The constant `C_1 = 4√(2π)/(3π)` of `lem:app-sgd-comparison` (explicit; the source's
`C_1 ≔ 4√(2π)/(3π)`). -/
noncomputable def sgdC1 : ℝ := 4 * Real.sqrt (2 * Real.pi) / (3 * Real.pi)

section SignComparisonHelpers

open Set


private lemma integrable_exp_cos (ε v : ℝ) (hε : 0 < ε) :
    Integrable (fun u : ℝ => Real.exp (-ε * u) * Real.cos (u * v)) (volume.restrict (Ioi 0)) := by
  have h := integrableOn_exp_mul_Ioi (a := -ε) (by linarith) 0
  refine Integrable.mono' h ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.mul
      (Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u => ?_
    rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    calc _ ≤ Real.exp (-ε * u) * 1 := by gcongr; exact Real.abs_cos_le_one _
      _ = _ := by ring_nf

private lemma integral_exp_cos (ε v : ℝ) (hε : 0 < ε) :
    ∫ u in Ioi (0:ℝ), Real.exp (-ε * u) * Real.cos (u * v) = ε / (ε ^ 2 + v ^ 2) := by
  have hre : ((-(ε:ℂ) + v * Complex.I)).re < 0 := by simp [hε]
  have h := integral_exp_mul_complex_Ioi hre 0
  have hint := integrableOn_exp_mul_complex_Ioi hre 0
  have h2 := integral_re (𝕜 := ℂ) hint
  have h3 : (fun u : ℝ => RCLike.re (Complex.exp ((-(ε:ℂ) + v * Complex.I) * u)))
      = fun u : ℝ => Real.exp (-ε * u) * Real.cos (u * v) := by
    funext u
    simp [Complex.exp_re]
    ring_nf
  rw [h3, h] at h2
  rw [h2]
  have hne : (ε:ℂ)^2 + v^2 ≠ 0 := by
    have : (0:ℝ) < ε^2 + v^2 := by positivity
    exact_mod_cast this.ne'
  simp [Complex.div_re, Complex.normSq]
  field_simp


private lemma integrable_exp_sinc (ε v : ℝ) (hε : 0 < ε) :
    Integrable (fun u : ℝ => Real.exp (-ε * u) * (Real.sin (u * v) / u)) (volume.restrict (Ioi 0)) := by
  have h := (integrableOn_exp_mul_Ioi (a := -ε) (by linarith) 0).const_mul |v|
  refine Integrable.mono' h ?_ ?_
  · exact (by fun_prop : Measurable fun u : ℝ => Real.exp (-ε * u) * (Real.sin (u * v) / u)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have hu : 0 < u := hu
    rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
      abs_div, abs_of_pos hu]
    have : |Real.sin (u * v)| / u ≤ |v| := by
      rw [div_le_iff₀ hu]
      calc _ ≤ |u * v| := Real.abs_sin_le_abs
        _ = _ := by rw [abs_mul, abs_of_pos hu]; ring
    calc _ ≤ Real.exp (-ε * u) * |v| := by gcongr
      _ = _ := by ring

private lemma hasDerivAt_laplace_sinc (ε v : ℝ) (hε : 0 < ε) :
    HasDerivAt (fun w : ℝ => ∫ u in Ioi (0:ℝ), Real.exp (-ε * u) * (Real.sin (u * w) / u))
      (ε / (ε ^ 2 + v ^ 2)) v := by
  rw [← integral_exp_cos ε v hε]
  have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun (w : ℝ) (u : ℝ) => Real.exp (-ε * u) * (Real.sin (u * w) / u))
    (F' := fun (w : ℝ) (u : ℝ) => Real.exp (-ε * u) * Real.cos (u * w))
    (bound := fun u => Real.exp (-ε * u)) (x₀ := v) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun w => ?_) (integrable_exp_sinc ε v hε) ?_ ?_
    (integrableOn_exp_mul_Ioi (a := -ε) (by linarith) 0) ?_)
  · exact this.2
  · exact (by fun_prop : Measurable fun u : ℝ => Real.exp (-ε * u) * (Real.sin (u * w) / u)).aestronglyMeasurable
  · exact (integrable_exp_cos ε v hε).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u w _ => ?_
    rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    calc _ ≤ Real.exp (-ε * u) * 1 := by gcongr; exact Real.abs_cos_le_one _
      _ = _ := by ring
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu w _ => ?_)
    have hu : 0 < u := hu
    have h1 : HasDerivAt (fun w : ℝ => Real.sin (u * w)) (Real.cos (u * w) * u) w := by
      have := (Real.hasDerivAt_sin (u * w)).comp w ((hasDerivAt_id w).const_mul u)
      exact this.congr_deriv (by simp [mul_comm])
    have h2 := (h1.div_const u).const_mul (Real.exp (-ε * u))
    refine h2.congr_deriv ?_
    field_simp

private lemma laplace_sinc (ε v : ℝ) (hε : 0 < ε) :
    ∫ u in Ioi (0:ℝ), Real.exp (-ε * u) * (Real.sin (u * v) / u) = Real.arctan (v / ε) := by
  set G : ℝ → ℝ := fun w => (∫ u in Ioi (0:ℝ), Real.exp (-ε * u) * (Real.sin (u * w) / u)) - Real.arctan (w / ε) with hG
  have hd : ∀ w, HasDerivAt G 0 w := by
    intro w
    have h1 := hasDerivAt_laplace_sinc ε w hε
    have h2 : HasDerivAt (fun w : ℝ => Real.arctan (w / ε)) (ε / (ε ^ 2 + w ^ 2)) w := by
      have := (Real.hasDerivAt_arctan (w / ε)).comp w ((hasDerivAt_id w).div_const ε)
      refine this.congr_deriv ?_
      have hε' : ε ≠ 0 := hε.ne'
      field_simp
    exact (h1.sub h2).congr_deriv (sub_self _)
  have hc := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt) (fun w => (hd w).deriv) v 0
  have h0 : G 0 = 0 := by simp [hG]
  have : G v = 0 := by rw [hc, h0]
  simpa [hG, sub_eq_zero] using this

private lemma arctan_hfi {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (hint : Integrable X P)
    (x ε : ℝ) (hε : 0 < ε) :
    Integrable (Function.uncurry fun (ω : Ω) (u : ℝ) =>
      Real.exp (-ε * u) * (Real.sin (u * (X ω + x)) / u)) (P.prod (volume.restrict (Ioi 0))) := by
  have hb : Integrable (fun z : Ω × ℝ => (|X z.1| + |x|) * Real.exp (-ε * z.2))
      (P.prod (volume.restrict (Ioi 0))) :=
    Integrable.mul_prod (f := fun ω => |X ω| + |x|) (g := fun u => Real.exp (-ε * u))
      (hint.abs.add (integrable_const _)) (integrableOn_exp_mul_Ioi (a := -ε) (by linarith) 0)
  refine Integrable.mono' hb ?_ ?_
  · exact (by fun_prop : Measurable fun z : Ω × ℝ =>
      Real.exp (-ε * z.2) * (Real.sin (z.2 * (X z.1 + x)) / z.2)).aestronglyMeasurable
  · have hae : ∀ᵐ u ∂(volume.restrict (Ioi (0:ℝ))), 0 < u :=
      (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => hu)
    have hae2 : ∀ᵐ z ∂(P.prod (volume.restrict (Ioi (0:ℝ)))), 0 < z.2 :=
      (Measure.quasiMeasurePreserving_snd).ae hae
    filter_upwards [hae2] with z hz
    simp only [Function.uncurry]
    rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
      abs_div, abs_of_pos hz]
    have : |Real.sin (z.2 * (X z.1 + x))| / z.2 ≤ |X z.1| + |x| := by
      rw [div_le_iff₀ hz]
      calc _ ≤ |z.2 * (X z.1 + x)| := Real.abs_sin_le_abs
        _ = z.2 * |X z.1 + x| := by rw [abs_mul, abs_of_pos hz]
        _ ≤ _ := by rw [mul_comm]; gcongr; exact abs_add_le _ _
    calc _ ≤ Real.exp (-ε * z.2) * (|X z.1| + |x|) := by gcongr
      _ = _ := by ring

private lemma arctan_inner {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (x ε u : ℝ) (_hu : 0 < u) :
    ∫ ω, Real.exp (-ε * u) * (Real.sin (u * (X ω + x)) / u) ∂P =
      Real.exp (-ε * u) / u *
        (Complex.exp ((u:ℂ) * x * Complex.I) * ∫ ω, Complex.exp ((u:ℂ) * Complex.I * (X ω : ℂ)) ∂P).im := by
  have e1 : ∀ ω, Real.exp (-ε * u) * (Real.sin (u * (X ω + x)) / u) =
      Real.exp (-ε * u) / u * Real.sin (u * (X ω + x)) := fun ω => by ring
  simp_rw [e1]
  rw [integral_const_mul]
  congr 1
  have e2 : ∀ ω, Real.sin (u * (X ω + x)) =
      (Complex.exp ((u:ℂ) * x * Complex.I) * Complex.exp ((u:ℂ) * Complex.I * (X ω : ℂ))).im := by
    intro ω
    rw [← Complex.exp_add]
    have : (u:ℂ) * x * Complex.I + (u:ℂ) * Complex.I * (X ω : ℂ) = ((u * (X ω + x) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_ofReal_mul_I_im]
  simp_rw [e2]
  have hci : Integrable (fun ω => Complex.exp ((u:ℂ) * Complex.I * (X ω : ℂ))) P := by
    refine Integrable.of_bound (C := 1) (by fun_prop) (Filter.Eventually.of_forall fun ω => ?_)
    have : (u:ℂ) * Complex.I * (X ω : ℂ) = ((u * X ω : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hci2 := hci.const_mul (Complex.exp ((u:ℂ) * x * Complex.I))
  have := integral_im (𝕜 := ℂ) hci2
  rw [integral_const_mul] at this
  simpa using this

private lemma arctan_expect_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (hint : Integrable X P)
    (x ε : ℝ) (hε : 0 < ε) :
    Integrable (fun u : ℝ => Real.exp (-ε * u) / u *
        (Complex.exp ((u:ℂ) * x * Complex.I) * ∫ ω, Complex.exp ((u:ℂ) * Complex.I * (X ω : ℂ)) ∂P).im)
        (volume.restrict (Ioi (0:ℝ))) ∧
    ∫ ω, Real.arctan ((X ω + x) / ε) ∂P =
      ∫ u in Ioi (0:ℝ), Real.exp (-ε * u) / u *
        (Complex.exp ((u:ℂ) * x * Complex.I) * ∫ ω, Complex.exp ((u:ℂ) * Complex.I * (X ω : ℂ)) ∂P).im := by
  have h1 : ∀ ω, Real.arctan ((X ω + x) / ε) =
      ∫ u in Ioi (0:ℝ), Real.exp (-ε * u) * (Real.sin (u * (X ω + x)) / u) :=
    fun ω => (laplace_sinc ε _ hε).symm
  have hfi := arctan_hfi P X hX hint x ε hε
  have hae : ∀ᵐ u ∂(volume.restrict (Ioi (0:ℝ))), 0 < u :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => hu)
  constructor
  · refine (hfi.integral_prod_right).congr ?_
    filter_upwards [hae] with u hu
    exact arctan_inner P X hX x ε u hu
  · simp_rw [h1]
    rw [integral_integral_swap hfi]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    exact arctan_inner P X hX x ε u hu

private lemma tendsto_arctan_sign (v : ℝ) :
    Filter.Tendsto (fun ε : ℝ => 2 / Real.pi * Real.arctan (v / ε)) (nhdsWithin 0 (Ioi 0))
      (nhds (Real.sign v)) := by
  have hpi := Real.pi_pos
  rcases lt_trichotomy v 0 with h | h | h
  · rw [Real.sign_of_neg h]
    have h1 : Filter.Tendsto (fun ε : ℝ => v / ε) (nhdsWithin 0 (Ioi 0)) Filter.atBot := by
      have := tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
      have := this.const_mul_atTop_of_neg h
      simpa [div_eq_mul_inv] using this
    have h2 := ((Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp h1)
    have h3 := (h2.const_mul (2 / Real.pi))
    have e : 2 / Real.pi * -(Real.pi / 2) = -1 := by field_simp
    rw [e] at h3
    exact h3
  · subst h; simp
  · rw [Real.sign_of_pos h]
    have h1 : Filter.Tendsto (fun ε : ℝ => v / ε) (nhdsWithin 0 (Ioi 0)) Filter.atTop := by
      have := tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
      have := this.const_mul_atTop h
      simpa [div_eq_mul_inv] using this
    have h2 := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1)
    have h3 := (h2.const_mul (2 / Real.pi))
    have e : 2 / Real.pi * (Real.pi / 2) = 1 := by field_simp
    rw [e] at h3
    exact h3

private lemma tendsto_expect_sign {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (x : ℝ) :
    Filter.Tendsto (fun ε : ℝ => 2 / Real.pi * ∫ ω, Real.arctan ((X ω + x) / ε) ∂P)
      (nhdsWithin 0 (Ioi 0)) (nhds (∫ ω, Real.sign (X ω + x) ∂P)) := by
  have hpi := Real.pi_pos
  simp_rw [← integral_const_mul]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun ε =>
      (by fun_prop : Measurable fun ω => 2 / Real.pi * Real.arctan ((X ω + x) / ε)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun ω => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 / Real.pi)]
    have := abs_le.2 ⟨(Real.neg_pi_div_two_lt_arctan ((X ω + x) / ε)).le, (Real.arctan_lt_pi_div_two ((X ω + x) / ε)).le⟩
    calc _ ≤ 2 / Real.pi * (Real.pi / 2) := by gcongr
      _ = 1 := by field_simp
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun ω => tendsto_arctan_sign _

/-- Generic comparison of expected signs through characteristic functions. -/
private lemma sign_comparison_generic {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (X₁ : Ω₁ → ℝ) (X₂ : Ω₂ → ℝ) (h₁ : Measurable X₁) (h₂ : Measurable X₂)
    (i₁ : Integrable X₁ P₁) (i₂ : Integrable X₂ P₂) (H : ℝ → ℝ)
    (hH : IntegrableOn H (Ioi 0))
    (hbd : ∀ u : ℝ, 0 < u →
      ‖(∫ ω, Complex.exp ((u:ℂ) * Complex.I * (X₁ ω : ℂ)) ∂P₁) -
        ∫ ω, Complex.exp ((u:ℂ) * Complex.I * (X₂ ω : ℂ)) ∂P₂‖ / u ≤ H u) (x : ℝ) :
    |∫ ω, Real.sign (X₁ ω + x) ∂P₁ - ∫ ω, Real.sign (X₂ ω + x) ∂P₂|
      ≤ 2 / Real.pi * ∫ u in Ioi (0:ℝ), H u := by
  have hpi := Real.pi_pos
  have hlim := ((tendsto_expect_sign P₁ X₁ h₁ x).sub (tendsto_expect_sign P₂ X₂ h₂ x)).abs
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : 0 < ε := hε
  obtain ⟨hi1, he1⟩ := arctan_expect_eq P₁ X₁ h₁ i₁ x ε hε
  obtain ⟨hi2, he2⟩ := arctan_expect_eq P₂ X₂ h₂ i₂ x ε hε
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 / Real.pi)]
  gcongr
  rw [he1, he2, ← integral_sub hi1 hi2, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hH ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
  have hu : 0 < u := hu
  refine le_trans ?_ (hbd u hu)
  rw [← mul_sub, ← Complex.sub_im, ← mul_sub, norm_mul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < Real.exp (-ε * u) / u)]
  generalize (∫ (ω : Ω₁), Complex.exp (↑u * Complex.I * ↑(X₁ ω)) ∂P₁ -
              ∫ (ω : Ω₂), Complex.exp (↑u * Complex.I * ↑(X₂ ω)) ∂P₂) = Δ
  have hn : ‖(Complex.exp ((u:ℂ) * x * Complex.I) * Δ).im‖ ≤ ‖Δ‖ := by
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul]
    have : (u:ℂ) * x * Complex.I = ((u * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I, one_mul]
  have he : Real.exp (-ε * u) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  calc Real.exp (-ε * u) / u * ‖(Complex.exp ((u:ℂ) * x * Complex.I) * Δ).im‖
      ≤ 1 / u * ‖Δ‖ := by gcongr
    _ = ‖Δ‖ / u := by ring




/-- Elementary bound: derivative bound `K |s|^m` gives value bound `K |x|^(m+1)`. -/
private lemma norm_le_of_deriv_le (f f' : ℝ → ℂ) (hf : ∀ s, HasDerivAt f (f' s) s) (h0 : f 0 = 0)
    (K : ℝ) (hK0 : 0 ≤ K) (m : ℕ) (hK : ∀ s, ‖f' s‖ ≤ K * |s| ^ m) (x : ℝ) :
    ‖f x‖ ≤ K * |x| ^ (m + 1) := by
  have hconv : Convex ℝ (uIcc (0:ℝ) x) := convex_uIcc 0 x
  have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f') (C := K * |x| ^ m)
    (fun s _ => (hf s).hasDerivWithinAt) (fun s hs => ?_) (left_mem_uIcc) (right_mem_uIcc)
  · simp only [h0, sub_zero, Real.norm_eq_abs] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  · refine (hK s).trans ?_
    have : |s| ≤ |x| := by
      have hx1 := le_abs_self x
      have hx2 := neg_le_abs x
      have hx3 := abs_nonneg x
      rcases mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact abs_le.2 ⟨by linarith, by linarith⟩
      · exact abs_le.2 ⟨by linarith, by linarith⟩
    gcongr

/-- Taylor remainders of `e^{ix}`. -/
private noncomputable def tay1 (x : ℝ) : ℂ := Complex.exp (x * Complex.I) - 1
private noncomputable def tay2 (x : ℝ) : ℂ := tay1 x - x * Complex.I
private noncomputable def tay3 (x : ℝ) : ℂ := tay2 x + (x:ℂ)^2 / 2
private noncomputable def tay4 (x : ℝ) : ℂ := tay3 x + (x:ℂ)^3 * Complex.I / 6

private lemma hasDerivAt_cexp_real (s : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp ((x:ℂ) * Complex.I)) (Complex.I * Complex.exp ((s:ℂ) * Complex.I)) s := by
  have h1 : HasDerivAt (fun x : ℝ => (x:ℂ) * Complex.I) Complex.I s := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const Complex.I
  have := (Complex.hasDerivAt_exp ((s:ℂ) * Complex.I)).comp s h1
  exact this.congr_deriv (by ring)

private lemma tay1_deriv (s : ℝ) : HasDerivAt tay1 (Complex.I * Complex.exp (s * Complex.I)) s := by
  exact (hasDerivAt_cexp_real s).sub_const 1

private lemma tay2_deriv (s : ℝ) : HasDerivAt tay2 (Complex.I * tay1 s) s := by
  have h : HasDerivAt (fun x : ℝ => (x:ℂ) * Complex.I) Complex.I s := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const Complex.I
  have := (tay1_deriv s).sub h
  refine this.congr_deriv ?_
  simp only [tay1]; ring

private lemma tay3_deriv (s : ℝ) : HasDerivAt tay3 (Complex.I * tay2 s) s := by
  have h : HasDerivAt (fun x : ℝ => (x:ℂ)^2 / 2) (s:ℂ) s := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := s)).pow 2).div_const 2
    refine this.congr_deriv ?_
    simp
  have := (tay2_deriv s).add h
  refine this.congr_deriv ?_
  simp only [tay2, tay1]; ring_nf; simp only [Complex.I_sq]; ring

private lemma tay4_deriv (s : ℝ) : HasDerivAt tay4 (Complex.I * tay3 s) s := by
  have h : HasDerivAt (fun x : ℝ => (x:ℂ)^3 * Complex.I / 6) ((s:ℂ)^2 * Complex.I / 2) s := by
    have := (((Complex.ofRealCLM.hasDerivAt (x := s)).pow 3).mul_const Complex.I).div_const 6
    refine this.congr_deriv ?_
    simp; ring
  have := (tay3_deriv s).add h
  refine this.congr_deriv ?_
  simp only [tay3, tay2, tay1]; ring

private lemma tay1_bound (x : ℝ) : ‖tay1 x‖ ≤ |x| := by
  have := norm_le_of_deriv_le tay1 _ tay1_deriv (by simp [tay1]) 1 zero_le_one 0 (fun s => by
    rw [norm_mul, Complex.norm_I, one_mul]
    simp [Complex.norm_exp_ofReal_mul_I]) x
  simpa using this

private lemma tay2_bound (x : ℝ) : ‖tay2 x‖ ≤ |x| ^ 2 := by
  have := norm_le_of_deriv_le tay2 _ tay2_deriv (by simp [tay2, tay1]) 1 zero_le_one 1 (fun s => by
    rw [norm_mul, Complex.norm_I, one_mul]
    simpa using tay1_bound s) x
  simpa using this

private lemma tay3_bound (x : ℝ) : ‖tay3 x‖ ≤ |x| ^ 3 := by
  have := norm_le_of_deriv_le tay3 _ tay3_deriv (by simp [tay3, tay2, tay1]) 1 zero_le_one 2 (fun s => by
    rw [norm_mul, Complex.norm_I, one_mul]
    simpa using tay2_bound s) x
  simpa using this

private lemma tay4_bound (x : ℝ) : ‖tay4 x‖ ≤ |x| ^ 4 := by
  have := norm_le_of_deriv_le tay4 _ tay4_deriv (by simp [tay4, tay3, tay2, tay1]) 1 zero_le_one 3 (fun s => by
    rw [norm_mul, Complex.norm_I, one_mul]
    simpa using tay3_bound s) x
  simpa using this

private lemma exp_neg_upper (s : ℝ) (hs : 0 ≤ s) : Real.exp (-s) ≤ 1 - s + s ^ 2 / 2 := by
  let h : ℝ → ℝ := fun s => 1 - s + s ^ 2 / 2 - Real.exp (-s)
  have hd : ∀ s, HasDerivAt h (-1 + s + Real.exp (-s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-s)) s := by
      exact ((Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun s : ℝ => 1 - s + s ^ 2 / 2) (-1 + s) s := by
      have := (((hasDerivAt_id s).const_sub 1).add (((hasDerivAt_id s).pow 2).div_const 2))
      refine this.congr_deriv ?_
      simp
    refine (h2.sub h1).congr_deriv ?_
    ring
  have hmono : MonotoneOn h (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) (fun x _ => ?_)
    rw [(hd x).deriv]
    have := Real.add_one_le_exp (-x)
    linarith
  have := hmono (show (0:ℝ) ∈ Ici 0 by simp) (show s ∈ Ici 0 from hs) hs
  simp only [h] at this
  simp at this
  linarith


section phi
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- The integrability of the moments from the fourth. -/
private lemma moments_integrable (hm4 : Integrable (fun y : ℝ => y ^ 4) μ) :
    Integrable (fun y : ℝ => y) μ ∧ Integrable (fun y : ℝ => y ^ 2) μ ∧
      Integrable (fun y : ℝ => y ^ 3) μ ∧ Integrable (fun y : ℝ => |y| ^ 3) μ := by
  have hb : Integrable (fun y : ℝ => 1 + y ^ 4) μ := (integrable_const _).add hm4
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine hb.mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
    simp only [Real.norm_eq_abs]
    have h4 : |y| ^ 4 = y ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (|y| ^ 2 - 1 / 2), sq_nonneg (|y| - 1 / 2)]
  · refine hb.mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg y)]
    nlinarith [sq_nonneg (y ^ 2 - 1 / 2)]
  · refine hb.mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
    simp only [Real.norm_eq_abs]
    have h4 : |y| ^ 4 = y ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
    rw [abs_pow]
    by_cases h : |y| ≤ 1
    · have := pow_le_one₀ (abs_nonneg y) h (n := 3)
      nlinarith [pow_nonneg (abs_nonneg y) 4]
    · have h' : 1 ≤ |y| := (not_le.1 h).le
      have := pow_le_pow_right₀ h' (show 3 ≤ 4 by norm_num)
      nlinarith
  · refine hb.mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
    simp only [Real.norm_eq_abs]
    have h4 : |y| ^ 4 = y ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
    rw [abs_pow, abs_abs]
    by_cases h : |y| ≤ 1
    · have := pow_le_one₀ (abs_nonneg y) h (n := 3)
      nlinarith [pow_nonneg (abs_nonneg y) 4]
    · have h' : 1 ≤ |y| := (not_le.1 h).le
      have := pow_le_pow_right₀ h' (show 3 ≤ 4 by norm_num)
      nlinarith

private lemma cexp_integrable (t : ℝ) :
    Integrable (fun y : ℝ => Complex.exp ((t:ℂ) * Complex.I * (y:ℂ))) μ := by
  refine Integrable.of_bound (C := 1) (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
  have : (t:ℂ) * Complex.I * (y:ℂ) = ((t * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

private lemma cpoly_integral (hI : ∀ k : ℕ, k ≤ 3 → Integrable (fun y : ℝ => y ^ k) μ) (t : ℝ) :
    Integrable (fun y : ℝ => (t:ℂ) * Complex.I * (y:ℂ)) μ ∧
    Integrable (fun y : ℝ => (((y ^ 2 : ℝ) : ℂ))) μ ∧
    Integrable (fun y : ℝ => (((y ^ 3 : ℝ) : ℂ))) μ := by
  refine ⟨?_, ?_, ?_⟩
  · have := ((hI 1 (by norm_num)).ofReal (𝕜 := ℂ)).const_mul ((t:ℂ) * Complex.I)
    simpa using this
  · exact (hI 2 (by norm_num)).ofReal (𝕜 := ℂ)
  · exact (hI 3 (by norm_num)).ofReal (𝕜 := ℂ)

private lemma tay3_integrable (hm4 : Integrable (fun y : ℝ => y ^ 4) μ) (t : ℝ) :
    Integrable (fun y : ℝ => tay3 (t * y)) μ := by
  obtain ⟨i1, i2, i3, -⟩ := moments_integrable μ hm4
  have hI : ∀ k : ℕ, k ≤ 3 → Integrable (fun y : ℝ => y ^ k) μ := by
    intro k hk
    interval_cases k
    · simp
    · simpa using i1
    · exact i2
    · exact i3
  obtain ⟨c1, c2, c3⟩ := cpoly_integral μ hI t
  have hpt : ∀ y : ℝ, Complex.exp ((t:ℂ) * Complex.I * (y:ℂ)) = tay3 (t * y) +
      (1 + (t:ℂ) * Complex.I * (y:ℂ) - ((t:ℂ) ^ 2 / 2) * (((y ^ 2 : ℝ) : ℂ))) := by
    intro y
    simp only [tay3, tay2, tay1]
    push_cast
    ring_nf
  have hA : Integrable (fun y : ℝ => (1:ℂ) + (t:ℂ) * Complex.I * (y:ℂ)) μ :=
    (integrable_const (1:ℂ)).add c1
  have hpoly : Integrable (fun y : ℝ => (1:ℂ) + (t:ℂ) * Complex.I * (y:ℂ) -
      ((t:ℂ) ^ 2 / 2) * (((y ^ 2 : ℝ) : ℂ))) μ :=
    hA.sub (c2.const_mul ((t:ℂ) ^ 2 / 2))
  have := (cexp_integrable μ t).sub hpoly
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.sub_apply]
  rw [hpt y]; ring

private lemma phi_eq3 (hm4 : Integrable (fun y : ℝ => y ^ 4) μ)
    (h1 : ∫ y, y ∂μ = 0) (h2 : ∫ y, y ^ 2 ∂μ = 1) (t : ℝ) :
    (∫ y, Complex.exp ((t:ℂ) * Complex.I * (y:ℂ)) ∂μ) =
      ∫ y, tay3 (t * y) ∂μ + 1 - (t:ℂ) ^ 2 / 2 := by
  obtain ⟨i1, i2, i3, -⟩ := moments_integrable μ hm4
  have hI : ∀ k : ℕ, k ≤ 3 → Integrable (fun y : ℝ => y ^ k) μ := by
    intro k hk
    interval_cases k
    · simp
    · simpa using i1
    · exact i2
    · exact i3
  obtain ⟨c1, c2, c3⟩ := cpoly_integral μ hI t
  have hpt : ∀ y : ℝ, Complex.exp ((t:ℂ) * Complex.I * (y:ℂ)) = tay3 (t * y) +
      (1 + (t:ℂ) * Complex.I * (y:ℂ) - ((t:ℂ) ^ 2 / 2) * (((y ^ 2 : ℝ) : ℂ))) := by
    intro y
    simp only [tay3, tay2, tay1]
    push_cast
    ring_nf
  have hA : Integrable (fun y : ℝ => (1:ℂ) + (t:ℂ) * Complex.I * (y:ℂ)) μ :=
    (integrable_const (1:ℂ)).add c1
  have hpoly : Integrable (fun y : ℝ => (1:ℂ) + (t:ℂ) * Complex.I * (y:ℂ) -
      ((t:ℂ) ^ 2 / 2) * (((y ^ 2 : ℝ) : ℂ))) μ :=
    hA.sub (c2.const_mul ((t:ℂ) ^ 2 / 2))
  have hf3 : Integrable (fun y : ℝ => tay3 (t * y)) μ := by
    have := (cexp_integrable μ t).sub hpoly
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    rw [hpt y]; ring
  simp_rw [hpt]
  rw [integral_add hf3 hpoly, integral_sub hA (c2.const_mul _),
    integral_add (integrable_const _) c1, integral_const_mul]
  have e1 : ∫ a : ℝ, (a:ℂ) ∂μ = 0 := by
    have := integral_complex_ofReal (μ := μ) (f := fun a : ℝ => a)
    rw [this, h1]; simp
  have e2 : ∫ a : ℝ, (((a ^ 2 : ℝ) : ℂ)) ∂μ = 1 := by
    have := integral_complex_ofReal (μ := μ) (f := fun a : ℝ => a ^ 2)
    rw [this, h2]; simp
  rw [integral_const_mul, e1, e2]
  simp
  ring

private lemma phi_eq4 (hm4 : Integrable (fun y : ℝ => y ^ 4) μ)
    (h1 : ∫ y, y ∂μ = 0) (h2 : ∫ y, y ^ 2 ∂μ = 1) (t : ℝ) :
    (∫ y, Complex.exp ((t:ℂ) * Complex.I * (y:ℂ)) ∂μ) =
      ∫ y, tay4 (t * y) ∂μ + 1 - (t:ℂ) ^ 2 / 2 - Complex.I * (t:ℂ) ^ 3 * (∫ y, y ^ 3 ∂μ : ℝ) / 6 := by
  obtain ⟨i1, i2, i3, -⟩ := moments_integrable μ hm4
  have h3 := phi_eq3 μ hm4 h1 h2 t
  have hf3 := tay3_integrable μ hm4 t
  have hc3 : Integrable (fun y : ℝ => (((y ^ 3 : ℝ) : ℂ))) μ := i3.ofReal (𝕜 := ℂ)
  have hg : Integrable (fun y : ℝ => (t:ℂ) ^ 3 * Complex.I / 6 * (((y ^ 3 : ℝ) : ℂ))) μ :=
    hc3.const_mul _
  have hpt : ∀ y : ℝ, tay4 (t * y) = tay3 (t * y) + (t:ℂ) ^ 3 * Complex.I / 6 * (((y ^ 3 : ℝ) : ℂ)) := by
    intro y
    simp only [tay4]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_add hf3 hg, integral_const_mul, integral_complex_ofReal (μ := μ) (f := fun a : ℝ => a ^ 3)] at *
  rw [h3]
  ring


private lemma phi_bound3 (hm4 : Integrable (fun y : ℝ => y ^ 4) μ)
    (h1 : ∫ y, y ∂μ = 0) (h2 : ∫ y, y ^ 2 ∂μ = 1) (t : ℝ) :
    ‖(∫ y, Complex.exp ((t:ℂ) * Complex.I * (y:ℂ)) ∂μ) - (1 - (t:ℂ) ^ 2 / 2)‖ ≤
      |t| ^ 3 * ((1 + ∫ y, y ^ 4 ∂μ) / 2) := by
  obtain ⟨i1, i2, i3, -⟩ := moments_integrable μ hm4
  rw [phi_eq3 μ hm4 h1 h2 t]
  have : ∫ y, tay3 (t * y) ∂μ + 1 - (t:ℂ) ^ 2 / 2 - (1 - (t:ℂ) ^ 2 / 2) = ∫ y, tay3 (t * y) ∂μ := by ring
  rw [this]
  have hg : Integrable (fun y : ℝ => |t| ^ 3 * ((y ^ 2 + y ^ 4) / 2)) μ :=
    ((i2.add hm4).div_const 2).const_mul _
  refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun y => ?_)).trans_eq ?_
  · refine (tay3_bound (t * y)).trans ?_
    rw [abs_mul, mul_pow]
    gcongr
    have h4 : |y| ^ 4 = y ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
    have h2' : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith [sq_nonneg (|y| ^ 2 - |y|), abs_nonneg y]
  · rw [integral_const_mul, integral_div, integral_add i2 hm4, h2]

private lemma phi_bound4 (hm4 : Integrable (fun y : ℝ => y ^ 4) μ)
    (h1 : ∫ y, y ∂μ = 0) (h2 : ∫ y, y ^ 2 ∂μ = 1) (t : ℝ) :
    ‖(∫ y, Complex.exp ((t:ℂ) * Complex.I * (y:ℂ)) ∂μ) - Complex.exp (-(t:ℂ) ^ 2 / 2)‖ ≤
      |∫ y, y ^ 3 ∂μ| * |t| ^ 3 / 6 + (∫ y, y ^ 4 ∂μ + 1 / 8) * t ^ 4 := by
  obtain ⟨i1, i2, i3, -⟩ := moments_integrable μ hm4
  rw [phi_eq4 μ hm4 h1 h2 t]
  set κ : ℝ := ∫ y, y ^ 3 ∂μ with hκ
  set R : ℂ := ∫ y, tay4 (t * y) ∂μ with hR
  set E : ℂ := Complex.exp (-(t:ℂ) ^ 2 / 2) with hE
  have hRb : ‖R‖ ≤ (∫ y, y ^ 4 ∂μ) * t ^ 4 := by
    have hg : Integrable (fun y : ℝ => t ^ 4 * y ^ 4) μ := hm4.const_mul _
    refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun y => ?_)).trans_eq ?_
    · refine (tay4_bound (t * y)).trans_eq ?_
      rw [abs_mul, mul_pow]
      have h4 : |y| ^ 4 = y ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
      have h4' : |t| ^ 4 = t ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
      rw [h4, h4']
    · rw [integral_const_mul]; ring
  have hEb : ‖E - (1 - (t:ℂ) ^ 2 / 2)‖ ≤ t ^ 4 / 8 := by
    have e : E = ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) := by
      rw [hE]; push_cast; ring_nf
    have e2 : E - (1 - (t:ℂ) ^ 2 / 2) = ((Real.exp (-(t ^ 2 / 2)) - (1 - t ^ 2 / 2) : ℝ) : ℂ) := by
      rw [e]; push_cast; ring
    rw [e2, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have hs : 0 ≤ t ^ 2 / 2 := by positivity
    have u := exp_neg_upper (t ^ 2 / 2) hs
    have l := Real.add_one_le_exp (-(t ^ 2 / 2))
    constructor <;> nlinarith
  have hdecomp : R + 1 - (t:ℂ) ^ 2 / 2 - Complex.I * (t:ℂ) ^ 3 * (κ : ℂ) / 6 - E =
      R - Complex.I * (t:ℂ) ^ 3 * (κ : ℂ) / 6 - (E - (1 - (t:ℂ) ^ 2 / 2)) := by ring
  rw [hdecomp]
  calc ‖R - Complex.I * (t:ℂ) ^ 3 * (κ : ℂ) / 6 - (E - (1 - (t:ℂ) ^ 2 / 2))‖
      ≤ ‖R‖ + ‖Complex.I * (t:ℂ) ^ 3 * (κ : ℂ) / 6‖ + ‖E - (1 - (t:ℂ) ^ 2 / 2)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ (∫ y, y ^ 4 ∂μ) * t ^ 4 + |κ| * |t| ^ 3 / 6 + t ^ 4 / 8 := by
        gcongr
        rw [norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, norm_pow, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        simp
        rw [mul_comm]
    _ = _ := by ring

end phi




private lemma pow_sub_pow_le (a b : ℂ) (r : ℝ) (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ (n + 1) * ‖a - b‖ * r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr : 0 ≤ r := (norm_nonneg a).trans ha
    have e : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) = a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖a‖ * ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ r * ((n + 1) * ‖a - b‖ * r ^ n) :=
      mul_le_mul ha ih (norm_nonneg _) hr
    have h2 : ‖a - b‖ * ‖b‖ ^ (n + 1) ≤ ‖a - b‖ * r ^ (n + 1) := by
      gcongr
    push_cast
    have h3 : r * ((n + 1) * ‖a - b‖ * r ^ n) = (n + 1) * ‖a - b‖ * r ^ (n + 1) := by ring
    nlinarith [h1, h2, h3]

private lemma L_small (φ : ℝ → ℂ) (δ A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (B : ℕ) (hB : 4 ≤ B)
    (hnear : ∀ t : ℝ, |t| ≤ δ → ‖φ t‖ ≤ Real.exp (-t ^ 2 / 4))
    (htay : ∀ t : ℝ, ‖φ t - Complex.exp (-(t:ℂ) ^ 2 / 2)‖ ≤ A * |t| ^ 3 / 6 + C * t ^ 4)
    (u : ℝ) (hu : 0 < u) (huδ : u ≤ δ * Real.sqrt B) :
    ‖φ (u / Real.sqrt B) ^ B - Complex.exp (-(u:ℂ) ^ 2 / 2)‖ / u ≤
      Real.exp (-u ^ 2 / 8) * (A * u ^ 2 / (6 * Real.sqrt B) + C * u ^ 3 / B) := by
  have hBpos : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  set q := Real.sqrt B with hq
  have hqpos : 0 < q := Real.sqrt_pos.2 hBpos
  have hq2 : q ^ 2 = B := Real.sq_sqrt hBpos.le
  set s := u / q with hs
  have hspos : 0 < s := div_pos hu hqpos
  have hsδ : |s| ≤ δ := by
    rw [abs_of_pos hspos, hs, div_le_iff₀ hqpos]; exact huδ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, B = n + 1 := ⟨B - 1, by omega⟩
  have hn3 : 3 ≤ n := by omega
  set a := φ s with ha
  set b : ℂ := Complex.exp (-(s:ℂ) ^ 2 / 2) with hb
  have hbn : ‖b‖ = Real.exp (-s ^ 2 / 2) := by
    rw [hb, Complex.norm_exp]
    congr 1
    have : (-(s:ℂ) ^ 2 / 2) = ((-s ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  have hs2 : s ^ 2 * B = u ^ 2 := by
    rw [hs, div_pow, hq2]; field_simp
  set r := Real.exp (-s ^ 2 / 4) with hr
  have har : ‖a‖ ≤ r := hnear s hsδ
  have hbr : ‖b‖ ≤ r := by
    rw [hbn, hr]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg s])
  have hbB : b ^ B = Complex.exp (-(u:ℂ) ^ 2 / 2) := by
    rw [hb, ← Complex.exp_nat_mul]
    congr 1
    have : (s:ℂ) ^ 2 * B = (u:ℂ) ^ 2 := by exact_mod_cast hs2
    rw [← this]; ring
  have htel := pow_sub_pow_le a b r har hbr n
  rw [← hn] at htel
  have hab : ‖a - b‖ ≤ A * |s| ^ 3 / 6 + C * s ^ 4 := htay s
  have hrn : r ^ n ≤ Real.exp (-u ^ 2 / 8) := by
    rw [hr, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have hnB : (n:ℝ) + 1 = B := by exact_mod_cast hn.symm
    have : (n:ℝ) * (-s ^ 2 / 4) = -(s ^ 2 * B) * (n / B) / 4 := by
      rw [← hnB]; field_simp
    rw [this, hs2]
    have hfrac : (3:ℝ) / 4 ≤ n / B := by
      rw [div_le_div_iff₀ (by norm_num) hBpos]
      rw [← hnB]
      have : (4:ℝ) ≤ n + 1 := by rw [hnB]; exact_mod_cast hB
      nlinarith
    nlinarith [sq_nonneg u]
  have hBeq : (B:ℝ) * ‖a - b‖ ≤ A * u ^ 3 / (6 * q) + C * u ^ 4 / B := by
    have := mul_le_mul_of_nonneg_left hab hBpos.le
    refine this.trans_eq ?_
    rw [abs_of_pos hspos, hs]
    rw [← hq2]
    field_simp
  rw [hbB] at htel
  rw [div_le_iff₀ hu]
  calc ‖a ^ B - Complex.exp (-(u:ℂ) ^ 2 / 2)‖ ≤ (B * ‖a - b‖) * r ^ n := by
        have hnB : (B:ℝ) = n + 1 := by exact_mod_cast hn
        rw [hnB]; exact htel
    _ ≤ (A * u ^ 3 / (6 * q) + C * u ^ 4 / B) * Real.exp (-u ^ 2 / 8) := by
        gcongr
    _ = _ := by
        rw [← hq2]; field_simp

private lemma L_large (φ : ℝ → ℂ) (δ ρ Cc : ℝ) (hδ : 0 < δ) (hρ : 0 ≤ ρ) (B : ℕ) (hB : 4 ≤ B)
    (hfar : ∀ t : ℝ, δ ≤ |t| → ‖φ t‖ ≤ ρ)
    (hone : ∀ t : ℝ, δ ≤ |t| → ‖φ t‖ ≤ 1)
    (hsq : ∀ t : ℝ, δ ≤ |t| → ‖φ t‖ ^ 2 ≤ Cc / |t|)
    (u : ℝ) (hu : 0 < u) (huδ : δ * Real.sqrt B < u) :
    ‖φ (u / Real.sqrt B) ^ B - Complex.exp (-(u:ℂ) ^ 2 / 2)‖ / u ≤
      ρ ^ (B - 4) * Cc * Real.sqrt B * u ^ (-2:ℝ) + 2 * u ^ (-3:ℝ) := by
  have hBpos : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  set q := Real.sqrt B with hq
  have hqpos : 0 < q := Real.sqrt_pos.2 hBpos
  set s := u / q with hs
  have hspos : 0 < s := div_pos hu hqpos
  have hsδ : δ ≤ |s| := by
    rw [abs_of_pos hspos, hs, le_div_iff₀ hqpos]; exact huδ.le
  have h1 := hone s hsδ
  have h2 := hfar s hsδ
  have h3 := hsq s hsδ
  rw [abs_of_pos hspos] at h3
  set m := ‖φ s‖ with hm
  have hm0 : 0 ≤ m := norm_nonneg _
  have hmB : m ^ B ≤ ρ ^ (B - 4) * (Cc / s) := by
    have e : m ^ B = m ^ (B - 4) * (m ^ 2 * m ^ 2) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [e]
    have a1 : m ^ (B - 4) ≤ ρ ^ (B - 4) := pow_le_pow_left₀ hm0 h2 _
    have a2 : m ^ 2 * m ^ 2 ≤ Cc / s := by
      calc m ^ 2 * m ^ 2 ≤ m ^ 2 * 1 := by gcongr; nlinarith
        _ ≤ Cc / s := by rw [mul_one]; exact h3
    exact mul_le_mul a1 a2 (by positivity) (by positivity)
  have hexp : Real.exp (-u ^ 2 / 2) ≤ 2 / u ^ 2 := by
    have := Real.add_one_le_exp (u ^ 2 / 2)
    have hpos : 0 < u ^ 2 / 2 := by positivity
    have : u ^ 2 / 2 ≤ Real.exp (u ^ 2 / 2) := by linarith
    rw [show -u ^ 2 / 2 = -(u ^ 2 / 2) by ring, Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    nlinarith
  have hnorm : ‖φ s ^ B - Complex.exp (-(u:ℂ) ^ 2 / 2)‖ ≤ m ^ B + Real.exp (-u ^ 2 / 2) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, Complex.norm_exp]
    have : (-(u:ℂ) ^ 2 / 2) = ((-u ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  have hs' : Cc / s = Cc * q / u := by rw [hs]; field_simp
  rw [div_le_iff₀ hu]
  have e2 : u ^ (-2:ℝ) = (u ^ 2)⁻¹ := by rw [Real.rpow_neg hu.le, Real.rpow_two]
  have e3 : u ^ (-3:ℝ) = (u ^ 3)⁻¹ := by
    rw [Real.rpow_neg hu.le, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [e2, e3]
  calc _ ≤ m ^ B + Real.exp (-u ^ 2 / 2) := hnorm
    _ ≤ ρ ^ (B - 4) * (Cc * q / u) + 2 / u ^ 2 := by rw [← hs']; gcongr
    _ = _ := by field_simp

private lemma gauss_moment2 :
    ∫ u in Ioi (0:ℝ), u ^ 2 * Real.exp (-u ^ 2 / 8) = 4 * Real.sqrt (2 * Real.pi) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := 1 / 8) (by norm_num)
    (by norm_num) (by norm_num)
  have e1 : ∀ x ∈ Ioi (0:ℝ), x ^ (2:ℝ) * Real.exp (-(1 / 8) * x ^ (2:ℝ)) = x ^ 2 * Real.exp (-x ^ 2 / 8) := by
    intro x _
    rw [Real.rpow_two]; ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi e1] at h
  rw [h]
  have hG : Real.Gamma ((2 + 1) / 2) = Real.sqrt Real.pi / 2 := by
    rw [show ((2:ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  rw [hG]
  have h8 : ((1:ℝ) / 8) ^ (-(2 + 1) / (2:ℝ)) = 8 * Real.sqrt 8 := by
    rw [show (-(2 + 1) / (2:ℝ)) = -(3/2) by norm_num, one_div, Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num), inv_inv, show (3/2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [h8]
  have h2 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8:ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h2, Real.sqrt_mul (by norm_num)]
  ring

private lemma gauss_moment3 :
    ∫ u in Ioi (0:ℝ), u ^ 3 * Real.exp (-u ^ 2 / 8) = 32 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 3) (b := 1 / 8) (by norm_num)
    (by norm_num) (by norm_num)
  have e1 : ∀ x ∈ Ioi (0:ℝ), x ^ (3:ℝ) * Real.exp (-(1 / 8) * x ^ (2:ℝ)) = x ^ 3 * Real.exp (-x ^ 2 / 8) := by
    intro x _
    rw [Real.rpow_two, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi e1] at h
  rw [h]
  have hG : Real.Gamma ((3 + 1) / 2) = 1 := by
    rw [show ((3:ℝ) + 1) / 2 = 2 by norm_num, Real.Gamma_two]
  rw [hG]
  rw [show (-(3 + 1) / (2:ℝ)) = -2 by norm_num, one_div, Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num), inv_inv]
  norm_num

private lemma gauss_integrable (k : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-u ^ 2 / 8)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 8) (by norm_num) (s := (k:ℝ)) (by
    have : (0:ℝ) ≤ k := Nat.cast_nonneg k
    linarith)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast]
  ring_nf

private lemma int_rpow_neg2 (a : ℝ) (ha : 0 < a) :
    ∫ u in Ioi a, u ^ (-2:ℝ) = a⁻¹ := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) ha]
  rw [show (-2:ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  ring

private lemma int_rpow_neg3 (a : ℝ) (ha : 0 < a) :
    ∫ u in Ioi a, u ^ (-3:ℝ) = (a ^ 2)⁻¹ / 2 := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) ha]
  rw [show (-3:ℝ) + 1 = -2 by norm_num, Real.rpow_neg (by positivity), Real.rpow_two]
  ring


private lemma L_int (A C c₁ a q Bn : ℝ) (hq : 0 < q) (hBn : 0 < Bn) (ha : 0 < a)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hc₁ : 0 ≤ c₁) (H : ℝ → ℝ)
    (hH : ∀ u, H u = if u ≤ a then Real.exp (-u ^ 2 / 8) * (A * u ^ 2 / (6 * q) + C * u ^ 3 / Bn)
      else c₁ * u ^ (-2:ℝ) + 2 * u ^ (-3:ℝ)) :
    IntegrableOn H (Ioi 0) ∧
      ∫ u in Ioi (0:ℝ), H u ≤
        A * (4 * Real.sqrt (2 * Real.pi)) / (6 * q) + 32 * C / Bn + c₁ / a + 1 / a ^ 2 := by
  set Hs : ℝ → ℝ := fun u => Real.exp (-u ^ 2 / 8) * (A * u ^ 2 / (6 * q) + C * u ^ 3 / Bn) with hHs
  set Hl : ℝ → ℝ := fun u => c₁ * u ^ (-2:ℝ) + 2 * u ^ (-3:ℝ) with hHl
  have hHsI : IntegrableOn Hs (Ioi 0) := by
    have : IntegrableOn (fun u : ℝ => A / (6 * q) * (u ^ 2 * Real.exp (-u ^ 2 / 8)) +
        C / Bn * (u ^ 3 * Real.exp (-u ^ 2 / 8))) (Ioi 0) :=
      ((gauss_integrable 2).const_mul (A / (6 * q))).add ((gauss_integrable 3).const_mul (C / Bn))
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [hHs]; ring
  have hHlI : IntegrableOn Hl (Ioi a) := by
    have h2 := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) ha
    have h3 := integrableOn_Ioi_rpow_of_lt (a := -3) (by norm_num) ha
    exact (h2.const_mul c₁).add (h3.const_mul 2)
  have hunion : Ioc (0:ℝ) a ∪ Ioi a = Ioi 0 := Ioc_union_Ioi_eq_Ioi ha.le
  have hdisj : Disjoint (Ioc (0:ℝ) a) (Ioi a) := Ioc_disjoint_Ioi le_rfl
  have hs1 : ∀ u ∈ Ioc (0:ℝ) a, H u = Hs u := fun u hu => by rw [hH, if_pos hu.2]
  have hs2 : ∀ u ∈ Ioi a, H u = Hl u := fun u hu => by rw [hH, if_neg (not_le.2 hu)]
  have hI1 : IntegrableOn H (Ioc 0 a) :=
    (hHsI.mono_set Ioc_subset_Ioi_self).congr_fun (fun u hu => (hs1 u hu).symm) measurableSet_Ioc
  have hI2 : IntegrableOn H (Ioi a) :=
    hHlI.congr_fun (fun u hu => (hs2 u hu).symm) measurableSet_Ioi
  have hI : IntegrableOn H (Ioi 0) := by
    rw [← hunion]; exact hI1.union hI2
  refine ⟨hI, ?_⟩
  have hsplit : ∫ u in Ioi (0:ℝ), H u = (∫ u in Ioc (0:ℝ) a, H u) + ∫ u in Ioi a, H u := by
    rw [← setIntegral_union hdisj measurableSet_Ioi hI1 hI2, hunion]
  have hP1 : ∫ u in Ioc (0:ℝ) a, H u = ∫ u in Ioc (0:ℝ) a, Hs u :=
    setIntegral_congr_fun measurableSet_Ioc hs1
  have hP2 : ∫ u in Ioi a, H u = ∫ u in Ioi a, Hl u :=
    setIntegral_congr_fun measurableSet_Ioi hs2
  have hHs0 : ∀ u ∈ Ioi (0:ℝ), 0 ≤ Hs u := by
    intro u hu
    have hu : 0 < u := hu
    simp only [hHs]
    positivity
  have hP1' : ∫ u in Ioc (0:ℝ) a, Hs u ≤ ∫ u in Ioi (0:ℝ), Hs u :=
    setIntegral_mono_set hHsI ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall hHs0)) (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
  have hHsval : ∫ u in Ioi (0:ℝ), Hs u = A * (4 * Real.sqrt (2 * Real.pi)) / (6 * q) + 32 * C / Bn := by
    have e : ∫ u in Ioi (0:ℝ), Hs u =
        ∫ u in Ioi (0:ℝ), (A / (6 * q) * (u ^ 2 * Real.exp (-u ^ 2 / 8)) + C / Bn * (u ^ 3 * Real.exp (-u ^ 2 / 8))) :=
      setIntegral_congr_fun measurableSet_Ioi (fun u _ => by simp only [hHs]; ring)
    rw [e, integral_add ((gauss_integrable 2).const_mul _) ((gauss_integrable 3).const_mul _),
      integral_const_mul, integral_const_mul, gauss_moment2, gauss_moment3]
    field_simp
  have hHlval : ∫ u in Ioi a, Hl u = c₁ / a + 1 / a ^ 2 := by
    have h2 := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) ha
    have h3 := integrableOn_Ioi_rpow_of_lt (a := -3) (by norm_num) ha
    simp only [hHl]
    rw [integral_add (h2.const_mul c₁) (h3.const_mul 2), integral_const_mul, integral_const_mul,
      int_rpow_neg2 a ha, int_rpow_neg3 a ha]
    field_simp
  rw [hsplit, hP1, hP2, hHlval]
  have := hP1'.trans_eq hHsval
  linarith



private lemma batch_phi (μ : Measure ℝ) [IsProbabilityMeasure μ] (B : ℕ) (u : ℝ) :
    ∫ p : Fin B → ℝ, Complex.exp ((u:ℂ) * Complex.I * (((∑ a, p a) / Real.sqrt B : ℝ) : ℂ))
        ∂(Measure.pi fun _ : Fin B => μ) =
      (∫ y, Complex.exp (((u / Real.sqrt B : ℝ) : ℂ) * Complex.I * (y : ℂ)) ∂μ) ^ B := by
  have hpt : ∀ p : Fin B → ℝ, Complex.exp ((u:ℂ) * Complex.I * (((∑ a, p a) / Real.sqrt B : ℝ) : ℂ)) =
      ∏ a, Complex.exp (((u / Real.sqrt B : ℝ) : ℂ) * Complex.I * (p a : ℂ)) := by
    intro p
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  simp_rw [hpt]
  rw [integral_fintype_prod_eq_pow (fun y : ℝ => Complex.exp (((u / Real.sqrt B : ℝ) : ℂ) * Complex.I * (y : ℂ)))]
  simp

private lemma gauss_phi (u : ℝ) :
    ∫ g : ℝ, Complex.exp ((u:ℂ) * Complex.I * (g : ℂ)) ∂(gaussianReal 0 1) =
      Complex.exp (-(u:ℂ) ^ 2 / 2) := by
  have h := charFun_gaussianReal (μ := 0) (v := 1) u
  rw [charFun_apply_real] at h
  simp_rw [show ∀ g : ℝ, (u:ℂ) * Complex.I * (g:ℂ) = (u:ℂ) * (g:ℂ) * Complex.I from fun g => by ring]
  rw [h]
  congr 1
  push_cast
  ring


private lemma mu_facts (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h1 : ∫ y, y ∂μ = 0) (hvar : variance (fun y : ℝ => y) μ = 1)
    (hM : ∫⁻ y, ENNReal.ofReal (y ^ 4) ∂μ ≤ ENNReal.ofReal 88208) :
    Integrable (fun y : ℝ => y ^ 4) μ ∧ ∫ y, y ^ 4 ∂μ ≤ 88208 ∧ ∫ y, y ^ 2 ∂μ = 1 := by
  have hmeas : AEStronglyMeasurable (fun y : ℝ => y ^ 4) μ :=
    (by fun_prop : Measurable fun y : ℝ => y ^ 4).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[μ] fun y : ℝ => y ^ 4 := Filter.Eventually.of_forall fun y => by positivity
  have hm4 : Integrable (fun y : ℝ => y ^ 4) μ := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hM ENNReal.ofReal_lt_top
  refine ⟨hm4, ?_, ?_⟩
  · have := ofReal_integral_eq_lintegral_ofReal hm4 hnn
    rw [← this] at hM
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 hM
  · obtain ⟨i1, i2, -, -⟩ := moments_integrable μ hm4
    have hL2 : MemLp (fun y : ℝ => y) 2 μ :=
      (memLp_two_iff_integrable_sq (by fun_prop)).2 i2
    have := variance_eq_sub hL2
    rw [hvar] at this
    simp only [Pi.pow_apply] at this
    rw [h1] at this
    linarith

end SignComparisonHelpers

/-- **lem:app-sgd-comparison** `Muon.SignSGD.lem_app_sgd_comparison` (snapshot `cr-2026-10-23`).
LaTeX statement, verbatim:
```latex
There is a universal constant $C_2$ such that the following holds with
$C_1\defeq4\sqrt{2\pi}/(3\pi)$. Let $Y$ be centered with variance $1$,
$\EE Y^4\le88208$, and characteristic function satisfying
\cref{eqn:app-sgd-decay}. Let $Y_1,\dots,Y_B$ be independent copies of $Y$,
$B\ge4$, and $g$ standard Gaussian. Then for every real $x$
\begin{equation}\label{eqn:app-sgd-comparison}
\Big|\EE\sign\Big(\frac1{\sqrt B}\sum_{a=1}^BY_a+x\Big)-\EE\sign(g+x)\Big|
\le\frac{C_1\abs{\EE Y^3}}{\sqrt B}+\frac{C_2}B .
\end{equation}
```
Hypotheses on the law `μ` of `Y`: probability measure, centered, variance `1`,
`E Y^4 ≤ 88208`, and the decay `eqn:app-sgd-decay` (`t ≠ 0`):
`|φ_Y(t)| ≤ ψ(|t|/8) ≤ min{1, C_ch |t|^{-1/2}}`.
-/
theorem lem_app_sgd_comparison :
    ∃ C₂ : ℝ, ∀ B : ℕ, 4 ≤ B →
      ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
        ∫ y, y ∂μ = 0 →
        variance (fun y : ℝ => y) μ = 1 →
        ∫⁻ y, ENNReal.ofReal (y ^ 4) ∂μ ≤ ENNReal.ofReal 88208 →
        (∀ t : ℝ, t ≠ 0 →
          ‖∫ y, Complex.exp ((t : ℂ) * Complex.I * (y : ℂ)) ∂μ‖ ≤ sgdPsi (|t| / 8) ∧
            sgdPsi (|t| / 8) ≤ min 1 (sgdCch * |t| ^ (-(1 / 2 : ℝ)))) →
        ∀ x : ℝ,
          |∫ p : Fin B → ℝ,
              Real.sign ((∑ a, p a) / Real.sqrt (B : ℝ) + x) ∂(Measure.pi fun _ : Fin B => μ)
            - ∫ g, Real.sign (g + x) ∂(gaussianReal 0 1)|
            ≤ sgdC1 * |∫ y, y ^ 3 ∂μ| / Real.sqrt (B : ℝ) + C₂ / (B : ℝ) := by
  classical
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / 200000 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; norm_num
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = sgdPsi (δ / 8) := ⟨_, rfl⟩
  have hρlt : ρ < 1 := by rw [hρ]; exact sgd_psi_lt_one (by positivity)
  have hρ0 : 0 ≤ ρ := by
    rw [hρ]
    refine integral_nonneg fun p => ?_
    exact Real.rpow_nonneg (by positivity) _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ n : ℕ, ((n : ℝ) + 4) * ρ ^ n ≤ K := by
    have ht := tendsto_self_mul_const_pow_of_lt_one hρ0 hρlt
    obtain ⟨K0, hK0⟩ := ht.bddAbove_range
    refine ⟨K0 + 4, fun n => ?_⟩
    have h1 : (n : ℝ) * ρ ^ n ≤ K0 := hK0 ⟨n, rfl⟩
    have h2 : ρ ^ n ≤ 1 := pow_le_one₀ hρ0 hρlt.le
    nlinarith
  refine ⟨2 / Real.pi * (32 * 88209 + K * sgdCch ^ 2 / δ + 1 / δ ^ 2), ?_⟩
  intro B hB μ hμ h1 hvar hM hdecay x
  haveI := hμ
  obtain ⟨hm4, hM4, h2⟩ := mu_facts μ h1 hvar hM
  obtain ⟨i1, i2, i3, -⟩ := moments_integrable μ hm4
  set φ : ℝ → ℂ := fun t => ∫ y, Complex.exp ((t : ℂ) * Complex.I * (y : ℂ)) ∂μ with hφ
  set κ : ℝ := ∫ y, y ^ 3 ∂μ with hκ
  have hnear : ∀ t : ℝ, |t| ≤ δ → ‖φ t‖ ≤ Real.exp (-t ^ 2 / 4) := by
    intro t ht
    have hb := phi_bound3 μ hm4 h1 h2 t
    have hc : ‖(1 : ℂ) - (t : ℂ) ^ 2 / 2‖ = 1 - t ^ 2 / 2 := by
      have e : (1 : ℂ) - (t : ℂ) ^ 2 / 2 = ((1 - t ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
      have hsq : t ^ 2 ≤ δ ^ 2 := by
        rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) ht 2
      have hδ1 : δ ^ 2 ≤ 1 := by rw [hδ]; norm_num
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hsplit : φ t = (φ t - (1 - (t : ℂ) ^ 2 / 2)) + (1 - (t : ℂ) ^ 2 / 2) := by ring
    have hn : ‖φ t‖ ≤ ‖φ t - (1 - (t : ℂ) ^ 2 / 2)‖ + ‖(1 : ℂ) - (t : ℂ) ^ 2 / 2‖ := by
      calc ‖φ t‖ = ‖(φ t - (1 - (t : ℂ) ^ 2 / 2)) + (1 - (t : ℂ) ^ 2 / 2)‖ := by rw [← hsplit]
        _ ≤ _ := norm_add_le _ _
    have e3 : |t| ^ 3 = t ^ 2 * |t| := by rw [← sq_abs t]; ring
    have hM4' : (1 + ∫ y, y ^ 4 ∂μ) / 2 ≤ 44105 := by linarith
    have hA : |t| ^ 3 * ((1 + ∫ y, y ^ 4 ∂μ) / 2) ≤ t ^ 2 / 4 := by
      have hM0 : 0 ≤ (1 + ∫ y, y ^ 4 ∂μ) / 2 := by
        have : 0 ≤ ∫ y, y ^ 4 ∂μ := integral_nonneg fun y => by positivity
        linarith
      calc |t| ^ 3 * ((1 + ∫ y, y ^ 4 ∂μ) / 2) ≤ (t ^ 2 * δ) * 44105 := by
            rw [e3]
            gcongr
        _ ≤ t ^ 2 / 4 := by
            rw [hδ]; nlinarith [sq_nonneg t]
    have := Real.add_one_le_exp (-t ^ 2 / 4)
    linarith
  have htay : ∀ t : ℝ, ‖φ t - Complex.exp (-(t : ℂ) ^ 2 / 2)‖ ≤
      |κ| * |t| ^ 3 / 6 + 88209 * t ^ 4 := by
    intro t
    refine (phi_bound4 μ hm4 h1 h2 t).trans ?_
    have : 0 ≤ t ^ 4 := by positivity
    nlinarith
  have hψ : ∀ t : ℝ, δ ≤ |t| → ‖φ t‖ ≤ ρ ∧ ‖φ t‖ ≤ 1 ∧ ‖φ t‖ ^ 2 ≤ sgdCch ^ 2 / |t| := by
    intro t ht
    have ht0 : t ≠ 0 := by
      intro h
      rw [h] at ht
      simp at ht
      linarith
    obtain ⟨h1', h2'⟩ := hdecay t ht0
    have htpos : 0 < |t| := abs_pos.2 ht0
    refine ⟨?_, ?_, ?_⟩
    · have hmono : sgdPsi (|t| / 8) ≤ sgdPsi (δ / 8) :=
        sgd_psi_antitoneOn (show δ / 8 ∈ Set.Ici (0:ℝ) from by simp only [Set.mem_Ici]; positivity)
          (show |t| / 8 ∈ Set.Ici (0:ℝ) from by simp only [Set.mem_Ici]; positivity)
          (by linarith)
      rw [hρ]; exact h1'.trans hmono
    · exact h1'.trans (h2'.trans (min_le_left _ _))
    · have hle : ‖φ t‖ ≤ sgdCch * |t| ^ (-(1 / 2 : ℝ)) := h1'.trans (h2'.trans (min_le_right _ _))
      have e : (|t| ^ (-(1 / 2 : ℝ))) ^ 2 = |t|⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg t)]
        norm_num [Real.rpow_neg_one]
      calc ‖φ t‖ ^ 2 ≤ (sgdCch * |t| ^ (-(1 / 2 : ℝ))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
        _ = sgdCch ^ 2 / |t| := by rw [mul_pow, e]; ring
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hq : 0 < Real.sqrt B := Real.sqrt_pos.2 hBpos
  have hq2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hBpos.le
  have ha : 0 < δ * Real.sqrt B := by positivity
  -- the bounding function
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ, ∀ u, H u =
      if u ≤ δ * Real.sqrt B then Real.exp (-u ^ 2 / 8) *
        (|κ| * u ^ 2 / (6 * Real.sqrt B) + 88209 * u ^ 3 / B)
      else ρ ^ (B - 4) * sgdCch ^ 2 * Real.sqrt B * u ^ (-2 : ℝ) + 2 * u ^ (-3 : ℝ) :=
    ⟨_, fun u => rfl⟩
  obtain ⟨hHint, hHbound⟩ := L_int |κ| 88209 (ρ ^ (B - 4) * sgdCch ^ 2 * Real.sqrt B)
    (δ * Real.sqrt B) (Real.sqrt B) B hq hBpos ha (abs_nonneg _) (by norm_num)
    (by positivity) H hH
  have hbd : ∀ u : ℝ, 0 < u →
      ‖(∫ p : Fin B → ℝ, Complex.exp ((u : ℂ) * Complex.I *
          (((∑ a, p a) / Real.sqrt B : ℝ) : ℂ)) ∂(Measure.pi fun _ : Fin B => μ)) -
        ∫ g : ℝ, Complex.exp ((u : ℂ) * Complex.I * (g : ℂ)) ∂(gaussianReal 0 1)‖ / u ≤ H u := by
    intro u hu
    rw [batch_phi μ B u, gauss_phi u, hH u]
    split_ifs with hle
    · exact L_small φ δ |κ| 88209 (abs_nonneg _) (by norm_num) B hB hnear htay u hu hle
    · exact L_large φ δ ρ (sgdCch ^ 2) hδpos hρ0 B hB (fun t ht => (hψ t ht).1)
        (fun t ht => (hψ t ht).2.1) (fun t ht => (hψ t ht).2.2) u hu (not_le.1 hle)
  have hi1 : Integrable (fun p : Fin B → ℝ => (∑ a, p a) / Real.sqrt B)
      (Measure.pi fun _ : Fin B => μ) := by
    refine (integrable_finset_sum _ fun a _ => ?_).div_const _
    exact integrable_eval (μ := fun _ : Fin B => μ) (i := a) i1
  have hi2 : Integrable (fun g : ℝ => g) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
  have key := sign_comparison_generic (Measure.pi fun _ : Fin B => μ) (gaussianReal 0 1)
    (fun p => (∑ a, p a) / Real.sqrt B) (fun g => g) (by fun_prop) measurable_id hi1 hi2 H hHint hbd x
  have hCc : 0 ≤ sgdCch ^ 2 := sq_nonneg _
  have hρB : ρ ^ (B - 4) ≤ K / B := by
    have h := hK (B - 4)
    have hc : ((B - 4 : ℕ) : ℝ) + 4 = B := by
      rw [Nat.cast_sub hB]; norm_num
    rw [hc] at h
    rw [le_div_iff₀ hBpos]
    linarith
  have hc1 : ρ ^ (B - 4) * sgdCch ^ 2 * Real.sqrt B / (δ * Real.sqrt B) ≤ K * sgdCch ^ 2 / δ / B := by
    have e : ρ ^ (B - 4) * sgdCch ^ 2 * Real.sqrt B / (δ * Real.sqrt B) =
        ρ ^ (B - 4) * (sgdCch ^ 2 / δ) := by
      field_simp
    rw [e]
    calc ρ ^ (B - 4) * (sgdCch ^ 2 / δ) ≤ (K / B) * (sgdCch ^ 2 / δ) := by gcongr
      _ = K * sgdCch ^ 2 / δ / B := by ring
  have h1a : 1 / (δ * Real.sqrt B) ^ 2 = 1 / δ ^ 2 / B := by
    rw [mul_pow, hq2]; field_simp
  have hpi := Real.pi_pos
  calc _ ≤ 2 / Real.pi * ∫ u in Set.Ioi (0 : ℝ), H u := key
    _ ≤ 2 / Real.pi * (|κ| * (4 * Real.sqrt (2 * Real.pi)) / (6 * Real.sqrt B) + 32 * 88209 / B +
          ρ ^ (B - 4) * sgdCch ^ 2 * Real.sqrt B / (δ * Real.sqrt B) +
          1 / (δ * Real.sqrt B) ^ 2) := by gcongr
    _ ≤ 2 / Real.pi * (|κ| * (4 * Real.sqrt (2 * Real.pi)) / (6 * Real.sqrt B) + 32 * 88209 / B +
          K * sgdCch ^ 2 / δ / B + 1 / δ ^ 2 / B) := by
        rw [h1a]; gcongr
    _ = _ := by
        unfold sgdC1
        field_simp
        ring

end Muon.SignSGD

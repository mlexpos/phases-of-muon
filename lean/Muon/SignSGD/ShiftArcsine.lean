import Muon.Foundations.GaussianCombinatorics

/-!
# Appendix I (SignSGD): Gaussian sign tools

Interface for the labels `lem:app-sgd-arcsine` (one theorem per clause: the arcsine law and the
degenerate clause) and `lem:app-sgd-shift` (four theorems, parts (i)–(iv)).
Source of record: snapshot `cr-2026-10-23`, `sections/08-signsgd/section.tex` l. 78–85 and
l. 104–123. Docstrings carry the LaTeX statement verbatim.

Cited result. Sheppard's formula is proved in `Muon.Foundations.sheppard_arcsine`
(GaussianCombinatorics, cited result `SheppardArcsine`); the arcsine proof reuses it, so no
certificate is needed here. The proof of `lem:app-sgd-arcsine` is therefore a reduction, not a
citation.

Hidden hypotheses made explicit. "Centered Gaussian pair" is read as a jointly Gaussian pair
(`HasGaussianLaw` of `ω ↦ (g₁ ω, g₂ ω)`), as CORRECTIONS card item 8 requires. The variances
`v₁, v₂` are `ProbabilityTheory.variance`; the correlation `ρ` is `gaussCorr`.

Quantifier order. Part (ii) and (iii) of `lem:app-sgd-shift` hold for all `x` with `|x| ≤ a`, for
the given `a`, `α`, `L_f` (resp. `a`, `K_f`); part (iv) holds for all real `x` and the given `σ`.
The constant `√(2/π)` and the bounds carry no free constant.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace Muon.SignSGD

/-- Private helper: scaling by a positive constant preserves `SignType.sign`. -/
private lemma sgn_div_pos_aux (g s : ℝ) (hs : 0 < s) :
    SignType.sign (g / s) = SignType.sign g := by
  rcases lt_trichotomy g 0 with h | h | h
  · rw [_root_.sign_neg h, _root_.sign_neg (div_neg_of_neg_of_pos h hs)]
  · simp [h]
  · rw [_root_.sign_pos h, _root_.sign_pos (div_pos h hs)]

/-- Private helper: `{p | sign p.1 ≠ sign p.2}` is measurable. -/
private lemma sign_ne_meas_pair_aux :
    MeasurableSet {p : ℝ × ℝ | SignType.sign p.1 ≠ SignType.sign p.2} := by
  have : {p : ℝ × ℝ | SignType.sign p.1 ≠ SignType.sign p.2} =
      (symmDiff {p : ℝ × ℝ | 0 < p.1} {p : ℝ × ℝ | 0 < p.2} ∪
        symmDiff {p : ℝ × ℝ | p.1 < 0} {p : ℝ × ℝ | p.2 < 0}) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_symmDiff]
    rcases lt_trichotomy p.1 0 with h1 | h1 | h1 <;>
      rcases lt_trichotomy p.2 0 with h2 | h2 | h2 <;>
      simp [h1, h2, _root_.sign_neg, _root_.sign_pos, h1.not_gt, h2.not_gt, h1.le, h2.le]
  rw [this]
  exact ((((measurableSet_lt measurable_const measurable_fst).symmDiff
      (measurableSet_lt measurable_const measurable_snd)).union
    ((measurableSet_lt measurable_fst measurable_const).symmDiff
      (measurableSet_lt measurable_snd measurable_const))))

/-- Private helper: two unit-variance centred `L²` variables have correlation in `[-1, 1]`. -/
private lemma unit_corr_bounds_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (a b : Ω → ℝ) (ha : MemLp a 2 P) (hb : MemLp b 2 P)
    (ha1 : ∫ ω, a ω ^ 2 ∂P = 1) (hb1 : ∫ ω, b ω ^ 2 ∂P = 1) :
    -1 ≤ ∫ ω, a ω * b ω ∂P ∧ ∫ ω, a ω * b ω ∂P ≤ 1 := by
  have hsa : Integrable (fun ω => a ω ^ 2) P := ha.integrable_sq
  have hsb : Integrable (fun ω => b ω ^ 2) P := hb.integrable_sq
  have hab : Integrable (fun ω => a ω * b ω) P := ha.integrable_mul hb
  have h1 : 0 ≤ ∫ ω, (a ω - b ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have h2 : 0 ≤ ∫ ω, (a ω + b ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have e1 : ∫ ω, (a ω - b ω) ^ 2 ∂P = 1 + 1 - 2 * ∫ ω, a ω * b ω ∂P := by
    have : (fun ω => (a ω - b ω) ^ 2) = fun ω => (a ω ^ 2 + b ω ^ 2) - 2 * (a ω * b ω) := by
      funext ω; ring
    have hsab : Integrable (fun ω => a ω ^ 2 + b ω ^ 2) P := hsa.add hsb
    rw [this, integral_sub hsab (hab.const_mul 2), integral_add hsa hsb,
      integral_const_mul, ha1, hb1]
  have e2 : ∫ ω, (a ω + b ω) ^ 2 ∂P = 1 + 1 + 2 * ∫ ω, a ω * b ω ∂P := by
    have : (fun ω => (a ω + b ω) ^ 2) = fun ω => (a ω ^ 2 + b ω ^ 2) + 2 * (a ω * b ω) := by
      funext ω; ring
    have hsab : Integrable (fun ω => a ω ^ 2 + b ω ^ 2) P := hsa.add hsb
    rw [this, integral_add hsab (hab.const_mul 2), integral_add hsa hsb,
      integral_const_mul, ha1, hb1]
  constructor <;> linarith

/-- Private helper: a centred `L²` variable with variance zero vanishes a.s. -/
private lemma zero_ae_of_var_zero_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (g : Ω → ℝ) (hg : MemLp g 2 P) (hm : ∫ ω, g ω ∂P = 0)
    (hv : variance g P = 0) : ∀ᵐ ω ∂P, g ω = 0 := by
  filter_upwards [ae_eq_integral_of_variance_eq_zero hg hv] with ω hω
  exact hω.trans hm

/-- Private helper: a positive-variance Gaussian variable is a.s. nonzero. -/
private lemma ae_ne_zero_of_var_pos_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (g : Ω → ℝ) (hg : HasGaussianLaw g P) (hv : 0 < variance g P) :
    ∀ᵐ ω ∂P, g ω ≠ 0 := by
  have hne : (variance g P).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hv
  rw [ae_iff]
  simp only [ne_eq, not_not]
  show P (g ⁻¹' {0}) = 0
  rw [← Measure.map_apply_of_aemeasurable hg.aemeasurable (measurableSet_singleton 0),
    hg.map_eq_gaussianReal]
  exact gaussianReal_absolutelyContinuous _ hne Real.volume_singleton

/-- Correlation `ρ = E[g₁ g₂] / √(v₁ v₂)` of a centred pair with variances `v₁ = Var g₁`,
`v₂ = Var g₂` (`lem:app-sgd-arcsine`, l. 80–81). Local to this module; not a project-wide
object. -/
noncomputable def gaussCorr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (g₁ g₂ : Ω → ℝ) : ℝ :=
  (∫ ω, g₁ ω * g₂ ω ∂P) / Real.sqrt (variance g₁ P * variance g₂ P)

/-- The smoothed sign mean `h(x) = E sign(X + x)` of `lem:app-sgd-shift` (l. 105). -/
noncomputable def signShiftMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (x : ℝ) : ℝ :=
  ∫ ω, Real.sign (X ω + x) ∂P

/-- `lem:app-sgd-arcsine` (snapshot `cr-2026-10-23`). LaTeX statement, verbatim:
```latex
\begin{lemma}[Arcsine law]\label{lem:app-sgd-arcsine}
Let $(g_1,g_2)$ be a centered Gaussian pair with variances $v_1,v_2>0$ and
correlation $\rho=\EE[g_1g_2]/\sqrt{v_1v_2}\in[-1,1]$. Then
\begin{equation}\label{eqn:signsgd-arcsin}
\EE\big[\sign(g_1)\sign(g_2)\big]=\frac2\pi\arcsin\rho .
\end{equation}
If $v_1=0$ or $v_2=0$, the left side is $0$.
\end{lemma}
```

Part (i) of `lem:app-sgd-arcsine`: the arcsine law for a centred jointly Gaussian pair with
positive variances. The correlation `ρ` lies in `[-1, 1]` and
`E[sign g₁ · sign g₂] = (2/π) arcsin ρ`. -/
theorem lem_app_sgd_arcsine_i {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (g₁ g₂ : Ω → ℝ)
    (hlaw : HasGaussianLaw (fun ω => (g₁ ω, g₂ ω)) P)
    (hmean₁ : ∫ ω, g₁ ω ∂P = 0) (hmean₂ : ∫ ω, g₂ ω ∂P = 0)
    (hv₁ : 0 < variance g₁ P) (hv₂ : 0 < variance g₂ P) :
    -1 ≤ gaussCorr P g₁ g₂ ∧ gaussCorr P g₁ g₂ ≤ 1 ∧
      ∫ ω, Real.sign (g₁ ω) * Real.sign (g₂ ω) ∂P
        = 2 / Real.pi * Real.arcsin (gaussCorr P g₁ g₂) := by
  have hm1 : MemLp g₁ 2 P := hlaw.fst.memLp_two
  have hm2 : MemLp g₂ 2 P := hlaw.snd.memLp_two
  have hsq₁ : ∫ ω, g₁ ω ^ 2 ∂P = variance g₁ P := by
    rw [variance_eq_sub hm1, hmean₁]; simp
  have hsq₂ : ∫ ω, g₂ ω ^ 2 ∂P = variance g₂ P := by
    rw [variance_eq_sub hm2, hmean₂]; simp
  set s₁ := Real.sqrt (variance g₁ P) with hs₁def
  set s₂ := Real.sqrt (variance g₂ P) with hs₂def
  have hs₁pos : 0 < s₁ := Real.sqrt_pos.2 hv₁
  have hs₂pos : 0 < s₂ := Real.sqrt_pos.2 hv₂
  have hs₁sq : s₁ ^ 2 = variance g₁ P := Real.sq_sqrt hv₁.le
  have hs₂sq : s₂ ^ 2 = variance g₂ P := Real.sq_sqrt hv₂.le
  -- normalised pair
  have hG : HasGaussianLaw (fun ω => (g₁ ω / s₁, g₂ ω / s₂)) P := by
    let L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
      (s₁⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (s₂⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)
    convert hlaw.map_fun L using 1
    funext ω
    simp [L, div_eq_inv_mul]
  have hmG1 : MemLp (fun ω => g₁ ω / s₁) 2 P := hG.fst.memLp_two
  have hmG2 : MemLp (fun ω => g₂ ω / s₂) 2 P := hG.snd.memLp_two
  have hunit₁ : ∫ ω, (g₁ ω / s₁) ^ 2 ∂P = 1 := by
    have : (fun ω => (g₁ ω / s₁) ^ 2) = fun ω => g₁ ω ^ 2 / s₁ ^ 2 := by
      funext ω; rw [div_pow]
    rw [this, integral_div, hsq₁, hs₁sq, div_self hv₁.ne']
  have hunit₂ : ∫ ω, (g₂ ω / s₂) ^ 2 ∂P = 1 := by
    have : (fun ω => (g₂ ω / s₂) ^ 2) = fun ω => g₂ ω ^ 2 / s₂ ^ 2 := by
      funext ω; rw [div_pow]
    rw [this, integral_div, hsq₂, hs₂sq, div_self hv₂.ne']
  have hmean_G1 : ∫ ω, g₁ ω / s₁ ∂P = 0 := by rw [integral_div, hmean₁, zero_div]
  have hmean_G2 : ∫ ω, g₂ ω / s₂ ∂P = 0 := by rw [integral_div, hmean₂, zero_div]
  have hcov : ∫ ω, (g₁ ω / s₁) * (g₂ ω / s₂) ∂P = gaussCorr P g₁ g₂ := by
    have : (fun ω => (g₁ ω / s₁) * (g₂ ω / s₂)) = fun ω => (g₁ ω * g₂ ω) / (s₁ * s₂) := by
      funext ω; rw [div_mul_div_comm]
    rw [this, integral_div]
    unfold gaussCorr
    rw [Real.sqrt_mul hv₁.le]
  have hρ := unit_corr_bounds_aux P _ _ hmG1 hmG2 hunit₁ hunit₂
  rw [hcov] at hρ
  -- sign set of the normalised pair
  set S : Set Ω := {ω | SignType.sign (g₁ ω / s₁) ≠ SignType.sign (g₂ ω / s₂)} with hS
  have hae₀ : ∀ᵐ ω ∂P, g₁ ω ≠ 0 := ae_ne_zero_of_var_pos_aux P g₁ hlaw.fst hv₁
  have hae₁ : ∀ᵐ ω ∂P, g₂ ω ≠ 0 := ae_ne_zero_of_var_pos_aux P g₂ hlaw.snd hv₂
  have key : ∀ ω, g₁ ω ≠ 0 → g₂ ω ≠ 0 →
      Real.sign (g₁ ω) * Real.sign (g₂ ω) = 1 - 2 * S.indicator 1 ω := by
    intro ω h1 h2
    have e1 : SignType.sign (g₁ ω / s₁) = SignType.sign (g₁ ω) := sgn_div_pos_aux _ _ hs₁pos
    have e2 : SignType.sign (g₂ ω / s₂) = SignType.sign (g₂ ω) := sgn_div_pos_aux _ _ hs₂pos
    simp only [hS, Set.indicator_apply, Set.mem_setOf_eq, e1, e2]
    rcases lt_or_gt_of_ne h1 with a | a <;> rcases lt_or_gt_of_ne h2 with b | b <;>
      simp [a, b, Real.sign_of_neg, Real.sign_of_pos, _root_.sign_neg, _root_.sign_pos] <;>
        norm_num
  have hae : ∀ᵐ ω ∂P, Real.sign (g₁ ω) * Real.sign (g₂ ω) = 1 - 2 * S.indicator 1 ω := by
    filter_upwards [hae₀, hae₁] with ω h1 h2
    exact key ω h1 h2
  have hSn : NullMeasurableSet S P := by
    rw [hS]
    exact hG.aemeasurable.nullMeasurableSet_preimage sign_ne_meas_pair_aux
  set T : Set Ω := toMeasurable P S with hTdef
  have hTm : MeasurableSet T := measurableSet_toMeasurable P S
  have hTS : P.real T = P.real S := by
    rw [measureReal_def, measureReal_def, measure_congr hSn.toMeasurable_ae_eq]
  have hindS : S.indicator (1 : Ω → ℝ) =ᵐ[P] T.indicator 1 :=
    indicator_ae_eq_of_ae_eq_set hSn.toMeasurable_ae_eq.symm
  have hint : ∫ ω, Real.sign (g₁ ω) * Real.sign (g₂ ω) ∂P = 1 - 2 * P.real S := by
    rw [integral_congr_ae hae]
    rw [integral_congr_ae (by filter_upwards [hindS] with ω hω; rw [hω] :
      (fun ω => 1 - 2 * S.indicator (1 : Ω → ℝ) ω) =ᵐ[P] fun ω => 1 - 2 * T.indicator 1 ω)]
    have hI : Integrable (fun ω => T.indicator (1 : Ω → ℝ) ω) P :=
      (integrable_const (1 : ℝ)).indicator hTm
    rw [integral_sub (integrable_const (1 : ℝ)) (hI.const_mul 2), integral_const_mul,
      integral_indicator_one hTm, hTS]
    simp
  -- Sheppard's formula
  have hρ' : gaussCorr P g₁ g₂ ∈ Set.Icc (-1 : ℝ) 1 := ⟨hρ.1, hρ.2⟩
  have hsh : P.real S = Real.arccos (gaussCorr P g₁ g₂) / Real.pi :=
    Muon.Foundations.sheppard_arcsine P (fun ω => g₁ ω / s₁) (fun ω => g₂ ω / s₂) (gaussCorr P g₁ g₂) hρ'
      hG hmean_G1 hmean_G2 hunit₁ hunit₂ hcov
  refine ⟨hρ.1, hρ.2, ?_⟩
  rw [hint, hsh, Real.arcsin_eq_pi_div_two_sub_arccos]
  field_simp

/-- `lem:app-sgd-arcsine` (snapshot `cr-2026-10-23`). LaTeX statement, verbatim:
```latex
\begin{lemma}[Arcsine law]\label{lem:app-sgd-arcsine}
Let $(g_1,g_2)$ be a centered Gaussian pair with variances $v_1,v_2>0$ and
correlation $\rho=\EE[g_1g_2]/\sqrt{v_1v_2}\in[-1,1]$. Then
\begin{equation}\label{eqn:signsgd-arcsin}
\EE\big[\sign(g_1)\sign(g_2)\big]=\frac2\pi\arcsin\rho .
\end{equation}
If $v_1=0$ or $v_2=0$, the left side is $0$.
\end{lemma}
```

Part (ii) of `lem:app-sgd-arcsine`: if `v₁ = 0` or `v₂ = 0`, the left side
`E[sign g₁ · sign g₂]` is `0`. -/
theorem lem_app_sgd_arcsine_ii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (g₁ g₂ : Ω → ℝ)
    (hlaw : HasGaussianLaw (fun ω => (g₁ ω, g₂ ω)) P)
    (hmean₁ : ∫ ω, g₁ ω ∂P = 0) (hmean₂ : ∫ ω, g₂ ω ∂P = 0)
    (hdeg : variance g₁ P = 0 ∨ variance g₂ P = 0) :
    ∫ ω, Real.sign (g₁ ω) * Real.sign (g₂ ω) ∂P = 0 := by
  rcases hdeg with h | h
  · have hz := zero_ae_of_var_zero_aux P g₁ hlaw.fst.memLp_two hmean₁ h
    have : ∀ᵐ ω ∂P, Real.sign (g₁ ω) * Real.sign (g₂ ω) = 0 := by
      filter_upwards [hz] with ω hω
      simp [hω]
    rw [integral_congr_ae this, integral_zero]
  · have hz := zero_ae_of_var_zero_aux P g₂ hlaw.snd.memLp_two hmean₂ h
    have : ∀ᵐ ω ∂P, Real.sign (g₁ ω) * Real.sign (g₂ ω) = 0 := by
      filter_upwards [hz] with ω hω
      simp [hω]
    rw [integral_congr_ae this, integral_zero]

/-- Private helper: `Real.sign` is measurable. -/
private lemma shift_meas_sign_aux : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const)

/-- Private helper: `hX` forces `X` to be AE-measurable (else the image is a Dirac mass). -/
private lemma shift_ae_meas_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (g : ℝ → ℝ)
    (hX : P.map X = volume.withDensity (fun y => ENNReal.ofReal (g y))) : AEMeasurable X P := by
  by_contra hn
  have hP : P ≠ 0 := IsProbabilityMeasure.ne_zero P
  rw [Measure.map_of_not_aemeasurable_of_ne_zero hn hP] at hX
  have hd := congrArg (fun μ : Measure ℝ => μ {Classical.ofNonempty}) hX
  simp only [Measure.dirac_apply_of_mem (Set.mem_singleton _),
    withDensity_apply _ (measurableSet_singleton _), Real.volume_singleton] at hd
  simp at hd

/-- Private helper: integrability and unit mass of the density. -/
private lemma shift_density_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hf_nn : ∀ y, 0 ≤ f y)
    (hX : P.map X = volume.withDensity (fun y => ENNReal.ofReal (f y))) :
    Integrable f ∧ ∫ y, f y = 1 := by
  have hae := shift_ae_meas_aux P X f hX
  have hmass : ∫⁻ y, ENNReal.ofReal (f y) = 1 := by
    have h := congrArg (fun μ : Measure ℝ => μ univ) hX
    rw [Measure.map_apply_of_aemeasurable hae MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
      Set.preimage_univ, measure_univ, Measure.restrict_univ] at h
    exact h.symm
  have hint : Integrable f := by
    have hl : ∫⁻ y, ENNReal.ofReal (f y) ≠ ⊤ := by rw [hmass]; exact ENNReal.one_ne_top
    have h := integrable_toReal_of_lintegral_ne_top (μ := volume)
      (f := fun y => ENNReal.ofReal (f y)) (ENNReal.measurable_ofReal.comp hf).aemeasurable hl
    exact h.congr (Eventually.of_forall fun y => ENNReal.toReal_ofReal (hf_nn y))
  have hint1 : ∫ y, f y = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => hf_nn y)
      hf.aestronglyMeasurable, hmass, ENNReal.toReal_one]
  exact ⟨hint, hint1⟩

/-- Private helper: the core identity `∫ f(y) sign(y+x) dy = 2 ∫₀ˣ f` for an even integrable
density of unit mass. -/
private lemma shift_core_aux (f : ℝ → ℝ) (hf_even : ∀ y, f (-y) = f y) (hint : Integrable f)
    (h1 : ∫ y, f y = 1) (x : ℝ) :
    ∫ y, f y * Real.sign (y + x) = 2 * ∫ y in (0:ℝ)..x, f y := by
  have hA : ∫ y, f y * Real.sign (y + x) = (∫ y, f y) - 2 * ∫ y in Iio (-x), f y := by
    have hne : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ -x := by
      rw [ae_iff]
      simpa using measure_singleton (μ := (volume : Measure ℝ)) (-x)
    have hae : (fun y => f y * Real.sign (y + x)) =ᵐ[volume]
        (fun y => f y - 2 * (Iio (-x)).indicator f y) := by
      filter_upwards [hne] with y hy
      rcases lt_or_gt_of_ne hy with h | h
      · have hs : Real.sign (y + x) = -1 := Real.sign_of_neg (by linarith)
        have hmem : y ∈ Iio (-x) := h
        simp only [hs, Set.indicator_of_mem hmem]
        ring
      · have hs : Real.sign (y + x) = 1 := Real.sign_of_pos (by linarith)
        have hnmem : y ∉ Iio (-x) := not_lt.2 h.le
        simp only [hs, Set.indicator_of_notMem hnmem, mul_one]
        ring
    rw [integral_congr_ae hae, integral_sub hint ((hint.indicator measurableSet_Iio).const_mul 2),
      integral_const_mul, integral_indicator measurableSet_Iio]
  have hhalf : ∫ y in Iio (0:ℝ), f y = 1 / 2 := by
    have h2 : ∫ y in Ioi (0:ℝ), f y = ∫ y in Iic (0:ℝ), f y := by
      have := integral_comp_neg_Ioi 0 f
      simp only [hf_even, neg_zero] at this
      exact this
    have hs : (∫ y in Iic (0:ℝ), f y) + (∫ y in Ioi (0:ℝ), f y) = ∫ y, f y :=
      intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn
    rw [h1, integral_Iic_eq_integral_Iio] at hs
    rw [integral_Iic_eq_integral_Iio] at h2
    linarith
  have hdec : ∫ y in Iio (-x), f y = 1 / 2 + ∫ y in (0:ℝ)..(-x), f y := by
    have := intervalIntegral.integral_Iic_sub_Iic (μ := volume) (f := f) (a := 0) (b := -x)
      hint.integrableOn hint.integrableOn
    simp only [integral_Iic_eq_integral_Iio] at this
    linarith
  have hneg_int : ∫ y in (0:ℝ)..(-x), f y = -∫ y in (0:ℝ)..x, f y := by
    have h1' : ∫ y in (0:ℝ)..x, f (-y) = ∫ y in (-x)..(-0), f y :=
      intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := x)
    simp only [hf_even, neg_zero] at h1'
    rw [intervalIntegral.integral_symm (-x) 0, h1']
  rw [hA, hdec, hneg_int, h1]
  ring

/-- Private helper: the `h(x) = ∫ f(y) sign(y+x)` representation of `signShiftMean`. -/
private lemma shift_rep_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hf_nn : ∀ y, 0 ≤ f y)
    (hX : P.map X = volume.withDensity (fun y => ENNReal.ofReal (f y))) (x : ℝ) :
    signShiftMean P X x = ∫ y, f y * Real.sign (y + x) := by
  have hae := shift_ae_meas_aux P X f hX
  have hsign : Measurable (fun y : ℝ => Real.sign (y + x)) :=
    shift_meas_sign_aux.comp (measurable_id.add_const x)
  have hpush := integral_map hae hsign.aestronglyMeasurable
  unfold signShiftMean
  rw [← hpush, hX]
  have hwd := integral_withDensity_eq_integral_toReal_smul (μ := volume)
    (f := fun y => ENNReal.ofReal (f y)) (ENNReal.measurable_ofReal.comp hf)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (fun y => Real.sign (y + x))
  refine hwd.trans (integral_congr_ae (Eventually.of_forall fun y => ?_))
  simp [smul_eq_mul, ENNReal.toReal_ofReal (hf_nn y)]

/-- `lem:app-sgd-shift` (snapshot `cr-2026-10-23`). LaTeX statement, verbatim:
```latex
\begin{lemma}[Small shifts]\label{lem:app-sgd-shift}
Let $X$ have an even density $f$, and put $h(x)\defeq\EE\sign(X+x)$ for real $x$.
\begin{enumerate}[label=(\roman*)]
\item For every real $x$, with oriented integrals,
\[
h(x)=2\int_0^xf(y)\,\dif y .
\]
\item If $a>0$, $\alpha>0$, $L_f\ge0$ and $\abs{f(y)-f(0)}\le L_f\abs y^\alpha$ for $\abs y\le a$, then
\[
\abs{h(x)-2xf(0)}\le\frac{2L_f}{\alpha+1}\abs x^{\alpha+1}\qquad(\abs x\le a).
\]
\item If $f$ is continuously differentiable on $[-a,a]$ with a
$K_f$-Lipschitz derivative, then
$\abs{h(x)-2xf(0)}\le\frac{K_f}3\abs x^3$ for $\abs x\le a$.
\item If $X\sim\mathcal N(0,\sigma^2)$ with $\sigma>0$, then for every real $x$
\begin{equation}\label{eqn:app-sgd-gauss-shift}
\Big|h(x)-\sqrt{\frac2\pi}\,\frac x\sigma\Big|\le\frac{\abs x^3}{3\sqrt{2\pi}\,\sigma^3}.
\end{equation}
\end{enumerate}
\end{lemma}
```

Part (i) of `lem:app-sgd-shift`: `h(x) = 2 ∫₀ˣ f`, with oriented integrals, for every real
`x`. -/
theorem lem_app_sgd_shift_i {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hf_nn : ∀ y, 0 ≤ f y) (hf_even : ∀ y, f (-y) = f y)
    (hX : P.map X = volume.withDensity (fun y => ENNReal.ofReal (f y))) (x : ℝ) :
    signShiftMean P X x = 2 * ∫ y in (0:ℝ)..x, f y := by
  obtain ⟨hint, hint1⟩ := shift_density_aux P X f hf hf_nn hX
  rw [shift_rep_aux P X f hf hf_nn hX x]
  exact shift_core_aux f hf_even hint hint1 x

/-- Private helper: the one-sided bound `|∫₀ᵘ ψ| ≤ L u^(α+1)/(α+1)` for `0 ≤ u ≤ a`. -/
private lemma shift_bound_aux (ψ : ℝ → ℝ) (a α L u : ℝ) (hα : 0 < α) (hL : 0 ≤ L)
    (hu0 : 0 ≤ u) (hψ : ∀ y : ℝ, |y| ≤ a → |ψ y| ≤ L * |y| ^ α) (hua : u ≤ a) :
    |∫ y in (0:ℝ)..u, ψ y| ≤ L * u ^ (α + 1) / (α + 1) := by
  have hb : IntervalIntegrable (fun t : ℝ => L * t ^ α) volume 0 u :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1:ℝ) < α)).const_mul L
  have h := intervalIntegral.norm_integral_le_of_norm_le hu0
    (Eventually.of_forall fun t => fun (ht : t ∈ Ioc 0 u) => by
      have ht0 : 0 < t := ht.1
      have hta : t ≤ a := le_trans ht.2 hua
      have := hψ t (by rw [abs_of_pos ht0]; exact hta)
      rw [Real.norm_eq_abs]
      rwa [abs_of_pos ht0] at this) hb
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
    Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < α + 1)), Real.norm_eq_abs] at h
  exact h.trans_eq (by ring)

/-- `lem:app-sgd-shift` (snapshot `cr-2026-10-23`). LaTeX statement, verbatim:
```latex
\begin{lemma}[Small shifts]\label{lem:app-sgd-shift}
Let $X$ have an even density $f$, and put $h(x)\defeq\EE\sign(X+x)$ for real $x$.
\begin{enumerate}[label=(\roman*)]
\item For every real $x$, with oriented integrals,
\[
h(x)=2\int_0^xf(y)\,\dif y .
\]
\item If $a>0$, $\alpha>0$, $L_f\ge0$ and $\abs{f(y)-f(0)}\le L_f\abs y^\alpha$ for $\abs y\le a$, then
\[
\abs{h(x)-2xf(0)}\le\frac{2L_f}{\alpha+1}\abs x^{\alpha+1}\qquad(\abs x\le a).
\]
\item If $f$ is continuously differentiable on $[-a,a]$ with a
$K_f$-Lipschitz derivative, then
$\abs{h(x)-2xf(0)}\le\frac{K_f}3\abs x^3$ for $\abs x\le a$.
\item If $X\sim\mathcal N(0,\sigma^2)$ with $\sigma>0$, then for every real $x$
\begin{equation}\label{eqn:app-sgd-gauss-shift}
\Big|h(x)-\sqrt{\frac2\pi}\,\frac x\sigma\Big|\le\frac{\abs x^3}{3\sqrt{2\pi}\,\sigma^3}.
\end{equation}
\end{enumerate}
\end{lemma}
```

Part (ii) of `lem:app-sgd-shift`: if `a > 0`, `α > 0`, `L_f ≥ 0` and
`|f y - f 0| ≤ L_f |y|^α` for `|y| ≤ a`, then `|h x - 2 x f(0)| ≤ (2 L_f / (α + 1)) |x|^(α+1)` for `|x| ≤ a`. -/
theorem lem_app_sgd_shift_ii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hf_nn : ∀ y, 0 ≤ f y) (hf_even : ∀ y, f (-y) = f y)
    (hX : P.map X = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (a α L : ℝ) (ha : 0 < a) (hα : 0 < α) (hL : 0 ≤ L)
    (hlip : ∀ y : ℝ, |y| ≤ a → |f y - f 0| ≤ L * |y| ^ α) :
    ∀ x : ℝ, |x| ≤ a →
      |signShiftMean P X x - 2 * x * f 0| ≤ 2 * L / (α + 1) * |x| ^ (α + 1) := by
  intro x hx
  obtain ⟨hint, _⟩ := shift_density_aux P X f hf hf_nn hX
  have hi := lem_app_sgd_shift_i P X f hf hf_nn hf_even hX x
  have hdiff : signShiftMean P X x - 2 * x * f 0 = 2 * ∫ y in (0:ℝ)..x, (f y - f 0) := by
    rw [hi, intervalIntegral.integral_sub hint.intervalIntegrable intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp
    ring
  have key : |∫ y in (0:ℝ)..x, (f y - f 0)| ≤ L * |x| ^ (α + 1) / (α + 1) := by
    rcases le_total 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0]
      exact shift_bound_aux (fun y => f y - f 0) a α L x hα hL hx0 hlip
        (le_trans (le_abs_self x) hx)
    · have hneg : ∫ y in (0:ℝ)..x, (f y - f 0) = -∫ y in (0:ℝ)..(-x), (f y - f 0) := by
        have h1' : ∫ y in (0:ℝ)..(-x), (f (-y) - f 0) = ∫ y in (-(-x))..(-0), (f y - f 0) :=
          intervalIntegral.integral_comp_neg (f := fun y => f y - f 0) (a := 0) (b := -x)
        simp only [hf_even, neg_neg, neg_zero] at h1'
        rw [intervalIntegral.integral_symm x 0, ← h1']
      rw [hneg, abs_neg, abs_of_nonpos hx0]
      exact shift_bound_aux (fun y => f y - f 0) a α L (-x) hα hL (by linarith)
        (fun y hy => hlip y hy) (le_trans (neg_le_abs x) hx)
  rw [hdiff, abs_mul, abs_two]
  calc 2 * |∫ y in (0:ℝ)..x, (f y - f 0)| ≤ 2 * (L * |x| ^ (α + 1) / (α + 1)) :=
        mul_le_mul_of_nonneg_left key (by norm_num)
    _ = 2 * L / (α + 1) * |x| ^ (α + 1) := by ring

/-- `lem:app-sgd-shift` (snapshot `cr-2026-10-23`). LaTeX statement, verbatim:
```latex
\begin{lemma}[Small shifts]\label{lem:app-sgd-shift}
Let $X$ have an even density $f$, and put $h(x)\defeq\EE\sign(X+x)$ for real $x$.
\begin{enumerate}[label=(\roman*)]
\item For every real $x$, with oriented integrals,
\[
h(x)=2\int_0^xf(y)\,\dif y .
\]
\item If $a>0$, $\alpha>0$, $L_f\ge0$ and $\abs{f(y)-f(0)}\le L_f\abs y^\alpha$ for $\abs y\le a$, then
\[
\abs{h(x)-2xf(0)}\le\frac{2L_f}{\alpha+1}\abs x^{\alpha+1}\qquad(\abs x\le a).
\]
\item If $f$ is continuously differentiable on $[-a,a]$ with a
$K_f$-Lipschitz derivative, then
$\abs{h(x)-2xf(0)}\le\frac{K_f}3\abs x^3$ for $\abs x\le a$.
\item If $X\sim\mathcal N(0,\sigma^2)$ with $\sigma>0$, then for every real $x$
\begin{equation}\label{eqn:app-sgd-gauss-shift}
\Big|h(x)-\sqrt{\frac2\pi}\,\frac x\sigma\Big|\le\frac{\abs x^3}{3\sqrt{2\pi}\,\sigma^3}.
\end{equation}
\end{enumerate}
\end{lemma}
```

Part (iii) of `lem:app-sgd-shift`: if `f` is continuously differentiable on `[-a, a]` with a
`K_f`-Lipschitz derivative there, then `|h x - 2 x f(0)| ≤ (K_f / 3) |x|³` for `|x| ≤ a`.
The derivative is `derivWithin f (Icc (-a) a)`, so the endpoints are read one-sidedly. -/
theorem lem_app_sgd_shift_iii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hf_nn : ∀ y, 0 ≤ f y) (hf_even : ∀ y, f (-y) = f y)
    (hX : P.map X = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (a K : ℝ) (hC1 : ContDiffOn ℝ 1 f (Icc (-a) a))
    (hLip : ∀ y ∈ Icc (-a) a, ∀ z ∈ Icc (-a) a,
      |derivWithin f (Icc (-a) a) y - derivWithin f (Icc (-a) a) z| ≤ K * |y - z|) :
    ∀ x : ℝ, |x| ≤ a → |signShiftMean P X x - 2 * x * f 0| ≤ K / 3 * |x| ^ 3 := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · intro x hx
    exact absurd (le_trans (abs_nonneg x) hx) (not_le.2 ha)
  · subst ha
    intro x hx
    have hx0 : x = 0 := abs_nonpos_iff.1 hx
    subst hx0
    have h0 := lem_app_sgd_shift_i P X f hf hf_nn hf_even hX 0
    simp [h0]
  · have hcont : ContinuousOn f (Icc (-a) a) := hC1.continuousOn
    have hdiff : DifferentiableOn ℝ f (Icc (-a) a) := hC1.differentiableOn (by norm_num)
    have hint_eq : ∀ t ∈ Ioo (-a) a, deriv f t = derivWithin f (Icc (-a) a) t := fun t ht =>
      (derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)).symm
    have hdifft : ∀ t ∈ Ioo (-a) a, DifferentiableAt ℝ f t := fun t ht =>
      hdiff.differentiableAt (Icc_mem_nhds ht.1 ht.2)
    -- the derivative of an even function vanishes at 0
    have hd0 : derivWithin f (Icc (-a) a) 0 = 0 := by
      have h0mem : (0:ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
      rw [← hint_eq 0 h0mem]
      have hfe : (fun y => f (-y)) = f := funext hf_even
      have h := deriv_comp_neg (f := f) (x := (0:ℝ))
      rw [hfe, neg_zero] at h
      linarith
    -- |f'(t)| ≤ K t on [0, a]
    have hbound : ∀ t ∈ Icc (0:ℝ) a, |derivWithin f (Icc (-a) a) t| ≤ K * t := by
      intro t ht
      have h := hLip t ⟨by linarith [ht.1], ht.2⟩ 0 ⟨by linarith, ha.le⟩
      simp only [hd0, sub_zero, abs_of_nonneg ht.1] at h
      exact h
    have hK : 0 ≤ K := by
      have h := hLip a ⟨by linarith, le_refl a⟩ (-a) ⟨le_refl (-a), by linarith⟩
      have h2 : |a - -a| = 2 * a := by rw [abs_of_pos (by linarith)]; ring
      rw [h2] at h
      have h3 := abs_nonneg (derivWithin f (Icc (-a) a) a - derivWithin f (Icc (-a) a) (-a))
      by_contra hneg
      push_neg at hneg
      nlinarith
    have hψ1 : ∀ t ∈ Ioo (0:ℝ) a,
        HasDerivAt (fun t => f t - f 0 - K / 2 * t ^ 2) (deriv f t - K * t) t := by
      intro t ht
      have hf' : HasDerivAt f (deriv f t) t := (hdifft t ⟨by linarith [ht.1], ht.2⟩).hasDerivAt
      have h2 := (hasDerivAt_pow 2 t).const_mul (K / 2)
      have := (hf'.sub_const (f 0)).sub h2
      convert this using 1
      norm_num <;> ring
    have hψ2 : ∀ t ∈ Ioo (0:ℝ) a,
        HasDerivAt (fun t => f t - f 0 + K / 2 * t ^ 2) (deriv f t + K * t) t := by
      intro t ht
      have hf' : HasDerivAt f (deriv f t) t := (hdifft t ⟨by linarith [ht.1], ht.2⟩).hasDerivAt
      have h2 := (hasDerivAt_pow 2 t).const_mul (K / 2)
      have := (hf'.sub_const (f 0)).add h2
      convert this using 1
      norm_num <;> ring
    have hcont0' : ContinuousOn f (Icc 0 a) := hcont.mono (Icc_subset_Icc (by linarith) le_rfl)
    have hcont0 : ContinuousOn (fun t => f t - f 0 - K / 2 * t ^ 2) (Icc 0 a) := by fun_prop
    have hcont0'' : ContinuousOn (fun t => f t - f 0 + K / 2 * t ^ 2) (Icc 0 a) := by fun_prop
    have hanti : AntitoneOn (fun t => f t - f 0 - K / 2 * t ^ 2) (Icc 0 a) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 a) hcont0
      · rw [interior_Icc]
        intro t ht
        exact (hψ1 t ht).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        rw [(hψ1 t ht).deriv]
        have hb := hbound t (Ioo_subset_Icc_self ht)
        have hd := hint_eq t ⟨by linarith [ht.1], ht.2⟩
        linarith [le_abs_self (derivWithin f (Icc (-a) a) t)]
    have hmono : MonotoneOn (fun t => f t - f 0 + K / 2 * t ^ 2) (Icc 0 a) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 a) hcont0''
      · rw [interior_Icc]
        intro t ht
        exact (hψ2 t ht).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        rw [(hψ2 t ht).deriv]
        have hb := hbound t (Ioo_subset_Icc_self ht)
        have hd := hint_eq t ⟨by linarith [ht.1], ht.2⟩
        linarith [neg_abs_le (derivWithin f (Icc (-a) a) t)]
    -- |f t - f 0| ≤ (K/2) t² on [0, a], then on [-a, a] by evenness
    have hquad : ∀ t ∈ Icc (0:ℝ) a, |f t - f 0| ≤ K / 2 * t ^ 2 := by
      intro t ht
      have h1 : f t - f 0 - K / 2 * t ^ 2 ≤ f 0 - f 0 - K / 2 * (0:ℝ) ^ 2 :=
        hanti ⟨le_refl 0, ha.le⟩ ht ht.1
      have h2 : f 0 - f 0 + K / 2 * (0:ℝ) ^ 2 ≤ f t - f 0 + K / 2 * t ^ 2 :=
        hmono ⟨le_refl 0, ha.le⟩ ht ht.1
      rw [abs_le]
      constructor <;> nlinarith
    have hlip2 : ∀ y : ℝ, |y| ≤ a → |f y - f 0| ≤ K / 2 * |y| ^ (2:ℝ) := by
      intro y hy
      rw [Real.rpow_two, sq_abs]
      rcases le_total 0 y with hy0 | hy0
      · exact hquad y ⟨hy0, (abs_le.1 hy).2⟩
      · have hmem : -y ∈ Icc (0:ℝ) a := ⟨by linarith, by linarith [(abs_le.1 hy).1]⟩
        have h := hquad (-y) hmem
        rw [hf_even y, neg_sq] at h
        exact h
    have hL : 0 ≤ K / 2 := by linarith
    have hii := lem_app_sgd_shift_ii P X f hf hf_nn hf_even hX a 2 (K / 2) ha (by norm_num) hL hlip2
    intro x hx
    have h := hii x hx
    have e : (2:ℝ) + 1 = ((3:ℕ):ℝ) := by norm_num
    rw [e, Real.rpow_natCast] at h
    refine h.trans (le_of_eq ?_)
    push_cast
    ring

/-- `lem:app-sgd-shift` (snapshot `cr-2026-10-23`). LaTeX statement, verbatim:
```latex
\begin{lemma}[Small shifts]\label{lem:app-sgd-shift}
Let $X$ have an even density $f$, and put $h(x)\defeq\EE\sign(X+x)$ for real $x$.
\begin{enumerate}[label=(\roman*)]
\item For every real $x$, with oriented integrals,
\[
h(x)=2\int_0^xf(y)\,\dif y .
\]
\item If $a>0$, $\alpha>0$, $L_f\ge0$ and $\abs{f(y)-f(0)}\le L_f\abs y^\alpha$ for $\abs y\le a$, then
\[
\abs{h(x)-2xf(0)}\le\frac{2L_f}{\alpha+1}\abs x^{\alpha+1}\qquad(\abs x\le a).
\]
\item If $f$ is continuously differentiable on $[-a,a]$ with a
$K_f$-Lipschitz derivative, then
$\abs{h(x)-2xf(0)}\le\frac{K_f}3\abs x^3$ for $\abs x\le a$.
\item If $X\sim\mathcal N(0,\sigma^2)$ with $\sigma>0$, then for every real $x$
\begin{equation}\label{eqn:app-sgd-gauss-shift}
\Big|h(x)-\sqrt{\frac2\pi}\,\frac x\sigma\Big|\le\frac{\abs x^3}{3\sqrt{2\pi}\,\sigma^3}.
\end{equation}
\end{enumerate}
\end{lemma}
```

Part (iv) of `lem:app-sgd-shift`: if `X ∼ N(0, σ²)` with `σ > 0`, then for every real `x`,
`|h x - √(2/π) x / σ| ≤ |x|³ / (3 √(2π) σ³)`. -/
theorem lem_app_sgd_shift_iv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hX : P.map X = gaussianReal 0 (σ ^ 2).toNNReal) :
    ∀ x : ℝ, |signShiftMean P X x - Real.sqrt (2 / Real.pi) * x / σ|
      ≤ |x| ^ 3 / (3 * Real.sqrt (2 * Real.pi) * σ ^ 3) := by
  intro x
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, f = gaussianPDFReal 0 (σ ^ 2).toNNReal := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (Real.sqrt (2 * Real.pi) * σ)⁻¹ := ⟨_, rfl⟩
  have hv0 : (σ ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; exact pow_pos hσ 2
  have hvR : (((σ ^ 2).toNNReal : NNReal) : ℝ) = σ ^ 2 :=
    Real.coe_toNNReal _ (by positivity)
  have hs : Real.sqrt (2 * Real.pi * σ ^ 2) = Real.sqrt (2 * Real.pi) * σ := by
    rw [Real.sqrt_mul (show (0:ℝ) ≤ 2 * Real.pi by positivity), Real.sqrt_sq hσ.le]
  have hcpos : 0 < c := by
    rw [hcdef]
    exact inv_pos.2 (mul_pos (Real.sqrt_pos.2 (by positivity)) hσ)
  have hf_eq : ∀ y, f y = c * Real.exp (-(y ^ 2 / (2 * σ ^ 2))) := by
    intro y
    rw [hfdef, hcdef]
    unfold gaussianPDFReal
    rw [hvR, hs]
    congr 2
    ring
  have hf0 : f 0 = c := by rw [hf_eq]; simp
  have hX2 : P.map X = volume.withDensity (fun y => ENNReal.ofReal (f y)) := by
    rw [hX, gaussianReal_of_var_ne_zero 0 hv0, hfdef]; rfl
  have hf_meas : Measurable f := by rw [hfdef]; exact measurable_gaussianPDFReal _ _
  have hf_nn : ∀ y, 0 ≤ f y := by intro y; rw [hfdef]; exact gaussianPDFReal_nonneg _ _ _
  have hf_even : ∀ y, f (-y) = f y := by intro y; rw [hf_eq, hf_eq, neg_sq]
  have hsqrt : Real.sqrt (2 / Real.pi) = 2 / Real.sqrt (2 * Real.pi) := by
    have hp : 0 < 2 * Real.pi := by positivity
    rw [eq_div_iff (Real.sqrt_pos.2 hp).ne',
      ← Real.sqrt_mul (show (0:ℝ) ≤ 2 / Real.pi by positivity)]
    rw [show 2 / Real.pi * (2 * Real.pi) = 2 ^ 2 by
      rw [div_mul_eq_mul_div, div_eq_iff Real.pi_pos.ne']; ring]
    rw [Real.sqrt_sq (by norm_num)]
  -- |f y - f 0| ≤ (c / (2σ²)) y² from 0 ≤ 1 - e^{-u} ≤ u
  have hlipG : ∀ y : ℝ, |f y - f 0| ≤ c / (2 * σ ^ 2) * |y| ^ (2:ℝ) := by
    intro y
    rw [Real.rpow_two, sq_abs, hf0, hf_eq y]
    have hu : 0 ≤ y ^ 2 / (2 * σ ^ 2) := by positivity
    have he1 : Real.exp (-(y ^ 2 / (2 * σ ^ 2))) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have he2 := Real.add_one_le_exp (-(y ^ 2 / (2 * σ ^ 2)))
    rw [show c * Real.exp (-(y ^ 2 / (2 * σ ^ 2))) - c
        = -(c * (1 - Real.exp (-(y ^ 2 / (2 * σ ^ 2))))) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg hcpos.le (by linarith))]
    calc c * (1 - Real.exp (-(y ^ 2 / (2 * σ ^ 2))))
        ≤ c * (y ^ 2 / (2 * σ ^ 2)) := mul_le_mul_of_nonneg_left (by linarith) hcpos.le
      _ = c / (2 * σ ^ 2) * y ^ 2 := by ring
  have hL : 0 ≤ c / (2 * σ ^ 2) := div_nonneg hcpos.le (by positivity)
  have hii := lem_app_sgd_shift_ii P X f hf_meas hf_nn hf_even hX2 (|x| + 1) 2
    (c / (2 * σ ^ 2)) (by positivity) (by norm_num) hL (fun y _ => hlipG y)
  have h := hii x (by linarith [abs_nonneg x])
  have e1 : 2 * x * f 0 = Real.sqrt (2 / Real.pi) * x / σ := by
    rw [hf0, hsqrt, hcdef]; ring
  rw [e1] at h
  refine h.trans (le_of_eq ?_)
  rw [show ((2:ℝ) + 1) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast, hcdef]
  field_simp
  ring

end Muon.SignSGD

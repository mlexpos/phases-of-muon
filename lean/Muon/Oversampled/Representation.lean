import Mathlib
import Muon.Oversampled.Profile

/-!
# Oversampled representation layer (Appendix G2, work package L-G2.2)

Source of record: snapshot `cr-2026-10-22`, `sections/12-oversampled/section.tex`.
Scope: `lem:app-os-integrals`, `lem:app-os-cparam`, `lem:app-os-repr` (the hub),
`lem:app-os-average`, `lem:app-os-defect`, `lem:app-os-count`, and part (i) of
`cor:app-os-identity`. Part (ii) of the corollary belongs to L-G2.7.

Imports the frozen L-G2.1 profile layer (`Muon.Oversampled.Profile`) and reuses
`mNu`, `profileRoot`, `dOsSq`, `varpi`, `sqrtEff` from it. The square-case profile is
`dOsSq ν μ = dOs ν 1 μ 0`.

Measure representation (fixed by L-G2.1): `ν : Measure ℝ`, `[IsProbabilityMeasure ν]`,
`ν (Set.Iio 0) = 0`. Results that use `profileRoot` at `r = 1` assume the same hypotheses.
-/

open MeasureTheory Set Filter Topology

namespace Muon.Oversampled

noncomputable section

/-- Υ_ν(c) := c (1 - m_ν(c)) = ∫ c² ν(dx)/(c+x) (`eqn:app-os-Upsilon`, the displayed
definition of the standing setup of the square case). Lean takes the first expression.

Statement verbatim:

\begin{equation}\label{eqn:app-os-Upsilon}
\Upsilon_\nu(c)\defeq c\,\big(1-m_\nu(c)\big)=\int\frac{c^2\,\nu(\dif x)}{c+x}=c^2S_\nu(-c)\qquad(c>0).
\end{equation}
-/
def Upsilon (ν : Measure ℝ) (c : ℝ) : ℝ :=
  c * (1 - mNu ν c)

/-- c_ν := Υ_ν^{-1}, the inverse of `Upsilon ν` on `(0,∞)` (`lem:app-os-cparam`).
`Function.invFunOn` returns an arbitrary value off the image of `Ioi 0`; the statements
below only use it on `Ioi 0`. -/
def cNu (ν : Measure ℝ) (s : ℝ) : ℝ :=
  Function.invFunOn (Upsilon ν) (Ioi (0 : ℝ)) s

/-- The measure ϖ(y) dy on `ℝ` with density `varpi` (`def:app-os-objects`(iii)). `varpi`
vanishes on `(-∞,0]` (since `√y = 0` there), so the measure lives on `(0,∞)`.
It is a probability measure by `lem_app_os_integrals_iv` (`varpiMeasure_univ`); the instance
below is used for Jensen in later files. -/
def varpiMeasure : Measure ℝ :=
  volume.withDensity (fun y : ℝ => ENNReal.ofReal (varpi y))

/-! Private helpers for the mass identity (self-contained, placed before `varpiMeasure_univ`). -/

private lemma os_mass_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => Real.arctan (Real.sqrt y) - Real.sqrt y / (1 + y))
      (Real.sqrt y / (1 + y) ^ 2) y := by
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt y)) y := Real.hasDerivAt_sqrt hy.ne'
  have ha := hs.arctan
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 y := (hasDerivAt_id y).const_add 1
  have hb := hs.div h1 (ne_of_gt (by linarith))
  convert ha.sub hb using 1
  have hpos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  obtain ⟨s, hs_def⟩ : ∃ s, Real.sqrt y = s := ⟨_, rfl⟩
  rw [hs_def] at hpos hsq ⊢
  subst hsq
  have hne : (1 + s ^ 2) ≠ 0 := by positivity
  have hsne : s ≠ 0 := hpos.ne'
  field_simp
  ring

private lemma os_mass_cont :
    ContinuousWithinAt (fun y : ℝ => Real.arctan (Real.sqrt y) - Real.sqrt y / (1 + y))
      (Ici 0) 0 := by
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.sub
  · exact (Real.continuous_arctan.comp Real.continuous_sqrt).continuousAt
  · exact ContinuousAt.div Real.continuous_sqrt.continuousAt
      (by fun_prop : Continuous fun y : ℝ => 1 + y).continuousAt (by norm_num)

private lemma os_mass_tendsto :
    Tendsto (fun y : ℝ => Real.arctan (Real.sqrt y) - Real.sqrt y / (1 + y)) atTop
      (𝓝 (Real.pi / 2)) := by
  have hsq : Tendsto (fun y : ℝ => Real.sqrt y / (1 + y)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun y : ℝ => (Real.sqrt y)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
    · exact Filter.eventually_atTop.2 ⟨0, fun y hy => by
        have : (0 : ℝ) < 1 + y := by linarith
        exact div_nonneg (Real.sqrt_nonneg y) this.le⟩
    · refine Filter.eventually_atTop.2 ⟨1, fun y hy => ?_⟩
      have hy0 : (0 : ℝ) < y := by linarith
      have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + y), inv_mul_eq_div, le_div_iff₀ hs]
      nlinarith [Real.mul_self_sqrt hy0.le]
  have h1 : Tendsto (fun y : ℝ => Real.arctan (Real.sqrt y)) atTop (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp Real.tendsto_sqrt_atTop
  have := h1.sub hsq
  rwa [sub_zero] at this

private lemma os_mass_integrable :
    IntegrableOn (fun y : ℝ => Real.sqrt y / (1 + y) ^ 2) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg (g := fun y : ℝ => Real.arctan (Real.sqrt y) - Real.sqrt y / (1 + y))
    (g' := fun x => Real.sqrt x / (1 + x) ^ 2) os_mass_cont
    (fun x hx => os_mass_hasDerivAt hx) (fun x _ => by positivity) os_mass_tendsto

private lemma os_mass_integral :
    ∫ y in Ioi (0 : ℝ), Real.sqrt y / (1 + y) ^ 2 = Real.pi / 2 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (g := fun y : ℝ => Real.arctan (Real.sqrt y) - Real.sqrt y / (1 + y))
    (g' := fun x => Real.sqrt x / (1 + x) ^ 2) os_mass_cont
    (fun x hx => os_mass_hasDerivAt hx) (fun x _ => by positivity) os_mass_tendsto]
  norm_num

private lemma os_mass_varpi_eq (y : ℝ) :
    varpi y = (2 / Real.pi) * (Real.sqrt y / (1 + y) ^ 2) := by
  unfold varpi
  ring

private lemma os_mass_one : ∫ y in Ioi (0 : ℝ), varpi y = 1 := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => os_mass_varpi_eq y),
    integral_const_mul, os_mass_integral]
  field_simp

/-- Helper for `lem:app-os-integrals`(iv): the measure `varpiMeasure` has total mass one.
Proof body is `sorry`; it is the withDensity form of the integral identity of part (iv). -/
theorem varpiMeasure_univ : varpiMeasure Set.univ = 1 := by
  have hz : ∀ x, x ∉ Ioi (0 : ℝ) → varpi x = 0 := fun x hx => by
    have hx' : x ≤ 0 := by simpa using hx
    rw [os_mass_varpi_eq, Real.sqrt_eq_zero'.mpr hx']
    simp
  have hsupp : Function.support varpi ⊆ Ioi (0 : ℝ) := by
    intro y hy
    rw [Function.mem_support] at hy
    by_contra h
    exact hy (hz y h)
  have hA : IntegrableOn (fun y : ℝ => (2 / Real.pi) * (Real.sqrt y / (1 + y) ^ 2)) (Ioi (0 : ℝ)) :=
    os_mass_integrable.const_mul _
  have hint1 : IntegrableOn varpi (Ioi (0 : ℝ)) :=
    hA.congr_fun (fun y _ => (os_mass_varpi_eq y).symm) measurableSet_Ioi
  have hint : Integrable varpi :=
    (integrableOn_iff_integrable_of_support_subset hsupp).mp hint1
  have hnn : ∀ y, (0 : ℝ) ≤ varpi y := fun y => by
    rw [os_mass_varpi_eq]
    positivity
  have hzint : ∫ x in Ioi (0 : ℝ), varpi x = ∫ x, varpi x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hz
  unfold varpiMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn), ← hzint, os_mass_one,
    ENNReal.ofReal_one]

instance varpiMeasure_isProbabilityMeasure : IsProbabilityMeasure varpiMeasure :=
  ⟨varpiMeasure_univ⟩

/-- The averaged ratio `m^ϖ_ν(μ) := ∫_0^∞ ϖ(y) m_ν(μ y) dy` (`eqn:app-os-mbar`, for `μ > 0`).

Statement verbatim:

\begin{equation}\label{eqn:app-os-mbar}
m^\varpi_\nu(\mu)\defeq\int_0^\infty\varpi(y)\,m_\nu(\mu y)\,\dif y=\int\frac{x\,\nu(\dif x)}{(\sqrt\mu+\sqrt x)^2}\le m_\nu(\mu).
\end{equation}
-/
def mBarNu (ν : Measure ℝ) (mu : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), varpi y * mNu ν (mu * y)

/-- The smoothed count `𝗌_ν(μ) := 1 - m^ϖ_ν(μ)` (`eqn:app-os-count`, for `μ > 0`).

Statement verbatim:

\begin{equation}\label{eqn:app-os-count}
\mathsf s_\nu(\mu)\defeq1-m^\varpi_\nu(\mu)=\int\frac{1+2\sqrt{x/\mu}}{\big(1+\sqrt{x/\mu}\big)^2}\,\nu(\dif x)\in(0,1].
\end{equation}
-/
def smoothCount (ν : Measure ℝ) (mu : ℝ) : ℝ :=
  1 - mBarNu ν mu

/-! ## Elementary integrals (`lem:app-os-integrals`) -/

/-- Antiderivative of `√y/(1+y)²` on `(0,∞)`: `arctan √y - √y/(1+y)`. -/
private lemma os_antideriv_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => Real.arctan (Real.sqrt y) - Real.sqrt y / (1 + y))
      (Real.sqrt y / (1 + y) ^ 2) y := by
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt y)) y := Real.hasDerivAt_sqrt hy.ne'
  have ha := hs.arctan
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 y := (hasDerivAt_id y).const_add 1
  have hb := hs.div h1 (ne_of_gt (by linarith))
  convert ha.sub hb using 1
  have hpos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  obtain ⟨s, hs_def⟩ : ∃ s, Real.sqrt y = s := ⟨_, rfl⟩
  rw [hs_def] at hpos hsq ⊢
  subst hsq
  have hne : (1 + s ^ 2) ≠ 0 := by positivity
  have hsne : s ≠ 0 := hpos.ne'
  field_simp
  ring

/-- Label `lem:app-os-integrals`, part (i) (∫_0^1 √y/(1+y)² dy = π/4 - 1/2). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Elementary integrals]\label{lem:app-os-integrals}
One has
\[
\int_0^1\frac{\sqrt y\,\dif y}{(1+y)^2}=\frac\pi4-\frac12,\qquad
\int_1^\infty\frac{\sqrt y\,\dif y}{(1+y)^2}=\frac\pi4+\frac12,\qquad
\int_0^1\frac{y\,\dif y}{(1+y)^2}=\log2-\frac12 .
\]
In particular $\varpi$ is a probability density on $(0,\infty)$, and for $\mu>0$
\[
\frac{\sqrt2}{\pi}\,\mu\int_0^\infty\frac{\sqrt c\,\dif c}{(c+\mu)^2}=\sqrt{\mu/2}.
\]
\end{lemma}
-/
theorem lem_app_os_integrals_i
 :
    ∫ y in Icc (0 : ℝ) 1, Real.sqrt y / (1 + y) ^ 2 = Real.pi / 4 - 1 / 2 := by
  have hcont : ContinuousOn (fun y : ℝ => Real.arctan (Real.sqrt y) - Real.sqrt y / (1 + y))
      (Icc 0 1) := by
    apply ContinuousOn.sub
    · exact (Real.continuous_arctan.comp Real.continuous_sqrt).continuousOn
    · apply ContinuousOn.div Real.continuous_sqrt.continuousOn
        (by fun_prop : Continuous fun y : ℝ => 1 + y).continuousOn
      intro y hy
      exact ne_of_gt (by linarith [hy.1])
  have hint : IntervalIntegrable (fun y : ℝ => Real.sqrt y / (1 + y) ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    apply ContinuousOn.div Real.continuous_sqrt.continuousOn
      (by fun_prop : Continuous fun y : ℝ => (1 + y) ^ 2).continuousOn
    intro y hy
    exact pow_ne_zero 2 (ne_of_gt (by linarith [hy.1]))
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont
      (fun y hy => os_antideriv_hasDerivAt hy.1) hint]
  norm_num [Real.arctan_one]

/-- Label `lem:app-os-integrals`, part (ii) (∫_1^∞ √y/(1+y)² dy = π/4 + 1/2). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Elementary integrals]\label{lem:app-os-integrals}
One has
\[
\int_0^1\frac{\sqrt y\,\dif y}{(1+y)^2}=\frac\pi4-\frac12,\qquad
\int_1^\infty\frac{\sqrt y\,\dif y}{(1+y)^2}=\frac\pi4+\frac12,\qquad
\int_0^1\frac{y\,\dif y}{(1+y)^2}=\log2-\frac12 .
\]
In particular $\varpi$ is a probability density on $(0,\infty)$, and for $\mu>0$
\[
\frac{\sqrt2}{\pi}\,\mu\int_0^\infty\frac{\sqrt c\,\dif c}{(c+\mu)^2}=\sqrt{\mu/2}.
\]
\end{lemma}
-/
theorem lem_app_os_integrals_ii
 :
    ∫ y in Ioi (1 : ℝ), Real.sqrt y / (1 + y) ^ 2 = Real.pi / 4 + 1 / 2 := by
  have hcont : ContinuousWithinAt (fun y : ℝ => Real.arctan (Real.sqrt y) - Real.sqrt y / (1 + y))
      (Ici 1) 1 :=
    (os_antideriv_hasDerivAt zero_lt_one).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi (1 : ℝ), HasDerivAt
      (fun y : ℝ => Real.arctan (Real.sqrt y) - Real.sqrt y / (1 + y))
      (Real.sqrt x / (1 + x) ^ 2) x :=
    fun x hx => os_antideriv_hasDerivAt (zero_lt_one.trans hx)
  have hpos : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ Real.sqrt x / (1 + x) ^ 2 := fun x _ => by positivity
  have hsq : Tendsto (fun y : ℝ => Real.sqrt y / (1 + y)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun y : ℝ => (Real.sqrt y)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
    · exact Filter.eventually_atTop.2 ⟨0, fun y hy => by
        have : (0 : ℝ) < 1 + y := by linarith
        exact div_nonneg (Real.sqrt_nonneg y) this.le⟩
    · refine Filter.eventually_atTop.2 ⟨1, fun y hy => ?_⟩
      have hy0 : (0 : ℝ) < y := by linarith
      have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + y), inv_mul_eq_div, le_div_iff₀ hs]
      nlinarith [Real.mul_self_sqrt hy0.le]
  have htend : Tendsto (fun y : ℝ => Real.arctan (Real.sqrt y) - Real.sqrt y / (1 + y)) atTop
      (𝓝 (Real.pi / 2)) := by
    have h1 : Tendsto (fun y : ℝ => Real.arctan (Real.sqrt y)) atTop (𝓝 (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp Real.tendsto_sqrt_atTop
    have := h1.sub hsq
    rwa [sub_zero] at this
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (g' := fun x => Real.sqrt x / (1 + x) ^ 2)
    hcont hderiv hpos htend]
  norm_num [Real.arctan_one]
  ring

/-- Label `lem:app-os-integrals`, part (iii) (∫_0^1 y/(1+y)² dy = log 2 - 1/2). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Elementary integrals]\label{lem:app-os-integrals}
One has
\[
\int_0^1\frac{\sqrt y\,\dif y}{(1+y)^2}=\frac\pi4-\frac12,\qquad
\int_1^\infty\frac{\sqrt y\,\dif y}{(1+y)^2}=\frac\pi4+\frac12,\qquad
\int_0^1\frac{y\,\dif y}{(1+y)^2}=\log2-\frac12 .
\]
In particular $\varpi$ is a probability density on $(0,\infty)$, and for $\mu>0$
\[
\frac{\sqrt2}{\pi}\,\mu\int_0^\infty\frac{\sqrt c\,\dif c}{(c+\mu)^2}=\sqrt{\mu/2}.
\]
\end{lemma}
-/
theorem lem_app_os_integrals_iii
 :
    ∫ y in Icc (0 : ℝ) 1, y / (1 + y) ^ 2 = Real.log 2 - 1 / 2 := by
  have hderiv : ∀ y : ℝ, 0 ≤ y →
      HasDerivAt (fun y : ℝ => Real.log (1 + y) + 1 / (1 + y)) (y / (1 + y) ^ 2) y := by
    intro y hy
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 y := (hasDerivAt_id y).const_add 1
    have hne : (1 + y) ≠ 0 := ne_of_gt (by linarith)
    have hlog := h1.log hne
    have hinv := (hasDerivAt_const y (1 : ℝ)).div h1 hne
    convert hlog.add hinv using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun y : ℝ => Real.log (1 + y) + 1 / (1 + y)) (Icc 0 1) := by
    apply ContinuousOn.add
    · apply ContinuousOn.log (by fun_prop)
      intro y hy
      exact ne_of_gt (by linarith [hy.1])
    · apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro y hy
      exact ne_of_gt (by linarith [hy.1])
  have hint : IntervalIntegrable (fun y : ℝ => y / (1 + y) ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro y hy
    exact pow_ne_zero 2 (ne_of_gt (by linarith [hy.1]))
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont
      (fun y hy => hderiv y hy.1.le) hint]
  norm_num
  ring

/-- Label `lem:app-os-integrals`, part (iv) (ϖ is a probability density on (0,∞)). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Elementary integrals]\label{lem:app-os-integrals}
One has
\[
\int_0^1\frac{\sqrt y\,\dif y}{(1+y)^2}=\frac\pi4-\frac12,\qquad
\int_1^\infty\frac{\sqrt y\,\dif y}{(1+y)^2}=\frac\pi4+\frac12,\qquad
\int_0^1\frac{y\,\dif y}{(1+y)^2}=\log2-\frac12 .
\]
In particular $\varpi$ is a probability density on $(0,\infty)$, and for $\mu>0$
\[
\frac{\sqrt2}{\pi}\,\mu\int_0^\infty\frac{\sqrt c\,\dif c}{(c+\mu)^2}=\sqrt{\mu/2}.
\]
\end{lemma}
-/
theorem lem_app_os_integrals_iv
 :
    (∀ y : ℝ, 0 < y → 0 ≤ varpi y) ∧ ∫ y in Ioi (0 : ℝ), varpi y = 1 := by
  refine ⟨fun y _ => ?_, os_mass_one⟩
  rw [os_mass_varpi_eq]
  positivity

/-- Label `lem:app-os-integrals`, part (v) (for μ > 0, (√2/π) μ ∫_0^∞ √c/(c+μ)² dc = √(μ/2)). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Elementary integrals]\label{lem:app-os-integrals}
One has
\[
\int_0^1\frac{\sqrt y\,\dif y}{(1+y)^2}=\frac\pi4-\frac12,\qquad
\int_1^\infty\frac{\sqrt y\,\dif y}{(1+y)^2}=\frac\pi4+\frac12,\qquad
\int_0^1\frac{y\,\dif y}{(1+y)^2}=\log2-\frac12 .
\]
In particular $\varpi$ is a probability density on $(0,\infty)$, and for $\mu>0$
\[
\frac{\sqrt2}{\pi}\,\mu\int_0^\infty\frac{\sqrt c\,\dif c}{(c+\mu)^2}=\sqrt{\mu/2}.
\]
\end{lemma}
-/
theorem lem_app_os_integrals_v
    {mu : ℝ} (hmu : 0 < mu) :
    Real.sqrt 2 / Real.pi * mu * ∫ c in Ioi (0 : ℝ), Real.sqrt c / (c + mu) ^ 2
      = Real.sqrt (mu / 2) := by
  have h := integral_comp_mul_left_Ioi
    (fun c : ℝ => Real.sqrt c / (c + mu) ^ 2) 0 hmu
  simp only [mul_zero, smul_eq_mul] at h
  have hI : ∫ c in Ioi (0 : ℝ), Real.sqrt c / (c + mu) ^ 2
      = mu * ∫ y in Ioi (0 : ℝ), Real.sqrt (mu * y) / (mu * y + mu) ^ 2 := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hmu.ne', one_mul]
  have hpt : Set.EqOn (fun y : ℝ => Real.sqrt (mu * y) / (mu * y + mu) ^ 2)
      (fun y : ℝ => Real.sqrt mu / mu ^ 2 * (Real.sqrt y / (1 + y) ^ 2)) (Ioi (0 : ℝ)) := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    have hy1 : (1 + y) ≠ 0 := (by linarith : (0 : ℝ) < 1 + y).ne'
    dsimp only
    rw [Real.sqrt_mul hmu.le y, show (mu * y + mu) ^ 2 = mu ^ 2 * (1 + y) ^ 2 by ring]
    field_simp
  have hs2 : Real.sqrt (mu / 2) = Real.sqrt mu * Real.sqrt 2 / 2 := by
    rw [Real.sqrt_div' mu (by norm_num : (0 : ℝ) ≤ 2),
      div_eq_div_iff (Real.sqrt_pos.2 two_pos).ne' two_ne_zero, mul_assoc,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hmu0 : mu ≠ 0 := hmu.ne'
  rw [hI, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    os_mass_integral, hs2]
  field_simp

/-! ## The c-parametrization (`lem:app-os-cparam`) -/

/-! Private helpers for `lem:app-os-cparam` (self-contained copies; the Profile helpers are private). -/

private lemma os_cp_ae_nonneg {ν : Measure ℝ} (hν : ν (Iio 0) = 0) : ∀ᵐ x ∂ν, 0 ≤ x := by
  rw [ae_iff]
  have h : {a : ℝ | ¬ (0 ≤ a)} = Iio 0 := by ext; simp
  rw [h]; exact hν

private lemma os_cp_frac_integrable {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {c : ℝ} (hc : 0 < c) : Integrable (fun x : ℝ => x / (c + x)) ν := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ => x / (c + x)).aestronglyMeasurable
  · filter_upwards [os_cp_ae_nonneg hν] with x hx
    have h2 : 0 < c + x := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hx h2.le)]
    exact (div_le_one h2).2 (by linarith)

private lemma os_cp_upsilon_eq {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {c : ℝ} (hc : 0 < c) : Upsilon ν c = ∫ x, c ^ 2 / (c + x) ∂ν := by
  have hint := os_cp_frac_integrable hν hc
  have h1 : ∫ x, (1 - x / (c + x)) ∂ν = ∫ x, c / (c + x) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [os_cp_ae_nonneg hν] with x hx
    have h2 : (c + x) ≠ 0 := (by linarith : (0 : ℝ) < c + x).ne'
    rw [eq_div_iff h2, sub_mul, div_mul_cancel₀ _ h2]
    ring
  have h2 : ∫ x, (1 - x / (c + x)) ∂ν = 1 - mNu ν c := by
    unfold mNu
    rw [integral_sub (integrable_const (1 : ℝ)) hint, integral_const]
    simp
  have h3 : ∫ x, c ^ 2 / (c + x) ∂ν = ∫ x, c * (c / (c + x)) ∂ν := by
    congr 1; ext x; ring
  unfold Upsilon
  rw [h3, integral_const_mul, ← h2, h1]

private lemma os_cp_bound {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) :
    ‖1 - x ^ 2 / (c + x) ^ 2‖ ≤ 1 := by
  have h2 : 0 < c + x := by linarith
  have hq0 : 0 ≤ x ^ 2 / (c + x) ^ 2 := by positivity
  have hq1 : x ^ 2 / (c + x) ^ 2 ≤ 1 := by
    rw [div_le_one (pow_pos h2 2)]; nlinarith [mul_pos hc hc, mul_nonneg hc.le hx]
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith

private lemma os_cp_fn_hasDerivAt {x : ℝ} (hx : 0 ≤ x) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (fun c : ℝ => c ^ 2 / (c + x)) (1 - x ^ 2 / (c + x) ^ 2) c := by
  have hne : c + x ≠ 0 := (by linarith : (0 : ℝ) < c + x).ne'
  have h := (hasDerivAt_pow 2 c).div ((hasDerivAt_id c).add_const x) hne
  refine h.congr_deriv ?_
  simp only [id]
  field_simp
  ring

private lemma os_cp_integral_hasDerivAt {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    HasDerivAt (fun c : ℝ => ∫ x, c ^ 2 / (c + x) ∂ν)
      (∫ x, (1 - x ^ 2 / (c₀ + x) ^ 2) ∂ν) c₀ := by
  have hF_meas : ∀ᶠ c in 𝓝 c₀, AEStronglyMeasurable (fun x : ℝ => c ^ 2 / (c + x)) ν :=
    Filter.Eventually.of_forall fun c =>
      (by fun_prop : Measurable fun x : ℝ => c ^ 2 / (c + x)).aestronglyMeasurable
  have hF_int : Integrable (fun x : ℝ => c₀ ^ 2 / (c₀ + x)) ν := by
    refine Integrable.mono' (integrable_const c₀) ?_ ?_
    · exact (by fun_prop : Measurable fun x : ℝ => c₀ ^ 2 / (c₀ + x)).aestronglyMeasurable
    · filter_upwards [os_cp_ae_nonneg hν] with x hx
      have h2 : 0 < c₀ + x := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) h2.le), div_le_iff₀ h2]
      nlinarith
  have hF'_meas : AEStronglyMeasurable (fun x : ℝ => 1 - x ^ 2 / (c₀ + x) ^ 2) ν :=
    (by fun_prop : Measurable fun x : ℝ => 1 - x ^ 2 / (c₀ + x) ^ 2).aestronglyMeasurable
  have h_bound : ∀ᵐ x ∂ν, ∀ c ∈ Ioi (0 : ℝ),
      ‖(fun c x : ℝ => 1 - x ^ 2 / (c + x) ^ 2) c x‖ ≤ (fun _ : ℝ => (1 : ℝ)) x := by
    filter_upwards [os_cp_ae_nonneg hν] with x hx c hc
    exact os_cp_bound hx hc
  have h_diff : ∀ᵐ x ∂ν, ∀ c ∈ Ioi (0 : ℝ),
      HasDerivAt (fun c : ℝ => (fun c x : ℝ => c ^ 2 / (c + x)) c x)
        ((fun c x : ℝ => 1 - x ^ 2 / (c + x) ^ 2) c x) c := by
    filter_upwards [os_cp_ae_nonneg hν] with x hx c hc
    exact os_cp_fn_hasDerivAt hx hc
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun c x : ℝ => c ^ 2 / (c + x))
    (F' := fun c x : ℝ => 1 - x ^ 2 / (c + x) ^ 2) (Ioi_mem_nhds hc₀) hF_meas hF_int hF'_meas
    h_bound (integrable_const (1 : ℝ)) h_diff).2

private lemma os_cp_ratio_le {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) : c ^ 2 / (c + x) ≤ c := by
  have h2 : 0 < c + x := by linarith
  rw [div_le_iff₀ h2]; nlinarith [mul_nonneg hc.le hx]

private lemma os_cp_ratio_integrable {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => c ^ 2 / (c + x)) ν := by
  refine Integrable.mono' (integrable_const c) ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ => c ^ 2 / (c + x)).aestronglyMeasurable
  · filter_upwards [os_cp_ae_nonneg hν] with x hx
    have h2 : 0 < c + x := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) h2.le)]
    exact os_cp_ratio_le hx hc

/-- Label `lem:app-os-cparam`, part (i) (Υ_ν is C¹ on (0,∞) with the stated derivative). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[The $c$-parametrization]\label{lem:app-os-cparam}
The function $\Upsilon_\nu$ is continuously differentiable on $(0,\infty)$,
with
\[
\Upsilon_\nu'(c)=\int\Big(1-\frac{x^2}{(c+x)^2}\Big)\nu(\dif x)\in(0,1],
\]
and $0<\Upsilon_\nu(c)\le c$. It tends to $0$ as $c\downarrow0$ and to
$\infty$ as $c\to\infty$, so it is an increasing bijection of $(0,\infty)$.
With $c_\nu\defeq\Upsilon_\nu^{-1}$ one has $c_\nu(\hat s)\ge\hat s$, and the
profile root of the square case is
\[
b_0^{\nu,1}(\hat s)=\frac{\hat s}{c_\nu(\hat s)},\qquad
\frac{b_0^{\nu,1}(\hat s)\,\mu}{\hat s+b_0^{\nu,1}(\hat s)\,\mu}=\frac{\mu}{c_\nu(\hat s)+\mu}.
\]
\end{lemma}
-/
theorem lem_app_os_cparam_i
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) :
    ContDiffOn ℝ 1 (Upsilon ν) (Ioi (0 : ℝ)) ∧
      ∀ c ∈ Ioi (0 : ℝ), HasDerivAt (Upsilon ν) (∫ x, (1 - x ^ 2 / (c + x) ^ 2) ∂ν) c := by
  have hderiv : ∀ c ∈ Ioi (0 : ℝ), HasDerivAt (Upsilon ν) (∫ x, (1 - x ^ 2 / (c + x) ^ 2) ∂ν) c := by
    intro c hc
    refine (os_cp_integral_hasDerivAt hν (Set.mem_Ioi.mp hc)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (Set.mem_Ioi.mp hc)] with d hd using
      os_cp_upsilon_eq hν (Set.mem_Ioi.mp hd)
  have hcont : ContinuousOn (fun c : ℝ => ∫ x, (1 - x ^ 2 / (c + x) ^ 2) ∂ν) (Ioi (0 : ℝ)) := by
    refine continuousOn_of_dominated (F := fun c x : ℝ => 1 - x ^ 2 / (c + x) ^ 2)
      (bound := fun _ : ℝ => (1 : ℝ)) ?_ ?_ (integrable_const _) ?_
    · intro c _
      exact (by fun_prop : Measurable fun x : ℝ => 1 - x ^ 2 / (c + x) ^ 2).aestronglyMeasurable
    · intro c hc
      filter_upwards [os_cp_ae_nonneg hν] with x hx
      exact os_cp_bound hx (Set.mem_Ioi.mp hc)
    · filter_upwards [os_cp_ae_nonneg hν] with x hx
      refine ContinuousOn.sub continuousOn_const ?_
      refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
      intro c hc
      show (c + x) ^ 2 ≠ 0
      have h2 : 0 < c + x := by linarith [Set.mem_Ioi.mp hc]
      exact pow_ne_zero 2 h2.ne'
  refine ⟨?_, fun c hc => hderiv c hc⟩
  rw [contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn]
  refine ⟨fun c hc => (hderiv c hc).differentiableAt.differentiableWithinAt, ?_⟩
  refine hcont.congr ?_
  intro c hc
  rw [derivWithin_of_isOpen isOpen_Ioi hc]
  exact (hderiv c hc).deriv

/-- Label `lem:app-os-cparam`, part (ii) (Υ'_ν(c) ∈ (0,1] for c > 0). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[The $c$-parametrization]\label{lem:app-os-cparam}
The function $\Upsilon_\nu$ is continuously differentiable on $(0,\infty)$,
with
\[
\Upsilon_\nu'(c)=\int\Big(1-\frac{x^2}{(c+x)^2}\Big)\nu(\dif x)\in(0,1],
\]
and $0<\Upsilon_\nu(c)\le c$. It tends to $0$ as $c\downarrow0$ and to
$\infty$ as $c\to\infty$, so it is an increasing bijection of $(0,\infty)$.
With $c_\nu\defeq\Upsilon_\nu^{-1}$ one has $c_\nu(\hat s)\ge\hat s$, and the
profile root of the square case is
\[
b_0^{\nu,1}(\hat s)=\frac{\hat s}{c_\nu(\hat s)},\qquad
\frac{b_0^{\nu,1}(\hat s)\,\mu}{\hat s+b_0^{\nu,1}(\hat s)\,\mu}=\frac{\mu}{c_\nu(\hat s)+\mu}.
\]
\end{lemma}
-/
theorem lem_app_os_cparam_ii
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) :
    ∀ c ∈ Ioi (0 : ℝ), (∫ x, (1 - x ^ 2 / (c + x) ^ 2) ∂ν) ∈ Ioc (0 : ℝ) 1 := by
  intro c hc
  have hc' : 0 < c := hc
  have hnn : 0 ≤ᵐ[ν] fun x : ℝ => 1 - x ^ 2 / (c + x) ^ 2 := by
    filter_upwards [os_cp_ae_nonneg hν] with x hx
    have h2 : 0 < c + x := by linarith
    show 0 ≤ 1 - x ^ 2 / (c + x) ^ 2
    have : x ^ 2 / (c + x) ^ 2 ≤ 1 := by
      rw [div_le_one (pow_pos h2 2)]; nlinarith [mul_pos hc' hc', mul_nonneg hc'.le hx]
    linarith
  have hint : Integrable (fun x : ℝ => 1 - x ^ 2 / (c + x) ^ 2) ν := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · exact (by fun_prop : Measurable fun x : ℝ => 1 - x ^ 2 / (c + x) ^ 2).aestronglyMeasurable
    · filter_upwards [os_cp_ae_nonneg hν] with x hx
      exact os_cp_bound hx hc'
  rw [Set.mem_Ioc]
  refine ⟨?_, ?_⟩
  · rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
    have hsub : Ici (0 : ℝ) ⊆ Function.support (fun x : ℝ => 1 - x ^ 2 / (c + x) ^ 2) := by
      intro x hx
      have hx' : (0 : ℝ) ≤ x := hx
      have h2 : 0 < c + x := by linarith
      have hq : x ^ 2 / (c + x) ^ 2 < 1 := by
        rw [div_lt_one (pow_pos h2 2)]; nlinarith [mul_pos hc' hc', mul_nonneg hc'.le hx']
      show 1 - x ^ 2 / (c + x) ^ 2 ≠ 0
      intro h; linarith
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    have hu := measure_union_le (μ := ν) (Iio (0 : ℝ)) (Ici 0)
    rw [Iio_union_Ici, measure_univ, hν, zero_add] at hu
    exact lt_of_lt_of_le zero_lt_one hu
  · calc ∫ x, (1 - x ^ 2 / (c + x) ^ 2) ∂ν ≤ ∫ _x, (1 : ℝ) ∂ν := by
          refine integral_mono_of_nonneg hnn (integrable_const 1)
            (Filter.Eventually.of_forall fun x => ?_)
          show 1 - x ^ 2 / (c + x) ^ 2 ≤ 1
          linarith [show 0 ≤ x ^ 2 / (c + x) ^ 2 from div_nonneg (sq_nonneg _) (sq_nonneg _)]
      _ = 1 := by simp

/-- Label `lem:app-os-cparam`, part (iii) (0 < Υ_ν(c) ≤ c for c > 0). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[The $c$-parametrization]\label{lem:app-os-cparam}
The function $\Upsilon_\nu$ is continuously differentiable on $(0,\infty)$,
with
\[
\Upsilon_\nu'(c)=\int\Big(1-\frac{x^2}{(c+x)^2}\Big)\nu(\dif x)\in(0,1],
\]
and $0<\Upsilon_\nu(c)\le c$. It tends to $0$ as $c\downarrow0$ and to
$\infty$ as $c\to\infty$, so it is an increasing bijection of $(0,\infty)$.
With $c_\nu\defeq\Upsilon_\nu^{-1}$ one has $c_\nu(\hat s)\ge\hat s$, and the
profile root of the square case is
\[
b_0^{\nu,1}(\hat s)=\frac{\hat s}{c_\nu(\hat s)},\qquad
\frac{b_0^{\nu,1}(\hat s)\,\mu}{\hat s+b_0^{\nu,1}(\hat s)\,\mu}=\frac{\mu}{c_\nu(\hat s)+\mu}.
\]
\end{lemma}
-/
theorem lem_app_os_cparam_iii
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) :
    ∀ c ∈ Ioi (0 : ℝ), 0 < Upsilon ν c ∧ Upsilon ν c ≤ c := by
  intro c hc
  have hc' : 0 < c := hc
  rw [os_cp_upsilon_eq hν hc']
  refine ⟨?_, ?_⟩
  · have hnn : 0 ≤ᵐ[ν] fun x : ℝ => c ^ 2 / (c + x) := by
      filter_upwards [os_cp_ae_nonneg hν] with x hx
      have h2 : 0 < c + x := by linarith
      exact (div_nonneg (sq_nonneg _) h2.le)
    rw [integral_pos_iff_support_of_nonneg_ae hnn (os_cp_ratio_integrable hν hc')]
    have hsub : Ici (0 : ℝ) ⊆ Function.support (fun x : ℝ => c ^ 2 / (c + x)) := by
      intro x hx
      have hx' : (0 : ℝ) ≤ x := hx
      have h2 : 0 < c + x := by linarith
      exact Function.mem_support.2 (div_pos (pow_pos hc' 2) h2).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    have hu := measure_union_le (μ := ν) (Iio (0 : ℝ)) (Ici 0)
    rw [Iio_union_Ici, measure_univ, hν, zero_add] at hu
    exact lt_of_lt_of_le zero_lt_one hu
  · calc ∫ x, c ^ 2 / (c + x) ∂ν ≤ ∫ _x, c ∂ν := by
          refine integral_mono_of_nonneg ?_ (integrable_const c) ?_
          · filter_upwards [os_cp_ae_nonneg hν] with x hx
            have h2 : 0 < c + x := by linarith
            exact (div_nonneg (sq_nonneg _) h2.le)
          · filter_upwards [os_cp_ae_nonneg hν] with x hx
            exact os_cp_ratio_le hx hc'
      _ = c := by simp

/-- Label `lem:app-os-cparam`, part (iv) (limits of Υ_ν at 0⁺ and at ∞). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[The $c$-parametrization]\label{lem:app-os-cparam}
The function $\Upsilon_\nu$ is continuously differentiable on $(0,\infty)$,
with
\[
\Upsilon_\nu'(c)=\int\Big(1-\frac{x^2}{(c+x)^2}\Big)\nu(\dif x)\in(0,1],
\]
and $0<\Upsilon_\nu(c)\le c$. It tends to $0$ as $c\downarrow0$ and to
$\infty$ as $c\to\infty$, so it is an increasing bijection of $(0,\infty)$.
With $c_\nu\defeq\Upsilon_\nu^{-1}$ one has $c_\nu(\hat s)\ge\hat s$, and the
profile root of the square case is
\[
b_0^{\nu,1}(\hat s)=\frac{\hat s}{c_\nu(\hat s)},\qquad
\frac{b_0^{\nu,1}(\hat s)\,\mu}{\hat s+b_0^{\nu,1}(\hat s)\,\mu}=\frac{\mu}{c_\nu(\hat s)+\mu}.
\]
\end{lemma}
-/
theorem lem_app_os_cparam_iv
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) :
    Tendsto (Upsilon ν) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧ Tendsto (Upsilon ν) atTop atTop := by
  refine ⟨?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_id.mono_left nhdsWithin_le_nhds) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact (lem_app_os_cparam_iii ν hν c hc).1.le
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact (lem_app_os_cparam_iii ν hν c hc).2
  · have h1 : Tendsto (fun c : ℝ => ν (Iic c)) atTop (𝓝 1) := by
      have := tendsto_measure_Iic_atTop ν
      rwa [measure_univ] at this
    have h2 : Tendsto (fun c : ℝ => (ν (Iic c)).toReal) atTop (𝓝 1) := by
      have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1
      simpa [Function.comp_def] using this
    have hIic : ∀ᶠ c in atTop, (1 / 2 : ℝ) ≤ (ν (Iic c)).toReal :=
      h2.eventually (Ici_mem_nhds (by norm_num))
    have hlow : ∀ᶠ c in atTop, c / 4 ≤ Upsilon ν c := by
      filter_upwards [hIic, eventually_gt_atTop 0] with c hc hc0
      have hf_nn : 0 ≤ᵐ[ν] (Iic c).indicator (fun _ : ℝ => c / 2) :=
        Eventually.of_forall fun x =>
          Set.indicator_nonneg (fun _ _ => (by linarith : (0 : ℝ) ≤ c / 2)) x
      have hf_int : Integrable ((Iic c).indicator (fun _ : ℝ => c / 2)) ν :=
        (integrable_const (c / 2)).indicator measurableSet_Iic
      have hmono : ∫ x, (Iic c).indicator (fun _ : ℝ => c / 2) x ∂ν
          ≤ ∫ x, c ^ 2 / (c + x) ∂ν := by
        refine integral_mono_of_nonneg hf_nn (os_cp_ratio_integrable hν hc0) ?_
        filter_upwards [os_cp_ae_nonneg hν] with x hx
        have h2 : 0 < c + x := by linarith
        by_cases hxc : x ∈ Iic c
        · have hxc' : x ≤ c := Set.mem_Iic.mp hxc
          rw [Set.indicator_of_mem hxc, le_div_iff₀ h2]
          nlinarith [mul_nonneg hc0.le (sub_nonneg.2 hxc')]
        · rw [Set.indicator_of_notMem hxc]
          exact (div_nonneg (sq_nonneg _) h2.le)
      rw [integral_indicator_const _ measurableSet_Iic, smul_eq_mul] at hmono
      have hreal : ν.real (Iic c) = (ν (Iic c)).toReal := rfl
      rw [hreal] at hmono
      rw [os_cp_upsilon_eq hν hc0]
      nlinarith [mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤ c / 2)]
    exact tendsto_atTop_mono' atTop hlow (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 4))

/-- Label `lem:app-os-cparam`, part (v) (Υ_ν is an increasing bijection of (0,∞)). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[The $c$-parametrization]\label{lem:app-os-cparam}
The function $\Upsilon_\nu$ is continuously differentiable on $(0,\infty)$,
with
\[
\Upsilon_\nu'(c)=\int\Big(1-\frac{x^2}{(c+x)^2}\Big)\nu(\dif x)\in(0,1],
\]
and $0<\Upsilon_\nu(c)\le c$. It tends to $0$ as $c\downarrow0$ and to
$\infty$ as $c\to\infty$, so it is an increasing bijection of $(0,\infty)$.
With $c_\nu\defeq\Upsilon_\nu^{-1}$ one has $c_\nu(\hat s)\ge\hat s$, and the
profile root of the square case is
\[
b_0^{\nu,1}(\hat s)=\frac{\hat s}{c_\nu(\hat s)},\qquad
\frac{b_0^{\nu,1}(\hat s)\,\mu}{\hat s+b_0^{\nu,1}(\hat s)\,\mu}=\frac{\mu}{c_\nu(\hat s)+\mu}.
\]
\end{lemma}
-/
theorem lem_app_os_cparam_v
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) :
    StrictMonoOn (Upsilon ν) (Ioi (0 : ℝ)) ∧ BijOn (Upsilon ν) (Ioi (0 : ℝ)) (Ioi (0 : ℝ)) := by
  have hC : ContinuousOn (Upsilon ν) (Ioi (0 : ℝ)) :=
    (lem_app_os_cparam_i ν hν).1.continuousOn
  have hmono : StrictMonoOn (Upsilon ν) (Ioi (0 : ℝ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi 0) hC ?_
    intro c hc
    rw [interior_Ioi] at hc
    rw [(lem_app_os_cparam_i ν hν).2 c hc |>.deriv]
    exact (Set.mem_Ioc.mp (lem_app_os_cparam_ii ν hν c hc)).1
  have hsurj : ∀ s ∈ Ioi (0 : ℝ), ∃ c ∈ Ioi (0 : ℝ), Upsilon ν c = s := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    have h0 := (lem_app_os_cparam_iv ν hν).1
    have hinf := (lem_app_os_cparam_iv ν hν).2
    obtain ⟨a, ha⟩ : ∃ a, (0 < a ∧ Upsilon ν a < s) := by
      have hev : ∀ᶠ c in 𝓝[>] (0 : ℝ), Upsilon ν c < s :=
        h0.eventually (gt_mem_nhds hs')
      obtain ⟨a, ha1, ha2⟩ := (hev.and self_mem_nhdsWithin).exists
      exact ⟨a, ha2, ha1⟩
    obtain ⟨b, hb⟩ : ∃ b, (a ≤ b ∧ s < Upsilon ν b) := by
      have hev : ∀ᶠ c in atTop, s + 1 ≤ Upsilon ν c := tendsto_atTop.1 hinf (s + 1)
      obtain ⟨b, hb1, hb2⟩ := (hev.and (eventually_ge_atTop a)).exists
      exact ⟨b, hb2, by linarith⟩
    have hcont : ContinuousOn (Upsilon ν) (Icc a b) :=
      hC.mono (fun x hx => (lt_of_lt_of_le ha.1 hx.1 : (0 : ℝ) < x))
    obtain ⟨c, hc, hcs⟩ := intermediate_value_Ioo hb.1 hcont ⟨ha.2, hb.2⟩
    exact ⟨c, lt_trans ha.1 hc.1, hcs⟩
  refine ⟨hmono, ⟨?_, hmono.injOn, ?_⟩⟩
  · intro c hc
    exact Set.mem_Ioi.mpr (lem_app_os_cparam_iii ν hν c hc).1
  · intro s hs
    obtain ⟨c, hc, hcs⟩ := hsurj s hs
    exact ⟨c, hc, hcs⟩

/-- Label `lem:app-os-cparam`, part (vi) (c_ν := Υ_ν^{-1} is well defined on (0,∞) and c_ν(ŝ) ≥ ŝ). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[The $c$-parametrization]\label{lem:app-os-cparam}
The function $\Upsilon_\nu$ is continuously differentiable on $(0,\infty)$,
with
\[
\Upsilon_\nu'(c)=\int\Big(1-\frac{x^2}{(c+x)^2}\Big)\nu(\dif x)\in(0,1],
\]
and $0<\Upsilon_\nu(c)\le c$. It tends to $0$ as $c\downarrow0$ and to
$\infty$ as $c\to\infty$, so it is an increasing bijection of $(0,\infty)$.
With $c_\nu\defeq\Upsilon_\nu^{-1}$ one has $c_\nu(\hat s)\ge\hat s$, and the
profile root of the square case is
\[
b_0^{\nu,1}(\hat s)=\frac{\hat s}{c_\nu(\hat s)},\qquad
\frac{b_0^{\nu,1}(\hat s)\,\mu}{\hat s+b_0^{\nu,1}(\hat s)\,\mu}=\frac{\mu}{c_\nu(\hat s)+\mu}.
\]
\end{lemma}
-/
theorem lem_app_os_cparam_vi
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) :
    ∀ s ∈ Ioi (0 : ℝ), cNu ν s ∈ Ioi (0 : ℝ) ∧ Upsilon ν (cNu ν s) = s ∧ s ≤ cNu ν s := by
  intro s hs
  have hex : ∃ a ∈ Ioi (0 : ℝ), Upsilon ν a = s := (lem_app_os_cparam_v ν hν).2.2.2 hs
  have hspec := Function.invFunOn_pos hex
  have hcpos : cNu ν s ∈ Ioi (0 : ℝ) := hspec.1
  have h2 : Upsilon ν (cNu ν s) = s := hspec.2
  refine ⟨hcpos, h2, ?_⟩
  have h := (lem_app_os_cparam_iii ν hν (cNu ν s) hcpos).2
  linarith

/-- Label `lem:app-os-cparam`, part (vii) (square-case profile root b_0^{ν,1}(ŝ) = ŝ / c_ν(ŝ)). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[The $c$-parametrization]\label{lem:app-os-cparam}
The function $\Upsilon_\nu$ is continuously differentiable on $(0,\infty)$,
with
\[
\Upsilon_\nu'(c)=\int\Big(1-\frac{x^2}{(c+x)^2}\Big)\nu(\dif x)\in(0,1],
\]
and $0<\Upsilon_\nu(c)\le c$. It tends to $0$ as $c\downarrow0$ and to
$\infty$ as $c\to\infty$, so it is an increasing bijection of $(0,\infty)$.
With $c_\nu\defeq\Upsilon_\nu^{-1}$ one has $c_\nu(\hat s)\ge\hat s$, and the
profile root of the square case is
\[
b_0^{\nu,1}(\hat s)=\frac{\hat s}{c_\nu(\hat s)},\qquad
\frac{b_0^{\nu,1}(\hat s)\,\mu}{\hat s+b_0^{\nu,1}(\hat s)\,\mu}=\frac{\mu}{c_\nu(\hat s)+\mu}.
\]
\end{lemma}
-/
theorem lem_app_os_cparam_vii
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) :
    ∀ s ∈ Ioi (0 : ℝ), profileRoot ν 1 s = s / cNu ν s := by
  intro s hs
  have hs0 : (0 : ℝ) < s := hs
  obtain ⟨⟨hbI, hbeq⟩, -⟩ := lem_app_os_root_i ν hν (r := 1) one_pos hs0
  have hb0 : (0 : ℝ) < profileRoot ν 1 s := hbI.1
  have hb' : profileRoot ν 1 s ≠ 0 := hb0.ne'
  set b := profileRoot ν 1 s with hbdef
  have hpt : ∀ x : ℝ, x / (s / b + x) = b * x / (s + b * x) := by
    intro x
    rw [show s / b + x = (s + b * x) / b by field_simp, div_div_eq_mul_div]
    ring
  have hmu : mNu ν (s / b) = 1 - b := by
    have h1 : mNu ν (s / b) = mNuExt ν s b := by
      unfold mNu mNuExt
      congr 1
      funext x
      exact hpt x
    have h2 : mNuExt ν s b = 1 - b := by linarith
    rw [h1, h2]
  have hUps : Upsilon ν (s / b) = s := by
    unfold Upsilon
    rw [hmu, show (1 : ℝ) - (1 - b) = b by ring]
    field_simp
  have hcp := lem_app_os_cparam_vi ν hν s hs
  have hinj : cNu ν s = s / b :=
    (lem_app_os_cparam_v ν hν).1.injOn hcp.1 (div_pos hs0 hb0) (hcp.2.1.trans hUps.symm)
  rw [hinj]
  field_simp

/-- Label `lem:app-os-cparam`, part (viii) (b μ/(ŝ + b μ) = μ/(c_ν(ŝ) + μ) at the square-case root; μ ≥ 0 (the range of μ in the profile)). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[The $c$-parametrization]\label{lem:app-os-cparam}
The function $\Upsilon_\nu$ is continuously differentiable on $(0,\infty)$,
with
\[
\Upsilon_\nu'(c)=\int\Big(1-\frac{x^2}{(c+x)^2}\Big)\nu(\dif x)\in(0,1],
\]
and $0<\Upsilon_\nu(c)\le c$. It tends to $0$ as $c\downarrow0$ and to
$\infty$ as $c\to\infty$, so it is an increasing bijection of $(0,\infty)$.
With $c_\nu\defeq\Upsilon_\nu^{-1}$ one has $c_\nu(\hat s)\ge\hat s$, and the
profile root of the square case is
\[
b_0^{\nu,1}(\hat s)=\frac{\hat s}{c_\nu(\hat s)},\qquad
\frac{b_0^{\nu,1}(\hat s)\,\mu}{\hat s+b_0^{\nu,1}(\hat s)\,\mu}=\frac{\mu}{c_\nu(\hat s)+\mu}.
\]
\end{lemma}
-/
theorem lem_app_os_cparam_viii
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) :
    ∀ s ∈ Ioi (0 : ℝ), ∀ mu : ℝ, 0 ≤ mu →
      profileRoot ν 1 s * mu / (s + profileRoot ν 1 s * mu) = mu / (cNu ν s + mu) := by
  intro s hs mu hmu
  have hs0 : (0 : ℝ) < s := hs
  have hc0 : (0 : ℝ) < cNu ν s := (lem_app_os_cparam_vi ν hν s hs).1
  rw [lem_app_os_cparam_vii ν hν s hs]
  have hnn : 0 ≤ s / cNu ν s * mu := mul_nonneg (div_nonneg hs0.le hc0.le) hmu
  have hden : 0 < s + s / cNu ν s * mu := by linarith
  have hden2 : 0 < cNu ν s + mu := by linarith
  rw [div_eq_div_iff hden.ne' hden2.ne']
  field_simp

/-! ## Representation of the profile (`lem:app-os-repr`, the hub) -/

/-- Private helper: `0 < 1 - m_ν(c) ≤ 1` for `c > 0`, from `0 < Υ_ν(c) ≤ c`. -/
private lemma os_repr_sub_pos {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {c : ℝ} (hc : 0 < c) : 0 < 1 - mNu ν c ∧ 1 - mNu ν c ≤ 1 := by
  obtain ⟨h1, h2⟩ := lem_app_os_cparam_iii ν hν c hc
  unfold Upsilon at h1 h2
  constructor
  · by_contra h
    push_neg at h
    nlinarith
  · nlinarith

/-- Private helper: `y ↦ m_ν(μ y)` is continuous on `(0,∞)`, via `m_ν(c) = 1 - Υ_ν(c)/c`. -/
private lemma os_repr_mNu_cont {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {mu : ℝ} (hmu : 0 < mu) : ContinuousOn (fun y : ℝ => mNu ν (mu * y)) (Ioi (0 : ℝ)) := by
  have hU : ContinuousOn (Upsilon ν) (Ioi (0 : ℝ)) := (lem_app_os_cparam_i ν hν).1.continuousOn
  have hmaps : MapsTo (fun y : ℝ => mu * y) (Ioi (0 : ℝ)) (Ioi (0 : ℝ)) :=
    fun y hy => mul_pos hmu hy
  have hlin : ContinuousOn (fun y : ℝ => mu * y) (Ioi (0 : ℝ)) :=
    (continuous_const.mul continuous_id).continuousOn
  have hcomp : ContinuousOn (fun y : ℝ => Upsilon ν (mu * y) / (mu * y)) (Ioi (0 : ℝ)) :=
    ContinuousOn.div (hU.comp hlin hmaps) hlin (fun y hy => (mul_pos hmu hy).ne')
  refine ContinuousOn.congr (f := fun y : ℝ => 1 - Upsilon ν (mu * y) / (mu * y)) ?_ ?_
  · exact continuousOn_const.sub hcomp
  · intro y hy
    have hc : mu * y ≠ 0 := (mul_pos hmu hy).ne'
    show mNu ν (mu * y) = 1 - Upsilon ν (mu * y) / (mu * y)
    rw [Upsilon, mul_div_cancel_left₀ _ hc]
    ring

/-- Private helper: `varpi` is integrable on `(0,∞)` (its integral is one). -/
private lemma os_repr_varpi_int : IntegrableOn varpi (Ioi (0 : ℝ)) := by
  by_contra hn
  have h := lem_app_os_integrals_iv.2
  rw [integral_undef hn] at h
  norm_num at h

/-- Private helper: `varpi y > 0` for `y > 0`. -/
private lemma os_repr_varpi_pos {y : ℝ} (hy : 0 < y) : 0 < varpi y := by
  unfold varpi
  exact div_pos (mul_pos (div_pos two_pos Real.pi_pos) (Real.sqrt_pos.2 hy))
    (pow_pos (by linarith) 2)

/-- Private helper: `Υ_ν` is measurable on all of `ℝ`. -/
private lemma os_repr_ups_meas (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Measurable (Upsilon ν) := by
  have h : StronglyMeasurable (fun c : ℝ => ∫ x, x / (c + x) ∂ν) :=
    StronglyMeasurable.integral_prod_right' (f := fun p : ℝ × ℝ => p.2 / (p.1 + p.2))
      (Measurable.stronglyMeasurable (by fun_prop))
  unfold Upsilon mNu
  exact measurable_id.mul (measurable_const.sub h.measurable)

/-- Private helper: integrability of `√c/(c+μ)²` on `(0,∞)`, from the closed form (v). -/
private lemma os_repr_sqrt_int {mu : ℝ} (hmu : 0 < mu) :
    IntegrableOn (fun c : ℝ => Real.sqrt c / (c + mu) ^ 2) (Ioi (0 : ℝ)) := by
  by_contra hn
  have h := lem_app_os_integrals_v hmu
  rw [integral_undef hn, mul_zero] at h
  have : 0 < Real.sqrt (mu / 2) := Real.sqrt_pos.2 (by positivity)
  linarith

/-- Private helper: the tail integral `∫_{c0}^∞ μ/(c+μ)² dc = μ/(c0+μ)` (real form). -/
private lemma os_repr_tail_real {mu : ℝ} (hmu : 0 < mu) {c0 : ℝ} (hc0 : 0 < c0) :
    IntegrableOn (fun c : ℝ => mu / (c + mu) ^ 2) (Ioi c0) ∧
      ∫ c in Ioi c0, mu / (c + mu) ^ 2 = mu / (c0 + mu) := by
  have hd : ∀ x ∈ Ioi c0, HasDerivAt (fun c : ℝ => -mu / (c + mu)) (mu / (x + mu) ^ 2) x := by
    intro x hx
    have hx' : (0 : ℝ) < x := lt_trans hc0 hx
    have hne : x + mu ≠ 0 := by positivity
    have := (hasDerivAt_const x (-mu)).div ((hasDerivAt_id x).add_const mu) hne
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hcont : ContinuousWithinAt (fun c : ℝ => -mu / (c + mu)) (Ici c0) c0 := by
    refine ContinuousAt.continuousWithinAt ?_
    exact continuousAt_const.div (continuousAt_id.add continuousAt_const) (by positivity)
  have hlim : Tendsto (fun c : ℝ => -mu / (c + mu)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_id)
  have hint : IntegrableOn (fun c : ℝ => mu / (c + mu) ^ 2) (Ioi c0) :=
    integrableOn_Ioi_deriv_of_nonneg hcont hd
      (fun x hx => by
        have hx' : (0 : ℝ) < x := lt_trans hc0 hx
        positivity) hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hint hlim]
  ring

/-- Private helper: pointwise layer-cake kernel. -/
private noncomputable def osReprF (ν : Measure ℝ) (mu v c : ℝ) : ENNReal :=
  if v < Real.sqrt (Upsilon ν c) then ENNReal.ofReal (mu / (c + mu) ^ 2) else 0

private lemma os_repr_F_meas (ν : Measure ℝ) [IsProbabilityMeasure ν] (mu : ℝ) :
    Measurable (fun p : ℝ × ℝ => osReprF ν mu p.1 p.2) := by
  unfold osReprF
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_lt measurable_fst
      (Real.continuous_sqrt.measurable.comp ((os_repr_ups_meas ν).comp measurable_snd))
  · exact ENNReal.measurable_ofReal.comp (by fun_prop)

private lemma os_repr_stepA {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {mu : ℝ} (hmu : 0 < mu) {v : ℝ} (hv : 0 < v) :
    ∫⁻ c in Ioi (0 : ℝ), osReprF ν mu v c = ENNReal.ofReal (mu / (cNu ν (v ^ 2) + mu)) := by
  have hv2 : v ^ 2 ∈ Ioi (0 : ℝ) := pow_pos hv 2
  obtain ⟨hc0, hU, -⟩ := lem_app_os_cparam_vi ν hν (v ^ 2) hv2
  have hc0' : (0 : ℝ) < cNu ν (v ^ 2) := hc0
  have hmono := (lem_app_os_cparam_v ν hν).1
  have hset : ∀ c ∈ Ioi (0 : ℝ), osReprF ν mu v c =
      (Ioi (cNu ν (v ^ 2))).indicator (fun c : ℝ => ENNReal.ofReal (mu / (c + mu) ^ 2)) c := by
    intro c hc
    unfold osReprF
    have : v < Real.sqrt (Upsilon ν c) ↔ cNu ν (v ^ 2) < c := by
      rw [Real.lt_sqrt hv.le, ← hmono.lt_iff_lt hc0 hc, hU]
    by_cases h : cNu ν (v ^ 2) < c
    · rw [if_pos (this.2 h), Set.indicator_of_mem (Set.mem_Ioi.2 h)]
    · rw [if_neg (fun h' => h (this.1 h')), Set.indicator_of_notMem (by simpa using h)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hset, lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    show Ioi (cNu ν (v ^ 2)) ∩ Ioi (0 : ℝ) = Ioi (cNu ν (v ^ 2)) from
      Set.inter_eq_left.2 (Ioi_subset_Ioi hc0'.le)]
  obtain ⟨hint, hval⟩ := os_repr_tail_real hmu hc0'
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun c => by
      show 0 ≤ mu / (c + mu) ^ 2
      positivity), hval]

private lemma os_repr_stepB {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {mu : ℝ} (hmu : 0 < mu) {c : ℝ} (hc : 0 < c) :
    ∫⁻ v in Ioi (0 : ℝ), osReprF ν mu v c =
      ENNReal.ofReal (mu / (c + mu) ^ 2 * Real.sqrt (Upsilon ν c)) := by
  have hK : 0 ≤ mu / (c + mu) ^ 2 := by positivity
  have hset : ∀ v : ℝ, osReprF ν mu v c =
      (Iio (Real.sqrt (Upsilon ν c))).indicator
        (fun _ : ℝ => ENNReal.ofReal (mu / (c + mu) ^ 2)) v := by
    intro v
    unfold osReprF
    by_cases h : v < Real.sqrt (Upsilon ν c)
    · rw [if_pos h, Set.indicator_of_mem (Set.mem_Iio.2 h)]
    · rw [if_neg h, Set.indicator_of_notMem (by simpa using h)]
  simp_rw [hset]
  rw [lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
    show Iio (Real.sqrt (Upsilon ν c)) ∩ Ioi (0 : ℝ) = Ioo 0 (Real.sqrt (Upsilon ν c)) by
      ext x; simp [and_comm],
    Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul hK]

/-- Label `lem:app-os-repr`, part (i) (first form of eqn:app-os-repr). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Representation of the profile]\label{lem:app-os-repr}
For every probability measure $\nu$ and every $\mu>0$,
\begin{equation}\label{eqn:app-os-repr}
\mathfrak d^{\rm os}_\nu(\mu)=\frac{\sqrt2}{\pi}\,\mu\int_0^\infty\frac{\sqrt{\Upsilon_\nu(c)}}{(c+\mu)^2}\,\dif c
=\sqrt{\frac\mu2}\;\chi_\nu(\mu),
\qquad \chi_\nu(\mu)\in(0,1].
\end{equation}
\end{lemma}
-/
theorem lem_app_os_repr_i
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) {mu : ℝ} (hmu : 0 < mu) :
    dOsSq ν mu = Real.sqrt 2 / Real.pi * mu * ∫ c in Ioi (0 : ℝ), Real.sqrt (Upsilon ν c) / (c + mu) ^ 2 := by
  have hmu0 : (0 : ℝ) ≤ mu := hmu.le
  -- the integrand in `c`
  set G : ℝ → ℝ := fun c => mu / (c + mu) ^ 2 * Real.sqrt (Upsilon ν c) with hG
  have hGnn : ∀ c ∈ Ioi (0 : ℝ), 0 ≤ G c := by
    intro c hc
    have : (0 : ℝ) < c := hc
    simp only [hG]; positivity
  have hGint : IntegrableOn G (Ioi (0 : ℝ)) := by
    have hb : IntegrableOn (fun c : ℝ => mu * (Real.sqrt c / (c + mu) ^ 2)) (Ioi (0 : ℝ)) :=
      (os_repr_sqrt_int hmu).const_mul mu
    refine Integrable.mono' hb ?_ ?_
    · exact (((measurable_const.div (by fun_prop : Measurable fun c : ℝ => (c + mu) ^ 2)).mul
        (Real.continuous_sqrt.measurable.comp (os_repr_ups_meas ν))).aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with c hc
      have hc' : (0 : ℝ) < c := hc
      have h1 : Real.sqrt (Upsilon ν c) ≤ Real.sqrt c :=
        Real.sqrt_le_sqrt (lem_app_os_cparam_iii ν hν c hc).2
      rw [Real.norm_eq_abs, abs_of_nonneg (hGnn c hc)]
      simp only [hG]
      calc mu / (c + mu) ^ 2 * Real.sqrt (Upsilon ν c)
          ≤ mu / (c + mu) ^ 2 * Real.sqrt c :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = mu * (Real.sqrt c / (c + mu) ^ 2) := by ring
  -- Tonelli
  have hFm := os_repr_F_meas ν mu
  have hswap : ∫⁻ v in Ioi (0 : ℝ), ∫⁻ c in Ioi (0 : ℝ), osReprF ν mu v c =
      ∫⁻ c in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ), osReprF ν mu v c :=
    lintegral_lintegral_swap hFm.aemeasurable
  have hRHS : ∫⁻ c in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ), osReprF ν mu v c =
      ENNReal.ofReal (∫ c in Ioi (0 : ℝ), G c) := by
    rw [ofReal_integral_eq_lintegral_ofReal hGint
      (ae_restrict_of_forall_mem measurableSet_Ioi hGnn)]
    exact setLIntegral_congr_fun measurableSet_Ioi (fun c hc => os_repr_stepB hmu hc)
  -- the measurable real function `h`
  set h : ℝ → ℝ := fun v => (∫⁻ c in Ioi (0 : ℝ), osReprF ν mu v c).toReal with hh
  have hhm : Measurable h := (hFm.lintegral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).ennreal_toReal
  have hha : ∀ v ∈ Ioi (0 : ℝ), h v = mu / (cNu ν (v ^ 2) + mu) := by
    intro v hv
    simp only [hh]
    rw [os_repr_stepA hν hmu hv]
    have hc0 : 0 < cNu ν (v ^ 2) := (lem_app_os_cparam_vi ν hν (v ^ 2) (Set.mem_Ioi.2 (pow_pos hv 2))).1
    exact ENNReal.toReal_ofReal (by positivity)
  have hhnn : ∀ v ∈ Ioi (0 : ℝ), 0 ≤ h v := fun v _ => ENNReal.toReal_nonneg
  have hofh : ∀ v ∈ Ioi (0 : ℝ), ENNReal.ofReal (h v) = ∫⁻ c in Ioi (0 : ℝ), osReprF ν mu v c := by
    intro v hv
    simp only [hh]
    rw [os_repr_stepA hν hmu hv]
    have hc0 : 0 < cNu ν (v ^ 2) := (lem_app_os_cparam_vi ν hν (v ^ 2) (Set.mem_Ioi.2 (pow_pos hv 2))).1
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hJ : ∫ v in Ioi (0 : ℝ), h v = ∫ c in Ioi (0 : ℝ), G c := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioi hhnn)
      hhm.aestronglyMeasurable]
    rw [setLIntegral_congr_fun measurableSet_Ioi hofh, hswap, hRHS,
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi hGnn)]
  -- assemble
  have hprof : ∫ v in Ioi (0 : ℝ), dOsIntegrand ν 1 mu 0 v = ∫ v in Ioi (0 : ℝ), h v := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
    rw [hha v hv]
    have := lem_app_os_cparam_viii ν hν (0 + v ^ 2) (by simpa using pow_pos hv 2) mu hmu0
    simpa [dOsIntegrand] using this
  have hGmul : ∫ c in Ioi (0 : ℝ), G c =
      mu * ∫ c in Ioi (0 : ℝ), Real.sqrt (Upsilon ν c) / (c + mu) ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun c _ => ?_)
    simp only [hG]; ring
  unfold dOsSq dOs
  rw [hprof, hJ, hGmul]
  ring

/-- Label `lem:app-os-repr`, part (ii) (second form of eqn:app-os-repr: 𝔡^os_ν(μ) = √(μ/2) χ_ν(μ)). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Representation of the profile]\label{lem:app-os-repr}
For every probability measure $\nu$ and every $\mu>0$,
\begin{equation}\label{eqn:app-os-repr}
\mathfrak d^{\rm os}_\nu(\mu)=\frac{\sqrt2}{\pi}\,\mu\int_0^\infty\frac{\sqrt{\Upsilon_\nu(c)}}{(c+\mu)^2}\,\dif c
=\sqrt{\frac\mu2}\;\chi_\nu(\mu),
\qquad \chi_\nu(\mu)\in(0,1].
\end{equation}
\end{lemma}
-/
theorem lem_app_os_repr_ii
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) {mu : ℝ} (hmu : 0 < mu) :
    dOsSq ν mu = Real.sqrt (mu / 2) * sqrtEff ν mu := by
  have hsubst : ∫ c in Ioi (0 : ℝ), Real.sqrt (Upsilon ν c) / (c + mu) ^ 2
      = mu * ∫ y in Ioi (0 : ℝ), Real.sqrt (Upsilon ν (mu * y)) / (mu * y + mu) ^ 2 := by
    have h := integral_comp_mul_left_Ioi
      (fun c : ℝ => Real.sqrt (Upsilon ν c) / (c + mu) ^ 2) 0 hmu
    simp only [mul_zero, smul_eq_mul] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ hmu.ne', one_mul]
  have hs2 : Real.sqrt (mu / 2) = Real.sqrt mu * Real.sqrt 2 / 2 := by
    rw [Real.sqrt_div' mu (by norm_num : (0 : ℝ) ≤ 2),
      div_eq_div_iff (Real.sqrt_pos.2 two_pos).ne' two_ne_zero, mul_assoc,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hpt : Set.EqOn (fun y : ℝ => Real.sqrt (Upsilon ν (mu * y)) / (mu * y + mu) ^ 2)
      (fun y : ℝ => Real.sqrt mu / mu ^ 2 * (Real.pi / 2) *
        (varpi y * Real.sqrt (1 - mNu ν (mu * y)))) (Ioi (0 : ℝ)) := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    have hc : 0 < mu * y := mul_pos hmu hy'
    have hm := os_repr_sub_pos hν hc
    have hy1 : (1 + y) ≠ 0 := (by linarith : (0 : ℝ) < 1 + y).ne'
    have hmu0 : mu ≠ 0 := hmu.ne'
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    dsimp only
    unfold Upsilon varpi
    rw [Real.sqrt_mul hc.le _, Real.sqrt_mul hmu.le _,
      show (mu * y + mu) ^ 2 = mu ^ 2 * (1 + y) ^ 2 by ring]
    field_simp
  unfold sqrtEff
  rw [lem_app_os_repr_i ν hν hmu, hsubst, setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_const_mul, hs2]
  field_simp

/-- Label `lem:app-os-repr`, part (iii) (χ_ν(μ) ∈ (0,1]). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Representation of the profile]\label{lem:app-os-repr}
For every probability measure $\nu$ and every $\mu>0$,
\begin{equation}\label{eqn:app-os-repr}
\mathfrak d^{\rm os}_\nu(\mu)=\frac{\sqrt2}{\pi}\,\mu\int_0^\infty\frac{\sqrt{\Upsilon_\nu(c)}}{(c+\mu)^2}\,\dif c
=\sqrt{\frac\mu2}\;\chi_\nu(\mu),
\qquad \chi_\nu(\mu)\in(0,1].
\end{equation}
\end{lemma}
-/
theorem lem_app_os_repr_iii
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) {mu : ℝ} (hmu : 0 < mu) :
    0 < sqrtEff ν mu ∧ sqrtEff ν mu ≤ 1 := by
  have hsub : ∀ y ∈ Ioi (0 : ℝ), 0 < 1 - mNu ν (mu * y) ∧ 1 - mNu ν (mu * y) ≤ 1 :=
    fun y hy => os_repr_sub_pos hν (mul_pos hmu hy)
  have hcont : ContinuousOn (fun y : ℝ => 1 - mNu ν (mu * y)) (Ioi (0 : ℝ)) :=
    continuousOn_const.sub (os_repr_mNu_cont hν hmu)
  have hvm : Measurable varpi := by unfold varpi; fun_prop
  have hm : AEStronglyMeasurable (fun y : ℝ => Real.sqrt (1 - mNu ν (mu * y)))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Real.continuous_sqrt.comp_continuousOn hcont).aestronglyMeasurable measurableSet_Ioi
  have hint : IntegrableOn (fun y : ℝ => varpi y * Real.sqrt (1 - mNu ν (mu * y)))
      (Ioi (0 : ℝ)) := by
    refine Integrable.mono' os_repr_varpi_int (hvm.aestronglyMeasurable.mul hm) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : (0 : ℝ) < y := hy
    have hv := os_repr_varpi_pos hy'
    have hs0 : 0 ≤ Real.sqrt (1 - mNu ν (mu * y)) := Real.sqrt_nonneg _
    have hs1 : Real.sqrt (1 - mNu ν (mu * y)) ≤ 1 := by
      have := Real.sqrt_le_sqrt (hsub y hy).2
      rwa [Real.sqrt_one] at this
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hv.le hs0)]
    calc varpi y * Real.sqrt (1 - mNu ν (mu * y)) ≤ varpi y * 1 :=
          mul_le_mul_of_nonneg_left hs1 hv.le
      _ = varpi y := mul_one _
  unfold sqrtEff
  constructor
  · have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun y : ℝ => varpi y * Real.sqrt (1 - mNu ν (mu * y))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy' : (0 : ℝ) < y := hy
      exact mul_nonneg (os_repr_varpi_pos hy').le (Real.sqrt_nonneg _)
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
    have hsupp : Ioi (0 : ℝ) ⊆ Function.support (fun y : ℝ => varpi y * Real.sqrt (1 - mNu ν (mu * y)))
        ∩ Ioi (0 : ℝ) := by
      intro y hy
      refine ⟨?_, hy⟩
      have hy' : (0 : ℝ) < y := hy
      refine mul_ne_zero (os_repr_varpi_pos hy').ne' ?_
      exact (Real.sqrt_pos.2 (hsub y hy).1).ne'
    exact lt_of_lt_of_le (by simp) (measure_mono hsupp)
  · have := setIntegral_mono_on hint os_repr_varpi_int measurableSet_Ioi
      (fun y hy => by
        have hy' : (0 : ℝ) < y := hy
        have hs1 : Real.sqrt (1 - mNu ν (mu * y)) ≤ 1 := by
          have := Real.sqrt_le_sqrt (hsub y hy).2
          rwa [Real.sqrt_one] at this
        calc varpi y * Real.sqrt (1 - mNu ν (mu * y)) ≤ varpi y * 1 :=
              mul_le_mul_of_nonneg_left hs1 (os_repr_varpi_pos hy').le
          _ = varpi y := mul_one _)
    rw [lem_app_os_integrals_iv.2] at this
    exact this

/-! ## The averaged ratio (`lem:app-os-average`) -/

private lemma os_avg_tend0 : Tendsto (fun y : ℝ => Real.sqrt y / (1 + y)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun y : ℝ => (Real.sqrt y)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
    · exact Filter.eventually_atTop.2 ⟨0, fun y hy => by
        have : (0 : ℝ) < 1 + y := by linarith
        exact div_nonneg (Real.sqrt_nonneg y) this.le⟩
    · refine Filter.eventually_atTop.2 ⟨1, fun y hy => ?_⟩
      have hy0 : (0 : ℝ) < y := by linarith
      have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + y), inv_mul_eq_div, le_div_iff₀ hs]
      nlinarith [Real.mul_self_sqrt hy0.le]

private lemma os_avg_tend1 : Tendsto (fun y : ℝ => Real.sqrt y / (1 + y) ^ 2) atTop (𝓝 0) := by
  have h3 : Tendsto (fun y : ℝ => (Real.sqrt y)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
  · exact Filter.eventually_atTop.2 ⟨0, fun y hy => by positivity⟩
  · refine Filter.eventually_atTop.2 ⟨1, fun y hy => ?_⟩
    have hy0 : (0 : ℝ) < y := by linarith
    have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
    rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hs]
    nlinarith [Real.mul_self_sqrt hy0.le]

private lemma os_avg_tendS (s : ℝ) (hs : 0 < s) :
    Tendsto (fun y : ℝ => Real.arctan (Real.sqrt y / s)) atTop (𝓝 (Real.pi / 2)) :=
  (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    ((Real.tendsto_sqrt_atTop).atTop_div_const hs)

private lemma os_avg_tendA :
    Tendsto (fun y : ℝ => Real.arctan (Real.sqrt y)) atTop (𝓝 (Real.pi / 2)) := by
  simpa using os_avg_tendS 1 one_pos

private lemma os_avg_core_ne (s : ℝ) (hs : 0 < s) (h1 : s ≠ 1) :
    ∫ y in Ioi (0 : ℝ), Real.sqrt y / (1 + y) ^ 2 * (s ^ 2 / (y + s ^ 2))
      = Real.pi * s ^ 2 / (2 * (1 + s) ^ 2) := by
  have hd : 1 - s ^ 2 ≠ 0 := by
    intro h
    have : (1 - s) * (1 + s) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h1 (by linarith)
    · linarith
  set g : ℝ → ℝ := fun y => 2 * s ^ 2 * (s ^ 2 / (1 - s ^ 2) ^ 2 * Real.arctan (Real.sqrt y)
      + 1 / (2 * (1 - s ^ 2)) * (Real.arctan (Real.sqrt y) + Real.sqrt y / (1 + y))
      - s / (1 - s ^ 2) ^ 2 * Real.arctan (Real.sqrt y / s)) with hg
  have hder : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt g
      (Real.sqrt y / (1 + y) ^ 2 * (s ^ 2 / (y + s ^ 2))) y := by
    intro y hy
    have hy : (0 : ℝ) < y := hy
    have hq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt y)) y := Real.hasDerivAt_sqrt hy.ne'
    have ha := hq.arctan
    have h1y : HasDerivAt (fun x : ℝ => 1 + x) 1 y := (hasDerivAt_id y).const_add 1
    have hb := hq.div h1y (ne_of_gt (by linarith))
    have hc := (hq.div_const s).arctan
    have := (((ha.const_mul (s ^ 2 / (1 - s ^ 2) ^ 2)).add
      ((ha.add hb).const_mul (1 / (2 * (1 - s ^ 2))))).sub
      (hc.const_mul (s / (1 - s ^ 2) ^ 2))).const_mul (2 * s ^ 2)
    convert this using 1
    have hpos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
    obtain ⟨w, hw⟩ : ∃ w, Real.sqrt y = w := ⟨_, rfl⟩
    rw [hw] at hpos hsq ⊢
    subst hsq
    have hne : (1 + w ^ 2) ≠ 0 := by positivity
    have hne2 : (w ^ 2 + s ^ 2) ≠ 0 := by positivity
    have hne3 : (1 + (w / s) ^ 2) ≠ 0 := by positivity
    have hsne : s ≠ 0 := hs.ne'
    have hwne : w ≠ 0 := hpos.ne'
    have e3 : 1 + (w / s) ^ 2 = (s ^ 2 + w ^ 2) / s ^ 2 := by field_simp
    rw [e3]
    have hne4 : (s ^ 2 + w ^ 2) ≠ 0 := by positivity
    field_simp
    ring
  have hcont : ContinuousWithinAt g (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    have h1 : Continuous fun y : ℝ => Real.arctan (Real.sqrt y) :=
      Real.continuous_arctan.comp Real.continuous_sqrt
    have h2 : ContinuousAt (fun y : ℝ => Real.sqrt y / (1 + y)) 0 :=
      ContinuousAt.div Real.continuous_sqrt.continuousAt
        (by fun_prop : Continuous fun y : ℝ => 1 + y).continuousAt (by norm_num)
    have h3 : Continuous fun y : ℝ => Real.arctan (Real.sqrt y / s) :=
      Real.continuous_arctan.comp (Real.continuous_sqrt.div_const s)
    rw [hg]
    exact ((continuousAt_const).mul
      ((((continuousAt_const).mul h1.continuousAt).add
        (continuousAt_const.mul (h1.continuousAt.add h2))).sub
        (continuousAt_const.mul h3.continuousAt)))
  have hlim : Tendsto g atTop (𝓝 (2 * s ^ 2 * (s ^ 2 / (1 - s ^ 2) ^ 2 * (Real.pi / 2)
      + 1 / (2 * (1 - s ^ 2)) * (Real.pi / 2 + 0) - s / (1 - s ^ 2) ^ 2 * (Real.pi / 2)))) := by
    rw [hg]
    exact (((os_avg_tendA.const_mul _).add
      ((os_avg_tendA.add os_avg_tend0).const_mul _)).sub
      ((os_avg_tendS s hs).const_mul _)).const_mul _
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hder (fun y hy => by
      have hy : (0 : ℝ) < y := hy
      positivity) hlim]
  simp only [hg, Real.sqrt_zero, Real.arctan_zero, zero_div, add_zero, mul_zero, sub_zero]
  have h1s : (1 + s) ≠ 0 := by positivity
  have h1m : 1 - s ≠ 0 := fun h => h1 (by linarith)
  have : 1 - s ^ 2 = (1 - s) * (1 + s) := by ring
  rw [this]
  field_simp
  ring

private lemma os_avg_core_one :
    ∫ y in Ioi (0 : ℝ), Real.sqrt y / (1 + y) ^ 2 * (1 ^ 2 / (y + 1 ^ 2))
      = Real.pi * 1 ^ 2 / (2 * (1 + 1) ^ 2) := by
  set g : ℝ → ℝ := fun y => 1 / 4 * (Real.arctan (Real.sqrt y) + Real.sqrt y / (1 + y))
      - Real.sqrt y / (2 * (1 + y) ^ 2) with hg
  have hder : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt g
      (Real.sqrt y / (1 + y) ^ 2 * (1 ^ 2 / (y + 1 ^ 2))) y := by
    intro y hy
    have hy : (0 : ℝ) < y := hy
    have hq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt y)) y := Real.hasDerivAt_sqrt hy.ne'
    have ha := hq.arctan
    have h1y : HasDerivAt (fun x : ℝ => 1 + x) 1 y := (hasDerivAt_id y).const_add 1
    have hb := hq.div h1y (ne_of_gt (by linarith))
    have h2y : HasDerivAt (fun x : ℝ => 2 * (1 + x) ^ 2) (2 * (2 * (1 + y) ^ 1 * 1)) y := by
      have := (h1y.pow 2).const_mul 2
      simpa using this
    have hc := hq.div h2y (by positivity)
    have := ((ha.add hb).const_mul (1 / 4)).sub hc
    convert this using 1
    have hpos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
    obtain ⟨w, hw⟩ : ∃ w, Real.sqrt y = w := ⟨_, rfl⟩
    rw [hw] at hpos hsq ⊢
    subst hsq
    have hne : (1 + w ^ 2) ≠ 0 := by positivity
    have hwne : w ≠ 0 := hpos.ne'
    field_simp
    ring
  have hcont : ContinuousWithinAt g (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    have h1 : Continuous fun y : ℝ => Real.arctan (Real.sqrt y) :=
      Real.continuous_arctan.comp Real.continuous_sqrt
    have h2 : ContinuousAt (fun y : ℝ => Real.sqrt y / (1 + y)) 0 :=
      ContinuousAt.div Real.continuous_sqrt.continuousAt
        (by fun_prop : Continuous fun y : ℝ => 1 + y).continuousAt (by norm_num)
    have h4 : ContinuousAt (fun y : ℝ => Real.sqrt y / (2 * (1 + y) ^ 2)) 0 :=
      ContinuousAt.div Real.continuous_sqrt.continuousAt
        (by fun_prop : Continuous fun y : ℝ => 2 * (1 + y) ^ 2).continuousAt (by norm_num)
    rw [hg]
    exact (continuousAt_const.mul (h1.continuousAt.add h2)).sub h4
  have hlim : Tendsto g atTop (𝓝 (1 / 4 * (Real.pi / 2 + 0) - 0)) := by
    rw [hg]
    refine ((os_avg_tendA.add os_avg_tend0).const_mul _).sub ?_
    have := os_avg_tend1.const_mul (1 / 2)
    simp only [mul_zero] at this
    refine this.congr (fun y => ?_)
    rw [div_mul_div_comm, one_mul]
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hder (fun y hy => by
      have hy : (0 : ℝ) < y := hy
      positivity) hlim]
  simp only [hg, Real.sqrt_zero, Real.arctan_zero, zero_div, add_zero, mul_zero, sub_zero]
  ring

private lemma os_avg_core (s : ℝ) (hs : 0 < s) :
    ∫ y in Ioi (0 : ℝ), Real.sqrt y / (1 + y) ^ 2 * (s ^ 2 / (y + s ^ 2))
      = Real.pi * s ^ 2 / (2 * (1 + s) ^ 2) := by
  by_cases h1 : s = 1
  · subst h1
    exact os_avg_core_one
  · exact os_avg_core_ne s hs h1

/-- Label `lem:app-os-average`, part (i) (∫_0^∞ ϖ(y) x/(μy+x) dy = x/(√μ+√x)²). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[The averaged ratio]\label{lem:app-os-average}
For $\mu>0$ and $x\ge0$,
\[
\int_0^\infty\varpi(y)\,\frac{x}{\mu y+x}\,\dif y=\frac{x}{(\sqrt\mu+\sqrt x)^2}.
\]
The right side is nondecreasing in $x$ and at most $\min\{x/\mu,\,1,\,x/(\mu+x)\}$.
Consequently
\begin{equation}\label{eqn:app-os-mbar}
m^\varpi_\nu(\mu)\defeq\int_0^\infty\varpi(y)\,m_\nu(\mu y)\,\dif y=\int\frac{x\,\nu(\dif x)}{(\sqrt\mu+\sqrt x)^2}\le m_\nu(\mu).
\end{equation}
\end{lemma}
-/
theorem lem_app_os_average_i
    {mu : ℝ} (hmu : 0 < mu) {x : ℝ} (hx : 0 ≤ x) :
    ∫ y in Ioi (0 : ℝ), varpi y * (x / (mu * y + x)) = x / (Real.sqrt mu + Real.sqrt x) ^ 2 := by
  have hq : 0 < Real.sqrt mu := Real.sqrt_pos.2 hmu
  have hr := Real.sqrt_nonneg x
  have hqq : Real.sqrt mu ^ 2 = mu := Real.sq_sqrt hmu.le
  have hrr : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  rcases hr.eq_or_lt with h0 | hpos
  · have hx0 : x = 0 := by
      rw [← hrr, ← h0]; ring
    subst hx0
    simp
  · set s := Real.sqrt x / Real.sqrt mu with hsdef
    have hs : 0 < s := div_pos hpos hq
    have hs2 : s ^ 2 = x / mu := by
      rw [hsdef, div_pow, hrr, hqq]
    have hxpos : 0 < x := by rw [← hrr]; positivity
    have hpt : Set.EqOn (fun y : ℝ => varpi y * (x / (mu * y + x)))
        (fun y : ℝ => (2 / Real.pi) * (Real.sqrt y / (1 + y) ^ 2 * (s ^ 2 / (y + s ^ 2))))
        (Ioi (0 : ℝ)) := by
      intro y hy
      have hy' : (0 : ℝ) < y := hy
      dsimp only
      rw [os_mass_varpi_eq, hs2]
      have : mu * y + x ≠ 0 := by positivity
      have : y + x / mu ≠ 0 := by positivity
      field_simp
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, os_avg_core s hs]
    have hxs : Real.sqrt x = s * Real.sqrt mu := by
      rw [hsdef]; field_simp
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have h1s : (1 + s) ≠ 0 := by positivity
    have hxe : x = s ^ 2 * mu := by rw [hs2]; field_simp
    have hsum : Real.sqrt mu + s * Real.sqrt mu = Real.sqrt mu * (1 + s) := by ring
    rw [hxs, hsum, mul_pow, hqq]
    rw [hxe]
    field_simp

/-- Label `lem:app-os-average`, part (ii) (the right side is nondecreasing in x and at most min{x/μ, 1, x/(μ+x)}). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[The averaged ratio]\label{lem:app-os-average}
For $\mu>0$ and $x\ge0$,
\[
\int_0^\infty\varpi(y)\,\frac{x}{\mu y+x}\,\dif y=\frac{x}{(\sqrt\mu+\sqrt x)^2}.
\]
The right side is nondecreasing in $x$ and at most $\min\{x/\mu,\,1,\,x/(\mu+x)\}$.
Consequently
\begin{equation}\label{eqn:app-os-mbar}
m^\varpi_\nu(\mu)\defeq\int_0^\infty\varpi(y)\,m_\nu(\mu y)\,\dif y=\int\frac{x\,\nu(\dif x)}{(\sqrt\mu+\sqrt x)^2}\le m_\nu(\mu).
\end{equation}
\end{lemma}
-/
theorem lem_app_os_average_ii
    {mu : ℝ} (hmu : 0 < mu) :
    MonotoneOn (fun x : ℝ => x / (Real.sqrt mu + Real.sqrt x) ^ 2) (Ici (0 : ℝ)) ∧
      ∀ x : ℝ, 0 ≤ x →
        x / (Real.sqrt mu + Real.sqrt x) ^ 2 ≤ x / mu ∧
        x / (Real.sqrt mu + Real.sqrt x) ^ 2 ≤ 1 ∧
        x / (Real.sqrt mu + Real.sqrt x) ^ 2 ≤ x / (mu + x) := by
  have hs : 0 < Real.sqrt mu := Real.sqrt_pos.2 hmu
  have hsq : ∀ x : ℝ, 0 ≤ x → Real.sqrt x ^ 2 = x := fun x hx => Real.sq_sqrt hx
  have hden : ∀ x : ℝ, 0 ≤ x → 0 < (Real.sqrt mu + Real.sqrt x) ^ 2 := fun x hx => by
    have := Real.sqrt_nonneg x
    positivity
  refine ⟨?_, fun x hx => ⟨?_, ?_, ?_⟩⟩
  · intro x hx x' hx' hxx'
    simp only [mem_Ici] at hx hx'
    have hp := Real.sqrt_nonneg x
    have hq := Real.sqrt_nonneg x'
    have hpx := hsq x hx
    have hqx := hsq x' hx'
    have hle : Real.sqrt x ≤ Real.sqrt x' := Real.sqrt_le_sqrt hxx'
    show x / (Real.sqrt mu + Real.sqrt x) ^ 2 ≤ x' / (Real.sqrt mu + Real.sqrt x') ^ 2
    rw [div_le_div_iff₀ (hden x hx) (hden x' hx')]
    have key : Real.sqrt x * (Real.sqrt mu + Real.sqrt x') ≤ Real.sqrt x' * (Real.sqrt mu + Real.sqrt x) := by
      nlinarith
    have key2 : 0 ≤ Real.sqrt x * (Real.sqrt mu + Real.sqrt x') := by positivity
    have h2 : (Real.sqrt x * (Real.sqrt mu + Real.sqrt x')) ^ 2 ≤ (Real.sqrt x' * (Real.sqrt mu + Real.sqrt x)) ^ 2 :=
      pow_le_pow_left₀ key2 key 2
    nlinarith [h2]
  · apply div_le_div_of_nonneg_left hx hmu
    have := Real.sqrt_nonneg x
    nlinarith [Real.sq_sqrt hmu.le]
  · rw [div_le_one (hden x hx)]
    have := Real.sqrt_nonneg x
    have := mul_nonneg hs.le this
    nlinarith [hsq x hx]
  · apply div_le_div_of_nonneg_left hx (by positivity)
    have := Real.sqrt_nonneg x
    have := mul_nonneg hs.le this
    nlinarith [hsq x hx, Real.sq_sqrt hmu.le]

/-- Private helper (P-G2.2.P8): `varpi` is measurable. -/
private lemma os_p8_varpi_meas : Measurable varpi := by
  unfold varpi
  fun_prop

/-- Private helper (P-G2.2.P8): `ν`-a.e. nonnegativity from `ν(Iio 0) = 0`. -/
private lemma os_p8_ae_nonneg {ν : Measure ℝ} (hν : ν (Iio 0) = 0) : ∀ᵐ x ∂ν, 0 ≤ x := by
  rw [ae_iff]
  have h : {a : ℝ | ¬ (0 ≤ a)} = Iio 0 := by ext; simp
  rw [h]; exact hν

/-- Private helper (P-G2.2.P8): elementary three-sided bound for `√(1-m)` with `m ∈ [0,1]`. -/
private lemma os_p8_defect_pt {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    m / 2 ≤ 1 - Real.sqrt (1 - m) ∧ 1 - Real.sqrt (1 - m) ≤ m := by
  have ht : 0 ≤ 1 - m := by linarith
  have hs : 0 ≤ Real.sqrt (1 - m) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (1 - m) ^ 2 = 1 - m := Real.sq_sqrt ht
  have hs1 : Real.sqrt (1 - m) ≤ 1 := by nlinarith
  constructor
  · nlinarith [sq_nonneg m]
  · nlinarith [mul_nonneg hs (sub_nonneg.2 hs1)]

/-- Private helper (P-G2.2.P8): pointwise bound `|ϖ(y) x/(μy+x)| ≤ ϖ(y)` for `x ≥ 0`. -/
private lemma os_p8_bound {mu : ℝ} (hmu : 0 < mu) (y x : ℝ) (hx : 0 ≤ x) :
    ‖varpi y * (x / (mu * y + x))‖ ≤ varpi y := by
  by_cases hy : 0 < y
  · have hnn : 0 ≤ varpi y := (os_repr_varpi_pos hy).le
    have hpos : 0 < mu * y := mul_pos hmu hy
    have hden : 0 < mu * y + x := by linarith
    have h0 : 0 ≤ x / (mu * y + x) := div_nonneg hx hden.le
    have h1 : x / (mu * y + x) ≤ 1 := (div_le_one hden).2 (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn, abs_of_nonneg h0]
    exact mul_le_of_le_one_right hnn h1
  · have hz : varpi y = 0 := by
      unfold varpi
      rw [Real.sqrt_eq_zero'.mpr (not_lt.1 hy)]
      simp
    rw [hz]
    simp

/-- Label `lem:app-os-average`, part (iii) (m^ϖ_ν(μ) = ∫ x ν(dx)/(√μ+√x)²). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[The averaged ratio]\label{lem:app-os-average}
For $\mu>0$ and $x\ge0$,
\[
\int_0^\infty\varpi(y)\,\frac{x}{\mu y+x}\,\dif y=\frac{x}{(\sqrt\mu+\sqrt x)^2}.
\]
The right side is nondecreasing in $x$ and at most $\min\{x/\mu,\,1,\,x/(\mu+x)\}$.
Consequently
\begin{equation}\label{eqn:app-os-mbar}
m^\varpi_\nu(\mu)\defeq\int_0^\infty\varpi(y)\,m_\nu(\mu y)\,\dif y=\int\frac{x\,\nu(\dif x)}{(\sqrt\mu+\sqrt x)^2}\le m_\nu(\mu).
\end{equation}
\end{lemma}
-/
theorem lem_app_os_average_iii
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) {mu : ℝ} (hmu : 0 < mu) :
    mBarNu ν mu = ∫ x, x / (Real.sqrt mu + Real.sqrt x) ^ 2 ∂ν := by
  have hae : ∀ᵐ x ∂ν, 0 ≤ x := os_p8_ae_nonneg hν
  have hFm : Measurable (fun p : ℝ × ℝ => varpi p.1 * (p.2 / (mu * p.1 + p.2))) :=
    (os_p8_varpi_meas.comp measurable_fst).mul
      (measurable_snd.div ((measurable_const.mul measurable_fst).add measurable_snd))
  have hvi : Integrable varpi (volume.restrict (Ioi (0 : ℝ))) := os_repr_varpi_int
  have hint : Integrable (fun p : ℝ × ℝ => varpi p.1 * (p.2 / (mu * p.1 + p.2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod ν) := by
    refine Integrable.mono' (hvi.comp_fst ν) hFm.aestronglyMeasurable ?_
    have hset : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod ν), 0 ≤ p.2 := by
      rw [ae_iff]
      have hs : {p : ℝ × ℝ | ¬ 0 ≤ p.2} = (univ : Set ℝ) ×ˢ Iio 0 := by
        ext p
        simp
      rw [hs, Measure.prod_prod, hν, mul_zero]
    filter_upwards [hset] with p hp
    exact os_p8_bound hmu p.1 p.2 hp
  have hinner : ∀ y : ℝ, varpi y * mNu ν (mu * y) = ∫ x, varpi y * (x / (mu * y + x)) ∂ν := by
    intro y
    unfold mNu
    rw [integral_const_mul]
  unfold mBarNu
  simp_rw [hinner]
  refine (integral_integral_swap (f := fun y x : ℝ => varpi y * (x / (mu * y + x))) hint).trans ?_
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  exact lem_app_os_average_i hmu hx

/-- Label `lem:app-os-average`, part (iv) (m^ϖ_ν(μ) ≤ m_ν(μ)). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[The averaged ratio]\label{lem:app-os-average}
For $\mu>0$ and $x\ge0$,
\[
\int_0^\infty\varpi(y)\,\frac{x}{\mu y+x}\,\dif y=\frac{x}{(\sqrt\mu+\sqrt x)^2}.
\]
The right side is nondecreasing in $x$ and at most $\min\{x/\mu,\,1,\,x/(\mu+x)\}$.
Consequently
\begin{equation}\label{eqn:app-os-mbar}
m^\varpi_\nu(\mu)\defeq\int_0^\infty\varpi(y)\,m_\nu(\mu y)\,\dif y=\int\frac{x\,\nu(\dif x)}{(\sqrt\mu+\sqrt x)^2}\le m_\nu(\mu).
\end{equation}
\end{lemma}
-/
theorem lem_app_os_average_iv
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) {mu : ℝ} (hmu : 0 < mu) :
    mBarNu ν mu ≤ mNu ν mu := by
  have hae : ∀ᵐ x ∂ν, 0 ≤ x := os_p8_ae_nonneg hν
  rw [lem_app_os_average_iii ν hν hmu]
  unfold mNu
  have hgm : Measurable (fun x : ℝ => x / (mu + x)) := by
    fun_prop
  have hgi : Integrable (fun x : ℝ => x / (mu + x)) ν := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hgm.aestronglyMeasurable ?_
    filter_upwards [hae] with x hx
    have hden : 0 < mu + x := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hx hden.le)]
    exact (div_le_one hden).2 (by linarith)
  refine integral_mono_of_nonneg ?_ hgi ?_
  · filter_upwards [hae] with x hx
    exact div_nonneg hx (sq_nonneg _)
  · filter_upwards [hae] with x hx
    exact ((lem_app_os_average_ii hmu).2 x hx).2.2

/-! ## Defect bounds (`lem:app-os-defect`) -/

/-- Label `lem:app-os-defect` (½ m^ϖ_ν(μ) ≤ 1 - χ_ν(μ) ≤ m^ϖ_ν(μ)). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Defect bounds]\label{lem:app-os-defect}
For every probability measure $\nu$ and every $\mu>0$,
\[
\tfrac12\,m^\varpi_\nu(\mu)\le1-\chi_\nu(\mu)\le m^\varpi_\nu(\mu).
\]
\end{lemma}
-/
theorem lem_app_os_defect
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) {mu : ℝ} (hmu : 0 < mu) :
    (1 / 2) * mBarNu ν mu ≤ 1 - sqrtEff ν mu ∧ 1 - sqrtEff ν mu ≤ mBarNu ν mu := by
  unfold mBarNu sqrtEff
  have hvi : Integrable varpi (volume.restrict (Ioi (0 : ℝ))) := os_repr_varpi_int
  have hvm : Measurable varpi := os_p8_varpi_meas
  have hmeas_m : AEStronglyMeasurable (fun y : ℝ => mNu ν (mu * y))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (os_repr_mNu_cont hν hmu).aestronglyMeasurable measurableSet_Ioi
  have hmeas_s : AEStronglyMeasurable (fun y : ℝ => Real.sqrt (1 - mNu ν (mu * y)))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Real.continuous_sqrt.comp_continuousOn
      ((continuousOn_const (c := (1 : ℝ))).sub (os_repr_mNu_cont hν hmu))).aestronglyMeasurable
      measurableSet_Ioi
  have hf1 : Integrable (fun y : ℝ => varpi y * mNu ν (mu * y)) (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.mono' hvi (hvm.aestronglyMeasurable.mul hmeas_m) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : (0 : ℝ) < y := hy
    have hv : 0 ≤ varpi y := (os_repr_varpi_pos hy').le
    obtain ⟨h1, h2⟩ := os_repr_sub_pos hν (mul_pos hmu hy')
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hv (by linarith))]
    exact mul_le_of_le_one_right hv (by linarith)
  have hf2 : Integrable (fun y : ℝ => varpi y * Real.sqrt (1 - mNu ν (mu * y)))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.mono' hvi (hvm.aestronglyMeasurable.mul hmeas_s) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : (0 : ℝ) < y := hy
    have hv : 0 ≤ varpi y := (os_repr_varpi_pos hy').le
    obtain ⟨h1, h2⟩ := os_repr_sub_pos hν (mul_pos hmu hy')
    have hsq1 : Real.sqrt (1 - mNu ν (mu * y)) ≤ 1 := by
      have := Real.sqrt_le_sqrt (show 1 - mNu ν (mu * y) ≤ 1 by linarith)
      rwa [Real.sqrt_one] at this
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hv (Real.sqrt_nonneg _))]
    exact mul_le_of_le_one_right hv hsq1
  have hone : ∫ y in Ioi (0 : ℝ), varpi y = 1 := os_mass_one
  have hsplit : ∫ y in Ioi (0 : ℝ), (varpi y - varpi y * Real.sqrt (1 - mNu ν (mu * y)))
      = 1 - ∫ y in Ioi (0 : ℝ), varpi y * Real.sqrt (1 - mNu ν (mu * y)) := by
    rw [integral_sub hvi hf2, hone]
  constructor
  · rw [← hsplit, ← integral_const_mul]
    refine integral_mono_ae (hf1.const_mul _) (hvi.sub hf2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : (0 : ℝ) < y := hy
    have hv : 0 ≤ varpi y := (os_repr_varpi_pos hy').le
    obtain ⟨h1, h2⟩ := os_repr_sub_pos hν (mul_pos hmu hy')
    have key := (os_p8_defect_pt (m := mNu ν (mu * y)) (by linarith) (by linarith)).1
    nlinarith [mul_le_mul_of_nonneg_left key hv]
  · rw [← hsplit]
    refine integral_mono_ae (hvi.sub hf2) hf1 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : (0 : ℝ) < y := hy
    have hv : 0 ≤ varpi y := (os_repr_varpi_pos hy').le
    obtain ⟨h1, h2⟩ := os_repr_sub_pos hν (mul_pos hmu hy')
    have key := (os_p8_defect_pt (m := mNu ν (mu * y)) (by linarith) (by linarith)).2
    nlinarith [mul_le_mul_of_nonneg_left key hv]

/-! ## Smoothed count (`lem:app-os-count`) -/

/-- Label `lem:app-os-count`, part (i) (formula for 𝗌_ν(μ) as an integral against ν). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Smoothed count]\label{lem:app-os-count}
For a probability measure $\nu$ and $\mu>0$ put
\begin{equation}\label{eqn:app-os-count}
\mathsf s_\nu(\mu)\defeq1-m^\varpi_\nu(\mu)=\int\frac{1+2\sqrt{x/\mu}}{\big(1+\sqrt{x/\mu}\big)^2}\,\nu(\dif x)\in(0,1].
\end{equation}
Then
\[
\mathsf s_\nu(\mu)\le\chi_\nu(\mu)\le\sqrt{\mathsf s_\nu(\mu)} .
\]
\end{lemma}
-/
theorem lem_app_os_count_i
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) {mu : ℝ} (hmu : 0 < mu) :
    smoothCount ν mu = ∫ x, (1 + 2 * Real.sqrt (x / mu)) / (1 + Real.sqrt (x / mu)) ^ 2 ∂ν := by
  have hae : ∀ᵐ x ∂ν, 0 ≤ x := os_p8_ae_nonneg hν
  have hgm : Measurable (fun x : ℝ => x / (Real.sqrt mu + Real.sqrt x) ^ 2) := by
    fun_prop
  have hg : Integrable (fun x : ℝ => x / (Real.sqrt mu + Real.sqrt x) ^ 2) ν := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hgm.aestronglyMeasurable ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hx (sq_nonneg _))]
    exact ((lem_app_os_average_ii hmu).2 x hx).2.1
  have hpt : ∀ x : ℝ, 0 ≤ x →
      1 - x / (Real.sqrt mu + Real.sqrt x) ^ 2
        = (1 + 2 * Real.sqrt (x / mu)) / (1 + Real.sqrt (x / mu)) ^ 2 := by
    intro x hx
    have ha : 0 < Real.sqrt mu := Real.sqrt_pos.2 hmu
    have ha' : Real.sqrt mu ≠ 0 := ha.ne'
    have hb : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have h1 : Real.sqrt mu + Real.sqrt x ≠ 0 := ne_of_gt (by linarith)
    have hid : 1 - Real.sqrt x ^ 2 / (Real.sqrt mu + Real.sqrt x) ^ 2
        = (1 + 2 * (Real.sqrt x / Real.sqrt mu)) / (1 + Real.sqrt x / Real.sqrt mu) ^ 2 := by
      field_simp
      ring
    rw [Real.sq_sqrt hx] at hid
    rw [Real.sqrt_div hx mu]
    exact hid
  unfold smoothCount
  rw [lem_app_os_average_iii ν hν hmu]
  calc 1 - ∫ x, x / (Real.sqrt mu + Real.sqrt x) ^ 2 ∂ν
      = ∫ x, (1 - x / (Real.sqrt mu + Real.sqrt x) ^ 2) ∂ν := by
        rw [integral_sub (integrable_const (1 : ℝ)) hg]
        simp
    _ = ∫ x, (1 + 2 * Real.sqrt (x / mu)) / (1 + Real.sqrt (x / mu)) ^ 2 ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with x hx
        exact hpt x hx

/-- Label `lem:app-os-count`, part (ii) (𝗌_ν(μ) ∈ (0,1]). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Smoothed count]\label{lem:app-os-count}
For a probability measure $\nu$ and $\mu>0$ put
\begin{equation}\label{eqn:app-os-count}
\mathsf s_\nu(\mu)\defeq1-m^\varpi_\nu(\mu)=\int\frac{1+2\sqrt{x/\mu}}{\big(1+\sqrt{x/\mu}\big)^2}\,\nu(\dif x)\in(0,1].
\end{equation}
Then
\[
\mathsf s_\nu(\mu)\le\chi_\nu(\mu)\le\sqrt{\mathsf s_\nu(\mu)} .
\]
\end{lemma}
-/
theorem lem_app_os_count_ii
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) {mu : ℝ} (hmu : 0 < mu) :
    smoothCount ν mu ∈ Ioc (0 : ℝ) 1 := by
  have hae : ∀ᵐ x ∂ν, 0 ≤ x := os_p8_ae_nonneg hν
  have hpos : ∀ x : ℝ, 0 < (1 + 2 * Real.sqrt (x / mu)) / (1 + Real.sqrt (x / mu)) ^ 2 :=
    fun x => by positivity
  have hle : ∀ x : ℝ, (1 + 2 * Real.sqrt (x / mu)) / (1 + Real.sqrt (x / mu)) ^ 2 ≤ 1 := by
    intro x
    rw [div_le_one (by positivity)]
    nlinarith [Real.sqrt_nonneg (x / mu), sq_nonneg (Real.sqrt (x / mu))]
  have hmeas : Measurable
      (fun x : ℝ => (1 + 2 * Real.sqrt (x / mu)) / (1 + Real.sqrt (x / mu)) ^ 2) := by
    fun_prop
  have hint : Integrable
      (fun x : ℝ => (1 + 2 * Real.sqrt (x / mu)) / (1 + Real.sqrt (x / mu)) ^ 2) ν := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (hpos x)]
    exact hle x
  have hsupp : Function.support
      (fun x : ℝ => (1 + 2 * Real.sqrt (x / mu)) / (1 + Real.sqrt (x / mu)) ^ 2) = Set.univ :=
    Set.eq_univ_of_forall fun x => (hpos x).ne'
  rw [lem_app_os_count_i ν hν hmu]
  refine Set.mem_Ioc.2 ⟨?_, ?_⟩
  · refine (integral_pos_iff_support_of_nonneg_ae ?_ hint).2 ?_
    · filter_upwards [hae] with x hx
      exact (hpos x).le
    · rw [hsupp, measure_univ]
      norm_num
  · calc ∫ x, (1 + 2 * Real.sqrt (x / mu)) / (1 + Real.sqrt (x / mu)) ^ 2 ∂ν
        ≤ ∫ _x, (1 : ℝ) ∂ν := by
          refine integral_mono_ae hint (integrable_const (1 : ℝ)) ?_
          filter_upwards [hae] with x hx
          exact hle x
      _ = 1 := by simp

/-- Label `lem:app-os-count`, part (iii) (𝗌_ν(μ) ≤ χ_ν(μ) ≤ √(𝗌_ν(μ))). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Smoothed count]\label{lem:app-os-count}
For a probability measure $\nu$ and $\mu>0$ put
\begin{equation}\label{eqn:app-os-count}
\mathsf s_\nu(\mu)\defeq1-m^\varpi_\nu(\mu)=\int\frac{1+2\sqrt{x/\mu}}{\big(1+\sqrt{x/\mu}\big)^2}\,\nu(\dif x)\in(0,1].
\end{equation}
Then
\[
\mathsf s_\nu(\mu)\le\chi_\nu(\mu)\le\sqrt{\mathsf s_\nu(\mu)} .
\]
\end{lemma}
-/
theorem lem_app_os_count_iii
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) {mu : ℝ} (hmu : 0 < mu) :
    smoothCount ν mu ≤ sqrtEff ν mu ∧ sqrtEff ν mu ≤ Real.sqrt (smoothCount ν mu) := by
  have hs : 0 < smoothCount ν mu := (Set.mem_Ioc.1 (lem_app_os_count_ii ν hν hmu)).1
  refine ⟨?_, ?_⟩
  · unfold smoothCount
    linarith [(lem_app_os_defect ν hν hmu).2]
  have hae : ∀ᵐ x ∂ν, 0 ≤ x := os_p8_ae_nonneg hν
  have hvm : Measurable varpi := os_p8_varpi_meas
  have hvi : Integrable varpi (volume.restrict (Ioi (0 : ℝ))) := os_repr_varpi_int
  have hmeas_m : AEStronglyMeasurable (fun y : ℝ => mNu ν (mu * y))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (os_repr_mNu_cont hν hmu).aestronglyMeasurable measurableSet_Ioi
  have hmeas_s : AEStronglyMeasurable (fun y : ℝ => Real.sqrt (1 - mNu ν (mu * y)))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Real.continuous_sqrt.comp_continuousOn
      ((continuousOn_const (c := (1 : ℝ))).sub (os_repr_mNu_cont hν hmu))).aestronglyMeasurable
      measurableSet_Ioi
  have hfm : Integrable (fun y : ℝ => varpi y * mNu ν (mu * y))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.mono' hvi (hvm.aestronglyMeasurable.mul hmeas_m) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : (0 : ℝ) < y := hy
    have hv : 0 ≤ varpi y := (os_repr_varpi_pos hy').le
    obtain ⟨h1, h2⟩ := os_repr_sub_pos hν (mul_pos hmu hy')
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hv (by linarith))]
    exact mul_le_of_le_one_right hv (by linarith)
  have hL : Integrable
      (fun y : ℝ => 2 * Real.sqrt (smoothCount ν mu) * (varpi y * Real.sqrt (1 - mNu ν (mu * y))))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.mono' (hvi.const_mul (2 * Real.sqrt (smoothCount ν mu)))
      ((hvm.aestronglyMeasurable.mul hmeas_s).const_mul _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : (0 : ℝ) < y := hy
    have hv : 0 ≤ varpi y := (os_repr_varpi_pos hy').le
    obtain ⟨h1, h2⟩ := os_repr_sub_pos hν (mul_pos hmu hy')
    have hsq1 : Real.sqrt (1 - mNu ν (mu * y)) ≤ 1 := by
      have := Real.sqrt_le_sqrt (show 1 - mNu ν (mu * y) ≤ 1 by linarith)
      rwa [Real.sqrt_one] at this
    have hc : 0 ≤ 2 * Real.sqrt (smoothCount ν mu) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc (mul_nonneg hv (Real.sqrt_nonneg _)))]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hv hsq1) hc
  have hR : Integrable
      (fun y : ℝ => varpi y - varpi y * mNu ν (mu * y) + smoothCount ν mu * varpi y)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (hvi.sub hfm).add (hvi.const_mul _)
  have hineq : ∫ y in Ioi (0 : ℝ), 2 * Real.sqrt (smoothCount ν mu) *
        (varpi y * Real.sqrt (1 - mNu ν (mu * y)))
      ≤ ∫ y in Ioi (0 : ℝ), (varpi y - varpi y * mNu ν (mu * y) + smoothCount ν mu * varpi y) := by
    refine integral_mono_ae hL hR ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : (0 : ℝ) < y := hy
    have hv : 0 ≤ varpi y := (os_repr_varpi_pos hy').le
    obtain ⟨h1, h2⟩ := os_repr_sub_pos hν (mul_pos hmu hy')
    have e1 : Real.sqrt (1 - mNu ν (mu * y)) ^ 2 = 1 - mNu ν (mu * y) := Real.sq_sqrt h1.le
    have e2 : Real.sqrt (smoothCount ν mu) ^ 2 = smoothCount ν mu := Real.sq_sqrt hs.le
    have hid : varpi y * (Real.sqrt (1 - mNu ν (mu * y)) - Real.sqrt (smoothCount ν mu)) ^ 2
        = varpi y - varpi y * mNu ν (mu * y) + smoothCount ν mu * varpi y
          - 2 * Real.sqrt (smoothCount ν mu) * (varpi y * Real.sqrt (1 - mNu ν (mu * y))) := by
      linear_combination varpi y * e1 + varpi y * e2
    have hnn := mul_nonneg hv (sq_nonneg (Real.sqrt (1 - mNu ν (mu * y)) - Real.sqrt (smoothCount ν mu)))
    linarith
  have hLval : ∫ y in Ioi (0 : ℝ), 2 * Real.sqrt (smoothCount ν mu) *
        (varpi y * Real.sqrt (1 - mNu ν (mu * y)))
      = 2 * Real.sqrt (smoothCount ν mu) * sqrtEff ν mu := by
    unfold sqrtEff
    rw [integral_const_mul]
  have hRval : ∫ y in Ioi (0 : ℝ), (varpi y - varpi y * mNu ν (mu * y) + smoothCount ν mu * varpi y)
      = 2 * smoothCount ν mu := by
    have hsc : smoothCount ν mu = 1 - ∫ y in Ioi (0 : ℝ), varpi y * mNu ν (mu * y) := rfl
    have h1 : ∫ y in Ioi (0 : ℝ), (varpi y - varpi y * mNu ν (mu * y) + smoothCount ν mu * varpi y)
        = (∫ y in Ioi (0 : ℝ), (varpi y - varpi y * mNu ν (mu * y)))
          + ∫ y in Ioi (0 : ℝ), smoothCount ν mu * varpi y :=
      integral_add (hvi.sub hfm) (hvi.const_mul _)
    rw [h1, integral_sub hvi hfm, integral_const_mul, os_mass_one, hsc]
    ring
  rw [hLval, hRval] at hineq
  have hss : Real.sqrt (smoothCount ν mu) * Real.sqrt (smoothCount ν mu) = smoothCount ν mu :=
    Real.mul_self_sqrt hs.le
  have hsqpos : 0 < Real.sqrt (smoothCount ν mu) := Real.sqrt_pos.2 hs
  refine le_of_mul_le_mul_left ?_ hsqpos
  linarith [hineq, hss]

/-! ## Identity covariance, part (i) (`cor:app-os-identity`) -/

/-- Helper: `m_ν` of the unit Dirac mass. -/
private lemma os_id_mNu_dirac (c : ℝ) : mNu (Measure.dirac (1 : ℝ)) c = 1 / (c + 1) := by
  unfold mNu
  rw [integral_dirac]

/-- Helper: the `sqrtEff` integrand for the unit Dirac mass at `μ = 1`. -/
private lemma os_id_integrand {y : ℝ} (hy : 0 < y) :
    varpi y * Real.sqrt (1 - mNu (Measure.dirac (1 : ℝ)) (1 * y))
      = (2 / Real.pi) * (y / ((1 + y) ^ 2 * Real.sqrt (1 + y))) := by
  rw [os_id_mNu_dirac]
  have hpos : 0 < 1 + y := by linarith
  have h1 : 1 - 1 / (1 * y + 1) = y / (1 + y) := by
    have hne : (1 + y) ≠ 0 := hpos.ne'
    field_simp
    ring
  have hsy : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy.le
  have key : Real.sqrt y * Real.sqrt y / ((1 + y) ^ 2 * Real.sqrt (1 + y))
      = y / ((1 + y) ^ 2 * Real.sqrt (1 + y)) := by
    rw [hsy]
  have hne : (1 + y) ≠ 0 := hpos.ne'
  have ht : Real.sqrt (1 + y) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  rw [h1, Real.sqrt_div hy.le, varpi, ← key]
  field_simp

/-- Helper: antiderivative of `y / ((1+y)^2 √(1+y))`, written with `t = (√(1+y))⁻¹`. -/
private lemma os_id_anti {y : ℝ} (hy : -1 < y) :
    HasDerivAt (fun x : ℝ => -2 * (Real.sqrt (1 + x))⁻¹ + 2 / 3 * (Real.sqrt (1 + x))⁻¹ ^ 3)
      (y / ((1 + y) ^ 2 * Real.sqrt (1 + y))) y := by
  have hpos : 0 < 1 + y := by linarith
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 y := (hasDerivAt_id y).const_add 1
  have hs : HasDerivAt (fun x : ℝ => Real.sqrt (1 + x)) (1 / (2 * Real.sqrt (1 + y))) y := by
    have := h1.sqrt hpos.ne'
    simpa using this
  have hi : HasDerivAt (fun x : ℝ => (Real.sqrt (1 + x))⁻¹)
      (-(1 / (2 * Real.sqrt (1 + y))) / Real.sqrt (1 + y) ^ 2) y :=
    hs.inv (Real.sqrt_pos.2 hpos).ne'
  have hp := hi.pow 3
  have hd := (hi.const_mul (-2)).add (hp.const_mul (2 / 3))
  refine hd.congr_deriv ?_
  generalize hT : Real.sqrt (1 + y) = t
  have ht : t ≠ 0 := by
    rw [← hT]
    exact (Real.sqrt_pos.2 hpos).ne'
  have hsq : t ^ 2 = 1 + y := by
    rw [← hT]
    exact Real.sq_sqrt hpos.le
  have hyt : y = t ^ 2 - 1 := by linarith
  subst hyt
  norm_num
  field_simp
  ring

/-- Helper: `∫_0^∞ y / ((1+y)² √(1+y)) dy = 4/3`. -/
private lemma os_id_int : ∫ y in Ioi (0 : ℝ), y / ((1 + y) ^ 2 * Real.sqrt (1 + y)) = 4 / 3 := by
  have hcont : ContinuousWithinAt
      (fun x : ℝ => -2 * (Real.sqrt (1 + x))⁻¹ + 2 / 3 * (Real.sqrt (1 + x))⁻¹ ^ 3)
      (Ici 0) 0 :=
    (os_id_anti (by norm_num : (-1 : ℝ) < 0)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt
      (fun x : ℝ => -2 * (Real.sqrt (1 + x))⁻¹ + 2 / 3 * (Real.sqrt (1 + x))⁻¹ ^ 3)
      (x / ((1 + x) ^ 2 * Real.sqrt (1 + x))) x :=
    fun x hx => os_id_anti (by linarith [show (0 : ℝ) < x from hx])
  have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ x / ((1 + x) ^ 2 * Real.sqrt (1 + x)) := fun x hx =>
    div_nonneg (le_of_lt hx) (by positivity)
  have htend : Tendsto
      (fun x : ℝ => -2 * (Real.sqrt (1 + x))⁻¹ + 2 / 3 * (Real.sqrt (1 + x))⁻¹ ^ 3)
      atTop (𝓝 0) := by
    have hT : Tendsto (fun x : ℝ => Real.sqrt (1 + x)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    have hI : Tendsto (fun x : ℝ => (Real.sqrt (1 + x))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hT
    have := (hI.const_mul (-2)).add ((hI.pow 3).const_mul (2 / 3))
    simpa using this
  rw [integral_Ioi_of_hasDerivAt_of_nonneg
    (g := fun x : ℝ => -2 * (Real.sqrt (1 + x))⁻¹ + 2 / 3 * (Real.sqrt (1 + x))⁻¹ ^ 3)
    (g' := fun x => x / ((1 + x) ^ 2 * Real.sqrt (1 + x))) hcont hderiv hpos htend]
  norm_num

/-- Label `cor:app-os-identity`, part (i) (𝔡^os_{δ_1}(1) = 4√2/(3π) = 8/(3π√2)). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{corollary}[Identity covariance]\label{cor:app-os-identity}
\begin{enumerate}[label=(\roman*)]
\item One has $\mathfrak d^{\rm os}_{\delta_1}(1)=\dfrac{4\sqrt2}{3\pi}=\dfrac{8}{3\pi\sqrt2}$.
\item If $\Sigmaout=\Id_N$, $\Nout=\Nin=N$, $\gamma=N/B$ and $\epsilon_{\rm os}<1$, then
\[
\mathfrak d_0(1)=\frac{8\,\vartheta}{3\pi\sqrt{2\sw2\gamma}}\qquad\text{for some }\vartheta\in\big[1-\epsilon_{\rm os},(1-\epsilon_{\rm os})^{-1}\big].
\]
\end{enumerate}
\end{corollary}
-/
theorem cor_app_os_identity_i
 :
    dOsSq (Measure.dirac (1 : ℝ)) 1 = 4 * Real.sqrt 2 / (3 * Real.pi) ∧
      4 * Real.sqrt 2 / (3 * Real.pi) = 8 / (3 * Real.pi * Real.sqrt 2) := by
  have hν : (Measure.dirac (1 : ℝ)) (Iio 0) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iio]
    simp
  have hrep := lem_app_os_repr_ii (Measure.dirac (1 : ℝ)) hν one_pos
  have hcongr : ∫ y in Ioi (0 : ℝ), varpi y * Real.sqrt (1 - mNu (Measure.dirac (1 : ℝ)) (1 * y))
      = ∫ y in Ioi (0 : ℝ), (2 / Real.pi) * (y / ((1 + y) ^ 2 * Real.sqrt (1 + y))) :=
    setIntegral_congr_fun measurableSet_Ioi (fun y hy => os_id_integrand hy)
  have hint : sqrtEff (Measure.dirac (1 : ℝ)) 1 = 8 / (3 * Real.pi) := by
    unfold sqrtEff
    rw [hcongr, integral_const_mul, os_id_int]
    ring
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsq1 : Real.sqrt (1 / 2 : ℝ) = Real.sqrt 2 / 2 := by
    rw [Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_one,
      div_eq_div_iff (Real.sqrt_pos.2 two_pos).ne' two_ne_zero]
    linarith [h2]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  refine ⟨?_, ?_⟩
  · rw [hrep, hint, hsq1]
    ring
  · rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (12 * Real.pi) * h2

end

end Muon.Oversampled

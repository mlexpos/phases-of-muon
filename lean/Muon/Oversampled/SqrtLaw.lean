import Mathlib
import Muon.Oversampled.Profile
import Muon.Oversampled.Representation

/-!
# Oversampled square-root law (Appendix G2, work package L-G2.3)

Source of record: snapshot `cr-2026-10-23`, `sections/12-oversampled/section.tex`.
Scope: `thm:app-os-sqrt` parts (i), (ii); the helper `chi_ge_Cstar_sqrt` (the lower bound
`C_* √(1 - m_ν(μ)) ≤ χ_ν(μ)` extracted from the proof of part (i)); `prop:app-os-head`
parts (i), (ii). Part (iii) of `thm:app-os-sqrt` belongs to L-G2.7.

Reuses `mNu`, `profileRoot`, `dOs`, `dOsSq`, `varpi`, `sqrtEff` (`Muon.Oversampled.Profile`)
and `Upsilon`, `cNu`, `varpiMeasure`, `mBarNu`, `smoothCount` (`Muon.Oversampled.Representation`).
Measure representation as fixed by L-G2.1: `ν : Measure ℝ`, `[IsProbabilityMeasure ν]`,
`ν (Set.Iio 0) = 0`. The sequence statement of `prop:app-os-head`(ii) takes sequences of such
measures indexed by `ℕ`.
-/

open MeasureTheory Set Filter Topology

namespace Muon.Oversampled

noncomputable section

/-- The constant `C_* := 1/2 + 2 log 2 / π` of `thm:app-os-sqrt`.

Label `thm:app-os-sqrt`. Snapshot `cr-2026-10-23`. Statement verbatim (the constant is defined
in the theorem header):

\begin{theorem}[Square-root law]\label{thm:app-os-sqrt}
Let $C_*\defeq\frac12+\frac{2\log2}{\pi}\approx0.9413$.
\end{theorem}
-/
def cStar : ℝ :=
  1 / 2 + 2 * Real.log 2 / Real.pi

/-! ### Private helpers for the square-root law (proved here; no external sorries used) -/

private lemma sa_ae_nonneg {ν : Measure ℝ} (hν : ν (Iio 0) = 0) : ∀ᵐ x ∂ν, 0 ≤ x := by
  rw [ae_iff]
  have h : {a : ℝ | ¬ (0 ≤ a)} = Iio 0 := by ext; simp
  rw [h]; exact hν

private lemma sa_ratio_bounds {ν : Measure ℝ} (hν : ν (Iio 0) = 0) {c : ℝ} (hc : 0 ≤ c) :
    ∀ᵐ x ∂ν, 0 ≤ x / (c + x) ∧ x / (c + x) ≤ 1 := by
  filter_upwards [sa_ae_nonneg hν] with x hx
  have h2 : 0 ≤ c + x := by linarith
  exact ⟨div_nonneg hx h2, div_le_one_of_le₀ (by linarith) h2⟩

private lemma sa_ratio_integrable {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {c : ℝ} (hc : 0 ≤ c) :
    Integrable (fun x : ℝ => x / (c + x)) ν := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ => x / (c + x)).aestronglyMeasurable
  · filter_upwards [sa_ratio_bounds hν hc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2

private lemma sa_mNu_nonneg {ν : Measure ℝ} (hν : ν (Iio 0) = 0) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ mNu ν c :=
  integral_nonneg_of_ae (by filter_upwards [sa_ratio_bounds hν hc] with x hx using hx.1)

private lemma sa_mNu_le_one {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {c : ℝ} (hc : 0 ≤ c) : mNu ν c ≤ 1 := by
  unfold mNu
  have h := integral_mono_ae (sa_ratio_integrable hν hc) (integrable_const (1 : ℝ))
    (by filter_upwards [sa_ratio_bounds hν hc] with x hx using hx.2)
  simpa using h

private lemma sa_mNu_anti {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μ y : ℝ} (hμ : 0 < μ) (hy : 1 ≤ y) : mNu ν (μ * y) ≤ mNu ν μ := by
  unfold mNu
  refine integral_mono_ae (sa_ratio_integrable hν (mul_nonneg hμ.le (by linarith)))
    (sa_ratio_integrable hν hμ.le) ?_
  filter_upwards [sa_ae_nonneg hν] with x hx
  have h1 : 0 < μ + x := by linarith
  have h2 : μ + x ≤ μ * y + x := by nlinarith
  exact div_le_div_of_nonneg_left hx h1 h2

private lemma sa_mNu_measurable (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Measurable (mNu ν) := by
  have hf : StronglyMeasurable (Function.uncurry fun (c x : ℝ) => x / (c + x)) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ => p.2 / (p.1 + p.2)).stronglyMeasurable
  have h2 : StronglyMeasurable (fun c : ℝ => ∫ x, x / (c + x) ∂ν) := hf.integral_prod_right
  exact h2.measurable

private lemma sa_varpi_measurable : Measurable varpi := by
  unfold varpi; fun_prop

private lemma sa_varpi_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ varpi y := by
  unfold varpi
  exact div_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg y)) (sq_nonneg _)

private lemma sa_integrand_measurable (ν : Measure ℝ) [IsProbabilityMeasure ν] (μ : ℝ) :
    Measurable fun y : ℝ => varpi y * Real.sqrt (1 - mNu ν (μ * y)) := by
  have hm := sa_mNu_measurable ν
  have hv := sa_varpi_measurable
  fun_prop

/-- Integrability of the `sqrtEff` integrand on a measurable set where `y > 0`. -/
private lemma sa_integrand_integrableOn {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {μ : ℝ} (hμ : 0 < μ) {s : Set ℝ} (hsm : MeasurableSet s)
    (hs : ∀ y ∈ s, 0 < y) (hvi : IntegrableOn varpi s) :
    IntegrableOn (fun y : ℝ => varpi y * Real.sqrt (1 - mNu ν (μ * y))) s := by
  refine Integrable.mono' hvi (sa_integrand_measurable ν μ).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hsm] with y hy
  have hy0 := hs y hy
  have hv := sa_varpi_nonneg hy0.le
  have hm0 := sa_mNu_nonneg hν (mul_nonneg hμ.le hy0.le)
  rw [Real.norm_of_nonneg (mul_nonneg hv (Real.sqrt_nonneg _))]
  exact mul_le_of_le_one_right hv
    ((Real.sqrt_le_sqrt (by linarith : 1 - mNu ν (μ * y) ≤ 1)).trans_eq Real.sqrt_one)

private lemma sa_varpi_integrableOn_Ioc : IntegrableOn varpi (Ioc (0 : ℝ) 1) := by
  refine Integrable.mono' (integrableOn_const (C := (2 / Real.pi)) measure_Ioc_lt_top.ne) ?_ ?_
  · exact sa_varpi_measurable.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hy0 : 0 < y := hy.1
    have hs1 : Real.sqrt y ≤ 1 := by simpa using Real.sqrt_le_sqrt hy.2
    have h1 : 1 ≤ (1 + y) ^ 2 := by nlinarith
    have hq : Real.sqrt y / (1 + y) ^ 2 ≤ 1 :=
      div_le_one_of_le₀ (by linarith) (by linarith)
    rw [Real.norm_of_nonneg (sa_varpi_nonneg hy0.le)]
    unfold varpi
    rw [mul_div_assoc]
    exact mul_le_of_le_one_right (by positivity) hq

private lemma sa_rpow_three_halves {y : ℝ} (hy : 0 < y) :
    y ^ (-(3 : ℝ) / 2) = (y * Real.sqrt y)⁻¹ := by
  rw [show -(3 : ℝ) / 2 = -(1 + 1 / 2) by norm_num, Real.rpow_neg hy.le, Real.rpow_add hy,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

private lemma sa_varpi_integrableOn_Ioi : IntegrableOn varpi (Ioi (1 : ℝ)) := by
  have hpow : IntegrableOn (fun y : ℝ => y ^ (-(3 : ℝ) / 2)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  refine Integrable.mono' (g := fun y : ℝ => 2 / Real.pi * y ^ (-(3 : ℝ) / 2)) ?_ ?_ ?_
  · exact hpow.const_mul (2 / Real.pi)
  · exact sa_varpi_measurable.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy1 : 1 < y := hy
    have hy0 : 0 < y := by linarith
    have hs2 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
    have hpt : Real.sqrt y / (1 + y) ^ 2 ≤ (y * Real.sqrt y)⁻¹ := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by nlinarith) (mul_pos hy0 (Real.sqrt_pos.2 hy0))]
      have e : Real.sqrt y * (y * Real.sqrt y) = y * y := by
        rw [show Real.sqrt y * (y * Real.sqrt y) = y * (Real.sqrt y * Real.sqrt y) by ring, hs2]
      rw [e, one_mul]
      nlinarith
    rw [Real.norm_of_nonneg (sa_varpi_nonneg hy0.le), sa_rpow_three_halves hy0]
    unfold varpi
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hpt (by positivity)

private lemma sa_varpi_integral_Ioi :
    ∫ y in Ioi (1 : ℝ), varpi y = 2 / Real.pi * (Real.pi / 4 + 1 / 2) := by
  have h : ∫ y in Ioi (1 : ℝ), varpi y = 2 / Real.pi * ∫ y in Ioi (1 : ℝ), Real.sqrt y / (1 + y) ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext y
    unfold varpi
    ring
  rw [h, lem_app_os_integrals_ii]

/-- Key pointwise comparison: `y (1 - m_ν(μ)) ≤ 1 - m_ν(μ y)` for `0 < y ≤ 1`. -/
private lemma sa_key {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μ y : ℝ} (hμ : 0 < μ) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    y * (1 - mNu ν μ) ≤ 1 - mNu ν (μ * y) := by
  have hμy : 0 ≤ μ * y := (mul_pos hμ hy0).le
  have e1 : 1 - mNu ν (μ * y) = ∫ x, (1 - x / (μ * y + x)) ∂ν := by
    unfold mNu
    rw [integral_sub (integrable_const (1 : ℝ)) (sa_ratio_integrable hν hμy)]
    simp
  have e2 : 1 - mNu ν μ = ∫ x, (1 - x / (μ + x)) ∂ν := by
    unfold mNu
    rw [integral_sub (integrable_const (1 : ℝ)) (sa_ratio_integrable hν hμ.le)]
    simp
  rw [e1, e2, ← integral_const_mul]
  refine integral_mono_ae
    (((integrable_const (1 : ℝ)).sub (sa_ratio_integrable hν hμ.le)).const_mul y)
    ((integrable_const (1 : ℝ)).sub (sa_ratio_integrable hν hμy)) ?_
  filter_upwards [sa_ae_nonneg hν] with x hx
  have h1 : 0 < μ + x := by linarith
  have h2 : 0 < μ * y + x := by nlinarith
  have iden : 1 - x / (μ * y + x) - y * (1 - x / (μ + x))
      = μ ^ 2 * y * (1 - y) / ((μ * y + x) * (μ + x)) := by
    field_simp
    ring
  have hnn : 0 ≤ μ ^ 2 * y * (1 - y) / ((μ * y + x) * (μ + x)) :=
    div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hy0.le) (by linarith)) (mul_pos h2 h1).le
  linarith

private lemma sa_split {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μ : ℝ} (hμ : 0 < μ) :
    sqrtEff ν μ = (∫ y in Ioc (0 : ℝ) 1, varpi y * Real.sqrt (1 - mNu ν (μ * y))) +
      ∫ y in Ioi (1 : ℝ), varpi y * Real.sqrt (1 - mNu ν (μ * y)) := by
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) :=
    Set.disjoint_left.2 fun y h1 h2 => absurd (Set.mem_Ioi.1 h2) (not_lt.2 h1.2)
  have hI1 := sa_integrand_integrableOn hν hμ measurableSet_Ioc (fun y hy => hy.1)
    sa_varpi_integrableOn_Ioc
  have hI2 := sa_integrand_integrableOn hν hμ measurableSet_Ioi
    (fun y hy => by have := Set.mem_Ioi.1 hy; linarith) sa_varpi_integrableOn_Ioi
  unfold sqrtEff
  rw [← setIntegral_union hdisj measurableSet_Ioi hI1 hI2, Ioc_union_Ioi_eq_Ioi zero_le_one]

/-- Lower bound on the `(0,1]` piece of `sqrtEff`. -/
private lemma sa_lower_Ioc {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μ : ℝ} (hμ : 0 < μ) :
    Real.sqrt (1 - mNu ν μ) * (2 / Real.pi * (Real.log 2 - 1 / 2)) ≤
      ∫ y in Ioc (0 : ℝ) 1, varpi y * Real.sqrt (1 - mNu ν (μ * y)) := by
  have hI : ∫ y in Ioc (0 : ℝ) 1, Real.sqrt (1 - mNu ν μ) * (2 / Real.pi * (y / (1 + y) ^ 2))
      = Real.sqrt (1 - mNu ν μ) * (2 / Real.pi * (Real.log 2 - 1 / 2)) := by
    rw [integral_const_mul, integral_const_mul, ← integral_Icc_eq_integral_Ioc,
      lem_app_os_integrals_iii]
  rw [← hI]
  refine integral_mono_of_nonneg ?_ (sa_integrand_integrableOn hν hμ measurableSet_Ioc
    (fun y hy => hy.1) sa_varpi_integrableOn_Ioc) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by positivity) (div_nonneg hy.1.le (sq_nonneg _)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hy0 : 0 < y := hy.1
    have hkey := sa_key hν hμ hy0 hy.2
    have hsa : 0 ≤ 1 - mNu ν μ := by linarith [sa_mNu_le_one hν hμ.le]
    have hR : Real.sqrt y * Real.sqrt (1 - mNu ν μ) ≤ Real.sqrt (1 - mNu ν (μ * y)) := by
      rw [← Real.sqrt_mul hy0.le]
      exact Real.sqrt_le_sqrt hkey
    have hs2 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
    have hc : 0 ≤ 2 / Real.pi * Real.sqrt y / (1 + y) ^ 2 :=
      div_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (sq_nonneg _)
    calc Real.sqrt (1 - mNu ν μ) * (2 / Real.pi * (y / (1 + y) ^ 2))
        = (2 / Real.pi * Real.sqrt y / (1 + y) ^ 2) * (Real.sqrt y * Real.sqrt (1 - mNu ν μ)) := by
          linear_combination (-(2 / Real.pi) / (1 + y) ^ 2 * Real.sqrt (1 - mNu ν μ)) * hs2
      _ ≤ (2 / Real.pi * Real.sqrt y / (1 + y) ^ 2) * Real.sqrt (1 - mNu ν (μ * y)) :=
          mul_le_mul_of_nonneg_left hR hc
      _ = varpi y * Real.sqrt (1 - mNu ν (μ * y)) := rfl

/-- Lower bound on the `(1,∞)` piece of `sqrtEff`. -/
private lemma sa_lower_Ioi {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μ : ℝ} (hμ : 0 < μ) :
    (2 / Real.pi * (Real.pi / 4 + 1 / 2)) * Real.sqrt (1 - mNu ν μ) ≤
      ∫ y in Ioi (1 : ℝ), varpi y * Real.sqrt (1 - mNu ν (μ * y)) := by
  have hI : ∫ y in Ioi (1 : ℝ), varpi y * Real.sqrt (1 - mNu ν μ)
      = (2 / Real.pi * (Real.pi / 4 + 1 / 2)) * Real.sqrt (1 - mNu ν μ) := by
    rw [integral_mul_const, sa_varpi_integral_Ioi]
  rw [← hI]
  refine integral_mono_of_nonneg ?_ (sa_integrand_integrableOn hν hμ measurableSet_Ioi
    (fun y hy => by have := Set.mem_Ioi.1 hy; linarith) sa_varpi_integrableOn_Ioi) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy1 : 1 < y := hy
    exact mul_nonneg (sa_varpi_nonneg (by linarith)) (Real.sqrt_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy1 : 1 ≤ y := (Set.mem_Ioi.1 hy).le
    have hm := sa_mNu_anti hν hμ hy1
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by linarith : 1 - mNu ν μ ≤ 1 - mNu ν (μ * y)))
      (sa_varpi_nonneg (by linarith))

/-- Helper: the lower bound `C_* √(1 - m_ν(μ)) ≤ χ_ν(μ)` for `μ > 0`, extracted from the proof
of `thm:app-os-sqrt`(i) (the first displayed chain of that proof, before `lem:app-os-repr` is
applied). Used again by `prop:app-os-tail`(iv) and `cor:app-os-powerlaw`(iii).

Snapshot `cr-2026-10-23`. Source: `sections/12-oversampled/section.tex`, proof of
`thm:app-os-sqrt`, l.886–894 (display ending `= C_*\sqrt{1-m_\nu(\mu)}`). -/
theorem chi_ge_Cstar_sqrt
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) {μ : ℝ} (hμ : 0 < μ) :
    cStar * Real.sqrt (1 - mNu ν μ) ≤ sqrtEff ν μ := by
  have hA := sa_lower_Ioc hν hμ
  have hB := sa_lower_Ioi hν hμ
  rw [sa_split hν hμ]
  have halg : cStar * Real.sqrt (1 - mNu ν μ) =
      Real.sqrt (1 - mNu ν μ) * (2 / Real.pi * (Real.log 2 - 1 / 2)) +
        (2 / Real.pi * (Real.pi / 4 + 1 / 2)) * Real.sqrt (1 - mNu ν μ) := by
    unfold cStar
    field_simp
    ring
  rw [halg]
  linarith

/-- Declaration of record for `thm:app-os-sqrt`(i).

Label `thm:app-os-sqrt`, part (i). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{theorem}[Square-root law]\label{thm:app-os-sqrt}
Let $C_*\defeq\frac12+\frac{2\log2}{\pi}\approx0.9413$.
\begin{enumerate}[label=(\roman*)]
\item For every probability measure $\nu$ and every $\mu>0$,
\[
\max\Big\{C_*\sqrt{1-m_\nu(\mu)},\ 1-m_\nu(\mu)\Big\}\sqrt{\frac\mu2}\ \le\ \mathfrak d^{\rm os}_\nu(\mu)\ \le\ \sqrt{\frac\mu2}.
\]
\end{enumerate}
\end{theorem}
-/
theorem thm_app_os_sqrt_i
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) {μ : ℝ} (hμ : 0 < μ) :
    max (cStar * Real.sqrt (1 - mNu ν μ)) (1 - mNu ν μ) * Real.sqrt (μ / 2) ≤ dOsSq ν μ ∧
      dOsSq ν μ ≤ Real.sqrt (μ / 2) := by
  have hrep := lem_app_os_repr_ii ν hν hμ
  have hpos : 0 ≤ Real.sqrt (μ / 2) := Real.sqrt_nonneg _
  have hC := chi_ge_Cstar_sqrt ν hν hμ
  have hD := lem_app_os_defect ν hν hμ
  have hAvg := lem_app_os_average_iv ν hν hμ
  have hE := lem_app_os_repr_iii ν hν hμ
  have h2 : 1 - mNu ν μ ≤ sqrtEff ν μ := by linarith [hD.2]
  rw [hrep]
  constructor
  · calc max (cStar * Real.sqrt (1 - mNu ν μ)) (1 - mNu ν μ) * Real.sqrt (μ / 2)
        ≤ sqrtEff ν μ * Real.sqrt (μ / 2) := mul_le_mul_of_nonneg_right (max_le hC h2) hpos
      _ = Real.sqrt (μ / 2) * sqrtEff ν μ := mul_comm _ _
  · exact mul_le_of_le_one_right hpos hE.2

/-- Private helper: `1 - m_ν(μ) = ∫ (1 - x/(μ+x)) dν` for `μ > 0`. -/
private lemma sb_one_sub_mNu {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {μ : ℝ} (hμ : 0 < μ) :
    1 - mNu ν μ = ∫ x, (1 - x / (μ + x)) ∂ν := by
  unfold mNu
  rw [integral_sub (integrable_const (1 : ℝ)) (sa_ratio_integrable hν hμ.le)]
  simp

/-- Private helper: `1 - m_ν(μ) ≥ ν([0,Kμ]) / (1+K)` for `μ > 0`, `K > 0`. -/
private lemma sb_lower_Icc {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {μ K : ℝ} (hμ : 0 < μ) (hK : 0 < K) :
    (ν (Icc 0 (K * μ))).toReal / (1 + K) ≤ 1 - mNu ν μ := by
  rw [sb_one_sub_mNu hν hμ]
  have hint : Integrable (fun x : ℝ => 1 - x / (μ + x)) ν :=
    (integrable_const (1 : ℝ)).sub (sa_ratio_integrable hν hμ.le)
  have hind : Integrable ((Icc (0 : ℝ) (K * μ)).indicator (fun _ : ℝ => 1 / (1 + K))) ν :=
    (integrable_const _).indicator measurableSet_Icc
  have hL : ∫ x, (Icc (0 : ℝ) (K * μ)).indicator (fun _ : ℝ => 1 / (1 + K)) x ∂ν
      = (ν (Icc 0 (K * μ))).toReal / (1 + K) := by
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, smul_eq_mul]
    ring
  rw [← hL]
  refine integral_mono_ae hind hint ?_
  filter_upwards [sa_ae_nonneg hν, sa_ratio_bounds hν hμ.le] with x hx hxb
  by_cases hxI : x ∈ Icc (0 : ℝ) (K * μ)
  · rw [indicator_of_mem hxI]
    have h1 : 0 < μ + x := by linarith [hxI.1]
    have hxK : x ≤ K * μ := hxI.2
    have e : 1 - x / (μ + x) = μ / (μ + x) := by
      rw [eq_div_iff h1.ne', sub_mul, div_mul_cancel₀ _ h1.ne']
      ring
    rw [e, div_le_div_iff₀ (by linarith) h1]
    nlinarith
  · rw [indicator_of_notMem hxI]
    linarith [hxb.2]

/-- Private helper: `x ↦ x/(√μ+√x)^2` is integrable under a probability measure carried on `[0,∞)`. -/
private lemma sb_avg_integrable {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {μ : ℝ} (hμ : 0 < μ) :
    Integrable (fun x : ℝ => x / (Real.sqrt μ + Real.sqrt x) ^ 2) ν := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ => x / (Real.sqrt μ + Real.sqrt x) ^ 2).aestronglyMeasurable
  · filter_upwards [sa_ae_nonneg hν] with x hx
    rw [Real.norm_of_nonneg (div_nonneg hx (sq_nonneg _))]
    exact (lem_app_os_average_ii hμ).2 x hx |>.2.1

/-- Private helper: lower bound `δ/(1+√δ)^2 · ν([δμ,∞)) ≤ m̄_ν(μ)` (with `m̄_ν` written as the
`ν`-integral of `x/(√μ+√x)^2`, via `lem_app_os_average_iii`). -/
private lemma sb_mBar_lower {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    δ / (1 + Real.sqrt δ) ^ 2 * (ν (Ici (δ * μ))).toReal ≤ mBarNu ν μ := by
  rw [lem_app_os_average_iii ν hν hμ]
  have hint := sb_avg_integrable hν hμ
  have hind : Integrable ((Ici (δ * μ)).indicator (fun _ : ℝ => δ / (1 + Real.sqrt δ) ^ 2)) ν :=
    (integrable_const _).indicator measurableSet_Ici
  have hL : ∫ x, (Ici (δ * μ)).indicator (fun _ : ℝ => δ / (1 + Real.sqrt δ) ^ 2) x ∂ν
      = δ / (1 + Real.sqrt δ) ^ 2 * (ν (Ici (δ * μ))).toReal := by
    rw [integral_indicator_const _ measurableSet_Ici, measureReal_def, smul_eq_mul]
    ring
  rw [← hL]
  refine integral_mono_ae hind hint ?_
  filter_upwards [sa_ae_nonneg hν] with x hx
  by_cases hxI : x ∈ Ici (δ * μ)
  · rw [indicator_of_mem hxI]
    have hxI' : δ * μ ≤ x := hxI
    have hδμ : 0 ≤ δ * μ := (mul_pos hδ hμ).le
    have hμs : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
    have hμμ : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt hμ.le
    have hden1 : 0 < Real.sqrt μ + Real.sqrt δ * Real.sqrt μ :=
      add_pos_of_pos_of_nonneg hμs (mul_nonneg (Real.sqrt_nonneg _) hμs.le)
    have hden2 : 0 < 1 + Real.sqrt δ := by positivity
    have h0 : δ * μ / (Real.sqrt μ + Real.sqrt (δ * μ)) ^ 2
        = δ / (1 + Real.sqrt δ) ^ 2 := by
      rw [Real.sqrt_mul hδ.le μ, div_eq_div_iff (pow_pos hden1 2).ne' (pow_pos hden2 2).ne']
      linear_combination (-(δ * (1 + Real.sqrt δ) ^ 2)) * hμμ
    have hmono := (lem_app_os_average_ii hμ).1
    have := hmono (Set.mem_Ici.2 hδμ) (Set.mem_Ici.2 hx) hxI'
    simp only at this
    rw [← h0]
    exact this
  · rw [indicator_of_notMem hxI]
    exact div_nonneg hx (sq_nonneg _)

/-- Private helper: upper bound `m̄_ν(μ) ≤ δ + ν([δμ,∞))` (via `lem_app_os_average_iii`). -/
private lemma sb_mBar_upper {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    mBarNu ν μ ≤ δ + (ν (Ici (δ * μ))).toReal := by
  rw [lem_app_os_average_iii ν hν hμ]
  have hint := sb_avg_integrable hν hμ
  have hind : Integrable ((Ici (δ * μ)).indicator (fun _ : ℝ => (1 : ℝ))) ν :=
    (integrable_const _).indicator measurableSet_Ici
  have hR : ∫ x, ((Ici (δ * μ)).indicator (fun _ : ℝ => (1 : ℝ)) x + δ) ∂ν
      = (ν (Ici (δ * μ))).toReal + δ := by
    rw [integral_add hind (integrable_const δ), integral_indicator_const _ measurableSet_Ici,
      measureReal_def, integral_const, probReal_univ]
    simp
  have hle : ∫ x, x / (Real.sqrt μ + Real.sqrt x) ^ 2 ∂ν
      ≤ ∫ x, ((Ici (δ * μ)).indicator (fun _ : ℝ => (1 : ℝ)) x + δ) ∂ν := by
    refine integral_mono_ae hint (hind.add (integrable_const δ)) ?_
    filter_upwards [sa_ae_nonneg hν] with x hx
    by_cases hxI : x ∈ Ici (δ * μ)
    · rw [indicator_of_mem hxI]
      have := (lem_app_os_average_ii hμ).2 x hx |>.2.1
      linarith
    · rw [indicator_of_notMem hxI]
      have hlt : x < δ * μ := by simpa using hxI
      have h1 := (lem_app_os_average_ii hμ).2 x hx |>.1
      have h2 : x / μ ≤ δ := by
        rw [div_le_iff₀ hμ]
        linarith
      linarith
  rw [hR] at hle
  linarith

/-- Declaration of record for `thm:app-os-sqrt`(ii).

Label `thm:app-os-sqrt`, part (ii). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{theorem}[Square-root law]\label{thm:app-os-sqrt}
Let $C_*\defeq\frac12+\frac{2\log2}{\pi}\approx0.9413$.
\begin{enumerate}[label=(\roman*)]
\item For every probability measure $\nu$ and every $\mu>0$,
\[
\max\Big\{C_*\sqrt{1-m_\nu(\mu)},\ 1-m_\nu(\mu)\Big\}\sqrt{\frac\mu2}\ \le\ \mathfrak d^{\rm os}_\nu(\mu)\ \le\ \sqrt{\frac\mu2}.
\]
\item For every probability measure $\nu$, every $\mu>0$ and every $K>0$,
\[
1-m_\nu(\mu)\ge\frac{\nu([0,K\mu])}{1+K};\qquad\text{in particular}\qquad 1-m_\nu(\mu)\ge\tfrac12\,\nu([0,\mu]).
\]
\end{enumerate}
\end{theorem}
-/
theorem thm_app_os_sqrt_ii
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) {μ K : ℝ}
    (hμ : 0 < μ) (hK : 0 < K) :
    (ν (Icc 0 (K * μ))).toReal / (1 + K) ≤ 1 - mNu ν μ ∧
      (ν (Icc 0 μ)).toReal / 2 ≤ 1 - mNu ν μ := by
  have h := sb_lower_Icc hν hμ hK
  refine ⟨h, ?_⟩
  have h1 := sb_lower_Icc (K := 1) hν hμ one_pos
  rw [one_mul] at h1
  have e2 : (1 : ℝ) + 1 = 2 := by norm_num
  rw [e2] at h1
  exact h1

/-- Declaration of record for `prop:app-os-head`(i).

Label `prop:app-os-head`, part (i). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{proposition}[Head modes]\label{prop:app-os-head}
\begin{enumerate}[label=(\roman*)]
\item For every probability measure $\nu$, every $\mu>0$ and every $\delta>0$,
\[
\frac{\delta}{2(1+\sqrt\delta)^2}\,\nu\big([\delta\mu,\infty)\big)\le1-\chi_\nu(\mu)\le\delta+\nu\big([\delta\mu,\infty)\big).
\]
\item For every sequence of probability measures $\nu_N$ and numbers
$\mu_N>0$, one has $\mathfrak d^{\rm os}_{\nu_N}(\mu_N)/\sqrt{\mu_N/2}\to1$ if and
only if $\nu_N([\delta\mu_N,\infty))\to0$ for every $\delta>0$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_os_head_i
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) {μ δ : ℝ}
    (hμ : 0 < μ) (hδ : 0 < δ) :
    δ / (2 * (1 + Real.sqrt δ) ^ 2) * (ν (Ici (δ * μ))).toReal ≤ 1 - sqrtEff ν μ ∧
      1 - sqrtEff ν μ ≤ δ + (ν (Ici (δ * μ))).toReal := by
  have hD := lem_app_os_defect ν hν hμ
  have hL := sb_mBar_lower hν hμ hδ
  have hU := sb_mBar_upper hν hμ hδ
  constructor
  · have e : δ / (2 * (1 + Real.sqrt δ) ^ 2) * (ν (Ici (δ * μ))).toReal
        = 1 / 2 * (δ / (1 + Real.sqrt δ) ^ 2 * (ν (Ici (δ * μ))).toReal) := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [e]
    linarith [hD.1, hL]
  · linarith [hD.2, hU]

/-- Declaration of record for `prop:app-os-head`(ii).

Label `prop:app-os-head`, part (ii). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{proposition}[Head modes]\label{prop:app-os-head}
\begin{enumerate}[label=(\roman*)]
\item For every probability measure $\nu$, every $\mu>0$ and every $\delta>0$,
\[
\frac{\delta}{2(1+\sqrt\delta)^2}\,\nu\big([\delta\mu,\infty)\big)\le1-\chi_\nu(\mu)\le\delta+\nu\big([\delta\mu,\infty)\big).
\]
\item For every sequence of probability measures $\nu_N$ and numbers
$\mu_N>0$, one has $\mathfrak d^{\rm os}_{\nu_N}(\mu_N)/\sqrt{\mu_N/2}\to1$ if and
only if $\nu_N([\delta\mu_N,\infty))\to0$ for every $\delta>0$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_os_head_ii
    (ν : ℕ → Measure ℝ) (hprob : ∀ N, IsProbabilityMeasure (ν N))
    (hν : ∀ N, ν N (Iio 0) = 0) (μ : ℕ → ℝ) (hμ : ∀ N, 0 < μ N) :
    Tendsto (fun N => dOsSq (ν N) (μ N) / Real.sqrt (μ N / 2)) atTop (𝓝 1) ↔
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun N => (ν N (Ici (δ * μ N))).toReal) atTop (𝓝 0) := by
  have hratio : ∀ N, dOsSq (ν N) (μ N) / Real.sqrt (μ N / 2) = sqrtEff (ν N) (μ N) := by
    intro N
    have hrep := lem_app_os_repr_ii (ν N) (hν N) (hμ N)
    have hpos : 0 < Real.sqrt (μ N / 2) := Real.sqrt_pos.2 (half_pos (hμ N))
    rw [hrep]
    field_simp
  have hfun : (fun N => dOsSq (ν N) (μ N) / Real.sqrt (μ N / 2))
      = fun N => sqrtEff (ν N) (μ N) := funext hratio
  rw [hfun]
  have key : ∀ N δ, 0 < δ →
      0 ≤ 1 - sqrtEff (ν N) (μ N) ∧
        1 - sqrtEff (ν N) (μ N) ≤ δ + (ν N (Ici (δ * μ N))).toReal ∧
        δ / (2 * (1 + Real.sqrt δ) ^ 2) * (ν N (Ici (δ * μ N))).toReal ≤
          1 - sqrtEff (ν N) (μ N) := by
    intro N δ hδ
    have hb := prop_app_os_head_i (ν N) (hν N) (hμ N) hδ
    have hc : 0 ≤ δ / (2 * (1 + Real.sqrt δ) ^ 2) := by positivity
    have hnn : 0 ≤ δ / (2 * (1 + Real.sqrt δ) ^ 2) * (ν N (Ici (δ * μ N))).toReal :=
      mul_nonneg hc ENNReal.toReal_nonneg
    exact ⟨by linarith [hb.1], hb.2, hb.1⟩
  constructor
  · intro h δ hδ
    have hc : 0 < δ / (2 * (1 + Real.sqrt δ) ^ 2) := div_pos hδ (by positivity)
    have hs : Tendsto (fun N => 1 - sqrtEff (ν N) (μ N)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub h
      simpa using this
    have hup : Tendsto (fun N => (1 - sqrtEff (ν N) (μ N)) / (δ / (2 * (1 + Real.sqrt δ) ^ 2)))
        atTop (𝓝 0) := by
      have := hs.div_const (δ / (2 * (1 + Real.sqrt δ) ^ 2))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun N => ENNReal.toReal_nonneg) (fun N => ?_)
    have hk := (key N δ hδ).2.2
    change (ν N (Ici (δ * μ N))).toReal ≤
      (1 - sqrtEff (ν N) (μ N)) / (δ / (2 * (1 + Real.sqrt δ) ^ 2))
    rw [le_div_iff₀ hc]
    linarith [hk]
  · intro h
    rw [Metric.tendsto_nhds]
    intro ε hε
    have ht := Metric.tendsto_nhds.1 (h (ε / 2) (by linarith)) (ε / 2) (by linarith)
    filter_upwards [ht] with N hN
    rw [Real.dist_eq, sub_zero] at hN
    have hlt : (ν N (Ici (ε / 2 * μ N))).toReal < ε / 2 :=
      lt_of_le_of_lt (le_abs_self _) hN
    obtain ⟨h0, h1, -⟩ := key N (ε / 2) (by linarith)
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

end

end Muon.Oversampled

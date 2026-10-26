import Mathlib
import Muon.Oversampled.Profile
import Muon.Oversampled.Representation
import Muon.Oversampled.SqrtLaw

/-!
# Oversampled tail modes (Appendix G2, work package L-G2.4)

Source of record: snapshot `cr-2026-10-23`, `sections/12-oversampled/section.tex`.
Scope: `lem:app-os-tailint` (parts (i)–(iii)), `lem:app-os-log`, `prop:app-os-tail` (parts (i)–(vi)),
and the derived positivity `ℐ_ν > 0` used in part (ii).

Reuses `mNu`, `dOsSq`, `sqrtEff`, `varpi` (`Muon.Oversampled.Profile`), `Upsilon`
(`Muon.Oversampled.Representation`) and `cStar` (`Muon.Oversampled.SqrtLaw`); no project
definition is copied.

Measure representation (fixed by L-G2.1): `ν : Measure ℝ`, `[IsProbabilityMeasure ν]`,
`ν (Set.Iio 0) = 0`. Where the source assumes `ν({0}) = 0` (parts (ii), (iii)), the Lean
statement assumes `ν {0} = 0` explicitly.

Tail modes are not defined in the source; the source's content is the integrals
`ℐ_ν(ℓ)` (valued in `ℝ≥0∞`, value `∞` allowed) and `ℰ(μ,Γ)`. Both are defined here.
Limits are at fixed `ν` (`𝓝[>] 0` in `μ`) or along sequences indexed by `ℕ`.
-/

open MeasureTheory Set Filter Topology

namespace Muon.Oversampled

noncomputable section

/-- Definition of `ℐ_ν(ℓ) := ∫_{(ℓ,∞)} ν(dx)/x ∈ [0,∞]`, valued in `ℝ≥0∞`, with `ℐ_ν := ℐ_ν(0)`
(the display in the section preamble before `lem:app-os-tailint`; `ℐ_ν` is `tailInt ν 0`).
Snapshot `cr-2026-10-23`. Statement verbatim:

For a probability measure $\nu$ and $\ell\ge0$ put
\[
\mathcal I_\nu(\ell)\defeq\int_{(\ell,\infty)}\frac{\nu(\dif x)}{x}\in[0,\infty],\qquad
\mathcal I_\nu\defeq\mathcal I_\nu(0).
\]
-/
def tailInt (ν : Measure ℝ) (ℓ : ℝ) : ENNReal :=
  ∫⁻ x in Ioi ℓ, ENNReal.ofReal x⁻¹ ∂ν

/-- `ℰ(μ,Γ) := (√2/π) μ ∫_0^∞ min{√c, c√Γ}/(c+μ)² dc` (defined in the statement of
`lem:app-os-tailint`). Snapshot `cr-2026-10-23`. Statement verbatim (from that lemma):

\begin{lemma}[The tail integral]\label{lem:app-os-tailint}
For $\mu>0$ and $\Gamma\ge0$ put
\[
\mathcal E(\mu,\Gamma)\defeq\frac{\sqrt2}{\pi}\,\mu\int_0^\infty\frac{\min\{\sqrt c,\ c\sqrt\Gamma\}}{(c+\mu)^2}\,\dif c .
\]
Then $\mathcal E$ is nondecreasing in $\Gamma$, $\mathcal E(\mu,0)=0$, and for $\Gamma>0$
\[
\mathcal E(\mu,\Gamma)\le\frac{\sqrt2}{\pi}\sqrt\Gamma\,\mu\Big[\log\Big(1+\frac1{\mu\Gamma}\Big)+2\Big].
\]
\end{lemma}
-/
def tailErr (μ Γ : ℝ) : ℝ :=
  (Real.sqrt 2 / Real.pi) * μ * ∫ c in Ioi (0 : ℝ), min (Real.sqrt c) (c * Real.sqrt Γ) / (c + μ) ^ 2

/-- Derived positivity `ℐ_ν > 0` under `ν(ℝ_{<0}) = 0`, `ν({0}) = 0`, `ν` probability
(used in `prop:app-os-tail`(ii)). Not a source label; it is the implicit fact the source uses
in the proof of part (ii) and part (iii). -/
theorem tailInt_zero_pos (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    (hν0 : ν {0} = 0) : 0 < tailInt ν 0 := by
  have hIic : ν (Iic 0) = 0 := by
    have : Iic (0 : ℝ) = Iio 0 ∪ {0} := by ext x; simp [le_iff_lt_or_eq]
    rw [this]; exact measure_union_null hν hν0
  have hIoi : ν (Ioi 0) = 1 := by
    rw [← Set.compl_Iic, prob_compl_eq_one_iff measurableSet_Iic]; exact hIic
  unfold tailInt
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal x⁻¹) := by fun_prop
  rw [lintegral_pos_iff_support hmeas, Measure.restrict_apply' measurableSet_Ioi]
  calc (0 : ENNReal) < ν (Ioi 0) := by rw [hIoi]; exact zero_lt_one
    _ ≤ ν (Function.support (fun x : ℝ => ENNReal.ofReal x⁻¹) ∩ Ioi 0) := by
      apply measure_mono
      intro x hx
      exact ⟨Function.mem_support.2 (ENNReal.ofReal_pos.2 (inv_pos.2 hx)).ne', hx⟩

/-- pointwise dominator of the tail integrand at `c > 0` by `c^(-3/2)` when `c ≥ 1`-type bound -/
private lemma tail_sqrt_div_le_rpow {μ c : ℝ} (hμ : 0 < μ) (hc : 0 < c) :
    Real.sqrt c / (c + μ) ^ 2 ≤ c ^ (-3 / 2 : ℝ) := by
  have e : c ^ (-3 / 2 : ℝ) = Real.sqrt c / c ^ 2 := by
    rw [show (-3 / 2 : ℝ) = 1 / 2 + (-2) by norm_num, Real.rpow_add hc, Real.rpow_neg hc.le,
      Real.sqrt_eq_rpow]
    norm_num
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_left (Real.sqrt_nonneg c) (by positivity)
  nlinarith

private lemma tail_integrable_dom (μ : ℝ) (hμ : 0 < μ) :
    IntegrableOn (fun c : ℝ => Real.sqrt c / (c + μ) ^ 2) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun c : ℝ => Real.sqrt c / μ ^ 2) (Ioc 0 1) := by
      have hi : IntegrableOn (fun c : ℝ => c ^ (1 / 2 : ℝ)) (Ioc 0 1) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
          (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
      have : IntegrableOn (fun c : ℝ => c ^ (1 / 2 : ℝ) / μ ^ 2) (Ioc 0 1) := hi.div_const _
      refine this.congr_fun ?_ measurableSet_Ioc
      intro c _
      simp only [Real.sqrt_eq_rpow]
    refine Integrable.mono' h1 ?_ ?_
    · exact (by fun_prop : Measurable (fun c : ℝ => Real.sqrt c / (c + μ) ^ 2)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
      intro c hc
      have hc0 : 0 < c := hc.1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply div_le_div_of_nonneg_left (Real.sqrt_nonneg c) (by positivity)
      nlinarith
  · refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) zero_lt_one) ?_ ?_
    · exact (by fun_prop : Measurable (fun c : ℝ => Real.sqrt c / (c + μ) ^ 2)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
      intro c hc
      have hc0 : 0 < c := lt_trans zero_lt_one hc
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact tail_sqrt_div_le_rpow hμ hc0


private lemma tail_integrable (μ : ℝ) (hμ : 0 < μ) (γ : ℝ) :
    IntegrableOn (fun c : ℝ => min (Real.sqrt c) (c * Real.sqrt γ) / (c + μ) ^ 2) (Ioi 0) := by
  refine Integrable.mono' (tail_integrable_dom μ hμ) ?_ ?_
  · exact (by fun_prop : Measurable (fun c : ℝ => min (Real.sqrt c) (c * Real.sqrt γ) / (c + μ) ^ 2)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro c hc
    have hc0 : 0 < c := hc
    have hnn : 0 ≤ min (Real.sqrt c) (c * Real.sqrt γ) :=
      le_min (Real.sqrt_nonneg c) (mul_nonneg hc0.le (Real.sqrt_nonneg γ))
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnn (sq_nonneg _))]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg _)

private lemma tail_ftc (μ a : ℝ) (hμ : 0 < μ) (ha : 0 ≤ a) :
    ∫ c in Ioc 0 a, c / (c + μ) ^ 2 ≤ Real.log (a + μ) - Real.log μ := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) a,
      HasDerivAt (fun x => Real.log (x + μ) + μ / (x + μ)) (x / (x + μ) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le ha] at hx
    have hx0 : 0 ≤ x := hx.1
    have hxμ : x + μ ≠ 0 := (by linarith : (0:ℝ) < x + μ).ne'
    have d1 : HasDerivAt (fun x => Real.log (x + μ)) (1 / (x + μ)) x :=
      ((hasDerivAt_id' x).add_const μ).log hxμ
    have d2 : HasDerivAt (fun x => μ / (x + μ)) ((0 * (x + μ) - μ * 1) / (x + μ) ^ 2) x :=
      (hasDerivAt_const x μ).div ((hasDerivAt_id' x).add_const μ) hxμ
    convert d1.add d2 using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun c : ℝ => c / (c + μ) ^ 2) volume 0 a := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_id
    · exact (by fun_prop : Continuous fun c : ℝ => (c + μ) ^ 2).continuousOn
    · intro c hc
      rw [Set.uIcc_of_le ha] at hc
      have : 0 < c + μ := by linarith [hc.1]
      exact pow_ne_zero 2 this.ne'
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_of_le ha] at h
  rw [h]
  simp only [zero_add, div_self hμ.ne']
  have hle : μ / (a + μ) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  linarith

private lemma tail_outer (a : ℝ) (ha : 0 < a) :
    ∫ c in Ioi a, c ^ (-3 / 2 : ℝ) = 2 / Real.sqrt a := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) ha]
  have : a ^ (-3 / 2 + 1 : ℝ) = (Real.sqrt a)⁻¹ := by
    rw [show (-3 / 2 + 1 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow]
  rw [this]
  field_simp
  norm_num


/-- `lem:app-os-tailint`(i). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{lemma}[The tail integral]\label{lem:app-os-tailint}
For $\mu>0$ and $\Gamma\ge0$ put
\[
\mathcal E(\mu,\Gamma)\defeq\frac{\sqrt2}{\pi}\,\mu\int_0^\infty\frac{\min\{\sqrt c,\ c\sqrt\Gamma\}}{(c+\mu)^2}\,\dif c .
\]
Then $\mathcal E$ is nondecreasing in $\Gamma$, $\mathcal E(\mu,0)=0$, and for $\Gamma>0$
\[
\mathcal E(\mu,\Gamma)\le\frac{\sqrt2}{\pi}\sqrt\Gamma\,\mu\Big[\log\Big(1+\frac1{\mu\Gamma}\Big)+2\Big].
\]
\end{lemma}
-/
theorem lem_app_os_tailint_i (μ : ℝ) (hμ : 0 < μ) {Γ₁ Γ₂ : ℝ} (h₁ : 0 ≤ Γ₁) (h : Γ₁ ≤ Γ₂) :
    tailErr μ Γ₁ ≤ tailErr μ Γ₂ := by
  unfold tailErr
  have hpos : 0 ≤ (Real.sqrt 2 / Real.pi) * μ := by
    have : 0 ≤ Real.sqrt 2 / Real.pi := div_nonneg (Real.sqrt_nonneg 2) Real.pi_pos.le
    exact mul_nonneg this hμ.le
  apply mul_le_mul_of_nonneg_left _ hpos
  apply setIntegral_mono_on (tail_integrable μ hμ Γ₁) (tail_integrable μ hμ Γ₂) measurableSet_Ioi
  intro c hc
  have hc0 : 0 < c := hc
  have hsq : Real.sqrt Γ₁ ≤ Real.sqrt Γ₂ := Real.sqrt_le_sqrt h
  have hmin : min (Real.sqrt c) (c * Real.sqrt Γ₁) ≤ min (Real.sqrt c) (c * Real.sqrt Γ₂) :=
    min_le_min le_rfl (mul_le_mul_of_nonneg_left hsq hc0.le)
  exact div_le_div_of_nonneg_right hmin (sq_nonneg _)

/-- `lem:app-os-tailint`(ii). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{lemma}[The tail integral]\label{lem:app-os-tailint}
For $\mu>0$ and $\Gamma\ge0$ put
\[
\mathcal E(\mu,\Gamma)\defeq\frac{\sqrt2}{\pi}\,\mu\int_0^\infty\frac{\min\{\sqrt c,\ c\sqrt\Gamma\}}{(c+\mu)^2}\,\dif c .
\]
Then $\mathcal E$ is nondecreasing in $\Gamma$, $\mathcal E(\mu,0)=0$, and for $\Gamma>0$
\[
\mathcal E(\mu,\Gamma)\le\frac{\sqrt2}{\pi}\sqrt\Gamma\,\mu\Big[\log\Big(1+\frac1{\mu\Gamma}\Big)+2\Big].
\]
\end{lemma}
-/
theorem lem_app_os_tailint_ii (μ : ℝ) (hμ : 0 < μ) : tailErr μ 0 = 0 := by
  unfold tailErr
  have h : ∫ c in Ioi (0 : ℝ), min (Real.sqrt c) (c * Real.sqrt 0) / (c + μ) ^ 2 = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ))]
    · simp
    · intro c hc
      have hc0 : 0 < c := hc
      simp only [Real.sqrt_zero, mul_zero]
      rw [min_eq_right (Real.sqrt_nonneg c), zero_div]
  rw [h, mul_zero]

/-- `lem:app-os-tailint`(iii). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{lemma}[The tail integral]\label{lem:app-os-tailint}
For $\mu>0$ and $\Gamma\ge0$ put
\[
\mathcal E(\mu,\Gamma)\defeq\frac{\sqrt2}{\pi}\,\mu\int_0^\infty\frac{\min\{\sqrt c,\ c\sqrt\Gamma\}}{(c+\mu)^2}\,\dif c .
\]
Then $\mathcal E$ is nondecreasing in $\Gamma$, $\mathcal E(\mu,0)=0$, and for $\Gamma>0$
\[
\mathcal E(\mu,\Gamma)\le\frac{\sqrt2}{\pi}\sqrt\Gamma\,\mu\Big[\log\Big(1+\frac1{\mu\Gamma}\Big)+2\Big].
\]
\end{lemma}
-/
theorem lem_app_os_tailint_iii (μ : ℝ) (hμ : 0 < μ) {Γ : ℝ} (hΓ : 0 < Γ) :
    tailErr μ Γ ≤ Real.sqrt 2 / Real.pi * Real.sqrt Γ * μ * (Real.log (1 + 1 / (μ * Γ)) + 2) := by
  unfold tailErr
  have ha : (0 : ℝ) < 1 / Γ := by positivity
  have hI := tail_integrable μ hμ Γ
  have hsplit : ∫ c in Ioi (0 : ℝ), min (Real.sqrt c) (c * Real.sqrt Γ) / (c + μ) ^ 2
      = (∫ c in Ioc (0 : ℝ) (1 / Γ), min (Real.sqrt c) (c * Real.sqrt Γ) / (c + μ) ^ 2)
        + ∫ c in Ioi (1 / Γ), min (Real.sqrt c) (c * Real.sqrt Γ) / (c + μ) ^ 2 := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi ha.le]
    exact setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hI.mono_set Set.Ioc_subset_Ioi_self) (hI.mono_set (Set.Ioi_subset_Ioi ha.le))
  have hpart1 : (∫ c in Ioc (0 : ℝ) (1 / Γ), min (Real.sqrt c) (c * Real.sqrt Γ) / (c + μ) ^ 2)
      = Real.sqrt Γ * ∫ c in Ioc (0 : ℝ) (1 / Γ), c / (c + μ) ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro c hc
    dsimp only
    have hc0 : 0 < c := hc.1
    have hcΓ : c * Γ ≤ 1 := (le_div_iff₀ hΓ).1 hc.2
    have hts : Real.sqrt c * Real.sqrt Γ ≤ 1 := by
      have h1 : (Real.sqrt c * Real.sqrt Γ) ^ 2 ≤ 1 := by
        rw [mul_pow, Real.sq_sqrt hc0.le, Real.sq_sqrt hΓ.le]; exact hcΓ
      nlinarith [Real.sqrt_nonneg c, Real.sqrt_nonneg Γ, mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg Γ)]
    have hle : c * Real.sqrt Γ ≤ Real.sqrt c := by
      nlinarith [Real.sqrt_nonneg c, Real.sqrt_nonneg Γ, Real.sq_sqrt hc0.le]
    rw [min_eq_right hle]
    ring
  have hpart2 : (∫ c in Ioi (1 / Γ), min (Real.sqrt c) (c * Real.sqrt Γ) / (c + μ) ^ 2) ≤ 2 * Real.sqrt Γ := by
    have hval : ∫ c in Ioi (1 / Γ), c ^ (-3 / 2 : ℝ) = 2 * Real.sqrt Γ := by
      rw [tail_outer (1 / Γ) ha]
      rw [one_div, Real.sqrt_inv]
      field_simp
    rw [← hval]
    apply setIntegral_mono_on (hI.mono_set (Set.Ioi_subset_Ioi ha.le))
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) ha) measurableSet_Ioi
    intro c hc
    have hc0 : 0 < c := lt_trans ha hc
    calc min (Real.sqrt c) (c * Real.sqrt Γ) / (c + μ) ^ 2
        ≤ Real.sqrt c / (c + μ) ^ 2 := div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
      _ ≤ c ^ (-3 / 2 : ℝ) := tail_sqrt_div_le_rpow hμ hc0
  have hL := tail_ftc μ (1 / Γ) hμ ha.le
  have hlog : Real.log (1 / Γ + μ) - Real.log μ = Real.log (1 + 1 / (μ * Γ)) := by
    rw [← Real.log_div (by positivity) hμ.ne']
    congr 1
    field_simp
    ring
  have key : (∫ c in Ioi (0 : ℝ), min (Real.sqrt c) (c * Real.sqrt Γ) / (c + μ) ^ 2)
      ≤ Real.sqrt Γ * (Real.log (1 + 1 / (μ * Γ)) + 2) := by
    rw [hsplit, hpart1]
    have hs : 0 ≤ Real.sqrt Γ := Real.sqrt_nonneg Γ
    nlinarith [mul_le_mul_of_nonneg_left hL hs]
  have hpos : 0 ≤ Real.sqrt 2 / Real.pi * μ := mul_nonneg (div_nonneg (Real.sqrt_nonneg 2) Real.pi_pos.le) hμ.le
  calc (Real.sqrt 2 / Real.pi) * μ * ∫ c in Ioi (0 : ℝ), min (Real.sqrt c) (c * Real.sqrt Γ) / (c + μ) ^ 2
      ≤ (Real.sqrt 2 / Real.pi) * μ * (Real.sqrt Γ * (Real.log (1 + 1 / (μ * Γ)) + 2)) :=
        mul_le_mul_of_nonneg_left key hpos
    _ = Real.sqrt 2 / Real.pi * Real.sqrt Γ * μ * (Real.log (1 + 1 / (μ * Γ)) + 2) := by ring

/-- `lem:app-os-log`. Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{lemma}[A logarithmic inequality]\label{lem:app-os-log}
For every $k>0$,
\[
\log(1+k)-\frac{k}{1+k}\ge\frac12\log k .
\]
\end{lemma}
-/
theorem lem_app_os_log {k : ℝ} (hk : 0 < k) :
    1 / 2 * Real.log k ≤ Real.log (1 + k) - k / (1 + k) := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = k / (1 + k) := ⟨_, rfl⟩
  rw [← ht]
  have h1k : 0 < 1 + k := by linarith
  have htk : t * (1 + k) = k := by
    rw [ht, div_mul_cancel₀]
    exact h1k.ne'
  have h3' : (3 - 2 * t) * (1 + k) = 3 + k := by linear_combination (-2 : ℝ) * htk
  have hlow : 3 - 2 * t ≤ Real.exp (2 * (1 - t)) := by
    have := Real.add_one_le_exp (2 * (1 - t))
    linarith
  have hE2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have hsplit : Real.exp (2 * t) * Real.exp (2 * (1 - t)) = Real.exp 2 := by
    rw [← Real.exp_add]
    ring_nf
  have ha : Real.exp (2 * t) * (3 - 2 * t) ≤ Real.exp 2 := by
    calc Real.exp (2 * t) * (3 - 2 * t)
        ≤ Real.exp (2 * t) * Real.exp (2 * (1 - t)) :=
          mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
      _ = Real.exp 2 := hsplit
  have hA : Real.exp (2 * t) * (3 + k) ≤ Real.exp 1 ^ 2 * (1 + k) := by
    have h := mul_le_mul_of_nonneg_right ha h1k.le
    rw [hE2] at h
    have heq : Real.exp (2 * t) * (3 + k) = Real.exp (2 * t) * (3 - 2 * t) * (1 + k) := by
      rw [← h3']; ring
    linarith
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hE2b : Real.exp 1 ^ 2 ≤ 7.38906 := by nlinarith
  have hpoly : Real.exp 1 ^ 2 * k ≤ (1 + k) * (3 + k) := by
    nlinarith [mul_le_mul_of_nonneg_right hE2b hk.le, sq_nonneg (k - 1.69453)]
  have hkey3 : k * Real.exp (2 * t) * (3 + k) ≤ (1 + k) ^ 2 * (3 + k) := by
    nlinarith [mul_le_mul_of_nonneg_left hA hk.le, mul_le_mul_of_nonneg_right hpoly h1k.le]
  have hkey : k * Real.exp (2 * t) ≤ (1 + k) ^ 2 :=
    le_of_mul_le_mul_right hkey3 (by linarith)
  have hlog := Real.log_le_log (mul_pos hk (Real.exp_pos _)) hkey
  rw [Real.log_mul hk.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow] at hlog
  norm_num at hlog
  linarith

/-! ### Helpers for `prop:app-os-tail`(i) (private, fully proved) -/

private lemma tail_ae_nonneg {ν : Measure ℝ} (hν : ν (Iio 0) = 0) : ∀ᵐ x ∂ν, 0 ≤ x := by
  rw [ae_iff]
  have : {x : ℝ | ¬ 0 ≤ x} = Iio 0 := by ext x; simp
  rw [this]; exact hν

/-- `∫_0^∞ √c/(c+μ)² dc = π/(2√μ)`, by the antiderivative `arctan(√c/√μ)/√μ - √c/(c+μ)`. -/
private lemma tail_sqrt_integral (μ : ℝ) (hμ : 0 < μ) :
    ∫ c in Ioi (0 : ℝ), Real.sqrt c / (c + μ) ^ 2 = Real.pi / (2 * Real.sqrt μ) := by
  have ha : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have ha2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun c : ℝ => Real.arctan (Real.sqrt c / Real.sqrt μ) / Real.sqrt μ
        - Real.sqrt c / (c + μ)) (Real.sqrt x / (x + μ) ^ 2) x := by
    intro x hx
    have hx0 : 0 < x := hx
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hsx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    have hd : HasDerivAt (fun c : ℝ => Real.sqrt c / Real.sqrt μ)
        (1 / (2 * Real.sqrt x) / Real.sqrt μ) x :=
      (Real.hasDerivAt_sqrt hx0.ne').div_const _
    have h1 := (hd.arctan).div_const (Real.sqrt μ)
    have h2 := (Real.hasDerivAt_sqrt hx0.ne').div ((hasDerivAt_id' x).add_const μ)
      (by show x + μ ≠ 0; exact (by linarith : (0:ℝ) < x + μ).ne')
    have h := h1.sub h2
    convert h using 1
    rw [div_pow, hsx2, ha2]
    field_simp
    nlinarith [Real.mul_self_sqrt hx0.le, Real.mul_self_sqrt hμ.le, hsx]
  have hcont : ContinuousWithinAt (fun c : ℝ => Real.arctan (Real.sqrt c / Real.sqrt μ)
      / Real.sqrt μ - Real.sqrt c / (c + μ)) (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.sub
    · exact ((Real.continuous_arctan.comp (Real.continuous_sqrt.div_const _)).div_const _).continuousAt
    · exact (Real.continuous_sqrt.continuousAt).div (continuousAt_id.add continuousAt_const)
        (by simp [hμ.ne'])
  have hsq_top : Tendsto (fun c : ℝ => Real.sqrt c) atTop atTop := by
    have h := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    refine h.congr' ?_
    filter_upwards with c using (Real.sqrt_eq_rpow c).symm
  have hsqrt_top : Tendsto (fun c : ℝ => Real.sqrt c / Real.sqrt μ) atTop atTop :=
    hsq_top.atTop_div_const ha
  have harc : Tendsto (fun c : ℝ => Real.arctan (Real.sqrt c / Real.sqrt μ) / Real.sqrt μ)
      atTop (𝓝 (Real.pi / 2 / Real.sqrt μ)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin (Real.tendsto_arctan_atTop.comp hsqrt_top)).div_const _
  have hrat : Tendsto (fun c : ℝ => Real.sqrt c / (c + μ)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_inv_atTop_zero.comp hsq_top) ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with c hc
      exact div_nonneg (Real.sqrt_nonneg c) (by linarith)
    · filter_upwards [eventually_ge_atTop 1] with c hc
      have hc0 : 0 < c := by linarith
      show Real.sqrt c / (c + μ) ≤ (Real.sqrt c)⁻¹
      rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (Real.sqrt_pos.2 hc0)]
      nlinarith [Real.mul_self_sqrt hc0.le]
  have hG := harc.sub hrat
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv (tail_integrable_dom μ hμ)
    (by simpa using hG)
  rw [key]
  simp [div_div]

private lemma tail_inv_facts (ν : Measure ℝ) [IsProbabilityMeasure ν] {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hfin : tailInt ν ℓ < ⊤) :
    IntegrableOn (fun x : ℝ => x⁻¹) (Ioi ℓ) ν ∧
      (tailInt ν ℓ).toReal = ∫ x in Ioi ℓ, x⁻¹ ∂ν := by
  have hmeas : AEMeasurable (fun x : ℝ => ENNReal.ofReal x⁻¹) (ν.restrict (Ioi ℓ)) :=
    (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal x⁻¹).aemeasurable
  have hne : ∫⁻ x in Ioi ℓ, ENNReal.ofReal x⁻¹ ∂ν ≠ ⊤ := by
    unfold tailInt at hfin; exact hfin.ne
  have hI : Integrable (fun x : ℝ => (ENNReal.ofReal x⁻¹).toReal) (ν.restrict (Ioi ℓ)) :=
    integrable_toReal_of_lintegral_ne_top hmeas hne
  have hcongr : (fun x : ℝ => (ENNReal.ofReal x⁻¹).toReal) =ᵐ[ν.restrict (Ioi ℓ)]
      fun x : ℝ => x⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have : 0 < x := lt_of_le_of_lt hℓ hx
    rw [ENNReal.toReal_ofReal (inv_nonneg.2 this.le)]
  refine ⟨hI.congr hcongr, ?_⟩
  unfold tailInt
  have hlt : ∀ᵐ x ∂(ν.restrict (Ioi ℓ)), ENNReal.ofReal x⁻¹ < ⊤ :=
    Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  rw [← integral_toReal hmeas hlt]
  exact integral_congr_ae hcongr

private lemma tail_ratio_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => c / (c + x)) ν := by
  refine Integrable.of_bound
    (by fun_prop : Measurable fun x : ℝ => c / (c + x)).aestronglyMeasurable 1 ?_
  filter_upwards [tail_ae_nonneg hν] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hc.le (by linarith))]
  rw [div_le_one (by linarith)]
  linarith

private lemma tail_one_sub_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {c : ℝ} (hc : 0 < c) : 1 - mNu ν c = ∫ x, c / (c + x) ∂ν := by
  have hm : mNu ν c = ∫ x, (1 - c / (c + x)) ∂ν := by
    unfold mNu
    apply integral_congr_ae
    filter_upwards [tail_ae_nonneg hν] with x hx
    have hcx : c + x ≠ 0 := (by linarith : (0:ℝ) < c + x).ne'
    have h : c / (c + x) + x / (c + x) = 1 := by rw [← add_div, div_self hcx]
    show x / (c + x) = 1 - c / (c + x)
    linarith
  rw [hm, integral_sub (integrable_const (1 : ℝ)) (tail_ratio_integrable ν hν hc)]
  simp

private lemma tail_one_sub_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hfin : tailInt ν ℓ < ⊤) {c : ℝ} (hc : 0 < c) :
    0 ≤ 1 - mNu ν c ∧ 1 - mNu ν c ≤ 1 ∧
      1 - mNu ν c ≤ (ν (Icc 0 ℓ)).toReal + c * (tailInt ν ℓ).toReal := by
  have hae := tail_ae_nonneg hν
  have hint := tail_ratio_integrable ν hν hc
  have hI := tail_inv_facts ν hℓ hfin
  rw [tail_one_sub_eq ν hν hc]
  refine ⟨integral_nonneg_of_ae ?_, ?_, ?_⟩
  · filter_upwards [hae] with x hx
    show (0 : ℝ) ≤ c / (c + x)
    exact div_nonneg hc.le (by linarith)
  · have h := integral_mono_ae hint (integrable_const (1 : ℝ)) (by
      filter_upwards [hae] with x hx
      show c / (c + x) ≤ 1
      rw [div_le_one (by linarith)]
      linarith)
    simpa using h
  · have h1 : Integrable (fun x : ℝ => (Icc 0 ℓ).indicator (fun _ => (1 : ℝ)) x) ν :=
      (integrable_const (1 : ℝ)).indicator measurableSet_Icc
    have h2 : Integrable (fun x : ℝ => (Ioi ℓ).indicator (fun x : ℝ => c * x⁻¹) x) ν :=
      (show IntegrableOn (fun x : ℝ => c * x⁻¹) (Ioi ℓ) ν from hI.1.const_mul c).integrable_indicator measurableSet_Ioi
    have hpt : ∀ᵐ x ∂ν, c / (c + x) ≤
        (Icc 0 ℓ).indicator (fun _ => (1 : ℝ)) x + (Ioi ℓ).indicator (fun x : ℝ => c * x⁻¹) x := by
      filter_upwards [hae] with x hx
      by_cases hxℓ : x ≤ ℓ
      · have hmem : x ∈ Icc 0 ℓ := ⟨hx, hxℓ⟩
        have hnot : x ∉ Ioi ℓ := fun h => absurd (mem_Ioi.1 h) (not_lt.2 hxℓ)
        rw [indicator_of_mem hmem, indicator_of_notMem hnot]
        have : c / (c + x) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        linarith
      · have hnot : x ∉ Icc 0 ℓ := fun h => hxℓ h.2
        have hxpos : 0 < x := lt_of_le_of_lt hℓ (not_le.1 hxℓ)
        have hmem : x ∈ Ioi ℓ := not_le.1 hxℓ
        rw [indicator_of_notMem hnot, indicator_of_mem hmem, zero_add]
        calc c / (c + x) ≤ c / x := div_le_div_of_nonneg_left hc.le hxpos (by linarith)
          _ = c * x⁻¹ := div_eq_mul_inv c x
    have hsplit : ∫ x, ((Icc 0 ℓ).indicator (fun _ => (1 : ℝ)) x
        + (Ioi ℓ).indicator (fun x : ℝ => c * x⁻¹) x) ∂ν
        = (ν (Icc 0 ℓ)).toReal + c * ∫ x in Ioi ℓ, x⁻¹ ∂ν := by
      rw [integral_add h1 h2, integral_indicator_const _ measurableSet_Icc,
        integral_indicator measurableSet_Ioi, integral_const_mul]
      simp [measureReal_def]
    have hmono : ∫ x, c / (c + x) ∂ν ≤ ∫ x, ((Icc 0 ℓ).indicator (fun _ => (1 : ℝ)) x
        + (Ioi ℓ).indicator (fun x : ℝ => c * x⁻¹) x) ∂ν :=
      integral_mono_ae hint (h1.add h2) hpt
    rw [hsplit] at hmono
    rw [hI.2]
    exact hmono

private lemma tail_sqrt_pt {ν : Measure ℝ} [IsProbabilityMeasure ν] {ℓ : ℝ}
    (hν : ν (Iio 0) = 0) (hℓ : 0 ≤ ℓ) (hfin : tailInt ν ℓ < ⊤) {c : ℝ} (hc : 0 < c) :
    Real.sqrt (Upsilon ν c) ≤ Real.sqrt c * Real.sqrt (ν (Icc 0 ℓ)).toReal
      + min (Real.sqrt c) (c * Real.sqrt (tailInt ν ℓ).toReal) := by
  obtain ⟨h0, h1, h2⟩ := tail_one_sub_bounds ν hν hℓ hfin hc
  have hν0 : 0 ≤ (ν (Icc 0 ℓ)).toReal := ENNReal.toReal_nonneg
  have hI : 0 ≤ (tailInt ν ℓ).toReal := ENNReal.toReal_nonneg
  have hU : Upsilon ν c = c * (1 - mNu ν c) := rfl
  have hUc : Upsilon ν c ≤ c := by
    rw [hU]; linarith [mul_le_mul_of_nonneg_left h1 hc.le]
  have hUB : Upsilon ν c ≤ c * (ν (Icc 0 ℓ)).toReal + c ^ 2 * (tailInt ν ℓ).toReal := by
    rw [hU]; nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]
  have hP : 0 ≤ Real.sqrt c * Real.sqrt (ν (Icc 0 ℓ)).toReal :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hB : 0 ≤ c * Real.sqrt (tailInt ν ℓ).toReal := mul_nonneg hc.le (Real.sqrt_nonneg _)
  have hPsq : (Real.sqrt c * Real.sqrt (ν (Icc 0 ℓ)).toReal) ^ 2 = c * (ν (Icc 0 ℓ)).toReal := by
    rw [mul_pow, Real.sq_sqrt hc.le, Real.sq_sqrt hν0]
  have hBsq : (c * Real.sqrt (tailInt ν ℓ).toReal) ^ 2 = c ^ 2 * (tailInt ν ℓ).toReal := by
    rw [mul_pow, Real.sq_sqrt hI]
  have hsqU : Upsilon ν c ≤ (Real.sqrt c * Real.sqrt (ν (Icc 0 ℓ)).toReal
      + c * Real.sqrt (tailInt ν ℓ).toReal) ^ 2 := by
    nlinarith [mul_nonneg hP hB]
  have hA : Real.sqrt (Upsilon ν c) ≤ Real.sqrt c := Real.sqrt_le_sqrt hUc
  have hB' : Real.sqrt (Upsilon ν c) ≤ Real.sqrt c * Real.sqrt (ν (Icc 0 ℓ)).toReal
      + c * Real.sqrt (tailInt ν ℓ).toReal := by
    calc Real.sqrt (Upsilon ν c) ≤ Real.sqrt ((Real.sqrt c * Real.sqrt (ν (Icc 0 ℓ)).toReal
          + c * Real.sqrt (tailInt ν ℓ).toReal) ^ 2) := Real.sqrt_le_sqrt hsqU
      _ = Real.sqrt c * Real.sqrt (ν (Icc 0 ℓ)).toReal + c * Real.sqrt (tailInt ν ℓ).toReal :=
          Real.sqrt_sq (add_nonneg hP hB)
  have hmin : min (Real.sqrt c) (Real.sqrt c * Real.sqrt (ν (Icc 0 ℓ)).toReal
      + c * Real.sqrt (tailInt ν ℓ).toReal) ≤ Real.sqrt c * Real.sqrt (ν (Icc 0 ℓ)).toReal
      + min (Real.sqrt c) (c * Real.sqrt (tailInt ν ℓ).toReal) := by
    rcases le_total (Real.sqrt c) (c * Real.sqrt (tailInt ν ℓ).toReal) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by linarith)
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (by linarith)
  exact (le_min hA hB').trans hmin

/-- `prop:app-os-tail`(i). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{proposition}[Tail modes]\label{prop:app-os-tail}
Let $\nu$ be a probability measure and $\mu>0$.
\begin{enumerate}[label=(\roman*)]
\item (Split bound.) For every $\ell\ge0$ with $\mathcal I_\nu(\ell)<\infty$,
\[
\mathfrak d^{\rm os}_\nu(\mu)\le\sqrt{\nu([0,\ell])}\,\sqrt{\frac\mu2}+\mathcal E\big(\mu,\mathcal I_\nu(\ell)\big).
\]
\item (Gradient-descent-like upper bound.) If $\nu(\{0\})=0$ and $\mathcal I_\nu<\infty$, then
\[
\mathfrak d^{\rm os}_\nu(\mu)\le\frac{\sqrt2}{\pi}\sqrt{\mathcal I_\nu}\;\mu\Big[\log\Big(1+\frac1{\mu\mathcal I_\nu}\Big)+2\Big].
\]
\item (Asymptotics.) If $\nu(\{0\})=0$ and $\mathcal I_\nu<\infty$, then, for fixed $\nu$,
\[
\mathfrak d^{\rm os}_\nu(\mu)\sim\frac{\sqrt2}{\pi}\sqrt{\mathcal I_\nu}\;\mu\log\frac1\mu\qquad(\mu\downarrow0).
\]
\item (Counts.) For every $K>0$,
\[
C_*\sqrt{\frac{\nu([0,K\mu])}{1+K}}\le\chi_\nu(\mu)\le\sqrt{\nu([0,K\mu])}+\frac{2}{\pi\sqrt K}\big[\log(1+K)+2\big].
\]
\item (Universal lower bound.) If $\nu([0,X])=1$ for some $X>0$, then
\[
\mathfrak d^{\rm os}_\nu(\mu)\ge\frac1\pi\,\frac{\mu}{\sqrt X}\Big[\log\Big(1+\frac X\mu\Big)-\frac{X}{X+\mu}\Big]\ge\frac1{2\pi}\,\frac{\mu}{\sqrt X}\,\log\frac X\mu .
\]
\item (Sequences.) For probability measures $\nu_N$ and numbers $\mu_N>0$ put
$\chi_N\defeq\chi_{\nu_N}(\mu_N)$. Then $\liminf_N\chi_N>0$ if and only if
$\liminf_N\nu_N([0,K\mu_N])>0$ for some $K>0$; and $\chi_N\to0$ if and only if
$\nu_N([0,K\mu_N])\to0$ for every $K>0$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_os_tail_i (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μ : ℝ} (hμ : 0 < μ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hfin : tailInt ν ℓ < ⊤) :
    dOsSq ν μ ≤ Real.sqrt (ν (Icc 0 ℓ)).toReal * Real.sqrt (μ / 2)
      + tailErr μ (tailInt ν ℓ).toReal := by
  have hrep := lem_app_os_repr_i ν hν hμ
  have hsq : Real.sqrt (μ / 2) = Real.sqrt μ * Real.sqrt 2 / 2 := by
    rw [show μ / 2 = (Real.sqrt μ * Real.sqrt 2 / 2) ^ 2 by
      rw [div_pow, mul_pow, Real.sq_sqrt hμ.le, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring]
    exact Real.sqrt_sq (by positivity)
  have hgi : IntegrableOn (fun c : ℝ => Real.sqrt (ν (Icc 0 ℓ)).toReal * (Real.sqrt c / (c + μ) ^ 2)
      + min (Real.sqrt c) (c * Real.sqrt (tailInt ν ℓ).toReal) / (c + μ) ^ 2) (Ioi 0) :=
    ((tail_integrable_dom μ hμ).const_mul _).add (tail_integrable μ hμ _)
  have hpt : ∀ c ∈ Ioi (0 : ℝ), Real.sqrt (Upsilon ν c) / (c + μ) ^ 2
      ≤ Real.sqrt (ν (Icc 0 ℓ)).toReal * (Real.sqrt c / (c + μ) ^ 2)
      + min (Real.sqrt c) (c * Real.sqrt (tailInt ν ℓ).toReal) / (c + μ) ^ 2 := by
    intro c hc
    have hc0 : 0 < c := hc
    have hd : 0 < (c + μ) ^ 2 := pow_pos (by linarith) 2
    have h := tail_sqrt_pt hν hℓ hfin hc0
    calc Real.sqrt (Upsilon ν c) / (c + μ) ^ 2
        ≤ (Real.sqrt c * Real.sqrt (ν (Icc 0 ℓ)).toReal
          + min (Real.sqrt c) (c * Real.sqrt (tailInt ν ℓ).toReal)) / (c + μ) ^ 2 :=
          div_le_div_of_nonneg_right h hd.le
      _ = Real.sqrt (ν (Icc 0 ℓ)).toReal * (Real.sqrt c / (c + μ) ^ 2)
          + min (Real.sqrt c) (c * Real.sqrt (tailInt ν ℓ).toReal) / (c + μ) ^ 2 := by ring
  have hf0 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun c : ℝ => Real.sqrt (Upsilon ν c) / (c + μ) ^ 2) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun c _ => by positivity)
  have hle : ∫ c in Ioi (0 : ℝ), Real.sqrt (Upsilon ν c) / (c + μ) ^ 2
      ≤ ∫ c in Ioi (0 : ℝ), (Real.sqrt (ν (Icc 0 ℓ)).toReal * (Real.sqrt c / (c + μ) ^ 2)
      + min (Real.sqrt c) (c * Real.sqrt (tailInt ν ℓ).toReal) / (c + μ) ^ 2) :=
    integral_mono_of_nonneg hf0 hgi ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun c hc => hpt c hc))
  rw [integral_add ((tail_integrable_dom μ hμ).const_mul _) (tail_integrable μ hμ _),
    integral_const_mul, tail_sqrt_integral μ hμ] at hle
  have hpos : 0 ≤ Real.sqrt 2 / Real.pi * μ := by positivity
  have hscal : Real.sqrt 2 / Real.pi * μ * (Real.pi / (2 * Real.sqrt μ)) = Real.sqrt μ * Real.sqrt 2 / 2 := by
    have hs : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
    have hs2 : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt hμ.le
    have h3 : μ / (2 * Real.sqrt μ) = Real.sqrt μ / 2 := by
      rw [div_eq_div_iff (by positivity) (by norm_num)]
      linear_combination (-2 : ℝ) * hs2
    calc Real.sqrt 2 / Real.pi * μ * (Real.pi / (2 * Real.sqrt μ))
        = Real.sqrt 2 * (μ / (2 * Real.sqrt μ)) := by field_simp
      _ = Real.sqrt μ * Real.sqrt 2 / 2 := by rw [h3]; ring
  have hkey : Real.sqrt 2 / Real.pi * μ * (Real.sqrt (ν (Icc 0 ℓ)).toReal * (Real.pi / (2 * Real.sqrt μ))
      + ∫ c in Ioi (0 : ℝ), min (Real.sqrt c) (c * Real.sqrt (tailInt ν ℓ).toReal) / (c + μ) ^ 2)
      = Real.sqrt (ν (Icc 0 ℓ)).toReal * Real.sqrt (μ / 2)
      + Real.sqrt 2 / Real.pi * μ * ∫ c in Ioi (0 : ℝ), min (Real.sqrt c) (c * Real.sqrt (tailInt ν ℓ).toReal) / (c + μ) ^ 2 := by
    rw [hsq]
    linear_combination (Real.sqrt (ν (Icc 0 ℓ)).toReal) * hscal
  have hmul := mul_le_mul_of_nonneg_left hle hpos
  rw [hrep]
  unfold tailErr
  linarith

/-- `prop:app-os-tail`(ii). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{proposition}[Tail modes]\label{prop:app-os-tail}
Let $\nu$ be a probability measure and $\mu>0$.
\begin{enumerate}[label=(\roman*)]
\item (Split bound.) For every $\ell\ge0$ with $\mathcal I_\nu(\ell)<\infty$,
\[
\mathfrak d^{\rm os}_\nu(\mu)\le\sqrt{\nu([0,\ell])}\,\sqrt{\frac\mu2}+\mathcal E\big(\mu,\mathcal I_\nu(\ell)\big).
\]
\item (Gradient-descent-like upper bound.) If $\nu(\{0\})=0$ and $\mathcal I_\nu<\infty$, then
\[
\mathfrak d^{\rm os}_\nu(\mu)\le\frac{\sqrt2}{\pi}\sqrt{\mathcal I_\nu}\;\mu\Big[\log\Big(1+\frac1{\mu\mathcal I_\nu}\Big)+2\Big].
\]
\item (Asymptotics.) If $\nu(\{0\})=0$ and $\mathcal I_\nu<\infty$, then, for fixed $\nu$,
\[
\mathfrak d^{\rm os}_\nu(\mu)\sim\frac{\sqrt2}{\pi}\sqrt{\mathcal I_\nu}\;\mu\log\frac1\mu\qquad(\mu\downarrow0).
\]
\item (Counts.) For every $K>0$,
\[
C_*\sqrt{\frac{\nu([0,K\mu])}{1+K}}\le\chi_\nu(\mu)\le\sqrt{\nu([0,K\mu])}+\frac{2}{\pi\sqrt K}\big[\log(1+K)+2\big].
\]
\item (Universal lower bound.) If $\nu([0,X])=1$ for some $X>0$, then
\[
\mathfrak d^{\rm os}_\nu(\mu)\ge\frac1\pi\,\frac{\mu}{\sqrt X}\Big[\log\Big(1+\frac X\mu\Big)-\frac{X}{X+\mu}\Big]\ge\frac1{2\pi}\,\frac{\mu}{\sqrt X}\,\log\frac X\mu .
\]
\item (Sequences.) For probability measures $\nu_N$ and numbers $\mu_N>0$ put
$\chi_N\defeq\chi_{\nu_N}(\mu_N)$. Then $\liminf_N\chi_N>0$ if and only if
$\liminf_N\nu_N([0,K\mu_N])>0$ for some $K>0$; and $\chi_N\to0$ if and only if
$\nu_N([0,K\mu_N])\to0$ for every $K>0$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_os_tail_ii (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    (hν0 : ν {0} = 0) {μ : ℝ} (hμ : 0 < μ) (hfin : tailInt ν 0 < ⊤) :
    dOsSq ν μ ≤ Real.sqrt 2 / Real.pi * Real.sqrt (tailInt ν 0).toReal * μ
      * (Real.log (1 + 1 / (μ * (tailInt ν 0).toReal)) + 2) := by
  have hI0 : 0 < tailInt ν 0 := tailInt_zero_pos ν hν hν0
  have hΓ : 0 < (tailInt ν 0).toReal := ENNReal.toReal_pos hI0.ne' hfin.ne
  have h1 := prop_app_os_tail_i ν hν hμ (le_refl 0) hfin
  have hsub : ν (Icc (0 : ℝ) 0) = 0 := by rw [Icc_self]; exact hν0
  rw [hsub, ENNReal.toReal_zero, Real.sqrt_zero, zero_mul, zero_add] at h1
  have h2 := lem_app_os_tailint_iii μ hμ hΓ
  linarith

/-- Private: lower count bound through `1 - m_ν(μ)` (for `prop:app-os-tail`(iv)). -/
private lemma tail_count_lower (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μ K : ℝ} (hμ : 0 < μ) (hK : 0 < K) :
    (ν (Icc 0 (K * μ))).toReal / (1 + K) ≤ 1 - mNu ν μ := by
  rw [tail_one_sub_eq ν hν hμ]
  have hint := tail_ratio_integrable ν hν hμ
  have hm : Integrable ((Icc 0 (K * μ)).indicator (fun _ : ℝ => 1 / (1 + K))) ν :=
    (integrable_const (1 / (1 + K))).indicator measurableSet_Icc
  have hle : ∫ x, (Icc 0 (K * μ)).indicator (fun _ : ℝ => 1 / (1 + K)) x ∂ν
      ≤ ∫ x, μ / (μ + x) ∂ν := by
    apply integral_mono_ae hm hint
    filter_upwards [tail_ae_nonneg hν] with x hx
    by_cases hxI : x ∈ Icc 0 (K * μ)
    · rw [indicator_of_mem hxI]
      have hxK : x ≤ K * μ := hxI.2
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    · rw [indicator_of_notMem hxI]
      exact div_nonneg hμ.le (by linarith)
  rw [integral_indicator_const _ measurableSet_Icc] at hle
  simp only [smul_eq_mul, measureReal_def] at hle
  rw [div_eq_mul_one_div]
  exact hle

/-- Private: algebraic identity `√(μ/2)·(2/(π√K))·L = (√2/π)·√(1/(Kμ))·μ·L`. -/
private lemma tail_sqrt_identity {μ K : ℝ} (hμ : 0 < μ) (hK : 0 < K) (L : ℝ) :
    Real.sqrt (μ / 2) * (2 / (Real.pi * Real.sqrt K) * L)
      = Real.sqrt 2 / Real.pi * Real.sqrt (1 / (K * μ)) * μ * L := by
  have e1 : Real.sqrt (μ / 2) = Real.sqrt μ / Real.sqrt 2 := Real.sqrt_div hμ.le 2
  have e2 : Real.sqrt (1 / (K * μ)) = 1 / (Real.sqrt K * Real.sqrt μ) := by
    rw [Real.sqrt_div zero_le_one, Real.sqrt_one, Real.sqrt_mul hK.le]
  have hsμ : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt hμ.le
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hsμpos : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [e1, e2]
  field_simp
  rw [Real.sq_sqrt hμ.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Private: the error term `2/(π√K)·(log(1+K)+2)` tends to `0` as `K → ∞`. -/
private lemma tail_C_tendsto :
    Tendsto (fun K : ℝ => 2 / (Real.pi * Real.sqrt K) * (Real.log (1 + K) + 2)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun K : ℝ => Real.log K / Real.sqrt K) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    refine h.congr' ?_
    filter_upwards with K
    rw [Real.sqrt_eq_rpow]
  have hsqrt : Tendsto (fun K : ℝ => Real.sqrt K) atTop atTop := by
    have h := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    refine h.congr' ?_
    filter_upwards with c using (Real.sqrt_eq_rpow c).symm
  have hc : Tendsto (fun K : ℝ => (Real.log 2 + 2) / Real.sqrt K) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsqrt
  have hmain : Tendsto (fun K : ℝ => (Real.log K / Real.sqrt K + (Real.log 2 + 2) / Real.sqrt K)
      * (2 / Real.pi)) atTop (𝓝 0) := by
    have := (hlog.add hc).mul_const (2 / Real.pi)
    rw [add_zero, zero_mul] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmain ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with K hK
    have h1 : 0 ≤ Real.log (1 + K) := Real.log_nonneg (by linarith)
    exact mul_nonneg (div_nonneg zero_le_two (mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg K)))
      (by linarith)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with K hK
    have hK0 : 0 < K := by linarith
    have hs : 0 < Real.sqrt K := Real.sqrt_pos.2 hK0
    have hlogle : Real.log (1 + K) ≤ Real.log K + Real.log 2 := by
      have h := Real.log_le_log (by linarith : (0 : ℝ) < 1 + K) (by linarith : 1 + K ≤ K * 2)
      rw [Real.log_mul hK0.ne' (by norm_num)] at h
      exact h
    have key : 2 / (Real.pi * Real.sqrt K) * (Real.log (1 + K) + 2)
        = (Real.log (1 + K) + 2) / Real.sqrt K * (2 / Real.pi) := by ring
    rw [key]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hs.le
    linarith

/-- Private: upper bound `sqrtEff ν μ ≤ √(ν[0,Kμ]) + 2/(π√K)·(log(1+K)+2)`
(for `prop:app-os-tail`(iv)). -/
private lemma tail_count_upper (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μ K : ℝ} (hμ : 0 < μ) (hK : 0 < K) :
    sqrtEff ν μ ≤ Real.sqrt (ν (Icc 0 (K * μ))).toReal
      + 2 / (Real.pi * Real.sqrt K) * (Real.log (1 + K) + 2) := by
  have hKμ : 0 < K * μ := mul_pos hK hμ
  have hbound : tailInt ν (K * μ) ≤ ENNReal.ofReal (1 / (K * μ)) := by
    unfold tailInt
    calc ∫⁻ x in Ioi (K * μ), ENNReal.ofReal x⁻¹ ∂ν
        ≤ ∫⁻ x in Ioi (K * μ), ENNReal.ofReal (1 / (K * μ)) ∂ν :=
          setLIntegral_mono' measurableSet_Ioi (fun x hx =>
            ENNReal.ofReal_le_ofReal (by
              rw [one_div]; exact inv_anti₀ hKμ (mem_Ioi.1 hx).le))
      _ = ENNReal.ofReal (1 / (K * μ)) * ν (Ioi (K * μ)) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (1 / (K * μ)) * 1 := mul_le_mul_of_nonneg_left prob_le_one zero_le
      _ = ENNReal.ofReal (1 / (K * μ)) := mul_one _
  have hfin : tailInt ν (K * μ) < ⊤ := lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hΓle : (tailInt ν (K * μ)).toReal ≤ 1 / (K * μ) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hbound
  have hΓ0 : (0 : ℝ) ≤ (tailInt ν (K * μ)).toReal := ENNReal.toReal_nonneg
  have hG : (0 : ℝ) < 1 / (K * μ) := by positivity
  have h1 := prop_app_os_tail_i ν hν hμ hKμ.le hfin
  have h2 := lem_app_os_tailint_i μ hμ hΓ0 hΓle
  have h3 := lem_app_os_tailint_iii μ hμ hG
  have hKk : 1 / (μ * (1 / (K * μ))) = K := by field_simp
  rw [hKk] at h3
  have h4 := lem_app_os_repr_ii ν hν hμ
  have hid := tail_sqrt_identity (K := K) hμ hK (Real.log (1 + K) + 2)
  have hpos : 0 < Real.sqrt (μ / 2) := Real.sqrt_pos.2 (by positivity)
  have hfinal : Real.sqrt (μ / 2) * sqrtEff ν μ
      ≤ Real.sqrt (μ / 2) * (Real.sqrt (ν (Icc 0 (K * μ))).toReal
        + 2 / (Real.pi * Real.sqrt K) * (Real.log (1 + K) + 2)) := by
    rw [mul_add, mul_comm (Real.sqrt (μ / 2)) (Real.sqrt (ν (Icc 0 (K * μ))).toReal)]
    nlinarith
  exact le_of_mul_le_mul_left hfinal hpos

private lemma tail_iii_ae_pos (ν : Measure ℝ) (hν : ν (Iio 0) = 0) (hν0 : ν {0} = 0) :
    ∀ᵐ x ∂ν, 0 < x := by
  have h : ν (Iic 0) = 0 := by
    rw [← Iio_union_right, measure_union_null_iff]
    exact ⟨hν, hν0⟩
  rw [ae_iff]
  have : {x : ℝ | ¬ 0 < x} = Iic 0 := by ext x; simp
  rw [this]; exact h

private lemma tail_iii_g_int (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {c : ℝ} (hc : 0 < c) : Integrable (fun x : ℝ => (c + x)⁻¹) ν := by
  refine Integrable.of_bound
    (by fun_prop : Measurable fun x : ℝ => (c + x)⁻¹).aestronglyMeasurable c⁻¹ ?_
  filter_upwards [tail_ae_nonneg hν] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (by linarith))]
  exact inv_anti₀ hc (by linarith)

private lemma tail_iii_ups_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {c : ℝ} (hc : 0 < c) : Upsilon ν c = c ^ 2 * ∫ x, (c + x)⁻¹ ∂ν := by
  have h := tail_one_sub_eq ν hν hc
  unfold Upsilon
  rw [h]
  have : ∀ x : ℝ, c / (c + x) = c * (c + x)⁻¹ := fun x => div_eq_mul_inv _ _
  simp_rw [this]
  rw [integral_const_mul]
  ring

private lemma tail_iii_sqrt_lower (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {c c1 : ℝ} (hc : 0 < c) (hcc : c ≤ c1) :
    c * Real.sqrt (∫ x, (c1 + x)⁻¹ ∂ν) ≤ Real.sqrt (Upsilon ν c) := by
  have hc1 : 0 < c1 := lt_of_lt_of_le hc hcc
  have hle : ∫ x, (c1 + x)⁻¹ ∂ν ≤ ∫ x, (c + x)⁻¹ ∂ν := by
    apply integral_mono_ae (tail_iii_g_int ν hν hc1) (tail_iii_g_int ν hν hc)
    filter_upwards [tail_ae_nonneg hν] with x hx
    exact inv_anti₀ (by linarith) (by linarith)
  rw [tail_iii_ups_eq ν hν hc, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) hc.le

private lemma tail_iii_g_tendsto (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    (hν0 : ν {0} = 0) (hfin : tailInt ν 0 < ⊤) :
    Tendsto (fun c : ℝ => ∫ x, (c + x)⁻¹ ∂ν) (𝓝[>] 0) (𝓝 (tailInt ν 0).toReal) := by
  have hpos := tail_iii_ae_pos ν hν hν0
  have hres : ν.restrict (Ioi 0) = ν := Measure.restrict_eq_self_of_ae_mem hpos
  obtain ⟨hint, heq⟩ := tail_inv_facts ν (le_refl 0) hfin
  unfold IntegrableOn at hint
  rw [hres] at hint heq
  rw [heq]
  refine tendsto_integral_filter_of_dominated_convergence (fun x : ℝ => x⁻¹) ?_ ?_ hint ?_
  · exact Eventually.of_forall fun c =>
      (by fun_prop : Measurable fun x : ℝ => (c + x)⁻¹).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with c hc
    filter_upwards [hpos] with x hx
    have hc' : 0 < c := hc
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (by linarith))]
    exact inv_anti₀ hx (by linarith)
  · filter_upwards [hpos] with x hx
    have h1 : Tendsto (fun c : ℝ => c + x) (𝓝 0) (𝓝 (0 + x)) :=
      (continuous_id.add continuous_const).tendsto 0
    have h2 : Tendsto (fun c : ℝ => (c + x)⁻¹) (𝓝 0) (𝓝 ((0 + x)⁻¹)) :=
      h1.inv₀ (by simpa using hx.ne')
    simp only [zero_add] at h2
    exact h2.mono_left nhdsWithin_le_nhds

private lemma tail_iii_mNu_meas (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Measurable (fun c : ℝ => mNu ν c) := by
  have hf : Measurable (fun p : ℝ × ℝ => p.2 / (p.1 + p.2)) := by fun_prop
  have hs := hf.stronglyMeasurable.integral_prod_right' (ν := ν)
  exact hs.measurable

private lemma tail_iii_ftc_eq (μ a : ℝ) (hμ : 0 < μ) (ha : 0 ≤ a) :
    ∫ c in Ioc 0 a, c / (c + μ) ^ 2 = Real.log (a + μ) - Real.log μ + μ / (a + μ) - 1 := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) a,
      HasDerivAt (fun x => Real.log (x + μ) + μ / (x + μ)) (x / (x + μ) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le ha] at hx
    have hx0 : 0 ≤ x := hx.1
    have hxμ : x + μ ≠ 0 := (by linarith : (0:ℝ) < x + μ).ne'
    have d1 : HasDerivAt (fun x => Real.log (x + μ)) (1 / (x + μ)) x :=
      ((hasDerivAt_id' x).add_const μ).log hxμ
    have d2 : HasDerivAt (fun x => μ / (x + μ)) ((0 * (x + μ) - μ * 1) / (x + μ) ^ 2) x :=
      (hasDerivAt_const x μ).div ((hasDerivAt_id' x).add_const μ) hxμ
    convert d1.add d2 using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun c : ℝ => c / (c + μ) ^ 2) volume 0 a := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_id
    · exact (by fun_prop : Continuous fun c : ℝ => (c + μ) ^ 2).continuousOn
    · intro c hc
      rw [Set.uIcc_of_le ha] at hc
      have : 0 < c + μ := by linarith [hc.1]
      exact pow_ne_zero 2 this.ne'
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_of_le ha] at h
  rw [h]
  simp only [zero_add, div_self hμ.ne']
  ring

private lemma tail_iii_lower (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    (hfin : tailInt ν 0 < ⊤) {μ c1 : ℝ} (hμ : 0 < μ) (hc1 : 0 < c1) :
    Real.sqrt 2 / Real.pi * μ * (Real.sqrt (∫ x, (c1 + x)⁻¹ ∂ν)
      * (Real.log c1 - Real.log μ - 1)) ≤ dOsSq ν μ := by
  rw [lem_app_os_repr_i ν hν hμ]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  set g := ∫ x, (c1 + x)⁻¹ ∂ν with hg
  have hmeas : Measurable (fun c : ℝ => Real.sqrt (Upsilon ν c) / (c + μ) ^ 2) := by
    have hU : Measurable (Upsilon ν) := by
      show Measurable fun c : ℝ => c * (1 - mNu ν c)
      exact measurable_id.mul (measurable_const.sub (tail_iii_mNu_meas ν))
    exact hU.sqrt.div (by fun_prop)
  have hf_int : IntegrableOn (fun c : ℝ => Real.sqrt (Upsilon ν c) / (c + μ) ^ 2) (Ioi 0) := by
    refine Integrable.mono' (tail_integrable_dom μ hμ) hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with c hc
    have hc0 : 0 < c := hc
    obtain ⟨h0, h1, -⟩ := tail_one_sub_bounds ν hν (le_refl 0) hfin hc0
    have hU : Upsilon ν c ≤ c := by
      show c * (1 - mNu ν c) ≤ c
      nlinarith
    have hU0 : 0 ≤ Upsilon ν c := by
      show 0 ≤ c * (1 - mNu ν c)
      exact mul_nonneg hc0.le h0
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hU) (sq_nonneg _)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun c : ℝ => Real.sqrt (Upsilon ν c) / (c + μ) ^ 2 :=
    Eventually.of_forall fun c => div_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  have h1 := setIntegral_mono_set hf_int hnn
    (HasSubset.Subset.eventuallyLE (show Ioc (0 : ℝ) c1 ⊆ Ioi 0 from Ioc_subset_Ioi_self))
  have hgi : IntegrableOn (fun c : ℝ => Real.sqrt g * (c / (c + μ) ^ 2)) (Ioc 0 c1) := by
    refine Integrable.const_mul ?_ _
    have hcont : ContinuousOn (fun c : ℝ => c / (c + μ) ^ 2) (Icc 0 c1) := by
      apply ContinuousOn.div continuousOn_id
      · exact (by fun_prop : Continuous fun c : ℝ => (c + μ) ^ 2).continuousOn
      · intro c hc
        have : 0 < c + μ := by linarith [hc.1]
        exact pow_ne_zero 2 this.ne'
    exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h2 : ∫ c in Ioc 0 c1, Real.sqrt g * (c / (c + μ) ^ 2)
      ≤ ∫ c in Ioc 0 c1, Real.sqrt (Upsilon ν c) / (c + μ) ^ 2 := by
    refine setIntegral_mono_on hgi (hf_int.mono_set (show Ioc (0 : ℝ) c1 ⊆ Ioi 0 from Ioc_subset_Ioi_self)) measurableSet_Ioc ?_
    intro c hc
    have hc0 : 0 < c := hc.1
    have h := tail_iii_sqrt_lower ν hν hc0 hc.2
    have hd : 0 < (c + μ) ^ 2 := pow_pos (by linarith) 2
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hd.le
    rw [mul_comm]
    exact h
  rw [integral_const_mul, tail_iii_ftc_eq μ c1 hμ hc1.le] at h2
  have hlog : Real.log c1 ≤ Real.log (c1 + μ) := Real.log_le_log hc1 (by linarith)
  have hfr : 0 ≤ μ / (c1 + μ) := div_nonneg hμ.le (by linarith)
  have hsg : 0 ≤ Real.sqrt g := Real.sqrt_nonneg _
  have : Real.sqrt g * (Real.log c1 - Real.log μ - 1)
      ≤ Real.sqrt g * (Real.log (c1 + μ) - Real.log μ + μ / (c1 + μ) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hsg
  linarith

/-- `prop:app-os-tail`(iii). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{proposition}[Tail modes]\label{prop:app-os-tail}
Let $\nu$ be a probability measure and $\mu>0$.
\begin{enumerate}[label=(\roman*)]
\item (Split bound.) For every $\ell\ge0$ with $\mathcal I_\nu(\ell)<\infty$,
\[
\mathfrak d^{\rm os}_\nu(\mu)\le\sqrt{\nu([0,\ell])}\,\sqrt{\frac\mu2}+\mathcal E\big(\mu,\mathcal I_\nu(\ell)\big).
\]
\item (Gradient-descent-like upper bound.) If $\nu(\{0\})=0$ and $\mathcal I_\nu<\infty$, then
\[
\mathfrak d^{\rm os}_\nu(\mu)\le\frac{\sqrt2}{\pi}\sqrt{\mathcal I_\nu}\;\mu\Big[\log\Big(1+\frac1{\mu\mathcal I_\nu}\Big)+2\Big].
\]
\item (Asymptotics.) If $\nu(\{0\})=0$ and $\mathcal I_\nu<\infty$, then, for fixed $\nu$,
\[
\mathfrak d^{\rm os}_\nu(\mu)\sim\frac{\sqrt2}{\pi}\sqrt{\mathcal I_\nu}\;\mu\log\frac1\mu\qquad(\mu\downarrow0).
\]
\item (Counts.) For every $K>0$,
\[
C_*\sqrt{\frac{\nu([0,K\mu])}{1+K}}\le\chi_\nu(\mu)\le\sqrt{\nu([0,K\mu])}+\frac{2}{\pi\sqrt K}\big[\log(1+K)+2\big].
\]
\item (Universal lower bound.) If $\nu([0,X])=1$ for some $X>0$, then
\[
\mathfrak d^{\rm os}_\nu(\mu)\ge\frac1\pi\,\frac{\mu}{\sqrt X}\Big[\log\Big(1+\frac X\mu\Big)-\frac{X}{X+\mu}\Big]\ge\frac1{2\pi}\,\frac{\mu}{\sqrt X}\,\log\frac X\mu .
\]
\item (Sequences.) For probability measures $\nu_N$ and numbers $\mu_N>0$ put
$\chi_N\defeq\chi_{\nu_N}(\mu_N)$. Then $\liminf_N\chi_N>0$ if and only if
$\liminf_N\nu_N([0,K\mu_N])>0$ for some $K>0$; and $\chi_N\to0$ if and only if
$\nu_N([0,K\mu_N])\to0$ for every $K>0$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_os_tail_iii (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    (hν0 : ν {0} = 0) (hfin : tailInt ν 0 < ⊤) :
    Asymptotics.IsEquivalent (𝓝[>] (0 : ℝ)) (fun μ => dOsSq ν μ)
      (fun μ => Real.sqrt 2 / Real.pi * Real.sqrt (tailInt ν 0).toReal * μ * Real.log (1 / μ)) := by
  have hI0 : 0 < tailInt ν 0 := tailInt_zero_pos ν hν hν0
  have hI : 0 < (tailInt ν 0).toReal := ENNReal.toReal_pos hI0.ne' hfin.ne
  have hgt := tail_iii_g_tendsto ν hν hν0 hfin
  have hsI : 0 < Real.sqrt (tailInt ν 0).toReal := Real.sqrt_pos.2 hI
  have hA : 0 < Real.sqrt 2 / Real.pi * Real.sqrt (tailInt ν 0).toReal := by positivity
  set I := (tailInt ν 0).toReal with hIdef
  set A := Real.sqrt 2 / Real.pi * Real.sqrt I with hAdef
  have hL : Tendsto (fun μ : ℝ => Real.log (1 / μ)) (𝓝[>] 0) atTop := by
    simp only [one_div, Real.log_inv]
    exact tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hT : ∀ K : ℝ, Tendsto (fun μ : ℝ => 1 + K / Real.log (1 / μ)) (𝓝[>] 0) (𝓝 1) := by
    intro K
    have := (tendsto_const_nhds (x := (1 : ℝ))).add ((tendsto_const_nhds (x := K)).div_atTop hL)
    simpa using this
  have hLpos : ∀ᶠ μ : ℝ in 𝓝[>] 0, 0 < μ ∧ 0 < Real.log (1 / μ) := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with μ hμ
    refine ⟨hμ.1, ?_⟩
    rw [one_div, Real.log_inv]
    have := Real.log_neg hμ.1 hμ.2
    linarith
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  rw [tendsto_order]
  constructor
  · intro a' ha'
    set b := max a' (1 / 2) with hb
    have hb1 : b < 1 := max_lt ha' (by norm_num)
    have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hba : a' ≤ b := le_max_left _ _
    set b' := (b + 1) / 2 with hb'
    have hbb' : b < b' := by rw [hb']; linarith
    have hb'1 : b' < 1 := by rw [hb']; linarith
    have hb'0 : 0 < b' := by linarith
    have hev : ∀ᶠ c : ℝ in 𝓝[>] 0, 0 < c ∧ b' ^ 2 * I < ∫ x, (c + x)⁻¹ ∂ν := by
      have h0 : ∀ᶠ c : ℝ in 𝓝[>] 0, 0 < c := self_mem_nhdsWithin
      refine h0.and (hgt.eventually (lt_mem_nhds ?_))
      nlinarith [mul_pos hI (by nlinarith : 0 < 1 - b' ^ 2)]
    obtain ⟨c1, hc1, hg1⟩ := hev.exists
    have hsg : b' * Real.sqrt I ≤ Real.sqrt (∫ x, (c1 + x)⁻¹ ∂ν) := by
      have : Real.sqrt (b' ^ 2 * I) = b' * Real.sqrt I := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb'0.le]
      rw [← this]
      exact Real.sqrt_le_sqrt hg1.le
    have hT1 : ∀ᶠ μ : ℝ in 𝓝[>] 0, b / b' < 1 + (Real.log c1 - 1) / Real.log (1 / μ) :=
      (hT (Real.log c1 - 1)).eventually (lt_mem_nhds (by rw [div_lt_one hb'0]; exact hbb'))
    filter_upwards [hLpos, hT1] with μ ⟨hμ, hLμ⟩ hTμ
    have hlow := tail_iii_lower ν hν hfin hμ hc1
    set L := Real.log (1 / μ) with hLdef
    have hLeq : Real.log c1 - Real.log μ - 1 = L * (1 + (Real.log c1 - 1) / L) := by
      have hLv : L = -Real.log μ := by rw [hLdef, one_div, Real.log_inv]
      have : L * (1 + (Real.log c1 - 1) / L) = L + (Real.log c1 - 1) := by
        field_simp
      rw [this, hLv]; ring
    rw [hLeq] at hlow
    have hTpos : 0 < 1 + (Real.log c1 - 1) / L := lt_trans (div_pos hb0 hb'0) hTμ
    have hP : 0 < A * μ * L := by positivity
    show a' < dOsSq ν μ / (A * μ * L)
    rw [lt_div_iff₀ hP]
    have h1 : b' * Real.sqrt I * (L * (1 + (Real.log c1 - 1) / L))
        ≤ Real.sqrt (∫ x, (c1 + x)⁻¹ ∂ν) * (L * (1 + (Real.log c1 - 1) / L)) :=
      mul_le_mul_of_nonneg_right hsg (by positivity)
    have h2 : Real.sqrt 2 / Real.pi * μ * (b' * Real.sqrt I * (L * (1 + (Real.log c1 - 1) / L)))
        ≤ Real.sqrt 2 / Real.pi * μ * (Real.sqrt (∫ x, (c1 + x)⁻¹ ∂ν)
          * (L * (1 + (Real.log c1 - 1) / L))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : b < b' * (1 + (Real.log c1 - 1) / L) := by
      rwa [div_lt_iff₀ hb'0, mul_comm] at hTμ
    have h4 : a' * (A * μ * L) ≤ b * (A * μ * L) := mul_le_mul_of_nonneg_right hba hP.le
    have h5 : b * (A * μ * L) < b' * (1 + (Real.log c1 - 1) / L) * (A * μ * L) :=
      mul_lt_mul_of_pos_right h3 hP
    have h6 : Real.sqrt 2 / Real.pi * μ * (b' * Real.sqrt I * (L * (1 + (Real.log c1 - 1) / L)))
        = b' * (1 + (Real.log c1 - 1) / L) * (A * μ * L) := by
      rw [hAdef]; ring
    linarith
  · intro b hb
    set K := Real.log 2 - Real.log I + 2 with hK
    have hev1 : ∀ᶠ μ : ℝ in 𝓝[>] 0, μ ∈ Ioo 0 (min 1 (1 / I)) :=
      Ioo_mem_nhdsGT (lt_min zero_lt_one (by positivity))
    have hT1 : ∀ᶠ μ : ℝ in 𝓝[>] 0, 1 + K / Real.log (1 / μ) < b :=
      (hT K).eventually (gt_mem_nhds hb)
    filter_upwards [hLpos, hev1, hT1] with μ ⟨hμ, hLμ⟩ hμ' hTμ
    have hμ1 : μ * I ≤ 1 := by
      have := hμ'.2
      have h2 : μ < 1 / I := lt_of_lt_of_le this (min_le_right _ _)
      have h3 : μ * I < 1 := by rwa [lt_div_iff₀ hI] at h2
      exact h3.le
    have hii := prop_app_os_tail_ii ν hν hν0 hμ hfin
    have hlog : Real.log (1 + 1 / (μ * I)) ≤ Real.log (2 / (μ * I)) := by
      apply Real.log_le_log (by positivity)
      have : 1 ≤ 1 / (μ * I) := by rw [le_div_iff₀ (by positivity)]; linarith
      have h2 : 2 / (μ * I) = 1 / (μ * I) + 1 / (μ * I) := by ring
      linarith
    set L := Real.log (1 / μ) with hLdef
    have hlog2 : Real.log (2 / (μ * I)) = L + Real.log 2 - Real.log I := by
      rw [Real.log_div (by norm_num) (by positivity), Real.log_mul hμ.ne' hI.ne', hLdef,
        one_div, Real.log_inv]
      ring
    have hP : 0 < A * μ * L := by positivity
    show dOsSq ν μ / (A * μ * L) < b
    rw [div_lt_iff₀ hP]
    have h1 : dOsSq ν μ ≤ A * μ * (L + K) := by
      calc dOsSq ν μ ≤ A * μ * (Real.log (1 + 1 / (μ * I)) + 2) := hii
        _ ≤ A * μ * (L + K) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [hK]; linarith
    have h2 : A * μ * (L + K) = (1 + K / L) * (A * μ * L) := by field_simp
    have h3 : (1 + K / L) * (A * μ * L) < b * (A * μ * L) := mul_lt_mul_of_pos_right hTμ hP
    linarith

/-- `prop:app-os-tail`(iv). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{proposition}[Tail modes]\label{prop:app-os-tail}
Let $\nu$ be a probability measure and $\mu>0$.
\begin{enumerate}[label=(\roman*)]
\item (Split bound.) For every $\ell\ge0$ with $\mathcal I_\nu(\ell)<\infty$,
\[
\mathfrak d^{\rm os}_\nu(\mu)\le\sqrt{\nu([0,\ell])}\,\sqrt{\frac\mu2}+\mathcal E\big(\mu,\mathcal I_\nu(\ell)\big).
\]
\item (Gradient-descent-like upper bound.) If $\nu(\{0\})=0$ and $\mathcal I_\nu<\infty$, then
\[
\mathfrak d^{\rm os}_\nu(\mu)\le\frac{\sqrt2}{\pi}\sqrt{\mathcal I_\nu}\;\mu\Big[\log\Big(1+\frac1{\mu\mathcal I_\nu}\Big)+2\Big].
\]
\item (Asymptotics.) If $\nu(\{0\})=0$ and $\mathcal I_\nu<\infty$, then, for fixed $\nu$,
\[
\mathfrak d^{\rm os}_\nu(\mu)\sim\frac{\sqrt2}{\pi}\sqrt{\mathcal I_\nu}\;\mu\log\frac1\mu\qquad(\mu\downarrow0).
\]
\item (Counts.) For every $K>0$,
\[
C_*\sqrt{\frac{\nu([0,K\mu])}{1+K}}\le\chi_\nu(\mu)\le\sqrt{\nu([0,K\mu])}+\frac{2}{\pi\sqrt K}\big[\log(1+K)+2\big].
\]
\item (Universal lower bound.) If $\nu([0,X])=1$ for some $X>0$, then
\[
\mathfrak d^{\rm os}_\nu(\mu)\ge\frac1\pi\,\frac{\mu}{\sqrt X}\Big[\log\Big(1+\frac X\mu\Big)-\frac{X}{X+\mu}\Big]\ge\frac1{2\pi}\,\frac{\mu}{\sqrt X}\,\log\frac X\mu .
\]
\item (Sequences.) For probability measures $\nu_N$ and numbers $\mu_N>0$ put
$\chi_N\defeq\chi_{\nu_N}(\mu_N)$. Then $\liminf_N\chi_N>0$ if and only if
$\liminf_N\nu_N([0,K\mu_N])>0$ for some $K>0$; and $\chi_N\to0$ if and only if
$\nu_N([0,K\mu_N])\to0$ for every $K>0$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_os_tail_iv (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μ : ℝ} (hμ : 0 < μ) {K : ℝ} (hK : 0 < K) :
    cStar * Real.sqrt ((ν (Icc 0 (K * μ))).toReal / (1 + K)) ≤ sqrtEff ν μ ∧
    sqrtEff ν μ ≤ Real.sqrt (ν (Icc 0 (K * μ))).toReal
      + 2 / (Real.pi * Real.sqrt K) * (Real.log (1 + K) + 2) := by
  refine ⟨?_, tail_count_upper ν hν hμ hK⟩
  have hC := chi_ge_Cstar_sqrt ν hν hμ
  have hC0 : 0 ≤ cStar :=
    add_nonneg (by norm_num) (div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
      Real.pi_pos.le)
  have hcs : cStar * Real.sqrt ((ν (Icc 0 (K * μ))).toReal / (1 + K))
      ≤ cStar * Real.sqrt (1 - mNu ν μ) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (tail_count_lower ν hν hμ hK)) hC0
  exact hcs.trans hC

private lemma tail_ftc_eq (μ a : ℝ) (hμ : 0 < μ) (ha : 0 ≤ a) :
    ∫ c in Ioc 0 a, c / (c + μ) ^ 2 = Real.log (a + μ) - Real.log μ + μ / (a + μ) - 1 := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) a,
      HasDerivAt (fun x => Real.log (x + μ) + μ / (x + μ)) (x / (x + μ) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le ha] at hx
    have hx0 : 0 ≤ x := hx.1
    have hxμ : x + μ ≠ 0 := (by linarith : (0:ℝ) < x + μ).ne'
    have d1 : HasDerivAt (fun x => Real.log (x + μ)) (1 / (x + μ)) x :=
      ((hasDerivAt_id' x).add_const μ).log hxμ
    have d2 : HasDerivAt (fun x => μ / (x + μ)) ((0 * (x + μ) - μ * 1) / (x + μ) ^ 2) x :=
      (hasDerivAt_const x μ).div ((hasDerivAt_id' x).add_const μ) hxμ
    convert d1.add d2 using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun c : ℝ => c / (c + μ) ^ 2) volume 0 a := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_id
    · exact (by fun_prop : Continuous fun c : ℝ => (c + μ) ^ 2).continuousOn
    · intro c hc
      rw [Set.uIcc_of_le ha] at hc
      have : 0 < c + μ := by linarith [hc.1]
      exact pow_ne_zero 2 this.ne'
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_of_le ha] at h
  rw [h]
  simp only [zero_add, div_self hμ.ne']
  ring

private lemma tail_v_upsilon_lower {ν : Measure ℝ} [IsProbabilityMeasure ν] {X c : ℝ}
    (hX : 0 < X) (hc : 0 < c) (hcX : c ≤ X) (hsupp : ν (Icc 0 X) = 1) :
    c ^ 2 / (2 * X) ≤ Upsilon ν c := by
  have hae : ∀ᵐ x ∂ν, x ∈ Icc 0 X := by
    have h0 : ν (Icc 0 X)ᶜ = 0 := (prob_compl_eq_zero_iff measurableSet_Icc).2 hsupp
    rw [ae_iff]
    exact h0
  have hint : Integrable (fun x : ℝ => x / (c + x)) ν := by
    refine Integrable.of_bound (by fun_prop : Measurable fun x : ℝ => x / (c + x)).aestronglyMeasurable 1 ?_
    filter_upwards [hae] with x hx
    obtain ⟨h0, hX'⟩ := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h0 (by linarith))]
    rw [div_le_one (by linarith)]
    linarith
  have hmono : mNu ν c ≤ X / (c + X) := by
    have hle : ∫ x, x / (c + x) ∂ν ≤ ∫ _x, X / (c + X) ∂ν := by
      apply integral_mono_ae hint (integrable_const _)
      filter_upwards [hae] with x hx
      obtain ⟨h0, hX'⟩ := hx
      show x / (c + x) ≤ X / (c + X)
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    simpa [integral_const, mNu] using hle
  have h1 : c * (1 - X / (c + X)) = c ^ 2 / (c + X) := by
    field_simp
    ring
  have h2 : c ^ 2 / (2 * X) ≤ c ^ 2 / (c + X) :=
    div_le_div_of_nonneg_left (sq_nonneg c) (by linarith) (by linarith)
  have h3 : c * (1 - X / (c + X)) ≤ c * (1 - mNu ν c) :=
    mul_le_mul_of_nonneg_left (by linarith) hc.le
  unfold Upsilon
  linarith

private lemma tail_v_sqrt_lower {ν : Measure ℝ} [IsProbabilityMeasure ν] {X c : ℝ}
    (hX : 0 < X) (hc : 0 < c) (hcX : c ≤ X) (hsupp : ν (Icc 0 X) = 1) :
    c / Real.sqrt (2 * X) ≤ Real.sqrt (Upsilon ν c) := by
  have hs : 0 < Real.sqrt (2 * X) := Real.sqrt_pos.2 (by linarith)
  have hs2 : Real.sqrt (2 * X) ^ 2 = 2 * X := Real.sq_sqrt (by linarith)
  rw [Real.le_sqrt' (div_pos hc hs), div_pow, hs2]
  exact tail_v_upsilon_lower hX hc hcX hsupp

private lemma tail_mNu_measurable (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Measurable (fun c : ℝ => mNu ν c) := by
  have hf : Measurable (fun p : ℝ × ℝ => p.2 / (p.1 + p.2)) := by fun_prop
  have hs := hf.stronglyMeasurable.integral_prod_right' (ν := ν)
  exact hs.measurable

private lemma tail_v_integrable {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μ X : ℝ} (hμ : 0 < μ) (hsupp : ν (Icc 0 X) = 1) :
    IntegrableOn (fun c : ℝ => Real.sqrt (Upsilon ν c) / (c + μ) ^ 2) (Ioi 0) := by
  have hae : ∀ᵐ x ∂ν, x ∈ Icc 0 X := by
    have h0 : ν (Icc 0 X)ᶜ = 0 := (prob_compl_eq_zero_iff measurableSet_Icc).2 hsupp
    rw [ae_iff]
    exact h0
  refine Integrable.mono' (tail_integrable_dom μ hμ) ?_ ?_
  · have hU : Measurable (fun c : ℝ => Upsilon ν c) := by
      unfold Upsilon
      exact measurable_id.mul (measurable_const.sub (tail_mNu_measurable ν))
    exact (by fun_prop : Measurable (fun c : ℝ => Real.sqrt (Upsilon ν c) / (c + μ) ^ 2)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro c hc
    have hc0 : 0 < c := hc
    have hm0 : 0 ≤ mNu ν c := by
      unfold mNu
      apply integral_nonneg_of_ae
      filter_upwards [hae] with x hx
      obtain ⟨h0, _⟩ := hx
      exact div_nonneg h0 (by linarith)
    have hUle : Upsilon ν c ≤ c := by
      unfold Upsilon
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hUle) (sq_nonneg _)

/-- Conditional first conjunct of `prop:app-os-tail`(v): given the representation of
`dOsSq` (the statement of `lem_app_os_repr_i`, taken as a hypothesis), the universal lower
bound follows from `S_ν(-c) ≥ 1/(2X)` for `c ≤ X`. -/
private lemma tail_v_first_cond {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μ X : ℝ} (hμ : 0 < μ) (hX : 0 < X) (hsupp : ν (Icc 0 X) = 1)
    (hrepr : dOsSq ν μ = Real.sqrt 2 / Real.pi * μ *
      ∫ c in Ioi (0 : ℝ), Real.sqrt (Upsilon ν c) / (c + μ) ^ 2) :
    1 / Real.pi * (μ / Real.sqrt X) * (Real.log (1 + X / μ) - X / (X + μ)) ≤ dOsSq ν μ := by
  have hs : 0 < Real.sqrt (2 * X) := Real.sqrt_pos.2 (by linarith)
  have hX' : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsplit : Real.sqrt (2 * X) = Real.sqrt 2 * Real.sqrt X := Real.sqrt_mul (by norm_num) X
  have hint := tail_v_integrable hν hμ hsupp
  have hnn : ∀ c : ℝ, 0 < c → 0 ≤ Real.sqrt (Upsilon ν c) / (c + μ) ^ 2 := fun c _ => by positivity
  have hcont : ContinuousOn (fun c : ℝ => c / (c + μ) ^ 2) (Icc 0 X) := by
    apply ContinuousOn.div continuousOn_id
    · exact (by fun_prop : Continuous fun c : ℝ => (c + μ) ^ 2).continuousOn
    · intro c hc
      have : 0 < c + μ := by linarith [hc.1]
      exact pow_ne_zero 2 this.ne'
  have hI1 : IntegrableOn (fun c : ℝ => c / (c + μ) ^ 2) (Ioc 0 X) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hJ : ∫ c in Ioc 0 X, c / (c + μ) ^ 2 = Real.log (X + μ) - Real.log μ + μ / (X + μ) - 1 :=
    tail_ftc_eq μ X hμ hX.le
  have hlog : Real.log (1 + X / μ) = Real.log (X + μ) - Real.log μ := by
    rw [← Real.log_div (by linarith) hμ.ne']
    congr 1
    rw [add_div, div_self hμ.ne']
    ring
  have hXm : X / (X + μ) + μ / (X + μ) = 1 := by
    rw [← add_div, div_self (by linarith : (0:ℝ) < X + μ).ne']
  have hLJ : Real.log (1 + X / μ) - X / (X + μ) = Real.log (X + μ) - Real.log μ + μ / (X + μ) - 1 := by
    rw [hlog]; linarith
  have hconst : ∫ c in Ioc 0 X, (1 / Real.sqrt (2 * X)) * (c / (c + μ) ^ 2)
      = (1 / Real.sqrt (2 * X)) * ∫ c in Ioc 0 X, c / (c + μ) ^ 2 := integral_const_mul _ _
  have hlow : ∫ c in Ioc 0 X, (1 / Real.sqrt (2 * X)) * (c / (c + μ) ^ 2)
      ≤ ∫ c in Ioc 0 X, Real.sqrt (Upsilon ν c) / (c + μ) ^ 2 := by
    apply setIntegral_mono_on (hI1.const_mul _) (hint.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc
    intro c hc
    have hc0 : 0 < c := hc.1
    have hcX : c ≤ X := hc.2
    have hsq := tail_v_sqrt_lower hX hc0 hcX hsupp
    rw [show (1 / Real.sqrt (2 * X)) * (c / (c + μ) ^ 2) = (c / Real.sqrt (2 * X)) / (c + μ) ^ 2 by ring]
    exact div_le_div_of_nonneg_right hsq (sq_nonneg _)
  have hmono : ∫ c in Ioc 0 X, Real.sqrt (Upsilon ν c) / (c + μ) ^ 2
      ≤ ∫ c in Ioi (0 : ℝ), Real.sqrt (Upsilon ν c) / (c + μ) ^ 2 :=
    setIntegral_mono_set hint
      (ae_restrict_iff' measurableSet_Ioi |>.2 (Filter.Eventually.of_forall fun c hc => hnn c hc))
      Ioc_subset_Ioi_self.eventuallyLE
  have key : Real.sqrt 2 / Real.pi * μ * ((1 / Real.sqrt (2 * X)) * (Real.log (X + μ) - Real.log μ + μ / (X + μ) - 1))
      = 1 / Real.pi * (μ / Real.sqrt X) * (Real.log (X + μ) - Real.log μ + μ / (X + μ) - 1) := by
    rw [hsplit]
    field_simp
  have hpos : 0 ≤ Real.sqrt 2 / Real.pi * μ := by positivity
  have hfin := mul_le_mul_of_nonneg_left (show (1 / Real.sqrt (2 * X)) * ∫ c in Ioc 0 X, c / (c + μ) ^ 2
      ≤ ∫ c in Ioc 0 X, Real.sqrt (Upsilon ν c) / (c + μ) ^ 2 by rw [← hconst]; exact le_trans hlow le_rfl) hpos
  rw [hJ] at hfin
  rw [hrepr]
  have hmono' := mul_le_mul_of_nonneg_left hmono hpos
  rw [hLJ]
  have : 1 / Real.pi * (μ / Real.sqrt X) * (Real.log (X + μ) - Real.log μ + μ / (X + μ) - 1)
      ≤ Real.sqrt 2 / Real.pi * μ * ∫ c in Ioi (0 : ℝ), Real.sqrt (Upsilon ν c) / (c + μ) ^ 2 := by
    rw [← key]
    exact le_trans hfin hmono'
  exact this

/-- Second conjunct of `prop:app-os-tail`(v): the logarithmic inequality (`lem:app-os-log`) at
`k = X/μ`. -/
private lemma tail_v_second {μ X : ℝ} (hμ : 0 < μ) (hX : 0 < X) :
    1 / (2 * Real.pi) * (μ / Real.sqrt X) * Real.log (X / μ)
      ≤ 1 / Real.pi * (μ / Real.sqrt X) * (Real.log (1 + X / μ) - X / (X + μ)) := by
  have hk := lem_app_os_log (k := X / μ) (div_pos hX hμ)
  have e : (X / μ) / (1 + X / μ) = X / (X + μ) := by
    have h1 : (1 + X / μ) ≠ 0 := by positivity
    have h2 : (X + μ) ≠ 0 := by linarith
    field_simp
    ring
  rw [e] at hk
  have hp : 0 ≤ 1 / Real.pi * (μ / Real.sqrt X) := by positivity
  calc 1 / (2 * Real.pi) * (μ / Real.sqrt X) * Real.log (X / μ)
      = 1 / Real.pi * (μ / Real.sqrt X) * (1 / 2 * Real.log (X / μ)) := by
        field_simp
    _ ≤ 1 / Real.pi * (μ / Real.sqrt X) * (Real.log (1 + X / μ) - X / (X + μ)) :=
        mul_le_mul_of_nonneg_left hk hp

/-- `prop:app-os-tail`(v). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{proposition}[Tail modes]\label{prop:app-os-tail}
Let $\nu$ be a probability measure and $\mu>0$.
\begin{enumerate}[label=(\roman*)]
\item (Split bound.) For every $\ell\ge0$ with $\mathcal I_\nu(\ell)<\infty$,
\[
\mathfrak d^{\rm os}_\nu(\mu)\le\sqrt{\nu([0,\ell])}\,\sqrt{\frac\mu2}+\mathcal E\big(\mu,\mathcal I_\nu(\ell)\big).
\]
\item (Gradient-descent-like upper bound.) If $\nu(\{0\})=0$ and $\mathcal I_\nu<\infty$, then
\[
\mathfrak d^{\rm os}_\nu(\mu)\le\frac{\sqrt2}{\pi}\sqrt{\mathcal I_\nu}\;\mu\Big[\log\Big(1+\frac1{\mu\mathcal I_\nu}\Big)+2\Big].
\]
\item (Asymptotics.) If $\nu(\{0\})=0$ and $\mathcal I_\nu<\infty$, then, for fixed $\nu$,
\[
\mathfrak d^{\rm os}_\nu(\mu)\sim\frac{\sqrt2}{\pi}\sqrt{\mathcal I_\nu}\;\mu\log\frac1\mu\qquad(\mu\downarrow0).
\]
\item (Counts.) For every $K>0$,
\[
C_*\sqrt{\frac{\nu([0,K\mu])}{1+K}}\le\chi_\nu(\mu)\le\sqrt{\nu([0,K\mu])}+\frac{2}{\pi\sqrt K}\big[\log(1+K)+2\big].
\]
\item (Universal lower bound.) If $\nu([0,X])=1$ for some $X>0$, then
\[
\mathfrak d^{\rm os}_\nu(\mu)\ge\frac1\pi\,\frac{\mu}{\sqrt X}\Big[\log\Big(1+\frac X\mu\Big)-\frac{X}{X+\mu}\Big]\ge\frac1{2\pi}\,\frac{\mu}{\sqrt X}\,\log\frac X\mu .
\]
\item (Sequences.) For probability measures $\nu_N$ and numbers $\mu_N>0$ put
$\chi_N\defeq\chi_{\nu_N}(\mu_N)$. Then $\liminf_N\chi_N>0$ if and only if
$\liminf_N\nu_N([0,K\mu_N])>0$ for some $K>0$; and $\chi_N\to0$ if and only if
$\nu_N([0,K\mu_N])\to0$ for every $K>0$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_os_tail_v (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μ : ℝ} (hμ : 0 < μ) {X : ℝ} (hX : 0 < X) (hsupp : ν (Icc 0 X) = 1) :
    1 / Real.pi * (μ / Real.sqrt X) * (Real.log (1 + X / μ) - X / (X + μ)) ≤ dOsSq ν μ ∧
    1 / (2 * Real.pi) * (μ / Real.sqrt X) * Real.log (X / μ)
      ≤ 1 / Real.pi * (μ / Real.sqrt X) * (Real.log (1 + X / μ) - X / (X + μ)) := by
  exact ⟨tail_v_first_cond hν hμ hX hsupp (lem_app_os_repr_i ν hν hμ), tail_v_second hμ hX⟩

/-- `prop:app-os-tail`(vi). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{proposition}[Tail modes]\label{prop:app-os-tail}
Let $\nu$ be a probability measure and $\mu>0$.
\begin{enumerate}[label=(\roman*)]
\item (Split bound.) For every $\ell\ge0$ with $\mathcal I_\nu(\ell)<\infty$,
\[
\mathfrak d^{\rm os}_\nu(\mu)\le\sqrt{\nu([0,\ell])}\,\sqrt{\frac\mu2}+\mathcal E\big(\mu,\mathcal I_\nu(\ell)\big).
\]
\item (Gradient-descent-like upper bound.) If $\nu(\{0\})=0$ and $\mathcal I_\nu<\infty$, then
\[
\mathfrak d^{\rm os}_\nu(\mu)\le\frac{\sqrt2}{\pi}\sqrt{\mathcal I_\nu}\;\mu\Big[\log\Big(1+\frac1{\mu\mathcal I_\nu}\Big)+2\Big].
\]
\item (Asymptotics.) If $\nu(\{0\})=0$ and $\mathcal I_\nu<\infty$, then, for fixed $\nu$,
\[
\mathfrak d^{\rm os}_\nu(\mu)\sim\frac{\sqrt2}{\pi}\sqrt{\mathcal I_\nu}\;\mu\log\frac1\mu\qquad(\mu\downarrow0).
\]
\item (Counts.) For every $K>0$,
\[
C_*\sqrt{\frac{\nu([0,K\mu])}{1+K}}\le\chi_\nu(\mu)\le\sqrt{\nu([0,K\mu])}+\frac{2}{\pi\sqrt K}\big[\log(1+K)+2\big].
\]
\item (Universal lower bound.) If $\nu([0,X])=1$ for some $X>0$, then
\[
\mathfrak d^{\rm os}_\nu(\mu)\ge\frac1\pi\,\frac{\mu}{\sqrt X}\Big[\log\Big(1+\frac X\mu\Big)-\frac{X}{X+\mu}\Big]\ge\frac1{2\pi}\,\frac{\mu}{\sqrt X}\,\log\frac X\mu .
\]
\item (Sequences.) For probability measures $\nu_N$ and numbers $\mu_N>0$ put
$\chi_N\defeq\chi_{\nu_N}(\mu_N)$. Then $\liminf_N\chi_N>0$ if and only if
$\liminf_N\nu_N([0,K\mu_N])>0$ for some $K>0$; and $\chi_N\to0$ if and only if
$\nu_N([0,K\mu_N])\to0$ for every $K>0$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_os_tail_vi (ν : ℕ → Measure ℝ) [∀ N, IsProbabilityMeasure (ν N)]
    (hν : ∀ N, ν N (Iio 0) = 0) (μ : ℕ → ℝ) (hμ : ∀ N, 0 < μ N) :
    (0 < liminf (fun N => sqrtEff (ν N) (μ N)) atTop ↔
        ∃ K : ℝ, 0 < K ∧ 0 < liminf (fun N => (ν N (Icc 0 (K * μ N))).toReal) atTop) ∧
    (Tendsto (fun N => sqrtEff (ν N) (μ N)) atTop (𝓝 0) ↔
        ∀ K : ℝ, 0 < K → Tendsto (fun N => (ν N (Icc 0 (K * μ N))).toReal) atTop (𝓝 0)) := by
  have hS_bdd : ∀ N, sqrtEff (ν N) (μ N) ≤ 1 := fun N => (lem_app_os_repr_iii (ν N) (hν N) (hμ N)).2
  have hS_pos : ∀ N, 0 ≤ sqrtEff (ν N) (μ N) := fun N => (lem_app_os_repr_iii (ν N) (hν N) (hμ N)).1.le
  have hp_le : ∀ N (K : ℝ), (ν N (Icc 0 (K * μ N))).toReal ≤ 1 := fun N K =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  have hp_nonneg : ∀ N (K : ℝ), 0 ≤ (ν N (Icc 0 (K * μ N))).toReal := fun _ _ =>
    ENNReal.toReal_nonneg
  have hlo : ∀ N (K : ℝ), 0 < K → cStar * Real.sqrt ((ν N (Icc 0 (K * μ N))).toReal / (1 + K))
      ≤ sqrtEff (ν N) (μ N) := fun N K hK =>
    (prop_app_os_tail_iv (ν N) (hν N) (hμ N) hK).1
  have hup : ∀ N (K : ℝ), 0 < K → sqrtEff (ν N) (μ N) ≤ Real.sqrt (ν N (Icc 0 (K * μ N))).toReal
      + 2 / (Real.pi * Real.sqrt K) * (Real.log (1 + K) + 2) := fun N K hK =>
    (prop_app_os_tail_iv (ν N) (hν N) (hμ N) hK).2
  have hc : 0 < cStar := add_pos_of_pos_of_nonneg (by norm_num)
    (div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) Real.pi_pos.le)
  constructor
  · constructor
    · intro hpos
      obtain ⟨L, hLdef⟩ : ∃ L, L = liminf (fun N => sqrtEff (ν N) (μ N)) atTop := ⟨_, rfl⟩
      rw [← hLdef] at hpos
      obtain ⟨K, hKC, hKgt⟩ := ((tail_C_tendsto.eventually
        (gt_mem_nhds (by linarith : (0 : ℝ) < L / 4))).and (eventually_gt_atTop (0 : ℝ))).exists
      have hev : ∀ᶠ N in atTop, 3 * L / 4 < sqrtEff (ν N) (μ N) :=
        eventually_lt_of_lt_liminf (by linarith) (isBoundedUnder_of ⟨0, hS_pos⟩)
      have hev2 : ∀ᶠ N in atTop, (L / 2) ^ 2 ≤ (ν N (Icc 0 (K * μ N))).toReal := by
        filter_upwards [hev] with N hN
        have h1 := hup N K hKgt
        have h2 : L / 2 < Real.sqrt (ν N (Icc 0 (K * μ N))).toReal := by linarith
        exact ((Real.lt_sqrt (by linarith)).1 h2).le
      refine ⟨K, hKgt, lt_of_lt_of_le (pow_pos (half_pos hpos) 2) ?_⟩
      exact le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun N => hp_le N K)) hev2
    · rintro ⟨K, hK, hpos⟩
      obtain ⟨l, hl⟩ : ∃ l, l = liminf (fun N => (ν N (Icc 0 (K * μ N))).toReal) atTop :=
        ⟨_, rfl⟩
      rw [← hl] at hpos
      have hev : ∀ᶠ N in atTop, l / 2 < (ν N (Icc 0 (K * μ N))).toReal :=
        eventually_lt_of_lt_liminf (by linarith) (isBoundedUnder_of ⟨0, fun N => hp_nonneg N K⟩)
      refine lt_of_lt_of_le ?_ (le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun N => hS_bdd N))
        (?_ : ∀ᶠ N in atTop, cStar * Real.sqrt ((l / 2) / (1 + K)) ≤ sqrtEff (ν N) (μ N)))
      · exact mul_pos hc (Real.sqrt_pos.2 (div_pos (half_pos hpos) (by linarith)))
      · filter_upwards [hev] with N hN
        exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
          (div_le_div_of_nonneg_right hN.le (by linarith))) hc.le).trans (hlo N K hK)
  · constructor
    · intro hT K hK
      have hg : Tendsto (fun N => (1 + K) * (sqrtEff (ν N) (μ N) / cStar) ^ 2) atTop (𝓝 0) := by
        have := ((hT.div_const cStar).pow 2).const_mul (1 + K)
        rw [zero_div, zero_pow two_ne_zero, mul_zero] at this
        exact this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
        (Eventually.of_forall fun N => hp_nonneg N K) (Eventually.of_forall fun N => ?_)
      have h1K : (0 : ℝ) < 1 + K := by linarith
      have hsqrt : Real.sqrt ((ν N (Icc 0 (K * μ N))).toReal / (1 + K))
          ≤ sqrtEff (ν N) (μ N) / cStar := by
        rw [le_div_iff₀ hc]
        rw [mul_comm]
        exact hlo N K hK
      have hx : (ν N (Icc 0 (K * μ N))).toReal / (1 + K) ≤ (sqrtEff (ν N) (μ N) / cStar) ^ 2 := by
        calc (ν N (Icc 0 (K * μ N))).toReal / (1 + K)
            = Real.sqrt ((ν N (Icc 0 (K * μ N))).toReal / (1 + K)) ^ 2 :=
              (Real.sq_sqrt (div_nonneg (hp_nonneg N K) h1K.le)).symm
          _ ≤ (sqrtEff (ν N) (μ N) / cStar) ^ 2 :=
              pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
      rw [div_le_iff₀ h1K] at hx
      exact hx.trans_eq (mul_comm _ _)
    · intro hK
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨K, hKC, hKpos⟩ := ((tail_C_tendsto.eventually
        (gt_mem_nhds (half_pos hε))).and (eventually_gt_atTop (0 : ℝ))).exists
      have hsq : Tendsto (fun N => Real.sqrt (ν N (Icc 0 (K * μ N))).toReal) atTop (𝓝 0) := by
        have := (hK K hKpos).sqrt
        rw [Real.sqrt_zero] at this
        exact this
      filter_upwards [hsq.eventually (gt_mem_nhds (half_pos hε))] with N hN
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hS_pos N)]
      linarith [hup N K hKpos]

end

end Muon.Oversampled

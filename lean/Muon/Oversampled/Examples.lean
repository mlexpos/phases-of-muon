import Mathlib
import Muon.Oversampled.Profile
import Muon.Oversampled.Representation
import Muon.Oversampled.SqrtLaw
import Muon.Oversampled.Tail

/-!
# Oversampled examples: two-level spectrum, acceleration, power-law spectra; packing
(Appendix G2, work package L-G2.5)

Source of record: snapshot `cr-2026-10-23`, `sections/12-oversampled/section.tex`.
Scope: `cor:app-os-twolevel`, `cor:app-os-accel`, `cor:app-os-powerlaw`, and the promoted part of
`rem:app-os-packed` (monotonicity of packing, and the power-law packing on `Fin N`). The remainder of
`rem:app-os-packed` (geometric spectrum, necessity) stays out of scope.

Reused: `dOsSq`, `sqrtEff`, `mNu`, `varpi` (`Muon.Oversampled.Profile`); `tailInt` (`Muon.Oversampled.Tail`);
`cStar` (`Muon.Oversampled.SqrtLaw`). Measure representation as fixed by L-G2.1: `ν : Measure ℝ`,
`[IsProbabilityMeasure ν]`, `ν (Set.Iio 0) = 0`.

Card points applied: §6.12 (the uniform clause of `cor:app-os-powerlaw`(ii) is written as the source
has it, `max` over `{i ≤ ε_N N}`, with the empty maximum read as `0` by `⨆`); §6.13 (`c_hi ≤ 5.78` is the
separate declaration `cor_app_os_twolevel_c_hi_le`, with the numerical input `log 3 ≤ 1.0988` as the helper
`log_three_le`).

The packing predicate `def:app-os-packed` is owned by L-G2.7 (`Muon.Oversampled.Model`). The two packing
declarations here state its unfolded form `δ * N ≤ #{k | μ k ≤ K * μ i}` so that this file does not import
`Model`; L-G2.7 may instantiate them.
-/

open MeasureTheory Set Filter Topology

namespace Muon.Oversampled

noncomputable section

/-! ## Two-level spectrum (`cor:app-os-twolevel`) -/

/-- Label `cor:app-os-twolevel`, definition of `ν_{p,κ}`, `Ω_{p,κ}`, `c_hi`. Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Two-level spectrum]\label{cor:app-os-twolevel}
Let $\nu_{p,\varkappa}\defeq(1-p)\delta_1+p\,\delta_{1/\varkappa}$ with $p\in(0,1)$ and
$\varkappa\ge2$, write $\mathfrak d^{\rm os}=\mathfrak d^{\rm os}_{\nu_{p,\varkappa}}$, and put
\[
\Omega_{p,\varkappa}\defeq\max\Big\{\sqrt{\frac p\varkappa},\ \frac{\log\varkappa}{\varkappa}\Big\},\qquad
c_{\rm hi}\defeq\frac2{C_*}\Big(\frac1{\sqrt2}+\frac{\sqrt2}{\pi}\,\frac{\log3+2}{\log2}\Big)\le5.78 .
\]
Then
\[
\begin{gathered}
\mathfrak d^{\rm os}(1)\in\Big[\frac{C_*}2,\frac1{\sqrt2}\Big],\\
\max\Big\{\frac{C_*}2\sqrt{\frac p\varkappa},\ \frac1{2\pi}\frac{\log\varkappa}\varkappa\Big\}
\le\mathfrak d^{\rm os}(1/\varkappa)\le\sqrt{\frac{p}{2\varkappa}}+\frac{\sqrt2}{\pi}\,\frac{\log(1+\varkappa)+2}{\varkappa},
\end{gathered}
\]
and consequently
\[
\frac{\Omega_{p,\varkappa}}{\sqrt2\,\pi}\le\frac{\mathfrak d^{\rm os}(1/\varkappa)}{\mathfrak d^{\rm os}(1)}\le c_{\rm hi}\,\Omega_{p,\varkappa}.
\]
\end{corollary}
-/
def nuTL (p κ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.dirac 1 + ENNReal.ofReal p • Measure.dirac (1 / κ)

/-- Label `cor:app-os-twolevel`, definition of `Ω_{p,κ}`. Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Two-level spectrum]\label{cor:app-os-twolevel}
Let $\nu_{p,\varkappa}\defeq(1-p)\delta_1+p\,\delta_{1/\varkappa}$ with $p\in(0,1)$ and
$\varkappa\ge2$, write $\mathfrak d^{\rm os}=\mathfrak d^{\rm os}_{\nu_{p,\varkappa}}$, and put
\[
\Omega_{p,\varkappa}\defeq\max\Big\{\sqrt{\frac p\varkappa},\ \frac{\log\varkappa}{\varkappa}\Big\},\qquad
c_{\rm hi}\defeq\frac2{C_*}\Big(\frac1{\sqrt2}+\frac{\sqrt2}{\pi}\,\frac{\log3+2}{\log2}\Big)\le5.78 .
\]
Then
\[
\begin{gathered}
\mathfrak d^{\rm os}(1)\in\Big[\frac{C_*}2,\frac1{\sqrt2}\Big],\\
\max\Big\{\frac{C_*}2\sqrt{\frac p\varkappa},\ \frac1{2\pi}\frac{\log\varkappa}\varkappa\Big\}
\le\mathfrak d^{\rm os}(1/\varkappa)\le\sqrt{\frac{p}{2\varkappa}}+\frac{\sqrt2}{\pi}\,\frac{\log(1+\varkappa)+2}{\varkappa},
\end{gathered}
\]
and consequently
\[
\frac{\Omega_{p,\varkappa}}{\sqrt2\,\pi}\le\frac{\mathfrak d^{\rm os}(1/\varkappa)}{\mathfrak d^{\rm os}(1)}\le c_{\rm hi}\,\Omega_{p,\varkappa}.
\]
\end{corollary}
-/
def omegaTL (p κ : ℝ) : ℝ :=
  max (Real.sqrt (p / κ)) (Real.log κ / κ)

/-- Label `cor:app-os-twolevel`, definition of the constant `c_hi`. Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Two-level spectrum]\label{cor:app-os-twolevel}
Let $\nu_{p,\varkappa}\defeq(1-p)\delta_1+p\,\delta_{1/\varkappa}$ with $p\in(0,1)$ and
$\varkappa\ge2$, write $\mathfrak d^{\rm os}=\mathfrak d^{\rm os}_{\nu_{p,\varkappa}}$, and put
\[
\Omega_{p,\varkappa}\defeq\max\Big\{\sqrt{\frac p\varkappa},\ \frac{\log\varkappa}{\varkappa}\Big\},\qquad
c_{\rm hi}\defeq\frac2{C_*}\Big(\frac1{\sqrt2}+\frac{\sqrt2}{\pi}\,\frac{\log3+2}{\log2}\Big)\le5.78 .
\]
Then
\[
\begin{gathered}
\mathfrak d^{\rm os}(1)\in\Big[\frac{C_*}2,\frac1{\sqrt2}\Big],\\
\max\Big\{\frac{C_*}2\sqrt{\frac p\varkappa},\ \frac1{2\pi}\frac{\log\varkappa}\varkappa\Big\}
\le\mathfrak d^{\rm os}(1/\varkappa)\le\sqrt{\frac{p}{2\varkappa}}+\frac{\sqrt2}{\pi}\,\frac{\log(1+\varkappa)+2}{\varkappa},
\end{gathered}
\]
and consequently
\[
\frac{\Omega_{p,\varkappa}}{\sqrt2\,\pi}\le\frac{\mathfrak d^{\rm os}(1/\varkappa)}{\mathfrak d^{\rm os}(1)}\le c_{\rm hi}\,\Omega_{p,\varkappa}.
\]
\end{corollary}
-/
def cHi : ℝ :=
  2 / cStar * (1 / Real.sqrt 2 + Real.sqrt 2 / Real.pi * ((Real.log 3 + 2) / Real.log 2))

/-- Numerical input for `c_hi ≤ 5.78`: `log 3 ≤ 1.0988` (card §6.13). Absent from Mathlib; the intended
route is `Real.exp_one_gt_d9` with `Real.quadratic_le_exp_of_nonneg`, since `e^{1.0988} > 3`. Helper,
not a source label. -/
theorem log_three_le : Real.log 3 ≤ 1.0988 := by
  have h1 : (3:ℝ) < Real.exp 1.0988 := by
    have hx : (1.0988:ℝ) = 1 + 0.0988 := by norm_num
    rw [hx, Real.exp_add]
    have hq := Real.quadratic_le_exp_of_nonneg (x := (0.0988:ℝ)) (by norm_num)
    have he := Real.exp_one_gt_d9
    have hq' : (1.10368:ℝ) ≤ Real.exp 0.0988 := by norm_num at hq ⊢; linarith
    have hpos : (0:ℝ) ≤ Real.exp 0.0988 := (Real.exp_pos _).le
    nlinarith [mul_le_mul he.le hq' (by norm_num) (Real.exp_pos 1).le]
  exact (Real.log_le_iff_le_exp (by norm_num)).mpr h1.le

/-- Monotonicity used by `cor:app-os-twolevel`: `(log(1+κ)+2)/log κ ≤ (log 3+2)/log 2` for `κ ≥ 2`
(the proof of `cor:app-os-twolevel` states that this ratio is decreasing). Helper, not a source label. -/
theorem twolevel_log_ratio_le {κ : ℝ} (hκ : 2 ≤ κ) :
    (Real.log (1 + κ) + 2) / Real.log κ ≤ (Real.log 3 + 2) / Real.log 2 := by
  have hκ0 : (0:ℝ) < κ := by linarith
  have hlogκ : 0 < Real.log κ := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have ha1 : 1 ≤ (Real.log 3 + 2) / Real.log 2 := by
    rw [le_div_iff₀ hl2]; linarith
  have hsub : 0 ≤ Real.log κ - Real.log 2 := by
    have := Real.log_le_log (by norm_num) hκ; linarith
  have e1 : Real.log (1 + κ) - Real.log 3 = Real.log ((1 + κ) / 3) :=
    (Real.log_div (by linarith) (by norm_num)).symm
  have e2 : Real.log κ - Real.log 2 = Real.log (κ / 2) :=
    (Real.log_div (by linarith) (by norm_num)).symm
  have hdiff : Real.log (1 + κ) - Real.log 3 ≤ Real.log κ - Real.log 2 := by
    rw [e1, e2]
    apply Real.log_le_log (by linarith)
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
  have ha : (Real.log 3 + 2) / Real.log 2 * Real.log 2 = Real.log 3 + 2 :=
    div_mul_cancel₀ _ hl2.ne'
  have hmul : 1 * (Real.log κ - Real.log 2) ≤
      (Real.log 3 + 2) / Real.log 2 * (Real.log κ - Real.log 2) :=
    mul_le_mul_of_nonneg_right ha1 hsub
  rw [div_le_iff₀ hlogκ]
  nlinarith

/-! ### Private helpers for `cor:app-os-twolevel` (fully proved) -/

private lemma tl_cStar_pos : 0 < cStar := by
  unfold cStar
  have h1 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have h2 := Real.pi_pos
  have h3 : 0 < 2 * Real.log 2 / Real.pi := div_pos (by linarith) h2
  linarith

private lemma tl_sqrt_half : Real.sqrt (1 / 2) = 1 / Real.sqrt 2 := by
  rw [Real.sqrt_div zero_le_one, Real.sqrt_one]

private lemma tl_apply_set (p κ : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    nuTL p κ s = ENNReal.ofReal (1 - p) * s.indicator 1 1
      + ENNReal.ofReal p * s.indicator 1 (1 / κ) := by
  unfold nuTL
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hs, Measure.dirac_apply' _ hs, smul_eq_mul, smul_eq_mul]

private lemma tl_isProb {p κ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    IsProbabilityMeasure (nuTL p κ) := by
  refine ⟨?_⟩
  rw [tl_apply_set p κ univ MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) hp0.le]
  norm_num

private lemma tl_Iio {p κ : ℝ} (hκ : 2 ≤ κ) : nuTL p κ (Iio 0) = 0 := by
  have hκ0 : (0:ℝ) < κ := by linarith
  have h1 : (1:ℝ) ∉ Iio (0:ℝ) := fun h => (not_lt.mpr zero_le_one : ¬ (1:ℝ) < 0) h
  have h2 : (1 / κ : ℝ) ∉ Iio (0:ℝ) := fun h => (not_lt.mpr (one_div_nonneg.mpr hκ0.le) : ¬ (1 / κ : ℝ) < 0) h
  rw [tl_apply_set p κ _ measurableSet_Iio, Set.indicator_of_notMem h1,
    Set.indicator_of_notMem h2]
  simp

private lemma tl_Icc_one {p κ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hκ : 2 ≤ κ) :
    nuTL p κ (Icc 0 1) = 1 := by
  have hκ0 : (0:ℝ) < κ := by linarith
  have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h2 : (1 / κ : ℝ) ∈ Icc (0:ℝ) 1 :=
    ⟨one_div_nonneg.mpr hκ0.le, by rw [div_le_one hκ0]; linarith⟩
  rw [tl_apply_set p κ _ measurableSet_Icc]
  simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) hp0.le]
  norm_num

private lemma tl_Icc_k {p κ : ℝ} (hp1 : p < 1) (hκ : 2 ≤ κ) :
    nuTL p κ (Icc 0 (1 / κ)) = ENNReal.ofReal p := by
  have hκ0 : (0:ℝ) < κ := by linarith
  have h2 : (1 / κ : ℝ) ∈ Icc (0:ℝ) (1 / κ) := ⟨one_div_nonneg.mpr hκ0.le, le_rfl⟩
  have hlt : 1 / κ < (1:ℝ) := (div_lt_one hκ0).mpr (by linarith)
  have h1 : (1:ℝ) ∉ Icc (0:ℝ) (1 / κ) := fun h => absurd h.2 (not_le.mpr hlt)
  rw [tl_apply_set p κ _ measurableSet_Icc, Set.indicator_of_notMem h1,
    Set.indicator_of_mem h2]
  simp

private lemma tl_tail {p κ : ℝ} (hκ : 2 ≤ κ) :
    tailInt (nuTL p κ) (1 / κ) = ENNReal.ofReal (1 - p) := by
  have hκ0 : (0:ℝ) < κ := by linarith
  have hlt : 1 / κ < (1:ℝ) := (div_lt_one hκ0).mpr (by linarith)
  have h1 : (1:ℝ) ∈ Ioi (1 / κ) := hlt
  have h2 : (1 / κ : ℝ) ∉ Ioi (1 / κ) := fun h => lt_irrefl (1 / κ : ℝ) h
  unfold tailInt nuTL
  rw [← lintegral_indicator measurableSet_Ioi, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac, lintegral_dirac]
  rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
  simp

/-- Label `cor:app-os-twolevel`, part (i). Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Two-level spectrum]\label{cor:app-os-twolevel}
Let $\nu_{p,\varkappa}\defeq(1-p)\delta_1+p\,\delta_{1/\varkappa}$ with $p\in(0,1)$ and
$\varkappa\ge2$, write $\mathfrak d^{\rm os}=\mathfrak d^{\rm os}_{\nu_{p,\varkappa}}$, and put
\[
\Omega_{p,\varkappa}\defeq\max\Big\{\sqrt{\frac p\varkappa},\ \frac{\log\varkappa}{\varkappa}\Big\},\qquad
c_{\rm hi}\defeq\frac2{C_*}\Big(\frac1{\sqrt2}+\frac{\sqrt2}{\pi}\,\frac{\log3+2}{\log2}\Big)\le5.78 .
\]
Then
\[
\begin{gathered}
\mathfrak d^{\rm os}(1)\in\Big[\frac{C_*}2,\frac1{\sqrt2}\Big],\\
\max\Big\{\frac{C_*}2\sqrt{\frac p\varkappa},\ \frac1{2\pi}\frac{\log\varkappa}\varkappa\Big\}
\le\mathfrak d^{\rm os}(1/\varkappa)\le\sqrt{\frac{p}{2\varkappa}}+\frac{\sqrt2}{\pi}\,\frac{\log(1+\varkappa)+2}{\varkappa},
\end{gathered}
\]
and consequently
\[
\frac{\Omega_{p,\varkappa}}{\sqrt2\,\pi}\le\frac{\mathfrak d^{\rm os}(1/\varkappa)}{\mathfrak d^{\rm os}(1)}\le c_{\rm hi}\,\Omega_{p,\varkappa}.
\]
\end{corollary}
-/
theorem cor_app_os_twolevel_i {p κ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hκ : 2 ≤ κ) :
    cStar / 2 ≤ dOsSq (nuTL p κ) 1 ∧ dOsSq (nuTL p κ) 1 ≤ 1 / Real.sqrt 2 := by
  haveI := tl_isProb (p := p) (κ := κ) hp0 hp1
  have hν : nuTL p κ (Iio 0) = 0 := tl_Iio (p := p) hκ
  have hsup : nuTL p κ (Icc 0 1) = 1 := tl_Icc_one hp0 hp1 hκ
  have hS := thm_app_os_sqrt_i (nuTL p κ) hν (μ := 1) one_pos
  have hII := thm_app_os_sqrt_ii (nuTL p κ) hν (μ := 1) (K := 1) one_pos one_pos
  have hm : (1 / 2 : ℝ) ≤ 1 - mNu (nuTL p κ) 1 := by
    have h := hII.2
    rw [hsup, ENNReal.toReal_one] at h
    linarith
  have hsq0 : 0 ≤ Real.sqrt (1 / 2) := Real.sqrt_nonneg _
  have hsqsq : Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = 1 / 2 :=
    Real.mul_self_sqrt (by norm_num)
  have ht : Real.sqrt (1 / 2) ≤ Real.sqrt (1 - mNu (nuTL p κ) 1) := Real.sqrt_le_sqrt hm
  have hlow : cStar / 2 ≤
      max (cStar * Real.sqrt (1 - mNu (nuTL p κ) 1)) (1 - mNu (nuTL p κ) 1)
        * Real.sqrt (1 / 2) := by
    have h2 : cStar * Real.sqrt (1 / 2) * Real.sqrt (1 / 2)
        ≤ cStar * Real.sqrt (1 - mNu (nuTL p κ) 1) * Real.sqrt (1 / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht tl_cStar_pos.le) hsq0
    have h3 : cStar * Real.sqrt (1 - mNu (nuTL p κ) 1) * Real.sqrt (1 / 2)
        ≤ max (cStar * Real.sqrt (1 - mNu (nuTL p κ) 1)) (1 - mNu (nuTL p κ) 1)
          * Real.sqrt (1 / 2) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hsq0
    have h4 : cStar * Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = cStar / 2 := by
      rw [mul_assoc, hsqsq]; ring
    linarith
  exact ⟨le_trans hlow hS.1, hS.2.trans_eq tl_sqrt_half⟩

/-- Label `cor:app-os-twolevel`, part (ii). Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Two-level spectrum]\label{cor:app-os-twolevel}
Let $\nu_{p,\varkappa}\defeq(1-p)\delta_1+p\,\delta_{1/\varkappa}$ with $p\in(0,1)$ and
$\varkappa\ge2$, write $\mathfrak d^{\rm os}=\mathfrak d^{\rm os}_{\nu_{p,\varkappa}}$, and put
\[
\Omega_{p,\varkappa}\defeq\max\Big\{\sqrt{\frac p\varkappa},\ \frac{\log\varkappa}{\varkappa}\Big\},\qquad
c_{\rm hi}\defeq\frac2{C_*}\Big(\frac1{\sqrt2}+\frac{\sqrt2}{\pi}\,\frac{\log3+2}{\log2}\Big)\le5.78 .
\]
Then
\[
\begin{gathered}
\mathfrak d^{\rm os}(1)\in\Big[\frac{C_*}2,\frac1{\sqrt2}\Big],\\
\max\Big\{\frac{C_*}2\sqrt{\frac p\varkappa},\ \frac1{2\pi}\frac{\log\varkappa}\varkappa\Big\}
\le\mathfrak d^{\rm os}(1/\varkappa)\le\sqrt{\frac{p}{2\varkappa}}+\frac{\sqrt2}{\pi}\,\frac{\log(1+\varkappa)+2}{\varkappa},
\end{gathered}
\]
and consequently
\[
\frac{\Omega_{p,\varkappa}}{\sqrt2\,\pi}\le\frac{\mathfrak d^{\rm os}(1/\varkappa)}{\mathfrak d^{\rm os}(1)}\le c_{\rm hi}\,\Omega_{p,\varkappa}.
\]
\end{corollary}
-/
theorem cor_app_os_twolevel_ii {p κ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hκ : 2 ≤ κ) :
    max (cStar / 2 * Real.sqrt (p / κ)) (1 / (2 * Real.pi) * (Real.log κ / κ))
      ≤ dOsSq (nuTL p κ) (1 / κ) := by
  haveI := tl_isProb (p := p) (κ := κ) hp0 hp1
  have hκ0 : (0:ℝ) < κ := by linarith
  have hκne : κ ≠ 0 := hκ0.ne'
  have hν : nuTL p κ (Iio 0) = 0 := tl_Iio (p := p) hκ
  have hμ : (0:ℝ) < 1 / κ := one_div_pos.mpr hκ0
  have htoR : (nuTL p κ (Icc 0 (1 / κ))).toReal = p := by
    rw [tl_Icc_k hp1 hκ, ENNReal.toReal_ofReal hp0.le]
  have hII := thm_app_os_sqrt_ii (nuTL p κ) hν (μ := 1 / κ) (K := 1) hμ one_pos
  have hm : p / 2 ≤ 1 - mNu (nuTL p κ) (1 / κ) := by
    have h := hII.2
    rw [htoR] at h
    linarith
  have hS := thm_app_os_sqrt_i (nuTL p κ) hν (μ := 1 / κ) hμ
  have hsqrt : Real.sqrt (p / 2) ≤ Real.sqrt (1 - mNu (nuTL p κ) (1 / κ)) :=
    Real.sqrt_le_sqrt hm
  have hE : Real.sqrt (p / 2) * Real.sqrt (1 / κ / 2) = Real.sqrt (p / κ) / 2 := by
    rw [← Real.sqrt_mul (div_nonneg hp0.le zero_le_two)]
    have e : p / 2 * (1 / κ / 2) = (p / κ) / 4 := by
      field_simp
      ring
    rw [e, Real.sqrt_div (div_nonneg hp0.le hκ0.le) 4]
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq zero_le_two
    rw [h4]
  have hkey1 : cStar / 2 * Real.sqrt (p / κ) ≤ dOsSq (nuTL p κ) (1 / κ) := by
    calc cStar / 2 * Real.sqrt (p / κ)
        = cStar * (Real.sqrt (p / 2) * Real.sqrt (1 / κ / 2)) := by rw [hE]; ring
      _ ≤ cStar * (Real.sqrt (1 - mNu (nuTL p κ) (1 / κ)) * Real.sqrt (1 / κ / 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)) tl_cStar_pos.le
      _ = cStar * Real.sqrt (1 - mNu (nuTL p κ) (1 / κ)) * Real.sqrt (1 / κ / 2) := by ring
      _ ≤ max (cStar * Real.sqrt (1 - mNu (nuTL p κ) (1 / κ)))
            (1 - mNu (nuTL p κ) (1 / κ)) * Real.sqrt (1 / κ / 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      _ ≤ dOsSq (nuTL p κ) (1 / κ) := hS.1
  have hsupp : nuTL p κ (Icc 0 1) = 1 := tl_Icc_one hp0 hp1 hκ
  have hv := prop_app_os_tail_v (nuTL p κ) hν hμ (X := 1) one_pos hsupp
  have hkey2 : 1 / (2 * Real.pi) * (Real.log κ / κ) ≤ dOsSq (nuTL p κ) (1 / κ) := by
    have h := le_trans hv.2 hv.1
    have e : 1 / (2 * Real.pi) * (1 / κ / Real.sqrt 1) * Real.log (1 / (1 / κ))
        = 1 / (2 * Real.pi) * (Real.log κ / κ) := by
      rw [Real.sqrt_one, div_one, one_div_one_div]
      ring
    rw [e] at h
    exact h
  exact max_le hkey1 hkey2

/-- Label `cor:app-os-twolevel`, part (iii). Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Two-level spectrum]\label{cor:app-os-twolevel}
Let $\nu_{p,\varkappa}\defeq(1-p)\delta_1+p\,\delta_{1/\varkappa}$ with $p\in(0,1)$ and
$\varkappa\ge2$, write $\mathfrak d^{\rm os}=\mathfrak d^{\rm os}_{\nu_{p,\varkappa}}$, and put
\[
\Omega_{p,\varkappa}\defeq\max\Big\{\sqrt{\frac p\varkappa},\ \frac{\log\varkappa}{\varkappa}\Big\},\qquad
c_{\rm hi}\defeq\frac2{C_*}\Big(\frac1{\sqrt2}+\frac{\sqrt2}{\pi}\,\frac{\log3+2}{\log2}\Big)\le5.78 .
\]
Then
\[
\begin{gathered}
\mathfrak d^{\rm os}(1)\in\Big[\frac{C_*}2,\frac1{\sqrt2}\Big],\\
\max\Big\{\frac{C_*}2\sqrt{\frac p\varkappa},\ \frac1{2\pi}\frac{\log\varkappa}\varkappa\Big\}
\le\mathfrak d^{\rm os}(1/\varkappa)\le\sqrt{\frac{p}{2\varkappa}}+\frac{\sqrt2}{\pi}\,\frac{\log(1+\varkappa)+2}{\varkappa},
\end{gathered}
\]
and consequently
\[
\frac{\Omega_{p,\varkappa}}{\sqrt2\,\pi}\le\frac{\mathfrak d^{\rm os}(1/\varkappa)}{\mathfrak d^{\rm os}(1)}\le c_{\rm hi}\,\Omega_{p,\varkappa}.
\]
\end{corollary}
-/
theorem cor_app_os_twolevel_iii {p κ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hκ : 2 ≤ κ) :
    dOsSq (nuTL p κ) (1 / κ)
      ≤ Real.sqrt (p / (2 * κ)) + Real.sqrt 2 / Real.pi * ((Real.log (1 + κ) + 2) / κ) := by
  haveI := tl_isProb (p := p) (κ := κ) hp0 hp1
  have hκ0 : (0:ℝ) < κ := by linarith
  have hκne : κ ≠ 0 := hκ0.ne'
  have hμ : (0:ℝ) < 1 / κ := one_div_pos.mpr hκ0
  have hν : nuTL p κ (Iio 0) = 0 := tl_Iio (p := p) hκ
  have hfin : tailInt (nuTL p κ) (1 / κ) < ⊤ := by
    rw [tl_tail hκ]
    exact ENNReal.ofReal_lt_top
  have hd := prop_app_os_tail_i (nuTL p κ) hν hμ (ℓ := 1 / κ) hμ.le hfin
  rw [tl_Icc_k hp1 hκ, ENNReal.toReal_ofReal hp0.le, tl_tail hκ,
    ENNReal.toReal_ofReal (show (0:ℝ) ≤ 1 - p by linarith)] at hd
  have hmono := lem_app_os_tailint_i (1 / κ) hμ (Γ₁ := 1 - p) (Γ₂ := 1)
    (by linarith) (by linarith)
  have hiii := lem_app_os_tailint_iii (1 / κ) hμ (Γ := 1) one_pos
  have e1 : Real.sqrt p * Real.sqrt (1 / κ / 2) = Real.sqrt (p / (2 * κ)) := by
    rw [← Real.sqrt_mul hp0.le]
    congr 1
    field_simp
  have e2 : Real.sqrt 2 / Real.pi * Real.sqrt 1 * (1 / κ) * (Real.log (1 + 1 / (1 / κ * 1)) + 2)
      = Real.sqrt 2 / Real.pi * ((Real.log (1 + κ) + 2) / κ) := by
    simp only [Real.sqrt_one, mul_one, one_div_one_div]
    ring
  linarith

/-- Label `cor:app-os-twolevel`, part (iv), the ratio bounds. Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Two-level spectrum]\label{cor:app-os-twolevel}
Let $\nu_{p,\varkappa}\defeq(1-p)\delta_1+p\,\delta_{1/\varkappa}$ with $p\in(0,1)$ and
$\varkappa\ge2$, write $\mathfrak d^{\rm os}=\mathfrak d^{\rm os}_{\nu_{p,\varkappa}}$, and put
\[
\Omega_{p,\varkappa}\defeq\max\Big\{\sqrt{\frac p\varkappa},\ \frac{\log\varkappa}{\varkappa}\Big\},\qquad
c_{\rm hi}\defeq\frac2{C_*}\Big(\frac1{\sqrt2}+\frac{\sqrt2}{\pi}\,\frac{\log3+2}{\log2}\Big)\le5.78 .
\]
Then
\[
\begin{gathered}
\mathfrak d^{\rm os}(1)\in\Big[\frac{C_*}2,\frac1{\sqrt2}\Big],\\
\max\Big\{\frac{C_*}2\sqrt{\frac p\varkappa},\ \frac1{2\pi}\frac{\log\varkappa}\varkappa\Big\}
\le\mathfrak d^{\rm os}(1/\varkappa)\le\sqrt{\frac{p}{2\varkappa}}+\frac{\sqrt2}{\pi}\,\frac{\log(1+\varkappa)+2}{\varkappa},
\end{gathered}
\]
and consequently
\[
\frac{\Omega_{p,\varkappa}}{\sqrt2\,\pi}\le\frac{\mathfrak d^{\rm os}(1/\varkappa)}{\mathfrak d^{\rm os}(1)}\le c_{\rm hi}\,\Omega_{p,\varkappa}.
\]
\end{corollary}
-/
theorem cor_app_os_twolevel_iv {p κ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hκ : 2 ≤ κ) :
    omegaTL p κ / (Real.sqrt 2 * Real.pi) ≤ dOsSq (nuTL p κ) (1 / κ) / dOsSq (nuTL p κ) 1 ∧
      dOsSq (nuTL p κ) (1 / κ) / dOsSq (nuTL p κ) 1 ≤ cHi * omegaTL p κ := by
  have hκ0 : (0:ℝ) < κ := by linarith
  have hκne : κ ≠ 0 := hκ0.ne'
  have hk1 := cor_app_os_twolevel_i hp0 hp1 hκ
  have hk2 := cor_app_os_twolevel_ii hp0 hp1 hκ
  have hk3 := cor_app_os_twolevel_iii hp0 hp1 hκ
  have hcS0 : 0 < cStar := tl_cStar_pos
  have hcSh : 1 / 2 ≤ cStar := by
    unfold cStar
    have h1 := Real.log_pos (by norm_num : (1:ℝ) < 2)
    have h2 : 0 < 2 * Real.log 2 / Real.pi := div_pos (by linarith) Real.pi_pos
    linarith
  have hd1lo := hk1.1
  have hd1hi := hk1.2
  have hd1pos : 0 < dOsSq (nuTL p κ) 1 := lt_of_lt_of_le (by linarith) hd1lo
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hpi := Real.pi_pos
  have hpi3 : 3 ≤ Real.pi := Real.pi_gt_three.le
  have ha0 : 0 ≤ Real.sqrt (p / κ) := Real.sqrt_nonneg _
  have hlogk : 0 < Real.log κ := Real.log_pos (by linarith)
  have hb0 : 0 ≤ Real.log κ / κ := div_nonneg hlogk.le hκ0.le
  have hΩ0 : 0 ≤ omegaTL p κ := by
    unfold omegaTL
    exact le_max_of_le_left ha0
  have hA : Real.sqrt (p / κ) ≤ 2 * Real.pi * dOsSq (nuTL p κ) (1 / κ) := by
    have h : cStar / 2 * Real.sqrt (p / κ) ≤ dOsSq (nuTL p κ) (1 / κ) :=
      le_trans (le_max_left _ _) hk2
    have h1 := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 2 * Real.pi)
    have hpc : 1 ≤ Real.pi * cStar := by nlinarith
    have h2 : Real.sqrt (p / κ) ≤ Real.pi * cStar * Real.sqrt (p / κ) :=
      le_mul_of_one_le_left ha0 hpc
    nlinarith
  have hB : Real.log κ / κ ≤ 2 * Real.pi * dOsSq (nuTL p κ) (1 / κ) := by
    have h : 1 / (2 * Real.pi) * (Real.log κ / κ) ≤ dOsSq (nuTL p κ) (1 / κ) :=
      le_trans (le_max_right _ _) hk2
    have h1 := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 2 * Real.pi)
    have e : 2 * Real.pi * (1 / (2 * Real.pi) * (Real.log κ / κ)) = Real.log κ / κ := by
      field_simp
    linarith
  have hΩle : omegaTL p κ ≤ 2 * Real.pi * dOsSq (nuTL p κ) (1 / κ) := by
    unfold omegaTL
    exact max_le hA hB
  have hlow : omegaTL p κ / (Real.sqrt 2 * Real.pi)
      ≤ dOsSq (nuTL p κ) (1 / κ) / dOsSq (nuTL p κ) 1 := by
    rw [div_le_div_iff₀ (by positivity) hd1pos]
    have hd1s : dOsSq (nuTL p κ) 1 * Real.sqrt 2 ≤ 1 := (le_div_iff₀ hs0).mp hd1hi
    have key : omegaTL p κ * dOsSq (nuTL p κ) 1 * Real.sqrt 2
        ≤ (dOsSq (nuTL p κ) (1 / κ) * (Real.sqrt 2 * Real.pi)) * Real.sqrt 2 := by
      calc omegaTL p κ * dOsSq (nuTL p κ) 1 * Real.sqrt 2
          = omegaTL p κ * (dOsSq (nuTL p κ) 1 * Real.sqrt 2) := by ring
        _ ≤ omegaTL p κ * 1 := mul_le_mul_of_nonneg_left hd1s hΩ0
        _ = omegaTL p κ := mul_one _
        _ ≤ 2 * Real.pi * dOsSq (nuTL p κ) (1 / κ) := hΩle
        _ = (Real.sqrt 2 * Real.sqrt 2) * Real.pi * dOsSq (nuTL p κ) (1 / κ) := by rw [hs2]
        _ = (dOsSq (nuTL p κ) (1 / κ) * (Real.sqrt 2 * Real.pi)) * Real.sqrt 2 := by ring
    exact le_of_mul_le_mul_right key hs0
  have hupp : dOsSq (nuTL p κ) (1 / κ) / dOsSq (nuTL p κ) 1 ≤ cHi * omegaTL p κ := by
    rw [div_le_iff₀ hd1pos]
    have hR0 : 0 ≤ (Real.log 3 + 2) / Real.log 2 := by
      have h3 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)
      have h2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
      exact div_nonneg (by linarith) h2.le
    have hK0 : 0 ≤ 1 / Real.sqrt 2 + Real.sqrt 2 / Real.pi * ((Real.log 3 + 2) / Real.log 2) := by
      have : 0 ≤ Real.sqrt 2 / Real.pi := div_nonneg hs0.le hpi.le
      have h5 : 0 ≤ 1 / Real.sqrt 2 := one_div_nonneg.mpr hs0.le
      have h6 := mul_nonneg this hR0
      linarith
    have hcH : cHi * (cStar / 2)
        = 1 / Real.sqrt 2 + Real.sqrt 2 / Real.pi * ((Real.log 3 + 2) / Real.log 2) := by
      unfold cHi
      field_simp
    have hcHnn : 0 ≤ cHi := by
      unfold cHi
      exact mul_nonneg (div_nonneg two_pos.le hcS0.le) hK0
    have hR_b : (Real.log (1 + κ) + 2) / κ ≤ (Real.log 3 + 2) / Real.log 2 * (Real.log κ / κ) := by
      have e4 : (Real.log (1 + κ) + 2) / κ
          = (Real.log (1 + κ) + 2) / Real.log κ * (Real.log κ / κ) := by
        field_simp
      rw [e4]
      exact mul_le_mul_of_nonneg_right (twolevel_log_ratio_le hκ) hb0
    have e3 : Real.sqrt (p / (2 * κ)) = Real.sqrt (p / κ) * (1 / Real.sqrt 2) := by
      rw [show p / (2 * κ) = p / κ * (1 / 2) by field_simp, Real.sqrt_mul (div_nonneg hp0.le hκ0.le),
        tl_sqrt_half]
    have h7 : Real.sqrt 2 / Real.pi * ((Real.log (1 + κ) + 2) / κ)
        ≤ Real.sqrt 2 / Real.pi * ((Real.log 3 + 2) / Real.log 2 * (Real.log κ / κ)) :=
      mul_le_mul_of_nonneg_left hR_b (div_nonneg hs0.le hpi.le)
    have hbΩ : Real.log κ / κ ≤ omegaTL p κ := by
      unfold omegaTL
      exact le_max_right _ _
    have haΩ : Real.sqrt (p / κ) ≤ omegaTL p κ := by
      unfold omegaTL
      exact le_max_left _ _
    have h8 : Real.sqrt 2 / Real.pi * ((Real.log 3 + 2) / Real.log 2 * (Real.log κ / κ))
        ≤ Real.sqrt 2 / Real.pi * ((Real.log 3 + 2) / Real.log 2 * omegaTL p κ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbΩ hR0) (div_nonneg hs0.le hpi.le)
    have h9 : Real.sqrt (p / κ) * (1 / Real.sqrt 2) ≤ omegaTL p κ * (1 / Real.sqrt 2) :=
      mul_le_mul_of_nonneg_right haΩ (one_div_nonneg.mpr hs0.le)
    have hdk : dOsSq (nuTL p κ) (1 / κ)
        ≤ (1 / Real.sqrt 2 + Real.sqrt 2 / Real.pi * ((Real.log 3 + 2) / Real.log 2))
          * omegaTL p κ := by
      rw [e3] at hk3
      nlinarith [hk3, h7, h8, h9]
    have hco : 0 ≤ cHi * omegaTL p κ := mul_nonneg hcHnn hΩ0
    have hcomb : (1 / Real.sqrt 2 + Real.sqrt 2 / Real.pi * ((Real.log 3 + 2) / Real.log 2))
          * omegaTL p κ ≤ cHi * omegaTL p κ * dOsSq (nuTL p κ) 1 := by
      calc (1 / Real.sqrt 2 + Real.sqrt 2 / Real.pi * ((Real.log 3 + 2) / Real.log 2))
            * omegaTL p κ = cHi * (cStar / 2) * omegaTL p κ := by rw [hcH]
        _ = cHi * omegaTL p κ * (cStar / 2) := by ring
        _ ≤ cHi * omegaTL p κ * dOsSq (nuTL p κ) 1 := mul_le_mul_of_nonneg_left hd1lo hco
    linarith
  exact ⟨hlow, hupp⟩

/-- Label `cor:app-os-twolevel`, the numerical claim `c_hi ≤ 5.78`, as its own declaration (card §6.13). Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Two-level spectrum]\label{cor:app-os-twolevel}
Let $\nu_{p,\varkappa}\defeq(1-p)\delta_1+p\,\delta_{1/\varkappa}$ with $p\in(0,1)$ and
$\varkappa\ge2$, write $\mathfrak d^{\rm os}=\mathfrak d^{\rm os}_{\nu_{p,\varkappa}}$, and put
\[
\Omega_{p,\varkappa}\defeq\max\Big\{\sqrt{\frac p\varkappa},\ \frac{\log\varkappa}{\varkappa}\Big\},\qquad
c_{\rm hi}\defeq\frac2{C_*}\Big(\frac1{\sqrt2}+\frac{\sqrt2}{\pi}\,\frac{\log3+2}{\log2}\Big)\le5.78 .
\]
Then
\[
\begin{gathered}
\mathfrak d^{\rm os}(1)\in\Big[\frac{C_*}2,\frac1{\sqrt2}\Big],\\
\max\Big\{\frac{C_*}2\sqrt{\frac p\varkappa},\ \frac1{2\pi}\frac{\log\varkappa}\varkappa\Big\}
\le\mathfrak d^{\rm os}(1/\varkappa)\le\sqrt{\frac{p}{2\varkappa}}+\frac{\sqrt2}{\pi}\,\frac{\log(1+\varkappa)+2}{\varkappa},
\end{gathered}
\]
and consequently
\[
\frac{\Omega_{p,\varkappa}}{\sqrt2\,\pi}\le\frac{\mathfrak d^{\rm os}(1/\varkappa)}{\mathfrak d^{\rm os}(1)}\le c_{\rm hi}\,\Omega_{p,\varkappa}.
\]
\end{corollary}
-/
theorem cor_app_os_twolevel_c_hi_le : cHi ≤ 5.78 := by
  unfold cHi cStar
  have hL : (0.69314718:ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hpiL : (3.141592:ℝ) < Real.pi := Real.pi_gt_d6
  have hpiU : Real.pi < 3.141593 := Real.pi_lt_d6
  have hpi0 : 0 < Real.pi := by linarith
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs2L : (1.41421:ℝ) < Real.sqrt 2 := by nlinarith
  have hs2U : Real.sqrt 2 < 1.41422 := by nlinarith
  have hT : Real.log 3 ≤ 1.0988 := log_three_le
  have hL0 : 0 < Real.log 2 := by linarith
  -- C_* ≥ 0.94127
  have hC : (0.94127:ℝ) ≤ 1 / 2 + 2 * Real.log 2 / Real.pi := by
    have h2 : (0.44127:ℝ) ≤ 2 * Real.log 2 / Real.pi := by
      rw [le_div_iff₀ hpi0]; nlinarith
    linarith
  have hCpos : 0 < 1 / 2 + 2 * Real.log 2 / Real.pi := by linarith
  have hfac : 2 / (1 / 2 + 2 * Real.log 2 / Real.pi) ≤ 2.1248 := by
    rw [div_le_iff₀ hCpos]; linarith
  -- 1/√2 ≤ 0.70711
  have hX : 1 / Real.sqrt 2 ≤ 0.70711 := by
    rw [div_le_iff₀ hs0]; linarith
  -- √2/π ≤ 0.450161
  have hY : Real.sqrt 2 / Real.pi ≤ 0.450161 := by
    rw [div_le_iff₀ hpi0]; nlinarith
  have hY0 : 0 ≤ Real.sqrt 2 / Real.pi := by positivity
  -- A = (log 3 + 2)/log 2 ≤ 4.4707
  have hA : (Real.log 3 + 2) / Real.log 2 ≤ 4.4707 := by
    rw [div_le_iff₀ hL0]; linarith
  have hA0 : 0 ≤ (Real.log 3 + 2) / Real.log 2 := by
    apply div_nonneg _ hL0.le
    have := Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num); linarith
  have hYA : Real.sqrt 2 / Real.pi * ((Real.log 3 + 2) / Real.log 2) ≤ 0.450161 * 4.4707 :=
    mul_le_mul hY hA hA0 (by norm_num)
  have hin : 1 / Real.sqrt 2 + Real.sqrt 2 / Real.pi * ((Real.log 3 + 2) / Real.log 2)
      ≤ 2.7196448 := by
    linarith
  have hin0 : 0 ≤ 1 / Real.sqrt 2 + Real.sqrt 2 / Real.pi * ((Real.log 3 + 2) / Real.log 2) := by
    have := mul_nonneg hY0 hA0
    have : 0 < 1 / Real.sqrt 2 := by positivity
    linarith
  have hfin := mul_le_mul hfac hin hin0 (by norm_num)
  have hnum : (2.1248:ℝ) * 2.7196448 ≤ 5.78 := by norm_num
  linarith

/-! ## Acceleration of a slow mode (`cor:app-os-accel`) -/

/-- Label `cor:app-os-accel`, definition of the acceleration `𝒜`. Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Acceleration of a slow mode]\label{cor:app-os-accel}
Let $\nu$ be a probability measure with $\nu([0,\mu_+])=1$ for some $\mu_+>0$,
and let $0<\mu\le\mu_+/2$.
\begin{enumerate}[label=(\roman*)]
\item One has
\[
\chi_\nu(\mu)\sqrt\varkappa\le\mathcal A\le\frac{\sqrt2}{C_*}\,\chi_\nu(\mu)\sqrt\varkappa .
\]
\item One has
\[
\frac{1}{\sqrt2\,\pi}\log\varkappa\le\mathcal A\le\frac{\sqrt2}{C_*}\sqrt\varkappa .
\]
\item For every $K>0$,
\[
C_*\sqrt{\frac{\nu([0,K\mu])}{1+K}}\,\sqrt\varkappa\le\mathcal A
\le\frac{\sqrt2}{C_*}\Big[\sqrt{\nu([0,K\mu])}+\frac{2(\log(1+K)+2)}{\pi\sqrt K}\Big]\sqrt\varkappa .
\]
\item If $\nu(\{0\})=0$ and $\mu_+\mathcal I_\nu\le\Gamma<\infty$, then
\[
\mathcal A\le\frac{2\sqrt2}{\pi C_*}\sqrt\Gamma\,\big[\log(1+\varkappa)+2\big].
\]
\item For the two-level spectrum of \cref{cor:app-os-twolevel}, with $\mu_+=1$ and
$\mu=1/\varkappa$,
\[
\frac{1}{\sqrt2\,\pi}\max\big\{\sqrt{p\varkappa},\ \log\varkappa\big\}\le\mathcal A\le c_{\rm hi}\max\big\{\sqrt{p\varkappa},\ \log\varkappa\big\}.
\]
\item Along sequences $(\nu_N,\mu_{+,N},\mu_N)$ satisfying the hypotheses, with
acceleration $\mathcal A_N$ and ratio $\varkappa_N$, one has
$\liminf_N\mathcal A_N/\sqrt{\varkappa_N}>0$ if and only if
$\liminf_N\nu_N([0,K\mu_N])>0$ for some $K>0$.
\end{enumerate}
\end{corollary}
-/
def accelA (ν : Measure ℝ) (μp μ : ℝ) : ℝ :=
  (dOsSq ν μ / dOsSq ν μp) / (μ / μp)

/-! ### Private helpers for `cor:app-os-accel` (fully proved) -/

private lemma ac_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μp μ : ℝ} (hμp : 0 < μp) (hμ : 0 < μ) (hb : sqrtEff ν μp ≠ 0) :
    accelA ν μp μ = sqrtEff ν μ / sqrtEff ν μp * Real.sqrt (μp / μ) := by
  unfold accelA
  rw [lem_app_os_repr_ii ν hν hμ, lem_app_os_repr_ii ν hν hμp]
  have hμ0 : μ ≠ 0 := hμ.ne'
  have hμp0 : μp ≠ 0 := hμp.ne'
  have hS : Real.sqrt (μp / μ) = Real.sqrt (μp / 2) / Real.sqrt (μ / 2) := by
    rw [← Real.sqrt_div (by linarith : (0:ℝ) ≤ μp / 2) (μ / 2)]
    congr 1
    field_simp
  have hμr : μ / μp = (Real.sqrt (μ / 2)) ^ 2 / (Real.sqrt (μp / 2)) ^ 2 := by
    rw [Real.sq_sqrt (by linarith : (0:ℝ) ≤ μ / 2), Real.sq_sqrt (by linarith : (0:ℝ) ≤ μp / 2)]
    field_simp
  have hr : Real.sqrt (μ / 2) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hq : Real.sqrt (μp / 2) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  rw [hS, hμr]
  field_simp

private lemma ac_b_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μp : ℝ} (hsupp : ν (Icc 0 μp) = 1) (hμp : 0 < μp) :
    cStar / Real.sqrt 2 ≤ sqrtEff ν μp ∧ 0 < sqrtEff ν μp ∧ sqrtEff ν μp ≤ 1 := by
  have hE := lem_app_os_repr_iii ν hν hμp
  have hs := thm_app_os_sqrt_ii ν hν (μ := μp) (K := 1) hμp one_pos
  have h1 : (ν (Icc 0 μp)).toReal = 1 := by rw [hsupp, ENNReal.toReal_one]
  have hs2 := hs.2
  rw [h1] at hs2
  have h2 : (1:ℝ) / 2 ≤ 1 - mNu ν μp := by linarith
  have hC := chi_ge_Cstar_sqrt ν hν hμp
  have h3 : Real.sqrt (1 / 2) ≤ Real.sqrt (1 - mNu ν μp) := Real.sqrt_le_sqrt h2
  rw [tl_sqrt_half] at h3
  have hc := tl_cStar_pos
  have hdpos : 0 < cStar / Real.sqrt 2 := div_pos hc (Real.sqrt_pos.2 (by norm_num))
  have h4 : cStar / Real.sqrt 2 ≤ cStar * Real.sqrt (1 - mNu ν μp) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left h3 hc.le
  exact ⟨by linarith, by linarith, hE.2⟩

private lemma ac_div_le {a b : ℝ} (ha : 0 ≤ a) (hdiv : cStar / Real.sqrt 2 ≤ b) (hb : 0 < b) :
    a / b ≤ Real.sqrt 2 / cStar * a := by
  have hc := tl_cStar_pos
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hcb : cStar ≤ b * Real.sqrt 2 := (div_le_iff₀ h2).1 hdiv
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hb hc]
  nlinarith [mul_le_mul_of_nonneg_left hcb ha]

private lemma ac_alg (P Q W ℓ a : ℝ) (hP : 0 < P) (hQ : 0 < Q) (hW : 0 < W) (hWW : W * W = 2)
    (hL : 1 / (2 * Real.pi) * (P ^ 2 / Q) * ℓ ≤ P / W * a) :
    1 / (W * Real.pi) * ℓ ≤ a * (Q / P) := by
  have hk : 0 < W * Q / P := div_pos (mul_pos hW hQ) hP
  have h1 := mul_le_mul_of_nonneg_right hL hk.le
  have hP0 : P ≠ 0 := hP.ne'
  have hW0 : W ≠ 0 := hW.ne'
  have hQ0 : Q ≠ 0 := hQ.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have e1 : 1 / (2 * Real.pi) * (P ^ 2 / Q) * ℓ * (W * Q / P) = W * P * ℓ / (2 * Real.pi) := by
    field_simp
  have e2 : P / W * a * (W * Q / P) = a * Q := by
    field_simp
  rw [e1, e2] at h1
  have e3 : 1 / (W * Real.pi) = W / (2 * Real.pi) := by
    rw [div_eq_div_iff (mul_pos hW Real.pi_pos).ne' (mul_pos two_pos Real.pi_pos).ne']
    linear_combination (-Real.pi) * hWW
  have e4 : a * (Q / P) = a * Q / P := by ring
  have e5 : W / (2 * Real.pi) * ℓ = W * P * ℓ / (2 * Real.pi) / P := by
    field_simp
  rw [e3, e4, e5]
  exact div_le_div_of_nonneg_right h1 hP.le

private lemma ac_iv_alg (μ P W J M a : ℝ) (hPμ : P * P = μ) (hP : 0 < P) (hW : 0 < W)
    (hWW : W * W = 2) (h : P / W * a ≤ W / Real.pi * J * μ * M) :
    a ≤ 2 * J * P * M / Real.pi := by
  subst hPμ
  have hP0 : P ≠ 0 := hP.ne'
  have hW0 : W ≠ 0 := hW.ne'
  have h1 := mul_le_mul_of_nonneg_right h (div_pos hW hP).le
  have e1 : P / W * a * (W / P) = a := by
    field_simp
  have e2 : W / Real.pi * J * (P * P) * M * (W / P) = W * W * J * P * M / Real.pi := by
    field_simp
  rw [e1, e2, hWW] at h1
  linarith


/-- Label `cor:app-os-accel`, part (i). Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Acceleration of a slow mode]\label{cor:app-os-accel}
Let $\nu$ be a probability measure with $\nu([0,\mu_+])=1$ for some $\mu_+>0$,
and let $0<\mu\le\mu_+/2$.
\begin{enumerate}[label=(\roman*)]
\item One has
\[
\chi_\nu(\mu)\sqrt\varkappa\le\mathcal A\le\frac{\sqrt2}{C_*}\,\chi_\nu(\mu)\sqrt\varkappa .
\]
\item One has
\[
\frac{1}{\sqrt2\,\pi}\log\varkappa\le\mathcal A\le\frac{\sqrt2}{C_*}\sqrt\varkappa .
\]
\item For every $K>0$,
\[
C_*\sqrt{\frac{\nu([0,K\mu])}{1+K}}\,\sqrt\varkappa\le\mathcal A
\le\frac{\sqrt2}{C_*}\Big[\sqrt{\nu([0,K\mu])}+\frac{2(\log(1+K)+2)}{\pi\sqrt K}\Big]\sqrt\varkappa .
\]
\item If $\nu(\{0\})=0$ and $\mu_+\mathcal I_\nu\le\Gamma<\infty$, then
\[
\mathcal A\le\frac{2\sqrt2}{\pi C_*}\sqrt\Gamma\,\big[\log(1+\varkappa)+2\big].
\]
\item For the two-level spectrum of \cref{cor:app-os-twolevel}, with $\mu_+=1$ and
$\mu=1/\varkappa$,
\[
\frac{1}{\sqrt2\,\pi}\max\big\{\sqrt{p\varkappa},\ \log\varkappa\big\}\le\mathcal A\le c_{\rm hi}\max\big\{\sqrt{p\varkappa},\ \log\varkappa\big\}.
\]
\item Along sequences $(\nu_N,\mu_{+,N},\mu_N)$ satisfying the hypotheses, with
acceleration $\mathcal A_N$ and ratio $\varkappa_N$, one has
$\liminf_N\mathcal A_N/\sqrt{\varkappa_N}>0$ if and only if
$\liminf_N\nu_N([0,K\mu_N])>0$ for some $K>0$.
\end{enumerate}
\end{corollary}
-/
theorem cor_app_os_accel_i (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μp μ : ℝ} (hsupp : ν (Icc 0 μp) = 1) (hμp : 0 < μp) (hμ : 0 < μ) (hμle : μ ≤ μp / 2) :
    sqrtEff ν μ * Real.sqrt (μp / μ) ≤ accelA ν μp μ ∧
      accelA ν μp μ ≤ Real.sqrt 2 / cStar * sqrtEff ν μ * Real.sqrt (μp / μ) := by
  obtain ⟨hdiv, hbpos, hb1⟩ := ac_b_bounds ν hν hsupp hμp
  have hEμ := lem_app_os_repr_iii ν hν hμ
  have ha : 0 ≤ sqrtEff ν μ := hEμ.1.le
  have hS : 0 ≤ Real.sqrt (μp / μ) := Real.sqrt_nonneg _
  have hA1 : sqrtEff ν μ ≤ sqrtEff ν μ / sqrtEff ν μp := by
    rw [le_div_iff₀ hbpos]; nlinarith
  have hA2 : sqrtEff ν μ / sqrtEff ν μp ≤ Real.sqrt 2 / cStar * sqrtEff ν μ :=
    ac_div_le ha hdiv hbpos
  rw [ac_eq ν hν hμp hμ hbpos.ne']
  exact ⟨mul_le_mul_of_nonneg_right hA1 hS, mul_le_mul_of_nonneg_right hA2 hS⟩

/-- Label `cor:app-os-accel`, part (ii). Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Acceleration of a slow mode]\label{cor:app-os-accel}
Let $\nu$ be a probability measure with $\nu([0,\mu_+])=1$ for some $\mu_+>0$,
and let $0<\mu\le\mu_+/2$.
\begin{enumerate}[label=(\roman*)]
\item One has
\[
\chi_\nu(\mu)\sqrt\varkappa\le\mathcal A\le\frac{\sqrt2}{C_*}\,\chi_\nu(\mu)\sqrt\varkappa .
\]
\item One has
\[
\frac{1}{\sqrt2\,\pi}\log\varkappa\le\mathcal A\le\frac{\sqrt2}{C_*}\sqrt\varkappa .
\]
\item For every $K>0$,
\[
C_*\sqrt{\frac{\nu([0,K\mu])}{1+K}}\,\sqrt\varkappa\le\mathcal A
\le\frac{\sqrt2}{C_*}\Big[\sqrt{\nu([0,K\mu])}+\frac{2(\log(1+K)+2)}{\pi\sqrt K}\Big]\sqrt\varkappa .
\]
\item If $\nu(\{0\})=0$ and $\mu_+\mathcal I_\nu\le\Gamma<\infty$, then
\[
\mathcal A\le\frac{2\sqrt2}{\pi C_*}\sqrt\Gamma\,\big[\log(1+\varkappa)+2\big].
\]
\item For the two-level spectrum of \cref{cor:app-os-twolevel}, with $\mu_+=1$ and
$\mu=1/\varkappa$,
\[
\frac{1}{\sqrt2\,\pi}\max\big\{\sqrt{p\varkappa},\ \log\varkappa\big\}\le\mathcal A\le c_{\rm hi}\max\big\{\sqrt{p\varkappa},\ \log\varkappa\big\}.
\]
\item Along sequences $(\nu_N,\mu_{+,N},\mu_N)$ satisfying the hypotheses, with
acceleration $\mathcal A_N$ and ratio $\varkappa_N$, one has
$\liminf_N\mathcal A_N/\sqrt{\varkappa_N}>0$ if and only if
$\liminf_N\nu_N([0,K\mu_N])>0$ for some $K>0$.
\end{enumerate}
\end{corollary}
-/
theorem cor_app_os_accel_ii (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μp μ : ℝ} (hsupp : ν (Icc 0 μp) = 1) (hμp : 0 < μp) (hμ : 0 < μ) (hμle : μ ≤ μp / 2) :
    1 / (Real.sqrt 2 * Real.pi) * Real.log (μp / μ) ≤ accelA ν μp μ ∧
      accelA ν μp μ ≤ Real.sqrt 2 / cStar * Real.sqrt (μp / μ) := by
  obtain ⟨hdiv, hbpos, hb1⟩ := ac_b_bounds ν hν hsupp hμp
  have hEμ := lem_app_os_repr_iii ν hν hμ
  have ha : 0 ≤ sqrtEff ν μ := hEμ.1.le
  have hS : 0 ≤ Real.sqrt (μp / μ) := Real.sqrt_nonneg _
  have hG : 0 ≤ Real.sqrt 2 / cStar := div_nonneg (Real.sqrt_nonneg _) tl_cStar_pos.le
  have hA1 : sqrtEff ν μ ≤ sqrtEff ν μ / sqrtEff ν μp := by
    rw [le_div_iff₀ hbpos]; nlinarith
  have hA2 : sqrtEff ν μ / sqrtEff ν μp ≤ Real.sqrt 2 / cStar * sqrtEff ν μ :=
    ac_div_le ha hdiv hbpos
  have hT := prop_app_os_tail_v ν hν hμ hμp hsupp
  have hL := hT.2.trans hT.1
  rw [lem_app_os_repr_ii ν hν hμ] at hL
  have eμ : μ / Real.sqrt μp = (Real.sqrt μ) ^ 2 / Real.sqrt μp := by
    rw [Real.sq_sqrt hμ.le]
  have e2 : Real.sqrt (μ / 2) = Real.sqrt μ / Real.sqrt 2 := Real.sqrt_div hμ.le 2
  have eS : Real.sqrt (μp / μ) = Real.sqrt μp / Real.sqrt μ := Real.sqrt_div hμp.le μ
  rw [eμ, e2] at hL
  have hkey := ac_alg (Real.sqrt μ) (Real.sqrt μp) (Real.sqrt 2) (Real.log (μp / μ))
    (sqrtEff ν μ) (Real.sqrt_pos.2 hμ) (Real.sqrt_pos.2 hμp) (Real.sqrt_pos.2 (by norm_num))
    (Real.mul_self_sqrt (by norm_num)) hL
  rw [← eS] at hkey
  rw [ac_eq ν hν hμp hμ hbpos.ne']
  constructor
  · exact hkey.trans (mul_le_mul_of_nonneg_right hA1 hS)
  · exact mul_le_mul_of_nonneg_right (hA2.trans (mul_le_of_le_one_right hG hEμ.2)) hS

/-- Label `cor:app-os-accel`, part (iii). Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Acceleration of a slow mode]\label{cor:app-os-accel}
Let $\nu$ be a probability measure with $\nu([0,\mu_+])=1$ for some $\mu_+>0$,
and let $0<\mu\le\mu_+/2$.
\begin{enumerate}[label=(\roman*)]
\item One has
\[
\chi_\nu(\mu)\sqrt\varkappa\le\mathcal A\le\frac{\sqrt2}{C_*}\,\chi_\nu(\mu)\sqrt\varkappa .
\]
\item One has
\[
\frac{1}{\sqrt2\,\pi}\log\varkappa\le\mathcal A\le\frac{\sqrt2}{C_*}\sqrt\varkappa .
\]
\item For every $K>0$,
\[
C_*\sqrt{\frac{\nu([0,K\mu])}{1+K}}\,\sqrt\varkappa\le\mathcal A
\le\frac{\sqrt2}{C_*}\Big[\sqrt{\nu([0,K\mu])}+\frac{2(\log(1+K)+2)}{\pi\sqrt K}\Big]\sqrt\varkappa .
\]
\item If $\nu(\{0\})=0$ and $\mu_+\mathcal I_\nu\le\Gamma<\infty$, then
\[
\mathcal A\le\frac{2\sqrt2}{\pi C_*}\sqrt\Gamma\,\big[\log(1+\varkappa)+2\big].
\]
\item For the two-level spectrum of \cref{cor:app-os-twolevel}, with $\mu_+=1$ and
$\mu=1/\varkappa$,
\[
\frac{1}{\sqrt2\,\pi}\max\big\{\sqrt{p\varkappa},\ \log\varkappa\big\}\le\mathcal A\le c_{\rm hi}\max\big\{\sqrt{p\varkappa},\ \log\varkappa\big\}.
\]
\item Along sequences $(\nu_N,\mu_{+,N},\mu_N)$ satisfying the hypotheses, with
acceleration $\mathcal A_N$ and ratio $\varkappa_N$, one has
$\liminf_N\mathcal A_N/\sqrt{\varkappa_N}>0$ if and only if
$\liminf_N\nu_N([0,K\mu_N])>0$ for some $K>0$.
\end{enumerate}
\end{corollary}
-/
theorem cor_app_os_accel_iii (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μp μ : ℝ} (hsupp : ν (Icc 0 μp) = 1) (hμp : 0 < μp) (hμ : 0 < μ) (hμle : μ ≤ μp / 2) :
    ∀ K : ℝ, 0 < K →
      cStar * Real.sqrt ((ν (Icc 0 (K * μ))).toReal / (1 + K)) * Real.sqrt (μp / μ)
          ≤ accelA ν μp μ ∧
        accelA ν μp μ ≤ Real.sqrt 2 / cStar *
          (Real.sqrt (ν (Icc 0 (K * μ))).toReal + 2 * (Real.log (1 + K) + 2) / (Real.pi * Real.sqrt K)) *
            Real.sqrt (μp / μ) := by
  intro K hK
  obtain ⟨hdiv, hbpos, hb1⟩ := ac_b_bounds ν hν hsupp hμp
  have hEμ := lem_app_os_repr_iii ν hν hμ
  have ha : 0 ≤ sqrtEff ν μ := hEμ.1.le
  have hS : 0 ≤ Real.sqrt (μp / μ) := Real.sqrt_nonneg _
  have hG : 0 ≤ Real.sqrt 2 / cStar := div_nonneg (Real.sqrt_nonneg _) tl_cStar_pos.le
  have hA1 : sqrtEff ν μ ≤ sqrtEff ν μ / sqrtEff ν μp := by
    rw [le_div_iff₀ hbpos]; nlinarith
  have hA2 : sqrtEff ν μ / sqrtEff ν μp ≤ Real.sqrt 2 / cStar * sqrtEff ν μ :=
    ac_div_le ha hdiv hbpos
  have hT := prop_app_os_tail_iv ν hν hμ hK
  have hbr : sqrtEff ν μ ≤ Real.sqrt (ν (Icc 0 (K * μ))).toReal
      + 2 * (Real.log (1 + K) + 2) / (Real.pi * Real.sqrt K) := by
    have h := hT.2
    have e : 2 / (Real.pi * Real.sqrt K) * (Real.log (1 + K) + 2)
        = 2 * (Real.log (1 + K) + 2) / (Real.pi * Real.sqrt K) := by ring
    rw [e] at h
    exact h
  rw [ac_eq ν hν hμp hμ hbpos.ne']
  constructor
  · exact (mul_le_mul_of_nonneg_right hT.1 hS).trans (mul_le_mul_of_nonneg_right hA1 hS)
  · exact mul_le_mul_of_nonneg_right
      (hA2.trans (mul_le_mul_of_nonneg_left hbr hG)) hS

/-- Label `cor:app-os-accel`, part (iv). Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Acceleration of a slow mode]\label{cor:app-os-accel}
Let $\nu$ be a probability measure with $\nu([0,\mu_+])=1$ for some $\mu_+>0$,
and let $0<\mu\le\mu_+/2$.
\begin{enumerate}[label=(\roman*)]
\item One has
\[
\chi_\nu(\mu)\sqrt\varkappa\le\mathcal A\le\frac{\sqrt2}{C_*}\,\chi_\nu(\mu)\sqrt\varkappa .
\]
\item One has
\[
\frac{1}{\sqrt2\,\pi}\log\varkappa\le\mathcal A\le\frac{\sqrt2}{C_*}\sqrt\varkappa .
\]
\item For every $K>0$,
\[
C_*\sqrt{\frac{\nu([0,K\mu])}{1+K}}\,\sqrt\varkappa\le\mathcal A
\le\frac{\sqrt2}{C_*}\Big[\sqrt{\nu([0,K\mu])}+\frac{2(\log(1+K)+2)}{\pi\sqrt K}\Big]\sqrt\varkappa .
\]
\item If $\nu(\{0\})=0$ and $\mu_+\mathcal I_\nu\le\Gamma<\infty$, then
\[
\mathcal A\le\frac{2\sqrt2}{\pi C_*}\sqrt\Gamma\,\big[\log(1+\varkappa)+2\big].
\]
\item For the two-level spectrum of \cref{cor:app-os-twolevel}, with $\mu_+=1$ and
$\mu=1/\varkappa$,
\[
\frac{1}{\sqrt2\,\pi}\max\big\{\sqrt{p\varkappa},\ \log\varkappa\big\}\le\mathcal A\le c_{\rm hi}\max\big\{\sqrt{p\varkappa},\ \log\varkappa\big\}.
\]
\item Along sequences $(\nu_N,\mu_{+,N},\mu_N)$ satisfying the hypotheses, with
acceleration $\mathcal A_N$ and ratio $\varkappa_N$, one has
$\liminf_N\mathcal A_N/\sqrt{\varkappa_N}>0$ if and only if
$\liminf_N\nu_N([0,K\mu_N])>0$ for some $K>0$.
\end{enumerate}
\end{corollary}
-/
theorem cor_app_os_accel_iv (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μp μ Γ : ℝ} (hsupp : ν (Icc 0 μp) = 1) (hμp : 0 < μp) (hμ : 0 < μ) (hμle : μ ≤ μp / 2)
    (h0 : ν {0} = 0) (hΓ : ENNReal.ofReal μp * tailInt ν 0 ≤ ENNReal.ofReal Γ) :
    accelA ν μp μ ≤ 2 * Real.sqrt 2 / (Real.pi * cStar) * Real.sqrt Γ * (Real.log (1 + μp / μ) + 2) := by
  obtain ⟨hdiv, hbpos, hb1⟩ := ac_b_bounds ν hν hsupp hμp
  have hEμ := lem_app_os_repr_iii ν hν hμ
  have ha : 0 ≤ sqrtEff ν μ := hEμ.1.le
  have hS : 0 ≤ Real.sqrt (μp / μ) := Real.sqrt_nonneg _
  have hA2 := ac_div_le ha hdiv hbpos
  have hfin : tailInt ν 0 ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hμp).ne'] at hΓ
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hΓ)
  have hsup1 : (1 : ENNReal) ≤ ν (Ioc 0 μp) := by
    have hsub : Icc (0:ℝ) μp ⊆ Ioc 0 μp ∪ {0} := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with h | h
      · exact Or.inr h.symm
      · exact Or.inl ⟨h, hx.2⟩
    calc (1 : ENNReal) = ν (Icc 0 μp) := hsupp.symm
      _ ≤ ν (Ioc 0 μp ∪ {0}) := measure_mono hsub
      _ ≤ ν (Ioc 0 μp) + ν {0} := measure_union_le _ _
      _ = ν (Ioc 0 μp) := by rw [h0, add_zero]
  have hLow : ENNReal.ofReal μp⁻¹ ≤ tailInt ν 0 := by
    unfold tailInt
    calc ENNReal.ofReal μp⁻¹ = ENNReal.ofReal μp⁻¹ * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal μp⁻¹ * ν (Ioc 0 μp) := mul_le_mul_of_nonneg_left hsup1 (by simp)
      _ = ∫⁻ _ in Ioc 0 μp, ENNReal.ofReal μp⁻¹ ∂ν := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in Ioc 0 μp, ENNReal.ofReal x⁻¹ ∂ν := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact ENNReal.ofReal_le_ofReal (inv_anti₀ hx.1 hx.2)
      _ ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal x⁻¹ ∂ν := lintegral_mono_set Ioc_subset_Ioi_self
  have hI : μp⁻¹ ≤ (tailInt ν 0).toReal := (ENNReal.ofReal_le_iff_le_toReal hfin).1 hLow
  have hIpos : 0 < μp⁻¹ := inv_pos.2 hμp
  have hI0pos : 0 < (tailInt ν 0).toReal := lt_of_lt_of_le hIpos hI
  have hk : 1 ≤ μp * (tailInt ν 0).toReal := by
    have h := mul_le_mul_of_nonneg_left hI hμp.le
    rwa [mul_inv_cancel₀ hμp.ne'] at h
  have hΓr : μp * (tailInt ν 0).toReal ≤ Γ := by
    have e : ENNReal.ofReal μp * tailInt ν 0 = ENNReal.ofReal (μp * (tailInt ν 0).toReal) := by
      rw [ENNReal.ofReal_mul hμp.le, ENNReal.ofReal_toReal hfin]
    rw [e] at hΓ
    rcases ENNReal.ofReal_le_ofReal_iff'.1 hΓ with h | h
    · exact h
    · linarith
  have hT := prop_app_os_tail_ii ν hν h0 hμ (lt_top_iff_ne_top.2 hfin)
  have hpos1 : 0 < 1 / (μ * (tailInt ν 0).toReal) := div_pos one_pos (mul_pos hμ hI0pos)
  have hlog : Real.log (1 + 1 / (μ * (tailInt ν 0).toReal)) ≤ Real.log (1 + μp / μ) := by
    apply Real.log_le_log (by linarith)
    have h1 : 1 / (μ * (tailInt ν 0).toReal) ≤ μp / μ := by
      rw [div_le_div_iff₀ (mul_pos hμ hI0pos) hμ]
      nlinarith [mul_le_mul_of_nonneg_left hk hμ.le]
    linarith
  have hM0 : 0 ≤ Real.log (1 + 1 / (μ * (tailInt ν 0).toReal)) + 2 := by
    have := Real.log_nonneg (by linarith : (1:ℝ) ≤ 1 + 1 / (μ * (tailInt ν 0).toReal))
    linarith
  have e2 : Real.sqrt (μ / 2) = Real.sqrt μ / Real.sqrt 2 := Real.sqrt_div hμ.le 2
  rw [lem_app_os_repr_ii ν hν hμ, e2] at hT
  have hcore := ac_iv_alg μ (Real.sqrt μ) (Real.sqrt 2) (Real.sqrt (tailInt ν 0).toReal)
    (Real.log (1 + 1 / (μ * (tailInt ν 0).toReal)) + 2) (sqrtEff ν μ)
    (Real.mul_self_sqrt hμ.le) (Real.sqrt_pos.2 hμ) (Real.sqrt_pos.2 (by norm_num))
    (Real.mul_self_sqrt (by norm_num)) hT
  have eS : Real.sqrt (μp / μ) = Real.sqrt μp / Real.sqrt μ := Real.sqrt_div hμp.le μ
  have hPne : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.2 hμ).ne'
  have hcoreS : sqrtEff ν μ * Real.sqrt (μp / μ) ≤
      2 * Real.sqrt (tailInt ν 0).toReal * Real.sqrt μp
        * (Real.log (1 + 1 / (μ * (tailInt ν 0).toReal)) + 2) / Real.pi := by
    rw [eS]
    calc sqrtEff ν μ * (Real.sqrt μp / Real.sqrt μ)
        ≤ 2 * Real.sqrt (tailInt ν 0).toReal * Real.sqrt μ
            * (Real.log (1 + 1 / (μ * (tailInt ν 0).toReal)) + 2) / Real.pi
          * (Real.sqrt μp / Real.sqrt μ) :=
          mul_le_mul_of_nonneg_right hcore (by positivity)
      _ = 2 * Real.sqrt (tailInt ν 0).toReal * Real.sqrt μp
            * (Real.log (1 + 1 / (μ * (tailInt ν 0).toReal)) + 2) / Real.pi := by
          field_simp
  have hJQ : Real.sqrt (tailInt ν 0).toReal * Real.sqrt μp ≤ Real.sqrt Γ := by
    calc Real.sqrt (tailInt ν 0).toReal * Real.sqrt μp
        = Real.sqrt (μp * (tailInt ν 0).toReal) := by
          rw [Real.sqrt_mul hμp.le]; ring
      _ ≤ Real.sqrt Γ := Real.sqrt_le_sqrt hΓr
  have hK1 : 0 ≤ 2 * Real.sqrt 2 / (Real.pi * cStar) :=
    div_nonneg (by positivity) (mul_nonneg Real.pi_pos.le tl_cStar_pos.le)
  have hG : 0 ≤ Real.sqrt 2 / cStar := div_nonneg (Real.sqrt_nonneg _) tl_cStar_pos.le
  rw [ac_eq ν hν hμp hμ hbpos.ne']
  calc sqrtEff ν μ / sqrtEff ν μp * Real.sqrt (μp / μ)
      ≤ Real.sqrt 2 / cStar * sqrtEff ν μ * Real.sqrt (μp / μ) :=
        mul_le_mul_of_nonneg_right hA2 hS
    _ = Real.sqrt 2 / cStar * (sqrtEff ν μ * Real.sqrt (μp / μ)) := by ring
    _ ≤ Real.sqrt 2 / cStar * (2 * Real.sqrt (tailInt ν 0).toReal * Real.sqrt μp
            * (Real.log (1 + 1 / (μ * (tailInt ν 0).toReal)) + 2) / Real.pi) :=
          mul_le_mul_of_nonneg_left hcoreS hG
    _ = (2 * Real.sqrt 2 / (Real.pi * cStar)) * (Real.sqrt (tailInt ν 0).toReal * Real.sqrt μp)
          * (Real.log (1 + 1 / (μ * (tailInt ν 0).toReal)) + 2) := by ring
    _ ≤ (2 * Real.sqrt 2 / (Real.pi * cStar)) * Real.sqrt Γ
          * (Real.log (1 + 1 / (μ * (tailInt ν 0).toReal)) + 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJQ hK1) hM0
    _ ≤ (2 * Real.sqrt 2 / (Real.pi * cStar)) * Real.sqrt Γ * (Real.log (1 + μp / μ) + 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hK1 (Real.sqrt_nonneg _))

/-- Label `cor:app-os-accel`, part (v), two-level spectrum with `μ_+ = 1`, `μ = 1/κ`. Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Acceleration of a slow mode]\label{cor:app-os-accel}
Let $\nu$ be a probability measure with $\nu([0,\mu_+])=1$ for some $\mu_+>0$,
and let $0<\mu\le\mu_+/2$.
\begin{enumerate}[label=(\roman*)]
\item One has
\[
\chi_\nu(\mu)\sqrt\varkappa\le\mathcal A\le\frac{\sqrt2}{C_*}\,\chi_\nu(\mu)\sqrt\varkappa .
\]
\item One has
\[
\frac{1}{\sqrt2\,\pi}\log\varkappa\le\mathcal A\le\frac{\sqrt2}{C_*}\sqrt\varkappa .
\]
\item For every $K>0$,
\[
C_*\sqrt{\frac{\nu([0,K\mu])}{1+K}}\,\sqrt\varkappa\le\mathcal A
\le\frac{\sqrt2}{C_*}\Big[\sqrt{\nu([0,K\mu])}+\frac{2(\log(1+K)+2)}{\pi\sqrt K}\Big]\sqrt\varkappa .
\]
\item If $\nu(\{0\})=0$ and $\mu_+\mathcal I_\nu\le\Gamma<\infty$, then
\[
\mathcal A\le\frac{2\sqrt2}{\pi C_*}\sqrt\Gamma\,\big[\log(1+\varkappa)+2\big].
\]
\item For the two-level spectrum of \cref{cor:app-os-twolevel}, with $\mu_+=1$ and
$\mu=1/\varkappa$,
\[
\frac{1}{\sqrt2\,\pi}\max\big\{\sqrt{p\varkappa},\ \log\varkappa\big\}\le\mathcal A\le c_{\rm hi}\max\big\{\sqrt{p\varkappa},\ \log\varkappa\big\}.
\]
\item Along sequences $(\nu_N,\mu_{+,N},\mu_N)$ satisfying the hypotheses, with
acceleration $\mathcal A_N$ and ratio $\varkappa_N$, one has
$\liminf_N\mathcal A_N/\sqrt{\varkappa_N}>0$ if and only if
$\liminf_N\nu_N([0,K\mu_N])>0$ for some $K>0$.
\end{enumerate}
\end{corollary}
-/
theorem cor_app_os_accel_v {p κ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hκ : 2 ≤ κ) :
    1 / (Real.sqrt 2 * Real.pi) * max (Real.sqrt (p * κ)) (Real.log κ)
        ≤ accelA (nuTL p κ) 1 (1 / κ) ∧
      accelA (nuTL p κ) 1 (1 / κ) ≤ cHi * max (Real.sqrt (p * κ)) (Real.log κ) := by
  have hκ0 : (0:ℝ) < κ := by linarith
  have hκne : κ ≠ 0 := hκ0.ne'
  obtain ⟨hlo, hhi⟩ := cor_app_os_twolevel_iv hp0 hp1 hκ
  have hA : accelA (nuTL p κ) 1 (1 / κ)
      = κ * (dOsSq (nuTL p κ) (1 / κ) / dOsSq (nuTL p κ) 1) := by
    unfold accelA
    field_simp
  have e : p * κ = (p / κ) * κ ^ 2 := by field_simp
  have hsq : Real.sqrt (p * κ) = κ * Real.sqrt (p / κ) := by
    rw [e, Real.sqrt_mul (div_pos hp0 hκ0).le, Real.sqrt_sq hκ0.le]
    ring
  have e2 : κ * (Real.log κ / κ) = Real.log κ := by field_simp
  have hmax : max (Real.sqrt (p * κ)) (Real.log κ) = κ * omegaTL p κ := by
    unfold omegaTL
    rw [mul_max_of_nonneg _ _ hκ0.le, hsq, e2]
  rw [hmax, hA]
  constructor
  · calc 1 / (Real.sqrt 2 * Real.pi) * (κ * omegaTL p κ)
        = κ * (omegaTL p κ / (Real.sqrt 2 * Real.pi)) := by ring
      _ ≤ κ * (dOsSq (nuTL p κ) (1 / κ) / dOsSq (nuTL p κ) 1) :=
          mul_le_mul_of_nonneg_left hlo hκ0.le
  · calc κ * (dOsSq (nuTL p κ) (1 / κ) / dOsSq (nuTL p κ) 1)
        ≤ κ * (cHi * omegaTL p κ) := mul_le_mul_of_nonneg_left hhi hκ0.le
      _ = cHi * (κ * omegaTL p κ) := by ring

/-- Private helper for `cor:app-os-accel` part (vi): the two-sided comparison `S ≤ A/√(μ_+/μ) ≤ (√2/C_*) S`
from part (i), with `S = sqrtEff`. Helper, not a source label. -/
private lemma acvi_sandwich (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {μp μ : ℝ} (hsupp : ν (Icc 0 μp) = 1) (hμp : 0 < μp) (hμ : 0 < μ) (hμle : μ ≤ μp / 2) :
    sqrtEff ν μ ≤ accelA ν μp μ / Real.sqrt (μp / μ) ∧
      accelA ν μp μ / Real.sqrt (μp / μ) ≤ Real.sqrt 2 / cStar * sqrtEff ν μ := by
  obtain ⟨h1, h2⟩ := cor_app_os_accel_i ν hν hsupp hμp hμ hμle
  have hr : 0 < Real.sqrt (μp / μ) := Real.sqrt_pos.2 (div_pos hμp hμ)
  exact ⟨(le_div_iff₀ hr).2 h1, (div_le_iff₀ hr).2 h2⟩

/-- Private helper for `cor:app-os-accel` part (vi): liminf bookkeeping for sequences `S ≤ a ≤ c S`
with `0 ≤ S ≤ 1`. Helper, not a source label. -/
private lemma acvi_liminf (a S : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hS0 : ∀ N, 0 ≤ S N)
    (hS1 : ∀ N, S N ≤ 1) (hSa : ∀ N, S N ≤ a N) (hac : ∀ N, a N ≤ c * S N) :
    0 < liminf a atTop ↔ 0 < liminf S atTop := by
  constructor
  · intro hpos
    have hev : ∀ᶠ N in atTop, liminf a atTop / 2 < a N :=
      eventually_lt_of_lt_liminf (b := liminf a atTop / 2) (by linarith)
        (isBoundedUnder_of ⟨0, fun N => (hS0 N).trans (hSa N)⟩)
    have hev2 : ∀ᶠ N in atTop, liminf a atTop / (2 * c) ≤ S N := by
      filter_upwards [hev] with N hN
      have h := hac N
      have e : S N * (2 * c) = 2 * (c * S N) := by ring
      rw [div_le_iff₀ (mul_pos two_pos hc), e]
      linarith
    have hlb : liminf a atTop / (2 * c) ≤ liminf S atTop := by
      have h1 : liminf (fun _ : ℕ => liminf a atTop / (2 * c)) atTop = liminf a atTop / (2 * c) :=
        liminf_const _
      rw [← h1]
      exact liminf_le_liminf hev2
        (isBoundedUnder_of ⟨liminf a atTop / (2 * c), fun _ => le_rfl⟩)
        (isCoboundedUnder_ge_of_le atTop (fun N => hS1 N))
    exact lt_of_lt_of_le (div_pos hpos (mul_pos two_pos hc)) hlb
  · intro hpos
    have hlt : liminf S atTop ≤ liminf a atTop :=
      liminf_le_liminf (Eventually.of_forall hSa) (isBoundedUnder_of ⟨0, hS0⟩)
        (isCoboundedUnder_ge_of_le atTop (fun N => (hac N).trans (mul_le_of_le_one_right hc.le (hS1 N))))
    exact lt_of_lt_of_le hpos hlt

/-- Label `cor:app-os-accel`, part (vi), along sequences. Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Acceleration of a slow mode]\label{cor:app-os-accel}
Let $\nu$ be a probability measure with $\nu([0,\mu_+])=1$ for some $\mu_+>0$,
and let $0<\mu\le\mu_+/2$.
\begin{enumerate}[label=(\roman*)]
\item One has
\[
\chi_\nu(\mu)\sqrt\varkappa\le\mathcal A\le\frac{\sqrt2}{C_*}\,\chi_\nu(\mu)\sqrt\varkappa .
\]
\item One has
\[
\frac{1}{\sqrt2\,\pi}\log\varkappa\le\mathcal A\le\frac{\sqrt2}{C_*}\sqrt\varkappa .
\]
\item For every $K>0$,
\[
C_*\sqrt{\frac{\nu([0,K\mu])}{1+K}}\,\sqrt\varkappa\le\mathcal A
\le\frac{\sqrt2}{C_*}\Big[\sqrt{\nu([0,K\mu])}+\frac{2(\log(1+K)+2)}{\pi\sqrt K}\Big]\sqrt\varkappa .
\]
\item If $\nu(\{0\})=0$ and $\mu_+\mathcal I_\nu\le\Gamma<\infty$, then
\[
\mathcal A\le\frac{2\sqrt2}{\pi C_*}\sqrt\Gamma\,\big[\log(1+\varkappa)+2\big].
\]
\item For the two-level spectrum of \cref{cor:app-os-twolevel}, with $\mu_+=1$ and
$\mu=1/\varkappa$,
\[
\frac{1}{\sqrt2\,\pi}\max\big\{\sqrt{p\varkappa},\ \log\varkappa\big\}\le\mathcal A\le c_{\rm hi}\max\big\{\sqrt{p\varkappa},\ \log\varkappa\big\}.
\]
\item Along sequences $(\nu_N,\mu_{+,N},\mu_N)$ satisfying the hypotheses, with
acceleration $\mathcal A_N$ and ratio $\varkappa_N$, one has
$\liminf_N\mathcal A_N/\sqrt{\varkappa_N}>0$ if and only if
$\liminf_N\nu_N([0,K\mu_N])>0$ for some $K>0$.
\end{enumerate}
\end{corollary}
-/
theorem cor_app_os_accel_vi (ν : ℕ → Measure ℝ) [∀ N, IsProbabilityMeasure (ν N)]
    (hν : ∀ N, ν N (Iio 0) = 0) (μp μ : ℕ → ℝ) (hsupp : ∀ N, ν N (Icc 0 (μp N)) = 1)
    (hμp : ∀ N, 0 < μp N) (hμ : ∀ N, 0 < μ N) (hμle : ∀ N, μ N ≤ μp N / 2) :
    0 < liminf (fun N => accelA (ν N) (μp N) (μ N) / Real.sqrt (μp N / μ N)) atTop ↔
      ∃ K : ℝ, 0 < K ∧ 0 < liminf (fun N => (ν N (Icc 0 (K * μ N))).toReal) atTop := by
  have hS0 : ∀ N, 0 ≤ sqrtEff (ν N) (μ N) := fun N => (lem_app_os_repr_iii (ν N) (hν N) (hμ N)).1.le
  have hS1 : ∀ N, sqrtEff (ν N) (μ N) ≤ 1 := fun N => (lem_app_os_repr_iii (ν N) (hν N) (hμ N)).2
  have hsd := fun N => acvi_sandwich (ν N) (hν N) (hsupp N) (hμp N) (hμ N) (hμle N)
  have hc : (0:ℝ) < Real.sqrt 2 / cStar := div_pos (Real.sqrt_pos.2 (by norm_num)) tl_cStar_pos
  exact (acvi_liminf (fun N => accelA (ν N) (μp N) (μ N) / Real.sqrt (μp N / μ N))
    (fun N => sqrtEff (ν N) (μ N)) (Real.sqrt 2 / cStar) hc hS0 hS1
    (fun N => (hsd N).1) (fun N => (hsd N).2)).trans (prop_app_os_tail_vi ν hν μ hμ).1

/-! ## Power-law spectra (`cor:app-os-powerlaw`) -/

/-- Label `cor:app-os-powerlaw`, definition of `μ_k`, `ν_N`, `Ξ_α`. Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Power-law spectra]\label{cor:app-os-powerlaw}
Let $\alpha>0$, $N\ge1$ and $c_N>0$, let $\mu_k=c_Nk^{-\alpha}$ for
$1\le k\le N$, and put $\nu_N\defeq N^{-1}\sum_{k=1}^N\delta_{\mu_k}$. For
$0<x\le1$ put
\[
\Xi_\alpha(x)\defeq\int_0^\infty\varpi(y)\Big(\int_0^1\frac{y\,u^\alpha}{y\,u^\alpha+x^\alpha}\,\dif u\Big)^{1/2}\dif y .
\]
\begin{enumerate}[label=(\roman*)]
\item For every $1\le i\le N$,
\[
0\le\chi_{\nu_N}(\mu_i)-\Xi_\alpha(i/N)\le N^{-1/2}.
\]
\item If $i\le\varepsilon N$ with $\varepsilon\in(0,1]$, then
$1-2\varepsilon^{\alpha/(1+\alpha)}\le\chi_{\nu_N}(\mu_i)\le1$. Consequently, for every
sequence $\varepsilon_N\to0$,
\[
\max_{i\le\varepsilon_NN}\Big|\frac{\mathfrak d^{\rm os}_{\nu_N}(\mu_i)}{\sqrt{\mu_i/2}}-1\Big|\longrightarrow0 .
\]
\item The function $\Xi_\alpha$ is nonincreasing on $(0,1]$, and
\[
1-\Xi_\alpha(x)\le2x^{\alpha/(1+\alpha)},\qquad \Xi_\alpha(x)\ge\frac{C_*}{\sqrt{2(1+\alpha)}} .
\]
\item For every $1\le i\le N$,
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\sqrt{\frac{\mu_i}2}\le\mathfrak d^{\rm os}_{\nu_N}(\mu_i)\le\sqrt{\frac{\mu_i}2}.
\]
\item If $N^\alpha\ge2$, the acceleration of \cref{cor:app-os-accel} for
$\nu=\nu_N$, $\mu_+=\mu_1$ and $\mu=\mu_N$, for which $\varkappa=N^\alpha$, satisfies
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\,N^{\alpha/2}\le\mathcal A\le\frac{\sqrt2}{C_*}\,N^{\alpha/2}.
\]
\end{enumerate}
\end{corollary}
-/
def plMu (α c : ℝ) (k : ℕ) : ℝ :=
  c * (k : ℝ) ^ (-α)

/-- Label `cor:app-os-powerlaw`, definition of `ν_N`. Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Power-law spectra]\label{cor:app-os-powerlaw}
Let $\alpha>0$, $N\ge1$ and $c_N>0$, let $\mu_k=c_Nk^{-\alpha}$ for
$1\le k\le N$, and put $\nu_N\defeq N^{-1}\sum_{k=1}^N\delta_{\mu_k}$. For
$0<x\le1$ put
\[
\Xi_\alpha(x)\defeq\int_0^\infty\varpi(y)\Big(\int_0^1\frac{y\,u^\alpha}{y\,u^\alpha+x^\alpha}\,\dif u\Big)^{1/2}\dif y .
\]
\begin{enumerate}[label=(\roman*)]
\item For every $1\le i\le N$,
\[
0\le\chi_{\nu_N}(\mu_i)-\Xi_\alpha(i/N)\le N^{-1/2}.
\]
\item If $i\le\varepsilon N$ with $\varepsilon\in(0,1]$, then
$1-2\varepsilon^{\alpha/(1+\alpha)}\le\chi_{\nu_N}(\mu_i)\le1$. Consequently, for every
sequence $\varepsilon_N\to0$,
\[
\max_{i\le\varepsilon_NN}\Big|\frac{\mathfrak d^{\rm os}_{\nu_N}(\mu_i)}{\sqrt{\mu_i/2}}-1\Big|\longrightarrow0 .
\]
\item The function $\Xi_\alpha$ is nonincreasing on $(0,1]$, and
\[
1-\Xi_\alpha(x)\le2x^{\alpha/(1+\alpha)},\qquad \Xi_\alpha(x)\ge\frac{C_*}{\sqrt{2(1+\alpha)}} .
\]
\item For every $1\le i\le N$,
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\sqrt{\frac{\mu_i}2}\le\mathfrak d^{\rm os}_{\nu_N}(\mu_i)\le\sqrt{\frac{\mu_i}2}.
\]
\item If $N^\alpha\ge2$, the acceleration of \cref{cor:app-os-accel} for
$\nu=\nu_N$, $\mu_+=\mu_1$ and $\mu=\mu_N$, for which $\varkappa=N^\alpha$, satisfies
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\,N^{\alpha/2}\le\mathcal A\le\frac{\sqrt2}{C_*}\,N^{\alpha/2}.
\]
\end{enumerate}
\end{corollary}
-/
def plSpec (α c : ℝ) (N : ℕ) : Measure ℝ :=
  (N : ENNReal)⁻¹ • ∑ k ∈ Finset.Icc 1 N, Measure.dirac (plMu α c k)

/-- Label `cor:app-os-powerlaw`, definition of `Ξ_α`. Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Power-law spectra]\label{cor:app-os-powerlaw}
Let $\alpha>0$, $N\ge1$ and $c_N>0$, let $\mu_k=c_Nk^{-\alpha}$ for
$1\le k\le N$, and put $\nu_N\defeq N^{-1}\sum_{k=1}^N\delta_{\mu_k}$. For
$0<x\le1$ put
\[
\Xi_\alpha(x)\defeq\int_0^\infty\varpi(y)\Big(\int_0^1\frac{y\,u^\alpha}{y\,u^\alpha+x^\alpha}\,\dif u\Big)^{1/2}\dif y .
\]
\begin{enumerate}[label=(\roman*)]
\item For every $1\le i\le N$,
\[
0\le\chi_{\nu_N}(\mu_i)-\Xi_\alpha(i/N)\le N^{-1/2}.
\]
\item If $i\le\varepsilon N$ with $\varepsilon\in(0,1]$, then
$1-2\varepsilon^{\alpha/(1+\alpha)}\le\chi_{\nu_N}(\mu_i)\le1$. Consequently, for every
sequence $\varepsilon_N\to0$,
\[
\max_{i\le\varepsilon_NN}\Big|\frac{\mathfrak d^{\rm os}_{\nu_N}(\mu_i)}{\sqrt{\mu_i/2}}-1\Big|\longrightarrow0 .
\]
\item The function $\Xi_\alpha$ is nonincreasing on $(0,1]$, and
\[
1-\Xi_\alpha(x)\le2x^{\alpha/(1+\alpha)},\qquad \Xi_\alpha(x)\ge\frac{C_*}{\sqrt{2(1+\alpha)}} .
\]
\item For every $1\le i\le N$,
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\sqrt{\frac{\mu_i}2}\le\mathfrak d^{\rm os}_{\nu_N}(\mu_i)\le\sqrt{\frac{\mu_i}2}.
\]
\item If $N^\alpha\ge2$, the acceleration of \cref{cor:app-os-accel} for
$\nu=\nu_N$, $\mu_+=\mu_1$ and $\mu=\mu_N$, for which $\varkappa=N^\alpha$, satisfies
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\,N^{\alpha/2}\le\mathcal A\le\frac{\sqrt2}{C_*}\,N^{\alpha/2}.
\]
\end{enumerate}
\end{corollary}
-/
def plXi (α x : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), varpi y * Real.sqrt (∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + x ^ α))

private lemma pl_sum_Icc_eq (g : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, g k = ∑ k ∈ Finset.range N, g (k + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

private lemma pl_riemann {f : ℝ → ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hmono : MonotoneOn f (Icc 0 1)) (h0 : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ f u ∧ f u ≤ 1) :
    ∫ u in Ioc (0 : ℝ) 1, f u ≤ (1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N, f ((k : ℝ) / N) ∧
      (1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N, f ((k : ℝ) / N) ≤ (∫ u in Ioc (0 : ℝ) 1, f u) + 1 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hint : IntervalIntegrable f volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hmono
  have hJ : ∫ u in Ioc (0 : ℝ) 1, f u = ∫ u in (0 : ℝ)..1, f u :=
    (intervalIntegral.integral_of_le zero_le_one).symm
  have hmem : ∀ k : ℕ, k ≤ N → ((k : ℝ) / N) ∈ Icc (0 : ℝ) 1 := fun k hk =>
    ⟨by positivity, by rw [div_le_one hN']; exact_mod_cast hk⟩
  have hpt : ∀ k : ℕ, k < N → IntervalIntegrable f volume ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N) := by
    intro k hk
    apply hint.mono_set
    have hk1 : ((k + 1 : ℕ) : ℝ) / N ≤ 1 := by
      rw [div_le_one hN']; exact_mod_cast (show k + 1 ≤ N by omega)
    have hab : (k : ℝ) / N ≤ ((k + 1 : ℕ) : ℝ) / N :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hN'.le
    rw [uIcc_of_le hab, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (by positivity) hk1
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
    (a := fun k : ℕ => (k : ℝ) / N) (n := N) hpt
  have e0 : ((0 : ℕ) : ℝ) / N = 0 := by simp
  have eN : ((N : ℕ) : ℝ) / N = 1 := div_self hN'.ne'
  simp only [e0, eN] at hsum
  have hlen : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N = 1 / N := fun k => by
    push_cast; ring
  have hcellLo : ∀ k ∈ Finset.range N,
      (1 / (N : ℝ)) * f ((k : ℝ) / N) ≤ ∫ x in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N), f x := by
    intro k hk
    have hk' : k < N := Finset.mem_range.mp hk
    have hab : (k : ℝ) / N ≤ ((k + 1 : ℕ) : ℝ) / N :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hN'.le
    have h := intervalIntegral.integral_mono_on hab (intervalIntegrable_const) (hpt k hk')
      (fun x hx => hmono (hmem k (by omega)) ⟨hx.1.trans' (by positivity), hx.2.trans (hmem _ (by omega)).2⟩ hx.1)
    rw [intervalIntegral.integral_const, smul_eq_mul, hlen k] at h
    exact h
  have hcellHi : ∀ k ∈ Finset.range N,
      ∫ x in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N), f x ≤ (1 / (N : ℝ)) * f (((k + 1 : ℕ) : ℝ) / N) := by
    intro k hk
    have hk' : k < N := Finset.mem_range.mp hk
    have hab : (k : ℝ) / N ≤ ((k + 1 : ℕ) : ℝ) / N :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hN'.le
    have h := intervalIntegral.integral_mono_on hab (hpt k hk') (intervalIntegrable_const)
      (fun x hx => hmono ⟨hx.1.trans' (by positivity), hx.2.trans (hmem _ (by omega)).2⟩
        (hmem _ (by omega)) hx.2)
    rw [intervalIntegral.integral_const, smul_eq_mul, hlen k] at h
    exact h
  have hlo := Finset.sum_le_sum hcellLo
  have hhi := Finset.sum_le_sum hcellHi
  rw [← Finset.mul_sum] at hlo hhi
  rw [hsum] at hlo hhi
  rw [pl_sum_Icc_eq (fun k : ℕ => f ((k : ℝ) / N)) N]
  have htel := Finset.sum_range_sub (fun k : ℕ => f ((k : ℝ) / N)) N
  simp only [e0, eN] at htel
  rw [Finset.sum_sub_distrib] at htel
  have hf0 := (h0 0 ⟨le_refl _, zero_le_one⟩)
  have hf1 := (h0 1 ⟨zero_le_one, le_refl _⟩)
  rw [hJ]
  constructor
  · linarith
  · have : (1 / (N : ℝ)) * ∑ k ∈ Finset.range N, f (((k + 1 : ℕ) : ℝ) / N)
        ≤ (1 / (N : ℝ)) * ∑ k ∈ Finset.range N, f ((k : ℝ) / N) + 1 / N := by
      have hle : ∑ k ∈ Finset.range N, f (((k + 1 : ℕ) : ℝ) / N)
          ≤ ∑ k ∈ Finset.range N, f ((k : ℝ) / N) + 1 := by linarith
      have : (1 / (N : ℝ)) * ∑ k ∈ Finset.range N, f (((k + 1 : ℕ) : ℝ) / N)
          ≤ (1 / (N : ℝ)) * (∑ k ∈ Finset.range N, f ((k : ℝ) / N) + 1) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      linarith [mul_add (1 / (N : ℝ)) (∑ k ∈ Finset.range N, f ((k : ℝ) / N)) 1,
        show (1 / (N : ℝ)) * 1 = 1 / N by ring]
    linarith

private lemma pl_sqrt_sub_le {J S : ℝ} (hJ : 0 ≤ J) (hJS : J ≤ S) :
    Real.sqrt S - Real.sqrt J ≤ Real.sqrt (S - J) := by
  have h1 := Real.sq_sqrt hJ
  have h2 := Real.sq_sqrt (sub_nonneg.2 hJS)
  have h3 := Real.sqrt_nonneg J
  have h4 := Real.sqrt_nonneg (S - J)
  have h5 : Real.sqrt S ≤ Real.sqrt J + Real.sqrt (S - J) :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [mul_nonneg h3 h4]⟩
  linarith

private lemma pl_sqrt_diff_le {J S : ℝ} {N : ℕ} (hJ : 0 ≤ J) (hJS : J ≤ S)
    (h : S ≤ J + 1 / (N : ℝ)) : Real.sqrt S - Real.sqrt J ≤ 1 / Real.sqrt N := by
  have hd := pl_sqrt_sub_le hJ hJS
  have hd2 := Real.sqrt_le_sqrt (show S - J ≤ 1 / (N : ℝ) by linarith)
  have hsq1 : Real.sqrt (1 / (N : ℝ)) = 1 / Real.sqrt N := by
    rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
  linarith

private lemma pl_varpi_integrableOn_Ioi : IntegrableOn varpi (Ioi (0 : ℝ)) := by
  by_contra h
  have h1 := lem_app_os_integrals_iv.2
  rw [integral_undef h] at h1
  norm_num at h1

private lemma pl_varpi_measurable : Measurable varpi := by
  unfold varpi
  fun_prop

private lemma pl_mNu_eq (α c : ℝ) {N : ℕ} (t : ℝ) :
    mNu (plSpec α c N) t = ∑ k ∈ Finset.Icc 1 N, plMu α c k / (t + plMu α c k) / N := by
  unfold mNu plSpec
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  · intro k hk
    apply integrable_dirac
    simp

private lemma pl_term_eq {α c y : ℝ} (hc : 0 < c) (hy : 0 < y) {N i k : ℕ} (hk : 1 ≤ k)
    (hi : 1 ≤ i) (hN : 1 ≤ N) :
    plMu α c k / (plMu α c i * y + plMu α c k)
      = 1 - y * ((k : ℝ) / N) ^ α / (y * ((k : ℝ) / N) ^ α + ((i : ℝ) / N) ^ α) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold plMu
  rw [Real.rpow_neg hk0.le, Real.rpow_neg hi0.le, Real.div_rpow hk0.le hN0.le,
    Real.div_rpow hi0.le hN0.le]
  have hA : 0 < (k : ℝ) ^ α := Real.rpow_pos_of_pos hk0 α
  have hB : 0 < (i : ℝ) ^ α := Real.rpow_pos_of_pos hi0 α
  have hM : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hN0 α
  field_simp
  ring

private lemma pl_one_sub_mNu {α c y : ℝ} (hc : 0 < c) (hy : 0 < y) {N i : ℕ} (hi : 1 ≤ i)
    (hN : 1 ≤ N) :
    1 - mNu (plSpec α c N) (plMu α c i * y)
      = (1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N,
          y * ((k : ℝ) / N) ^ α / (y * ((k : ℝ) / N) ^ α + ((i : ℝ) / N) ^ α) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [pl_mNu_eq α c]
  have key : ∀ k ∈ Finset.Icc 1 N,
      plMu α c k / (plMu α c i * y + plMu α c k) / N
        = 1 / (N : ℝ) - (1 / (N : ℝ)) * (y * ((k : ℝ) / N) ^ α
            / (y * ((k : ℝ) / N) ^ α + ((i : ℝ) / N) ^ α)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [pl_term_eq hc hy hk.1 hi hN]
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
  have hNN : (N : ℝ) * (1 / N) = 1 := by field_simp
  rw [hNN]
  ring

private lemma pl_F_mem {α x y u : ℝ} (hy : 0 < y) (hx : 0 < x) (hu : 0 ≤ u) :
    0 ≤ y * u ^ α / (y * u ^ α + x ^ α) ∧ y * u ^ α / (y * u ^ α + x ^ α) ≤ 1 := by
  have h1 : 0 ≤ y * u ^ α := mul_nonneg hy.le (Real.rpow_nonneg hu α)
  have h2 : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have h3 : 0 < y * u ^ α + x ^ α := by linarith
  exact ⟨div_nonneg h1 h3.le, (div_le_one h3).2 (by linarith)⟩

private lemma pl_F_mono {α x y : ℝ} (hα : 0 < α) (hy : 0 < y) (hx : 0 < x) :
    MonotoneOn (fun u : ℝ => y * u ^ α / (y * u ^ α + x ^ α)) (Icc 0 1) := by
  intro u hu v hv huv
  have h1 : u ^ α ≤ v ^ α := Real.rpow_le_rpow hu.1 huv hα.le
  have h2 : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hun : 0 ≤ u ^ α := Real.rpow_nonneg hu.1 α
  have hvn : 0 ≤ v ^ α := Real.rpow_nonneg hv.1 α
  have hd1 : 0 < y * u ^ α + x ^ α := by nlinarith [mul_nonneg hy.le hun]
  have hd2 : 0 < y * v ^ α + x ^ α := by nlinarith [mul_nonneg hy.le hvn]
  show y * u ^ α / (y * u ^ α + x ^ α) ≤ y * v ^ α / (y * v ^ α + x ^ α)
  rw [div_le_div_iff₀ hd1 hd2]
  nlinarith [mul_nonneg (mul_nonneg hy.le h2.le) (sub_nonneg.2 h1)]

private lemma pl_J_measurable (α x : ℝ) :
    Measurable (fun y : ℝ => ∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + x ^ α)) := by
  let E : ℝ × ℝ → ℝ := fun p => p.1 * p.2 ^ α / (p.1 * p.2 ^ α + x ^ α)
  have hEm : Measurable E := by
    simp only [E]
    fun_prop
  have hGm : Measurable ({p : ℝ × ℝ | p.2 ∈ Ioc (0 : ℝ) 1}.indicator E) :=
    hEm.indicator (measurable_snd measurableSet_Ioc)
  have hG : Function.uncurry (fun (y u : ℝ) => {p : ℝ × ℝ | p.2 ∈ Ioc (0 : ℝ) 1}.indicator E (y, u))
      = {p : ℝ × ℝ | p.2 ∈ Ioc (0 : ℝ) 1}.indicator E := by
    funext p
    rfl
  have hsm : StronglyMeasurable
      (Function.uncurry (fun (y u : ℝ) => {p : ℝ × ℝ | p.2 ∈ Ioc (0 : ℝ) 1}.indicator E (y, u))) := by
    rw [hG]
    exact hGm.stronglyMeasurable
  have hres := (StronglyMeasurable.integral_prod_right (ν := volume) hsm).measurable
  convert hres using 1
  funext y
  rw [← integral_indicator measurableSet_Ioc]
  congr 1

private lemma pl_pointwise {α x y : ℝ} (hα : 0 < α) (hy : 0 < y) (hx : 0 < x) {N : ℕ}
    (hN : 1 ≤ N) :
    0 ≤ ∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + x ^ α) ∧
    ∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + x ^ α)
      ≤ (1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N,
          y * ((k : ℝ) / N) ^ α / (y * ((k : ℝ) / N) ^ α + x ^ α) ∧
    (1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N,
          y * ((k : ℝ) / N) ^ α / (y * ((k : ℝ) / N) ^ α + x ^ α)
      ≤ (∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + x ^ α)) + 1 / N ∧
    (1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N,
          y * ((k : ℝ) / N) ^ α / (y * ((k : ℝ) / N) ^ α + x ^ α) ≤ 1 := by
  have hR := pl_riemann (f := fun u : ℝ => y * u ^ α / (y * u ^ α + x ^ α)) hN
    (pl_F_mono hα hy hx) (fun u hu => pl_F_mem hy hx hu.1)
  refine ⟨setIntegral_nonneg measurableSet_Ioc (fun u hu => (pl_F_mem hy hx hu.1.le).1),
    hR.1, hR.2, ?_⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsum : ∑ k ∈ Finset.Icc 1 N, y * ((k : ℝ) / N) ^ α / (y * ((k : ℝ) / N) ^ α + x ^ α)
      ≤ ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) :=
    Finset.sum_le_sum (fun k _ => (pl_F_mem hy hx (by positivity)).2)
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one] at hsum
  calc (1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N, y * ((k : ℝ) / N) ^ α / (y * ((k : ℝ) / N) ^ α + x ^ α)
      ≤ (1 / (N : ℝ)) * N := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := by field_simp

/-! ### Private helpers for `cor:app-os-powerlaw` (iii)-(v) -/

private lemma pl_inf_isProb (α : ℝ) :
    IsProbabilityMeasure ((volume.restrict (Ioc (0 : ℝ) 1)).map (fun u : ℝ => u ^ (-α))) := by
  haveI : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; norm_num⟩
  infer_instance

private lemma pl_inf_Iio (α : ℝ) :
    (volume.restrict (Ioc (0 : ℝ) 1)).map (fun u : ℝ => u ^ (-α)) (Iio 0) = 0 := by
  have hm : Measurable (fun u : ℝ => u ^ (-α)) := by fun_prop
  rw [Measure.map_apply hm measurableSet_Iio, Measure.restrict_apply (hm measurableSet_Iio)]
  have h0 : (fun u : ℝ => u ^ (-α)) ⁻¹' Iio 0 ∩ Ioc (0 : ℝ) 1 = ∅ := by
    ext u
    constructor
    · rintro ⟨h1, hu⟩
      exact absurd (show u ^ (-α) < 0 from h1) (not_lt.2 (Real.rpow_nonneg hu.1.le _))
    · intro h
      exact absurd h (by simp)
  rw [h0, measure_empty]

private lemma pl_inf_mNu (α t : ℝ) :
    mNu ((volume.restrict (Ioc (0 : ℝ) 1)).map (fun u : ℝ => u ^ (-α))) t
      = ∫ u in Ioc (0 : ℝ) 1, u ^ (-α) / (t + u ^ (-α)) := by
  have hm : Measurable (fun u : ℝ => u ^ (-α)) := by fun_prop
  unfold mNu
  rw [integral_map hm.aemeasurable
    (by fun_prop : Measurable fun x : ℝ => x / (t + x)).aestronglyMeasurable]

private lemma pl_one_integrableOn : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) 1) :=
  integrable_const 1

private lemma pl_inf_g_integrable (α : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun u : ℝ => u ^ (-α) / (t + u ^ (-α))) (Ioc (0 : ℝ) 1) := by
  refine Integrable.mono' pl_one_integrableOn ?_ ?_
  · exact (by fun_prop : Measurable fun u : ℝ => u ^ (-α) / (t + u ^ (-α))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hp : 0 < u ^ (-α) := Real.rpow_pos_of_pos hu.1 _
    rw [Real.norm_of_nonneg (div_nonneg hp.le (by linarith))]
    exact (div_le_one (by linarith)).2 (by linarith)

private lemma pl_inf_key (α x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    1 - mNu ((volume.restrict (Ioc (0 : ℝ) 1)).map (fun u : ℝ => u ^ (-α))) ((x ^ α)⁻¹ * y)
      = ∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + x ^ α) := by
  have hA : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have ht : 0 ≤ (x ^ α)⁻¹ * y := (mul_pos (inv_pos.2 hA) hy).le
  have h1 : ∫ u in Ioc (0 : ℝ) 1, (1 : ℝ) = 1 := by simp [Real.volume_Ioc]
  have h2 : ∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + x ^ α)
      = ∫ u in Ioc (0 : ℝ) 1, ((1 : ℝ) - u ^ (-α) / ((x ^ α)⁻¹ * y + u ^ (-α))) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    have hu0 : 0 < u := hu.1
    have hB : 0 < u ^ α := Real.rpow_pos_of_pos hu0 α
    have hA0 : x ^ α ≠ 0 := hA.ne'
    have hB0 : u ^ α ≠ 0 := hB.ne'
    have hD1 : y * u ^ α + x ^ α ≠ 0 := (add_pos (mul_pos hy hB) hA).ne'
    have hD2 : (x ^ α)⁻¹ * y + (u ^ α)⁻¹ ≠ 0 :=
      (add_pos (mul_pos (inv_pos.2 hA) hy) (inv_pos.2 hB)).ne'
    simp only [Real.rpow_neg hu0.le]
    field_simp
    ring
  rw [pl_inf_mNu, h2, integral_sub pl_one_integrableOn (pl_inf_g_integrable α ht), h1]

private lemma pl_F_integrableOn (α y x : ℝ) (hy : 0 < y) (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => y * u ^ α / (y * u ^ α + x ^ α)) (Ioc (0 : ℝ) 1) := by
  refine Integrable.mono' pl_one_integrableOn ?_ ?_
  · exact (by fun_prop : Measurable fun u : ℝ => y * u ^ α / (y * u ^ α + x ^ α)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_of_nonneg (pl_F_mem (α := α) hy hx hu.1.le).1]
    exact (pl_F_mem (α := α) hy hx hu.1.le).2

private lemma pl_J_le_one (α x y : ℝ) (hy : 0 < y) (hx : 0 < x) :
    ∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + x ^ α) ≤ 1 := by
  calc ∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + x ^ α)
      ≤ ∫ u in Ioc (0 : ℝ) 1, (1 : ℝ) :=
        setIntegral_mono_on (pl_F_integrableOn α y x hy hx) pl_one_integrableOn measurableSet_Ioc
          (fun u hu => (pl_F_mem (α := α) hy hx hu.1.le).2)
    _ = 1 := by simp [Real.volume_Ioc]

private lemma pl_xi_integrable (α x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun y : ℝ => varpi y *
      Real.sqrt (∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + x ^ α))) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' pl_varpi_integrableOn_Ioi ?_ ?_
  · exact (pl_varpi_measurable.mul (pl_J_measurable α x).sqrt).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    have hv := lem_app_os_integrals_iv.1 y hy0
    rw [Real.norm_of_nonneg (mul_nonneg hv (Real.sqrt_nonneg _))]
    exact mul_le_of_le_one_right hv
      ((Real.sqrt_le_sqrt (pl_J_le_one α x y hy0 hx)).trans_eq Real.sqrt_one)

private lemma pl_J_anti (α : ℝ) (hα : 0 < α) {x x' : ℝ} (hx : 0 < x) (hx' : 0 < x')
    (hxx' : x ≤ x') (y : ℝ) (hy : 0 < y) :
    ∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + x' ^ α)
      ≤ ∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + x ^ α) := by
  refine setIntegral_mono_on (pl_F_integrableOn α y x' hy hx') (pl_F_integrableOn α y x hy hx)
    measurableSet_Ioc (fun u hu => ?_)
  show y * u ^ α / (y * u ^ α + x' ^ α) ≤ y * u ^ α / (y * u ^ α + x ^ α)
  have hu0 : 0 < u := hu.1
  have hB : 0 < u ^ α := Real.rpow_pos_of_pos hu0 α
  have hA : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hA' : 0 < x' ^ α := Real.rpow_pos_of_pos hx' α
  have hle : x ^ α ≤ x' ^ α := Real.rpow_le_rpow hx.le hxx' hα.le
  have hD1 : 0 < y * u ^ α + x' ^ α := add_pos (mul_pos hy hB) hA'
  have hD2 : 0 < y * u ^ α + x ^ α := add_pos (mul_pos hy hB) hA
  rw [div_le_div_iff₀ hD1 hD2]
  nlinarith [mul_nonneg (mul_nonneg hy.le hB.le) (sub_nonneg.2 hle)]

private lemma pl_xi_anti (α : ℝ) (hα : 0 < α) : AntitoneOn (plXi α) (Ioc 0 1) := by
  intro x hx x' hx' hxx'
  unfold plXi
  exact setIntegral_mono_on (pl_xi_integrable α x' hx'.1) (pl_xi_integrable α x hx.1)
    measurableSet_Ioi
    (fun y hy => mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (pl_J_anti α hα hx.1 hx'.1 hxx' y hy)) (lem_app_os_integrals_iv.1 y hy))

private lemma pl_xi_eq (α x : ℝ) (hx : 0 < x) :
    plXi α x
      = sqrtEff ((volume.restrict (Ioc (0 : ℝ) 1)).map (fun u : ℝ => u ^ (-α))) ((x ^ α)⁻¹) := by
  unfold plXi sqrtEff
  refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  have hy0 : 0 < y := hy
  rw [pl_inf_key α x y hx hy0]

private lemma pl_xi_upper (α x : ℝ) (hα : 0 < α) (hx : 0 < x) (hx1 : x ≤ 1) :
    1 - plXi α x ≤ 2 * x ^ (α / (1 + α)) := by
  haveI := pl_inf_isProb α
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = x ^ (α / (1 + α)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact Real.rpow_pos_of_pos hx _
  have h1α : (1 + α) ≠ 0 := (by linarith : (0 : ℝ) < 1 + α).ne'
  have hA : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hA0 : x ^ α ≠ 0 := hA.ne'
  have hH := (prop_app_os_head_i _ (pl_inf_Iio α) (inv_pos.2 hA) hδ0).2
  have hmass : ((volume.restrict (Ioc (0 : ℝ) 1)).map (fun u : ℝ => u ^ (-α))
      (Ici (δ * (x ^ α)⁻¹))).toReal ≤ δ := by
    have hm : Measurable (fun u : ℝ => u ^ (-α)) := by fun_prop
    have hsub : (fun u : ℝ => u ^ (-α)) ⁻¹' Ici (δ * (x ^ α)⁻¹) ∩ Ioc (0 : ℝ) 1 ⊆ Ioc 0 δ := by
      rintro u ⟨hu1, hu2⟩
      have hpre : δ * (x ^ α)⁻¹ ≤ u ^ (-α) := hu1
      have hu0 : 0 < u := hu2.1
      have hB : 0 < u ^ α := Real.rpow_pos_of_pos hu0 α
      have hB0 : u ^ α ≠ 0 := hB.ne'
      rw [Real.rpow_neg hu0.le] at hpre
      have e1 : δ * (x ^ α)⁻¹ * (u ^ α * x ^ α) = δ * u ^ α := by field_simp
      have e2 : (u ^ α)⁻¹ * (u ^ α * x ^ α) = x ^ α := by field_simp
      have hmul := mul_le_mul_of_nonneg_right hpre (mul_pos hB hA).le
      rw [e1, e2] at hmul
      have hδpow : δ ^ (1 + α) = x ^ α := by
        rw [hδ, ← Real.rpow_mul hx.le]
        congr 1
        field_simp
      have hδsplit : δ ^ (1 + α) = δ * δ ^ α := by
        rw [Real.rpow_add hδ0, Real.rpow_one]
      have hgoal : δ * u ^ α ≤ δ * δ ^ α := by
        rw [← hδsplit, hδpow]; exact hmul
      exact ⟨hu0, (Real.rpow_le_rpow_iff hu0.le hδ0.le hα).1 (le_of_mul_le_mul_left hgoal hδ0)⟩
    rw [Measure.map_apply hm measurableSet_Ici, Measure.restrict_apply (hm measurableSet_Ici)]
    apply ENNReal.toReal_le_of_le_ofReal hδ0.le
    calc _ ≤ volume (Ioc (0 : ℝ) δ) := measure_mono hsub
      _ = ENNReal.ofReal δ := by rw [Real.volume_Ioc, sub_zero]
  rw [pl_xi_eq α x hx, ← hδ]
  linarith [hH, hmass]

private lemma pl_xi_lower (α x : ℝ) (hα : 0 < α) (hx : 0 < x) (hx1 : x ≤ 1) :
    cStar / Real.sqrt (2 * (1 + α)) ≤ plXi α x := by
  haveI := pl_inf_isProb α
  have hA : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hμ : 0 < (x ^ α)⁻¹ := inv_pos.2 hA
  have hC := chi_ge_Cstar_sqrt _ (pl_inf_Iio α) hμ
  rw [pl_xi_eq α x hx]
  have hk := pl_inf_key α x 1 hx one_pos
  rw [mul_one] at hk
  have hI : ∫ u in Ioc (0 : ℝ) 1, u ^ α = 1 / (α + 1) := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_rpow (r := α) (Or.inl (by linarith))]
    rw [Real.one_rpow, Real.zero_rpow (by linarith : (0 : ℝ) < α + 1).ne']
    ring
  have e : (1 : ℝ) / (2 * (1 + α)) = 1 / (α + 1) / 2 := by
    rw [div_div, add_comm 1 α, mul_comm]
  have hf : IntegrableOn (fun u : ℝ => u ^ α / 2) (Ioc (0 : ℝ) 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < α)).1.div_const 2
  have hL : ∫ u in Ioc (0 : ℝ) 1, u ^ α / 2 = 1 / (2 * (1 + α)) := by
    rw [integral_div, hI, e]
  have hlow : 1 / (2 * (1 + α))
      ≤ 1 - mNu ((volume.restrict (Ioc (0 : ℝ) 1)).map (fun u : ℝ => u ^ (-α))) ((x ^ α)⁻¹) := by
    rw [hk, ← hL]
    refine setIntegral_mono_on hf (pl_F_integrableOn α 1 x one_pos hx) measurableSet_Ioc
      (fun u hu => ?_)
    show u ^ α / 2 ≤ 1 * u ^ α / (1 * u ^ α + x ^ α)
    have hB1 : u ^ α ≤ 1 := Real.rpow_le_one hu.1.le hu.2 hα.le
    have hA1 : x ^ α ≤ 1 := Real.rpow_le_one hx.le hx1 hα.le
    have hB0 : 0 ≤ u ^ α := Real.rpow_nonneg hu.1.le α
    have hD : 0 < 1 * u ^ α + x ^ α := by linarith
    rw [le_div_iff₀ hD]
    nlinarith [mul_nonneg hB0 (sub_nonneg.2 hB1), mul_nonneg hB0 (sub_nonneg.2 hA1)]
  have hsq : (Real.sqrt (2 * (1 + α)))⁻¹
      ≤ Real.sqrt (1 - mNu ((volume.restrict (Ioc (0 : ℝ) 1)).map (fun u : ℝ => u ^ (-α)))
          ((x ^ α)⁻¹)) := by
    rw [← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt (by rwa [one_div] at hlow)
  have h2 := mul_le_mul_of_nonneg_left hsq tl_cStar_pos.le
  rw [div_eq_mul_inv]
  exact le_trans h2 hC

/-- Label `cor:app-os-powerlaw`, part (i). Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Power-law spectra]\label{cor:app-os-powerlaw}
Let $\alpha>0$, $N\ge1$ and $c_N>0$, let $\mu_k=c_Nk^{-\alpha}$ for
$1\le k\le N$, and put $\nu_N\defeq N^{-1}\sum_{k=1}^N\delta_{\mu_k}$. For
$0<x\le1$ put
\[
\Xi_\alpha(x)\defeq\int_0^\infty\varpi(y)\Big(\int_0^1\frac{y\,u^\alpha}{y\,u^\alpha+x^\alpha}\,\dif u\Big)^{1/2}\dif y .
\]
\begin{enumerate}[label=(\roman*)]
\item For every $1\le i\le N$,
\[
0\le\chi_{\nu_N}(\mu_i)-\Xi_\alpha(i/N)\le N^{-1/2}.
\]
\item If $i\le\varepsilon N$ with $\varepsilon\in(0,1]$, then
$1-2\varepsilon^{\alpha/(1+\alpha)}\le\chi_{\nu_N}(\mu_i)\le1$. Consequently, for every
sequence $\varepsilon_N\to0$,
\[
\max_{i\le\varepsilon_NN}\Big|\frac{\mathfrak d^{\rm os}_{\nu_N}(\mu_i)}{\sqrt{\mu_i/2}}-1\Big|\longrightarrow0 .
\]
\item The function $\Xi_\alpha$ is nonincreasing on $(0,1]$, and
\[
1-\Xi_\alpha(x)\le2x^{\alpha/(1+\alpha)},\qquad \Xi_\alpha(x)\ge\frac{C_*}{\sqrt{2(1+\alpha)}} .
\]
\item For every $1\le i\le N$,
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\sqrt{\frac{\mu_i}2}\le\mathfrak d^{\rm os}_{\nu_N}(\mu_i)\le\sqrt{\frac{\mu_i}2}.
\]
\item If $N^\alpha\ge2$, the acceleration of \cref{cor:app-os-accel} for
$\nu=\nu_N$, $\mu_+=\mu_1$ and $\mu=\mu_N$, for which $\varkappa=N^\alpha$, satisfies
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\,N^{\alpha/2}\le\mathcal A\le\frac{\sqrt2}{C_*}\,N^{\alpha/2}.
\]
\end{enumerate}
\end{corollary}
-/
theorem cor_app_os_powerlaw_i {α c : ℝ} (hα : 0 < α) (hc : 0 < c) {N i : ℕ} (hi1 : 1 ≤ i)
    (hiN : i ≤ N) :
    0 ≤ sqrtEff (plSpec α c N) (plMu α c i) - plXi α ((i : ℝ) / N) ∧
      sqrtEff (plSpec α c N) (plMu α c i) - plXi α ((i : ℝ) / N) ≤ 1 / Real.sqrt N := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hx : (0 : ℝ) < (i : ℝ) / N := div_pos hi0 hN0
  have hc' : 0 < c := hc
  have hsq : sqrtEff (plSpec α c N) (plMu α c i)
      = ∫ y in Ioi (0 : ℝ), varpi y * Real.sqrt ((1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N,
          y * ((k : ℝ) / N) ^ α / (y * ((k : ℝ) / N) ^ α + ((i : ℝ) / N) ^ α)) := by
    unfold sqrtEff
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : 0 < y := hy
    rw [pl_one_sub_mNu hc' hy0 hi1 hN1]
  have hmeasS : Measurable (fun y : ℝ => (1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N,
      y * ((k : ℝ) / N) ^ α / (y * ((k : ℝ) / N) ^ α + ((i : ℝ) / N) ^ α)) := by
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro k _
    fun_prop
  have hintS : IntegrableOn (fun y : ℝ => varpi y * Real.sqrt ((1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N,
      y * ((k : ℝ) / N) ^ α / (y * ((k : ℝ) / N) ^ α + ((i : ℝ) / N) ^ α))) (Ioi (0 : ℝ)) := by
    refine Integrable.mono' pl_varpi_integrableOn_Ioi ?_ ?_
    · exact (pl_varpi_measurable.mul hmeasS.sqrt).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 : 0 < y := hy
      have hv := lem_app_os_integrals_iv.1 y hy0
      have hS := pl_pointwise hα hy0 hx hN1
      rw [Real.norm_of_nonneg (mul_nonneg hv (Real.sqrt_nonneg _))]
      exact mul_le_of_le_one_right hv ((Real.sqrt_le_sqrt hS.2.2.2).trans_eq Real.sqrt_one)
  have hintJ : IntegrableOn (fun y : ℝ => varpi y * Real.sqrt
      (∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + ((i : ℝ) / N) ^ α))) (Ioi (0 : ℝ)) := by
    refine Integrable.mono' pl_varpi_integrableOn_Ioi ?_ ?_
    · exact (pl_varpi_measurable.mul (pl_J_measurable α ((i : ℝ) / N)).sqrt).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 : 0 < y := hy
      have hv := lem_app_os_integrals_iv.1 y hy0
      have hS := pl_pointwise hα hy0 hx hN1
      rw [Real.norm_of_nonneg (mul_nonneg hv (Real.sqrt_nonneg _))]
      exact mul_le_of_le_one_right hv
        ((Real.sqrt_le_sqrt (hS.2.1.trans hS.2.2.2)).trans_eq Real.sqrt_one)
  have hintD : IntegrableOn (fun y : ℝ => varpi y * (Real.sqrt ((1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N,
      y * ((k : ℝ) / N) ^ α / (y * ((k : ℝ) / N) ^ α + ((i : ℝ) / N) ^ α))
      - Real.sqrt (∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + ((i : ℝ) / N) ^ α)))) (Ioi (0 : ℝ)) := by
    refine Integrable.congr (Integrable.sub hintS hintJ) (ae_of_all _ (fun y => ?_))
    simp only [Pi.sub_apply, mul_sub]
  have hcomb : (∫ y in Ioi (0 : ℝ), varpi y * Real.sqrt ((1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N,
      y * ((k : ℝ) / N) ^ α / (y * ((k : ℝ) / N) ^ α + ((i : ℝ) / N) ^ α)))
      - (∫ y in Ioi (0 : ℝ), varpi y * Real.sqrt
      (∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + ((i : ℝ) / N) ^ α)))
      = ∫ y in Ioi (0 : ℝ), varpi y * (Real.sqrt ((1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N,
      y * ((k : ℝ) / N) ^ α / (y * ((k : ℝ) / N) ^ α + ((i : ℝ) / N) ^ α))
      - Real.sqrt (∫ u in Ioc (0 : ℝ) 1, y * u ^ α / (y * u ^ α + ((i : ℝ) / N) ^ α))) := by
    rw [← integral_sub hintS hintJ]
    congr 1
    funext y
    ring
  rw [hsq]
  unfold plXi
  rw [hcomb]
  constructor
  · apply setIntegral_nonneg measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := hy
    have hS := pl_pointwise hα hy0 hx hN1
    exact mul_nonneg (lem_app_os_integrals_iv.1 y hy0) (sub_nonneg.2 (Real.sqrt_le_sqrt hS.2.1))
  · have hsq1 : Real.sqrt (1 / (N : ℝ)) = 1 / Real.sqrt N := by
      rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
    calc _ ≤ ∫ y in Ioi (0 : ℝ), varpi y * (1 / Real.sqrt N) := by
          refine setIntegral_mono_on hintD (Integrable.mul_const pl_varpi_integrableOn_Ioi _)
            measurableSet_Ioi ?_
          intro y hy
          have hy0 : 0 < y := hy
          have hS := pl_pointwise hα hy0 hx hN1
          have hd := pl_sqrt_diff_le (N := N) hS.1 hS.2.1 hS.2.2.1
          exact mul_le_mul_of_nonneg_left hd (lem_app_os_integrals_iv.1 y hy0)
      _ = 1 / Real.sqrt N := by
          rw [integral_mul_const, lem_app_os_integrals_iv.2, one_mul]

/-- Label `cor:app-os-powerlaw`, part (iii). Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Power-law spectra]\label{cor:app-os-powerlaw}
Let $\alpha>0$, $N\ge1$ and $c_N>0$, let $\mu_k=c_Nk^{-\alpha}$ for
$1\le k\le N$, and put $\nu_N\defeq N^{-1}\sum_{k=1}^N\delta_{\mu_k}$. For
$0<x\le1$ put
\[
\Xi_\alpha(x)\defeq\int_0^\infty\varpi(y)\Big(\int_0^1\frac{y\,u^\alpha}{y\,u^\alpha+x^\alpha}\,\dif u\Big)^{1/2}\dif y .
\]
\begin{enumerate}[label=(\roman*)]
\item For every $1\le i\le N$,
\[
0\le\chi_{\nu_N}(\mu_i)-\Xi_\alpha(i/N)\le N^{-1/2}.
\]
\item If $i\le\varepsilon N$ with $\varepsilon\in(0,1]$, then
$1-2\varepsilon^{\alpha/(1+\alpha)}\le\chi_{\nu_N}(\mu_i)\le1$. Consequently, for every
sequence $\varepsilon_N\to0$,
\[
\max_{i\le\varepsilon_NN}\Big|\frac{\mathfrak d^{\rm os}_{\nu_N}(\mu_i)}{\sqrt{\mu_i/2}}-1\Big|\longrightarrow0 .
\]
\item The function $\Xi_\alpha$ is nonincreasing on $(0,1]$, and
\[
1-\Xi_\alpha(x)\le2x^{\alpha/(1+\alpha)},\qquad \Xi_\alpha(x)\ge\frac{C_*}{\sqrt{2(1+\alpha)}} .
\]
\item For every $1\le i\le N$,
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\sqrt{\frac{\mu_i}2}\le\mathfrak d^{\rm os}_{\nu_N}(\mu_i)\le\sqrt{\frac{\mu_i}2}.
\]
\item If $N^\alpha\ge2$, the acceleration of \cref{cor:app-os-accel} for
$\nu=\nu_N$, $\mu_+=\mu_1$ and $\mu=\mu_N$, for which $\varkappa=N^\alpha$, satisfies
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\,N^{\alpha/2}\le\mathcal A\le\frac{\sqrt2}{C_*}\,N^{\alpha/2}.
\]
\end{enumerate}
\end{corollary}
-/
theorem cor_app_os_powerlaw_iii {α : ℝ} (hα : 0 < α) :
    AntitoneOn (plXi α) (Ioc 0 1) ∧
      (∀ x ∈ Ioc (0 : ℝ) 1, 1 - plXi α x ≤ 2 * x ^ (α / (1 + α))) ∧
      (∀ x ∈ Ioc (0 : ℝ) 1, cStar / Real.sqrt (2 * (1 + α)) ≤ plXi α x) := by
  exact ⟨pl_xi_anti α hα, fun x hx => pl_xi_upper α x hα hx.1 hx.2,
    fun x hx => pl_xi_lower α x hα hx.1 hx.2⟩

private lemma pl_mNu_nonneg {α c : ℝ} (hc : 0 < c) {N : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ mNu (plSpec α c N) t := by
  rw [pl_mNu_eq α c t]
  apply Finset.sum_nonneg
  intro k _
  have hp : 0 ≤ plMu α c k := by
    unfold plMu
    exact mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  exact div_nonneg (div_nonneg hp (by linarith)) (by positivity)

private lemma pl_ii_first {α c : ℝ} (hα : 0 < α) (hc : 0 < c) {ε : ℝ} (hε0 : 0 < ε)
    {N i : ℕ} (hi1 : 1 ≤ i) (hiN : i ≤ N) (hiε : (i : ℝ) ≤ ε * N) :
    1 - 2 * ε ^ (α / (1 + α)) ≤ sqrtEff (plSpec α c N) (plMu α c i) ∧
      sqrtEff (plSpec α c N) (plMu α c i) ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hx : (0 : ℝ) < (i : ℝ) / N := div_pos hi0 hN0
  have hx1 : (i : ℝ) / N ≤ 1 := by
    rw [div_le_one hN0]; exact_mod_cast hiN
  have hxε : (i : ℝ) / N ≤ ε := by
    rw [div_le_iff₀ hN0]; linarith
  have hIII := (cor_app_os_powerlaw_iii hα).2.1 ((i : ℝ) / N) ⟨hx, hx1⟩
  have hI := (cor_app_os_powerlaw_i hα hc hi1 hiN).1
  have hpow : ((i : ℝ) / N) ^ (α / (1 + α)) ≤ ε ^ (α / (1 + α)) :=
    Real.rpow_le_rpow hx.le hxε (by positivity)
  have hμ : 0 ≤ plMu α c i := by
    unfold plMu
    exact mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg i) _)
  refine ⟨by linarith [hI, hIII], ?_⟩
  unfold sqrtEff
  calc ∫ y in Ioi (0 : ℝ), varpi y * Real.sqrt (1 - mNu (plSpec α c N) (plMu α c i * y))
      ≤ ∫ y in Ioi (0 : ℝ), varpi y := by
        apply integral_mono_of_nonneg
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
          exact mul_nonneg (lem_app_os_integrals_iv.1 y hy) (Real.sqrt_nonneg _)
        · exact pl_varpi_integrableOn_Ioi
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
          have hy0 : 0 < y := hy
          have hm := pl_mNu_nonneg (α := α) (N := N) hc
            (t := plMu α c i * y) (mul_nonneg hμ hy0.le)
          exact mul_le_of_le_one_right (lem_app_os_integrals_iv.1 y hy0)
            ((Real.sqrt_le_sqrt (by linarith)).trans_eq Real.sqrt_one)
    _ = 1 := lem_app_os_integrals_iv.2

private lemma pl_isProb {α c : ℝ} {N : ℕ} (hN : 1 ≤ N) : IsProbabilityMeasure (plSpec α c N) := by
  refine ⟨?_⟩
  unfold plSpec
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul]
  have : (N : ENNReal) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp [ENNReal.inv_mul_cancel this (ENNReal.natCast_ne_top N)]

private lemma pl_Iio {α c : ℝ} (hc : 0 < c) (N : ℕ) : plSpec α c N (Iio 0) = 0 := by
  unfold plSpec
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  have : ∀ k ∈ Finset.Icc 1 N, Measure.dirac (plMu α c k) (Iio 0) = 0 := by
    intro k _
    rw [Measure.dirac_apply' _ measurableSet_Iio, Set.indicator_of_notMem]
    intro h
    have : 0 ≤ plMu α c k := mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    exact absurd (show plMu α c k < 0 from h) (not_lt.mpr this)
  rw [Finset.sum_eq_zero this]
  simp

private lemma pl_ii_N {N i : ℕ} (hi1 : 1 ≤ i) {ε : ℝ} (hiε : (i : ℝ) ≤ ε * N) : 1 ≤ N := by
  by_contra h
  have : N = 0 := by omega
  subst this
  simp at hiε
  have : (1 : ℝ) ≤ i := by exact_mod_cast hi1
  linarith

private lemma pl_ii_term {α c : ℝ} (hα : 0 < α) (hc : 0 < c) {N i : ℕ} (hi1 : 1 ≤ i)
    {ε δ : ℝ} (hδ : 0 < δ) (hiε : (i : ℝ) ≤ ε * N) {k : ℕ} (hk : 1 ≤ k) :
    plMu α c k / (plMu α c i + plMu α c k)
      ≤ (if (k : ℝ) ≤ δ * N then (1 : ℝ) else 0) + (ε / δ) ^ α := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hμk : 0 < plMu α c k := mul_pos hc (Real.rpow_pos_of_pos hk0 _)
  have hμi : 0 < plMu α c i := mul_pos hc (Real.rpow_pos_of_pos hi0 _)
  have hp : 0 ≤ (ε / δ) ^ α := by
    have : 0 ≤ ε := by
      by_contra h
      push_neg at h
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    exact Real.rpow_nonneg (div_nonneg this hδ.le) _
  have h1 : plMu α c k / (plMu α c i + plMu α c k) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  split_ifs with h
  · linarith
  · push_neg at h
    have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by have := pl_ii_N hi1 hiε; omega)
    have h2 : plMu α c k / (plMu α c i + plMu α c k) ≤ plMu α c k / plMu α c i :=
      div_le_div_of_nonneg_left hμk.le hμi (by linarith)
    have h3 : plMu α c k / plMu α c i = ((i : ℝ) / k) ^ α := by
      unfold plMu
      rw [mul_div_mul_left _ _ hc.ne', Real.rpow_neg hk0.le, Real.rpow_neg hi0.le,
        Real.div_rpow hi0.le hk0.le]
      field_simp
    have h4 : (i : ℝ) / k ≤ ε / δ := by
      rw [div_le_div_iff₀ hk0 hδ]
      nlinarith
    have h5 : ((i : ℝ) / k) ^ α ≤ (ε / δ) ^ α :=
      Real.rpow_le_rpow (div_nonneg hi0.le hk0.le) h4 hα.le
    linarith

private lemma pl_ii_m {α c : ℝ} (hα : 0 < α) (hc : 0 < c) {N i : ℕ} (hi1 : 1 ≤ i)
    {ε δ : ℝ} (hδ : 0 < δ) (hiε : (i : ℝ) ≤ ε * N) :
    mNu (plSpec α c N) (plMu α c i) ≤ δ + (ε / δ) ^ α := by
  have hN1 : 1 ≤ N := pl_ii_N hi1 hiε
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [pl_mNu_eq α c]
  have hsum : ∑ k ∈ Finset.Icc 1 N, plMu α c k / (plMu α c i + plMu α c k)
      ≤ ∑ k ∈ Finset.Icc 1 N, ((if (k : ℝ) ≤ δ * N then (1 : ℝ) else 0) + (ε / δ) ^ α) := by
    apply Finset.sum_le_sum
    intro k hk
    exact pl_ii_term hα hc hi1 hδ hiε (Finset.mem_Icc.mp hk).1
  have hcard : ∑ k ∈ Finset.Icc 1 N, (if (k : ℝ) ≤ δ * N then (1 : ℝ) else 0) ≤ δ * N := by
    rw [Finset.sum_boole]
    have hsub : (Finset.Icc 1 N).filter (fun k : ℕ => (k : ℝ) ≤ δ * N) ⊆ Finset.Icc 1 ⌊δ * N⌋₊ := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      rw [Finset.mem_Icc]
      exact ⟨hk.1.1, Nat.le_floor hk.2⟩
    have := Finset.card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at this
    calc ((Finset.filter (fun k : ℕ => (k : ℝ) ≤ δ * N) (Finset.Icc 1 N)).card : ℝ)
        ≤ (⌊δ * N⌋₊ : ℝ) := by exact_mod_cast this
      _ ≤ δ * N := Nat.floor_le (by positivity)
  have hdiv : ∑ k ∈ Finset.Icc 1 N, plMu α c k / (plMu α c i + plMu α c k) / (N : ℝ)
      = (∑ k ∈ Finset.Icc 1 N, plMu α c k / (plMu α c i + plMu α c k)) / N :=
    (Finset.sum_div _ _ _).symm
  rw [hdiv, div_le_iff₀ hN0]
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul] at hsum
  nlinarith

private lemma pl_ii_abs {α c : ℝ} (hα : 0 < α) (hc : 0 < c) {N i : ℕ} (hi1 : 1 ≤ i)
    {ε δ : ℝ} (hδ : 0 < δ) (hiε : (i : ℝ) ≤ ε * N) :
    |dOsSq (plSpec α c N) (plMu α c i) / Real.sqrt (plMu α c i / 2) - 1|
      ≤ δ + (ε / δ) ^ α := by
  have hN1 : 1 ≤ N := pl_ii_N hi1 hiε
  haveI := pl_isProb (α := α) (c := c) hN1
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hμi : 0 < plMu α c i := mul_pos hc (Real.rpow_pos_of_pos hi0 _)
  have hs : 0 < Real.sqrt (plMu α c i / 2) := Real.sqrt_pos.mpr (by linarith)
  have hT := thm_app_os_sqrt_i (plSpec α c N) (pl_Iio hc N) hμi
  have hm := pl_ii_m hα hc hi1 hδ hiε
  have hlow : (1 - mNu (plSpec α c N) (plMu α c i)) * Real.sqrt (plMu α c i / 2)
      ≤ dOsSq (plSpec α c N) (plMu α c i) :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hs.le).trans hT.1
  have hR1 : dOsSq (plSpec α c N) (plMu α c i) / Real.sqrt (plMu α c i / 2) ≤ 1 :=
    (div_le_one hs).mpr hT.2
  have hR2 : 1 - mNu (plSpec α c N) (plMu α c i)
      ≤ dOsSq (plSpec α c N) (plMu α c i) / Real.sqrt (plMu α c i / 2) :=
    (le_div_iff₀ hs).mpr hlow
  rw [abs_le]
  constructor <;> linarith

private lemma pl_ii_second {α : ℝ} (hα : 0 < α) (cN : ℕ → ℝ) (hcN : ∀ N, 0 < cN N)
    (εN : ℕ → ℝ) (hε : Tendsto εN atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ⨆ i ∈ (Finset.Icc 1 N).filter (fun i : ℕ => (i : ℝ) ≤ εN N * N),
      |dOsSq (plSpec α (cN N) N) (plMu α (cN N) i) / Real.sqrt (plMu α (cN N) i / 2) - 1|)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  set δ : ℝ := η / 4 with hδdef
  have hδ : 0 < δ := by positivity
  set ε0 : ℝ := δ * (η / 4) ^ α⁻¹ with hε0def
  have hε0 : 0 < ε0 := mul_pos hδ (Real.rpow_pos_of_pos (by positivity) _)
  have hratio : (ε0 / δ) ^ α = η / 4 := by
    rw [hε0def, mul_div_cancel_left₀ _ hδ.ne', Real.rpow_inv_rpow (by positivity) hα.ne']
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.mp hε) ε0 hε0
  refine ⟨N0, fun N hN => ?_⟩
  have hbound : (⨆ i ∈ (Finset.Icc 1 N).filter (fun i : ℕ => (i : ℝ) ≤ εN N * N),
      |dOsSq (plSpec α (cN N) N) (plMu α (cN N) i) / Real.sqrt (plMu α (cN N) i / 2) - 1|)
        ≤ η / 2 := by
    apply Real.iSup_le _ (by positivity)
    intro i
    apply Real.iSup_le _ (by positivity)
    intro hi
    rw [Finset.mem_filter, Finset.mem_Icc] at hi
    have hεN : εN N < ε0 := by
      have := hN0 N hN
      rw [Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans_lt this
    have hN0' : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hiε : (i : ℝ) ≤ ε0 * N := hi.2.trans (mul_le_mul_of_nonneg_right hεN.le hN0')
    have := pl_ii_abs hα (hcN N) hi.1.1 hδ hiε
    rw [hratio] at this
    linarith
  have hnonneg : 0 ≤ (⨆ i ∈ (Finset.Icc 1 N).filter (fun i : ℕ => (i : ℝ) ≤ εN N * N),
      |dOsSq (plSpec α (cN N) N) (plMu α (cN N) i) / Real.sqrt (plMu α (cN N) i / 2) - 1|) := by
    apply Real.iSup_nonneg
    intro i
    apply Real.iSup_nonneg
    intro _
    exact abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith

/-- Label `cor:app-os-powerlaw`, part (ii). Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Power-law spectra]\label{cor:app-os-powerlaw}
Let $\alpha>0$, $N\ge1$ and $c_N>0$, let $\mu_k=c_Nk^{-\alpha}$ for
$1\le k\le N$, and put $\nu_N\defeq N^{-1}\sum_{k=1}^N\delta_{\mu_k}$. For
$0<x\le1$ put
\[
\Xi_\alpha(x)\defeq\int_0^\infty\varpi(y)\Big(\int_0^1\frac{y\,u^\alpha}{y\,u^\alpha+x^\alpha}\,\dif u\Big)^{1/2}\dif y .
\]
\begin{enumerate}[label=(\roman*)]
\item For every $1\le i\le N$,
\[
0\le\chi_{\nu_N}(\mu_i)-\Xi_\alpha(i/N)\le N^{-1/2}.
\]
\item If $i\le\varepsilon N$ with $\varepsilon\in(0,1]$, then
$1-2\varepsilon^{\alpha/(1+\alpha)}\le\chi_{\nu_N}(\mu_i)\le1$. Consequently, for every
sequence $\varepsilon_N\to0$,
\[
\max_{i\le\varepsilon_NN}\Big|\frac{\mathfrak d^{\rm os}_{\nu_N}(\mu_i)}{\sqrt{\mu_i/2}}-1\Big|\longrightarrow0 .
\]
\item The function $\Xi_\alpha$ is nonincreasing on $(0,1]$, and
\[
1-\Xi_\alpha(x)\le2x^{\alpha/(1+\alpha)},\qquad \Xi_\alpha(x)\ge\frac{C_*}{\sqrt{2(1+\alpha)}} .
\]
\item For every $1\le i\le N$,
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\sqrt{\frac{\mu_i}2}\le\mathfrak d^{\rm os}_{\nu_N}(\mu_i)\le\sqrt{\frac{\mu_i}2}.
\]
\item If $N^\alpha\ge2$, the acceleration of \cref{cor:app-os-accel} for
$\nu=\nu_N$, $\mu_+=\mu_1$ and $\mu=\mu_N$, for which $\varkappa=N^\alpha$, satisfies
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\,N^{\alpha/2}\le\mathcal A\le\frac{\sqrt2}{C_*}\,N^{\alpha/2}.
\]
\end{enumerate}
\end{corollary}
-/
theorem cor_app_os_powerlaw_ii {α c : ℝ} (hα : 0 < α) (hc : 0 < c) :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ N i : ℕ, 1 ≤ i → i ≤ N → (i : ℝ) ≤ ε * N →
      1 - 2 * ε ^ (α / (1 + α)) ≤ sqrtEff (plSpec α c N) (plMu α c i) ∧
        sqrtEff (plSpec α c N) (plMu α c i) ≤ 1) ∧
    ∀ cN : ℕ → ℝ, (∀ N, 0 < cN N) → ∀ εN : ℕ → ℝ, Tendsto εN atTop (𝓝 0) →
      Tendsto (fun N : ℕ => ⨆ i ∈ (Finset.Icc 1 N).filter (fun i : ℕ => (i : ℝ) ≤ εN N * N),
        |dOsSq (plSpec α (cN N) N) (plMu α (cN N) i) / Real.sqrt (plMu α (cN N) i / 2) - 1|)
        atTop (𝓝 0) := by
  exact ⟨fun ε hε0 _ N i hi1 hiN hiε => pl_ii_first hα hc hε0 hi1 hiN hiε,
    fun cN hcN εN hε => pl_ii_second hα cN hcN εN hε⟩

private lemma pl_mu_pos {α c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 1 ≤ k) : 0 < plMu α c k :=
  mul_pos hc (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < k by omega)) _)

private lemma pl_spec_one {α c : ℝ} {N : ℕ} (hN : 1 ≤ N) (s : Set ℝ)
    (h : ∀ k ∈ Finset.Icc 1 N, plMu α c k ∈ s) : plSpec α c N s = 1 := by
  unfold plSpec
  rw [Measure.smul_apply, Measure.finsetSum_apply,
    Finset.sum_congr rfl (fun k hk => Measure.dirac_apply_of_mem (h k hk))]
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul,
    mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (show N ≠ 0 by omega))
    (ENNReal.natCast_ne_top N)

/-- Label `cor:app-os-powerlaw`, part (iv). Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Power-law spectra]\label{cor:app-os-powerlaw}
Let $\alpha>0$, $N\ge1$ and $c_N>0$, let $\mu_k=c_Nk^{-\alpha}$ for
$1\le k\le N$, and put $\nu_N\defeq N^{-1}\sum_{k=1}^N\delta_{\mu_k}$. For
$0<x\le1$ put
\[
\Xi_\alpha(x)\defeq\int_0^\infty\varpi(y)\Big(\int_0^1\frac{y\,u^\alpha}{y\,u^\alpha+x^\alpha}\,\dif u\Big)^{1/2}\dif y .
\]
\begin{enumerate}[label=(\roman*)]
\item For every $1\le i\le N$,
\[
0\le\chi_{\nu_N}(\mu_i)-\Xi_\alpha(i/N)\le N^{-1/2}.
\]
\item If $i\le\varepsilon N$ with $\varepsilon\in(0,1]$, then
$1-2\varepsilon^{\alpha/(1+\alpha)}\le\chi_{\nu_N}(\mu_i)\le1$. Consequently, for every
sequence $\varepsilon_N\to0$,
\[
\max_{i\le\varepsilon_NN}\Big|\frac{\mathfrak d^{\rm os}_{\nu_N}(\mu_i)}{\sqrt{\mu_i/2}}-1\Big|\longrightarrow0 .
\]
\item The function $\Xi_\alpha$ is nonincreasing on $(0,1]$, and
\[
1-\Xi_\alpha(x)\le2x^{\alpha/(1+\alpha)},\qquad \Xi_\alpha(x)\ge\frac{C_*}{\sqrt{2(1+\alpha)}} .
\]
\item For every $1\le i\le N$,
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\sqrt{\frac{\mu_i}2}\le\mathfrak d^{\rm os}_{\nu_N}(\mu_i)\le\sqrt{\frac{\mu_i}2}.
\]
\item If $N^\alpha\ge2$, the acceleration of \cref{cor:app-os-accel} for
$\nu=\nu_N$, $\mu_+=\mu_1$ and $\mu=\mu_N$, for which $\varkappa=N^\alpha$, satisfies
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\,N^{\alpha/2}\le\mathcal A\le\frac{\sqrt2}{C_*}\,N^{\alpha/2}.
\]
\end{enumerate}
\end{corollary}
-/
theorem cor_app_os_powerlaw_iv {α c : ℝ} (hα : 0 < α) (hc : 0 < c) {N i : ℕ} (hi1 : 1 ≤ i)
    (hiN : i ≤ N) :
    cStar / Real.sqrt (2 * (1 + α)) * Real.sqrt (plMu α c i / 2)
        ≤ dOsSq (plSpec α c N) (plMu α c i) ∧
      dOsSq (plSpec α c N) (plMu α c i) ≤ Real.sqrt (plMu α c i / 2) := by
  have hN1 : 1 ≤ N := hi1.trans hiN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  haveI := pl_isProb (α := α) (c := c) hN1
  have hν := pl_Iio (α := α) hc N
  have hμ := pl_mu_pos (α := α) hc hi1
  have hx : (0 : ℝ) < (i : ℝ) / N := div_pos hi0 hN0
  have hx1 : (i : ℝ) / N ∈ Ioc (0 : ℝ) 1 :=
    ⟨hx, (div_le_one hN0).2 (by exact_mod_cast hiN)⟩
  have hI := cor_app_os_powerlaw_i hα hc hi1 hiN
  have hIII := (cor_app_os_powerlaw_iii hα).2.2 _ hx1
  have hSE : cStar / Real.sqrt (2 * (1 + α)) ≤ sqrtEff (plSpec α c N) (plMu α c i) :=
    le_trans hIII (by linarith [hI.1])
  have hrep := lem_app_os_repr_ii (plSpec α c N) hν hμ
  have hpos : 0 ≤ Real.sqrt (plMu α c i / 2) := Real.sqrt_nonneg _
  constructor
  · rw [hrep]
    nlinarith [mul_le_mul_of_nonneg_left hSE hpos]
  · exact (thm_app_os_sqrt_i (plSpec α c N) hν hμ).2

/-- Label `cor:app-os-powerlaw`, part (v). Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{corollary}[Power-law spectra]\label{cor:app-os-powerlaw}
Let $\alpha>0$, $N\ge1$ and $c_N>0$, let $\mu_k=c_Nk^{-\alpha}$ for
$1\le k\le N$, and put $\nu_N\defeq N^{-1}\sum_{k=1}^N\delta_{\mu_k}$. For
$0<x\le1$ put
\[
\Xi_\alpha(x)\defeq\int_0^\infty\varpi(y)\Big(\int_0^1\frac{y\,u^\alpha}{y\,u^\alpha+x^\alpha}\,\dif u\Big)^{1/2}\dif y .
\]
\begin{enumerate}[label=(\roman*)]
\item For every $1\le i\le N$,
\[
0\le\chi_{\nu_N}(\mu_i)-\Xi_\alpha(i/N)\le N^{-1/2}.
\]
\item If $i\le\varepsilon N$ with $\varepsilon\in(0,1]$, then
$1-2\varepsilon^{\alpha/(1+\alpha)}\le\chi_{\nu_N}(\mu_i)\le1$. Consequently, for every
sequence $\varepsilon_N\to0$,
\[
\max_{i\le\varepsilon_NN}\Big|\frac{\mathfrak d^{\rm os}_{\nu_N}(\mu_i)}{\sqrt{\mu_i/2}}-1\Big|\longrightarrow0 .
\]
\item The function $\Xi_\alpha$ is nonincreasing on $(0,1]$, and
\[
1-\Xi_\alpha(x)\le2x^{\alpha/(1+\alpha)},\qquad \Xi_\alpha(x)\ge\frac{C_*}{\sqrt{2(1+\alpha)}} .
\]
\item For every $1\le i\le N$,
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\sqrt{\frac{\mu_i}2}\le\mathfrak d^{\rm os}_{\nu_N}(\mu_i)\le\sqrt{\frac{\mu_i}2}.
\]
\item If $N^\alpha\ge2$, the acceleration of \cref{cor:app-os-accel} for
$\nu=\nu_N$, $\mu_+=\mu_1$ and $\mu=\mu_N$, for which $\varkappa=N^\alpha$, satisfies
\[
\frac{C_*}{\sqrt{2(1+\alpha)}}\,N^{\alpha/2}\le\mathcal A\le\frac{\sqrt2}{C_*}\,N^{\alpha/2}.
\]
\end{enumerate}
\end{corollary}
-/
theorem cor_app_os_powerlaw_v {α c : ℝ} (hα : 0 < α) (hc : 0 < c) {N : ℕ}
    (hN : 2 ≤ (N : ℝ) ^ α) :
    cStar / Real.sqrt (2 * (1 + α)) * (N : ℝ) ^ (α / 2)
        ≤ accelA (plSpec α c N) (plMu α c 1) (plMu α c N) ∧
      accelA (plSpec α c N) (plMu α c 1) (plMu α c N)
        ≤ Real.sqrt 2 / cStar * (N : ℝ) ^ (α / 2) := by
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, Nat.cast_zero, Real.zero_rpow hα.ne'] at hN
      norm_num at hN
    · exact h
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  haveI := pl_isProb (α := α) (c := c) hN1
  have hν := pl_Iio (α := α) hc N
  have hmem : ∀ k ∈ Finset.Icc 1 N, plMu α c k ∈ Icc 0 (plMu α c 1) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    refine ⟨(pl_mu_pos hc hk.1).le, ?_⟩
    unfold plMu
    rw [Nat.cast_one, Real.one_rpow, mul_one]
    have h1 := Real.rpow_le_rpow_of_nonpos (x := 1) (y := (k : ℝ)) one_pos
      (by exact_mod_cast hk.1 : (1 : ℝ) ≤ k) (by linarith : -α ≤ 0)
    rw [Real.one_rpow] at h1
    exact mul_le_of_le_one_right hc.le h1
  have hsupp : plSpec α c N (Icc 0 (plMu α c 1)) = 1 := pl_spec_one hN1 _ hmem
  have hμN := pl_mu_pos (α := α) hc hN1
  have hinv : (N : ℝ) ^ (-α) ≤ 1 / 2 := by
    rw [Real.rpow_neg hN0.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hN
  have hμle : plMu α c N ≤ plMu α c 1 / 2 := by
    unfold plMu
    rw [Nat.cast_one, Real.one_rpow, mul_one]
    have := mul_le_mul_of_nonneg_left hinv hc.le
    linarith
  have hratio : plMu α c 1 / plMu α c N = (N : ℝ) ^ α := by
    have hNα : (N : ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos hN0 α).ne'
    unfold plMu
    rw [Nat.cast_one, Real.one_rpow, Real.rpow_neg hN0.le]
    field_simp
  have hsqrt : Real.sqrt ((N : ℝ) ^ α) = (N : ℝ) ^ (α / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  have hI := cor_app_os_powerlaw_i hα hc hN1 le_rfl
  have hx1 : (N : ℝ) / N ∈ Ioc (0 : ℝ) 1 := ⟨div_pos hN0 hN0, (div_le_one hN0).2 le_rfl⟩
  have hIII := (cor_app_os_powerlaw_iii hα).2.2 _ hx1
  have hSE : cStar / Real.sqrt (2 * (1 + α)) ≤ sqrtEff (plSpec α c N) (plMu α c N) :=
    le_trans hIII (by linarith [hI.1])
  have hs1 := (lem_app_os_repr_iii _ hν hμN).2
  have hacc := cor_app_os_accel_i (plSpec α c N) hν hsupp (pl_mu_pos (α := α) hc (le_refl 1)) hμN hμle
  rw [hratio, hsqrt] at hacc
  have hK : 0 ≤ Real.sqrt 2 / cStar := div_nonneg (Real.sqrt_nonneg _) tl_cStar_pos.le
  have ht : 0 ≤ (N : ℝ) ^ (α / 2) := Real.rpow_nonneg hN0.le _
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_right hSE ht) hacc.1
  · have h3 : Real.sqrt 2 / cStar * sqrtEff (plSpec α c N) (plMu α c N) * (N : ℝ) ^ (α / 2)
        ≤ Real.sqrt 2 / cStar * (N : ℝ) ^ (α / 2) := by
      nlinarith [mul_nonneg (mul_nonneg hK ht) (sub_nonneg.2 hs1)]
    exact le_trans hacc.2 h3

/-! ## Packing (promoted part of `rem:app-os-packed`) -/

/-- Label `rem:app-os-packed`, promoted part (i): packing transfers from the smallest eigenvalue to every larger mode; the unfolded form of `def:app-os-packed` (owned by L-G2.7). Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{remark}[Where packing holds]\label{rem:app-os-packed}
The count $\#\{k:\mu_k\le K\mu\}$ is nondecreasing in $\mu$, so if the smallest
positive eigenvalue is $(K,\delta)$-packed, then every mode is. If all
eigenvalues lie in $[\mu_{\min},\kappa\mu_{\min}]$ with $\mu_{\min}>0$, every mode is
$(\kappa,1)$-packed, since $\mu_k\le\kappa\mu_{\min}\le\kappa\mu_i$ for all $k$. If the spectrum
consists of clusters of equal eigenvalues, each holding at least $pN$ of them, every
mode is $(1,p)$-packed, since its own cluster lies in $[0,\mu_i]$. For the geometric
spectrum $\mu_k=q^k$ with fixed $q\in(0,1)$, the smallest eigenvalue $\mu_N$ has only
$1+\lfloor\log K/\log(1/q)\rfloor$ eigenvalues in $[0,K\mu_N]$, a vanishing fraction as $N\to\infty$, so it is
not $(K,\delta)$-packed for any fixed $K,\delta$ once $N$ is large. For the power law
$\mu_k=c_Nk^{-\alpha}$, $1\le k\le N$, every mode is $(2,1-2^{-1/\alpha})$-packed, because
$\mu_k\le2\mu_i$ for every $k\ge2^{-1/\alpha}i$, and there are at least $N-2^{-1/\alpha}i\ge(1-2^{-1/\alpha})N$
such $k$. Conversely, packing is necessary for a lower bound of this form:
by \cref{prop:app-os-tail}(vi), along a sequence of spectra the efficiency
$\chi_{\nu_N}(\mu_N)$ stays bounded below only if, for some $K$, the fraction of
the spectrum in $[0,K\mu_N]$ stays bounded below, and by
\cref{prop:app-os-tail}(ii),(iii) a mode far below most of the spectrum
receives drift of gradient-descent order up to a logarithm.
\end{remark}
-/
theorem rem_app_os_packed_i {N : ℕ} (μ : Fin N → ℝ) {K δ : ℝ} (hK : 1 ≤ K) {m i : Fin N}
    (hmin : μ m ≤ μ i)
    (hpk : δ * N ≤ ((Finset.univ.filter fun k : Fin N => μ k ≤ K * μ m).card : ℝ)) :
    δ * N ≤ ((Finset.univ.filter fun k : Fin N => μ k ≤ K * μ i).card : ℝ) := by
  have hsub : (Finset.univ.filter fun k : Fin N => μ k ≤ K * μ m) ⊆
      Finset.univ.filter fun k : Fin N => μ k ≤ K * μ i := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.trans (mul_le_mul_of_nonneg_left hmin (by linarith))
  have hcard : (Finset.univ.filter fun k : Fin N => μ k ≤ K * μ m).card ≤
      (Finset.univ.filter fun k : Fin N => μ k ≤ K * μ i).card := Finset.card_le_card hsub
  have hcardR : ((Finset.univ.filter fun k : Fin N => μ k ≤ K * μ m).card : ℝ) ≤
      ((Finset.univ.filter fun k : Fin N => μ k ≤ K * μ i).card : ℝ) := by exact_mod_cast hcard
  linarith

/-- Label `rem:app-os-packed`, promoted part (ii): power-law spectrum `μ_k = c k^{-α}` (`1 ≤ k ≤ N`) on `Fin N` is `(2, 1-2^{-1/α})`-packed; unfolded form of `def:app-os-packed` (owned by L-G2.7). Snapshot `cr-2026-10-23`. Statement verbatim (the whole environment of the label; the declaration formalizes the part named above):

\begin{remark}[Where packing holds]\label{rem:app-os-packed}
The count $\#\{k:\mu_k\le K\mu\}$ is nondecreasing in $\mu$, so if the smallest
positive eigenvalue is $(K,\delta)$-packed, then every mode is. If all
eigenvalues lie in $[\mu_{\min},\kappa\mu_{\min}]$ with $\mu_{\min}>0$, every mode is
$(\kappa,1)$-packed, since $\mu_k\le\kappa\mu_{\min}\le\kappa\mu_i$ for all $k$. If the spectrum
consists of clusters of equal eigenvalues, each holding at least $pN$ of them, every
mode is $(1,p)$-packed, since its own cluster lies in $[0,\mu_i]$. For the geometric
spectrum $\mu_k=q^k$ with fixed $q\in(0,1)$, the smallest eigenvalue $\mu_N$ has only
$1+\lfloor\log K/\log(1/q)\rfloor$ eigenvalues in $[0,K\mu_N]$, a vanishing fraction as $N\to\infty$, so it is
not $(K,\delta)$-packed for any fixed $K,\delta$ once $N$ is large. For the power law
$\mu_k=c_Nk^{-\alpha}$, $1\le k\le N$, every mode is $(2,1-2^{-1/\alpha})$-packed, because
$\mu_k\le2\mu_i$ for every $k\ge2^{-1/\alpha}i$, and there are at least $N-2^{-1/\alpha}i\ge(1-2^{-1/\alpha})N$
such $k$. Conversely, packing is necessary for a lower bound of this form:
by \cref{prop:app-os-tail}(vi), along a sequence of spectra the efficiency
$\chi_{\nu_N}(\mu_N)$ stays bounded below only if, for some $K$, the fraction of
the spectrum in $[0,K\mu_N]$ stays bounded below, and by
\cref{prop:app-os-tail}(ii),(iii) a mode far below most of the spectrum
receives drift of gradient-descent order up to a logarithm.
\end{remark}
-/
theorem rem_app_os_packed_ii {α c : ℝ} (hα : 0 < α) (hc : 0 < c) {N : ℕ} (μ : Fin N → ℝ)
    (hμ : ∀ k : Fin N, μ k = c * (((k : ℕ) : ℝ) + 1) ^ (-α)) (i : Fin N) :
    (1 - (2 : ℝ) ^ (-1 / α)) * N ≤ ((Finset.univ.filter fun k : Fin N => μ k ≤ 2 * μ i).card : ℝ) := by
  have hα0 : α ≠ 0 := hα.ne'
  have hr0 : (0 : ℝ) < (2 : ℝ) ^ (-1 / α) := Real.rpow_pos_of_pos (by norm_num) _
  have hpow : ((2 : ℝ) ^ (-1 / α)) ^ (-α) = 2 := by
    rw [← Real.rpow_mul (by norm_num)]
    have h1 : -1 / α * -α = 1 := by field_simp
    rw [h1, Real.rpow_one]
  set r : ℝ := (2 : ℝ) ^ (-1 / α) with hr
  set t : ℝ := r * (((i : ℕ) : ℝ) + 1) with ht
  have ht0 : 0 < t := mul_pos hr0 (by positivity)
  have hμi : μ i = c * (((i : ℕ) : ℝ) + 1) ^ (-α) := hμ i
  have hS : ∀ k : Fin N, t ≤ ((k : ℕ) : ℝ) + 1 → μ k ≤ 2 * μ i := by
    intro k hk
    rw [hμ k, hμi]
    have h1 : (((k : ℕ) : ℝ) + 1) ^ (-α) ≤ t ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos ht0 hk (by linarith)
    have h2 : t ^ (-α) = 2 * (((i : ℕ) : ℝ) + 1) ^ (-α) := by
      rw [ht, Real.mul_rpow hr0.le (by positivity), hpow]
    calc c * (((k : ℕ) : ℝ) + 1) ^ (-α) ≤ c * (2 * (((i : ℕ) : ℝ) + 1) ^ (-α)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2.le) hc.le
      _ = 2 * (c * (((i : ℕ) : ℝ) + 1) ^ (-α)) := by ring
  have hsub : (Finset.univ.filter fun k : Fin N => t ≤ ((k : ℕ) : ℝ) + 1) ⊆
      Finset.univ.filter fun k : Fin N => μ k ≤ 2 * μ i := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hS k hk
  have hA : (Finset.univ.filter fun k : Fin N => ¬ (t ≤ ((k : ℕ) : ℝ) + 1)).card ≤ ⌊t⌋₊ := by
    have hmaps : Set.MapsTo (fun k : Fin N => (k : ℕ) + 1)
        ((Finset.univ.filter fun k : Fin N => ¬ (t ≤ ((k : ℕ) : ℝ) + 1)) : Set (Fin N))
        ((Finset.Icc 1 ⌊t⌋₊ : Finset ℕ) : Set ℕ) := by
      intro k hk
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, not_le] at hk
      simp only [Finset.coe_Icc, Set.mem_Icc]
      refine ⟨by omega, Nat.le_floor ?_⟩
      push_cast
      exact hk.le
    have hinj : Set.InjOn (fun k : Fin N => (k : ℕ) + 1)
        ((Finset.univ.filter fun k : Fin N => ¬ (t ≤ ((k : ℕ) : ℝ) + 1)) : Set (Fin N)) := by
      intro a _ b _ hab
      exact Fin.ext (by simpa using hab)
    have := Finset.card_le_card_of_injOn _ hmaps hinj
    simpa using this
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (fun k : Fin N => t ≤ ((k : ℕ) : ℝ) + 1)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have hfl : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
  have hiN : ((i : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
    have := i.isLt
    exact_mod_cast Nat.succ_le_of_lt this
  have htN : t ≤ r * N := by
    rw [ht]
    exact mul_le_mul_of_nonneg_left hiN hr0.le
  have hcS := Finset.card_le_card hsub
  have hsplitR : ((Finset.univ.filter fun k : Fin N => t ≤ ((k : ℕ) : ℝ) + 1).card : ℝ) +
      ((Finset.univ.filter fun k : Fin N => ¬ (t ≤ ((k : ℕ) : ℝ) + 1)).card : ℝ) = (N : ℝ) := by
    exact_mod_cast hsplit
  have hAR : ((Finset.univ.filter fun k : Fin N => ¬ (t ≤ ((k : ℕ) : ℝ) + 1)).card : ℝ) ≤
      ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast hA
  have hcSR : ((Finset.univ.filter fun k : Fin N => t ≤ ((k : ℕ) : ℝ) + 1).card : ℝ) ≤
      ((Finset.univ.filter fun k : Fin N => μ k ≤ 2 * μ i).card : ℝ) := by exact_mod_cast hcS
  rw [sub_mul, one_mul]
  linarith

end

end Muon.Oversampled

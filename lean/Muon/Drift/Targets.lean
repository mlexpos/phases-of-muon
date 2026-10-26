import Muon.DetEquiv.Trace
import Muon.Drift.Defs
import Muon.Drift.Coefficients
import Muon.Setup.Regime
import Muon.Drift.Scalar

/-!
# Muon.Drift: targets and the Gaussian limit of the derivative functional (work package L-C.8)

Interface draft (statements only; every proof is `sorry`) for `lem:app-drift-gaussian` and
`lem:app-drift-targets` of `sections/03-drift/CARD.md` §3, snapshot `cr-2026-10-23`.

Reused, not restated: `rPrimeB` (the functional `r'_B`), `thetaB` (`ϑ_B(I)`), `alphaStar1/2`
(`α⋆`), `specOutFM`/`specInFM` (`ν_out`, `ν_in`), `emaW`, `freshExp`, and the setup regime
`Muon.Setup.SetupRegime` (`assum:app-setup-regime`). The coefficients `delAlpha1/2` and the
scalar targets are those of `Muon.DetEquiv.Concentration`.

Representation choices (see the docstrings):
* `lem:app-drift-gaussian` is stated along a sequence of frozen states `A k` with
  `‖A k‖_F = 1` and `‖A k‖_op → 0`, the hypotheses of `lem:app-de-gaussian` (card §6.6); the
  functional is the one fixed in `Muon.Drift.Defs` (`rPrimeB`), whose expectation is over the fresh
  Gaussian pair `freshMeas`.
* `lem:app-drift-targets` is stated first for a general weight sequence `w` with
  `WeightClass w` (`lem_app_drift_targets_i_weights`, `lem_app_drift_targets_ii_weights`; card
  rule (a)). The EMA records `lem_app_drift_targets_i/ii` are their instances at `emaW R.β`, which
  equals `(R.F k).β` for every `k` by `R.hβ`; `emaW_weightClass` supplies `WeightClass`.
* Claim (i) of the targets is `ϑ_B(I) → 0` together with the boundedness of the family over `I`
  (`BddAbove` conjunct, card rule (c)), so the `iSup` in `thetaB` is exported as a genuine supremum.
* Claim (ii) quantifies the sequence `e_B^⋆ = e_B + C_I ϑ_B(I)` existentially, because `e_B` and
  `C_I` are existential in the source and only `e_B^⋆ → 0` together with the bounds is asserted.
-/

open MeasureTheory Filter Topology Set
open scoped Matrix ENNReal
open Matrix
open Muon Muon.Setup Muon.DetEquiv

set_option linter.style.longLine false

namespace Muon.Drift


private lemma scr_fX_contDiff (x : ℝ) (hx : 0 ≤ x) : ContDiff ℝ 2 (fX x) := by
  have hc : ContDiff ℝ 2 (fun d : ℝ => 1 + x * d ^ 2) := by fun_prop
  have hne : ∀ d : ℝ, (1 + x * d ^ 2) ≠ 0 := fun d => by
    have := mul_nonneg hx (sq_nonneg d); linarith
  exact (contDiff_id (𝕜 := ℝ)).div hc hne

private lemma scr_stein (x : ℝ) (hx : 0 ≤ x) :
    ∫ g, deriv (fX x) g ∂(ProbabilityTheory.gaussianReal 0 1) = J x := by
  have hC1 : ContDiff ℝ 1 (fX x) := (scr_fX_contDiff x hx).of_le (by norm_num)
  have hb : ∃ C : ℝ, ∃ k : ℕ, ∀ y : ℝ, |fX x y| ≤ C * (1 + |y| ^ k) := by
    refine ⟨1, 1, fun y => ?_⟩
    have hd : 1 ≤ 1 + x * y ^ 2 := by have := mul_nonneg hx (sq_nonneg y); linarith
    have h1 : |fX x y| ≤ |y| := by
      unfold fX
      rw [abs_div, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + x * y ^ 2)]
      exact div_le_self (abs_nonneg _) hd
    have : 0 ≤ |y| ^ 1 := by positivity
    simp only [pow_one] at this ⊢
    linarith
  have hdb : ∃ C : ℝ, ∃ k : ℕ, ∀ y : ℝ, |deriv (fX x) y| ≤ C * (1 + |y| ^ k) := by
    refine ⟨1, 0, fun y => ?_⟩
    have := lem_app_drift_derivatives_i hx y
    simp only [pow_zero]
    linarith
  have hs := Muon.Foundations.gaussian_stein (fX x) hC1 hb hdb
  rw [← hs]
  unfold DetEquiv.J
  congr 1
  ext g
  unfold fX
  field_simp


private lemma scr_drift_hpow2 (d : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2) (2 * d) d := by
  simpa using hasDerivAt_pow 2 d

private lemma scr_deriv_formula (s d : ℝ) (hs : 1 + s * d ^ 2 ≠ 0) :
    deriv (fX s) d = (1 * (1 + s * d ^ 2) - d * (s * (2 * d))) / (1 + s * d ^ 2) ^ 2 := by
  have h2 : HasDerivAt (fun e : ℝ => 1 + s * e ^ 2) (s * (2 * d)) d :=
    ((scr_drift_hpow2 d).const_mul s).const_add 1
  have h := (hasDerivAt_id' d).div h2 hs
  unfold fX
  exact h.deriv

private lemma scr_diff (d t : ℝ) (ht : 0 ≤ t) :
    DifferentiableAt ℝ (fun s => deriv (fX s) d) t := by
  have hD : 0 < 1 + t * d ^ 2 := by have := mul_nonneg ht (sq_nonneg d); linarith
  have hc : Continuous (fun s : ℝ => 1 + s * d ^ 2) := by fun_prop
  have hev : ∀ᶠ s in 𝓝 t, 0 < 1 + s * d ^ 2 :=
    hc.continuousAt.eventually (lt_mem_nhds hD)
  have hE : DifferentiableAt ℝ
      (fun s : ℝ => (1 * (1 + s * d ^ 2) - d * (s * (2 * d))) / (1 + s * d ^ 2) ^ 2) t := by
    apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact pow_ne_zero 2 hD.ne'
  refine hE.congr_of_eventuallyEq ?_
  filter_upwards [hev] with s hs
  exact scr_deriv_formula s d hs.ne'

private lemma scr_pointwise_lip (d x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |deriv (fX x) d - deriv (fX y) d| ≤ 3 * d ^ 2 * |x - y| := by
  have hb : ∀ t ∈ Ici (0:ℝ), ‖deriv (fun s => deriv (fX s) d) t‖ ≤ 3 * d ^ 2 := fun t ht => by
    rw [Real.norm_eq_abs]; exact lem_app_drift_derivatives_vi ht d
  have h := (convex_Ici (0:ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := fun s => deriv (fX s) d) (fun t ht => scr_diff d t ht) hb
    (mem_Ici.mpr hx) (mem_Ici.mpr hy)
  have h2 : |deriv (fX y) d - deriv (fX x) d| ≤ 3 * d ^ 2 * |y - x| := by
    simpa only [Real.norm_eq_abs] using h
  rw [abs_sub_comm (deriv (fX x) d), abs_sub_comm x y]
  exact h2

private lemma scr_resid_memLp (m n : ℕ) (A : Mat m n) (hA : fro A = 1) :
    MemLp (fun p : Vec m × Vec n => resid A p) 2 (gaussPair m n) ∧
      ∫ p, (resid A p) ^ 2 ∂(gaussPair m n) ≤ 1 := by
  have h := lem_app_de_moments_ii A hA 1 le_rfl
  norm_num [Nat.doubleFactorial] at h
  have hcont : Continuous (fun p : Vec m × Vec n => resid A p) := by
    unfold resid; fun_prop
  have hmem : MemLp (fun p : Vec m × Vec n => resid A p) 2 (gaussPair m n) := by
    exact lt_of_le_of_lt h ENNReal.one_lt_top
  refine ⟨hmem, ?_⟩
  have he := hmem.eLpNorm_eq_integral_rpow_norm (p := 2) (by norm_num) (by norm_num)
  rw [he] at h
  have h3 := ENNReal.ofReal_le_one.mp h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h3
  by_contra hc
  push_neg at hc
  have := Real.one_lt_rpow hc (by norm_num : (0:ℝ) < 2⁻¹)
  linarith

private lemma scr_freshExp_lip (m n : ℕ) (A : Mat m n) (hA : fro A = 1) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |freshExp A (fun d => deriv (fX x) d) - freshExp A (fun d => deriv (fX y) d)| ≤ 3 * |x - y| := by
  obtain ⟨hmem, hint⟩ := scr_resid_memLp m n A hA
  have hsq : Integrable (fun p : Vec m × Vec n => (resid A p) ^ 2) (gaussPair m n) :=
    hmem.integrable_sq
  have hcont : Continuous (fun p : Vec m × Vec n => resid A p) := by
    unfold resid; fun_prop
  have hI : ∀ z : ℝ, 0 ≤ z → Integrable (fun p : Vec m × Vec n => deriv (fX z) (resid A p))
      (gaussPair m n) := by
    intro z hz
    refine (integrable_const (1:ℝ)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (((scr_fX_contDiff z hz).continuous_deriv (by norm_num)).comp hcont).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact lem_app_drift_derivatives_i hz _
  have e1 : freshExp A (fun d => deriv (fX x) d)
      = ∫ p, deriv (fX x) (resid A p) ∂(gaussPair m n) := rfl
  have e2 : freshExp A (fun d => deriv (fX y) d)
      = ∫ p, deriv (fX y) (resid A p) ∂(gaussPair m n) := rfl
  rw [e1, e2, ← integral_sub (hI x hx) (hI y hy)]
  have hbound : |∫ p, (deriv (fX x) (resid A p) - deriv (fX y) (resid A p)) ∂(gaussPair m n)|
      ≤ ∫ p, 3 * |x - y| * (resid A p) ^ 2 ∂(gaussPair m n) := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hsq.const_mul (3 * |x - y|))
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    have := scr_pointwise_lip (resid A p) x y hx hy
    calc _ ≤ 3 * (resid A p) ^ 2 * |x - y| := this
      _ = 3 * |x - y| * (resid A p) ^ 2 := by ring
  calc _ ≤ ∫ p, 3 * |x - y| * (resid A p) ^ 2 ∂(gaussPair m n) := hbound
    _ = 3 * |x - y| * ∫ p, (resid A p) ^ 2 ∂(gaussPair m n) := integral_const_mul _ _
    _ ≤ 3 * |x - y| * 1 := mul_le_mul_of_nonneg_left hint (by positivity)
    _ = 3 * |x - y| := mul_one _

private lemma scr_pointwise (m n : ℕ → ℕ) (A : ∀ k, Mat (m k) (n k)) (hA : ∀ k, fro (A k) = 1)
    (hAn : Tendsto (fun k => opNorm (A k)) atTop (𝓝 0)) (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun k => freshExp (A k) (fun d => deriv (fX x) d)) atTop
      (𝓝 (Muon.DetEquiv.J x)) := by
  have hcont : Continuous (deriv (fX x)) :=
    (scr_fX_contDiff x hx).continuous_deriv (by norm_num)
  have hbd : ∀ y : ℝ, |deriv (fX x) y| ≤ 1 + y ^ 2 := fun y => by
    have := lem_app_drift_derivatives_i hx y
    nlinarith [sq_nonneg y]
  have hlaw : ∀ k, (gaussPair (m k) (n k)).map
      (fun ω : Vec (m k) × Vec (n k) => (ω.1, ω.2)) = gaussPair (m k) (n k) :=
    fun k => Measure.map_id
  have key := (lem_app_setup_residual_iii (m := m) (n := n)
    (Ω := fun k => Vec (m k) × Vec (n k)) (P := fun k => gaussPair (m k) (n k))
    A (fun k p => p.1) (fun k p => p.2) hlaw hA hAn).2 (deriv (fX x)) hcont hbd
  have key' : Tendsto (fun k => freshExp (A k) (fun d => deriv (fX x) d)) atTop
      (𝓝 (∫ y, deriv (fX x) y ∂(ProbabilityTheory.gaussianReal 0 1))) := key
  rw [scr_stein x hx] at key'
  exact key'

/-- `lem:app-drift-gaussian`, snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.623–628):
```latex
\begin{lemma}[Uniform Gaussian limit of the derivative functional]\label{lem:app-drift-gaussian}
With $d=z^\T\Ahat w$ as in \cref{lem:app-de-gaussian},
\[
r_B'\defeq\sup_{0\le x\le q_I}\abs{\EE f_x'(d)-\Jfun(x)}\longrightarrow0 .
\]
\end{lemma}
```
Statement: with `d = zᵀ Â w` the fresh Gaussian scalar, `r'_B = sup_{0 ≤ x ≤ q_I} |𝔼 f'_x(d) − J(x)|`
tends to `0` along any sequence of normalized states with `‖Â‖_F = 1` and `‖Â‖_op → 0` (the
hypotheses of `lem:app-de-gaussian`, card §6.6). `q_I` is an explicit real parameter. -/
theorem lem_app_drift_gaussian {m n : ℕ → ℕ} (A : ∀ k, Mat (m k) (n k))
    (hA : ∀ k, fro (A k) = 1) (hAn : Tendsto (fun k => opNorm (A k)) atTop (𝓝 0)) (qI : ℝ) :
    Tendsto (fun k => rPrimeB (A k) qI) atTop (𝓝 0) := by
  rcases lt_or_ge qI 0 with hq | hq
  · have hz : ∀ k, rPrimeB (A k) qI = 0 := by
      intro k
      unfold rPrimeB
      apply le_antisymm
      · refine Real.iSup_le (fun x => Real.iSup_le (fun hx => ?_) le_rfl) le_rfl
        exfalso
        linarith [hx.1, hx.2]
      · exact Real.iSup_nonneg fun x => Real.iSup_nonneg fun _ => abs_nonneg _
    simp only [hz]
    exact tendsto_const_nhds
  · have hJ := (Muon.Drift.abs_deriv_J_le_three).2
    have hL : ∀ k : ℕ, ∀ x ∈ Icc (0:ℝ) qI, ∀ y ∈ Icc (0:ℝ) qI,
        |(freshExp (A k) (fun d => deriv (fX x) d) - Muon.DetEquiv.J x)
          - (freshExp (A k) (fun d => deriv (fX y) d) - Muon.DetEquiv.J y)| ≤ 6 * |x - y| := by
      intro k x hx y hy
      have h1 := scr_freshExp_lip (m k) (n k) (A k) (hA k) x y hx.1 hy.1
      have h2 : |Muon.DetEquiv.J x - Muon.DetEquiv.J y| ≤ 3 * |x - y| := by
        have := hJ.dist_le_mul x (mem_Ici.mpr hx.1) y (mem_Ici.mpr hy.1)
        simpa [Real.dist_eq] using this
      have e : (freshExp (A k) (fun d => deriv (fX x) d) - Muon.DetEquiv.J x)
          - (freshExp (A k) (fun d => deriv (fX y) d) - Muon.DetEquiv.J y)
          = (freshExp (A k) (fun d => deriv (fX x) d) - freshExp (A k) (fun d => deriv (fX y) d))
            - (Muon.DetEquiv.J x - Muon.DetEquiv.J y) := by ring
      rw [e]
      calc _ ≤ |freshExp (A k) (fun d => deriv (fX x) d) - freshExp (A k) (fun d => deriv (fX y) d)|
            + |Muon.DetEquiv.J x - Muon.DetEquiv.J y| := abs_sub _ _
        _ ≤ 6 * |x - y| := by linarith
    have hpt : ∀ x ∈ Icc (0:ℝ) qI, Tendsto
        (fun k => freshExp (A k) (fun d => deriv (fX x) d) - Muon.DetEquiv.J x) atTop
        (𝓝 ((fun _ : ℝ => (0:ℝ)) x)) := by
      intro x hx
      have := (scr_pointwise m n A hA hAn x hx.1).sub_const (Muon.DetEquiv.J x)
      simpa using this
    have hU := uniform_of_pointwise_lipschitz (Q := qI) (L := 6)
      (f := fun k x => freshExp (A k) (fun d => deriv (fX x) d) - Muon.DetEquiv.J x)
      (g := fun _ => (0:ℝ)) hL hpt
    rw [Metric.tendstoUniformlyOn_iff] at hU
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hU (ε / 2) (by positivity)] with k hk
    rw [Real.dist_eq, sub_zero]
    unfold rPrimeB
    rw [abs_of_nonneg (Real.iSup_nonneg fun x => Real.iSup_nonneg fun _ => abs_nonneg _)]
    refine lt_of_le_of_lt (Real.iSup_le (fun x => Real.iSup_le (fun hx => ?_) (by positivity))
      (by positivity)) (by linarith : ε / 2 < ε)
    have := hk x hx
    simp only [Real.dist_eq, zero_sub, abs_neg] at this
    exact this.le


private lemma scr_inv_measurable {a : ℕ} : Measurable (fun X : Mat a a => X⁻¹) := by
  have hdet : Measurable (fun X : Mat a a => X.det) := (continuous_id.matrix_det).measurable
  have hadj : Measurable (fun X : Mat a a => X.adjugate) :=
    (continuous_id.matrix_adjugate).measurable
  have hinv : (fun X : Mat a a => X⁻¹) = fun X => Ring.inverse X.det • X.adjugate :=
    funext fun X => Matrix.inv_def X
  have h1 : Measurable (fun X : Mat a a => Ring.inverse X.det) := by
    simp only [Ring.inverse_eq_inv]
    exact hdet.inv
  rw [hinv]
  exact h1.smul hadj

private lemma scr_Rs_measurable {a b : ℕ} (s : ℝ) :
    Measurable (fun M : Mat a b => Rs M s) := by
  have hc : Continuous (fun M : Mat a b => M * Mᵀ + s • (1 : Mat a a)) := by fun_prop
  exact (scr_inv_measurable (a := a)).comp hc.measurable

private lemma scr_Rts_measurable {a b : ℕ} (s : ℝ) :
    Measurable (fun M : Mat a b => Rts M s) := by
  have hc : Continuous (fun M : Mat a b => Mᵀ * M + s • (1 : Mat b b)) := by fun_prop
  exact (scr_inv_measurable (a := b)).comp hc.measurable

private lemma scr_meas_WB {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'} {m n B : ℕ}
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) :
    Measurable (WeightedBuf w F S t) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hQ : Measurable (fun x : Vec m × Vec n =>
      (dotProduct x.1 (Matrix.mulVec F.A x.2)) • (rOut F.C * Muon.outer x.1 x.2 * rIn F.C)) := by
    have hdot : Measurable (fun x : Vec m × Vec n => dotProduct x.1 (Matrix.mulVec F.A x.2)) := by
      show Measurable (fun x : Vec m × Vec n => ∑ i, x.1 i * ∑ j, F.A i j * x.2 j)
      exact Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp measurable_fst).mul
        (Finset.measurable_sum _ (fun j _ =>
          measurable_const.mul ((measurable_pi_apply j).comp measurable_snd))))
    have hout : Continuous (fun x : Vec m × Vec n => Muon.outer x.1 x.2) :=
      continuous_pi fun i => continuous_pi fun j =>
        ((continuous_apply i).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)
    have hM : Measurable (fun x : Vec m × Vec n => rOut F.C * Muon.outer x.1 x.2 * rIn F.C) :=
      Continuous.measurable ((continuous_const.matrix_mul hout).matrix_mul continuous_const)
    exact hdot.smul hM
  unfold WeightedBuf
  refine Measurable.tsum fun j => ?_
  refine Measurable.const_smul ?_ (w j)
  show Measurable (fun ω => ((B : ℝ))⁻¹ • ∑ a : Fin B,
    (dotProduct (S.zw (t + 1 - (j : ℤ)) a ω).1 (Matrix.mulVec F.A (S.zw (t + 1 - (j : ℤ)) a ω).2)) •
      (rOut F.C * outer (S.zw (t + 1 - (j : ℤ)) a ω).1 (S.zw (t + 1 - (j : ℤ)) a ω).2 * rIn F.C))
  exact (Finset.measurable_sum _ fun a _ => hQ.comp (S.meas _ _)).const_smul ((B : ℝ)⁻¹)

private lemma scr_abs_entry_le_opNorm {p q : ℕ} (K : Mat p q) (i : Fin p) (j : Fin q) :
    |K i j| ≤ opNorm K := by
  have h1 := Matrix.l2_opNorm_mulVec K (EuclideanSpace.single j (1 : ℝ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin p) ℝ).symm
    (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i
  have h3 : ((EuclideanSpace.equiv (Fin p) ℝ).symm
      (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i = K i j := by
    simp [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at h1
  rw [h3, Real.norm_eq_abs] at h2
  rw [opNorm_eq_norm]
  linarith

private lemma scr_trace_mean_eq {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {p : ℕ} (X : Ω' → Mat p p)
    (hX : Measurable X) (c : ℝ) (hb : ∀ ω, opNorm (X ω) ≤ c) (S : Mat p p) :
    (S * Muon.mean P X).trace = ∫ ω, (S * X ω).trace ∂P := by
  have hmeas : ∀ i k, Measurable (fun ω => X ω k i) := fun i k =>
    (by fun_prop : Measurable fun M : Mat p p => M k i).comp hX
  have hint : ∀ i k, Integrable (fun ω => X ω k i) P := fun i k =>
    Integrable.mono' (integrable_const c) (hmeas i k).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact (scr_abs_entry_le_opNorm (X ω) k i).trans (hb ω))
  have hL : (S * Muon.mean P X).trace = ∑ i, ∑ k, S i k * ∫ ω, X ω k i ∂P := by
    simp [Matrix.trace, Matrix.mul_apply, Muon.mean]
  have hR : ∀ ω, (S * X ω).trace = ∑ i, ∑ k, S i k * X ω k i := fun ω => by
    simp [Matrix.trace, Matrix.mul_apply]
  simp only [hR]
  rw [hL, integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun k _ =>
    (hint i k).const_mul (S i k)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun k _ => (hint i k).const_mul (S i k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]

/-- Pointwise bound on `|Tr(S X)|` from an operator-norm bound on `X`. -/
private lemma scr_trace_bound {p : ℕ} (S X : Mat p p) (c : ℝ) (hb : opNorm X ≤ c) :
    |(S * X).trace| ≤ ∑ i, ∑ k, |S i k| * c := by
  have hR : (S * X).trace = ∑ i, ∑ k, S i k * X k i := by
    simp [Matrix.trace, Matrix.mul_apply]
  rw [hR]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((scr_abs_entry_le_opNorm X k i).trans hb) (abs_nonneg _)

/-- Chebyshev-type deviation bound: `|𝔼 f − b| ≤ L/(2ε) + ε/2` when `𝔼 (f−b)² ≤ L`. -/
private lemma scr_dev_bound {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] (f : Ω' → ℝ) (hf : Measurable f) (M : ℝ)
    (hM : ∀ ω, |f ω| ≤ M) (b ε : ℝ) (hε : 0 < ε) (L : ℝ≥0∞)
    (hL : ∫⁻ ω, ENNReal.ofReal (‖f ω - b‖ ^ 2) ∂P ≤ L) (hLtop : L ≠ ⊤) :
    |(∫ ω, f ω ∂P) - b| ≤ L.toReal / (2 * ε) + ε / 2 := by
  have hfi : Integrable f P := Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hM ω)
  have hgi : Integrable (fun ω => (f ω - b) ^ 2) P := by
    refine Integrable.mono' (integrable_const ((M + |b|) ^ 2))
      ((hf.sub_const b).pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    have h1 : |f ω - b| ≤ M + |b| := (abs_sub _ _).trans (by linarith [hM ω])
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hint2 : ∫ ω, (f ω - b) ^ 2 ∂P ≤ L.toReal := by
    have h0 : (0 : ℝ) ≤ ∫ ω, (f ω - b) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    have h1 := ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ fun ω => sq_nonneg _)
    have h2 : ENNReal.ofReal (∫ ω, (f ω - b) ^ 2 ∂P) ≤ L := by
      rw [h1]
      refine le_trans (lintegral_mono fun ω => ?_) hL
      rw [Real.norm_eq_abs, sq_abs]
    exact (ENNReal.ofReal_le_iff_le_toReal hLtop).mp h2
  have hsub : (∫ ω, f ω ∂P) - b = ∫ ω, (f ω - b) ∂P := by
    rw [integral_sub hfi (integrable_const b)]
    simp
  have hpt : ∀ ω, |f ω - b| ≤ (f ω - b) ^ 2 / (2 * ε) + ε / 2 := fun ω => by
    have h2ε : 0 < 2 * ε := by positivity
    rw [← sub_nonneg]
    have : (f ω - b) ^ 2 / (2 * ε) + ε / 2 - |f ω - b| = (|f ω - b| - ε) ^ 2 / (2 * ε) := by
      field_simp
      rw [← sq_abs (f ω - b)]
      ring
    rw [this]; positivity
  have hrhs : Integrable (fun ω => (f ω - b) ^ 2 / (2 * ε) + ε / 2) P :=
    (hgi.div_const _).add (integrable_const _)
  rw [hsub, ← Real.norm_eq_abs]
  calc ‖∫ ω, (f ω - b) ∂P‖ ≤ ∫ ω, ‖f ω - b‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ((f ω - b) ^ 2 / (2 * ε) + ε / 2) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => norm_nonneg _) hrhs
          (ae_of_all _ fun ω => by
            show ‖f ω - b‖ ≤ _
            rw [Real.norm_eq_abs]; exact hpt ω)
    _ = (∫ ω, (f ω - b) ^ 2 ∂P) / (2 * ε) + ε / 2 := by
        rw [integral_add (hgi.div_const _) (integrable_const _), integral_div]
        simp
    _ ≤ L.toReal / (2 * ε) + ε / 2 := by
        gcongr

private lemma scr_sigma_dev {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'}
    [IsProbabilityMeasure P] {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ) (hs : 0 < s) (b ε : ℝ) (hε : 0 < ε) (L : ℝ≥0∞)
    (hL : ∫⁻ ω, ENNReal.ofReal (‖(B : ℝ)⁻¹ * Matrix.trace (F.C.Sout *
        Rs (WeightedBuf w F S t ω) s) - b‖ ^ 2) ∂P ≤ L) (hLtop : L ≠ ⊤) :
    |sigmaB w F S t s - b| ≤ L.toReal / (2 * ε) + ε / 2 := by
  have hmeas : Measurable (fun ω => Rs (WeightedBuf w F S t ω) s) :=
    (scr_Rs_measurable s).comp (scr_meas_WB w F S t)
  have hb : ∀ ω, opNorm (Rs (WeightedBuf w F S t ω) s) ≤ 1 / s :=
    fun ω => (lem_app_de_resolvent _ s hs).1
  have heq : sigmaB w F S t s =
      ∫ ω, (B : ℝ)⁻¹ * (F.C.Sout * Rs (WeightedBuf w F S t ω) s).trace ∂P := by
    unfold sigmaB expRes
    rw [scr_trace_mean_eq P _ hmeas (1 / s) hb, integral_const_mul]
  rw [heq]
  refine scr_dev_bound P _ ?_ ((B : ℝ)⁻¹ * ∑ i, ∑ k, |F.C.Sout i k| * (1 / s)) ?_ b ε hε L hL hLtop
  · have h1 : Measurable (fun M : Mat m m => (F.C.Sout * M).trace) :=
      (Continuous.matrix_trace (continuous_const.matrix_mul continuous_id)).measurable
    exact (h1.comp hmeas).const_mul _
  · intro ω
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg B))]
    exact mul_le_mul_of_nonneg_left (scr_trace_bound _ _ _ (hb ω)) (inv_nonneg.mpr (Nat.cast_nonneg B))

private lemma scr_sigmaT_dev {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'}
    [IsProbabilityMeasure P] {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ) (hs : 0 < s) (b ε : ℝ) (hε : 0 < ε) (L : ℝ≥0∞)
    (hL : ∫⁻ ω, ENNReal.ofReal (‖(B : ℝ)⁻¹ * Matrix.trace (F.C.Sin *
        Rts (WeightedBuf w F S t ω) s) - b‖ ^ 2) ∂P ≤ L) (hLtop : L ≠ ⊤) :
    |sigmaTildeB w F S t s - b| ≤ L.toReal / (2 * ε) + ε / 2 := by
  have hmeas : Measurable (fun ω => Rts (WeightedBuf w F S t ω) s) :=
    (scr_Rts_measurable s).comp (scr_meas_WB w F S t)
  have hb : ∀ ω, opNorm (Rts (WeightedBuf w F S t ω) s) ≤ 1 / s :=
    fun ω => (lem_app_de_resolvent _ s hs).2.1
  have heq : sigmaTildeB w F S t s =
      ∫ ω, (B : ℝ)⁻¹ * (F.C.Sin * Rts (WeightedBuf w F S t ω) s).trace ∂P := by
    unfold sigmaTildeB expResT
    rw [scr_trace_mean_eq P _ hmeas (1 / s) hb, integral_const_mul]
  rw [heq]
  refine scr_dev_bound P _ ?_ ((B : ℝ)⁻¹ * ∑ i, ∑ k, |F.C.Sin i k| * (1 / s)) ?_ b ε hε L hL hLtop
  · have h1 : Measurable (fun M : Mat n n => (F.C.Sin * M).trace) :=
      (Continuous.matrix_trace (continuous_const.matrix_mul continuous_id)).measurable
    exact (h1.comp hmeas).const_mul _
  · intro ω
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg B))]
    exact mul_le_mul_of_nonneg_left (scr_trace_bound _ _ _ (hb ω)) (inv_nonneg.mpr (Nat.cast_nonneg B))

/-- General-weight form of claim (i) of `lem:app-drift-targets`, snapshot `cr-2026-10-23`
(card rule (a), §6.1). For `WeightClass w` under `assum:app-setup-regime`, with the spectral
measures `specOutFM`, `specInFM`: the family `s ↦ |σ_B(s) − σ(−s)| + |σ̃_B(s) − σ̃(−s)|` is bounded
on `I` for every `k` (`BddAbove`, card rule (c)), and `ϑ_B(I) → 0`. The EMA record is the
instance at `emaW R.β`. -/
theorem lem_app_drift_targets_i_weights (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) (w : ℕ → ℝ) (hw : WeightClass w) :
    (∀ k, BddAbove ((fun s => |sigmaB w (R.F k) (S k) t s - (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).1|
        + |sigmaTildeB w (R.F k) (S k) t s - (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).2.1|) '' I)) ∧
    Tendsto (fun k => thetaB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) I) atTop (𝓝 0) := by
  classical
  set γ' : ℝ := max R.γstar 1 with hγ'
  have hC0 : 0 < R.CSig := lt_of_lt_of_le one_pos R.hC
  have hγ0 : 0 < γ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hνo : ∀ k, ((specOutFM (R.F k) : FiniteMeasure ℝ) : Measure ℝ) =
      nuOut (R.F k).C (R.B k) := fun k => rfl
  have hνi : ∀ k, ((specInFM (R.F k) : FiniteMeasure ℝ) : Measure ℝ) =
      nuIn (R.F k).C (R.B k) := fun k => rfl
  have hK : ∀ k, (specOutFM (R.F k), specInFM (R.F k)) ∈ classK R.CSig γ' := by
    intro k
    obtain ⟨o1, o2⟩ := assum_app_setup_regime_nuOut R k
    obtain ⟨i1, i2⟩ := assum_app_setup_regime_nuIn R k
    have hle : ENNReal.ofReal R.γstar ≤ ENNReal.ofReal γ' :=
      ENNReal.ofReal_le_ofReal (le_max_left _ _)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hνo k]; exact (measure_mono (Set.subset_univ _)).trans (o2.trans hle)
    · rw [hνo k]; exact o1
    · rw [hνi k]; exact (measure_mono (Set.subset_univ _)).trans (i2.trans hle)
    · rw [hνi k]; exact i1
  obtain ⟨sm, hsm, hsmI⟩ : ∃ sm : ℝ, 0 < sm ∧ ∀ s ∈ I, sm ≤ s := by
    rcases I.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨sInf I, hIpos (hI.sInf_mem h), fun s hs => csInf_le hI.bddBelow hs⟩
  have hdm : ∀ k, (R.m k : ℝ) ≤ γ' * (R.B k : ℝ) := fun k =>
    (le_trans (Nat.cast_le.mpr (le_max_left _ _)) (R.dims k)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  have hdn : ∀ k, (R.n k : ℝ) ≤ γ' * (R.B k : ℝ) := fun k =>
    (le_trans (Nat.cast_le.mpr (le_max_right _ _)) (R.dims k)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  have hq : ∀ k, ∀ s ∈ I, 0 ≤ sigmaB w (R.F k) (S k) t s ∧
      sigmaB w (R.F k) (S k) t s ≤ R.CSig * γ' / s ∧
      0 ≤ sigmaTildeB w (R.F k) (S k) t s ∧
      sigmaTildeB w (R.F k) (S k) t s ≤ R.CSig * γ' / s := by
    intro k s hs
    obtain ⟨a1, a2, a3, a4, -, -⟩ := eqn_app_de_qI w hw (R.F k) (S k) t R.CSig γ' sm I hsm hsmI
      ⟨R.normOut k, R.normIn k⟩ ⟨hdm k, hdn k⟩ s hs
    exact ⟨a1, a2, a3, a4⟩
  have hbr : ∀ k, ∀ s ∈ I,
      0 ≤ (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).1 ∧
      (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).1 ≤ R.CSig * γ' / s ∧
      0 ≤ (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).2.1 ∧
      (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).2.1 ≤ R.CSig * γ' / s := by
    intro k s hs
    have hpos : 0 < s := hIpos hs
    have hsol := branchSol_spec (Fw_admissible hw.1) hC0 hγ0 (hK k) hpos
    have hb := ((thm_app_de_branch_i (Fw_admissible hw.1) hC0 hγ0 _ _ (hK k) s hpos).2 _ hsol)
    have hnn : ∀ x : ℝ × ℝ × ℝ × ℝ, IsBranchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s x →
        0 ≤ x.1 ∧ 0 ≤ x.2.1 := by
      rintro ⟨σ, σ', a, c⟩ h
      simp only [IsBranchSol] at h
      exact ⟨h.1, h.2.1⟩
    have hn := hnn _ hsol
    refine ⟨hn.1, ?_, hn.2, ?_⟩
    · have := hb.1; rwa [mul_comm] at this
    · have := hb.2.1; rwa [mul_comm] at this
  have hK0 : 0 ≤ R.CSig * γ' := by positivity
  refine ⟨fun k => ?_, ?_⟩
  · refine ⟨2 * (R.CSig * γ' / sm), ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hpos : 0 < s := hIpos hs
    obtain ⟨a1, a2, a3, a4⟩ := hq k s hs
    obtain ⟨b1, b2, b3, b4⟩ := hbr k s hs
    have hle : R.CSig * γ' / s ≤ R.CSig * γ' / sm :=
      div_le_div_of_nonneg_left hK0 hsm (hsmI s hs)
    have e1 : |sigmaB w (R.F k) (S k) t s -
        (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).1| ≤ R.CSig * γ' / s := by
      rw [abs_le]; constructor <;> linarith
    have e2 : |sigmaTildeB w (R.F k) (S k) t s -
        (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).2.1| ≤ R.CSig * γ' / s := by
      rw [abs_le]; constructor <;> linarith
    show _ ≤ _
    linarith
  · have ht3 := (cor_app_de_trace_iii R w hw P S (fun k => specOutFM (R.F k))
      (fun k => specInFM (R.F k)) hνo hνi t I hI hIpos).2
    have ht4 := (cor_app_de_trace_iv R w hw P S (fun k => specOutFM (R.F k))
      (fun k => specInFM (R.F k)) hνo hνi t I hI hIpos).2
    rw [Metric.tendsto_nhds]
    intro ε' hε'
    set e : ℝ := ε' / 4 with he
    have he0 : 0 < e := by positivity
    have hpe : (0 : ℝ≥0∞) < ENNReal.ofReal (e ^ 2) := ENNReal.ofReal_pos.mpr (by positivity)
    filter_upwards [ht3.eventually (gt_mem_nhds hpe), ht4.eventually (gt_mem_nhds hpe)]
      with k hk3 hk4
    have fin3 := hk3.ne_top
    have fin4 := hk4.ne_top
    have t3 : (∫⁻ ω, ⨆ s ∈ I, ENNReal.ofReal (‖((R.B k : ℝ))⁻¹ * Matrix.trace ((R.F k).C.Sout *
        Rs (WeightedBuf w (R.F k) (S k) t ω) s) -
        (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).1‖ ^ 2) ∂(P k)).toReal
        ≤ e ^ 2 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hk3.le
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have t4 : (∫⁻ ω, ⨆ s ∈ I, ENNReal.ofReal (‖((R.B k : ℝ))⁻¹ * Matrix.trace ((R.F k).C.Sin *
        Rts (WeightedBuf w (R.F k) (S k) t ω) s) -
        (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).2.1‖ ^ 2) ∂(P k)).toReal
        ≤ e ^ 2 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hk4.le
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have key : ∀ x : ℝ, 0 ≤ x → x ≤ e ^ 2 → x / (2 * e) + e / 2 ≤ e := by
      intro x hx0 hx1
      have : x / (2 * e) ≤ e / 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    have hθ : thetaB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) I ≤ 2 * e := by
      refine Real.iSup_le (fun s => Real.iSup_le (fun hs => ?_) (by positivity)) (by positivity)
      have hpos : 0 < s := hIpos hs
      have d3 := scr_sigma_dev w (R.F k) (S k) t s hpos
        (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).1 e he0 _
        (lintegral_mono fun ω => le_iSup₂ (f := fun s (_ : s ∈ I) => ENNReal.ofReal
          (‖((R.B k : ℝ))⁻¹ * Matrix.trace ((R.F k).C.Sout *
            Rs (WeightedBuf w (R.F k) (S k) t ω) s) -
            (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).1‖ ^ 2)) s hs) fin3
      have d4 := scr_sigmaT_dev w (R.F k) (S k) t s hpos
        (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).2.1 e he0 _
        (lintegral_mono fun ω => le_iSup₂ (f := fun s (_ : s ∈ I) => ENNReal.ofReal
          (‖((R.B k : ℝ))⁻¹ * Matrix.trace ((R.F k).C.Sin *
            Rts (WeightedBuf w (R.F k) (S k) t ω) s) -
            (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).2.1‖ ^ 2)) s hs) fin4
      have := key _ ENNReal.toReal_nonneg t3
      have := key _ ENNReal.toReal_nonneg t4
      linarith
    have hθ0 : 0 ≤ thetaB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) I :=
      Real.iSup_nonneg fun s => Real.iSup_nonneg fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hθ0]
    linarith

/-- Claim (i) of `lem:app-drift-targets`, snapshot `cr-2026-10-23`: `ϑ_B(I) → 0` under
`assum:app-setup-regime` with the EMA weights `emaW β` (`β` fixed by `R.hβ`), together with the
boundedness of the family over `I` (`BddAbove`). Instance of `lem_app_drift_targets_i_weights`.
`lem:app-drift-targets`, snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.659–673):
```latex
\begin{lemma}[Candidate-centered targets]\label{lem:app-drift-targets}
Under \cref{assum:app-setup-regime}, $\vartheta_B(I)\to0$. For a sample of
age $j$ and $s\in I$ define, with $x_j\defeq\emaw j^2q(-s)\in[0,q_I]$,
\begin{equation}\label{eqn:app-drift-targets}
\alpha_{1,j}^\star\defeq\emaw j\,f_{x_j}(d_j),\qquad
\alpha_{2,j}^\star\defeq\emaw j^2\,\sigma(-s)\,\psi_{x_j}(d_j).
\end{equation}
Then, with $e_B$ the sequence of \cref{lem:app-de-replace} and
$e_B^\star\defeq e_B+C_I\vartheta_B(I)\to0$,
\begin{equation}\label{eqn:app-drift-replace}
\norm{\alpha_{1,j}-\alpha_{1,j}^\star}_2\le\emaw j\,e_B^\star,\qquad
\norm{\alpha_{2,j}-\alpha_{2,j}^\star}_2\le\emaw j^2\,e_B^\star
\qquad(j\ge0,\ s\in I).
\end{equation}
\end{lemma}
```
-/
theorem lem_app_drift_targets_i (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) :
    (∀ k, BddAbove ((fun s => |sigmaB (emaW R.β) (R.F k) (S k) t s - (branchSol (Fw (emaW R.β)) (specOutFM (R.F k)) (specInFM (R.F k)) s).1|
        + |sigmaTildeB (emaW R.β) (R.F k) (S k) t s - (branchSol (Fw (emaW R.β)) (specOutFM (R.F k)) (specInFM (R.F k)) s).2.1|) '' I)) ∧
    Tendsto (fun k => thetaB (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) I)
      atTop (𝓝 0) :=
  lem_app_drift_targets_i_weights R P S t I hI hIpos (emaW R.β) (by have h0 := (R.F 0).hβ; rw [R.hβ 0] at h0; exact emaW_weightClass R.β h0)

/-- Pointwise change-of-centre bound for the deletion targets: `|f_x(d) − f_y(d)| ≤ |x − y| |d|³`
for `x, y ≥ 0` (the mean-value step behind the `α⋆` vs `α̌` comparison). -/
private lemma scr_fX_lip_x (x y d : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |fX x d - fX y d| ≤ |x - y| * |d| ^ 3 := by
  have hx' : 0 < 1 + x * d ^ 2 := by have := mul_nonneg hx (sq_nonneg d); linarith
  have hy' : 0 < 1 + y * d ^ 2 := by have := mul_nonneg hy (sq_nonneg d); linarith
  have hD : 1 ≤ (1 + x * d ^ 2) * (1 + y * d ^ 2) := by
    have h1 : 0 ≤ x * d ^ 2 := mul_nonneg hx (sq_nonneg d)
    have h2 : 0 ≤ y * d ^ 2 := mul_nonneg hy (sq_nonneg d)
    nlinarith [mul_nonneg h1 h2]
  have hE : fX x d - fX y d = (y - x) * d ^ 3 / ((1 + x * d ^ 2) * (1 + y * d ^ 2)) := by
    unfold fX
    field_simp
    ring
  rw [hE, abs_div, abs_mul, abs_of_pos (mul_pos hx' hy'), abs_pow, abs_sub_comm y x]
  exact div_le_self (by positivity) hD


private lemma scr_eLpNorm_le {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') (f : Ω' → ℝ)
    (hf : Measurable f) (c : ℝ) (hc : 0 ≤ c)
    (h : ∫⁻ ω, ENNReal.ofReal ((f ω) ^ 2) ∂P ≤ ENNReal.ofReal (c ^ 2)) :
    eLpNorm f 2 P ≤ ENNReal.ofReal c := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have hpt : ∀ ω, ‖f ω‖ₑ ^ (2 : ℝ) = ENNReal.ofReal ((f ω) ^ 2) := by
    intro ω
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    congr 1
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  simp_rw [hpt]
  calc (∫⁻ ω, ENNReal.ofReal ((f ω) ^ 2) ∂P) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal (c ^ 2)) ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal c := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      congr 1
      rw [← Real.sqrt_eq_rpow]
      exact Real.sqrt_sq hc

private lemma scr_lint_pow {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : Measurable f) (p : ℕ) (hp : 1 ≤ p) (K : ℝ) (hK : 0 ≤ K)
    (h : eLpNorm f (p : ENNReal) μ ≤ ENNReal.ofReal K) :
    ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ ≤ ENNReal.ofReal (K ^ p) := by
  have hp0 : ((p : ℕ) : ENNReal) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 (ENNReal.natCast_ne_top _)
    hf.aestronglyMeasurable, ENNReal.toReal_natCast] at h
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 := ENNReal.rpow_le_rpow h hpr.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpr.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hK hpr.le, Real.rpow_natCast] at h2
  refine le_trans (le_of_eq ?_) h2
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hpr.le,
    Real.rpow_natCast]

private lemma scr_ageD_meas {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'} {m n B : ℕ}
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    Measurable (ageD F S t j) := by
  have hdm : Measurable (fun x : Vec m × Vec n => resid F.A x) := by unfold resid; fun_prop
  have : ageD F S t j = fun ω => resid F.A (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω) := rfl
  rw [this]; exact hdm.comp (S.meas _ _)

/-- Moments of the age-`j` fresh scalar: `‖ |d_j|^p ‖_2 ≤ K_p`, uniformly in `(k, j)`. -/
private lemma scr_dpow {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n B : ℕ} (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (p : ℕ) (hp : 1 ≤ p) :
    eLpNorm (fun ω => |ageD F S t j ω| ^ p) 2 P ≤
      ENNReal.ofReal ((((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / p)) ^ p) := by
  have hx : Measurable (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) := S.meas _ _
  have hlaw : P.map (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) = gaussPair m n := by
    unfold gaussPair
    exact S.law (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hdm : Measurable (fun x : Vec m × Vec n => resid F.A x) := by unfold resid; fun_prop
  set K : ℝ := (((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / p)) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hmom := lem_app_de_moments_ii F.A F.hA p hp
  have hl := scr_lint_pow (gaussPair m n) (fun x => resid F.A x) hdm (2 * p) (by omega) K hK0
    (by simpa [hK] using hmom)
  have hint : ∫⁻ ω, ENNReal.ofReal (|ageD F S t j ω| ^ (2 * p)) ∂P ≤ ENNReal.ofReal (K ^ (2 * p)) := by
    calc ∫⁻ ω, ENNReal.ofReal (|ageD F S t j ω| ^ (2 * p)) ∂P
        = ∫⁻ y, ENNReal.ofReal (|resid F.A y| ^ (2 * p))
            ∂(P.map (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB))) :=
          (lintegral_map (ENNReal.measurable_ofReal.comp (hdm.abs.pow_const _)) hx).symm
      _ ≤ _ := by rw [hlaw]; exact hl
  refine scr_eLpNorm_le P _ ((scr_ageD_meas F S t j).abs.pow_const p) _ (by positivity) ?_
  have e1 : ∀ ω, ((|ageD F S t j ω| ^ p) ^ 2) = |ageD F S t j ω| ^ (2 * p) := fun ω => by
    rw [← pow_mul, mul_comm]
  have e2 : (K ^ p) ^ 2 = K ^ (2 * p) := by rw [← pow_mul, mul_comm]
  simp_rw [e1, e2]
  exact hint


private lemma scr_psi_le (x d : ℝ) (hx : 0 ≤ x) : |psiX x d| ≤ d ^ 2 := by
  have hx' : 0 < 1 + x * d ^ 2 := by have := mul_nonneg hx (sq_nonneg d); linarith
  unfold psiX
  rw [abs_of_nonneg (by positivity)]
  exact div_le_self (sq_nonneg d) (by have := mul_nonneg hx (sq_nonneg d); linarith)

private lemma scr_psi_lip_x (x y d : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |psiX x d - psiX y d| ≤ |x - y| * d ^ 4 := by
  have hx' : 0 < 1 + x * d ^ 2 := by have := mul_nonneg hx (sq_nonneg d); linarith
  have hy' : 0 < 1 + y * d ^ 2 := by have := mul_nonneg hy (sq_nonneg d); linarith
  have hD : 1 ≤ (1 + x * d ^ 2) * (1 + y * d ^ 2) := by
    have h1 : 0 ≤ x * d ^ 2 := mul_nonneg hx (sq_nonneg d)
    have h2 : 0 ≤ y * d ^ 2 := mul_nonneg hy (sq_nonneg d)
    nlinarith [mul_nonneg h1 h2]
  have hE : psiX x d - psiX y d = (y - x) * d ^ 4 / ((1 + x * d ^ 2) * (1 + y * d ^ 2)) := by
    unfold psiX
    field_simp
    ring
  have h4 : (0 : ℝ) ≤ d ^ 4 := by positivity
  rw [hE, abs_div, abs_mul, abs_of_pos (mul_pos hx' hy'), abs_of_nonneg h4, abs_sub_comm y x]
  exact div_le_self (by positivity) hD

private lemma scr_E1_pt (wj x1 x2 d c : ℝ) (hw0 : 0 ≤ wj) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2)
    (hx : |x1 - x2| ≤ c) :
    |wj * fX x1 d - wj * fX x2 d| ≤ wj * c * |d| ^ 3 := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hw0, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hw0
  exact (scr_fX_lip_x x1 x2 d hx1 hx2).trans (mul_le_mul_of_nonneg_right hx (by positivity))

private lemma scr_E2_pt (wj σB σ x1 x2 d θ Cs c : ℝ) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2)
    (hσB : |σB - σ| ≤ θ) (hσ0 : 0 ≤ σ) (hσ : σ ≤ Cs) (hx : |x1 - x2| ≤ c) :
    |wj ^ 2 * σB * psiX x1 d - wj ^ 2 * σ * psiX x2 d|
      ≤ wj ^ 2 * θ * d ^ 2 + wj ^ 2 * (Cs * c) * d ^ 4 := by
  have e : wj ^ 2 * σB * psiX x1 d - wj ^ 2 * σ * psiX x2 d
      = wj ^ 2 * ((σB - σ) * psiX x1 d + σ * (psiX x1 d - psiX x2 d)) := by ring
  rw [e, abs_mul, abs_of_nonneg (sq_nonneg wj)]
  have h1 : |(σB - σ) * psiX x1 d| ≤ θ * d ^ 2 := by
    rw [abs_mul]
    exact mul_le_mul hσB (scr_psi_le x1 d hx1) (abs_nonneg _) ((abs_nonneg _).trans hσB)
  have h2 : |σ * (psiX x1 d - psiX x2 d)| ≤ (Cs * c) * d ^ 4 := by
    rw [abs_mul, abs_of_nonneg hσ0]
    have := (scr_psi_lip_x x1 x2 d hx1 hx2).trans (mul_le_mul_of_nonneg_right hx (by positivity))
    exact (mul_le_mul hσ this (abs_nonneg _) (hσ0.trans hσ)).trans_eq (by ring)
  have h3 := (abs_add_le _ _).trans (add_le_add h1 h2)
  calc wj ^ 2 * |(σB - σ) * psiX x1 d + σ * (psiX x1 d - psiX x2 d)|
      ≤ wj ^ 2 * (θ * d ^ 2 + (Cs * c) * d ^ 4) := mul_le_mul_of_nonneg_left h3 (sq_nonneg wj)
    _ = _ := by ring

/-- Two-term `L²` comparison from a pointwise bound. -/
private lemma scr_l2_two {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω')
    (E h1 h2 : Ω' → ℝ) (c1 c2 K1 K2 : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hE : Measurable E)
    (hpt : ∀ ω, |E ω| ≤ c1 * h1 ω + c2 * h2 ω)
    (hh1 : eLpNorm h1 2 P ≤ ENNReal.ofReal K1) (hh2 : eLpNorm h2 2 P ≤ ENNReal.ofReal K2) :
    eLpNorm E 2 P ≤ ENNReal.ofReal (c1 * K1 + c2 * K2) := by
  have hle : eLpNorm E 2 P ≤ eLpNorm (fun ω => c1 * h1 ω + c2 * h2 ω) 2 P := by
    refine eLpNorm_mono_real hE.aestronglyMeasurable fun ω => ?_
    rw [Real.norm_eq_abs]; exact hpt ω
  refine hle.trans ?_
  have e : (fun ω => c1 * h1 ω + c2 * h2 ω) = (c1 • h1) + (c2 • h2) := by
    funext ω; simp [smul_eq_mul]
  rw [e]
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  rw [eLpNorm_const_smul, eLpNorm_const_smul, Real.enorm_eq_ofReal hc1, Real.enorm_eq_ofReal hc2,
    ENNReal.ofReal_add (mul_nonneg hc1 hK1) (mul_nonneg hc2 hK2),
    ENNReal.ofReal_mul hc1, ENNReal.ofReal_mul hc2]
  gcongr


private lemma scr_le_iSup_mem (f : ℝ → ℝ) (I : Set ℝ) (hb : BddAbove (f '' I)) (s : ℝ)
    (hs : s ∈ I) : f s ≤ ⨆ s ∈ I, f s := by
  obtain ⟨M, hM⟩ := hb
  have hM' : ∀ s ∈ I, f s ≤ M := fun s hs => hM ⟨s, hs, rfl⟩
  have hbdd : BddAbove (Set.range fun s => ⨆ (_ : s ∈ I), f s) := by
    refine ⟨max M 0, ?_⟩
    rintro _ ⟨s', rfl⟩
    show (⨆ (_ : s' ∈ I), f s') ≤ max M 0
    by_cases h : s' ∈ I
    · rw [ciSup_pos h]; exact (hM' s' h).trans (le_max_left _ _)
    · haveI : IsEmpty (s' ∈ I) := ⟨h⟩
      rw [Real.iSup_of_isEmpty]; exact le_max_right _ _
  calc f s = ⨆ (_ : s ∈ I), f s := by rw [ciSup_pos hs]
    _ ≤ ⨆ s ∈ I, f s := le_ciSup hbdd s

private lemma scr_q_diff (s σB σ σtB σt Cg θ1 θ2 : ℝ) (hs : 0 < s)
    (h1 : |σB - σ| ≤ θ1) (h2 : |σtB - σt| ≤ θ2)
    (hσ0 : 0 ≤ σ) (hσtB0 : 0 ≤ σtB) (hσ : σ ≤ Cg / s) (hσtB : σtB ≤ Cg / s) :
    |s * σB * σtB - s * σ * σt| ≤ Cg * (θ1 + θ2) := by
  have e : s * σB * σtB - s * σ * σt = s * ((σB - σ) * σtB + σ * (σtB - σt)) := by ring
  rw [e, abs_mul, abs_of_pos hs]
  have a1 : |(σB - σ) * σtB| ≤ θ1 * (Cg / s) := by
    rw [abs_mul, abs_of_nonneg hσtB0]
    exact mul_le_mul h1 hσtB hσtB0 ((abs_nonneg _).trans h1)
  have a2 : |σ * (σtB - σt)| ≤ (Cg / s) * θ2 := by
    rw [abs_mul, abs_of_nonneg hσ0]
    exact mul_le_mul hσ h2 (abs_nonneg _) (hσ0.trans hσ)
  have a3 := (abs_add_le _ _).trans (add_le_add a1 a2)
  calc s * |(σB - σ) * σtB + σ * (σtB - σt)| ≤ s * (θ1 * (Cg / s) + (Cg / s) * θ2) :=
        mul_le_mul_of_nonneg_left a3 hs.le
    _ = Cg * (θ1 + θ2) := by field_simp

/-- General-weight form of claim (ii) of `lem:app-drift-targets`, snapshot `cr-2026-10-23`
(card rule (a), §6.1). For `WeightClass w` under `assum:app-setup-regime`: there is a sequence
`e^⋆ → 0` with, for all `k`, `j ≥ 0`, `s ∈ I`, `‖α_{1,j} − α⋆_{1,j}‖_2 ≤ w_j e^⋆` and
`‖α_{2,j} − α⋆_{2,j}‖_2 ≤ w_j² e^⋆`. The EMA record is the instance at `emaW R.β`. -/
theorem lem_app_drift_targets_ii_weights (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) (w : ℕ → ℝ) (hw : WeightClass w) :
    ∃ eStar : ℕ → ℝ, Tendsto eStar atTop (𝓝 0) ∧
      ∀ k : ℕ, ∀ j : ℕ, ∀ s ∈ I,
        eLpNorm (fun ω => delAlpha1 w (R.F k) (S k) t j s ω
            - alphaStar1 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
          2 (P k) ≤ ENNReal.ofReal (w j * eStar k) ∧
        eLpNorm (fun ω => delAlpha2 w (R.F k) (S k) t j s ω
            - alphaStar2 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
          2 (P k) ≤ ENNReal.ofReal (w j ^ 2 * eStar k) := by
  classical
  set γ' : ℝ := max R.γstar 1 with hγ'
  have hC0 : 0 < R.CSig := lt_of_lt_of_le one_pos R.hC
  have hγ0 : 0 < γ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hνo : ∀ k, ((specOutFM (R.F k) : FiniteMeasure ℝ) : Measure ℝ) =
      nuOut (R.F k).C (R.B k) := fun k => rfl
  have hνi : ∀ k, ((specInFM (R.F k) : FiniteMeasure ℝ) : Measure ℝ) =
      nuIn (R.F k).C (R.B k) := fun k => rfl
  have hK : ∀ k, (specOutFM (R.F k), specInFM (R.F k)) ∈ classK R.CSig γ' := by
    intro k
    obtain ⟨o1, o2⟩ := assum_app_setup_regime_nuOut R k
    obtain ⟨i1, i2⟩ := assum_app_setup_regime_nuIn R k
    have hle : ENNReal.ofReal R.γstar ≤ ENNReal.ofReal γ' :=
      ENNReal.ofReal_le_ofReal (le_max_left _ _)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hνo k]; exact (measure_mono (Set.subset_univ _)).trans (o2.trans hle)
    · rw [hνo k]; exact o1
    · rw [hνi k]; exact (measure_mono (Set.subset_univ _)).trans (i2.trans hle)
    · rw [hνi k]; exact i1
  obtain ⟨sm, hsm, hsmI⟩ : ∃ sm : ℝ, 0 < sm ∧ ∀ s ∈ I, sm ≤ s := by
    rcases I.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨sInf I, hIpos (hI.sInf_mem h), fun s hs => csInf_le hI.bddBelow hs⟩
  have hdm : ∀ k, (R.m k : ℝ) ≤ γ' * (R.B k : ℝ) := fun k =>
    (le_trans (Nat.cast_le.mpr (le_max_left _ _)) (R.dims k)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  have hdn : ∀ k, (R.n k : ℝ) ≤ γ' * (R.B k : ℝ) := fun k =>
    (le_trans (Nat.cast_le.mpr (le_max_right _ _)) (R.dims k)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  have hq : ∀ k, ∀ s ∈ I, 0 ≤ sigmaB w (R.F k) (S k) t s ∧
      sigmaB w (R.F k) (S k) t s ≤ R.CSig * γ' / s ∧
      0 ≤ sigmaTildeB w (R.F k) (S k) t s ∧
      sigmaTildeB w (R.F k) (S k) t s ≤ R.CSig * γ' / s ∧ 0 ≤ qB w (R.F k) (S k) t s := by
    intro k s hs
    obtain ⟨a1, a2, a3, a4, a5, -⟩ := eqn_app_de_qI w hw (R.F k) (S k) t R.CSig γ' sm I hsm hsmI
      ⟨R.normOut k, R.normIn k⟩ ⟨hdm k, hdn k⟩ s hs
    exact ⟨a1, a2, a3, a4, a5⟩
  have hbr : ∀ k, ∀ s ∈ I,
      0 ≤ (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).1 ∧
      (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).1 ≤ R.CSig * γ' / s ∧
      0 ≤ (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).2.1 ∧
      (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).2.1 ≤ R.CSig * γ' / s := by
    intro k s hs
    have hpos : 0 < s := hIpos hs
    have hsol := branchSol_spec (Fw_admissible hw.1) hC0 hγ0 (hK k) hpos
    have hb := ((thm_app_de_branch_i (Fw_admissible hw.1) hC0 hγ0 _ _ (hK k) s hpos).2 _ hsol)
    have hnn : ∀ x : ℝ × ℝ × ℝ × ℝ, IsBranchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s x →
        0 ≤ x.1 ∧ 0 ≤ x.2.1 := by
      rintro ⟨σ, σ', a, c⟩ h
      simp only [IsBranchSol] at h
      exact ⟨h.1, h.2.1⟩
    have hn := hnn _ hsol
    refine ⟨hn.1, ?_, hn.2, ?_⟩
    · have := hb.1; rwa [mul_comm] at this
    · have := hb.2.1; rwa [mul_comm] at this
  obtain ⟨hbdd, hθt⟩ := lem_app_drift_targets_i_weights R P S t I hI hIpos w hw
  obtain ⟨e, he, hrep⟩ := lem_app_de_replace I hI hIpos R.CSig γ'
  have hw1 : ∀ j, w j ≤ 1 := hw.2.1
  have hw0 : ∀ j, 0 ≤ w j := fun j => hw.1.1 j
  have hw2 : ∀ j, w j ^ 2 ≤ 1 := fun j => by
    have := pow_le_pow_left₀ (hw0 j) (hw1 j) 2
    simpa using this
  obtain ⟨K2, hK2, hK2b⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ (k j : ℕ),
      eLpNorm (fun ω => |ageD (R.F k) (S k) t j ω| ^ 2) 2 (P k) ≤ ENNReal.ofReal K :=
    ⟨_, by positivity, fun k j => scr_dpow (P k) (R.F k) (S k) t j 2 (by norm_num)⟩
  obtain ⟨K3, hK3, hK3b⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ (k j : ℕ),
      eLpNorm (fun ω => |ageD (R.F k) (S k) t j ω| ^ 3) 2 (P k) ≤ ENNReal.ofReal K :=
    ⟨_, by positivity, fun k j => scr_dpow (P k) (R.F k) (S k) t j 3 (by norm_num)⟩
  obtain ⟨K4, hK4, hK4b⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ (k j : ℕ),
      eLpNorm (fun ω => |ageD (R.F k) (S k) t j ω| ^ 4) 2 (P k) ≤ ENNReal.ofReal K :=
    ⟨_, by positivity, fun k j => scr_dpow (P k) (R.F k) (S k) t j 4 (by norm_num)⟩
  set Cg : ℝ := R.CSig * γ' with hCg
  have hCg0 : 0 ≤ Cg := by positivity
  set Cs : ℝ := Cg / sm with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  set Cstar : ℝ := 2 * (Cg * K3 + (K2 + Cs * Cg * K4)) with hCstar
  have hCstar0 : 0 ≤ Cstar := by positivity
  refine ⟨fun k => max (e (R.B k)) 0 + Cstar *
    thetaB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) I, ?_, ?_⟩
  · have h0 : Tendsto (fun k => max (e (R.B k)) 0) atTop (𝓝 (max 0 0)) :=
      (he.comp R.prop.B_top).max tendsto_const_nhds
    have := h0.add (hθt.const_mul Cstar)
    simpa using this
  intro k j s hs
  have hspos : 0 < s := hIpos hs
  set θ := thetaB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) I with hθdef
  have hθ0 : 0 ≤ θ :=
    Real.iSup_nonneg fun s => Real.iSup_nonneg fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hterm := scr_le_iSup_mem (fun s => |sigmaB w (R.F k) (S k) t s -
      (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).1|
      + |sigmaTildeB w (R.F k) (S k) t s -
      (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).2.1|) I (hbdd k) s hs
  have hθs : |sigmaB w (R.F k) (S k) t s -
      (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).1|
      + |sigmaTildeB w (R.F k) (S k) t s -
      (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).2.1| ≤ θ := hterm
  have hΔ1 : |sigmaB w (R.F k) (S k) t s -
      (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).1| ≤ θ := by
    have := abs_nonneg (sigmaTildeB w (R.F k) (S k) t s -
      (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).2.1)
    linarith
  have hΔ2 : |sigmaTildeB w (R.F k) (S k) t s -
      (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).2.1| ≤ θ := by
    have := abs_nonneg (sigmaB w (R.F k) (S k) t s -
      (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).1)
    linarith
  obtain ⟨a1, a2, a3, a4, a5⟩ := hq k s hs
  obtain ⟨b1, b2, b3, b4⟩ := hbr k s hs
  have hqd : |qB w (R.F k) (S k) t s - branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s|
      ≤ Cg * (θ + θ) := by
    have := scr_q_diff s _ _ _ _ Cg θ θ hspos hΔ1 hΔ2 b1 a3 b2 a4
    exact this
  have hbq0 : 0 ≤ branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s := by
    unfold branchQ; positivity
  set x1 := w j ^ 2 * qB w (R.F k) (S k) t s with hx1
  set x2 := xJ w (specOutFM (R.F k)) (specInFM (R.F k)) j s with hx2
  have hx10 : 0 ≤ x1 := mul_nonneg (sq_nonneg _) a5
  have hx20 : 0 ≤ x2 := mul_nonneg (sq_nonneg _) hbq0
  have hxd : |x1 - x2| ≤ Cg * (θ + θ) := by
    have e1 : x1 - x2 = w j ^ 2 * (qB w (R.F k) (S k) t s -
        branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s) := by
      rw [hx1, hx2]; unfold xJ; ring
    rw [e1, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc w j ^ 2 * |qB w (R.F k) (S k) t s - branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s|
        ≤ 1 * (Cg * (θ + θ)) := mul_le_mul (hw2 j) hqd (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hd := scr_ageD_meas (R.F k) (S k) t j
  obtain ⟨hD1, hD2, -⟩ := hrep (R.m k) (R.n k) (R.B k) w hw (Ω k) (P k) (R.F k) (S k) t
    (R.normOut k) (R.normIn k) (hdm k) (hdn k) j s hs
  have hem : ENNReal.ofReal (w j * e (R.B k)) ≤ ENNReal.ofReal (w j * max (e (R.B k)) 0) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_max_left _ _) (hw0 j))
  have hem2 : ENNReal.ofReal (w j ^ 2 * e (R.B k)) ≤ ENNReal.ofReal (w j ^ 2 * max (e (R.B k)) 0) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg _))
  have hmax0 : 0 ≤ max (e (R.B k)) 0 := le_max_right _ _
  constructor
  · -- claim for `α₁`
    have hE : eLpNorm (fun ω => checkAlpha1 w (R.F k) (S k) t j s ω
        - alphaStar1 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω) 2 (P k)
        ≤ ENNReal.ofReal (w j * (Cg * (θ + θ)) * K3 + 0 * K3) := by
      refine scr_l2_two (P k) _ (fun ω => |ageD (R.F k) (S k) t j ω| ^ 3)
        (fun ω => |ageD (R.F k) (S k) t j ω| ^ 3) _ 0 K3 K3
        (by have := hw0 j; positivity) le_rfl hK3 hK3 ?_ ?_ (hK3b k j) (hK3b k j)
      · unfold checkAlpha1 alphaStar1 fX
        fun_prop
      · intro ω
        have := scr_E1_pt (w j) x1 x2 (ageD (R.F k) (S k) t j ω) _ (hw0 j) hx10 hx20 hxd
        simpa [checkAlpha1, alphaStar1, hx1, hx2] using this
    have hsplit : (fun ω => delAlpha1 w (R.F k) (S k) t j s ω
        - alphaStar1 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
        = (fun ω => delAlpha1 w (R.F k) (S k) t j s ω - checkAlpha1 w (R.F k) (S k) t j s ω)
          + (fun ω => checkAlpha1 w (R.F k) (S k) t j s ω
        - alphaStar1 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω) := by
      funext ω; simp only [Pi.add_apply]; ring
    rw [hsplit]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    refine (add_le_add (hD1.trans hem) hE).trans ?_
    have hpos1 : 0 ≤ w j * max (e (R.B k)) 0 := mul_nonneg (hw0 j) hmax0
    have hpos2 : 0 ≤ w j * (Cg * (θ + θ)) * K3 + 0 * K3 := by
      have := hw0 j; positivity
    rw [← ENNReal.ofReal_add hpos1 hpos2]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ w j * θ * (K2 + Cs * Cg * K4) := by have := hw0 j; positivity
    nlinarith [this]
  · -- claim for `α₂`
    have hE : eLpNorm (fun ω => checkAlpha2 w (R.F k) (S k) t j s ω
        - alphaStar2 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω) 2 (P k)
        ≤ ENNReal.ofReal (w j ^ 2 * θ * K2 + w j ^ 2 * (Cs * (Cg * (θ + θ))) * K4) := by
      refine scr_l2_two (P k) _ (fun ω => |ageD (R.F k) (S k) t j ω| ^ 2)
        (fun ω => |ageD (R.F k) (S k) t j ω| ^ 4) _ _ K2 K4
        (by positivity) (by have := hCs0; positivity) hK2 hK4 ?_ ?_ (hK2b k j) (hK4b k j)
      · unfold checkAlpha2 alphaStar2 psiX
        fun_prop
      · intro ω
        have := scr_E2_pt (w j) (sigmaB w (R.F k) (S k) t s)
          (branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s) x1 x2
          (ageD (R.F k) (S k) t j ω) θ Cs (Cg * (θ + θ)) hx10 hx20 hΔ1 b1
          ((b2.trans (div_le_div_of_nonneg_left hCg0 hsm (hsmI s hs)))) hxd
        have e2 : |ageD (R.F k) (S k) t j ω| ^ 2 = ageD (R.F k) (S k) t j ω ^ 2 := sq_abs _
        have e4 : |ageD (R.F k) (S k) t j ω| ^ 4 = ageD (R.F k) (S k) t j ω ^ 4 := by
          rw [← abs_pow, abs_of_nonneg (by positivity)]
        rw [e2, e4]
        simpa [checkAlpha2, alphaStar2, hx1, hx2] using this
    have hsplit : (fun ω => delAlpha2 w (R.F k) (S k) t j s ω
        - alphaStar2 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
        = (fun ω => delAlpha2 w (R.F k) (S k) t j s ω - checkAlpha2 w (R.F k) (S k) t j s ω)
          + (fun ω => checkAlpha2 w (R.F k) (S k) t j s ω
        - alphaStar2 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω) := by
      funext ω; simp only [Pi.add_apply]; ring
    rw [hsplit]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    refine (add_le_add (hD2.trans hem2) hE).trans ?_
    have hpos1 : 0 ≤ w j ^ 2 * max (e (R.B k)) 0 := mul_nonneg (sq_nonneg _) hmax0
    have hpos2 : 0 ≤ w j ^ 2 * θ * K2 + w j ^ 2 * (Cs * (Cg * (θ + θ))) * K4 := by positivity
    rw [← ENNReal.ofReal_add hpos1 hpos2]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 0 ≤ w j ^ 2 * θ * (Cg * K3) := by positivity
    have h2 : 0 ≤ w j ^ 2 * θ * K2 := by positivity
    nlinarith [h1, h2]

/-- Claim (ii) of `lem:app-drift-targets`, snapshot `cr-2026-10-23`: for `e_B^⋆ = e_B + C_I ϑ_B(I)`
(existential, see the module doc) there is a sequence `e^⋆ → 0` such that for every `k`, age
`j ≥ 0` and `s ∈ I`, `‖α_{1,j} − α⋆_{1,j}‖_2 ≤ w_j e^⋆` and `‖α_{2,j} − α⋆_{2,j}‖_2 ≤ w_j² e^⋆`,
with `w = emaW β`. Instance of `lem_app_drift_targets_ii_weights`.
`lem:app-drift-targets`, snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.659–673):
```latex
\begin{lemma}[Candidate-centered targets]\label{lem:app-drift-targets}
Under \cref{assum:app-setup-regime}, $\vartheta_B(I)\to0$. For a sample of
age $j$ and $s\in I$ define, with $x_j\defeq\emaw j^2q(-s)\in[0,q_I]$,
\begin{equation}\label{eqn:app-drift-targets}
\alpha_{1,j}^\star\defeq\emaw j\,f_{x_j}(d_j),\qquad
\alpha_{2,j}^\star\defeq\emaw j^2\,\sigma(-s)\,\psi_{x_j}(d_j).
\end{equation}
Then, with $e_B$ the sequence of \cref{lem:app-de-replace} and
$e_B^\star\defeq e_B+C_I\vartheta_B(I)\to0$,
\begin{equation}\label{eqn:app-drift-replace}
\norm{\alpha_{1,j}-\alpha_{1,j}^\star}_2\le\emaw j\,e_B^\star,\qquad
\norm{\alpha_{2,j}-\alpha_{2,j}^\star}_2\le\emaw j^2\,e_B^\star
\qquad(j\ge0,\ s\in I).
\end{equation}
\end{lemma}
```
-/
theorem lem_app_drift_targets_ii (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) :
    ∃ eStar : ℕ → ℝ, Tendsto eStar atTop (𝓝 0) ∧
      ∀ k : ℕ, ∀ j : ℕ, ∀ s ∈ I,
        eLpNorm (fun ω => delAlpha1 (emaW R.β) (R.F k) (S k) t j s ω
            - alphaStar1 (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
          2 (P k) ≤ ENNReal.ofReal (emaW R.β j * eStar k) ∧
        eLpNorm (fun ω => delAlpha2 (emaW R.β) (R.F k) (S k) t j s ω
            - alphaStar2 (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
          2 (P k) ≤ ENNReal.ofReal (emaW R.β j ^ 2 * eStar k) :=
  lem_app_drift_targets_ii_weights R P S t I hI hIpos (emaW R.β) (by have h0 := (R.F 0).hβ; rw [R.hβ 0] at h0; exact emaW_weightClass R.β h0)

end Muon.Drift

import Mathlib
import Muon.Phase.CommonDrift
import Muon.Isotropic.Aspect
import Muon.Isotropic.Helpers
import Muon.Isotropic.Measure

/-!
# Appendix H: the isotropic ratio and the isotropic comparison (task L-H.12)

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`:
`eqn:app-phase-iso-arrays` and `eqn:app-phase-NB` (l.641–664), `prop:app-phase-iso-ratio` (l.666–678),
`def:app-phase-scalar` (l.702–711), `lem:app-phase-ratio-integral` (l.724–737),
`thm:app-phase-iso-extrema` (l.805–817), `thm:app-phase-iso` (l.880–908).
Card: `sections/07-phase-comparison/CARD.md` §2, §3, §5 (L-H.12), §6 items 3, 7, 10. The card's two
modules `IsoRatio` and `IsoComparison` are merged into this one file (scope of the work package).
`cor:app-phase-iso-one` belongs to L-H.18 and is not here.

Reused, not redefined: `Muon.Phase.RowModel`, `RowModel.S`, `RowModel.F0`, `RowModel.risk`,
`Muon.Phase.firstHit`, `Muon.Phase.IsGlobalRowSolution`, `Muon.Phase.thm_app_phase_matched`
(the consumer of the matched formula, used only in the proofs), `Muon.Isotropic.isoPhi`
(`Φ`, `Muon.Isotropic.Helpers`) and `Muon.Isotropic.isoNegStieltjes` (`σ(t) = ∫(x+t)^{-1}dμ`,
`Muon.Isotropic.Aspect`). The two Isotropic definitions are imported because
`Muon.Isotropic.Measure.isoPair_square_iff` is stated with them; `def_app_phase_scalar` uses the
same two expressions, so that the two predicates agree term by term.

New local declarations: the inverse `isoV` of `Φ` on `(0,1)`, `isoW` (`w`), `isoWcirc` (`w_∘`),
`isoI` (`I(γ)`), `isoDriftConst` (`C(γ)` in the measure-free form `eqn:app-phase-CI`), `isoRho`
(`ρ(γ)`), `isoA`, `isoD` (`𝒜`, `𝒟`), and the predicate `IsIsoSetting`, which packages the
isotropic arrays `eqn:app-phase-iso-arrays` with the bounds `eqn:app-phase-NB` as hypotheses.

Interface choices (faithfulness notes):
* `C(γ)` is `isoDriftConst γ := √2/(πγ²) · I(γ)`, the declaration of record of CARD §6.7. The
  measure-based definition `(√2γ²)⁻¹∫√x dμ` is an identity proved by `lem_app_phase_ratio_integral`
  for every measure satisfying `def_app_phase_scalar`; it is not used as a definition.
* `N_B` is the real parameter `NB`, with the two-sided bound `eqn:app-phase-NB` as hypotheses in
  `IsIsoSetting`. It is instantiated at `Muon.SignSGD.batchConst` only in L-H.18.
* The isotropic arrays are two `RowModel (Fin N)` values. Their coefficients are fixed by the
  equations of `eqn:app-phase-iso-arrays` (`μ_i = 1`, common `d_i`, the sum of `v_i`), with
  `v_i` otherwise arbitrary (CARD §2: only `∑ 𝔳_i` is specified). The common initial energies are
  `Q0`; both models are run at the matched step `2√ε/𝒮`.
* Hitting times are `firstHit` in `ℝ≥0∞`. The ratio clauses use `toReal` and state finiteness
  explicitly (`≠ ⊤`), since a top value would make the equation false.
* The integrability of `√x` against `μ` is an explicit conjunct of `lem_app_phase_ratio_integral`:
  the paper's proof shows the half moment is finite, and the Bochner integral of a non-integrable
  function is `0` in Lean.
* `thm_app_phase_iso`(i): the paper's "as `ε/F₀ → 0`, uniformly in `N`, `B` and `C(γ)`" is written
  as `∀ δ > 0, ∃ θ > 0, ∀ N B NB ε mS mN, …, ε/F₀ < θ → …`, with `T` fixed beforehand. The model
  quantifier ranges over all isotropic settings (this includes every `C(γ)`).
* `thm_app_phase_iso`(ii): the limit order of CARD §6.3 is made explicit: the first display needs
  `B → ∞` and `ε/F₀ → 0` jointly; the ratio statement needs `B → ∞` only; the limit
  `γ → γ₀` is `|N/B − γ₀| < η` with `B ≥ B₀`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open Muon.Isotropic (isoNegStieltjes isoPhi)

noncomputable section

namespace Muon.Phase

/-! ## The scalar measure hypothesis -/

/-- The scalar measure hypothesis at `γ` for a measure `μ` (`def:app-phase-scalar`, l.702–711):
`μ` is a finite nonnegative measure on `[0,∞)` of mass `γ`, and its transform
`σ_μ(t) = ∫(x+t)^{-1} μ(dx)` satisfies `γ − t σ_μ(t) = Φ(t σ_μ(t)²)` for `t > 0`. The standing
hypothesis `γ > 0` of the definition is carried by the lemmas that use it. The conjunction is
the right-hand side of `Muon.Isotropic.isoPair_square_iff`, term by term.

LaTeX (verbatim, `section.tex` l.702–711):
```
\begin{definition}[Scalar measure hypothesis]\label{def:app-phase-scalar}
Let $\gamma>0$. The scalar measure hypothesis at $\gamma$ is the existence of
a finite nonnegative measure $\mu_\gamma$ on $[0,\infty)$ of mass $\gamma$
whose transform $\sigma_\gamma(t)\defeq\int(x+t)^{-1}\mu_\gamma(\dif x)$, $t>0$,
satisfies
\begin{equation}\label{eqn:app-phase-scalar}
\psi_\gamma(t)\defeq\gamma-t\,\sigma_\gamma(t)=\Phi\big(t\,\sigma_\gamma(t)^2\big)\qquad(t>0).
\end{equation}
Under it, $C(\gamma)\defeq(\sqrt2\,\gamma^2)^{-1}\int\sqrt x\,\mu_\gamma(\dif x)$.
\end{definition}
```
-/
def def_app_phase_scalar (γ : ℝ) (μ : Measure ℝ) : Prop :=
  μ univ = ENNReal.ofReal γ ∧ μ (Iio 0) = 0 ∧
    ∀ t : ℝ, 0 < t →
      γ - t * isoNegStieltjes μ t = isoPhi (t * isoNegStieltjes μ t ^ 2)

/-! ## Auxiliary functions of the isotropic drift constant -/

/-- The inverse `V` of `Φ` on `(0,1)`, extended by `Function.invFunOn` (`lem:app-phase-ratio-integral`). -/
def isoV (y : ℝ) : ℝ := Function.invFunOn isoPhi (Ioi 0) y

/-- `w(y) = V(y)^{-1/2}`. -/
def isoW (y : ℝ) : ℝ := (Real.sqrt (isoV y))⁻¹

/-- `w_∘(y) = √y · w(y)`. -/
def isoWcirc (y : ℝ) : ℝ := Real.sqrt y * isoW y

/-- `I(γ) = ∫_0^{min(γ,1)} (γ − y) w(y) dy` (`eqn:app-phase-CI`). -/
def isoI (γ : ℝ) : ℝ := ∫ y in (0 : ℝ)..min γ 1, (γ - y) * isoW y

/-- `C(γ) = (√2/(πγ²)) I(γ)` (`eqn:app-phase-CI`): the drift constant of the isotropic arrays,
in the measure-free form. -/
def isoDriftConst (γ : ℝ) : ℝ := Real.sqrt 2 / (Real.pi * γ ^ 2) * isoI γ

/-- `ρ(γ) = π C(γ)² γ max(1,γ)` (`prop:app-phase-iso-ratio`). -/
def isoRho (γ : ℝ) : ℝ := Real.pi * isoDriftConst γ ^ 2 * γ * max 1 γ

/-- `𝒜 = ∫_0^1 w(y) dy` (`eqn:app-phase-AD`). -/
def isoA : ℝ := ∫ y in (0 : ℝ)..1, isoW y

/-- `𝒟 = ∫_0^1 y w(y) dy` (`eqn:app-phase-AD`). -/
def isoD : ℝ := ∫ y in (0 : ℝ)..1, y * isoW y

/-! ## Private helpers for `lem_app_phase_ratio_integral` -/

private lemma rt_den_pos {v : ℝ} (hv : 0 ≤ v) (g : ℝ) : 0 < 1 + v * g ^ 2 := by
  have := mul_nonneg hv (sq_nonneg g)
  linarith

private lemma rt_gauss_compl_pos : (0 : ENNReal) < ProbabilityTheory.gaussianReal 0 1 ({(0 : ℝ)}ᶜ) := by
  have h0 : ProbabilityTheory.gaussianReal 0 1 {(0 : ℝ)} = 0 :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton
  have h1 : ProbabilityTheory.gaussianReal 0 1 ({(0 : ℝ)}ᶜ) = 1 := by
    rw [measure_compl (measurableSet_singleton 0) (by simp [h0]), h0]
    simp
  rw [h1]
  exact one_pos

private lemma rt_integral_pos {f : ℝ → ℝ} (h0 : ∀ g, 0 ≤ f g)
    (hfi : Integrable f (ProbabilityTheory.gaussianReal 0 1)) (hne : ∀ g : ℝ, g ≠ 0 → f g ≠ 0) :
    0 < ∫ g, f g ∂(ProbabilityTheory.gaussianReal 0 1) := by
  rw [integral_pos_iff_support_of_nonneg h0 hfi]
  refine lt_of_lt_of_le rt_gauss_compl_pos (measure_mono ?_)
  intro g hg
  exact Function.mem_support.mpr (hne g (by simpa using hg))

private lemma rt_deriv_cont {v : ℝ} (hv : 0 < v) :
    ContinuousAt Muon.Isotropic.isoPhiDeriv v := by
  unfold Muon.Isotropic.isoPhiDeriv
  refine continuousAt_of_dominated (bound := fun g => g ^ 2) ?_ ?_
    (Muon.Foundations.gaussian_integrable_pow 2) ?_
  · exact Filter.Eventually.of_forall fun x =>
      (by fun_prop : Measurable fun g : ℝ => g ^ 2 / (1 + x * g ^ 2) ^ 2).aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds hv] with x hx
    refine Filter.Eventually.of_forall fun g => ?_
    have hx' : 0 ≤ x := le_of_lt hx
    have hd : 0 < 1 + x * g ^ 2 := rt_den_pos hx' g
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply div_le_self (sq_nonneg g)
    nlinarith [mul_nonneg hx' (sq_nonneg g), sq_nonneg (x * g ^ 2)]
  · refine Filter.Eventually.of_forall fun g => ?_
    have hd : 1 + v * g ^ 2 ≠ 0 := (rt_den_pos hv.le g).ne'
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hd)

private lemma rt_contDiff_phi : ContDiffOn ℝ 1 Muon.Isotropic.isoPhi (Ioi 0) := by
  have hd := Muon.Isotropic.lem_app_iso_gaussian_ii.2.1
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun v hv => (hd v hv).1.differentiableAt.differentiableWithinAt, by simp, ?_⟩
  have h : EqOn (deriv Muon.Isotropic.isoPhi) Muon.Isotropic.isoPhiDeriv (Ioi 0) :=
    fun v hv => (hd v hv).1.deriv
  rw [contDiffOn_zero]
  exact (continuousOn_of_forall_continuousAt (fun v hv => rt_deriv_cont hv)).congr h

private lemma rt_phi_le {v : ℝ} (hv : 0 < v) : Muon.Isotropic.isoPhi v ≤ v := by
  linarith [(Muon.Isotropic.lem_app_iso_gaussian_iii v hv).1]

private lemma rt_surj : SurjOn Muon.Isotropic.isoPhi (Ioi 0) (Ioo 0 1) := by
  intro y hy
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hmono, -, hpos⟩ := Muon.Isotropic.lem_app_iso_gaussian_ii
  have hcont := rt_contDiff_phi.continuousOn
  obtain ⟨b, hb, hb0⟩ := ((Muon.Isotropic.lem_app_iso_gaussian_iv.2.eventually_const_lt hy1).and
    (eventually_gt_atTop 0)).exists
  set a := y / 2 with ha
  have ha0 : 0 < a := by positivity
  have hay : Muon.Isotropic.isoPhi a < y := by linarith [rt_phi_le ha0]
  have hab : a ≤ b := by
    by_contra h
    rw [not_le] at h
    have := hmono.monotoneOn (Set.mem_Ioi.2 hb0) (Set.mem_Ioi.2 ha0) h.le
    linarith
  have hsub : Icc a b ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le ha0 hx.1
  obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hab (hcont.mono hsub) ⟨hay.le, hb.le⟩
  exact ⟨x, hsub hx, hxy⟩

private lemma rt_bij : BijOn Muon.Isotropic.isoPhi (Ioi 0) (Ioo 0 1) := by
  obtain ⟨hmono, -, hpos⟩ := Muon.Isotropic.lem_app_iso_gaussian_ii
  exact ⟨fun v hv => hpos v hv, hmono.injOn, rt_surj⟩

private lemma rt_V_spec {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    isoV y ∈ Ioi 0 ∧ Muon.Isotropic.isoPhi (isoV y) = y :=
  Function.invFunOn_pos (rt_surj hy)

private lemma rt_V_phi {v : ℝ} (hv : 0 < v) : isoV (Muon.Isotropic.isoPhi v) = v := by
  have hy : Muon.Isotropic.isoPhi v ∈ Ioo (0 : ℝ) 1 := rt_bij.mapsTo hv
  obtain ⟨h1, h2⟩ := rt_V_spec hy
  exact (rt_bij.injOn h1 hv h2)

private lemma rt_V_strictMono : StrictMonoOn isoV (Ioo 0 1) := by
  intro y hy y' hy' hlt
  obtain ⟨h1, h2⟩ := rt_V_spec hy
  obtain ⟨h1', h2'⟩ := rt_V_spec hy'
  by_contra h
  rw [not_lt] at h
  have := (Muon.Isotropic.lem_app_iso_gaussian_ii.1).monotoneOn h1' h1 h
  linarith

private lemma rt_V_image : isoV '' Ioo 0 1 = Ioi 0 := by
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact (rt_V_spec hy).1
  · intro v hv
    exact ⟨_, rt_bij.mapsTo hv, rt_V_phi hv⟩

private lemma rt_V_cont {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : ContinuousAt isoV y := by
  refine continuousAt_of_monotoneOn_of_image_mem_nhds rt_V_strictMono.monotoneOn
    (Ioo_mem_nhds hy.1 hy.2) ?_
  rw [rt_V_image]
  exact Ioi_mem_nhds (rt_V_spec hy).1

private lemma rt_V_hasDeriv {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt isoV (Muon.Isotropic.isoPhiDeriv (isoV y))⁻¹ y := by
  obtain ⟨hmono, hd, hpos⟩ := Muon.Isotropic.lem_app_iso_gaussian_ii
  obtain ⟨h1, h2⟩ := rt_V_spec hy
  have hv : 0 < isoV y := h1
  refine HasDerivAt.of_local_left_inverse (rt_V_cont hy) (hd _ hv).1 (hd _ hv).2.1.ne' ?_
  filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
  exact (rt_V_spec hz).2

private lemma rt_contDiff_V : ContDiffOn ℝ 1 isoV (Ioo 0 1) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun y hy => (rt_V_hasDeriv hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  have h : EqOn (deriv isoV) (fun y => (Muon.Isotropic.isoPhiDeriv (isoV y))⁻¹) (Ioo 0 1) :=
    fun y hy => (rt_V_hasDeriv hy).deriv
  rw [contDiffOn_zero]
  refine ContinuousOn.congr ?_ h
  refine continuousOn_of_forall_continuousAt (fun y hy => ?_)
  have hv : 0 < isoV y := (rt_V_spec hy).1
  exact ((rt_deriv_cont hv).comp (rt_V_cont hy)).inv₀
    (Muon.Isotropic.lem_app_iso_gaussian_ii.2.1 _ hv).2.1.ne'

private lemma rt_J_bounded {v : ℝ} (hv : 0 < v) :
    Integrable (fun g : ℝ => g ^ 2 / (1 + v * g ^ 2)) (ProbabilityTheory.gaussianReal 0 1) := by
  refine Integrable.of_bound (by fun_prop : Measurable fun g : ℝ => g ^ 2 / (1 + v * g ^ 2)).aestronglyMeasurable
    (1 / v) (Filter.Eventually.of_forall fun g => ?_)
  have hd := rt_den_pos hv.le g
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_div_iff₀ hd hv]
  nlinarith [sq_nonneg g]

private lemma rt_J_anti {v u : ℝ} (hv : 0 < v) (hvu : v < u) :
    Muon.DetEquiv.J u < Muon.DetEquiv.J v := by
  have hu : 0 < u := hv.trans hvu
  have hint := (rt_J_bounded hv).sub (rt_J_bounded hu)
  have hpos : 0 < ∫ g, (g ^ 2 / (1 + v * g ^ 2) - g ^ 2 / (1 + u * g ^ 2))
      ∂(ProbabilityTheory.gaussianReal 0 1) := by
    refine rt_integral_pos (fun g => ?_) hint (fun g hg => ?_)
    · rw [sub_nonneg]
      exact div_le_div_of_nonneg_left (sq_nonneg g) (rt_den_pos hv.le g)
        (by nlinarith [sq_nonneg g])
    · have hg2 : 0 < g ^ 2 := by positivity
      have : g ^ 2 / (1 + u * g ^ 2) < g ^ 2 / (1 + v * g ^ 2) :=
        div_lt_div_of_pos_left hg2 (rt_den_pos hv.le g) (by nlinarith)
      linarith
  rw [integral_sub (rt_J_bounded hv) (rt_J_bounded hu)] at hpos
  unfold Muon.DetEquiv.J
  linarith

private lemma rt_phi_eq_J {v : ℝ} : Muon.Isotropic.isoPhi v = v * Muon.DetEquiv.J v := rfl

private lemma rt_J_pos_le {v : ℝ} (hv : 0 < v) : 0 < Muon.DetEquiv.J v ∧ Muon.DetEquiv.J v ≤ 1 := by
  have h1 := (Muon.Isotropic.lem_app_iso_gaussian_ii.2.2 v hv).1
  have h2 := rt_phi_le hv
  rw [rt_phi_eq_J] at h1 h2
  exact ⟨pos_of_mul_pos_right h1 hv.le, by nlinarith⟩

private lemma rt_wcirc_eq {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    isoWcirc y = Real.sqrt (Muon.DetEquiv.J (isoV y)) := by
  obtain ⟨hv, hphi⟩ := rt_V_spec hy
  have hv' : 0 < isoV y := hv
  have : Muon.DetEquiv.J (isoV y) = y / isoV y := by
    rw [eq_div_iff hv'.ne']
    have := hphi
    rw [rt_phi_eq_J] at this
    linarith
  rw [this, Real.sqrt_div hy.1.le, isoWcirc, isoW, div_eq_mul_inv]

private lemma rt_wcirc_bounds {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : 0 < isoWcirc y ∧ isoWcirc y ≤ 1 := by
  rw [rt_wcirc_eq hy]
  have := rt_J_pos_le (rt_V_spec hy).1
  exact ⟨Real.sqrt_pos.2 this.1, Real.sqrt_le_one.2 this.2⟩

private lemma rt_wcirc_anti : StrictAntiOn isoWcirc (Ioo 0 1) := by
  intro y hy y' hy' hlt
  rw [rt_wcirc_eq hy, rt_wcirc_eq hy']
  exact Real.sqrt_lt_sqrt (rt_J_pos_le (rt_V_spec hy').1).1.le
    (rt_J_anti (rt_V_spec hy).1 (rt_V_strictMono hy hy' hlt))

private lemma rt_V_tendsto : Tendsto isoV (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · refine tendsto_order.2 ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with y hy
      exact lt_trans ha' (rt_V_spec hy).1
    · have hp := Muon.Isotropic.lem_app_iso_gaussian_ii.2.2 a' ha'
      filter_upwards [Ioo_mem_nhdsGT hp.1] with y hy
      have hy' : y ∈ Ioo (0 : ℝ) 1 := ⟨hy.1, hy.2.trans hp.2⟩
      have := rt_V_strictMono hy' ⟨hp.1, hp.2⟩ hy.2
      rwa [rt_V_phi ha'] at this
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with y hy
    exact (rt_V_spec hy).1

private lemma rt_wcirc_tendsto : Tendsto isoWcirc (𝓝[>] 0) (𝓝 1) := by
  have h1 := Muon.Isotropic.lem_app_iso_gaussian_iv.1.comp rt_V_tendsto
  have h2 := (Real.continuous_sqrt.tendsto 1).comp h1
  rw [Real.sqrt_one] at h2
  refine h2.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with y hy
  rw [rt_wcirc_eq hy]
  have hv : 0 < isoV y := (rt_V_spec hy).1
  simp only [Function.comp]
  congr 1
  rw [rt_phi_eq_J, mul_div_cancel_left₀ _ hv.ne']

private lemma rt_Eabs : ∫ g : ℝ, |g| ∂(ProbabilityTheory.gaussianReal 0 1) = Real.sqrt (2 / Real.pi) := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hpt : (fun x : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 x • |x|)
      = fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹
          * (fun y : ℝ => y * Real.exp (-((1 / 2 : ℝ) * y ^ 2))) |x| := by
    funext x
    rw [ProbabilityTheory.gaussianPDFReal_def, smul_eq_mul]
    have hexp : -(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) = -((1 / 2 : ℝ) * |x| ^ 2) := by
      rw [sq_abs]; simp; ring
    simp only [hexp]
    simp only [NNReal.coe_one, mul_one]
    ring
  have hI : ∫ y in Ioi (0 : ℝ), y * Real.exp (-((1 / 2 : ℝ) * y ^ 2)) = 1 := by
    have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => -Real.exp (-((1 / 2 : ℝ) * y ^ 2)))
        (x * Real.exp (-((1 / 2 : ℝ) * x ^ 2))) x := by
      intro x _
      have h1 : HasDerivAt (fun y : ℝ => -((1 / 2 : ℝ) * y ^ 2)) (-((1 / 2 : ℝ) * (2 * x))) x := by
        have := ((hasDerivAt_pow 2 x).const_mul (1 / 2 : ℝ)).neg
        convert this using 1
        simp
      have := (h1.exp).neg
      convert this using 1
      ring
    have ht : Tendsto (fun y : ℝ => -Real.exp (-((1 / 2 : ℝ) * y ^ 2))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun y : ℝ => -((1 / 2 : ℝ) * y ^ 2)) atTop atBot := by
        refine tendsto_neg_atTop_atBot.comp ?_
        exact (tendsto_pow_atTop two_ne_zero).const_mul_atTop (by norm_num)
      simpa using (Real.tendsto_exp_atBot.comp h1).neg
    have hc : ContinuousWithinAt (fun y : ℝ => -Real.exp (-((1 / 2 : ℝ) * y ^ 2))) (Ici 0) 0 := by
      fun_prop
    have hint := integrableOn_Ioi_deriv_of_nonneg hc hd
      (fun x hx => mul_nonneg (le_of_lt hx) (Real.exp_pos _).le) ht
    rw [integral_Ioi_of_hasDerivAt_of_tendsto hc hd hint ht]
    simp
  rw [hpt, integral_const_mul, integral_comp_abs
    (f := fun y : ℝ => y * Real.exp (-((1 / 2 : ℝ) * y ^ 2))), hI]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hs2ne : Real.sqrt 2 ≠ 0 := by positivity
  rw [Real.sqrt_mul (by norm_num) Real.pi, Real.sqrt_div (by norm_num)]
  field_simp
  nlinarith [hs2]

private lemma rt_beta_aux {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun v : ℝ => c / (1 + v * c) ^ 2 * (Real.sqrt v)⁻¹) (Ioi 0) ∧
    ∫ v in Ioi (0 : ℝ), c / (1 + v * c) ^ 2 * (Real.sqrt v)⁻¹ = Real.pi / 2 * Real.sqrt c := by
  set a := Real.sqrt c with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 hc
  have ha2 : a ^ 2 = c := Real.sq_sqrt hc.le
  let F : ℝ → ℝ := fun v => a * (Real.arctan (a * Real.sqrt v) +
    a * Real.sqrt v / (1 + (a * Real.sqrt v) ^ 2))
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F (c / (1 + x * c) ^ 2 * (Real.sqrt x)⁻¹) x := by
    intro x hx
    have hx0 : 0 < x := hx
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    have hu : HasDerivAt (fun v : ℝ => a * Real.sqrt v) (a * (1 / (2 * Real.sqrt x))) x := by
      have := (Real.hasDerivAt_sqrt hx0.ne').const_mul a
      simpa using this
    have h1 := hu.arctan
    have hq : HasDerivAt (fun v : ℝ => 1 + (a * Real.sqrt v) ^ 2)
        (2 * (a * Real.sqrt x) * (a * (1 / (2 * Real.sqrt x)))) x := by
      have := (hu.pow 2).const_add 1
      simpa using this
    have h2 := hu.div hq (by positivity)
    have h3 := (h1.add h2).const_mul a
    convert h3 using 1
    rw [← ha2]
    have : x = Real.sqrt x ^ 2 := hs2.symm
    generalize Real.sqrt x = s at *
    subst this
    field_simp
    ring
  have ht : Tendsto F atTop (𝓝 (a * (Real.pi / 2))) := by
    have hu : Tendsto (fun v : ℝ => a * Real.sqrt v) atTop atTop :=
      Real.tendsto_sqrt_atTop.const_mul_atTop ha0
    have h1 := ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp hu)
    have h2 : Tendsto (fun v : ℝ => a * Real.sqrt v / (1 + (a * Real.sqrt v) ^ 2)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_inv_atTop_zero.comp hu) ?_ ?_
      · filter_upwards [hu.eventually_gt_atTop 0] with v hv
        positivity
      · filter_upwards [hu.eventually_gt_atTop 0] with v hv
        simp only [Function.comp]
        rw [div_le_iff₀ (by positivity)]
        have : (a * Real.sqrt v)⁻¹ * (1 + (a * Real.sqrt v) ^ 2)
            = (a * Real.sqrt v)⁻¹ + a * Real.sqrt v := by
          field_simp
        rw [this]
        have : 0 < (a * Real.sqrt v)⁻¹ := by positivity
        linarith
    have := (h1.add h2).const_mul a
    simpa using this
  have hc0 : ContinuousWithinAt F (Ici 0) 0 := by
    refine Continuous.continuousWithinAt ?_
    refine continuous_const.mul (Continuous.add (Real.continuous_arctan.comp (by fun_prop)) ?_)
    refine Continuous.div (by fun_prop) (by fun_prop) (fun x => ?_)
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg hc0 hd
    (fun x hx => by
      have : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
      positivity) ht
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hc0 hd hint ht]
  simp only [F]
  simp
  ring

private lemma rt_W_phi {v : ℝ} (hv : 0 < v) : isoW (Muon.Isotropic.isoPhi v) = (Real.sqrt v)⁻¹ := by
  rw [isoW, rt_V_phi hv]

private lemma rt_A_change :
    ∫ y in Ioo (0 : ℝ) 1, isoW y =
      ∫ v in Ioi (0 : ℝ), Muon.Isotropic.isoPhiDeriv v * (Real.sqrt v)⁻¹ := by
  obtain ⟨hmono, hd, hpos⟩ := Muon.Isotropic.lem_app_iso_gaussian_ii
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := Muon.Isotropic.isoPhi) (f' := Muon.Isotropic.isoPhiDeriv) measurableSet_Ioi
    (fun x hx => (hd x hx).1.hasDerivWithinAt) hmono.injOn isoW
  rw [rt_bij.image_eq] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
  simp only [smul_eq_mul]
  rw [abs_of_pos (hd v hv).2.1, rt_W_phi hv]

private lemma rt_A_fubini :
    ∫ v in Ioi (0 : ℝ), Muon.Isotropic.isoPhiDeriv v * (Real.sqrt v)⁻¹ = Real.sqrt (Real.pi / 2) := by
  set γ := ProbabilityTheory.gaussianReal 0 1 with hγ
  let f : ℝ → ℝ → ℝ := fun v g => g ^ 2 / (1 + v * g ^ 2) ^ 2 * (Real.sqrt v)⁻¹
  have hinner : ∀ g : ℝ, g ≠ 0 →
      IntegrableOn (fun v => f v g) (Ioi 0) ∧
      ∫ v in Ioi (0 : ℝ), f v g = Real.pi / 2 * |g| := by
    intro g hg
    have := rt_beta_aux (c := g ^ 2) (by positivity)
    rw [Real.sqrt_sq_eq_abs] at this
    exact this
  have hnn : ∀ v g, 0 ≤ f v g := fun v g => by
    simp only [f]; positivity
  have hmeas : Measurable (fun p : ℝ × ℝ => f p.1 p.2) := by
    simp only [f]; fun_prop
  have hint : Integrable (fun p : ℝ × ℝ => f p.1 p.2) ((volume.restrict (Ioi (0 : ℝ))).prod γ) := by
    rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun g => ?_, ?_⟩
    · by_cases hg : g = 0
      · subst hg
        simp [f]
      · exact (hinner g hg).1
    · have hgi : Integrable (fun g : ℝ => Real.pi / 2 * |g|) γ :=
        (by simpa using (Muon.Foundations.gaussian_integrable_pow 1).abs :
          Integrable (fun g : ℝ => |g|) γ).const_mul _
      refine hgi.congr (Filter.Eventually.of_forall fun g => ?_)
      by_cases hg : g = 0
      · subst hg
        simp [f]
      · show Real.pi / 2 * |g| = ∫ x in Ioi (0 : ℝ), ‖f x g‖
        rw [← (hinner g hg).2]
        refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (hnn v g)]
  have hswap := integral_integral_swap (f := f) hint
  have e1 : ∫ v in Ioi (0 : ℝ), Muon.Isotropic.isoPhiDeriv v * (Real.sqrt v)⁻¹ =
      ∫ v in Ioi (0 : ℝ), ∫ g, f v g ∂γ := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
    simp only [f]
    unfold Muon.Isotropic.isoPhiDeriv
    rw [← integral_mul_const]
  rw [e1]
  rw [hswap]
  have e2 : ∫ g, (∫ v in Ioi (0 : ℝ), f v g) ∂γ = ∫ g, Real.pi / 2 * |g| ∂γ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    by_cases hg : g = 0
    · subst hg
      simp [f]
    · exact (hinner g hg).2
  rw [e2, integral_const_mul, rt_Eabs]
  have hs : Real.sqrt (Real.pi / 2) ^ 2 = Real.pi / 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.2 (by positivity)
  rw [show 2 / Real.pi = (Real.pi / 2)⁻¹ by field_simp, Real.sqrt_inv]
  field_simp
  linarith

private lemma rt_W_pos {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : 0 < isoW y := by
  have := (rt_V_spec hy).1
  have h : 0 < isoV y := this
  rw [isoW]
  positivity

private lemma rt_W_le {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : isoW y ≤ (Real.sqrt y)⁻¹ := by
  have h1 := (rt_wcirc_bounds hy).2
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy.1
  rw [isoWcirc] at h1
  have : isoW y = (Real.sqrt y * isoW y) / Real.sqrt y := by field_simp
  rw [this, ← one_div]
  exact div_le_div_of_nonneg_right h1 hs.le

private lemma rt_W_cont : ContinuousOn isoW (Ioo 0 1) := by
  refine continuousOn_of_forall_continuousAt (fun y hy => ?_)
  have hv : 0 < isoV y := (rt_V_spec hy).1
  unfold isoW
  exact ((Real.continuous_sqrt.continuousAt.comp (rt_V_cont hy)).inv₀ (Real.sqrt_pos.2 hv).ne')

private lemma rt_W_integrableOn : IntegrableOn isoW (Ioo 0 1) := by
  have h1 : IntegrableOn (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  refine (h1.mono_set Ioo_subset_Ioc_self).mono' (rt_W_cont.aestronglyMeasurable measurableSet_Ioo) ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Filter.Eventually.of_forall fun y hy => ?_
  rw [Real.norm_eq_abs, abs_of_pos (rt_W_pos hy), Real.rpow_neg hy.1.le, ← Real.sqrt_eq_rpow]
  exact rt_W_le hy

private lemma rt_yW_integrableOn : IntegrableOn (fun y => y * isoW y) (Ioo 0 1) := by
  refine rt_W_integrableOn.mono' (by
    exact (continuousOn_id.mul rt_W_cont).aestronglyMeasurable measurableSet_Ioo) ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Filter.Eventually.of_forall fun y hy => ?_
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hy.1 (rt_W_pos hy))]
  nlinarith [rt_W_pos hy, hy.1, hy.2]

private lemma rt_W_ii : IntervalIntegrable isoW volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
    ((integrableOn_Ioc_iff_integrableOn_Ioo (μ := volume) (f := isoW) (a := 0) (b := 1)).2
      rt_W_integrableOn)

private lemma rt_yW_ii : IntervalIntegrable (fun y => y * isoW y) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
    ((integrableOn_Ioc_iff_integrableOn_Ioo (μ := volume) (f := fun y => y * isoW y) (a := 0)
      (b := 1)).2 rt_yW_integrableOn)

private lemma rt_isoA : isoA = Real.sqrt (Real.pi / 2) := by
  unfold isoA
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, rt_A_change,
    rt_A_fubini]

private lemma rt_isoD_pos : 0 < isoD :=
  intervalIntegral.intervalIntegral_pos_of_pos_on rt_yW_ii
    (fun y hy => mul_pos hy.1 (rt_W_pos hy)) zero_lt_one

private lemma rt_isoD_lt : isoD < isoA := by
  unfold isoD isoA
  have h := intervalIntegral.integral_sub rt_W_ii rt_yW_ii
  have hpos : 0 < ∫ y in (0 : ℝ)..1, (isoW y - y * isoW y) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (rt_W_ii.sub rt_yW_ii)
      (fun y hy => ?_) zero_lt_one
    have := rt_W_pos hy
    nlinarith [hy.2]
  linarith

private lemma rt_isoI_ge {γ : ℝ} (hγ : 1 ≤ γ) : isoI γ = γ * isoA - isoD := by
  unfold isoI isoA isoD
  rw [min_eq_right hγ]
  have h := intervalIntegral.integral_sub (rt_W_ii.const_mul γ) rt_yW_ii
  rw [intervalIntegral.integral_const_mul] at h
  rw [← h]
  congr 1
  funext y
  ring

private lemma rt_char {γ t ψ y : ℝ} (ht : 0 < t) (hψ0 : 0 < ψ) (hψ1 : ψ < 1) (hψγ : ψ < γ)
    (hV : isoV ψ * t = (γ - ψ) ^ 2) (hy : y ∈ Ioo (0 : ℝ) 1) (hyγ : y < γ) :
    y < ψ ↔ t < (γ - y) ^ 2 / isoV y := by
  have hVy : 0 < isoV y := (rt_V_spec hy).1
  rw [lt_div_iff₀ hVy]
  constructor
  · intro h
    have h1 : isoV y < isoV ψ := rt_V_strictMono hy ⟨hψ0, hψ1⟩ h
    have h2 : (γ - ψ) ^ 2 < (γ - y) ^ 2 := by nlinarith
    nlinarith
  · intro h
    by_contra hc
    rw [not_lt] at hc
    have h1 : isoV ψ ≤ isoV y := rt_V_strictMono.monotoneOn ⟨hψ0, hψ1⟩ hy hc
    have h2 : (γ - y) ^ 2 ≤ (γ - ψ) ^ 2 := by nlinarith
    nlinarith

section MeasureSide

variable {γ : ℝ} {μ : Measure ℝ}

private lemma rt_fin (hγ : 0 < γ) (h : def_app_phase_scalar γ μ) : IsFiniteMeasure μ :=
  ⟨by rw [h.1]; exact ENNReal.ofReal_lt_top⟩

private lemma rt_ae_nonneg (h : def_app_phase_scalar γ μ) : ∀ᵐ x ∂μ, 0 ≤ x := by
  have := (measure_eq_zero_iff_ae_notMem).1 h.2.1
  filter_upwards [this] with x hx
  simpa using hx

private lemma rt_sigma_int (hγ : 0 < γ) (h : def_app_phase_scalar γ μ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => (x + t)⁻¹) μ := by
  haveI := rt_fin hγ h
  refine Integrable.of_bound ((measurable_id.add_const t).inv).aestronglyMeasurable (t⁻¹) ?_
  filter_upwards [rt_ae_nonneg h] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (by linarith))]
  exact inv_anti₀ ht (by linarith)

private lemma rt_psi_eq (hγ : 0 < γ) (h : def_app_phase_scalar γ μ) {t : ℝ} (ht : 0 < t) :
    ∫ x, x / (x + t) ∂μ = γ - t * isoNegStieltjes μ t := by
  haveI := rt_fin hγ h
  have hint := rt_sigma_int hγ h ht
  have h1 : ∫ x, x / (x + t) ∂μ = ∫ x, (1 - t * (x + t)⁻¹) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [rt_ae_nonneg h] with x hx
    have : x + t ≠ 0 := by linarith
    field_simp
    ring
  rw [h1, integral_sub (integrable_const _) (hint.const_mul t), integral_const_mul]
  have : ∫ _x, (1 : ℝ) ∂μ = γ := by
    simp [h.1, Measure.real, ENNReal.toReal_ofReal hγ.le]
  rw [this]
  rfl

private lemma rt_sigma_pos (hγ : 0 < γ) (h : def_app_phase_scalar γ μ) {t : ℝ} (ht : 0 < t) :
    0 < isoNegStieltjes μ t := by
  have hnn : 0 ≤ isoNegStieltjes μ t := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [rt_ae_nonneg h] with x hx
    exact (inv_pos.2 (by linarith)).le
  rcases hnn.lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    have := h.2.2 t ht
    rw [← h1] at this
    simp [Muon.Isotropic.isoPhi] at this
    linarith

private lemma rt_psi_facts (hγ : 0 < γ) (h : def_app_phase_scalar γ μ) {t : ℝ} (ht : 0 < t) :
    0 < ∫ x, x / (x + t) ∂μ ∧ ∫ x, x / (x + t) ∂μ < 1 ∧ ∫ x, x / (x + t) ∂μ < γ ∧
    isoV (∫ x, x / (x + t) ∂μ) * t = (γ - ∫ x, x / (x + t) ∂μ) ^ 2 := by
  have hσ := rt_sigma_pos hγ h ht
  have hψ := rt_psi_eq hγ h ht
  have hs := h.2.2 t ht
  have hv : 0 < t * isoNegStieltjes μ t ^ 2 := by positivity
  have hp := Muon.Isotropic.lem_app_iso_gaussian_ii.2.2 _ hv
  rw [← hs] at hp
  refine ⟨by rw [hψ]; exact hp.1, by rw [hψ]; exact hp.2, by rw [hψ]; nlinarith [mul_pos ht hσ], ?_⟩
  have hmem : (∫ x, x / (x + t) ∂μ) ∈ Ioo (0 : ℝ) 1 := by
    rw [hψ]; exact hp
  have hV : isoV (∫ x, x / (x + t) ∂μ) = t * isoNegStieltjes μ t ^ 2 := by
    rw [hψ, hs, rt_V_phi hv]
  rw [hV, hψ]
  ring


private lemma rt_invsqrt {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => (Real.sqrt t)⁻¹) (Ioo 0 b) ∧
    ∫ t in Ioo (0 : ℝ) b, (Real.sqrt t)⁻¹ = 2 * Real.sqrt b := by
  have hcongr : ∀ t ∈ Ioc (0 : ℝ) b, (Real.sqrt t)⁻¹ = t ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    rw [Real.rpow_neg ht.1.le, ← Real.sqrt_eq_rpow]
  have h1 : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Ioc 0 b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).1
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  refine ⟨(h1.mono_set Ioo_subset_Ioc_self).congr_fun
    (fun t ht => (hcongr t (Ioo_subset_Ioc_self ht)).symm) measurableSet_Ioo, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb.le]
  rw [intervalIntegral.integral_congr (g := fun t : ℝ => t ^ (-(1 / 2 : ℝ)))
    (fun t ht => by
      rw [Set.uIcc_of_le hb.le] at ht
      rcases ht.1.eq_or_lt with h | h
      · subst h; simp
      · exact hcongr t ⟨h, ht.2⟩)]
  rw [integral_rpow (Or.inl (by norm_num))]
  rw [Real.zero_rpow (by norm_num)]
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  ring

private lemma rt_psi_meas (hγ : 0 < γ) (h : def_app_phase_scalar γ μ) :
    Measurable (fun t : ℝ => ∫ x, x / (x + t) ∂μ) := by
  haveI := rt_fin hγ h
  have := (by fun_prop : Measurable fun p : ℝ × ℝ => p.2 / (p.2 + p.1)).stronglyMeasurable
    |>.integral_prod_right' (ν := μ)
  exact this.measurable


private lemma rt_theta_sqrt {γ y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hyγ : y < γ) :
    Real.sqrt ((γ - y) ^ 2 / isoV y) = (γ - y) * isoW y := by
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (by linarith), isoW, div_eq_mul_inv]

private lemma rt_layer (hγ : 0 < γ) (h : def_app_phase_scalar γ μ) :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂μ) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂μ = 2 * isoI γ := by
  haveI := rt_fin hγ h
  set m := min γ 1 with hm
  have hm0 : 0 < m := lt_min hγ one_pos
  set ψ : ℝ → ℝ := fun t => ∫ x, x / (x + t) ∂μ with hψdef
  have hψm : Measurable ψ := rt_psi_meas hγ h
  let F : ℝ → ℝ → ℝ := fun t y => if y < ψ t then (Real.sqrt t)⁻¹ else 0
  have hFnn : ∀ t y, 0 ≤ F t y := fun t y => by
    simp only [F]; split_ifs
    · positivity
    · exact le_rfl
  have hFmeas : Measurable (fun p : ℝ × ℝ => F p.1 p.2) := by
    simp only [F]
    refine Measurable.ite (measurableSet_lt measurable_snd (hψm.comp measurable_fst)) ?_
      measurable_const
    exact (Real.continuous_sqrt.measurable.comp measurable_fst).inv
  -- inner integral in y
  have hA : ∀ t : ℝ, 0 < t → ∫ y in Ioo (0 : ℝ) m, F t y = (Real.sqrt t)⁻¹ * ψ t := by
    intro t ht
    obtain ⟨h0, h1, h2, -⟩ := rt_psi_facts hγ h ht
    have hlt : ψ t < m := lt_min h2 h1
    have : ∀ y, F t y = (Iio (ψ t)).indicator (fun _ => (Real.sqrt t)⁻¹) y := by
      intro y
      simp only [F, Set.indicator, Set.mem_Iio]
    simp_rw [this]
    rw [setIntegral_indicator measurableSet_Iio]
    have hs : Ioo (0 : ℝ) m ∩ Iio (ψ t) = Ioo 0 (ψ t) := by
      ext y
      simp only [mem_inter_iff, mem_Ioo, mem_Iio]
      constructor
      · rintro ⟨⟨a, _⟩, b⟩; exact ⟨a, b⟩
      · rintro ⟨a, b⟩; exact ⟨⟨a, b.trans hlt⟩, b⟩
    rw [hs, setIntegral_const, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    simp only [smul_eq_mul]
    rw [mul_comm]
    simp
  -- the layer in t
  have hyfacts : ∀ y ∈ Ioo (0 : ℝ) m, y ∈ Ioo (0 : ℝ) 1 ∧ y < γ := fun y hy =>
    ⟨⟨hy.1, lt_of_lt_of_le hy.2 (min_le_right _ _)⟩, lt_of_lt_of_le hy.2 (min_le_left _ _)⟩
  have hFy : ∀ y ∈ Ioo (0 : ℝ) m, ∀ t ∈ Ioi (0 : ℝ),
      F t y = (Ioo 0 ((γ - y) ^ 2 / isoV y)).indicator (fun t => (Real.sqrt t)⁻¹) t := by
    intro y hy t ht
    obtain ⟨hy1, hyγ⟩ := hyfacts y hy
    obtain ⟨h0, h1, h2, h3⟩ := rt_psi_facts hγ h ht
    have hc := rt_char ht h0 h1 h2 h3 hy1 hyγ
    simp only [F, Set.indicator, Set.mem_Ioo]
    by_cases hlt : y < ψ t
    · rw [if_pos hlt, if_pos ⟨ht, hc.1 hlt⟩]
    · rw [if_neg hlt, if_neg]
      intro hh
      exact hlt (hc.2 hh.2)
  have hΘpos : ∀ y ∈ Ioo (0 : ℝ) m, 0 < (γ - y) ^ 2 / isoV y := by
    intro y hy
    obtain ⟨hy1, hyγ⟩ := hyfacts y hy
    have := (rt_V_spec hy1).1
    have h' : 0 < isoV y := this
    have : 0 < γ - y := by linarith
    positivity
  have hBint : ∀ y ∈ Ioo (0 : ℝ) m, IntegrableOn (fun t => F t y) (Ioi 0) := by
    intro y hy
    have h1 := (rt_invsqrt (hΘpos y hy)).1
    have h2 : Integrable ((Ioo 0 ((γ - y) ^ 2 / isoV y)).indicator
        (fun t : ℝ => (Real.sqrt t)⁻¹)) volume :=
      (integrable_indicator_iff measurableSet_Ioo).2 h1
    exact h2.integrableOn.congr_fun (fun t ht => (hFy y hy t ht).symm) measurableSet_Ioi
  have hBval : ∀ y ∈ Ioo (0 : ℝ) m, ∫ t in Ioi (0 : ℝ), F t y = 2 * ((γ - y) * isoW y) := by
    intro y hy
    obtain ⟨hy1, hyγ⟩ := hyfacts y hy
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hFy y hy t ht),
      setIntegral_indicator measurableSet_Ioo]
    have : Ioi (0 : ℝ) ∩ Ioo 0 ((γ - y) ^ 2 / isoV y) = Ioo 0 ((γ - y) ^ 2 / isoV y) := by
      ext t
      simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨_, b⟩; exact b
      · rintro ⟨a, b⟩; exact ⟨a, a, b⟩
    rw [this, (rt_invsqrt (hΘpos y hy)).2, rt_theta_sqrt hy1 hyγ]
  have hWint : IntegrableOn (fun y => (γ - y) * isoW y) (Ioo 0 m) := by
    have h1 : IntegrableOn (fun y => γ * isoW y - y * isoW y) (Ioo 0 1) :=
      (rt_W_integrableOn.const_mul γ).sub rt_yW_integrableOn
    refine (h1.mono_set (Ioo_subset_Ioo_right (min_le_right _ _))).congr_fun
      (fun y _ => by ring) measurableSet_Ioo
  have hint : Integrable (fun p : ℝ × ℝ => F p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) m))) := by
    rw [integrable_prod_iff' hFmeas.aestronglyMeasurable]
    refine ⟨(ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun y hy => ?_), ?_⟩
    · exact hBint y hy
    · refine (hWint.const_mul 2).congr ?_
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun y hy => ?_
      have : ∫ t, ‖F t y‖ ∂(volume.restrict (Ioi (0 : ℝ))) = ∫ t in Ioi (0 : ℝ), F t y := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [Real.norm_eq_abs, abs_of_nonneg (hFnn t y)]
      rw [this, hBval y hy]
  have hswap := integral_integral_swap (f := F) hint
  have hfun : (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂μ) =ᵐ[volume.restrict (Ioi 0)]
      (fun t => ∫ y in Ioo (0 : ℝ) m, F t y) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [hA t ht, Real.rpow_neg (le_of_lt ht), ← Real.sqrt_eq_rpow]
  refine ⟨?_, ?_⟩
  · exact (hint.integral_prod_left).congr hfun.symm
  · rw [integral_congr_ae hfun]
    rw [hswap]
    rw [setIntegral_congr_fun measurableSet_Ioo (fun y hy => hBval y hy), integral_const_mul,
      isoI, intervalIntegral.integral_of_le (le_of_lt hm0), integral_Ioc_eq_integral_Ioo]


private lemma rt_measure_formula (hγ : 0 < γ) (h : def_app_phase_scalar γ μ)
    (hHM : (Integrable (fun x : ℝ => Real.sqrt x) μ ↔
        IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂μ) (Ioi (0 : ℝ))) ∧
      ∫ x, Real.sqrt x ∂μ =
        1 / Real.pi * ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂μ) :
    Integrable (fun x : ℝ => Real.sqrt x) μ ∧
      (Real.sqrt 2 * γ ^ 2)⁻¹ * ∫ x, Real.sqrt x ∂μ = isoDriftConst γ := by
  obtain ⟨hl1, hl2⟩ := rt_layer hγ h
  refine ⟨hHM.1.2 hl1, ?_⟩
  rw [hHM.2, hl2, isoDriftConst]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2ne : Real.sqrt 2 ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  rw [sq]
  rw [hs2]

end MeasureSide


/-! ## The integral formula for the drift constant -/

/-- lem:app-phase-ratio-integral, snapshot `cr-2026-10-23`. The first conjuncts are the preamble
facts of the lemma about `Φ`, `V`, `w`, `w_∘`; the last conjunct is the formula for `C(γ)` at every
measure satisfying `def_app_phase_scalar`, with the integrability of `√x` made explicit.

LaTeX (verbatim, `section.tex` l.724–737):
```
\begin{lemma}[An integral for the drift constant]\label{lem:app-phase-ratio-integral}
The map $\Phi$ is a continuously differentiable increasing bijection from
$(0,\infty)$ onto $(0,1)$; let $V$ be its inverse and $w(y)\defeq V(y)^{-1/2}$
for $0<y<1$. The function $w_\circ(y)\defeq\sqrt y\,w(y)$ is positive, strictly
decreasing, at most $1$, and tends to $1$ as $y\downarrow0$. For every
$\gamma>0$,
\begin{equation}\label{eqn:app-phase-CI}
C(\gamma)=\frac{\sqrt2}{\pi\gamma^2}\,I(\gamma),\qquad I(\gamma)\defeq\int_0^{\min(\gamma,1)}(\gamma-y)\,w(y)\,\dif y .
\end{equation}
Moreover
\begin{equation}\label{eqn:app-phase-AD}
\mathcal A\defeq\int_0^1w(y)\,\dif y=\sqrt{\frac\pi2},\qquad \mathcal D\defeq\int_0^1y\,w(y)\,\dif y\in(0,\mathcal A),\qquad I(\gamma)=\gamma\mathcal A-\mathcal D\quad(\gamma\ge1).
\end{equation}
\end{lemma}
```
-/
theorem lem_app_phase_ratio_integral :
    ContDiffOn ℝ 1 isoPhi (Ioi 0) ∧ StrictMonoOn isoPhi (Ioi 0) ∧
    BijOn isoPhi (Ioi 0) (Ioo 0 1) ∧
    (∀ y ∈ Ioo (0 : ℝ) 1, isoV y ∈ Ioi 0 ∧ isoPhi (isoV y) = y) ∧
    ContDiffOn ℝ 1 isoV (Ioo 0 1) ∧
    (∀ y ∈ Ioo (0 : ℝ) 1, 0 < isoWcirc y ∧ isoWcirc y ≤ 1) ∧
    StrictAntiOn isoWcirc (Ioo 0 1) ∧
    Tendsto isoWcirc (𝓝[>] 0) (𝓝 1) ∧
    (∀ γ : ℝ, 0 < γ → ∀ μ : Measure ℝ, def_app_phase_scalar γ μ →
      Integrable (fun x : ℝ => Real.sqrt x) μ ∧
      (Real.sqrt 2 * γ ^ 2)⁻¹ * ∫ x, Real.sqrt x ∂μ = isoDriftConst γ) ∧
    isoA = Real.sqrt (Real.pi / 2) ∧
    0 < isoD ∧ isoD < isoA ∧
    (∀ γ : ℝ, 1 ≤ γ → isoI γ = γ * isoA - isoD) := by
  refine ⟨rt_contDiff_phi, Muon.Isotropic.lem_app_iso_gaussian_ii.1, rt_bij,
    fun y hy => rt_V_spec hy, rt_contDiff_V, fun y hy => rt_wcirc_bounds hy, rt_wcirc_anti,
    rt_wcirc_tendsto, ?_, rt_isoA, rt_isoD_pos, rt_isoD_lt, fun γ hγ => rt_isoI_ge hγ⟩
  intro γ hγ μ hμ
  refine rt_measure_formula hγ hμ ?_
  exact Muon.Isotropic.lem_app_iso_moments_v μ (rt_fin hγ hμ) hμ.2.1

/-! ## The isotropic ratio -/

/-! ## Helpers for `prop_app_phase_iso_ratio` (task P-H.12.P3) -/

private lemma p12_isoI_pos_lt {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) : 0 < isoI γ := by
  unfold isoI
  rw [min_eq_left hγ1.le]
  have hii1 : IntervalIntegrable (fun y => γ * isoW y - y * isoW y) volume 0 1 :=
    (rt_W_ii.const_mul γ).sub rt_yW_ii
  have hfun : (fun y => (γ - y) * isoW y) = fun y => γ * isoW y - y * isoW y := by
    funext y; ring
  rw [hfun]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (hii1.mono_set ?_) (fun y hy => ?_) hγ0
  · rw [uIcc_of_le hγ0.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hγ1.le
  · have hy1 : y ∈ Ioo (0 : ℝ) 1 := ⟨hy.1, lt_trans hy.2 hγ1⟩
    have hW := rt_W_pos hy1
    have h2 : 0 < γ - y := sub_pos.2 hy.2
    show 0 < γ * isoW y - y * isoW y
    nlinarith

private lemma p12_isoI_pos_ge {γ : ℝ} (hγ : 1 ≤ γ) : 0 < isoI γ := by
  have hA : 0 < isoA := by rw [rt_isoA]; exact Real.sqrt_pos.2 (by positivity)
  rw [rt_isoI_ge hγ]
  nlinarith [rt_isoD_lt, rt_isoD_pos, mul_nonneg (sub_nonneg.2 hγ) hA.le]

private lemma p12_isoI_pos {γ : ℝ} (hγ : 0 < γ) : 0 < isoI γ := by
  rcases lt_or_ge γ 1 with h | h
  · exact p12_isoI_pos_lt hγ h
  · exact p12_isoI_pos_ge h

private lemma p12_C_pos {γ : ℝ} (hγ : 0 < γ) : 0 < isoDriftConst γ := by
  unfold isoDriftConst
  exact mul_pos (div_pos (Real.sqrt_pos.2 two_pos) (mul_pos Real.pi_pos (pow_pos hγ 2)))
    (p12_isoI_pos hγ)

private lemma p12_key {N B : ℝ} (hN : 0 < N) (hB : 0 < B) :
    N / B * max 1 (N / B) * B = N ^ 2 / min B N := by
  rcases le_total N B with h | h
  · have hγ1 : N / B ≤ 1 := (div_le_one hB).2 h
    rw [min_eq_right h, max_eq_left hγ1]
    field_simp
  · have hγ1 : 1 ≤ N / B := (one_le_div hB).2 h
    rw [min_eq_left h, max_eq_right hγ1]
    field_simp

/-- The isotropic setting: two `RowModel (Fin N)` values `mS` (s-SVD) and `mN` (s-SGD) with the
isotropic arrays `eqn:app-phase-iso-arrays` for the batch `B`, the bounds `eqn:app-phase-NB` on
`NB` (the value `𝒩_B`), the matched steps at level `ε`, the horizon `T > 1`, and `F₀ > Tε`.
Both models have `μ_i = 1` and the same initial energies `Q0`. The drift of `mS` is `C(N/B)`
(`isoDriftConst`), with `∑ 𝔳_i = min(B,N)`; the drift of `mN` is `𝒩_B/√π`, with `∑ 𝔳_i = N²`.
-/
def IsIsoSetting (N B : ℕ) (NB ε T : ℝ) (mS mN : RowModel (Fin N)) : Prop :=
  1 ≤ N ∧ 1 ≤ B ∧
    max (2 / Real.pi * Real.sqrt (B : ℝ)) (Real.sqrt (B : ℝ) - 4 / Real.sqrt (B : ℝ)) ≤ NB ∧
    NB ≤ Real.sqrt (B : ℝ) ∧
    1 < T ∧ 0 < ε ∧
    (∀ i, mS.μ i = 1) ∧ (∀ i, mN.μ i = 1) ∧
    (∀ i, mS.d i = isoDriftConst ((N : ℝ) / B)) ∧ (∀ i, mN.d i = NB / Real.sqrt Real.pi) ∧
    (∑ i, mS.v i = min (B : ℝ) (N : ℝ)) ∧ (∑ i, mN.v i = (N : ℝ) ^ 2) ∧
    mS.Q0 = mN.Q0 ∧ T * ε < mS.F0 ∧
    mS.η = 2 * Real.sqrt ε / mS.S ∧ mN.η = 2 * Real.sqrt ε / mN.S

/-- prop:app-phase-iso-ratio, snapshot `cr-2026-10-23`. For an isotropic setting, the two
Volterra solutions give finite hitting times, the ratio of the times is `ρ(γ) B / 𝒩_B²`, and the
bounds on `B / 𝒩_B²` hold.

LaTeX (verbatim, `section.tex` l.666–678):
```
\begin{proposition}[The isotropic ratio]\label{prop:app-phase-iso-ratio}
Take the arrays \cref{eqn:app-phase-iso-arrays} with a common $F_0$, the
matched steps $\lr^\star=2\sqrt\epsilon/\mathcal S$ of each, and $T>1$ with
$F_0>T\epsilon$. Then
\[
\mathcal S^{\text{s-SVD}}=\frac m{2C(\gamma)},\qquad \mathcal S^{\text{s-SGD}}=\frac{N^2\sqrt\pi}{2\mathcal N_B},\qquad
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}=\frac{\pi N^2C(\gamma)^2}{m\,\mathcal N_B^2}=\rho(\gamma)\,\frac B{\mathcal N_B^2} .
\]
Moreover $1\le B/\mathcal N_B^2\le\pi^2/4$ for every $B$, and for $B>4$
\[
0\le\frac{t^{\text{s-SGD}}_{T\epsilon}/t^{\text{s-SVD}}_{T\epsilon}}{\rho(\gamma)}-1\le\Big(1-\frac4B\Big)^{-2}-1 .
\]
\end{proposition}
```
-/
theorem prop_app_phase_iso_ratio (N B : ℕ) (NB ε T : ℝ) (mS mN : RowModel (Fin N))
    (h : IsIsoSetting N B NB ε T mS mN) :
    mS.S = min (B : ℝ) (N : ℝ) / (2 * isoDriftConst ((N : ℝ) / B)) ∧
    mN.S = (N : ℝ) ^ 2 * Real.sqrt Real.pi / (2 * NB) ∧
    (∀ Qs Qn : Fin N → ℝ → ℝ, IsGlobalRowSolution mS Qs → IsGlobalRowSolution mN Qn →
      firstHit (mS.risk Qs) (T * ε) ≠ ⊤ ∧ firstHit (mN.risk Qn) (T * ε) ≠ ⊤ ∧
      (firstHit (mN.risk Qn) (T * ε)).toReal / (firstHit (mS.risk Qs) (T * ε)).toReal
        = isoRho ((N : ℝ) / B) * (B : ℝ) / NB ^ 2) ∧
    isoRho ((N : ℝ) / B) * (B : ℝ) / NB ^ 2
        = Real.pi * (N : ℝ) ^ 2 * isoDriftConst ((N : ℝ) / B) ^ 2
          / (min (B : ℝ) (N : ℝ) * NB ^ 2) ∧
    (∀ Qs Qn : Fin N → ℝ → ℝ, IsGlobalRowSolution mS Qs → IsGlobalRowSolution mN Qn →
      4 < B →
        0 ≤ ((firstHit (mN.risk Qn) (T * ε)).toReal / (firstHit (mS.risk Qs) (T * ε)).toReal)
            / isoRho ((N : ℝ) / B) - 1 ∧
        ((firstHit (mN.risk Qn) (T * ε)).toReal / (firstHit (mS.risk Qs) (T * ε)).toReal)
            / isoRho ((N : ℝ) / B) - 1 ≤ ((1 - 4 / (B : ℝ)) ^ 2)⁻¹ - 1) ∧
    1 ≤ (B : ℝ) / NB ^ 2 ∧ (B : ℝ) / NB ^ 2 ≤ Real.pi ^ 2 / 4 ∧
    (4 < B → (B : ℝ) / NB ^ 2 ≤ ((1 - 4 / (B : ℝ)) ^ 2)⁻¹) := by
  unfold IsIsoSetting at h
  obtain ⟨hN1, hB1, hNBlo, hNBhi, hT, hε, hμS, hμN, hdS, hdN, hvS, hvN, hQ0, hFT, hηS, hηN⟩ := h
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hsB : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.2 hBpos
  have hs2 : Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) = B := Real.mul_self_sqrt hBpos.le
  have hNBpos : 0 < NB := lt_of_lt_of_le (mul_pos (div_pos two_pos Real.pi_pos) hsB)
    (le_trans (le_max_left _ _) hNBlo)
  have hNBlo' : 2 / Real.pi * Real.sqrt (B : ℝ) ≤ NB := le_trans (le_max_left _ _) hNBlo
  have hNB2pos : 0 < NB ^ 2 := pow_pos hNBpos 2
  have hNB2le : NB ^ 2 ≤ (B : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hNBhi hNBpos.le, mul_le_mul_of_nonneg_right hNBhi hsB.le]
  have hπne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hBNB1 : 1 ≤ (B : ℝ) / NB ^ 2 := (one_le_div hNB2pos).2 hNB2le
  have hBNB2 : (B : ℝ) / NB ^ 2 ≤ Real.pi ^ 2 / 4 := by
    have hlo2 : (2 / Real.pi * Real.sqrt (B : ℝ)) ^ 2 ≤ NB ^ 2 :=
      pow_le_pow_left₀ (mul_pos (div_pos two_pos Real.pi_pos) hsB).le hNBlo' 2
    have key : (2 / Real.pi * Real.sqrt (B : ℝ)) ^ 2 = 4 / Real.pi ^ 2 * B := by
      rw [mul_pow, div_pow, Real.sq_sqrt hBpos.le]; ring
    rw [key] at hlo2
    rw [div_le_iff₀ hNB2pos]
    have h3 := mul_le_mul_of_nonneg_left hlo2 (by positivity : (0 : ℝ) ≤ Real.pi ^ 2 / 4)
    have h4 : Real.pi ^ 2 / 4 * (4 / Real.pi ^ 2 * B) = B := by field_simp
    linarith
  have hBNB3 : 4 < B → (B : ℝ) / NB ^ 2 ≤ ((1 - 4 / (B : ℝ)) ^ 2)⁻¹ := by
    intro h4
    have h4' : (4 : ℝ) < B := by exact_mod_cast h4
    have hq : 0 < 1 - 4 / (B : ℝ) := by
      have : 4 / (B : ℝ) < 1 := by rw [div_lt_one hBpos]; exact h4'
      linarith
    have e : 4 / Real.sqrt (B : ℝ) = Real.sqrt (B : ℝ) * (4 / B) := by
      field_simp
      nlinarith [hs2]
    have hlow : Real.sqrt (B : ℝ) * (1 - 4 / (B : ℝ)) ≤ NB := by
      have h5 := le_trans (le_max_right _ _) hNBlo
      rw [e] at h5
      linarith [show Real.sqrt (B : ℝ) * (1 - 4 / (B : ℝ))
        = Real.sqrt (B : ℝ) - Real.sqrt (B : ℝ) * (4 / B) by ring]
    have h6 := pow_le_pow_left₀ (mul_pos hsB hq).le hlow 2
    rw [mul_pow, Real.sq_sqrt hBpos.le] at h6
    have hqpos : 0 < (1 - 4 / (B : ℝ)) ^ 2 := pow_pos hq 2
    rw [inv_eq_one_div, div_le_div_iff₀ hNB2pos hqpos]
    linarith
  -- the common quantities
  have hγ : (0 : ℝ) < (N : ℝ) / B := div_pos hNpos hBpos
  have hC := p12_C_pos hγ
  have hCne : isoDriftConst ((N : ℝ) / B) ≠ 0 := hC.ne'
  have hminpos : (0 : ℝ) < min (B : ℝ) (N : ℝ) := lt_min hBpos hNpos
  have hminne : min (B : ℝ) (N : ℝ) ≠ 0 := hminpos.ne'
  have hNBne : NB ≠ 0 := hNBpos.ne'
  have hsπ : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hvS' : commonVtot mS = min (B : ℝ) (N : ℝ) := by
    unfold commonVtot; simp only [hμS, one_mul]; exact hvS
  have hvN' : commonVtot mN = (N : ℝ) ^ 2 := by
    unfold commonVtot; simp only [hμN, one_mul]; exact hvN
  have hdN2 : (0 : ℝ) < NB / Real.sqrt Real.pi := div_pos hNBpos (Real.sqrt_pos.2 Real.pi_pos)
  have hF₂eq : mN.F0 = mS.F0 := by
    unfold RowModel.F0; simp only [hμS, hμN, hQ0]
  have hFN : T * ε < mN.F0 := by rw [hF₂eq]; exact hFT
  have hvN_pos : 0 < commonVtot mN := by rw [hvN']; exact pow_pos hNpos 2
  have hvS_pos : 0 < commonVtot mS := by rw [hvS']; exact hminpos
  obtain ⟨hAN, hBN⟩ := thm_app_phase_matched mN (NB / Real.sqrt Real.pi) hdN2 hdN hvN_pos ε T
    hε hT hFN hηN mS (isoDriftConst ((N : ℝ) / B)) hC hdS hvS_pos hηS hFT hF₂eq.symm
  obtain ⟨hAS, -⟩ := thm_app_phase_matched mS (isoDriftConst ((N : ℝ) / B)) hC hdS hvS_pos ε T
    hε hT hFT hηS mN (NB / Real.sqrt Real.pi) hdN2 hdN hvN_pos hηN hFN hF₂eq
  -- the S-formulas
  have hS1 : mS.S = min (B : ℝ) (N : ℝ) / (2 * isoDriftConst ((N : ℝ) / B)) := by
    unfold RowModel.S
    rw [tsum_fintype]
    simp only [hμS, one_mul, hdS]
    rw [← Finset.sum_div, hvS]
  have hS2 : mN.S = (N : ℝ) ^ 2 * Real.sqrt Real.pi / (2 * NB) := by
    unfold RowModel.S
    rw [tsum_fintype]
    simp only [hμN, one_mul, hdN]
    rw [← Finset.sum_div, hvN]
    field_simp
  -- the algebra of the ratio
  have hK2 : ((N : ℝ) ^ 2 / (NB / Real.sqrt Real.pi) ^ 2)
      / (min (B : ℝ) (N : ℝ) / isoDriftConst ((N : ℝ) / B) ^ 2)
      = Real.pi * (N : ℝ) ^ 2 * isoDriftConst ((N : ℝ) / B) ^ 2
        / (min (B : ℝ) (N : ℝ) * NB ^ 2) := by
    rw [div_pow, Real.sq_sqrt Real.pi_pos.le]
    field_simp
  have hmid : isoRho ((N : ℝ) / B) * (B : ℝ) / NB ^ 2
      = Real.pi * (N : ℝ) ^ 2 * isoDriftConst ((N : ℝ) / B) ^ 2
        / (min (B : ℝ) (N : ℝ) * NB ^ 2) := by
    have e : isoRho ((N : ℝ) / B) * B
        = Real.pi * isoDriftConst ((N : ℝ) / B) ^ 2 * ((N : ℝ) / B * max 1 ((N : ℝ) / B) * B) := by
      unfold isoRho; ring
    rw [e, p12_key hNpos hBpos]
    ring
  have hρ : 0 < isoRho ((N : ℝ) / B) := by
    unfold isoRho
    exact mul_pos (mul_pos (mul_pos Real.pi_pos (pow_pos hC 2)) hγ)
      (lt_of_lt_of_le one_pos (le_max_left _ _))
  have hρne : isoRho ((N : ℝ) / B) ≠ 0 := hρ.ne'
  -- the ratio of hitting times
  have hR : ∀ Qs Qn : Fin N → ℝ → ℝ, IsGlobalRowSolution mS Qs → IsGlobalRowSolution mN Qn →
      (firstHit (mN.risk Qn) (T * ε)).toReal / (firstHit (mS.risk Qs) (T * ε)).toReal
        = isoRho ((N : ℝ) / B) * (B : ℝ) / NB ^ 2 := by
    intro Qs Qn hQs hQn
    rw [hBN Qn hQn Qs hQs, hvN', hvS', hK2, hmid]
  have hR3 : ∀ Qs Qn : Fin N → ℝ → ℝ, IsGlobalRowSolution mS Qs → IsGlobalRowSolution mN Qn →
      firstHit (mS.risk Qs) (T * ε) ≠ ⊤ ∧ firstHit (mN.risk Qn) (T * ε) ≠ ⊤ ∧
      (firstHit (mN.risk Qn) (T * ε)).toReal / (firstHit (mS.risk Qs) (T * ε)).toReal
        = isoRho ((N : ℝ) / B) * (B : ℝ) / NB ^ 2 := by
    intro Qs Qn hQs hQn
    refine ⟨?_, ?_, hR Qs Qn hQs hQn⟩
    · rw [(hAS Qs hQs).2.1]; exact ENNReal.ofReal_ne_top
    · rw [(hAN Qn hQn).2.1]; exact ENNReal.ofReal_ne_top
  have hR5 : ∀ Qs Qn : Fin N → ℝ → ℝ, IsGlobalRowSolution mS Qs → IsGlobalRowSolution mN Qn →
      4 < B →
        0 ≤ ((firstHit (mN.risk Qn) (T * ε)).toReal / (firstHit (mS.risk Qs) (T * ε)).toReal)
            / isoRho ((N : ℝ) / B) - 1 ∧
        ((firstHit (mN.risk Qn) (T * ε)).toReal / (firstHit (mS.risk Qs) (T * ε)).toReal)
            / isoRho ((N : ℝ) / B) - 1 ≤ ((1 - 4 / (B : ℝ)) ^ 2)⁻¹ - 1 := by
    intro Qs Qn hQs hQn h4
    rw [hR Qs Qn hQs hQn]
    have hdiv : isoRho ((N : ℝ) / B) * (B : ℝ) / NB ^ 2 / isoRho ((N : ℝ) / B)
        = (B : ℝ) / NB ^ 2 := by
      field_simp
    rw [hdiv]
    have := hBNB3 h4
    constructor <;> linarith
  exact ⟨hS1, hS2, hR3, hmid, hR5, hBNB1, hBNB2, hBNB3⟩

/-! ## Helpers for `thm_app_phase_iso_extrema` -/

private lemma rt_isoA_sq : isoA ^ 2 = Real.pi / 2 := by
  rw [rt_isoA, Real.sq_sqrt (by positivity)]

private lemma rt_isoA_pos : 0 < isoA := by
  rw [rt_isoA]; positivity

private lemma rt_rho_ge_one {γ : ℝ} (hγ : 1 ≤ γ) :
    isoRho γ = (1 - (isoD / isoA) / γ) ^ 2 := by
  have hpi : Real.pi = 2 * isoA ^ 2 := by linarith [rt_isoA_sq]
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hγ0 : γ ≠ 0 := ne_of_gt (by linarith)
  have hApos : isoA ≠ 0 := ne_of_gt rt_isoA_pos
  unfold isoRho isoDriftConst
  rw [rt_isoI_ge hγ, max_eq_right hγ, hpi]
  rw [mul_pow, div_pow, hsqrt2]
  field_simp

private lemma rt_rho_one : isoRho 1 = Real.pi * isoDriftConst 1 ^ 2 := by
  unfold isoRho
  rw [max_self]
  ring

private lemma rt_d_bounds : 0 < isoD / isoA ∧ isoD / isoA < 1 :=
  ⟨div_pos rt_isoD_pos rt_isoA_pos, (div_lt_one rt_isoA_pos).2 rt_isoD_lt⟩

private lemma rt_d_C1 : isoD / isoA = 1 - Real.sqrt Real.pi * isoDriftConst 1 := by
  have hA' : isoA * Real.sqrt 2 = Real.sqrt Real.pi := by
    rw [rt_isoA, ← Real.sqrt_mul (by positivity) 2]
    congr 1
    ring
  have hpi : Real.pi = 2 * isoA ^ 2 := by linarith [rt_isoA_sq]
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hApos : isoA ≠ 0 := ne_of_gt rt_isoA_pos
  unfold isoDriftConst
  rw [rt_isoI_ge le_rfl, ← hA', hpi]
  field_simp
  linear_combination (isoA - isoD) * hsqrt2

private lemma rt_rho_strictMono_ge_one : StrictMonoOn isoRho (Ici 1) := by
  intro a ha b hb hab
  have ha' : (1 : ℝ) ≤ a := ha
  have hb' : (1 : ℝ) ≤ b := hb
  obtain ⟨hd0, hd1⟩ := rt_d_bounds
  rw [rt_rho_ge_one ha', rt_rho_ge_one hb']
  have h1 : isoD / isoA / b < isoD / isoA / a :=
    div_lt_div_of_pos_left hd0 (by linarith) hab
  have h2 : 0 < 1 - isoD / isoA / a := by
    have : isoD / isoA / a < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    linarith
  nlinarith

private lemma rt_rho_tendsto_top : Tendsto isoRho atTop (𝓝 1) := by
  have h0 : Tendsto (fun γ : ℝ => isoD / isoA / γ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h1 := ((tendsto_const_nhds (x := (1 : ℝ))).sub h0).pow 2
  rw [sub_zero, one_pow] at h1
  exact h1.congr' (eventually_atTop.2 ⟨1, fun γ hγ => (rt_rho_ge_one hγ).symm⟩)

private lemma rt_isoI_eq {γ : ℝ} (hγ : 0 < γ) :
    isoI γ = γ * (∫ y in (0 : ℝ)..min γ 1, isoW y) - ∫ y in (0 : ℝ)..min γ 1, y * isoW y := by
  have hm0 : 0 ≤ min γ 1 := le_min hγ.le zero_le_one
  have hm1 : min γ 1 ≤ 1 := min_le_right _ _
  have hsub : uIcc (0 : ℝ) (min γ 1) ⊆ uIcc (0 : ℝ) 1 :=
    uIcc_subset_uIcc left_mem_uIcc (Set.mem_uIcc.2 (Or.inl ⟨hm0, hm1⟩))
  have hi1 : IntervalIntegrable isoW volume 0 (min γ 1) := rt_W_ii.mono_set hsub
  have hi2 : IntervalIntegrable (fun y => y * isoW y) volume 0 (min γ 1) := rt_yW_ii.mono_set hsub
  unfold isoI
  have e : (fun y : ℝ => (γ - y) * isoW y) = fun y => γ * isoW y - y * isoW y :=
    funext fun y => by ring
  rw [e, intervalIntegral.integral_sub (hi1.const_mul γ) hi2, intervalIntegral.integral_const_mul]

private lemma rt_isoI_cont : ContinuousOn isoI (Ioi 0) := by
  have hF := intervalIntegral.continuousOn_primitive_interval' (μ := volume) (a := 0) rt_W_ii
    left_mem_uIcc
  have hG := intervalIntegral.continuousOn_primitive_interval' (μ := volume) (a := 0) rt_yW_ii
    left_mem_uIcc
  have hm : ContinuousOn (fun γ : ℝ => min γ 1) (Ioi 0) :=
    (continuous_id.min continuous_const).continuousOn
  have hmaps : Set.MapsTo (fun γ : ℝ => min γ 1) (Ioi 0) (uIcc (0 : ℝ) 1) := fun γ hγ =>
    Set.mem_uIcc.2 (Or.inl ⟨le_min (le_of_lt (Set.mem_Ioi.1 hγ)) zero_le_one, min_le_right _ _⟩)
  have hc := (continuousOn_id.mul (hF.comp hm hmaps)).sub (hG.comp hm hmaps)
  refine hc.congr ?_
  intro γ hγ
  exact rt_isoI_eq (Set.mem_Ioi.1 hγ)

private lemma rt_rho_cont : ContinuousOn isoRho (Ioi 0) := by
  have hC : ContinuousOn isoDriftConst (Ioi 0) := by
    unfold isoDriftConst
    refine ContinuousOn.mul ?_ rt_isoI_cont
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (continuous_const.mul (continuous_pow 2)).continuousOn
    · intro γ hγ
      exact mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 (ne_of_gt (Set.mem_Ioi.1 hγ)))
  unfold isoRho
  exact ((continuousOn_const.mul (hC.pow 2)).mul continuousOn_id).mul
    (continuous_const.max continuous_id).continuousOn

private lemma rt_invsqrt_ii {γ : ℝ} (hγ : 0 < γ) :
    IntervalIntegrable (fun y : ℝ => (√y)⁻¹) volume 0 γ := by
  have h1 : IntegrableOn (fun y : ℝ => y ^ (-(1 / 2) : ℝ)) (Ioc 0 γ) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hγ.le).1 (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hγ.le).2 (h1.congr_fun ?_ measurableSet_Ioc)
  intro y hy
  show y ^ (-(1 / 2) : ℝ) = (√y)⁻¹
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hy.1.le]

private lemma rt_zero_int {γ : ℝ} (hγ : 0 < γ) :
    ∫ y in (0 : ℝ)..γ, (3 * y - γ) * (√y)⁻¹ = 0 := by
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) γ, HasDerivWithinAt (fun y : ℝ => 2 * y * √y - 2 * γ * √y)
      ((3 * x - γ) * (√x)⁻¹) (Ioi x) x := by
    intro x hx
    have hA : HasDerivAt (fun y : ℝ => 2 * y * √y) (2 * 1 * √x + 2 * x * (1 / (2 * √x))) x :=
      ((hasDerivAt_id' x).const_mul 2).mul (Real.hasDerivAt_sqrt hx.1.ne')
    have hB : HasDerivAt (fun y : ℝ => 2 * γ * √y) (2 * γ * (1 / (2 * √x))) x :=
      (Real.hasDerivAt_sqrt hx.1.ne').const_mul (2 * γ)
    have hsq : √x * √x = x := Real.mul_self_sqrt hx.1.le
    have hx' : x * (√x)⁻¹ = √x := by
      have hs : √x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx.1)
      exact (mul_inv_eq_iff_eq_mul₀ hs).2 hsq.symm
    have h := hA.sub hB
    exact (h.congr_deriv (by linear_combination (-2) * hx')).hasDerivWithinAt
  have hcont : ContinuousOn (fun y : ℝ => 2 * y * √y - 2 * γ * √y) (Icc 0 γ) :=
    (by fun_prop : Continuous fun y : ℝ => 2 * y * √y - 2 * γ * √y).continuousOn
  have hint : IntervalIntegrable (fun y : ℝ => (3 * y - γ) * (√y)⁻¹) volume 0 γ :=
    (rt_invsqrt_ii hγ).continuousOn_mul
      (by fun_prop : Continuous fun y : ℝ => 3 * y - γ).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hγ.le hcont hderiv hint]
  simp

private lemma rt_diff_eq {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    isoW y = isoWcirc y * (√y)⁻¹ := by
  unfold isoWcirc
  have hs : √y ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hy.1)
  field_simp

private lemma rt_sign_left {γ y : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hy : y ∈ Ioo 0 (γ / 3)) :
    0 < -((3 * y - γ) * isoW y - isoWcirc (γ / 3) * ((3 * y - γ) * (√y)⁻¹)) := by
  have hy0 : 0 < y := hy.1
  have hyI : y ∈ Ioo (0 : ℝ) 1 := ⟨hy0, by linarith [hy.2]⟩
  have hcI : γ / 3 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hw := rt_wcirc_anti hyI hcI hy.2
  rw [rt_diff_eq hyI]
  have key : -((3 * y - γ) * (isoWcirc y * (√y)⁻¹) - isoWcirc (γ / 3) * ((3 * y - γ) * (√y)⁻¹))
      = (γ - 3 * y) * (isoWcirc y - isoWcirc (γ / 3)) * (√y)⁻¹ := by ring
  rw [key]
  have h1 : 0 < γ - 3 * y := by linarith [hy.2]
  have h2 : 0 < isoWcirc y - isoWcirc (γ / 3) := by linarith
  have h3 : 0 < (√y)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hy0)
  exact mul_pos (mul_pos h1 h2) h3

private lemma rt_sign_right {γ y : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hy : y ∈ Ioo (γ / 3) γ) :
    0 < -((3 * y - γ) * isoW y - isoWcirc (γ / 3) * ((3 * y - γ) * (√y)⁻¹)) := by
  have hy0 : 0 < y := by linarith [hy.1]
  have hyI : y ∈ Ioo (0 : ℝ) 1 := ⟨hy0, by linarith [hy.2]⟩
  have hcI : γ / 3 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hw := rt_wcirc_anti hcI hyI hy.1
  rw [rt_diff_eq hyI]
  have key : -((3 * y - γ) * (isoWcirc y * (√y)⁻¹) - isoWcirc (γ / 3) * ((3 * y - γ) * (√y)⁻¹))
      = (3 * y - γ) * (isoWcirc (γ / 3) - isoWcirc y) * (√y)⁻¹ := by ring
  rw [key]
  have h1 : 0 < 3 * y - γ := by linarith [hy.1]
  have h2 : 0 < isoWcirc (γ / 3) - isoWcirc y := by linarith
  have h3 : 0 < (√y)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hy0)
  exact mul_pos (mul_pos h1 h2) h3

private lemma rt_key {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∫ y in (0 : ℝ)..γ, (3 * y - γ) * isoW y < 0 := by
  have hsub : uIcc (0 : ℝ) γ ⊆ uIcc (0 : ℝ) 1 :=
    uIcc_subset_uIcc left_mem_uIcc (Set.mem_uIcc.2 (Or.inl ⟨hγ0.le, hγ1.le⟩))
  have hcont : Continuous fun y : ℝ => 3 * y - γ := by fun_prop
  have hP : IntervalIntegrable (fun y : ℝ => (3 * y - γ) * isoW y) volume 0 γ :=
    (rt_W_ii.mono_set hsub).continuousOn_mul hcont.continuousOn
  have hQ : IntervalIntegrable (fun y : ℝ => (3 * y - γ) * (√y)⁻¹) volume 0 γ :=
    (rt_invsqrt_ii hγ0).continuousOn_mul hcont.continuousOn
  have hg : IntervalIntegrable
      (fun y : ℝ => (3 * y - γ) * isoW y - isoWcirc (γ / 3) * ((3 * y - γ) * (√y)⁻¹))
      volume 0 γ := hP.sub (hQ.const_mul _)
  have hsplitI : ∫ y in (0 : ℝ)..γ,
      ((3 * y - γ) * isoW y - isoWcirc (γ / 3) * ((3 * y - γ) * (√y)⁻¹))
        = ∫ y in (0 : ℝ)..γ, (3 * y - γ) * isoW y := by
    rw [intervalIntegral.integral_sub hP (hQ.const_mul _), intervalIntegral.integral_const_mul,
      rt_zero_int hγ0, mul_zero, sub_zero]
  have hc0 : 0 < γ / 3 := by linarith
  have hc1 : γ / 3 < γ := by linarith
  have h1 : uIcc (0 : ℝ) (γ / 3) ⊆ uIcc (0 : ℝ) γ :=
    uIcc_subset_uIcc left_mem_uIcc (Set.mem_uIcc.2 (Or.inl ⟨hc0.le, hc1.le⟩))
  have h2 : uIcc (γ / 3) γ ⊆ uIcc (0 : ℝ) γ :=
    uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨hc0.le, hc1.le⟩)) right_mem_uIcc
  have hmid := intervalIntegral.integral_add_adjacent_intervals (hg.mono_set h1) (hg.mono_set h2)
  have hneg1 : ∫ y in (0 : ℝ)..γ / 3,
      ((3 * y - γ) * isoW y - isoWcirc (γ / 3) * ((3 * y - γ) * (√y)⁻¹)) < 0 := by
    have h : 0 < ∫ y in (0 : ℝ)..γ / 3,
        -((3 * y - γ) * isoW y - isoWcirc (γ / 3) * ((3 * y - γ) * (√y)⁻¹)) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on ((hg.mono_set h1).neg)
        (fun y hy => rt_sign_left hγ0 hγ1 hy) hc0
    rw [intervalIntegral.integral_neg] at h
    linarith
  have hneg2 : ∫ y in (γ / 3)..γ,
      ((3 * y - γ) * isoW y - isoWcirc (γ / 3) * ((3 * y - γ) * (√y)⁻¹)) < 0 := by
    have h : 0 < ∫ y in (γ / 3)..γ,
        -((3 * y - γ) * isoW y - isoWcirc (γ / 3) * ((3 * y - γ) * (√y)⁻¹)) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on ((hg.mono_set h2).neg)
        (fun y hy => rt_sign_right hγ0 hγ1 hy) hc1
    rw [intervalIntegral.integral_neg] at h
    linarith
  rw [← hsplitI]
  linarith

private lemma rt_isoI_eq' {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    isoI u = u * (∫ y in (0 : ℝ)..u, isoW y) - ∫ y in (0 : ℝ)..u, y * isoW y := by
  have := rt_isoI_eq hu0
  rw [min_eq_left hu1.le] at this
  exact this

private lemma rt_key2 {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    2 * γ * (∫ y in (0 : ℝ)..γ, isoW y) - 3 * isoI γ < 0 := by
  have hsub : uIcc (0 : ℝ) γ ⊆ uIcc (0 : ℝ) 1 :=
    uIcc_subset_uIcc left_mem_uIcc (Set.mem_uIcc.2 (Or.inl ⟨hγ0.le, hγ1.le⟩))
  have hw : IntervalIntegrable isoW volume 0 γ := rt_W_ii.mono_set hsub
  have hyw : IntervalIntegrable (fun y => y * isoW y) volume 0 γ := rt_yW_ii.mono_set hsub
  have hsplit : ∫ y in (0 : ℝ)..γ, (3 * y - γ) * isoW y
      = 3 * (∫ y in (0 : ℝ)..γ, y * isoW y) - γ * (∫ y in (0 : ℝ)..γ, isoW y) := by
    have e : (fun y : ℝ => (3 * y - γ) * isoW y)
        = fun y => 3 * (y * isoW y) - γ * isoW y := funext fun y => by ring
    rw [e, intervalIntegral.integral_sub (hyw.const_mul 3) (hw.const_mul γ),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have key := rt_key hγ0 hγ1
  rw [hsplit] at key
  rw [rt_isoI_eq' hγ0 hγ1]
  linarith

private lemma rt_isoI_pos {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) : 0 < isoI γ := by
  have hsub : uIcc (0 : ℝ) γ ⊆ uIcc (0 : ℝ) 1 :=
    uIcc_subset_uIcc left_mem_uIcc (Set.mem_uIcc.2 (Or.inl ⟨hγ0.le, hγ1.le⟩))
  have hint0 : IntervalIntegrable (fun y : ℝ => γ * isoW y - y * isoW y) volume 0 γ :=
    ((rt_W_ii.mono_set hsub).const_mul γ).sub (rt_yW_ii.mono_set hsub)
  have hint : IntervalIntegrable (fun y : ℝ => (γ - y) * isoW y) volume 0 γ := by
    convert hint0 using 1
    funext y
    ring
  unfold isoI
  rw [min_eq_left hγ1.le]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun x hx => ?_) hγ0
  have hwx : 0 < isoW x := rt_W_pos ⟨hx.1, by linarith [hx.2]⟩
  exact mul_pos (by linarith [hx.2]) hwx

private lemma rt_isoI_hasDeriv {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt isoI (∫ y in (0 : ℝ)..γ, isoW y) γ := by
  have hsub : uIcc (0 : ℝ) γ ⊆ uIcc (0 : ℝ) 1 :=
    uIcc_subset_uIcc left_mem_uIcc (Set.mem_uIcc.2 (Or.inl ⟨hγ.1.le, hγ.2.le⟩))
  have hw : IntervalIntegrable isoW volume 0 γ := rt_W_ii.mono_set hsub
  have hyw : IntervalIntegrable (fun y => y * isoW y) volume 0 γ := rt_yW_ii.mono_set hsub
  have hWc : ContinuousAt isoW γ := rt_W_cont.continuousAt (isOpen_Ioo.mem_nhds hγ)
  have hYc : ContinuousAt (fun y => y * isoW y) γ :=
    (continuousAt_id.mul hWc)
  have hF : HasDerivAt (fun u => ∫ y in (0 : ℝ)..u, isoW y) (isoW γ) γ :=
    intervalIntegral.integral_hasDerivAt_right hw
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo rt_W_cont γ hγ) hWc
  have hG : HasDerivAt (fun u => ∫ y in (0 : ℝ)..u, y * isoW y) (γ * isoW γ) γ :=
    intervalIntegral.integral_hasDerivAt_right hyw
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (continuousOn_id.mul rt_W_cont) γ hγ)
      hYc
  have h := ((hasDerivAt_id' γ).mul hF).sub hG
  have hev : isoI =ᶠ[𝓝 γ] fun u => u * (∫ y in (0 : ℝ)..u, isoW y)
      - ∫ y in (0 : ℝ)..u, y * isoW y := by
    filter_upwards [isOpen_Ioo.mem_nhds hγ] with u hu
    exact rt_isoI_eq' hu.1 hu.2
  exact (h.congr_deriv (by ring)).congr_of_eventuallyEq hev

private lemma rt_rho_eq_small {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    isoRho γ = 2 / Real.pi * isoI γ ^ 2 / γ ^ 3 := by
  unfold isoRho isoDriftConst
  rw [max_eq_left hγ1]
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hγ0' : γ ≠ 0 := ne_of_gt hγ0
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [mul_pow, div_pow, hsqrt2]
  field_simp

private lemma rt_rho_deriv_neg {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    deriv (fun u : ℝ => 2 / Real.pi * isoI u ^ 2 / u ^ 3) γ < 0 := by
  have hγ0 : 0 < γ := hγ.1
  have hγ1 : γ < 1 := hγ.2
  have hI := rt_isoI_hasDeriv hγ
  have hd := (((hI.pow 2).const_mul (2 / Real.pi)).div (hasDerivAt_pow 3 γ)
    (pow_ne_zero 3 hγ0.ne'))
  have hIpos := rt_isoI_pos hγ0 hγ1
  have hkey := rt_key2 hγ0 hγ1
  have hp : 0 < 2 / Real.pi := by positivity
  have hclean : (2 / Real.pi * (↑(2 : ℕ) * isoI γ ^ (2 - 1) * ∫ y in (0 : ℝ)..γ, isoW y) * γ ^ 3
      - 2 / Real.pi * isoI γ ^ 2 * (↑(3 : ℕ) * γ ^ (3 - 1))) / (γ ^ 3) ^ 2
      = -(2 / Real.pi * isoI γ * γ ^ 2 * (3 * isoI γ - 2 * γ * ∫ y in (0 : ℝ)..γ, isoW y))
        / (γ ^ 3) ^ 2 := by
    norm_num <;> ring
  have hd2 := hd.congr_deriv hclean
  rw [show (fun u : ℝ => 2 / Real.pi * isoI u ^ 2 / u ^ 3)
      = (fun y : ℝ => 2 / Real.pi * (isoI ^ 2) y) / (fun x : ℝ => x ^ 3) from rfl, hd2.deriv]
  apply div_neg_of_neg_of_pos
  · apply neg_lt_zero.2
    exact mul_pos (mul_pos (mul_pos hp hIpos) (pow_pos hγ0 2)) (by linarith)
  · positivity

private lemma rt_rho_strictAnti : StrictAntiOn isoRho (Ioc 0 1) := by
  have hcont : ContinuousOn isoRho (Ioc 0 1) :=
    rt_rho_cont.mono (fun x hx => Set.mem_Ioi.2 hx.1)
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 1) hcont
  intro x hx
  rw [interior_Ioc] at hx
  have hfun : isoRho =ᶠ[𝓝 x] fun u : ℝ => 2 / Real.pi * isoI u ^ 2 / u ^ 3 := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with u hu
    exact rt_rho_eq_small hu.1 hu.2.le
  rw [hfun.deriv_eq]
  exact rt_rho_deriv_neg hx

private lemma rt_rho_min_one {γ : ℝ} (hγ : 0 < γ) : isoRho 1 ≤ isoRho γ := by
  rcases le_total γ 1 with h | h
  · exact rt_rho_strictAnti.antitoneOn ⟨hγ, h⟩ ⟨zero_lt_one, le_rfl⟩ h
  · exact rt_rho_strictMono_ge_one.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h

private lemma rt_rho_unique {γ : ℝ} (hγ : 0 < γ) (h : isoRho γ = isoRho 1) : γ = 1 := by
  rcases lt_trichotomy γ 1 with h1 | h1 | h1
  · have := rt_rho_strictAnti ⟨hγ, h1.le⟩ ⟨zero_lt_one, le_rfl⟩ h1
    linarith
  · exact h1
  · have := rt_rho_strictMono_ge_one (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h1.le) h1
    linarith

private lemma rt_I_subst {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    isoI γ = γ * √γ * ∫ s in (0 : ℝ)..1, (1 - s) * (√s)⁻¹ * isoWcirc (γ * s) := by
  have hnull : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simp
  have hsubst := intervalIntegral.integral_comp_mul_left (f := fun y => (γ - y) * isoW y)
    (a := 0) (b := 1) hγ0.ne'
  rw [mul_zero, mul_one] at hsubst
  have hYI : ∫ y in (0 : ℝ)..γ, (γ - y) * isoW y
      = γ * ∫ x in (0 : ℝ)..1, (γ - γ * x) * isoW (γ * x) := by
    rw [hsubst, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hγ0.ne', one_mul]
  have hpt : ∫ x in (0 : ℝ)..1, (γ - γ * x) * isoW (γ * x)
      = √γ * ∫ x in (0 : ℝ)..1, (1 - x) * (√x)⁻¹ * isoWcirc (γ * x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hnull] with x hx1 hxI
    rw [Set.uIoc_of_le zero_le_one] at hxI
    have hxI' : x ∈ Ioo (0 : ℝ) 1 := ⟨hxI.1, lt_of_le_of_ne hxI.2 hx1⟩
    show (γ - γ * x) * isoW (γ * x) = √γ * ((1 - x) * (√x)⁻¹ * isoWcirc (γ * x))
    have hγx : γ * x ∈ Ioo (0 : ℝ) 1 := ⟨mul_pos hγ0 hxI'.1, by nlinarith [hxI'.2]⟩
    rw [rt_diff_eq hγx, Real.sqrt_mul hγ0.le x]
    have hs : √x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hxI'.1)
    have hg : √γ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hγ0)
    have e : γ * (√γ)⁻¹ = √γ := (mul_inv_eq_iff_eq_mul₀ hg).2 (Real.mul_self_sqrt hγ0.le).symm
    have key : (γ - γ * x) * (isoWcirc (γ * x) * (√γ * √x)⁻¹)
        = (γ * (√γ)⁻¹) * ((1 - x) * (√x)⁻¹ * isoWcirc (γ * x)) := by
      field_simp
    rw [key, e]
  unfold isoI
  rw [min_eq_left hγ1.le, hYI, hpt]
  ring

private lemma rt_K_const : ∫ s in (0 : ℝ)..1, (1 - s) * (√s)⁻¹ = 4 / 3 := by
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => 2 * √y - 2 / 3 * (y * √y)) ((1 - x) * (√x)⁻¹) x := by
    intro x hx
    have hs : √x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx.1)
    have hsq : √x * √x = x := Real.mul_self_sqrt hx.1.le
    have hx' : x * (√x)⁻¹ = √x := (mul_inv_eq_iff_eq_mul₀ hs).2 hsq.symm
    have hA := (Real.hasDerivAt_sqrt hx.1.ne').const_mul 2
    have hB := (((hasDerivAt_id' x).mul (Real.hasDerivAt_sqrt hx.1.ne'))).const_mul (2 / 3)
    have h := hA.sub hB
    exact h.congr_deriv (by linear_combination (2 / 3) * hx')
  have hcont : ContinuousOn (fun y : ℝ => 2 * √y - 2 / 3 * (y * √y)) (Icc 0 1) :=
    (by fun_prop : Continuous fun y : ℝ => 2 * √y - 2 / 3 * (y * √y)).continuousOn
  have hint : IntervalIntegrable (fun s : ℝ => (1 - s) * (√s)⁻¹) volume 0 1 :=
    (rt_invsqrt_ii one_pos).continuousOn_mul
      (by fun_prop : Continuous fun s : ℝ => 1 - s).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hcont
    (fun x hx => (hderiv x hx).hasDerivWithinAt) hint]
  norm_num

private lemma rt_wc_cont : ContinuousOn isoWcirc (Ioo 0 1) :=
  Real.continuous_sqrt.continuousOn.mul rt_W_cont

private lemma rt_K_tendsto :
    Tendsto (fun γ : ℝ => ∫ s in (0 : ℝ)..1, (1 - s) * (√s)⁻¹ * isoWcirc (γ * s))
      (𝓝[>] 0) (𝓝 (4 / 3)) := by
  have hcontF : ∀ γ ∈ Ioo (0 : ℝ) 1,
      ContinuousOn (fun s : ℝ => (1 - s) * (√s)⁻¹ * isoWcirc (γ * s)) (Ioo 0 1) := by
    intro γ hγ
    have hA : ContinuousOn (fun s : ℝ => (1 - s) * (√s)⁻¹) (Ioo 0 1) :=
      (continuousOn_const.sub continuousOn_id).mul
        (Real.continuous_sqrt.continuousOn.inv₀ (fun s hs => (Real.sqrt_pos.2 hs.1).ne'))
    have hB : ContinuousOn (fun s : ℝ => isoWcirc (γ * s)) (Ioo 0 1) :=
      rt_wc_cont.comp (continuousOn_const.mul continuousOn_id)
        (fun s hs => ⟨mul_pos hγ.1 hs.1, by linarith [hs.2, mul_lt_of_lt_one_left hs.1 hγ.2]⟩)
    exact hA.mul hB
  have hF_meas : ∀ᶠ γ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun s : ℝ => (1 - s) * (√s)⁻¹ * isoWcirc (γ * s))
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with γ hγ
    rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact (hcontF γ hγ).aestronglyMeasurable measurableSet_Ioo
  have h_bound : ∀ᶠ γ in 𝓝[>] (0 : ℝ), ∀ᵐ s : ℝ ∂volume, s ∈ Set.uIoc (0 : ℝ) 1 →
      ‖(1 - s) * (√s)⁻¹ * isoWcirc (γ * s)‖ ≤ (1 - s) * (√s)⁻¹ := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with γ hγ
    refine Filter.Eventually.of_forall (fun s hs => ?_)
    rw [Set.uIoc_of_le zero_le_one] at hs
    have hγs : γ * s ∈ Ioo (0 : ℝ) 1 :=
      ⟨mul_pos hγ.1 hs.1, by linarith [hs.2, mul_lt_of_lt_one_left hs.1 hγ.2]⟩
    have hwc := rt_wcirc_bounds hγs
    have hA : 0 ≤ (1 - s) * (√s)⁻¹ :=
      mul_nonneg (by linarith [hs.2]) (inv_nonneg.2 (Real.sqrt_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA hwc.1.le)]
    exact mul_le_of_le_one_right hA hwc.2
  have hbound_int : IntervalIntegrable (fun s : ℝ => (1 - s) * (√s)⁻¹) volume 0 1 :=
    (rt_invsqrt_ii one_pos).continuousOn_mul
      (by fun_prop : Continuous fun s : ℝ => 1 - s).continuousOn
  have h_lim : ∀ᵐ s : ℝ ∂volume, s ∈ Set.uIoc (0 : ℝ) 1 →
      Tendsto (fun γ : ℝ => (1 - s) * (√s)⁻¹ * isoWcirc (γ * s)) (𝓝[>] 0)
        (𝓝 ((fun s : ℝ => (1 - s) * (√s)⁻¹ * 1) s)) := by
    refine Filter.Eventually.of_forall (fun s hs => ?_)
    rw [Set.uIoc_of_le zero_le_one] at hs
    have hmap : Tendsto (fun γ : ℝ => γ * s) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h0 : Tendsto (fun γ : ℝ => γ * s) (𝓝 0) (𝓝 (0 * s)) :=
          (continuous_id.mul continuous_const).tendsto 0
        rw [zero_mul] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with γ hγ
        exact mul_pos hγ hs.1
    have hwc : Tendsto (fun γ : ℝ => isoWcirc (γ * s)) (𝓝[>] 0) (𝓝 1) :=
      rt_wcirc_tendsto.comp hmap
    exact hwc.const_mul ((1 - s) * (√s)⁻¹)
  have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun s : ℝ => (1 - s) * (√s)⁻¹) hF_meas h_bound hbound_int h_lim
  simp only [mul_one] at hlim
  rw [rt_K_const] at hlim
  exact hlim

private lemma rt_alg (γ K : ℝ) (hγ : 0 < γ) :
    2 / Real.pi * (γ * √γ * K) ^ 2 / γ ^ 3 = 2 / Real.pi * K ^ 2 := by
  have hsq : √γ ^ 2 = γ := Real.sq_sqrt hγ.le
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [mul_pow, mul_pow, hsq]
  field_simp

private lemma rt_rho_tendsto_zero :
    Tendsto isoRho (𝓝[>] 0) (𝓝 (32 / (9 * Real.pi))) := by
  have h2 := ((rt_K_tendsto.pow 2).const_mul (2 / Real.pi))
  have hEq : (fun γ : ℝ => 2 / Real.pi * (∫ s in (0 : ℝ)..1, (1 - s) * (√s)⁻¹ * isoWcirc (γ * s)) ^ 2)
      =ᶠ[𝓝[>] (0 : ℝ)] isoRho := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with γ hγ
    rw [rt_rho_eq_small hγ.1 hγ.2.le, rt_I_subst hγ.1 hγ.2]
    exact (rt_alg γ _ hγ.1).symm
  have hval : (2 / Real.pi) * (4 / 3) ^ 2 = 32 / (9 * Real.pi) := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [← hval]
  exact h2.congr' hEq

private lemma rt_rho_lt_sup {γ : ℝ} (hγ : 0 < γ) : isoRho γ < 32 / (9 * Real.pi) := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hL1 : 1 < 32 / (9 * Real.pi) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith [Real.pi_pos]
  rcases lt_or_ge γ 1 with h1 | h1
  · have hm : (0 : ℝ) < γ / 2 := by linarith
    have hanti : isoRho γ < isoRho (γ / 2) :=
      rt_rho_strictAnti ⟨hm, by linarith⟩ ⟨hγ, h1.le⟩ (by linarith)
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), isoRho (γ / 2) ≤ isoRho δ := by
      filter_upwards [Ioo_mem_nhdsGT hm] with δ hδ
      exact rt_rho_strictAnti.antitoneOn ⟨hδ.1, by linarith [hδ.2]⟩ ⟨hm, by linarith⟩ hδ.2.le
    have hle : isoRho (γ / 2) ≤ 32 / (9 * Real.pi) := ge_of_tendsto rt_rho_tendsto_zero hev
    exact lt_of_lt_of_le hanti hle
  · rw [rt_rho_ge_one h1]
    obtain ⟨hd0, hd1⟩ := rt_d_bounds
    have hx0 : 0 < isoD / isoA / γ := div_pos hd0 (by linarith)
    have hx1 : isoD / isoA / γ < 1 := lt_of_le_of_lt (div_le_self hd0.le h1) hd1
    nlinarith

private lemma rt_rho_isLUB : IsLUB (isoRho '' Ioi 0) (32 / (9 * Real.pi)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    exact (rt_rho_lt_sup (Set.mem_Ioi.1 hγ)).le
  · intro u hu
    by_contra hlt
    push_neg at hlt
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), u < isoRho δ :=
      rt_rho_tendsto_zero.eventually (lt_mem_nhds hlt)
    obtain ⟨δ, hδ⟩ := (hev.and self_mem_nhdsWithin).exists
    exact absurd (hu (Set.mem_image_of_mem isoRho hδ.2)) (not_le.2 hδ.1)

/-! ## Extrema of the isotropic ratio -/

/-- thm:app-phase-iso-extrema, snapshot `cr-2026-10-23`. The continuity and monotonicity of
`ρ`, its minimum `ρ(1) = π C(1)²` (attained only at `γ = 1`), its supremum `32/(9π)` (the limit at
`0`, not attained), its limit `1` at `∞`, and the closed form for `γ ≥ 1`, with the constant
`𝗱 = 𝒟/𝒜 = 1 − √π C(1) ∈ (0,1)`.

LaTeX (verbatim, `section.tex` l.805–817):
```
\begin{theorem}[Extrema of the isotropic ratio]\label{thm:app-phase-iso-extrema}
The ratio $\rho$ is
continuous on $(0,\infty)$, strictly decreasing on $(0,1]$ and strictly
increasing on $[1,\infty)$, and
\[
\min_{\gamma>0}\rho(\gamma)=\rho(1)=\pi C(1)^2,\qquad
\sup_{\gamma>0}\rho(\gamma)=\lim_{\gamma\downarrow0}\rho(\gamma)=\frac{32}{9\pi},\qquad
\lim_{\gamma\to\infty}\rho(\gamma)=1 .
\]
The minimum is attained only at $\gamma=1$ and the supremum is not
attained. For $\gamma\ge1$, $\rho(\gamma)=(1-\mathsf d/\gamma)^2$ with
$\mathsf d\defeq\mathcal D/\mathcal A=1-\sqrt\pi\,C(1)\in(0,1)$.
\end{theorem}
```
-/
theorem thm_app_phase_iso_extrema :
    ContinuousOn isoRho (Ioi 0) ∧
    StrictAntiOn isoRho (Ioc 0 1) ∧ StrictMonoOn isoRho (Ici 1) ∧
    (∀ γ : ℝ, 0 < γ → isoRho 1 ≤ isoRho γ) ∧
    isoRho 1 = Real.pi * isoDriftConst 1 ^ 2 ∧
    (∀ γ : ℝ, 0 < γ → isoRho γ = isoRho 1 → γ = 1) ∧
    IsLUB (isoRho '' Ioi 0) (32 / (9 * Real.pi)) ∧
    (∀ γ : ℝ, 0 < γ → isoRho γ ≠ 32 / (9 * Real.pi)) ∧
    Tendsto isoRho (𝓝[>] 0) (𝓝 (32 / (9 * Real.pi))) ∧
    Tendsto isoRho atTop (𝓝 1) ∧
    (0 < isoD / isoA ∧ isoD / isoA < 1) ∧
    isoD / isoA = 1 - Real.sqrt Real.pi * isoDriftConst 1 ∧
    (∀ γ : ℝ, 1 ≤ γ → isoRho γ = (1 - (isoD / isoA) / γ) ^ 2) := by
  exact ⟨rt_rho_cont, rt_rho_strictAnti, rt_rho_strictMono_ge_one,
    fun γ hγ => rt_rho_min_one hγ, rt_rho_one,
    fun γ hγ h => rt_rho_unique hγ h, rt_rho_isLUB,
    fun γ hγ => (rt_rho_lt_sup hγ).ne, rt_rho_tendsto_zero, rt_rho_tendsto_top,
    rt_d_bounds, rt_d_C1, fun γ hγ => rt_rho_ge_one hγ⟩

/-! ## The isotropic comparison -/

/-! ## Helpers for `thm_app_phase_iso` (task P-H.12.P4) -/

private lemma p4_err (A δ : ℝ) (hδ : 0 < δ) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ s : ℝ, S ≤ s → (1 / s) * (A + Real.log s + 2 * (1 / s)) < δ := by
  have h1 : Tendsto (fun s : ℝ => 1 / s) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero
  have hL : Tendsto (fun s : ℝ => Real.log s / s) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hg : Tendsto (fun s : ℝ => A * (1 / s) + Real.log s / s + (2 * (1 / s)) * (1 / s)) atTop
      (𝓝 (A * 0 + 0 + (2 * 0) * 0)) :=
    ((h1.const_mul A).add hL).add ((h1.const_mul 2).mul h1)
  rw [show A * 0 + 0 + (2 * 0) * 0 = (0 : ℝ) by ring] at hg
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.1 ((tendsto_order.1 hg).2 δ hδ)
  refine ⟨max S₀ 2, le_max_right _ _, fun s hs => ?_⟩
  have hs0 := hS₀ s (le_trans (le_max_left _ _) hs)
  have heq : (1 / s) * (A + Real.log s + 2 * (1 / s))
      = A * (1 / s) + Real.log s / s + (2 * (1 / s)) * (1 / s) := by ring
  rw [heq]
  exact hs0

private lemma p4_B_large {κ : ℝ} (hκ : 0 < κ) :
    ∃ B₀ : ℕ, 5 ≤ B₀ ∧ ∀ B : ℕ, B₀ ≤ B → ((1 - 4 / (B : ℝ)) ^ 2)⁻¹ ≤ 1 + κ := by
  have h4 : Tendsto (fun x : ℝ => 4 / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlim : Tendsto (fun x : ℝ => ((1 - 4 / x) ^ 2)⁻¹) atTop (𝓝 1) := by
    have := (((tendsto_const_nhds (x := (1 : ℝ))).sub h4).pow 2).inv₀ (by norm_num)
    simpa using this
  have h2 := hlim.comp tendsto_natCast_atTop_atTop
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.1 ((tendsto_order.1 h2).2 (1 + κ) (by linarith))
  refine ⟨max B₁ 5, le_max_right _ _, fun B hB => ?_⟩
  exact (hB₁ B (le_trans (le_max_left _ _) hB)).le

private lemma p4_pos {N B : ℕ} {NB ε T : ℝ} {mS mN : RowModel (Fin N)}
    (h : IsIsoSetting N B NB ε T mS mN) :
    (0 : ℝ) < N ∧ (0 : ℝ) < B ∧ 0 < NB ∧ 0 < ε ∧ 0 < mS.F0 := by
  unfold IsIsoSetting at h
  obtain ⟨hN1, hB1, hNBlo, -, hT1, hε, -, -, -, -, -, -, -, hFT, -, -⟩ := h
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hBp : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hNBp : 0 < NB :=
    lt_of_lt_of_le (mul_pos (div_pos two_pos Real.pi_pos) (Real.sqrt_pos.2 hBp))
      (le_trans (le_max_left _ _) hNBlo)
  have hF0p : 0 < mS.F0 := lt_trans (mul_pos (by linarith) hε) hFT
  exact ⟨hNp, hBp, hNBp, hε, hF0p⟩

private lemma p4_r_facts {N B : ℕ} {NB ε T : ℝ} {mS mN : RowModel (Fin N)}
    (h : IsIsoSetting N B NB ε T mS mN) :
    1 ≤ (B : ℝ) / NB ^ 2 ∧ (4 < B → (B : ℝ) / NB ^ 2 ≤ ((1 - 4 / (B : ℝ)) ^ 2)⁻¹) := by
  obtain ⟨-, -, -, -, -, hr1, -, hr2⟩ := prop_app_phase_iso_ratio N B NB ε T mS mN h
  exact ⟨hr1, hr2⟩

private lemma p4_rho_pos {γ : ℝ} (hγ : 0 < γ) : 0 < isoRho γ := by
  have hC := p12_C_pos (show (0 : ℝ) < 1 by norm_num)
  have h1 : 0 < isoRho 1 := by
    rw [rt_rho_one]
    exact mul_pos Real.pi_pos (pow_pos hC 2)
  exact lt_of_lt_of_le h1 (rt_rho_min_one hγ)

private lemma p4_mul_bound (u r : ℝ) (hr : 0 ≤ r) :
    |u * r - 1| ≤ |u - 1| * r + |r - 1| := by
  have heq : u * r - 1 = (u - 1) * r + (r - 1) := by ring
  rw [heq]
  calc |(u - 1) * r + (r - 1)| ≤ |(u - 1) * r| + |r - 1| := abs_add_le _ _
    _ = |u - 1| * r + |r - 1| := by rw [abs_mul, abs_of_nonneg hr]

private lemma p4_asymp_pair (T : ℝ) (hT : 1 < T) (δ : ℝ) (hδ : 0 < δ) :
    ∃ θ : ℝ, 0 < θ ∧
      ∀ (N B : ℕ) (NB ε : ℝ) (mS mN : RowModel (Fin N)), IsIsoSetting N B NB ε T mS mN →
        ε / mS.F0 < θ →
        (∀ Qs : Fin N → ℝ → ℝ, IsGlobalRowSolution mS Qs →
          |(firstHit (mS.risk Qs) (T * ε)).toReal
              / (min (B : ℝ) (N : ℝ) / (4 * isoDriftConst ((N : ℝ) / B) ^ 2)
                  * Real.sqrt (mS.F0 / ε)) - 1| ≤ δ) ∧
        (∀ Qn : Fin N → ℝ → ℝ, IsGlobalRowSolution mN Qn →
          |(firstHit (mN.risk Qn) (T * ε)).toReal
              / ((N : ℝ) ^ 2 * Real.pi / (4 * NB ^ 2) * Real.sqrt (mS.F0 / ε)) - 1| ≤ δ) := by
  obtain ⟨S, hS2, hSb⟩ := p4_err (Real.sqrt T + |Real.log (Real.sqrt T - 1)|) δ hδ
  refine ⟨1 / S ^ 2, by positivity, ?_⟩
  intro N B NB ε mS mN h hθ
  obtain ⟨hNpos, hBpos, hNBpos, hε, hF0⟩ := p4_pos h
  have hNBne : NB ≠ 0 := hNBpos.ne'
  unfold IsIsoSetting at h
  obtain ⟨-, -, -, -, -, -, hμS, hμN, hdS, hdN, hvS, hvN, hQ0, hFT, hηS, hηN⟩ := h
  have hFeq : mN.F0 = mS.F0 := by
    unfold RowModel.F0
    rw [hQ0]
    simp only [hμS, hμN]
  have hFN : T * ε < mN.F0 := by rw [hFeq]; exact hFT
  have hsumS : commonVtot mS = min (B : ℝ) (N : ℝ) := by
    unfold commonVtot
    simp only [hμS, one_mul]
    exact hvS
  have hsumN : commonVtot mN = (N : ℝ) ^ 2 := by
    unfold commonVtot
    simp only [hμN, one_mul]
    exact hvN
  have hvS' : 0 < commonVtot mS := by rw [hsumS]; exact lt_min hBpos hNpos
  have hvN' : 0 < commonVtot mN := by rw [hsumN]; positivity
  have hγ : (0 : ℝ) < (N : ℝ) / B := div_pos hNpos hBpos
  have hdS0 : 0 < isoDriftConst ((N : ℝ) / B) := p12_C_pos hγ
  have hdN0 : 0 < NB / Real.sqrt Real.pi := div_pos hNBpos (Real.sqrt_pos.2 Real.pi_pos)
  have hmS := thm_app_phase_matched mS (isoDriftConst ((N : ℝ) / B)) hdS0 hdS hvS' ε T hε hT
    hFT hηS mN (NB / Real.sqrt Real.pi) hdN0 hdN hvN' hηN hFN hFeq
  have hmN := thm_app_phase_matched mN (NB / Real.sqrt Real.pi) hdN0 hdN hvN' ε T hε hT
    hFN hηN mS (isoDriftConst ((N : ℝ) / B)) hdS0 hdS hvS' hηS hFT hFeq.symm
  have hS0 : 0 < S := by linarith
  have hθ' : ε / mS.F0 * S ^ 2 < 1 := (lt_div_iff₀ (by positivity)).1 hθ
  have h2 : ε * S ^ 2 < mS.F0 := by
    have h' := hθ'
    rw [div_mul_eq_mul_div, div_lt_one hF0] at h'
    exact h'
  have h3 : S ^ 2 ≤ mS.F0 / ε := by
    rw [le_div_iff₀ hε, mul_comm]
    exact h2.le
  have hsS : S ≤ Real.sqrt (mS.F0 / ε) :=
    calc S = Real.sqrt (S ^ 2) := (Real.sqrt_sq hS0.le).symm
      _ ≤ Real.sqrt (mS.F0 / ε) := Real.sqrt_le_sqrt h3
  have hle : 1 / Real.sqrt (mS.F0 / ε) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (le_trans hS2 hsS)
  refine ⟨fun Qs hQs => ?_, fun Qn hQn => ?_⟩
  · have bS := (hmS.1 Qs hQs).2.2 hle
    unfold matchedX at bS
    rw [hsumS] at bS
    exact le_trans bS (le_of_lt (hSb _ hsS))
  · have bN := (hmN.1 Qn hQn).2.2 (by unfold matchedX; rw [hFeq]; exact hle)
    unfold matchedX at bN
    rw [hsumN, hFeq] at bN
    have hcoef : (N : ℝ) ^ 2 / (4 * (NB / Real.sqrt Real.pi) ^ 2)
        = (N : ℝ) ^ 2 * Real.pi / (4 * NB ^ 2) := by
      rw [div_pow, Real.sq_sqrt Real.pi_pos.le]
      field_simp
    rw [hcoef] at bN
    exact le_trans bN (le_of_lt (hSb _ hsS))

private lemma p4_ii_a (T : ℝ) (hT : 1 < T) : ∀ δ : ℝ, 0 < δ → ∃ B₀ : ℕ, ∃ θ : ℝ, 0 < θ ∧
    ∀ (N B : ℕ) (NB ε : ℝ) (mS mN : RowModel (Fin N)), IsIsoSetting N B NB ε T mS mN →
      B₀ ≤ B → ε / mS.F0 < θ →
      ∀ Qn : Fin N → ℝ → ℝ, IsGlobalRowSolution mN Qn →
        |(firstHit (mN.risk Qn) (T * ε)).toReal
            / ((N : ℝ) ^ 2 * Real.pi / (4 * (B : ℝ)) * Real.sqrt (mS.F0 / ε)) - 1| ≤ δ := by
  intro δ hδ
  have hκ : 0 < min 1 (δ / 8) := lt_min one_pos (by linarith)
  obtain ⟨B₀, hB₀5, hB₀⟩ := p4_B_large hκ
  obtain ⟨θ, hθ, hpair⟩ := p4_asymp_pair T hT (δ / 8) (by linarith)
  refine ⟨B₀, θ, hθ, fun N B NB ε mS mN h hB hθε Qn hQn => ?_⟩
  have hN := (hpair N B NB ε mS mN h hθε).2 Qn hQn
  obtain ⟨hr1, hr2⟩ := p4_r_facts h
  have hB4 : 4 < B := by omega
  have hr3 := hB₀ B hB
  have hr4 := hr2 hB4
  obtain ⟨hNp, hBp, hNBp, hεp, hF0p⟩ := p4_pos h
  have hs : 0 < Real.sqrt (mS.F0 / ε) := Real.sqrt_pos.2 (div_pos hF0p hεp)
  have hr0 : (0 : ℝ) ≤ (B : ℝ) / NB ^ 2 := div_nonneg hBp.le (sq_nonneg _)
  have hNBne : NB ≠ 0 := hNBp.ne'
  have hNne : (N : ℝ) ≠ 0 := hNp.ne'
  have hBne : (B : ℝ) ≠ 0 := hBp.ne'
  have hsne : Real.sqrt (mS.F0 / ε) ≠ 0 := hs.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hid : (firstHit (mN.risk Qn) (T * ε)).toReal
        / ((N : ℝ) ^ 2 * Real.pi / (4 * (B : ℝ)) * Real.sqrt (mS.F0 / ε))
      = ((firstHit (mN.risk Qn) (T * ε)).toReal
          / ((N : ℝ) ^ 2 * Real.pi / (4 * NB ^ 2) * Real.sqrt (mS.F0 / ε)))
        * ((B : ℝ) / NB ^ 2) := by
    field_simp
  rw [hid]
  have hk := p4_mul_bound ((firstHit (mN.risk Qn) (T * ε)).toReal
          / ((N : ℝ) ^ 2 * Real.pi / (4 * NB ^ 2) * Real.sqrt (mS.F0 / ε))) ((B : ℝ) / NB ^ 2) hr0
  have hr2' : (B : ℝ) / NB ^ 2 ≤ 2 := by linarith [min_le_left 1 (δ / 8)]
  have hrm1 : (B : ℝ) / NB ^ 2 - 1 ≤ δ / 8 := by linarith [min_le_right 1 (δ / 8)]
  have h1 : |(firstHit (mN.risk Qn) (T * ε)).toReal
          / ((N : ℝ) ^ 2 * Real.pi / (4 * NB ^ 2) * Real.sqrt (mS.F0 / ε)) - 1|
        * ((B : ℝ) / NB ^ 2) ≤ δ / 8 * 2 :=
    mul_le_mul hN hr2' hr0 (by linarith)
  have h2 : |(B : ℝ) / NB ^ 2 - 1| ≤ δ / 8 := abs_le.2 ⟨by linarith, hrm1⟩
  linarith

private lemma p4_ii_b (T : ℝ) : ∀ δ : ℝ, 0 < δ → ∃ B₀ : ℕ, ∀ (N B : ℕ) (NB ε : ℝ)
    (mS mN : RowModel (Fin N)), IsIsoSetting N B NB ε T mS mN → B₀ ≤ B →
    ∀ Qs Qn : Fin N → ℝ → ℝ, IsGlobalRowSolution mS Qs → IsGlobalRowSolution mN Qn →
      |((firstHit (mN.risk Qn) (T * ε)).toReal / (firstHit (mS.risk Qs) (T * ε)).toReal)
          / isoRho ((N : ℝ) / B) - 1| ≤ δ := by
  intro δ hδ
  obtain ⟨B₀, hB₀5, hB₀⟩ := p4_B_large hδ
  refine ⟨B₀, fun N B NB ε mS mN h hB Qs Qn hQs hQn => ?_⟩
  obtain ⟨hNp, hBp, -, -, -⟩ := p4_pos h
  obtain ⟨hr1, hr2⟩ := p4_r_facts h
  obtain ⟨-, -, hratio, -, -, -, -, -⟩ := prop_app_phase_iso_ratio N B NB ε T mS mN h
  have hρ : isoRho ((N : ℝ) / B) ≠ 0 := (p4_rho_pos (div_pos hNp hBp)).ne'
  rw [(hratio Qs Qn hQs hQn).2.2, mul_div_assoc, mul_div_cancel_left₀ _ hρ]
  have hB4 : 4 < B := by omega
  have hr3 := hB₀ B hB
  have hr4 := hr2 hB4
  rw [abs_le]
  constructor <;> linarith

private lemma p4_ii_c (T : ℝ) : ∀ γ₀ : ℝ, 0 < γ₀ → ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
    ∃ B₀ : ℕ, ∀ (N B : ℕ) (NB ε : ℝ) (mS mN : RowModel (Fin N)),
      IsIsoSetting N B NB ε T mS mN → B₀ ≤ B → |(N : ℝ) / B - γ₀| < η →
      ∀ Qs Qn : Fin N → ℝ → ℝ, IsGlobalRowSolution mS Qs → IsGlobalRowSolution mN Qn →
        |(firstHit (mN.risk Qn) (T * ε)).toReal / (firstHit (mS.risk Qs) (T * ε)).toReal
            - isoRho γ₀| ≤ δ := by
  intro γ₀ hγ₀ δ hδ
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.1
    ((rt_rho_cont.continuousAt (Ioi_mem_nhds hγ₀))) (δ / 8) (by linarith)
  have hκ : 0 < min 1 (δ / 8) := lt_min one_pos (by linarith)
  obtain ⟨B₀, hB₀5, hB₀⟩ := p4_B_large hκ
  refine ⟨η, hη, B₀, fun N B NB ε mS mN h hB hdist Qs Qn hQs hQn => ?_⟩
  obtain ⟨hNp, hBp, -, -, -⟩ := p4_pos h
  obtain ⟨hr1, hr2⟩ := p4_r_facts h
  obtain ⟨-, -, hratio, -, -, -, -, -⟩ := prop_app_phase_iso_ratio N B NB ε T mS mN h
  have hγ : (0 : ℝ) < (N : ℝ) / B := div_pos hNp hBp
  have hρc : |isoRho ((N : ℝ) / B) - isoRho γ₀| < δ / 8 := by
    have h' := hcont (show dist ((N : ℝ) / B) γ₀ < η by rw [Real.dist_eq]; exact hdist)
    rw [Real.dist_eq] at h'
    exact h'
  have hρ0 : 0 < isoRho γ₀ := p4_rho_pos hγ₀
  have hρ2 : isoRho γ₀ < 2 := by
    have h1 := rt_rho_lt_sup hγ₀
    have h2 : 32 / (9 * Real.pi) < 2 := by
      rw [div_lt_iff₀ (by positivity)]
      linarith [Real.pi_gt_three]
    linarith
  have hB4 : 4 < B := by omega
  have hr3 := hB₀ B hB
  have hr4 := hr2 hB4
  have hrle2 : (B : ℝ) / NB ^ 2 ≤ 2 := by linarith [min_le_left 1 (δ / 8)]
  have hrm1 : (B : ℝ) / NB ^ 2 - 1 ≤ δ / 8 := by linarith [min_le_right 1 (δ / 8)]
  have hr0 : (0 : ℝ) ≤ (B : ℝ) / NB ^ 2 := by linarith
  rw [(hratio Qs Qn hQs hQn).2.2, mul_div_assoc]
  have key : isoRho ((N : ℝ) / B) * ((B : ℝ) / NB ^ 2) - isoRho γ₀
      = (isoRho ((N : ℝ) / B) - isoRho γ₀) * ((B : ℝ) / NB ^ 2)
        + isoRho γ₀ * ((B : ℝ) / NB ^ 2 - 1) := by ring
  have h1 : |(isoRho ((N : ℝ) / B) - isoRho γ₀) * ((B : ℝ) / NB ^ 2)| ≤ δ / 8 * 2 := by
    rw [abs_mul, abs_of_nonneg hr0]
    exact mul_le_mul hρc.le hrle2 hr0 (by linarith)
  have h2 : |isoRho γ₀ * ((B : ℝ) / NB ^ 2 - 1)| ≤ 2 * (δ / 8) := by
    rw [abs_mul, abs_of_pos hρ0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (B : ℝ) / NB ^ 2 - 1)]
    exact mul_le_mul hρ2.le hrm1 (by linarith) (by norm_num)
  rw [key]
  exact (abs_add_le _ _).trans (by linarith)

/-- thm:app-phase-iso, snapshot `cr-2026-10-23`. Fixed `T > 1`. (i) The ratio of the times is
`ρ(γ) B / 𝒩_B²`, and as `ε/F₀ → 0` the two times are asymptotic to their explicit
equivalents, uniformly in `N`, `B`, `C(γ)`. (ii) If `B → ∞` (with `N`, `γ` varying) the s-SGD
time is `∼ πN²/(4B) √(F₀/ε)`, the ratio divided by `ρ(γ)` tends to `1`, and the ratio tends to
`ρ(γ₀)` when `γ → γ₀ ∈ (0,∞)`. (iii) The bounds `ρ(1) ≤ ρ(γ) < 32/(9π)` and
`ρ(1) ≤ ratio ≤ (π²/4)(32/(9π))`, together with the limits of `ρ`.

LaTeX (verbatim, `section.tex` l.880–908):
```
\begin{theorem}[Isotropic comparison]\label{thm:app-phase-iso}
Let $N,B\ge1$, $\gamma=N/B$, $m=\min(B,N)$, and take the isotropic arrays
\cref{eqn:app-phase-iso-arrays} with a common initial risk
$F_0=\fRisk^{\text{s-SVD}}(0)=\fRisk^{\text{s-SGD}}(0)$. Choose
$\lr^\star_{\text{s-SVD}}$ and $\lr^\star_{\text{s-SGD}}$ by
\cref{eqn:eta-star-tte}, so that both models have floor $\epsilon$, and fix
$T>1$ with $F_0>T\epsilon$.
\begin{enumerate}[label=(\roman*)]
\item For every such $\epsilon$,
$t^{\text{s-SGD}}_{T\epsilon}/t^{\text{s-SVD}}_{T\epsilon}=\rho(\gamma)\,B/\mathcal N_B^2$.
As $\epsilon/F_0\to0$, uniformly in $N$, $B$ and $C(\gamma)$,
\[
t^{\text{s-SVD}}_{T\epsilon}\sim\frac m{4C(\gamma)^2}\sqrt{\frac{F_0}\epsilon},\qquad
t^{\text{s-SGD}}_{T\epsilon}\sim\frac{\pi N^2}{4\mathcal N_B^2}\sqrt{\frac{F_0}\epsilon} .
\]
\item If in addition $B\to\infty$, with $N$ and $\gamma$ allowed to vary, then
\[
t^{\text{s-SGD}}_{T\epsilon}\sim\frac{\pi N^2}{4B}\sqrt{\frac{F_0}\epsilon},\qquad
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\Big/\rho(\gamma)\longrightarrow1 ,
\]
and the ratio tends to $\rho(\gamma_0)$ if $\gamma\to\gamma_0\in(0,\infty)$.
\item For every $\gamma>0$,
\[
\rho(1)\le\rho(\gamma)<\frac{32}{9\pi},\qquad \rho(1)\le\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\le\frac{\pi^2}4\cdot\frac{32}{9\pi},
\]
with $\rho(\gamma)=\rho(1)$ only at $\gamma=1$; and $\rho(\gamma)\to\frac{32}{9\pi}$ as
$\gamma\downarrow0$ and $\rho(\gamma)\to1$ as $\gamma\to\infty$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_phase_iso (T : ℝ) (hT : 1 < T) :
    -- (i) the exact ratio
    (∀ (N B : ℕ) (NB ε : ℝ) (mS mN : RowModel (Fin N)), IsIsoSetting N B NB ε T mS mN →
      ∀ Qs Qn : Fin N → ℝ → ℝ, IsGlobalRowSolution mS Qs → IsGlobalRowSolution mN Qn →
        (firstHit (mN.risk Qn) (T * ε)).toReal / (firstHit (mS.risk Qs) (T * ε)).toReal
          = isoRho ((N : ℝ) / B) * (B : ℝ) / NB ^ 2) ∧
    -- (i) asymptotics, uniform in N, B, C(γ)
    (∀ δ : ℝ, 0 < δ → ∃ θ : ℝ, 0 < θ ∧
      ∀ (N B : ℕ) (NB ε : ℝ) (mS mN : RowModel (Fin N)), IsIsoSetting N B NB ε T mS mN →
        ε / mS.F0 < θ →
        ∀ Qs Qn : Fin N → ℝ → ℝ, IsGlobalRowSolution mS Qs → IsGlobalRowSolution mN Qn →
          |(firstHit (mS.risk Qs) (T * ε)).toReal
              / (min (B : ℝ) (N : ℝ) / (4 * isoDriftConst ((N : ℝ) / B) ^ 2)
                  * Real.sqrt (mS.F0 / ε)) - 1| ≤ δ ∧
          |(firstHit (mN.risk Qn) (T * ε)).toReal
              / ((N : ℝ) ^ 2 * Real.pi / (4 * NB ^ 2) * Real.sqrt (mS.F0 / ε)) - 1| ≤ δ) ∧
    -- (ii) B → ∞ with ε/F₀ → 0 jointly, for the s-SGD time
    (∀ δ : ℝ, 0 < δ → ∃ B₀ : ℕ, ∃ θ : ℝ, 0 < θ ∧
      ∀ (N B : ℕ) (NB ε : ℝ) (mS mN : RowModel (Fin N)), IsIsoSetting N B NB ε T mS mN →
        B₀ ≤ B → ε / mS.F0 < θ →
        ∀ Qn : Fin N → ℝ → ℝ, IsGlobalRowSolution mN Qn →
          |(firstHit (mN.risk Qn) (T * ε)).toReal
              / ((N : ℝ) ^ 2 * Real.pi / (4 * B) * Real.sqrt (mS.F0 / ε)) - 1| ≤ δ) ∧
    -- (ii) B → ∞ alone, for the ratio divided by ρ(γ)
    (∀ δ : ℝ, 0 < δ → ∃ B₀ : ℕ,
      ∀ (N B : ℕ) (NB ε : ℝ) (mS mN : RowModel (Fin N)), IsIsoSetting N B NB ε T mS mN →
        B₀ ≤ B →
        ∀ Qs Qn : Fin N → ℝ → ℝ, IsGlobalRowSolution mS Qs → IsGlobalRowSolution mN Qn →
          |((firstHit (mN.risk Qn) (T * ε)).toReal / (firstHit (mS.risk Qs) (T * ε)).toReal)
              / isoRho ((N : ℝ) / B) - 1| ≤ δ) ∧
    -- (ii) the limit γ → γ₀
    (∀ γ₀ : ℝ, 0 < γ₀ → ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∃ B₀ : ℕ,
      ∀ (N B : ℕ) (NB ε : ℝ) (mS mN : RowModel (Fin N)), IsIsoSetting N B NB ε T mS mN →
        B₀ ≤ B → |(N : ℝ) / B - γ₀| < η →
        ∀ Qs Qn : Fin N → ℝ → ℝ, IsGlobalRowSolution mS Qs → IsGlobalRowSolution mN Qn →
          |(firstHit (mN.risk Qn) (T * ε)).toReal / (firstHit (mS.risk Qs) (T * ε)).toReal
              - isoRho γ₀| ≤ δ) ∧
    -- (iii) bounds on ρ and on the ratio
    (∀ γ : ℝ, 0 < γ → isoRho 1 ≤ isoRho γ ∧ isoRho γ < 32 / (9 * Real.pi)) ∧
    (∀ γ : ℝ, 0 < γ → isoRho γ = isoRho 1 → γ = 1) ∧
    (∀ (N B : ℕ) (NB ε : ℝ) (mS mN : RowModel (Fin N)), IsIsoSetting N B NB ε T mS mN →
      ∀ Qs Qn : Fin N → ℝ → ℝ, IsGlobalRowSolution mS Qs → IsGlobalRowSolution mN Qn →
        isoRho 1 ≤ (firstHit (mN.risk Qn) (T * ε)).toReal / (firstHit (mS.risk Qs) (T * ε)).toReal ∧
        (firstHit (mN.risk Qn) (T * ε)).toReal / (firstHit (mS.risk Qs) (T * ε)).toReal
          ≤ Real.pi ^ 2 / 4 * (32 / (9 * Real.pi))) ∧
    Tendsto isoRho (𝓝[>] 0) (𝓝 (32 / (9 * Real.pi))) ∧
    Tendsto isoRho atTop (𝓝 1) := by
  obtain ⟨-, -, -, hmin, -, huniq, hlub, hne, htz, htt, -, -, -⟩ := thm_app_phase_iso_extrema
  refine ⟨?_, fun δ hδ => ?_, p4_ii_a T hT, p4_ii_b T, p4_ii_c T, ?_, huniq, ?_, htz, htt⟩
  · intro N B NB ε mS mN h Qs Qn hQs hQn
    obtain ⟨-, -, hratio, -, -, -, -, -⟩ := prop_app_phase_iso_ratio N B NB ε T mS mN h
    exact (hratio Qs Qn hQs hQn).2.2
  · obtain ⟨θ, hθ, hpair⟩ := p4_asymp_pair T hT δ hδ
    exact ⟨θ, hθ, fun N B NB ε mS mN h hθε Qs Qn hQs hQn =>
      ⟨(hpair N B NB ε mS mN h hθε).1 Qs hQs, (hpair N B NB ε mS mN h hθε).2 Qn hQn⟩⟩
  · intro γ hγ
    exact ⟨hmin γ hγ, lt_of_le_of_ne (hlub.1 (Set.mem_image_of_mem isoRho (Set.mem_Ioi.2 hγ)))
      (hne γ hγ)⟩
  · intro N B NB ε mS mN h Qs Qn hQs hQn
    obtain ⟨-, -, hratio, -, -, hr1, hr2, -⟩ := prop_app_phase_iso_ratio N B NB ε T mS mN h
    obtain ⟨hNp, hBp, -, -, -⟩ := p4_pos h
    have hγ : (0 : ℝ) < (N : ℝ) / B := div_pos hNp hBp
    rw [(hratio Qs Qn hQs hQn).2.2, mul_div_assoc]
    have hρ0 : 0 ≤ isoRho ((N : ℝ) / B) := (p4_rho_pos hγ).le
    have hsup := hlub.1 (Set.mem_image_of_mem isoRho (Set.mem_Ioi.2 hγ))
    have hr0 : (0 : ℝ) ≤ (B : ℝ) / NB ^ 2 := by linarith
    constructor
    · calc isoRho 1 ≤ isoRho ((N : ℝ) / B) := hmin _ hγ
        _ ≤ isoRho ((N : ℝ) / B) * ((B : ℝ) / NB ^ 2) := le_mul_of_one_le_right hρ0 hr1
    · calc isoRho ((N : ℝ) / B) * ((B : ℝ) / NB ^ 2)
          ≤ (32 / (9 * Real.pi)) * (Real.pi ^ 2 / 4) := mul_le_mul hsup hr2 hr0 (by positivity)
        _ = Real.pi ^ 2 / 4 * (32 / (9 * Real.pi)) := mul_comm _ _

end Muon.Phase

end

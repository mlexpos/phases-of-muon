import Muon.Dynamics.Transport
import Muon.Dynamics.FiniteMean
import Muon.Foundations.Freezing
import Muon.External.Certificates

/-!
# Appendix E, coordinator bridge: freezing at random stopped states

Snapshot `cr-2026-10-23`. No source label: every declaration of this module is an internal proof-step
lemma (coordinator bridge) that the source uses silently through the conventions of
`sections/05-dynamics/section.tex` ll. 126–132 ("Conditional expectations given `𝓕_t` are computed by
integrating the batches of the steps `t, t+1, …` with the past held fixed, since these batches are
independent of the past") and `lem:app-dyn-chains`(iv) (ll. 511–512, proof ll. 533–534).
Interface draft: every proof is `sorry`.

Consumers (blocked proof cards):
* `lem_app_dyn_diffuse` (`Muon.Dynamics.Diffuse`, P-E.11.P2): the drift display of its proof (ll. 2076–2091)
  at the random block starts `t = t_b ≤ TB`, uniformly in `t`, is `cond_block_drift`.
* `lem_app_dyn_martingale` (`Muon.Dynamics.Concentration`, P-E.10.P2): the conditional projection variance
  (ll. 1813–1815, "By `lem:app-dyn-poincare`, conditionally on `𝓕_t` with `T = 𝒲D`") is `cond_poincare_block`.
* `thm_app_dyn_main_iv` (`Muon.Dynamics.Main`, P-E.13.P2): the transfer of `lem_app_dyn_diffuse` from the
  sample-level `DynSetup` to the law-level `DynHyp` is `DynHyp.exists_dynSetup_pathLaw`.

Layering (the bridge statements are proved from one another and from frozen statements):
* `stationary_freezing_condExp` (freezing of the stationary chain at a past-measurable state): from
  `Muon.Foundations.freezing_condExp` with `X = D`, `Y` = the future samples (`chainFuture`).
* `mean_physical_uniform` (the third bound of `eqn:app-dyn-mean-physical`, uniform in the state, the time and
  the lag): from `lem_app_dyn_chains_i` (law of the stationary chain = frozen model at `Â(D)`, all lags) and
  `lem_app_dyn_mean_iv_ema` (uniform in the normalized state and the time), as in the source's derivation
  ll. 787–797; or from `eqn_app_dyn_mean_physical` by the contradiction argument of `lem:app-dyn-uniform`.
* `opNorm_condExpMat_le` (conditional Jensen for the operator norm): pure measure theory.
* `cond_block_drift`: from the three above and `lem_app_dyn_coupling_iv`.
* `cond_poincare_block`: from `stationary_freezing_condExp` and `lem_app_dyn_poincare_ii`.
* `DynHyp.exists_dynSetup_pathLaw`: from `DynHyp.exists_dynSetup` (Transport) and measurability of `devRand`.

Representation choices:
* Freezing. The stationary chain at `(t, D)` uses only the batches of the steps `≥ t` and the auxiliary batches
  of comparison `t` (`chainFuture cs t`). A functional `Φ(D, (V_r)_r)` of the state and of the stationary update
  path is jointly measurable and `Φ(D, V(D))` integrable; consumers take `Φ = 𝟙_𝒦(D) · ψ` with
  `𝒦 ⊆ {𝓡 ≥ r₋ > 0}`, so only states where `def:app-dyn-chains` is in force (`𝓡(D) > 0`) contribute.
* Conditional expectations of matrices are entrywise (`Muon.Foundations.condExpMat`); `‖·‖` is `opNorm`, `‖·‖_F`
  is `fro`, `Σ_out^{1/2} = rOut`, `Σ_in^{1/2} = rIn`.
* Constants. `∃ B₀ K` come after the fixed parameters and the compact set `𝒦 = 𝒦(r₋, r₊, E)` and before the
  dimensions, the sample spaces and the states; the vanishing sequence `r` comes after the sequence of models
  (as in `lem_app_dyn_mean_iv_ema`) and before the times, lags and states.
* The path law transfer is stated for measurable sets of paths `ℕ → Mat` (product σ-algebra); the `DynHyp`
  error path is written out as `devRand … (initState W₀ M°₋₁) x`, which is `errPath hyp k` of
  `Muon.Dynamics.Corollaries` by definition (this module does not import `Corollaries`).
-/

set_option linter.style.longLine false

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open Muon Muon.Setup Muon.Volatility

universe u

noncomputable section

namespace Muon.Dynamics

/-! ## Freezing of the stationary chain at a past-measurable state -/

private lemma freezing_risk_nonneg {m n : ℕ} (C : Covariances m n) (D : Mat m n) :
    0 ≤ riskSigma C D := by
  rw [eqn_app_setup_whitened_risk]
  positivity

private lemma freezing_chainFuture_le {m n B : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} (cs : ChainSamples P m n B) (t : ℕ) : chainFuture cs t ≤ mΩ := by
  refine sup_le (iSup_le fun s => iSup_le fun _ => iSup_le fun a => ?_)
    (iSup_le fun j => iSup_le fun a => ?_)
  · exact (cs.meas_act s a).comap_le
  · exact (cs.meas_aux (t : ℤ) j a).comap_le

private abbrev FreezingFuture (m n B : ℕ) :=
  (ℕ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)

private def freezingFuture {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (cs : ChainSamples P m n B) (t : ℕ) (ω : Ω) :
    FreezingFuture m n B :=
  (fun k a => cs.act ((t : ℤ) + k + 1) a ω, fun j a => cs.aux (t : ℤ) j a ω)

private def freezingEma {m n B : ℕ} (p : DynParams) (C : Covariances m n)
    (D : Mat m n) (y : FreezingFuture m n B) : ℕ → Mat m n
  | 0 => ∑' j : ℕ, emaW p.β j • batchGrad D (fun a => phys C (y.2 j a))
  | k + 1 => p.β • freezingEma (B := B) p C D y k +
      (1 - p.β) • batchGrad D (fun a => phys C (y.1 k a))

private def freezingV {m n B : ℕ} (p : DynParams) (C : Covariances m n)
    (D : Mat m n) (y : FreezingFuture m n B) (r : ℕ) : Mat m n :=
  Q (physRidge p C D) (freezingEma (B := B) p C D y (r + 1))

private lemma freezingV_eq {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B)
    (t : ℕ) (D : Mat m n) (r : ℕ) (ω : Ω) :
    freezingV p C D (freezingFuture cs t ω) r = stationaryV p C cs t D r ω := by
  have hema : ∀ k, freezingEma p C D (freezingFuture cs t ω) k =
      emaChain p.β D (fun s => physBatch C (cs.act s) ω) t
        (chainInit p.β C D (cs.aux (t : ℤ)) ω) k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [freezingEma, emaChain]
      rw [ih]
      rfl
  simp only [freezingV, stationaryV, def_app_dyn_chains]
  rw [hema]

private lemma freezingV_joint_meas {m n B : ℕ} (p : DynParams) (C : Covariances m n)
    (r : ℕ) : Measurable (fun z : Mat m n × FreezingFuture m n B =>
      freezingV (B := B) p C z.1 z.2 r) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) :=
    inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hinit : Measurable (fun z : Mat m n × FreezingFuture m n B =>
      ∑' j : ℕ, emaW p.β j • batchGrad z.1 (fun a => phys C (z.2.2 j a))) := by
    refine Measurable.tsum fun j => Measurable.const_smul ?_ (emaW p.β j)
    unfold batchGrad grad resid phys outer
    fun_prop
  have hema : ∀ k, Measurable (fun z : Mat m n × FreezingFuture m n B =>
      freezingEma (B := B) p C z.1 z.2 k) := by
    intro k
    induction k with
    | zero => simpa only [freezingEma] using hinit
    | succ k ih =>
      have hb : Measurable (fun z : Mat m n × FreezingFuture m n B =>
          batchGrad z.1 (fun a => phys C (z.2.1 k a))) := by
        unfold batchGrad grad resid phys outer
        fun_prop
      exact (ih.const_smul p.β).add (hb.const_smul (1 - p.β))
  have hρ : ∀ z : Mat m n × FreezingFuture m n B, 0 ≤ physRidge p C z.1 := fun z => by
    exact mul_nonneg (mul_nonneg (by norm_num) (freezing_risk_nonneg C z.1)) p.hϱ.le
  have hρm : Measurable (fun z : Mat m n × FreezingFuture m n B =>
      (⟨physRidge p C z.1, hρ z⟩ : Set.Ici (0 : ℝ))) := by
    have hrisk : Continuous (fun D : Mat m n => riskSigma C D) := by
      unfold riskSigma pairSigma
      fun_prop
    exact (((hrisk.measurable.comp measurable_fst).const_mul 2).mul_const p.ϱ).subtype_mk
  exact measurable_Q.comp (hρm.prodMk (hema (r + 1)))

/-- Coordinator bridge (no source label), snapshot `cr-2026-10-23`. Freezing of the stationary chain at a
random state. Let `𝓕` be a σ-algebra independent of the future samples `chainFuture cs t` (the batches of the
steps `≥ t` and the auxiliary batches of comparison `t`), and let `D` be `𝓕`-measurable. For every jointly
measurable functional `Φ(D, (V_r)_{r ≥ 0})` of the state and of the stationary update path with `Φ(D, V(D))`
integrable, the conditional expectation given `𝓕` is the expectation
with `D` frozen at its `𝓕`-value.
Source: `section.tex` ll. 126–132 (conventions), verbatim:
```latex
The past $\cF_t$ is that of \cref{def:app-setup-model}, and
$\EE_t=\EE[\,\cdot\mid\cF_t]$. Conditional expectations given $\cF_t$ are
computed by integrating the batches of the steps $t,t+1,\dots$ with the past
held fixed, since these batches are independent of the past. Comparisons
with the frozen-state model use auxiliary batches, independent of
everything else and drawn anew for each comparison; $\EE_t$ integrates
them as well.
```
and `lem:app-dyn-chains`(iv) (ll. 511–512, proof ll. 533–534): "At a step $t<t_{\rm stop}$, the statements
(i)--(iii) hold conditionally on $\cF_t$ with $D=\Dt$ and $m=M^\circ_{t-1}$." / "Part (iv) holds because the
batches of the steps $t,t+1,\dots$ and the auxiliary batches are independent of the past."
`lem_app_dyn_chains_iv` states this for bounded `Φ` of the normalized path alone; the consumers need `Φ`
depending on `D` as well (the test `T = 𝒲D` of ll. 1813–1815, the indicator `𝟙_𝒦(D)`), and integrable `Φ`.
Proof route: `Muon.Foundations.freezing_condExp` with `X = D`, `Y` the family of future samples, and
`f(D, y) = Φ(D, V(D, y))`, jointly measurable (`measurable_Q` of `Muon.Setup.RegularizedMap`, jointly in `(ℓ, K)` on `ℓ ≥ 0`, the physical ridge
`2𝓡(D)ϱ ≥ 0` is continuous in `D`, `chainInit` is a measurable series in `(D, y)`). No positivity of `𝓡(D)` is
needed for the identity; consumers insert `𝟙_𝒦(D)` themselves. -/
theorem stationary_freezing_condExp {m n B : ℕ} {Ω : Type*} (𝓕 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (p : DynParams) (C : Covariances m n)
    (cs : ChainSamples P m n B) (t : ℕ)
    (h𝓕 : 𝓕 ≤ mΩ) (hind : Indep 𝓕 (chainFuture cs t) P)
    (D : Ω → Mat m n) (hD : Measurable[𝓕] D)
    (Φ : Mat m n → (ℕ → Mat m n) → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    (hint : Integrable (fun ω => Φ (D ω) (fun r => stationaryV p C cs t (D ω) r ω)) P) :
    condExp 𝓕 P (fun ω => Φ (D ω) (fun r => stationaryV p C cs t (D ω) r ω)) =ᵐ[P]
      fun ω => ∫ ω', Φ (D ω) (fun r => stationaryV p C cs t (D ω) r ω') ∂P := by
  let Y : Ω → FreezingFuture m n B := freezingFuture cs t
  have hY : Measurable Y := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro k
      apply Measurable.of_eval
      intro a
      exact cs.meas_act ((t : ℤ) + k + 1) a
    · apply Measurable.of_eval
      intro j
      apply Measurable.of_eval
      intro a
      exact cs.meas_aux (t : ℤ) j a
  have hYcomap : MeasurableSpace.comap Y inferInstance ≤ chainFuture cs t := by
    rw [show Y = freezingFuture cs t by rfl]
    unfold freezingFuture
    change (MeasurableSpace.prod
      (inferInstance : MeasurableSpace (ℕ → Fin B → Vec m × Vec n))
      (inferInstance : MeasurableSpace (ℕ → Fin B → Vec m × Vec n))).comap
        (fun ω => ((fun (k : ℕ) a => cs.act ((t : ℤ) + (k : ℤ) + 1) a ω),
          fun j a => cs.aux (t : ℤ) j a ω)) ≤ chainFuture cs t
    rw [MeasurableSpace.comap_prodMk]
    simp_rw [MeasurableSpace.comap_process_pi]
    refine sup_le (iSup_le fun k => iSup_le fun a => ?_)
      (iSup_le fun j => iSup_le fun a => ?_)
    · apply le_sup_of_le_left
      refine le_iSup_of_le ((t : ℤ) + k + 1) (le_iSup_of_le (by omega) ?_)
      exact le_iSup_of_le a le_rfl
    · apply le_sup_of_le_right
      exact le_iSup_of_le j (le_iSup_of_le a le_rfl)
  have hindY : Indep 𝓕 (MeasurableSpace.comap Y inferInstance) P :=
    indep_of_indep_of_le_right hind hYcomap
  let f : Mat m n → FreezingFuture m n B → ℝ :=
    fun D y => Φ D (fun r => freezingV p C D y r)
  have hf : Measurable (Function.uncurry f) := by
    change Measurable (Function.uncurry Φ ∘
      fun z : Mat m n × FreezingFuture m n B =>
        (z.1, fun r => freezingV p C z.1 z.2 r))
    have hg : Measurable (fun z : Mat m n × FreezingFuture m n B =>
        (z.1, fun r => freezingV p C z.1 z.2 r)) :=
      measurable_fst.prodMk (Measurable.of_eval fun r => freezingV_joint_meas p C r)
    exact hΦ.comp hg
  have hint' : Integrable (fun ω => f (D ω) (Y ω)) P := by
    apply hint.congr
    filter_upwards with ω
    apply congrArg (Φ (D ω))
    funext r
    exact (freezingV_eq p C cs t (D ω) r ω).symm
  have hfreeze := Muon.Foundations.freezing_condExp 𝓕 h𝓕 hD hY hindY hf hint'
  have hleft : (fun ω => f (D ω) (Y ω)) =
      (fun ω => Φ (D ω) (fun r => stationaryV p C cs t (D ω) r ω)) := by
    funext ω
    apply congrArg (Φ (D ω))
    funext r
    exact freezingV_eq p C cs t (D ω) r ω
  rw [hleft] at hfreeze
  filter_upwards [hfreeze] with ω hω
  rw [hω]
  have hfm : Measurable (f (D ω)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [integral_map hY.aemeasurable hfm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with ω'
  apply congrArg (Φ (D ω))
  funext r
  exact freezingV_eq p C cs t (D ω) r ω'

private theorem freezing_Ahat_norm {m n : ℕ} (C : Covariances m n) (D : Mat m n)
    (hD : 0 < riskSigma C D) : fro (Ahat C D) = 1 := by
  have hsq : ∀ (c : ℝ) (K : Mat m n), fro (c • K) ^ 2 = c ^ 2 * fro K ^ 2 := by
    intro c K
    have hf : ∀ L : Mat m n, fro L ^ 2 = ∑ i, ∑ j, L i j ^ 2 := by
      intro L
      unfold fro
      rw [Real.sq_sqrt (by positivity)]
      simp only [Real.norm_eq_abs, sq_abs]
    simp only [hf, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  have hr := eqn_app_setup_whitened_risk C D
  have hs : fro (Ahat C D) ^ 2 = 1 := by
    rw [Ahat, hsq, inv_pow, Real.sq_sqrt (by linarith)]
    rw [show fro (Arot C D) ^ 2 = 2 * riskSigma C D by linarith,
      inv_mul_cancel₀ (by linarith)]
  have hn : 0 ≤ fro (Ahat C D) := Real.sqrt_nonneg _
  nlinarith

private theorem freezing_stat_aesm {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B)
    (t : ℕ) (D : Mat m n)
    (hs : ∀ᵐ ω ∂P, Summable (fun j : ℕ =>
      emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))) (k : ℕ) :
    AEStronglyMeasurable (fun ω => (def_app_dyn_chains p C cs t D 0 ω).stat k) P := by
  have hcG : Continuous (fun b : Fin B → Vec m × Vec n =>
      batchGrad D (fun a => phys C (b a))) := by
    unfold batchGrad grad resid phys outer
    fun_prop
  have hb : ∀ s : ℤ, Measurable (fun ω => batchGrad D (physBatch C (cs.act s) ω)) := by
    intro s
    exact hcG.measurable.comp (measurable_pi_iff.mpr fun a => cs.meas_act s a)
  induction k with
  | zero =>
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
      ∑ j ∈ Finset.range N, emaW p.β j • batchGrad D
        (physBatch C (cs.aux (t : ℤ) j) ω)) (fun N => ?_) ?_
    · exact (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ =>
        (hcG.measurable.comp (measurable_pi_iff.mpr fun a =>
          cs.meas_aux (t : ℤ) j a)).stronglyMeasurable.const_smul (emaW p.β j)).aestronglyMeasurable
    · filter_upwards [hs] with ω hω
      exact hω.hasSum.tendsto_sum_nat
  | succ k ih =>
    exact (ih.const_smul p.β).add
      ((hb ((t : ℤ) + k + 1)).stronglyMeasurable.aestronglyMeasurable.const_smul (1 - p.β))

private theorem freezing_statV_aem {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B)
    (t : ℕ) (D : Mat m n)
    (hs : ∀ᵐ ω ∂P, Summable (fun j : ℕ =>
      emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))) (k : ℕ) :
    AEMeasurable (fun ω => (def_app_dyn_chains p C cs t D 0 ω).statV k) P := by
  have hρ : 0 ≤ physRidge p C D := by
    unfold physRidge
    exact mul_nonneg (mul_nonneg (by norm_num) (freezing_risk_nonneg C D)) p.hϱ.le
  have hst := (freezing_stat_aesm p C cs t D hs k).aemeasurable
  have hρm : Measurable (fun _ : Ω => (⟨physRidge p C D, hρ⟩ : Set.Ici (0 : ℝ))) :=
    measurable_const
  exact (measurable_Q (m := m) (n := n)).comp_aemeasurable
    (hρm.aemeasurable.prodMk hst)

open scoped Matrix.Norms.Frobenius in
private theorem freezing_summable_of_fro {m n : ℕ} (f : ℕ → Mat m n)
    (hf : Summable (fun j => fro (f j))) : Summable f := by
  apply Summable.of_norm
  simpa only [fro_eq_norm] using hf

private theorem freezing_batch_sm {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    StronglyMeasurable (frozenBatchG F S s) := by
  have hc : Continuous (fun q : Vec m × Vec n =>
      (dotProduct q.1 (Matrix.mulVec F.A q.2)) •
        (rOut F.C * outer q.1 q.2 * rIn F.C)) := by fun_prop
  unfold frozenBatchG
  refine StronglyMeasurable.const_smul ?_ ((B : ℝ))⁻¹
  exact Finset.stronglyMeasurable_fun_sum Finset.univ fun a _ =>
    hc.comp_stronglyMeasurable (S.meas s a).stronglyMeasurable

private theorem freezing_buf_aesm {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) : AEStronglyMeasurable (frozenBuf F S t) P := by
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
    ∑ j ∈ Finset.range N, emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω)
    (fun N => ?_) ?_
  · exact (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ =>
      (freezing_batch_sm F S _).const_smul (emaW F.β j)).aestronglyMeasurable
  · filter_upwards [(lem_app_setup_ema_law_i F S).1] with ω hω
    exact (freezing_summable_of_fro _ (hω t)).hasSum.tendsto_sum_nat

private theorem freezing_upd_aem {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (t : ℤ) :
    AEMeasurable (frozenUpd F S ϱ t) P := by
  have hρm : Measurable (fun _ : Ω => (⟨ϱ, hϱ⟩ : Set.Ici (0 : ℝ))) := measurable_const
  exact (measurable_Q (m := m) (n := n)).comp_aemeasurable
    (hρm.aemeasurable.prodMk (freezing_buf_aesm F S t).aemeasurable)

private lemma freezing_abs_entry_le_fro {m n : ℕ} (A : Mat m n) (i : Fin m) (j : Fin n) :
    |A i j| ≤ fro A := by
  unfold fro
  apply Real.abs_le_sqrt
  have h1 : ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
  have h2 : ∑ j', ‖A i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  simpa [Real.norm_eq_abs, sq_abs] using h1.trans h2

private theorem freezing_upd_integrable {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (t : ℤ) (i : Fin m) (j : Fin n) :
    Integrable (fun ω => frozenUpd F S ϱ t ω i j) P := by
  refine Integrable.of_bound (C := Real.sqrt (min m n : ℕ))
    (((freezing_upd_aem F S ϱ hϱ t).eval i).eval j |>.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]
    refine (freezing_abs_entry_le_fro _ i j).trans (Real.le_sqrt_of_sq_le ?_)
    obtain ⟨-, hsq, hrank, -⟩ := lem_app_setup_filter_i ϱ hϱ (frozenBuf F S t ω)
    exact hsq.trans (by exact_mod_cast hrank)

private theorem freezing_stationary_frozen {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (p : DynParams) (C : Covariances m n)
    (cs : ChainSamples P m n B) (t j : ℕ) (D : Mat m n) (hD : 0 < riskSigma C D)
    (F : FrozenParams m n B) (hFC : F.C = C) (hFA : F.A = Ahat C D)
    (hFβ : F.β = p.β) (S : FrozenSamples P m n B) :
    (∀ i i', Integrable (fun ω => stationaryV p C cs t D j ω i i') P) ∧
      mean P (fun ω => stationaryV p C cs t D j ω) =
        mean P (fun ω => frozenUpd F S p.ϱ ((t : ℤ) + (j : ℤ)) ω) := by
  have hlaw := lem_app_dyn_chains_i p C cs t D 0 hD F hFC hFA hFβ S
  have hleft : AEMeasurable
      (fun ω (k : ℕ) => (def_app_dyn_chains p C cs t D 0 ω).statV k) P :=
    AEMeasurable.of_eval fun k => freezing_statV_aem p C cs t D hlaw.1 k
  have hright : AEMeasurable
      (fun ω (k : ℕ) => frozenUpd F S p.ϱ ((t : ℤ) + (k : ℤ) - 1) ω) P :=
    AEMeasurable.of_eval fun k => freezing_upd_aem F S p.ϱ p.hϱ.le _
  have hidPath : IdentDistrib
      (fun ω (k : ℕ) => (def_app_dyn_chains p C cs t D 0 ω).statV k)
      (fun ω (k : ℕ) => frozenUpd F S p.ϱ ((t : ℤ) + (k : ℤ) - 1) ω) P P :=
    ⟨hleft, hright, hlaw.2.2.1⟩
  have hid : IdentDistrib (stationaryV p C cs t D j)
      (fun ω => frozenUpd F S p.ϱ ((t : ℤ) + (j : ℤ)) ω) P P := by
    change IdentDistrib
      (fun ω => (def_app_dyn_chains p C cs t D 0 ω).statV (j + 1)) _ P P
    convert hidPath.comp (measurable_pi_apply (j + 1)) using 1
    · rfl
    · apply congrArg (fun s : ℤ => fun ω => frozenUpd F S p.ϱ s ω)
      push_cast
      ring
  have hintR : ∀ i i', Integrable
      (fun ω => frozenUpd F S p.ϱ ((t : ℤ) + (j : ℤ)) ω i i') P :=
    fun i i' => freezing_upd_integrable F S p.ϱ p.hϱ.le _ i i'
  constructor
  · intro i i'
    exact ((hid.comp ((measurable_pi_apply i').comp (measurable_pi_apply i))).integrable_iff).2
      (hintR i i')
  · ext i i'
    exact (hid.comp ((measurable_pi_apply i').comp (measurable_pi_apply i))).integral_eq

private lemma freezingUnit_fro {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    fro (fun i j => if i = ⟨0, hm⟩ ∧ j = ⟨0, hn⟩ then 1 else 0 : Mat m n) = 1 := by
  unfold fro
  have hs : (∑ i : Fin m, ∑ j : Fin n,
      ‖if i = ⟨0, hm⟩ ∧ j = ⟨0, hn⟩ then (1 : ℝ) else 0‖ ^ 2) = 1 := by
    rw [Finset.sum_eq_single ⟨0, hm⟩]
    · rw [Finset.sum_eq_single ⟨0, hn⟩]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    · intro a _ ha
      simp [ha]
    · simp
  rw [hs]
  norm_num

open scoped Matrix.Norms.L2Operator in
private theorem freezing_opNorm_mean_le {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : Ω → Mat m n)
    (hae : AEStronglyMeasurable X P) (c : ℝ) (hX : ∀ ω, opNorm (X ω) ≤ c) :
    opNorm (mean P X) ≤ c := by
  have hint : Integrable X P := by
    refine Integrable.of_bound hae c ?_
    filter_upwards with ω
    rw [← opNorm_eq_norm]
    exact hX ω
  have heq : mean P X = ∫ ω, X ω ∂P := by
    ext i j
    let L1 : Mat m n →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.proj i
    let L2 : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
    have h1 := L1.integral_comp_comm hint
    have h2 := L2.integral_comp_comm (L1.integrable_comp hint)
    dsimp [L1, L2] at h1 h2
    change (∫ ω, X ω i j ∂P) = (∫ ω, X ω ∂P) i j
    exact h2.trans (congrArg (fun z => z j) h1)
  rw [heq, opNorm_eq_norm]
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := P) (f := X) (C := c)
      (ae_of_all _ fun ω => by rw [← opNorm_eq_norm]; exact hX ω)

private lemma freezing_opNorm_mul {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  open scoped Matrix.Norms.L2Operator in
    simpa only [opNorm_eq_norm] using Matrix.l2_opNorm_mul A B

private lemma freezing_opNorm_smul {a b : ℕ} (c : ℝ) (A : Mat a b) :
    opNorm (c • A) = |c| * opNorm A := by
  open scoped Matrix.Norms.L2Operator in
    rw [opNorm_eq_norm, opNorm_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma freezing_opNorm_rOut_sq {m n : ℕ} (C : Covariances m n) :
    opNorm (rOut C) * opNorm (rOut C) = opNorm C.Sout := by
  have hh : (rOut C)ᴴ = rOut C :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sout)).isHermitian
  have hsq : rOut C * rOut C = C.Sout :=
    CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (rOut C)
  rw [hh, hsq] at h
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact h.symm

private lemma freezing_opNorm_rIn_sq {m n : ℕ} (C : Covariances m n) :
    opNorm (rIn C) * opNorm (rIn C) = opNorm C.Sin := by
  have hh : (rIn C)ᴴ = rIn C :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  have hsq : rIn C * rIn C = C.Sin :=
    CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (rIn C)
  rw [hh, hsq] at h
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact h.symm

private lemma freezing_opNorm_nonneg {a b : ℕ} (A : Mat a b) : 0 ≤ opNorm A := by
  unfold opNorm
  exact norm_nonneg _

/-! ## The physical mean bound, uniform in the state, the time and the lag -/

/-- Coordinator bridge (no source label), snapshot `cr-2026-10-23`. The third bound of
`eqn:app-dyn-mean-physical`, `‖Σ_out^{1/2} V̄(D) Σ_in^{1/2}‖ ≤ C‖Σ_out^{1/2} D Σ_in^{1/2}‖ + C r_B`, with the
vanishing sequence `r_B` chosen before the state `D`, the comparison time `t` and the lag `j` (the mean of
`V_j` at `(t, D)`), as the source requires: `lem:app-dyn-mean`(iv) gives `r_B` "depending only on
$(\ridge,\gamma_\star,C_\Sigma)$ and on the sequence of dimensions" and the bound "for every normalized state"
(ll. 780–783), and `lem:app-dyn-chains`(i) (ll. 498–506) makes `(V_r)_{r≥0}` stationary with
`\overline V(D) = \EE\,\Qridge\ridge(\Mt)` at `Â(D)`. The frozen `eqn_app_dyn_mean_physical` fixes `t` and the
deterministic sequence `D_k` before its `r`; the persistence of diffuseness applies the bound at the random
block starts `D = Δ_{t_b}`, `t_b ≤ TB` (ll. 2076–2080), which needs this uniform form.
Source, `section.tex` ll. 780–797, verbatim (excerpt):
```latex
\item for the fixed ridge $\ridge$ there are $C$ and a sequence $r_B\to0$,
depending only on $(\ridge,\gamma_\star,C_\Sigma)$ and on the sequence of
dimensions, such that $\norm{\EE\,\Qridge\ridge(\Mt)}\le C\norm{\Ahat}+r_B$ for
every normalized state.
\end{enumerate}
The constants depend only on $(\gamma_\star,C_\Sigma)$ and on $I$ where
indicated, not on $\Ahat$, on the dimension or on the weights within the
class \cref{eqn:app-de-weightclass}. Consequently, for the stationary chain
of \cref{def:app-dyn-chains} at a deterministic $D$ with
$r_-\le\cR(D)\le r_+$,
\begin{equation}\label{eqn:app-dyn-mean-physical}
\begin{gathered}
\norm{\overline V(D)}_\F\le C,\qquad
\big\|\EE\,\partial_\ell\Qridge\ell(N_0)\big|_{\ell=\ridgephys(D)}\big\|_\F\le C,\\
\norm{\Sigmaout^{1/2}\overline V(D)\Sigmain^{1/2}}\le C\norm{\Sigmaout^{1/2}D\Sigmain^{1/2}}+Cr_B ,
\end{gathered}
\end{equation}
with $C$ depending also on $(r_-,r_+)$.
```
Encoding: as `eqn_app_dyn_mean_physical` (the constant `K` is chosen before `p`, linked by field equalities),
except that `r` is chosen after the model sequence and before `k, t, j, D`. The mean is that of
`stationaryV p C cs t D j = V_j` at `(t, D)`. Proof route: `lem_app_dyn_chains_i` (law of the path
`(statV k)_k` = law of `frozenUpd F S ϱ (t + k − 1)` at `F.A = Â(D)`, so `mean V_j = mean Q_ϱ(M_{t+j})`),
`lem_app_dyn_mean_iv_ema` (uniform in `A` and `t : ℤ`), `‖Â(D)‖ = ‖Σ_out^{1/2}DΣ_in^{1/2}‖/√(2𝓡(D))` with
`𝓡(D) ≥ r₋`, and `‖Σ^{1/2}‖ ≤ √C_Σ`. -/
theorem mean_physical_uniform (γ CS ϱ rlo rhi : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ K : ℝ, ∀ (p : DynParams), p.γstar = γ → p.CSig = CS → p.ϱ = ϱ →
      ∀ (m n B : ℕ → ℕ) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
      (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
      (Cv : ∀ k, Covariances (m k) (n k)) (cs : ∀ k, ChainSamples (P k) (m k) (n k) (B k)),
      (∀ k, ((max (m k) (n k) : ℕ) : ℝ) ≤ γ * (B k : ℝ)) →
      (∀ k, opNorm (Cv k).Sout ≤ CS) → (∀ k, opNorm (Cv k).Sin ≤ CS) →
      ProportionalRegime m n B Cv →
      ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
        ∀ (k t j : ℕ) (D : Mat (m k) (n k)), rlo ≤ riskSigma (Cv k) D → riskSigma (Cv k) D ≤ rhi →
          (∀ (i : Fin (m k)) (i' : Fin (n k)),
            Integrable (fun ω => stationaryV p (Cv k) (cs k) t D j ω i i') (P k)) ∧
          opNorm (rOut (Cv k) * mean (P k) (fun ω => stationaryV p (Cv k) (cs k) t D j ω) * rIn (Cv k)) ≤
            K * opNorm (rOut (Cv k) * D * rIn (Cv k)) + K * r k := by
  by_cases hϱ : 0 < ϱ
  · obtain ⟨K0, hK0⟩ := lem_app_dyn_mean_iv_ema γ CS ϱ hϱ
    let K : ℝ := max (|CS| * |K0| / Real.sqrt (2 * rlo)) |CS|
    refine ⟨K, ?_⟩
    intro p hpγ hpCS hpϱ m n B Ω _ P _ Cv cs hdim hOut hIn hreg
    have heB : ∀ᶠ k in atTop, 0 < B k := hreg.B_top.eventually_gt_atTop 0
    have henR : ∀ᶠ k in atTop, hreg.γin / 2 < (n k : ℝ) / (B k : ℝ) :=
      (tendsto_order.1 hreg.ratio_in).1 _ (by linarith [hreg.γin_pos])
    have hemR : ∀ᶠ k in atTop, hreg.γout / 2 < (m k : ℝ) / (B k : ℝ) :=
      (tendsto_order.1 hreg.ratio_out).1 _ (by linarith [hreg.γout_pos])
    have hen : ∀ᶠ k in atTop, 0 < n k := by
      filter_upwards [henR] with k hk
      by_contra hn
      have hn0 : n k = 0 := by omega
      simp only [hn0, Nat.cast_zero, zero_div] at hk
      linarith [hreg.γin_pos]
    have hem : ∀ᶠ k in atTop, 0 < m k := by
      filter_upwards [hemR] with k hk
      by_contra hm
      have hm0 : m k = 0 := by omega
      simp only [hm0, Nat.cast_zero, zero_div] at hk
      linarith [hreg.γout_pos]
    obtain ⟨N, hN⟩ := (eventually_atTop.1 (heB.and (hem.and hen)))
    let F : ∀ q, FrozenParams (m (N + q)) (n (N + q)) (B (N + q)) := fun q =>
      { C := Cv (N + q)
        A := fun i j => if i = ⟨0, (hN (N + q) (Nat.le_add_right N q)).2.1⟩ ∧
          j = ⟨0, (hN (N + q) (Nat.le_add_right N q)).2.2⟩ then 1 else 0
        hA := freezingUnit_fro (hN (N + q) (Nat.le_add_right N q)).2.1
          (hN (N + q) (Nat.le_add_right N q)).2.2
        β := p.β
        hβ := p.hβ
        hB := (hN (N + q) (Nat.le_add_right N q)).1 }
    let S : ∀ q, FrozenSamples (P (N + q)) (m (N + q)) (n (N + q)) (B (N + q)) :=
      fun q =>
        { zw := (cs (N + q)).act
          meas := (cs (N + q)).meas_act
          indep := (cs (N + q)).indep.precomp Sum.inl_injective
          law := (cs (N + q)).law_act }
    have hφ : StrictMono (fun q : ℕ => N + q) := fun _ _ h => Nat.add_lt_add_left h N
    have hreg' : ProportionalRegime (fun q => m (N + q)) (fun q => n (N + q))
        (fun q => B (N + q)) (fun q => (F q).C) :=
      { γin := hreg.γin
        γout := hreg.γout
        γin_pos := hreg.γin_pos
        γout_pos := hreg.γout_pos
        B_top := hreg.B_top.comp hφ.tendsto_atTop
        ratio_in := hreg.ratio_in.comp hφ.tendsto_atTop
        ratio_out := hreg.ratio_out.comp hφ.tendsto_atTop
        bdd := hreg.bdd.imp fun c hc => ⟨hc.1, fun q => by simpa [F] using hc.2 (N + q)⟩ }
    obtain ⟨r0, hr0, hall⟩ := hK0 (fun q => m (N + q)) (fun q => n (N + q))
      (fun q => B (N + q)) (fun q => Ω (N + q)) (fun q => P (N + q)) S F
      (fun q => hdim (N + q)) (fun q => by simpa [F] using hOut (N + q))
      (fun q => by simpa [F] using hIn (N + q)) hreg'
    let r : ℕ → ℝ := fun k => if k < N then 1 else |r0 (k - N)|
    have hr : Tendsto r atTop (𝓝 0) := by
      apply (tendsto_add_atTop_iff_nat N).mp
      have ha : Tendsto (fun q => |r0 q|) atTop (𝓝 0) :=
        by
          change Tendsto (abs ∘ r0) atTop (𝓝 0)
          simpa only [abs_zero] using continuous_abs.continuousAt.tendsto.comp hr0
      convert ha using 1
      funext q
      simp [r, Nat.add_sub_cancel_left, Nat.not_lt_of_ge (Nat.le_add_right N q), Nat.add_comm]
    refine ⟨r, hr, ?_⟩
    intro k t j D hDlo hDhi
    have hDpos : 0 < riskSigma (Cv k) D := lt_of_lt_of_le hrlo hDlo
    have hBpos : 0 < B k := by
      by_contra hb
      have hb0 : B k = 0 := by omega
      have hmax : max (m k) (n k) = 0 := by
        have hh := hdim k
        simp only [hb0, Nat.cast_zero, mul_zero, Nat.cast_nonpos] at hh
        exact_mod_cast hh
      have hm0 : m k = 0 := by omega
      have hrisk := eqn_app_setup_whitened_risk (Cv k) D
      simp [hm0, fro] at hrisk
      linarith
    let Sk : FrozenSamples (P k) (m k) (n k) (B k) :=
      { zw := (cs k).act
        meas := (cs k).meas_act
        indep := (cs k).indep.precomp Sum.inl_injective
        law := (cs k).law_act }
    have hCS : 0 ≤ CS :=
      (freezing_opNorm_nonneg (Cv k).Sout).trans (hOut k)
    have hrO : opNorm (rOut (Cv k)) ≤ Real.sqrt CS := by
      have hs := freezing_opNorm_rOut_sq (Cv k)
      have hsCS : Real.sqrt CS ^ 2 = CS := Real.sq_sqrt hCS
      nlinarith [freezing_opNorm_nonneg (rOut (Cv k)), Real.sqrt_nonneg CS, hOut k]
    have hrI : opNorm (rIn (Cv k)) ≤ Real.sqrt CS := by
      have hs := freezing_opNorm_rIn_sq (Cv k)
      have hsCS : Real.sqrt CS ^ 2 = CS := Real.sq_sqrt hCS
      nlinarith [freezing_opNorm_nonneg (rIn (Cv k)), Real.sqrt_nonneg CS, hIn k]
    have hrOI : opNorm (rOut (Cv k)) * opNorm (rIn (Cv k)) ≤ |CS| := by
      have hh := mul_le_mul hrO hrI (freezing_opNorm_nonneg (rIn (Cv k)))
        (Real.sqrt_nonneg CS)
      rw [abs_of_nonneg hCS]
      nlinarith [Real.sq_sqrt hCS]
    have hAop : opNorm (Ahat (Cv k) D) ≤
        opNorm (rOut (Cv k) * D * rIn (Cv k)) / Real.sqrt (2 * rlo) := by
      have hspos : 0 < Real.sqrt (2 * riskSigma (Cv k) D) := Real.sqrt_pos.mpr (by positivity)
      have hslo : 0 < Real.sqrt (2 * rlo) := Real.sqrt_pos.mpr (by positivity)
      have hsle : Real.sqrt (2 * rlo) ≤ Real.sqrt (2 * riskSigma (Cv k) D) :=
        Real.sqrt_le_sqrt (by linarith)
      have hinv : (Real.sqrt (2 * riskSigma (Cv k) D))⁻¹ ≤
          (Real.sqrt (2 * rlo))⁻¹ := (inv_le_inv₀ hspos hslo).2 hsle
      rw [Ahat, Arot, freezing_opNorm_smul, abs_of_pos (inv_pos.mpr hspos)]
      calc
        _ ≤ (Real.sqrt (2 * rlo))⁻¹ *
            opNorm (rOut (Cv k) * D * rIn (Cv k)) :=
          mul_le_mul_of_nonneg_right hinv
            (freezing_opNorm_nonneg (rOut (Cv k) * D * rIn (Cv k)))
        _ = opNorm (rOut (Cv k) * D * rIn (Cv k)) / Real.sqrt (2 * rlo) := by
          rw [div_eq_mul_inv, mul_comm]
    by_cases hk : k < N
    · let Fk : FrozenParams (m k) (n k) (B k) :=
        { C := Cv k
          A := Ahat (Cv k) D
          hA := freezing_Ahat_norm (Cv k) D hDpos
          β := p.β
          hβ := p.hβ
          hB := hBpos }
      obtain ⟨hint, hmean⟩ := freezing_stationary_frozen p (Cv k) (cs k) t j D hDpos
        Fk rfl rfl rfl Sk
      refine ⟨hint, ?_⟩
      rw [hmean]
      have hq : opNorm (mean (P k)
          (fun ω => frozenUpd Fk Sk p.ϱ ((t : ℤ) + (j : ℤ)) ω)) ≤ 1 :=
        freezing_opNorm_mean_le _
          (freezing_upd_aem Fk Sk p.ϱ p.hϱ.le _).aestronglyMeasurable 1
          (fun ω => (lem_app_setup_filter_i p.ϱ p.hϱ.le (frozenBuf Fk Sk _ ω)).1)
      have hmul1 := freezing_opNorm_mul (rOut (Cv k))
        (mean (P k) (fun ω => frozenUpd Fk Sk p.ϱ ((t : ℤ) + (j : ℤ)) ω))
      have hmul2 := freezing_opNorm_mul
        (rOut (Cv k) * mean (P k) (fun ω => frozenUpd Fk Sk p.ϱ ((t : ℤ) + (j : ℤ)) ω))
        (rIn (Cv k))
      have hleft : opNorm (rOut (Cv k) * mean (P k)
          (fun ω => frozenUpd Fk Sk p.ϱ ((t : ℤ) + (j : ℤ)) ω) * rIn (Cv k)) ≤ |CS| := by
        calc
          _ ≤ (opNorm (rOut (Cv k)) * opNorm (mean (P k)
              (fun ω => frozenUpd Fk Sk p.ϱ ((t : ℤ) + (j : ℤ)) ω))) *
              opNorm (rIn (Cv k)) := hmul2.trans (mul_le_mul_of_nonneg_right hmul1
                (freezing_opNorm_nonneg (rIn (Cv k))))
          _ ≤ (opNorm (rOut (Cv k)) * 1) * opNorm (rIn (Cv k)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hq (freezing_opNorm_nonneg (rOut (Cv k))))
              (freezing_opNorm_nonneg (rIn (Cv k)))
          _ ≤ |CS| := by simpa using hrOI
      have hKCS : |CS| ≤ K := le_max_right _ _
      have hK0 : 0 ≤ K := (abs_nonneg CS).trans hKCS
      have hstate : 0 ≤ K * opNorm (rOut (Cv k) * D * rIn (Cv k)) :=
        mul_nonneg hK0 (freezing_opNorm_nonneg _)
      simp only [r, if_pos hk]
      nlinarith
    · obtain ⟨q, hkq⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hk)
      subst k
      let A0 : ∀ q, Mat (m (N + q)) (n (N + q)) := fun q => (F q).A
      let A : ∀ q, Mat (m (N + q)) (n (N + q)) :=
        Function.update A0 q (Ahat (Cv (N + q)) D)
      have hA : ∀ u, fro (A u) = 1 := by
        intro u
        by_cases hu : u = q
        · subst u
          simp [A]
          exact freezing_Ahat_norm _ _ hDpos
        · simp [A, hu, A0]
          exact (F u).hA
      obtain ⟨hint0, hbound⟩ := hall A hA ((t : ℤ) + (j : ℤ))
      let Fq := withState (F q) (A q) (hA q)
      have hFqC : Fq.C = Cv (N + q) := rfl
      have hFqA : Fq.A = Ahat (Cv (N + q)) D := by
        change A q = Ahat (Cv (N + q)) D
        simp [A]
      have hFqβ : Fq.β = p.β := rfl
      obtain ⟨hint, hmean⟩ := freezing_stationary_frozen p (Cv (N + q))
        (cs (N + q)) t j D hDpos Fq hFqC hFqA hFqβ Sk
      refine ⟨hint, ?_⟩
      rw [hmean]
      have hbq : opNorm (mean (P (N + q))
          (fun ω => frozenUpd Fq Sk p.ϱ ((t : ℤ) + (j : ℤ)) ω)) ≤
          K0 * opNorm (A q) + r0 q := by
        rw [hpϱ]
        simpa [Fq, Sk, S, frozenUpd] using hbound q
      have hAq : A q = Ahat (Cv (N + q)) D := by simp [A]
      rw [hAq] at hbq
      have hmul1 := freezing_opNorm_mul (rOut (Cv (N + q)))
        (mean (P (N + q)) (fun ω => frozenUpd Fq Sk p.ϱ ((t : ℤ) + (j : ℤ)) ω))
      have hmul2 := freezing_opNorm_mul
        (rOut (Cv (N + q)) * mean (P (N + q))
          (fun ω => frozenUpd Fq Sk p.ϱ ((t : ℤ) + (j : ℤ)) ω)) (rIn (Cv (N + q)))
      calc
        _ ≤ (opNorm (rOut (Cv (N + q))) * opNorm (mean (P (N + q))
            (fun ω => frozenUpd Fq Sk p.ϱ ((t : ℤ) + (j : ℤ)) ω))) *
            opNorm (rIn (Cv (N + q))) := hmul2.trans (mul_le_mul_of_nonneg_right hmul1
              (freezing_opNorm_nonneg (rIn (Cv (N + q)))))
        _ ≤ |CS| * (K0 * opNorm (Ahat (Cv (N + q)) D) + r0 q) := by
          have hR : 0 ≤ K0 * opNorm (Ahat (Cv (N + q)) D) + r0 q :=
            (freezing_opNorm_nonneg (mean (P (N + q))
              (fun ω => frozenUpd Fq Sk p.ϱ ((t : ℤ) + (j : ℤ)) ω))).trans hbq
          calc
            _ ≤ (opNorm (rOut (Cv (N + q))) *
                (K0 * opNorm (Ahat (Cv (N + q)) D) + r0 q)) *
                opNorm (rIn (Cv (N + q))) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hbq
                  (freezing_opNorm_nonneg (rOut (Cv (N + q)))))
                (freezing_opNorm_nonneg (rIn (Cv (N + q))))
            _ = (opNorm (rOut (Cv (N + q))) * opNorm (rIn (Cv (N + q)))) *
                (K0 * opNorm (Ahat (Cv (N + q)) D) + r0 q) := by ring
            _ ≤ |CS| * (K0 * opNorm (Ahat (Cv (N + q)) D) + r0 q) :=
              mul_le_mul_of_nonneg_right hrOI hR
        _ ≤ K * opNorm (rOut (Cv (N + q)) * D * rIn (Cv (N + q))) +
            K * r (N + q) := by
          have hnlt : ¬N + q < N := by omega
          simp only [r, hnlt, if_false, Nat.add_sub_cancel_left]
          have hK1 : |CS| * |K0| / Real.sqrt (2 * rlo) ≤ K := le_max_left _ _
          have hK2 : |CS| ≤ K := le_max_right _ _
          have hs : 0 < Real.sqrt (2 * rlo) := Real.sqrt_pos.mpr (by positivity)
          have hnA := freezing_opNorm_nonneg (Ahat (Cv (N + q)) D)
          have hnD := freezing_opNorm_nonneg
            (rOut (Cv (N + q)) * D * rIn (Cv (N + q)))
          have hrabs : r0 q ≤ |r0 q| := le_abs_self _
          have hKnon : 0 ≤ K := (abs_nonneg CS).trans hK2
          have hK0abs : K0 ≤ |K0| := le_abs_self _
          have hstate1 : |CS| * (K0 * opNorm (Ahat (Cv (N + q)) D)) ≤
              |CS| * (|K0| * opNorm (Ahat (Cv (N + q)) D)) := by
            gcongr
          have hstate2 : |CS| * (|K0| * opNorm (Ahat (Cv (N + q)) D)) ≤
              |CS| * (|K0| *
                (opNorm (rOut (Cv (N + q)) * D * rIn (Cv (N + q))) /
                  Real.sqrt (2 * rlo))) := by
            gcongr
          have hstate3 : |CS| * (|K0| *
                (opNorm (rOut (Cv (N + q)) * D * rIn (Cv (N + q))) /
                  Real.sqrt (2 * rlo))) ≤
              K * opNorm (rOut (Cv (N + q)) * D * rIn (Cv (N + q))) := by
            rw [div_eq_mul_inv]
            calc
              _ = (|CS| * |K0| / Real.sqrt (2 * rlo)) *
                  opNorm (rOut (Cv (N + q)) * D * rIn (Cv (N + q))) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right hK1 hnD
          have herr : |CS| * r0 q ≤ K * |r0 q| := by
            calc
              _ ≤ |CS| * |r0 q| := mul_le_mul_of_nonneg_left hrabs (abs_nonneg CS)
              _ ≤ K * |r0 q| := mul_le_mul_of_nonneg_right hK2 (abs_nonneg _)
          nlinarith
  · refine ⟨0, ?_⟩
    intro p hpγ hpCS hpϱ
    exfalso
    have hp := p.hϱ
    rw [hpϱ] at hp
    exact hϱ hp

/-! ## Conditional Jensen for the operator norm -/

open scoped Matrix.Norms.L2Operator in
private lemma freezing_condExpMat_eq_condExp {m n : ℕ} {Ω : Type*}
    (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] (X : Ω → Mat m n)
    (hX : ∀ i j, Integrable (fun ω => X ω i j) P)
    (hXop : Integrable (fun ω => opNorm (X ω)) P) :
    Muon.Foundations.condExpMat 𝒢 P X =ᵐ[P] condExp 𝒢 P X := by
  have hXaem : AEMeasurable X P :=
    AEMeasurable.of_eval fun i => AEMeasurable.of_eval fun j => (hX i j).aemeasurable
  have hXint : Integrable X P := by
    refine Integrable.mono' hXop hXaem.aestronglyMeasurable ?_
    filter_upwards with ω
    exact le_rfl
  have hent : ∀ i j, ∀ᵐ ω ∂P,
      condExp 𝒢 P X ω i j = condExp 𝒢 P (fun ω' => X ω' i j) ω := by
    intro i j
    let T : Mat m n →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj i : Mat m n →L[ℝ] (Fin n → ℝ))
    have hh := T.comp_condExp_comm (m := 𝒢) hXint
    filter_upwards [hh] with ω hω
    change condExp 𝒢 P X ω i j = condExp 𝒢 P (fun ω' => X ω' i j) ω at hω
    exact hω
  have hall : ∀ᵐ ω ∂P, ∀ i j,
      condExp 𝒢 P X ω i j = condExp 𝒢 P (fun ω' => X ω' i j) ω :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => hent i j
  filter_upwards [hall] with ω hω
  ext i j
  exact (hω i j).symm

/-- Coordinator bridge (no source label), snapshot `cr-2026-10-23`. Conditional Jensen inequality for the
operator norm: `‖𝔼[X | 𝒢]‖ ≤ 𝔼[‖X‖ | 𝒢]` almost surely, with the entrywise matrix conditional expectation
`condExpMat`. Used silently in the source where a bound on `𝔼_t‖𝓔‖` (`lem:app-dyn-coupling`(iv), l. 1568)
is turned into a bound on `‖𝔼_t[Y_{b+1} − Y_b]‖` (the drift display, ll. 2076–2080). True for every random
matrix with integrable entries and integrable operator norm: `‖A‖ = sup_{u,v} uᵀAv` over a countable dense set
of unit vectors, `uᵀ condExpMat(X) v = 𝔼[uᵀXv | 𝒢] ≤ 𝔼[‖X‖ | 𝒢]` a.s. for each pair. -/
theorem opNorm_condExpMat_le {m n : ℕ} {Ω : Type*} (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] (h𝒢 : 𝒢 ≤ mΩ) (X : Ω → Mat m n)
    (hX : ∀ i j, Integrable (fun ω => X ω i j) P) (hXop : Integrable (fun ω => opNorm (X ω)) P) :
    ∀ᵐ ω ∂P, opNorm (Muon.Foundations.condExpMat 𝒢 P X ω) ≤ condExp 𝒢 P (fun ω' => opNorm (X ω')) ω := by
  open scoped Matrix.Norms.L2Operator in
    have heq := freezing_condExpMat_eq_condExp 𝒢 X hX hXop
    have hj := norm_condExp_le (m := 𝒢) (μ := P) X
    filter_upwards [heq, hj] with ω heqω hjω
    rw [heqω, opNorm_eq_norm]
    simpa only [← opNorm_eq_norm] using hjω

/-! ## Private infrastructure for the conditional bridges (copied from the private lemmas of Transport/Block) -/

section fzbinfra

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}

private lemma fzb_Q_entry_bound {m n : ℕ} (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (K : Mat m n) (i : Fin m) (j : Fin n) :
    |Q ϱ K i j| ≤ (m : ℝ) + 1 := by
  obtain ⟨_, hf, hk, _⟩ := lem_app_setup_filter_i ϱ hϱ K
  have h1 := freezing_abs_entry_le_fro (Q ϱ K) i j
  have hr : (K.rank : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hk.trans (min_le_left m n)
  have h2 : fro (Q ϱ K) ^ 2 ≤ (m : ℝ) := hf.trans hr
  have h0 : 0 ≤ fro (Q ϱ K) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (fro (Q ϱ K) - 1)]

private lemma fzb_past_le (S : DynSetup p P m n B) (t : ℕ) : dynPast S t ≤ mΩ := by
  refine sup_le (iSup_le fun s => iSup_le fun _ => iSup_le fun a => ?_) ?_
  · exact (S.cs.meas_act s a).comap_le
  · exact S.M0_meas.comap_le

private lemma fzb_past_mono (S : DynSetup p P m n B) {s t : ℕ} (h : s ≤ t) :
    dynPast S s ≤ dynPast S t := by
  refine sup_le_sup_right ?_ _
  refine iSup_le fun u => iSup_le fun hu => iSup_le fun a => ?_
  exact le_iSup₂_of_le u ⟨hu.1, hu.2.trans (by exact_mod_cast h)⟩ (le_iSup_of_le a le_rfl)

private lemma fzb_indep_sup {Ω : Type} (A M F G : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hAG : A ≤ G) (hFG : F ≤ G) (hGle : G ≤ mΩ) (hMle : M ≤ mΩ) (hFle : F ≤ mΩ)
    (hAF : Indep A F P) (hMG : Indep M G P) : Indep (A ⊔ M) F P := by
  have hAle : A ≤ mΩ := hAG.trans hGle
  let p1 : Set (Set Ω) := {s | ∃ a, MeasurableSet[A] a ∧ ∃ b, MeasurableSet[M] b ∧ s = a ∩ b}
  have hp1 : IsPiSystem p1 := by
    rintro _ ⟨a, ha, b, hb, rfl⟩ _ ⟨a', ha', b', hb', rfl⟩ _
    refine ⟨a ∩ a', @MeasurableSet.inter Ω A _ _ ha ha', b ∩ b', @MeasurableSet.inter Ω M _ _ hb hb', ?_⟩
    ext x; simp only [Set.mem_inter_iff]; tauto
  have hgen : A ⊔ M = MeasurableSpace.generateFrom p1 := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro a ha
        refine MeasurableSpace.measurableSet_generateFrom ⟨a, ha, Set.univ, @MeasurableSet.univ Ω M, by simp⟩
      · intro b hb
        refine MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, @MeasurableSet.univ Ω A, b, hb, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact @MeasurableSet.inter Ω (A ⊔ M) _ _ ((le_sup_left : A ≤ A ⊔ M) _ ha) ((le_sup_right : M ≤ A ⊔ M) _ hb)
  have hp2 : IsPiSystem {s | MeasurableSet[F] s} := @MeasurableSpace.isPiSystem_measurableSet Ω F
  have hgen2 : F = MeasurableSpace.generateFrom {s | MeasurableSet[F] s} := (@MeasurableSpace.generateFrom_measurableSet Ω F).symm
  refine IndepSets.indep (sup_le hAle hMle) hFle hp1 hp2 hgen hgen2 ?_
  rw [IndepSets_iff]
  rintro _ f ⟨a, ha, b, hb, rfl⟩ hf
  have haG : MeasurableSet[G] a := hAG a ha
  have hfG : MeasurableSet[G] f := hFG f hf
  have h1 : P (a ∩ b ∩ f) = P b * P (a ∩ f) := by
    have := (Indep_iff _ _ _).mp hMG b (a ∩ f) hb (@MeasurableSet.inter Ω G _ _ haG hfG)
    rw [show a ∩ b ∩ f = b ∩ (a ∩ f) by ext x; simp only [Set.mem_inter_iff]; tauto]
    exact this
  have h2 : P (a ∩ f) = P a * P f := (Indep_iff _ _ _).mp hAF a f ha hf
  have h3 : P (a ∩ b) = P b * P a := by
    have := (Indep_iff _ _ _).mp hMG b a hb haG
    rw [Set.inter_comm]; exact this
  rw [h1, h2, h3]; ring


private lemma fzb_indep_past_future [IsProbabilityMeasure P] (S : DynSetup p P m n B) (t : ℕ) :
    Indep (dynPast S t) (chainFuture S.cs t) P := by
  refine fzb_indep_sup _ _ _
    ((⨆ (s : ℤ) (_ : 1 ≤ s) (a : Fin B), MeasurableSpace.comap (S.cs.act s a) inferInstance) ⊔
      (⨆ (s : ℤ) (j : ℕ) (a : Fin B), MeasurableSpace.comap (S.cs.aux s j a) inferInstance)) P
    ?_ ?_ ?_ ?_ ?_ ?_ S.M0_indep
  · refine le_sup_of_le_left (iSup_le fun s => iSup_le fun hs => iSup_le fun a => ?_)
    exact le_iSup₂_of_le s hs.1 (le_iSup_of_le a le_rfl)
  · refine sup_le ?_ ?_
    · refine le_sup_of_le_left (iSup_le fun s => iSup_le fun hs => iSup_le fun a => ?_)
      exact le_iSup₂_of_le s (by omega) (le_iSup_of_le a le_rfl)
    · refine le_sup_of_le_right (iSup_le fun j => iSup_le fun a => ?_)
      exact le_iSup_of_le (t : ℤ) (le_iSup_of_le j (le_iSup_of_le a le_rfl))
  · refine sup_le (iSup_le fun s => iSup_le fun _ => iSup_le fun a => ?_)
      (iSup_le fun s => iSup_le fun j => iSup_le fun a => ?_)
    · exact (S.cs.meas_act s a).comap_le
    · exact (S.cs.meas_aux s j a).comap_le
  · exact S.M0_meas.comap_le
  · refine sup_le ?_ ?_
    · exact iSup_le fun s => iSup_le fun _ => iSup_le fun a => (S.cs.meas_act s a).comap_le
    · exact iSup_le fun j => iSup_le fun a => (S.cs.meas_aux _ j a).comap_le
  · have hind := (iIndepFun_iff_iIndep _ _ _).mp S.cs.indep
    have hle : ∀ i, MeasurableSpace.comap
        (Sum.elim (fun q : ℤ × Fin B => S.cs.act q.1 q.2)
          (fun q : ℤ × ℕ × Fin B => S.cs.aux q.1 q.2.1 q.2.2) i : Ω → Vec m × Vec n) inferInstance ≤ mΩ := by
      intro i
      rcases i with q | q
      · exact (S.cs.meas_act q.1 q.2).comap_le
      · exact (S.cs.meas_aux q.1 q.2.1 q.2.2).comap_le
    have hdisj : Disjoint {i : (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B) | ∃ q : ℤ × Fin B, i = Sum.inl q ∧ 1 ≤ q.1 ∧ q.1 ≤ (t : ℤ)}
        {i | (∃ q : ℤ × Fin B, i = Sum.inl q ∧ (t : ℤ) < q.1) ∨ (∃ q : ℤ × ℕ × Fin B, i = Sum.inr q ∧ q.1 = (t : ℤ))} := by
      rw [Set.disjoint_left]
      rintro i ⟨q, rfl, h1, h2⟩ (⟨q', hq', h3⟩ | ⟨q', hq', _⟩)
      · cases hq'; omega
      · cases hq'
    have := indep_iSup_of_disjoint hle hind hdisj
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left this ?_) ?_
    · refine iSup_le fun s => iSup_le fun hs => iSup_le fun a => ?_
      exact le_iSup₂_of_le (Sum.inl (s, a)) ⟨(s, a), rfl, hs.1, hs.2⟩ le_rfl
    · refine sup_le (iSup_le fun s => iSup_le fun hs => iSup_le fun a => ?_)
        (iSup_le fun j => iSup_le fun a => ?_)
      · exact le_iSup₂_of_le (Sum.inl (s, a)) (Or.inl ⟨(s, a), rfl, hs⟩) le_rfl
      · exact le_iSup₂_of_le (Sum.inr ((t : ℤ), j, a)) (Or.inr ⟨((t : ℤ), j, a), rfl, rfl⟩) le_rfl

private lemma fzb_risk_nonneg {m n : ℕ} (C : Covariances m n) (Δ : Mat m n) :
    0 ≤ riskSigma C Δ := by
  rw [eqn_app_setup_whitened_risk]
  positivity

private lemma fzb_risk_cont {m n : ℕ} (C : Covariances m n) :
    Continuous (fun Δ : Mat m n => riskSigma C Δ) := by
  unfold riskSigma pairSigma
  fun_prop

private lemma fzb_mat_meas {Ω : Type} {σ : MeasurableSpace Ω} {m n : ℕ} {F : Ω → Mat m n}
    (h : ∀ i j, Measurable[σ] fun ω => F ω i j) : Measurable[σ] F :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => h i j

private lemma fzb_entry_meas {Ω : Type} {σ : MeasurableSpace Ω} {m n : ℕ} {F : Ω → Mat m n}
    (hF : Measurable[σ] F) (i : Fin m) (j : Fin n) : Measurable[σ] fun ω => F ω i j :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hF)

private lemma fzb_grad_meas {Ω : Type} {σ : MeasurableSpace Ω} {B m n : ℕ}
    {Δ : Ω → Mat m n} {b : Ω → Batch m n B}
    (hΔ : Measurable[σ] Δ) (hb : Measurable[σ] b) :
    Measurable[σ] (fun ω => grad (Δ ω) (b ω)) := by
  have hGc : Continuous (fun pr : Mat m n × Batch m n B => grad pr.1 pr.2) := by
    unfold grad resid outer
    fun_prop
  exact Measurable.comp (g := fun pr : Mat m n × Batch m n B => grad pr.1 pr.2)
    (f := fun ω => (Δ ω, b ω)) hGc.measurable (hΔ.prodMk hb)

private lemma fzb_stepUpdate_meas {Ω : Type} {σ : MeasurableSpace Ω} {B m n : ℕ}
    (C : Covariances m n) (p : AlgParams m n) (s : Ω → AlgState m n) (b : Ω → Batch m n B)
    (hW : Measurable[σ] (fun ω => (s ω).W)) (hMp : Measurable[σ] (fun ω => (s ω).Mprev))
    (hb : Measurable[σ] b) :
    Measurable[σ] (fun ω => stepUpdate C p (s ω) (b ω)) ∧
      Measurable[σ] (fun ω => stepBuffer p (s ω) (b ω)) := by
  have hWc : Continuous (fun A : Mat m n => A - p.Wstar) := continuous_id.sub continuous_const
  have hD : Measurable[σ] (fun ω => errorOf p (s ω)) := hWc.measurable.comp hW
  have hR : Measurable[σ] (fun ω => riskSigma C (errorOf p (s ω))) := (fzb_risk_cont C).measurable.comp hD
  have hset : MeasurableSet[σ] {ω | riskSigma C (errorOf p (s ω)) = 0} :=
    hR (measurableSet_singleton 0)
  have hF : Measurable[σ] (fun ω => grad (errorOf p (s ω)) (b ω)) := fzb_grad_meas hD hb
  have hbuf : Measurable[σ] (fun ω => stepBuffer p (s ω) (b ω)) := by
    apply fzb_mat_meas
    intro i j
    have hMij := fzb_entry_meas hMp i j
    have hFij := fzb_entry_meas hF i j
    simp only [stepBuffer, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact (hMij.const_mul _).add (hFij.const_mul _)
  refine ⟨?_, hbuf⟩
  refine Measurable.ite hset measurable_const ?_
  have hnn : ∀ ω, (0 : ℝ) ≤ 2 * riskSigma C (errorOf p (s ω)) * p.ϱ :=
    fun ω => mul_nonneg (mul_nonneg (by norm_num) (fzb_risk_nonneg C _)) p.hϱ.le
  have hφ : Measurable[σ]
      (fun ω => (⟨2 * riskSigma C (errorOf p (s ω)) * p.ϱ, hnn ω⟩ : Set.Ici (0 : ℝ))) :=
    ((hR.const_mul 2).mul_const p.ϱ).subtype_mk
  exact measurable_Q.comp (hφ.prodMk hbuf)

private lemma fzb_step_meas {Ω : Type} {σ : MeasurableSpace Ω} {B m n : ℕ}
    (C : Covariances m n) (p : AlgParams m n) (k : ℕ) (s : Ω → AlgState m n) (b : Ω → Batch m n B)
    (hW : Measurable[σ] (fun ω => (s ω).W)) (hMp : Measurable[σ] (fun ω => (s ω).Mprev))
    (hb : Measurable[σ] b) :
    Measurable[σ] (fun ω => (step C p k (s ω) (b ω)).W) ∧
      Measurable[σ] (fun ω => (step C p k (s ω) (b ω)).Mprev) := by
  obtain ⟨hU, hbuf⟩ := fzb_stepUpdate_meas (σ := σ) C p s b hW hMp hb
  refine ⟨?_, hbuf⟩
  apply fzb_mat_meas
  intro i j
  have hWij := fzb_entry_meas hW i j
  have hUij := fzb_entry_meas hU i j
  simp only [step, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact hWij.sub (hUij.const_mul _)

private lemma fzb_pi_meas {Ω : Type} {σ : MeasurableSpace Ω} {ι : Type*} {π : ι → Type*}
    [∀ i, MeasurableSpace (π i)] {g : Ω → ∀ i, π i} (h : ∀ i, Measurable[σ] fun ω => g ω i) :
    Measurable[σ] g := measurable_pi_iff.mpr h


section dyn

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}

private lemma fzb_batch_meas (S : DynSetup p P m n B) (u : ℕ) :
    Measurable[dynPast S (u + 1)] (dynBatch S u) := by
  refine fzb_pi_meas (fun a => ?_)
  have h1 : Measurable[dynPast S (u + 1)] (S.cs.act ((u : ℤ) + 1) a) := by
    refine Measurable.of_comap_le ?_
    refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le ((u : ℤ) + 1) ⟨by omega, by push_cast; omega⟩ (le_iSup_of_le a le_rfl)
  have hc : Continuous (fun z : Vec m × Vec n => phys S.C z) := by
    unfold phys; fun_prop
  exact hc.measurable.comp h1

private lemma fzb_state_meas (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S t] (fun ω => (dynState S t ω).W) ∧
      Measurable[dynPast S t] (fun ω => (dynState S t ω).Mprev) := by
  induction t with
  | zero =>
    refine ⟨measurable_const, ?_⟩
    have : Measurable[MeasurableSpace.comap S.M0 inferInstance] S.M0 := comap_measurable _
    exact this.mono (le_sup_right) le_rfl
  | succ k ih =>
    have hW : Measurable[dynPast S (k + 1)] (fun ω => (dynState S k ω).W) := ih.1.mono (fzb_past_mono S (Nat.le_succ k)) le_rfl
    have hM : Measurable[dynPast S (k + 1)] (fun ω => (dynState S k ω).Mprev) := ih.2.mono (fzb_past_mono S (Nat.le_succ k)) le_rfl
    exact fzb_step_meas (σ := dynPast S (k + 1)) S.C S.alg k (dynState S k) (dynBatch S k) hW hM (fzb_batch_meas S k)



private lemma fzb_delta_meas (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S t] (dynDelta S t) := by
  have hWc : Continuous (fun A : Mat m n => A - S.alg.Wstar) := continuous_id.sub continuous_const
  exact hWc.measurable.comp (fzb_state_meas S t).1

private lemma fzb_buf_meas (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S t] (dynBuf S t) := (fzb_state_meas S t).2

private lemma fzb_upd_meas (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S (t + 1)] (dynUpd S t) := by
  have hW : Measurable[dynPast S (t + 1)] (fun ω => (dynState S t ω).W) :=
    (fzb_state_meas S t).1.mono (fzb_past_mono S (Nat.le_succ t)) le_rfl
  have hM : Measurable[dynPast S (t + 1)] (fun ω => (dynState S t ω).Mprev) :=
    (fzb_state_meas S t).2.mono (fzb_past_mono S (Nat.le_succ t)) le_rfl
  exact (fzb_stepUpdate_meas (σ := dynPast S (t + 1)) S.C S.alg (dynState S t) (dynBatch S t) hW hM
    (fzb_batch_meas S t)).1

private lemma fzb_upd_meas' (S : DynSetup p P m n B) (t : ℕ) : Measurable (dynUpd S t) :=
  (fzb_upd_meas S t).mono (fzb_past_le S _) le_rfl

private lemma fzb_dynUpd_bound (S : DynSetup p P m n B) (t : ℕ) (ω : Ω) (i : Fin m) (j : Fin n) :
    |dynUpd S t ω i j| ≤ (m : ℝ) + 1 := by
  unfold dynUpd gtRand stepUpdate
  split_ifs with h
  · simp; positivity
  · exact fzb_Q_entry_bound _ (mul_nonneg (mul_nonneg (by norm_num) (fzb_risk_nonneg _ _)) S.alg.hϱ.le) _ i j

end dyn

end fzbinfra

section fzbmore

private lemma fzb_bound_of_cont {m n : ℕ} (h : Mat m n → ℝ) (hc : Continuous h) (R : ℝ) :
    ∃ K : ℝ, ∀ Y : Mat m n, (∀ i j, |Y i j| ≤ R) → |h Y| ≤ K := by
  have hK : IsCompact (Set.pi Set.univ fun i : Fin m => Set.pi Set.univ fun j : Fin n => Set.Icc (-R) R :
      Set (Mat m n)) :=
    isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_Icc
  obtain ⟨K, hK'⟩ := hK.exists_bound_of_continuousOn (f := h) hc.continuousOn
  refine ⟨K, fun Y hY => ?_⟩
  have hmem : Y ∈ (Set.pi Set.univ fun i : Fin m => Set.pi Set.univ fun j : Fin n => Set.Icc (-R) R :
      Set (Mat m n)) := by
    intro i _ j _
    exact abs_le.mp (hY i j)
  simpa using hK' Y hmem

private lemma fzb_integrable_cont {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {m n : ℕ} {X : Ω' → Mat m n} (hX : AEMeasurable X P') (R : ℝ)
    (hb : ∀ ω i j, |X ω i j| ≤ R) (h : Mat m n → ℝ) (hc : Continuous h) :
    Integrable (fun ω => h (X ω)) P' := by
  obtain ⟨K, hK⟩ := fzb_bound_of_cont h hc R
  refine Integrable.of_bound (C := K) (hc.measurable.comp_aemeasurable hX).aestronglyMeasurable ?_
  exact ae_of_all _ fun ω => by simpa using hK (X ω) (hb ω)

open scoped Matrix.Norms.L2Operator in
private lemma fzb_opNorm_cont {m n : ℕ} : Continuous (fun A : Mat m n => opNorm A) := by
  have h : (fun M : Mat m n => opNorm M) = fun M => ‖M‖ := funext opNorm_eq_norm
  rw [h]
  exact continuous_norm

open scoped Matrix.Norms.L2Operator in
private lemma fzb_opNorm_add_le {m n : ℕ} (A B : Mat m n) :
    opNorm (A + B) ≤ opNorm A + opNorm B := by
  simpa only [opNorm_eq_norm] using norm_add_le A B

open scoped Matrix.Norms.L2Operator in
private lemma fzb_opNorm_sum_le {m n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Mat m n) :
    opNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, opNorm (f i) := by
  simpa only [opNorm_eq_norm] using norm_sum_le s f

private lemma fzb_future_meas {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (cs : ChainSamples P m n B) (t : ℕ) : Measurable (freezingFuture cs t) := by
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro k
    apply Measurable.of_eval
    intro a
    exact cs.meas_act ((t : ℤ) + k + 1) a
  · apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro a
    exact cs.meas_aux (t : ℤ) j a

private lemma fzb_statV_meas {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ)
    {D : Ω → Mat m n} (hD : Measurable D) (r : ℕ) :
    Measurable (fun ω => stationaryV p C cs t (D ω) r ω) := by
  have h := (freezingV_joint_meas (B := B) p C r).comp (hD.prodMk (fzb_future_meas cs t))
  have e : (fun ω => stationaryV p C cs t (D ω) r ω) =
      fun ω => freezingV p C (D ω) (freezingFuture cs t ω) r :=
    funext fun ω => (freezingV_eq p C cs t (D ω) r ω).symm
  rw [e]
  exact h

private lemma fzb_statV_bound {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ)
    (D : Mat m n) (r : ℕ) (ω : Ω) (i : Fin m) (j : Fin n) :
    |stationaryV p C cs t D r ω i j| ≤ (m : ℝ) + 1 := by
  rw [← freezingV_eq p C cs t D r ω]
  unfold freezingV
  exact fzb_Q_entry_bound _ (by
    unfold physRidge
    exact mul_nonneg (mul_nonneg (by norm_num) (freezing_risk_nonneg C D)) p.hϱ.le) _ i j

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}

private lemma fzb_delta_meas' (S : DynSetup p P m n B) (t : ℕ) : Measurable (dynDelta S t) :=
  (fzb_delta_meas S t).mono (fzb_past_le S t) le_rfl

private lemma fzb_stat_entry_meas (S : DynSetup p P m n B) (t : ℕ) (i : Fin m) (j : Fin n) :
    Measurable (fun ω => dynStatSum p S t ω i j) := by
  have : (fun ω => dynStatSum p S t ω i j) =
      fun ω => ∑ r ∈ Finset.range (blockLen B), stationaryV p S.C S.cs t (dynDelta S t ω) r ω i j := by
    funext ω
    simp only [dynStatSum, Matrix.sum_apply]
  rw [this]
  refine Finset.measurable_sum _ fun r _ => ?_
  exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    (fzb_statV_meas p S.C S.cs t (fzb_delta_meas' S t) r))

private lemma fzb_stat_entry_bound (S : DynSetup p P m n B) (t : ℕ) (ω : Ω) (i : Fin m) (j : Fin n) :
    |dynStatSum p S t ω i j| ≤ (blockLen B : ℝ) * ((m : ℝ) + 1) := by
  simp only [dynStatSum, Matrix.sum_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun r _ => fzb_statV_bound p S.C S.cs t _ r ω i j).trans ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact le_rfl

private lemma fzb_X_entry_meas (S : DynSetup p P m n B) (t : ℕ) (i : Fin m) (j : Fin n) :
    Measurable (fun ω => (∑ u ∈ Finset.range (blockLen B), dynUpd S (t + u) ω) i j) := by
  have : (fun ω => (∑ u ∈ Finset.range (blockLen B), dynUpd S (t + u) ω) i j) =
      fun ω => ∑ u ∈ Finset.range (blockLen B), dynUpd S (t + u) ω i j := by
    funext ω
    simp only [Matrix.sum_apply]
  rw [this]
  refine Finset.measurable_sum _ fun u _ => ?_
  exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (fzb_upd_meas' S (t + u)))

private lemma fzb_X_entry_bound (S : DynSetup p P m n B) (t : ℕ) (ω : Ω) (i : Fin m) (j : Fin n) :
    |(∑ u ∈ Finset.range (blockLen B), dynUpd S (t + u) ω) i j| ≤
      (blockLen B : ℝ) * ((m : ℝ) + 1) := by
  simp only [Matrix.sum_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun u _ => fzb_dynUpd_bound S (t + u) ω i j).trans ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact le_rfl

end fzbmore

section fzbcore

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}

private lemma fzb_admSet_meas {m n : ℕ} (C : Covariances m n) (K : ℝ × ℝ × ℝ) :
    MeasurableSet (admSetOf C K) := by
  have hr : Measurable (fun D : Mat m n => riskSigma C D) := (fzb_risk_cont C).measurable
  have hf : Measurable (fun D : Mat m n => fro D ^ 2) := by
    apply (show Continuous (fun D : Mat m n => fro D ^ 2) by
      unfold fro
      fun_prop).measurable
  change MeasurableSet ({D : Mat m n | K.1 ≤ riskSigma C D} ∩
    ({D : Mat m n | riskSigma C D ≤ K.2.1} ∩ {D : Mat m n | fro D ^ 2 ≤ K.2.2}))
  exact (measurableSet_le measurable_const hr).inter
    ((measurableSet_le hr measurable_const).inter (measurableSet_le hf measurable_const))

private lemma fzb_condExp_stat [IsProbabilityMeasure P] (S : DynSetup p P m n B) (t : ℕ)
    (𝒦 : Set (Mat m n)) (h𝒦 : MeasurableSet 𝒦) (i : Fin m) (j : Fin n) :
    ∀ᵐ ω ∂P, dynDelta S t ω ∈ 𝒦 →
      condExp (dynPast S t) P (fun ω' => dynStatSum p S t ω' i j) ω =
        (∑ r ∈ Finset.range (blockLen B),
          mean P (fun ω' => stationaryV p S.C S.cs t (dynDelta S t ω) r ω')) i j := by
  set A : Set Ω := dynDelta S t ⁻¹' 𝒦 with hA
  have hAm : MeasurableSet[dynPast S t] A := fzb_delta_meas S t h𝒦
  have hAm' : MeasurableSet A := fzb_delta_meas' S t h𝒦
  let f : Ω → ℝ := fun ω => dynStatSum p S t ω i j
  have hfm : Measurable f := fzb_stat_entry_meas S t i j
  have hfi : Integrable f P :=
    Integrable.of_bound hfm.aestronglyMeasurable ((blockLen B : ℝ) * ((m : ℝ) + 1))
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using fzb_stat_entry_bound S t ω i j)
  let Φ : Mat m n → (ℕ → Mat m n) → ℝ := fun D x =>
    𝒦.indicator (fun _ => (∑ r ∈ Finset.range (blockLen B), x r) i j) D
  have hΦ : Measurable (Function.uncurry Φ) := by
    have e : Function.uncurry Φ = {z : Mat m n × (ℕ → Mat m n) | z.1 ∈ 𝒦}.indicator
        (fun z => (∑ r ∈ Finset.range (blockLen B), z.2 r) i j) := by
      funext z
      simp [Φ, Function.uncurry, Set.indicator]
    rw [e]
    refine Measurable.indicator ?_ (measurable_fst h𝒦)
    simp only [Matrix.sum_apply]
    refine Finset.measurable_sum _ fun r _ => ?_
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      ((measurable_pi_apply r).comp measurable_snd))
  have hΦeq : (fun ω => Φ (dynDelta S t ω)
      (fun r => stationaryV p S.C S.cs t (dynDelta S t ω) r ω)) = A.indicator f := by
    funext ω
    by_cases h : dynDelta S t ω ∈ 𝒦
    · have h' : ω ∈ A := h
      simp [Φ, Set.indicator, h, h', f, dynStatSum, Matrix.sum_apply]
    · have h' : ω ∉ A := h
      simp [Φ, Set.indicator, h, h']
  have hint : Integrable (fun ω => Φ (dynDelta S t ω)
      (fun r => stationaryV p S.C S.cs t (dynDelta S t ω) r ω)) P := by
    rw [hΦeq]
    exact hfi.indicator hAm'
  have hF0 := stationary_freezing_condExp (dynPast S t) p S.C S.cs t (fzb_past_le S t)
    (fzb_indep_past_future S t) (dynDelta S t) (fzb_delta_meas S t) Φ hΦ hint
  rw [hΦeq] at hF0
  have hind := condExp_indicator (μ := P) hfi hAm
  filter_upwards [hF0, hind] with ω h0 h1 hω
  have hωA : ω ∈ A := hω
  rw [Set.indicator_of_mem hωA] at h1
  rw [← h1, h0]
  have hent : ∀ ω', Φ (dynDelta S t ω)
      (fun r => stationaryV p S.C S.cs t (dynDelta S t ω) r ω') =
      ∑ r ∈ Finset.range (blockLen B), stationaryV p S.C S.cs t (dynDelta S t ω) r ω' i j := by
    intro ω'
    simp [Φ, hω, Matrix.sum_apply]
  simp_rw [hent]
  rw [integral_finsetSum]
  · simp [mean, Matrix.sum_apply]
  · intro r _
    refine Integrable.of_bound ?_ ((m : ℝ) + 1)
      (ae_of_all _ fun ω' => by
        simpa [Real.norm_eq_abs] using fzb_statV_bound p S.C S.cs t (dynDelta S t ω) r ω' i j)
    exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (fzb_statV_meas p S.C S.cs t (D := fun _ => dynDelta S t ω) measurable_const r))).aestronglyMeasurable

private lemma fzb_root_prod_le {m n : ℕ} (C : Covariances m n) (CS : ℝ) (hCS : 0 ≤ CS)
    (h1 : opNorm C.Sout ≤ CS) (h2 : opNorm C.Sin ≤ CS) :
    opNorm (rOut C) * opNorm (rIn C) ≤ CS := by
  have ho : opNorm (rOut C) ≤ Real.sqrt CS := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [sq]
    exact (freezing_opNorm_rOut_sq C).le.trans h1
  have hi : opNorm (rIn C) ≤ Real.sqrt CS := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [sq]
    exact (freezing_opNorm_rIn_sq C).le.trans h2
  calc opNorm (rOut C) * opNorm (rIn C) ≤ Real.sqrt CS * Real.sqrt CS :=
        mul_le_mul ho hi (freezing_opNorm_nonneg _) (Real.sqrt_nonneg _)
    _ = CS := Real.mul_self_sqrt hCS

private lemma fzb_drift_pw [IsProbabilityMeasure P] (S : DynSetup p P m n B) (t : ℕ)
    (rlo rhi E K1 rk : ℝ) (R : Ω → ℝ)
    (hmean : ∀ (j : ℕ) (D : Mat m n), rlo ≤ riskSigma S.C D → riskSigma S.C D ≤ rhi →
      opNorm (rOut S.C * mean P (fun ω => stationaryV p S.C S.cs t D j ω) * rIn S.C) ≤
        K1 * opNorm (rOut S.C * D * rIn S.C) + K1 * rk)
    (hcoup : ∀ᵐ ω ∂P, ω ∈ dynInK S t (rlo, rhi, E) →
      condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
        (fun ω => opNorm (dynSumErr p S t ω))) ω ≤ R ω) :
    ∀ᵐ ω ∂P, ω ∈ dynInK S t (rlo, rhi, E) →
      opNorm (rOut S.C * Muon.Foundations.condExpMat (dynPast S t) P
          (fun ω' => ∑ u ∈ Finset.range (blockLen B), dynUpd S (t + u) ω') ω * rIn S.C) ≤
        (blockLen B : ℝ) * (K1 * opNorm (rOut S.C * dynDelta S t ω * rIn S.C) + K1 * rk) +
          opNorm (rOut S.C) * opNorm (rIn S.C) * R ω := by
  classical
  set 𝒦 := admSetOf S.C (rlo, rhi, E) with h𝒦def
  have h𝒦 : MeasurableSet 𝒦 := fzb_admSet_meas S.C _
  have hXE : ∀ ω, (∑ u ∈ Finset.range (blockLen B), dynUpd S (t + u) ω) =
      dynStatSum p S t ω + dynSumErr p S t ω := by
    intro ω
    simp only [dynStatSum, dynSumErr, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by abel
  have hEe : ∀ ω i j, dynSumErr p S t ω i j =
      (∑ u ∈ Finset.range (blockLen B), dynUpd S (t + u) ω) i j - dynStatSum p S t ω i j := by
    intro ω i j
    rw [hXE ω]
    simp
  have hXi : ∀ i j, Integrable (fun ω => (∑ u ∈ Finset.range (blockLen B), dynUpd S (t + u) ω) i j) P :=
    fun i j => Integrable.of_bound (fzb_X_entry_meas S t i j).aestronglyMeasurable
      ((blockLen B : ℝ) * ((m : ℝ) + 1))
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using fzb_X_entry_bound S t ω i j)
  have hSi : ∀ i j, Integrable (fun ω => dynStatSum p S t ω i j) P :=
    fun i j => Integrable.of_bound (fzb_stat_entry_meas S t i j).aestronglyMeasurable
      ((blockLen B : ℝ) * ((m : ℝ) + 1))
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using fzb_stat_entry_bound S t ω i j)
  have hEi : ∀ i j, Integrable (fun ω => dynSumErr p S t ω i j) P := by
    intro i j
    have := (hXi i j).sub (hSi i j)
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp only [Pi.sub_apply]
    exact (hEe ω i j).symm
  have hEm : ∀ i j, Measurable (fun ω => dynSumErr p S t ω i j) := by
    intro i j
    have e : (fun ω => dynSumErr p S t ω i j) =
        (fun ω => (∑ u ∈ Finset.range (blockLen B), dynUpd S (t + u) ω) i j) -
          (fun ω => dynStatSum p S t ω i j) := funext fun ω => hEe ω i j
    rw [e]
    exact (fzb_X_entry_meas S t i j).sub (fzb_stat_entry_meas S t i j)
  have hEmat : Measurable (dynSumErr p S t) :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => hEm i j
  have hEop : Integrable (fun ω => opNorm (dynSumErr p S t ω)) P := by
    refine fzb_integrable_cont (X := dynSumErr p S t) hEmat.aemeasurable
      (2 * ((blockLen B : ℝ) * ((m : ℝ) + 1))) (fun ω i j => ?_) (fun A => opNorm A) fzb_opNorm_cont
    rw [hEe ω i j]
    have h1 := fzb_X_entry_bound S t ω i j
    have h2 := fzb_stat_entry_bound S t ω i j
    calc _ ≤ |(∑ u ∈ Finset.range (blockLen B), dynUpd S (t + u) ω) i j| + |dynStatSum p S t ω i j| :=
          abs_sub _ _
      _ ≤ _ := by linarith
  have h1 : ∀ᵐ ω ∂P, ∀ i j,
      condExp (dynPast S t) P (fun ω' => (∑ u ∈ Finset.range (blockLen B), dynUpd S (t + u) ω') i j) ω =
        condExp (dynPast S t) P (fun ω' => dynStatSum p S t ω' i j) ω +
          condExp (dynPast S t) P (fun ω' => dynSumErr p S t ω' i j) ω := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    have := condExp_add (μ := P) (hSi i j) (hEi i j) (dynPast S t)
    have e : (fun ω' => (∑ u ∈ Finset.range (blockLen B), dynUpd S (t + u) ω') i j) =
        (fun ω' => dynStatSum p S t ω' i j) + (fun ω' => dynSumErr p S t ω' i j) := by
      funext ω'
      rw [hXE ω']
      simp
    rw [e]
    filter_upwards [this] with ω hω
    simpa using hω
  have h2 : ∀ᵐ ω ∂P, ∀ i j, dynDelta S t ω ∈ 𝒦 →
      condExp (dynPast S t) P (fun ω' => dynStatSum p S t ω' i j) ω =
        (∑ r ∈ Finset.range (blockLen B),
          mean P (fun ω' => stationaryV p S.C S.cs t (dynDelta S t ω) r ω')) i j :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => fzb_condExp_stat S t 𝒦 h𝒦 i j
  have h3 := opNorm_condExpMat_le (dynPast S t) (fzb_past_le S t) (dynSumErr p S t) hEi hEop
  have hAm : MeasurableSet[dynPast S t] (dynInK S t (rlo, rhi, E)) := fzb_delta_meas S t h𝒦
  have h4 := condExp_indicator (μ := P) hEop hAm
  filter_upwards [h1, h2, h3, h4, hcoup] with ω e1 e2 e3 e4 e5 hω
  have hD𝒦 : dynDelta S t ω ∈ 𝒦 := hω
  have hmat : Muon.Foundations.condExpMat (dynPast S t) P
      (fun ω' => ∑ u ∈ Finset.range (blockLen B), dynUpd S (t + u) ω') ω =
      (∑ r ∈ Finset.range (blockLen B),
          mean P (fun ω' => stationaryV p S.C S.cs t (dynDelta S t ω) r ω')) +
        Muon.Foundations.condExpMat (dynPast S t) P (dynSumErr p S t) ω := by
    ext i j
    simp only [Matrix.add_apply]
    rw [Muon.Foundations.condExpMat_apply, Muon.Foundations.condExpMat_apply, e1 i j, e2 i j hD𝒦]
  rw [hmat, Matrix.mul_add, Matrix.add_mul]
  refine (fzb_opNorm_add_le _ _).trans (add_le_add ?_ ?_)
  · have e : rOut S.C * (∑ r ∈ Finset.range (blockLen B),
          mean P (fun ω' => stationaryV p S.C S.cs t (dynDelta S t ω) r ω')) * rIn S.C =
        ∑ r ∈ Finset.range (blockLen B), (rOut S.C *
          mean P (fun ω' => stationaryV p S.C S.cs t (dynDelta S t ω) r ω') * rIn S.C) := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
    rw [e]
    refine (fzb_opNorm_sum_le _ _).trans ?_
    calc _ ≤ ∑ r ∈ Finset.range (blockLen B),
          (K1 * opNorm (rOut S.C * dynDelta S t ω * rIn S.C) + K1 * rk) :=
          Finset.sum_le_sum fun r _ => hmean r _ hD𝒦.1 hD𝒦.2.1
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · have hcE : opNorm (Muon.Foundations.condExpMat (dynPast S t) P (dynSumErr p S t) ω) ≤ R ω := by
      refine e3.trans ?_
      have e4' : condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => opNorm (dynSumErr p S t ω))) ω =
          condExp (dynPast S t) P (fun ω' => opNorm (dynSumErr p S t ω')) ω := by
        rw [e4]
        exact Set.indicator_of_mem hω _
      rw [← e4']
      exact e5 hω
    have hnn1 := freezing_opNorm_nonneg (rOut S.C)
    have hnn2 := freezing_opNorm_nonneg (rIn S.C)
    have hnn3 := freezing_opNorm_nonneg (Muon.Foundations.condExpMat (dynPast S t) P (dynSumErr p S t) ω)
    calc _ ≤ opNorm (rOut S.C * Muon.Foundations.condExpMat (dynPast S t) P (dynSumErr p S t) ω) *
          opNorm (rIn S.C) := freezing_opNorm_mul _ _
      _ ≤ (opNorm (rOut S.C) * opNorm (Muon.Foundations.condExpMat (dynPast S t) P (dynSumErr p S t) ω)) *
          opNorm (rIn S.C) :=
          mul_le_mul_of_nonneg_right (freezing_opNorm_mul _ _) hnn2
      _ ≤ (opNorm (rOut S.C) * R ω) * opNorm (rIn S.C) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcE hnn1) hnn2
      _ = _ := by ring

end fzbcore

/-! ## The conditional drift of a block (persistence of diffuseness) -/

/-- Coordinator bridge (no source label), snapshot `cr-2026-10-23`. The drift display of the proof of
`lem:app-dyn-diffuse`, uniform over all times `t`: on `{Δ_t ∈ 𝒦}`,
`‖Σ_out^{1/2} 𝔼_t[∑_{r<L} 𝖲_{t+r}] Σ_in^{1/2}‖ ≤ CL(‖Σ_out^{1/2}Δ_tΣ_in^{1/2}‖ + r_B) + C(‖M°_{t-1}‖ + log(2B) + L² log(2B)/√B)`,
with `r_B → 0` chosen before the time `t` and the sample point. The source writes it for
`Y_{b+1} − Y_b = −λΣ_out^{1/2}(∑_{r<L}𝖲_{t+r})Σ_in^{1/2}` at a block start `t = t_b`, `b < b_c` (so `Δ_t ∈ 𝒜`,
`𝒦 = 𝒜` is the consumer's choice), after factoring out `λ = h/B`.
Source, `section.tex` ll. 2070–2080 (proof of `lem:app-dyn-diffuse`), verbatim:
```latex
and $\mathcal E=\sum_{r<L}{\mathsf S}_{t+r}-\sum_{r<L}V_r$ as before. Then
$Y_{b+1}-Y_b=-\lr\Sigmaout^{1/2}\big(\sum_{r<L}{\mathsf S}_{t+r}\big)\Sigmain^{1/2}$ and
\[
\EE_t\big[Y_{b+1}-Y_b\big]=-\lr\Sigmaout^{1/2}\big(L\overline V(D)+\EE_t\mathcal E\big)\Sigmain^{1/2}.
\]

\emph{The drift.} By \cref{eqn:app-dyn-mean-physical} and
\cref{lem:app-dyn-coupling}(iv),
\[
\norm{\EE_t[Y_{b+1}-Y_b]}\le C\lr L\big(\norm{Y_b}+r_B\big)+C\lr\big(\norm m+\log(2B)+L^2\log(2B)/\sqrt B\big).
\]
```
Each step: `∑_{r<L}𝖲_{t+r} = dynStatSum + dynSumErr` (definitions); `𝔼_t[dynStatSum] = ∑_{r<L} V̄_r(Δ_t)` by
`stationary_freezing_condExp` with `Φ(D, x) = 𝟙_𝒦(D)(∑_{r<L} x_r)_{ij}` (bounded: `‖Q‖ ≤ 1`), the source's
`L V̄(D)` (stationarity, `lem:app-dyn-chains`(i)); `‖Σ_out^{1/2}V̄_r(D)Σ_in^{1/2}‖ ≤ K‖Σ_out^{1/2}DΣ_in^{1/2}‖ + Kr_B`
by `mean_physical_uniform` (here the uniformity in `D` and `t` is used); `‖𝔼_t 𝓔‖ ≤ 𝔼_t‖𝓔‖` by
`opNorm_condExpMat_le`, bounded by `lem_app_dyn_coupling_iv`; `‖Σ^{1/2}‖ ≤ √C_Σ` (`DynSetup.size`).
Constants: `B₀, K` depend on `p` and `𝒦 = 𝒦(r₋, r₊, E)` only; `r` on `p` and the model sequence. The regime
hypothesis is (H1) along the sequence (as in `lem_app_dyn_diffuse`). The integrability of the block sum of
updates (bounded entries) is a conjunct. -/
theorem cond_block_drift (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) (rlo rhi E : ℝ)
    (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ B0 : ℕ, ∃ K : ℝ, ∀ (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
      (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
      (m n B : ℕ → ℕ) (S : ∀ k, DynSetup p (P k) (m k) (n k) (B k)),
      ProportionalRegime m n B (fun k => (S k).C) →
      ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ k : ℕ, B0 ≤ B k → ∀ t : ℕ,
        (∀ (i : Fin (m k)) (j : Fin (n k)), Integrable (fun ω =>
          (∑ u ∈ Finset.range (blockLen (B k)), dynUpd (S k) (t + u) ω) i j) (P k)) ∧
        ∀ᵐ ω ∂(P k), ω ∈ dynInK (S k) t (rlo, rhi, E) →
          opNorm (rOut (S k).C * Muon.Foundations.condExpMat (dynPast (S k) t) (P k)
              (fun ω' => ∑ u ∈ Finset.range (blockLen (B k)), dynUpd (S k) (t + u) ω') ω * rIn (S k).C) ≤
            K * (blockLen (B k) : ℝ) *
                (opNorm (rOut (S k).C * dynDelta (S k) t ω * rIn (S k).C) + r k) +
              K * (opNorm (dynBuf (S k) t ω) + Real.log (2 * (B k : ℝ)) +
                (blockLen (B k) : ℝ) ^ 2 * Real.log (2 * (B k : ℝ)) / Real.sqrt (B k : ℝ)) := by
  classical
  obtain ⟨K1, hK1⟩ := mean_physical_uniform p.γstar p.CSig p.ϱ rlo rhi hrlo hle
  obtain ⟨B0, K2, hK2⟩ := lem_app_dyn_coupling_iv certOp p rlo rhi E hrlo hle
  refine ⟨max B0 1, max |K1| (p.CSig * |K2|), ?_⟩
  intro Ω _ P _ m n B S hreg
  obtain ⟨r, hr, hrb⟩ := hK1 p rfl rfl rfl m n B Ω P (fun k => (S k).C) (fun k => (S k).cs)
    (fun k => (S k).size.1) (fun k => (S k).size.2.1) (fun k => (S k).size.2.2) hreg
  refine ⟨fun k => |r k|, by simpa using hr.abs, ?_⟩
  intro k hk t
  have hB0 : B0 ≤ B k := (le_max_left _ _).trans hk
  have hB1 : 1 ≤ B k := (le_max_right _ _).trans hk
  obtain ⟨_, hcoup⟩ := hK2 (Ω k) (P k) (m k) (n k) (B k) (S k) hB0 t
  refine ⟨fun i j => Integrable.of_bound (fzb_X_entry_meas (S k) t i j).aestronglyMeasurable
    ((blockLen (B k) : ℝ) * ((m k : ℝ) + 1))
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using fzb_X_entry_bound (S k) t ω i j), ?_⟩
  set Kc : ℝ := max |K1| (p.CSig * |K2|) with hKc
  set L : ℝ := (blockLen (B k) : ℝ) with hL
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (2 * (B k : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ B k := by exact_mod_cast hB1
    linarith
  have hρ : 0 ≤ |r k| := abs_nonneg _
  have hmean : ∀ (j : ℕ) (D : Mat (m k) (n k)), rlo ≤ riskSigma (S k).C D → riskSigma (S k).C D ≤ rhi →
      opNorm (rOut (S k).C * mean (P k) (fun ω => stationaryV p (S k).C (S k).cs t D j ω) * rIn (S k).C) ≤
        |K1| * opNorm (rOut (S k).C * D * rIn (S k).C) + |K1| * |r k| := by
    intro j D hlo hhi
    have h := (hrb k t j D hlo hhi).2
    have ha := freezing_opNorm_nonneg (rOut (S k).C * D * rIn (S k).C)
    refine h.trans (add_le_add (mul_le_mul_of_nonneg_right (le_abs_self _) ha) ?_)
    calc K1 * r k ≤ |K1 * r k| := le_abs_self _
      _ = |K1| * |r k| := abs_mul _ _
  have hpw := fzb_drift_pw (S k) t rlo rhi E |K1| |r k|
    (fun ω => K2 * (opNorm (dynBuf (S k) t ω) + Real.log (2 * (B k : ℝ))) +
      K2 * (blockLen (B k) : ℝ) ^ 2 * Real.log (2 * (B k : ℝ)) / Real.sqrt (B k : ℝ)) hmean hcoup
  have hprod := fzb_root_prod_le (S k).C p.CSig (zero_le_one.trans p.hC) (S k).size.2.1 (S k).size.2.2
  filter_upwards [hpw] with ω hω hωK
  have h := hω hωK
  have ha := freezing_opNorm_nonneg (rOut (S k).C * dynDelta (S k) t ω * rIn (S k).C)
  have hbuf := freezing_opNorm_nonneg (dynBuf (S k) t ω)
  have hnn := mul_nonneg (freezing_opNorm_nonneg (rOut (S k).C)) (freezing_opNorm_nonneg (rIn (S k).C))
  set a := opNorm (rOut (S k).C * dynDelta (S k) t ω * rIn (S k).C) with ha_def
  set bf := opNorm (dynBuf (S k) t ω) with hbf_def
  set lg := Real.log (2 * (B k : ℝ)) with hlg
  set q := L ^ 2 * lg / Real.sqrt (B k : ℝ) with hq
  have hq0 : 0 ≤ q := by
    rw [hq]
    exact div_nonneg (mul_nonneg (sq_nonneg _) hlog) (Real.sqrt_nonneg _)
  have hy : 0 ≤ bf + lg + q := by linarith
  have h1 : L * (|K1| * a + |K1| * |r k|) ≤ Kc * L * (a + |r k|) := by
    have hK : |K1| ≤ Kc := le_max_left _ _
    calc L * (|K1| * a + |K1| * |r k|) = |K1| * (L * (a + |r k|)) := by ring
      _ ≤ Kc * (L * (a + |r k|)) :=
          mul_le_mul_of_nonneg_right hK (mul_nonneg hL0 (add_nonneg ha hρ))
      _ = _ := by ring
  have hR : K2 * (bf + lg) + K2 * L ^ 2 * lg / Real.sqrt (B k : ℝ) ≤ |K2| * (bf + lg + q) := by
    have e : K2 * L ^ 2 * lg / Real.sqrt (B k : ℝ) = K2 * q := by
      rw [hq]; ring
    rw [e]
    calc K2 * (bf + lg) + K2 * q = K2 * (bf + lg + q) := by ring
      _ ≤ |K2| * (bf + lg + q) := mul_le_mul_of_nonneg_right (le_abs_self _) hy
  have h2 : opNorm (rOut (S k).C) * opNorm (rIn (S k).C) *
      (K2 * (bf + lg) + K2 * L ^ 2 * lg / Real.sqrt (B k : ℝ)) ≤ Kc * (bf + lg + q) := by
    calc _ ≤ opNorm (rOut (S k).C) * opNorm (rIn (S k).C) * (|K2| * (bf + lg + q)) :=
          mul_le_mul_of_nonneg_left hR hnn
      _ ≤ p.CSig * (|K2| * (bf + lg + q)) :=
          mul_le_mul_of_nonneg_right hprod (mul_nonneg (abs_nonneg _) hy)
      _ ≤ Kc * (bf + lg + q) := by
          have hK : p.CSig * |K2| ≤ Kc := le_max_right _ _
          calc p.CSig * (|K2| * (bf + lg + q)) = (p.CSig * |K2|) * (bf + lg + q) := by ring
            _ ≤ Kc * (bf + lg + q) := mul_le_mul_of_nonneg_right hK hy
  calc _ ≤ _ := h
    _ ≤ Kc * L * (a + |r k|) + Kc * (bf + lg + q) := add_le_add h1 h2

/-! ## Conditional projection variance (block martingale) -/

/-! ## Path-law transfer from `DynHyp` to `DynSetup` -/

private lemma pathLaw_risk_cont {m n : ℕ} (C : Covariances m n) :
    Continuous (fun D : Mat m n => riskSigma C D) := by
  unfold riskSigma pairSigma
  fun_prop

private lemma pathLaw_mat_meas {Ω : Type*} {σ : MeasurableSpace Ω} {m n : ℕ}
    {F : Ω → Mat m n} (h : ∀ i j, Measurable[σ] fun ω => F ω i j) : Measurable[σ] F :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => h i j

private lemma pathLaw_entry_meas {Ω : Type*} {σ : MeasurableSpace Ω} {m n : ℕ}
    {F : Ω → Mat m n} (hF : Measurable[σ] F) (i : Fin m) (j : Fin n) :
    Measurable[σ] fun ω => F ω i j :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hF)

private lemma pathLaw_grad_meas {Ω : Type*} {σ : MeasurableSpace Ω} {B m n : ℕ}
    {D : Ω → Mat m n} {b : Ω → Batch m n B} (hD : Measurable[σ] D)
    (hb : Measurable[σ] b) : Measurable[σ] (fun ω => grad (D ω) (b ω)) := by
  have hc : Continuous (fun z : Mat m n × Batch m n B => grad z.1 z.2) := by
    unfold grad resid outer
    fun_prop
  exact Measurable.comp (g := fun z : Mat m n × Batch m n B => grad z.1 z.2)
    (f := fun ω => (D ω, b ω)) hc.measurable (hD.prodMk hb)

private lemma pathLaw_stepUpdate_meas {Ω : Type*} {σ : MeasurableSpace Ω} {B m n : ℕ}
    (C : Covariances m n) (p : AlgParams m n) (s : Ω → AlgState m n)
    (b : Ω → Batch m n B) (hW : Measurable[σ] (fun ω => (s ω).W))
    (hM : Measurable[σ] (fun ω => (s ω).Mprev)) (hb : Measurable[σ] b) :
    Measurable[σ] (fun ω => stepUpdate C p (s ω) (b ω)) ∧
      Measurable[σ] (fun ω => stepBuffer p (s ω) (b ω)) := by
  have hD : Measurable[σ] (fun ω => errorOf p (s ω)) :=
    (continuous_id.sub continuous_const).measurable.comp hW
  have hR : Measurable[σ] (fun ω => riskSigma C (errorOf p (s ω))) :=
    (pathLaw_risk_cont C).measurable.comp hD
  have hset : MeasurableSet[σ] {ω | riskSigma C (errorOf p (s ω)) = 0} :=
    hR (measurableSet_singleton 0)
  have hF : Measurable[σ] (fun ω => grad (errorOf p (s ω)) (b ω)) :=
    pathLaw_grad_meas hD hb
  have hbuf : Measurable[σ] (fun ω => stepBuffer p (s ω) (b ω)) := by
    apply pathLaw_mat_meas
    intro i j
    simp only [stepBuffer, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact ((pathLaw_entry_meas hM i j).const_mul _).add
      ((pathLaw_entry_meas hF i j).const_mul _)
  refine ⟨Measurable.ite hset measurable_const ?_, hbuf⟩
  have hnn : ∀ ω, (0 : ℝ) ≤ 2 * riskSigma C (errorOf p (s ω)) * p.ϱ := fun ω =>
    mul_nonneg (mul_nonneg (by norm_num) (freezing_risk_nonneg C _)) p.hϱ.le
  have hρ : Measurable[σ]
      (fun ω => (⟨2 * riskSigma C (errorOf p (s ω)) * p.ϱ, hnn ω⟩ : Set.Ici (0 : ℝ))) :=
    ((hR.const_mul 2).mul_const p.ϱ).subtype_mk
  exact measurable_Q.comp (hρ.prodMk hbuf)

private lemma pathLaw_step_meas {Ω : Type*} {σ : MeasurableSpace Ω} {B m n : ℕ}
    (C : Covariances m n) (p : AlgParams m n) (t : ℕ) (s : Ω → AlgState m n)
    (b : Ω → Batch m n B) (hW : Measurable[σ] (fun ω => (s ω).W))
    (hM : Measurable[σ] (fun ω => (s ω).Mprev)) (hb : Measurable[σ] b) :
    Measurable[σ] (fun ω => (step C p t (s ω) (b ω)).W) ∧
      Measurable[σ] (fun ω => (step C p t (s ω) (b ω)).Mprev) := by
  obtain ⟨hU, hbuf⟩ := pathLaw_stepUpdate_meas C p s b hW hM hb
  refine ⟨?_, hbuf⟩
  apply pathLaw_mat_meas
  intro i j
  simp only [step, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact (pathLaw_entry_meas hW i j).sub ((pathLaw_entry_meas hU i j).const_mul _)

private lemma pathLaw_run_aem {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (C : Covariances m n) (p : AlgParams m n) (W0 : Mat m n)
    (M : Ω → Mat m n) (hM : AEMeasurable M P) (x : ℕ → Ω → Batch m n B)
    (hx : ∀ u a, AEMeasurable (fun ω => x u ω a) P) (t : ℕ) :
    AEMeasurable (fun ω => (run C p (initState W0 (M ω)) (fun u => x u ω) t).W) P := by
  classical
  let xm : ℕ → Ω → Batch m n B := fun u ω a => (hx u a).mk _ ω
  let Mm : Ω → Mat m n := hM.mk M
  have hxm : ∀ u, Measurable (xm u) := fun u =>
    measurable_pi_iff.mpr fun a => (hx u a).measurable_mk
  have hmeas : Measurable
      (fun ω => (run C p (initState W0 (Mm ω)) (fun u => xm u ω) t).W) ∧
      Measurable (fun ω => (run C p (initState W0 (Mm ω)) (fun u => xm u ω) t).Mprev) := by
    induction t with
    | zero => exact ⟨measurable_const, hM.measurable_mk⟩
    | succ t ih =>
      exact pathLaw_step_meas C p t
        (fun ω => run C p (initState W0 (Mm ω)) (fun u => xm u ω) t) (xm t)
        ih.1 ih.2 (hxm t)
  have hxeq : ∀ᵐ ω ∂P, ∀ u, x u ω = xm u ω := by
    refine ae_all_iff.2 fun u => ?_
    have ha : ∀ᵐ ω ∂P, ∀ a, x u ω a = xm u ω a := ae_all_iff.2 fun a => (hx u a).ae_eq_mk
    exact ha.mono fun _ h => funext fun a => h a
  have hrun : (fun ω => (run C p (initState W0 (M ω)) (fun u => x u ω) t).W) =ᵐ[P]
      (fun ω => (run C p (initState W0 (Mm ω)) (fun u => xm u ω) t).W) := by
    filter_upwards [hxeq, hM.ae_eq_mk] with ω hxω hMω
    rw [show (fun u => x u ω) = (fun u => xm u ω) from funext hxω, hMω]
  exact hmeas.1.aemeasurable.congr hrun.symm

private lemma pathLaw_dev_aem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ → ℕ} {C : ∀ k, Covariances (m k) (n k)} {p : DynParams}
    (H : DynHyp p P m n B C) (k t : ℕ) :
    AEMeasurable
      (devRand (C k) (H.alg k) (fun ω => initState (H.W0 k) (H.Mm1 k ω)) (H.x k) t) P := by
  have hrun := pathLaw_run_aem (C k) (H.alg k) (H.W0 k) (H.Mm1 k) (H.Mm1_meas k)
    (H.x k) (fun u a => (H.iid k u).meas a) t
  exact (continuous_id.sub continuous_const).measurable.comp_aemeasurable hrun

private lemma pathLaw_prob {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams}
    {m n B : ℕ → ℕ} {C : ∀ k, Covariances (m k) (n k)} (H : DynHyp p P m n B C) :
    IsProbabilityMeasure P := by
  have hev : ∀ᶠ k in atTop, 1 ≤ B k := H.regime.B_top.eventually (eventually_ge_atTop 1)
  obtain ⟨k, hk⟩ := hev.exists
  let a : Fin (B k) := ⟨0, hk⟩
  refine IsProbabilityMeasure.mk ?_
  have hlaw := (H.iid k 0).law a
  have hm := Measure.map_apply_of_aemeasurable ((H.iid k 0).meas a) MeasurableSet.univ
  rw [hlaw] at hm
  haveI : IsProbabilityMeasure (dataTarget (C k)) := by unfold dataTarget; infer_instance
  simpa only [Set.preimage_univ, IsProbabilityMeasure.measure_univ] using hm.symm

/-- Coordinator bridge (no source label), snapshot `cr-2026-10-23`. Strengthened form of the frozen bridge
`DynHyp.exists_dynSetup` (Transport): at each dimension `k` there is a sample-level `DynSetup` on a probability
space `(Ω', P')`, with the covariances, algorithm and initial parameter of `H`, whose error path
`(Δ_t)_{t ≥ 0} = (dynDelta S t)_t` has the law of the `DynHyp` error path
`(errPath H k t)_t = (devRand (C k) (H.alg k) (initState (H.W0 k) (H.Mm1 k)) (H.x k) t)_t` on the measurable
sets of paths. This is what transfers the sample-level `lem_app_dyn_diffuse` to the law-level framework of
`thm:app-dyn-main`(iv) (`section.tex` ll. 2339–2340: "Part (iv) is \cref{lem:app-dyn-diffuse} with
$T=T_\star+1$ on the event $\{t_{b_c}>BT_\star+L\}$") and of `lem:app-dyn-block` (l. 2197, "By
\cref{lem:app-dyn-diffuse} with $T+1$ in place of $T$"): the event of `lem_app_dyn_diffuse` is the preimage of
a measurable set of paths (the exit index `b_c` and the diffuseness `δ` are measurable functions of the path).
Proof route: the projection `pi` of `DynHyp.exists_dynSetup` with `S.M0 =ᵐ H.Mm1 k ∘ pi` and
`dynBatch S u =ᵐ H.x k u ∘ pi` (countably many `u`) gives `dynDelta S t =ᵐ (errPath H k t) ∘ pi` for all `t`
simultaneously (`devRand` is pointwise in the initial state and the batches); the `DynHyp` path map is
`AEMeasurable` (`devRand` is measurable in the initial state and the batches, `H.Mm1 k` and `H.x k u` are
`AEMeasurable`), so the preimage of a measurable set is null-measurable and `MeasurePreserving.measure_preimage`
applies. `P'` is a probability measure because `pi` is measure preserving onto the probability measure `P`
(`DynHyp` forces `P` to be a probability measure through `H.iid`). -/
theorem DynHyp.exists_dynSetup_pathLaw {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams}
    {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)} (H : DynHyp p P m n B C) (k : ℕ) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (P' : Measure Ω') (S : DynSetup p P' (m k) (n k) (B k)),
      IsProbabilityMeasure P' ∧ S.C = C k ∧ S.alg = H.alg k ∧ S.W0 = H.W0 k ∧
      ∀ A : Set (ℕ → Mat (m k) (n k)), MeasurableSet A →
        P {ω | (fun t => devRand (C k) (H.alg k) (fun ω₀ => initState (H.W0 k) (H.Mm1 k ω₀)) (H.x k) t ω) ∈ A} =
          P' {ω' | (fun t => dynDelta S t ω') ∈ A} := by
  obtain ⟨Ω', mΩ', P', pi, S, hpi, hC, hAlg, hW, hM, hx⟩ := H.exists_dynSetup k
  refine ⟨Ω', mΩ', P', S, ?_, hC, hAlg, hW, ?_⟩
  · letI : IsProbabilityMeasure P := pathLaw_prob H
    refine IsProbabilityMeasure.mk ?_
    simpa only [Set.preimage_univ, IsProbabilityMeasure.measure_univ] using
      hpi.measure_preimage MeasurableSet.univ.nullMeasurableSet
  · intro A hA
    let γ : ℕ → Ω → Mat (m k) (n k) := fun t =>
      devRand (C k) (H.alg k) (fun ω => initState (H.W0 k) (H.Mm1 k ω)) (H.x k) t
    have hγ : ∀ t, AEMeasurable (γ t) P := fun t => pathLaw_dev_aem H k t
    have hγpath : AEMeasurable (fun ω t => γ t ω) P := AEMeasurable.of_eval hγ
    have hnull : NullMeasurableSet {ω | (fun t => γ t ω) ∈ A} P := by
      exact hγpath.nullMeasurable hA
    have hxeq : ∀ᵐ ω' ∂P', ∀ t, dynDelta S t ω' = γ t (pi ω') := by
      have hx' : ∀ᵐ ω' ∂P', ∀ t, dynBatch S t ω' = H.x k t (pi ω') := ae_all_iff.2 hx
      filter_upwards [hx', hM] with ω' hxω hMω t
      have hb : (fun u => dynBatch S u ω') = (fun u => H.x k u (pi ω')) := funext hxω
      simp only [dynDelta, devRand, runRand, dynStart, γ, hb, hMω, Function.comp_apply]
      rw [hC, hAlg, hW]
    rw [← hpi.measure_preimage hnull]
    refine measure_congr ?_
    filter_upwards [hxeq] with ω' hω
    have hp : (fun t => dynDelta S t ω') = fun t => γ t (pi ω') := funext hω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hp]

end Muon.Dynamics

end

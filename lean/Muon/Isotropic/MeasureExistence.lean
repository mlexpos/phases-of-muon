import Muon.Isotropic.Measure
import SpectralFoundations
import Muon.DetEquiv.Trace
import Muon.DetEquiv.BranchStability
import Muon.DetEquiv.SampleModel
import Muon.Setup.Regime
import Muon.Setup.Frozen
import Muon.Isotropic.Closure
import Muon.Volatility.Replication
import Muon.Volatility.OddSpectral
import Muon.Drift.Targets

/-!
# Appendix F: existence of the isotropic measure pair

Task L-F.7 (interface). Snapshot `cr-2026-10-23`. Source: `sections/05b-isotropic/section.tex`,
`prop:app-iso-measure` (l.948–951 statement; l.953–992 proof). Uniqueness is
`prop_app_iso_measure_unique` of `Muon.Isotropic.Measure` (L-F.6) and is reused, not restated.

Declarations of record:
* `prop_app_iso_measure_exists`: the existence half of the source statement.
* `prop_app_iso_measure`: the source statement as an `ExistsUnique` record over pairs
  `(𝔪_out, 𝔪_in)`, built from the existence half and the uniqueness half.

Interface choices (faithfulness notes):
* The standing hypotheses `0 < γin`, `0 < γout` of the source ("for every `γin>0` and `γout>0`") are
  explicit hypotheses; no other hypothesis is added. The cited inputs of the proof (B
  `cor:app-de-trace`, `thm:app-de-branch`(ii), A `lem:app-setup-gaussian-moments`,
  `assum:app-setup-regime`, Prokhorov) are
  proof-side only and do not appear in the statements.
* The pair is `Prod`-valued in the `ExistsUnique` record, `p.1 = 𝔪_out`, `p.2 = 𝔪_in`, matching the
  argument order of `IsIsoMeasurePair`.
* Every theorem is a statement with proof `sorry`, except `prop_app_iso_measure`, whose proof is the
  one-line assembly of the two halves.
-/

open MeasureTheory Filter Set
open ProbabilityTheory Topology

noncomputable section

namespace Muon.Isotropic

/-! ### Proof of `prop_app_iso_measure_exists` (P-F.7.P1)

Private helpers, moved verbatim from the staging package `muon-glue` (`MuonGlue/IsoMeasureExistence.lean`) at final integration; the route is documented there.
Measure theory (Stieltjes inversion, expected eigenvalue measures) comes from `SpectralFoundations`. -/

section MeasureExistenceProof

open SpectralFoundations
open scoped Matrix

private def isoFiniteMeasure (γ : ℝ) : FiniteMeasure ℝ :=
  ⟨isoSpecMeasure γ, by
    unfold isoSpecMeasure
    exact (Measure.dirac (1 : ℝ)).smul_finite ENNReal.ofReal_ne_top⟩

private def identityCovariances (m n : ℕ) : Muon.Covariances m n where
  Sout := 1
  Sin := 1
  psdOut := Matrix.PosSemidef.one
  psdIn := Matrix.PosSemidef.one

private def identitySpectralData (m n : ℕ) :
    Muon.Setup.SpectralData (identityCovariances m n) where
  uOut := 1
  vIn := 1
  μ := fun _ => 1
  lam := fun _ => 1
  huOut := by simp
  hvIn := by simp
  eigOut := by intro i; ext j; simp [identityCovariances]
  eigIn := by intro i; ext j; simp [identityCovariances]

private lemma ceil_ratio_tendsto {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun k : ℕ => (⌈γ * (k + 1 : ℕ)⌉₊ : ℝ) / (k + 1 : ℕ))
      atTop (𝓝 γ) := by
  have hden : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  have herr : Tendsto
      (fun k : ℕ => ((⌈γ * (k + 1 : ℕ)⌉₊ : ℝ) - γ * (k + 1 : ℕ)) /
        (k + 1 : ℕ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => div_nonneg
      (sub_nonneg.mpr (Nat.le_ceil _)) (by positivity)) (fun k => ?_) hinv
    have hlo : γ * ((k + 1 : ℕ) : ℝ) ≤ (⌈γ * (k + 1 : ℕ)⌉₊ : ℝ) := Nat.le_ceil _
    have hhi : (⌈γ * (k + 1 : ℕ)⌉₊ : ℝ) < γ * (k + 1 : ℕ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    rw [div_le_iff₀ (by positivity)]
    rw [inv_mul_cancel₀ (by positivity : (((k + 1 : ℕ) : ℝ)) ≠ 0)]
    linarith
  have hadd := herr.add_const γ
  convert hadd using 1
  funext k
  have hk : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp
  ring
  simp

private structure OrderedRegime (γin γout : ℝ) where
  R : Muon.Setup.SetupRegime
  gamma_in : R.prop.γin = γin
  gamma_out : R.prop.γout = γout
  isotropic : ∀ k, (R.F k).C.Sin = 1 ∧ (R.F k).C.Sout = 1

private lemma opNorm_one_le (d : ℕ) :
    Muon.opNorm (1 : Muon.Mat d d) ≤ 1 := by
  unfold Muon.opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp [Matrix.toEuclideanLin]

private lemma regime_specOut_tendsto {γin γout : ℝ} (D : OrderedRegime γin γout) :
    Tendsto (fun k => Muon.Drift.specOutFM (D.R.F k)) atTop
      (𝓝 (isoFiniteMeasure γout)) := by
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hr := D.R.prop.ratio_out
  rw [D.gamma_out] at hr
  have hscaled := hr.mul_const (f (1 : ℝ))
  have hγ : 0 ≤ γout := by rw [← D.gamma_out]; exact D.R.prop.γout_pos.le
  have htarget : ∫ x, f x ∂(isoFiniteMeasure γout : Measure ℝ) = γout * f 1 := by
    simp [isoFiniteMeasure, isoSpecMeasure, hγ]
  rw [htarget]
  refine hscaled.congr fun k => ?_
  rw [show ((Muon.Drift.specOutFM (D.R.F k) : FiniteMeasure ℝ) : Measure ℝ) =
      Muon.nuOut (D.R.F k).C (D.R.B k) from rfl]
  rw [← Muon.trace_cfc_eq_integral_nuOut (D.R.F k).C (D.R.F k).hB f]
  rw [(D.isotropic k).2]
  simp [Matrix.trace, Matrix.diag, Algebra.algebraMap_eq_smul_one, div_eq_inv_mul]
  ring

private lemma regime_specIn_tendsto {γin γout : ℝ} (D : OrderedRegime γin γout) :
    Tendsto (fun k => Muon.Drift.specInFM (D.R.F k)) atTop
      (𝓝 (isoFiniteMeasure γin)) := by
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hr := D.R.prop.ratio_in
  rw [D.gamma_in] at hr
  have hscaled := hr.mul_const (f (1 : ℝ))
  have hγ : 0 ≤ γin := by rw [← D.gamma_in]; exact D.R.prop.γin_pos.le
  have htarget : ∫ x, f x ∂(isoFiniteMeasure γin : Measure ℝ) = γin * f 1 := by
    simp [isoFiniteMeasure, isoSpecMeasure, hγ]
  rw [htarget]
  refine hscaled.congr fun k => ?_
  rw [show ((Muon.Drift.specInFM (D.R.F k) : FiniteMeasure ℝ) : Measure ℝ) =
      Muon.nuIn (D.R.F k).C (D.R.B k) from rfl]
  rw [← Muon.trace_cfc_eq_integral_nuIn (D.R.F k).C (D.R.F k).hB f]
  rw [(D.isotropic k).1]
  simp [Matrix.trace, Matrix.diag, Algebra.algebraMap_eq_smul_one, div_eq_inv_mul]
  ring

private lemma weightedBuf_zero_measurable_early {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B)
    (S : Muon.Setup.FrozenSamples P m n B) :
    Measurable (Muon.DetEquiv.WeightedBuf (Muon.emaW 0) F S 0) := by
  have hb : ∀ s : ℤ, Measurable (Muon.Setup.frozenBatchG F S s) := by
    intro s
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
    simp only [Muon.Setup.frozenBatchG, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    refine (Finset.measurable_sum _ fun a _ => ?_).const_mul _
    have hdot : Measurable (fun ω =>
        dotProduct (S.zw s a ω).1 (Matrix.mulVec F.A (S.zw s a ω).2)) := by
      simp only [dotProduct, Matrix.mulVec]
      exact Finset.measurable_sum _ fun p _ => ((measurable_pi_apply p).comp
        (measurable_fst.comp (S.meas s a))).mul
          (Finset.measurable_sum _ fun q _ => measurable_const.mul
            ((measurable_pi_apply q).comp (measurable_snd.comp (S.meas s a))))
    have houter : Measurable (fun ω =>
        (Muon.Setup.rOut F.C * Muon.outer (S.zw s a ω).1 (S.zw s a ω).2 *
          Muon.Setup.rIn F.C) i k) := by
      simp only [Matrix.mul_apply, Muon.outer, Matrix.vecMulVec_apply]
      exact Finset.measurable_sum _ fun q _ =>
        (Finset.measurable_sum _ fun p _ => measurable_const.mul
          (((measurable_pi_apply p).comp (measurable_fst.comp (S.meas s a))).mul
            ((measurable_pi_apply q).comp (measurable_snd.comp (S.meas s a))))).mul
              measurable_const
    exact hdot.mul houter
  letI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Muon.Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  letI : SecondCountableTopology (Muon.Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  letI : MeasurableAdd₂ (Muon.Mat m n) :=
    inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  unfold Muon.DetEquiv.WeightedBuf
  exact Measurable.tsum fun j => (hb (0 + 1 - (j : ℤ))).const_smul (Muon.emaW 0 j)

private lemma abs_entry_le_opNorm {p q : ℕ} (K : Muon.Mat p q) (i : Fin p) (j : Fin q) :
    |K i j| ≤ Muon.opNorm K := by
  have h1 := Matrix.l2_opNorm_mulVec K (EuclideanSpace.single j (1 : ℝ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin p) ℝ).symm
    (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i
  have h3 : ((EuclideanSpace.equiv (Fin p) ℝ).symm
      (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i = K i j := by
    simp
  simp only [PiLp.norm_single, norm_one, mul_one] at h1
  rw [h3, Real.norm_eq_abs] at h2
  rw [Muon.opNorm_eq_norm]
  linarith

private lemma matrix_inv_measurable {a : ℕ} :
    Measurable (fun X : Muon.Mat a a => X⁻¹) := by
  have hdet : Measurable (fun X : Muon.Mat a a => X.det) :=
    (continuous_id.matrix_det).measurable
  have hadj : Measurable (fun X : Muon.Mat a a => X.adjugate) :=
    (continuous_id.matrix_adjugate).measurable
  have hinv : (fun X : Muon.Mat a a => X⁻¹) =
      fun X => Ring.inverse X.det • X.adjugate :=
    funext fun X => Matrix.inv_def X
  have hscalar : Measurable (fun X : Muon.Mat a a => Ring.inverse X.det) := by
    simp only [Ring.inverse_eq_inv]
    exact hdet.inv
  rw [hinv]
  exact hscalar.smul hadj

private lemma resolvent_measurable {a b : ℕ} (s : ℝ) :
    Measurable (fun M : Muon.Mat a b => Muon.DetEquiv.Rs M s) := by
  have hc : Continuous (fun M : Muon.Mat a b =>
      M * Mᵀ + s • (1 : Muon.Mat a a)) := by fun_prop
  exact matrix_inv_measurable.comp hc.measurable

private lemma real_iSup_singleton (f : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ f x) :
    (⨆ s ∈ ({x} : Set ℝ), f s) = f x := by
  have hb : ∀ s : ℝ, (⨆ (_ : s ∈ ({x} : Set ℝ)), f s) ≤ f x := by
    intro s
    by_cases hs : s ∈ ({x} : Set ℝ)
    · rw [ciSup_pos hs]
      rcases hs with rfl
      exact le_rfl
    · rw [ciSup_neg hs]
      simpa only [Real.sSup_empty] using hx
  apply le_antisymm (ciSup_le hb)
  have h := le_ciSup (show BddAbove
      (Set.range (fun s : ℝ => ⨆ (_ : s ∈ ({x} : Set ℝ)), f s)) from
    ⟨f x, by rintro _ ⟨s, rfl⟩; exact hb s⟩) x
  simpa only [ciSup_pos (Set.mem_singleton x)] using h

private lemma fro_sq_eq {m n : ℕ} (K : Muon.Mat m n) :
    Muon.fro K ^ 2 = ∑ i, ∑ j, K i j ^ 2 := by
  unfold Muon.fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma continuous_fro_sq {m n : ℕ} :
    Continuous (fun K : Muon.Mat m n => Muon.fro K ^ 2) := by
  simp_rw [fro_sq_eq]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (Continuous.matrix_elem continuous_id i j).pow 2

private lemma abs_entry_le_fro {m n : ℕ} (K : Muon.Mat m n) (i : Fin m) (j : Fin n) :
    |K i j| ≤ Muon.fro K := by
  unfold Muon.fro
  apply Real.abs_le_sqrt
  have h1 : ‖K i j‖ ^ 2 ≤ ∑ j', ‖K i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖K i j'‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖K i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖K i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖K i' j'‖ ^ 2)
      (fun i' _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have h3 : ‖K i j‖ ^ 2 = K i j ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  linarith

private lemma trace_mul_transpose_eq_fro_sq {m n : ℕ} (K : Muon.Mat m n) :
    Matrix.trace (K * Kᵀ) = Muon.fro K ^ 2 := by
  rw [fro_sq_eq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma uncentered_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n : ℕ}
    (Y : Ω → Muon.Mat m n) (hY : Measurable Y)
    (hint : Integrable (fun ω => Muon.fro (Y ω) ^ 2) P)
    (μ : Muon.Mat m n) (hmean : Muon.mean P Y = μ) (V : ℝ)
    (hcenter : ∫ ω, Muon.fro (Y ω - μ) ^ 2 ∂P = V) :
    ∫ ω, Muon.fro (Y ω) ^ 2 ∂P = Muon.fro μ ^ 2 + V := by
  have hent : ∀ i j, Integrable (fun ω => Y ω i j) P := by
    intro i j
    have hae : AEStronglyMeasurable (fun ω => Y ω i j) P :=
      ((Continuous.matrix_elem continuous_id i j).measurable.comp hY).aestronglyMeasurable
    refine (hint.add (integrable_const (1 : ℝ))).mono' hae
      (Filter.Eventually.of_forall fun ω => ?_)
    have h := abs_entry_le_fro (Y ω) i j
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    nlinarith [abs_nonneg (Y ω i j), sq_nonneg (Muon.fro (Y ω) - 1)]
  have hmu : ∀ i j, ∫ ω, Y ω i j ∂P = μ i j := by
    intro i j
    have h := congrFun (congrFun hmean i) j
    simpa [Muon.mean] using h
  have hpt : ∀ ω, Muon.fro (Y ω - μ) ^ 2 = Muon.fro (Y ω) ^ 2
      - 2 * ∑ i, ∑ j, μ i j * Y ω i j + Muon.fro μ ^ 2 := by
    intro ω
    rw [fro_sq_eq, fro_sq_eq, fro_sq_eq, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.sub_apply]
    ring
  have hI : ∀ i j, Integrable (fun ω => μ i j * Y ω i j) P :=
    fun i j => (hent i j).const_mul (μ i j)
  have hcrossI : Integrable (fun ω => ∑ i, ∑ j, μ i j * Y ω i j) P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j
  have hcross : ∫ ω, ∑ i, ∑ j, μ i j * Y ω i j ∂P = Muon.fro μ ^ 2 := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI i j)]
    rw [fro_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hI i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, hmu]
    ring
  have h := hcenter
  simp_rw [hpt] at h
  have e1 : Integrable (fun ω => 2 * ∑ i, ∑ j, μ i j * Y ω i j) P :=
    hcrossI.const_mul 2
  have e2 : Integrable (fun ω => Muon.fro (Y ω) ^ 2
      - 2 * ∑ i, ∑ j, μ i j * Y ω i j) P := hint.sub e1
  rw [integral_add e2 (integrable_const _), integral_sub hint e1, integral_const_mul,
    hcross, integral_const] at h
  simp only [probReal_univ, smul_eq_mul, one_mul] at h
  linarith

private lemma weightedBuf_zero_eq_batch {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B)
    (S : Muon.Setup.FrozenSamples P m n B) (ω : Ω) :
    Muon.DetEquiv.WeightedBuf (Muon.emaW 0) F S 0 ω =
      Muon.Setup.frozenBatchG F S 1 ω := by
  unfold Muon.DetEquiv.WeightedBuf
  rw [tsum_eq_single 0]
  · simp [Muon.emaW]
  · intro b hb
    simp [Muon.emaW, hb]

/-- The spectrally diffuse identity-covariance regime used in the approximation. -/
private lemma regime_exists {γin γout : ℝ} (hin : 0 < γin) (hout : 0 < γout)
    (hord : γout ≤ γin) : Nonempty (OrderedRegime γin γout) := by
  let mo : ℕ → ℕ := fun k => ⌈γout * (k + 1 : ℕ)⌉₊
  let ni : ℕ → ℕ := fun k => ⌈γin * (k + 1 : ℕ)⌉₊
  let m : ℕ → ℕ := fun k => 1 * mo k
  let n : ℕ → ℕ := fun k => 1 * ni k
  let B : ℕ → ℕ := fun k => k + 1
  have hmo : ∀ k, 0 < mo k := fun k => Nat.ceil_pos.mpr (by positivity)
  have hni : ∀ k, 0 < ni k := fun k => Nat.ceil_pos.mpr (by positivity)
  let A : ∀ k, Muon.Mat (m k) (n k) := fun k =>
    Muon.Volatility.replState (identityCovariances (mo k) (ni k))
      (identitySpectralData (mo k) (ni k)) 1
  have hA : ∀ k, Muon.fro (A k) = 1 := fun k => by
    simpa [A, m, n] using Muon.Volatility.def_app_vol_replication_vi
      (identityCovariances (mo k) (ni k)) (identitySpectralData (mo k) (ni k)) 1
      (hmo k) (hni k) Nat.one_pos
  let F : ∀ k, Muon.Setup.FrozenParams (m k) (n k) (B k) := fun k =>
    { C := identityCovariances (m k) (n k)
      A := A k
      hA := hA k
      β := 0
      hβ := ⟨le_rfl, zero_lt_one⟩
      hB := by simp [B] }
  have hBtop : Tendsto B atTop atTop := by
    simpa [B] using tendsto_add_atTop_nat 1
  have hratioOut : Tendsto (fun k => (m k : ℝ) / (B k : ℝ)) atTop (𝓝 γout) := by
    simpa [m, mo, B] using ceil_ratio_tendsto hout
  have hratioIn : Tendsto (fun k => (n k : ℝ) / (B k : ℝ)) atTop (𝓝 γin) := by
    simpa [n, ni, B] using ceil_ratio_tendsto hin
  let prop : Muon.ProportionalRegime m n B (fun k => (F k).C) :=
    { γin := γin
      γout := γout
      γin_pos := hin
      γout_pos := hout
      B_top := hBtop
      ratio_in := hratioIn
      ratio_out := hratioOut
      bdd := ⟨1, zero_lt_one, fun k => ⟨by
        simpa [F, identityCovariances] using opNorm_one_le (n k), by
        simpa [F, identityCovariances] using opNorm_one_le (m k)⟩⟩ }
  let γstar : ℝ := max γin γout + 2
  have hdims : ∀ k, ((max (m k) (n k) : ℕ) : ℝ) ≤ γstar * (B k : ℝ) := by
    intro k
    rw [Nat.cast_max]
    apply max_le
    · have hc := Nat.ceil_lt_add_one (show 0 ≤ γout * ((k + 1 : ℕ) : ℝ) by positivity)
      have hb0 : 0 ≤ (B k : ℝ) := by positivity
      have hb1 : 1 ≤ (B k : ℝ) := by simp [B]
      have hmax : γout ≤ max γin γout := hord.trans (le_max_left _ _)
      rw [show m k = mo k by simp [m]]
      calc
        (mo k : ℝ) ≤ γout * (B k : ℝ) + 1 := by simpa [mo, B] using hc.le
        _ ≤ max γin γout * (B k : ℝ) + 1 :=
          by simpa [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_right hmax hb0) 1
        _ ≤ max γin γout * (B k : ℝ) + 2 * (B k : ℝ) := by linarith
        _ = γstar * (B k : ℝ) := by dsimp [γstar]; ring
    · have hc := Nat.ceil_lt_add_one (show 0 ≤ γin * ((k + 1 : ℕ) : ℝ) by positivity)
      have hb0 : 0 ≤ (B k : ℝ) := by positivity
      have hb1 : 1 ≤ (B k : ℝ) := by simp [B]
      have hmax : γin ≤ max γin γout := le_max_left _ _
      rw [show n k = ni k by simp [n]]
      calc
        (ni k : ℝ) ≤ γin * (B k : ℝ) + 1 := by simpa [ni, B] using hc.le
        _ ≤ max γin γout * (B k : ℝ) + 1 :=
          by simpa [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_right hmax hb0) 1
        _ ≤ max γin γout * (B k : ℝ) + 2 * (B k : ℝ) := by linarith
        _ = γstar * (B k : ℝ) := by dsimp [γstar]; ring
  have hminTop : Tendsto (fun k => min (mo k) (ni k)) atTop atTop := by
    have hcast : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hoR : Tendsto (fun k => (mo k : ℝ)) atTop atTop :=
      tendsto_atTop_mono' atTop (Eventually.of_forall fun k => Nat.le_ceil _)
        (hcast.const_mul_atTop hout)
    have hiR : Tendsto (fun k => (ni k : ℝ)) atTop atTop :=
      tendsto_atTop_mono' atTop (Eventually.of_forall fun k => Nat.le_ceil _)
        (hcast.const_mul_atTop hin)
    have hoN : Tendsto mo atTop atTop := tendsto_natCast_atTop_iff.mp hoR
    have hiN : Tendsto ni atTop atTop := tendsto_natCast_atTop_iff.mp hiR
    refine tendsto_atTop.2 fun q => ?_
    filter_upwards [tendsto_atTop.1 hoN q, tendsto_atTop.1 hiN q] with k hk1 hk2
    exact le_min hk1 hk2
  have hdiffuse : Tendsto (fun k => Muon.opNorm (A k)) atTop (𝓝 0) := by
    have hminR : Tendsto (fun k => ((min (mo k) (ni k) : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hminTop
    have hlim := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hminR)
    refine hlim.congr fun k => ?_
    simpa [A, m, n] using (Muon.Volatility.def_app_vol_replication_vii
      (identityCovariances (mo k) (ni k)) (identitySpectralData (mo k) (ni k)) 1).symm
  let R : Muon.Setup.SetupRegime :=
    { m := m
      n := n
      B := B
      F := F
      prop := prop
      γstar := γstar
      CSig := 1
      hC := le_rfl
      dims := hdims
      normOut := fun k => by simpa [F, identityCovariances] using opNorm_one_le (m k)
      normIn := fun k => by simpa [F, identityCovariances] using opNorm_one_le (n k)
      β := 0
      hβ := fun _ => rfl
      ϱlo := 1
      ϱhi := 1
      hϱ := ⟨zero_lt_one, le_rfl⟩
      diffuse := by simpa [F] using hdiffuse }
  refine ⟨⟨R, ?_, ?_, ?_⟩⟩
  · rfl
  · rfl
  · intro k
    exact ⟨rfl, rfl⟩

/-- The canonical infinite product carries independent standard Gaussian sample pairs at every
time and batch slot. -/
private lemma samples_exist (R : Muon.Setup.SetupRegime) :
    let Ω : ℕ → Type := fun k => (ℤ × Fin (R.B k)) →
      Muon.Vec (R.m k) × Muon.Vec (R.n k)
    let P : ∀ k, Measure (Ω k) := fun k => Measure.infinitePi fun _ : ℤ × Fin (R.B k) =>
      (Muon.Foundations.stdGaussianPi (R.m k)).prod
        (Muon.Foundations.stdGaussianPi (R.n k))
    Nonempty (∀ k, Muon.Setup.FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) := by
  dsimp only
  exact ⟨fun k => (Muon.Setup.frozenSamples_nonempty (R.m k) (R.n k) (R.B k)).some⟩

/-- The output resolvent trace converges to the first coordinate of the limiting isotropic
branch.  This packages `cor_app_de_trace_iii`, conversion from mean square to convergence of
means, and continuity of `branchSol` in the two aspect ratios. -/
private lemma trace_limit_regime {γin γout : ℝ} (D : OrderedRegime γin γout)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, Muon.Setup.FrozenSamples (P k) (D.R.m k) (D.R.n k) (D.R.B k))
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun k => (D.R.B k : ℝ)⁻¹ * ∫ ω,
        Matrix.trace (Muon.DetEquiv.Rs
          (Muon.DetEquiv.WeightedBuf (Muon.emaW 0) (D.R.F k) (S k) 0 ω) t) ∂(P k))
      atTop (𝓝 ((Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0))
        (isoFiniteMeasure γout) (isoFiniteMeasure γin) t).1)) := by
  let νo : ℕ → FiniteMeasure ℝ := fun k => Muon.Drift.specOutFM (D.R.F k)
  let νi : ℕ → FiniteMeasure ℝ := fun k => Muon.Drift.specInFM (D.R.F k)
  have hw : Muon.DetEquiv.WeightClass (Muon.emaW 0) :=
    Muon.Drift.emaW_weightClass 0 ⟨le_rfl, zero_lt_one⟩
  have htargets := Muon.Drift.lem_app_drift_targets_i_weights D.R P S 0 {t}
    isCompact_singleton (Set.singleton_subset_iff.mpr ht) (Muon.emaW 0) hw
  have htheta := htargets.2
  have htheta_single : ∀ k, Muon.Drift.thetaB (Muon.emaW 0) (D.R.F k) (S k) 0
      (Muon.Drift.specOutFM (D.R.F k)) (Muon.Drift.specInFM (D.R.F k)) {t} =
      |Muon.DetEquiv.sigmaB (Muon.emaW 0) (D.R.F k) (S k) 0 t -
          (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0))
            (Muon.Drift.specOutFM (D.R.F k)) (Muon.Drift.specInFM (D.R.F k)) t).1| +
        |Muon.DetEquiv.sigmaTildeB (Muon.emaW 0) (D.R.F k) (S k) 0 t -
          (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0))
            (Muon.Drift.specOutFM (D.R.F k)) (Muon.Drift.specInFM (D.R.F k)) t).2.1| := by
    intro k
    unfold Muon.Drift.thetaB
    exact real_iSup_singleton _ t (by positivity)
  have hsum : Tendsto (fun k =>
      |Muon.DetEquiv.sigmaB (Muon.emaW 0) (D.R.F k) (S k) 0 t -
        (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0)) (νo k) (νi k) t).1| +
      |Muon.DetEquiv.sigmaTildeB (Muon.emaW 0) (D.R.F k) (S k) 0 t -
        (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0)) (νo k) (νi k) t).2.1|)
      atTop (𝓝 0) := by
    convert htheta using 1
    funext k
    simpa [νo, νi] using (htheta_single k).symm
  have habs : Tendsto (fun k =>
      |Muon.DetEquiv.sigmaB (Muon.emaW 0) (D.R.F k) (S k) 0 t -
        (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0)) (νo k) (νi k) t).1|)
      atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => abs_nonneg _) (fun k => ?_) hsum
    exact le_add_of_nonneg_right (abs_nonneg _)
  have hdiff : Tendsto (fun k =>
      Muon.DetEquiv.sigmaB (Muon.emaW 0) (D.R.F k) (S k) 0 t -
        (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0)) (νo k) (νi k) t).1)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using habs
  let γ : ℝ := max D.R.γstar 1
  have hC : 0 < D.R.CSig := lt_of_lt_of_le zero_lt_one D.R.hC
  have hγ : 0 < γ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hK : ∀ k, (νo k, νi k) ∈ Muon.DetEquiv.classK D.R.CSig γ := by
    intro k
    obtain ⟨o1, o2⟩ := Muon.Setup.assum_app_setup_regime_nuOut D.R k
    obtain ⟨i1, i2⟩ := Muon.Setup.assum_app_setup_regime_nuIn D.R k
    have hle : ENNReal.ofReal D.R.γstar ≤ ENNReal.ofReal γ :=
      ENNReal.ofReal_le_ofReal (le_max_left _ _)
    exact ⟨(measure_mono (Set.subset_univ _)).trans (o2.trans hle), o1,
      (measure_mono (Set.subset_univ _)).trans (i2.trans hle), i1⟩
  have hmeasOut : Tendsto νo atTop (𝓝 (isoFiniteMeasure γout)) := by
    simpa [νo] using regime_specOut_tendsto D
  have hmeasIn : Tendsto νi atTop (𝓝 (isoFiniteMeasure γin)) := by
    simpa [νi] using regime_specIn_tendsto D
  have hmeas : Tendsto (fun k => (νo k, νi k)) atTop
      (𝓝 (isoFiniteMeasure γout, isoFiniteMeasure γin)) := by
    simpa only [nhds_prod_eq] using hmeasOut.prodMk hmeasIn
  have hKlim : (isoFiniteMeasure γout, isoFiniteMeasure γin) ∈
      Muon.DetEquiv.classK D.R.CSig γ := by
    exact (Muon.DetEquiv.lem_app_de_compact_i hC hγ).isClosed.mem_of_tendsto hmeas
      (Eventually.of_forall hK)
  have hpair : Tendsto (fun k => (t, (νo k, νi k))) atTop
      (𝓝 (t, (isoFiniteMeasure γout, isoFiniteMeasure γin))) := by
    simpa only [nhds_prod_eq] using (tendsto_const_nhds.prodMk hmeas)
  have hbranchAll : Tendsto (fun k => Muon.DetEquiv.branchSol
      (Muon.DetEquiv.Fw (Muon.emaW 0)) (νo k) (νi k) t) atTop
      (𝓝 (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0))
        (isoFiniteMeasure γout) (isoFiniteMeasure γin) t)) := by
    have hc := (Muon.DetEquiv.thm_app_de_branch_ii
      (Muon.DetEquiv.Fw_admissible hw.1) hC hγ).1
      (t, (isoFiniteMeasure γout, isoFiniteMeasure γin)) ⟨ht, hKlim⟩
    have hwithin : Tendsto (fun k => (t, (νo k, νi k))) atTop
        (𝓝[Ioi 0 ×ˢ Muon.DetEquiv.classK D.R.CSig γ]
          (t, (isoFiniteMeasure γout, isoFiniteMeasure γin))) :=
      tendsto_nhdsWithin_iff.2 ⟨hpair,
        Eventually.of_forall fun k => ⟨ht, hK k⟩⟩
    exact Filter.Tendsto.comp hc hwithin
  have hbranch := (continuous_fst.tendsto _).comp hbranchAll
  have hsigma : Tendsto (fun k => Muon.DetEquiv.sigmaB (Muon.emaW 0)
      (D.R.F k) (S k) 0 t) atTop
      (𝓝 ((Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0))
        (isoFiniteMeasure γout) (isoFiniteMeasure γin) t).1)) := by
    convert hdiff.add hbranch using 1 <;> simp
  refine hsigma.congr fun k => ?_
  unfold Muon.DetEquiv.sigmaB Muon.DetEquiv.expRes Muon.mean
  rw [(D.isotropic k).2]
  simp only [Matrix.one_mul]
  change (D.R.B k : ℝ)⁻¹ * (∑ i, ∫ ω,
      Muon.DetEquiv.Rs
        (Muon.DetEquiv.WeightedBuf (Muon.emaW 0) (D.R.F k) (S k) 0 ω) t i i ∂(P k)) =
    (D.R.B k : ℝ)⁻¹ * ∫ ω, ∑ i,
      Muon.DetEquiv.Rs
        (Muon.DetEquiv.WeightedBuf (Muon.emaW 0) (D.R.F k) (S k) 0 ω) t i i ∂(P k)
  congr 1
  rw [integral_finsetSum]
  intro i hi
  refine Integrable.of_bound (C := 1 / t) ?_ ?_
  · exact (((measurable_pi_apply i).comp ((measurable_pi_apply i).comp
      (resolvent_measurable t))).comp
        (weightedBuf_zero_measurable_early (D.R.F k) (S k))).aestronglyMeasurable
  · filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    exact (abs_entry_le_opNorm _ i i).trans
      (Muon.DetEquiv.lem_app_de_resolvent _ t ht).1

/-- The scaled expected squared Frobenius norm has the required first-moment limit. -/
private lemma moment_limit_regime {γin γout : ℝ} (D : OrderedRegime γin γout)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, Muon.Setup.FrozenSamples (P k) (D.R.m k) (D.R.n k) (D.R.B k)) :
    (∀ k, Integrable (fun ω => Matrix.trace
      (Muon.DetEquiv.WeightedBuf (Muon.emaW 0) (D.R.F k) (S k) 0 ω *
        (Muon.DetEquiv.WeightedBuf (Muon.emaW 0) (D.R.F k) (S k) 0 ω)ᵀ)) (P k)) ∧
    Tendsto (fun k => (D.R.B k : ℝ)⁻¹ * ∫ ω, Matrix.trace
      (Muon.DetEquiv.WeightedBuf (Muon.emaW 0) (D.R.F k) (S k) 0 ω *
        (Muon.DetEquiv.WeightedBuf (Muon.emaW 0) (D.R.F k) (S k) 0 ω)ᵀ) ∂(P k))
      atTop (𝓝 (γin * γout)) := by
  let F0 : ∀ k, Muon.Setup.FrozenParams (D.R.m k) (D.R.n k) (D.R.B k) :=
    fun k => { D.R.F k with β := 0, hβ := ⟨le_rfl, zero_lt_one⟩ }
  let Y : ∀ k, Ω k → Muon.Mat (D.R.m k) (D.R.n k) := fun k =>
    Muon.DetEquiv.WeightedBuf (Muon.emaW 0) (D.R.F k) (S k) 0
  have hYmeas : ∀ k, Measurable (Y k) := fun k => by
    simpa [Y] using weightedBuf_zero_measurable_early (D.R.F k) (S k)
  have hint : ∀ k, Integrable (fun ω => Muon.fro (Y k ω) ^ 2) (P k) := by
    intro k
    have hm : ((D.R.m k : ℕ) : ℝ) ≤ D.R.γstar * (D.R.B k : ℝ) :=
      (Nat.cast_le.mpr (le_max_left _ _)).trans (D.R.dims k)
    have hn : ((D.R.n k : ℕ) : ℝ) ≤ D.R.γstar * (D.R.B k : ℝ) :=
      (Nat.cast_le.mpr (le_max_right _ _)).trans (D.R.dims k)
    have hlin := Muon.Volatility.lem_app_vol_square_iii (F0 k) (S k)
      D.R.CSig D.R.γstar (by simpa [F0] using D.R.normOut k)
      (by simpa [F0] using D.R.normIn k) hm hn 0
    have hlin' : ENNReal.ofReal ((D.R.B k : ℝ)⁻¹) *
        ∫⁻ ω, ENNReal.ofReal (Muon.fro (Y k ω) ^ 2) ∂(P k) ≤
          ENNReal.ofReal (D.R.CSig ^ 2 * (D.R.γstar + 2) ^ 2) := by
      simpa [F0, Y, Muon.Setup.frozenBuf, Muon.DetEquiv.WeightedBuf,
        Muon.Setup.frozenBatchG] using hlin
    have hB : (0 : ℝ) < D.R.B k := by exact_mod_cast (D.R.F k).hB
    have hscaled : ENNReal.ofReal (D.R.B k : ℝ) *
        (ENNReal.ofReal ((D.R.B k : ℝ)⁻¹) *
          ∫⁻ ω, ENNReal.ofReal (Muon.fro (Y k ω) ^ 2) ∂(P k)) ≤
        ENNReal.ofReal (D.R.B k : ℝ) *
          ENNReal.ofReal (D.R.CSig ^ 2 * (D.R.γstar + 2) ^ 2) := by
      gcongr
    have hcancel : ENNReal.ofReal (D.R.B k : ℝ) *
        ENNReal.ofReal ((D.R.B k : ℝ)⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul hB.le, mul_inv_cancel₀ hB.ne', ENNReal.ofReal_one]
    rw [← mul_assoc, hcancel, one_mul] at hscaled
    have hfin : (∫⁻ ω, ENNReal.ofReal (Muon.fro (Y k ω) ^ 2) ∂(P k)) ≠ ⊤ :=
      ne_top_of_le_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hscaled
    have hmeas : AEMeasurable (fun ω => Muon.fro (Y k ω) ^ 2) (P k) :=
      (continuous_fro_sq.measurable.comp (hYmeas k)).aemeasurable
    exact (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
      (ae_of_all _ fun ω => sq_nonneg _)).mp hfin
  have hmean : ∀ k, Muon.mean (P k) (Y k) = (D.R.F k).A := by
    intro k
    have h := (Muon.Setup.lem_app_setup_gaussian_moments_iv (D.R.F k) (S k) 1).1
    simp only [Muon.Setup.rOut, Muon.Setup.rIn] at h
    rw [(D.isotropic k).1, (D.isotropic k).2] at h
    simp only [CFC.sqrt_one, Matrix.one_mul, Matrix.mul_one] at h
    calc
      Muon.mean (P k) (Y k) =
          Muon.mean (P k) (Muon.Setup.frozenBatchG (D.R.F k) (S k) 1) := by
        congr 1
        funext ω
        exact weightedBuf_zero_eq_batch (D.R.F k) (S k) ω
      _ = (D.R.F k).A := h
  have hsecond : ∀ k, ∫ ω, Muon.fro (Y k ω) ^ 2 ∂(P k) =
      1 + (D.R.B k : ℝ)⁻¹ *
        ((D.R.m k : ℝ) * (D.R.n k : ℝ) + 2 * (D.R.m k : ℝ) +
          2 * (D.R.n k : ℝ) + 3) := by
    intro k
    have hmean0 : Muon.mean (P k) (Muon.Setup.frozenBatchG (F0 k) (S k) 1) =
        (D.R.F k).A := by
      have h := (Muon.Setup.lem_app_setup_gaussian_moments_iv (F0 k) (S k) 1).1
      simp only [Muon.Setup.rOut, Muon.Setup.rIn] at h
      rw [(D.isotropic k).1, (D.isotropic k).2] at h
      simpa [F0, CFC.sqrt_one] using h
    have hcen := (Muon.Setup.lem_app_setup_ema_law_iii (F0 k) (S k) 0).2.2
    change (∫ ω, Muon.fro (Muon.Setup.frozenBuf (F0 k) (S k) 0 ω -
        Muon.mean (P k) (Muon.Setup.frozenBatchG (F0 k) (S k) 1)) ^ 2 ∂(P k)) =
      Muon.sPow 0 2 * Muon.Setup.frozenVB (S k) (F0 k) at hcen
    rw [hmean0, Muon.sPow_two (by norm_num) (by norm_num)] at hcen
    norm_num at hcen
    have hcen' : ∫ ω, Muon.fro (Y k ω - (D.R.F k).A) ^ 2 ∂(P k) =
        Muon.Setup.frozenVB (S k) (F0 k) := by
      simpa [F0, Y, Muon.Setup.frozenBuf, Muon.DetEquiv.WeightedBuf,
        Muon.Setup.frozenBatchG] using hcen
    have htotal := uncentered_second_moment (Y k) (hYmeas k) (hint k)
      (D.R.F k).A (hmean k) (Muon.Setup.frozenVB (S k) (F0 k)) hcen'
    have hVB := Muon.Setup.lem_app_setup_gaussian_moments_v (F0 k) (S k)
    have hmeanBatch0 : Muon.mean (P k)
        (Muon.Setup.frozenBatchG (F0 k) (S k) 0) = (D.R.F k).A := by
      have h := (Muon.Setup.lem_app_setup_gaussian_moments_iv (F0 k) (S k) 0).1
      simp only [Muon.Setup.rOut, Muon.Setup.rIn] at h
      rw [(D.isotropic k).1, (D.isotropic k).2] at h
      simpa [F0, CFC.sqrt_one] using h
    rw [hmeanBatch0] at hVB
    change Muon.Setup.frozenVB (S k) (F0 k) = (1 / (D.R.B k : ℝ)) *
      (Matrix.trace (D.R.F k).C.Sout * Matrix.trace (D.R.F k).C.Sin +
        2 * Matrix.trace ((D.R.F k).C.Sout * ((D.R.F k).A * (D.R.F k).Aᵀ)) *
          Matrix.trace (D.R.F k).C.Sin +
        2 * Matrix.trace (D.R.F k).C.Sout *
          Matrix.trace ((D.R.F k).C.Sin * ((D.R.F k).Aᵀ * (D.R.F k).A)) +
        3 * Muon.fro (D.R.F k).A ^ 2) at hVB
    rw [(D.isotropic k).1, (D.isotropic k).2] at hVB
    have htrOut : Matrix.trace (1 : Muon.Mat (D.R.m k) (D.R.m k)) = D.R.m k := by
      simp [Matrix.trace, Matrix.diag]
    have htrIn : Matrix.trace (1 : Muon.Mat (D.R.n k) (D.R.n k)) = D.R.n k := by
      simp [Matrix.trace, Matrix.diag]
    have hAA : Matrix.trace ((D.R.F k).A * (D.R.F k).Aᵀ) = 1 := by
      rw [trace_mul_transpose_eq_fro_sq, (D.R.F k).hA]
      norm_num
    have hAtA : Matrix.trace ((D.R.F k).Aᵀ * (D.R.F k).A) = 1 := by
      rw [Matrix.trace_mul_comm, hAA]
    rw [Matrix.one_mul, Matrix.one_mul, htrOut, htrIn, hAA, hAtA,
      (D.R.F k).hA] at hVB
    rw [htotal, hVB, (D.R.F k).hA]
    simp only [one_pow, mul_one]
    ring_nf
  have htrace : ∀ k, (fun ω => Matrix.trace (Y k ω * (Y k ω)ᵀ)) =
      fun ω => Muon.fro (Y k ω) ^ 2 := by
    intro k
    funext ω
    exact trace_mul_transpose_eq_fro_sq (Y k ω)
  refine ⟨?_, ?_⟩
  · intro k
    simpa [Y, htrace k] using hint k
  · have hBinv : Tendsto (fun k => (D.R.B k : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp D.R.prop.B_top)
    have hro := D.R.prop.ratio_out
    have hri := D.R.prop.ratio_in
    rw [D.gamma_out] at hro
    rw [D.gamma_in] at hri
    have hlim := hBinv.add (((hro.mul hri).add
      (((hro.const_mul 2).mul hBinv).add
        (((hri.const_mul 2).mul hBinv).add ((hBinv.pow 2).const_mul 3)))))
    have hlim' : Tendsto (fun k => (D.R.B k : ℝ)⁻¹ +
        (((D.R.m k : ℝ) / (D.R.B k : ℝ)) *
          ((D.R.n k : ℝ) / (D.R.B k : ℝ)) +
        ((2 * ((D.R.m k : ℝ) / (D.R.B k : ℝ))) * (D.R.B k : ℝ)⁻¹ +
        ((2 * ((D.R.n k : ℝ) / (D.R.B k : ℝ))) * (D.R.B k : ℝ)⁻¹ +
          3 * (D.R.B k : ℝ)⁻¹ ^ 2)))) atTop (𝓝 (γout * γin)) := by
      convert hlim using 1
      all_goals ring_nf
    convert hlim' using 1
    · funext k
      rw [htrace k, hsecond k]
      have hBne : (D.R.B k : ℝ) ≠ 0 := by exact_mod_cast (D.R.F k).hB.ne'
      field_simp
      ring_nf
    · ring_nf

/-- The limiting isotropic branch supplies exactly the two closure identities required by
`OrderedApproximation`. -/
private lemma closure_regime {γin γout : ℝ} (hin : 0 < γin) (hout : 0 < γout)
    (t : ℝ) (ht : 0 < t) :
    let x := Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0))
      (isoFiniteMeasure γout) (isoFiniteMeasure γin) t
    γout - t * x.1 = γin - t * (x.1 + (γin - γout) / t) ∧
      γout - t * x.1 = isoPhi (t * x.1 * (x.1 + (γin - γout) / t)) := by
  dsimp only
  let νo := isoFiniteMeasure γout
  let νi := isoFiniteMeasure γin
  let x := Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0)) νo νi t
  have hw : Muon.DetEquiv.WeightSeq (Muon.emaW 0) := by
    refine ⟨fun j => ?_, ?_, 0, ?_⟩
    · unfold Muon.emaW
      positivity
    · unfold Muon.emaW
      exact (summable_geometric_of_lt_one (show (0 : ℝ) ≤ 0 by norm_num) zero_lt_one).mul_left _
    · simp [Muon.emaW]
  have hx : Muon.DetEquiv.IsBranchSol (Muon.DetEquiv.Fw (Muon.emaW 0)) νo νi t x := by
    apply Muon.DetEquiv.branchSol_spec
      (Muon.DetEquiv.Fw_admissible hw)
      (Cs := 1) (γ := max γin γout) zero_lt_one (lt_max_of_lt_left hin)
    · unfold Muon.DetEquiv.classK
      change (νo : Measure ℝ) (Icc 0 1) ≤ _ ∧ (νo : Measure ℝ) (Icc 0 1)ᶜ = 0 ∧
        (νi : Measure ℝ) (Icc 0 1) ≤ _ ∧ (νi : Measure ℝ) (Icc 0 1)ᶜ = 0
      dsimp [νo, νi, isoFiniteMeasure]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [isoSpecMeasure, Measure.smul_apply] using
          ENNReal.ofReal_le_ofReal (le_max_right γin γout)
      · simp [isoSpecMeasure, Measure.smul_apply]
      · simpa [isoSpecMeasure, Measure.smul_apply] using
          ENNReal.ofReal_le_ofReal (le_max_left γin γout)
      · simp [isoSpecMeasure, Measure.smul_apply]
    · exact ht
  have hcl := prop_app_iso_closure_i (β := 0) le_rfl zero_lt_one hin hout ht
    (ν := νo) (ν' := νi) rfl rfl hx
  have hphi := prop_app_iso_closure_iii hin hout ht
    (ν := νo) (ν' := νi) rfl rfl hx
  have hdiff : x.2.1 = x.1 + (γin - γout) / t := by
    linarith [hcl.2.2.2.2.2.2.1]
  change γout - t * x.1 = γin - t * (x.1 + (γin - γout) / t) ∧
    γout - t * x.1 = isoPhi (t * x.1 * (x.1 + (γin - γout) / t))
  refine ⟨?_, ?_⟩
  · rw [← hdiff]
    linarith [hcl.2.2.2.2.1, hcl.2.2.2.2.2.1]
  · rw [← hdiff]
    calc
      γout - t * x.1 = isoPsi 0 t x := hcl.2.2.2.2.1.symm
      _ = isoPhi (isoQ t x) := hphi.1
      _ = isoPhi (t * x.1 * x.2.1) := rfl

/-- Measurability of the no-momentum weighted buffer. -/
private lemma weightedBuf_zero_measurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B)
    (S : Muon.Setup.FrozenSamples P m n B) :
    Measurable (Muon.DetEquiv.WeightedBuf (Muon.emaW 0) F S 0) := by
  have hb : ∀ s : ℤ, Measurable (Muon.Setup.frozenBatchG F S s) := by
    intro s
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
    simp only [Muon.Setup.frozenBatchG, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    refine (Finset.measurable_sum _ fun a _ => ?_).const_mul _
    have hdot : Measurable (fun ω =>
        dotProduct (S.zw s a ω).1 (Matrix.mulVec F.A (S.zw s a ω).2)) := by
      simp only [dotProduct, Matrix.mulVec]
      exact Finset.measurable_sum _ fun p _ => ((measurable_pi_apply p).comp
        (measurable_fst.comp (S.meas s a))).mul
          (Finset.measurable_sum _ fun q _ => measurable_const.mul
            ((measurable_pi_apply q).comp (measurable_snd.comp (S.meas s a))))
    have houter : Measurable (fun ω =>
        (Muon.Setup.rOut F.C * Muon.outer (S.zw s a ω).1 (S.zw s a ω).2 *
          Muon.Setup.rIn F.C) i k) := by
      simp only [Matrix.mul_apply, Muon.outer, Matrix.vecMulVec_apply]
      exact Finset.measurable_sum _ fun q _ =>
        (Finset.measurable_sum _ fun p _ => measurable_const.mul
          (((measurable_pi_apply p).comp (measurable_fst.comp (S.meas s a))).mul
            ((measurable_pi_apply q).comp (measurable_snd.comp (S.meas s a))))).mul
              measurable_const
    exact hdot.mul houter
  letI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Muon.Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  letI : SecondCountableTopology (Muon.Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  letI : MeasurableAdd₂ (Muon.Mat m n) :=
    inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  unfold Muon.DetEquiv.WeightedBuf
  exact Measurable.tsum fun j => (hb (0 + 1 - (j : ℤ))).const_smul (Muon.emaW 0 j)

/-- The data produced by the finite-dimensional Gaussian regime in the ordered case
`γout ≤ γin`.  Keeping this package private isolates the only part of the proof which uses the
large Muon setup/deterministic-equivalent stack. -/
private structure OrderedApproximation (γin γout : ℝ) where
  ν : ℕ → Measure ℝ
  σ : ℝ → ℝ
  finite : ∀ k, IsFiniteMeasure (ν k)
  support : ∀ k, ν k (Iio 0) = 0
  mass : Tendsto (fun k => (ν k).real univ) atTop (𝓝 γout)
  trace : ∀ t : ℝ, 0 < t →
    Tendsto (fun k => negStieltjes (ν k) t) atTop (𝓝 (σ t))
  moment_integrable : ∀ k, Integrable (fun x : ℝ => x) (ν k)
  moment : Tendsto (fun k => ∫ x, x ∂(ν k)) atTop (𝓝 (γin * γout))
  closure : ∀ t : ℝ, 0 < t →
    γout - t * σ t = γin - t * (σ t + (γin - γout) / t) ∧
      γout - t * σ t = isoPhi (t * σ t * (σ t + (γin - γout) / t))

/-- Steps 2--4 of the module route: construct the identity-covariance Gaussian regime, its
scaled expected output Gram measures, and identify their trace and first-moment limits.  The
proof needs `SetupRegime`, `FrozenSamples`, `cor_app_de_trace_i`, and
`thm_app_de_branch_ii`; those declarations are not in the transitive closure of this module's
frozen imports. -/
private lemma regime_sample_construction {γin γout : ℝ} (hin : 0 < γin) (hout : 0 < γout)
    (hord : γout ≤ γin) : Nonempty (OrderedApproximation γin γout) := by
  let D : OrderedRegime γin γout := (regime_exists hin hout hord).some
  let R := D.R
  let Ω : ℕ → Type := fun k => (ℤ × Fin (R.B k)) →
    Muon.Vec (R.m k) × Muon.Vec (R.n k)
  let P : ∀ k, Measure (Ω k) := fun k => Measure.infinitePi fun _ : ℤ × Fin (R.B k) =>
    (Muon.Foundations.stdGaussianPi (R.m k)).prod
      (Muon.Foundations.stdGaussianPi (R.n k))
  letI : ∀ k, IsProbabilityMeasure (P k) := fun _ => inferInstance
  let S : ∀ k, Muon.Setup.FrozenSamples (P k) (R.m k) (R.n k) (R.B k) :=
    (samples_exist R).some
  let M : ∀ k, Ω k → Muon.Mat (R.m k) (R.n k) := fun k =>
    Muon.DetEquiv.WeightedBuf (Muon.emaW 0) (R.F k) (S k) 0
  have hM : ∀ k, AEMeasurable (M k) (P k) := fun k =>
    (weightedBuf_zero_measurable (R.F k) (S k)).aemeasurable
  have hA : ∀ k, AEMeasurable (fun ω => M k ω * (M k ω)ᵀ) (P k) :=
    fun k => (hM k).mul_transpose_self
  have hpsd : ∀ k, ∀ᵐ ω ∂(P k), (M k ω * (M k ω)ᵀ).PosSemidef :=
    fun k => ae_of_all _ fun ω => posSemidef_mul_transpose_self _
  have hc : ∀ k, 0 ≤ (R.B k : ℝ)⁻¹ := fun _ => by positivity
  let ν : ℕ → Measure ℝ := fun k => ENNReal.ofReal (R.B k : ℝ)⁻¹ •
    expectedEigMeasure (P k) (fun ω => M k ω * (M k ω)ᵀ)
  let σ : ℝ → ℝ := fun t =>
    (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0))
      (isoFiniteMeasure γout) (isoFiniteMeasure γin) t).1
  have hfin : ∀ k, IsFiniteMeasure (ν k) := fun k =>
    isFiniteMeasure_ofReal_smul_expectedEigMeasure (hA k) _
  have hsupp : ∀ k, ν k (Iio 0) = 0 := fun k =>
    ofReal_smul_expectedEigMeasure_Iio_zero (hA k) (hpsd k) _
  have hmass : Tendsto (fun k => (ν k).real univ) atTop (𝓝 γout) := by
    have hr := R.prop.ratio_out
    rw [D.gamma_out] at hr
    refine hr.congr fun k => ?_
    rw [measureReal_ofReal_smul_expectedEigMeasure_univ (hA k) (hc k)]
    simp [div_eq_inv_mul]
  obtain ⟨htrInt, hmom⟩ := moment_limit_regime D P S
  have hmomk := fun k => integral_id_ofReal_smul_expectedEigMeasure (hA k) (hpsd k)
    (by simpa [M] using htrInt k) (hc k)
  refine ⟨⟨ν, σ, hfin, hsupp, hmass, ?_, fun k => (hmomk k).1, ?_, ?_⟩⟩
  · intro t ht
    refine (trace_limit_regime D P S t ht).congr fun k => ?_
    rw [negStieltjes_ofReal_smul_expectedEigMeasure (hA k) (hpsd k) (hc k) ht]
    simp [M, Muon.DetEquiv.Rs, negResolvent]
    rfl
  · refine hmom.congr fun k => ?_
    rw [(hmomk k).2]
    rfl
  · intro t ht
    exact closure_regime hin hout t ht

/-- Step 4(b): the resolvent-trace limit supplied by the ordered Gaussian approximation. -/
private lemma trace_limit {γin γout : ℝ} (D : OrderedApproximation γin γout)
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun k => negStieltjes (D.ν k) t) atTop (𝓝 (D.σ t)) :=
  D.trace t ht

/-- Step 4(c): the first-moment limit supplied by the ordered Gaussian approximation. -/
private lemma first_moment_limit {γin γout : ℝ} (D : OrderedApproximation γin γout) :
    Tendsto (fun k => ∫ x, x ∂(D.ν k)) atTop (𝓝 (γin * γout)) :=
  D.moment

/-- Step 5: extract the limiting output measure from an ordered approximation. -/
private lemma limit_output_measure {γin γout : ℝ} (D : OrderedApproximation γin γout) :
    ∃ mo : Measure ℝ, IsFiniteMeasure mo ∧ mo univ = ENNReal.ofReal γout ∧
      mo (Iio 0) = 0 ∧ ∀ t : ℝ, 0 < t → isoNegStieltjes mo t = D.σ t := by
  let _ : ∀ k, IsFiniteMeasure (D.ν k) := D.finite
  obtain ⟨B, hB⟩ := (first_moment_limit D).bddAbove_range
  obtain ⟨mo, hfin, hmass, hsupp, htrace, -⟩ :=
    exists_tendsto_of_tendsto_negStieltjes D.ν D.support D.mass D.moment_integrable
      (B := B) (fun k => hB ⟨k, rfl⟩) (fun t ht => trace_limit D t ht)
  refine ⟨mo, hfin, hmass, hsupp, ?_⟩
  intro t ht
  exact htrace t ht

/-- Step 5--6: add the missing zero atom on the input side and assemble the ordered pair. -/
private lemma assemble_ordered_pair {γin γout : ℝ} (hin : 0 < γin) (hout : 0 < γout)
    (hord : γout ≤ γin) (D : OrderedApproximation γin γout) :
    ∃ mo mi : Measure ℝ, Muon.Isotropic.IsIsoMeasurePair γin γout mo mi := by
  obtain ⟨mo, hmo_fin, hmo_mass, hmo_supp, hmo_trace⟩ := limit_output_measure D
  let d : ℝ := γin - γout
  let mi : Measure ℝ := mo + ENNReal.ofReal d • Measure.dirac 0
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have hd0 : Measure.dirac (0 : ℝ) (Iio 0) = 0 := by simp
  let _ : IsFiniteMeasure mo := hmo_fin
  let _ : IsFiniteMeasure (ENNReal.ofReal d • Measure.dirac (0 : ℝ)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hmi_mass : mi univ = ENNReal.ofReal γin := by
    rw [show mi = mo + ENNReal.ofReal d • Measure.dirac 0 from rfl,
      Measure.add_apply, Measure.smul_apply, hmo_mass]
    simp only [measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hout.le hd]
    congr 1
    dsimp [d]
    ring
  have hmi_supp : mi (Iio 0) = 0 := by
    rw [show mi = mo + ENNReal.ofReal d • Measure.dirac 0 from rfl,
      Measure.add_apply, Measure.smul_apply, hmo_supp, hd0]
    simp
  have hmi_trace : ∀ t : ℝ, 0 < t →
      isoNegStieltjes mi t = D.σ t + (γin - γout) / t := by
    intro t ht
    change negStieltjes mi t = _
    rw [show mi = mo + ENNReal.ofReal d • Measure.dirac 0 from rfl,
      negStieltjes_add hmo_supp (by simp [Measure.smul_apply, hd0]) ht,
      negStieltjes_smul, negStieltjes_dirac, ENNReal.toReal_ofReal hd]
    rw [show negStieltjes mo t = D.σ t from hmo_trace t ht]
    dsimp [d]
    rw [zero_add, div_eq_mul_inv]
  refine ⟨mo, mi, ?_⟩
  refine
    { pos_in := hin
      pos_out := hout
      mass_out := hmo_mass
      mass_in := hmi_mass
      supp_out := hmo_supp
      supp_in := hmi_supp
      identity := ?_ }
  intro t ht
  rw [hmo_trace t ht, hmi_trace t ht]
  exact D.closure t ht

/-- Step 1: symmetry of `IsIsoMeasurePair` under swapping input and output. -/
private lemma swap_iso_measure_pair {γin γout : ℝ} {mo mi : Measure ℝ}
    (h : Muon.Isotropic.IsIsoMeasurePair γout γin mi mo) :
    Muon.Isotropic.IsIsoMeasurePair γin γout mo mi := by
  refine
    { pos_in := h.pos_out
      pos_out := h.pos_in
      mass_out := h.mass_in
      mass_in := h.mass_out
      supp_out := h.supp_in
      supp_in := h.supp_out
      identity := ?_ }
  intro t ht
  obtain ⟨heq, hphi⟩ := h.identity t ht
  refine ⟨heq.symm, ?_⟩
  calc
    γout - t * Muon.Isotropic.isoNegStieltjes mo t =
        γin - t * Muon.Isotropic.isoNegStieltjes mi t := heq.symm
    _ = isoPhi (t * Muon.Isotropic.isoNegStieltjes mi t *
          Muon.Isotropic.isoNegStieltjes mo t) := hphi
    _ = isoPhi (t * Muon.Isotropic.isoNegStieltjes mo t *
          Muon.Isotropic.isoNegStieltjes mi t) := by ring_nf

end MeasureExistenceProof

/-- prop:app-iso-measure (existence half), snapshot `cr-2026-10-23`.
The source environment, verbatim
(`sections/05b-isotropic/section.tex`, l.948–951):
```latex
\begin{proposition}[Existence of the isotropic measure pair]\label{prop:app-iso-measure}
For every $\gin>0$ and $\gout>0$ there is exactly one isotropic measure pair
$(\mathfrak m_{\mathrm{out}},\mathfrak m_{\mathrm{in}})$ at $(\gin,\gout)$.
\end{proposition}
```
The proof (l.953–992) is the limit of expected Gram spectral measures; it is not restated here. -/
theorem prop_app_iso_measure_exists {γin γout : ℝ} (hin : 0 < γin) (hout : 0 < γout) :
    ∃ mo mi : Measure ℝ, IsIsoMeasurePair γin γout mo mi := by
  rcases le_total γout γin with hord | hord
  · exact assemble_ordered_pair hin hout hord (regime_sample_construction hin hout hord).some
  · obtain ⟨mi, mo, hpair⟩ :=
      assemble_ordered_pair hout hin hord (regime_sample_construction hout hin hord).some
    exact ⟨mo, mi, swap_iso_measure_pair hpair⟩

/-- prop:app-iso-measure (ExistsUnique record), snapshot `cr-2026-10-23`. The source environment,
verbatim (`sections/05b-isotropic/section.tex`, l.948–951):
```latex
\begin{proposition}[Existence of the isotropic measure pair]\label{prop:app-iso-measure}
For every $\gin>0$ and $\gout>0$ there is exactly one isotropic measure pair
$(\mathfrak m_{\mathrm{out}},\mathfrak m_{\mathrm{in}})$ at $(\gin,\gout)$.
\end{proposition}
```
Declaration of record of the label. Existence is `prop_app_iso_measure_exists`; uniqueness is
`prop_app_iso_measure_unique` (L-F.6). -/
theorem prop_app_iso_measure {γin γout : ℝ} (hin : 0 < γin) (hout : 0 < γout) :
    ∃! p : Measure ℝ × Measure ℝ, IsIsoMeasurePair γin γout p.1 p.2 := by
  obtain ⟨mo, mi, h⟩ := prop_app_iso_measure_exists hin hout
  refine ⟨(mo, mi), h, fun p hp => ?_⟩
  obtain ⟨h1, h2⟩ := prop_app_iso_measure_unique hp h
  exact Prod.ext h1 h2

/-- thm:app-iso-large, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1640–1665):
```latex
\begin{theorem}[Large aspect ratios]\label{thm:app-iso-large}
Let $\gin^{(j)},\gout^{(j)}\to\infty$, without a condition on their ratio,
and let $(\mathfrak m_{\mathrm{out}}^{(j)},\mathfrak m_{\mathrm{in}}^{(j)})$ be the isotropic
measure pair at $(\gin^{(j)},\gout^{(j)})$ of \cref{prop:app-iso-measure}.
For $j$ with $\gin^{(j)},\gout^{(j)}>1$ write
$\mathfrak m_{\mathrm{out}}^{(j)}=(\gout^{(j)}-1)\delta_0+\eta_j$ as in
\cref{lem:app-iso-moments}(iv), let $\mathsf E_j$ be the image of the
probability measure $\eta_j$ under $\lambda\mapsto\lambda/(\gin^{(j)}\gout^{(j)})$,
and put $\epsilon_j\defeq1/\gin^{(j)}+1/\gout^{(j)}$. Let $\mathsf X$ be the law
of $g^2$ for $g\sim\mathcal N(0,1)$, which has density, first moment and
half-moment
\begin{equation}\label{eqn:app-iso-chi}
\frac{e^{-x/2}}{\sqrt{2\pi x}}\,\mathbf 1_{x>0},\qquad
\int x\,\mathsf X(\dif x)=1,\qquad
\int\sqrt x\,\mathsf X(\dif x)=\sqrt{\frac2\pi}.
\end{equation}
Then $\mathsf E_j\to\mathsf X$ weakly,
\begin{equation}\label{eqn:app-iso-large-error}
0\le\sqrt{\frac2\pi}-\int\sqrt x\,\mathsf E_j(\dif x)\le\frac4\pi\sqrt{\epsilon_j},
\end{equation}
and
\begin{equation}\label{eqn:app-iso-large}
C\big(\gin^{(j)},\gout^{(j)}\big)=\frac{1}{\sqrt{2\gin^{(j)}\gout^{(j)}}}\int\sqrt x\,\mathsf E_j(\dif x)\sim\frac{1}{\sqrt{\pi\gin^{(j)}\gout^{(j)}}} .
\end{equation}
In particular $C(\gamma)\sim1/(\sqrt\pi\,\gamma)$ as $\gamma\to\infty$.
\end{theorem}
```

Relocated here from `Muon.Isotropic.Measure` by the coordinator (2026-10-24): the γ-limit
needs measure pairs for every γ (`prop_app_iso_measure_exists`, this file). -/
theorem thm_app_iso_large_iii (gin gout : ℕ → ℝ) (mo mi : ℕ → Measure ℝ)
    (hp : ∀ j, IsIsoMeasurePair (gin j) (gout j) (mo j) (mi j))
    (hin : Tendsto gin atTop atTop) (hout : Tendsto gout atTop atTop) :
    (∀ j : ℕ, 1 < gin j → 1 < gout j →
      Cbeta 0 (gin j) (gout j) =
        1 / Real.sqrt (2 * (gin j * gout j)) *
          ∫ x, Real.sqrt x ∂(isoScaledImage (gin j * gout j) ((mo j).restrict (Ioi 0)))) ∧
    Asymptotics.IsEquivalent atTop (fun j => Cbeta 0 (gin j) (gout j))
        (fun j => 1 / Real.sqrt (Real.pi * gin j * gout j)) ∧
    Tendsto (fun γ : ℝ => Cbeta 0 γ γ / (1 / (Real.sqrt Real.pi * γ))) atTop (𝓝 1) := by
  refine ⟨(m_iii_parts12 gin gout mo mi hp hin hout).1,
    (m_iii_parts12 gin gout mo mi hp hin hout).2, ?_⟩
  apply tendsto_of_seq_tendsto
  intro u hu
  have hv : Tendsto (fun n => max (u n) 1) atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_left _ _) hu
  have hpos : ∀ n, 0 < max (u n) 1 := fun n => lt_of_lt_of_le one_pos (le_max_right _ _)
  choose mo' mi' hpair using fun n => prop_app_iso_measure_exists (hpos n) (hpos n)
  have h12 := (m_iii_parts12 (fun n => max (u n) 1) (fun n => max (u n) 1) mo' mi' hpair hv hv).2
  have hne : ∀ n, 1 / Real.sqrt (Real.pi * max (u n) 1 * max (u n) 1) ≠ 0 := fun n => by
    have := hpos n
    positivity
  have ht := (Asymptotics.isEquivalent_iff_tendsto_one
    (Filter.Eventually.of_forall hne)).1 h12
  refine ht.congr' ?_
  filter_upwards [hu.eventually_ge_atTop 1] with n hn
  have hm : max (u n) 1 = u n := max_eq_left hn
  simp only [Pi.div_apply, Function.comp_apply, hm]
  have hu0 : 0 < u n := by linarith
  have : Real.sqrt (Real.pi * u n * u n) = Real.sqrt Real.pi * u n := by
    rw [mul_assoc, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_mul_self hu0.le]
  rw [this]

end Muon.Isotropic

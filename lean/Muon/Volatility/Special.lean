import Muon.Volatility.Closed.Kernel
import Muon.Volatility.LagKernel
import Muon.Volatility.Defs

/-!
# Appendix D, work package L-D.19: the same-time kernel and totals for two anisotropic covariances

Work package L-D.19 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/04-volatility/section.tex`, the corollary `thm:app-vol-double-same` (l.3152–3176), with
its forward definitions `eqn:app-vol-traces`, `eqn:app-vol-Upsilon`, `eqn:app-vol-kernel`,
`eqn:app-vol-Zk` (l.3120–3145), and `eqn:app-vol-Z` (l.420), `eqn:app-vol-contraction` (l.259).
Card: `sections/04-volatility/CARD.md` §2, §3 (row `thm:app-vol-double-same`), §5 (row L-D.19), §6.

Reused, not redefined:
* `upsilonK`, `kernelK`, `zkK` (`Muon.Volatility.Closed.Kernel`, L-D.18; these are the definitions
  of `eqn:app-vol-Upsilon`, `eqn:app-vol-kernel`, `eqn:app-vol-Zk`, which L-D.19 shares), with
  `trOutP`, `trInP` for `eqn:app-vol-traces`.
* `lagResp` (`Muon.Volatility.LagKernel`), `iotaF`, `omegaF`, `contractionRes`
  (`Muon.Volatility.OddSpectral`), `SizeFin`, `SizeSeq`, `sameTimeZ`, `sameTimeZc`,
  `def_app_vol_product`, `indepSpaceLaw` (`Muon.Volatility.Defs`).
* `FrozenParams` (with `β`, `0 ≤ β < 1`, `0 < B`), `FrozenSamples`, `frozenBuf` (`Muon.Setup`),
  `SpectralData`, `SetupRegime` (`Muon.Setup.Regime`), `Muon.nuOut`, `Muon.nuIn`, `Muon.opNorm`.

Encoding decisions:
* The covariance-weighted kernel is `kernelK` at the covariances `Σ_out = Fp.C.Sout`,
  `Σ_in = Fp.C.Sin`, with the full spectral measures `ν, ν'` as `FiniteMeasure ℝ` (`hν`, `hν'`).
  `𝔨_0[Σ_out,Σ_in]` is `lagResp` at lag `0` with diagonal tests `Fd = S.μ`, `Gd = S.lam`, the
  encoding of `LagKernel`.
* `𝔨(s,u) = 𝔨_0[Σ_out,Σ_in](s,u)` is part (i) of the statement (`prop:app-vol-closed-reductions`(a)
  is cited there in the source).
* `𝔼 K_{s,u}(M_t,M_t)` is `∫ contractionRes … (frozenBuf …) (frozenBuf …)`, with `M_t = frozenBuf`
  (`\Mt`) and `M^g_t = def_app_vol_product`. Each integral carries an `Integrable` conjunct.
* Sup-norm limits are stated in the `ε`-form `∀ ε > 0, ∀ᶠ k, ∀ …, |…| ≤ ε` (no `iSup`), with the
  quantifiers in the source's order: `ε`, then the index, then `t`, then the points of `J` or `I`.
* The sequence statements use `SetupRegime` (`assum:app-setup-regime`, with `ϱ ∈ I = [ϱlo, ϱhi]`) and
  `SizeSeq` for the independent model (size conditions). The hypotheses `Σ_out ≠ 0`, `Σ_in ≠ 0` of the
  corollary's header are carried by every part.
* `1 ≤ C_Σ` is carried by the fixed-dimension statements and by the independent-model statement,
  because the lag-zero closed form is proved through `lagResp`, which needs it (the convention of
  `Muon.Volatility.Closed.Kernel`; `SetupRegime` has it as field `hC`). Flagged in the result JSON.
* Positivity `0 < ϱ` is a hypothesis of the ridge statements; `0 < s`, `0 < u` of the kernel statements.
* `cert : Muon.External.GaussianOpNorm` is an explicit argument wherever the proof goes through
  `lagResp`, and is not otherwise used by the statement.
-/


set_option linter.style.longLine false

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped Matrix MatrixOrder
open Matrix
open Muon Muon.Setup Muon.DetEquiv

noncomputable section

namespace Muon.Volatility

/-! ### Private helpers for `thm_app_vol_double_same_i` (task P-D.19.P1) -/

private lemma dsi_gauss_family :
    ∃ (P : Measure (ℕ ⊕ Fin 0 → ℝ)), IsProbabilityMeasure P ∧
      IsStdGaussianFamily P (fun (a : ℕ ⊕ Fin 0) (ω : ℕ ⊕ Fin 0 → ℝ) => ω a) := by
  refine ⟨Measure.infinitePi fun _ : ℕ ⊕ Fin 0 => gaussianReal 0 1, inferInstance, ?_, ?_, ?_⟩
  · intro a; exact measurable_pi_apply a
  · exact iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  · intro a
    exact ⟨(measurable_pi_apply a).aemeasurable, Measure.infinitePi_map_eval _ a⟩

private lemma dsi_opNorm_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ Muon.opNorm A := by
  unfold Muon.opNorm; exact norm_nonneg _

private lemma dsi_tsum_fin0 (f : ℕ ⊕ Fin 0 → ℝ) : ∑' a, f a = ∑' j : ℕ, f (Sum.inl j) := by
  rw [← (Equiv.sumEmpty ℕ (Fin 0)).symm.tsum_eq f]
  simp

private lemma dsi_branch {m n B : ℕ} (hB : 0 < B) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {g : ℕ ⊕ Fin 0 → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (C : Muon.Covariances m n) (hout : C.Sout ≠ 0) (hin : C.Sin ≠ 0) (γstar CSig : ℝ)
    (hS : SizeFin C B γstar CSig) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut C B) (hν' : (ν' : Measure ℝ) = Muon.nuIn C B)
    {s : ℝ} (hs : 0 < s) :
    branchPt (profileF P (emaXi₁ β 0 g)) C B s = branchSol (Fw (Muon.emaW β)) ν ν' s ∧
    branchPt (profileF P (emaXi₂ β 0 g)) C B s = branchSol (Fw (Muon.emaW β)) ν ν' s ∧
    0 < (branchSol (Fw (Muon.emaW β)) ν ν' s).1 ∧
    0 < (branchSol (Fw (Muon.emaW β)) ν ν' s).2.1 ∧
    0 < (branchSol (Fw (Muon.emaW β)) ν ν' s).2.2.1 ∧
    0 < (branchSol (Fw (Muon.emaW β)) ν ν' s).2.2.2 := by
  have hK := nu_pair_mem_classK C γstar CSig hS hB ν ν' hν hν'
  have h1 := lem_app_vol_closed_branch_ema hB hβ0 hβ1 hg C CSig γstar ν ν' hν hν' hK hs
  have h2 := lem_app_vol_closed_branch_ema_two hB hβ0 hβ1 hg C CSig γstar ν ν' hν hν' hK hs
  have hp := lem_app_vol_closed_profile_iv (P := P) hβ0 hβ1 hg
  have hmax : (max m n : ℝ) ≤ γstar * B := by simpa only [Nat.cast_max] using hS.1
  have hbr := lem_app_vol_closed_branch_ii hB hp.2.2.2.2.2.profile₁ hs C hout hin γstar hmax
  have hex := hbr.1.exists
  have hx : IsBranchPoint (profileF P (emaXi₁ β 0 g)) C B s
      (branchPt (profileF P (emaXi₁ β 0 g)) C B s) := by
    unfold branchPt
    rw [dif_pos hex]
    exact hex.choose_spec
  have hpos := (hbr.2 _ hx).1
  rw [h1.2] at hpos
  exact ⟨h1.2, h2.2, hpos⟩

private lemma dsi_pairedE {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {β : ℝ} {g : ℕ ⊕ Fin 0 → Ω → ℝ} (hg : IsStdGaussianFamily P g) (q : ℝ) :
    pairedE P (emaXi₁ β 0 g) (emaXi₂ β 0 g) q q = fwNegDeriv β q := by
  unfold pairedE
  rw [dsi_tsum_fin0]
  unfold fwNegDeriv
  refine tsum_congr (fun j => ?_)
  simp only [emaXi₁, emaXi₂, pow_zero, one_mul]
  set w := Muon.emaW β j
  have hm : Measurable (fun x : ℝ => (w * x) ^ 2 * (w * x) ^ 2 /
      ((1 + q * (w * x) ^ 2) * (1 + q * (w * x) ^ 2))) := by fun_prop
  have h := (hg.2.2 (Sum.inl j)).integral_comp hm.aestronglyMeasurable
  simp only [Function.comp] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ (fun x => ?_))
  have hD : (1 + q * (w * x) ^ 2) * (1 + q * (w * x) ^ 2) = (1 + q * w ^ 2 * x ^ 2) ^ 2 := by ring
  simp only
  rw [hD]
  ring

private lemma dsi_pairedB_diag {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {g : ℕ ⊕ Fin 0 → Ω → ℝ} (hg : IsStdGaussianFamily P g) {q : ℝ} (hq : 0 < q) :
    pairedB P (emaXi₁ β 0 g) (emaXi₂ β 0 g) q q = rwDeriv β q := by
  have hp := lem_app_vol_closed_profile_iv (P := P) hβ0 hβ1 hg
  have hw : WeightSeq (Muon.emaW β) := (Muon.Drift.emaW_weightClass β ⟨hβ0, hβ1⟩).1
  have h4 := (hp.2.2.2.1 q q hq.le hq.le (by simp)).1
  have h3 := (lem_app_de_scalar_iii hw).2.2.2.1 q hq
  rw [h4]
  have hd : derivWithin (rW (Muon.emaW β)) (Ici 0) q = deriv (rW (Muon.emaW β)) q :=
    derivWithin_of_mem_nhds (Ici_mem_nhds hq)
  rw [hd, h3.deriv]
  simp only [pow_zero, one_mul]
  unfold rwDeriv
  refine tsum_congr (fun j => ?_)
  congr 1
  refine integral_congr_ae (ae_of_all _ (fun x => ?_))
  simp only
  rw [show 1 + q * Muon.emaW β j ^ 2 * x ^ 2 = 1 + Muon.emaW β j ^ 2 * q * x ^ 2 by ring]

private lemma dsi_pairedB_pos {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {g : ℕ ⊕ Fin 0 → Ω → ℝ} (hg : IsStdGaussianFamily P g) {q q' : ℝ} (hq : 0 < q)
    (hq' : 0 < q') :
    0 < pairedB P (emaXi₁ β 0 g) (emaXi₂ β 0 g) q q' := by
  have hp := lem_app_vol_closed_profile_iv (P := P) hβ0 hβ1 hg
  have hw : WeightSeq (Muon.emaW β) := (Muon.Drift.emaW_weightClass β ⟨hβ0, hβ1⟩).1
  have hiii := lem_app_de_scalar_iii hw
  by_cases h : q = β ^ (2 * 0) * q'
  · have h4 := (hp.2.2.2.1 q q' hq.le hq'.le h).1
    have h3 := hiii.2.2.2.1 q hq
    have hd : derivWithin (rW (Muon.emaW β)) (Ici 0) q = deriv (rW (Muon.emaW β)) q :=
      derivWithin_of_mem_nhds (Ici_mem_nhds hq)
    rw [h4, hd, h3.deriv]
    simpa only [pow_zero, one_mul] using hiii.2.2.2.2.1 q hq
  · have h4 := (hp.2.2.1 q q' hq.le hq'.le h).1
    rw [h4]
    simp only [mul_zero, pow_zero, one_mul] at h ⊢
    have hmono := hiii.2.1
    rcases lt_or_gt_of_ne h with hlt | hgt
    · exact div_pos_of_neg_of_neg (sub_neg.2 (hmono (Set.mem_Ici.2 hq.le) (Set.mem_Ici.2 hq'.le) hlt))
        (sub_neg.2 hlt)
    · exact div_pos (sub_pos.2 (hmono (Set.mem_Ici.2 hq'.le) (Set.mem_Ici.2 hq.le) hgt))
        (sub_pos.2 hgt)

private lemma dsi_trace_two {d : ℕ}
    (A U : Matrix (Fin d) (Fin d) ℝ) (v w : Fin d → ℝ)
    (hU : Uᵀ * U = 1) (hA : A = U * Matrix.diagonal v * Uᵀ)
    (F : Matrix (Fin d) (Fin d) ℝ) (hF : F = U * Matrix.diagonal w * Uᵀ)
    (s a u c : ℝ) (hs : ∀ i, s + a * v i ≠ 0) (hu : ∀ i, u + c * v i ≠ 0) :
    (F * A * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • A)⁻¹ *
      (u • (1 : Matrix (Fin d) (Fin d) ℝ) + c • A)⁻¹).trace =
        ∑ i, w i * v i / ((s + a * v i) * (u + c * v i)) := by
  classical
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hinv : ∀ (t b : ℝ), (∀ i, t + b * v i ≠ 0) →
      (t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • A)⁻¹ =
        U * Matrix.diagonal (fun i => (t + b * v i)⁻¹) * Uᵀ := by
    intro t b hden
    have he : Matrix.diagonal (fun i => t + b * v i) =
        t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • Matrix.diagonal v := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
    have hfac : t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • A =
        U * Matrix.diagonal (fun i => t + b * v i) * Uᵀ := by
      rw [he, Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU, ← hA]
    have hdiag : Matrix.diagonal (fun i => t + b * v i) *
        Matrix.diagonal (fun i => (t + b * v i)⁻¹) = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij, hden]
    apply Matrix.inv_eq_right_inv
    rw [hfac]
    calc U * Matrix.diagonal (fun i => t + b * v i) * Uᵀ *
          (U * Matrix.diagonal (fun i => (t + b * v i)⁻¹) * Uᵀ) =
        U * (Matrix.diagonal (fun i => t + b * v i) *
          Matrix.diagonal (fun i => (t + b * v i)⁻¹)) * Uᵀ := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
      _ = 1 := by rw [hdiag, Matrix.mul_one, hUU]
  rw [hinv s a hs, hinv u c hu, hA, hF]
  calc
    (U * Matrix.diagonal w * Uᵀ * (U * Matrix.diagonal v * Uᵀ) *
        (U * Matrix.diagonal (fun i => (s + a * v i)⁻¹) * Uᵀ) *
        (U * Matrix.diagonal (fun i => (u + c * v i)⁻¹) * Uᵀ)).trace =
      (U * (Matrix.diagonal w * Matrix.diagonal v *
        Matrix.diagonal (fun i => (s + a * v i)⁻¹) *
        Matrix.diagonal (fun i => (u + c * v i)⁻¹)) * Uᵀ).trace := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul,
            ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul,
            ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
    _ = (Matrix.diagonal w * Matrix.diagonal v *
        Matrix.diagonal (fun i => (s + a * v i)⁻¹) *
        Matrix.diagonal (fun i => (u + c * v i)⁻¹)).trace := by
          rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    _ = _ := by
      simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, div_eq_mul_inv]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_inv]
      ring


private lemma dsi_tout_pos {m n B : ℕ} (hB : 0 < B) {C : Muon.Covariances m n}
    (S : SpectralData C) (hout : C.Sout ≠ 0) (x y : ℝ × ℝ × ℝ × ℝ)
    (hx : 0 ≤ x.2.2.1) (hy : 0 ≤ y.2.2.1) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    0 < toutT C B x y s u C.Sout := by
  have hso : ∀ i, s + x.2.2.1 * S.μ i ≠ 0 := fun i => ne_of_gt
    (add_pos_of_pos_of_nonneg hs (mul_nonneg hx (μ_nonneg S i)))
  have huo : ∀ i, u + y.2.2.1 * S.μ i ≠ 0 := fun i => ne_of_gt
    (add_pos_of_pos_of_nonneg hu (mul_nonneg hy (μ_nonneg S i)))
  unfold toutT
  rw [dsi_trace_two C.Sout S.uOut S.μ S.μ S.huOut (Sout_eq_spectral S) C.Sout
    (Sout_eq_spectral S) s x.2.2.1 u y.2.2.1 hso huo]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  refine mul_pos (inv_pos.2 hBr) ?_
  have hex : ∃ i, S.μ i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hout
    rw [Sout_eq_spectral S]
    have : S.μ = 0 := funext hcon
    simp [this]
  obtain ⟨i0, hi0⟩ := hex
  refine Finset.sum_pos' (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
  · have := μ_nonneg S i
    have h1 : 0 < s + x.2.2.1 * S.μ i := by positivity
    have h2 : 0 < u + y.2.2.1 * S.μ i := by positivity
    positivity
  · have h1 : 0 < s + x.2.2.1 * S.μ i0 := add_pos_of_pos_of_nonneg hs (mul_nonneg hx (μ_nonneg S i0))
    have h2 : 0 < u + y.2.2.1 * S.μ i0 := add_pos_of_pos_of_nonneg hu (mul_nonneg hy (μ_nonneg S i0))
    have h3 : 0 < S.μ i0 * S.μ i0 := mul_self_pos.2 hi0
    positivity

private lemma dsi_tin_pos {m n B : ℕ} (hB : 0 < B) {C : Muon.Covariances m n}
    (S : SpectralData C) (hin : C.Sin ≠ 0) (x y : ℝ × ℝ × ℝ × ℝ)
    (hx : 0 ≤ x.2.2.2) (hy : 0 ≤ y.2.2.2) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    0 < tinT C B x y s u C.Sin := by
  have hso : ∀ i, s + x.2.2.2 * S.lam i ≠ 0 := fun i => ne_of_gt
    (add_pos_of_pos_of_nonneg hs (mul_nonneg hx (lam_nonneg S i)))
  have huo : ∀ i, u + y.2.2.2 * S.lam i ≠ 0 := fun i => ne_of_gt
    (add_pos_of_pos_of_nonneg hu (mul_nonneg hy (lam_nonneg S i)))
  unfold tinT
  rw [dsi_trace_two C.Sin S.vIn S.lam S.lam S.hvIn (Sin_eq_spectral S) C.Sin
    (Sin_eq_spectral S) s x.2.2.2 u y.2.2.2 hso huo]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  refine mul_pos (inv_pos.2 hBr) ?_
  have hex : ∃ i, S.lam i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hin
    rw [Sin_eq_spectral S]
    have : S.lam = 0 := funext hcon
    simp [this]
  obtain ⟨i0, hi0⟩ := hex
  refine Finset.sum_pos' (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
  · have := lam_nonneg S i
    have h1 : 0 < s + x.2.2.2 * S.lam i := by positivity
    have h2 : 0 < u + y.2.2.2 * S.lam i := by positivity
    positivity
  · have h1 : 0 < s + x.2.2.2 * S.lam i0 := add_pos_of_pos_of_nonneg hs (mul_nonneg hx (lam_nonneg S i0))
    have h2 : 0 < u + y.2.2.2 * S.lam i0 := add_pos_of_pos_of_nonneg hu (mul_nonneg hy (lam_nonneg S i0))
    have h3 : 0 < S.lam i0 * S.lam i0 := mul_self_pos.2 hi0
    positivity

private lemma dsi_inv_comm {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (s a u c : ℝ) :
    (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • S)⁻¹ * (u • (1 : Matrix (Fin d) (Fin d) ℝ) + c • S)⁻¹ =
      (u • (1 : Matrix (Fin d) (Fin d) ℝ) + c • S)⁻¹ * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • S)⁻¹ := by
  have h : Commute (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • S)
      (u • (1 : Matrix (Fin d) (Fin d) ℝ) + c • S) := by
    unfold Commute SemiconjBy
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_add, smul_smul]
    module
  rw [← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, h.eq]

private lemma dsi_trOut_comm {m n : ℕ} (β : ℝ) (C : Muon.Covariances m n) (B : ℕ)
    (ν ν' : FiniteMeasure ℝ) (p : ℕ) (s u : ℝ) :
    trOutP β C B ν ν' p s u = trOutP β C B ν ν' p u s := by
  unfold trOutP Rbar
  rw [Matrix.mul_assoc, Matrix.mul_assoc, dsi_inv_comm]

private lemma dsi_trIn_comm {m n : ℕ} (β : ℝ) (C : Muon.Covariances m n) (B : ℕ)
    (ν ν' : FiniteMeasure ℝ) (p : ℕ) (s u : ℝ) :
    trInP β C B ν ν' p s u = trInP β C B ν ν' p u s := by
  unfold trInP Rtbar
  rw [Matrix.mul_assoc, Matrix.mul_assoc, dsi_inv_comm]

private lemma dsi_trOut_eq_toutT {m n : ℕ} (β : ℝ) (C : Muon.Covariances m n) (B : ℕ)
    (ν ν' : FiniteMeasure ℝ) (s u : ℝ) :
    trOutP β C B ν ν' 2 s u =
      toutT C B (branchSol (Fw (Muon.emaW β)) ν ν' s) (branchSol (Fw (Muon.emaW β)) ν ν' u) s u
        C.Sout := by
  unfold trOutP toutT Rbar
  rw [pow_two]

private lemma dsi_trIn_eq_tinT {m n : ℕ} (β : ℝ) (C : Muon.Covariances m n) (B : ℕ)
    (ν ν' : FiniteMeasure ℝ) (s u : ℝ) :
    trInP β C B ν ν' 2 s u =
      tinT C B (branchSol (Fw (Muon.emaW β)) ν ν' s) (branchSol (Fw (Muon.emaW β)) ν ν' u) s u
        C.Sin := by
  unfold trInP tinT Rtbar
  rw [pow_two]

private lemma dsi_kernelK_symm {m n : ℕ} (β : ℝ) (C : Muon.Covariances m n) (B : ℕ)
    (ν ν' : FiniteMeasure ℝ) (s u : ℝ) :
    kernelK β C B ν ν' s u = kernelK β C B ν ν' u s := by
  by_cases h : s = u
  · subst h; rfl
  · unfold kernelK
    simp only [if_neg h, if_neg (Ne.symm h)]
    rw [dsi_trOut_comm β C B ν ν' 2 u s, dsi_trIn_comm β C B ν ν' 2 u s,
      dsi_trOut_comm β C B ν ν' 1 u s]
    rw [show (s * (branchSol (Fw (Muon.emaW β)) ν ν' u).2.2.2 -
          u * (branchSol (Fw (Muon.emaW β)) ν ν' s).2.2.2) =
        -(u * (branchSol (Fw (Muon.emaW β)) ν ν' s).2.2.2 -
          s * (branchSol (Fw (Muon.emaW β)) ν ν' u).2.2.2) by ring,
      show (s - u) = -(u - s) by ring, neg_mul, mul_neg, neg_div_neg_eq]

/-- `thm:app-vol-double-same`, part (i), snapshot `cr-2026-10-23`. Declaration of record for the
fixed-dimension part (i): `Υ(s) > 0` for `s > 0`; `𝔨 = 𝔨_0[Σ_out,Σ_in]` (the lag-zero response at the
covariances, `lagResp`); `𝔨` is positive, symmetric and continuous on `(0,∞)²`; and
`𝔨(s,u) ≤ γ⋆ C_Σ² / (4√(su))`. The standing assumptions are `SizeFin`, `Σ_out ≠ 0`, `Σ_in ≠ 0`,
and `1 ≤ C_Σ`. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{corollary}[Same-time volatility, two anisotropic covariances]\label{thm:app-vol-double-same}
Assume the size conditions, and that $\Sigmaout\ne0$ and $\Sigmain\ne0$.
\begin{enumerate}[label=(\roman*)]
\item At every finite dimension, $\Upsilon(s)>0$ for $s>0$, and
$\mathfrak k=\mathfrak k_0[\Sigmaout,\Sigmain]$. In particular $\mathfrak k$ is positive,
symmetric and continuous on $(0,\infty)^2$, with
\begin{equation}\label{eqn:app-vol-kernel-bounds}
\mathfrak k(s,u)\le\frac{\gamma_\star C_\Sigma^2}{4\sqrt{su}} .
\end{equation}
\item Under \cref{assum:app-setup-regime}, for every compact
$\mathcal J\subset(0,\infty)$,
\begin{equation}\label{eqn:app-vol-double-kernel}
\sup_{s,u\in\mathcal J}\abs{\EE\,\mathcal K_{s,u}(\Mt,\Mt)-\mathfrak k(s,u)}\longrightarrow0 ,
\end{equation}
and the same holds with $\Mt$ replaced by $M^{\mathrm g}_t$ under the size
conditions.
\item The integral \cref{eqn:app-vol-Zk} converges, $\overline Z_{\mathfrak k}(\ridge)=\overline C_0(\ridge,\ridge)$,
$0<\overline Z_{\mathfrak k}(\ridge)\le\gamma_\star C_\Sigma^2$, and under
\cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-double-total}
\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z_{\mathfrak k}(\ridge)}\longrightarrow0,\qquad
\sup_{\ridge\in I}\abs{\EE Z^{\mathrm c}(\ridge)-\overline Z_{\mathfrak k}(\ridge)}\longrightarrow0 .
\end{equation}
\end{enumerate}
\end{corollary}
```
-/
theorem thm_app_vol_double_same_i (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut Fp.C B) (hν' : (ν' : Measure ℝ) = Muon.nuIn Fp.C B) :
    (∀ s : ℝ, 0 < s → 0 < upsilonK Fp.β Fp.C B ν ν' s) ∧
    (∀ s u : ℝ, 0 < s → 0 < u →
      kernelK Fp.β Fp.C B ν ν' s u =
        lagResp cert γstar CSig Fp.β 0 B S.μ S.lam S.μ S.lam (iotaF s) (iotaF u)) ∧
    ContinuousOn (fun p : ℝ × ℝ => kernelK Fp.β Fp.C B ν ν' p.1 p.2) (Ioi 0 ×ˢ Ioi 0) ∧
    (∀ s u : ℝ, 0 < s → 0 < u → 0 < kernelK Fp.β Fp.C B ν ν' s u) ∧
    (∀ s u : ℝ, 0 < s → 0 < u →
      kernelK Fp.β Fp.C B ν ν' s u = kernelK Fp.β Fp.C B ν ν' u s) ∧
    (∀ s u : ℝ, 0 < s → 0 < u →
      kernelK Fp.β Fp.C B ν ν' s u ≤ γstar * CSig ^ 2 / (4 * Real.sqrt (s * u))) := by
  obtain ⟨P, hP, hg⟩ := dsi_gauss_family
  haveI := hP
  have hB := Fp.hB
  have hβ0 := Fp.hβ.1
  have hβ1 := Fp.hβ.2
  have hFd : Fp.C.Sout = S.uOut * Matrix.diagonal S.μ * S.uOutᵀ := Sout_eq_spectral S
  have hGd : Fp.C.Sin = S.vIn * Matrix.diagonal S.lam * S.vInᵀ := Sin_eq_spectral S
  have hlag : ∀ s u : ℝ, 0 < s → 0 < u → kernelK Fp.β Fp.C B ν ν' s u =
      lagResp cert γstar CSig Fp.β 0 B S.μ S.lam S.μ S.lam (iotaF s) (iotaF u) :=
    fun s u hs hu => (prop_app_vol_closed_reductions_i cert γstar CSig Fp S hS hCSig hout hin ν ν'
      hν hν' s u hs hu).symm
  have hΔ := fun s u (hs : 0 < s) (hu : 0 < u) =>
    (thm_app_vol_closed_kernel_i γstar CSig Fp.C hB hS hβ0 hβ1 0 hg s u hs hu).1
  have hbr := fun s (hs : 0 < s) =>
    dsi_branch hB hβ0 hβ1 hg Fp.C hout hin γstar CSig hS ν ν' hν hν' hs
  refine ⟨?_, hlag, ?_, ?_, fun s u _ _ => dsi_kernelK_symm Fp.β Fp.C B ν ν' s u, ?_⟩
  · intro s hs
    obtain ⟨h1, h2, p1, p2, p3, p4⟩ := hbr s hs
    have hq : 0 < s * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).1 *
        (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).2.1 := by positivity
    have hd := hΔ s s hs hs
    unfold profileDelta closedDelta at hd
    dsimp only at hd
    rw [h1, h2, dsi_pairedB_diag hβ0 hβ1 hg hq, dsi_pairedE hg] at hd
    unfold upsilonK
    dsimp only
    rw [dsi_trOut_eq_toutT, dsi_trIn_eq_tinT]
    convert hd using 1
    ring
  · exact ((cor_app_vol_closed_bounds_i cert γstar CSig Fp S hS hCSig 0 Fp.C.Sout Fp.C.Sin S.μ S.lam
      hFd hGd).1).congr (fun p hp => (hlag p.1 p.2 hp.1 hp.2).symm ▸ rfl)
  · intro s u hs hu
    obtain ⟨h1s, h2s, p1s, p2s, p3s, p4s⟩ := hbr s hs
    obtain ⟨h1u, h2u, p1u, p2u, p3u, p4u⟩ := hbr u hu
    rw [hlag s u hs hu, (thm_app_vol_closed_kernel_ii cert γstar CSig Fp S hS hCSig 0 hg
      Fp.C.Sout Fp.C.Sin S.μ S.lam hFd hGd s u hs hu).2]
    unfold profileKernel
    dsimp only
    rw [h1s, h2u]
    have hb := dsi_pairedB_pos hβ0 hβ1 hg
      (q := s * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).1 *
        (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).2.1)
      (q' := u * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).1 *
        (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).2.1) (by positivity) (by positivity)
    have ht1 := dsi_tout_pos hB S hout (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s)
      (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u) p3s.le p3u.le hs hu
    have ht2 := dsi_tin_pos hB S hin (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s)
      (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u) p4s.le p4u.le hs hu
    have hd := hΔ s u hs hu
    have := mul_pos (mul_pos (mul_pos (mul_pos hs hu) hb) ht1) ht2
    exact div_pos this hd
  · intro s u hs hu
    have h1 := (cor_app_vol_closed_bounds_ii cert γstar CSig Fp S hS hCSig 0 Fp.C.Sout Fp.C.Sin S.μ
      S.lam hFd hGd s u hs hu).1
    rw [hlag s u hs hu]
    refine (le_abs_self _).trans (h1.trans ?_)
    have hγ : 0 ≤ γstar := by
      have hm : (0 : ℝ) ≤ (max m n : ℕ) := Nat.cast_nonneg _
      have hBr : (0 : ℝ) < B := by exact_mod_cast hB
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_neg_of_pos hneg hBr
      linarith [hS.1]
    have hsq : 0 < 4 * Real.sqrt (s * u) := by positivity
    have ho1 := dsi_opNorm_nonneg Fp.C.Sout
    have ho2 := dsi_opNorm_nonneg Fp.C.Sin
    rw [pow_two]
    refine div_le_div_of_nonneg_right ?_ hsq.le
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hγ
    exact mul_le_mul hS.2.1 hS.2.2 ho2 (ho1.trans hS.2.1)

/-! ### Private helpers for `thm_app_vol_double_same_ii_*` (task P-D.19.P2) -/

private lemma dsii_spec_exists {m n : ℕ} (C : Muon.Covariances m n) :
    Nonempty (SpectralData C) := by
  have hA := C.psdOut.isHermitian
  have hB := C.psdIn.isHermitian
  have key : ∀ {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian),
      ∃ (U : Matrix (Fin d) (Fin d) ℝ) (μ : Fin d → ℝ), Uᵀ * U = 1 ∧
        ∀ i : Fin d, A *ᵥ (fun k => U k i) = μ i • (fun k => U k i) := by
    intro d A hA
    refine ⟨(hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ), hA.eigenvalues, ?_, ?_⟩
    · have h1 : (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) *
          (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) = 1 :=
        Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
      rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h1
    · intro i
      have := hA.mulVec_eigenvectorBasis i
      exact this
  obtain ⟨U, μ, hU, hUe⟩ := key C.Sout hA
  obtain ⟨V, l, hV, hVe⟩ := key C.Sin hB
  exact ⟨⟨U, V, μ, l, hU, hV, hUe, hVe⟩⟩


private lemma dsii_contractionRes_smul {m n : ℕ} (B : ℕ) (F : Matrix (Fin m) (Fin m) ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) (c d s u : ℝ) (K H : Mat m n) :
    contractionRes B (c • F) (d • G) s u K H = c * d * contractionRes B F G s u K H := by
  unfold contractionRes contraction
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

open scoped Matrix.Norms.L2Operator in
private lemma dsii_opNorm_smul {p q : ℕ} (c : ℝ) (K : Mat p q) :
    opNorm (c • K) = |c| * opNorm K := by
  rw [opNorm_eq_norm, opNorm_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma dsii_lagResp_scale (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ) (c d : ℝ)
    (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) :
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (fun i => c * S.μ i) (fun j => d * S.lam j) f g =
      c * d * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam S.μ S.lam f g := by
  obtain ⟨-, hlinF, hlinG, -⟩ :=
    thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hCSig ℓ f g hf hg
  have h0F : ∀ Gd : Fin n → ℝ,
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (fun _ => (0 : ℝ)) Gd f g = 0 := by
    intro Gd
    have := hlinF 1 (fun _ => 0) (fun _ => 0) Gd
    simp only [mul_zero, add_zero, one_mul] at this
    linarith
  have h0G : ∀ Fd : Fin m → ℝ,
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd (fun _ => (0 : ℝ)) f g = 0 := by
    intro Fd
    have := hlinG 1 Fd (fun _ => 0) (fun _ => 0)
    simp only [mul_zero, add_zero, one_mul] at this
    linarith
  have h1 := hlinF c S.μ (fun _ => 0) (fun j => d * S.lam j)
  simp only [add_zero] at h1
  have h3 := hlinG d S.μ S.lam (fun _ => 0)
  simp only [add_zero] at h3
  rw [h1, h0F, add_zero, h3, h0G, add_zero]
  ring


private lemma dsii_diag_smul {d : ℕ} (c : ℝ) (U : Matrix (Fin d) (Fin d) ℝ) (μ : Fin d → ℝ) :
    c • (U * Matrix.diagonal μ * Uᵀ) = U * Matrix.diagonal (fun i => c * μ i) * Uᵀ := by
  have hd : Matrix.diagonal (fun i => c * μ i) = c • Matrix.diagonal μ := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.diagonal_apply_ne _ h]
  rw [hd]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

private lemma dsii_norm_facts {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (CSig : ℝ) (hCSig : 1 ≤ CSig) (h1 : opNorm Fp.C.Sout ≤ CSig) (h2 : opNorm Fp.C.Sin ≤ CSig) :
    CSig⁻¹ • Fp.C.Sout = S.uOut * Matrix.diagonal (fun i => CSig⁻¹ * S.μ i) * S.uOutᵀ ∧
    CSig⁻¹ • Fp.C.Sin = S.vIn * Matrix.diagonal (fun j => CSig⁻¹ * S.lam j) * S.vInᵀ ∧
    opNorm (CSig⁻¹ • Fp.C.Sout) ≤ 1 ∧ opNorm (CSig⁻¹ • Fp.C.Sin) ≤ 1 := by
  have hpos : 0 < CSig := by linarith
  have hc : |CSig⁻¹| = CSig⁻¹ := abs_of_pos (inv_pos.mpr hpos)
  refine ⟨?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [Sout_eq_spectral S]
    exact dsii_diag_smul _ _ _
  · conv_lhs => rw [Sin_eq_spectral S]
    exact dsii_diag_smul _ _ _
  · rw [dsii_opNorm_smul, hc]
    calc CSig⁻¹ * opNorm Fp.C.Sout ≤ CSig⁻¹ * CSig :=
          mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hpos).le
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  · rw [dsii_opNorm_smul, hc]
    calc CSig⁻¹ * opNorm Fp.C.Sin ≤ CSig⁻¹ * CSig :=
          mul_le_mul_of_nonneg_left h2 (inv_pos.mpr hpos).le
      _ = 1 := inv_mul_cancel₀ hpos.ne'

private lemma dsii_red_pt (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut Fp.C B) (hν' : (ν' : Measure ℝ) = Muon.nuIn Fp.C B)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (M : Ω → Mat m n) (s u ε : ℝ)
    (hs : 0 < s) (hu : 0 < u)
    (hcl : |(∫ ω, contractionRes B (CSig⁻¹ • Fp.C.Sout) (CSig⁻¹ • Fp.C.Sin) s u (M ω) (M ω) ∂μ) -
      lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (fun i => CSig⁻¹ * S.μ i)
        (fun j => CSig⁻¹ * S.lam j) (iotaF s) (iotaF u)| ≤ ε / CSig ^ 2) :
    |(∫ ω, contractionRes B Fp.C.Sout Fp.C.Sin s u (M ω) (M ω) ∂μ) -
      kernelK Fp.β Fp.C B ν ν' s u| ≤ ε := by
  have hpos : 0 < CSig := by linarith
  have hsc := dsii_lagResp_scale cert γstar CSig Fp S hS hCSig 0 CSig⁻¹ CSig⁻¹ (iotaF s) (iotaF u)
    (lem_app_vol_sharp_ii hs one_pos).1 (lem_app_vol_sharp_ii hu one_pos).1
  rw [hsc] at hcl
  have hK := prop_app_vol_closed_reductions_i cert γstar CSig Fp S hS hCSig hout hin ν ν' hν hν' s u
    hs hu
  rw [← hK]
  have hpt : ∀ ω, contractionRes B Fp.C.Sout Fp.C.Sin s u (M ω) (M ω) =
      CSig ^ 2 * contractionRes B (CSig⁻¹ • Fp.C.Sout) (CSig⁻¹ • Fp.C.Sin) s u (M ω) (M ω) := by
    intro ω
    rw [dsii_contractionRes_smul]
    field_simp
  simp_rw [hpt]
  rw [integral_const_mul]
  have e : CSig ^ 2 * (∫ ω, contractionRes B (CSig⁻¹ • Fp.C.Sout) (CSig⁻¹ • Fp.C.Sin) s u (M ω) (M ω) ∂μ)
      - lagResp cert γstar CSig Fp.β 0 B S.μ S.lam S.μ S.lam (iotaF s) (iotaF u) =
      CSig ^ 2 * ((∫ ω, contractionRes B (CSig⁻¹ • Fp.C.Sout) (CSig⁻¹ • Fp.C.Sin) s u (M ω) (M ω) ∂μ)
      - CSig⁻¹ * CSig⁻¹ * lagResp cert γstar CSig Fp.β 0 B S.μ S.lam S.μ S.lam (iotaF s) (iotaF u)) := by
    field_simp
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  calc CSig ^ 2 * _ ≤ CSig ^ 2 * (ε / CSig ^ 2) := mul_le_mul_of_nonneg_left hcl (by positivity)
    _ = ε := by field_simp


open scoped Matrix.Norms.Frobenius in
private lemma dsii_oddSharp_cont {m n : ℕ} (f : ℝ → ℝ) (hf : IsOddBddLip f) :
    Continuous (fun K : Mat m n => oddSharp f K) := by
  have hnn : 0 ≤ lipConst f :=
    Real.iSup_nonneg fun p => by
      split_ifs
      · exact le_rfl
      · positivity
  have hL : LipschitzWith (Real.toNNReal (lipConst f)) (fun K : Mat m n => oddSharp f K) := by
    refine LipschitzWith.of_dist_le_mul fun K K' => ?_
    rw [dist_eq_norm, dist_eq_norm, ← fro_eq_norm, ← fro_eq_norm, Real.coe_toNNReal _ hnn]
    exact (lem_app_vol_sharp_i f hf K K').2.2
  exact hL.continuous

private lemma dsii_contr_cont {m n : ℕ} (B : ℕ) (F : Matrix (Fin m) (Fin m) ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    Continuous (fun K : Mat m n => contractionRes B F G s u K K) := by
  have h1 := dsii_oddSharp_cont (m := m) (n := n) (iotaF s) (lem_app_vol_sharp_ii hs one_pos).1
  have h2 := dsii_oddSharp_cont (m := m) (n := n) (iotaF u) (lem_app_vol_sharp_ii hu one_pos).1
  unfold contractionRes contraction
  exact continuous_const.mul
    ((((continuous_const.matrix_mul h1).matrix_mul continuous_const).matrix_mul
      h2.matrix_transpose).matrix_trace)

private lemma dsii_integrable {m n B : ℕ} (γstar CSig : ℝ) (Fp : FrozenParams m n B)
    (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (M : Ω → Mat m n)
    (hM : AEStronglyMeasurable M μ) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    Integrable (fun ω => contractionRes B Fp.C.Sout Fp.C.Sin s u (M ω) (M ω)) μ := by
  have hpos : 0 < CSig := by linarith
  obtain ⟨-, -, hF, hG⟩ := dsii_norm_facts Fp S CSig hCSig hS.2.1 hS.2.2
  have hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B :=
    le_trans (by exact_mod_cast (min_le_left m n).trans (le_max_left m n)) hS.1
  have hpt : ∀ ω, contractionRes B Fp.C.Sout Fp.C.Sin s u (M ω) (M ω) =
      CSig ^ 2 * contractionRes B (CSig⁻¹ • Fp.C.Sout) (CSig⁻¹ • Fp.C.Sin) s u (M ω) (M ω) := by
    intro ω
    rw [dsii_contractionRes_smul]
    field_simp
  simp_rw [hpt]
  refine Integrable.const_mul ?_ _
  refine Integrable.of_bound (C := γstar * supNorm (iotaF s) * supNorm (iotaF u)) ?_ ?_
  · exact (dsii_contr_cont B _ _ hs hu).comp_aestronglyMeasurable hM
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    exact lem_app_vol_finite_i Fp.hB γstar hdim _ _ hF hG _ _ (lem_app_vol_sharp_ii hs one_pos).1
      (lem_app_vol_sharp_ii hu one_pos).1 _ _


private lemma dsii_entry_le_fro {m n : ℕ} (K : Mat m n) (i : Fin m) (j : Fin n) :
    |K i j| ≤ fro K := by
  unfold fro
  refine Real.abs_le_sqrt ?_
  have h1 : ‖K i j‖ ^ 2 ≤ ∑ j', ‖K i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖K i j'‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖K i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖K i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖K i' j'‖ ^ 2)
      (fun i' _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
  have h3 : ‖K i j‖ ^ 2 = K i j ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  linarith

private lemma dsii_summable_mat {m n : ℕ} {ι : Type*} (f : ι → Mat m n)
    (hf : Summable fun j => fro (f j)) : Summable f := by
  refine (Pi.summable).2 fun i => (Pi.summable).2 fun k => ?_
  refine Summable.of_norm_bounded hf (fun j => ?_)
  rw [Real.norm_eq_abs]
  exact dsii_entry_le_fro (f j) i k

private lemma dsii_aesm_tsum {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → Mat m n) (hf : ∀ j, StronglyMeasurable (f j))
    (hs : ∀ᵐ ω ∂μ, Summable fun j => fro (f j ω)) :
    AEStronglyMeasurable (fun ω => ∑' j, f j ω) μ := by
  haveI : TopologicalSpace.PseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin n → ℝ))
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun N ω => ∑ j ∈ Finset.range N, f j ω) (fun N => ?_) ?_
  · exact (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ => hf j).aestronglyMeasurable
  · filter_upwards [hs] with ω hω
    exact (dsii_summable_mat _ hω).hasSum.tendsto_sum_nat

private lemma dsii_frozenBuf_aesm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) :
    AEStronglyMeasurable (frozenBuf F S t) P := by
  haveI : TopologicalSpace.PseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin n → ℝ))
  have hae := (lem_app_setup_ema_law_i F S).1
  have hc : Continuous (fun p : Vec m × Vec n =>
      (dotProduct p.1 (Matrix.mulVec F.A p.2)) • (rOut F.C * outer p.1 p.2 * rIn F.C)) := by
    fun_prop
  have hsm : ∀ s : ℤ, StronglyMeasurable (frozenBatchG F S s) := by
    intro s
    unfold frozenBatchG
    refine StronglyMeasurable.const_smul ?_ ((B : ℝ))⁻¹
    exact Finset.stronglyMeasurable_fun_sum Finset.univ fun a _ =>
      hc.comp_stronglyMeasurable (S.meas s a).stronglyMeasurable
  exact dsii_aesm_tsum P _ (fun j => (hsm (t + 1 - (j : ℤ))).const_smul (emaW F.β j))
    (by filter_upwards [hae] with ω hω using hω t)

private lemma dsii_product_aesm {m n B : ℕ} (F : FrozenParams m n B) (t : ℤ) :
    AEStronglyMeasurable (fun ω => def_app_vol_product F ω t) (indepSpaceLaw m n B) := by
  haveI : TopologicalSpace.PseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin n → ℝ))
  have hc : Continuous (fun p : ℝ × (Vec m × Vec n) =>
      p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) := by
    fun_prop
  have hsm : ∀ s : ℤ, StronglyMeasurable (fun ω => indepBatchG F ω s) := by
    intro s
    unfold indepBatchG
    refine StronglyMeasurable.const_smul ?_ ((B : ℝ))⁻¹
    exact Finset.stronglyMeasurable_fun_sum Finset.univ fun a _ =>
      hc.comp_stronglyMeasurable (measurable_pi_apply (s, a)).stronglyMeasurable
  unfold def_app_vol_product
  exact dsii_aesm_tsum _ _ (fun j => (hsm (t + 1 - (j : ℤ))).const_smul (emaW F.β j))
    (by filter_upwards [def_app_vol_product_summable F] with ω hω using hω t)


/-- `thm:app-vol-double-same`, part (ii), actual model, snapshot `cr-2026-10-23`. Declaration of
record: under `assum:app-setup-regime` (`SetupRegime R`, with `Σ_out ≠ 0`, `Σ_in ≠ 0` at every index),
for every compact `J ⊂ (0,∞)`, `sup_{s,u∈J} |𝔼 K_{s,u}(M_t,M_t) − 𝔨(s,u)| → 0`, in the `ε`-form, for
all `t`; the integrands are integrable. The covariance-weighted kernel `K_{s,u}` is `contractionRes` at
`Σ_out, Σ_in`, with `M_t = frozenBuf`. The `cert` argument is the certificate of `lagResp`, used by the
proof. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{corollary}[Same-time volatility, two anisotropic covariances]\label{thm:app-vol-double-same}
Assume the size conditions, and that $\Sigmaout\ne0$ and $\Sigmain\ne0$.
\begin{enumerate}[label=(\roman*)]
\item At every finite dimension, $\Upsilon(s)>0$ for $s>0$, and
$\mathfrak k=\mathfrak k_0[\Sigmaout,\Sigmain]$. In particular $\mathfrak k$ is positive,
symmetric and continuous on $(0,\infty)^2$, with
\begin{equation}\label{eqn:app-vol-kernel-bounds}
\mathfrak k(s,u)\le\frac{\gamma_\star C_\Sigma^2}{4\sqrt{su}} .
\end{equation}
\item Under \cref{assum:app-setup-regime}, for every compact
$\mathcal J\subset(0,\infty)$,
\begin{equation}\label{eqn:app-vol-double-kernel}
\sup_{s,u\in\mathcal J}\abs{\EE\,\mathcal K_{s,u}(\Mt,\Mt)-\mathfrak k(s,u)}\longrightarrow0 ,
\end{equation}
and the same holds with $\Mt$ replaced by $M^{\mathrm g}_t$ under the size
conditions.
\item The integral \cref{eqn:app-vol-Zk} converges, $\overline Z_{\mathfrak k}(\ridge)=\overline C_0(\ridge,\ridge)$,
$0<\overline Z_{\mathfrak k}(\ridge)\le\gamma_\star C_\Sigma^2$, and under
\cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-double-total}
\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z_{\mathfrak k}(\ridge)}\longrightarrow0,\qquad
\sup_{\ridge\in I}\abs{\EE Z^{\mathrm c}(\ridge)-\overline Z_{\mathfrak k}(\ridge)}\longrightarrow0 .
\end{equation}
\end{enumerate}
\end{corollary}
```
-/
theorem thm_app_vol_double_same_ii_actual (cert : Muon.External.GaussianOpNorm)
    (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (hout : ∀ k, (R.F k).C.Sout ≠ 0) (hin : ∀ k, (R.F k).C.Sin ≠ 0)
    (ν ν' : ∀ k, FiniteMeasure ℝ)
    (hν : ∀ k, (ν k : Measure ℝ) = Muon.nuOut (R.F k).C (R.B k))
    (hν' : ∀ k, (ν' k : Measure ℝ) = Muon.nuIn (R.F k).C (R.B k))
    (J : Set ℝ) (hJ : IsCompact J) (hJpos : J ⊆ Set.Ioi 0) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ s ∈ J, ∀ u ∈ J,
      |(∫ ω, contractionRes (R.B k) (R.F k).C.Sout (R.F k).C.Sin s u
            (frozenBuf (R.F k) (S k) t ω) (frozenBuf (R.F k) (S k) t ω) ∂(P k)) -
        kernelK (R.F k).β (R.F k).C (R.B k) (ν k) (ν' k) s u| ≤ ε) ∧
    (∀ᶠ k in atTop, ∀ t : ℤ, ∀ s ∈ J, ∀ u ∈ J,
      Integrable (fun ω => contractionRes (R.B k) (R.F k).C.Sout (R.F k).C.Sin s u
        (frozenBuf (R.F k) (S k) t ω) (frozenBuf (R.F k) (S k) t ω)) (P k)) := by
  have hSz : ∀ k, SizeFin (R.F k).C (R.B k) R.γstar R.CSig :=
    fun k => ⟨R.dims k, R.normOut k, R.normIn k⟩
  let Sp : ∀ k, SpectralData (R.F k).C := fun k => (dsii_spec_exists (R.F k).C).some
  have hcl := (thm_app_vol_lag_kernel_closure_actual cert R Ω P S Sp 0 J hJ hJpos).1
  have hCpos : 0 < R.CSig := by linarith [R.hC]
  refine ⟨fun ε hε => ?_, Filter.Eventually.of_forall fun k t s hs u hu => ?_⟩
  · filter_upwards [hcl (ε / R.CSig ^ 2) (by positivity)] with k hk t s hs u hu
    obtain ⟨h1, h2, h3, h4⟩ := dsii_norm_facts (R.F k) (Sp k) R.CSig R.hC (R.normOut k) (R.normIn k)
    have := hk t s hs u hu _ _ _ _ h1 h2 h3 h4
    simp only [Nat.cast_zero, add_zero] at this
    exact dsii_red_pt cert R.γstar R.CSig (R.F k) (Sp k) (hSz k) R.hC (hout k) (hin k) (ν k) (ν' k)
      (hν k) (hν' k) (P k) (frozenBuf (R.F k) (S k) t) s u ε (hJpos hs) (hJpos hu) this
  · exact dsii_integrable R.γstar R.CSig (R.F k) (Sp k) (hSz k) R.hC (P k) _
      (dsii_frozenBuf_aesm (R.F k) (S k) t) (hJpos hs) (hJpos hu)

/-- `thm:app-vol-double-same`, part (ii), independent model, snapshot `cr-2026-10-23`. Declaration of
record: under the size conditions along the sequence (`SizeSeq`, with `Σ_out ≠ 0`, `Σ_in ≠ 0` and
`1 ≤ C_Σ`), for every compact `J ⊂ (0,∞)`, `sup_{s,u∈J} |𝔼 K_{s,u}(M^g_t,M^g_t) − 𝔨(s,u)| → 0` in the
`ε`-form, for all `t`, with `M^g_t = def_app_vol_product` on the independent product space
`indepSpaceLaw`. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{corollary}[Same-time volatility, two anisotropic covariances]\label{thm:app-vol-double-same}
Assume the size conditions, and that $\Sigmaout\ne0$ and $\Sigmain\ne0$.
\begin{enumerate}[label=(\roman*)]
\item At every finite dimension, $\Upsilon(s)>0$ for $s>0$, and
$\mathfrak k=\mathfrak k_0[\Sigmaout,\Sigmain]$. In particular $\mathfrak k$ is positive,
symmetric and continuous on $(0,\infty)^2$, with
\begin{equation}\label{eqn:app-vol-kernel-bounds}
\mathfrak k(s,u)\le\frac{\gamma_\star C_\Sigma^2}{4\sqrt{su}} .
\end{equation}
\item Under \cref{assum:app-setup-regime}, for every compact
$\mathcal J\subset(0,\infty)$,
\begin{equation}\label{eqn:app-vol-double-kernel}
\sup_{s,u\in\mathcal J}\abs{\EE\,\mathcal K_{s,u}(\Mt,\Mt)-\mathfrak k(s,u)}\longrightarrow0 ,
\end{equation}
and the same holds with $\Mt$ replaced by $M^{\mathrm g}_t$ under the size
conditions.
\item The integral \cref{eqn:app-vol-Zk} converges, $\overline Z_{\mathfrak k}(\ridge)=\overline C_0(\ridge,\ridge)$,
$0<\overline Z_{\mathfrak k}(\ridge)\le\gamma_\star C_\Sigma^2$, and under
\cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-double-total}
\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z_{\mathfrak k}(\ridge)}\longrightarrow0,\qquad
\sup_{\ridge\in I}\abs{\EE Z^{\mathrm c}(\ridge)-\overline Z_{\mathfrak k}(\ridge)}\longrightarrow0 .
\end{equation}
\end{enumerate}
\end{corollary}
```
-/
theorem thm_app_vol_double_same_ii_indep (cert : Muon.External.GaussianOpNorm)
    (γstar CSig γout γin : ℝ) (hCSig : 1 ≤ CSig)
    (m n B : ℕ → ℕ) (Fp : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hSize : SizeSeq (B := B) (fun k => (Fp k).C) γstar CSig γout γin)
    (b : ℝ) (hb : b < 1) (hβ : ∀ k, (Fp k).β ≤ b)
    (hout : ∀ k, (Fp k).C.Sout ≠ 0) (hin : ∀ k, (Fp k).C.Sin ≠ 0)
    (ν ν' : ∀ k, FiniteMeasure ℝ)
    (hν : ∀ k, (ν k : Measure ℝ) = Muon.nuOut (Fp k).C (B k))
    (hν' : ∀ k, (ν' k : Measure ℝ) = Muon.nuIn (Fp k).C (B k))
    (J : Set ℝ) (hJ : IsCompact J) (hJpos : J ⊆ Set.Ioi 0) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ s ∈ J, ∀ u ∈ J,
      |(∫ ω, contractionRes (B k) (Fp k).C.Sout (Fp k).C.Sin s u
            (def_app_vol_product (Fp k) ω t) (def_app_vol_product (Fp k) ω t)
          ∂(indepSpaceLaw (m k) (n k) (B k))) -
        kernelK (Fp k).β (Fp k).C (B k) (ν k) (ν' k) s u| ≤ ε) ∧
    (∀ᶠ k in atTop, ∀ t : ℤ, ∀ s ∈ J, ∀ u ∈ J,
      Integrable (fun ω => contractionRes (B k) (Fp k).C.Sout (Fp k).C.Sin s u
        (def_app_vol_product (Fp k) ω t) (def_app_vol_product (Fp k) ω t))
        (indepSpaceLaw (m k) (n k) (B k))) := by
  have hCpos : 0 < CSig := by linarith
  let Sp : ∀ k, SpectralData (Fp k).C := fun k => (dsii_spec_exists (Fp k).C).some
  refine ⟨fun ε hε => ?_, Filter.Eventually.of_forall fun k t s hs u hu => ?_⟩
  · -- OBSTRUCTION: `thm_app_vol_lag_kernel_closure_indep` needs a uniform momentum bound
    -- `β_k ≤ b < 1`, which `SizeSeq` does not provide.
    obtain ⟨b, hb, hβb⟩ : ∃ b : ℝ, b < 1 ∧ ∀ k, (Fp k).β ≤ b := ⟨b, hb, hβ⟩
    have hcl := (thm_app_vol_lag_kernel_closure_indep cert γstar CSig γout γin hCSig 1 1
      ⟨one_pos, le_rfl⟩ m n B Fp Sp hSize b hb hβb 0 J hJ hJpos).1
    filter_upwards [hcl (ε / CSig ^ 2) (by positivity)] with k hk t s hs u hu
    obtain ⟨h1, h2, h3, h4⟩ := dsii_norm_facts (Fp k) (Sp k) CSig hCSig (hSize.1 k).2.1
      (hSize.1 k).2.2
    have := hk t s hs u hu _ _ _ _ h1 h2 h3 h4
    simp only [Nat.cast_zero, add_zero] at this
    exact dsii_red_pt cert γstar CSig (Fp k) (Sp k) (hSize.1 k) hCSig (hout k) (hin k) (ν k) (ν' k)
      (hν k) (hν' k) (indepSpaceLaw (m k) (n k) (B k)) (fun ω => def_app_vol_product (Fp k) ω t)
      s u ε (hJpos hs) (hJpos hu) this
  · haveI : IsProbabilityMeasure (indepSpaceLaw (m k) (n k) (B k)) := by
      unfold indepSpaceLaw; infer_instance
    exact dsii_integrable γstar CSig (Fp k) (Sp k) (hSize.1 k) hCSig _ _
      (dsii_product_aesm (Fp k) t) (hJpos hs) (hJpos hu)

/-- `thm:app-vol-double-same`, part (iii), fixed dimension, snapshot `cr-2026-10-23`. Declaration of
record: `∫∫ 𝔨(ϱ+x², ϱ+y²)` converges absolutely on `(0,∞)²` (the integrability that makes
`eqn:app-vol-Zk` meaningful; `zkK` is the Bochner-form iterated integral); `𝔷_𝔨(ϱ) = C̄_0(ϱ,ϱ)`, the
lag-zero filtered coefficient `lagResp` at `ω_ϱ, ω_ϱ` with tests `Σ_out, Σ_in`; and
`0 < 𝔷_𝔨(ϱ) ≤ γ⋆ C_Σ²`, for `ϱ > 0`. The standing assumptions are `SizeFin`, `Σ_out ≠ 0`,
`Σ_in ≠ 0`, `1 ≤ C_Σ`. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{corollary}[Same-time volatility, two anisotropic covariances]\label{thm:app-vol-double-same}
Assume the size conditions, and that $\Sigmaout\ne0$ and $\Sigmain\ne0$.
\begin{enumerate}[label=(\roman*)]
\item At every finite dimension, $\Upsilon(s)>0$ for $s>0$, and
$\mathfrak k=\mathfrak k_0[\Sigmaout,\Sigmain]$. In particular $\mathfrak k$ is positive,
symmetric and continuous on $(0,\infty)^2$, with
\begin{equation}\label{eqn:app-vol-kernel-bounds}
\mathfrak k(s,u)\le\frac{\gamma_\star C_\Sigma^2}{4\sqrt{su}} .
\end{equation}
\item Under \cref{assum:app-setup-regime}, for every compact
$\mathcal J\subset(0,\infty)$,
\begin{equation}\label{eqn:app-vol-double-kernel}
\sup_{s,u\in\mathcal J}\abs{\EE\,\mathcal K_{s,u}(\Mt,\Mt)-\mathfrak k(s,u)}\longrightarrow0 ,
\end{equation}
and the same holds with $\Mt$ replaced by $M^{\mathrm g}_t$ under the size
conditions.
\item The integral \cref{eqn:app-vol-Zk} converges, $\overline Z_{\mathfrak k}(\ridge)=\overline C_0(\ridge,\ridge)$,
$0<\overline Z_{\mathfrak k}(\ridge)\le\gamma_\star C_\Sigma^2$, and under
\cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-double-total}
\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z_{\mathfrak k}(\ridge)}\longrightarrow0,\qquad
\sup_{\ridge\in I}\abs{\EE Z^{\mathrm c}(\ridge)-\overline Z_{\mathfrak k}(\ridge)}\longrightarrow0 .
\end{equation}
\end{enumerate}
\end{corollary}
```
-/
theorem thm_app_vol_double_same_iii_identity (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut Fp.C B) (hν' : (ν' : Measure ℝ) = Muon.nuIn Fp.C B)
    (ϱ : ℝ) (hϱ : 0 < ϱ) :
    IntegrableOn (fun p : ℝ × ℝ => kernelK Fp.β Fp.C B ν ν' (ϱ + p.1 ^ 2) (ϱ + p.2 ^ 2))
        (Ioi 0 ×ˢ Ioi 0) ∧
      zkK Fp.β Fp.C B ν ν' ϱ =
        lagResp cert γstar CSig Fp.β 0 B S.μ S.lam S.μ S.lam (omegaF ϱ) (omegaF ϱ) ∧
      0 < zkK Fp.β Fp.C B ν ν' ϱ ∧
      zkK Fp.β Fp.C B ν ν' ϱ ≤ γstar * CSig ^ 2 := by
  have hker := (thm_app_vol_double_same_i cert γstar CSig Fp S hS hCSig hout hin ν ν' hν hν').2.1
  have hpos := (thm_app_vol_double_same_i cert γstar CSig Fp S hS hCSig hout hin ν ν' hν hν').2.2.2.1
  have hf := thm_app_vol_closed_filtered_i cert γstar CSig Fp S hS hCSig 0 S.μ S.lam ϱ ϱ hϱ hϱ
  have hint : IntegrableOn
      (fun p : ℝ × ℝ => kernelK Fp.β Fp.C B ν ν' (ϱ + p.1 ^ 2) (ϱ + p.2 ^ 2))
      (Ioi 0 ×ˢ Ioi 0) := by
    refine hf.1.congr ?_
    exact Filter.Eventually.of_forall fun p => (hker _ _ (by positivity) (by positivity)).symm
  have hid : zkK Fp.β Fp.C B ν ν' ϱ =
      lagResp cert γstar CSig Fp.β 0 B S.μ S.lam S.μ S.lam (omegaF ϱ) (omegaF ϱ) := by
    unfold zkK
    rw [hf.2]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => integral_congr_ae
      (Filter.Eventually.of_forall fun y => hker _ _ (by positivity) (by positivity))
  have hiter : 0 < ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
      kernelK Fp.β Fp.C B ν ν' (ϱ + x ^ 2) (ϱ + y ^ 2) := by
    rw [← setIntegral_prod _ hint]
    refine (integral_pos_iff_support_of_nonneg ?_ hint).2 ?_
    · intro p
      exact (hpos _ _ (by positivity) (by positivity)).le
    · have hsupp : Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) ⊆ Function.support
          (fun p : ℝ × ℝ => kernelK Fp.β Fp.C B ν ν' (ϱ + p.1 ^ 2) (ϱ + p.2 ^ 2)) := by
        intro p hp
        exact (hpos _ _ (by positivity) (by positivity)).ne'
      have hm : ((volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))
          (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) ≤
          ((volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))
            (Function.support
              (fun p : ℝ × ℝ => kernelK Fp.β Fp.C B ν ν' (ϱ + p.1 ^ 2) (ϱ + p.2 ^ 2))) :=
        measure_mono hsupp
      have hfull : ((volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))
          (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) = ⊤ := by
        rw [Measure.restrict_apply (measurableSet_Ioi.prod measurableSet_Ioi)]
        rw [inter_self]
        rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod]
        simp
      rw [hfull] at hm
      exact ENNReal.zero_lt_top.trans_le hm
  have hzk : 0 < zkK Fp.β Fp.C B ν ν' ϱ := by
    unfold zkK
    exact mul_pos (by positivity) hiter
  have hbound := (thm_app_vol_integrated_ii cert γstar CSig Fp S hS hCSig ϱ ϱ
    ⟨hϱ, le_rfl⟩ Fp.C.Sout Fp.C.Sin S.μ S.lam (Sout_eq_spectral S)
      (Sin_eq_spectral S) ϱ ϱ ⟨le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl⟩).1
  have hγ : 0 ≤ γstar := by
    have hm : (0 : ℝ) ≤ (max m n : ℕ) := Nat.cast_nonneg _
    have hBr : (0 : ℝ) < B := by exact_mod_cast Fp.hB
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg hBr
    linarith [hS.1]
  have hub : zkK Fp.β Fp.C B ν ν' ϱ ≤ γstar * CSig ^ 2 := by
    rw [hid]
    refine (le_abs_self _).trans (hbound.trans ?_)
    rw [pow_two, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hS.2.1 hS.2.2 (dsi_opNorm_nonneg _) ((dsi_opNorm_nonneg _).trans hS.2.1)) hγ
  exact ⟨hint, hid, hzk, hub⟩

/-! ### Private helpers for `thm_app_vol_double_same_iii_limit` (task P-D.19.P3) -/

private lemma dsiii_borel (m n : ℕ) : BorelSpace (Mat m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))

private lemma dsiii_sc (m n : ℕ) : SecondCountableTopology (Mat m n) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))

private lemma dsiii_batch_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    Measurable (frozenBatchG F S s) := by
  haveI := dsiii_borel m n
  haveI := dsiii_sc m n
  unfold frozenBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : Vec m × Vec n =>
      (dotProduct p.1 (Matrix.mulVec F.A p.2)) • (rOut F.C * outer p.1 p.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (S.meas s a)

private lemma dsiii_tsum_meas {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (f : ℕ → Ω → Mat m n) (hf : ∀ j, Measurable (f j)) : Measurable (fun ω => ∑' j, f j ω) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  exact Measurable.tsum hf

private lemma dsiii_buf_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) :
    Measurable (frozenBuf F S t) := by
  unfold frozenBuf
  exact dsiii_tsum_meas _ fun j => (dsiii_batch_meas F S _).const_smul (emaW F.β j)

private lemma dsiii_Q_meas {m n : ℕ} {ϱ : ℝ} (hϱ : 0 ≤ ϱ) :
    Measurable (fun K : Mat m n => Q ϱ K) :=
  (measurable_Q (m := m) (n := n)).comp
    ((measurable_const (a := (⟨ϱ, hϱ⟩ : Set.Ici (0 : ℝ)))).prodMk measurable_id)

private lemma dsiii_stat {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} (X : ℤ → Ω → E) (hst : StrictlyStationary P X)
    (Φ : (ℤ → E) → ℝ) (hΦ : Measurable Φ) (k : ℤ) :
    ∫ ω, Φ (fun t => X (t + k) ω) ∂P = ∫ ω, Φ (fun t => X t ω) ∂P := by
  have hsh : Measurable (fun x : ℤ → E => fun t => x (t + k)) :=
    measurable_pi_iff.mpr (fun t => measurable_pi_apply (t + k))
  have h1 : AEMeasurable (fun ω t => X (t + k) ω) P := hsh.comp_aemeasurable hst.1
  calc ∫ ω, Φ (fun t => X (t + k) ω) ∂P
      = ∫ x, Φ x ∂(P.map (fun ω t => X (t + k) ω)) :=
        (integral_map h1 hΦ.aestronglyMeasurable).symm
    _ = ∫ x, Φ x ∂(P.map (fun ω t => X t ω)) := by rw [hst.2 k]
    _ = ∫ ω, Φ (fun t => X t ω) ∂P := integral_map hst.1 hΦ.aestronglyMeasurable

private lemma dsiii_mean_shift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (s k : ℤ) :
    mean P (frozenUpd F S ϱ (s + k)) = mean P (frozenUpd F S ϱ s) := by
  haveI := dsiii_borel m n
  haveI := dsiii_sc m n
  have hst := (lem_app_setup_ema_law_ii F S).2
  ext i j
  simp only [mean, Matrix.of_apply]
  have h := dsiii_stat (frozenBuf F S) hst (fun x => Q ϱ (x s) i j) (by
    have h1 : Measurable (fun x : ℤ → Mat m n => Q ϱ (x s)) :=
      (dsiii_Q_meas hϱ).comp (measurable_pi_apply s)
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp h1)) k
  simpa [frozenUpd] using h

private lemma dsiii_fro_add {m n : ℕ} (A D : Mat m n) : fro (A + D) ≤ fro A + fro D := by
  open scoped Matrix.Norms.Frobenius in
  rw [fro_eq_norm, fro_eq_norm, fro_eq_norm]
  exact norm_add_le _ _

private lemma dsiii_le_biSup {f : ℝ → ℝ} {I : Set ℝ} (hb : BddAbove (f '' I))
    {s : ℝ} (hs : s ∈ I) : f s ≤ ⨆ s ∈ I, f s := by
  obtain ⟨b, hb'⟩ := hb
  have hbdd : BddAbove (Set.range fun s => ⨆ (_ : s ∈ I), f s) := by
    refine ⟨max b 0, ?_⟩
    rintro _ ⟨s', rfl⟩
    show (⨆ (_ : s' ∈ I), f s') ≤ max b 0
    by_cases hs' : s' ∈ I
    · rw [ciSup_pos hs']
      exact le_max_of_le_left (hb' ⟨s', hs', rfl⟩)
    · haveI : IsEmpty (s' ∈ I) := ⟨hs'⟩
      rw [Real.iSup_of_isEmpty]
      exact le_max_right _ _
  refine le_ciSup_of_le hbdd s ?_
  rw [ciSup_pos hs]

private lemma dsiii_def_lag_scale {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (ℓ : ℕ) (t : ℤ) (Fo : Mat m m) (Gi : Mat n n) (c d ϱ ϱ' : ℝ) :
    def_app_vol_lag F S ℓ t (c • Fo) (d • Gi) ϱ ϱ' =
      c * d * def_app_vol_lag F S ℓ t Fo Gi ϱ ϱ' := by
  unfold def_app_vol_lag
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul]
  ring

private lemma dsiii_red_lag (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Fp : FrozenParams m n B) (S : FrozenSamples P m n B) (Sp : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (t : ℤ) (ϱ ε : ℝ) (hϱ : 0 < ϱ)
    (hcl : |def_app_vol_lag Fp S 0 t (CSig⁻¹ • Fp.C.Sout) (CSig⁻¹ • Fp.C.Sin) ϱ ϱ -
      lagResp cert γstar CSig Fp.β 0 B Sp.μ Sp.lam (fun i => CSig⁻¹ * Sp.μ i)
        (fun j => CSig⁻¹ * Sp.lam j) (omegaF ϱ) (omegaF ϱ)| ≤ ε / CSig ^ 2) :
    |def_app_vol_lag Fp S 0 t Fp.C.Sout Fp.C.Sin ϱ ϱ -
      lagResp cert γstar CSig Fp.β 0 B Sp.μ Sp.lam Sp.μ Sp.lam (omegaF ϱ) (omegaF ϱ)| ≤ ε := by
  have hpos : 0 < CSig := by linarith
  rw [dsiii_def_lag_scale,
    dsii_lagResp_scale cert γstar CSig Fp Sp hS hCSig 0 CSig⁻¹ CSig⁻¹
      (omegaF ϱ) (omegaF ϱ) (lem_app_vol_sharp_ii hϱ hϱ).2.1
      (lem_app_vol_sharp_ii hϱ hϱ).2.1] at hcl
  have heq : CSig⁻¹ * CSig⁻¹ * def_app_vol_lag Fp S 0 t Fp.C.Sout Fp.C.Sin ϱ ϱ -
      CSig⁻¹ * CSig⁻¹ * lagResp cert γstar CSig Fp.β 0 B Sp.μ Sp.lam Sp.μ Sp.lam
        (omegaF ϱ) (omegaF ϱ) = (CSig⁻¹ * CSig⁻¹) *
      (def_app_vol_lag Fp S 0 t Fp.C.Sout Fp.C.Sin ϱ ϱ -
        lagResp cert γstar CSig Fp.β 0 B Sp.μ Sp.lam Sp.μ Sp.lam (omegaF ϱ) (omegaF ϱ)) := by ring
  rw [heq, abs_mul, abs_of_pos (mul_pos (inv_pos.mpr hpos) (inv_pos.mpr hpos))] at hcl
  have := mul_le_mul_of_nonneg_left hcl (show 0 ≤ CSig ^ 2 by positivity)
  field_simp at this
  exact this

private lemma dsiii_contraction_integrable {m n B : ℕ} (γstar CSig : ℝ)
    (Fp : FrozenParams m n B) (Sp : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (M : Ω → Mat m n) (hM : AEStronglyMeasurable M μ) (f g : ℝ → ℝ)
    (hf : IsOddBddLip f) (hg : IsOddBddLip g) :
    Integrable (fun ω => contraction B Fp.C.Sout Fp.C.Sin f g (M ω) (M ω)) μ := by
  have hpos : 0 < CSig := by linarith
  obtain ⟨-, -, hF, hG⟩ := dsii_norm_facts Fp Sp CSig hCSig hS.2.1 hS.2.2
  have hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B :=
    le_trans (by exact_mod_cast (min_le_left m n).trans (le_max_left m n)) hS.1
  have hpt : ∀ ω, contraction B Fp.C.Sout Fp.C.Sin f g (M ω) (M ω) =
      CSig ^ 2 * contraction B (CSig⁻¹ • Fp.C.Sout) (CSig⁻¹ • Fp.C.Sin) f g (M ω) (M ω) := by
    intro ω
    unfold contraction
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    field_simp
  simp_rw [hpt]
  refine Integrable.const_mul ?_ _
  refine Integrable.of_bound (C := γstar * supNorm f * supNorm g) ?_ ?_
  · have hc : Continuous (fun K : Mat m n => contraction B (CSig⁻¹ • Fp.C.Sout)
        (CSig⁻¹ • Fp.C.Sin) f g K K) := by
      unfold contraction
      exact continuous_const.mul
        ((((continuous_const.matrix_mul (dsii_oddSharp_cont f hf)).matrix_mul
          continuous_const).matrix_mul (dsii_oddSharp_cont g hg).matrix_transpose).matrix_trace)
    exact hc.comp_aestronglyMeasurable hM
  · exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact lem_app_vol_finite_i Fp.hB γstar hdim _ _ hF hG f g hf hg _ _

private lemma dsiii_integrable_totals {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (γstar CSig ϱlo ϱhi εB : ℝ)
    (Fp : FrozenParams m n B) (S : FrozenSamples P m n B) (Sp : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hmean : ∀ s : ℤ, ∀ r ∈ Icc ϱlo ϱhi,
      fro (Muon.mean P (frozenUpd Fp S r s)) ≤ CSig / Real.sqrt ϱlo + εB)
    (t : ℤ) (ϱ : ℝ) (hϱlo : 0 < ϱlo) (hϱI : ϱ ∈ Icc ϱlo ϱhi) :
    Integrable (fun ω => sameTimeZ Fp S ϱ t ω) P ∧
      Integrable (fun ω => sameTimeZc Fp S ϱ t ω) P := by
  have hϱ : 0 < ϱ := hϱlo.trans_le hϱI.1
  have hraw0 := dsiii_contraction_integrable γstar CSig Fp Sp hS hCSig P
    (frozenBuf Fp S t) (dsii_frozenBuf_aesm Fp S t) (omegaF ϱ) (omegaF ϱ)
    (lem_app_vol_sharp_ii hϱ hϱ).2.1 (lem_app_vol_sharp_ii hϱ hϱ).2.1
  have hraw : Integrable (fun ω => sameTimeZ Fp S ϱ t ω) P := by
    convert hraw0 using 1
    funext ω
    unfold sameTimeZ frozenUpd Muon.Setup.pairSigma contraction
    rw [← eqn_app_vol_filters_sharp_ii hϱ]
  have hupd : AEStronglyMeasurable (frozenUpd Fp S ϱ t) P := by
    have hm := (dsii_oddSharp_cont (omegaF ϱ) (lem_app_vol_sharp_ii hϱ hϱ).2.1)
      |>.comp_aestronglyMeasurable (dsii_frozenBuf_aesm Fp S t)
    convert hm using 1
    funext ω
    exact (eqn_app_vol_filters_sharp_ii hϱ _).symm
  have hcenUpd : AEStronglyMeasurable (centredUpd Fp S ϱ t) P :=
    hupd.sub aestronglyMeasurable_const
  have hccont : Continuous (fun X : Mat m n => (B : ℝ)⁻¹ * Muon.Setup.pairSigma Fp.C X X) := by
    unfold Muon.Setup.pairSigma
    fun_prop
  have hcmeas : AEStronglyMeasurable (fun ω => sameTimeZc Fp S ϱ t ω) P := by
    exact hccont.comp_aestronglyMeasurable hcenUpd
  let c := CSig ^ 2 * (4 * Real.sqrt γstar / Real.sqrt B *
      (CSig / Real.sqrt ϱlo + εB) + (CSig / Real.sqrt ϱlo + εB) ^ 2 / B)
  have hdiff : Integrable (fun ω => sameTimeZ Fp S ϱ t ω - sameTimeZc Fp S ϱ t ω) P := by
    refine Integrable.of_bound (C := c) (hraw.aestronglyMeasurable.sub hcmeas) ?_
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact lem_app_vol_centering_ii Fp S t γstar CSig ϱlo ϱhi εB hS hϱlo hmean ω ϱ hϱI
  refine ⟨hraw, ?_⟩
  have hi := hraw.sub hdiff
  refine hi.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.sub_apply]
  ring

/-- `thm:app-vol-double-same`, part (iii), limit, snapshot `cr-2026-10-23`. Declaration of record:
under `assum:app-setup-regime` (`SetupRegime R`, with `Σ_out ≠ 0`, `Σ_in ≠ 0` at every index), the
means of `Z(ϱ)` and `Z^c(ϱ)` (`sameTimeZ`, `sameTimeZc`, `eqn:app-vol-Z`) are integrable, and
`sup_{ϱ∈I} |𝔼 Z(ϱ) − 𝔷_𝔨(ϱ)| → 0` and `sup_{ϱ∈I} |𝔼 Z^c(ϱ) − 𝔷_𝔨(ϱ)| → 0`, in the `ε`-form, for all `t`.
Here `I = [ϱlo, ϱhi]` is the regime interval. LaTeX, verbatim from `section.tex` (the whole
environment):

```latex
\begin{corollary}[Same-time volatility, two anisotropic covariances]\label{thm:app-vol-double-same}
Assume the size conditions, and that $\Sigmaout\ne0$ and $\Sigmain\ne0$.
\begin{enumerate}[label=(\roman*)]
\item At every finite dimension, $\Upsilon(s)>0$ for $s>0$, and
$\mathfrak k=\mathfrak k_0[\Sigmaout,\Sigmain]$. In particular $\mathfrak k$ is positive,
symmetric and continuous on $(0,\infty)^2$, with
\begin{equation}\label{eqn:app-vol-kernel-bounds}
\mathfrak k(s,u)\le\frac{\gamma_\star C_\Sigma^2}{4\sqrt{su}} .
\end{equation}
\item Under \cref{assum:app-setup-regime}, for every compact
$\mathcal J\subset(0,\infty)$,
\begin{equation}\label{eqn:app-vol-double-kernel}
\sup_{s,u\in\mathcal J}\abs{\EE\,\mathcal K_{s,u}(\Mt,\Mt)-\mathfrak k(s,u)}\longrightarrow0 ,
\end{equation}
and the same holds with $\Mt$ replaced by $M^{\mathrm g}_t$ under the size
conditions.
\item The integral \cref{eqn:app-vol-Zk} converges, $\overline Z_{\mathfrak k}(\ridge)=\overline C_0(\ridge,\ridge)$,
$0<\overline Z_{\mathfrak k}(\ridge)\le\gamma_\star C_\Sigma^2$, and under
\cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-double-total}
\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z_{\mathfrak k}(\ridge)}\longrightarrow0,\qquad
\sup_{\ridge\in I}\abs{\EE Z^{\mathrm c}(\ridge)-\overline Z_{\mathfrak k}(\ridge)}\longrightarrow0 .
\end{equation}
\end{enumerate}
\end{corollary}
```
-/
theorem thm_app_vol_double_same_iii_limit (cert : Muon.External.GaussianOpNorm)
    (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (hout : ∀ k, (R.F k).C.Sout ≠ 0) (hin : ∀ k, (R.F k).C.Sin ≠ 0)
    (ν ν' : ∀ k, FiniteMeasure ℝ)
    (hν : ∀ k, (ν k : Measure ℝ) = Muon.nuOut (R.F k).C (R.B k))
    (hν' : ∀ k, (ν' k : Measure ℝ) = Muon.nuIn (R.F k).C (R.B k)) :
    (∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi,
      Integrable (fun ω => sameTimeZ (R.F k) (S k) ϱ t ω) (P k) ∧
      Integrable (fun ω => sameTimeZc (R.F k) (S k) ϱ t ω) (P k)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi,
      |(∫ ω, sameTimeZ (R.F k) (S k) ϱ t ω ∂(P k)) -
        zkK (R.F k).β (R.F k).C (R.B k) (ν k) (ν' k) ϱ| ≤ ε) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi,
      |(∫ ω, sameTimeZc (R.F k) (S k) ϱ t ω ∂(P k)) -
        zkK (R.F k).β (R.F k).C (R.B k) (ν k) (ν' k) ϱ| ≤ ε) := by
  have hSz : ∀ k, SizeFin (R.F k).C (R.B k) R.γstar R.CSig :=
    fun k => ⟨R.dims k, R.normOut k, R.normIn k⟩
  let Sp : ∀ k, SpectralData (R.F k).C := fun k => (dsii_spec_exists (R.F k).C).some
  have hcl := (thm_app_vol_lag_kernel_closure_actual cert R Ω P S Sp 0
    (Icc R.ϱlo R.ϱhi) isCompact_Icc (fun _ h => R.hϱ.1.trans_le h.1)).2
  let εB : ℕ → ℝ := fun k => Muon.Drift.epsB (emaW R.β) (R.F k) (S k) 0
    (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) R.ϱlo R.ϱhi
  let a : ℕ → ℝ := fun k => R.CSig / Real.sqrt R.ϱlo + εB k
  let c : ℕ → ℝ := fun k => R.CSig ^ 2 *
    (4 * Real.sqrt R.γstar / Real.sqrt (R.B k) * a k + (a k) ^ 2 / R.B k)
  have hm := Muon.Drift.thm_app_drift_mean R P S 0
  have hεB : Tendsto εB atTop (𝓝 0) := hm.2.2.1
  have hmean : ∀ k, ∀ s : ℤ, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      fro (Muon.mean (P k) (frozenUpd (R.F k) (S k) ϱ s)) ≤ a k := by
    intro k s ϱ hϱI
    have he : fro (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) 0 ϱ -
        Muon.Drift.Gbar (emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) ϱ) ≤ εB k := dsiii_le_biSup (hm.2.1 k) hϱI
    have hg := (hm.1 k ϱ hϱI).2
    have hsqrt : R.CSig / Real.sqrt ϱ ≤ R.CSig / Real.sqrt R.ϱlo :=
      div_le_div_of_nonneg_left (by linarith [R.hC]) (Real.sqrt_pos.mpr R.hϱ.1)
        (Real.sqrt_le_sqrt hϱI.1)
    have hadd := dsiii_fro_add
      (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) 0 ϱ -
        Muon.Drift.Gbar (emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) ϱ)
      (Muon.Drift.Gbar (emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) ϱ)
    rw [sub_add_cancel] at hadd
    have heq : Muon.Drift.EQ (emaW R.β) (R.F k) (S k) 0 ϱ =
        Muon.mean (P k) (frozenUpd (R.F k) (S k) ϱ 0) := by
      unfold Muon.Drift.EQ
      congr 1
      funext ω
      unfold frozenUpd WeightedBuf frozenBuf
      rw [R.hβ k]
    rw [heq] at hadd he
    have hzero : fro (Muon.mean (P k) (frozenUpd (R.F k) (S k) ϱ 0)) ≤ a k := by
      dsimp only [a]
      linarith
    have hshift := dsiii_mean_shift (R.F k) (S k) (R.hϱ.1.le.trans hϱI.1) 0 s
    rw [zero_add] at hshift
    rw [hshift]
    exact hzero
  have hBtop : Tendsto (fun k => (R.B k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp R.prop.B_top
  have hBi : Tendsto (fun k => (R.B k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hBtop
  have hBsi : Tendsto (fun k => (Real.sqrt (R.B k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hBtop)
  have ha : Tendsto a atTop (𝓝 (R.CSig / Real.sqrt R.ϱlo)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hεB
  have hc1 : Tendsto (fun k => 4 * Real.sqrt R.γstar / Real.sqrt (R.B k) * a k)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_mul] using
      (tendsto_const_nhds.mul hBsi).mul ha
  have hc2 : Tendsto (fun k => (a k) ^ 2 / R.B k) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (ha.pow 2).mul hBi
  have hc : Tendsto c atTop (𝓝 0) := by
    simpa only [c, add_zero, mul_zero] using (hc1.add hc2).const_mul (R.CSig ^ 2)
  have hint : ∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      Integrable (fun ω => sameTimeZ (R.F k) (S k) ϱ t ω) (P k) ∧
      Integrable (fun ω => sameTimeZc (R.F k) (S k) ϱ t ω) (P k) :=
    Filter.Eventually.of_forall fun k t ϱ hϱI =>
      dsiii_integrable_totals R.γstar R.CSig R.ϱlo R.ϱhi (εB k) (R.F k) (S k) (Sp k)
        (hSz k) R.hC (hmean k) t ϱ R.hϱ.1 hϱI
  have hcentered : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      |(∫ ω, sameTimeZc (R.F k) (S k) ϱ t ω ∂(P k)) -
        zkK (R.F k).β (R.F k).C (R.B k) (ν k) (ν' k) ϱ| ≤ ε := by
    intro ε hε
    have hCpos : 0 < R.CSig := zero_lt_one.trans_le R.hC
    have hn := hcl (ε / R.CSig ^ 2) (div_pos hε (sq_pos_of_pos hCpos))
    filter_upwards [hn] with k hk
    intro t ϱ hϱI
    obtain ⟨h1, h2, h3, h4⟩ :=
      dsii_norm_facts (R.F k) (Sp k) R.CSig R.hC (R.normOut k) (R.normIn k)
    have hsmall := hk t ϱ hϱI ϱ hϱI _ _ _ _ h1 h2 h3 h4
    have hred := dsiii_red_lag cert R.γstar R.CSig (R.F k) (S k) (Sp k) (hSz k) R.hC
      t ϱ ε (R.hϱ.1.trans_le hϱI.1) hsmall
    have hz := (thm_app_vol_double_same_iii_identity cert R.γstar R.CSig (R.F k) (Sp k)
      (hSz k) R.hC (hout k) (hin k) (ν k) (ν' k) (hν k) (hν' k) ϱ
      (R.hϱ.1.trans_le hϱI.1)).2.1
    have heq : (∫ ω, sameTimeZc (R.F k) (S k) ϱ t ω ∂(P k)) =
        def_app_vol_lag (R.F k) (S k) 0 t (R.F k).C.Sout (R.F k).C.Sin ϱ ϱ := by
      unfold sameTimeZc def_app_vol_lag Muon.Setup.pairSigma
      rw [integral_const_mul]
      simp
    rw [heq, hz]
    exact hred
  refine ⟨hint, ?_, hcentered⟩
  intro ε hε
  have hcsmall : ∀ᶠ k in atTop, c k < ε / 2 :=
    (tendsto_order.1 hc).2 (ε / 2) (by positivity)
  have hclose := hcentered (ε / 2) (by positivity)
  filter_upwards [hint, hcsmall, hclose] with k hkint hck hkclose
  intro t ϱ hϱI
  have hkint' := hkint t ϱ hϱI
  have hkclose' := hkclose t ϱ hϱI
  have hpt := lem_app_vol_centering_ii (R.F k) (S k) t R.γstar R.CSig R.ϱlo R.ϱhi
    (εB k) (hSz k) R.hϱ.1 (hmean k)
  have hdiff : |(∫ ω, sameTimeZ (R.F k) (S k) ϱ t ω ∂(P k)) -
      (∫ ω, sameTimeZc (R.F k) (S k) ϱ t ω ∂(P k))| ≤ c k := by
    rw [← integral_sub hkint'.1 hkint'.2, ← Real.norm_eq_abs]
    have hb := norm_integral_le_of_norm_le_const (μ := P k)
      (f := fun ω => sameTimeZ (R.F k) (S k) ϱ t ω - sameTimeZc (R.F k) (S k) ϱ t ω)
      (C := c k) (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs, c, a] using hpt ω ϱ hϱI)
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using hb
  have htri := abs_sub_le
    (∫ ω, sameTimeZ (R.F k) (S k) ϱ t ω ∂(P k))
    (∫ ω, sameTimeZc (R.F k) (S k) ϱ t ω ∂(P k))
    (zkK (R.F k).β (R.F k).C (R.B k) (ν k) (ν' k) ϱ)
  linarith [hkclose']

end Muon.Volatility

end

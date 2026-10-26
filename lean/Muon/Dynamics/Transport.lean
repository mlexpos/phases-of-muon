import Muon.Dynamics.FiniteMean
import Muon.Volatility.LagReduction
import Muon.External.Certificates
import Muon.Dynamics.Causal
import Muon.Setup.Algorithm
import Muon.Setup.RegularizedMap

/-!
# Appendix E, work package L-E.9: transport along the algorithm

Snapshot `cr-2026-10-23`. Source: `sections/05-dynamics/section.tex`, subsection "Transport, concentration
and diffuseness along the algorithm": `lem:app-dyn-movement` (ll. 1496–1506), `lem:app-dyn-buffer`
(ll. 1531–1539), `lem:app-dyn-coupling` (ll. 1557–1571), `lem:app-dyn-startup` (ll. 1614–1623),
`lem:app-dyn-taylor` (ll. 1656–1663), `lem:app-dyn-quadratic` (ll. 1995–2004). Card:
`sections/05-dynamics/CARD.md` §2, §3, §5 (L-E.9). Interface draft: every proof is `sorry`.

Representation choices:
* Standing hypotheses. "From here on the hypotheses (H1)–(H4) of `thm:app-dyn-main` are in force"
  (l. 1472). They are bundled per dimension in `DynSetup`, with one field group per hypothesis. (H1) enters
  as `SizeFin` (the finite-dimensional size conditions, as in `Muon.Dynamics.Chains`); the proportional
  regime and the convergence of aspect ratios are asymptotic and are not restated (see open questions).
* Sample model. The batch of algorithm step `u` is the physical batch of `cs.act (u+1)`, because the
  gradient of step `u` is `G°_{u+1}` (`def:app-setup-algorithm`, `Muon.Dynamics.ChainSamples`). The same
  family drives the frozen chains, so the actual process and the chains of `def:app-dyn-chains` share their
  batches, as the source's coupling requires. Auxiliary batches are `cs.aux`.
* Indexing. `dynState S t` is the state before step `t`, so `dynBuf S t = M°_{t-1}` and the buffer after
  step `t` is `dynBuf S (t+1)`. `dynDelta S t = Δ_t` and `dynUpd S t = 𝖲_t` (update of step `t`).
* Past. `dynPast S t` is `𝓕_t` (`section.tex` l. 72): the batches of steps `0, …, t-1` and the initial buffer.
* Conditioning on `{Δ_t ∈ K}`. The source writes `𝔼_t` on the event `{Δ_t ∈ K}`; we write the conditional
  expectation of the indicator of that event, which equals `1_{A} 𝔼_t[·]` because `A ∈ 𝓕_t`.
* Integrability. Every expectation and conditional expectation carries an `Integrable` conjunct.
* Norms. An unsubscripted `‖·‖` is `opNorm`, `‖·‖_F` is `fro`, as in the source.
* Constants. `∃ K` (and `∃ B0`) come after the fixed parameters `p, r₋, r₊, E` and before the dimensions
  `m n B`, the covariances, the samples and the states (the source's constants depend only on those).
* `ℕ∞`-valued stopping times `τ` and `t_stop` are compared with `(t : ℕ∞)`.
-/

set_option linter.style.longLine false

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open Muon Muon.Setup Muon.Volatility

universe u

noncomputable section

namespace Muon.Dynamics

/-! ## Standing hypotheses of one dimension and the actual process -/

/-- The standing hypotheses (H1)–(H4) of `thm:app-dyn-main` at one dimension (`section.tex` ll. 340–352),
with the sample model of `Muon.Dynamics.ChainSamples`. Field groups:
* (H1) `hyp:app-dyn-data`: `SizeFin` (`max(N_out,N_in) ≤ γ⋆B`, `‖Σ_in‖,‖Σ_out‖ ≤ C_Σ`), and the batches
  `cs.act` are whitened standard Gaussian pairs, jointly independent (`ChainSamples`, `assum:data-target`);
* (H2) `hyp:app-dyn-algorithm`: momentum `β`, normalized ridge `ϱ`, step `η_t = h/B`;
* (H3) `hyp:app-dyn-initial`: deterministic `W₀`, `‖Δ₀‖_F² ≤ E⋆`, `r₀ ≤ 𝓡(0) ≤ r₁`;
  (`‖Â₀‖ → 0` is asymptotic and is not part of a single-dimension statement);
* (H4) `hyp:app-dyn-buffer`: the initial buffer `M°_{-1}` is independent of all actual batches and
  `E‖M°_{-1}‖_F² ≤ c_M B`. -/
structure DynSetup (p : DynParams) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (m n B : ℕ) where
  /-- The covariances `Σ_in`, `Σ_out`. -/
  C : Covariances m n
  /-- The algorithm parameters of `def:app-setup-algorithm`. -/
  alg : AlgParams m n
  /-- The sample family: actual batches (`cs.act (u+1)` for step `u`) and auxiliary batches. -/
  cs : ChainSamples P m n B
  /-- Deterministic initial parameter `W₀` (H3). -/
  W0 : Mat m n
  /-- Initial buffer `M°_{-1}` (H4). -/
  M0 : Ω → Mat m n
  /-- (H1): `max(N_out,N_in) ≤ γ⋆B`, `‖Σ_in‖,‖Σ_out‖ ≤ C_Σ`. -/
  size : SizeFin C B p.γstar p.CSig
  /-- (H2): momentum `β`. -/
  alg_β : alg.β = p.β
  /-- (H2): normalized ridge `ϱ`. -/
  alg_ϱ : alg.ϱ = p.ϱ
  /-- (H2): step `η_t = h/B`. -/
  alg_η : ∀ t, alg.η t = p.h / B
  /-- (H3): `‖Δ₀‖_F² ≤ E⋆`. -/
  W0_norm : fro (W0 - alg.Wstar) ^ 2 ≤ p.Estar
  /-- (H3): `r₀ ≤ 𝓡(0) ≤ r₁`. -/
  W0_risk : p.r0 ≤ riskSigma C (W0 - alg.Wstar) ∧ riskSigma C (W0 - alg.Wstar) ≤ p.r1
  /-- (H4): the initial buffer is a random matrix. -/
  M0_meas : Measurable M0
  /-- (H4): the initial buffer is independent of all actual batches (steps `u ≥ 0`) and of the
  auxiliary batches (`section.tex` ll. 129–131: the auxiliary family is independent of everything
  else, and `𝔼_t` integrates it). -/
  M0_indep : Indep (MeasurableSpace.comap M0 inferInstance)
    ((⨆ (s : ℤ) (_ : 1 ≤ s) (a : Fin B), MeasurableSpace.comap (cs.act s a) inferInstance) ⊔
      (⨆ (s : ℤ) (j : ℕ) (a : Fin B), MeasurableSpace.comap (cs.aux s j a) inferInstance)) P
  /-- (H4): `E‖M°_{-1}‖_F² ≤ c_M B`. -/
  M0_bound : ∫⁻ ω, ENNReal.ofReal (fro (M0 ω) ^ 2) ∂P ≤ ENNReal.ofReal (p.cM * B)

/-- Batch of algorithm step `u`: the physical batch of the sample `cs.act (u+1)`, whose gradient is
`G°_{u+1}` (`def:app-setup-algorithm`, `eqn:app-dyn-batch`). -/
def dynBatch {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (u : ℕ) : Ω → Batch m n B :=
  fun ω => physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω

/-- Initial state `(W₀, M°_{-1})` of the actual algorithm. -/
def dynStart {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) : Ω → AlgState m n :=
  fun ω => initState S.W0 (S.M0 ω)

/-- State before step `t` of the actual algorithm (`def:app-setup-algorithm`). -/
def dynState {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) : Ω → AlgState m n :=
  runRand S.C S.alg (dynStart S) (dynBatch S) t

/-- The actual error `Δ_t = W_t − W⋆` (`eqn:app-dyn-algorithm`). -/
def dynDelta {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) : Ω → Mat m n :=
  devRand S.C S.alg (dynStart S) (dynBatch S) t

/-- The actual update `𝖲_t = G̃_t` of step `t` (`eqn:app-setup-algorithm`). -/
def dynUpd {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) : Ω → Mat m n :=
  gtRand S.C S.alg (dynStart S) (dynBatch S) t

/-- The stopping time `t_stop` of the actual algorithm (`def:app-setup-algorithm`). -/
def dynStop {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) : Ω → ℕ∞ :=
  tstopRand S.C S.alg (dynStart S) (dynBatch S)

/-- The buffer `M°_{t-1}` used at step `t` (the `Mprev` component of the state before step `t`). -/
def dynBuf {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) : Ω → Mat m n :=
  fun ω => (dynState S t ω).Mprev

/-- The past `𝓕_t` at step `t` (`section.tex` l. 72): the batches of steps `0, …, t-1` (the samples
`cs.act s` with `1 ≤ s ≤ t`) and the initial buffer. -/
abbrev dynPast {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) : MeasurableSpace Ω :=
  (⨆ (s : ℤ) (_ : 1 ≤ s ∧ s ≤ (t : ℤ)) (a : Fin B), MeasurableSpace.comap (S.cs.act s a) inferInstance) ⊔
    MeasurableSpace.comap S.M0 inferInstance

/-- The event `{Δ_t ∈ 𝒦}` for `𝒦 = 𝒦(r₋, r₊, E)` given as a triple (`Muon.Dynamics.admSetOf`). -/
def dynInK {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) (K : ℝ × ℝ × ℝ) : Set Ω :=
  {ω | dynDelta S t ω ∈ admSetOf S.C K}

/-- The chains at time `t` with `D = Δ_t`, `M = M°_{t-1}` (`def:app-dyn-chains`), the same-buffer
chain `N̂_r = same (r+1)` at the actual state. -/
def dynHatN (p : DynParams) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t r : ℕ) : Ω → Mat m n :=
  fun ω => (def_app_dyn_chains p S.C S.cs t (dynDelta S t ω) (dynBuf S t ω) ω).same (r + 1)

/-- The same-buffer frozen update `V̂_r = sameV (r+1)` at the actual state (`def:app-dyn-chains`). -/
def dynHatV (p : DynParams) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t r : ℕ) : Ω → Mat m n :=
  fun ω => (def_app_dyn_chains p S.C S.cs t (dynDelta S t ω) (dynBuf S t ω) ω).sameV (r + 1)

/-- The buffer error `M°_{t+r} − N̂_r`, with `M°_{t+r}` the buffer after step `t+r`, i.e. `dynBuf S (t+r+1)`. -/
def dynErrM (p : DynParams) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t r : ℕ) : Ω → Mat m n :=
  fun ω => dynBuf S (t + r + 1) ω - dynHatN p S t r ω

/-- The update error `𝖲_{t+r} − V̂_r` (`lem:app-dyn-coupling`(i)). -/
def dynErrS (p : DynParams) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t r : ℕ) : Ω → Mat m n :=
  fun ω => dynUpd S (t + r) ω - dynHatV p S t r ω

/-- The frozen-update error `V̂_r − V_r`, with `V_r` the stationary update at `(t, Δ_t)`
(`lem:app-dyn-coupling`(ii)). -/
def dynErrV (p : DynParams) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t r : ℕ) : Ω → Mat m n :=
  fun ω => dynHatV p S t r ω - stationaryV p S.C S.cs t (dynDelta S t ω) r ω

/-- The block sum `𝓔 = ∑_{r<L}(𝖲_{t+r} − V_r)` with `L = blockLen B` and `V_r` the stationary chain at
`(t, Δ_t)` (`lem:app-dyn-coupling`(iii)–(iv), `lem:app-dyn-quadratic`). -/
def dynSumErr (p : DynParams) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) : Ω → Mat m n :=
  fun ω => ∑ r ∈ Finset.range (blockLen B),
    (dynUpd S (t + r) ω - stationaryV p S.C S.cs t (dynDelta S t ω) r ω)

/-- The stationary block sum `S = ∑_{r<L} V_r` at `(t, Δ_t)` (`lem:app-dyn-quadratic`). -/
def dynStatSum (p : DynParams) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) : Ω → Mat m n :=
  fun ω => ∑ r ∈ Finset.range (blockLen B), stationaryV p S.C S.cs t (dynDelta S t ω) r ω

/-- The tangent `V̇̂_r` of the same-buffer chain at `(t, Δ_t, M°_{t-1})`: the entrywise derivative
`Ṡ_r` of the causal chain (`lem:app-dyn-tangent`(iii), `lem:app-dyn-taylor`). -/
def dynTangent (p : DynParams) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t r : ℕ) : Ω → Mat m n :=
  fun ω => causalDot p S.C (fun s => physBatch S.C (S.cs.act s) ω) t
    (dynDelta S t ω) (dynBuf S t ω) r

/-! ## `lem:app-dyn-movement` -/

private lemma movement_fro_nn {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma movement_fro_transpose {k l : ℕ} (A : Mat k l) : fro Aᵀ = fro A := by
  unfold fro
  congr 1
  exact Finset.sum_comm

private lemma movement_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma movement_opNorm_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ opNorm A := by
  unfold opNorm
  exact norm_nonneg _

private lemma movement_fro_sq {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma movement_fro_mul_le_left {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ opNorm M * fro N := by
  have hcol : ∀ j : Fin r, ∑ i, (M * N) i j ^ 2 ≤ opNorm M ^ 2 * ∑ k, N k j ^ 2 := by
    intro j
    obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin q), ∀ k, v.ofLp k = N k j :=
      ⟨(EuclideanSpace.equiv (Fin q) ℝ).symm (fun k => N k j), fun k => rfl⟩
    have h1 : ‖(EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)‖ ≤ opNorm M * ‖v‖ := by
      rw [opNorm_eq_norm]
      exact Matrix.l2_opNorm_mulVec M v
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at h2
    have e1 : ∀ i, ((EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)).ofLp i = (M * N) i j := by
      intro i
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, hv]
    have e2 : ∑ k, v.ofLp k ^ 2 = ∑ k, N k j ^ 2 :=
      Finset.sum_congr rfl fun k _ => by rw [hv]
    simp only [e1, e2] at h2
    exact h2
  have hfro : fro (M * N) ^ 2 ≤ (opNorm M * fro N) ^ 2 := by
    rw [movement_fro_sq, mul_pow, movement_fro_sq, Finset.sum_comm]
    calc ∑ j, ∑ i, (M * N) i j ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, N k j ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, N k j ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (movement_fro_nn _) (mul_nonneg (movement_opNorm_nonneg M) (movement_fro_nn N))
    two_ne_zero).mp hfro

private lemma movement_fro_mul_le_right {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ fro M * opNorm N := by
  have h := movement_fro_mul_le_left Nᵀ Mᵀ
  rw [movement_opNorm_transpose, movement_fro_transpose, ← Matrix.transpose_mul, movement_fro_transpose] at h
  linarith [mul_comm (opNorm N) (fro M)]


open scoped Matrix.Norms.L2Operator in
private lemma movement_sqrt_norm {k : ℕ} (A : Mat k k) (hA : A.PosSemidef) :
    opNorm (CFC.sqrt A) ^ 2 = opNorm A := by
  have hh : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hs : CFC.sqrt A * CFC.sqrt A = A :=
    CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.mpr hA)
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (CFC.sqrt A)
  rw [hh, hs] at h
  simpa only [opNorm_eq_norm, pow_two] using h.symm

private lemma movement_Arot_bound (p : DynParams) {m n B : ℕ}
    (C : Covariances m n) (hsize : SizeFin C B p.γstar p.CSig) (D : Mat m n) :
    fro (Arot C D) ≤ p.CSig * fro D := by
  have ho := movement_sqrt_norm C.Sout C.psdOut
  have hi := movement_sqrt_norm C.Sin C.psdIn
  have hC : 0 ≤ p.CSig := le_trans (by norm_num) p.hC
  have hn : opNorm (rOut C) * opNorm (rIn C) ≤ p.CSig := by
    have h1 : 0 ≤ opNorm (rOut C) := movement_opNorm_nonneg _
    have h2 : 0 ≤ opNorm (rIn C) := movement_opNorm_nonneg _
    have h3 : opNorm (rOut C) ^ 2 ≤ p.CSig := ho.le.trans hsize.2.1
    have h4 : opNorm (rIn C) ^ 2 ≤ p.CSig := hi.le.trans hsize.2.2
    have hm := mul_le_mul h3 h4 (sq_nonneg (opNorm (rIn C))) hC
    nlinarith [mul_nonneg h1 h2]
  calc fro (Arot C D) ≤ (opNorm (rOut C) * fro D) * opNorm (rIn C) :=
      (movement_fro_mul_le_right _ _).trans
        (mul_le_mul_of_nonneg_right (movement_fro_mul_le_left _ _) (movement_opNorm_nonneg _))
    _ ≤ p.CSig * fro D := by nlinarith [movement_fro_nn D]

private lemma movement_risk_sqrt {m n : ℕ} (C : Covariances m n) (D : Mat m n) :
    Real.sqrt (2 * riskSigma C D) = fro (Arot C D) := by
  rw [eqn_app_setup_whitened_risk]
  ring_nf
  exact Real.sqrt_sq (movement_fro_nn _)

private lemma movement_risk_lip (p : DynParams) {m n B : ℕ}
    (C : Covariances m n) (hsize : SizeFin C B p.γstar p.CSig) (D F : Mat m n) :
    |Real.sqrt (2 * riskSigma C D) - Real.sqrt (2 * riskSigma C F)| ≤
      p.CSig * fro (D - F) := by
  rw [movement_risk_sqrt, movement_risk_sqrt]
  have he : Arot C (D - F) = Arot C D - Arot C F := by
    simp [Arot, Matrix.mul_sub, Matrix.sub_mul]
  open scoped Matrix.Norms.Frobenius in
    calc |fro (Arot C D) - fro (Arot C F)| ≤ fro (Arot C D - Arot C F) := by
          simp only [fro_eq_norm]
          exact abs_norm_sub_norm_le _ _
      _ ≤ p.CSig * fro (D - F) := he ▸ movement_Arot_bound p C hsize (D - F)

private lemma movement_update_bounds (p : DynParams) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) (t : ℕ) :
    opNorm (dynUpd S t ω) ≤ 1 ∧ fro (dynUpd S t ω) ≤ Real.sqrt (p.γstar * B) := by
  have hr : 0 ≤ riskSigma S.C (dynDelta S t ω) := by
    rw [eqn_app_setup_whitened_risk]
    positivity
  unfold dynUpd gtRand stepUpdate
  split_ifs with hz
  · simp [opNorm, fro]
    positivity
  · have hh : 0 ≤ 2 * riskSigma S.C (dynDelta S t ω) * S.alg.ϱ := by
      exact mul_nonneg (mul_nonneg (by norm_num) hr) S.alg.hϱ.le
    obtain ⟨ho, hf, hk, _⟩ := lem_app_setup_filter_i _ hh
      (stepBuffer S.alg (runRand S.C S.alg (dynStart S) (dynBatch S) t ω) (dynBatch S t ω))
    refine ⟨ho, ?_⟩
    have hmin : ((min m n : ℕ) : ℝ) ≤ p.γstar * B := by
      have hm : ((min m n : ℕ) : ℝ) ≤ ((max m n : ℕ) : ℝ) := by
        exact_mod_cast (min_le_max : min m n ≤ max m n)
      exact hm.trans S.size.1
    have hk' : ((stepBuffer S.alg (runRand S.C S.alg (dynStart S) (dynBatch S) t ω)
        (dynBatch S t ω)).rank : ℝ) ≤ ((min m n : ℕ) : ℝ) := by exact_mod_cast hk
    exact (Real.le_sqrt (movement_fro_nn _) (mul_nonneg p.hγ (Nat.cast_nonneg B))).mpr
      (hf.trans (hk'.trans hmin))

private lemma movement_delta_succ (p : DynParams) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) (t : ℕ) :
    dynDelta S (t + 1) ω = dynDelta S t ω - (p.h / B) • dynUpd S t ω := by
  change (run S.C S.alg _ _ (t + 1)).W - S.alg.Wstar = _
  simp only [run, step, dynDelta, devRand, dynUpd, gtRand, errorOf, runRand, S.alg_η]
  module

private lemma movement_accumulate {m n : ℕ} (D : ℕ → Mat m n) (N : Mat m n → ℝ)
    (a : ℝ) (hzero : N 0 = 0) (hadd : ∀ X Y, N (X + Y) ≤ N X + N Y)
    (hstep : ∀ u, N (D (u + 1) - D u) ≤ a) (t t' : ℕ) (ht : t ≤ t') :
    N (D t' - D t) ≤ a * ((t' : ℝ) - t) := by
  induction t', ht using Nat.le_induction with
  | base => simp [hzero]
  | succ u hu ih =>
    have he : D (u + 1) - D t = (D (u + 1) - D u) + (D u - D t) := by abel
    rw [he]
    have h := (hadd _ _).trans (add_le_add (hstep u) ih)
    push_cast
    linarith

private lemma movement_all (p : DynParams) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) (t t' : ℕ) (ht : t ≤ t') :
    opNorm (dynDelta S t' ω - dynDelta S t ω) ≤ p.h * ((t' : ℝ) - t) / B ∧
    fro (dynDelta S t' ω - dynDelta S t ω) ≤ p.h * Real.sqrt p.γstar * ((t' : ℝ) - t) / Real.sqrt B ∧
    |Real.sqrt (2 * riskSigma S.C (dynDelta S t' ω)) - Real.sqrt (2 * riskSigma S.C (dynDelta S t ω))| ≤
      p.CSig * p.h * Real.sqrt p.γstar * ((t' : ℝ) - t) / Real.sqrt B := by
  have hη : 0 ≤ p.h / (B : ℝ) := div_nonneg p.hh.le (Nat.cast_nonneg _)
  have ho := movement_accumulate (fun u => dynDelta S u ω) opNorm (p.h / B)
    (by simp [opNorm]) (fun X Y => by
      open scoped Matrix.Norms.L2Operator in
        simpa only [opNorm_eq_norm] using norm_add_le X Y)
    (fun u => by
      rw [movement_delta_succ, sub_sub_cancel_left]
      open scoped Matrix.Norms.L2Operator in
        simp only [opNorm_eq_norm, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
        exact (mul_le_mul_of_nonneg_left (movement_update_bounds p S ω u).1 hη).trans_eq (mul_one _)) t t' ht
  have hf := movement_accumulate (fun u => dynDelta S u ω) fro
    (p.h / B * Real.sqrt (p.γstar * B)) (by simp [fro]) (fun X Y => by
      open scoped Matrix.Norms.Frobenius in
        simpa only [fro_eq_norm] using norm_add_le X Y)
    (fun u => by
      rw [movement_delta_succ, sub_sub_cancel_left]
      open scoped Matrix.Norms.Frobenius in
        simp only [fro_eq_norm, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
        simpa only [fro_eq_norm] using
          mul_le_mul_of_nonneg_left (movement_update_bounds p S ω u).2 hη) t t' ht
  have he : p.h / B * Real.sqrt (p.γstar * B) = p.h * Real.sqrt p.γstar / Real.sqrt B := by
    rw [Real.sqrt_mul p.hγ]
    by_cases hb : B = 0
    · simp [hb]
    · have hs : Real.sqrt (B : ℝ) ≠ 0 := by positivity
      have hsq := Real.sq_sqrt (Nat.cast_nonneg B)
      field_simp
      linear_combination p.h * Real.sqrt p.γstar * hsq
  rw [he] at hf
  refine ⟨?_, ?_, ?_⟩
  · convert ho using 1 <;> ring
  · convert hf using 1 <;> ring
  · have hl := (movement_risk_lip p S.C S.size _ _).trans
      (mul_le_mul_of_nonneg_left hf (le_trans (by norm_num) p.hC))
    convert hl using 1 <;> ring



/-- `lem:app-dyn-movement`, snapshot `cr-2026-10-23`, part (i). Pathwise: for every sample point and
`t ≤ t' < t_stop`. The norms are `opNorm` (`‖·‖`) and `fro` (`‖·‖_F`). Statement verbatim from
`section.tex` (ll. 1496–1506):
```latex
\begin{lemma}[Movement]\label{lem:app-dyn-movement}
\begin{enumerate}[label=(\roman*)]
\item For $t\le t'<t_{\rm stop}$,
$\norm{\Delta_{t'}-\Dt}\le\macrostep(t'-t)/B$,
$\norm{\Delta_{t'}-\Dt}_\F\le\macrostep\sqrt{\gamma_\star}\,(t'-t)/\sqrt B$ and
$\abs{\sqrt{2\cR(\Delta_{t'})}-\sqrt{2\cR(\Dt)}}\le C_\Sigma\macrostep\sqrt{\gamma_\star}\,(t'-t)/\sqrt B$.
\item For every $\mathcal K=\mathcal K(r_-,r_+,E)$ there is $B_0$ such that for
$B\ge B_0$: if $\Dt\in\mathcal K$, then $t+4L<t_{\rm stop}$ and
$\Delta_{t'}\in\mathcal K'$ for all $t'\ge0$ with $\abs{t'-t}\le4L$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_dyn_movement_i (p : DynParams) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) (t t' : ℕ) (ht : t ≤ t')
    (hlt : (t' : ℕ∞) < dynStop S ω) :
    opNorm (dynDelta S t' ω - dynDelta S t ω) ≤ p.h * ((t' : ℝ) - t) / B ∧
    fro (dynDelta S t' ω - dynDelta S t ω) ≤ p.h * Real.sqrt p.γstar * ((t' : ℝ) - t) / Real.sqrt B ∧
    |Real.sqrt (2 * riskSigma S.C (dynDelta S t' ω)) - Real.sqrt (2 * riskSigma S.C (dynDelta S t ω))| ≤
      p.CSig * p.h * Real.sqrt p.γstar * ((t' : ℝ) - t) / Real.sqrt B := by
  exact movement_all p S ω t t' ht

private lemma movement_block_small (p : DynParams) (ε : ℝ) (hε : 0 < ε) :
    ∃ B0 : ℕ, ∀ B : ℕ, B0 ≤ B →
      p.CSig * p.h * Real.sqrt p.γstar * (4 * (blockLen B : ℝ)) / Real.sqrt B ≤ ε := by
  have hC : 0 ≤ p.CSig := le_trans (by norm_num) p.hC
  have hh : 0 ≤ p.h := p.hh.le
  have ht : Tendsto (fun B : ℕ =>
      (4 * p.CSig * p.h * Real.sqrt p.γstar) * (B : ℝ) ^ (-(3 / 8 : ℝ)))
      atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 8)).comp
      tendsto_natCast_atTop_atTop).const_mul (4 * p.CSig * p.h * Real.sqrt p.γstar)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (ht.eventually (gt_mem_nhds hε)))
  refine ⟨max N 1, fun B hB => ?_⟩
  have hb : 0 < (B : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N 1).trans hB))
  have hf : (blockLen B : ℝ) ≤ (B : ℝ) ^ ((1 : ℝ) / 8) :=
    Nat.floor_le (Real.rpow_nonneg hb.le _)
  calc p.CSig * p.h * Real.sqrt p.γstar * (4 * (blockLen B : ℝ)) / Real.sqrt B
      ≤ p.CSig * p.h * Real.sqrt p.γstar * (4 * (B : ℝ) ^ ((1 : ℝ) / 8)) / Real.sqrt B := by
        gcongr
    _ = (4 * p.CSig * p.h * Real.sqrt p.γstar) * (B : ℝ) ^ (-(3 / 8 : ℝ)) := by
        simp only [Real.sqrt_eq_rpow]
        have he : -(3 / 8 : ℝ) = 1 / 8 - 1 / 2 := by norm_num
        rw [he, Real.rpow_sub hb]
        ring
    _ ≤ ε := (hN B ((le_max_left N 1).trans hB)).le

private lemma movement_window (p : DynParams) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) (t t' : ℕ)
    (hdist : |(t' : ℤ) - (t : ℤ)| ≤ 4 * (blockLen B : ℤ)) :
    fro (dynDelta S t' ω - dynDelta S t ω) ≤
      p.CSig * p.h * Real.sqrt p.γstar * (4 * (blockLen B : ℝ)) / Real.sqrt B ∧
    |Real.sqrt (2 * riskSigma S.C (dynDelta S t' ω)) -
      Real.sqrt (2 * riskSigma S.C (dynDelta S t ω))| ≤
      p.CSig * p.h * Real.sqrt p.γstar * (4 * (blockLen B : ℝ)) / Real.sqrt B := by
  have hd : |(t' : ℝ) - (t : ℝ)| ≤ 4 * (blockLen B : ℝ) := by exact_mod_cast hdist
  have hC : 0 ≤ p.CSig := le_trans (by norm_num) p.hC
  have hh : 0 ≤ p.h := p.hh.le
  have hn : 0 ≤ p.h * Real.sqrt p.γstar / Real.sqrt B := by positivity
  have hCn : 0 ≤ p.CSig * p.h * Real.sqrt p.γstar / Real.sqrt B := by positivity
  by_cases hle : t ≤ t'
  · obtain ⟨_, hf, hr⟩ := movement_all p S ω t t' hle
    have hdiff : (t' : ℝ) - t ≤ 4 * (blockLen B : ℝ) := (le_abs_self _).trans hd
    constructor
    · calc fro (dynDelta S t' ω - dynDelta S t ω)
          ≤ p.h * Real.sqrt p.γstar * ((t' : ℝ) - t) / Real.sqrt B := hf
        _ ≤ p.h * Real.sqrt p.γstar * (4 * (blockLen B : ℝ)) / Real.sqrt B := by gcongr
        _ ≤ p.CSig * p.h * Real.sqrt p.γstar * (4 * (blockLen B : ℝ)) / Real.sqrt B := by
          have hh : 0 ≤ p.h * Real.sqrt p.γstar * (4 * (blockLen B : ℝ)) / Real.sqrt B := by positivity
          have hm := mul_le_mul_of_nonneg_right p.hC hh
          convert hm using 1 <;> ring
    · exact hr.trans (by gcongr)
  · obtain ⟨_, hf, hr⟩ := movement_all p S ω t' t (by omega)
    have hdiff : (t : ℝ) - t' ≤ 4 * (blockLen B : ℝ) := by
      have := (neg_le_abs ((t' : ℝ) - t)).trans hd
      linarith
    have he : fro (dynDelta S t' ω - dynDelta S t ω) = fro (dynDelta S t ω - dynDelta S t' ω) := by
      open scoped Matrix.Norms.Frobenius in
        simp only [fro_eq_norm, norm_sub_rev]
    rw [he, abs_sub_comm]
    constructor
    · calc fro (dynDelta S t ω - dynDelta S t' ω)
          ≤ p.h * Real.sqrt p.γstar * ((t : ℝ) - t') / Real.sqrt B := hf
        _ ≤ p.h * Real.sqrt p.γstar * (4 * (blockLen B : ℝ)) / Real.sqrt B := by gcongr
        _ ≤ p.CSig * p.h * Real.sqrt p.γstar * (4 * (blockLen B : ℝ)) / Real.sqrt B := by
          have hh : 0 ≤ p.h * Real.sqrt p.γstar * (4 * (blockLen B : ℝ)) / Real.sqrt B := by positivity
          have hm := mul_le_mul_of_nonneg_right p.hC hh
          convert hm using 1 <;> ring
    · exact hr.trans (by gcongr)

private lemma movement_enlarge (p : DynParams) {m n B : ℕ}
    (C : Covariances m n) (hsize : SizeFin C B p.γstar p.CSig)
    (rlo rhi E : ℝ) (hrlo : 0 < rlo) (D F : Mat m n)
    (hD : D ∈ admSetOf C (rlo, rhi, E))
    (hf : fro (F - D) ≤ 1)
    (hr : |Real.sqrt (2 * riskSigma C F) - Real.sqrt (2 * riskSigma C D)| ≤
      Real.sqrt (2 * rlo) / 4) : F ∈ admSetOf C (enl (rlo, rhi, E)) := by
  obtain ⟨hlo, hhi, hE⟩ := hD
  have hRD : 0 ≤ riskSigma C D := hrlo.le.trans hlo
  have hRF : 0 ≤ riskSigma C F := by rw [eqn_app_setup_whitened_risk]; positivity
  have ha : 0 ≤ Real.sqrt (2 * riskSigma C D) := Real.sqrt_nonneg _
  have hb : 0 ≤ Real.sqrt (2 * riskSigma C F) := Real.sqrt_nonneg _
  have hasq := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hRD)
  have hbsq := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hRF)
  have hroot : Real.sqrt (2 * rlo) ≤ Real.sqrt (2 * riskSigma C D) :=
    Real.sqrt_le_sqrt (by linarith)
  have hd := abs_le.mp hr
  have hlow : (3 / 4 : ℝ) * Real.sqrt (2 * riskSigma C D) ≤ Real.sqrt (2 * riskSigma C F) := by
    linarith
  have hupp : Real.sqrt (2 * riskSigma C F) ≤ (5 / 4 : ℝ) * Real.sqrt (2 * riskSigma C D) := by
    linarith
  have hl2 := mul_self_le_mul_self (by positivity : 0 ≤ (3 / 4 : ℝ) * Real.sqrt (2 * riskSigma C D)) hlow
  have hu2 := mul_self_le_mul_self hb hupp
  have hnorm : fro F ≤ fro (F - D) + fro D := by
    open scoped Matrix.Norms.Frobenius in
      simpa only [fro_eq_norm, sub_add_cancel] using norm_add_le (F - D) D
  have hfD := movement_fro_nn D
  have hfF := movement_fro_nn F
  have hfsq := sq_nonneg (fro (F - D) - fro D)
  change rlo / 2 ≤ riskSigma C F ∧ riskSigma C F ≤ 2 * rhi ∧ fro F ^ 2 ≤ 2 * E + 2
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have hsum : fro F ≤ 1 + fro D := by linarith
  have hs := mul_self_le_mul_self hfF hsum
  nlinarith [sq_nonneg (fro D - 1)]

/-- `lem:app-dyn-movement`, snapshot `cr-2026-10-23`, part (ii). The constant `B₀` depends on the
fixed parameters and on `𝒦 = 𝒦(r₋, r₊, E)` only, and is quantified before the dimensions. Statement
verbatim from `section.tex` (ll. 1496–1506):
```latex
\begin{lemma}[Movement]\label{lem:app-dyn-movement}
\begin{enumerate}[label=(\roman*)]
\item For $t\le t'<t_{\rm stop}$,
$\norm{\Delta_{t'}-\Dt}\le\macrostep(t'-t)/B$,
$\norm{\Delta_{t'}-\Dt}_\F\le\macrostep\sqrt{\gamma_\star}\,(t'-t)/\sqrt B$ and
$\abs{\sqrt{2\cR(\Delta_{t'})}-\sqrt{2\cR(\Dt)}}\le C_\Sigma\macrostep\sqrt{\gamma_\star}\,(t'-t)/\sqrt B$.
\item For every $\mathcal K=\mathcal K(r_-,r_+,E)$ there is $B_0$ such that for
$B\ge B_0$: if $\Dt\in\mathcal K$, then $t+4L<t_{\rm stop}$ and
$\Delta_{t'}\in\mathcal K'$ for all $t'\ge0$ with $\abs{t'-t}\le4L$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_dyn_movement_ii (p : DynParams) (rlo rhi E : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ B0 : ℕ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (m n B : ℕ)
      (S : DynSetup p P m n B), B0 ≤ B → ∀ (ω : Ω) (t : ℕ),
        dynDelta S t ω ∈ admSetOf S.C (rlo, rhi, E) →
          ((t + 4 * blockLen B : ℕ) : ℕ∞) < dynStop S ω ∧
          ∀ t' : ℕ, |(t' : ℤ) - (t : ℤ)| ≤ 4 * (blockLen B : ℤ) →
            dynDelta S t' ω ∈ admSetOf S.C (enl (rlo, rhi, E)) := by
  obtain ⟨B0, hB0⟩ := movement_block_small p (min 1 (Real.sqrt (2 * rlo) / 4))
    (lt_min (by norm_num) (by positivity))
  refine ⟨B0, ?_⟩
  intro Ω _ P m n B S hB ω t hD
  have hsmall := hB0 B hB
  have hwindow : ∀ t' : ℕ, |(t' : ℤ) - (t : ℤ)| ≤ 4 * (blockLen B : ℤ) →
      dynDelta S t' ω ∈ admSetOf S.C (enl (rlo, rhi, E)) := by
    intro t' ht'
    obtain ⟨hf, hr⟩ := movement_window p S ω t t' ht'
    exact movement_enlarge p S.C S.size rlo rhi E hrlo _ _ hD
      (hf.trans (hsmall.trans (min_le_left _ _)))
      (hr.trans (hsmall.trans (min_le_right _ _)))
  refine ⟨?_, hwindow⟩
  have hnear : |((t + 4 * blockLen B : ℕ) : ℤ) - (t : ℤ)| ≤ 4 * (blockLen B : ℤ) := by
    simp
  have hpos : 0 < riskSigma S.C (dynDelta S (t + 4 * blockLen B) ω) :=
    lt_of_lt_of_le (by linarith : 0 < rlo / 2) (hwindow _ hnear).1
  apply lt_of_not_ge
  intro hstop
  have hz := (update_eq_zero_iff S.C S.alg (dynStart S ω)
    (fun u => dynBatch S u ω) (t + 4 * blockLen B)).mp hstop
  exact hpos.ne' hz

/-! ## `lem:app-dyn-buffer` -/

private lemma buffer_past_le {p : DynParams} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) : dynPast S t ≤ mΩ := by
  refine sup_le (iSup_le fun s => iSup_le fun _ => iSup_le fun a => ?_) S.M0_meas.comap_le
  exact (S.cs.meas_act s a).comap_le

private lemma buffer_past_mono {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) {s t : ℕ} (h : s ≤ t) :
    dynPast S s ≤ dynPast S t := by
  refine sup_le_sup_right (iSup_le fun u => iSup_le fun hu => iSup_le fun a => ?_) _
  exact le_iSup₂_of_le u ⟨hu.1, hu.2.trans (by exact_mod_cast h)⟩ (le_iSup_of_le a le_rfl)

private lemma buffer_mat_meas {Ω : Type*} {σ : MeasurableSpace Ω} {m n : ℕ}
    {F : Ω → Mat m n} (h : ∀ i j, Measurable[σ] fun ω => F ω i j) : Measurable[σ] F :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => h i j

private lemma buffer_entry_meas {Ω : Type*} {σ : MeasurableSpace Ω} {m n : ℕ}
    {F : Ω → Mat m n} (hF : Measurable[σ] F) (i : Fin m) (j : Fin n) :
    Measurable[σ] fun ω => F ω i j :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hF)

private lemma buffer_grad_meas {Ω : Type*} {σ : MeasurableSpace Ω} {B m n : ℕ}
    {D : Ω → Mat m n} {b : Ω → Batch m n B} (hD : Measurable[σ] D)
    (hb : Measurable[σ] b) : Measurable[σ] (fun ω => grad (D ω) (b ω)) := by
  have hc : Continuous (fun q : Mat m n × Batch m n B => grad q.1 q.2) := by
    unfold grad resid outer
    fun_prop
  exact Measurable.comp (g := fun q : Mat m n × Batch m n B => grad q.1 q.2)
    (f := fun ω => (D ω, b ω)) hc.measurable (hD.prodMk hb)

private lemma buffer_step_meas {Ω : Type*} {σ : MeasurableSpace Ω} {B m n : ℕ}
    (C : Covariances m n) (p : AlgParams m n) (k : ℕ) (s : Ω → AlgState m n)
    (b : Ω → Batch m n B) (hW : Measurable[σ] (fun ω => (s ω).W))
    (hM : Measurable[σ] (fun ω => (s ω).Mprev)) (hb : Measurable[σ] b) :
    Measurable[σ] (fun ω => (step C p k (s ω) (b ω)).W) ∧
      Measurable[σ] (fun ω => (step C p k (s ω) (b ω)).Mprev) := by
  have hD : Measurable[σ] (fun ω => errorOf p (s ω)) :=
    (continuous_id.sub continuous_const).measurable.comp hW
  have hG := buffer_grad_meas hD hb
  have hbuf : Measurable[σ] (fun ω => stepBuffer p (s ω) (b ω)) := by
    apply buffer_mat_meas
    intro i j
    simp only [stepBuffer, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact ((buffer_entry_meas hM i j).const_mul _).add ((buffer_entry_meas hG i j).const_mul _)
  have hR : Measurable[σ] (fun ω => riskSigma C (errorOf p (s ω))) := by
    apply (show Continuous (fun D : Mat m n => riskSigma C D) by
      unfold riskSigma pairSigma
      fun_prop).measurable.comp hD
  have hset : MeasurableSet[σ] {ω | riskSigma C (errorOf p (s ω)) = 0} :=
    hR (measurableSet_singleton 0)
  have hU : Measurable[σ] (fun ω => stepUpdate C p (s ω) (b ω)) := by
    refine Measurable.ite hset measurable_const ?_
    have hnn : ∀ ω, 0 ≤ 2 * riskSigma C (errorOf p (s ω)) * p.ϱ := fun ω => by
      exact mul_nonneg (mul_nonneg (by norm_num)
        (by rw [eqn_app_setup_whitened_risk]; positivity)) p.hϱ.le
    have hφ : Measurable[σ]
        (fun ω => (⟨2 * riskSigma C (errorOf p (s ω)) * p.ϱ, hnn ω⟩ : Set.Ici (0 : ℝ))) :=
      ((hR.const_mul 2).mul_const p.ϱ).subtype_mk
    exact measurable_Q.comp (hφ.prodMk hbuf)
  refine ⟨?_, hbuf⟩
  apply buffer_mat_meas
  intro i j
  simp only [step, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact (buffer_entry_meas hW i j).sub ((buffer_entry_meas hU i j).const_mul _)

private lemma buffer_pi_meas {Ω : Type*} {σ : MeasurableSpace Ω} {ι : Type*}
    {π : ι → Type*} [∀ i, MeasurableSpace (π i)] {g : Ω → ∀ i, π i}
    (h : ∀ i, Measurable[σ] fun ω => g ω i) : Measurable[σ] g :=
  measurable_pi_iff.mpr h

private lemma buffer_batch_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (u : ℕ) :
    Measurable[dynPast S (u + 1)] (dynBatch S u) := by
  refine buffer_pi_meas (fun a => ?_)
  have hz : Measurable[dynPast S (u + 1)] (S.cs.act ((u : ℤ) + 1) a) := by
    apply Measurable.of_comap_le
    refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le ((u : ℤ) + 1) ⟨by omega, by push_cast; omega⟩ (le_iSup_of_le a le_rfl)
  exact (show Continuous (fun z : Vec m × Vec n => phys S.C z) by
    unfold phys
    fun_prop).measurable.comp hz

private lemma buffer_state_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S t] (fun ω => (dynState S t ω).W) ∧
      Measurable[dynPast S t] (dynBuf S t) := by
  induction t with
  | zero =>
      refine ⟨measurable_const, ?_⟩
      exact (comap_measurable S.M0).mono le_sup_right le_rfl
  | succ k ih =>
      have hW := ih.1.mono (buffer_past_mono S (Nat.le_succ k)) le_rfl
      have hM := ih.2.mono (buffer_past_mono S (Nat.le_succ k)) le_rfl
      exact buffer_step_meas (σ := dynPast S (k + 1)) S.C S.alg k (dynState S k)
        (dynBatch S k) hW hM (buffer_batch_meas S k)

private lemma buffer_delta_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S t] (dynDelta S t) :=
  (continuous_id.sub continuous_const).measurable.comp (buffer_state_meas S t).1

private lemma buffer_iid {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (u : ℕ) :
    IIDBatch P ((Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)) (S.cs.act ((u : ℤ) + 1)) := by
  refine ⟨fun a => (S.cs.meas_act _ a).aemeasurable, fun a => S.cs.law_act _ a, ?_⟩
  exact S.cs.indep.precomp (g := fun a : Fin B => Sum.inl (((u : ℤ) + 1), a))
    (fun a b h => congrArg Prod.snd (Sum.inl.inj h))

private lemma buffer_indep_sup {Ω : Type*} (A M F G : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (hAG : A ≤ G) (hFG : F ≤ G) (hGle : G ≤ mΩ) (hMle : M ≤ mΩ) (hFle : F ≤ mΩ)
    (hAF : Indep A F P) (hMG : Indep M G P) : Indep (A ⊔ M) F P := by
  have hAle : A ≤ mΩ := hAG.trans hGle
  let q : Set (Set Ω) := {s | ∃ a, MeasurableSet[A] a ∧ ∃ b, MeasurableSet[M] b ∧ s = a ∩ b}
  have hq : IsPiSystem q := by
    rintro _ ⟨a, ha, b, hb, rfl⟩ _ ⟨a', ha', b', hb', rfl⟩ _
    refine ⟨a ∩ a', ha.inter ha', b ∩ b', hb.inter hb', ?_⟩
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  have hgen : A ⊔ M = MeasurableSpace.generateFrom q := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro a ha
        exact MeasurableSpace.measurableSet_generateFrom ⟨a, ha, Set.univ, MeasurableSet.univ, by simp⟩
      · intro b hb
        exact MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, MeasurableSet.univ, b, hb, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact @MeasurableSet.inter Ω (A ⊔ M) _ _
        ((le_sup_left : A ≤ A ⊔ M) a ha) ((le_sup_right : M ≤ A ⊔ M) b hb)
  have hgen2 : F = MeasurableSpace.generateFrom {s | MeasurableSet[F] s} :=
    (@MeasurableSpace.generateFrom_measurableSet Ω F).symm
  refine IndepSets.indep (sup_le hAle hMle) hFle hq
    (@MeasurableSpace.isPiSystem_measurableSet Ω F) hgen hgen2 ?_
  rw [IndepSets_iff]
  rintro _ f ⟨a, ha, b, hb, rfl⟩ hf
  have h1 : P (a ∩ b ∩ f) = P b * P (a ∩ f) := by
    rw [show a ∩ b ∩ f = b ∩ (a ∩ f) by ext x; simp only [Set.mem_inter_iff]; tauto]
    exact (Indep_iff _ _ _).mp hMG b (a ∩ f) hb ((hAG a ha).inter (hFG f hf))
  have h2 : P (a ∩ f) = P a * P f := (Indep_iff _ _ _).mp hAF a f ha hf
  have h3 : P (a ∩ b) = P b * P a := by
    rw [Set.inter_comm]
    exact (Indep_iff _ _ _).mp hMG b a hb (hAG a ha)
  rw [h1, h2, h3]
  ring

private lemma buffer_indep_past_future {p : DynParams} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) :
    Indep (dynPast S t) (chainFuture S.cs t) P := by
  refine buffer_indep_sup _ _ _
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

private lemma buffer_indep_past_batch {p : DynParams} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (u : ℕ) :
    Indep (dynPast S u)
      (⨆ a, MeasurableSpace.comap (S.cs.act ((u : ℤ) + 1) a) inferInstance) P := by
  refine indep_of_indep_of_le_right (buffer_indep_past_future S u) ?_
  refine le_sup_of_le_left (iSup_le fun a => ?_)
  exact le_iSup₂_of_le ((u : ℤ) + 1) (by push_cast; omega) (le_iSup_of_le a le_rfl)

private lemma buffer_fro_sq_meas {m n : ℕ} : Measurable (fun A : Mat m n => fro A ^ 2) := by
  have hfun : (fun A : Mat m n => fro A ^ 2) = fun A => ∑ i, ∑ j, A i j ^ 2 := by
    funext A
    exact movement_fro_sq A
  rw [hfun]
  fun_prop

private lemma buffer_stopped_grad_fro {p : DynParams} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B)
    (τ : Ω → ℕ∞) (hB : 0 < B) (rlo rhi E : ℝ) (hrhi : 0 ≤ rhi)
    (hτ : ∀ t : ℕ, MeasurableSet[dynPast S t] {ω | (t : ℕ∞) < τ ω})
    (hK : ∀ (t : ℕ) (ω : Ω), (t : ℕ∞) < τ ω →
      dynDelta S t ω ∈ admSetOf S.C (rlo, rhi, E)) (u : ℕ) :
    Integrable ({ω | (u : ℕ∞) < τ ω}.indicator
      (fun ω => fro (batchGrad (dynDelta S u ω)
        (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω)) ^ 2)) P ∧
    ∫ ω, {ω | (u : ℕ∞) < τ ω}.indicator
        (fun ω => fro (batchGrad (dynDelta S u ω)
          (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω)) ^ 2) ω ∂P ≤
      2 * cMConst p.CSig p.γstar * rhi * B := by
  let A : Set Ω := {ω | (u : ℕ∞) < τ ω}
  let D : Ω → Mat m n := A.indicator (dynDelta S u)
  have hA : MeasurableSet[dynPast S u] A := hτ u
  have hD : Measurable[dynPast S u] D := (buffer_delta_meas S u).indicator hA
  have hrotD : Measurable[dynPast S u] (fun ω => rOut S.C * D ω * rIn S.C) := by
    apply buffer_mat_meas
    intro i j
    simp only [Matrix.mul_apply]
    fun_prop
  have hsq : Measurable[dynPast S u] (fun ω => fro (rOut S.C * D ω * rIn S.C) ^ 2) :=
    buffer_fro_sq_meas.comp hrotD
  have hrot_bd : ∀ ω, fro (rOut S.C * D ω * rIn S.C) ^ 2 ≤ 2 * rhi := by
    intro ω
    by_cases hω : ω ∈ A
    · have hu := (hK u ω hω).2.1
      rw [eqn_app_setup_whitened_risk] at hu
      simpa only [D, Set.indicator_of_mem hω, Arot] using (show
        fro (Arot S.C (dynDelta S u ω)) ^ 2 ≤ 2 * rhi by linarith)
    · simp [D, Set.indicator_of_notMem hω, fro, hrhi]
  have hEint : Integrable (fun ω => fro (rOut S.C * D ω * rIn S.C) ^ 2) P :=
    Integrable.of_bound (hsq.mono (buffer_past_le S u) le_rfl).aestronglyMeasurable (2 * rhi)
      (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hrot_bd ω)
  obtain ⟨⟨hGint, hcond⟩, _⟩ := lem_app_dyn_batch_iv (dynPast S u) S.C p.γstar p.CSig
    hB S.size (S.cs.act ((u : ℤ) + 1)) (buffer_iid S u) (buffer_past_le S u)
    (buffer_indep_past_batch S u) D hD hEint
  have hfun : (fun ω => fro (batchGrad (D ω)
      (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω)) ^ 2) =
      A.indicator (fun ω => fro (batchGrad (dynDelta S u ω)
        (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω)) ^ 2) := by
    funext ω
    by_cases hω : ω ∈ A
    · simp [D, Set.indicator_of_mem hω]
    · have hg : batchGrad (0 : Mat m n)
          (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω) = 0 := by
        ext i j
        simp [grad, resid, Matrix.mulVec]
      simp only [D, Set.indicator_of_notMem hω, hg]
      rw [movement_fro_sq]
      simp
  rw [← hfun]
  refine ⟨hGint, ?_⟩
  calc
    ∫ ω, fro (batchGrad (D ω) (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω)) ^ 2 ∂P =
        ∫ ω, condExp (dynPast S u) P
          (fun ω' => fro (batchGrad (D ω')
            (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω')) ^ 2) ω ∂P :=
      (integral_condExp (buffer_past_le S u)).symm
    _ ≤ ∫ _ω, 2 * cMConst p.CSig p.γstar * rhi * B ∂P := by
      apply integral_mono_ae integrable_condExp (integrable_const _)
      filter_upwards [hcond] with ω hω
      calc
        condExp (dynPast S u) P
            (fun ω' => fro (batchGrad (D ω')
              (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω')) ^ 2) ω
            ≤ cMConst p.CSig p.γstar * (B : ℝ) *
              fro (rOut S.C * D ω * rIn S.C) ^ 2 := hω
        _ ≤ 2 * cMConst p.CSig p.γstar * rhi * B := by
          have hc : 0 ≤ cMConst p.CSig p.γstar := by unfold cMConst; positivity
          have hBr : 0 ≤ (B : ℝ) := by positivity
          calc
            cMConst p.CSig p.γstar * (B : ℝ) *
                fro (rOut S.C * D ω * rIn S.C) ^ 2
                ≤ cMConst p.CSig p.γstar * (B : ℝ) * (2 * rhi) :=
              mul_le_mul_of_nonneg_left (hrot_bd ω) (mul_nonneg hc hBr)
            _ = 2 * cMConst p.CSig p.γstar * rhi * B := by ring
    _ = 2 * cMConst p.CSig p.γstar * rhi * B := by
      rw [integral_const, probReal_univ]
      simp

private lemma buffer_M0_fro {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) :
    Integrable (fun ω => fro (S.M0 ω) ^ 2) P ∧
      ∫ ω, fro (S.M0 ω) ^ 2 ∂P ≤ p.cM * B := by
  have hm : Measurable (fun ω => fro (S.M0 ω) ^ 2) := buffer_fro_sq_meas.comp S.M0_meas
  have hnn : ∀ᵐ ω ∂P, 0 ≤ fro (S.M0 ω) ^ 2 := ae_of_all _ fun _ => sq_nonneg _
  have hlt : ∫⁻ ω, ENNReal.ofReal (fro (S.M0 ω) ^ 2) ∂P < ⊤ :=
    lt_of_le_of_lt S.M0_bound ENNReal.ofReal_lt_top
  have hint : Integrable (fun ω => fro (S.M0 ω) ^ 2) P :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hlt⟩
  refine ⟨hint, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg p.hcM (by positivity))).mp
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
  exact S.M0_bound

private lemma buffer_weighted_sq (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (t : ℕ) (x : ℕ → ℝ) :
    (∑ j ∈ Finset.range t, emaW β j * x j) ^ 2 ≤
      ∑ j ∈ Finset.range t, emaW β j * x j ^ 2 := by
  have hw : ∀ j, 0 ≤ emaW β j := fun j => by
    unfold emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 _)
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range t)
    (r := fun j => emaW β j * x j) (f := fun j => emaW β j)
    (g := fun j => emaW β j * x j ^ 2)
    (fun j _ => hw j) (fun j _ => mul_nonneg (hw j) (sq_nonneg _))
    (fun j _ => by ring_nf; nlinarith [hw j, sq_nonneg (x j)])
  have hsum : ∑ j ∈ Finset.range t, emaW β j ≤ 1 := by
    rw [← tsum_emaW hβ0 hβ1]
    exact ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (1 - β)).sum_le_tsum _
      (fun j _ => hw j)
  have hright : 0 ≤ ∑ j ∈ Finset.range t, emaW β j * x j ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
  exact hs.trans (by nlinarith)

private lemma buffer_fro_unroll_bound {m n : ℕ} (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (t : ℕ) (M : Mat m n) (G : ℕ → Mat m n) :
    fro (β ^ t • M + ∑ j ∈ Finset.range t, emaW β j • G j) ^ 2 ≤
      2 * β ^ (2 * t) * fro M ^ 2 +
        2 * ∑ j ∈ Finset.range t, emaW β j * fro (G j) ^ 2 := by
  have hw : ∀ j, 0 ≤ emaW β j := fun j => by
    unfold emaW
    positivity
  have hsum : fro (∑ j ∈ Finset.range t, emaW β j • G j) ≤
      ∑ j ∈ Finset.range t, emaW β j * fro (G j) := by
    open scoped Matrix.Norms.Frobenius in
      simpa only [fro_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw _)] using
        norm_sum_le (Finset.range t) (fun j => emaW β j • G j)
  have hfadd : fro (β ^ t • M + ∑ j ∈ Finset.range t, emaW β j • G j) ≤
      β ^ t * fro M + ∑ j ∈ Finset.range t, emaW β j * fro (G j) := by
    have hadd : fro (β ^ t • M + ∑ j ∈ Finset.range t, emaW β j • G j) ≤
        fro (β ^ t • M) + fro (∑ j ∈ Finset.range t, emaW β j • G j) := by
      open scoped Matrix.Norms.Frobenius in
        simpa only [fro_eq_norm] using
          norm_add_le (β ^ t • M) (∑ j ∈ Finset.range t, emaW β j • G j)
    calc
      fro (β ^ t • M + ∑ j ∈ Finset.range t, emaW β j • G j)
          ≤ fro (β ^ t • M) + fro (∑ j ∈ Finset.range t, emaW β j • G j) := hadd
      _ ≤ β ^ t * fro M + ∑ j ∈ Finset.range t, emaW β j * fro (G j) := by
        open scoped Matrix.Norms.Frobenius in
          simpa only [fro_eq_norm, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (pow_nonneg hβ0 _)] using add_le_add le_rfl hsum
  have hsq := pow_le_pow_left₀ (movement_fro_nn _)
    hfadd 2
  have hweighted := buffer_weighted_sq β hβ0 hβ1 t (fun j => fro (G j))
  have ha : 0 ≤ β ^ t * fro M := mul_nonneg (pow_nonneg hβ0 _) (movement_fro_nn _)
  have hb : 0 ≤ ∑ j ∈ Finset.range t, emaW β j * fro (G j) := by
    exact Finset.sum_nonneg fun j _ => mul_nonneg (by unfold emaW; positivity) (movement_fro_nn _)
  calc
    fro (β ^ t • M + ∑ j ∈ Finset.range t, emaW β j • G j) ^ 2
        ≤ (β ^ t * fro M + ∑ j ∈ Finset.range t, emaW β j * fro (G j)) ^ 2 := hsq
    _ ≤ 2 * (β ^ t * fro M) ^ 2 +
        2 * (∑ j ∈ Finset.range t, emaW β j * fro (G j)) ^ 2 := by
      nlinarith [sq_nonneg (β ^ t * fro M - ∑ j ∈ Finset.range t, emaW β j * fro (G j))]
    _ ≤ 2 * β ^ (2 * t) * fro M ^ 2 +
        2 * ∑ j ∈ Finset.range t, emaW β j * fro (G j) ^ 2 := by
      have heq : (β ^ t * fro M) ^ 2 = β ^ (2 * t) * fro M ^ 2 := by ring
      calc
        2 * (β ^ t * fro M) ^ 2 +
            2 * (∑ j ∈ Finset.range t, emaW β j * fro (G j)) ^ 2
            = 2 * β ^ (2 * t) * fro M ^ 2 +
              2 * (∑ j ∈ Finset.range t, emaW β j * fro (G j)) ^ 2 := by rw [heq]; ring
        _ ≤ 2 * β ^ (2 * t) * fro M ^ 2 +
            2 * ∑ j ∈ Finset.range t, emaW β j * fro (G j) ^ 2 := by
          exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hweighted (by norm_num))

private lemma buffer_stopped_pathwise {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (τ : Ω → ℕ∞)
    (t : ℕ) (ω : Ω) :
    {ω | (t : ℕ∞) ≤ τ ω}.indicator (fun ω => fro (dynBuf S t ω) ^ 2) ω ≤
      2 * p.β ^ (2 * t) * fro (S.M0 ω) ^ 2 +
        2 * ∑ j ∈ Finset.range t, emaW p.β j *
          fro ({ω | ((t - 1 - j : ℕ) : ℕ∞) < τ ω}.indicator
            (fun ω => batchGrad (dynDelta S (t - 1 - j) ω)
              (physBatch S.C (S.cs.act (((t - 1 - j : ℕ) : ℤ) + 1)) ω)) ω) ^ 2 := by
  cases t with
  | zero =>
      rw [Set.indicator_of_mem (show ω ∈ {ω | ((0 : ℕ) : ℕ∞) ≤ τ ω} by simp)]
      simp only [pow_zero, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      simp only [dynBuf, dynState, runRand, run, dynStart, initState]
      nlinarith [sq_nonneg (fro (S.M0 ω))]
  | succ k =>
      by_cases ht : ((k + 1 : ℕ) : ℕ∞) ≤ τ ω
      · rw [Set.indicator_of_mem (show ω ∈ {ω | (((k + 1 : ℕ) : ℕ∞) ≤ τ ω)} from ht)]
        simp only [Nat.add_sub_cancel]
        have heq : dynBuf S (k + 1) ω =
            p.β ^ (k + 1) • S.M0 ω +
              ∑ j ∈ Finset.range (k + 1), emaW p.β j •
                batchGrad (dynDelta S (k - j) ω)
                  (physBatch S.C (S.cs.act (((k - j : ℕ) : ℤ) + 1)) ω) := by
          simpa only [dynBuf, dynState, runRand, dynStart, initState, dynDelta, devRand,
            dynBatch, S.alg_β] using
            eqn_app_setup_unrolled S.C S.alg (dynStart S ω)
              (fun u => dynBatch S u ω) k
        have hstop : ∀ j ∈ Finset.range (k + 1),
            ((k - j : ℕ) : ℕ∞) < τ ω := by
          intro j hj
          exact lt_of_lt_of_le (by exact_mod_cast (Nat.sub_lt_succ k j)) ht
        have hbase := buffer_fro_unroll_bound p.β p.hβ.1 p.hβ.2 (k + 1) (S.M0 ω)
          (fun j => batchGrad (dynDelta S (k - j) ω)
            (physBatch S.C (S.cs.act (((k - j : ℕ) : ℤ) + 1)) ω))
        rw [heq]
        calc
          fro (p.β ^ (k + 1) • S.M0 ω +
              ∑ j ∈ Finset.range (k + 1), emaW p.β j •
                batchGrad (dynDelta S (k - j) ω)
                  (physBatch S.C (S.cs.act (((k - j : ℕ) : ℤ) + 1)) ω)) ^ 2
              ≤ 2 * p.β ^ (2 * (k + 1)) * fro (S.M0 ω) ^ 2 +
                2 * ∑ j ∈ Finset.range (k + 1), emaW p.β j *
                  fro (batchGrad (dynDelta S (k - j) ω)
                    (physBatch S.C (S.cs.act (((k - j : ℕ) : ℤ) + 1)) ω)) ^ 2 := hbase
          _ = 2 * p.β ^ (2 * (k + 1)) * fro (S.M0 ω) ^ 2 +
                2 * ∑ j ∈ Finset.range (k + 1), emaW p.β j *
                  fro ({ω | ((k - j : ℕ) : ℕ∞) < τ ω}.indicator
                    (fun ω => batchGrad (dynDelta S (k - j) ω)
                      (physBatch S.C (S.cs.act (((k - j : ℕ) : ℤ) + 1)) ω)) ω) ^ 2 := by
            congr 2
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [Set.indicator_of_mem (show ω ∈ {ω | ((k - j : ℕ) : ℕ∞) < τ ω} from hstop j hj)]
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | (((k + 1 : ℕ) : ℕ∞) ≤ τ ω)} from ht)]
        have hw : ∀ j, 0 ≤ emaW p.β j := fun j => by
          unfold emaW
          exact mul_nonneg (by linarith [p.hβ.2]) (pow_nonneg p.hβ.1 _)
        have hs : 0 ≤ ∑ j ∈ Finset.range (k + 1), emaW p.β j *
            fro ({ω | ((k + 1 - 1 - j : ℕ) : ℕ∞) < τ ω}.indicator
              (fun ω => batchGrad (dynDelta S (k + 1 - 1 - j) ω)
                (physBatch S.C (S.cs.act (((k + 1 - 1 - j : ℕ) : ℤ) + 1)) ω)) ω) ^ 2 :=
          Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
        exact add_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg p.hβ.1 _)) (sq_nonneg _))
          (mul_nonneg (by norm_num) hs)

private lemma buffer_indicator_fro_sq {Ω : Type*} {m n : ℕ} (A : Set Ω)
    (F : Ω → Mat m n) (ω : Ω) :
    fro (A.indicator F ω) ^ 2 = A.indicator (fun ω => fro (F ω) ^ 2) ω := by
  by_cases hω : ω ∈ A
  · simp [Set.indicator_of_mem hω]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, movement_fro_sq]
    simp

private lemma buffer_stop_event_meas {p : DynParams} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (τ : Ω → ℕ∞)
    (hτ : ∀ t : ℕ, MeasurableSet[dynPast S t] {ω | (t : ℕ∞) < τ ω}) (t : ℕ) :
    MeasurableSet {ω | (t : ℕ∞) ≤ τ ω} := by
  cases t with
  | zero => simp
  | succ k =>
      have hk : MeasurableSet {ω | (k : ℕ∞) < τ ω} := (buffer_past_le S k) _ (hτ k)
      convert hk using 1
      ext ω
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, Nat.cast_succ, ENat.add_one_le_iff]
      exact ENat.natCast_ne_top k

/-- `lem:app-dyn-buffer`, snapshot `cr-2026-10-23`, part (i): the first bound. The stopping
time `τ` is given with `{t < τ} ∈ 𝓕_t` (whether `t < τ` is decided by the past) and `Δ_t ∈ 𝒦` for `t < τ`.
Statement verbatim from `section.tex` (ll. 1531–1539):
```latex
\begin{lemma}[Stopped buffer moments]\label{lem:app-dyn-buffer}
Let $\mathcal K=\mathcal K(r_-,r_+,E)$, and let $\tau$ be a time such that
whether $t<\tau$ is decided by the past $\cF_t$, and such that $\Dt\in\mathcal K$
for $t<\tau$. Then for every $t\ge0$,
\[
\EE\big[\mathbf 1_{t\le\tau}\norm{M^\circ_{t-1}}_\F^2\big]\le2c_MB+4C_Mr_+B,\qquad
\EE\big[\mathbf 1_{t\le\tau}\norm{M^\circ_{t-1}}^2\big]\le2\bmom^{2t}c_MB+C\log^2(2B).
\]
\end{lemma}
```
-/
theorem lem_app_dyn_buffer_i (p : DynParams) (rlo rhi E : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (m n B : ℕ)
      (S : DynSetup p P m n B) (τ : Ω → ℕ∞),
      (∀ t : ℕ, MeasurableSet[dynPast S t] {ω | (t : ℕ∞) < τ ω}) →
      (∀ (t : ℕ) (ω : Ω), (t : ℕ∞) < τ ω → dynDelta S t ω ∈ admSetOf S.C (rlo, rhi, E)) →
      ∀ t : ℕ,
        Integrable ({ω | (t : ℕ∞) ≤ τ ω}.indicator (fun ω => fro (dynBuf S t ω) ^ 2)) P ∧
        ∫ ω, {ω | (t : ℕ∞) ≤ τ ω}.indicator (fun ω => fro (dynBuf S t ω) ^ 2) ω ∂P ≤
          2 * (p.cM * B) + 4 * cMConst p.CSig p.γstar * rhi * B := by
  intro Ω _ P _ m n B S τ hτ hK t
  by_cases hB : 0 < B
  · have hrhi : 0 ≤ rhi := le_trans hrlo.le hle
    have hM := buffer_M0_fro S
    let g : ℕ → Ω → ℝ := fun u => {ω | (u : ℕ∞) < τ ω}.indicator
      (fun ω => fro (batchGrad (dynDelta S u ω)
        (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω)) ^ 2)
    have hg : ∀ u, Integrable (g u) P ∧
        ∫ ω, g u ω ∂P ≤ 2 * cMConst p.CSig p.γstar * rhi * B := by
      intro u
      exact buffer_stopped_grad_fro S τ hB rlo rhi E hrhi hτ hK u
    let R : Ω → ℝ := fun ω =>
      2 * p.β ^ (2 * t) * fro (S.M0 ω) ^ 2 +
        2 * ∑ j ∈ Finset.range t, emaW p.β j * g (t - 1 - j) ω
    have hsumint : Integrable
        (fun ω => ∑ j ∈ Finset.range t, emaW p.β j * g (t - 1 - j) ω) P :=
      integrable_finset_sum _ fun j _ => (hg (t - 1 - j)).1.const_mul _
    have hRint : Integrable R P :=
      (hM.1.const_mul (2 * p.β ^ (2 * t))).add (hsumint.const_mul 2)
    have htarget_meas : Measurable
        ({ω | (t : ℕ∞) ≤ τ ω}.indicator (fun ω => fro (dynBuf S t ω) ^ 2)) := by
      have hb := (buffer_state_meas S t).2.mono (buffer_past_le S t) le_rfl
      exact (buffer_fro_sq_meas.comp hb).indicator (buffer_stop_event_meas S τ hτ t)
    have hpoint : ∀ ω, {ω | (t : ℕ∞) ≤ τ ω}.indicator
        (fun ω => fro (dynBuf S t ω) ^ 2) ω ≤ R ω := by
      intro ω
      have hp := buffer_stopped_pathwise S τ t ω
      simp_rw [buffer_indicator_fro_sq] at hp
      exact hp
    have hRnonneg : ∀ ω, 0 ≤ R ω := by
      intro ω
      have hw : ∀ j, 0 ≤ emaW p.β j := fun j => by
        unfold emaW
        exact mul_nonneg (by linarith [p.hβ.2]) (pow_nonneg p.hβ.1 _)
      have hg0 : ∀ u ω, 0 ≤ g u ω := fun u ω => by
        unfold g
        exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
      exact add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg p.hβ.1 _)) (sq_nonneg _))
        (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (hg0 _ _)))
    have htarget_int : Integrable
        ({ω | (t : ℕ∞) ≤ τ ω}.indicator (fun ω => fro (dynBuf S t ω) ^ 2)) P := by
      refine Integrable.mono' hRint htarget_meas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
      rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω)]
      exact hpoint ω
    refine ⟨htarget_int, (integral_mono_ae htarget_int hRint (ae_of_all _ hpoint)).trans ?_⟩
    have hw : ∀ j, 0 ≤ emaW p.β j := fun j => by
      unfold emaW
      exact mul_nonneg (by linarith [p.hβ.2]) (pow_nonneg p.hβ.1 _)
    have hwsum : ∑ j ∈ Finset.range t, emaW p.β j ≤ 1 := by
      rw [← tsum_emaW p.hβ.1 p.hβ.2]
      exact ((summable_geometric_of_lt_one p.hβ.1 p.hβ.2).mul_left (1 - p.β)).sum_le_tsum _
        (fun j _ => hw j)
    have hfirst : 2 * p.β ^ (2 * t) * (∫ ω, fro (S.M0 ω) ^ 2 ∂P) ≤ 2 * (p.cM * B) := by
      have hi : 0 ≤ ∫ ω, fro (S.M0 ω) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
      have hpw : p.β ^ (2 * t) ≤ 1 := pow_le_one₀ p.hβ.1 p.hβ.2.le
      have hcM : 0 ≤ p.cM * B := mul_nonneg p.hcM (by positivity)
      calc
        2 * p.β ^ (2 * t) * (∫ ω, fro (S.M0 ω) ^ 2 ∂P)
            ≤ 2 * p.β ^ (2 * t) * (p.cM * B) :=
              mul_le_mul_of_nonneg_left hM.2
                (mul_nonneg (by norm_num) (pow_nonneg p.hβ.1 _))
        _ ≤ 2 * 1 * (p.cM * B) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpw (by norm_num)) hcM
        _ = 2 * (p.cM * B) := by ring
    have hforce : 2 * ∑ j ∈ Finset.range t,
        emaW p.β j * (∫ ω, g (t - 1 - j) ω ∂P) ≤
        4 * cMConst p.CSig p.γstar * rhi * B := by
      have hc : 0 ≤ 2 * cMConst p.CSig p.γstar * rhi * B := by
        unfold cMConst
        positivity
      calc
        2 * ∑ j ∈ Finset.range t, emaW p.β j * (∫ ω, g (t - 1 - j) ω ∂P)
            ≤ 2 * ∑ j ∈ Finset.range t,
              emaW p.β j * (2 * cMConst p.CSig p.γstar * rhi * B) := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                exact Finset.sum_le_sum fun j _ =>
                  mul_le_mul_of_nonneg_left (hg (t - 1 - j)).2 (hw j)
        _ = 2 * ((∑ j ∈ Finset.range t, emaW p.β j) *
              (2 * cMConst p.CSig p.γstar * rhi * B)) := by rw [Finset.sum_mul]
        _ = 2 * (2 * cMConst p.CSig p.γstar * rhi * B) *
              (∑ j ∈ Finset.range t, emaW p.β j) := by ring
        _ ≤ 2 * (2 * cMConst p.CSig p.γstar * rhi * B) * 1 := by gcongr
        _ = 4 * cMConst p.CSig p.γstar * rhi * B := by ring
    change ∫ ω, 2 * p.β ^ (2 * t) * fro (S.M0 ω) ^ 2 +
        2 * ∑ j ∈ Finset.range t, emaW p.β j * g (t - 1 - j) ω ∂P ≤ _
    rw [integral_add (hM.1.const_mul _) (hsumint.const_mul _), integral_const_mul,
      integral_const_mul, integral_finset_sum _ (fun j _ => (hg (t - 1 - j)).1.const_mul _)]
    simp_rw [integral_const_mul]
    linarith
  · have hB0 : B = 0 := Nat.eq_zero_of_not_pos hB
    subst B
    have hmax : max m n = 0 := by
      have hs := S.size.1
      simp only [Nat.cast_zero, mul_zero] at hs
      exact Nat.le_zero.mp (by exact_mod_cast hs)
    have hm : m = 0 := Nat.le_zero.mp (Nat.le_max_left m n |>.trans (le_of_eq hmax))
    have hn : n = 0 := Nat.le_zero.mp (Nat.le_max_right m n |>.trans (le_of_eq hmax))
    subst m
    subst n
    have hz : ({ω | (t : ℕ∞) ≤ τ ω}.indicator
        (fun ω => fro (dynBuf S t ω) ^ 2)) = 0 := by
      funext ω
      by_cases hω : (t : ℕ∞) ≤ τ ω
      · rw [Set.indicator_of_mem (show ω ∈ {ω | (t : ℕ∞) ≤ τ ω} from hω)]
        have hb : dynBuf S t ω = 0 := Subsingleton.elim _ _
        rw [hb, movement_fro_sq]
        simp
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | (t : ℕ∞) ≤ τ ω} from hω)]
        rfl
    rw [hz]
    simp

private lemma buffer_opNorm_continuous {m n : ℕ} :
    Continuous (fun A : Mat m n => opNorm A) := by
  open scoped Matrix.Norms.L2Operator in
    simpa only [opNorm_eq_norm] using (continuous_norm : Continuous (fun A : Mat m n => ‖A‖))

private lemma buffer_opNorm_le_fro {m n : ℕ} (K : Mat m n) : opNorm K ≤ fro K := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, fro,
    ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have hK : ∀ i, ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)) x).ofLp i =
      ∑ j, K i j * x.ofLp j := fun i => by
    simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
  have hi : ∀ i, ‖∑ j, K i j * x.ofLp j‖ ^ 2 ≤
      (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) := by
    intro i
    calc
      ‖∑ j, K i j * x.ofLp j‖ ^ 2 ≤ (∑ j, ‖K i j‖ * ‖x.ofLp j‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
        exact norm_mul _ _
      _ ≤ (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc
    ∑ i, ‖((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)) x).ofLp i‖ ^ 2 =
        ∑ i, ‖∑ j, K i j * x.ofLp j‖ ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [hK i]
    _ ≤ ∑ i, (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => hi i
    _ = (∑ i, ∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) :=
      (Finset.sum_mul _ _ _).symm

private lemma buffer_op_unroll_bound {m n : ℕ} (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (t : ℕ) (M : Mat m n) (G : ℕ → Mat m n) :
    opNorm (β ^ t • M + ∑ j ∈ Finset.range t, emaW β j • G j) ^ 2 ≤
      2 * β ^ (2 * t) * opNorm M ^ 2 +
        2 * ∑ j ∈ Finset.range t, emaW β j * opNorm (G j) ^ 2 := by
  have hw : ∀ j, 0 ≤ emaW β j := fun j => by
    unfold emaW
    positivity
  have hsum : opNorm (∑ j ∈ Finset.range t, emaW β j • G j) ≤
      ∑ j ∈ Finset.range t, emaW β j * opNorm (G j) := by
    open scoped Matrix.Norms.L2Operator in
      simpa only [opNorm_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw _)] using
        norm_sum_le (Finset.range t) (fun j => emaW β j • G j)
  have hadd : opNorm (β ^ t • M + ∑ j ∈ Finset.range t, emaW β j • G j) ≤
      opNorm (β ^ t • M) + opNorm (∑ j ∈ Finset.range t, emaW β j • G j) := by
    open scoped Matrix.Norms.L2Operator in
      simpa only [opNorm_eq_norm] using
        norm_add_le (β ^ t • M) (∑ j ∈ Finset.range t, emaW β j • G j)
  have htotal : opNorm (β ^ t • M + ∑ j ∈ Finset.range t, emaW β j • G j) ≤
      β ^ t * opNorm M + ∑ j ∈ Finset.range t, emaW β j * opNorm (G j) := by
    calc
      opNorm (β ^ t • M + ∑ j ∈ Finset.range t, emaW β j • G j)
          ≤ opNorm (β ^ t • M) + opNorm (∑ j ∈ Finset.range t, emaW β j • G j) := hadd
      _ ≤ β ^ t * opNorm M + ∑ j ∈ Finset.range t, emaW β j * opNorm (G j) := by
        open scoped Matrix.Norms.L2Operator in
          simpa only [opNorm_eq_norm, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (pow_nonneg hβ0 _)] using add_le_add le_rfl hsum
  have hsq := pow_le_pow_left₀ (movement_opNorm_nonneg _) htotal 2
  have hweighted := buffer_weighted_sq β hβ0 hβ1 t (fun j => opNorm (G j))
  calc
    opNorm (β ^ t • M + ∑ j ∈ Finset.range t, emaW β j • G j) ^ 2
        ≤ (β ^ t * opNorm M +
          ∑ j ∈ Finset.range t, emaW β j * opNorm (G j)) ^ 2 := hsq
    _ ≤ 2 * (β ^ t * opNorm M) ^ 2 +
        2 * (∑ j ∈ Finset.range t, emaW β j * opNorm (G j)) ^ 2 := by
      nlinarith [sq_nonneg (β ^ t * opNorm M -
        ∑ j ∈ Finset.range t, emaW β j * opNorm (G j))]
    _ ≤ 2 * β ^ (2 * t) * opNorm M ^ 2 +
        2 * ∑ j ∈ Finset.range t, emaW β j * opNorm (G j) ^ 2 := by
      have heq : (β ^ t * opNorm M) ^ 2 = β ^ (2 * t) * opNorm M ^ 2 := by ring
      calc
        2 * (β ^ t * opNorm M) ^ 2 +
            2 * (∑ j ∈ Finset.range t, emaW β j * opNorm (G j)) ^ 2 =
            2 * β ^ (2 * t) * opNorm M ^ 2 +
              2 * (∑ j ∈ Finset.range t, emaW β j * opNorm (G j)) ^ 2 := by
                rw [heq]
                ring
        _ ≤ 2 * β ^ (2 * t) * opNorm M ^ 2 +
            2 * ∑ j ∈ Finset.range t, emaW β j * opNorm (G j) ^ 2 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hweighted (by norm_num))

private lemma buffer_stopped_pathwise_op {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (τ : Ω → ℕ∞)
    (t : ℕ) (ω : Ω) :
    {ω | (t : ℕ∞) ≤ τ ω}.indicator (fun ω => opNorm (dynBuf S t ω) ^ 2) ω ≤
      2 * p.β ^ (2 * t) * opNorm (S.M0 ω) ^ 2 +
        2 * ∑ j ∈ Finset.range t, emaW p.β j *
          opNorm ({ω | ((t - 1 - j : ℕ) : ℕ∞) < τ ω}.indicator
            (fun ω => batchGrad (dynDelta S (t - 1 - j) ω)
              (physBatch S.C (S.cs.act (((t - 1 - j : ℕ) : ℤ) + 1)) ω)) ω) ^ 2 := by
  cases t with
  | zero =>
      rw [Set.indicator_of_mem (show ω ∈ {ω | ((0 : ℕ) : ℕ∞) ≤ τ ω} by simp)]
      simp only [pow_zero, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      simp only [dynBuf, dynState, runRand, run, dynStart, initState]
      nlinarith [sq_nonneg (opNorm (S.M0 ω))]
  | succ k =>
      by_cases ht : ((k + 1 : ℕ) : ℕ∞) ≤ τ ω
      · rw [Set.indicator_of_mem (show ω ∈ {ω | (((k + 1 : ℕ) : ℕ∞) ≤ τ ω)} from ht)]
        simp only [Nat.add_sub_cancel]
        have heq : dynBuf S (k + 1) ω =
            p.β ^ (k + 1) • S.M0 ω +
              ∑ j ∈ Finset.range (k + 1), emaW p.β j •
                batchGrad (dynDelta S (k - j) ω)
                  (physBatch S.C (S.cs.act (((k - j : ℕ) : ℤ) + 1)) ω) := by
          simpa only [dynBuf, dynState, runRand, dynStart, initState, dynDelta, devRand,
            dynBatch, S.alg_β] using
            eqn_app_setup_unrolled S.C S.alg (dynStart S ω)
              (fun u => dynBatch S u ω) k
        have hstop : ∀ j ∈ Finset.range (k + 1),
            ((k - j : ℕ) : ℕ∞) < τ ω := by
          intro j hj
          exact lt_of_lt_of_le (by exact_mod_cast (Nat.sub_lt_succ k j)) ht
        have hbase := buffer_op_unroll_bound p.β p.hβ.1 p.hβ.2 (k + 1) (S.M0 ω)
          (fun j => batchGrad (dynDelta S (k - j) ω)
            (physBatch S.C (S.cs.act (((k - j : ℕ) : ℤ) + 1)) ω))
        rw [heq]
        calc
          opNorm (p.β ^ (k + 1) • S.M0 ω +
              ∑ j ∈ Finset.range (k + 1), emaW p.β j •
                batchGrad (dynDelta S (k - j) ω)
                  (physBatch S.C (S.cs.act (((k - j : ℕ) : ℤ) + 1)) ω)) ^ 2
              ≤ 2 * p.β ^ (2 * (k + 1)) * opNorm (S.M0 ω) ^ 2 +
                2 * ∑ j ∈ Finset.range (k + 1), emaW p.β j *
                  opNorm (batchGrad (dynDelta S (k - j) ω)
                    (physBatch S.C (S.cs.act (((k - j : ℕ) : ℤ) + 1)) ω)) ^ 2 := hbase
          _ = 2 * p.β ^ (2 * (k + 1)) * opNorm (S.M0 ω) ^ 2 +
                2 * ∑ j ∈ Finset.range (k + 1), emaW p.β j *
                  opNorm ({ω | ((k - j : ℕ) : ℕ∞) < τ ω}.indicator
                    (fun ω => batchGrad (dynDelta S (k - j) ω)
                      (physBatch S.C (S.cs.act (((k - j : ℕ) : ℤ) + 1)) ω)) ω) ^ 2 := by
            congr 2
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [Set.indicator_of_mem (show ω ∈ {ω | ((k - j : ℕ) : ℕ∞) < τ ω} from hstop j hj)]
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | (((k + 1 : ℕ) : ℕ∞) ≤ τ ω)} from ht)]
        have hw : ∀ j, 0 ≤ emaW p.β j := fun j => by
          unfold emaW
          exact mul_nonneg (by linarith [p.hβ.2]) (pow_nonneg p.hβ.1 _)
        have hs : 0 ≤ ∑ j ∈ Finset.range (k + 1), emaW p.β j *
            opNorm ({ω | ((k + 1 - 1 - j : ℕ) : ℕ∞) < τ ω}.indicator
              (fun ω => batchGrad (dynDelta S (k + 1 - 1 - j) ω)
                (physBatch S.C (S.cs.act (((k + 1 - 1 - j : ℕ) : ℤ) + 1)) ω)) ω) ^ 2 :=
          Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
        exact add_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg p.hβ.1 _)) (sq_nonneg _))
          (mul_nonneg (by norm_num) hs)

private lemma buffer_indicator_op_sq {Ω : Type*} {m n : ℕ} (A : Set Ω)
    (F : Ω → Mat m n) (ω : Ω) :
    opNorm (A.indicator F ω) ^ 2 = A.indicator (fun ω => opNorm (F ω) ^ 2) ω := by
  by_cases hω : ω ∈ A
  · simp [Set.indicator_of_mem hω]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
    unfold opNorm
    simp

private lemma buffer_M0_op {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) :
    Integrable (fun ω => opNorm (S.M0 ω) ^ 2) P ∧
      ∫ ω, opNorm (S.M0 ω) ^ 2 ∂P ≤ p.cM * B := by
  have hF := buffer_M0_fro S
  have hm : Measurable (fun ω => opNorm (S.M0 ω) ^ 2) :=
    (buffer_opNorm_continuous.measurable.comp S.M0_meas).pow_const 2
  have hle : ∀ ω, opNorm (S.M0 ω) ^ 2 ≤ fro (S.M0 ω) ^ 2 := fun ω =>
    pow_le_pow_left₀ (movement_opNorm_nonneg _) (buffer_opNorm_le_fro _) 2
  have hint : Integrable (fun ω => opNorm (S.M0 ω) ^ 2) P := by
    refine Integrable.mono' hF.1 hm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hle ω
  refine ⟨hint, (integral_mono_ae hint hF.1 (ae_of_all _ hle)).trans hF.2⟩

/-- `lem:app-dyn-buffer`, snapshot `cr-2026-10-23`, part (ii): the second bound with `‖·‖` the operator
norm. The constant `K` depends on the fixed parameters and `𝒦` only and is quantified before the
dimensions (`section.tex` l. 1531: "the constants called `C`"). Statement verbatim from `section.tex`
(ll. 1531–1539):
```latex
\begin{lemma}[Stopped buffer moments]\label{lem:app-dyn-buffer}
Let $\mathcal K=\mathcal K(r_-,r_+,E)$, and let $\tau$ be a time such that
whether $t<\tau$ is decided by the past $\cF_t$, and such that $\Dt\in\mathcal K$
for $t<\tau$. Then for every $t\ge0$,
\[
\EE\big[\mathbf 1_{t\le\tau}\norm{M^\circ_{t-1}}_\F^2\big]\le2c_MB+4C_Mr_+B,\qquad
\EE\big[\mathbf 1_{t\le\tau}\norm{M^\circ_{t-1}}^2\big]\le2\bmom^{2t}c_MB+C\log^2(2B).
\]
\end{lemma}
```
-/
theorem lem_app_dyn_buffer_ii (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) (rlo rhi E : ℝ)
    (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ K : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (m n B : ℕ)
      (S : DynSetup p P m n B) (τ : Ω → ℕ∞),
      (∀ t : ℕ, MeasurableSet[dynPast S t] {ω | (t : ℕ∞) < τ ω}) →
      (∀ (t : ℕ) (ω : Ω), (t : ℕ∞) < τ ω → dynDelta S t ω ∈ admSetOf S.C (rlo, rhi, E)) →
      ∀ t : ℕ,
        Integrable ({ω | (t : ℕ∞) ≤ τ ω}.indicator (fun ω => opNorm (dynBuf S t ω) ^ 2)) P ∧
        ∫ ω, {ω | (t : ℕ∞) ≤ τ ω}.indicator (fun ω => opNorm (dynBuf S t ω) ^ 2) ω ∂P ≤
          2 * p.β ^ (2 * t) * (p.cM * B) + K * Real.log (2 * (B : ℝ)) ^ 2 := by
  obtain ⟨K0, hbatch⟩ := lem_app_dyn_batch_iv_ii certOp p.γstar p.CSig
  refine ⟨4 * K0 ^ 2 * rhi, ?_⟩
  intro Ω _ P _ m n B S τ hτ hK t
  by_cases hB : 0 < B
  · have hrhi : 0 ≤ rhi := le_trans hrlo.le hle
    have hM := buffer_M0_op S
    let g : ℕ → Ω → ℝ := fun u => {ω | (u : ℕ∞) < τ ω}.indicator
      (fun ω => opNorm (batchGrad (dynDelta S u ω)
        (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω)) ^ 2)
    have hg : ∀ u, Integrable (g u) P ∧
        ∫ ω, g u ω ∂P ≤
          2 * K0 ^ 2 * rhi * Real.log (2 * (B : ℝ)) ^ 2 := by
      intro u
      let A : Set Ω := {ω | (u : ℕ∞) < τ ω}
      let D : Ω → Mat m n := A.indicator (dynDelta S u)
      have hA : MeasurableSet[dynPast S u] A := hτ u
      have hD : Measurable[dynPast S u] D := (buffer_delta_meas S u).indicator hA
      have hrotD : Measurable[dynPast S u] (fun ω => rOut S.C * D ω * rIn S.C) := by
        apply buffer_mat_meas
        intro i j
        simp only [Matrix.mul_apply]
        fun_prop
      have hsq : Measurable[dynPast S u]
          (fun ω => fro (rOut S.C * D ω * rIn S.C) ^ 2) :=
        buffer_fro_sq_meas.comp hrotD
      have hsix : Measurable[dynPast S u]
          (fun ω => fro (rOut S.C * D ω * rIn S.C) ^ 6) := by
        convert hsq.pow_const 3 using 1
        funext ω
        ring
      have hrot_bd : ∀ ω, fro (rOut S.C * D ω * rIn S.C) ^ 2 ≤ 2 * rhi := by
        intro ω
        by_cases hω : ω ∈ A
        · have hu := (hK u ω hω).2.1
          rw [eqn_app_setup_whitened_risk] at hu
          simpa only [D, Set.indicator_of_mem hω, Arot] using (show
            fro (Arot S.C (dynDelta S u ω)) ^ 2 ≤ 2 * rhi by linarith)
        · simp [D, Set.indicator_of_notMem hω, fro, hrhi]
      have hEint2 : Integrable (fun ω => fro (rOut S.C * D ω * rIn S.C) ^ 2) P :=
        Integrable.of_bound (hsq.mono (buffer_past_le S u) le_rfl).aestronglyMeasurable
          (2 * rhi) (ae_of_all _ fun ω => by
            rw [Real.norm_of_nonneg (sq_nonneg _)]
            exact hrot_bd ω)
      have hEint6 : Integrable (fun ω => fro (rOut S.C * D ω * rIn S.C) ^ 6) P :=
        Integrable.of_bound (hsix.mono (buffer_past_le S u) le_rfl).aestronglyMeasurable
          ((2 * rhi) ^ 3) (ae_of_all _ fun ω => by
            rw [Real.norm_of_nonneg (pow_nonneg (movement_fro_nn _) 6)]
            calc
              fro (rOut S.C * D ω * rIn S.C) ^ 6 =
                  (fro (rOut S.C * D ω * rIn S.C) ^ 2) ^ 3 := by ring
              _ ≤ (2 * rhi) ^ 3 :=
                pow_le_pow_left₀ (sq_nonneg _) (hrot_bd ω) 3)
      obtain ⟨⟨hGint, hcond⟩, _⟩ := hbatch m n B S.C hB S.size Ω
        (dynPast S u) P (S.cs.act ((u : ℤ) + 1)) (buffer_iid S u)
        (buffer_past_le S u) (buffer_indep_past_batch S u) D hD hEint2 hEint6
      have hfun : (fun ω => opNorm (batchGrad (D ω)
          (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω)) ^ 2) =
          A.indicator (fun ω => opNorm (batchGrad (dynDelta S u ω)
            (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω)) ^ 2) := by
        funext ω
        by_cases hω : ω ∈ A
        · simp [D, Set.indicator_of_mem hω]
        · have hg0 : batchGrad (0 : Mat m n)
              (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω) = 0 := by
            ext i j
            simp [grad, resid, Matrix.mulVec]
          simp only [D, Set.indicator_of_notMem hω, hg0]
          unfold opNorm
          simp
      have hcond0 : 0 ≤ᵐ[P] condExp (dynPast S u) P
          (fun ω => opNorm (batchGrad (D ω)
            (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω)) ^ 2) :=
        condExp_nonneg (ae_of_all _ fun ω => sq_nonneg _)
      change Integrable (A.indicator (fun ω => opNorm (batchGrad (dynDelta S u ω)
          (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω)) ^ 2)) P ∧
        ∫ ω, A.indicator (fun ω => opNorm (batchGrad (dynDelta S u ω)
          (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω)) ^ 2) ω ∂P ≤
            2 * K0 ^ 2 * rhi * Real.log (2 * (B : ℝ)) ^ 2
      rw [← hfun]
      refine ⟨hGint, ?_⟩
      calc
        ∫ ω, opNorm (batchGrad (D ω)
            (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω)) ^ 2 ∂P =
            ∫ ω, condExp (dynPast S u) P
              (fun ω' => opNorm (batchGrad (D ω')
                (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω')) ^ 2) ω ∂P :=
          (integral_condExp (buffer_past_le S u)).symm
        _ ≤ ∫ _ω, 2 * K0 ^ 2 * rhi * Real.log (2 * (B : ℝ)) ^ 2 ∂P := by
          apply integral_mono_ae integrable_condExp (integrable_const _)
          filter_upwards [hcond, hcond0] with ω hc hc0
          have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg _) hc 2
          calc
            condExp (dynPast S u) P
                (fun ω' => opNorm (batchGrad (D ω')
                  (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω')) ^ 2) ω =
                Real.sqrt (condExp (dynPast S u) P
                  (fun ω' => opNorm (batchGrad (D ω')
                    (physBatch S.C (S.cs.act ((u : ℤ) + 1)) ω')) ^ 2) ω) ^ 2 :=
              (Real.sq_sqrt hc0).symm
            _ ≤ (K0 * Real.log (2 * (B : ℝ)) *
                fro (rOut S.C * D ω * rIn S.C)) ^ 2 := hsquare
            _ ≤ 2 * K0 ^ 2 * rhi * Real.log (2 * (B : ℝ)) ^ 2 := by
              have hh := mul_le_mul_of_nonneg_left (hrot_bd ω)
                (sq_nonneg (K0 * Real.log (2 * (B : ℝ))))
              nlinarith
        _ = 2 * K0 ^ 2 * rhi * Real.log (2 * (B : ℝ)) ^ 2 := by
          rw [integral_const, probReal_univ]
          simp
    let R : Ω → ℝ := fun ω =>
      2 * p.β ^ (2 * t) * opNorm (S.M0 ω) ^ 2 +
        2 * ∑ j ∈ Finset.range t, emaW p.β j * g (t - 1 - j) ω
    have hsumint : Integrable
        (fun ω => ∑ j ∈ Finset.range t, emaW p.β j * g (t - 1 - j) ω) P :=
      integrable_finset_sum _ fun j _ => (hg (t - 1 - j)).1.const_mul _
    have hRint : Integrable R P :=
      (hM.1.const_mul (2 * p.β ^ (2 * t))).add (hsumint.const_mul 2)
    have htarget_meas : Measurable
        ({ω | (t : ℕ∞) ≤ τ ω}.indicator (fun ω => opNorm (dynBuf S t ω) ^ 2)) := by
      have hb := (buffer_state_meas S t).2.mono (buffer_past_le S t) le_rfl
      exact ((buffer_opNorm_continuous.measurable.pow_const 2).comp hb).indicator
        (buffer_stop_event_meas S τ hτ t)
    have hpoint : ∀ ω, {ω | (t : ℕ∞) ≤ τ ω}.indicator
        (fun ω => opNorm (dynBuf S t ω) ^ 2) ω ≤ R ω := by
      intro ω
      have hp := buffer_stopped_pathwise_op S τ t ω
      simp_rw [buffer_indicator_op_sq] at hp
      exact hp
    have hRnonneg : ∀ ω, 0 ≤ R ω := by
      intro ω
      have hw : ∀ j, 0 ≤ emaW p.β j := fun j => by
        unfold emaW
        exact mul_nonneg (by linarith [p.hβ.2]) (pow_nonneg p.hβ.1 _)
      have hg0 : ∀ u ω, 0 ≤ g u ω := fun u ω => by
        unfold g
        exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
      exact add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg p.hβ.1 _)) (sq_nonneg _))
        (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (hg0 _ _)))
    have htarget_int : Integrable
        ({ω | (t : ℕ∞) ≤ τ ω}.indicator (fun ω => opNorm (dynBuf S t ω) ^ 2)) P := by
      refine Integrable.mono' hRint htarget_meas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
      rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω)]
      exact hpoint ω
    refine ⟨htarget_int, (integral_mono_ae htarget_int hRint (ae_of_all _ hpoint)).trans ?_⟩
    have hw : ∀ j, 0 ≤ emaW p.β j := fun j => by
      unfold emaW
      exact mul_nonneg (by linarith [p.hβ.2]) (pow_nonneg p.hβ.1 _)
    have hwsum : ∑ j ∈ Finset.range t, emaW p.β j ≤ 1 := by
      rw [← tsum_emaW p.hβ.1 p.hβ.2]
      exact ((summable_geometric_of_lt_one p.hβ.1 p.hβ.2).mul_left (1 - p.β)).sum_le_tsum _
        (fun j _ => hw j)
    have hfirst : 2 * p.β ^ (2 * t) * (∫ ω, opNorm (S.M0 ω) ^ 2 ∂P) ≤
        2 * p.β ^ (2 * t) * (p.cM * B) :=
      mul_le_mul_of_nonneg_left hM.2
        (mul_nonneg (by norm_num) (pow_nonneg p.hβ.1 _))
    have hforce : 2 * ∑ j ∈ Finset.range t,
        emaW p.β j * (∫ ω, g (t - 1 - j) ω ∂P) ≤
        (4 * K0 ^ 2 * rhi) * Real.log (2 * (B : ℝ)) ^ 2 := by
      have hc : 0 ≤ 2 * K0 ^ 2 * rhi * Real.log (2 * (B : ℝ)) ^ 2 := by positivity
      calc
        2 * ∑ j ∈ Finset.range t, emaW p.β j * (∫ ω, g (t - 1 - j) ω ∂P)
            ≤ 2 * ∑ j ∈ Finset.range t,
              emaW p.β j * (2 * K0 ^ 2 * rhi * Real.log (2 * (B : ℝ)) ^ 2) := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                exact Finset.sum_le_sum fun j _ =>
                  mul_le_mul_of_nonneg_left (hg (t - 1 - j)).2 (hw j)
        _ = 2 * ((∑ j ∈ Finset.range t, emaW p.β j) *
              (2 * K0 ^ 2 * rhi * Real.log (2 * (B : ℝ)) ^ 2)) := by
                rw [Finset.sum_mul]
        _ = 2 * (2 * K0 ^ 2 * rhi * Real.log (2 * (B : ℝ)) ^ 2) *
              (∑ j ∈ Finset.range t, emaW p.β j) := by ring
        _ ≤ 2 * (2 * K0 ^ 2 * rhi * Real.log (2 * (B : ℝ)) ^ 2) * 1 := by gcongr
        _ = (4 * K0 ^ 2 * rhi) * Real.log (2 * (B : ℝ)) ^ 2 := by ring
    change ∫ ω, 2 * p.β ^ (2 * t) * opNorm (S.M0 ω) ^ 2 +
        2 * ∑ j ∈ Finset.range t, emaW p.β j * g (t - 1 - j) ω ∂P ≤ _
    rw [integral_add (hM.1.const_mul _) (hsumint.const_mul _), integral_const_mul,
      integral_const_mul, integral_finset_sum _ (fun j _ => (hg (t - 1 - j)).1.const_mul _)]
    simp_rw [integral_const_mul]
    linarith
  · have hB0 : B = 0 := Nat.eq_zero_of_not_pos hB
    subst B
    have hmax : max m n = 0 := by
      have hs := S.size.1
      simp only [Nat.cast_zero, mul_zero] at hs
      exact Nat.le_zero.mp (by exact_mod_cast hs)
    have hm : m = 0 := Nat.le_zero.mp (Nat.le_max_left m n |>.trans (le_of_eq hmax))
    have hn : n = 0 := Nat.le_zero.mp (Nat.le_max_right m n |>.trans (le_of_eq hmax))
    subst m
    subst n
    have hz : ({ω | (t : ℕ∞) ≤ τ ω}.indicator
        (fun ω => opNorm (dynBuf S t ω) ^ 2)) = 0 := by
      funext ω
      by_cases hω : (t : ℕ∞) ≤ τ ω
      · rw [Set.indicator_of_mem (show ω ∈ {ω | (t : ℕ∞) ≤ τ ω} from hω)]
        have hb : dynBuf S t ω = 0 := Subsingleton.elim _ _
        rw [hb]
        unfold opNorm
        simp
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | (t : ℕ∞) ≤ τ ω} from hω)]
        rfl
    rw [hz]
    simp

/-! ## `lem:app-dyn-coupling`: helpers -/

private lemma coupling_grad_sub {m n B : ℕ} (D1 D2 : Mat m n) (b : Batch m n B) :
    grad (D1 - D2) b = grad D1 b - grad D2 b := by
  unfold grad resid
  simp [Matrix.sub_mulVec, dotProduct_sub, sub_smul, Finset.sum_sub_distrib, smul_sub]

private lemma coupling_grad_zero {m n B : ℕ} (b : Batch m n B) : grad (0 : Mat m n) b = 0 := by
  ext i j
  simp [grad, resid, Matrix.mulVec]

private lemma coupling_buf_succ {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (u : ℕ) (ω : Ω) :
    dynBuf S (u + 1) ω =
      p.β • dynBuf S u ω + (1 - p.β) • batchGrad (dynDelta S u ω) (dynBatch S u ω) := by
  change S.alg.β • _ + (1 - S.alg.β) • _ = _
  rw [S.alg_β]
  rfl

private lemma coupling_errM_unroll {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) (ω : Ω) (k : ℕ) :
    dynBuf S (t + k) ω -
        emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t (dynBuf S t ω) k =
      ∑ j ∈ Finset.range k, emaW p.β (k - 1 - j) •
        batchGrad (dynDelta S (t + j) ω - dynDelta S t ω) (dynBatch S (t + j) ω) := by
  induction k with
  | zero => simp [emaChain]
  | succ k ih =>
    rw [← add_assoc, coupling_buf_succ S (t + k) ω]
    have hch : emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
        (dynBuf S t ω) (k + 1) =
        p.β • emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
          (dynBuf S t ω) k + (1 - p.β) • batchGrad (dynDelta S t ω) (dynBatch S (t + k) ω) := by
      simp only [emaChain]
      congr 3
    rw [hch, Finset.sum_range_succ]
    have hsum : ∑ j ∈ Finset.range k, emaW p.β (k + 1 - 1 - j) •
        batchGrad (dynDelta S (t + j) ω - dynDelta S t ω) (dynBatch S (t + j) ω) =
        p.β • ∑ j ∈ Finset.range k, emaW p.β (k - 1 - j) •
        batchGrad (dynDelta S (t + j) ω - dynDelta S t ω) (dynBatch S (t + j) ω) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j < k := Finset.mem_range.mp hj
      have : k + 1 - 1 - j = (k - 1 - j) + 1 := by omega
      rw [this, smul_smul]
      congr 1
      unfold emaW
      rw [pow_succ]
      ring
    rw [hsum, ← ih]
    simp only [Nat.add_sub_cancel, Nat.sub_self, coupling_grad_sub, smul_sub, emaW, pow_zero,
      mul_one]
    module

private lemma coupling_wsum_le_one (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (k : ℕ) :
    ∑ j ∈ Finset.range k, emaW β (k - 1 - j) ≤ 1 := by
  rw [Finset.sum_range_reflect (fun j => emaW β j) k]
  rw [← tsum_emaW hβ0 hβ1]
  exact ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (1 - β)).sum_le_tsum _
    (fun j _ => by unfold emaW; exact mul_nonneg (by linarith) (pow_nonneg hβ0 _))

private lemma coupling_emaW_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (j : ℕ) :
    0 ≤ emaW β j := by
  unfold emaW
  exact mul_nonneg (by linarith) (pow_nonneg hβ0 _)

private lemma coupling_weighted_sq (k : ℕ) (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hsum : ∑ j ∈ Finset.range k, w j ≤ 1) (x : ℕ → ℝ) :
    (∑ j ∈ Finset.range k, w j * x j) ^ 2 ≤ ∑ j ∈ Finset.range k, w j * x j ^ 2 := by
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range k)
    (r := fun j => w j * x j) (f := fun j => w j) (g := fun j => w j * x j ^ 2)
    (fun j _ => hw j) (fun j _ => mul_nonneg (hw j) (sq_nonneg _))
    (fun j _ => by ring_nf; nlinarith [hw j, sq_nonneg (x j)])
  have hright : 0 ≤ ∑ j ∈ Finset.range k, w j * x j ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
  exact hs.trans (by nlinarith)

private lemma coupling_norm_sum_sq {m n : ℕ} (N : Mat m n → ℝ)
    (hsmul : ∀ (c : ℝ) (x : Mat m n), 0 ≤ c → N (c • x) = c * N x)
    (hadd : ∀ x y, N (x + y) ≤ N x + N y) (hzero : N 0 = 0) (hN0 : ∀ x, 0 ≤ N x)
    (k : ℕ) (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j ∈ Finset.range k, w j ≤ 1)
    (x : ℕ → Mat m n) :
    N (∑ j ∈ Finset.range k, w j • x j) ^ 2 ≤ ∑ j ∈ Finset.range k, w j * N (x j) ^ 2 := by
  have h1 : ∀ s : ℕ, N (∑ j ∈ Finset.range s, w j • x j) ≤ ∑ j ∈ Finset.range s, w j * N (x j) := by
    intro s
    induction s with
    | zero => simp [hzero]
    | succ s ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      calc N (∑ j ∈ Finset.range s, w j • x j + w s • x s)
          ≤ N (∑ j ∈ Finset.range s, w j • x j) + N (w s • x s) := hadd _ _
        _ ≤ _ := by rw [hsmul _ _ (hw s)]; linarith
  have h2 := pow_le_pow_left₀ (hN0 _) (h1 k) 2
  exact h2.trans (coupling_weighted_sq k w hw hsum (fun j => N (x j)))

private lemma coupling_fro_props {m n : ℕ} :
    (∀ (c : ℝ) (x : Mat m n), 0 ≤ c → fro (c • x) = c * fro x) ∧
    (∀ x y : Mat m n, fro (x + y) ≤ fro x + fro y) ∧ fro (0 : Mat m n) = 0 ∧
    (∀ x : Mat m n, 0 ≤ fro x) := by
  open scoped Matrix.Norms.Frobenius in
  refine ⟨fun c x hc => ?_, fun x y => ?_, by simp [fro], fun x => Real.sqrt_nonneg _⟩
  · simp only [fro_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  · simpa only [fro_eq_norm] using norm_add_le x y

private lemma coupling_op_props {m n : ℕ} :
    (∀ (c : ℝ) (x : Mat m n), 0 ≤ c → opNorm (c • x) = c * opNorm x) ∧
    (∀ x y : Mat m n, opNorm (x + y) ≤ opNorm x + opNorm y) ∧ opNorm (0 : Mat m n) = 0 ∧
    (∀ x : Mat m n, 0 ≤ opNorm x) := by
  open scoped Matrix.Norms.L2Operator in
  refine ⟨fun c x hc => ?_, fun x y => ?_, by simp [opNorm], fun x => ?_⟩
  · simp only [opNorm_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  · simpa only [opNorm_eq_norm] using norm_add_le x y
  · simpa only [opNorm_eq_norm] using norm_nonneg x

private lemma coupling_risk_meas {Ω : Type*} {σ : MeasurableSpace Ω} {m n : ℕ}
    (C : Covariances m n) {D : Ω → Mat m n} (hD : Measurable[σ] D) :
    Measurable[σ] (fun ω => riskSigma C (D ω)) :=
  (show Continuous (fun D : Mat m n => riskSigma C D) by
    unfold riskSigma pairSigma
    fun_prop).measurable.comp hD

private lemma coupling_admSet_meas {m n : ℕ} (C : Covariances m n) (K0 : ℝ × ℝ × ℝ) :
    MeasurableSet (admSetOf C K0) := by
  have hR : Measurable (fun D : Mat m n => riskSigma C D) :=
    (show Continuous (fun D : Mat m n => riskSigma C D) by
      unfold riskSigma pairSigma
      fun_prop).measurable
  have h1 : MeasurableSet {D : Mat m n | K0.1 ≤ riskSigma C D} :=
    measurableSet_le measurable_const hR
  have h2 : MeasurableSet {D : Mat m n | riskSigma C D ≤ K0.2.1} :=
    measurableSet_le hR measurable_const
  have h3 : MeasurableSet {D : Mat m n | fro D ^ 2 ≤ K0.2.2} :=
    measurableSet_le buffer_fro_sq_meas measurable_const
  exact h1.inter (h2.inter h3)

private lemma coupling_A_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) (K0 : ℝ × ℝ × ℝ) :
    MeasurableSet[dynPast S t] (dynInK S t K0) :=
  (buffer_delta_meas S t) (coupling_admSet_meas S.C K0)

private lemma coupling_upd_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (hB : 0 < B) (u : ℕ) :
    Measurable (dynUpd S u) := by
  have hΔ : Measurable (dynDelta S u) :=
    (buffer_delta_meas S u).mono (buffer_past_le S u) le_rfl
  have hΔ' : Measurable (dynDelta S (u + 1)) :=
    (buffer_delta_meas S (u + 1)).mono (buffer_past_le S (u + 1)) le_rfl
  have hh : p.h ≠ 0 := p.hh.ne'
  have heq : dynUpd S u = fun ω => ((B : ℝ) / p.h) • (dynDelta S u ω - dynDelta S (u + 1) ω) := by
    funext ω
    rw [movement_delta_succ, sub_sub_cancel, smul_smul]
    have : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    field_simp
    simp
  rw [heq]
  exact (hΔ.sub hΔ').const_smul ((B : ℝ) / p.h)

private lemma coupling_phys_meas {Ω : Type*} [MeasurableSpace Ω] {m n B : ℕ}
    (C : Covariances m n) {z : Fin B → Ω → Vec m × Vec n} (hz : ∀ a, Measurable (z a)) :
    Measurable (fun ω => physBatch C z ω) := by
  refine buffer_pi_meas (fun a => ?_)
  exact (show Continuous (fun z : Vec m × Vec n => phys C z) by
    unfold phys
    fun_prop).measurable.comp (hz a)

private lemma coupling_ema_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ)
    {D : Ω → Mat m n} (hD : Measurable D) {init : Ω → Mat m n} (hinit : Measurable init)
    (k : ℕ) :
    Measurable (fun ω => emaChain p.β (D ω) (fun s => physBatch S.C (S.cs.act s) ω) t (init ω) k) := by
  induction k with
  | zero => simpa [emaChain] using hinit
  | succ k ih =>
    have hb : Measurable (fun ω => batchGrad (D ω)
        (physBatch S.C (S.cs.act ((t : ℤ) + k + 1)) ω)) :=
      buffer_grad_meas hD (coupling_phys_meas S.C (fun a => S.cs.meas_act _ a))
    simp only [emaChain]
    exact (ih.const_smul p.β).add (hb.const_smul (1 - p.β))

private lemma coupling_chainInit_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ)
    {D : Ω → Mat m n} (hD : Measurable D) :
    Measurable (fun ω => chainInit p.β S.C (D ω) (S.cs.aux (t : ℤ)) ω) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) :=
    inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  unfold chainInit
  refine Measurable.tsum fun j => Measurable.const_smul ?_ (emaW p.β j)
  exact buffer_grad_meas hD (coupling_phys_meas S.C (fun a => S.cs.meas_aux _ j a))

private lemma coupling_Q_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B)
    {D : Ω → Mat m n} (hD : Measurable D) {K : Ω → Mat m n} (hK : Measurable K) :
    Measurable (fun ω => Q (physRidge p S.C (D ω)) (K ω)) := by
  have hρ : ∀ ω, 0 ≤ physRidge p S.C (D ω) := fun ω => by
    unfold physRidge
    exact mul_nonneg (mul_nonneg (by norm_num)
      (by rw [eqn_app_setup_whitened_risk]; positivity)) p.hϱ.le
  have hρm : Measurable (fun ω => (⟨physRidge p S.C (D ω), hρ ω⟩ : Set.Ici (0 : ℝ))) :=
    (((coupling_risk_meas S.C hD).const_mul 2).mul_const p.ϱ).subtype_mk
  exact measurable_Q.comp (hρm.prodMk hK)

private lemma coupling_delta_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) :
    Measurable (dynDelta S t) :=
  (buffer_delta_meas S t).mono (buffer_past_le S t) le_rfl

private lemma coupling_buf_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) :
    Measurable (dynBuf S t) :=
  (buffer_state_meas S t).2.mono (buffer_past_le S t) le_rfl

private lemma coupling_hatN_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t r : ℕ) :
    Measurable (dynHatN p S t r) :=
  coupling_ema_meas S t (coupling_delta_meas S t) (coupling_buf_meas S t) (r + 1)

private lemma coupling_hatV_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t r : ℕ) :
    Measurable (dynHatV p S t r) :=
  coupling_Q_meas S (coupling_delta_meas S t) (coupling_hatN_meas S t r)

private lemma coupling_statN_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t k : ℕ) :
    Measurable (fun ω => emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
      (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) k) :=
  coupling_ema_meas S t (coupling_delta_meas S t)
    (coupling_chainInit_meas S t (coupling_delta_meas S t)) k

private lemma coupling_statV_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t r : ℕ) :
    Measurable (fun ω => stationaryV p S.C S.cs t (dynDelta S t ω) r ω) :=
  coupling_Q_meas S (coupling_delta_meas S t) (coupling_statN_meas S t (r + 1))

private lemma coupling_errM_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t r : ℕ) :
    Measurable (dynErrM p S t r) :=
  (coupling_buf_meas S _).sub (coupling_hatN_meas S t r)

private lemma coupling_errV_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t r : ℕ) :
    Measurable (dynErrV p S t r) :=
  (coupling_hatV_meas S t r).sub (coupling_statV_meas S t r)

private lemma coupling_errS_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (hB : 0 < B) (t r : ℕ) :
    Measurable (dynErrS p S t r) :=
  (coupling_upd_meas S hB _).sub (coupling_hatV_meas S t r)

private lemma coupling_tower {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B)
    {t u : ℕ} (htu : t ≤ u) {f : Ω → ℝ} (hf : Integrable f P) (c : ℝ)
    (h : ∀ᵐ ω ∂P, condExp (dynPast S u) P f ω ≤ c) :
    ∀ᵐ ω ∂P, condExp (dynPast S t) P f ω ≤ c := by
  have h1 := condExp_condExp_of_le (μ := P) (f := f) (buffer_past_mono S htu) (buffer_past_le S u)
  have h2 : condExp (dynPast S t) P (condExp (dynPast S u) P f) ≤ᵐ[P]
      condExp (dynPast S t) P (fun _ => c) :=
    condExp_mono integrable_condExp (integrable_const c) h
  have h3 : condExp (dynPast S t) P (fun _ : Ω => c) = fun _ => c :=
    condExp_const (buffer_past_le S t) c
  filter_upwards [h1, h2] with ω h1ω h2ω
  rw [← h1ω]
  have := h2ω
  rw [h3] at this
  exact this

private lemma coupling_grad_cond_fro {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (hB : 0 < B)
    {t u : ℕ} (htu : t ≤ u) (D : Ω → Mat m n) (hD : Measurable[dynPast S u] D) (c : ℝ)
    (hc : ∀ ω, fro (rOut S.C * D ω * rIn S.C) ^ 2 ≤ c) :
    Integrable (fun ω => fro (batchGrad (D ω) (dynBatch S u ω)) ^ 2) P ∧
    ∀ᵐ ω ∂P, condExp (dynPast S t) P
      (fun ω' => fro (batchGrad (D ω') (dynBatch S u ω')) ^ 2) ω ≤
        cMConst p.CSig p.γstar * B * c := by
  have hrotD : Measurable[dynPast S u] (fun ω => rOut S.C * D ω * rIn S.C) := by
    apply buffer_mat_meas
    intro i j
    simp only [Matrix.mul_apply]
    fun_prop
  have hsq : Measurable[dynPast S u] (fun ω => fro (rOut S.C * D ω * rIn S.C) ^ 2) :=
    buffer_fro_sq_meas.comp hrotD
  have hEint : Integrable (fun ω => fro (rOut S.C * D ω * rIn S.C) ^ 2) P :=
    Integrable.of_bound (hsq.mono (buffer_past_le S u) le_rfl).aestronglyMeasurable c
      (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hc ω)
  obtain ⟨⟨hGint, hcond⟩, _⟩ := lem_app_dyn_batch_iv (dynPast S u) S.C p.γstar p.CSig
    hB S.size (S.cs.act ((u : ℤ) + 1)) (buffer_iid S u) (buffer_past_le S u)
    (buffer_indep_past_batch S u) D hD hEint
  refine ⟨hGint, coupling_tower S htu hGint _ ?_⟩
  filter_upwards [hcond] with ω hω
  have hc0 : 0 ≤ cMConst p.CSig p.γstar * (B : ℝ) := by unfold cMConst; positivity
  exact hω.trans (mul_le_mul_of_nonneg_left (hc ω) hc0)

private lemma coupling_grad_cond_op (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B) (hB : 0 < B) (t u : ℕ) (htu : t ≤ u)
      (D : Ω → Mat m n) (hD : Measurable[dynPast S u] D) (c : ℝ) (hc0 : 0 ≤ c)
      (hc : ∀ ω, fro (rOut S.C * D ω * rIn S.C) ^ 2 ≤ c),
      Integrable (fun ω => opNorm (batchGrad (D ω) (dynBatch S u ω)) ^ 2) P ∧
      ∀ᵐ ω ∂P, condExp (dynPast S t) P
        (fun ω' => opNorm (batchGrad (D ω') (dynBatch S u ω')) ^ 2) ω ≤
          Kb ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * c := by
  obtain ⟨K0, hK0⟩ := lem_app_dyn_batch_iv_ii certOp p.γstar p.CSig
  refine ⟨max K0 0, le_max_right _ _, ?_⟩
  intro Ω _ P _ m n B S hB t u htu D hD c hc0 hc
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) :=
    Real.log_nonneg (by
      have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
      nlinarith)
  have hrotD : Measurable[dynPast S u] (fun ω => rOut S.C * D ω * rIn S.C) := by
    apply buffer_mat_meas
    intro i j
    simp only [Matrix.mul_apply]
    fun_prop
  have hsq : Measurable[dynPast S u] (fun ω => fro (rOut S.C * D ω * rIn S.C) ^ 2) :=
    buffer_fro_sq_meas.comp hrotD
  have hEint : Integrable (fun ω => fro (rOut S.C * D ω * rIn S.C) ^ 2) P :=
    Integrable.of_bound (hsq.mono (buffer_past_le S u) le_rfl).aestronglyMeasurable c
      (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hc ω)
  have hE6 : Integrable (fun ω => fro (rOut S.C * D ω * rIn S.C) ^ 6) P := by
    have h6 : ∀ ω, fro (rOut S.C * D ω * rIn S.C) ^ 6 = (fro (rOut S.C * D ω * rIn S.C) ^ 2) ^ 3 := by
      intro ω; ring
    simp_rw [h6]
    refine Integrable.of_bound ((hsq.pow_const 3).mono (buffer_past_le S u) le_rfl).aestronglyMeasurable
      (c ^ 3) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (sq_nonneg _) (hc ω) 3
  obtain ⟨⟨hGint, hcond⟩, _⟩ := hK0 m n B S.C hB S.size Ω (dynPast S u) P
    (S.cs.act ((u : ℤ) + 1)) (buffer_iid S u) (buffer_past_le S u)
    (buffer_indep_past_batch S u) D hD hEint hE6
  refine ⟨hGint, coupling_tower S htu hGint _ ?_⟩
  filter_upwards [hcond] with ω hω
  have hK : 0 ≤ max K0 0 := le_max_right _ _
  have hfro : 0 ≤ max K0 0 * Real.log (2 * (B : ℝ)) * fro (rOut S.C * D ω * rIn S.C) :=
    mul_nonneg (mul_nonneg hK hlog) (Real.sqrt_nonneg _)
  have hω' := hω.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left K0 0) hlog) (Real.sqrt_nonneg _))
  have h1 := (Real.sqrt_le_iff.mp hω').2
  calc _ ≤ _ := h1
    _ = (max K0 0) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * fro (rOut S.C * D ω * rIn S.C) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hc ω) (by positivity)

private def couplingD {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (A : Set Ω) (t j : ℕ) : Ω → Mat m n :=
  A.indicator (fun ω => dynDelta S (t + j) ω - dynDelta S t ω)

private lemma coupling_D_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) {A : Set Ω} {t : ℕ}
    (hA : MeasurableSet[dynPast S t] A) (j : ℕ) :
    Measurable[dynPast S (t + j)] (couplingD S A t j) := by
  have h1 := buffer_delta_meas S (t + j)
  have h2 := (buffer_delta_meas S t).mono (buffer_past_mono S (Nat.le_add_right t j)) le_rfl
  exact (h1.sub h2).indicator (buffer_past_mono S (Nat.le_add_right t j) _ hA)

private lemma coupling_D_bound {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (hB : 0 < B) (A : Set Ω) (t j : ℕ)
    (ω : Ω) :
    fro (rOut S.C * couplingD S A t j ω * rIn S.C) ^ 2 ≤
      p.CSig ^ 2 * p.h ^ 2 * p.γstar * (j : ℝ) ^ 2 / B := by
  by_cases hω : ω ∈ A
  · have hmv := (movement_all p S ω t (t + j) (Nat.le_add_right t j)).2.1
    have hj : ((t + j : ℕ) : ℝ) - t = j := by push_cast; ring
    rw [hj] at hmv
    have hAr := movement_Arot_bound p S.C S.size
      (dynDelta S (t + j) ω - dynDelta S t ω)
    have hC : 0 ≤ p.CSig := le_trans (by norm_num) p.hC
    have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
    have hsq : 0 ≤ Real.sqrt (B : ℝ) := Real.sqrt_nonneg _
    have hspos : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBpos
    have hcd : couplingD S A t j ω = dynDelta S (t + j) ω - dynDelta S t ω := by
      simp only [couplingD, Set.indicator_of_mem hω]
    have hf : fro (couplingD S A t j ω) ≤ p.h * Real.sqrt p.γstar * j / Real.sqrt B := by
      rw [hcd]; exact hmv
    have hrot : fro (rOut S.C * couplingD S A t j ω * rIn S.C) ≤
        p.CSig * (p.h * Real.sqrt p.γstar * j / Real.sqrt B) := by
      have : fro (Arot S.C (couplingD S A t j ω)) ≤ p.CSig * fro (couplingD S A t j ω) := by
        rw [hcd]; exact hAr
      exact (this.trans (mul_le_mul_of_nonneg_left hf hC))
    have hnn := movement_fro_nn (rOut S.C * couplingD S A t j ω * rIn S.C)
    calc fro (rOut S.C * couplingD S A t j ω * rIn S.C) ^ 2
        ≤ (p.CSig * (p.h * Real.sqrt p.γstar * j / Real.sqrt B)) ^ 2 :=
          pow_le_pow_left₀ hnn hrot 2
      _ = p.CSig ^ 2 * p.h ^ 2 * p.γstar * (j : ℝ) ^ 2 / B := by
          rw [mul_pow, div_pow, mul_pow, mul_pow, Real.sq_sqrt p.hγ, Real.sq_sqrt hBpos.le]
          ring
  · have hz : couplingD S A t j ω = 0 := by simp only [couplingD, Set.indicator_of_notMem hω]
    rw [hz]
    have : rOut S.C * (0 : Mat m n) * rIn S.C = 0 := by simp
    rw [this]
    have : fro (0 : Mat m n) = 0 := by simp [fro]
    rw [this]
    have hC : 0 ≤ p.CSig := le_trans (by norm_num) p.hC
    have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [h0]
    have hγ := p.hγ
    positivity

private lemma coupling_cond_sum {Ω : Type*} (F : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hF : F ≤ m0) (k : ℕ) (a0 : ℝ) (w : ℕ → ℝ)
    (hw : ∀ j, 0 ≤ w j) (f : ℕ → Ω → ℝ) (hf : ∀ j, Integrable (f j) P) (c : ℕ → ℝ)
    (hc : ∀ j, ∀ᵐ ω ∂P, condExp F P (f j) ω ≤ c j)
    (X : Ω → ℝ) (hX : AEStronglyMeasurable X P) (hX0 : ∀ ω, 0 ≤ X ω)
    (hXle : ∀ ω, X ω ≤ a0 + ∑ j ∈ Finset.range k, w j * f j ω) :
    Integrable X P ∧ ∀ᵐ ω ∂P, condExp F P X ω ≤ a0 + ∑ j ∈ Finset.range k, w j * c j := by
  have hSint : Integrable (fun ω => ∑ j ∈ Finset.range k, w j * f j ω) P :=
    integrable_finset_sum _ fun j _ => (hf j).const_mul (w j)
  have hTint : Integrable (fun ω => a0 + ∑ j ∈ Finset.range k, w j * f j ω) P :=
    (integrable_const a0).add hSint
  have hXint : Integrable X P := by
    refine Integrable.mono' hTint hX (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (hX0 ω)]
    exact hXle ω
  refine ⟨hXint, ?_⟩
  have hmono : condExp F P X ≤ᵐ[P] condExp F P (fun ω => a0 + ∑ j ∈ Finset.range k, w j * f j ω) :=
    condExp_mono hXint hTint (ae_of_all _ hXle)
  have hfun : (fun ω => ∑ j ∈ Finset.range k, w j * f j ω) =
      ∑ j ∈ Finset.range k, (w j • f j) := by
    funext ω
    simp [Finset.sum_apply]
  have hadd := condExp_add (μ := P) (integrable_const a0) hSint F
  have hconst : condExp F P (fun _ : Ω => a0) = fun _ => a0 := condExp_const hF a0
  have hsum := condExp_finsetSum (μ := P) (s := Finset.range k) (f := fun j => w j • f j)
    (fun j _ => (hf j).smul (w j)) F
  have hsmul : ∀ j, condExp F P (w j • f j) =ᵐ[P] w j • condExp F P (f j) :=
    fun j => condExp_smul (w j) (f j) F
  have hall : ∀ᵐ ω ∂P, ∀ j ∈ Finset.range k, condExp F P (w j • f j) ω =
      (w j • condExp F P (f j)) ω :=
    (Filter.eventually_all_finset _).2 fun j _ => hsmul j
  have hall2 : ∀ᵐ ω ∂P, ∀ j ∈ Finset.range k, condExp F P (f j) ω ≤ c j :=
    (Filter.eventually_all_finset _).2 fun j _ => hc j
  filter_upwards [hmono, hadd, hsum, hall, hall2] with ω h1 h0 h2 h3 h4
  refine h1.trans ?_
  have h0' : condExp F P (fun ω => a0 + ∑ j ∈ Finset.range k, w j * f j ω) ω =
      a0 + condExp F P (fun ω => ∑ j ∈ Finset.range k, w j * f j ω) ω := by
    have := h0
    simp only [Pi.add_apply] at this
    rw [hconst] at this
    exact this
  rw [h0', hfun, h2, Finset.sum_apply]
  refine add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_)
  rw [h3 j hj]
  exact mul_le_mul_of_nonneg_left (h4 j hj) (hw j)

private lemma coupling_upd_eq {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (u : ℕ) (ω : Ω)
    (hR : riskSigma S.C (dynDelta S u ω) ≠ 0) :
    dynUpd S u ω = Q (physRidge p S.C (dynDelta S u ω)) (dynBuf S (u + 1) ω) := by
  unfold dynUpd gtRand stepUpdate
  have h1 : errorOf S.alg (runRand S.C S.alg (dynStart S) (dynBatch S) u ω) = dynDelta S u ω := rfl
  rw [h1, if_neg hR]
  have h2 : stepBuffer S.alg (runRand S.C S.alg (dynStart S) (dynBatch S) u ω) (dynBatch S u ω) =
      dynBuf S (u + 1) ω := rfl
  rw [h2, S.alg_ϱ]
  rfl

private lemma coupling_errM_ind {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (A : Set Ω) (t r : ℕ) (ω : Ω) :
    A.indicator (dynErrM p S t r) ω =
      ∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) •
        batchGrad (couplingD S A t j ω) (dynBatch S (t + j) ω) := by
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω]
    have h := coupling_errM_unroll S t ω (r + 1)
    simp only [Nat.add_sub_cancel] at h
    refine Eq.trans h (Finset.sum_congr rfl fun j _ => ?_)
    simp only [couplingD, Set.indicator_of_mem hω]
  · rw [Set.indicator_of_notMem hω]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [couplingD, Set.indicator_of_notMem hω, coupling_grad_zero, smul_zero]

private lemma coupling_rpow_sq {x : ℝ} (hx : 0 < x) : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num
  exact Real.rpow_neg_one x

private lemma coupling_sq_add_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

private lemma coupling_S_path {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (hB : 0 < B)
    (rlo rhi E : ℝ) (hrlo : 0 < rlo) (t r : ℕ) (ω : Ω)
    (h0 : dynDelta S t ω ∈ admSetOf S.C (rlo, rhi, E))
    (hr : dynDelta S (t + r) ω ∈ admSetOf S.C (enl (rlo, rhi, E))) :
    fro (dynErrS p S t r ω) ^ 2 ≤
      2 * (p.CSig * p.h * p.γstar * Real.sqrt (4 * rhi) / rlo * r) ^ 2 +
        2 * (rlo * p.ϱ)⁻¹ * fro (dynErrM p S t r ω) ^ 2 := by
  obtain ⟨hlo0, hhi0, -⟩ := h0
  obtain ⟨hlor, hhir, -⟩ := hr
  simp only [enl] at hlor hhir
  simp only at hlo0 hhi0
  have hR0pos : 0 < riskSigma S.C (dynDelta S t ω) := lt_of_lt_of_le hrlo hlo0
  have hRrpos : 0 < riskSigma S.C (dynDelta S (t + r) ω) := lt_of_lt_of_le (half_pos hrlo) hlor
  have hϱ := p.hϱ
  have hC : 0 ≤ p.CSig := le_trans (by norm_num) p.hC
  have hγ := p.hγ
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hϱo : 0 < rlo * p.ϱ := mul_pos hrlo hϱ
  have hϱ0 : rlo * p.ϱ ≤ physRidge p S.C (dynDelta S t ω) := by
    unfold physRidge; nlinarith
  have hϱr : rlo * p.ϱ ≤ physRidge p S.C (dynDelta S (t + r) ω) := by
    unfold physRidge; nlinarith
  set M := dynBuf S (t + r + 1) ω with hM
  set N := dynHatN p S t r ω with hN
  set ρ0 := physRidge p S.C (dynDelta S t ω) with hρ0
  set ρr := physRidge p S.C (dynDelta S (t + r) ω) with hρr
  have hS : dynUpd S (t + r) ω = Q ρr M := coupling_upd_eq S (t + r) ω hRrpos.ne'
  have hV : dynHatV p S t r ω = Q ρ0 N := rfl
  have hsplit : dynErrS p S t r ω = (Q ρr M - Q ρ0 M) + (Q ρ0 M - Q ρ0 N) := by
    simp only [dynErrS, hS, hV]; abel
  have hMN : dynErrM p S t r ω = M - N := rfl
  -- first bracket
  have hA1 := (lem_app_dyn_schatten_iv hϱo hϱr hϱ0 M).2
  have hmv := (movement_all p S ω t (t + r) (Nat.le_add_right t r)).2.2
  have hrr : ((t + r : ℕ) : ℝ) - t = r := by push_cast; ring
  rw [hrr] at hmv
  set a0 := Real.sqrt (2 * riskSigma S.C (dynDelta S t ω)) with ha0
  set ar := Real.sqrt (2 * riskSigma S.C (dynDelta S (t + r) ω)) with har
  have ha0sq : a0 ^ 2 = 2 * riskSigma S.C (dynDelta S t ω) :=
    Real.sq_sqrt (by linarith)
  have harsq : ar ^ 2 = 2 * riskSigma S.C (dynDelta S (t + r) ω) :=
    Real.sq_sqrt (by linarith)
  have ha0le : a0 ≤ Real.sqrt (4 * rhi) := Real.sqrt_le_sqrt (by linarith)
  have harle : ar ≤ Real.sqrt (4 * rhi) := Real.sqrt_le_sqrt (by linarith)
  have ha0nn : 0 ≤ a0 := Real.sqrt_nonneg _
  have harnn : 0 ≤ ar := Real.sqrt_nonneg _
  set δ := p.CSig * p.h * Real.sqrt p.γstar * (r : ℝ) / Real.sqrt B with hδ
  have hδnn : 0 ≤ δ := by
    have := p.hh
    positivity
  have hRdiff : |riskSigma S.C (dynDelta S (t + r) ω) - riskSigma S.C (dynDelta S t ω)| ≤
      δ * Real.sqrt (4 * rhi) := by
    have h1 : riskSigma S.C (dynDelta S (t + r) ω) - riskSigma S.C (dynDelta S t ω) =
        (ar - a0) * (ar + a0) / 2 := by nlinarith
    rw [h1, abs_div, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ar + a0),
      abs_two]
    have h2 : |ar - a0| ≤ δ := hmv
    have h3 : (ar + a0) / 2 ≤ Real.sqrt (4 * rhi) := by linarith
    calc |ar - a0| * (ar + a0) / 2 = |ar - a0| * ((ar + a0) / 2) := by ring
      _ ≤ δ * Real.sqrt (4 * rhi) :=
          mul_le_mul h2 h3 (by linarith) hδnn
  have hρdiff : |ρr - ρ0| = 2 * p.ϱ * |riskSigma S.C (dynDelta S (t + r) ω) -
      riskSigma S.C (dynDelta S t ω)| := by
    have : ρr - ρ0 = 2 * p.ϱ * (riskSigma S.C (dynDelta S (t + r) ω) -
        riskSigma S.C (dynDelta S t ω)) := by
      simp only [hρr, hρ0, physRidge]; ring
    rw [this, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * p.ϱ)]
  have hmin : Real.sqrt ((min m n : ℕ) : ℝ) ≤ Real.sqrt (p.γstar * B) := by
    apply Real.sqrt_le_sqrt
    have hm : ((min m n : ℕ) : ℝ) ≤ ((max m n : ℕ) : ℝ) := by
      exact_mod_cast (min_le_max : min m n ≤ max m n)
    exact hm.trans S.size.1
  have hκ : Real.sqrt (p.γstar * B) * (|ρr - ρ0| / (2 * (rlo * p.ϱ))) ≤
      p.CSig * p.h * p.γstar * Real.sqrt (4 * rhi) / rlo * r := by
    rw [hρdiff]
    have hsB : Real.sqrt (p.γstar * B) = Real.sqrt p.γstar * Real.sqrt B := Real.sqrt_mul hγ _
    have hspos : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBpos
    have hsq := Real.sq_sqrt hγ
    calc Real.sqrt (p.γstar * B) * (2 * p.ϱ * |riskSigma S.C (dynDelta S (t + r) ω) -
            riskSigma S.C (dynDelta S t ω)| / (2 * (rlo * p.ϱ)))
        ≤ Real.sqrt (p.γstar * B) * (2 * p.ϱ * (δ * Real.sqrt (4 * rhi)) / (2 * (rlo * p.ϱ))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hRdiff (by positivity)
      _ = p.CSig * p.h * p.γstar * Real.sqrt (4 * rhi) / rlo * r := by
          rw [hsB, hδ]
          field_simp
          rw [hsq]
          ring
  have hA1' : fro (Q ρr M - Q ρ0 M) ≤ p.CSig * p.h * p.γstar * Real.sqrt (4 * rhi) / rlo * r :=
    hA1.trans ((mul_le_mul_of_nonneg_right hmin (by positivity)).trans hκ)
  -- second bracket
  have hρ0pos : 0 < ρ0 := lt_of_lt_of_le hϱo hϱ0
  have hA2 := lem_app_setup_filter_iii ρ0 hρ0pos M N
  have hA2' : fro (Q ρ0 M - Q ρ0 N) ≤ (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * fro (dynErrM p S t r ω) := by
    rw [hMN]
    refine hA2.trans (mul_le_mul_of_nonneg_right ?_ (movement_fro_nn _))
    exact Real.rpow_le_rpow_of_nonpos hϱo hϱ0 (by norm_num)
  -- combine
  have hsub : fro (dynErrS p S t r ω) ≤ fro (Q ρr M - Q ρ0 M) + fro (Q ρ0 M - Q ρ0 N) := by
    rw [hsplit]; exact coupling_fro_props.2.1 _ _
  have hnn := movement_fro_nn (dynErrS p S t r ω)
  have htot : fro (dynErrS p S t r ω) ≤
      p.CSig * p.h * p.γstar * Real.sqrt (4 * rhi) / rlo * r +
        (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * fro (dynErrM p S t r ω) :=
    hsub.trans (add_le_add hA1' hA2')
  have hsq2 := (pow_le_pow_left₀ hnn htot 2).trans (coupling_sq_add_le _ _)
  refine hsq2.trans (le_of_eq ?_)
  have hr2 := coupling_rpow_sq hϱo
  generalize (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) = q at hr2 ⊢
  generalize fro (dynErrM p S t r ω) = f
  rw [mul_pow (a := q), hr2]
  ring

private lemma coupling_wsum_r (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (r : ℕ) :
    ∑ j ∈ Finset.range (r + 1), emaW β (r - j) ≤ 1 := by
  have := coupling_wsum_le_one β hβ0 hβ1 (r + 1)
  simpa using this

private lemma coupling_Z_fro_bound {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (A : Set Ω) (t r : ℕ) (ω : Ω) :
    A.indicator (fun ω => fro (dynErrM p S t r ω) ^ 2) ω ≤
      ∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) *
        fro (batchGrad (couplingD S A t j ω) (dynBatch S (t + j) ω)) ^ 2 := by
  rw [← buffer_indicator_fro_sq, coupling_errM_ind]
  obtain ⟨h1, h2, h3, h4⟩ := coupling_fro_props (m := m) (n := n)
  exact coupling_norm_sum_sq fro h1 h2 h3 h4 (r + 1) (fun j => emaW p.β (r - j))
    (fun j => coupling_emaW_nonneg p.hβ.1 p.hβ.2 _) (coupling_wsum_r p.β p.hβ.1 p.hβ.2 r) _

private lemma coupling_Z_op_bound {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (A : Set Ω) (t r : ℕ) (ω : Ω) :
    A.indicator (fun ω => opNorm (dynErrM p S t r ω) ^ 2) ω ≤
      ∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) *
        opNorm (batchGrad (couplingD S A t j ω) (dynBatch S (t + j) ω)) ^ 2 := by
  rw [← buffer_indicator_op_sq, coupling_errM_ind]
  obtain ⟨h1, h2, h3, h4⟩ := coupling_op_props (m := m) (n := n)
  exact coupling_norm_sum_sq opNorm h1 h2 h3 h4 (r + 1) (fun j => emaW p.β (r - j))
    (fun j => coupling_emaW_nonneg p.hβ.1 p.hβ.2 _) (coupling_wsum_r p.β p.hβ.1 p.hβ.2 r) _

private lemma coupling_Y_fro {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (hB : 0 < B)
    {A : Set Ω} {t : ℕ} (hA : MeasurableSet[dynPast S t] A) (j : ℕ) :
    Integrable (fun ω => fro (batchGrad (couplingD S A t j ω) (dynBatch S (t + j) ω)) ^ 2) P ∧
    ∀ᵐ ω ∂P, condExp (dynPast S t) P
      (fun ω' => fro (batchGrad (couplingD S A t j ω') (dynBatch S (t + j) ω')) ^ 2) ω ≤
        cMConst p.CSig p.γstar * (p.CSig ^ 2 * p.h ^ 2 * p.γstar) * (j : ℝ) ^ 2 := by
  have h := coupling_grad_cond_fro S hB (Nat.le_add_right t j) (couplingD S A t j)
    (coupling_D_meas S hA j) _ (coupling_D_bound S hB A t j)
  refine ⟨h.1, ?_⟩
  filter_upwards [h.2] with ω hω
  refine hω.trans (le_of_eq ?_)
  have : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  field_simp

private lemma coupling_i_aux (certOp : Muon.External.GaussianOpNormL6) (p : DynParams)
    (rlo rhi E : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ B0 : ℕ, ∃ K : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B), B0 ≤ B → ∀ t r : ℕ, r ≤ 4 * blockLen B →
      (Integrable ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => fro (dynErrM p S t r ω) ^ 2 + fro (dynErrS p S t r ω) ^ 2)) P ∧
        ∀ᵐ ω ∂P, ω ∈ dynInK S t (rlo, rhi, E) →
          condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
            (fun ω => fro (dynErrM p S t r ω) ^ 2 + fro (dynErrS p S t r ω) ^ 2)) ω ≤ K * (r : ℝ) ^ 2) ∧
      (Integrable ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => opNorm (dynErrM p S t r ω) ^ 2)) P ∧
        ∀ᵐ ω ∂P, ω ∈ dynInK S t (rlo, rhi, E) →
          condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
            (fun ω => opNorm (dynErrM p S t r ω) ^ 2)) ω ≤
            K * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B) := by
  obtain ⟨B0m, hB0m⟩ := lem_app_dyn_movement_ii p rlo rhi E hrlo hle
  obtain ⟨Kb, hKb0, hKb⟩ := coupling_grad_cond_op certOp p
  set κ : ℝ := cMConst p.CSig p.γstar * (p.CSig ^ 2 * p.h ^ 2 * p.γstar) with hκ
  set κo : ℝ := Kb ^ 2 * (p.CSig ^ 2 * p.h ^ 2 * p.γstar) with hκo
  set c1 : ℝ := p.CSig * p.h * p.γstar * Real.sqrt (4 * rhi) / rlo with hc1
  set μ : ℝ := 2 * (rlo * p.ϱ)⁻¹ with hμ
  have hκ0 : 0 ≤ κ := by
    have := p.hγ
    rw [hκ]
    unfold cMConst
    positivity
  have hκo0 : 0 ≤ κo := by
    have := p.hγ
    rw [hκo]
    positivity
  have hμ0 : 0 ≤ μ := by
    have := p.hϱ
    rw [hμ]
    positivity
  refine ⟨max B0m 1, max (2 * c1 ^ 2 + (1 + μ) * κ) κo, ?_⟩
  intro Ω _ P _ m n B S hB t r hr
  have hB1 : 0 < B := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hB)
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB1
  have hmov := hB0m Ω P m n B S ((le_max_left _ _).trans hB)
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) :=
    Real.log_nonneg (by
      have hB1' : (1 : ℝ) ≤ B := by exact_mod_cast hB1
      nlinarith)
  set A := dynInK S t (rlo, rhi, E) with hAdef
  have hA : MeasurableSet[dynPast S t] A := coupling_A_meas S t _
  have hAm : MeasurableSet A := buffer_past_le S t _ hA
  have hw0 : ∀ j, 0 ≤ emaW p.β (r - j) := fun j => coupling_emaW_nonneg p.hβ.1 p.hβ.2 _
  have hwsum := coupling_wsum_r p.β p.hβ.1 p.hβ.2 r
  have hj2 : ∀ j ∈ Finset.range (r + 1), (j : ℝ) ^ 2 ≤ (r : ℝ) ^ 2 := by
    intro j hj
    have : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast this) 2
  constructor
  · -- Frobenius display
    have hXmeas : Measurable (A.indicator (fun ω => fro (dynErrM p S t r ω) ^ 2 +
        fro (dynErrS p S t r ω) ^ 2)) :=
      ((buffer_fro_sq_meas.comp (coupling_errM_meas S t r)).add
        (buffer_fro_sq_meas.comp (coupling_errS_meas S hB1 t r))).indicator hAm
    have hX0 : ∀ ω, 0 ≤ A.indicator (fun ω => fro (dynErrM p S t r ω) ^ 2 +
        fro (dynErrS p S t r ω) ^ 2) ω :=
      fun ω => Set.indicator_nonneg (fun _ _ => by positivity) ω
    have hXle : ∀ ω, A.indicator (fun ω => fro (dynErrM p S t r ω) ^ 2 +
        fro (dynErrS p S t r ω) ^ 2) ω ≤ 2 * c1 ^ 2 * (r : ℝ) ^ 2 +
        ∑ j ∈ Finset.range (r + 1), ((1 + μ) * emaW p.β (r - j)) *
          fro (batchGrad (couplingD S A t j ω) (dynBatch S (t + j) ω)) ^ 2 := by
      intro ω
      have hnn : 0 ≤ ∑ j ∈ Finset.range (r + 1), ((1 + μ) * emaW p.β (r - j)) *
          fro (batchGrad (couplingD S A t j ω) (dynBatch S (t + j) ω)) ^ 2 :=
        Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (by linarith) (hw0 j)) (sq_nonneg _)
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]
        have h0 : dynDelta S t ω ∈ admSetOf S.C (rlo, rhi, E) := hω
        have hr' : dynDelta S (t + r) ω ∈ admSetOf S.C (enl (rlo, rhi, E)) := by
          refine (hmov ω t h0).2 (t + r) ?_
          have : |((t + r : ℕ) : ℤ) - (t : ℤ)| = r := by
            push_cast
            simp
          rw [this]
          exact_mod_cast hr
        have hS := coupling_S_path S hB1 rlo rhi E hrlo t r ω h0 hr'
        have hZ := coupling_Z_fro_bound S A t r ω
        rw [Set.indicator_of_mem hω] at hZ
        have hmul : ∑ j ∈ Finset.range (r + 1), ((1 + μ) * emaW p.β (r - j)) *
            fro (batchGrad (couplingD S A t j ω) (dynBatch S (t + j) ω)) ^ 2 =
            (1 + μ) * ∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) *
            fro (batchGrad (couplingD S A t j ω) (dynBatch S (t + j) ω)) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [hmul]
        have h1 := mul_le_mul_of_nonneg_left hZ (show (0 : ℝ) ≤ 1 + μ by linarith)
        have h2 : 2 * (c1 * r) ^ 2 = 2 * c1 ^ 2 * (r : ℝ) ^ 2 := by ring
        have h3 : 2 * (rlo * p.ϱ)⁻¹ * fro (dynErrM p S t r ω) ^ 2 = μ * fro (dynErrM p S t r ω) ^ 2 := by
          rw [hμ]
        nlinarith [hS, h1, h2, h3]
      · rw [Set.indicator_of_notMem hω]
        have : (0 : ℝ) ≤ 2 * c1 ^ 2 * (r : ℝ) ^ 2 := by positivity
        linarith
    obtain ⟨hint, hcond⟩ := coupling_cond_sum (dynPast S t) (buffer_past_le S t) (r + 1)
      (2 * c1 ^ 2 * (r : ℝ) ^ 2) (fun j => (1 + μ) * emaW p.β (r - j))
      (fun j => mul_nonneg (by linarith) (hw0 j))
      (fun j ω => fro (batchGrad (couplingD S A t j ω) (dynBatch S (t + j) ω)) ^ 2)
      (fun j => (coupling_Y_fro S hB1 hA j).1) (fun j => κ * (j : ℝ) ^ 2)
      (fun j => (coupling_Y_fro S hB1 hA j).2) _ hXmeas.aestronglyMeasurable hX0 hXle
    refine ⟨hint, ?_⟩
    filter_upwards [hcond] with ω hω _
    refine hω.trans ?_
    have hs : ∑ j ∈ Finset.range (r + 1), (1 + μ) * emaW p.β (r - j) * (κ * (j : ℝ) ^ 2) ≤
        (1 + μ) * κ * (r : ℝ) ^ 2 := by
      calc ∑ j ∈ Finset.range (r + 1), (1 + μ) * emaW p.β (r - j) * (κ * (j : ℝ) ^ 2)
          ≤ ∑ j ∈ Finset.range (r + 1), (1 + μ) * κ * (r : ℝ) ^ 2 * emaW p.β (r - j) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have := mul_le_mul_of_nonneg_left (hj2 j hj)
              (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + μ) hκ0) (hw0 j))
            nlinarith [this]
        _ = (1 + μ) * κ * (r : ℝ) ^ 2 * ∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) := by
            rw [Finset.mul_sum]
        _ ≤ (1 + μ) * κ * (r : ℝ) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hwsum (by positivity)
        _ = _ := by ring
    have hK : 2 * c1 ^ 2 + (1 + μ) * κ ≤ max (2 * c1 ^ 2 + (1 + μ) * κ) κo := le_max_left _ _
    have hr2 : 0 ≤ (r : ℝ) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hK hr2]
  · -- operator display
    have hXmeas : Measurable (A.indicator (fun ω => opNorm (dynErrM p S t r ω) ^ 2)) :=
      ((buffer_opNorm_continuous.measurable.comp (coupling_errM_meas S t r)).pow_const 2).indicator hAm
    have hX0 : ∀ ω, 0 ≤ A.indicator (fun ω => opNorm (dynErrM p S t r ω) ^ 2) ω :=
      fun ω => Set.indicator_nonneg (fun _ _ => by positivity) ω
    have hXle : ∀ ω, A.indicator (fun ω => opNorm (dynErrM p S t r ω) ^ 2) ω ≤ 0 +
        ∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) *
          opNorm (batchGrad (couplingD S A t j ω) (dynBatch S (t + j) ω)) ^ 2 := by
      intro ω
      rw [zero_add]
      exact coupling_Z_op_bound S A t r ω
    have hY : ∀ j, Integrable (fun ω => opNorm (batchGrad (couplingD S A t j ω)
          (dynBatch S (t + j) ω)) ^ 2) P ∧
        ∀ᵐ ω ∂P, condExp (dynPast S t) P (fun ω' => opNorm (batchGrad (couplingD S A t j ω')
          (dynBatch S (t + j) ω')) ^ 2) ω ≤
          κo * (j : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B := by
      intro j
      have hc0 : 0 ≤ p.CSig ^ 2 * p.h ^ 2 * p.γstar * (j : ℝ) ^ 2 / B := by
        have := p.hγ
        positivity
      have h := hKb Ω P m n B S hB1 t (t + j) (Nat.le_add_right t j) (couplingD S A t j)
        (coupling_D_meas S hA j) _ hc0 (coupling_D_bound S hB1 A t j)
      refine ⟨h.1, ?_⟩
      filter_upwards [h.2] with ω hω
      refine hω.trans (le_of_eq ?_)
      rw [hκo]
      ring
    obtain ⟨hint, hcond⟩ := coupling_cond_sum (dynPast S t) (buffer_past_le S t) (r + 1)
      0 (fun j => emaW p.β (r - j)) hw0
      (fun j ω => opNorm (batchGrad (couplingD S A t j ω) (dynBatch S (t + j) ω)) ^ 2)
      (fun j => (hY j).1) (fun j => κo * (j : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B)
      (fun j => (hY j).2) _ hXmeas.aestronglyMeasurable hX0 hXle
    refine ⟨hint, ?_⟩
    filter_upwards [hcond] with ω hω _
    refine hω.trans ?_
    have hs : 0 + ∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) *
        (κo * (j : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B) ≤
        κo * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B := by
      have hq : 0 ≤ Real.log (2 * (B : ℝ)) ^ 2 / B := by positivity
      calc 0 + ∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) *
            (κo * (j : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B)
          ≤ ∑ j ∈ Finset.range (r + 1), (κo * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B) *
              emaW p.β (r - j) := by
            rw [zero_add]
            refine Finset.sum_le_sum fun j hj => ?_
            have h1 := mul_le_mul_of_nonneg_left (hj2 j hj) (mul_nonneg hκo0 hq)
            have h2 := mul_le_mul_of_nonneg_right h1 (hw0 j)
            have e1 : κo * (j : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B =
                κo * ((j : ℝ) ^ 2) * (Real.log (2 * (B : ℝ)) ^ 2 / B) := by ring
            have e2 : κo * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B =
                κo * ((r : ℝ) ^ 2) * (Real.log (2 * (B : ℝ)) ^ 2 / B) := by ring
            rw [e1, e2]
            nlinarith [h2]
        _ = (κo * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B) *
              ∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) := by rw [Finset.mul_sum]
        _ ≤ (κo * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B) * 1 :=
            mul_le_mul_of_nonneg_left hwsum (by positivity)
        _ = _ := by ring
    refine hs.trans ?_
    have hK : κo ≤ max (2 * c1 ^ 2 + (1 + μ) * κ) κo := le_max_right _ _
    have hq : 0 ≤ (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B := by positivity
    have := mul_le_mul_of_nonneg_right hK hq
    calc κo * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B
        = κo * ((r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B) := by ring
      _ ≤ _ := this.trans (le_of_eq (by ring))

private lemma coupling_sq_add_le' (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

private lemma coupling_fro_sub_le {m n : ℕ} (x y : Mat m n) : fro (x - y) ≤ fro x + fro y := by
  open scoped Matrix.Norms.Frobenius in
  simpa only [fro_eq_norm] using norm_sub_le x y

private lemma coupling_op_sub_le {m n : ℕ} (x y : Mat m n) :
    opNorm (x - y) ≤ opNorm x + opNorm y := by
  open scoped Matrix.Norms.L2Operator in
  simpa only [opNorm_eq_norm] using norm_sub_le x y

/-- Pathwise structure of the frozen-update error. -/
private lemma coupling_V_eq {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t r : ℕ) (ω : Ω) :
    dynErrV p S t r ω =
      Q (physRidge p S.C (dynDelta S t ω)) (dynHatN p S t r ω) -
        Q (physRidge p S.C (dynDelta S t ω))
          (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
            (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1)) := rfl

private lemma coupling_V_diff {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t r : ℕ) (ω : Ω) :
    dynHatN p S t r ω -
        emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
          (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1) =
      (p.β ^ (r + 1)) • (dynBuf S t ω - chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) :=
  lem_app_dyn_chains_ii p S.C S.cs t (dynDelta S t ω) (dynBuf S t ω) ω (r + 1)

private lemma coupling_V_fro_path {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (rlo : ℝ) (hrlo : 0 < rlo)
    (t r : ℕ) (ω : Ω) (h0 : rlo ≤ riskSigma S.C (dynDelta S t ω)) :
    fro (dynErrV p S t r ω) ^ 2 ≤
      2 * (rlo * p.ϱ)⁻¹ * p.β ^ (2 * (r + 1)) *
        (fro (dynBuf S t ω) ^ 2 +
          fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2) := by
  have hϱ := p.hϱ
  have hϱo : 0 < rlo * p.ϱ := mul_pos hrlo hϱ
  have hϱ0 : rlo * p.ϱ ≤ physRidge p S.C (dynDelta S t ω) := by
    unfold physRidge; nlinarith
  have hρpos : 0 < physRidge p S.C (dynDelta S t ω) := lt_of_lt_of_le hϱo hϱ0
  rw [coupling_V_eq]
  have h1 := lem_app_setup_filter_iii _ hρpos (dynHatN p S t r ω)
    (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
      (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1))
  rw [coupling_V_diff] at h1
  have hsm := (coupling_fro_props (m := m) (n := n)).1 (p.β ^ (r + 1))
    (dynBuf S t ω - chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)
    (pow_nonneg p.hβ.1 _)
  rw [hsm] at h1
  have h2 := coupling_fro_sub_le (dynBuf S t ω)
    (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)
  have hq : (physRidge p S.C (dynDelta S t ω)) ^ (-(1 / 2 : ℝ)) ≤ (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hϱo hϱ0 (by norm_num)
  have hq0 : 0 ≤ (physRidge p S.C (dynDelta S t ω)) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg hρpos.le _
  have hb0 := pow_nonneg p.hβ.1 (r + 1)
  have hnn := movement_fro_nn (dynErrV p S t r ω)
  have hbound : fro (Q (physRidge p S.C (dynDelta S t ω)) (dynHatN p S t r ω) -
      Q (physRidge p S.C (dynDelta S t ω))
        (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
          (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1))) ≤
      (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * p.β ^ (r + 1) *
      (fro (dynBuf S t ω) + fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) := by
    refine h1.trans ?_
    have hf0 := movement_fro_nn (dynBuf S t ω - chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)
    calc _ ≤ (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * (p.β ^ (r + 1) * fro (dynBuf S t ω -
          chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) :=
          mul_le_mul_of_nonneg_right hq (mul_nonneg hb0 hf0)
      _ ≤ (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * (p.β ^ (r + 1) * (fro (dynBuf S t ω) +
          fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hb0) (Real.rpow_nonneg hϱo.le _)
      _ = _ := by ring
  have hnn := movement_fro_nn (Q (physRidge p S.C (dynDelta S t ω)) (dynHatN p S t r ω) -
      Q (physRidge p S.C (dynDelta S t ω))
        (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
          (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1)))
  have hsq3 := pow_le_pow_left₀ hnn hbound 2
  have hsq4 : ((rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * p.β ^ (r + 1) *
      (fro (dynBuf S t ω) +
        fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω))) ^ 2 ≤
      ((rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * p.β ^ (r + 1)) ^ 2 * (2 * (fro (dynBuf S t ω) ^ 2 +
        fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2)) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (coupling_sq_add_le' _ _) (sq_nonneg _)
  have hsq := hsq3.trans hsq4
  refine hsq.trans (le_of_eq ?_)
  have hr2 := coupling_rpow_sq hϱo
  generalize (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) = q at hr2 ⊢
  have hb2 : p.β ^ (2 * (r + 1)) = (p.β ^ (r + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
  rw [hb2]
  rw [mul_pow, hr2]
  ring

private lemma coupling_V_op_path {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (rlo : ℝ) (hrlo : 0 < rlo)
    (t r : ℕ) (ω : Ω) (h0 : rlo ≤ riskSigma S.C (dynDelta S t ω)) :
    opNorm (dynErrV p S t r ω) ^ 2 ≤
      2 * (rlo * p.ϱ)⁻¹ * p.β ^ (2 * (r + 1)) *
        (opNorm (dynBuf S t ω) ^ 2 +
          opNorm (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2) := by
  have hϱ := p.hϱ
  have hϱo : 0 < rlo * p.ϱ := mul_pos hrlo hϱ
  have hϱ0 : rlo * p.ϱ ≤ physRidge p S.C (dynDelta S t ω) := by
    unfold physRidge; nlinarith
  have hρpos : 0 < physRidge p S.C (dynDelta S t ω) := lt_of_lt_of_le hϱo hϱ0
  rw [coupling_V_eq]
  have h1 : opNorm (Q (physRidge p S.C (dynDelta S t ω)) (dynHatN p S t r ω) -
      Q (physRidge p S.C (dynDelta S t ω)) (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
      (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1))) ≤ (physRidge p S.C (dynDelta S t ω)) ^ (-(1 / 2 : ℝ)) * opNorm (dynHatN p S t r ω - (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
      (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1))) := by
    have := lem_app_dyn_schatten_ii (p := ⊤) (Or.inr rfl) hρpos (dynHatN p S t r ω)
      (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
        (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1))
    simpa [schatNorm] using this
  rw [coupling_V_diff] at h1
  have hsm := (coupling_op_props (m := m) (n := n)).1 (p.β ^ (r + 1))
    (dynBuf S t ω - chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)
    (pow_nonneg p.hβ.1 _)
  rw [hsm] at h1
  have h2 := coupling_op_sub_le (dynBuf S t ω)
    (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)
  have hq : (physRidge p S.C (dynDelta S t ω)) ^ (-(1 / 2 : ℝ)) ≤ (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hϱo hϱ0 (by norm_num)
  have hq0 : 0 ≤ (physRidge p S.C (dynDelta S t ω)) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg hρpos.le _
  have hb0 := pow_nonneg p.hβ.1 (r + 1)
  have hnn := movement_opNorm_nonneg (dynErrV p S t r ω)
  have hbound : opNorm (Q (physRidge p S.C (dynDelta S t ω)) (dynHatN p S t r ω) -
      Q (physRidge p S.C (dynDelta S t ω))
        (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
          (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1))) ≤
      (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * p.β ^ (r + 1) *
      (opNorm (dynBuf S t ω) + opNorm (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) := by
    refine h1.trans ?_
    have hf0 := movement_opNorm_nonneg (dynBuf S t ω - chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)
    calc _ ≤ (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * (p.β ^ (r + 1) * opNorm (dynBuf S t ω -
          chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) :=
          mul_le_mul_of_nonneg_right hq (mul_nonneg hb0 hf0)
      _ ≤ (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * (p.β ^ (r + 1) * (opNorm (dynBuf S t ω) +
          opNorm (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hb0) (Real.rpow_nonneg hϱo.le _)
      _ = _ := by ring
  have hnn := movement_opNorm_nonneg (Q (physRidge p S.C (dynDelta S t ω)) (dynHatN p S t r ω) -
      Q (physRidge p S.C (dynDelta S t ω))
        (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
          (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1)))
  have hsq3 := pow_le_pow_left₀ hnn hbound 2
  have hsq4 : ((rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * p.β ^ (r + 1) *
      (opNorm (dynBuf S t ω) +
        opNorm (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω))) ^ 2 ≤
      ((rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * p.β ^ (r + 1)) ^ 2 * (2 * (opNorm (dynBuf S t ω) ^ 2 +
        opNorm (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2)) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (coupling_sq_add_le' _ _) (sq_nonneg _)
  have hsq := hsq3.trans hsq4
  refine hsq.trans (le_of_eq ?_)
  have hr2 := coupling_rpow_sq hϱo
  generalize (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) = q at hr2 ⊢
  have hb2 : p.β ^ (2 * (r + 1)) = (p.β ^ (r + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
  rw [hb2]
  rw [mul_pow, hr2]
  ring

private lemma coupling_ridge_nonneg {p : DynParams} {m n : ℕ} (C : Covariances m n)
    (D : Mat m n) : 0 ≤ physRidge p C D := by
  unfold physRidge
  exact mul_nonneg (mul_nonneg (by norm_num)
    (by rw [eqn_app_setup_whitened_risk]; positivity)) p.hϱ.le

private lemma coupling_Q_fro_sq {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (ρ : ℝ) (hρ : 0 ≤ ρ) (K : Mat m n) :
    fro (Q ρ K) ^ 2 ≤ p.γstar * B := by
  obtain ⟨_, hf, hk, _⟩ := lem_app_setup_filter_i ρ hρ K
  have hmin : ((min m n : ℕ) : ℝ) ≤ p.γstar * B := by
    have hm : ((min m n : ℕ) : ℝ) ≤ ((max m n : ℕ) : ℝ) := by
      exact_mod_cast (min_le_max : min m n ≤ max m n)
    exact hm.trans S.size.1
  have hk' : (K.rank : ℝ) ≤ ((min m n : ℕ) : ℝ) := by exact_mod_cast hk
  exact hf.trans (hk'.trans hmin)

private lemma coupling_V_fro_bdd {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t r : ℕ) (ω : Ω) :
    fro (dynErrV p S t r ω) ^ 2 ≤ 4 * (p.γstar * B) := by
  have h1 := coupling_Q_fro_sq S _ (coupling_ridge_nonneg (p := p) S.C (dynDelta S t ω))
    (dynHatN p S t r ω)
  have h2 := coupling_Q_fro_sq S _ (coupling_ridge_nonneg (p := p) S.C (dynDelta S t ω))
    (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
      (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1))
  rw [coupling_V_eq]
  have h3 := coupling_fro_sub_le
    (Q (physRidge p S.C (dynDelta S t ω)) (dynHatN p S t r ω))
    (Q (physRidge p S.C (dynDelta S t ω))
      (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
        (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1)))
  have h4 := pow_le_pow_left₀ (movement_fro_nn _) h3 2
  have h5 := coupling_sq_add_le' (fro (Q (physRidge p S.C (dynDelta S t ω)) (dynHatN p S t r ω)))
    (fro (Q (physRidge p S.C (dynDelta S t ω))
      (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
        (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1))))
  linarith

private lemma coupling_V_op_bdd {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t r : ℕ) (ω : Ω) :
    opNorm (dynErrV p S t r ω) ^ 2 ≤ 4 := by
  have hρ := coupling_ridge_nonneg (p := p) S.C (dynDelta S t ω)
  have h1 := (lem_app_setup_filter_i _ hρ (dynHatN p S t r ω)).1
  have h2 := (lem_app_setup_filter_i _ hρ
    (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
      (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1))).1
  rw [coupling_V_eq]
  have h3 := coupling_op_sub_le
    (Q (physRidge p S.C (dynDelta S t ω)) (dynHatN p S t r ω))
    (Q (physRidge p S.C (dynDelta S t ω))
      (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
        (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1)))
  have h4 : opNorm (Q (physRidge p S.C (dynDelta S t ω)) (dynHatN p S t r ω) -
      Q (physRidge p S.C (dynDelta S t ω))
        (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
          (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1))) ≤ 2 := by linarith
  have h5 := pow_le_pow_left₀ (movement_opNorm_nonneg _) h4 2
  linarith

/-- Private copy of `pd_freeze_bound` (Chains.lean). -/
private lemma coupling_freeze_bound {Ω α β : Type*} (𝓕 : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] [MeasurableSpace α] [MeasurableSpace β]
    (h𝓕 : 𝓕 ≤ mΩ) {X : Ω → α} {Y : Ω → β}
    (hX : Measurable[𝓕] X) (hY : Measurable Y)
    (hind : Indep 𝓕 (MeasurableSpace.comap Y inferInstance) P)
    {f : α → β → ℝ} (hf : Measurable (Function.uncurry f)) (hf0 : ∀ x y, 0 ≤ f x y)
    {g : α → ℝ} (hgint : Integrable (fun ω => g (X ω)) P)
    (hfx : ∀ x, Integrable (f x) (P.map Y))
    (hbound : ∀ x, ∫ y, f x y ∂(P.map Y) ≤ g x) :
    Integrable (fun ω => f (X ω) (Y ω)) P ∧
      ∀ᵐ ω ∂P, 0 ≤ condExp 𝓕 P (fun ω' => f (X ω') (Y ω')) ω ∧
        condExp 𝓕 P (fun ω' => f (X ω') (Y ω')) ω ≤ g (X ω) := by
  have hXm : Measurable X := hX.mono h𝓕 le_rfl
  have hint : Integrable (fun ω => f (X ω) (Y ω)) P := by
    have hindf : IndepFun X Y P := by
      refine indep_of_indep_of_le_left hind ?_
      exact hX.comap_le
    have hmap := (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hY.aemeasurable).1 hindf
    have hpair : Measurable (fun ω => (X ω, Y ω)) := hXm.prodMk hY
    show Integrable ((Function.uncurry f) ∘ (fun ω => (X ω, Y ω))) P
    rw [← integrable_map_measure hf.aestronglyMeasurable hpair.aemeasurable, hmap]
    rw [integrable_prod_iff hf.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x => hfx x, ?_⟩
    have hm : Measurable (fun x => ∫ y, ‖Function.uncurry f (x, y)‖ ∂(P.map Y)) :=
      (hf.norm.stronglyMeasurable.integral_prod_right' (ν := P.map Y)).measurable
    refine (integrable_map_measure hm.aestronglyMeasurable hXm.aemeasurable).2 ?_
    refine hgint.mono' (hm.comp hXm).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    have : ∫ y, |Function.uncurry f (X ω, y)| ∂(P.map Y) = ∫ y, f (X ω) y ∂(P.map Y) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by
        simp [Function.uncurry, abs_of_nonneg (hf0 _ y)])
    simp only [Function.comp, Real.norm_eq_abs]
    rw [this, abs_of_nonneg (integral_nonneg fun y => hf0 _ y)]
    exact hbound _
  refine ⟨hint, ?_⟩
  have hc := Muon.Foundations.freezing_condExp 𝓕 h𝓕 hX hY hind hf hint
  filter_upwards [hc] with ω hω
  rw [hω]
  exact ⟨integral_nonneg fun y => hf0 _ y, hbound _⟩

private lemma coupling_N0_cond {p : DynParams} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ)
    (Aset : Set (Mat m n)) (hAset : MeasurableSet Aset)
    (ψ : Mat m n → ℝ) (hψ : Measurable ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (c : ℝ) (hc : 0 ≤ c)
    (hfix : ∀ x ∈ Aset, Integrable (fun ω => ψ (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω)) P ∧
        ∫ ω, ψ (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω) ∂P ≤ c) :
    Integrable (fun ω => Aset.indicator (fun _ => (1 : ℝ)) (dynDelta S t ω) *
        ψ (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) P ∧
    ∀ᵐ ω ∂P, condExp (dynPast S t) P (fun ω' => Aset.indicator (fun _ => (1 : ℝ)) (dynDelta S t ω') *
        ψ (chainInit p.β S.C (dynDelta S t ω') (S.cs.aux (t : ℤ)) ω')) ω ≤ c := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) :=
    inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  let Y : Ω → (ℕ → Fin B → Vec m × Vec n) := fun ω j a => S.cs.aux (t : ℤ) j a ω
  have hY : Measurable Y :=
    Measurable.of_eval fun j => Measurable.of_eval fun a => S.cs.meas_aux _ j a
  have hYcf : Measurable[chainFuture S.cs t] Y := by
    refine buffer_pi_meas (σ := chainFuture S.cs t) (fun j => ?_)
    refine buffer_pi_meas (σ := chainFuture S.cs t) (fun a => ?_)
    exact Measurable.of_comap_le (le_sup_of_le_right (le_iSup_of_le j (le_iSup_of_le a le_rfl)))
  have hind : Indep (dynPast S t) (MeasurableSpace.comap Y inferInstance) P :=
    indep_of_indep_of_le_right (buffer_indep_past_future S t) hYcf.comap_le
  let f : Mat m n → (ℕ → Fin B → Vec m × Vec n) → ℝ := fun x y =>
    Aset.indicator (fun _ => (1 : ℝ)) x *
      ψ (∑' j : ℕ, emaW p.β j • grad x (fun a => phys S.C (y j a)))
  have hf : Measurable (Function.uncurry f) := by
    have hinit : Measurable (fun z : Mat m n × (ℕ → Fin B → Vec m × Vec n) =>
        ∑' j : ℕ, emaW p.β j • grad z.1 (fun a => phys S.C (z.2 j a))) := by
      refine Measurable.tsum fun j => Measurable.const_smul ?_ (emaW p.β j)
      unfold grad resid phys outer
      fun_prop
    exact (((measurable_const.indicator hAset).comp measurable_fst).mul (hψ.comp hinit))
  have hf0 : ∀ x y, 0 ≤ f x y := fun x y =>
    mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) x) (hψ0 _)
  let g : Mat m n → ℝ := Aset.indicator (fun _ => c)
  have hgint : Integrable (fun ω => g (dynDelta S t ω)) P := by
    refine Integrable.of_bound (((measurable_const.indicator hAset).comp
      (coupling_delta_meas S t)).aestronglyMeasurable) c (ae_of_all _ fun ω => ?_)
    by_cases h : dynDelta S t ω ∈ Aset
    · simp [g, Set.indicator_of_mem h, abs_of_nonneg hc]
    · simp [g, Set.indicator_of_notMem h, hc]
  have hfm : ∀ x, Measurable (f x) := fun x => hf.comp (measurable_const.prodMk measurable_id)
  have hfx : ∀ x, Integrable (f x) (P.map Y) := by
    intro x
    by_cases hx : x ∈ Aset
    · rw [integrable_map_measure (hfm x).aestronglyMeasurable hY.aemeasurable]
      have := (hfix x hx).1
      refine this.congr (ae_of_all _ fun ω => ?_)
      simp only [Function.comp, f, Set.indicator_of_mem hx, one_mul]
      rfl
    · have : f x = fun _ => 0 := by
        funext y
        simp [f, Set.indicator_of_notMem hx]
      rw [this]
      exact integrable_zero _ _ _
  have hbound : ∀ x, ∫ y, f x y ∂(P.map Y) ≤ g x := by
    intro x
    by_cases hx : x ∈ Aset
    · rw [integral_map hY.aemeasurable (hfm x).aestronglyMeasurable]
      have := (hfix x hx).2
      simp only [g, Set.indicator_of_mem hx]
      refine le_trans (le_of_eq ?_) this
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only [f, Set.indicator_of_mem hx, one_mul]
      rfl
    · have : f x = fun _ => 0 := by
        funext y
        simp [f, Set.indicator_of_notMem hx]
      rw [this]
      simp [g, Set.indicator_of_notMem hx]
  have hres := coupling_freeze_bound (dynPast S t) (buffer_past_le S t) (buffer_delta_meas S t) hY
    hind hf hf0 hgint hfx hbound
  refine ⟨hres.1, ?_⟩
  filter_upwards [hres.2] with ω hω
  refine hω.2.trans ?_
  by_cases h : dynDelta S t ω ∈ Aset
  · simp [g, Set.indicator_of_mem h]
  · simp [g, Set.indicator_of_notMem h, hc]

private lemma coupling_sq_integral_of_eLpNorm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (hf : AEStronglyMeasurable f P) (hf0 : ∀ ω, 0 ≤ f ω)
    (c : ℝ) (hc : 0 ≤ c) (hb : eLpNorm f 2 P ≤ ENNReal.ofReal c) :
    Integrable (fun ω => f ω ^ 2) P ∧ ∫ ω, f ω ^ 2 ∂P ≤ c ^ 2 := by
  have hm : MemLp f (2 : ℕ) P := lt_of_le_of_lt (by simpa using hb) ENNReal.ofReal_lt_top
  have hi' := hm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hi : Integrable (fun ω => f ω ^ 2) P := hi'.congr
    (Filter.Eventually.of_forall fun ω => by
      change ‖f ω‖ ^ 2 = f ω ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)])
  refine ⟨hi, ?_⟩
  have heq := hm.eLpNorm_eq_integral_rpow_norm
    (show ((2 : ℕ) : ℝ≥0∞) ≠ 0 by norm_num) (by simp)
  have heq' : eLpNorm f ((2 : ℕ) : ℝ≥0∞) P =
      ENNReal.ofReal ((∫ ω, f ω ^ 2 ∂P) ^ (1 / ((2 : ℕ) : ℝ))) := by
    simpa only [ENNReal.toReal_natCast, Real.norm_eq_abs,
      abs_of_nonneg (hf0 _), Real.rpow_natCast, inv_eq_one_div] using heq
  have hb' : ENNReal.ofReal ((∫ ω, f ω ^ 2 ∂P) ^ (1 / ((2 : ℕ) : ℝ))) ≤ ENNReal.ofReal c := by
    rw [← heq']
    simpa using hb
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb'
  rw [ENNReal.toReal_ofReal hc] at hreal
  have hint0 : 0 ≤ ∫ ω, f ω ^ 2 ∂P := integral_nonneg fun ω => pow_nonneg (hf0 ω) 2
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hint0 _)] at hreal
  have h2 : ((∫ ω, f ω ^ 2 ∂P) ^ (1 / ((2 : ℕ) : ℝ))) ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hint0]
    norm_num
  calc ∫ ω, f ω ^ 2 ∂P = ((∫ ω, f ω ^ 2 ∂P) ^ (1 / ((2 : ℕ) : ℝ))) ^ 2 := h2.symm
    _ ≤ c ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hint0 _) hreal 2

private lemma coupling_sum_emaW_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (J : ℕ) :
    ∑ j ∈ Finset.range J, emaW β j ≤ 1 := by
  rw [← tsum_emaW hβ0 hβ1]
  exact ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (1 - β)).sum_le_tsum _
    (fun j _ => coupling_emaW_nonneg hβ0 hβ1 j)

private lemma coupling_aux_iid {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t j : ℕ) :
    IIDBatch P ((Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)) (S.cs.aux (t : ℤ) j) := by
  refine ⟨fun a => (S.cs.meas_aux _ _ a).aemeasurable, fun a => S.cs.law_aux _ _ a, ?_⟩
  exact S.cs.indep.precomp (g := fun a : Fin B => Sum.inr ((t : ℤ), j, a))
    (fun a b h => congrArg (fun q => q.2.2) (Sum.inr.inj h))

private lemma coupling_N0_op_fixed (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B) (hB : 0 < B) (t : ℕ) (x : Mat m n),
      0 < riskSigma S.C x →
      Integrable (fun ω => opNorm (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω) ^ 2) P ∧
      ∫ ω, opNorm (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω) ^ 2 ∂P ≤
        Kb ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * (2 * riskSigma S.C x) := by
  obtain ⟨K0, hK0⟩ := lem_app_dyn_batch_ii certOp p.γstar p.CSig
  refine ⟨max K0 0, le_max_right _ _, ?_⟩
  intro Ω _ P _ m n B S hB t x hx
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) :=
    Real.log_nonneg (by
      have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
      nlinarith)
  set G : ℕ → Ω → Mat m n := fun j ω => batchGrad x (physBatch S.C (S.cs.aux (t : ℤ) j) ω) with hG
  set c : ℝ := max K0 0 * Real.log (2 * (B : ℝ)) * fro (rOut S.C * x * rIn S.C) with hc
  have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg (le_max_right _ _) hlog) (movement_fro_nn _)
  have hGm : ∀ j, Measurable (G j) := fun j =>
    buffer_grad_meas measurable_const (coupling_phys_meas S.C (fun a => S.cs.meas_aux _ j a))
  have hGint : ∀ j, Integrable (fun ω => opNorm (G j ω) ^ 2) P ∧
      ∫ ω, opNorm (G j ω) ^ 2 ∂P ≤ c ^ 2 := by
    intro j
    have h := (hK0 m n B S.C hB S.size Ω P _ (coupling_aux_iid S t j) x).1
    have hb : eLpNorm (fun ω => opNorm (G j ω)) 2 P ≤ ENNReal.ofReal c :=
      h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog) (movement_fro_nn _)))
    exact coupling_sq_integral_of_eLpNorm P _
      ((buffer_opNorm_continuous.measurable.comp (hGm j)).aestronglyMeasurable)
      (fun ω => movement_opNorm_nonneg _) c hc0 hb
  set Sp : ℕ → Ω → Mat m n := fun J ω => ∑ j ∈ Finset.range J, emaW p.β j • G j ω with hSpdef
  have hSpm : ∀ J, Measurable (fun ω => opNorm (Sp J ω) ^ 2) := fun J =>
    (buffer_opNorm_continuous.measurable.comp
      (Finset.measurable_sum _ fun j _ => (hGm j).const_smul (emaW p.β j))).pow_const 2
  have hSp : ∀ J, Integrable (fun ω => opNorm (Sp J ω) ^ 2) P ∧
      ∫ ω, opNorm (Sp J ω) ^ 2 ∂P ≤ c ^ 2 := by
    intro J
    have hpt : ∀ ω, opNorm (Sp J ω) ^ 2 ≤
        ∑ j ∈ Finset.range J, emaW p.β j * opNorm (G j ω) ^ 2 := by
      intro ω
      obtain ⟨h1, h2, h3, h4⟩ := coupling_op_props (m := m) (n := n)
      exact coupling_norm_sum_sq opNorm h1 h2 h3 h4 J (emaW p.β)
        (coupling_emaW_nonneg p.hβ.1 p.hβ.2) (coupling_sum_emaW_le p.hβ.1 p.hβ.2 J) (fun j => G j ω)
    have hdom : Integrable (fun ω => ∑ j ∈ Finset.range J, emaW p.β j * opNorm (G j ω) ^ 2) P :=
      integrable_finset_sum _ fun j _ => (hGint j).1.const_mul _
    have hint : Integrable (fun ω => opNorm (Sp J ω) ^ 2) P :=
      Integrable.mono' hdom (hSpm J).aestronglyMeasurable (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt ω)
    refine ⟨hint, (integral_mono hint hdom hpt).trans ?_⟩
    rw [integral_finset_sum _ (fun j _ => (hGint j).1.const_mul _)]
    simp_rw [integral_const_mul]
    calc ∑ j ∈ Finset.range J, emaW p.β j * ∫ ω, opNorm (G j ω) ^ 2 ∂P
        ≤ ∑ j ∈ Finset.range J, emaW p.β j * c ^ 2 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hGint j).2
            (coupling_emaW_nonneg p.hβ.1 p.hβ.2 j)
      _ = (∑ j ∈ Finset.range J, emaW p.β j) * c ^ 2 := by rw [Finset.sum_mul]
      _ ≤ 1 * c ^ 2 := mul_le_mul_of_nonneg_right (coupling_sum_emaW_le p.hβ.1 p.hβ.2 J) (sq_nonneg c)
      _ = c ^ 2 := one_mul _
  obtain ⟨hsum, -, -⟩ := lem_app_dyn_chains_iii p S.C S.cs t x 0 hx S.size
  have hlim : ∀ᵐ ω ∂P, Filter.Tendsto (fun J => opNorm (Sp J ω) ^ 2) Filter.atTop
      (𝓝 (opNorm (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω) ^ 2)) := by
    filter_upwards [hsum] with ω hω
    have ht : Filter.Tendsto (fun J => Sp J ω) Filter.atTop
        (𝓝 (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω)) := hω.hasSum.tendsto_sum_nat
    exact ((buffer_opNorm_continuous.tendsto _).comp ht).pow 2
  have hN0m : Measurable (fun ω => opNorm (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω) ^ 2) :=
    (buffer_opNorm_continuous.measurable.comp
      (coupling_chainInit_meas S t (D := fun _ => x) measurable_const)).pow_const 2
  have hfat : ∫⁻ ω, ENNReal.ofReal (opNorm (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω) ^ 2) ∂P ≤
      ENNReal.ofReal (c ^ 2) := by
    calc _ = ∫⁻ ω, Filter.liminf (fun J => ENNReal.ofReal (opNorm (Sp J ω) ^ 2)) Filter.atTop ∂P :=
          lintegral_congr_ae (by
            filter_upwards [hlim] with ω hω
            exact (Filter.Tendsto.liminf_eq
              ((ENNReal.continuous_ofReal.tendsto _).comp hω)).symm)
      _ ≤ Filter.liminf (fun J => ∫⁻ ω, ENNReal.ofReal (opNorm (Sp J ω) ^ 2) ∂P) Filter.atTop :=
          lintegral_liminf_le (fun J => ENNReal.measurable_ofReal.comp (hSpm J))
      _ ≤ ENNReal.ofReal (c ^ 2) := by
          refine Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun J => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hSp J).1 (ae_of_all _ fun ω => sq_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hSp J).2
  have hnn : ∀ᵐ ω ∂P, 0 ≤ opNorm (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω) ^ 2 :=
    ae_of_all _ fun ω => sq_nonneg _
  have hint : Integrable (fun ω => opNorm (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω) ^ 2) P :=
    ⟨hN0m.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnn).2 (lt_of_le_of_lt hfat ENNReal.ofReal_lt_top)⟩
  have hc2 : c ^ 2 = max K0 0 ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * (2 * riskSigma S.C x) := by
    rw [hc, mul_pow, eqn_app_setup_whitened_risk]
    have : fro (rOut S.C * x * rIn S.C) = fro (Arot S.C x) := rfl
    rw [this]
    ring
  refine ⟨hint, ?_⟩
  rw [← hc2]
  apply (ENNReal.ofReal_le_ofReal_iff (sq_nonneg c)).mp
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
  exact hfat

private lemma coupling_cond_sum2 {Ω : Type*} (F : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hF : F ≤ m0) (k : ℕ) (a0 : Ω → ℝ)
    (ha0m : Measurable[F] a0) (C0 : ℝ) (ha0b : ∀ ω, |a0 ω| ≤ C0) (w : ℕ → ℝ)
    (hw : ∀ j, 0 ≤ w j) (f : ℕ → Ω → ℝ) (hf : ∀ j, Integrable (f j) P) (c : ℕ → ℝ)
    (hc : ∀ j, ∀ᵐ ω ∂P, condExp F P (f j) ω ≤ c j)
    (X : Ω → ℝ) (hX : AEStronglyMeasurable X P) (hX0 : ∀ ω, 0 ≤ X ω)
    (hXle : ∀ ω, X ω ≤ a0 ω + ∑ j ∈ Finset.range k, w j * f j ω) :
    Integrable X P ∧ ∀ᵐ ω ∂P, condExp F P X ω ≤ a0 ω + ∑ j ∈ Finset.range k, w j * c j := by
  have ha0int : Integrable a0 P :=
    Integrable.of_bound (ha0m.mono hF le_rfl).aestronglyMeasurable C0
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact ha0b ω)
  have hSint : Integrable (fun ω => ∑ j ∈ Finset.range k, w j * f j ω) P :=
    integrable_finset_sum _ fun j _ => (hf j).const_mul (w j)
  have hTint : Integrable (fun ω => a0 ω + ∑ j ∈ Finset.range k, w j * f j ω) P :=
    ha0int.add hSint
  have hXint : Integrable X P := by
    refine Integrable.mono' hTint hX (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (hX0 ω)]
    exact hXle ω
  refine ⟨hXint, ?_⟩
  have hmono : condExp F P X ≤ᵐ[P] condExp F P (fun ω => a0 ω + ∑ j ∈ Finset.range k, w j * f j ω) :=
    condExp_mono hXint hTint (ae_of_all _ hXle)
  have hfun : (fun ω => ∑ j ∈ Finset.range k, w j * f j ω) =
      ∑ j ∈ Finset.range k, (w j • f j) := by
    funext ω
    simp [Finset.sum_apply]
  have hadd := condExp_add (μ := P) ha0int hSint F
  have hconst : condExp F P a0 = a0 := condExp_of_stronglyMeasurable hF ha0m.stronglyMeasurable ha0int
  have hsum := condExp_finsetSum (μ := P) (s := Finset.range k) (f := fun j => w j • f j)
    (fun j _ => (hf j).smul (w j)) F
  have hsmul : ∀ j, condExp F P (w j • f j) =ᵐ[P] w j • condExp F P (f j) :=
    fun j => condExp_smul (w j) (f j) F
  have hall : ∀ᵐ ω ∂P, ∀ j ∈ Finset.range k, condExp F P (w j • f j) ω =
      (w j • condExp F P (f j)) ω :=
    (Filter.eventually_all_finset _).2 fun j _ => hsmul j
  have hall2 : ∀ᵐ ω ∂P, ∀ j ∈ Finset.range k, condExp F P (f j) ω ≤ c j :=
    (Filter.eventually_all_finset _).2 fun j _ => hc j
  filter_upwards [hmono, hadd, hsum, hall, hall2] with ω h1 h0 h2 h3 h4
  refine h1.trans ?_
  have h0' : condExp F P (fun ω => a0 ω + ∑ j ∈ Finset.range k, w j * f j ω) ω =
      a0 ω + condExp F P (fun ω => ∑ j ∈ Finset.range k, w j * f j ω) ω := by
    have := h0
    simp only [Pi.add_apply] at this
    rw [hconst] at this
    exact this
  rw [h0', hfun, h2, Finset.sum_apply]
  refine add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_)
  rw [h3 j hj]
  exact mul_le_mul_of_nonneg_left (h4 j hj) (hw j)

private lemma coupling_ii_assemble {p : DynParams} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ)
    (A : Set Ω) (hA : MeasurableSet[dynPast S t] A)
    (h : Ω → ℝ) (hh0 : ∀ ω, 0 ≤ h ω) (hint : Integrable h P)
    (a : Ω → ℝ) (ha : Measurable[dynPast S t] a) (ha0 : ∀ ω, 0 ≤ a ω)
    (G : Ω → ℝ) (hG : Integrable G P) (hG0 : ∀ ω, 0 ≤ G ω) (cG : ℝ)
    (hcG : ∀ᵐ ω ∂P, condExp (dynPast S t) P G ω ≤ cG)
    (L : ℝ) (hL : 0 ≤ L)
    (hle : ∀ ω ∈ A, h ω ≤ L * (a ω + G ω)) :
    ∀ᵐ ω ∂P, ω ∈ A → condExp (dynPast S t) P h ω ≤ L * (a ω + cG) := by
  have hk : ∀ k : ℕ, ∀ᵐ ω ∂P, ω ∈ A ∩ {ω | a ω ≤ k} →
      condExp (dynPast S t) P h ω ≤ L * (a ω + cG) := by
    intro k
    have hAk : MeasurableSet[dynPast S t] (A ∩ {ω | a ω ≤ k}) :=
      hA.inter (measurableSet_le ha measurable_const)
    have hAkm : MeasurableSet (A ∩ {ω | a ω ≤ k}) := buffer_past_le S t _ hAk
    have ha0m : Measurable[dynPast S t] (fun ω => L * (A ∩ {ω | a ω ≤ k}).indicator a ω) :=
      (ha.indicator hAk).const_mul L
    have ha0b : ∀ ω, |L * (A ∩ {ω | a ω ≤ k}).indicator a ω| ≤ L * k := by
      intro ω
      by_cases hω : ω ∈ A ∩ {ω | a ω ≤ k}
      · rw [Set.indicator_of_mem hω, abs_of_nonneg (mul_nonneg hL (ha0 ω))]
        exact mul_le_mul_of_nonneg_left hω.2 hL
      · rw [Set.indicator_of_notMem hω]
        simp only [mul_zero, abs_zero]
        exact mul_nonneg hL (Nat.cast_nonneg k)
    have hXle : ∀ ω, (A ∩ {ω | a ω ≤ k}).indicator h ω ≤
        L * (A ∩ {ω | a ω ≤ k}).indicator a ω + ∑ j ∈ Finset.range 1, L * G ω := by
      intro ω
      simp only [Finset.sum_range_one]
      by_cases hω : ω ∈ A ∩ {ω | a ω ≤ k}
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        have := hle ω hω.1
        linarith
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
        simpa using mul_nonneg hL (hG0 ω)
    obtain ⟨-, hcond⟩ := coupling_cond_sum2 (dynPast S t) (buffer_past_le S t) 1
      (fun ω => L * (A ∩ {ω | a ω ≤ k}).indicator a ω) ha0m (L * k) ha0b (fun _ => L)
      (fun _ => hL) (fun _ => G) (fun _ => hG) (fun _ => cG) (fun _ => hcG)
      ((A ∩ {ω | a ω ≤ k}).indicator h) (hint.1.indicator hAkm)
      (fun ω => Set.indicator_nonneg (fun ω _ => hh0 ω) ω) hXle
    have hind := condExp_indicator (m := dynPast S t) hint hAk
    filter_upwards [hcond, hind] with ω h1 h2 hω
    simp only [Set.indicator_of_mem hω, Finset.sum_range_one] at h1 h2
    rw [← h2]
    linarith
  have hall := ae_all_iff.2 hk
  filter_upwards [hall] with ω hω hωA
  have hω' := hω ⌈a ω⌉₊
  exact hω' ⟨hωA, show a ω ≤ ((⌈a ω⌉₊ : ℕ) : ℝ) from Nat.le_ceil (a ω)⟩

private lemma coupling_ii_aux (certOp : Muon.External.GaussianOpNormL6) (p : DynParams)
    (rlo rhi E : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ B0 : ℕ, ∃ K : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B), B0 ≤ B → ∀ t r : ℕ, r ≤ 4 * blockLen B →
      (Integrable ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => fro (dynErrV p S t r ω) ^ 2)) P ∧
        ∀ᵐ ω ∂P, ω ∈ dynInK S t (rlo, rhi, E) →
          condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
            (fun ω => fro (dynErrV p S t r ω) ^ 2)) ω ≤
            K * p.β ^ (2 * (r + 1)) * (fro (dynBuf S t ω) ^ 2 + B)) ∧
      (Integrable ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => opNorm (dynErrV p S t r ω) ^ 2)) P ∧
        ∀ᵐ ω ∂P, ω ∈ dynInK S t (rlo, rhi, E) →
          condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
            (fun ω => opNorm (dynErrV p S t r ω) ^ 2)) ω ≤
            K * p.β ^ (2 * (r + 1)) * (opNorm (dynBuf S t ω) ^ 2 + Real.log (2 * (B : ℝ)) ^ 2)) := by
  obtain ⟨Kb, hKb0, hKb⟩ := coupling_N0_op_fixed certOp p
  set CM : ℝ := cMConst p.CSig p.γstar with hCM
  set q : ℝ := (rlo * p.ϱ)⁻¹ with hq
  have hq0 : 0 ≤ q := by
    have := p.hϱ
    rw [hq]
    positivity
  have hCM0 : 0 ≤ CM := by
    rw [hCM]
    unfold cMConst
    positivity
  have hrhi : 0 < rhi := lt_of_lt_of_le hrlo hle
  set MF : ℝ := max 1 (2 * rhi * CM) with hMF
  set MO : ℝ := max 1 (2 * rhi * Kb ^ 2) with hMO
  have hMF1 : 1 ≤ MF := le_max_left _ _
  have hMO1 : 1 ≤ MO := le_max_left _ _
  refine ⟨1, max (2 * q * MF) (2 * q * MO), ?_⟩
  intro Ω _ P _ m n B S hB t r _
  have hB1 : 0 < B := hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB1
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) :=
    Real.log_nonneg (by
      have hB1' : (1 : ℝ) ≤ B := by exact_mod_cast hB1
      nlinarith)
  set A := dynInK S t (rlo, rhi, E) with hAdef
  have hA : MeasurableSet[dynPast S t] A := coupling_A_meas S t _
  have hAm : MeasurableSet A := buffer_past_le S t _ hA
  have hR : Measurable (fun D : Mat m n => riskSigma S.C D) :=
    (show Continuous (fun D : Mat m n => riskSigma S.C D) by
      unfold riskSigma pairSigma
      fun_prop).measurable
  set Aset : Set (Mat m n) := {x | rlo ≤ riskSigma S.C x ∧ riskSigma S.C x ≤ rhi} with hAsetdef
  have hAset : MeasurableSet Aset :=
    (measurableSet_le measurable_const hR).inter (measurableSet_le hR measurable_const)
  have hAin : ∀ ω ∈ A, dynDelta S t ω ∈ Aset := by
    intro ω hω
    have h : rlo ≤ riskSigma S.C (dynDelta S t ω) ∧ riskSigma S.C (dynDelta S t ω) ≤ rhi ∧
        fro (dynDelta S t ω) ^ 2 ≤ E := hω
    exact ⟨h.1, h.2.1⟩
  have hβ0 : 0 ≤ p.β ^ (2 * (r + 1)) := pow_nonneg p.hβ.1 _
  have hL : 0 ≤ 2 * q * p.β ^ (2 * (r + 1)) := by positivity
  constructor
  · -- Frobenius display
    have hmeas : Measurable (A.indicator (fun ω => fro (dynErrV p S t r ω) ^ 2)) :=
      (buffer_fro_sq_meas.comp (coupling_errV_meas S t r)).indicator hAm
    have hbd : ∀ ω, |A.indicator (fun ω => fro (dynErrV p S t r ω) ^ 2) ω| ≤ 4 * (p.γstar * B) := by
      intro ω
      have h0 : 0 ≤ A.indicator (fun ω => fro (dynErrV p S t r ω) ^ 2) ω :=
        Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
      rw [abs_of_nonneg h0]
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]; exact coupling_V_fro_bdd S t r ω
      · rw [Set.indicator_of_notMem hω]
        have := p.hγ
        positivity
    have hint : Integrable (A.indicator (fun ω => fro (dynErrV p S t r ω) ^ 2)) P :=
      Integrable.of_bound hmeas.aestronglyMeasurable _ (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact hbd ω)
    refine ⟨hint, ?_⟩
    have hfix : ∀ x ∈ Aset, Integrable (fun ω => (fun D : Mat m n => fro D ^ 2)
          (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω)) P ∧
        ∫ ω, (fun D : Mat m n => fro D ^ 2) (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω) ∂P ≤
          2 * rhi * CM * B := by
      intro x hx
      obtain ⟨-, hi, hle'⟩ := lem_app_dyn_chains_iii p S.C S.cs t x 0
        (lt_of_lt_of_le hrlo hx.1) S.size
      refine ⟨hi, hle'.trans ?_⟩
      have : 2 * riskSigma S.C x * CM * (B : ℝ) ≤ 2 * rhi * CM * B := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hx.2 (by norm_num : (0 : ℝ) ≤ 2)) hCM0
        exact mul_le_mul_of_nonneg_right this hBr.le
      exact this
    have hcF : 0 ≤ 2 * rhi * CM * (B : ℝ) := by positivity
    obtain ⟨hGint, hGcond⟩ := coupling_N0_cond S t Aset hAset (fun D => fro D ^ 2)
      buffer_fro_sq_meas (fun x => sq_nonneg _) _ hcF hfix
    have hres := coupling_ii_assemble S t A hA
      (A.indicator (fun ω => fro (dynErrV p S t r ω) ^ 2))
      (fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω) hint
      (fun ω => fro (dynBuf S t ω) ^ 2)
      (buffer_fro_sq_meas.comp (buffer_state_meas S t).2) (fun ω => sq_nonneg _)
      (fun ω => Aset.indicator (fun _ => (1 : ℝ)) (dynDelta S t ω) *
        fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2)
      hGint (fun ω => mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (sq_nonneg _))
      _ hGcond (2 * q * p.β ^ (2 * (r + 1))) hL (by
        intro ω hω
        rw [Set.indicator_of_mem hω]
        have h0 : rlo ≤ riskSigma S.C (dynDelta S t ω) := (hAin ω hω).1
        have := coupling_V_fro_path S rlo hrlo t r ω h0
        rw [Set.indicator_of_mem (hAin ω hω), one_mul]
        calc _ ≤ _ := this
          _ = _ := by rw [hq])
    filter_upwards [hres] with ω hω hωA
    refine (hω hωA).trans ?_
    have ha0 : 0 ≤ fro (dynBuf S t ω) ^ 2 := sq_nonneg _
    have hK : 2 * q * MF ≤ max (2 * q * MF) (2 * q * MO) := le_max_left _ _
    have h1 : fro (dynBuf S t ω) ^ 2 + 2 * rhi * CM * B ≤ MF * (fro (dynBuf S t ω) ^ 2 + B) := by
      have e1 : fro (dynBuf S t ω) ^ 2 ≤ MF * fro (dynBuf S t ω) ^ 2 := by nlinarith
      have e2 : 2 * rhi * CM * (B : ℝ) ≤ MF * B :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hBr.le
      nlinarith
    calc 2 * q * p.β ^ (2 * (r + 1)) * (fro (dynBuf S t ω) ^ 2 + 2 * rhi * CM * B)
        ≤ 2 * q * p.β ^ (2 * (r + 1)) * (MF * (fro (dynBuf S t ω) ^ 2 + B)) :=
          mul_le_mul_of_nonneg_left h1 hL
      _ = (2 * q * MF) * p.β ^ (2 * (r + 1)) * (fro (dynBuf S t ω) ^ 2 + B) := by ring
      _ ≤ max (2 * q * MF) (2 * q * MO) * p.β ^ (2 * (r + 1)) * (fro (dynBuf S t ω) ^ 2 + B) := by
          have : 0 ≤ p.β ^ (2 * (r + 1)) * (fro (dynBuf S t ω) ^ 2 + B) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hK this]
  · -- operator display
    have hmeas : Measurable (A.indicator (fun ω => opNorm (dynErrV p S t r ω) ^ 2)) :=
      ((buffer_opNorm_continuous.measurable.comp (coupling_errV_meas S t r)).pow_const 2).indicator hAm
    have hbd : ∀ ω, |A.indicator (fun ω => opNorm (dynErrV p S t r ω) ^ 2) ω| ≤ 4 := by
      intro ω
      have h0 : 0 ≤ A.indicator (fun ω => opNorm (dynErrV p S t r ω) ^ 2) ω :=
        Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
      rw [abs_of_nonneg h0]
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]; exact coupling_V_op_bdd S t r ω
      · rw [Set.indicator_of_notMem hω]; norm_num
    have hint : Integrable (A.indicator (fun ω => opNorm (dynErrV p S t r ω) ^ 2)) P :=
      Integrable.of_bound hmeas.aestronglyMeasurable _ (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact hbd ω)
    refine ⟨hint, ?_⟩
    have hfix : ∀ x ∈ Aset, Integrable (fun ω => (fun D : Mat m n => opNorm D ^ 2)
          (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω)) P ∧
        ∫ ω, (fun D : Mat m n => opNorm D ^ 2) (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω) ∂P ≤
          Kb ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * (2 * rhi) := by
      intro x hx
      obtain ⟨hi, hle'⟩ := hKb Ω P m n B S hB1 t x (lt_of_lt_of_le hrlo hx.1)
      refine ⟨hi, hle'.trans ?_⟩
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx.2 (by norm_num))
        (by positivity)
    have hcO : 0 ≤ Kb ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * (2 * rhi) := by positivity
    obtain ⟨hGint, hGcond⟩ := coupling_N0_cond S t Aset hAset (fun D => opNorm D ^ 2)
      (buffer_opNorm_continuous.measurable.pow_const 2) (fun x => sq_nonneg _) _ hcO hfix
    have hres := coupling_ii_assemble S t A hA
      (A.indicator (fun ω => opNorm (dynErrV p S t r ω) ^ 2))
      (fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω) hint
      (fun ω => opNorm (dynBuf S t ω) ^ 2)
      ((buffer_opNorm_continuous.measurable.comp (buffer_state_meas S t).2).pow_const 2)
      (fun ω => sq_nonneg _)
      (fun ω => Aset.indicator (fun _ => (1 : ℝ)) (dynDelta S t ω) *
        opNorm (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2)
      hGint (fun ω => mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (sq_nonneg _))
      _ hGcond (2 * q * p.β ^ (2 * (r + 1))) hL (by
        intro ω hω
        rw [Set.indicator_of_mem hω]
        have h0 : rlo ≤ riskSigma S.C (dynDelta S t ω) := (hAin ω hω).1
        have := coupling_V_op_path S rlo hrlo t r ω h0
        rw [Set.indicator_of_mem (hAin ω hω), one_mul]
        calc _ ≤ _ := this
          _ = _ := by rw [hq])
    filter_upwards [hres] with ω hω hωA
    refine (hω hωA).trans ?_
    have ha0 : 0 ≤ opNorm (dynBuf S t ω) ^ 2 := sq_nonneg _
    have hK : 2 * q * MO ≤ max (2 * q * MF) (2 * q * MO) := le_max_right _ _
    have hlg : 0 ≤ Real.log (2 * (B : ℝ)) ^ 2 := sq_nonneg _
    have h1 : opNorm (dynBuf S t ω) ^ 2 + Kb ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * (2 * rhi) ≤
        MO * (opNorm (dynBuf S t ω) ^ 2 + Real.log (2 * (B : ℝ)) ^ 2) := by
      have e1 : opNorm (dynBuf S t ω) ^ 2 ≤ MO * opNorm (dynBuf S t ω) ^ 2 := by nlinarith
      have e2 : Kb ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * (2 * rhi) ≤ MO * Real.log (2 * (B : ℝ)) ^ 2 := by
        have := mul_le_mul_of_nonneg_right (le_max_right 1 (2 * rhi * Kb ^ 2)) hlg
        nlinarith
      nlinarith
    calc 2 * q * p.β ^ (2 * (r + 1)) * (opNorm (dynBuf S t ω) ^ 2 +
          Kb ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * (2 * rhi))
        ≤ 2 * q * p.β ^ (2 * (r + 1)) * (MO * (opNorm (dynBuf S t ω) ^ 2 +
          Real.log (2 * (B : ℝ)) ^ 2)) := mul_le_mul_of_nonneg_left h1 hL
      _ = (2 * q * MO) * p.β ^ (2 * (r + 1)) * (opNorm (dynBuf S t ω) ^ 2 +
          Real.log (2 * (B : ℝ)) ^ 2) := by ring
      _ ≤ max (2 * q * MF) (2 * q * MO) * p.β ^ (2 * (r + 1)) * (opNorm (dynBuf S t ω) ^ 2 +
          Real.log (2 * (B : ℝ)) ^ 2) := by
          have : 0 ≤ p.β ^ (2 * (r + 1)) * (opNorm (dynBuf S t ω) ^ 2 +
              Real.log (2 * (B : ℝ)) ^ 2) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hK this]

/-! ## `lem:app-dyn-coupling` -/

/-- `lem:app-dyn-coupling`, snapshot `cr-2026-10-23`, part (i). On `{Δ_t ∈ 𝒦}` (written as the indicator
of that event, with the conditional expectation given `𝓕_t`), for `0 ≤ r ≤ 4L`. Constants `B₀`, `K`
depend on the fixed parameters and `𝒦` only (`B₀` is the one of `lem:app-dyn-movement`(ii)). Two displays:
the Frobenius bound on the sum of squares, and the operator-norm bound on the buffer.
Statement verbatim from `section.tex` (ll. 1557–1571):
```latex
\begin{lemma}[Coupling]\label{lem:app-dyn-coupling}
Let $\mathcal K=\mathcal K(r_-,r_+,E)$ with $B_0$ as in \cref{lem:app-dyn-movement}.
At a step $t$, on the event $\{\Dt\in\mathcal K\}$, let the chains at time $t$
be those of \cref{def:app-dyn-chains} with $D=\Dt$ and $m=M^\circ_{t-1}$. Then
for $0\le r\le4L$:
\begin{enumerate}[label=(\roman*)]
\item $\EE_t\norm{M^\circ_{t+r}-\widehat N_r}_\F^2+\EE_t\norm{{\mathsf S}_{t+r}-\widehat V_r}_\F^2\le Cr^2$
and $\EE_t\norm{M^\circ_{t+r}-\widehat N_r}^2\le Cr^2\log^2(2B)/B$;
\item $\EE_t\norm{\widehat V_r-V_r}_\F^2\le C\bmom^{2(r+1)}(\norm m_\F^2+B)$ and
$\EE_t\norm{\widehat V_r-V_r}^2\le C\bmom^{2(r+1)}(\norm m^2+\log^2(2B))$;
\item $\EE_t\big\|\sum_{r<L}({\mathsf S}_{t+r}-V_r)\big\|_\F^2\le C(L^4+B+\norm m_\F^2)$;
\item $\EE_t\big\|\sum_{r<L}({\mathsf S}_{t+r}-V_r)\big\|\le C(\norm m+\log(2B))+CL^2\log(2B)/\sqrt B$.
\end{enumerate}
The constant $C$ depends only on $\mathcal K$ and the fixed parameters.
\end{lemma}
```
-/
theorem lem_app_dyn_coupling_i (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) (rlo rhi E : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ B0 : ℕ, ∃ K : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B), B0 ≤ B → ∀ t r : ℕ, r ≤ 4 * blockLen B →
      (Integrable ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => fro (dynErrM p S t r ω) ^ 2 + fro (dynErrS p S t r ω) ^ 2)) P ∧
        ∀ᵐ ω ∂P, ω ∈ dynInK S t (rlo, rhi, E) →
          condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
            (fun ω => fro (dynErrM p S t r ω) ^ 2 + fro (dynErrS p S t r ω) ^ 2)) ω ≤ K * (r : ℝ) ^ 2) ∧
      (Integrable ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => opNorm (dynErrM p S t r ω) ^ 2)) P ∧
        ∀ᵐ ω ∂P, ω ∈ dynInK S t (rlo, rhi, E) →
          condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
            (fun ω => opNorm (dynErrM p S t r ω) ^ 2)) ω ≤
            K * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B) := by
  exact coupling_i_aux certOp p rlo rhi E hrlo hle

/-- `lem:app-dyn-coupling`, snapshot `cr-2026-10-23`, part (ii): the same-buffer chain against the
stationary chain (`V̂_r − V_r`), with `m = M°_{t-1}`. Two displays: Frobenius and operator norm.
Statement verbatim from `section.tex` (ll. 1557–1571):
```latex
\begin{lemma}[Coupling]\label{lem:app-dyn-coupling}
Let $\mathcal K=\mathcal K(r_-,r_+,E)$ with $B_0$ as in \cref{lem:app-dyn-movement}.
At a step $t$, on the event $\{\Dt\in\mathcal K\}$, let the chains at time $t$
be those of \cref{def:app-dyn-chains} with $D=\Dt$ and $m=M^\circ_{t-1}$. Then
for $0\le r\le4L$:
\begin{enumerate}[label=(\roman*)]
\item $\EE_t\norm{M^\circ_{t+r}-\widehat N_r}_\F^2+\EE_t\norm{{\mathsf S}_{t+r}-\widehat V_r}_\F^2\le Cr^2$
and $\EE_t\norm{M^\circ_{t+r}-\widehat N_r}^2\le Cr^2\log^2(2B)/B$;
\item $\EE_t\norm{\widehat V_r-V_r}_\F^2\le C\bmom^{2(r+1)}(\norm m_\F^2+B)$ and
$\EE_t\norm{\widehat V_r-V_r}^2\le C\bmom^{2(r+1)}(\norm m^2+\log^2(2B))$;
\item $\EE_t\big\|\sum_{r<L}({\mathsf S}_{t+r}-V_r)\big\|_\F^2\le C(L^4+B+\norm m_\F^2)$;
\item $\EE_t\big\|\sum_{r<L}({\mathsf S}_{t+r}-V_r)\big\|\le C(\norm m+\log(2B))+CL^2\log(2B)/\sqrt B$.
\end{enumerate}
The constant $C$ depends only on $\mathcal K$ and the fixed parameters.
\end{lemma}
```
-/
theorem lem_app_dyn_coupling_ii (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) (rlo rhi E : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ B0 : ℕ, ∃ K : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B), B0 ≤ B → ∀ t r : ℕ, r ≤ 4 * blockLen B →
      (Integrable ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => fro (dynErrV p S t r ω) ^ 2)) P ∧
        ∀ᵐ ω ∂P, ω ∈ dynInK S t (rlo, rhi, E) →
          condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
            (fun ω => fro (dynErrV p S t r ω) ^ 2)) ω ≤
            K * p.β ^ (2 * (r + 1)) * (fro (dynBuf S t ω) ^ 2 + B)) ∧
      (Integrable ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => opNorm (dynErrV p S t r ω) ^ 2)) P ∧
        ∀ᵐ ω ∂P, ω ∈ dynInK S t (rlo, rhi, E) →
          condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
            (fun ω => opNorm (dynErrV p S t r ω) ^ 2)) ω ≤
            K * p.β ^ (2 * (r + 1)) * (opNorm (dynBuf S t ω) ^ 2 + Real.log (2 * (B : ℝ)) ^ 2)) := by
  exact coupling_ii_aux certOp p rlo rhi E hrlo hle

private lemma coupling_sum_pow_le (p : DynParams) (k : ℕ) :
    ∑ r ∈ Finset.range k, p.β ^ r ≤ (1 - p.β)⁻¹ := by
  rw [← tsum_geometric_of_lt_one p.hβ.1 p.hβ.2]
  exact (summable_geometric_of_lt_one p.hβ.1 p.hβ.2).sum_le_tsum _
    (fun r _ => pow_nonneg p.hβ.1 r)

private lemma coupling_norm_finset_sum {m n : ℕ} (N : Mat m n → ℝ)
    (hadd : ∀ x y, N (x + y) ≤ N x + N y) (hzero : N 0 = 0)
    (k : ℕ) (x : ℕ → Mat m n) :
    N (∑ r ∈ Finset.range k, x r) ≤ ∑ r ∈ Finset.range k, N (x r) := by
  induction k with
  | zero => simp [hzero]
  | succ k ih =>
      simp only [Finset.sum_range_succ, Finset.sum_insert, Finset.mem_range, not_lt,
        Finset.sum_singleton]
      exact (hadd _ _).trans (add_le_add ih le_rfl)

private lemma coupling_norm_finset_sum_sq {m n : ℕ} (N : Mat m n → ℝ)
    (hadd : ∀ x y, N (x + y) ≤ N x + N y) (hzero : N 0 = 0)
    (hN0 : ∀ x, 0 ≤ N x) (k : ℕ) (x : ℕ → Mat m n) :
    N (∑ r ∈ Finset.range k, x r) ^ 2 ≤
      (k : ℝ) * ∑ r ∈ Finset.range k, N (x r) ^ 2 := by
  have h := coupling_norm_finset_sum N hadd hzero k x
  have hs := pow_le_pow_left₀ (hN0 _) h 2
  exact hs.trans (by simpa using
    (sq_sum_le_card_mul_sum_sq (s := Finset.range k) (f := fun r => N (x r))))

private lemma coupling_sumErr_eq {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) (ω : Ω) :
    dynSumErr p S t ω = ∑ r ∈ Finset.range (blockLen B),
      (dynErrS p S t r ω + dynErrV p S t r ω) := by
  unfold dynSumErr dynErrS dynErrV
  apply Finset.sum_congr rfl
  intro r hr
  abel

private lemma coupling_sumErr_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (hB : 0 < B) (t : ℕ) :
    Measurable (dynSumErr p S t) := by
  simp_rw [funext (coupling_sumErr_eq S t)]
  exact Finset.measurable_sum _ fun r _ =>
    (coupling_errS_meas S hB t r).add (coupling_errV_meas S t r)

private lemma coupling_sq_le_sq_of_sq_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  nlinarith

private lemma coupling_V_fro_linear {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (rlo : ℝ) (hrlo : 0 < rlo)
    (t r : ℕ) (ω : Ω) (h0 : rlo ≤ riskSigma S.C (dynDelta S t ω)) :
    fro (dynErrV p S t r ω) ≤
      Real.sqrt (2 * (rlo * p.ϱ)⁻¹) * p.β ^ (r + 1) *
        (fro (dynBuf S t ω) +
          fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) := by
  have hden : 0 < rlo * p.ϱ := mul_pos hrlo p.hϱ
  have hq : 0 ≤ 2 * (rlo * p.ϱ)⁻¹ := mul_nonneg (by norm_num) (inv_nonneg.mpr hden.le)
  have hs := coupling_V_fro_path S rlo hrlo t r ω h0
  apply coupling_sq_le_sq_of_sq_le (movement_fro_nn _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg p.hβ.1 _))
      (add_nonneg (movement_fro_nn _) (movement_fro_nn _)))
  refine hs.trans ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt hq]
  have hab : fro (dynBuf S t ω) ^ 2 +
      fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2 ≤
      (fro (dynBuf S t ω) +
        fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) ^ 2 := by
    nlinarith [mul_nonneg (movement_fro_nn (dynBuf S t ω))
      (movement_fro_nn (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω))]
  have hb : p.β ^ (2 * (r + 1)) = (p.β ^ (r + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
  rw [hb]
  exact mul_le_mul_of_nonneg_left hab (mul_nonneg hq (sq_nonneg _))

private lemma coupling_V_op_linear {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (rlo : ℝ) (hrlo : 0 < rlo)
    (t r : ℕ) (ω : Ω) (h0 : rlo ≤ riskSigma S.C (dynDelta S t ω)) :
    opNorm (dynErrV p S t r ω) ≤
      Real.sqrt (2 * (rlo * p.ϱ)⁻¹) * p.β ^ (r + 1) *
        (opNorm (dynBuf S t ω) +
          opNorm (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) := by
  have hden : 0 < rlo * p.ϱ := mul_pos hrlo p.hϱ
  have hq : 0 ≤ 2 * (rlo * p.ϱ)⁻¹ := mul_nonneg (by norm_num) (inv_nonneg.mpr hden.le)
  have hs := coupling_V_op_path S rlo hrlo t r ω h0
  apply coupling_sq_le_sq_of_sq_le (movement_opNorm_nonneg _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg p.hβ.1 _))
      (add_nonneg (movement_opNorm_nonneg _) (movement_opNorm_nonneg _)))
  refine hs.trans ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt hq]
  have hab : opNorm (dynBuf S t ω) ^ 2 +
      opNorm (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2 ≤
      (opNorm (dynBuf S t ω) +
        opNorm (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) ^ 2 := by
    nlinarith [mul_nonneg (movement_opNorm_nonneg (dynBuf S t ω))
      (movement_opNorm_nonneg (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω))]
  have hb : p.β ^ (2 * (r + 1)) = (p.β ^ (r + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
  rw [hb]
  exact mul_le_mul_of_nonneg_left hab (mul_nonneg hq (sq_nonneg _))

private lemma coupling_S_op_linear {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (hB : 0 < B)
    (rlo rhi E : ℝ) (hrlo : 0 < rlo) (t r : ℕ) (ω : Ω)
    (h0 : dynDelta S t ω ∈ admSetOf S.C (rlo, rhi, E))
    (hr : dynDelta S (t + r) ω ∈ admSetOf S.C (enl (rlo, rhi, E))) :
    opNorm (dynErrS p S t r ω) ≤
      (p.CSig * p.h * Real.sqrt p.γstar * Real.sqrt (4 * rhi) / rlo) * r / Real.sqrt B +
        (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * opNorm (dynErrM p S t r ω) := by
  obtain ⟨hlo0, hhi0, -⟩ := h0
  obtain ⟨hlor, hhir, -⟩ := hr
  simp only [enl] at hlor hhir
  simp only at hlo0 hhi0
  have hRrpos : 0 < riskSigma S.C (dynDelta S (t + r) ω) := lt_of_lt_of_le (half_pos hrlo) hlor
  have hϱo : 0 < rlo * p.ϱ := mul_pos hrlo p.hϱ
  have hϱ0 : rlo * p.ϱ ≤ physRidge p S.C (dynDelta S t ω) := by
    unfold physRidge
    nlinarith
  have hϱr : rlo * p.ϱ ≤ physRidge p S.C (dynDelta S (t + r) ω) := by
    unfold physRidge
    nlinarith
  set M := dynBuf S (t + r + 1) ω
  set N := dynHatN p S t r ω
  set ρ0 := physRidge p S.C (dynDelta S t ω)
  set ρr := physRidge p S.C (dynDelta S (t + r) ω)
  have hS : dynUpd S (t + r) ω = Q ρr M := coupling_upd_eq S (t + r) ω hRrpos.ne'
  have hV : dynHatV p S t r ω = Q ρ0 N := rfl
  have hsplit : dynErrS p S t r ω = (Q ρr M - Q ρ0 M) + (Q ρ0 M - Q ρ0 N) := by
    simp only [dynErrS, hS, hV]
    abel
  have hMN : dynErrM p S t r ω = M - N := rfl
  have hmv := (movement_all p S ω t (t + r) (Nat.le_add_right t r)).2.2
  have hrr : ((t + r : ℕ) : ℝ) - t = r := by push_cast; ring
  rw [hrr] at hmv
  set a0 := Real.sqrt (2 * riskSigma S.C (dynDelta S t ω))
  set ar := Real.sqrt (2 * riskSigma S.C (dynDelta S (t + r) ω))
  have ha0sq : a0 ^ 2 = 2 * riskSigma S.C (dynDelta S t ω) := Real.sq_sqrt (by linarith)
  have harsq : ar ^ 2 = 2 * riskSigma S.C (dynDelta S (t + r) ω) := Real.sq_sqrt (by linarith)
  have ha0le : a0 ≤ Real.sqrt (4 * rhi) := Real.sqrt_le_sqrt (by linarith)
  have harle : ar ≤ Real.sqrt (4 * rhi) := Real.sqrt_le_sqrt (by linarith)
  have ha0nn : 0 ≤ a0 := Real.sqrt_nonneg _
  have harnn : 0 ≤ ar := Real.sqrt_nonneg _
  set δ := p.CSig * p.h * Real.sqrt p.γstar * (r : ℝ) / Real.sqrt B
  have hδnn : 0 ≤ δ := by
    unfold δ
    have hC : 0 ≤ p.CSig := le_trans zero_le_one p.hC
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hC p.hh.le) (Real.sqrt_nonneg _))
        (Nat.cast_nonneg r)) (Real.sqrt_nonneg _)
  have hRdiff : |riskSigma S.C (dynDelta S (t + r) ω) - riskSigma S.C (dynDelta S t ω)| ≤
      δ * Real.sqrt (4 * rhi) := by
    have heq : riskSigma S.C (dynDelta S (t + r) ω) - riskSigma S.C (dynDelta S t ω) =
        (ar - a0) * (ar + a0) / 2 := by nlinarith
    rw [heq, abs_div, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ar + a0), abs_two]
    have h3 : (ar + a0) / 2 ≤ Real.sqrt (4 * rhi) := by linarith
    calc |ar - a0| * (ar + a0) / 2 = |ar - a0| * ((ar + a0) / 2) := by ring
      _ ≤ δ * Real.sqrt (4 * rhi) := mul_le_mul hmv h3 (by linarith) hδnn
  have hρdiff : |ρr - ρ0| = 2 * p.ϱ *
      |riskSigma S.C (dynDelta S (t + r) ω) - riskSigma S.C (dynDelta S t ω)| := by
    have : ρr - ρ0 = 2 * p.ϱ * (riskSigma S.C (dynDelta S (t + r) ω) -
        riskSigma S.C (dynDelta S t ω)) := by
      simp only [ρr, ρ0, physRidge]
      ring
    rw [this, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) p.hϱ.le)]
  have hA1 := (lem_app_dyn_schatten_iv hϱo hϱr hϱ0 M).1
  have hA1' : opNorm (Q ρr M - Q ρ0 M) ≤
      (p.CSig * p.h * Real.sqrt p.γstar * Real.sqrt (4 * rhi) / rlo) * r /
        Real.sqrt B := by
    refine hA1.trans ?_
    rw [hρdiff]
    calc 2 * p.ϱ * |riskSigma S.C (dynDelta S (t + r) ω) -
            riskSigma S.C (dynDelta S t ω)| / (2 * (rlo * p.ϱ))
        ≤ 2 * p.ϱ * (δ * Real.sqrt (4 * rhi)) / (2 * (rlo * p.ϱ)) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hRdiff (mul_nonneg (by norm_num) p.hϱ.le))
            (mul_pos (by norm_num) hϱo).le
      _ = _ := by
          unfold δ
          have hsB : Real.sqrt (B : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hB)).ne'
          field_simp [hrlo.ne', p.hϱ.ne', hsB]
  have hρ0pos : 0 < ρ0 := lt_of_lt_of_le hϱo hϱ0
  have hA2 : opNorm (Q ρ0 M - Q ρ0 N) ≤ ρ0 ^ (-(1 / 2 : ℝ)) * opNorm (M - N) := by
    simpa [schatNorm] using
      (lem_app_dyn_schatten_ii (p := ⊤) (Or.inr rfl) hρ0pos M N)
  have hA2' : opNorm (Q ρ0 M - Q ρ0 N) ≤
      (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * opNorm (dynErrM p S t r ω) := by
    rw [hMN]
    refine hA2.trans (mul_le_mul_of_nonneg_right ?_ (movement_opNorm_nonneg _))
    exact Real.rpow_le_rpow_of_nonpos hϱo hϱ0 (by norm_num)
  rw [hsplit]
  exact (coupling_op_props.2.1 _ _).trans (add_le_add hA1' hA2')

private lemma coupling_assemble_extra {p : DynParams} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ)
    (A : Set Ω) (hA : MeasurableSet[dynPast S t] A)
    (h : Ω → ℝ) (hh0 : ∀ ω, 0 ≤ h ω) (hint : Integrable h P)
    (a : Ω → ℝ) (ha : Measurable[dynPast S t] a) (ha0 : ∀ ω, 0 ≤ a ω)
    (G H : Ω → ℝ) (hG : Integrable G P) (hG0 : ∀ ω, 0 ≤ G ω)
    (hH : Integrable H P) (hH0 : ∀ ω, 0 ≤ H ω) (cG cH : ℝ)
    (hcG : ∀ᵐ ω ∂P, condExp (dynPast S t) P G ω ≤ cG)
    (hcH : ∀ᵐ ω ∂P, condExp (dynPast S t) P H ω ≤ cH)
    (L : ℝ) (hL : 0 ≤ L) (hle : ∀ ω ∈ A, h ω ≤ L * (a ω + G ω) + H ω) :
    ∀ᵐ ω ∂P, ω ∈ A →
      condExp (dynPast S t) P h ω ≤ L * (a ω + cG) + cH := by
  have hk : ∀ k : ℕ, ∀ᵐ ω ∂P, ω ∈ A ∩ {ω | a ω ≤ k} →
      condExp (dynPast S t) P h ω ≤ L * (a ω + cG) + cH := by
    intro k
    have hAk : MeasurableSet[dynPast S t] (A ∩ {ω | a ω ≤ k}) :=
      hA.inter (measurableSet_le ha measurable_const)
    have hAkm : MeasurableSet (A ∩ {ω | a ω ≤ k}) := buffer_past_le S t _ hAk
    have ha0m : Measurable[dynPast S t]
        (fun ω => L * (A ∩ {ω | a ω ≤ k}).indicator a ω) :=
      (ha.indicator hAk).const_mul L
    have ha0b : ∀ ω, |L * (A ∩ {ω | a ω ≤ k}).indicator a ω| ≤ L * k := by
      intro ω
      by_cases hω : ω ∈ A ∩ {ω | a ω ≤ k}
      · rw [Set.indicator_of_mem hω, abs_of_nonneg (mul_nonneg hL (ha0 ω))]
        exact mul_le_mul_of_nonneg_left hω.2 hL
      · rw [Set.indicator_of_notMem hω]
        simp only [mul_zero, abs_zero]
        exact mul_nonneg hL (Nat.cast_nonneg k)
    have hXle : ∀ ω, (A ∩ {ω | a ω ≤ k}).indicator h ω ≤
        L * (A ∩ {ω | a ω ≤ k}).indicator a ω +
          ∑ j ∈ Finset.range 2, (if j = 0 then L else 1) * (if j = 0 then G ω else H ω) := by
      intro ω
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.one_ne_zero,
        if_false, if_true]
      by_cases hω : ω ∈ A ∩ {ω | a ω ≤ k}
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        have := hle ω hω.1
        linarith
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
        have hGω := hG0 ω
        have hHω := hH0 ω
        positivity
    obtain ⟨-, hcond⟩ := coupling_cond_sum2 (dynPast S t) (buffer_past_le S t) 2
      (fun ω => L * (A ∩ {ω | a ω ≤ k}).indicator a ω) ha0m (L * k) ha0b
      (fun j => if j = 0 then L else 1) (fun j => by split_ifs <;> positivity)
      (fun j => if j = 0 then G else H) (fun j => by split_ifs <;> assumption)
      (fun j => if j = 0 then cG else cH) (fun j => by split_ifs <;> assumption)
      ((A ∩ {ω | a ω ≤ k}).indicator h) (hint.1.indicator hAkm)
      (fun ω => Set.indicator_nonneg (fun ω _ => hh0 ω) ω) hXle
    have hind := condExp_indicator (m := dynPast S t) hint hAk
    filter_upwards [hcond, hind] with ω h1 h2 hω
    simp only [Set.indicator_of_mem hω, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, Nat.one_ne_zero, if_false, if_true] at h1 h2
    rw [← h2]
    linarith
  have hall := ae_all_iff.2 hk
  filter_upwards [hall] with ω hω hωA
  have hω' := hω ⌈a ω⌉₊
  exact hω' ⟨hωA, show a ω ≤ ((⌈a ω⌉₊ : ℕ) : ℝ) from Nat.le_ceil (a ω)⟩

private lemma coupling_jensen_sq {Ω : Type*} (F : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf0 : ∀ ω, 0 ≤ f ω)
    (hf2 : Integrable (fun ω => f ω ^ 2) P) :
    ∀ᵐ ω ∂P, condExp F P f ω ^ 2 ≤ condExp F P (fun ω => f ω ^ 2) ω := by
  have hfun : (fun ω => ‖f ω‖ ^ (2 : ℝ)) = fun ω => f ω ^ 2 := by
    funext ω
    rw [Real.norm_of_nonneg (hf0 ω)]
    exact_mod_cast Real.rpow_two (f ω)
  have hj := Integrable.norm_condExp_rpow_le (m := F) (f := f) (μ := P) (p := (2 : ℝ))
    (by norm_num) (by rw [hfun]; exact hf2)
  rw [hfun] at hj
  filter_upwards [hj] with ω h
  simpa [Real.norm_eq_abs, Real.rpow_two, sq_abs] using h

private lemma coupling_fro_blocksq {m n : ℕ} (k : ℕ) (x y : ℕ → Mat m n) :
    fro (∑ r ∈ Finset.range k, (x r + y r)) ^ 2 ≤
      2 * (k : ℝ) * (∑ r ∈ Finset.range k, fro (x r) ^ 2 + ∑ r ∈ Finset.range k, fro (y r) ^ 2) := by
  rw [Finset.sum_add_distrib]
  have hs := coupling_norm_finset_sum_sq fro coupling_fro_props.2.1 coupling_fro_props.2.2.1
    coupling_fro_props.2.2.2 k x
  have hv := coupling_norm_finset_sum_sq fro coupling_fro_props.2.1 coupling_fro_props.2.2.1
    coupling_fro_props.2.2.2 k y
  have hn := coupling_fro_props.2.1 (∑ r ∈ Finset.range k, x r) (∑ r ∈ Finset.range k, y r)
  have hn2 := pow_le_pow_left₀ (movement_fro_nn _) hn 2
  have ht := coupling_sq_add_le' (fro (∑ r ∈ Finset.range k, x r))
    (fro (∑ r ∈ Finset.range k, y r))
  nlinarith

private lemma coupling_cond_l1_of_sq {Ω : Type*} (F : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hfm : AEStronglyMeasurable f P) (hf0 : ∀ ω, 0 ≤ f ω)
    (hf2 : Integrable (fun ω => f ω ^ 2) P) (c : Ω → ℝ) (hc0 : ∀ ω, 0 ≤ c ω)
    (hsq : ∀ᵐ ω ∂P, condExp F P (fun ω => f ω ^ 2) ω ≤ c ω ^ 2) :
    Integrable f P ∧ ∀ᵐ ω ∂P, condExp F P f ω ≤ c ω := by
  have hf : Integrable f P := by
    have hdom : Integrable (fun ω => 1 + f ω ^ 2) P := (integrable_const 1).add hf2
    refine Integrable.mono' hdom hfm (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (hf0 ω)]
    nlinarith [sq_nonneg (f ω - 1 / 2)]
  refine ⟨hf, ?_⟩
  have hj := coupling_jensen_sq F f hf0 hf2
  have hnon := condExp_nonneg (m := F) (μ := P) (ae_of_all _ hf0)
  filter_upwards [hsq, hj, hnon] with ω h1 h2 h3
  exact coupling_sq_le_sq_of_sq_le h3 (hc0 ω) (h2.trans (h1.trans le_rfl))

private lemma coupling_cond_ind_self {Ω : Type*} (F : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet[F] A) (g : Ω → ℝ) (hg : Integrable (A.indicator g) P)
    (c : ℝ) (hc0 : 0 ≤ c)
    (h : ∀ᵐ ω ∂P, ω ∈ A → condExp F P (A.indicator g) ω ≤ c) :
    ∀ᵐ ω ∂P, condExp F P (A.indicator g) ω ≤ c := by
  have hind := condExp_indicator (m := F) (μ := P) hg hA
  rw [Set.indicator_indicator, Set.inter_self] at hind
  filter_upwards [hind, h] with ω h1 h2
  by_cases hω : ω ∈ A
  · exact h2 hω
  · rw [h1, Set.indicator_of_notMem hω]
    exact hc0

/-- `lem:app-dyn-coupling`, snapshot `cr-2026-10-23`, part (iii): the Frobenius bound on the block sum
`∑_{r<L}(𝖲_{t+r} − V_r)`. Statement verbatim from `section.tex` (ll. 1557–1571):
```latex
\begin{lemma}[Coupling]\label{lem:app-dyn-coupling}
Let $\mathcal K=\mathcal K(r_-,r_+,E)$ with $B_0$ as in \cref{lem:app-dyn-movement}.
At a step $t$, on the event $\{\Dt\in\mathcal K\}$, let the chains at time $t$
be those of \cref{def:app-dyn-chains} with $D=\Dt$ and $m=M^\circ_{t-1}$. Then
for $0\le r\le4L$:
\begin{enumerate}[label=(\roman*)]
\item $\EE_t\norm{M^\circ_{t+r}-\widehat N_r}_\F^2+\EE_t\norm{{\mathsf S}_{t+r}-\widehat V_r}_\F^2\le Cr^2$
and $\EE_t\norm{M^\circ_{t+r}-\widehat N_r}^2\le Cr^2\log^2(2B)/B$;
\item $\EE_t\norm{\widehat V_r-V_r}_\F^2\le C\bmom^{2(r+1)}(\norm m_\F^2+B)$ and
$\EE_t\norm{\widehat V_r-V_r}^2\le C\bmom^{2(r+1)}(\norm m^2+\log^2(2B))$;
\item $\EE_t\big\|\sum_{r<L}({\mathsf S}_{t+r}-V_r)\big\|_\F^2\le C(L^4+B+\norm m_\F^2)$;
\item $\EE_t\big\|\sum_{r<L}({\mathsf S}_{t+r}-V_r)\big\|\le C(\norm m+\log(2B))+CL^2\log(2B)/\sqrt B$.
\end{enumerate}
The constant $C$ depends only on $\mathcal K$ and the fixed parameters.
\end{lemma}
```
-/
theorem lem_app_dyn_coupling_iii (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) (rlo rhi E : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ B0 : ℕ, ∃ K : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B), B0 ≤ B → ∀ t : ℕ,
      Integrable ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => fro (dynSumErr p S t ω) ^ 2)) P ∧
        ∀ᵐ ω ∂P, ω ∈ dynInK S t (rlo, rhi, E) →
          condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
            (fun ω => fro (dynSumErr p S t ω) ^ 2)) ω ≤
            K * ((blockLen B : ℝ) ^ 4 + B + fro (dynBuf S t ω) ^ 2) := by
  obtain ⟨B1, K1, h1⟩ := lem_app_dyn_coupling_i certOp p rlo rhi E hrlo hle
  obtain ⟨B2, K2, h2⟩ := lem_app_dyn_coupling_ii certOp p rlo rhi E hrlo hle
  set CM : ℝ := cMConst p.CSig p.γstar
  set q : ℝ := Real.sqrt (2 * (rlo * p.ϱ)⁻¹)
  set gb : ℝ := (1 - p.β)⁻¹
  set Cv : ℝ := 4 * (q * gb) ^ 2
  have hCM : 0 ≤ CM := by
    unfold CM cMConst
    positivity
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hgb : 0 ≤ gb := by
    unfold gb
    exact inv_nonneg.mpr (sub_nonneg.mpr p.hβ.2.le)
  have hCv : 0 ≤ Cv := by unfold Cv; positivity
  set K : ℝ := Cv * max 1 (2 * rhi * CM) + 2 * |K1|
  refine ⟨max B1 (max B2 1), K, ?_⟩
  intro Ω _ P _ m n B S hB t
  have hB1 : 0 < B := lt_of_lt_of_le one_pos
    ((le_max_right B2 1).trans ((le_max_right B1 (max B2 1)).trans hB))
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB1
  have hLpos : 0 < blockLen B := by
    unfold blockLen
    apply Nat.floor_pos.mpr
    have : (1 : ℝ) ≤ B := by exact_mod_cast hB1
    exact Real.one_le_rpow this (by norm_num)
  have hLr : (0 : ℝ) < blockLen B := by exact_mod_cast hLpos
  set A := dynInK S t (rlo, rhi, E)
  have hA : MeasurableSet[dynPast S t] A := coupling_A_meas S t _
  have hAm : MeasurableSet A := buffer_past_le S t _ hA
  have hi : ∀ r ∈ Finset.range (blockLen B),
      Integrable (A.indicator (fun ω => fro (dynErrM p S t r ω) ^ 2 +
        fro (dynErrS p S t r ω) ^ 2)) P ∧
      ∀ᵐ ω ∂P, condExp (dynPast S t) P
        (A.indicator (fun ω => fro (dynErrM p S t r ω) ^ 2 +
          fro (dynErrS p S t r ω) ^ 2)) ω ≤ |K1| * (r : ℝ) ^ 2 := by
    intro r hr
    have hrL : r ≤ 4 * blockLen B := by
      have := Finset.mem_range.mp hr
      omega
    have hh := h1 Ω P m n B S ((le_max_left _ _).trans hB) t r hrL
    refine ⟨hh.1.1, coupling_cond_ind_self (P := P) (dynPast S t) A hA _ hh.1.1 _
      (by positivity) ?_⟩
    filter_upwards [hh.1.2] with ω hω hωA
    exact (hω hωA).trans (mul_le_mul_of_nonneg_right (le_abs_self K1) (sq_nonneg _))
  have hv : ∀ r ∈ Finset.range (blockLen B),
      Integrable (A.indicator (fun ω => fro (dynErrV p S t r ω) ^ 2)) P := by
    intro r hr
    have hrL : r ≤ 4 * blockLen B := by
      have := Finset.mem_range.mp hr
      omega
    exact (h2 Ω P m n B S ((le_max_left B2 1).trans ((le_max_right B1 _).trans hB))
      t r hrL).1.1
  set fI : ℕ → Ω → ℝ := fun r ω => if r ∈ Finset.range (blockLen B) then
    A.indicator (fun ω => fro (dynErrM p S t r ω) ^ 2 + fro (dynErrS p S t r ω) ^ 2) ω else 0
  set H : Ω → ℝ := fun ω => 2 * (blockLen B : ℝ) *
    ∑ r ∈ Finset.range (blockLen B), fI r ω
  have hH0 : ∀ ω, 0 ≤ H ω := by
    intro ω
    unfold H fI
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun r hr => by
      simp only [if_pos hr]
      exact Set.indicator_nonneg (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) _)
  obtain ⟨hHint, hHcond⟩ := coupling_cond_sum (dynPast S t) (buffer_past_le S t)
    (blockLen B) 0 (fun _ => 2 * (blockLen B : ℝ)) (fun _ => by positivity)
    fI
    (fun r => by
      by_cases hr : r ∈ Finset.range (blockLen B)
      · simpa only [fI, if_pos hr] using (hi r hr).1
      · have h0 : fI r = fun _ => (0 : ℝ) := by funext ω; simp only [fI]; rw [if_neg hr]
        rw [h0]; exact integrable_const 0)
    (fun r => |K1| * (r : ℝ) ^ 2)
    (fun r => by
      by_cases hr : r ∈ Finset.range (blockLen B)
      · simpa only [fI, if_pos hr] using (hi r hr).2
      · have h0 : fI r = 0 := by funext ω; simp only [fI]; rw [if_neg hr]; rfl
        rw [h0, condExp_zero]
        exact ae_of_all _ fun ω => by simp only [Pi.zero_apply]; positivity)
    H (by exact ((integrable_finset_sum _ fun r hr => by
      simpa only [fI, if_pos hr] using (hi r hr).1).const_mul
        (2 * (blockLen B : ℝ))).aestronglyMeasurable)
    hH0 (by
      intro ω
      unfold H
      simp only [zero_add]
      rw [Finset.mul_sum])
  have hHbound : ∀ᵐ ω ∂P, condExp (dynPast S t) P H ω ≤
      2 * |K1| * (blockLen B : ℝ) ^ 4 := by
    filter_upwards [hHcond] with ω hω
    refine hω.trans ?_
    have hrsq : ∀ r ∈ Finset.range (blockLen B), (r : ℝ) ^ 2 ≤ (blockLen B : ℝ) ^ 2 := by
      intro r hr
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (Finset.mem_range.mp hr).le) 2
    calc 0 + ∑ r ∈ Finset.range (blockLen B),
          (2 * (blockLen B : ℝ)) * (|K1| * (r : ℝ) ^ 2)
        ≤ ∑ _r ∈ Finset.range (blockLen B),
          2 * |K1| * (blockLen B : ℝ) ^ 3 := by
            rw [zero_add]
            refine Finset.sum_le_sum fun r hr => ?_
            have := mul_le_mul_of_nonneg_left (hrsq r hr)
              (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg K1)) hLr.le)
            calc 2 * (blockLen B : ℝ) * (|K1| * (r : ℝ) ^ 2)
                = (2 * |K1| * (blockLen B : ℝ)) * (r : ℝ) ^ 2 := by ring
              _ ≤ (2 * |K1| * (blockLen B : ℝ)) * (blockLen B : ℝ) ^ 2 := this
              _ = 2 * |K1| * (blockLen B : ℝ) ^ 3 := by ring
      _ = 2 * |K1| * (blockLen B : ℝ) ^ 4 := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
  set Aset : Set (Mat m n) := {x | rlo ≤ riskSigma S.C x ∧ riskSigma S.C x ≤ rhi}
  have hR : Measurable (fun D : Mat m n => riskSigma S.C D) :=
    (show Continuous (fun D : Mat m n => riskSigma S.C D) by
      unfold riskSigma pairSigma
      fun_prop).measurable
  have hAset : MeasurableSet Aset :=
    (measurableSet_le measurable_const hR).inter (measurableSet_le hR measurable_const)
  set G : Ω → ℝ := fun ω => Aset.indicator (fun _ => (1 : ℝ)) (dynDelta S t ω) *
    fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2
  have hfix : ∀ x ∈ Aset, Integrable (fun ω =>
      fro (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω) ^ 2) P ∧
      ∫ ω, fro (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω) ^ 2 ∂P ≤
        2 * rhi * CM * B := by
    intro x hx
    obtain ⟨-, hxi, hxb⟩ := lem_app_dyn_chains_iii p S.C S.cs t x 0
      (lt_of_lt_of_le hrlo hx.1) S.size
    refine ⟨hxi, hxb.trans ?_⟩
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx.2 (by norm_num)) hCM) hBr.le
  have hcG0 : 0 ≤ 2 * rhi * CM * (B : ℝ) := by
    exact mul_nonneg (mul_nonneg (by linarith) hCM) hBr.le
  obtain ⟨hGint, hGcond⟩ := coupling_N0_cond S t Aset hAset (fun D => fro D ^ 2)
    buffer_fro_sq_meas (fun x => sq_nonneg _) _ hcG0 hfix
  have hG0 : ∀ ω, 0 ≤ G ω := by
    intro ω
    unfold G
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (sq_nonneg _)
  have hXmeas : Measurable (A.indicator (fun ω => fro (dynSumErr p S t ω) ^ 2)) :=
    (buffer_fro_sq_meas.comp (coupling_sumErr_meas S hB1 t)).indicator hAm
  have hX0 : ∀ ω, 0 ≤ A.indicator (fun ω => fro (dynSumErr p S t ω) ^ 2) ω :=
    fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
  have hXint : Integrable (A.indicator (fun ω => fro (dynSumErr p S t ω) ^ 2)) P := by
    set T : Ω → ℝ := fun ω => 2 * (blockLen B : ℝ) *
      (∑ r ∈ Finset.range (blockLen B), A.indicator
        (fun ω => fro (dynErrM p S t r ω) ^ 2 + fro (dynErrS p S t r ω) ^ 2) ω +
       ∑ r ∈ Finset.range (blockLen B), A.indicator
        (fun ω => fro (dynErrV p S t r ω) ^ 2) ω)
    have hTint : Integrable T P := by
      apply Integrable.const_mul
      apply Integrable.add
      · exact integrable_finset_sum _ fun r hr => (hi r hr).1
      · exact integrable_finset_sum _ fun r hr => hv r hr
    refine Integrable.mono' hTint hXmeas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (hX0 ω)]
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      rw [coupling_sumErr_eq S t ω]
      have hb := coupling_fro_blocksq (blockLen B) (fun r => dynErrS p S t r ω)
        (fun r => dynErrV p S t r ω)
      have hsind : ∑ r ∈ Finset.range (blockLen B), fro (dynErrS p S t r ω) ^ 2 ≤
          ∑ r ∈ Finset.range (blockLen B), A.indicator
            (fun ω => fro (dynErrM p S t r ω) ^ 2 + fro (dynErrS p S t r ω) ^ 2) ω := by
        simp_rw [Set.indicator_of_mem hω]
        exact Finset.sum_le_sum fun r _ => by nlinarith [sq_nonneg (fro (dynErrM p S t r ω))]
      refine hb.trans ?_
      unfold T
      simp_rw [Set.indicator_of_mem hω]
      have h2L : (0 : ℝ) ≤ 2 * (blockLen B : ℝ) := by positivity
      refine mul_le_mul_of_nonneg_left ?_ h2L
      simp_rw [Set.indicator_of_mem hω] at hsind
      linarith
    · rw [Set.indicator_of_notMem hω]
      unfold T
      exact mul_nonneg (by positivity) (add_nonneg
        (Finset.sum_nonneg fun r hr => Set.indicator_nonneg
          (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) _)
        (Finset.sum_nonneg fun r hr => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _))
  refine ⟨hXint, ?_⟩
  have hcoup := coupling_assemble_extra S t A hA
    (A.indicator (fun ω => fro (dynSumErr p S t ω) ^ 2)) hX0 hXint
    (fun ω => fro (dynBuf S t ω) ^ 2)
    (buffer_fro_sq_meas.comp (buffer_state_meas S t).2) (fun ω => sq_nonneg _)
    G H hGint hG0 hHint hH0 (2 * rhi * CM * B)
    (2 * |K1| * (blockLen B : ℝ) ^ 4) hGcond hHbound Cv hCv (by
    intro ω hω
    rw [Set.indicator_of_mem hω]
    have hAin : dynDelta S t ω ∈ Aset := ⟨hω.1, hω.2.1⟩
    have hsumβ : ∑ r ∈ Finset.range (blockLen B), p.β ^ (r + 1) ≤ gb := by
      calc _ ≤ ∑ r ∈ Finset.range (blockLen B), p.β ^ r :=
            Finset.sum_le_sum fun r _ => by
              rw [pow_succ]
              exact mul_le_of_le_one_right (pow_nonneg p.hβ.1 r) p.hβ.2.le
        _ ≤ gb := by simpa [gb] using coupling_sum_pow_le p (blockLen B)
    have hVn := coupling_norm_finset_sum fro coupling_fro_props.2.1 coupling_fro_props.2.2.1
      (blockLen B) (fun r => dynErrV p S t r ω)
    have hVeach : ∑ r ∈ Finset.range (blockLen B), fro (dynErrV p S t r ω) ≤
        q * gb * (fro (dynBuf S t ω) +
          fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) := by
      calc _ ≤ ∑ r ∈ Finset.range (blockLen B),
            q * p.β ^ (r + 1) * (fro (dynBuf S t ω) +
              fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) :=
            Finset.sum_le_sum fun r _ => coupling_V_fro_linear S rlo hrlo t r ω hAin.1
        _ = q * (∑ r ∈ Finset.range (blockLen B), p.β ^ (r + 1)) *
              (fro (dynBuf S t ω) +
                fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) := by
            rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsumβ hq)
              (add_nonneg (movement_fro_nn _) (movement_fro_nn _))
    have hVsq : fro (∑ r ∈ Finset.range (blockLen B), dynErrV p S t r ω) ^ 2 ≤
        (q * gb) ^ 2 * 2 * (fro (dynBuf S t ω) ^ 2 +
          fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2) := by
      have hh := pow_le_pow_left₀ (movement_fro_nn _) (hVn.trans hVeach) 2
      refine hh.trans ?_
      rw [mul_pow]
      calc _ ≤ (q * gb) ^ 2 * (2 * (fro (dynBuf S t ω) ^ 2 +
            fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2)) :=
            mul_le_mul_of_nonneg_left (coupling_sq_add_le' _ _) (sq_nonneg _)
        _ = _ := by ring
    have hSsq := coupling_norm_finset_sum_sq fro coupling_fro_props.2.1
      coupling_fro_props.2.2.1 coupling_fro_props.2.2.2 (blockLen B)
      (fun r => dynErrS p S t r ω)
    rw [coupling_sumErr_eq S t ω, Finset.sum_add_distrib]
    have hn := coupling_fro_props.2.1
      (∑ r ∈ Finset.range (blockLen B), dynErrS p S t r ω)
      (∑ r ∈ Finset.range (blockLen B), dynErrV p S t r ω)
    have hn2 := pow_le_pow_left₀ (movement_fro_nn _) hn 2
    have hsind : ∑ r ∈ Finset.range (blockLen B), fro (dynErrS p S t r ω) ^ 2 ≤
        ∑ r ∈ Finset.range (blockLen B), A.indicator
          (fun ω => fro (dynErrM p S t r ω) ^ 2 + fro (dynErrS p S t r ω) ^ 2) ω := by
      simp_rw [Set.indicator_of_mem hω]
      exact Finset.sum_le_sum fun r _ => by nlinarith [sq_nonneg (fro (dynErrM p S t r ω))]
    have hGmem : G ω = fro (chainInit p.β S.C (dynDelta S t ω)
        (S.cs.aux (t : ℤ)) ω) ^ 2 := by simp [G, Set.indicator_of_mem hAin]
    rw [hGmem]
    have hHexpr : H ω = 2 * (blockLen B : ℝ) *
        ∑ r ∈ Finset.range (blockLen B), A.indicator
          (fun ω => fro (dynErrM p S t r ω) ^ 2 + fro (dynErrS p S t r ω) ^ 2) ω := by
      unfold H fI
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      simp [hr]
    rw [hHexpr]
    unfold Cv
    have hLs := mul_le_mul_of_nonneg_left hsind hLr.le
    have ht := coupling_sq_add_le' (fro (∑ r ∈ Finset.range (blockLen B), dynErrS p S t r ω))
      (fro (∑ r ∈ Finset.range (blockLen B), dynErrV p S t r ω))
    nlinarith)
  filter_upwards [hcoup] with ω hc hωA
  refine (hc hωA).trans ?_
  have hmax : 1 ≤ max 1 (2 * rhi * CM) := le_max_left _ _
  have hmax2 : 2 * rhi * CM ≤ max 1 (2 * rhi * CM) := le_max_right _ _
  have hbuf : 0 ≤ fro (dynBuf S t ω) ^ 2 := sq_nonneg _
  have hL4 : 0 ≤ (blockLen B : ℝ) ^ 4 := by positivity
  have hcoef : 0 ≤ 2 * rhi * CM :=
    mul_nonneg (mul_nonneg (by norm_num) (hrlo.trans_le hle).le) hCM
  unfold K
  have e1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hCv) hbuf
  have e2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax2 hCv) hBr.le
  have e3 : 0 ≤ Cv * max 1 (2 * rhi * CM) * (blockLen B : ℝ) ^ 4 :=
    mul_nonneg (mul_nonneg hCv (by positivity)) hL4
  have e4 : 0 ≤ 2 * |K1| * ((B : ℝ) + fro (dynBuf S t ω) ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (by positivity)
  nlinarith

/-- `lem:app-dyn-coupling`, snapshot `cr-2026-10-23`, part (iv): the operator-norm bound on the block
sum. Statement verbatim from `section.tex` (ll. 1557–1571):
```latex
\begin{lemma}[Coupling]\label{lem:app-dyn-coupling}
Let $\mathcal K=\mathcal K(r_-,r_+,E)$ with $B_0$ as in \cref{lem:app-dyn-movement}.
At a step $t$, on the event $\{\Dt\in\mathcal K\}$, let the chains at time $t$
be those of \cref{def:app-dyn-chains} with $D=\Dt$ and $m=M^\circ_{t-1}$. Then
for $0\le r\le4L$:
\begin{enumerate}[label=(\roman*)]
\item $\EE_t\norm{M^\circ_{t+r}-\widehat N_r}_\F^2+\EE_t\norm{{\mathsf S}_{t+r}-\widehat V_r}_\F^2\le Cr^2$
and $\EE_t\norm{M^\circ_{t+r}-\widehat N_r}^2\le Cr^2\log^2(2B)/B$;
\item $\EE_t\norm{\widehat V_r-V_r}_\F^2\le C\bmom^{2(r+1)}(\norm m_\F^2+B)$ and
$\EE_t\norm{\widehat V_r-V_r}^2\le C\bmom^{2(r+1)}(\norm m^2+\log^2(2B))$;
\item $\EE_t\big\|\sum_{r<L}({\mathsf S}_{t+r}-V_r)\big\|_\F^2\le C(L^4+B+\norm m_\F^2)$;
\item $\EE_t\big\|\sum_{r<L}({\mathsf S}_{t+r}-V_r)\big\|\le C(\norm m+\log(2B))+CL^2\log(2B)/\sqrt B$.
\end{enumerate}
The constant $C$ depends only on $\mathcal K$ and the fixed parameters.
\end{lemma}
```
-/
theorem lem_app_dyn_coupling_iv (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) (rlo rhi E : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ B0 : ℕ, ∃ K : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B), B0 ≤ B → ∀ t : ℕ,
      Integrable ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => opNorm (dynSumErr p S t ω))) P ∧
        ∀ᵐ ω ∂P, ω ∈ dynInK S t (rlo, rhi, E) →
          condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
            (fun ω => opNorm (dynSumErr p S t ω))) ω ≤
            K * (opNorm (dynBuf S t ω) + Real.log (2 * (B : ℝ))) +
              K * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt B := by
  obtain ⟨Bm, hm⟩ := lem_app_dyn_movement_ii p rlo rhi E hrlo hle
  obtain ⟨B1, K1, h1⟩ := lem_app_dyn_coupling_i certOp p rlo rhi E hrlo hle
  obtain ⟨B2, K2, h2⟩ := lem_app_dyn_coupling_ii certOp p rlo rhi E hrlo hle
  obtain ⟨Kb, hKb0, hKb⟩ := coupling_N0_op_fixed certOp p
  set q : ℝ := Real.sqrt (2 * (rlo * p.ϱ)⁻¹)
  set qM : ℝ := (rlo * p.ϱ) ^ (-(1 / 2 : ℝ))
  set gb : ℝ := (1 - p.β)⁻¹
  set cR : ℝ := p.CSig * p.h * Real.sqrt p.γstar * Real.sqrt (4 * rhi) / rlo
  set cN : ℝ := |Kb| * Real.sqrt (2 * rhi)
  set cM : ℝ := Real.sqrt |K1|
  set Lv : ℝ := q * gb
  set Ch : ℝ := 2 * cR + qM * cM
  set K : ℝ := max (Lv * max 1 cN) Ch
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hqM : 0 ≤ qM := Real.rpow_nonneg (mul_pos hrlo p.hϱ).le _
  have hgb : 0 ≤ gb := by unfold gb; exact inv_nonneg.mpr (sub_nonneg.mpr p.hβ.2.le)
  have hrhi : 0 < rhi := hrlo.trans_le hle
  have hcR : 0 ≤ cR := by
    unfold cR
    have hC : 0 ≤ p.CSig := le_trans zero_le_one p.hC
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC p.hh.le) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) hrlo.le
  have hcN : 0 ≤ cN := by unfold cN; exact mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hcM : 0 ≤ cM := Real.sqrt_nonneg _
  have hLv : 0 ≤ Lv := by unfold Lv; exact mul_nonneg hq hgb
  have hCh : 0 ≤ Ch := by unfold Ch; exact add_nonneg (mul_nonneg (by norm_num) hcR) (mul_nonneg hqM hcM)
  refine ⟨max Bm (max B1 (max B2 1)), K, ?_⟩
  intro Ω _ P _ m n B S hB t
  have hB1 : 0 < B := lt_of_lt_of_le one_pos
    ((le_max_right B2 1).trans ((le_max_right B1 (max B2 1)).trans
      ((le_max_right Bm (max B1 (max B2 1))).trans hB)))
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB1
  have hsB : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBr
  have hLpos : 0 < blockLen B := by
    unfold blockLen
    apply Nat.floor_pos.mpr
    have : (1 : ℝ) ≤ B := by exact_mod_cast hB1
    exact Real.one_le_rpow this (by norm_num)
  have hLr : (0 : ℝ) < blockLen B := by exact_mod_cast hLpos
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) :=
    Real.log_nonneg (by
      have : (1 : ℝ) ≤ B := by exact_mod_cast hB1
      nlinarith)
  have hloghalf : 1 ≤ 2 * Real.log (2 * (B : ℝ)) := by
    have harg : (2 : ℝ) ≤ 2 * B := by
      have : (1 : ℝ) ≤ B := by exact_mod_cast hB1
      nlinarith
    have hl := Real.log_le_log (by norm_num) harg
    nlinarith [Real.log_two_gt_d9]
  set A := dynInK S t (rlo, rhi, E)
  have hA : MeasurableSet[dynPast S t] A := coupling_A_meas S t _
  have hAm : MeasurableSet A := buffer_past_le S t _ hA
  have hmov := hm Ω P m n B S ((le_max_left _ _).trans hB)
  have hi : ∀ r ∈ Finset.range (blockLen B),
      Integrable (A.indicator (fun ω => opNorm (dynErrM p S t r ω) ^ 2)) P ∧
      ∀ᵐ ω ∂P, condExp (dynPast S t) P
        (A.indicator (fun ω => opNorm (dynErrM p S t r ω) ^ 2)) ω ≤
          |K1| * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B := by
    intro r hr
    have hrL : r ≤ 4 * blockLen B := by
      have := Finset.mem_range.mp hr
      omega
    have hh := h1 Ω P m n B S ((le_max_left B1 _).trans ((le_max_right Bm _).trans hB)) t r hrL
    refine ⟨hh.2.1, coupling_cond_ind_self (P := P) (dynPast S t) A hA _ hh.2.1 _
      (by positivity) ?_⟩
    filter_upwards [hh.2.2] with ω hω hωA
    refine (hω hωA).trans ?_
    have := le_abs_self K1
    gcongr
  set eM : ℕ → Ω → ℝ := fun r ω => if r ∈ Finset.range (blockLen B) then
    A.indicator (fun ω => opNorm (dynErrM p S t r ω)) ω else 0
  have heM0 : ∀ r ω, 0 ≤ eM r ω := fun r ω => by
    unfold eM
    split_ifs
    · exact Set.indicator_nonneg (fun _ _ => movement_opNorm_nonneg _) _
    · exact le_rfl
  have heMsq : ∀ r ∈ Finset.range (blockLen B), (fun ω => eM r ω ^ 2) =
      A.indicator (fun ω => opNorm (dynErrM p S t r ω) ^ 2) := by
    intro r hr
    funext ω
    by_cases hω : ω ∈ A
    · simp only [eM, if_pos hr, Set.indicator_of_mem hω]
    · simp only [eM, if_pos hr, Set.indicator_of_notMem hω]
      norm_num
  have heMint : ∀ r, Integrable (eM r) P := by
    intro r
    by_cases hr : r ∈ Finset.range (blockLen B)
    · have hf2 : Integrable (fun ω => eM r ω ^ 2) P := by rw [heMsq r hr]; exact (hi r hr).1
      have hm' : AEStronglyMeasurable (eM r) P := by
        have heq : eM r = A.indicator (fun ω => opNorm (dynErrM p S t r ω)) := by
          funext ω; simp only [eM]; rw [if_pos hr]
        rw [heq]
        exact (((buffer_opNorm_continuous.measurable.comp (coupling_errM_meas S t r)).indicator hAm)).aestronglyMeasurable
      have hdom : Integrable (fun ω => 1 + eM r ω ^ 2) P := (integrable_const 1).add hf2
      refine Integrable.mono' hdom hm' (ae_of_all _ fun ω => ?_)
      rw [Real.norm_of_nonneg (heM0 r ω)]
      nlinarith [sq_nonneg (eM r ω - 1 / 2)]
    · have h0 : eM r = fun _ => (0 : ℝ) := by
        funext ω; simp only [eM]; rw [if_neg hr]
      rw [h0]; exact integrable_const 0
  have heMcond : ∀ r, ∀ᵐ ω ∂P,
      condExp (dynPast S t) P (eM r) ω ≤
        cM * r * Real.log (2 * (B : ℝ)) / Real.sqrt B := by
    intro r
    by_cases hr : r ∈ Finset.range (blockLen B)
    · have hf2 : Integrable (fun ω => eM r ω ^ 2) P := by rw [heMsq r hr]; exact (hi r hr).1
      have hj := coupling_jensen_sq (P := P) (dynPast S t) (eM r) (heM0 r) hf2
      have hn := condExp_nonneg (m := dynPast S t) (μ := P) (ae_of_all _ (heM0 r))
      filter_upwards [(hi r hr).2, hj, hn] with ω hsq hj' hn'
      have hj2 : |condExp (dynPast S t) P (eM r) ω| ^ 2 ≤
          condExp (dynPast S t) P (fun ω => eM r ω ^ 2) ω := by
        simpa [abs_of_nonneg hn'] using hj'
      rw [abs_of_nonneg hn', heMsq r hr] at hj2
      have hbroot : (Real.sqrt (B : ℝ)) ^ 2 = B := Real.sq_sqrt hBr.le
      have hcMsq : cM ^ 2 = |K1| := by unfold cM; rw [Real.sq_sqrt (abs_nonneg K1)]
      have hright : (cM * (r : ℝ) * Real.log (2 * (B : ℝ)) / Real.sqrt B) ^ 2 =
          |K1| * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B := by
        rw [div_pow, hbroot, mul_pow, mul_pow, hcMsq]
      apply coupling_sq_le_sq_of_sq_le hn' (by positivity)
      rw [hright]
      exact hj2.trans hsq
    · have h0 : eM r = 0 := by funext ω; simp only [eM]; rw [if_neg hr]; rfl
      rw [h0, condExp_zero]
      exact ae_of_all _ fun ω => by
        simp only [Pi.zero_apply]
        exact div_nonneg (mul_nonneg (mul_nonneg hcM (Nat.cast_nonneg r)) hlog) hsB.le
  set d : ℝ := cR * (blockLen B : ℝ) ^ 2 / Real.sqrt B
  set H : Ω → ℝ := fun ω => d + qM * ∑ r ∈ Finset.range (blockLen B), eM r ω
  have hd : 0 ≤ d := div_nonneg (mul_nonneg hcR (sq_nonneg _)) hsB.le
  have hH0 : ∀ ω, 0 ≤ H ω := fun ω =>
    add_nonneg hd (mul_nonneg hqM (Finset.sum_nonneg fun r _ => heM0 r ω))
  obtain ⟨hHint, hHcond⟩ := coupling_cond_sum (dynPast S t) (buffer_past_le S t)
    (blockLen B) d (fun _ => qM) (fun _ => hqM) eM
    heMint
    (fun r => cM * r * Real.log (2 * (B : ℝ)) / Real.sqrt B)
    heMcond
    H (((integrable_const d).add ((integrable_finset_sum _ fun r _ => heMint r).const_mul
      qM)).aestronglyMeasurable) hH0
    (fun ω => le_of_eq (by simp only [H]; rw [Finset.mul_sum]))
  have hHbound : ∀ᵐ ω ∂P, condExp (dynPast S t) P H ω ≤
      Ch * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt B := by
    filter_upwards [hHcond] with ω hω
    refine hω.trans ?_
    have hrsum : ∑ r ∈ Finset.range (blockLen B), (r : ℝ) ≤ (blockLen B : ℝ) ^ 2 := by
      calc _ ≤ ∑ _r ∈ Finset.range (blockLen B), (blockLen B : ℝ) :=
            Finset.sum_le_sum fun r hr => by exact_mod_cast (Finset.mem_range.mp hr).le
        _ = _ := by simp; ring
    have hsum : ∑ r ∈ Finset.range (blockLen B),
        qM * (cM * (r : ℝ) * Real.log (2 * (B : ℝ)) / Real.sqrt B) ≤
        qM * cM * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt B := by
      calc _ = qM * cM * Real.log (2 * (B : ℝ)) / Real.sqrt B *
            ∑ r ∈ Finset.range (blockLen B), (r : ℝ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r hr
              ring
        _ ≤ qM * cM * Real.log (2 * (B : ℝ)) / Real.sqrt B *
            (blockLen B : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hrsum (by positivity)
        _ = _ := by ring
    unfold d Ch
    have hdlog : cR * (blockLen B : ℝ) ^ 2 / Real.sqrt B ≤
        2 * cR * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt B := by
      have := mul_le_mul_of_nonneg_left hloghalf
        (div_nonneg (mul_nonneg hcR (sq_nonneg (blockLen B : ℝ))) hsB.le)
      have key : 2 * cR * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt B =
          cR * (blockLen B : ℝ) ^ 2 / Real.sqrt B * (2 * Real.log (2 * (B : ℝ))) := by ring
      rw [key]
      linarith
    calc d + ∑ j ∈ Finset.range (blockLen B),
          qM * (cM * (j : ℝ) * Real.log (2 * (B : ℝ)) / Real.sqrt B)
        ≤ 2 * cR * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt B +
          qM * cM * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt B :=
            add_le_add hdlog hsum
      _ = (2 * cR + qM * cM) * (blockLen B : ℝ) ^ 2 *
          Real.log (2 * (B : ℝ)) / Real.sqrt B := by ring
  set Aset : Set (Mat m n) := {x | rlo ≤ riskSigma S.C x ∧ riskSigma S.C x ≤ rhi}
  have hR : Measurable (fun D : Mat m n => riskSigma S.C D) :=
    (show Continuous (fun D : Mat m n => riskSigma S.C D) by
      unfold riskSigma pairSigma
      fun_prop).measurable
  have hAset : MeasurableSet Aset :=
    (measurableSet_le measurable_const hR).inter (measurableSet_le hR measurable_const)
  set G : Ω → ℝ := fun ω => Aset.indicator (fun _ => (1 : ℝ)) (dynDelta S t ω) *
    opNorm (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)
  have hG0 : ∀ ω, 0 ≤ G ω := by
    intro ω
    unfold G
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      (movement_opNorm_nonneg _)
  set G2 : Ω → ℝ := fun ω => Aset.indicator (fun _ => (1 : ℝ)) (dynDelta S t ω) *
    opNorm (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2
  have hfix : ∀ x ∈ Aset, Integrable (fun ω =>
      opNorm (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω) ^ 2) P ∧
      ∫ ω, opNorm (chainInit p.β S.C x (S.cs.aux (t : ℤ)) ω) ^ 2 ∂P ≤
        Kb ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * (2 * rhi) := by
    intro x hx
    obtain ⟨hxi, hxb⟩ := hKb Ω P m n B S hB1 t x (lt_of_lt_of_le hrlo hx.1)
    refine ⟨hxi, hxb.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx.2 (by norm_num))
      (mul_nonneg (sq_nonneg Kb) (sq_nonneg _))
  have hcG20 : 0 ≤ Kb ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * (2 * rhi) :=
    mul_nonneg (mul_nonneg (sq_nonneg Kb) (sq_nonneg _)) (by linarith)
  obtain ⟨hG2int, hG2cond⟩ := coupling_N0_cond S t Aset hAset (fun D => opNorm D ^ 2)
    (buffer_opNorm_continuous.measurable.pow_const 2) (fun x => sq_nonneg _) _ hcG20 hfix
  have hGsq : (fun ω => G ω ^ 2) = G2 := by
    funext ω
    by_cases hx : dynDelta S t ω ∈ Aset <;> simp [G, G2, hx]
  have hcNsq : (cN * Real.log (2 * (B : ℝ))) ^ 2 =
      Kb ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * (2 * rhi) := by
    have hrhi : 0 ≤ 2 * rhi := by linarith
    unfold cN
    rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt hrhi]
    ring
  obtain ⟨hGint, hGcond⟩ := coupling_cond_l1_of_sq (P := P) (dynPast S t) G
    (by
      unfold G
      exact (((measurable_const.indicator hAset).comp (coupling_delta_meas S t)).mul
        (buffer_opNorm_continuous.measurable.comp
          (coupling_chainInit_meas S t (coupling_delta_meas S t)))).aestronglyMeasurable)
    hG0 (by rw [hGsq]; exact hG2int)
    (fun _ => cN * Real.log (2 * (B : ℝ))) (fun _ => mul_nonneg hcN hlog) (by
      filter_upwards [hG2cond] with ω hω
      rw [hGsq, hcNsq]
      exact hω)
  have hXmeas : Measurable (A.indicator (fun ω => opNorm (dynSumErr p S t ω))) :=
    (buffer_opNorm_continuous.measurable.comp (coupling_sumErr_meas S hB1 t)).indicator hAm
  have hX0 : ∀ ω, 0 ≤ A.indicator (fun ω => opNorm (dynSumErr p S t ω)) ω :=
    fun ω => Set.indicator_nonneg (fun _ _ => movement_opNorm_nonneg _) ω
  have hSterm : ∀ ω ∈ A, ∀ r ∈ Finset.range (blockLen B), opNorm (dynErrS p S t r ω) ≤
      cR * r / Real.sqrt B + qM * eM r ω := by
    intro ω hω r hr
    have hr' : dynDelta S (t + r) ω ∈ admSetOf S.C (enl (rlo, rhi, E)) := by
      refine (hmov ω t hω).2 (t + r) ?_
      have : |((t + r : ℕ) : ℤ) - (t : ℤ)| = r := by push_cast; simp
      rw [this]
      have := Finset.mem_range.mp hr
      omega
    have hl := coupling_S_op_linear S hB1 rlo rhi E hrlo t r ω hω hr'
    have heMr : eM r ω = opNorm (dynErrM p S t r ω) := by
      simp only [eM]; rw [if_pos hr, Set.indicator_of_mem hω]
    rw [heMr]
    exact hl
  have hXint : Integrable (A.indicator (fun ω => opNorm (dynSumErr p S t ω))) P := by
    have heV2 : ∀ r ∈ Finset.range (blockLen B),
        Integrable (A.indicator (fun ω => opNorm (dynErrV p S t r ω) ^ 2)) P := by
      intro r hr
      have hrL : r ≤ 4 * blockLen B := by have := Finset.mem_range.mp hr; omega
      exact (h2 Ω P m n B S
        ((le_max_left B2 1).trans ((le_max_right B1 _).trans
          ((le_max_right Bm _).trans hB))) t r hrL).2.1
    have heV : ∀ r ∈ Finset.range (blockLen B),
        Integrable (A.indicator (fun ω => opNorm (dynErrV p S t r ω))) P := by
      intro r hr
      have hf2 := heV2 r hr
      have hm' := ((buffer_opNorm_continuous.measurable.comp (coupling_errV_meas S t r)).indicator hAm).aestronglyMeasurable (μ := P)
      have hdom := (integrable_const (1 : ℝ)).add hf2
      refine Integrable.mono' hdom hm' (ae_of_all _ fun ω => ?_)
      have h0 : 0 ≤ A.indicator (fun ω => opNorm (dynErrV p S t r ω)) ω :=
        Set.indicator_nonneg (fun _ _ => movement_opNorm_nonneg _) _
      rw [Real.norm_of_nonneg h0]
      by_cases hω : ω ∈ A
      · simp only [Set.indicator_of_mem hω, Pi.add_apply]
        nlinarith [sq_nonneg (opNorm (dynErrV p S t r ω) - 1 / 2)]
      · simp only [Set.indicator_of_notMem hω, Pi.add_apply]
        norm_num
    set T : Ω → ℝ := fun ω => H ω +
      ∑ r ∈ Finset.range (blockLen B), A.indicator (fun ω => opNorm (dynErrV p S t r ω)) ω
    have hTint : Integrable T P := hHint.add
      (integrable_finset_sum _ fun r hr => heV r hr)
    refine Integrable.mono' hTint hXmeas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (hX0 ω)]
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, coupling_sumErr_eq S t ω, Finset.sum_add_distrib]
      have hs := coupling_norm_finset_sum opNorm coupling_op_props.2.1 coupling_op_props.2.2.1
        (blockLen B) (fun r => dynErrS p S t r ω)
      have hv := coupling_norm_finset_sum opNorm coupling_op_props.2.1 coupling_op_props.2.2.1
        (blockLen B) (fun r => dynErrV p S t r ω)
      have htop := coupling_op_props.2.1
        (∑ r ∈ Finset.range (blockLen B), dynErrS p S t r ω)
        (∑ r ∈ Finset.range (blockLen B), dynErrV p S t r ω)
      have hSterm := hSterm ω hω
      unfold T
      simp_rw [Set.indicator_of_mem hω]
      calc opNorm (∑ r ∈ Finset.range (blockLen B), dynErrS p S t r ω +
              ∑ r ∈ Finset.range (blockLen B), dynErrV p S t r ω)
          ≤ ∑ r ∈ Finset.range (blockLen B), opNorm (dynErrS p S t r ω) +
              ∑ r ∈ Finset.range (blockLen B), opNorm (dynErrV p S t r ω) :=
            htop.trans (add_le_add hs hv)
        _ ≤ _ := by
          have hSs : ∑ r ∈ Finset.range (blockLen B), opNorm (dynErrS p S t r ω) ≤ H ω := by
            refine (Finset.sum_le_sum fun r hr => hSterm r hr).trans ?_
            have hrsum : ∑ r ∈ Finset.range (blockLen B), (r : ℝ) ≤ (blockLen B : ℝ) ^ 2 := by
              calc _ ≤ ∑ _r ∈ Finset.range (blockLen B), (blockLen B : ℝ) :=
                    Finset.sum_le_sum fun r hr => by exact_mod_cast (Finset.mem_range.mp hr).le
                _ = _ := by simp; ring
            unfold H d
            rw [Finset.sum_add_distrib]
            have hc : ∑ r ∈ Finset.range (blockLen B), cR * r / Real.sqrt B ≤
                cR * (blockLen B : ℝ) ^ 2 / Real.sqrt B := by
              calc _ = cR / Real.sqrt B * ∑ r ∈ Finset.range (blockLen B), (r : ℝ) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro r hr
                    ring
                _ ≤ cR / Real.sqrt B * (blockLen B : ℝ) ^ 2 :=
                    mul_le_mul_of_nonneg_left hrsum (by positivity)
                _ = _ := by ring
            have he : ∑ r ∈ Finset.range (blockLen B), qM * eM r ω =
                qM * ∑ r ∈ Finset.range (blockLen B), eM r ω := by rw [Finset.mul_sum]
            rw [he]
            linarith
          exact add_le_add hSs le_rfl
    · rw [Set.indicator_of_notMem hω]
      exact add_nonneg (hH0 ω) (Finset.sum_nonneg fun r _ =>
        Set.indicator_nonneg (fun _ _ => movement_opNorm_nonneg _) _)
  refine ⟨hXint, ?_⟩
  have hcoup := coupling_assemble_extra S t A hA
    (A.indicator (fun ω => opNorm (dynSumErr p S t ω))) hX0 hXint
    (fun ω => opNorm (dynBuf S t ω))
    (buffer_opNorm_continuous.measurable.comp (buffer_state_meas S t).2)
    (fun ω => movement_opNorm_nonneg _) G H hGint hG0 hHint hH0
    (cN * Real.log (2 * (B : ℝ)))
    (Ch * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt B)
    hGcond hHbound Lv hLv (by
    intro ω hω
    rw [Set.indicator_of_mem hω, coupling_sumErr_eq S t ω, Finset.sum_add_distrib]
    have hAin : dynDelta S t ω ∈ Aset := ⟨hω.1, hω.2.1⟩
    have hsumβ : ∑ r ∈ Finset.range (blockLen B), p.β ^ (r + 1) ≤ gb := by
      calc _ ≤ ∑ r ∈ Finset.range (blockLen B), p.β ^ r :=
            Finset.sum_le_sum fun r _ => by
              rw [pow_succ]
              exact mul_le_of_le_one_right (pow_nonneg p.hβ.1 r) p.hβ.2.le
        _ ≤ gb := by simpa [gb] using coupling_sum_pow_le p (blockLen B)
    have hV := coupling_norm_finset_sum opNorm coupling_op_props.2.1 coupling_op_props.2.2.1
      (blockLen B) (fun r => dynErrV p S t r ω)
    have hV' : opNorm (∑ r ∈ Finset.range (blockLen B), dynErrV p S t r ω) ≤
        Lv * (opNorm (dynBuf S t ω) + G ω) := by
      refine hV.trans ?_
      calc _ ≤ ∑ r ∈ Finset.range (blockLen B),
            q * p.β ^ (r + 1) * (opNorm (dynBuf S t ω) +
              opNorm (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) :=
            Finset.sum_le_sum fun r _ => coupling_V_op_linear S rlo hrlo t r ω hAin.1
        _ = q * (∑ r ∈ Finset.range (blockLen B), p.β ^ (r + 1)) *
              (opNorm (dynBuf S t ω) +
                opNorm (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) := by
            rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ q * gb * (opNorm (dynBuf S t ω) +
              opNorm (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsumβ hq)
              (add_nonneg (movement_opNorm_nonneg _) (movement_opNorm_nonneg _))
        _ = Lv * (opNorm (dynBuf S t ω) + G ω) := by
            simp [Lv, G, Set.indicator_of_mem hAin]
    have hS : opNorm (∑ r ∈ Finset.range (blockLen B), dynErrS p S t r ω) ≤ H ω := by
      refine (coupling_norm_finset_sum opNorm coupling_op_props.2.1 coupling_op_props.2.2.1
        (blockLen B) (fun r => dynErrS p S t r ω)).trans ?_
      have hterm := hSterm ω hω
      refine (Finset.sum_le_sum fun r hr => hterm r hr).trans ?_
      have hrsum : ∑ r ∈ Finset.range (blockLen B), (r : ℝ) ≤ (blockLen B : ℝ) ^ 2 := by
        calc _ ≤ ∑ _r ∈ Finset.range (blockLen B), (blockLen B : ℝ) :=
              Finset.sum_le_sum fun r hr => by exact_mod_cast (Finset.mem_range.mp hr).le
          _ = _ := by simp; ring
      unfold H d
      rw [Finset.sum_add_distrib]
      have hc : ∑ r ∈ Finset.range (blockLen B), cR * r / Real.sqrt B ≤
          cR * (blockLen B : ℝ) ^ 2 / Real.sqrt B := by
        calc _ = cR / Real.sqrt B * ∑ r ∈ Finset.range (blockLen B), (r : ℝ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r hr
              ring
          _ ≤ cR / Real.sqrt B * (blockLen B : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left hrsum (by positivity)
          _ = _ := by ring
      have he : ∑ r ∈ Finset.range (blockLen B), qM * eM r ω =
          qM * ∑ r ∈ Finset.range (blockLen B), eM r ω := by rw [Finset.mul_sum]
      rw [he]
      linarith
    have h1 := coupling_op_props.2.1 (∑ r ∈ Finset.range (blockLen B), dynErrS p S t r ω)
      (∑ r ∈ Finset.range (blockLen B), dynErrV p S t r ω)
    linarith)
  filter_upwards [hcoup] with ω hc hωA
  refine (hc hωA).trans ?_
  have hK1 : Lv * max 1 cN ≤ K := le_max_left _ _
  have hK2 : Ch ≤ K := le_max_right _ _
  have hcN1 : 1 ≤ max 1 cN := le_max_left _ _
  have hcN2 : cN ≤ max 1 cN := le_max_right _ _
  have hb0 : 0 ≤ opNorm (dynBuf S t ω) := movement_opNorm_nonneg _
  unfold K
  have hfirst : Lv * (opNorm (dynBuf S t ω) + cN * Real.log (2 * (B : ℝ))) ≤
        max (Lv * max 1 cN) Ch * (opNorm (dynBuf S t ω) + Real.log (2 * (B : ℝ))) := by
      have hleft : Lv * (opNorm (dynBuf S t ω) + cN * Real.log (2 * (B : ℝ))) ≤
          Lv * max 1 cN * (opNorm (dynBuf S t ω) + Real.log (2 * (B : ℝ))) := by
        have h1' := mul_le_mul_of_nonneg_right hcN1 hb0
        have h2' := mul_le_mul_of_nonneg_right hcN2 hlog
        nlinarith
      exact hleft.trans (mul_le_mul_of_nonneg_right hK1 (add_nonneg hb0 hlog))
  have hsecond : Ch * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt B ≤
        max (Lv * max 1 cN) Ch * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) /
          Real.sqrt B := by
      gcongr
  linarith

/-! ## `lem:app-dyn-startup` -/

private lemma startup_fro_sq_eq {m n : ℕ} (A : Mat m n) :
    fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (by positivity)]
  simp only [Real.norm_eq_abs, sq_abs]

private lemma startup_fro_sq_meas {m n : ℕ} :
    Measurable (fun A : Mat m n => fro A ^ 2) := by
  simp_rw [startup_fro_sq_eq]
  fun_prop

private lemma startup_Ahat_norm {m n : ℕ} (C : Covariances m n) (D : Mat m n)
    (hD : 0 < riskSigma C D) : fro (Ahat C D) = 1 := by
  have hsq : ∀ (c : ℝ) (K : Mat m n), fro (c • K) ^ 2 = c ^ 2 * fro K ^ 2 := by
    intro c K
    simp only [startup_fro_sq_eq, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  have hr := eqn_app_setup_whitened_risk C D
  have hs : fro (Ahat C D) ^ 2 = 1 := by
    rw [Ahat, hsq, inv_pow, Real.sq_sqrt (by linarith)]
    rw [show fro (Arot C D) ^ 2 = 2 * riskSigma C D by linarith,
      inv_mul_cancel₀ (by linarith)]
  nlinarith [movement_fro_nn (Ahat C D)]

private lemma startup_Q_meas {m n : ℕ} (ϱ : ℝ) (hϱ : 0 ≤ ϱ) :
    Measurable (fun K : Mat m n => Q ϱ K) :=
  (measurable_Q (m := m) (n := n)).comp (measurable_const.prodMk measurable_id :
    Measurable (fun K : Mat m n => ((⟨ϱ, hϱ⟩ : Set.Ici (0 : ℝ)), K)))

private lemma startup_physgrad_cont {m n B : ℕ} (C : Covariances m n) (D : Mat m n) :
    Continuous (fun b : Fin B → Vec m × Vec n =>
      batchGrad D (fun a => phys C (b a))) := by
  unfold batchGrad grad resid phys outer
  fun_prop

private lemma startup_stat_aesm {p : DynParams} {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (C : Covariances m n)
    (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n)
    (hs : ∀ᵐ ω ∂P, Summable (fun j : ℕ =>
      emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))) (k : ℕ) :
    AEStronglyMeasurable (fun ω => (def_app_dyn_chains p C cs t D M ω).stat k) P := by
  induction k with
  | zero =>
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
      ∑ j ∈ Finset.range N,
        emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))
      (fun N => ?_) ?_
    · refine (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ => ?_).aestronglyMeasurable
      exact ((startup_physgrad_cont C D).measurable.comp
        (Measurable.of_eval fun a => cs.meas_aux (t : ℤ) j a)).stronglyMeasurable.const_smul
          (emaW p.β j)
    · filter_upwards [hs] with ω hω
      exact hω.hasSum.tendsto_sum_nat
  | succ k ih =>
    exact (ih.const_smul p.β).add
      (((startup_physgrad_cont C D).measurable.comp (Measurable.of_eval fun a =>
        cs.meas_act ((t : ℤ) + k + 1) a)).stronglyMeasurable.aestronglyMeasurable.const_smul
          (1 - p.β))

private lemma startup_statV_path_aem {p : DynParams} {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (C : Covariances m n)
    (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n)
    (hD : 0 < riskSigma C D)
    (hs : ∀ᵐ ω ∂P, Summable (fun j : ℕ =>
      emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))) :
    AEMeasurable (fun ω (k : ℕ) => (def_app_dyn_chains p C cs t D M ω).statV k) P := by
  apply AEMeasurable.of_eval
  intro k
  have hρ : 0 ≤ physRidge p C D := by
    unfold physRidge
    exact mul_nonneg (by linarith) p.hϱ.le
  exact (startup_Q_meas (physRidge p C D) hρ).comp_aemeasurable
    (startup_stat_aesm C cs t D M hs k).aemeasurable

private lemma startup_Qpath_meas {m n : ℕ} (ϱ : ℝ) (hϱ : 0 ≤ ϱ) :
    Measurable (fun (x : ℤ → Mat m n) (s : ℤ) => Q ϱ (x s)) :=
  Measurable.of_eval fun s => (startup_Q_meas ϱ hϱ).comp (measurable_pi_apply s)

private lemma startup_updpath_aem {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (ϱ : ℝ) (hϱ : 0 ≤ ϱ) :
    AEMeasurable (fun ω (s : ℤ) => frozenUpd F S ϱ s ω) P :=
  (startup_Qpath_meas ϱ hϱ).comp_aemeasurable (lem_app_setup_ema_law_ii F S).2.1

private lemma startup_updpath_integral_shift {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (ϱ : ℝ) (hϱ : 0 ≤ ϱ)
    (k : ℤ) (Ψ : (ℤ → Mat m n) → ℝ) (hΨ : Measurable Ψ) :
    ∫ ω, Ψ (fun s => frozenUpd F S ϱ (s + k) ω) ∂P =
      ∫ ω, Ψ (fun s => frozenUpd F S ϱ s ω) ∂P := by
  have hA := startup_updpath_aem F S ϱ hϱ
  have hbuf := (lem_app_setup_ema_law_ii F S).2.1
  have hsh : Measurable (fun x : ℤ → Mat m n => fun s => x (s + k)) :=
    Measurable.of_eval fun s => measurable_pi_apply (s + k)
  have hB : AEMeasurable (fun ω (s : ℤ) => frozenUpd F S ϱ (s + k) ω) P :=
    hsh.comp_aemeasurable hA
  have hst := (lem_app_setup_ema_law_ii F S).2.2 k
  have hQ := startup_Qpath_meas (m := m) (n := n) ϱ hϱ
  have hmap : P.map (fun ω (s : ℤ) => frozenUpd F S ϱ (s + k) ω) =
      P.map (fun ω (s : ℤ) => frozenUpd F S ϱ s ω) := by
    have hbufk : AEMeasurable (fun ω (s : ℤ) => frozenBuf F S (s + k) ω) P :=
      hsh.comp_aemeasurable hbuf
    have c1 : (fun ω (s : ℤ) => frozenUpd F S ϱ (s + k) ω) =
        (fun x s => Q ϱ (x s)) ∘ (fun ω s => frozenBuf F S (s + k) ω) := rfl
    have c2 : (fun ω (s : ℤ) => frozenUpd F S ϱ s ω) =
        (fun x s => Q ϱ (x s)) ∘ (fun ω s => frozenBuf F S s ω) := rfl
    rw [c1, c2, ← AEMeasurable.map_map_of_aemeasurable hQ.aemeasurable hbufk,
      ← AEMeasurable.map_map_of_aemeasurable hQ.aemeasurable hbuf, hst]
  calc
    ∫ ω, Ψ (fun s => frozenUpd F S ϱ (s + k) ω) ∂P =
        ∫ x, Ψ x ∂(P.map (fun ω (s : ℤ) => frozenUpd F S ϱ (s + k) ω)) :=
      (integral_map hB hΨ.aestronglyMeasurable).symm
    _ = ∫ x, Ψ x ∂(P.map (fun ω (s : ℤ) => frozenUpd F S ϱ s ω)) := by rw [hmap]
    _ = _ := integral_map hA hΨ.aestronglyMeasurable

private lemma startup_mean_shift {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (s k : ℤ) :
    mean P (frozenUpd F S ϱ (s + k)) = mean P (frozenUpd F S ϱ s) := by
  ext i j
  simp only [mean, Matrix.of_apply]
  let Ψ : (ℤ → Mat m n) → ℝ := fun x => x s i j
  have hΨ : Measurable Ψ := (measurable_pi_apply j).comp
    ((measurable_pi_apply i).comp (measurable_pi_apply s))
  have h := startup_updpath_integral_shift F S ϱ hϱ k Ψ hΨ
  simpa [Ψ, frozenUpd] using h

private lemma startup_Icc_sum {α : Type*} [AddCommMonoid α] (g : ℤ → α) (T : ℕ) :
    ∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), g s =
      ∑ a ∈ Finset.range T, g ((a : ℤ) + 1) := by
  have hset : Finset.Icc (1 : ℤ) (T : ℤ) =
      (Finset.range T).image (fun a : ℕ => (a : ℤ) + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(x - 1).toNat, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [hset, Finset.sum_image (fun a _ b _ h => by simpa using h)]

private lemma startup_trace_fro_sq {m n : ℕ} (X : Mat m n) :
    Matrix.trace ((1 : Mat m m) * X * (1 : Mat n n) * Xᵀ) = fro X ^ 2 := by
  rw [Matrix.one_mul, Matrix.mul_one, startup_fro_sq_eq]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_two]

private lemma startup_opNorm_one (d : ℕ) : opNorm (1 : Mat d d) ≤ 1 := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp [Matrix.toEuclideanLin]

private lemma startup_abs_entry_le_fro {m n : ℕ} (A : Mat m n)
    (i : Fin m) (j : Fin n) : |A i j| ≤ fro A := by
  unfold fro
  apply Real.abs_le_sqrt
  have h1 : ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
  have h2 : ∑ j', ‖A i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  simpa [Real.norm_eq_abs, sq_abs] using h1.trans h2

private lemma startup_Q_entry_bound {m n : ℕ} (ϱ : ℝ) (hϱ : 0 ≤ ϱ)
    (K : Mat m n) (i : Fin m) (j : Fin n) : |Q ϱ K i j| ≤ (m : ℝ) + 1 := by
  obtain ⟨_, hf, hk, _⟩ := lem_app_setup_filter_i ϱ hϱ K
  have h1 := startup_abs_entry_le_fro (Q ϱ K) i j
  have hr : (K.rank : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hk.trans (min_le_left m n)
  have h2 : fro (Q ϱ K) ^ 2 ≤ (m : ℝ) := hf.trans hr
  nlinarith [movement_fro_nn (Q ϱ K), sq_nonneg (fro (Q ϱ K) - 1)]

private lemma startup_bound_of_cont {m n : ℕ} (h : Mat m n → ℝ)
    (hc : Continuous h) (R : ℝ) :
    ∃ K : ℝ, ∀ Y : Mat m n, (∀ i j, |Y i j| ≤ R) → |h Y| ≤ K := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin m =>
      Set.pi Set.univ fun _ : Fin n => Set.Icc (-R) R : Set (Mat m n)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨K, hK'⟩ := hK.exists_bound_of_continuousOn (f := h) hc.continuousOn
  refine ⟨K, fun Y hY => hK' Y ?_⟩
  intro i _ j _
  exact abs_le.mp (hY i j)

private lemma startup_integrable_cont {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → Mat m n}
    (hX : AEMeasurable X P) (R : ℝ) (hb : ∀ ω i j, |X ω i j| ≤ R)
    (h : Mat m n → ℝ) (hc : Continuous h) : Integrable (fun ω => h (X ω)) P := by
  obtain ⟨K, hK⟩ := startup_bound_of_cont h hc R
  refine Integrable.of_bound (C := K)
    (hc.measurable.comp_aemeasurable hX).aestronglyMeasurable ?_
  exact ae_of_all _ fun ω => by simpa using hK (X ω) (hb ω)

private lemma startup_statV_fro_sq_le {p : DynParams} {m n B : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n)
    (hsize : SizeFin C B p.γstar p.CSig) (hD : 0 < riskSigma C D) (r : ℕ) (ω : Ω) :
    fro (stationaryV p C cs t D r ω) ^ 2 ≤ p.γstar * B := by
  have hρ : 0 ≤ physRidge p C D := by
    unfold physRidge
    exact mul_nonneg (mul_nonneg (by norm_num) hD.le) p.hϱ.le
  have hQ := (lem_app_setup_filter_i (physRidge p C D) hρ
    ((def_app_dyn_chains p C cs t D 0 ω).stat (r + 1))).2.1
  have hrank : (((def_app_dyn_chains p C cs t D 0 ω).stat (r + 1)).rank : ℝ) ≤
      ((max m n : ℕ) : ℝ) := by
    exact_mod_cast ((Matrix.rank_le_height _).trans (le_max_left m n))
  unfold stationaryV
  exact hQ.trans (hrank.trans hsize.1)

private lemma startup_error_fro_le {p : DynParams} {m n B : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M0 : Mat m n)
    (rlo : ℝ) (hrlo : 0 < rlo) (hD : rlo ≤ riskSigma C D) (r : ℕ) (ω : Ω) :
    fro ((def_app_dyn_chains p C cs t D M0 ω).sameV (r + 1) -
        (def_app_dyn_chains p C cs t D M0 ω).statV (r + 1)) ≤
      (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * p.β ^ (r + 1) *
        (fro M0 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0)) := by
  have hϱlo : 0 < rlo * p.ϱ := mul_pos hrlo p.hϱ
  have hρlo : rlo * p.ϱ ≤ physRidge p C D := by
    unfold physRidge
    nlinarith
  have hρ : 0 < physRidge p C D := lt_of_lt_of_le hϱlo hρlo
  have hlip := lem_app_setup_filter_iii (physRidge p C D) hρ
    ((def_app_dyn_chains p C cs t D M0 ω).same (r + 1))
    ((def_app_dyn_chains p C cs t D M0 ω).stat (r + 1))
  have hdiff := lem_app_dyn_chains_ii p C cs t D M0 ω (r + 1)
  rw [hdiff] at hlip
  have hsmul := (coupling_fro_props (m := m) (n := n)).1 (p.β ^ (r + 1))
    (M0 - (def_app_dyn_chains p C cs t D M0 ω).stat 0) (pow_nonneg p.hβ.1 _)
  rw [hsmul] at hlip
  refine hlip.trans ?_
  have hpow : 0 ≤ p.β ^ (r + 1) := pow_nonneg p.hβ.1 _
  have hsub := coupling_fro_sub_le M0 ((def_app_dyn_chains p C cs t D M0 ω).stat 0)
  have hrpow := Real.rpow_le_rpow_of_nonpos hϱlo hρlo (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
  calc
    (physRidge p C D) ^ (-(1 / 2 : ℝ)) *
          (p.β ^ (r + 1) * fro (M0 - (def_app_dyn_chains p C cs t D M0 ω).stat 0))
        ≤ (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) *
          (p.β ^ (r + 1) * fro (M0 - (def_app_dyn_chains p C cs t D M0 ω).stat 0)) :=
      mul_le_mul_of_nonneg_right hrpow
        (mul_nonneg hpow (movement_fro_nn _))
    _ ≤ (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * p.β ^ (r + 1) *
          (fro M0 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0)) := by
      have hq : 0 ≤ (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hϱlo.le _
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsub hpow) hq)

private lemma startup_error_sum_fro_le {p : DynParams} {m n B : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M0 : Mat m n)
    (rlo : ℝ) (hrlo : 0 < rlo) (hD : rlo ≤ riskSigma C D) (L : ℕ) (ω : Ω) :
    fro (∑ r ∈ Finset.range L,
        ((def_app_dyn_chains p C cs t D M0 ω).sameV (r + 1) -
          (def_app_dyn_chains p C cs t D M0 ω).statV (r + 1))) ≤
      (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * (p.β / (1 - p.β)) *
        (fro M0 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0)) := by
  have hsum := coupling_norm_finset_sum fro coupling_fro_props.2.1
    coupling_fro_props.2.2.1 L (fun r =>
      (def_app_dyn_chains p C cs t D M0 ω).sameV (r + 1) -
        (def_app_dyn_chains p C cs t D M0 ω).statV (r + 1))
  refine hsum.trans ?_
  calc
    _ ≤ ∑ r ∈ Finset.range L,
        (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * p.β ^ (r + 1) *
          (fro M0 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0)) :=
      Finset.sum_le_sum fun r _ => startup_error_fro_le C cs t D M0 rlo hrlo hD r ω
    _ = (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) *
        (∑ r ∈ Finset.range L, p.β ^ (r + 1)) *
          (fro M0 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * (p.β / (1 - p.β)) *
          (fro M0 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0)) := by
      have hgeom : ∑ r ∈ Finset.range L, p.β ^ (r + 1) ≤ p.β / (1 - p.β) := by
        calc
          _ = p.β * ∑ r ∈ Finset.range L, p.β ^ r := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r _
            rw [pow_succ]
            exact mul_comm _ _
          _ ≤ p.β * (1 - p.β)⁻¹ :=
            mul_le_mul_of_nonneg_left (coupling_sum_pow_le p L) p.hβ.1
          _ = p.β / (1 - p.β) := by rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgeom (Real.rpow_nonneg (mul_pos hrlo p.hϱ).le _))
        (add_nonneg (movement_fro_nn _) (movement_fro_nn _))

private lemma startup_same_aesm {p : DynParams} {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (C : Covariances m n)
    (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n) (k : ℕ) :
    AEStronglyMeasurable (fun ω => (def_app_dyn_chains p C cs t D M ω).same k) P := by
  induction k with
  | zero => exact aestronglyMeasurable_const
  | succ k ih =>
    exact (ih.const_smul p.β).add
      (((startup_physgrad_cont C D).measurable.comp (Measurable.of_eval fun a =>
        cs.meas_act ((t : ℤ) + k + 1) a)).stronglyMeasurable.aestronglyMeasurable.const_smul
          (1 - p.β))

private lemma startup_sameV_path_aem {p : DynParams} {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (C : Covariances m n)
    (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n) (hD : 0 < riskSigma C D) :
    AEMeasurable (fun ω (k : ℕ) => (def_app_dyn_chains p C cs t D M ω).sameV k) P := by
  apply AEMeasurable.of_eval
  intro k
  have hρ : 0 ≤ physRidge p C D := by
    unfold physRidge
    exact mul_nonneg (by linarith) p.hϱ.le
  exact (startup_Q_meas (physRidge p C D) hρ).comp_aemeasurable
    (startup_same_aesm C cs t D M k).aemeasurable

private lemma startup_error_sum_fro_sq_bound {p : DynParams} {m n B : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M0 : Mat m n)
    (rlo rhi : ℝ) (hrlo : 0 < rlo) (hDlo : rlo ≤ riskSigma C D)
    (hDhi : riskSigma C D ≤ rhi) (hsize : SizeFin C B p.γstar p.CSig) (L : ℕ) :
    let A : Ω → Mat m n := fun ω => ∑ r ∈ Finset.range L,
      ((def_app_dyn_chains p C cs t D M0 ω).sameV (r + 1) -
        (def_app_dyn_chains p C cs t D M0 ω).statV (r + 1))
    let q := (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * (p.β / (1 - p.β))
    Integrable (fun ω => fro (A ω) ^ 2) P ∧
      ∫ ω, fro (A ω) ^ 2 ∂P ≤
        2 * q ^ 2 * (fro M0 ^ 2 + 2 * rhi * cMConst p.CSig p.γstar * B) := by
  dsimp only
  let q := (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * (p.β / (1 - p.β))
  let A : Ω → Mat m n := fun ω => ∑ r ∈ Finset.range L,
    ((def_app_dyn_chains p C cs t D M0 ω).sameV (r + 1) -
      (def_app_dyn_chains p C cs t D M0 ω).statV (r + 1))
  have hD : 0 < riskSigma C D := hrlo.trans_le hDlo
  obtain ⟨hsum, hNint, hNbd⟩ := lem_app_dyn_chains_iii p C cs t D M0 hD hsize
  have hstat := startup_statV_path_aem C cs t D M0 hD hsum
  have hsame := startup_sameV_path_aem (p := p) C cs t D M0 hD
  have hAae : AEMeasurable A P := by
    exact Finset.aemeasurable_fun_sum _ fun r _ =>
      ((measurable_pi_apply (r + 1)).comp_aemeasurable hsame).sub
        ((measurable_pi_apply (r + 1)).comp_aemeasurable hstat)
  have hq : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg (Real.rpow_nonneg (mul_pos hrlo p.hϱ).le _)
      (div_nonneg p.hβ.1 (sub_nonneg.mpr p.hβ.2.le))
  have hpt : ∀ ω, fro (A ω) ^ 2 ≤ 2 * q ^ 2 *
      (fro M0 ^ 2 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0) ^ 2) := by
    intro ω
    have ha := startup_error_sum_fro_le (p := p) C cs t D M0 rlo hrlo hDlo L ω
    change fro (A ω) ≤ q *
      (fro M0 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0)) at ha
    have hsquare := pow_le_pow_left₀ (movement_fro_nn (A ω)) ha 2
    have hsum2 : (fro M0 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0)) ^ 2 ≤
        2 * (fro M0 ^ 2 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0) ^ 2) := by
      nlinarith [sq_nonneg (fro M0 - fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0))]
    rw [mul_pow] at hsquare
    refine hsquare.trans ?_
    convert mul_le_mul_of_nonneg_left hsum2 (sq_nonneg q) using 1 <;> ring
  have hgint : Integrable (fun ω => 2 * q ^ 2 *
      (fro M0 ^ 2 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0) ^ 2)) P :=
    ((integrable_const (μ := P) (fro M0 ^ 2)).add hNint).const_mul (2 * q ^ 2)
  have hAint : Integrable (fun ω => fro (A ω) ^ 2) P := by
    refine hgint.mono' (startup_fro_sq_meas.comp_aemeasurable hAae).aestronglyMeasurable ?_
    exact ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpt ω
  refine ⟨hAint, (integral_mono hAint hgint (fun ω => hpt ω)).trans ?_⟩
  rw [integral_const_mul, integral_add (integrable_const _) hNint, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, one_mul]
  have hcM : 0 ≤ cMConst p.CSig p.γstar := by
    unfold cMConst
    positivity
  have hNB : ∫ ω, fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0) ^ 2 ∂P ≤
      2 * rhi * cMConst p.CSig p.γstar * B := by
    refine hNbd.trans ?_
    calc
      2 * riskSigma C D * cMConst p.CSig p.γstar * B =
          riskSigma C D * (2 * cMConst p.CSig p.γstar * B) := by ring
      _ ≤ rhi * (2 * cMConst p.CSig p.γstar * B) :=
        mul_le_mul_of_nonneg_right hDhi (by positivity)
      _ = 2 * rhi * cMConst p.CSig p.γstar * B := by ring
  have hadd : fro M0 ^ 2 +
      ∫ ω, fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0) ^ 2 ∂P ≤
      fro M0 ^ 2 + 2 * rhi * cMConst p.CSig p.γstar * B := by linarith
  exact mul_le_mul_of_nonneg_left hadd (mul_nonneg (by norm_num) (sq_nonneg q))

/-- `lem:app-dyn-startup`, snapshot `cr-2026-10-23`, part (i). Deterministic `D` with
`r₋ ≤ 𝓡(D) ≤ r₊`, `0 < r₋ ≤ r₊`; the chains at `(t, D, M)` of `def:app-dyn-chains`. The stationary
block sum against `L·V̄(D)`, with `V̄(D) = 𝔼V_0` (`Muon.mean`). `SizeFin` is the finite-dimensional
(H1). Constant `K` depends on the fixed parameters and `(r₋, r₊)` only. Statement verbatim from
`section.tex` (ll. 1614–1623):
```latex
\begin{lemma}[Stationary block sums and the startup cross term]\label{lem:app-dyn-startup}
Let $D$, $m$ be deterministic with $r_-\le\cR(D)\le r_+$, consider the chains
at $(t,D,m)$, and put $S\defeq\sum_{r<L}V_r$, $A\defeq\sum_{r<L}(\widehat V_r-V_r)$ and
$a\defeq1+\norm m_\F/\sqrt B$. Then
\begin{enumerate}[label=(\roman*)]
\item $\EE\norm{S-L\overline V(D)}_\F^2\le CBL$;
\item for every linear map $\mathcal W$ on $\R^{\Nout\times\Nin}$ of Frobenius norm at
most one, $\abs{\EE\langle S,\mathcal WA\rangle}\le Ca\big(B+L\sqrt B\big)$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_dyn_startup_i (p : DynParams) (rlo rhi : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ K : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M0 : Mat m n),
      SizeFin C B p.γstar p.CSig → rlo ≤ riskSigma C D → riskSigma C D ≤ rhi →
      Integrable (fun ω => fro (∑ r ∈ Finset.range (blockLen B), stationaryV p C cs t D r ω -
        (blockLen B : ℝ) • mean P (fun ω' => stationaryV p C cs t D 0 ω')) ^ 2) P ∧
      ∫ ω, fro (∑ r ∈ Finset.range (blockLen B), stationaryV p C cs t D r ω -
        (blockLen B : ℝ) • mean P (fun ω' => stationaryV p C cs t D 0 ω')) ^ 2 ∂P ≤
          K * B * blockLen B := by
  let K0 := kStar p.CSig p.γstar p.ϱ
  refine ⟨p.γstar + 2 * K0 * p.β / (1 - p.β), ?_⟩
  intro Ω _ P _ m n B C cs t D M0 hsize hDlo hDhi
  have hD : 0 < riskSigma C D := hrlo.trans_le hDlo
  have hB : 0 < B := by
    by_contra hb
    have hb0 : B = 0 := by omega
    have hmax : max m n = 0 := by
      have hh := hsize.1
      simp only [hb0, Nat.cast_zero, mul_zero, Nat.cast_nonpos] at hh
      exact hh
    have hm0 : m = 0 := by omega
    have hr := eqn_app_setup_whitened_risk C D
    simp [hm0, fro] at hr
    linarith
  have hL : 0 < blockLen B := by
    unfold blockLen
    apply Nat.floor_pos.mpr
    exact Real.one_le_rpow (by exact_mod_cast hB) (by norm_num)
  let F : FrozenParams m n B :=
    ⟨C, Ahat C D, startup_Ahat_norm C D hD, p.β, p.hβ, hB⟩
  let S : FrozenSamples P m n B :=
    ⟨cs.act, cs.meas_act, cs.indep.precomp Sum.inl_injective, cs.law_act⟩
  have hlaw := lem_app_dyn_chains_i p C cs t D 0 hD F rfl rfl rfl S
  have hXp := startup_statV_path_aem C cs t D 0 hD hlaw.1
  have hYp : AEMeasurable (fun ω (k : ℕ) =>
      frozenUpd F S p.ϱ ((t : ℤ) + (k : ℤ) - 1) ω) P := by
    have heval : Measurable (fun (x : ℤ → Mat m n) (k : ℕ) =>
        x ((t : ℤ) + (k : ℤ) - 1)) := Measurable.of_eval fun k => measurable_pi_apply _
    exact heval.comp_aemeasurable (startup_updpath_aem F S p.ϱ p.hϱ.le)
  let μ : Mat m n := mean P (fun ω => stationaryV p C cs t D 0 ω)
  let X : Ω → Mat m n := fun ω =>
    ∑ r ∈ Finset.range (blockLen B), stationaryV p C cs t D r ω -
      (blockLen B : ℝ) • μ
  let Ψ : (ℕ → Mat m n) → ℝ := fun x =>
    fro (∑ r ∈ Finset.range (blockLen B), x (r + 1) - (blockLen B : ℝ) • μ) ^ 2
  have hΨ : Measurable Ψ := startup_fro_sq_meas.comp
    ((Finset.measurable_sum _ fun r _ => measurable_pi_apply (r + 1)).sub measurable_const)
  have hXae : AEMeasurable X P := by
    have hm : Measurable (fun x : ℕ → Mat m n =>
        ∑ r ∈ Finset.range (blockLen B), x (r + 1) - (blockLen B : ℝ) • μ) :=
      (Finset.measurable_sum _ fun r _ => measurable_pi_apply (r + 1)).sub measurable_const
    exact hm.comp_aemeasurable hXp
  have hρ : 0 ≤ physRidge p C D := by
    unfold physRidge
    exact mul_nonneg (mul_nonneg (by norm_num) hD.le) p.hϱ.le
  have hμentry : ∀ i j, |μ i j| ≤ (m : ℝ) + 1 := by
    intro i j
    have hbnd : ∀ ω, |stationaryV p C cs t D 0 ω i j| ≤ (m : ℝ) + 1 := by
      intro ω
      exact startup_Q_entry_bound (physRidge p C D) hρ
        ((def_app_dyn_chains p C cs t D 0 ω).stat 1) i j
    have hi := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => stationaryV p C cs t D 0 ω i j) (C := (m : ℝ) + 1)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hbnd ω)
    simpa [μ, mean] using hi
  have hXentry : ∀ ω i j,
      |X ω i j| ≤ 2 * (blockLen B : ℝ) * ((m : ℝ) + 1) := by
    intro ω i j
    have hterm : ∀ r, |stationaryV p C cs t D r ω i j| ≤ (m : ℝ) + 1 := by
      intro r
      exact startup_Q_entry_bound (physRidge p C D) hρ
        ((def_app_dyn_chains p C cs t D 0 ω).stat (r + 1)) i j
    have hsum : |∑ r ∈ Finset.range (blockLen B), stationaryV p C cs t D r ω i j| ≤
        (blockLen B : ℝ) * ((m : ℝ) + 1) := by
      calc
        |∑ r ∈ Finset.range (blockLen B), stationaryV p C cs t D r ω i j| ≤
            ∑ r ∈ Finset.range (blockLen B),
              |stationaryV p C cs t D r ω i j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _r ∈ Finset.range (blockLen B), ((m : ℝ) + 1) :=
          Finset.sum_le_sum fun r _ => hterm r
        _ = _ := by simp; ring
    have hscale : |(blockLen B : ℝ) * μ i j| ≤
        (blockLen B : ℝ) * ((m : ℝ) + 1) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hμentry i j) (Nat.cast_nonneg _)
    change |(∑ r ∈ Finset.range (blockLen B), stationaryV p C cs t D r ω) i j -
      ((blockLen B : ℝ) • μ) i j| ≤ _
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact (abs_sub _ _).trans (by linarith)
  have hint : Integrable (fun ω => fro (X ω) ^ 2) P :=
    startup_integrable_cont hXae _ hXentry _ (by
      exact (show Continuous (fun A : Mat m n => fro A) by
        unfold fro
        fun_prop).pow 2)
  have htransfer : ∫ ω, fro (X ω) ^ 2 ∂P =
      ∫ ω, fro (∑ r ∈ Finset.range (blockLen B),
        frozenUpd F S p.ϱ ((t : ℤ) + r) ω - (blockLen B : ℝ) • μ) ^ 2 ∂P := by
    have e1 := integral_map hXp hΨ.aestronglyMeasurable
    have e2 := integral_map hYp hΨ.aestronglyMeasurable
    rw [hlaw.2.2.1] at e1
    have e3 := e1.symm.trans e2
    have he : ∀ r : ℕ, (t : ℤ) + ((r + 1 : ℕ) : ℤ) - 1 = (t : ℤ) + r := by
      intro r; push_cast; ring
    simpa only [X, Ψ, stationaryV, he] using e3
  have hmean : μ = mean P (frozenUpd F S p.ϱ (t : ℤ)) := by
    exact hlaw.2.2.2.2
  have hmean1 : μ = mean P (frozenUpd F S p.ϱ 1) := by
    rw [hmean]
    have hs := startup_mean_shift F S p.hϱ.le 1 ((t : ℤ) - 1)
    simpa using hs
  let Ψ0 : (ℤ → Mat m n) → ℝ := fun x =>
    fro (∑ r ∈ Finset.range (blockLen B), x ((r : ℤ) + 1) -
      (blockLen B : ℝ) • mean P (frozenUpd F S p.ϱ 1)) ^ 2
  have hΨ0 : Measurable Ψ0 := by
    have hs : Measurable (fun x : ℤ → Mat m n =>
        ∑ r ∈ Finset.range (blockLen B), x ((r : ℤ) + 1)) :=
      Finset.measurable_sum _ fun r _ => measurable_pi_apply ((r : ℤ) + 1)
    exact startup_fro_sq_meas.comp (hs.sub measurable_const)
  have hshift := startup_updpath_integral_shift F S p.ϱ p.hϱ.le ((t : ℤ) - 1) Ψ0 hΨ0
  have hcanon : ∫ ω, fro (X ω) ^ 2 ∂P =
      ∫ ω, fro (∑ s ∈ Finset.Icc (1 : ℤ) (blockLen B : ℤ),
        centredUpd F S p.ϱ s ω) ^ 2 ∂P := by
    rw [htransfer]
    calc
      _ = ∫ ω, Ψ0 (fun s => frozenUpd F S p.ϱ (s + ((t : ℤ) - 1)) ω) ∂P := by
        apply integral_congr_ae
        exact ae_of_all _ fun ω => by
          simp only [Ψ0, hmean1]
          apply congrArg (fun Z : Mat m n => fro Z ^ 2)
          congr 1
          apply Finset.sum_congr rfl
          intro r _
          push_cast
          ring_nf
      _ = ∫ ω, Ψ0 (fun s => frozenUpd F S p.ϱ s ω) ∂P := hshift
      _ = _ := by
        apply integral_congr_ae
        exact ae_of_all _ fun ω => by
          simp only [Ψ0, centredUpd]
          congr 2
          rw [startup_Icc_sum]
          have heq : (∑ r ∈ Finset.range (blockLen B),
              (frozenUpd F S p.ϱ ((r : ℤ) + 1) ω -
                mean P (frozenUpd F S p.ϱ ((r : ℤ) + 1)))) =
              ∑ r ∈ Finset.range (blockLen B),
                (frozenUpd F S p.ϱ ((r : ℤ) + 1) ω -
                  mean P (frozenUpd F S p.ϱ 1)) := by
            apply Finset.sum_congr rfl
            intro r _
            have hm := startup_mean_shift F S p.hϱ.le 1 (r : ℤ)
            rw [show (r : ℤ) + 1 = 1 + (r : ℤ) by ring, hm]
          rw [heq, Finset.sum_sub_distrib]
          ext i j
          simp [Matrix.smul_apply]
  have hfinite : ∫ ω, fro (X ω) ^ 2 ∂P =
      (B : ℝ) * (blockLen B : ℝ) *
        finiteTimeCov F S (blockLen B) p.ϱ p.ϱ (1 : Mat m m) (1 : Mat n n) := by
    rw [hcanon]
    unfold finiteTimeCov
    simp_rw [startup_trace_fro_sq]
    field_simp
  have hlag := thm_app_vol_lag_reduction_ii_actual F S p.γstar p.CSig
    p.ϱ p.ϱ hsize p.hC ⟨p.hϱ, le_rfl⟩
    (1 : Mat m m) (1 : Mat n n) (by simp) (by simp)
    (startup_opNorm_one m) (startup_opNorm_one n) p.ϱ p.ϱ
    ⟨le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl⟩ 0
  have hfi := thm_app_vol_lag_reduction_i F S p.γstar p.CSig
    p.ϱ p.ϱ hsize p.hC ⟨p.hϱ, le_rfl⟩
    (1 : Mat m m) (1 : Mat n n) (by simp) (by simp)
    (startup_opNorm_one m) (startup_opNorm_one n) p.ϱ p.ϱ
    ⟨le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl⟩
    (blockLen B) hL 0
  have hK0 : 0 ≤ K0 := by
    have hp : 0 ≤ 2 * p.γstar * (p.γstar ^ 2 + 4 * p.γstar + 3) / p.ϱ := by
      have hpoly : 0 ≤ p.γstar ^ 2 + 4 * p.γstar + 3 := by
        nlinarith [sq_nonneg p.γstar, p.hγ]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hγ) hpoly) p.hϱ.le
    change 0 ≤ p.CSig * Real.sqrt
      (2 * p.γstar * (p.γstar ^ 2 + 4 * p.γstar + 3) / p.ϱ)
    exact mul_nonneg (le_trans zero_le_one p.hC) (Real.sqrt_nonneg _)
  have hcov : finiteTimeCov F S (blockLen B) p.ϱ p.ϱ (1 : Mat m m) (1 : Mat n n) ≤
      p.γstar + 2 * K0 * p.β / (1 - p.β) := by
    rw [hfi]
    let g : ℕ → ℝ := fun ℓ =>
      (1 - (ℓ : ℝ) / (blockLen B : ℝ)) *
        (def_app_vol_lag F S ℓ 0 (1 : Mat m m) (1 : Mat n n) p.ϱ p.ϱ +
         def_app_vol_lag F S ℓ 0 (1 : Mat m m) (1 : Mat n n) p.ϱ p.ϱ)
    have hterms : ∀ ℓ : ℕ, ℓ ∈ (Finset.Ico 1 (blockLen B)) →
        |g ℓ| ≤ 2 * K0 * p.β ^ ℓ := by
      intro ℓ hℓ
      have hℓ' := Finset.mem_Ico.mp hℓ
      have hw0 : 0 ≤ 1 - (ℓ : ℝ) / (blockLen B : ℝ) :=
        sub_nonneg.mpr ((div_le_one (by positivity)).mpr (by exact_mod_cast hℓ'.2.le))
      have hw : |1 - (ℓ : ℝ) / (blockLen B : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg hw0]
        exact sub_le_self _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      dsimp only [g]
      rw [abs_mul]
      calc
        _ ≤ 1 * |def_app_vol_lag F S ℓ 0 (1 : Mat m m) (1 : Mat n n) p.ϱ p.ϱ +
            def_app_vol_lag F S ℓ 0 (1 : Mat m m) (1 : Mat n n) p.ϱ p.ϱ| :=
          mul_le_mul hw le_rfl (abs_nonneg _) zero_le_one
        _ ≤ 2 * (K0 * p.β ^ ℓ) := by
          rw [one_mul]
          exact (abs_add_le _ _).trans (by
            have hh := hlag.2 ℓ hℓ'.1
            change |def_app_vol_lag F S ℓ 0 (1 : Mat m m) (1 : Mat n n) p.ϱ p.ϱ| ≤
              K0 * p.β ^ ℓ at hh
            linarith)
        _ = _ := by ring
    calc
      _ ≤ |def_app_vol_lag F S 0 0 (1 : Mat m m) (1 : Mat n n) p.ϱ p.ϱ| +
          ∑ ℓ ∈ Finset.Ico 1 (blockLen B), |g ℓ| := by
        refine (le_abs_self _).trans ((abs_add_le _ _).trans ?_)
        have hs := Finset.abs_sum_le_sum_abs g (Finset.Ico 1 (blockLen B))
        linarith
      _ ≤ p.γstar + ∑ ℓ ∈ Finset.Ico 1 (blockLen B), 2 * K0 * p.β ^ ℓ :=
        add_le_add hlag.1 (Finset.sum_le_sum hterms)
      _ ≤ p.γstar + 2 * K0 * (p.β / (1 - p.β)) := by
        gcongr
        obtain ⟨T', hT'⟩ : ∃ T', blockLen B = T' + 1 :=
          ⟨blockLen B - 1, by omega⟩
        have heq : ∑ ℓ ∈ Finset.Ico 1 (blockLen B), 2 * K0 * p.β ^ ℓ =
            2 * K0 * (p.β * ∑ r ∈ Finset.range T', p.β ^ r) := by
          rw [hT', Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel, Finset.mul_sum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          rw [add_comm 1 r, pow_succ]
          ring
        calc
          ∑ ℓ ∈ Finset.Ico 1 (blockLen B), 2 * K0 * p.β ^ ℓ ≤
              2 * K0 * (p.β * ∑ r ∈ Finset.range T', p.β ^ r) := heq.le
          _ ≤ 2 * K0 * (p.β * (1 - p.β)⁻¹) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (coupling_sum_pow_le p T') p.hβ.1)
              (mul_nonneg (by norm_num) hK0)
          _ = 2 * K0 * (p.β / (1 - p.β)) := by rw [div_eq_mul_inv]
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  · simpa only [X, μ] using hint
  · rw [hfinite]
    convert mul_le_mul_of_nonneg_left hcov
      (mul_nonneg (Nat.cast_nonneg B) (Nat.cast_nonneg (blockLen B))) using 1 <;> ring

private lemma startup_integral_mul_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f g : Ω → ℝ) (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P)
    (hf2 : Integrable (fun ω => f ω ^ 2) P) (hg2 : Integrable (fun ω => g ω ^ 2) P)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) :
    ∫ ω, f ω * g ω ∂P ≤
      Real.sqrt (∫ ω, f ω ^ 2 ∂P) * Real.sqrt (∫ ω, g ω ^ 2 ∂P) := by
  have hfp : MemLp f 2 P := (memLp_two_iff_integrable_sq hf).2 hf2
  have hgp : MemLp g 2 P := (memLp_two_iff_integrable_sq hg).2 hg2
  have hfp' : MemLp f (ENNReal.ofReal (2 : ℝ)) P := by simpa using hfp
  have hgp' : MemLp g (ENNReal.ofReal (2 : ℝ)) P := by simpa using hgp
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := f) (g := g) (ae_of_all _ hf0) (ae_of_all _ hg0) hfp' hgp'
  simpa only [one_div, Real.sqrt_eq_rpow, Real.rpow_two] using h

private lemma startup_fro_mean_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n : ℕ} (X : Ω → Mat m n)
    (hX : AEStronglyMeasurable X P) (hX2 : Integrable (fun ω => fro (X ω) ^ 2) P) :
    fro (mean P X) ≤ Real.sqrt (∫ ω, fro (X ω) ^ 2 ∂P) := by
  have heq : fro (mean P X) ^ 2 = ∑ i, ∑ j, (∫ ω, X ω i j ∂P) ^ 2 := by
    rw [startup_fro_sq_eq]
    simp only [mean, Matrix.of_apply]
  have hi2 : ∀ i j, Integrable (fun ω => (X ω i j) ^ 2) P := by
    intro i j
    have hm : AEStronglyMeasurable (fun ω => X ω i j) P :=
      ((measurable_pi_apply j).comp_aemeasurable
        ((measurable_pi_apply i).comp_aemeasurable hX.aemeasurable)).aestronglyMeasurable
    refine hX2.mono' (hm.pow 2) (ae_of_all _ fun ω => ?_)
    change |(X ω i j) ^ 2| ≤ fro (X ω) ^ 2
    rw [abs_of_nonneg (sq_nonneg _)]
    have ht := pow_le_pow_left₀ (abs_nonneg _) (startup_abs_entry_le_fro (X ω) i j) 2
    simpa only [sq_abs] using ht
  have hentry : ∀ i j, (∫ ω, X ω i j ∂P) ^ 2 ≤ ∫ ω, (X ω i j) ^ 2 ∂P := by
    intro i j
    have hm : AEStronglyMeasurable (fun ω => X ω i j) P :=
      ((measurable_pi_apply j).comp_aemeasurable
        ((measurable_pi_apply i).comp_aemeasurable hX.aemeasurable)).aestronglyMeasurable
    have habs2 : Integrable (fun ω => |X ω i j| ^ 2) P := by
      simpa only [sq_abs] using hi2 i j
    have hcs := startup_integral_mul_le_sqrt (fun ω => |X ω i j|) (fun _ => (1 : ℝ))
      hm.norm aestronglyMeasurable_const habs2
      (by simpa using (integrable_const (μ := P) (1 : ℝ)))
      (fun _ => abs_nonneg _) (fun _ => zero_le_one)
    have ha : |∫ ω, X ω i j ∂P| ≤ Real.sqrt (∫ ω, (X ω i j) ^ 2 ∂P) :=
      (norm_integral_le_of_norm_le (f := fun ω => X ω i j) (g := fun ω => |X ω i j|)
        ((memLp_two_iff_integrable_sq hm.norm).2 habs2 |>.integrable one_le_two)
        (ae_of_all _ fun ω => le_rfl)).trans (by
          simpa only [mul_one, one_pow, sq_abs, integral_const, measureReal_def,
            measure_univ, ENNReal.toReal_one, one_smul, Real.sqrt_one] using hcs)
    have hs0 : 0 ≤ ∫ ω, (X ω i j) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
    calc
      (∫ ω, X ω i j ∂P) ^ 2 = |∫ ω, X ω i j ∂P| ^ 2 := (sq_abs _).symm
      _ ≤ Real.sqrt (∫ ω, (X ω i j) ^ 2 ∂P) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) ha 2
      _ = _ := Real.sq_sqrt hs0
  have hsum : fro (mean P X) ^ 2 ≤ ∫ ω, fro (X ω) ^ 2 ∂P := by
    rw [heq]
    calc
      _ ≤ ∑ i, ∑ j, ∫ ω, (X ω i j) ^ 2 ∂P := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hentry i j
      _ = ∫ ω, ∑ i, ∑ j, (X ω i j) ^ 2 ∂P := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro i _
          rw [integral_finsetSum]
          intro j _
          exact hi2 i j
        · intro i _
          exact integrable_finsetSum _ fun j _ => hi2 i j
      _ = _ := by simp_rw [← startup_fro_sq_eq]
  exact Real.le_sqrt_of_sq_le hsum

private lemma startup_frobIP_eq_sum {m n : ℕ} (X Y : Mat m n) :
    frobIP X Y = ∑ i, ∑ j, X i j * Y i j := by
  simp only [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]

private lemma startup_frobIP_le {m n : ℕ} (X Y : Mat m n) :
    |frobIP X Y| ≤ fro X * fro Y := by
  have htr : frobIP X Y = ∑ x : Fin m × Fin n, X x.1 x.2 * Y x.1 x.2 := by
    simp [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [htr]
  calc
    |∑ x : Fin m × Fin n, X x.1 x.2 * Y x.1 x.2| ≤
        ∑ x : Fin m × Fin n, |X x.1 x.2| * |Y x.1 x.2| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun x : Fin m × Fin n => X x.1 x.2 * Y x.1 x.2) Finset.univ
    _ ≤ _ := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m × Fin n))
        (fun x => |X x.1 x.2|) (fun x => |Y x.1 x.2|)
      simpa [fro, Fintype.sum_prod_type, Real.norm_eq_abs] using h

private lemma startup_frobIP_cont {m n : ℕ} :
    Continuous (fun x : Mat m n × Mat m n => frobIP x.1 x.2) := by
  simp_rw [startup_frobIP_eq_sum]
  fun_prop

private lemma startup_ip_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n : ℕ} (X Y : Ω → Mat m n) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hX2 : Integrable (fun ω => fro (X ω) ^ 2) P)
    (hY2 : Integrable (fun ω => fro (Y ω) ^ 2) P) :
    Integrable (fun ω => frobIP (X ω) (Y ω)) P := by
  refine ((hX2.add hY2).div_const 2).mono'
    ((startup_frobIP_cont.measurable.comp_aemeasurable (hX.prodMk hY)).aestronglyMeasurable) ?_
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]
    change |frobIP (X ω) (Y ω)| ≤ (fro (X ω) ^ 2 + fro (Y ω) ^ 2) / 2
    refine (startup_frobIP_le _ _).trans ?_
    nlinarith [sq_nonneg (fro (X ω) - fro (Y ω))]

private lemma startup_centered_fro_sq_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n : ℕ} (X : Ω → Mat m n)
    (hX : AEMeasurable X P) (hX2 : Integrable (fun ω => fro (X ω) ^ 2) P) :
    Integrable (fun ω => fro (X ω - mean P X) ^ 2) P := by
  have hm : AEMeasurable (fun ω => X ω - mean P X) P := hX.sub aemeasurable_const
  have hmean := startup_fro_mean_le_sqrt X hX.aestronglyMeasurable hX2
  have hI0 : 0 ≤ ∫ ω, fro (X ω) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
  have hm2 : fro (mean P X) ^ 2 ≤ ∫ ω, fro (X ω) ^ 2 ∂P := by
    calc
      fro (mean P X) ^ 2 ≤ Real.sqrt (∫ ω, fro (X ω) ^ 2 ∂P) ^ 2 :=
        pow_le_pow_left₀ (movement_fro_nn _) hmean 2
      _ = _ := Real.sq_sqrt hI0
  have hmajor : Integrable (fun ω => 2 *
      (fro (X ω) ^ 2 + ∫ ω, fro (X ω) ^ 2 ∂P)) P :=
    (hX2.add (integrable_const _)).const_mul 2
  refine hmajor.mono'
    (startup_fro_sq_meas.comp_aemeasurable hm).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hsub := coupling_fro_sub_le (X ω) (mean P X)
  have hs := pow_le_pow_left₀ (movement_fro_nn _) hsub 2
  calc
    fro (X ω - mean P X) ^ 2 ≤ (fro (X ω) + fro (mean P X)) ^ 2 := hs
    _ ≤ 2 * (fro (X ω) ^ 2 + fro (mean P X) ^ 2) := by
      nlinarith [sq_nonneg (fro (X ω) - fro (mean P X))]
    _ ≤ 2 * (fro (X ω) ^ 2 + ∫ ω, fro (X ω) ^ 2 ∂P) := by nlinarith

private lemma startup_entry_sq_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n : ℕ} (X : Ω → Mat m n) (hX : AEMeasurable X P)
    (hX2 : Integrable (fun ω => fro (X ω) ^ 2) P) (i : Fin m) (j : Fin n) :
    Integrable (fun ω => (X ω i j) ^ 2) P := by
  have hm : AEStronglyMeasurable (fun ω => X ω i j) P :=
    ((measurable_pi_apply j).comp_aemeasurable
      ((measurable_pi_apply i).comp_aemeasurable hX)).aestronglyMeasurable
  refine hX2.mono' (hm.pow 2) (ae_of_all _ fun ω => ?_)
  change |(X ω i j) ^ 2| ≤ fro (X ω) ^ 2
  rw [abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using
    pow_le_pow_left₀ (abs_nonneg _) (startup_abs_entry_le_fro (X ω) i j) 2

private lemma startup_abs_integral_ip_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n : ℕ} (X Y : Ω → Mat m n)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hX2 : Integrable (fun ω => fro (X ω) ^ 2) P)
    (hY2 : Integrable (fun ω => fro (Y ω) ^ 2) P) :
    |∫ ω, frobIP (X ω) (Y ω) ∂P| ≤
      Real.sqrt (∫ ω, fro (X ω) ^ 2 ∂P) *
        Real.sqrt (∫ ω, fro (Y ω) ^ 2 ∂P) := by
  have hint := startup_ip_integrable X Y hX hY hX2 hY2
  have hfro : Measurable (fun A : Mat m n => fro A) := by
    exact (show Continuous (fun A : Mat m n => fro A) by
      unfold fro
      fun_prop).measurable
  calc
    |∫ ω, frobIP (X ω) (Y ω) ∂P| ≤ ∫ ω, |frobIP (X ω) (Y ω)| ∂P :=
      abs_integral_le_integral_abs
    _ ≤ ∫ ω, fro (X ω) * fro (Y ω) ∂P := by
      exact integral_mono hint.abs
        ((memLp_two_iff_integrable_sq
          ((hfro.comp_aemeasurable hX).aestronglyMeasurable)).2 hX2 |>.integrable_mul
            ((memLp_two_iff_integrable_sq
              ((hfro.comp_aemeasurable hY).aestronglyMeasurable)).2 hY2))
        (fun ω => startup_frobIP_le _ _)
    _ ≤ _ := startup_integral_mul_le_sqrt (fun ω => fro (X ω)) (fun ω => fro (Y ω))
      (hfro.comp_aemeasurable hX).aestronglyMeasurable
      (hfro.comp_aemeasurable hY).aestronglyMeasurable hX2 hY2
      (fun _ => movement_fro_nn _) (fun _ => movement_fro_nn _)

private lemma startup_indep_centered_ip_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n : ℕ} (X Y : Ω → Mat m n)
    (hX : Measurable X) (hY : Measurable Y) (hind : IndepFun X Y P)
    (hX2 : Integrable (fun ω => fro (X ω) ^ 2) P)
    (hY2 : Integrable (fun ω => fro (Y ω) ^ 2) P) :
    ∫ ω, frobIP (X ω - mean P X) (Y ω) ∂P = 0 := by
  have hXi : ∀ i j, Integrable (fun ω => X ω i j) P := fun i j =>
    ((memLp_two_iff_integrable_sq
      (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hX)).aestronglyMeasurable)).2
        (startup_entry_sq_integrable X hX.aemeasurable hX2 i j)).integrable one_le_two
  have hYi : ∀ i j, Integrable (fun ω => Y ω i j) P := fun i j =>
    ((memLp_two_iff_integrable_sq
      (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hY)).aestronglyMeasurable)).2
        (startup_entry_sq_integrable Y hY.aemeasurable hY2 i j)).integrable one_le_two
  have hprod : ∀ i j, Integrable (fun ω =>
      (X ω i j - mean P X i j) * Y ω i j) P := by
    intro i j
    exact (hind.comp
      (((measurable_pi_apply j).comp (measurable_pi_apply i)).sub measurable_const)
      ((measurable_pi_apply j).comp (measurable_pi_apply i))).integrable_mul
        ((hXi i j).sub (integrable_const _)) (hYi i j)
  simp_rw [startup_frobIP_eq_sum, Matrix.sub_apply]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hprod i j)]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finsetSum _ (fun j _ => hprod i j)]
  apply Finset.sum_eq_zero
  intro j _
  let f : Mat m n → ℝ := fun A => A i j - mean P X i j
  let g : Mat m n → ℝ := fun A => A i j
  have hfm : Measurable f := by
    dsimp [f]
    fun_prop
  have hgm : Measurable g := by
    dsimp [g]
    fun_prop
  have he : ∫ ω, (X ω i j - mean P X i j) * Y ω i j ∂P =
      (∫ ω, X ω i j - mean P X i j ∂P) * ∫ ω, Y ω i j ∂P := by
    change (∫ ω, f (X ω) * g (Y ω) ∂P) =
      (∫ ω, f (X ω) ∂P) * ∫ ω, g (Y ω) ∂P
    exact hind.integral_fun_comp_mul_comp hX.aemeasurable hY.aemeasurable
      hfm.aestronglyMeasurable hgm.aestronglyMeasurable
  have hz : ∫ ω, X ω i j - mean P X i j ∂P = 0 := by
    rw [integral_sub (hXi i j) (integrable_const _), integral_const]
    simp only [mean, Matrix.of_apply, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_smul, sub_self]
  rw [he, hz, zero_mul]

private lemma startup_replacement_cov_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n : ℕ} (X Y Z : Ω → Mat m n)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hind : IndepFun Z Y P)
    (hX2 : Integrable (fun ω => fro (X ω) ^ 2) P)
    (hY2 : Integrable (fun ω => fro (Y ω) ^ 2) P)
    (hZ2 : Integrable (fun ω => fro (Z ω) ^ 2) P)
    (hD2 : Integrable (fun ω => fro (X ω - Z ω) ^ 2) P) :
    |∫ ω, frobIP (X ω - mean P X) (Y ω) ∂P| ≤
      2 * Real.sqrt (∫ ω, fro (X ω - Z ω) ^ 2 ∂P) *
        Real.sqrt (∫ ω, fro (Y ω) ^ 2 ∂P) := by
  let D : Ω → Mat m n := fun ω => X ω - Z ω
  have hD : Measurable D := hX.sub hZ
  have hmD : mean P X - mean P Z = mean P D := by
    ext i j
    simp only [mean, Matrix.sub_apply, Matrix.of_apply, D]
    rw [integral_sub]
    · exact ((memLp_two_iff_integrable_sq
        (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hX)).aestronglyMeasurable)).2
          (startup_entry_sq_integrable X hX.aemeasurable hX2 i j)).integrable one_le_two
    · exact ((memLp_two_iff_integrable_sq
        (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hZ)).aestronglyMeasurable)).2
          (startup_entry_sq_integrable Z hZ.aemeasurable hZ2 i j)).integrable one_le_two
  have hZc2 := startup_centered_fro_sq_integrable Z hZ.aemeasurable hZ2
  have hDc2 : Integrable (fun _ : Ω => fro (mean P D) ^ 2) P := integrable_const _
  have hDY := startup_ip_integrable D Y hD.aemeasurable hY.aemeasurable hD2 hY2
  have hZY := startup_ip_integrable (fun ω => Z ω - mean P Z) Y
    (hZ.sub measurable_const).aemeasurable hY.aemeasurable hZc2 hY2
  have hMY := startup_ip_integrable (fun _ : Ω => mean P D) Y
    measurable_const.aemeasurable hY.aemeasurable hDc2 hY2
  have hzero := startup_indep_centered_ip_zero Z Y hZ hY hind hZ2 hY2
  have hdec : ∀ ω, frobIP (X ω - mean P X) (Y ω) =
      frobIP (D ω) (Y ω) + frobIP (Z ω - mean P Z) (Y ω) -
        frobIP (mean P D) (Y ω) := by
    intro ω
    simp_rw [startup_frobIP_eq_sum, Matrix.sub_apply, D]
    rw [← hmD]
    simp only [Matrix.sub_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have heq : ∫ ω, frobIP (X ω - mean P X) (Y ω) ∂P =
      (∫ ω, frobIP (D ω) (Y ω) ∂P) -
        ∫ ω, frobIP (mean P D) (Y ω) ∂P := by
    rw [integral_congr_ae (ae_of_all _ hdec)]
    calc
      (∫ ω, frobIP (D ω) (Y ω) + frobIP (Z ω - mean P Z) (Y ω) -
          frobIP (mean P D) (Y ω) ∂P) =
          (∫ ω, frobIP (D ω) (Y ω) ∂P) +
            (∫ ω, frobIP (Z ω - mean P Z) (Y ω) ∂P) -
              ∫ ω, frobIP (mean P D) (Y ω) ∂P := by
        have hs := integral_sub (hDY.add hZY) hMY
        have ha := integral_add hDY hZY
        simpa only [Pi.add_apply, Pi.sub_apply, ha] using hs
      _ = _ := by rw [hzero]; ring
  have hmeanD := startup_fro_mean_le_sqrt D hD.aestronglyMeasurable hD2
  have hconst : |∫ ω, frobIP (mean P D) (Y ω) ∂P| ≤
      Real.sqrt (∫ ω, fro (D ω) ^ 2 ∂P) *
        Real.sqrt (∫ ω, fro (Y ω) ^ 2 ∂P) := by
    have hb := startup_abs_integral_ip_le (fun _ : Ω => mean P D) Y
      measurable_const.aemeasurable hY.aemeasurable hDc2 hY2
    have hYsqrt : 0 ≤ Real.sqrt (∫ ω, fro (Y ω) ^ 2 ∂P) := Real.sqrt_nonneg _
    calc
      _ ≤ Real.sqrt (∫ _ : Ω, fro (mean P D) ^ 2 ∂P) *
          Real.sqrt (∫ ω, fro (Y ω) ^ 2 ∂P) := hb
      _ = fro (mean P D) * Real.sqrt (∫ ω, fro (Y ω) ^ 2 ∂P) := by
        simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
          one_smul, Real.sqrt_sq_eq_abs, abs_of_nonneg (movement_fro_nn _)]
      _ ≤ Real.sqrt (∫ ω, fro (D ω) ^ 2 ∂P) *
          Real.sqrt (∫ ω, fro (Y ω) ^ 2 ∂P) :=
        mul_le_mul_of_nonneg_right hmeanD hYsqrt
  rw [heq]
  calc
    |(∫ ω, frobIP (D ω) (Y ω) ∂P) -
        ∫ ω, frobIP (mean P D) (Y ω) ∂P| ≤
        |∫ ω, frobIP (D ω) (Y ω) ∂P| +
          |∫ ω, frobIP (mean P D) (Y ω) ∂P| := abs_sub _ _
    _ ≤ Real.sqrt (∫ ω, fro (D ω) ^ 2 ∂P) *
          Real.sqrt (∫ ω, fro (Y ω) ^ 2 ∂P) +
        Real.sqrt (∫ ω, fro (D ω) ^ 2 ∂P) *
          Real.sqrt (∫ ω, fro (Y ω) ^ 2 ∂P) :=
      add_le_add (startup_abs_integral_ip_le D Y hD.aemeasurable hY.aemeasurable hD2 hY2)
        hconst
    _ = _ := by ring

private lemma startup_emaChain_add {m n B : ℕ} (β : ℝ) (D : Mat m n)
    (G : ℤ → Batch m n B) (t k l : ℕ) (M : Mat m n) :
    emaChain β D G t M (k + l) =
      emaChain β D G (t + k) (emaChain β D G t M k) l := by
  induction l with
  | zero => simp [emaChain]
  | succ l ih =>
    rw [Nat.add_succ]
    change β • emaChain β D G t M (k + l) +
        (1 - β) • batchGrad D (G ((t : ℤ) + (k + l : ℕ) + 1)) =
      β • emaChain β D G (t + k) (emaChain β D G t M k) l +
        (1 - β) • batchGrad D (G (((t + k : ℕ) : ℤ) + l + 1))
    rw [ih]
    congr 3
    push_cast
    ring

private lemma startup_emaChain_sub_eq {m n B : ℕ} (β : ℝ) (D : Mat m n)
    (G : ℤ → Batch m n B) (t : ℕ) (init M : Mat m n) (k : ℕ) :
    emaChain β D G t M k - emaChain β D G t init k = (β ^ k) • (M - init) := by
  induction k with
  | zero => simp [emaChain]
  | succ k ih =>
    have h : emaChain β D G t M (k + 1) - emaChain β D G t init (k + 1) =
        β • (emaChain β D G t M k - emaChain β D G t init k) := by
      simp only [emaChain, smul_sub]
      abel
    rw [h, ih, smul_smul, ← pow_succ']

private lemma startup_indep_past_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (cs : ChainSamples P m n B) (t r : ℕ) :
    Indep
      ((⨆ (s : ℤ) (_ : s ≤ (t : ℤ) + r + 1) (a : Fin B),
          MeasurableSpace.comap (cs.act s a) inferInstance) ⊔
        ⨆ (j : ℕ) (a : Fin B),
          MeasurableSpace.comap (cs.aux (t : ℤ) j a) inferInstance)
      (⨆ (s : ℤ) (_ : (t : ℤ) + r + 1 < s) (a : Fin B),
        MeasurableSpace.comap (cs.act s a) inferInstance) P := by
  have hind := (iIndepFun_iff_iIndep _ _ _).mp cs.indep
  have hle : ∀ i : (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B), MeasurableSpace.comap
      (Sum.elim (fun q : ℤ × Fin B => cs.act q.1 q.2)
        (fun q : ℤ × ℕ × Fin B => cs.aux q.1 q.2.1 q.2.2) i :
          Ω → Vec m × Vec n) inferInstance ≤ mΩ := by
    intro i
    rcases i with q | q
    · exact (cs.meas_act q.1 q.2).comap_le
    · exact (cs.meas_aux q.1 q.2.1 q.2.2).comap_le
  let A : Set ((ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B)) :=
    {i | (∃ q : ℤ × Fin B, i = Sum.inl q ∧ q.1 ≤ (t : ℤ) + r + 1) ∨
      (∃ q : ℤ × ℕ × Fin B, i = Sum.inr q ∧ q.1 = (t : ℤ))}
  let T : Set ((ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B)) :=
    {i | ∃ q : ℤ × Fin B, i = Sum.inl q ∧ (t : ℤ) + r + 1 < q.1}
  have hdisj : Disjoint A T := by
    rw [Set.disjoint_left]
    rintro i (⟨q, hq, hqle⟩ | ⟨q, hq, _⟩) ⟨q', hq', hqlt⟩
    · cases hq
      cases hq'
      omega
    · exact Sum.inr_ne_inl (hq.symm.trans hq')
  have hAT := indep_iSup_of_disjoint hle hind hdisj
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hAT ?_) ?_
  · refine sup_le ?_ ?_
    · refine iSup_le fun s => iSup_le fun hs => iSup_le fun a => ?_
      exact le_iSup₂_of_le (Sum.inl (s, a))
        (show Sum.inl (s, a) ∈ A from Or.inl ⟨(s, a), rfl, hs⟩) le_rfl
    · refine iSup_le fun j => iSup_le fun a => ?_
      exact le_iSup₂_of_le (Sum.inr ((t : ℤ), j, a))
        (show Sum.inr ((t : ℤ), j, a) ∈ A from Or.inr ⟨((t : ℤ), j, a), rfl, rfl⟩)
          le_rfl
  · refine iSup_le fun s => iSup_le fun hs => iSup_le fun a => ?_
    exact le_iSup₂_of_le (Sum.inl (s, a))
      (show Sum.inl (s, a) ∈ T from ⟨(s, a), rfl, hs⟩) le_rfl

open scoped Matrix.Norms.Frobenius in
private lemma startup_chainInit_meas {Ω : Type*} {A : MeasurableSpace Ω}
    {m n B : ℕ} (β : ℝ) (C : Covariances m n) (D : Mat m n)
    (z : ℕ → Fin B → Ω → Vec m × Vec n)
    (hz : ∀ j a, Measurable[A] (z j a)) :
    Measurable[A] (fun ω => chainInit β C D z ω) := by
  letI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) := by
    constructor
    exact ⟨inferInstance, rfl, inferInstance⟩
  unfold chainInit
  apply Measurable.tsum
  intro j
  exact ((startup_physgrad_cont C D).measurable.comp
    (Measurable.of_eval fun a => hz j a)).const_smul (emaW β j)

private lemma startup_future_indep_error {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (p : DynParams) (C : Covariances m n)
    (cs : ChainSamples P m n B) (t : ℕ) (D M0 : Mat m n) (W : Mat m n →ₗ[ℝ] Mat m n)
    (hD : 0 < riskSigma C D) (r l : ℕ) :
    let Z : Ω → Mat m n := fun ω => Q (physRidge p C D)
      (emaChain p.β D (fun s => physBatch C (cs.act s) ω) (t + r + 1) 0 l)
    let E : Ω → Mat m n := fun ω =>
      (def_app_dyn_chains p C cs t D M0 ω).sameV (r + 1) -
        (def_app_dyn_chains p C cs t D M0 ω).statV (r + 1)
    Measurable Z ∧ Measurable E ∧ IndepFun Z (fun ω => W (E ω)) P := by
  dsimp only
  let act : ℤ → Fin B → Ω → Vec m × Vec n := cs.act
  let aux : ℤ → ℕ → Fin B → Ω → Vec m × Vec n := cs.aux
  let A : MeasurableSpace Ω :=
    (⨆ (s : ℤ) (_ : s ≤ (t : ℤ) + r + 1) (a : Fin B),
        MeasurableSpace.comap (act s a) inferInstance) ⊔
      ⨆ (j : ℕ) (a : Fin B), MeasurableSpace.comap (aux (t : ℤ) j a) inferInstance
  let T : MeasurableSpace Ω :=
    ⨆ (s : ℤ) (_ : (t : ℤ) + r + 1 < s) (a : Fin B),
      MeasurableSpace.comap (act s a) inferInstance
  letI instA : MeasurableSpace Ω := A
  have haux : ∀ j a, Measurable[A] (aux (t : ℤ) j a) := by
    intro j a
    exact Measurable.of_comap_le
      (le_sup_of_le_right (le_iSup_of_le j (le_iSup_of_le a le_rfl)))
  have hactA : ∀ (q : ℕ), q < r + 1 → ∀ a,
      Measurable[A] (act ((t : ℤ) + q + 1) a) := by
    intro q hq a
    apply Measurable.of_comap_le
    refine le_sup_of_le_left (le_iSup_of_le ((t : ℤ) + q + 1) ?_)
    refine le_iSup_of_le (show (t : ℤ) + q + 1 ≤ (t : ℤ) + r + 1 by omega) ?_
    exact le_iSup_of_le a le_rfl
  have hinit : Measurable[A] (fun ω => chainInit p.β C D (aux (t : ℤ)) ω) :=
    startup_chainInit_meas p.β C D (aux (t : ℤ)) haux
  have hstat : ∀ k, k ≤ r + 1 → Measurable[A]
      (fun ω => emaChain p.β D (fun s => physBatch C (act s) ω) t
        (chainInit p.β C D (aux (t : ℤ)) ω) k) := by
    intro k hk
    induction k with
    | zero => simpa only [emaChain] using hinit
    | succ k ih =>
      simp only [emaChain]
      have hb : Measurable[A] (fun ω a => act ((t : ℤ) + k + 1) a ω) :=
        Measurable.of_eval fun a => hactA k (by omega) a
      exact (ih (by omega)).const_smul p.β |>.add (by
        convert ((startup_physgrad_cont C D).measurable.comp hb).const_smul
          (1 - p.β) using 1 <;> rfl)
  have hsame : ∀ k, k ≤ r + 1 → Measurable[A]
      (fun ω => emaChain p.β D (fun s => physBatch C (act s) ω) t M0 k) := by
    intro k hk
    induction k with
    | zero => exact measurable_const
    | succ k ih =>
      simp only [emaChain]
      have hb : Measurable[A] (fun ω a => act ((t : ℤ) + k + 1) a ω) :=
        Measurable.of_eval fun a => hactA k (by omega) a
      exact (ih (by omega)).const_smul p.β |>.add (by
        convert ((startup_physgrad_cont C D).measurable.comp hb).const_smul
          (1 - p.β) using 1 <;> rfl)
  have hρ : 0 ≤ physRidge p C D := by
    unfold physRidge
    exact mul_nonneg (by linarith) p.hϱ.le
  have hE : Measurable[A] (fun ω =>
      Q (physRidge p C D) (emaChain p.β D (fun s => physBatch C (act s) ω) t M0 (r + 1)) -
        Q (physRidge p C D) (emaChain p.β D (fun s => physBatch C (act s) ω) t
          (chainInit p.β C D (aux (t : ℤ)) ω) (r + 1))) := by
    exact ((startup_Q_meas _ hρ).comp (hsame (r + 1) le_rfl)).sub
      ((startup_Q_meas _ hρ).comp (hstat (r + 1) le_rfl))
  letI instT : MeasurableSpace Ω := T
  have hactT : ∀ (q : ℕ), ∀ a,
      Measurable[T] (act (((t + r + 1 : ℕ) : ℤ) + q + 1) a) := by
    intro q a
    apply Measurable.of_comap_le
    refine le_iSup_of_le (((t + r + 1 : ℕ) : ℤ) + q + 1) ?_
    refine le_iSup_of_le (show (t : ℤ) + r + 1 < ((t + r + 1 : ℕ) : ℤ) + q + 1 by
      push_cast
      omega) ?_
    exact le_iSup_of_le a le_rfl
  have hfutureBuf : ∀ k, Measurable[T]
      (fun ω => emaChain p.β D (fun s => physBatch C (act s) ω) (t + r + 1) 0 k) := by
    intro k
    induction k with
    | zero => exact measurable_const
    | succ k ih =>
      simp only [emaChain]
      have hb : Measurable[T] (fun ω a =>
          act (((t + r + 1 : ℕ) : ℤ) + k + 1) a ω) :=
        Measurable.of_eval fun a => hactT k a
      exact ih.const_smul p.β |>.add (by
        convert ((startup_physgrad_cont C D).measurable.comp hb).const_smul
          (1 - p.β) using 1 <;> rfl)
  have hZ : Measurable[T] (fun ω => Q (physRidge p C D)
      (emaChain p.β D (fun s => physBatch C (act s) ω) (t + r + 1) 0 l)) :=
    (startup_Q_meas _ hρ).comp (hfutureBuf l)
  letI instGlobal : MeasurableSpace Ω := mΩ
  have hAT : Indep A T P := by
    simpa only [A, T, act, aux] using startup_indep_past_tail cs t r
  have hEZ : IndepFun
      (fun ω => Q (physRidge p C D)
          (emaChain p.β D (fun s => physBatch C (act s) ω) t M0 (r + 1)) -
        Q (physRidge p C D) (emaChain p.β D (fun s => physBatch C (act s) ω) t
          (chainInit p.β C D (aux (t : ℤ)) ω) (r + 1)))
      (fun ω => Q (physRidge p C D)
        (emaChain p.β D (fun s => physBatch C (act s) ω) (t + r + 1) 0 l)) P := by
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hAT hE.comap_le) hZ.comap_le
  have hTle : T ≤ mΩ := by
    dsimp [T, act]
    exact iSup_le fun s => iSup_le fun _ => iSup_le fun a => (cs.meas_act s a).comap_le
  have hAle : A ≤ mΩ := by
      dsimp [A, act, aux]
      exact sup_le
        (iSup_le fun s => iSup_le fun _ => iSup_le fun a => (cs.meas_act s a).comap_le)
        (iSup_le fun j => iSup_le fun a => (cs.meas_aux (t : ℤ) j a).comap_le)
  have hZglobal := hZ.mono hTle le_rfl
  have hEglobal := hE.mono hAle le_rfl
  have hfinal := hEZ.symm.comp measurable_id (show Measurable W from (by fun_prop))
  have hfinal' : IndepFun
      (fun ω => Q (physRidge p C D)
        (emaChain p.β D (fun s => physBatch C (act s) ω) (t + r + 1) 0 l))
      (fun ω => W (Q (physRidge p C D)
          (emaChain p.β D (fun s => physBatch C (act s) ω) t M0 (r + 1)) -
        Q (physRidge p C D) (emaChain p.β D (fun s => physBatch C (act s) ω) t
          (chainInit p.β C D (aux (t : ℤ)) ω) (r + 1)))) P := by
    simpa only [Function.comp_def, id_eq] using hfinal
  simpa only [act, aux, def_app_dyn_chains] using
    And.intro hZglobal (And.intro hEglobal hfinal')

private lemma startup_bufpath_integral_shift {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (k : ℤ) (Ψ : (ℤ → Mat m n) → ℝ) (hΨ : Measurable Ψ) :
    ∫ ω, Ψ (fun s => frozenBuf F S (s + k) ω) ∂P =
      ∫ ω, Ψ (fun s => frozenBuf F S s ω) ∂P := by
  have hA := (lem_app_setup_ema_law_ii F S).2.1
  have hsh : Measurable (fun x : ℤ → Mat m n => fun s => x (s + k)) :=
    Measurable.of_eval fun s => measurable_pi_apply (s + k)
  have hB : AEMeasurable (fun ω (s : ℤ) => frozenBuf F S (s + k) ω) P :=
    hsh.comp_aemeasurable hA
  have hst := (lem_app_setup_ema_law_ii F S).2.2 k
  calc
    ∫ ω, Ψ (fun s => frozenBuf F S (s + k) ω) ∂P =
        ∫ x, Ψ x ∂(P.map (fun ω (s : ℤ) => frozenBuf F S (s + k) ω)) :=
      (integral_map hB hΨ.aestronglyMeasurable).symm
    _ = ∫ x, Ψ x ∂(P.map (fun ω (s : ℤ) => frozenBuf F S s ω)) := by rw [hst]
    _ = _ := integral_map hA hΨ.aestronglyMeasurable

private lemma startup_stat_fro_sq_moment {p : DynParams} {m n B : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M0 : Mat m n)
    (hD : 0 < riskSigma C D) (hsize : SizeFin C B p.γstar p.CSig) (k : ℕ) :
    Integrable (fun ω => fro ((def_app_dyn_chains p C cs t D M0 ω).stat k) ^ 2) P ∧
    ∫ ω, fro ((def_app_dyn_chains p C cs t D M0 ω).stat k) ^ 2 ∂P ≤
      2 * riskSigma C D * cMConst p.CSig p.γstar * B := by
  have hB : 0 < B := by
    by_contra h
    have hb : B = 0 := by omega
    have hdim : max m n = 0 := by
      have hh := hsize.1
      simp only [hb, Nat.cast_zero, mul_zero, Nat.cast_nonpos] at hh
      exact hh
    have hm : m = 0 := by omega
    have hr := eqn_app_setup_whitened_risk C D
    simp [hm, fro] at hr
    linarith
  have hA : fro (Ahat C D) = 1 := startup_Ahat_norm C D hD
  let F : FrozenParams m n B := ⟨C, Ahat C D, hA, p.β, p.hβ, hB⟩
  let S : FrozenSamples P m n B :=
    ⟨cs.act, cs.meas_act, cs.indep.precomp Sum.inl_injective, cs.law_act⟩
  have hlaw := lem_app_dyn_chains_i p C cs t D M0 hD F rfl rfl rfl S
  have hid : IdentDistrib (fun ω => normChainPath p C cs t D M0 ω)
      (fun ω (q : ℕ) => frozenBuf F S ((t : ℤ) + (q : ℤ) - 1) ω) P P :=
    ⟨AEMeasurable.of_eval fun q => by
        convert (startup_stat_aesm C cs t D M0 hlaw.1 q).const_smul
          (Real.sqrt (2 * riskSigma C D))⁻¹ |>.aemeasurable using 1 <;> rfl,
      AEMeasurable.of_eval fun q =>
        (measurable_pi_apply ((t : ℤ) + (q : ℤ) - 1)).comp_aemeasurable
          (lem_app_setup_ema_law_ii F S).2.1,
      hlaw.2.1⟩
  have hfun : Measurable (fun x : ℕ → Mat m n => fro (x k) ^ 2) :=
    startup_fro_sq_meas.comp (measurable_pi_apply k)
  have hidk := hid.comp hfun
  have hfun0 : Measurable (fun x : ℕ → Mat m n => fro (x 0) ^ 2) :=
    startup_fro_sq_meas.comp (measurable_pi_apply 0)
  have hid0 := hid.comp hfun0
  have hshift : ∫ ω, fro (frozenBuf F S ((t : ℤ) + (k : ℤ) - 1) ω) ^ 2 ∂P =
      ∫ ω, fro (frozenBuf F S ((t : ℤ) - 1) ω) ^ 2 ∂P := by
    let Ψ : (ℤ → Mat m n) → ℝ := fun x => fro (x ((t : ℤ) - 1)) ^ 2
    have hΨ : Measurable Ψ := startup_fro_sq_meas.comp (measurable_pi_apply _)
    have hs := startup_bufpath_integral_shift F S (k : ℤ) Ψ hΨ
    convert hs using 1 <;> dsimp only [Ψ] <;> congr 3 <;> ring
  have hbufpath := (lem_app_setup_ema_law_ii F S).2.1
  have hshfun : Measurable (fun x : ℤ → Mat m n => fun s => x (s + (k : ℤ))) :=
    Measurable.of_eval fun s => measurable_pi_apply (s + (k : ℤ))
  have hidshift : IdentDistrib (fun ω (s : ℤ) => frozenBuf F S (s + (k : ℤ)) ω)
      (fun ω (s : ℤ) => frozenBuf F S s ω) P P :=
    ⟨hshfun.comp_aemeasurable hbufpath, hbufpath,
      (lem_app_setup_ema_law_ii F S).2.2 (k : ℤ)⟩
  let Ψ : (ℤ → Mat m n) → ℝ := fun x => fro (x ((t : ℤ) - 1)) ^ 2
  have hΨ : Measurable Ψ := startup_fro_sq_meas.comp (measurable_pi_apply _)
  have hidshift' := hidshift.comp hΨ
  have hnorm0 := lem_app_dyn_chains_iii p C cs t D M0 hD hsize
  have hscale : ∀ q ω, fro ((def_app_dyn_chains p C cs t D M0 ω).stat q) ^ 2 =
      (2 * riskSigma C D) * fro (normChainPath p C cs t D M0 ω q) ^ 2 := by
    intro q ω
    unfold normChainPath
    rw [(coupling_fro_props (m := m) (n := n)).1
      (Real.sqrt (2 * riskSigma C D))⁻¹
      ((def_app_dyn_chains p C cs t D M0 ω).stat q) (by positivity)]
    have hs : Real.sqrt (2 * riskSigma C D) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    have hs2 : Real.sqrt (2 * riskSigma C D) ^ 2 = 2 * riskSigma C D :=
      Real.sq_sqrt (by linarith)
    field_simp [hs]
    nlinarith
  have hnk : Integrable (fun ω => fro (normChainPath p C cs t D M0 ω k) ^ 2) P := by
    have h0n : Integrable (fun ω => fro (normChainPath p C cs t D M0 ω 0) ^ 2) P := by
      have hs := hnorm0.2.1
      rw [show (fun ω => fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0) ^ 2) =
          fun ω => (2 * riskSigma C D) * fro (normChainPath p C cs t D M0 ω 0) ^ 2 by
        funext ω; exact hscale 0 ω] at hs
      have hd := hs.div_const (2 * riskSigma C D)
      refine hd.congr (ae_of_all _ fun ω => ?_)
      field_simp [(by linarith : 2 * riskSigma C D ≠ 0)]
    have hf0 : Integrable (fun ω => fro (frozenBuf F S ((t : ℤ) - 1) ω) ^ 2) P := by
      have hh := hid0.integrable_iff.mp h0n
      refine hh.congr (ae_of_all _ fun ω => ?_)
      rfl
    have hfk : Integrable (fun ω => fro (frozenBuf F S
        (((t : ℤ) - 1) + (k : ℤ)) ω) ^ 2) P := by
      have hh := hidshift'.integrable_iff.mpr hf0
      refine hh.congr (ae_of_all _ fun ω => ?_)
      rfl
    rw [show ((t : ℤ) - 1) + (k : ℤ) = (t : ℤ) + (k : ℤ) - 1 by ring] at hfk
    apply hidk.integrable_iff.mpr
    exact hfk
  constructor
  · simpa only [hscale] using hnk.const_mul (2 * riskSigma C D)
  · have heq : ∫ ω, fro ((def_app_dyn_chains p C cs t D M0 ω).stat k) ^ 2 ∂P =
        ∫ ω, fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0) ^ 2 ∂P := by
      have hnormeq : ∫ ω, fro (normChainPath p C cs t D M0 ω k) ^ 2 ∂P =
          ∫ ω, fro (normChainPath p C cs t D M0 ω 0) ^ 2 ∂P := by
        calc
          _ = ∫ ω, fro (frozenBuf F S ((t : ℤ) + (k : ℤ) - 1) ω) ^ 2 ∂P := by
            simpa only [Function.comp_apply] using hidk.integral_eq
          _ = ∫ ω, fro (frozenBuf F S ((t : ℤ) - 1) ω) ^ 2 ∂P := hshift
          _ = _ := by
            simpa only [Function.comp_apply, Nat.cast_zero, add_zero] using hid0.integral_eq.symm
      simp_rw [hscale]
      rw [integral_const_mul, integral_const_mul, hnormeq]
    rw [heq]
    exact hnorm0.2.2

private lemma startup_Q_fro_sq_le {m n B : ℕ} (γ ρ : ℝ) (hρ : 0 ≤ ρ)
    (hsize : ((max m n : ℕ) : ℝ) ≤ γ * B) (K : Mat m n) :
    fro (Q ρ K) ^ 2 ≤ γ * B := by
  have hQ := (lem_app_setup_filter_i ρ hρ K).2.1
  have hr : (K.rank : ℝ) ≤ ((max m n : ℕ) : ℝ) := by
    exact_mod_cast (Matrix.rank_le_height K).trans (le_max_left m n)
  exact hQ.trans (hr.trans hsize)

private lemma startup_error_one_fro_sq_bound {p : DynParams} {m n B : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M0 : Mat m n)
    (rlo rhi : ℝ) (hrlo : 0 < rlo) (hDlo : rlo ≤ riskSigma C D)
    (hDhi : riskSigma C D ≤ rhi) (hsize : SizeFin C B p.γstar p.CSig) (r : ℕ) :
    let E : Ω → Mat m n := fun ω =>
      (def_app_dyn_chains p C cs t D M0 ω).sameV (r + 1) -
        (def_app_dyn_chains p C cs t D M0 ω).statV (r + 1)
    Integrable (fun ω => fro (E ω) ^ 2) P ∧
      ∫ ω, fro (E ω) ^ 2 ∂P ≤
        2 * ((rlo * p.ϱ) ^ (-(1 / 2 : ℝ))) ^ 2 * p.β ^ (2 * (r + 1)) *
          (fro M0 ^ 2 + 2 * rhi * cMConst p.CSig p.γstar * B) := by
  dsimp only
  let E : Ω → Mat m n := fun ω =>
    (def_app_dyn_chains p C cs t D M0 ω).sameV (r + 1) -
      (def_app_dyn_chains p C cs t D M0 ω).statV (r + 1)
  have hD : 0 < riskSigma C D := hrlo.trans_le hDlo
  obtain ⟨hsum, hNint, hNbd⟩ := lem_app_dyn_chains_iii p C cs t D M0 hD hsize
  have hEae : AEMeasurable E P :=
    (((measurable_pi_apply (r + 1)).comp_aemeasurable
      (startup_sameV_path_aem (p := p) C cs t D M0 hD)).sub
    ((measurable_pi_apply (r + 1)).comp_aemeasurable
      (startup_statV_path_aem C cs t D M0 hD hsum)))
  let q := (rlo * p.ϱ) ^ (-(1 / 2 : ℝ))
  have hpt : ∀ ω, fro (E ω) ^ 2 ≤ 2 * q ^ 2 * p.β ^ (2 * (r + 1)) *
      (fro M0 ^ 2 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0) ^ 2) := by
    intro ω
    have hb := startup_error_fro_le (p := p) C cs t D M0 rlo hrlo hDlo r ω
    change fro (E ω) ≤ q * p.β ^ (r + 1) *
      (fro M0 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0)) at hb
    have hs := pow_le_pow_left₀ (movement_fro_nn _) hb 2
    calc
      fro (E ω) ^ 2 ≤ (q * p.β ^ (r + 1) *
          (fro M0 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0))) ^ 2 := hs
      _ ≤ 2 * q ^ 2 * p.β ^ (2 * (r + 1)) *
          (fro M0 ^ 2 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0) ^ 2) := by
        have hh := coupling_sq_add_le' (fro M0)
          (fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0))
        rw [show p.β ^ (2 * (r + 1)) = (p.β ^ (r + 1)) ^ 2 by
          rw [mul_comm, pow_mul]]
        convert mul_le_mul_of_nonneg_left hh
          (mul_nonneg (sq_nonneg q) (sq_nonneg (p.β ^ (r + 1)))) using 1 <;> ring
  have hmajor : Integrable (fun ω => 2 * q ^ 2 * p.β ^ (2 * (r + 1)) *
      (fro M0 ^ 2 + fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0) ^ 2)) P :=
    ((integrable_const (μ := P) (fro M0 ^ 2)).add hNint).const_mul _
  have hint : Integrable (fun ω => fro (E ω) ^ 2) P := by
    refine hmajor.mono' (startup_fro_sq_meas.comp_aemeasurable hEae).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨hint, (integral_mono hint hmajor hpt).trans ?_⟩
  rw [integral_const_mul, integral_add (integrable_const _) hNint, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, one_mul]
  have hc : 0 ≤ 2 * q ^ 2 * p.β ^ (2 * (r + 1)) :=
    mul_nonneg (mul_nonneg (by positivity) (sq_nonneg q)) (pow_nonneg p.hβ.1 _)
  apply mul_le_mul_of_nonneg_left _ hc
  have hcM : 0 ≤ cMConst p.CSig p.γstar := by unfold cMConst; positivity
  have hfac : 0 ≤ 2 * cMConst p.CSig p.γstar * B := by positivity
  have hh := mul_le_mul_of_nonneg_right hDhi hfac
  have hNB : ∫ ω, fro ((def_app_dyn_chains p C cs t D M0 ω).stat 0) ^ 2 ∂P ≤
      2 * rhi * cMConst p.CSig p.γstar * B := hNbd.trans (by
    convert hh using 1 <;> ring)
  gcongr

private lemma startup_future_diff_fro_sq_bound {p : DynParams} {m n B : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M0 : Mat m n)
    (rlo rhi : ℝ) (hrlo : 0 < rlo) (hDlo : rlo ≤ riskSigma C D)
    (hDhi : riskSigma C D ≤ rhi) (hsize : SizeFin C B p.γstar p.CSig) (r l : ℕ) :
    let X : Ω → Mat m n := fun ω => stationaryV p C cs t D (r + l) ω
    let Z : Ω → Mat m n := fun ω => Q (physRidge p C D)
      (emaChain p.β D (fun s => physBatch C (cs.act s) ω) (t + r + 1) 0 l)
    Integrable (fun ω => fro (X ω - Z ω) ^ 2) P ∧
      ∫ ω, fro (X ω - Z ω) ^ 2 ∂P ≤
        ((rlo * p.ϱ) ^ (-(1 / 2 : ℝ))) ^ 2 * p.β ^ (2 * l) *
          (2 * rhi * cMConst p.CSig p.γstar * B) := by
  dsimp only
  let X : Ω → Mat m n := fun ω => stationaryV p C cs t D (r + l) ω
  let Z : Ω → Mat m n := fun ω => Q (physRidge p C D)
    (emaChain p.β D (fun s => physBatch C (cs.act s) ω) (t + r + 1) 0 l)
  have hD : 0 < riskSigma C D := hrlo.trans_le hDlo
  have hmom := startup_stat_fro_sq_moment C cs t D M0 hD hsize (r + 1)
  have hρlo : 0 < rlo * p.ϱ := mul_pos hrlo p.hϱ
  have hρ : 0 < physRidge p C D := by unfold physRidge; nlinarith
  let q := (rlo * p.ϱ) ^ (-(1 / 2 : ℝ))
  have hpt : ∀ ω, fro (X ω - Z ω) ^ 2 ≤ q ^ 2 * p.β ^ (2 * l) *
      fro ((def_app_dyn_chains p C cs t D M0 ω).stat (r + 1)) ^ 2 := by
    intro ω
    have hadd := startup_emaChain_add p.β D (fun s => physBatch C (cs.act s) ω)
      t (r + 1) l ((def_app_dyn_chains p C cs t D M0 ω).stat 0)
    change emaChain p.β D (fun s => physBatch C (cs.act s) ω) t
        ((def_app_dyn_chains p C cs t D M0 ω).stat 0) (r + 1 + l) =
      emaChain p.β D (fun s => physBatch C (cs.act s) ω) (t + (r + 1))
        ((def_app_dyn_chains p C cs t D M0 ω).stat (r + 1)) l at hadd
    have hsub := startup_emaChain_sub_eq p.β D (fun s => physBatch C (cs.act s) ω)
      (t + r + 1) 0 ((def_app_dyn_chains p C cs t D M0 ω).stat (r + 1)) l
    have hlip := lem_app_setup_filter_iii (physRidge p C D) hρ
      ((def_app_dyn_chains p C cs t D M0 ω).stat (r + l + 1))
      (emaChain p.β D (fun s => physBatch C (cs.act s) ω) (t + r + 1) 0 l)
    have hidx : r + l + 1 = (r + 1) + l := by omega
    have hadd' : (def_app_dyn_chains p C cs t D M0 ω).stat (r + l + 1) =
        emaChain p.β D (fun s => physBatch C (cs.act s) ω) (t + r + 1)
          ((def_app_dyn_chains p C cs t D M0 ω).stat (r + 1)) l := by
      change emaChain p.β D (fun s => physBatch C (cs.act s) ω) t
        ((def_app_dyn_chains p C cs t D M0 ω).stat 0) (r + l + 1) = _
      rw [hidx]
      simpa only [Nat.add_assoc] using hadd
    rw [hadd', hsub] at hlip
    have hsm := (coupling_fro_props (m := m) (n := n)).1 (p.β ^ l)
      ((def_app_dyn_chains p C cs t D M0 ω).stat (r + 1) - 0) (pow_nonneg p.hβ.1 _)
    rw [hsm, sub_zero] at hlip
    have hq : (physRidge p C D) ^ (-(1 / 2 : ℝ)) ≤ q := by
      have hrl : rlo * p.ϱ ≤ physRidge p C D := by unfold physRidge; nlinarith
      exact Real.rpow_le_rpow_of_nonpos hρlo hrl (by norm_num)
    have hb : fro (X ω - Z ω) ≤ q * (p.β ^ l *
        fro ((def_app_dyn_chains p C cs t D M0 ω).stat (r + 1))) := by
      change fro (Q (physRidge p C D)
          ((def_app_dyn_chains p C cs t D M0 ω).stat (r + l + 1)) -
        Q (physRidge p C D)
          (emaChain p.β D (fun s => physBatch C (cs.act s) ω) (t + r + 1) 0 l)) ≤ _
      rw [hadd']
      exact hlip.trans (mul_le_mul_of_nonneg_right hq
        (mul_nonneg (pow_nonneg p.hβ.1 _) (movement_fro_nn _)))
    have hs := pow_le_pow_left₀ (movement_fro_nn _) hb 2
    calc
      fro (X ω - Z ω) ^ 2 ≤
          (q * (p.β ^ l * fro ((def_app_dyn_chains p C cs t D M0 ω).stat (r + 1)))) ^ 2 := hs
      _ = q ^ 2 * p.β ^ (2 * l) *
          fro ((def_app_dyn_chains p C cs t D M0 ω).stat (r + 1)) ^ 2 := by
        rw [mul_pow, mul_pow, show p.β ^ (2 * l) = (p.β ^ l) ^ 2 by
          rw [mul_comm, pow_mul]]
        ring
  have hXZae : AEMeasurable (fun ω => X ω - Z ω) P := by
    have hx := (startup_stat_aesm C cs t D M0 (lem_app_dyn_chains_iii p C cs t D M0 hD hsize).1
      (r + l + 1)).aemeasurable
    have hz : AEMeasurable Z P := (startup_future_indep_error p C cs t D M0
      (LinearMap.id : Mat m n →ₗ[ℝ] Mat m n) hD r l).1.aemeasurable
    exact ((startup_Q_meas _ hρ.le).comp_aemeasurable hx).sub hz
  have hmajor : Integrable (fun ω => q ^ 2 * p.β ^ (2 * l) *
      fro ((def_app_dyn_chains p C cs t D M0 ω).stat (r + 1)) ^ 2) P := hmom.1.const_mul _
  have hint : Integrable (fun ω => fro (X ω - Z ω) ^ 2) P := by
    refine hmajor.mono' (startup_fro_sq_meas.comp_aemeasurable hXZae).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨hint, (integral_mono hint hmajor hpt).trans ?_⟩
  rw [integral_const_mul]
  have hc : 0 ≤ q ^ 2 * p.β ^ (2 * l) :=
    mul_nonneg (sq_nonneg q) (pow_nonneg p.hβ.1 _)
  exact mul_le_mul_of_nonneg_left (hmom.2.trans (by
    have hcM : 0 ≤ cMConst p.CSig p.γstar := by unfold cMConst; positivity
    have hfac : 0 ≤ 2 * cMConst p.CSig p.γstar * B := by positivity
    have hh := mul_le_mul_of_nonneg_right hDhi hfac
    exact (by convert hh using 1 <;> ring))) hc

private lemma startup_statV_meas {p : DynParams} {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (C : Covariances m n)
    (cs : ChainSamples P m n B) (t : ℕ) (D M0 : Mat m n)
    (hD : 0 < riskSigma C D) (k : ℕ) :
    Measurable (fun ω => (def_app_dyn_chains p C cs t D M0 ω).statV k) := by
  have hinit : Measurable (fun ω => chainInit p.β C D (cs.aux (t : ℤ)) ω) :=
    startup_chainInit_meas p.β C D (cs.aux (t : ℤ)) (fun j a => cs.meas_aux (t : ℤ) j a)
  have hs : Measurable (fun ω =>
      emaChain p.β D (fun s => physBatch C (cs.act s) ω) t
        (chainInit p.β C D (cs.aux (t : ℤ)) ω) k) := by
    induction k with
    | zero => simpa only [emaChain] using hinit
    | succ k ih =>
      simp only [emaChain]
      have hb : Measurable (fun ω a => cs.act ((t : ℤ) + k + 1) a ω) :=
        Measurable.of_eval fun a => cs.meas_act _ a
      exact ih.const_smul p.β |>.add (by
        convert ((startup_physgrad_cont C D).measurable.comp hb).const_smul
          (1 - p.β) using 1 <;> rfl)
  have hρ : 0 ≤ physRidge p C D := by
    unfold physRidge
    exact mul_nonneg (by linarith) p.hϱ.le
  exact (startup_Q_meas _ hρ).comp hs

private lemma startup_weighted_geom (p : DynParams) (L : ℕ) :
    ∑ r ∈ Finset.range L, (r + 1 : ℝ) * p.β ^ (r + 1) ≤
      p.β / (1 - p.β) ^ 2 := by
  let s : Finset ℕ := (Finset.range L).image Nat.succ
  have hinj : Set.InjOn Nat.succ (Finset.range L) := fun _ _ _ _ h => Nat.succ.inj h
  have heq : ∑ r ∈ Finset.range L, (r + 1 : ℝ) * p.β ^ (r + 1) =
      ∑ n ∈ s, (n : ℝ) * p.β ^ n := by
    dsimp [s]
    rw [Finset.sum_image hinj]
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
  rw [heq]
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one
    (show ‖p.β‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg p.hβ.1]; exact p.hβ.2)).summable
  calc
    _ ≤ ∑' n : ℕ, (n : ℝ) * p.β ^ n := hs.sum_le_tsum s
      (fun n _ => mul_nonneg (Nat.cast_nonneg n) (pow_nonneg p.hβ.1 _))
    _ = _ := (hasSum_coe_mul_geometric_of_norm_lt_one
      (show ‖p.β‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg p.hβ.1]; exact p.hβ.2)).tsum_eq

private lemma startup_frobIP_sum_right {m n : ℕ} {ι : Type*}
    (X : Mat m n) (s : Finset ι) (Y : ι → Mat m n) :
    frobIP X (∑ i ∈ s, Y i) = ∑ i ∈ s, frobIP X (Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frobIP]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [show frobIP X (Y i + ∑ j ∈ s, Y j) =
        frobIP X (Y i) + frobIP X (∑ j ∈ s, Y j) by
      unfold frobIP
      simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.trace_add]]
    rw [ih]

private lemma startup_frobIP_comm {m n : ℕ} (X Y : Mat m n) :
    frobIP X Y = frobIP Y X := by
  unfold frobIP
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]

private lemma startup_frobIP_sum_left {m n : ℕ} {ι : Type*}
    (X : ι → Mat m n) (s : Finset ι) (Y : Mat m n) :
    frobIP (∑ i ∈ s, X i) Y = ∑ i ∈ s, frobIP (X i) Y := by
  rw [startup_frobIP_comm, startup_frobIP_sum_right]
  apply Finset.sum_congr rfl
  intro i _
  exact startup_frobIP_comm _ _

private lemma startup_sqrt_sq_major {x c y : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c)
    (hy : 0 ≤ y) (h : x ≤ c * y ^ 2) :
    Real.sqrt x ≤ Real.sqrt c * y := by
  calc
    Real.sqrt x ≤ Real.sqrt (c * y ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt c * y := by
      rw [Real.sqrt_mul hc, Real.sqrt_sq_eq_abs, abs_of_nonneg hy]

private lemma startup_centered_fro_sq_bound {m n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → Mat m n) (hX : AEMeasurable X P)
    (hX2 : Integrable (fun ω ↦ fro (X ω) ^ 2) P) :
    ∫ ω, fro (X ω - mean P X) ^ 2 ∂P ≤ 4 * ∫ ω, fro (X ω) ^ 2 ∂P := by
  have hI0 : 0 ≤ ∫ ω, fro (X ω) ^ 2 ∂P := integral_nonneg fun _ ↦ sq_nonneg _
  have hm := startup_fro_mean_le_sqrt X hX.aestronglyMeasurable hX2
  have hm2 : fro (mean P X) ^ 2 ≤ ∫ ω, fro (X ω) ^ 2 ∂P := by
    calc
      fro (mean P X) ^ 2 ≤ Real.sqrt (∫ ω, fro (X ω) ^ 2 ∂P) ^ 2 :=
        pow_le_pow_left₀ (movement_fro_nn _) hm 2
      _ = _ := Real.sq_sqrt hI0
  have hcent := startup_centered_fro_sq_integrable X hX hX2
  have hmajor : Integrable (fun ω ↦
      2 * (fro (X ω) ^ 2 + fro (mean P X) ^ 2)) P :=
    (hX2.add (integrable_const _)).const_mul 2
  calc
    ∫ ω, fro (X ω - mean P X) ^ 2 ∂P ≤
        ∫ ω, 2 * (fro (X ω) ^ 2 + fro (mean P X) ^ 2) ∂P := by
      apply integral_mono hcent hmajor
      intro ω
      have hs := pow_le_pow_left₀ (movement_fro_nn _)
        (coupling_fro_sub_le (X ω) (mean P X)) 2
      exact hs.trans (by nlinarith [sq_nonneg (fro (X ω) - fro (mean P X))])
    _ = 2 * ((∫ ω, fro (X ω) ^ 2 ∂P) + fro (mean P X) ^ 2) := by
      rw [integral_const_mul, integral_add hX2 (integrable_const _), integral_const]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    _ ≤ 4 * ∫ ω, fro (X ω) ^ 2 ∂P := by linarith

private lemma startup_sum_if_le (L r : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ∑ u ∈ Finset.range L, (if u ≤ r then x else 0) ≤ (r + 1 : ℝ) * x := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.range L).filter fun u ↦ u ≤ r).card ≤ r + 1 := by
    calc
      _ ≤ (Finset.range (r + 1)).card := Finset.card_le_card (by
        intro u hu
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_filter.mp hu).2))
      _ = r + 1 := Finset.card_range _
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hx

private lemma startup_sum_if_lt (L u : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ∑ r ∈ Finset.range L, (if r < u then x else 0) ≤ (u + 1 : ℝ) * x := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.range L).filter fun r ↦ r < u).card ≤ u + 1 := by
    calc
      _ ≤ (Finset.range (u + 1)).card := Finset.card_le_card (by
        intro r hr
        exact Finset.mem_range.mpr
          (lt_trans (Finset.mem_filter.mp hr).2 (Nat.lt_succ_self u)))
      _ = u + 1 := Finset.card_range _
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hx

/-- `lem:app-dyn-startup`, snapshot `cr-2026-10-23`, part (ii): the startup cross term. `𝒲` is a
linear map on `ℝ^{N_out×N_in}` with Frobenius norm at most one (`∀ X, ‖𝒲X‖_F ≤ ‖X‖_F`), and
`A = ∑_{r<L}(V̂_r − V_r)` with `a = 1 + ‖m‖_F/√B`. The pairing is `frobIP`. Constant `K` depends on
the fixed parameters and `(r₋, r₊)` only. Statement verbatim from `section.tex` (ll. 1614–1623):
```latex
\begin{lemma}[Stationary block sums and the startup cross term]\label{lem:app-dyn-startup}
Let $D$, $m$ be deterministic with $r_-\le\cR(D)\le r_+$, consider the chains
at $(t,D,m)$, and put $S\defeq\sum_{r<L}V_r$, $A\defeq\sum_{r<L}(\widehat V_r-V_r)$ and
$a\defeq1+\norm m_\F/\sqrt B$. Then
\begin{enumerate}[label=(\roman*)]
\item $\EE\norm{S-L\overline V(D)}_\F^2\le CBL$;
\item for every linear map $\mathcal W$ on $\R^{\Nout\times\Nin}$ of Frobenius norm at
most one, $\abs{\EE\langle S,\mathcal WA\rangle}\le Ca\big(B+L\sqrt B\big)$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_dyn_startup_ii (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) (rlo rhi : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ K : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M0 : Mat m n)
      (W : Mat m n →ₗ[ℝ] Mat m n),
      SizeFin C B p.γstar p.CSig → rlo ≤ riskSigma C D → riskSigma C D ≤ rhi →
      (∀ X : Mat m n, fro (W X) ≤ fro X) →
      Integrable (fun ω => frobIP (∑ r ∈ Finset.range (blockLen B), stationaryV p C cs t D r ω)
        (W (∑ r ∈ Finset.range (blockLen B),
          ((def_app_dyn_chains p C cs t D M0 ω).sameV (r + 1) -
            (def_app_dyn_chains p C cs t D M0 ω).statV (r + 1))))) P ∧
      |∫ ω, frobIP (∑ r ∈ Finset.range (blockLen B), stationaryV p C cs t D r ω)
        (W (∑ r ∈ Finset.range (blockLen B),
          ((def_app_dyn_chains p C cs t D M0 ω).sameV (r + 1) -
            (def_app_dyn_chains p C cs t D M0 ω).statV (r + 1)))) ∂P| ≤
          K * (1 + fro M0 / Real.sqrt B) * (B + (blockLen B : ℝ) * Real.sqrt B) := by
  obtain ⟨Cm, hCm⟩ := lem_app_dyn_mean_iii_ema
    p.γstar p.CSig p.ϱ p.ϱ p.hϱ le_rfl
  let q := (rlo * p.ϱ) ^ (-(1 / 2 : ℝ))
  let c := max 1 (2 * rhi * cMConst p.CSig p.γstar)
  let e := Real.sqrt (2 * c) * q
  let vn := Real.sqrt (4 * p.γstar)
  let cn := vn * e
  let cf := 2 * Real.sqrt c * q * e
  let cm := max Cm 0 * e
  let g := p.β / (1 - p.β)
  let wg := p.β / (1 - p.β) ^ 2
  let K := max 0 ((cn + cf) * wg + cm * g)
  refine ⟨K, ?_⟩
  intro Ω _ P _ m n B C cs t D M0 W hsize hDlo hDhi hW
  have hD : 0 < riskSigma C D := hrlo.trans_le hDlo
  have hB : 0 < B := by
    by_contra hb
    have hb0 : B = 0 := by omega
    have hmax : max m n = 0 := by
      have hh := hsize.1
      simp only [hb0, Nat.cast_zero, mul_zero, Nat.cast_nonpos] at hh
      exact hh
    have hm0 : m = 0 := by omega
    have hr := eqn_app_setup_whitened_risk C D
    simp [hm0, fro] at hr
    linarith
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr (by exact_mod_cast hB)
  have hc0 : 0 ≤ c := by
    exact zero_le_one.trans (by dsimp [c]; exact le_max_left _ _)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact Real.rpow_nonneg (mul_pos hrlo p.hϱ).le _
  have he0 : 0 ≤ e := mul_nonneg (Real.sqrt_nonneg _) hq0
  have hvn0 : 0 ≤ vn := Real.sqrt_nonneg _
  have hcn0 : 0 ≤ cn := mul_nonneg hvn0 he0
  have hcf0 : 0 ≤ cf := by dsimp [cf]; positivity
  have hcm0 : 0 ≤ cm := mul_nonneg (le_max_right _ _) he0
  have hg0 : 0 ≤ g := by
    dsimp [g]
    exact div_nonneg p.hβ.1 (sub_nonneg.mpr p.hβ.2.le)
  have hwg0 : 0 ≤ wg := by
    dsimp [wg]
    exact div_nonneg p.hβ.1 (sq_nonneg _)
  have hK0 : 0 ≤ K := le_max_left _ _
  let L := blockLen B
  let V : ℕ → Ω → Mat m n := fun u ω ↦ stationaryV p C cs t D u ω
  let E : ℕ → Ω → Mat m n := fun r ω ↦
    (def_app_dyn_chains p C cs t D M0 ω).sameV (r + 1) -
      (def_app_dyn_chains p C cs t D M0 ω).statV (r + 1)
  let A : Ω → Mat m n := fun ω ↦ ∑ r ∈ Finset.range L, E r ω
  let S0 : Ω → Mat m n := fun ω ↦ ∑ u ∈ Finset.range L, V u ω
  let μ : Mat m n := mean P (V 0)
  have hVmeas : ∀ u, Measurable (V u) := fun u ↦ by
    simpa only [V, stationaryV] using startup_statV_meas C cs t D 0 hD (u + 1)
  have hV2 : ∀ u, Integrable (fun ω ↦ fro (V u ω) ^ 2) P := by
    intro u
    refine Integrable.of_bound (C := p.γstar * B)
      (startup_fro_sq_meas.comp (hVmeas u)).aestronglyMeasurable ?_
    exact ae_of_all _ fun ω ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      simpa only [V] using startup_statV_fro_sq_le C cs t D hsize hD u ω
  have hV2bd : ∀ u, ∫ ω, fro (V u ω) ^ 2 ∂P ≤ p.γstar * B := by
    intro u
    calc
      _ ≤ ∫ _ : Ω, p.γstar * B ∂P := integral_mono (hV2 u) (integrable_const _) fun ω ↦ by
        simpa only [V] using startup_statV_fro_sq_le C cs t D hsize hD u ω
      _ = _ := by
        simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  have hEmeas : ∀ r, Measurable (E r) := fun r ↦ by
    simpa only [E] using
      (startup_future_indep_error p C cs t D M0 W hD r 0).2.1
  have hWEmeas : ∀ r, Measurable (fun ω ↦ W (E r ω)) := fun r ↦
    (show Measurable W by fun_prop).comp (hEmeas r)
  have hE2 : ∀ r, Integrable (fun ω ↦ fro (E r ω) ^ 2) P := fun r ↦ by
    simpa only [E] using
      (startup_error_one_fro_sq_bound C cs t D M0 rlo rhi hrlo hDlo hDhi hsize r).1
  have hE2bd : ∀ r, ∫ ω, fro (E r ω) ^ 2 ∂P ≤
      2 * q ^ 2 * p.β ^ (2 * (r + 1)) *
        (fro M0 ^ 2 + 2 * rhi * cMConst p.CSig p.γstar * B) := fun r ↦ by
    simpa only [E, q] using
      (startup_error_one_fro_sq_bound C cs t D M0 rlo rhi hrlo hDlo hDhi hsize r).2
  have hWE2 : ∀ r, Integrable (fun ω ↦ fro (W (E r ω)) ^ 2) P := by
    intro r
    refine (hE2 r).mono' (startup_fro_sq_meas.comp (hWEmeas r)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (movement_fro_nn _) (hW (E r ω)) 2
  have hWE2bd : ∀ r, ∫ ω, fro (W (E r ω)) ^ 2 ∂P ≤
      2 * q ^ 2 * p.β ^ (2 * (r + 1)) *
        (fro M0 ^ 2 + 2 * rhi * cMConst p.CSig p.γstar * B) := by
    intro r
    exact (integral_mono (hWE2 r) (hE2 r) fun ω ↦
      pow_le_pow_left₀ (movement_fro_nn _) (hW (E r ω)) 2).trans (hE2bd r)
  have hA2raw := startup_error_sum_fro_sq_bound C cs t D M0
    rlo rhi hrlo hDlo hDhi hsize L
  have hA2 : Integrable (fun ω ↦ fro (A ω) ^ 2) P := by
    simpa only [A, E, q, L, mul_assoc] using hA2raw.1
  have hSmeas : AEMeasurable S0 P :=
    Finset.aemeasurable_fun_sum _ fun u _ ↦ (hVmeas u).aemeasurable
  have hS2 : Integrable (fun ω ↦ fro (S0 ω) ^ 2) P := by
    let C0 : ℝ := (L : ℝ) ^ 2 * p.γstar * B
    refine Integrable.of_bound (C := C0)
      (startup_fro_sq_meas.comp_aemeasurable hSmeas).aestronglyMeasurable ?_
    exact ae_of_all _ fun ω ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hs := coupling_norm_finset_sum_sq fro coupling_fro_props.2.1
        coupling_fro_props.2.2.1 movement_fro_nn L (fun u ↦ V u ω)
      refine hs.trans ?_
      calc
        (L : ℝ) * ∑ u ∈ Finset.range L, fro (V u ω) ^ 2 ≤
            (L : ℝ) * ∑ _u ∈ Finset.range L, p.γstar * B := by
          gcongr with u hu
          simpa only [V] using startup_statV_fro_sq_le C cs t D hsize hD u ω
        _ = C0 := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; dsimp [C0]; ring
  have hWA2 : Integrable (fun ω ↦ fro (W (A ω)) ^ 2) P := by
    have hAmeas : AEMeasurable A P :=
      Finset.aemeasurable_fun_sum _ fun r _ ↦ (hEmeas r).aemeasurable
    refine hA2.mono'
      (startup_fro_sq_meas.comp_aemeasurable
        ((show Measurable W by fun_prop).comp_aemeasurable hAmeas)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (movement_fro_nn _) (hW (A ω)) 2
  have htargetInt : Integrable (fun ω ↦ frobIP (S0 ω) (W (A ω))) P :=
    startup_ip_integrable S0 (fun ω ↦ W (A ω)) hSmeas
      ((show Measurable W by fun_prop).comp_aemeasurable
        (Finset.aemeasurable_fun_sum _ fun r _ ↦ (hEmeas r).aemeasurable))
      hS2 hWA2
  refine ⟨by simpa only [S0, A, V, E, L] using htargetInt, ?_⟩
  let F : FrozenParams m n B :=
    ⟨C, Ahat C D, startup_Ahat_norm C D hD, p.β, p.hβ, hB⟩
  let FS : FrozenSamples P m n B :=
    ⟨cs.act, cs.meas_act, cs.indep.precomp Sum.inl_injective, cs.law_act⟩
  have hlaw := lem_app_dyn_chains_i p C cs t D 0 hD F rfl rfl rfl FS
  have hmueq : μ = mean P (frozenUpd F FS p.ϱ (t : ℤ)) := by
    simpa only [μ, V, stationaryV] using hlaw.2.2.2.2
  have hmubd : fro μ ≤ max Cm 0 := by
    have hh := (hCm m n B Ω P FS F (t : ℤ) hsize.1 hsize.2.1 hsize.2.2).2.2.2
      p.ϱ ⟨le_rfl, le_rfl⟩
    have hd : 0 ≤ fro (mean P (fun ω ↦ dQ p.ϱ (frozenBuf F FS (t : ℤ) ω))) :=
      movement_fro_nn _
    rw [hmueq]
    have hqmean : fro (mean P (fun ω ↦ Q p.ϱ (frozenBuf F FS (t : ℤ) ω))) ≤ Cm := by
      linarith
    have hqmean' : fro (mean P (frozenUpd F FS p.ϱ (t : ℤ))) ≤ Cm := by
      change fro (mean P (fun ω ↦ Q p.ϱ (frozenBuf F FS (t : ℤ) ω))) ≤ Cm
      exact hqmean
    exact hqmean'.trans (le_max_left _ _)
  let T : ℝ := fro M0 + Real.sqrt B
  let R : ℝ := Real.sqrt B * T
  have hT0 : 0 ≤ T := add_nonneg (movement_fro_nn _) hsB.le
  have hR0 : 0 ≤ R := mul_nonneg hsB.le hT0
  have hrhi : 0 < rhi := hrlo.trans_le hle
  have hcM0 : 0 ≤ cMConst p.CSig p.γstar := by
    unfold cMConst
    positivity
  have hcN0 : 0 ≤ 2 * rhi * cMConst p.CSig p.γstar := by positivity
  have hcN : 2 * rhi * cMConst p.CSig p.γstar ≤ c := by
    dsimp [c]
    exact le_max_right _ _
  have hc1 : 1 ≤ c := by
    dsimp [c]
    exact le_max_left _ _
  have hsBsq : Real.sqrt B ^ 2 = (B : ℝ) := Real.sq_sqrt (by positivity)
  have hinside : fro M0 ^ 2 + 2 * rhi * cMConst p.CSig p.γstar * B ≤
      c * T ^ 2 := by
    calc
      _ ≤ c * fro M0 ^ 2 + c * B := add_le_add
        (by nlinarith [mul_le_mul_of_nonneg_right hc1 (sq_nonneg (fro M0))])
        (mul_le_mul_of_nonneg_right hcN (by positivity))
      _ = c * (fro M0 ^ 2 + Real.sqrt B ^ 2) := by rw [hsBsq]; ring
      _ ≤ c * T ^ 2 := by
        exact mul_le_mul_of_nonneg_left (by
          dsimp [T]
          nlinarith [mul_nonneg (movement_fro_nn M0) hsB.le]) hc0
  have he_sq : e ^ 2 = 2 * c * q ^ 2 := by
    dsimp [e]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hc0)]
  have hWEroot : ∀ r, Real.sqrt (∫ ω, fro (W (E r ω)) ^ 2 ∂P) ≤
      e * p.β ^ (r + 1) * T := by
    intro r
    have hI0 : 0 ≤ ∫ ω, fro (W (E r ω)) ^ 2 ∂P :=
      integral_nonneg fun _ ↦ sq_nonneg _
    have hp2 : p.β ^ (2 * (r + 1)) = (p.β ^ (r + 1)) ^ 2 := by
      rw [mul_comm, pow_mul]
    have hmaj : ∫ ω, fro (W (E r ω)) ^ 2 ∂P ≤
        (e * p.β ^ (r + 1) * T) ^ 2 := by
      calc
        _ ≤ 2 * q ^ 2 * p.β ^ (2 * (r + 1)) *
            (fro M0 ^ 2 + 2 * rhi * cMConst p.CSig p.γstar * B) := hWE2bd r
        _ ≤ 2 * q ^ 2 * p.β ^ (2 * (r + 1)) * (c * T ^ 2) := by
          exact mul_le_mul_of_nonneg_left hinside
            (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg q))
              (pow_nonneg p.hβ.1 _))
        _ = e ^ 2 * (p.β ^ (r + 1)) ^ 2 * T ^ 2 := by rw [he_sq]; ring
        _ = (e * p.β ^ (r + 1) * T) ^ 2 := by ring
    simpa using startup_sqrt_sq_major hI0 zero_le_one
      (mul_nonneg (mul_nonneg he0 (pow_nonneg p.hβ.1 _)) hT0) (by simpa using hmaj)
  have hmu2 : fro μ ^ 2 ≤ ∫ ω, fro (V 0 ω) ^ 2 ∂P := by
    have hm := startup_fro_mean_le_sqrt (V 0) (hVmeas 0).aestronglyMeasurable (hV2 0)
    have hI0 : 0 ≤ ∫ ω, fro (V 0 ω) ^ 2 ∂P := integral_nonneg fun _ ↦ sq_nonneg _
    calc
      fro μ ^ 2 ≤ Real.sqrt (∫ ω, fro (V 0 ω) ^ 2 ∂P) ^ 2 := by
        simpa only [μ] using pow_le_pow_left₀ (movement_fro_nn _) hm 2
      _ = _ := Real.sq_sqrt hI0
  have hVc2 : ∀ u, Integrable (fun ω ↦ fro (V u ω - μ) ^ 2) P := by
    intro u
    have hmajor : Integrable (fun ω ↦ 2 * (fro (V u ω) ^ 2 + fro μ ^ 2)) P :=
      ((hV2 u).add (integrable_const _)).const_mul 2
    refine hmajor.mono'
      (startup_fro_sq_meas.comp ((hVmeas u).sub measurable_const)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hs := pow_le_pow_left₀ (movement_fro_nn _)
      (coupling_fro_sub_le (V u ω) μ) 2
    exact hs.trans (coupling_sq_add_le' _ _)
  have hvn_sq : vn ^ 2 = 4 * p.γstar := by
    dsimp [vn]
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) p.hγ)]
  have hVcroot : ∀ u, Real.sqrt (∫ ω, fro (V u ω - μ) ^ 2 ∂P) ≤
      vn * Real.sqrt B := by
    intro u
    have hI0 : 0 ≤ ∫ ω, fro (V u ω - μ) ^ 2 ∂P :=
      integral_nonneg fun _ ↦ sq_nonneg _
    have hmaj : ∫ ω, fro (V u ω - μ) ^ 2 ∂P ≤
        (vn * Real.sqrt B) ^ 2 := by
      calc
        _ ≤ ∫ ω, 2 * (fro (V u ω) ^ 2 + fro μ ^ 2) ∂P := by
          apply integral_mono (hVc2 u) (((hV2 u).add (integrable_const _)).const_mul 2)
          intro ω
          have hs := pow_le_pow_left₀ (movement_fro_nn _)
            (coupling_fro_sub_le (V u ω) μ) 2
          exact hs.trans (coupling_sq_add_le' _ _)
        _ = 2 * ((∫ ω, fro (V u ω) ^ 2 ∂P) + fro μ ^ 2) := by
          rw [integral_const_mul, integral_add (hV2 u) (integrable_const _), integral_const]
          simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
        _ ≤ 4 * (p.γstar * B) := by
          have h0 := hV2bd 0
          have hu := hV2bd u
          nlinarith
        _ = (vn * Real.sqrt B) ^ 2 := by rw [mul_pow, hvn_sq, hsBsq]; ring
    calc
      _ ≤ Real.sqrt ((vn * Real.sqrt B) ^ 2) := Real.sqrt_le_sqrt hmaj
      _ = _ := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hvn0 hsB.le)]
  have hXp := startup_statV_path_aem C cs t D 0 hD hlaw.1
  have hYp : AEMeasurable (fun ω (k : ℕ) ↦
      frozenUpd F FS p.ϱ ((t : ℤ) + (k : ℤ) - 1) ω) P := by
    have heval : Measurable (fun (x : ℤ → Mat m n) (k : ℕ) ↦
        x ((t : ℤ) + (k : ℤ) - 1)) := Measurable.of_eval fun k ↦ measurable_pi_apply _
    exact heval.comp_aemeasurable (startup_updpath_aem F FS p.ϱ p.hϱ.le)
  have hid : IdentDistrib
      (fun ω (k : ℕ) ↦ (def_app_dyn_chains p C cs t D 0 ω).statV k)
      (fun ω (k : ℕ) ↦ frozenUpd F FS p.ϱ ((t : ℤ) + (k : ℤ) - 1) ω) P P :=
    ⟨hXp, hYp, hlaw.2.2.1⟩
  have hmeanV : ∀ u, mean P (V u) =
      mean P (frozenUpd F FS p.ϱ ((t : ℤ) + (u : ℤ))) := by
    intro u
    ext i j
    let f : (ℕ → Mat m n) → ℝ := fun x ↦ x (u + 1) i j
    have hf : Measurable f :=
      (measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp (measurable_pi_apply (u + 1)))
    have hi := (hid.comp hf).integral_eq
    have htime : (t : ℤ) + ((u + 1 : ℕ) : ℤ) - 1 = (t : ℤ) + (u : ℤ) := by
      push_cast
      ring
    simpa only [Function.comp_apply, mean, Matrix.of_apply, f, V, stationaryV, htime] using hi
  have hmeanVbd : ∀ u, fro (mean P (V u)) ≤ max Cm 0 := by
    intro u
    have hh := (hCm m n B Ω P FS F ((t : ℤ) + (u : ℤ))
      hsize.1 hsize.2.1 hsize.2.2).2.2.2 p.ϱ ⟨le_rfl, le_rfl⟩
    have hd : 0 ≤ fro (mean P (fun ω ↦
        dQ p.ϱ (frozenBuf F FS ((t : ℤ) + (u : ℤ)) ω))) := movement_fro_nn _
    have hb : fro (mean P (fun ω ↦
        Q p.ϱ (frozenBuf F FS ((t : ℤ) + (u : ℤ)) ω))) ≤ Cm := by linarith
    rw [hmeanV u]
    have hb' : fro (mean P (frozenUpd F FS p.ϱ ((t : ℤ) + (u : ℤ)))) ≤ Cm := by
      change fro (mean P (fun ω ↦
        Q p.ϱ (frozenBuf F FS ((t : ℤ) + (u : ℤ)) ω))) ≤ Cm
      exact hb
    exact hb'.trans (le_max_left _ _)
  have hVuc2 : ∀ u, Integrable
      (fun ω ↦ fro (V u ω - mean P (V u)) ^ 2) P := fun u ↦
    startup_centered_fro_sq_integrable (V u) (hVmeas u).aemeasurable (hV2 u)
  have hVucroot : ∀ u, Real.sqrt
      (∫ ω, fro (V u ω - mean P (V u)) ^ 2 ∂P) ≤ vn * Real.sqrt B := by
    intro u
    have hI0 : 0 ≤ ∫ ω, fro (V u ω - mean P (V u)) ^ 2 ∂P :=
      integral_nonneg fun _ ↦ sq_nonneg _
    have hmaj : ∫ ω, fro (V u ω - mean P (V u)) ^ 2 ∂P ≤
        (vn * Real.sqrt B) ^ 2 := by
      calc
        _ ≤ 4 * ∫ ω, fro (V u ω) ^ 2 ∂P :=
          startup_centered_fro_sq_bound (V u) (hVmeas u).aemeasurable (hV2 u)
        _ ≤ 4 * (p.γstar * B) := mul_le_mul_of_nonneg_left (hV2bd u) (by norm_num)
        _ = (vn * Real.sqrt B) ^ 2 := by rw [mul_pow, hvn_sq, hsBsq]; ring
    calc
      _ ≤ Real.sqrt ((vn * Real.sqrt B) ^ 2) := Real.sqrt_le_sqrt hmaj
      _ = _ := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hvn0 hsB.le)]
  have hnear : ∀ u r, |∫ ω,
      frobIP (V u ω - mean P (V u)) (W (E r ω)) ∂P| ≤
        cn * p.β ^ (r + 1) * R := by
    intro u r
    have hh := startup_abs_integral_ip_le
      (fun ω ↦ V u ω - mean P (V u)) (fun ω ↦ W (E r ω))
      ((hVmeas u).sub measurable_const).aemeasurable (hWEmeas r).aemeasurable
      (hVuc2 u) (hWE2 r)
    calc
      _ ≤ Real.sqrt (∫ ω, fro (V u ω - mean P (V u)) ^ 2 ∂P) *
          Real.sqrt (∫ ω, fro (W (E r ω)) ^ 2 ∂P) := hh
      _ ≤ (vn * Real.sqrt B) * (e * p.β ^ (r + 1) * T) :=
        mul_le_mul (hVucroot u) (hWEroot r) (Real.sqrt_nonneg _)
          (mul_nonneg hvn0 hsB.le)
      _ = cn * p.β ^ (r + 1) * R := by dsimp [cn, R]; ring
  have hmeanpair : ∀ u r, |∫ ω, frobIP (mean P (V u)) (W (E r ω)) ∂P| ≤
      cm * p.β ^ (r + 1) * T := by
    intro u r
    have hh := startup_abs_integral_ip_le
      (fun _ : Ω ↦ mean P (V u)) (fun ω ↦ W (E r ω))
      measurable_const.aemeasurable (hWEmeas r).aemeasurable
      (integrable_const _) (hWE2 r)
    calc
      _ ≤ Real.sqrt (∫ _ : Ω, fro (mean P (V u)) ^ 2 ∂P) *
          Real.sqrt (∫ ω, fro (W (E r ω)) ^ 2 ∂P) := hh
      _ = fro (mean P (V u)) *
          Real.sqrt (∫ ω, fro (W (E r ω)) ^ 2 ∂P) := by
        simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
          one_smul, Real.sqrt_sq_eq_abs, abs_of_nonneg (movement_fro_nn _)]
      _ ≤ max Cm 0 * (e * p.β ^ (r + 1) * T) :=
        mul_le_mul (hmeanVbd u) (hWEroot r) (Real.sqrt_nonneg _) (le_max_right _ _)
      _ = cm * p.β ^ (r + 1) * T := by dsimp [cm]; ring
  have hρ : 0 ≤ physRidge p C D := by
    unfold physRidge
    exact mul_nonneg (mul_nonneg (by norm_num) hD.le) p.hϱ.le
  have hfar : ∀ r l, |∫ ω,
      frobIP (V (r + l) ω - mean P (V (r + l))) (W (E r ω)) ∂P| ≤
        cf * p.β ^ l * p.β ^ (r + 1) * R := by
    intro r l
    let Z : Ω → Mat m n := fun ω ↦ Q (physRidge p C D)
      (emaChain p.β D (fun s ↦ physBatch C (cs.act s) ω) (t + r + 1) 0 l)
    have hfut := startup_future_indep_error p C cs t D M0 W hD r l
    have hZmeas : Measurable Z := by simpa only [Z] using hfut.1
    have hZ2 : Integrable (fun ω ↦ fro (Z ω) ^ 2) P := by
      refine Integrable.of_bound (C := p.γstar * B)
        (startup_fro_sq_meas.comp hZmeas).aestronglyMeasurable ?_
      exact ae_of_all _ fun ω ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact startup_Q_fro_sq_le p.γstar (physRidge p C D) hρ hsize.1 _
    have hdiff := startup_future_diff_fro_sq_bound C cs t D M0
      rlo rhi hrlo hDlo hDhi hsize r l
    have hdiff2 : Integrable (fun ω ↦ fro (V (r + l) ω - Z ω) ^ 2) P := by
      simpa only [V, Z] using hdiff.1
    have hdiffroot : Real.sqrt (∫ ω, fro (V (r + l) ω - Z ω) ^ 2 ∂P) ≤
        Real.sqrt c * q * p.β ^ l * Real.sqrt B := by
      have hI0 : 0 ≤ ∫ ω, fro (V (r + l) ω - Z ω) ^ 2 ∂P :=
        integral_nonneg fun _ ↦ sq_nonneg _
      have hp2 : p.β ^ (2 * l) = (p.β ^ l) ^ 2 := by rw [mul_comm, pow_mul]
      have hcsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0
      have hmaj : ∫ ω, fro (V (r + l) ω - Z ω) ^ 2 ∂P ≤
          (Real.sqrt c * q * p.β ^ l * Real.sqrt B) ^ 2 := by
        calc
          _ ≤ q ^ 2 * p.β ^ (2 * l) *
              (2 * rhi * cMConst p.CSig p.γstar * B) := by
            simpa only [V, Z, q] using hdiff.2
          _ ≤ q ^ 2 * p.β ^ (2 * l) * (c * B) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hcN (by positivity))
              (mul_nonneg (sq_nonneg q) (pow_nonneg p.hβ.1 _))
          _ = (Real.sqrt c * q * p.β ^ l * Real.sqrt B) ^ 2 := by
            rw [hp2, mul_pow, mul_pow, mul_pow, hcsq, hsBsq]
            ring
      simpa using startup_sqrt_sq_major hI0 zero_le_one
        (mul_nonneg
          (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hq0) (pow_nonneg p.hβ.1 _))
          hsB.le)
        (by simpa using hmaj)
    have hrep := startup_replacement_cov_bound (V (r + l)) (fun ω ↦ W (E r ω)) Z
      (hVmeas (r + l)) (hWEmeas r) hZmeas
      (by simpa only [E, Z] using hfut.2.2)
      (hV2 (r + l)) (hWE2 r) hZ2 hdiff2
    calc
      _ ≤ 2 * Real.sqrt (∫ ω, fro (V (r + l) ω - Z ω) ^ 2 ∂P) *
          Real.sqrt (∫ ω, fro (W (E r ω)) ^ 2 ∂P) := hrep
      _ ≤ 2 * (Real.sqrt c * q * p.β ^ l * Real.sqrt B) *
          (e * p.β ^ (r + 1) * T) := by
        have ha0 : 0 ≤ Real.sqrt c * q * p.β ^ l * Real.sqrt B :=
          mul_nonneg
            (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hq0) (pow_nonneg p.hβ.1 _))
            hsB.le
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hdiffroot (by norm_num))
          (hWEroot r) (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) ha0)
      _ = cf * p.β ^ l * p.β ^ (r + 1) * R := by dsimp [cf, R]; ring
  have hpairInt : ∀ u r, Integrable (fun ω ↦ frobIP (V u ω) (W (E r ω))) P :=
    fun u r ↦ startup_ip_integrable (V u) (fun ω ↦ W (E r ω))
      (hVmeas u).aemeasurable (hWEmeas r).aemeasurable (hV2 u) (hWE2 r)
  have hpair : ∀ u r, |∫ ω, frobIP (V u ω) (W (E r ω)) ∂P| ≤
      cm * p.β ^ (r + 1) * T +
        (if u ≤ r then cn * p.β ^ (r + 1) * R else cf * p.β ^ (u + 1) * R) := by
    intro u r
    have hcint := startup_ip_integrable
      (fun ω ↦ V u ω - mean P (V u)) (fun ω ↦ W (E r ω))
      ((hVmeas u).sub measurable_const).aemeasurable (hWEmeas r).aemeasurable
      (hVuc2 u) (hWE2 r)
    have hmuint := startup_ip_integrable
      (fun _ : Ω ↦ mean P (V u)) (fun ω ↦ W (E r ω))
      measurable_const.aemeasurable (hWEmeas r).aemeasurable (integrable_const _) (hWE2 r)
    have heq : ∫ ω, frobIP (V u ω) (W (E r ω)) ∂P =
        (∫ ω, frobIP (V u ω - mean P (V u)) (W (E r ω)) ∂P) +
          ∫ ω, frobIP (mean P (V u)) (W (E r ω)) ∂P := by
      rw [← integral_add hcint hmuint]
      apply integral_congr_ae
      exact ae_of_all _ fun ω ↦ by
        simp_rw [startup_frobIP_eq_sum, Matrix.sub_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
    rw [heq]
    by_cases hur : u ≤ r
    · rw [if_pos hur]
      calc
        _ ≤ |∫ ω, frobIP (V u ω - mean P (V u)) (W (E r ω)) ∂P| +
            |∫ ω, frobIP (mean P (V u)) (W (E r ω)) ∂P| := abs_add_le _ _
        _ ≤ cn * p.β ^ (r + 1) * R + cm * p.β ^ (r + 1) * T :=
          add_le_add (hnear u r) (hmeanpair u r)
        _ = cm * p.β ^ (r + 1) * T + cn * p.β ^ (r + 1) * R := add_comm _ _
    ·
      rw [if_neg hur]
      have hru : r + (u - r) = u := by omega
      have hh := hfar r (u - r)
      rw [hru] at hh
      have hpow : p.β ^ (u - r) * p.β ^ (r + 1) = p.β ^ (u + 1) := by
        rw [← pow_add]
        congr 1
        omega
      have hh' : |∫ ω, frobIP (V u ω - mean P (V u)) (W (E r ω)) ∂P| ≤
          cf * p.β ^ (u + 1) * R := hh.trans_eq (by
            calc
              cf * p.β ^ (u - r) * p.β ^ (r + 1) * R =
                  cf * (p.β ^ (u - r) * p.β ^ (r + 1)) * R := by ring
              _ = cf * p.β ^ (u + 1) * R := by rw [hpow])
      calc
        _ ≤ |∫ ω, frobIP (V u ω - mean P (V u)) (W (E r ω)) ∂P| +
            |∫ ω, frobIP (mean P (V u)) (W (E r ω)) ∂P| := abs_add_le _ _
        _ ≤ cf * p.β ^ (u + 1) * R + cm * p.β ^ (r + 1) * T :=
          add_le_add hh' (hmeanpair u r)
        _ = cm * p.β ^ (r + 1) * T + cf * p.β ^ (u + 1) * R := add_comm _ _
  have hexpand : ∀ ω, frobIP (S0 ω) (W (A ω)) =
      ∑ u ∈ Finset.range L, ∑ r ∈ Finset.range L,
        frobIP (V u ω) (W (E r ω)) := by
    intro ω
    have hWsum : W (∑ r ∈ Finset.range L, E r ω) =
        ∑ r ∈ Finset.range L, W (E r ω) := by
      exact map_sum W (fun r ↦ E r ω) (Finset.range L)
    dsimp only [S0, A]
    rw [hWsum, startup_frobIP_sum_left]
    apply Finset.sum_congr rfl
    intro u _
    rw [startup_frobIP_sum_right]
  have hintsum : Integrable (fun ω ↦
      ∑ u ∈ Finset.range L, ∑ r ∈ Finset.range L,
        frobIP (V u ω) (W (E r ω))) P :=
    integrable_finsetSum _ fun u _ ↦ integrable_finsetSum _ fun r _ ↦ hpairInt u r
  have hinteq : ∫ ω, frobIP (S0 ω) (W (A ω)) ∂P =
      ∑ u ∈ Finset.range L, ∑ r ∈ Finset.range L,
        ∫ ω, frobIP (V u ω) (W (E r ω)) ∂P := by
    rw [integral_congr_ae (ae_of_all _ hexpand)]
    rw [integral_finsetSum _ (fun u _ ↦ integrable_finsetSum _ fun r _ ↦ hpairInt u r)]
    apply Finset.sum_congr rfl
    intro u _
    rw [integral_finsetSum _ (fun r _ ↦ hpairInt u r)]
  have hgeom : ∑ r ∈ Finset.range L, p.β ^ (r + 1) ≤ g := by
    calc
      _ = p.β * ∑ r ∈ Finset.range L, p.β ^ r := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [pow_succ]
        ring
      _ ≤ p.β * (1 - p.β)⁻¹ :=
        mul_le_mul_of_nonneg_left (coupling_sum_pow_le p L) p.hβ.1
      _ = g := by dsimp [g]; rw [div_eq_mul_inv]
  have hmeanSum : ∑ u ∈ Finset.range L, ∑ r ∈ Finset.range L,
      cm * p.β ^ (r + 1) * T ≤ (L : ℝ) * cm * g * T := by
    have hi : ∑ r ∈ Finset.range L, cm * p.β ^ (r + 1) * T =
        cm * (∑ r ∈ Finset.range L, p.β ^ (r + 1)) * T := by
      rw [Finset.mul_sum, Finset.sum_mul]
    calc
      _ = (L : ℝ) * (cm * (∑ r ∈ Finset.range L, p.β ^ (r + 1)) * T) := by
        rw [show (∑ r ∈ Finset.range L, cm * p.β ^ (r + 1) * T) =
          cm * (∑ r ∈ Finset.range L, p.β ^ (r + 1)) * T from hi]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (L : ℝ) * (cm * g * T) := by
        gcongr
      _ = _ := by ring
  have hnearSum : ∑ u ∈ Finset.range L, ∑ r ∈ Finset.range L,
      (if u ≤ r then cn * p.β ^ (r + 1) * R else 0) ≤ cn * wg * R := by
    calc
      _ = ∑ r ∈ Finset.range L, ∑ u ∈ Finset.range L,
          (if u ≤ r then cn * p.β ^ (r + 1) * R else 0) := Finset.sum_comm
      _ ≤ ∑ r ∈ Finset.range L,
          (r + 1 : ℝ) * (cn * p.β ^ (r + 1) * R) := by
        apply Finset.sum_le_sum
        intro r _
        exact startup_sum_if_le L r _
          (mul_nonneg (mul_nonneg hcn0 (pow_nonneg p.hβ.1 _)) hR0)
      _ = cn * R * ∑ r ∈ Finset.range L, (r + 1 : ℝ) * p.β ^ (r + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ ≤ cn * R * wg := mul_le_mul_of_nonneg_left
        (by simpa only [wg] using startup_weighted_geom p L) (mul_nonneg hcn0 hR0)
      _ = cn * wg * R := by ring
  have hfarSum : ∑ u ∈ Finset.range L, ∑ r ∈ Finset.range L,
      (if r < u then cf * p.β ^ (u + 1) * R else 0) ≤ cf * wg * R := by
    calc
      _ ≤ ∑ u ∈ Finset.range L,
          (u + 1 : ℝ) * (cf * p.β ^ (u + 1) * R) := by
        apply Finset.sum_le_sum
        intro u _
        exact startup_sum_if_lt L u _
          (mul_nonneg (mul_nonneg hcf0 (pow_nonneg p.hβ.1 _)) hR0)
      _ = cf * R * ∑ u ∈ Finset.range L, (u + 1 : ℝ) * p.β ^ (u + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ ≤ cf * R * wg := mul_le_mul_of_nonneg_left
        (by simpa only [wg] using startup_weighted_geom p L) (mul_nonneg hcf0 hR0)
      _ = cf * wg * R := by ring
  have hcenterSum : ∑ u ∈ Finset.range L, ∑ r ∈ Finset.range L,
      (if u ≤ r then cn * p.β ^ (r + 1) * R else cf * p.β ^ (u + 1) * R) ≤
        (cn + cf) * wg * R := by
    calc
      _ ≤ (∑ u ∈ Finset.range L, ∑ r ∈ Finset.range L,
          (if u ≤ r then cn * p.β ^ (r + 1) * R else 0)) +
          ∑ u ∈ Finset.range L, ∑ r ∈ Finset.range L,
          (if r < u then cf * p.β ^ (u + 1) * R else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro u _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro r _
        by_cases hur : u ≤ r
        · simp only [if_pos hur, if_neg (not_lt_of_ge hur), add_zero]
          exact le_rfl
        · have hru : r < u := Nat.lt_of_not_ge hur
          simp only [if_neg hur, if_pos hru, zero_add]
          exact le_rfl
      _ ≤ cn * wg * R + cf * wg * R := add_le_add hnearSum hfarSum
      _ = (cn + cf) * wg * R := by ring
  have hsumBound : |∫ ω, frobIP (S0 ω) (W (A ω)) ∂P| ≤
      (L : ℝ) * cm * g * T + (cn + cf) * wg * R := by
    rw [hinteq]
    calc
      |∑ u ∈ Finset.range L, ∑ r ∈ Finset.range L,
          ∫ ω, frobIP (V u ω) (W (E r ω)) ∂P| ≤
          ∑ u ∈ Finset.range L, abs
            (∑ r ∈ Finset.range L, ∫ ω, frobIP (V u ω) (W (E r ω)) ∂P) :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u ∈ Finset.range L, ∑ r ∈ Finset.range L,
          |∫ ω, frobIP (V u ω) (W (E r ω)) ∂P| := by
        apply Finset.sum_le_sum
        intro u _
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u ∈ Finset.range L, ∑ r ∈ Finset.range L,
          (cm * p.β ^ (r + 1) * T +
            (if u ≤ r then cn * p.β ^ (r + 1) * R else
              cf * p.β ^ (u + 1) * R)) :=
        Finset.sum_le_sum fun u _ ↦ Finset.sum_le_sum fun r _ ↦ hpair u r
      _ = (∑ u ∈ Finset.range L, ∑ r ∈ Finset.range L,
          cm * p.β ^ (r + 1) * T) +
          ∑ u ∈ Finset.range L, ∑ r ∈ Finset.range L,
            (if u ≤ r then cn * p.β ^ (r + 1) * R else
              cf * p.β ^ (u + 1) * R) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_add_distrib]
      _ ≤ (L : ℝ) * cm * g * T + (cn + cf) * wg * R :=
        add_le_add hmeanSum hcenterSum
  have hbase0 : 0 ≤ (cn + cf) * wg + cm * g := by positivity
  have hdom : (L : ℝ) * cm * g * T + (cn + cf) * wg * R ≤
      ((cn + cf) * wg + cm * g) * (R + (L : ℝ) * T) := by
    have hcross1 : 0 ≤ (cn + cf) * wg * ((L : ℝ) * T) :=
      mul_nonneg (mul_nonneg (add_nonneg hcn0 hcf0) hwg0)
        (mul_nonneg (Nat.cast_nonneg L) hT0)
    have hcross2 : 0 ≤ cm * g * R := mul_nonneg (mul_nonneg hcm0 hg0) hR0
    calc
      _ ≤ ((L : ℝ) * cm * g * T + (cn + cf) * wg * R) +
          (cn + cf) * wg * ((L : ℝ) * T) + cm * g * R := by linarith
      _ = _ := by ring
  have hscale : R + (L : ℝ) * T =
      (1 + fro M0 / Real.sqrt B) * (B + (L : ℝ) * Real.sqrt B) := by
    have hBs : (B : ℝ) = Real.sqrt B * Real.sqrt B := by
      calc
        (B : ℝ) = Real.sqrt B ^ 2 := hsBsq.symm
        _ = Real.sqrt B * Real.sqrt B := pow_two _
    have h1 : fro M0 / Real.sqrt B * (B : ℝ) = fro M0 * Real.sqrt B := by
      calc
        fro M0 / Real.sqrt B * (B : ℝ) =
            fro M0 / Real.sqrt B * (Real.sqrt B * Real.sqrt B) :=
          congrArg (fun x : ℝ ↦ fro M0 / Real.sqrt B * x) hBs
        fro M0 / Real.sqrt B * (Real.sqrt B * Real.sqrt B) =
            (fro M0 / Real.sqrt B * Real.sqrt B) * Real.sqrt B := by ring
        _ = fro M0 * Real.sqrt B := by rw [div_mul_cancel₀ _ hsB.ne']
    have h2 : fro M0 / Real.sqrt B * ((L : ℝ) * Real.sqrt B) =
        fro M0 * (L : ℝ) := by
      calc
        fro M0 / Real.sqrt B * ((L : ℝ) * Real.sqrt B) =
            (fro M0 / Real.sqrt B * Real.sqrt B) * (L : ℝ) := by ring
        _ = fro M0 * (L : ℝ) := by rw [div_mul_cancel₀ _ hsB.ne']
    change Real.sqrt B * (fro M0 + Real.sqrt B) +
      (L : ℝ) * (fro M0 + Real.sqrt B) = _
    have hsprod : Real.sqrt B * Real.sqrt B = (B : ℝ) := hBs.symm
    calc
      Real.sqrt B * (fro M0 + Real.sqrt B) +
          (L : ℝ) * (fro M0 + Real.sqrt B) =
          Real.sqrt B * fro M0 + Real.sqrt B * Real.sqrt B +
            (L : ℝ) * fro M0 + (L : ℝ) * Real.sqrt B := by ring
      _ = (B : ℝ) + (L : ℝ) * Real.sqrt B +
            (fro M0 * Real.sqrt B + fro M0 * (L : ℝ)) := by rw [hsprod]; ring
      _ = (B : ℝ) + (L : ℝ) * Real.sqrt B +
            (fro M0 / Real.sqrt B * B +
              fro M0 / Real.sqrt B * ((L : ℝ) * Real.sqrt B)) := by rw [h1, h2]
      _ = (1 + fro M0 / Real.sqrt B) *
          (B + (L : ℝ) * Real.sqrt B) := by ring
  change |∫ ω, frobIP (S0 ω) (W (A ω)) ∂P| ≤
    K * (1 + fro M0 / Real.sqrt B) * (B + (L : ℝ) * Real.sqrt B)
  calc
    _ ≤ (L : ℝ) * cm * g * T + (cn + cf) * wg * R := hsumBound
    _ ≤ ((cn + cf) * wg + cm * g) * (R + (L : ℝ) * T) := hdom
    _ ≤ K * (R + (L : ℝ) * T) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (add_nonneg hR0
        (mul_nonneg (Nat.cast_nonneg L) hT0))
    _ = _ := by rw [hscale]; ring

/-! ## `lem:app-dyn-taylor`: deterministic helpers -/

private lemma taylor_Q_contDiff {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun N : Fin m → Fin n → ℝ => fun i j => Q ℓ (Matrix.of N) i j) := by
  apply contDiff_iff_contDiffAt.mpr
  intro N
  have hQ := (Q_contDiffOn_pos m n).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds
      (show 0 < (N, ℓ).2 from hℓ))
  exact hQ.comp N ((contDiff_id.prodMk contDiff_const).contDiffAt)

private lemma taylor_dd_fderiv {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (N R : Mat m n) (i : Fin m) (j : Fin n) :
    dirDeriv ℓ N R i j = (fderiv ℝ (fun M : Fin m → Fin n → ℝ =>
      fun i j => Q ℓ (Matrix.of M) i j) N) R i j := by
  have hQ := (taylor_Q_contDiff (m := m) (n := n) hℓ).differentiable (by simp)
  set N' : Fin m → Fin n → ℝ := N
  set R' : Fin m → Fin n → ℝ := R
  have hline : HasDerivAt (fun t : ℝ => N' + t • R') R' 0 := by
    exact (hasDerivAt_const_add_iff _).mpr (by
      simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const R')
  have hcomp := (hQ N').hasFDerivAt.comp_hasDerivAt_of_eq 0 hline
    (by simp only [zero_smul, add_zero])
  exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hcomp i) j).deriv)

private lemma taylor_dd_sub {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (N R R' : Mat m n) :
    dirDeriv ℓ N R - dirDeriv ℓ N R' = dirDeriv ℓ N (R - R') := by
  ext i j
  rw [Matrix.sub_apply, taylor_dd_fderiv hℓ, taylor_dd_fderiv hℓ, taylor_dd_fderiv hℓ]
  have h := (fderiv ℝ (fun M : Fin m → Fin n → ℝ =>
      fun i j => Q ℓ (Matrix.of M) i j) (N : Fin m → Fin n → ℝ)).map_sub R R'
  have h2 := congrFun (congrFun h i) j
  simp only [Pi.sub_apply] at h2
  exact h2.symm

private lemma taylor_dd_smul {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (N R : Mat m n) (c : ℝ) :
    dirDeriv ℓ N (c • R) = c • dirDeriv ℓ N R := by
  ext i j
  rw [Matrix.smul_apply, taylor_dd_fderiv hℓ, taylor_dd_fderiv hℓ]
  have h := (fderiv ℝ (fun M : Fin m → Fin n → ℝ =>
      fun i j => Q ℓ (Matrix.of M) i j) (N : Fin m → Fin n → ℝ)).map_smul c R
  have h2 := congrFun (congrFun h i) j
  simp only [Pi.smul_apply] at h2
  exact h2

private lemma taylor_fro_smul {m n : ℕ} (c : ℝ) (X : Mat m n) : fro (c • X) = |c| * fro X := by
  open scoped Matrix.Norms.Frobenius in
  rw [fro_eq_norm, fro_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma taylor_ridge_hasDeriv {m n : ℕ} (K : Mat m n) (i : Fin m) (j : Fin n) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (fun y => Q y K i j) (ridgeDeriv x K i j) x ∧
    HasDerivAt (fun y => ridgeDeriv y K i j) (ridgeDeriv2 x K i j) x := by
  set g : ℝ → ℝ := fun y => Q y K i j with hg
  have hmap : Set.MapsTo (fun y : ℝ => ((K : Fin m → Fin n → ℝ), y)) (Set.Ioi 0)
      {p : (Fin m → Fin n → ℝ) × ℝ | 0 < p.2} := fun y hy => hy
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => fun i j => Q y (Matrix.of (K : Fin m → Fin n → ℝ)) i j)
      (Set.Ioi 0) :=
    (Q_contDiffOn_pos m n).comp (contDiffOn_const.prodMk contDiffOn_id) hmap
  have hgc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (Set.Ioi 0) := by
    have := contDiffOn_pi.1 (contDiffOn_pi.1 hc i) j
    exact this
  have hd1 : DifferentiableAt ℝ g x :=
    (hgc.differentiableOn (by simp) x hx).differentiableAt (Ioi_mem_nhds hx)
  have hrd : (fun y => ridgeDeriv y K i j) = deriv g := by
    funext y
    simp [ridgeDeriv, hg]
  have hgc' : ContDiffOn ℝ 1 (deriv g) (Set.Ioi 0) :=
    hgc.deriv_of_isOpen isOpen_Ioi (by simp)
  have hd2 : DifferentiableAt ℝ (deriv g) x :=
    (hgc'.differentiableOn (by simp) x hx).differentiableAt (Ioi_mem_nhds hx)
  refine ⟨?_, ?_⟩
  · have := hd1.hasDerivAt
    simpa [ridgeDeriv, hg] using this
  · rw [hrd]
    have := hd2.hasDerivAt
    have e : ridgeDeriv2 x K i j = deriv (deriv g) x := by
      simp only [ridgeDeriv2, Matrix.of_apply]
      rw [hrd]
    rw [e]
    exact this

private lemma taylor_fro_add {m n : ℕ} (X Y : Mat m n) : fro (X + Y) ≤ fro X + fro Y := by
  open scoped Matrix.Norms.Frobenius in
  simpa only [fro_eq_norm] using norm_add_le X Y

private lemma taylor_fro_nn {m n : ℕ} (X : Mat m n) : 0 ≤ fro X := Real.sqrt_nonneg _

private lemma taylor_abs_sum_le {m n : ℕ} (X Y : Mat m n) :
    |∑ i, ∑ j, X i j * Y i j| ≤ fro X * fro Y := by
  have htr : ∑ i, ∑ j, X i j * Y i j = ∑ x : Fin m × Fin n, X x.1 x.2 * Y x.1 x.2 := by
    simp [Fintype.sum_prod_type]
  rw [htr]
  calc
    |∑ x : Fin m × Fin n, X x.1 x.2 * Y x.1 x.2| ≤
        ∑ x : Fin m × Fin n, |X x.1 x.2| * |Y x.1 x.2| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun x : Fin m × Fin n => X x.1 x.2 * Y x.1 x.2) Finset.univ
    _ ≤ _ := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m × Fin n))
        (fun x => |X x.1 x.2|) (fun x => |Y x.1 x.2|)
      simpa [fro, Fintype.sum_prod_type, Real.norm_eq_abs] using h

private lemma taylor_sum_self {m n : ℕ} (X : Mat m n) : ∑ i, ∑ j, X i j * X i j = fro X ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq]

private lemma taylor_ridge_taylor {m n : ℕ} {ℓlo ℓhi C2 : ℝ} (hlo : 0 < ℓlo) (K : Mat m n)
    (hC2 : ∀ x ∈ Icc ℓlo ℓhi, fro (ridgeDeriv2 x K) ≤ C2) {ℓ ℓ' : ℝ}
    (hℓ : ℓ ∈ Icc ℓlo ℓhi) (hℓ' : ℓ' ∈ Icc ℓlo ℓhi) :
    fro (Q ℓ' K - Q ℓ K - (ℓ' - ℓ) • ridgeDeriv ℓ K) ≤ C2 * (ℓ' - ℓ) ^ 2 := by
  set Rm := Q ℓ' K - Q ℓ K - (ℓ' - ℓ) • ridgeDeriv ℓ K with hRm
  have hC2n : 0 ≤ C2 := (taylor_fro_nn _).trans (hC2 ℓ hℓ)
  have hs : Set.uIcc ℓ ℓ' ⊆ Icc ℓlo ℓhi := Set.uIcc_subset_Icc hℓ hℓ'
  have hpos : ∀ x ∈ Set.uIcc ℓ ℓ', 0 < x := fun x hx => lt_of_lt_of_le hlo (hs hx).1
  set ψ : ℝ → ℝ := fun y => ∑ i, ∑ j, Rm i j * (ridgeDeriv y K i j - ridgeDeriv ℓ K i j) with hψ
  set φ : ℝ → ℝ := fun y => ∑ i, ∑ j, Rm i j *
    (Q y K i j - Q ℓ K i j - (y - ℓ) * ridgeDeriv ℓ K i j) with hφ
  have hψd : ∀ x ∈ Set.uIcc ℓ ℓ', HasDerivWithinAt ψ (∑ i, ∑ j, Rm i j * ridgeDeriv2 x K i j)
      (Set.uIcc ℓ ℓ') x := by
    intro x hx
    have : HasDerivAt ψ (∑ i, ∑ j, Rm i j * ridgeDeriv2 x K i j) x := by
      apply HasDerivAt.fun_sum
      intro i _
      apply HasDerivAt.fun_sum
      intro j _
      have h := ((taylor_ridge_hasDeriv K i j (hpos x hx)).2.sub_const (ridgeDeriv ℓ K i j)).const_mul (Rm i j)
      simpa using h
    exact this.hasDerivWithinAt
  have hψb : ∀ x ∈ Set.uIcc ℓ ℓ', ‖∑ i, ∑ j, Rm i j * ridgeDeriv2 x K i j‖ ≤ fro Rm * C2 := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact (taylor_abs_sum_le _ _).trans (mul_le_mul_of_nonneg_left (hC2 x (hs hx)) (taylor_fro_nn _))
  have hψℓ : ψ ℓ = 0 := by simp [hψ]
  have hψx : ∀ x ∈ Set.uIcc ℓ ℓ', ‖ψ x‖ ≤ fro Rm * C2 * |ℓ' - ℓ| := by
    intro x hx
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hψd hψb (convex_uIcc ℓ ℓ')
      (Set.left_mem_uIcc) hx
    rw [hψℓ, sub_zero, Real.norm_eq_abs (x - ℓ)] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc hx)
      (mul_nonneg (taylor_fro_nn _) hC2n))
  have hφd : ∀ x ∈ Set.uIcc ℓ ℓ', HasDerivWithinAt φ (ψ x) (Set.uIcc ℓ ℓ') x := by
    intro x hx
    have : HasDerivAt φ (ψ x) x := by
      apply HasDerivAt.fun_sum
      intro i _
      apply HasDerivAt.fun_sum
      intro j _
      have h1 := (taylor_ridge_hasDeriv K i j (hpos x hx)).1
      have h2 := ((hasDerivAt_id x).sub_const ℓ).mul_const (ridgeDeriv ℓ K i j)
      have h := ((h1.sub_const (Q ℓ K i j)).sub h2).const_mul (Rm i j)
      convert h using 1 <;> simp
    exact this.hasDerivWithinAt
  have hφ' := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hφd hψx (convex_uIcc ℓ ℓ')
    (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have hφℓ : φ ℓ = 0 := by simp [hφ]
  have hφℓ' : φ ℓ' = fro Rm ^ 2 := by
    rw [← taylor_sum_self]
    simp only [hφ, hRm, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hφℓ, hφℓ', sub_zero, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs] at hφ'
  have hf := taylor_fro_nn Rm
  have hq : 0 ≤ C2 * (ℓ' - ℓ) ^ 2 := by positivity
  have hsq : |ℓ' - ℓ| * |ℓ' - ℓ| = (ℓ' - ℓ) ^ 2 := by rw [← sq, sq_abs]
  have hφ'' : fro Rm ^ 2 ≤ fro Rm * (C2 * (ℓ' - ℓ) ^ 2) := by
    calc fro Rm ^ 2 ≤ fro Rm * C2 * |ℓ' - ℓ| * |ℓ' - ℓ| := hφ'
      _ = fro Rm * (C2 * (ℓ' - ℓ) ^ 2) := by rw [← hsq]; ring
  nlinarith

private lemma taylor_det {ℓlo ℓhi : ℝ} (hlo : 0 < ℓlo) (hle : ℓlo ≤ ℓhi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m n : ℕ} (ℓ ℓ' a : ℝ), ℓ ∈ Icc ℓlo ℓhi → ℓ' ∈ Icc ℓlo ℓhi →
      ∀ N M X : Mat m n,
      fro (Q ℓ' M - Q ℓ N - (dirDeriv ℓ N X + a • ridgeDeriv ℓ N)) ≤
        C * Real.sqrt ((min m n : ℕ) : ℝ) * (ℓ' - ℓ) ^ 2 + C * |ℓ' - ℓ| * fro (M - N) +
        C * Real.sqrt ((min m n : ℕ) : ℝ) * |ℓ' - ℓ - a| + C * opNorm (M - N) * fro (M - N) +
        ℓlo ^ (-(1 / 2 : ℝ)) * fro (M - N - X) := by
  obtain ⟨C2, hC2⟩ := lem_app_dyn_second_ii hlo hle
  obtain ⟨C4, hC4⟩ := lem_app_dyn_second_iv hlo hle
  refine ⟨max (max C2 C4) 0, le_max_right _ _, ?_⟩
  intro m n ℓ ℓ' a hℓ hℓ' N M X
  set C := max (max C2 C4) 0 with hCdef
  have hC2C : C2 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC4C : C4 ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC0 : 0 ≤ C := le_max_right _ _
  have hℓpos : 0 < ℓ := lt_of_lt_of_le hlo hℓ.1
  set sq := Real.sqrt ((min m n : ℕ) : ℝ) with hsqdef
  have hsq : 0 ≤ sq := Real.sqrt_nonneg _
  set T1 := Q ℓ' M - Q ℓ M - (ℓ' - ℓ) • ridgeDeriv ℓ M with hT1
  set T2 := (ℓ' - ℓ) • (ridgeDeriv ℓ M - ridgeDeriv ℓ N) with hT2
  set T3 := (ℓ' - ℓ - a) • ridgeDeriv ℓ N with hT3
  set T4 := Q ℓ (N + (M - N)) - Q ℓ N - dirDeriv ℓ N (M - N) with hT4
  set T5 := dirDeriv ℓ N (M - N - X) with hT5
  have hsplit : Q ℓ' M - Q ℓ N - (dirDeriv ℓ N X + a • ridgeDeriv ℓ N) =
      T1 + T2 + T3 + T4 + T5 := by
    have h5 : T5 = dirDeriv ℓ N (M - N) - dirDeriv ℓ N X := (taylor_dd_sub hℓpos N (M - N) X).symm
    have hNM : N + (M - N) = M := by abel
    rw [h5, hT1, hT2, hT3, hT4, hNM]
    module
  have b1 : fro T1 ≤ C * sq * (ℓ' - ℓ) ^ 2 := by
    have hb : ∀ x ∈ Icc ℓlo ℓhi, fro (ridgeDeriv2 x M) ≤ C4 * sq := by
      intro x hx
      have := (hC4 x hx M M).2.1
      linarith [taylor_fro_nn (ridgeDeriv x M)]
    have h := taylor_ridge_taylor hlo M hb hℓ hℓ'
    calc fro T1 ≤ C4 * sq * (ℓ' - ℓ) ^ 2 := h
      _ ≤ C * sq * (ℓ' - ℓ) ^ 2 := by gcongr
  have b2 : fro T2 ≤ C * |ℓ' - ℓ| * fro (M - N) := by
    rw [hT2, taylor_fro_smul]
    have h := (hC4 ℓ hℓ M N).2.2
    have h' := mul_le_mul_of_nonneg_left h (abs_nonneg (ℓ' - ℓ))
    have h'' : |ℓ' - ℓ| * (C4 * fro (M - N)) ≤ C * |ℓ' - ℓ| * fro (M - N) := by
      have := mul_le_mul_of_nonneg_right hC4C (mul_nonneg (abs_nonneg (ℓ' - ℓ)) (taylor_fro_nn (M - N)))
      nlinarith
    linarith
  have b3 : fro T3 ≤ C * sq * |ℓ' - ℓ - a| := by
    rw [hT3, taylor_fro_smul]
    have h := (hC4 ℓ hℓ N N).2.1
    have h1 : fro (ridgeDeriv ℓ N) ≤ C4 * sq := by linarith [taylor_fro_nn (ridgeDeriv2 ℓ N)]
    have h' := mul_le_mul_of_nonneg_left h1 (abs_nonneg (ℓ' - ℓ - a))
    have h'' := mul_le_mul_of_nonneg_right hC4C (mul_nonneg (abs_nonneg (ℓ' - ℓ - a)) hsq)
    nlinarith
  have b4 : fro T4 ≤ C * opNorm (M - N) * fro (M - N) := by
    have h := hC2 ℓ hℓ N (M - N)
    have hop : 0 ≤ opNorm (M - N) := by unfold opNorm; exact norm_nonneg _
    have h' := mul_le_mul_of_nonneg_right hC2C (mul_nonneg hop (taylor_fro_nn (M - N)))
    rw [hT4]
    nlinarith
  have b5 : fro T5 ≤ ℓlo ^ (-(1 / 2 : ℝ)) * fro (M - N - X) := by
    refine (lem_app_dyn_second_i hlo hle ℓ hℓ N _).trans ?_
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hlo hℓ.1 (by norm_num))
      (taylor_fro_nn _)
  rw [hsplit]
  have t1 := taylor_fro_add (T1 + T2 + T3 + T4) T5
  have t2 := taylor_fro_add (T1 + T2 + T3) T4
  have t3 := taylor_fro_add (T1 + T2) T3
  have t4 := taylor_fro_add T1 T2
  linarith

private lemma taylor_Qclamp_cont {m n : ℕ} {c : ℝ} (hc : 0 < c) (i : Fin m) (j : Fin n) :
    Continuous (fun p : Mat m n × ℝ => Q (max p.2 c) p.1 i j) := by
  have hΦ := (Q_contDiffOn_pos m n).continuousOn
  have h1 : Continuous (fun p : Mat m n × ℝ => ((p.1 : Fin m → Fin n → ℝ), max p.2 c)) := by
    fun_prop
  have h2 := hΦ.comp_continuous h1
    (fun p => show (0 : ℝ) < max p.2 c from lt_of_lt_of_le hc (le_max_right _ _))
  exact (continuous_apply j).comp ((continuous_apply i).comp h2)

private lemma taylor_dd_meas {Ω : Type*} {σ : MeasurableSpace Ω} {m n : ℕ} {c : ℝ} (hc : 0 < c)
    {ℓ : Ω → ℝ} {N X : Ω → Mat m n} (hℓ : Measurable[σ] ℓ) (hN : Measurable[σ] N)
    (hX : Measurable[σ] X) :
    Measurable[σ] (fun ω => dirDeriv (max (ℓ ω) c) (N ω) (X ω)) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  have hf : Continuous (fun q : (ℝ × Mat m n × Mat m n) × ℝ =>
      Q (max q.1.1 c) (q.1.2.1 + q.2 • q.1.2.2) i j) := by
    have h := taylor_Qclamp_cont (m := m) (n := n) hc i j
    exact h.comp (by fun_prop : Continuous fun q : (ℝ × Mat m n × Mat m n) × ℝ =>
      (q.1.2.1 + q.2 • q.1.2.2, q.1.1))
  have hm := measurable_deriv_with_param
    (f := fun (a : ℝ × Mat m n × Mat m n) (s : ℝ) => Q (max a.1 c) (a.2.1 + s • a.2.2) i j) hf
  exact hm.comp ((hℓ.prodMk (hN.prodMk hX)).prodMk (measurable_const (a := (0 : ℝ))))

private lemma taylor_rd_clamp {m n : ℕ} {c ℓ : ℝ} (hcℓ : c < ℓ) (N : Mat m n) :
    ridgeDeriv ℓ N = Matrix.of fun i j => deriv (fun x => Q (max x c) N i j) ℓ := by
  ext i j
  simp only [ridgeDeriv, Matrix.of_apply]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hcℓ] with x hx
  rw [max_eq_left (le_of_lt hx)]

private lemma taylor_rd_meas {Ω : Type*} {σ : MeasurableSpace Ω} {m n : ℕ} {c : ℝ} (hc : 0 < c)
    {ℓ : Ω → ℝ} {N : Ω → Mat m n} (hℓ : Measurable[σ] ℓ) (hN : Measurable[σ] N) :
    Measurable[σ] (fun ω => (Matrix.of fun i j => deriv (fun x => Q (max x c) (N ω) i j) (ℓ ω) :
      Mat m n)) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  have hf : Continuous (fun q : Mat m n × ℝ => Q (max q.2 c) q.1 i j) :=
    taylor_Qclamp_cont hc i j
  have hm := measurable_deriv_with_param
    (f := fun (a : Mat m n) (x : ℝ) => Q (max x c) a i j) hf
  exact hm.comp (hN.prodMk hℓ)


/-! ## `lem:app-dyn-taylor`: algebraic and pathwise helpers -/

private lemma taylor_pair_symm {m n : ℕ} (C : Covariances m n) (A E : Mat m n) :
    pairSigma C A E = pairSigma C E A := by
  have ho : C.Soutᵀ = C.Sout := C.psdOut.isHermitian.eq
  have hi : C.Sinᵀ = C.Sin := C.psdIn.isHermitian.eq
  unfold pairSigma
  rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose, ho, hi]
  simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_comm (E * C.Sin * Aᵀ) C.Sout)

private lemma taylor_pair_add_right {m n : ℕ} (C : Covariances m n) (A X Y : Mat m n) :
    pairSigma C A (X + Y) = pairSigma C A X + pairSigma C A Y := by
  unfold pairSigma
  rw [Matrix.transpose_add, Matrix.mul_add, Matrix.trace_add]

private lemma taylor_pair_smul_right {m n : ℕ} (C : Covariances m n) (A X : Mat m n) (c : ℝ) :
    pairSigma C A (c • X) = c * pairSigma C A X := by
  unfold pairSigma
  rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

private lemma taylor_risk_add {m n : ℕ} (C : Covariances m n) (D E : Mat m n) :
    riskSigma C (D + E) = riskSigma C D + pairSigma C D E + riskSigma C E := by
  have h1 : pairSigma C (D + E) (D + E) = pairSigma C D D + pairSigma C D E +
      pairSigma C E D + pairSigma C E E := by
    unfold pairSigma
    simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
    ring
  unfold riskSigma
  rw [h1, taylor_pair_symm C E D]
  ring

private lemma taylor_pair_bound (p : DynParams) {m n B : ℕ} (C : Covariances m n)
    (hsize : SizeFin C B p.γstar p.CSig) (D Y : Mat m n) :
    |pairSigma C D Y| ≤ Real.sqrt (2 * riskSigma C D) * (p.CSig * fro Y) := by
  have hpol : pairSigma C D Y = riskSigma C (D + Y) - riskSigma C D - riskSigma C Y := by
    rw [taylor_risk_add]; ring
  have hArot : Arot C (D + Y) = Arot C D + Arot C Y := by
    simp [Arot, Matrix.mul_add, Matrix.add_mul]
  have hip : fro (Arot C D + Arot C Y) ^ 2 / 2 - fro (Arot C D) ^ 2 / 2 - fro (Arot C Y) ^ 2 / 2 =
      frobIP (Arot C D) (Arot C Y) := by
    rw [movement_fro_sq, movement_fro_sq, movement_fro_sq, startup_frobIP_eq_sum]
    simp only [Matrix.add_apply, add_sq, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  rw [movement_risk_sqrt, hpol, eqn_app_setup_whitened_risk, eqn_app_setup_whitened_risk,
    eqn_app_setup_whitened_risk, hArot, hip]
  refine (startup_frobIP_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (movement_Arot_bound p C hsize Y) (movement_fro_nn _)

private lemma taylor_grad_add {m n B : ℕ} (D1 D2 : Mat m n) (b : Batch m n B) :
    grad (D1 + D2) b = grad D1 b + grad D2 b := by
  unfold grad resid
  simp [Matrix.add_mulVec, dotProduct_add, add_smul, Finset.sum_add_distrib, smul_add]

private lemma taylor_grad_smul {m n B : ℕ} (c : ℝ) (D : Mat m n) (b : Batch m n B) :
    grad (c • D) b = c • grad D b := by
  unfold grad resid
  simp [Matrix.smul_mulVec, dotProduct_smul, smul_smul, Finset.smul_sum, mul_comm, mul_assoc]

private lemma taylor_grad_sum {m n B : ℕ} (k : ℕ) (D : ℕ → Mat m n) (b : Batch m n B) :
    grad (∑ i ∈ Finset.range k, D i) b = ∑ i ∈ Finset.range k, grad (D i) b := by
  induction k with
  | zero => simp [coupling_grad_zero]
  | succ k ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, taylor_grad_add, ih]

private lemma taylor_delta_sum {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) (t j : ℕ) :
    dynDelta S (t + j) ω - dynDelta S t ω =
      -((p.h / B) • ∑ k ∈ Finset.range j, dynUpd S (t + k) ω) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, movement_delta_succ, Finset.sum_range_succ, smul_add]
    rw [show dynDelta S (t + j) ω - (p.h / B) • dynUpd S (t + j) ω - dynDelta S t ω =
      (dynDelta S (t + j) ω - dynDelta S t ω) - (p.h / B) • dynUpd S (t + j) ω by abel, ih]
    abel

private lemma taylor_batch_eq {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) (t j : ℕ) :
    physBatch S.C (S.cs.act ((t : ℤ) + (j : ℤ) + 1)) ω = dynBatch S (t + j) ω := by
  unfold dynBatch
  congr 3

/-- The scaled tangent buffer `λ Ṁ_r` as an EMA of gradients of the first-order states. -/
private lemma taylor_tangentM_smul {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) (t r : ℕ) :
    (p.h / B) • tangentM p S.C (fun s => physBatch S.C (S.cs.act s) ω) t (dynDelta S t ω)
        (dynBuf S t ω) r =
      ∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) •
        batchGrad (-((p.h / B) • ∑ k ∈ Finset.range j, dynHatV p S t k ω))
          (dynBatch S (t + j) ω) := by
  unfold tangentM
  rw [smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  change -((p.h / B) • ∑ k ∈ Finset.range j, emaW p.β (r - j) • batchGrad (dynHatV p S t k ω)
    (physBatch S.C (S.cs.act ((t : ℤ) + (j : ℤ) + 1)) ω)) = _
  rw [taylor_batch_eq]
  rw [← Finset.smul_sum, smul_comm, ← taylor_grad_sum, ← taylor_grad_smul, ← smul_neg]
  congr 1
  have hz : ∀ Z : Mat m n, batchGrad (-Z) (dynBatch S (t + j) ω) =
      -batchGrad Z (dynBatch S (t + j) ω) := by
    intro Z
    rw [← neg_one_smul ℝ Z]
    change grad ((-1 : ℝ) • Z) _ = -grad Z _
    rw [taylor_grad_smul, neg_one_smul]
  rw [hz]

/-- The first-order state error `Y_j = Δ_{t+j} − Δ_t − E^{(1)}_j` (on the event `A`). -/
private def taylorY {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (A : Set Ω) (t j : ℕ) : Ω → Mat m n :=
  A.indicator (fun ω => dynDelta S (t + j) ω - dynDelta S t ω +
    (p.h / B) • ∑ k ∈ Finset.range j, dynHatV p S t k ω)

private lemma taylorY_eq {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (t j : ℕ) (ω : Ω) :
    dynDelta S (t + j) ω - dynDelta S t ω + (p.h / B) • ∑ k ∈ Finset.range j, dynHatV p S t k ω =
      -((p.h / B) • ∑ k ∈ Finset.range j, dynErrS p S t k ω) := by
  rw [taylor_delta_sum]
  simp only [dynErrS, Finset.sum_sub_distrib, smul_sub]
  abel

private lemma taylor_RX_eq {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (A : Set Ω) (t r : ℕ) (ω : Ω) :
    A.indicator (fun ω => dynErrM p S t r ω - (p.h / B) •
      tangentM p S.C (fun s => physBatch S.C (S.cs.act s) ω) t (dynDelta S t ω)
        (dynBuf S t ω) r) ω =
      ∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) •
        batchGrad (taylorY S A t j ω) (dynBatch S (t + j) ω) := by
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω, taylor_tangentM_smul]
    have h := coupling_errM_unroll S t ω (r + 1)
    simp only [Nat.add_sub_cancel] at h
    change dynBuf S (t + (r + 1)) ω - emaChain p.β (dynDelta S t ω)
      (fun s => physBatch S.C (S.cs.act s) ω) t (dynBuf S t ω) (r + 1) - _ = _
    rw [h, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_sub, ← coupling_grad_sub]
    simp only [taylorY, Set.indicator_of_mem hω]
    congr 2
    abel
  · rw [Set.indicator_of_notMem hω]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [taylorY, Set.indicator_of_notMem hω, coupling_grad_zero, smul_zero]


/-! ## `lem:app-dyn-taylor`: tangent formula, measurability and conditional bounds -/

private lemma taylor_tangent_eq {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (t r : ℕ) (ω : Ω)
    (hD : 0 < riskSigma S.C (dynDelta S t ω)) :
    dynTangent p S t r ω =
      dirDeriv (physRidge p S.C (dynDelta S t ω)) (dynHatN p S t r ω)
          (tangentM p S.C (fun s => physBatch S.C (S.cs.act s) ω) t (dynDelta S t ω)
            (dynBuf S t ω) r)
        + (-(2 * p.ϱ * pairSigma S.C (dynDelta S t ω)
            (∑ k ∈ Finset.range r, dynHatV p S t k ω))) •
          ridgeDeriv (physRidge p S.C (dynDelta S t ω)) (dynHatN p S t r ω) := by
  have h := (lem_app_dyn_tangent p S.C (fun s => physBatch S.C (S.cs.act s) ω) t
    (dynDelta S t ω) (dynBuf S t ω) hD).2.2 r
  ext i j
  exact (h i j).deriv

private lemma taylor_ema_past {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (t i : ℕ) :
    Measurable[dynPast S (t + i)] (fun ω => emaChain p.β (dynDelta S t ω)
      (fun s => physBatch S.C (S.cs.act s) ω) t (dynBuf S t ω) i) := by
  induction i with
  | zero => simpa [emaChain] using (buffer_state_meas S t).2
  | succ i ih =>
    have hle := buffer_past_mono S (show t + i ≤ t + (i + 1) by omega)
    have hD := (buffer_delta_meas S t).mono
      (buffer_past_mono S (show t ≤ t + (i + 1) by omega)) le_rfl
    have hb : Measurable[dynPast S (t + (i + 1))]
        (fun ω => physBatch S.C (S.cs.act ((t : ℤ) + (i : ℤ) + 1)) ω) := by
      have h := buffer_batch_meas S (t + i)
      have e : (fun ω => physBatch S.C (S.cs.act ((t : ℤ) + (i : ℤ) + 1)) ω) = dynBatch S (t + i) :=
        funext fun ω => taylor_batch_eq S ω t i
      rw [e]
      exact h
    have hg := buffer_grad_meas hD hb
    simp only [emaChain]
    exact ((ih.mono hle le_rfl).const_smul p.β).add (hg.const_smul (1 - p.β))

private lemma taylor_Q_meas_sigma {Ω : Type*} {σ : MeasurableSpace Ω} {m n : ℕ}
    {ρ : Ω → ℝ} (hρ : Measurable[σ] ρ) (hρ0 : ∀ ω, 0 ≤ ρ ω) {K : Ω → Mat m n}
    (hK : Measurable[σ] K) : Measurable[σ] (fun ω => Q (ρ ω) (K ω)) := by
  have hρm : Measurable[σ] (fun ω => (⟨ρ ω, hρ0 ω⟩ : Set.Ici (0 : ℝ))) := hρ.subtype_mk
  exact measurable_Q.comp (hρm.prodMk hK)

private lemma taylor_hatV_past {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (t k : ℕ) :
    Measurable[dynPast S (t + (k + 1))] (dynHatV p S t k) := by
  have hN := taylor_ema_past S t (k + 1)
  have hD := (buffer_delta_meas S t).mono
    (buffer_past_mono S (Nat.le_add_right t (k + 1))) le_rfl
  have hρ : Measurable[dynPast S (t + (k + 1))] (fun ω => physRidge p S.C (dynDelta S t ω)) :=
    ((coupling_risk_meas S.C hD).const_mul 2).mul_const p.ϱ
  exact taylor_Q_meas_sigma hρ (fun ω => coupling_ridge_nonneg (p := p) S.C _) hN

private lemma taylorY_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) {A : Set Ω} {t : ℕ}
    (hA : MeasurableSet[dynPast S t] A) (j : ℕ) :
    Measurable[dynPast S (t + j)] (taylorY S A t j) := by
  have h1 := buffer_delta_meas S (t + j)
  have h2 := (buffer_delta_meas S t).mono (buffer_past_mono S (Nat.le_add_right t j)) le_rfl
  have h3 : Measurable[dynPast S (t + j)]
      (fun ω => ∑ k ∈ Finset.range j, dynHatV p S t k ω) := by
    refine Finset.measurable_sum _ fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    exact (taylor_hatV_past S t k).mono (buffer_past_mono S (by omega)) le_rfl
  exact ((h1.sub h2).add (h3.const_smul (p.h / (B : ℝ)))).indicator
    (buffer_past_mono S (Nat.le_add_right t j) _ hA)

private lemma taylor_grad_cond {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (hB : 0 < B)
    {t u : ℕ} (htu : t ≤ u) (D : Ω → Mat m n) (hD : Measurable[dynPast S u] D) (c : ℝ)
    (hc : ∀ ω, fro (rOut S.C * D ω * rIn S.C) ^ 2 ≤ c) :
    Integrable (fun ω => fro (batchGrad (D ω) (dynBatch S u ω)) ^ 2) P ∧
    Integrable (fun ω => fro (rOut S.C * D ω * rIn S.C) ^ 2) P ∧
    ∀ᵐ ω ∂P, condExp (dynPast S t) P
      (fun ω' => fro (batchGrad (D ω') (dynBatch S u ω')) ^ 2) ω ≤
        cMConst p.CSig p.γstar * B *
          condExp (dynPast S t) P (fun ω' => fro (rOut S.C * D ω' * rIn S.C) ^ 2) ω := by
  have hrotD : Measurable[dynPast S u] (fun ω => rOut S.C * D ω * rIn S.C) := by
    apply buffer_mat_meas
    intro i j
    simp only [Matrix.mul_apply]
    fun_prop
  have hsq : Measurable[dynPast S u] (fun ω => fro (rOut S.C * D ω * rIn S.C) ^ 2) :=
    buffer_fro_sq_meas.comp hrotD
  have hEint : Integrable (fun ω => fro (rOut S.C * D ω * rIn S.C) ^ 2) P :=
    Integrable.of_bound (hsq.mono (buffer_past_le S u) le_rfl).aestronglyMeasurable c
      (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hc ω)
  obtain ⟨⟨hGint, hcond⟩, _⟩ := lem_app_dyn_batch_iv (dynPast S u) S.C p.γstar p.CSig
    hB S.size (S.cs.act ((u : ℤ) + 1)) (buffer_iid S u) (buffer_past_le S u)
    (buffer_indep_past_batch S u) D hD hEint
  refine ⟨hGint, hEint, ?_⟩
  set κ : ℝ := cMConst p.CSig p.γstar * (B : ℝ) with hκ
  set g : Ω → ℝ := fun ω => fro (rOut S.C * D ω * rIn S.C) ^ 2 with hg
  have h1 := condExp_condExp_of_le (μ := P)
    (f := fun ω' => fro (batchGrad (D ω') (dynBatch S u ω')) ^ 2)
    (buffer_past_mono S htu) (buffer_past_le S u)
  have hc' : condExp (dynPast S u) P (fun ω' => fro (batchGrad (D ω') (dynBatch S u ω')) ^ 2)
      ≤ᵐ[P] κ • g := by
    filter_upwards [hcond] with ω hω
    exact hω
  have h2 := condExp_mono (m := dynPast S t) integrable_condExp (hEint.smul κ) hc'
  have h3 := condExp_smul (μ := P) κ g (dynPast S t)
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  rw [← e1]
  refine e2.trans (le_of_eq ?_)
  rw [e3]
  simp [smul_eq_mul]

private lemma taylor_cond_mono {Ω : Type*} (F : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
    {P : Measure Ω} (f g : Ω → ℝ) (hg : Integrable g P) (c : ℝ)
    (hc : ∀ᵐ ω ∂P, condExp F P g ω ≤ c) (hf : AEStronglyMeasurable f P) (hf0 : ∀ ω, 0 ≤ f ω)
    (hfg : ∀ ω, f ω ≤ g ω) : Integrable f P ∧ ∀ᵐ ω ∂P, condExp F P f ω ≤ c := by
  have hfi : Integrable f P := by
    refine Integrable.mono' hg hf (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (hf0 ω)]
    exact hfg ω
  refine ⟨hfi, ?_⟩
  have hm := condExp_mono (m := F) hfi hg (ae_of_all _ hfg)
  filter_upwards [hm, hc] with ω h1 h2
  exact h1.trans h2

private lemma taylor_ind_sq {Ω : Type*} (A : Set Ω) (g : Ω → ℝ) (ω : Ω) :
    (A.indicator g ω) ^ 2 = A.indicator (fun ω => g ω ^ 2) ω := by
  by_cases h : ω ∈ A <;> simp [h]

private lemma taylor_fro_cont {m n : ℕ} : Continuous (fun A : Mat m n => fro A) := by
  unfold fro
  fun_prop

private lemma taylor_cond4 {Ω : Type*} (F : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hF : F ≤ m0) (a0 w1 w2 w3 w4 c1 c2 c3 c4 : ℝ)
    (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3) (hw4 : 0 ≤ w4) (f1 f2 f3 f4 : Ω → ℝ)
    (hf1 : Integrable f1 P) (hf2 : Integrable f2 P) (hf3 : Integrable f3 P)
    (hf4 : Integrable f4 P)
    (hc1 : ∀ᵐ ω ∂P, condExp F P f1 ω ≤ c1) (hc2 : ∀ᵐ ω ∂P, condExp F P f2 ω ≤ c2)
    (hc3 : ∀ᵐ ω ∂P, condExp F P f3 ω ≤ c3) (hc4 : ∀ᵐ ω ∂P, condExp F P f4 ω ≤ c4)
    (X : Ω → ℝ) (hX : AEStronglyMeasurable X P) (hX0 : ∀ ω, 0 ≤ X ω)
    (hXle : ∀ ω, X ω ≤ a0 + (w1 * f1 ω + w2 * f2 ω + w3 * f3 ω + w4 * f4 ω)) :
    Integrable X P ∧ ∀ᵐ ω ∂P, condExp F P X ω ≤ a0 + (w1 * c1 + w2 * c2 + w3 * c3 + w4 * c4) := by
  let w : ℕ → ℝ := fun j => if j = 0 then w1 else if j = 1 then w2 else if j = 2 then w3 else w4
  let f : ℕ → Ω → ℝ := fun j => if j = 0 then f1 else if j = 1 then f2 else if j = 2 then f3 else f4
  let c : ℕ → ℝ := fun j => if j = 0 then c1 else if j = 1 then c2 else if j = 2 then c3 else c4
  have hw : ∀ j, 0 ≤ w j := by
    intro j; simp only [w]; split_ifs <;> assumption
  have hf : ∀ j, Integrable (f j) P := by
    intro j; simp only [f]; split_ifs <;> assumption
  have hc : ∀ j, ∀ᵐ ω ∂P, condExp F P (f j) ω ≤ c j := by
    intro j; simp only [f, c]; split_ifs <;> assumption
  have hsum : ∀ ω, ∑ j ∈ Finset.range 4, w j * f j ω =
      w1 * f1 ω + w2 * f2 ω + w3 * f3 ω + w4 * f4 ω := by
    intro ω; simp [Finset.sum_range_succ, w, f]
  have hsumc : ∑ j ∈ Finset.range 4, w j * c j = w1 * c1 + w2 * c2 + w3 * c3 + w4 * c4 := by
    simp [Finset.sum_range_succ, w, c]
  obtain ⟨hi, hb⟩ := coupling_cond_sum F hF 4 a0 w hw f hf c hc X hX hX0
    (fun ω => by rw [hsum]; exact hXle ω)
  refine ⟨hi, ?_⟩
  filter_upwards [hb] with ω hω
  rwa [hsumc] at hω


/-- `lem:app-dyn-coupling`(i) in the global form used by the Taylor transfer: first and second
conditional moments of the buffer and update errors, as almost-everywhere bounds. -/
private lemma taylor_coupling (certOp : Muon.External.GaussianOpNormL6) (p : DynParams)
    (rlo rhi E : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ B0 : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (m n B : ℕ) (S : DynSetup p P m n B), B0 ≤ B → 0 < B →
      ∀ t r : ℕ, r ≤ 4 * blockLen B →
      (Integrable ((dynInK S t (rlo, rhi, E)).indicator (fun ω => fro (dynErrM p S t r ω))) P ∧
        ∀ᵐ ω ∂P, condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => fro (dynErrM p S t r ω))) ω ≤ Real.sqrt K * r) ∧
      (Integrable ((dynInK S t (rlo, rhi, E)).indicator (fun ω => fro (dynErrS p S t r ω))) P ∧
        ∀ᵐ ω ∂P, condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => fro (dynErrS p S t r ω))) ω ≤ Real.sqrt K * r) ∧
      (Integrable ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => fro (dynErrM p S t r ω) ^ 2)) P ∧
        ∀ᵐ ω ∂P, condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => fro (dynErrM p S t r ω) ^ 2)) ω ≤ K * (r : ℝ) ^ 2) ∧
      (Integrable ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => fro (dynErrS p S t r ω) ^ 2)) P ∧
        ∀ᵐ ω ∂P, condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => fro (dynErrS p S t r ω) ^ 2)) ω ≤ K * (r : ℝ) ^ 2) ∧
      (Integrable ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => opNorm (dynErrM p S t r ω) ^ 2)) P ∧
        ∀ᵐ ω ∂P, condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => opNorm (dynErrM p S t r ω) ^ 2)) ω ≤
            K * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B) := by
  obtain ⟨B0, K, hK⟩ := lem_app_dyn_coupling_i certOp p rlo rhi E hrlo hle
  refine ⟨B0, max K 0, le_max_right _ _, ?_⟩
  intro Ω _ P _ m n B S hB hB1 t r hr
  obtain ⟨⟨hi1, hc1⟩, ⟨hi2, hc2⟩⟩ := hK Ω P m n B S hB t r hr
  set A := dynInK S t (rlo, rhi, E) with hAdef
  have hA : MeasurableSet[dynPast S t] A := coupling_A_meas S t _
  have hAm : MeasurableSet A := buffer_past_le S t _ hA
  set K' := max K 0 with hK'def
  have hK' : K ≤ K' := le_max_left _ _
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hr2 : 0 ≤ (r : ℝ) ^ 2 := by positivity
  have hlogB : 0 ≤ Real.log (2 * (B : ℝ)) ^ 2 / B := by positivity
  have hg1 := coupling_cond_ind_self (dynPast S t) A hA _ hi1 (K' * (r : ℝ) ^ 2)
    (mul_nonneg hK'0 hr2)
    (by filter_upwards [hc1] with ω h hω; exact (h hω).trans (mul_le_mul_of_nonneg_right hK' hr2))
  have hg2 := coupling_cond_ind_self (dynPast S t) A hA _ hi2
    (K' * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B) (by positivity)
    (by
      filter_upwards [hc2] with ω h hω
      refine (h hω).trans ?_
      have := mul_le_mul_of_nonneg_right hK' (mul_nonneg hr2 hlogB)
      calc K * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / B
          = K * ((r : ℝ) ^ 2 * (Real.log (2 * (B : ℝ)) ^ 2 / B)) := by ring
        _ ≤ K' * ((r : ℝ) ^ 2 * (Real.log (2 * (B : ℝ)) ^ 2 / B)) := this
        _ = _ := by ring)
  have hMsq : Measurable (A.indicator (fun ω => fro (dynErrM p S t r ω) ^ 2)) :=
    (buffer_fro_sq_meas.comp (coupling_errM_meas S t r)).indicator hAm
  have hSsq : Measurable (A.indicator (fun ω => fro (dynErrS p S t r ω) ^ 2)) :=
    (buffer_fro_sq_meas.comp (coupling_errS_meas S hB1 t r)).indicator hAm
  have hM2 := taylor_cond_mono (dynPast S t) _ _ hi1 _ hg1 hMsq.aestronglyMeasurable
    (fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω)
    (fun ω => by
      by_cases h : ω ∈ A
      · simp only [Set.indicator_of_mem h]
        nlinarith [sq_nonneg (fro (dynErrS p S t r ω))]
      · simp [h])
  have hS2 := taylor_cond_mono (dynPast S t) _ _ hi1 _ hg1 hSsq.aestronglyMeasurable
    (fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω)
    (fun ω => by
      by_cases h : ω ∈ A
      · simp only [Set.indicator_of_mem h]
        nlinarith [sq_nonneg (fro (dynErrM p S t r ω))]
      · simp [h])
  have hM1 := coupling_cond_l1_of_sq (dynPast S t) (A.indicator fun ω => fro (dynErrM p S t r ω))
    (((taylor_fro_cont.measurable.comp (coupling_errM_meas S t r)).indicator hAm).aestronglyMeasurable)
    (fun ω => Set.indicator_nonneg (fun _ _ => movement_fro_nn _) ω)
    (by simp_rw [taylor_ind_sq]; exact hM2.1)
    (fun _ => Real.sqrt K' * r) (fun _ => by positivity)
    (by
      simp_rw [taylor_ind_sq]
      filter_upwards [hM2.2] with ω h
      rw [mul_pow, Real.sq_sqrt hK'0]
      exact h)
  have hS1 := coupling_cond_l1_of_sq (dynPast S t) (A.indicator fun ω => fro (dynErrS p S t r ω))
    (((taylor_fro_cont.measurable.comp (coupling_errS_meas S hB1 t r)).indicator hAm).aestronglyMeasurable)
    (fun ω => Set.indicator_nonneg (fun _ _ => movement_fro_nn _) ω)
    (by simp_rw [taylor_ind_sq]; exact hS2.1)
    (fun _ => Real.sqrt K' * r) (fun _ => by positivity)
    (by
      simp_rw [taylor_ind_sq]
      filter_upwards [hS2.2] with ω h
      rw [mul_pow, Real.sq_sqrt hK'0]
      exact h)
  exact ⟨hM1, hS1, hM2, hS2, hi2, hg2⟩

/-- Pathwise first-order expansion of `𝖲_{t+r} − V̂_r − λ V̇̂_r` (`section.tex` ll. 1666–1713). -/
private lemma taylor_path {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (hB : 0 < B) (rlo rhi E : ℝ) (hrlo : 0 < rlo)
    (Cd : ℝ) (hCd0 : 0 ≤ Cd)
    (hCd : ∀ (ℓ ℓ' a : ℝ), ℓ ∈ Icc (rlo * p.ϱ) (4 * rhi * p.ϱ) →
      ℓ' ∈ Icc (rlo * p.ϱ) (4 * rhi * p.ϱ) → ∀ N M X : Mat m n,
      fro (Q ℓ' M - Q ℓ N - (dirDeriv ℓ N X + a • ridgeDeriv ℓ N)) ≤
        Cd * Real.sqrt ((min m n : ℕ) : ℝ) * (ℓ' - ℓ) ^ 2 + Cd * |ℓ' - ℓ| * fro (M - N) +
        Cd * Real.sqrt ((min m n : ℕ) : ℝ) * |ℓ' - ℓ - a| + Cd * opNorm (M - N) * fro (M - N) +
        (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * fro (M - N - X))
    (t r : ℕ) (ω : Ω)
    (h0 : dynDelta S t ω ∈ admSetOf S.C (rlo, rhi, E))
    (hr : dynDelta S (t + r) ω ∈ admSetOf S.C (enl (rlo, rhi, E))) :
    fro (dynUpd S (t + r) ω - dynHatV p S t r ω - (p.h / B) • dynTangent p S t r ω) ≤
      (Cd * Real.sqrt (p.γstar * B) *
          (2 * p.ϱ * Real.sqrt (4 * rhi) * (p.CSig * p.h * Real.sqrt p.γstar) * r /
            Real.sqrt B) ^ 2 +
        Cd * Real.sqrt (p.γstar * B) *
          (2 * p.ϱ * (p.CSig ^ 2 * (p.h * Real.sqrt p.γstar * r / Real.sqrt B) ^ 2 / 2))) +
      (Cd * (2 * p.ϱ * Real.sqrt (4 * rhi) * (p.CSig * p.h * Real.sqrt p.γstar) * r /
            Real.sqrt B) * fro (dynErrM p S t r ω) +
        Cd * Real.sqrt (p.γstar * B) * (2 * p.ϱ * (Real.sqrt (2 * rhi) * p.CSig * (p.h / B))) *
          ∑ k ∈ Finset.range r, fro (dynErrS p S t k ω) +
        Cd * (opNorm (dynErrM p S t r ω) * fro (dynErrM p S t r ω)) +
        (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * fro (dynErrM p S t r ω - (p.h / B) •
          tangentM p S.C (fun s => physBatch S.C (S.cs.act s) ω) t (dynDelta S t ω)
            (dynBuf S t ω) r)) := by
  obtain ⟨hlo0, hhi0, -⟩ := h0
  obtain ⟨hlor, hhir, -⟩ := hr
  simp only [enl] at hlor hhir
  simp only at hlo0 hhi0
  have hR0pos : 0 < riskSigma S.C (dynDelta S t ω) := lt_of_lt_of_le hrlo hlo0
  have hRrpos : 0 < riskSigma S.C (dynDelta S (t + r) ω) := lt_of_lt_of_le (half_pos hrlo) hlor
  have hϱ := p.hϱ
  have hC : 0 ≤ p.CSig := le_trans (by norm_num) p.hC
  have hγ := p.hγ
  have hh := p.hh
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hsB : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBpos
  have hmv := movement_all p S ω t (t + r) (Nat.le_add_right t r)
  have hrr : ((t + r : ℕ) : ℝ) - t = r := by push_cast; ring
  rw [hrr] at hmv
  obtain ⟨-, hmvF, hmvR⟩ := hmv
  have hYeq := taylorY_eq S t r ω
  set D := dynDelta S t ω with hDdef
  set D' := dynDelta S (t + r) ω with hD'def
  set ℓ := physRidge p S.C D with hℓdef
  set ℓ' := physRidge p S.C D' with hℓ'def
  set N := dynHatN p S t r ω with hNdef
  set M := dynBuf S (t + r + 1) ω with hMdef
  set T := tangentM p S.C (fun s => physBatch S.C (S.cs.act s) ω) t D (dynBuf S t ω) r with hTdef
  set Vs := ∑ k ∈ Finset.range r, dynHatV p S t k ω with hVs
  set a := -(2 * p.ϱ * pairSigma S.C D Vs) with ha
  set lam := p.h / (B : ℝ) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hh.le hBpos.le
  have hℓpos : 0 < ℓ := by simp only [hℓdef, physRidge]; positivity
  have hS : dynUpd S (t + r) ω = Q ℓ' M := coupling_upd_eq S (t + r) ω hRrpos.ne'
  have hV : dynHatV p S t r ω = Q ℓ N := rfl
  have hT : lam • dynTangent p S t r ω = dirDeriv ℓ N (lam • T) + (lam * a) • ridgeDeriv ℓ N := by
    rw [taylor_tangent_eq S t r ω hR0pos, smul_add, taylor_dd_smul hℓpos, smul_smul]
  have hrem : dynUpd S (t + r) ω - dynHatV p S t r ω - lam • dynTangent p S t r ω =
      Q ℓ' M - Q ℓ N - (dirDeriv ℓ N (lam • T) + (lam * a) • ridgeDeriv ℓ N) := by
    rw [hS, hV, hT]
  have hℓI : ℓ ∈ Icc (rlo * p.ϱ) (4 * rhi * p.ϱ) := by
    constructor <;> simp only [hℓdef, physRidge] <;> nlinarith
  have hℓ'I : ℓ' ∈ Icc (rlo * p.ϱ) (4 * rhi * p.ϱ) := by
    constructor <;> simp only [hℓ'def, physRidge] <;> nlinarith
  have hmain := hCd ℓ ℓ' (lam * a) hℓI hℓ'I N M (lam • T)
  have hMN : M - N = dynErrM p S t r ω := rfl
  rw [hMN] at hmain
  rw [hrem]
  refine hmain.trans ?_
  -- the ridge increment
  set a0 := Real.sqrt (2 * riskSigma S.C D) with ha0
  set ar := Real.sqrt (2 * riskSigma S.C D') with har
  have ha0sq : a0 ^ 2 = 2 * riskSigma S.C D := Real.sq_sqrt (by linarith)
  have harsq : ar ^ 2 = 2 * riskSigma S.C D' := Real.sq_sqrt (by linarith)
  have ha0le : a0 ≤ Real.sqrt (4 * rhi) := Real.sqrt_le_sqrt (by linarith)
  have harle : ar ≤ Real.sqrt (4 * rhi) := Real.sqrt_le_sqrt (by linarith)
  have ha0nn : 0 ≤ a0 := Real.sqrt_nonneg _
  have harnn : 0 ≤ ar := Real.sqrt_nonneg _
  set δ := p.CSig * p.h * Real.sqrt p.γstar * (r : ℝ) / Real.sqrt B with hδ
  have hδnn : 0 ≤ δ := by positivity
  have hRdiff : |riskSigma S.C D' - riskSigma S.C D| ≤ δ * Real.sqrt (4 * rhi) := by
    have h1 : riskSigma S.C D' - riskSigma S.C D = (ar - a0) * (ar + a0) / 2 := by
      have e : (ar - a0) * (ar + a0) / 2 = (ar ^ 2 - a0 ^ 2) / 2 := by ring
      rw [e, harsq, ha0sq]
      ring
    rw [h1, abs_div, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ar + a0), abs_two]
    have h2 : |ar - a0| ≤ δ := hmvR
    have h3 : (ar + a0) / 2 ≤ Real.sqrt (4 * rhi) := by linarith
    calc |ar - a0| * (ar + a0) / 2 = |ar - a0| * ((ar + a0) / 2) := by ring
      _ ≤ δ * Real.sqrt (4 * rhi) := mul_le_mul h2 h3 (by linarith) hδnn
  set u := 2 * p.ϱ * Real.sqrt (4 * rhi) * (p.CSig * p.h * Real.sqrt p.γstar) * r /
    Real.sqrt B with hu
  have hu0 : 0 ≤ u := by positivity
  have hdl : |ℓ' - ℓ| ≤ u := by
    have : ℓ' - ℓ = 2 * p.ϱ * (riskSigma S.C D' - riskSigma S.C D) := by
      simp only [hℓ'def, hℓdef, physRidge]; ring
    rw [this, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * p.ϱ)]
    calc 2 * p.ϱ * |riskSigma S.C D' - riskSigma S.C D| ≤ 2 * p.ϱ * (δ * Real.sqrt (4 * rhi)) :=
          mul_le_mul_of_nonneg_left hRdiff (by positivity)
      _ = u := by rw [hδ, hu]; ring
  -- the ridge-tangent defect
  set Eδ := D' - D with hEδ
  set sS := ∑ k ∈ Finset.range r, fro (dynErrS p S t k ω) with hsS
  have hid : ℓ' - ℓ - lam * a =
      2 * p.ϱ * (pairSigma S.C D (Eδ + lam • Vs) + riskSigma S.C Eδ) := by
    have hD' : D' = D + Eδ := by rw [hEδ]; abel
    have h1 : ℓ' = 2 * riskSigma S.C (D + Eδ) * p.ϱ := by rw [← hD']; rfl
    rw [h1, taylor_risk_add, taylor_pair_add_right, taylor_pair_smul_right, ha]
    simp only [hℓdef, physRidge]
    ring
  have hpair := taylor_pair_bound p S.C S.size D (Eδ + lam • Vs)
  have hYfro : fro (Eδ + lam • Vs) ≤ lam * sS := by
    rw [hYeq, ← neg_smul, taylor_fro_smul, abs_neg, abs_of_nonneg hlam0]
    exact mul_le_mul_of_nonneg_left (coupling_norm_finset_sum fro coupling_fro_props.2.1
      coupling_fro_props.2.2.1 r _) hlam0
  have hrisk : riskSigma S.C Eδ ≤
      p.CSig ^ 2 * (p.h * Real.sqrt p.γstar * r / Real.sqrt B) ^ 2 / 2 := by
    rw [eqn_app_setup_whitened_risk]
    have h1 := movement_Arot_bound p S.C S.size Eδ
    have h2 : fro (Arot S.C Eδ) ≤ p.CSig * (p.h * Real.sqrt p.γstar * r / Real.sqrt B) :=
      h1.trans (mul_le_mul_of_nonneg_left hmvF hC)
    have h3 := pow_le_pow_left₀ (movement_fro_nn _) h2 2
    rw [mul_pow] at h3
    linarith
  have hsq0 : Real.sqrt (2 * riskSigma S.C D) ≤ Real.sqrt (2 * rhi) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsS0 : 0 ≤ sS := Finset.sum_nonneg fun k _ => movement_fro_nn _
  set v := p.CSig ^ 2 * (p.h * Real.sqrt p.γstar * r / Real.sqrt B) ^ 2 / 2 with hv
  have hdla : |ℓ' - ℓ - lam * a| ≤
      2 * p.ϱ * (Real.sqrt (2 * rhi) * p.CSig * lam * sS + v) := by
    rw [hid, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * p.ϱ)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hr0 : 0 ≤ riskSigma S.C Eδ := by rw [eqn_app_setup_whitened_risk]; positivity
    have hab := abs_add_le (pairSigma S.C D (Eδ + lam • Vs)) (riskSigma S.C Eδ)
    rw [abs_of_nonneg hr0] at hab
    have hp2 : |pairSigma S.C D (Eδ + lam • Vs)| ≤ Real.sqrt (2 * rhi) * (p.CSig * (lam * sS)) :=
      hpair.trans (mul_le_mul hsq0 (mul_le_mul_of_nonneg_left hYfro hC)
        (mul_nonneg hC (movement_fro_nn _)) (Real.sqrt_nonneg _))
    have e : Real.sqrt (2 * rhi) * (p.CSig * (lam * sS)) = Real.sqrt (2 * rhi) * p.CSig * lam * sS := by
      ring
    linarith
  have hmin : Real.sqrt ((min m n : ℕ) : ℝ) ≤ Real.sqrt (p.γstar * B) := by
    apply Real.sqrt_le_sqrt
    have hm : ((min m n : ℕ) : ℝ) ≤ ((max m n : ℕ) : ℝ) := by
      exact_mod_cast (min_le_max : min m n ≤ max m n)
    exact hm.trans S.size.1
  -- combination
  set sm := Real.sqrt ((min m n : ℕ) : ℝ) with hsm
  set sg := Real.sqrt (p.γstar * B) with hsg
  have hsm0 : 0 ≤ sm := Real.sqrt_nonneg _
  have hq0 := movement_fro_nn (dynErrM p S t r ω)
  have hsq : (ℓ' - ℓ) ^ 2 ≤ u ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hdl 2
  have t1 : Cd * sm * (ℓ' - ℓ) ^ 2 ≤ Cd * sg * u ^ 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hmin hCd0) hsq (sq_nonneg _)
      (mul_nonneg hCd0 (Real.sqrt_nonneg _))
  have t2 : Cd * |ℓ' - ℓ| * fro (dynErrM p S t r ω) ≤ Cd * u * fro (dynErrM p S t r ω) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdl hCd0) hq0
  have t3 : Cd * sm * |ℓ' - ℓ - lam * a| ≤
      Cd * sg * (2 * p.ϱ * (Real.sqrt (2 * rhi) * p.CSig * lam * sS + v)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hmin hCd0) hdla (abs_nonneg _)
      (mul_nonneg hCd0 (Real.sqrt_nonneg _))
  have e3 : Cd * sg * (2 * p.ϱ * (Real.sqrt (2 * rhi) * p.CSig * lam * sS + v)) =
      Cd * sg * (2 * p.ϱ * (Real.sqrt (2 * rhi) * p.CSig * lam)) * sS + Cd * sg * (2 * p.ϱ * v) := by
    ring
  have e4 : Cd * opNorm (dynErrM p S t r ω) * fro (dynErrM p S t r ω) =
      Cd * (opNorm (dynErrM p S t r ω) * fro (dynErrM p S t r ω)) := by ring
  linarith


private lemma taylor_cond_sum' {Ω : Type*} (F : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hF : F ≤ m0) (k : ℕ) (a0 : ℝ) (w : ℕ → ℝ)
    (hw : ∀ j ∈ Finset.range k, 0 ≤ w j) (f : ℕ → Ω → ℝ)
    (hf : ∀ j ∈ Finset.range k, Integrable (f j) P) (c : ℕ → ℝ)
    (hc : ∀ j ∈ Finset.range k, ∀ᵐ ω ∂P, condExp F P (f j) ω ≤ c j)
    (X : Ω → ℝ) (hX : AEStronglyMeasurable X P) (hX0 : ∀ ω, 0 ≤ X ω)
    (hXle : ∀ ω, X ω ≤ a0 + ∑ j ∈ Finset.range k, w j * f j ω) :
    Integrable X P ∧ ∀ᵐ ω ∂P, condExp F P X ω ≤ a0 + ∑ j ∈ Finset.range k, w j * c j := by
  classical
  let w' : ℕ → ℝ := fun j => if j < k then w j else 0
  let f' : ℕ → Ω → ℝ := fun j => if j < k then f j else 0
  let c' : ℕ → ℝ := fun j => if j < k then c j else 0
  have hw' : ∀ j, 0 ≤ w' j := by
    intro j
    simp only [w']
    split_ifs with h
    · exact hw j (Finset.mem_range.mpr h)
    · exact le_rfl
  have hf' : ∀ j, Integrable (f' j) P := by
    intro j
    simp only [f']
    split_ifs with h
    · exact hf j (Finset.mem_range.mpr h)
    · exact integrable_zero _ _ _
  have hc' : ∀ j, ∀ᵐ ω ∂P, condExp F P (f' j) ω ≤ c' j := by
    intro j
    simp only [f', c']
    split_ifs with h
    · exact hc j (Finset.mem_range.mpr h)
    · rw [condExp_zero]
      exact ae_of_all _ fun ω => le_rfl
  have hs : ∀ ω, ∑ j ∈ Finset.range k, w' j * f' j ω = ∑ j ∈ Finset.range k, w j * f j ω := by
    intro ω
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.mp hj
    simp [w', f', this]
  have hsc : ∑ j ∈ Finset.range k, w' j * c' j = ∑ j ∈ Finset.range k, w j * c j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.mp hj
    simp [w', c', this]
  obtain ⟨hi, hb⟩ := coupling_cond_sum F hF k a0 w' hw' f' hf' c' hc' X hX hX0
    (fun ω => by rw [hs]; exact hXle ω)
  refine ⟨hi, ?_⟩
  filter_upwards [hb] with ω hω
  rwa [hsc] at hω

private lemma taylor_ind_fro {Ω : Type*} {m n : ℕ} (A : Set Ω) (g : Ω → Mat m n) (ω : Ω) :
    A.indicator (fun ω => fro (g ω)) ω = fro (A.indicator g ω) := by
  by_cases h : ω ∈ A
  · simp [h]
  · simp [h, fro]

private lemma taylor_errS_bdd {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (t k : ℕ) (ω : Ω) :
    fro (dynErrS p S t k ω) ^ 2 ≤ 4 * (p.γstar * B) := by
  have h1 := (movement_update_bounds p S ω (t + k)).2
  have h2 := coupling_Q_fro_sq S _ (coupling_ridge_nonneg (p := p) S.C (dynDelta S t ω))
    (dynHatN p S t k ω)
  have h3 := coupling_fro_sub_le (dynUpd S (t + k) ω) (dynHatV p S t k ω)
  have hq : 0 ≤ p.γstar * B := mul_nonneg p.hγ (Nat.cast_nonneg _)
  have h1' := pow_le_pow_left₀ (movement_fro_nn _) h1 2
  rw [Real.sq_sqrt hq] at h1'
  have h4 := pow_le_pow_left₀ (movement_fro_nn _) h3 2
  have h5 := coupling_sq_add_le' (fro (dynUpd S (t + k) ω)) (fro (dynHatV p S t k ω))
  change fro (dynUpd S (t + k) ω - dynHatV p S t k ω) ^ 2 ≤ _
  have h2' : fro (dynHatV p S t k ω) ^ 2 ≤ p.γstar * B := h2
  linarith

/-- The tangent-replacement error `R_r − λ Ṅ̂_r` in conditional `L¹` (`section.tex` ll. 1695–1700). -/
private lemma taylor_G_bound {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (hB : 0 < B)
    {A : Set Ω} {t : ℕ} (hA : MeasurableSet[dynPast S t] A) (r : ℕ) (K1 : ℝ) (hK1 : 0 ≤ K1)
    (hS2 : ∀ k < r, Integrable (A.indicator (fun ω => fro (dynErrS p S t k ω) ^ 2)) P ∧
      ∀ᵐ ω ∂P, condExp (dynPast S t) P (A.indicator (fun ω => fro (dynErrS p S t k ω) ^ 2)) ω ≤
        K1 * (k : ℝ) ^ 2) :
    Integrable (A.indicator (fun ω => fro (dynErrM p S t r ω - (p.h / B) •
        tangentM p S.C (fun s => physBatch S.C (S.cs.act s) ω) t (dynDelta S t ω)
          (dynBuf S t ω) r))) P ∧
    ∀ᵐ ω ∂P, condExp (dynPast S t) P (A.indicator (fun ω => fro (dynErrM p S t r ω - (p.h / B) •
        tangentM p S.C (fun s => physBatch S.C (S.cs.act s) ω) t (dynDelta S t ω)
          (dynBuf S t ω) r))) ω ≤
      Real.sqrt (cMConst p.CSig p.γstar * p.CSig ^ 2 * p.h ^ 2 * K1) * (r : ℝ) ^ 2 /
        Real.sqrt B := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hC : 0 ≤ p.CSig := le_trans (by norm_num) p.hC
  have hγ := p.hγ
  have hh := p.hh
  have hCM : 0 ≤ cMConst p.CSig p.γstar := by unfold cMConst; positivity
  have hAm : MeasurableSet A := buffer_past_le S t _ hA
  set lam : ℝ := p.h / (B : ℝ) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hh.le hBr.le
  -- pathwise bound on the rotated first-order error
  have hYrot : ∀ j ω, fro (rOut S.C * taylorY S A t j ω * rIn S.C) ^ 2 ≤
      0 + ∑ k ∈ Finset.range j, (p.CSig ^ 2 * lam ^ 2 * j) *
        A.indicator (fun ω => fro (dynErrS p S t k ω) ^ 2) ω := by
    intro j ω
    rw [zero_add]
    by_cases hω : ω ∈ A
    · simp only [taylorY, Set.indicator_of_mem hω]
      rw [taylorY_eq, ← Finset.mul_sum]
      have h1 := movement_Arot_bound p S.C S.size
        (-(lam • ∑ k ∈ Finset.range j, dynErrS p S t k ω))
      change fro (Arot S.C _) ^ 2 ≤ _
      have h2 := pow_le_pow_left₀ (movement_fro_nn _) h1 2
      have hY : fro (-(lam • ∑ k ∈ Finset.range j, dynErrS p S t k ω)) =
          lam * fro (∑ k ∈ Finset.range j, dynErrS p S t k ω) := by
        rw [← neg_smul, taylor_fro_smul, abs_neg, abs_of_nonneg hlam0]
      rw [hY] at h2
      have h3 := coupling_norm_finset_sum_sq fro coupling_fro_props.2.1 coupling_fro_props.2.2.1
        coupling_fro_props.2.2.2 j (fun k => dynErrS p S t k ω)
      have h4 : (p.CSig * (lam * fro (∑ k ∈ Finset.range j, dynErrS p S t k ω))) ^ 2 =
          p.CSig ^ 2 * lam ^ 2 * fro (∑ k ∈ Finset.range j, dynErrS p S t k ω) ^ 2 := by ring
      rw [h4] at h2
      refine h2.trans ?_
      have h6 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ p.CSig ^ 2 * lam ^ 2)
      exact h6.trans (le_of_eq (by ring))
    · simp only [taylorY, Set.indicator_of_notMem hω, Matrix.mul_zero, Matrix.zero_mul]
      have : fro (0 : Mat m n) = 0 := by simp [fro]
      rw [this]
      have : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [this]
      exact Finset.sum_nonneg fun k _ => by simp
  have hYbd : ∀ j ω, fro (rOut S.C * taylorY S A t j ω * rIn S.C) ^ 2 ≤
      (j : ℝ) * ((p.CSig ^ 2 * lam ^ 2 * j) * (4 * (p.γstar * B))) := by
    intro j ω
    refine (hYrot j ω).trans ?_
    rw [zero_add]
    calc ∑ k ∈ Finset.range j, (p.CSig ^ 2 * lam ^ 2 * j) *
          A.indicator (fun ω => fro (dynErrS p S t k ω) ^ 2) ω
        ≤ ∑ k ∈ Finset.range j, (p.CSig ^ 2 * lam ^ 2 * j) * (4 * (p.γstar * B)) := by
          refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
          by_cases hω : ω ∈ A
          · rw [Set.indicator_of_mem hω]; exact taylor_errS_bdd S t k ω
          · rw [Set.indicator_of_notMem hω]; positivity
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- conditional bound on each gradient term
  set cc : ℝ := cMConst p.CSig p.γstar * p.CSig ^ 2 * p.h ^ 2 * K1 * (r : ℝ) ^ 4 / B with hcc
  have hGj : ∀ j ∈ Finset.range (r + 1),
      Integrable (fun ω => fro (batchGrad (taylorY S A t j ω) (dynBatch S (t + j) ω)) ^ 2) P ∧
      ∀ᵐ ω ∂P, condExp (dynPast S t) P
        (fun ω => fro (batchGrad (taylorY S A t j ω) (dynBatch S (t + j) ω)) ^ 2) ω ≤ cc := by
    intro j hj
    have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hYm := taylorY_meas S hA j
    obtain ⟨hGi, hRi, hGc⟩ := taylor_grad_cond S hB (Nat.le_add_right t j) (taylorY S A t j) hYm _
      (hYbd j)
    refine ⟨hGi, ?_⟩
    have hrotm : Measurable (fun ω => fro (rOut S.C * taylorY S A t j ω * rIn S.C) ^ 2) := by
      have hY' : Measurable (taylorY S A t j) := hYm.mono (buffer_past_le S _) le_rfl
      have hrotD : Measurable (fun ω => rOut S.C * taylorY S A t j ω * rIn S.C) := by
        apply buffer_mat_meas
        intro i l
        simp only [Matrix.mul_apply]
        have := buffer_entry_meas hY'
        fun_prop
      exact buffer_fro_sq_meas.comp hrotD
    obtain ⟨-, hRc⟩ := taylor_cond_sum' (dynPast S t) (buffer_past_le S t) j 0
      (fun _ => p.CSig ^ 2 * lam ^ 2 * j) (fun _ _ => by positivity)
      (fun k => A.indicator (fun ω => fro (dynErrS p S t k ω) ^ 2))
      (fun k hk => (hS2 k (lt_of_lt_of_le (Finset.mem_range.mp hk) hjr)).1)
      (fun k => K1 * (k : ℝ) ^ 2)
      (fun k hk => (hS2 k (lt_of_lt_of_le (Finset.mem_range.mp hk) hjr)).2)
      _ hrotm.aestronglyMeasurable (fun ω => sq_nonneg _) (hYrot j)
    have hsum : 0 + ∑ k ∈ Finset.range j, p.CSig ^ 2 * lam ^ 2 * j * (K1 * (k : ℝ) ^ 2) ≤
        p.CSig ^ 2 * lam ^ 2 * K1 * (r : ℝ) ^ 4 := by
      rw [zero_add]
      have hk : ∀ k ∈ Finset.range j, p.CSig ^ 2 * lam ^ 2 * j * (K1 * (k : ℝ) ^ 2) ≤
          p.CSig ^ 2 * lam ^ 2 * K1 * (r : ℝ) ^ 3 := by
        intro k hk
        have hkj : (k : ℝ) ≤ r := by
          have := Finset.mem_range.mp hk
          exact_mod_cast (le_of_lt (lt_of_lt_of_le this hjr))
        have hjr' : (j : ℝ) ≤ r := by exact_mod_cast hjr
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
        have hk2 : (k : ℝ) ^ 2 ≤ (r : ℝ) ^ 2 := pow_le_pow_left₀ hk0 hkj 2
        have hc0 : 0 ≤ p.CSig ^ 2 * lam ^ 2 * K1 := by positivity
        have e1 : p.CSig ^ 2 * lam ^ 2 * j * (K1 * (k : ℝ) ^ 2) =
            (p.CSig ^ 2 * lam ^ 2 * K1) * ((j : ℝ) * (k : ℝ) ^ 2) := by ring
        have e2 : p.CSig ^ 2 * lam ^ 2 * K1 * (r : ℝ) ^ 3 =
            (p.CSig ^ 2 * lam ^ 2 * K1) * ((r : ℝ) * (r : ℝ) ^ 2) := by ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hjr' hk2 (sq_nonneg _) (Nat.cast_nonneg _)) hc0
      calc ∑ k ∈ Finset.range j, p.CSig ^ 2 * lam ^ 2 * j * (K1 * (k : ℝ) ^ 2)
          ≤ ∑ k ∈ Finset.range j, p.CSig ^ 2 * lam ^ 2 * K1 * (r : ℝ) ^ 3 := Finset.sum_le_sum hk
        _ = (j : ℝ) * (p.CSig ^ 2 * lam ^ 2 * K1 * (r : ℝ) ^ 3) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ (r : ℝ) * (p.CSig ^ 2 * lam ^ 2 * K1 * (r : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hjr) (by positivity)
        _ = _ := by ring
    filter_upwards [hGc, hRc] with ω h1 h2
    refine h1.trans ?_
    have h3 := mul_le_mul_of_nonneg_left (h2.trans hsum)
      (by positivity : (0 : ℝ) ≤ cMConst p.CSig p.γstar * B)
    refine h3.trans (le_of_eq ?_)
    rw [hcc, hlam]
    field_simp
  -- assemble the square
  have hGm : ∀ j, Measurable (fun ω => batchGrad (taylorY S A t j ω) (dynBatch S (t + j) ω)) := by
    intro j
    exact buffer_grad_meas ((taylorY_meas S hA j).mono (buffer_past_le S _) le_rfl)
      ((buffer_batch_meas S (t + j)).mono (buffer_past_le S _) le_rfl)
  have hfG : A.indicator (fun ω => fro (dynErrM p S t r ω - (p.h / B) •
        tangentM p S.C (fun s => physBatch S.C (S.cs.act s) ω) t (dynDelta S t ω)
          (dynBuf S t ω) r)) = fun ω => fro (∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) •
        batchGrad (taylorY S A t j ω) (dynBatch S (t + j) ω)) := by
    funext ω
    rw [taylor_ind_fro, taylor_RX_eq]
  rw [hfG]
  have hmeasG : Measurable (fun ω => fro (∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) •
        batchGrad (taylorY S A t j ω) (dynBatch S (t + j) ω))) :=
    taylor_fro_cont.measurable.comp (Finset.measurable_sum _ fun j _ => by
      exact (hGm j).const_smul (emaW p.β (r - j)))
  have hw0 : ∀ j, 0 ≤ emaW p.β (r - j) := fun j => coupling_emaW_nonneg p.hβ.1 p.hβ.2 _
  have hwsum := coupling_wsum_r p.β p.hβ.1 p.hβ.2 r
  obtain ⟨hsqi, hsqc⟩ := taylor_cond_sum' (dynPast S t) (buffer_past_le S t) (r + 1) 0
    (fun j => emaW p.β (r - j)) (fun j _ => hw0 j)
    (fun j ω => fro (batchGrad (taylorY S A t j ω) (dynBatch S (t + j) ω)) ^ 2)
    (fun j hj => (hGj j hj).1) (fun _ => cc) (fun j hj => (hGj j hj).2)
    (fun ω => fro (∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) •
        batchGrad (taylorY S A t j ω) (dynBatch S (t + j) ω)) ^ 2)
    (hmeasG.pow_const 2).aestronglyMeasurable (fun ω => sq_nonneg _)
    (fun ω => by
      rw [zero_add]
      obtain ⟨h1, h2, h3, h4⟩ := coupling_fro_props (m := m) (n := n)
      exact coupling_norm_sum_sq fro h1 h2 h3 h4 (r + 1) (fun j => emaW p.β (r - j)) hw0 hwsum _)
  have hcc0 : 0 ≤ cc := by rw [hcc]; positivity
  have hfinal := coupling_cond_l1_of_sq (dynPast S t) _ hmeasG.aestronglyMeasurable
    (fun ω => movement_fro_nn _) hsqi
    (fun _ => Real.sqrt (cMConst p.CSig p.γstar * p.CSig ^ 2 * p.h ^ 2 * K1) * (r : ℝ) ^ 2 /
        Real.sqrt B) (fun _ => by positivity)
    (by
      filter_upwards [hsqc] with ω hω
      refine hω.trans ?_
      rw [zero_add, ← Finset.sum_mul]
      have h1 : (∑ j ∈ Finset.range (r + 1), emaW p.β (r - j)) * cc ≤ cc := by
        nlinarith
      refine h1.trans (le_of_eq ?_)
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hBr.le, hcc]
      ring)
  exact hfinal


private lemma taylor_X_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (hB : 0 < B) (rlo rhi E : ℝ) (hrlo : 0 < rlo)
    (t r : ℕ) :
    Measurable ((dynInK S t (rlo, rhi, E)).indicator (fun ω => fro (dynUpd S (t + r) ω -
      dynHatV p S t r ω - (p.h / B) • dynTangent p S t r ω))) := by
  set A := dynInK S t (rlo, rhi, E) with hAdef
  have hAm : MeasurableSet A := buffer_past_le S t _ (coupling_A_meas S t _)
  set c := rlo * p.ϱ with hcdef
  have hc : 0 < c := mul_pos hrlo p.hϱ
  have hD := coupling_delta_meas S t
  have hℓ : Measurable (fun ω => physRidge p S.C (dynDelta S t ω)) :=
    ((coupling_risk_meas S.C hD).const_mul 2).mul_const p.ϱ
  have hN := coupling_hatN_meas S t r
  have hVs : Measurable (fun ω => ∑ k ∈ Finset.range r, dynHatV p S t k ω) :=
    Finset.measurable_sum _ fun k _ => coupling_hatV_meas S t k
  have hX : Measurable (fun ω => (p.h / B) • tangentM p S.C (fun s => physBatch S.C (S.cs.act s) ω)
      t (dynDelta S t ω) (dynBuf S t ω) r) := by
    have e : (fun ω => (p.h / B) • tangentM p S.C (fun s => physBatch S.C (S.cs.act s) ω)
        t (dynDelta S t ω) (dynBuf S t ω) r) = fun ω => ∑ j ∈ Finset.range (r + 1),
          emaW p.β (r - j) • batchGrad (-((p.h / B) • ∑ k ∈ Finset.range j, dynHatV p S t k ω))
            (dynBatch S (t + j) ω) := funext fun ω => taylor_tangentM_smul S ω t r
    rw [e]
    refine Finset.measurable_sum _ fun j _ => ?_
    have hb : Measurable (dynBatch S (t + j)) :=
      (buffer_batch_meas S (t + j)).mono (buffer_past_le S _) le_rfl
    have hs : Measurable (fun ω => ∑ k ∈ Finset.range j, dynHatV p S t k ω) :=
      Finset.measurable_sum _ fun k _ => coupling_hatV_meas S t k
    have hg := buffer_grad_meas ((hs.const_smul (p.h / (B : ℝ))).neg) hb
    exact hg.const_smul (emaW p.β (r - j))
  have ha : Measurable (fun ω => (p.h / B) * -(2 * p.ϱ * pairSigma S.C (dynDelta S t ω)
      (∑ k ∈ Finset.range r, dynHatV p S t k ω))) := by
    have hcont : Continuous (fun q : Mat m n × Mat m n => pairSigma S.C q.1 q.2) := by
      unfold pairSigma
      fun_prop
    exact (((hcont.measurable.comp (hD.prodMk hVs)).const_mul _).neg).const_mul _
  have hrd := taylor_rd_meas (σ := inferInstance) hc hℓ hN
  have hdd := taylor_dd_meas (σ := inferInstance) hc hℓ hN hX
  have hsm : Measurable (fun ω => ((p.h / B) * -(2 * p.ϱ * pairSigma S.C (dynDelta S t ω)
      (∑ k ∈ Finset.range r, dynHatV p S t k ω))) •
        (Matrix.of fun i j => deriv (fun x => Q (max x c) (dynHatN p S t r ω) i j)
          (physRidge p S.C (dynDelta S t ω)) : Mat m n)) := by
    apply buffer_mat_meas
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact ha.mul (buffer_entry_meas hrd i j)
  have hrem : Measurable (fun ω => dynUpd S (t + r) ω - dynHatV p S t r ω -
      (dirDeriv (max (physRidge p S.C (dynDelta S t ω)) c) (dynHatN p S t r ω)
          ((p.h / B) • tangentM p S.C (fun s => physBatch S.C (S.cs.act s) ω)
            t (dynDelta S t ω) (dynBuf S t ω) r) +
        ((p.h / B) * -(2 * p.ϱ * pairSigma S.C (dynDelta S t ω)
          (∑ k ∈ Finset.range r, dynHatV p S t k ω))) •
        (Matrix.of fun i j => deriv (fun x => Q (max x c) (dynHatN p S t r ω) i j)
          (physRidge p S.C (dynDelta S t ω)) : Mat m n))) :=
    ((coupling_upd_meas S hB _).sub (coupling_hatV_meas S t r)).sub (hdd.add hsm)
  have heq : A.indicator (fun ω => fro (dynUpd S (t + r) ω - dynHatV p S t r ω -
      (p.h / B) • dynTangent p S t r ω)) = A.indicator (fun ω => fro (dynUpd S (t + r) ω -
        dynHatV p S t r ω -
      (dirDeriv (max (physRidge p S.C (dynDelta S t ω)) c) (dynHatN p S t r ω)
          ((p.h / B) • tangentM p S.C (fun s => physBatch S.C (S.cs.act s) ω)
            t (dynDelta S t ω) (dynBuf S t ω) r) +
        ((p.h / B) * -(2 * p.ϱ * pairSigma S.C (dynDelta S t ω)
          (∑ k ∈ Finset.range r, dynHatV p S t k ω))) •
        (Matrix.of fun i j => deriv (fun x => Q (max x c) (dynHatN p S t r ω) i j)
          (physRidge p S.C (dynDelta S t ω)) : Mat m n)))) := by
    funext ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      have hlo0 : rlo ≤ riskSigma S.C (dynDelta S t ω) := hω.1
      have hR0 : 0 < riskSigma S.C (dynDelta S t ω) := lt_of_lt_of_le hrlo hlo0
      have hℓ2 : c < physRidge p S.C (dynDelta S t ω) := by
        rw [hcdef]
        unfold physRidge
        have := p.hϱ
        nlinarith
      have hℓpos : 0 < physRidge p S.C (dynDelta S t ω) := hc.trans hℓ2
      rw [taylor_tangent_eq S t r ω hR0, smul_add, max_eq_left hℓ2.le, taylor_dd_smul hℓpos,
        smul_smul, ← taylor_rd_clamp hℓ2]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
  rw [heq]
  exact (taylor_fro_cont.measurable.comp hrem).indicator hAm


private lemma taylor_cond2 {Ω : Type*} (F : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hF : F ≤ m0) (w1 w2 c1 c2 : ℝ)
    (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (f1 f2 : Ω → ℝ)
    (hf1 : Integrable f1 P) (hf2 : Integrable f2 P)
    (hc1 : ∀ᵐ ω ∂P, condExp F P f1 ω ≤ c1) (hc2 : ∀ᵐ ω ∂P, condExp F P f2 ω ≤ c2)
    (X : Ω → ℝ) (hX : AEStronglyMeasurable X P) (hX0 : ∀ ω, 0 ≤ X ω)
    (hXle : ∀ ω, X ω ≤ w1 * f1 ω + w2 * f2 ω) :
    Integrable X P ∧ ∀ᵐ ω ∂P, condExp F P X ω ≤ w1 * c1 + w2 * c2 := by
  let w : ℕ → ℝ := fun j => if j = 0 then w1 else w2
  let f : ℕ → Ω → ℝ := fun j => if j = 0 then f1 else f2
  let c : ℕ → ℝ := fun j => if j = 0 then c1 else c2
  have hw : ∀ j, 0 ≤ w j := by
    intro j; simp only [w]; split_ifs <;> assumption
  have hf : ∀ j, Integrable (f j) P := by
    intro j; simp only [f]; split_ifs <;> assumption
  have hc : ∀ j, ∀ᵐ ω ∂P, condExp F P (f j) ω ≤ c j := by
    intro j; simp only [f, c]; split_ifs <;> assumption
  have hsum : ∀ ω, ∑ j ∈ Finset.range 2, w j * f j ω = w1 * f1 ω + w2 * f2 ω := by
    intro ω; simp [Finset.sum_range_succ, w, f]
  have hsumc : ∑ j ∈ Finset.range 2, w j * c j = w1 * c1 + w2 * c2 := by
    simp [Finset.sum_range_succ, w, c]
  obtain ⟨hi, hb⟩ := coupling_cond_sum F hF 2 0 w hw f hf c hc X hX hX0
    (fun ω => by rw [zero_add, hsum]; exact hXle ω)
  refine ⟨hi, ?_⟩
  filter_upwards [hb] with ω hω
  rwa [zero_add, hsumc] at hω

private lemma taylor_amgm_arith (K1 r sB L Bv : ℝ) (hsB : 0 < sB) (hL : 0 < L)
    (hBv : sB ^ 2 = Bv) :
    sB / L / 2 * (K1 * r ^ 2 * L ^ 2 / Bv) + 1 / (2 * (sB / L)) * (K1 * r ^ 2) =
      K1 * r ^ 2 * L / sB := by
  subst hBv
  field_simp
  ring

private lemma taylor_arith (Cd sγ cs ϱ C h rhi K1 w4 cG r sB L l2 Bv : ℝ) (hsB : 0 < sB)
    (hl2 : 0 < l2) (hL : l2 ≤ L) (hBv : sB ^ 2 = Bv) (hr : 0 ≤ r)
    (hκ0 : 0 ≤ Cd * sγ * cs ^ 2 + Cd * sγ * (ϱ * C ^ 2 * h ^ 2 * sγ ^ 2) + Cd * cs * Real.sqrt K1 +
      Cd * sγ * (2 * ϱ * Real.sqrt (2 * rhi) * C * h) * Real.sqrt K1 + w4 * cG) :
    Cd * (sγ * sB) * (cs * r / sB) ^ 2 +
        Cd * (sγ * sB) * (2 * ϱ * (C ^ 2 * (h * sγ * r / sB) ^ 2 / 2)) +
      (Cd * (cs * r / sB) * (Real.sqrt K1 * r) +
        Cd * (sγ * sB) * (2 * ϱ * (Real.sqrt (2 * rhi) * C * (h / Bv))) * (Real.sqrt K1 * r ^ 2) +
        Cd * (K1 * r ^ 2 * L / sB) + w4 * (cG * r ^ 2 / sB)) ≤
    ((Cd * sγ * cs ^ 2 + Cd * sγ * (ϱ * C ^ 2 * h ^ 2 * sγ ^ 2) + Cd * cs * Real.sqrt K1 +
      Cd * sγ * (2 * ϱ * Real.sqrt (2 * rhi) * C * h) * Real.sqrt K1 + w4 * cG) / l2 + Cd * K1) *
        r ^ 2 * L / sB := by
  subst hBv
  set κ := Cd * sγ * cs ^ 2 + Cd * sγ * (ϱ * C ^ 2 * h ^ 2 * sγ ^ 2) + Cd * cs * Real.sqrt K1 +
      Cd * sγ * (2 * ϱ * Real.sqrt (2 * rhi) * C * h) * Real.sqrt K1 + w4 * cG with hκ
  have heq : Cd * (sγ * sB) * (cs * r / sB) ^ 2 +
        Cd * (sγ * sB) * (2 * ϱ * (C ^ 2 * (h * sγ * r / sB) ^ 2 / 2)) +
      (Cd * (cs * r / sB) * (Real.sqrt K1 * r) +
        Cd * (sγ * sB) * (2 * ϱ * (Real.sqrt (2 * rhi) * C * (h / sB ^ 2))) * (Real.sqrt K1 * r ^ 2) +
        Cd * (K1 * r ^ 2 * L / sB) + w4 * (cG * r ^ 2 / sB)) =
      κ * (r ^ 2 / sB) + Cd * K1 * r ^ 2 * L / sB := by
    rw [hκ]
    field_simp
    ring
  rw [heq]
  have hq : 0 ≤ r ^ 2 / sB := by positivity
  have h1 : κ * (r ^ 2 / sB) ≤ κ / l2 * r ^ 2 * L / sB := by
    have : κ / l2 * r ^ 2 * L / sB = κ * (r ^ 2 / sB) * (L / l2) := by
      field_simp
    rw [this]
    have hLl : 1 ≤ L / l2 := by rw [le_div_iff₀ hl2]; linarith
    nlinarith [mul_nonneg hκ0 hq]
  have h2 : (κ / l2 + Cd * K1) * r ^ 2 * L / sB = κ / l2 * r ^ 2 * L / sB + Cd * K1 * r ^ 2 * L / sB := by
    ring
  rw [h2]
  linarith


/-! ## `lem:app-dyn-taylor` -/

/-- `lem:app-dyn-taylor`, snapshot `cr-2026-10-23`. On `{Δ_t ∈ 𝒦}` (indicator form), for `0 ≤ r ≤ 4L`,
the same-buffer update is the first-order Taylor expansion with step `λ = h/B` along the tangent
`V̇̂_r = dynTangent`. The constant `B₀`, `K` depend on the fixed parameters and `𝒦` only.
Statement verbatim from `section.tex` (ll. 1656–1663):
```latex
\begin{lemma}[Taylor transfer]\label{lem:app-dyn-taylor}
In the setting of \cref{lem:app-dyn-coupling}, let $\dot{\widehat V}_r$ be the
tangent of \cref{lem:app-dyn-tangent} for the same-buffer chain at
$(t,\Dt,M^\circ_{t-1})$. On $\{\Dt\in\mathcal K\}$, for $0\le r\le4L$,
\[
\EE_t\big\|{\mathsf S}_{t+r}-\widehat V_r-\lr\,\dot{\widehat V}_r\big\|_\F\le\frac{Cr^2\log(2B)}{\sqrt B}.
\]
\end{lemma}
```
-/
theorem lem_app_dyn_taylor (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) (rlo rhi E : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ B0 : ℕ, ∃ K : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B), B0 ≤ B → ∀ t r : ℕ, r ≤ 4 * blockLen B →
      Integrable ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => fro (dynUpd S (t + r) ω - dynHatV p S t r ω - (p.h / B) • dynTangent p S t r ω))) P ∧
        ∀ᵐ ω ∂P, ω ∈ dynInK S t (rlo, rhi, E) →
          condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
            (fun ω => fro (dynUpd S (t + r) ω - dynHatV p S t r ω - (p.h / B) • dynTangent p S t r ω)))
            ω ≤ K * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt B := by
  obtain ⟨B0m, hB0m⟩ := lem_app_dyn_movement_ii p rlo rhi E hrlo hle
  obtain ⟨B0c, K1, hK1, hcoup⟩ := taylor_coupling certOp p rlo rhi E hrlo hle
  have hϱ := p.hϱ
  have hC : 0 ≤ p.CSig := le_trans (by norm_num) p.hC
  have hγ := p.hγ
  have hh := p.hh
  have hrhi : 0 < rhi := lt_of_lt_of_le hrlo hle
  have hlo : 0 < rlo * p.ϱ := mul_pos hrlo hϱ
  have hlh : rlo * p.ϱ ≤ 4 * rhi * p.ϱ := by nlinarith
  obtain ⟨Cd, hCd0, hCd⟩ := taylor_det hlo hlh
  have hw40 : 0 ≤ (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hlo.le _
  have hκ0 : 0 ≤ Cd * Real.sqrt p.γstar *
        (2 * p.ϱ * Real.sqrt (4 * rhi) * (p.CSig * p.h * Real.sqrt p.γstar)) ^ 2 +
      Cd * Real.sqrt p.γstar * (p.ϱ * p.CSig ^ 2 * p.h ^ 2 * Real.sqrt p.γstar ^ 2) +
      Cd * (2 * p.ϱ * Real.sqrt (4 * rhi) * (p.CSig * p.h * Real.sqrt p.γstar)) * Real.sqrt K1 +
      Cd * Real.sqrt p.γstar * (2 * p.ϱ * Real.sqrt (2 * rhi) * p.CSig * p.h) * Real.sqrt K1 +
      (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) *
        Real.sqrt (cMConst p.CSig p.γstar * p.CSig ^ 2 * p.h ^ 2 * K1) := by positivity
  refine ⟨max (max B0m B0c) 1, (Cd * Real.sqrt p.γstar *
        (2 * p.ϱ * Real.sqrt (4 * rhi) * (p.CSig * p.h * Real.sqrt p.γstar)) ^ 2 +
      Cd * Real.sqrt p.γstar * (p.ϱ * p.CSig ^ 2 * p.h ^ 2 * Real.sqrt p.γstar ^ 2) +
      Cd * (2 * p.ϱ * Real.sqrt (4 * rhi) * (p.CSig * p.h * Real.sqrt p.γstar)) * Real.sqrt K1 +
      Cd * Real.sqrt p.γstar * (2 * p.ϱ * Real.sqrt (2 * rhi) * p.CSig * p.h) * Real.sqrt K1 +
      (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) *
        Real.sqrt (cMConst p.CSig p.γstar * p.CSig ^ 2 * p.h ^ 2 * K1)) / Real.log 2 + Cd * K1, ?_⟩
  intro Ω _ P _ m n B S hB t r hr
  have hB1 : 0 < B := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hB)
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB1
  have hB1r : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hsB : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogB : Real.log 2 ≤ Real.log (2 * (B : ℝ)) := Real.log_le_log (by norm_num) (by linarith)
  have hL : 0 < Real.log (2 * (B : ℝ)) := lt_of_lt_of_le hlog2 hlogB
  have hmov := hB0m Ω P m n B S ((le_max_left _ _).trans ((le_max_left _ _).trans hB))
  have hBc : B0c ≤ B := (le_max_right _ _).trans ((le_max_left _ _).trans hB)
  have hcB := hcoup Ω P m n B S hBc hB1 t
  have hA : MeasurableSet[dynPast S t] (dynInK S t (rlo, rhi, E)) := coupling_A_meas S t _
  have hAm : MeasurableSet (dynInK S t (rlo, rhi, E)) := buffer_past_le S t _ hA
  obtain ⟨hR1, -, -, -, hRo⟩ := hcB r hr
  have hR2 := (hcB r hr).2.2.1
  -- the sum of update errors
  have hSk : ∀ k < r, _ := fun k (hk : k < r) => hcB k ((le_of_lt hk).trans hr)
  have hfSm : Measurable (fun ω => ∑ k ∈ Finset.range r,
      (dynInK S t (rlo, rhi, E)).indicator (fun ω => fro (dynErrS p S t k ω)) ω) :=
    Finset.measurable_sum _ fun k _ =>
      (taylor_fro_cont.measurable.comp (coupling_errS_meas S hB1 t k)).indicator hAm
  obtain ⟨hfSi, hfSc⟩ := taylor_cond_sum' (dynPast S t) (buffer_past_le S t) r 0 (fun _ => 1)
    (fun _ _ => zero_le_one)
    (fun k => (dynInK S t (rlo, rhi, E)).indicator (fun ω => fro (dynErrS p S t k ω)))
    (fun k hk => (hSk k (Finset.mem_range.mp hk)).2.1.1) (fun k => Real.sqrt K1 * k)
    (fun k hk => (hSk k (Finset.mem_range.mp hk)).2.1.2) _ hfSm.aestronglyMeasurable
    (fun ω => Finset.sum_nonneg fun k _ => Set.indicator_nonneg (fun _ _ => movement_fro_nn _) ω)
    (fun ω => by simp)
  have hfSc' : ∀ᵐ ω ∂P, condExp (dynPast S t) P (fun ω => ∑ k ∈ Finset.range r,
      (dynInK S t (rlo, rhi, E)).indicator (fun ω => fro (dynErrS p S t k ω)) ω) ω ≤
        Real.sqrt K1 * (r : ℝ) ^ 2 := by
    filter_upwards [hfSc] with ω hω
    refine hω.trans ?_
    rw [zero_add]
    calc ∑ k ∈ Finset.range r, 1 * (Real.sqrt K1 * (k : ℝ))
        ≤ ∑ k ∈ Finset.range r, Real.sqrt K1 * (r : ℝ) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have : (k : ℝ) ≤ r := by exact_mod_cast (le_of_lt (Finset.mem_range.mp hk))
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
      _ = Real.sqrt K1 * (r : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  -- the quadratic buffer term
  set aB : ℝ := Real.sqrt B / Real.log (2 * (B : ℝ)) with haB
  have haB0 : 0 < aB := div_pos hsB hL
  have hfRRm : Measurable ((dynInK S t (rlo, rhi, E)).indicator
      (fun ω => opNorm (dynErrM p S t r ω) * fro (dynErrM p S t r ω))) :=
    (((buffer_opNorm_continuous.measurable.comp (coupling_errM_meas S t r))).mul
      (taylor_fro_cont.measurable.comp (coupling_errM_meas S t r))).indicator hAm
  obtain ⟨hfRRi, hfRRc⟩ := taylor_cond2 (dynPast S t) (buffer_past_le S t) (aB / 2)
    (1 / (2 * aB)) _ _ (by positivity) (by positivity) _ _ hRo.1 hR2.1 hRo.2 hR2.2 _
    hfRRm.aestronglyMeasurable
    (fun ω => Set.indicator_nonneg (fun _ _ => mul_nonneg (movement_opNorm_nonneg _)
      (movement_fro_nn _)) ω)
    (fun ω => by
      by_cases hω : ω ∈ dynInK S t (rlo, rhi, E)
      · simp only [Set.indicator_of_mem hω]
        set x := opNorm (dynErrM p S t r ω)
        set y := fro (dynErrM p S t r ω)
        have e : aB / 2 * x ^ 2 + 1 / (2 * aB) * y ^ 2 - x * y = (aB * x - y) ^ 2 / (2 * aB) := by
          field_simp
          ring
        have : 0 ≤ (aB * x - y) ^ 2 / (2 * aB) := by positivity
        linarith
      · simp [Set.indicator_of_notMem hω])
  have hfRRc' : ∀ᵐ ω ∂P, condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
      (fun ω => opNorm (dynErrM p S t r ω) * fro (dynErrM p S t r ω))) ω ≤
        K1 * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt B := by
    filter_upwards [hfRRc] with ω hω
    refine hω.trans (le_of_eq ?_)
    rw [haB]
    exact taylor_amgm_arith K1 r (Real.sqrt B) (Real.log (2 * (B : ℝ))) B hsB hL
      (Real.sq_sqrt hBr.le)
  -- the tangent replacement
  obtain ⟨hGi, hGc⟩ := taylor_G_bound S hB1 hA r K1 hK1 (fun k hk => (hSk k hk).2.2.2.1)
  -- assemble
  obtain ⟨hint, hcond⟩ := taylor_cond4 (dynPast S t) (buffer_past_le S t)
    (Cd * Real.sqrt (p.γstar * B) *
          (2 * p.ϱ * Real.sqrt (4 * rhi) * (p.CSig * p.h * Real.sqrt p.γstar) * r /
            Real.sqrt B) ^ 2 +
        Cd * Real.sqrt (p.γstar * B) *
          (2 * p.ϱ * (p.CSig ^ 2 * (p.h * Real.sqrt p.γstar * r / Real.sqrt B) ^ 2 / 2)))
    (Cd * (2 * p.ϱ * Real.sqrt (4 * rhi) * (p.CSig * p.h * Real.sqrt p.γstar) * r /
            Real.sqrt B))
    (Cd * Real.sqrt (p.γstar * B) * (2 * p.ϱ * (Real.sqrt (2 * rhi) * p.CSig * (p.h / B))))
    Cd ((rlo * p.ϱ) ^ (-(1 / 2 : ℝ)))
    (Real.sqrt K1 * r) (Real.sqrt K1 * (r : ℝ) ^ 2)
    (K1 * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt B)
    (Real.sqrt (cMConst p.CSig p.γstar * p.CSig ^ 2 * p.h ^ 2 * K1) * (r : ℝ) ^ 2 /
        Real.sqrt B)
    (by positivity) (by positivity) hCd0 hw40 _ _ _ _ hR1.1 hfSi hfRRi hGi hR1.2 hfSc' hfRRc' hGc
    _ (taylor_X_meas S hB1 rlo rhi E hrlo t r).aestronglyMeasurable
    (fun ω => Set.indicator_nonneg (fun _ _ => movement_fro_nn _) ω)
    (fun ω => by
      by_cases hω : ω ∈ dynInK S t (rlo, rhi, E)
      · have h0 : dynDelta S t ω ∈ admSetOf S.C (rlo, rhi, E) := hω
        have hr' : dynDelta S (t + r) ω ∈ admSetOf S.C (enl (rlo, rhi, E)) := by
          refine (hmov ω t h0).2 (t + r) ?_
          have : |((t + r : ℕ) : ℤ) - (t : ℤ)| = r := by
            push_cast
            simp
          rw [this]
          exact_mod_cast hr
        have hp := taylor_path S hB1 rlo rhi E hrlo Cd hCd0
          (fun ℓ ℓ' a h1 h2 N M X => hCd ℓ ℓ' a h1 h2 N M X) t r ω h0 hr'
        simp only [Set.indicator_of_mem hω]
        exact hp
      · simp only [Set.indicator_of_notMem hω, mul_zero, Finset.sum_const_zero, add_zero]
        positivity)
  refine ⟨hint, ?_⟩
  filter_upwards [hcond] with ω hω _
  refine hω.trans ?_
  rw [Real.sqrt_mul hγ]
  exact taylor_arith Cd (Real.sqrt p.γstar)
    (2 * p.ϱ * Real.sqrt (4 * rhi) * (p.CSig * p.h * Real.sqrt p.γstar)) p.ϱ p.CSig p.h rhi K1
    ((rlo * p.ϱ) ^ (-(1 / 2 : ℝ))) (Real.sqrt (cMConst p.CSig p.γstar * p.CSig ^ 2 * p.h ^ 2 * K1))
    r (Real.sqrt B) (Real.log (2 * (B : ℝ))) (Real.log 2) B hsB hlog2 hlogB (Real.sq_sqrt hBr.le)
    (Nat.cast_nonneg _) hκ0

/-! ## `lem:app-dyn-quadratic`: helpers -/

private lemma quad_blockLen_pos {B : ℕ} (hB : 0 < B) : 0 < blockLen B := by
  unfold blockLen
  apply Nat.floor_pos.mpr
  exact Real.one_le_rpow (by exact_mod_cast hB) (by norm_num)

private lemma quad_blockLen_le {B : ℕ} (hB : 1 ≤ B) : (blockLen B : ℝ) ≤ B := by
  have h1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  unfold blockLen
  calc
    ((⌊(B : ℝ) ^ ((1 : ℝ) / 8)⌋₊ : ℕ) : ℝ) ≤ (B : ℝ) ^ ((1 : ℝ) / 8) :=
      Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    _ ≤ (B : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    _ = B := Real.rpow_one _

/-- The future samples after time `t`: the batches of the steps `≥ t` and the auxiliary batches. -/
private abbrev QFut (m n B : ℕ) :=
  (ℕ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)

private def qFut {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (cs : ChainSamples P m n B) (t : ℕ) (ω : Ω) : QFut m n B :=
  (fun k a => cs.act ((t : ℤ) + k + 1) a ω, fun j a => cs.aux (t : ℤ) j a ω)

private def qEma {m n B : ℕ} (p : DynParams) (C : Covariances m n) (D init : Mat m n)
    (y : QFut m n B) : ℕ → Mat m n
  | 0 => init
  | k + 1 => p.β • qEma p C D init y k + (1 - p.β) • batchGrad D (fun a => phys C (y.1 k a))

private def qInit {m n B : ℕ} (p : DynParams) (C : Covariances m n) (D : Mat m n)
    (y : QFut m n B) : Mat m n :=
  ∑' j : ℕ, emaW p.β j • batchGrad D (fun a => phys C (y.2 j a))

private lemma qEma_eq {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D init : Mat m n)
    (ω : Ω) (k : ℕ) :
    qEma p C D init (qFut cs t ω) k =
      emaChain p.β D (fun s => physBatch C (cs.act s) ω) t init k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [qEma, emaChain]
    rw [ih]
    rfl

private lemma qInit_eq {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n)
    (ω : Ω) : qInit p C D (qFut cs t ω) = chainInit p.β C D (cs.aux (t : ℤ)) ω := rfl

private lemma qStat_eq {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n)
    (ω : Ω) (r : ℕ) :
    Q (physRidge p C D) (qEma p C D (qInit p C D (qFut cs t ω)) (qFut cs t ω) (r + 1)) =
      (def_app_dyn_chains p C cs t D M ω).statV (r + 1) := by
  rw [qEma_eq, qInit_eq]
  rfl

private lemma qSame_eq {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n)
    (ω : Ω) (r : ℕ) :
    Q (physRidge p C D) (qEma p C D M (qFut cs t ω) (r + 1)) =
      (def_app_dyn_chains p C cs t D M ω).sameV (r + 1) := by
  rw [qEma_eq]
  rfl

private lemma qChain_meas {m n B : ℕ} (p : DynParams) (C : Covariances m n) (r : ℕ) :
    Measurable (fun z : (Mat m n × Mat m n) × QFut m n B =>
      Q (physRidge p C z.1.1) (qEma p C z.1.1 (qInit p C z.1.1 z.2) z.2 (r + 1))) ∧
    Measurable (fun z : (Mat m n × Mat m n) × QFut m n B =>
      Q (physRidge p C z.1.1) (qEma p C z.1.1 z.1.2 z.2 (r + 1))) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) :=
    inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hinit : Measurable (fun z : (Mat m n × Mat m n) × QFut m n B =>
      qInit p C z.1.1 z.2) := by
    unfold qInit
    refine Measurable.tsum fun j => Measurable.const_smul ?_ (emaW p.β j)
    unfold batchGrad grad resid phys outer
    fun_prop
  have hema : ∀ (I : (Mat m n × Mat m n) × QFut m n B → Mat m n), Measurable I → ∀ k,
      Measurable (fun z : (Mat m n × Mat m n) × QFut m n B => qEma p C z.1.1 (I z) z.2 k) := by
    intro I hI k
    induction k with
    | zero => simpa only [qEma] using hI
    | succ k ih =>
      have hb : Measurable (fun z : (Mat m n × Mat m n) × QFut m n B =>
          batchGrad z.1.1 (fun a => phys C (z.2.1 k a))) := by
        unfold batchGrad grad resid phys outer
        fun_prop
      simp only [qEma]
      exact (ih.const_smul p.β).add (hb.const_smul (1 - p.β))
  have hρ : ∀ z : (Mat m n × Mat m n) × QFut m n B, 0 ≤ physRidge p C z.1.1 := fun z =>
    coupling_ridge_nonneg (p := p) C _
  have hρm : Measurable (fun z : (Mat m n × Mat m n) × QFut m n B =>
      (⟨physRidge p C z.1.1, hρ z⟩ : Set.Ici (0 : ℝ))) := by
    have hrisk : Continuous (fun D : Mat m n => riskSigma C D) := by
      unfold riskSigma pairSigma
      fun_prop
    exact (((hrisk.measurable.comp (measurable_fst.comp measurable_fst)).const_mul 2).mul_const
      p.ϱ).subtype_mk
  exact ⟨measurable_Q.comp (hρm.prodMk (hema _ hinit (r + 1))),
    measurable_Q.comp (hρm.prodMk (hema _ (measurable_snd.comp measurable_fst) (r + 1)))⟩

private lemma quad_Y_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) : Measurable (qFut S.cs t) := by
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro k
    apply Measurable.of_eval
    intro a
    exact S.cs.meas_act ((t : ℤ) + k + 1) a
  · apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro a
    exact S.cs.meas_aux (t : ℤ) j a

private lemma quad_Y_indep {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) :
    Indep (dynPast S t) (MeasurableSpace.comap (qFut S.cs t) inferInstance) P := by
  have hYcomap : MeasurableSpace.comap (qFut S.cs t) inferInstance ≤ chainFuture S.cs t := by
    unfold qFut
    change (MeasurableSpace.prod
      (inferInstance : MeasurableSpace (ℕ → Fin B → Vec m × Vec n))
      (inferInstance : MeasurableSpace (ℕ → Fin B → Vec m × Vec n))).comap
        (fun ω => ((fun (k : ℕ) a => S.cs.act ((t : ℤ) + (k : ℤ) + 1) a ω),
          fun j a => S.cs.aux (t : ℤ) j a ω)) ≤ chainFuture S.cs t
    rw [MeasurableSpace.comap_prodMk]
    simp_rw [MeasurableSpace.comap_process_pi]
    refine sup_le (iSup_le fun k => iSup_le fun a => ?_)
      (iSup_le fun j => iSup_le fun a => ?_)
    · apply le_sup_of_le_left
      refine le_iSup_of_le ((t : ℤ) + k + 1) (le_iSup_of_le (by omega) ?_)
      exact le_iSup_of_le a le_rfl
    · apply le_sup_of_le_right
      exact le_iSup_of_le j (le_iSup_of_le a le_rfl)
  exact indep_of_indep_of_le_right (buffer_indep_past_future S t) hYcomap

private lemma quad_X_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S t] (fun ω => (dynDelta S t ω, dynBuf S t ω)) :=
  (buffer_delta_meas S t).prodMk (buffer_state_meas S t).2

private lemma quad_freeze {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ)
    (f : Mat m n × Mat m n → QFut m n B → ℝ) (hf : Measurable (Function.uncurry f))
    (hint : Integrable (fun ω => f (dynDelta S t ω, dynBuf S t ω) (qFut S.cs t ω)) P) :
    condExp (dynPast S t) P (fun ω => f (dynDelta S t ω, dynBuf S t ω) (qFut S.cs t ω)) =ᵐ[P]
      fun ω => ∫ ω', f (dynDelta S t ω, dynBuf S t ω) (qFut S.cs t ω') ∂P := by
  have hY := quad_Y_meas S t
  have hfreeze := Muon.Foundations.freezing_condExp (dynPast S t) (buffer_past_le S t)
    (quad_X_meas S t) hY (quad_Y_indep S t) hf hint
  filter_upwards [hfreeze] with ω hω
  rw [hω]
  have hfm : Measurable (f (dynDelta S t ω, dynBuf S t ω)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  exact integral_map hY.aemeasurable hfm.aestronglyMeasurable


private lemma quad_Ahat_norm {m n : ℕ} (C : Covariances m n) (D : Mat m n)
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

/-- The physical mean bound `‖V̄(D)‖_F ≤ C` of `eqn:app-dyn-mean-physical` at one dimension. -/
private lemma quad_mean_bound (p : DynParams) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (Cv : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n),
      SizeFin Cv B p.γstar p.CSig → 0 < B → 0 < riskSigma Cv D →
      fro (mean P (fun ω => stationaryV p Cv cs t D 0 ω)) ≤ Cm := by
  obtain ⟨C3, h3⟩ := lem_app_dyn_mean_iii_ema p.γstar p.CSig p.ϱ p.ϱ p.hϱ le_rfl
  refine ⟨|C3|, abs_nonneg _, ?_⟩
  intro Ω _ P _ m n B Cv cs t D hsize hB hD
  let F : FrozenParams m n B :=
    { C := Cv
      A := Ahat Cv D
      hA := quad_Ahat_norm Cv D hD
      β := p.β
      hβ := p.hβ
      hB := hB }
  let S : FrozenSamples P m n B :=
    { zw := cs.act
      meas := cs.meas_act
      indep := cs.indep.precomp Sum.inl_injective
      law := cs.law_act }
  obtain ⟨-, -, -, -, hmean⟩ := lem_app_dyn_chains_i p Cv cs t D 0 hD F rfl rfl rfl S
  obtain ⟨-, -, -, hb⟩ := h3 m n B Ω P S F (t : ℤ) hsize.1 hsize.2.1 hsize.2.2
  have hb' := hb p.ϱ ⟨le_rfl, le_rfl⟩
  have hf2 : 0 ≤ fro (mean P (fun ω => dQ p.ϱ (frozenBuf F S (t : ℤ) ω))) := Real.sqrt_nonneg _
  change fro (mean P (fun ω => (def_app_dyn_chains p Cv cs t D 0 ω).statV 1)) ≤ _
  rw [hmean]
  change fro (mean P (fun ω => Q p.ϱ (frozenBuf F S (t : ℤ) ω))) ≤ _
  linarith [le_abs_self C3]

private lemma quad_Q_fro {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (ρ : ℝ) (hρ : 0 ≤ ρ) (K : Mat m n) :
    fro (Q ρ K) ≤ Real.sqrt (p.γstar * B) :=
  Real.le_sqrt_of_sq_le (coupling_Q_fro_sq S ρ hρ K)

private lemma quad_sum_fro {m n : ℕ} (k : ℕ) (x : ℕ → Mat m n) (c : ℝ)
    (hx : ∀ r, fro (x r) ≤ c) : fro (∑ r ∈ Finset.range k, x r) ≤ k * c := by
  refine (coupling_norm_finset_sum fro coupling_fro_props.2.1 coupling_fro_props.2.2.1 k x).trans ?_
  calc ∑ r ∈ Finset.range k, fro (x r) ≤ ∑ r ∈ Finset.range k, c := Finset.sum_le_sum fun r _ => hx r
    _ = k * c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `lem:app-dyn-startup`(ii) applied conditionally on `𝓕_t` (`section.tex` l. 2011). -/
private lemma quad_cross_A (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B) (t : ℕ) (W : Mat m n →ₗ[ℝ] Mat m n),
      (∀ X : Mat m n, fro (W X) ≤ fro X) →
      Integrable ({ω | dynDelta S t ω ∈ admA p S.C}.indicator (fun ω => frobIP (dynStatSum p S t ω)
        (W (∑ r ∈ Finset.range (blockLen B), dynErrV p S t r ω)))) P ∧
      ∀ᵐ ω ∂P, |condExp (dynPast S t) P ({ω | dynDelta S t ω ∈ admA p S.C}.indicator
        (fun ω => frobIP (dynStatSum p S t ω)
          (W (∑ r ∈ Finset.range (blockLen B), dynErrV p S t r ω)))) ω| ≤
        K * (1 + fro (dynBuf S t ω) / Real.sqrt B) * (B + (blockLen B : ℝ) * Real.sqrt B) := by
  have hr0 := p.hr0
  have hr := p.hr
  obtain ⟨K2, hK2⟩ := lem_app_dyn_startup_ii certOp p (p.r0 / 2) (p.r1 + 1 / 2) (by linarith)
    (by linarith)
  refine ⟨|K2|, abs_nonneg _, ?_⟩
  intro Ω _ P _ m n B S t W hW
  set L := blockLen B with hLdef
  have hWm : Measurable W := by fun_prop
  have hAset : MeasurableSet (admA p S.C) := coupling_admSet_meas S.C _
  let sV : Mat m n × Mat m n → QFut m n B → ℕ → Mat m n := fun x y r =>
    Q (physRidge p S.C x.1) (qEma p S.C x.1 (qInit p S.C x.1 y) y (r + 1))
  let hV : Mat m n × Mat m n → QFut m n B → ℕ → Mat m n := fun x y r =>
    Q (physRidge p S.C x.1) (qEma p S.C x.1 x.2 y (r + 1))
  let f : Mat m n × Mat m n → QFut m n B → ℝ := fun x y =>
    (admA p S.C).indicator (fun _ => (1 : ℝ)) x.1 *
      frobIP (∑ r ∈ Finset.range L, sV x y r) (W (∑ r ∈ Finset.range L, (hV x y r - sV x y r)))
  have hsVm : ∀ r, Measurable (fun z : (Mat m n × Mat m n) × QFut m n B => sV z.1 z.2 r) :=
    fun r => (qChain_meas p S.C r).1
  have hhVm : ∀ r, Measurable (fun z : (Mat m n × Mat m n) × QFut m n B => hV z.1 z.2 r) :=
    fun r => (qChain_meas p S.C r).2
  have hf : Measurable (Function.uncurry f) := by
    have h1 : Measurable (fun z : (Mat m n × Mat m n) × QFut m n B =>
        (admA p S.C).indicator (fun _ => (1 : ℝ)) z.1.1) :=
      (measurable_const.indicator hAset).comp (measurable_fst.comp measurable_fst)
    have h2 : Measurable (fun z : (Mat m n × Mat m n) × QFut m n B =>
        ∑ r ∈ Finset.range L, sV z.1 z.2 r) := Finset.measurable_sum _ fun r _ => hsVm r
    have h3 : Measurable (fun z : (Mat m n × Mat m n) × QFut m n B =>
        W (∑ r ∈ Finset.range L, (hV z.1 z.2 r - sV z.1 z.2 r))) :=
      hWm.comp (Finset.measurable_sum _ fun r _ => (hhVm r).sub (hsVm r))
    have h4 := h1.mul (startup_frobIP_cont.measurable.comp (h2.prodMk h3))
    change Measurable (fun z : (Mat m n × Mat m n) × QFut m n B =>
      (admA p S.C).indicator (fun _ => (1 : ℝ)) z.1.1 *
        frobIP (∑ r ∈ Finset.range L, sV z.1 z.2 r)
          (W (∑ r ∈ Finset.range L, (hV z.1 z.2 r - sV z.1 z.2 r))))
    exact h4
  have hstat : ∀ ω r, sV (dynDelta S t ω, dynBuf S t ω) (qFut S.cs t ω) r =
      stationaryV p S.C S.cs t (dynDelta S t ω) r ω := fun ω r =>
    qStat_eq p S.C S.cs t (dynDelta S t ω) 0 ω r
  have hsame : ∀ ω r, hV (dynDelta S t ω, dynBuf S t ω) (qFut S.cs t ω) r =
      dynHatV p S t r ω := fun ω r =>
    qSame_eq p S.C S.cs t (dynDelta S t ω) (dynBuf S t ω) ω r
  have heq : {ω | dynDelta S t ω ∈ admA p S.C}.indicator (fun ω => frobIP (dynStatSum p S t ω)
        (W (∑ r ∈ Finset.range L, dynErrV p S t r ω))) =
      fun ω => f (dynDelta S t ω, dynBuf S t ω) (qFut S.cs t ω) := by
    funext ω
    simp only [f, hstat, hsame]
    by_cases h : dynDelta S t ω ∈ admA p S.C
    · rw [Set.indicator_of_mem (show ω ∈ {ω | dynDelta S t ω ∈ admA p S.C} from h),
        Set.indicator_of_mem h, one_mul]
      rfl
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | dynDelta S t ω ∈ admA p S.C} from h),
        Set.indicator_of_notMem h, zero_mul]
  -- boundedness
  have hγB : 0 ≤ Real.sqrt (p.γstar * B) := Real.sqrt_nonneg _
  have hfb : ∀ x y, |f x y| ≤ (L * Real.sqrt (p.γstar * B)) * (L * (2 * Real.sqrt (p.γstar * B))) := by
    intro x y
    have hρ := coupling_ridge_nonneg (p := p) S.C x.1
    have hs : fro (∑ r ∈ Finset.range L, sV x y r) ≤ L * Real.sqrt (p.γstar * B) :=
      quad_sum_fro L _ _ fun r => quad_Q_fro S _ hρ _
    have ha : fro (W (∑ r ∈ Finset.range L, (hV x y r - sV x y r))) ≤
        L * (2 * Real.sqrt (p.γstar * B)) :=
      (hW _).trans (quad_sum_fro L _ _ fun r => (coupling_fro_sub_le _ _).trans (by
        have := quad_Q_fro S _ hρ (qEma p S.C x.1 x.2 y (r + 1))
        have := quad_Q_fro S _ hρ (qEma p S.C x.1 (qInit p S.C x.1 y) y (r + 1))
        linarith))
    have hip := startup_frobIP_le (∑ r ∈ Finset.range L, sV x y r)
      (W (∑ r ∈ Finset.range L, (hV x y r - sV x y r)))
    have hind : |(admA p S.C).indicator (fun _ => (1 : ℝ)) x.1| ≤ 1 := by
      by_cases h : x.1 ∈ admA p S.C <;> simp [h]
    simp only [f, abs_mul]
    calc |(admA p S.C).indicator (fun _ => (1 : ℝ)) x.1| *
          |frobIP (∑ r ∈ Finset.range L, sV x y r) (W (∑ r ∈ Finset.range L, (hV x y r - sV x y r)))|
        ≤ 1 * (fro (∑ r ∈ Finset.range L, sV x y r) *
            fro (W (∑ r ∈ Finset.range L, (hV x y r - sV x y r)))) :=
          mul_le_mul hind hip (abs_nonneg _) zero_le_one
      _ ≤ _ := by
          rw [one_mul]
          exact mul_le_mul hs ha (movement_fro_nn _) (by positivity)
  have hXY : Measurable (fun ω => ((dynDelta S t ω, dynBuf S t ω), qFut S.cs t ω)) :=
    ((quad_X_meas S t).mono (buffer_past_le S t) le_rfl).prodMk (quad_Y_meas S t)
  have hint : Integrable (fun ω => f (dynDelta S t ω, dynBuf S t ω) (qFut S.cs t ω)) P :=
    Integrable.of_bound (hf.comp hXY).aestronglyMeasurable _
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hfb _ _)
  rw [heq]
  refine ⟨hint, ?_⟩
  have hfr := quad_freeze S t f hf hint
  filter_upwards [hfr] with ω hω
  rw [hω]
  set x := (dynDelta S t ω, dynBuf S t ω) with hx
  have hmeasω : Measurable (fun ω' => ((x, qFut S.cs t ω') : (Mat m n × Mat m n) × QFut m n B)) :=
    measurable_const.prodMk (quad_Y_meas S t)
  have hK0 : 0 ≤ (1 + fro x.2 / Real.sqrt B) * (B + (L : ℝ) * Real.sqrt B) :=
    mul_nonneg (add_nonneg zero_le_one (div_nonneg (movement_fro_nn _) (Real.sqrt_nonneg _)))
      (by positivity)
  by_cases h : x.1 ∈ admA p S.C
  · have hfx : ∀ ω', f x (qFut S.cs t ω') = frobIP (∑ r ∈ Finset.range L,
        stationaryV p S.C S.cs t x.1 r ω')
        (W (∑ r ∈ Finset.range L, ((def_app_dyn_chains p S.C S.cs t x.1 x.2 ω').sameV (r + 1) -
          (def_app_dyn_chains p S.C S.cs t x.1 x.2 ω').statV (r + 1)))) := by
      intro ω'
      simp only [f, Set.indicator_of_mem h, one_mul, sV, hV, qStat_eq p S.C S.cs t x.1 x.2 ω',
        qSame_eq p S.C S.cs t x.1 x.2 ω']
      rfl
    simp_rw [hfx]
    obtain ⟨hlo, hhi, -⟩ := h
    have hb := (hK2 Ω P m n B S.C S.cs t x.1 x.2 W S.size hlo hhi hW).2
    refine hb.trans ?_
    have := mul_le_mul_of_nonneg_right (le_abs_self K2) hK0
    calc K2 * (1 + fro x.2 / Real.sqrt B) * (B + (blockLen B : ℝ) * Real.sqrt B)
        = K2 * ((1 + fro x.2 / Real.sqrt B) * (B + (L : ℝ) * Real.sqrt B)) := by ring
      _ ≤ |K2| * ((1 + fro x.2 / Real.sqrt B) * (B + (L : ℝ) * Real.sqrt B)) := this
      _ = _ := by ring
  · have hfx : ∀ ω', f x (qFut S.cs t ω') = 0 := by
      intro ω'
      simp only [f, Set.indicator_of_notMem h, zero_mul]
    simp_rw [hfx]
    simp only [integral_zero, abs_zero]
    have := mul_nonneg (abs_nonneg K2) hK0
    calc (0 : ℝ) ≤ |K2| * ((1 + fro x.2 / Real.sqrt B) * (B + (L : ℝ) * Real.sqrt B)) := this
      _ = _ := by ring


private lemma quad_S_fixed (p : DynParams) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n),
      SizeFin C B p.γstar p.CSig → 0 < B → D ∈ admA p C →
      Measurable (fun ω => fro (∑ r ∈ Finset.range (blockLen B), stationaryV p C cs t D r ω) ^ 2) →
      ∫ ω, fro (∑ r ∈ Finset.range (blockLen B), stationaryV p C cs t D r ω) ^ 2 ∂P ≤
        c0 * (B * blockLen B + (blockLen B : ℝ) ^ 2) := by
  have hr0 := p.hr0
  have hr := p.hr
  obtain ⟨K1, hK1⟩ := lem_app_dyn_startup_i p (p.r0 / 2) (p.r1 + 1 / 2) (by linarith) (by linarith)
  obtain ⟨Cm, hCm0, hCm⟩ := quad_mean_bound p
  refine ⟨2 * |K1| + 2 * Cm ^ 2, by positivity, ?_⟩
  intro Ω _ P _ m n B C cs t D hsize hB hD hSm
  set L := blockLen B with hLdef
  obtain ⟨hlo, hhi, -⟩ := hD
  have hR : 0 < riskSigma C D := lt_of_lt_of_le (by simp only [admBase]; linarith) hlo
  obtain ⟨hI, hb⟩ := hK1 Ω P m n B C cs t D 0 hsize hlo hhi
  have hmean := hCm Ω P m n B C cs t D hsize hB hR
  set Vb := mean P (fun ω' => stationaryV p C cs t D 0 ω') with hVb
  have hpt : ∀ ω', fro (∑ r ∈ Finset.range L, stationaryV p C cs t D r ω') ^ 2 ≤
      2 * fro (∑ r ∈ Finset.range L, stationaryV p C cs t D r ω' - (L : ℝ) • Vb) ^ 2 +
        2 * ((L : ℝ) * Cm) ^ 2 := by
    intro ω'
    set U := ∑ r ∈ Finset.range L, stationaryV p C cs t D r ω'
    have h1 : fro U ≤ fro (U - (L : ℝ) • Vb) + fro ((L : ℝ) • Vb) := by
      have := coupling_fro_props.2.1 (U - (L : ℝ) • Vb) ((L : ℝ) • Vb)
      rwa [sub_add_cancel] at this
    have h2 : fro ((L : ℝ) • Vb) ≤ (L : ℝ) * Cm := by
      rw [coupling_fro_props.1 _ _ (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg _)
    have h3 := pow_le_pow_left₀ (movement_fro_nn _) (h1.trans (add_le_add le_rfl h2)) 2
    exact h3.trans (coupling_sq_add_le _ _)
  have hRint : Integrable (fun ω' => 2 * fro (∑ r ∈ Finset.range L,
      stationaryV p C cs t D r ω' - (L : ℝ) • Vb) ^ 2 + 2 * ((L : ℝ) * Cm) ^ 2) P :=
    (hI.const_mul 2).add (integrable_const _)
  have hSint : Integrable (fun ω' =>
      fro (∑ r ∈ Finset.range L, stationaryV p C cs t D r ω') ^ 2) P :=
    hRint.mono' hSm.aestronglyMeasurable (ae_of_all _ fun ω' => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt ω')
  calc ∫ ω', fro (∑ r ∈ Finset.range L, stationaryV p C cs t D r ω') ^ 2 ∂P
      ≤ ∫ ω', (2 * fro (∑ r ∈ Finset.range L,
          stationaryV p C cs t D r ω' - (L : ℝ) • Vb) ^ 2 + 2 * ((L : ℝ) * Cm) ^ 2) ∂P :=
        integral_mono hSint hRint hpt
    _ = 2 * ∫ ω', fro (∑ r ∈ Finset.range L,
          stationaryV p C cs t D r ω' - (L : ℝ) • Vb) ^ 2 ∂P + 2 * ((L : ℝ) * Cm) ^ 2 := by
        rw [integral_add (hI.const_mul 2) (integrable_const _), integral_const_mul,
          integral_const, smul_eq_mul, probReal_univ, one_mul]
    _ ≤ 2 * (K1 * B * L) + 2 * ((L : ℝ) * Cm) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
        linarith
    _ ≤ (2 * |K1| + 2 * Cm ^ 2) * (B * L + (L : ℝ) ^ 2) := by
        have hK : K1 * B * L ≤ |K1| * (B * L) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        nlinarith [mul_nonneg (abs_nonneg K1) (sq_nonneg (L : ℝ)),
          mul_nonneg (sq_nonneg Cm) (mul_nonneg (Nat.cast_nonneg B) (Nat.cast_nonneg L))]

/-- `lem:app-dyn-startup`(i) with `eqn:app-dyn-mean-physical`, conditionally on `𝓕_t`:
`𝔼_t‖S‖_F² ≤ C(BL + L²)` on `{Δ_t ∈ 𝒜}` (`section.tex` ll. 2013–2014). -/
private lemma quad_S_sq (p : DynParams) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B), 0 < B → ∀ t : ℕ,
      Integrable ({ω | dynDelta S t ω ∈ admA p S.C}.indicator
        (fun ω => fro (dynStatSum p S t ω) ^ 2)) P ∧
      ∀ᵐ ω ∂P, condExp (dynPast S t) P ({ω | dynDelta S t ω ∈ admA p S.C}.indicator
        (fun ω => fro (dynStatSum p S t ω) ^ 2)) ω ≤
          K * (B * blockLen B + (blockLen B : ℝ) ^ 2) := by
  obtain ⟨c0, hc00, hc0⟩ := quad_S_fixed p
  refine ⟨c0, hc00, ?_⟩
  intro Ω _ P _ m n B S hB t
  set L := blockLen B with hLdef
  have hAset : MeasurableSet (admA p S.C) := coupling_admSet_meas S.C _
  let sV : Mat m n × Mat m n → QFut m n B → ℕ → Mat m n := fun x y r =>
    Q (physRidge p S.C x.1) (qEma p S.C x.1 (qInit p S.C x.1 y) y (r + 1))
  let f : Mat m n × Mat m n → QFut m n B → ℝ := fun x y =>
    (admA p S.C).indicator (fun _ => (1 : ℝ)) x.1 * fro (∑ r ∈ Finset.range L, sV x y r) ^ 2
  have hsVm : ∀ r, Measurable (fun z : (Mat m n × Mat m n) × QFut m n B => sV z.1 z.2 r) :=
    fun r => (qChain_meas p S.C r).1
  have hf : Measurable (Function.uncurry f) := by
    have h1 : Measurable (fun z : (Mat m n × Mat m n) × QFut m n B =>
        (admA p S.C).indicator (fun _ => (1 : ℝ)) z.1.1) :=
      (measurable_const.indicator hAset).comp (measurable_fst.comp measurable_fst)
    have h2 : Measurable (fun z : (Mat m n × Mat m n) × QFut m n B =>
        ∑ r ∈ Finset.range L, sV z.1 z.2 r) := Finset.measurable_sum _ fun r _ => hsVm r
    have h4 := h1.mul (buffer_fro_sq_meas.comp h2)
    change Measurable (fun z : (Mat m n × Mat m n) × QFut m n B =>
      (admA p S.C).indicator (fun _ => (1 : ℝ)) z.1.1 * fro (∑ r ∈ Finset.range L, sV z.1 z.2 r) ^ 2)
    exact h4
  have hind01 : ∀ x : Mat m n, 0 ≤ (admA p S.C).indicator (fun _ => (1 : ℝ)) x ∧
      (admA p S.C).indicator (fun _ => (1 : ℝ)) x ≤ 1 := by
    intro x
    by_cases h : x ∈ admA p S.C <;> simp [h]
  have hf0 : ∀ x y, 0 ≤ f x y := fun x y => mul_nonneg (hind01 x.1).1 (sq_nonneg _)
  have hfb : ∀ x y, f x y ≤ (L * Real.sqrt (p.γstar * B)) ^ 2 := by
    intro x y
    have hρ := coupling_ridge_nonneg (p := p) S.C x.1
    have hs : fro (∑ r ∈ Finset.range L, sV x y r) ≤ L * Real.sqrt (p.γstar * B) :=
      quad_sum_fro L _ _ fun r => quad_Q_fro S _ hρ _
    have h2 := pow_le_pow_left₀ (movement_fro_nn _) hs 2
    calc f x y ≤ 1 * fro (∑ r ∈ Finset.range L, sV x y r) ^ 2 :=
          mul_le_mul_of_nonneg_right (hind01 x.1).2 (sq_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h2
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = c0 * (B * L + (L : ℝ) ^ 2) := ⟨_, rfl⟩
  have hc0' : 0 ≤ c := by rw [hc]; positivity
  let g : Mat m n × Mat m n → ℝ := fun x => (admA p S.C).indicator (fun _ => c) x.1
  have hgint : Integrable (fun ω => g (dynDelta S t ω, dynBuf S t ω)) P := by
    refine Integrable.of_bound (((measurable_const.indicator hAset).comp
      (coupling_delta_meas S t)).aestronglyMeasurable) c (ae_of_all _ fun ω => ?_)
    by_cases h : dynDelta S t ω ∈ admA p S.C
    · simp [g, Set.indicator_of_mem h, abs_of_nonneg hc0']
    · simp [g, Set.indicator_of_notMem h, hc0']
  have hY := quad_Y_meas S t
  have hfm : ∀ x, Measurable (f x) := fun x => hf.of_uncurry_left
  have hfx : ∀ x, Integrable (f x) (P.map (qFut S.cs t)) := fun x =>
    Integrable.of_bound (hfm x).aestronglyMeasurable _ (ae_of_all _ fun y => by
      rw [Real.norm_of_nonneg (hf0 x y)]; exact hfb x y)
  have hbound : ∀ x, ∫ y, f x y ∂(P.map (qFut S.cs t)) ≤ g x := by
    intro x
    rw [integral_map hY.aemeasurable (hfm x).aestronglyMeasurable]
    by_cases h : x.1 ∈ admA p S.C
    · have hfx' : ∀ ω', f x (qFut S.cs t ω') =
          fro (∑ r ∈ Finset.range L, stationaryV p S.C S.cs t x.1 r ω') ^ 2 := by
        intro ω'
        simp only [f, Set.indicator_of_mem h, one_mul, sV, qStat_eq p S.C S.cs t x.1 0 ω']
        rfl
      have hSm : Measurable (fun ω' =>
          fro (∑ r ∈ Finset.range L, stationaryV p S.C S.cs t x.1 r ω') ^ 2) := by
        have he : (fun ω' => fro (∑ r ∈ Finset.range L, stationaryV p S.C S.cs t x.1 r ω') ^ 2) =
            (f x) ∘ qFut S.cs t := funext fun ω' => (hfx' ω').symm
        rw [he]
        exact (hfm x).comp hY
      simp_rw [hfx']
      simp only [g, Set.indicator_of_mem h]
      rw [hc]
      exact hc0 Ω P m n B S.C S.cs t x.1 S.size hB h hSm
    · have hfx' : ∀ ω', f x (qFut S.cs t ω') = 0 := by
        intro ω'
        simp only [f, Set.indicator_of_notMem h, zero_mul]
      simp_rw [hfx']
      simp [g, Set.indicator_of_notMem h]
  have hres := coupling_freeze_bound (dynPast S t) (buffer_past_le S t) (quad_X_meas S t) hY
    (quad_Y_indep S t) hf hf0 hgint hfx hbound
  have heq : {ω | dynDelta S t ω ∈ admA p S.C}.indicator (fun ω => fro (dynStatSum p S t ω) ^ 2) =
      fun ω => f (dynDelta S t ω, dynBuf S t ω) (qFut S.cs t ω) := by
    funext ω
    simp only [f, sV, qStat_eq p S.C S.cs t (dynDelta S t ω) 0 ω]
    by_cases h : dynDelta S t ω ∈ admA p S.C
    · rw [Set.indicator_of_mem (show ω ∈ {ω | dynDelta S t ω ∈ admA p S.C} from h),
        Set.indicator_of_mem h, one_mul]
      rfl
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | dynDelta S t ω ∈ admA p S.C} from h),
        Set.indicator_of_notMem h, zero_mul]
  rw [heq]
  refine ⟨hres.1, ?_⟩
  filter_upwards [hres.2] with ω hω
  refine hω.2.trans ?_
  by_cases h : dynDelta S t ω ∈ admA p S.C
  · simp only [g, Set.indicator_of_mem h, hc]
    exact le_of_eq (by ring)
  · simp only [g, Set.indicator_of_notMem h]
    positivity


/-- `𝔼_t‖∑_{r<L}(𝖲_{t+r} − V̂_r)‖_F² ≤ C L⁴` on `{Δ_t ∈ 𝒜}`, from `lem:app-dyn-coupling`(i). -/
private lemma quad_J_sq (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∃ B0 : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (m n B : ℕ) (S : DynSetup p P m n B), B0 ≤ B → 0 < B → ∀ t : ℕ,
      Integrable ({ω | dynDelta S t ω ∈ admA p S.C}.indicator
        (fun ω => fro (∑ r ∈ Finset.range (blockLen B), dynErrS p S t r ω) ^ 2)) P ∧
      ∀ᵐ ω ∂P, condExp (dynPast S t) P ({ω | dynDelta S t ω ∈ admA p S.C}.indicator
        (fun ω => fro (∑ r ∈ Finset.range (blockLen B), dynErrS p S t r ω) ^ 2)) ω ≤
          K * (blockLen B : ℝ) ^ 4 := by
  have hr0 := p.hr0
  have hr := p.hr
  obtain ⟨B0c, K1, hK1, hcoup⟩ := taylor_coupling certOp p (p.r0 / 2) (p.r1 + 1 / 2)
    (p.Estar + 1) (by linarith) (by linarith)
  refine ⟨B0c, K1, hK1, ?_⟩
  intro Ω _ P _ m n B S hB hB1 t
  set L := blockLen B with hLdef
  have hA : MeasurableSet[dynPast S t] {ω | dynDelta S t ω ∈ admA p S.C} :=
    coupling_A_meas S t (admBase p)
  have hAm : MeasurableSet {ω | dynDelta S t ω ∈ admA p S.C} := buffer_past_le S t _ hA
  have hk : ∀ r ∈ Finset.range L,
      Integrable ({ω | dynDelta S t ω ∈ admA p S.C}.indicator
        (fun ω => fro (dynErrS p S t r ω) ^ 2)) P ∧
      ∀ᵐ ω ∂P, condExp (dynPast S t) P ({ω | dynDelta S t ω ∈ admA p S.C}.indicator
        (fun ω => fro (dynErrS p S t r ω) ^ 2)) ω ≤ K1 * (r : ℝ) ^ 2 := by
    intro r hr'
    have hrL : r ≤ 4 * L := by
      have := Finset.mem_range.mp hr'
      omega
    exact (hcoup Ω P m n B S hB hB1 t r hrL).2.2.2.1
  have hXm : Measurable ({ω | dynDelta S t ω ∈ admA p S.C}.indicator
      (fun ω => fro (∑ r ∈ Finset.range L, dynErrS p S t r ω) ^ 2)) :=
    (buffer_fro_sq_meas.comp (Finset.measurable_sum _ fun r _ =>
      coupling_errS_meas S hB1 t r)).indicator hAm
  obtain ⟨hi, hc⟩ := taylor_cond_sum' (dynPast S t) (buffer_past_le S t) L 0 (fun _ => (L : ℝ))
    (fun _ _ => Nat.cast_nonneg _)
    (fun r => {ω | dynDelta S t ω ∈ admA p S.C}.indicator (fun ω => fro (dynErrS p S t r ω) ^ 2))
    (fun r hr' => (hk r hr').1) (fun r => K1 * (r : ℝ) ^ 2) (fun r hr' => (hk r hr').2)
    _ hXm.aestronglyMeasurable (fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω)
    (fun ω => by
      rw [zero_add, ← Finset.mul_sum]
      by_cases h : ω ∈ {ω | dynDelta S t ω ∈ admA p S.C}
      · simp only [Set.indicator_of_mem h]
        exact coupling_norm_finset_sum_sq fro coupling_fro_props.2.1 coupling_fro_props.2.2.1
          coupling_fro_props.2.2.2 L _
      · simp only [Set.indicator_of_notMem h, Finset.sum_const_zero, mul_zero, le_refl])
  refine ⟨hi, ?_⟩
  filter_upwards [hc] with ω hω
  refine hω.trans ?_
  rw [zero_add]
  calc ∑ r ∈ Finset.range L, (L : ℝ) * (K1 * (r : ℝ) ^ 2)
      ≤ ∑ r ∈ Finset.range L, (L : ℝ) * (K1 * (L : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun r hr' => ?_
        have : (r : ℝ) ≤ L := by exact_mod_cast (le_of_lt (Finset.mem_range.mp hr'))
        have h2 : (r : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hK1) (Nat.cast_nonneg _)
    _ = K1 * (L : ℝ) ^ 4 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

private lemma quad_frobIP_add_right {m n : ℕ} (X Y Z : Mat m n) :
    frobIP X (Y + Z) = frobIP X Y + frobIP X Z := by
  unfold frobIP
  rw [Matrix.transpose_add, Matrix.mul_add, Matrix.trace_add]

private lemma quad_arith_core (K2 Ks Kj Ke A1 A2 A3 A4 A5 A6 y1 y2 y3 y4 : ℝ) (hK2 : 0 ≤ K2)
    (hKs : 0 ≤ Ks) (hKj : 0 ≤ Kj) (hKe : 0 ≤ Ke) (t1 : 0 ≤ A1) (t2 : 0 ≤ A2) (t3 : 0 ≤ A3)
    (t4 : 0 ≤ A4) (t5 : 0 ≤ A5) (t6 : 0 ≤ A6)
    (q1 : 2 * K2 * y1 ≤ 2 * K2 * A1) (q2 : Ks * A4 * y2 ≤ Ks * A4)
    (q3 : Ke * y3 + Ke * y4 ≤ 2 * Ke * A1) :
    (2 * K2 * y1 + 2 * K2 * A2) + (Ks * A4 + Ks * A4 * y2 + Kj * A4) +
      (Ke * A6 + Ke * y3 + Ke * y4) ≤
      (2 * K2 + 2 * Ks + Kj + 2 * Ke) * (A1 + A2 + A3 + A4 + A5 + A6) := by
  have e : (2 * K2 + 2 * Ks + Kj + 2 * Ke) * (A1 + A2 + A3 + A4 + A5 + A6) =
      (2 * K2 * A1 + 2 * Ke * A1) + (2 * Ks + Kj) * A1 + 2 * K2 * A2 + (2 * Ks + Kj + 2 * Ke) * A2 +
        (2 * K2 + 2 * Ks + Kj + 2 * Ke) * A3 + (Ks * A4 + Ks * A4 + Kj * A4) +
        (2 * K2 + 2 * Ke) * A4 + (2 * K2 + 2 * Ks + Kj + 2 * Ke) * A5 + Ke * A6 +
        (2 * K2 + 2 * Ks + Kj + Ke) * A6 := by ring
  have v1 := mul_nonneg (show (0 : ℝ) ≤ 2 * Ks + Kj by linarith) t1
  have v2 := mul_nonneg (show (0 : ℝ) ≤ 2 * Ks + Kj + 2 * Ke by linarith) t2
  have v3 := mul_nonneg (show (0 : ℝ) ≤ 2 * K2 + 2 * Ks + Kj + 2 * Ke by linarith) t3
  have v4 := mul_nonneg (show (0 : ℝ) ≤ 2 * K2 + 2 * Ke by linarith) t4
  have v5 := mul_nonneg (show (0 : ℝ) ≤ 2 * K2 + 2 * Ks + Kj + 2 * Ke by linarith) t5
  have v6 := mul_nonneg (show (0 : ℝ) ≤ 2 * K2 + 2 * Ks + Kj + Ke by linarith) t6
  rw [e]
  linarith

private lemma quad_arith (K2 Ks Kj Ke L B sB x a m c1 c2 c3 : ℝ) (hK2 : 0 ≤ K2) (hKs : 0 ≤ Ks)
    (hKj : 0 ≤ Kj) (hKe : 0 ≤ Ke) (hL1 : 1 ≤ L) (hLB : L ≤ B) (hsB : 0 < sB) (hsB2 : sB ^ 2 = B)
    (hx : 0 < x) (hx2 : x ^ 2 = L ^ 3) (hm : 0 ≤ m) (ha : a = 1 + m / sB)
    (h1 : |c1| ≤ K2 * a * (B + L * sB))
    (h2 : |c2| ≤ x / sB / 2 * (Ks * (B * L + L ^ 2)) + 1 / (2 * (x / sB)) * (Kj * L ^ 4))
    (h3 : |c3| ≤ Ke * (L ^ 4 + B + m ^ 2)) :
    |2 * c1 + 2 * c2 + c3| / (L * B) ≤ (2 * K2 + 2 * Ks + Kj + 2 * Ke) *
      ((a + a ^ 2) / L + a / sB + L ^ 2 / B + x / sB + a * L / sB + L ^ 3 / B) := by
  subst hsB2
  have hL : 0 < L := by linarith
  have hB : 0 < sB ^ 2 := by positivity
  have hmsB : 0 ≤ m / sB := div_nonneg hm hsB.le
  have ha1 : 1 ≤ a := by rw [ha]; linarith
  have ha0 : 0 ≤ a := by linarith
  have hT : |2 * c1 + 2 * c2 + c3| ≤ 2 * |c1| + 2 * |c2| + |c3| := by
    have e1 := abs_add_le (2 * c1 + 2 * c2) c3
    have e2 := abs_add_le (2 * c1) (2 * c2)
    rw [abs_mul, abs_mul, abs_two] at e2
    linarith
  have hD0 : 0 < L * sB ^ 2 := by positivity
  rw [div_le_iff₀ hD0]
  have p1 : 2 * (K2 * a * (sB ^ 2 + L * sB)) =
      (2 * K2 * (a / L) + 2 * K2 * (a / sB)) * (L * sB ^ 2) := by
    field_simp
  have p2 : 2 * (x / sB / 2 * (Ks * (sB ^ 2 * L + L ^ 2)) + 1 / (2 * (x / sB)) * (Kj * L ^ 4)) =
      (Ks * (x / sB) + Ks * (x / sB) * (L / sB ^ 2) + Kj * (x / sB)) * (L * sB ^ 2) := by
    field_simp
    rw [← hx2]
    ring
  have p3 : Ke * (L ^ 4 + sB ^ 2 + m ^ 2) =
      (Ke * (L ^ 3 / sB ^ 2) + Ke * (1 / L) + Ke * ((m / sB) ^ 2 / L)) * (L * sB ^ 2) := by
    field_simp
  have hLsB : L / sB ^ 2 ≤ 1 := by rw [div_le_one hB]; exact hLB
  have hxs : 0 ≤ x / sB := div_nonneg hx.le hsB.le
  have hm2 : (m / sB) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hmsB (by rw [ha]; linarith) 2
  have t1 : 0 ≤ (a + a ^ 2) / L := div_nonneg (by positivity) hL.le
  have q1 : 2 * K2 * (a / L) ≤ 2 * K2 * ((a + a ^ 2) / L) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact div_le_div_of_nonneg_right (by nlinarith) hL.le
  have q2 : Ks * (x / sB) * (L / sB ^ 2) ≤ Ks * (x / sB) :=
    mul_le_of_le_one_right (mul_nonneg hKs hxs) hLsB
  have q3 : Ke * (1 / L) + Ke * ((m / sB) ^ 2 / L) ≤ 2 * Ke * ((a + a ^ 2) / L) := by
    have e : Ke * (1 / L) + Ke * ((m / sB) ^ 2 / L) = Ke * ((1 + (m / sB) ^ 2) / L) := by ring
    rw [e]
    have h5 : (1 + (m / sB) ^ 2) / L ≤ 2 * ((a + a ^ 2) / L) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by nlinarith) hL.le
    have := mul_le_mul_of_nonneg_left h5 hKe
    linarith
  have hXY := quad_arith_core K2 Ks Kj Ke ((a + a ^ 2) / L) (a / sB) (L ^ 2 / sB ^ 2) (x / sB)
    (a * L / sB) (L ^ 3 / sB ^ 2) (a / L) (L / sB ^ 2) (1 / L) ((m / sB) ^ 2 / L) hK2 hKs hKj hKe
    t1 (div_nonneg ha0 hsB.le) (div_nonneg (sq_nonneg _) hB.le) hxs
    (div_nonneg (mul_nonneg ha0 hL.le) hsB.le) (div_nonneg (by positivity) hB.le) q1 q2 q3
  have b1 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
  have b2 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2)
  rw [p1] at b1
  rw [p2] at b2
  rw [p3] at h3
  have hsum : 2 * |c1| + 2 * |c2| + |c3| ≤
      ((2 * K2 * (a / L) + 2 * K2 * (a / sB)) +
        (Ks * (x / sB) + Ks * (x / sB) * (L / sB ^ 2) + Kj * (x / sB)) +
        (Ke * (L ^ 3 / sB ^ 2) + Ke * (1 / L) + Ke * ((m / sB) ^ 2 / L))) * (L * sB ^ 2) := by
    rw [add_mul, add_mul]
    linarith
  calc |2 * c1 + 2 * c2 + c3| ≤ 2 * |c1| + 2 * |c2| + |c3| := hT
    _ ≤ _ := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_right hXY hD0.le


private lemma quad_abs_condExp {Ω : Type*} (F : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
    {P : Measure Ω} (f : Ω → ℝ) (hf : Integrable f P) :
    ∀ᵐ ω ∂P, |condExp F P f ω| ≤ condExp F P (fun ω => |f ω|) ω := by
  have h1 := condExp_mono (m := F) hf hf.abs (ae_of_all _ fun ω => le_abs_self (f ω))
  have h2 := condExp_mono (m := F) hf.neg hf.abs (ae_of_all _ fun ω => neg_le_abs (f ω))
  have h3 := condExp_neg (m := F) (μ := P) f
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  rw [abs_le]
  refine ⟨?_, e1⟩
  have e4 : condExp F P (-f) ω = -condExp F P f ω := by
    rw [e3]
    rfl
  linarith


/-! ## `lem:app-dyn-quadratic` -/

/-- `lem:app-dyn-quadratic`, snapshot `cr-2026-10-23`. The setting of `lem:app-dyn-coupling` with
`𝒦 = 𝒜` (`admA`): `S = ∑_{r<L}V_r`, `𝓔 = ∑_{r<L}𝖲_{t+r} − S`, `a = 1 + ‖M°_{t-1}‖_F/√B`, and `𝒲` a
selfadjoint linear map with `‖𝒲‖_{F→F} ≤ 1` (selfadjoint for `frobIP`). The constant `B₀`, `K` do not depend
on `𝒲`. The conditional expectation is written as the indicator form of `{Δ_t ∈ 𝒜}`. Statement verbatim
from `section.tex` (ll. 1995–2004):
```latex
\begin{lemma}[Quadratic block response]\label{lem:app-dyn-quadratic}
In the setting of \cref{lem:app-dyn-coupling} with $\mathcal K=\mathcal A$, let
$S=\sum_{r<L}V_r$, $\mathcal E=\sum_{r<L}{\mathsf S}_{t+r}-S$ and
$a\defeq1+\norm{M^\circ_{t-1}}_\F/\sqrt B$, and let $\mathcal W$ be selfadjoint with
$\norm{\mathcal W}_{\F\to\F}\le1$. On $\{\Dt\in\mathcal A\}$,
\[
\frac{1}{LB}\Big|\EE_t\big[2\langle S,\mathcal W\mathcal E\rangle+\langle\mathcal E,\mathcal W\mathcal E\rangle\big]\Big|
\le C\Big\{\frac{a+a^2}{L}+\frac{a}{\sqrt B}+\frac{L^2}{B}+\frac{L^{3/2}}{\sqrt B}+\frac{aL}{\sqrt B}+\frac{L^3}{B}\Big\}.
\]
\end{lemma}
```
-/
theorem lem_app_dyn_quadratic (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∃ B0 : ℕ, ∃ K : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B), B0 ≤ B → ∀ t : ℕ,
      ∀ (W : Mat m n →ₗ[ℝ] Mat m n), (∀ X Y : Mat m n, frobIP (W X) Y = frobIP X (W Y)) →
      (∀ X : Mat m n, fro (W X) ≤ fro X) →
      Integrable ({ω | dynDelta S t ω ∈ admA p S.C}.indicator
          (fun ω => 2 * frobIP (dynStatSum p S t ω) (W (dynSumErr p S t ω)) +
            frobIP (dynSumErr p S t ω) (W (dynSumErr p S t ω)))) P ∧
        ∀ᵐ ω ∂P, ω ∈ {ω | dynDelta S t ω ∈ admA p S.C} →
          |condExp (dynPast S t) P ({ω | dynDelta S t ω ∈ admA p S.C}.indicator
            (fun ω => 2 * frobIP (dynStatSum p S t ω) (W (dynSumErr p S t ω)) +
              frobIP (dynSumErr p S t ω) (W (dynSumErr p S t ω)))) ω| /
              ((blockLen B : ℝ) * B) ≤
            K * ((1 + fro (dynBuf S t ω) / Real.sqrt B + (1 + fro (dynBuf S t ω) / Real.sqrt B) ^ 2) /
                (blockLen B : ℝ) + (1 + fro (dynBuf S t ω) / Real.sqrt B) / Real.sqrt B +
                (blockLen B : ℝ) ^ 2 / B + (blockLen B : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt B +
                (1 + fro (dynBuf S t ω) / Real.sqrt B) * (blockLen B : ℝ) / Real.sqrt B +
                (blockLen B : ℝ) ^ 3 / B) := by
  have hr0 := p.hr0
  have hr := p.hr
  have hE := p.hE
  obtain ⟨K2, hK2, hAc⟩ := quad_cross_A certOp p
  obtain ⟨Ks, hKs, hSq⟩ := quad_S_sq p
  obtain ⟨B0j, Kj, hKj, hJ⟩ := quad_J_sq certOp p
  obtain ⟨B0e, Ke, hE3⟩ := lem_app_dyn_coupling_iii certOp p (p.r0 / 2) (p.r1 + 1 / 2)
    (p.Estar + 1) (by linarith) (by linarith)
  refine ⟨max (max B0j B0e) 1, 2 * K2 + 2 * Ks + Kj + 2 * max Ke 0, ?_⟩
  intro Ω _ P _ m n B S hB t W hWsa hW
  have hB1 : 0 < B := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hB)
  have hBj : B0j ≤ B := (le_max_left _ _).trans ((le_max_left _ _).trans hB)
  have hBe : B0e ≤ B := (le_max_right _ _).trans ((le_max_left _ _).trans hB)
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB1
  have hsB : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBr
  have hL1 : (1 : ℝ) ≤ (blockLen B : ℝ) := by exact_mod_cast quad_blockLen_pos hB1
  have hLB : (blockLen B : ℝ) ≤ B := quad_blockLen_le hB1
  have hAp : MeasurableSet[dynPast S t] {ω | dynDelta S t ω ∈ admA p S.C} :=
    coupling_A_meas S t (admBase p)
  have hAm : MeasurableSet {ω | dynDelta S t ω ∈ admA p S.C} := buffer_past_le S t _ hAp
  have hWm : Measurable W := by fun_prop
  -- measurability and bounds of the block sums
  have hSsm : Measurable (dynStatSum p S t) := by
    change Measurable (fun ω => ∑ r ∈ Finset.range (blockLen B),
      stationaryV p S.C S.cs t (dynDelta S t ω) r ω)
    exact Finset.measurable_sum _ fun r _ => coupling_statV_meas S t r
  have hJm : Measurable (fun ω => ∑ r ∈ Finset.range (blockLen B), dynErrS p S t r ω) :=
    Finset.measurable_sum _ fun r _ => coupling_errS_meas S hB1 t r
  have hEm : Measurable (dynSumErr p S t) := coupling_sumErr_meas S hB1 t
  have hg0 : 0 ≤ Real.sqrt (p.γstar * B) := Real.sqrt_nonneg _
  have hSsb : ∀ ω, fro (dynStatSum p S t ω) ≤ (blockLen B : ℝ) * Real.sqrt (p.γstar * B) :=
    fun ω => quad_sum_fro _ _ _ fun r => quad_Q_fro S _ (coupling_ridge_nonneg (p := p) S.C _) _
  have hSb1 : ∀ ω r, fro (dynErrS p S t r ω) ≤ 2 * Real.sqrt (p.γstar * B) := by
    intro ω r
    have h1 := (movement_update_bounds p S ω (t + r)).2
    have h2 := quad_Q_fro S _ (coupling_ridge_nonneg (p := p) S.C (dynDelta S t ω))
      (dynHatN p S t r ω)
    change fro (dynHatV p S t r ω) ≤ _ at h2
    have h3 := coupling_fro_sub_le (dynUpd S (t + r) ω) (dynHatV p S t r ω)
    change fro (dynErrS p S t r ω) ≤ _ at h3
    linarith
  have hVb1 : ∀ ω r, fro (dynErrV p S t r ω) ≤ 2 * Real.sqrt (p.γstar * B) := by
    intro ω r
    have h1 := quad_Q_fro S _ (coupling_ridge_nonneg (p := p) S.C (dynDelta S t ω))
      (dynHatN p S t r ω)
    change fro (dynHatV p S t r ω) ≤ _ at h1
    have h2 := quad_Q_fro S _ (coupling_ridge_nonneg (p := p) S.C (dynDelta S t ω))
      (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
        (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1))
    change fro (stationaryV p S.C S.cs t (dynDelta S t ω) r ω) ≤ _ at h2
    have h3 := coupling_fro_sub_le (dynHatV p S t r ω) (stationaryV p S.C S.cs t (dynDelta S t ω) r ω)
    change fro (dynErrV p S t r ω) ≤ _ at h3
    linarith
  have hJb : ∀ ω, fro (∑ r ∈ Finset.range (blockLen B), dynErrS p S t r ω) ≤
      (blockLen B : ℝ) * (2 * Real.sqrt (p.γstar * B)) :=
    fun ω => quad_sum_fro _ _ _ fun r => hSb1 ω r
  have hEsplit : ∀ ω, dynSumErr p S t ω = (∑ r ∈ Finset.range (blockLen B), dynErrS p S t r ω) +
      ∑ r ∈ Finset.range (blockLen B), dynErrV p S t r ω := by
    intro ω
    rw [coupling_sumErr_eq, Finset.sum_add_distrib]
  have hEb : ∀ ω, fro (dynSumErr p S t ω) ≤
      (blockLen B : ℝ) * (2 * Real.sqrt (p.γstar * B)) +
        (blockLen B : ℝ) * (2 * Real.sqrt (p.γstar * B)) := by
    intro ω
    rw [hEsplit]
    exact (coupling_fro_props.2.1 _ _).trans (add_le_add (hJb ω)
      (quad_sum_fro _ _ _ fun r => hVb1 ω r))
  -- the three terms
  set T1 : Ω → ℝ := {ω | dynDelta S t ω ∈ admA p S.C}.indicator (fun ω =>
    frobIP (dynStatSum p S t ω) (W (∑ r ∈ Finset.range (blockLen B), dynErrV p S t r ω)))
    with hT1def
  set T2 : Ω → ℝ := {ω | dynDelta S t ω ∈ admA p S.C}.indicator (fun ω =>
    frobIP (dynStatSum p S t ω) (W (∑ r ∈ Finset.range (blockLen B), dynErrS p S t r ω)))
    with hT2def
  set T3 : Ω → ℝ := {ω | dynDelta S t ω ∈ admA p S.C}.indicator (fun ω =>
    frobIP (dynSumErr p S t ω) (W (dynSumErr p S t ω))) with hT3def
  have hF : {ω | dynDelta S t ω ∈ admA p S.C}.indicator
      (fun ω => 2 * frobIP (dynStatSum p S t ω) (W (dynSumErr p S t ω)) +
        frobIP (dynSumErr p S t ω) (W (dynSumErr p S t ω))) = (2 : ℝ) • T1 + (2 : ℝ) • T2 + T3 := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hT1def, hT2def, hT3def]
    by_cases h : ω ∈ {ω | dynDelta S t ω ∈ admA p S.C}
    · simp only [Set.indicator_of_mem h]
      rw [hEsplit ω, map_add, quad_frobIP_add_right]
      ring
    · simp only [Set.indicator_of_notMem h]
      ring
  have hT1i : Integrable T1 P := (hAc Ω P m n B S t W hW).1
  have hT2m : Measurable T2 :=
    (startup_frobIP_cont.measurable.comp (hSsm.prodMk (hWm.comp hJm))).indicator hAm
  have hT3m : Measurable T3 :=
    (startup_frobIP_cont.measurable.comp (hEm.prodMk (hWm.comp hEm))).indicator hAm
  have hip : ∀ X Y : Mat m n, |frobIP X (W Y)| ≤ fro X * fro Y := fun X Y =>
    (startup_frobIP_le X (W Y)).trans (mul_le_mul_of_nonneg_left (hW Y) (movement_fro_nn X))
  have hind : ∀ (f : Ω → ℝ) (c : ℝ), 0 ≤ c → (∀ ω, |f ω| ≤ c) → ∀ ω,
      |{ω | dynDelta S t ω ∈ admA p S.C}.indicator f ω| ≤ c := by
    intro f c hc hfc ω
    by_cases h : ω ∈ {ω | dynDelta S t ω ∈ admA p S.C}
    · rw [Set.indicator_of_mem h]; exact hfc ω
    · rw [Set.indicator_of_notMem h, abs_zero]; exact hc
  have hT2i : Integrable T2 P := by
    refine Integrable.of_bound hT2m.aestronglyMeasurable
      (((blockLen B : ℝ) * Real.sqrt (p.γstar * B)) * ((blockLen B : ℝ) * (2 * Real.sqrt (p.γstar * B))))
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact hind _ _ (by positivity) (fun ω => (hip _ _).trans
      (mul_le_mul (hSsb ω) (hJb ω) (movement_fro_nn _) (by positivity))) ω
  have hT3i : Integrable T3 P := by
    refine Integrable.of_bound hT3m.aestronglyMeasurable
      (((blockLen B : ℝ) * (2 * Real.sqrt (p.γstar * B)) +
        (blockLen B : ℝ) * (2 * Real.sqrt (p.γstar * B))) ^ 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact hind _ _ (by positivity) (fun ω => (hip _ _).trans (by
      rw [← sq]; exact pow_le_pow_left₀ (movement_fro_nn _) (hEb ω) 2)) ω
  -- linearity of the conditional expectation
  have hlin : ∀ᵐ ω ∂P, condExp (dynPast S t) P ((2 : ℝ) • T1 + (2 : ℝ) • T2 + T3) ω =
      2 * condExp (dynPast S t) P T1 ω + 2 * condExp (dynPast S t) P T2 ω +
        condExp (dynPast S t) P T3 ω := by
    have ha := condExp_add (μ := P) ((hT1i.smul (2 : ℝ)).add (hT2i.smul (2 : ℝ))) hT3i (dynPast S t)
    have hb := condExp_add (μ := P) (hT1i.smul (2 : ℝ)) (hT2i.smul (2 : ℝ)) (dynPast S t)
    have hc := condExp_smul (μ := P) (2 : ℝ) T1 (dynPast S t)
    have hd := condExp_smul (μ := P) (2 : ℝ) T2 (dynPast S t)
    filter_upwards [ha, hb, hc, hd] with ω e1 e2 e3 e4
    rw [e1, Pi.add_apply, e2, Pi.add_apply, e3, e4]
    simp only [Pi.smul_apply, smul_eq_mul]
  -- the startup cross term
  have hc1 : ∀ᵐ ω ∂P, |condExp (dynPast S t) P T1 ω| ≤
      K2 * (1 + fro (dynBuf S t ω) / Real.sqrt B) * (B + (blockLen B : ℝ) * Real.sqrt B) :=
    (hAc Ω P m n B S t W hW).2
  -- the cross term with the update error, by the AM-GM inequality
  set x : ℝ := (blockLen B : ℝ) ^ ((3 : ℝ) / 2) with hxdef
  have hx : 0 < x := Real.rpow_pos_of_pos (by linarith) _
  have hx2 : x ^ 2 = (blockLen B : ℝ) ^ 3 := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  set cc : ℝ := x / Real.sqrt B with hccdef
  have hcc : 0 < cc := div_pos hx hsB
  obtain ⟨hSqi, hSqc⟩ := hSq Ω P m n B S hB1 t
  obtain ⟨hJi, hJc⟩ := hJ Ω P m n B S hBj hB1 t
  have hT2a : Measurable (fun ω => |T2 ω|) := hT2m.abs
  obtain ⟨hT2ai, hT2ac⟩ := taylor_cond2 (dynPast S t) (buffer_past_le S t) (cc / 2) (1 / (2 * cc))
    _ _ (by positivity) (by positivity) _ _ hSqi hJi hSqc hJc (fun ω => |T2 ω|)
    hT2a.aestronglyMeasurable (fun ω => abs_nonneg _)
    (fun ω => by
      by_cases h : ω ∈ {ω | dynDelta S t ω ∈ admA p S.C}
      · simp only [hT2def, Set.indicator_of_mem h]
        set u := fro (dynStatSum p S t ω)
        set v := fro (∑ r ∈ Finset.range (blockLen B), dynErrS p S t r ω)
        have h1 := hip (dynStatSum p S t ω) (∑ r ∈ Finset.range (blockLen B), dynErrS p S t r ω)
        have e : cc / 2 * u ^ 2 + 1 / (2 * cc) * v ^ 2 - u * v = (cc * u - v) ^ 2 / (2 * cc) := by
          field_simp
          ring
        have : 0 ≤ (cc * u - v) ^ 2 / (2 * cc) := by positivity
        linarith
      · simp [hT2def, Set.indicator_of_notMem h])
  have hc2 : ∀ᵐ ω ∂P, |condExp (dynPast S t) P T2 ω| ≤
      cc / 2 * (Ks * (B * blockLen B + (blockLen B : ℝ) ^ 2)) +
        1 / (2 * cc) * (Kj * (blockLen B : ℝ) ^ 4) := by
    filter_upwards [quad_abs_condExp (dynPast S t) T2 hT2i, hT2ac] with ω h1 h2
    exact h1.trans h2
  -- the quadratic term
  obtain ⟨hE2i, hE2c⟩ := hE3 Ω P m n B S hBe t
  have hT3abs : ∀ ω, |T3 ω| ≤ (dynInK S t (p.r0 / 2, p.r1 + 1 / 2, p.Estar + 1)).indicator
      (fun ω => fro (dynSumErr p S t ω) ^ 2) ω := by
    intro ω
    by_cases h : ω ∈ {ω | dynDelta S t ω ∈ admA p S.C}
    · have h' : ω ∈ dynInK S t (p.r0 / 2, p.r1 + 1 / 2, p.Estar + 1) := h
      simp only [hT3def, Set.indicator_of_mem h, Set.indicator_of_mem h']
      exact (hip _ _).trans (le_of_eq (sq _).symm)
    · have h' : ω ∉ dynInK S t (p.r0 / 2, p.r1 + 1 / 2, p.Estar + 1) := h
      rw [hT3def, Set.indicator_of_notMem h, Set.indicator_of_notMem h', abs_zero]
  have hc3m := condExp_mono (m := dynPast S t) hT3i.abs hE2i (ae_of_all _ hT3abs)
  -- assemble
  rw [hF]
  refine ⟨((hT1i.smul (2 : ℝ)).add (hT2i.smul (2 : ℝ))).add hT3i, ?_⟩
  filter_upwards [hlin, hc1, hc2, quad_abs_condExp (dynPast S t) T3 hT3i, hc3m, hE2c]
    with ω e0 e1 e2 e3 e4 e5 hω
  rw [e0]
  have hω' : ω ∈ dynInK S t (p.r0 / 2, p.r1 + 1 / 2, p.Estar + 1) := hω
  have e5' := e5 hω'
  have hKe : Ke * ((blockLen B : ℝ) ^ 4 + B + fro (dynBuf S t ω) ^ 2) ≤
      max Ke 0 * ((blockLen B : ℝ) ^ 4 + B + fro (dynBuf S t ω) ^ 2) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have h3 : |condExp (dynPast S t) P T3 ω| ≤
      max Ke 0 * ((blockLen B : ℝ) ^ 4 + B + fro (dynBuf S t ω) ^ 2) :=
    e3.trans (e4.trans (e5'.trans hKe))
  have h2 : |condExp (dynPast S t) P T2 ω| ≤
      x / Real.sqrt B / 2 * (Ks * (B * blockLen B + (blockLen B : ℝ) ^ 2)) +
        1 / (2 * (x / Real.sqrt B)) * (Kj * (blockLen B : ℝ) ^ 4) := e2
  exact quad_arith K2 Ks Kj (max Ke 0) (blockLen B) B (Real.sqrt B) x
    (1 + fro (dynBuf S t ω) / Real.sqrt B) (fro (dynBuf S t ω)) _ _ _ hK2 hKs hKj
    (le_max_right _ _) hL1 hLB hsB (Real.sq_sqrt hBr.le) hx hx2 (movement_fro_nn _) rfl
    e1 h2 h3

/-! ## Coordinator bridge: from `DynHyp` to `DynSetup` -/

/-! ### Private helpers for `DynHyp.exists_dynSetup` (P-E.9.P7) -/

/-- Pseudo-inverse `M⁺ = cfc (x ↦ x⁻¹) M` of a selfadjoint matrix. -/
private def exPinv {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  cfc (fun x : ℝ => x⁻¹) M

/-- Range projection `M⁺ M = cfc (x ↦ x⁻¹ x) M` of a selfadjoint matrix. -/
private def exProj {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  cfc (fun x : ℝ => x⁻¹ * x) M

private lemma ex_cont {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ M) :=
  (Matrix.finite_spectrum M).continuousOn f

private lemma ex_pinv_mul {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsSelfAdjoint M) :
    exPinv M * M = exProj M := by
  unfold exPinv exProj
  have h := cfc_mul (fun x : ℝ => x⁻¹) (fun x : ℝ => x) M (ex_cont M _) (ex_cont M _)
  rw [cfc_id' ℝ M] at h
  exact h.symm

private lemma ex_mul_pinv {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsSelfAdjoint M) :
    M * exPinv M = exProj M := by
  unfold exPinv exProj
  have h := cfc_mul (fun x : ℝ => x) (fun x : ℝ => x⁻¹) M (ex_cont M _) (ex_cont M _)
  rw [cfc_id' ℝ M] at h
  rw [← h]
  congr 1
  funext x
  ring

private lemma ex_mul_proj {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsSelfAdjoint M) :
    M * exProj M = M := by
  unfold exProj
  have h := cfc_mul (fun x : ℝ => x) (fun x : ℝ => x⁻¹ * x) M (ex_cont M _) (ex_cont M _)
  rw [cfc_id' ℝ M] at h
  rw [← h]
  conv_rhs => rw [← cfc_id' ℝ M]
  congr 1
  funext x
  by_cases hx : x = 0
  · simp [hx]
  · field_simp

private lemma ex_proj_mul {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsSelfAdjoint M) :
    exProj M * M = M := by
  unfold exProj
  have h := cfc_mul (fun x : ℝ => x⁻¹ * x) (fun x : ℝ => x) M (ex_cont M _) (ex_cont M _)
  rw [cfc_id' ℝ M] at h
  rw [← h]
  conv_rhs => rw [← cfc_id' ℝ M]
  congr 1
  funext x
  by_cases hx : x = 0
  · simp [hx]
  · field_simp

private lemma ex_proj_idem {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) :
    exProj M * exProj M = exProj M := by
  unfold exProj
  rw [← cfc_mul _ _ M (ex_cont M _) (ex_cont M _)]
  congr 1
  funext x
  by_cases hx : x = 0
  · simp [hx]
  · field_simp

private lemma ex_proj_symm {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) :
    (exProj M)ᵀ = exProj M := by
  have h : IsSelfAdjoint (exProj M) := cfc_predicate _ _
  have h2 := h.star_eq
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  exact h2

private lemma ex_rOut_sa {m n : ℕ} (C : Covariances m n) : IsSelfAdjoint (rOut C) := by
  unfold rOut
  exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)

private lemma ex_rIn_sa {m n : ℕ} (C : Covariances m n) : IsSelfAdjoint (rIn C) := by
  unfold rIn
  exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)


/-- Private copy (generalized to a `Fintype` index) of `rotE` of `Muon.Foundations.GaussianExtra`. -/
private def exRotE {ι : Type} [Fintype ι] [DecidableEq ι] (O : Matrix ι ι ℝ) (h1 : Oᵀ * O = 1)
    (h2 : O * Oᵀ = 1) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  LinearEquiv.isometryOfInner
    { toFun := fun x => WithLp.toLp 2 (O *ᵥ WithLp.ofLp x)
      invFun := fun x => WithLp.toLp 2 (Oᵀ *ᵥ WithLp.ofLp x)
      map_add' := by
        intro x y
        ext i
        simp [Matrix.mulVec_add]
      map_smul' := by
        intro c x
        ext i
        simp [Matrix.mulVec_smul]
      left_inv := by
        intro x
        ext i
        change (Oᵀ *ᵥ (O *ᵥ WithLp.ofLp x)) i = WithLp.ofLp x i
        rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
      right_inv := by
        intro x
        ext i
        change (O *ᵥ (Oᵀ *ᵥ WithLp.ofLp x)) i = WithLp.ofLp x i
        rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] }
    (by
      intro x y
      simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.star_mulVec,
        Matrix.conjTranspose_eq_transpose_of_trivial]
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one,
        dotProduct_comm])

/-- Rotation invariance of the coordinatewise standard Gaussian on a `Fintype` index (private copy of
`Muon.Foundations.stdGaussianPi_map_orthogonal`, generalized). -/
private lemma ex_pi_map_orth {ι : Type} [Fintype ι] [DecidableEq ι] (O : Matrix ι ι ℝ) (h1 : Oᵀ * O = 1)
    (h2 : O * Oᵀ = 1) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun z : ι → ℝ => O *ᵥ z)
      = Measure.pi fun _ : ι => gaussianReal 0 1 := by
  have hrot : Measurable (exRotE O h1 h2) := (exRotE O h1 h2).continuous.measurable
  have hf : Measurable (fun z : ι → ℝ => O *ᵥ z) := by fun_prop
  have he : Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding
  have hG := stdGaussian_map (exRotE O h1 h2)
  have hcomp : (WithLp.toLp 2 ∘ fun z : ι → ℝ => O *ᵥ z)
      = (exRotE O h1 h2) ∘ (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) := by
    funext z
    ext i
    simp [exRotE]
  have key : ((Measure.pi fun _ : ι => gaussianReal 0 1).map
      (fun z : ι → ℝ => O *ᵥ z)).map (WithLp.toLp 2)
      = (Measure.pi fun _ : ι => gaussianReal 0 1).map (WithLp.toLp 2) := by
    rw [Measure.map_map he hf, hcomp, ← Measure.map_map hrot he, map_pi_eq_stdGaussian, hG]
  exact hemb.map_injective key

/-- Gaussian splitting: for a symmetric idempotent `Π`, `Π g + (1 - Π) g'` is standard Gaussian when
`g, g'` are independent standard Gaussians. -/
private lemma ex_gauss_split {ι : Type} [Fintype ι] [DecidableEq ι] (Pm : Matrix ι ι ℝ)
    (hs : Pmᵀ = Pm) (hi : Pm * Pm = Pm) :
    ((Measure.pi fun _ : ι => gaussianReal 0 1).prod (Measure.pi fun _ : ι => gaussianReal 0 1)).map
      (fun p : (ι → ℝ) × (ι → ℝ) => Pm *ᵥ p.1 + (1 - Pm) *ᵥ p.2)
      = Measure.pi fun _ : ι => gaussianReal 0 1 := by
  set γ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1 with hγ
  set γ2 : Measure (ι ⊕ ι → ℝ) := Measure.pi fun _ : ι ⊕ ι => gaussianReal 0 1 with hγ2
  set O : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ := Matrix.fromBlocks Pm (1 - Pm) (1 - Pm) Pm with hO
  have e1 : Pm * (1 - Pm) = 0 := by rw [mul_sub, mul_one, hi, sub_self]
  have e2 : (1 - Pm) * Pm = 0 := by rw [sub_mul, one_mul, hi, sub_self]
  have e3 : (1 - Pm) * (1 - Pm) = 1 - Pm := by rw [sub_mul, one_mul, e1, sub_zero]
  have hOt : Oᵀ = O := by
    rw [hO, Matrix.fromBlocks_transpose, hs, Matrix.transpose_sub, Matrix.transpose_one, hs]
  have hOO : O * O = 1 := by
    rw [hO, Matrix.fromBlocks_multiply, e1, e2, e3, hi, ← Matrix.fromBlocks_one]
    congr 1 <;> abel
  have hsplit := measurePreserving_sumPiEquivProdPi (X := fun _ : ι ⊕ ι => ℝ)
    (fun _ : ι ⊕ ι => gaussianReal 0 1)
  have hmapγ : γ2.map (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => ℝ)) = γ.prod γ :=
    hsplit.map_eq
  have hF : Measurable (fun p : (ι → ℝ) × (ι → ℝ) => Pm *ᵥ p.1 + (1 - Pm) *ᵥ p.2) := by
    fun_prop
  have hcomp : (fun p : (ι → ℝ) × (ι → ℝ) => Pm *ᵥ p.1 + (1 - Pm) *ᵥ p.2) ∘
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => ℝ))
      = (fun v : ι ⊕ ι → ℝ => fun i => v (Sum.inl i)) ∘ (fun v => O *ᵥ v) := by
    funext v
    simp only [Function.comp_apply, hO, Matrix.fromBlocks_mulVec, Sum.elim_inl]
    rfl
  have hinl : Measurable (fun v : ι ⊕ ι → ℝ => fun i => v (Sum.inl i)) := by fun_prop
  have hOm : Measurable (fun v : ι ⊕ ι → ℝ => O *ᵥ v) := by fun_prop
  rw [← hmapγ, Measure.map_map hF (MeasurableEquiv.measurable _), hcomp,
    ← Measure.map_map hinl hOm, ex_pi_map_orth O (by rw [hOt, hOO]) (by rw [hOt, hOO])]
  have hfst : (fun v : ι ⊕ ι → ℝ => fun i => v (Sum.inl i))
      = Prod.fst ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => ℝ)) := rfl
  rw [hfst, ← Measure.map_map measurable_fst (MeasurableEquiv.measurable _), hmapγ,
    Measure.map_fst_prod, measure_univ, one_smul]


private lemma ex_merge {ι κ X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] :
    ((Measure.infinitePi fun _ : ι => μ).prod (Measure.infinitePi fun _ : κ => μ)).map
      (fun p : (ι → X) × (κ → X) => (Sum.elim p.1 p.2 : ι ⊕ κ → X))
      = Measure.infinitePi fun _ : ι ⊕ κ => μ := by
  have hm : Measurable (fun p : (ι → X) × (κ → X) => (Sum.elim p.1 p.2 : ι ⊕ κ → X)) := by
    rw [measurable_pi_iff]
    rintro (i | j)
    · exact (measurable_pi_apply i).comp measurable_fst
    · exact (measurable_pi_apply j).comp measurable_snd
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have hset : (fun p : (ι → X) × (κ → X) => (Sum.elim p.1 p.2 : ι ⊕ κ → X)) ⁻¹'
      (Set.pi (↑s) t) = Set.pi (↑s.toLeft) (fun i => t (Sum.inl i)) ×ˢ
        Set.pi (↑s.toRight) (fun j => t (Sum.inr j)) := by
    ext p
    simp [Set.mem_pi, Sum.forall]
  rw [hset, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht _),
    Measure.infinitePi_pi _ (fun i _ => ht _), Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]

private lemma ex_zip {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((Measure.infinitePi fun _ : ι => μ).prod (Measure.infinitePi fun _ : ι => ν)).map
      (fun p : (ι → X) × (ι → Y) => fun i => (p.1 i, p.2 i))
      = Measure.infinitePi fun _ : ι => μ.prod ν := by
  have hm : Measurable (fun p : (ι → X) × (ι → Y) => fun i => (p.1 i, p.2 i)) := by fun_prop
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have hz : Measurable (fun q : (s → X) × (s → Y) =>
      fun i => (q.1 i, q.2 i)) := by fun_prop
  have hS : MeasurableSet (Set.univ.pi fun i : s => t i) :=
    MeasurableSet.univ_pi fun i => ht _
  have hset : (fun p : (ι → X) × (ι → Y) => fun i => (p.1 i, p.2 i)) ⁻¹' (Set.pi (↑s) t)
      = Prod.map (Finset.restrict s) (Finset.restrict s) ⁻¹'
        ((fun q : (s → X) × (s → Y) => fun i => (q.1 i, q.2 i)) ⁻¹'
          Set.univ.pi fun i : s => t i) := by
    ext p
    simp [Set.mem_pi]
  have hPM : Measurable (Prod.map (Finset.restrict (π := fun _ : ι => X) s)
      (Finset.restrict (π := fun _ : ι => Y) s)) := by fun_prop
  rw [hset, ← Measure.map_apply hPM (hz hS), ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict,
    ← (measurePreserving_arrowProdEquivProdArrow X Y s (fun _ => μ) (fun _ => ν)).map_eq,
    MeasurableEquiv.map_apply]
  have hset2 : (MeasurableEquiv.arrowProdEquivProdArrow X Y s) ⁻¹'
      ((fun q : (s → X) × (s → Y) => fun i => (q.1 i, q.2 i)) ⁻¹'
          Set.univ.pi fun i : s => t i) = Set.univ.pi fun i : s => t i := by
    ext f
    simp [MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
  rw [hset2, Measure.pi_pi, Finset.prod_coe_sort s (fun i => (μ.prod ν) (t i))]


/-- The whitening map: `x ↦ Σ^{-1/2} x + (1 - Π) g` on each side. -/
private def exWh {m n : ℕ} (C : Covariances m n) (x g : Vec m × Vec n) : Vec m × Vec n :=
  (exPinv (rOut C) *ᵥ x.1 + (1 - exProj (rOut C)) *ᵥ g.1,
    exPinv (rIn C) *ᵥ x.2 + (1 - exProj (rIn C)) *ᵥ g.2)

/-- The range of `phys C`. -/
private def exRange {m n : ℕ} (C : Covariances m n) : Set (Vec m × Vec n) :=
  {x | exProj (rOut C) *ᵥ x.1 = x.1 ∧ exProj (rIn C) *ᵥ x.2 = x.2}

private lemma ex_phys_wh {m n : ℕ} (C : Covariances m n) (x g : Vec m × Vec n)
    (hx : x ∈ exRange C) : phys C (exWh C x g) = x := by
  obtain ⟨h1, h2⟩ := hx
  have o1 : rOut C * (1 - exProj (rOut C)) = 0 := by
    rw [mul_sub, mul_one, ex_mul_proj _ (ex_rOut_sa C), sub_self]
  have o2 : rIn C * (1 - exProj (rIn C)) = 0 := by
    rw [mul_sub, mul_one, ex_mul_proj _ (ex_rIn_sa C), sub_self]
  simp only [phys, exWh, Matrix.mulVec_add, Matrix.mulVec_mulVec, o1, o2, Matrix.zero_mulVec,
    add_zero, ex_mul_pinv _ (ex_rOut_sa C), ex_mul_pinv _ (ex_rIn_sa C), h1, h2]

private lemma ex_range_meas {m n : ℕ} (C : Covariances m n) : MeasurableSet (exRange C) := by
  have : IsClosed (exRange C) := by
    apply IsClosed.inter
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · exact isClosed_eq (by fun_prop) (by fun_prop)
  exact this.measurableSet

private lemma ex_phys_range {m n : ℕ} (C : Covariances m n) (z : Vec m × Vec n) :
    phys C z ∈ exRange C := by
  constructor
  · simp only [phys, Matrix.mulVec_mulVec, ex_proj_mul _ (ex_rOut_sa C)]
  · simp only [phys, Matrix.mulVec_mulVec, ex_proj_mul _ (ex_rIn_sa C)]

private lemma ex_phys_meas {m n : ℕ} (C : Covariances m n) : Measurable (phys C) := by
  unfold phys
  fun_prop

private lemma ex_range_ae {m n : ℕ} (C : Covariances m n) :
    ∀ᵐ x ∂(dataTarget C), x ∈ exRange C := by
  unfold dataTarget
  exact (ae_map_iff (p := fun x => x ∈ exRange C) (ex_phys_meas C).aemeasurable
    (ex_range_meas C)).2 (ae_of_all _ (ex_phys_range C))

private lemma ex_wh_meas {m n : ℕ} (C : Covariances m n) :
    Measurable (fun p : (Vec m × Vec n) × (Vec m × Vec n) => exWh C p.1 p.2) := by
  unfold exWh
  fun_prop

/-- Rearrangement of four factors. -/
private lemma ex_rearr {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasurePreserving (fun p : (α × β) × (α × β) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μ.prod ν).prod (μ.prod ν)) ((μ.prod μ).prod (ν.prod ν)) := by
  have r1 := measurePreserving_prodAssoc μ ν (μ.prod ν)
  have r2 := (MeasurePreserving.id μ).prod
    ((measurePreserving_prodAssoc ν μ ν).symm MeasurableEquiv.prodAssoc)
  have r3 := (MeasurePreserving.id μ).prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).prod (MeasurePreserving.id ν))
  have r4 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc μ ν ν)
  have r5 := (measurePreserving_prodAssoc μ μ (ν.prod ν)).symm MeasurableEquiv.prodAssoc
  have := r5.comp (r4.comp (r3.comp (r2.comp r1)))
  convert this using 1
  funext ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rfl

private lemma ex_wh_law {m n : ℕ} (C : Covariances m n) :
    ((dataTarget C).prod
        ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))).map
      (fun p : (Vec m × Vec n) × (Vec m × Vec n) => exWh C p.1 p.2)
      = (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n) := by
  set γm := Muon.Foundations.stdGaussianPi m
  set γn := Muon.Foundations.stdGaussianPi n
  have hFo := ex_gauss_split (exProj (rOut C)) (ex_proj_symm _) (ex_proj_idem _)
  have hFi := ex_gauss_split (exProj (rIn C)) (ex_proj_symm _) (ex_proj_idem _)
  have hD : dataTarget C = (γm.prod γn).map (phys C) := rfl
  rw [hD, ← Measure.map_id (μ := γm.prod γn),
    Measure.map_prod_map _ _ (ex_phys_meas C) measurable_id, Measure.map_id,
    Measure.map_map (ex_wh_meas C) ((ex_phys_meas C).prodMap measurable_id)]
  have hcomp : (fun p : (Vec m × Vec n) × (Vec m × Vec n) => exWh C p.1 p.2) ∘
      Prod.map (phys C) id
      = Prod.map (fun p : Vec m × Vec m => exProj (rOut C) *ᵥ p.1 + (1 - exProj (rOut C)) *ᵥ p.2)
          (fun p : Vec n × Vec n => exProj (rIn C) *ᵥ p.1 + (1 - exProj (rIn C)) *ᵥ p.2) ∘
        (fun p : (Vec m × Vec n) × (Vec m × Vec n) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) := by
    funext p
    simp only [Function.comp_apply, Prod.map, exWh, phys, id, Matrix.mulVec_mulVec,
      ex_pinv_mul _ (ex_rOut_sa C), ex_pinv_mul _ (ex_rIn_sa C)]
  rw [hcomp, ← Measure.map_map (by fun_prop) (ex_rearr γm γn).measurable, (ex_rearr γm γn).map_eq,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  unfold γm γn Muon.Foundations.stdGaussianPi
  rw [hFo, hFi]


/-- Merge of two product measures into one (measure-preserving form). -/
private lemma ex_merge_mp {ι κ X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] :
    MeasurePreserving (fun p : (ι → X) × (κ → X) => (Sum.elim p.1 p.2 : ι ⊕ κ → X))
      ((Measure.infinitePi fun _ : ι => μ).prod (Measure.infinitePi fun _ : κ => μ))
      (Measure.infinitePi fun _ : ι ⊕ κ => μ) := by
  refine ⟨?_, ex_merge μ⟩
  rw [measurable_pi_iff]
  rintro (i | j)
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

/-- The whitening of a product of data-target samples with an independent Gaussian family. -/
private lemma ex_W_mp {ι : Type*} {m n : ℕ} (C : Covariances m n)
    [IsProbabilityMeasure (dataTarget C)] :
    MeasurePreserving (fun p : (ι → Vec m × Vec n) × (ι → Vec m × Vec n) =>
        fun q => exWh C (p.1 q) (p.2 q))
      ((Measure.infinitePi fun _ : ι => dataTarget C).prod
        (Measure.infinitePi fun _ : ι =>
          (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)))
      (Measure.infinitePi fun _ : ι =>
          (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) := by
  have hw := ex_wh_meas C
  refine ⟨by fun_prop, ?_⟩
  have hcomp : (fun p : (ι → Vec m × Vec n) × (ι → Vec m × Vec n) =>
        fun q => exWh C (p.1 q) (p.2 q))
      = (fun z : ι → (Vec m × Vec n) × (Vec m × Vec n) => fun q => exWh C (z q).1 (z q).2) ∘
        (fun p : (ι → Vec m × Vec n) × (ι → Vec m × Vec n) => fun i => (p.1 i, p.2 i)) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), ex_zip,
    Measure.infinitePi_map_pi _ (fun _ => hw), ex_wh_law]

/-- The sample family on the extension: whitened actual samples on `inl`, fresh Gaussians on `inr`. -/
private def exR {Ω ι κ : Type*} {m n : ℕ} (C : Covariances m n)
    (X : ι → Ω → Vec m × Vec n) (ω' : Ω × ((ι → Vec m × Vec n) × (κ → Vec m × Vec n))) :
    ι ⊕ κ → Vec m × Vec n :=
  Sum.elim (fun q => exWh C (X q ω'.1) (ω'.2.1 q)) (fun i => ω'.2.2 i)

private lemma ex_R_meas {Ω ι κ : Type*} [MeasurableSpace Ω] {m n : ℕ} (C : Covariances m n)
    (X : ι → Ω → Vec m × Vec n) (hX : ∀ q, Measurable (X q)) (k : ι ⊕ κ) :
    Measurable (fun ω' : Ω × ((ι → Vec m × Vec n) × (κ → Vec m × Vec n)) => exR C X ω' k) := by
  rcases k with q | i
  · have hw := ex_wh_meas C
    have h1 : Measurable (fun ω' : Ω × ((ι → Vec m × Vec n) × (κ → Vec m × Vec n)) =>
        (X q ω'.1, ω'.2.1 q)) :=
      ((hX q).comp measurable_fst).prodMk
        ((measurable_pi_apply q).comp (measurable_fst.comp measurable_snd))
    exact hw.comp h1
  · exact (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)

/-- Core joint law on the extension. -/
private lemma ex_core {Ω ι κ M : Type*} [MeasurableSpace Ω] [MeasurableSpace M] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n : ℕ} (C : Covariances m n) [IsProbabilityMeasure (dataTarget C)]
    (Mm : Ω → M) (X : ι → Ω → Vec m × Vec n) (hMm : Measurable Mm) (hX : ∀ q, Measurable (X q))
    (hlaw : P.map (fun ω => (Mm ω, fun q => X q ω))
      = (P.map Mm).prod (Measure.infinitePi fun _ : ι => dataTarget C)) :
    MeasurePreserving
      (fun ω' : Ω × ((ι → Vec m × Vec n) × (κ → Vec m × Vec n)) => (Mm ω'.1, exR C X ω'))
      (P.prod ((Measure.infinitePi fun _ : ι =>
          (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)).prod
        (Measure.infinitePi fun _ : κ =>
          (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))))
      ((P.map Mm).prod (Measure.infinitePi fun _ : ι ⊕ κ =>
          (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))) := by
  set g0 := (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)
  set γA := Measure.infinitePi fun _ : ι => g0
  set γI := Measure.infinitePi fun _ : κ => g0
  set Lx := Measure.infinitePi fun _ : ι => dataTarget C
  set μM := P.map Mm
  have h0 : MeasurePreserving (fun ω => (Mm ω, fun q => X q ω)) P (μM.prod Lx) :=
    ⟨hMm.prodMk (measurable_pi_iff.2 hX), hlaw⟩
  have h1 := h0.prod (MeasurePreserving.id (γA.prod γI))
  have h2 := measurePreserving_prodAssoc μM Lx (γA.prod γI)
  have h3 := (MeasurePreserving.id μM).prod
    ((measurePreserving_prodAssoc Lx γA γI).symm MeasurableEquiv.prodAssoc)
  have h4 := (MeasurePreserving.id μM).prod
    ((ex_W_mp (ι := ι) C).prod (MeasurePreserving.id γI))
  have h5 := (MeasurePreserving.id μM).prod (ex_merge_mp (ι := ι) (κ := κ) g0)
  have := h5.comp (h4.comp (h3.comp (h2.comp h1)))
  convert this using 1
  funext ⟨ω, g, h⟩
  refine Prod.ext rfl ?_
  funext k
  rcases k with q | i <;> rfl


/-! ### The actual samples of `DynHyp`, made measurable -/

/-- Measurable version of the sample `a` of step `u` of `H` (index `q = (u, a)`). -/
private def exX {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ → ℕ}
    {C : ∀ k : ℕ, Covariances (m k) (n k)} (H : DynHyp p P m n B C) (k : ℕ)
    (q : ℕ × Fin (B k)) : Ω → Vec (m k) × Vec (n k) :=
  ((H.iid k q.1).meas q.2).mk _

/-- Measurable version of the initial buffer of `H`. -/
private def exM {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ → ℕ}
    {C : ∀ k : ℕ, Covariances (m k) (n k)} (H : DynHyp p P m n B C) (k : ℕ) :
    Ω → Mat (m k) (n k) :=
  (H.Mm1_meas k).mk _

private lemma ex_X_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)}
    (H : DynHyp p P m n B C) (k : ℕ) (q : ℕ × Fin (B k)) :
    Measurable (exX H k q) :=
  ((H.iid k q.1).meas q.2).measurable_mk

private lemma ex_X_ae {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)}
    (H : DynHyp p P m n B C) (k : ℕ) (q : ℕ × Fin (B k)) :
    (fun ω => H.x k q.1 ω q.2) =ᵐ[P] exX H k q :=
  ((H.iid k q.1).meas q.2).ae_eq_mk

private lemma ex_M_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)}
    (H : DynHyp p P m n B C) (k : ℕ) : Measurable (exM H k) :=
  (H.Mm1_meas k).measurable_mk

private lemma ex_X_law {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)}
    (H : DynHyp p P m n B C) (k : ℕ) (q : ℕ × Fin (B k)) :
    P.map (exX H k q) = dataTarget (C k) := by
  rw [← Measure.map_congr (ex_X_ae H k q)]
  exact (H.iid k q.1).law q.2

private lemma ex_X_indep {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)}
    (H : DynHyp p P m n B C) (k : ℕ) :
    iIndepFun (fun q : ℕ × Fin (B k) => exX H k q) P := by
  have h1 : iIndepFun (fun (u : ℕ) (ω : Ω) => fun a : Fin (B k) => exX H k (u, a) ω) P := by
    refine (H.steps_indep k).congr (fun u => ?_)
    filter_upwards [ae_all_iff.2 (fun a : Fin (B k) => ex_X_ae H k (u, a))] with ω hω
    funext a
    exact hω a
  have h2 : ∀ u, iIndepFun (fun a : Fin (B k) => exX H k (u, a)) P :=
    fun u => (H.iid k u).indep.congr (fun a => ex_X_ae H k (u, a))
  exact iIndepFun_uncurry' (X := fun u a => exX H k (u, a)) (fun u a => ex_X_meas H k _) h1 h2

private lemma ex_Y_law {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)}
    (H : DynHyp p P m n B C) (k : ℕ) [IsProbabilityMeasure (dataTarget (C k))] :
    P.map (fun ω (q : ℕ × Fin (B k)) => exX H k q ω)
      = Measure.infinitePi fun _ : ℕ × Fin (B k) => dataTarget (C k) := by
  rw [(ex_X_indep H k).map_fun_eq_infinitePi_map (ex_X_meas H k)]
  congr 1
  funext q
  exact ex_X_law H k q

private lemma ex_MY_indep {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)}
    (H : DynHyp p P m n B C) (k : ℕ) :
    IndepFun (exM H k) (fun ω (q : ℕ × Fin (B k)) => exX H k q ω) P := by
  have h := (H.Mm1_indep k).comp (φ := id)
    (ψ := fun (b : ℕ → Batch (m k) (n k) (B k)) (q : ℕ × Fin (B k)) => b q.1 q.2)
    measurable_id (by fun_prop)
  refine h.congr (H.Mm1_meas k).ae_eq_mk ?_
  filter_upwards [ae_all_iff.2 (fun q : ℕ × Fin (B k) => ex_X_ae H k q)] with ω hω
  funext q
  exact hω q

private lemma ex_hyp_law {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)}
    (H : DynHyp p P m n B C) (k : ℕ)
    [IsProbabilityMeasure (dataTarget (C k))] :
    P.map (fun ω => (exM H k ω, fun q : ℕ × Fin (B k) => exX H k q ω))
      = (P.map (exM H k)).prod (Measure.infinitePi fun _ : ℕ × Fin (B k) => dataTarget (C k)) := by
  have := (H.steps_indep k).isProbabilityMeasure
  rw [(indepFun_iff_map_prod_eq_prod_map_map (ex_M_meas H k).aemeasurable
    (measurable_pi_iff.2 (fun q => ex_X_meas H k q)).aemeasurable).1 (ex_MY_indep H k),
    ex_Y_law H k]


/-- Index map of the sample family: actual batches `s ≥ 1` go to the whitened samples of step
`s - 1`, everything else to a fresh Gaussian coordinate. -/
private def exE {B : ℕ} :
    (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B) → (ℕ × Fin B) ⊕ ((ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B))
  | Sum.inl sa => if 1 ≤ sa.1 then Sum.inl ((sa.1 - 1).toNat, sa.2) else Sum.inr (Sum.inl sa)
  | Sum.inr q => Sum.inr (Sum.inr q)

private lemma exE_inj {B : ℕ} : Function.Injective (exE (B := B)) := by
  rintro (⟨s, a⟩ | q) (⟨s', a'⟩ | q') h
  · simp only [exE] at h
    split_ifs at h with h1 h2 h2 <;>
      simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq] at h
    · obtain ⟨h3, rfl⟩ := h
      rw [show s = s' by omega]
    · obtain ⟨rfl, rfl⟩ := h
      rfl
  · simp only [exE] at h
    split_ifs at h
    simp at h
  · simp only [exE] at h
    split_ifs at h
    simp at h
  · simp only [exE, Sum.inr.injEq] at h
    rw [h]

private lemma exE_act {B : ℕ} (u : ℕ) (a : Fin B) :
    exE (Sum.inl ((u : ℤ) + 1, a)) = Sum.inl (u, a) := by
  simp [exE]


/-- Coordinator bridge (no source label), linking the law-level `DynHyp` of `thm:app-dyn-main` (used by
L-E.2, L-E.4 and L-E.13) to the sample-level `DynSetup` of this module. Snapshot `cr-2026-10-23`. For each
dimension `k` of `H` there is an extension probability space `(Ω', P')` with a measure-preserving
projection `pi : Ω' → Ω` onto `(Ω, P)`, carrying a `DynSetup` whose covariances, algorithm, initial
parameter and initial buffer agree with those of `H` (the initial buffer is the almost-everywhere
measurable representative of `H.Mm1 k`), and whose actual batches agree almost surely with the batches
`H.x k u` pulled back by `pi`. The extension carries the whitened and auxiliary batches of `ChainSamples`. -/
theorem DynHyp.exists_dynSetup {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams}
    {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)} (H : DynHyp p P m n B C) (k : ℕ) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (P' : Measure Ω') (pi : Ω' → Ω)
      (S : DynSetup p P' (m k) (n k) (B k)),
      MeasurePreserving pi P' P ∧ S.C = C k ∧ S.alg = H.alg k ∧ S.W0 = H.W0 k ∧
      S.M0 =ᵐ[P'] (H.Mm1 k ∘ pi) ∧ ∀ u : ℕ, dynBatch S u =ᵐ[P'] (H.x k u ∘ pi) := by
  have hP : IsProbabilityMeasure P := (H.steps_indep k).isProbabilityMeasure
  have hD : IsProbabilityMeasure (dataTarget (C k)) := by
    unfold dataTarget
    infer_instance
  set g0 := (Muon.Foundations.stdGaussianPi (m k)).prod (Muon.Foundations.stdGaussianPi (n k))
    with hg0
  set γA := Measure.infinitePi fun _ : ℕ × Fin (B k) => g0 with hγA
  set γI := Measure.infinitePi fun _ : (ℤ × Fin (B k)) ⊕ (ℤ × ℕ × Fin (B k)) => g0 with hγI
  set P' := P.prod (γA.prod γI) with hP'
  have hfst : MeasurePreserving
      (Prod.fst : Ω × ((ℕ × Fin (B k) → Vec (m k) × Vec (n k)) ×
        ((ℤ × Fin (B k)) ⊕ (ℤ × ℕ × Fin (B k)) → Vec (m k) × Vec (n k))) → Ω) P' P :=
    measurePreserving_fst
  have hcore := ex_core (κ := (ℤ × Fin (B k)) ⊕ (ℤ × ℕ × Fin (B k))) (C k) (exM H k) (exX H k)
    (ex_M_meas H k) (ex_X_meas H k) (ex_hyp_law H k)
  have hRm := ex_R_meas (κ := (ℤ × Fin (B k)) ⊕ (ℤ × ℕ × Fin (B k))) (C k) (exX H k)
    (ex_X_meas H k)
  have hRall : Measurable (fun ω' : Ω × ((ℕ × Fin (B k) → Vec (m k) × Vec (n k)) ×
        ((ℤ × Fin (B k)) ⊕ (ℤ × ℕ × Fin (B k)) → Vec (m k) × Vec (n k))) =>
      exR (C k) (exX H k) ω') := measurable_pi_iff.2 hRm
  have hRlaw : P'.map (fun ω' => exR (C k) (exX H k) ω')
      = Measure.infinitePi fun _ : (ℕ × Fin (B k)) ⊕ ((ℤ × Fin (B k)) ⊕ (ℤ × ℕ × Fin (B k))) =>
        g0 := by
    have e : (fun ω' : Ω × ((ℕ × Fin (B k) → Vec (m k) × Vec (n k)) ×
        ((ℤ × Fin (B k)) ⊕ (ℤ × ℕ × Fin (B k)) → Vec (m k) × Vec (n k))) =>
          exR (C k) (exX H k) ω')
        = Prod.snd ∘ (fun ω' => (exM H k ω'.1, exR (C k) (exX H k) ω')) := rfl
    rw [e, ← Measure.map_map measurable_snd hcore.measurable, hcore.map_eq,
      Measure.map_snd_prod, measure_univ, one_smul]
  have hMlaw : P'.map (fun ω' => exM H k ω'.1) = P.map (exM H k) := by
    have e : (fun ω' : Ω × ((ℕ × Fin (B k) → Vec (m k) × Vec (n k)) ×
        ((ℤ × Fin (B k)) ⊕ (ℤ × ℕ × Fin (B k)) → Vec (m k) × Vec (n k))) => exM H k ω'.1)
        = exM H k ∘ Prod.fst := rfl
    rw [e, ← Measure.map_map (ex_M_meas H k) measurable_fst, hfst.map_eq]
  have hRmarg : ∀ j, P'.map (fun ω' => exR (C k) (exX H k) ω' j) = g0 := by
    intro j
    have e : (fun ω' : Ω × ((ℕ × Fin (B k) → Vec (m k) × Vec (n k)) ×
        ((ℤ × Fin (B k)) ⊕ (ℤ × ℕ × Fin (B k)) → Vec (m k) × Vec (n k))) =>
          exR (C k) (exX H k) ω' j)
        = (fun f => f j) ∘ (fun ω' => exR (C k) (exX H k) ω') := rfl
    rw [e, ← Measure.map_map (measurable_pi_apply j) hRall, hRlaw, Measure.infinitePi_map_eval]
  have hRind : iIndepFun (fun j ω' => exR (C k) (exX H k) ω' j) P' := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map hRm]
    simp only [hRmarg]
    exact hRlaw
  have hMR : IndepFun (fun ω' : Ω × ((ℕ × Fin (B k) → Vec (m k) × Vec (n k)) ×
        ((ℤ × Fin (B k)) ⊕ (ℤ × ℕ × Fin (B k)) → Vec (m k) × Vec (n k))) => exM H k ω'.1)
      (fun ω' => exR (C k) (exX H k) ω') P' := by
    refine (indepFun_iff_map_prod_eq_prod_map_map (μ := P') (f := fun ω' => exM H k ω'.1)
      ((ex_M_meas H k).comp measurable_fst).aemeasurable hRall.aemeasurable).2 ?_
    rw [hcore.map_eq, hRlaw, hMlaw]
  have hle : ∀ i : (ℤ × Fin (B k)) ⊕ (ℤ × ℕ × Fin (B k)),
      MeasurableSpace.comap (fun ω' : Ω × ((ℕ × Fin (B k) → Vec (m k) × Vec (n k)) ×
        ((ℤ × Fin (B k)) ⊕ (ℤ × ℕ × Fin (B k)) → Vec (m k) × Vec (n k))) =>
          exR (C k) (exX H k) ω' (exE i)) inferInstance
        ≤ MeasurableSpace.comap (fun ω' => exR (C k) (exX H k) ω') inferInstance := by
    intro i
    have e : (fun ω' : Ω × ((ℕ × Fin (B k) → Vec (m k) × Vec (n k)) ×
        ((ℤ × Fin (B k)) ⊕ (ℤ × ℕ × Fin (B k)) → Vec (m k) × Vec (n k))) =>
          exR (C k) (exX H k) ω' (exE i))
        = (fun f => f (exE i)) ∘ (fun ω' => exR (C k) (exX H k) ω') := rfl
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  have hfrob : Measurable (fun M : Mat (m k) (n k) => ENNReal.ofReal (fro M ^ 2)) := by
    unfold fro
    fun_prop
  let cs : ChainSamples P' (m k) (n k) (B k) :=
    { act := fun s a ω' => exR (C k) (exX H k) ω' (exE (Sum.inl (s, a)))
      aux := fun t j a ω' => exR (C k) (exX H k) ω' (exE (Sum.inr (t, j, a)))
      meas_act := fun s a => hRm _
      meas_aux := fun t j a => hRm _
      law_act := fun s a => hRmarg _
      law_aux := fun t j a => hRmarg _
      indep := by
        have hfam : (fun i : (ℤ × Fin (B k)) ⊕ (ℤ × ℕ × Fin (B k)) =>
            (Sum.elim (fun q : ℤ × Fin (B k) =>
                fun ω' => exR (C k) (exX H k) ω' (exE (Sum.inl (q.1, q.2))))
              (fun q : ℤ × ℕ × Fin (B k) =>
                fun ω' => exR (C k) (exX H k) ω' (exE (Sum.inr (q.1, q.2.1, q.2.2)))) i :
              Ω × ((ℕ × Fin (B k) → Vec (m k) × Vec (n k)) ×
                ((ℤ × Fin (B k)) ⊕ (ℤ × ℕ × Fin (B k)) → Vec (m k) × Vec (n k))) →
                  Vec (m k) × Vec (n k)))
            = fun i ω' => exR (C k) (exX H k) ω' (exE i) := by
          funext i
          rcases i with ⟨s, a⟩ | ⟨t, j, a⟩ <;> rfl
        rw [hfam]
        exact hRind.precomp exE_inj }
  refine ⟨_, inferInstance, P', Prod.fst,
    { C := C k
      alg := H.alg k
      cs := cs
      W0 := H.W0 k
      M0 := fun ω' => exM H k ω'.1
      size := ⟨H.dims k, (H.normBd k).2, (H.normBd k).1⟩
      alg_β := H.alg_β k
      alg_ϱ := H.alg_ϱ k
      alg_η := H.alg_η k
      W0_norm := H.W0_norm k
      W0_risk := H.W0_risk k
      M0_meas := (ex_M_meas H k).comp measurable_fst
      M0_indep := by
        refine indep_of_indep_of_le_right ((IndepFun_iff_Indep _ _ _).1 hMR) ?_
        refine sup_le (iSup_le fun s => iSup_le fun _ => iSup_le fun a => ?_)
          (iSup_le fun t => iSup_le fun j => iSup_le fun a => ?_)
        · exact hle (Sum.inl (s, a))
        · exact hle (Sum.inr (t, j, a))
      M0_bound := by
        refine le_of_eq_of_le ((hfst.lintegral_comp (hfrob.comp (ex_M_meas H k))).trans
          (lintegral_congr_ae ?_)) (H.Mm1_bound k)
        filter_upwards [(H.Mm1_meas k).ae_eq_mk] with ω hω
        show ENNReal.ofReal (fro (exM H k ω) ^ 2) = ENNReal.ofReal (fro (H.Mm1 k ω) ^ 2)
        rw [exM, ← hω] },
    hfst, rfl, rfl, rfl, ?_, ?_⟩
  · exact hfst.quasiMeasurePreserving.ae_eq_comp (H.Mm1_meas k).ae_eq_mk.symm
  · intro u
    have hgood : ∀ᵐ ω ∂P, ∀ a : Fin (B k),
        exX H k (u, a) ω ∈ exRange (C k) ∧ exX H k (u, a) ω = H.x k u ω a := by
      rw [ae_all_iff]
      intro a
      have h1 : ∀ᵐ ω ∂P, exX H k (u, a) ω ∈ exRange (C k) := by
        have := ex_range_ae (C k)
        rw [← ex_X_law H k (u, a)] at this
        exact (ae_map_iff (p := fun x => x ∈ exRange (C k)) (ex_X_meas H k _).aemeasurable
          (ex_range_meas _)).1 this
      filter_upwards [h1, ex_X_ae H k (u, a)] with ω h1 h2
      exact ⟨h1, h2.symm⟩
    filter_upwards [hfst.quasiMeasurePreserving.ae hgood] with ω' h
    funext a
    show phys (C k) (exR (C k) (exX H k) ω' (exE (Sum.inl ((u : ℤ) + 1, a)))) = H.x k u ω'.1 a
    rw [exE_act]
    exact (ex_phys_wh (C k) _ _ (h a).1).trans (h a).2

end Muon.Dynamics

end

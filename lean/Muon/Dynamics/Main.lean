import Muon.Dynamics.Block
import Muon.Dynamics.Closure

/-!
# Appendix E, work package L-E.13: the main theorem and the no-exit lemma

Snapshot `cr-2026-10-23`. Source: `sections/05-dynamics/section.tex`, `thm:app-dyn-main` (ll. 336–367) and
`lem:app-dyn-interval` (ll. 2286–2296). Card: `sections/05-dynamics/CARD.md` §2, §3, §6 and the L-E.13 row of §5.
Interface only: every proof is `sorry`.

Framework. Everything is in the law-level `DynHyp` of `Muon.Dynamics.Corollaries`/`Basic` (one probability space
`P`, dimensions `k`), with `errPath`, `dev0`, `actMeas`, `IsActualCoeff`, exactly as in `Muon.Dynamics.Block`. The
block exit index is `blockExitIdx` of `Block` (the `DynHyp` form of `b_c` of `lem:app-dyn-diffuse`). The source's
standing "along a sequence of dimensions with `B → ∞`" is the explicit hypothesis `hB`, carried by every part.

Representation choices (also in the result JSON `open_questions`):
* Certificates. Each part routes through `lem_app_dyn_block` (`lem:app-dyn-interval`, and through it every part of
  `thm:app-dyn-main`), which takes four certificates. Every declaration here takes the same four, and `hc` for the
  actual coefficients. Gronwall (teschl2012ordinary, Lemma 2.7) is not a certificate: it is proved in the proof card.
* Stopping. `t_stop` is `Muon.Setup.tstopRand` along the initial state `(W_0, M°_{-1})` of `hyp` (the same
  initial state as `errPath`). The event "`t_stop > BT⋆`" is written `∀ t ∈ ℕ, t ≤ BT⋆ → t < t_stop`, equivalent for
  `ℕ∞`-valued `t_stop`. `t_{b_c} ≤ BT⋆ + L` is `L · b_c ≤ ⌊BT⋆ + L⌋₊` in `ℕ∞` (a finite integer `t` is `≤ x`
  iff `t ≤ ⌊x⌋₊`; `⊤` is never `≤`).
* Probability. "In probability" is `∀ ε > 0, P {ε < sup …} → 0` with the supremum in `ℝ≥0∞`
  (`⨆ τ ∈ Icc 0 T, ENNReal.ofReal …`), as in `lem_app_dyn_block`. "With probability tending to one" is `P E → 1`.
* The ODE solution is an argument `e` with `def_app_dyn_ode` (existence and uniqueness are `prop_app_dyn_ode`); the
  statement quantifies over all solutions, which is equivalent since the source's solution is unique.
* The weighted BL norm `‖μλ m‖_BL` is `blDistLam` (new helper: `blNorm` of `φ ↦ ∫ μλ φ dμ − ∫ μλ φ dν`).
  `fRisk(τ)` is `odeRisk` (the source's `½ ∑ μ_i λ_j 𝔔_ij(τ)`, which equals `riskOf` of `odeMeasure`).
* `𝔐 = admMeasures p` (`Adm`), `χ^act(τ) = actMeas`, `χ^ode(τ) = odeMeasure (B k) μ λ (e k τ)`.
* (iv): "on the event of (i)" is the indicator form `P (mainEvent ∩ {sup > ε}) → 0` (card F5).
  `‖Â_t‖` is `opNorm (normState _ _)`, the diffuseness `δ(Δ_t)` of `Basic.diffuseness`.
* Integrability of the test integrals against the (atomic, finite) actual and ODE measures is a conclusion conjunct.
-/

set_option linter.style.longLine false

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open Muon Muon.Setup

noncomputable section

namespace Muon.Dynamics

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams}
  {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)}

/-! ## Helpers -/

/-- The stopping time `t_stop` of the actual algorithm at dimension `k` (`def:app-setup-algorithm`), run from the
initial state `(W₀, M°₋₁)` of `hyp`, the same initial state as `errPath`. Snapshot `cr-2026-10-23`. -/
def stopTime (hyp : DynHyp p P m n B C) (k : ℕ) : Ω → ℕ∞ :=
  tstopRand (C k) (hyp.alg k) (fun ω => initState (hyp.W0 k) (hyp.Mm1 k ω)) (hyp.x k)

/-- The bounded-Lipschitz norm of the measures weighted by `μλ`, `‖μλ (m − ν)‖_BL`: `blNorm` of
`φ ↦ ∫ μλ φ dμ − ∫ μλ φ dν` (`thm:app-dyn-main`(iii)). Snapshot `cr-2026-10-23`. -/
def blDistLam (Cs : ℝ) (μ ν : Measure (ℝ × ℝ)) : ℝ :=
  blNorm Cs (fun φ => ∫ x, x.1 * x.2 * φ x ∂μ - ∫ x, x.1 * x.2 * φ x ∂ν)

/-- The event of `thm:app-dyn-main`(i) at dimension `k`: for every integer `t ≤ BT⋆`, `t < t_stop`,
`𝓡(Δ_t) ≥ r₀/2` and `‖Δ_t‖_F² ≤ E⋆+1`. Snapshot `cr-2026-10-23`. -/
def mainEvent (hyp : DynHyp p P m n B C) (k : ℕ) : Set Ω :=
  {ω | ∀ t : ℕ, (t : ℝ) ≤ (B k : ℝ) * Tstar p →
    (t : ℕ∞) < stopTime hyp k ω ∧ p.r0 / 2 ≤ riskSigma (C k) (errPath hyp k t ω) ∧
      fro (errPath hyp k t ω) ^ 2 ≤ p.Estar + 1}

/-- The event of `lem:app-dyn-interval`(ii) at dimension `k`: for every integer `t ≤ BT⋆`,
`|‖Δ_t‖_F² − ‖Δ_0‖_F²| ≤ ¼` and `|𝓡(Δ_t) − 𝓡(Δ_0)| ≤ min(r₀,1)/4`. Snapshot `cr-2026-10-23`. -/
def boundEvent (hyp : DynHyp p P m n B C) (k : ℕ) : Set Ω :=
  {ω | ∀ t : ℕ, (t : ℝ) ≤ (B k : ℝ) * Tstar p →
    |fro (errPath hyp k t ω) ^ 2 - fro (dev0 hyp k) ^ 2| ≤ 1 / 4 ∧
      |riskSigma (C k) (errPath hyp k t ω) - riskSigma (C k) (dev0 hyp k)| ≤ min p.r0 1 / 4}

private lemma prob_of_dynHyp (hyp : DynHyp p P m n B C) : IsProbabilityMeasure P := by
  have hev : ∀ᶠ k in atTop, 1 ≤ B k := hyp.regime.B_top.eventually (eventually_ge_atTop 1)
  obtain ⟨k, hk⟩ := hev.exists
  let a : Fin (B k) := ⟨0, hk⟩
  refine IsProbabilityMeasure.mk ?_
  have hlaw := (hyp.iid k 0).law a
  have hm := Measure.map_apply_of_aemeasurable ((hyp.iid k 0).meas a) MeasurableSet.univ
  rw [hlaw] at hm
  haveI : IsProbabilityMeasure (dataTarget (C k)) := by unfold dataTarget; infer_instance
  simpa only [Set.preimage_univ, IsProbabilityMeasure.measure_univ] using hm.symm

private lemma tendsto_measure_one_of_subset {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (A D : ℕ → Set Ω)
    (hA : Tendsto (fun k => P (A k)) atTop (𝓝 1)) (hsub : ∀ k, A k ⊆ D k) :
    Tendsto (fun k => P (D k)) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hA tendsto_const_nhds
  · exact Filter.Eventually.of_forall fun k => measure_mono (hsub k)
  · exact Filter.Eventually.of_forall fun k => by
      have h : P (D k) ≤ P Set.univ := measure_mono (subset_univ (D k))
      simpa only [IsProbabilityMeasure.measure_univ] using h

private lemma boundEvent_stop (hyp : DynHyp p P m n B C) (k : ℕ) :
    boundEvent hyp k ⊆
      {ω | ∀ t : ℕ, (t : ℝ) ≤ (B k : ℝ) * Tstar p → (t : ℕ∞) < stopTime hyp k ω} := by
  intro ω hω t ht
  have hbd := (hω t ht).2
  have hR0 := (hyp.W0_risk k).1
  change p.r0 ≤ riskSigma (C k) (dev0 hyp k) at hR0
  have hmin : min p.r0 1 ≤ p.r0 := min_le_left _ _
  have hdiff : - (min p.r0 1 / 4) ≤
      riskSigma (C k) (errPath hyp k t ω) - riskSigma (C k) (dev0 hyp k) :=
    neg_le_of_abs_le hbd
  have hminpos : 0 < min p.r0 1 := lt_min p.hr0 zero_lt_one
  have hpos : 0 < riskSigma (C k) (errPath hyp k t ω) := by
    nlinarith
  apply lt_of_not_ge
  intro hstop
  have hz := (update_eq_zero_iff (C k) (hyp.alg k)
    (initState (hyp.W0 k) (hyp.Mm1 k ω)) (fun u => hyp.x k u ω) t).mp hstop
  exact hpos.ne' hz

private lemma atom_integral {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (q : Fin m → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j) (φ : ℝ × ℝ → ℝ) :
    ∫ x, φ x ∂(atomMeasure μ lam q) = ∑ i, ∑ j, q i j * φ (μ i, lam j) := by
  unfold atomMeasure
  rw [integral_finsetSum_measure (fun i _ => integrable_finsetSum_measure.mpr fun j _ =>
    (integrable_dirac (f := φ) (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum_measure (fun j _ =>
    (integrable_dirac (f := φ) (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul_measure, integral_dirac]
  simp [ENNReal.toReal_ofReal (hq i j)]

private lemma atom_mass {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (q : Fin m → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j) :
    (atomMeasure μ lam q).real Set.univ = ∑ i, ∑ j, q i j := by
  unfold atomMeasure
  rw [Measure.real_def]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.sum_ne_top.mpr fun j _ => ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.toReal_sum (fun j _ => ENNReal.ofReal_ne_top)]
  exact Finset.sum_congr rfl fun j _ => ENNReal.toReal_ofReal (hq i j)

private lemma fro_sq_eq' {m n : ℕ} (K : Mat m n) :
    fro K ^ 2 = ∑ i, ∑ j, K i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma modeQ_sum {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (Δ : Mat m n) : ∑ i, ∑ j, modeQ S Δ i j = fro Δ ^ 2 := by
  have ht : ∀ {a b : ℕ} (Y : Mat a b), (Y * Matrix.transpose Y).trace = fro Y ^ 2 := by
    intro a b Y
    rw [fro_sq_eq']
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_two]
  have he : fro (Matrix.transpose S.uOut * Δ * S.vIn) ^ 2 = fro Δ ^ 2 := by
    rw [← ht, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S.vIn (Matrix.transpose S.vIn), mul_eq_one_comm.mp S.hvIn,
      Matrix.one_mul]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
    rw [mul_eq_one_comm.mp S.huOut, Matrix.mul_one, ht]
  rw [← he, fro_sq_eq']
  simp_rw [P_apply, modeQ]

private lemma abs_eig_le_opNorm {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (w : Fin k → ℝ) (μ : ℝ) (hw : ∑ a, w a * w a = 1) (he : Matrix.mulVec A w = μ • w) :
    |μ| ≤ opNorm A := by
  set x : EuclideanSpace ℝ (Fin k) := (EuclideanSpace.equiv (Fin k) ℝ).symm w with hxdef
  have hsum : ∑ a, ‖x a‖ ^ 2 = 1 := by
    have hterm : ∀ a, ‖x a‖ ^ 2 = w a * w a := fun a => by
      rw [Real.norm_eq_abs, sq_abs, sq]
      rfl
    simp only [hterm]
    exact hw
  have hx : ‖x‖ = 1 := by rw [EuclideanSpace.norm_eq, hsum, Real.sqrt_one]
  have h1 := Matrix.l2_opNorm_mulVec A x
  have h2 : (EuclideanSpace.equiv (Fin k) ℝ).symm (Matrix.mulVec A ⇑x) = μ • x := by
    ext a
    have ha := congrFun he a
    simp only [hxdef, Pi.smul_apply, smul_eq_mul] at ha ⊢
    exact ha
  rw [h2, norm_smul, hx, Real.norm_eq_abs] at h1
  simp only [mul_one] at h1
  rw [opNorm_eq_norm]
  exact h1

private lemma spec_isFinite {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (Δ : Mat m n) : IsFiniteMeasure (specMeasure S Δ) := by
  constructor
  unfold specMeasure atomMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.2 fun i _ =>
    ENNReal.sum_lt_top.2 fun j _ => ENNReal.ofReal_lt_top

private lemma spec_support {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (Δ : Mat m n) (Cs : ℝ) (hout : opNorm C.Sout ≤ Cs) (hin : opNorm C.Sin ≤ Cs) :
    specMeasure S Δ (specRect Cs)ᶜ = 0 := by
  have hμ : ∀ i, S.μ i ∈ Icc (0 : ℝ) Cs := fun i => ⟨μ_nonneg S i, by
    exact (le_abs_self _).trans ((abs_eig_le_opNorm C.Sout (fun a => S.uOut a i) (S.μ i)
      (sum_col_sq_eq_one S.uOut S.huOut i) (S.eigOut i)).trans hout)⟩
  have hlam : ∀ j, S.lam j ∈ Icc (0 : ℝ) Cs := fun j => ⟨lam_nonneg S j, by
    exact (le_abs_self _).trans ((abs_eig_le_opNorm C.Sin (fun a => S.vIn a j) (S.lam j)
      (sum_col_sq_eq_one S.vIn S.hvIn j) (S.eigIn j)).trans hin)⟩
  have hc : MeasurableSet (specRect Cs)ᶜ := by
    apply MeasurableSet.compl
    exact measurableSet_Icc.prod measurableSet_Icc
  unfold specMeasure atomMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [Measure.dirac_apply' _ hc, Set.indicator_of_notMem]
  · simp
  · exact fun h => h ⟨hμ i, hlam j⟩

private lemma spec_mass {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (Δ : Mat m n) : (specMeasure S Δ).real Set.univ = fro Δ ^ 2 := by
  rw [show specMeasure S Δ = atomMeasure S.μ S.lam (modeQ S Δ) by rfl,
    atom_mass S.μ S.lam (modeQ S Δ) (fun i j => sq_nonneg _), modeQ_sum]

private lemma spec_risk {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (Δ : Mat m n) : riskOf (specMeasure S Δ) = riskSigma C Δ := by
  unfold riskOf specMeasure riskSigma
  rw [atom_integral S.μ S.lam (modeQ S Δ) (fun i j => sq_nonneg _)]
  have hsum : ∑ i, ∑ j, modeQ S Δ i j * (S.μ i * S.lam j) =
      ∑ i, ∑ j, S.μ i * S.lam j * modeQ S Δ i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum, ← lem_app_setup_decomposition_ii S Δ]
  ring

private lemma spec_adm {m n : ℕ} {C : Covariances m n} (p : DynParams)
    (S : SpectralData C) (Δ : Mat m n) (hout : opNorm C.Sout ≤ p.CSig)
    (hin : opNorm C.Sin ≤ p.CSig) (hE : fro Δ ^ 2 ≤ p.Estar + 1)
    (hlo : p.r0 / 2 ≤ riskSigma C Δ) (hhi : riskSigma C Δ ≤ p.r1 + 1 / 2) :
    specMeasure S Δ ∈ admMeasures p := by
  refine ⟨spec_isFinite S Δ, spec_support S Δ p.CSig hout hin, ?_, ?_, ?_⟩
  · simpa [spec_mass S Δ] using hE
  · simpa [spec_risk S Δ] using hlo
  · simpa [spec_risk S Δ] using hhi

private lemma boundEvent_adm (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C) (k : ℕ) :
    boundEvent hyp k ⊆
      {ω | ∀ τ ∈ Icc (0 : ℝ) (Tstar p), actMeas hyp S k ω τ ∈ admMeasures p} := by
  intro ω hω τ hτ
  let t := ⌊(B k : ℝ) * τ⌋₊
  have hnonneg : 0 ≤ (B k : ℝ) * τ := mul_nonneg (Nat.cast_nonneg _) hτ.1
  have ht : (t : ℝ) ≤ (B k : ℝ) * Tstar p := by
    exact (Nat.floor_le hnonneg).trans (mul_le_mul_of_nonneg_left hτ.2 (Nat.cast_nonneg _))
  obtain ⟨hEabs, hRabs⟩ := hω t ht
  have hE0 := hyp.W0_norm k
  change fro (dev0 hyp k) ^ 2 ≤ p.Estar at hE0
  have hR0 := hyp.W0_risk k
  change p.r0 ≤ riskSigma (F k).C (dev0 hyp k) ∧
    riskSigma (F k).C (dev0 hyp k) ≤ p.r1 at hR0
  have hEupper : fro (errPath hyp k t ω) ^ 2 - fro (dev0 hyp k) ^ 2 ≤ 1 / 4 :=
    (le_abs_self _).trans hEabs
  have hRlower : -(min p.r0 1 / 4) ≤
      riskSigma (F k).C (errPath hyp k t ω) - riskSigma (F k).C (dev0 hyp k) :=
    neg_le_of_abs_le hRabs
  have hRupper : riskSigma (F k).C (errPath hyp k t ω) -
      riskSigma (F k).C (dev0 hyp k) ≤ min p.r0 1 / 4 :=
    (le_abs_self _).trans hRabs
  have hminr : min p.r0 1 ≤ p.r0 := min_le_left _ _
  have hmin1 : min p.r0 1 ≤ 1 := min_le_right _ _
  have hadm : specMeasure (S k) (errPath hyp k t ω) ∈ admMeasures p :=
    spec_adm p (S k) (errPath hyp k t ω) (hyp.normBd k).2 (hyp.normBd k).1
      (by nlinarith) (by nlinarith [p.hr0]) (by nlinarith)
  simpa [actMeas, actMeasure, t] using hadm


/-! ### Private helpers for `lem:app-dyn-interval` (i), (ii) -/

private lemma fro_nn' {m n : ℕ} (K : Mat m n) : 0 ≤ fro K := Real.sqrt_nonneg _

private lemma fro_sub_triangle' {m n : ℕ} (A B C' : Mat m n) :
    fro (A - C') ≤ fro (A - B) + fro (B - C') := by
  open scoped Matrix.Norms.Frobenius in
  simp only [fro_eq_norm]
  have := norm_add_le (A - B) (B - C')
  rwa [sub_add_sub_cancel] at this

private lemma errPath_succ' (hyp : DynHyp p P m n B C) (k t : ℕ) (ω : Ω) :
    errPath hyp k (t + 1) ω = errPath hyp k t ω - (p.h / (B k : ℝ)) •
      stepUpdate (C k) (hyp.alg k)
        (runRand (C k) (hyp.alg k) (fun ω => initState (hyp.W0 k) (hyp.Mm1 k ω)) (hyp.x k) t ω)
        (hyp.x k t ω) := by
  simp only [errPath, devRand, runRand, run, step, errorOf, hyp.alg_η]
  module

private lemma fro_stepUpdate_le' (hyp : DynHyp p P m n B C) (k t : ℕ) (ω : Ω) :
    fro (stepUpdate (C k) (hyp.alg k)
        (runRand (C k) (hyp.alg k) (fun ω => initState (hyp.W0 k) (hyp.Mm1 k ω)) (hyp.x k) t ω)
        (hyp.x k t ω)) ≤ Real.sqrt (p.γstar * (B k : ℝ)) := by
  have hγ : 0 ≤ p.γstar * (B k : ℝ) := mul_nonneg p.hγ (Nat.cast_nonneg _)
  unfold stepUpdate
  split_ifs with hz
  · have h0 : fro (0 : Mat (m k) (n k)) = 0 := by simp [fro]
    rw [h0]; exact Real.sqrt_nonneg _
  · have hr : 0 ≤ riskSigma (C k) (errorOf (hyp.alg k)
        (runRand (C k) (hyp.alg k) (fun ω => initState (hyp.W0 k) (hyp.Mm1 k ω)) (hyp.x k) t ω)) := by
      rw [eqn_app_setup_whitened_risk]
      positivity
    have hh : 0 ≤ 2 * riskSigma (C k) (errorOf (hyp.alg k)
        (runRand (C k) (hyp.alg k) (fun ω => initState (hyp.W0 k) (hyp.Mm1 k ω)) (hyp.x k) t ω))
        * (hyp.alg k).ϱ := mul_nonneg (mul_nonneg (by norm_num) hr) (hyp.alg k).hϱ.le
    obtain ⟨_, hf, hk, _⟩ := lem_app_setup_filter_i _ hh
      (stepBuffer (hyp.alg k)
        (runRand (C k) (hyp.alg k) (fun ω => initState (hyp.W0 k) (hyp.Mm1 k ω)) (hyp.x k) t ω)
        (hyp.x k t ω))
    have hmin : ((min (m k) (n k) : ℕ) : ℝ) ≤ p.γstar * B k :=
      (by exact_mod_cast (min_le_max : min (m k) (n k) ≤ max (m k) (n k)) :
        ((min (m k) (n k) : ℕ) : ℝ) ≤ ((max (m k) (n k) : ℕ) : ℝ)).trans (hyp.dims k)
    have hk' : ((stepBuffer (hyp.alg k)
        (runRand (C k) (hyp.alg k) (fun ω => initState (hyp.W0 k) (hyp.Mm1 k ω)) (hyp.x k) t ω)
        (hyp.x k t ω)).rank : ℝ) ≤ ((min (m k) (n k) : ℕ) : ℝ) := by exact_mod_cast hk
    exact (Real.le_sqrt (fro_nn' _) hγ).mpr (hf.trans (hk'.trans hmin))

/-- One-step movement of the error path in Frobenius norm. -/
private lemma fro_errPath_succ_le' (hyp : DynHyp p P m n B C) (k t : ℕ) (ω : Ω) :
    fro (errPath hyp k (t + 1) ω - errPath hyp k t ω) ≤
      p.h / (B k : ℝ) * Real.sqrt (p.γstar * (B k : ℝ)) := by
  have hη : 0 ≤ p.h / (B k : ℝ) := div_nonneg p.hh.le (Nat.cast_nonneg _)
  rw [errPath_succ', sub_sub_cancel_left]
  open scoped Matrix.Norms.Frobenius in
  simp only [fro_eq_norm, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
  simpa only [fro_eq_norm] using
    mul_le_mul_of_nonneg_left (fro_stepUpdate_le' hyp k t ω) hη

private lemma fro_errPath_le' (hyp : DynHyp p P m n B C) (k t s : ℕ) (ω : Ω) :
    fro (errPath hyp k (t + s) ω - errPath hyp k t ω) ≤
      (s : ℝ) * (p.h / (B k : ℝ) * Real.sqrt (p.γstar * (B k : ℝ))) := by
  induction s with
  | zero => simp [fro]
  | succ s ih =>
    rw [show t + (s + 1) = t + s + 1 by ring]
    have h1 := fro_sub_triangle' (errPath hyp k (t + s + 1) ω) (errPath hyp k (t + s) ω)
      (errPath hyp k t ω)
    have h2 := fro_errPath_succ_le' hyp k (t + s) ω
    push_cast
    linarith


private lemma modeQ_diff_sum' {m n : ℕ} {C' : Covariances m n} (S : SpectralData C')
    (D D' : Mat m n) :
    ∑ i, ∑ j, |modeQ S D' i j - modeQ S D i j| ≤ fro (D' - D) * (fro D' + fro D) := by
  have hlin : ∀ (X Y : Mat m n) i j, S.u i ⬝ᵥ ((X + Y) *ᵥ S.v j) =
      S.u i ⬝ᵥ (X *ᵥ S.v j) + S.u i ⬝ᵥ (Y *ᵥ S.v j) := by
    intro X Y i j
    rw [Matrix.add_mulVec, dotProduct_add]
  have hlin' : ∀ (X Y : Mat m n) i j, S.u i ⬝ᵥ ((X - Y) *ᵥ S.v j) =
      S.u i ⬝ᵥ (X *ᵥ S.v j) - S.u i ⬝ᵥ (Y *ᵥ S.v j) := by
    intro X Y i j
    rw [Matrix.sub_mulVec, dotProduct_sub]
  have hterm : ∀ i j, |modeQ S D' i j - modeQ S D i j| =
      |S.u i ⬝ᵥ ((D' - D) *ᵥ S.v j)| * |S.u i ⬝ᵥ ((D' + D) *ᵥ S.v j)| := by
    intro i j
    rw [← abs_mul, hlin', hlin]
    unfold modeQ
    congr 1
    ring
  have hsq : ∀ X : Mat m n, ∑ i, ∑ j, |S.u i ⬝ᵥ (X *ᵥ S.v j)| ^ 2 = fro X ^ 2 := by
    intro X
    rw [← modeQ_sum S X]
    simp [modeQ, sq_abs]
  have h1 : ∑ i, ∑ j, |modeQ S D' i j - modeQ S D i j| =
      ∑ x : Fin m × Fin n, |S.u x.1 ⬝ᵥ ((D' - D) *ᵥ S.v x.2)| *
        |S.u x.1 ⬝ᵥ ((D' + D) *ᵥ S.v x.2)| := by
    rw [Fintype.sum_prod_type]
    simp_rw [hterm]
  rw [h1]
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
  have e1 : ∑ x : Fin m × Fin n, |S.u x.1 ⬝ᵥ ((D' - D) *ᵥ S.v x.2)| ^ 2 = fro (D' - D) ^ 2 := by
    rw [Fintype.sum_prod_type]; exact hsq _
  have e2 : ∑ x : Fin m × Fin n, |S.u x.1 ⬝ᵥ ((D' + D) *ᵥ S.v x.2)| ^ 2 = fro (D' + D) ^ 2 := by
    rw [Fintype.sum_prod_type]; exact hsq _
  rw [e1, e2, Real.sqrt_sq (fro_nn' _), Real.sqrt_sq (fro_nn' _)]
  refine mul_le_mul_of_nonneg_left ?_ (fro_nn' _)
  open scoped Matrix.Norms.Frobenius in
  simp only [fro_eq_norm]
  exact norm_add_le _ _

private lemma fro_le_add' {m n : ℕ} (D D' : Mat m n) : fro D' ≤ fro D + fro (D' - D) := by
  open scoped Matrix.Norms.Frobenius in
  simp only [fro_eq_norm]
  have := norm_add_le D (D' - D)
  rwa [add_sub_cancel] at this

private lemma spec_mu_mem' {m n : ℕ} {C' : Covariances m n} (S : SpectralData C') (Cs : ℝ)
    (hout : opNorm C'.Sout ≤ Cs) (hin : opNorm C'.Sin ≤ Cs) :
    (∀ i, S.μ i ∈ Icc (0 : ℝ) Cs) ∧ (∀ j, S.lam j ∈ Icc (0 : ℝ) Cs) :=
  ⟨fun i => ⟨μ_nonneg S i, (le_abs_self _).trans ((abs_eig_le_opNorm C'.Sout (fun a => S.uOut a i)
      (S.μ i) (sum_col_sq_eq_one S.uOut S.huOut i) (S.eigOut i)).trans hout)⟩,
   fun j => ⟨lam_nonneg S j, (le_abs_self _).trans ((abs_eig_le_opNorm C'.Sin (fun a => S.vIn a j)
      (S.lam j) (sum_col_sq_eq_one S.vIn S.hvIn j) (S.eigIn j)).trans hin)⟩⟩

private lemma risk_diff_le' {m n : ℕ} {C' : Covariances m n} (S : SpectralData C') (Cs : ℝ)
    (hout : opNorm C'.Sout ≤ Cs) (hin : opNorm C'.Sin ≤ Cs) (D D' : Mat m n) :
    |riskSigma C' D' - riskSigma C' D| ≤
      (1 / 2) * Cs ^ 2 * (fro (D' - D) * (fro D' + fro D)) := by
  obtain ⟨hμ, hl⟩ := spec_mu_mem' S Cs hout hin
  have hr : ∀ X : Mat m n, riskSigma C' X =
      (1 / 2) * ∑ i, ∑ j, modeQ S X i j * (S.μ i * S.lam j) := by
    intro X
    rw [← spec_risk S X]
    unfold riskOf specMeasure
    rw [atom_integral S.μ S.lam (modeQ S X) (fun i j => sq_nonneg _)]
  rw [hr D', hr D, ← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← sub_mul]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hb : |∑ i, ∑ j, (modeQ S D' i j - modeQ S D i j) * (S.μ i * S.lam j)| ≤
      Cs ^ 2 * ∑ i, ∑ j, |modeQ S D' i j - modeQ S D i j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, abs_of_nonneg (mul_nonneg (hμ i).1 (hl j).1)]
    have : S.μ i * S.lam j ≤ Cs ^ 2 := by
      rw [sq]; exact mul_le_mul (hμ i).2 (hl j).2 (hl j).1 ((hμ i).1.trans (hμ i).2)
    nlinarith [abs_nonneg (modeQ S D' i j - modeQ S D i j)]
  have := modeQ_diff_sum' S D D'
  nlinarith


private lemma spec_adm_gen' {m n : ℕ} {C' : Covariances m n} (Cs M rlo rhi : ℝ)
    (S : SpectralData C') (Δ : Mat m n) (hout : opNorm C'.Sout ≤ Cs)
    (hin : opNorm C'.Sin ≤ Cs) (hE : fro Δ ^ 2 ≤ M)
    (hlo : rlo ≤ riskSigma C' Δ) (hhi : riskSigma C' Δ ≤ rhi) :
    specMeasure S Δ ∈ Adm Cs M rlo rhi := by
  refine ⟨spec_isFinite S Δ, spec_support S Δ Cs hout hin, ?_, ?_, ?_⟩
  · simpa [spec_mass S Δ] using hE
  · simpa [spec_risk S Δ] using hlo
  · simpa [spec_risk S Δ] using hhi

/-- The perturbation constant. -/
private def pertK (p : DynParams) : ℝ := (p.CSig ^ 2 + 1) * (2 * Real.sqrt (p.Estar + 1) + 1)

private lemma pertK_nonneg (p : DynParams) : 0 ≤ pertK p := by
  unfold pertK; positivity

private lemma pert_adm' {m n : ℕ} {C' : Covariances m n} (p : DynParams)
    (S : SpectralData C') (hout : opNorm C'.Sout ≤ p.CSig) (hin : opNorm C'.Sin ≤ p.CSig)
    (D D' : Mat m n) (hD : D ∈ admA p C') (ν ε : ℝ) (hν0 : 0 ≤ ν) (hν : fro (D' - D) ≤ ν)
    (hν1 : ν ≤ 1) (hε : pertK p * ν ≤ ε) :
    specMeasure S D' ∈ Adm p.CSig (p.Estar + 1 + ε) (p.r0 / 2 - ε) (p.r1 + 1 / 2 + ε) := by
  obtain ⟨hDlo, hDhi, hDE⟩ := hD
  change p.r0 / 2 ≤ riskSigma C' D at hDlo
  change riskSigma C' D ≤ p.r1 + 1 / 2 at hDhi
  change fro D ^ 2 ≤ p.Estar + 1 at hDE
  have ha : fro D ≤ Real.sqrt (p.Estar + 1) := Real.le_sqrt_of_sq_le hDE
  have h1 := fro_le_add' D D'
  have hD'a : fro D' ≤ Real.sqrt (p.Estar + 1) + ν := by linarith
  have hsum : fro D' + fro D ≤ 2 * Real.sqrt (p.Estar + 1) + 1 := by linarith
  have hsum0 : 0 ≤ fro D' + fro D := add_nonneg (fro_nn' _) (fro_nn' _)
  have hprod : fro (D' - D) * (fro D' + fro D) ≤ ν * (2 * Real.sqrt (p.Estar + 1) + 1) :=
    mul_le_mul hν hsum hsum0 hν0
  have hCs : 0 ≤ p.CSig ^ 2 := by positivity
  have hrd := risk_diff_le' S p.CSig hout hin D D'
  have hmass : fro D' ^ 2 ≤ fro D ^ 2 + fro (D' - D) * (fro D' + fro D) := by
    have h2 : fro D' - fro D ≤ fro (D' - D) := by linarith
    nlinarith [fro_nn' D, fro_nn' D']
  have hK : pertK p * ν = (p.CSig ^ 2 + 1) * (ν * (2 * Real.sqrt (p.Estar + 1) + 1)) := by
    unfold pertK; ring
  have hP0 : 0 ≤ ν * (2 * Real.sqrt (p.Estar + 1) + 1) := by positivity
  have hrisk : |riskSigma C' D' - riskSigma C' D| ≤ ε := by
    refine hrd.trans ?_
    have : (1 / 2) * p.CSig ^ 2 * (fro (D' - D) * (fro D' + fro D)) ≤
        (p.CSig ^ 2 + 1) * (ν * (2 * Real.sqrt (p.Estar + 1) + 1)) := by
      have hq : fro (D' - D) * (fro D' + fro D) ≤ ν * (2 * Real.sqrt (p.Estar + 1) + 1) := hprod
      have hq0 : 0 ≤ fro (D' - D) * (fro D' + fro D) :=
        mul_nonneg (fro_nn' _) hsum0
      nlinarith
    linarith
  refine spec_adm_gen' p.CSig _ _ _ S D' hout hin ?_ ?_ ?_
  · have : (p.CSig ^ 2 + 1) * (ν * (2 * Real.sqrt (p.Estar + 1) + 1)) ≥
        ν * (2 * Real.sqrt (p.Estar + 1) + 1) := by nlinarith
    linarith
  · have := (abs_le.mp hrisk).1
    linarith
  · have := (abs_le.mp hrisk).2
    linarith


private lemma nu_small' (hB : Tendsto (fun k : ℕ => B k) atTop atTop) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, (blockLen (B k) : ℝ) * (p.h / (B k : ℝ) * Real.sqrt (p.γstar * (B k : ℝ))) ≤ δ := by
  have hx : Tendsto (fun k : ℕ => ((B k : ℕ) : ℝ) ^ ((1 : ℝ) / 8)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      (tendsto_natCast_atTop_atTop.comp hB)
  have hx3 : Tendsto (fun k : ℕ => (p.h * Real.sqrt p.γstar) /
      (((B k : ℕ) : ℝ) ^ ((1 : ℝ) / 8)) ^ 3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp hx)
  filter_upwards [hx3.eventually (gt_mem_nhds hδ), hx.eventually_gt_atTop 0,
    hB.eventually_gt_atTop 0] with k hk hxpos hBpos
  set x : ℝ := ((B k : ℕ) : ℝ) ^ ((1 : ℝ) / 8) with hxdef
  have hBR : (0 : ℝ) < (B k : ℝ) := by exact_mod_cast hBpos
  have hx8 : x ^ 8 = (B k : ℝ) := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul hBR.le]; norm_num
  have hL : (blockLen (B k) : ℝ) ≤ x := Nat.floor_le (Real.rpow_nonneg hBR.le _)
  have hsq : Real.sqrt (B k : ℝ) = x ^ 4 := by
    rw [← hx8, show x ^ 8 = (x ^ 4) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hγ := p.hγ
  have hexp : p.h / (B k : ℝ) * Real.sqrt (p.γstar * (B k : ℝ)) =
      (p.h * Real.sqrt p.γstar) / x ^ 4 := by
    rw [Real.sqrt_mul hγ, hsq, ← hx8]
    field_simp
  rw [hexp]
  have hnn : 0 ≤ (p.h * Real.sqrt p.γstar) / x ^ 4 := by
    have := p.hh; positivity
  calc (blockLen (B k) : ℝ) * ((p.h * Real.sqrt p.γstar) / x ^ 4)
      ≤ x * ((p.h * Real.sqrt p.γstar) / x ^ 4) := mul_le_mul_of_nonneg_right hL hnn
    _ = (p.h * Real.sqrt p.γstar) / x ^ 3 := by field_simp
    _ ≤ δ := hk.le

private lemma notMem_of_lt_exit' (hyp : DynHyp p P m n B C) (k : ℕ) (ω : Ω) (b : ℕ)
    (hb : (b : ℕ∞) < blockExitIdx hyp k ω) :
    errPath hyp k (b * blockLen (B k)) ω ∈ admA p (C k) := by
  by_contra h
  have : blockExitIdx hyp k ω ≤ (b : ℕ∞) :=
    iInf₂_le (f := fun (b : ℕ) (_ : errPath hyp k (b * blockLen (B k)) ω ∉ admA p (C k)) =>
      (b : ℕ∞)) b h
  exact absurd hb (not_lt.mpr this)

private lemma act_mem_adm' (hB : Tendsto (fun k : ℕ => B k) atTop atTop)
    (hyp : DynHyp p P m n B C) (S : ∀ k : ℕ, SpectralData (C k)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ (ω : Ω) (σ : ℝ),
      ((⌊(B k : ℝ) * σ⌋₊ : ℕ) : ℕ∞) < (blockLen (B k) : ℕ∞) * blockExitIdx hyp k ω →
      actMeas hyp S k ω σ ∈ Adm p.CSig (p.Estar + 1 + ε) (p.r0 / 2 - ε) (p.r1 + 1 / 2 + ε) := by
  have hKpos : 0 < pertK p + 1 := by linarith [pertK_nonneg p]
  filter_upwards [nu_small' hB (min 1 (ε / (pertK p + 1))) (lt_min one_pos (div_pos hε hKpos))]
    with k hk ω σ hlt
  set t := ⌊(B k : ℝ) * σ⌋₊ with ht
  set L := blockLen (B k) with hL
  have hL0 : L ≠ 0 := by
    intro h0
    rw [h0] at hlt
    simp at hlt
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
  set b := t / L with hb
  have hbt : b * L ≤ t := Nat.div_mul_le_self t L
  have hbc : (b : ℕ∞) < blockExitIdx hyp k ω := by
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : (L : ℕ∞) * blockExitIdx hyp k ω ≤ (L : ℕ∞) * (b : ℕ∞) := mul_le_mul_right hcon _
    have h2 : (L : ℕ∞) * (b : ℕ∞) ≤ (t : ℕ∞) := by
      rw [← Nat.cast_mul]; exact_mod_cast (by rw [mul_comm]; exact hbt)
    exact absurd hlt (not_lt.mpr (h1.trans h2))
  have hD := notMem_of_lt_exit' hyp k ω b hbc
  have hts : t = b * L + t % L := by
    have := Nat.div_add_mod' t L
    rw [hb]; omega
  have hmod : t % L < L := Nat.mod_lt _ hLpos
  have hmv := fro_errPath_le' hyp k (b * L) (t % L) ω
  rw [← hts] at hmv
  have hstep0 : 0 ≤ p.h / (B k : ℝ) * Real.sqrt (p.γstar * (B k : ℝ)) :=
    mul_nonneg (div_nonneg p.hh.le (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
  have hν : fro (errPath hyp k t ω - errPath hyp k (b * L) ω) ≤
      (L : ℝ) * (p.h / (B k : ℝ) * Real.sqrt (p.γstar * (B k : ℝ))) :=
    hmv.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hmod.le) hstep0)
  have hν0 : 0 ≤ (L : ℝ) * (p.h / (B k : ℝ) * Real.sqrt (p.γstar * (B k : ℝ))) :=
    mul_nonneg (Nat.cast_nonneg _) hstep0
  have hk1 := (le_min_iff.mp hk).1
  have hk2 := (le_min_iff.mp hk).2
  have hε' : pertK p * ((L : ℝ) * (p.h / (B k : ℝ) * Real.sqrt (p.γstar * (B k : ℝ)))) ≤ ε := by
    have : (L : ℝ) * (p.h / (B k : ℝ) * Real.sqrt (p.γstar * (B k : ℝ))) * (pertK p + 1) ≤ ε := by
      calc _ ≤ ε / (pertK p + 1) * (pertK p + 1) := mul_le_mul_of_nonneg_right hk2 hKpos.le
        _ = ε := by field_simp
    nlinarith [pertK_nonneg p]
  exact pert_adm' p (S k) (hyp.normBd k).2 (hyp.normBd k).1 _ _ hD _ ε hν0 hν hk1 hε'


private lemma exit_cases' (hyp : DynHyp p P m n B C) (k : ℕ) (ω : Ω) :
    blockExitIdx hyp k ω = ⊤ ∨ ∃ b : ℕ, blockExitIdx hyp k ω = (b : ℕ∞) ∧
      errPath hyp k (b * blockLen (B k)) ω ∉ admA p (C k) := by
  classical
  by_cases hS : ∃ b : ℕ, errPath hyp k (b * blockLen (B k)) ω ∉ admA p (C k)
  · right
    refine ⟨Nat.find hS, le_antisymm ?_ ?_, Nat.find_spec hS⟩
    · exact iInf₂_le (f := fun (b : ℕ) (_ : errPath hyp k (b * blockLen (B k)) ω ∉ admA p (C k)) =>
        (b : ℕ∞)) (Nat.find hS) (Nat.find_spec hS)
    · refine le_iInf₂ fun b hb => ?_
      exact_mod_cast Nat.find_min' hS hb
  · left
    refine top_le_iff.mp (le_iInf₂ fun b hb => ?_)
    exact absurd ⟨b, hb⟩ hS

/-- Field bounds at an admissible measure, for the two test pairs. -/
private lemma field_bds' (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k)) (k : ℕ)
    (M rlo rhi : ℝ) (hrlo : 0 < rlo) (hrhi : rhi ≤ p.r1 + 1) (χ : Measure (ℝ × ℝ))
    (hχ : χ ∈ Adm p.CSig M rlo rhi) :
    |fieldOp p.h (c k).d (c k).ζ χ (tensorFG (fun _ => 1) (fun _ => 1))| ≤
        2 * p.h * dMax p * M / Real.sqrt rlo + p.h ^ 2 * mZeta p ∧
      |fieldOp p.h (c k).d (c k).ζ χ (tensorFG (fun x => x / 2) (fun x => x))| ≤ CR p := by
  obtain ⟨h1, -, -, h4⟩ := lem_app_dyn_field_i_gen p (S k) (c k) (hyp.normBd k).2 (hyp.normBd k).1
    M rlo rhi hrlo χ hχ
  have e1 : tensorFG (fun _ => 1) (fun _ => 1) = fun _ => (1 : ℝ) := by
    funext x; simp [tensorFG]
  have e2 : fieldOp p.h (c k).d (c k).ζ χ (tensorFG (fun x => x / 2) (fun x => x)) =
      (1 / 2) * fieldOp p.h (c k).d (c k).ζ χ (fun x => x.1 * x.2) := by
    unfold fieldOp tensorFG
    split_ifs
    · have a1 : (fun x : ℝ × ℝ => x.1 / 2 * x.2 * (c k).d x) =
          fun x => (1 / 2) * (x.1 * x.2 * (c k).d x) := by funext x; ring
      have a2 : (fun x : ℝ × ℝ => x.1 / 2 * x.2) = fun x => (1 / 2) * (x.1 * x.2) := by
        funext x; ring
      simp only [a1, a2, integral_const_mul]
      ring
    · simp
  rw [e1]
  refine ⟨h1, ?_⟩
  rw [e2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  refine h4.trans ?_
  unfold CR
  have hsq : Real.sqrt rhi ≤ Real.sqrt (p.r1 + 1) := Real.sqrt_le_sqrt hrhi
  have hpos : 0 ≤ 2 * p.h * dMax p :=
    mul_nonneg (mul_nonneg (by norm_num) p.hh.le) (by unfold dMax; positivity)
  nlinarith


private lemma int_bound' (G : ℝ → ℝ) (s A : ℝ) (hs : 0 ≤ s)
    (hG : ∀ σ : ℝ, 0 ≤ σ → σ < s → |G σ| ≤ A) :
    |∫ σ in (0 : ℝ)..s, G σ| ≤ A * s := by
  have hae : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Set.Ioc (0 : ℝ) s → ‖G σ‖ ≤ A := by
    filter_upwards [(Set.countable_singleton s).ae_notMem (volume : Measure ℝ)] with σ hσ hmem
    have hlt : σ < s := lt_of_le_of_ne hmem.2 (fun h => hσ (by simp [h]))
    exact hG σ hmem.1.le hlt
  have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hs hae
    (intervalIntegrable_const (c := A))
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm] at this
  simpa using this

private lemma errPath_zero' (hyp : DynHyp p P m n B C) (k : ℕ) (ω : Ω) :
    errPath hyp k 0 ω = dev0 hyp k := by
  simp [errPath, devRand, runRand, run, errorOf, initState, dev0]

private lemma lt_exit_of_lt_stop' (hyp : DynHyp p P m n B C) (k : ℕ) (ω : Ω)
    (hBk : 0 < B k) (hL : 0 < blockLen (B k)) (τ σ : ℝ) (hσ : 0 ≤ σ)
    (hlt : σ < stopMacro (blockLen (B k)) (B k) (blockExitIdx hyp k ω) τ) :
    ((⌊(B k : ℝ) * σ⌋₊ : ℕ) : ℕ∞) < (blockLen (B k) : ℕ∞) * blockExitIdx hyp k ω := by
  by_cases hb : blockExitIdx hyp k ω = ⊤
  · rw [hb, ENat.mul_top (by exact_mod_cast hL.ne')]
    exact ENat.coe_lt_top _
  · obtain ⟨b0, hb0⟩ := ENat.ne_top_iff_exists.mp hb
    rw [← hb0]
    unfold stopMacro at hlt
    rw [if_neg hb, ← hb0] at hlt
    simp only [ENat.toNat_coe] at hlt
    have hBR : (0 : ℝ) < (B k : ℝ) := by exact_mod_cast hBk
    have h1 : σ < (blockLen (B k) : ℝ) * (b0 : ℝ) / (B k : ℝ) := lt_of_lt_of_le hlt (min_le_right _ _)
    have h2 : (B k : ℝ) * σ < ((blockLen (B k) * b0 : ℕ) : ℝ) := by
      rw [lt_div_iff₀ hBR] at h1
      push_cast; linarith
    have h3 := (Nat.floor_lt (mul_nonneg hBR.le hσ)).mpr h2
    rw [← Nat.cast_mul]
    exact_mod_cast h3

private lemma I1_eq' (hyp : DynHyp p P m n B C) (S : ∀ k : ℕ, SpectralData (C k)) (k : ℕ) (ω : Ω)
    (σ : ℝ) :
    ∫ x, tensorFG (fun _ => 1) (fun _ => 1) x ∂(actMeas hyp S k ω σ) =
      fro (errPath hyp k ⌊(B k : ℝ) * σ⌋₊ ω) ^ 2 := by
  have e1 : tensorFG (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) = fun _ => (1 : ℝ) := by
    funext x; simp [tensorFG]
  rw [e1, integral_const, smul_eq_mul, mul_one]
  exact spec_mass (S k) _

private lemma I2_eq' (hyp : DynHyp p P m n B C) (S : ∀ k : ℕ, SpectralData (C k)) (k : ℕ) (ω : Ω)
    (σ : ℝ) :
    ∫ x, tensorFG (fun x => x / 2) (fun x => x) x ∂(actMeas hyp S k ω σ) =
      riskSigma (C k) (errPath hyp k ⌊(B k : ℝ) * σ⌋₊ ω) := by
  have e1 : (tensorFG (fun x : ℝ => x / 2) (fun x : ℝ => x)) =
      fun x : ℝ × ℝ => (1 / 2) * (x.1 * x.2) := by
    funext x; simp only [tensorFG]; ring
  rw [e1, integral_const_mul, ← spec_risk (S k)]
  rfl


/-- The deterministic core: on the event that the actual measures before the exit are in an enlarged
admissible set, the stopped energy and risk move by at most the field bound times the stopped time plus
the block residual. -/
private lemma stopped_dev' (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k)) (k : ℕ)
    (ε : ℝ) (hε1 : ε ≤ 1 / 2) (hεr : 0 < p.r0 / 2 - ε)
    (hBk : 0 < B k) (hL : 0 < blockLen (B k)) (ω : Ω)
    (hadm : ∀ σ : ℝ, ((⌊(B k : ℝ) * σ⌋₊ : ℕ) : ℕ∞) < (blockLen (B k) : ℕ∞) * blockExitIdx hyp k ω →
      actMeas hyp S k ω σ ∈ Adm p.CSig (p.Estar + 1 + ε) (p.r0 / 2 - ε) (p.r1 + 1 / 2 + ε))
    (τ : ℝ) (hτ : 0 ≤ τ) (ρ : ℝ)
    (h1 : blockResidual hyp S c (fun _ => 1) (fun _ => 1) k ω τ ≤ ρ)
    (h2 : blockResidual hyp S c (fun x => x / 2) (fun x => x) k ω τ ≤ ρ) :
    |fro (errPath hyp k ⌊(B k : ℝ) * stopMacro (blockLen (B k)) (B k) (blockExitIdx hyp k ω) τ⌋₊ ω) ^ 2
        - fro (dev0 hyp k) ^ 2| ≤
      (2 * p.h * dMax p * (p.Estar + 1 + ε) / Real.sqrt (p.r0 / 2 - ε) + p.h ^ 2 * mZeta p) *
        stopMacro (blockLen (B k)) (B k) (blockExitIdx hyp k ω) τ + ρ ∧
    |riskSigma (F k).C (errPath hyp k ⌊(B k : ℝ) * stopMacro (blockLen (B k)) (B k)
          (blockExitIdx hyp k ω) τ⌋₊ ω) - riskSigma (F k).C (dev0 hyp k)| ≤
      CR p * stopMacro (blockLen (B k)) (B k) (blockExitIdx hyp k ω) τ + ρ := by
  set s := stopMacro (blockLen (B k)) (B k) (blockExitIdx hyp k ω) τ with hsdef
  have hs0 : 0 ≤ s := by
    rw [hsdef]; unfold stopMacro
    split_ifs
    · exact hτ
    · exact le_min hτ (by positivity)
  have hmem : ∀ σ : ℝ, 0 ≤ σ → σ < s →
      actMeas hyp S k ω σ ∈ Adm p.CSig (p.Estar + 1 + ε) (p.r0 / 2 - ε) (p.r1 + 1 / 2 + ε) :=
    fun σ hσ hlt => hadm σ (lt_exit_of_lt_stop' hyp k ω hBk hL τ σ hσ hlt)
  have hb := fun σ (hσ : 0 ≤ σ) (hlt : σ < s) =>
    field_bds' F hyp S c k _ _ _ hεr (by linarith) _ (hmem σ hσ hlt)
  have hJ1 := int_bound' (fun σ => fieldOp p.h (c k).d (c k).ζ (actMeas hyp S k ω σ)
    (tensorFG (fun _ => 1) (fun _ => 1))) s _ hs0 (fun σ hσ hlt => (hb σ hσ hlt).1)
  have hJ2 := int_bound' (fun σ => fieldOp p.h (c k).d (c k).ζ (actMeas hyp S k ω σ)
    (tensorFG (fun x => x / 2) (fun x => x))) s _ hs0 (fun σ hσ hlt => (hb σ hσ hlt).2)
  unfold blockResidual at h1 h2
  rw [← hsdef] at h1 h2
  have hI1s := I1_eq' hyp S k ω s
  have hI10 := I1_eq' hyp S k ω 0
  have hI2s := I2_eq' hyp S k ω s
  have hI20 := I2_eq' hyp S k ω 0
  simp only [mul_zero, Nat.floor_zero, errPath_zero'] at hI10 hI20
  rw [hI1s, hI10] at h1
  rw [hI2s, hI20] at h2
  constructor
  · calc _ = |(fro (errPath hyp k ⌊(B k : ℝ) * s⌋₊ ω) ^ 2 - fro (dev0 hyp k) ^ 2 -
          ∫ σ in (0 : ℝ)..s, fieldOp p.h (c k).d (c k).ζ (actMeas hyp S k ω σ)
            (tensorFG (fun _ => 1) (fun _ => 1))) +
          ∫ σ in (0 : ℝ)..s, fieldOp p.h (c k).d (c k).ζ (actMeas hyp S k ω σ)
            (tensorFG (fun _ => 1) (fun _ => 1))| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by linarith [h1, hJ1])
  · calc _ = |(riskSigma (F k).C (errPath hyp k ⌊(B k : ℝ) * s⌋₊ ω) - riskSigma (F k).C (dev0 hyp k) -
          ∫ σ in (0 : ℝ)..s, fieldOp p.h (c k).d (c k).ζ (actMeas hyp S k ω σ)
            (tensorFG (fun x => x / 2) (fun x => x))) +
          ∫ σ in (0 : ℝ)..s, fieldOp p.h (c k).d (c k).ζ (actMeas hyp S k ω σ)
            (tensorFG (fun x => x / 2) (fun x => x))| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by linarith [h2, hJ2])


private lemma dMax_nonneg'' (p : DynParams) : 0 ≤ dMax p := by
  unfold dMax; exact div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)

private lemma mZeta_nonneg'' (p : DynParams) : 0 ≤ mZeta p := by
  have hk : 0 ≤ kStar p.CSig p.γstar p.ϱ := by
    unfold kStar
    exact mul_nonneg (by linarith [p.hC]) (Real.sqrt_nonneg _)
  unfold mZeta
  exact add_nonneg p.hγ
    (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk) p.hβ.1) (by linarith [p.hβ.2]))

private lemma CE_nonneg'' (p : DynParams) : 0 ≤ CE p := by
  unfold CE
  exact add_nonneg
    (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hh.le)
      (dMax_nonneg'' p)) (by linarith [p.hE])) (Real.sqrt_nonneg _))
    (mul_nonneg (sq_nonneg _) (mZeta_nonneg'' p))

private lemma CR_nonneg'' (p : DynParams) : 0 ≤ CR p := by
  unfold CR
  exact add_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hh.le) (dMax_nonneg'' p))
      (Real.sqrt_nonneg _))
    (div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mZeta_nonneg'' p)) (by norm_num))

private lemma Tstar_bds' (p : DynParams) :
    0 ≤ Tstar p ∧ (CE p + 1 / 2) * Tstar p ≤ min p.r0 1 / 8 ∧ CR p * Tstar p ≤ min p.r0 1 / 8 := by
  have hm : 0 < min p.r0 1 := lt_min p.hr0 zero_lt_one
  have hCE := CE_nonneg'' p
  have hCR := CR_nonneg'' p
  have hD : 0 < 8 * (1 + CE p + CR p) := by positivity
  have hT : Tstar p = min p.r0 1 / (8 * (1 + CE p + CR p)) := rfl
  refine ⟨by rw [hT]; positivity, ?_, ?_⟩
  · rw [hT, ← mul_div_assoc, div_le_iff₀ hD]
    nlinarith
  · rw [hT, ← mul_div_assoc, div_le_iff₀ hD]
    nlinarith

private lemma L_facts' (hB : Tendsto (fun k : ℕ => B k) atTop atTop) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, 0 < B k ∧ 1 ≤ blockLen (B k) ∧ (blockLen (B k) : ℝ) ≤ (B k : ℝ) ∧
      (blockLen (B k) : ℝ) / (B k : ℝ) ≤ δ := by
  have hx : Tendsto (fun k : ℕ => ((B k : ℕ) : ℝ) ^ ((1 : ℝ) / 8)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      (tendsto_natCast_atTop_atTop.comp hB)
  filter_upwards [hx.eventually_ge_atTop (max 1 (1 / δ)), hB.eventually_gt_atTop 0] with k hk hBpos
  set x : ℝ := ((B k : ℕ) : ℝ) ^ ((1 : ℝ) / 8) with hxdef
  have hBR : (0 : ℝ) < (B k : ℝ) := by exact_mod_cast hBpos
  have hx8 : x ^ 8 = (B k : ℝ) := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul hBR.le]; norm_num
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hk
  have hxδ : 1 / δ ≤ x := (le_max_right _ _).trans hk
  have hL1 : 1 ≤ blockLen (B k) := Nat.le_floor (by rw [Nat.cast_one]; exact hx1)
  have hLx : (blockLen (B k) : ℝ) ≤ x := Nat.floor_le (Real.rpow_nonneg hBR.le _)
  have hxB : x ≤ (B k : ℝ) := by
    rw [← hx8]; exact le_self_pow₀ hx1 (by norm_num)
  refine ⟨hBpos, hL1, hLx.trans hxB, ?_⟩
  have hxpos : 0 < x := by linarith
  have h1 : (blockLen (B k) : ℝ) / (B k : ℝ) ≤ x / x ^ 8 := by
    rw [hx8]; exact div_le_div_of_nonneg_right hLx hBR.le
  have h2 : x / x ^ 8 ≤ 1 / x := by
    rw [div_le_div_iff₀ (by positivity) hxpos]
    have : x ^ 2 ≤ x ^ 8 := pow_le_pow_right₀ hx1 (by norm_num)
    nlinarith
  have h3 : 1 / x ≤ δ := by
    rw [div_le_iff₀ hxpos]
    have := (div_le_iff₀ hδ).mp hxδ
    linarith
  linarith


private lemma eps_choice' (p : DynParams) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ min (p.r0 / 4) (1 / 2) ∧
      2 * p.h * dMax p * (p.Estar + 1 + ε) / Real.sqrt (p.r0 / 2 - ε) + p.h ^ 2 * mZeta p ≤
        CE p + 1 / 2 := by
  set g : ℝ → ℝ := fun ε => 2 * p.h * dMax p * (p.Estar + 1 + ε) / Real.sqrt (p.r0 / 2 - ε) +
    p.h ^ 2 * mZeta p with hg
  have hr : 0 < p.r0 / 2 := by linarith [p.hr0]
  have hcont : ContinuousAt g 0 := by
    refine ContinuousAt.add (ContinuousAt.div ?_ ?_ ?_) continuousAt_const
    · exact continuousAt_const.mul (continuousAt_const.add continuousAt_id)
    · exact (Real.continuous_sqrt.continuousAt).comp (continuousAt_const.sub continuousAt_id)
    · simp only [sub_zero]; exact (Real.sqrt_pos.mpr hr).ne'
  have hg0 : g 0 = CE p := by
    simp only [hg, add_zero, sub_zero, CE]
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), g ε < CE p + 1 / 2 :=
    hcont.eventually (gt_mem_nhds (by rw [hg0]; linarith))
  have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < min (p.r0 / 4) (1 / 2) :=
    eventually_lt_nhds (lt_min (by linarith [p.hr0]) (by norm_num))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (h1.and h2)
  have := hball (y := δ / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  exact ⟨δ / 2, by linarith, this.2.le, this.1.le⟩


private lemma good_of_res' (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k)) (k : ℕ)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ min (p.r0 / 4) (1 / 2))
    (hCE : 2 * p.h * dMax p * (p.Estar + 1 + ε) / Real.sqrt (p.r0 / 2 - ε) + p.h ^ 2 * mZeta p ≤
      CE p + 1 / 2)
    (hBk : 0 < B k) (hL : 1 ≤ blockLen (B k)) (hLB : (blockLen (B k) : ℝ) ≤ (B k : ℝ))
    (hsm : (CE p + 1 / 2 + CR p) * ((blockLen (B k) : ℝ) / (B k : ℝ)) ≤ min p.r0 1 / 4)
    (ω : Ω)
    (hadm : ∀ σ : ℝ, ((⌊(B k : ℝ) * σ⌋₊ : ℕ) : ℕ∞) < (blockLen (B k) : ℕ∞) * blockExitIdx hyp k ω →
      actMeas hyp S k ω σ ∈ Adm p.CSig (p.Estar + 1 + ε) (p.r0 / 2 - ε) (p.r1 + 1 / 2 + ε))
    (hres : ∀ τ ∈ Icc (0 : ℝ) (Tstar p + 1),
      blockResidual hyp S c (fun _ => 1) (fun _ => 1) k ω τ ≤ min p.r0 1 / 16 ∧
      blockResidual hyp S c (fun x => x / 2) (fun x => x) k ω τ ≤ min p.r0 1 / 16) :
    ¬ ((blockLen (B k) : ℕ∞) * blockExitIdx hyp k ω ≤
        ((⌊(B k : ℝ) * Tstar p + (blockLen (B k) : ℝ)⌋₊ : ℕ) : ℕ∞)) ∧ ω ∈ boundEvent hyp k := by
  have hm0 : 0 < min p.r0 1 := lt_min p.hr0 zero_lt_one
  have hm1 : min p.r0 1 ≤ 1 := min_le_right _ _
  have hm2 : min p.r0 1 ≤ p.r0 := min_le_left _ _
  obtain ⟨hT0, hTE, hTR⟩ := Tstar_bds' p
  have hCE0 := CE_nonneg'' p
  have hCR0 := CR_nonneg'' p
  have hε2 : ε ≤ p.r0 / 4 := hε1.trans (min_le_left _ _)
  have hε3 : ε ≤ 1 / 2 := hε1.trans (min_le_right _ _)
  have hεr : 0 < p.r0 / 2 - ε := by linarith [p.hr0]
  have hBR : (0 : ℝ) < (B k : ℝ) := by exact_mod_cast hBk
  have hL0 : 0 < blockLen (B k) := hL
  set CE' := 2 * p.h * dMax p * (p.Estar + 1 + ε) / Real.sqrt (p.r0 / 2 - ε) +
    p.h ^ 2 * mZeta p with hCE'
  have hCE'0 : 0 ≤ CE' := by
    have := dMax_nonneg'' p; have := mZeta_nonneg'' p; have := p.hh; have := p.hE
    rw [hCE']; positivity
  have hdev := fun τ (hτ : τ ∈ Icc (0 : ℝ) (Tstar p + 1)) =>
    stopped_dev' F hyp S c k ε hε3 hεr hBk hL0 ω hadm τ hτ.1 _ (hres τ hτ).1 (hres τ hτ).2
  have hE0 := hyp.W0_norm k
  have hR0 := hyp.W0_risk k
  change fro (dev0 hyp k) ^ 2 ≤ p.Estar at hE0
  change p.r0 ≤ riskSigma (F k).C (dev0 hyp k) ∧ riskSigma (F k).C (dev0 hyp k) ≤ p.r1 at hR0
  -- Part A
  have hA : ¬ ((blockLen (B k) : ℕ∞) * blockExitIdx hyp k ω ≤
        ((⌊(B k : ℝ) * Tstar p + (blockLen (B k) : ℝ)⌋₊ : ℕ) : ℕ∞)) := by
    intro hA
    rcases exit_cases' hyp k ω with hb | ⟨b0, hb0, hnot⟩
    · rw [hb, ENat.mul_top (by exact_mod_cast hL0.ne')] at hA
      exact absurd hA (by simp)
    · rw [hb0] at hA
      have hA' : blockLen (B k) * b0 ≤ ⌊(B k : ℝ) * Tstar p + (blockLen (B k) : ℝ)⌋₊ := by
        exact_mod_cast hA
      have ht0 : ((blockLen (B k) * b0 : ℕ) : ℝ) ≤ (B k : ℝ) * Tstar p + (blockLen (B k) : ℝ) :=
        (Nat.cast_le.mpr hA').trans (Nat.floor_le (by positivity))
      push_cast at ht0
      have hLBd : (blockLen (B k) : ℝ) / (B k : ℝ) ≤ 1 := (div_le_one hBR).mpr hLB
      have hLBn : 0 ≤ (blockLen (B k) : ℝ) / (B k : ℝ) := by positivity
      set t0r : ℝ := (blockLen (B k) : ℝ) * (b0 : ℝ) / (B k : ℝ) with ht0r
      have hs_le : t0r ≤ Tstar p + (blockLen (B k) : ℝ) / (B k : ℝ) := by
        rw [ht0r, div_le_iff₀ hBR]
        have : (Tstar p + (blockLen (B k) : ℝ) / (B k : ℝ)) * (B k : ℝ) =
            (B k : ℝ) * Tstar p + (blockLen (B k) : ℝ) := by field_simp
        rw [this]; exact ht0
      have hs_eq : stopMacro (blockLen (B k)) (B k) (blockExitIdx hyp k ω) (Tstar p + 1) = t0r := by
        unfold stopMacro
        rw [hb0, if_neg (by simp)]
        simp only [ENat.toNat_coe]
        exact min_eq_right (by linarith)
      have hfl : ⌊(B k : ℝ) * t0r⌋₊ = b0 * blockLen (B k) := by
        have h1 : (B k : ℝ) * t0r = ((b0 * blockLen (B k) : ℕ) : ℝ) := by
          rw [ht0r]; push_cast; field_simp
        rw [h1, Nat.floor_natCast]
      obtain ⟨hdE, hdR⟩ := hdev (Tstar p + 1) ⟨by linarith, le_rfl⟩
      rw [hs_eq, hfl] at hdE hdR
      have hmem : errPath hyp k (b0 * blockLen (B k)) ω ∈ admA p (F k).C := by
        have hE1 : CE' * t0r ≤ (CE p + 1 / 2) * (Tstar p + (blockLen (B k) : ℝ) / (B k : ℝ)) := by
          have h0 : 0 ≤ t0r := by positivity
          calc CE' * t0r ≤ (CE p + 1 / 2) * t0r := mul_le_mul_of_nonneg_right hCE h0
            _ ≤ _ := mul_le_mul_of_nonneg_left hs_le (by linarith)
        have hR1 : CR p * t0r ≤ CR p * (Tstar p + (blockLen (B k) : ℝ) / (B k : ℝ)) :=
          mul_le_mul_of_nonneg_left hs_le hCR0
        have hcr : 0 ≤ CR p * ((blockLen (B k) : ℝ) / (B k : ℝ)) := mul_nonneg hCR0 hLBn
        have hE2 := (abs_le.mp hdE).2
        have hR2 := abs_le.mp hdR
        have hexp1 : (CE p + 1 / 2) * (Tstar p + (blockLen (B k) : ℝ) / (B k : ℝ)) =
            (CE p + 1 / 2) * Tstar p + (CE p + 1 / 2) * ((blockLen (B k) : ℝ) / (B k : ℝ)) := by
          ring
        have hexp2 : CR p * (Tstar p + (blockLen (B k) : ℝ) / (B k : ℝ)) =
            CR p * Tstar p + CR p * ((blockLen (B k) : ℝ) / (B k : ℝ)) := by ring
        have hexp3 : (CE p + 1 / 2 + CR p) * ((blockLen (B k) : ℝ) / (B k : ℝ)) =
            (CE p + 1 / 2) * ((blockLen (B k) : ℝ) / (B k : ℝ)) +
              CR p * ((blockLen (B k) : ℝ) / (B k : ℝ)) := by ring
        have hce : 0 ≤ (CE p + 1 / 2) * ((blockLen (B k) : ℝ) / (B k : ℝ)) :=
          mul_nonneg (by linarith) hLBn
        obtain ⟨hR0a, hR0b⟩ := hR0
        refine ⟨?_, ?_, ?_⟩
        · show p.r0 / 2 ≤ _
          linarith [hR2.1]
        · show _ ≤ p.r1 + 1 / 2
          linarith [hR2.2]
        · show fro _ ^ 2 ≤ p.Estar + 1
          linarith
      exact hnot hmem
  refine ⟨hA, ?_⟩
  -- Part B
  intro t ht
  have hτ0 : 0 ≤ (t : ℝ) / (B k : ℝ) := by positivity
  have hτT : (t : ℝ) / (B k : ℝ) ≤ Tstar p := by
    rw [div_le_iff₀ hBR]; linarith
  have hfl : ⌊(B k : ℝ) * ((t : ℝ) / (B k : ℝ))⌋₊ = t := by
    have h1 : (B k : ℝ) * ((t : ℝ) / (B k : ℝ)) = (t : ℝ) := by field_simp
    rw [h1]; exact Nat.floor_natCast t
  have hs_eq : stopMacro (blockLen (B k)) (B k) (blockExitIdx hyp k ω) ((t : ℝ) / (B k : ℝ)) =
      (t : ℝ) / (B k : ℝ) := by
    unfold stopMacro
    split_ifs with hbt
    · rfl
    · obtain ⟨b0, hb0, -⟩ : ∃ b0 : ℕ, blockExitIdx hyp k ω = (b0 : ℕ∞) ∧ True :=
        ⟨(blockExitIdx hyp k ω).toNat, (ENat.coe_toNat hbt).symm, trivial⟩
      rw [hb0] at hA hbt ⊢
      simp only [ENat.toNat_coe]
      apply min_eq_left
      rw [div_le_div_iff_of_pos_right hBR]
      have h1 : t ≤ ⌊(B k : ℝ) * Tstar p + (blockLen (B k) : ℝ)⌋₊ :=
        Nat.le_floor (by push_cast; linarith [(Nat.cast_nonneg (blockLen (B k)) : (0:ℝ) ≤ _)])
      have h2 : ⌊(B k : ℝ) * Tstar p + (blockLen (B k) : ℝ)⌋₊ < blockLen (B k) * b0 := by
        by_contra hcon
        rw [not_lt] at hcon
        exact hA (by exact_mod_cast hcon)
      have : (t : ℝ) ≤ ((blockLen (B k) * b0 : ℕ) : ℝ) := by exact_mod_cast (h1.trans h2.le)
      push_cast at this; exact this
  obtain ⟨hdE, hdR⟩ := hdev ((t : ℝ) / (B k : ℝ)) ⟨hτ0, by linarith⟩
  rw [hs_eq, hfl] at hdE hdR
  constructor
  · have : CE' * ((t : ℝ) / (B k : ℝ)) ≤ (CE p + 1 / 2) * Tstar p :=
      (mul_le_mul_of_nonneg_right hCE hτ0).trans (mul_le_mul_of_nonneg_left hτT (by linarith))
    refine hdE.trans ?_
    linarith
  · have : CR p * ((t : ℝ) / (B k : ℝ)) ≤ CR p * Tstar p :=
      mul_le_mul_of_nonneg_left hτT hCR0
    refine hdR.trans ?_
    linarith


private lemma core' (cert : Muon.External.GaussianOpNorm) (certOp : Muon.External.GaussianOpNormL6)
    (certP : Muon.External.GaussianPoincare) (certQ : Muon.External.GaussianQuadFormLp)
    (hB : Tendsto (fun k : ℕ => B k) atTop atTop)
    (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C)
    (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k)) :
    ∃ Bad : ℕ → Set Ω, Tendsto (fun k => P (Bad k)) atTop (𝓝 0) ∧
      ∀ᶠ k in atTop, ∀ ω, ω ∉ Bad k →
        ¬ ((blockLen (B k) : ℕ∞) * blockExitIdx hyp k ω ≤
          ((⌊(B k : ℝ) * Tstar p + (blockLen (B k) : ℝ)⌋₊ : ℕ) : ℕ∞)) ∧ ω ∈ boundEvent hyp k := by
  obtain ⟨ε, hε0, hε1, hCE⟩ := eps_choice' p
  have hm0 : 0 < min p.r0 1 := lt_min p.hr0 zero_lt_one
  set ρ0 : ℝ := min p.r0 1 / 16 with hρ0
  have hρ0pos : 0 < ρ0 := by rw [hρ0]; positivity
  obtain ⟨hT0, -, -⟩ := Tstar_bds' p
  have hT : 0 < Tstar p + 1 := by linarith
  have hCE0 := CE_nonneg'' p
  have hCR0 := CR_nonneg'' p
  have blk1 := lem_app_dyn_block cert certOp certP certQ F hyp S c hc (Tstar p + 1) hT
    (fun _ => 1) (fun _ => 1) ⟨1, fun x _ => by simp⟩ ⟨1, fun x _ => by simp⟩
  have blk2 := lem_app_dyn_block cert certOp certP certQ F hyp S c hc (Tstar p + 1) hT
    (fun x => x / 2) (fun x => x)
    ⟨p.CSig, fun x hx => by
      have hCs : 1 ≤ p.CSig := p.hC
      rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2]⟩
    ⟨p.CSig, fun x hx => by rw [abs_of_nonneg hx.1]; exact hx.2⟩
  have t1 := blk1.2.2 ρ0 hρ0pos
  have t2 := blk2.2.2 ρ0 hρ0pos
  refine ⟨fun k => {ω | ENNReal.ofReal ρ0 < ⨆ τ ∈ Icc (0 : ℝ) (Tstar p + 1),
        ENNReal.ofReal (blockResidual hyp S c (fun _ => 1) (fun _ => 1) k ω τ)} ∪
      {ω | ENNReal.ofReal ρ0 < ⨆ τ ∈ Icc (0 : ℝ) (Tstar p + 1),
        ENNReal.ofReal (blockResidual hyp S c (fun x => x / 2) (fun x => x) k ω τ)}, ?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using t1.add t2) (fun k => bot_le) (fun k => measure_union_le _ _)
  · have hden : 0 < CE p + 1 / 2 + CR p := by linarith
    have hδ : 0 < min p.r0 1 / 4 / (CE p + 1 / 2 + CR p) := by positivity
    filter_upwards [act_mem_adm' hB hyp S ε hε0, L_facts' hB _ hδ] with k hadm hLf ω hω
    obtain ⟨hBk, hL1, hLB, hLd⟩ := hLf
    have hsm : (CE p + 1 / 2 + CR p) * ((blockLen (B k) : ℝ) / (B k : ℝ)) ≤ min p.r0 1 / 4 := by
      calc _ ≤ (CE p + 1 / 2 + CR p) * (min p.r0 1 / 4 / (CE p + 1 / 2 + CR p)) :=
            mul_le_mul_of_nonneg_left hLd hden.le
        _ = _ := by field_simp
    have hres : ∀ τ ∈ Icc (0 : ℝ) (Tstar p + 1),
        blockResidual hyp S c (fun _ => 1) (fun _ => 1) k ω τ ≤ min p.r0 1 / 16 ∧
        blockResidual hyp S c (fun x => x / 2) (fun x => x) k ω τ ≤ min p.r0 1 / 16 := by
      intro τ hτ
      have h1 : ¬ (ENNReal.ofReal ρ0 < ⨆ τ ∈ Icc (0 : ℝ) (Tstar p + 1),
          ENNReal.ofReal (blockResidual hyp S c (fun _ => 1) (fun _ => 1) k ω τ)) :=
        fun h => hω (Or.inl h)
      have h2 : ¬ (ENNReal.ofReal ρ0 < ⨆ τ ∈ Icc (0 : ℝ) (Tstar p + 1),
          ENNReal.ofReal (blockResidual hyp S c (fun x => x / 2) (fun x => x) k ω τ)) :=
        fun h => hω (Or.inr h)
      rw [not_lt] at h1 h2
      exact ⟨(ENNReal.ofReal_le_ofReal_iff hρ0pos.le).mp
          ((le_iSup₂ (f := fun τ (_ : τ ∈ Icc (0 : ℝ) (Tstar p + 1)) => ENNReal.ofReal
            (blockResidual hyp S c (fun _ => 1) (fun _ => 1) k ω τ)) τ hτ).trans h1),
        (ENNReal.ofReal_le_ofReal_iff hρ0pos.le).mp
          ((le_iSup₂ (f := fun τ (_ : τ ∈ Icc (0 : ℝ) (Tstar p + 1)) => ENNReal.ofReal
            (blockResidual hyp S c (fun x => x / 2) (fun x => x) k ω τ)) τ hτ).trans h2)⟩
    exact good_of_res' F hyp S c k ε hε0 hε1 hCE hBk hL1 hLB hsm ω (hadm ω) hres

/-! ## `lem:app-dyn-interval` -/

/-- `lem:app-dyn-interval`(i), snapshot `cr-2026-10-23`. No exit before `T⋆`: `Pr(t_{b_c} ≤ BT⋆ + L) → 0`, with
`t_{b_c} = L · b_c` (`blockExitIdx`, `ℕ∞`-valued) and `L = blockLen B`. Routes through `lem_app_dyn_block`, hence the
four certificates and `hc`. Source, `section.tex` ll. 2286–2296, verbatim:
```latex
\begin{lemma}[No exit before $T_\star$]\label{lem:app-dyn-interval}
Let $b_c$ be as in \cref{lem:app-dyn-diffuse}. Then
$\Pr(t_{b_c}\le BT_\star+L)\to0$. Moreover, with probability tending to one,
for all $t\le BT_\star$,
\[
\abs{\norm{\Dt}_\F^2-\norm{\Delta_0}_\F^2}\le\frac14,\qquad
\abs{\cR(t)-\cR(0)}\le\frac{\min(r_0,1)}{4};
\]
in particular $t_{\rm stop}>BT_\star$ and $\chi^{\mathrm{act}}(\macrotime)\in\mathfrak M$ for
$\macrotime\le T_\star$.
\end{lemma}
```
-/
theorem lem_app_dyn_interval_i
    -- certificates of the cited results used by the proof (`Muon.External`), as in `lem_app_dyn_block`
    (cert : Muon.External.GaussianOpNorm) (certOp : Muon.External.GaussianOpNormL6)
    (certP : Muon.External.GaussianPoincare) (certQ : Muon.External.GaussianQuadFormLp)
    -- the sequence of dimensions with `B → ∞`, the frozen parameters, (H1)–(H4), the spectral data and coefficients
    (hB : Tendsto (fun k : ℕ => B k) atTop atTop)
    (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C)
    (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k)) :
    Tendsto (fun k : ℕ => P {ω | (blockLen (B k) : ℕ∞) * blockExitIdx hyp k ω ≤
      ((⌊(B k : ℝ) * Tstar p + (blockLen (B k) : ℝ)⌋₊ : ℕ) : ℕ∞)}) atTop (𝓝 0) := by
  obtain ⟨Bad, hBad, hev⟩ := core' cert certOp certP certQ hB F hyp S c hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBad
    (Filter.Eventually.of_forall fun k => bot_le) ?_
  filter_upwards [hev] with k hk
  refine measure_mono fun ω hω => ?_
  by_contra hnot
  exact (hk ω hnot).1 hω

/-- `lem:app-dyn-interval`(ii), snapshot `cr-2026-10-23`. Moreover, with probability tending to one, for all
`t ≤ BT⋆` the bounds `|‖Δ_t‖_F² − ‖Δ_0‖_F²| ≤ ¼` and `|𝓡(Δ_t) − 𝓡(Δ_0)| ≤ min(r₀,1)/4` hold (`boundEvent`).
Source as in `lem_app_dyn_interval_i`. -/
theorem lem_app_dyn_interval_ii
    (cert : Muon.External.GaussianOpNorm) (certOp : Muon.External.GaussianOpNormL6)
    (certP : Muon.External.GaussianPoincare) (certQ : Muon.External.GaussianQuadFormLp)
    (hB : Tendsto (fun k : ℕ => B k) atTop atTop)
    (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C)
    (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k)) :
    Tendsto (fun k : ℕ => P (boundEvent hyp k)) atTop (𝓝 1) := by
  letI : IsProbabilityMeasure P := prob_of_dynHyp hyp
  obtain ⟨Bad, hBad, hev⟩ := core' cert certOp certP certQ hB F hyp S c hc
  have hsub : Tendsto (fun k => 1 - P (Bad k)) atTop (𝓝 1) := by
    simpa using ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) hBad
      (Or.inl ENNReal.one_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hsub tendsto_const_nhds ?_ ?_
  · filter_upwards [hev] with k hk
    have hcov : (Set.univ : Set Ω) ⊆ Bad k ∪ boundEvent hyp k := by
      intro ω _
      by_cases h : ω ∈ Bad k
      · exact Or.inl h
      · exact Or.inr (hk ω h).2
    have h1 : 1 ≤ P (Bad k) + P (boundEvent hyp k) := by
      calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
        _ ≤ P (Bad k ∪ boundEvent hyp k) := measure_mono hcov
        _ ≤ _ := measure_union_le _ _
    exact tsub_le_iff_left.mpr h1
  · exact Filter.Eventually.of_forall fun k => prob_le_one

/-- `lem:app-dyn-interval`(iii), snapshot `cr-2026-10-23`. In particular, with probability tending to one,
`t_stop > BT⋆`, and `χ^act(τ) ∈ 𝔐` for all `τ ≤ T⋆` (`admMeasures p`). Source as in `lem_app_dyn_interval_i`. -/
theorem lem_app_dyn_interval_iii
    (cert : Muon.External.GaussianOpNorm) (certOp : Muon.External.GaussianOpNormL6)
    (certP : Muon.External.GaussianPoincare) (certQ : Muon.External.GaussianQuadFormLp)
    (hB : Tendsto (fun k : ℕ => B k) atTop atTop)
    (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C)
    (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k)) :
    Tendsto (fun k : ℕ => P {ω | ∀ t : ℕ, (t : ℝ) ≤ (B k : ℝ) * Tstar p → (t : ℕ∞) < stopTime hyp k ω})
        atTop (𝓝 1) ∧
    Tendsto (fun k : ℕ => P {ω | ∀ τ ∈ Icc (0 : ℝ) (Tstar p), actMeas hyp S k ω τ ∈ admMeasures p})
        atTop (𝓝 1) := by
  letI : IsProbabilityMeasure P := prob_of_dynHyp hyp
  have hb := lem_app_dyn_interval_ii cert certOp certP certQ hB F hyp S c hc
  constructor
  · exact tendsto_measure_one_of_subset (fun k => boundEvent hyp k)
      (fun k => {ω | ∀ t : ℕ, (t : ℝ) ≤ (B k : ℝ) * Tstar p →
        (t : ℕ∞) < stopTime hyp k ω}) hb (boundEvent_stop hyp)
  · exact tendsto_measure_one_of_subset (fun k => boundEvent hyp k)
      (fun k => {ω | ∀ τ ∈ Icc (0 : ℝ) (Tstar p),
        actMeas hyp S k ω τ ∈ admMeasures p}) hb (boundEvent_adm F hyp S)

/-! ## `thm:app-dyn-main` -/

/-- `thm:app-dyn-main`(i), snapshot `cr-2026-10-23`. With probability tending to one, `t_stop > BT⋆`,
`inf_{t≤BT⋆} 𝓡(Δ_t) ≥ r₀/2` and `sup_{t≤BT⋆} ‖Δ_t‖_F² ≤ E⋆+1` (`mainEvent`). Source, `section.tex` ll. 336–367,
verbatim:
```latex
\begin{theorem}[Dynamical comparison]\label{thm:app-dyn-main}
Fix $\macrostep>0$, $\ridge>0$, $\bmom\in[0,1)$, $\gamma_\star<\infty$,
$C_\Sigma\ge1$, $E_\star<\infty$, $c_M<\infty$ and $0<r_0\le r_1<\infty$.
Along a sequence of dimensions with $B\to\infty$ assume:
\begin{enumerate}[label=(H\arabic*)]
\item \label{hyp:app-dyn-data} \cref{assum:data-target,assum:proportional-regime}
hold with deterministic covariances, $\max(\Nin,\Nout)\le\gamma_\star B$
and $\norm{\Sigmain},\norm{\Sigmaout}\le C_\Sigma$;
\item \label{hyp:app-dyn-algorithm} the algorithm of
\cref{def:app-setup-algorithm} is run with momentum $\bmom$, normalized
ridge $\ridge$ and step $\lr_t=\macrostep/B$;
\item \label{hyp:app-dyn-initial} $W_0$ is deterministic,
$\norm{\Delta_0}_\F^2\le E_\star$, $r_0\le\cR(0)\le r_1$, and
$\norm{\widehat A_0}\to0$;
\item \label{hyp:app-dyn-buffer} the initial buffer $M^\circ_{-1}$ is
independent of all batches and $\EE\norm{M^\circ_{-1}}_\F^2\le c_MB$.
\end{enumerate}
Let $T_\star$ be given by \cref{eqn:app-dyn-Tstar} and let $(\fQ_{ij})$ be
the solution of \cref{eqn:app-dyn-ode} of \cref{prop:app-dyn-ode}. Then the
following hold.
\begin{enumerate}[label=(\roman*)]
\item With probability tending to one, $t_{\rm stop}>BT_\star$,
$\inf_{t\le BT_\star}\cR(t)\ge r_0/2$ and
$\sup_{t\le BT_\star}\norm{\Dt}_\F^2\le E_\star+1$.
\item $\sup_{\macrotime\le T_\star}\norm{\chi^{\mathrm{act}}(\macrotime)-\chi^{\mathrm{ode}}(\macrotime)}_\BL\to0$
in probability.
\item $\sup_{\macrotime\le T_\star}\norm{\mu\lambda\,(\chi^{\mathrm{act}}(\macrotime)-\chi^{\mathrm{ode}}(\macrotime))}_\BL\to0$
and $\sup_{\macrotime\le T_\star}\abs{\cR(\lfloor B\macrotime\rfloor)-\fRisk(\macrotime)}\to0$
in probability.
\item On the event of (i), $\sup_{t\le BT_\star}\norm{\Ahat}\to0$ in probability.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_dyn_main_i
    (cert : Muon.External.GaussianOpNorm) (certOp : Muon.External.GaussianOpNormL6)
    (certP : Muon.External.GaussianPoincare) (certQ : Muon.External.GaussianQuadFormLp)
    -- (H1)–(H4) along a sequence of dimensions with `B → ∞`
    (hB : Tendsto (fun k : ℕ => B k) atTop atTop)
    (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C)
    (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k)) :
    Tendsto (fun k : ℕ => P (mainEvent hyp k)) atTop (𝓝 1) := by
  letI : IsProbabilityMeasure P := prob_of_dynHyp hyp
  have hb := lem_app_dyn_interval_ii cert certOp certP certQ hB F hyp S c hc
  refine tendsto_measure_one_of_subset (fun k => boundEvent hyp k)
    (fun k => mainEvent hyp k) hb ?_
  intro k ω hω t ht
  have hstop := boundEvent_stop hyp k hω t ht
  obtain ⟨hE, hR⟩ := hω t ht
  have hE0 := hyp.W0_norm k
  change fro (dev0 hyp k) ^ 2 ≤ p.Estar at hE0
  have hR0 := (hyp.W0_risk k).1
  change p.r0 ≤ riskSigma (F k).C (dev0 hyp k) at hR0
  have hEupper : fro (errPath hyp k t ω) ^ 2 - fro (dev0 hyp k) ^ 2 ≤ 1 / 4 :=
    (le_abs_self _).trans hE
  have hRlower : -(min p.r0 1 / 4) ≤
      riskSigma (F k).C (errPath hyp k t ω) - riskSigma (F k).C (dev0 hyp k) :=
    neg_le_of_abs_le hR
  have hmin : min p.r0 1 ≤ p.r0 := min_le_left _ _
  exact ⟨hstop, by nlinarith [p.hr0], by nlinarith⟩

/-! ### Private helpers for `thm:app-dyn-main`(ii) -/

private lemma mii_floor_ii (G : ℕ → ℝ) (Bn : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun σ => G ⌊(Bn : ℝ) * σ⌋₊) volume a b := by
  have hmeas : Measurable (fun σ : ℝ => G ⌊(Bn : ℝ) * σ⌋₊) :=
    (measurable_from_nat (f := G)).comp (measurable_const_mul (Bn : ℝ)).nat_floor
  set N := ⌊(Bn : ℝ) * max a b⌋₊ with hN
  set M := ∑ t ∈ Finset.range (N + 1), |G t| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun t _ => abs_nonneg _
  refine (intervalIntegrable_const (c := M)).mono_fun hmeas.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_uIoc fun σ hσ => ?_
  have hσ' : σ ≤ max a b := hσ.2
  have ht : ⌊(Bn : ℝ) * σ⌋₊ ≤ N :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hσ' (Nat.cast_nonneg _))
  have hmem : ⌊(Bn : ℝ) * σ⌋₊ ∈ Finset.range (N + 1) :=
    Finset.mem_range.2 (Nat.lt_succ_of_le ht)
  have h1 : |G ⌊(Bn : ℝ) * σ⌋₊| ≤ M :=
    Finset.single_le_sum (f := fun t => |G t|) (fun t _ => abs_nonneg _) hmem
  simp only [Real.norm_eq_abs, abs_of_nonneg hM0]
  exact h1

private lemma mii_atoms {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (Cs : ℝ)
    (hout : opNorm C.Sout ≤ Cs) (hin : opNorm C.Sin ≤ Cs) (i : Fin m) (j : Fin n) :
    (S.μ i, S.lam j) ∈ specRect Cs :=
  ⟨⟨μ_nonneg S i, (le_abs_self _).trans ((abs_eig_le_opNorm C.Sout (fun a => S.uOut a i) (S.μ i)
      (sum_col_sq_eq_one S.uOut S.huOut i) (S.eigOut i)).trans hout)⟩,
   ⟨lam_nonneg S j, (le_abs_self _).trans ((abs_eig_le_opNorm C.Sin (fun a => S.vIn a j)
      (S.lam j) (sum_col_sq_eq_one S.vIn S.hvIn j) (S.eigIn j)).trans hin)⟩⟩

private lemma mii_atom_integrable {a b : ℕ} (mu : Fin a → ℝ) (lam : Fin b → ℝ)
    (q : Fin a → Fin b → ℝ) (f : ℝ × ℝ → ℝ) :
    Integrable f (atomMeasure mu lam q) := by
  unfold atomMeasure
  exact integrable_finsetSum_measure.mpr fun i _ =>
    integrable_finsetSum_measure.mpr fun j _ =>
      (integrable_dirac (f := f) (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma mii_field_atom {m n : ℕ} (h : ℝ) (d : ℝ × ℝ → ℝ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (w u : Fin m → Fin n → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hu : ∀ i j, 0 ≤ u i j) (φ : ℝ × ℝ → ℝ) :
    fieldOp h d (atomMeasure μ lam u) (atomMeasure μ lam w) φ =
      ∑ i, ∑ j, (if 0 < riskOf (atomMeasure μ lam w) then
        -(2 * h / Real.sqrt (riskOf (atomMeasure μ lam w))) * (w i j * d (μ i, lam j)) +
          h ^ 2 * u i j
        else 0) * φ (μ i, lam j) := by
  unfold fieldOp
  by_cases hr : 0 < riskOf (atomMeasure μ lam w)
  · rw [if_pos hr, atom_integral μ lam w hw (fun x => φ x * d x), atom_integral μ lam u hu φ,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos hr]
    ring
  · rw [if_neg hr]
    simp [hr]

private lemma mii_stop (L Bn : ℕ) (b : ℕ∞) (T : ℝ) (hBn : 0 < Bn)
    (h : ¬ ((L : ℕ∞) * b ≤ ((⌊(Bn : ℝ) * T + (L : ℝ)⌋₊ : ℕ) : ℕ∞))) (τ : ℝ) (hτ : τ ≤ T) :
    stopMacro L Bn b τ = τ := by
  unfold stopMacro
  split_ifs with hb
  · rfl
  · obtain ⟨b0, rfl⟩ := ENat.ne_top_iff_exists.mp hb
    simp only [ENat.toNat_coe]
    apply min_eq_left
    have h' : ⌊(Bn : ℝ) * T + L⌋₊ < L * b0 := by
      by_contra hc
      push_neg at hc
      exact h (by exact_mod_cast hc)
    have hBR : (0 : ℝ) < Bn := by exact_mod_cast hBn
    have hlt : (Bn : ℝ) * T + L < ((L * b0 : ℕ) : ℝ) := Nat.lt_of_floor_lt h'
    push_cast at hlt
    rw [le_div_iff₀ hBR]
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hτ hBR.le]

private lemma mii_grid {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Cs δ : ℝ) (hCs : 0 ≤ Cs)
    (hδ : 0 < δ) (hat : ∀ i j, (μ i, lam j) ∈ specRect Cs) (ρ : Fin m → Fin n → ℝ) (η0 A : ℝ)
    (hA : ∑ i, ∑ j, |ρ i j| ≤ A)
    (hcell : ∀ r ∈ Finset.range (⌊Cs / δ⌋₊ + 1), ∀ s ∈ Finset.range (⌊Cs / δ⌋₊ + 1),
      |∑ i, ∑ j, ρ i j * tensorFG (fun y : ℝ => if ⌊y / δ⌋₊ = r then (1 : ℝ) else 0)
        (fun y : ℝ => if ⌊y / δ⌋₊ = s then (1 : ℝ) else 0) (μ i, lam j)| ≤ η0)
    (φ : ℝ × ℝ → ℝ) (hφ : φ ∈ blTest Cs) :
    |∑ i, ∑ j, ρ i j * φ (μ i, lam j)| ≤ ((⌊Cs / δ⌋₊ + 1 : ℕ) : ℝ) ^ 2 * η0 + 2 * δ * A := by
  set N := ⌊Cs / δ⌋₊ with hN
  set R := Finset.range (N + 1) with hR
  have hgr : ∀ y ∈ Icc (0 : ℝ) Cs, ⌊y / δ⌋₊ ∈ R ∧ δ * (⌊y / δ⌋₊ : ℝ) ∈ Icc (0 : ℝ) Cs ∧
      |y - δ * (⌊y / δ⌋₊ : ℝ)| ≤ δ := by
    intro y hy
    have hyd : 0 ≤ y / δ := div_nonneg hy.1 hδ.le
    have h1 : (⌊y / δ⌋₊ : ℝ) ≤ y / δ := Nat.floor_le hyd
    have h2 : y / δ < ⌊y / δ⌋₊ + 1 := Nat.lt_floor_add_one _
    have h1' : δ * ⌊y / δ⌋₊ ≤ y := by rw [le_div_iff₀ hδ] at h1; linarith
    have h2' : y < δ * ⌊y / δ⌋₊ + δ := by rw [div_lt_iff₀ hδ] at h2; linarith
    refine ⟨Finset.mem_range.2 (Nat.lt_succ_of_le
      (Nat.floor_mono (div_le_div_of_nonneg_right hy.2 hδ.le))),
      ⟨by positivity, h1'.trans hy.2⟩, ?_⟩
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hRK : ∀ r ∈ R, δ * (r : ℝ) ∈ Icc (0 : ℝ) Cs := by
    intro r hr
    have hr' : r ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    have h1 : (N : ℝ) ≤ Cs / δ := Nat.floor_le (div_nonneg hCs hδ.le)
    have h2 : (r : ℝ) ≤ Cs / δ := (Nat.cast_le.2 hr').trans h1
    refine ⟨by positivity, ?_⟩
    rw [le_div_iff₀ hδ] at h2
    linarith
  set fr : ℕ → ℝ → ℝ := fun r y => if ⌊y / δ⌋₊ = r then (1 : ℝ) else 0 with hfr
  have hcellsum : ∀ i j, ∑ r ∈ R, ∑ s ∈ R, φ (δ * r, δ * s) * tensorFG (fr r) (fr s) (μ i, lam j) =
      φ (δ * ⌊μ i / δ⌋₊, δ * ⌊lam j / δ⌋₊) := by
    intro i j
    have hi := (hgr (μ i) (hat i j).1).1
    have hj := (hgr (lam j) (hat i j).2).1
    simp only [tensorFG, hfr, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, hi, hj, if_true]
  have hsplit : ∑ i, ∑ j, ρ i j * φ (δ * ⌊μ i / δ⌋₊, δ * ⌊lam j / δ⌋₊) =
      ∑ r ∈ R, ∑ s ∈ R, φ (δ * r, δ * s) *
        ∑ i, ∑ j, ρ i j * tensorFG (fr r) (fr s) (μ i, lam j) := by
    calc _ = ∑ i, ∑ j, ∑ r ∈ R, ∑ s ∈ R,
          ρ i j * (φ (δ * r, δ * s) * tensorFG (fr r) (fr s) (μ i, lam j)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← hcellsum i j, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, ∑ r ∈ R, ∑ s ∈ R, ∑ j,
          ρ i j * (φ (δ * r, δ * s) * tensorFG (fr r) (fr s) (μ i, lam j)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ r ∈ R, ∑ s ∈ R, ∑ i, ∑ j,
          ρ i j * (φ (δ * r, δ * s) * tensorFG (fr r) (fr s) (μ i, lam j)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_comm]
      _ = _ := by
          refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  have hpart1 : |∑ i, ∑ j, ρ i j * φ (δ * ⌊μ i / δ⌋₊, δ * ⌊lam j / δ⌋₊)| ≤
      ((N + 1 : ℕ) : ℝ) ^ 2 * η0 := by
    rw [hsplit]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ r ∈ R, |∑ s ∈ R, φ (δ * r, δ * s) *
          ∑ i, ∑ j, ρ i j * tensorFG (fr r) (fr s) (μ i, lam j)|
        ≤ ∑ r ∈ R, ∑ s ∈ R, η0 := by
          refine Finset.sum_le_sum fun r hr => (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine Finset.sum_le_sum fun s hs => ?_
          rw [abs_mul]
          have h1 : |φ (δ * r, δ * s)| ≤ 1 := hφ.1 _ ⟨hRK r hr, hRK s hs⟩
          have h2 := hcell r hr s hs
          exact (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one).trans (by rw [one_mul])
      _ = ((N + 1 : ℕ) : ℝ) ^ 2 * η0 := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hR]
          push_cast
          ring
  have hpart2 : |∑ i, ∑ j, ρ i j * φ (μ i, lam j) -
      ∑ i, ∑ j, ρ i j * φ (δ * ⌊μ i / δ⌋₊, δ * ⌊lam j / δ⌋₊)| ≤ 2 * δ * A := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ j, ρ i j * φ (μ i, lam j) - ∑ j, ρ i j * φ (δ * ⌊μ i / δ⌋₊, δ * ⌊lam j / δ⌋₊)|
        ≤ ∑ i, ∑ j, |ρ i j| * (2 * δ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [← mul_sub, abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          obtain ⟨_, hgi, hdi⟩ := hgr (μ i) (hat i j).1
          obtain ⟨_, hgj, hdj⟩ := hgr (lam j) (hat i j).2
          refine (hφ.2 _ (hat i j) _ ⟨hgi, hgj⟩).trans ?_
          unfold l1
          simp only
          linarith
      _ = 2 * δ * ∑ i, ∑ j, |ρ i j| := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ 2 * δ * A := mul_le_mul_of_nonneg_left hA (by positivity)
  calc |∑ i, ∑ j, ρ i j * φ (μ i, lam j)|
      = |∑ i, ∑ j, ρ i j * φ (δ * ⌊μ i / δ⌋₊, δ * ⌊lam j / δ⌋₊) +
          (∑ i, ∑ j, ρ i j * φ (μ i, lam j) -
            ∑ i, ∑ j, ρ i j * φ (δ * ⌊μ i / δ⌋₊, δ * ⌊lam j / δ⌋₊))| := by
        rw [add_sub_cancel]
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hpart1 hpart2)

private lemma mii_kappa_sum {m n : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    {Bn : ℕ} (c : DynCoeff p S Bn) (hout : opNorm C.Sout ≤ p.CSig) (hin : opNorm C.Sin ≤ p.CSig)
    (D : Mat m n) (hD : specMeasure S D ∈ admMeasures p) :
    ∑ i, ∑ j, |(if 0 < riskOf (specMeasure S D) then
        -(2 * p.h / Real.sqrt (riskOf (specMeasure S D))) * (modeQ S D i j * c.d (S.μ i, S.lam j)) +
          p.h ^ 2 * (c.v i j / (Bn : ℝ))
        else 0)| ≤
      2 * p.h / Real.sqrt (p.r0 / 2) * dMax p * (p.Estar + 1) + p.h ^ 2 * mZeta p := by
  have hR : p.r0 / 2 ≤ riskOf (specMeasure S D) := hD.2.2.2.1
  have hr0 : 0 < p.r0 / 2 := by linarith [p.hr0]
  have hRpos : 0 < riskOf (specMeasure S D) := hr0.trans_le hR
  have hh := p.hh
  simp only [if_pos hRpos]
  set a := 2 * p.h / Real.sqrt (riskOf (specMeasure S D)) with ha
  set a0 := 2 * p.h / Real.sqrt (p.r0 / 2) with ha0
  have ha0' : 0 ≤ a := by rw [ha]; positivity
  have haa : a ≤ a0 :=
    div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 hr0) (Real.sqrt_le_sqrt hR)
  have hv : ∀ i j, 0 ≤ c.v i j / (Bn : ℝ) := fun i j =>
    div_nonneg (c.v_nonneg i j) (Nat.cast_nonneg _)
  have hq : ∀ i j, 0 ≤ modeQ S D i j := fun i j => sq_nonneg _
  have hdm := dMax_nonneg'' p
  have hterm : ∀ i j, |-a * (modeQ S D i j * c.d (S.μ i, S.lam j)) + p.h ^ 2 * (c.v i j / (Bn : ℝ))| ≤
      a0 * dMax p * modeQ S D i j + p.h ^ 2 * (c.v i j / (Bn : ℝ)) := by
    intro i j
    have hK := mii_atoms S p.CSig hout hin i j
    have hd0 := c.d_nonneg _ hK
    have hd1 := c.d_le _ hK
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_neg, abs_of_nonneg ha0', abs_of_nonneg (mul_nonneg (hq i j) hd0),
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (hv i j))]
    have h1 : modeQ S D i j * c.d (S.μ i, S.lam j) ≤ modeQ S D i j * dMax p :=
      mul_le_mul_of_nonneg_left hd1 (hq i j)
    have h2 : a * (modeQ S D i j * c.d (S.μ i, S.lam j)) ≤ a0 * (modeQ S D i j * dMax p) :=
      mul_le_mul haa h1 (mul_nonneg (hq i j) hd0) (ha0'.trans haa)
    nlinarith
  have hmass : ∑ i, ∑ j, modeQ S D i j ≤ p.Estar + 1 := by
    have h := hD.2.2.1
    rwa [show specMeasure S D = atomMeasure S.μ S.lam (modeQ S D) from rfl,
      atom_mass _ _ _ hq] at h
  have hzeta : ∑ i, ∑ j, c.v i j / (Bn : ℝ) ≤ mZeta p := by
    have h := c.ζ_mass
    rwa [c.ζ_eq, atom_mass _ _ _ hv] at h
  calc _ ≤ ∑ i, ∑ j, (a0 * dMax p * modeQ S D i j + p.h ^ 2 * (c.v i j / (Bn : ℝ))) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = a0 * dMax p * ∑ i, ∑ j, modeQ S D i j + p.h ^ 2 * ∑ i, ∑ j, c.v i j / (Bn : ℝ) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ a0 * dMax p * (p.Estar + 1) + p.h ^ 2 * mZeta p := by
        have : 0 ≤ a0 * dMax p := by rw [ha0]; positivity
        gcongr

private lemma mii_rep {m n : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    {Bn : ℕ} (c : DynCoeff p S Bn) (hout : opNorm C.Sout ≤ p.CSig) (hin : opNorm C.Sin ≤ p.CSig)
    (Δ : ℕ → Mat m n) (τ : ℝ) (hτ : 0 ≤ τ)
    (hadm : ∀ σ ∈ Icc 0 τ, actMeasure S Bn Δ σ ∈ admMeasures p) :
    ∃ ρ : Fin m → Fin n → ℝ,
      (∀ φ : ℝ × ℝ → ℝ, (∫ x, φ x ∂(actMeasure S Bn Δ τ)) - (∫ x, φ x ∂(actMeasure S Bn Δ 0)) -
          (∫ σ in (0 : ℝ)..τ, fieldOp p.h c.d c.ζ (actMeasure S Bn Δ σ) φ) =
        ∑ i, ∑ j, ρ i j * φ (S.μ i, S.lam j)) ∧
      ∑ i, ∑ j, |ρ i j| ≤ 2 * (p.Estar + 1) +
        τ * (2 * p.h / Real.sqrt (p.r0 / 2) * dMax p * (p.Estar + 1) + p.h ^ 2 * mZeta p) := by
  set κ : Fin m → Fin n → ℕ → ℝ := fun i j t =>
    if 0 < riskOf (specMeasure S (Δ t)) then
      -(2 * p.h / Real.sqrt (riskOf (specMeasure S (Δ t)))) *
          (modeQ S (Δ t) i j * c.d (S.μ i, S.lam j)) + p.h ^ 2 * (c.v i j / (Bn : ℝ))
    else 0 with hκ
  have hv : ∀ i j, 0 ≤ c.v i j / (Bn : ℝ) := fun i j =>
    div_nonneg (c.v_nonneg i j) (Nat.cast_nonneg _)
  have hq : ∀ (D : Mat m n) i j, 0 ≤ modeQ S D i j := fun D i j => sq_nonneg _
  have hfield : ∀ (t : ℕ) (φ : ℝ × ℝ → ℝ), fieldOp p.h c.d c.ζ (specMeasure S (Δ t)) φ =
      ∑ i, ∑ j, κ i j t * φ (S.μ i, S.lam j) := by
    intro t φ
    rw [c.ζ_eq]
    exact mii_field_atom p.h c.d S.μ S.lam (modeQ S (Δ t)) _ (hq (Δ t)) hv φ
  set Kk := 2 * p.h / Real.sqrt (p.r0 / 2) * dMax p * (p.Estar + 1) + p.h ^ 2 * mZeta p with hKk
  refine ⟨fun i j => modeQ S (Δ ⌊(Bn : ℝ) * τ⌋₊) i j - modeQ S (Δ ⌊(Bn : ℝ) * 0⌋₊) i j -
      ∫ σ in (0 : ℝ)..τ, κ i j ⌊(Bn : ℝ) * σ⌋₊, ?_, ?_⟩
  · intro φ
    have hI : ∫ σ in (0 : ℝ)..τ, fieldOp p.h c.d c.ζ (actMeasure S Bn Δ σ) φ =
        ∑ i, ∑ j, (∫ σ in (0 : ℝ)..τ, κ i j ⌊(Bn : ℝ) * σ⌋₊) * φ (S.μ i, S.lam j) := by
      simp only [actMeasure, hfield]
      rw [intervalIntegral.integral_finsetSum fun i _ =>
        mii_floor_ii (fun t => ∑ j, κ i j t * φ (S.μ i, S.lam j)) Bn 0 τ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_finsetSum fun j _ =>
        mii_floor_ii (fun t => κ i j t * φ (S.μ i, S.lam j)) Bn 0 τ]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [intervalIntegral.integral_mul_const]
    rw [hI]
    simp only [actMeasure, specMeasure]
    rw [atom_integral _ _ _ (hq _), atom_integral _ _ _ (hq _), ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · have hw : ∀ σ ∈ Icc 0 τ, ∑ i, ∑ j, |modeQ S (Δ ⌊(Bn : ℝ) * σ⌋₊) i j| ≤ p.Estar + 1 := by
      intro σ hσ
      have h := (hadm σ hσ).2.2.1
      simp only [abs_of_nonneg (hq _ _ _)]
      rwa [show actMeasure S Bn Δ σ = atomMeasure S.μ S.lam (modeQ S (Δ ⌊(Bn : ℝ) * σ⌋₊)) from rfl,
        atom_mass _ _ _ (hq _)] at h
    have hk : ∑ i, ∑ j, |∫ σ in (0 : ℝ)..τ, κ i j ⌊(Bn : ℝ) * σ⌋₊| ≤ τ * Kk := by
      calc ∑ i, ∑ j, |∫ σ in (0 : ℝ)..τ, κ i j ⌊(Bn : ℝ) * σ⌋₊|
          ≤ ∑ i, ∑ j, ∫ σ in (0 : ℝ)..τ, |κ i j ⌊(Bn : ℝ) * σ⌋₊| :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              intervalIntegral.abs_integral_le_integral_abs hτ
        _ = ∫ σ in (0 : ℝ)..τ, ∑ i, ∑ j, |κ i j ⌊(Bn : ℝ) * σ⌋₊| := by
            rw [intervalIntegral.integral_finsetSum fun i _ =>
              mii_floor_ii (fun t => ∑ j, |κ i j t|) Bn 0 τ]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [intervalIntegral.integral_finsetSum fun j _ =>
              mii_floor_ii (fun t => |κ i j t|) Bn 0 τ]
        _ ≤ τ * Kk := by
            have hpt : ∀ σ ∈ Set.uIoc (0 : ℝ) τ, ‖∑ i, ∑ j, |κ i j ⌊(Bn : ℝ) * σ⌋₊|‖ ≤ Kk := by
              intro σ hσ
              rw [uIoc_of_le hτ] at hσ
              have hσ' : σ ∈ Icc 0 τ := ⟨hσ.1.le, hσ.2⟩
              rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ =>
                Finset.sum_nonneg fun j _ => abs_nonneg _)]
              exact mii_kappa_sum p S c hout hin _ (hadm σ hσ')
            have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
            rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hτ] at h
            linarith [le_abs_self (∫ σ in (0 : ℝ)..τ, ∑ i, ∑ j, |κ i j ⌊(Bn : ℝ) * σ⌋₊|)]
    have h1 := hw τ ⟨hτ, le_rfl⟩
    have h0 := hw 0 ⟨le_rfl, hτ⟩
    calc ∑ i, ∑ j, |modeQ S (Δ ⌊(Bn : ℝ) * τ⌋₊) i j - modeQ S (Δ ⌊(Bn : ℝ) * 0⌋₊) i j -
          ∫ σ in (0 : ℝ)..τ, κ i j ⌊(Bn : ℝ) * σ⌋₊|
        ≤ ∑ i, ∑ j, (|modeQ S (Δ ⌊(Bn : ℝ) * τ⌋₊) i j| + |modeQ S (Δ ⌊(Bn : ℝ) * 0⌋₊) i j| +
          |∫ σ in (0 : ℝ)..τ, κ i j ⌊(Bn : ℝ) * σ⌋₊|) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ = ∑ i, ∑ j, |modeQ S (Δ ⌊(Bn : ℝ) * τ⌋₊) i j| +
          ∑ i, ∑ j, |modeQ S (Δ ⌊(Bn : ℝ) * 0⌋₊) i j| +
          ∑ i, ∑ j, |∫ σ in (0 : ℝ)..τ, κ i j ⌊(Bn : ℝ) * σ⌋₊| := by
          simp only [Finset.sum_add_distrib]
      _ ≤ 2 * (p.Estar + 1) + τ * Kk := by linarith

private lemma mii_ae_K {Cs : ℝ} {χ : Measure (ℝ × ℝ)} (hK : χ (specRect Cs)ᶜ = 0) :
    ∀ᵐ x ∂χ, x ∈ specRect Cs := by
  rw [ae_iff]
  exact hK

private lemma mii_test_abs_le {Cs : ℝ} (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hμ : μ (specRect Cs)ᶜ = 0) (φ : ℝ × ℝ → ℝ) (hφ : ∀ x ∈ specRect Cs, |φ x| ≤ 1) :
    |∫ x, φ x ∂μ| ≤ μ.real univ := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := φ) (C := 1)
    ((mii_ae_K hμ).mono fun x hx => by rw [Real.norm_eq_abs]; exact hφ x hx)
  simpa only [Real.norm_eq_abs, one_mul] using h

private lemma mii_bl_nonneg (Cs : ℝ) (μ ν : Measure (ℝ × ℝ)) : 0 ≤ blDist Cs μ ν := by
  unfold blDist blNorm
  exact Real.sSup_nonneg (by rintro _ ⟨φ, _, rfl⟩; exact abs_nonneg _)

private lemma mii_bl_le_of {Cs A : ℝ} (μ ν : Measure (ℝ × ℝ)) (hA : 0 ≤ A)
    (h : ∀ φ ∈ blTest Cs, |∫ x, φ x ∂μ - ∫ x, φ x ∂ν| ≤ A) : blDist Cs μ ν ≤ A := by
  unfold blDist blNorm
  exact Real.sSup_le (by rintro _ ⟨φ, hφ, rfl⟩; exact h φ hφ) hA

private lemma mii_bl_le_mass {Cs : ℝ} (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0) :
    blDist Cs μ ν ≤ μ.real univ + ν.real univ :=
  mii_bl_le_of μ ν (add_nonneg measureReal_nonneg measureReal_nonneg) fun φ hφ =>
    (abs_sub _ _).trans (add_le_add (mii_test_abs_le μ hμ φ hφ.1)
      (mii_test_abs_le ν hν φ hφ.1))

private lemma mii_integral_congr_K {Cs : ℝ} {f g : ℝ × ℝ → ℝ}
    (hfg : ∀ x ∈ specRect Cs, f x = g x) (μ : Measure (ℝ × ℝ)) (hμ : μ (specRect Cs)ᶜ = 0) :
    ∫ x, f x ∂μ = ∫ x, g x ∂μ :=
  integral_congr_ae ((mii_ae_K hμ).mono fun x hx => hfg x hx)

private lemma mii_local_lip_cont {Cs L : ℝ} {g : ℝ × ℝ → ℝ} (hL : 0 ≤ L)
    (hl : ∀ x ∈ specRect Cs, ∀ y ∈ specRect Cs, |g x - g y| ≤ L * l1 x y) :
    ContinuousOn g (specRect Cs) := by
  have h : LipschitzOnWith ⟨2 * L, by positivity⟩ g (specRect Cs) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Real.dist_eq]
    have hd : l1 x y ≤ 2 * dist x y := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      unfold l1
      linarith [le_max_left |x.1 - y.1| |x.2 - y.2|,
        le_max_right |x.1 - y.1| |x.2 - y.2|]
    exact (hl x hx y hy).trans (by
      change L * l1 x y ≤ (2 * L) * dist x y
      nlinarith [mul_le_mul_of_nonneg_left hd hL])
  exact h.continuousOn

private lemma mii_test_ext {Cs : ℝ} (hCs : 0 ≤ Cs) (φ : ℝ × ℝ → ℝ) (hφ : φ ∈ blTest Cs) :
    ∃ ψ : ℝ × ℝ → ℝ, Continuous ψ ∧ (∀ x, |ψ x| ≤ 1) ∧ ψ ∈ blTest Cs ∧
      ∀ x ∈ specRect Cs, ψ x = φ x := by
  let pr : ℝ × ℝ → ℝ × ℝ := fun x => ((projIcc 0 Cs hCs x.1 : ℝ), (projIcc 0 Cs hCs x.2 : ℝ))
  have hpr : ∀ x, pr x ∈ specRect Cs := fun x =>
    ⟨(projIcc 0 Cs hCs x.1).2, (projIcc 0 Cs hCs x.2).2⟩
  have hprc : Continuous pr :=
    (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
  have hprK : ∀ x ∈ specRect Cs, pr x = x := by
    intro x hx
    simp only [pr, projIcc_of_mem hCs hx.1, projIcc_of_mem hCs hx.2]
  have hφc : ContinuousOn φ (specRect Cs) :=
    mii_local_lip_cont zero_le_one (fun x hx y hy => by
      simpa only [one_mul] using hφ.2 x hx y hy)
  refine ⟨fun x => φ (pr x), hφc.comp_continuous hprc hpr, fun x => hφ.1 _ (hpr x), ?_, ?_⟩
  · refine ⟨fun x hx => by simp only [hprK x hx]; exact hφ.1 x hx, fun x hx y hy => ?_⟩
    simp only [hprK x hx, hprK y hy]
    exact hφ.2 x hx y hy
  · intro x hx
    simp only [hprK x hx]

/-- Gronwall in exponentially weighted sup form. -/
private lemma mii_exp_gronwall {T CF A : ℝ} (hT : 0 ≤ T) (hCF : 0 ≤ CF) (hA : 0 ≤ A)
    (D : ℝ → ℝ) (hDb : ∃ M, ∀ τ ∈ Icc 0 T, D τ ≤ M)
    (hD : ∀ M : ℝ, 0 ≤ M → (∀ σ ∈ Icc 0 T, D σ ≤ M * Real.exp ((2 * CF + 1) * σ)) →
      ∀ τ ∈ Icc 0 T, D τ ≤ A + CF * M * (Real.exp ((2 * CF + 1) * τ) - 1) / (2 * CF + 1)) :
    ∀ τ ∈ Icc 0 T, D τ ≤ 2 * A * Real.exp ((2 * CF + 1) * T) := by
  have hL0 : 0 < 2 * CF + 1 := by linarith
  obtain ⟨M0, hM0⟩ := hDb
  set s : Set ℝ := (fun τ => (Real.exp ((2 * CF + 1) * τ))⁻¹ * D τ) '' Icc 0 T with hs
  have hbdd : BddAbove s := by
    refine ⟨max M0 0, ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    have he1 : 1 ≤ Real.exp ((2 * CF + 1) * τ) := Real.one_le_exp (by nlinarith [hτ.1])
    have hi0 : 0 < (Real.exp ((2 * CF + 1) * τ))⁻¹ := inv_pos.2 (Real.exp_pos _)
    have hi1 : (Real.exp ((2 * CF + 1) * τ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ he1
    calc (Real.exp ((2 * CF + 1) * τ))⁻¹ * D τ ≤ (Real.exp ((2 * CF + 1) * τ))⁻¹ * max M0 0 :=
          mul_le_mul_of_nonneg_left ((hM0 τ hτ).trans (le_max_left _ _)) hi0.le
      _ ≤ 1 * max M0 0 := mul_le_mul_of_nonneg_right hi1 (le_max_right _ _)
      _ = max M0 0 := one_mul _
  set M := max (sSup s) 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hDM : ∀ σ ∈ Icc 0 T, D σ ≤ M * Real.exp ((2 * CF + 1) * σ) := by
    intro σ hσ
    have h1 : (Real.exp ((2 * CF + 1) * σ))⁻¹ * D σ ≤ M :=
      (le_csSup hbdd ⟨σ, hσ, rfl⟩).trans (le_max_left _ _)
    have hp := Real.exp_pos ((2 * CF + 1) * σ)
    rw [inv_mul_le_iff₀ hp] at h1
    linarith
  have hkey : ∀ τ ∈ Icc 0 T, (Real.exp ((2 * CF + 1) * τ))⁻¹ * D τ ≤ A + M / 2 := by
    intro τ hτ
    have hE1 : 1 ≤ Real.exp ((2 * CF + 1) * τ) := Real.one_le_exp (by nlinarith [hτ.1])
    set E := Real.exp ((2 * CF + 1) * τ) with hE
    have h1 := hD M hM hDM τ hτ
    have h2 : CF * M * (E - 1) / (2 * CF + 1) ≤ M / 2 * E := by
      rw [div_le_iff₀ hL0]
      have hME : 0 ≤ M * E := mul_nonneg hM (by linarith)
      nlinarith [mul_nonneg hCF hM, mul_nonneg hCF hME]
    have hp : 0 < E := by rw [hE]; exact Real.exp_pos _
    rw [inv_mul_le_iff₀ hp]
    nlinarith
  have hsup : sSup s ≤ A + M / 2 :=
    csSup_le ⟨_, 0, ⟨le_rfl, hT⟩, rfl⟩ (by rintro _ ⟨τ, hτ, rfl⟩; exact hkey τ hτ)
  have hM2 : M ≤ 2 * A := by
    have : M ≤ A + M / 2 := max_le hsup (by linarith)
    linarith
  intro τ hτ
  have hmono : Real.exp ((2 * CF + 1) * τ) ≤ Real.exp ((2 * CF + 1) * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτ.2 hL0.le)
  calc D τ ≤ M * Real.exp ((2 * CF + 1) * τ) := hDM τ hτ
    _ ≤ 2 * A * Real.exp ((2 * CF + 1) * T) :=
      mul_le_mul hM2 hmono (Real.exp_pos _).le (by linarith)

/-- Deterministic Gronwall comparison: `ψ` solves the measure equation of the field `fld` exactly,
`χ` up to a residual `η` on the bounded-Lipschitz class, both in `𝔐`, same initial value. -/
private lemma mii_compare (CF : ℝ) (hCF0 : 0 ≤ CF)
    (fld : Measure (ℝ × ℝ) → (ℝ × ℝ → ℝ) → ℝ)
    (hCF : ∀ χ χ' : Measure (ℝ × ℝ), χ ∈ admMeasures p → χ' ∈ admMeasures p →
      BddAbove ((fun φ => |fld χ φ - fld χ' φ|) '' blTest p.CSig) ∧
      blNorm p.CSig (fun φ => fld χ φ - fld χ' φ) ≤ CF * blDist p.CSig χ χ')
    (ψ χ : ℝ → Measure (ℝ × ℝ)) (hψ : ∀ τ ∈ Icc 0 (Tstar p), ψ τ ∈ admMeasures p)
    (hχ : ∀ τ ∈ Icc 0 (Tstar p), χ τ ∈ admMeasures p)
    (hψeq : ∀ φ : ℝ × ℝ → ℝ, Measurable φ → (∃ M0 : ℝ, ∀ x, |φ x| ≤ M0) →
      ∀ τ ∈ Icc 0 (Tstar p),
        IntervalIntegrable (fun σ => fld (ψ σ) φ) volume 0 τ ∧
        ∫ x, φ x ∂(ψ τ) = ∫ x, φ x ∂(ψ 0) + ∫ σ in (0 : ℝ)..τ, fld (ψ σ) φ)
    (hχint : ∀ φ : ℝ × ℝ → ℝ, ∀ τ ∈ Icc 0 (Tstar p),
      IntervalIntegrable (fun σ => fld (χ σ) φ) volume 0 τ)
    (h0 : χ 0 = ψ 0) (η : ℝ) (hη0 : 0 ≤ η)
    (hη : ∀ τ ∈ Icc 0 (Tstar p), ∀ φ ∈ blTest p.CSig,
      |(∫ x, φ x ∂(χ τ)) - (∫ x, φ x ∂(χ 0)) - ∫ σ in (0 : ℝ)..τ, fld (χ σ) φ| ≤ η) :
    ∀ τ ∈ Icc 0 (Tstar p), blDist p.CSig (χ τ) (ψ τ) ≤
      2 * η * Real.exp ((2 * CF + 1) * Tstar p) := by
  have hT : 0 ≤ Tstar p := (Tstar_bds' p).1
  have hCs : 0 ≤ p.CSig := by linarith [p.hC]
  apply mii_exp_gronwall (D := fun τ => blDist p.CSig (χ τ) (ψ τ)) hT hCF0 hη0
  · refine ⟨2 * (p.Estar + 1), fun τ hτ => ?_⟩
    haveI := (hψ τ hτ).1
    haveI := (hχ τ hτ).1
    exact (mii_bl_le_mass _ _ (hχ τ hτ).2.1 (hψ τ hτ).2.1).trans
      (by linarith [(hψ τ hτ).2.2.1, (hχ τ hτ).2.2.1])
  · intro M hM hDM τ hτ
    haveI := (hψ τ hτ).1
    haveI := (hχ τ hτ).1
    have hE1 : 1 ≤ Real.exp ((2 * CF + 1) * τ) := Real.one_le_exp (by nlinarith [hτ.1])
    have hL0 : 0 < 2 * CF + 1 := by linarith
    have hpos : 0 ≤ CF * M * (Real.exp ((2 * CF + 1) * τ) - 1) / (2 * CF + 1) := by
      apply div_nonneg _ hL0.le
      exact mul_nonneg (mul_nonneg hCF0 hM) (by linarith)
    apply mii_bl_le_of _ _ (by positivity)
    intro φ0 hφ0
    obtain ⟨φ, hφc, hφb, hφ, hφeq⟩ := mii_test_ext hCs φ0 hφ0
    rw [mii_integral_congr_K (fun x hx => (hφeq x hx).symm) (χ τ) (hχ τ hτ).2.1,
      mii_integral_congr_K (fun x hx => (hφeq x hx).symm) (ψ τ) (hψ τ hτ).2.1]
    have hφm : Measurable φ := hφc.measurable
    have hφB : ∃ M0 : ℝ, ∀ x, |φ x| ≤ M0 := ⟨1, hφb⟩
    obtain ⟨hI2, hE2⟩ := hψeq φ hφm hφB τ hτ
    have hI1 := hχint φ τ hτ
    have hres := hη τ hτ φ hφ
    have hsub : (∫ x, φ x ∂(χ τ)) - ∫ x, φ x ∂(ψ τ) =
        ((∫ x, φ x ∂(χ τ)) - (∫ x, φ x ∂(χ 0)) - ∫ σ in (0 : ℝ)..τ, fld (χ σ) φ) +
          ∫ σ in (0 : ℝ)..τ, (fld (χ σ) φ - fld (ψ σ) φ) := by
      rw [intervalIntegral.integral_sub hI1 hI2, hE2, h0]
      ring
    rw [hsub]
    have hpt : ∀ σ ∈ Icc 0 τ, |fld (χ σ) φ - fld (ψ σ) φ| ≤
        CF * M * Real.exp ((2 * CF + 1) * σ) := by
      intro σ hσ
      have hσ' : σ ∈ Icc 0 (Tstar p) := ⟨hσ.1, hσ.2.trans hτ.2⟩
      obtain ⟨hbdd, hle⟩ := hCF (χ σ) (ψ σ) (hχ σ hσ') (hψ σ hσ')
      have h1 : |fld (χ σ) φ - fld (ψ σ) φ| ≤ CF * blDist p.CSig (χ σ) (ψ σ) :=
        (le_csSup hbdd ⟨φ, hφ, rfl⟩).trans hle
      have h3 : CF * blDist p.CSig (χ σ) (ψ σ) ≤ CF * M * Real.exp ((2 * CF + 1) * σ) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hDM σ hσ') hCF0
      exact h1.trans h3
    have hderiv : ∀ x ∈ uIcc (0 : ℝ) τ, HasDerivAt
        (fun σ => CF * M * Real.exp ((2 * CF + 1) * σ) / (2 * CF + 1))
        (CF * M * Real.exp ((2 * CF + 1) * x)) x := by
      intro x _
      have h := (((hasDerivAt_id x).const_mul (2 * CF + 1)).exp.const_mul (CF * M)).div_const
        (2 * CF + 1)
      have heq : CF * M * (Real.exp ((2 * CF + 1) * id x) * ((2 * CF + 1) * 1)) / (2 * CF + 1) =
          CF * M * Real.exp ((2 * CF + 1) * x) := by
        rw [id, mul_one]
        field_simp
      exact h.congr_deriv heq
    have hcont : Continuous fun σ => CF * M * Real.exp ((2 * CF + 1) * σ) := by fun_prop
    have hcalc : ∫ σ in (0 : ℝ)..τ, CF * M * Real.exp ((2 * CF + 1) * σ) =
        CF * M * (Real.exp ((2 * CF + 1) * τ) - 1) / (2 * CF + 1) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
      simp only [mul_zero, Real.exp_zero, mul_one]
      ring
    have hint : |∫ σ in (0 : ℝ)..τ, (fld (χ σ) φ - fld (ψ σ) φ)| ≤
        CF * M * (Real.exp ((2 * CF + 1) * τ) - 1) / (2 * CF + 1) := by
      refine (intervalIntegral.abs_integral_le_integral_abs hτ.1).trans ?_
      rw [← hcalc]
      exact intervalIntegral.integral_mono_on hτ.1 (hI1.sub hI2).abs
        (hcont.intervalIntegrable _ _) hpt
    exact (abs_add_le _ _).trans (add_le_add hres hint)

/-- `thm:app-dyn-main`(ii), snapshot `cr-2026-10-23`. Let `(𝔔_ij)` be the solution of `def:app-dyn-ode` on `[0, T⋆]`
(`e k`, `def_app_dyn_ode` with the coefficients `c k` and initial value `Δ_0 = dev0 hyp k`). Then the bounded-Lipschitz
distance between the actual and the ODE spectral energy measures tends to zero in probability:
`sup_{τ≤T⋆} ‖χ^act(τ) − χ^ode(τ)‖_BL → 0` in probability. Integrability of the test functions against the two
measures is a conclusion conjunct. Source, `section.tex` ll. 336–367, verbatim:
```latex
\begin{theorem}[Dynamical comparison]\label{thm:app-dyn-main}
Fix $\macrostep>0$, $\ridge>0$, $\bmom\in[0,1)$, $\gamma_\star<\infty$,
$C_\Sigma\ge1$, $E_\star<\infty$, $c_M<\infty$ and $0<r_0\le r_1<\infty$.
Along a sequence of dimensions with $B\to\infty$ assume:
\begin{enumerate}[label=(H\arabic*)]
\item \label{hyp:app-dyn-data} \cref{assum:data-target,assum:proportional-regime}
hold with deterministic covariances, $\max(\Nin,\Nout)\le\gamma_\star B$
and $\norm{\Sigmain},\norm{\Sigmaout}\le C_\Sigma$;
\item \label{hyp:app-dyn-algorithm} the algorithm of
\cref{def:app-setup-algorithm} is run with momentum $\bmom$, normalized
ridge $\ridge$ and step $\lr_t=\macrostep/B$;
\item \label{hyp:app-dyn-initial} $W_0$ is deterministic,
$\norm{\Delta_0}_\F^2\le E_\star$, $r_0\le\cR(0)\le r_1$, and
$\norm{\widehat A_0}\to0$;
\item \label{hyp:app-dyn-buffer} the initial buffer $M^\circ_{-1}$ is
independent of all batches and $\EE\norm{M^\circ_{-1}}_\F^2\le c_MB$.
\end{enumerate}
Let $T_\star$ be given by \cref{eqn:app-dyn-Tstar} and let $(\fQ_{ij})$ be
the solution of \cref{eqn:app-dyn-ode} of \cref{prop:app-dyn-ode}. Then the
following hold.
\begin{enumerate}[label=(\roman*)]
\item With probability tending to one, $t_{\rm stop}>BT_\star$,
$\inf_{t\le BT_\star}\cR(t)\ge r_0/2$ and
$\sup_{t\le BT_\star}\norm{\Dt}_\F^2\le E_\star+1$.
\item $\sup_{\macrotime\le T_\star}\norm{\chi^{\mathrm{act}}(\macrotime)-\chi^{\mathrm{ode}}(\macrotime)}_\BL\to0$
in probability.
\item $\sup_{\macrotime\le T_\star}\norm{\mu\lambda\,(\chi^{\mathrm{act}}(\macrotime)-\chi^{\mathrm{ode}}(\macrotime))}_\BL\to0$
and $\sup_{\macrotime\le T_\star}\abs{\cR(\lfloor B\macrotime\rfloor)-\fRisk(\macrotime)}\to0$
in probability.
\item On the event of (i), $\sup_{t\le BT_\star}\norm{\Ahat}\to0$ in probability.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_dyn_main_ii
    (cert : Muon.External.GaussianOpNorm) (certOp : Muon.External.GaussianOpNormL6)
    (certP : Muon.External.GaussianPoincare) (certQ : Muon.External.GaussianQuadFormLp)
    (hB : Tendsto (fun k : ℕ => B k) atTop atTop)
    (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C)
    (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k))
    (e : ∀ k : ℕ, ℝ → Fin (m k) → Fin (n k) → ℝ)
    (he : ∀ k : ℕ, def_app_dyn_ode p (S k) (c k) (dev0 hyp k) (Tstar p) (e k)) :
    (∀ k : ℕ, ∀ ω : Ω, ∀ τ ∈ Icc (0 : ℝ) (Tstar p), ∀ φ ∈ blTest p.CSig,
      Integrable φ (actMeas hyp S k ω τ) ∧
        Integrable φ (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ))) ∧
    ∀ ε : ℝ, 0 < ε → Tendsto (fun k : ℕ => P {ω | ENNReal.ofReal ε <
      ⨆ τ ∈ Icc (0 : ℝ) (Tstar p), ENNReal.ofReal
        (blDist p.CSig (actMeas hyp S k ω τ) (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ)))})
      atTop (𝓝 0) := by
  classical
  letI : IsProbabilityMeasure P := prob_of_dynHyp hyp
  refine ⟨fun k ω τ _ φ _ => ⟨mii_atom_integrable _ _ _ φ, mii_atom_integrable _ _ _ φ⟩, ?_⟩
  intro ε hε
  have hCs : 0 ≤ p.CSig := by linarith [p.hC]
  have hT0 : 0 < Tstar p := by
    have hm : 0 < min p.r0 1 := lt_min p.hr0 zero_lt_one
    have h1 := CE_nonneg'' p
    have h2 := CR_nonneg'' p
    have hD : 0 < 8 * (1 + CE p + CR p) := by positivity
    exact div_pos hm hD
  obtain ⟨CF0, hCF0⟩ := lem_app_dyn_field_iii p (p.Estar + 1) (p.r0 / 2) (p.r1 + 1 / 2)
    (by linarith [p.hr0])
  set CF := max CF0 0 with hCFdef
  have hCF0' : 0 ≤ CF := le_max_right _ _
  set Kx := 2 * Real.exp ((2 * CF + 1) * Tstar p) with hKx
  have hKx0 : 0 < Kx := by positivity
  set Kk := 2 * p.h / Real.sqrt (p.r0 / 2) * dMax p * (p.Estar + 1) + p.h ^ 2 * mZeta p with hKk
  have hKk0 : 0 ≤ Kk := by
    have := dMax_nonneg'' p
    have := mZeta_nonneg'' p
    have := p.hh
    have := p.hE
    positivity
  set A := 2 * (p.Estar + 1) + Tstar p * Kk with hA
  have hA0 : 0 ≤ A := by
    have := p.hE
    have : 0 ≤ Tstar p * Kk := mul_nonneg hT0.le hKk0
    rw [hA]
    linarith
  set δ := ε / (4 * (A + 1) * Kx) with hδ
  have hδ0 : 0 < δ := by
    have : 0 < A + 1 := by linarith
    positivity
  set N := ⌊p.CSig / δ⌋₊ with hN
  set η0 := ε / (4 * ((N + 1 : ℕ) : ℝ) ^ 2 * Kx) with hη0
  have hη00 : 0 < η0 := by positivity
  set η := ((N + 1 : ℕ) : ℝ) ^ 2 * η0 + 2 * δ * A with hη
  have hηn : 0 ≤ η := add_nonneg (by positivity) (mul_nonneg (by positivity) hA0)
  have hηε : 2 * η * Real.exp ((2 * CF + 1) * Tstar p) ≤ ε := by
    have hN1 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    have e1 : Kx * (((N + 1 : ℕ) : ℝ) ^ 2 * η0) = ε / 4 := by
      rw [hη0]
      field_simp
    have hA1 : 0 < A + 1 := by linarith
    have e2 : Kx * (2 * δ * A) = ε / 2 * (A / (A + 1)) := by
      rw [hδ]
      field_simp
      ring
    have e3 : A / (A + 1) ≤ 1 := (div_le_one hA1).2 (by linarith)
    have e4 : ε / 2 * (A / (A + 1)) ≤ ε / 2 := by nlinarith
    calc 2 * η * Real.exp ((2 * CF + 1) * Tstar p) = Kx * η := by rw [hKx]; ring
      _ = Kx * (((N + 1 : ℕ) : ℝ) ^ 2 * η0) + Kx * (2 * δ * A) := by rw [hη]; ring
      _ ≤ ε := by linarith
  set R := Finset.range (N + 1) with hR
  let fr : ℕ → ℝ → ℝ := fun r y => if ⌊y / δ⌋₊ = r then (1 : ℝ) else 0
  have hfr : ∀ r, ∃ M : ℝ, ∀ x ∈ Icc (0 : ℝ) p.CSig, |fr r x| ≤ M := fun r =>
    ⟨1, fun x _ => by simp only [fr]; split_ifs <;> simp⟩
  let E : ℕ × ℕ → ℕ → Set Ω := fun rs k => {ω | ENNReal.ofReal η0 <
    ⨆ τ ∈ Icc (0 : ℝ) (Tstar p), ENNReal.ofReal (blockResidual hyp S c (fr rs.1) (fr rs.2) k ω τ)}
  have hE : ∀ rs, Tendsto (fun k => P (E rs k)) atTop (𝓝 0) := fun rs =>
    (lem_app_dyn_block cert certOp certP certQ F hyp S c hc (Tstar p) hT0 (fr rs.1) (fr rs.2)
      (hfr _) (hfr _)).2.2 η0 hη00
  obtain ⟨Bad, hBad, hev⟩ := core' cert certOp certP certQ hB F hyp S c hc
  have hup : Tendsto (fun k => P (Bad k) + ∑ rs ∈ R ×ˢ R, P (E rs k)) atTop (𝓝 0) := by
    have := hBad.add (tendsto_finsetSum (R ×ˢ R) fun rs _ => hE rs)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun k => bot_le) ?_
  filter_upwards [hev, hB.eventually (eventually_ge_atTop 1)] with k hk hBk
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (measure_biUnion_finset_le (R ×ˢ R) (fun rs => E rs k))))
  intro ω hω
  by_contra hnot
  have hnB : ω ∉ Bad k := fun h => hnot (Or.inl h)
  have hnE : ∀ r ∈ R, ∀ s ∈ R, ω ∉ E (r, s) k := fun r hr s hs h =>
    hnot (Or.inr (Set.mem_iUnion₂.2 ⟨(r, s), Finset.mem_product.2 ⟨hr, hs⟩, h⟩))
  obtain ⟨hnoexit, hbd⟩ := hk ω hnB
  have hBk0 : 0 < B k := hBk
  have hadm := boundEvent_adm F hyp S k hbd
  have hstop : ∀ τ ∈ Icc (0 : ℝ) (Tstar p),
      stopMacro (blockLen (B k)) (B k) (blockExitIdx hyp k ω) τ = τ :=
    fun τ hτ => mii_stop _ _ _ _ hBk0 hnoexit τ hτ.2
  have hres : ∀ r ∈ R, ∀ s ∈ R, ∀ τ ∈ Icc (0 : ℝ) (Tstar p),
      blockResidual hyp S c (fr r) (fr s) k ω τ ≤ η0 := by
    intro r hr s hs τ hτ
    have h := hnE r hr s hs
    simp only [E, Set.mem_setOf_eq, not_lt] at h
    exact (ENNReal.ofReal_le_ofReal_iff hη00.le).1 ((le_iSup₂_of_le τ hτ le_rfl).trans h)
  have hηb : ∀ τ ∈ Icc (0 : ℝ) (Tstar p), ∀ φ ∈ blTest p.CSig,
      |(∫ x, φ x ∂(actMeas hyp S k ω τ)) - (∫ x, φ x ∂(actMeas hyp S k ω 0)) -
        ∫ σ in (0 : ℝ)..τ, fieldOp p.h (c k).d (c k).ζ (actMeas hyp S k ω σ) φ| ≤ η := by
    intro τ hτ φ hφ
    obtain ⟨ρ, hρ, hρA⟩ := mii_rep p (S k) (c k) (hyp.normBd k).2 (hyp.normBd k).1
      (fun t => errPath hyp k t ω) τ hτ.1 (fun σ hσ => hadm σ ⟨hσ.1, hσ.2.trans hτ.2⟩)
    have hρ' : ∀ φ : ℝ × ℝ → ℝ, (∫ x, φ x ∂(actMeas hyp S k ω τ)) -
        (∫ x, φ x ∂(actMeas hyp S k ω 0)) -
        ∫ σ in (0 : ℝ)..τ, fieldOp p.h (c k).d (c k).ζ (actMeas hyp S k ω σ) φ =
          ∑ i, ∑ j, ρ i j * φ ((S k).μ i, (S k).lam j) := hρ
    rw [hρ' φ]
    have hA' : ∑ i, ∑ j, |ρ i j| ≤ A := by
      refine hρA.trans ?_
      rw [hA]
      have := mul_le_mul_of_nonneg_right hτ.2 hKk0
      linarith
    refine mii_grid (S k).μ (S k).lam p.CSig δ hCs hδ0
      (mii_atoms (S k) p.CSig (hyp.normBd k).2 (hyp.normBd k).1) ρ η0 A hA' ?_ φ hφ
    intro r hr s hs
    have h1 := hres r hr s hs τ hτ
    unfold blockResidual at h1
    rw [hstop τ hτ, hρ'] at h1
    exact h1
  have hχint : ∀ φ : ℝ × ℝ → ℝ, ∀ τ ∈ Icc (0 : ℝ) (Tstar p), IntervalIntegrable
      (fun σ => fieldOp p.h (c k).d (c k).ζ (actMeas hyp S k ω σ) φ) volume 0 τ :=
    fun φ τ _ => mii_floor_ii (fun t => fieldOp p.h (c k).d (c k).ζ
      (specMeasure (S k) (errPath hyp k t ω)) φ) (B k) 0 τ
  have hψadm : ∀ τ ∈ Icc 0 (Tstar p),
      odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ) ∈ admMeasures p := fun τ hτ =>
    (prop_app_dyn_ode_ii p (S k) (c k) (dev0 hyp k) (hyp.normBd k).2 (hyp.normBd k).1
      (hyp.dims k) (hyp.W0_norm k) (hyp.W0_risk k).1 (hyp.W0_risk k).2 (e k) (he k) τ hτ).2.2
  have hψeq := prop_app_dyn_ode_iii p (S k) (c k) (dev0 hyp k) (hyp.normBd k).2
    (hyp.normBd k).1 (hyp.dims k) (hyp.W0_norm k) (hyp.W0_risk k).1 (hyp.W0_risk k).2 (e k) (he k)
  have h0 : actMeas hyp S k ω 0 = odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k 0) := by
    have hBR : (B k : ℝ) ≠ 0 := by exact_mod_cast hBk0.ne'
    rw [(he k).1.1]
    show specMeasure (S k) (errPath hyp k ⌊(B k : ℝ) * 0⌋₊ ω) = _
    rw [mul_zero, Nat.floor_zero, errPath_zero']
    unfold specMeasure odeMeasure odeInit
    congr 1
    funext i j
    field_simp
  have hcmp := mii_compare CF hCF0' (fieldOp p.h (c k).d (c k).ζ)
    (fun χ χ' h h' => by
      obtain ⟨hb, hl⟩ := hCF0 (S k) (c k) χ χ' h h'
      exact ⟨hb, hl.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (mii_bl_nonneg _ _ _))⟩)
    (fun τ => odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ)) (fun τ => actMeas hyp S k ω τ)
    hψadm (fun τ hτ => hadm τ hτ) hψeq hχint h0 η hηn hηb
  have hsup : (⨆ τ ∈ Icc (0 : ℝ) (Tstar p), ENNReal.ofReal (blDist p.CSig
      (actMeas hyp S k ω τ) (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ)))) ≤
      ENNReal.ofReal ε :=
    iSup₂_le fun τ hτ => ENNReal.ofReal_le_ofReal ((hcmp τ hτ).trans hηε)
  exact (not_lt_of_ge hsup) hω

private lemma main_atom_integrable {a b : ℕ} (mu : Fin a → ℝ) (lam : Fin b → ℝ)
    (q : Fin a → Fin b → ℝ) (f : ℝ × ℝ → ℝ) :
    Integrable f (atomMeasure mu lam q) := by
  unfold atomMeasure
  exact integrable_finsetSum_measure.mpr fun i _ =>
    integrable_finsetSum_measure.mpr fun j _ =>
      (integrable_dirac (f := f) (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma main_ae_specRect {Cs : ℝ} {rho : Measure (ℝ × ℝ)}
    (hrho : rho (specRect Cs)ᶜ = 0) : ∀ᵐ x ∂rho, x ∈ specRect Cs := by
  rw [ae_iff]
  exact hrho

private lemma main_test_bdd {Cs : ℝ} (mu nu : Measure (ℝ × ℝ))
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : mu (specRect Cs)ᶜ = 0) (hnu : nu (specRect Cs)ᶜ = 0) :
    BddAbove ((fun phi => |∫ x, phi x ∂mu - ∫ x, phi x ∂nu|) '' blTest Cs) := by
  refine ⟨mu.real univ + nu.real univ, ?_⟩
  rintro _ ⟨phi, hphi, rfl⟩
  have hb (rho : Measure (ℝ × ℝ)) [IsFiniteMeasure rho]
      (hrho : rho (specRect Cs)ᶜ = 0) : |∫ x, phi x ∂rho| ≤ rho.real univ := by
    have h := norm_integral_le_of_norm_le_const (μ := rho) (f := phi) (C := 1)
      ((main_ae_specRect hrho).mono fun x hx => by
        rw [Real.norm_eq_abs]
        exact hphi.1 x hx)
    simpa only [Real.norm_eq_abs, one_mul] using h
  exact (abs_sub _ _).trans (add_le_add (hb mu hmu) (hb nu hnu))

private lemma main_test_scaled {Cs A : ℝ} (mu nu : Measure (ℝ × ℝ))
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : mu (specRect Cs)ᶜ = 0) (hnu : nu (specRect Cs)ᶜ = 0)
    (g psi : ℝ × ℝ → ℝ) (hpsi : psi ∈ blTest Cs) (hA : 0 ≤ A)
    (heq : ∀ x ∈ specRect Cs, g x = A * psi x) :
    |∫ x, g x ∂mu - ∫ x, g x ∂nu| ≤ A * blDist Cs mu nu := by
  have he (rho : Measure (ℝ × ℝ)) (hrho : rho (specRect Cs)ᶜ = 0) :
      ∫ x, g x ∂rho = A * ∫ x, psi x ∂rho := by
    rw [← integral_const_mul]
    exact integral_congr_ae ((main_ae_specRect hrho).mono fun x hx => heq x hx)
  rw [he mu hmu, he nu hnu, ← mul_sub, abs_mul, abs_of_nonneg hA]
  unfold blDist blNorm
  exact mul_le_mul_of_nonneg_left
    (le_csSup (main_test_bdd mu nu hmu hnu) ⟨psi, hpsi, rfl⟩) hA

private lemma main_bl_scaled {Cs A : ℝ} (hA : 0 < A)
    (mu nu : Measure (ℝ × ℝ)) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : mu (specRect Cs)ᶜ = 0) (hnu : nu (specRect Cs)ᶜ = 0)
    (g : ℝ × ℝ → ℝ) (hb : ∀ x ∈ specRect Cs, |g x| ≤ A)
    (hl : ∀ x ∈ specRect Cs, ∀ y ∈ specRect Cs, |g x - g y| ≤ A * l1 x y) :
    |∫ x, g x ∂mu - ∫ x, g x ∂nu| ≤ A * blDist Cs mu nu := by
  refine main_test_scaled mu nu hmu hnu g (fun x => g x / A) ?_ hA.le ?_
  · refine ⟨?_, ?_⟩
    · intro x hx
      rw [abs_div, abs_of_pos hA]
      exact (div_le_one hA).2 (hb x hx)
    · intro x hx y hy
      rw [← sub_div, abs_div, abs_of_pos hA]
      exact (div_le_iff₀ hA).2 (by simpa only [mul_comm] using hl x hx y hy)
  · intro x _
    field_simp

private lemma main_mul_test_bound (Cs : ℝ) (hCs : 1 ≤ Cs)
    (mu nu : Measure (ℝ × ℝ)) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : mu (specRect Cs)ᶜ = 0) (hnu : nu (specRect Cs)ᶜ = 0)
    (phi : ℝ × ℝ → ℝ) (hphi : phi ∈ blTest Cs) :
    |∫ x, x.1 * x.2 * phi x ∂mu - ∫ x, x.1 * x.2 * phi x ∂nu| ≤
      (Cs ^ 2 + Cs + 1) * blDist Cs mu nu := by
  have hC0 : 0 ≤ Cs := zero_le_one.trans hCs
  have hA : 0 < Cs ^ 2 + Cs + 1 := by nlinarith [sq_nonneg Cs]
  apply main_bl_scaled hA mu nu hmu hnu (fun x => x.1 * x.2 * phi x)
  · intro x hx
    rw [abs_mul]
    have hxy : |x.1 * x.2| ≤ Cs ^ 2 := by
      rw [abs_of_nonneg (mul_nonneg hx.1.1 hx.2.1)]
      nlinarith [mul_le_mul hx.1.2 hx.2.2 hx.2.1 hC0]
    nlinarith [mul_le_mul_of_nonneg_left (hphi.1 x hx) (abs_nonneg (x.1 * x.2))]
  · intro x hx y hy
    have hprod : |x.1 * x.2 - y.1 * y.2| ≤ Cs * l1 x y := by
      rw [show x.1 * x.2 - y.1 * y.2 = x.1 * (x.2 - y.2) + y.2 * (x.1 - y.1) by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hx.1.1, abs_of_nonneg hy.2.1]
      unfold l1
      nlinarith [mul_le_mul_of_nonneg_right hx.1.2 (abs_nonneg (x.2 - y.2)),
        mul_le_mul_of_nonneg_right hy.2.2 (abs_nonneg (x.1 - y.1))]
    rw [show x.1 * x.2 * phi x - y.1 * y.2 * phi y =
      x.1 * x.2 * (phi x - phi y) + phi y * (x.1 * x.2 - y.1 * y.2) by ring]
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul]
    have hxy : |x.1 * x.2| ≤ Cs ^ 2 := by
      rw [abs_of_nonneg (mul_nonneg hx.1.1 hx.2.1)]
      nlinarith [mul_le_mul hx.1.2 hx.2.2 hx.2.1 hC0]
    have hdist : 0 ≤ l1 x y := by unfold l1; positivity
    have h1 := mul_le_mul hxy (hphi.2 x hx y hy) (abs_nonneg _) (by positivity)
    have h2 := mul_le_mul (hphi.1 y hy) hprod (abs_nonneg _) (by positivity)
    rw [← abs_mul] at ⊢
    calc
      |x.1 * x.2| * |phi x - phi y| + |phi y| * |x.1 * x.2 - y.1 * y.2| ≤
          Cs ^ 2 * l1 x y + 1 * (Cs * l1 x y) := add_le_add h1 h2
      _ ≤ (Cs ^ 2 + Cs + 1) * l1 x y := by nlinarith

private lemma main_blDistLam_le (Cs : ℝ) (hCs : 1 ≤ Cs)
    (mu nu : Measure (ℝ × ℝ)) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : mu (specRect Cs)ᶜ = 0) (hnu : nu (specRect Cs)ᶜ = 0) :
    blDistLam Cs mu nu ≤ (Cs ^ 2 + Cs + 1) * blDist Cs mu nu := by
  unfold blDistLam blNorm
  apply csSup_le
  · refine ⟨0, ⟨fun _ => 0, ?_, by simp⟩⟩
    exact ⟨by simp, by intros; simp [l1]; positivity⟩
  · rintro _ ⟨phi, hphi, rfl⟩
    exact main_mul_test_bound Cs hCs mu nu hmu hnu phi hphi

private lemma main_risk_diff_le (Cs : ℝ) (hCs : 1 ≤ Cs)
    (mu nu : Measure (ℝ × ℝ)) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : mu (specRect Cs)ᶜ = 0) (hnu : nu (specRect Cs)ᶜ = 0) :
    |riskOf mu - riskOf nu| ≤ ((Cs ^ 2 + Cs + 1) / 2) * blDist Cs mu nu := by
  have h := main_bl_scaled (Cs := Cs) (A := Cs ^ 2 + Cs + 1)
    (by nlinarith [sq_nonneg Cs]) mu nu hmu hnu (fun x => x.1 * x.2) (by
      intro x hx
      rw [abs_of_nonneg (mul_nonneg hx.1.1 hx.2.1)]
      have hC0 : 0 ≤ Cs := zero_le_one.trans hCs
      nlinarith [mul_le_mul hx.1.2 hx.2.2 hx.2.1 hC0]) (by
      intro x hx y hy
      have hprod : |x.1 * x.2 - y.1 * y.2| ≤ Cs * l1 x y := by
        rw [show x.1 * x.2 - y.1 * y.2 =
          x.1 * (x.2 - y.2) + y.2 * (x.1 - y.1) by ring]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hx.1.1, abs_of_nonneg hy.2.1]
        unfold l1
        nlinarith [mul_le_mul_of_nonneg_right hx.1.2 (abs_nonneg (x.2 - y.2)),
          mul_le_mul_of_nonneg_right hy.2.2 (abs_nonneg (x.1 - y.1))]
      have hdist : 0 ≤ l1 x y := by unfold l1; positivity
      exact hprod.trans (by nlinarith [sq_nonneg Cs]))
  unfold riskOf
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith

private lemma main_riskOf_odeMeasure {a b : ℕ} (Bc : ℝ) (mu : Fin a → ℝ)
    (lam : Fin b → ℝ) (q : Fin a → Fin b → ℝ)
    (hq : ∀ i j, 0 ≤ q i j / Bc ^ 2) :
    riskOf (odeMeasure Bc mu lam q) = odeRisk mu lam Bc q := by
  unfold riskOf odeMeasure odeRisk
  rw [atom_integral mu lam _ hq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma main_iSup_scale {alpha : Type*} (s : Set alpha) (f g : alpha → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hfg : ∀ x ∈ s, g x ≤ K * f x) :
    (⨆ x, ⨆ (_ : x ∈ s), ENNReal.ofReal (g x)) ≤
      ENNReal.ofReal K * (⨆ x, ⨆ (_ : x ∈ s), ENNReal.ofReal (f x)) := by
  refine iSup_le fun x => iSup_le fun hx => ?_
  calc
    ENNReal.ofReal (g x) ≤ ENNReal.ofReal (K * f x) := ENNReal.ofReal_le_ofReal (hfg x hx)
    _ = ENNReal.ofReal K * ENNReal.ofReal (f x) := ENNReal.ofReal_mul hK
    _ ≤ ENNReal.ofReal K * (⨆ y, ⨆ (_ : y ∈ s), ENNReal.ofReal (f y)) :=
      by gcongr; exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)

/-- `thm:app-dyn-main`(iii), snapshot `cr-2026-10-23`. Let `(𝔔_ij)` and `e k` be as in `thm_app_dyn_main_ii`. Then
(a) `sup_{τ≤T⋆} ‖μλ (χ^act(τ) − χ^ode(τ))‖_BL → 0` in probability (`blDistLam`), and (b)
`sup_{τ≤T⋆} |𝓡(⌊Bτ⌋) − fRisk(τ)| → 0` in probability, with `𝓡(⌊Bτ⌋) = riskSigma (Δ_{⌊Bτ⌋})` and `fRisk = odeRisk`.
Integrability of the weighted test functions is a conclusion conjunct. Source, `section.tex` ll. 336–367, verbatim:
```latex
\begin{theorem}[Dynamical comparison]\label{thm:app-dyn-main}
Fix $\macrostep>0$, $\ridge>0$, $\bmom\in[0,1)$, $\gamma_\star<\infty$,
$C_\Sigma\ge1$, $E_\star<\infty$, $c_M<\infty$ and $0<r_0\le r_1<\infty$.
Along a sequence of dimensions with $B\to\infty$ assume:
\begin{enumerate}[label=(H\arabic*)]
\item \label{hyp:app-dyn-data} \cref{assum:data-target,assum:proportional-regime}
hold with deterministic covariances, $\max(\Nin,\Nout)\le\gamma_\star B$
and $\norm{\Sigmain},\norm{\Sigmaout}\le C_\Sigma$;
\item \label{hyp:app-dyn-algorithm} the algorithm of
\cref{def:app-setup-algorithm} is run with momentum $\bmom$, normalized
ridge $\ridge$ and step $\lr_t=\macrostep/B$;
\item \label{hyp:app-dyn-initial} $W_0$ is deterministic,
$\norm{\Delta_0}_\F^2\le E_\star$, $r_0\le\cR(0)\le r_1$, and
$\norm{\widehat A_0}\to0$;
\item \label{hyp:app-dyn-buffer} the initial buffer $M^\circ_{-1}$ is
independent of all batches and $\EE\norm{M^\circ_{-1}}_\F^2\le c_MB$.
\end{enumerate}
Let $T_\star$ be given by \cref{eqn:app-dyn-Tstar} and let $(\fQ_{ij})$ be
the solution of \cref{eqn:app-dyn-ode} of \cref{prop:app-dyn-ode}. Then the
following hold.
\begin{enumerate}[label=(\roman*)]
\item With probability tending to one, $t_{\rm stop}>BT_\star$,
$\inf_{t\le BT_\star}\cR(t)\ge r_0/2$ and
$\sup_{t\le BT_\star}\norm{\Dt}_\F^2\le E_\star+1$.
\item $\sup_{\macrotime\le T_\star}\norm{\chi^{\mathrm{act}}(\macrotime)-\chi^{\mathrm{ode}}(\macrotime)}_\BL\to0$
in probability.
\item $\sup_{\macrotime\le T_\star}\norm{\mu\lambda\,(\chi^{\mathrm{act}}(\macrotime)-\chi^{\mathrm{ode}}(\macrotime))}_\BL\to0$
and $\sup_{\macrotime\le T_\star}\abs{\cR(\lfloor B\macrotime\rfloor)-\fRisk(\macrotime)}\to0$
in probability.
\item On the event of (i), $\sup_{t\le BT_\star}\norm{\Ahat}\to0$ in probability.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_dyn_main_iii
    (cert : Muon.External.GaussianOpNorm) (certOp : Muon.External.GaussianOpNormL6)
    (certP : Muon.External.GaussianPoincare) (certQ : Muon.External.GaussianQuadFormLp)
    (hB : Tendsto (fun k : ℕ => B k) atTop atTop)
    (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C)
    (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k))
    (e : ∀ k : ℕ, ℝ → Fin (m k) → Fin (n k) → ℝ)
    (he : ∀ k : ℕ, def_app_dyn_ode p (S k) (c k) (dev0 hyp k) (Tstar p) (e k)) :
    (∀ k : ℕ, ∀ ω : Ω, ∀ τ ∈ Icc (0 : ℝ) (Tstar p), ∀ φ ∈ blTest p.CSig,
      Integrable (fun x => x.1 * x.2 * φ x) (actMeas hyp S k ω τ) ∧
        Integrable (fun x => x.1 * x.2 * φ x) (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ))) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun k : ℕ => P {ω | ENNReal.ofReal ε <
      ⨆ τ ∈ Icc (0 : ℝ) (Tstar p), ENNReal.ofReal
        (blDistLam p.CSig (actMeas hyp S k ω τ) (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ)))})
      atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun k : ℕ => P {ω | ENNReal.ofReal ε <
      ⨆ τ ∈ Icc (0 : ℝ) (Tstar p), ENNReal.ofReal
        |riskSigma (F k).C (errPath hyp k ⌊(B k : ℝ) * τ⌋₊ ω) - odeRisk (S k).μ (S k).lam (B k : ℝ) (e k τ)|})
      atTop (𝓝 0)) := by
  have hmain := thm_app_dyn_main_ii cert certOp certP certQ hB F hyp S c hc e he
  have hnonneg : ∀ k τ, τ ∈ Icc (0 : ℝ) (Tstar p) → ∀ i j,
      0 ≤ e k τ i j / (B k : ℝ) ^ 2 := by
    intro k τ hτ
    exact (prop_app_dyn_ode_i p (S k) (c k) (dev0 hyp k)
      (hyp.normBd k).2 (hyp.normBd k).1 (hyp.dims k) (hyp.W0_norm k)
      (hyp.W0_risk k).1 (hyp.W0_risk k).2).2.2 (e k) (he k) τ hτ
  have hodeadm : ∀ k τ, τ ∈ Icc (0 : ℝ) (Tstar p) →
      odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ) ∈ admMeasures p := by
    intro k τ hτ
    exact (prop_app_dyn_ode_ii p (S k) (c k) (dev0 hyp k)
      (hyp.normBd k).2 (hyp.normBd k).1 (hyp.dims k) (hyp.W0_norm k)
      (hyp.W0_risk k).1 (hyp.W0_risk k).2 (e k) (he k) τ hτ).2.2
  have hactSupport : ∀ k ω τ,
      actMeas hyp S k ω τ (specRect p.CSig)ᶜ = 0 := by
    intro k ω τ
    simpa [actMeas, actMeasure] using
      spec_support (S k) (errPath hyp k ⌊(B k : ℝ) * τ⌋₊ ω) p.CSig
        (hyp.normBd k).2 (hyp.normBd k).1
  refine ⟨?_, ?_, ?_⟩
  · intro k ω τ hτ phi hphi
    constructor
    · simpa [actMeas, actMeasure, specMeasure] using
        (main_atom_integrable (S k).μ (S k).lam
          (modeQ (S k) (errPath hyp k ⌊(B k : ℝ) * τ⌋₊ ω))
          (fun x => x.1 * x.2 * phi x))
    · simpa [odeMeasure] using
        (main_atom_integrable (S k).μ (S k).lam
          (fun i j => e k τ i j / (B k : ℝ) ^ 2) (fun x => x.1 * x.2 * phi x))
  · intro eps heps
    let K : ℝ := p.CSig ^ 2 + p.CSig + 1
    have hK : 0 < K := by dsimp only [K]; nlinarith [sq_nonneg p.CSig]
    have hbase := hmain.2 (eps / K) (div_pos heps hK)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbase
      (Filter.Eventually.of_forall fun k => bot_le) ?_
    refine Filter.Eventually.of_forall fun k => measure_mono ?_
    intro ω hbad
    by_contra hnot
    have hsup : (⨆ τ, ⨆ (_ : τ ∈ Icc (0 : ℝ) (Tstar p)), ENNReal.ofReal
        (blDist p.CSig (actMeas hyp S k ω τ)
          (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ)))) ≤ ENNReal.ofReal (eps / K) :=
      le_of_not_gt hnot
    have hscale : (⨆ τ, ⨆ (_ : τ ∈ Icc (0 : ℝ) (Tstar p)), ENNReal.ofReal
        (blDistLam p.CSig (actMeas hyp S k ω τ)
          (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ)))) ≤
        ENNReal.ofReal K * (⨆ τ, ⨆ (_ : τ ∈ Icc (0 : ℝ) (Tstar p)), ENNReal.ofReal
          (blDist p.CSig (actMeas hyp S k ω τ)
            (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ)))) := by
      apply main_iSup_scale
      · exact hK.le
      · intro τ hτ
        letI : IsFiniteMeasure (actMeas hyp S k ω τ) := spec_isFinite (S k) _
        letI : IsFiniteMeasure (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ)) :=
          (hodeadm k τ hτ).1
        exact main_blDistLam_le p.CSig p.hC _ _ (hactSupport k ω τ)
          (hodeadm k τ hτ).2.1
    have hmul : ENNReal.ofReal K * (⨆ τ, ⨆ (_ : τ ∈ Icc (0 : ℝ) (Tstar p)),
        ENNReal.ofReal (blDist p.CSig (actMeas hyp S k ω τ)
          (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ)))) ≤
        ENNReal.ofReal K * ENNReal.ofReal (eps / K) := by gcongr
    have hle := hscale.trans hmul
    have heq : ENNReal.ofReal K * ENNReal.ofReal (eps / K) = ENNReal.ofReal eps := by
      rw [← ENNReal.ofReal_mul hK.le]
      congr 1
      field_simp
    rw [heq] at hle
    exact (not_lt_of_ge hle) hbad
  · intro eps heps
    let K : ℝ := (p.CSig ^ 2 + p.CSig + 1) / 2
    have hK : 0 < K := by dsimp only [K]; nlinarith [sq_nonneg p.CSig]
    have hbase := hmain.2 (eps / K) (div_pos heps hK)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbase
      (Filter.Eventually.of_forall fun k => bot_le) ?_
    refine Filter.Eventually.of_forall fun k => measure_mono ?_
    intro ω hbad
    by_contra hnot
    have hsup : (⨆ τ, ⨆ (_ : τ ∈ Icc (0 : ℝ) (Tstar p)), ENNReal.ofReal
        (blDist p.CSig (actMeas hyp S k ω τ)
          (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ)))) ≤ ENNReal.ofReal (eps / K) :=
      le_of_not_gt hnot
    have hscale : (⨆ τ, ⨆ (_ : τ ∈ Icc (0 : ℝ) (Tstar p)), ENNReal.ofReal
        |riskSigma (F k).C (errPath hyp k ⌊(B k : ℝ) * τ⌋₊ ω) -
          odeRisk (S k).μ (S k).lam (B k : ℝ) (e k τ)|) ≤
        ENNReal.ofReal K * (⨆ τ, ⨆ (_ : τ ∈ Icc (0 : ℝ) (Tstar p)), ENNReal.ofReal
          (blDist p.CSig (actMeas hyp S k ω τ)
            (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ)))) := by
      apply main_iSup_scale
      · exact hK.le
      · intro τ hτ
        letI : IsFiniteMeasure (actMeas hyp S k ω τ) := spec_isFinite (S k) _
        letI : IsFiniteMeasure (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ)) :=
          (hodeadm k τ hτ).1
        have hactrisk : riskOf (actMeas hyp S k ω τ) =
            riskSigma (F k).C (errPath hyp k ⌊(B k : ℝ) * τ⌋₊ ω) := by
          simpa [actMeas, actMeasure] using
            spec_risk (S k) (errPath hyp k ⌊(B k : ℝ) * τ⌋₊ ω)
        have hoderisk : riskOf (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ)) =
            odeRisk (S k).μ (S k).lam (B k : ℝ) (e k τ) :=
          main_riskOf_odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ) (hnonneg k τ hτ)
        rw [← hactrisk, ← hoderisk]
        exact main_risk_diff_le p.CSig p.hC _ _ (hactSupport k ω τ)
          (hodeadm k τ hτ).2.1
    have hmul : ENNReal.ofReal K * (⨆ τ, ⨆ (_ : τ ∈ Icc (0 : ℝ) (Tstar p)),
        ENNReal.ofReal (blDist p.CSig (actMeas hyp S k ω τ)
          (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ)))) ≤
        ENNReal.ofReal K * ENNReal.ofReal (eps / K) := by gcongr
    have hle := hscale.trans hmul
    have heq : ENNReal.ofReal K * ENNReal.ofReal (eps / K) = ENNReal.ofReal eps := by
      rw [← ENNReal.ofReal_mul hK.le]
      congr 1
      field_simp
    rw [heq] at hle
    exact (not_lt_of_ge hle) hbad

private lemma main_blockLen_pos {B : ℕ} (hB : 0 < B) : 0 < blockLen B := by
  unfold blockLen
  apply Nat.floor_pos.mpr
  exact Real.one_le_rpow (by exact_mod_cast hB) (by norm_num)

private lemma main_admA_measurable {m n : ℕ} (p : DynParams) (C : Covariances m n) :
    MeasurableSet (admA p C) := by
  have hr : Measurable (fun D : Mat m n => riskSigma C D) := by
    apply Continuous.measurable
    unfold riskSigma pairSigma
    fun_prop
  have hf : Measurable (fun D : Mat m n => fro D ^ 2) := by
    simp_rw [fro_sq_eq']
    fun_prop
  unfold admA admSetOf admBase
  simp only [Set.setOf_and]
  exact (measurableSet_le measurable_const hr).inter
    ((measurableSet_le hr measurable_const).inter (measurableSet_le hf measurable_const))

private lemma main_diffuseness_measurable {m n : ℕ} (C : Covariances m n) :
    Measurable (fun D : Mat m n => diffuseness C D) := by
  have hop : Continuous (fun A : Mat m n => opNorm A) := by
    open scoped Matrix.Norms.L2Operator in
      simpa only [opNorm_eq_norm] using (continuous_norm : Continuous (fun A : Mat m n => ‖A‖))
  unfold diffuseness normState Ahat
  have hr : Measurable (fun D : Mat m n => (Real.sqrt (2 * riskSigma C D))⁻¹) := by
    apply Measurable.inv
    apply Measurable.sqrt
    apply Measurable.const_mul
    apply Continuous.measurable
    unfold riskSigma pairSigma
    fun_prop
  have ha : Measurable (fun D : Mat m n => Arot C D) := by
    apply Continuous.measurable
    unfold Arot
    fun_prop
  exact hop.measurable.comp (hr.smul ha)

private lemma main_le_path_exit_iff {m n L t : ℕ} (p : DynParams) (C : Covariances m n)
    (hL : 0 < L) (path : ℕ → Mat m n) :
    (t : ℕ∞) ≤ (L : ℕ∞) *
        (⨅ (b : ℕ) (_ : path (b * L) ∉ admA p C), (b : ℕ∞)) ↔
      ∀ b : ℕ, path (b * L) ∉ admA p C → (t : ℕ∞) ≤ (L : ℕ∞) * (b : ℕ∞) := by
  rw [ENat.mul_iInf]
  constructor
  · intro h b hb
    exact (h.trans (iInf_le _ b)).trans (mul_le_mul' le_rfl (iInf_le _ hb))
  · intro h
    refine le_iInf fun b => ?_
    by_cases hb : path (b * L) ∉ admA p C
    · simpa [hb] using h b hb
    · simp [hb, show (L : ℕ∞) ≠ 0 by exact_mod_cast hL.ne']

private lemma main_path_exit_event_measurable {m n L t : ℕ} (p : DynParams)
    (C : Covariances m n) (hL : 0 < L) :
    MeasurableSet {path : ℕ → Mat m n | (t : ℕ∞) ≤ (L : ℕ∞) *
      (⨅ (b : ℕ) (_ : path (b * L) ∉ admA p C), (b : ℕ∞))} := by
  rw [show {path : ℕ → Mat m n | (t : ℕ∞) ≤ (L : ℕ∞) *
      (⨅ (b : ℕ) (_ : path (b * L) ∉ admA p C), (b : ℕ∞))} =
      ⋂ b : ℕ, {path | path (b * L) ∉ admA p C →
        (t : ℕ∞) ≤ (L : ℕ∞) * (b : ℕ∞)} by
    ext path
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact main_le_path_exit_iff p C hL path]
  refine MeasurableSet.iInter fun b => ?_
  by_cases htb : (t : ℕ∞) ≤ (L : ℕ∞) * (b : ℕ∞)
  · convert MeasurableSet.univ
    ext path
    simp [htb]
  · have heval : Measurable (fun path : ℕ → Mat m n => path (b * L)) :=
      measurable_pi_apply (b * L)
    convert heval (main_admA_measurable p C)
    ext path
    simp [htb]

private lemma main_diffuse_path_event_measurable {m n L B : ℕ} (p : DynParams)
    (C : Covariances m n) (hL : 0 < L) (T ε : ℝ) :
    MeasurableSet {path : ℕ → Mat m n | ∃ t : ℕ,
      (t : ℕ∞) ≤ (L : ℕ∞) *
        (⨅ (b : ℕ) (_ : path (b * L) ∉ admA p C), (b : ℕ∞)) ∧
      (t : ℝ) ≤ T * (B : ℝ) ∧ ε < diffuseness C (path t)} := by
  rw [show {path : ℕ → Mat m n | ∃ t : ℕ,
      (t : ℕ∞) ≤ (L : ℕ∞) *
        (⨅ (b : ℕ) (_ : path (b * L) ∉ admA p C), (b : ℕ∞)) ∧
      (t : ℝ) ≤ T * (B : ℝ) ∧ ε < diffuseness C (path t)} =
      ⋃ t : ℕ, {path | (t : ℕ∞) ≤ (L : ℕ∞) *
        (⨅ (b : ℕ) (_ : path (b * L) ∉ admA p C), (b : ℕ∞)) ∧
        (t : ℝ) ≤ T * (B : ℝ) ∧ ε < diffuseness C (path t)} by
    ext path
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    ]
  refine MeasurableSet.iUnion fun t => ?_
  by_cases ht : (t : ℝ) ≤ T * (B : ℝ)
  · have hd : MeasurableSet {path : ℕ → Mat m n | ε < diffuseness C (path t)} :=
      measurableSet_lt measurable_const
        (main_diffuseness_measurable C |>.comp (measurable_pi_apply t))
    convert (main_path_exit_event_measurable (L := L) (t := t) p C hL).inter hd using 1
    ext path
    simp [ht]
  · convert MeasurableSet.empty
    ext path
    simp [ht]

/-- `thm:app-dyn-main`(iv), snapshot `cr-2026-10-23`. On the event of (i), the normalized states tend to zero in
probability: `1_{mainEvent} · sup_{t≤BT⋆} ‖Â_t‖ → 0` in probability, written as `P (mainEvent ∩ {ε < sup}) → 0`
(card F5). `‖Â_t‖ = opNorm (normState (F k).C (Δ_t))`, the diffuseness of `Basic.diffuseness`. Source, `section.tex`
ll. 336–367, verbatim:
```latex
\begin{theorem}[Dynamical comparison]\label{thm:app-dyn-main}
Fix $\macrostep>0$, $\ridge>0$, $\bmom\in[0,1)$, $\gamma_\star<\infty$,
$C_\Sigma\ge1$, $E_\star<\infty$, $c_M<\infty$ and $0<r_0\le r_1<\infty$.
Along a sequence of dimensions with $B\to\infty$ assume:
\begin{enumerate}[label=(H\arabic*)]
\item \label{hyp:app-dyn-data} \cref{assum:data-target,assum:proportional-regime}
hold with deterministic covariances, $\max(\Nin,\Nout)\le\gamma_\star B$
and $\norm{\Sigmain},\norm{\Sigmaout}\le C_\Sigma$;
\item \label{hyp:app-dyn-algorithm} the algorithm of
\cref{def:app-setup-algorithm} is run with momentum $\bmom$, normalized
ridge $\ridge$ and step $\lr_t=\macrostep/B$;
\item \label{hyp:app-dyn-initial} $W_0$ is deterministic,
$\norm{\Delta_0}_\F^2\le E_\star$, $r_0\le\cR(0)\le r_1$, and
$\norm{\widehat A_0}\to0$;
\item \label{hyp:app-dyn-buffer} the initial buffer $M^\circ_{-1}$ is
independent of all batches and $\EE\norm{M^\circ_{-1}}_\F^2\le c_MB$.
\end{enumerate}
Let $T_\star$ be given by \cref{eqn:app-dyn-Tstar} and let $(\fQ_{ij})$ be
the solution of \cref{eqn:app-dyn-ode} of \cref{prop:app-dyn-ode}. Then the
following hold.
\begin{enumerate}[label=(\roman*)]
\item With probability tending to one, $t_{\rm stop}>BT_\star$,
$\inf_{t\le BT_\star}\cR(t)\ge r_0/2$ and
$\sup_{t\le BT_\star}\norm{\Dt}_\F^2\le E_\star+1$.
\item $\sup_{\macrotime\le T_\star}\norm{\chi^{\mathrm{act}}(\macrotime)-\chi^{\mathrm{ode}}(\macrotime)}_\BL\to0$
in probability.
\item $\sup_{\macrotime\le T_\star}\norm{\mu\lambda\,(\chi^{\mathrm{act}}(\macrotime)-\chi^{\mathrm{ode}}(\macrotime))}_\BL\to0$
and $\sup_{\macrotime\le T_\star}\abs{\cR(\lfloor B\macrotime\rfloor)-\fRisk(\macrotime)}\to0$
in probability.
\item On the event of (i), $\sup_{t\le BT_\star}\norm{\Ahat}\to0$ in probability.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_dyn_main_iv
    (cert : Muon.External.GaussianOpNorm) (certOp : Muon.External.GaussianOpNormL6)
    (certP : Muon.External.GaussianPoincare) (certQ : Muon.External.GaussianQuadFormLp)
    (hB : Tendsto (fun k : ℕ => B k) atTop atTop)
    (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C)
    (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun k : ℕ => P (mainEvent hyp k ∩ {ω | ENNReal.ofReal ε <
      ⨆ (t : ℕ) (_ : (t : ℝ) ≤ (B k : ℝ) * Tstar p),
        ENNReal.ofReal (opNorm (normState (F k).C (errPath hyp k t ω)))}))
      atTop (𝓝 0) := by
  intro ε hε
  classical
  choose Ω' inst P' S' hP' hC hAlg hW hLaw using fun k => hyp.exists_dynSetup_pathLaw k
  letI : ∀ k, MeasurableSpace (Ω' k) := inst
  letI : ∀ k, IsProbabilityMeasure (P' k) := hP'
  have hreg : ProportionalRegime m n B (fun k => (S' k).C) := by
    simpa only [hC] using hyp.regime
  have hW0 : Tendsto
      (fun k => opNorm (Ahat (S' k).C ((S' k).W0 - (S' k).alg.Wstar))) atTop (𝓝 0) := by
    refine hyp.W0_hat.congr fun k => ?_
    rw [hC k, hW k, hAlg k]
  have hT : 0 < Tstar p + 1 := by linarith [(Tstar_bds' p).1]
  have hdiff := lem_app_dyn_diffuse certOp p P' m n B S' hreg hW0
    (Tstar p + 1) hT ε hε
  let E1 : ℕ → Set Ω := fun k => {ω | (blockLen (B k) : ℕ∞) * blockExitIdx hyp k ω ≤
    ((⌊(B k : ℝ) * Tstar p + (blockLen (B k) : ℝ)⌋₊ : ℕ) : ℕ∞)}
  let E2 : ℕ → Set Ω := fun k => {ω | ∃ t : ℕ,
    (t : ℕ∞) ≤ (blockLen (B k) : ℕ∞) * blockExitIdx hyp k ω ∧
      (t : ℝ) ≤ (Tstar p + 1) * (B k : ℝ) ∧
        ε < diffuseness (F k).C (errPath hyp k t ω)}
  have hE1 : Tendsto (fun k => P (E1 k)) atTop (𝓝 0) := by
    simpa only [E1] using lem_app_dyn_interval_i cert certOp certP certQ hB F hyp S c hc
  have hBpos : ∀ᶠ k in atTop, 0 < B k := hB.eventually_gt_atTop 0
  have htransfer : ∀ᶠ k in atTop, P (E2 k) = P' k {ω | ∃ t : ℕ,
      (t : ℕ∞) ≤ dynBlockExitTime (S' k) ω ∧
        (t : ℝ) ≤ (Tstar p + 1) * (B k : ℝ) ∧
          ε < diffuseness (S' k).C (dynDelta (S' k) t ω)} := by
    filter_upwards [hBpos] with k hk
    have hL : 0 < blockLen (B k) := main_blockLen_pos hk
    have hlaw := hLaw k
      {path : ℕ → Mat (m k) (n k) | ∃ t : ℕ,
        (t : ℕ∞) ≤ (blockLen (B k) : ℕ∞) *
          (⨅ (b : ℕ) (_ : path (b * blockLen (B k)) ∉ admA p (F k).C), (b : ℕ∞)) ∧
        (t : ℝ) ≤ (Tstar p + 1) * (B k : ℝ) ∧
          ε < diffuseness (F k).C (path t)}
      (main_diffuse_path_event_measurable p (F k).C hL (Tstar p + 1) ε)
    simpa only [E2, errPath, blockExitIdx, dynBlockExitTime, dynBlockIndexExit, hC k,
      Set.mem_setOf_eq] using hlaw
  have hE2 : Tendsto (fun k => P (E2 k)) atTop (𝓝 0) :=
    hdiff.congr' (Filter.EventuallyEq.symm htransfer)
  have hsub : ∀ᶠ k in atTop,
      mainEvent hyp k ∩ {ω | ENNReal.ofReal ε <
        ⨆ (t : ℕ) (_ : (t : ℝ) ≤ (B k : ℝ) * Tstar p),
          ENNReal.ofReal (opNorm (normState (F k).C (errPath hyp k t ω)))} ⊆ E1 k ∪ E2 k := by
    filter_upwards [hBpos] with k hk
    rintro ω ⟨_, hsup⟩
    change ENNReal.ofReal ε < ⨆ (t : ℕ) (_ : (t : ℝ) ≤ (B k : ℝ) * Tstar p),
      ENNReal.ofReal (opNorm (normState (F k).C (errPath hyp k t ω))) at hsup
    obtain ⟨t, ht'⟩ := lt_iSup_iff.1 hsup
    obtain ⟨ht, hopen⟩ := lt_iSup_iff.1 ht'
    have hsmall : ε < diffuseness (F k).C (errPath hyp k t ω) := by
      unfold diffuseness
      exact (ENNReal.ofReal_lt_ofReal_iff'.1 hopen).1
    by_cases he : ω ∈ E1 k
    · exact Or.inl he
    · right
      have he' : ((⌊(B k : ℝ) * Tstar p + (blockLen (B k) : ℝ)⌋₊ : ℕ) : ℕ∞) <
          (blockLen (B k) : ℕ∞) * blockExitIdx hyp k ω := by
        simpa only [E1, Set.mem_setOf_eq] using (not_le.1 he)
      have htadd : (t : ℝ) ≤ (B k : ℝ) * Tstar p + (blockLen (B k) : ℝ) :=
        ht.trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
      have htfloor : t ≤ ⌊(B k : ℝ) * Tstar p + (blockLen (B k) : ℝ)⌋₊ := Nat.le_floor htadd
      have htexit : (t : ℕ∞) ≤ (blockLen (B k) : ℕ∞) * blockExitIdx hyp k ω := by
        have hcst : (t : ℕ∞) ≤
            ((⌊(B k : ℝ) * Tstar p + (blockLen (B k) : ℝ)⌋₊ : ℕ) : ℕ∞) := by
          exact_mod_cast htfloor
        exact hcst.trans he'.le
      have htT : (t : ℝ) ≤ (Tstar p + 1) * (B k : ℝ) := by
        have hk' : (0 : ℝ) ≤ B k := Nat.cast_nonneg _
        nlinarith
      exact ⟨t, htexit, htT, hsmall⟩
  have hmeasure : ∀ᶠ k in atTop, P (mainEvent hyp k ∩ {ω | ENNReal.ofReal ε <
      ⨆ (t : ℕ) (_ : (t : ℝ) ≤ (B k : ℝ) * Tstar p),
        ENNReal.ofReal (opNorm (normState (F k).C (errPath hyp k t ω)))}) ≤
      P (E1 k) + P (E2 k) := by
    filter_upwards [hsub] with k hk
    exact (measure_mono hk).trans (measure_union_le _ _)
  have hsum : Tendsto (fun k => P (E1 k) + P (E2 k)) atTop (𝓝 0) := by
    simpa only [add_zero] using hE1.add hE2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun _ => bot_le) hmeasure

private lemma pe4p2b_lam_eq_one {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (hSin : C.Sin = 1) (j : Fin n) : S.lam j = 1 := by
  have h := eig_v S j
  rw [hSin, Matrix.one_mulVec] at h
  have hn := sum_col_sq_eq_one S.vIn S.hvIn j
  have hvv : S.v j ⬝ᵥ S.v j = 1 := by
    simpa [dotProduct, SpectralData.v, sq] using hn
  have h2 := congrArg (fun w => S.v j ⬝ᵥ w) h
  simp only [dotProduct_smul, smul_eq_mul] at h2
  rw [hvv] at h2
  linarith

private lemma pe4p2b_rowMeas_eq_atomMeasure {m n : ℕ} {C : Covariances m n}
    (S : SpectralData C) (a : Fin m → Fin n → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    rowMeas S (fun i ↦ ∑ j, a i j) = atomMeasure S.μ (fun _ : Fin n ↦ (1 : ℝ)) a := by
  unfold rowMeas atomMeasure
  ext s hs
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, hs,
    Measure.dirac_apply']
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ ha _ j)]
  simp only [Fin.sum_univ_one, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_mul Finset.univ (fun j ↦ ENNReal.ofReal (a i j))
    (s.indicator 1 (S.μ i, 1))

private lemma pe4p2b_actRow_eq_actMeas
    (hyp : DynHyp p P m n B C) (S : ∀ k : ℕ, SpectralData (C k))
    (hSin : ∀ k : ℕ, (C k).Sin = 1) (k : ℕ) (omega : Ω) (tau : ℝ) :
    actRow hyp S k omega tau = actMeas hyp S k omega tau := by
  unfold actRow actMeas Muon.Dynamics.actMeasure specMeasure
  rw [show (fun i ↦ rowQ (S k) (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i) =
      (fun i ↦ ∑ j, modeQ (S k) (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i j) by
    funext i
    exact lem_app_setup_decomposition_i (S k) _ i]
  rw [pe4p2b_rowMeas_eq_atomMeasure]
  · congr 2
    funext j
    exact (pe4p2b_lam_eq_one (S k) (hSin k) j).symm
  · intro i j
    exact sq_nonneg _

private lemma pe4p2b_rowMeas_eq_odeMeasure {m n : ℕ} {C : Covariances m n}
    (S : SpectralData C) (hSin : C.Sin = 1) (Bc : ℝ)
    (e : Fin m → Fin n → ℝ) (he : ∀ i j, 0 ≤ e i j / Bc ^ 2) :
    rowMeas S (fun i ↦ ∑ j, e i j / Bc ^ 2) = odeMeasure Bc S.μ S.lam e := by
  unfold odeMeasure
  rw [pe4p2b_rowMeas_eq_atomMeasure S (fun i j ↦ e i j / Bc ^ 2) he]
  congr 2
  funext j
  exact (pe4p2b_lam_eq_one S hSin j).symm

private lemma pe4p2b_row_solution_eq_mode_sum
    (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (hSin : ∀ k : ℕ, (F k).C.Sin = 1)
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (e : ∀ k : ℕ, ℝ → Fin (m k) → Fin (n k) → ℝ)
    (he : ∀ k, def_app_dyn_ode p (S k) (c k) (dev0 hyp k) (Tstar p) (e k))
    (q : ∀ k : ℕ, ℝ → Fin (m k) → ℝ)
    (hq : ∀ k : ℕ, eqn_app_dyn_ode_rows p.h (B k : ℝ) (S k).μ (c k).d
      (rowCoef (c k)) (Tstar p) (fun i => rowQ (S k) (dev0 hyp k) i) (q k)) :
    ∀ (k : ℕ) (tau : ℝ), tau ∈ Icc 0 (Tstar p) → ∀ i,
      q k tau i = (∑ j, e k tau i j) / (B k : ℝ) ^ 2 := by
  intro k tau ht i
  obtain ⟨q', hq', hq'e⟩ := (cor_app_dyn_half_i F hyp hSin S c k).2.2 (e k) (he k)
  have hqq' := (cor_app_dyn_half_i F hyp hSin S c k).2.1 (q k) q' (hq k) hq'
  exact (congrFun (hqq' ht) i).trans (hq'e tau ht i)

private lemma pe4p2b_row_integral_abs_le {m n : ℕ} {C : Covariances m n}
    (Cs : ℝ) (S : SpectralData C) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hmem : ∀ i, (S.μ i, (1 : ℝ)) ∈ specRect Cs) (phi : ℝ × ℝ → ℝ)
    (hphi : phi ∈ blTest Cs) :
    |∫ x, phi x ∂(rowMeas S a)| ≤ ∑ i, a i := by
  unfold rowMeas
  rw [atom_integral S.μ (fun _ : Fin 1 => (1 : ℝ)) (fun i _ => a i)
    (fun i _ => ha i) phi]
  simp only [Fin.sum_univ_one]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (ha i)]
  exact mul_le_of_le_one_right (ha i) (hphi.1 (S.μ i, 1) (hmem i))

private lemma pe4p2b_blDist_le {m n : ℕ} {C : Covariances m n}
    (Cs : ℝ) (S : SpectralData C) (a b : Fin m → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hmem : ∀ i, (S.μ i, (1 : ℝ)) ∈ specRect Cs) :
    blDist Cs (rowMeas S a) (rowMeas S b) ≤ ∑ i, (a i + b i) := by
  unfold blDist blNorm
  apply csSup_le
  · refine ⟨(0 : ℝ), ⟨fun _ : ℝ × ℝ => (0 : ℝ), ?_, by simp⟩⟩
    refine ⟨by simp, ?_⟩
    intro (x : ℝ × ℝ) hx (y : ℝ × ℝ) hy
    simp only [sub_self, abs_zero]
    unfold l1
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  · rintro _ ⟨phi, hphi, rfl⟩
    have ha' := pe4p2b_row_integral_abs_le Cs S a ha hmem phi hphi
    have hb' := pe4p2b_row_integral_abs_le Cs S b hb hmem phi hphi
    refine (abs_sub _ _).trans ?_
    calc
      |∫ x, phi x ∂rowMeas S a| + |∫ x, phi x ∂rowMeas S b| ≤
          (∑ i, a i) + ∑ i, b i := add_le_add ha' hb'
      _ = ∑ i, (a i + b i) := by rw [Finset.sum_add_distrib]

private lemma pe4p2b_ofReal_csSup_image {α : Type*} (s : Set α) (f : α → ℝ)
    (hne : s.Nonempty) (hbdd : BddAbove (f '' s)) :
    ENNReal.ofReal (sSup (f '' s)) = ⨆ x, ⨆ (_ : x ∈ s), ENNReal.ofReal (f x) := by
  rw [Monotone.map_csSup_of_continuousAt ENNReal.continuous_ofReal.continuousAt
    (fun _ _ h => ENNReal.ofReal_le_ofReal h) (hne.image f) hbdd]
  apply le_antisymm
  · apply sSup_le
    rintro z ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  · refine iSup_le fun x => iSup_le fun hx => ?_
    exact le_sSup ⟨f x, ⟨x, hx, rfl⟩, rfl⟩

/-- `cor:app-dyn-half`(ii), snapshot `cr-2026-10-23`. The row measures converge in probability in the
bounded-Lipschitz distance, uniformly on `[0, T⋆]`: `sup_τ ‖χ^act_row(τ) − χ^ode_row(τ)‖_BL → 0`, where
`χ^ode_row(τ) = ∑_i 𝔮_i(τ) δ_{μ_i}` for the row solution `q` of `eqn_app_dyn_ode_rows`. Probabilistic:
takes `hc`, the identification of the coefficients (`IsActualCoeff`).

Source (`section.tex`, whole environment):
```latex
\begin{corollary}[Half-anisotropic input]\label{cor:app-dyn-half}
Assume the hypotheses of \cref{thm:app-dyn-main} with $\Sigmain=\Id_{\Nin}$.
Let $\mathfrak d_i\defeq\mathfrak d(\mu_i,1)$ and let $\mathfrak v_i\defeq\mathfrak v_i(\ridge)$
be the row coefficient of \cref{eqn:app-vol-rows}. Then the row equations
\begin{equation}\label{eqn:app-dyn-ode-rows}
\frac{\dif}{\dif\macrotime}\big(B\fQ_i(\macrotime)\big)=-\frac{2\macrostep\,\mathfrak d_i}{\sqrt{\fRisk(\macrotime)}}\,B\fQ_i(\macrotime)+\macrostep^2\mathfrak v_i,\qquad
\fRisk(\macrotime)=\frac12\sum_i\mu_i\fQ_i(\macrotime),\qquad
\fQ_i(0)=\norm{\Delta_0^\T u_i}^2,
\end{equation}
have a unique solution on $[0,T_\star]$, given by $\fQ_i=\sum_j\fQ_{ij}$
with $(\fQ_{ij})$ the solution of \cref{eqn:app-dyn-ode}. The row measures
$\chi^{\mathrm{act}}_{\mathrm{row}}(\macrotime)\defeq\sum_i\CMscr Q_i(\lfloor B\macrotime\rfloor)\,\delta_{\mu_i}$
and $\chi^{\mathrm{ode}}_{\mathrm{row}}(\macrotime)\defeq\sum_i\fQ_i(\macrotime)\,\delta_{\mu_i}$
on $[0,C_\Sigma]$ satisfy
$\sup_{\macrotime\le T_\star}\norm{\chi^{\mathrm{act}}_{\mathrm{row}}(\macrotime)-\chi^{\mathrm{ode}}_{\mathrm{row}}(\macrotime)}_\BL\to0$
in probability, and the same holds for the measures weighted by $\mu$.
\end{corollary}
```

Relocated here from `Muon.Dynamics.Corollaries` by the coordinator (2026-10-24): its proof needs results of this
module, which imports the original one. -/
theorem cor_app_dyn_half_ii (certOp : Muon.External.GaussianOpNormL6) (certP : Muon.External.GaussianPoincare) (certQ : Muon.External.GaussianQuadFormLp) (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C)) (hB : Tendsto B atTop atTop)
    (hSin : ∀ k : ℕ, (F k).C.Sin = 1) (S : ∀ k : ℕ, SpectralData (F k).C)
    (c : ∀ k : ℕ, DynCoeff p (S k) (B k)) (cert : Muon.External.GaussianOpNorm)
    (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k))
    (q : ∀ k : ℕ, ℝ → Fin (m k) → ℝ)
    (hq : ∀ k : ℕ, eqn_app_dyn_ode_rows p.h ((B k : ℕ) : ℝ) (S k).μ (c k).d (rowCoef (c k)) (Tstar p)
      (fun i => rowQ (S k) (dev0 hyp k) i) (q k)) :
    (∀ k : ℕ, ∀ ω : Ω, BddAbove ((fun τ => blDist p.CSig (actRow hyp S k ω τ) (rowMeas (S k) (q k τ))) ''
      Icc 0 (Tstar p))) ∧
    ∀ ε > 0, Tendsto (fun k : ℕ => P {ω | ε < sSup ((fun τ => blDist p.CSig (actRow hyp S k ω τ)
      (rowMeas (S k) (q k τ))) '' Icc 0 (Tstar p))}) atTop (𝓝 0) := by
  have hmode : ∀ k : ℕ, ∃ e : ℝ → Fin (m k) → Fin (n k) → ℝ,
      def_app_dyn_ode p (S k) (c k) (dev0 hyp k) (Tstar p) e := by
    intro k
    exact (prop_app_dyn_ode_i p (S k) (c k) (dev0 hyp k)
      (hyp.normBd k).2 (hyp.normBd k).1 (hyp.dims k) (hyp.W0_norm k)
      (hyp.W0_risk k).1 (hyp.W0_risk k).2).1
  choose e he using hmode
  have hnonneg : ∀ k tau, tau ∈ Icc 0 (Tstar p) → ∀ i j,
      0 ≤ e k tau i j / (B k : ℝ) ^ 2 := by
    intro k tau ht
    exact (prop_app_dyn_ode_i p (S k) (c k) (dev0 hyp k)
      (hyp.normBd k).2 (hyp.normBd k).1 (hyp.dims k) (hyp.W0_norm k)
      (hyp.W0_risk k).1 (hyp.W0_risk k).2).2.2 (e k) (he k) tau ht
  have hqmode := pe4p2b_row_solution_eq_mode_sum F hyp hSin S c e he q hq
  have hpoint : ∀ k omega tau, tau ∈ Icc 0 (Tstar p) →
      blDist p.CSig (actRow hyp S k omega tau) (rowMeas (S k) (q k tau)) =
        blDist p.CSig (actMeas hyp S k omega tau)
          (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau)) := by
    intro k omega tau ht
    have hode : rowMeas (S k) (q k tau) =
        odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau) := by
      calc
        rowMeas (S k) (q k tau) =
            rowMeas (S k) (fun i => ∑ j, e k tau i j / (B k : ℝ) ^ 2) := by
          congr 1
          funext i
          rw [hqmode k tau ht i, Finset.sum_div]
        _ = odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau) :=
          pe4p2b_rowMeas_eq_odeMeasure (S k) (hSin k) (B k : ℝ) (e k tau)
            (hnonneg k tau ht)
    rw [pe4p2b_actRow_eq_actMeas hyp S hSin k omega tau, hode]
  have hbdd : ∀ k : ℕ, ∀ omega : Ω,
      BddAbove ((fun tau => blDist p.CSig (actRow hyp S k omega tau)
        (rowMeas (S k) (q k tau))) '' Icc 0 (Tstar p)) := by
    intro k omega
    let N := ⌊(B k : ℝ) * Tstar p⌋₊
    let A : ℝ := ∑ u ∈ Finset.range (N + 1),
      ∑ i, rowQ (S k) (errPath hyp k u omega) i
    refine ⟨A + (p.Estar + 1), ?_⟩
    rintro z ⟨tau, ht, rfl⟩
    have hmem : ∀ i, ((S k).μ i, (1 : ℝ)) ∈ specRect p.CSig := by
      intro i
      exact ⟨(spec_mu_mem' (S k) p.CSig (hyp.normBd k).2 (hyp.normBd k).1).1 i,
        ⟨zero_le_one, p.hC⟩⟩
    have hactnn : ∀ i, 0 ≤ rowQ (S k)
        (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i := by
      intro i
      unfold rowQ
      positivity
    have hqnn : ∀ i, 0 ≤ q k tau i := by
      intro i
      rw [hqmode k tau ht i, Finset.sum_div]
      exact Finset.sum_nonneg fun j _ => hnonneg k tau ht i j
    have hdist := pe4p2b_blDist_le p.CSig (S k)
      (fun i => rowQ (S k) (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i)
      (q k tau) hactnn hqnn hmem
    have hfloor : ⌊(B k : ℝ) * tau⌋₊ ≤ N := by
      exact Nat.floor_le_floor (mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg (B k)))
    have hactual : (∑ i,
        rowQ (S k) (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i) ≤ A := by
      dsimp only [A]
      have hGnn : ∀ u : ℕ, 0 ≤ ∑ i, rowQ (S k) (errPath hyp k u omega) i := by
        intro u
        exact Finset.sum_nonneg fun i _ => by
          unfold rowQ
          positivity
      exact Finset.single_le_sum (fun u _ => hGnn u)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hfloor))
    have hadm : odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau) ∈ admMeasures p :=
      (prop_app_dyn_ode_ii p (S k) (c k) (dev0 hyp k)
        (hyp.normBd k).2 (hyp.normBd k).1 (hyp.dims k) (hyp.W0_norm k)
        (hyp.W0_risk k).1 (hyp.W0_risk k).2 (e k) (he k) tau ht).2.2
    have hmass : (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau)).real univ =
        ∑ i, ∑ j, e k tau i j / (B k : ℝ) ^ 2 := by
      unfold odeMeasure
      exact atom_mass (S k).μ (S k).lam _ (hnonneg k tau ht)
    have hqsum : ∑ i, q k tau i =
        (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau)).real univ := by
      rw [hmass]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hqmode k tau ht i, Finset.sum_div]
    have hqbound : (∑ i, q k tau i) ≤ p.Estar + 1 := by
      rw [hqsum]
      exact hadm.2.2.1
    calc
      blDist p.CSig (actRow hyp S k omega tau) (rowMeas (S k) (q k tau)) ≤
          ∑ i, (rowQ (S k) (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i +
            q k tau i) := by
        simpa only [actRow] using hdist
      _ = (∑ i, rowQ (S k) (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i) +
          ∑ i, q k tau i := by rw [Finset.sum_add_distrib]
      _ ≤ A + (p.Estar + 1) := add_le_add hactual hqbound
  refine ⟨hbdd, ?_⟩
  intro epsilon hepsilon
  have hmain := (thm_app_dyn_main_ii cert certOp certP certQ hB F hyp S c hc e he).2
  have hconv := hmain epsilon hepsilon
  convert hconv using 1
  funext k
  congr 1
  ext omega
  simp only [Set.mem_setOf_eq]
  have hT : 0 ≤ Tstar p := by
    unfold Tstar
    exact div_nonneg (le_of_lt (lt_min p.hr0 zero_lt_one))
      (mul_nonneg (by norm_num) (by linarith [CE_nonneg'' p, CR_nonneg'' p]))
  have hne : (Icc (0 : ℝ) (Tstar p)).Nonempty := nonempty_Icc.2 hT
  rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg hepsilon.le,
    pe4p2b_ofReal_csSup_image (Icc 0 (Tstar p))
      (fun tau => blDist p.CSig (actRow hyp S k omega tau) (rowMeas (S k) (q k tau)))
      hne (hbdd k omega)]
  have hsups : (⨆ tau, ⨆ (_ : tau ∈ Icc 0 (Tstar p)), ENNReal.ofReal
      (blDist p.CSig (actRow hyp S k omega tau) (rowMeas (S k) (q k tau)))) =
      ⨆ tau, ⨆ (_ : tau ∈ Icc 0 (Tstar p)), ENNReal.ofReal
        (blDist p.CSig (actMeas hyp S k omega tau)
          (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau))) := by
    apply le_antisymm
    · refine iSup_le fun tau => iSup_le fun ht => ?_
      rw [hpoint k omega tau ht]
      exact le_iSup_of_le tau (le_iSup_of_le ht le_rfl)
    · refine iSup_le fun tau => iSup_le fun ht => ?_
      rw [← hpoint k omega tau ht]
      exact le_iSup_of_le tau (le_iSup_of_le ht le_rfl)
  rw [hsups]

/-- `cor:app-dyn-half`(iii), snapshot `cr-2026-10-23`. The same statement for the row measures weighted by `μ`:
`sup_τ ‖μ (χ^act_row(τ) − χ^ode_row(τ))‖_BL → 0` in probability (`blDistMu`). Probabilistic: takes `hc`.

Source (`section.tex`, whole environment):
```latex
\begin{corollary}[Half-anisotropic input]\label{cor:app-dyn-half}
Assume the hypotheses of \cref{thm:app-dyn-main} with $\Sigmain=\Id_{\Nin}$.
Let $\mathfrak d_i\defeq\mathfrak d(\mu_i,1)$ and let $\mathfrak v_i\defeq\mathfrak v_i(\ridge)$
be the row coefficient of \cref{eqn:app-vol-rows}. Then the row equations
\begin{equation}\label{eqn:app-dyn-ode-rows}
\frac{\dif}{\dif\macrotime}\big(B\fQ_i(\macrotime)\big)=-\frac{2\macrostep\,\mathfrak d_i}{\sqrt{\fRisk(\macrotime)}}\,B\fQ_i(\macrotime)+\macrostep^2\mathfrak v_i,\qquad
\fRisk(\macrotime)=\frac12\sum_i\mu_i\fQ_i(\macrotime),\qquad
\fQ_i(0)=\norm{\Delta_0^\T u_i}^2,
\end{equation}
have a unique solution on $[0,T_\star]$, given by $\fQ_i=\sum_j\fQ_{ij}$
with $(\fQ_{ij})$ the solution of \cref{eqn:app-dyn-ode}. The row measures
$\chi^{\mathrm{act}}_{\mathrm{row}}(\macrotime)\defeq\sum_i\CMscr Q_i(\lfloor B\macrotime\rfloor)\,\delta_{\mu_i}$
and $\chi^{\mathrm{ode}}_{\mathrm{row}}(\macrotime)\defeq\sum_i\fQ_i(\macrotime)\,\delta_{\mu_i}$
on $[0,C_\Sigma]$ satisfy
$\sup_{\macrotime\le T_\star}\norm{\chi^{\mathrm{act}}_{\mathrm{row}}(\macrotime)-\chi^{\mathrm{ode}}_{\mathrm{row}}(\macrotime)}_\BL\to0$
in probability, and the same holds for the measures weighted by $\mu$.
\end{corollary}
```

Relocated here from `Muon.Dynamics.Corollaries` by the coordinator (2026-10-24): its proof needs results of this
module, which imports the original one. -/
private lemma pe4p2c_lam_eq_one {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (hSin : C.Sin = 1) (j : Fin n) : S.lam j = 1 := by
  have h := eig_v S j
  rw [hSin, Matrix.one_mulVec] at h
  have hn := sum_col_sq_eq_one S.vIn S.hvIn j
  have hvv : S.v j ⬝ᵥ S.v j = 1 := by
    simpa [dotProduct, SpectralData.v, sq] using hn
  have h2 := congrArg (fun w => S.v j ⬝ᵥ w) h
  simp only [dotProduct_smul, smul_eq_mul] at h2
  rw [hvv] at h2
  linarith

private lemma pe4p2c_rowMeas_eq_atomMeasure {m n : ℕ} {C : Covariances m n}
    (S : SpectralData C) (a : Fin m → Fin n → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    rowMeas S (fun i ↦ ∑ j, a i j) = atomMeasure S.μ (fun _ : Fin n ↦ (1 : ℝ)) a := by
  unfold rowMeas atomMeasure
  ext s hs
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, hs,
    Measure.dirac_apply']
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ ha _ j)]
  simp only [Fin.sum_univ_one, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_mul Finset.univ (fun j ↦ ENNReal.ofReal (a i j))
    (s.indicator 1 (S.μ i, 1))

private lemma pe4p2c_actRow_eq_actMeas
    (hyp : DynHyp p P m n B C) (S : ∀ k : ℕ, SpectralData (C k))
    (hSin : ∀ k : ℕ, (C k).Sin = 1) (k : ℕ) (omega : Ω) (tau : ℝ) :
    actRow hyp S k omega tau = actMeas hyp S k omega tau := by
  unfold actRow actMeas Muon.Dynamics.actMeasure specMeasure
  rw [show (fun i ↦ rowQ (S k) (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i) =
      (fun i ↦ ∑ j, modeQ (S k) (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i j) by
    funext i
    exact lem_app_setup_decomposition_i (S k) _ i]
  rw [pe4p2c_rowMeas_eq_atomMeasure]
  · congr 2
    funext j
    exact (pe4p2c_lam_eq_one (S k) (hSin k) j).symm
  · intro i j
    exact sq_nonneg _

private lemma pe4p2c_rowMeas_eq_odeMeasure {m n : ℕ} {C : Covariances m n}
    (S : SpectralData C) (hSin : C.Sin = 1) (Bc : ℝ)
    (e : Fin m → Fin n → ℝ) (he : ∀ i j, 0 ≤ e i j / Bc ^ 2) :
    rowMeas S (fun i ↦ ∑ j, e i j / Bc ^ 2) = odeMeasure Bc S.μ S.lam e := by
  unfold odeMeasure
  rw [pe4p2c_rowMeas_eq_atomMeasure S (fun i j ↦ e i j / Bc ^ 2) he]
  congr 2
  funext j
  exact (pe4p2c_lam_eq_one S hSin j).symm

private lemma pe4p2c_row_solution_eq_mode_sum
    (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (hSin : ∀ k : ℕ, (F k).C.Sin = 1)
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (e : ∀ k : ℕ, ℝ → Fin (m k) → Fin (n k) → ℝ)
    (he : ∀ k, def_app_dyn_ode p (S k) (c k) (dev0 hyp k) (Tstar p) (e k))
    (q : ∀ k : ℕ, ℝ → Fin (m k) → ℝ)
    (hq : ∀ k : ℕ, eqn_app_dyn_ode_rows p.h (B k : ℝ) (S k).μ (c k).d
      (rowCoef (c k)) (Tstar p) (fun i => rowQ (S k) (dev0 hyp k) i) (q k)) :
    ∀ (k : ℕ) (tau : ℝ), tau ∈ Icc 0 (Tstar p) → ∀ i,
      q k tau i = (∑ j, e k tau i j) / (B k : ℝ) ^ 2 := by
  intro k tau ht i
  obtain ⟨q', hq', hq'e⟩ := (cor_app_dyn_half_i F hyp hSin S c k).2.2 (e k) (he k)
  have hqq' := (cor_app_dyn_half_i F hyp hSin S c k).2.1 (q k) q' (hq k) hq'
  exact (congrFun (hqq' ht) i).trans (hq'e tau ht i)

private lemma pe4p2c_integral_mul_snd_rowMeas {m n : ℕ} {C : Covariances m n}
    (S : SpectralData C) (q : Fin m → ℝ) (phi : ℝ × ℝ → ℝ) :
    (∫ x, x.1 * x.2 * phi x ∂(rowMeas S q)) =
      ∫ x, x.1 * phi x ∂(rowMeas S q) := by
  unfold rowMeas atomMeasure
  simp only [Fin.sum_univ_one]
  rw [MeasureTheory.integral_finsetSum_measure (fun i _ ↦
    (MeasureTheory.integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  rw [MeasureTheory.integral_finsetSum_measure (fun i _ ↦
    (MeasureTheory.integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  simp

private lemma pe4p2c_blDistMu_eq_mul_snd_rowMeas {m n : ℕ} {C : Covariances m n}
    (Cs : ℝ) (S : SpectralData C) (q r : Fin m → ℝ) :
    blDistMu Cs (rowMeas S q) (rowMeas S r) =
      blNorm Cs (fun phi ↦
        ∫ x, x.1 * x.2 * phi x ∂(rowMeas S q) -
          ∫ x, x.1 * x.2 * phi x ∂(rowMeas S r)) := by
  unfold blDistMu
  apply congrArg (blNorm Cs)
  funext phi
  rw [pe4p2c_integral_mul_snd_rowMeas, pe4p2c_integral_mul_snd_rowMeas]

private lemma pe4p2c_blNorm_nonneg (Cs : ℝ) (ell : (ℝ × ℝ → ℝ) → ℝ) :
    0 ≤ blNorm Cs ell := by
  unfold blNorm
  exact Real.sSup_nonneg (by rintro _ ⟨phi, -, rfl⟩; exact abs_nonneg (ell phi))

private lemma pe4p2c_row_weighted_integral_abs_le {m n : ℕ} {C : Covariances m n}
    (Cs : ℝ) (S : SpectralData C) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hmem : ∀ i, (S.μ i, (1 : ℝ)) ∈ specRect Cs) (phi : ℝ × ℝ → ℝ)
    (hphi : phi ∈ blTest Cs) :
    |∫ x, x.1 * phi x ∂(rowMeas S a)| ≤ ∑ i, |S.μ i| * a i := by
  unfold rowMeas
  rw [atom_integral S.μ (fun _ : Fin 1 => (1 : ℝ)) (fun i _ => a i)
    (fun i _ => ha i) (fun x => x.1 * phi x)]
  simp only [Fin.sum_univ_one]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (ha i), abs_mul]
  have htest := hphi.1 (S.μ i, (1 : ℝ)) (hmem i)
  calc
    a i * (|S.μ i| * |phi (S.μ i, 1)|) = (a i * |S.μ i|) * |phi (S.μ i, 1)| := by ring
    _ ≤ (a i * |S.μ i|) * 1 :=
      mul_le_mul_of_nonneg_left htest (mul_nonneg (ha i) (abs_nonneg _))
    _ = |S.μ i| * a i := by ring

private lemma pe4p2c_blDistMu_le {m n : ℕ} {C : Covariances m n}
    (Cs : ℝ) (S : SpectralData C) (a b : Fin m → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hmem : ∀ i, (S.μ i, (1 : ℝ)) ∈ specRect Cs) :
    blDistMu Cs (rowMeas S a) (rowMeas S b) ≤
      ∑ i, |S.μ i| * (a i + b i) := by
  unfold blDistMu blNorm
  apply csSup_le
  · refine ⟨(0 : ℝ), ⟨fun _ : ℝ × ℝ => (0 : ℝ), ?_, by simp⟩⟩
    refine ⟨by simp, ?_⟩
    intro (x : ℝ × ℝ) hx (y : ℝ × ℝ) hy
    simp only [sub_self, abs_zero]
    unfold l1
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  · rintro _ ⟨phi, hphi, rfl⟩
    have ha' := pe4p2c_row_weighted_integral_abs_le Cs S a ha hmem phi hphi
    have hb' := pe4p2c_row_weighted_integral_abs_le Cs S b hb hmem phi hphi
    refine (abs_sub _ _).trans ?_
    calc
      |∫ x, x.1 * phi x ∂rowMeas S a| + |∫ x, x.1 * phi x ∂rowMeas S b| ≤
          (∑ i, |S.μ i| * a i) + ∑ i, |S.μ i| * b i := add_le_add ha' hb'
      _ = ∑ i, |S.μ i| * (a i + b i) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring

private lemma pe4p2c_ofReal_csSup_image {α : Type*} (s : Set α) (f : α → ℝ)
    (hne : s.Nonempty) (hbdd : BddAbove (f '' s)) :
    ENNReal.ofReal (sSup (f '' s)) = ⨆ x, ⨆ (_ : x ∈ s), ENNReal.ofReal (f x) := by
  rw [Monotone.map_csSup_of_continuousAt ENNReal.continuous_ofReal.continuousAt
    (fun _ _ h => ENNReal.ofReal_le_ofReal h) (hne.image f) hbdd]
  apply le_antisymm
  · apply sSup_le
    rintro z ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  · refine iSup_le fun x => iSup_le fun hx => ?_
    exact le_sSup ⟨f x, ⟨x, hx, rfl⟩, rfl⟩

theorem cor_app_dyn_half_iii (certOp : Muon.External.GaussianOpNormL6) (certP : Muon.External.GaussianPoincare) (certQ : Muon.External.GaussianQuadFormLp) (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C)) (hB : Tendsto B atTop atTop)
    (hSin : ∀ k : ℕ, (F k).C.Sin = 1) (S : ∀ k : ℕ, SpectralData (F k).C)
    (c : ∀ k : ℕ, DynCoeff p (S k) (B k)) (cert : Muon.External.GaussianOpNorm)
    (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k))
    (q : ∀ k : ℕ, ℝ → Fin (m k) → ℝ)
    (hq : ∀ k : ℕ, eqn_app_dyn_ode_rows p.h ((B k : ℕ) : ℝ) (S k).μ (c k).d (rowCoef (c k)) (Tstar p)
      (fun i => rowQ (S k) (dev0 hyp k) i) (q k)) :
    (∀ k : ℕ, ∀ ω : Ω, BddAbove ((fun τ => blDistMu p.CSig (actRow hyp S k ω τ) (rowMeas (S k) (q k τ))) ''
      Icc 0 (Tstar p))) ∧
    ∀ ε > 0, Tendsto (fun k : ℕ => P {ω | ε < sSup ((fun τ => blDistMu p.CSig (actRow hyp S k ω τ)
      (rowMeas (S k) (q k τ))) '' Icc 0 (Tstar p))}) atTop (𝓝 0) := by
  have hmode : ∀ k : ℕ, ∃ e : ℝ → Fin (m k) → Fin (n k) → ℝ,
      def_app_dyn_ode p (S k) (c k) (dev0 hyp k) (Tstar p) e := by
    intro k
    exact (prop_app_dyn_ode_i p (S k) (c k) (dev0 hyp k)
      (hyp.normBd k).2 (hyp.normBd k).1 (hyp.dims k) (hyp.W0_norm k)
      (hyp.W0_risk k).1 (hyp.W0_risk k).2).1
  choose e he using hmode
  have hnonneg : ∀ k tau, tau ∈ Icc 0 (Tstar p) → ∀ i j,
      0 ≤ e k tau i j / (B k : ℝ) ^ 2 := by
    intro k tau ht
    exact (prop_app_dyn_ode_i p (S k) (c k) (dev0 hyp k)
      (hyp.normBd k).2 (hyp.normBd k).1 (hyp.dims k) (hyp.W0_norm k)
      (hyp.W0_risk k).1 (hyp.W0_risk k).2).2.2 (e k) (he k) tau ht
  have hqmode := pe4p2c_row_solution_eq_mode_sum F hyp hSin S c e he q hq
  have hpoint : ∀ k omega tau, tau ∈ Icc 0 (Tstar p) →
      blDistMu p.CSig (actRow hyp S k omega tau) (rowMeas (S k) (q k tau)) =
        blDistLam p.CSig (actMeas hyp S k omega tau)
          (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau)) := by
    intro k omega tau ht
    have hode : rowMeas (S k) (q k tau) =
        odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau) := by
      calc
        rowMeas (S k) (q k tau) =
            rowMeas (S k) (fun i => ∑ j, e k tau i j / (B k : ℝ) ^ 2) := by
          congr 1
          funext i
          rw [hqmode k tau ht i, Finset.sum_div]
        _ = odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau) :=
          pe4p2c_rowMeas_eq_odeMeasure (S k) (hSin k) (B k : ℝ) (e k tau)
            (hnonneg k tau ht)
    calc
      blDistMu p.CSig (actRow hyp S k omega tau) (rowMeas (S k) (q k tau)) =
          blDistLam p.CSig (actRow hyp S k omega tau) (rowMeas (S k) (q k tau)) := by
        unfold actRow blDistLam
        exact pe4p2c_blDistMu_eq_mul_snd_rowMeas p.CSig (S k) _ _
      _ = blDistLam p.CSig (actMeas hyp S k omega tau)
          (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau)) := by
        rw [pe4p2c_actRow_eq_actMeas hyp S hSin k omega tau, hode]
  have hbdd : ∀ k : ℕ, ∀ omega : Ω,
      BddAbove ((fun tau => blDistMu p.CSig (actRow hyp S k omega tau)
        (rowMeas (S k) (q k tau))) '' Icc 0 (Tstar p)) := by
    intro k omega
    let N := ⌊(B k : ℝ) * Tstar p⌋₊
    let A : ℝ := ∑ u ∈ Finset.range (N + 1),
      ∑ i, |(S k).μ i| * rowQ (S k) (errPath hyp k u omega) i
    refine ⟨A + p.CSig * (p.Estar + 1), ?_⟩
    rintro z ⟨tau, ht, rfl⟩
    have hmem : ∀ i, ((S k).μ i, (1 : ℝ)) ∈ specRect p.CSig := by
      intro i
      exact ⟨(spec_mu_mem' (S k) p.CSig (hyp.normBd k).2 (hyp.normBd k).1).1 i,
        ⟨zero_le_one, p.hC⟩⟩
    have hactnn : ∀ i, 0 ≤ rowQ (S k)
        (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i := by
      intro i
      unfold rowQ
      positivity
    have hqnn : ∀ i, 0 ≤ q k tau i := by
      intro i
      rw [hqmode k tau ht i, Finset.sum_div]
      exact Finset.sum_nonneg fun j _ => hnonneg k tau ht i j
    have hdist := pe4p2c_blDistMu_le p.CSig (S k)
      (fun i => rowQ (S k) (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i)
      (q k tau) hactnn hqnn hmem
    have hfloor : ⌊(B k : ℝ) * tau⌋₊ ≤ N := by
      exact Nat.floor_le_floor (mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg (B k)))
    have hactual : (∑ i, |(S k).μ i| *
        rowQ (S k) (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i) ≤ A := by
      dsimp only [A]
      have hGnn : ∀ u : ℕ, 0 ≤ ∑ i, |(S k).μ i| *
          rowQ (S k) (errPath hyp k u omega) i := by
        intro u
        exact Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (by
          unfold rowQ
          positivity)
      exact Finset.single_le_sum (fun u _ => hGnn u)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hfloor))
    have hadm : odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau) ∈ admMeasures p :=
      (prop_app_dyn_ode_ii p (S k) (c k) (dev0 hyp k)
        (hyp.normBd k).2 (hyp.normBd k).1 (hyp.dims k) (hyp.W0_norm k)
        (hyp.W0_risk k).1 (hyp.W0_risk k).2 (e k) (he k) tau ht).2.2
    have hmass : (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau)).real univ =
        ∑ i, ∑ j, e k tau i j / (B k : ℝ) ^ 2 := by
      unfold odeMeasure
      exact atom_mass (S k).μ (S k).lam _ (hnonneg k tau ht)
    have hqsum : ∑ i, q k tau i =
        (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau)).real univ := by
      rw [hmass]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hqmode k tau ht i, Finset.sum_div]
    have hqbound : (∑ i, |(S k).μ i| * q k tau i) ≤ p.CSig * (p.Estar + 1) := by
      calc
        (∑ i, |(S k).μ i| * q k tau i) ≤ ∑ i, p.CSig * q k tau i := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_of_nonneg (μ_nonneg (S k) i)]
          exact mul_le_mul_of_nonneg_right
            ((spec_mu_mem' (S k) p.CSig (hyp.normBd k).2 (hyp.normBd k).1).1 i).2
            (hqnn i)
        _ = p.CSig * ∑ i, q k tau i := by rw [Finset.mul_sum]
        _ = p.CSig * (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau)).real univ := by
          rw [hqsum]
        _ ≤ p.CSig * (p.Estar + 1) :=
          mul_le_mul_of_nonneg_left hadm.2.2.1 (le_trans zero_le_one p.hC)
    calc
      blDistMu p.CSig (actRow hyp S k omega tau) (rowMeas (S k) (q k tau)) ≤
          ∑ i, |(S k).μ i| *
            (rowQ (S k) (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i + q k tau i) := by
        simpa only [actRow] using hdist
      _ = (∑ i, |(S k).μ i| *
          rowQ (S k) (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i) +
          ∑ i, |(S k).μ i| * q k tau i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ A + p.CSig * (p.Estar + 1) := add_le_add hactual hqbound
  refine ⟨hbdd, ?_⟩
  intro epsilon hepsilon
  have hmain := (thm_app_dyn_main_iii cert certOp certP certQ hB F hyp S c hc e he).2.1
  have hconv := hmain epsilon hepsilon
  convert hconv using 1
  funext k
  congr 1
  ext omega
  simp only [Set.mem_setOf_eq]
  have hT : 0 ≤ Tstar p := by
    unfold Tstar
    exact div_nonneg (le_of_lt (lt_min p.hr0 zero_lt_one))
      (mul_nonneg (by norm_num) (by linarith [CE_nonneg'' p, CR_nonneg'' p]))
  have hne : (Icc (0 : ℝ) (Tstar p)).Nonempty := nonempty_Icc.2 hT
  rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg hepsilon.le,
    pe4p2c_ofReal_csSup_image (Icc 0 (Tstar p))
      (fun tau => blDistMu p.CSig (actRow hyp S k omega tau) (rowMeas (S k) (q k tau)))
      hne (hbdd k omega)]
  have hsups : (⨆ tau, ⨆ (_ : tau ∈ Icc 0 (Tstar p)), ENNReal.ofReal
      (blDistMu p.CSig (actRow hyp S k omega tau) (rowMeas (S k) (q k tau)))) =
      ⨆ tau, ⨆ (_ : tau ∈ Icc 0 (Tstar p)), ENNReal.ofReal
        (blDistLam p.CSig (actMeas hyp S k omega tau)
          (odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k tau))) := by
    apply le_antisymm
    · refine iSup_le fun tau => iSup_le fun ht => ?_
      rw [hpoint k omega tau ht]
      exact le_iSup_of_le tau (le_iSup_of_le ht le_rfl)
    · refine iSup_le fun tau => iSup_le fun ht => ?_
      rw [← hpoint k omega tau ht]
      exact le_iSup_of_le tau (le_iSup_of_le ht le_rfl)
  rw [hsups]

private lemma pe4p5b_ae_specRect {Cs : ℝ} {ρ : Measure (ℝ × ℝ)}
    (hK : ρ (specRect Cs)ᶜ = 0) : ∀ᵐ x ∂ρ, x ∈ specRect Cs := by
  rw [ae_iff]
  exact hK

private lemma pe4p5b_test_le_mass {Cs : ℝ} (μ ν : Measure (ℝ × ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0)
    (φ : ℝ × ℝ → ℝ) (hφ : φ ∈ blTest Cs) :
    |∫ x, φ x ∂μ - ∫ x, φ x ∂ν| ≤ μ.real univ + ν.real univ := by
  have hb (ρ : Measure (ℝ × ℝ)) [IsFiniteMeasure ρ]
      (hρ : ρ (specRect Cs)ᶜ = 0) : |∫ x, φ x ∂ρ| ≤ ρ.real univ := by
    have h := norm_integral_le_of_norm_le_const (μ := ρ) (f := φ) (C := 1)
      ((pe4p5b_ae_specRect hρ).mono fun x hx => by
        rw [Real.norm_eq_abs]
        exact hφ.1 x hx)
    simpa only [Real.norm_eq_abs, one_mul] using h
  exact (abs_sub _ _).trans (add_le_add (hb μ hμ) (hb ν hν))

private lemma pe4p5b_test_bdd {Cs : ℝ} (μ ν : Measure (ℝ × ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0) :
    BddAbove ((fun φ => |∫ x, φ x ∂μ - ∫ x, φ x ∂ν|) '' blTest Cs) := by
  refine ⟨μ.real univ + ν.real univ, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  exact pe4p5b_test_le_mass μ ν hμ hν φ hφ

private lemma pe4p5b_blDist_le_mass {Cs : ℝ} (μ ν : Measure (ℝ × ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0) :
    blDist Cs μ ν ≤ μ.real univ + ν.real univ := by
  unfold blDist blNorm
  exact csSup_le (by
    refine ⟨0, ⟨fun _ => 0, ?_, by simp⟩⟩
    refine ⟨by simp, ?_⟩
    intro x hx y hy
    simp only [sub_self, abs_zero]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)) (by
      rintro _ ⟨φ, hφ, rfl⟩
      exact pe4p5b_test_le_mass μ ν hμ hν φ hφ)

private lemma pe4p5b_blDist_triangle {Cs : ℝ} (μ ν ρ : Measure (ℝ × ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0)
    (hρ : ρ (specRect Cs)ᶜ = 0) :
    blDist Cs μ ρ ≤ blDist Cs μ ν + blDist Cs ν ρ := by
  unfold blDist blNorm
  apply csSup_le
  · refine ⟨0, ⟨fun _ => 0, ?_, by simp⟩⟩
    refine ⟨by simp, ?_⟩
    intro x hx y hy
    simp only [sub_self, abs_zero]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  · rintro _ ⟨φ, hφ, rfl⟩
    calc
      |∫ x, φ x ∂μ - ∫ x, φ x ∂ρ| =
          |(∫ x, φ x ∂μ - ∫ x, φ x ∂ν) + (∫ x, φ x ∂ν - ∫ x, φ x ∂ρ)| := by ring_nf
      _ ≤ |∫ x, φ x ∂μ - ∫ x, φ x ∂ν| + |∫ x, φ x ∂ν - ∫ x, φ x ∂ρ| :=
        abs_add_le _ _
      _ ≤ sSup ((fun ψ => |∫ x, ψ x ∂μ - ∫ x, ψ x ∂ν|) '' blTest Cs) +
          sSup ((fun ψ => |∫ x, ψ x ∂ν - ∫ x, ψ x ∂ρ|) '' blTest Cs) :=
        add_le_add
          (le_csSup (pe4p5b_test_bdd μ ν hμ hν) ⟨φ, hφ, rfl⟩)
          (le_csSup (pe4p5b_test_bdd ν ρ hν hρ) ⟨φ, hφ, rfl⟩)

/-- `cor:app-dyn-continuum`(iii), snapshot `cr-2026-10-23`. Probabilistic part: along any subsequence `ι` on which
the limits of (i) hold, for every solution `χ` of `eqn_app_dyn_continuum`, `sup_τ ‖χ^act_B(τ) − χ(τ)‖_BL → 0`
in probability, with `χ^act_B(τ) = actMeas` (the reused `actMeasure`). Takes `hc`.

Source (`section.tex`, whole environment):
```latex
\begin{corollary}[Continuum equation]\label{cor:app-dyn-continuum}
Assume the hypotheses of \cref{thm:app-dyn-main}, and write $\mathfrak d_B$,
$\zeta_B$, $\chi^{\mathrm{act}}_B$, $\chi^{\mathrm{ode}}_B$ for the objects
at the dimension indexed by $B$.
\begin{enumerate}[label=(\roman*)]
\item Every sequence of dimensions has a subsequence along which $\mathfrak d_B\to\mathfrak d_\infty$
uniformly on $\mathbb K$, $\zeta_B\to\zeta_\infty$ weakly and
$\chi^{\mathrm{act}}_B(0)\to\chi_0$ weakly.
\item Along any such subsequence, the measure equation
\begin{equation}\label{eqn:app-dyn-continuum}
\chi(\macrotime)=\chi_0+\int_0^\macrotime\Big(-\frac{2\macrostep\,\mathfrak d_\infty\,\chi(\sigma)}{\sqrt{\fRisk(\chi(\sigma))}}+\macrostep^2\zeta_\infty\Big)\dif\sigma
\end{equation}
has a unique solution $\chi$ on $[0,T_\star]$ among paths with values in
$\mathfrak M$ that are continuous for the bounded-Lipschitz norm, and
\[
\sup_{\macrotime\le T_\star}\norm{\chi^{\mathrm{ode}}_B(\macrotime)-\chi(\macrotime)}_\BL\to0,\qquad
\sup_{\macrotime\le T_\star}\norm{\chi^{\mathrm{act}}_B(\macrotime)-\chi(\macrotime)}_\BL\to0\ \text{in probability}.
\]
\item Along any such subsequence,
$\sup_{\macrotime\le T_\star}\abs{\cR(\lfloor B\macrotime\rfloor)-\fRisk(\chi(\macrotime))}\to0$ in probability.
\end{enumerate}
\end{corollary}
```

Relocated here from `Muon.Dynamics.Corollaries` by the coordinator (2026-10-24): its proof needs results of this
module, which imports the original one. -/
theorem cor_app_dyn_continuum_iii (certOp : Muon.External.GaussianOpNormL6) (certP : Muon.External.GaussianPoincare) (certQ : Muon.External.GaussianQuadFormLp) (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C)) (hB : Tendsto B atTop atTop)
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (cert : Muon.External.GaussianOpNorm) (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k))
    (ι : ℕ → ℕ) (hι : StrictMono ι) (dinf : ℝ × ℝ → ℝ) (ζinf χ0 : Measure (ℝ × ℝ))
    (hL : contLimit hyp S c ι dinf ζinf χ0) :
    ∀ χ : ℝ → Measure (ℝ × ℝ), eqn_app_dyn_continuum p dinf ζinf χ0 χ →
      (∀ n : ℕ, ∀ ω : Ω, BddAbove ((fun τ => blDist p.CSig (actMeas hyp S (ι n) ω τ) (χ τ)) ''
        Icc 0 (Tstar p))) ∧
      ∀ ε > 0, Tendsto (fun n : ℕ => P {ω | ε < sSup ((fun τ => blDist p.CSig
        (actMeas hyp S (ι n) ω τ) (χ τ)) '' Icc 0 (Tstar p))}) atTop (𝓝 0) := by
  intro χ hχ
  have hmode : ∀ k : ℕ, ∃ e : ℝ → Fin (m k) → Fin (n k) → ℝ,
      def_app_dyn_ode p (S k) (c k) (dev0 hyp k) (Tstar p) e := by
    intro k
    exact (prop_app_dyn_ode_i p (S k) (c k) (dev0 hyp k)
      (hyp.normBd k).2 (hyp.normBd k).1 (hyp.dims k) (hyp.W0_norm k)
      (hyp.W0_risk k).1 (hyp.W0_risk k).2).1
  choose e he using hmode
  have hodeadm : ∀ k : ℕ, ∀ τ ∈ Icc (0 : ℝ) (Tstar p),
      odeMeasure (B k : ℝ) (S k).μ (S k).lam (e k τ) ∈ admMeasures p := by
    intro k τ hτ
    exact (prop_app_dyn_ode_ii p (S k) (c k) (dev0 hyp k)
      (hyp.normBd k).2 (hyp.normBd k).1 (hyp.dims k) (hyp.W0_norm k)
      (hyp.W0_risk k).1 (hyp.W0_risk k).2 (e k) (he k) τ hτ).2.2
  have hcont :=
    (cor_app_dyn_continuum_ii F hyp hB S c ι hι dinf ζinf χ0 hL e he).2.2 χ hχ
  have hmain := (thm_app_dyn_main_ii cert certOp certP certQ hB F hyp S c hc e he).2
  have hT : 0 ≤ Tstar p := by
    unfold Tstar
    exact div_nonneg (le_of_lt (lt_min p.hr0 zero_lt_one))
      (mul_nonneg (by norm_num) (by linarith [CE_nonneg'' p, CR_nonneg'' p]))
  have hIcc : (Icc (0 : ℝ) (Tstar p)).Nonempty := nonempty_Icc.2 hT
  have hbddAO : ∀ n : ℕ, ∀ ω : Ω, BddAbove ((fun τ => blDist p.CSig
      (actMeas hyp S (ι n) ω τ)
      (odeMeasure (B (ι n) : ℝ) (S (ι n)).μ (S (ι n)).lam (e (ι n) τ))) ''
      Icc 0 (Tstar p)) := by
    intro n' ω
    let N := ⌊(B (ι n') : ℝ) * Tstar p⌋₊
    let A : ℝ := ∑ u ∈ Finset.range (N + 1), fro (errPath hyp (ι n') u ω) ^ 2
    refine ⟨A + (p.Estar + 1), ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    letI : IsFiniteMeasure (actMeas hyp S (ι n') ω τ) := by
      unfold actMeas actMeasure
      exact spec_isFinite (S (ι n')) _
    have hactSupp : actMeas hyp S (ι n') ω τ (specRect p.CSig)ᶜ = 0 := by
      simpa only [actMeas, actMeasure] using
        spec_support (S (ι n')) (errPath hyp (ι n')
          ⌊(B (ι n') : ℝ) * τ⌋₊ ω) p.CSig (hyp.normBd (ι n')).2 (hyp.normBd (ι n')).1
    have hadm := hodeadm (ι n') τ hτ
    letI : IsFiniteMeasure
        (odeMeasure (B (ι n') : ℝ) (S (ι n')).μ (S (ι n')).lam (e (ι n') τ)) := hadm.1
    have hfloor : ⌊(B (ι n') : ℝ) * τ⌋₊ ≤ N := by
      exact Nat.floor_le_floor
        (mul_le_mul_of_nonneg_left hτ.2 (Nat.cast_nonneg (B (ι n'))))
    have hactual : fro (errPath hyp (ι n') ⌊(B (ι n') : ℝ) * τ⌋₊ ω) ^ 2 ≤ A := by
      dsimp only [A]
      exact Finset.single_le_sum (fun u _ => sq_nonneg (fro (errPath hyp (ι n') u ω)))
        (Finset.mem_range.2 (Nat.lt_succ_of_le hfloor))
    calc
      blDist p.CSig (actMeas hyp S (ι n') ω τ)
          (odeMeasure (B (ι n') : ℝ) (S (ι n')).μ (S (ι n')).lam (e (ι n') τ)) ≤
          (actMeas hyp S (ι n') ω τ).real univ +
            (odeMeasure (B (ι n') : ℝ) (S (ι n')).μ
              (S (ι n')).lam (e (ι n') τ)).real univ :=
        pe4p5b_blDist_le_mass _ _ hactSupp hadm.2.1
      _ = fro (errPath hyp (ι n') ⌊(B (ι n') : ℝ) * τ⌋₊ ω) ^ 2 +
          (odeMeasure (B (ι n') : ℝ) (S (ι n')).μ
            (S (ι n')).lam (e (ι n') τ)).real univ := by
        rw [show actMeas hyp S (ι n') ω τ =
          specMeasure (S (ι n')) (errPath hyp (ι n')
            ⌊(B (ι n') : ℝ) * τ⌋₊ ω) by rfl, spec_mass]
      _ ≤ A + (p.Estar + 1) := add_le_add hactual hadm.2.2.1
  have htri : ∀ n : ℕ, ∀ ω : Ω, ∀ τ ∈ Icc (0 : ℝ) (Tstar p),
      blDist p.CSig (actMeas hyp S (ι n) ω τ) (χ τ) ≤
        blDist p.CSig (actMeas hyp S (ι n) ω τ)
          (odeMeasure (B (ι n) : ℝ) (S (ι n)).μ (S (ι n)).lam (e (ι n) τ)) +
        blDist p.CSig
          (odeMeasure (B (ι n) : ℝ) (S (ι n)).μ (S (ι n)).lam (e (ι n) τ)) (χ τ) := by
    intro n' ω τ hτ
    letI : IsFiniteMeasure (actMeas hyp S (ι n') ω τ) := by
      unfold actMeas actMeasure
      exact spec_isFinite (S (ι n')) _
    have hactSupp : actMeas hyp S (ι n') ω τ (specRect p.CSig)ᶜ = 0 := by
      simpa only [actMeas, actMeasure] using
        spec_support (S (ι n')) (errPath hyp (ι n')
          ⌊(B (ι n') : ℝ) * τ⌋₊ ω) p.CSig (hyp.normBd (ι n')).2 (hyp.normBd (ι n')).1
    have hode := hodeadm (ι n') τ hτ
    letI : IsFiniteMeasure
        (odeMeasure (B (ι n') : ℝ) (S (ι n')).μ (S (ι n')).lam (e (ι n') τ)) := hode.1
    have hχadm := hχ.2.1 τ hτ
    letI : IsFiniteMeasure (χ τ) := hχadm.1
    exact pe4p5b_blDist_triangle _ _ _ hactSupp hode.2.1 hχadm.2.1
  have hbdd : ∀ n : ℕ, ∀ ω : Ω, BddAbove ((fun τ =>
      blDist p.CSig (actMeas hyp S (ι n) ω τ) (χ τ)) '' Icc 0 (Tstar p)) := by
    intro n' ω
    refine ⟨sSup ((fun τ => blDist p.CSig (actMeas hyp S (ι n') ω τ)
        (odeMeasure (B (ι n') : ℝ) (S (ι n')).μ (S (ι n')).lam (e (ι n') τ))) ''
          Icc 0 (Tstar p)) +
      sSup ((fun τ => blDist p.CSig
        (odeMeasure (B (ι n') : ℝ) (S (ι n')).μ (S (ι n')).lam (e (ι n') τ)) (χ τ)) ''
          Icc 0 (Tstar p)), ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    exact (htri n' ω τ hτ).trans (add_le_add
      (le_csSup (hbddAO n' ω) ⟨τ, hτ, rfl⟩)
      (le_csSup (hcont.1 n') ⟨τ, hτ, rfl⟩))
  refine ⟨hbdd, ?_⟩
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hmainι := (hmain (ε / 2) hhalf).comp hι.tendsto_atTop
  have hsmall := hcont.2.eventually (Iio_mem_nhds hhalf)
  have hsub : ∀ᶠ n' in atTop,
      {ω | ε < sSup ((fun τ => blDist p.CSig (actMeas hyp S (ι n') ω τ) (χ τ)) ''
        Icc 0 (Tstar p))} ⊆
      {ω | ENNReal.ofReal (ε / 2) < ⨆ τ ∈ Icc (0 : ℝ) (Tstar p), ENNReal.ofReal
        (blDist p.CSig (actMeas hyp S (ι n') ω τ)
          (odeMeasure (B (ι n') : ℝ) (S (ι n')).μ (S (ι n')).lam (e (ι n') τ)))} := by
    filter_upwards [hsmall] with n' hn
    intro ω hω
    have hsup : sSup ((fun τ => blDist p.CSig (actMeas hyp S (ι n') ω τ) (χ τ)) ''
        Icc 0 (Tstar p)) ≤
        sSup ((fun τ => blDist p.CSig (actMeas hyp S (ι n') ω τ)
          (odeMeasure (B (ι n') : ℝ) (S (ι n')).μ (S (ι n')).lam (e (ι n') τ))) ''
            Icc 0 (Tstar p)) +
        sSup ((fun τ => blDist p.CSig
          (odeMeasure (B (ι n') : ℝ) (S (ι n')).μ (S (ι n')).lam (e (ι n') τ)) (χ τ)) ''
            Icc 0 (Tstar p)) := by
      apply csSup_le
      · exact hIcc.image _
      · rintro _ ⟨τ, hτ, rfl⟩
        exact (htri n' ω τ hτ).trans (add_le_add
          (le_csSup (hbddAO n' ω) ⟨τ, hτ, rfl⟩)
          (le_csSup (hcont.1 n') ⟨τ, hτ, rfl⟩))
    have hao : ε / 2 < sSup ((fun τ => blDist p.CSig (actMeas hyp S (ι n') ω τ)
        (odeMeasure (B (ι n') : ℝ) (S (ι n')).μ (S (ι n')).lam (e (ι n') τ))) ''
          Icc 0 (Tstar p)) := by
      change ε < _ at hω
      linarith
    simp only [Set.mem_setOf_eq]
    rw [← pe4p2b_ofReal_csSup_image (Icc 0 (Tstar p))
      (fun τ => blDist p.CSig (actMeas hyp S (ι n') ω τ)
        (odeMeasure (B (ι n') : ℝ) (S (ι n')).μ (S (ι n')).lam (e (ι n') τ)))
      hIcc (hbddAO n' ω)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hhalf.le).2 hao
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmainι
    (Filter.Eventually.of_forall fun _ => bot_le) (hsub.mono fun _ hn => measure_mono hn)

private lemma pe4p5c_ae_specRect {Cs : ℝ} {ρ : Measure (ℝ × ℝ)}
    (hK : ρ (specRect Cs)ᶜ = 0) : ∀ᵐ x ∂ρ, x ∈ specRect Cs := by
  rw [ae_iff]
  exact hK

private lemma pe4p5c_test_bdd {Cs : ℝ} (T : Set (ℝ × ℝ → ℝ))
    (hT : ∀ φ ∈ T, ∀ x ∈ specRect Cs, |φ x| ≤ 1)
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0) :
    BddAbove ((fun φ => |∫ x, φ x ∂μ - ∫ x, φ x ∂ν|) '' T) := by
  refine ⟨μ.real univ + ν.real univ, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  have hb (ρ : Measure (ℝ × ℝ)) [IsFiniteMeasure ρ]
      (hρ : ρ (specRect Cs)ᶜ = 0) : |∫ x, φ x ∂ρ| ≤ ρ.real univ := by
    have h := norm_integral_le_of_norm_le_const (μ := ρ) (f := φ) (C := 1)
      ((pe4p5c_ae_specRect hρ).mono fun x hx => by
        rw [Real.norm_eq_abs]
        exact hT φ hφ x hx)
    simpa only [Real.norm_eq_abs, one_mul] using h
  exact (abs_sub _ _).trans (add_le_add (hb μ hμ) (hb ν hν))

private lemma pe4p5c_test_scaled {Cs A : ℝ} (T : Set (ℝ × ℝ → ℝ))
    (hT : ∀ φ ∈ T, ∀ x ∈ specRect Cs, |φ x| ≤ 1)
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0)
    (g ψ : ℝ × ℝ → ℝ) (hψ : ψ ∈ T) (hA : 0 ≤ A)
    (he : ∀ x ∈ specRect Cs, g x = A * ψ x) :
    |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤
      A * sSup ((fun φ => |∫ x, φ x ∂μ - ∫ x, φ x ∂ν|) '' T) := by
  have e (ρ : Measure (ℝ × ℝ)) (hρ : ρ (specRect Cs)ᶜ = 0) :
      ∫ x, g x ∂ρ = A * ∫ x, ψ x ∂ρ := by
    rw [← integral_const_mul]
    exact integral_congr_ae ((pe4p5c_ae_specRect hρ).mono fun x hx => he x hx)
  rw [e μ hμ, e ν hν, ← mul_sub, abs_mul, abs_of_nonneg hA]
  exact mul_le_mul_of_nonneg_left
    (le_csSup (pe4p5c_test_bdd T hT μ ν hμ hν) ⟨ψ, hψ, rfl⟩) hA

private lemma pe4p5c_bl_scaled {Cs A : ℝ} (hA : 0 < A)
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0)
    (g : ℝ × ℝ → ℝ) (hb : ∀ x ∈ specRect Cs, |g x| ≤ A)
    (hl : ∀ x ∈ specRect Cs, ∀ y ∈ specRect Cs, |g x - g y| ≤ A * l1 x y) :
    |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤ A * blDist Cs μ ν := by
  refine pe4p5c_test_scaled (blTest Cs) (fun φ hφ => hφ.1) μ ν hμ hν g
    (fun x => g x / A) ?_ hA.le ?_
  · refine ⟨?_, ?_⟩
    · intro x hx
      rw [abs_div, abs_of_pos hA]
      exact (div_le_one hA).2 (hb x hx)
    · intro x hx y hy
      rw [← sub_div, abs_div, abs_of_pos hA]
      exact (div_le_iff₀ hA).2 (by simpa only [mul_comm] using hl x hx y hy)
  · intro x _
    field_simp

private lemma pe4p5c_risk_diff_le {Cs : ℝ} (hC : 1 ≤ Cs)
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0) :
    |riskOf μ - riskOf ν| ≤ (1 / 2) * Cs ^ 2 * blDist Cs μ ν := by
  have hC0 : 0 ≤ Cs := zero_le_one.trans hC
  have hCpos : 0 < Cs := zero_lt_one.trans_le hC
  have hscaled := pe4p5c_bl_scaled (sq_pos_of_pos hCpos) μ ν hμ hν
    (fun x => x.1 * x.2) (by
      intro x hx
      rw [abs_of_nonneg (mul_nonneg hx.1.1 hx.2.1)]
      calc
        x.1 * x.2 ≤ Cs * Cs := mul_le_mul hx.1.2 hx.2.2 hx.2.1 hC0
        _ = Cs ^ 2 := by ring) (by
      intro x hx y hy
      have hxabs : |x.1| ≤ Cs := by rw [abs_of_nonneg hx.1.1]; exact hx.1.2
      have hyabs : |y.2| ≤ Cs := by rw [abs_of_nonneg hy.2.1]; exact hy.2.2
      have htri : |x.1 * x.2 - y.1 * y.2| ≤
          |x.1| * |x.2 - y.2| + |y.2| * |x.1 - y.1| := by
        rw [show x.1 * x.2 - y.1 * y.2 =
          x.1 * (x.2 - y.2) + y.2 * (x.1 - y.1) by ring]
        exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])
      calc
        |x.1 * x.2 - y.1 * y.2| ≤
            |x.1| * |x.2 - y.2| + |y.2| * |x.1 - y.1| := htri
        _ ≤ Cs * |x.2 - y.2| + Cs * |x.1 - y.1| :=
          add_le_add (mul_le_mul_of_nonneg_right hxabs (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hyabs (abs_nonneg _))
        _ = Cs * l1 x y := by unfold l1; ring
        _ ≤ Cs ^ 2 * l1 x y :=
          mul_le_mul_of_nonneg_right (by nlinarith) (by unfold l1; positivity))
  unfold riskOf
  rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2) * |∫ (x : ℝ × ℝ), x.1 * x.2 ∂μ - ∫ (x : ℝ × ℝ), x.1 * x.2 ∂ν| ≤
        (1 / 2) * (Cs ^ 2 * blDist Cs μ ν) :=
      mul_le_mul_of_nonneg_left hscaled (by norm_num)
    _ = (1 / 2) * Cs ^ 2 * blDist Cs μ ν := by ring

/-- `cor:app-dyn-continuum`(iv), snapshot `cr-2026-10-23`. Probabilistic part on the risk: along any subsequence
`ι` on which the limits of (i) hold, for every solution `χ` of `eqn_app_dyn_continuum`,
`sup_τ |𝓡(⌊Bτ⌋) − 𝓡(χ(τ))| → 0` in probability, with `𝓡(χ) = riskOf χ` and `𝓡(Δ) = riskSigma`. Takes `hc`.

Source (`section.tex`, whole environment):
```latex
\begin{corollary}[Continuum equation]\label{cor:app-dyn-continuum}
Assume the hypotheses of \cref{thm:app-dyn-main}, and write $\mathfrak d_B$,
$\zeta_B$, $\chi^{\mathrm{act}}_B$, $\chi^{\mathrm{ode}}_B$ for the objects
at the dimension indexed by $B$.
\begin{enumerate}[label=(\roman*)]
\item Every sequence of dimensions has a subsequence along which $\mathfrak d_B\to\mathfrak d_\infty$
uniformly on $\mathbb K$, $\zeta_B\to\zeta_\infty$ weakly and
$\chi^{\mathrm{act}}_B(0)\to\chi_0$ weakly.
\item Along any such subsequence, the measure equation
\begin{equation}\label{eqn:app-dyn-continuum}
\chi(\macrotime)=\chi_0+\int_0^\macrotime\Big(-\frac{2\macrostep\,\mathfrak d_\infty\,\chi(\sigma)}{\sqrt{\fRisk(\chi(\sigma))}}+\macrostep^2\zeta_\infty\Big)\dif\sigma
\end{equation}
has a unique solution $\chi$ on $[0,T_\star]$ among paths with values in
$\mathfrak M$ that are continuous for the bounded-Lipschitz norm, and
\[
\sup_{\macrotime\le T_\star}\norm{\chi^{\mathrm{ode}}_B(\macrotime)-\chi(\macrotime)}_\BL\to0,\qquad
\sup_{\macrotime\le T_\star}\norm{\chi^{\mathrm{act}}_B(\macrotime)-\chi(\macrotime)}_\BL\to0\ \text{in probability}.
\]
\item Along any such subsequence,
$\sup_{\macrotime\le T_\star}\abs{\cR(\lfloor B\macrotime\rfloor)-\fRisk(\chi(\macrotime))}\to0$ in probability.
\end{enumerate}
\end{corollary}
```

Relocated here from `Muon.Dynamics.Corollaries` by the coordinator (2026-10-24): its proof needs results of this
module, which imports the original one. -/
theorem cor_app_dyn_continuum_iv (certOp : Muon.External.GaussianOpNormL6) (certP : Muon.External.GaussianPoincare) (certQ : Muon.External.GaussianQuadFormLp) (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C)) (hB : Tendsto B atTop atTop)
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (cert : Muon.External.GaussianOpNorm) (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k))
    (ι : ℕ → ℕ) (hι : StrictMono ι) (dinf : ℝ × ℝ → ℝ) (ζinf χ0 : Measure (ℝ × ℝ))
    (hL : contLimit hyp S c ι dinf ζinf χ0) (χ : ℝ → Measure (ℝ × ℝ))
    (hχ : eqn_app_dyn_continuum p dinf ζinf χ0 χ) :
    (∀ n : ℕ, ∀ ω : Ω, BddAbove ((fun τ => |riskSigma (F (ι n)).C (errPath hyp (ι n)
        ⌊((B (ι n) : ℕ) : ℝ) * τ⌋₊ ω) - riskOf (χ τ)|) '' Icc 0 (Tstar p))) ∧
    ∀ ε > 0, Tendsto (fun n : ℕ => P {ω | ε < sSup ((fun τ => |riskSigma (F (ι n)).C (errPath hyp (ι n)
        ⌊((B (ι n) : ℕ) : ℝ) * τ⌋₊ ω) - riskOf (χ τ)|) '' Icc 0 (Tstar p))}) atTop (𝓝 0) := by
  obtain ⟨hbd, hconv⟩ := cor_app_dyn_continuum_iii certOp certP certQ F hyp hB S c
    cert hc ι hι dinf ζinf χ0 hL χ hχ
  let K : ℝ := (1 / 2) * p.CSig ^ 2
  have hKpos : 0 < K := by
    dsimp only [K]
    have hCs : 0 < p.CSig := zero_lt_one.trans_le p.hC
    positivity
  have hK0 : 0 ≤ K := hKpos.le
  have hrisk : ∀ (n : ℕ) (ω : Ω) (τ : ℝ), τ ∈ Icc 0 (Tstar p) →
      |riskSigma (F (ι n)).C (errPath hyp (ι n) ⌊(B (ι n) : ℝ) * τ⌋₊ ω) -
        riskOf (χ τ)| ≤
      K * blDist p.CSig (actMeas hyp S (ι n) ω τ) (χ τ) := by
    intro n ω τ hτ
    haveI : IsFiniteMeasure (actMeas hyp S (ι n) ω τ) := by
      unfold actMeas actMeasure
      exact spec_isFinite (S (ι n)) _
    have hact : actMeas hyp S (ι n) ω τ (specRect p.CSig)ᶜ = 0 := by
      unfold actMeas actMeasure
      exact spec_support (S (ι n)) _ p.CSig (hyp.normBd (ι n)).2 (hyp.normBd (ι n)).1
    have hχadm := hχ.2.1 τ hτ
    unfold admMeasures Adm at hχadm
    letI : IsFiniteMeasure (χ τ) := hχadm.1
    have hχsupp : χ τ (specRect p.CSig)ᶜ = 0 := hχadm.2.1
    have h := pe4p5c_risk_diff_le p.hC (actMeas hyp S (ι n) ω τ) (χ τ) hact hχsupp
    simpa only [K, actMeas, actMeasure, spec_risk] using h
  have hriskBdd : ∀ n : ℕ, ∀ ω : Ω,
      BddAbove ((fun τ => |riskSigma (F (ι n)).C (errPath hyp (ι n)
        ⌊((B (ι n) : ℕ) : ℝ) * τ⌋₊ ω) - riskOf (χ τ)|) '' Icc 0 (Tstar p)) := by
    intro n ω
    obtain ⟨M, hM⟩ := hbd n ω
    refine ⟨K * M, ?_⟩
    rintro z ⟨τ, hτ, rfl⟩
    exact (hrisk n ω τ hτ).trans
      (mul_le_mul_of_nonneg_left (hM ⟨τ, hτ, rfl⟩) hK0)
  refine ⟨hriskBdd, ?_⟩
  intro ε hε
  have hεK : 0 < ε / K := div_pos hε hKpos
  have htend := hconv (ε / K) hεK
  have hT : 0 ≤ Tstar p := by
    unfold Tstar
    exact div_nonneg (le_of_lt (lt_min p.hr0 zero_lt_one))
      (mul_nonneg (by norm_num) (by linarith [CE_nonneg'' p, CR_nonneg'' p]))
  have hne : (Icc (0 : ℝ) (Tstar p)).Nonempty := nonempty_Icc.2 hT
  have hsub : ∀ n : ℕ,
      {ω | ε < sSup ((fun τ => |riskSigma (F (ι n)).C (errPath hyp (ι n)
        ⌊((B (ι n) : ℕ) : ℝ) * τ⌋₊ ω) - riskOf (χ τ)|) '' Icc 0 (Tstar p))} ⊆
      {ω | ε / K < sSup ((fun τ => blDist p.CSig
        (actMeas hyp S (ι n) ω τ) (χ τ)) '' Icc 0 (Tstar p))} := by
    intro n ω hω
    have hsup : sSup ((fun τ => |riskSigma (F (ι n)).C (errPath hyp (ι n)
          ⌊((B (ι n) : ℕ) : ℝ) * τ⌋₊ ω) - riskOf (χ τ)|) '' Icc 0 (Tstar p)) ≤
        K * sSup ((fun τ => blDist p.CSig
          (actMeas hyp S (ι n) ω τ) (χ τ)) '' Icc 0 (Tstar p)) := by
      apply csSup_le (hne.image _)
      rintro z ⟨τ, hτ, rfl⟩
      exact (hrisk n ω τ hτ).trans (mul_le_mul_of_nonneg_left
        (le_csSup (hbd n ω) ⟨τ, hτ, rfl⟩) hK0)
    have he : ε < K * sSup ((fun τ => blDist p.CSig
        (actMeas hyp S (ι n) ω τ) (χ τ)) '' Icc 0 (Tstar p)) := hω.trans_le hsup
    exact (div_lt_iff₀ hKpos).2 (by simpa only [mul_comm] using he)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun n => measure_mono (hsub n))

end Muon.Dynamics

end

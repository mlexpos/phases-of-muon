import Muon.Foundations.Conventions
import Muon.Setup.Basic
import Muon.Setup.Model
import Muon.Setup.RegularizedMap
import Muon.Foundations.Freezing

/-!
# Appendix A: the algorithm, the conditional risk recursion, and the support event

Snapshot `cr-2026-10-23`. Source: `sections/01-setup/section.tex`, algorithm (`def:app-setup-algorithm`,
`eqn:app-setup-unrolled`, `eqn:app-setup-nomomentum`), recursion (`prop:app-setup-risk-recursion`,
`cor:app-setup-augmented`), support (`prop:app-setup-support`). Card: `sections/01-setup/CARD.md`
§2, §3, §5 row L-A.5.

Representation choices:
* The update is `G̃_t = 0` when `𝓡(t) = 0` and `Q_{2𝓡(t)ϱ}(M°_t)` otherwise (card rule). Zero risk is
  absorbing: at zero risk the update vanishes, so the iterate is frozen (`update_eq_zero_iff`).
  `stepUpdate_eq_paper` gives the literal `t < t_stop` form of the paper.
* `tstop` is the first zero of the trajectory risk, as an element of `ℕ∞` (`⊤` if none).
* Matrix-valued conditional expectations are entrywise (`Mat` carries no norm instance).
-/

noncomputable section

open scoped Matrix MatrixOrder Classical
open Matrix MeasureTheory ProbabilityTheory

namespace Muon.Setup

variable {m n : ℕ}

/-! ## Parameters, state and one step -/

/-- Algorithm parameters: momentum `β`, normalized ridge `ϱ > 0`, step sizes `η t ≥ 0`, and the
population minimizer `W⋆` (`def:app-setup-algorithm`). -/
structure AlgParams (m n : ℕ) where
  β : ℝ
  ϱ : ℝ
  hβ : 0 ≤ β ∧ β < 1
  hϱ : 0 < ϱ
  η : ℕ → ℝ
  hη : ∀ t, 0 ≤ η t
  Wstar : Mat m n

/-- State before step `t`: the iterate `W_t` and the buffer `M°_{t-1}`. -/
structure AlgState (m n : ℕ) where
  W : Mat m n
  Mprev : Mat m n

/-- Initial state. -/
def initState (W0 Mm1 : Mat m n) : AlgState m n := ⟨W0, Mm1⟩

/-- The error `Δ = W − W⋆` of a state. -/
def errorOf (p : AlgParams m n) (s : AlgState m n) : Mat m n := s.W - p.Wstar

/-- Buffer after step `t`: `M°_t = β M°_{t-1} + (1-β) G°_{t+1}`, where `G°_{t+1}` is the minibatch
gradient at `Δ_t` computed from the batch `b` of step `t` (`def:app-setup-algorithm`). -/
def stepBuffer (p : AlgParams m n) {B : ℕ} (s : AlgState m n) (b : Batch m n B) : Mat m n :=
  p.β • s.Mprev + (1 - p.β) • grad (errorOf p s) b

/-- Update `G̃_t` of step `t`: `0` at zero risk, otherwise `Q_{2𝓡(t)ϱ}(M°_t)`
(`eqn:app-setup-algorithm`, with `ridgephys_t = 2𝓡(t)ϱ`). -/
def stepUpdate (C : Covariances m n) (p : AlgParams m n) {B : ℕ} (s : AlgState m n)
    (b : Batch m n B) : Mat m n :=
  if riskSigma C (errorOf p s) = 0 then 0
  else Q (2 * riskSigma C (errorOf p s) * p.ϱ) (stepBuffer p s b)

/-- One step `(W_t, M°_{t-1}) ↦ (W_{t+1}, M°_t)` with `W_{t+1} = W_t − η_t G̃_t`. -/
def step (C : Covariances m n) (p : AlgParams m n) {B : ℕ} (t : ℕ) (s : AlgState m n)
    (b : Batch m n B) : AlgState m n :=
  { W := s.W - p.η t • stepUpdate C p s b
    Mprev := stepBuffer p s b }

/-- Pathwise trajectory: `run C p s₀ x t` is the state before step `t`, driven by the batches
`x u` of the steps `u < t`. -/
def run (C : Covariances m n) (p : AlgParams m n) {B : ℕ} (s₀ : AlgState m n)
    (x : ℕ → Batch m n B) : ℕ → AlgState m n
  | 0 => s₀
  | t + 1 => step C p t (run C p s₀ x t) (x t)

/-- The stopping time `t_stop = inf {t : 𝓡(t) = 0}` of the trajectory, with values in `ℕ∞`
(`⊤` if the risk never vanishes). -/
def tstop (C : Covariances m n) (p : AlgParams m n) {B : ℕ} (s₀ : AlgState m n)
    (x : ℕ → Batch m n B) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : riskSigma C (errorOf p (run C p s₀ x t)) = 0), (t : ℕ∞)

/-- `def:app-setup-algorithm`, the algorithm (trajectory and stopping time), snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.408–423):

```latex
\begin{definition}[The algorithm]\label{def:app-setup-algorithm}
Fix a momentum $\bmom\in[0,1)$, a normalized ridge $\ridge>0$, a
deterministic step sequence $(\lr_t)_{t\ge0}$ with $\lr_t\ge0$, an initial
parameter $W_0$ and an initial buffer $M_{-1}^\circ\in\R^{\Nout\times\Nin}$,
both given before the first batch is drawn (the default is $M_{-1}^\circ=0$).
Let $t_{\mathrm{stop}}\defeq\inf\{t\ge0:\cR(t)=0\}\in\{0,1,\dots\}\cup\{\infty\}$.
The algorithm is, for $t\ge0$,
\begin{equation}\label{eqn:app-setup-algorithm}
\begin{gathered}
M_t^\circ=\bmom\,M_{t-1}^\circ+(1-\bmom)\,\Gt^\circ,\qquad
W_{t+1}=\Wt-\lr_t\,\Gtilde^\circ,\\
\Gtilde^\circ\defeq\begin{cases}\Qridge{\ridgephys_t}(M_t^\circ),&t<t_{\mathrm{stop}},\\ 0,&t\ge t_{\mathrm{stop}},\end{cases}
\qquad \ridgephys_t\defeq2\cR(t)\,\ridge .
\end{gathered}
\end{equation}
\end{definition}
```
-/
def def_app_setup_algorithm (C : Covariances m n) (p : AlgParams m n) {B : ℕ}
    (s₀ : AlgState m n) (x : ℕ → Batch m n B) : (ℕ → AlgState m n) × ℕ∞ :=
  (run C p s₀ x, tstop C p s₀ x)

/-! ## Random version -/

/-- Random trajectory: `s₀ : Ω → AlgState`, batches `x u : Ω → Batch`. -/
def runRand (C : Covariances m n) (p : AlgParams m n) {Ω : Type*} {B : ℕ}
    (s₀ : Ω → AlgState m n) (x : ℕ → Ω → Batch m n B) (t : ℕ) (ω : Ω) : AlgState m n :=
  run C p (s₀ ω) (fun u => x u ω) t

/-- Random error `Δ_t`. -/
def devRand (C : Covariances m n) (p : AlgParams m n) {Ω : Type*} {B : ℕ}
    (s₀ : Ω → AlgState m n) (x : ℕ → Ω → Batch m n B) (t : ℕ) : Ω → Mat m n :=
  fun ω => errorOf p (runRand C p s₀ x t ω)

/-- Random update `G̃_t`. -/
def gtRand (C : Covariances m n) (p : AlgParams m n) {Ω : Type*} {B : ℕ}
    (s₀ : Ω → AlgState m n) (x : ℕ → Ω → Batch m n B) (t : ℕ) : Ω → Mat m n :=
  fun ω => stepUpdate C p (runRand C p s₀ x t ω) (x t ω)

/-- Random stopping time `t_stop`. -/
def tstopRand (C : Covariances m n) (p : AlgParams m n) {Ω : Type*} {B : ℕ}
    (s₀ : Ω → AlgState m n) (x : ℕ → Ω → Batch m n B) : Ω → ℕ∞ :=
  fun ω => tstop C p (s₀ ω) (fun u => x u ω)

/-! ## Conditional mode quantities (`eqn:app-setup-DV`) -/

/-- `eqn:app-setup-DV`, definition of 𝒟_ij, snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.494–497):

```latex
\begin{equation}\label{eqn:app-setup-DV}
\cD_{ij}(t)\defeq(u_i^\T\Dt v_j)\,\EE_t\big[u_i^\T {\mathsf S}v_j\big],\qquad
\cV_{ij}(t)\defeq\EE_t\big[(u_i^\T {\mathsf S}v_j)^2\big].
\end{equation}
```
-/
def condDrift {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝒢 : MeasurableSpace Ω)
    {C : Covariances m n} (S : SpectralData C) (Δ U : Ω → Mat m n) (i : Fin m) (j : Fin n) :
    Ω → ℝ :=
  fun ω => (S.u i ⬝ᵥ (Δ ω *ᵥ S.v j)) * condExp 𝒢 P (fun ω' => S.u i ⬝ᵥ (U ω' *ᵥ S.v j)) ω

/-- `eqn:app-setup-DV`, definition of 𝒱_ij, snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.494–497):

```latex
\begin{equation}\label{eqn:app-setup-DV}
\cD_{ij}(t)\defeq(u_i^\T\Dt v_j)\,\EE_t\big[u_i^\T {\mathsf S}v_j\big],\qquad
\cV_{ij}(t)\defeq\EE_t\big[(u_i^\T {\mathsf S}v_j)^2\big].
\end{equation}
```
-/
def condVol {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝒢 : MeasurableSpace Ω)
    {C : Covariances m n} (S : SpectralData C) (U : Ω → Mat m n) (i : Fin m) (j : Fin n) :
    Ω → ℝ :=
  condExp 𝒢 P (fun ω' => (S.u i ⬝ᵥ (U ω' *ᵥ S.v j)) ^ 2)

/-! ## Support projections and batch support -/

/-- Output support projection `P_out = ∑_{μ_i > 0} u_i ⊗ u_i`. -/
def projOut {C : Covariances m n} (S : SpectralData C) : Mat m m :=
  ∑ i, if 0 < S.μ i then outer (S.u i) (S.u i) else 0

/-- Input support projection `P_in = ∑_{λ_j > 0} v_j ⊗ v_j`. -/
def projIn {C : Covariances m n} (S : SpectralData C) : Mat n n :=
  ∑ j, if 0 < S.lam j then outer (S.v j) (S.v j) else 0

/-- A minibatch lies in the support: every sample has zero component along each zero mode. -/
def BatchSupported {C : Covariances m n} (S : SpectralData C) {B : ℕ} (b : Batch m n B) : Prop :=
  (∀ a i, S.μ i = 0 → S.u i ⬝ᵥ (b a).1 = 0) ∧ (∀ a j, S.lam j = 0 → S.v j ⬝ᵥ (b a).2 = 0)

/-! ## Statements -/

/-- `eqn:app-setup-unrolled`, unrolled buffer, snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.444–447):

```latex
\begin{equation}\label{eqn:app-setup-unrolled}
M_t^\circ=\bmom^{t+1}M_{-1}^\circ+\sum_{j=0}^t\emaw{j}\,G^\circ_{t+1-j},\qquad
\emaw{j}\defeq(1-\bmom)\bmom^j ,
\end{equation}
```
-/
theorem eqn_app_setup_unrolled (C : Covariances m n) (p : AlgParams m n) {B : ℕ}
    (s₀ : AlgState m n) (x : ℕ → Batch m n B) (t : ℕ) :
    (run C p s₀ x (t + 1)).Mprev
      = p.β ^ (t + 1) • s₀.Mprev
        + ∑ j ∈ Finset.range (t + 1),
            emaW p.β j • grad (errorOf p (run C p s₀ x (t - j))) (x (t - j)) := by
  induction t with
  | zero =>
    simp [run, step, stepBuffer, emaW]
  | succ k ih =>
    have key : ∑ i ∈ Finset.range (k + 1), emaW p.β (i + 1)
          • grad (errorOf p (run C p s₀ x (k - i))) (x (k - i))
        = p.β • ∑ i ∈ Finset.range (k + 1), emaW p.β i
          • grad (errorOf p (run C p s₀ x (k - i))) (x (k - i)) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
      congr 1
      unfold emaW
      ring
    show stepBuffer p (run C p s₀ x (k + 1)) (x (k + 1)) = _
    unfold stepBuffer
    rw [ih, Finset.sum_range_succ' _ (k + 1)]
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [key]
    simp only [emaW, pow_zero, mul_one]
    module

/-! ### Private helpers used by the targets below (copies of later lemmas, stated early) -/

private lemma aux_sqrt_transpose {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) :
    (CFC.sqrt A)ᵀ = CFC.sqrt A := by
  have h : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma aux_sqrt_mul_self {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.PosSemidef) :
    CFC.sqrt A * CFC.sqrt A = A :=
  CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.mpr hA)

/-- Trace identity for a Gram form, with square roots as abstract factors. -/
private lemma aux_trace_gram {k l : ℕ} (r : Matrix (Fin k) (Fin k) ℝ) (s : Matrix (Fin l) (Fin l) ℝ)
    (hrT : rᵀ = r) (hsT : sᵀ = s) (Δ : Matrix (Fin k) (Fin l) ℝ) :
    ((r * r) * Δ * (s * s) * Δᵀ).trace = ((r * Δ * s) * (r * Δ * s)ᴴ).trace := by
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  simp only [Matrix.transpose_mul, hrT, hsT, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- Risk is nonnegative (trace of a Gram matrix). -/
private lemma aux_riskSigma_nonneg {m n : ℕ} (C : Covariances m n) (Δ : Mat m n) :
    0 ≤ riskSigma C Δ := by
  have hr : CFC.sqrt C.Sout * CFC.sqrt C.Sout = C.Sout := aux_sqrt_mul_self _ C.psdOut
  have hs : CFC.sqrt C.Sin * CFC.sqrt C.Sin = C.Sin := aux_sqrt_mul_self _ C.psdIn
  have htr := (Matrix.posSemidef_self_mul_conjTranspose
    (CFC.sqrt C.Sout * Δ * CFC.sqrt C.Sin)).trace_nonneg
  have heq : pairSigma C Δ Δ
      = ((CFC.sqrt C.Sout * Δ * CFC.sqrt C.Sin)
          * (CFC.sqrt C.Sout * Δ * CFC.sqrt C.Sin)ᴴ).trace := by
    have key := aux_trace_gram (CFC.sqrt C.Sout) (CFC.sqrt C.Sin)
      (aux_sqrt_transpose _) (aux_sqrt_transpose _) Δ
    rw [hr, hs] at key
    unfold pairSigma
    exact key
  unfold riskSigma
  rw [heq]
  positivity

private lemma aux_risk_succ (C : Covariances m n) (p : AlgParams m n) {B : ℕ}
    (s₀ : AlgState m n) (x : ℕ → Batch m n B) (u : ℕ)
    (hu : riskSigma C (errorOf p (run C p s₀ x u)) = 0) :
    riskSigma C (errorOf p (run C p s₀ x (u + 1))) = 0 := by
  have h0 : stepUpdate C p (run C p s₀ x u) (x u) = 0 := by
    unfold stepUpdate
    rw [if_pos hu]
  have hE : errorOf p (run C p s₀ x (u + 1)) = errorOf p (run C p s₀ x u) := by
    simp only [run, step, errorOf, h0, smul_zero, sub_zero]
  rw [hE]
  exact hu

private lemma aux_risk_le (C : Covariances m n) (p : AlgParams m n) {B : ℕ}
    (s₀ : AlgState m n) (x : ℕ → Batch m n B) (u t : ℕ) (hut : u ≤ t)
    (hu : riskSigma C (errorOf p (run C p s₀ x u)) = 0) :
    riskSigma C (errorOf p (run C p s₀ x t)) = 0 := by
  induction t, hut using Nat.le_induction with
  | base => exact hu
  | succ k _ ih => exact aux_risk_succ C p s₀ x k ih

/-- The stopping time is strictly after `t` exactly when the risk at `t` is nonzero. -/
private lemma aux_lt_tstop_iff (C : Covariances m n) (p : AlgParams m n) {B : ℕ}
    (s₀ : AlgState m n) (x : ℕ → Batch m n B) (t : ℕ) :
    (t : ℕ∞) < tstop C p s₀ x ↔ riskSigma C (errorOf p (run C p s₀ x t)) ≠ 0 := by
  constructor
  · intro h hR
    have hle : tstop C p s₀ x ≤ (t : ℕ∞) := by
      unfold tstop
      exact iInf_le_of_le t (iInf_le_of_le hR le_rfl)
    exact absurd h (not_lt.mpr hle)
  · intro hR
    by_contra hnot
    push_neg at hnot
    have hex : ∃ u ≤ t, riskSigma C (errorOf p (run C p s₀ x u)) = 0 := by
      by_contra hne
      push_neg at hne
      have h1 : ((t + 1 : ℕ) : ℕ∞) ≤ tstop C p s₀ x := by
        unfold tstop
        refine le_iInf fun u => le_iInf fun hu => ?_
        have hut : t < u := by
          by_contra hle
          exact hne u (by omega) hu
        exact_mod_cast (show t + 1 ≤ u by omega)
      have h2 : ((t + 1 : ℕ) : ℕ∞) ≤ (t : ℕ∞) := le_trans h1 hnot
      have h3 : t + 1 ≤ t := by exact_mod_cast h2
      omega
    obtain ⟨u, hut, hu⟩ := hex
    exact hR (aux_risk_le C p s₀ x u t hut hu)

/-- A vector expansion in an orthogonal basis (columns of `A`). -/
private lemma aux_expand {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : Aᵀ * A = 1)
    (x : Fin k → ℝ) :
    ∑ i, ((fun r => A r i) ⬝ᵥ x) • (fun r => A r i) = x := by
  have hAA : A * Aᵀ = 1 := mul_eq_one_comm.mp hA
  have h2 : (A * Aᵀ) *ᵥ x = x := by rw [hAA, Matrix.one_mulVec]
  ext r
  have hr := congrFun h2 r
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hr ⊢
  rw [Finset.sum_comm] at hr
  rw [← hr]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring

private lemma aux_outer_mulVec {m : ℕ} (u x : Vec m) :
    outer u u *ᵥ x = (u ⬝ᵥ x) • u := by
  ext r
  simp only [Matrix.mulVec, dotProduct, outer, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- `eqn:app-setup-nomomentum`, momentum-free update, snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.436–439):

```latex
\begin{equation}\label{eqn:app-setup-nomomentum}
\Gtilde^\circ=\Qridge{2\cR(t)\ridge}(\Gt^\circ)=\Qridge{\ridge}(\Gt)
\qquad(t<t_{\mathrm{stop}}),
\end{equation}
```
-/
theorem eqn_app_setup_nomomentum (C : Covariances m n) (p : AlgParams m n) (hβ : p.β = 0)
    {B : ℕ} (s₀ : AlgState m n) (x : ℕ → Batch m n B) (t : ℕ)
    (ht : (t : ℕ∞) < tstop C p s₀ x) :
    stepUpdate C p (run C p s₀ x t) (x t)
        = Q (2 * riskSigma C (errorOf p (run C p s₀ x t)) * p.ϱ)
            (grad (errorOf p (run C p s₀ x t)) (x t))
      ∧ Q (2 * riskSigma C (errorOf p (run C p s₀ x t)) * p.ϱ)
            (grad (errorOf p (run C p s₀ x t)) (x t))
          = Q p.ϱ (Gnorm C (errorOf p (run C p s₀ x t)) (x t)) := by
  have hR : riskSigma C (errorOf p (run C p s₀ x t)) ≠ 0 := (aux_lt_tstop_iff C p s₀ x t).mp ht
  have hRpos : 0 < riskSigma C (errorOf p (run C p s₀ x t)) :=
    lt_of_le_of_ne (aux_riskSigma_nonneg C _) (Ne.symm hR)
  have hbuf : stepBuffer p (run C p s₀ x t) (x t)
      = grad (errorOf p (run C p s₀ x t)) (x t) := by
    simp [stepBuffer, hβ]
  have hstep : stepUpdate C p (run C p s₀ x t) (x t)
      = Q (2 * riskSigma C (errorOf p (run C p s₀ x t)) * p.ϱ)
          (grad (errorOf p (run C p s₀ x t)) (x t)) := by
    unfold stepUpdate
    rw [if_neg hR, hbuf]
  have hsq : Real.sqrt (2 * riskSigma C (errorOf p (run C p s₀ x t))) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith)).ne'
  have hG : grad (errorOf p (run C p s₀ x t)) (x t)
      = Real.sqrt (2 * riskSigma C (errorOf p (run C p s₀ x t)))
          • Gnorm C (errorOf p (run C p s₀ x t)) (x t) := by
    unfold Gnorm
    rw [smul_smul, mul_inv_cancel₀ hsq, one_smul]
  refine ⟨hstep, ?_⟩
  rw [hG, prop_app_setup_scaling_ii _ p.hϱ.le _ _ hRpos]

/-- The stopping rule of `def:app-setup-algorithm` in literal form: `G̃_t = Q_{ridgephys_t}(M°_t)`
if `t < t_stop`, and `0` otherwise. -/
theorem stepUpdate_eq_paper (C : Covariances m n) (p : AlgParams m n) {B : ℕ}
    (s₀ : AlgState m n) (x : ℕ → Batch m n B) (t : ℕ) :
    stepUpdate C p (run C p s₀ x t) (x t)
      = if (t : ℕ∞) < tstop C p s₀ x then
          Q (2 * riskSigma C (errorOf p (run C p s₀ x t)) * p.ϱ)
            (stepBuffer p (run C p s₀ x t) (x t))
        else 0 := by
  by_cases hR : riskSigma C (errorOf p (run C p s₀ x t)) = 0
  · have h1 : ¬ ((t : ℕ∞) < tstop C p s₀ x) := fun h => (aux_lt_tstop_iff C p s₀ x t).mp h hR
    rw [if_neg h1]
    unfold stepUpdate
    rw [if_pos hR]
  · have h1 : (t : ℕ∞) < tstop C p s₀ x := (aux_lt_tstop_iff C p s₀ x t).mpr hR
    rw [if_pos h1]
    unfold stepUpdate
    rw [if_neg hR]

/-- Private helper: zero risk at `u` gives zero update at step `u`, hence the iterate is frozen. -/
private lemma risk_succ_of_zero (C : Covariances m n) (p : AlgParams m n) {B : ℕ}
    (s₀ : AlgState m n) (x : ℕ → Batch m n B) (u : ℕ)
    (hu : riskSigma C (errorOf p (run C p s₀ x u)) = 0) :
    riskSigma C (errorOf p (run C p s₀ x (u + 1))) = 0 := by
  have h0 : stepUpdate C p (run C p s₀ x u) (x u) = 0 := by
    unfold stepUpdate
    rw [if_pos hu]
  have hE : errorOf p (run C p s₀ x (u + 1)) = errorOf p (run C p s₀ x u) := by
    simp only [run, step, errorOf, h0, smul_zero, sub_zero]
  rw [hE]
  exact hu

/-- Private helper: zero risk persists for all later times. -/
private lemma risk_zero_of_le (C : Covariances m n) (p : AlgParams m n) {B : ℕ}
    (s₀ : AlgState m n) (x : ℕ → Batch m n B) (u t : ℕ) (hut : u ≤ t)
    (hu : riskSigma C (errorOf p (run C p s₀ x u)) = 0) :
    riskSigma C (errorOf p (run C p s₀ x t)) = 0 := by
  induction t, hut using Nat.le_induction with
  | base => exact hu
  | succ k _ ih => exact risk_succ_of_zero C p s₀ x k ih

/-- Private helper: the characterization of `tstop` (proof of `tstop_le_iff`). -/
private lemma tstop_le_iff_aux (C : Covariances m n) (p : AlgParams m n) {B : ℕ}
    (s₀ : AlgState m n) (x : ℕ → Batch m n B) (t : ℕ) :
    tstop C p s₀ x ≤ (t : ℕ∞)
      ↔ ∃ u ≤ t, riskSigma C (errorOf p (run C p s₀ x u)) = 0 := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have h1 : ((t + 1 : ℕ) : ℕ∞) ≤ tstop C p s₀ x := by
      unfold tstop
      refine le_iInf fun u => le_iInf fun hu => ?_
      have hut : t < u := by
        by_contra hle
        exact hne u (by omega) hu
      exact_mod_cast (show t + 1 ≤ u by omega)
    have h2 : ((t + 1 : ℕ) : ℕ∞) ≤ (t : ℕ∞) := le_trans h1 h
    have h3 : t + 1 ≤ t := by exact_mod_cast h2
    omega
  · rintro ⟨u, hut, hu⟩
    have hle : tstop C p s₀ x ≤ (u : ℕ∞) := by
      unfold tstop
      exact iInf_le_of_le u (iInf_le_of_le hu le_rfl)
    exact le_trans hle (by exact_mod_cast hut)

/-- Absorption at zero risk: `t ≥ t_stop` iff `𝓡(t) = 0`. The update vanishes at zero risk, so the
iterate is frozen and the risk stays zero afterwards. -/
theorem update_eq_zero_iff (C : Covariances m n) (p : AlgParams m n) {B : ℕ}
    (s₀ : AlgState m n) (x : ℕ → Batch m n B) (t : ℕ) :
    tstop C p s₀ x ≤ (t : ℕ∞)
      ↔ riskSigma C (errorOf p (run C p s₀ x t)) = 0 := by
  constructor
  · intro h
    obtain ⟨u, hut, hu⟩ := (tstop_le_iff_aux C p s₀ x t).mp h
    exact risk_zero_of_le C p s₀ x u t hut hu
  · intro h
    exact (tstop_le_iff_aux C p s₀ x t).mpr ⟨t, le_rfl, h⟩

/-- Characterization of the stopping time: `t ≥ t_stop` iff `𝓡(u) = 0` for some `u ≤ t`. -/
theorem tstop_le_iff (C : Covariances m n) (p : AlgParams m n) {B : ℕ}
    (s₀ : AlgState m n) (x : ℕ → Batch m n B) (t : ℕ) :
    tstop C p s₀ x ≤ (t : ℕ∞)
      ↔ ∃ u ≤ t, riskSigma C (errorOf p (run C p s₀ x u)) = 0 :=
  tstop_le_iff_aux C p s₀ x t

/-- The error recursion `Δ_{t+1} = Δ_t − η_t G̃_t`. -/
theorem devRand_succ (C : Covariances m n) (p : AlgParams m n) {Ω : Type*} {B : ℕ}
    (s₀ : Ω → AlgState m n) (x : ℕ → Ω → Batch m n B) (t : ℕ) (ω : Ω) :
    devRand C p s₀ x (t + 1) ω = devRand C p s₀ x t ω - p.η t • gtRand C p s₀ x t ω := by
  simp only [devRand, gtRand, runRand, run, step, errorOf]
  abel

/-- A `Mat`-valued map is measurable once all its entries are. -/
private lemma aux_measurable_mat {Ω : Type*} {σ : MeasurableSpace Ω} {F : Ω → Mat m n}
    (h : ∀ i j, Measurable[σ] fun ω => F ω i j) : Measurable[σ] F :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => h i j

/-- Joint measurability of the minibatch gradient in the error and the batch. -/
private lemma aux_grad_meas {Ω : Type*} {σ : MeasurableSpace Ω} {B : ℕ}
    {m n : ℕ} {Δ : Ω → Mat m n} {b : Ω → Batch m n B}
    (hΔ : Measurable[σ] Δ) (hb : Measurable[σ] b) :
    Measurable[σ] (fun ω => grad (Δ ω) (b ω)) := by
  have hGc : Continuous (fun pr : Mat m n × Batch m n B => grad pr.1 pr.2) := by
    unfold grad resid outer
    fun_prop
  exact Measurable.comp (g := fun pr : Mat m n × Batch m n B => grad pr.1 pr.2)
    (f := fun ω => (Δ ω, b ω)) hGc.measurable (hΔ.prodMk hb)

/-- Entries of a `Mat`-valued measurable map are measurable. -/
private lemma aux_entry {Ω : Type*} {σ : MeasurableSpace Ω} {F : Ω → Mat m n}
    (hF : Measurable[σ] F) (i : Fin m) (j : Fin n) : Measurable[σ] fun ω => F ω i j :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hF)

/-- Adaptedness of the random trajectory: `W_t` and `M°_{t-1}` at time `t` are `ℱ t`-measurable,
given `ℱ 0`-measurable initial data and the filtration of the model. -/
theorem runRand_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    [IsProbabilityMeasure ν] {B : ℕ} (hM : ModelLaw P ν B) (p : AlgParams m n)
    (s₀ : Ω → AlgState m n)
    (hs₀W : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).W i j)
    (hs₀M : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).Mprev i j) (t : ℕ) :
    (∀ i j, Measurable[hM.ℱ t] fun ω => (runRand C p s₀ hM.x t ω).W i j)
      ∧ (∀ i j, Measurable[hM.ℱ t] fun ω => (runRand C p s₀ hM.x t ω).Mprev i j) := by
  have hRc : Continuous (fun Δ : Mat m n => riskSigma C Δ) := by
    unfold riskSigma pairSigma
    fun_prop
  have hWc : Continuous (fun A : Mat m n => A - p.Wstar) := continuous_id.sub continuous_const
  have key : ∀ k : ℕ,
      Measurable[hM.ℱ k] (fun ω => (runRand C p s₀ hM.x k ω).W)
        ∧ Measurable[hM.ℱ k] (fun ω => (runRand C p s₀ hM.x k ω).Mprev) := by
    intro k
    induction k with
    | zero =>
      constructor
      · exact aux_measurable_mat fun i j => hs₀W i j
      · exact aux_measurable_mat fun i j => hs₀M i j
    | succ k ih =>
      obtain ⟨hWk, hMk⟩ := ih
      have hWk' : Measurable[hM.ℱ (k + 1)] (fun ω => (runRand C p s₀ hM.x k ω).W) :=
        hWk.mono (hM.ℱ.mono (Nat.le_succ k)) le_rfl
      have hMk' : Measurable[hM.ℱ (k + 1)] (fun ω => (runRand C p s₀ hM.x k ω).Mprev) :=
        hMk.mono (hM.ℱ.mono (Nat.le_succ k)) le_rfl
      have hx : Measurable[hM.ℱ (k + 1)] (hM.x k) := hM.x_meas k
      have hD : Measurable[hM.ℱ (k + 1)] (fun ω => errorOf p (runRand C p s₀ hM.x k ω)) :=
        hWc.measurable.comp hWk'
      have hF : Measurable[hM.ℱ (k + 1)]
          (fun ω => grad (errorOf p (runRand C p s₀ hM.x k ω)) (hM.x k ω)) :=
        aux_grad_meas hD hx
      have hbuf : Measurable[hM.ℱ (k + 1)]
          (fun ω => stepBuffer p (runRand C p s₀ hM.x k ω) (hM.x k ω)) := by
        apply aux_measurable_mat
        intro i j
        have hMij := aux_entry hMk' i j
        have hFij := aux_entry hF i j
        simp only [stepBuffer, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        exact (hMij.const_mul _).add (hFij.const_mul _)
      have hR : Measurable[hM.ℱ (k + 1)]
          (fun ω => riskSigma C (errorOf p (runRand C p s₀ hM.x k ω))) :=
        hRc.measurable.comp hD
      have hU : Measurable[hM.ℱ (k + 1)]
          (fun ω => stepUpdate C p (runRand C p s₀ hM.x k ω) (hM.x k ω)) := by
        have hset : MeasurableSet[hM.ℱ (k + 1)]
            {ω | riskSigma C (errorOf p (runRand C p s₀ hM.x k ω)) = 0} :=
          hR (measurableSet_singleton 0)
        refine Measurable.ite hset measurable_const ?_
        have hnn : ∀ ω, (0 : ℝ) ≤ 2 * riskSigma C (errorOf p (runRand C p s₀ hM.x k ω)) * p.ϱ :=
          fun ω => mul_nonneg (mul_nonneg (by norm_num) (aux_riskSigma_nonneg C _)) p.hϱ.le
        have hφ : Measurable[hM.ℱ (k + 1)]
            (fun ω => (⟨2 * riskSigma C (errorOf p (runRand C p s₀ hM.x k ω)) * p.ϱ, hnn ω⟩
              : Set.Ici (0 : ℝ))) :=
          ((hR.const_mul 2).mul_const p.ϱ).subtype_mk
        exact measurable_Q.comp (hφ.prodMk hbuf)
      constructor
      · apply aux_measurable_mat
        intro i j
        have hWij := aux_entry hWk' i j
        have hUij := aux_entry hU i j
        simp only [runRand, run, step, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        exact hWij.sub (hUij.const_mul _)
      · exact hbuf
  exact ⟨fun i j => aux_entry (key t).1 i j, fun i j => aux_entry (key t).2 i j⟩

private lemma aux_dot_meas {Ω : Type*} {σ : MeasurableSpace Ω} {F : Ω → Mat m n}
    (hF : ∀ i j, Measurable[σ] fun ω => F ω i j) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    Measurable[σ] fun ω => x ⬝ᵥ (F ω *ᵥ y) := by
  have e : (fun ω => x ⬝ᵥ (F ω *ᵥ y)) = fun ω => ∑ k, x k * ∑ l, F ω k l * y l := rfl
  rw [e]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact measurable_const.mul (Finset.measurable_sum _ fun l _ => (hF k l).mul_const (y l))

private lemma aux_dot_memLp {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {F : Ω → Mat m n}
    (hF : ∀ i j, MemLp (fun ω => F ω i j) 2 P) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    MemLp (fun ω => x ⬝ᵥ (F ω *ᵥ y)) 2 P := by
  have e : (fun ω => x ⬝ᵥ (F ω *ᵥ y)) = fun ω => ∑ k, ∑ l, (x k * y l) * F ω k l := by
    funext ω
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [e]
  refine memLp_finsetSum _ fun k _ => memLp_finsetSum _ fun l _ => ?_
  exact (hF k l).const_mul (x k * y l)

private lemma aux_mode_scalar {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (𝒢 : MeasurableSpace Ω) (h𝒢 : 𝒢 ≤ mΩ) (a b : Ω → ℝ) (η : ℝ)
    (ha : Measurable[𝒢] a) (haL : MemLp a 2 P) (hbL : MemLp b 2 P) :
    condExp 𝒢 P (fun ω => (a ω - η * b ω) ^ 2)
      =ᵐ[P] fun ω => a ω ^ 2 - 2 * η * (a ω * condExp 𝒢 P b ω)
        + η ^ 2 * condExp 𝒢 P (fun ω' => b ω' ^ 2) ω := by
  have hA2 : Integrable (fun ω => a ω ^ 2) P := haL.integrable_sq
  have hB2 : Integrable (fun ω => b ω ^ 2) P := hbL.integrable_sq
  have hAB : Integrable (fun ω => a ω * b ω) P := memLp_one_iff_integrable.1 (haL.mul hbL)
  have hBint : Integrable b P := hbL.integrable one_le_two
  have hE1 : condExp 𝒢 P (fun ω => a ω ^ 2) = fun ω => a ω ^ 2 :=
    condExp_of_stronglyMeasurable h𝒢 ((ha.pow_const 2).stronglyMeasurable) hA2
  have hE2 : condExp 𝒢 P (fun ω => a ω * b ω) =ᵐ[P] fun ω => a ω * condExp 𝒢 P b ω :=
    condExp_mul_of_stronglyMeasurable_left ha.stronglyMeasurable hAB hBint
  have e : (fun ω => (a ω - η * b ω) ^ 2)
      = (fun ω => a ω ^ 2) + ((-(2 * η)) • fun ω => a ω * b ω) + (η ^ 2 • fun ω => b ω ^ 2) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hi2 : Integrable ((-(2 * η)) • fun ω => a ω * b ω) P := hAB.smul _
  have hi3 : Integrable (η ^ 2 • fun ω => b ω ^ 2) P := hB2.smul _
  rw [e]
  have h1 := condExp_add (hA2.add hi2) hi3 𝒢
  have h2 := condExp_add hA2 hi2 𝒢
  have h3 := condExp_smul (μ := P) (-(2 * η)) (fun ω => a ω * b ω) 𝒢
  have h4 := condExp_smul (μ := P) (η ^ 2) (fun ω => b ω ^ 2) 𝒢
  filter_upwards [h1, h2, h3, h4, hE2] with ω h1ω h2ω h3ω h4ω h5ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hE1] at h1ω h2ω h3ω h4ω ⊢
  rw [h1ω, h2ω, h3ω, h4ω, h5ω]
  ring


private lemma aux_bilin {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) (W : Mat m n) :
    x ⬝ᵥ (W *ᵥ y) = ∑ a, ∑ b, (x a * y b) * W a b := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private lemma aux_modeQ_integrable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] {C : Covariances m n} (S : SpectralData C) (Δ U : Ω → Mat m n)
    (η : ℝ) (hΔ : ∀ i j, MemLp (fun ω => Δ ω i j) 2 P)
    (hU : ∀ i j, MemLp (fun ω => U ω i j) 2 P) (i : Fin m) (j : Fin n) :
    Integrable (fun ω => modeQ S (Δ ω - η • U ω) i j) P := by
  have hf : (fun ω => modeQ S (Δ ω - η • U ω) i j)
      = fun ω => (S.u i ⬝ᵥ (Δ ω *ᵥ S.v j) - η * (S.u i ⬝ᵥ (U ω *ᵥ S.v j))) ^ 2 := by
    funext ω
    simp only [modeQ, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul]
  rw [hf]
  exact ((aux_dot_memLp hΔ _ _).sub ((aux_dot_memLp hU _ _).const_mul η)).integrable_sq

private lemma aux_condExp_sum1 {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (𝒢 : MeasurableSpace Ω) {ι : Type*} [Fintype ι]
    (g : ι → Ω → ℝ) (hg : ∀ j, Integrable (g j) P) :
    condExp 𝒢 P (fun ω => ∑ j, g j ω) =ᵐ[P] fun ω => ∑ j, condExp 𝒢 P (g j) ω := by
  have h := condExp_finsetSum (s := Finset.univ) (f := g) (fun j _ => hg j) 𝒢
  have e1 : (∑ j ∈ Finset.univ, g j) = fun ω => ∑ j, g j ω := by
    funext ω; simp [Finset.sum_apply]
  have e2 : (∑ j ∈ Finset.univ, condExp 𝒢 P (g j)) = fun ω => ∑ j, condExp 𝒢 P (g j) ω := by
    funext ω; simp [Finset.sum_apply]
  rw [e1, e2] at h
  exact h

private lemma aux_condExp_wsum {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (𝒢 : MeasurableSpace Ω) {m n : ℕ}
    (w : Fin m → Fin n → ℝ) (g : Fin m → Fin n → Ω → ℝ) (hg : ∀ i j, Integrable (g i j) P) :
    condExp 𝒢 P (fun ω => ∑ i, ∑ j, w i j * g i j ω)
      =ᵐ[P] fun ω => ∑ i, ∑ j, w i j * condExp 𝒢 P (g i j) ω := by
  have hin : ∀ i, Integrable (fun ω => ∑ j, w i j * g i j ω) P :=
    fun i => integrable_finsetSum _ fun j _ => (hg i j).const_mul _
  have h1 : condExp 𝒢 P (fun ω => ∑ i, ∑ j, w i j * g i j ω)
      =ᵐ[P] fun ω => ∑ i, condExp 𝒢 P (fun ω' => ∑ j, w i j * g i j ω') ω :=
    aux_condExp_sum1 P 𝒢 (fun i ω => ∑ j, w i j * g i j ω) hin
  have h2 : ∀ i, condExp 𝒢 P (fun ω => ∑ j, w i j * g i j ω)
      =ᵐ[P] fun ω => ∑ j, w i j * condExp 𝒢 P (g i j) ω := by
    intro i
    have h := aux_condExp_sum1 P 𝒢 (fun j ω => w i j * g i j ω)
      (fun j => (hg i j).const_mul _)
    have hc : ∀ j, condExp 𝒢 P (fun ω => w i j * g i j ω)
        =ᵐ[P] fun ω => w i j * condExp 𝒢 P (g i j) ω := by
      intro j
      exact condExp_smul (μ := P) (w i j) (g i j) 𝒢
    have hall := Filter.eventually_all.2 hc
    filter_upwards [h, hall] with ω h1ω h2ω
    rw [h1ω]
    exact Finset.sum_congr rfl fun j _ => by simpa [Pi.smul_def, smul_eq_mul] using h2ω j
  have h2' := Filter.eventually_all.2 h2
  filter_upwards [h1, h2'] with ω h1ω h2ω
  rw [h1ω]
  exact Finset.sum_congr rfl fun i _ => h2ω i

/-- `prop:app-setup-risk-recursion`, (i) mode identity, snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.488–509):

```latex
\begin{proposition}[Conditional recursion of the projected risks]\label{prop:app-setup-risk-recursion}
In \cref{def:app-setup-model}, fix $t\ge0$, let $\Dt$ be the state at step
$t$ with $\EE\norm{\Dt}_\F^2<\infty$, let ${\mathsf S}$ be a random matrix in
$\R^{\Nout\times\Nin}$ with $\EE\norm {\mathsf S}_\F^2<\infty$ (the update, determined
by the past and the batch of step $t$), let $\lr_t\ge0$ be deterministic,
and put $\Delta_{t+1}\defeq\Dt-\lr_t{\mathsf S}$. Define
\begin{equation}\label{eqn:app-setup-DV}
\cD_{ij}(t)\defeq(u_i^\T\Dt v_j)\,\EE_t\big[u_i^\T {\mathsf S}v_j\big],\qquad
\cV_{ij}(t)\defeq\EE_t\big[(u_i^\T {\mathsf S}v_j)^2\big].
\end{equation}
Then
\begin{align}
\EE_t\big[\CMscr Q_{ij}(\Delta_{t+1})\big]&=\CMscr Q_{ij}(\Dt)-2\lr_t\,\cD_{ij}(t)+\lr_t^2\,\cV_{ij}(t),\label{eqn:app-setup-mode}\\
\EE_t\big[\CMscr Q_{i}(\Delta_{t+1})\big]&=\CMscr Q_{i}(\Dt)-2\lr_t\sum_j\cD_{ij}(t)+\lr_t^2\sum_j\cV_{ij}(t),\label{eqn:app-setup-row}\\
\EE_t\big[\tfrac12\norm{\Delta_{t+1}}_\Sigma^2\big]&=\tfrac12\norm{\Dt}_\Sigma^2-\lr_t\sum_{i,j}\mu_i\lambda_j\cD_{ij}(t)+\frac{\lr_t^2}2\sum_{i,j}\mu_i\lambda_j\cV_{ij}(t),\label{eqn:app-setup-total}
\end{align}
with the contractions in the last line equal to
\begin{equation}\label{eqn:app-setup-contractions}
\sum_{i,j}\mu_i\lambda_j\cD_{ij}(t)=\big\langle\Dt,\EE_t{\mathsf S}\big\rangle_\Sigma,\qquad
\sum_{i,j}\mu_i\lambda_j\cV_{ij}(t)=\EE_t\norm{{\mathsf S}}_\Sigma^2 .
\end{equation}
\end{proposition}
```
-/
theorem prop_app_setup_risk_recursion_mode {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {C : Covariances m n} (S : SpectralData C)
    (𝒢 : MeasurableSpace Ω) (h𝒢 : 𝒢 ≤ mΩ) (Δ U : Ω → Mat m n) (η : ℝ) (hη : 0 ≤ η)
    (hΔm : ∀ i j, Measurable[𝒢] fun ω => Δ ω i j)
    (hΔ : ∀ i j, MemLp (fun ω => Δ ω i j) 2 P)
    (hU : ∀ i j, MemLp (fun ω => U ω i j) 2 P) (i : Fin m) (j : Fin n) :
    condExp 𝒢 P (fun ω => modeQ S (Δ ω - η • U ω) i j)
      =ᵐ[P] fun ω => modeQ S (Δ ω) i j
        - 2 * η * condDrift P 𝒢 S Δ U i j ω + η ^ 2 * condVol P 𝒢 S U i j ω := by
  have hA : Measurable[𝒢] (fun ω => S.u i ⬝ᵥ (Δ ω *ᵥ S.v j)) := aux_dot_meas hΔm _ _
  have hAL : MemLp (fun ω => S.u i ⬝ᵥ (Δ ω *ᵥ S.v j)) 2 P := aux_dot_memLp hΔ _ _
  have hBL : MemLp (fun ω => S.u i ⬝ᵥ (U ω *ᵥ S.v j)) 2 P := aux_dot_memLp hU _ _
  have hf : (fun ω => modeQ S (Δ ω - η • U ω) i j)
      = fun ω => (S.u i ⬝ᵥ (Δ ω *ᵥ S.v j) - η * (S.u i ⬝ᵥ (U ω *ᵥ S.v j))) ^ 2 := by
    funext ω
    simp only [modeQ, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul]
  rw [hf]
  filter_upwards [aux_mode_scalar P 𝒢 h𝒢 _ _ η hA hAL hBL] with ω hω
  simp only [modeQ, condDrift, condVol] at hω ⊢
  rw [hω]

/-- `prop:app-setup-risk-recursion`, row identity, snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.488–509):

```latex
\begin{proposition}[Conditional recursion of the projected risks]\label{prop:app-setup-risk-recursion}
In \cref{def:app-setup-model}, fix $t\ge0$, let $\Dt$ be the state at step
$t$ with $\EE\norm{\Dt}_\F^2<\infty$, let ${\mathsf S}$ be a random matrix in
$\R^{\Nout\times\Nin}$ with $\EE\norm {\mathsf S}_\F^2<\infty$ (the update, determined
by the past and the batch of step $t$), let $\lr_t\ge0$ be deterministic,
and put $\Delta_{t+1}\defeq\Dt-\lr_t{\mathsf S}$. Define
\begin{equation}\label{eqn:app-setup-DV}
\cD_{ij}(t)\defeq(u_i^\T\Dt v_j)\,\EE_t\big[u_i^\T {\mathsf S}v_j\big],\qquad
\cV_{ij}(t)\defeq\EE_t\big[(u_i^\T {\mathsf S}v_j)^2\big].
\end{equation}
Then
\begin{align}
\EE_t\big[\CMscr Q_{ij}(\Delta_{t+1})\big]&=\CMscr Q_{ij}(\Dt)-2\lr_t\,\cD_{ij}(t)+\lr_t^2\,\cV_{ij}(t),\label{eqn:app-setup-mode}\\
\EE_t\big[\CMscr Q_{i}(\Delta_{t+1})\big]&=\CMscr Q_{i}(\Dt)-2\lr_t\sum_j\cD_{ij}(t)+\lr_t^2\sum_j\cV_{ij}(t),\label{eqn:app-setup-row}\\
\EE_t\big[\tfrac12\norm{\Delta_{t+1}}_\Sigma^2\big]&=\tfrac12\norm{\Dt}_\Sigma^2-\lr_t\sum_{i,j}\mu_i\lambda_j\cD_{ij}(t)+\frac{\lr_t^2}2\sum_{i,j}\mu_i\lambda_j\cV_{ij}(t),\label{eqn:app-setup-total}
\end{align}
with the contractions in the last line equal to
\begin{equation}\label{eqn:app-setup-contractions}
\sum_{i,j}\mu_i\lambda_j\cD_{ij}(t)=\big\langle\Dt,\EE_t{\mathsf S}\big\rangle_\Sigma,\qquad
\sum_{i,j}\mu_i\lambda_j\cV_{ij}(t)=\EE_t\norm{{\mathsf S}}_\Sigma^2 .
\end{equation}
\end{proposition}
```
-/
theorem prop_app_setup_risk_recursion_row {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {C : Covariances m n} (S : SpectralData C)
    (𝒢 : MeasurableSpace Ω) (h𝒢 : 𝒢 ≤ mΩ) (Δ U : Ω → Mat m n) (η : ℝ) (hη : 0 ≤ η)
    (hΔm : ∀ i j, Measurable[𝒢] fun ω => Δ ω i j)
    (hΔ : ∀ i j, MemLp (fun ω => Δ ω i j) 2 P)
    (hU : ∀ i j, MemLp (fun ω => U ω i j) 2 P) (i : Fin m) :
    condExp 𝒢 P (fun ω => rowQ S (Δ ω - η • U ω) i)
      =ᵐ[P] fun ω => rowQ S (Δ ω) i
        - 2 * η * (∑ j, condDrift P 𝒢 S Δ U i j ω)
        + η ^ 2 * (∑ j, condVol P 𝒢 S U i j ω) := by
  have hint : ∀ j : Fin n, Integrable (fun ω => modeQ S (Δ ω - η • U ω) i j) P :=
    fun j => aux_modeQ_integrable P S Δ U η hΔ hU i j
  have hrow : (fun ω => rowQ S (Δ ω - η • U ω) i)
      = fun ω => ∑ j, modeQ S (Δ ω - η • U ω) i j :=
    funext fun ω => lem_app_setup_decomposition_i S _ i
  rw [hrow]
  have hs := aux_condExp_sum1 P 𝒢 (fun j ω => modeQ S (Δ ω - η • U ω) i j) hint
  have hall := Filter.eventually_all.2 fun j =>
    prop_app_setup_risk_recursion_mode (mΩ := mΩ) P S 𝒢 h𝒢 Δ U η hη hΔm hΔ hU i j
  filter_upwards [hs, hall] with ω h1 h2
  rw [h1, lem_app_setup_decomposition_i S (Δ ω) i]
  rw [Finset.sum_congr rfl fun j _ => h2 j]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

/-- `prop:app-setup-risk-recursion`, total identity, snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.488–509):

```latex
\begin{proposition}[Conditional recursion of the projected risks]\label{prop:app-setup-risk-recursion}
In \cref{def:app-setup-model}, fix $t\ge0$, let $\Dt$ be the state at step
$t$ with $\EE\norm{\Dt}_\F^2<\infty$, let ${\mathsf S}$ be a random matrix in
$\R^{\Nout\times\Nin}$ with $\EE\norm {\mathsf S}_\F^2<\infty$ (the update, determined
by the past and the batch of step $t$), let $\lr_t\ge0$ be deterministic,
and put $\Delta_{t+1}\defeq\Dt-\lr_t{\mathsf S}$. Define
\begin{equation}\label{eqn:app-setup-DV}
\cD_{ij}(t)\defeq(u_i^\T\Dt v_j)\,\EE_t\big[u_i^\T {\mathsf S}v_j\big],\qquad
\cV_{ij}(t)\defeq\EE_t\big[(u_i^\T {\mathsf S}v_j)^2\big].
\end{equation}
Then
\begin{align}
\EE_t\big[\CMscr Q_{ij}(\Delta_{t+1})\big]&=\CMscr Q_{ij}(\Dt)-2\lr_t\,\cD_{ij}(t)+\lr_t^2\,\cV_{ij}(t),\label{eqn:app-setup-mode}\\
\EE_t\big[\CMscr Q_{i}(\Delta_{t+1})\big]&=\CMscr Q_{i}(\Dt)-2\lr_t\sum_j\cD_{ij}(t)+\lr_t^2\sum_j\cV_{ij}(t),\label{eqn:app-setup-row}\\
\EE_t\big[\tfrac12\norm{\Delta_{t+1}}_\Sigma^2\big]&=\tfrac12\norm{\Dt}_\Sigma^2-\lr_t\sum_{i,j}\mu_i\lambda_j\cD_{ij}(t)+\frac{\lr_t^2}2\sum_{i,j}\mu_i\lambda_j\cV_{ij}(t),\label{eqn:app-setup-total}
\end{align}
with the contractions in the last line equal to
\begin{equation}\label{eqn:app-setup-contractions}
\sum_{i,j}\mu_i\lambda_j\cD_{ij}(t)=\big\langle\Dt,\EE_t{\mathsf S}\big\rangle_\Sigma,\qquad
\sum_{i,j}\mu_i\lambda_j\cV_{ij}(t)=\EE_t\norm{{\mathsf S}}_\Sigma^2 .
\end{equation}
\end{proposition}
```
-/
theorem prop_app_setup_risk_recursion_total {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {C : Covariances m n} (S : SpectralData C)
    (𝒢 : MeasurableSpace Ω) (h𝒢 : 𝒢 ≤ mΩ) (Δ U : Ω → Mat m n) (η : ℝ) (hη : 0 ≤ η)
    (hΔm : ∀ i j, Measurable[𝒢] fun ω => Δ ω i j)
    (hΔ : ∀ i j, MemLp (fun ω => Δ ω i j) 2 P)
    (hU : ∀ i j, MemLp (fun ω => U ω i j) 2 P) :
    condExp 𝒢 P (fun ω => riskSigma C (Δ ω - η • U ω))
      =ᵐ[P] fun ω => riskSigma C (Δ ω)
        - η * (∑ i, ∑ j, S.μ i * S.lam j * condDrift P 𝒢 S Δ U i j ω)
        + η ^ 2 / 2 * (∑ i, ∑ j, S.μ i * S.lam j * condVol P 𝒢 S U i j ω) := by
  have hR : ∀ D : Mat m n, riskSigma C D
      = ∑ i, ∑ j, (1 / 2 * (S.μ i * S.lam j)) * modeQ S D i j := by
    intro D
    have h := lem_app_setup_decomposition_ii S D
    unfold riskSigma
    calc pairSigma C D D / 2 = (1 / 2) * pairSigma C D D := by ring
      _ = (1 / 2) * ∑ i, ∑ j, S.μ i * S.lam j * modeQ S D i j := h
      _ = ∑ i, ∑ j, (1 / 2 * (S.μ i * S.lam j)) * modeQ S D i j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
  have e1 : (fun ω => riskSigma C (Δ ω - η • U ω))
      = fun ω => ∑ i, ∑ j, (1 / 2 * (S.μ i * S.lam j)) * modeQ S (Δ ω - η • U ω) i j :=
    funext fun ω => hR _
  rw [e1]
  have hw := aux_condExp_wsum P 𝒢 (fun i j => 1 / 2 * (S.μ i * S.lam j))
    (fun i j ω => modeQ S (Δ ω - η • U ω) i j)
    (fun i j => aux_modeQ_integrable P S Δ U η hΔ hU i j)
  have hall := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
    prop_app_setup_risk_recursion_mode (mΩ := mΩ) P S 𝒢 h𝒢 Δ U η hη hΔm hΔ hU i j
  filter_upwards [hw, hall] with ω h1 h2
  rw [h1, hR (Δ ω)]
  have hterm : ∀ i j, (1 / 2 * (S.μ i * S.lam j))
      * (modeQ S (Δ ω) i j - 2 * η * condDrift P 𝒢 S Δ U i j ω
          + η ^ 2 * condVol P 𝒢 S U i j ω)
      = (1 / 2 * (S.μ i * S.lam j)) * modeQ S (Δ ω) i j
        + (-η) * (S.μ i * S.lam j * condDrift P 𝒢 S Δ U i j ω)
        + (η ^ 2 / 2) * (S.μ i * S.lam j * condVol P 𝒢 S U i j ω) := by
    intro i j; ring
  have hs1 : ∑ i, ∑ j, (-η) * (S.μ i * S.lam j * condDrift P 𝒢 S Δ U i j ω)
      = (-η) * ∑ i, ∑ j, S.μ i * S.lam j * condDrift P 𝒢 S Δ U i j ω := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  have hs2 : ∑ i, ∑ j, (η ^ 2 / 2) * (S.μ i * S.lam j * condVol P 𝒢 S U i j ω)
      = (η ^ 2 / 2) * ∑ i, ∑ j, S.μ i * S.lam j * condVol P 𝒢 S U i j ω := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  have hL : ∑ i, ∑ j, (1 / 2 * (S.μ i * S.lam j)) * condExp 𝒢 P
        (fun ω' => modeQ S (Δ ω' - η • U ω') i j) ω
      = ∑ i, ∑ j, (1 / 2 * (S.μ i * S.lam j))
          * (modeQ S (Δ ω) i j - 2 * η * condDrift P 𝒢 S Δ U i j ω
              + η ^ 2 * condVol P 𝒢 S U i j ω) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [h2 i j]
  rw [hL, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j]
  simp only [Finset.sum_add_distrib]
  rw [hs1, hs2]
  ring

/-- `prop:app-setup-risk-recursion`, contraction identities, snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.488–509):

```latex
\begin{proposition}[Conditional recursion of the projected risks]\label{prop:app-setup-risk-recursion}
In \cref{def:app-setup-model}, fix $t\ge0$, let $\Dt$ be the state at step
$t$ with $\EE\norm{\Dt}_\F^2<\infty$, let ${\mathsf S}$ be a random matrix in
$\R^{\Nout\times\Nin}$ with $\EE\norm {\mathsf S}_\F^2<\infty$ (the update, determined
by the past and the batch of step $t$), let $\lr_t\ge0$ be deterministic,
and put $\Delta_{t+1}\defeq\Dt-\lr_t{\mathsf S}$. Define
\begin{equation}\label{eqn:app-setup-DV}
\cD_{ij}(t)\defeq(u_i^\T\Dt v_j)\,\EE_t\big[u_i^\T {\mathsf S}v_j\big],\qquad
\cV_{ij}(t)\defeq\EE_t\big[(u_i^\T {\mathsf S}v_j)^2\big].
\end{equation}
Then
\begin{align}
\EE_t\big[\CMscr Q_{ij}(\Delta_{t+1})\big]&=\CMscr Q_{ij}(\Dt)-2\lr_t\,\cD_{ij}(t)+\lr_t^2\,\cV_{ij}(t),\label{eqn:app-setup-mode}\\
\EE_t\big[\CMscr Q_{i}(\Delta_{t+1})\big]&=\CMscr Q_{i}(\Dt)-2\lr_t\sum_j\cD_{ij}(t)+\lr_t^2\sum_j\cV_{ij}(t),\label{eqn:app-setup-row}\\
\EE_t\big[\tfrac12\norm{\Delta_{t+1}}_\Sigma^2\big]&=\tfrac12\norm{\Dt}_\Sigma^2-\lr_t\sum_{i,j}\mu_i\lambda_j\cD_{ij}(t)+\frac{\lr_t^2}2\sum_{i,j}\mu_i\lambda_j\cV_{ij}(t),\label{eqn:app-setup-total}
\end{align}
with the contractions in the last line equal to
\begin{equation}\label{eqn:app-setup-contractions}
\sum_{i,j}\mu_i\lambda_j\cD_{ij}(t)=\big\langle\Dt,\EE_t{\mathsf S}\big\rangle_\Sigma,\qquad
\sum_{i,j}\mu_i\lambda_j\cV_{ij}(t)=\EE_t\norm{{\mathsf S}}_\Sigma^2 .
\end{equation}
\end{proposition}
```
-/
theorem prop_app_setup_risk_recursion_contractions {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {C : Covariances m n} (S : SpectralData C)
    (𝒢 : MeasurableSpace Ω) (h𝒢 : 𝒢 ≤ mΩ) (Δ U : Ω → Mat m n)
    (hΔm : ∀ i j, Measurable[𝒢] fun ω => Δ ω i j)
    (hΔ : ∀ i j, MemLp (fun ω => Δ ω i j) 2 P)
    (hU : ∀ i j, MemLp (fun ω => U ω i j) 2 P) :
    (∀ᵐ ω ∂P, ∑ i, ∑ j, S.μ i * S.lam j * condDrift P 𝒢 S Δ U i j ω
        = pairSigma C (Δ ω) (Matrix.of fun a b => condExp 𝒢 P (fun ω' => U ω' a b) ω))
      ∧ (∀ᵐ ω ∂P, ∑ i, ∑ j, S.μ i * S.lam j * condVol P 𝒢 S U i j ω
        = condExp 𝒢 P (fun ω' => pairSigma C (U ω') (U ω')) ω) := by

  have hd : ∀ i j, condExp 𝒢 P (fun ω' => S.u i ⬝ᵥ (U ω' *ᵥ S.v j)) =ᵐ[P]
      fun ω => ∑ a, ∑ b, (S.u i a * S.v j b) * condExp 𝒢 P (fun ω' => U ω' a b) ω := by
    intro i j
    have e : (fun ω' => S.u i ⬝ᵥ (U ω' *ᵥ S.v j))
        = fun ω' => ∑ a, ∑ b, (S.u i a * S.v j b) * U ω' a b :=
      funext fun ω' => aux_bilin _ _ _
    rw [e]
    exact aux_condExp_wsum P 𝒢 (fun a b => S.u i a * S.v j b) (fun a b ω' => U ω' a b)
      (fun a b => (hU a b).integrable one_le_two)
  have hall := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hd i j
  have hpart1 : ∀ᵐ ω ∂P, ∑ i, ∑ j, S.μ i * S.lam j * condDrift P 𝒢 S Δ U i j ω
      = pairSigma C (Δ ω) (Matrix.of fun a b => condExp 𝒢 P (fun ω' => U ω' a b) ω) := by
    filter_upwards [hall] with ω hω
    rw [pairSigma_eq_sum S]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [condDrift]
    rw [hω i j]
    simp only [aux_bilin, Matrix.of_apply]
  have e2 : (fun ω' => pairSigma C (U ω') (U ω'))
      = fun ω' => ∑ i, ∑ j, S.μ i * S.lam j * (S.u i ⬝ᵥ (U ω' *ᵥ S.v j)) ^ 2 := by
    funext ω'
    rw [pairSigma_eq_sum S]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hpart2 : ∀ᵐ ω ∂P, ∑ i, ∑ j, S.μ i * S.lam j * condVol P 𝒢 S U i j ω
      = condExp 𝒢 P (fun ω' => pairSigma C (U ω') (U ω')) ω := by
    rw [e2]
    filter_upwards [aux_condExp_wsum P 𝒢 (fun i j => S.μ i * S.lam j)
      (fun i j ω' => (S.u i ⬝ᵥ (U ω' *ᵥ S.v j)) ^ 2)
      (fun i j => (aux_dot_memLp hU _ _).integrable_sq)] with ω hω
    beta_reduce at hω
    rw [hω]
    rfl
  exact ⟨hpart1, hpart2⟩

/-- A conditional expectation vanishes a.e. on an event of the σ-algebra where the integrand vanishes. -/
private lemma aux_condExp_zero_on {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (𝒢 : MeasurableSpace Ω) (h𝒢 : 𝒢 ≤ mΩ) (E : Set Ω)
    (hE : MeasurableSet[𝒢] E) (f : Ω → ℝ) (hf : ∀ ω ∈ E, f ω = 0) :
    ∀ᵐ ω ∂P, ω ∈ E → condExp 𝒢 P f ω = 0 := by
  by_cases hI : Integrable f P
  · have h1 := condExp_indicator (μ := P) hI hE
    have h2 : E.indicator f = 0 := by
      funext ω
      by_cases hω : ω ∈ E
      · simp [Set.indicator_of_mem hω, hf ω hω]
      · simp [Set.indicator, hω]
    rw [h2, condExp_zero] at h1
    filter_upwards [h1] with ω hω hωE
    simp only [Pi.zero_apply] at hω
    rw [Set.indicator_of_mem hωE] at hω
    exact hω.symm
  · exact Filter.Eventually.of_forall fun ω _ => by
      simp [condExp_of_not_integrable hI]

/-- The error `Δ_t` is `ℱ t`-measurable as a matrix. -/
private lemma aux_dev_mat {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    [IsProbabilityMeasure ν] {B : ℕ} (hM : ModelLaw P ν B) (p : AlgParams m n)
    (s₀ : Ω → AlgState m n)
    (hs₀W : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).W i j)
    (hs₀M : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).Mprev i j) (t : ℕ) :
    Measurable[hM.ℱ t] (devRand C p s₀ hM.x t) := by
  refine aux_measurable_mat fun i j => ?_
  have h := (((runRand_measurable (C := C) P hM p s₀ hs₀W hs₀M t).1 i j)).sub
    (measurable_const : Measurable[hM.ℱ t] fun _ : Ω => p.Wstar i j)
  exact h

/-- The squared entries of a `Mat`-valued `fro` norm are bounded by the squared norm. -/
private lemma aux_sq_le_fro {k l : ℕ} (K : Mat k l) (i : Fin k) (j : Fin l) :
    K i j ^ 2 ≤ fro K ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity)]
  calc K i j ^ 2 = ‖K i j‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ b, ‖K i b‖ ^ 2 :=
        Finset.single_le_sum (f := fun b => ‖K i b‖ ^ 2) (fun b _ => by positivity)
          (Finset.mem_univ j)
    _ ≤ ∑ a, ∑ b, ‖K a b‖ ^ 2 :=
        Finset.single_le_sum (f := fun a => ∑ b, ‖K a b‖ ^ 2)
          (fun a _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ i)

/-- Every entry of the update `G̃_t` is bounded: its square is at most `min m n`. -/
private lemma aux_stepUpdate_entry_sq {B : ℕ} (C : Covariances m n) (p : AlgParams m n)
    (s : AlgState m n) (b : Batch m n B) (i : Fin m) (j : Fin n) :
    (stepUpdate C p s b i j) ^ 2 ≤ ((min m n : ℕ) : ℝ) := by
  unfold stepUpdate
  split_ifs with h
  · simp
  · have hnn : (0 : ℝ) ≤ 2 * riskSigma C (errorOf p s) * p.ϱ :=
      mul_nonneg (mul_nonneg (by norm_num) (aux_riskSigma_nonneg C _)) p.hϱ.le
    obtain ⟨_, hfro, hrank, _⟩ := lem_app_setup_filter_i _ hnn (stepBuffer p s b)
    have hsq := aux_sq_le_fro (Q (2 * riskSigma C (errorOf p s) * p.ϱ) (stepBuffer p s b)) i j
    have hr : ((stepBuffer p s b).rank : ℝ) ≤ ((min m n : ℕ) : ℝ) := by exact_mod_cast hrank
    exact le_trans hsq (le_trans hfro hr)

/-- Measurability of the update as a function of the state and the batch. -/
private lemma aux_stepUpdate_meas {Ω : Type*} {σ : MeasurableSpace Ω} {B : ℕ}
    (C : Covariances m n) (p : AlgParams m n) (s : Ω → AlgState m n) (b : Ω → Batch m n B)
    (hW : ∀ i j, Measurable[σ] fun ω => (s ω).W i j)
    (hMp : ∀ i j, Measurable[σ] fun ω => (s ω).Mprev i j) (hb : Measurable[σ] b) :
    Measurable[σ] (fun ω => stepUpdate C p (s ω) (b ω)) := by
  have hRc : Continuous (fun Δ : Mat m n => riskSigma C Δ) := by
    unfold riskSigma pairSigma
    fun_prop
  have hWc : Continuous (fun A : Mat m n => A - p.Wstar) := continuous_id.sub continuous_const
  have hWm : Measurable[σ] (fun ω => (s ω).W) := aux_measurable_mat hW
  have hMm : Measurable[σ] (fun ω => (s ω).Mprev) := aux_measurable_mat hMp
  have hD : Measurable[σ] (fun ω => errorOf p (s ω)) := hWc.measurable.comp hWm
  have hR : Measurable[σ] (fun ω => riskSigma C (errorOf p (s ω))) := hRc.measurable.comp hD
  have hset : MeasurableSet[σ] {ω | riskSigma C (errorOf p (s ω)) = 0} :=
    hR (measurableSet_singleton 0)
  have hF : Measurable[σ] (fun ω => grad (errorOf p (s ω)) (b ω)) := aux_grad_meas hD hb
  have hbuf : Measurable[σ] (fun ω => stepBuffer p (s ω) (b ω)) := by
    apply aux_measurable_mat
    intro i j
    have hMij := aux_entry hMm i j
    have hFij := aux_entry hF i j
    simp only [stepBuffer, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact (hMij.const_mul _).add (hFij.const_mul _)
  refine Measurable.ite hset measurable_const ?_
  have hnn : ∀ ω, (0 : ℝ) ≤ 2 * riskSigma C (errorOf p (s ω)) * p.ϱ :=
    fun ω => mul_nonneg (mul_nonneg (by norm_num) (aux_riskSigma_nonneg C _)) p.hϱ.le
  have hφ : Measurable[σ]
      (fun ω => (⟨2 * riskSigma C (errorOf p (s ω)) * p.ϱ, hnn ω⟩ : Set.Ici (0 : ℝ))) :=
    ((hR.const_mul 2).mul_const p.ϱ).subtype_mk
  exact measurable_Q.comp (hφ.prodMk hbuf)

/-- Each entry of the random update `G̃_t` is measurable. -/
private lemma aux_gt_meas {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    [IsProbabilityMeasure ν] {B : ℕ} (hM : ModelLaw P ν B) (p : AlgParams m n)
    (s₀ : Ω → AlgState m n)
    (hs₀W : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).W i j)
    (hs₀M : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).Mprev i j) (t : ℕ) (i : Fin m) (j : Fin n) :
    Measurable (fun ω => gtRand C p s₀ hM.x t ω i j) := by
  have hrt := runRand_measurable (C := C) P hM p s₀ hs₀W hs₀M t
  have hW : ∀ i j, Measurable[hM.ℱ (t + 1)] fun ω => (runRand C p s₀ hM.x t ω).W i j :=
    fun i j => (hrt.1 i j).mono (hM.ℱ.mono (Nat.le_succ t)) le_rfl
  have hMp : ∀ i j, Measurable[hM.ℱ (t + 1)] fun ω => (runRand C p s₀ hM.x t ω).Mprev i j :=
    fun i j => (hrt.2 i j).mono (hM.ℱ.mono (Nat.le_succ t)) le_rfl
  have hG : Measurable[hM.ℱ (t + 1)] (fun ω => gtRand C p s₀ hM.x t ω) :=
    aux_stepUpdate_meas C p (runRand C p s₀ hM.x t) (hM.x t) hW hMp (hM.x_meas t)
  exact aux_entry (hG.mono (hM.ℱ.le (t + 1)) le_rfl) i j

/-- Each entry of the random update `G̃_t` is square integrable. -/
private lemma aux_gt_memLp {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    [IsProbabilityMeasure ν] {B : ℕ} (hM : ModelLaw P ν B) (p : AlgParams m n)
    (s₀ : Ω → AlgState m n)
    (hs₀W : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).W i j)
    (hs₀M : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).Mprev i j) (t : ℕ) (i : Fin m)
    (j : Fin n) : MemLp (fun ω => gtRand C p s₀ hM.x t ω i j) 2 P := by
  refine MemLp.of_bound (aux_gt_meas P hM p s₀ hs₀W hs₀M t i j).aestronglyMeasurable
    (Real.sqrt ((min m n : ℕ) : ℝ)) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt (aux_stepUpdate_entry_sq C p _ _ i j)

/-- Each entry of the error `Δ_t` is square integrable, by induction along `Δ_{t+1} = Δ_t - η_t G̃_t`. -/
private lemma aux_dev_memLp {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    [IsProbabilityMeasure ν] {B : ℕ} (hM : ModelLaw P ν B) (p : AlgParams m n)
    (s₀ : Ω → AlgState m n)
    (hs₀W : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).W i j)
    (hs₀M : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).Mprev i j)
    (hΔ0 : ∀ i j, MemLp (fun ω => devRand C p s₀ hM.x 0 ω i j) 2 P) (t : ℕ) :
    ∀ i j, MemLp (fun ω => devRand C p s₀ hM.x t ω i j) 2 P := by
  induction t with
  | zero => exact hΔ0
  | succ k ih =>
    intro i j
    have e : (fun ω => devRand C p s₀ hM.x (k + 1) ω i j)
        = fun ω => devRand C p s₀ hM.x k ω i j - p.η k * gtRand C p s₀ hM.x k ω i j := by
      funext ω
      rw [devRand_succ]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [e]
    exact (ih i j).sub ((aux_gt_memLp P hM p s₀ hs₀W hs₀M k i j).const_mul _)

/-- Real unitary matrices satisfy `Uᵀ U = 1`. -/
private lemma aux_unitary_transpose_mul {k : ℕ} (U : Matrix.unitaryGroup (Fin k) ℝ) :
    (U : Mat k k)ᵀ * (U : Mat k k) = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp U.2
  rw [star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

/-- An eigenbasis of `Σ_out`, `Σ_in` as a `SpectralData` (spectral theorem for the PSD covariances). -/
private noncomputable def aux_spectral {m n : ℕ} (C : Covariances m n) : SpectralData C :=
  { uOut := (C.psdOut.isHermitian.eigenvectorUnitary : Mat m m)
    vIn := (C.psdIn.isHermitian.eigenvectorUnitary : Mat n n)
    μ := C.psdOut.isHermitian.eigenvalues
    lam := C.psdIn.isHermitian.eigenvalues
    huOut := aux_unitary_transpose_mul _
    hvIn := aux_unitary_transpose_mul _
    eigOut := fun i => C.psdOut.isHermitian.mulVec_eigenvectorBasis i
    eigIn := fun j => C.psdIn.isHermitian.mulVec_eigenvectorBasis j }

open scoped Matrix.Norms.L2Operator in
/-- Bilinear bound: `|xᵀ K y| ≤ ‖K‖` for unit vectors `x`, `y`. -/
private lemma aux_bilin_le {k l : ℕ} (K : Mat k l) (x : Vec k) (y : Vec l)
    (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1) :
    |x ⬝ᵥ (K *ᵥ y)| ≤ opNorm K := by
  have hn : ∀ {r : ℕ} (z : Vec r),
      ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin r))‖ = Real.sqrt (z ⬝ᵥ z) := by
    intro r z
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp [dotProduct, sq]
  have h1 := Matrix.l2_opNorm_mulVec K (WithLp.toLp 2 y)
  have hcs := abs_real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k))
    (WithLp.toLp 2 (K *ᵥ y))
  have hin : inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k)) (WithLp.toLp 2 (K *ᵥ y))
      = x ⬝ᵥ (K *ᵥ y) := by
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  rw [hin] at hcs
  rw [hn x, hx, Real.sqrt_one, one_mul] at hcs
  rw [hn y, hy, Real.sqrt_one, mul_one] at h1
  have : opNorm K = ‖K‖ := opNorm_eq_norm K
  rw [this]; exact hcs.trans h1

/-- The eigenvectors `u_i` are unit vectors. -/
private lemma aux_u_unit {C : Covariances m n} (S : SpectralData C) (i : Fin m) :
    S.u i ⬝ᵥ S.u i = 1 := by
  have h := congrFun (congrFun S.huOut i) i
  simpa [Matrix.mul_apply, Matrix.transpose_apply, SpectralData.u, dotProduct] using h

/-- The eigenvectors `v_j` are unit vectors. -/
private lemma aux_v_unit {C : Covariances m n} (S : SpectralData C) (j : Fin n) :
    S.v j ⬝ᵥ S.v j = 1 := by
  have h := congrFun (congrFun S.hvIn j) j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, SpectralData.v, dotProduct] using h

/-- Every mode coefficient of the update is bounded by one. -/
private lemma aux_stepUpdate_bilin_le {B : ℕ} (C : Covariances m n) (p : AlgParams m n)
    (S : SpectralData C) (s : AlgState m n) (b : Batch m n B) (i : Fin m) (j : Fin n) :
    |S.u i ⬝ᵥ (stepUpdate C p s b *ᵥ S.v j)| ≤ 1 := by
  unfold stepUpdate
  split_ifs with h
  · simp
  · have hnn : (0 : ℝ) ≤ 2 * riskSigma C (errorOf p s) * p.ϱ :=
      mul_nonneg (mul_nonneg (by norm_num) (aux_riskSigma_nonneg C _)) p.hϱ.le
    obtain ⟨hop, _, _, _⟩ := lem_app_setup_filter_i _ hnn (stepBuffer p s b)
    exact (aux_bilin_le _ _ _ (aux_u_unit S i) (aux_v_unit S j)).trans hop

/-- `cor:app-setup-augmented`, first claim (mode, row, total identities and bounds), snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.540–553):

```latex
\begin{corollary}[Recursion of the algorithm]\label{cor:app-setup-augmented}
In \cref{def:app-setup-algorithm}, assume $\EE\norm{\Delta_0}_\F^2<\infty$. Then
for every $t\ge0$ the identities
\cref{eqn:app-setup-mode,eqn:app-setup-row,eqn:app-setup-total} hold with
${\mathsf S}=\Gtilde^\circ$, with $0\le\cV_{ij}(t)\le1$. In particular
\begin{equation}\label{eqn:app-setup-augmented}
\EE_t\big[\cR(t+1)\big]-\cR(t)=-\lr_t\big\langle\Dt,\EE_t\Gtilde^\circ\big\rangle_\Sigma+\frac{\lr_t^2}2\,\EE_t\norm{\Gtilde^\circ}_\Sigma^2 .
\end{equation}
On $\{t<t_{\mathrm{stop}}\}$ the conditional expectations in
\cref{eqn:app-setup-DV,eqn:app-setup-augmented} are obtained by integrating
the fresh batch of step $t$ with $(\Dt,M_{t-1}^\circ)$ held fixed, because
the batch is independent of the past; on $\{t\ge t_{\mathrm{stop}}\}$ both
sides of \cref{eqn:app-setup-augmented} vanish.
\end{corollary}
```
-/
theorem cor_app_setup_augmented_i {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    [IsProbabilityMeasure ν] {B : ℕ} (hM : ModelLaw P ν B) (S : SpectralData C)
    (p : AlgParams m n) (s₀ : Ω → AlgState m n)
    (hs₀W : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).W i j)
    (hs₀M : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).Mprev i j)
    (hΔ0 : ∀ i j, MemLp (fun ω => devRand C p s₀ hM.x 0 ω i j) 2 P) (t : ℕ) :
    (∀ᵐ ω ∂P, ∀ i j, 0 ≤ condVol P (hM.ℱ t) S (gtRand C p s₀ hM.x t) i j ω
        ∧ condVol P (hM.ℱ t) S (gtRand C p s₀ hM.x t) i j ω ≤ 1)
      ∧ (∀ i j, (condExp (hM.ℱ t) P fun ω => modeQ S (devRand C p s₀ hM.x (t + 1) ω) i j)
        =ᵐ[P] fun ω => modeQ S (devRand C p s₀ hM.x t ω) i j
          - 2 * p.η t * condDrift P (hM.ℱ t) S (devRand C p s₀ hM.x t) (gtRand C p s₀ hM.x t) i j ω
          + p.η t ^ 2 * condVol P (hM.ℱ t) S (gtRand C p s₀ hM.x t) i j ω)
      ∧ (∀ i, (condExp (hM.ℱ t) P fun ω => rowQ S (devRand C p s₀ hM.x (t + 1) ω) i)
        =ᵐ[P] fun ω => rowQ S (devRand C p s₀ hM.x t ω) i
          - 2 * p.η t * (∑ j, condDrift P (hM.ℱ t) S (devRand C p s₀ hM.x t)
              (gtRand C p s₀ hM.x t) i j ω)
          + p.η t ^ 2 * (∑ j, condVol P (hM.ℱ t) S (gtRand C p s₀ hM.x t) i j ω))
      ∧ ((condExp (hM.ℱ t) P fun ω => riskSigma C (devRand C p s₀ hM.x (t + 1) ω))
        =ᵐ[P] fun ω => riskSigma C (devRand C p s₀ hM.x t ω)
          - p.η t * (∑ i, ∑ j, S.μ i * S.lam j * condDrift P (hM.ℱ t) S (devRand C p s₀ hM.x t)
              (gtRand C p s₀ hM.x t) i j ω)
          + p.η t ^ 2 / 2 * (∑ i, ∑ j, S.μ i * S.lam j
              * condVol P (hM.ℱ t) S (gtRand C p s₀ hM.x t) i j ω)) := by
  have hΔm : ∀ i j, Measurable[hM.ℱ t] fun ω => devRand C p s₀ hM.x t ω i j :=
    fun i j => aux_entry (aux_dev_mat P hM p s₀ hs₀W hs₀M t) i j
  have hΔ := aux_dev_memLp P hM p s₀ hs₀W hs₀M hΔ0 t
  have hU : ∀ i j, MemLp (fun ω => gtRand C p s₀ hM.x t ω i j) 2 P :=
    fun i j => aux_gt_memLp P hM p s₀ hs₀W hs₀M t i j
  refine ⟨?_, fun i j => ?_, fun i => ?_, ?_⟩
  · refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    have hint : Integrable (fun ω' => (S.u i ⬝ᵥ (gtRand C p s₀ hM.x t ω' *ᵥ S.v j)) ^ 2) P :=
      (aux_dot_memLp hU _ _).integrable_sq
    have hb : ∀ ω', (S.u i ⬝ᵥ (gtRand C p s₀ hM.x t ω' *ᵥ S.v j)) ^ 2 ≤ 1 := fun ω' => by
      have h := aux_stepUpdate_bilin_le C p S (runRand C p s₀ hM.x t ω') (hM.x t ω') i j
      have h2 : (S.u i ⬝ᵥ (gtRand C p s₀ hM.x t ω' *ᵥ S.v j)) ^ 2 ≤ 1 := by
        have := sq_le_one_iff_abs_le_one _ |>.2 h
        exact this
      exact h2
    have h0 : 0 ≤ᵐ[P] condExp (hM.ℱ t) P
        (fun ω' => (S.u i ⬝ᵥ (gtRand C p s₀ hM.x t ω' *ᵥ S.v j)) ^ 2) :=
      condExp_nonneg (Filter.Eventually.of_forall fun ω' => sq_nonneg _)
    have h1 := condExp_mono (m := hM.ℱ t) hint (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall hb)
    rw [condExp_const (hM.ℱ.le t)] at h1
    filter_upwards [h0, h1] with ω a b
    exact ⟨a, b⟩
  · have h := prop_app_setup_risk_recursion_mode (mΩ := mΩ) P S (hM.ℱ t) (hM.ℱ.le t)
      (devRand C p s₀ hM.x t) (gtRand C p s₀ hM.x t) (p.η t) (p.hη t) hΔm hΔ hU i j
    simp only [devRand_succ]
    exact h
  · have h := prop_app_setup_risk_recursion_row (mΩ := mΩ) P S (hM.ℱ t) (hM.ℱ.le t)
      (devRand C p s₀ hM.x t) (gtRand C p s₀ hM.x t) (p.η t) (p.hη t) hΔm hΔ hU i
    simp only [devRand_succ]
    exact h
  · have h := prop_app_setup_risk_recursion_total (mΩ := mΩ) P S (hM.ℱ t) (hM.ℱ.le t)
      (devRand C p s₀ hM.x t) (gtRand C p s₀ hM.x t) (p.η t) (p.hη t) hΔm hΔ hU
    simp only [devRand_succ]
    exact h

/-- `cor:app-setup-augmented`, augmented identity, snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.540–553):

```latex
\begin{corollary}[Recursion of the algorithm]\label{cor:app-setup-augmented}
In \cref{def:app-setup-algorithm}, assume $\EE\norm{\Delta_0}_\F^2<\infty$. Then
for every $t\ge0$ the identities
\cref{eqn:app-setup-mode,eqn:app-setup-row,eqn:app-setup-total} hold with
${\mathsf S}=\Gtilde^\circ$, with $0\le\cV_{ij}(t)\le1$. In particular
\begin{equation}\label{eqn:app-setup-augmented}
\EE_t\big[\cR(t+1)\big]-\cR(t)=-\lr_t\big\langle\Dt,\EE_t\Gtilde^\circ\big\rangle_\Sigma+\frac{\lr_t^2}2\,\EE_t\norm{\Gtilde^\circ}_\Sigma^2 .
\end{equation}
On $\{t<t_{\mathrm{stop}}\}$ the conditional expectations in
\cref{eqn:app-setup-DV,eqn:app-setup-augmented} are obtained by integrating
the fresh batch of step $t$ with $(\Dt,M_{t-1}^\circ)$ held fixed, because
the batch is independent of the past; on $\{t\ge t_{\mathrm{stop}}\}$ both
sides of \cref{eqn:app-setup-augmented} vanish.
\end{corollary}
```
-/
theorem cor_app_setup_augmented_ii {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    [IsProbabilityMeasure ν] {B : ℕ} (hM : ModelLaw P ν B) (p : AlgParams m n)
    (s₀ : Ω → AlgState m n)
    (hs₀W : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).W i j)
    (hs₀M : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).Mprev i j)
    (hΔ0 : ∀ i j, MemLp (fun ω => devRand C p s₀ hM.x 0 ω i j) 2 P) (t : ℕ) :
    (fun ω => condExp (hM.ℱ t) P (fun ω' => riskSigma C (devRand C p s₀ hM.x (t + 1) ω')) ω
        - riskSigma C (devRand C p s₀ hM.x t ω))
      =ᵐ[P] fun ω =>
        - p.η t * pairSigma C (devRand C p s₀ hM.x t ω)
            (Matrix.of fun a b => condExp (hM.ℱ t) P (fun ω' => gtRand C p s₀ hM.x t ω' a b) ω)
        + p.η t ^ 2 / 2 * condExp (hM.ℱ t) P
            (fun ω' => pairSigma C (gtRand C p s₀ hM.x t ω') (gtRand C p s₀ hM.x t ω')) ω := by
  have S : SpectralData C := aux_spectral C
  have hΔm : ∀ i j, Measurable[hM.ℱ t] fun ω => devRand C p s₀ hM.x t ω i j :=
    fun i j => aux_entry (aux_dev_mat P hM p s₀ hs₀W hs₀M t) i j
  have hΔ := aux_dev_memLp P hM p s₀ hs₀W hs₀M hΔ0 t
  have hU : ∀ i j, MemLp (fun ω => gtRand C p s₀ hM.x t ω i j) 2 P :=
    fun i j => aux_gt_memLp P hM p s₀ hs₀W hs₀M t i j
  have hTot := prop_app_setup_risk_recursion_total (mΩ := mΩ) P S (hM.ℱ t) (hM.ℱ.le t)
    (devRand C p s₀ hM.x t) (gtRand C p s₀ hM.x t) (p.η t) (p.hη t) hΔm hΔ hU
  have hCon := prop_app_setup_risk_recursion_contractions (mΩ := mΩ) P S (hM.ℱ t) (hM.ℱ.le t)
    (devRand C p s₀ hM.x t) (gtRand C p s₀ hM.x t) hΔm hΔ hU
  simp only [devRand_succ]
  filter_upwards [hTot, hCon.1, hCon.2] with ω h1 h2 h3
  rw [h1, h2, h3]
  ring

/-- Freezing for continuous functionals of the update: the conditional expectation of `φ(G̃_t)`
given `ℱ t` is the integral of `φ` of the update over a fresh batch, the state being held fixed. -/
private lemma aux_freeze {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    [IsProbabilityMeasure ν] {B : ℕ} (hM : ModelLaw P ν B) (p : AlgParams m n)
    (s₀ : Ω → AlgState m n)
    (hs₀W : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).W i j)
    (hs₀M : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).Mprev i j) (t : ℕ)
    (φ : Mat m n → ℝ) (hφ : Continuous φ)
    (hint : Integrable (fun ω => φ (gtRand C p s₀ hM.x t ω)) P) :
    condExp (hM.ℱ t) P (fun ω => φ (gtRand C p s₀ hM.x t ω))
      =ᵐ[P] fun ω => ∫ b, φ (stepUpdate C p (runRand C p s₀ hM.x t ω) b)
        ∂(Measure.pi fun _ : Fin B => ν) := by
  have hrt := runRand_measurable (C := C) P hM p s₀ hs₀W hs₀M t
  have hX : Measurable[hM.ℱ t] (fun ω => ((runRand C p s₀ hM.x t ω).W,
      (runRand C p s₀ hM.x t ω).Mprev)) :=
    (aux_measurable_mat hrt.1).prodMk (aux_measurable_mat hrt.2)
  have hY : Measurable (hM.x t) := (hM.x_meas t).mono (hM.ℱ.le (t + 1)) le_rfl
  have hind : Indep (hM.ℱ t) (MeasurableSpace.comap (hM.x t) inferInstance) P :=
    (hM.x_indep t).symm
  have hf : Measurable (Function.uncurry fun (x : Mat m n × Mat m n) (y : Batch m n B) =>
      φ (stepUpdate C p ⟨x.1, x.2⟩ y)) := by
    have hm : Measurable (fun z : (Mat m n × Mat m n) × Batch m n B =>
        stepUpdate C p (⟨z.1.1, z.1.2⟩ : AlgState m n) z.2) := by
      refine aux_stepUpdate_meas C p (fun z : (Mat m n × Mat m n) × Batch m n B =>
        (⟨z.1.1, z.1.2⟩ : AlgState m n)) (fun z => z.2) ?_ ?_ measurable_snd
      · intro i j
        exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
          (measurable_fst.comp measurable_fst))
      · intro i j
        exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
          (measurable_snd.comp measurable_fst))
    exact hφ.measurable.comp hm
  have h := Muon.Foundations.freezing_condExp (μ := P) (hM.ℱ t) (hM.ℱ.le t) hX hY hind hf hint
  rw [hM.x_law t] at h
  exact h

/-- `cor:app-setup-augmented`, freezing representation on {t < t_stop}, snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.540–553):

```latex
\begin{corollary}[Recursion of the algorithm]\label{cor:app-setup-augmented}
In \cref{def:app-setup-algorithm}, assume $\EE\norm{\Delta_0}_\F^2<\infty$. Then
for every $t\ge0$ the identities
\cref{eqn:app-setup-mode,eqn:app-setup-row,eqn:app-setup-total} hold with
${\mathsf S}=\Gtilde^\circ$, with $0\le\cV_{ij}(t)\le1$. In particular
\begin{equation}\label{eqn:app-setup-augmented}
\EE_t\big[\cR(t+1)\big]-\cR(t)=-\lr_t\big\langle\Dt,\EE_t\Gtilde^\circ\big\rangle_\Sigma+\frac{\lr_t^2}2\,\EE_t\norm{\Gtilde^\circ}_\Sigma^2 .
\end{equation}
On $\{t<t_{\mathrm{stop}}\}$ the conditional expectations in
\cref{eqn:app-setup-DV,eqn:app-setup-augmented} are obtained by integrating
the fresh batch of step $t$ with $(\Dt,M_{t-1}^\circ)$ held fixed, because
the batch is independent of the past; on $\{t\ge t_{\mathrm{stop}}\}$ both
sides of \cref{eqn:app-setup-augmented} vanish.
\end{corollary}
```
-/
theorem cor_app_setup_augmented_iii {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    [IsProbabilityMeasure ν] {B : ℕ} (hM : ModelLaw P ν B) (p : AlgParams m n)
    (S : SpectralData C) (s₀ : Ω → AlgState m n)
    (hs₀W : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).W i j)
    (hs₀M : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).Mprev i j) (t : ℕ) :
    ∀ᵐ ω ∂P, (t : ℕ∞) < tstopRand C p s₀ hM.x ω →
      ((∀ a c, condExp (hM.ℱ t) P (fun ω' => gtRand C p s₀ hM.x t ω' a c) ω
          = ∫ b, stepUpdate C p (runRand C p s₀ hM.x t ω) b a c
              ∂(Measure.pi fun _ : Fin B => ν))
        ∧ (∀ i j, condVol P (hM.ℱ t) S (gtRand C p s₀ hM.x t) i j ω
          = ∫ b, (S.u i ⬝ᵥ (stepUpdate C p (runRand C p s₀ hM.x t ω) b *ᵥ S.v j)) ^ 2
              ∂(Measure.pi fun _ : Fin B => ν))
        ∧ (condExp (hM.ℱ t) P
              (fun ω' => pairSigma C (gtRand C p s₀ hM.x t ω') (gtRand C p s₀ hM.x t ω')) ω
          = ∫ b, pairSigma C (stepUpdate C p (runRand C p s₀ hM.x t ω) b)
              (stepUpdate C p (runRand C p s₀ hM.x t ω) b)
              ∂(Measure.pi fun _ : Fin B => ν))) := by
  have hU : ∀ i j, MemLp (fun ω => gtRand C p s₀ hM.x t ω i j) 2 P :=
    fun i j => aux_gt_memLp P hM p s₀ hs₀W hs₀M t i j
  have hA : ∀ a c, ∀ᵐ ω ∂P, condExp (hM.ℱ t) P (fun ω' => gtRand C p s₀ hM.x t ω' a c) ω
      = ∫ b, stepUpdate C p (runRand C p s₀ hM.x t ω) b a c
          ∂(Measure.pi fun _ : Fin B => ν) := fun a c =>
    aux_freeze P hM p s₀ hs₀W hs₀M t (fun K => K a c) (by fun_prop)
      ((hU a c).integrable one_le_two)
  have hV : ∀ i j, ∀ᵐ ω ∂P, condVol P (hM.ℱ t) S (gtRand C p s₀ hM.x t) i j ω
      = ∫ b, (S.u i ⬝ᵥ (stepUpdate C p (runRand C p s₀ hM.x t ω) b *ᵥ S.v j)) ^ 2
          ∂(Measure.pi fun _ : Fin B => ν) := fun i j =>
    aux_freeze P hM p s₀ hs₀W hs₀M t (fun K => (S.u i ⬝ᵥ (K *ᵥ S.v j)) ^ 2)
      (by unfold dotProduct Matrix.mulVec; fun_prop) (aux_dot_memLp hU _ _).integrable_sq
  have hQint : Integrable (fun ω => pairSigma C (gtRand C p s₀ hM.x t ω)
      (gtRand C p s₀ hM.x t ω)) P := by
    have e2 : (fun ω' => pairSigma C (gtRand C p s₀ hM.x t ω') (gtRand C p s₀ hM.x t ω'))
        = fun ω' => ∑ i, ∑ j, S.μ i * S.lam j *
            (S.u i ⬝ᵥ (gtRand C p s₀ hM.x t ω' *ᵥ S.v j)) ^ 2 := by
      funext ω'
      rw [pairSigma_eq_sum S]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e2]
    exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
      ((aux_dot_memLp hU (S.u i) (S.v j)).integrable_sq).const_mul (S.μ i * S.lam j)
  have hQ := aux_freeze P hM p s₀ hs₀W hs₀M t (fun K => pairSigma C K K)
    (by unfold pairSigma; fun_prop) hQint
  have hAall := ae_all_iff.2 fun a => ae_all_iff.2 fun c => hA a c
  have hVall := ae_all_iff.2 fun i => ae_all_iff.2 fun j => hV i j
  filter_upwards [hAall, hVall, hQ] with ω h1 h2 h3 _
  exact ⟨h1, h2, h3⟩

/-- `cor:app-setup-augmented`, vanishing on {t ≥ t_stop}, snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.540–553):

```latex
\begin{corollary}[Recursion of the algorithm]\label{cor:app-setup-augmented}
In \cref{def:app-setup-algorithm}, assume $\EE\norm{\Delta_0}_\F^2<\infty$. Then
for every $t\ge0$ the identities
\cref{eqn:app-setup-mode,eqn:app-setup-row,eqn:app-setup-total} hold with
${\mathsf S}=\Gtilde^\circ$, with $0\le\cV_{ij}(t)\le1$. In particular
\begin{equation}\label{eqn:app-setup-augmented}
\EE_t\big[\cR(t+1)\big]-\cR(t)=-\lr_t\big\langle\Dt,\EE_t\Gtilde^\circ\big\rangle_\Sigma+\frac{\lr_t^2}2\,\EE_t\norm{\Gtilde^\circ}_\Sigma^2 .
\end{equation}
On $\{t<t_{\mathrm{stop}}\}$ the conditional expectations in
\cref{eqn:app-setup-DV,eqn:app-setup-augmented} are obtained by integrating
the fresh batch of step $t$ with $(\Dt,M_{t-1}^\circ)$ held fixed, because
the batch is independent of the past; on $\{t\ge t_{\mathrm{stop}}\}$ both
sides of \cref{eqn:app-setup-augmented} vanish.
\end{corollary}
```
-/
theorem cor_app_setup_augmented_iv {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    [IsProbabilityMeasure ν] {B : ℕ} (hM : ModelLaw P ν B) (p : AlgParams m n)
    (s₀ : Ω → AlgState m n)
    (hs₀W : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).W i j)
    (hs₀M : ∀ i j, Measurable[hM.ℱ 0] fun ω => (s₀ ω).Mprev i j) (t : ℕ) :
    ∀ᵐ ω ∂P, tstopRand C p s₀ hM.x ω ≤ (t : ℕ∞) →
      (condExp (hM.ℱ t) P (fun ω' => riskSigma C (devRand C p s₀ hM.x (t + 1) ω')) ω
          - riskSigma C (devRand C p s₀ hM.x t ω) = 0)
      ∧ (- p.η t * pairSigma C (devRand C p s₀ hM.x t ω)
            (Matrix.of fun a b => condExp (hM.ℱ t) P (fun ω' => gtRand C p s₀ hM.x t ω' a b) ω)
          + p.η t ^ 2 / 2 * condExp (hM.ℱ t) P
              (fun ω' => pairSigma C (gtRand C p s₀ hM.x t ω') (gtRand C p s₀ hM.x t ω')) ω
          = 0) := by
  have hR : Measurable[hM.ℱ t] (fun ω => riskSigma C (devRand C p s₀ hM.x t ω)) := by
    have hRc : Continuous (fun Δ : Mat m n => riskSigma C Δ) := by
      unfold riskSigma pairSigma
      fun_prop
    exact hRc.measurable.comp (aux_dev_mat P hM p s₀ hs₀W hs₀M t)
  have hEm : MeasurableSet[hM.ℱ t] {ω | riskSigma C (devRand C p s₀ hM.x t ω) = 0} :=
    hR (measurableSet_singleton 0)
  have hG0 : ∀ ω ∈ {ω | riskSigma C (devRand C p s₀ hM.x t ω) = 0},
      gtRand C p s₀ hM.x t ω = 0 := by
    intro ω hω
    have hω' : riskSigma C (errorOf p (runRand C p s₀ hM.x t ω)) = 0 := hω
    unfold gtRand stepUpdate
    rw [if_pos hω']
  have hR0 : ∀ ω ∈ {ω | riskSigma C (devRand C p s₀ hM.x t ω) = 0},
      riskSigma C (devRand C p s₀ hM.x (t + 1) ω) = 0 := by
    intro ω hω
    have hω' : riskSigma C (devRand C p s₀ hM.x t ω) = 0 := hω
    rw [devRand_succ, hG0 ω hω, smul_zero, sub_zero, hω']
  have hE1 := aux_condExp_zero_on P (hM.ℱ t) (hM.ℱ.le t)
    {ω | riskSigma C (devRand C p s₀ hM.x t ω) = 0} hEm
    (fun ω => riskSigma C (devRand C p s₀ hM.x (t + 1) ω)) hR0
  have hGz : ∀ a c, ∀ᵐ ω ∂P, ω ∈ {ω | riskSigma C (devRand C p s₀ hM.x t ω) = 0} →
      condExp (hM.ℱ t) P (fun ω' => gtRand C p s₀ hM.x t ω' a c) ω = 0 := fun a c =>
    aux_condExp_zero_on P (hM.ℱ t) (hM.ℱ.le t) _ hEm _
      (fun ω hω => by simp [hG0 ω hω])
  have hQ := aux_condExp_zero_on P (hM.ℱ t) (hM.ℱ.le t)
    {ω | riskSigma C (devRand C p s₀ hM.x t ω) = 0} hEm
    (fun ω' => pairSigma C (gtRand C p s₀ hM.x t ω') (gtRand C p s₀ hM.x t ω'))
    (fun ω hω => by simp [hG0 ω hω, pairSigma])
  have hall := ae_all_iff.2 fun a => ae_all_iff.2 fun c => hGz a c
  filter_upwards [hE1, hall, hQ] with ω h1 h2 h3 hstop
  have hωE : ω ∈ {ω | riskSigma C (devRand C p s₀ hM.x t ω) = 0} :=
    (update_eq_zero_iff C p (s₀ ω) (fun u => hM.x u ω) t).mp hstop
  have hM0 : Matrix.of (fun a c => condExp (hM.ℱ t) P (fun ω' => gtRand C p s₀ hM.x t ω' a c) ω)
      = 0 := by
    ext a c
    simp [h2 a c hωE]
  have hrisk : riskSigma C (devRand C p s₀ hM.x t ω) = 0 := hωE
  constructor
  · rw [h1 hωE, hrisk]
    ring
  · have hz : pairSigma C (devRand C p s₀ hM.x t ω) 0 = 0 := by simp [pairSigma]
    rw [hM0, hz, h3 hωE]
    ring

/-- Orthonormality of the output eigenvectors. -/
private lemma aux_uOut_dot {C : Covariances m n} (S : SpectralData C) (i k : Fin m) :
    S.u i ⬝ᵥ S.u k = if i = k then 1 else 0 := by
  have h := congrFun (congrFun S.huOut i) k
  simpa [Matrix.mul_apply, Matrix.transpose_apply, SpectralData.u, dotProduct,
    Matrix.one_apply] using h

/-- Orthonormality of the input eigenvectors. -/
private lemma aux_vIn_dot {C : Covariances m n} (S : SpectralData C) (j l : Fin n) :
    S.v j ⬝ᵥ S.v l = if j = l then 1 else 0 := by
  have h := congrFun (congrFun S.hvIn j) l
  simpa [Matrix.mul_apply, Matrix.transpose_apply, SpectralData.v, dotProduct,
    Matrix.one_apply] using h

/-- Expansion of the output projection on a vector. -/
private lemma aux_projOut_mulVec {C : Covariances m n} (S : SpectralData C) (z : Vec m) :
    projOut S *ᵥ z = ∑ k, if 0 < S.μ k then (S.u k ⬝ᵥ z) • S.u k else 0 := by
  unfold projOut
  rw [Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : 0 < S.μ k
  · rw [if_pos hk, if_pos hk]; exact aux_outer_mulVec _ _
  · rw [if_neg hk, if_neg hk]; simp

/-- Expansion of the input projection on a vector. -/
private lemma aux_projIn_mulVec {C : Covariances m n} (S : SpectralData C) (z : Vec n) :
    projIn S *ᵥ z = ∑ k, if 0 < S.lam k then (S.v k ⬝ᵥ z) • S.v k else 0 := by
  unfold projIn
  rw [Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : 0 < S.lam k
  · rw [if_pos hk, if_pos hk]; exact aux_outer_mulVec _ _
  · rw [if_neg hk, if_neg hk]; simp

/-- The output projection acts on a basis vector: `u_i ⬝ᵥ P_out z = 1_{μ_i>0} u_i ⬝ᵥ z`. -/
private lemma aux_projOut_dot_basis {C : Covariances m n} (S : SpectralData C) (i : Fin m)
    (z : Vec m) :
    S.u i ⬝ᵥ (projOut S *ᵥ z) = if 0 < S.μ i then S.u i ⬝ᵥ z else 0 := by
  rw [aux_projOut_mulVec, dotProduct_sum, Finset.sum_eq_single i]
  · by_cases hi : 0 < S.μ i
    · simp [hi, dotProduct_smul, aux_uOut_dot]
    · simp [hi]
  · intro k _ hk
    by_cases hkpos : 0 < S.μ k
    · rw [if_pos hkpos, dotProduct_smul, aux_uOut_dot, if_neg (Ne.symm hk), smul_zero]
    · rw [if_neg hkpos]; simp
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The input projection acts on a basis vector: `v_j ⬝ᵥ P_in z = 1_{λ_j>0} v_j ⬝ᵥ z`. -/
private lemma aux_projIn_dot_basis {C : Covariances m n} (S : SpectralData C) (j : Fin n)
    (z : Vec n) :
    S.v j ⬝ᵥ (projIn S *ᵥ z) = if 0 < S.lam j then S.v j ⬝ᵥ z else 0 := by
  rw [aux_projIn_mulVec, dotProduct_sum, Finset.sum_eq_single j]
  · by_cases hj : 0 < S.lam j
    · simp [hj, dotProduct_smul, aux_vIn_dot]
    · simp [hj]
  · intro k _ hk
    by_cases hkpos : 0 < S.lam k
    · rw [if_pos hkpos, dotProduct_smul, aux_vIn_dot, if_neg (Ne.symm hk), smul_zero]
    · rw [if_neg hkpos]; simp
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Zero output mode: `u_i ⬝ᵥ P_out z = 0` when `μ_i = 0`. -/
private lemma aux_projOut_dot_zero {C : Covariances m n} (S : SpectralData C) (i : Fin m)
    (hi : S.μ i = 0) (z : Vec m) : S.u i ⬝ᵥ (projOut S *ᵥ z) = 0 := by
  rw [aux_projOut_dot_basis, if_neg (by rw [hi]; exact lt_irrefl 0)]

/-- Zero input mode: `P_in v_j = 0` when `λ_j = 0`. -/
private lemma aux_projIn_mulVec_zero {C : Covariances m n} (S : SpectralData C) (j : Fin n)
    (hj : S.lam j = 0) : projIn S *ᵥ S.v j = 0 := by
  rw [aux_projIn_mulVec]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : 0 < S.lam k
  · rw [if_pos hk, aux_vIn_dot]
    by_cases hkj : k = j
    · subst hkj; rw [hj] at hk; exact absurd hk (lt_irrefl 0)
    · simp [hkj]
  · rw [if_neg hk]

/-- Symmetry of the output projection. -/
private lemma aux_projOut_symm {C : Covariances m n} (S : SpectralData C) :
    (projOut S)ᵀ = projOut S := by
  unfold projOut
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · ext r c
    simp [outer, Matrix.vecMulVec_apply, mul_comm]
  · exact Matrix.transpose_zero

/-- Symmetry of the input projection. -/
private lemma aux_projIn_symm {C : Covariances m n} (S : SpectralData C) :
    (projIn S)ᵀ = projIn S := by
  unfold projIn
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · ext r c
    simp [outer, Matrix.vecMulVec_apply, mul_comm]
  · exact Matrix.transpose_zero

/-- Idempotence of the output projection. -/
private lemma aux_projOut_idem {C : Covariances m n} (S : SpectralData C) :
    projOut S * projOut S = projOut S := by
  have hvec : ∀ z : Vec m, projOut S *ᵥ (projOut S *ᵥ z) = projOut S *ᵥ z := by
    intro z
    conv_lhs => rw [aux_projOut_mulVec]
    simp only [aux_projOut_dot_basis]
    rw [aux_projOut_mulVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : 0 < S.μ k <;> simp [hk]
  ext r c
  have h : (projOut S * projOut S) *ᵥ Pi.single c 1 = projOut S *ᵥ Pi.single c 1 := by
    rw [← Matrix.mulVec_mulVec]; exact hvec _
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  exact congrFun h r

/-- Idempotence of the input projection. -/
private lemma aux_projIn_idem {C : Covariances m n} (S : SpectralData C) :
    projIn S * projIn S = projIn S := by
  have hvec : ∀ z : Vec n, projIn S *ᵥ (projIn S *ᵥ z) = projIn S *ᵥ z := by
    intro z
    conv_lhs => rw [aux_projIn_mulVec]
    simp only [aux_projIn_dot_basis]
    rw [aux_projIn_mulVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : 0 < S.lam k <;> simp [hk]
  ext r c
  have h : (projIn S * projIn S) *ᵥ Pi.single c 1 = projIn S *ᵥ Pi.single c 1 := by
    rw [← Matrix.mulVec_mulVec]; exact hvec _
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  exact congrFun h r

/-- Mode coefficients of a support-form matrix vanish on zero modes: `u_i ⬝ᵥ (G v_j) = 0` when
`μ_i λ_j = 0`. -/
private lemma aux_modeQ_mul_zero {C : Covariances m n} (S : SpectralData C) (G : Mat m n)
    (hG : G = projOut S * G * projIn S) (i : Fin m) (j : Fin n) (h : S.μ i * S.lam j = 0) :
    S.u i ⬝ᵥ (G *ᵥ S.v j) = 0 := by
  have hGv : G *ᵥ S.v j = projOut S *ᵥ (G *ᵥ (projIn S *ᵥ S.v j)) := by
    conv_lhs => rw [hG]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rcases mul_eq_zero.mp h with hμ | hl
  · rw [hGv]; exact aux_projOut_dot_zero S i hμ _
  · rw [hGv, aux_projIn_mulVec_zero S j hl, Matrix.mulVec_zero, Matrix.mulVec_zero,
      dotProduct_zero]

/-- A supported sample has zero bilinear residual when every nonzero mode pair is killed by
`Δ`. -/
private lemma aux_resid_zero {C : Covariances m n} (S : SpectralData C) (Δ : Mat m n)
    (hD : ∀ i j, 0 < S.μ i * S.lam j → S.u i ⬝ᵥ (Δ *ᵥ S.v j) = 0)
    (x : Vec m × Vec n) (hx1 : ∀ i, S.μ i = 0 → S.u i ⬝ᵥ x.1 = 0)
    (hx2 : ∀ j, S.lam j = 0 → S.v j ⬝ᵥ x.2 = 0) :
    resid Δ x = 0 := by
  have ha : x.1 = ∑ i, (S.u i ⬝ᵥ x.1) • S.u i := (aux_expand S.uOut S.huOut x.1).symm
  have hc : x.2 = ∑ j, (S.v j ⬝ᵥ x.2) • S.v j := (aux_expand S.vIn S.hvIn x.2).symm
  have h1 : ∀ w : Vec m, x.1 ⬝ᵥ w = ∑ i, (S.u i ⬝ᵥ x.1) * (S.u i ⬝ᵥ w) := by
    intro w
    conv_lhs => rw [ha]
    rw [sum_dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_dotProduct, smul_eq_mul]
  have h2 : Δ *ᵥ x.2 = ∑ j, (S.v j ⬝ᵥ x.2) • (Δ *ᵥ S.v j) := by
    conv_lhs => rw [hc]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul]
  have hres_sum : resid Δ x = ∑ j, ∑ i,
      (S.v j ⬝ᵥ x.2) * ((S.u i ⬝ᵥ x.1) * (S.u i ⬝ᵥ (Δ *ᵥ S.v j))) := by
    unfold resid
    rw [h2, dotProduct_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dotProduct_smul, h1, smul_eq_mul, Finset.mul_sum]
  have hterm : ∀ i j, (S.v j ⬝ᵥ x.2) * ((S.u i ⬝ᵥ x.1) * (S.u i ⬝ᵥ (Δ *ᵥ S.v j))) = 0 := by
    intro i j
    by_cases hμ : S.μ i = 0
    · simp [hx1 i hμ]
    by_cases hl : S.lam j = 0
    · simp [hx2 j hl]
    have hpos : 0 < S.μ i * S.lam j :=
      mul_pos (lt_of_le_of_ne (μ_nonneg S i) (Ne.symm hμ))
        (lt_of_le_of_ne (lam_nonneg S j) (Ne.symm hl))
    simp [hD i j hpos]
  rw [hres_sum]
  exact Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => hterm i j

/-- The projection `x ↦ u ⬝ᵥ x.1` of a feature pair is measurable. -/
private lemma aux_meas_dot_fst {m n : ℕ} (u : Vec m) :
    Measurable fun y : Vec m × Vec n => u ⬝ᵥ y.1 := by
  unfold dotProduct
  exact Finset.measurable_sum _ fun k _ =>
    measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)

/-- The projection `x ↦ v ⬝ᵥ x.2` of a feature pair is measurable. -/
private lemma aux_meas_dot_snd {m n : ℕ} (v : Vec n) :
    Measurable fun y : Vec m × Vec n => v ⬝ᵥ y.2 := by
  unfold dotProduct
  exact Finset.measurable_sum _ fun k _ =>
    measurable_const.mul ((measurable_pi_apply k).comp measurable_snd)

/-- Marginal of a product law. -/
private lemma aux_pi_map_eval {m n B : ℕ} (ν : Measure (Vec m × Vec n)) [IsProbabilityMeasure ν]
    (a : Fin B) : (Measure.pi fun _ : Fin B => ν).map (Function.eval a) = ν := by
  rw [Measure.pi_map_eval]
  simp

/-- A zero output mode vanishes `ν`-a.e.: its second moment is `μ_i = 0`. -/
private lemma aux_out_zero_ae {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    (hν : IsFeatureLaw C ν) (S : SpectralData C) (i : Fin m) (hi : S.μ i = 0) :
    ∀ᵐ x ∂ν, S.u i ⬝ᵥ x.1 = 0 := by
  haveI := hν.isProb
  haveI : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  have hmul : ∀ k l : Fin m, Integrable (fun x : Vec m × Vec n => x.1 k * x.1 l) ν :=
    fun k l => (hν.memLp_out k).integrable_mul (hν.memLp_out l)
  have hexp : ∀ x : Vec m × Vec n, (S.u i ⬝ᵥ x.1) ^ 2
      = ∑ k, ∑ l, (S.u i k * S.u i l) * (x.1 k * x.1 l) := by
    intro x
    rw [sq]
    simp only [dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hsq_int : Integrable (fun x : Vec m × Vec n => (S.u i ⬝ᵥ x.1) ^ 2) ν := by
    simp only [hexp]
    exact integrable_finset_sum _ fun k _ =>
      integrable_finset_sum _ fun l _ => (hmul k l).const_mul (S.u i k * S.u i l)
  have hq : ∑ k, ∑ l, S.u i k * S.u i l * C.Sout k l = S.μ i := by
    have h1 : C.Sout *ᵥ S.u i = S.μ i • S.u i := S.eigOut i
    have h2 : S.u i ⬝ᵥ (C.Sout *ᵥ S.u i) = ∑ k, ∑ l, S.u i k * S.u i l * C.Sout k l := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [← h2, h1, dotProduct_smul, aux_u_unit, smul_eq_mul, mul_one]
  have hint_eq : ∫ x, (S.u i ⬝ᵥ x.1) ^ 2 ∂ν = ∑ k, ∑ l, S.u i k * S.u i l * C.Sout k l := by
    simp only [hexp]
    rw [integral_finset_sum _ fun k _ =>
      integrable_finset_sum _ fun l _ => (hmul k l).const_mul (S.u i k * S.u i l)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finset_sum _ fun l _ => (hmul k l).const_mul (S.u i k * S.u i l)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, hν.second_out k l]
  have hzero : ∫ x, (S.u i ⬝ᵥ x.1) ^ 2 ∂ν = 0 := by
    rw [hint_eq, hq, hi]
  have hnn : (0 : Vec m × Vec n → ℝ) ≤ fun x => (S.u i ⬝ᵥ x.1) ^ 2 :=
    fun x => sq_nonneg _
  have h0 := (integral_eq_zero_iff_of_nonneg hnn hsq_int).mp hzero
  filter_upwards [h0] with x hx
  simpa using hx

/-- A zero input mode vanishes `ν`-a.e.: its second moment is `λ_j = 0`. -/
private lemma aux_in_zero_ae {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    (hν : IsFeatureLaw C ν) (S : SpectralData C) (j : Fin n) (hj : S.lam j = 0) :
    ∀ᵐ x ∂ν, S.v j ⬝ᵥ x.2 = 0 := by
  haveI := hν.isProb
  haveI : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  have hmul : ∀ k l : Fin n, Integrable (fun x : Vec m × Vec n => x.2 k * x.2 l) ν :=
    fun k l => (hν.memLp_in k).integrable_mul (hν.memLp_in l)
  have hexp : ∀ x : Vec m × Vec n, (S.v j ⬝ᵥ x.2) ^ 2
      = ∑ k, ∑ l, (S.v j k * S.v j l) * (x.2 k * x.2 l) := by
    intro x
    rw [sq]
    simp only [dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hsq_int : Integrable (fun x : Vec m × Vec n => (S.v j ⬝ᵥ x.2) ^ 2) ν := by
    simp only [hexp]
    exact integrable_finset_sum _ fun k _ =>
      integrable_finset_sum _ fun l _ => (hmul k l).const_mul (S.v j k * S.v j l)
  have hq : ∑ k, ∑ l, S.v j k * S.v j l * C.Sin k l = S.lam j := by
    have h1 : C.Sin *ᵥ S.v j = S.lam j • S.v j := S.eigIn j
    have h2 : S.v j ⬝ᵥ (C.Sin *ᵥ S.v j) = ∑ k, ∑ l, S.v j k * S.v j l * C.Sin k l := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [← h2, h1, dotProduct_smul, aux_v_unit, smul_eq_mul, mul_one]
  have hint_eq : ∫ x, (S.v j ⬝ᵥ x.2) ^ 2 ∂ν = ∑ k, ∑ l, S.v j k * S.v j l * C.Sin k l := by
    simp only [hexp]
    rw [integral_finset_sum _ fun k _ =>
      integrable_finset_sum _ fun l _ => (hmul k l).const_mul (S.v j k * S.v j l)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finset_sum _ fun l _ => (hmul k l).const_mul (S.v j k * S.v j l)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, hν.second_in k l]
  have hzero : ∫ x, (S.v j ⬝ᵥ x.2) ^ 2 ∂ν = 0 := by
    rw [hint_eq, hq, hj]
  have hnn : (0 : Vec m × Vec n → ℝ) ≤ fun x => (S.v j ⬝ᵥ x.2) ^ 2 :=
    fun x => sq_nonneg _
  have h0 := (integral_eq_zero_iff_of_nonneg hnn hsq_int).mp hzero
  filter_upwards [h0] with x hx
  simpa using hx

/-- `prop:app-setup-support`, first claim, pathwise in the batch, snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.568–583):

```latex
\begin{proposition}[Support event and zero risk]\label{prop:app-setup-support}
In \cref{def:app-setup-model} let $P_{\mathrm{out}}\defeq\sum_{\mu_i>0}u_i\tensor u_i$
and $P_{\mathrm{in}}\defeq\sum_{\lambda_j>0}v_j\tensor v_j$. There is an event
$\Omega_t$ of probability one, determined by the batch of step $t$, on which
\begin{equation}\label{eqn:app-setup-support}
\Xout^{(a)}=P_{\mathrm{out}}\Xout^{(a)},\qquad \Xin^{(a)}=P_{\mathrm{in}}\Xin^{(a)}\quad(a\le B),\qquad
\Gt^\circ=P_{\mathrm{out}}\Gt^\circ P_{\mathrm{in}}
\end{equation}
for every value of $\Dt$. On $\Omega_t$, if $\cR(t)=0$ then $d_a^\circ=0$ for
every $a$ and $\Gt^\circ=0$. If, in \cref{def:app-setup-algorithm},
$M_{-1}^\circ=P_{\mathrm{out}}M_{-1}^\circ P_{\mathrm{in}}$, then on
$\bigcap_t\Omega_t$ every buffer and every update satisfy
$M_t^\circ=P_{\mathrm{out}}M_t^\circ P_{\mathrm{in}}$ and
$\Gtilde^\circ=P_{\mathrm{out}}\Gtilde^\circ P_{\mathrm{in}}$, and
$\CMscr Q_{ij}(\Dt)$ is constant in $t$ for every pair with $\mu_i\lambda_j=0$.
\end{proposition}
```
-/
theorem prop_app_setup_support_i {C : Covariances m n} (S : SpectralData C) {B : ℕ}
    (b : Batch m n B) (hb : BatchSupported S b) (Δ : Mat m n) :
    (∀ a, projOut S *ᵥ (b a).1 = (b a).1) ∧ (∀ a, projIn S *ᵥ (b a).2 = (b a).2)
      ∧ grad Δ b = projOut S * grad Δ b * projIn S := by
  obtain ⟨hbo, hbi⟩ := hb
  -- output side: `P_out x = x` for every batch output sample
  have hPout : ∀ x : Fin m → ℝ, (∀ i, S.μ i = 0 → S.u i ⬝ᵥ x = 0) → projOut S *ᵥ x = x := by
    intro x hx
    unfold projOut
    rw [Matrix.sum_mulVec]
    have hterm : ∀ i, (if 0 < S.μ i then outer (S.u i) (S.u i) else 0) *ᵥ x
        = if 0 < S.μ i then (S.u i ⬝ᵥ x) • S.u i else 0 := by
      intro i
      split_ifs
      · exact aux_outer_mulVec _ _
      · simp
    simp only [hterm]
    conv_rhs => rw [← aux_expand S.uOut S.huOut x]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · have hμ : S.μ i = 0 := le_antisymm (not_lt.mp h) (μ_nonneg S i)
      show 0 = (S.u i ⬝ᵥ x) • S.u i
      rw [hx i hμ, zero_smul]
  -- input side: `y ᵥ* P_in = y`
  have hPin : ∀ y : Fin n → ℝ, (∀ j, S.lam j = 0 → S.v j ⬝ᵥ y = 0) → y ᵥ* projIn S = y := by
    intro y hy
    unfold projIn
    rw [Matrix.vecMul_sum]
    have hterm : ∀ j, y ᵥ* (if 0 < S.lam j then outer (S.v j) (S.v j) else 0)
        = if 0 < S.lam j then (y ⬝ᵥ S.v j) • S.v j else 0 := by
      intro j
      split_ifs
      · exact Matrix.vecMul_vecMulVec _ _ _
      · simp
    simp only [hterm]
    conv_rhs => rw [← aux_expand S.vIn S.hvIn y]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [dotProduct_comm]; rfl
    · have hlam : S.lam j = 0 := le_antisymm (not_lt.mp h) (lam_nonneg S j)
      show 0 = (S.v j ⬝ᵥ y) • S.v j
      rw [hy j hlam, zero_smul]
  -- projIn is symmetric, so the row-vector identity gives the column one
  have hsymIn : (projIn S)ᵀ = projIn S := by
    unfold projIn
    rw [Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · ext r c
      simp [outer, Matrix.vecMulVec_apply, mul_comm]
    · exact Matrix.transpose_zero
  have hPinM : ∀ y : Fin n → ℝ, (∀ j, S.lam j = 0 → S.v j ⬝ᵥ y = 0) → projIn S *ᵥ y = y := by
    intro y hy
    have h := hPin y hy
    calc projIn S *ᵥ y = y ᵥ* (projIn S)ᵀ := (Matrix.vecMul_transpose _ _).symm
      _ = y ᵥ* projIn S := by rw [hsymIn]
      _ = y := h
  have hkey : ∀ (u : Vec m) (v : Vec n), projOut S *ᵥ u = u → v ᵥ* projIn S = v →
      projOut S * outer u v * projIn S = outer u v := by
    intro u v hu hv
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hu, hv]
  have hterm : ∀ a, projOut S * (resid Δ (b a) • outer (b a).1 (b a).2) * projIn S
      = resid Δ (b a) • outer (b a).1 (b a).2 := by
    intro a
    rw [Matrix.mul_smul, Matrix.smul_mul, hkey _ _ (hPout _ fun i hi => hbo a i hi)
      (hPin _ fun j hj => hbi a j hj)]
  refine ⟨fun a => hPout _ fun i hi => hbo a i hi, fun a => hPinM _ fun j hj => hbi a j hj, ?_⟩
  unfold grad
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun a _ => (hterm a).symm

/-- `prop:app-setup-support`, probability one, snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.568–583):

```latex
\begin{proposition}[Support event and zero risk]\label{prop:app-setup-support}
In \cref{def:app-setup-model} let $P_{\mathrm{out}}\defeq\sum_{\mu_i>0}u_i\tensor u_i$
and $P_{\mathrm{in}}\defeq\sum_{\lambda_j>0}v_j\tensor v_j$. There is an event
$\Omega_t$ of probability one, determined by the batch of step $t$, on which
\begin{equation}\label{eqn:app-setup-support}
\Xout^{(a)}=P_{\mathrm{out}}\Xout^{(a)},\qquad \Xin^{(a)}=P_{\mathrm{in}}\Xin^{(a)}\quad(a\le B),\qquad
\Gt^\circ=P_{\mathrm{out}}\Gt^\circ P_{\mathrm{in}}
\end{equation}
for every value of $\Dt$. On $\Omega_t$, if $\cR(t)=0$ then $d_a^\circ=0$ for
every $a$ and $\Gt^\circ=0$. If, in \cref{def:app-setup-algorithm},
$M_{-1}^\circ=P_{\mathrm{out}}M_{-1}^\circ P_{\mathrm{in}}$, then on
$\bigcap_t\Omega_t$ every buffer and every update satisfy
$M_t^\circ=P_{\mathrm{out}}M_t^\circ P_{\mathrm{in}}$ and
$\Gtilde^\circ=P_{\mathrm{out}}\Gtilde^\circ P_{\mathrm{in}}$, and
$\CMscr Q_{ij}(\Dt)$ is constant in $t$ for every pair with $\mu_i\lambda_j=0$.
\end{proposition}
```
-/
theorem prop_app_setup_support_ii {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    [IsProbabilityMeasure ν] {B : ℕ} (hν : IsFeatureLaw C ν) (hM : ModelLaw P ν B)
    (S : SpectralData C) (t : ℕ) :
    ∀ᵐ ω ∂P, BatchSupported S (hM.x t ω) := by
  have hY : Measurable (hM.x t) := (hM.x_meas t).mono (hM.ℱ.le (t + 1)) le_rfl
  have hYae : AEMeasurable (hM.x t) P := hY.aemeasurable
  -- each output coordinate of each sample vanishes on a zero output mode, a.s.
  have hx1 : ∀ a i, ∀ᵐ ω ∂P, S.μ i = 0 → S.u i ⬝ᵥ (hM.x t ω a).1 = 0 := by
    intro a i
    by_cases hi : S.μ i = 0
    · have hq : ∀ᵐ y ∂(Measure.pi fun _ : Fin B => ν).map (Function.eval a),
          S.u i ⬝ᵥ y.1 = 0 := by
        rw [aux_pi_map_eval ν a]; exact aux_out_zero_ae hν S i hi
      have hA := (ae_map_iff (measurable_pi_apply a).aemeasurable
        (measurableSet_eq_fun (aux_meas_dot_fst (n := n) (S.u i)) measurable_const)).mp hq
      have hY' : ∀ᵐ y ∂(P.map (hM.x t)), S.u i ⬝ᵥ (y a).1 = 0 := by
        rw [hM.x_law t]; exact hA
      have hgB : Measurable fun b : Batch m n B => S.u i ⬝ᵥ (b a).1 :=
        (aux_meas_dot_fst (n := n) (S.u i)).comp (measurable_pi_apply a)
      exact ((ae_map_iff hYae (measurableSet_eq_fun hgB measurable_const)).mp hY').mono
        fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h hi
  have hx2 : ∀ a j, ∀ᵐ ω ∂P, S.lam j = 0 → S.v j ⬝ᵥ (hM.x t ω a).2 = 0 := by
    intro a j
    by_cases hj : S.lam j = 0
    · have hq : ∀ᵐ y ∂(Measure.pi fun _ : Fin B => ν).map (Function.eval a),
          S.v j ⬝ᵥ y.2 = 0 := by
        rw [aux_pi_map_eval ν a]; exact aux_in_zero_ae hν S j hj
      have hA := (ae_map_iff (measurable_pi_apply a).aemeasurable
        (measurableSet_eq_fun (aux_meas_dot_snd (m := m) (S.v j)) measurable_const)).mp hq
      have hY' : ∀ᵐ y ∂(P.map (hM.x t)), S.v j ⬝ᵥ (y a).2 = 0 := by
        rw [hM.x_law t]; exact hA
      have hgB : Measurable fun b : Batch m n B => S.v j ⬝ᵥ (b a).2 :=
        (aux_meas_dot_snd (m := m) (S.v j)).comp (measurable_pi_apply a)
      exact ((ae_map_iff hYae (measurableSet_eq_fun hgB measurable_const)).mp hY').mono
        fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h hj
  have hall1 : ∀ᵐ ω ∂P, ∀ a i, S.μ i = 0 → S.u i ⬝ᵥ (hM.x t ω a).1 = 0 :=
    ae_all_iff.2 fun a => ae_all_iff.2 fun i => hx1 a i
  have hall2 : ∀ᵐ ω ∂P, ∀ a j, S.lam j = 0 → S.v j ⬝ᵥ (hM.x t ω a).2 = 0 :=
    ae_all_iff.2 fun a => ae_all_iff.2 fun j => hx2 a j
  filter_upwards [hall1, hall2] with ω h1 h2
  unfold BatchSupported
  exact ⟨fun a i hi => h1 a i hi, fun a j hj => h2 a j hj⟩

/-- `prop:app-setup-support`, zero risk, snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.568–583):

```latex
\begin{proposition}[Support event and zero risk]\label{prop:app-setup-support}
In \cref{def:app-setup-model} let $P_{\mathrm{out}}\defeq\sum_{\mu_i>0}u_i\tensor u_i$
and $P_{\mathrm{in}}\defeq\sum_{\lambda_j>0}v_j\tensor v_j$. There is an event
$\Omega_t$ of probability one, determined by the batch of step $t$, on which
\begin{equation}\label{eqn:app-setup-support}
\Xout^{(a)}=P_{\mathrm{out}}\Xout^{(a)},\qquad \Xin^{(a)}=P_{\mathrm{in}}\Xin^{(a)}\quad(a\le B),\qquad
\Gt^\circ=P_{\mathrm{out}}\Gt^\circ P_{\mathrm{in}}
\end{equation}
for every value of $\Dt$. On $\Omega_t$, if $\cR(t)=0$ then $d_a^\circ=0$ for
every $a$ and $\Gt^\circ=0$. If, in \cref{def:app-setup-algorithm},
$M_{-1}^\circ=P_{\mathrm{out}}M_{-1}^\circ P_{\mathrm{in}}$, then on
$\bigcap_t\Omega_t$ every buffer and every update satisfy
$M_t^\circ=P_{\mathrm{out}}M_t^\circ P_{\mathrm{in}}$ and
$\Gtilde^\circ=P_{\mathrm{out}}\Gtilde^\circ P_{\mathrm{in}}$, and
$\CMscr Q_{ij}(\Dt)$ is constant in $t$ for every pair with $\mu_i\lambda_j=0$.
\end{proposition}
```
-/
theorem prop_app_setup_support_iii {C : Covariances m n} (S : SpectralData C) {B : ℕ}
    (b : Batch m n B) (hb : BatchSupported S b) (Δ : Mat m n) (hR : riskSigma C Δ = 0) :
    (∀ a, resid Δ (b a) = 0) ∧ grad Δ b = 0 := by
  obtain ⟨hbo, hbi⟩ := hb
  have hpair : pairSigma C Δ Δ = 0 := by
    unfold riskSigma at hR; linarith
  have hsq : Real.sqrt (pairSigma C Δ Δ) = 0 := by rw [hpair, Real.sqrt_zero]
  have hD := (lem_app_setup_decomposition_iv S Δ).mp hsq
  have hres : ∀ a, resid Δ (b a) = 0 := fun a =>
    aux_resid_zero S Δ hD (b a) (hbo a) (hbi a)
  refine ⟨hres, ?_⟩
  simp [grad, hres]

/-- `prop:app-setup-support`, buffers, updates and zero modes along the trajectory, snapshot `cr-2026-10-23`. Verbatim source (`sections/01-setup/section.tex` l.568–583):

```latex
\begin{proposition}[Support event and zero risk]\label{prop:app-setup-support}
In \cref{def:app-setup-model} let $P_{\mathrm{out}}\defeq\sum_{\mu_i>0}u_i\tensor u_i$
and $P_{\mathrm{in}}\defeq\sum_{\lambda_j>0}v_j\tensor v_j$. There is an event
$\Omega_t$ of probability one, determined by the batch of step $t$, on which
\begin{equation}\label{eqn:app-setup-support}
\Xout^{(a)}=P_{\mathrm{out}}\Xout^{(a)},\qquad \Xin^{(a)}=P_{\mathrm{in}}\Xin^{(a)}\quad(a\le B),\qquad
\Gt^\circ=P_{\mathrm{out}}\Gt^\circ P_{\mathrm{in}}
\end{equation}
for every value of $\Dt$. On $\Omega_t$, if $\cR(t)=0$ then $d_a^\circ=0$ for
every $a$ and $\Gt^\circ=0$. If, in \cref{def:app-setup-algorithm},
$M_{-1}^\circ=P_{\mathrm{out}}M_{-1}^\circ P_{\mathrm{in}}$, then on
$\bigcap_t\Omega_t$ every buffer and every update satisfy
$M_t^\circ=P_{\mathrm{out}}M_t^\circ P_{\mathrm{in}}$ and
$\Gtilde^\circ=P_{\mathrm{out}}\Gtilde^\circ P_{\mathrm{in}}$, and
$\CMscr Q_{ij}(\Dt)$ is constant in $t$ for every pair with $\mu_i\lambda_j=0$.
\end{proposition}
```
-/
theorem prop_app_setup_support_iv {C : Covariances m n} (S : SpectralData C) (p : AlgParams m n)
    {B : ℕ} (s₀ : AlgState m n) (x : ℕ → Batch m n B)
    (hx : ∀ t, BatchSupported S (x t))
    (hs : s₀.Mprev = projOut S * s₀.Mprev * projIn S) :
    (∀ t, (run C p s₀ x t).Mprev = projOut S * (run C p s₀ x t).Mprev * projIn S
        ∧ stepUpdate C p (run C p s₀ x t) (x t)
          = projOut S * stepUpdate C p (run C p s₀ x t) (x t) * projIn S)
      ∧ (∀ t i j, S.μ i * S.lam j = 0 →
          modeQ S (errorOf p (run C p s₀ x t)) i j = modeQ S (errorOf p s₀) i j) := by
  -- buffer step preserves the support form
  have hbuf : ∀ s : AlgState m n, s.Mprev = projOut S * s.Mprev * projIn S →
      ∀ b : Batch m n B, BatchSupported S b →
      stepBuffer p s b = projOut S * stepBuffer p s b * projIn S := by
    intro s hM b hb
    have hG := (prop_app_setup_support_i S b hb (errorOf p s)).2.2
    unfold stepBuffer
    conv_rhs => rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    rw [← hM, ← hG]
  have hM : ∀ t, (run C p s₀ x t).Mprev = projOut S * (run C p s₀ x t).Mprev * projIn S := by
    intro t
    induction t with
    | zero => exact hs
    | succ t ih =>
      change stepBuffer p (run C p s₀ x t) (x t)
        = projOut S * stepBuffer p (run C p s₀ x t) (x t) * projIn S
      exact hbuf _ ih (x t) (hx t)
  have hupd : ∀ t, stepUpdate C p (run C p s₀ x t) (x t)
      = projOut S * stepUpdate C p (run C p s₀ x t) (x t) * projIn S := by
    intro t
    have hnn : (0 : ℝ) ≤ 2 * riskSigma C (errorOf p (run C p s₀ x t)) * p.ϱ :=
      mul_nonneg (mul_nonneg (by norm_num) (aux_riskSigma_nonneg C _)) p.hϱ.le
    unfold stepUpdate
    split_ifs with h
    · simp
    · exact lem_app_setup_filter_ii _ hnn _ (projOut S) (projIn S) (aux_projOut_symm S)
        (aux_projOut_idem S) (aux_projIn_symm S) (aux_projIn_idem S)
        (hbuf _ (hM t) (x t) (hx t))
  have hE : ∀ t, errorOf p (run C p s₀ x (t + 1))
      = errorOf p (run C p s₀ x t) - p.η t • stepUpdate C p (run C p s₀ x t) (x t) := by
    intro t
    simp only [run, step, errorOf]
    abel
  have hmode : ∀ t i j, S.μ i * S.lam j = 0 →
      modeQ S (errorOf p (run C p s₀ x (t + 1))) i j
        = modeQ S (errorOf p (run C p s₀ x t)) i j := by
    intro t i j hij
    have hz := aux_modeQ_mul_zero S _ (hupd t) i j hij
    rw [hE t]
    unfold modeQ
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, hz,
      smul_zero, sub_zero]
  refine ⟨fun t => ⟨hM t, hupd t⟩, ?_⟩
  intro t i j hij
  induction t with
  | zero => rfl
  | succ t ih => rw [hmode t i j hij, ih]

end Muon.Setup

end

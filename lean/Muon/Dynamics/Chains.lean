import Muon.External.Certificates
import Muon.Dynamics.Basic
import Muon.DetEquiv.Gaussian
import Muon.Setup.Frozen
import Muon.Setup.Model
import Muon.Volatility.Defs

/-!
# Appendix E, work package L-E.6: frozen chains, batch moments, covariance inequality

Snapshot `cr-2026-10-23`. Source: `sections/05-dynamics/section.tex`: `def:app-dyn-chains`
(ll. 472–491), `lem:app-dyn-chains` (ll. 497–514), `lem:app-dyn-batch` (ll. 537–550),
`lem:app-dyn-covariance` (ll. 716–723). Card: `sections/05-dynamics/CARD.md` §2, §3, §5 (L-E.6).
Interface draft: statements are `sorry`ed; proofs are later work.

Representation choices:
* Sampling model. The source's batches are whitened Gaussian pairs `(z_{s,a}, w_{s,a})`, and the
  batch gradient is taken at the physical features `(Σ_out^{1/2} z, Σ_in^{1/2} w)` (`Muon.Setup.phys`,
  as in `Muon.Dynamics.batchGrad`). `ChainSamples` carries the whitened pairs: `act s a` for the batches
  whose gradients are `G°_s`, `s ∈ ℤ` (the source's batch of step `s-1`), and `aux t j a` for the auxiliary batches `G*_j` of each comparison
  time `t` ("drawn anew for each comparison"). All of them are jointly independent standard Gaussian pairs.
* Indexing. Chain arrays are indexed by `k : ℕ` with `k = r + 1`: `stat k = N_{k-1}`, so `N_{-1}` is
  index `0` and `V_0` is index `1`. `N_r` uses the batch of step `t + r + 1`, as in the source. The frozen
  buffer `M_{t'}` of `Muon.Setup.frozenBuf` is matched with `N_r` at `t' = t + r`, so `N_{-1} ↔ M_{t-1}`.
* Series. `N_{-1}` is a series; its a.s. summability is a conjunct wherever it is integrated.
* Constants. `cMConst CSig γstar = C_Σ²(γ⋆+2)²`, the source's `C_M`.
-/

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open Muon Muon.Setup Muon.Volatility

noncomputable section

namespace Muon.Dynamics

variable {m n B : ℕ}

/-! ## Constants and the sampling model -/

/-- `cMConst CSig γstar = C_M = C_Σ²(γ⋆+2)²`, the constant of `lem:app-dyn-chains`(iii)
(source l. 499: `C_M ≔ C_Σ²(γ⋆+2)²`). Snapshot `cr-2026-10-23`. -/
def cMConst (CSig γstar : ℝ) : ℝ := CSig ^ 2 * (γstar + 2) ^ 2

/-- Whitened sampling model of the frozen chains, `cr-2026-10-23` (`def:app-dyn-chains`, ll. 472–491,
and the conventions at `eqn:app-dyn-coefficient-bounds`, ll. 124–132). `act s a` is the whitened pair
of sample `a` of the batch whose gradient is `G°_s` (the source's batch of step `s-1`; `G°_{t+1}` is
the gradient of the batch of step `t`), `aux t j a` the pair of sample `a` of the auxiliary batch
`G*_j` of comparison time `t`. Every coordinate is a standard Gaussian pair `N(0,I_m) ⊗ N(0,I_n)`,
and the whole family is jointly independent, so auxiliary batches are independent of everything
else and are drawn anew for each comparison. -/
structure ChainSamples {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (m n B : ℕ) where
  act : ℤ → Fin B → Ω → Vec m × Vec n
  aux : ℤ → ℕ → Fin B → Ω → Vec m × Vec n
  meas_act : ∀ s a, Measurable (act s a)
  meas_aux : ∀ t j a, Measurable (aux t j a)
  law_act : ∀ s a,
    P.map (act s a) = (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)
  law_aux : ∀ t j a,
    P.map (aux t j a) = (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)
  indep : iIndepFun (fun p : (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B) =>
    (Sum.elim (fun q : ℤ × Fin B => act q.1 q.2)
      (fun q : ℤ × ℕ × Fin B => aux q.1 q.2.1 q.2.2) p : Ω → Vec m × Vec n)) P

/-- The physical batch of one step, `cr-2026-10-23`: the features `(Σ_out^{1/2} z_a, Σ_in^{1/2} w_a)` of
`Muon.Setup.phys`, `a ≤ B`, at the sample point `ω`. -/
def physBatch {Ω : Type*} (C : Covariances m n) (z : Fin B → Ω → Vec m × Vec n) (ω : Ω) :
    Batch m n B :=
  fun a => phys C (z a ω)

/-- The σ-algebra `chainFuture cs t` of the future after comparison time `t`, `cr-2026-10-23`: the
batches whose gradients are `G°_s` for `s > t` (the batches of steps `≥ t`) and the auxiliary batches of
comparison `t`. `F_t` is independent of it (`Conventions`, ll. 127–132). -/
abbrev chainFuture {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (cs : ChainSamples P m n B) (t : ℕ) : MeasurableSpace Ω :=
  (⨆ (s : ℤ) (_ : (t : ℤ) < s) (a : Fin B), MeasurableSpace.comap (cs.act s a) inferInstance) ⊔
    ⨆ (j : ℕ) (a : Fin B), MeasurableSpace.comap (cs.aux (t : ℤ) j a) inferInstance

/-! ## The frozen chains (`def:app-dyn-chains`) -/

/-- Initial value `N_{-1} = ∑_{j≥0} w_j G*_j[D]` of the stationary chain at `(t, D)`, where
`G*_j[D]` is the gradient at `D` of the auxiliary batch `j` (`def:app-dyn-chains`, ll. 472–491).
The series is a `tsum`; its summability is a conjunct of `lem_app_dyn_chains_iii`. -/
def chainInit {Ω : Type*} (β : ℝ) (C : Covariances m n) (D : Mat m n)
    (aux : ℕ → Fin B → Ω → Vec m × Vec n) (ω : Ω) : Mat m n :=
  ∑' j : ℕ, emaW β j • batchGrad D (physBatch C (aux j) ω)

/-- The EMA recursion of `def:app-dyn-chains`, `cr-2026-10-23`: starting from `init`, `N_r = β N_{r-1} + (1-β) G°_{t+r+1}[D]`
for `r ≥ 0`, where `G s` is the physical batch of step `s`. Indexed as `k = r + 1`, so the value at
index `k + 1` is `N_k` and index `0` is `init`. -/
def emaChain (β : ℝ) (D : Mat m n) (G : ℤ → Batch m n B) (t : ℕ) (init : Mat m n) : ℕ → Mat m n
  | 0 => init
  | k + 1 => β • emaChain β D G t init k + (1 - β) • batchGrad D (G ((t : ℤ) + k + 1))

/-- The chains at time `t` with `D` and `M` (`def:app-dyn-chains`, ll. 472–491), arrays indexed by
`k = r + 1`: `stat k = N_{k-1}` (stationary chain), `same k = N̂_{k-1}` (same-buffer chain, with
`N̂_{-1} = M`), and `statV k = V_{k-1}`, `sameV k = V̂_{k-1}` with `V_r = Q_{ϱ°(D)}(N_r)`, the
physical ridge `ϱ°(D) = physRidge p C D`. -/
structure ChainPath (m n : ℕ) where
  stat : ℕ → Mat m n
  same : ℕ → Mat m n
  statV : ℕ → Mat m n
  sameV : ℕ → Mat m n

/-- `def:app-dyn-chains` (cr-2026-10-23). The stationary and same-buffer chains at time `t` with
`D = Δ_t` and `M = M°_{t-1}` (the substitution is made by the caller), evaluated at the sample point
`ω`. The stationary chain starts from the auxiliary buffer `chainInit` of comparison `t`; the
same-buffer chain starts from the actual buffer `M`. Statement and definition verbatim from
`section.tex` (ll. 472–491):
```latex
\begin{definition}[Frozen chains]\label{def:app-dyn-chains}
Let $t\ge0$, let $D,m\in\R^{\Nout\times\Nin}$ with $\cR(D)>0$, and let
$G^\ast_j[\cdot]$, $j\ge0$, be the gradients \cref{eqn:app-dyn-batch} of
auxiliary batches. The stationary chain at $(t,D)$ is
\[
N_{-1}\defeq\sum_{j\ge0}\emaw j\,G^\ast_j[D],\qquad
N_r\defeq\bmom N_{r-1}+(1-\bmom)\,G^\circ_{t+r+1}[D],\qquad
V_r\defeq\Qridge{\ridgephys(D)}(N_r),
\]
for $r\ge0$.
The same-buffer chain at $(t,D,m)$ is
\[
\widehat N_{-1}\defeq m,\qquad
\widehat N_r\defeq\bmom\widehat N_{r-1}+(1-\bmom)\,G^\circ_{t+r+1}[D],\qquad
\widehat V_r\defeq\Qridge{\ridgephys(D)}(\widehat N_r)\qquad(r\ge0).
\]
At a step $t<t_{\rm stop}$ of the algorithm, the chains at time $t$ are
those with $D=\Dt$ and $m=M^\circ_{t-1}$. The mean frozen update at $D$ is
$\overline V(D)\defeq\EE V_0$.
\end{definition}
```
-/
def def_app_dyn_chains {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ)
    (D M : Mat m n) (ω : Ω) : ChainPath m n :=
  let G : ℤ → Batch m n B := fun s => physBatch C (cs.act s) ω
  let N0 : Mat m n := chainInit p.β C D (cs.aux (t : ℤ)) ω
  { stat := emaChain p.β D G t N0
    same := emaChain p.β D G t M
    statV := fun k => Q (physRidge p C D) (emaChain p.β D G t N0 k)
    sameV := fun k => Q (physRidge p C D) (emaChain p.β D G t M k) }

/-- The normalized stationary chain `N_r / √(2𝓡(D))`, `cr-2026-10-23`, indexed by `k = r + 1` (the normalization of
`lem:app-dyn-chains`(i)). -/
def normChainPath {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ)
    (D M : Mat m n) (ω : Ω) : ℕ → Mat m n :=
  fun k => (Real.sqrt (2 * riskSigma C D))⁻¹ • (def_app_dyn_chains p C cs t D M ω).stat k

/-! ## Laws of the frozen chains (`lem:app-dyn-chains`) -/

open scoped Matrix.Norms.Frobenius in
private theorem pc_summable_of_fro (f : ℕ → Mat m n)
    (hf : Summable (fun j => fro (f j))) : Summable f := by
  apply Summable.of_norm
  simpa only [fro_eq_norm] using hf

private lemma pd_buf_ae_Psi {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (T : ℤ)
    (G : (ℤ × Fin B → Vec m × Vec n) → ℤ → Mat m n)
    (hG : ∀ ω s, frozenBatchG F S s ω = G (fun p => S.zw p.1 p.2 ω) s) :
    (fun ω (k : ℕ) => frozenBuf F S (T + (k : ℤ) - 1) ω) =ᵐ[P]
      fun ω (k : ℕ) => Matrix.of fun i l => limUnder Filter.atTop (fun N : ℕ =>
        ∑ j ∈ Finset.range N,
          emaW F.β j * G (fun p => S.zw p.1 p.2 ω) (T + (k : ℤ) - 1 + 1 - (j : ℤ)) i l) := by
  filter_upwards [(lem_app_setup_ema_law_i F S).1] with ω hω
  funext k
  have hs := pc_summable_of_fro _ (hω (T + (k : ℤ) - 1))
  funext i l
  show (∑' j : ℕ, emaW F.β j • frozenBatchG F S (T + (k : ℤ) - 1 + 1 - (j : ℤ)) ω) i l = _
  rw [← (Pi.hasSum.1 (Pi.hasSum.1 hs.hasSum i) l).tsum_eq]
  have hsk : Summable fun j : ℕ =>
      (emaW F.β j • frozenBatchG F S (T + (k : ℤ) - 1 + 1 - (j : ℤ)) ω) i l :=
    Pi.summable.1 (Pi.summable.1 hs i) l
  simp only [Matrix.smul_apply, smul_eq_mul, hG] at hsk ⊢
  exact (hsk.hasSum.tendsto_sum_nat.limUnder_eq).symm

private lemma pd_buf_law_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (S' : FrozenSamples P' m n B) (T : ℤ)
    (hlaw : P.map (fun ω (p : ℤ × Fin B) => S.zw p.1 p.2 ω) =
      P'.map (fun ω' (p : ℤ × Fin B) => S'.zw p.1 p.2 ω')) :
    P.map (fun ω (k : ℕ) => frozenBuf F S (T + (k : ℤ) - 1) ω) =
      P'.map (fun ω' (k : ℕ) => frozenBuf F S' (T + (k : ℤ) - 1) ω') := by
  let G : (ℤ × Fin B → Vec m × Vec n) → ℤ → Mat m n := fun x s =>
    ((B : ℝ))⁻¹ • ∑ a : Fin B,
      (dotProduct (x (s, a)).1 (Matrix.mulVec F.A (x (s, a)).2)) •
        (rOut F.C * outer (x (s, a)).1 (x (s, a)).2 * rIn F.C)
  have hGc : ∀ s, Continuous (fun x : ℤ × Fin B → Vec m × Vec n => G x s) := by
    intro s
    unfold G
    fun_prop
  let Ψ : (ℤ × Fin B → Vec m × Vec n) → ℕ → Mat m n := fun x k =>
    Matrix.of fun i l => limUnder Filter.atTop (fun N : ℕ => ∑ j ∈ Finset.range N,
      emaW F.β j * G x (T + (k : ℤ) - 1 + 1 - (j : ℤ)) i l)
  have hΨ : Measurable Ψ := by
    refine measurable_pi_iff.2 fun k => measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun l => ?_
    have hf : ∀ N : ℕ, MeasureTheory.StronglyMeasurable
        (fun x : ℤ × Fin B → Vec m × Vec n => ∑ j ∈ Finset.range N,
          emaW F.β j * G x (T + (k : ℤ) - 1 + 1 - (j : ℤ)) i l) := fun N =>
      (Finset.measurable_sum _ fun j _ =>
        (((measurable_pi_apply l).comp (measurable_pi_apply i)).comp
          (hGc _).measurable).const_mul _).stronglyMeasurable
    exact (MeasureTheory.StronglyMeasurable.limUnder (l := Filter.atTop) hf).measurable
  have hX : Measurable (fun ω (p : ℤ × Fin B) => S.zw p.1 p.2 ω) :=
    measurable_pi_iff.2 fun p => S.meas p.1 p.2
  have hX' : Measurable (fun ω' (p : ℤ × Fin B) => S'.zw p.1 p.2 ω') :=
    measurable_pi_iff.2 fun p => S'.meas p.1 p.2
  have e1 := pd_buf_ae_Psi F S T G (fun _ _ => rfl)
  have e2 := pd_buf_ae_Psi F S' T G (fun _ _ => rfl)
  rw [Measure.map_congr e1, Measure.map_congr e2]
  have e3 : P.map (fun ω => Ψ (fun p => S.zw p.1 p.2 ω)) =
      (P.map (fun ω (p : ℤ × Fin B) => S.zw p.1 p.2 ω)).map Ψ :=
    (Measure.map_map hΨ hX).symm
  have e4 : P'.map (fun ω => Ψ (fun p => S'.zw p.1 p.2 ω)) =
      (P'.map (fun ω (p : ℤ × Fin B) => S'.zw p.1 p.2 ω)).map Ψ :=
    (Measure.map_map hΨ hX').symm
  exact e3.trans ((congrArg (fun μ => μ.map Ψ) hlaw).trans e4.symm)

private lemma pc_merged_exists {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (cs : ChainSamples P m n B) (t : ℕ) :
    ∃ S : FrozenSamples P m n B,
      (∀ (j : ℕ) a ω, S.zw ((t : ℤ) - (j : ℤ)) a ω = cs.aux (t : ℤ) j a ω) ∧
      (∀ s a ω, (t : ℤ) < s → S.zw s a ω = cs.act s a ω) := by
  classical
  let Z : ℤ → Fin B → Ω → Vec m × Vec n := fun s a =>
    if s ≤ (t : ℤ) then cs.aux (t : ℤ) ((t : ℤ) - s).toNat a else cs.act s a
  let g : ℤ × Fin B → (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B) := fun p =>
    if p.1 ≤ (t : ℤ) then Sum.inr ((t : ℤ), ((t : ℤ) - p.1).toNat, p.2) else Sum.inl (p.1, p.2)
  have hg : Function.Injective g := by
    intro p q h
    simp only [g] at h
    by_cases h1 : p.1 ≤ (t : ℤ) <;> by_cases h2 : q.1 ≤ (t : ℤ) <;>
      simp only [h1, h2, if_true, if_false] at h
    · simp only [Sum.inr.injEq, Prod.mk.injEq, true_and] at h
      exact Prod.ext (by omega) h.2
    · simp at h
    · simp at h
    · simpa using h
  have hind : iIndepFun (fun p : ℤ × Fin B => Z p.1 p.2) P := by
    have := cs.indep.precomp hg
    convert this using 1
    funext p
    simp only [Z, g, Function.comp]
    split_ifs <;> rfl
  refine ⟨⟨Z, ?_, hind, ?_⟩, ?_, ?_⟩
  · intro s a
    simp only [Z]
    split_ifs
    · exact cs.meas_aux _ _ _
    · exact cs.meas_act _ _
  · intro s a
    simp only [Z]
    split_ifs
    · exact cs.law_aux _ _ _
    · exact cs.law_act _ _
  · intro j a ω
    simp only [Z]
    rw [if_pos (by omega)]
    congr 2
    omega
  · intro s a ω hs
    simp only [Z]
    rw [if_neg (by omega)]

private lemma pc_norm_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : DynParams) (C : Covariances m n)
    (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n) (hD : 0 < riskSigma C D)
    (F : FrozenParams m n B) (hFC : F.C = C) (hFA : F.A = Ahat C D) (hFβ : F.β = p.β)
    (S : FrozenSamples P m n B)
    (hS1 : ∀ (j : ℕ) a ω, S.zw ((t : ℤ) - (j : ℤ)) a ω = cs.aux (t : ℤ) j a ω)
    (hS2 : ∀ s a ω, (t : ℤ) < s → S.zw s a ω = cs.act s a ω) :
    ∀ᵐ ω ∂P, Summable (fun j : ℕ =>
        emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) ∧
      ∀ k : ℕ, normChainPath p C cs t D M ω k = frozenBuf F S ((t : ℤ) + (k : ℤ) - 1) ω := by
  have hsq : 0 < Real.sqrt (2 * riskSigma C D) := Real.sqrt_pos.mpr (by linarith)
  have hfb : ∀ (s : ℤ) ω, batchGrad D (fun a => phys C (S.zw s a ω)) =
      Real.sqrt (2 * riskSigma C D) • frozenBatchG F S s ω := by
    intro s ω
    have h1 : frozenBatchG F S s ω = Gnorm C D (fun a => phys C (S.zw s a ω)) := by
      rw [eqn_app_setup_normalized_grad]
      unfold frozenBatchG
      rw [hFA, hFC]
    rw [h1]
    unfold Gnorm
    rw [smul_smul, mul_inv_cancel₀ hsq.ne', one_smul]
  filter_upwards [(lem_app_setup_ema_law_i F S).1, (lem_app_setup_ema_law_ii F S).1] with ω h1 h2
  have hterm : ∀ j : ℕ, emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω) =
      Real.sqrt (2 * riskSigma C D) •
        (emaW F.β j • frozenBatchG F S ((t : ℤ) - 1 + 1 - (j : ℤ)) ω) := by
    intro j
    rw [show (t : ℤ) - 1 + 1 - (j : ℤ) = (t : ℤ) - (j : ℤ) by ring, smul_comm, ← hfb, hFβ]
    simp only [physBatch, hS1]
    rfl
  have hsum : Summable (fun j : ℕ => emaW F.β j • frozenBatchG F S ((t : ℤ) - 1 + 1 - (j : ℤ)) ω) :=
    pc_summable_of_fro _ (h1 ((t : ℤ) - 1))
  have hsum' : Summable (fun j : ℕ =>
      emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) := by
    simp_rw [hterm]
    exact hsum.const_smul _
  refine ⟨hsum', ?_⟩
  have h0 : normChainPath p C cs t D M ω 0 = frozenBuf F S ((t : ℤ) + ((0 : ℕ) : ℤ) - 1) ω := by
    simp only [normChainPath, def_app_dyn_chains, emaChain, chainInit]
    simp_rw [hterm]
    rw [tsum_const_smul'' _, smul_smul, inv_mul_cancel₀ hsq.ne', one_smul]
    simp only [frozenBuf, Nat.cast_zero, add_zero]
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    have hrec := h2 ((t : ℤ) + ((k + 1 : ℕ) : ℤ) - 1)
    have e1 : (t : ℤ) + ((k + 1 : ℕ) : ℤ) - 1 - 1 = (t : ℤ) + (k : ℤ) - 1 := by push_cast; ring
    have e2 : (t : ℤ) + ((k + 1 : ℕ) : ℤ) - 1 + 1 = (t : ℤ) + (k : ℤ) + 1 := by push_cast; ring
    rw [hrec, e1, e2, ← ih, hFβ]
    have hact : batchGrad D (physBatch C (cs.act ((t : ℤ) + (k : ℤ) + 1)) ω) =
        Real.sqrt (2 * riskSigma C D) • frozenBatchG F S ((t : ℤ) + (k : ℤ) + 1) ω := by
      rw [← hfb]
      have : ∀ a, S.zw ((t : ℤ) + (k : ℤ) + 1) a ω = cs.act ((t : ℤ) + (k : ℤ) + 1) a ω :=
        fun a => hS2 _ a ω (by omega)
      simp only [this]
      rfl
    simp only [normChainPath, def_app_dyn_chains, emaChain] at ih ⊢
    rw [hact, smul_add, smul_comm (Real.sqrt (2 * riskSigma C D))⁻¹ p.β,
      smul_comm (Real.sqrt (2 * riskSigma C D))⁻¹ (1 - p.β),
      smul_smul (Real.sqrt (2 * riskSigma C D))⁻¹, inv_mul_cancel₀ hsq.ne', one_smul]

private lemma pc_entry_le_fro (A : Mat m n) (i : Fin m) (j : Fin n) : |A i j| ≤ fro A := by
  unfold fro
  refine Real.le_sqrt_of_sq_le ?_
  have h1 : ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
  have h2 : ∑ j', ‖A i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  simpa only [Real.norm_eq_abs, sq_abs] using h1.trans h2

private lemma pc_Q_entry_le (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (K : Mat m n) (i : Fin m) (j : Fin n) :
    |Q ϱ K i j| ≤ (m : ℝ) + 1 := by
  have h := (lem_app_setup_filter_i ϱ hϱ K)
  have hr : (K.rank : ℝ) ≤ m := by
    exact_mod_cast h.2.2.1.trans (min_le_left _ _)
  have h1 := pc_entry_le_fro (Q ϱ K) i j
  have h2 : fro (Q ϱ K) ^ 2 ≤ m := h.2.1.trans hr
  nlinarith [abs_nonneg (Q ϱ K i j), sq_nonneg (fro (Q ϱ K) - 1)]

private theorem pc_batch_sm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    MeasureTheory.StronglyMeasurable (frozenBatchG F S s) := by
  have hc : Continuous (fun q : Vec m × Vec n =>
      (dotProduct q.1 (Matrix.mulVec F.A q.2)) •
        (rOut F.C * outer q.1 q.2 * rIn F.C)) := by fun_prop
  unfold frozenBatchG
  refine MeasureTheory.StronglyMeasurable.const_smul ?_ ((B : ℝ))⁻¹
  exact Finset.stronglyMeasurable_fun_sum Finset.univ fun a _ =>
    hc.comp_stronglyMeasurable (S.meas s a).stronglyMeasurable

private theorem pc_buf_aesm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) : AEStronglyMeasurable (frozenBuf F S t) P := by
  refine aestronglyMeasurable_of_tendsto_ae Filter.atTop (f := fun N ω =>
    ∑ j ∈ Finset.range N, emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω)
    (fun N => ?_) ?_
  · exact (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ =>
      (pc_batch_sm F S _).const_smul (emaW F.β j)).aestronglyMeasurable
  · filter_upwards [(lem_app_setup_ema_law_i F S).1] with ω hω
    exact (pc_summable_of_fro _ (hω t)).hasSum.tendsto_sum_nat

private theorem pc_measurable_Qpath (ϱ : ℝ) (hϱ : 0 ≤ ϱ) :
    Measurable (fun (x : ℕ → Mat m n) (k : ℕ) => Q ϱ (x k)) := by
  refine measurable_pi_iff.2 fun k => ?_
  exact (measurable_Q (m := m) (n := n)).comp
    ((measurable_const (a := (⟨ϱ, hϱ⟩ : Set.Ici (0 : ℝ)))).prodMk (measurable_pi_apply k))

/-- `lem:app-dyn-chains` (cr-2026-10-23), part (i): the normalized stationary chain has the law of the
frozen-state buffers `(M_{t'})_{t' ≥ t-1}` at the normalized state `Â(D)`, and the chain updates
`V_r = Q_ϱ(N_r/√(2𝓡(D)))` have the law of the frozen updates. Also `V̄(D) = E V_0` is the expected
frozen update. The frozen model is `F` (`Muon.Setup.FrozenParams`) with covariances `C`, normalized
state `F.A = Â(D)` and momentum `β`, driven by any frozen sample family `S` on `(Ω', P')`
(`def:app-setup-frozen`). Statement verbatim from `section.tex` (ll. 497–514):
```latex
\begin{lemma}[Laws of the frozen chains]\label{lem:app-dyn-chains}
Let $D,m$ be deterministic with $\cR(D)>0$, and put $C_M\defeq C_\Sigma^2(\gamma_\star+2)^2$.
\begin{enumerate}[label=(\roman*)]
\item The sequence $(N_r/\sqrt{2\cR(D)})_{r\ge-1}$ has the law of the
buffers $(M_{t'})_{t'\ge t-1}$ of the frozen-state model of
\cref{def:app-setup-frozen} at the normalized state $\widehat A(D)$, with the
samples indexed by time, and $V_r=\Qridge\ridge(N_r/\sqrt{2\cR(D)})$ is its
update. In particular $(V_r)_{r\ge0}$ is stationary, $\overline V(D)$ is the
expected frozen update $\EE\,\Qridge\ridge(\Mt)$ at $\widehat A(D)$, and the lag
covariances, the integrated covariance measure $\mathfrak C_{\mathrm{int}}(\ridge)$
and the finite-time measures $\mathfrak F_T(\ridge)$ of the volatility section
at the state $\widehat A(D)$ are those of $(V_r)$.
\item For $r\ge-1$, $\widehat N_r-N_r=\bmom^{r+1}(m-N_{-1})$.
\item $\EE\norm{N_{-1}}_\F^2\le2\cR(D)\,C_MB$.
\item At a step $t<t_{\rm stop}$, the statements (i)--(iii) hold
conditionally on $\cF_t$ with $D=\Dt$ and $m=M^\circ_{t-1}$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_dyn_chains_i {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] (p : DynParams) (C : Covariances m n)
    (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n) (hD : 0 < riskSigma C D)
    (F : FrozenParams m n B) (hFC : F.C = C) (hFA : F.A = Ahat C D) (hFβ : F.β = p.β)
    (S : FrozenSamples P' m n B) :
    (∀ᵐ ω ∂P, Summable (fun j : ℕ => emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))) ∧
    P.map (fun ω => normChainPath p C cs t D M ω) =
        P'.map (fun ω' (k : ℕ) => frozenBuf F S ((t : ℤ) + (k : ℤ) - 1) ω') ∧
    P.map (fun ω (k : ℕ) => (def_app_dyn_chains p C cs t D M ω).statV k) =
        P'.map (fun ω' (k : ℕ) => frozenUpd F S p.ϱ ((t : ℤ) + (k : ℤ) - 1) ω') ∧
    ((∀ i j, Integrable (fun ω => (def_app_dyn_chains p C cs t D M ω).statV 1 i j) P) ∧
      (∀ i j, Integrable (fun ω' => frozenUpd F S p.ϱ (t : ℤ) ω' i j) P')) ∧
    mean P (fun ω => (def_app_dyn_chains p C cs t D M ω).statV 1) =
        mean P' (fun ω' => frozenUpd F S p.ϱ (t : ℤ) ω') := by
  classical
  obtain ⟨S0, hS1, hS2⟩ := pc_merged_exists cs t
  have hnorm := pc_norm_eq p C cs t D M hD F hFC hFA hFβ S0 hS1 hS2
  have hsq : 0 < Real.sqrt (2 * riskSigma C D) := Real.sqrt_pos.mpr (by linarith)
  have hlaw : P.map (fun ω (q : ℤ × Fin B) => S0.zw q.1 q.2 ω) =
      P'.map (fun ω' (q : ℤ × Fin B) => S.zw q.1 q.2 ω') := by
    have e0 := iIndepFun.map_fun_eq_infinitePi_map (P := P)
      (X := fun q : ℤ × Fin B => S0.zw q.1 q.2) (fun q => S0.meas q.1 q.2) S0.indep
    have e1 := iIndepFun.map_fun_eq_infinitePi_map (P := P')
      (X := fun q : ℤ × Fin B => S.zw q.1 q.2) (fun q => S.meas q.1 q.2) S.indep
    refine e0.trans (Eq.trans ?_ e1.symm)
    congr 1
    funext q
    rw [S0.law, S.law]
  have hLeq : (fun ω => normChainPath p C cs t D M ω) =ᵐ[P]
      (fun ω (k : ℕ) => frozenBuf F S0 ((t : ℤ) + (k : ℤ) - 1) ω) := by
    filter_upwards [hnorm] with ω hω
    funext k
    exact hω.2 k
  have hbuf0 : AEMeasurable (fun ω (k : ℕ) => frozenBuf F S0 ((t : ℤ) + (k : ℤ) - 1) ω) P :=
    AEMeasurable.of_eval fun k => (pc_buf_aesm F S0 _).aemeasurable
  have hbuf1 : AEMeasurable (fun ω' (k : ℕ) => frozenBuf F S ((t : ℤ) + (k : ℤ) - 1) ω') P' :=
    AEMeasurable.of_eval fun k => (pc_buf_aesm F S _).aemeasurable
  have hLm : AEMeasurable (fun ω => normChainPath p C cs t D M ω) P := hbuf0.congr hLeq.symm
  have hlawL : P.map (fun ω => normChainPath p C cs t D M ω) =
      P'.map (fun ω' (k : ℕ) => frozenBuf F S ((t : ℤ) + (k : ℤ) - 1) ω') :=
    (Measure.map_congr hLeq).trans (pd_buf_law_eq F S0 S (t : ℤ) hlaw)
  -- the update path
  have hVeq : (fun ω (k : ℕ) => (def_app_dyn_chains p C cs t D M ω).statV k) =
      (fun (x : ℕ → Mat m n) (k : ℕ) => Q p.ϱ (x k)) ∘
        (fun ω => normChainPath p C cs t D M ω) := by
    funext ω k
    simp only [Function.comp, normChainPath, def_app_dyn_chains, physRidge]
    rw [← prop_app_setup_scaling_ii p.ϱ p.hϱ.le _ (riskSigma C D) hD, smul_smul,
      mul_inv_cancel₀ hsq.ne', one_smul]
  have hQm := pc_measurable_Qpath (m := m) (n := n) p.ϱ p.hϱ.le
  have hVm : AEMeasurable (fun ω (k : ℕ) => (def_app_dyn_chains p C cs t D M ω).statV k) P := by
    rw [hVeq]; exact hQm.comp_aemeasurable hLm
  have hUm : AEMeasurable (fun ω' (k : ℕ) => frozenUpd F S p.ϱ ((t : ℤ) + (k : ℤ) - 1) ω') P' := by
    have : (fun ω' (k : ℕ) => frozenUpd F S p.ϱ ((t : ℤ) + (k : ℤ) - 1) ω') =
        (fun (x : ℕ → Mat m n) (k : ℕ) => Q p.ϱ (x k)) ∘
          (fun ω' (k : ℕ) => frozenBuf F S ((t : ℤ) + (k : ℤ) - 1) ω') := by
      funext ω' k; rfl
    rw [this]; exact hQm.comp_aemeasurable hbuf1
  have hlawV : P.map (fun ω (k : ℕ) => (def_app_dyn_chains p C cs t D M ω).statV k) =
      P'.map (fun ω' (k : ℕ) => frozenUpd F S p.ϱ ((t : ℤ) + (k : ℤ) - 1) ω') := by
    have e1 : (fun ω' (k : ℕ) => frozenUpd F S p.ϱ ((t : ℤ) + (k : ℤ) - 1) ω') =
        (fun (x : ℕ → Mat m n) (k : ℕ) => Q p.ϱ (x k)) ∘
          (fun ω' (k : ℕ) => frozenBuf F S ((t : ℤ) + (k : ℤ) - 1) ω') := by
      funext ω' k; rfl
    rw [hVeq, e1, ← AEMeasurable.map_map_of_aemeasurable hQm.aemeasurable hLm,
      ← AEMeasurable.map_map_of_aemeasurable hQm.aemeasurable hbuf1, hlawL]
  have hent : ∀ i j, Measurable (fun x : ℕ → Mat m n => x 1 i j) := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_pi_apply 1))
  have hb : ∀ (K : Mat m n) i j, |Q p.ϱ K i j| ≤ (m : ℝ) + 1 :=
    fun K i j => pc_Q_entry_le p.ϱ p.hϱ.le K i j
  have hi1 : ∀ i j, Integrable (fun ω => (def_app_dyn_chains p C cs t D M ω).statV 1 i j) P := by
    intro i j
    refine Integrable.of_bound (C := (m : ℝ) + 1) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((hent i j).comp_aemeasurable hVm).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact pc_Q_entry_le (physRidge p C D)
        (mul_nonneg (by linarith) p.hϱ.le) _ i j
  have hi2 : ∀ i j, Integrable (fun ω' => frozenUpd F S p.ϱ (t : ℤ) ω' i j) P' := by
    intro i j
    refine Integrable.of_bound (C := (m : ℝ) + 1) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · have := ((hent i j).comp_aemeasurable hUm).aestronglyMeasurable
      refine this.congr (Filter.Eventually.of_forall fun ω' => ?_)
      simp
    · rw [Real.norm_eq_abs]
      exact hb _ i j
  refine ⟨hnorm.mono fun ω hω => hω.1, hlawL, hlawV, ⟨hi1, hi2⟩, ?_⟩
  ext i j
  simp only [mean, Matrix.of_apply]
  have h1 : ∫ ω, (def_app_dyn_chains p C cs t D M ω).statV 1 i j ∂P =
      ∫ x, x 1 i j ∂(P.map (fun ω (k : ℕ) => (def_app_dyn_chains p C cs t D M ω).statV k)) := by
    rw [integral_map hVm (hent i j).aestronglyMeasurable]
  have h2 : ∫ x, x 1 i j ∂(P'.map (fun ω' (k : ℕ) =>
      frozenUpd F S p.ϱ ((t : ℤ) + (k : ℤ) - 1) ω')) = ∫ ω', frozenUpd F S p.ϱ (t : ℤ) ω' i j ∂P' := by
    rw [integral_map hUm (hent i j).aestronglyMeasurable]
    simp
  rw [h1, hlawV, h2]

/-- `lem:app-dyn-chains` (cr-2026-10-23), part (ii): the same-buffer and stationary chains differ by
`N̂_r - N_r = β^{r+1}(M - N_{-1})`, pathwise (indices `k = r + 1`). Statement verbatim from
`section.tex` (ll. 497–514):
```latex
\begin{lemma}[Laws of the frozen chains]\label{lem:app-dyn-chains}
Let $D,m$ be deterministic with $\cR(D)>0$, and put $C_M\defeq C_\Sigma^2(\gamma_\star+2)^2$.
\begin{enumerate}[label=(\roman*)]
\item The sequence $(N_r/\sqrt{2\cR(D)})_{r\ge-1}$ has the law of the
buffers $(M_{t'})_{t'\ge t-1}$ of the frozen-state model of
\cref{def:app-setup-frozen} at the normalized state $\widehat A(D)$, with the
samples indexed by time, and $V_r=\Qridge\ridge(N_r/\sqrt{2\cR(D)})$ is its
update. In particular $(V_r)_{r\ge0}$ is stationary, $\overline V(D)$ is the
expected frozen update $\EE\,\Qridge\ridge(\Mt)$ at $\widehat A(D)$, and the lag
covariances, the integrated covariance measure $\mathfrak C_{\mathrm{int}}(\ridge)$
and the finite-time measures $\mathfrak F_T(\ridge)$ of the volatility section
at the state $\widehat A(D)$ are those of $(V_r)$.
\item For $r\ge-1$, $\widehat N_r-N_r=\bmom^{r+1}(m-N_{-1})$.
\item $\EE\norm{N_{-1}}_\F^2\le2\cR(D)\,C_MB$.
\item At a step $t<t_{\rm stop}$, the statements (i)--(iii) hold
conditionally on $\cF_t$ with $D=\Dt$ and $m=M^\circ_{t-1}$.
\end{enumerate}
\end{lemma}
```
-/
private theorem emaChain_sub_eq (β : ℝ) (D : Mat m n) (G : ℤ → Batch m n B) (t : ℕ)
    (init M : Mat m n) (k : ℕ) :
    emaChain β D G t M k - emaChain β D G t init k = (β ^ k) • (M - init) := by
  induction k with
  | zero => simp [emaChain]
  | succ k ih =>
    have h : emaChain β D G t M (k + 1) - emaChain β D G t init (k + 1) =
        β • (emaChain β D G t M k - emaChain β D G t init k) := by
      simp only [emaChain, smul_sub]
      abel
    rw [h, ih, smul_smul, ← pow_succ']

theorem lem_app_dyn_chains_ii (p : DynParams) (C : Covariances m n) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n)
    (ω : Ω) (k : ℕ) :
    (def_app_dyn_chains p C cs t D M ω).same k - (def_app_dyn_chains p C cs t D M ω).stat k =
      (p.β ^ k) • (M - (def_app_dyn_chains p C cs t D M ω).stat 0) := by
  exact emaChain_sub_eq p.β D _ t _ M k

private theorem pd_fro_sq (K : Mat m n) :
    fro K ^ 2 = ∑ i, ∑ j, K i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (by positivity)]
  simp only [Real.norm_eq_abs, sq_abs]

private theorem pd_fro_sq_smul (c : ℝ) (K : Mat m n) :
    fro (c • K) ^ 2 = c ^ 2 * fro K ^ 2 := by
  simp only [pd_fro_sq, Matrix.smul_apply, smul_eq_mul, mul_pow,
    Finset.mul_sum]

private theorem pd_fro_sq_meas : Measurable (fun K : Mat m n => fro K ^ 2) := by
  simp_rw [pd_fro_sq]
  fun_prop

open scoped Matrix.Norms.Frobenius in
private theorem pd_fro_pos {K : Mat m n} (hK : K ≠ 0) : 0 < fro K := by
  rw [fro_eq_norm]
  exact norm_pos_iff.mpr hK

open scoped Matrix.Norms.Frobenius in
private theorem pd_summable_of_fro (f : ℕ → Mat m n)
    (hf : Summable (fun j => fro (f j))) : Summable f := by
  apply Summable.of_norm
  simpa only [fro_eq_norm] using hf

private theorem pd_batch_sm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    StronglyMeasurable (frozenBatchG F S s) := by
  have hc : Continuous (fun q : Vec m × Vec n =>
      (dotProduct q.1 (Matrix.mulVec F.A q.2)) •
        (rOut F.C * outer q.1 q.2 * rIn F.C)) := by fun_prop
  unfold frozenBatchG
  refine StronglyMeasurable.const_smul ?_ ((B : ℝ))⁻¹
  exact Finset.stronglyMeasurable_fun_sum Finset.univ fun a _ =>
    hc.comp_stronglyMeasurable (S.meas s a).stronglyMeasurable

private theorem pd_buf_aesm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) : AEStronglyMeasurable (frozenBuf F S t) P := by
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
    ∑ j ∈ Finset.range N, emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω)
    (fun N => ?_) ?_
  · exact (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ =>
      (pd_batch_sm F S _).const_smul (emaW F.β j)).aestronglyMeasurable
  · filter_upwards [(lem_app_setup_ema_law_i F S).1] with ω hω
    exact (pd_summable_of_fro _ (hω t)).hasSum.tendsto_sum_nat

private theorem pd_frozen_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (γstar CSig : ℝ) (hS : SizeFin F.C B γstar CSig) (t : ℤ) :
    Integrable (fun ω => fro (frozenBuf F S t ω) ^ 2) P ∧
      ∫ ω, fro (frozenBuf F S t ω) ^ 2 ∂P ≤ cMConst CSig γstar * (B : ℝ) := by
  have hB : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hm : (m : ℝ) ≤ γstar * B :=
    (Nat.cast_le.mpr (le_max_left m n)).trans hS.1
  have hn : (n : ℝ) ≤ γstar * B :=
    (Nat.cast_le.mpr (le_max_right m n)).trans hS.1
  have hb := lem_app_vol_square_iii F S CSig γstar hS.2.1 hS.2.2 hm hn t
  have hb' : ENNReal.ofReal (B : ℝ) *
      (ENNReal.ofReal ((B : ℝ)⁻¹) *
        ∫⁻ ω, ENNReal.ofReal (fro (frozenBuf F S t ω) ^ 2) ∂P) ≤
      ENNReal.ofReal (B : ℝ) * ENNReal.ofReal (CSig ^ 2 * (γstar + 2) ^ 2) := by
    gcongr
  have hcancel : ENNReal.ofReal (B : ℝ) * ENNReal.ofReal ((B : ℝ)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hB.le, mul_inv_cancel₀ hB.ne', ENNReal.ofReal_one]
  rw [← mul_assoc, hcancel, one_mul] at hb'
  have hfin : (∫⁻ ω, ENNReal.ofReal (fro (frozenBuf F S t ω) ^ 2) ∂P) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top) hb'
  have hmeas := pd_fro_sq_meas.comp_aemeasurable (pd_buf_aesm F S t).aemeasurable
  have hint : Integrable (fun ω => fro (frozenBuf F S t ω) ^ 2) P :=
    (lintegral_ofReal_ne_top_iff_integrable
      hmeas.aestronglyMeasurable (ae_of_all _ fun ω => sq_nonneg _)).mp hfin
  refine ⟨hint, ?_⟩
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top) hb'
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => sq_nonneg _),
    ENNReal.toReal_ofReal (integral_nonneg fun ω => sq_nonneg _),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hB.le,
    ENNReal.toReal_ofReal (by positivity)] at hh
  simpa only [cMConst, mul_comm] using hh

private theorem pd_physgrad_cont (C : Covariances m n) (D : Mat m n) :
    Continuous (fun b : Fin B → Vec m × Vec n =>
      batchGrad D (fun a => phys C (b a))) := by
  unfold batchGrad grad resid phys outer
  fun_prop

private theorem pd_init_aesm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ)
    (D : Mat m n)
    (hs : ∀ᵐ ω ∂P, Summable (fun j : ℕ =>
      emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))) :
    AEStronglyMeasurable (chainInit p.β C D (cs.aux (t : ℤ))) P := by
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
    ∑ j ∈ Finset.range N,
      emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))
    (fun N => ?_) ?_
  · refine (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ => ?_).aestronglyMeasurable
    exact ((pd_physgrad_cont C D).measurable.comp
      (Measurable.of_eval fun a => cs.meas_aux (t : ℤ) j a)).stronglyMeasurable.const_smul
        (emaW p.β j)
  · filter_upwards [hs] with ω hω
    exact hω.hasSum.tendsto_sum_nat

private theorem pd_normpath_aemeas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ)
    (D M : Mat m n)
    (hs : ∀ᵐ ω ∂P, Summable (fun j : ℕ =>
      emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))) :
    AEMeasurable (fun ω => normChainPath p C cs t D M ω) P := by
  apply AEMeasurable.of_eval
  intro k
  have hk : AEStronglyMeasurable
      (fun ω => (def_app_dyn_chains p C cs t D M ω).stat k) P := by
    induction k with
    | zero => exact pd_init_aesm p C cs t D hs
    | succ k ih =>
      exact (ih.const_smul p.β).add
        (((pd_physgrad_cont C D).measurable.comp (Measurable.of_eval fun a =>
          cs.meas_act ((t : ℤ) + k + 1) a)).stronglyMeasurable.aestronglyMeasurable.const_smul
            (1 - p.β))
  exact (hk.const_smul ((Real.sqrt (2 * riskSigma C D))⁻¹)).aemeasurable

private theorem pd_Ahat_norm (C : Covariances m n) (D : Mat m n)
    (hD : 0 < riskSigma C D) : fro (Ahat C D) = 1 := by
  have hr := eqn_app_setup_whitened_risk C D
  have hs : fro (Ahat C D) ^ 2 = 1 := by
    rw [Ahat, pd_fro_sq_smul, inv_pow, Real.sq_sqrt (by linarith)]
    rw [show fro (Arot C D) ^ 2 = 2 * riskSigma C D by linarith,
      inv_mul_cancel₀ (by linarith)]
  have hn : 0 ≤ fro (Ahat C D) := Real.sqrt_nonneg _
  nlinarith

/-- `lem:app-dyn-chains` (cr-2026-10-23), part (iii): for deterministic `D` with `𝓡(D) > 0` and
`C_M = C_Σ²(γ⋆+2)²`, the auxiliary series defining `N_{-1}` converges almost surely, and
`E‖N_{-1}‖_F² ≤ 2𝓡(D) C_M B`. The standing size condition `SizeFin` (`max(N_out,N_in) ≤ γ⋆ B`,
`‖Σ_out‖, ‖Σ_in‖ ≤ C_Σ`) is `hS`. Statement verbatim from `section.tex` (ll. 497–514):
```latex
\begin{lemma}[Laws of the frozen chains]\label{lem:app-dyn-chains}
Let $D,m$ be deterministic with $\cR(D)>0$, and put $C_M\defeq C_\Sigma^2(\gamma_\star+2)^2$.
\begin{enumerate}[label=(\roman*)]
\item The sequence $(N_r/\sqrt{2\cR(D)})_{r\ge-1}$ has the law of the
buffers $(M_{t'})_{t'\ge t-1}$ of the frozen-state model of
\cref{def:app-setup-frozen} at the normalized state $\widehat A(D)$, with the
samples indexed by time, and $V_r=\Qridge\ridge(N_r/\sqrt{2\cR(D)})$ is its
update. In particular $(V_r)_{r\ge0}$ is stationary, $\overline V(D)$ is the
expected frozen update $\EE\,\Qridge\ridge(\Mt)$ at $\widehat A(D)$, and the lag
covariances, the integrated covariance measure $\mathfrak C_{\mathrm{int}}(\ridge)$
and the finite-time measures $\mathfrak F_T(\ridge)$ of the volatility section
at the state $\widehat A(D)$ are those of $(V_r)$.
\item For $r\ge-1$, $\widehat N_r-N_r=\bmom^{r+1}(m-N_{-1})$.
\item $\EE\norm{N_{-1}}_\F^2\le2\cR(D)\,C_MB$.
\item At a step $t<t_{\rm stop}$, the statements (i)--(iii) hold
conditionally on $\cF_t$ with $D=\Dt$ and $m=M^\circ_{t-1}$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_dyn_chains_iii {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B)
    (t : ℕ) (D M : Mat m n) (hD : 0 < riskSigma C D) (hS : SizeFin C B p.γstar p.CSig) :
    (∀ᵐ ω ∂P, Summable (fun j : ℕ => emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))) ∧
    Integrable (fun ω => fro ((def_app_dyn_chains p C cs t D M ω).stat 0) ^ 2) P ∧
    ∫ ω, fro ((def_app_dyn_chains p C cs t D M ω).stat 0) ^ 2 ∂P ≤
      2 * riskSigma C D * cMConst p.CSig p.γstar * (B : ℝ) := by
  have hB : 0 < B := by
    by_contra h
    have hb : B = 0 := by omega
    have hdim : max m n = 0 := by
      have hh := hS.1
      simp only [hb, Nat.cast_zero, mul_zero, Nat.cast_nonpos] at hh
      exact hh
    have hm : m = 0 := by omega
    have hr := eqn_app_setup_whitened_risk C D
    simp [hm, fro] at hr
    linarith
  have hA : fro (Ahat C D) = 1 := by
    exact pd_Ahat_norm C D hD
  let F : FrozenParams m n B := ⟨C, Ahat C D, hA, p.β, p.hβ, hB⟩
  let S : FrozenSamples P m n B :=
    ⟨cs.act, cs.meas_act, cs.indep.precomp Sum.inl_injective, cs.law_act⟩
  have hlaw := lem_app_dyn_chains_i p C cs t D M hD F rfl rfl rfl S
  have hmom : Integrable (fun ω => fro ((def_app_dyn_chains p C cs t D M ω).stat 0) ^ 2) P ∧
      ∫ ω, fro ((def_app_dyn_chains p C cs t D M ω).stat 0) ^ 2 ∂P ≤
        2 * riskSigma C D * cMConst p.CSig p.γstar * (B : ℝ) := by
    have hid : IdentDistrib (fun ω => normChainPath p C cs t D M ω)
        (fun ω (k : ℕ) => frozenBuf F S ((t : ℤ) + (k : ℤ) - 1) ω) P P :=
      ⟨pd_normpath_aemeas p C cs t D M hlaw.1,
        AEMeasurable.of_eval fun k => (pd_buf_aesm F S _).aemeasurable, hlaw.2.1⟩
    have hid0 : IdentDistrib (fun ω => fro (normChainPath p C cs t D M ω 0) ^ 2)
        (fun ω => fro (frozenBuf F S ((t : ℤ) - 1) ω) ^ 2) P P := by
      simpa only [Function.comp_def, Nat.cast_zero, add_zero] using
        hid.comp (pd_fro_sq_meas.comp (measurable_pi_apply 0))
    have hb := pd_frozen_moment F S p.γstar p.CSig hS ((t : ℤ) - 1)
    have hn : ∀ ω, fro ((def_app_dyn_chains p C cs t D M ω).stat 0) ^ 2 =
        (2 * riskSigma C D) * fro (normChainPath p C cs t D M ω 0) ^ 2 := by
      intro ω
      simp only [normChainPath, pd_fro_sq_smul, inv_pow,
        Real.sq_sqrt (show 0 ≤ 2 * riskSigma C D by linarith)]
      rw [← mul_assoc, mul_inv_cancel₀ (by linarith), one_mul]
    have hi : Integrable (fun ω => fro (normChainPath p C cs t D M ω 0) ^ 2) P := by
      exact hid0.integrable_iff.mpr (by simpa using hb.1)
    constructor
    · simpa only [hn] using hi.const_mul (2 * riskSigma C D)
    · simp_rw [hn]
      rw [integral_const_mul, hid0.integral_eq]
      simpa only [Function.comp_apply, Nat.cast_zero, add_zero, mul_assoc] using
        mul_le_mul_of_nonneg_left hb.2 (show 0 ≤ 2 * riskSigma C D by linarith)
  exact ⟨hlaw.1, hmom⟩

private lemma pd_freeze_bound0 {Ω α β : Type*} (𝓕 : MeasurableSpace Ω)
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

private lemma pc_emaChain_congr (β : ℝ) (D : Mat m n) (G G' : ℤ → Batch m n B) (t : ℕ)
    (init : Mat m n) (h : ∀ k : ℕ, G ((t : ℤ) + k + 1) = G' ((t : ℤ) + k + 1)) (k : ℕ) :
    emaChain β D G t init k = emaChain β D G' t init k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [emaChain, ih, h k]

private lemma pc_chain_rep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) :
    ∃ Ξ : Mat m n × ((ℕ × Fin B → Vec m × Vec n) × (ℕ × Fin B → Vec m × Vec n)) → ℕ → Mat m n,
      (∀ k, Measurable (fun q => Ξ q k)) ∧
      (∀ d y, Arot C d = 0 → Ξ (d, y) 0 = 0) ∧
      ∀ (d M : Mat m n) ω,
        Summable (fun j : ℕ => emaW p.β j • batchGrad d (physBatch C (cs.aux (t : ℤ) j) ω)) →
        ∀ k, (def_app_dyn_chains p C cs t d M ω).stat k =
          Ξ (d, ((fun q : ℕ × Fin B => cs.aux (t : ℤ) q.1 q.2 ω),
                 (fun q : ℕ × Fin B => cs.act ((t : ℤ) + 1 + (q.1 : ℤ)) q.2 ω))) k := by
  let N0 : Mat m n × ((ℕ × Fin B → Vec m × Vec n) × (ℕ × Fin B → Vec m × Vec n)) → Mat m n :=
    fun q => Matrix.of fun i l => limUnder Filter.atTop (fun N : ℕ => ∑ j ∈ Finset.range N,
      (emaW p.β j • batchGrad q.1 (fun a => phys C (q.2.1 (j, a)))) i l)
  let Gy : ((ℕ × Fin B → Vec m × Vec n) × (ℕ × Fin B → Vec m × Vec n)) → ℤ → Batch m n B :=
    fun y s a => phys C (y.2 (((s - (t : ℤ) - 1).toNat), a))
  have hcont : ∀ j : ℕ, Continuous (fun q : Mat m n × ((ℕ × Fin B → Vec m × Vec n) ×
      (ℕ × Fin B → Vec m × Vec n)) => batchGrad q.1 (fun a => phys C (q.2.1 (j, a)))) := by
    intro j
    unfold batchGrad Muon.Setup.grad resid phys outer
    fun_prop
  have hN0 : Measurable N0 := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun l => ?_
    have hf : ∀ N : ℕ, MeasureTheory.StronglyMeasurable
        (fun q : Mat m n × ((ℕ × Fin B → Vec m × Vec n) × (ℕ × Fin B → Vec m × Vec n)) =>
          ∑ j ∈ Finset.range N,
            (emaW p.β j • batchGrad q.1 (fun a => phys C (q.2.1 (j, a)))) i l) := fun N =>
      (Finset.measurable_sum _ fun j _ => by
        have := ((measurable_pi_apply l).comp (measurable_pi_apply i)).comp
          ((hcont j).measurable.const_smul (emaW p.β j))
        exact this).stronglyMeasurable
    exact (MeasureTheory.StronglyMeasurable.limUnder (l := Filter.atTop) hf).measurable
  refine ⟨fun q k => emaChain p.β q.1 (Gy q.2) t (N0 q) k, ?_, ?_, ?_⟩
  · intro k
    induction k with
    | zero => exact hN0
    | succ k ih =>
      simp only [emaChain]
      have hc : Continuous (fun q : Mat m n × ((ℕ × Fin B → Vec m × Vec n) ×
          (ℕ × Fin B → Vec m × Vec n)) => batchGrad q.1 (Gy q.2 ((t : ℤ) + k + 1))) := by
        unfold Gy batchGrad Muon.Setup.grad resid phys outer
        fun_prop
      exact (ih.const_smul p.β).add (hc.measurable.const_smul (1 - p.β))
  · intro d y hd
    have h0 : ∀ j : ℕ, batchGrad d (fun a => phys C (y.1 (j, a))) = 0 := by
      intro j
      unfold batchGrad
      rw [eqn_app_setup_whitened_grad (zw := fun a => y.1 (j, a)), hd]
      simp
    show N0 (d, y) = 0
    ext i l
    simp only [N0, h0]
    simpa using (tendsto_const_nhds (x := (0 : ℝ)) (f := Filter.atTop (α := ℕ))).limUnder_eq
  · intro d M ω hs k
    have hinit : chainInit p.β C d (cs.aux (t : ℤ)) ω = N0 (d, ((fun q : ℕ × Fin B =>
        cs.aux (t : ℤ) q.1 q.2 ω), (fun q : ℕ × Fin B => cs.act ((t : ℤ) + 1 + (q.1 : ℤ)) q.2 ω))) := by
      ext i l
      show (∑' j : ℕ, emaW p.β j • batchGrad d (physBatch C (cs.aux (t : ℤ) j) ω)) i l = _
      rw [← (Pi.hasSum.1 (Pi.hasSum.1 hs.hasSum i) l).tsum_eq]
      have hsk : Summable fun j : ℕ =>
          (emaW p.β j • batchGrad d (physBatch C (cs.aux (t : ℤ) j) ω)) i l :=
        Pi.summable.1 (Pi.summable.1 hs i) l
      exact (hsk.hasSum.tendsto_sum_nat.limUnder_eq).symm
    simp only [def_app_dyn_chains]
    rw [hinit]
    refine pc_emaChain_congr p.β d _ _ t _ (fun k' => ?_) k
    funext a
    simp only [physBatch, Gy]
    have this : ((t : ℤ) + k' + 1 - (t : ℤ) - 1).toNat = k' := by omega
    have e : (t : ℤ) + k' + 1 = (t : ℤ) + 1 + k' := by ring
    rw [this, e]

private lemma pc_batchGrad_basis (d : Mat m n) (b : Batch m n B) :
    batchGrad d b = ∑ i : Fin m, ∑ k : Fin n, d i k • batchGrad (Matrix.single i k (1 : ℝ)) b := by
  let L : Mat m n →ₗ[ℝ] Mat m n :=
    { toFun := fun d => batchGrad d b
      map_add' := by
        intro d1 d2
        simp only [batchGrad, Muon.Setup.grad, resid, Matrix.add_mulVec, dotProduct_add,
          add_smul, Finset.sum_add_distrib, smul_add]
      map_smul' := by
        intro c d
        simp only [batchGrad, Muon.Setup.grad, resid, Matrix.smul_mulVec, dotProduct_smul,
          smul_eq_mul, RingHom.id_apply, smul_smul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        ring }
  have hL : ∀ d, batchGrad d b = L d := fun d => rfl
  conv_lhs => rw [hL, Matrix.matrix_eq_sum_single d]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  have : Matrix.single i k (d i k) = d i k • Matrix.single i k (1 : ℝ) := by
    ext x y
    simp [Matrix.single_apply]
  rw [this, map_smul]
  rfl

private lemma pc_summable_all {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : DynParams) (C : Covariances m n)
    (cs : ChainSamples P m n B) (t : ℕ) (hS : SizeFin C B p.γstar p.CSig) :
    ∀ᵐ ω ∂P, ∀ d : Mat m n,
      Summable (fun j : ℕ => emaW p.β j • batchGrad d (physBatch C (cs.aux (t : ℤ) j) ω)) := by
  have hE : ∀ (i : Fin m) (k : Fin n), ∀ᵐ ω ∂P,
      Summable (fun j : ℕ => emaW p.β j •
        batchGrad (Matrix.single i k (1 : ℝ)) (physBatch C (cs.aux (t : ℤ) j) ω)) := by
    intro i k
    by_cases hpos : 0 < riskSigma C (Matrix.single i k (1 : ℝ))
    · exact (lem_app_dyn_chains_iii p C cs t _ 0 hpos hS).1
    · have hr := eqn_app_setup_whitened_risk C (Matrix.single i k (1 : ℝ))
      have h0 : fro (Arot C (Matrix.single i k (1 : ℝ))) ^ 2 = 0 := by
        have := sq_nonneg (fro (Arot C (Matrix.single i k (1 : ℝ))))
        rw [not_lt] at hpos
        linarith
      have hA : Arot C (Matrix.single i k (1 : ℝ)) = 0 := by
        by_contra hne
        have := pd_fro_pos hne
        nlinarith
      refine Filter.Eventually.of_forall fun ω => ?_
      have hz : ∀ j : ℕ, batchGrad (Matrix.single i k (1 : ℝ))
          (physBatch C (cs.aux (t : ℤ) j) ω) = 0 := by
        intro j
        unfold batchGrad physBatch
        rw [eqn_app_setup_whitened_grad (zw := fun a => cs.aux (t : ℤ) j a ω), hA]
        simp
      simp only [hz, smul_zero]
      exact summable_zero
  have hall : ∀ᵐ ω ∂P, ∀ (i : Fin m) (k : Fin n), Summable (fun j : ℕ => emaW p.β j •
      batchGrad (Matrix.single i k (1 : ℝ)) (physBatch C (cs.aux (t : ℤ) j) ω)) :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun k => hE i k
  filter_upwards [hall] with ω hω d
  have : (fun j : ℕ => emaW p.β j • batchGrad d (physBatch C (cs.aux (t : ℤ) j) ω)) =
      fun j => ∑ i : Fin m, ∑ k : Fin n, d i k • (emaW p.β j •
        batchGrad (Matrix.single i k (1 : ℝ)) (physBatch C (cs.aux (t : ℤ) j) ω)) := by
    funext j
    rw [pc_batchGrad_basis d, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  rw [this]
  exact summable_sum fun i _ => summable_sum fun k _ => (hω i k).const_smul _


/-- `lem:app-dyn-chains` (cr-2026-10-23), part (iv): at a step `t` before the stopping time, with
`D = Δ_t` and `M = M°_{t-1}` measurable with respect to the past `𝓕` (`F_t`) and the future
`chainFuture cs t` independent of `𝓕`, the bound of part (iii) holds conditionally on `𝓕`, and the
conditional law of the normalized chain is the frozen one: for every bounded measurable `Φ`, the
conditional expectation of `Φ` of the path equals the integral with `D` and `M` frozen at their
`𝓕`-values (freezing). Statement verbatim from `section.tex` (ll. 497–514):
```latex
\begin{lemma}[Laws of the frozen chains]\label{lem:app-dyn-chains}
Let $D,m$ be deterministic with $\cR(D)>0$, and put $C_M\defeq C_\Sigma^2(\gamma_\star+2)^2$.
\begin{enumerate}[label=(\roman*)]
\item The sequence $(N_r/\sqrt{2\cR(D)})_{r\ge-1}$ has the law of the
buffers $(M_{t'})_{t'\ge t-1}$ of the frozen-state model of
\cref{def:app-setup-frozen} at the normalized state $\widehat A(D)$, with the
samples indexed by time, and $V_r=\Qridge\ridge(N_r/\sqrt{2\cR(D)})$ is its
update. In particular $(V_r)_{r\ge0}$ is stationary, $\overline V(D)$ is the
expected frozen update $\EE\,\Qridge\ridge(\Mt)$ at $\widehat A(D)$, and the lag
covariances, the integrated covariance measure $\mathfrak C_{\mathrm{int}}(\ridge)$
and the finite-time measures $\mathfrak F_T(\ridge)$ of the volatility section
at the state $\widehat A(D)$ are those of $(V_r)$.
\item For $r\ge-1$, $\widehat N_r-N_r=\bmom^{r+1}(m-N_{-1})$.
\item $\EE\norm{N_{-1}}_\F^2\le2\cR(D)\,C_MB$.
\item At a step $t<t_{\rm stop}$, the statements (i)--(iii) hold
conditionally on $\cF_t$ with $D=\Dt$ and $m=M^\circ_{t-1}$.
\end{enumerate}
\end{lemma}
```
The law at a frozen
state is part (i). -/
theorem lem_app_dyn_chains_iv {Ω : Type*} (𝓕 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (p : DynParams) (C : Covariances m n)
    (cs : ChainSamples P m n B) (t : ℕ) (hS : SizeFin C B p.γstar p.CSig)
    (h𝓕 : 𝓕 ≤ mΩ) (hind : Indep 𝓕 (chainFuture cs t) P)
    (D M : Ω → Mat m n) (hD : Measurable[𝓕] D) (hM : Measurable[𝓕] M)
    (hDpos : ∀ᵐ ω ∂P, 0 < riskSigma C (D ω))
    (hDint : Integrable (fun ω => riskSigma C (D ω)) P) :
    (∀ᵐ ω ∂P, Summable (fun j : ℕ =>
        emaW p.β j • batchGrad (D ω) (physBatch C (cs.aux (t : ℤ) j) ω))) ∧
    Integrable (fun ω => fro ((def_app_dyn_chains p C cs t (D ω) (M ω) ω).stat 0) ^ 2) P ∧
    (∀ᵐ ω ∂P, condExp 𝓕 P
        (fun ω' => fro ((def_app_dyn_chains p C cs t (D ω') (M ω') ω').stat 0) ^ 2) ω ≤
          2 * riskSigma C (D ω) * cMConst p.CSig p.γstar * (B : ℝ)) ∧
    (∀ Φ : (ℕ → Mat m n) → ℝ, Measurable Φ → (∃ K : ℝ, ∀ x, |Φ x| ≤ K) →
      ∀ᵐ ω ∂P, condExp 𝓕 P (fun ω' => Φ (normChainPath p C cs t (D ω') (M ω') ω')) ω =
        ∫ ω', Φ (normChainPath p C cs t (D ω) (M ω) ω') ∂P) := by
  obtain ⟨Ξ, hΞm, hΞ0, hΞeq⟩ := pc_chain_rep p C cs t
  have hsumall := pc_summable_all p C cs t hS
  have hsumD : ∀ᵐ ω ∂P, Summable (fun j : ℕ =>
      emaW p.β j • batchGrad (D ω) (physBatch C (cs.aux (t : ℤ) j) ω)) :=
    hsumall.mono fun ω h => h (D ω)
  let Yf : Ω → ((ℕ × Fin B → Vec m × Vec n) × (ℕ × Fin B → Vec m × Vec n)) := fun ω =>
    ((fun q : ℕ × Fin B => cs.aux (t : ℤ) q.1 q.2 ω),
      (fun q : ℕ × Fin B => cs.act ((t : ℤ) + 1 + (q.1 : ℤ)) q.2 ω))
  have hYm : Measurable Yf :=
    (measurable_pi_iff.2 fun q : ℕ × Fin B => cs.meas_aux (t : ℤ) q.1 q.2).prodMk
      (measurable_pi_iff.2 fun q : ℕ × Fin B => cs.meas_act ((t : ℤ) + 1 + (q.1 : ℤ)) q.2)
  have hindY : Indep 𝓕 (MeasurableSpace.comap Yf inferInstance) P := by
    refine indep_of_indep_of_le_right hind ?_
    have hle1 : ∀ q : ℕ × Fin B,
        MeasurableSpace.comap (cs.aux (t : ℤ) q.1 q.2) inferInstance ≤ chainFuture cs t := by
      intro q
      exact le_trans (le_iSup₂ (f := fun (j : ℕ) (a : Fin B) =>
        MeasurableSpace.comap (cs.aux (t : ℤ) j a) inferInstance) q.1 q.2) le_sup_right
    have hle2 : ∀ q : ℕ × Fin B,
        MeasurableSpace.comap (cs.act ((t : ℤ) + 1 + (q.1 : ℤ)) q.2) inferInstance ≤
          chainFuture cs t := by
      intro q
      refine le_trans ?_ le_sup_left
      refine le_trans ?_ (le_iSup (fun s : ℤ => ⨆ (_ : (t : ℤ) < s) (a : Fin B),
        MeasurableSpace.comap (cs.act s a) inferInstance) ((t : ℤ) + 1 + (q.1 : ℤ)))
      refine le_trans ?_ (le_iSup (fun _ : (t : ℤ) < (t : ℤ) + 1 + (q.1 : ℤ) => ⨆ (a : Fin B),
        MeasurableSpace.comap (cs.act ((t : ℤ) + 1 + (q.1 : ℤ)) a) inferInstance) (by omega))
      exact le_iSup (fun a : Fin B =>
        MeasurableSpace.comap (cs.act ((t : ℤ) + 1 + (q.1 : ℤ)) a) inferInstance) q.2
    change MeasurableSpace.comap Yf (MeasurableSpace.comap Prod.fst MeasurableSpace.pi ⊔
      MeasurableSpace.comap Prod.snd MeasurableSpace.pi) ≤ _
    rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
    refine sup_le ?_ ?_
    · unfold MeasurableSpace.pi
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun q => ?_
      rw [MeasurableSpace.comap_comp]
      exact hle1 q
    · unfold MeasurableSpace.pi
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun q => ?_
      rw [MeasurableSpace.comap_comp]
      exact hle2 q
  have hDm : Measurable D := hD.mono h𝓕 le_rfl
  have hRm : Measurable (fun d : Mat m n => riskSigma C d) := by
    simp_rw [eqn_app_setup_whitened_risk]
    refine (pd_fro_sq_meas.comp ?_).div_const 2
    have hc : Continuous (fun d : Mat m n => Arot C d) := by
      unfold Arot
      fun_prop
    exact hc.measurable
  have hpair : Measurable (fun ω => (D ω, Yf ω)) := hDm.prodMk hYm
  have hArot : ∀ d : Mat m n, ¬ 0 < riskSigma C d → Arot C d = 0 := by
    intro d hd
    have hr := eqn_app_setup_whitened_risk C d
    have h0 : fro (Arot C d) ^ 2 = 0 := by
      have := sq_nonneg (fro (Arot C d))
      rw [not_lt] at hd
      linarith
    by_contra hne
    have := pd_fro_pos hne
    nlinarith
  -- parts 2 and 3
  let f1 : Mat m n → ((ℕ × Fin B → Vec m × Vec n) × (ℕ × Fin B → Vec m × Vec n)) → ℝ :=
    fun d y => fro (Ξ (d, y) 0) ^ 2
  have hf1m : Measurable (Function.uncurry f1) := pd_fro_sq_meas.comp (hΞm 0)
  have key1 : ∀ d : Mat m n, Integrable (f1 d) (P.map Yf) ∧
      ∫ y, f1 d y ∂(P.map Yf) ≤ 2 * riskSigma C d * cMConst p.CSig p.γstar * (B : ℝ) := by
    intro d
    have hmeas : AEStronglyMeasurable (f1 d) (P.map Yf) :=
      (Measurable.of_uncurry_left hf1m).aestronglyMeasurable
    by_cases hd : 0 < riskSigma C d
    · obtain ⟨hs, hi, hv⟩ := lem_app_dyn_chains_iii p C cs t d 0 hd hS
      have heq : ∀ᵐ ω ∂P, fro ((def_app_dyn_chains p C cs t d 0 ω).stat 0) ^ 2 =
          f1 d (Yf ω) := hs.mono fun ω h => by rw [hΞeq d 0 ω h 0]
      have hi' : Integrable (fun ω => f1 d (Yf ω)) P := hi.congr heq
      refine ⟨(integrable_map_measure hmeas hYm.aemeasurable).2 hi', ?_⟩
      rw [integral_map hYm.aemeasurable hmeas]
      calc ∫ ω, f1 d (Yf ω) ∂P = ∫ ω, fro ((def_app_dyn_chains p C cs t d 0 ω).stat 0) ^ 2 ∂P :=
            (integral_congr_ae heq).symm
        _ ≤ _ := hv
    · have hA := hArot d hd
      have hf0 : ∀ y, f1 d y = 0 := by
        intro y
        simp only [f1, hΞ0 d y hA]
        have : fro (0 : Mat m n) = 0 := by simp [fro]
        simp [this]
      have hr0 : riskSigma C d = 0 := by
        rw [eqn_app_setup_whitened_risk, hA]
        have : fro (0 : Mat m n) = 0 := by simp [fro]
        simp [this]
      have hfd : f1 d = fun _ => 0 := funext hf0
      rw [hfd, hr0]
      simp
  have hg : Integrable (fun ω => 2 * riskSigma C (D ω) * cMConst p.CSig p.γstar * (B : ℝ)) P :=
    (hDint.const_mul (2 * cMConst p.CSig p.γstar * (B : ℝ))).congr
      (Filter.Eventually.of_forall fun ω => by ring)
  obtain ⟨hint1, hae1⟩ := pd_freeze_bound0 𝓕 h𝓕 hD hYm hindY hf1m
    (fun d y => sq_nonneg _)
    (g := fun d => 2 * riskSigma C d * cMConst p.CSig p.γstar * (B : ℝ)) hg
    (fun d => (key1 d).1) (fun d => (key1 d).2)
  have heq1 : ∀ᵐ ω ∂P, f1 (D ω) (Yf ω) =
      fro ((def_app_dyn_chains p C cs t (D ω) (M ω) ω).stat 0) ^ 2 :=
    hsumD.mono fun ω h => by rw [hΞeq (D ω) (M ω) ω h 0]
  have heq1' : (fun ω => f1 (D ω) (Yf ω)) =ᵐ[P]
      (fun ω => fro ((def_app_dyn_chains p C cs t (D ω) (M ω) ω).stat 0) ^ 2) := heq1
  refine ⟨hsumD, hint1.congr heq1', ?_, ?_⟩
  · have hc := condExp_congr_ae (m := 𝓕) heq1'
    filter_upwards [hc, hae1] with ω h1 h2
    rw [← h1]
    exact h2.2
  · intro Φ hΦ hbd
    obtain ⟨K, hK⟩ := hbd
    let f2 : Mat m n → ((ℕ × Fin B → Vec m × Vec n) × (ℕ × Fin B → Vec m × Vec n)) →
        ℝ := fun d y => Φ (fun k => (Real.sqrt (2 * riskSigma C d))⁻¹ • Ξ (d, y) k)
    have hf2m : Measurable (Function.uncurry f2) := by
      refine hΦ.comp (measurable_pi_iff.2 fun k => ?_)
      have hs : Measurable (fun q : Mat m n × ((ℕ × Fin B → Vec m × Vec n) ×
          (ℕ × Fin B → Vec m × Vec n)) => (Real.sqrt (2 * riskSigma C q.1))⁻¹) :=
        (((hRm.comp measurable_fst).const_mul 2).sqrt).inv
      exact hs.smul (hΞm k)
    have hfint : Integrable (fun ω => f2 (D ω) (Yf ω)) P :=
      Integrable.of_bound (hf2m.comp hpair).aestronglyMeasurable K
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]; exact hK _)
    have hc := Muon.Foundations.freezing_condExp 𝓕 h𝓕 hD hYm hindY hf2m hfint
    have heq2 : (fun ω' => Φ (normChainPath p C cs t (D ω') (M ω') ω')) =ᵐ[P]
        (fun ω' => f2 (D ω') (Yf ω')) := by
      filter_upwards [hsumD] with ω h
      simp only [f2, normChainPath]
      congr 1
      funext k
      simp only [normChainPath]
      rw [hΞeq (D ω) (M ω) ω h k]
    have hc2 := (condExp_congr_ae (m := 𝓕) heq2).trans hc
    filter_upwards [hc2] with ω hω
    rw [hω]
    have hmeas : AEStronglyMeasurable (f2 (D ω)) (P.map Yf) :=
      (Measurable.of_uncurry_left hf2m).aestronglyMeasurable
    rw [integral_map hYm.aemeasurable hmeas]
    refine integral_congr_ae ?_
    filter_upwards [hsumall] with ω' h
    simp only [f2, normChainPath]
    congr 1
    funext k
    simp only [normChainPath]
    rw [hΞeq (D ω) (M ω) ω' (h _) k]

/-! ## Moments of one batch (`lem:app-dyn-batch`) -/

/-- The `a`-th summand `X_a` (`cr-2026-10-23`), `X_a = B⁻¹ d_a Σ_out^{1/2}(z_a ⊗ w_a) Σ_in^{1/2}` of the batch gradient, with
`d_a = z_aᵀ A_E w_a` and `A_E = Σ_out^{1/2} E Σ_in^{1/2}` (`lem:app-dyn-batch`, ll. 537–550). In
physical features `d_a = resid E (phys C (z_a, w_a))`, so `Σ_a X_a = batchGrad E (physBatch C z ω)`. -/
def batchSummand {Ω : Type*} (C : Covariances m n) (E : Mat m n) (z : Fin B → Ω → Vec m × Vec n)
    (a : Fin B) (ω : Ω) : Mat m n :=
  ((B : ℝ)⁻¹ * resid E (phys C (z a ω))) • outer (phys C (z a ω)).1 (phys C (z a ω)).2

private theorem pd_batchSummand_rank_le_one {Ω : Type*} (C : Covariances m n)
    (E : Mat m n) (z : Fin B → Ω → Vec m × Vec n) (a : Fin B) (ω : Ω) :
    (batchSummand C E z a ω).rank ≤ 1 := by
  rw [batchSummand]
  have houter :
      ((B : ℝ)⁻¹ * resid E (phys C (z a ω))) •
          outer (phys C (z a ω)).1 (phys C (z a ω)).2 =
        outer (((B : ℝ)⁻¹ * resid E (phys C (z a ω))) • (phys C (z a ω)).1)
          (phys C (z a ω)).2 := by
    ext i j
    simp only [outer, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [houter]
  exact Matrix.rank_vecMulVec_le _ _

private theorem pd_batchSummand_nuc {Ω : Type*} (C : Covariances m n)
    (E : Mat m n) (z : Fin B → Ω → Vec m × Vec n) (a : Fin B) (ω : Ω) :
    nuc (batchSummand C E z a ω) =
      |(B : ℝ)⁻¹ * resid E (phys C (z a ω))| *
        eucNorm (phys C (z a ω)).1 * eucNorm (phys C (z a ω)).2 := by
  rw [batchSummand, nuc_smul, nuc_outer]
  unfold eucNorm
  ring

private theorem pd_eucNorm_smul {k : ℕ} (c : ℝ) (v : Vec k) :
    eucNorm (c • v) = |c| * eucNorm v := by
  unfold eucNorm
  have : ∑ i, (c • v) i ^ 2 = c ^ 2 * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_pow]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

private theorem pd_batchSummand_nuc_normalized {Ω : Type*} (C : Covariances m n)
    (E : Mat m n) (z : Fin B → Ω → Vec m × Vec n) (a : Fin B) (ω : Ω)
    (hB : 0 < B) (hA : Arot C E ≠ 0) :
    nuc (batchSummand C E z a ω) =
      fro (Arot C E) *
        (|resid ((fro (Arot C E))⁻¹ • Arot C E) (z a ω)| *
          eucNorm (Muon.DetEquiv.momU C B (z a ω)) *
          eucNorm (Muon.DetEquiv.momV C B (z a ω))) := by
  rw [pd_batchSummand_nuc, eqn_app_setup_whitened_resid]
  have hf : 0 < fro (Arot C E) := pd_fro_pos hA
  have hB' : 0 < (B : ℝ) := by exact_mod_cast hB
  have hres : resid ((fro (Arot C E))⁻¹ • Arot C E) (z a ω) =
      (fro (Arot C E))⁻¹ *
        dotProduct (z a ω).1 (Matrix.mulVec (Arot C E) (z a ω).2) := by
    unfold resid
    rw [Matrix.smul_mulVec, dotProduct_smul]
    rfl
  rw [hres]
  unfold Muon.DetEquiv.momU Muon.DetEquiv.momV phys
  rw [pd_eucNorm_smul, pd_eucNorm_smul]
  simp only [Prod.fst, Prod.snd, abs_mul, abs_inv]
  rw [abs_of_pos hB', abs_of_pos hf, abs_of_nonneg (Real.sqrt_nonneg _)]
  field_simp [ne_of_gt hf, ne_of_gt (Real.sqrt_pos.2 hB')]
  rw [Real.sq_sqrt hB'.le]
  ring

private theorem pd_batchSummand_nuc_eLpNorm {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (C : Covariances m n) (γstar CSig : ℝ)
    (hB : 0 < B) (hS : SizeFin C B γstar CSig)
    (z : Fin B → Ω → Vec m × Vec n)
    (hz : IIDBatch P ((Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)) z) (E : Mat m n) (a : Fin B) :
    eLpNorm (fun ω => nuc (batchSummand C E z a ω)) 2 P ≤
      ENNReal.ofReal (7 * CSig * γstar * fro (Arot C E)) := by
  by_cases hA : Arot C E = 0
  · have hzero : ∀ ω, batchSummand C E z a ω = 0 := by
      intro ω
      rw [batchSummand, eqn_app_setup_whitened_resid, hA]
      simp [resid]
    simp_rw [hzero]
    rw [hA]
    have hnuc : nuc (0 : Mat m n) = 0 := by
      simpa using nuc_smul (0 : ℝ) (0 : Mat m n)
    simp [hnuc, fro]
  · have hf : 0 < fro (Arot C E) := pd_fro_pos hA
    let Ah : Mat m n := (fro (Arot C E))⁻¹ • Arot C E
    have hAh : fro Ah = 1 := by
      have hs : fro Ah ^ 2 = 1 := by
        change fro ((fro (Arot C E))⁻¹ • Arot C E) ^ 2 = 1
        rw [pd_fro_sq_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hf.ne')]
      have hn : 0 ≤ fro Ah := Real.sqrt_nonneg _
      nlinarith
    have hdim : (m : ℝ) ≤ γstar * (B : ℝ) ∧ (n : ℝ) ≤ γstar * (B : ℝ) := by
      constructor
      · exact le_trans (by exact_mod_cast (Nat.le_max_left m n : m ≤ max m n)) hS.1
      · exact le_trans (by exact_mod_cast (Nat.le_max_right m n : n ≤ max m n)) hS.1
    have hγ : 0 ≤ γstar := by
      have hmpos : 0 < m := by
        by_contra hm
        have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        subst m
        exact hA (Subsingleton.elim _ _)
      have hB' : 0 < (B : ℝ) := by exact_mod_cast hB
      have hprod : 0 < γstar * (B : ℝ) := lt_of_lt_of_le (by exact_mod_cast hmpos) hdim.1
      nlinarith
    have hmom := Muon.DetEquiv.lem_app_de_moments_iii C B γstar CSig hdim hγ hS.2 Ah hAh
    let q : Vec m × Vec n → ℝ := fun x =>
      |resid Ah x| * eucNorm (Muon.DetEquiv.momU C B x) *
        eucNorm (Muon.DetEquiv.momV C B x)
    have hqm : Measurable q := by
      unfold q resid eucNorm Muon.DetEquiv.momU Muon.DetEquiv.momV
      fun_prop
    have hmom1 : eLpNorm q 2 (Muon.Setup.gaussPair m n) ≤
        ENNReal.ofReal ((15 : ℝ) ^ ((2 : ℝ) / 3) * CSig * γstar) := by
      simpa only [q] using hmom.1
    have hmap : eLpNorm (fun ω => q (z a ω)) 2 P =
        eLpNorm q 2 (Muon.Setup.gaussPair m n) := by
      calc
        _ = eLpNorm q 2 (P.map (z a)) :=
          (eLpNorm_map_measure hqm.aestronglyMeasurable (hz.meas a)).symm
        _ = _ := by rw [hz.law a]; rfl
    have hfun : (fun ω => nuc (batchSummand C E z a ω)) =
        (fro (Arot C E)) • (fun ω => q (z a ω)) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul, q, Ah]
      exact pd_batchSummand_nuc_normalized C E z a ω hB hA
    rw [hfun, eLpNorm_const_smul, hmap]
    calc
      ‖fro (Arot C E)‖ₑ * eLpNorm q 2 (Muon.Setup.gaussPair m n) ≤
          ‖fro (Arot C E)‖ₑ * ENNReal.ofReal
            ((15 : ℝ) ^ ((2 : ℝ) / 3) * CSig * γstar) :=
        by simpa [mul_comm] using mul_le_mul_left hmom1 ‖fro (Arot C E)‖ₑ
      _ ≤ ‖fro (Arot C E)‖ₑ * ENNReal.ofReal (7 * CSig * γstar) := by
        simpa [mul_comm] using
          mul_le_mul_left (ENNReal.ofReal_le_ofReal hmom.2) ‖fro (Arot C E)‖ₑ
      _ = ENNReal.ofReal (7 * CSig * γstar * fro (Arot C E)) := by
        rw [Real.enorm_eq_ofReal_abs, abs_of_pos hf, ← ENNReal.ofReal_mul (le_of_lt hf)]
        congr 1
        ring

private noncomputable def pdGlue (m n : ℕ) :
    ((Fin m → ℝ) × (Fin n → ℝ)) ≃ᵐ (Fin (m + n) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (m + n) => ℝ) finSumFinEquiv)

private theorem pdGlue_left (p : (Fin m → ℝ) × (Fin n → ℝ)) (i : Fin m) :
    pdGlue m n p (finSumFinEquiv (Sum.inl i)) = p.1 i := by
  change (Equiv.piCongrLeft (fun _ : Fin (m + n) => ℝ) finSumFinEquiv)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)).symm p)
    (finSumFinEquiv (Sum.inl i)) = p.1 i
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

private theorem pdGlue_right (p : (Fin m → ℝ) × (Fin n → ℝ)) (j : Fin n) :
    pdGlue m n p (finSumFinEquiv (Sum.inr j)) = p.2 j := by
  change (Equiv.piCongrLeft (fun _ : Fin (m + n) => ℝ) finSumFinEquiv)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)).symm p)
    (finSumFinEquiv (Sum.inr j)) = p.2 j
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

private theorem pdGlue_measurePreserving (m n : ℕ) :
    MeasurePreserving (pdGlue m n) (Muon.Setup.gaussPair m n)
      (Muon.Foundations.stdGaussianPi (m + n)) := by
  have h1 := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin m ⊕ Fin n => gaussianReal 0 1)
  have h2 := measurePreserving_piCongrLeft (α := fun _ : Fin (m + n) => ℝ)
    (fun _ => gaussianReal 0 1) finSumFinEquiv
  exact h1.trans h2

private noncomputable def pdResidPoly (A : Mat m n) : MvPolynomial (Fin (m + n)) ℝ :=
  ∑ i, ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X (finSumFinEquiv (Sum.inl i)) *
    MvPolynomial.X (finSumFinEquiv (Sum.inr j))

private theorem pdResidPoly_eval (A : Mat m n) (p : Vec m × Vec n) :
    MvPolynomial.eval (pdGlue m n p) (pdResidPoly A) = resid A p := by
  simp only [pdResidPoly, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    pdGlue_left, pdGlue_right, resid, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem pdResidPoly_ne_zero (A : Mat m n) (hA : A ≠ 0) : pdResidPoly A ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hA
  obtain ⟨j, hij⟩ := Function.ne_iff.mp hi
  intro hp
  have he := pdResidPoly_eval A (Pi.single i 1, Pi.single j 1)
  rw [hp] at he
  have hr : resid A (Pi.single i 1, Pi.single j 1) = A i j := by
    unfold resid
    rw [single_dotProduct]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hr] at he
  exact hij he.symm

private theorem pd_gaussPair_resid_ne_zero (A : Mat m n) (hA : A ≠ 0) :
    ∀ᵐ x ∂(Muon.Setup.gaussPair m n), resid A x ≠ 0 := by
  let s : Set (Fin (m + n) → ℝ) := {x | MvPolynomial.eval x (pdResidPoly A) = 0}
  have hs : MeasurableSet s :=
    (isClosed_eq (MvPolynomial.continuous_eval _) continuous_const).measurableSet
  have hnull := (Muon.Foundations.poly_zero_set_null (m + n) (pdResidPoly A)
    (pdResidPoly_ne_zero A hA)).2.2
  have hpre : {x : Vec m × Vec n | resid A x = 0} = pdGlue m n ⁻¹' s := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, s, pdResidPoly_eval]
  rw [MeasureTheory.ae_iff]
  simp only [not_ne_iff]
  rw [hpre, (pdGlue_measurePreserving m n).measure_preimage hs.nullMeasurableSet]
  exact hnull

private theorem pd_rank_eq_one_of_le_one {K : Mat m n} (hle : K.rank ≤ 1) (hK : K ≠ 0) :
    K.rank = 1 := by
  apply le_antisymm hle
  rw [Nat.one_le_iff_ne_zero]
  intro hr
  have hsub : Subsingleton (LinearMap.range K.mulVecLin) :=
    Module.finrank_zero_iff.mp hr
  apply hK
  ext i j
  have hv : K.mulVec (Pi.single j 1) = 0 := by
    have heq : (⟨K.mulVec (Pi.single j 1), LinearMap.mem_range_self K.mulVecLin
        (Pi.single j 1)⟩ : LinearMap.range K.mulVecLin) = 0 := Subsingleton.elim _ _
    exact Subtype.ext_iff.mp heq
  have hij := congrFun hv i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hij

private theorem pd_batchSummand_rank_eq_one_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (C : Covariances m n) (hB : 0 < B)
    (z : Fin B → Ω → Vec m × Vec n)
    (hz : IIDBatch P (Muon.Setup.gaussPair m n) z) (E : Mat m n) (a : Fin B)
    (hA : Arot C E ≠ 0) : ∀ᵐ ω ∂P, (batchSummand C E z a ω).rank = 1 := by
  have hcan := pd_gaussPair_resid_ne_zero (Arot C E) hA
  have hres : ∀ᵐ ω ∂P, resid (Arot C E) (z a ω) ≠ 0 := by
    rw [MeasureTheory.ae_iff] at hcan ⊢
    simp only [not_ne_iff] at hcan ⊢
    have hm : MeasurableSet {x : Vec m × Vec n | resid (Arot C E) x = 0} := by
      change MeasurableSet ((fun x : Vec m × Vec n => resid (Arot C E) x) ⁻¹' {0})
      exact (by unfold resid dotProduct Matrix.mulVec; fun_prop :
        Measurable fun x : Vec m × Vec n => resid (Arot C E) x) (measurableSet_singleton 0)
    rw [← hz.law a] at hcan
    rwa [Measure.map_apply_of_aemeasurable (hz.meas a) hm] at hcan
  filter_upwards [hres] with ω hω
  apply pd_rank_eq_one_of_le_one (pd_batchSummand_rank_le_one C E z a ω)
  have hphys : resid E (phys C (z a ω)) ≠ 0 := by
    rw [eqn_app_setup_whitened_resid]
    simpa only [resid] using hω
  have hscalar : (B : ℝ)⁻¹ * resid E (phys C (z a ω)) ≠ 0 := by
    exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hB.ne')) hphys
  have hout : (phys C (z a ω)).1 ≠ 0 := by
    intro ho
    apply hphys
    simp [resid, ho]
  have hin : (phys C (z a ω)).2 ≠ 0 := by
    intro hi
    apply hphys
    simp [resid, hi]
  rw [batchSummand]
  intro heq
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hout
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hin
  have hij := congrFun (congrFun heq i) j
  simp only [Matrix.smul_apply, outer, Matrix.vecMulVec_apply, smul_eq_mul,
    Pi.zero_apply] at hij
  exact (mul_ne_zero (mul_ne_zero hscalar hi) hj) (by simpa [mul_assoc] using hij)

/-- `lem:app-dyn-batch` (cr-2026-10-23), part (i): for a deterministic `E` and one batch `z` of i.i.d.
standard Gaussian pairs, `E‖G°[E]‖_F² ≤ C_M B ‖A_E‖_F²`. The standing `SizeFin` is `hS` (its `C_Σ`
and `γ⋆` are those of `C_M`). Statement verbatim from `section.tex` (ll. 537–550):
```latex
\begin{lemma}[Moments of one batch]\label{lem:app-dyn-batch}
Let $E\in\R^{\Nout\times\Nin}$ be deterministic, put $A_E\defeq\Sigmaout^{1/2}E\Sigmain^{1/2}$
and $d_a\defeq z_a^\T A_Ew_a$ for the samples of one batch, and let
$G^\circ[E]$ be the gradient \cref{eqn:app-dyn-batch} of that batch.
\begin{enumerate}[label=(\roman*)]
\item $\EE\norm{G^\circ[E]}_\F^2\le C_MB\norm{A_E}_\F^2$.
\item $\big(\EE\norm{G^\circ[E]}^2\big)^{1/2}\le C\log(2B)\norm{A_E}_\F$ and
$\big\|\max_{a\le B}\abs{d_a}\big\|_6\le C\log(2B)\norm{A_E}_\F$.
\item The sample $X_a\defeq B^{-1}d_a\Sigmaout^{1/2}(z_a\tensor w_a)\Sigmain^{1/2}$ has rank
one and $(\EE\norm{X_a}_*^2)^{1/2}\le7C_\Sigma\gamma_\star\norm{A_E}_\F$.
\end{enumerate}
The same bounds hold conditionally on $\cF_t$ for a matrix $E$ determined by
the past and the batch of step $t$.
\end{lemma}
```
-/
theorem lem_app_dyn_batch_i {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Covariances m n) (γstar CSig : ℝ) (hB : 0 < B) (hS : SizeFin C B γstar CSig)
    (z : Fin B → Ω → Vec m × Vec n)
    (hz : IIDBatch P ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) z)
    (E : Mat m n) :
    Integrable (fun ω => fro (batchGrad E (physBatch C z ω)) ^ 2) P ∧
    ∫ ω, fro (batchGrad E (physBatch C z ω)) ^ 2 ∂P ≤
      cMConst CSig γstar * (B : ℝ) * fro (rOut C * E * rIn C) ^ 2 := by
  have hzero : Arot C E = 0 →
      (fun ω => batchGrad E (physBatch C z ω)) = 0 := by
    intro h
    funext ω
    change grad E (fun a => phys C (z a ω)) = 0
    rw [eqn_app_setup_whitened_grad, h]
    simp
  by_cases hA : Arot C E = 0
  · have hz0 : ∀ ω, batchGrad E (physBatch C z ω) = 0 :=
      fun ω => congrFun (hzero hA) ω
    simp_rw [hz0]
    simp [fro]
    unfold cMConst
    positivity
  · have hnormalized : ∃ F : FrozenParams m n B,
        F.C = C ∧ F.β = 0 ∧
        Arot C E = fro (Arot C E) • F.A := by
      have hp := pd_fro_pos hA
      have hn : fro ((fro (Arot C E))⁻¹ • Arot C E) = 1 := by
        have hs : fro ((fro (Arot C E))⁻¹ • Arot C E) ^ 2 = 1 := by
          rw [pd_fro_sq_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hp.ne')]
        have hnn : 0 ≤ fro ((fro (Arot C E))⁻¹ • Arot C E) := Real.sqrt_nonneg _
        nlinarith
      refine ⟨⟨C, (fro (Arot C E))⁻¹ • Arot C E, hn, 0, ⟨le_rfl, zero_lt_one⟩, hB⟩,
        rfl, rfl, ?_⟩
      simp only [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
    obtain ⟨F, hFC, hFβ, hFA⟩ := hnormalized
    have hmom : Integrable (fun ω => fro (batchGrad E (physBatch C z ω)) ^ 2) P ∧
        ∫ ω, fro (batchGrad E (physBatch C z ω)) ^ 2 ∂P ≤
          cMConst CSig γstar * (B : ℝ) * fro (rOut C * E * rIn C) ^ 2 := by
      let P0 : Measure ((ℤ × Fin B) → Vec m × Vec n) :=
        Measure.infinitePi fun _ : ℤ × Fin B =>
          (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)
      let S : FrozenSamples P0 m n B := Classical.choice (frozenSamples_nonempty m n B)
      have hsindep : iIndepFun (S.zw 0) P0 :=
        S.indep.precomp (g := fun a : Fin B => ((0 : ℤ), a))
          (fun a b h => congrArg Prod.snd h)
      have hidbatch : IdentDistrib (fun ω a => z a ω) (fun ω a => S.zw 0 a ω) P P0 := by
        refine ⟨AEMeasurable.of_eval hz.meas,
          (Measurable.of_eval (S.meas 0)).aemeasurable, ?_⟩
        rw [hz.indep.map_fun_eq_pi_map hz.meas,
          hsindep.map_fun_eq_pi_map (fun a => (S.meas 0 a).aemeasurable)]
        simp_rw [hz.law, S.law]
      have hid : IdentDistrib (fun ω => fro (batchGrad E (physBatch C z ω)) ^ 2)
          (fun ω => fro (batchGrad E (physBatch C (S.zw 0) ω)) ^ 2) P P0 :=
        hidbatch.comp (pd_fro_sq_meas.comp (pd_physgrad_cont C E).measurable)
      have hbuf : ∀ ω, frozenBuf F S (-1) ω = frozenBatchG F S 0 ω := by
        intro ω
        unfold frozenBuf
        rw [tsum_eq_single 0]
        · simp [emaW, hFβ]
        · intro j hj
          simp [emaW, hFβ, zero_pow hj]
      have hscale : ∀ ω, batchGrad E (physBatch C (S.zw 0) ω) =
          fro (Arot C E) • frozenBatchG F S 0 ω := by
        intro ω
        change grad E (fun a => phys C (S.zw 0 a ω)) = _
        rw [eqn_app_setup_whitened_grad]
        conv_lhs => rw [hFA]
        unfold frozenBatchG
        rw [hFC]
        simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mul_smul,
          ← Finset.smul_sum]
        rw [smul_comm]
      have hb := pd_frozen_moment F S γstar CSig (by simpa only [hFC] using hS) (-1)
      simp_rw [hbuf] at hb
      have hi : Integrable (fun ω => fro (batchGrad E (physBatch C (S.zw 0) ω)) ^ 2) P0 := by
        simp_rw [hscale, pd_fro_sq_smul]
        exact hb.1.const_mul _
      refine ⟨hid.integrable_iff.mpr hi, ?_⟩
      rw [hid.integral_eq]
      simp_rw [hscale, pd_fro_sq_smul]
      rw [integral_const_mul]
      simpa only [Arot, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hb.2 (sq_nonneg (fro (Arot C E)))
    exact hmom

private theorem pd_doubleFactorial_odd_le (p : ℕ) :
    Nat.doubleFactorial (2 * p - 1) ≤ (2 * p) ^ p := by
  induction p with
  | zero => simp [Nat.doubleFactorial]
  | succ p ih =>
      by_cases hp : p = 0
      · subst p
        norm_num [Nat.doubleFactorial]
      · have he : 2 * (p + 1) - 1 = (2 * p - 1) + 2 := by omega
        rw [he, Nat.doubleFactorial_add_two]
        have hfac : 2 * p - 1 + 2 ≤ 2 * (p + 1) := by omega
        have hpow : (2 * p) ^ p ≤ (2 * (p + 1)) ^ p := by
          exact Nat.pow_le_pow_left (by omega : 2 * p ≤ 2 * (p + 1)) p
        calc
          (2 * p - 1 + 2) * Nat.doubleFactorial (2 * p - 1) ≤
              (2 * (p + 1)) * (2 * (p + 1)) ^ p :=
            Nat.mul_le_mul hfac (ih.trans hpow)
          _ = (2 * (p + 1)) ^ (p + 1) := by rw [pow_succ']

private theorem pd_doubleFactorial_rpow_le (p : ℕ) (hp : 1 ≤ p) :
    (((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / p)) ≤ 2 * p := by
  have hnat := pd_doubleFactorial_odd_le p
  have hreal : ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) ≤ ((2 * p : ℕ) : ℝ) ^ p := by
    exact_mod_cast hnat
  calc
    (((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / p)) ≤
        ((((2 * p : ℕ) : ℝ) ^ p) ^ ((1 : ℝ) / p)) :=
      Real.rpow_le_rpow (by positivity) hreal (by positivity)
    _ = 2 * p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      have hp0 : (p : ℝ) ≠ 0 := by positivity
      have he : (p : ℝ) * (1 / (p : ℝ)) = 1 := by field_simp
      rw [he, Real.rpow_one]
      norm_num

private theorem pd_resid_max_high_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hB : 0 < B)
    (z : Fin B → Ω → Vec m × Vec n)
    (hz : IIDBatch P (Muon.Setup.gaussPair m n) z) (A : Mat m n) (hA : fro A = 1)
    (p : ℕ) (hp : 1 ≤ p) :
    eLpNorm (fun ω => Finset.univ.sup'
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
        (fun a => |resid A (z a ω)|)) ((2 * p : ℕ) : ℝ≥0∞) P ≤
      (B : ℝ≥0∞) ^ (1 / (2 * p : ℝ)) * ENNReal.ofReal (2 * p) := by
  let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
  let M : Ω → ℝ := fun ω => Finset.univ.sup' hne (fun a => |resid A (z a ω)|)
  have hZm : AEMeasurable (fun ω a => z a ω) P := AEMeasurable.of_eval hz.meas
  have hM : AEMeasurable M P := by
    let g : (Fin B → Vec m × Vec n) → ℝ := fun x =>
      Finset.univ.sup' hne (fun a => |resid A (x a)|)
    have hg : Measurable g := by
      dsimp [g, resid, dotProduct, Matrix.mulVec]
      fun_prop
    exact hg.comp_aemeasurable hZm
  have hq : (2 * p : ℕ) ≠ 0 := by omega
  have hpow : eLpNorm M ((2 * p : ℕ) : ℝ≥0∞) P ^ ((2 * p : ℕ) : ℝ) =
      ∫⁻ x, ‖M x‖ₑ ^ ((2 * p : ℕ) : ℝ) ∂P := by
    simpa using eLpNorm_nnreal_pow_eq_lintegral (μ := P)
      (p := ((2 * p : ℕ) : NNReal)) (f := M) (by exact_mod_cast hq)
        hM.aestronglyMeasurable
  have hpoint : ∀ ω, ‖M ω‖ₑ ^ ((2 * p : ℕ) : ℝ) ≤
      ∑ a : Fin B, ‖resid A (z a ω)‖ₑ ^ ((2 * p : ℕ) : ℝ) := by
    intro ω
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' hne (fun b => |resid A (z b ω)|)
    have hnonneg : 0 ≤ M ω := by rw [show M ω = |resid A (z a ω)| by exact ha]; positivity
    simp only [ENNReal.rpow_natCast]
    have hle : ‖M ω‖ₑ ^ (2 * p) ≤ ‖resid A (z a ω)‖ₑ ^ (2 * p) := by
      rw [show M ω = |resid A (z a ω)| by exact ha]
      simp [Real.enorm_eq_ofReal_abs]
    exact hle.trans (Finset.single_le_sum
      (f := fun b : Fin B => ‖resid A (z b ω)‖ₑ ^ (2 * p))
      (fun _ _ => by positivity) (Finset.mem_univ a))
  have hlin : ∫⁻ ω, ‖M ω‖ₑ ^ ((2 * p : ℕ) : ℝ) ∂P ≤
      (B : ℝ≥0∞) * ENNReal.ofReal (2 * p) ^ ((2 * p : ℕ) : ℝ) := by
    calc
      _ ≤ ∫⁻ ω, ∑ a : Fin B, ‖resid A (z a ω)‖ₑ ^ ((2 * p : ℕ) : ℝ) ∂P :=
        lintegral_mono hpoint
      _ = ∑ a : Fin B, ∫⁻ ω, ‖resid A (z a ω)‖ₑ ^ ((2 * p : ℕ) : ℝ) ∂P := by
        rw [lintegral_finsetSum']
        intro a _
        exact ((by unfold resid dotProduct Matrix.mulVec; fun_prop : Measurable
          fun x : Vec m × Vec n => resid A x).comp_aemeasurable (hz.meas a)).enorm.pow_const _
      _ ≤ ∑ _a : Fin B, ENNReal.ofReal (2 * p) ^ ((2 * p : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        have hra : AEStronglyMeasurable (fun ω => resid A (z a ω)) P :=
          ((by unfold resid dotProduct Matrix.mulVec; fun_prop : Measurable
            fun x : Vec m × Vec n => resid A x).comp_aemeasurable (hz.meas a)).aestronglyMeasurable
        have hmap : eLpNorm (fun ω => resid A (z a ω)) ((2 * p : ℕ) : ℝ≥0∞) P =
            eLpNorm (fun x => resid A x) ((2 * p : ℕ) : ℝ≥0∞) (Muon.Setup.gaussPair m n) := by
          calc
            _ = eLpNorm (fun x => resid A x) ((2 * p : ℕ) : ℝ≥0∞) (P.map (z a)) :=
              (eLpNorm_map_measure
                (by unfold resid dotProduct Matrix.mulVec; fun_prop)
                  (hz.meas a)).symm
            _ = _ := by rw [hz.law a]
        have hpowa : eLpNorm (fun ω => resid A (z a ω)) ((2 * p : ℕ) : ℝ≥0∞) P ^
            ((2 * p : ℕ) : ℝ) =
            ∫⁻ ω, ‖resid A (z a ω)‖ₑ ^ ((2 * p : ℕ) : ℝ) ∂P := by
          simpa using eLpNorm_nnreal_pow_eq_lintegral (μ := P)
            (p := ((2 * p : ℕ) : NNReal)) (f := fun ω => resid A (z a ω))
              (by exact_mod_cast hq) hra
        rw [← hpowa, hmap]
        apply ENNReal.rpow_le_rpow
        · exact (Muon.DetEquiv.lem_app_de_moments_ii A hA p hp).trans
            (ENNReal.ofReal_le_ofReal (pd_doubleFactorial_rpow_le p hp))
        · positivity
      _ = _ := by simp [ENNReal.rpow_natCast]
  rw [← hpow] at hlin
  have hr := ENNReal.rpow_le_rpow hlin (by positivity : 0 ≤ (1 / (2 * p : ℝ)))
  have hecast : ((2 * p : ℕ) : ℝ) = 2 * (p : ℝ) := by norm_num
  rw [hecast] at hr
  rw [← ENNReal.rpow_mul, show (2 * (p : ℝ)) * (1 / (2 * p : ℝ)) = 1 by
      field_simp [show (2 * p : ℝ) ≠ 0 by positivity], ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    show (2 * (p : ℝ)) * (1 / (2 * p : ℝ)) = 1 by
      field_simp [show (2 * p : ℝ) ≠ 0 by positivity], ENNReal.rpow_one] at hr
  simpa only [M, hne] using hr

private theorem pd_resid_max_normalized {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hB : 0 < B)
    (z : Fin B → Ω → Vec m × Vec n)
    (hz : IIDBatch P (Muon.Setup.gaussPair m n) z) (A : Mat m n) (hA : fro A = 1) :
    eLpNorm (fun ω => Finset.univ.sup'
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
        (fun a => |resid A (z a ω)|)) 6 P ≤
      ENNReal.ofReal (54 * Real.log (2 * (B : ℝ))) := by
  let L : ℝ := Real.log (2 * (B : ℝ))
  let c : ℕ := ⌈L⌉₊
  let p : ℕ := 3 * c
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hLlog2 : Real.log 2 ≤ L := by
    dsimp only [L]
    apply Real.log_le_log (x := (2 : ℝ)) (y := 2 * (B : ℝ)) (by norm_num)
    nlinarith
  have hLhalf : (1 : ℝ) / 2 ≤ L :=
    le_trans (by linarith [Real.log_two_gt_d9]) hLlog2
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLhalf
  have hcpos : 1 ≤ c := by
    rw [Nat.one_le_ceil_iff]
    exact hLpos
  have hppos : 1 ≤ p := by dsimp only [p]; omega
  have hLle : L ≤ (c : ℝ) := by exact Nat.le_ceil L
  have hc_lt : (c : ℝ) < L + 1 := Nat.ceil_lt_add_one hLpos.le
  have hc_le : (c : ℝ) ≤ 3 * L := by nlinarith
  have hp_le : (p : ℝ) ≤ 9 * L := by
    dsimp only [p]
    norm_num
    nlinarith
  have hlogB : Real.log (B : ℝ) ≤ L := by
    dsimp only [L]
    apply Real.log_le_log hBr
    nlinarith
  have hfac_real : (B : ℝ) ^ (1 / (2 * p : ℝ)) ≤ 3 := by
    rw [Real.rpow_def_of_pos hBr]
    calc
      Real.exp (Real.log (B : ℝ) * (1 / (2 * (p : ℝ)))) ≤ Real.exp 1 := by
        apply Real.exp_le_exp.mpr
        have hpL : L ≤ (p : ℝ) := by
          dsimp only [p]
          norm_num
          nlinarith
        have hpR : 0 < (p : ℝ) := by positivity
        have hden : 0 < 2 * (p : ℝ) := by positivity
        calc
          Real.log (B : ℝ) * (1 / (2 * (p : ℝ))) =
              Real.log (B : ℝ) / (2 * (p : ℝ)) := by ring
          _ ≤ L / (2 * (p : ℝ)) := by gcongr
          _ ≤ 1 := (div_le_one hden).2 (by nlinarith)
      _ ≤ 3 := Real.exp_one_lt_three.le
  have hfac : (B : ℝ≥0∞) ^ (1 / (2 * p : ℝ)) ≤ ENNReal.ofReal 3 := by
    rw [show (B : ℝ≥0∞) = ENNReal.ofReal (B : ℝ) by simp [hBr.le],
      ENNReal.ofReal_rpow_of_pos hBr]
    exact ENNReal.ofReal_le_ofReal hfac_real
  have hhigh := pd_resid_max_high_moment hB z hz A hA p hppos
  have hM : AEStronglyMeasurable (fun ω => Finset.univ.sup'
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
      (fun a => |resid A (z a ω)|)) P := by
    have hZm : AEMeasurable (fun ω a => z a ω) P := AEMeasurable.of_eval hz.meas
    apply Measurable.comp_aemeasurable (g := fun x : Fin B → Vec m × Vec n =>
      Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
        (fun a => |resid A (x a)|)) ?_ hZm |>.aestronglyMeasurable
    dsimp [resid, dotProduct, Matrix.mulVec]
    fun_prop
  have h6high : eLpNorm (fun ω => Finset.univ.sup'
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
        (fun a => |resid A (z a ω)|)) 6 P ≤
      eLpNorm (fun ω => Finset.univ.sup'
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
        (fun a => |resid A (z a ω)|)) ((2 * p : ℕ) : ℝ≥0∞) P := by
    apply eLpNorm_le_eLpNorm_of_exponent_le
    norm_num
    have : 6 ≤ 2 * p := by dsimp only [p]; omega
    exact_mod_cast this
  calc
    _ ≤ _ := h6high
    _ ≤ (B : ℝ≥0∞) ^ (1 / (2 * p : ℝ)) * ENNReal.ofReal (2 * p) := hhigh
    _ ≤ ENNReal.ofReal 3 * ENNReal.ofReal (2 * p) :=
      mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = ENNReal.ofReal (6 * (p : ℝ)) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      norm_num
      ring
    _ ≤ ENNReal.ofReal (54 * L) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith
    _ = _ := by rfl

private theorem pd_resid_max {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hB : 0 < B)
    (z : Fin B → Ω → Vec m × Vec n)
    (hz : IIDBatch P (Muon.Setup.gaussPair m n) z) (A : Mat m n) :
    eLpNorm (fun ω => Finset.univ.sup'
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
        (fun a => |resid A (z a ω)|)) 6 P ≤
      ENNReal.ofReal (54 * Real.log (2 * (B : ℝ)) * fro A) := by
  by_cases hAz : A = 0
  · subst A
    simp [resid, fro]
  · have hf : 0 < fro A := pd_fro_pos hAz
    let Ah : Mat m n := (fro A)⁻¹ • A
    have hAh : fro Ah = 1 := by
      have hs : fro Ah ^ 2 = 1 := by
        change fro ((fro A)⁻¹ • A) ^ 2 = 1
        rw [pd_fro_sq_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hf.ne')]
      have hn : 0 ≤ fro Ah := Real.sqrt_nonneg _
      nlinarith
    have hfun : (fun ω => Finset.univ.sup'
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
        (fun a => |resid A (z a ω)|)) =
        (fro A) • (fun ω => Finset.univ.sup'
          (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
          (fun a => |resid Ah (z a ω)|)) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.apply_sup'_eq_sup'_comp
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩) (fun x : ℝ => fro A * x)
        (fun x y => mul_max_of_nonneg x y hf.le)]
      apply Finset.sup'_congr
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩) rfl
      intro a _
      have hr : resid Ah (z a ω) = (fro A)⁻¹ * resid A (z a ω) := by
        dsimp only [Ah]
        unfold resid
        rw [Matrix.smul_mulVec, dotProduct_smul]
        rfl
      change |resid A (z a ω)| = fro A * |resid Ah (z a ω)|
      rw [hr, abs_mul, abs_inv, abs_of_pos hf]
      field_simp [hf.ne']
    rw [hfun, eLpNorm_const_smul]
    have hn := pd_resid_max_normalized hB z hz Ah hAh
    calc
      ‖fro A‖ₑ * eLpNorm (fun ω => Finset.univ.sup'
          (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
          (fun a => |resid Ah (z a ω)|)) 6 P ≤
          ‖fro A‖ₑ * ENNReal.ofReal (54 * Real.log (2 * (B : ℝ))) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = ENNReal.ofReal (54 * Real.log (2 * (B : ℝ)) * fro A) := by
        rw [Real.enorm_eq_ofReal_abs, abs_of_pos hf,
          ← ENNReal.ofReal_mul (le_of_lt hf)]
        congr 1
        ring

private lemma pd_canonical_iid_matrix {m n B k : ℕ}
    (pick : Vec m × Vec n → Vec k) (hmeas : Measurable pick)
    (hpick : ((Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)).map pick = Muon.Foundations.stdGaussianPi k) :
    Muon.External.IsIIDGaussianMatrix
      (Measure.pi (fun _ : Fin B =>
        (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)))
      (fun (z : Fin B → Vec m × Vec n) (i : Fin k) (a : Fin B) => pick (z a) i) := by
  have hF : Measurable (fun (z : Fin B → Vec m × Vec n) (ij : Fin k × Fin B) =>
      pick (z ij.2) ij.1) := by
    refine measurable_pi_iff.mpr (fun ij => ?_)
    exact (measurable_pi_apply ij.1).comp (hmeas.comp (measurable_pi_apply ij.2))
  unfold Muon.External.IsIIDGaussianMatrix
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply hF (MeasurableSet.univ_pi hs)]
  have hpre : (fun (z : Fin B → Vec m × Vec n) (ij : Fin k × Fin B) =>
      pick (z ij.2) ij.1) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun a : Fin B => pick ⁻¹' (Set.univ.pi fun i => s (i, a))) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h a i
      exact h (i, a)
    · intro h ij
      exact h ij.2 ij.1
  rw [hpre, Measure.pi_pi]
  have hslot (a : Fin B) :
      ((Muon.Foundations.stdGaussianPi m).prod
        (Muon.Foundations.stdGaussianPi n))
          (pick ⁻¹' (Set.univ.pi fun i => s (i, a))) =
        ∏ i, gaussianReal 0 1 (s (i, a)) := by
    rw [← Measure.map_apply hmeas (MeasurableSet.univ_pi fun i => hs (i, a)), hpick]
    unfold Muon.Foundations.stdGaussianPi
    rw [Measure.pi_pi]
  rw [Finset.prod_congr rfl (fun a _ => hslot a), Fintype.prod_prod_type,
    Finset.prod_comm]

private lemma pd_iid_matrix_left {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (z : Fin B → Ω → Vec m × Vec n)
    (hz : IIDBatch P (Muon.Setup.gaussPair m n) z) :
    Muon.External.IsIIDGaussianMatrix P
      (fun (ω : Ω) (i : Fin m) (a : Fin B) => (z a ω).1 i) := by
  let Y : Ω → (Fin B → Vec m × Vec n) := fun ω a => z a ω
  let F : (Fin B → Vec m × Vec n) → (Fin m × Fin B → ℝ) :=
    fun y ia => (y ia.2).1 ia.1
  have hY : AEMeasurable Y P := AEMeasurable.of_eval hz.meas
  have hF : Measurable F := by dsimp [F]; fun_prop
  unfold Muon.External.IsIIDGaussianMatrix
  change P.map (F ∘ Y) = _
  rw [← hF.aemeasurable.map_map_of_aemeasurable hY,
    hz.indep.map_fun_eq_pi_map hz.meas]
  simp_rw [hz.law]
  exact pd_canonical_iid_matrix (fun x : Vec m × Vec n => x.1) measurable_fst
    (by rw [Measure.map_fst_prod, measure_univ, one_smul])

private lemma pd_iid_matrix_right {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (z : Fin B → Ω → Vec m × Vec n)
    (hz : IIDBatch P (Muon.Setup.gaussPair m n) z) :
    Muon.External.IsIIDGaussianMatrix P
      (fun (ω : Ω) (j : Fin n) (a : Fin B) => (z a ω).2 j) := by
  let Y : Ω → (Fin B → Vec m × Vec n) := fun ω a => z a ω
  let F : (Fin B → Vec m × Vec n) → (Fin n × Fin B → ℝ) :=
    fun y ja => (y ja.2).2 ja.1
  have hY : AEMeasurable Y P := AEMeasurable.of_eval hz.meas
  have hF : Measurable F := by dsimp [F]; fun_prop
  unfold Muon.External.IsIIDGaussianMatrix
  change P.map (F ∘ Y) = _
  rw [← hF.aemeasurable.map_map_of_aemeasurable hY,
    hz.indep.map_fun_eq_pi_map hz.meas]
  simp_rw [hz.law]
  exact pd_canonical_iid_matrix (fun x : Vec m × Vec n => x.2) measurable_snd
    (by rw [Measure.map_snd_prod, measure_univ, one_smul])

private lemma pd_opNorm_mul {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B

private lemma pd_opNorm_transpose {a b : ℕ} (A : Mat a b) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma pd_opNorm_nonneg {a b : ℕ} (A : Mat a b) : 0 ≤ opNorm A := by
  unfold opNorm
  positivity

private lemma pd_opNorm_continuous {a b : ℕ} :
    Continuous (fun A : Mat a b => opNorm A) := by
  open scoped Matrix.Norms.L2Operator in
  have h : (fun A : Mat a b => opNorm A) = fun A => ‖A‖ := funext opNorm_eq_norm
  rw [h]
  exact continuous_norm

private lemma pd_opNorm_smul {a b : ℕ} (c : ℝ) (A : Mat a b) :
    opNorm (c • A) = |c| * opNorm A := by
  open scoped Matrix.Norms.L2Operator in
    rw [opNorm_eq_norm, opNorm_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma pd_opNorm_diag_le {a : ℕ} (d : Fin a → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hd : ∀ i, |d i| ≤ R) :
    opNorm (Matrix.diagonal d) ≤ R := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hR).2 fun i => by
    simpa [Real.norm_eq_abs] using hd i

private lemma pd_opNorm_rOut_sq {m n : ℕ} (C : Covariances m n) :
    opNorm (rOut C) * opNorm (rOut C) = opNorm C.Sout := by
  have hh : (rOut C)ᴴ = rOut C :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sout)).isHermitian
  have hsq : rOut C * rOut C = C.Sout :=
    CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (rOut C)
  rw [hh, hsq] at h
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact h.symm

private lemma pd_opNorm_rIn_sq {m n : ℕ} (C : Covariances m n) :
    opNorm (rIn C) * opNorm (rIn C) = opNorm C.Sin := by
  have hh : (rIn C)ᴴ = rIn C :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  have hsq : rIn C * rIn C = C.Sin :=
    CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (rIn C)
  rw [hh, hsq] at h
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact h.symm

private lemma pd_sum_outer_eq {m n B : ℕ} (rO : Mat m m) (rI : Mat n n)
    (c : Fin B → ℝ) (Z : Mat m B) (W : Mat n B)
    (z : Fin B → Vec m) (w : Fin B → Vec n)
    (hz : ∀ i a, Z i a = z a i) (hw : ∀ j a, W j a = w a j) :
    ∑ a, c a • (rO * outer (z a) (w a) * rI) =
      rO * (Z * Matrix.diagonal c * Wᵀ) * rI := by
  have hsum : ∑ a, c a • outer (z a) (w a) = Z * Matrix.diagonal c * Wᵀ := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, outer, Matrix.vecMulVec_apply,
      Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul, hz, hw,
      Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [← hsum, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

private lemma pd_batchGrad_factor {m n B : ℕ} (C : Covariances m n)
    (E : Mat m n) (z : Fin B → Vec m × Vec n) :
    batchGrad E (fun a => phys C (z a)) = ((B : ℝ))⁻¹ •
      (rOut C *
        ((Matrix.of fun i a => (z a).1 i : Mat m B) *
          Matrix.diagonal (fun a => resid (Arot C E) (z a)) *
          (Matrix.of fun j a => (z a).2 j : Mat n B)ᵀ) * rIn C) := by
  show Muon.Setup.grad E (fun a => phys C (z a)) = _
  rw [eqn_app_setup_whitened_grad]
  congr 1
  exact pd_sum_outer_eq (rOut C) (rIn C)
    (fun a => resid (Arot C E) (z a))
    (fun i a => (z a).1 i) (fun j a => (z a).2 j)
    (fun a => (z a).1) (fun a => (z a).2) (fun _ _ => rfl) (fun _ _ => rfl)

private lemma pd_eLpNorm_triple_mul_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f g h : Ω → ℝ)
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P)
    (hh : AEStronglyMeasurable h P) :
    eLpNorm (fun x => f x * g x * h x) 2 P ≤
      eLpNorm f 6 P * eLpNorm g 6 P * eLpNorm h 6 P := by
  letI : ENNReal.HolderTriple (6 : ℝ≥0∞) 6 3 :=
    ENNReal.HolderTriple.of_toReal (by
      simp only [ENNReal.toReal_ofNat]
      constructor <;> norm_num)
  letI : ENNReal.HolderTriple (3 : ℝ≥0∞) 6 2 :=
    ENNReal.HolderTriple.of_toReal (by
      simp only [ENNReal.toReal_ofNat]
      constructor <;> norm_num)
  have hfg : AEStronglyMeasurable (fun x => f x * g x) P := hf.mul hg
  have h₁ := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
    (μ := P) (f := fun x => f x * g x) (g := h)
    (p := (3 : ℝ≥0∞)) (q := (6 : ℝ≥0∞)) (r := (2 : ℝ≥0∞))
    (fun a b : ℝ => a * b) 1 (by fun_prop) hfg hh
    (Filter.Eventually.of_forall fun x => by simp [abs_mul])
  have h₂ := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
    (μ := P) (f := f) (g := g) (p := (6 : ℝ≥0∞)) (q := (6 : ℝ≥0∞))
    (r := (3 : ℝ≥0∞))
    (fun a b : ℝ => a * b) 1 (by fun_prop) hf hg
    (Filter.Eventually.of_forall fun x => by simp [abs_mul])
  exact h₁.trans (by
    simp only [ENNReal.coe_one, one_mul]
    gcongr
    simpa using h₂)

private lemma pd_power_integral_of_eLpNorm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (p : ℕ) (hp : p ≠ 0)
    (hf : AEStronglyMeasurable f P) (hf0 : ∀ ω, 0 ≤ f ω)
    (c : ℝ) (hc : 0 ≤ c)
    (hb : eLpNorm f (p : ℝ≥0∞) P ≤ ENNReal.ofReal c) :
    Integrable (fun ω => f ω ^ p) P ∧
      (∫ ω, f ω ^ p ∂P) ^ (1 / (p : ℝ)) ≤ c := by
  have hm : MemLp f (p : ℝ≥0∞) P :=
    lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  have hi' := hm.integrable_norm_pow hp
  have hi : Integrable (fun ω => f ω ^ p) P := hi'.congr
    (Filter.Eventually.of_forall fun ω => by
      change ‖f ω‖ ^ p = f ω ^ p
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)])
  refine ⟨hi, ?_⟩
  have heq := hm.eLpNorm_eq_integral_rpow_norm
    (show (p : ℝ≥0∞) ≠ 0 by exact_mod_cast hp) (by simp)
  have heq' : eLpNorm f (p : ℝ≥0∞) P =
      ENNReal.ofReal ((∫ ω, f ω ^ p ∂P) ^ (1 / (p : ℝ))) := by
    simpa only [ENNReal.toReal_natCast, Real.norm_eq_abs,
      abs_of_nonneg (hf0 _), Real.rpow_natCast, inv_eq_one_div] using heq
  have hb' : ENNReal.ofReal ((∫ ω, f ω ^ p ∂P) ^ (1 / (p : ℝ))) ≤
      ENNReal.ofReal c := by
    rw [← heq']
    exact hb
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb'
  rw [ENNReal.toReal_ofReal hc] at hreal
  have hint0 : 0 ≤ ∫ ω, f ω ^ p ∂P := integral_nonneg fun ω => pow_nonneg (hf0 ω) p
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hint0 _)] at hreal
  exact hreal

private lemma pd_indep_mk_right {Ω β : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace β] {P : Measure Ω} (G : MeasurableSpace Ω)
    (Y : Ω → β) (hY : AEMeasurable Y P)
    (hind : Indep G (MeasurableSpace.comap Y inferInstance) P) :
    Indep G (MeasurableSpace.comap (hY.mk Y) inferInstance) P := by
  rw [Indep_iff] at hind ⊢
  intro t1 t2 h1 h2
  obtain ⟨S, hS, rfl⟩ := h2
  have hae : (hY.mk Y) ⁻¹' S =ᵐ[P] Y ⁻¹' S := by
    filter_upwards [hY.ae_eq_mk] with ω hω
    simp [Set.preimage, hω]
  have hh := hind t1 (Y ⁻¹' S) h1 ⟨S, hS, rfl⟩
  have hae_inter : t1 ∩ (hY.mk Y) ⁻¹' S =ᵐ[P] t1 ∩ Y ⁻¹' S := by
    filter_upwards [hae] with ω hω
    simp only [Set.mem_inter_iff]
    exact congrArg (fun h => ω ∈ t1 ∧ h) hω
  rw [measure_congr hae_inter, measure_congr hae]
  exact hh

private lemma pd_opNorm_le_fro {p q : ℕ} (K : Mat p q) : opNorm K ≤ fro K := by
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

/-- `lem:app-dyn-batch` (cr-2026-10-23), part (ii): a constant `K` depending only on `(C_Σ, γ⋆)`
(quantified before the dimensions, the batch and `E`) such that, for every batch of i.i.d. standard
Gaussian pairs and every deterministic `E`, `(E‖G°[E]‖²)^{1/2} ≤ K log(2B) ‖A_E‖_F` and
`‖max_{a≤B} |d_a|‖_{L⁶} ≤ K log(2B) ‖A_E‖_F`. The maximum is a `Finset.sup'` over the nonempty
`Fin B`, and `‖·‖_{L⁶}` is `eLpNorm` with exponent `6`. Statement verbatim from `section.tex` (ll. 537–550):
```latex
\begin{lemma}[Moments of one batch]\label{lem:app-dyn-batch}
Let $E\in\R^{\Nout\times\Nin}$ be deterministic, put $A_E\defeq\Sigmaout^{1/2}E\Sigmain^{1/2}$
and $d_a\defeq z_a^\T A_Ew_a$ for the samples of one batch, and let
$G^\circ[E]$ be the gradient \cref{eqn:app-dyn-batch} of that batch.
\begin{enumerate}[label=(\roman*)]
\item $\EE\norm{G^\circ[E]}_\F^2\le C_MB\norm{A_E}_\F^2$.
\item $\big(\EE\norm{G^\circ[E]}^2\big)^{1/2}\le C\log(2B)\norm{A_E}_\F$ and
$\big\|\max_{a\le B}\abs{d_a}\big\|_6\le C\log(2B)\norm{A_E}_\F$.
\item The sample $X_a\defeq B^{-1}d_a\Sigmaout^{1/2}(z_a\tensor w_a)\Sigmain^{1/2}$ has rank
one and $(\EE\norm{X_a}_*^2)^{1/2}\le7C_\Sigma\gamma_\star\norm{A_E}_\F$.
\end{enumerate}
The same bounds hold conditionally on $\cF_t$ for a matrix $E$ determined by
the past and the batch of step $t$.
\end{lemma}
```
-/
theorem lem_app_dyn_batch_ii (certOp : Muon.External.GaussianOpNormL6) (γstar CSig : ℝ) :
    ∃ K : ℝ, ∀ (m n B : ℕ) (C : Covariances m n) (hB : 0 < B),
      SizeFin C B γstar CSig → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (z : Fin B → Ω → Vec m × Vec n),
        IIDBatch P ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) z →
        ∀ E : Mat m n,
          eLpNorm (fun ω => opNorm (batchGrad E (physBatch C z ω))) 2 P ≤
              ENNReal.ofReal (K * Real.log (2 * (B : ℝ)) * fro (rOut C * E * rIn C)) ∧
          eLpNorm (fun ω => Finset.univ.sup'
              (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
              (fun a => |resid E (phys C (z a ω))|)) 6 P ≤
              ENNReal.ofReal (K * Real.log (2 * (B : ℝ)) * fro (rOut C * E * rIn C)) := by
  let C₀ : ℝ := certOp.holds.choose
  let q₀ : ℝ := (C₀ + 1) * (Real.sqrt γstar + 1)
  let K₀ : ℝ := 54 * CSig * q₀ ^ 2
  refine ⟨max 54 K₀, ?_⟩
  intro m n B C hB hS Ω _ P _ z hz E
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hγ : 0 ≤ γstar := by
    have hγB : 0 ≤ γstar * (B : ℝ) :=
      (Nat.cast_nonneg (max m n)).trans hS.1
    nlinarith
  have hCS : 0 ≤ CSig :=
    (pd_opNorm_nonneg C.Sout).trans hS.2.1
  have hC₀ : 0 < C₀ := certOp.holds.choose_spec.1
  have hq₀ : 0 ≤ q₀ := by
    dsimp [q₀]
    positivity
  let A : Mat m n := Arot C E
  let Z : Ω → Mat m B := fun ω i a => (z a ω).1 i
  let W : Ω → Mat n B := fun ω j a => (z a ω).2 j
  let R : Ω → ℝ := fun ω => Finset.univ.sup'
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
    (fun a => |resid A (z a ω)|)
  let OZ : Ω → ℝ := fun ω => opNorm (Z ω)
  let OW : Ω → ℝ := fun ω => opNorm (W ω)
  let q : ℝ := q₀ * Real.sqrt B
  let r : ℝ := 54 * Real.log (2 * (B : ℝ)) * fro A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) :=
    Real.log_nonneg (by
      have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
      nlinarith)
  have hr : 0 ≤ r := by
    dsimp [r]
    exact mul_nonneg (mul_nonneg (by norm_num) hlog) (Real.sqrt_nonneg _)
  have hm : (m : ℝ) ≤ γstar * (B : ℝ) :=
    (Nat.cast_le.mpr (Nat.le_max_left m n)).trans hS.1
  have hn : (n : ℝ) ≤ γstar * (B : ℝ) :=
    (Nat.cast_le.mpr (Nat.le_max_right m n)).trans hS.1
  have hsqrt (d : ℕ) (hd : (d : ℝ) ≤ γstar * (B : ℝ)) :
      Real.sqrt d ≤ Real.sqrt γstar * Real.sqrt B := by
    calc
      Real.sqrt d ≤ Real.sqrt (γstar * (B : ℝ)) := Real.sqrt_le_sqrt hd
      _ = _ := Real.sqrt_mul hγ _
  have hOZ : eLpNorm OZ 6 P ≤ ENNReal.ofReal q := by
    have hh := certOp.holds.choose_spec.2 m B Ω P Z (pd_iid_matrix_left z hz)
    have harg : C₀ * (Real.sqrt m + Real.sqrt B) ≤ q := by
      have hs := hsqrt m hm
      dsimp [q, q₀]
      nlinarith [mul_le_mul_of_nonneg_left
        (add_le_add_right hs (Real.sqrt B)) hC₀.le]
    exact hh.trans (ENNReal.ofReal_le_ofReal harg)
  have hOW : eLpNorm OW 6 P ≤ ENNReal.ofReal q := by
    have hh := certOp.holds.choose_spec.2 n B Ω P W (pd_iid_matrix_right z hz)
    have harg : C₀ * (Real.sqrt n + Real.sqrt B) ≤ q := by
      have hs := hsqrt n hn
      dsimp [q, q₀]
      nlinarith [mul_le_mul_of_nonneg_left
        (add_le_add_right hs (Real.sqrt B)) hC₀.le]
    exact hh.trans (ENNReal.ofReal_le_ofReal harg)
  have hR : eLpNorm R 6 P ≤ ENNReal.ofReal r := by
    dsimp only [R, r, A]
    exact pd_resid_max hB z hz (Arot C E)
  have hY : AEMeasurable (fun ω : Ω => fun a => z a ω) P :=
    AEMeasurable.of_eval hz.meas
  have hmZ : AEStronglyMeasurable Z P := by
    have h : Measurable (fun y : Fin B → Vec m × Vec n =>
        (fun i a => (y a).1 i : Mat m B)) := by fun_prop
    exact (h.aemeasurable.comp_aemeasurable hY).aestronglyMeasurable
  have hmW : AEStronglyMeasurable W P := by
    have h : Measurable (fun y : Fin B → Vec m × Vec n =>
        (fun j a => (y a).2 j : Mat n B)) := by fun_prop
    exact (h.aemeasurable.comp_aemeasurable hY).aestronglyMeasurable
  have hmOZ : AEStronglyMeasurable OZ P :=
    pd_opNorm_continuous.comp_aestronglyMeasurable hmZ
  have hmOW : AEStronglyMeasurable OW P :=
    pd_opNorm_continuous.comp_aestronglyMeasurable hmW
  have hmR : AEStronglyMeasurable R P := by
    have h : Measurable (fun y : Fin B → Vec m × Vec n => Finset.univ.sup'
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
        (fun a => |resid A (y a)|)) := by
      unfold resid Matrix.mulVec dotProduct
      fun_prop
    exact (h.aemeasurable.comp_aemeasurable hY).aestronglyMeasurable
  have hrO : opNorm (rOut C) ≤ Real.sqrt CSig := by
    have hs := pd_opNorm_rOut_sq C
    have hle := hS.2.1
    have hsCS : Real.sqrt CSig ^ 2 = CSig := Real.sq_sqrt hCS
    nlinarith [pd_opNorm_nonneg (rOut C), Real.sqrt_nonneg CSig]
  have hrI : opNorm (rIn C) ≤ Real.sqrt CSig := by
    have hs := pd_opNorm_rIn_sq C
    have hle := hS.2.2
    have hsCS : Real.sqrt CSig ^ 2 = CSig := Real.sq_sqrt hCS
    nlinarith [pd_opNorm_nonneg (rIn C), Real.sqrt_nonneg CSig]
  have hrOI : opNorm (rOut C) * opNorm (rIn C) ≤ CSig := by
    have := mul_le_mul hrO hrI (pd_opNorm_nonneg (rIn C)) (Real.sqrt_nonneg _)
    nlinarith [Real.sq_sqrt hCS]
  have hpoint (ω : Ω) :
      opNorm (batchGrad E (physBatch C z ω)) ≤
        (CSig / (B : ℝ)) * OZ ω * OW ω * R ω := by
    have hRω : 0 ≤ R ω := by
      dsimp only [R]
      exact (abs_nonneg (resid A (z ⟨0, hB⟩ ω))).trans
        (Finset.le_sup' (fun a => |resid A (z a ω)|) (Finset.mem_univ ⟨0, hB⟩))
    have hD : opNorm (Matrix.diagonal (fun a => resid A (z a ω))) ≤ R ω := by
      apply pd_opNorm_diag_le _ _ hRω
      intro a
      exact Finset.le_sup' (fun b => |resid A (z b ω)|) (Finset.mem_univ a)
    have hmid : opNorm
        (Z ω * Matrix.diagonal (fun a => resid A (z a ω)) * (W ω)ᵀ) ≤
        OZ ω * R ω * OW ω := by
      calc
        _ ≤ opNorm (Z ω * Matrix.diagonal (fun a => resid A (z a ω))) *
            opNorm (W ω)ᵀ := pd_opNorm_mul _ _
        _ ≤ (opNorm (Z ω) *
            opNorm (Matrix.diagonal (fun a => resid A (z a ω)))) * opNorm (W ω)ᵀ :=
          mul_le_mul_of_nonneg_right (pd_opNorm_mul _ _) (pd_opNorm_nonneg _)
        _ = (opNorm (Z ω) *
            opNorm (Matrix.diagonal (fun a => resid A (z a ω)))) * opNorm (W ω) := by
          rw [pd_opNorm_transpose]
        _ ≤ OZ ω * R ω * OW ω := by
          exact mul_le_mul (mul_le_mul le_rfl hD (pd_opNorm_nonneg _) (pd_opNorm_nonneg _))
            le_rfl (pd_opNorm_nonneg _) (mul_nonneg (pd_opNorm_nonneg _) hRω)
    have hout : opNorm (rOut C *
        (Z ω * Matrix.diagonal (fun a => resid A (z a ω)) * (W ω)ᵀ) * rIn C) ≤
        CSig * (OZ ω * R ω * OW ω) := by
      calc
        _ ≤ opNorm (rOut C *
              (Z ω * Matrix.diagonal (fun a => resid A (z a ω)) * (W ω)ᵀ)) *
            opNorm (rIn C) := pd_opNorm_mul _ _
        _ ≤ (opNorm (rOut C) * opNorm
              (Z ω * Matrix.diagonal (fun a => resid A (z a ω)) * (W ω)ᵀ)) *
            opNorm (rIn C) :=
          mul_le_mul_of_nonneg_right (pd_opNorm_mul _ _) (pd_opNorm_nonneg _)
        _ = (opNorm (rOut C) * opNorm (rIn C)) * opNorm
              (Z ω * Matrix.diagonal (fun a => resid A (z a ω)) * (W ω)ᵀ) := by ring
        _ ≤ _ := mul_le_mul hrOI hmid (pd_opNorm_nonneg _) hCS
    rw [show batchGrad E (physBatch C z ω) = _ from pd_batchGrad_factor C E (fun a => z a ω),
      pd_opNorm_smul, abs_inv, abs_of_pos hBr]
    dsimp only [A] at hout
    calc
      (B : ℝ)⁻¹ * opNorm (rOut C *
          (Z ω * Matrix.diagonal (fun a => resid (Arot C E) (z a ω)) * (W ω)ᵀ) * rIn C)
          ≤ (B : ℝ)⁻¹ * (CSig * (OZ ω * R ω * OW ω)) :=
        mul_le_mul_of_nonneg_left hout (by positivity)
      _ = _ := by field_simp
  have hmG : AEStronglyMeasurable
      (fun ω => opNorm (batchGrad E (physBatch C z ω))) P := by
    have h : Measurable (fun y : Fin B → Vec m × Vec n =>
        opNorm (batchGrad E (fun a => phys C (y a)))) := by
      apply pd_opNorm_continuous.measurable.comp
      unfold batchGrad Muon.Setup.grad phys resid outer Matrix.vecMulVec
        Matrix.mulVec dotProduct
      fun_prop
    exact (h.aemeasurable.comp_aemeasurable hY).aestronglyMeasurable
  have hmono : eLpNorm (fun ω => opNorm (batchGrad E (physBatch C z ω))) 2 P ≤
      eLpNorm (fun ω => (CSig / (B : ℝ)) * OZ ω * OW ω * R ω) 2 P := by
    refine eLpNorm_mono_real hmG fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (pd_opNorm_nonneg _)]
    exact hpoint ω
  have htriple := pd_eLpNorm_triple_mul_le P OZ OW R hmOZ hmOW hmR
  have hop : eLpNorm (fun ω => opNorm (batchGrad E (physBatch C z ω))) 2 P ≤
      ENNReal.ofReal (K₀ * Real.log (2 * (B : ℝ)) * fro A) := by
    have hc : 0 ≤ CSig / (B : ℝ) := div_nonneg hCS hBr.le
    have hprod : eLpNorm (fun ω => OZ ω * OW ω * R ω) 2 P ≤
        ENNReal.ofReal q * ENNReal.ofReal q * ENNReal.ofReal r :=
      htriple.trans (mul_le_mul (mul_le_mul hOZ hOW (by positivity) (by positivity))
        hR (by positivity) (by positivity))
    calc
      _ ≤ eLpNorm (fun ω => (CSig / (B : ℝ)) * OZ ω * OW ω * R ω) 2 P := hmono
      _ = ‖CSig / (B : ℝ)‖ₑ * eLpNorm (fun ω => OZ ω * OW ω * R ω) 2 P := by
        rw [show (fun ω => (CSig / (B : ℝ)) * OZ ω * OW ω * R ω) =
          (CSig / (B : ℝ)) • (fun ω => OZ ω * OW ω * R ω) by
            funext ω; simp only [Pi.smul_apply, smul_eq_mul]; ring]
        rw [eLpNorm_const_smul]
      _ ≤ ENNReal.ofReal (CSig / (B : ℝ)) *
          (ENNReal.ofReal q * ENNReal.ofReal q * ENNReal.ofReal r) := by
        rw [Real.enorm_eq_ofReal hc]
        exact mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = ENNReal.ofReal (K₀ * Real.log (2 * (B : ℝ)) * fro A) := by
        have heq : (CSig / (B : ℝ)) * q * q * r =
            K₀ * Real.log (2 * (B : ℝ)) * fro A := by
          dsimp [q, r, K₀]
          calc
            CSig / (B : ℝ) * (q₀ * Real.sqrt B) * (q₀ * Real.sqrt B) *
                (54 * Real.log (2 * (B : ℝ)) * fro A) =
              CSig / (B : ℝ) * (q₀ ^ 2 * Real.sqrt B ^ 2) *
                (54 * Real.log (2 * (B : ℝ)) * fro A) := by ring
            _ = _ := by
              rw [Real.sq_sqrt hBr.le]
              field_simp
        rw [← heq, ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hc hq) hq),
          ENNReal.ofReal_mul (mul_nonneg hc hq), ENNReal.ofReal_mul hc]
        ac_rfl
  constructor
  · exact hop.trans (ENNReal.ofReal_le_ofReal (by
      have hK : K₀ ≤ max 54 K₀ := le_max_right _ _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hlog)
        (Real.sqrt_nonneg _)))
  · have hres : eLpNorm (fun ω => Finset.univ.sup'
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
        (fun a => |resid E (phys C (z a ω))|)) 6 P ≤
        ENNReal.ofReal (54 * Real.log (2 * (B : ℝ)) * fro A) := by
      simp_rw [eqn_app_setup_whitened_resid]
      change eLpNorm (fun ω => Finset.univ.sup'
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
        (fun a => |resid A (z a ω)|)) 6 P ≤ _
      exact pd_resid_max hB z hz A
    exact hres.trans (ENNReal.ofReal_le_ofReal (by
      have hK : (54 : ℝ) ≤ max 54 K₀ := le_max_left _ _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hlog)
        (Real.sqrt_nonneg _)))

/-- `lem:app-dyn-batch` (cr-2026-10-23), part (iii): for each sample `a ≤ B` and deterministic `E`,
the summand `X_a` has rank at most one, has rank exactly one almost surely when `A_E ≠ 0`, and
`(E‖X_a‖_*²)^{1/2} ≤ 7 C_Σ γ⋆ ‖A_E‖_F` with `‖·‖_*` the nuclear norm (`Muon.nuc`). The rank-one
clause is stated as a conjunction because it fails when `A_E = 0`; see `open_questions`.
Statement verbatim from `section.tex` (ll. 537–550):
```latex
\begin{lemma}[Moments of one batch]\label{lem:app-dyn-batch}
Let $E\in\R^{\Nout\times\Nin}$ be deterministic, put $A_E\defeq\Sigmaout^{1/2}E\Sigmain^{1/2}$
and $d_a\defeq z_a^\T A_Ew_a$ for the samples of one batch, and let
$G^\circ[E]$ be the gradient \cref{eqn:app-dyn-batch} of that batch.
\begin{enumerate}[label=(\roman*)]
\item $\EE\norm{G^\circ[E]}_\F^2\le C_MB\norm{A_E}_\F^2$.
\item $\big(\EE\norm{G^\circ[E]}^2\big)^{1/2}\le C\log(2B)\norm{A_E}_\F$ and
$\big\|\max_{a\le B}\abs{d_a}\big\|_6\le C\log(2B)\norm{A_E}_\F$.
\item The sample $X_a\defeq B^{-1}d_a\Sigmaout^{1/2}(z_a\tensor w_a)\Sigmain^{1/2}$ has rank
one and $(\EE\norm{X_a}_*^2)^{1/2}\le7C_\Sigma\gamma_\star\norm{A_E}_\F$.
\end{enumerate}
The same bounds hold conditionally on $\cF_t$ for a matrix $E$ determined by
the past and the batch of step $t$.
\end{lemma}
```
-/
theorem lem_app_dyn_batch_iii {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (C : Covariances m n) (γstar CSig : ℝ) (hB : 0 < B)
    (hS : SizeFin C B γstar CSig) (z : Fin B → Ω → Vec m × Vec n)
    (hz : IIDBatch P ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) z)
    (E : Mat m n) (a : Fin B) :
    (∀ ω, (batchSummand C E z a ω).rank ≤ 1) ∧
    (rOut C * E * rIn C ≠ 0 → ∀ᵐ ω ∂P, (batchSummand C E z a ω).rank = 1) ∧
    eLpNorm (fun ω => nuc (batchSummand C E z a ω)) 2 P ≤
      ENNReal.ofReal (7 * CSig * γstar * fro (rOut C * E * rIn C)) := by
  refine ⟨fun ω => pd_batchSummand_rank_le_one C E z a ω, ?_, ?_⟩
  · intro hA
    exact pd_batchSummand_rank_eq_one_ae C hB z (by simpa [Muon.Setup.gaussPair] using hz)
      E a hA
  · exact pd_batchSummand_nuc_eLpNorm C γstar CSig hB hS z hz E a

/-- `lem:app-dyn-batch` (cr-2026-10-23), the conditional sentence (ll. 548–550), part (i) and (iii).
Lean states the corrected reading of CORRECTIONS row 1: `E` is determined by the past, i.e. it is
`𝓕`-measurable with `𝓕 = F_t`, and the batch of step `t` is independent of `𝓕`. The integrability
hypothesis `hEint` on `‖A_E‖_F²` makes the conditional expectations non-junk. Statement verbatim
from `section.tex` (ll. 537–550):
```latex
\begin{lemma}[Moments of one batch]\label{lem:app-dyn-batch}
Let $E\in\R^{\Nout\times\Nin}$ be deterministic, put $A_E\defeq\Sigmaout^{1/2}E\Sigmain^{1/2}$
and $d_a\defeq z_a^\T A_Ew_a$ for the samples of one batch, and let
$G^\circ[E]$ be the gradient \cref{eqn:app-dyn-batch} of that batch.
\begin{enumerate}[label=(\roman*)]
\item $\EE\norm{G^\circ[E]}_\F^2\le C_MB\norm{A_E}_\F^2$.
\item $\big(\EE\norm{G^\circ[E]}^2\big)^{1/2}\le C\log(2B)\norm{A_E}_\F$ and
$\big\|\max_{a\le B}\abs{d_a}\big\|_6\le C\log(2B)\norm{A_E}_\F$.
\item The sample $X_a\defeq B^{-1}d_a\Sigmaout^{1/2}(z_a\tensor w_a)\Sigmain^{1/2}$ has rank
one and $(\EE\norm{X_a}_*^2)^{1/2}\le7C_\Sigma\gamma_\star\norm{A_E}_\F$.
\end{enumerate}
The same bounds hold conditionally on $\cF_t$ for a matrix $E$ determined by
the past and the batch of step $t$.
\end{lemma}
```
-/
theorem lem_app_dyn_batch_iv {Ω : Type*} (𝓕 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (C : Covariances m n) (γstar CSig : ℝ) (hB : 0 < B)
    (hS : SizeFin C B γstar CSig) (z : Fin B → Ω → Vec m × Vec n)
    (hz : IIDBatch P ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) z)
    (h𝓕 : 𝓕 ≤ mΩ)
    (hind : Indep 𝓕 (⨆ a, MeasurableSpace.comap (z a) inferInstance) P)
    (E : Ω → Mat m n) (hE : Measurable[𝓕] E)
    (hEint : Integrable (fun ω => fro (rOut C * E ω * rIn C) ^ 2) P) :
    (Integrable (fun ω' => fro (batchGrad (E ω') (physBatch C z ω')) ^ 2) P ∧
      ∀ᵐ ω ∂P, condExp 𝓕 P (fun ω' => fro (batchGrad (E ω') (physBatch C z ω')) ^ 2) ω ≤
        cMConst CSig γstar * (B : ℝ) * fro (rOut C * E ω * rIn C) ^ 2) ∧
    (∀ a, Integrable (fun ω' => nuc (batchSummand C (E ω') z a ω') ^ 2) P ∧
      ∀ᵐ ω ∂P, Real.sqrt (condExp 𝓕 P (fun ω' => nuc (batchSummand C (E ω') z a ω') ^ 2) ω) ≤
        7 * CSig * γstar * fro (rOut C * E ω * rIn C)) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hγ : 0 ≤ γstar := by
    have h0 : (0 : ℝ) ≤ ((max m n : ℕ) : ℝ) := Nat.cast_nonneg _
    have := hS.1
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hCS : 0 ≤ CSig := (pd_opNorm_nonneg _).trans hS.2.1
  have hcc : 0 ≤ 7 * CSig * γstar := by positivity
  let Y0 : Ω → (Fin B → Vec m × Vec n) := fun ω a => z a ω
  have hY0 : AEMeasurable Y0 P := AEMeasurable.of_eval hz.meas
  let Y : Ω → (Fin B → Vec m × Vec n) := hY0.mk Y0
  have hYm : Measurable Y := hY0.measurable_mk
  have hYae : Y0 =ᵐ[P] Y := hY0.ae_eq_mk
  have hindY0 : Indep 𝓕 (MeasurableSpace.comap Y0 inferInstance) P := by
    refine indep_of_indep_of_le_right hind ?_
    change MeasurableSpace.comap Y0 MeasurableSpace.pi ≤ _
    unfold MeasurableSpace.pi
    rw [MeasurableSpace.comap_iSup]
    refine iSup_mono fun a => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_rfl
  have hindY : Indep 𝓕 (MeasurableSpace.comap Y inferInstance) P :=
    pd_indep_mk_right 𝓕 Y0 hY0 hindY0
  have hlaw : P.map Y = P.map Y0 := (Measure.map_congr hYae).symm
  have hswap : ∀ᵐ ω ∂P, Y0 ω = Y ω := hYae
  refine ⟨?_, fun a => ?_⟩
  · let R1 : Mat m n → (Fin B → Vec m × Vec n) → ℝ :=
      fun e y => fro (batchGrad e (fun a => phys C (y a))) ^ 2
    have hR1 : Measurable (Function.uncurry R1) := by
      have : Measurable (fun p : Mat m n × (Fin B → Vec m × Vec n) =>
          batchGrad p.1 (fun a => phys C (p.2 a))) := by
        unfold batchGrad Muon.Setup.grad phys resid outer Matrix.vecMulVec
          Matrix.mulVec dotProduct
        fun_prop
      have hm : Measurable (fun K : Mat m n => fro K ^ 2) := pd_fro_sq_meas
      exact hm.comp this
    have key : ∀ e : Mat m n, Integrable (R1 e) (P.map Y) ∧
        ∫ y, R1 e y ∂(P.map Y) ≤ cMConst CSig γstar * (B : ℝ) * fro (rOut C * e * rIn C) ^ 2 := by
      intro e
      obtain ⟨hi, hv⟩ := lem_app_dyn_batch_i C γstar CSig hB hS z hz e
      have hmeas : AEStronglyMeasurable (R1 e) (P.map Y0) :=
        (Measurable.of_uncurry_left hR1).aestronglyMeasurable
      rw [hlaw]
      refine ⟨(integrable_map_measure hmeas hY0).2 hi, ?_⟩
      rw [integral_map hY0 hmeas]
      exact hv
    have hg : Integrable (fun ω => cMConst CSig γstar * (B : ℝ) *
        fro (rOut C * E ω * rIn C) ^ 2) P := hEint.const_mul _
    obtain ⟨hint, hae⟩ := pd_freeze_bound0 𝓕 h𝓕 hE hYm hindY hR1
      (fun e y => sq_nonneg _)
      (g := fun e => cMConst CSig γstar * (B : ℝ) * fro (rOut C * e * rIn C) ^ 2) hg
      (fun e => (key e).1) (fun e => (key e).2)
    have heq : (fun ω => R1 (E ω) (Y ω)) =ᵐ[P]
        (fun ω' => fro (batchGrad (E ω') (physBatch C z ω')) ^ 2) := by
      filter_upwards [hswap] with ω hω
      rw [← hω]; rfl
    refine ⟨hint.congr heq, ?_⟩
    have hc := condExp_congr_ae (m := 𝓕) heq
    filter_upwards [hc, hae] with ω h1 h2
    rw [← h1]
    exact h2.2
  · let R3 : Mat m n → (Fin B → Vec m × Vec n) → ℝ :=
      fun e y => (|(B : ℝ)⁻¹ * resid e (phys C (y a))| *
        eucNorm (phys C (y a)).1 * eucNorm (phys C (y a)).2) ^ 2
    have hR3 : Measurable (Function.uncurry R3) := by
      unfold R3 resid eucNorm phys Function.uncurry Matrix.mulVec dotProduct
      fun_prop
    have hR30 : ∀ e y, 0 ≤ R3 e y := fun e y => sq_nonneg _
    have hnuc : ∀ e ω, nuc (batchSummand C e z a ω) ^ 2 = R3 e (Y0 ω) := by
      intro e ω
      rw [pd_batchSummand_nuc]
    have key : ∀ e : Mat m n, Integrable (R3 e) (P.map Y) ∧
        ∫ y, R3 e y ∂(P.map Y) ≤ (7 * CSig * γstar * fro (rOut C * e * rIn C)) ^ 2 := by
      intro e
      have hcn : 0 ≤ 7 * CSig * γstar * fro (rOut C * e * rIn C) :=
        mul_nonneg hcc (Real.sqrt_nonneg _)
      have hae : AEStronglyMeasurable (fun ω => nuc (batchSummand C e z a ω)) P := by
        have : (fun ω => nuc (batchSummand C e z a ω)) =
            fun ω => Real.sqrt (R3 e (Y0 ω)) := by
          funext ω
          rw [← hnuc, Real.sqrt_sq (nuc_nonneg _)]
        rw [this]
        exact ((Measurable.of_uncurry_left hR3).sqrt.comp_aemeasurable hY0).aestronglyMeasurable
      have hb := pd_batchSummand_nuc_eLpNorm C γstar CSig hB hS z hz e a
      have hb' : eLpNorm (fun ω => nuc (batchSummand C e z a ω)) ((2 : ℕ) : ℝ≥0∞) P ≤
          ENNReal.ofReal (7 * CSig * γstar * fro (rOut C * e * rIn C)) := by
        rw [Nat.cast_ofNat]; exact hb
      obtain ⟨hi, hv⟩ := pd_power_integral_of_eLpNorm P _ 2 (by norm_num) hae
        (fun ω => nuc_nonneg _) _ hcn hb'
      have hmeas : AEStronglyMeasurable (R3 e) (P.map Y0) :=
        (Measurable.of_uncurry_left hR3).aestronglyMeasurable
      have hi' : Integrable (fun ω => R3 e (Y0 ω)) P := hi.congr
        (Filter.Eventually.of_forall fun ω => hnuc e ω)
      rw [hlaw]
      refine ⟨(integrable_map_measure hmeas hY0).2 hi', ?_⟩
      rw [integral_map hY0 hmeas]
      have hint0 : 0 ≤ ∫ ω, R3 e (Y0 ω) ∂P := integral_nonneg fun ω => hR30 _ _
      have hv' : (∫ ω, R3 e (Y0 ω) ∂P) ^ (1 / (2 : ℝ)) ≤
          7 * CSig * γstar * fro (rOut C * e * rIn C) := by
        have : (∫ ω, nuc (batchSummand C e z a ω) ^ 2 ∂P) = ∫ ω, R3 e (Y0 ω) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω => hnuc e ω)
        simpa only [Nat.cast_ofNat, this] using hv
      have := pow_le_pow_left₀ (Real.rpow_nonneg hint0 _) hv' 2
      rwa [← Real.rpow_natCast, ← Real.rpow_mul hint0, one_div,
        show (((2:ℝ)⁻¹) * ((2:ℕ):ℝ)) = 1 by norm_num, Real.rpow_one] at this
    have hg : Integrable (fun ω => (7 * CSig * γstar * fro (rOut C * E ω * rIn C)) ^ 2) P :=
      (hEint.const_mul ((7 * CSig * γstar) ^ 2)).congr
        (Filter.Eventually.of_forall fun ω => by simp only [mul_pow])
    obtain ⟨hint, hae⟩ := pd_freeze_bound0 𝓕 h𝓕 hE hYm hindY hR3 hR30
      (g := fun e => (7 * CSig * γstar * fro (rOut C * e * rIn C)) ^ 2) hg
      (fun e => (key e).1) (fun e => (key e).2)
    have heq : (fun ω => R3 (E ω) (Y ω)) =ᵐ[P]
        (fun ω' => nuc (batchSummand C (E ω') z a ω') ^ 2) := by
      filter_upwards [hswap] with ω hω
      rw [hnuc, hω]
    refine ⟨hint.congr heq, ?_⟩
    have hc := condExp_congr_ae (m := 𝓕) heq
    filter_upwards [hc, hae] with ω h1 h2
    rw [← h1]
    calc Real.sqrt _ ≤ Real.sqrt ((7 * CSig * γstar * fro (rOut C * E ω * rIn C)) ^ 2) :=
          Real.sqrt_le_sqrt h2.2
      _ = _ := Real.sqrt_sq (mul_nonneg hcc (Real.sqrt_nonneg _))

private lemma pd_freeze_bound {Ω α β : Type*} (𝓕 : MeasurableSpace Ω)
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


/-- `lem:app-dyn-batch` (cr-2026-10-23), the conditional sentence (ll. 548–550), part (ii). The constant
`K = K(C_Σ, γ⋆)` is quantified before the data, as in `lem_app_dyn_batch_ii`. Lean states the corrected
reading of CORRECTIONS row 1 (`E` is `𝓕`-measurable, `𝓕 = F_t`, batch independent of `𝓕`), with the
integrability hypotheses on `‖A_E‖_F²` and `‖A_E‖_F⁶`. The conditional `L²` bound is
`(E[‖G°[E]‖_op²|𝓕])^{1/2}` and the conditional `L⁶` bound is `(E[max_a|d_a|⁶|𝓕])^{1/6}`, both with the
same `K`, as in `lem:app-dyn-batch`(ii) (ll. 548–549).
Statement verbatim from `section.tex` (ll. 537–550):
```latex
\begin{lemma}[Moments of one batch]\label{lem:app-dyn-batch}
Let $E\in\R^{\Nout\times\Nin}$ be deterministic, put $A_E\defeq\Sigmaout^{1/2}E\Sigmain^{1/2}$
and $d_a\defeq z_a^\T A_Ew_a$ for the samples of one batch, and let
$G^\circ[E]$ be the gradient \cref{eqn:app-dyn-batch} of that batch.
\begin{enumerate}[label=(\roman*)]
\item $\EE\norm{G^\circ[E]}_\F^2\le C_MB\norm{A_E}_\F^2$.
\item $\big(\EE\norm{G^\circ[E]}^2\big)^{1/2}\le C\log(2B)\norm{A_E}_\F$ and
$\big\|\max_{a\le B}\abs{d_a}\big\|_6\le C\log(2B)\norm{A_E}_\F$.
\item The sample $X_a\defeq B^{-1}d_a\Sigmaout^{1/2}(z_a\tensor w_a)\Sigmain^{1/2}$ has rank
one and $(\EE\norm{X_a}_*^2)^{1/2}\le7C_\Sigma\gamma_\star\norm{A_E}_\F$.
\end{enumerate}
The same bounds hold conditionally on $\cF_t$ for a matrix $E$ determined by
the past and the batch of step $t$.
\end{lemma}
```
-/
theorem lem_app_dyn_batch_iv_ii (certOp : Muon.External.GaussianOpNormL6) (γstar CSig : ℝ) :
    ∃ K : ℝ, ∀ (m n B : ℕ) (C : Covariances m n) (hB : 0 < B), SizeFin C B γstar CSig →
      ∀ (Ω : Type) (𝓕 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (z : Fin B → Ω → Vec m × Vec n),
        IIDBatch P ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) z →
        𝓕 ≤ mΩ → Indep 𝓕 (⨆ a, MeasurableSpace.comap (z a) inferInstance) P →
          ∀ E : Ω → Mat m n, Measurable[𝓕] E →
            Integrable (fun ω => fro (rOut C * E ω * rIn C) ^ 2) P →
            Integrable (fun ω => fro (rOut C * E ω * rIn C) ^ 6) P →
            (Integrable (fun ω' => opNorm (batchGrad (E ω') (physBatch C z ω')) ^ 2) P ∧
              ∀ᵐ ω ∂P, Real.sqrt (condExp 𝓕 P
                (fun ω' => opNorm (batchGrad (E ω') (physBatch C z ω')) ^ 2) ω) ≤
                K * Real.log (2 * (B : ℝ)) * fro (rOut C * E ω * rIn C)) ∧
            (Integrable (fun ω' => (Finset.univ.sup'
                (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
                (fun a => |resid (E ω') (phys C (z a ω'))|)) ^ 6) P ∧
              ∀ᵐ ω ∂P, condExp 𝓕 P (fun ω' => (Finset.univ.sup'
                (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
                (fun a => |resid (E ω') (phys C (z a ω'))|)) ^ 6) ω ^ (1 / 6 : ℝ) ≤
                K * Real.log (2 * (B : ℝ)) * fro (rOut C * E ω * rIn C)) := by
  obtain ⟨K0, hK0⟩ := lem_app_dyn_batch_ii certOp γstar CSig
  refine ⟨max K0 0, ?_⟩
  intro m n B C hB hS Ω 𝓕 mΩ P _ z hz h𝓕 hind E hE hE2 hE6
  have hKnn : 0 ≤ max K0 0 := le_max_right _ _
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) :=
    Real.log_nonneg (by
      have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
      nlinarith)
  set K : ℝ := max K0 0 with hKdef
  set L : ℝ := Real.log (2 * (B : ℝ)) with hLdef
  let Y0 : Ω → (Fin B → Vec m × Vec n) := fun ω a => z a ω
  have hY0 : AEMeasurable Y0 P := AEMeasurable.of_eval hz.meas
  let Y : Ω → (Fin B → Vec m × Vec n) := hY0.mk Y0
  have hYm : Measurable Y := hY0.measurable_mk
  have hYae : Y0 =ᵐ[P] Y := hY0.ae_eq_mk
  have hindY0 : Indep 𝓕 (MeasurableSpace.comap Y0 inferInstance) P := by
    refine indep_of_indep_of_le_right hind ?_
    change MeasurableSpace.comap Y0 MeasurableSpace.pi ≤ _
    unfold MeasurableSpace.pi
    rw [MeasurableSpace.comap_iSup]
    refine iSup_mono fun a => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_rfl
  have hindY : Indep 𝓕 (MeasurableSpace.comap Y inferInstance) P :=
    pd_indep_mk_right 𝓕 Y0 hY0 hindY0
  have hlaw : P.map Y = P.map Y0 := (Measure.map_congr hYae).symm
  let R1 : Mat m n → (Fin B → Vec m × Vec n) → ℝ :=
    fun e y => opNorm (batchGrad e (fun a => phys C (y a)))
  let R2 : Mat m n → (Fin B → Vec m × Vec n) → ℝ :=
    fun e y => Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
      (fun a => |resid e (phys C (y a))|)
  have hR1 : Measurable (Function.uncurry R1) := by
    apply pd_opNorm_continuous.measurable.comp
    unfold batchGrad Muon.Setup.grad phys resid outer Matrix.vecMulVec
      Matrix.mulVec dotProduct
    fun_prop
  have hR2 : Measurable (Function.uncurry R2) := by
    have heq : Function.uncurry R2 = Finset.univ.sup'
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
        (fun a (p : Mat m n × (Fin B → Vec m × Vec n)) =>
          |resid p.1 (phys C (p.2 a))|) := by
      funext p
      simp [R2, Function.uncurry, Finset.sup'_apply]
    rw [heq]
    refine Finset.measurable_sup' _ fun a _ => ?_
    unfold phys resid Matrix.mulVec dotProduct
    fun_prop

  have hpow : ∀ (x c : ℝ) (p : ℕ), p ≠ 0 → 0 ≤ x → 0 ≤ c → x ^ (1 / (p : ℝ)) ≤ c →
      x ≤ c ^ p := by
    intro x c p hp hx hc h
    have := pow_le_pow_left₀ (Real.rpow_nonneg hx _) h p
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hx, one_div,
      inv_mul_cancel₀ (by exact_mod_cast hp), Real.rpow_one] at this
  have hR1e : ∀ e, Measurable (R1 e) := fun e => Measurable.of_uncurry_left hR1
  have hR2e : ∀ e, Measurable (R2 e) := fun e => Measurable.of_uncurry_left hR2
  have hR10 : ∀ e y, 0 ≤ R1 e y := fun e y => pd_opNorm_nonneg _
  have hR20 : ∀ e y, 0 ≤ R2 e y := fun e y =>
    (abs_nonneg _).trans (Finset.le_sup' (fun a => |resid e (phys C (y a))|)
      (Finset.mem_univ ⟨0, hB⟩))
  have hbat := fun e : Mat m n => hK0 m n B C hB hS Ω P z hz e
  have hKLnn : 0 ≤ K * L := mul_nonneg hKnn hlog
  have hcnn : ∀ e : Mat m n, 0 ≤ K * L * fro (rOut C * e * rIn C) :=
    fun e => mul_nonneg hKLnn (Real.sqrt_nonneg _)
  have hle1 : ∀ e : Mat m n, K0 * L * fro (rOut C * e * rIn C) ≤
      K * L * fro (rOut C * e * rIn C) := fun e =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)
      (Real.sqrt_nonneg _)
  -- fixed-`e` bounds
  have key1 : ∀ e : Mat m n, Integrable (fun y => R1 e y ^ 2) (P.map Y) ∧
      ∫ y, R1 e y ^ 2 ∂(P.map Y) ≤ (K * L * fro (rOut C * e * rIn C)) ^ 2 := by
    intro e
    have hae : AEStronglyMeasurable (fun ω => R1 e (Y0 ω)) P :=
      ((hR1e e).comp_aemeasurable hY0).aestronglyMeasurable
    have hb : eLpNorm (fun ω => R1 e (Y0 ω)) ((2 : ℕ) : ℝ≥0∞) P ≤
        ENNReal.ofReal (K * L * fro (rOut C * e * rIn C)) := by
      rw [Nat.cast_ofNat]
      exact (hbat e).1.trans (ENNReal.ofReal_le_ofReal (hle1 e))
    obtain ⟨hi, hv⟩ := pd_power_integral_of_eLpNorm P _ 2 (by norm_num) hae
      (fun ω => hR10 _ _) _ (hcnn e) hb
    have hmeas : AEStronglyMeasurable (fun y => R1 e y ^ 2) (P.map Y0) :=
      ((hR1e e).pow_const 2).aestronglyMeasurable
    rw [hlaw]
    refine ⟨(integrable_map_measure hmeas hY0).2 hi, ?_⟩
    rw [integral_map hY0 hmeas]
    exact hpow _ _ 2 (by norm_num) (integral_nonneg fun ω => sq_nonneg _) (hcnn e) hv
  have key2 : ∀ e : Mat m n, Integrable (fun y => R2 e y ^ 6) (P.map Y) ∧
      ∫ y, R2 e y ^ 6 ∂(P.map Y) ≤ (K * L * fro (rOut C * e * rIn C)) ^ 6 := by
    intro e
    have hae : AEStronglyMeasurable (fun ω => R2 e (Y0 ω)) P :=
      ((hR2e e).comp_aemeasurable hY0).aestronglyMeasurable
    have hb : eLpNorm (fun ω => R2 e (Y0 ω)) ((6 : ℕ) : ℝ≥0∞) P ≤
        ENNReal.ofReal (K * L * fro (rOut C * e * rIn C)) := by
      rw [Nat.cast_ofNat]
      exact (hbat e).2.trans (ENNReal.ofReal_le_ofReal (hle1 e))
    obtain ⟨hi, hv⟩ := pd_power_integral_of_eLpNorm P _ 6 (by norm_num) hae
      (fun ω => hR20 _ _) _ (hcnn e) hb
    have hmeas : AEStronglyMeasurable (fun y => R2 e y ^ 6) (P.map Y0) :=
      ((hR2e e).pow_const 6).aestronglyMeasurable
    rw [hlaw]
    refine ⟨(integrable_map_measure hmeas hY0).2 hi, ?_⟩
    rw [integral_map hY0 hmeas]
    exact hpow _ _ 6 (by norm_num) (integral_nonneg fun ω => by positivity) (hcnn e) hv
  have hg1 : Integrable (fun ω => (K * L * fro (rOut C * E ω * rIn C)) ^ 2) P :=
    (hE2.const_mul ((K * L) ^ 2)).congr
      (Filter.Eventually.of_forall fun ω => by simp only [mul_pow])
  have hg2 : Integrable (fun ω => (K * L * fro (rOut C * E ω * rIn C)) ^ 6) P :=
    (hE6.const_mul ((K * L) ^ 6)).congr
      (Filter.Eventually.of_forall fun ω => by simp only [mul_pow])
  have hf1 : Measurable (Function.uncurry fun e y => R1 e y ^ 2) := hR1.pow_const 2
  have hf2 : Measurable (Function.uncurry fun e y => R2 e y ^ 6) := hR2.pow_const 6
  obtain ⟨hint1, hae1⟩ := pd_freeze_bound 𝓕 h𝓕 hE hYm hindY hf1
    (fun e y => sq_nonneg _) (g := fun e => (K * L * fro (rOut C * e * rIn C)) ^ 2) hg1
    (fun e => (key1 e).1) (fun e => (key1 e).2)
  obtain ⟨hint2, hae2⟩ := pd_freeze_bound 𝓕 h𝓕 hE hYm hindY hf2
    (fun e y => pow_nonneg (hR20 e y) 6)
    (g := fun e => (K * L * fro (rOut C * e * rIn C)) ^ 6) hg2
    (fun e => (key2 e).1) (fun e => (key2 e).2)
  have hswap : ∀ᵐ ω ∂P, Y0 ω = Y ω := hYae
  have heq1 : (fun ω => R1 (E ω) (Y ω) ^ 2) =ᵐ[P]
      (fun ω' => opNorm (batchGrad (E ω') (physBatch C z ω')) ^ 2) := by
    filter_upwards [hswap] with ω hω
    rw [← hω]; rfl
  have heq2 : (fun ω => R2 (E ω) (Y ω) ^ 6) =ᵐ[P]
      (fun ω' => (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
        (fun a => |resid (E ω') (phys C (z a ω'))|)) ^ 6) := by
    filter_upwards [hswap] with ω hω
    rw [← hω]
  have hc1 := condExp_congr_ae (m := 𝓕) heq1
  have hc2 := condExp_congr_ae (m := 𝓕) heq2
  refine ⟨⟨hint1.congr heq1, ?_⟩, ⟨hint2.congr heq2, ?_⟩⟩
  · filter_upwards [hc1, hae1] with ω h1 h2
    rw [← h1]
    calc Real.sqrt _ ≤ Real.sqrt ((K * L * fro (rOut C * E ω * rIn C)) ^ 2) :=
          Real.sqrt_le_sqrt h2.2
      _ = K * L * fro (rOut C * E ω * rIn C) := Real.sqrt_sq (hcnn _)
  · filter_upwards [hc2, hae2] with ω h1 h2
    rw [← h1]
    calc _ ≤ ((K * L * fro (rOut C * E ω * rIn C)) ^ 6) ^ (1 / (6 : ℝ)) :=
          Real.rpow_le_rpow h2.1 h2.2 (by norm_num)
      _ = K * L * fro (rOut C * E ω * rIn C) := by
          have := Real.pow_rpow_inv_natCast (hcnn (E ω)) (n := 6) (by norm_num)
          simpa [one_div] using this

/-! ## Covariance inequality (`lem:app-dyn-covariance`) -/

/-- Cauchy–Schwarz in `eLpNorm` form. -/
private lemma cov_cs {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a b : Ω → ℝ} (ha : MemLp a 2 P) (hb : MemLp b 2 P) :
    ENNReal.ofReal |∫ ω, a ω * b ω ∂P| ≤ eLpNorm a 2 P * eLpNorm b 2 P := by
  have h1 : eLpNorm (fun ω => a ω * b ω) 1 P ≤ eLpNorm a 2 P * eLpNorm b 2 P := by
    exact eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) ha.aestronglyMeasurable hb.aestronglyMeasurable
  have hint : Integrable (fun ω => a ω * b ω) P := by
    have : Integrable (a * b) P := ha.integrable_mul hb
    exact this
  calc ENNReal.ofReal |∫ ω, a ω * b ω ∂P| ≤ ENNReal.ofReal (∫ ω, ‖a ω * b ω‖ ∂P) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := norm_integral_le_integral_norm (μ := P) (f := fun ω => a ω * b ω)
        simpa only [Real.norm_eq_abs] using this
    _ = eLpNorm (fun ω => a ω * b ω) 1 P := by
        rw [ofReal_integral_norm_eq_lintegral_enorm hint, eLpNorm_one_eq_lintegral_enorm]
        exact hint.aestronglyMeasurable
    _ ≤ _ := h1

/-- `∫ h u = ∫ h E[u | m]` for `m`-measurable `L²` `h`. -/
private lemma cov_ip_cond {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (hm : m ≤ mΩ) {h u : Ω → ℝ}
    (hh : StronglyMeasurable[m] h) (hh2 : MemLp h 2 P) (hu : MemLp u 2 P) :
    ∫ ω, h ω * u ω ∂P = ∫ ω, h ω * (P[u | m]) ω ∂P := by
  have hint : Integrable (fun ω => h ω * u ω) P := by
    have : Integrable (h * u) P := hh2.integrable_mul hu
    exact this
  have hc := condExp_mul_of_stronglyMeasurable_left (μ := P) hh hint (hu.integrable one_le_two)
  rw [← integral_condExp hm (f := fun ω => h ω * u ω)]
  exact integral_congr_ae hc

/-- `L²` Lévy upward theorem (Fatou + Pythagoras form). -/
private lemma cov_levy_l2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) {f : Ω → ℝ} (hf2 : MemLp f 2 P)
    (hfm : StronglyMeasurable[⨆ n, ℱ n] f) :
    Tendsto (fun n => ∫ ω, (f ω - (P[f | ℱ n]) ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hfi : Integrable f P := hf2.integrable one_le_two
  have hfn2 : ∀ n, MemLp (P[f | ℱ n]) 2 P := fun n => MemLp.condExp one_le_two hf2
  have hmeas : ∀ n, Measurable (P[f | ℱ n]) := fun n =>
    (stronglyMeasurable_condExp.mono (ℱ.le n)).measurable
  have hsq : Integrable (fun ω => f ω ^ 2) P := hf2.integrable_sq
  have hsqn : ∀ n, Integrable (fun ω => (P[f | ℱ n]) ω ^ 2) P := fun n => (hfn2 n).integrable_sq
  have hprod : ∀ n, Integrable (fun ω => f ω * (P[f | ℱ n]) ω) P := fun n => by
    have : Integrable (f * P[f | ℱ n]) P := hf2.integrable_mul (hfn2 n)
    exact this
  set a : ℝ := ∫ ω, f ω ^ 2 ∂P with ha
  set an : ℕ → ℝ := fun n => ∫ ω, (P[f | ℱ n]) ω ^ 2 ∂P with han
  have hip : ∀ n, ∫ ω, f ω * (P[f | ℱ n]) ω ∂P = an n := by
    intro n
    have := cov_ip_cond (ℱ.le n) (h := P[f | ℱ n]) (u := f) stronglyMeasurable_condExp (hfn2 n) hf2
    simp only [han, sq]
    calc ∫ ω, f ω * (P[f | ℱ n]) ω ∂P = ∫ ω, (P[f | ℱ n]) ω * f ω ∂P :=
          integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
      _ = _ := this
  have hpy : ∀ n, ∫ ω, (f ω - (P[f | ℱ n]) ω) ^ 2 ∂P = a - an n := by
    intro n
    have e : (fun ω => (f ω - (P[f | ℱ n]) ω) ^ 2) =
        fun ω => (f ω ^ 2 - 2 * (f ω * (P[f | ℱ n]) ω)) + (P[f | ℱ n]) ω ^ 2 := by
      ext ω; ring
    have i1 : Integrable (fun ω => f ω ^ 2 - 2 * (f ω * (P[f | ℱ n]) ω)) P :=
      hsq.sub ((hprod n).const_mul 2)
    have i2 : Integrable (fun ω => 2 * (f ω * (P[f | ℱ n]) ω)) P := (hprod n).const_mul 2
    rw [e, integral_add i1 (hsqn n), integral_sub hsq i2, integral_const_mul, hip n]
    simp only [ha, han]; ring
  have han_le : ∀ n, an n ≤ a := fun n => by
    have h0 : 0 ≤ ∫ ω, (f ω - (P[f | ℱ n]) ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    rw [hpy n] at h0; linarith
  have han0 : ∀ n, 0 ≤ an n := fun n => integral_nonneg fun ω => sq_nonneg _
  -- a.e. convergence
  have hae : ∀ᵐ ω ∂P, Tendsto (fun n => (P[f | ℱ n]) ω) atTop (𝓝 (f ω)) := hfi.tendsto_ae_condExp hfm
  -- Fatou
  have hfat : ENNReal.ofReal a ≤ liminf (fun n => ENNReal.ofReal (an n)) atTop := by
    have h1 : ENNReal.ofReal a = ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P :=
      ofReal_integral_eq_lintegral_ofReal hsq (Eventually.of_forall fun ω => sq_nonneg _)
    have h2 : ∀ n, ENNReal.ofReal (an n) = ∫⁻ ω, ENNReal.ofReal ((P[f | ℱ n]) ω ^ 2) ∂P :=
      fun n => ofReal_integral_eq_lintegral_ofReal (hsqn n) (Eventually.of_forall fun ω => sq_nonneg _)
    have h3 : ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P =
        ∫⁻ ω, liminf (fun n => ENNReal.ofReal ((P[f | ℱ n]) ω ^ 2)) atTop ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with ω hω
      have : Tendsto (fun n => ENNReal.ofReal ((P[f | ℱ n]) ω ^ 2)) atTop
          (𝓝 (ENNReal.ofReal (f ω ^ 2))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_pow 2).tendsto _ |>.comp hω)
      exact this.liminf_eq.symm
    rw [h1, h3]
    simp_rw [h2]
    exact lintegral_liminf_le (fun n => ((hmeas n).pow_const 2).ennreal_ofReal)
  have hlim : Tendsto (fun n => ENNReal.ofReal (an n)) atTop (𝓝 (ENNReal.ofReal a)) := by
    refine tendsto_of_le_liminf_of_limsup_le hfat ?_
    refine (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n => ?_))
    exact ENNReal.ofReal_le_ofReal (han_le n)
  have hlim' : Tendsto an atTop (𝓝 a) := by
    have ha0 : 0 ≤ a := integral_nonneg fun ω => sq_nonneg (f ω)
    have := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hlim
    rw [ENNReal.toReal_ofReal ha0] at this
    refine this.congr fun n => ?_
    simp [ENNReal.toReal_ofReal (han0 n)]
  simp_rw [hpy]
  simpa using (tendsto_const_nhds (x := a)).sub hlim'


private lemma cov_eLpNorm_two {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {a : Ω → ℝ} (ha : MemLp a 2 P) :
    eLpNorm a 2 P = ENNReal.ofReal ((∫ ω, a ω ^ 2 ∂P) ^ (1 / (2 : ℝ))) := by
  have := ha.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  rw [this]
  simp only [ENNReal.toReal_ofNat]
  have h : ∫ ω, ‖a ω‖ ^ (2 : ℝ) ∂P = ∫ ω, a ω ^ 2 ∂P :=
    integral_congr_ae (Eventually.of_forall fun ω => by simp [sq_abs])
  rw [h, one_div]


/-- Orthogonality: `∫ h P[u | ℱ n] = ∫ h P[u | ℱ k]` for `ℱ k`-measurable `h`, `k ≤ n`. -/
private lemma cov_orth {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) {k n : ℕ} (hkn : k ≤ n) {h u : Ω → ℝ}
    (hh : StronglyMeasurable[ℱ k] h) (hh2 : MemLp h 2 P) (hu : MemLp u 2 P) :
    ∫ ω, h ω * (P[u | ℱ n]) ω ∂P = ∫ ω, h ω * (P[u | ℱ k]) ω ∂P := by
  rw [← cov_ip_cond (ℱ.le n) (hh.mono (ℱ.mono hkn)) hh2 hu, ← cov_ip_cond (ℱ.le k) hh hh2 hu]

/-- Abstract covariance bound from martingale-difference bounds. -/
private lemma cov_main_abstract {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (h0 : (ℱ 0 : MeasurableSpace Ω) = ⊥)
    {f g : Ω → ℝ} (hf2 : MemLp f 2 P) (hg2 : MemLp g 2 P)
    (hfm : StronglyMeasurable[⨆ n, ℱ n] f)
    (bf bg : ℕ → ℝ≥0∞)
    (hbf : ∀ l, eLpNorm (fun ω => (P[f | ℱ (l + 1)]) ω - (P[f | ℱ l]) ω) 2 P ≤ bf l)
    (hbg : ∀ l, eLpNorm (fun ω => (P[g | ℱ (l + 1)]) ω - (P[g | ℱ l]) ω) 2 P ≤ bg l) :
    ENNReal.ofReal |covariance f g P| ≤ ∑' l, bf l * bg l := by
  have hF2 : ∀ n, MemLp (P[f | ℱ n]) 2 P := fun n => MemLp.condExp one_le_two hf2
  have hG2 : ∀ n, MemLp (P[g | ℱ n]) 2 P := fun n => MemLp.condExp one_le_two hg2
  have hFs : ∀ n, StronglyMeasurable[ℱ n] (P[f | ℱ n]) := fun n => stronglyMeasurable_condExp
  have hGs : ∀ n, StronglyMeasurable[ℱ n] (P[g | ℱ n]) := fun n => stronglyMeasurable_condExp
  set c : ℕ → ℝ := fun l => ∫ ω, ((P[f | ℱ (l + 1)]) ω - (P[f | ℱ l]) ω) *
      ((P[g | ℱ (l + 1)]) ω - (P[g | ℱ l]) ω) ∂P with hc
  set T : ℕ → ℝ := fun n => ∫ ω, (P[f | ℱ n]) ω * (P[g | ℱ n]) ω ∂P with hT
  have hint : ∀ {a b : Ω → ℝ}, MemLp a 2 P → MemLp b 2 P → Integrable (fun ω => a ω * b ω) P :=
    fun {a b} ha hb => by
      have : Integrable (a * b) P := ha.integrable_mul hb
      exact this
  -- Step A
  have hA : ∀ l, c l = T (l + 1) - T l := by
    intro l
    have e2 : ∫ ω, (P[f | ℱ (l + 1)]) ω * (P[g | ℱ l]) ω ∂P = T l := by
      have := cov_orth ℱ (Nat.le_succ l) (h := P[g | ℱ l]) (u := f) (hGs l) (hG2 l) hf2
      simp only [hT]
      calc ∫ ω, (P[f | ℱ (l + 1)]) ω * (P[g | ℱ l]) ω ∂P
          = ∫ ω, (P[g | ℱ l]) ω * (P[f | ℱ (l + 1)]) ω ∂P :=
            integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
        _ = ∫ ω, (P[g | ℱ l]) ω * (P[f | ℱ l]) ω ∂P := this
        _ = _ := integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    have e3 : ∫ ω, (P[f | ℱ l]) ω * (P[g | ℱ (l + 1)]) ω ∂P = T l :=
      cov_orth ℱ (Nat.le_succ l) (hFs l) (hF2 l) hg2
    have expand : (fun ω => ((P[f | ℱ (l + 1)]) ω - (P[f | ℱ l]) ω) *
        ((P[g | ℱ (l + 1)]) ω - (P[g | ℱ l]) ω)) =
        fun ω => ((P[f | ℱ (l + 1)]) ω * (P[g | ℱ (l + 1)]) ω -
          (P[f | ℱ (l + 1)]) ω * (P[g | ℱ l]) ω) -
          (P[f | ℱ l]) ω * (P[g | ℱ (l + 1)]) ω + (P[f | ℱ l]) ω * (P[g | ℱ l]) ω := by
      ext ω; ring
    have i1 := hint (hF2 (l + 1)) (hG2 (l + 1))
    have i2 := hint (hF2 (l + 1)) (hG2 l)
    have i3 := hint (hF2 l) (hG2 (l + 1))
    have i4 := hint (hF2 l) (hG2 l)
    simp only [hc]
    have j1 : Integrable (fun ω => (P[f | ℱ (l + 1)]) ω * (P[g | ℱ (l + 1)]) ω -
        (P[f | ℱ (l + 1)]) ω * (P[g | ℱ l]) ω) P := i1.sub i2
    have j2 : Integrable (fun ω => (P[f | ℱ (l + 1)]) ω * (P[g | ℱ (l + 1)]) ω -
        (P[f | ℱ (l + 1)]) ω * (P[g | ℱ l]) ω - (P[f | ℱ l]) ω * (P[g | ℱ (l + 1)]) ω) P := j1.sub i3
    rw [expand, integral_add j2 i4, integral_sub j1 i3, integral_sub i1 i2, e2, e3]
    simp only [hT]; ring
  -- Step B
  have hT0 : T 0 = (∫ ω, f ω ∂P) * ∫ ω, g ω ∂P := by
    simp only [hT]
    have hf0 : P[f | ℱ 0] = fun _ => ∫ x, f x ∂P := by rw [h0]; exact condExp_bot f
    have hg0 : P[g | ℱ 0] = fun _ => ∫ x, g x ∂P := by rw [h0]; exact condExp_bot g
    rw [hf0, hg0]
    simp
  have hS : ∀ n, ∑ l ∈ Finset.range n, c l = T n - T 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, hA n]; ring
  -- Step D: T n → ∫ f g
  have hTn : Tendsto T atTop (𝓝 (∫ ω, f ω * g ω ∂P)) := by
    have hTeq : ∀ n, T n = ∫ ω, (P[f | ℱ n]) ω * g ω ∂P := fun n => by
      simp only [hT]
      exact (cov_ip_cond (ℱ.le n) (hFs n) (hF2 n) hg2).symm
    have hlev := cov_levy_l2 ℱ hf2 hfm
    have hen : Tendsto (fun n => eLpNorm (fun ω => (P[f | ℱ n]) ω - f ω) 2 P) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => ∫ ω, ((P[f | ℱ n]) ω - f ω) ^ 2 ∂P) atTop (𝓝 0) := by
        refine hlev.congr fun n => ?_
        exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
      have h2 : Tendsto (fun n => ENNReal.ofReal ((∫ ω, ((P[f | ℱ n]) ω - f ω) ^ 2 ∂P) ^ (1 / (2 : ℝ))))
          atTop (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ (1 / (2 : ℝ))))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp
          ((Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).tendsto.comp h1)
      simp only [Real.zero_rpow (by norm_num : (1 / (2 : ℝ)) ≠ 0), ENNReal.ofReal_zero] at h2
      refine h2.congr fun n => ?_
      exact (cov_eLpNorm_two ((hF2 n).sub hf2)).symm
    have hu : Tendsto (fun n => ENNReal.ofReal |∫ ω, (P[f | ℱ n]) ω * g ω ∂P - ∫ ω, f ω * g ω ∂P|)
        atTop (𝓝 0) := by
      have hup : Tendsto (fun n => eLpNorm (fun ω => (P[f | ℱ n]) ω - f ω) 2 P * eLpNorm g 2 P)
          atTop (𝓝 0) := by
        have := ENNReal.Tendsto.mul_const hen (Or.inr hg2.eLpNorm_ne_top)
        simpa using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => bot_le) ?_
      intro n
      have := cov_cs (a := fun ω => (P[f | ℱ n]) ω - f ω) ((hF2 n).sub hf2) hg2
      have e : ∫ ω, ((P[f | ℱ n]) ω - f ω) * g ω ∂P =
          ∫ ω, (P[f | ℱ n]) ω * g ω ∂P - ∫ ω, f ω * g ω ∂P := by
        rw [← integral_sub (hint (hF2 n) hg2) (hint hf2 hg2)]
        exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
      simpa only [e] using this
    have hu' : Tendsto (fun n => |∫ ω, (P[f | ℱ n]) ω * g ω ∂P - ∫ ω, f ω * g ω ∂P|) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hu
      rw [ENNReal.toReal_zero] at this
      refine this.congr fun n => ?_
      simp [ENNReal.toReal_ofReal (abs_nonneg _)]
    rw [show T = fun n => ∫ ω, (P[f | ℱ n]) ω * g ω ∂P from funext hTeq]
    refine tendsto_iff_dist_tendsto_zero.2 ?_
    simpa [Real.dist_eq] using hu'
  -- Step E
  have hcov : covariance f g P = (∫ ω, f ω * g ω ∂P) - (∫ ω, f ω ∂P) * ∫ ω, g ω ∂P := by
    rw [covariance_eq_sub hf2 hg2]; rfl
  have hSn : Tendsto (fun n => ENNReal.ofReal |T n - T 0|) atTop (𝓝 (ENNReal.ofReal |covariance f g P|)) := by
    rw [hcov, ← hT0]
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((continuous_abs.tendsto _).comp (hTn.sub_const _))
  refine le_of_tendsto' hSn fun n => ?_
  rw [← hS n]
  calc ENNReal.ofReal |∑ l ∈ Finset.range n, c l|
      ≤ ENNReal.ofReal (∑ l ∈ Finset.range n, |c l|) :=
        ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ l ∈ Finset.range n, ENNReal.ofReal |c l| :=
        ENNReal.ofReal_sum_of_nonneg fun l _ => abs_nonneg _
    _ ≤ ∑ l ∈ Finset.range n, bf l * bg l := by
        refine Finset.sum_le_sum fun l _ => ?_
        have := cov_cs ((hF2 (l + 1)).sub (hF2 l)) ((hG2 (l + 1)).sub (hG2 l))
        exact this.trans (mul_le_mul' (hbf l) (hbg l))
    _ ≤ ∑' l, bf l * bg l := ENNReal.sum_le_tsum _

/-- gluing of a finite prefix and a tail -/
private lemma cov_glue_meas {β : Type*} [MeasurableSpace β] (l : ℕ) :
    Measurable (fun p : (Fin l → β) × (ℕ → β) =>
      (fun k : ℕ => if h : k < l then p.1 ⟨k, h⟩ else p.2 (k - l))) := by
  refine measurable_pi_iff.2 fun k => ?_
  by_cases hk : k < l
  · simp only [hk, dite_true]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [hk, dite_false]
    exact (measurable_pi_apply _).comp measurable_snd

/-- coordinates are measurable for the prefix σ-algebra -/
private lemma cov_prefix_meas {Ω β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace β]
    (ξ : ℕ → Ω → β) (n : ℕ) :
    Measurable[⨆ k, ⨆ (_ : k < n), MeasurableSpace.comap (ξ k) inferInstance]
      (fun ω (i : Fin n) => ξ i ω) := by
  refine @measurable_pi_iff _ _ _ (⨆ k, ⨆ (_ : k < n), MeasurableSpace.comap (ξ k) inferInstance) _ _ |>.2 fun i => ?_
  exact (comap_measurable (ξ i)).mono (le_iSup₂_of_le (i : ℕ) i.2 le_rfl) le_rfl

/-- independence of prefix and tail -/
private lemma cov_indep_tail {Ω β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] (ξ ξ' : ℕ → Ω → β)
    (hξ : ∀ l, Measurable (ξ l)) (hξ' : ∀ l, Measurable (ξ' l))
    (hind : iIndepFun (Sum.elim ξ ξ' : ℕ ⊕ ℕ → Ω → β) P)
    (n : ℕ) (ι : ℕ → ℕ ⊕ ℕ) (hι : ∀ j, ι j ∉ ((fun k : ℕ => (Sum.inl k : ℕ ⊕ ℕ)) '' {k | k < n})) :
    Indep (⨆ k, ⨆ (_ : k < n), MeasurableSpace.comap (ξ k) inferInstance)
      (MeasurableSpace.comap (fun ω j => (Sum.elim ξ ξ' : ℕ ⊕ ℕ → Ω → β) (ι j) ω) inferInstance) P := by
  set Z : ℕ ⊕ ℕ → Ω → β := Sum.elim ξ ξ' with hZ
  have hZm : ∀ i, Measurable (Z i) := fun i => by
    cases i with
    | inl k => exact hξ k
    | inr k => exact hξ' k
  have hindep := indep_iSup_of_disjoint (m := fun i => MeasurableSpace.comap (Z i) inferInstance)
    (fun i => (hZm i).comap_le) hind (S := (fun k : ℕ => (Sum.inl k : ℕ ⊕ ℕ)) '' {k | k < n})
    (T := Set.range ι) (by
      rw [Set.disjoint_left]
      rintro i ⟨k, hk, rfl⟩ ⟨j, hj⟩
      exact hι j (hj ▸ ⟨k, hk, rfl⟩))
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hindep ?_) ?_
  · refine iSup₂_le fun k hk => ?_
    exact le_iSup₂_of_le (Sum.inl k) ⟨k, hk, rfl⟩ le_rfl
  · refine Measurable.comap_le ?_
    refine @measurable_pi_iff _ _ _ (⨆ i ∈ Set.range ι, MeasurableSpace.comap (Z i) inferInstance) _ _ |>.2 fun j => ?_
    exact (comap_measurable (Z (ι j))).mono (le_iSup₂_of_le (ι j) ⟨j, rfl⟩ le_rfl) le_rfl


private lemma cov_law_tail {Ω β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] (ξ ξ' : ℕ → Ω → β)
    (hξ : ∀ l, Measurable (ξ l)) (hξ' : ∀ l, Measurable (ξ' l))
    (hind : iIndepFun (Sum.elim ξ ξ' : ℕ ⊕ ℕ → Ω → β) P)
    (ι₁ ι₂ : ℕ → ℕ ⊕ ℕ) (h₁ : Function.Injective ι₁) (h₂ : Function.Injective ι₂)
    (hm : ∀ j, P.map ((Sum.elim ξ ξ' : ℕ ⊕ ℕ → Ω → β) (ι₁ j)) =
      P.map ((Sum.elim ξ ξ' : ℕ ⊕ ℕ → Ω → β) (ι₂ j))) :
    P.map (fun ω j => (Sum.elim ξ ξ' : ℕ ⊕ ℕ → Ω → β) (ι₁ j) ω) =
      P.map (fun ω j => (Sum.elim ξ ξ' : ℕ ⊕ ℕ → Ω → β) (ι₂ j) ω) := by
  have hZm : ∀ i, Measurable ((Sum.elim ξ ξ' : ℕ ⊕ ℕ → Ω → β) i) := fun i => by
    cases i with
    | inl k => exact hξ k
    | inr k => exact hξ' k
  rw [(hind.precomp h₁).map_fun_eq_infinitePi_map (fun j => hZm _),
    (hind.precomp h₂).map_fun_eq_infinitePi_map (fun j => hZm _)]
  congr 1
  funext j
  exact hm j


private lemma cov_key {Ω β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] (ξ ξ' : ℕ → Ω → β)
    (hξ : ∀ l, Measurable (ξ l)) (hξ' : ∀ l, Measurable (ξ' l))
    (hlaw : ∀ l, P.map (ξ' l) = P.map (ξ l))
    (hind : iIndepFun (Sum.elim ξ ξ' : ℕ ⊕ ℕ → Ω → β) P)
    (F : (ℕ → β) → ℝ) (hF : Measurable F) (l : ℕ)
    (hf : Integrable (fun ω => F (fun k => ξ k ω)) P)
    (hfl : Integrable (fun ω => F (Function.update (fun k => ξ k ω) l (ξ' l ω))) P) :
    condExp (⨆ k, ⨆ (_ : k < l + 1), MeasurableSpace.comap (ξ k) inferInstance) P
        (fun ω => F (Function.update (fun k => ξ k ω) l (ξ' l ω))) =ᵐ[P]
      condExp (⨆ k, ⨆ (_ : k < l), MeasurableSpace.comap (ξ k) inferInstance) P
        (fun ω => F (fun k => ξ k ω)) := by
  set Z : ℕ ⊕ ℕ → Ω → β := Sum.elim ξ ξ' with hZ
  set gl : (Fin l → β) → (ℕ → β) → (ℕ → β) :=
    fun x y k => if h : k < l then x ⟨k, h⟩ else y (k - l) with hgl
  have hglm : Measurable (fun p : (Fin l → β) × (ℕ → β) => gl p.1 p.2) := cov_glue_meas l
  set ι₁ : ℕ → ℕ ⊕ ℕ := fun j => Sum.inl (l + j) with hι₁
  set ι₂ : ℕ → ℕ ⊕ ℕ := fun j => if j = 0 then Sum.inr l else Sum.inl (l + j) with hι₂
  have hι₁inj : Function.Injective ι₁ := fun a b h => by
    simp only [hι₁, Sum.inl.injEq] at h; omega
  have hι₂inj : Function.Injective ι₂ := fun a b h => by
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [hι₂, ha, hb] at h <;> omega
  set Y₁ : Ω → ℕ → β := fun ω j => Z (ι₁ j) ω with hY₁
  set Y₂ : Ω → ℕ → β := fun ω j => Z (ι₂ j) ω with hY₂
  have hZm : ∀ i, Measurable (Z i) := fun i => by
    cases i with
    | inl k => exact hξ k
    | inr k => exact hξ' k
  have hY₁m : Measurable Y₁ := measurable_pi_iff.2 fun j => hZm _
  have hY₂m : Measurable Y₂ := measurable_pi_iff.2 fun j => hZm _
  have hlawY : P.map Y₂ = P.map Y₁ := by
    refine (cov_law_tail ξ ξ' hξ hξ' hind ι₁ ι₂ hι₁inj hι₂inj ?_).symm
    intro j
    by_cases hj : j = 0
    · subst hj; simp [hι₁, hι₂, hZ, hlaw l]
    · simp [hι₁, hι₂, hj]
  have hind₁ := cov_indep_tail ξ ξ' hξ hξ' hind l ι₁ (by
    rintro j ⟨k, hk, hkj⟩
    simp only [hι₁, Sum.inl.injEq] at hkj
    simp only [Set.mem_setOf_eq] at hk
    omega)
  have hind₂ := cov_indep_tail ξ ξ' hξ hξ' hind (l + 1) ι₂ (by
    intro j
    rintro ⟨k, hk, hkj⟩
    simp only [Set.mem_setOf_eq] at hk
    by_cases hj : j = 0
    · simp [hι₂, hj] at hkj
    · simp [hι₂, hj] at hkj; omega)
  set X₁ : Ω → Fin l → β := fun ω i => ξ i ω with hX₁
  set X₂ : Ω → Fin (l + 1) → β := fun ω i => ξ i ω with hX₂
  have hle : ∀ n, (⨆ k, ⨆ (_ : k < n), MeasurableSpace.comap (ξ k) inferInstance) ≤ mΩ :=
    fun n => iSup₂_le fun k _ => (hξ k).comap_le
  -- representations
  have hrep1 : (fun ω => F (fun k => ξ k ω)) =
      fun ω => (fun (x : Fin l → β) (y : ℕ → β) => F (gl x y)) (X₁ ω) (Y₁ ω) := by
    funext ω
    congr 1
    funext k
    by_cases hk : k < l
    · simp [hgl, hX₁, hk]
    · simp only [hgl, hY₁, hι₁, hk, dite_false, hZ, Sum.elim_inl]
      congr 1; omega
  have hrep2 : (fun ω => F (Function.update (fun k => ξ k ω) l (ξ' l ω))) =
      fun ω => (fun (x : Fin (l + 1) → β) (y : ℕ → β) =>
        F (gl (fun i => x (Fin.castSucc i)) y)) (X₂ ω) (Y₂ ω) := by
    funext ω
    congr 1
    funext k
    by_cases hk : k < l
    · simp [hgl, hX₂, hk, Function.update, Nat.ne_of_lt hk]
    · by_cases hk' : k = l
      · subst hk'
        simp [hgl, hY₂, hι₂, hZ]
      · have hk'' : k - l ≠ 0 := by omega
        simp [hgl, hY₂, hι₂, hk, hk', hk'', hZ, Function.update]
        congr 1; omega
  have hm1 : Measurable (Function.uncurry fun (x : Fin l → β) (y : ℕ → β) => F (gl x y)) :=
    hF.comp hglm
  have hm2 : Measurable (Function.uncurry fun (x : Fin (l + 1) → β) (y : ℕ → β) =>
      F (gl (fun i => x (Fin.castSucc i)) y)) := by
    have hh : Measurable (fun p : (Fin (l + 1) → β) × (ℕ → β) =>
        ((fun i => p.1 (Fin.castSucc i), p.2) : (Fin l → β) × (ℕ → β))) :=
      (measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp measurable_fst).prodMk
        measurable_snd
    exact hF.comp (hglm.comp hh)
  have c1 := Muon.Foundations.freezing_condExp
    (⨆ k, ⨆ (_ : k < l), MeasurableSpace.comap (ξ k) inferInstance) (hle l)
    (cov_prefix_meas ξ l) hY₁m hind₁ hm1 (by rw [← hrep1]; exact hf)
  have c2 := Muon.Foundations.freezing_condExp
    (⨆ k, ⨆ (_ : k < l + 1), MeasurableSpace.comap (ξ k) inferInstance) (hle (l + 1))
    (cov_prefix_meas ξ (l + 1)) hY₂m hind₂ hm2 (by rw [← hrep2]; exact hfl)
  have c1' : condExp (⨆ k, ⨆ (_ : k < l), MeasurableSpace.comap (ξ k) inferInstance) P
        (fun ω => F (fun k => ξ k ω)) =ᵐ[P] fun ω => ∫ y, F (gl (X₁ ω) y) ∂(P.map Y₁) := by
    rw [hrep1]; exact c1
  have c2' : condExp (⨆ k, ⨆ (_ : k < l + 1), MeasurableSpace.comap (ξ k) inferInstance) P
        (fun ω => F (Function.update (fun k => ξ k ω) l (ξ' l ω))) =ᵐ[P]
        fun ω => ∫ y, F (gl (fun i => X₂ ω (Fin.castSucc i)) y) ∂(P.map Y₂) := by
    rw [hrep2]; exact c2
  refine c2'.trans (Filter.EventuallyEq.trans ?_ c1'.symm)
  refine Eventually.of_forall fun ω => ?_
  simp only [hlawY]
  rfl


private lemma cov_step {Ω β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] (ξ ξ' : ℕ → Ω → β)
    (hξ : ∀ l, Measurable (ξ l)) (hξ' : ∀ l, Measurable (ξ' l))
    (hlaw : ∀ l, P.map (ξ' l) = P.map (ξ l))
    (hind : iIndepFun (Sum.elim ξ ξ' : ℕ ⊕ ℕ → Ω → β) P)
    (F : (ℕ → β) → ℝ) (hF : Measurable F)
    (hF2 : MemLp (fun ω => F (fun l => ξ l ω)) 2 P)
    (ℱ : Filtration ℕ mΩ)
    (hℱ : ∀ n, (ℱ n : MeasurableSpace Ω) =
      ⨆ k, ⨆ (_ : k < n), MeasurableSpace.comap (ξ k) inferInstance) (l : ℕ) :
    eLpNorm (fun ω => (P[(fun ω => F (fun k => ξ k ω)) | ℱ (l + 1)]) ω -
        (P[(fun ω => F (fun k => ξ k ω)) | ℱ l]) ω) 2 P ≤
      eLpNorm (fun ω => F (fun k => ξ k ω) -
        F (Function.update (fun k => ξ k ω) l (ξ' l ω))) 2 P := by
  by_cases htop : eLpNorm (fun ω => F (fun k => ξ k ω) -
      F (Function.update (fun k => ξ k ω) l (ξ' l ω))) 2 P = ⊤
  · rw [htop]; exact le_top
  set f : Ω → ℝ := fun ω => F (fun k => ξ k ω) with hfdef
  set fl : Ω → ℝ := fun ω => F (Function.update (fun k => ξ k ω) l (ξ' l ω)) with hfldef
  have hfl_meas : Measurable fl := by
    refine hF.comp ?_
    exact (measurable_update' (a := l)).comp ((measurable_pi_iff.2 hξ).prodMk (hξ' l))
  have hd : MemLp (fun ω => f ω - fl ω) 2 P :=
    lt_top_iff_ne_top.2 htop
  have hfl2 : MemLp fl 2 P := by
    have := hF2.sub hd
    refine this.ae_eq (Eventually.of_forall fun ω => ?_)
    simp
  have hf1 : Integrable f P := hF2.integrable one_le_two
  have hfl1 : Integrable fl P := hfl2.integrable one_le_two
  have hkey := cov_key ξ ξ' hξ hξ' hlaw hind F hF l hf1 hfl1
  have hsub : P[(fun ω => f ω - fl ω) | ℱ (l + 1)] =ᵐ[P]
      fun ω => (P[f | ℱ (l + 1)]) ω - (P[fl | ℱ (l + 1)]) ω := condExp_sub hf1 hfl1 _
  have hk : P[fl | ℱ (l + 1)] =ᵐ[P] P[f | ℱ l] := by
    rw [hℱ (l + 1)]; rw [hℱ l]; exact hkey
  calc eLpNorm (fun ω => (P[f | ℱ (l + 1)]) ω - (P[f | ℱ l]) ω) 2 P
      = eLpNorm (P[(fun ω => f ω - fl ω) | ℱ (l + 1)]) 2 P := by
        refine eLpNorm_congr_ae ?_
        filter_upwards [hsub, hk] with ω h1 h2
        rw [h1, h2]
    _ ≤ _ := eLpNorm_condExp_le_eLpNorm _ one_le_two

/-- `lem:app-dyn-covariance` (cr-2026-10-23): for square-integrable `F, G` of countably many
independent random coordinates `(ξ_l)_{l}`, with `F^{[l]}, G^{[l]}` obtained by replacing `ξ_l` with an
independent copy `ξ'_l` (same law, jointly independent of all coordinates, `Sum.elim`), the covariance
satisfies `|Cov(F,G)| ≤ ∑_l ‖F − F^{[l]}‖₂ ‖G − G^{[l]}‖₂`. The sum is an `ENNReal` series, so no
summability is assumed. The index is `ℕ` (the source's `l ≥ 1`, relabelled). Generic: `Muon.Foundations`
candidate. Statement verbatim from `section.tex` (ll. 716–723):
```latex
\begin{lemma}[Covariance inequality]\label{lem:app-dyn-covariance}
Let $F,G$ be square-integrable functions of countably many independent
random coordinates $(\xi_l)_{l\ge1}$, and let $F^{[l]}$, $G^{[l]}$ denote $F$,
$G$ with $\xi_l$ replaced by an independent copy. Then
\[
\abs{\Cov(F,G)}\le\sum_{l\ge1}\norm{F-F^{[l]}}_2\,\norm{G-G^{[l]}}_2 .
\]
\end{lemma}
```
-/
theorem lem_app_dyn_covariance {Ω : Type*} [MeasurableSpace Ω] {β : Type*} [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ ξ' : ℕ → Ω → β)
    (hξ : ∀ l, Measurable (ξ l)) (hξ' : ∀ l, Measurable (ξ' l))
    (hlaw : ∀ l, P.map (ξ' l) = P.map (ξ l))
    (hind : iIndepFun (Sum.elim ξ ξ' : ℕ ⊕ ℕ → Ω → β) P)
    (F G : (ℕ → β) → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hF2 : MemLp (fun ω => F (fun l => ξ l ω)) 2 P)
    (hG2 : MemLp (fun ω => G (fun l => ξ l ω)) 2 P) :
    ENNReal.ofReal |covariance (fun ω => F (fun l => ξ l ω)) (fun ω => G (fun l => ξ l ω)) P| ≤
      ∑' l : ℕ,
        eLpNorm (fun ω => F (fun k => ξ k ω) -
            F (Function.update (fun k => ξ k ω) l (ξ' l ω))) 2 P *
        eLpNorm (fun ω => G (fun k => ξ k ω) -
            G (Function.update (fun k => ξ k ω) l (ξ' l ω))) 2 P := by
  let ℱ : Filtration ℕ ‹MeasurableSpace Ω› :=
    { seq := fun n => ⨆ k, ⨆ (_ : k < n), MeasurableSpace.comap (ξ k) inferInstance
      mono' := fun n m h => iSup₂_le fun k hk => le_iSup₂_of_le k (lt_of_lt_of_le hk h) le_rfl
      le' := fun n => iSup₂_le fun k _ => (hξ k).comap_le }
  have hℱ : ∀ n, (ℱ n : MeasurableSpace Ω) =
      ⨆ k, ⨆ (_ : k < n), MeasurableSpace.comap (ξ k) inferInstance := fun n => rfl
  have h0 : (ℱ 0 : MeasurableSpace Ω) = ⊥ := by
    rw [hℱ 0]; simp
  have hX : Measurable[⨆ n, ℱ n] (fun ω (k : ℕ) => ξ k ω) := by
    refine @measurable_pi_iff _ _ _ (⨆ n, ℱ n) _ _ |>.2 fun k => ?_
    exact (comap_measurable (ξ k)).mono (le_iSup_of_le (k + 1)
      (le_iSup₂_of_le k (Nat.lt_succ_self k) le_rfl)) le_rfl
  have hfm : StronglyMeasurable[⨆ n, ℱ n] (fun ω => F (fun k => ξ k ω)) :=
    (hF.comp hX).stronglyMeasurable
  exact cov_main_abstract ℱ h0 hF2 hG2 hfm _ _
    (fun l => cov_step ξ ξ' hξ hξ' hlaw hind F hF hF2 ℱ hℱ l)
    (fun l => cov_step ξ ξ' hξ hξ' hlaw hind G hG hG2 ℱ hℱ l)

end Muon.Dynamics

end

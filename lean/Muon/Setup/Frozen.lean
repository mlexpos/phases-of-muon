import Muon.Foundations.Conventions
import Muon.Foundations.Gaussian
import Muon.Setup.Basic
import Muon.Setup.Weights
import Muon.Setup.RegularizedMap

/-!
# Frozen-state model and its buffer laws (Appendix A)

Source: `sections/01-setup/section.tex`, snapshot `cr-2026-10-23`: `def:app-setup-frozen`
(l.623–651), `lem:app-setup-gaussian-moments` (l.653–676), `lem:app-setup-ema-law`
(l.735–758, with the proof's `eqn:app-setup-orthogonality` and `eqn:app-setup-lag-decomposition`),
`prop:app-setup-startup` (l.815–834). Consumers: B, C, D, E.

Conventions of this file:
* Samples are indexed by time `s : ℤ` and by batch slot `a : Fin B` (the paper's `a = 1,…,B`,
  0-based). The age-`j` sample of `M_t` is the sample of time `t+1-j`.
* The paper's `\Gt` is `G_{t+1}`, so it is `frozenBatchG F S (t+1)`.
* Names: `frozenBatchG`, `frozenBuf`, `frozenUpd` are the paper's `G_s`, `M_t`, `Q_ϱ(M_t)`. They
  are distinct from the algorithm's normalized `G°`, `M°` (card §6.7).
* `A` ranges over all real matrices with `‖A‖_F = 1`; the paper's `Ahat(Δ_t)` is one instance.
* `tsum` is junk off the summable set. The a.s. summability is `lem_app_setup_ema_law_i`.
* Covariances of matrices are `covT` (Conventions); cross-covariances are `crossCovT`.
-/

noncomputable section

open scoped Matrix MatrixOrder
open MeasureTheory ProbabilityTheory Filter Topology
open Muon

namespace Muon.Setup

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}

/-! ## Norms, parameters and samples -/

/-- Euclidean norm `‖z‖` of a vector, as used in `lem:app-setup-ema-law`(i). -/
def eucNorm {k : ℕ} (z : Vec k) : ℝ :=
  Real.sqrt (∑ i, z i ^ 2)

/-- Parameters of the frozen-state model (`def:app-setup-frozen`): the covariances `C`, the
deterministic normalized state `A` (`Ahat`, with `‖A‖_F = 1`), the momentum `β ∈ [0,1)` and the
batch size `B > 0`. -/
structure FrozenParams (m n B : ℕ) where
  C : Covariances m n
  A : Mat m n
  hA : fro A = 1
  β : ℝ
  hβ : 0 ≤ β ∧ β < 1
  hB : 0 < B

/-- Independent standard Gaussian pairs `(z_{sa}, w_{sa})`, `s ∈ ℤ`, `a ≤ B`, on `(Ω, P)`
(`def:app-setup-frozen`, time-indexed form). Each pair has law `N(0,I_m) ⊗ N(0,I_n)`, and the
family over `(s, a)` is independent. -/
structure FrozenSamples {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (m n B : ℕ) where
  zw : ℤ → Fin B → Ω → Vec m × Vec n
  meas : ∀ s a, Measurable (zw s a)
  indep : iIndepFun (fun p : ℤ × Fin B => zw p.1 p.2) P
  law : ∀ s a,
    P.map (zw s a) = (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)

/-! ## The frozen objects -/

/-- Frozen batch `G_s = (1/B) ∑_a d_{sa} Σ_out^{1/2} (z_{sa} ⊗ w_{sa}) Σ_in^{1/2}` with
`d_{sa} = z_{sa}ᵀ A w_{sa}` (`def:app-setup-frozen`, time-indexed form). -/
def frozenBatchG (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) (ω : Ω) :
    Mat m n :=
  ((B : ℝ))⁻¹ • ∑ a : Fin B,
    (dotProduct (S.zw s a ω).1 (Matrix.mulVec F.A (S.zw s a ω).2)) •
      (rOut F.C * outer (S.zw s a ω).1 (S.zw s a ω).2 * rIn F.C)

/-- Frozen buffer `M_t = ∑_{j ≥ 0} w_j G_{t+1-j}`, `w_j = emaW β j` (`def:app-setup-frozen`).
The series is `tsum`; its a.s. absolute convergence is `lem_app_setup_ema_law_i`. -/
def frozenBuf (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (ω : Ω) : Mat m n :=
  ∑' j : ℕ, emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω

/-- Frozen update `S_t(ϱ) = Q_ϱ(M_t)` (`def:app-setup-frozen`: the update applied at step `t`
is `G̃ := Q_ϱ(M_t)`). -/
def frozenUpd (F : FrozenParams m n B) (S : FrozenSamples P m n B) (ϱ : ℝ) (t : ℤ) (ω : Ω) :
    Mat m n :=
  Q ϱ (frozenBuf F S t ω)

/-- `def:app-setup-frozen`, snapshot `cr-2026-10-23`. Declaration of record: the frozen-state model
at time `t` with ridge `ϱ`, i.e. the normalized buffer `M_t` together with the update
`G̃ = Q_ϱ(M_t)`. The definition, verbatim from `section.tex` (l.623–651):
```latex
\begin{definition}[Frozen-state model]\label{def:app-setup-frozen}
Assume \cref{assum:data-target}. Fix $t$, condition on $\cF_t$, and assume
$\cR(t)>0$, so that $\Dt$ and $\Ahat$ are deterministic. Let
$(z_{ja},w_{ja})$, $j\ge0$, $1\le a\le B$, be independent standard Gaussian
vectors in $\R^{\Nout}\times\R^{\Nin}$, and put
\begin{equation}\label{eqn:app-setup-frozen-objects}
\begin{gathered}
d_{ja}\defeq z_{ja}^\T\Ahat w_{ja},\qquad
G_{t+1-j}\defeq\frac1B\sum_{a=1}^Bd_{ja}\,\Sigmaout^{1/2}(z_{ja}\tensor w_{ja})\Sigmain^{1/2},\\
\Mt\defeq\sum_{j\ge0}\emaw{j}\,G_{t+1-j}.
\end{gathered}
\end{equation}
The frozen-state model is the model in which the normalized buffer at time
$t$ is $\Mt$ and the update applied at step $t$ is $\Gtilde\defeq\Qridge{\ridge}(\Mt)$.
\end{definition}
```
-/
def def_app_setup_frozen (F : FrozenParams m n B) (S : FrozenSamples P m n B) (ϱ : ℝ) (t : ℤ) :
    (Ω → Mat m n) × (Ω → Mat m n) :=
  (frozenBuf F S t, frozenUpd F S ϱ t)

/-- Single-sample matrix `X = (zᵀ A w) (z ⊗ w)` (`lem:app-setup-gaussian-moments`(a)). -/
def sampleX {m n : ℕ} (A : Mat m n) (z : Vec m) (w : Vec n) : Mat m n :=
  dotProduct z (Matrix.mulVec A w) • outer z w

/-- Right-hand side of `eqn:app-setup-tensor`: the covariance tensor of `sampleX A` for
`‖A‖_F = 1`. -/
def sampleTensor {m n : ℕ} (A : Mat m n) : Fin m → Fin n → Fin m → Fin n → ℝ :=
  fun i j k l =>
    (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
      + 2 * (A * Aᵀ) i k * (if j = l then (1 : ℝ) else 0)
      + 2 * (if i = k then (1 : ℝ) else 0) * (Aᵀ * A) j l
      + A i j * A k l + 2 * A i l * A k j

/-- Cross-covariance tensor `Cov(X_{ij}, Y_{kl})` of two random matrices. `covT P X` is
`crossCovT P X X`. -/
def crossCovT {m n : ℕ} (P : Measure Ω) (X Y : Ω → Mat m n) :
    Fin m → Fin n → Fin m → Fin n → ℝ :=
  fun i j k l => covariance (fun ω => X ω i j) (fun ω => Y ω k l) P

/-- The batch covariance tensor `Σ_G = Cov(vec G_t)` (`lem:app-setup-ema-law`), taken at
time `0`; by `lem_app_setup_gaussian_moments_iii` the batches are identically distributed. -/
def SigmaG (S : FrozenSamples P m n B) (F : FrozenParams m n B) :
    Fin m → Fin n → Fin m → Fin n → ℝ :=
  covT P (frozenBatchG F S 0)

/-- Single-batch Frobenius variance `V_B = E‖G_t − E G_t‖_F²` (`eqn:app-setup-VB`), taken at
time `0`. -/
def frozenVB (S : FrozenSamples P m n B) (F : FrozenParams m n B) : ℝ :=
  ∫ ω, (fro (frozenBatchG F S 0 ω - mean P (frozenBatchG F S 0))) ^ 2 ∂P

/-- Partial sum `∑_{t=1}^T vec(M_t − E G_t)` of `lem:app-setup-ema-law`(v), as a random matrix. -/
def blockSum (S : FrozenSamples P m n B) (F : FrozenParams m n B) (T : ℕ) : Ω → Mat m n :=
  fun ω => ∑ t ∈ Finset.Icc (1 : ℤ) (T : ℤ),
    (frozenBuf F S t ω - mean P (frozenBatchG F S (t + 1)))

/-- Strict stationarity of a `ℤ`-indexed family of random matrices: the law of the whole path
`(X_{t+k})_{t ∈ ℤ}` equals the law of `(X_t)_{t ∈ ℤ}` for every shift `k`. -/
def StrictlyStationary {E : Type*} [MeasurableSpace E] (P : Measure Ω) (X : ℤ → Ω → E) :
    Prop :=
  AEMeasurable (fun ω t => X t ω) P ∧
    ∀ k : ℤ, P.map (fun ω t => X (t + k) ω) = P.map (fun ω t => X t ω)

/-- Non-vacuity of the frozen model: there are samples on the infinite product of standard
Gaussian pairs (`Measure.infinitePi`). -/
theorem frozenSamples_nonempty (m n B : ℕ) :
    Nonempty (FrozenSamples (Measure.infinitePi fun _ : ℤ × Fin B =>
      (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) m n B) := by
  refine ⟨{
    zw := fun s a ω => ω (s, a)
    meas := fun s a => measurable_pi_apply (s, a)
    indep := ?_
    law := ?_ }⟩
  · exact iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  · intro s a
    exact Measure.infinitePi_map_eval _ (s, a)

/-! ## Gaussian covariance of a batch -/

/-! ### Private helpers for the Gaussian batch moments -/

private lemma gm_coord_pow_integrable (n : ℕ) (i : Fin n) (k : ℕ) :
    Integrable (fun z : Fin n → ℝ => z i ^ k) (Muon.Foundations.stdGaussianPi n) := by
  have hm : MeasurePreserving (fun z : Fin n → ℝ => z i) (Muon.Foundations.stdGaussianPi n)
      (gaussianReal 0 1) := measurePreserving_eval _ i
  exact (hm.integrable_comp (g := fun x : ℝ => x ^ k) (by fun_prop)).2
    (Muon.Foundations.gaussian_integrable_pow k)

private lemma gm_two_integrable (n : ℕ) (a i : Fin n) :
    Integrable (fun z : Fin n → ℝ => z a * z i) (Muon.Foundations.stdGaussianPi n) := by
  refine ((((gm_coord_pow_integrable n a 2).add (gm_coord_pow_integrable n i 2)).div_const 2)).mono'
    (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun z => ?_)
  show ‖z a * z i‖ ≤ (z a ^ 2 + z i ^ 2) / 2
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|z a| - |z i|), sq_abs (z a), sq_abs (z i)]

private lemma gm_two_integral (n : ℕ) (a i : Fin n) :
    ∫ z : Fin n → ℝ, z a * z i ∂(Muon.Foundations.stdGaussianPi n) = if i = a then 1 else 0 := by
  by_cases hia : i = a
  · subst hia
    rw [if_pos rfl]
    have h := integral_map (μ := Muon.Foundations.stdGaussianPi n)
      (φ := fun z : Fin n → ℝ => z i) (f := fun x : ℝ => x ^ 2)
      (measurable_pi_apply i).aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))
    rw [Muon.Foundations.stdGaussianPi_map_coord, Muon.Foundations.gaussian_moment_two] at h
    simp only [← pow_two]
    exact h.symm
  · rw [if_neg hia]
    unfold Muon.Foundations.stdGaussianPi
    have hprod : ∀ z : Fin n → ℝ,
        ∏ k, (if k = a ∨ k = i then z k else 1) = z a * z i := by
      intro z
      exact (Finset.prod_eq_mul (f := fun k => if k = a ∨ k = i then z k else 1) a i
        (fun h => hia h.symm)
        (fun c _ hc => by simp [hc.1, hc.2])
        (fun h => absurd (Finset.mem_univ a) h) (fun h => absurd (Finset.mem_univ i) h)).trans
        (by simp)
    have hfun : (fun z : Fin n → ℝ => z a * z i)
        = fun z : Fin n → ℝ => ∏ k, (fun (k : Fin n) (x : ℝ) =>
            if k = a ∨ k = i then x else 1) k (z k) := by
      funext z
      change z a * z i = ∏ k, (if k = a ∨ k = i then z k else 1)
      rw [hprod z]
    have hint : ∀ k : Fin n, ∫ x, (if k = a ∨ k = i then x else 1) ∂(gaussianReal 0 1)
        = if k = a ∨ k = i then 0 else 1 := by
      intro k
      split_ifs
      · simpa using Muon.Foundations.gaussian_moment_odd 0
      · simp
    have h0 : ∏ k : Fin n, (if k = a ∨ k = i then (0 : ℝ) else 1) = 0 :=
      Finset.prod_eq_zero (f := fun k : Fin n => if k = a ∨ k = i then (0 : ℝ) else 1)
        (Finset.mem_univ a) (by simp)
    rw [hfun, integral_fintype_prod_eq_prod
      (f := fun (k : Fin n) (x : ℝ) => if k = a ∨ k = i then x else 1)]
    change ∏ k, ∫ x, (if k = a ∨ k = i then x else 1) ∂(gaussianReal 0 1) = _
    rw [Finset.prod_congr rfl (fun k _ => hint k), h0]

private lemma gm_four_eq_prod (n : ℕ) (i j k l : Fin n) (z : Fin n → ℝ) :
    z i * z j * z k * z l = ∏ c, z c ^ ((if c = i then 1 else 0) + (if c = j then 1 else 0)
      + (if c = k then 1 else 0) + (if c = l then 1 else 0)) := by
  simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
    Finset.prod_ite_eq', Finset.mem_univ, if_true]

private lemma gm_four_integrable (n : ℕ) (i j k l : Fin n) :
    Integrable (fun z : Fin n → ℝ => z i * z j * z k * z l)
      (Muon.Foundations.stdGaussianPi n) := by
  simp_rw [gm_four_eq_prod]
  unfold Muon.Foundations.stdGaussianPi
  exact Integrable.fintype_prod (f := fun (c : Fin n) (x : ℝ) => x ^ ((if c = i then 1 else 0)
    + (if c = j then 1 else 0) + (if c = k then 1 else 0) + (if c = l then 1 else 0)))
    (fun c => Muon.Foundations.gaussian_integrable_pow _)

private lemma gm_four_integral (n : ℕ) (i j k l : Fin n) :
    ∫ z : Fin n → ℝ, z i * z j * z k * z l ∂(Muon.Foundations.stdGaussianPi n)
      = (if i = j then 1 else 0) * (if k = l then 1 else 0)
        + (if i = k then 1 else 0) * (if j = l then 1 else 0)
        + (if i = l then 1 else 0) * (if j = k then 1 else 0) := by
  simp_rw [gm_four_eq_prod]
  unfold Muon.Foundations.stdGaussianPi
  rw [integral_fintype_prod_eq_prod (f := fun (c : Fin n) (x : ℝ) => x ^ ((if c = i then 1 else 0)
    + (if c = j then 1 else 0) + (if c = k then 1 else 0) + (if c = l then 1 else 0)))]
  have m0 : ∫ x : ℝ, x ^ 0 ∂(gaussianReal 0 1) = 1 := by simp
  have m1 : ∫ x : ℝ, x ^ 1 ∂(gaussianReal 0 1) = 0 := by
    simpa using Muon.Foundations.gaussian_moment_odd 0
  have m2 : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := Muon.Foundations.gaussian_moment_two
  have m3 : ∫ x : ℝ, x ^ 3 ∂(gaussianReal 0 1) = 0 := by
    simpa using Muon.Foundations.gaussian_moment_odd 1
  have m4 : ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1) = 3 := Muon.Foundations.gaussian_moment_four
  by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hil : i = l <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkl : k = l <;>
    first
    | (exfalso; simp_all; done)
    | skip
  all_goals subst_vars
  all_goals have key : ∀ {a b : Fin n}, ¬ a = b → (b = a) = False := fun h => by simp [eq_comm, h]
  all_goals first
    | (refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).trans ?_
       · simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_zero (Finset.mem_univ j) ?_).trans ?_
       · simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_zero (Finset.mem_univ k) ?_).trans ?_
       · simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_zero (Finset.mem_univ l) ?_).trans ?_
       · simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_one fun c _ => ?_).trans ?_
       · split_ifs <;> simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_single_of_mem i (Finset.mem_univ _) (fun c _ hc => ?_)).trans ?_
       · split_ifs <;> simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_single_of_mem j (Finset.mem_univ _) (fun c _ hc => ?_)).trans ?_
       · split_ifs <;> simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_single_of_mem k (Finset.mem_univ _) (fun c _ hc => ?_)).trans ?_
       · split_ifs <;> simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_single_of_mem l (Finset.mem_univ _) (fun c _ hc => ?_)).trans ?_
       · split_ifs <;> simp_all [key]
       · simp_all)
    | skip
  all_goals
    refine (Finset.prod_eq_single_of_mem l (Finset.mem_univ _) (fun c _ hc => ?_)).trans ?_
  · simp [hc, m0]
  · norm_num [m4]

/-- A pushforward equal to a product Gaussian law forces measurability of `(Z, W)`: otherwise
the pushforward is a Dirac mass, which has no second moment matching the Gaussian ones. -/
private lemma gm_aemeas {m n : ℕ} {Z : Ω → Vec m} {W : Ω → Vec n} [IsProbabilityMeasure P]
    (hZW : P.map (fun ω => (Z ω, W ω)) = (Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)) :
    AEMeasurable (fun ω => (Z ω, W ω)) P := by
  by_contra h
  have hd := Measure.map_of_not_aemeasurable_of_ne_zero h (IsProbabilityMeasure.ne_zero P)
  rw [hZW] at hd
  obtain ⟨c, hc⟩ : ∃ c : Vec m × Vec n, (Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n) = Measure.dirac c := ⟨_, hd⟩
  have hfst : ∫ p : Vec m × Vec n, (∑ i, p.1 i ^ 2)
      ∂((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
      = (m : ℝ) := by
    rw [integral_fun_fst (fun x : Vec m => ∑ i, x i ^ 2), probReal_univ, one_smul]
    have h1 := Muon.Foundations.stdGaussianPi_sq_norm_moment m 1 le_rfl
    simpa using h1
  have hfst2 : ∫ p : Vec m × Vec n, (∑ i, p.1 i ^ 2) ^ 2
      ∂((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
      = (m : ℝ) * ((m : ℝ) + 2) := by
    rw [integral_fun_fst (fun x : Vec m => (∑ i, x i ^ 2) ^ 2), probReal_univ, one_smul]
    have h2 := Muon.Foundations.stdGaussianPi_sq_norm_moment m 2 (by norm_num)
    norm_num [Finset.prod_range_succ] at h2
    rw [h2]
  have hsnd : ∫ p : Vec m × Vec n, (∑ i, p.2 i ^ 2)
      ∂((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
      = (n : ℝ) := by
    rw [integral_fun_snd (fun x : Vec n => ∑ i, x i ^ 2), probReal_univ, one_smul]
    have h1 := Muon.Foundations.stdGaussianPi_sq_norm_moment n 1 le_rfl
    simpa using h1
  have hsnd2 : ∫ p : Vec m × Vec n, (∑ i, p.2 i ^ 2) ^ 2
      ∂((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
      = (n : ℝ) * ((n : ℝ) + 2) := by
    rw [integral_fun_snd (fun x : Vec n => (∑ i, x i ^ 2) ^ 2), probReal_univ, one_smul]
    have h2 := Muon.Foundations.stdGaussianPi_sq_norm_moment n 2 (by norm_num)
    norm_num [Finset.prod_range_succ] at h2
    rw [h2]
  rw [hc, integral_dirac] at hfst hfst2 hsnd hsnd2
  have hm : (m : ℝ) = 0 := by
    have e1 : (m : ℝ) = (∑ i, c.1 i ^ 2) := hfst.symm.trans rfl
    have e2 : (m : ℝ) * ((m : ℝ) + 2) = (∑ i, c.1 i ^ 2) ^ 2 := hfst2.symm
    nlinarith
  have hn : (n : ℝ) = 0 := by
    have e1 : (n : ℝ) = (∑ i, c.2 i ^ 2) := hsnd.symm
    have e2 : (n : ℝ) * ((n : ℝ) + 2) = (∑ i, c.2 i ^ 2) ^ 2 := hsnd2.symm
    nlinarith
  have hm0 : m = 0 := by exact_mod_cast hm
  have hn0 : n = 0 := by exact_mod_cast hn
  subst hm0 hn0
  exact h aemeasurable_of_subsingleton_codomain

/-- Law of `(Z, W)` pushes forward integrals to the product law. -/
private lemma gm_transport {m n : ℕ} {Z : Ω → Vec m} {W : Ω → Vec n} [IsProbabilityMeasure P]
    (hZW : P.map (fun ω => (Z ω, W ω)) = (Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n))
    (g : Vec m × Vec n → ℝ) (hg : Measurable g) :
    ∫ ω, g (Z ω, W ω) ∂P = ∫ p, g p ∂((Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)) := by
  have hae : AEMeasurable (fun ω => (Z ω, W ω)) P := gm_aemeas hZW
  have := integral_map (μ := P) hae (f := g) (by rw [hZW]; exact hg.aestronglyMeasurable)
  rw [hZW] at this
  exact this.symm

private lemma gm_sample_entry {m n : ℕ} (A : Mat m n) (z : Vec m) (w : Vec n) (i : Fin m)
    (j : Fin n) :
    sampleX A z w i j = ∑ a, ∑ b, A a b * ((z a * z i) * (w b * w j)) := by
  simp only [sampleX, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, dotProduct,
    Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private lemma gm_sample_prod {m n : ℕ} (A : Mat m n) (z : Vec m) (w : Vec n) (i : Fin m)
    (j : Fin n) (k : Fin m) (l : Fin n) :
    sampleX A z w i j * sampleX A z w k l
      = ∑ a, ∑ b, ∑ c, ∑ d, (A a b * A c d) *
          ((z a * z i * z c * z k) * (w b * w j * w d * w l)) := by
  rw [gm_sample_entry, gm_sample_entry]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

private lemma gm_mean_rho {m n : ℕ} (A : Mat m n) (i : Fin m) (j : Fin n) :
    ∫ p : Vec m × Vec n, sampleX A p.1 p.2 i j
      ∂((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) = A i j := by
  have hsum : ∑ a : Fin m, ∑ b : Fin n,
      A a b * ((if i = a then (1 : ℝ) else 0) * (if j = b then (1 : ℝ) else 0)) = A i j := by
    simp [mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  rw [← hsum]
  simp only [gm_sample_entry]
  rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
    ((gm_two_integrable m a i).mul_prod (gm_two_integrable n b j)).const_mul (A a b)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finset_sum _ fun b _ => ((gm_two_integrable m a i).mul_prod
    (gm_two_integrable n b j)).const_mul (A a b)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, integral_prod_mul (fun x : Vec m => x a * x i)
    (fun y : Vec n => y b * y j), gm_two_integral, gm_two_integral]

private lemma gm_centered {m n : ℕ} {F G : Vec m × Vec n → ℝ} {a b : ℝ}
    {ρ : Measure (Vec m × Vec n)} [IsProbabilityMeasure ρ]
    (hF : Integrable F ρ) (hG : Integrable G ρ) (hFG : Integrable (fun p => F p * G p) ρ)
    (hFm : ∫ p, F p ∂ρ = a) (hGm : ∫ p, G p ∂ρ = b) :
    ∫ p, (F p - a) * (G p - b) ∂ρ = ∫ p, F p * G p ∂ρ - a * b := by
  have e : ∀ p, (F p - a) * (G p - b) = (F p * G p - b * F p) - a * G p + a * b :=
    fun p => by ring
  simp_rw [e]
  have i1 : Integrable (fun p => F p * G p - b * F p) ρ := hFG.sub (hF.const_mul b)
  have i2 : Integrable (fun p => F p * G p - b * F p - a * G p) ρ := i1.sub (hG.const_mul a)
  rw [integral_add i2 (integrable_const _), integral_sub i1 (hG.const_mul a),
    integral_sub hFG (hF.const_mul b), integral_const_mul, integral_const_mul, hFm, hGm]
  simp only [integral_const, probReal_univ, one_smul]
  ring

private lemma gm_tensor_alg {m n : ℕ} (A : Mat m n) (hA : fro A = 1) (i : Fin m) (j : Fin n)
    (k : Fin m) (l : Fin n) :
    ∑ a : Fin m, ∑ b : Fin n, ∑ c : Fin m, ∑ d : Fin n, (A a b * A c d) *
        (((if a = i then (1 : ℝ) else 0) * (if c = k then (1 : ℝ) else 0)
          + (if a = c then (1 : ℝ) else 0) * (if i = k then (1 : ℝ) else 0)
          + (if a = k then (1 : ℝ) else 0) * (if i = c then (1 : ℝ) else 0)) *
         ((if b = j then (1 : ℝ) else 0) * (if d = l then (1 : ℝ) else 0)
          + (if b = d then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          + (if b = l then (1 : ℝ) else 0) * (if j = d then (1 : ℝ) else 0)))
      - A i j * A k l = sampleTensor A i j k l := by
  have hsq : ∑ a, ∑ b, A a b * A a b = 1 := by
    unfold fro at hA
    rw [Real.sqrt_eq_one] at hA
    simpa [Real.norm_eq_abs, sq_abs, sq] using hA
  simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, one_mul,
    mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero, ite_and]
  have hc1 : ∑ x : Fin n, A k x * A i x = ∑ x : Fin n, A i x * A k x :=
    Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hc3 : ∑ x : Fin m, A x l * A x j = ∑ x : Fin m, A x j * A x l :=
    Finset.sum_congr rfl fun x _ => mul_comm _ _
  simp only [sampleTensor, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [hsq, hc1, hc3]
  split_ifs <;> ring

private lemma gm_mean_entry {m n : ℕ} {Z : Ω → Vec m} {W : Ω → Vec n} [IsProbabilityMeasure P]
    (hZW : P.map (fun ω => (Z ω, W ω)) = (Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)) (A : Mat m n) (i : Fin m) (j : Fin n) :
    ∫ ω, sampleX A (Z ω) (W ω) i j ∂P = A i j := by
  have hmeas : Measurable (fun p : Vec m × Vec n => sampleX A p.1 p.2 i j) := by
    simp only [gm_sample_entry]; fun_prop
  have key := gm_transport hZW (fun p : Vec m × Vec n => sampleX A p.1 p.2 i j) hmeas
  try dsimp only at key
  rw [key]
  exact gm_mean_rho A i j

private lemma gm_term_integrable {m n : ℕ} (A : Mat m n) (i : Fin m) (j : Fin n) (k : Fin m)
    (l : Fin n) (a c : Fin m) (b d : Fin n) :
    Integrable (fun p : Vec m × Vec n => (A a b * A c d) *
        ((p.1 a * p.1 i * p.1 c * p.1 k) * (p.2 b * p.2 j * p.2 d * p.2 l)))
      ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) :=
  ((gm_four_integrable m a i c k).mul_prod (gm_four_integrable n b j d l)).const_mul _


/-- `lem:app-setup-gaussian-moments`(i): mean of one sample, `E X = A`.
Declaration of record of part (i). The full environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Gaussian covariance of a batch]\label{lem:app-setup-gaussian-moments}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic with $\norm A_\F=1$, let
$z\sim\mathcal N(0,\Id_{\Nout})$ and $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent, and let $X\defeq(z^\T Aw)\,z\tensor w$. Then $\EE X=A$, and its
covariance tensor $\mathcal C_{ij,kl}\defeq\Cov(X_{ij},X_{kl})$ is
\begin{equation}\label{eqn:app-setup-tensor}
\mathcal C_{ij,kl}=\delta_{ik}\delta_{jl}+2(AA^\T)_{ik}\delta_{jl}+2\delta_{ik}(A^\T A)_{jl}+A_{ij}A_{kl}+2A_{il}A_{kj}.
\end{equation}
Consequently, in the frozen-state model with $A=\Ahat$, the batches
$G_{t+1-j}$ are independent and identically distributed,
\begin{equation}\label{eqn:app-setup-batch-cov}
\begin{gathered}
\EE\Gt=\Sigmaout^{1/2}\Ahat\Sigmain^{1/2},\\
\Cov\big((\Gt)_{ij},(\Gt)_{kl}\big)=\frac1B\sum_{p,q,r,s}(\Sigmaout^{1/2})_{ip}(\Sigmain^{1/2})_{jq}\,\mathcal C_{pq,rs}\,(\Sigmaout^{1/2})_{kr}(\Sigmain^{1/2})_{ls},
\end{gathered}
\end{equation}
and the single-batch Frobenius variance is
\begin{equation}\label{eqn:app-setup-VB}
\begin{aligned}
\mathsf V_B&\defeq\EE\norm{\Gt-\EE\Gt}_\F^2\\
&=\frac1B\Big\{\Tr\Sigmaout\Tr\Sigmain+2\Tr(\Sigmaout\Ahat\Ahat^\T)\Tr\Sigmain+2\Tr\Sigmaout\Tr(\Sigmain\Ahat^\T\Ahat)+3\norm{\EE\Gt}_\F^2\Big\}.
\end{aligned}
\end{equation}
\end{lemma}
```
-/
theorem lem_app_setup_gaussian_moments_i [IsProbabilityMeasure P] {Z : Ω → Vec m} {W : Ω → Vec n}
    (hZW : P.map (fun ω => (Z ω, W ω)) = (Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n))
    (A : Mat m n) (hA : fro A = 1) :
    mean P (fun ω => sampleX A (Z ω) (W ω)) = A := by
  ext i j
  simp only [mean, Matrix.of_apply]
  exact gm_mean_entry hZW A i j

/-- `lem:app-setup-gaussian-moments`(ii): covariance tensor of one sample, `eqn:app-setup-tensor`.
Declaration of record of part (ii). The full environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Gaussian covariance of a batch]\label{lem:app-setup-gaussian-moments}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic with $\norm A_\F=1$, let
$z\sim\mathcal N(0,\Id_{\Nout})$ and $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent, and let $X\defeq(z^\T Aw)\,z\tensor w$. Then $\EE X=A$, and its
covariance tensor $\mathcal C_{ij,kl}\defeq\Cov(X_{ij},X_{kl})$ is
\begin{equation}\label{eqn:app-setup-tensor}
\mathcal C_{ij,kl}=\delta_{ik}\delta_{jl}+2(AA^\T)_{ik}\delta_{jl}+2\delta_{ik}(A^\T A)_{jl}+A_{ij}A_{kl}+2A_{il}A_{kj}.
\end{equation}
Consequently, in the frozen-state model with $A=\Ahat$, the batches
$G_{t+1-j}$ are independent and identically distributed,
\begin{equation}\label{eqn:app-setup-batch-cov}
\begin{gathered}
\EE\Gt=\Sigmaout^{1/2}\Ahat\Sigmain^{1/2},\\
\Cov\big((\Gt)_{ij},(\Gt)_{kl}\big)=\frac1B\sum_{p,q,r,s}(\Sigmaout^{1/2})_{ip}(\Sigmain^{1/2})_{jq}\,\mathcal C_{pq,rs}\,(\Sigmaout^{1/2})_{kr}(\Sigmain^{1/2})_{ls},
\end{gathered}
\end{equation}
and the single-batch Frobenius variance is
\begin{equation}\label{eqn:app-setup-VB}
\begin{aligned}
\mathsf V_B&\defeq\EE\norm{\Gt-\EE\Gt}_\F^2\\
&=\frac1B\Big\{\Tr\Sigmaout\Tr\Sigmain+2\Tr(\Sigmaout\Ahat\Ahat^\T)\Tr\Sigmain+2\Tr\Sigmaout\Tr(\Sigmain\Ahat^\T\Ahat)+3\norm{\EE\Gt}_\F^2\Big\}.
\end{aligned}
\end{equation}
\end{lemma}
```
-/
theorem lem_app_setup_gaussian_moments_ii [IsProbabilityMeasure P] {Z : Ω → Vec m}
    {W : Ω → Vec n}
    (hZW : P.map (fun ω => (Z ω, W ω)) = (Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n))
    (A : Mat m n) (hA : fro A = 1) :
    covT P (fun ω => sampleX A (Z ω) (W ω)) = sampleTensor A := by
  funext i j k l
  simp only [covT, covariance]
  rw [gm_mean_entry hZW A i j, gm_mean_entry hZW A k l]
  have hF : Integrable (fun p : Vec m × Vec n => sampleX A p.1 p.2 i j)
      ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) := by
    simp only [gm_sample_entry]
    exact integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
      ((gm_two_integrable m a i).mul_prod (gm_two_integrable n b j)).const_mul (A a b)
  have hG : Integrable (fun p : Vec m × Vec n => sampleX A p.1 p.2 k l)
      ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) := by
    simp only [gm_sample_entry]
    exact integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
      ((gm_two_integrable m a k).mul_prod (gm_two_integrable n b l)).const_mul (A a b)
  have hFG : Integrable (fun p : Vec m × Vec n => sampleX A p.1 p.2 i j * sampleX A p.1 p.2 k l)
      ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) := by
    simp only [gm_sample_prod]
    exact integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
      integrable_finset_sum _ fun c _ => integrable_finset_sum _ fun d _ =>
        gm_term_integrable A i j k l a c b d
  have hS4 : ∫ p : Vec m × Vec n, sampleX A p.1 p.2 i j * sampleX A p.1 p.2 k l
      ∂((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
      = ∑ a : Fin m, ∑ b : Fin n, ∑ c : Fin m, ∑ d : Fin n, (A a b * A c d) *
        (((if a = i then (1 : ℝ) else 0) * (if c = k then (1 : ℝ) else 0)
          + (if a = c then (1 : ℝ) else 0) * (if i = k then (1 : ℝ) else 0)
          + (if a = k then (1 : ℝ) else 0) * (if i = c then (1 : ℝ) else 0)) *
         ((if b = j then (1 : ℝ) else 0) * (if d = l then (1 : ℝ) else 0)
          + (if b = d then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          + (if b = l then (1 : ℝ) else 0) * (if j = d then (1 : ℝ) else 0))) := by
    simp only [gm_sample_prod]
    rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
      integrable_finset_sum _ fun c _ => integrable_finset_sum _ fun d _ =>
        gm_term_integrable A i j k l a c b d]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ fun b _ => integrable_finset_sum _ fun c _ =>
      integrable_finset_sum _ fun d _ => gm_term_integrable A i j k l a c b d]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finset_sum _ fun c _ => integrable_finset_sum _ fun d _ =>
      gm_term_integrable A i j k l a c b d]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finset_sum _ fun d _ => gm_term_integrable A i j k l a c b d]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [integral_const_mul, integral_prod_mul (fun x : Vec m => x a * x i * x c * x k)
      (fun y : Vec n => y b * y j * y d * y l), gm_four_integral, gm_four_integral]
  have hmeas : Measurable (fun p : Vec m × Vec n =>
      (sampleX A p.1 p.2 i j - A i j) * (sampleX A p.1 p.2 k l - A k l)) := by
    simp only [gm_sample_entry]; fun_prop
  have key := gm_transport hZW (fun p : Vec m × Vec n =>
    (sampleX A p.1 p.2 i j - A i j) * (sampleX A p.1 p.2 k l - A k l)) hmeas
  try dsimp only at key
  rw [key]
  refine (gm_centered hF hG hFG (gm_mean_rho A i j) (gm_mean_rho A k l)).trans ?_
  beta_reduce
  rw [hS4]
  exact gm_tensor_alg A hA i j k l

/-! ### Batch-level helpers for part (iv) -/

private lemma gm_pair_law {m n : ℕ} (S : FrozenSamples P m n B) (s : ℤ) (a : Fin B) :
    P.map (fun ω => ((S.zw s a ω).1, (S.zw s a ω).2)) = (Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n) :=
  S.law s a

private lemma gm_is_prob {m n : ℕ} (S : FrozenSamples P m n B) (s : ℤ) (a : Fin B) :
    IsProbabilityMeasure P := by
  have h1 : (P.map (S.zw s a)) Set.univ = 1 := by
    rw [S.law s a]; exact measure_univ
  rw [Measure.map_apply (S.meas s a) MeasurableSet.univ] at h1
  exact ⟨by simpa using h1⟩

private lemma gm_rIn_comm {n : ℕ} {m : ℕ} (C : Covariances m n) (x y : Fin n) :
    rIn C x y = rIn C y x := by
  have h : IsSelfAdjoint (rIn C) := by
    unfold rIn
    rw [CFC.sqrt_eq_real_sqrt _ C.psdIn.nonneg, cfcₙ_eq_cfc]
    exact IsSelfAdjoint.cfc
  have h2 : (rIn C)ᵀ = rIn C := by
    simpa [IsSelfAdjoint, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using h
  simpa [Matrix.transpose_apply] using congrFun (congrFun h2 y) x

private lemma gm_sample_meas {m n : ℕ} (A : Mat m n) (i : Fin m) (j : Fin n) :
    Measurable (fun p : Vec m × Vec n => sampleX A p.1 p.2 i j) := by
  simp only [gm_sample_entry]; fun_prop

/-- Entries of one sample are in `L²` under any Gaussian-pair representation. -/
private lemma gm_memLp_sample [IsProbabilityMeasure P] {Z : Ω → Vec m} {W : Ω → Vec n}
    (hZW : P.map (fun ω => (Z ω, W ω)) = (Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)) (A : Mat m n) (i : Fin m) (j : Fin n) :
    MemLp (fun ω => sampleX A (Z ω) (W ω) i j) 2 P := by
  have hfun : MemLp (fun p : Vec m × Vec n => sampleX A p.1 p.2 i j) 2
      ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) := by
    rw [memLp_two_iff_integrable_sq (gm_sample_meas A i j).aestronglyMeasurable]
    simp only [pow_two]
    simp only [gm_sample_prod]
    exact integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
      integrable_finset_sum _ fun c _ => integrable_finset_sum _ fun d _ =>
        gm_term_integrable A i j i j a c b d
  rw [← hZW] at hfun
  exact (memLp_map_measure_iff (gm_sample_meas A i j).aestronglyMeasurable
    (gm_aemeas hZW)).1 hfun

private lemma gm_lr_apply {m n p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ) (X : Mat m n) (i : Fin p) (j : Fin q) :
    (L * X * R) i j = ∑ y : Fin m, ∑ x : Fin n, (L i y * R x j) * X y x := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

private lemma gm_lr_apply' {m n p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ) (X : Mat m n) (i : Fin p) (j : Fin q) :
    (L * X * R) i j = ∑ c : Fin m × Fin n, (L i c.1 * R c.2 j) * X c.1 c.2 := by
  rw [gm_lr_apply, Fintype.sum_prod_type]

private lemma gm_memLp_lr [IsProbabilityMeasure P] {Z : Ω → Vec m} {W : Ω → Vec n}
    (hZW : P.map (fun ω => (Z ω, W ω)) = (Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)) (A : Mat m n) {p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ) (i : Fin p) (j : Fin q) :
    MemLp (fun ω => (L * sampleX A (Z ω) (W ω) * R) i j) 2 P := by
  simp only [gm_lr_apply]
  exact memLp_finsetSum _ fun y _ => memLp_finsetSum _ fun x _ =>
    (gm_memLp_sample hZW A y x).const_mul _

private lemma gm_integral_lr [IsProbabilityMeasure P] {p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ) (X : Ω → Mat m n)
    (hX : ∀ y x, Integrable (fun ω => X ω y x) P) (i : Fin p) (j : Fin q) :
    ∫ ω, (L * X ω * R) i j ∂P = (L * mean P X * R) i j := by
  simp only [gm_lr_apply]
  rw [integral_finsetSum _ (fun y _ => integrable_finsetSum _ fun x _ => (hX y x).const_mul _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_finsetSum _ (fun x _ => (hX y x).const_mul _)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_const_mul]
  simp only [mean, Matrix.of_apply]

/-- Batch as a sum of single-sample matrices. -/
private lemma gm_batch_eq (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) (ω : Ω) :
    frozenBatchG F S s ω = ((B : ℝ))⁻¹ • ∑ a : Fin B,
      rOut F.C * sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 * rIn F.C := by
  unfold frozenBatchG sampleX
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.mul_smul, Matrix.smul_mul]

private lemma gm_batch_mean [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) :
    mean P (frozenBatchG F S s) = rOut F.C * F.A * rIn F.C := by
  ext i j
  have hX : ∀ a : Fin B, ∀ y x,
      Integrable (fun ω => sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 y x) P := fun a y x =>
    (gm_memLp_sample (gm_pair_law S s a) F.A y x).integrable (by norm_num)
  have hlr : ∀ a : Fin B, ∫ ω, (rOut F.C * sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 * rIn F.C) i j
      ∂P = (rOut F.C * F.A * rIn F.C) i j := by
    intro a
    rw [gm_integral_lr (rOut F.C) (rIn F.C) (fun ω => sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2)
      (hX a) i j]
    rw [lem_app_setup_gaussian_moments_i (gm_pair_law S s a) F.A F.hA]
  have hB : (B : ℝ) ≠ 0 := by exact_mod_cast F.hB.ne'
  show ∫ ω, frozenBatchG F S s ω i j ∂P = _
  simp only [gm_batch_eq, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [integral_const_mul, integral_finsetSum _ (fun a _ =>
    (gm_memLp_lr (gm_pair_law S s a) F.A (rOut F.C) (rIn F.C) i j).integrable (by norm_num))]
  simp only [hlr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

private lemma gm_cov_weighted [IsFiniteMeasure P] {ι : Type*} [Fintype ι] {F G : ι → Ω → ℝ}
    {c d : ι → ℝ}
    (hF : ∀ p, MemLp (F p) 2 P) (hG : ∀ q, MemLp (G q) 2 P) :
    covariance (fun ω => ∑ p, c p * F p ω) (fun ω => ∑ q, d q * G q ω) P
      = ∑ p, ∑ q, c p * d q * covariance (F p) (G q) P := by
  rw [covariance_fun_sum_fun_sum (X := fun p ω => c p * F p ω)
    (Y := fun q ω => d q * G q ω) (fun p => (hF p).const_mul (c p))
    (fun q => (hG q).const_mul (d q))]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]
  ring

private lemma gm_cov_lr [IsProbabilityMeasure P] {Z : Ω → Vec m} {W : Ω → Vec n}
    (hZW : P.map (fun ω => (Z ω, W ω)) = (Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n))
    (A : Mat m n) (hA : fro A = 1) {p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ) (i : Fin p) (j : Fin q) (k : Fin p) (l : Fin q) :
    covariance (fun ω => (L * sampleX A (Z ω) (W ω) * R) i j)
      (fun ω => (L * sampleX A (Z ω) (W ω) * R) k l) P
      = ∑ x : Fin m × Fin n, ∑ y : Fin m × Fin n,
          (L i x.1 * R x.2 j) * (L k y.1 * R y.2 l) * sampleTensor A x.1 x.2 y.1 y.2 := by
  have h2 := lem_app_setup_gaussian_moments_ii hZW A hA
  have h3 : ∀ x y : Fin m × Fin n, covariance (fun ω => sampleX A (Z ω) (W ω) x.1 x.2)
      (fun ω => sampleX A (Z ω) (W ω) y.1 y.2) P = sampleTensor A x.1 x.2 y.1 y.2 :=
    fun x y => congrFun (congrFun (congrFun (congrFun h2 x.1) x.2) y.1) y.2
  simp only [gm_lr_apply']
  rw [gm_cov_weighted (fun c : Fin m × Fin n => gm_memLp_sample hZW A c.1 c.2)
    (fun c : Fin m × Fin n => gm_memLp_sample hZW A c.1 c.2)]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [h3]

private lemma gm_indep_entries [IsProbabilityMeasure P] {p q : ℕ} (S : FrozenSamples P m n B)
    (s : ℤ) (A : Mat m n) (L : Matrix (Fin p) (Fin m) ℝ) (R : Matrix (Fin n) (Fin q) ℝ)
    (i : Fin p) (j : Fin q) (k : Fin p) (l : Fin q) {a b : Fin B} (hab : a ≠ b) :
    IndepFun (fun ω => (L * sampleX A (S.zw s a ω).1 (S.zw s a ω).2 * R) i j)
      (fun ω => (L * sampleX A (S.zw s b ω).1 (S.zw s b ω).2 * R) k l) P := by
  have hind := S.indep.indepFun (show ((s, a) : ℤ × Fin B) ≠ (s, b) from
    fun h => hab (congrArg Prod.snd h))
  have hφ : Measurable (fun v : Vec m × Vec n => (L * sampleX A v.1 v.2 * R) i j) := by
    simp only [gm_lr_apply, gm_sample_entry]; fun_prop
  have hψ : Measurable (fun v : Vec m × Vec n => (L * sampleX A v.1 v.2 * R) k l) := by
    simp only [gm_lr_apply, gm_sample_entry]; fun_prop
  exact hind.comp hφ hψ

private lemma gm_batch_cov [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n) :
    covT P (frozenBatchG F S s) i j k l =
      (1 / (B : ℝ)) * ∑ p : Fin m, ∑ q : Fin n, ∑ r : Fin m, ∑ u : Fin n,
        rOut F.C i p * rIn F.C j q * sampleTensor F.A p q r u * rOut F.C k r * rIn F.C l u := by
  have hB : (B : ℝ) ≠ 0 := by exact_mod_cast F.hB.ne'
  have hG : ∀ (x : Fin m) (y : Fin n) (ω : Ω), frozenBatchG F S s ω x y
      = ((B : ℝ))⁻¹ * ∑ a : Fin B,
        (rOut F.C * sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 * rIn F.C) x y := by
    intro x y ω
    simp only [gm_batch_eq, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  have hmem : ∀ (a : Fin B) (x : Fin m) (y : Fin n),
      MemLp (fun ω => (rOut F.C * sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 * rIn F.C) x y) 2 P :=
    fun a x y => gm_memLp_lr (gm_pair_law S s a) F.A (rOut F.C) (rIn F.C) x y
  show covariance (fun ω => frozenBatchG F S s ω i j) (fun ω => frozenBatchG F S s ω k l) P = _
  simp only [hG]
  rw [covariance_const_mul_left, covariance_const_mul_right]
  rw [covariance_fun_sum_fun_sum (fun a => hmem a i j) (fun b => hmem b k l)]
  have hdiag : ∀ a : Fin B, ∑ b : Fin B,
      covariance (fun ω => (rOut F.C * sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 * rIn F.C) i j)
        (fun ω => (rOut F.C * sampleX F.A (S.zw s b ω).1 (S.zw s b ω).2 * rIn F.C) k l) P
      = covariance (fun ω => (rOut F.C * sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 * rIn F.C) i j)
        (fun ω => (rOut F.C * sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 * rIn F.C) k l) P := by
    intro a
    refine Finset.sum_eq_single a (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ a) h)
    exact (gm_indep_entries S s F.A (rOut F.C) (rIn F.C) i j k l (Ne.symm hb)).covariance_eq_zero
      (hmem a i j) (hmem b k l)
  rw [Finset.sum_congr rfl fun a _ => hdiag a]
  have hterm : ∀ a : Fin B,
      covariance (fun ω => (rOut F.C * sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 * rIn F.C) i j)
        (fun ω => (rOut F.C * sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 * rIn F.C) k l) P
      = ∑ x : Fin m × Fin n, ∑ y : Fin m × Fin n,
          (rOut F.C i x.1 * rIn F.C x.2 j) * (rOut F.C k y.1 * rIn F.C y.2 l)
            * sampleTensor F.A x.1 x.2 y.1 y.2 :=
    fun a => gm_cov_lr (gm_pair_law S s a) F.A F.hA (rOut F.C) (rIn F.C) i j k l
  rw [Finset.sum_congr rfl fun a _ => hterm a]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Fintype.sum_prod_type]
  have hsum : ∀ T : Fin m → Fin n → Fin m → Fin n → ℝ,
      (∑ x : Fin m, ∑ x_1 : Fin n, ∑ x_2 : Fin m, ∑ x_3 : Fin n,
          rOut F.C i x * rIn F.C x_1 j * (rOut F.C k x_2 * rIn F.C x_3 l) * T x x_1 x_2 x_3)
        = ∑ p : Fin m, ∑ q : Fin n, ∑ r : Fin m, ∑ u : Fin n,
          rOut F.C i p * rIn F.C j q * T p q r u * rOut F.C k r * rIn F.C l u := by
    intro T
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun u _ => ?_
    rw [gm_rIn_comm F.C q j, gm_rIn_comm F.C u l]
    ring
  rw [hsum (sampleTensor F.A)]
  field_simp

/-! ### Block-level helpers for part (iii) -/

/-- The law of one standard Gaussian pair `(z, w)`. -/
abbrev gmPair (m n : ℕ) : Measure (Vec m × Vec n) :=
  (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)

/-- The batch as a function of the block `(z_{sa}, w_{sa})_a`. -/
private def gm_Phi (F : FrozenParams m n B) (v : Fin B → Vec m × Vec n) : Mat m n :=
  ((B : ℝ))⁻¹ • ∑ a : Fin B, rOut F.C * sampleX F.A (v a).1 (v a).2 * rIn F.C

private lemma gm_Phi_meas (F : FrozenParams m n B) : Measurable (gm_Phi F) := by
  refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun y => ?_
  simp only [gm_Phi, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, gm_lr_apply,
    gm_sample_entry]
  fun_prop

/-- Law of one block `a ↦ (z_{sa}, w_{sa})` at fixed time `s`. -/
private lemma gm_block_marg [IsProbabilityMeasure P] (S : FrozenSamples P m n B) (s : ℤ) :
    P.map (fun ω (a : Fin B) => S.zw s a ω)
      = Measure.infinitePi (fun _ : Fin B => gmPair m n) := by
  have hinj : Function.Injective (fun a : Fin B => ((s, a) : ℤ × Fin B)) := by
    intro a b h
    exact (Prod.mk.inj h).2
  have hsub : iIndepFun (fun a : Fin B => fun ω => S.zw s a ω) P :=
    S.indep.precomp hinj
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun a => (S.meas s a).aemeasurable)).1 hsub]
  simp only [S.law]
  exact (Measure.infinitePi_eq_pi (fun _ : Fin B => gmPair m n)).symm

/-- Law of the full family of blocks `(s, a) ↦ (z_{sa}, w_{sa})`. -/
private lemma gm_block_law [IsProbabilityMeasure P] (S : FrozenSamples P m n B) :
    P.map (fun ω (s : ℤ) (a : Fin B) => S.zw s a ω)
      = Measure.infinitePi (fun _ : ℤ => Measure.infinitePi (fun _ : Fin B => gmPair m n)) := by
  have hinj : Function.Injective (fun p : (_ : ℤ) × Fin B => ((p.1, p.2) : ℤ × Fin B)) := by
    rintro ⟨s, a⟩ ⟨t, b⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  have hsig : iIndepFun (fun p : (_ : ℤ) × Fin B => S.zw p.1 p.2) P := S.indep.precomp hinj
  have hmeas : ∀ p : (_ : ℤ) × Fin B, Measurable (fun ω => S.zw p.1 p.2 ω) :=
    fun p => S.meas p.1 p.2
  have h1 := (iIndepFun_iff_map_fun_eq_infinitePi_map hmeas).1 hsig
  have hmarg : ∀ p : (_ : ℤ) × Fin B, P.map (fun ω => S.zw p.1 p.2 ω) = gmPair m n :=
    fun p => S.law p.1 p.2
  simp only [hmarg] at h1
  have hc : (fun ω (s : ℤ) (a : Fin B) => S.zw s a ω)
      = (MeasurableEquiv.piCurry (fun (_ : ℤ) (_ : Fin B) => Vec m × Vec n)) ∘
        (fun ω (p : (_ : ℤ) × Fin B) => S.zw p.1 p.2 ω) := rfl
  rw [hc, ← Measure.map_map (MeasurableEquiv.piCurry _).measurable (measurable_pi_iff.2 fun p => hmeas p), h1]
  exact Measure.infinitePi_map_piCurry (fun (_ : ℤ) (_ : Fin B) => gmPair m n)

private lemma gm_block_indep [IsProbabilityMeasure P] (S : FrozenSamples P m n B) :
    iIndepFun (fun (s : ℤ) (ω : Ω) (a : Fin B) => S.zw s a ω) P := by
  refine (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun s => measurable_pi_iff.2 fun a => S.meas s a)).2 ?_
  have e : Measure.infinitePi (fun s : ℤ => P.map (fun ω (a : Fin B) => S.zw s a ω))
      = Measure.infinitePi (fun _ : ℤ => Measure.infinitePi (fun _ : Fin B => gmPair m n)) := by
    simp only [gm_block_marg]
  exact (gm_block_law S).trans e.symm

/-- `lem:app-setup-gaussian-moments`(iii): the frozen batches are independent and identically
distributed (the independence and identical-law part of `eqn:app-setup-batch-cov`).
Declaration of record of part (iii). The full environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Gaussian covariance of a batch]\label{lem:app-setup-gaussian-moments}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic with $\norm A_\F=1$, let
$z\sim\mathcal N(0,\Id_{\Nout})$ and $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent, and let $X\defeq(z^\T Aw)\,z\tensor w$. Then $\EE X=A$, and its
covariance tensor $\mathcal C_{ij,kl}\defeq\Cov(X_{ij},X_{kl})$ is
\begin{equation}\label{eqn:app-setup-tensor}
\mathcal C_{ij,kl}=\delta_{ik}\delta_{jl}+2(AA^\T)_{ik}\delta_{jl}+2\delta_{ik}(A^\T A)_{jl}+A_{ij}A_{kl}+2A_{il}A_{kj}.
\end{equation}
Consequently, in the frozen-state model with $A=\Ahat$, the batches
$G_{t+1-j}$ are independent and identically distributed,
\begin{equation}\label{eqn:app-setup-batch-cov}
\begin{gathered}
\EE\Gt=\Sigmaout^{1/2}\Ahat\Sigmain^{1/2},\\
\Cov\big((\Gt)_{ij},(\Gt)_{kl}\big)=\frac1B\sum_{p,q,r,s}(\Sigmaout^{1/2})_{ip}(\Sigmain^{1/2})_{jq}\,\mathcal C_{pq,rs}\,(\Sigmaout^{1/2})_{kr}(\Sigmain^{1/2})_{ls},
\end{gathered}
\end{equation}
and the single-batch Frobenius variance is
\begin{equation}\label{eqn:app-setup-VB}
\begin{aligned}
\mathsf V_B&\defeq\EE\norm{\Gt-\EE\Gt}_\F^2\\
&=\frac1B\Big\{\Tr\Sigmaout\Tr\Sigmain+2\Tr(\Sigmaout\Ahat\Ahat^\T)\Tr\Sigmain+2\Tr\Sigmaout\Tr(\Sigmain\Ahat^\T\Ahat)+3\norm{\EE\Gt}_\F^2\Big\}.
\end{aligned}
\end{equation}
\end{lemma}
```
-/
theorem lem_app_setup_gaussian_moments_iii (F : FrozenParams m n B) (S : FrozenSamples P m n B) :
    iIndepFun (fun s : ℤ => frozenBatchG F S s) P ∧
      ∀ s s' : ℤ, P.map (frozenBatchG F S s) = P.map (frozenBatchG F S s') := by
  haveI : IsProbabilityMeasure P := gm_is_prob S 0 ⟨0, F.hB⟩
  refine ⟨?_, ?_⟩
  · have hG : (fun s : ℤ => frozenBatchG F S s)
        = fun s => (fun _ : ℤ => gm_Phi F) s ∘ (fun ω (a : Fin B) => S.zw s a ω) := by
      funext s ω
      exact gm_batch_eq F S s ω
    rw [hG]
    exact (gm_block_indep S).comp (fun _ => gm_Phi F) (fun _ => gm_Phi_meas F)
  · have hmap : ∀ t : ℤ, P.map (frozenBatchG F S t)
        = (Measure.infinitePi fun _ : Fin B => gmPair m n).map (gm_Phi F) := by
      intro t
      have hG : frozenBatchG F S t = gm_Phi F ∘ (fun ω (a : Fin B) => S.zw t a ω) := by
        funext ω
        exact gm_batch_eq F S t ω
      rw [hG, ← Measure.map_map (gm_Phi_meas F) (measurable_pi_iff.2 fun a => S.meas t a),
        gm_block_marg S t]
    intro s s'
    rw [hmap s, hmap s']

/-- `lem:app-setup-gaussian-moments`(iv): mean and covariance of one frozen batch,
`E G = Σ_out^{1/2} Â Σ_in^{1/2}` and `eqn:app-setup-batch-cov`.
Declaration of record of part (iv). The full environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Gaussian covariance of a batch]\label{lem:app-setup-gaussian-moments}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic with $\norm A_\F=1$, let
$z\sim\mathcal N(0,\Id_{\Nout})$ and $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent, and let $X\defeq(z^\T Aw)\,z\tensor w$. Then $\EE X=A$, and its
covariance tensor $\mathcal C_{ij,kl}\defeq\Cov(X_{ij},X_{kl})$ is
\begin{equation}\label{eqn:app-setup-tensor}
\mathcal C_{ij,kl}=\delta_{ik}\delta_{jl}+2(AA^\T)_{ik}\delta_{jl}+2\delta_{ik}(A^\T A)_{jl}+A_{ij}A_{kl}+2A_{il}A_{kj}.
\end{equation}
Consequently, in the frozen-state model with $A=\Ahat$, the batches
$G_{t+1-j}$ are independent and identically distributed,
\begin{equation}\label{eqn:app-setup-batch-cov}
\begin{gathered}
\EE\Gt=\Sigmaout^{1/2}\Ahat\Sigmain^{1/2},\\
\Cov\big((\Gt)_{ij},(\Gt)_{kl}\big)=\frac1B\sum_{p,q,r,s}(\Sigmaout^{1/2})_{ip}(\Sigmain^{1/2})_{jq}\,\mathcal C_{pq,rs}\,(\Sigmaout^{1/2})_{kr}(\Sigmain^{1/2})_{ls},
\end{gathered}
\end{equation}
and the single-batch Frobenius variance is
\begin{equation}\label{eqn:app-setup-VB}
\begin{aligned}
\mathsf V_B&\defeq\EE\norm{\Gt-\EE\Gt}_\F^2\\
&=\frac1B\Big\{\Tr\Sigmaout\Tr\Sigmain+2\Tr(\Sigmaout\Ahat\Ahat^\T)\Tr\Sigmain+2\Tr\Sigmaout\Tr(\Sigmain\Ahat^\T\Ahat)+3\norm{\EE\Gt}_\F^2\Big\}.
\end{aligned}
\end{equation}
\end{lemma}
```
-/
theorem lem_app_setup_gaussian_moments_iv (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (s : ℤ) :
    mean P (frozenBatchG F S s) = rOut F.C * F.A * rIn F.C ∧
      ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
        covT P (frozenBatchG F S s) i j k l =
          (1 / (B : ℝ)) * ∑ p : Fin m, ∑ q : Fin n, ∑ r : Fin m, ∑ u : Fin n,
            rOut F.C i p * rIn F.C j q * sampleTensor F.A p q r u *
              rOut F.C k r * rIn F.C l u := by
  haveI : IsProbabilityMeasure P := gm_is_prob S s ⟨0, F.hB⟩
  exact ⟨gm_batch_mean F S s, fun i j k l => gm_batch_cov F S s i j k l⟩

/-! ### Trace identities for the Frobenius variance (part (v)) -/

private lemma gv_swap_pair {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]
    (g : α → β → κ → ℝ) :
    ∑ a, ∑ b, ∑ x, g a b x = ∑ x, ∑ a, ∑ b, g a b x := by
  calc ∑ a, ∑ b, ∑ x, g a b x = ∑ a, ∑ x, ∑ b, g a b x :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ x, ∑ a, ∑ b, g a b x := Finset.sum_comm

private lemma gv_nest4 (h : Fin m → Fin n → Fin m → Fin n → ℝ) :
    ∑ p, ∑ q, ∑ r, ∑ u, h p q r u
      = ∑ x : Fin m × Fin n × Fin m × Fin n, h x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  simp only [Fintype.sum_prod_type]

private lemma gv_trace_mul_symm {k : ℕ} (So M : Matrix (Fin k) (Fin k) ℝ) (hM : Mᵀ = M) :
    ∑ p, ∑ r, So p r * M p r = Matrix.trace (So * M) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  have := congrFun (congrFun hM r) p
  simp only [Matrix.transpose_apply] at this
  rw [this]

private lemma gv_P1 (So : Matrix (Fin m) (Fin m) ℝ) (Si : Matrix (Fin n) (Fin n) ℝ) :
    ∑ p, ∑ q, ∑ r, ∑ u, So p r * Si q u
        * ((if p = r then (1:ℝ) else 0) * (if q = u then (1:ℝ) else 0))
      = Matrix.trace So * Matrix.trace Si := by
  simp [Matrix.trace, Matrix.diag, mul_ite, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

private lemma gv_P2 (So : Matrix (Fin m) (Fin m) ℝ) (Si : Matrix (Fin n) (Fin n) ℝ)
    (M : Matrix (Fin m) (Fin m) ℝ) (hM : Mᵀ = M) :
    ∑ p, ∑ q, ∑ r, ∑ u, So p r * Si q u * (2 * M p r * (if q = u then (1:ℝ) else 0))
      = 2 * Matrix.trace (So * M) * Matrix.trace Si := by
  have htr : Matrix.trace Si = ∑ q, Si q q := rfl
  rw [← gv_trace_mul_symm So M hM, htr]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  ring

private lemma gv_P3 (So : Matrix (Fin m) (Fin m) ℝ) (Si : Matrix (Fin n) (Fin n) ℝ)
    (N : Matrix (Fin n) (Fin n) ℝ) (hN : Nᵀ = N) :
    ∑ p, ∑ q, ∑ r, ∑ u, So p r * Si q u * (2 * (if p = r then (1:ℝ) else 0) * N q u)
      = 2 * Matrix.trace So * Matrix.trace (Si * N) := by
  have htr : Matrix.trace So = ∑ p, So p p := rfl
  have h3 : ∀ p q r u, So p r * Si q u * (2 * (if p = r then (1:ℝ) else 0) * N q u)
      = if p = r then 2 * So p r * (Si q u * N q u) else 0 := by
    intro p q r u
    split_ifs <;> ring
  simp only [h3, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [← gv_trace_mul_symm Si N hN, htr]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

private lemma gv_P5 (So : Matrix (Fin m) (Fin m) ℝ) (Si : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (hSi : Siᵀ = Si) :
    ∑ p, ∑ q, ∑ r, ∑ u, So p r * Si q u * (2 * A p u * A r q)
      = 2 * ∑ p, ∑ q, ∑ r, ∑ u, So p r * Si q u * (A p q * A r u) := by
  have hs : ∀ x y, Si x y = Si y x := fun x y => by
    have := congrFun (congrFun hSi y) x
    simpa [Matrix.transpose_apply] using this
  have hpr : ∀ p r : Fin m, ∑ q, ∑ u, So p r * Si q u * (2 * A p u * A r q)
      = 2 * ∑ q, ∑ u, So p r * Si q u * (A p q * A r u) := by
    intro p r
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [hs y x]
    ring
  have step1 : ∑ p, ∑ q, ∑ r, ∑ u, So p r * Si q u * (2 * A p u * A r q)
      = ∑ p, ∑ r, ∑ q, ∑ u, So p r * Si q u * (2 * A p u * A r q) :=
    Finset.sum_congr rfl fun p _ => Finset.sum_comm
  have step2 : ∑ p, ∑ r, ∑ q, ∑ u, So p r * Si q u * (2 * A p u * A r q)
      = ∑ p, ∑ r, 2 * ∑ q, ∑ u, So p r * Si q u * (A p q * A r u) :=
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => hpr p r
  have step3 : ∑ p, ∑ r, 2 * ∑ q, ∑ u, So p r * Si q u * (A p q * A r u)
      = 2 * ∑ p, ∑ q, ∑ r, ∑ u, So p r * Si q u * (A p q * A r u) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
  rw [step1, step2, step3]

private lemma gv_core (So : Matrix (Fin m) (Fin m) ℝ) (Si : Matrix (Fin n) (Fin n) ℝ)
    (hSi : Siᵀ = Si) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∑ p, ∑ q, ∑ r, ∑ u, So p r * Si q u * sampleTensor A p q r u
      = Matrix.trace So * Matrix.trace Si + 2 * Matrix.trace (So * (A * Aᵀ)) * Matrix.trace Si
        + 2 * Matrix.trace So * Matrix.trace (Si * (Aᵀ * A))
        + 3 * ∑ p, ∑ q, ∑ r, ∑ u, So p r * Si q u * (A p q * A r u) := by
  have hAAT : (A * Aᵀ)ᵀ = A * Aᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hATA : (Aᵀ * A)ᵀ = Aᵀ * A := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have e : ∀ p q r u, So p r * Si q u * sampleTensor A p q r u
      = So p r * Si q u * ((if p = r then (1:ℝ) else 0) * (if q = u then (1:ℝ) else 0))
        + So p r * Si q u * (2 * (A * Aᵀ) p r * (if q = u then (1:ℝ) else 0))
        + So p r * Si q u * (2 * (if p = r then (1:ℝ) else 0) * (Aᵀ * A) q u)
        + So p r * Si q u * (A p q * A r u)
        + So p r * Si q u * (2 * A p u * A r q) := by
    intro p q r u
    simp only [sampleTensor]
    ring
  simp only [e, Finset.sum_add_distrib]
  rw [gv_P1, gv_P2 So Si (A * Aᵀ) hAAT, gv_P3 So Si (Aᵀ * A) hATA, gv_P5 So Si A hSi]
  ring

private lemma gv_Qtr (So : Matrix (Fin m) (Fin m) ℝ) (Si : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (hSi : Siᵀ = Si) :
    ∑ p, ∑ q, ∑ r, ∑ u, So p r * Si q u * (A p q * A r u)
      = Matrix.trace (So * (A * Si * Aᵀ)) := by
  have hsym : (A * Si * Aᵀ)ᵀ = A * Si * Aᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hSi,
      Matrix.mul_assoc]
  rw [← gv_trace_mul_symm So (A * Si * Aᵀ) hsym]
  have hM : ∀ p r, (A * Si * Aᵀ) p r = ∑ u, ∑ q, A p q * Si q u * A r u := by
    intro p r
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  simp only [hM, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun q _ => ?_
  ring

private lemma gv_gram_trace {k l : ℕ} (X : Matrix (Fin k) (Fin l) ℝ) :
    ∑ i, ∑ j, X i j ^ 2 = Matrix.trace (Xᵀ * X) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]
  exact Finset.sum_comm

private lemma gv_fro_trace (Ro : Matrix (Fin m) (Fin m) ℝ) (Ri : Matrix (Fin n) (Fin n) ℝ)
    (So : Matrix (Fin m) (Fin m) ℝ) (Si : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hRo : Roᵀ = Ro) (hRi : Riᵀ = Ri) (hRo2 : Ro * Ro = So) (hRi2 : Ri * Ri = Si)
    (hSi : Siᵀ = Si) :
    ∑ i, ∑ j, (Ro * A * Ri) i j ^ 2 = Matrix.trace (So * (A * Si * Aᵀ)) := by
  rw [gv_gram_trace]
  have hX : (Ro * A * Ri)ᵀ * (Ro * A * Ri) = Ri * (Aᵀ * So * A * Ri) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hRo, hRi]
    rw [← hRo2]
    simp only [Matrix.mul_assoc]
  rw [hX]
  have h1 : Matrix.trace (Ri * (Aᵀ * So * A * Ri)) = Matrix.trace (Aᵀ * So * A * Si) := by
    rw [Matrix.trace_mul_comm, ← hRi2]
    simp only [Matrix.mul_assoc]
  rw [h1]
  have h2 : Matrix.trace (Aᵀ * So * A * Si) = Matrix.trace (So * (A * Si * Aᵀ)) := by
    rw [show Aᵀ * So * A * Si = Aᵀ * (So * A * Si) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h2]

private lemma gv_fro_sq {k l : ℕ} (K : Matrix (Fin k) (Fin l) ℝ) :
    fro K ^ 2 = ∑ i, ∑ j, K i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma gv_rOut_transpose (C : Covariances m n) : (rOut C)ᵀ = rOut C := by
  have h : (CFC.sqrt C.Sout)ᴴ = CFC.sqrt C.Sout :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sout)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma gv_rIn_transpose (C : Covariances m n) : (rIn C)ᵀ = rIn C := by
  have h : (CFC.sqrt C.Sin)ᴴ = CFC.sqrt C.Sin :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma gv_rOut_mul_self (C : Covariances m n) : rOut C * rOut C = C.Sout :=
  CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)

private lemma gv_rIn_mul_self (C : Covariances m n) : rIn C * rIn C = C.Sin :=
  CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)

private lemma gv_sum_out (C : Covariances m n) (p r : Fin m) :
    ∑ a, rOut C a p * rOut C a r = C.Sout p r := by
  have h := congrFun (congrFun (gv_rOut_mul_self C) p) r
  rw [Matrix.mul_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hs := congrFun (congrFun (gv_rOut_transpose C) p) a
  simp only [Matrix.transpose_apply] at hs
  rw [hs]

private lemma gv_sum_in (C : Covariances m n) (q u : Fin n) :
    ∑ b, rIn C b q * rIn C b u = C.Sin q u := by
  have h := congrFun (congrFun (gv_rIn_mul_self C) q) u
  rw [Matrix.mul_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hs := congrFun (congrFun (gv_rIn_transpose C) q) b
  simp only [Matrix.transpose_apply] at hs
  rw [hs]

/-- Entries of one frozen batch are in `L²`. -/
private lemma gv_entry_memLp [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (a : Fin m) (b : Fin n) :
    MemLp (fun ω => frozenBatchG F S s ω a b) 2 P := by
  have hf : (fun ω => frozenBatchG F S s ω a b)
      = fun ω => ((B : ℝ))⁻¹ * ∑ c : Fin B,
          (rOut F.C * sampleX F.A (S.zw s c ω).1 (S.zw s c ω).2 * rIn F.C) a b := by
    funext ω
    simp only [gm_batch_eq, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [hf]
  exact (memLp_finsetSum _ fun c _ =>
    gm_memLp_lr (gm_pair_law S s c) F.A (rOut F.C) (rIn F.C) a b).const_mul _

/-- Frobenius variance of one batch as the sum of entrywise variances. -/
private lemma gv_int_fro [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) :
    ∫ ω, (fro (frozenBatchG F S s ω - mean P (frozenBatchG F S s))) ^ 2 ∂P
      = ∑ a, ∑ b, covariance (fun ω => frozenBatchG F S s ω a b)
          (fun ω => frozenBatchG F S s ω a b) P := by
  have hint : ∀ a b, Integrable (fun ω =>
      (frozenBatchG F S s ω a b - mean P (frozenBatchG F S s) a b) ^ 2) P := fun a b =>
    ((gv_entry_memLp F S s a b).sub (memLp_const _)).integrable_sq
  have hfro : ∀ ω, (fro (frozenBatchG F S s ω - mean P (frozenBatchG F S s))) ^ 2
      = ∑ a, ∑ b, (frozenBatchG F S s ω a b - mean P (frozenBatchG F S s) a b) ^ 2 := by
    intro ω
    rw [gv_fro_sq]
    simp only [Matrix.sub_apply]
  simp_rw [hfro]
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun b _ => hint a b)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finset_sum _ (fun b _ => hint a b)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hmean : mean P (frozenBatchG F S s) a b = ∫ ω, frozenBatchG F S s ω a b ∂P := rfl
  unfold covariance
  simp only [hmean, sq]

/-- Pointwise factorization of the batch covariance sum over the batch index. -/
private lemma gv_pt (F : FrozenParams m n B) (p : Fin m) (q : Fin n) (r : Fin m) (u : Fin n) :
    ∑ a, ∑ b, rOut F.C a p * rIn F.C b q * sampleTensor F.A p q r u * rOut F.C a r
        * rIn F.C b u
      = F.C.Sout p r * F.C.Sin q u * sampleTensor F.A p q r u := by
  have e : ∀ a b, rOut F.C a p * rIn F.C b q * sampleTensor F.A p q r u * rOut F.C a r
      * rIn F.C b u
      = (rOut F.C a p * rOut F.C a r) * (rIn F.C b q * rIn F.C b u * sampleTensor F.A p q r u) := by
    intros
    ring
  simp only [e, ← Finset.mul_sum, ← Finset.sum_mul, gv_sum_out, gv_sum_in]
  try ring

/-- The batch Frobenius-variance sum in closed trace form, for any batch index `s`. -/
private lemma gv_VB [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) :
    ∑ a, ∑ b, covariance (fun ω => frozenBatchG F S s ω a b)
        (fun ω => frozenBatchG F S s ω a b) P
      = (1 / (B : ℝ)) * (Matrix.trace F.C.Sout * Matrix.trace F.C.Sin
          + 2 * Matrix.trace (F.C.Sout * (F.A * Matrix.transpose F.A)) * Matrix.trace F.C.Sin
          + 2 * Matrix.trace F.C.Sout * Matrix.trace (F.C.Sin * (Matrix.transpose F.A * F.A))
          + 3 * (fro (rOut F.C * F.A * rIn F.C)) ^ 2) := by
  have hSi : F.C.Sinᵀ = F.C.Sin := by
    have h := F.C.psdIn.isHermitian
    unfold Matrix.IsHermitian at h
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hc : ∀ a b, covariance (fun ω => frozenBatchG F S s ω a b)
      (fun ω => frozenBatchG F S s ω a b) P
      = (1 / (B : ℝ)) * ∑ p, ∑ q, ∑ r, ∑ u, rOut F.C a p * rIn F.C b q
          * sampleTensor F.A p q r u * rOut F.C a r * rIn F.C b u :=
    fun a b => gm_batch_cov F S s a b a b
  have hsw : ∑ a, ∑ b, ∑ p, ∑ q, ∑ r, ∑ u, rOut F.C a p * rIn F.C b q
          * sampleTensor F.A p q r u * rOut F.C a r * rIn F.C b u
      = ∑ p, ∑ q, ∑ r, ∑ u, ∑ a, ∑ b, rOut F.C a p * rIn F.C b q
          * sampleTensor F.A p q r u * rOut F.C a r * rIn F.C b u := by
    calc _ = ∑ a, ∑ b, ∑ x : Fin m × Fin n × Fin m × Fin n,
          (fun p q r u => rOut F.C a p * rIn F.C b q * sampleTensor F.A p q r u * rOut F.C a r
            * rIn F.C b u) x.1 x.2.1 x.2.2.1 x.2.2.2 :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => gv_nest4 _
      _ = ∑ x : Fin m × Fin n × Fin m × Fin n, ∑ a, ∑ b,
          (fun p q r u => rOut F.C a p * rIn F.C b q * sampleTensor F.A p q r u * rOut F.C a r
            * rIn F.C b u) x.1 x.2.1 x.2.2.1 x.2.2.2 := gv_swap_pair _
      _ = _ := (gv_nest4 (fun p q r u => ∑ a, ∑ b, rOut F.C a p * rIn F.C b q
          * sampleTensor F.A p q r u * rOut F.C a r * rIn F.C b u)).symm
  have hs1 : ∑ a, ∑ b, covariance (fun ω => frozenBatchG F S s ω a b)
        (fun ω => frozenBatchG F S s ω a b) P
      = (1 / (B : ℝ)) * ∑ a, ∑ b, ∑ p, ∑ q, ∑ r, ∑ u, rOut F.C a p * rIn F.C b q
          * sampleTensor F.A p q r u * rOut F.C a r * rIn F.C b u := by
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hc a b]
    simp only [Finset.mul_sum]
  rw [hs1, hsw]
  simp only [gv_pt]
  rw [gv_core F.C.Sout F.C.Sin hSi F.A]
  rw [gv_Qtr F.C.Sout F.C.Sin F.A hSi, gv_fro_sq, gv_fro_trace (rOut F.C) (rIn F.C) F.C.Sout
    F.C.Sin F.A (gv_rOut_transpose F.C) (gv_rIn_transpose F.C) (gv_rOut_mul_self F.C)
    (gv_rIn_mul_self F.C) hSi]

/-- `lem:app-setup-gaussian-moments`(v): the single-batch Frobenius variance, `eqn:app-setup-VB`.
Declaration of record of part (v). The full environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Gaussian covariance of a batch]\label{lem:app-setup-gaussian-moments}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic with $\norm A_\F=1$, let
$z\sim\mathcal N(0,\Id_{\Nout})$ and $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent, and let $X\defeq(z^\T Aw)\,z\tensor w$. Then $\EE X=A$, and its
covariance tensor $\mathcal C_{ij,kl}\defeq\Cov(X_{ij},X_{kl})$ is
\begin{equation}\label{eqn:app-setup-tensor}
\mathcal C_{ij,kl}=\delta_{ik}\delta_{jl}+2(AA^\T)_{ik}\delta_{jl}+2\delta_{ik}(A^\T A)_{jl}+A_{ij}A_{kl}+2A_{il}A_{kj}.
\end{equation}
Consequently, in the frozen-state model with $A=\Ahat$, the batches
$G_{t+1-j}$ are independent and identically distributed,
\begin{equation}\label{eqn:app-setup-batch-cov}
\begin{gathered}
\EE\Gt=\Sigmaout^{1/2}\Ahat\Sigmain^{1/2},\\
\Cov\big((\Gt)_{ij},(\Gt)_{kl}\big)=\frac1B\sum_{p,q,r,s}(\Sigmaout^{1/2})_{ip}(\Sigmain^{1/2})_{jq}\,\mathcal C_{pq,rs}\,(\Sigmaout^{1/2})_{kr}(\Sigmain^{1/2})_{ls},
\end{gathered}
\end{equation}
and the single-batch Frobenius variance is
\begin{equation}\label{eqn:app-setup-VB}
\begin{aligned}
\mathsf V_B&\defeq\EE\norm{\Gt-\EE\Gt}_\F^2\\
&=\frac1B\Big\{\Tr\Sigmaout\Tr\Sigmain+2\Tr(\Sigmaout\Ahat\Ahat^\T)\Tr\Sigmain+2\Tr\Sigmaout\Tr(\Sigmain\Ahat^\T\Ahat)+3\norm{\EE\Gt}_\F^2\Big\}.
\end{aligned}
\end{equation}
\end{lemma}
```
-/
theorem lem_app_setup_gaussian_moments_v (F : FrozenParams m n B) (S : FrozenSamples P m n B) :
    frozenVB S F = (1 / (B : ℝ)) *
      (Matrix.trace F.C.Sout * Matrix.trace F.C.Sin
        + 2 * Matrix.trace (F.C.Sout * (F.A * Matrix.transpose F.A)) * Matrix.trace F.C.Sin
        + 2 * Matrix.trace F.C.Sout * Matrix.trace (F.C.Sin * (Matrix.transpose F.A * F.A))
        + 3 * (fro (mean P (frozenBatchG F S 0))) ^ 2) := by
  haveI : IsProbabilityMeasure P := gm_is_prob S 0 ⟨0, F.hB⟩
  unfold frozenVB
  rw [gv_int_fro, gv_VB F S 0, gm_batch_mean F S 0]

/-! ## Stationary EMA law -/

/-- Second-moment expansion of a centered linear combination of entries of batches. -/
private lemma gv_var_comb [IsFiniteMeasure P] {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (X : ι → Ω → ℝ) (e : ℝ)
    (hX : ∀ j ∈ s, MemLp (X j) 2 P) (he : ∀ j ∈ s, ∫ ω, X j ω ∂P = e) :
    ∫ ω, (∑ j ∈ s, c j * (X j ω - e)) ^ 2 ∂P
      = ∑ j ∈ s, ∑ j' ∈ s, c j * c j' * covariance (X j) (X j') P := by
  have hZ : ∀ j ∈ s, MemLp (fun ω => X j ω - e) 2 P := fun j hj =>
    (hX j hj).sub (memLp_const e)
  have hpt : ∀ ω, (∑ j ∈ s, c j * (X j ω - e)) ^ 2
      = ∑ j ∈ s, ∑ j' ∈ s, c j * c j' * ((X j ω - e) * (X j' ω - e)) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    ring
  have hI : ∀ j ∈ s, ∀ j' ∈ s, Integrable
      (fun ω => c j * c j' * ((X j ω - e) * (X j' ω - e))) P := fun j hj j' hj' => by
    have h := ((hZ j hj).integrable_mul (hZ j' hj')).const_mul (c j * c j')
    exact h
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun j hj => integrable_finsetSum _ fun j' hj' => hI j hj j' hj')]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_finsetSum _ (fun j' hj' => hI j hj j' hj')]
  refine Finset.sum_congr rfl fun j' hj' => ?_
  rw [integral_const_mul]
  congr 1
  unfold covariance
  simp only [he j hj, he j' hj']

/-- Swap the batch-entry sums past the two lag sums. -/
private lemma gv_swap4 {α β : Type*} [Fintype α] [Fintype β] (s : Finset ℕ)
    (H : α → β → ℕ → ℕ → ℝ) :
    ∑ a, ∑ b, ∑ j ∈ s, ∑ j' ∈ s, H a b j j' = ∑ j ∈ s, ∑ j' ∈ s, ∑ a, ∑ b, H a b j j' := by
  calc ∑ a, ∑ b, ∑ j ∈ s, ∑ j' ∈ s, H a b j j' = ∑ a, ∑ j ∈ s, ∑ b, ∑ j' ∈ s, H a b j j' :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ j ∈ s, ∑ j' ∈ s, ∑ b, H a b j j' :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j ∈ s, ∑ a, ∑ j' ∈ s, ∑ b, H a b j j' := Finset.sum_comm
    _ = ∑ j ∈ s, ∑ j' ∈ s, ∑ a, ∑ b, H a b j j' :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm

/-- Distinct batches are independent, so their entrywise covariances vanish. -/
private lemma gv_cov_indep [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s s' : ℤ)
    (hss : s ≠ s') (a : Fin m) (b : Fin n) :
    covariance (fun ω => frozenBatchG F S s ω a b) (fun ω => frozenBatchG F S s' ω a b) P = 0 := by
  have hI := (lem_app_setup_gaussian_moments_iii F S).1.indepFun hss
  have hφ : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => M a b) :=
    (measurable_pi_apply b).comp (measurable_pi_apply a)
  have h2 := hI.comp hφ hφ
  exact h2.covariance_eq_zero (gv_entry_memLp F S s a b) (gv_entry_memLp F S s' a b)

/-- `eqn:app-setup-orthogonality` (exported from the proof of `lem:app-setup-ema-law`(iii)):
the orthogonality of the centered, independent batches. Declaration of record of the equation.
The displayed equation, verbatim from `section.tex`:
```latex
\begin{equation}\label{eqn:app-setup-orthogonality}
\EE\Big\|\sum_{j=k}^l\emaw{j}\big(G_{t+1-j}-\EE\Gt\big)\Big\|_\F^2=\mathsf V_B\sum_{j=k}^l\emaw{j}^2 .
\end{equation}
```
-/
theorem eqn_app_setup_orthogonality [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) {k l : ℕ} (hkl : k ≤ l) :
    ∫ ω, (fro (∑ j ∈ Finset.Icc k l,
        emaW F.β j • (frozenBatchG F S (t + 1 - (j : ℤ)) ω - mean P (frozenBatchG F S 0)))) ^ 2
      ∂P
      = frozenVB S F * ∑ j ∈ Finset.Icc k l, emaW F.β j ^ 2 := by
  have hV0 : frozenVB S F = ∑ a, ∑ b, covariance (fun ω => frozenBatchG F S 0 ω a b)
      (fun ω => frozenBatchG F S 0 ω a b) P := by
    unfold frozenVB
    exact gv_int_fro F S 0
  have hVs : ∀ s : ℤ, ∑ a, ∑ b, covariance (fun ω => frozenBatchG F S s ω a b)
      (fun ω => frozenBatchG F S s ω a b) P = frozenVB S F := fun s => by
    rw [hV0]
    exact (gv_VB F S s).trans (gv_VB F S 0).symm
  have hint_entry : ∀ (s : ℤ) (a : Fin m) (b : Fin n),
      ∫ ω, frozenBatchG F S s ω a b ∂P = (rOut F.C * F.A * rIn F.C) a b :=
    fun s a b => congrFun (congrFun (gm_batch_mean F S s) a) b
  rw [gm_batch_mean F S 0]
  have hfro : ∀ ω, (fro (∑ j ∈ Finset.Icc k l, emaW F.β j •
      (frozenBatchG F S (t + 1 - (j : ℤ)) ω - rOut F.C * F.A * rIn F.C))) ^ 2
      = ∑ a, ∑ b, (∑ j ∈ Finset.Icc k l, emaW F.β j
          * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b)) ^ 2 := by
    intro ω
    rw [gv_fro_sq]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  have hMem : ∀ (a : Fin m) (b : Fin n), MemLp (fun ω => ∑ j ∈ Finset.Icc k l,
      emaW F.β j * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b))
      2 P := fun a b => memLp_finsetSum _ fun j _ =>
    ((gv_entry_memLp F S _ a b).sub (memLp_const _)).const_mul _
  have hvc : ∀ (a : Fin m) (b : Fin n), ∫ ω, (∑ j ∈ Finset.Icc k l, emaW F.β j
      * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b)) ^ 2 ∂P
      = ∑ j ∈ Finset.Icc k l, ∑ j' ∈ Finset.Icc k l, emaW F.β j * emaW F.β j'
          * covariance (fun ω => frozenBatchG F S (t + 1 - (j : ℤ)) ω a b)
            (fun ω => frozenBatchG F S (t + 1 - (j' : ℤ)) ω a b) P := fun a b =>
    gv_var_comb (Finset.Icc k l) (fun j => emaW F.β j)
      (fun j ω => frozenBatchG F S (t + 1 - (j : ℤ)) ω a b) ((rOut F.C * F.A * rIn F.C) a b)
      (fun j _ => gv_entry_memLp F S _ a b)
      (fun j _ => hint_entry _ a b)
  simp_rw [hfro]
  have hsplit : ∫ ω, ∑ a, ∑ b, (∑ j ∈ Finset.Icc k l, emaW F.β j
      * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b)) ^ 2 ∂P
      = ∑ a, ∑ b, ∫ ω, (∑ j ∈ Finset.Icc k l, emaW F.β j
      * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b)) ^ 2 ∂P := by
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (hMem a b).integrable_sq)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ (fun b _ => (hMem a b).integrable_sq)]
  rw [hsplit, Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hvc a b,
    gv_swap4 (Finset.Icc k l)]
  have hsum : ∀ j ∈ Finset.Icc k l, ∀ j' ∈ Finset.Icc k l,
      ∑ a, ∑ b, emaW F.β j * emaW F.β j' * covariance
          (fun ω => frozenBatchG F S (t + 1 - (j : ℤ)) ω a b)
          (fun ω => frozenBatchG F S (t + 1 - (j' : ℤ)) ω a b) P
        = emaW F.β j * emaW F.β j' * ∑ a, ∑ b, covariance
          (fun ω => frozenBatchG F S (t + 1 - (j : ℤ)) ω a b)
          (fun ω => frozenBatchG F S (t + 1 - (j' : ℤ)) ω a b) P := by
    intro j _ j' _
    simp only [Finset.mul_sum]
  have hD : ∀ j ∈ Finset.Icc k l, ∀ j' ∈ Finset.Icc k l, j ≠ j' →
      ∑ a, ∑ b, covariance (fun ω => frozenBatchG F S (t + 1 - (j : ℤ)) ω a b)
        (fun ω => frozenBatchG F S (t + 1 - (j' : ℤ)) ω a b) P = 0 := by
    intro j _ j' _ hjj'
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    exact gv_cov_indep F S _ _ (by omega) a b
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun j' hj' => hsum j hj j' hj']
  calc _ = ∑ j ∈ Finset.Icc k l, emaW F.β j * emaW F.β j * frozenVB S F :=
        Finset.sum_congr rfl fun j hj => by
          rw [Finset.sum_eq_single j (fun j' hj' hne => by
              simp only [hD j hj j' hj' (Ne.symm hne), mul_zero])
            (fun h => absurd hj h), hVs]
    _ = frozenVB S F * ∑ j ∈ Finset.Icc k l, emaW F.β j ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring

/-! ### Private copies of the a.s. series helpers (used by the lag decomposition) -/

private lemma gq_ae_summable {ι : Type*} [Countable ι] {g : ι → Ω → ℝ}
    (hm : ∀ i, Measurable (g i)) (hnn : ∀ i ω, 0 ≤ g i ω)
    (hfin : ∑' i, ∫⁻ ω, ENNReal.ofReal (g i ω) ∂P ≠ ⊤) :
    ∀ᵐ ω ∂P, Summable fun i => g i ω := by
  have h1 : ∫⁻ ω, ∑' i, ENNReal.ofReal (g i ω) ∂P = ∑' i, ∫⁻ ω, ENNReal.ofReal (g i ω) ∂P :=
    lintegral_tsum fun i => (hm i).ennreal_ofReal.aemeasurable
  have h2 : ∫⁻ ω, ∑' i, ENNReal.ofReal (g i ω) ∂P ≠ ⊤ := by rw [h1]; exact hfin
  have h3 : ∀ᵐ ω ∂P, ∑' i, ENNReal.ofReal (g i ω) < ⊤ :=
    ae_lt_top (Measurable.ennreal_tsum fun i => (hm i).ennreal_ofReal) h2
  filter_upwards [h3] with ω hω
  refine (ENNReal.summable_toReal hω.ne).congr fun i => ?_
  exact ENNReal.toReal_ofReal (hnn i ω)

private lemma gq_fro_smul {k l : ℕ} (c : ℝ) (K : Mat k l) : fro (c • K) = |c| * fro K := by
  have h : ∀ i j, ‖(c • K) i j‖ ^ 2 = c ^ 2 * ‖K i j‖ ^ 2 := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs, mul_pow, sq_abs]
  unfold fro
  simp only [h, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

private lemma gq_fro_le {k l : ℕ} (K : Mat k l) : fro K ≤ ∑ i, ∑ j, ‖K i j‖ := by
  have hnn : 0 ≤ ∑ i, ∑ j, ‖K i j‖ :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  unfold fro
  rw [Real.sqrt_le_left hnn]
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin k × Fin l)))
    (f := fun p => ‖K p.1 p.2‖) (fun p _ => norm_nonneg _)
  simp only [Fintype.sum_prod_type] at h
  exact h

private lemma gq_fro_meas {k l : ℕ} {Y : Ω → Mat k l} (hY : ∀ i j, Measurable fun ω => Y ω i j) :
    Measurable fun ω => fro (Y ω) := by
  unfold fro
  exact Measurable.sqrt (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (hY i j).norm.pow_const 2)

private lemma gq_batch_meas (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    ∀ i j, Measurable fun ω => frozenBatchG F S s ω i j := by
  intro i j
  have hsx : ∀ a : Fin B, ∀ y x,
      Measurable fun ω => sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 y x :=
    fun a y x => (gm_sample_meas F.A y x).comp (S.meas s a)
  simp only [gm_batch_eq, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, gm_lr_apply]
  exact measurable_const.mul (Finset.measurable_sum _ fun a _ =>
    Finset.measurable_sum _ fun y _ => Finset.measurable_sum _ fun x _ =>
      measurable_const.mul (hsx a y x))

private lemma gq_fro_integrable [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) :
    Integrable (fun ω => fro (frozenBatchG F S s ω)) P := by
  have hbound : Integrable (fun ω => ∑ i, ∑ j, ‖frozenBatchG F S s ω i j‖) P :=
    integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
      ((gv_entry_memLp F S s i j).integrable (by norm_num)).norm
  refine hbound.mono' (gq_fro_meas (gq_batch_meas F S s)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have hnn : 0 ≤ fro (frozenBatchG F S s ω) := by unfold fro; exact Real.sqrt_nonneg _
  rw [Real.norm_of_nonneg hnn]
  exact gq_fro_le _

private lemma gq_fro_lint_eq [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) :
    ∫⁻ ω, ENNReal.ofReal (fro (frozenBatchG F S s ω)) ∂P
      = ∫⁻ ω, ENNReal.ofReal (fro (frozenBatchG F S 0 ω)) ∂P := by
  have hmeas : ∀ s', Measurable (frozenBatchG F S s') := fun s' =>
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => gq_batch_meas F S s' i j
  have hent : ∀ i j, Measurable fun K : Mat m n => K i j :=
    fun i j => (measurable_pi_apply j).comp (measurable_pi_apply i)
  have hfK : Measurable fun K : Mat m n => ENNReal.ofReal (fro K) :=
    ENNReal.measurable_ofReal.comp (gq_fro_meas (Y := fun K : Mat m n => K) hent)
  have key : ∀ s', ∫⁻ ω, ENNReal.ofReal (fro (frozenBatchG F S s' ω)) ∂P
      = ∫⁻ K, ENNReal.ofReal (fro K) ∂(P.map (frozenBatchG F S s')) := fun s' =>
    (lintegral_map hfK (hmeas s')).symm
  rw [key s, key 0, (lem_app_setup_gaussian_moments_iii F S).2 s 0]

private lemma gq_fro_series_ae [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) :
    ∀ᵐ ω ∂P, ∀ t : ℤ, Summable fun j : ℕ =>
        fro (emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) := by
  have hC : ∫⁻ ω, ENNReal.ofReal (fro (frozenBatchG F S 0 ω)) ∂P ≠ ⊤ :=
    ne_top_of_lt (gq_fro_integrable F S 0).lintegral_lt_top
  have hnn : ∀ j : ℕ, 0 ≤ emaW F.β j := fun j =>
    mul_nonneg (by linarith [F.hβ.2]) (pow_nonneg F.hβ.1 j)
  have hsum : Summable (fun j : ℕ => emaW F.β j) :=
    (summable_geometric_of_lt_one F.hβ.1 F.hβ.2).mul_left (1 - F.β)
  have hterm : ∀ (t : ℤ) (j : ℕ),
      ∫⁻ ω, ENNReal.ofReal (fro (emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω)) ∂P
        = ENNReal.ofReal (emaW F.β j) * ∫⁻ ω, ENNReal.ofReal (fro (frozenBatchG F S 0 ω)) ∂P := by
    intro t j
    have h1 : ∀ ω, ENNReal.ofReal (fro (emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω))
        = ENNReal.ofReal (|emaW F.β j|) * ENNReal.ofReal (fro (frozenBatchG F S (t + 1 - (j : ℤ)) ω)) :=
      fun ω => by rw [gq_fro_smul, ENNReal.ofReal_mul (abs_nonneg _)]
    have hmeasf : Measurable fun ω =>
        ENNReal.ofReal (fro (frozenBatchG F S (t + 1 - (j : ℤ)) ω)) :=
      ENNReal.measurable_ofReal.comp (gq_fro_meas (gq_batch_meas F S _))
    simp_rw [h1]
    rw [lintegral_const_mul _ hmeasf, gq_fro_lint_eq, abs_of_nonneg (hnn j)]
  refine ae_all_iff.2 fun t => gq_ae_summable (g := fun j ω =>
      fro (emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω)) ?_ ?_ ?_
  · intro j
    exact gq_fro_meas (Y := fun ω => emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω)
      fun i k => (gq_batch_meas F S _ i k).const_mul _
  · intro j ω
    have hnn' : 0 ≤ fro (emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) := by
      unfold fro; exact Real.sqrt_nonneg _
    exact hnn'
  · simp only [hterm]
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg hnn hsum,
      tsum_emaW F.hβ.1 F.hβ.2]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC

private lemma gq_entry_le_fro {k l : ℕ} (K : Mat k l) (i : Fin k) (j : Fin l) :
    ‖K i j‖ ≤ fro K := by
  unfold fro
  rw [Real.norm_eq_abs]
  refine Real.abs_le_sqrt ?_
  have h1 : ‖K i j‖ ^ 2 ≤ ∑ j', ‖K i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖K i j'‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖K i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖K i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖K i' j'‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  rw [Real.norm_eq_abs, sq_abs] at h1
  simpa [Real.norm_eq_abs, sq_abs] using h1.trans (by simpa [Real.norm_eq_abs, sq_abs] using h2)

private lemma gq_summable_of_fro {k l : ℕ} {f : ℕ → Mat k l}
    (h : Summable fun j => fro (f j)) : Summable f :=
  Pi.summable.2 fun i => Pi.summable.2 fun j =>
    Summable.of_norm_bounded h (fun n => gq_entry_le_fro (f n) i j)

/-- `eqn:app-setup-lag-decomposition` (exported from the proof of `lem:app-setup-ema-law`(iv)):
the lag decomposition of a later buffer, almost surely and for all `t ∈ ℤ`, `ℓ ≥ 0`.
The displayed equation, verbatim from `section.tex`:
```latex
\begin{equation}\label{eqn:app-setup-lag-decomposition}
M_{t+\ell}=\bmom^\ell\,\Mt+\sum_{r=0}^{\ell-1}\emaw{r}\,G_{t+\ell+1-r},
\end{equation}
```
-/
theorem eqn_app_setup_lag_decomposition [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) :
    ∀ᵐ ω ∂P, ∀ (t : ℤ) (ℓ : ℕ), frozenBuf F S (t + (ℓ : ℤ)) ω =
      F.β ^ ℓ • frozenBuf F S t ω
        + ∑ r ∈ Finset.range ℓ, emaW F.β r • frozenBatchG F S (t + (ℓ : ℤ) + 1 - (r : ℤ)) ω := by
  filter_upwards [gq_fro_series_ae F S] with ω hω
  intro t ℓ
  have hfs : Summable fun j : ℕ => emaW F.β j • frozenBatchG F S (t + (ℓ : ℤ) + 1 - (j : ℤ)) ω :=
    gq_summable_of_fro (hω (t + (ℓ : ℤ)))
  have hs : Summable fun j : ℕ => emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω :=
    gq_summable_of_fro (hω t)
  have hcongr : ∀ i : ℕ,
      emaW F.β (i + ℓ) • frozenBatchG F S (t + (ℓ : ℤ) + 1 - ((i + ℓ : ℕ) : ℤ)) ω
        = F.β ^ ℓ • (emaW F.β i • frozenBatchG F S (t + 1 - (i : ℤ)) ω) := by
    intro i
    have e1 : emaW F.β (i + ℓ) = F.β ^ ℓ * emaW F.β i := by
      simp only [emaW]
      rw [pow_add]
      ring
    have e2 : t + (ℓ : ℤ) + 1 - ((i + ℓ : ℕ) : ℤ) = t + 1 - (i : ℤ) := by
      push_cast
      ring
    rw [e1, e2, smul_smul]
  have htail : ∑' i : ℕ, emaW F.β (i + ℓ) •
      frozenBatchG F S (t + (ℓ : ℤ) + 1 - ((i + ℓ : ℕ) : ℤ)) ω
        = F.β ^ ℓ • frozenBuf F S t ω := by
    simp only [hcongr]
    rw [hs.tsum_const_smul (F.β ^ ℓ)]
    rfl
  have hsplit := hfs.sum_add_tsum_nat_add ℓ
  have hbuf : frozenBuf F S (t + (ℓ : ℤ)) ω
      = ∑' j : ℕ, emaW F.β j • frozenBatchG F S (t + (ℓ : ℤ) + 1 - (j : ℤ)) ω := rfl
  rw [hbuf, ← hsplit, htail, add_comm]

/-! ### Private helpers for `lem:app-setup-ema-law`(i)-(ii) -/

private lemma gi_ae_summable {ι : Type*} [Countable ι] {g : ι → Ω → ℝ}
    (hm : ∀ i, Measurable (g i)) (hnn : ∀ i ω, 0 ≤ g i ω)
    (hfin : ∑' i, ∫⁻ ω, ENNReal.ofReal (g i ω) ∂P ≠ ⊤) :
    ∀ᵐ ω ∂P, Summable fun i => g i ω := by
  have h1 : ∫⁻ ω, ∑' i, ENNReal.ofReal (g i ω) ∂P = ∑' i, ∫⁻ ω, ENNReal.ofReal (g i ω) ∂P :=
    lintegral_tsum fun i => (hm i).ennreal_ofReal.aemeasurable
  have h2 : ∫⁻ ω, ∑' i, ENNReal.ofReal (g i ω) ∂P ≠ ⊤ := by rw [h1]; exact hfin
  have h3 : ∀ᵐ ω ∂P, ∑' i, ENNReal.ofReal (g i ω) < ⊤ :=
    ae_lt_top (Measurable.ennreal_tsum fun i => (hm i).ennreal_ofReal) h2
  filter_upwards [h3] with ω hω
  refine (ENNReal.summable_toReal hω.ne).congr fun i => ?_
  exact ENNReal.toReal_ofReal (hnn i ω)

private lemma gi_fro_smul {k l : ℕ} (c : ℝ) (K : Mat k l) : fro (c • K) = |c| * fro K := by
  have h : ∀ i j, ‖(c • K) i j‖ ^ 2 = c ^ 2 * ‖K i j‖ ^ 2 := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs, mul_pow, sq_abs]
  unfold fro
  simp only [h, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

private lemma gi_fro_le {k l : ℕ} (K : Mat k l) : fro K ≤ ∑ i, ∑ j, ‖K i j‖ := by
  have hnn : 0 ≤ ∑ i, ∑ j, ‖K i j‖ :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  unfold fro
  rw [Real.sqrt_le_left hnn]
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin k × Fin l)))
    (f := fun p => ‖K p.1 p.2‖) (fun p _ => norm_nonneg _)
  simp only [Fintype.sum_prod_type] at h
  exact h

private lemma gi_fro_meas {k l : ℕ} {Y : Ω → Mat k l} (hY : ∀ i j, Measurable fun ω => Y ω i j) :
    Measurable fun ω => fro (Y ω) := by
  unfold fro
  exact Measurable.sqrt (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (hY i j).norm.pow_const 2)

private lemma gi_batch_meas (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    ∀ i j, Measurable fun ω => frozenBatchG F S s ω i j := by
  intro i j
  have hsx : ∀ a : Fin B, ∀ y x,
      Measurable fun ω => sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 y x :=
    fun a y x => (gm_sample_meas F.A y x).comp (S.meas s a)
  simp only [gm_batch_eq, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, gm_lr_apply]
  exact measurable_const.mul (Finset.measurable_sum _ fun a _ =>
    Finset.measurable_sum _ fun y _ => Finset.measurable_sum _ fun x _ =>
      measurable_const.mul (hsx a y x))

private lemma gi_fro_integrable [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) :
    Integrable (fun ω => fro (frozenBatchG F S s ω)) P := by
  have hbound : Integrable (fun ω => ∑ i, ∑ j, ‖frozenBatchG F S s ω i j‖) P :=
    integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
      ((gv_entry_memLp F S s i j).integrable (by norm_num)).norm
  refine hbound.mono' (gi_fro_meas (gi_batch_meas F S s)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have hnn : 0 ≤ fro (frozenBatchG F S s ω) := by unfold fro; exact Real.sqrt_nonneg _
  rw [Real.norm_of_nonneg hnn]
  exact gi_fro_le _

private lemma gi_fro_lint_eq [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) :
    ∫⁻ ω, ENNReal.ofReal (fro (frozenBatchG F S s ω)) ∂P
      = ∫⁻ ω, ENNReal.ofReal (fro (frozenBatchG F S 0 ω)) ∂P := by
  have hmeas : ∀ s', Measurable (frozenBatchG F S s') := fun s' =>
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => gi_batch_meas F S s' i j
  have hent : ∀ i j, Measurable fun K : Mat m n => K i j :=
    fun i j => (measurable_pi_apply j).comp (measurable_pi_apply i)
  have hfK : Measurable fun K : Mat m n => ENNReal.ofReal (fro K) :=
    ENNReal.measurable_ofReal.comp (gi_fro_meas (Y := fun K : Mat m n => K) hent)
  have key : ∀ s', ∫⁻ ω, ENNReal.ofReal (fro (frozenBatchG F S s' ω)) ∂P
      = ∫⁻ K, ENNReal.ofReal (fro K) ∂(P.map (frozenBatchG F S s')) := fun s' =>
    (lintegral_map hfK (hmeas s')).symm
  rw [key s, key 0, (lem_app_setup_gaussian_moments_iii F S).2 s 0]

private lemma gi_fro_series_ae [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) :
    ∀ᵐ ω ∂P, ∀ t : ℤ, Summable fun j : ℕ =>
        fro (emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) := by
  have hC : ∫⁻ ω, ENNReal.ofReal (fro (frozenBatchG F S 0 ω)) ∂P ≠ ⊤ :=
    ne_top_of_lt (gi_fro_integrable F S 0).lintegral_lt_top
  have hnn : ∀ j : ℕ, 0 ≤ emaW F.β j := fun j =>
    mul_nonneg (by linarith [F.hβ.2]) (pow_nonneg F.hβ.1 j)
  have hsum : Summable (fun j : ℕ => emaW F.β j) :=
    (summable_geometric_of_lt_one F.hβ.1 F.hβ.2).mul_left (1 - F.β)
  have hterm : ∀ (t : ℤ) (j : ℕ),
      ∫⁻ ω, ENNReal.ofReal (fro (emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω)) ∂P
        = ENNReal.ofReal (emaW F.β j) * ∫⁻ ω, ENNReal.ofReal (fro (frozenBatchG F S 0 ω)) ∂P := by
    intro t j
    have h1 : ∀ ω, ENNReal.ofReal (fro (emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω))
        = ENNReal.ofReal (|emaW F.β j|) * ENNReal.ofReal (fro (frozenBatchG F S (t + 1 - (j : ℤ)) ω)) :=
      fun ω => by rw [gi_fro_smul, ENNReal.ofReal_mul (abs_nonneg _)]
    have hmeasf : Measurable fun ω =>
        ENNReal.ofReal (fro (frozenBatchG F S (t + 1 - (j : ℤ)) ω)) :=
      ENNReal.measurable_ofReal.comp (gi_fro_meas (gi_batch_meas F S _))
    simp_rw [h1]
    rw [lintegral_const_mul _ hmeasf, gi_fro_lint_eq, abs_of_nonneg (hnn j)]
  refine ae_all_iff.2 fun t => gi_ae_summable (g := fun j ω =>
      fro (emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω)) ?_ ?_ ?_
  · intro j
    exact gi_fro_meas (Y := fun ω => emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω)
      fun i k => (gi_batch_meas F S _ i k).const_mul _
  · intro j ω
    have hnn' : 0 ≤ fro (emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) := by
      unfold fro; exact Real.sqrt_nonneg _
    exact hnn'
  · simp only [hterm]
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg hnn hsum,
      tsum_emaW F.hβ.1 F.hβ.2]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC

/-- `lem:app-setup-ema-law`(ii) first conjunct (the recursion), from the lag decomposition with
`ℓ = 1`: `M_t = β M_{t-1} + (1-β) G_{t+1}` almost surely for all `t`. -/
private lemma gi_recursion_ae [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) :
    ∀ᵐ ω ∂P, ∀ t : ℤ, frozenBuf F S t ω =
      F.β • frozenBuf F S (t - 1) ω + (1 - F.β) • frozenBatchG F S (t + 1) ω := by
  filter_upwards [eqn_app_setup_lag_decomposition F S] with ω hω
  intro t
  have h := hω (t - 1) 1
  have hs : t - 1 + ((1 : ℕ) : ℤ) = t := by push_cast; ring
  have e0 : emaW F.β 0 = 1 - F.β := by simp [emaW]
  rw [hs, Finset.sum_range_one, Nat.cast_zero, sub_zero, e0, pow_one] at h
  exact h

private lemma gi_euc_nonneg {k : ℕ} (z : Vec k) : 0 ≤ eucNorm z := Real.sqrt_nonneg _

private lemma gi_h_le (A : Mat m n) (hA : fro A = 1) (z : Vec m) (w : Vec n) :
    |dotProduct z (Matrix.mulVec A w)| * eucNorm z * eucNorm w
      ≤ (∑ i, z i ^ 2) * (∑ j, w j ^ 2) := by
  have hz : eucNorm z ^ 2 = ∑ i, z i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hw : eucNorm w ^ 2 = ∑ j, w j ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hA2 : ∑ i, ∑ j, A i j ^ 2 = 1 := by
    have h := hA
    unfold fro at h
    have h1 : ∑ i, ∑ j, ‖A i j‖ ^ 2 = 1 := by
      have := Real.sqrt_eq_one.1 h
      exact this
    simpa [Real.norm_eq_abs, sq_abs] using h1
  have hd : dotProduct z (Matrix.mulVec A w) = ∑ p : Fin m × Fin n, A p.1 p.2 * (z p.1 * w p.2) := by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
    (fun p => A p.1 p.2) (fun p => z p.1 * w p.2)
  have e1 : ∑ p : Fin m × Fin n, A p.1 p.2 ^ 2 = 1 := by
    simpa [Fintype.sum_prod_type] using hA2
  have e2 : ∑ p : Fin m × Fin n, (z p.1 * w p.2) ^ 2 = (∑ i, z i ^ 2) * (∑ j, w j ^ 2) := by
    simp only [Fintype.sum_prod_type, Finset.sum_mul_sum, mul_pow]
  rw [e1, e2, one_mul, ← hd] at hcs
  have hn : |dotProduct z (Matrix.mulVec A w)| ≤ eucNorm z * eucNorm w := by
    refine abs_le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    exact le_of_le_of_eq hcs (by rw [mul_pow, hz, hw])
  have h0 : 0 ≤ eucNorm z * eucNorm w := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc |dotProduct z (Matrix.mulVec A w)| * eucNorm z * eucNorm w
      = |dotProduct z (Matrix.mulVec A w)| * (eucNorm z * eucNorm w) := by ring
    _ ≤ (eucNorm z * eucNorm w) * (eucNorm z * eucNorm w) :=
        mul_le_mul_of_nonneg_right hn h0
    _ = (∑ i, z i ^ 2) * (∑ j, w j ^ 2) := by rw [← hz, ← hw]; ring

private lemma gi_h_int (A : Mat m n) (hA : fro A = 1) :
    Integrable (fun x : Vec m × Vec n => |dotProduct x.1 (Matrix.mulVec A x.2)| * eucNorm x.1
      * eucNorm x.2) ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) := by
  have hq : Integrable (fun x : Vec m × Vec n => (∑ i, x.1 i ^ 2) * (∑ j, x.2 j ^ 2))
      ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) := by
    simp only [Finset.sum_mul_sum]
    refine integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => ?_
    have h1 : Integrable (fun z : Vec m => z i ^ 2) (Muon.Foundations.stdGaussianPi m) :=
      gm_coord_pow_integrable m i 2
    have h2 : Integrable (fun w : Vec n => w j ^ 2) (Muon.Foundations.stdGaussianPi n) :=
      gm_coord_pow_integrable n j 2
    exact h1.mul_prod h2
  refine hq.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · unfold eucNorm dotProduct Matrix.mulVec
    exact Continuous.aestronglyMeasurable (by fun_prop)
  · rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (gi_euc_nonneg _))
      (gi_euc_nonneg _))]
    exact gi_h_le A hA x.1 x.2

private lemma gi_sample_series_ae [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) :
    ∀ᵐ ω ∂P, ∀ t : ℤ, Summable fun p : ℕ × Fin B =>
        emaW F.β p.1 *
          |dotProduct (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).1
              (Matrix.mulVec F.A (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).2)| *
          eucNorm (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).1 *
          eucNorm (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).2 := by
  set h : Vec m × Vec n → ℝ := fun x => |dotProduct x.1 (Matrix.mulVec F.A x.2)| * eucNorm x.1
      * eucNorm x.2 with hh
  have hhm : Measurable h := by
    simp only [hh]; unfold eucNorm dotProduct Matrix.mulVec
    fun_prop
  have hhnn : ∀ x, 0 ≤ h x := fun x => mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  set C : ENNReal := ∫⁻ x, ENNReal.ofReal (h x)
    ∂((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) with hC
  have hCfin : C ≠ ⊤ := ne_top_of_lt (gi_h_int F.A F.hA).lintegral_lt_top
  have hnn : ∀ j : ℕ, 0 ≤ emaW F.β j := fun j =>
    mul_nonneg (by linarith [F.hβ.2]) (pow_nonneg F.hβ.1 j)
  have hsum : Summable (fun j : ℕ => emaW F.β j) :=
    (summable_geometric_of_lt_one F.hβ.1 F.hβ.2).mul_left (1 - F.β)
  have hlint : ∀ s a, ∫⁻ ω, ENNReal.ofReal (h (S.zw s a ω)) ∂P = C := by
    intro s a
    rw [hC, ← S.law s a]
    exact (lintegral_map (f := fun x => ENNReal.ofReal (h x))
      (ENNReal.measurable_ofReal.comp hhm) (S.meas s a)).symm
  refine ae_all_iff.2 fun t => gi_ae_summable (g := fun (p : ℕ × Fin B) ω =>
      emaW F.β p.1 * h (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω)) ?_ ?_ ?_ |>.mono fun ω hω => ?_
  · intro p
    exact measurable_const.mul (hhm.comp (S.meas _ _))
  · intro p ω
    exact mul_nonneg (hnn _) (hhnn _)
  · have hterm : ∀ p : ℕ × Fin B, ∫⁻ ω, ENNReal.ofReal (emaW F.β p.1 *
        h (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω)) ∂P = ENNReal.ofReal (emaW F.β p.1) * C := by
      intro p
      simp_rw [ENNReal.ofReal_mul (hnn p.1)]
      have hmz : Measurable fun ω => ENNReal.ofReal (h (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω)) :=
        ENNReal.measurable_ofReal.comp (hhm.comp (S.meas _ _))
      rw [lintegral_const_mul _ hmz, hlint]
    simp only [hterm]
    rw [ENNReal.tsum_mul_right]
    refine ENNReal.mul_ne_top ?_ hCfin
    have htp := ENNReal.tsum_prod (f := fun (a : ℕ) (_ : Fin B) => ENNReal.ofReal (emaW F.β a))
    rw [htp]
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg hnn hsum,
      tsum_emaW F.hβ.1 F.hβ.2]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  · refine hω.congr fun p => ?_
    simp only [hh]; ring

private lemma gi_shift_map {V : Type*} [MeasurableSpace V] (μ0 : Measure V)
    [IsProbabilityMeasure μ0] (k : ℤ) :
    (Measure.infinitePi (fun _ : ℤ × Fin B => μ0)).map
      (fun (x : ℤ × Fin B → V) (p : ℤ × Fin B) => x (p.1 + k, p.2))
      = Measure.infinitePi (fun _ : ℤ × Fin B => μ0) := by
  let e : (ℤ × Fin B) ≃ (ℤ × Fin B) := Equiv.prodCongr (Equiv.addRight (-k)) (Equiv.refl _)
  have h := Measure.infinitePi_map_piCongrLeft (X := fun _ : ℤ × Fin B => V)
    (fun _ => μ0) e
  have hf : (fun (x : ℤ × Fin B → V) (p : ℤ × Fin B) => x (p.1 + k, p.2))
      = ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℤ × Fin B => V) e) := by
    funext x b
    simp only [MeasurableEquiv.coe_piCongrLeft]
    have hb : b = e (b.1 + k, b.2) := by simp [e]
    conv_rhs => rw [hb]
    rw [Equiv.piCongrLeft_apply_apply]
  rw [hf]; exact h

private lemma gi_entry_le_fro {k l : ℕ} (K : Mat k l) (i : Fin k) (j : Fin l) :
    ‖K i j‖ ≤ fro K := by
  unfold fro
  rw [Real.norm_eq_abs]
  refine Real.abs_le_sqrt ?_
  have h1 : ‖K i j‖ ^ 2 ≤ ∑ j', ‖K i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖K i j'‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖K i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖K i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖K i' j'‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  rw [Real.norm_eq_abs, sq_abs] at h1
  simpa [Real.norm_eq_abs, sq_abs] using h1.trans (by simpa [Real.norm_eq_abs, sq_abs] using h2)

private lemma gi_summable_of_fro {k l : ℕ} {f : ℕ → Mat k l}
    (h : Summable fun j => fro (f j)) : Summable f :=
  Pi.summable.2 fun i => Pi.summable.2 fun j =>
    Summable.of_norm_bounded h (fun n => gi_entry_le_fro (f n) i j)

private lemma gi_stationary [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) : StrictlyStationary P (frozenBuf F S) := by
  classical
  set μ0 := (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n) with hμ0
  have : IsProbabilityMeasure μ0 := inferInstance
  set ν0 := Measure.infinitePi (fun _ : ℤ × Fin B => μ0) with hν0
  let X : Ω → (ℤ × Fin B → Vec m × Vec n) := fun ω p => S.zw p.1 p.2 ω
  have hX : Measurable X := measurable_pi_iff.2 fun p : ℤ × Fin B => S.meas p.1 p.2
  have hXlaw : P.map X = ν0 := by
    have := S.indep.map_fun_eq_infinitePi_map (fun p : ℤ × Fin B => S.meas p.1 p.2)
    rw [hν0]
    convert this using 2
    funext p
    exact (S.law p.1 p.2).symm
  let S' : FrozenSamples ν0 m n B :=
    { zw := fun s a x => x (s, a)
      meas := fun s a => measurable_pi_apply (s, a)
      indep := iIndepFun_infinitePi (P := fun _ : ℤ × Fin B => μ0)
        (X := fun _ => id) (fun _ => measurable_id)
      law := fun s a => by
        simpa using Measure.infinitePi_map_eval (fun _ : ℤ × Fin B => μ0) (s, a) }
  have hbm : ∀ s, Measurable (frozenBatchG F S' s) := fun s =>
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => gi_batch_meas F S' s i j
  let Φ : (ℤ × Fin B → Vec m × Vec n) → ℤ → Mat m n := fun x t =>
    Matrix.of fun i k => limUnder Filter.atTop (fun N : ℕ => ∑ j ∈ Finset.range N,
      emaW F.β j * frozenBatchG F S' (t + 1 - (j : ℤ)) x i k)
  have hΦ : Measurable Φ := by
    refine measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
    have hf : ∀ N : ℕ, MeasureTheory.StronglyMeasurable
        (fun x : ℤ × Fin B → Vec m × Vec n => ∑ j ∈ Finset.range N,
          emaW F.β j * frozenBatchG F S' (t + 1 - (j : ℤ)) x i k) := fun N =>
      (Finset.measurable_sum _ fun j _ => (gi_batch_meas F S' _ i k).const_mul _).stronglyMeasurable
    exact (MeasureTheory.StronglyMeasurable.limUnder (l := Filter.atTop) hf).measurable
  have hA : ∀ᵐ ω ∂P, ∀ t, frozenBuf F S t ω = Φ (X ω) t := by
    filter_upwards [gi_fro_series_ae F S] with ω hω t
    have hs := gi_summable_of_fro (hω t)
    funext i k
    show (∑' j : ℕ, emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) i k = _
    rw [← (Pi.hasSum.1 (Pi.hasSum.1 hs.hasSum i) k).tsum_eq]
    have hsk : Summable fun j : ℕ => (emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) i k :=
      Summable.of_norm_bounded (hω t) (fun j => gi_entry_le_fro _ i k)
    simp only [Matrix.smul_apply, smul_eq_mul] at hsk ⊢
    exact (hsk.hasSum.tendsto_sum_nat.limUnder_eq).symm
  have hB : ∀ (k : ℤ) x t, Φ (fun p => x (p.1 + k, p.2)) t = Φ x (t + k) := by
    intro k x t
    funext i l
    simp only [Φ, Matrix.of_apply]
    congr 1
    funext N
    refine Finset.sum_congr rfl fun j _ => ?_
    show emaW F.β j * frozenBatchG F S' (t + 1 - (j : ℤ) + k) x i l = _
    rw [show t + 1 - (j : ℤ) + k = t + k + 1 - (j : ℤ) by ring]
  have hΦX : Measurable fun ω => Φ (X ω) := hΦ.comp hX
  refine ⟨?_, fun k => ?_⟩
  · refine hΦX.aemeasurable.congr ?_
    filter_upwards [hA] with ω hω
    funext t
    exact (hω t).symm
  · have hσ : Measurable fun (x : ℤ × Fin B → Vec m × Vec n) (p : ℤ × Fin B) => x (p.1 + k, p.2) :=
      measurable_pi_iff.2 fun p => measurable_pi_apply _
    have e1 : P.map (fun ω t => frozenBuf F S (t + k) ω)
        = P.map (fun ω => Φ (fun p => X ω (p.1 + k, p.2))) := by
      refine Measure.map_congr ?_
      filter_upwards [hA] with ω hω
      funext t
      rw [hB, hω]
    have e2 : P.map (fun ω t => frozenBuf F S t ω) = P.map (fun ω => Φ (X ω)) := by
      refine Measure.map_congr ?_
      filter_upwards [hA] with ω hω
      funext t
      exact hω t
    rw [e1, e2]
    have e3 : P.map (fun ω => Φ (fun p => X ω (p.1 + k, p.2)))
        = (P.map X).map (fun x => Φ (fun p => x (p.1 + k, p.2))) :=
      (Measure.map_map (hΦ.comp hσ) hX).symm
    have e4 : P.map (fun ω => Φ (X ω)) = (P.map X).map Φ := (Measure.map_map hΦ hX).symm
    rw [e3, e4, hXlaw]
    have e5 : ν0.map (fun x => Φ (fun p => x (p.1 + k, p.2)))
        = (ν0.map (fun (x : ℤ × Fin B → Vec m × Vec n) (p : ℤ × Fin B) => x (p.1 + k, p.2))).map Φ :=
      (Measure.map_map hΦ hσ).symm
    rw [e5, hν0, gi_shift_map μ0 k]

/-- `lem:app-setup-ema-law`(i): a.s. absolute convergence of the buffer series and of the sample
series. Declaration of record of part (i). The full environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Stationary EMA law]\label{lem:app-setup-ema-law}
In the frozen-state model, index the samples by time as above, and write
$\Sigma_G\defeq\Cov(\operatorname{vec}\Gt)$ for the batch covariance
\cref{eqn:app-setup-batch-cov}.
\begin{enumerate}[label=(\roman*)]
\item The series $\Mt=\sum_{j\ge0}\emaw{j}G_{t+1-j}$ and the sample series
$\sum_{j,a}\emaw{j}\abs{d_{ja}}\norm{z_{ja}}\norm{w_{ja}}$ converge absolutely.
\item For every integer $t$, $\Mt=\bmom M_{t-1}+(1-\bmom)\Gt$,
and the sequence $(\Mt)_{t\in\mathbb Z}$ is strictly stationary.
\item $\EE\Mt=\EE\Gt$, $\Cov(\operatorname{vec}\Mt)=\sw2\,\Sigma_G$, and
$\EE\norm{\Mt-\EE\Gt}_\F^2=\sw2\,\mathsf V_B$.
\item For every lag $\ell\ge0$,
$\Cov(\operatorname{vec}\Mt,\operatorname{vec}M_{t+\ell})=\bmom^\ell\,\sw2\,\Sigma_G$.
\item For every positive integer $T$,
\begin{equation}\label{eqn:app-setup-block-cov}
\Cov\Big(\sum_{t=1}^T\operatorname{vec}(\Mt-\EE\Gt)\Big)
=\sw2\Big[T+2\sum_{\ell=1}^{T-1}(T-\ell)\bmom^\ell\Big]\Sigma_G
=\Big[T-\frac{2\bmom(1-\bmom^T)}{1-\bmom^2}\Big]\Sigma_G ,
\end{equation}
the two-sided lag sum $\sum_{\ell\in\mathbb Z}\Cov(\operatorname{vec}\Mt,\operatorname{vec}M_{t+\ell})$
converges absolutely and equals $\Sigma_G$, and
$T^{-1}\Cov(\sum_{t\le T}\operatorname{vec}(\Mt-\EE\Gt))\to\Sigma_G$ as $T\to\infty$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_setup_ema_law_i [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) :
    (∀ᵐ ω ∂P, ∀ t : ℤ, Summable fun j : ℕ =>
        fro (emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℤ, Summable fun p : ℕ × Fin B =>
        emaW F.β p.1 *
          |dotProduct (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).1
              (Matrix.mulVec F.A (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).2)| *
          eucNorm (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).1 *
          eucNorm (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).2) := by
  exact ⟨gi_fro_series_ae F S, gi_sample_series_ae F S⟩

/-- `lem:app-setup-ema-law`(ii): the a.s. recursion `M_t = β M_{t-1} + (1-β) G_{t+1}` for all
`t ∈ ℤ`, and strict stationarity of `(M_t)_{t ∈ ℤ}`. Declaration of record of part (ii). The full
environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Stationary EMA law]\label{lem:app-setup-ema-law}
In the frozen-state model, index the samples by time as above, and write
$\Sigma_G\defeq\Cov(\operatorname{vec}\Gt)$ for the batch covariance
\cref{eqn:app-setup-batch-cov}.
\begin{enumerate}[label=(\roman*)]
\item The series $\Mt=\sum_{j\ge0}\emaw{j}G_{t+1-j}$ and the sample series
$\sum_{j,a}\emaw{j}\abs{d_{ja}}\norm{z_{ja}}\norm{w_{ja}}$ converge absolutely.
\item For every integer $t$, $\Mt=\bmom M_{t-1}+(1-\bmom)\Gt$,
and the sequence $(\Mt)_{t\in\mathbb Z}$ is strictly stationary.
\item $\EE\Mt=\EE\Gt$, $\Cov(\operatorname{vec}\Mt)=\sw2\,\Sigma_G$, and
$\EE\norm{\Mt-\EE\Gt}_\F^2=\sw2\,\mathsf V_B$.
\item For every lag $\ell\ge0$,
$\Cov(\operatorname{vec}\Mt,\operatorname{vec}M_{t+\ell})=\bmom^\ell\,\sw2\,\Sigma_G$.
\item For every positive integer $T$,
\begin{equation}\label{eqn:app-setup-block-cov}
\Cov\Big(\sum_{t=1}^T\operatorname{vec}(\Mt-\EE\Gt)\Big)
=\sw2\Big[T+2\sum_{\ell=1}^{T-1}(T-\ell)\bmom^\ell\Big]\Sigma_G
=\Big[T-\frac{2\bmom(1-\bmom^T)}{1-\bmom^2}\Big]\Sigma_G ,
\end{equation}
the two-sided lag sum $\sum_{\ell\in\mathbb Z}\Cov(\operatorname{vec}\Mt,\operatorname{vec}M_{t+\ell})$
converges absolutely and equals $\Sigma_G$, and
$T^{-1}\Cov(\sum_{t\le T}\operatorname{vec}(\Mt-\EE\Gt))\to\Sigma_G$ as $T\to\infty$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_setup_ema_law_ii [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) :
    (∀ᵐ ω ∂P, ∀ t : ℤ, frozenBuf F S t ω =
        F.β • frozenBuf F S (t - 1) ω + (1 - F.β) • frozenBatchG F S (t + 1) ω) ∧
      StrictlyStationary P (frozenBuf F S) := by
  exact ⟨gi_recursion_ae F S, gi_stationary F S⟩

private lemma gl_holder {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    |∫ ω, f ω * g ω ∂P| ≤
      (∫ ω, f ω ^ 2 ∂P) ^ ((1 : ℝ) / 2) * (∫ ω, g ω ^ 2 ∂P) ^ ((1 : ℝ) / 2) := by
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hf' : MemLp (fun ω => ‖f ω‖) (ENNReal.ofReal 2) P := by rw [h2]; exact hf.norm
  have hg' : MemLp (fun ω => ‖g ω‖) (ENNReal.ofReal 2) P := by rw [h2]; exact hg.norm
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) (p := 2) (q := 2)
    Real.HolderConjugate.two_two
    (Eventually.of_forall fun ω => norm_nonneg (f ω))
    (Eventually.of_forall fun ω => norm_nonneg (g ω)) hf' hg'
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs] at key
  calc |∫ ω, f ω * g ω ∂P| ≤ ∫ ω, ‖f ω * g ω‖ ∂P := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ = ∫ ω, ‖f ω‖ * ‖g ω‖ ∂P := by simp only [norm_mul]
    _ ≤ _ := key

private lemma gl_integral_tendsto [IsProbabilityMeasure P] {f : ℕ → Ω → ℝ} {fL : Ω → ℝ}
    (hf : ∀ N, MemLp (f N) 2 P) (hfL : MemLp fL 2 P)
    (hlim : Tendsto (fun N => ∫ ω, (f N ω - fL ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun N => ∫ ω, f N ω ∂P) atTop (𝓝 (∫ ω, fL ω ∂P)) := by
  have hbound : ∀ N, |∫ ω, f N ω ∂P - ∫ ω, fL ω ∂P|
      ≤ (∫ ω, (f N ω - fL ω) ^ 2 ∂P) ^ ((1 : ℝ) / 2) := by
    intro N
    have hd : MemLp (fun ω => f N ω - fL ω) 2 P := (hf N).sub hfL
    have h1 := gl_holder (g := fun _ => (1 : ℝ)) hd (memLp_const (1 : ℝ))
    have hint : ∫ ω, (f N ω - fL ω) * 1 ∂P = ∫ ω, f N ω ∂P - ∫ ω, fL ω ∂P := by
      simp only [mul_one]
      exact integral_sub ((hf N).integrable (by norm_num)) (hfL.integrable (by norm_num))
    rw [← hint]
    simpa using h1
  have hlim' : Tendsto (fun N => (∫ ω, (f N ω - fL ω) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) atTop (𝓝 0) := by
    have := hlim.rpow_const (p := (1 : ℝ) / 2) (Or.inr (by norm_num))
    simpa [Real.zero_rpow (by norm_num : (1 : ℝ) / 2 ≠ 0)] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hlim'
  rw [Real.norm_eq_abs]
  exact hbound N

private lemma gl_L2_of_cauchy [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {XL : Ω → ℝ}
    (hX : ∀ N, MemLp (X N) 2 P) (hmeasL : AEStronglyMeasurable XL P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun N => X N ω) atTop (𝓝 (XL ω)))
    {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    (hcauchy : ∀ N M, N ≤ M → ∫ ω, (X M ω - X N ω) ^ 2 ∂P ≤ c N) :
    MemLp XL 2 P ∧ Tendsto (fun N => ∫ ω, (X N ω - XL ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hcnn : ∀ N, 0 ≤ c N := fun N =>
    (integral_nonneg fun ω => sq_nonneg _).trans (hcauchy N N le_rfl)
  have hmeasDiff : ∀ N M, AEMeasurable (fun ω => ENNReal.ofReal ((X M ω - X N ω) ^ 2)) P :=
    fun N M => (((hX M).aemeasurable.sub (hX N).aemeasurable).pow_const 2).ennreal_ofReal
  have hN : ∀ N, ∫⁻ ω, ENNReal.ofReal ((XL ω - X N ω) ^ 2) ∂P ≤ ENNReal.ofReal (c N) := by
    intro N
    have h1 : ∫⁻ ω, ENNReal.ofReal ((XL ω - X N ω) ^ 2) ∂P
        ≤ liminf (fun M => ∫⁻ ω, ENNReal.ofReal ((X M ω - X N ω) ^ 2) ∂P) atTop := by
      calc _ = ∫⁻ ω, liminf (fun M => ENNReal.ofReal ((X M ω - X N ω) ^ 2)) atTop ∂P := by
            refine lintegral_congr_ae ?_
            filter_upwards [hae] with ω hω
            refine (Tendsto.liminf_eq ?_).symm
            exact (ENNReal.continuous_ofReal.tendsto _).comp ((hω.sub_const (X N ω)).pow 2)
        _ ≤ _ := lintegral_liminf_le' fun M => hmeasDiff N M
    have h2 : liminf (fun M => ∫⁻ ω, ENNReal.ofReal ((X M ω - X N ω) ^ 2) ∂P) atTop
        ≤ ENNReal.ofReal (c N) := by
      have hev : ∀ᶠ M in atTop, ∫⁻ ω, ENNReal.ofReal ((X M ω - X N ω) ^ 2) ∂P
          ≤ ENNReal.ofReal (c N) := by
        filter_upwards [eventually_ge_atTop N] with M hM
        have hint : Integrable (fun ω => (X M ω - X N ω) ^ 2) P :=
          ((hX M).sub (hX N)).integrable_sq
        rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hcauchy N M hM)
      calc _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal (c N)) atTop := Filter.liminf_le_liminf hev
        _ = _ := liminf_const _
    exact h1.trans h2
  have hL : ∀ N, MemLp (fun ω => XL ω - X N ω) 2 P := by
    intro N
    refine (memLp_two_iff_integrable_sq ((hmeasL.sub (hX N).aestronglyMeasurable))).2 ⟨?_, ?_⟩
    · exact ((hmeasL.sub (hX N).aestronglyMeasurable)).pow 2
    · refine (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _)).2 ?_
      exact lt_of_le_of_lt (hN N) ENNReal.ofReal_lt_top
  have hXL : MemLp XL 2 P := by
    have h : MemLp (fun ω => (XL ω - X 0 ω) + X 0 ω) 2 P := (hL 0).add (hX 0)
    have e : (fun ω => (XL ω - X 0 ω) + X 0 ω) = XL := by funext ω; ring
    rw [e] at h
    exact h
  have hbd : ∀ N, ∫ ω, (XL ω - X N ω) ^ 2 ∂P ≤ c N := by
    intro N
    have hnn : 0 ≤ᵐ[P] fun ω => (XL ω - X N ω) ^ 2 :=
      Eventually.of_forall fun ω => sq_nonneg _
    have hm : AEStronglyMeasurable (fun ω => (XL ω - X N ω) ^ 2) P :=
      (hL N).aestronglyMeasurable.pow 2
    rw [integral_eq_lintegral_of_nonneg_ae hnn hm]
    calc _ ≤ (ENNReal.ofReal (c N)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hN N)
      _ = c N := ENNReal.toReal_ofReal (hcnn N)
  have e : (fun N => ∫ ω, (X N ω - XL ω) ^ 2 ∂P) = fun N => ∫ ω, (XL ω - X N ω) ^ 2 ∂P := by
    funext N; congr 1; funext ω; ring
  refine ⟨hXL, ?_⟩
  rw [e]
  exact squeeze_zero (fun N => integral_nonneg fun ω => sq_nonneg _) hbd hc

private lemma gl_cov_tendsto [IsProbabilityMeasure P] {X Y : ℕ → Ω → ℝ} {XL YL : Ω → ℝ}
    (hX : ∀ N, MemLp (X N) 2 P) (hY : ∀ N, MemLp (Y N) 2 P)
    (hXL : MemLp XL 2 P) (hYL : MemLp YL 2 P)
    (hXl : Tendsto (fun N => ∫ ω, (X N ω - XL ω) ^ 2 ∂P) atTop (𝓝 0))
    (hYl : Tendsto (fun N => ∫ ω, (Y N ω - YL ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun N => covariance (X N) (Y N) P) atTop (𝓝 (covariance XL YL P)) := by
  have hXi := gl_integral_tendsto hX hXL hXl
  have hYi := gl_integral_tendsto hY hYL hYl
  have hu : Tendsto (fun N => (∫ ω, (X N ω - XL ω) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) atTop (𝓝 0) := by
    have := hXl.rpow_const (p := (1 : ℝ) / 2) (Or.inr (by norm_num))
    simpa [Real.zero_rpow (by norm_num : (1 : ℝ) / 2 ≠ 0)] using this
  have hv : Tendsto (fun N => (∫ ω, (Y N ω - YL ω) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) atTop (𝓝 0) := by
    have := hYl.rpow_const (p := (1 : ℝ) / 2) (Or.inr (by norm_num))
    simpa [Real.zero_rpow (by norm_num : (1 : ℝ) / 2 ≠ 0)] using this
  set e := (∫ ω, (YL ω) ^ 2 ∂P) ^ ((1 : ℝ) / 2) with he
  set d := (∫ ω, (XL ω) ^ 2 ∂P) ^ ((1 : ℝ) / 2) with hd
  have hprod : Tendsto (fun N => ∫ ω, X N ω * Y N ω ∂P) atTop (𝓝 (∫ ω, XL ω * YL ω ∂P)) := by
    have hsplit : ∀ N, ∫ ω, X N ω * Y N ω ∂P - ∫ ω, XL ω * YL ω ∂P
        = ∫ ω, (X N ω - XL ω) * (Y N ω - YL ω) ∂P
          + (∫ ω, (X N ω - XL ω) * YL ω ∂P + ∫ ω, XL ω * (Y N ω - YL ω) ∂P) := by
      intro N
      have hA : Integrable (fun ω => (X N ω - XL ω) * (Y N ω - YL ω)) P :=
        ((hX N).sub hXL).integrable_mul ((hY N).sub hYL)
      have hB : Integrable (fun ω => (X N ω - XL ω) * YL ω) P :=
        ((hX N).sub hXL).integrable_mul hYL
      have hC : Integrable (fun ω => XL ω * (Y N ω - YL ω)) P :=
        hXL.integrable_mul ((hY N).sub hYL)
      have hXY : Integrable (fun ω => X N ω * Y N ω) P := (hX N).integrable_mul (hY N)
      have hXY' : Integrable (fun ω => XL ω * YL ω) P := hXL.integrable_mul hYL
      calc ∫ ω, X N ω * Y N ω ∂P - ∫ ω, XL ω * YL ω ∂P
          = ∫ ω, (X N ω * Y N ω - XL ω * YL ω) ∂P := (integral_sub hXY hXY').symm
        _ = ∫ ω, ((X N ω - XL ω) * (Y N ω - YL ω)
              + ((X N ω - XL ω) * YL ω + XL ω * (Y N ω - YL ω))) ∂P := by
            congr 1; funext ω; ring
        _ = _ := by
            have hBC : Integrable (fun ω => (X N ω - XL ω) * YL ω + XL ω * (Y N ω - YL ω)) P :=
              hB.add hC
            rw [integral_add hA hBC, integral_add hB hC]
    have hA_bd : ∀ N, |∫ ω, (X N ω - XL ω) * (Y N ω - YL ω) ∂P|
        ≤ (∫ ω, (X N ω - XL ω) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
          * (∫ ω, (Y N ω - YL ω) ^ 2 ∂P) ^ ((1 : ℝ) / 2) :=
      fun N => gl_holder ((hX N).sub hXL) ((hY N).sub hYL)
    have hB_bd : ∀ N, |∫ ω, (X N ω - XL ω) * YL ω ∂P|
        ≤ (∫ ω, (X N ω - XL ω) ^ 2 ∂P) ^ ((1 : ℝ) / 2) * e :=
      fun N => gl_holder ((hX N).sub hXL) hYL
    have hC_bd : ∀ N, |∫ ω, XL ω * (Y N ω - YL ω) ∂P|
        ≤ d * (∫ ω, (Y N ω - YL ω) ^ 2 ∂P) ^ ((1 : ℝ) / 2) :=
      fun N => gl_holder hXL ((hY N).sub hYL)
    have hbound : Tendsto (fun N => (∫ ω, (X N ω - XL ω) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
          * (∫ ω, (Y N ω - YL ω) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
        + ((∫ ω, (X N ω - XL ω) ^ 2 ∂P) ^ ((1 : ℝ) / 2) * e
        + d * (∫ ω, (Y N ω - YL ω) ^ 2 ∂P) ^ ((1 : ℝ) / 2))) atTop (𝓝 0) := by
      have := ((hu.mul hv).add ((hu.mul_const e).add (hv.const_mul d)))
      simpa using this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hbound
    rw [Real.norm_eq_abs, hsplit N]
    have h3 := abs_add_three (∫ ω, (X N ω - XL ω) * (Y N ω - YL ω) ∂P)
      (∫ ω, (X N ω - XL ω) * YL ω ∂P) (∫ ω, XL ω * (Y N ω - YL ω) ∂P)
    have h4 : |∫ ω, (X N ω - XL ω) * YL ω ∂P + ∫ ω, XL ω * (Y N ω - YL ω) ∂P|
        ≤ |∫ ω, (X N ω - XL ω) * YL ω ∂P| + |∫ ω, XL ω * (Y N ω - YL ω) ∂P| :=
      abs_add_le _ _
    have h5 := hA_bd N
    have h6 := hB_bd N
    have h7 := hC_bd N
    calc _ ≤ |∫ ω, (X N ω - XL ω) * (Y N ω - YL ω) ∂P|
          + (|∫ ω, (X N ω - XL ω) * YL ω ∂P| + |∫ ω, XL ω * (Y N ω - YL ω) ∂P|) := by
          exact (abs_add_le _ _).trans (by linarith)
      _ ≤ _ := by linarith
  have hcov1 : ∀ N, covariance (X N) (Y N) P
      = ∫ ω, X N ω * Y N ω ∂P - (∫ ω, X N ω ∂P) * ∫ ω, Y N ω ∂P :=
    fun N => covariance_eq_sub (hX N) (hY N)
  have hcov2 : covariance XL YL P = ∫ ω, XL ω * YL ω ∂P - (∫ ω, XL ω ∂P) * ∫ ω, YL ω ∂P :=
    covariance_eq_sub hXL hYL
  simp only [hcov1, hcov2]
  exact hprod.sub (hXi.mul hYi)


private lemma gl_cov_add_fun [IsProbabilityMeasure P] {X Y Z : Ω → ℝ} (hX : MemLp X 2 P)
    (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P) :
    covariance X (fun ω => Y ω + Z ω) P = covariance X Y P + covariance X Z P :=
  covariance_add_right hX hY hZ

private lemma gl_cov_congr_right {X Y Y' : Ω → ℝ} (h : Y =ᵐ[P] Y') :
    covariance X Y P = covariance X Y' P := by
  unfold covariance
  have hm : ∫ ω, Y ω ∂P = ∫ ω, Y' ω ∂P := integral_congr_ae h
  rw [hm]
  refine integral_congr_ae ?_
  filter_upwards [h] with ω hω
  rw [hω]

private lemma gl_cov_self_of_mean_zero {W : Ω → ℝ} (hW : ∫ ω, W ω ∂P = 0) :
    ∫ ω, W ω ^ 2 ∂P = covariance W W P := by
  unfold covariance
  rw [hW]
  simp [sq]

private lemma gl_cov_indep_gen [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {s s' : ℤ} (hss : s ≠ s') (a : Fin m) (b : Fin n)
    (c : Fin m) (d : Fin n) :
    covariance (fun ω => frozenBatchG F S s ω a b) (fun ω => frozenBatchG F S s' ω c d) P = 0 := by
  have hI := (lem_app_setup_gaussian_moments_iii F S).1.indepFun hss
  have hφ : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => M a b) :=
    (measurable_pi_apply b).comp (measurable_pi_apply a)
  have hψ : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => M c d) :=
    (measurable_pi_apply d).comp (measurable_pi_apply c)
  exact (hI.comp hφ hψ).covariance_eq_zero (gv_entry_memLp F S s a b) (gv_entry_memLp F S s' c d)

private lemma gl_cov_same_time [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (a : Fin m) (b : Fin n) (c : Fin m) (d : Fin n) :
    covariance (fun ω => frozenBatchG F S s ω a b) (fun ω => frozenBatchG F S s ω c d) P
      = SigmaG S F a b c d := by
  have hmeas : ∀ s', Measurable (frozenBatchG F S s') := fun s' =>
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => gi_batch_meas F S s' i j
  have hφ : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => M a b) :=
    (measurable_pi_apply b).comp (measurable_pi_apply a)
  have hψ : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => M c d) :=
    (measurable_pi_apply d).comp (measurable_pi_apply c)
  have e : ∀ s', covariance (fun ω => frozenBatchG F S s' ω a b)
      (fun ω => frozenBatchG F S s' ω c d) P
      = covariance (fun M : Matrix (Fin m) (Fin n) ℝ => M a b) (fun M => M c d)
          (P.map (frozenBatchG F S s')) := by
    intro s'
    rw [covariance_map hφ.aestronglyMeasurable hψ.aestronglyMeasurable (hmeas s').aemeasurable]
    rfl
  rw [e s, (lem_app_setup_gaussian_moments_iii F S).2 s 0, ← e 0]
  rfl

private lemma gl_int_entry [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (a : Fin m) (b : Fin n) :
    ∫ ω, frozenBatchG F S s ω a b ∂P = (rOut F.C * F.A * rIn F.C) a b := by
  have := congrFun (congrFun (gm_batch_mean F S s) a) b
  simpa only [mean, Matrix.of_apply] using this

private lemma gl_Z_mean [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (s : Finset ℕ) (a : Fin m) (b : Fin n) :
    ∫ ω, (∑ j ∈ s, emaW F.β j * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b
      - (rOut F.C * F.A * rIn F.C) a b)) ∂P = 0 := by
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul, integral_sub ((gv_entry_memLp F S _ a b).integrable (by norm_num)) (integrable_const _),
      gl_int_entry F S, integral_const]
    simp
  · intro j _
    exact (((gv_entry_memLp F S _ a b).integrable (by norm_num)).sub (integrable_const _)).const_mul _

private lemma gl_Z_cov [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (s : Finset ℕ) (a : Fin m) (b : Fin n)
    (c : Fin m) (d : Fin n) :
    covariance (fun ω => ∑ j ∈ s, emaW F.β j * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b
        - (rOut F.C * F.A * rIn F.C) a b))
      (fun ω => ∑ j ∈ s, emaW F.β j * (frozenBatchG F S (t + 1 - (j : ℤ)) ω c d
        - (rOut F.C * F.A * rIn F.C) c d)) P
      = (∑ j ∈ s, emaW F.β j ^ 2) * SigmaG S F a b c d := by
  have hX : ∀ j : ℕ, MemLp (fun ω => emaW F.β j * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b
      - (rOut F.C * F.A * rIn F.C) a b)) 2 P := fun j =>
    ((gv_entry_memLp F S _ a b).sub (memLp_const _)).const_mul _
  have hY : ∀ j : ℕ, MemLp (fun ω => emaW F.β j * (frozenBatchG F S (t + 1 - (j : ℤ)) ω c d
      - (rOut F.C * F.A * rIn F.C) c d)) 2 P := fun j =>
    ((gv_entry_memLp F S _ c d).sub (memLp_const _)).const_mul _
  rw [covariance_fun_sum_fun_sum' (fun j _ => hX j) (fun j _ => hY j)]
  have hcross : ∀ j ∈ s, ∀ j' ∈ s,
      covariance (fun ω => emaW F.β j * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b
        - (rOut F.C * F.A * rIn F.C) a b))
        (fun ω => emaW F.β j' * (frozenBatchG F S (t + 1 - (j' : ℤ)) ω c d
        - (rOut F.C * F.A * rIn F.C) c d)) P
      = if j = j' then emaW F.β j ^ 2 * SigmaG S F a b c d else 0 := by
    intro j _ j' _
    have hI1 := (gv_entry_memLp F S (t + 1 - (j : ℤ)) a b).integrable (by norm_num)
    have hI2 := (gv_entry_memLp F S (t + 1 - (j' : ℤ)) c d).integrable (by norm_num)
    rw [covariance_const_mul_left, covariance_const_mul_right, covariance_sub_const_left hI1,
      covariance_sub_const_right hI2]
    by_cases h : j = j'
    · subst h
      rw [if_pos rfl, gl_cov_same_time F S _ a b c d]
      ring
    · rw [if_neg h, gl_cov_indep_gen F S (by omega) a b c d, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun j' hj' => hcross j hj j' hj']
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_ite_eq, if_pos hj]

private lemma gl_partial_ae [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N,
        emaW F.β j • (frozenBatchG F S (t + 1 - (j : ℤ)) ω - rOut F.C * F.A * rIn F.C))
      atTop (𝓝 (frozenBuf F S t ω - rOut F.C * F.A * rIn F.C)) := by
  filter_upwards [gi_fro_series_ae F S] with ω hω
  have hs : Summable (fun j : ℕ => emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) :=
    gi_summable_of_fro (hω t)
  have hW : Summable (fun j : ℕ => emaW F.β j) :=
    (summable_geometric_of_lt_one F.hβ.1 F.hβ.2).mul_left (1 - F.β)
  have h1 := hs.hasSum.tendsto_sum_nat
  have h2 := hW.hasSum.tendsto_sum_nat
  rw [tsum_emaW F.hβ.1 F.hβ.2] at h2
  have h3 := h1.sub (h2.smul_const (rOut F.C * F.A * rIn F.C))
  rw [one_smul] at h3
  have hfun : ∀ N : ℕ, ∑ j ∈ Finset.range N, emaW F.β j
      • (frozenBatchG F S (t + 1 - (j : ℤ)) ω - rOut F.C * F.A * rIn F.C)
      = (∑ j ∈ Finset.range N, emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω)
        - (∑ j ∈ Finset.range N, emaW F.β j) • (rOut F.C * F.A * rIn F.C) := by
    intro N
    rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => smul_sub _ _ _
  simp_rw [hfun]
  exact h3

private lemma gl_entry_L2 [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (a : Fin m) (b : Fin n) :
    MemLp (fun ω => frozenBuf F S t ω a b - (rOut F.C * F.A * rIn F.C) a b) 2 P ∧
    Tendsto (fun N : ℕ => ∫ ω, (∑ j ∈ Finset.range N, emaW F.β j
        * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b)
        - (frozenBuf F S t ω a b - (rOut F.C * F.A * rIn F.C) a b)) ^ 2 ∂P) atTop (𝓝 0) := by
  have hZmem : ∀ N : ℕ, MemLp (fun ω => ∑ j ∈ Finset.range N, emaW F.β j
      * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b)) 2 P :=
    fun N => memLp_finsetSum _ fun j _ =>
      ((gv_entry_memLp F S _ a b).sub (memLp_const _)).const_mul _
  have hae : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, emaW F.β j
      * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b))
      atTop (𝓝 (frozenBuf F S t ω a b - (rOut F.C * F.A * rIn F.C) a b)) := by
    filter_upwards [gl_partial_ae F S t] with ω hω
    have := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hω a) b
    simpa [Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] using this
  have hmeasL : AEStronglyMeasurable (fun ω => frozenBuf F S t ω a b
      - (rOut F.C * F.A * rIn F.C) a b) P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun N => (hZmem N).aestronglyMeasurable) hae
  have hsq : Summable fun j : ℕ => emaW F.β j ^ 2 := by
    refine Summable.congr ((summable_geometric_of_lt_one (sq_nonneg F.β)
      (pow_lt_one₀ F.hβ.1 F.hβ.2 two_ne_zero)).mul_left ((1 - F.β) ^ 2)) fun j => ?_
    unfold emaW; ring
  have hS2 : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, emaW F.β j ^ 2) atTop
      (𝓝 (sPow F.β 2)) := by
    unfold sPow; exact hsq.hasSum.tendsto_sum_nat
  set σ := SigmaG S F a b a b with hσ
  have htail : Tendsto (fun N : ℕ => sPow F.β 2 - ∑ j ∈ Finset.range N, emaW F.β j ^ 2) atTop
      (𝓝 0) := by
    have := (tendsto_const_nhds (x := sPow F.β 2)).sub hS2
    simpa using this
  have hc : Tendsto (fun N : ℕ => |σ| * (sPow F.β 2 - ∑ j ∈ Finset.range N, emaW F.β j ^ 2))
      atTop (𝓝 0) := by
    have := htail.const_mul |σ|
    rwa [mul_zero] at this
  have hcauchy : ∀ N M : ℕ, N ≤ M → ∫ ω, ((∑ j ∈ Finset.range M, emaW F.β j
      * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b))
      - (∑ j ∈ Finset.range N, emaW F.β j
      * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b))) ^ 2 ∂P
      ≤ |σ| * (sPow F.β 2 - ∑ j ∈ Finset.range N, emaW F.β j ^ 2) := by
    intro N M hNM
    have hsplit : ∀ ω, (∑ j ∈ Finset.range M, emaW F.β j
        * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b))
        - (∑ j ∈ Finset.range N, emaW F.β j
        * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b))
        = ∑ j ∈ Finset.Ico N M, emaW F.β j
        * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b) := by
      intro ω
      rw [← Finset.sum_range_add_sum_Ico _ hNM]
      ring
    have hfun : (fun ω => (∑ j ∈ Finset.range M, emaW F.β j
        * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b))
        - (∑ j ∈ Finset.range N, emaW F.β j
        * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b)))
        = fun ω => ∑ j ∈ Finset.Ico N M, emaW F.β j
        * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b) :=
      funext hsplit
    have hmean : ∫ ω, ((∑ j ∈ Finset.range M, emaW F.β j
        * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b))
        - (∑ j ∈ Finset.range N, emaW F.β j
        * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b))) ∂P = 0 := by
      rw [hfun]
      exact gl_Z_mean F S t _ a b
    rw [gl_cov_self_of_mean_zero hmean]
    have hcv : covariance (fun ω => (∑ j ∈ Finset.range M, emaW F.β j
        * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b))
        - (∑ j ∈ Finset.range N, emaW F.β j
        * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b)))
        (fun ω => (∑ j ∈ Finset.range M, emaW F.β j
        * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b))
        - (∑ j ∈ Finset.range N, emaW F.β j
        * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b))) P
        = (∑ j ∈ Finset.Ico N M, emaW F.β j ^ 2) * σ := by
      rw [hfun]
      exact gl_Z_cov F S t _ a b a b
    rw [hcv]
    have hT0 : 0 ≤ ∑ j ∈ Finset.Ico N M, emaW F.β j ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have hTle : ∑ j ∈ Finset.Ico N M, emaW F.β j ^ 2
        ≤ sPow F.β 2 - ∑ j ∈ Finset.range N, emaW F.β j ^ 2 := by
      have h1 := Finset.sum_range_add_sum_Ico (fun j => emaW F.β j ^ 2) hNM
      have h2 : ∑ j ∈ Finset.range M, emaW F.β j ^ 2 ≤ sPow F.β 2 := by
        unfold sPow
        exact sum_le_hasSum _ (fun j _ => sq_nonneg _) hsq.hasSum
      linarith
    have h3 : (∑ j ∈ Finset.Ico N M, emaW F.β j ^ 2) * σ
        ≤ |σ| * (∑ j ∈ Finset.Ico N M, emaW F.β j ^ 2) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hT0
    exact h3.trans (mul_le_mul_of_nonneg_left hTle (abs_nonneg _))
  obtain ⟨hL, hlim⟩ := gl_L2_of_cauchy hZmem hmeasL hae hc hcauchy
  exact ⟨hL, hlim⟩

private lemma gl_Z_memLp [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (s : Finset ℕ) (a : Fin m) (b : Fin n) :
    MemLp (fun ω => ∑ j ∈ s, emaW F.β j * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b
      - (rOut F.C * F.A * rIn F.C) a b)) 2 P :=
  memLp_finsetSum _ fun j _ => ((gv_entry_memLp F S _ a b).sub (memLp_const _)).const_mul _

private lemma gl_entry_int [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (a : Fin m) (b : Fin n) :
    Integrable (fun ω => frozenBuf F S t ω a b) P := by
  have e : (fun ω => frozenBuf F S t ω a b) = fun ω => (frozenBuf F S t ω a b
      - (rOut F.C * F.A * rIn F.C) a b) + (rOut F.C * F.A * rIn F.C) a b := by
    funext ω; ring
  rw [e]
  exact ((gl_entry_L2 F S t a b).1.integrable (by norm_num)).add
    (integrable_const ((rOut F.C * F.A * rIn F.C) a b))

private lemma gl_entry_memLp [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (a : Fin m) (b : Fin n) :
    MemLp (fun ω => frozenBuf F S t ω a b) 2 P := by
  have e : (fun ω => frozenBuf F S t ω a b) = fun ω => (frozenBuf F S t ω a b
      - (rOut F.C * F.A * rIn F.C) a b) + (rOut F.C * F.A * rIn F.C) a b := by
    funext ω; ring
  rw [e]
  exact (gl_entry_L2 F S t a b).1.add (memLp_const ((rOut F.C * F.A * rIn F.C) a b))

private lemma gl_entry_mean [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (a : Fin m) (b : Fin n) :
    ∫ ω, frozenBuf F S t ω a b ∂P = (rOut F.C * F.A * rIn F.C) a b := by
  obtain ⟨hL, hlim⟩ := gl_entry_L2 F S t a b
  have hZ0 : Tendsto (fun N : ℕ => ∫ ω, (∑ j ∈ Finset.range N, emaW F.β j
      * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b)) ∂P)
      atTop (𝓝 0) := by
    simp only [gl_Z_mean]
    exact tendsto_const_nhds
  have hT := gl_integral_tendsto (fun N => gl_Z_memLp F S t (Finset.range N) a b) hL hlim
  have h0 : ∫ ω, (frozenBuf F S t ω a b - (rOut F.C * F.A * rIn F.C) a b) ∂P = 0 :=
    tendsto_nhds_unique hT hZ0
  have hi := gl_entry_int F S t a b
  rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul] at h0
  linarith

private lemma gl_entry_cov [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (a : Fin m) (b : Fin n) (c : Fin m) (d : Fin n) :
    covariance (fun ω => frozenBuf F S t ω a b) (fun ω => frozenBuf F S t ω c d) P
      = sPow F.β 2 * SigmaG S F a b c d := by
  obtain ⟨hL1, hl1⟩ := gl_entry_L2 F S t a b
  obtain ⟨hL2, hl2⟩ := gl_entry_L2 F S t c d
  have hcovL := gl_cov_tendsto (fun N => gl_Z_memLp F S t (Finset.range N) a b)
    (fun N => gl_Z_memLp F S t (Finset.range N) c d) hL1 hL2 hl1 hl2
  have hsq : Summable fun j : ℕ => emaW F.β j ^ 2 := by
    refine Summable.congr ((summable_geometric_of_lt_one (sq_nonneg F.β)
      (pow_lt_one₀ F.hβ.1 F.hβ.2 two_ne_zero)).mul_left ((1 - F.β) ^ 2)) fun j => ?_
    unfold emaW; ring
  have hS2 : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, emaW F.β j ^ 2) atTop
      (𝓝 (sPow F.β 2)) := by
    unfold sPow; exact hsq.hasSum.tendsto_sum_nat
  have hS : Tendsto (fun N : ℕ => covariance
      (fun ω => ∑ j ∈ Finset.range N, emaW F.β j
        * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b))
      (fun ω => ∑ j ∈ Finset.range N, emaW F.β j
        * (frozenBatchG F S (t + 1 - (j : ℤ)) ω c d - (rOut F.C * F.A * rIn F.C) c d)) P)
      atTop (𝓝 (sPow F.β 2 * SigmaG S F a b c d)) := by
    simp_rw [gl_Z_cov F S t _ a b c d]
    exact hS2.mul_const _
  have heq := tendsto_nhds_unique hcovL hS
  have e1 : (fun ω => frozenBuf F S t ω a b)
      = fun ω => (frozenBuf F S t ω a b - (rOut F.C * F.A * rIn F.C) a b)
        + (rOut F.C * F.A * rIn F.C) a b := by
    funext ω; ring
  have e2 : (fun ω => frozenBuf F S t ω c d)
      = fun ω => (frozenBuf F S t ω c d - (rOut F.C * F.A * rIn F.C) c d)
        + (rOut F.C * F.A * rIn F.C) c d := by
    funext ω; ring
  rw [e1, e2, covariance_add_const_left (hL1.integrable (by norm_num)) ((rOut F.C * F.A * rIn F.C) a b),
    covariance_add_const_right (hL2.integrable (by norm_num)) ((rOut F.C * F.A * rIn F.C) c d)]
  exact heq

private lemma gl_cov_future [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t s : ℤ) (hs : ∀ j : ℕ, t + 1 - (j : ℤ) ≠ s)
    (a : Fin m) (b : Fin n) (c : Fin m) (d : Fin n) :
    covariance (fun ω => frozenBuf F S t ω a b) (fun ω => frozenBatchG F S s ω c d) P = 0 := by
  obtain ⟨hL, hlim⟩ := gl_entry_L2 F S t a b
  have hY : MemLp (fun ω => frozenBatchG F S s ω c d) 2 P := gv_entry_memLp F S s c d
  have hYl : Tendsto (fun _ : ℕ => ∫ ω, (frozenBatchG F S s ω c d
      - frozenBatchG F S s ω c d) ^ 2 ∂P) atTop (𝓝 0) := by
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero]
    exact tendsto_const_nhds
  have hcov := gl_cov_tendsto (fun N => gl_Z_memLp F S t (Finset.range N) a b)
    (fun _ => hY) hL hY hlim hYl
  have hN : ∀ N : ℕ, covariance (fun ω => ∑ j ∈ Finset.range N, emaW F.β j
      * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b - (rOut F.C * F.A * rIn F.C) a b))
      (fun ω => frozenBatchG F S s ω c d) P = 0 := by
    intro N
    have hX : ∀ j : ℕ, MemLp (fun ω => emaW F.β j * (frozenBatchG F S (t + 1 - (j : ℤ)) ω a b
        - (rOut F.C * F.A * rIn F.C) a b)) 2 P := fun j =>
      ((gv_entry_memLp F S _ a b).sub (memLp_const _)).const_mul _
    rw [covariance_fun_sum_left' (fun j _ => hX j) hY]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hI := (gv_entry_memLp F S (t + 1 - (j : ℤ)) a b).integrable (by norm_num)
    rw [covariance_const_mul_left, covariance_sub_const_left hI,
      gl_cov_indep_gen F S (hs j) a b c d, mul_zero]
  simp_rw [hN] at hcov
  have h0 := tendsto_nhds_unique hcov tendsto_const_nhds
  have e1 : (fun ω => frozenBuf F S t ω a b)
      = fun ω => (frozenBuf F S t ω a b - (rOut F.C * F.A * rIn F.C) a b)
        + (rOut F.C * F.A * rIn F.C) a b := by
    funext ω; ring
  rw [e1, covariance_add_const_left (hL.integrable (by norm_num)) ((rOut F.C * F.A * rIn F.C) a b)]
  exact h0

private lemma gl_entry_var [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (a : Fin m) (b : Fin n) :
    ∫ ω, (frozenBuf F S t ω a b - (rOut F.C * F.A * rIn F.C) a b) ^ 2 ∂P
      = sPow F.β 2 * SigmaG S F a b a b := by
  have hm0 : ∫ ω, (frozenBuf F S t ω a b - (rOut F.C * F.A * rIn F.C) a b) ∂P = 0 := by
    rw [integral_sub (gl_entry_int F S t a b) (integrable_const _), gl_entry_mean F S t a b,
      integral_const]
    simp
  rw [gl_cov_self_of_mean_zero hm0, covariance_sub_const_left (gl_entry_int F S t a b),
    covariance_sub_const_right (gl_entry_int F S t a b)]
  exact gl_entry_cov F S t a b a b


/-- `lem:app-setup-ema-law`(iii): mean, covariance and Frobenius variance of the stationary
buffer `M_t`. Declaration of record of part (iii). The full environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Stationary EMA law]\label{lem:app-setup-ema-law}
In the frozen-state model, index the samples by time as above, and write
$\Sigma_G\defeq\Cov(\operatorname{vec}\Gt)$ for the batch covariance
\cref{eqn:app-setup-batch-cov}.
\begin{enumerate}[label=(\roman*)]
\item The series $\Mt=\sum_{j\ge0}\emaw{j}G_{t+1-j}$ and the sample series
$\sum_{j,a}\emaw{j}\abs{d_{ja}}\norm{z_{ja}}\norm{w_{ja}}$ converge absolutely.
\item For every integer $t$, $\Mt=\bmom M_{t-1}+(1-\bmom)\Gt$,
and the sequence $(\Mt)_{t\in\mathbb Z}$ is strictly stationary.
\item $\EE\Mt=\EE\Gt$, $\Cov(\operatorname{vec}\Mt)=\sw2\,\Sigma_G$, and
$\EE\norm{\Mt-\EE\Gt}_\F^2=\sw2\,\mathsf V_B$.
\item For every lag $\ell\ge0$,
$\Cov(\operatorname{vec}\Mt,\operatorname{vec}M_{t+\ell})=\bmom^\ell\,\sw2\,\Sigma_G$.
\item For every positive integer $T$,
\begin{equation}\label{eqn:app-setup-block-cov}
\Cov\Big(\sum_{t=1}^T\operatorname{vec}(\Mt-\EE\Gt)\Big)
=\sw2\Big[T+2\sum_{\ell=1}^{T-1}(T-\ell)\bmom^\ell\Big]\Sigma_G
=\Big[T-\frac{2\bmom(1-\bmom^T)}{1-\bmom^2}\Big]\Sigma_G ,
\end{equation}
the two-sided lag sum $\sum_{\ell\in\mathbb Z}\Cov(\operatorname{vec}\Mt,\operatorname{vec}M_{t+\ell})$
converges absolutely and equals $\Sigma_G$, and
$T^{-1}\Cov(\sum_{t\le T}\operatorname{vec}(\Mt-\EE\Gt))\to\Sigma_G$ as $T\to\infty$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_setup_ema_law_iii [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) :
    mean P (frozenBuf F S t) = mean P (frozenBatchG F S (t + 1)) ∧
      covT P (frozenBuf F S t) = sPow F.β 2 • SigmaG S F ∧
      ∫ ω, (fro (frozenBuf F S t ω - mean P (frozenBatchG F S (t + 1)))) ^ 2 ∂P =
        sPow F.β 2 * frozenVB S F := by
  have hV0 : frozenVB S F = ∑ a, ∑ b, covariance (fun ω => frozenBatchG F S 0 ω a b)
      (fun ω => frozenBatchG F S 0 ω a b) P := by
    unfold frozenVB
    exact gv_int_fro F S 0
  refine ⟨?_, ?_, ?_⟩
  · ext a b
    simp only [mean, Matrix.of_apply]
    rw [gl_entry_mean F S t a b, gl_int_entry F S (t + 1) a b]
  · funext a b c d
    simp only [covT, Pi.smul_apply, smul_eq_mul]
    exact gl_entry_cov F S t a b c d
  · have hfro : ∀ ω, (fro (frozenBuf F S t ω - mean P (frozenBatchG F S (t + 1)))) ^ 2
        = ∑ a, ∑ b, (frozenBuf F S t ω a b - (rOut F.C * F.A * rIn F.C) a b) ^ 2 := by
      intro ω
      rw [gm_batch_mean F S (t + 1), gv_fro_sq]
      simp only [Matrix.sub_apply]
    simp_rw [hfro]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (gl_entry_L2 F S t a b).1.integrable_sq]
    have hrow : ∀ a, ∫ ω, ∑ b, (frozenBuf F S t ω a b - (rOut F.C * F.A * rIn F.C) a b) ^ 2 ∂P
        = ∑ b, sPow F.β 2 * SigmaG S F a b a b := by
      intro a
      rw [integral_finsetSum _ fun b _ => (gl_entry_L2 F S t a b).1.integrable_sq]
      exact Finset.sum_congr rfl fun b _ => gl_entry_var F S t a b
    rw [Finset.sum_congr rfl fun a _ => hrow a, hV0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    rfl

/-- `lem:app-setup-ema-law`(iv): the lag covariance `Cov(vec M_t, vec M_{t+ℓ}) = β^ℓ S_2 Σ_G`
for `ℓ ≥ 0`. Declaration of record of part (iv). The full environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Stationary EMA law]\label{lem:app-setup-ema-law}
In the frozen-state model, index the samples by time as above, and write
$\Sigma_G\defeq\Cov(\operatorname{vec}\Gt)$ for the batch covariance
\cref{eqn:app-setup-batch-cov}.
\begin{enumerate}[label=(\roman*)]
\item The series $\Mt=\sum_{j\ge0}\emaw{j}G_{t+1-j}$ and the sample series
$\sum_{j,a}\emaw{j}\abs{d_{ja}}\norm{z_{ja}}\norm{w_{ja}}$ converge absolutely.
\item For every integer $t$, $\Mt=\bmom M_{t-1}+(1-\bmom)\Gt$,
and the sequence $(\Mt)_{t\in\mathbb Z}$ is strictly stationary.
\item $\EE\Mt=\EE\Gt$, $\Cov(\operatorname{vec}\Mt)=\sw2\,\Sigma_G$, and
$\EE\norm{\Mt-\EE\Gt}_\F^2=\sw2\,\mathsf V_B$.
\item For every lag $\ell\ge0$,
$\Cov(\operatorname{vec}\Mt,\operatorname{vec}M_{t+\ell})=\bmom^\ell\,\sw2\,\Sigma_G$.
\item For every positive integer $T$,
\begin{equation}\label{eqn:app-setup-block-cov}
\Cov\Big(\sum_{t=1}^T\operatorname{vec}(\Mt-\EE\Gt)\Big)
=\sw2\Big[T+2\sum_{\ell=1}^{T-1}(T-\ell)\bmom^\ell\Big]\Sigma_G
=\Big[T-\frac{2\bmom(1-\bmom^T)}{1-\bmom^2}\Big]\Sigma_G ,
\end{equation}
the two-sided lag sum $\sum_{\ell\in\mathbb Z}\Cov(\operatorname{vec}\Mt,\operatorname{vec}M_{t+\ell})$
converges absolutely and equals $\Sigma_G$, and
$T^{-1}\Cov(\sum_{t\le T}\operatorname{vec}(\Mt-\EE\Gt))\to\Sigma_G$ as $T\to\infty$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_setup_ema_law_iv [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (ℓ : ℕ) :
    crossCovT P (frozenBuf F S t) (frozenBuf F S (t + (ℓ : ℤ))) =
      (F.β ^ ℓ * sPow F.β 2) • SigmaG S F := by
  funext a b c d
  simp only [crossCovT, Pi.smul_apply, smul_eq_mul]
  have hcong : (fun ω => frozenBuf F S (t + (ℓ : ℤ)) ω c d) =ᵐ[P]
      fun ω => F.β ^ ℓ * frozenBuf F S t ω c d
        + ∑ r ∈ Finset.range ℓ, emaW F.β r * frozenBatchG F S (t + (ℓ : ℤ) + 1 - (r : ℤ)) ω c d := by
    filter_upwards [eqn_app_setup_lag_decomposition F S] with ω hω
    simp only [hω t ℓ, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [gl_cov_congr_right hcong]
  have hFmem : ∀ r ∈ Finset.range ℓ, MemLp (fun ω => emaW F.β r
      * frozenBatchG F S (t + (ℓ : ℤ) + 1 - (r : ℤ)) ω c d) 2 P := fun r _ =>
    (gv_entry_memLp F S _ c d).const_mul _
  rw [gl_cov_add_fun (gl_entry_memLp F S t a b)
    ((gl_entry_memLp F S t c d).const_mul _)
    (memLp_finsetSum _ fun r hr => (gv_entry_memLp F S _ c d).const_mul _)]
  rw [covariance_const_mul_right, covariance_fun_sum_right' hFmem (gl_entry_memLp F S t a b)]
  have hzero : ∑ r ∈ Finset.range ℓ, covariance (fun ω => frozenBuf F S t ω a b)
      (fun ω => emaW F.β r * frozenBatchG F S (t + (ℓ : ℤ) + 1 - (r : ℤ)) ω c d) P = 0 :=
    Finset.sum_eq_zero fun r hr => by
      rw [covariance_const_mul_right, gl_cov_future F S t (t + (ℓ : ℤ) + 1 - (r : ℤ))
        (fun j => by
          have := Finset.mem_range.1 hr
          omega) a b c d, mul_zero]
  rw [hzero, add_zero, gl_entry_cov F S t a b c d]
  ring

/-! ### Private helpers for `lem:app-setup-ema-law`(v) -/

section BkComb
open Finset

private lemma bk_icc_reindex (g : ℤ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc (1 : ℤ) T, g t = ∑ i ∈ Finset.range T, g ((i : ℤ) + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hI : Finset.Icc (1 : ℤ) ((T + 1 : ℕ) : ℤ) = insert ((T : ℤ) + 1) (Finset.Icc (1 : ℤ) T) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have hnot : ((T : ℤ) + 1) ∉ Finset.Icc (1 : ℤ) T := by
      simp only [Finset.mem_Icc]; omega
    rw [hI, Finset.sum_insert hnot, ih, Finset.sum_range_succ, add_comm]

private lemma bk_natAbs_shift (i j : ℕ) :
    ((((i : ℤ) + 1) - ((j : ℤ) + 1)).natAbs) = ((i : ℤ) - (j : ℤ)).natAbs := by
  congr 1; ring

private lemma bk_natAbs_diff (i T : ℕ) (h : i ≤ T) :
    (((i : ℤ) - (T : ℤ)).natAbs) = T - i := by
  omega

private lemma bk_natAbs_comm (T : ℕ) (j : ℕ) :
    (((T : ℤ) - (j : ℤ)).natAbs) = (((j : ℤ) - (T : ℤ)).natAbs) := by
  rw [← Int.natAbs_neg]; congr 1; ring

private lemma bk_pow_sum_reflect (β : ℝ) (T : ℕ) :
    ∑ i ∈ range T, β ^ (T - i) = ∑ ℓ ∈ range T, β ^ (ℓ + 1) := by
  have h := Finset.sum_range_reflect (fun ℓ => β ^ (ℓ + 1)) T
  rw [← h]
  apply Finset.sum_congr rfl
  intro i hi
  have := Finset.mem_range.1 hi
  congr 1
  omega

private lemma bk_range_double_succ (β : ℝ) (T : ℕ) :
    ∑ i ∈ range (T + 1), ∑ j ∈ range (T + 1), β ^ ((i : ℤ) - (j : ℤ)).natAbs
      = ∑ i ∈ range T, ∑ j ∈ range T, β ^ ((i : ℤ) - (j : ℤ)).natAbs
        + 2 * ∑ i ∈ range T, β ^ (T - i) + 1 := by
  have e1 : ∑ i ∈ range (T + 1), ∑ j ∈ range (T + 1), β ^ ((i : ℤ) - (j : ℤ)).natAbs
      = ∑ i ∈ range T, (∑ j ∈ range T, β ^ ((i : ℤ) - (j : ℤ)).natAbs
          + β ^ (T - i)) + (∑ j ∈ range T, β ^ ((j : ℤ) - (T : ℤ)).natAbs + 1) := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_range_succ, bk_natAbs_diff i T (by have := Finset.mem_range.1 hi; omega)]
    · rw [Finset.sum_range_succ]
      simp only [sub_self, Int.natAbs_zero, pow_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [bk_natAbs_comm]
  have e2 : ∑ j ∈ range T, β ^ ((j : ℤ) - (T : ℤ)).natAbs = ∑ j ∈ range T, β ^ (T - j) :=
    Finset.sum_congr rfl fun j hj => by
      rw [bk_natAbs_diff j T (by have := Finset.mem_range.1 hj; omega)]
  rw [e1, Finset.sum_add_distrib, e2]
  ring

private lemma bk_range_identity (β : ℝ) (T : ℕ) :
    ∑ i ∈ range T, ∑ j ∈ range T, β ^ ((i : ℤ) - (j : ℤ)).natAbs
      = 2 * ∑ ℓ ∈ range T, ((T : ℝ) - (ℓ : ℝ)) * β ^ ℓ - (T : ℝ) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hE1 : ∑ ℓ ∈ range (T + 1), (((T + 1 : ℕ) : ℝ) - (ℓ : ℝ)) * β ^ ℓ
        = ∑ ℓ ∈ range T, ((T : ℝ) - (ℓ : ℝ)) * β ^ ℓ + ∑ ℓ ∈ range (T + 1), β ^ ℓ := by
      have : ∑ ℓ ∈ range (T + 1), (((T + 1 : ℕ) : ℝ) - (ℓ : ℝ)) * β ^ ℓ
          = ∑ ℓ ∈ range (T + 1), (((T : ℝ) - (ℓ : ℝ)) * β ^ ℓ + β ^ ℓ) :=
        Finset.sum_congr rfl fun ℓ _ => by push_cast; ring
      rw [this, Finset.sum_add_distrib, Finset.sum_range_succ (fun ℓ => ((T : ℝ) - (ℓ : ℝ)) * β ^ ℓ) T]
      simp only [sub_self, zero_mul]
      rw [add_zero]
    have hG : ∑ ℓ ∈ range (T + 1), β ^ ℓ = 1 + ∑ ℓ ∈ range T, β ^ (ℓ + 1) := by
      rw [Finset.sum_range_succ', pow_zero, add_comm]
    rw [bk_range_double_succ, ih, bk_pow_sum_reflect, hE1, hG]
    push_cast
    ring

private lemma bk_block_comb (β : ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc (1 : ℤ) T, ∑ t' ∈ Finset.Icc (1 : ℤ) T, β ^ (t - t').natAbs
      = (T : ℝ) + 2 * ∑ ℓ ∈ Finset.Ico 1 T, ((T : ℝ) - (ℓ : ℝ)) * β ^ ℓ := by
  have h1 : ∑ t ∈ Finset.Icc (1 : ℤ) T, ∑ t' ∈ Finset.Icc (1 : ℤ) T, β ^ (t - t').natAbs
      = ∑ i ∈ range T, ∑ j ∈ range T, β ^ ((i : ℤ) - (j : ℤ)).natAbs := by
    rw [bk_icc_reindex]
    apply Finset.sum_congr rfl
    intro i _
    rw [bk_icc_reindex]
    apply Finset.sum_congr rfl
    intro j _
    rw [bk_natAbs_shift]
  rw [h1, bk_range_identity]
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hT]
    simp only [sub_zero, Nat.cast_zero, pow_zero, mul_one, zero_add]
    ring

end BkComb

/-- Centered covariance of finite sums: `Cov(∑ (f_t − c_t), ∑ (g_u − d_u)) = ∑_t ∑_u Cov(f_t, g_u)`. -/
private lemma bk_cov_centered {ι : Type*} [IsProbabilityMeasure P] (s : Finset ι)
    (f g : ι → Ω → ℝ) (cf cg : ι → ℝ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 P) (hg : ∀ i ∈ s, MemLp (g i) 2 P) :
    covariance (fun ω => ∑ i ∈ s, (f i ω - cf i)) (fun ω => ∑ i ∈ s, (g i ω - cg i)) P
      = ∑ i ∈ s, ∑ j ∈ s, covariance (f i) (g j) P := by
  have hX : MemLp (fun ω => ∑ i ∈ s, f i ω) 2 P := memLp_finsetSum s hf
  have hY : MemLp (fun ω => ∑ j ∈ s, g j ω) 2 P := memLp_finsetSum s hg
  have e1 : (fun ω => ∑ i ∈ s, (f i ω - cf i))
      = fun ω => (∑ i ∈ s, f i ω) + (-(∑ i ∈ s, cf i)) :=
    funext fun ω => by rw [Finset.sum_sub_distrib]; ring
  have e2 : (fun ω => ∑ i ∈ s, (g i ω - cg i))
      = fun ω => (∑ j ∈ s, g j ω) + (-(∑ j ∈ s, cg j)) :=
    funext fun ω => by rw [Finset.sum_sub_distrib]; ring
  rw [e1, e2, covariance_add_const_left (hX.integrable (by norm_num)) (-(∑ i ∈ s, cf i)),
    covariance_add_const_right (hY.integrable (by norm_num)) (-(∑ j ∈ s, cg j)),
    covariance_fun_sum_left' hf hY]
  exact Finset.sum_congr rfl fun i hi => covariance_fun_sum_right' hg (hf i hi)

private lemma bk_SigmaG_symm (S : FrozenSamples P m n B) (F : FrozenParams m n B)
    [IsProbabilityMeasure P] (a : Fin m) (b : Fin n) (c : Fin m) (d : Fin n) :
    SigmaG S F a b c d = SigmaG S F c d a b := by
  simp only [SigmaG, covT]
  exact covariance_comm _ _

private lemma bk_cross_formula [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t s : ℤ) (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n) :
    crossCovT P (frozenBuf F S t) (frozenBuf F S s) i j k l
      = (F.β ^ (t - s).natAbs * sPow F.β 2) * SigmaG S F i j k l := by
  rcases le_total t s with h | h
  · have hs : s = t + ((s - t).toNat : ℤ) := by omega
    have hn : (t - s).natAbs = (s - t).toNat := by omega
    have key := congrFun (congrFun (congrFun (congrFun
      (lem_app_setup_ema_law_iv F S t (s - t).toNat) i) j) k) l
    rw [← hs] at key
    simp only [Pi.smul_apply, smul_eq_mul] at key
    rw [hn, key]
  · have hs : t = s + ((t - s).toNat : ℤ) := by omega
    have hn : (t - s).natAbs = (t - s).toNat := by omega
    have key := congrFun (congrFun (congrFun (congrFun
      (lem_app_setup_ema_law_iv F S s (t - s).toNat) k) l) i) j
    rw [← hs] at key
    simp only [Pi.smul_apply, smul_eq_mul] at key
    have hsym : crossCovT P (frozenBuf F S t) (frozenBuf F S s) i j k l
        = crossCovT P (frozenBuf F S s) (frozenBuf F S t) k l i j := by
      simp only [crossCovT]
      exact covariance_comm _ _
    rw [hn, hsym, key, bk_SigmaG_symm S F k l i j]

private lemma bk_block_cov [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (T : ℕ) :
    covT P (blockSum S F T) = (sPow F.β 2 * ((T : ℝ) +
        2 * ∑ ℓ ∈ Finset.Ico 1 T, ((T : ℝ) - (ℓ : ℝ)) * F.β ^ ℓ)) • SigmaG S F := by
  funext a b c d
  have hf : ∀ t : ℤ, MemLp (fun ω => frozenBuf F S t ω a b) 2 P :=
    fun t => gl_entry_memLp F S t a b
  have hg : ∀ t : ℤ, MemLp (fun ω => frozenBuf F S t ω c d) 2 P :=
    fun t => gl_entry_memLp F S t c d
  have hcov := bk_cov_centered (P := P) (Finset.Icc (1 : ℤ) T)
    (fun t ω => frozenBuf F S t ω a b) (fun t ω => frozenBuf F S t ω c d)
    (fun t => mean P (frozenBatchG F S (t + 1)) a b)
    (fun t => mean P (frozenBatchG F S (t + 1)) c d)
    (fun t _ => hf t) (fun t _ => hg t)
  have e1 : (fun ω => blockSum S F T ω a b)
      = fun ω => ∑ t ∈ Finset.Icc (1 : ℤ) T,
          (frozenBuf F S t ω a b - mean P (frozenBatchG F S (t + 1)) a b) := by
    funext ω
    simp only [blockSum, Matrix.sum_apply, Matrix.sub_apply]
  have e2 : (fun ω => blockSum S F T ω c d)
      = fun ω => ∑ t ∈ Finset.Icc (1 : ℤ) T,
          (frozenBuf F S t ω c d - mean P (frozenBatchG F S (t + 1)) c d) := by
    funext ω
    simp only [blockSum, Matrix.sum_apply, Matrix.sub_apply]
  simp only [covT, Pi.smul_apply, smul_eq_mul]
  rw [e1, e2]
  refine Eq.trans hcov ?_
  have hc : ∀ t u : ℤ, covariance (fun ω => frozenBuf F S t ω a b)
      (fun ω => frozenBuf F S u ω c d) P
        = (F.β ^ (t - u).natAbs * sPow F.β 2) * SigmaG S F a b c d :=
    fun t u => bk_cross_formula F S t u a b c d
  simp only [hc]
  simp only [← Finset.sum_mul]
  rw [bk_block_comb]
  ring

/-- `lem:app-setup-ema-law`(v): block covariance `eqn:app-setup-block-cov` (closed form and
scalar identity), absolute summability and sum of the two-sided lag covariances, and the
limit `T^{-1} Cov(∑_{t≤T} vec(M_t − E G_t)) → Σ_G`. Declaration of record of part (v). The full
environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Stationary EMA law]\label{lem:app-setup-ema-law}
In the frozen-state model, index the samples by time as above, and write
$\Sigma_G\defeq\Cov(\operatorname{vec}\Gt)$ for the batch covariance
\cref{eqn:app-setup-batch-cov}.
\begin{enumerate}[label=(\roman*)]
\item The series $\Mt=\sum_{j\ge0}\emaw{j}G_{t+1-j}$ and the sample series
$\sum_{j,a}\emaw{j}\abs{d_{ja}}\norm{z_{ja}}\norm{w_{ja}}$ converge absolutely.
\item For every integer $t$, $\Mt=\bmom M_{t-1}+(1-\bmom)\Gt$,
and the sequence $(\Mt)_{t\in\mathbb Z}$ is strictly stationary.
\item $\EE\Mt=\EE\Gt$, $\Cov(\operatorname{vec}\Mt)=\sw2\,\Sigma_G$, and
$\EE\norm{\Mt-\EE\Gt}_\F^2=\sw2\,\mathsf V_B$.
\item For every lag $\ell\ge0$,
$\Cov(\operatorname{vec}\Mt,\operatorname{vec}M_{t+\ell})=\bmom^\ell\,\sw2\,\Sigma_G$.
\item For every positive integer $T$,
\begin{equation}\label{eqn:app-setup-block-cov}
\Cov\Big(\sum_{t=1}^T\operatorname{vec}(\Mt-\EE\Gt)\Big)
=\sw2\Big[T+2\sum_{\ell=1}^{T-1}(T-\ell)\bmom^\ell\Big]\Sigma_G
=\Big[T-\frac{2\bmom(1-\bmom^T)}{1-\bmom^2}\Big]\Sigma_G ,
\end{equation}
the two-sided lag sum $\sum_{\ell\in\mathbb Z}\Cov(\operatorname{vec}\Mt,\operatorname{vec}M_{t+\ell})$
converges absolutely and equals $\Sigma_G$, and
$T^{-1}\Cov(\sum_{t\le T}\operatorname{vec}(\Mt-\EE\Gt))\to\Sigma_G$ as $T\to\infty$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_setup_ema_law_v [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) :
    (∀ T : ℕ, 0 < T →
      (covT P (blockSum S F T) = (sPow F.β 2 * ((T : ℝ) +
          2 * ∑ ℓ ∈ Finset.Ico 1 T, ((T : ℝ) - (ℓ : ℝ)) * F.β ^ ℓ)) • SigmaG S F ∧
        covT P (blockSum S F T) = ((T : ℝ) - 2 * F.β * (1 - F.β ^ T) / (1 - F.β ^ 2)) •
          SigmaG S F)) ∧
    (∀ (t : ℤ) (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
      Summable (fun ℓ : ℤ => |crossCovT P (frozenBuf F S t) (frozenBuf F S (t + ℓ)) i j k l|) ∧
        HasSum (fun ℓ : ℤ => crossCovT P (frozenBuf F S t) (frozenBuf F S (t + ℓ)) i j k l)
          (SigmaG S F i j k l)) ∧
    Tendsto (fun T : ℕ => ((T : ℝ))⁻¹ • covT P (blockSum S F T)) atTop (𝓝 (SigmaG S F)) := by
  have hβ0 := F.hβ.1
  have hβ1 := F.hβ.2
  refine ⟨fun T hT => ⟨bk_block_cov F S T, ?_⟩, fun t i j k l => ?_, ?_⟩
  · rw [bk_block_cov F S T, ema_block_scalar hβ0 hβ1 hT]
  · have hn : ∀ ℓ : ℤ, (t - (t + ℓ)).natAbs = ℓ.natAbs := fun ℓ => by
      rw [show t - (t + ℓ) = -ℓ by ring, Int.natAbs_neg]
    have hH := (ema_two_sided_lag_scalar hβ0 hβ1).mul_right (SigmaG S F i j k l)
    rw [one_mul] at hH
    simp only [bk_cross_formula, hn]
    exact ⟨hH.summable.abs, hH⟩
  · have hc : ∀ T : ℕ, ((T : ℝ))⁻¹ • covT P (blockSum S F T)
        = (((T : ℝ))⁻¹ * (sPow F.β 2 * ((T : ℝ) +
            2 * ∑ ℓ ∈ Finset.Ico 1 T, ((T : ℝ) - (ℓ : ℝ)) * F.β ^ ℓ))) • SigmaG S F :=
      fun T => by rw [bk_block_cov F S T, smul_smul]
    have ht := (ema_block_scalar_tendsto hβ0 hβ1).smul_const (SigmaG S F)
    rw [one_smul] at ht
    exact Filter.Tendsto.congr (fun T => (hc T).symm) ht

/-! ## Startup and bias correction -/

/-- Startup recursion `M_t^K` of `prop:app-setup-startup`, indexed by `k = t + 1`:
`startupBuf 0 = K` (that is `M_{-1}^K = K`) and `startupBuf (k+1) = β startupBuf k + (1-β) G_{k+1}`,
so that `startupBuf (t+1) = M_t^K`. -/
def startupBuf (F : FrozenParams m n B) (S : FrozenSamples P m n B) (K : Mat m n) :
    ℕ → Ω → Mat m n
  | 0 => fun _ => K
  | k + 1 => fun ω =>
      F.β • startupBuf F S K k ω + (1 - F.β) • frozenBatchG F S ((k : ℤ) + 1) ω

private lemma sb_explicit (F : FrozenParams m n B) (S : FrozenSamples P m n B) (K : Mat m n)
    (ω : Ω) (k : ℕ) :
    startupBuf F S K k ω = F.β ^ k • K +
      ∑ j ∈ Finset.range k, emaW F.β j • frozenBatchG F S ((k : ℤ) - (j : ℤ)) ω := by
  induction k with
  | zero => simp [startupBuf]
  | succ k ih =>
    have hL : startupBuf F S K (k + 1) ω = F.β • startupBuf F S K k ω
        + (1 - F.β) • frozenBatchG F S ((k : ℤ) + 1) ω := rfl
    have hsum : ∑ j ∈ Finset.range k,
        emaW F.β (j + 1) • frozenBatchG F S (((k + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)) ω
        = F.β • ∑ j ∈ Finset.range k, emaW F.β j • frozenBatchG F S ((k : ℤ) - (j : ℤ)) ω := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hw : emaW F.β (j + 1) = F.β * emaW F.β j := by simp only [emaW]; ring
      have hi : ((k + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) = (k : ℤ) - (j : ℤ) := by push_cast; ring
      rw [hw, hi, mul_smul]
    have h0 : emaW F.β 0 = 1 - F.β := by simp [emaW]
    have hz : ((k + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    rw [Finset.sum_range_succ', hL, ih, hsum, h0, hz, smul_add, smul_smul, ← pow_succ']
    abel

private lemma sb_explicit_succ (F : FrozenParams m n B) (S : FrozenSamples P m n B) (K : Mat m n)
    (ω : Ω) (t : ℕ) :
    startupBuf F S K (t + 1) ω = F.β ^ (t + 1) • K +
      ∑ j ∈ Finset.range (t + 1), emaW F.β j • frozenBatchG F S ((t : ℤ) + 1 - (j : ℤ)) ω := by
  have h := sb_explicit F S K ω (t + 1)
  push_cast at h
  exact h

private lemma sb_cov_entry [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℕ) (a : Fin m) (b : Fin n) (c : Fin m) (d : Fin n) :
    covariance (fun ω => ∑ j ∈ Finset.range (t + 1),
        emaW F.β j * frozenBatchG F S ((t : ℤ) + 1 - (j : ℤ)) ω a b)
      (fun ω => ∑ j ∈ Finset.range (t + 1),
        emaW F.β j * frozenBatchG F S ((t : ℤ) + 1 - (j : ℤ)) ω c d) P
      = (∑ j ∈ Finset.range (t + 1), emaW F.β j ^ 2) * SigmaG S F a b c d := by
  have hX : ∀ j : ℕ, MemLp (fun ω => emaW F.β j * frozenBatchG F S ((t : ℤ) + 1 - (j : ℤ)) ω a b) 2 P :=
    fun j => (gv_entry_memLp F S _ a b).const_mul _
  have hY : ∀ j : ℕ, MemLp (fun ω => emaW F.β j * frozenBatchG F S ((t : ℤ) + 1 - (j : ℤ)) ω c d) 2 P :=
    fun j => (gv_entry_memLp F S _ c d).const_mul _
  rw [covariance_fun_sum_left' (fun j _ => hX j) (memLp_finsetSum _ fun k _ => hY k), Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [covariance_const_mul_left, covariance_fun_sum_right' (fun k _ => hY k) (gv_entry_memLp F S ((t : ℤ) + 1 - (j : ℤ)) a b)]
  simp only [covariance_const_mul_right]
  rw [Finset.sum_eq_single j (fun k _ hkj => ?_) (fun h => absurd hj h)]
  · rw [gl_cov_same_time, sq]
    ring
  · rw [gl_cov_indep_gen F S (s := (t : ℤ) + 1 - (j : ℤ)) (s' := (t : ℤ) + 1 - (k : ℤ))
      (by intro h; exact hkj (by omega)) a b c d, mul_zero]

/-- `prop:app-setup-startup`(i): explicit form `M_t^K = β^{t+1} K + ∑_{j=0}^t w_j G_{t+1-j}`.
Declaration of record of part (i). The full environment, verbatim from `section.tex`:
```latex
\begin{proposition}[Startup and bias correction]\label{prop:app-setup-startup}
In the frozen-state model let $K\in\R^{\Nout\times\Nin}$ be deterministic and
let $(M_t^K)_{t\ge-1}$ be the recursion $M_t^K=\bmom M_{t-1}^K+(1-\bmom)G_{t+1}$
started from $M_{-1}^K=K$. Then for $t\ge0$,
\begin{equation}\label{eqn:app-setup-startup}
\begin{gathered}
M_t^K=\bmom^{t+1}K+\sum_{j=0}^t\emaw{j}G_{t+1-j},\qquad
\EE M_t^K=\bmom^{t+1}K+(1-\bmom^{t+1})\,\EE\Gt,\\
\Cov(\operatorname{vec}M_t^K)=\sw2\big(1-\bmom^{2(t+1)}\big)\Sigma_G .
\end{gathered}
\end{equation}
The bias-corrected zero-start buffer $\widetilde M_t\defeq M_t^0/(1-\bmom^{t+1})$
has mean $\EE\Gt$ and covariance $\sw2\,\frac{1+\bmom^{t+1}}{1-\bmom^{t+1}}\Sigma_G$.
If $M_t^K$ and the stationary buffer $\Mt$ are built from the same batches,
then
\begin{equation}\label{eqn:app-setup-startup-coupling}
M_t^K-\Mt=\bmom^{t+1}(K-M_{-1}),\qquad
\EE\norm{M_t^K-\Mt}_\F^2=\bmom^{2(t+1)}\big(\norm{K-\EE\Gt}_\F^2+\sw2\mathsf V_B\big).
\end{equation}
\end{proposition}
```
-/
theorem prop_app_setup_startup_i (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (K : Mat m n) (t : ℕ) (ω : Ω) :
    startupBuf F S K (t + 1) ω = F.β ^ (t + 1) • K +
      ∑ j ∈ Finset.range (t + 1), emaW F.β j • frozenBatchG F S ((t : ℤ) + 1 - (j : ℤ)) ω := by
  exact sb_explicit_succ F S K ω t

/-- `prop:app-setup-startup`(ii): mean and covariance of `M_t^K`.
Declaration of record of part (ii). The full environment, verbatim from `section.tex`:
```latex
\begin{proposition}[Startup and bias correction]\label{prop:app-setup-startup}
In the frozen-state model let $K\in\R^{\Nout\times\Nin}$ be deterministic and
let $(M_t^K)_{t\ge-1}$ be the recursion $M_t^K=\bmom M_{t-1}^K+(1-\bmom)G_{t+1}$
started from $M_{-1}^K=K$. Then for $t\ge0$,
\begin{equation}\label{eqn:app-setup-startup}
\begin{gathered}
M_t^K=\bmom^{t+1}K+\sum_{j=0}^t\emaw{j}G_{t+1-j},\qquad
\EE M_t^K=\bmom^{t+1}K+(1-\bmom^{t+1})\,\EE\Gt,\\
\Cov(\operatorname{vec}M_t^K)=\sw2\big(1-\bmom^{2(t+1)}\big)\Sigma_G .
\end{gathered}
\end{equation}
The bias-corrected zero-start buffer $\widetilde M_t\defeq M_t^0/(1-\bmom^{t+1})$
has mean $\EE\Gt$ and covariance $\sw2\,\frac{1+\bmom^{t+1}}{1-\bmom^{t+1}}\Sigma_G$.
If $M_t^K$ and the stationary buffer $\Mt$ are built from the same batches,
then
\begin{equation}\label{eqn:app-setup-startup-coupling}
M_t^K-\Mt=\bmom^{t+1}(K-M_{-1}),\qquad
\EE\norm{M_t^K-\Mt}_\F^2=\bmom^{2(t+1)}\big(\norm{K-\EE\Gt}_\F^2+\sw2\mathsf V_B\big).
\end{equation}
\end{proposition}
```
-/
theorem prop_app_setup_startup_ii [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (K : Mat m n) (t : ℕ) :
    mean P (startupBuf F S K (t + 1)) = F.β ^ (t + 1) • K +
        (1 - F.β ^ (t + 1)) • mean P (frozenBatchG F S ((t : ℤ) + 1)) ∧
      covT P (startupBuf F S K (t + 1)) =
        (sPow F.β 2 * (1 - F.β ^ (2 * (t + 1)))) • SigmaG S F := by
  have hβ0 := F.hβ.1
  have hβ1 := F.hβ.2
  have hI : ∀ (a : Fin m) (b : Fin n) (ω : Ω), startupBuf F S K (t + 1) ω a b = F.β ^ (t + 1) * K a b +
      ∑ j ∈ Finset.range (t + 1), emaW F.β j * frozenBatchG F S ((t : ℤ) + 1 - (j : ℤ)) ω a b := by
    intro a b ω
    rw [sb_explicit_succ F S K ω t]
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hint : ∀ a b, Integrable (fun ω => ∑ j ∈ Finset.range (t + 1),
      emaW F.β j * frozenBatchG F S ((t : ℤ) + 1 - (j : ℤ)) ω a b) P := fun a b =>
    integrable_finset_sum _ fun j _ =>
      ((gv_entry_memLp F S ((t : ℤ) + 1 - (j : ℤ)) a b).integrable (by norm_num)).const_mul _
  constructor
  · ext i j
    have hint' : ∀ j' ∈ Finset.range (t + 1), Integrable (fun ω =>
        emaW F.β j' * frozenBatchG F S ((t : ℤ) + 1 - (j' : ℤ)) ω i j) P := fun j' _ =>
      ((gv_entry_memLp F S ((t : ℤ) + 1 - (j' : ℤ)) i j).integrable (by norm_num)).const_mul _
    simp only [mean, Matrix.of_apply, hI]
    rw [integral_add (integrable_const _) (integrable_finsetSum _ hint'),
      integral_finset_sum _ hint']
    simp only [integral_const, probReal_univ, one_smul, integral_const_mul, gl_int_entry,
      Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← Finset.sum_mul, startup_weight_sum hβ0 hβ1 t, one_mul]
  · funext i j k l
    simp only [covT, Pi.smul_apply, smul_eq_mul, hI]
    rw [covariance_const_add_left (hint i j), covariance_const_add_right (hint k l),
      sb_cov_entry F S t i j k l, startup_weight_sq_sum hβ0 hβ1 t]

/-- `prop:app-setup-startup`(iii): the bias-corrected zero-start buffer
`M̃_t = M_t^0 / (1 − β^{t+1})` has mean `E G_{t+1}` and covariance
`S_2 (1+β^{t+1})/(1−β^{t+1}) Σ_G`. Declaration of record of part (iii). The full environment,
verbatim from `section.tex`:
```latex
\begin{proposition}[Startup and bias correction]\label{prop:app-setup-startup}
In the frozen-state model let $K\in\R^{\Nout\times\Nin}$ be deterministic and
let $(M_t^K)_{t\ge-1}$ be the recursion $M_t^K=\bmom M_{t-1}^K+(1-\bmom)G_{t+1}$
started from $M_{-1}^K=K$. Then for $t\ge0$,
\begin{equation}\label{eqn:app-setup-startup}
\begin{gathered}
M_t^K=\bmom^{t+1}K+\sum_{j=0}^t\emaw{j}G_{t+1-j},\qquad
\EE M_t^K=\bmom^{t+1}K+(1-\bmom^{t+1})\,\EE\Gt,\\
\Cov(\operatorname{vec}M_t^K)=\sw2\big(1-\bmom^{2(t+1)}\big)\Sigma_G .
\end{gathered}
\end{equation}
The bias-corrected zero-start buffer $\widetilde M_t\defeq M_t^0/(1-\bmom^{t+1})$
has mean $\EE\Gt$ and covariance $\sw2\,\frac{1+\bmom^{t+1}}{1-\bmom^{t+1}}\Sigma_G$.
If $M_t^K$ and the stationary buffer $\Mt$ are built from the same batches,
then
\begin{equation}\label{eqn:app-setup-startup-coupling}
M_t^K-\Mt=\bmom^{t+1}(K-M_{-1}),\qquad
\EE\norm{M_t^K-\Mt}_\F^2=\bmom^{2(t+1)}\big(\norm{K-\EE\Gt}_\F^2+\sw2\mathsf V_B\big).
\end{equation}
\end{proposition}
```
-/
theorem prop_app_setup_startup_iii [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℕ) :
    mean P (fun ω => (1 - F.β ^ (t + 1))⁻¹ • startupBuf F S 0 (t + 1) ω) =
        mean P (frozenBatchG F S ((t : ℤ) + 1)) ∧
      covT P (fun ω => (1 - F.β ^ (t + 1))⁻¹ • startupBuf F S 0 (t + 1) ω) =
        (sPow F.β 2 * ((1 + F.β ^ (t + 1)) / (1 - F.β ^ (t + 1)))) • SigmaG S F := by
  have hβ0 := F.hβ.1
  have hβ1 := F.hβ.2
  have hlt : F.β ^ (t + 1) < 1 := pow_lt_one₀ hβ0 hβ1 (Nat.succ_ne_zero t)
  have hpos : (0 : ℝ) < 1 - F.β ^ (t + 1) := by linarith
  have hne : 1 - F.β ^ (t + 1) ≠ 0 := hpos.ne'
  have hsmul_mean : ∀ (c : ℝ) (Y : Ω → Mat m n), mean P (fun ω => c • Y ω) = c • mean P Y := by
    intro c Y
    ext i j
    simp only [mean, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  have hsmul_cov : ∀ (c : ℝ) (Y : Ω → Mat m n),
      covT P (fun ω => c • Y ω) = (c * c) • covT P Y := by
    intro c Y
    funext i j k l
    simp only [covT, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [covariance_const_mul_left, covariance_const_mul_right]
    ring
  obtain ⟨hm, hc⟩ := prop_app_setup_startup_ii F S 0 t
  constructor
  · rw [hsmul_mean, hm, smul_zero, zero_add, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · rw [hsmul_cov, hc, smul_smul]
    congr 1
    have h2 : F.β ^ (2 * (t + 1)) = (F.β ^ (t + 1)) ^ 2 := by
      rw [← pow_mul, mul_comm]
    rw [h2]
    field_simp
    ring

/-- `prop:app-setup-startup`(iv): coupling of the startup buffer with the stationary buffer built
from the same batches, `M_t^K − M_t = β^{t+1}(K − M_{-1})` almost surely, and
`E‖M_t^K − M_t‖_F² = β^{2(t+1)}(‖K − E G‖_F² + S_2 V_B)`. Declaration of record of part (iv).
The full environment, verbatim from `section.tex`:
```latex
\begin{proposition}[Startup and bias correction]\label{prop:app-setup-startup}
In the frozen-state model let $K\in\R^{\Nout\times\Nin}$ be deterministic and
let $(M_t^K)_{t\ge-1}$ be the recursion $M_t^K=\bmom M_{t-1}^K+(1-\bmom)G_{t+1}$
started from $M_{-1}^K=K$. Then for $t\ge0$,
\begin{equation}\label{eqn:app-setup-startup}
\begin{gathered}
M_t^K=\bmom^{t+1}K+\sum_{j=0}^t\emaw{j}G_{t+1-j},\qquad
\EE M_t^K=\bmom^{t+1}K+(1-\bmom^{t+1})\,\EE\Gt,\\
\Cov(\operatorname{vec}M_t^K)=\sw2\big(1-\bmom^{2(t+1)}\big)\Sigma_G .
\end{gathered}
\end{equation}
The bias-corrected zero-start buffer $\widetilde M_t\defeq M_t^0/(1-\bmom^{t+1})$
has mean $\EE\Gt$ and covariance $\sw2\,\frac{1+\bmom^{t+1}}{1-\bmom^{t+1}}\Sigma_G$.
If $M_t^K$ and the stationary buffer $\Mt$ are built from the same batches,
then
\begin{equation}\label{eqn:app-setup-startup-coupling}
M_t^K-\Mt=\bmom^{t+1}(K-M_{-1}),\qquad
\EE\norm{M_t^K-\Mt}_\F^2=\bmom^{2(t+1)}\big(\norm{K-\EE\Gt}_\F^2+\sw2\mathsf V_B\big).
\end{equation}
\end{proposition}
```
-/
theorem prop_app_setup_startup_iv [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (K : Mat m n) (t : ℕ) :
    (∀ᵐ ω ∂P, startupBuf F S K (t + 1) ω - frozenBuf F S (t : ℤ) ω =
        F.β ^ (t + 1) • (K - frozenBuf F S (-1) ω)) ∧
      ∫ ω, (fro (startupBuf F S K (t + 1) ω - frozenBuf F S (t : ℤ) ω)) ^ 2 ∂P =
        F.β ^ (2 * (t + 1)) *
          ((fro (K - mean P (frozenBatchG F S 0))) ^ 2 + sPow F.β 2 * frozenVB S F) := by
  have hdec := eqn_app_setup_lag_decomposition F S
  have hae : ∀ᵐ ω ∂P, startupBuf F S K (t + 1) ω - frozenBuf F S (t : ℤ) ω =
      F.β ^ (t + 1) • (K - frozenBuf F S (-1) ω) := by
    filter_upwards [hdec] with ω hω
    have h := hω (-1) (t + 1)
    have e1 : (-1 : ℤ) + ((t + 1 : ℕ) : ℤ) = (t : ℤ) := by push_cast; ring
    have hsum : ∑ r ∈ Finset.range (t + 1),
        emaW F.β r • frozenBatchG F S ((-1 : ℤ) + ((t + 1 : ℕ) : ℤ) + 1 - (r : ℤ)) ω
        = ∑ r ∈ Finset.range (t + 1), emaW F.β r • frozenBatchG F S ((t : ℤ) + 1 - (r : ℤ)) ω := by
      refine Finset.sum_congr rfl fun r _ => ?_
      congr 2
      push_cast
      ring
    rw [hsum, e1] at h
    rw [sb_explicit_succ F S K ω t, h, smul_sub]
    abel
  refine ⟨hae, ?_⟩
  have hβ0 := F.hβ.1
  have hX2 : ∀ a b, MemLp (fun ω => frozenBuf F S (-1) ω a b) 2 P :=
    fun a b => gl_entry_memLp F S (-1) a b
  have hmean0 : mean P (frozenBuf F S (-1)) = mean P (frozenBatchG F S 0) := by
    have h := (lem_app_setup_ema_law_iii F S (-1)).1
    rw [show ((-1 : ℤ) + 1) = 0 by norm_num] at h
    exact h
  have hmeanE : ∀ a b, ∫ ω, frozenBuf F S (-1) ω a b ∂P = mean P (frozenBatchG F S 0) a b := by
    intro a b
    rw [← hmean0]
    simp only [mean, Matrix.of_apply]
  have hZ2g : ∀ a b, Integrable (fun ω =>
      (frozenBuf F S (-1) ω a b - mean P (frozenBatchG F S 0) a b) ^ 2) P :=
    fun a b => ((hX2 a b).sub (memLp_const _)).integrable_sq
  have hintK : ∀ a b, Integrable (fun ω => (K a b - frozenBuf F S (-1) ω a b) ^ 2) P :=
    fun a b => ((memLp_const (K a b)).sub (hX2 a b)).integrable_sq
  have hsq : ∀ a b, ∫ ω, (K a b - frozenBuf F S (-1) ω a b) ^ 2 ∂P
      = (K a b - mean P (frozenBatchG F S 0) a b) ^ 2
        + ∫ ω, (frozenBuf F S (-1) ω a b - mean P (frozenBatchG F S 0) a b) ^ 2 ∂P := by
    intro a b
    have hZi : Integrable (fun ω => frozenBuf F S (-1) ω a b - mean P (frozenBatchG F S 0) a b) P :=
      ((hX2 a b).integrable (by norm_num)).sub (integrable_const _)
    have hZ0 : ∫ ω, (frozenBuf F S (-1) ω a b - mean P (frozenBatchG F S 0) a b) ∂P = 0 := by
      rw [integral_sub ((hX2 a b).integrable (by norm_num)) (integrable_const _), integral_const,
        hmeanE a b]
      simp
    have hpt : ∀ ω, (K a b - frozenBuf F S (-1) ω a b) ^ 2
        = (K a b - mean P (frozenBatchG F S 0) a b) ^ 2
          + (-2 * (K a b - mean P (frozenBatchG F S 0) a b)) *
            (frozenBuf F S (-1) ω a b - mean P (frozenBatchG F S 0) a b)
          + (frozenBuf F S (-1) ω a b - mean P (frozenBatchG F S 0) a b) ^ 2 := fun ω => by ring
    have hc1 : Integrable (fun _ : Ω => (K a b - mean P (frozenBatchG F S 0) a b) ^ 2) P :=
      integrable_const _
    have hc2 : Integrable (fun ω => (-2 * (K a b - mean P (frozenBatchG F S 0) a b)) *
        (frozenBuf F S (-1) ω a b - mean P (frozenBatchG F S 0) a b)) P := hZi.const_mul _
    have hI1 : Integrable (fun ω => (K a b - mean P (frozenBatchG F S 0) a b) ^ 2 +
        (-2 * (K a b - mean P (frozenBatchG F S 0) a b)) *
          (frozenBuf F S (-1) ω a b - mean P (frozenBatchG F S 0) a b)) P := hc1.add hc2
    simp_rw [hpt]
    rw [integral_add hI1 (hZ2g a b), integral_add hc1 hc2, integral_const,
      integral_const_mul, hZ0]
    simp
  have hsumInt : ∀ (f : Fin m → Fin n → Ω → ℝ), (∀ a b, Integrable (f a b) P) →
      ∫ ω, ∑ a, ∑ b, f a b ω ∂P = ∑ a, ∑ b, ∫ ω, f a b ω ∂P := by
    intro f hf
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hf a b]
    exact Finset.sum_congr rfl fun a _ => integral_finsetSum _ fun b _ => hf a b
  have hfroK : ∀ ω, (fro (K - frozenBuf F S (-1) ω)) ^ 2
      = ∑ a, ∑ b, (K a b - frozenBuf F S (-1) ω a b) ^ 2 := by
    intro ω
    rw [gv_fro_sq]
    simp only [Matrix.sub_apply]
  have hfroX : ∀ ω, (fro (frozenBuf F S (-1) ω - mean P (frozenBatchG F S 0))) ^ 2
      = ∑ a, ∑ b, (frozenBuf F S (-1) ω a b - mean P (frozenBatchG F S 0) a b) ^ 2 := by
    intro ω
    rw [gv_fro_sq]
    simp only [Matrix.sub_apply]
  have hfroM : (fro (K - mean P (frozenBatchG F S 0))) ^ 2
      = ∑ a, ∑ b, (K a b - mean P (frozenBatchG F S 0) a b) ^ 2 := by
    rw [gv_fro_sq]
    simp only [Matrix.sub_apply]
  have hL2 : ∫ ω, (fro (K - frozenBuf F S (-1) ω)) ^ 2 ∂P
      = (fro (K - mean P (frozenBatchG F S 0))) ^ 2 + sPow F.β 2 * frozenVB S F := by
    have hvar := (lem_app_setup_ema_law_iii F S (-1)).2.2
    rw [show ((-1 : ℤ) + 1) = 0 by norm_num] at hvar
    rw [← hvar]
    simp only [hfroK, hfroX]
    rw [hfroM, hsumInt _ hintK, hsumInt _ hZ2g]
    simp only [hsq, Finset.sum_add_distrib]
  have hp : (F.β ^ (t + 1)) ^ 2 = F.β ^ (2 * (t + 1)) := by
    rw [← pow_mul, mul_comm]
  have hLHS : ∫ ω, (fro (startupBuf F S K (t + 1) ω - frozenBuf F S (t : ℤ) ω)) ^ 2 ∂P
      = F.β ^ (2 * (t + 1)) * ∫ ω, (fro (K - frozenBuf F S (-1) ω)) ^ 2 ∂P := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [hω, gi_fro_smul, mul_pow, sq_abs, hp]
  rw [hLHS, hL2]

end Muon.Setup

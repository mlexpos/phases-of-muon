import Muon.Dynamics.Freezing
import Muon.Dynamics.Transport
import Muon.Dynamics.FiniteMean
import Muon.Dynamics.Causal
import Muon.Foundations.Freezing
import Muon.External.Certificates

/-!
# Appendix E, work package L-E.10: projection variance, block martingale, prefixes, transport, response

Snapshot `cr-2026-10-23`. Source: `sections/05-dynamics/section.tex`, subsection "Transport, concentration
and diffuseness along the algorithm": `lem:app-dyn-poincare` (ll. 1713–1721), `lem:app-dyn-martingale`
(ll. 1786–1797), `lem:app-dyn-prefix` with `eqn:app-dyn-envelope` (ll. 1837–1853), `prop:app-dyn-transport`
(ll. 1907–1916), `prop:app-dyn-response` (ll. 1966–1977). Card: `sections/05-dynamics/CARD.md` §2, §3, §5
(L-E.10). Interface draft: every proof is `sorry`.

Representation choices:
* Standing hypotheses. "From here on the hypotheses (H1)–(H4) of `thm:app-dyn-main` are in force" (l. 1472),
  bundled per dimension in `DynSetup` (`Muon.Dynamics.Transport`). Every statement takes `S : DynSetup p P m n B`.
* Blocks and prefixes. `blockLen B = L`, `prefixLen p.β B = 𝗊`, block starts `t_b = b * L`
  (`Muon.Dynamics.Basic`). The admissible set is `admA p C = 𝒜`, its enlargement `admAplus p C = 𝒜⁺`.
* Stopping time. `tauPlus p S ω = τ⁺ = inf{t ≥ 0 : Δ_t ∉ 𝒜⁺}` (`ℕ∞`-valued, `⊤` if the set is empty).
* Subsection convention. "We fix `B₀` such that … all statements below are for `B ≥ B₀`" (ll. 1526–1531): the
  statements of this file that lie in that subsection carry `∃ B₀` before the constant and `B₀ ≤ B` as a
  hypothesis. `lem:app-dyn-poincare` is stated for every `B` (its proof needs no threshold; see open questions).
* Constants. `∃ K` (and `∃ B₀`) come after the fixed parameters and the constants of the statement (`cW`,
  `cΠ`, the sequence `δ`), and before the dimensions, the covariances, the samples and the states.
* Expectations and conditional expectations. Each carries an `Integrable` conjunct. Conditional expectations of
  matrices are entrywise (`Muon.Foundations.condExpMat`); means are entrywise (`Muon.mean`).
* Pairing and norms. `frobIP` is the Frobenius pairing `⟨·,·⟩`, `fro` is `‖·‖_F`, and an unsubscripted `‖·‖`
  is `opNorm`.
* Certificates. `lem:app-dyn-poincare` cites the Gaussian Poincaré inequality, entering as the explicit argument
  `Muon.External.GaussianPoincare`. The Doob `L²` inequality of `lem:app-dyn-martingale` is provable from
  Mathlib (`MeasureTheory.maximal_ineq`) and carries no certificate.
* Variance and maxima. `ProbabilityTheory.variance` is accompanied by `MemLp _ 2 P`. The maximum over
  `j ≤ TB/L` is a `Finset.sup'` over `Finset.range (⌊TB/L⌋₊ + 1)`.
-/


set_option linter.style.longLine false

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open Muon Muon.Setup Muon.Volatility

noncomputable section

namespace Muon.Dynamics

/-! ## Auxiliary objects of this subsection -/

/-- The quadratic functional `X_{f,g}(Δ) = ∫ f ⊗ g dχ(Δ) = ⟨Δ, 𝒲_{f,g} Δ⟩_F` (`section.tex`, ll. 1780–1783),
with `𝒲_{f,g}` the map `wfg` of `Muon.Dynamics.Basic`. Snapshot `cr-2026-10-23`. -/
def Xfg {m n : ℕ} (f g : ℝ → ℝ) (C : Covariances m n) (Δ : Mat m n) : ℝ :=
  frobIP Δ (wfg f g C Δ)

/-- The stopping time `τ⁺ = inf{t ≥ 0 : Δ_t ∉ 𝒜⁺}` of `section.tex` l. 1493 (`𝒜⁺ = admAplus p C`), with the
convention `inf ∅ = ∞`. Snapshot `cr-2026-10-23`. -/
def tauPlus (p : DynParams) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (ω : Ω) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : dynDelta S t ω ∉ admAplus p S.C), (t : ℕ∞)

/-- `Ω_β(ε) = ∑_{r≥0} min(ε, β^{r+1})` of `lem:app-dyn-prefix` (`section.tex` l. 1846). Snapshot `cr-2026-10-23`. -/
def omegaBeta (β ε : ℝ) : ℝ := ∑' r : ℕ, min ε (β ^ (r + 1))

/-- The stationary causal tangent `V̇_r` of `prop:app-dyn-transport`: the tangent of `lem:app-dyn-tangent` for the
stationary chain at `(t, Δ_t)` with its initial buffer `N_{-1}` (`chainInit`, the aux family of comparison `t`)
held fixed (`prop:app-dyn-stationary-tangent`, `section.tex` ll. 1417–1419). Snapshot `cr-2026-10-23`. -/
def dynStatTangent (p : DynParams) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t r : ℕ) : Ω → Mat m n :=
  fun ω => causalDot p S.C (fun s => physBatch S.C (S.cs.act s) ω) t (dynDelta S t ω)
    (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) r

/-- The mean frozen update `V̄(D) = 𝔼 V_0` of the stationary chain at `(t, D)` (`def:app-dyn-chains`). Entrywise
mean `Muon.mean`. Snapshot `cr-2026-10-23`. -/
def dynVbar (p : DynParams) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) (D : Mat m n) : Mat m n :=
  Muon.mean P (fun ω => stationaryV p S.C S.cs t D 0 ω)

/-- The right-hand side `ρ_B` of `prop:app-dyn-response` with constant `K` and test constant `c_Π`, as a function of
`B` (`section.tex` ll. 1966–1977). Snapshot `cr-2026-10-23`. -/
def responseRho (p : DynParams) (K cPi : ℝ) (δ : ℕ → ℝ) (B : ℕ) : ℝ :=
  K * ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ)
    + (blockLen B : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ)
    + δ B * (cPi + δ B) + omegaBeta p.β ((prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ))
    + p.β ^ prefixLen p.β B + Real.sqrt (B : ℝ) * (blockLen B : ℝ) * p.β ^ prefixLen p.β B)

/-- The block increment `X_{f,g}(Δ_{t_{b+1}}) − X_{f,g}(Δ_{t_b})` with `t_b = b L` (`lem:app-dyn-martingale`, cr-2026-10-23). -/
def blockIncr (p : DynParams) (f g : ℝ → ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (b : ℕ) : Ω → ℝ :=
  fun ω => Xfg f g S.C (dynDelta S ((b + 1) * blockLen B) ω) - Xfg f g S.C (dynDelta S (b * blockLen B) ω)

/-- (cr-2026-10-23) The martingale difference `I_b ξ_b` with `I_b = 𝟙_{b<b⋆}` and
`ξ_b = X(Δ_{t_{b+1}}) − X(Δ_{t_b}) − 𝔼_{t_b}[X(Δ_{t_{b+1}}) − X(Δ_{t_b})]` (`lem:app-dyn-martingale`). The
conditional expectation is `condExp` given `𝓕_{t_b}`; its integrability is a conjunct of the lemma. -/
def blockMartDiff (p : DynParams) (f g : ℝ → ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (bstar : Ω → ℕ) (b : ℕ) : Ω → ℝ :=
  fun ω => (if b < bstar ω then (1 : ℝ) else 0) *
    (blockIncr p f g S b ω - condExp (dynPast S (b * blockLen B)) P (blockIncr p f g S b) ω)

/-- (cr-2026-10-23) The squared maximum `max_{j ≤ TB/L} |∑_{b<j} I_b ξ_b|²` over the integers `j ≤ TB/L`, as a `Finset.sup'`
over `Finset.range (⌊TB/L⌋₊ + 1)`. -/
def blockMaxSq (p : DynParams) (f g : ℝ → ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (bstar : Ω → ℕ) (T : ℝ) : Ω → ℝ :=
  fun ω => (Finset.range (⌊T * (B : ℝ) / (blockLen B : ℝ)⌋₊ + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    (fun j => (∑ b ∈ Finset.range j, blockMartDiff p f g S bstar b ω) ^ 2)

private lemma projection_gaussian_map_toLp (d : ℕ) :
    (Muon.Foundations.stdGaussianPi d).map
      (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  unfold Muon.Foundations.stdGaussianPi
  exact map_pi_eq_stdGaussian

private lemma projection_poincare_pi (cert : Muon.External.GaussianPoincare)
    (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiff ℝ 1 f)
    (c : ℝ) (hc : 0 ≤ c)
    (henergy : ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ ENNReal.ofReal c) :
    MemLp (fun x : Fin d → ℝ => f (WithLp.toLp 2 x)) 2
        (Muon.Foundations.stdGaussianPi d) ∧
      variance (fun x : Fin d → ℝ => f (WithLp.toLp 2 x))
        (Muon.Foundations.stdGaussianPi d) ≤ c := by
  have hfinite : ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2
      ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) < ⊤ :=
    henergy.trans_lt ENNReal.ofReal_lt_top
  have hvar := (cert.holds d f hf hfinite).trans henergy
  have hmem : MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (evariance_lt_top_iff_memLp hf.continuous.aestronglyMeasurable).mp
      (hvar.trans_lt ENNReal.ofReal_lt_top)
  have hmap : MeasurePreserving
      (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
      (Muon.Foundations.stdGaussianPi d) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    ⟨by fun_prop, projection_gaussian_map_toLp d⟩
  refine ⟨hmem.comp_measurePreserving hmap, ?_⟩
  rw [hmap.variance_fun_comp hf.continuous.aemeasurable]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvar
  simpa only [variance, ENNReal.toReal_ofReal hc] using hreal

private lemma projection_batch_measurable {Ω : Type*} [MeasurableSpace Ω]
    {m n B : ℕ} (C : Covariances m n) (D : Mat m n)
    (z : Fin B → Ω → Vec m × Vec n) (hz : ∀ a, Measurable (z a)) :
    Measurable (fun ω => batchGrad D (physBatch C z ω)) := by
  unfold batchGrad Muon.Setup.grad physBatch phys resid outer Matrix.vecMulVec
    Matrix.mulVec dotProduct
  fun_prop

private lemma projection_stationary_measurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B)
    (t r : ℕ) (D : Mat m n) (hD : 0 < riskSigma C D)
    (hS : SizeFin C B p.γstar p.CSig) :
    AEStronglyMeasurable (stationaryV p C cs t D r) P := by
  have hinit : AEStronglyMeasurable (chainInit p.β C D (cs.aux (t : ℤ))) P := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N ω => ∑ j ∈ Finset.range N,
        emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) ?_ ?_
    · intro N
      exact (Finset.stronglyMeasurable_fun_sum _ fun j _ =>
        (projection_batch_measurable C D _ (cs.meas_aux _ j)).stronglyMeasurable.const_smul
          (emaW p.β j)).aestronglyMeasurable
    · filter_upwards [(lem_app_dyn_chains_iii p C cs t D 0 hD hS).1] with ω hω
      exact hω.hasSum.tendsto_sum_nat
  have hchain (k : ℕ) : AEStronglyMeasurable
      (fun ω => emaChain p.β D (fun s => physBatch C (cs.act s) ω) t
        (chainInit p.β C D (cs.aux (t : ℤ)) ω) k) P := by
    induction k with
    | zero => exact hinit
    | succ k hk =>
      exact (hk.const_smul p.β).add
        ((projection_batch_measurable C D _ (cs.meas_act _)).aestronglyMeasurable.const_smul
          (1 - p.β))
  have hridge : 0 ≤ physRidge p C D := by
    exact mul_nonneg (mul_nonneg (by norm_num) hD.le) p.hϱ.le
  have hQ : Measurable (fun K : Mat m n => Q (physRidge p C D) K) :=
    measurable_Q.comp
      ((measurable_const (a := (⟨physRidge p C D, hridge⟩ : Ici (0 : ℝ)))).prodMk
        measurable_id)
  exact (hQ.comp_aemeasurable (hchain (r + 1)).aemeasurable).aestronglyMeasurable

private lemma projection_entry_sq_le_fro {m n : ℕ} (K : Mat m n)
    (i : Fin m) (j : Fin n) : K i j ^ 2 ≤ fro K ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity)]
  calc
    K i j ^ 2 = ‖K i j‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ b, ‖K i b‖ ^ 2 :=
      Finset.single_le_sum (fun b _ => sq_nonneg ‖K i b‖) (Finset.mem_univ j)
    _ ≤ ∑ a, ∑ b, ‖K a b‖ ^ 2 :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg ‖K a b‖)
        (Finset.mem_univ i)

private lemma projection_stationary_memLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B)
    (t r : ℕ) (D T : Mat m n) (hD : 0 < riskSigma C D)
    (hS : SizeFin C B p.γstar p.CSig) :
    MemLp (fun ω => frobIP T (stationaryV p C cs t D r ω)) 2 P := by
  have hmeas := projection_stationary_measurable p C cs t r D hD hS
  have hentry (i : Fin m) (j : Fin n) :
      MemLp (fun ω => stationaryV p C cs t D r ω i j) 2 P := by
    have hmc : Continuous (fun K : Mat m n => K i j) := by fun_prop
    refine MemLp.of_bound (hmc.comp_aestronglyMeasurable hmeas)
      (Real.sqrt ((min m n : ℕ) : ℝ)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    have hridge : 0 ≤ physRidge p C D :=
      mul_nonneg (mul_nonneg (by norm_num) hD.le) p.hϱ.le
    have hfilter := lem_app_setup_filter_i _ hridge (stationaryN p C cs t D r ω)
    have hsq := projection_entry_sq_le_fro (stationaryV p C cs t D r ω) i j
    have hrank : ((stationaryN p C cs t D r ω).rank : ℝ) ≤ ((min m n : ℕ) : ℝ) :=
      Nat.cast_le.mpr hfilter.2.2.1
    exact hsq.trans (hfilter.2.1.trans hrank)
  simp only [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => (hentry i j).const_mul _

private lemma projection_variance_sum_le {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : Finset ι) (Y : ι → Ω → ℝ)
    (hY : ∀ i ∈ s, MemLp (Y i) 2 P) (c : ℝ)
    (hc : ∀ i ∈ s, variance (Y i) P ≤ c) :
    variance (fun ω => ∑ i ∈ s, Y i ω) P ≤ (s.card : ℝ) ^ 2 * c := by
  rw [variance_fun_sum' hY]
  calc
    ∑ i ∈ s, ∑ j ∈ s, covariance (Y i) (Y j) P ≤ ∑ i ∈ s, ∑ j ∈ s, c := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hsub := variance_nonneg (fun ω => Y i ω - Y j ω) P
      rw [variance_fun_sub (hY i hi) (hY j hj)] at hsub
      linarith [hc i hi, hc j hj]
    _ = (s.card : ℝ) ^ 2 * c := by simp; ring

private lemma frobIP_sum_right {m n : ℕ} {ι : Type*} (T : Mat m n)
    (s : Finset ι) (V : ι → Mat m n) :
    frobIP T (∑ i ∈ s, V i) = ∑ i ∈ s, frobIP T (V i) := by
  simp [frobIP, Matrix.transpose_sum, Matrix.mul_sum, Matrix.trace_sum]

private lemma projection_Q_contDiff {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun N : Fin m → Fin n → ℝ => fun i j => Q ℓ (Matrix.of N) i j) := by
  apply contDiff_iff_contDiffAt.mpr
  intro N
  have hQ := (Q_contDiffOn_pos m n).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds
      (show 0 < (N, ℓ).2 from hℓ))
  exact hQ.comp N ((contDiff_id.prodMk contDiff_const).contDiffAt)

private lemma projection_frobIP_le {m n : ℕ} (T R : Mat m n) :
    |frobIP T R| ≤ fro T * fro R := by
  have htr : frobIP T R = ∑ x : Fin m × Fin n, T x.1 x.2 * R x.1 x.2 := by
    simp [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [htr]
  calc
    |∑ x : Fin m × Fin n, T x.1 x.2 * R x.1 x.2| ≤
        ∑ x : Fin m × Fin n, |T x.1 x.2| * |R x.1 x.2| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun x : Fin m × Fin n => T x.1 x.2 * R x.1 x.2) Finset.univ
    _ ≤ _ := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m × Fin n))
        (fun x => |T x.1 x.2|) (fun x => |R x.1 x.2|)
      simpa [fro, Fintype.sum_prod_type, Real.norm_eq_abs] using h

private lemma projection_filter_test_bound {m n : ℕ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (T N R : Mat m n) :
    |frobIP T (dirDeriv ℓ N R)| ≤ ℓ ^ (-(1 / 2 : ℝ)) * fro T * fro R := by
  calc
    |frobIP T (dirDeriv ℓ N R)| ≤ fro T * fro (dirDeriv ℓ N R) :=
      projection_frobIP_le _ _
    _ ≤ fro T * (ℓ ^ (-(1 / 2 : ℝ)) * fro R) :=
      mul_le_mul_of_nonneg_left
        (lem_app_dyn_second_i hℓ le_rfl ℓ ⟨le_rfl, le_rfl⟩ N R) (Real.sqrt_nonneg _)
    _ = _ := by ring

private lemma projection_batch_contDiff {m n B : ℕ}
    (C : Covariances m n) (D : Mat m n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Batch m n B =>
      fun i j => batchGrad D (fun a => phys C (z a)) i j) := by
  unfold batchGrad Muon.Setup.grad phys resid outer Matrix.vecMulVec
    Matrix.mulVec dotProduct
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.of_apply, smul_eq_mul]
  fun_prop

private lemma projection_filter_fderiv {m n : ℕ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (N R : Fin m → Fin n → ℝ) :
    (fderiv ℝ (fun M : Fin m → Fin n → ℝ =>
      fun i j => Q ℓ (Matrix.of M) i j) N) R = dirDeriv ℓ (Matrix.of N) (Matrix.of R) := by
  have hQ := (projection_Q_contDiff (m := m) (n := n) hℓ).differentiable (by simp)
  have hline : HasDerivAt (fun t : ℝ => N + t • R) R 0 := by
    exact (hasDerivAt_const_add_iff N).mpr (by
      simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const R)
  have hcomp := (hQ N).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline
    (by simp only [zero_smul, add_zero])
  ext i j
  exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hcomp i) j).deriv).symm

private lemma projection_filter_chain_rule {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {m n : ℕ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (N : E → Fin m → Fin n → ℝ) (x v : E)
    (hN : DifferentiableAt ℝ N x) :
    fderiv ℝ (fun y => fun i j => Q ℓ (Matrix.of (N y)) i j) x v =
      dirDeriv ℓ (Matrix.of (N x)) (Matrix.of (fderiv ℝ N x v)) := by
  have h := congrArg (fun L => L v) (fderiv_comp x
    ((projection_Q_contDiff hℓ).differentiable (by simp) (N x)) hN)
  exact h.trans (projection_filter_fderiv hℓ _ _)

private lemma projection_phys_hasDerivAt {m n : ℕ} (C : Covariances m n)
    {q : ℝ → Vec m × Vec n} {q' : Vec m × Vec n} {x : ℝ}
    (hq : HasDerivAt q q' x) :
    HasDerivAt (fun t => phys C (q t)) (phys C q') x := by
  apply HasDerivAt.prodMk
  · apply hasDerivAt_pi.mpr
    intro i
    simpa only [Matrix.mulVec, dotProduct] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
        (hasDerivAt_pi.mp hq.fst j).const_mul (rOut C i j))
  · apply hasDerivAt_pi.mpr
    intro i
    simpa only [Matrix.mulVec, dotProduct] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
        (hasDerivAt_pi.mp hq.snd j).const_mul (rIn C i j))

private lemma projection_resid_hasDerivAt {m n : ℕ} (D : Mat m n)
    {q : ℝ → Vec m × Vec n} {q' : Vec m × Vec n} {x : ℝ}
    (hq : HasDerivAt q q' x) :
    HasDerivAt (fun t => resid D (q t))
      (resid D (q'.1, (q x).2) + resid D ((q x).1, q'.2)) x := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_pi.mp hq.fst i).mul
      (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
        (hasDerivAt_pi.mp hq.snd j).const_mul (D i j))))
  simp only [Pi.mul_apply, Finset.sum_add_distrib] at h
  convert! h using 1

private lemma projection_frobIP_smul_outer {m n : ℕ} (T : Mat m n)
    (a : ℝ) (z : Vec m) (w : Vec n) :
    frobIP T (a • outer z w) = a * resid T (z, w) := by
  simp only [frobIP, resid, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.smul_apply, outer, Matrix.vecMulVec_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma projection_sample_test_hasDerivAt {m n : ℕ} (D T : Mat m n)
    {q : ℝ → Vec m × Vec n} {q' : Vec m × Vec n} {x : ℝ}
    (hq : HasDerivAt q q' x) :
    HasDerivAt (fun t => frobIP T (resid D (q t) • outer (q t).1 (q t).2))
      ((resid D (q'.1, (q x).2) + resid D ((q x).1, q'.2)) * resid T (q x) +
        resid D (q x) * (resid T (q'.1, (q x).2) + resid T ((q x).1, q'.2))) x := by
  simp only [projection_frobIP_smul_outer]
  convert! (projection_resid_hasDerivAt D hq).mul
    (projection_resid_hasDerivAt T hq) using 1

private lemma projection_sample_hasDerivAt {m n : ℕ} (D : Mat m n)
    {q : ℝ → Vec m × Vec n} {q' : Vec m × Vec n} {x : ℝ}
    (hq : HasDerivAt q q' x) :
    HasDerivAt (fun t => fun i j => (resid D (q t) • outer (q t).1 (q t).2) i j)
      (fun i j =>
        ((resid D (q'.1, (q x).2) + resid D ((q x).1, q'.2)) •
          outer (q x).1 (q x).2 +
        resid D (q x) • (outer q'.1 (q x).2 + outer (q x).1 q'.2)) i j) x := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h := (projection_resid_hasDerivAt D hq).mul
    ((hasDerivAt_pi.mp hq.fst i).mul (hasDerivAt_pi.mp hq.snd j))
  simp only [Pi.mul_apply] at h
  convert! h using 1

private lemma projection_frobIP_hasDerivAt {m n : ℕ} (T : Mat m n)
    {N : ℝ → Fin m → Fin n → ℝ} {R : Fin m → Fin n → ℝ} {x : ℝ}
    (hN : HasDerivAt N R x) :
    HasDerivAt (fun t => frobIP T (Matrix.of (N t))) (frobIP T (Matrix.of R)) x := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hN i) j).const_mul (T i j)))
  convert! h using 1

private lemma projection_batch_hasDerivAt {m n B : ℕ}
    (C : Covariances m n) (D : Mat m n)
    {z : ℝ → Batch m n B} {z' : Batch m n B} {x : ℝ}
    (hz : HasDerivAt z z' x) :
    let q := fun a => phys C (z x a)
    let h := fun a => phys C (z' a)
    HasDerivAt (fun t => fun i j => batchGrad D (fun a => phys C (z t a)) i j)
      (fun i j => ((B : ℝ)⁻¹ • ∑ a : Fin B,
        ((resid D ((h a).1, (q a).2) + resid D ((q a).1, (h a).2)) •
          outer (q a).1 (q a).2 +
        resid D (q a) • (outer (h a).1 (q a).2 + outer (q a).1 (h a).2))) i j) x := by
  dsimp only
  have h := (HasDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
    projection_sample_hasDerivAt D
      (projection_phys_hasDerivAt C (hasDerivAt_pi.mp hz a)))).const_smul (B : ℝ)⁻¹
  convert! h using 1

private lemma projection_finite_chain_rule {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {m n : ℕ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (s : Finset ι) (w : ι → ℝ)
    (G : ι → E → Fin m → Fin n → ℝ) (T : Mat m n) (x v : E)
    (hG : ∀ j ∈ s, DifferentiableAt ℝ (G j) x) :
    let N := ∑ j ∈ s, w j • G j x
    let R := ∑ j ∈ s, w j • fderiv ℝ (G j) x v
    fderiv ℝ (fun y => frobIP T (Q ℓ (Matrix.of (∑ j ∈ s, w j • G j y)))) x v =
      frobIP T (dirDeriv ℓ (Matrix.of N) (Matrix.of R)) := by
  dsimp only
  let N : E → Fin m → Fin n → ℝ := fun y => ∑ j ∈ s, w j • G j y
  have hN : DifferentiableAt ℝ N x :=
    DifferentiableAt.fun_sum (fun j hj => (hG j hj).const_smul (w j))
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    exact (hasDerivAt_const_add_iff x).mpr (by
      simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const v)
  have hNline := hN.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hQline := ((projection_Q_contDiff hℓ).differentiable (by simp) (N x)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hNline (by simp)
  have htest := projection_frobIP_hasDerivAt T hQline
  have htestdiff : DifferentiableAt ℝ
      (fun y => frobIP T (Q ℓ (Matrix.of (N y)))) x := by
    have hQ := (projection_Q_contDiff hℓ).differentiable (by simp) (N x) |>.comp x hN
    simp only [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    exact DifferentiableAt.fun_sum (fun i _ => DifferentiableAt.fun_sum (fun j _ =>
      (differentiableAt_pi.mp (differentiableAt_pi.mp hQ i) j).const_mul (T i j)))
  have htestline := htestdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hR : fderiv ℝ N x v = ∑ j ∈ s, w j • fderiv ℝ (G j) x v := by
    have h := (HasFDerivAt.fun_sum (fun j hj =>
      (hG j hj).hasFDerivAt.const_smul (w j))).fderiv
    simpa [N] using congrArg (fun L => L v) h
  have h := htestline.unique htest
  rw [projection_filter_fderiv hℓ, hR] at h
  exact h

private lemma projection_finite_contDiff {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {m n : ℕ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (s : Finset ι) (w : ι → ℝ)
    (G : ι → E → Fin m → Fin n → ℝ) (T : Mat m n)
    (hG : ∀ j ∈ s, ContDiff ℝ 1 (G j)) :
    ContDiff ℝ 1
      (fun y => frobIP T (Q ℓ (Matrix.of (∑ j ∈ s, w j • G j y)))) := by
  have hN : ContDiff ℝ 1 (fun y => ∑ j ∈ s, w j • G j y) :=
    ContDiff.sum (fun j hj => (hG j hj).const_smul (w j))
  have hQ := ((projection_Q_contDiff hℓ).of_le (by simp :
    (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).comp hN
  simp only [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (contDiff_const.mul (contDiff_pi.mp (contDiff_pi.mp hQ i) j))))

private lemma projection_frobIP_representer {m n : ℕ}
    (L : (Fin m → Fin n → ℝ) →L[ℝ] ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hL : ∀ R : Fin m → Fin n → ℝ, |L R| ≤ c * fro (Matrix.of R)) :
    ∃ C : Mat m n, fro C ≤ c ∧
      ∀ R : Fin m → Fin n → ℝ, L R = frobIP C (Matrix.of R) := by
  classical
  let C : Mat m n := Matrix.of fun i j => L (Pi.single i (Pi.single j 1))
  have hsingle (i : Fin m) (j : Fin n) (a : ℝ) :
      (Pi.single i (Pi.single j a) : Fin m → Fin n → ℝ) =
        a • Pi.single i (Pi.single j (1 : ℝ)) := by
    ext k l
    by_cases hk : k = i <;> by_cases hl : l = j <;>
      simp [Pi.single_apply, hk, hl, eq_comm]
  have hrepr (R : Fin m → Fin n → ℝ) : L R = frobIP C (Matrix.of R) := by
    calc
      L R = ∑ i, L (Pi.single i (R i)) := by rw [← map_sum, Finset.univ_sum_single]
      _ = ∑ i, ∑ j, R i j * C i j := by
        apply Finset.sum_congr rfl
        intro i _
        have hi : (Pi.single i (R i) : Fin m → Fin n → ℝ) =
            ∑ j, Pi.single i (Pi.single j (R i j)) := by
          ext k l
          by_cases hk : k = i
          · subst k
            simp [Pi.single_apply]
          · simp [Pi.single_apply, hk]
        rw [hi, map_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [hsingle, map_smul]
        rfl
      _ = frobIP C (Matrix.of R) := by
        simp only [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Matrix.transpose_apply, Matrix.of_apply]
        congr 1
        ext i
        congr 1
        ext j
        exact mul_comm _ _
  have hsq : frobIP C C = fro C ^ 2 := by
    simp only [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    unfold fro
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
    simp [Real.norm_eq_abs, sq_abs, pow_two]
  refine ⟨C, ?_, hrepr⟩
  have h := hL (fun i j => C i j)
  rw [hrepr] at h
  change |frobIP C C| ≤ c * fro C at h
  rw [hsq, abs_of_nonneg (sq_nonneg _)] at h
  nlinarith [Real.sqrt_nonneg (∑ i, ∑ j, ‖C i j‖ ^ 2)]

private lemma projection_filter_adjoint_test {m n : ℕ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (N T : Mat m n) :
    ∃ C : Mat m n, fro C ≤ ℓ ^ (-(1 / 2 : ℝ)) * fro T ∧
      ∀ R : Mat m n, frobIP T (dirDeriv ℓ N R) = frobIP C R := by
  let L := fderiv ℝ (fun M : Fin m → Fin n → ℝ => frobIP T (Q ℓ (Matrix.of M)))
    (fun i j => N i j)
  have hL (R : Fin m → Fin n → ℝ) :
      L R = frobIP T (dirDeriv ℓ N (Matrix.of R)) := by
    have h := projection_finite_chain_rule hℓ ({()} : Finset Unit) (fun _ => (1 : ℝ))
      (fun (_ : Unit) (y : Fin m → Fin n → ℝ) => y) T (fun i j => N i j) R
      (fun _ _ => differentiableAt_id)
    have h' : L R = frobIP T (dirDeriv ℓ
        (Matrix.of (fun i j => N i j)) (Matrix.of R)) := by
      simpa [L] using h
    convert! h' using 1
  obtain ⟨C, hC, hrepr⟩ := projection_frobIP_representer L
    (ℓ ^ (-(1 / 2 : ℝ)) * fro T)
    (mul_nonneg (Real.rpow_nonneg hℓ.le _) (Real.sqrt_nonneg _))
    (fun R => by rw [hL]; exact projection_filter_test_bound hℓ T N (Matrix.of R))
  refine ⟨C, hC, ?_⟩
  intro R
  exact (hL (fun i j => R i j)).symm.trans (hrepr (fun i j => R i j))

private lemma projection_ema_sq_sum_le_one {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), emaW β j ^ 2 ≤ 1 := by
  rw [startup_weight_sq_sum hβ0 hβ1, sPow_two hβ0 hβ1]
  have ha : 0 ≤ (1 - β) / (1 + β) := div_nonneg (by linarith) (by linarith)
  have hb : (1 - β) / (1 + β) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  exact (mul_le_of_le_one_right ha (by nlinarith [pow_nonneg hβ0 (2 * (J + 1))])).trans hb

private lemma projection_gradient_energy_coordinates {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) :
    ‖fderiv ℝ f x‖ ^ 2 =
      ∑ a : ι, (fderiv ℝ f x (EuclideanSpace.basisFun ι ℝ a)) ^ 2 := by
  exact (EuclideanSpace.basisFun ι ℝ).norm_dual (fderiv ℝ f x)

private lemma projection_ema_energy_sum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (J : ℕ)
    (E : ℕ → Ω → ℝ≥0∞) (hE : ∀ j, AEMeasurable (E j) P)
    (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ j, ∫⁻ ω, E j ω ∂P ≤ ENNReal.ofReal c) :
    ∫⁻ ω, ∑ j ∈ Finset.range (J + 1), ENNReal.ofReal (emaW β j ^ 2) * E j ω ∂P ≤
      ENNReal.ofReal c := by
  rw [lintegral_finsetSum' _ (fun j _ => (hE j).const_mul _)]
  calc
    ∑ j ∈ Finset.range (J + 1),
        ∫⁻ ω, ENNReal.ofReal (emaW β j ^ 2) * E j ω ∂P ≤
        ∑ j ∈ Finset.range (J + 1),
          ENNReal.ofReal (emaW β j ^ 2) * ENNReal.ofReal c := by
      apply Finset.sum_le_sum
      intro j _
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      exact hbound j
    _ = ENNReal.ofReal (∑ j ∈ Finset.range (J + 1), emaW β j ^ 2) * ENNReal.ofReal c := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _), Finset.sum_mul]
    _ ≤ ENNReal.ofReal c := by
      exact mul_le_of_le_one_left (by positivity)
        (by simpa using ENNReal.ofReal_le_ofReal (projection_ema_sq_sum_le_one hβ0 hβ1 J))

private lemma projection_truncation_weight_sq_sum_le_two {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (r J : ℕ) :
    ∑ j : Fin (r + 1) ⊕ Fin J, (Sum.elim
      (fun i : Fin (r + 1) => emaW β (r + 1 - (i + 1)))
      (fun j : Fin J => β ^ (r + 1) * emaW β j) j) ^ 2 ≤ 2 := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hfirst : (∑ i : Fin (r + 1), emaW β (r + 1 - (i + 1)) ^ 2) =
      ∑ i : Fin (r + 1), emaW β i ^ 2 := by
    let e : Fin (r + 1) ≃ Fin (r + 1) :=
      ⟨Fin.rev, Fin.rev, Fin.rev_involutive.leftInverse, Fin.rev_involutive.rightInverse⟩
    apply Fintype.sum_equiv e
    intro i
    simp [e, Fin.rev]
  rw [hfirst]
  have hleft : (∑ i : Fin (r + 1), emaW β i ^ 2) ≤ 1 := by
    change (∑ i : Fin (r + 1), (fun j : ℕ => emaW β j ^ 2) i) ≤ 1
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => emaW β j ^ 2) (r + 1)]
    exact projection_ema_sq_sum_le_one hβ0 hβ1 r
  have hright0 : (∑ j : Fin J, emaW β j ^ 2) ≤ 1 := by
    change (∑ i : Fin J, (fun j : ℕ => emaW β j ^ 2) i) ≤ 1
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => emaW β j ^ 2) J]
    by_cases hJ : J = 0
    · subst J
      simp
    · have hJ1 : 1 ≤ J := Nat.one_le_iff_ne_zero.mpr hJ
      simpa only [Nat.sub_add_cancel hJ1] using
        projection_ema_sq_sum_le_one hβ0 hβ1 (J - 1)
  have hpow : (β ^ (r + 1)) ^ 2 ≤ 1 := by
    have hb1 : β ^ (r + 1) ≤ 1 := pow_le_one₀ hβ0 hβ1.le
    exact pow_le_one₀ (pow_nonneg hβ0 _) hb1
  have hright : (∑ j : Fin J, (β ^ (r + 1) * emaW β j) ^ 2) ≤ 1 := by
    calc
      _ = (β ^ (r + 1)) ^ 2 * ∑ j : Fin J, emaW β j ^ 2 := by
        simp only [mul_pow, Finset.mul_sum]
      _ ≤ 1 * 1 := mul_le_mul hpow hright0 (by positivity) (by norm_num)
      _ = 1 := by norm_num
  linarith

private lemma projection_fintype_energy_sum_le_two {Ω κ : Type*}
    [MeasurableSpace Ω] [Fintype κ] (P : Measure Ω) (w : κ → ℝ)
    (E : κ → Ω → ℝ≥0∞) (hE : ∀ k, AEMeasurable (E k) P)
    (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ k, ∫⁻ x, E k x ∂P ≤ ENNReal.ofReal c)
    (hw : ∑ k, w k ^ 2 ≤ 2) :
    ∫⁻ x, ∑ k, ENNReal.ofReal (w k ^ 2) * E k x ∂P ≤ ENNReal.ofReal (2 * c) := by
  rw [lintegral_finsetSum' _ (fun k _ => (hE k).const_mul _)]
  calc
    ∑ k, ∫⁻ x, ENNReal.ofReal (w k ^ 2) * E k x ∂P ≤
        ∑ k, ENNReal.ofReal (w k ^ 2) * ENNReal.ofReal c := by
      apply Finset.sum_le_sum
      intro k _
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      exact hbound k
    _ = ENNReal.ofReal (∑ k, w k ^ 2) * ENNReal.ofReal c := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _), Finset.sum_mul]
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal c := by
      gcongr
    _ = ENNReal.ofReal (2 * c) := by
      rw [ENNReal.ofReal_mul (by norm_num)]

private lemma projection_batch_pos_of_risk_pos (p : DynParams) {m n B : ℕ}
    (C : Covariances m n) (hsize : SizeFin C B p.γstar p.CSig)
    (D : Mat m n) (hD : 0 < riskSigma C D) : 0 < B := by
  by_contra hn
  have hB0 : B = 0 := Nat.eq_zero_of_not_pos hn
  have hdim : ((max m n : ℕ) : ℝ) ≤ 0 := by
    simpa only [hB0, Nat.cast_zero, mul_zero] using hsize.1
  have hmax : max m n = 0 := by
    exact Nat.eq_zero_of_le_zero (by exact_mod_cast hdim)
  have hm : m = 0 := Nat.eq_zero_of_le_zero ((Nat.le_max_left m n).trans_eq hmax)
  have hn' : n = 0 := Nat.eq_zero_of_le_zero ((Nat.le_max_right m n).trans_eq hmax)
  subst m
  subst n
  simp [riskSigma, pairSigma] at hD

private lemma projection_variance_tendsto_of_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (C : ℝ) (hY : ∀ J, AEStronglyMeasurable (Y J) P)
    (hX : AEStronglyMeasurable X P)
    (hYC : ∀ J, ∀ᵐ ω ∂P, ‖Y J ω‖ ≤ C) (hXC : ∀ᵐ ω ∂P, ‖X ω‖ ≤ C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun J => Y J ω) atTop (𝓝 (X ω))) :
    Tendsto (fun J => variance (Y J) P) atTop (𝓝 (variance X P)) := by
  have hmemY (J : ℕ) : MemLp (Y J) 2 P := MemLp.of_bound (hY J) C (hYC J)
  have hmemX : MemLp X 2 P := MemLp.of_bound hX C hXC
  have hmean := tendsto_integral_of_dominated_convergence (fun _ : Ω => C) hY
    (integrable_const C) hYC hlim
  have hsquare : Tendsto (fun J => ∫ ω, (Y J ω) ^ 2 ∂P) atTop
      (𝓝 (∫ ω, (X ω) ^ 2 ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Ω => C ^ 2)
      (fun J => (hY J).pow 2) (integrable_const _) _ _
    · intro J
      filter_upwards [hYC J] with ω hω
      rw [Pi.pow_apply, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hω 2
    · filter_upwards [hlim] with ω hω using hω.pow 2
  simpa only [variance_eq_sub (hmemY _), variance_eq_sub hmemX, Pi.pow_apply] using
    hsquare.sub (hmean.pow 2)

private lemma projection_Q_uniform_bound {m n : ℕ} (T N : Mat m n) {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) :
    ‖frobIP T (Q ℓ N)‖ ≤
      (∑ i, ∑ j, |T i j|) * Real.sqrt ((min m n : ℕ) : ℝ) := by
  have hfilter := lem_app_setup_filter_i ℓ hℓ N
  have hentry (i : Fin m) (j : Fin n) :
      |Q ℓ N i j| ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
    apply Real.abs_le_sqrt
    exact (projection_entry_sq_le_fro (Q ℓ N) i j).trans
      (hfilter.2.1.trans (Nat.cast_le.mpr hfilter.2.2.1))
  simp only [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  calc
    ‖∑ i, ∑ j, T i j * Q ℓ N i j‖ ≤ ∑ i, ∑ j, ‖T i j * Q ℓ N i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, |T i j| * Real.sqrt ((min m n : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hentry i j) (abs_nonneg _)
    _ = _ := by simp only [Finset.sum_mul]

private lemma projection_emaChain_continuous_init {m n B : ℕ} (β : ℝ)
    (D : Mat m n) (G : ℤ → Batch m n B) (t k : ℕ) :
    Continuous (fun init : Mat m n => emaChain β D G t init k) := by
  induction k with
  | zero => exact continuous_id
  | succ k hk => exact (hk.const_smul β).add continuous_const

private lemma projection_stationary_truncation_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B)
    (t r : ℕ) (D T : Mat m n) (hD : 0 < riskSigma C D)
    (hS : SizeFin C B p.γstar p.CSig) :
    ∀ᵐ ω ∂P, Tendsto (fun J => frobIP T (Q (physRidge p C D)
      (emaChain p.β D (fun s => physBatch C (cs.act s) ω) t
        (∑ j ∈ Finset.range J,
          emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) (r + 1))))
      atTop (𝓝 (frobIP T (stationaryV p C cs t D r ω))) := by
  have hridge : 0 < physRidge p C D := by
    exact mul_pos (mul_pos (by norm_num) hD) p.hϱ
  filter_upwards [(lem_app_dyn_chains_iii p C cs t D 0 hD hS).1] with ω hω
  have hinit := hω.hasSum.tendsto_sum_nat
  have hchain := (projection_emaChain_continuous_init p.β D
    (fun s => physBatch C (cs.act s) ω) t (r + 1)).tendsto _ |>.comp hinit
  have hQ := (projection_Q_contDiff (m := m) (n := n) hridge).continuous
  have hscalar : Continuous (fun M : Fin m → Fin n → ℝ =>
      frobIP T (Q (physRidge p C D) (Matrix.of M))) := by
    simp only [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
      ((continuous_apply j).comp ((continuous_apply i).comp hQ)).const_mul (T i j)))
  exact hscalar.tendsto _ |>.comp hchain

private lemma projection_stationary_truncation_variance_tendsto {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B)
    (t r : ℕ) (D T : Mat m n) (hD : 0 < riskSigma C D)
    (hS : SizeFin C B p.γstar p.CSig) :
    Tendsto (fun J => variance (fun ω => frobIP T (Q (physRidge p C D)
      (emaChain p.β D (fun s => physBatch C (cs.act s) ω) t
        (∑ j ∈ Finset.range J,
          emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) (r + 1)))) P)
      atTop (𝓝 (variance (fun ω => frobIP T (stationaryV p C cs t D r ω)) P)) := by
  let Y : ℕ → Ω → ℝ := fun J ω => frobIP T (Q (physRidge p C D)
    (emaChain p.β D (fun s => physBatch C (cs.act s) ω) t
      (∑ j ∈ Finset.range J,
        emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) (r + 1)))
  have hridge : 0 ≤ physRidge p C D :=
    mul_nonneg (mul_nonneg (by norm_num) hD.le) p.hϱ.le
  have hQ : Measurable (fun M : Mat m n => Q (physRidge p C D) M) :=
    measurable_Q.comp
      ((measurable_const (a := (⟨physRidge p C D, hridge⟩ : Ici (0 : ℝ)))).prodMk
        measurable_id)
  have hY (J : ℕ) : AEStronglyMeasurable (Y J) P := by
    have hinit : Measurable (fun ω => ∑ j ∈ Finset.range J,
        emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) :=
      Finset.measurable_fun_sum _ (fun j _ =>
        (projection_batch_measurable C D _ (cs.meas_aux (t : ℤ) j)).const_smul (emaW p.β j))
    have hchain (k : ℕ) : Measurable (fun ω =>
        emaChain p.β D (fun s => physBatch C (cs.act s) ω) t
          (∑ j ∈ Finset.range J,
            emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) k) := by
      induction k with
      | zero => exact hinit
      | succ k hk =>
        exact (hk.const_smul p.β).add
          ((projection_batch_measurable C D _ (cs.meas_act _)).const_smul (1 - p.β))
    have htest : Continuous (fun M : Mat m n => frobIP T M) := by
      unfold frobIP Matrix.trace Matrix.diag
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      fun_prop
    exact (htest.measurable.comp (hQ.comp (hchain (r + 1)))).aestronglyMeasurable
  have htest : Continuous (fun M : Mat m n => frobIP T M) := by
    unfold frobIP Matrix.trace Matrix.diag
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  apply projection_variance_tendsto_of_bound Y _
    ((∑ i, ∑ j, |T i j|) * Real.sqrt ((min m n : ℕ) : ℝ)) hY
    (htest.comp_aestronglyMeasurable (projection_stationary_measurable p C cs t r D hD hS))
  · intro J
    exact Filter.Eventually.of_forall (fun ω => projection_Q_uniform_bound T _ hridge)
  · exact Filter.Eventually.of_forall (fun ω => projection_Q_uniform_bound T _ hridge)
  · exact projection_stationary_truncation_tendsto p C cs t r D T hD hS

private lemma projection_stationary_variance_le_of_truncation {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B)
    (t r : ℕ) (D T : Mat m n) (hD : 0 < riskSigma C D)
    (hS : SizeFin C B p.γstar p.CSig) (c : ℝ)
    (htrunc : ∀ J : ℕ, variance (fun ω => frobIP T (Q (physRidge p C D)
      (emaChain p.β D (fun s => physBatch C (cs.act s) ω) t
        (∑ j ∈ Finset.range J,
          emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) (r + 1)))) P ≤ c) :
    MemLp (fun ω => frobIP T (stationaryV p C cs t D r ω)) 2 P ∧
      variance (fun ω => frobIP T (stationaryV p C cs t D r ω)) P ≤ c := by
  refine ⟨projection_stationary_memLp p C cs t r D T hD hS, ?_⟩
  exact le_of_tendsto (projection_stationary_truncation_variance_tendsto p C cs t r D T hD hS)
    (Filter.Eventually.of_forall htrunc)

private lemma projection_chain_samples_joint_law {Ω ι : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ} [Fintype ι]
    (cs : ChainSamples P m n B)
    (q : ι → (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B)) (hq : Function.Injective q) :
    P.map (fun ω i => Sum.elim (fun a => cs.act a.1 a.2 ω)
      (fun a => cs.aux a.1 a.2.1 a.2.2 ω) (q i)) =
      Measure.pi (fun _ : ι =>
        (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) := by
  have hm (i : ι) : Measurable (fun ω =>
      Sum.elim (fun a => cs.act a.1 a.2 ω)
        (fun a => cs.aux a.1 a.2.1 a.2.2 ω) (q i)) := by
    cases q i with
    | inl a => exact cs.meas_act a.1 a.2
    | inr a => exact cs.meas_aux a.1 a.2.1 a.2.2
  have hlaw (i : ι) : P.map (fun ω =>
      Sum.elim (fun a => cs.act a.1 a.2 ω)
        (fun a => cs.aux a.1 a.2.1 a.2.2 ω) (q i)) =
      (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n) := by
    cases q i with
    | inl a => exact cs.law_act a.1 a.2
    | inr a => exact cs.law_aux a.1 a.2.1 a.2.2
  have hind := cs.indep.precomp hq
  have heq : (fun i => Sum.elim (fun a => cs.act a.1 a.2)
      (fun a => cs.aux a.1 a.2.1 a.2.2) (q i)) =
      (fun i ω => Sum.elim (fun a => cs.act a.1 a.2 ω)
        (fun a => cs.aux a.1 a.2.1 a.2.2 ω) (q i)) := by
    funext i ω
    cases q i <;> rfl
  rw [heq] at hind
  rw [hind.map_fun_eq_pi_map (fun i => (hm i).aemeasurable)]
  simp_rw [hlaw]

private lemma projection_gaussian_uncurry {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurePreserving (fun z : ι → κ → ℝ => fun a : ι × κ => z a.1 a.2)
      (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => gaussianReal 0 1)))
      (Measure.pi (fun _ : ι × κ => gaussianReal 0 1)) := by
  have hm : Measurable (fun z : ι → κ → ℝ => fun a : ι × κ => z a.1 a.2) := by
    fun_prop
  refine ⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun z : ι → κ → ℝ => fun a : ι × κ => z a.1 a.2) ⁻¹' univ.pi s =
      univ.pi (fun i : ι => univ.pi (fun j : κ => s (i, j))) := by
    ext z
    simp [Set.mem_pi, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type
    (fun a : ι × κ => (gaussianReal 0 1) (s a))).symm

private lemma projection_pi_uncurry {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun z : ι → κ → α => fun a : ι × κ => z a.1 a.2)
      (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ)))
      (Measure.pi (fun _ : ι × κ => μ)) := by
  have hm : Measurable (fun z : ι → κ → α => fun a : ι × κ => z a.1 a.2) := by
    fun_prop
  refine ⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun z : ι → κ → α => fun a : ι × κ => z a.1 a.2) ⁻¹' univ.pi s =
      univ.pi (fun i : ι => univ.pi (fun j : κ => s (i, j))) := by
    ext z
    simp [Set.mem_pi, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun a : ι × κ => μ (s a))).symm

private lemma projection_encoded_batch_measurePreserving {κ : Type*} [Fintype κ]
    {m n B d : ℕ} (e : ((κ × Fin B) × (Fin m ⊕ Fin n)) ≃ Fin d) (k : κ) :
    MeasurePreserving (fun y : Fin d → ℝ => fun a : Fin B =>
      (fun i => y (e ((k, a), Sum.inl i)), fun j => y (e ((k, a), Sum.inr j))))
      (Muon.Foundations.stdGaussianPi d)
      (Measure.pi (fun _ : Fin B =>
        (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))) := by
  classical
  let ν := (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)
  let μbatch := Measure.pi (fun _ : Fin B => ν)
  let H : (κ → Fin B → Vec m × Vec n) ≃ᵐ (Fin d → ℝ) :=
    { toFun := fun (z : κ → Fin B → Vec m × Vec n) =>
        (MeasurableEquiv.piCongrLeft (fun _ : Fin d => ℝ) e)
          (fun a => (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)).symm
            (z a.1.1 a.1.2) a.2)
      invFun := fun (y : Fin d → ℝ) (l : κ) (a : Fin B) =>
        ((fun i => y (e ((l, a), Sum.inl i)),
          fun j => y (e ((l, a), Sum.inr j))) : Vec m × Vec n)
      left_inv := by
        intro z
        ext l a q <;> simp [MeasurableEquiv.coe_piCongrLeft,
          MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi]
      right_inv := by
        intro y
        ext r
        obtain ⟨s, rfl⟩ := e.surjective r
        rcases s with ⟨⟨l, a⟩, q⟩
        cases q <;> simp [MeasurableEquiv.coe_piCongrLeft,
          MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi]
      measurable_toFun := by
        apply measurable_pi_lambda
        intro r
        rcases hs : e.symm r with ⟨⟨l, a⟩, q⟩
        cases q <;> simp [hs] <;> fun_prop
      measurable_invFun := by
        apply measurable_pi_lambda
        intro l
        apply measurable_pi_lambda
        intro a
        apply Measurable.prod
        · apply measurable_pi_lambda
          intro i
          fun_prop
        · apply measurable_pi_lambda
          intro j
          fun_prop }
  have h₀ := projection_pi_uncurry (ι := κ) (κ := Fin B) ν
  have h₁ := measurePreserving_pi
    (fun _ : κ × Fin B => ν)
    (fun _ : κ × Fin B => Measure.pi (fun _ : Fin m ⊕ Fin n => gaussianReal 0 1))
    (fun _ => measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Fin m ⊕ Fin n => gaussianReal 0 1))
  have h₂ := projection_gaussian_uncurry (ι := κ × Fin B) (κ := Fin m ⊕ Fin n)
  have h₃ := measurePreserving_piCongrLeft
    (fun _ : Fin d => gaussianReal 0 1) e
  have hfwd := h₃.comp (h₂.comp (h₁.comp h₀))
  have hfwd' : MeasurePreserving H
      (Measure.pi (fun _ : κ => μbatch)) (Muon.Foundations.stdGaussianPi d) := by
    convert! hfwd using 1 <;> rfl
  have hinv := hfwd'.symm H
  have heval := MeasureTheory.measurePreserving_eval
    (μ := fun _ : κ => μbatch) k
  have hcomp := heval.comp hinv
  convert! hcomp using 1

private lemma projection_encoded_euclidean_batch_measurePreserving {κ : Type*} [Fintype κ]
    {m n B d : ℕ} (e : ((κ × Fin B) × (Fin m ⊕ Fin n)) ≃ Fin d) (k : κ) :
    MeasurePreserving (fun y : EuclideanSpace ℝ (Fin d) => fun a : Fin B =>
      (fun i => y (e ((k, a), Sum.inl i)), fun j => y (e ((k, a), Sum.inr j))))
      (stdGaussian (EuclideanSpace ℝ (Fin d)))
      (Measure.pi (fun _ : Fin B =>
        (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))) := by
  have hto : MeasurePreserving
      (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
      (Muon.Foundations.stdGaussianPi d) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    ⟨by fun_prop, projection_gaussian_map_toLp d⟩
  have hfrom := hto.symm (MeasurableEquiv.toLp 2 (Fin d → ℝ))
  have hraw := projection_encoded_batch_measurePreserving e k
  convert! hraw.comp hfrom using 1

private lemma projection_gaussian_pair_coordinates (m n : ℕ) :
    MeasurePreserving (fun z : Vec m × Vec n => Sum.elim z.1 z.2)
      ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
      (Measure.pi (fun _ : Fin m ⊕ Fin n => gaussianReal 0 1)) := by
  exact measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin m ⊕ Fin n => gaussianReal 0 1)

private lemma projection_chain_samples_coordinate_law {Ω ι : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m n B d : ℕ} [Fintype ι]
    (cs : ChainSamples P m n B)
    (q : ι → (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B)) (hq : Function.Injective q)
    (e : (ι × (Fin m ⊕ Fin n)) ≃ Fin d) :
    P.map (fun ω k =>
      let a := e.symm k
      let z := Sum.elim (fun b => cs.act b.1 b.2 ω)
        (fun b => cs.aux b.1 b.2.1 b.2.2 ω) (q a.1)
      Sum.elim z.1 z.2 a.2) = Muon.Foundations.stdGaussianPi d := by
  let Z : Ω → ι → Vec m × Vec n := fun ω i =>
    Sum.elim (fun a => cs.act a.1 a.2 ω)
      (fun a => cs.aux a.1 a.2.1 a.2.2 ω) (q i)
  have hZ : MeasurePreserving Z P (Measure.pi (fun _ : ι =>
      (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))) := by
    refine ⟨measurable_pi_iff.mpr (fun i => ?_),
      projection_chain_samples_joint_law cs q hq⟩
    dsimp only [Z]
    cases q i with
    | inl a => exact cs.meas_act a.1 a.2
    | inr a => exact cs.meas_aux a.1 a.2.1 a.2.2
  have hp := measurePreserving_pi
    (fun _ : ι => (Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n))
    (fun _ : ι => Measure.pi (fun _ : Fin m ⊕ Fin n => gaussianReal 0 1))
    (fun _ => projection_gaussian_pair_coordinates m n)
  have he := measurePreserving_piCongrLeft
    (fun _ : Fin d => gaussianReal 0 1) e
  convert! (he.comp (projection_gaussian_uncurry.comp (hp.comp hZ))).map_eq using 1
  congr 1
  funext ω k
  simp [Function.comp_def, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply, Z]

private lemma projection_poincare_of_coordinate_law {Ω ι : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n B d : ℕ} [Fintype ι]
    (cert : Muon.External.GaussianPoincare) (cs : ChainSamples P m n B)
    (q : ι → (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B)) (hq : Function.Injective q)
    (e : (ι × (Fin m ⊕ Fin n)) ≃ Fin d)
    (F : (ι → Vec m × Vec n) → ℝ) (hF : ContDiff ℝ 1 F)
    (c : ℝ) (hc : 0 ≤ c)
    (henergy : ∫⁻ x : EuclideanSpace ℝ (Fin d),
      ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) =>
        F (fun i => (fun j => y (e (i, Sum.inl j)),
          fun j => y (e (i, Sum.inr j))))) x‖ₑ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ ENNReal.ofReal c) :
    MemLp (fun ω => F (fun i => Sum.elim (fun a => cs.act a.1 a.2 ω)
      (fun a => cs.aux a.1 a.2.1 a.2.2 ω) (q i))) 2 P ∧
      variance (fun ω => F (fun i => Sum.elim (fun a => cs.act a.1 a.2 ω)
        (fun a => cs.aux a.1 a.2.1 a.2.2 ω) (q i))) P ≤ c := by
  let Z : Ω → Fin d → ℝ := fun ω k =>
    let a := e.symm k
    let z := Sum.elim (fun b => cs.act b.1 b.2 ω)
      (fun b => cs.aux b.1 b.2.1 b.2.2 ω) (q a.1)
    Sum.elim z.1 z.2 a.2
  let f : EuclideanSpace ℝ (Fin d) → ℝ := fun y =>
    F (fun i => (fun j => y (e (i, Sum.inl j)), fun j => y (e (i, Sum.inr j))))
  have hf : ContDiff ℝ 1 f := hF.comp (by fun_prop)
  have hZ : MeasurePreserving Z P (Muon.Foundations.stdGaussianPi d) := by
    refine ⟨measurable_pi_iff.mpr (fun k => ?_),
      projection_chain_samples_coordinate_law cs q hq e⟩
    dsimp only [Z]
    cases hqk : q (e.symm k).1 with
    | inl a =>
      cases (e.symm k).2 with
      | inl j => exact (measurable_pi_apply j).comp (cs.meas_act a.1 a.2).fst
      | inr j => exact (measurable_pi_apply j).comp (cs.meas_act a.1 a.2).snd
    | inr a =>
      cases (e.symm k).2 with
      | inl j => exact (measurable_pi_apply j).comp (cs.meas_aux a.1 a.2.1 a.2.2).fst
      | inr j => exact (measurable_pi_apply j).comp (cs.meas_aux a.1 a.2.1 a.2.2).snd
  have h := projection_poincare_pi cert d f hf c hc henergy
  have hfun : (fun ω => f (WithLp.toLp 2 (Z ω))) =
      (fun ω => F (fun i => Sum.elim (fun a => cs.act a.1 a.2 ω)
        (fun a => cs.aux a.1 a.2.1 a.2.2 ω) (q i))) := by
    funext ω
    apply congrArg F
    funext i
    dsimp [f, Z]
    simp only [e.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  have hm := h.1.comp_measurePreserving hZ
  have hv := hZ.variance_fun_comp
    ((hf.continuous.comp (by fun_prop : Continuous (WithLp.toLp 2))).aemeasurable)
  simp only [Function.comp_def] at hm
  rw [hfun] at hm
  change variance (fun ω => f (WithLp.toLp 2 (Z ω))) P = _ at hv
  rw [hfun] at hv
  exact ⟨hm, hv.trans_le h.2⟩

private lemma projection_truncation_sample_index_injective (t k J B : ℕ) :
    Function.Injective (fun a : (Fin k ⊕ Fin J) × Fin B =>
      Sum.elim (fun i : Fin k => Sum.inl (((t : ℤ) + i + 1), a.2))
        (fun j : Fin J => Sum.inr ((t : ℤ), (j : ℕ), a.2)) a.1 :
      (Fin k ⊕ Fin J) × Fin B → (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  cases i <;> cases j <;>
    simp only [Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, Prod.mk.injEq, true_and] at h
  · rcases h with ⟨h, rfl⟩
    congr 2
    apply Fin.ext
    omega
  · rcases h with ⟨h, rfl⟩
    congr 2
    exact Fin.ext h

private lemma projection_emaChain_expansion {m n B : ℕ} (β : ℝ)
    (D : Mat m n) (G : ℤ → Batch m n B) (t : ℕ) (init : Mat m n) (k : ℕ) :
    emaChain β D G t init k = β ^ k • init +
      ∑ i ∈ Finset.range k, emaW β (k - (i + 1)) •
        batchGrad D (G ((t : ℤ) + i + 1)) := by
  induction k with
  | zero => simp [emaChain]
  | succ k ih =>
    rw [emaChain, ih, smul_add, Finset.smul_sum, smul_smul, ← pow_succ',
      Finset.sum_range_succ]
    have hw (i : ℕ) (hi : i ∈ Finset.range k) :
        β • (emaW β (k - (i + 1)) • batchGrad D (G ((t : ℤ) + i + 1))) =
          emaW β (k + 1 - (i + 1)) • batchGrad D (G ((t : ℤ) + i + 1)) := by
      rw [show k + 1 - (i + 1) = (k - (i + 1)) + 1 by
        have := Finset.mem_range.mp hi
        omega]
      simp only [emaW, pow_succ, smul_smul]
      congr 1
      ring
    rw [Finset.sum_congr rfl hw]
    simp [emaW, add_assoc, add_left_comm, add_comm]

private lemma projection_ema_truncation_weights {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (k J : ℕ) :
    (∑ i ∈ Finset.range k, emaW β (k - (i + 1)) ^ 2) +
      ∑ j ∈ Finset.range J, (β ^ k * emaW β j) ^ 2 ≤ 1 := by
  have hsum (N : ℕ) : ∑ i ∈ Finset.range N, emaW β i ^ 2 =
      (1 - β) / (1 + β) * (1 - β ^ (2 * N)) := by
    cases N with
    | zero => simp
    | succ N => rw [startup_weight_sq_sum hβ0 hβ1, sPow_two hβ0 hβ1]
  have hrev : (∑ i ∈ Finset.range k, emaW β (k - (i + 1)) ^ 2) =
      ∑ i ∈ Finset.range k, emaW β i ^ 2 := by
    simpa only [Nat.sub_sub, Nat.add_comm] using
      (Finset.sum_range_reflect (fun i => emaW β i ^ 2) k)
  rw [hrev]
  simp only [mul_pow, ← Finset.mul_sum]
  rw [hsum k, hsum J]
  have hc0 : 0 ≤ (1 - β) / (1 + β) := div_nonneg (by linarith) (by linarith)
  have hc1 : (1 - β) / (1 + β) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hk : β ^ (2 * k) = (β ^ k) ^ 2 := by rw [mul_comm 2 k, pow_mul]
  rw [hk]
  nlinarith [mul_nonneg (mul_nonneg hc0 (sq_nonneg (β ^ k)))
    (pow_nonneg hβ0 (2 * J))]

private lemma projection_emaChain_sum_type {m n B : ℕ} (β : ℝ)
    (D : Mat m n) (G : ℤ → Batch m n B) (t k J : ℕ) (H : Fin J → Mat m n) :
    emaChain β D G t (∑ j : Fin J, emaW β j • H j) k =
      ∑ a : Fin k ⊕ Fin J, Sum.elim
        (fun i : Fin k => emaW β (k - (i + 1)) •
          batchGrad D (G ((t : ℤ) + i + 1)))
        (fun j : Fin J => (β ^ k * emaW β j) • H j) a := by
  rw [projection_emaChain_expansion, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    emaW β (k - (i + 1)) • batchGrad D (G ((t : ℤ) + i + 1)))]
  simp only [Finset.smul_sum, smul_smul]
  exact add_comm _ _

private lemma projection_weighted_batches_contDiff {κ : Type*} [Fintype κ]
    {m n B : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (C : Covariances m n)
    (D T : Mat m n) (w : κ → ℝ) :
    ContDiff ℝ 1 (fun z : κ × Fin B → Vec m × Vec n => frobIP T
      (Q ℓ (∑ j : κ, w j • batchGrad D (fun a => phys C (z (j, a)))))) := by
  refine projection_finite_contDiff hℓ Finset.univ w
    (fun j (z : κ × Fin B → Vec m × Vec n) =>
      fun i l => batchGrad D (fun a => phys C (z (j, a))) i l) T ?_
  intro j _
  exact ((projection_batch_contDiff C D).of_le (by simp)).comp (by fun_prop)

private lemma projection_weighted_batches_poincare {Ω κ : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] [Fintype κ]
    {m n B d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (cert : Muon.External.GaussianPoincare) (cs : ChainSamples P m n B)
    (q : κ × Fin B → (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B)) (hq : Function.Injective q)
    (e : ((κ × Fin B) × (Fin m ⊕ Fin n)) ≃ Fin d)
    (C : Covariances m n) (D T : Mat m n) (w : κ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (henergy : ∫⁻ x : EuclideanSpace ℝ (Fin d),
      ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => frobIP T
        (Q ℓ (∑ j : κ, w j • batchGrad D (fun a => phys C
          (fun i => y (e ((j, a), Sum.inl i)),
            fun i => y (e ((j, a), Sum.inr i))))))) x‖ₑ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ ENNReal.ofReal c) :
    let Z := fun ω j a => phys C (Sum.elim (fun b => cs.act b.1 b.2 ω)
      (fun b => cs.aux b.1 b.2.1 b.2.2 ω) (q (j, a)))
    MemLp (fun ω => frobIP T (Q ℓ (∑ j : κ, w j • batchGrad D (Z ω j)))) 2 P ∧
      variance (fun ω => frobIP T (Q ℓ (∑ j : κ, w j • batchGrad D (Z ω j)))) P ≤ c := by
  exact projection_poincare_of_coordinate_law cert cs q hq e _
    (projection_weighted_batches_contDiff hℓ C D T w) c hc henergy

private lemma projection_stationary_variance_of_weighted_energy {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B)
    (cert : Muon.External.GaussianPoincare) (t r : ℕ) (D T : Mat m n)
    (hD : 0 < riskSigma C D) (hS : SizeFin C B p.γstar p.CSig)
    (c : ℝ) (hc : 0 ≤ c)
    (henergy : ∀ (J d : ℕ)
      (e : (((Fin (r + 1) ⊕ Fin J) × Fin B) × (Fin m ⊕ Fin n)) ≃ Fin d),
      let w : Fin (r + 1) ⊕ Fin J → ℝ := Sum.elim
        (fun i => emaW p.β (r + 1 - (i + 1)))
        (fun j => p.β ^ (r + 1) * emaW p.β j)
      ∫⁻ x : EuclideanSpace ℝ (Fin d),
        ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => frobIP T
          (Q (physRidge p C D) (∑ j : Fin (r + 1) ⊕ Fin J,
            w j • batchGrad D (fun a => phys C
              (fun i => y (e ((j, a), Sum.inl i)),
                fun i => y (e ((j, a), Sum.inr i))))))) x‖ₑ ^ 2
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ ENNReal.ofReal c) :
    MemLp (fun ω => frobIP T (stationaryV p C cs t D r ω)) 2 P ∧
      variance (fun ω => frobIP T (stationaryV p C cs t D r ω)) P ≤ c := by
  apply projection_stationary_variance_le_of_truncation p C cs t r D T hD hS c
  intro J
  let κ := Fin (r + 1) ⊕ Fin J
  let w : κ → ℝ := Sum.elim (fun i => emaW p.β (r + 1 - (i + 1)))
    (fun j => p.β ^ (r + 1) * emaW p.β j)
  let q : κ × Fin B → (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B) := fun a =>
    Sum.elim (fun i : Fin (r + 1) => Sum.inl (((t : ℤ) + i + 1), a.2))
      (fun j : Fin J => Sum.inr ((t : ℤ), (j : ℕ), a.2)) a.1
  let e := Fintype.equivFin ((κ × Fin B) × (Fin m ⊕ Fin n))
  have hridge : 0 < physRidge p C D := mul_pos (mul_pos (by norm_num) hD) p.hϱ
  have hb := projection_weighted_batches_poincare hridge cert cs q
    (projection_truncation_sample_index_injective t (r + 1) J B) e C D T w c hc
    (henergy J _ e)
  let N : Ω → Mat m n := fun ω => ∑ j : κ, w j • batchGrad D (fun a => phys C
    (Sum.elim (fun b => cs.act b.1 b.2 ω)
      (fun b => cs.aux b.1 b.2.1 b.2.2 ω) (q (j, a))))
  have hN (ω : Ω) : N ω =
      emaChain p.β D (fun s => physBatch C (cs.act s) ω) t
        (∑ j ∈ Finset.range J,
          emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) (r + 1) := by
    have hexp := projection_emaChain_sum_type p.β D
      (fun s => physBatch C (cs.act s) ω) t (r + 1) J
      (fun j => batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))
    rw [Fin.sum_univ_eq_sum_range (fun j =>
      emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))] at hexp
    rw [hexp]
    apply Finset.sum_congr rfl
    intro j _
    cases j <;> rfl
  have hv : variance (fun ω => frobIP T (Q (physRidge p C D) (N ω))) P ≤ c := hb.2
  simpa only [hN] using hv

private lemma projection_gaussian_sqnorm_memLp (n : ℕ) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun z : Vec n => ∑ i, z i ^ 2) p (Muon.Foundations.stdGaussianPi n) := by
  exact memLp_finsetSum _ fun i _ =>
    (Muon.Foundations.gaussian_memLp_pow 2 p hp).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)

private lemma projection_gaussian_norm_four (n : ℕ) :
    ∫ z : Vec n, (∑ i, z i ^ 2) ^ 2 ∂(Muon.Foundations.stdGaussianPi n) =
      (n : ℝ) * ((n : ℝ) + 2) := by
  simpa [Finset.prod_range_succ] using
    Muon.Foundations.stdGaussianPi_sq_norm_moment n 2 (by norm_num)

private lemma projection_gaussian_norm_eight (n : ℕ) :
    ∫ z : Vec n, (∑ i, z i ^ 2) ^ 4 ∂(Muon.Foundations.stdGaussianPi n) =
      (n : ℝ) * ((n : ℝ) + 2) * ((n : ℝ) + 4) * ((n : ℝ) + 6) := by
  have h := Muon.Foundations.stdGaussianPi_sq_norm_moment n 4 (by norm_num)
  norm_num [Finset.prod_range_succ] at h
  exact h

private lemma projection_fro_sq {m n : ℕ} (M : Mat m n) :
    fro M ^ 2 = ∑ i, ∑ j, M i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (by positivity)]
  simp only [Real.norm_eq_abs, sq_abs]

private lemma projection_fro_transpose {m n : ℕ} (M : Mat m n) : fro Mᵀ = fro M := by
  unfold fro
  congr 1
  exact Finset.sum_comm

private lemma projection_opNorm_transpose {m n : ℕ} (M : Mat m n) :
    opNorm Mᵀ = opNorm M := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma projection_opNorm_continuous {m n : ℕ} :
    Continuous (fun M : Mat m n => opNorm M) := by
  open scoped Matrix.Norms.L2Operator in
    have h : (fun M : Mat m n => opNorm M) = fun M => ‖M‖ := funext opNorm_eq_norm
    rw [h]
    exact continuous_norm

private lemma projection_rOut_transpose {m n : ℕ} (C : Covariances m n) :
    (rOut C)ᵀ = rOut C := by
  have h : (CFC.sqrt C.Sout)ᴴ = CFC.sqrt C.Sout :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sout)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma projection_rIn_transpose {m n : ℕ} (C : Covariances m n) :
    (rIn C)ᵀ = rIn C := by
  have h : (CFC.sqrt C.Sin)ᴴ = CFC.sqrt C.Sin :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma projection_resid_phys_left_basis {m n : ℕ} (C : Covariances m n)
    (D : Mat m n) (i : Fin m) (w : Vec n) :
    resid D (phys C (Pi.single i 1, w)) = (Arot C D *ᵥ w) i := by
  classical
  rw [eqn_app_setup_whitened_resid]
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

private lemma projection_resid_left_basis {m n : ℕ} (A : Mat m n)
    (i : Fin m) (w : Vec n) : resid A (Pi.single i 1, w) = (A *ᵥ w) i := by
  classical
  simp [resid, dotProduct, Matrix.mulVec, Pi.single_apply]

private lemma projection_resid_right_basis {m n : ℕ} (A : Mat m n)
    (z : Vec m) (j : Fin n) : resid A (z, Pi.single j 1) = (Aᵀ *ᵥ z) j := by
  classical
  simp only [resid, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hs : ∑ x, A i x * (if x = j then 1 else 0) = A i j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hs]
  exact mul_comm _ _

private lemma projection_resid_phys_parts {m n : ℕ} (C : Covariances m n)
    (D : Mat m n) (z : Vec m × Vec n) :
    resid D ((phys C z).1, (phys C z).2) = resid (Arot C D) z := by
  simpa only [resid] using eqn_app_setup_whitened_resid C D z

private lemma projection_resid_phys_right_basis {m n : ℕ} (C : Covariances m n)
    (D : Mat m n) (z : Vec m) (j : Fin n) :
    resid D (phys C (z, Pi.single j 1)) = ((Arot C D)ᵀ *ᵥ z) j := by
  classical
  rw [eqn_app_setup_whitened_resid]
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply]
  simp only [Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i _
  have hs : ∑ x, Arot C D i x * (if x = j then 1 else 0) = Arot C D i j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hs]
  exact mul_comm _ _

private lemma projection_phys_zero {m n : ℕ} (C : Covariances m n) :
    phys C (0 : Vec m × Vec n) = 0 := by
  ext <;> simp [phys, Matrix.mulVec]

private lemma projection_resid_zero_left {m n : ℕ} (D : Mat m n) (w : Vec n) :
    resid D (0, w) = 0 := by simp [resid, Matrix.mulVec, dotProduct]

private lemma projection_resid_zero_right {m n : ℕ} (D : Mat m n) (z : Vec m) :
    resid D (z, 0) = 0 := by simp [resid, Matrix.mulVec, dotProduct]

private lemma projection_outer_zero_left {m n : ℕ} (w : Vec n) :
    outer (0 : Vec m) w = 0 := by ext <;> simp [outer]

private lemma projection_outer_zero_right {m n : ℕ} (z : Vec m) :
    outer z (0 : Vec n) = 0 := by ext <;> simp [outer, Matrix.vecMulVec_apply]

private lemma projection_batch_test_fderiv_left {m n B : ℕ}
    (C : Covariances m n) (D M : Mat m n) (hB : 0 < B) (z : Batch m n B)
    (a : Fin B) (i : Fin m) :
    fderiv ℝ (fun y : Batch m n B => frobIP M
      (batchGrad D (fun b => phys C (y b)))) z
      (Pi.single a (Pi.single i 1, 0)) =
      (B : ℝ)⁻¹ *
        ((Arot C D *ᵥ (z a).2) i * resid (Arot C M) (z a) +
          resid (Arot C D) (z a) * (Arot C M *ᵥ (z a).2) i) := by
  classical
  let v : Batch m n B := Pi.single a (Pi.single i 1, 0)
  let A := Arot C D
  let N := Arot C M
  let g : Batch m n B → ℝ := fun y =>
    (B : ℝ)⁻¹ * ∑ b, resid A (y b) * resid N (y b)
  have hgfun : (fun y : Batch m n B => frobIP M
      (batchGrad D (fun b => phys C (y b)))) = g := by
    funext y
    dsimp only [g, A, N]
    unfold batchGrad Muon.Setup.grad
    rw [Finset.smul_sum]
    have hsum := frobIP_sum_right M Finset.univ (fun b =>
      (B : ℝ)⁻¹ • (resid D (phys C (y b)) •
        outer (phys C (y b)).1 (phys C (y b)).2))
    rw [hsum]
    simp_rw [smul_smul, projection_frobIP_smul_outer,
      eqn_app_setup_whitened_resid, projection_resid_phys_parts]
    change (∑ x, (B : ℝ)⁻¹ * resid (Arot C D) (y x) *
      resid (Arot C M) (y x)) = _
    rw [Finset.mul_sum]
    ring
  have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    exact (hasDerivAt_const_add_iff z).mpr (by
      simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const v)
  have hres (E : Mat m n) (b : Fin B) :=
    projection_resid_hasDerivAt E (hasDerivAt_pi.mp hline b)
  have hs := (HasDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
    (hres A b).mul (hres N b))).const_mul (B : ℝ)⁻¹
  have hdiff : DifferentiableAt ℝ g z := by
    dsimp only [g, A, N]
    unfold resid Matrix.mulVec dotProduct
    fun_prop
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have heq := hcomp.unique hs
  rw [hgfun]
  change fderiv ℝ g z v = _
  rw [heq]
  dsimp only [g, A, N, v]
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  rw [mul_eq_mul_left_iff]
  left
  rw [Finset.sum_eq_single a]
  · simp [projection_resid_left_basis, projection_resid_zero_right]
  · intro b _ hba
    simp [Pi.single_apply, hba, projection_resid_zero_left,
      projection_resid_zero_right]
  · simp

private lemma projection_batch_test_fderiv_right {m n B : ℕ}
    (C : Covariances m n) (D M : Mat m n) (hB : 0 < B) (z : Batch m n B)
    (a : Fin B) (j : Fin n) :
    fderiv ℝ (fun y : Batch m n B => frobIP M
      (batchGrad D (fun b => phys C (y b)))) z
      (Pi.single a (0, Pi.single j 1)) =
      (B : ℝ)⁻¹ *
        (((Arot C D)ᵀ *ᵥ (z a).1) j * resid (Arot C M) (z a) +
          resid (Arot C D) (z a) * ((Arot C M)ᵀ *ᵥ (z a).1) j) := by
  classical
  let v : Batch m n B := Pi.single a (0, Pi.single j 1)
  let A := Arot C D
  let N := Arot C M
  let g : Batch m n B → ℝ := fun y =>
    (B : ℝ)⁻¹ * ∑ b, resid A (y b) * resid N (y b)
  have hgfun : (fun y : Batch m n B => frobIP M
      (batchGrad D (fun b => phys C (y b)))) = g := by
    funext y
    dsimp only [g, A, N]
    unfold batchGrad Muon.Setup.grad
    rw [Finset.smul_sum]
    have hsum := frobIP_sum_right M Finset.univ (fun b =>
      (B : ℝ)⁻¹ • (resid D (phys C (y b)) •
        outer (phys C (y b)).1 (phys C (y b)).2))
    rw [hsum]
    simp_rw [smul_smul, projection_frobIP_smul_outer,
      eqn_app_setup_whitened_resid, projection_resid_phys_parts]
    change (∑ x, (B : ℝ)⁻¹ * resid (Arot C D) (y x) *
      resid (Arot C M) (y x)) = _
    rw [Finset.mul_sum]
    ring
  have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    exact (hasDerivAt_const_add_iff z).mpr (by
      simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const v)
  have hres (E : Mat m n) (b : Fin B) :=
    projection_resid_hasDerivAt E (hasDerivAt_pi.mp hline b)
  have hs := (HasDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
    (hres A b).mul (hres N b))).const_mul (B : ℝ)⁻¹
  have hdiff : DifferentiableAt ℝ g z := by
    dsimp only [g, A, N]
    unfold resid Matrix.mulVec dotProduct
    fun_prop
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have heq := hcomp.unique hs
  rw [hgfun]
  change fderiv ℝ g z v = _
  rw [heq]
  dsimp only [g, A, N, v]
  rw [mul_eq_mul_left_iff]
  left
  rw [Finset.sum_eq_single a]
  · simp [projection_resid_right_basis, projection_resid_zero_left]
  · intro b _ hba
    simp [Pi.single_apply, hba, projection_resid_zero_left,
      projection_resid_zero_right]
  · simp

private lemma projection_batch_test_differentiable {m n B : ℕ}
    (C : Covariances m n) (D M : Mat m n) (z : Batch m n B) :
    DifferentiableAt ℝ (fun y : Batch m n B => frobIP M
      (batchGrad D (fun b => phys C (y b)))) z := by
  have hmat := (projection_batch_contDiff C D).differentiable (by simp) z
  simp only [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact DifferentiableAt.fun_sum (fun k _ => DifferentiableAt.fun_sum (fun l _ =>
    (differentiableAt_pi.mp (differentiableAt_pi.mp hmat k) l).const_mul (M k l)))

private lemma projection_frobIP_fderiv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {m n : ℕ}
    (M : Mat m n) (G : E → Fin m → Fin n → ℝ) (x v : E)
    (hG : DifferentiableAt ℝ G x) :
    fderiv ℝ (fun y => frobIP M (Matrix.of (G y))) x v =
      frobIP M (Matrix.of (fderiv ℝ G x v)) := by
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    exact (hasDerivAt_const_add_iff x).mpr (by
      simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const v)
  have hGline := hG.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have htest := projection_frobIP_hasDerivAt M hGline
  have hscalar : DifferentiableAt ℝ (fun y => frobIP M (Matrix.of (G y))) x := by
    simp only [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.of_apply]
    exact DifferentiableAt.fun_sum (fun i _ => DifferentiableAt.fun_sum (fun j _ =>
      (differentiableAt_pi.mp (differentiableAt_pi.mp hG i) j).const_mul (M i j)))
  have hscalarLine := hscalar.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  exact hscalarLine.unique htest

private lemma projection_encoded_batch_fderiv_left {κ : Type*} [Fintype κ]
    [DecidableEq κ] {m n B d : ℕ}
    (e : ((κ × Fin B) × (Fin m ⊕ Fin n)) ≃ Fin d)
    (C : Covariances m n) (D M : Mat m n) (hB : 0 < B)
    (x : EuclideanSpace ℝ (Fin d)) (k j : κ) (a : Fin B) (i : Fin m) :
    let E := fun l (y : EuclideanSpace ℝ (Fin d)) (b : Fin B) =>
      ((fun q => y (e ((l, b), Sum.inl q)), fun q => y (e ((l, b), Sum.inr q))) :
        Vec m × Vec n)
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => frobIP M
      (batchGrad D (fun b => phys C (E k y b)))) x
      (EuclideanSpace.basisFun (Fin d) ℝ (e ((j, a), Sum.inl i))) =
      if k = j then (B : ℝ)⁻¹ *
        ((Arot C D *ᵥ (E j x a).2) i * resid (Arot C M) (E j x a) +
          resid (Arot C D) (E j x a) * (Arot C M *ᵥ (E j x a).2) i) else 0 := by
  dsimp only
  classical
  let E := fun l (y : EuclideanSpace ℝ (Fin d)) (b : Fin B) =>
    ((fun q => y (e ((l, b), Sum.inl q)), fun q => y (e ((l, b), Sum.inr q))) :
      Vec m × Vec n)
  let v := EuclideanSpace.basisFun (Fin d) ℝ (e ((j, a), Sum.inl i))
  let u : Batch m n B := Pi.single a (Pi.single i 1, 0)
  let F : EuclideanSpace ℝ (Fin d) → ℝ := fun y => frobIP M
    (batchGrad D (fun b => phys C (E k y b)))
  have hF : DifferentiableAt ℝ F x :=
    (projection_batch_test_differentiable C D M (E k x)).comp x (by fun_prop)
  have hxline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    exact (hasDerivAt_const_add_iff x).mpr (by
      simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const v)
  have hglobal := hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hxline (by simp)
  by_cases hkj : k = j
  · subst k
    have hpath : (fun t : ℝ => E j (x + t • v)) =
        (fun t => E j x + t • u) := by
      funext t
      funext b
      apply Prod.ext
      · funext q
        by_cases hba : b = a
        · subst b
          simp [E, v, u, EuclideanSpace.basisFun_apply, Pi.single_apply]
        · simp [E, v, u, EuclideanSpace.basisFun_apply, Pi.single_apply, hba]
      · funext q
        by_cases hba : b = a
        · subst b
          simp [E, v, u, EuclideanSpace.basisFun_apply, Pi.single_apply]
        · simp [E, v, u, EuclideanSpace.basisFun_apply, Pi.single_apply, hba]
    have huLine : HasDerivAt (fun t : ℝ => E j x + t • u) u 0 := by
      exact (hasDerivAt_const_add_iff (E j x)).mpr (by
        simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const u)
    have hlocal := (projection_batch_test_differentiable C D M (E j x)).hasFDerivAt
      |>.comp_hasDerivAt_of_eq 0 huLine (by simp)
    have hlocal' : HasDerivAt (F ∘ fun t : ℝ => x + t • v)
        ((fderiv ℝ (fun y : Batch m n B => frobIP M
          (batchGrad D (fun b => phys C (y b)))) (E j x)) u) 0 := by
      rw [show (F ∘ fun t : ℝ => x + t • v) = fun t => frobIP M
          (batchGrad D (fun b => phys C ((E j x + t • u) b))) by
        funext t
        change frobIP M (batchGrad D (fun b => phys C (E j (x + t • v) b))) = _
        rw [congrFun hpath t]]
      exact hlocal
    have heq := hglobal.unique hlocal'
    rw [if_pos rfl]
    exact heq.trans (projection_batch_test_fderiv_left C D M hB (E j x) a i)
  · have hpath : (fun t : ℝ => E k (x + t • v)) = fun _ => E k x := by
      funext t
      funext b
      apply Prod.ext
      · funext q
        simp [E, v, EuclideanSpace.basisFun_apply, hkj]
      · funext q
        simp [E, v, EuclideanSpace.basisFun_apply, hkj]
    have hzero : HasDerivAt (fun _t : ℝ => frobIP M
        (batchGrad D (fun b => phys C (E k x b)))) 0 0 := hasDerivAt_const _ _
    have hzero' : HasDerivAt (F ∘ fun t : ℝ => x + t • v) 0 0 := by
      rw [show (F ∘ fun t : ℝ => x + t • v) = fun _ => frobIP M
          (batchGrad D (fun b => phys C (E k x b))) by
        funext t
        change frobIP M (batchGrad D (fun b => phys C (E k (x + t • v) b))) = _
        rw [congrFun hpath t]]
      exact hzero
    have heq := hglobal.unique hzero'
    rw [if_neg hkj]
    exact heq

private lemma projection_encoded_batch_fderiv_right {κ : Type*} [Fintype κ]
    [DecidableEq κ] {m n B d : ℕ}
    (e : ((κ × Fin B) × (Fin m ⊕ Fin n)) ≃ Fin d)
    (C : Covariances m n) (D M : Mat m n) (hB : 0 < B)
    (x : EuclideanSpace ℝ (Fin d)) (k j : κ) (a : Fin B) (i : Fin n) :
    let E := fun l (y : EuclideanSpace ℝ (Fin d)) (b : Fin B) =>
      ((fun q => y (e ((l, b), Sum.inl q)), fun q => y (e ((l, b), Sum.inr q))) :
        Vec m × Vec n)
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => frobIP M
      (batchGrad D (fun b => phys C (E k y b)))) x
      (EuclideanSpace.basisFun (Fin d) ℝ (e ((j, a), Sum.inr i))) =
      if k = j then (B : ℝ)⁻¹ *
        (((Arot C D)ᵀ *ᵥ (E j x a).1) i * resid (Arot C M) (E j x a) +
          resid (Arot C D) (E j x a) * ((Arot C M)ᵀ *ᵥ (E j x a).1) i) else 0 := by
  dsimp only
  classical
  let E := fun l (y : EuclideanSpace ℝ (Fin d)) (b : Fin B) =>
    ((fun q => y (e ((l, b), Sum.inl q)), fun q => y (e ((l, b), Sum.inr q))) :
      Vec m × Vec n)
  let v := EuclideanSpace.basisFun (Fin d) ℝ (e ((j, a), Sum.inr i))
  let u : Batch m n B := Pi.single a (0, Pi.single i 1)
  let F : EuclideanSpace ℝ (Fin d) → ℝ := fun y => frobIP M
    (batchGrad D (fun b => phys C (E k y b)))
  have hF : DifferentiableAt ℝ F x :=
    (projection_batch_test_differentiable C D M (E k x)).comp x (by fun_prop)
  have hxline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    exact (hasDerivAt_const_add_iff x).mpr (by
      simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const v)
  have hglobal := hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hxline (by simp)
  by_cases hkj : k = j
  · subst k
    have hpath : (fun t : ℝ => E j (x + t • v)) =
        (fun t => E j x + t • u) := by
      funext t
      funext b
      apply Prod.ext
      · funext q
        by_cases hba : b = a
        · subst b
          simp [E, v, u, EuclideanSpace.basisFun_apply, Pi.single_apply]
        · simp [E, v, u, EuclideanSpace.basisFun_apply, Pi.single_apply, hba]
      · funext q
        by_cases hba : b = a
        · subst b
          simp [E, v, u, EuclideanSpace.basisFun_apply, Pi.single_apply]
        · simp [E, v, u, EuclideanSpace.basisFun_apply, Pi.single_apply, hba]
    have huLine : HasDerivAt (fun t : ℝ => E j x + t • u) u 0 := by
      exact (hasDerivAt_const_add_iff (E j x)).mpr (by
        simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const u)
    have hlocal := (projection_batch_test_differentiable C D M (E j x)).hasFDerivAt
      |>.comp_hasDerivAt_of_eq 0 huLine (by simp)
    have hlocal' : HasDerivAt (F ∘ fun t : ℝ => x + t • v)
        ((fderiv ℝ (fun y : Batch m n B => frobIP M
          (batchGrad D (fun b => phys C (y b)))) (E j x)) u) 0 := by
      rw [show (F ∘ fun t : ℝ => x + t • v) = fun t => frobIP M
          (batchGrad D (fun b => phys C ((E j x + t • u) b))) by
        funext t
        change frobIP M (batchGrad D (fun b => phys C (E j (x + t • v) b))) = _
        rw [congrFun hpath t]]
      exact hlocal
    have heq := hglobal.unique hlocal'
    rw [if_pos rfl]
    exact heq.trans (projection_batch_test_fderiv_right C D M hB (E j x) a i)
  · have hpath : (fun t : ℝ => E k (x + t • v)) = fun _ => E k x := by
      funext t
      funext b
      apply Prod.ext
      · funext q
        simp [E, v, EuclideanSpace.basisFun_apply, hkj]
      · funext q
        simp [E, v, EuclideanSpace.basisFun_apply, hkj]
    have hzero : HasDerivAt (fun _t : ℝ => frobIP M
        (batchGrad D (fun b => phys C (E k x b)))) 0 0 := hasDerivAt_const _ _
    have hzero' : HasDerivAt (F ∘ fun t : ℝ => x + t • v) 0 0 := by
      rw [show (F ∘ fun t : ℝ => x + t • v) = fun _ => frobIP M
          (batchGrad D (fun b => phys C (E k x b))) by
        funext t
        change frobIP M (batchGrad D (fun b => phys C (E k (x + t • v) b))) = _
        rw [congrFun hpath t]]
      exact hzero
    have heq := hglobal.unique hzero'
    rw [if_neg hkj]
    exact heq

private lemma projection_weighted_filter_fderiv_left {κ : Type*} [Fintype κ]
    [DecidableEq κ] {m n B d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (e : ((κ × Fin B) × (Fin m ⊕ Fin n)) ≃ Fin d)
    (C : Covariances m n) (D T M : Mat m n) (hB : 0 < B)
    (w : κ → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hrepr : ∀ R : Mat m n, frobIP T (dirDeriv ℓ
      (∑ k : κ, w k • batchGrad D (fun a => phys C
        ((fun i => x (e ((k, a), Sum.inl i))),
          (fun i => x (e ((k, a), Sum.inr i)))))) R) =
        frobIP M R)
    (j : κ) (a : Fin B) (i : Fin m) :
    let E := fun k (y : EuclideanSpace ℝ (Fin d)) (b : Fin B) =>
      ((fun q => y (e ((k, b), Sum.inl q)), fun q => y (e ((k, b), Sum.inr q))) :
        Vec m × Vec n)
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => frobIP T
      (Q ℓ (∑ k : κ, w k • batchGrad D (fun b => phys C (E k y b))))) x
      (EuclideanSpace.basisFun (Fin d) ℝ (e ((j, a), Sum.inl i))) =
      w j * (B : ℝ)⁻¹ *
        ((Arot C D *ᵥ (E j x a).2) i * resid (Arot C M) (E j x a) +
          resid (Arot C D) (E j x a) * (Arot C M *ᵥ (E j x a).2) i) := by
  dsimp only
  classical
  let E := fun k (y : EuclideanSpace ℝ (Fin d)) (b : Fin B) =>
    ((fun q => y (e ((k, b), Sum.inl q)), fun q => y (e ((k, b), Sum.inr q))) :
      Vec m × Vec n)
  let G := fun k (y : EuclideanSpace ℝ (Fin d)) =>
    fun r s => batchGrad D (fun b => phys C (E k y b)) r s
  let v := EuclideanSpace.basisFun (Fin d) ℝ (e ((j, a), Sum.inl i))
  have hG (k : κ) : DifferentiableAt ℝ (G k) x :=
    (projection_batch_contDiff C D).differentiable (by simp) (E k x) |>.comp x (by fun_prop)
  have hchain := projection_finite_chain_rule hℓ Finset.univ w G T x v
    (fun k _ => hG k)
  change (fderiv ℝ (fun y => frobIP T
    (Q ℓ (Matrix.of (∑ k : κ, w k • G k y)))) x) v = _
  rw [hchain]
  have hbase : Matrix.of (∑ k : κ, w k • G k x) =
      ∑ k : κ, w k • batchGrad D (fun a => phys C (E k x a)) := by rfl
  rw [hbase, hrepr]
  have hscalar (k : κ) : frobIP M (Matrix.of (fderiv ℝ (G k) x v)) =
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => frobIP M
        (batchGrad D (fun b => phys C (E k y b)))) x v := by
    symm
    exact projection_frobIP_fderiv M (G k) x v (hG k)
  change frobIP M (Matrix.of (∑ k, w k • fderiv ℝ (G k) x v)) = _
  have hsum : frobIP M (Matrix.of (∑ k, w k • fderiv ℝ (G k) x v)) =
      ∑ k, w k * frobIP M (Matrix.of (fderiv ℝ (G k) x v)) := by
    simp only [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    calc
      (∑ r : Fin m, ∑ s : Fin n, ∑ k : κ,
          M r s * (w k * (fderiv ℝ (G k) x v) r s)) =
          ∑ r : Fin m, ∑ k : κ, ∑ s : Fin n,
          M r s * (w k * (fderiv ℝ (G k) x v) r s) := by
        apply Finset.sum_congr rfl
        intro r _
        exact Finset.sum_comm
      _ = ∑ k : κ, ∑ r : Fin m, ∑ s : Fin n,
          M r s * (w k * (fderiv ℝ (G k) x v) r s) := Finset.sum_comm
      _ = _ := by simp only [mul_assoc, mul_left_comm, mul_comm]
  rw [hsum]
  simp_rw [hscalar]
  dsimp only [E, v]
  simp_rw [projection_encoded_batch_fderiv_left e C D M hB x]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true]
    ring
  · intro k _ hkj
    simp [hkj]
  · simp

private lemma projection_weighted_filter_fderiv_right {κ : Type*} [Fintype κ]
    [DecidableEq κ] {m n B d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (e : ((κ × Fin B) × (Fin m ⊕ Fin n)) ≃ Fin d)
    (C : Covariances m n) (D T M : Mat m n) (hB : 0 < B)
    (w : κ → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hrepr : ∀ R : Mat m n, frobIP T (dirDeriv ℓ
      (∑ k : κ, w k • batchGrad D (fun a => phys C
        ((fun i => x (e ((k, a), Sum.inl i))),
          (fun i => x (e ((k, a), Sum.inr i)))))) R) =
        frobIP M R)
    (j : κ) (a : Fin B) (i : Fin n) :
    let E := fun k (y : EuclideanSpace ℝ (Fin d)) (b : Fin B) =>
      ((fun q => y (e ((k, b), Sum.inl q)), fun q => y (e ((k, b), Sum.inr q))) :
        Vec m × Vec n)
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => frobIP T
      (Q ℓ (∑ k : κ, w k • batchGrad D (fun b => phys C (E k y b))))) x
      (EuclideanSpace.basisFun (Fin d) ℝ (e ((j, a), Sum.inr i))) =
      w j * (B : ℝ)⁻¹ *
        (((Arot C D)ᵀ *ᵥ (E j x a).1) i * resid (Arot C M) (E j x a) +
          resid (Arot C D) (E j x a) * ((Arot C M)ᵀ *ᵥ (E j x a).1) i) := by
  dsimp only
  classical
  let E := fun k (y : EuclideanSpace ℝ (Fin d)) (b : Fin B) =>
    ((fun q => y (e ((k, b), Sum.inl q)), fun q => y (e ((k, b), Sum.inr q))) :
      Vec m × Vec n)
  let G := fun k (y : EuclideanSpace ℝ (Fin d)) =>
    fun r s => batchGrad D (fun b => phys C (E k y b)) r s
  let v := EuclideanSpace.basisFun (Fin d) ℝ (e ((j, a), Sum.inr i))
  have hG (k : κ) : DifferentiableAt ℝ (G k) x :=
    (projection_batch_contDiff C D).differentiable (by simp) (E k x) |>.comp x (by fun_prop)
  have hchain := projection_finite_chain_rule hℓ Finset.univ w G T x v
    (fun k _ => hG k)
  change (fderiv ℝ (fun y => frobIP T
    (Q ℓ (Matrix.of (∑ k : κ, w k • G k y)))) x) v = _
  rw [hchain]
  have hbase : Matrix.of (∑ k : κ, w k • G k x) =
      ∑ k : κ, w k • batchGrad D (fun a => phys C (E k x a)) := by rfl
  rw [hbase, hrepr]
  have hscalar (k : κ) : frobIP M (Matrix.of (fderiv ℝ (G k) x v)) =
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => frobIP M
        (batchGrad D (fun b => phys C (E k y b)))) x v := by
    symm
    exact projection_frobIP_fderiv M (G k) x v (hG k)
  change frobIP M (Matrix.of (∑ k, w k • fderiv ℝ (G k) x v)) = _
  have hsum : frobIP M (Matrix.of (∑ k, w k • fderiv ℝ (G k) x v)) =
      ∑ k, w k * frobIP M (Matrix.of (fderiv ℝ (G k) x v)) := by
    simp only [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    calc
      (∑ r : Fin m, ∑ s : Fin n, ∑ k : κ,
          M r s * (w k * (fderiv ℝ (G k) x v) r s)) =
          ∑ r : Fin m, ∑ k : κ, ∑ s : Fin n,
          M r s * (w k * (fderiv ℝ (G k) x v) r s) := by
        apply Finset.sum_congr rfl
        intro r _
        exact Finset.sum_comm
      _ = ∑ k : κ, ∑ r : Fin m, ∑ s : Fin n,
          M r s * (w k * (fderiv ℝ (G k) x v) r s) := Finset.sum_comm
      _ = _ := by simp only [mul_assoc, mul_left_comm, mul_comm]
  rw [hsum]
  simp_rw [hscalar]
  dsimp only [E, v]
  simp_rw [projection_encoded_batch_fderiv_right e C D M hB x]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true]
    ring
  · intro k _ hkj
    simp [hkj]
  · simp

/-
private lemma projection_weighted_filter_gradient_energy_le {κ : Type*} [Fintype κ]
    [DecidableEq κ] {m n B d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (e : ((κ × Fin B) × (Fin m ⊕ Fin n)) ≃ Fin d)
    (C : Covariances m n) (D T M : Mat m n) (hB : 0 < B)
    (w : κ → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hrepr : ∀ R : Mat m n, frobIP T (dirDeriv ℓ
      (∑ k : κ, w k • batchGrad D (fun a => phys C
        ((fun i => x (e ((k, a), Sum.inl i))),
          (fun i => x (e ((k, a), Sum.inr i)))))) R) =
        frobIP M R) :
    let E := fun k (b : Fin B) =>
      ((fun q => x (e ((k, b), Sum.inl q)), fun q => x (e ((k, b), Sum.inr q))) :
        Vec m × Vec n)
    let Z : κ → Mat m B := fun k i a => (E k a).1 i
    let W : κ → Mat n B := fun k j a => (E k a).2 j
    let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
    let U := fun k => Real.sqrt
      (Finset.univ.sup' hne (fun a => ∑ i, (Arot C D * W k) i a ^ 2))
    let V := fun k => Real.sqrt
      (Finset.univ.sup' hne (fun a => ∑ j, ((Arot C D)ᵀ * Z k) j a ^ 2))
    let R := fun k => Finset.univ.sup' hne (fun a => |resid (Arot C D) (E k a)|)
    ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => frobIP T
      (Q ℓ (∑ k : κ, w k • batchGrad D (fun b => phys C
        (fun q => y (e ((k, b), Sum.inl q)), fun q => y (e ((k, b), Sum.inr q))))))) x‖ ^ 2 ≤
      ∑ k : κ, w k ^ 2 * (2 * (B : ℝ)⁻¹ ^ 2 * fro (Arot C M) ^ 2 *
        (U k ^ 2 * opNorm (W k) ^ 2 * opNorm (Z k) ^ 2 +
          V k ^ 2 * opNorm (Z k) ^ 2 * opNorm (W k) ^ 2 +
          R k ^ 2 * (opNorm (W k) ^ 2 + opNorm (Z k) ^ 2))) := by
  dsimp only
  classical
  let E := fun k (b : Fin B) =>
    ((fun q => x (e ((k, b), Sum.inl q)), fun q => x (e ((k, b), Sum.inr q))) :
      Vec m × Vec n)
  let Z : κ → Mat m B := fun k i a => (E k a).1 i
  let W : κ → Mat n B := fun k j a => (E k a).2 j
  let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
  let U := fun k => Real.sqrt
    (Finset.univ.sup' hne (fun a => ∑ i, (Arot C D * W k) i a ^ 2))
  let V := fun k => Real.sqrt
    (Finset.univ.sup' hne (fun a => ∑ j, ((Arot C D)ᵀ * Z k) j a ^ 2))
  let R := fun k => Finset.univ.sup' hne (fun a => |resid (Arot C D) (E k a)|)
  let F : EuclideanSpace ℝ (Fin d) → ℝ := fun y => frobIP T
    (Q ℓ (∑ k : κ, w k • batchGrad D (fun b => phys C
      (fun q => y (e ((k, b), Sum.inl q)), fun q => y (e ((k, b), Sum.inr q))))))
  rw [projection_gradient_energy_coordinates F x, ← e.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  apply Finset.sum_le_sum
  intro k _
  have hu0 : 0 ≤ U k ^ 2 := sq_nonneg _
  have hv0 : 0 ≤ V k ^ 2 := sq_nonneg _
  have hr0 : 0 ≤ R k ^ 2 := sq_nonneg _
  have hZ0 : 0 ≤ opNorm (Z k) ^ 2 := sq_nonneg _
  have hW0 : 0 ≤ opNorm (W k) ^ 2 := sq_nonneg _
  have hUsq : U k ^ 2 = Finset.univ.sup' hne
      (fun a => ∑ i, (Arot C D * W k) i a ^ 2) := by
    dsimp only [U]
    rw [Real.sq_sqrt]
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' hne
      (fun a => ∑ i, (Arot C D * W k) i a ^ 2)
    rw [ha]
    positivity
  have hVsq : V k ^ 2 = Finset.univ.sup' hne
      (fun a => ∑ j, ((Arot C D)ᵀ * Z k) j a ^ 2) := by
    dsimp only [V]
    rw [Real.sq_sqrt]
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' hne
      (fun a => ∑ j, ((Arot C D)ᵀ * Z k) j a ^ 2)
    rw [ha]
    positivity
  have hb := projection_batch_gradient_energy_le (Arot C D) (Arot C M) (Z k) (W k)
    (U k ^ 2) (V k ^ 2) (opNorm (Z k) ^ 2) (opNorm (W k) ^ 2) (R k ^ 2)
    hu0 hv0 hZ0 hW0 hr0
    (fun a => by rw [hUsq]; exact Finset.le_sup' _ (Finset.mem_univ a))
    (fun a => by
      rw [hVsq]
      exact Finset.le_sup'
        (fun b : Fin B => ∑ j, ((Arot C D)ᵀ * Z k) j b ^ 2) (Finset.mem_univ a))
    (fun a => projection_column_sq_le_opNorm_sq (Z k) a)
    (fun a => projection_column_sq_le_opNorm_sq (W k) a)
    (fun a => by
      have hmax := Finset.le_sup' (fun b => |resid (Arot C D) (E k b)|)
        (Finset.mem_univ a)
      have hR0 : 0 ≤ R k := (abs_nonneg _).trans hmax
      change resid (Arot C D) (E k a) ^ 2 ≤ R k ^ 2
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hR0).mpr hmax)
  dsimp only [F]
  simp_rw [projection_weighted_filter_fderiv_left hℓ e C D T M hB w x hrepr
    (j := k)]
  simp_rw [projection_weighted_filter_fderiv_right hℓ e C D T M hB w x hrepr
    (j := k)]
  calc
    (∑ a, ∑ i,
        (w k * (B : ℝ)⁻¹ * ((Arot C D * W k) i a * resid (Arot C M) (E k a) +
          resid (Arot C D) (E k a) * (Arot C M * W k) i a)) ^ 2) +
      ∑ a, ∑ j,
        (w k * (B : ℝ)⁻¹ * (((Arot C D)ᵀ * Z k) j a * resid (Arot C M) (E k a) +
          resid (Arot C D) (E k a) * ((Arot C M)ᵀ * Z k) j a)) ^ 2 =
        (w k * (B : ℝ)⁻¹) ^ 2 *
          ((∑ a, ∑ i, ((Arot C D * W k) i a * resid (Arot C M) (E k a) +
            resid (Arot C D) (E k a) * (Arot C M * W k) i a) ^ 2) +
           (∑ a, ∑ j, (((Arot C D)ᵀ * Z k) j a * resid (Arot C M) (E k a) +
            resid (Arot C D) (E k a) * ((Arot C M)ᵀ * Z k) j a) ^ 2)) := by
          simp only [mul_add, Finset.mul_sum]
          apply congrArg₂ (· + ·)
          · apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro i _
            ring
          · apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ ≤ (w k * (B : ℝ)⁻¹) ^ 2 * (2 * fro (Arot C M) ^ 2 *
        (U k ^ 2 * opNorm (W k) ^ 2 * opNorm (Z k) ^ 2 +
          V k ^ 2 * opNorm (Z k) ^ 2 * opNorm (W k) ^ 2 +
          R k ^ 2 * (opNorm (W k) ^ 2 + opNorm (Z k) ^ 2))) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring
-/

private lemma projection_sum_sq_mulVec_le {m n : ℕ} (M : Mat m n) (x : Vec n) :
    ∑ i, (M *ᵥ x) i ^ 2 ≤ opNorm M ^ 2 * ∑ i, x i ^ 2 := by
  have hb : ‖Matrix.toEuclideanLin M (WithLp.toLp 2 x)‖ ≤
      opNorm M * ‖WithLp.toLp 2 x‖ :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)).le_opNorm _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at hsq
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Real.norm_eq_abs, sq_abs] using hsq

private lemma projection_fro_mul_sq_le_left {m n k : ℕ} (M : Mat m n) (N : Mat n k) :
    fro (M * N) ^ 2 ≤ opNorm M ^ 2 * fro N ^ 2 := by
  rw [projection_fro_sq, projection_fro_sq, Finset.sum_comm, Finset.mul_sum]
  calc
    ∑ j, ∑ i, (M * N) i j ^ 2 ≤
        ∑ j : Fin k, opNorm M ^ 2 * ∑ l, N l j ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact projection_sum_sq_mulVec_le M (fun l => N l j)
    _ = ∑ i, opNorm M ^ 2 * ∑ j, N i j ^ 2 := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm

private lemma projection_fro_mul_sq_le_right {m n k : ℕ} (M : Mat m n) (N : Mat n k) :
    fro (M * N) ^ 2 ≤ fro M ^ 2 * opNorm N ^ 2 := by
  have h := projection_fro_mul_sq_le_left Nᵀ Mᵀ
  rw [← Matrix.transpose_mul, projection_fro_transpose, projection_fro_transpose,
    projection_opNorm_transpose] at h
  exact h.trans_eq (mul_comm _ _)

private lemma projection_batch_test_sq_sum_le {m n B : ℕ}
    (M : Mat m n) (Z : Mat m B) (W : Mat n B) (cW : ℝ) (hcW : 0 ≤ cW)
    (hW : ∀ a, ∑ j, W j a ^ 2 ≤ cW) :
    ∑ a : Fin B, resid M (fun i => Z i a, fun j => W j a) ^ 2 ≤
      cW * fro M ^ 2 * opNorm Z ^ 2 := by
  have hpoint (a : Fin B) :
      resid M (fun i => Z i a, fun j => W j a) ^ 2 ≤
        cW * ∑ j, (Mᵀ * Z) j a ^ 2 := by
    have heq : resid M (fun i => Z i a, fun j => W j a) =
        ∑ j, (Mᵀ * Z) j a * W j a := by
      simp only [resid, Matrix.mulVec, dotProduct, Matrix.mul_apply,
        Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq]
    exact (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans
      (by simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hW a) (Finset.sum_nonneg fun j _ => sq_nonneg ((Mᵀ * Z) j a)))
  calc
    ∑ a : Fin B, resid M (fun i => Z i a, fun j => W j a) ^ 2 ≤
        ∑ a : Fin B, cW * ∑ j, (Mᵀ * Z) j a ^ 2 := Finset.sum_le_sum fun a _ => hpoint a
    _ = cW * fro (Mᵀ * Z) ^ 2 := by
      rw [projection_fro_sq]
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ cW * (fro Mᵀ ^ 2 * opNorm Z ^ 2) :=
      mul_le_mul_of_nonneg_left (projection_fro_mul_sq_le_right _ _) hcW
    _ = _ := by rw [projection_fro_transpose]; ring

private lemma projection_batch_gradient_one_side {m n B : ℕ}
    (A M : Mat m n) (Z : Mat m B) (W : Mat n B) (u cW cD : ℝ)
    (hu : 0 ≤ u) (hcW : 0 ≤ cW) (hcD : 0 ≤ cD)
    (hAW : ∀ a, ∑ i, (A * W) i a ^ 2 ≤ u)
    (hW : ∀ a, ∑ j, W j a ^ 2 ≤ cW)
    (hD : ∀ a, resid A (fun i => Z i a, fun j => W j a) ^ 2 ≤ cD) :
    ∑ a : Fin B, ∑ i : Fin m,
      ((A * W) i a * resid M (fun i => Z i a, fun j => W j a) +
        resid A (fun i => Z i a, fun j => W j a) * (M * W) i a) ^ 2 ≤
      2 * fro M ^ 2 * (u * cW * opNorm Z ^ 2 + cD * opNorm W ^ 2) := by
  let q := fun a => resid M (fun i => Z i a, fun j => W j a)
  let d := fun a => resid A (fun i => Z i a, fun j => W j a)
  have hpoint (a : Fin B) :
      (∑ i : Fin m, ((A * W) i a * q a + d a * (M * W) i a) ^ 2) ≤
        2 * (u * q a ^ 2 + cD * ∑ i, (M * W) i a ^ 2) := by
    calc
      _ ≤ ∑ i : Fin m, 2 * ((A * W) i a ^ 2 * q a ^ 2 +
          d a ^ 2 * (M * W) i a ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [sq_nonneg ((A * W) i a * q a - d a * (M * W) i a)]
      _ = 2 * ((∑ i, (A * W) i a ^ 2) * q a ^ 2 +
          d a ^ 2 * ∑ i, (M * W) i a ^ 2) := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_add, Finset.sum_add_distrib]
      _ ≤ _ := by
        gcongr
        · exact hAW a
        · exact hD a
  have hq := projection_batch_test_sq_sum_le M Z W cW hcW hW
  have hMW := projection_fro_mul_sq_le_right M W
  calc
    _ ≤ ∑ a : Fin B, 2 * (u * q a ^ 2 + cD * ∑ i, (M * W) i a ^ 2) :=
      Finset.sum_le_sum fun a _ => hpoint a
    _ = 2 * (u * (∑ a, q a ^ 2) + cD * fro (M * W) ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      congr 1
      congr 1
      rw [projection_fro_sq, Finset.sum_comm]
    _ ≤ 2 * (u * (cW * fro M ^ 2 * opNorm Z ^ 2) +
        cD * (fro M ^ 2 * opNorm W ^ 2)) := by
      gcongr
    _ = _ := by ring

private lemma projection_resid_transpose {m n : ℕ} (A : Mat m n) (z : Vec m) (w : Vec n) :
    resid Aᵀ (w, z) = resid A (z, w) := by
  simp only [resid, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma projection_batch_gradient_energy_le {m n B : ℕ}
    (A M : Mat m n) (Z : Mat m B) (W : Mat n B) (u v cZ cW cD : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hcZ : 0 ≤ cZ) (hcW : 0 ≤ cW) (hcD : 0 ≤ cD)
    (hAW : ∀ a, ∑ i, (A * W) i a ^ 2 ≤ u)
    (hAZ : ∀ a, ∑ j, (Aᵀ * Z) j a ^ 2 ≤ v)
    (hZ : ∀ a, ∑ i, Z i a ^ 2 ≤ cZ)
    (hW : ∀ a, ∑ j, W j a ^ 2 ≤ cW)
    (hD : ∀ a, resid A (fun i => Z i a, fun j => W j a) ^ 2 ≤ cD) :
    (∑ a : Fin B, ∑ i : Fin m,
      ((A * W) i a * resid M (fun i => Z i a, fun j => W j a) +
        resid A (fun i => Z i a, fun j => W j a) * (M * W) i a) ^ 2) +
      (∑ a : Fin B, ∑ j : Fin n,
        ((Aᵀ * Z) j a * resid M (fun i => Z i a, fun j => W j a) +
          resid A (fun i => Z i a, fun j => W j a) * (Mᵀ * Z) j a) ^ 2) ≤
      2 * fro M ^ 2 * (u * cW * opNorm Z ^ 2 + v * cZ * opNorm W ^ 2 +
        cD * (opNorm W ^ 2 + opNorm Z ^ 2)) := by
  have hleft := projection_batch_gradient_one_side A M Z W u cW cD hu hcW hcD hAW hW hD
  have hright := projection_batch_gradient_one_side Aᵀ Mᵀ W Z v cZ cD hv hcZ hcD hAZ hZ
    (fun a => by simpa only [projection_resid_transpose] using hD a)
  simp only [projection_resid_transpose, projection_fro_transpose] at hright
  exact (add_le_add hleft hright).trans_eq (by ring)

private lemma projection_canonical_iid_batch (m n B : ℕ) :
    IIDBatch (Measure.pi (fun _ : Fin B =>
      (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)))
      ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
      (fun a (z : Fin B → Vec m × Vec n) => z a) := by
  refine ⟨fun a => (measurable_pi_apply a).aemeasurable, fun a => ?_, ?_⟩
  · rw [Measure.pi_map_eval, Finset.prod_eq_one (fun _ _ => measure_univ), one_smul]
  · exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

private lemma projection_canonical_iid_matrix {m n B k : ℕ}
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

private lemma projection_canonical_iid_matrix_left (m n B : ℕ) :
    Muon.External.IsIIDGaussianMatrix
      (Measure.pi (fun _ : Fin B =>
        (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)))
      (fun (z : Fin B → Vec m × Vec n) (i : Fin m) (a : Fin B) => (z a).1 i) := by
  apply projection_canonical_iid_matrix (fun z : Vec m × Vec n => z.1) measurable_fst
  rw [Measure.map_fst_prod, measure_univ, one_smul]

private lemma projection_canonical_iid_matrix_right (m n B : ℕ) :
    Muon.External.IsIIDGaussianMatrix
      (Measure.pi (fun _ : Fin B =>
        (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)))
      (fun (z : Fin B → Vec m × Vec n) (j : Fin n) (a : Fin B) => (z a).2 j) := by
  apply projection_canonical_iid_matrix (fun z : Vec m × Vec n => z.2) measurable_snd
  rw [Measure.map_snd_prod, measure_univ, one_smul]

private lemma projection_gaussian_linear_map {m : ℕ} (v : Vec m) :
    (Muon.Foundations.stdGaussianPi m).map (fun z : Vec m => dotProduct z v) =
      (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (dotProduct v v) * x) := by
  have h := Muon.Foundations.stdGaussianPi_linear_map m v
  have e : (fun z : Vec m => dotProduct z v) = fun z => ∑ i, z i * v i := rfl
  rw [e, h, gaussianReal_map_const_mul]
  have hv : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hd : dotProduct v v = ∑ i, v i ^ 2 := by simp [dotProduct, sq]
  congr 1
  · simp
  · apply NNReal.eq
    simp only [NNReal.coe_mk, Real.coe_toNNReal _ hv, mul_one]
    rw [hd, Real.sq_sqrt hv]

private lemma projection_gaussian_linear_six {m : ℕ} (v : Vec m) :
    Integrable (fun z : Vec m => (dotProduct z v) ^ 6)
        (Muon.Foundations.stdGaussianPi m) ∧
      ∫ z, (dotProduct z v) ^ 6 ∂(Muon.Foundations.stdGaussianPi m) =
        15 * (∑ i, v i ^ 2) ^ 3 := by
  have hm : Measurable (fun z : Vec m => dotProduct z v) := by
    unfold dotProduct
    fun_prop
  set c := Real.sqrt (dotProduct v v) with hc
  have hmc : Measurable (fun x : ℝ => c * x) := by fun_prop
  have hc2 : c ^ 2 = dotProduct v v := Real.sq_sqrt (by
    rw [show dotProduct v v = ∑ i, v i ^ 2 by simp [dotProduct, sq]]
    positivity)
  have hL := projection_gaussian_linear_map v
  rw [← hc] at hL
  constructor
  · have h1 : Integrable (fun x : ℝ => x ^ 6)
        ((gaussianReal 0 1).map (fun x : ℝ => c * x)) := by
      rw [integrable_map_measure (by fun_prop) hmc.aemeasurable]
      have h := (Muon.Foundations.gaussian_integrable_pow 6).const_mul (c ^ 6)
      refine h.congr (Filter.Eventually.of_forall fun x => ?_)
      simp [mul_pow]
    rw [← hL, integrable_map_measure (by fun_prop) hm.aemeasurable] at h1
    exact h1
  · have h1 : ∫ x, x ^ 6 ∂((gaussianReal 0 1).map (fun x : ℝ => c * x)) =
        15 * (dotProduct v v) ^ 3 := by
      rw [integral_map hmc.aemeasurable (by fun_prop)]
      simp_rw [mul_pow]
      rw [integral_const_mul, Muon.Foundations.gaussian_moment_six, ← hc2]
      ring
    rw [← hL, integral_map hm.aemeasurable (by fun_prop)] at h1
    simpa [dotProduct, sq] using h1

private lemma projection_max_mulVec_eLpNorm_le_resid {m n B : ℕ} (hB : 0 < B)
    (A : Mat m n) :
    let μ := Measure.pi (fun _ : Fin B =>
      (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
    let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
    eLpNorm (fun z : Fin B → Vec m × Vec n => Real.sqrt
        (Finset.univ.sup' hne (fun a => ∑ i, (A *ᵥ (z a).2) i ^ 2))) 6 μ ≤
      eLpNorm (fun z : Fin B → Vec m × Vec n =>
        Finset.univ.sup' hne (fun a => |resid A (z a)|)) 6 μ := by
  dsimp only
  let μZ := Measure.pi (fun _ : Fin B => Muon.Foundations.stdGaussianPi m)
  let μW := Measure.pi (fun _ : Fin B => Muon.Foundations.stdGaussianPi n)
  let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
  let U : (Fin B → Vec n) → ℝ := fun w => Real.sqrt
    (Finset.univ.sup' hne (fun a => ∑ i, (A *ᵥ w a) i ^ 2))
  let R : (Fin B → Vec m) × (Fin B → Vec n) → ℝ := fun z =>
    Finset.univ.sup' hne (fun a => |resid A (z.1 a, z.2 a)|)
  have hU : Measurable U := by
    dsimp [U]
    fun_prop
  have hR : Measurable R := by
    dsimp [R, resid, Matrix.mulVec, dotProduct]
    fun_prop
  have hsep := measurePreserving_arrowProdEquivProdArrow (Vec m) (Vec n) (Fin B)
    (fun _ => Muon.Foundations.stdGaussianPi m)
    (fun _ => Muon.Foundations.stdGaussianPi n)
  have hleft : eLpNorm (fun z : Fin B → Vec m × Vec n => U (fun a => (z a).2)) 6
      (Measure.pi (fun _ : Fin B =>
        (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))) =
      eLpNorm (fun z : (Fin B → Vec m) × (Fin B → Vec n) => U z.2) 6 (μZ.prod μW) := by
    have hh := eLpNorm_comp_measurePreserving
      (p := (6 : ℝ≥0∞)) (hU.comp measurable_snd).aestronglyMeasurable hsep
    change eLpNorm (fun z : Fin B → Vec m × Vec n => U (fun a => (z a).2)) 6
        (Measure.pi (fun _ : Fin B =>
          (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))) =
      eLpNorm (fun z : (Fin B → Vec m) × (Fin B → Vec n) => U z.2) 6
        ((Measure.pi fun _ : Fin B => Muon.Foundations.stdGaussianPi m).prod
          (Measure.pi fun _ : Fin B => Muon.Foundations.stdGaussianPi n)) at hh
    simpa only [μZ, μW] using hh
  have hright : eLpNorm (fun z : Fin B → Vec m × Vec n =>
      Finset.univ.sup' hne (fun a => |resid A (z a)|)) 6
      (Measure.pi (fun _ : Fin B =>
        (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))) =
      eLpNorm R 6 (μZ.prod μW) := by
    have hh := eLpNorm_comp_measurePreserving (p := (6 : ℝ≥0∞)) hR.aestronglyMeasurable hsep
    change eLpNorm (fun z : Fin B → Vec m × Vec n =>
        Finset.univ.sup' hne (fun a => |resid A (z a)|)) 6
        (Measure.pi (fun _ : Fin B =>
          (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))) =
      eLpNorm R 6 ((Measure.pi fun _ : Fin B => Muon.Foundations.stdGaussianPi m).prod
        (Measure.pi fun _ : Fin B => Muon.Foundations.stdGaussianPi n)) at hh
    simpa only [μZ, μW] using hh
  rw [show (fun z : Fin B → Vec m × Vec n => Real.sqrt
      (Finset.univ.sup' hne (fun a => ∑ i, (A *ᵥ (z a).2) i ^ 2))) =
      (fun z => U (fun a => (z a).2)) by rfl, hleft, hright]
  have hUs : AEStronglyMeasurable
      (fun z : (Fin B → Vec m) × (Fin B → Vec n) => U z.2) (μZ.prod μW) :=
    (hU.comp measurable_snd).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hUs,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hR.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  apply ENNReal.rpow_le_rpow
  · rw [lintegral_prod_symm
        (fun x : (Fin B → Vec m) × (Fin B → Vec n) => ‖U x.2‖ₑ ^ (6 : ℝ))
        (by fun_prop),
      lintegral_prod_symm
        (fun x : (Fin B → Vec m) × (Fin B → Vec n) => ‖R x‖ₑ ^ (6 : ℝ))
        (by fun_prop)]
    apply lintegral_mono
    intro w
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' hne
      (fun a => ∑ i, (A *ᵥ w a) i ^ 2)
    have hmax0 : 0 ≤ Finset.univ.sup' hne (fun a => ∑ i, (A *ᵥ w a) i ^ 2) := by
      rw [ha]
      positivity
    have hinner : ∫⁻ z : Fin B → Vec m,
        ‖dotProduct (z a) (A *ᵥ w a)‖ₑ ^ (6 : ℝ) ∂μZ ≤
        ∫⁻ z : Fin B → Vec m, ‖R (z, w)‖ₑ ^ (6 : ℝ) ∂μZ := by
      apply lintegral_mono
      intro z
      have hle := Finset.le_sup' (fun b => |resid A (z b, w b)|) (Finset.mem_univ a)
      have hR0 : 0 ≤ R (z, w) := (abs_nonneg _).trans hle
      have hle' : |dotProduct (z a) (A *ᵥ w a)| ≤ R (z, w) := by
        simpa only [R, resid] using hle
      apply ENNReal.rpow_le_rpow
      · rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_nonneg hR0]
        exact ENNReal.ofReal_le_ofReal hle'
      · norm_num
    have heval : MeasurePreserving (fun z : Fin B → Vec m => z a) μZ
        (Muon.Foundations.stdGaussianPi m) := by
      refine ⟨measurable_pi_apply a, ?_⟩
      dsimp [μZ]
      rw [Measure.pi_map_eval, Finset.prod_eq_one (fun _ _ => measure_univ), one_smul]
    have hlin := projection_gaussian_linear_six (A *ᵥ w a)
    have hlin' : ∫⁻ z : Vec m, ‖dotProduct z (A *ᵥ w a)‖ₑ ^ (6 : ℝ)
        ∂(Muon.Foundations.stdGaussianPi m) =
        ENNReal.ofReal (15 * (∑ i, (A *ᵥ w a) i ^ 2) ^ 3) := by
      have heq : (fun z : Vec m => ‖dotProduct z (A *ᵥ w a)‖ₑ ^ (6 : ℝ)) =
          (fun z : Vec m => ENNReal.ofReal ((dotProduct z (A *ᵥ w a)) ^ 6)) := by
        funext z
        rw [Real.enorm_eq_ofReal_abs]
        change ENNReal.ofReal |dotProduct z (A *ᵥ w a)| ^ ((6 : ℕ) : ℝ) = _
        rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (abs_nonneg _) 6]
        congr 1
        simpa using (even_two_mul 3).pow_abs (dotProduct z (A *ᵥ w a))
      rw [heq, ← ofReal_integral_eq_lintegral_ofReal hlin.1
        (Filter.Eventually.of_forall fun z => by positivity), hlin.2]
    have hlinmeas : Measurable
        (fun z : Vec m => ‖dotProduct z (A *ᵥ w a)‖ₑ ^ (6 : ℝ)) := by
      unfold dotProduct
      fun_prop
    have hevaleq := heval.lintegral_comp
      (f := fun z : Vec m => ‖dotProduct z (A *ᵥ w a)‖ₑ ^ (6 : ℝ)) hlinmeas
    change (∫⁻ z : Fin B → Vec m,
      ‖dotProduct (z a) (A *ᵥ w a)‖ₑ ^ (6 : ℝ) ∂μZ) =
        ∫⁻ z : Vec m, ‖dotProduct z (A *ᵥ w a)‖ₑ ^ (6 : ℝ)
          ∂(Muon.Foundations.stdGaussianPi m) at hevaleq
    rw [hevaleq, hlin'] at hinner
    have hconst : ∫⁻ _z : Fin B → Vec m, ‖U w‖ₑ ^ (6 : ℝ) ∂μZ =
        ENNReal.ofReal ((Finset.univ.sup' hne
          (fun a => ∑ i, (A *ᵥ w a) i ^ 2)) ^ 3) := by
      rw [lintegral_const, measure_univ, mul_one]
      dsimp [U]
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      change ENNReal.ofReal (Real.sqrt (Finset.univ.sup' hne
        (fun a => ∑ i, (A *ᵥ w a) i ^ 2))) ^ ((6 : ℕ) : ℝ) = _
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 6]
      congr 1
      calc
        Real.sqrt (Finset.univ.sup' hne
            (fun a => ∑ i, (A *ᵥ w a) i ^ 2)) ^ 6 =
            (Real.sqrt (Finset.univ.sup' hne
              (fun a => ∑ i, (A *ᵥ w a) i ^ 2)) ^ 2) ^ 3 := by ring
        _ = _ := by rw [Real.sq_sqrt hmax0]
    change (∫⁻ _z : Fin B → Vec m, ‖U w‖ₑ ^ (6 : ℝ) ∂μZ) ≤
      ∫⁻ z : Fin B → Vec m, ‖R (z, w)‖ₑ ^ (6 : ℝ) ∂μZ
    rw [hconst]
    calc
      ENNReal.ofReal ((Finset.univ.sup' hne
          (fun a => ∑ i, (A *ᵥ w a) i ^ 2)) ^ 3) ≤
          ENNReal.ofReal (15 * (∑ i, (A *ᵥ w a) i ^ 2) ^ 3) := by
        rw [ha]
        have hp3 : 0 ≤ (∑ i, (A *ᵥ w a) i ^ 2) ^ 3 := pow_nonneg (by positivity) 3
        exact ENNReal.ofReal_le_ofReal (by nlinarith)
      _ ≤ _ := hinner
  · positivity

private lemma projection_max_transpose_mulVec_eLpNorm_le_resid {m n B : ℕ}
    (hB : 0 < B) (A : Mat m n) :
    let μ := Measure.pi (fun _ : Fin B =>
      (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
    let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
    eLpNorm (fun z : Fin B → Vec m × Vec n => Real.sqrt
        (Finset.univ.sup' hne (fun a => ∑ j, (Aᵀ *ᵥ (z a).1) j ^ 2))) 6 μ ≤
      eLpNorm (fun z : Fin B → Vec m × Vec n =>
        Finset.univ.sup' hne (fun a => |resid A (z a)|)) 6 μ := by
  dsimp only
  let μmn := Measure.pi (fun _ : Fin B =>
    (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
  let μnm := Measure.pi (fun _ : Fin B =>
    (Muon.Foundations.stdGaussianPi n).prod (Muon.Foundations.stdGaussianPi m))
  let sw : (Fin B → Vec m × Vec n) → (Fin B → Vec n × Vec m) :=
    fun z a => (z a).swap
  have hsw : MeasurePreserving sw μmn μnm := by
    have h := measurePreserving_pi
      (fun _ : Fin B => (Muon.Foundations.stdGaussianPi m).prod
        (Muon.Foundations.stdGaussianPi n))
      (fun _ : Fin B => (Muon.Foundations.stdGaussianPi n).prod
        (Muon.Foundations.stdGaussianPi m))
      (fun _ => (Measure.measurePreserving_swap
        (μ := Muon.Foundations.stdGaussianPi m)
        (ν := Muon.Foundations.stdGaussianPi n)))
    simpa only [sw, μmn, μnm, Function.comp_apply, Prod.swap_prod_mk] using h
  let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
  have hbase := projection_max_mulVec_eLpNorm_le_resid hB Aᵀ
  dsimp only at hbase
  have hLmeas : AEStronglyMeasurable (fun z : Fin B → Vec n × Vec m => Real.sqrt
      (Finset.univ.sup' hne (fun a => ∑ j, (Aᵀ *ᵥ (z a).2) j ^ 2))) μnm := by
    apply Measurable.aestronglyMeasurable
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hRmeas : AEStronglyMeasurable (fun z : Fin B → Vec n × Vec m =>
      Finset.univ.sup' hne (fun a => |resid Aᵀ (z a)|)) μnm := by
    apply Measurable.aestronglyMeasurable
    unfold resid Matrix.mulVec dotProduct
    fun_prop
  have hLmap := eLpNorm_comp_measurePreserving (p := (6 : ℝ≥0∞)) hLmeas hsw
  have hRmap := eLpNorm_comp_measurePreserving (p := (6 : ℝ≥0∞)) hRmeas hsw
  change eLpNorm (fun z : Fin B → Vec m × Vec n => Real.sqrt
      (Finset.univ.sup' hne (fun a => ∑ j, (Aᵀ *ᵥ (z a).1) j ^ 2))) 6 μmn = _ at hLmap
  change eLpNorm (fun z : Fin B → Vec m × Vec n =>
      Finset.univ.sup' hne (fun a => |resid Aᵀ ((z a).2, (z a).1)|)) 6 μmn = _ at hRmap
  have hRmap' : eLpNorm (fun z : Fin B → Vec m × Vec n =>
      Finset.univ.sup' hne (fun a => |resid A (z a)|)) 6 μmn =
      eLpNorm (fun z : Fin B → Vec n × Vec m =>
        Finset.univ.sup' hne (fun a => |resid Aᵀ (z a)|)) 6 μnm := by
    simpa only [projection_resid_transpose] using hRmap
  rw [hLmap, hRmap']
  exact hbase

private lemma projection_column_sq_le_opNorm_sq {m B : ℕ} (Z : Mat m B) (a : Fin B) :
    ∑ i, Z i a ^ 2 ≤ opNorm Z ^ 2 := by
  let e : Vec B := fun b => if b = a then 1 else 0
  have he : ∑ b, e b ^ 2 = 1 := by
    simp [e]
  have h := projection_sum_sq_mulVec_le Z e
  rw [he, mul_one] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp [Matrix.mulVec, dotProduct, e]

private lemma projection_weighted_filter_gradient_energy_le {κ : Type*} [Fintype κ]
    [DecidableEq κ] {m n B d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (e : ((κ × Fin B) × (Fin m ⊕ Fin n)) ≃ Fin d)
    (C : Covariances m n) (D T M : Mat m n) (hB : 0 < B)
    (w : κ → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hrepr : ∀ R : Mat m n, frobIP T (dirDeriv ℓ
      (∑ k : κ, w k • batchGrad D (fun a => phys C
        ((fun i => x (e ((k, a), Sum.inl i))),
          (fun i => x (e ((k, a), Sum.inr i)))))) R) =
        frobIP M R) :
    let E := fun k (b : Fin B) =>
      ((fun q => x (e ((k, b), Sum.inl q)), fun q => x (e ((k, b), Sum.inr q))) :
        Vec m × Vec n)
    let Z : κ → Mat m B := fun k i a => (E k a).1 i
    let W : κ → Mat n B := fun k j a => (E k a).2 j
    let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
    let U := fun k => Real.sqrt
      (Finset.univ.sup' hne (fun a => ∑ i, (Arot C D * W k) i a ^ 2))
    let V := fun k => Real.sqrt
      (Finset.univ.sup' hne (fun a => ∑ j, ((Arot C D)ᵀ * Z k) j a ^ 2))
    let R := fun k => Finset.univ.sup' hne (fun a => |resid (Arot C D) (E k a)|)
    ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => frobIP T
      (Q ℓ (∑ k : κ, w k • batchGrad D (fun b => phys C
        (fun q => y (e ((k, b), Sum.inl q)), fun q => y (e ((k, b), Sum.inr q))))))) x‖ ^ 2 ≤
      ∑ k : κ, w k ^ 2 * (2 * (B : ℝ)⁻¹ ^ 2 * fro (Arot C M) ^ 2 *
        (U k ^ 2 * opNorm (W k) ^ 2 * opNorm (Z k) ^ 2 +
          V k ^ 2 * opNorm (Z k) ^ 2 * opNorm (W k) ^ 2 +
          R k ^ 2 * (opNorm (W k) ^ 2 + opNorm (Z k) ^ 2))) := by
  dsimp only
  classical
  let E := fun k (b : Fin B) =>
    ((fun q => x (e ((k, b), Sum.inl q)), fun q => x (e ((k, b), Sum.inr q))) :
      Vec m × Vec n)
  let Z : κ → Mat m B := fun k i a => (E k a).1 i
  let W : κ → Mat n B := fun k j a => (E k a).2 j
  let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
  let U := fun k => Real.sqrt
    (Finset.univ.sup' hne (fun a => ∑ i, (Arot C D * W k) i a ^ 2))
  let V := fun k => Real.sqrt
    (Finset.univ.sup' hne (fun a => ∑ j, ((Arot C D)ᵀ * Z k) j a ^ 2))
  let R := fun k => Finset.univ.sup' hne (fun a => |resid (Arot C D) (E k a)|)
  let F : EuclideanSpace ℝ (Fin d) → ℝ := fun y => frobIP T
    (Q ℓ (∑ k : κ, w k • batchGrad D (fun b => phys C
      (fun q => y (e ((k, b), Sum.inl q)), fun q => y (e ((k, b), Sum.inr q))))))
  rw [projection_gradient_energy_coordinates F x, ← e.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  apply Finset.sum_le_sum
  intro k _
  rw [Finset.sum_add_distrib]
  have hu0 : 0 ≤ U k ^ 2 := sq_nonneg _
  have hv0 : 0 ≤ V k ^ 2 := sq_nonneg _
  have hr0 : 0 ≤ R k ^ 2 := sq_nonneg _
  have hZ0 : 0 ≤ opNorm (Z k) ^ 2 := sq_nonneg _
  have hW0 : 0 ≤ opNorm (W k) ^ 2 := sq_nonneg _
  have hUsq : U k ^ 2 = Finset.univ.sup' hne
      (fun a => ∑ i, (Arot C D * W k) i a ^ 2) := by
    dsimp only [U]
    rw [Real.sq_sqrt]
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' hne
      (fun a => ∑ i, (Arot C D * W k) i a ^ 2)
    rw [ha]
    positivity
  have hVsq : V k ^ 2 = Finset.univ.sup' hne
      (fun a => ∑ j, ((Arot C D)ᵀ * Z k) j a ^ 2) := by
    dsimp only [V]
    rw [Real.sq_sqrt]
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' hne
      (fun a => ∑ j, ((Arot C D)ᵀ * Z k) j a ^ 2)
    rw [ha]
    positivity
  have hb := projection_batch_gradient_energy_le (Arot C D) (Arot C M) (Z k) (W k)
    (U k ^ 2) (V k ^ 2) (opNorm (Z k) ^ 2) (opNorm (W k) ^ 2) (R k ^ 2)
    hu0 hv0 hZ0 hW0 hr0
    (fun a => by
      rw [hUsq]
      exact Finset.le_sup'
        (fun b : Fin B => ∑ i, (Arot C D * W k) i b ^ 2) (Finset.mem_univ a))
    (fun a => by
      rw [hVsq]
      exact Finset.le_sup'
        (fun b : Fin B => ∑ j, ((Arot C D)ᵀ * Z k) j b ^ 2) (Finset.mem_univ a))
    (fun a => projection_column_sq_le_opNorm_sq (Z k) a)
    (fun a => projection_column_sq_le_opNorm_sq (W k) a)
    (fun a => by
      have hmax := Finset.le_sup' (fun b => |resid (Arot C D) (E k b)|)
        (Finset.mem_univ a)
      have hR0 : 0 ≤ R k := (abs_nonneg _).trans hmax
      change resid (Arot C D) (E k a) ^ 2 ≤ R k ^ 2
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hR0).mpr hmax)
  dsimp only [F]
  simp_rw [projection_weighted_filter_fderiv_left hℓ e C D T M hB w x hrepr
    (j := k)]
  simp_rw [projection_weighted_filter_fderiv_right hℓ e C D T M hB w x hrepr
    (j := k)]
  calc
    (∑ a, ∑ i,
        (w k * (B : ℝ)⁻¹ * ((Arot C D * W k) i a * resid (Arot C M) (E k a) +
          resid (Arot C D) (E k a) * (Arot C M * W k) i a)) ^ 2) +
      ∑ a, ∑ j,
        (w k * (B : ℝ)⁻¹ * (((Arot C D)ᵀ * Z k) j a * resid (Arot C M) (E k a) +
          resid (Arot C D) (E k a) * ((Arot C M)ᵀ * Z k) j a)) ^ 2 =
        (w k * (B : ℝ)⁻¹) ^ 2 *
          ((∑ a, ∑ i, ((Arot C D * W k) i a * resid (Arot C M) (E k a) +
            resid (Arot C D) (E k a) * (Arot C M * W k) i a) ^ 2) +
           (∑ a, ∑ j, (((Arot C D)ᵀ * Z k) j a * resid (Arot C M) (E k a) +
            resid (Arot C D) (E k a) * ((Arot C M)ᵀ * Z k) j a) ^ 2)) := by
          simp only [mul_add, Finset.mul_sum]
          apply congrArg₂ (· + ·)
          · apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro i _
            ring
          · apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ ≤ (w k * (B : ℝ)⁻¹) ^ 2 * (2 * fro (Arot C M) ^ 2 *
        (U k ^ 2 * opNorm (W k) ^ 2 * opNorm (Z k) ^ 2 +
          V k ^ 2 * opNorm (Z k) ^ 2 * opNorm (W k) ^ 2 +
          R k ^ 2 * (opNorm (W k) ^ 2 + opNorm (Z k) ^ 2))) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring

private lemma projection_eLpNorm_triple_mul_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f g h : Ω → ℝ)
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P)
    (hh : AEStronglyMeasurable h P) :
    eLpNorm (fun x => f x * g x * h x) 1 P ≤
      eLpNorm f 3 P * eLpNorm g 3 P * eLpNorm h 3 P := by
  letI : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2) :=
    ENNReal.HolderTriple.of_toReal (by
      simp only [ENNReal.toReal_ofNat, ENNReal.toReal_div]
      constructor <;> norm_num)
  letI : ENNReal.HolderTriple (3 / 2 : ℝ≥0∞) 3 1 :=
    ENNReal.HolderTriple.of_toReal (by
      simp only [ENNReal.toReal_ofNat, ENNReal.toReal_div]
      constructor <;> norm_num)
  have hfg : AEStronglyMeasurable (fun x => f x * g x) P := hf.mul hg
  have h₁ := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
    (μ := P) (f := fun x => f x * g x) (g := h)
    (p := (3 / 2 : ℝ≥0∞)) (q := (3 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
    (fun a b : ℝ => a * b) 1 (by fun_prop) hfg hh
    (Filter.Eventually.of_forall fun x => by simp [abs_mul])
  have h₂ := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
    (μ := P) (f := f) (g := g) (p := (3 : ℝ≥0∞)) (q := (3 : ℝ≥0∞))
    (r := (3 / 2 : ℝ≥0∞))
    (fun a b : ℝ => a * b) 1 (by fun_prop) hf hg
    (Filter.Eventually.of_forall fun x => by simp [abs_mul])
  exact h₁.trans (by
    simp only [ENNReal.coe_one, one_mul]
    gcongr
    simpa using h₂)

private lemma projection_eLpNorm_sq_three {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (hf : AEStronglyMeasurable f P) :
    eLpNorm (fun x => f x ^ 2) 3 P = eLpNorm f 6 P ^ 2 := by
  convert (eLpNorm_norm_rpow (μ := P) (p := (3 : ℝ≥0∞)) f hf (q := (2 : ℝ))
    (by norm_num)) using 1 <;> norm_num [Real.norm_eq_abs, sq_abs]

private lemma projection_lintegral_sq_triple {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f g h : Ω → ℝ)
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P)
    (hh : AEStronglyMeasurable h P) :
    ∫⁻ x, ENNReal.ofReal (f x ^ 2 * g x ^ 2 * h x ^ 2) ∂P ≤
      eLpNorm f 6 P ^ 2 * eLpNorm g 6 P ^ 2 * eLpNorm h 6 P ^ 2 := by
  have hprod : AEStronglyMeasurable (fun x => f x ^ 2 * g x ^ 2 * h x ^ 2) P :=
    (hf.pow 2 |>.mul (hg.pow 2)).mul (hh.pow 2)
  calc
    (∫⁻ x, ENNReal.ofReal (f x ^ 2 * g x ^ 2 * h x ^ 2) ∂P) =
        eLpNorm (fun x => f x ^ 2 * g x ^ 2 * h x ^ 2) 1 P := by
      rw [eLpNorm_one_eq_lintegral_enorm hprod]
      apply lintegral_congr
      intro x
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg]
      positivity
    _ ≤ eLpNorm (fun x => f x ^ 2) 3 P * eLpNorm (fun x => g x ^ 2) 3 P *
        eLpNorm (fun x => h x ^ 2) 3 P :=
      projection_eLpNorm_triple_mul_le P _ _ _ (hf.pow 2) (hg.pow 2) (hh.pow 2)
    _ = _ := by rw [projection_eLpNorm_sq_three P f hf,
      projection_eLpNorm_sq_three P g hg, projection_eLpNorm_sq_three P h hh]

private lemma projection_canonical_batch_factor_lintegral_le
    (certOp : Muon.External.GaussianOpNormL6) (γ Kb : ℝ) (hγ : 0 ≤ γ)
    {m n B : ℕ} (hB : 0 < B) (hdim : ((max m n : ℕ) : ℝ) ≤ γ * (B : ℝ))
    (A : Mat m n)
    (hres : let μ := Measure.pi (fun _ : Fin B =>
        (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
      let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
        Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
      eLpNorm (fun z : Fin B → Vec m × Vec n =>
        Finset.univ.sup' hne (fun a => |resid A (z a)|)) 6 μ ≤
        ENNReal.ofReal (Kb * Real.log (2 * (B : ℝ)) * fro A)) :
    let μ := Measure.pi (fun _ : Fin B =>
      (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
    let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
    let Z : (Fin B → Vec m × Vec n) → Mat m B := fun z i a => (z a).1 i
    let W : (Fin B → Vec m × Vec n) → Mat n B := fun z j a => (z a).2 j
    let U : (Fin B → Vec m × Vec n) → ℝ := fun z => Real.sqrt
      (Finset.univ.sup' hne (fun a => ∑ i, (A * W z) i a ^ 2))
    let V : (Fin B → Vec m × Vec n) → ℝ := fun z => Real.sqrt
      (Finset.univ.sup' hne (fun a => ∑ j, (Aᵀ * Z z) j a ^ 2))
    let R : (Fin B → Vec m × Vec n) → ℝ := fun z =>
      Finset.univ.sup' hne (fun a => |resid A (z a)|)
    ∫⁻ z, ENNReal.ofReal
        (U z ^ 2 * opNorm (W z) ^ 2 * opNorm (Z z) ^ 2 +
          V z ^ 2 * opNorm (Z z) ^ 2 * opNorm (W z) ^ 2 +
          R z ^ 2 * (opNorm (W z) ^ 2 + opNorm (Z z) ^ 2)) ∂μ ≤
      ENNReal.ofReal
        (4 * (|Kb| + 1) ^ 2 * (Real.log (2 * (B : ℝ))) ^ 2 * fro A ^ 2 *
          ((certOp.holds.choose + 1) * (Real.sqrt γ + 1)) ^ 4 * (B : ℝ) ^ 2) := by
  dsimp only
  let μ := Measure.pi (fun _ : Fin B =>
    (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
  let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
  let Z : (Fin B → Vec m × Vec n) → Mat m B := fun z i a => (z a).1 i
  let W : (Fin B → Vec m × Vec n) → Mat n B := fun z j a => (z a).2 j
  let U : (Fin B → Vec m × Vec n) → ℝ := fun z => Real.sqrt
    (Finset.univ.sup' hne (fun a => ∑ i, (A * W z) i a ^ 2))
  let V : (Fin B → Vec m × Vec n) → ℝ := fun z => Real.sqrt
    (Finset.univ.sup' hne (fun a => ∑ j, (Aᵀ * Z z) j a ^ 2))
  let R : (Fin B → Vec m × Vec n) → ℝ := fun z =>
    Finset.univ.sup' hne (fun a => |resid A (z a)|)
  let OZ : (Fin B → Vec m × Vec n) → ℝ := fun z => opNorm (Z z)
  let OW : (Fin B → Vec m × Vec n) → ℝ := fun z => opNorm (W z)
  let a₀ := (|Kb| + 1) * Real.log (2 * (B : ℝ)) * fro A
  let o₀ := (certOp.holds.choose + 1) * (Real.sqrt γ + 1) * Real.sqrt B
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ B := by exact_mod_cast hB
    nlinarith)
  have ha₀ : 0 ≤ a₀ := mul_nonneg (mul_nonneg (by positivity) hlog) (Real.sqrt_nonneg _)
  have hC := certOp.holds.choose_spec
  have ho₀ : 0 ≤ o₀ := by
    dsimp [o₀]
    exact mul_nonneg (mul_nonneg (by linarith [hC.1]) (by positivity)) (by positivity)
  have hone_o₀ : 1 ≤ o₀ := by
    have hB1 : (1 : ℝ) ≤ Real.sqrt B := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ B from hB))
    have hc1 : 1 ≤ certOp.holds.choose + 1 := by linarith [hC.1]
    have hg1 : 1 ≤ Real.sqrt γ + 1 := by linarith [Real.sqrt_nonneg γ]
    dsimp [o₀]
    have hcg : 1 ≤ (certOp.holds.choose + 1) * (Real.sqrt γ + 1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hg1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hcg) (sub_nonneg.mpr hB1)]
  have hm : (m : ℝ) ≤ γ * (B : ℝ) :=
    (Nat.cast_le.mpr (Nat.le_max_left m n)).trans hdim
  have hn : (n : ℝ) ≤ γ * (B : ℝ) :=
    (Nat.cast_le.mpr (Nat.le_max_right m n)).trans hdim
  have hsqrt (d : ℕ) (hd : (d : ℝ) ≤ γ * (B : ℝ)) :
      Real.sqrt d ≤ Real.sqrt γ * Real.sqrt B := by
    calc
      Real.sqrt d ≤ Real.sqrt (γ * (B : ℝ)) := Real.sqrt_le_sqrt hd
      _ = _ := Real.sqrt_mul hγ _
  have hOZ : eLpNorm OZ 6 μ ≤ ENNReal.ofReal o₀ := by
    have hh := hC.2 m B (Fin B → Vec m × Vec n) μ Z
      (projection_canonical_iid_matrix_left m n B)
    have harg : certOp.holds.choose * (Real.sqrt m + Real.sqrt B) ≤ o₀ := by
      have hs := hsqrt m hm
      have hc0 := hC.1.le
      have hB0 := Real.sqrt_nonneg (B : ℝ)
      dsimp [o₀]
      nlinarith [mul_le_mul_of_nonneg_left
        (add_le_add_right hs (Real.sqrt B)) hc0]
    exact hh.trans (ENNReal.ofReal_le_ofReal harg)
  have hOW : eLpNorm OW 6 μ ≤ ENNReal.ofReal o₀ := by
    have hh := hC.2 n B (Fin B → Vec m × Vec n) μ W
      (projection_canonical_iid_matrix_right m n B)
    have harg : certOp.holds.choose * (Real.sqrt n + Real.sqrt B) ≤ o₀ := by
      have hs := hsqrt n hn
      have hc0 := hC.1.le
      have hB0 := Real.sqrt_nonneg (B : ℝ)
      dsimp [o₀]
      nlinarith [mul_le_mul_of_nonneg_left
        (add_le_add_right hs (Real.sqrt B)) hc0]
    exact hh.trans (ENNReal.ofReal_le_ofReal harg)
  have hR : eLpNorm R 6 μ ≤ ENNReal.ofReal a₀ := by
    have hk : Kb * Real.log (2 * (B : ℝ)) * fro A ≤ a₀ := by
      dsimp [a₀]
      have hk' : Kb ≤ |Kb| + 1 := by linarith [le_abs_self Kb]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk' hlog)
        (show 0 ≤ fro A from Real.sqrt_nonneg _)
    exact hres.trans (ENNReal.ofReal_le_ofReal hk)
  have hU : eLpNorm U 6 μ ≤ ENNReal.ofReal a₀ :=
    (projection_max_mulVec_eLpNorm_le_resid hB A).trans hR
  have hV : eLpNorm V 6 μ ≤ ENNReal.ofReal a₀ :=
    (projection_max_transpose_mulVec_eLpNorm_le_resid hB A).trans hR
  have hmU : AEStronglyMeasurable U μ := by
    apply Measurable.aestronglyMeasurable
    dsimp only [U]
    simp only [Matrix.mul_apply]
    dsimp only [W]
    fun_prop
  have hmV : AEStronglyMeasurable V μ := by
    apply Measurable.aestronglyMeasurable
    dsimp only [V]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    dsimp only [Z]
    fun_prop
  have hmR : AEStronglyMeasurable R μ := by
    apply Measurable.aestronglyMeasurable
    dsimp [R]
    unfold resid Matrix.mulVec dotProduct
    fun_prop
  have hmOZ : AEStronglyMeasurable OZ μ := by
    apply Continuous.comp_aestronglyMeasurable projection_opNorm_continuous
    exact Measurable.aestronglyMeasurable (by dsimp [Z]; fun_prop)
  have hmOW : AEStronglyMeasurable OW μ := by
    apply Continuous.comp_aestronglyMeasurable projection_opNorm_continuous
    exact Measurable.aestronglyMeasurable (by dsimp [W]; fun_prop)
  have hmOne : AEStronglyMeasurable (fun _z : Fin B → Vec m × Vec n => (1 : ℝ)) μ :=
    aestronglyMeasurable_const
  have hOne : eLpNorm (fun _z : Fin B → Vec m × Vec n => (1 : ℝ)) 6 μ = 1 := by
    have hμ : μ ≠ 0 := by
      intro hz
      have hu := measure_univ (μ := μ)
      rw [hz] at hu
      simp at hu
    rw [eLpNorm_const (μ := μ) (p := (6 : ℝ≥0∞)) 1 (by norm_num) hμ,
      measure_univ]
    norm_num
  have htermU := projection_lintegral_sq_triple μ U OW OZ hmU hmOW hmOZ
  have htermV := projection_lintegral_sq_triple μ V OZ OW hmV hmOZ hmOW
  have htermRW := projection_lintegral_sq_triple μ R OW (fun _ => 1) hmR hmOW hmOne
  have htermRZ := projection_lintegral_sq_triple μ R OZ (fun _ => 1) hmR hmOZ hmOne
  have hbU : ∫⁻ z, ENNReal.ofReal (U z ^ 2 * OW z ^ 2 * OZ z ^ 2) ∂μ ≤
      ENNReal.ofReal (a₀ ^ 2 * o₀ ^ 4) := by
    calc
      _ ≤ eLpNorm U 6 μ ^ 2 * eLpNorm OW 6 μ ^ 2 * eLpNorm OZ 6 μ ^ 2 := htermU
      _ ≤ ENNReal.ofReal a₀ ^ 2 * ENNReal.ofReal o₀ ^ 2 * ENNReal.ofReal o₀ ^ 2 := by
        gcongr
      _ = _ := by rw [← ENNReal.ofReal_pow ha₀ 2, ← ENNReal.ofReal_pow ho₀ 2,
        ← ENNReal.ofReal_mul (sq_nonneg a₀),
        ← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have hbV : ∫⁻ z, ENNReal.ofReal (V z ^ 2 * OZ z ^ 2 * OW z ^ 2) ∂μ ≤
      ENNReal.ofReal (a₀ ^ 2 * o₀ ^ 4) := by
    calc
      _ ≤ eLpNorm V 6 μ ^ 2 * eLpNorm OZ 6 μ ^ 2 * eLpNorm OW 6 μ ^ 2 := htermV
      _ ≤ ENNReal.ofReal a₀ ^ 2 * ENNReal.ofReal o₀ ^ 2 * ENNReal.ofReal o₀ ^ 2 := by
        gcongr
      _ = _ := by rw [← ENNReal.ofReal_pow ha₀ 2, ← ENNReal.ofReal_pow ho₀ 2,
        ← ENNReal.ofReal_mul (sq_nonneg a₀),
        ← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have hbRW : ∫⁻ z, ENNReal.ofReal (R z ^ 2 * OW z ^ 2) ∂μ ≤
      ENNReal.ofReal (a₀ ^ 2 * o₀ ^ 4) := by
    have hh : ∫⁻ z, ENNReal.ofReal (R z ^ 2 * OW z ^ 2 * (1 : ℝ) ^ 2) ∂μ ≤
        eLpNorm R 6 μ ^ 2 * eLpNorm OW 6 μ ^ 2 *
          eLpNorm (fun _z : Fin B → Vec m × Vec n => (1 : ℝ)) 6 μ ^ 2 := htermRW
    simp only [one_pow, mul_one, hOne] at hh
    calc
      _ ≤ eLpNorm R 6 μ ^ 2 * eLpNorm OW 6 μ ^ 2 := hh
      _ ≤ ENNReal.ofReal a₀ ^ 2 * ENNReal.ofReal o₀ ^ 2 := by gcongr
      _ ≤ ENNReal.ofReal a₀ ^ 2 * ENNReal.ofReal o₀ ^ 4 := by
        apply mul_le_mul_of_nonneg_left
        exact pow_le_pow_right₀ (by simpa using ENNReal.ofReal_le_ofReal hone_o₀) (by norm_num)
        exact bot_le
      _ = _ := by rw [← ENNReal.ofReal_pow ha₀ 2, ← ENNReal.ofReal_pow ho₀ 4,
        ← ENNReal.ofReal_mul (sq_nonneg a₀)]
  have hbRZ : ∫⁻ z, ENNReal.ofReal (R z ^ 2 * OZ z ^ 2) ∂μ ≤
      ENNReal.ofReal (a₀ ^ 2 * o₀ ^ 4) := by
    have hh : ∫⁻ z, ENNReal.ofReal (R z ^ 2 * OZ z ^ 2 * (1 : ℝ) ^ 2) ∂μ ≤
        eLpNorm R 6 μ ^ 2 * eLpNorm OZ 6 μ ^ 2 *
          eLpNorm (fun _z : Fin B → Vec m × Vec n => (1 : ℝ)) 6 μ ^ 2 := htermRZ
    simp only [one_pow, mul_one, hOne] at hh
    calc
      _ ≤ eLpNorm R 6 μ ^ 2 * eLpNorm OZ 6 μ ^ 2 := hh
      _ ≤ ENNReal.ofReal a₀ ^ 2 * ENNReal.ofReal o₀ ^ 2 := by gcongr
      _ ≤ ENNReal.ofReal a₀ ^ 2 * ENNReal.ofReal o₀ ^ 4 := by
        apply mul_le_mul_of_nonneg_left
        exact pow_le_pow_right₀ (by simpa using ENNReal.ofReal_le_ofReal hone_o₀) (by norm_num)
        exact bot_le
      _ = _ := by rw [← ENNReal.ofReal_pow ha₀ 2, ← ENNReal.ofReal_pow ho₀ 4,
        ← ENNReal.ofReal_mul (sq_nonneg a₀)]
  have hsplit : (∫⁻ z, ENNReal.ofReal
      (U z ^ 2 * OW z ^ 2 * OZ z ^ 2 + V z ^ 2 * OZ z ^ 2 * OW z ^ 2 +
        R z ^ 2 * (OW z ^ 2 + OZ z ^ 2)) ∂μ) =
      (∫⁻ z, ENNReal.ofReal (U z ^ 2 * OW z ^ 2 * OZ z ^ 2) ∂μ) +
      (∫⁻ z, ENNReal.ofReal (V z ^ 2 * OZ z ^ 2 * OW z ^ 2) ∂μ) +
      (∫⁻ z, ENNReal.ofReal (R z ^ 2 * OW z ^ 2) ∂μ) +
      (∫⁻ z, ENNReal.ofReal (R z ^ 2 * OZ z ^ 2) ∂μ) := by
    have hfun : (fun z => ENNReal.ofReal
        (U z ^ 2 * OW z ^ 2 * OZ z ^ 2 + V z ^ 2 * OZ z ^ 2 * OW z ^ 2 +
          R z ^ 2 * (OW z ^ 2 + OZ z ^ 2))) =
        (fun z => (ENNReal.ofReal (U z ^ 2 * OW z ^ 2 * OZ z ^ 2) +
          ENNReal.ofReal (V z ^ 2 * OZ z ^ 2 * OW z ^ 2)) +
          (ENNReal.ofReal (R z ^ 2 * OW z ^ 2) +
            ENNReal.ofReal (R z ^ 2 * OZ z ^ 2))) := by
      funext z
      have hU0 : 0 ≤ U z ^ 2 * OW z ^ 2 * OZ z ^ 2 :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
      have hV0 : 0 ≤ V z ^ 2 * OZ z ^ 2 * OW z ^ 2 :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
      have hRW0 : 0 ≤ R z ^ 2 * OW z ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      have hRZ0 : 0 ≤ R z ^ 2 * OZ z ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      let u := U z ^ 2 * OW z ^ 2 * OZ z ^ 2
      let v := V z ^ 2 * OZ z ^ 2 * OW z ^ 2
      let rw₀ := R z ^ 2 * OW z ^ 2
      let rz₀ := R z ^ 2 * OZ z ^ 2
      have hu : 0 ≤ u := by dsimp [u]; positivity
      have hv : 0 ≤ v := by dsimp [v]; positivity
      have hrw : 0 ≤ rw₀ := by dsimp [rw₀]; positivity
      have hrz : 0 ≤ rz₀ := by dsimp [rz₀]; positivity
      rw [show U z ^ 2 * OW z ^ 2 * OZ z ^ 2 + V z ^ 2 * OZ z ^ 2 * OW z ^ 2 +
          R z ^ 2 * (OW z ^ 2 + OZ z ^ 2) = (u + v) + (rw₀ + rz₀) by
        dsimp [u, v, rw₀, rz₀]; ring]
      calc
        ENNReal.ofReal ((u + v) + (rw₀ + rz₀)) =
            ENNReal.ofReal (u + v) + ENNReal.ofReal (rw₀ + rz₀) :=
          ENNReal.ofReal_add (add_nonneg hu hv) (add_nonneg hrw hrz)
        _ = (ENNReal.ofReal u + ENNReal.ofReal v) + ENNReal.ofReal (rw₀ + rz₀) := by
          rw [ENNReal.ofReal_add hu hv]
        _ = (ENNReal.ofReal u + ENNReal.ofReal v) +
            (ENNReal.ofReal rw₀ + ENNReal.ofReal rz₀) := by
          rw [ENNReal.ofReal_add hrw hrz]
    rw [hfun]
    let fU : (Fin B → Vec m × Vec n) → ℝ≥0∞ := fun z =>
      ENNReal.ofReal (U z ^ 2 * OW z ^ 2 * OZ z ^ 2)
    let fV : (Fin B → Vec m × Vec n) → ℝ≥0∞ := fun z =>
      ENNReal.ofReal (V z ^ 2 * OZ z ^ 2 * OW z ^ 2)
    let fRW : (Fin B → Vec m × Vec n) → ℝ≥0∞ := fun z =>
      ENNReal.ofReal (R z ^ 2 * OW z ^ 2)
    let fRZ : (Fin B → Vec m × Vec n) → ℝ≥0∞ := fun z =>
      ENNReal.ofReal (R z ^ 2 * OZ z ^ 2)
    have hfU : AEMeasurable fU μ :=
      ((hmU.pow 2).mul (hmOW.pow 2) |>.mul (hmOZ.pow 2)).aemeasurable.ennreal_ofReal
    have hfV : AEMeasurable fV μ :=
      ((hmV.pow 2).mul (hmOZ.pow 2) |>.mul (hmOW.pow 2)).aemeasurable.ennreal_ofReal
    have hfRW : AEMeasurable fRW μ :=
      ((hmR.pow 2).mul (hmOW.pow 2)).aemeasurable.ennreal_ofReal
    change (∫⁻ z, (fU z + fV z) + (fRW z + fRZ z) ∂μ) = _
    have hout := lintegral_add_left' (μ := μ) (hfU.add hfV) (fun z => fRW z + fRZ z)
    have hleft := lintegral_add_left' (μ := μ) hfU fV
    have hright := lintegral_add_left' (μ := μ) hfRW fRZ
    calc
      _ = (∫⁻ z, fU z + fV z ∂μ) + (∫⁻ z, fRW z + fRZ z ∂μ) := by
        simpa only [Pi.add_apply] using hout
      _ = _ := by
        rw [hleft, hright]
        simp only [fU, fV, fRW, fRZ]
        ac_rfl
  rw [hsplit]
  calc
    _ ≤ ENNReal.ofReal (a₀ ^ 2 * o₀ ^ 4) + ENNReal.ofReal (a₀ ^ 2 * o₀ ^ 4) +
        ENNReal.ofReal (a₀ ^ 2 * o₀ ^ 4) + ENNReal.ofReal (a₀ ^ 2 * o₀ ^ 4) := by gcongr
    _ = ENNReal.ofReal (4 * a₀ ^ 2 * o₀ ^ 4) := by
      rw [show 4 * a₀ ^ 2 * o₀ ^ 4 = 4 * (a₀ ^ 2 * o₀ ^ 4) by ring]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
      ring
    _ = _ := by
      congr 1
      dsimp [a₀, o₀]
      have hsqrt4 : Real.sqrt (B : ℝ) ^ 4 = (B : ℝ) ^ 2 := by
        calc
          Real.sqrt (B : ℝ) ^ 4 = (Real.sqrt (B : ℝ) ^ 2) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg B)]
      calc
        4 * ((|Kb| + 1) * Real.log (2 * (B : ℝ)) * fro A) ^ 2 *
            ((certOp.holds.choose + 1) * (Real.sqrt γ + 1) * Real.sqrt B) ^ 4 =
            4 * (|Kb| + 1) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * fro A ^ 2 *
              ((certOp.holds.choose + 1) * (Real.sqrt γ + 1)) ^ 4 *
                Real.sqrt B ^ 4 := by ring
        _ = _ := by rw [hsqrt4]

open scoped Matrix.Norms.L2Operator in
private lemma projection_sqrt_opNorm_sq {k : ℕ} (A : Mat k k) (hA : A.PosSemidef) :
    opNorm (CFC.sqrt A) ^ 2 = opNorm A := by
  have hh : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hs : CFC.sqrt A * CFC.sqrt A = A :=
    CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.mpr hA)
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (CFC.sqrt A)
  rw [hh, hs] at h
  simpa only [opNorm_eq_norm, pow_two] using h.symm

private lemma projection_Arot_fro_le (p : DynParams) {m n B : ℕ}
    (C : Covariances m n) (hsize : SizeFin C B p.γstar p.CSig) (M : Mat m n) :
    fro (Arot C M) ≤ p.CSig * fro M := by
  have ho := projection_sqrt_opNorm_sq C.Sout C.psdOut
  have hi := projection_sqrt_opNorm_sq C.Sin C.psdIn
  have hC : 0 ≤ p.CSig := le_trans (by norm_num) p.hC
  have hOut : 0 ≤ opNorm (rOut C) := by unfold opNorm; exact norm_nonneg _
  have hIn : 0 ≤ opNorm (rIn C) := by unfold opNorm; exact norm_nonneg _
  have hn : opNorm (rOut C) * opNorm (rIn C) ≤ p.CSig := by
    have h3 : opNorm (rOut C) ^ 2 ≤ p.CSig := ho.le.trans hsize.2.1
    have h4 : opNorm (rIn C) ^ 2 ≤ p.CSig := hi.le.trans hsize.2.2
    have hm := mul_le_mul h3 h4 (sq_nonneg (opNorm (rIn C))) hC
    nlinarith [mul_nonneg hOut hIn]
  have hsq : fro (Arot C M) ^ 2 ≤ (p.CSig * fro M) ^ 2 := by
    calc
      fro (Arot C M) ^ 2 ≤ fro (rOut C * M) ^ 2 * opNorm (rIn C) ^ 2 :=
        projection_fro_mul_sq_le_right _ _
      _ ≤ (opNorm (rOut C) ^ 2 * fro M ^ 2) * opNorm (rIn C) ^ 2 :=
        mul_le_mul_of_nonneg_right (projection_fro_mul_sq_le_left _ _) (sq_nonneg _)
      _ ≤ (p.CSig * fro M) ^ 2 := by
        have hf : 0 ≤ fro M := Real.sqrt_nonneg _
        have hsqprod : (opNorm (rOut C) * opNorm (rIn C)) ^ 2 ≤ p.CSig ^ 2 := by
          nlinarith [mul_nonneg hOut hIn]
        nlinarith [mul_nonneg hC hf]
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _)
    (mul_nonneg hC (Real.sqrt_nonneg _)) two_ne_zero).mp hsq

private lemma projection_filter_Arot_adjoint_sq_le (p : DynParams) (rlo : ℝ)
    (hrlo : 0 < rlo) {m n B : ℕ} (C : Covariances m n)
    (hsize : SizeFin C B p.γstar p.CSig) (D T : Mat m n)
    (hD : rlo ≤ riskSigma C D) (N : Mat m n) :
    ∃ M : Mat m n,
      fro (Arot C M) ^ 2 ≤
        (p.CSig * ((2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)))) ^ 2 * fro T ^ 2 ∧
      ∀ R : Mat m n, frobIP T (dirDeriv (physRidge p C D) N R) = frobIP M R := by
  have hbase : 0 < 2 * rlo * p.ϱ := mul_pos (mul_pos (by norm_num) hrlo) p.hϱ
  have hrisk : 0 < riskSigma C D := hrlo.trans_le hD
  have hridge : 0 < physRidge p C D := mul_pos (mul_pos (by norm_num) hrisk) p.hϱ
  obtain ⟨M, hM, hrepr⟩ := projection_filter_adjoint_test hridge N T
  refine ⟨M, ?_, hrepr⟩
  have hridge_lower : 2 * rlo * p.ϱ ≤ physRidge p C D := by
    dsimp only [physRidge]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD (by norm_num)) p.hϱ.le
  have hpow : (physRidge p C D) ^ (-(1 / 2 : ℝ)) ≤
      (2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hbase hridge_lower (by norm_num)
  have hMT : fro M ≤ (2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * fro T :=
    hM.trans (mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg _))
  have hA := projection_Arot_fro_le p C hsize M
  have hC : 0 ≤ p.CSig := le_trans (by norm_num) p.hC
  have hq : 0 ≤ (2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hbase.le _
  have hchain : fro (Arot C M) ≤
      p.CSig * ((2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * fro T) :=
    hA.trans (mul_le_mul_of_nonneg_left hMT hC)
  have hright : 0 ≤ p.CSig * ((2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * fro T) :=
    mul_nonneg hC (mul_nonneg hq (Real.sqrt_nonneg _))
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hchain 2
  calc
    fro (Arot C M) ^ 2 ≤
        (p.CSig * ((2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * fro T)) ^ 2 := hsq
    _ = _ := by ring

private lemma projection_one_batch_energy_lintegral_le
    (p : DynParams) (rlo rhi Kb : ℝ) (certOp : Muon.External.GaussianOpNormL6)
    (hrlo : 0 < rlo) {κ : Type*} [Fintype κ] {m n B d : ℕ}
    (hB : 0 < B) (C : Covariances m n) (hsize : SizeFin C B p.γstar p.CSig)
    (D T : Mat m n) (hDhi : riskSigma C D ≤ rhi)
    (e : ((κ × Fin B) × (Fin m ⊕ Fin n)) ≃ Fin d) (k : κ)
    (hres : let μ := Measure.pi (fun _ : Fin B =>
        (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
      let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
        Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
      eLpNorm (fun z : Fin B → Vec m × Vec n =>
        Finset.univ.sup' hne (fun a => |resid (Arot C D) (z a)|)) 6 μ ≤
        ENNReal.ofReal (Kb * Real.log (2 * (B : ℝ)) * fro (Arot C D))) :
    let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
    let Z : EuclideanSpace ℝ (Fin d) → Mat m B := fun x i a =>
      x (e ((k, a), Sum.inl i))
    let W : EuclideanSpace ℝ (Fin d) → Mat n B := fun x j a =>
      x (e ((k, a), Sum.inr j))
    let E : EuclideanSpace ℝ (Fin d) → Fin B → Vec m × Vec n := fun x a =>
      (fun i => Z x i a, fun j => W x j a)
    let U : EuclideanSpace ℝ (Fin d) → ℝ := fun x => Real.sqrt
      (Finset.univ.sup' hne (fun a => ∑ i, (Arot C D * W x) i a ^ 2))
    let V : EuclideanSpace ℝ (Fin d) → ℝ := fun x => Real.sqrt
      (Finset.univ.sup' hne (fun a => ∑ j, ((Arot C D)ᵀ * Z x) j a ^ 2))
    let R : EuclideanSpace ℝ (Fin d) → ℝ := fun x =>
      Finset.univ.sup' hne (fun a => |resid (Arot C D) (E x a)|)
    ∫⁻ x, ENNReal.ofReal (2 * (B : ℝ)⁻¹ ^ 2 *
        ((p.CSig * ((2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)))) ^ 2 * fro T ^ 2) *
        (U x ^ 2 * opNorm (W x) ^ 2 * opNorm (Z x) ^ 2 +
          V x ^ 2 * opNorm (Z x) ^ 2 * opNorm (W x) ^ 2 +
          R x ^ 2 * (opNorm (W x) ^ 2 + opNorm (Z x) ^ 2)))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      ENNReal.ofReal (16 * rhi *
        (p.CSig * ((2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)))) ^ 2 *
        (|Kb| + 1) ^ 2 * ((certOp.holds.choose + 1) *
          (Real.sqrt p.γstar + 1)) ^ 4 * Real.log (2 * (B : ℝ)) ^ 2 * fro T ^ 2) := by
  dsimp only
  let μ := Measure.pi (fun _ : Fin B =>
    (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
  let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
  let Z₀ : (Fin B → Vec m × Vec n) → Mat m B := fun z i a => (z a).1 i
  let W₀ : (Fin B → Vec m × Vec n) → Mat n B := fun z j a => (z a).2 j
  let U₀ : (Fin B → Vec m × Vec n) → ℝ := fun z => Real.sqrt
    (Finset.univ.sup' hne (fun a => ∑ i, (Arot C D * W₀ z) i a ^ 2))
  let V₀ : (Fin B → Vec m × Vec n) → ℝ := fun z => Real.sqrt
    (Finset.univ.sup' hne (fun a => ∑ j, ((Arot C D)ᵀ * Z₀ z) j a ^ 2))
  let R₀ : (Fin B → Vec m × Vec n) → ℝ := fun z =>
    Finset.univ.sup' hne (fun a => |resid (Arot C D) (z a)|)
  let H : (Fin B → Vec m × Vec n) → ℝ := fun z =>
    U₀ z ^ 2 * opNorm (W₀ z) ^ 2 * opNorm (Z₀ z) ^ 2 +
      V₀ z ^ 2 * opNorm (Z₀ z) ^ 2 * opNorm (W₀ z) ^ 2 +
      R₀ z ^ 2 * (opNorm (W₀ z) ^ 2 + opNorm (Z₀ z) ^ 2)
  have hmU : Measurable U₀ := by
    dsimp only [U₀]
    simp only [Matrix.mul_apply]
    dsimp only [W₀]
    fun_prop
  have hmV : Measurable V₀ := by
    dsimp only [V₀]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    dsimp only [Z₀]
    fun_prop
  have hmR : Measurable R₀ := by
    dsimp [R₀]
    unfold resid Matrix.mulVec dotProduct
    fun_prop
  have hmZ : Measurable (fun z => opNorm (Z₀ z)) :=
    projection_opNorm_continuous.measurable.comp (by dsimp [Z₀]; fun_prop)
  have hmW : Measurable (fun z => opNorm (W₀ z)) :=
    projection_opNorm_continuous.measurable.comp (by dsimp [W₀]; fun_prop)
  have hmH : Measurable (fun z => ENNReal.ofReal (H z)) := by
    apply Measurable.ennreal_ofReal
    dsimp only [H]
    fun_prop
  have hcan := projection_canonical_batch_factor_lintegral_le certOp p.γstar Kb
    p.hγ hB hsize.1 (Arot C D) hres
  have htransport :
      (∫⁻ x : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (H (fun a =>
          (fun i => x (e ((k, a), Sum.inl i)),
            fun j => x (e ((k, a), Sum.inr j)))))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
      ∫⁻ z, ENNReal.ofReal (H z) ∂μ := by
    exact (projection_encoded_euclidean_batch_measurePreserving e k).lintegral_comp hmH
  let s := 2 * (B : ℝ)⁻¹ ^ 2 *
    ((p.CSig * ((2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)))) ^ 2 * fro T ^ 2)
  let b := 4 * (|Kb| + 1) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 *
    fro (Arot C D) ^ 2 * ((certOp.holds.choose + 1) *
      (Real.sqrt p.γstar + 1)) ^ 4 * (B : ℝ) ^ 2
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hcan' : (∫⁻ z, ENNReal.ofReal (H z) ∂μ) ≤ ENNReal.ofReal b := by
    change (∫⁻ z, ENNReal.ofReal (H z) ∂μ) ≤ ENNReal.ofReal b at hcan
    exact hcan
  have hDrot : fro (Arot C D) ^ 2 ≤ 2 * rhi := by
    rw [eqn_app_setup_whitened_risk] at hDhi
    linarith
  have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hcancel : (B : ℝ)⁻¹ ^ 2 * (B : ℝ) ^ 2 = 1 := by
    field_simp
  have hreal : s * b ≤ 16 * rhi *
      (p.CSig * ((2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)))) ^ 2 *
      (|Kb| + 1) ^ 2 * ((certOp.holds.choose + 1) *
        (Real.sqrt p.γstar + 1)) ^ 4 * Real.log (2 * (B : ℝ)) ^ 2 * fro T ^ 2 := by
    dsimp [s, b]
    calc
      2 * (B : ℝ)⁻¹ ^ 2 *
          ((p.CSig * ((2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)))) ^ 2 * fro T ^ 2) *
          (4 * (|Kb| + 1) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 *
            fro (Arot C D) ^ 2 * ((certOp.holds.choose + 1) *
              (Real.sqrt p.γstar + 1)) ^ 4 * (B : ℝ) ^ 2) =
          8 * (|Kb| + 1) ^ 2 * ((certOp.holds.choose + 1) *
            (Real.sqrt p.γstar + 1)) ^ 4 * Real.log (2 * (B : ℝ)) ^ 2 *
            ((p.CSig * ((2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)))) ^ 2 * fro T ^ 2) *
              fro (Arot C D) ^ 2 := by
        field_simp
        ring
      _ ≤ 8 * (|Kb| + 1) ^ 2 * ((certOp.holds.choose + 1) *
            (Real.sqrt p.γstar + 1)) ^ 4 * Real.log (2 * (B : ℝ)) ^ 2 *
          ((p.CSig * ((2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)))) ^ 2 * fro T ^ 2) *
          (2 * rhi) := by gcongr
      _ = _ := by ring
  change (∫⁻ x, ENNReal.ofReal (s * H (fun a =>
      (fun i => x (e ((k, a), Sum.inl i)),
        fun j => x (e ((k, a), Sum.inr j)))))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ≤ _
  simp_rw [ENNReal.ofReal_mul hs]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, htransport]
  calc
    ENNReal.ofReal s * (∫⁻ z, ENNReal.ofReal (H z) ∂μ) ≤
        ENNReal.ofReal s * ENNReal.ofReal b := by gcongr
    _ = ENNReal.ofReal (s * b) := by rw [ENNReal.ofReal_mul hs]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-! ## `lem:app-dyn-poincare` -/

/-- `lem:app-dyn-poincare` (cr-2026-10-23), part (i): the projection variance of one stationary update.
`D` is deterministic with `r₋ ≤ 𝓡(D) ≤ r₊`, `0 < r₋ ≤ r₊`; `T` deterministic; the constant `K` depends on the fixed
parameters and `r₋, r₊` only and is quantified before the dimensions. The cited Gaussian Poincaré inequality is the
explicit argument `cert`. Statement verbatim from `section.tex` (ll. 1713–1721):
```latex
\begin{lemma}[Projection variance]\label{lem:app-dyn-poincare}
Let $D$ be deterministic with $r_-\le\cR(D)\le r_+$, consider the stationary
chain at $(t,D)$, and let $T\in\R^{\Nout\times\Nin}$ be deterministic. Then
\[
\Var\langle T,V_r\rangle\le C\log^2(2B)\norm T_\F^2,\qquad
\Var\Big\langle T,\sum_{r<L}V_r\Big\rangle\le CL^2\log^2(2B)\norm T_\F^2 .
\]
No bound on $\norm T$ and no diffuseness of $D$ is assumed.
\end{lemma}
```
-/
theorem lem_app_dyn_poincare_i (p : DynParams) (rlo rhi : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi)
    (cert : Muon.External.GaussianPoincare)  (certOp : Muon.External.GaussianOpNormL6) :
    ∃ K : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B) (t r : ℕ) (D T : Mat m n),
      rlo ≤ riskSigma S.C D → riskSigma S.C D ≤ rhi →
        MemLp (fun ω => frobIP T (stationaryV p S.C S.cs t D r ω)) 2 P ∧
        variance (fun ω => frobIP T (stationaryV p S.C S.cs t D r ω)) P ≤
          K * Real.log (2 * (B : ℝ)) ^ 2 * fro T ^ 2 := by
  obtain ⟨Kb, hKb⟩ := lem_app_dyn_batch_ii certOp p.γstar p.CSig
  let q := p.CSig * ((2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)))
  let C₀ := (|Kb| + 1) ^ 2 *
    ((certOp.holds.choose + 1) * (Real.sqrt p.γstar + 1)) ^ 4
  refine ⟨32 * rhi * q ^ 2 * C₀, ?_⟩
  intro Ω _ P _ m n B S t r D T hDlo hDhi
  have hrisk : 0 < riskSigma S.C D := hrlo.trans_le hDlo
  have hB : 0 < B := projection_batch_pos_of_risk_pos p S.C S.size D hrisk
  let μ := Measure.pi (fun _ : Fin B =>
    (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
  have hresPhys := (hKb m n B S.C hB S.size
    (Fin B → Vec m × Vec n) μ (fun a z => z a)
    (projection_canonical_iid_batch m n B) D).2
  have hres :
      let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
        Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
      eLpNorm (fun z : Fin B → Vec m × Vec n =>
        Finset.univ.sup' hne (fun a => |resid (Arot S.C D) (z a)|)) 6 μ ≤
        ENNReal.ofReal (Kb * Real.log (2 * (B : ℝ)) * fro (Arot S.C D)) := by
    dsimp only
    have hfun : (fun z : Fin B → Vec m × Vec n =>
        Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
          (fun a => |resid D (phys S.C (z a))|)) =
        (fun z : Fin B → Vec m × Vec n =>
          Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩)
            (fun a => |resid (Arot S.C D) (z a)|)) := by
      funext z
      apply Finset.sup'_congr _ rfl
      intro a _
      rw [eqn_app_setup_whitened_resid]
      rfl
    rw [hfun] at hresPhys
    simpa only [Arot] using hresPhys
  have hK0 : 0 ≤ 16 * rhi * q ^ 2 * C₀ *
      Real.log (2 * (B : ℝ)) ^ 2 * fro T ^ 2 := by
    have hrhi : 0 < rhi := hrlo.trans_le hle
    dsimp [q, C₀]
    positivity
  apply projection_stationary_variance_of_weighted_energy p S.C S.cs cert t r D T
    hrisk S.size (32 * rhi * q ^ 2 * C₀ *
      Real.log (2 * (B : ℝ)) ^ 2 * fro T ^ 2) (by
        nlinarith)
  intro J d e
  let κ := Fin (r + 1) ⊕ Fin J
  let w : κ → ℝ := Sum.elim
    (fun i => emaW p.β (r + 1 - (i + 1)))
    (fun j => p.β ^ (r + 1) * emaW p.β j)
  let N : EuclideanSpace ℝ (Fin d) → Mat m n := fun x =>
    ∑ j : κ, w j • batchGrad D (fun a => phys S.C
      (fun i => x (e ((j, a), Sum.inl i)),
        fun i => x (e ((j, a), Sum.inr i))))
  have hridge : 0 < physRidge p S.C D :=
    mul_pos (mul_pos (by norm_num) hrisk) p.hϱ
  let hne : (Finset.univ : Finset (Fin B)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hB⟩⟩
  let E : EuclideanSpace ℝ (Fin d) → κ → Fin B → Vec m × Vec n := fun x k a =>
    (fun i => x (e ((k, a), Sum.inl i)), fun j => x (e ((k, a), Sum.inr j)))
  let Z : κ → EuclideanSpace ℝ (Fin d) → Mat m B := fun k x i a => (E x k a).1 i
  let W : κ → EuclideanSpace ℝ (Fin d) → Mat n B := fun k x j a => (E x k a).2 j
  let U : κ → EuclideanSpace ℝ (Fin d) → ℝ := fun k x => Real.sqrt
    (Finset.univ.sup' hne (fun a => ∑ i, (Arot S.C D * W k x) i a ^ 2))
  let V : κ → EuclideanSpace ℝ (Fin d) → ℝ := fun k x => Real.sqrt
    (Finset.univ.sup' hne (fun a => ∑ j, ((Arot S.C D)ᵀ * Z k x) j a ^ 2))
  let R : κ → EuclideanSpace ℝ (Fin d) → ℝ := fun k x =>
    Finset.univ.sup' hne (fun a => |resid (Arot S.C D) (E x k a)|)
  let G : κ → EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun k x => ENNReal.ofReal
    (2 * (B : ℝ)⁻¹ ^ 2 * (q ^ 2 * fro T ^ 2) *
      (U k x ^ 2 * opNorm (W k x) ^ 2 * opNorm (Z k x) ^ 2 +
        V k x ^ 2 * opNorm (Z k x) ^ 2 * opNorm (W k x) ^ 2 +
        R k x ^ 2 * (opNorm (W k x) ^ 2 + opNorm (Z k x) ^ 2)))
  have hG (k : κ) : AEMeasurable (G k) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    apply Measurable.aemeasurable
    apply Measurable.ennreal_ofReal
    have hmZ : Measurable (fun x => opNorm (Z k x)) :=
      projection_opNorm_continuous.measurable.comp (by dsimp [Z, E]; fun_prop)
    have hmW : Measurable (fun x => opNorm (W k x)) :=
      projection_opNorm_continuous.measurable.comp (by dsimp [W, E]; fun_prop)
    have hmU : Measurable (U k) := by
      dsimp only [U]
      simp only [Matrix.mul_apply]
      dsimp only [W, E]
      fun_prop
    have hmV : Measurable (V k) := by
      dsimp only [V]
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      dsimp only [Z, E]
      fun_prop
    have hmR : Measurable (R k) := by
      dsimp [R, E]
      unfold resid Matrix.mulVec dotProduct
      fun_prop
    fun_prop
  have hGbound (k : κ) :
      ∫⁻ x, G k x ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        ENNReal.ofReal (16 * rhi * q ^ 2 * C₀ *
          Real.log (2 * (B : ℝ)) ^ 2 * fro T ^ 2) := by
    have hh := projection_one_batch_energy_lintegral_le p rlo rhi Kb certOp hrlo
      hB S.C S.size D T hDhi e k hres
    simpa only [G, E, Z, W, U, V, R, hne, q, C₀, mul_assoc] using hh
  have hw : ∑ k : κ, w k ^ 2 ≤ 2 := by
    exact projection_truncation_weight_sq_sum_le_two p.hβ.1 p.hβ.2 r J
  have hsum := projection_fintype_energy_sum_le_two
    (stdGaussian (EuclideanSpace ℝ (Fin d))) w G hG
    (16 * rhi * q ^ 2 * C₀ * Real.log (2 * (B : ℝ)) ^ 2 * fro T ^ 2)
    hK0 hGbound hw
  calc
    (∫⁻ x : EuclideanSpace ℝ (Fin d),
        ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => frobIP T
          (Q (physRidge p S.C D) (∑ j : Fin (r + 1) ⊕ Fin J,
            Sum.elim (fun i : Fin (r + 1) => emaW p.β (r + 1 - (i + 1)))
              (fun j : Fin J => p.β ^ (r + 1) * emaW p.β j) j •
                batchGrad D (fun a => phys S.C
                  (fun i => y (e ((j, a), Sum.inl i)),
                    fun i => y (e ((j, a), Sum.inr i))))))) x‖ₑ ^ 2
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ≤
        ∫⁻ x, ∑ k : κ, ENNReal.ofReal (w k ^ 2) * G k x
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      apply lintegral_mono
      intro x
      change ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => frobIP T
          (Q (physRidge p S.C D) (∑ k : κ, w k • batchGrad D (fun b => phys S.C
            (fun u => y (e ((k, b), Sum.inl u)),
              fun v => y (e ((k, b), Sum.inr v))))))) x‖ₑ ^ 2 ≤
        ∑ k : κ, ENNReal.ofReal (w k ^ 2) * G k x
      obtain ⟨M, hM, hrepr⟩ := projection_filter_Arot_adjoint_sq_le
        p rlo hrlo S.C S.size D T hDlo (N x)
      have hp := projection_weighted_filter_gradient_energy_le hridge e S.C D T M hB w x
        (fun R₀ => by simpa only [N] using hrepr R₀)
      have hp' : ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => frobIP T
          (Q (physRidge p S.C D) (∑ k : κ, w k • batchGrad D (fun b => phys S.C
            (fun u => y (e ((k, b), Sum.inl u)),
              fun v => y (e ((k, b), Sum.inr v))))))) x‖ ^ 2 ≤
          ∑ k : κ, w k ^ 2 * (2 * (B : ℝ)⁻¹ ^ 2 * (q ^ 2 * fro T ^ 2) *
            (U k x ^ 2 * opNorm (W k x) ^ 2 * opNorm (Z k x) ^ 2 +
              V k x ^ 2 * opNorm (Z k x) ^ 2 * opNorm (W k x) ^ 2 +
              R k x ^ 2 * (opNorm (W k x) ^ 2 + opNorm (Z k x) ^ 2))) := by
        calc
          _ ≤ ∑ k : κ, w k ^ 2 * (2 * (B : ℝ)⁻¹ ^ 2 * fro (Arot S.C M) ^ 2 *
              (U k x ^ 2 * opNorm (W k x) ^ 2 * opNorm (Z k x) ^ 2 +
                V k x ^ 2 * opNorm (Z k x) ^ 2 * opNorm (W k x) ^ 2 +
                R k x ^ 2 * (opNorm (W k x) ^ 2 + opNorm (Z k x) ^ 2))) := by
            simpa only [E, Z, W, U, V, R, hne] using hp
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro k _
            have hfactor : 0 ≤ U k x ^ 2 * opNorm (W k x) ^ 2 * opNorm (Z k x) ^ 2 +
                V k x ^ 2 * opNorm (Z k x) ^ 2 * opNorm (W k x) ^ 2 +
                R k x ^ 2 * (opNorm (W k x) ^ 2 + opNorm (Z k x) ^ 2) := by positivity
            have hw0 : 0 ≤ w k ^ 2 := sq_nonneg _
            dsimp [q] at hM ⊢
            gcongr
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      calc
        ENNReal.ofReal _ ≤ ENNReal.ofReal (∑ k : κ, w k ^ 2 *
            (2 * (B : ℝ)⁻¹ ^ 2 * (q ^ 2 * fro T ^ 2) *
              (U k x ^ 2 * opNorm (W k x) ^ 2 * opNorm (Z k x) ^ 2 +
                V k x ^ 2 * opNorm (Z k x) ^ 2 * opNorm (W k x) ^ 2 +
                R k x ^ 2 * (opNorm (W k x) ^ 2 + opNorm (Z k x) ^ 2)))) :=
          ENNReal.ofReal_le_ofReal hp'
        _ = _ := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          · apply Finset.sum_congr rfl
            intro k _
            rw [ENNReal.ofReal_mul (sq_nonneg _)]
          · intro k _
            exact mul_nonneg (sq_nonneg _) (by positivity)
    _ ≤ ENNReal.ofReal (2 * (16 * rhi * q ^ 2 * C₀ *
        Real.log (2 * (B : ℝ)) ^ 2 * fro T ^ 2)) := hsum
    _ = ENNReal.ofReal (32 * rhi * q ^ 2 * C₀ *
        Real.log (2 * (B : ℝ)) ^ 2 * fro T ^ 2) := by congr 1 <;> ring

/-- `lem:app-dyn-poincare` (cr-2026-10-23), part (ii): the projection variance of the block sum
`∑_{r<L} V_r`, with `L = blockLen B`. Same hypotheses and constant convention as part (i). Statement verbatim from
`section.tex` (ll. 1713–1721):
```latex
\begin{lemma}[Projection variance]\label{lem:app-dyn-poincare}
Let $D$ be deterministic with $r_-\le\cR(D)\le r_+$, consider the stationary
chain at $(t,D)$, and let $T\in\R^{\Nout\times\Nin}$ be deterministic. Then
\[
\Var\langle T,V_r\rangle\le C\log^2(2B)\norm T_\F^2,\qquad
\Var\Big\langle T,\sum_{r<L}V_r\Big\rangle\le CL^2\log^2(2B)\norm T_\F^2 .
\]
No bound on $\norm T$ and no diffuseness of $D$ is assumed.
\end{lemma}
```
-/
theorem lem_app_dyn_poincare_ii (p : DynParams) (rlo rhi : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi)
    (cert : Muon.External.GaussianPoincare)  (certOp : Muon.External.GaussianOpNormL6) :
    ∃ K : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B) (t : ℕ) (D T : Mat m n),
      rlo ≤ riskSigma S.C D → riskSigma S.C D ≤ rhi →
        MemLp (fun ω => frobIP T (∑ r ∈ Finset.range (blockLen B), stationaryV p S.C S.cs t D r ω)) 2 P ∧
        variance (fun ω => frobIP T (∑ r ∈ Finset.range (blockLen B), stationaryV p S.C S.cs t D r ω)) P ≤
          K * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * fro T ^ 2 := by
  obtain ⟨K, hK⟩ := lem_app_dyn_poincare_i p rlo rhi hrlo hle cert certOp
  refine ⟨K, ?_⟩
  intro Ω _ P _ m n B S t D T hDlo hDhi
  have hproj (r : ℕ) := hK Ω P m n B S t r D T hDlo hDhi
  have hsum : (fun ω => frobIP T
      (∑ r ∈ Finset.range (blockLen B), stationaryV p S.C S.cs t D r ω)) =
      (fun ω => ∑ r ∈ Finset.range (blockLen B),
        frobIP T (stationaryV p S.C S.cs t D r ω)) := by
    funext ω
    exact frobIP_sum_right T _ _
  rw [hsum]
  constructor
  · exact memLp_finsetSum _ (fun r _ => (hproj r).1)
  · calc
      variance (fun ω => ∑ r ∈ Finset.range (blockLen B),
          frobIP T (stationaryV p S.C S.cs t D r ω)) P ≤
          ((Finset.range (blockLen B)).card : ℝ) ^ 2 *
            (K * Real.log (2 * (B : ℝ)) ^ 2 * fro T ^ 2) :=
        projection_variance_sum_le P _ _ (fun r _ => (hproj r).1) _
          (fun r _ => (hproj r).2)
      _ = K * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * fro T ^ 2 := by
        rw [Finset.card_range]
        ring


/-! ## `lem:app-dyn-martingale` -/

open scoped Matrix.Norms.L2Operator in
private lemma concentration_cfc_opNorm_le_one {k : ℕ} {c : ℝ} (A : Mat k k)
    (hA : A.PosSemidef) (hAop : opNorm A ≤ c) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Icc (0 : ℝ) c, |f x| ≤ 1) :
    opNorm (cfc f A) ≤ 1 := by
  by_cases hk : k = 0
  · subst k
    simp [opNorm]
  letI : NeZero k := ⟨hk⟩
  rw [opNorm_eq_norm]
  apply norm_cfc_le zero_le_one
  intro x hx
  apply hf x
  refine ⟨spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hA) hx, ?_⟩
  have hspec : |x| ≤ opNorm A := by
    simpa only [Real.norm_eq_abs, ← opNorm_eq_norm] using spectrum.norm_le_norm_of_mem hx
  exact (le_abs_self x).trans (hspec.trans hAop)

open scoped Matrix.Norms.L2Operator in
private lemma concentration_wfg_fro_le {m n : ℕ} {c : ℝ} (f g : ℝ → ℝ)
    (C : Covariances m n)
    (hf : ∀ x ∈ Icc (0 : ℝ) c, |f x| ≤ 1)
    (hg : ∀ x ∈ Icc (0 : ℝ) c, |g x| ≤ 1)
    (hout : opNorm C.Sout ≤ c) (hin : opNorm C.Sin ≤ c) (X : Mat m n) :
    fro (wfg f g C X) ≤ fro X := by
  have hfo : opNorm (cfc f C.Sout) ≤ 1 :=
    concentration_cfc_opNorm_le_one C.Sout C.psdOut hout f hf
  have hgo : opNorm (cfc g C.Sin) ≤ 1 :=
    concentration_cfc_opNorm_le_one C.Sin C.psdIn hin g hg
  have hleft := projection_fro_mul_sq_le_left (cfc f C.Sout) X
  have hright := projection_fro_mul_sq_le_right (cfc f C.Sout * X) (cfc g C.Sin)
  have hf0 : 0 ≤ fro (wfg f g C X) := Real.sqrt_nonneg _
  have hX0 : 0 ≤ fro X := Real.sqrt_nonneg _
  have hfo0 : 0 ≤ opNorm (cfc f C.Sout) := by
    rw [opNorm_eq_norm]
    exact norm_nonneg _
  have hgo0 : 0 ≤ opNorm (cfc g C.Sin) := by
    rw [opNorm_eq_norm]
    exact norm_nonneg _
  have hfo2 : opNorm (cfc f C.Sout) ^ 2 ≤ 1 := by nlinarith
  have hgo2 : opNorm (cfc g C.Sin) ^ 2 ≤ 1 := by nlinarith
  have hleft' : fro (cfc f C.Sout * X) ^ 2 ≤ fro X ^ 2 :=
    hleft.trans (by nlinarith [sq_nonneg (fro X)])
  have hright' : fro (cfc f C.Sout * X * cfc g C.Sin) ^ 2 ≤
      fro (cfc f C.Sout * X) ^ 2 :=
    hright.trans (by nlinarith [sq_nonneg (fro (cfc f C.Sout * X))])
  unfold wfg
  nlinarith

private lemma concentration_frobIP_comm {m n : ℕ} (X Y : Mat m n) :
    frobIP X Y = frobIP Y X := by
  unfold frobIP
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]

private lemma concentration_wfg_self_adjoint {m n : ℕ} (f g : ℝ → ℝ)
    (C : Covariances m n) (X Y : Mat m n) :
    frobIP (wfg f g C X) Y = frobIP X (wfg f g C Y) := by
  unfold wfg frobIP
  have hf : (cfc f C.Sout)ᵀ = cfc f C.Sout := by
    have h : IsSelfAdjoint (cfc f C.Sout) := cfc_predicate f C.Sout
    have h' := h.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h'
  have hg : (cfc g C.Sin)ᵀ = cfc g C.Sin := by
    have h : IsSelfAdjoint (cfc g C.Sin) := cfc_predicate g C.Sin
    have h' := h.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h'
  simp only [Matrix.transpose_mul, hf, hg, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

private lemma concentration_Xfg_quadratic {m n : ℕ} (f g : ℝ → ℝ)
    (C : Covariances m n) (D U : Mat m n) (a : ℝ) :
    Xfg f g C (D - a • U) - Xfg f g C D =
      -2 * a * frobIP (wfg f g C D) U + a ^ 2 * frobIP U (wfg f g C U) := by
  unfold Xfg wfg frobIP
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  have hf : (cfc f C.Sout)ᵀ = cfc f C.Sout := by
    have h : IsSelfAdjoint (cfc f C.Sout) := cfc_predicate f C.Sout
    have h' := h.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h'
  have hg : (cfc g C.Sin)ᵀ = cfc g C.Sin := by
    have h : IsSelfAdjoint (cfc g C.Sin) := cfc_predicate g C.Sin
    have h' := h.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h'
  have hleft : ((cfc f C.Sout * D * cfc g C.Sin) * Uᵀ).trace =
      (D * (cfc f C.Sout * U * cfc g C.Sin)ᵀ).trace := by
    simp only [Matrix.transpose_mul, hf, hg, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hcomm : (U * (cfc f C.Sout * D * cfc g C.Sin)ᵀ).trace =
      (D * (cfc f C.Sout * U * cfc g C.Sin)ᵀ).trace := by
    rw [← Matrix.trace_transpose]
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hf, hg,
      Matrix.mul_assoc] using hleft
  rw [hleft, hcomm]
  ring

private lemma concentration_delta_sum (p : DynParams) {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (S : DynSetup p P m n B)
    (t L : ℕ) (ω : Ω) :
    dynDelta S (t + L) ω = dynDelta S t ω -
      (p.h / (B : ℝ)) • ∑ r ∈ Finset.range L, dynUpd S (t + r) ω := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.add_succ]
    change Muon.Setup.devRand S.C S.alg (dynStart S) (dynBatch S) (t + L + 1) ω = _
    rw [Muon.Setup.devRand_succ]
    change dynDelta S (t + L) ω - S.alg.η (t + L) • dynUpd S (t + L) ω = _
    rw [ih, S.alg_η]
    simp only [Finset.sum_range_succ, smul_add]
    module

private lemma concentration_upd_decomposition (p : DynParams) {m n B : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (S : DynSetup p P m n B)
    (t : ℕ) (ω : Ω) :
    (∑ r ∈ Finset.range (blockLen B), dynUpd S (t + r) ω) =
      dynStatSum p S t ω + dynSumErr p S t ω := by
  simp only [dynStatSum, dynSumErr]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  module

private lemma concentration_pointwise_identity (p : DynParams) {m n B : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (S : DynSetup p P m n B)
    (f g : ℝ → ℝ) (t : ℕ) (ω : Ω) :
    Xfg f g S.C (dynDelta S (t + blockLen B) ω) - Xfg f g S.C (dynDelta S t ω) =
      -2 * (p.h / (B : ℝ)) *
          frobIP (wfg f g S.C (dynDelta S t ω)) (dynStatSum p S t ω) -
      2 * (p.h / (B : ℝ)) *
          frobIP (wfg f g S.C (dynDelta S t ω)) (dynSumErr p S t ω) +
      (p.h / (B : ℝ)) ^ 2 *
          frobIP (dynStatSum p S t ω + dynSumErr p S t ω)
            (wfg f g S.C (dynStatSum p S t ω + dynSumErr p S t ω)) := by
  rw [concentration_delta_sum, concentration_Xfg_quadratic,
    concentration_upd_decomposition]
  unfold frobIP
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, Matrix.trace_add]
  ring

private lemma concentration_past_le {p : DynParams} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) : dynPast S t ≤ mΩ := by
  refine sup_le (iSup_le fun s => iSup_le fun _ => iSup_le fun a => ?_) S.M0_meas.comap_le
  exact (S.cs.meas_act s a).comap_le

private lemma concentration_past_mono {p : DynParams} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) {s t : ℕ} (hst : s ≤ t) :
    dynPast S s ≤ dynPast S t := by
  refine sup_le_sup_right (iSup_le fun u => iSup_le fun hu => iSup_le fun a => ?_) _
  exact le_iSup₂_of_le u ⟨hu.1, hu.2.trans (by exact_mod_cast hst)⟩
    (le_iSup_of_le a le_rfl)

private lemma concentration_risk_nonneg {m n : ℕ} (C : Covariances m n)
    (D : Mat m n) : 0 ≤ riskSigma C D := by
  rw [eqn_app_setup_whitened_risk]
  positivity

private lemma concentration_risk_cont {m n : ℕ} (C : Covariances m n) :
    Continuous (fun D : Mat m n => riskSigma C D) := by
  unfold riskSigma pairSigma
  fun_prop

private lemma concentration_mat_meas {Ω : Type*} {σ : MeasurableSpace Ω} {m n : ℕ}
    {F : Ω → Mat m n} (h : ∀ i j, Measurable[σ] fun ω => F ω i j) :
    Measurable[σ] F :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => h i j

private lemma concentration_entry_meas {Ω : Type*} {σ : MeasurableSpace Ω} {m n : ℕ}
    {F : Ω → Mat m n} (hF : Measurable[σ] F) (i : Fin m) (j : Fin n) :
    Measurable[σ] fun ω => F ω i j :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hF)

private lemma concentration_grad_meas {Ω : Type*} {σ : MeasurableSpace Ω} {B m n : ℕ}
    {D : Ω → Mat m n} {b : Ω → Batch m n B}
    (hD : Measurable[σ] D) (hb : Measurable[σ] b) :
    Measurable[σ] (fun ω => grad (D ω) (b ω)) := by
  have hc : Continuous (fun z : Mat m n × Batch m n B => grad z.1 z.2) := by
    unfold grad resid outer
    fun_prop
  exact Measurable.comp (g := fun z : Mat m n × Batch m n B => grad z.1 z.2)
    (f := fun ω => (D ω, b ω)) hc.measurable (hD.prodMk hb)

private lemma concentration_stepUpdate_meas {Ω : Type*} {σ : MeasurableSpace Ω}
    {B m n : ℕ} (C : Covariances m n) (q : AlgParams m n)
    (s : Ω → AlgState m n) (b : Ω → Batch m n B)
    (hW : Measurable[σ] (fun ω => (s ω).W))
    (hM : Measurable[σ] (fun ω => (s ω).Mprev)) (hb : Measurable[σ] b) :
    Measurable[σ] (fun ω => stepUpdate C q (s ω) (b ω)) ∧
      Measurable[σ] (fun ω => stepBuffer q (s ω) (b ω)) := by
  have hD : Measurable[σ] (fun ω => errorOf q (s ω)) :=
    (continuous_id.sub continuous_const).measurable.comp hW
  have hR : Measurable[σ] (fun ω => riskSigma C (errorOf q (s ω))) :=
    (concentration_risk_cont C).measurable.comp hD
  have hset : MeasurableSet[σ] {ω | riskSigma C (errorOf q (s ω)) = 0} :=
    hR (measurableSet_singleton 0)
  have hG : Measurable[σ] (fun ω => grad (errorOf q (s ω)) (b ω)) :=
    concentration_grad_meas hD hb
  have hbuf : Measurable[σ] (fun ω => stepBuffer q (s ω) (b ω)) := by
    apply concentration_mat_meas
    intro i j
    simp only [stepBuffer, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact ((concentration_entry_meas hM i j).const_mul _).add
      ((concentration_entry_meas hG i j).const_mul _)
  refine ⟨Measurable.ite hset measurable_const ?_, hbuf⟩
  have hnn : ∀ ω, 0 ≤ 2 * riskSigma C (errorOf q (s ω)) * q.ϱ := fun ω =>
    mul_nonneg (mul_nonneg (by norm_num) (concentration_risk_nonneg C _)) q.hϱ.le
  have hridge : Measurable[σ]
      (fun ω => (⟨2 * riskSigma C (errorOf q (s ω)) * q.ϱ, hnn ω⟩ : Ici (0 : ℝ))) :=
    ((hR.const_mul 2).mul_const q.ϱ).subtype_mk
  exact measurable_Q.comp (hridge.prodMk hbuf)

private lemma concentration_step_meas {Ω : Type*} {σ : MeasurableSpace Ω}
    {B m n : ℕ} (C : Covariances m n) (q : AlgParams m n) (k : ℕ)
    (s : Ω → AlgState m n) (b : Ω → Batch m n B)
    (hW : Measurable[σ] (fun ω => (s ω).W))
    (hM : Measurable[σ] (fun ω => (s ω).Mprev)) (hb : Measurable[σ] b) :
    Measurable[σ] (fun ω => (step C q k (s ω) (b ω)).W) ∧
      Measurable[σ] (fun ω => (step C q k (s ω) (b ω)).Mprev) := by
  obtain ⟨hU, hbuf⟩ := concentration_stepUpdate_meas C q s b hW hM hb
  refine ⟨?_, hbuf⟩
  apply concentration_mat_meas
  intro i j
  simp only [step, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact (concentration_entry_meas hW i j).sub
    ((concentration_entry_meas hU i j).const_mul _)

private lemma concentration_pi_meas {Ω : Type*} {σ : MeasurableSpace Ω}
    {ι : Type*} {π : ι → Type*} [∀ i, MeasurableSpace (π i)]
    {F : Ω → ∀ i, π i} (h : ∀ i, Measurable[σ] fun ω => F ω i) :
    Measurable[σ] F := measurable_pi_iff.mpr h

private lemma concentration_batch_meas {p : DynParams} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (u : ℕ) :
    Measurable[dynPast S (u + 1)] (dynBatch S u) := by
  refine concentration_pi_meas (fun a => ?_)
  have hz : Measurable[dynPast S (u + 1)] (S.cs.act ((u : ℤ) + 1) a) := by
    apply Measurable.of_comap_le
    refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le ((u : ℤ) + 1) ⟨by omega, by push_cast; omega⟩
      (le_iSup_of_le a le_rfl)
  exact (show Continuous (fun z : Vec m × Vec n => phys S.C z) by
    unfold phys
    fun_prop).measurable.comp hz

private lemma concentration_state_meas {p : DynParams} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S t] (fun ω => (dynState S t ω).W) ∧
      Measurable[dynPast S t] (dynBuf S t) := by
  induction t with
  | zero =>
      refine ⟨measurable_const, ?_⟩
      exact (comap_measurable S.M0).mono le_sup_right le_rfl
  | succ k ih =>
      exact concentration_step_meas (σ := dynPast S (k + 1)) S.C S.alg k
        (dynState S k) (dynBatch S k)
        (ih.1.mono (concentration_past_mono S (Nat.le_succ k)) le_rfl)
        (ih.2.mono (concentration_past_mono S (Nat.le_succ k)) le_rfl)
        (concentration_batch_meas S k)

private lemma concentration_delta_meas {p : DynParams} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S t] (dynDelta S t) :=
  (continuous_id.sub continuous_const).measurable.comp (concentration_state_meas S t).1

private lemma concentration_upd_meas {p : DynParams} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S (t + 1)] (dynUpd S t) := by
  exact (concentration_stepUpdate_meas (σ := dynPast S (t + 1)) S.C S.alg
    (dynState S t) (dynBatch S t)
    ((concentration_state_meas S t).1.mono
      (concentration_past_mono S (Nat.le_succ t)) le_rfl)
    ((concentration_state_meas S t).2.mono
      (concentration_past_mono S (Nat.le_succ t)) le_rfl)
    (concentration_batch_meas S t)).1

private lemma concentration_blockIncr_meas {p : DynParams} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (f g : ℝ → ℝ) (b : ℕ) :
    Measurable[dynPast S ((b + 1) * blockLen B)] (blockIncr p f g S b) := by
  have hX : Continuous (Xfg f g S.C) := by
    unfold Xfg wfg frobIP
    fun_prop
  have ht : b * blockLen B ≤ (b + 1) * blockLen B := Nat.mul_le_mul_right _ (Nat.le_succ b)
  exact (hX.measurable.comp (concentration_delta_meas S _)).sub
    (hX.measurable.comp ((concentration_delta_meas S _).mono
      (concentration_past_mono S ht) le_rfl))

private lemma concentration_admSet_meas {m n : ℕ} (C : Covariances m n)
    (q : ℝ × ℝ × ℝ) : MeasurableSet (admSetOf C q) := by
  have hR : Measurable (fun D : Mat m n => riskSigma C D) :=
    (concentration_risk_cont C).measurable
  have hF : Measurable (fun D : Mat m n => fro D ^ 2) := by
    simp_rw [projection_fro_sq]
    fun_prop
  unfold admSetOf
  simp only [Set.setOf_and]
  exact (measurableSet_le measurable_const hR).inter
    ((measurableSet_le hR measurable_const).inter
      (measurableSet_le hF measurable_const))

private lemma concentration_A_Aplus {m n : ℕ} (p : DynParams)
    (C : Covariances m n) {D : Mat m n} (hD : D ∈ admA p C) :
    D ∈ admAplus p C := by
  simp only [admA, admAplus, admBase, enl, admSetOf, Set.mem_setOf_eq] at hD ⊢
  exact ⟨by linarith [hD.1, p.hr0], by linarith [hD.2.1, p.hr, p.hr0],
    by linarith [hD.2.2, p.hE]⟩

private lemma concentration_tauPlus_iff {p : DynParams} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) (ω : Ω) :
    (t : ℕ∞) < tauPlus p S ω ↔
      ∀ s ≤ t, dynDelta S s ω ∈ admAplus p S.C := by
  unfold tauPlus
  constructor
  · intro h s hs
    by_contra hnot
    have hle : (⨅ (u : ℕ) (_ : dynDelta S u ω ∉ admAplus p S.C),
        (u : ℕ∞)) ≤ (s : ℕ∞) := iInf₂_le s hnot
    exact absurd (lt_of_lt_of_le h hle) (by exact_mod_cast not_lt.2 hs)
  · intro h
    have hle : ((t + 1 : ℕ) : ℕ∞) ≤
        ⨅ (u : ℕ) (_ : dynDelta S u ω ∉ admAplus p S.C), (u : ℕ∞) := by
      refine le_iInf₂ fun s hs => ?_
      have hst : ¬ s ≤ t := fun h' => hs (h s h')
      exact_mod_cast Nat.succ_le_of_lt (not_le.1 hst)
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self t) hle

private lemma concentration_tauPlus_meas {p : DynParams} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) :
    MeasurableSet[dynPast S t] {ω | (t : ℕ∞) < tauPlus p S ω} := by
  have heq : {ω | (t : ℕ∞) < tauPlus p S ω} =
      ⋂ s ∈ Finset.range (t + 1), {ω | dynDelta S s ω ∈ admAplus p S.C} := by
    ext ω
    simp only [Set.mem_setOf_eq, concentration_tauPlus_iff, Set.mem_iInter,
      Finset.mem_range]
    constructor <;> intro h s hs <;> exact h s (by omega)
  rw [heq]
  refine MeasurableSet.biInter (Finset.countable_toSet _) fun s hs => ?_
  have hst : s ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
  exact (concentration_past_mono S hst) _
    ((concentration_delta_meas S s) (concentration_admSet_meas S.C _))

private lemma concentration_blockLen_pos {B : ℕ} (hB : 0 < B) :
    0 < blockLen B := by
  unfold blockLen
  apply Nat.floor_pos.mpr
  exact Real.one_le_rpow (by exact_mod_cast hB) (by norm_num)

private lemma concentration_tau_of_good {p : DynParams} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (ω : Ω) (hL : 0 < blockLen B)
    (hwin : ∀ b, dynDelta S (b * blockLen B) ω ∈ admA p S.C →
      ∀ u, b * blockLen B ≤ u → u ≤ b * blockLen B + blockLen B →
        dynDelta S u ω ∈ admAplus p S.C)
    (b : ℕ) (hb : ∀ b' ≤ b, dynDelta S (b' * blockLen B) ω ∈ admA p S.C) :
    ((b * blockLen B : ℕ) : ℕ∞) < tauPlus p S ω := by
  rw [concentration_tauPlus_iff]
  intro s hs
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · exact concentration_A_Aplus p S.C (by
      simpa only [zero_mul] using hb 0 (Nat.zero_le b))
  · obtain ⟨b', hb'def⟩ : ∃ b', b' = (s - 1) / blockLen B := ⟨_, rfl⟩
    have hdm := Nat.div_add_mod' (s - 1) (blockLen B)
    rw [← hb'def] at hdm
    have hml := Nat.mod_lt (s - 1) hL
    have h1 : b' * blockLen B ≤ s - 1 := by omega
    have h2 : s ≤ b' * blockLen B + blockLen B := by omega
    have hb'b : b' ≤ b := by
      by_contra hcon
      have h3 : (b + 1) * blockLen B ≤ b' * blockLen B :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at h3
      omega
    exact hwin b' (hb b' hb'b) s (by omega) h2

private lemma concentration_abs_entry_le_fro {m n : ℕ} (A : Mat m n)
    (i : Fin m) (j : Fin n) : |A i j| ≤ fro A := by
  unfold fro
  apply Real.abs_le_sqrt
  have h1 : ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖A i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  simpa [Real.norm_eq_abs, sq_abs] using h1.trans h2

private lemma concentration_Q_entry_bound {m n : ℕ} (ϱ : ℝ) (hϱ : 0 ≤ ϱ)
    (K : Mat m n) (i : Fin m) (j : Fin n) : |Q ϱ K i j| ≤ (m : ℝ) + 1 := by
  obtain ⟨_, hf, hk, _⟩ := lem_app_setup_filter_i ϱ hϱ K
  have h1 := concentration_abs_entry_le_fro (Q ϱ K) i j
  have hr : (K.rank : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hk.trans (min_le_left m n)
  have h2 : fro (Q ϱ K) ^ 2 ≤ (m : ℝ) := hf.trans hr
  have h0 : 0 ≤ fro (Q ϱ K) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (fro (Q ϱ K) - 1)]

private lemma concentration_dynUpd_bound {p : DynParams} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) (ω : Ω) (i : Fin m) (j : Fin n) :
    |dynUpd S t ω i j| ≤ (m : ℝ) + 1 := by
  unfold dynUpd gtRand stepUpdate
  split_ifs
  · simp
    positivity
  · exact concentration_Q_entry_bound _
      (mul_nonneg (mul_nonneg (by norm_num) (concentration_risk_nonneg _ _))
        S.alg.hϱ.le) _ i j

private lemma concentration_delta_entry_bdd {p : DynParams} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (s : ℕ) :
    ∃ R : ℝ, ∀ (ω : Ω) (i : Fin m) (j : Fin n), |dynDelta S s ω i j| ≤ R := by
  induction s with
  | zero =>
      exact ⟨fro (S.W0 - S.alg.Wstar), fun ω i j =>
        concentration_abs_entry_le_fro _ i j⟩
  | succ s ih =>
      obtain ⟨R, hR⟩ := ih
      refine ⟨R + p.h / B * ((m : ℝ) + 1), fun ω i j => ?_⟩
      have h := concentration_delta_sum p S s 1 ω
      simp only [Finset.range_one, Finset.sum_singleton, add_zero] at h
      rw [h, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      have hc : 0 ≤ p.h / (B : ℝ) := div_nonneg p.hh.le (Nat.cast_nonneg B)
      calc
        |dynDelta S s ω i j - p.h / B * dynUpd S s ω i j| ≤
            |dynDelta S s ω i j| + |p.h / B * dynUpd S s ω i j| := abs_sub _ _
        _ ≤ R + p.h / B * ((m : ℝ) + 1) := by
          refine add_le_add (hR ω i j) ?_
          rw [abs_mul, abs_of_nonneg hc]
          exact mul_le_mul_of_nonneg_left
            (concentration_dynUpd_bound S s ω i j) hc

private lemma concentration_bound_of_cont {m n : ℕ} (F : Mat m n → ℝ)
    (hF : Continuous F) (R : ℝ) :
    ∃ C : ℝ, ∀ X : Mat m n, (∀ i j, |X i j| ≤ R) → |F X| ≤ C := by
  have hK : IsCompact
      (Set.pi Set.univ fun _i : Fin m => Set.pi Set.univ fun _j : Fin n => Icc (-R) R :
        Set (Mat m n)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := F) hF.continuousOn
  refine ⟨C, fun X hX => ?_⟩
  have hmem : X ∈
      (Set.pi Set.univ fun _i : Fin m => Set.pi Set.univ fun _j : Fin n => Icc (-R) R :
        Set (Mat m n)) := by
    intro i _ j _
    exact abs_le.mp (hX i j)
  simpa using hC X hmem

private lemma concentration_Xfg_cont {m n : ℕ} (f g : ℝ → ℝ)
    (C : Covariances m n) : Continuous (Xfg f g C) := by
  unfold Xfg wfg frobIP
  fun_prop

private lemma concentration_Xfg_delta_integrable {p : DynParams} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ}
    (S : DynSetup p P m n B) (f g : ℝ → ℝ) (s : ℕ) :
    Integrable (fun ω => Xfg f g S.C (dynDelta S s ω)) P := by
  obtain ⟨R, hR⟩ := concentration_delta_entry_bdd S s
  obtain ⟨C, hC⟩ := concentration_bound_of_cont (Xfg f g S.C)
    (concentration_Xfg_cont f g S.C) R
  exact Integrable.of_bound (C := C)
    ((concentration_Xfg_cont f g S.C).measurable.comp
      ((concentration_delta_meas S s).mono (concentration_past_le S s) le_rfl)).aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa using hC (dynDelta S s ω) (hR ω))

private lemma concentration_blockIncr_integrable {p : DynParams} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ}
    (S : DynSetup p P m n B) (f g : ℝ → ℝ) (b : ℕ) :
    Integrable (blockIncr p f g S b) P :=
  (concentration_Xfg_delta_integrable S f g _).sub
    (concentration_Xfg_delta_integrable S f g _)

private lemma concentration_blockFiltration_exists {p : DynParams} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) :
    ∃ ℱ : Filtration ℕ mΩ, ∀ b, ℱ b = dynPast S (b * blockLen B) := by
  let ℱ : Filtration ℕ mΩ :=
    { seq := fun b => dynPast S (b * blockLen B)
      mono' := fun i j hij => concentration_past_mono S (Nat.mul_le_mul_right _ hij)
      le' := fun b => concentration_past_le S (b * blockLen B) }
  exact ⟨ℱ, fun b => rfl⟩

private lemma martingale_finset_partialSums {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (d : ℕ → Ω → ℝ) (hdmeas : ∀ b, StronglyMeasurable[ℱ (b + 1)] (d b))
    (hdint : ∀ b, Integrable (d b) P)
    (hcenter : ∀ b, condExp (ℱ b) P (d b) =ᵐ[P] 0) :
    Martingale (fun j ω => ∑ b ∈ Finset.range j, d b ω) ℱ P := by
  apply martingale_of_condExp_sub_eq_zero_nat
  · intro j
    apply Finset.stronglyMeasurable_fun_sum
    intro b hb
    exact (hdmeas b).mono (ℱ.mono (Nat.succ_le_iff.mpr (Finset.mem_range.mp hb)))
  · intro j
    exact integrable_finsetSum _ fun b _ => hdint b
  · intro j
    have hdiff : (fun ω => ∑ b ∈ Finset.range (j + 1), d b ω) -
        (fun ω => ∑ b ∈ Finset.range j, d b ω) = d j := by
      funext ω
      change (∑ b ∈ Finset.range (j + 1), d b ω) -
        ∑ b ∈ Finset.range j, d b ω = d j ω
      rw [Finset.sum_range_succ]
      ring
    rw [hdiff]
    exact hcenter j

private lemma memLp_finset_partialSums {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (d : ℕ → Ω → ℝ) (hd : ∀ b, MemLp (d b) 2 P) (j : ℕ) :
    MemLp (fun ω => ∑ b ∈ Finset.range j, d b ω) 2 P := by
  exact memLp_finsetSum _ fun b _ => hd b

private lemma integral_sq_finset_partialSums {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (d : ℕ → Ω → ℝ) (hdmeas : ∀ b, StronglyMeasurable[ℱ (b + 1)] (d b))
    (hd : ∀ b, MemLp (d b) 2 P)
    (hcenter : ∀ b, condExp (ℱ b) P (d b) =ᵐ[P] 0) (j : ℕ) :
    ∫ ω, (∑ b ∈ Finset.range j, d b ω) ^ 2 ∂P =
      ∑ b ∈ Finset.range j, ∫ ω, (d b ω) ^ 2 ∂P := by
  induction j with
  | zero => simp
  | succ j ih =>
    let M : Ω → ℝ := fun ω => ∑ b ∈ Finset.range j, d b ω
    have hMmem : MemLp M 2 P := memLp_finset_partialSums d hd j
    have hMsm : StronglyMeasurable[ℱ j] M := by
      apply Finset.stronglyMeasurable_fun_sum
      intro b hb
      exact (hdmeas b).mono (ℱ.mono (Nat.succ_le_iff.mpr (Finset.mem_range.mp hb)))
    have hprod : Integrable (M * d j) P := hMmem.integrable_mul (hd j)
    have hcross : ∫ ω, M ω * d j ω ∂P = 0 := by
      calc
        ∫ ω, M ω * d j ω ∂P = ∫ ω, condExp (ℱ j) P (M * d j) ω ∂P :=
          (integral_condExp (ℱ.le j)).symm
        _ = ∫ ω, M ω * condExp (ℱ j) P (d j) ω ∂P :=
          integral_congr_ae
            (condExp_mul_of_stronglyMeasurable_left hMsm hprod ((hd j).integrable one_le_two))
        _ = ∫ _ω, 0 ∂P := by
          apply integral_congr_ae
          filter_upwards [hcenter j] with ω hω
          simp only [Pi.zero_apply, hω, mul_zero]
        _ = 0 := by simp
    have hMsq : Integrable (fun ω => M ω ^ 2) P := hMmem.integrable_sq
    have hdsq : Integrable (fun ω => d j ω ^ 2) P := (hd j).integrable_sq
    have htwo : Integrable (fun ω => 2 * (M ω * d j ω)) P := hprod.const_mul 2
    have hsum : (fun ω => ∑ b ∈ Finset.range (j + 1), d b ω) =
        fun ω => M ω + d j ω := by
      funext ω
      rw [Finset.sum_range_succ]
    have hrsum : (∑ b ∈ Finset.range (j + 1), ∫ ω, d b ω ^ 2 ∂P) =
        (∑ b ∈ Finset.range j, ∫ ω, d b ω ^ 2 ∂P) + ∫ ω, d j ω ^ 2 ∂P := by
      rw [Finset.sum_range_succ]
    rw [hrsum, ← ih]
    simp_rw [Finset.sum_range_succ]
    change ∫ ω, (M ω + d j ω) ^ 2 ∂P =
      ∫ ω, M ω ^ 2 ∂P + ∫ ω, d j ω ^ 2 ∂P
    simp_rw [add_sq]
    simp_rw [mul_assoc]
    calc
      ∫ ω, M ω ^ 2 + 2 * (M ω * d j ω) + d j ω ^ 2 ∂P =
          ∫ ω, M ω ^ 2 + 2 * (M ω * d j ω) ∂P +
            ∫ ω, d j ω ^ 2 ∂P := integral_add (hMsq.add htwo) hdsq
      _ = (∫ ω, M ω ^ 2 ∂P) + (∫ ω, 2 * (M ω * d j ω) ∂P) +
            ∫ ω, d j ω ^ 2 ∂P := by rw [integral_add hMsq htwo]
      _ = _ := by rw [integral_const_mul, hcross, mul_zero, add_zero]

private lemma doob_finset_max_sq {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (M : ℕ → Ω → ℝ) (hM : Martingale M ℱ P)
    (hL2 : ∀ j, MemLp (M j) 2 P) (n : ℕ) :
    Integrable (fun ω => (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun j => (M j ω) ^ 2)) P ∧
    ∫ ω, (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun j => (M j ω) ^ 2) ∂P ≤ 4 * ∫ ω, (M n ω) ^ 2 ∂P := by
  classical
  let Z : Ω → ℝ := fun ω => (Finset.range (n + 1)).sup'
    Finset.nonempty_range_add_one (fun j => (M j ω) ^ 2)
  have hZmeas : Measurable Z :=
    Finset.measurable_range_sup'' (n := n) fun j _ =>
      ((hM.1 j).measurable.mono (ℱ.le j) le_rfl).pow_const 2
  have hZnonneg : ∀ ω, 0 ≤ Z ω := fun ω =>
    (sq_nonneg (M 0 ω)).trans
      (Finset.le_sup' (fun j => (M j ω) ^ 2) (by simp))
  have hZle : ∀ ω, Z ω ≤ ∑ j ∈ Finset.range (n + 1), (M j ω) ^ 2 := by
    intro ω
    change (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun j => (M j ω) ^ 2) ≤ ∑ j ∈ Finset.range (n + 1), (M j ω) ^ 2
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup'
      (s := Finset.range (n + 1)) Finset.nonempty_range_add_one
      (fun j => (M j ω) ^ 2)
    rw [hjeq]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (M k ω)) hj
  have hsumint : Integrable (fun ω => ∑ j ∈ Finset.range (n + 1), (M j ω) ^ 2) P :=
    integrable_finsetSum _ fun j _ => (hL2 j).integrable_sq
  have hZint : Integrable Z P := by
    apply Integrable.mono' hsumint hZmeas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hZnonneg ω)]
    exact hZle ω
  refine ⟨hZint, ?_⟩
  have hpoint (ω : Ω) : ENNReal.ofReal (Z ω) =
      ⨆ j ∈ Finset.range (n + 1), ENNReal.ofReal ((M j ω) ^ 2) := by
    change ENNReal.ofReal ((Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun j => (M j ω) ^ 2)) = _
    apply le_antisymm
    · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup'
        (s := Finset.range (n + 1)) Finset.nonempty_range_add_one
        (fun j => (M j ω) ^ 2)
      rw [hjeq]
      exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)
    · refine iSup₂_le fun j hj => ENNReal.ofReal_le_ofReal ?_
      exact Finset.le_sup' (fun k => (M k ω) ^ 2) hj
  have hdoob := Muon.Foundations.doob_L2 ℱ M hM hL2 n
  have hfun : (fun ω => ENNReal.ofReal (Z ω)) =
      (fun ω => ⨆ j ∈ Finset.range (n + 1), ENNReal.ofReal ((M j ω) ^ 2)) :=
    funext hpoint
  rw [← hfun, ← ofReal_integral_eq_lintegral_ofReal hZint (ae_of_all _ hZnonneg),
    ← ofReal_integral_eq_lintegral_ofReal (hL2 n).integrable_sq
      (ae_of_all _ fun ω => sq_nonneg (M n ω))] at hdoob
  have hright : 0 ≤ 4 * ∫ ω, (M n ω) ^ 2 ∂P :=
    mul_nonneg (by norm_num) (integral_nonneg fun ω => sq_nonneg (M n ω))
  apply (ENNReal.ofReal_le_ofReal_iff hright).mp
  rw [ENNReal.ofReal_mul (by norm_num)]
  simpa only [ENNReal.ofReal_ofNat] using hdoob

private lemma concentration_blockMartDiff_eq_indicator (p : DynParams)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (f g : ℝ → ℝ) (bstar : Ω → ℕ) (b : ℕ) :
    blockMartDiff p f g S bstar b = {ω | b < bstar ω}.indicator
      (blockIncr p f g S b -
        condExp (dynPast S (b * blockLen B)) P (blockIncr p f g S b)) := by
  funext ω
  by_cases hω : b < bstar ω <;> simp [blockMartDiff, Set.indicator, hω]

private lemma concentration_blockMartDiff_centered (p : DynParams)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n B : ℕ} (S : DynSetup p P m n B) (f g : ℝ → ℝ) (bstar : Ω → ℕ)
    (hbstar : ∀ b : ℕ, MeasurableSet[dynPast S (b * blockLen B)] {ω | b < bstar ω})
    (b : ℕ) :
    condExp (dynPast S (b * blockLen B)) P (blockMartDiff p f g S bstar b) =ᵐ[P] 0 := by
  have hY : Integrable (blockIncr p f g S b) P :=
    concentration_blockIncr_integrable S f g b
  have hEY : Integrable (condExp (dynPast S (b * blockLen B)) P
      (blockIncr p f g S b)) P := integrable_condExp
  have hdiff : Integrable (blockIncr p f g S b -
      condExp (dynPast S (b * blockLen B)) P (blockIncr p f g S b)) P := hY.sub hEY
  have hI : StronglyMeasurable[dynPast S (b * blockLen B)]
      (fun ω => if b < bstar ω then (1 : ℝ) else 0) := by
    exact (Measurable.ite (hbstar b) measurable_const measurable_const).stronglyMeasurable
  have hset : MeasurableSet {ω | b < bstar ω} :=
    (concentration_past_le S (b * blockLen B)) _ (hbstar b)
  have hprod : Integrable ((fun ω => if b < bstar ω then (1 : ℝ) else 0) *
      (blockIncr p f g S b - condExp (dynPast S (b * blockLen B)) P
        (blockIncr p f g S b))) P := by
    have hi := hdiff.indicator hset
    apply hi.congr
    filter_upwards [] with ω
    by_cases hω : b < bstar ω <;> simp [Set.indicator, hω]
  have hpull := condExp_mul_of_stronglyMeasurable_left hI hprod hdiff
  have hzero : condExp (dynPast S (b * blockLen B)) P
      (blockIncr p f g S b - condExp (dynPast S (b * blockLen B)) P
        (blockIncr p f g S b)) =ᵐ[P] 0 := by
    filter_upwards [condExp_sub hY hEY (dynPast S (b * blockLen B)),
      condExp_condExp_of_le (μ := P) (f := blockIncr p f g S b)
        (le_refl (dynPast S (b * blockLen B)))
        (concentration_past_le S (b * blockLen B))] with ω hsub htower
    simp only [Pi.sub_apply, hsub, htower, sub_self, Pi.zero_apply]
  have hresult : condExp (dynPast S (b * blockLen B)) P
      ((fun ω => if b < bstar ω then (1 : ℝ) else 0) *
        (blockIncr p f g S b - condExp (dynPast S (b * blockLen B)) P
          (blockIncr p f g S b))) =ᵐ[P] 0 := by
    filter_upwards [hpull, hzero] with ω hp hz
    simp only [Pi.mul_apply, hp, hz, mul_zero, Pi.zero_apply]
  rw [concentration_blockMartDiff_eq_indicator]
  have heq : {ω | b < bstar ω}.indicator
      (blockIncr p f g S b - condExp (dynPast S (b * blockLen B)) P
        (blockIncr p f g S b)) =
      (fun ω => if b < bstar ω then (1 : ℝ) else 0) *
        (blockIncr p f g S b - condExp (dynPast S (b * blockLen B)) P
          (blockIncr p f g S b)) := by
    funext ω
    by_cases hω : b < bstar ω <;> simp [Set.indicator, hω]
  rw [heq]
  exact hresult

private lemma concentration_blockMartDiff_memLp (p : DynParams)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n B : ℕ} (S : DynSetup p P m n B) (f g : ℝ → ℝ) (bstar : Ω → ℕ)
    (hbstar : ∀ b : ℕ, MeasurableSet[dynPast S (b * blockLen B)] {ω | b < bstar ω})
    (b : ℕ) : MemLp (blockMartDiff p f g S bstar b) 2 P := by
  let t0 := b * blockLen B
  let t1 := (b + 1) * blockLen B
  obtain ⟨R0, hR0⟩ := concentration_delta_entry_bdd S t0
  obtain ⟨R1, hR1⟩ := concentration_delta_entry_bdd S t1
  obtain ⟨C0, hC0⟩ := concentration_bound_of_cont (Xfg f g S.C)
    (concentration_Xfg_cont f g S.C) R0
  obtain ⟨C1, hC1⟩ := concentration_bound_of_cont (Xfg f g S.C)
    (concentration_Xfg_cont f g S.C) R1
  have hYsm : AEStronglyMeasurable (blockIncr p f g S b) P :=
    ((concentration_blockIncr_meas S f g b).mono
      (concentration_past_le S ((b + 1) * blockLen B)) le_rfl).aestronglyMeasurable
  have hYbdd : ∀ ω, ‖blockIncr p f g S b ω‖ ≤ C1 + C0 := by
    intro ω
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add
      (hC1 _ (by simpa only [t1] using hR1 ω))
      (hC0 _ (by simpa only [t0] using hR0 ω)))
  have hYmem : MemLp (blockIncr p f g S b) 2 P :=
    MemLp.of_bound hYsm (C1 + C0) (ae_of_all _ hYbdd)
  have hdiff : MemLp (blockIncr p f g S b -
      condExp (dynPast S (b * blockLen B)) P (blockIncr p f g S b)) 2 P :=
    hYmem.sub (hYmem.condExp one_le_two)
  have hset : MeasurableSet {ω | b < bstar ω} :=
    (concentration_past_le S (b * blockLen B)) _ (hbstar b)
  rw [concentration_blockMartDiff_eq_indicator]
  exact hdiff.indicator hset

private lemma concentration_blockIncr_memLp (p : DynParams)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n B : ℕ} (S : DynSetup p P m n B) (f g : ℝ → ℝ) (b : ℕ) :
    MemLp (blockIncr p f g S b) 2 P := by
  let t0 := b * blockLen B
  let t1 := (b + 1) * blockLen B
  obtain ⟨R0, hR0⟩ := concentration_delta_entry_bdd S t0
  obtain ⟨R1, hR1⟩ := concentration_delta_entry_bdd S t1
  obtain ⟨C0, hC0⟩ := concentration_bound_of_cont (Xfg f g S.C)
    (concentration_Xfg_cont f g S.C) R0
  obtain ⟨C1, hC1⟩ := concentration_bound_of_cont (Xfg f g S.C)
    (concentration_Xfg_cont f g S.C) R1
  have hYsm : AEStronglyMeasurable (blockIncr p f g S b) P :=
    ((concentration_blockIncr_meas S f g b).mono
      (concentration_past_le S ((b + 1) * blockLen B)) le_rfl).aestronglyMeasurable
  exact MemLp.of_bound hYsm (C1 + C0) (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add
      (hC1 _ (by simpa only [t1] using hR1 ω))
      (hC0 _ (by simpa only [t0] using hR0 ω))))

private lemma concentration_dynUpd_fro_bound (p : DynParams) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B)
    (ω : Ω) (t : ℕ) : fro (dynUpd S t ω) ≤ Real.sqrt (p.γstar * B) := by
  have hr : 0 ≤ riskSigma S.C (dynDelta S t ω) := by
    rw [eqn_app_setup_whitened_risk]
    positivity
  unfold dynUpd gtRand stepUpdate
  split_ifs
  · simp [fro]
    positivity
  · have hh : 0 ≤ 2 * riskSigma S.C (dynDelta S t ω) * S.alg.ϱ :=
      mul_nonneg (mul_nonneg (by norm_num) hr) S.alg.hϱ.le
    obtain ⟨_, hf, hk, _⟩ := lem_app_setup_filter_i _ hh
      (stepBuffer S.alg (runRand S.C S.alg (dynStart S) (dynBatch S) t ω)
        (dynBatch S t ω))
    have hmin : ((min m n : ℕ) : ℝ) ≤ p.γstar * B := by
      have hm : ((min m n : ℕ) : ℝ) ≤ ((max m n : ℕ) : ℝ) := by
        exact_mod_cast (min_le_max : min m n ≤ max m n)
      exact hm.trans S.size.1
    have hk' : ((stepBuffer S.alg (runRand S.C S.alg (dynStart S) (dynBatch S) t ω)
        (dynBatch S t ω)).rank : ℝ) ≤ ((min m n : ℕ) : ℝ) := by
      exact_mod_cast hk
    exact (Real.le_sqrt (Real.sqrt_nonneg _) (mul_nonneg p.hγ (Nat.cast_nonneg B))).mpr
      (hf.trans (hk'.trans hmin))

private lemma concentration_dynUpd_sum_fro_bound (p : DynParams) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B)
    (ω : Ω) (t : ℕ) :
    fro (∑ r ∈ Finset.range (blockLen B), dynUpd S (t + r) ω) ≤
      (blockLen B : ℝ) * Real.sqrt (p.γstar * B) := by
  open scoped Matrix.Norms.Frobenius in
    calc
      fro (∑ r ∈ Finset.range (blockLen B), dynUpd S (t + r) ω) ≤
          ∑ r ∈ Finset.range (blockLen B), fro (dynUpd S (t + r) ω) :=
        by simpa only [fro_eq_norm] using
          (norm_sum_le (Finset.range (blockLen B)) fun r => dynUpd S (t + r) ω)
      _ ≤ ∑ _r ∈ Finset.range (blockLen B), Real.sqrt (p.γstar * B) :=
        Finset.sum_le_sum fun r _ => concentration_dynUpd_fro_bound p S ω (t + r)
      _ = (blockLen B : ℝ) * Real.sqrt (p.γstar * B) := by simp

private lemma concentration_centered_indicator_sq_le {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (𝒢 : MeasurableSpace Ω) (h𝒢 : 𝒢 ≤ mΩ) (A : Set Ω) (hA : MeasurableSet[𝒢] A)
    (X : Ω → ℝ) (hX : MemLp X 2 P) :
    ∫ ω, (A.indicator (fun ω => X ω - condExp 𝒢 P X ω) ω) ^ 2 ∂P ≤
      ∫ ω, A.indicator (fun ω => X ω ^ 2) ω ∂P := by
  have hcenter : Integrable (fun ω => (X ω - condExp 𝒢 P X ω) ^ 2) P :=
    (hX.sub (hX.condExp one_le_two)).integrable_sq
  have hAm : @MeasurableSet Ω mΩ A := h𝒢 A hA
  have hcondvar := setIntegral_condVar (μ := P) (m := 𝒢) (hm := h𝒢) hcenter hA
  have hle := condVar_ae_le_condExp_sq h𝒢 hX
  have hcondint : Integrable (condExp 𝒢 P (X ^ 2)) P := integrable_condExp
  have hind : (fun ω => (A.indicator (fun ω => X ω - condExp 𝒢 P X ω) ω) ^ 2) =
      A.indicator (fun ω => (X ω - condExp 𝒢 P X ω) ^ 2) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
  calc
    ∫ ω, (A.indicator (fun ω => X ω - condExp 𝒢 P X ω) ω) ^ 2 ∂P =
        ∫ ω in A, (X ω - condExp 𝒢 P X ω) ^ 2 ∂P := by
      rw [hind]
      exact integral_indicator (μ := P) (f := fun ω =>
        (X ω - condExp 𝒢 P X ω) ^ 2) hAm
    _ = ∫ ω in A, Var[X; P | 𝒢] ω ∂P := hcondvar.symm
    _ ≤ ∫ ω in A, condExp 𝒢 P (X ^ 2) ω ∂P :=
      integral_mono_ae integrable_condVar.integrableOn hcondint.integrableOn
        (hle.filter_mono (ae_mono Measure.restrict_le_self))
    _ = ∫ ω in A, X ω ^ 2 ∂P := setIntegral_condExp h𝒢 hX.integrable_sq hA
    _ = ∫ ω, A.indicator (fun ω => X ω ^ 2) ω ∂P :=
      (integral_indicator (μ := P) (f := fun ω => X ω ^ 2) hAm).symm

private lemma concentration_centered_indicator_sq_le_of_cond {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (𝒢 : MeasurableSpace Ω) (h𝒢 : 𝒢 ≤ mΩ) (A : Set Ω) (hA : MeasurableSet[𝒢] A)
    (X : Ω → ℝ) (hX : MemLp X 2 P) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ᵐ ω ∂P, ω ∈ A →
      condExp 𝒢 P (fun ω' => (X ω' - condExp 𝒢 P X ω') ^ 2) ω ≤ R) :
    ∫ ω, (A.indicator (fun ω => X ω - condExp 𝒢 P X ω) ω) ^ 2 ∂P ≤ R := by
  have hAm : @MeasurableSet Ω mΩ A := h𝒢 A hA
  have hcenter : Integrable (fun ω => (X ω - condExp 𝒢 P X ω) ^ 2) P :=
    (hX.sub (hX.condExp one_le_two)).integrable_sq
  have hcond : Integrable (condExp 𝒢 P
      (fun ω => (X ω - condExp 𝒢 P X ω) ^ 2)) P := integrable_condExp
  have hind : (fun ω => (A.indicator (fun ω => X ω - condExp 𝒢 P X ω) ω) ^ 2) =
      A.indicator (fun ω => (X ω - condExp 𝒢 P X ω) ^ 2) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
  calc
    ∫ ω, (A.indicator (fun ω => X ω - condExp 𝒢 P X ω) ω) ^ 2 ∂P =
        ∫ ω in A, (X ω - condExp 𝒢 P X ω) ^ 2 ∂P := by
      rw [hind]
      exact integral_indicator (μ := P) (f := fun ω =>
        (X ω - condExp 𝒢 P X ω) ^ 2) hAm
    _ = ∫ ω in A, condExp 𝒢 P
        (fun ω' => (X ω' - condExp 𝒢 P X ω') ^ 2) ω ∂P :=
      (setIntegral_condExp h𝒢 hcenter hA).symm
    _ ≤ ∫ _ω in A, R ∂P := by
      apply integral_mono_ae hcond.integrableOn integrableOn_const
      exact (ae_restrict_iff' (μ := P) hAm).2 hbound
    _ = P.real A * R := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ R := by
      nlinarith [(measureReal_nonneg : 0 ≤ P.real A), measureReal_le_one (μ := P) (s := A)]

private lemma concentration_quadratic_term_bound (p : DynParams)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n B : ℕ} (S : DynSetup p P m n B) (f g : ℝ → ℝ)
    (hf : ∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1)
    (hg : ∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1)
    (hB : 0 < B) (t : ℕ) :
    let Z : Ω → ℝ := fun ω =>
      (p.h / (B : ℝ)) ^ 2 *
        frobIP (∑ r ∈ Finset.range (blockLen B), dynUpd S (t + r) ω)
          (wfg f g S.C (∑ r ∈ Finset.range (blockLen B), dynUpd S (t + r) ω))
    MemLp Z 2 P ∧
      ∫ ω, Z ω ^ 2 ∂P ≤
        p.h ^ 4 * p.γstar ^ 2 * (blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 := by
  dsimp only
  let U : Ω → Mat m n := fun ω =>
    ∑ r ∈ Finset.range (blockLen B), dynUpd S (t + r) ω
  have hU : Measurable U := by
    apply Finset.measurable_sum
    intro r hr
    exact (concentration_upd_meas S (t + r)).mono
      (concentration_past_le S (t + r + 1)) le_rfl
  have hZ : Measurable (fun ω =>
      (p.h / (B : ℝ)) ^ 2 * frobIP (U ω) (wfg f g S.C (U ω))) := by
    have hc : Continuous (fun X : Mat m n => frobIP X (wfg f g S.C X)) := by
      unfold frobIP wfg
      fun_prop
    exact measurable_const.mul (hc.measurable.comp hU)
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hpoint : ∀ ω, |(p.h / (B : ℝ)) ^ 2 *
      frobIP (U ω) (wfg f g S.C (U ω))| ≤
      p.h ^ 2 * p.γstar * (blockLen B : ℝ) ^ 2 / (B : ℝ) := by
    intro ω
    have hW := concentration_wfg_fro_le f g S.C hf hg S.size.2.1 S.size.2.2 (U ω)
    have hIP := projection_frobIP_le (U ω) (wfg f g S.C (U ω))
    have hUb := concentration_dynUpd_sum_fro_bound p S ω t
    have hγB : 0 ≤ p.γstar * (B : ℝ) := mul_nonneg p.hγ (Nat.cast_nonneg B)
    have hsqrt : (Real.sqrt (p.γstar * (B : ℝ))) ^ 2 = p.γstar * (B : ℝ) :=
      Real.sq_sqrt hγB
    rw [abs_mul]
    have hpair : |frobIP (U ω) (wfg f g S.C (U ω))| ≤ fro (U ω) ^ 2 := by
      calc
        _ ≤ fro (U ω) * fro (wfg f g S.C (U ω)) := hIP
        _ ≤ fro (U ω) * fro (U ω) :=
          mul_le_mul_of_nonneg_left hW (Real.sqrt_nonneg _)
        _ = fro (U ω) ^ 2 := by ring
    have hUsq : fro (U ω) ^ 2 ≤
        (blockLen B : ℝ) ^ 2 * (p.γstar * (B : ℝ)) := by
      calc
        fro (U ω) ^ 2 = fro (U ω) * fro (U ω) := by ring
        _ ≤ ((blockLen B : ℝ) * Real.sqrt (p.γstar * (B : ℝ))) *
            ((blockLen B : ℝ) * Real.sqrt (p.γstar * (B : ℝ))) :=
          mul_self_le_mul_self (Real.sqrt_nonneg _) hUb
        _ = (blockLen B : ℝ) ^ 2 * (p.γstar * (B : ℝ)) := by
          calc
            _ = (blockLen B : ℝ) ^ 2 *
                (Real.sqrt (p.γstar * (B : ℝ))) ^ 2 := by ring
            _ = _ := by rw [hsqrt]
    calc
      |(p.h / (B : ℝ)) ^ 2| * |frobIP (U ω) (wfg f g S.C (U ω))| ≤
          (p.h / (B : ℝ)) ^ 2 * fro (U ω) ^ 2 := by
            rw [abs_of_nonneg (sq_nonneg _)]
            exact mul_le_mul_of_nonneg_left hpair (sq_nonneg _)
      _ ≤ (p.h / (B : ℝ)) ^ 2 *
          ((blockLen B : ℝ) ^ 2 * (p.γstar * (B : ℝ))) :=
        mul_le_mul_of_nonneg_left hUsq (sq_nonneg _)
      _ = p.h ^ 2 * p.γstar * (blockLen B : ℝ) ^ 2 / (B : ℝ) := by
        field_simp
  have hZmem : MemLp (fun ω =>
      (p.h / (B : ℝ)) ^ 2 * frobIP (U ω) (wfg f g S.C (U ω))) 2 P :=
    MemLp.of_bound hZ.aestronglyMeasurable _ (ae_of_all _ hpoint)
  refine ⟨hZmem, ?_⟩
  have hsquare : ∀ ω, ((p.h / (B : ℝ)) ^ 2 *
      frobIP (U ω) (wfg f g S.C (U ω))) ^ 2 ≤
      (p.h ^ 2 * p.γstar * (blockLen B : ℝ) ^ 2 / (B : ℝ)) ^ 2 := by
    intro ω
    rw [← sq_abs]
    have hR : 0 ≤ p.h ^ 2 * p.γstar * (blockLen B : ℝ) ^ 2 / (B : ℝ) := by
      exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) p.hγ) (sq_nonneg _)) hBr.le
    simpa only [pow_two] using mul_self_le_mul_self (abs_nonneg _) (hpoint ω)
  calc
    ∫ ω, ((p.h / (B : ℝ)) ^ 2 *
        frobIP (U ω) (wfg f g S.C (U ω))) ^ 2 ∂P ≤
        ∫ _ω, (p.h ^ 2 * p.γstar * (blockLen B : ℝ) ^ 2 / (B : ℝ)) ^ 2 ∂P :=
      integral_mono (hZmem.integrable_sq) (by fun_prop) hsquare
    _ = p.h ^ 4 * p.γstar ^ 2 * (blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 := by
      simp only [integral_const, probReal_univ, one_smul]
      ring

private lemma cpb_indep_sup {Ω : Type*} (A M F G : MeasurableSpace Ω)
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

private lemma cpb_indep_past_future {p : DynParams} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) :
    Indep (dynPast S t) (chainFuture S.cs t) P := by
  refine cpb_indep_sup _ _ _
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

private lemma cpb_frobIP_eq_sum {m n : ℕ} (T M : Mat m n) :
    frobIP T M = ∑ i, ∑ j, T i j * M i j := by
  simp only [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]

private lemma cpb_statV_fro_sq {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t r : ℕ) (D : Mat m n)
    (ω : Ω) : fro (stationaryV p C cs t D r ω) ^ 2 ≤ ((min m n : ℕ) : ℝ) := by
  have hridge : 0 ≤ physRidge p C D := by
    unfold physRidge
    have := concentration_risk_nonneg C D
    have := p.hϱ
    positivity
  have hfilter := lem_app_setup_filter_i _ hridge (stationaryN p C cs t D r ω)
  have hrank : ((stationaryN p C cs t D r ω).rank : ℝ) ≤ ((min m n : ℕ) : ℝ) :=
    Nat.cast_le.mpr hfilter.2.2.1
  exact hfilter.2.1.trans hrank


private lemma cpb_risk_comp_meas {Ω : Type*} {σ : MeasurableSpace Ω} {m n : ℕ}
    (C : Covariances m n) {D : Ω → Mat m n} (hD : Measurable[σ] D) :
    Measurable[σ] (fun ω => riskSigma C (D ω)) :=
  (show Continuous (fun D : Mat m n => riskSigma C D) by
    unfold riskSigma pairSigma
    fun_prop).measurable.comp hD

private lemma cpb_phys_meas {Ω : Type*} [MeasurableSpace Ω] {m n B : ℕ}
    (C : Covariances m n) {z : Fin B → Ω → Vec m × Vec n} (hz : ∀ a, Measurable (z a)) :
    Measurable (fun ω => physBatch C z ω) := by
  refine measurable_pi_iff.mpr (fun a => ?_)
  exact (show Continuous (fun z : Vec m × Vec n => phys C z) by
    unfold phys
    fun_prop).measurable.comp (hz a)

set_option maxHeartbeats 1000000 in
private lemma cpb_ema_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ)
    {D : Ω → Mat m n} (hD : Measurable D) {init : Ω → Mat m n} (hinit : Measurable init)
    (k : ℕ) :
    Measurable (fun ω => emaChain p.β (D ω) (fun s => physBatch S.C (S.cs.act s) ω) t (init ω) k) := by
  induction k with
  | zero => simpa [emaChain] using hinit
  | succ k ih =>
    have hb : Measurable (fun ω => batchGrad (D ω)
        (physBatch S.C (S.cs.act ((t : ℤ) + k + 1)) ω)) :=
      concentration_grad_meas hD (cpb_phys_meas S.C (fun a => S.cs.meas_act _ a))
    simp only [emaChain]
    exact (ih.const_smul p.β).add (hb.const_smul (1 - p.β))

set_option maxHeartbeats 1000000 in
private lemma cpb_chainInit_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
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
  exact concentration_grad_meas hD (cpb_phys_meas S.C (fun a => S.cs.meas_aux _ j a))

private lemma cpb_Q_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B)
    {D : Ω → Mat m n} (hD : Measurable D) {M : Ω → Mat m n} (hM : Measurable M) :
    Measurable (fun ω => Q (physRidge p S.C (D ω)) (M ω)) := by
  have hρ : ∀ ω, 0 ≤ physRidge p S.C (D ω) := fun ω => by
    unfold physRidge
    exact mul_nonneg (mul_nonneg (by norm_num)
      (by rw [eqn_app_setup_whitened_risk]; positivity)) p.hϱ.le
  have hρm : Measurable (fun ω => (⟨physRidge p S.C (D ω), hρ ω⟩ : Set.Ici (0 : ℝ))) :=
    (((cpb_risk_comp_meas S.C hD).const_mul 2).mul_const p.ϱ).subtype_mk
  exact measurable_Q.comp (hρm.prodMk hM)

set_option maxHeartbeats 1000000 in
-- Elaborating the two freezing identities requires the full matrix-valued stationary path.
/-- Coordinator bridge (no source label), snapshot `cr-2026-10-23`. The conditional form of
`lem:app-dyn-poincare` (second display) at the random state `D = Δ_t` with the random test `T = 𝒯(Δ_t)`: on
`{Δ_t ∈ 𝒦}`, `Var_t⟨𝒯(Δ_t), ∑_{r<L} V_r⟩ ≤ C L² log²(2B) ‖𝒯(Δ_t)‖_F²`, where `(V_r)` is the stationary chain at
`(t, Δ_t)` (`dynStatSum`) and `Var_t` is the conditional variance given `𝓕_t`, written
`𝔼_t[(Y − 𝔼_t Y)²]` with `Y = 𝟙_{Δ_t ∈ 𝒦}⟨𝒯(Δ_t), ∑_{r<L}V_r⟩`. The consumer takes `𝒯 = 𝒲_{f,g}` (`wfg`), with
`‖𝒲_{f,g}X‖_F ≤ ‖X‖_F` for `‖f‖_∞, ‖g‖_∞ ≤ 1`, and `𝒦 = 𝒜`.
Source, `section.tex` ll. 1811–1815 (proof of `lem:app-dyn-martingale`), verbatim:
```latex
$\EE_t\xi_b^2\le3\big(4\lr^2\Var_t\langle\mathcal WD,S\rangle+4\lr^2\EE_t\langle\mathcal WD,\mathcal E\rangle^2+\lr^4\EE_t\langle\Sigma_{\mathsf S},\mathcal W\Sigma_{\mathsf S}\rangle^2\big)$.

The three terms are bounded as follows. By \cref{lem:app-dyn-poincare},
conditionally on $\cF_t$ with $T=\mathcal WD$ and $\norm{\mathcal WD}_\F\le\norm D_\F\le C$,
the first is at most $C\lr^2L^2\log^2(2B)$.
```
and `lem:app-dyn-poincare` (ll. 1713–1721): "Let $D$ be deterministic with $r_-\le\cR(D)\le r_+$ … $\Var\Big\langle
T,\sum_{r<L}V_r\Big\rangle\le CL^2\log^2(2B)\norm T_\F^2$. No bound on $\norm T$ and no diffuseness of $D$ is
assumed." Proof route: `stationary_freezing_condExp` with `Φ₁(D, x) = 𝟙_𝒦(D)⟨𝒯D, ∑_{r<L}x_r⟩` and `Φ₂ = Φ₁²`
gives `𝔼_tY` and `𝔼_tY²` as frozen expectations; `𝔼_t[(Y − 𝔼_tY)²] = 𝔼_tY² − (𝔼_tY)²`, which at the frozen
`D = Δ_t(ω) ∈ 𝒦` is `variance ⟨𝒯D, ∑_{r<L}V_r⟩`, bounded by `lem_app_dyn_poincare_ii`. The constant `K` is that of
`lem_app_dyn_poincare_ii` (it depends on `p, r₋, r₊` and not on `E` or `𝒯`); `E` enters only the `MemLp` conjunct. 
Relocated here from `Muon.Dynamics.Freezing` by the coordinator (2026-10-24): its proof needs results of this
module, which imports the original one. -/
theorem cond_poincare_block (certP : Muon.External.GaussianPoincare) (certOp : Muon.External.GaussianOpNormL6)
    (p : DynParams) (rlo rhi : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ K : ℝ, ∀ (E : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B) (t : ℕ) (𝒯 : Mat m n → Mat m n),
      Measurable 𝒯 → (∀ X : Mat m n, fro (𝒯 X) ≤ fro X) →
      MemLp ((dynInK S t (rlo, rhi, E)).indicator
          (fun ω => frobIP (𝒯 (dynDelta S t ω)) (dynStatSum p S t ω))) 2 P ∧
      ∀ᵐ ω ∂P, ω ∈ dynInK S t (rlo, rhi, E) →
        condExp (dynPast S t) P (fun ω' =>
            ((dynInK S t (rlo, rhi, E)).indicator
                (fun ω => frobIP (𝒯 (dynDelta S t ω)) (dynStatSum p S t ω)) ω' -
              condExp (dynPast S t) P ((dynInK S t (rlo, rhi, E)).indicator
                (fun ω => frobIP (𝒯 (dynDelta S t ω)) (dynStatSum p S t ω))) ω') ^ 2) ω ≤
          K * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * fro (𝒯 (dynDelta S t ω)) ^ 2 := by
  classical
  obtain ⟨K, hK⟩ := lem_app_dyn_poincare_ii p rlo rhi hrlo hle certP certOp
  refine ⟨K, ?_⟩
  intro E Ω mΩ P hP m n B S t 𝒯 h𝒯 h𝒯bound
  let 𝒦 := admSetOf S.C (rlo, rhi, E)
  let Φ : Mat m n → (ℕ → Mat m n) → ℝ := fun D x =>
    if D ∈ 𝒦 then frobIP (𝒯 D) (∑ r ∈ Finset.range (blockLen B), x r) else 0
  have hΦ : Measurable (Function.uncurry Φ) := by
    have hpair : Measurable (fun z : Mat m n × (ℕ → Mat m n) =>
        frobIP (𝒯 z.1) (∑ r ∈ Finset.range (blockLen B), z.2 r)) := by
      simp only [cpb_frobIP_eq_sum, Matrix.sum_apply]
      refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
      refine (concentration_entry_meas (h𝒯.comp measurable_fst) i j).mul ?_
      refine Finset.measurable_sum _ fun r _ => ?_
      have hxr : Measurable (fun z : Mat m n × (ℕ → Mat m n) => z.2 r) :=
        (measurable_pi_apply r).comp measurable_snd
      exact concentration_entry_meas hxr i j
    exact Measurable.ite (measurable_fst (concentration_admSet_meas S.C (rlo, rhi, E)))
      hpair measurable_const
  have h𝓕 : dynPast S t ≤ mΩ := concentration_past_le S t
  have hD := concentration_delta_meas S t
  have hDm : Measurable (dynDelta S t) := hD.mono h𝓕 le_rfl
  have hpath : Measurable (fun ω r => stationaryV p S.C S.cs t (dynDelta S t ω) r ω) := by
    refine measurable_pi_iff.mpr fun r => ?_
    exact cpb_Q_meas S hDm (cpb_ema_meas S t hDm (cpb_chainInit_meas S t hDm) (r + 1))
  let Y : Ω → ℝ := fun ω => Φ (dynDelta S t ω)
    (fun r => stationaryV p S.C S.cs t (dynDelta S t ω) r ω)
  have hY : (dynInK S t (rlo, rhi, E)).indicator
      (fun ω => frobIP (𝒯 (dynDelta S t ω)) (dynStatSum p S t ω)) = Y := by
    rfl
  have hYm := hΦ.comp (hDm.prodMk hpath)
  have hYbound : ∀ ω, ‖Y ω‖ ≤
      (blockLen B : ℝ) * ((max E 0 + 1) * (((min m n : ℕ) : ℝ) + 1)) := by
    intro ω
    dsimp [Y, Φ]
    split_ifs with hω
    · rw [frobIP_sum_right]
      have hDb : fro (dynDelta S t ω) ≤ max E 0 + 1 := by
        have hsq : fro (dynDelta S t ω) ^ 2 ≤ max E 0 :=
          hω.2.2.trans (le_max_left _ _)
        nlinarith [sq_nonneg (fro (dynDelta S t ω) - 1)]
      calc
        |∑ r ∈ Finset.range (blockLen B),
            frobIP (𝒯 (dynDelta S t ω)) (stationaryV p S.C S.cs t (dynDelta S t ω) r ω)|
            ≤ ∑ r ∈ Finset.range (blockLen B),
              |frobIP (𝒯 (dynDelta S t ω)) (stationaryV p S.C S.cs t (dynDelta S t ω) r ω)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _r ∈ Finset.range (blockLen B),
            (max E 0 + 1) * (((min m n : ℕ) : ℝ) + 1) := by
          refine Finset.sum_le_sum fun r _ => ?_
          have hV : fro (stationaryV p S.C S.cs t (dynDelta S t ω) r ω) ≤
              ((min m n : ℕ) : ℝ) + 1 := by
            have hsq := cpb_statV_fro_sq p S.C S.cs t r (dynDelta S t ω) ω
            nlinarith [sq_nonneg (fro (stationaryV p S.C S.cs t (dynDelta S t ω) r ω) - 1)]
          exact (projection_frobIP_le _ _).trans
            (mul_le_mul ((h𝒯bound _).trans hDb) hV (Real.sqrt_nonneg _) (by positivity))
        _ = _ := by simp
    · simp only [abs_zero]
      positivity
  have hmem : MemLp Y 2 P := MemLp.of_bound hYm.aestronglyMeasurable _ (ae_of_all _ hYbound)
  have hind := cpb_indep_past_future S t
  have hF1 := stationary_freezing_condExp (dynPast S t) p S.C S.cs t h𝓕 hind
    (dynDelta S t) hD Φ hΦ (hmem.integrable one_le_two)
  let Φ₂ : Mat m n → (ℕ → Mat m n) → ℝ := fun D x => Φ D x ^ 2
  have hΦ₂ : Measurable (Function.uncurry Φ₂) := hΦ.pow_const 2
  have hF2 := stationary_freezing_condExp (dynPast S t) p S.C S.cs t h𝓕 hind
    (dynDelta S t) hD Φ₂ hΦ₂ hmem.integrable_sq
  have hCV := condVar_ae_eq_condExp_sq_sub_sq_condExp h𝓕 hmem
  rw [hY]
  refine ⟨hmem, ?_⟩
  change ∀ᵐ ω ∂P, ω ∈ dynInK S t (rlo, rhi, E) →
    condVar (dynPast S t) Y P ω ≤ _
  filter_upwards [hCV, hF1, hF2] with ω hcv hf1 hf2
  intro hω
  have hDmem : dynDelta S t ω ∈ 𝒦 := hω
  obtain ⟨hZmem, hZvar⟩ := hK Ω P m n B S t (dynDelta S t ω)
    (𝒯 (dynDelta S t ω)) hDmem.1 hDmem.2.1
  rw [hcv]
  change condExp (dynPast S t) P (Y ^ 2) ω - (condExp (dynPast S t) P Y ω) ^ 2 ≤ _
  change condExp (dynPast S t) P (Y ^ 2) ω = _ at hf2
  change condExp (dynPast S t) P Y ω = _ at hf1
  rw [hf2, hf1]
  simp only [Φ₂, Φ, if_pos hDmem]
  exact (variance_eq_sub hZmem).symm.trans_le hZvar

private lemma concentration_stationary_term_bound
    (certP : Muon.External.GaussianPoincare) (certOp : Muon.External.GaussianOpNormL6)
    (p : DynParams) :
    ∃ C : ℝ, ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (m n B : ℕ)
      (S : DynSetup p P m n B) (f g : ℝ → ℝ) (I : Set Ω) (b : ℕ),
      (∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1) →
      (∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1) →
      MeasurableSet[dynPast S (b * blockLen B)] I →
      (∀ ω ∈ I, dynDelta S (b * blockLen B) ω ∈ admA p S.C) →
      let K := dynInK S (b * blockLen B) (admBase p)
      let Q : Ω → ℝ := K.indicator (fun ω =>
        -2 * (p.h / (B : ℝ)) *
          frobIP (wfg f g S.C (dynDelta S (b * blockLen B) ω))
            (dynStatSum p S (b * blockLen B) ω))
      MemLp Q 2 P ∧
        ∫ ω, (I.indicator (fun ω =>
          Q ω - condExp (dynPast S (b * blockLen B)) P Q ω) ω) ^ 2 ∂P ≤
          C * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) ^ 2 := by
  let rlo := p.r0 / 2
  let rhi := p.r1 + 1 / 2
  let E := p.Estar + 1
  have hrlo : 0 < rlo := by dsimp [rlo]; linarith [p.hr0]
  have hle : rlo ≤ rhi := by dsimp [rlo, rhi]; linarith [p.hr, p.hr0]
  obtain ⟨KP, hKP⟩ := cond_poincare_block certP certOp p rlo rhi hrlo hle
  refine ⟨4 * p.h ^ 2 * max KP 0 * E, ?_⟩
  intro Ω mΩ P hP m n B S f g I b hf hg hI hIK
  dsimp only
  let t := b * blockLen B
  let K := dynInK S t (admBase p)
  let q : Ω → ℝ := fun ω =>
    frobIP (wfg f g S.C (dynDelta S t ω)) (dynStatSum p S t ω)
  let qK : Ω → ℝ := K.indicator q
  have hTmeas : Measurable (wfg f g S.C) := by
    have hc : Continuous (fun X : Mat m n => wfg f g S.C X) := by
      unfold wfg
      fun_prop
    exact hc.measurable
  have hTcontract : ∀ X : Mat m n, fro (wfg f g S.C X) ≤ fro X :=
    concentration_wfg_fro_le f g S.C hf hg S.size.2.1 S.size.2.2
  have hpoin := hKP E Ω P m n B S t (wfg f g S.C) hTmeas hTcontract
  have hqmem : MemLp qK 2 P := by
    simpa only [K, qK, q, t, rlo, rhi, E, admBase] using hpoin.1
  have hIambient : MeasurableSet I :=
    (concentration_past_le S t) I (by simpa only [t] using hI)
  have hbase : ∫ ω, (I.indicator (fun ω =>
      qK ω - condExp (dynPast S t) P qK ω) ω) ^ 2 ∂P ≤
      max KP 0 * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 * E := by
    apply concentration_centered_indicator_sq_le_of_cond
      (dynPast S t) (concentration_past_le S t) I (by simpa only [t] using hI)
      qK hqmem _ (by
        exact mul_nonneg (mul_nonneg (mul_nonneg (le_max_right KP 0) (sq_nonneg _))
          (sq_nonneg _)) (by dsimp [E]; linarith [p.hE]))
    filter_upwards [hpoin.2] with ω hω hωI
    have hωK : ω ∈ K := by
      change dynDelta S t ω ∈ admSetOf S.C (admBase p)
      simpa only [t, admA] using hIK ω hωI
    have hbound := hω hωK
    have hD := hIK ω hωI
    have hDf : fro (dynDelta S t ω) ^ 2 ≤ E := by
      simpa only [t, E, admA, admBase, admSetOf, Set.mem_setOf_eq] using hD.2.2
    have hW := hTcontract (dynDelta S t ω)
    have hWsq : fro (wfg f g S.C (dynDelta S t ω)) ^ 2 ≤ E := by
      have hW0 : 0 ≤ fro (wfg f g S.C (dynDelta S t ω)) := Real.sqrt_nonneg _
      have hD0 : 0 ≤ fro (dynDelta S t ω) := Real.sqrt_nonneg _
      calc
        fro (wfg f g S.C (dynDelta S t ω)) ^ 2 ≤ fro (dynDelta S t ω) ^ 2 := by
          nlinarith [sq_nonneg (fro (wfg f g S.C (dynDelta S t ω)) +
            fro (dynDelta S t ω))]
        _ ≤ E := hDf
    have hfac : 0 ≤ (blockLen B : ℝ) ^ 2 *
        Real.log (2 * (B : ℝ)) ^ 2 := by positivity
    have hKPle : KP * ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2) *
        fro (wfg f g S.C (dynDelta S t ω)) ^ 2 ≤
        max KP 0 * ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2) * E := by
      have hKE : 0 ≤ E := by dsimp [E]; linarith [p.hE]
      gcongr
      exact le_max_left _ _
    simpa only [qK, q, K, t, rlo, rhi, E, admBase, mul_assoc] using
      hbound.trans (by simpa only [mul_assoc] using hKPle)
  let c : ℝ := -2 * (p.h / (B : ℝ))
  have hQmem : MemLp (fun ω => c * qK ω) 2 P := hqmem.const_mul c
  have hscaled : K.indicator (fun ω => c * q ω) = (fun ω => c * qK ω) := by
    funext ω
    by_cases hω : ω ∈ K <;> simp [qK, Set.indicator, hω]
  have hQmem' : MemLp (K.indicator (fun ω => c * q ω)) 2 P := by
    rw [hscaled]
    exact hQmem
  refine ⟨by simpa only [c, q, K, t, mul_assoc] using hQmem', ?_⟩
  have hcond := condExp_smul (μ := P) c qK (dynPast S t)
  have hcond' : condExp (dynPast S t) P (fun ω => c * qK ω) =ᵐ[P]
      (fun ω => c * condExp (dynPast S t) P qK ω) := by
    have hfun : (c • qK) = (fun ω => c * qK ω) := rfl
    have hfun' : (c • condExp (dynPast S t) P qK) =
        (fun ω => c * condExp (dynPast S t) P qK ω) := rfl
    rw [← hfun, ← hfun']
    exact hcond
  have heq : (fun ω => (I.indicator (fun ω =>
      c * qK ω - condExp (dynPast S t) P (fun ω => c * qK ω) ω) ω) ^ 2) =ᵐ[P]
      (fun ω => c ^ 2 * (I.indicator (fun ω =>
        qK ω - condExp (dynPast S t) P qK ω) ω) ^ 2) := by
    filter_upwards [hcond'] with ω hω
    by_cases hωI : ω ∈ I <;> simp [Set.indicator, hωI, hω, Pi.smul_apply]
    ring
  have hscaled' : K.indicator (fun ω =>
      -2 * (p.h / (B : ℝ)) * q ω) = (fun ω => c * qK ω) := by
    simpa only [c, mul_assoc] using hscaled
  rw [show K.indicator (fun ω =>
      -2 * (p.h / (B : ℝ)) * q ω) = (fun ω => c * qK ω) from hscaled']
  calc
    ∫ ω, (I.indicator (fun ω =>
        c * qK ω - condExp (dynPast S t) P (fun ω => c * qK ω) ω) ω) ^ 2 ∂P =
        c ^ 2 * ∫ ω, (I.indicator (fun ω =>
          qK ω - condExp (dynPast S t) P qK ω) ω) ^ 2 ∂P := by
      rw [integral_congr_ae heq, integral_const_mul]
    _ ≤ c ^ 2 * (max KP 0 * (blockLen B : ℝ) ^ 2 *
        Real.log (2 * (B : ℝ)) ^ 2 * E) :=
      mul_le_mul_of_nonneg_left hbase (sq_nonneg c)
    _ = (4 * p.h ^ 2 * max KP 0 * E) * (blockLen B : ℝ) ^ 2 *
        Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) ^ 2 := by
      by_cases hB0 : (B : ℝ) = 0
      · simp [c, hB0]
      · dsimp only [c]
        field_simp [hB0]
        ring

private lemma concentration_error_term_bound
    (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∃ B0 : ℕ, ∃ C : ℝ, ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (m n B : ℕ)
      (S : DynSetup p P m n B) (f g : ℝ → ℝ) (I : Set Ω) (b : ℕ),
      B0 ≤ B →
      (∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1) →
      (∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1) →
      MeasurableSet[dynPast S (b * blockLen B)] I →
      (∀ ω ∈ I, dynDelta S (b * blockLen B) ω ∈ admA p S.C) →
      (∀ ω ∈ I, ((b * blockLen B : ℕ) : ℕ∞) ≤ tauPlus p S ω) →
      MemLp ((dynInK S (b * blockLen B) (admBase p)).indicator (fun ω =>
        -2 * (p.h / (B : ℝ)) *
          frobIP (wfg f g S.C (dynDelta S (b * blockLen B) ω))
            (dynStatSum p S (b * blockLen B) ω))) 2 P →
      let K := dynInK S (b * blockLen B) (admBase p)
      let Q : Ω → ℝ := K.indicator (fun ω =>
        -2 * (p.h / (B : ℝ)) *
          frobIP (wfg f g S.C (dynDelta S (b * blockLen B) ω))
            (dynSumErr p S (b * blockLen B) ω))
      MemLp Q 2 P ∧
        ∫ ω, (I.indicator (fun ω =>
          Q ω - condExp (dynPast S (b * blockLen B)) P Q ω) ω) ^ 2 ∂P ≤
          C * ((blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) := by
  let rlo := p.r0 / 2
  let rhi := p.r1 + 1 / 2
  let E := p.Estar + 1
  have hrlo : 0 < rlo := by dsimp [rlo]; linarith [p.hr0]
  have hle : rlo ≤ rhi := by dsimp [rlo, rhi]; linarith [p.hr, p.hr0]
  obtain ⟨Bcouple, KC, hcouple⟩ :=
    lem_app_dyn_coupling_iii certOp p rlo rhi E hrlo hle
  let rlo' := rlo / 2
  let rhi' := 2 * rhi
  let E' := 2 * E + 2
  have hrlo' : 0 < rlo' := by dsimp [rlo']; positivity
  have hle' : rlo' ≤ rhi' := by dsimp [rlo', rhi']; linarith [hrlo, hle]
  let Cbuf := 2 * p.cM + 4 * cMConst p.CSig p.γstar * rhi'
  let C := 4 * p.h ^ 2 * E * max KC 0 * (2 + Cbuf)
  refine ⟨max Bcouple 1, C, ?_⟩
  intro Ω mΩ P hP m n B S f g I b hB hf hg hI hIK hstop hstat
  dsimp only
  let t := b * blockLen B
  let K := dynInK S t (admBase p)
  let Y : Ω → ℝ := blockIncr p f g S b
  let A : Ω → ℝ := fun ω =>
    -2 * (p.h / (B : ℝ)) *
      frobIP (wfg f g S.C (dynDelta S t ω)) (dynStatSum p S t ω)
  let R : Ω → ℝ := fun ω =>
    -2 * (p.h / (B : ℝ)) *
      frobIP (wfg f g S.C (dynDelta S t ω)) (dynSumErr p S t ω)
  let Z : Ω → ℝ := fun ω =>
    (p.h / (B : ℝ)) ^ 2 *
      frobIP (∑ r ∈ Finset.range (blockLen B), dynUpd S (t + r) ω)
        (wfg f g S.C (∑ r ∈ Finset.range (blockLen B), dynUpd S (t + r) ω))
  have hBcouple : Bcouple ≤ B := (le_max_left _ _).trans hB
  have hBone : 1 ≤ B := (le_max_right _ _).trans hB
  have hBpos : 0 < B := lt_of_lt_of_le Nat.zero_lt_one hBone
  have hKmeas : MeasurableSet[dynPast S t] K := by
    exact (concentration_delta_meas S t) (concentration_admSet_meas S.C (admBase p))
  have hKambient : MeasurableSet K := (concentration_past_le S t) K hKmeas
  have hIambient : MeasurableSet I :=
    (concentration_past_le S t) I (by simpa only [t] using hI)
  have hIKset : I ⊆ K := by
    intro ω hω
    change dynDelta S t ω ∈ admSetOf S.C (admBase p)
    simpa only [t, admA] using hIK ω hω
  have hYmem : MemLp Y 2 P := concentration_blockIncr_memLp p S f g b
  have hKYmem : MemLp (K.indicator Y) 2 P := hYmem.indicator hKambient
  have hAmem : MemLp (K.indicator A) 2 P := by
    simpa only [A, K, t] using hstat
  have hZdata := concentration_quadratic_term_bound p S f g hf hg hBpos t
  have hZmem : MemLp Z 2 P := by simpa only [Z] using hZdata.1
  have hKZmem : MemLp (K.indicator Z) 2 P := hZmem.indicator hKambient
  have hpoint : ∀ ω, Y ω = A ω + R ω + Z ω := by
    intro ω
    dsimp only [Y, A, R, Z, blockIncr, t]
    rw [Nat.add_mul, one_mul]
    rw [concentration_pointwise_identity p S f g (b * blockLen B) ω,
      concentration_upd_decomposition p S (b * blockLen B) ω]
    ring
  have hRfun : K.indicator R = K.indicator Y - K.indicator A - K.indicator Z := by
    funext ω
    by_cases hω : ω ∈ K <;> simp [Set.indicator, hω, hpoint]
    ring
  have hRmem : MemLp (K.indicator R) 2 P := by
    rw [hRfun]
    exact (hKYmem.sub hAmem).sub hKZmem
  refine ⟨by simpa only [R, K, t] using hRmem, ?_⟩
  have hcenter := concentration_centered_indicator_sq_le
    (dynPast S t) (concentration_past_le S t) I (by simpa only [t] using hI)
    (K.indicator R) hRmem
  have hcoup := hcouple Ω P m n B S hBcouple t
  let F : Ω → ℝ := K.indicator (fun ω => fro (dynSumErr p S t ω) ^ 2)
  have hFint : Integrable F P := by
    simpa only [F, K, t, rlo, rhi, E, admBase] using hcoup.1
  have hcondF : ∫ ω in I, F ω ∂P =
      ∫ ω in I, condExp (dynPast S t) P F ω ∂P :=
    (setIntegral_condExp (concentration_past_le S t) hFint
      (by simpa only [t] using hI)).symm
  have hbuf := lem_app_dyn_buffer_i p rlo' rhi' E' hrlo' hle'
    Ω P m n B S (tauPlus p S) (concentration_tauPlus_meas S) (by
      intro s ω hs
      have hs' := (concentration_tauPlus_iff S s ω).1 hs
      simpa only [rlo', rhi', E', rlo, rhi, E, admAplus, admBase, enl] using hs' s le_rfl) t
  let J : Set Ω := {ω | (t : ℕ∞) ≤ tauPlus p S ω}
  have hIJ : I ⊆ J := by
    intro ω hω
    simpa only [J, t, Set.mem_setOf_eq] using hstop ω hω
  have hbufI : Integrable (I.indicator (fun ω => fro (dynBuf S t ω) ^ 2)) P := by
    have hsqmeas : Measurable (fun ω => fro (dynBuf S t ω) ^ 2) := by
      have hc : Continuous (fun M : Mat m n => fro M ^ 2) := by
        simp_rw [projection_fro_sq]
        fun_prop
      exact hc.measurable.comp ((concentration_state_meas S t).2.mono
        (concentration_past_le S t) le_rfl)
    apply hbuf.1.mono' ((hsqmeas.indicator hIambient).aestronglyMeasurable)
    filter_upwards [] with ω
    by_cases hω : ω ∈ I
    · have hωJ := hIJ hω
      change (t : ℕ∞) ≤ tauPlus p S ω at hωJ
      simp [Set.indicator, hω, hωJ]
    · by_cases hωJ : ω ∈ J <;> simp [J, Set.indicator, hω, hωJ]
      positivity
  have hbufIle : ∫ ω, I.indicator (fun ω => fro (dynBuf S t ω) ^ 2) ω ∂P ≤
      Cbuf * (B : ℝ) := by
    calc
      _ ≤ ∫ ω, J.indicator (fun ω => fro (dynBuf S t ω) ^ 2) ω ∂P := by
        apply integral_mono hbufI hbuf.1
        intro ω
        by_cases hω : ω ∈ I
        · have hωJ := hIJ hω
          change (t : ℕ∞) ≤ tauPlus p S ω at hωJ
          simp [Set.indicator, hω, hωJ]
        · simp [Set.indicator, hω]
          positivity
      _ ≤ 2 * (p.cM * B) + 4 * cMConst p.CSig p.γstar * rhi' * B := by
        simpa only [J, t] using hbuf.2
      _ = Cbuf * (B : ℝ) := by
        simp only [Cbuf]
        push_cast
        ring
  have hFerrI : Integrable (I.indicator (fun ω => fro (dynSumErr p S t ω) ^ 2)) P := by
    have hFI := hFint.indicator hIambient
    apply hFI.congr
    filter_upwards [] with ω
    by_cases hω : ω ∈ I
    · have hωK := hIKset hω
      simp [F, Set.indicator, hω, hωK]
    · simp [Set.indicator, hω]
  have hErrI : ∫ ω, I.indicator (fun ω => fro (dynSumErr p S t ω) ^ 2) ω ∂P ≤
      max KC 0 * ((blockLen B : ℝ) ^ 4 + (B : ℝ) + Cbuf * (B : ℝ)) := by
    have hcondInt : Integrable (condExp (dynPast S t) P F) P := integrable_condExp
    have hbufOn : IntegrableOn (fun ω => fro (dynBuf S t ω) ^ 2) I P :=
      (integrable_indicator_iff hIambient).1 hbufI
    have hconstOn : Integrable (fun _ω : Ω =>
        (blockLen B : ℝ) ^ 4 + (B : ℝ)) (P.restrict I) := integrable_const _
    have hRint : Integrable (fun ω => max KC 0 *
        ((blockLen B : ℝ) ^ 4 + (B : ℝ) + fro (dynBuf S t ω) ^ 2)) (P.restrict I) := by
      exact (hconstOn.add hbufOn).const_mul _
    calc
      _ = ∫ ω in I, F ω ∂P := by
        rw [← integral_indicator hIambient]
        apply integral_congr_ae
        filter_upwards [] with ω
        by_cases hω : ω ∈ I
        · have hωK := hIKset hω
          simp [F, Set.indicator, hω, hωK]
        · simp [Set.indicator, hω]
      _ = ∫ ω in I, condExp (dynPast S t) P F ω ∂P := hcondF
      _ ≤ ∫ ω in I, max KC 0 *
          ((blockLen B : ℝ) ^ 4 + (B : ℝ) + fro (dynBuf S t ω) ^ 2) ∂P := by
        apply integral_mono_ae hcondInt.integrableOn hRint
        exact (ae_restrict_iff' hIambient).2 (hcoup.2.mono fun ω hω hωI => by
          have hωK := hIKset hωI
          have hb := hω hωK
          calc
            condExp (dynPast S t) P F ω ≤
                KC * ((blockLen B : ℝ) ^ 4 + (B : ℝ) + fro (dynBuf S t ω) ^ 2) := by
              simpa only [F, K, t, rlo, rhi, E, admBase] using hb
            _ ≤ max KC 0 * ((blockLen B : ℝ) ^ 4 + (B : ℝ) +
                fro (dynBuf S t ω) ^ 2) := by
              gcongr
              exact le_max_left _ _)
      _ ≤ max KC 0 * ((blockLen B : ℝ) ^ 4 + (B : ℝ) + Cbuf * (B : ℝ)) := by
        rw [integral_const_mul]
        gcongr
        calc
          ∫ ω in I, ((blockLen B : ℝ) ^ 4 + (B : ℝ) +
              fro (dynBuf S t ω) ^ 2) ∂P =
              ((blockLen B : ℝ) ^ 4 + (B : ℝ)) * P.real I +
                ∫ ω, I.indicator (fun ω => fro (dynBuf S t ω) ^ 2) ω ∂P := by
            rw [integral_add hconstOn hbufOn, integral_const,
              measureReal_restrict_apply_univ, integral_indicator hIambient]
            ring
          _ ≤ (blockLen B : ℝ) ^ 4 + (B : ℝ) + Cbuf * (B : ℝ) := by
            have hconst : 0 ≤ (blockLen B : ℝ) ^ 4 + (B : ℝ) := by positivity
            nlinarith [(measureReal_nonneg : 0 ≤ P.real I),
              measureReal_le_one (μ := P) (s := I), hbufIle]
  have hpairInt : ∫ ω, I.indicator (fun ω => (K.indicator R ω) ^ 2) ω ∂P ≤
      4 * (p.h / (B : ℝ)) ^ 2 * E *
        (max KC 0 * ((blockLen B : ℝ) ^ 4 + (B : ℝ) + Cbuf * (B : ℝ))) := by
    have hdomint : Integrable (I.indicator (fun ω =>
        4 * (p.h / (B : ℝ)) ^ 2 * E * fro (dynSumErr p S t ω) ^ 2)) P := by
      have hmul := hFerrI.const_mul (4 * (p.h / (B : ℝ)) ^ 2 * E)
      apply hmul.congr
      filter_upwards [] with ω
      by_cases hω : ω ∈ I <;> simp [Set.indicator, hω]
    calc
      _ ≤ ∫ ω, I.indicator (fun ω =>
          4 * (p.h / (B : ℝ)) ^ 2 * E * fro (dynSumErr p S t ω) ^ 2) ω ∂P := by
        apply integral_mono (hRmem.integrable_sq.indicator hIambient)
          hdomint
        intro ω
        by_cases hω : ω ∈ I
        · have hωK := hIKset hω
          have hD := hIK ω hω
          have hDf : fro (dynDelta S t ω) ^ 2 ≤ E := by
            simpa only [t, E, admA, admBase, admSetOf, Set.mem_setOf_eq] using hD.2.2
          have hW := concentration_wfg_fro_le f g S.C hf hg S.size.2.1 S.size.2.2
            (dynDelta S t ω)
          have hWs : fro (wfg f g S.C (dynDelta S t ω)) ^ 2 ≤ E := by
            have hW0 : 0 ≤ fro (wfg f g S.C (dynDelta S t ω)) := Real.sqrt_nonneg _
            have hD0 : 0 ≤ fro (dynDelta S t ω) := Real.sqrt_nonneg _
            nlinarith [sq_nonneg (fro (wfg f g S.C (dynDelta S t ω)) +
              fro (dynDelta S t ω))]
          have hip := projection_frobIP_le
            (wfg f g S.C (dynDelta S t ω)) (dynSumErr p S t ω)
          simp only [Set.indicator_of_mem hω, Set.indicator_of_mem hωK, R]
          have habs : |frobIP (wfg f g S.C (dynDelta S t ω))
              (dynSumErr p S t ω)| ^ 2 ≤
              E * fro (dynSumErr p S t ω) ^ 2 := by
            have hm := mul_self_le_mul_self (abs_nonneg _) hip
            calc
              |frobIP (wfg f g S.C (dynDelta S t ω)) (dynSumErr p S t ω)| ^ 2 ≤
                  (fro (wfg f g S.C (dynDelta S t ω)) *
                    fro (dynSumErr p S t ω)) ^ 2 := by
                simpa only [pow_two] using hm
              _ = fro (wfg f g S.C (dynDelta S t ω)) ^ 2 *
                  fro (dynSumErr p S t ω) ^ 2 := by ring
              _ ≤ E * fro (dynSumErr p S t ω) ^ 2 :=
                mul_le_mul_of_nonneg_right hWs (sq_nonneg _)
          calc
            (-2 * (p.h / (B : ℝ)) * frobIP (wfg f g S.C (dynDelta S t ω))
                (dynSumErr p S t ω)) ^ 2 =
                4 * (p.h / (B : ℝ)) ^ 2 *
                  frobIP (wfg f g S.C (dynDelta S t ω)) (dynSumErr p S t ω) ^ 2 := by ring
            _ ≤ 4 * (p.h / (B : ℝ)) ^ 2 *
                (E * fro (dynSumErr p S t ω) ^ 2) :=
              mul_le_mul_of_nonneg_left (by simpa only [sq_abs] using habs) (by positivity)
            _ = 4 * (p.h / (B : ℝ)) ^ 2 * E * fro (dynSumErr p S t ω) ^ 2 := by ring
        · simp [Set.indicator, hω]
      _ = 4 * (p.h / (B : ℝ)) ^ 2 * E *
          ∫ ω, I.indicator (fun ω => fro (dynSumErr p S t ω) ^ 2) ω ∂P := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with ω
        by_cases hω : ω ∈ I <;> simp [Set.indicator, hω]
      _ ≤ _ := mul_le_mul_of_nonneg_left hErrI (by
        have hE0 : 0 ≤ E := by dsimp only [E]; linarith [p.hE]
        exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hE0)
  calc
    ∫ ω, (I.indicator (fun ω =>
        K.indicator R ω - condExp (dynPast S t) P (K.indicator R) ω) ω) ^ 2 ∂P ≤
        ∫ ω, I.indicator (fun ω => (K.indicator R ω) ^ 2) ω ∂P := hcenter
    _ ≤ 4 * (p.h / (B : ℝ)) ^ 2 * E *
        (max KC 0 * ((blockLen B : ℝ) ^ 4 + (B : ℝ) + Cbuf * (B : ℝ))) := hpairInt
    _ ≤ C * ((blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) := by
      have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
      have hCbuf0 : 0 ≤ Cbuf := by
        have hrhi : 0 ≤ p.r1 + 1 / 2 := by linarith [p.hr, p.hr0]
        have hrhi'0 : 0 ≤ rhi' := by dsimp [rhi']; positivity
        have hcm : 0 ≤ cMConst p.CSig p.γstar := by
          unfold cMConst
          positivity
        dsimp only [Cbuf]
        exact add_nonneg (mul_nonneg (by norm_num) p.hcM)
          (mul_nonneg (mul_nonneg (by norm_num) hcm) hrhi'0)
      have hKC0 : 0 ≤ max KC 0 := le_max_right _ _
      have hE0 : 0 ≤ E := by dsimp [E]; linarith [p.hE]
      have hinner : (blockLen B : ℝ) ^ 4 + (B : ℝ) + Cbuf * (B : ℝ) ≤
          (2 + Cbuf) * ((blockLen B : ℝ) ^ 4 + (B : ℝ)) := by
        have hL4 : 0 ≤ (blockLen B : ℝ) ^ 4 := by positivity
        have hCB : 0 ≤ Cbuf * (B : ℝ) := mul_nonneg hCbuf0 hBr.le
        have hCL : 0 ≤ Cbuf * (blockLen B : ℝ) ^ 4 := mul_nonneg hCbuf0 hL4
        nlinarith
      dsimp only [C]
      calc
        4 * (p.h / (B : ℝ)) ^ 2 * E *
            (max KC 0 * ((blockLen B : ℝ) ^ 4 + (B : ℝ) + Cbuf * (B : ℝ))) ≤
            4 * (p.h / (B : ℝ)) ^ 2 * E *
              (max KC 0 * ((2 + Cbuf) * ((blockLen B : ℝ) ^ 4 + (B : ℝ)))) := by
          gcongr
        _ = (4 * p.h ^ 2 * E * max KC 0 * (2 + Cbuf)) *
            ((blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) := by
          field_simp

private lemma concentration_blockMartDiff_sq_bound
    (certP : Muon.External.GaussianPoincare) (certOp : Muon.External.GaussianOpNormL6)
    (p : DynParams) :
    ∃ B0 : ℕ, ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (m n B : ℕ)
      (S : DynSetup p P m n B) (f g : ℝ → ℝ) (bstar : Ω → ℕ),
      B0 ≤ B →
      (∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1) →
      (∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1) →
      (∀ b : ℕ, MeasurableSet[dynPast S (b * blockLen B)] {ω | b < bstar ω}) →
      (∀ (b : ℕ) (ω : Ω), b < bstar ω →
        dynDelta S (b * blockLen B) ω ∈ admA p S.C) →
      ∀ b : ℕ,
        ∫ ω, (blockMartDiff p f g S bstar b ω) ^ 2 ∂P ≤
          C * ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) ^ 2 +
            (blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) := by
  obtain ⟨C1, hterm1⟩ := concentration_stationary_term_bound certP certOp p
  obtain ⟨B2, C2, hterm2⟩ := concentration_error_term_bound certOp p
  let rlo := p.r0 / 2
  let rhi := p.r1 + 1 / 2
  let E := p.Estar + 1
  have hrlo : 0 < rlo := by dsimp [rlo]; linarith [p.hr0]
  have hle : rlo ≤ rhi := by dsimp [rlo, rhi]; linarith [p.hr, p.hr0]
  obtain ⟨Bmove, hmove⟩ := lem_app_dyn_movement_ii p rlo rhi E hrlo hle
  let C3 := p.h ^ 4 * p.γstar ^ 2
  let C := 3 * (max C1 0 + max C2 0 + C3)
  refine ⟨max B2 (max Bmove 1), C, ?_⟩
  intro Ω mΩ P hP m n B S f g bstar hB hf hg hbstar hadm b
  let t := b * blockLen B
  let I : Set Ω := {ω | b < bstar ω}
  let K := dynInK S t (admBase p)
  let Y : Ω → ℝ := blockIncr p f g S b
  let A : Ω → ℝ := fun ω =>
    -2 * (p.h / (B : ℝ)) *
      frobIP (wfg f g S.C (dynDelta S t ω)) (dynStatSum p S t ω)
  let R : Ω → ℝ := fun ω =>
    -2 * (p.h / (B : ℝ)) *
      frobIP (wfg f g S.C (dynDelta S t ω)) (dynSumErr p S t ω)
  let Z : Ω → ℝ := fun ω =>
    (p.h / (B : ℝ)) ^ 2 *
      frobIP (∑ r ∈ Finset.range (blockLen B), dynUpd S (t + r) ω)
        (wfg f g S.C (∑ r ∈ Finset.range (blockLen B), dynUpd S (t + r) ω))
  let Q1 := K.indicator A
  let Q2 := K.indicator R
  let Q3 := K.indicator Z
  have hB2 : B2 ≤ B := (le_max_left B2 (max Bmove 1)).trans hB
  have hBmove : Bmove ≤ B :=
    (le_max_of_le_right (le_max_left Bmove 1)).trans hB
  have hBone : 1 ≤ B := (le_max_of_le_right (le_max_right Bmove 1)).trans hB
  have hBpos : 0 < B := lt_of_lt_of_le Nat.zero_lt_one hBone
  have hLpos : 0 < blockLen B := concentration_blockLen_pos hBpos
  have hImeas : MeasurableSet[dynPast S t] I := by
    simpa only [I, t] using hbstar b
  have hIambient : MeasurableSet I := (concentration_past_le S t) I hImeas
  have hIK : ∀ ω ∈ I, dynDelta S t ω ∈ admA p S.C := by
    intro ω hω
    simpa only [I, t, Set.mem_setOf_eq] using hadm b ω hω
  have hIKset : I ⊆ K := by
    intro ω hω
    change dynDelta S t ω ∈ admSetOf S.C (admBase p)
    simpa only [admA] using hIK ω hω
  have hKmeas : MeasurableSet[dynPast S t] K :=
    (concentration_delta_meas S t) (concentration_admSet_meas S.C (admBase p))
  have hKambient : MeasurableSet K := (concentration_past_le S t) K hKmeas
  have hstop : ∀ ω ∈ I, (t : ℕ∞) ≤ tauPlus p S ω := by
    intro ω hω
    have hwin : ∀ b', dynDelta S (b' * blockLen B) ω ∈ admA p S.C →
        ∀ u, b' * blockLen B ≤ u → u ≤ b' * blockLen B + blockLen B →
          dynDelta S u ω ∈ admAplus p S.C := by
      intro b' hD u hu1 hu2
      have hm := (hmove Ω P m n B S hBmove ω (b' * blockLen B) (by
        simpa only [rlo, rhi, E, admA, admBase] using hD)).2 u
      have hdist : |(u : ℤ) - (b' * blockLen B : ℕ)| ≤
          4 * (blockLen B : ℤ) := by
        have hu1z : ((b' * blockLen B : ℕ) : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu1
        have hu2z : (u : ℤ) ≤ ((b' * blockLen B + blockLen B : ℕ) : ℤ) := by
          exact_mod_cast hu2
        rw [abs_of_nonneg (sub_nonneg.mpr hu1z)]
        push_cast at hu2z ⊢
        omega
      simpa only [rlo, rhi, E, admAplus, admBase] using hm hdist
    have hstarts : ∀ b' ≤ b,
        dynDelta S (b' * blockLen B) ω ∈ admA p S.C := by
      intro b' hb'
      apply hadm b' ω
      have hbI : b < bstar ω := hω
      omega
    exact (concentration_tau_of_good S ω hLpos hwin b hstarts).le
  have h1 := hterm1 Ω P m n B S f g I b hf hg hImeas hIK
  have h2 := hterm2 Ω P m n B S f g I b hB2 hf hg hImeas hIK hstop h1.1
  have h3data := concentration_quadratic_term_bound p S f g hf hg hBpos t
  have hYmem : MemLp Y 2 P := concentration_blockIncr_memLp p S f g b
  have hQ1mem : MemLp Q1 2 P := by simpa only [Q1, A, K, t] using h1.1
  have hQ2mem : MemLp Q2 2 P := by simpa only [Q2, R, K, t] using h2.1
  have hZmem : MemLp Z 2 P := by simpa only [Z] using h3data.1
  have hQ3mem : MemLp Q3 2 P := hZmem.indicator hKambient
  have h3center := concentration_centered_indicator_sq_le
    (dynPast S t) (concentration_past_le S t) I hImeas Q3 hQ3mem
  have h3 : ∫ ω, (I.indicator (fun ω =>
      Q3 ω - condExp (dynPast S t) P Q3 ω) ω) ^ 2 ∂P ≤
      C3 * (blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 := by
    calc
      _ ≤ ∫ ω, I.indicator (fun ω => Q3 ω ^ 2) ω ∂P := h3center
      _ ≤ ∫ ω, Z ω ^ 2 ∂P := by
        apply integral_mono (hQ3mem.integrable_sq.indicator hIambient) hZmem.integrable_sq
        intro ω
        by_cases hωI : ω ∈ I
        · have hωK := hIKset hωI
          simp [Q3, Set.indicator, hωI, hωK]
        · simp [Set.indicator, hωI]
          positivity
      _ ≤ C3 * (blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 := by
        simpa only [C3] using h3data.2
  have hpoint : K.indicator Y = Q1 + Q2 + Q3 := by
    funext ω
    by_cases hω : ω ∈ K
    · simp only [Q1, Q2, Q3, Set.indicator_of_mem hω, Pi.add_apply]
      dsimp only [Y, A, R, Z, blockIncr, t]
      rw [Nat.add_mul, one_mul]
      rw [concentration_pointwise_identity p S f g (b * blockLen B) ω,
        concentration_upd_decomposition p S (b * blockLen B) ω]
      ring
    · simp [Q1, Q2, Q3, Set.indicator, hω]
  have hcondK := condExp_indicator (hYmem.integrable one_le_two) hKmeas
  have hsum12 := condExp_add (hQ1mem.integrable one_le_two)
    (hQ2mem.integrable one_le_two) (dynPast S t)
  have hsum123 := condExp_add ((hQ1mem.add hQ2mem).integrable one_le_two)
    (hQ3mem.integrable one_le_two) (dynPast S t)
  have hcondDecomp : condExp (dynPast S t) P (K.indicator Y) =ᵐ[P]
      condExp (dynPast S t) P Q1 + condExp (dynPast S t) P Q2 +
        condExp (dynPast S t) P Q3 := by
    have hcongr := condExp_congr_ae (μ := P) (m := dynPast S t)
      (ae_of_all P fun ω => congr_fun hpoint ω)
    filter_upwards [hcongr, hsum12, hsum123] with ω hcongrω h12 h123
    rw [hcongrω, h123]
    simp only [Pi.add_apply]
    rw [h12]
    rfl
  have hdecomp : (fun ω => I.indicator (fun ω =>
      Y ω - condExp (dynPast S t) P Y ω) ω) =ᵐ[P]
      (fun ω => I.indicator (fun ω => Q1 ω - condExp (dynPast S t) P Q1 ω) ω +
        I.indicator (fun ω => Q2 ω - condExp (dynPast S t) P Q2 ω) ω +
        I.indicator (fun ω => Q3 ω - condExp (dynPast S t) P Q3 ω) ω) := by
    filter_upwards [hcondK, hcondDecomp] with ω hK hD
    by_cases hωI : ω ∈ I
    · have hωK := hIKset hωI
      have hp := congr_fun hpoint ω
      simp only [Set.indicator_of_mem hωI, Set.indicator_of_mem hωK,
        Pi.add_apply] at hK hp ⊢
      simp only [Pi.add_apply] at hD
      rw [← hK, hD, hp]
      ring
    · simp [Set.indicator, hωI]
  have hdmem := concentration_blockMartDiff_memLp p S f g bstar hbstar b
  have hd1mem : MemLp (I.indicator (fun ω =>
      Q1 ω - condExp (dynPast S t) P Q1 ω)) 2 P :=
    (hQ1mem.sub (hQ1mem.condExp one_le_two)).indicator hIambient
  have hd2mem : MemLp (I.indicator (fun ω =>
      Q2 ω - condExp (dynPast S t) P Q2 ω)) 2 P :=
    (hQ2mem.sub (hQ2mem.condExp one_le_two)).indicator hIambient
  have hd3mem : MemLp (I.indicator (fun ω =>
      Q3 ω - condExp (dynPast S t) P Q3 ω)) 2 P :=
    (hQ3mem.sub (hQ3mem.condExp one_le_two)).indicator hIambient
  have hdYmem : MemLp (I.indicator (fun ω =>
      Y ω - condExp (dynPast S t) P Y ω)) 2 P :=
    (hYmem.sub (hYmem.condExp one_le_two)).indicator hIambient
  have hsq : ∀ᵐ ω ∂P, (I.indicator (fun ω =>
      Y ω - condExp (dynPast S t) P Y ω) ω) ^ 2 ≤
      3 * ((I.indicator (fun ω => Q1 ω - condExp (dynPast S t) P Q1 ω) ω) ^ 2 +
        (I.indicator (fun ω => Q2 ω - condExp (dynPast S t) P Q2 ω) ω) ^ 2 +
        (I.indicator (fun ω => Q3 ω - condExp (dynPast S t) P Q3 ω) ω) ^ 2) := by
    filter_upwards [hdecomp] with ω heqω
    rw [heqω]
    nlinarith [sq_nonneg
        (I.indicator (fun ω => Q1 ω - condExp (dynPast S t) P Q1 ω) ω -
          I.indicator (fun ω => Q2 ω - condExp (dynPast S t) P Q2 ω) ω),
      sq_nonneg
        (I.indicator (fun ω => Q2 ω - condExp (dynPast S t) P Q2 ω) ω -
          I.indicator (fun ω => Q3 ω - condExp (dynPast S t) P Q3 ω) ω),
      sq_nonneg
        (I.indicator (fun ω => Q3 ω - condExp (dynPast S t) P Q3 ω) ω -
          I.indicator (fun ω => Q1 ω - condExp (dynPast S t) P Q1 ω) ω)]
  rw [concentration_blockMartDiff_eq_indicator]
  calc
    ∫ ω, (I.indicator (fun ω => Y ω - condExp (dynPast S t) P Y ω) ω) ^ 2 ∂P ≤
        ∫ ω, 3 * ((I.indicator (fun ω =>
          Q1 ω - condExp (dynPast S t) P Q1 ω) ω) ^ 2 +
          (I.indicator (fun ω => Q2 ω - condExp (dynPast S t) P Q2 ω) ω) ^ 2 +
          (I.indicator (fun ω => Q3 ω - condExp (dynPast S t) P Q3 ω) ω) ^ 2) ∂P := by
      apply integral_mono_ae hdYmem.integrable_sq
        (((hd1mem.integrable_sq.add hd2mem.integrable_sq).add hd3mem.integrable_sq).const_mul 3)
      exact hsq
    _ = 3 * (∫ ω, (I.indicator (fun ω =>
          Q1 ω - condExp (dynPast S t) P Q1 ω) ω) ^ 2 ∂P +
        ∫ ω, (I.indicator (fun ω =>
          Q2 ω - condExp (dynPast S t) P Q2 ω) ω) ^ 2 ∂P +
        ∫ ω, (I.indicator (fun ω =>
          Q3 ω - condExp (dynPast S t) P Q3 ω) ω) ^ 2 ∂P) := by
      rw [integral_const_mul]
      congr 1
      calc
        ∫ ω, (I.indicator (fun ω => Q1 ω - condExp (dynPast S t) P Q1 ω) ω) ^ 2 +
            (I.indicator (fun ω => Q2 ω - condExp (dynPast S t) P Q2 ω) ω) ^ 2 +
            (I.indicator (fun ω => Q3 ω - condExp (dynPast S t) P Q3 ω) ω) ^ 2 ∂P =
            ∫ ω, (I.indicator (fun ω => Q1 ω - condExp (dynPast S t) P Q1 ω) ω) ^ 2 +
              (I.indicator (fun ω => Q2 ω - condExp (dynPast S t) P Q2 ω) ω) ^ 2 ∂P +
            ∫ ω, (I.indicator (fun ω => Q3 ω - condExp (dynPast S t) P Q3 ω) ω) ^ 2 ∂P :=
          integral_add (hd1mem.integrable_sq.add hd2mem.integrable_sq) hd3mem.integrable_sq
        _ = _ := by rw [integral_add hd1mem.integrable_sq hd2mem.integrable_sq]
    _ ≤ 3 * (C1 * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 /
          (B : ℝ) ^ 2 + C2 * ((blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) +
          C3 * (blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2) := by
      gcongr
      · simpa only [Q1, A, K, t] using h1.2
      · simpa only [Q2, R, K, t] using h2.2
    _ ≤ C * ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) ^ 2 +
        (blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) := by
      have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
      have hA0 : 0 ≤ (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 /
          (B : ℝ) ^ 2 := by positivity
      have hB0 : 0 ≤ (blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 := by positivity
      have hD0 : 0 ≤ 1 / (B : ℝ) := by positivity
      have hC30 : 0 ≤ C3 := by dsimp [C3]; positivity
      have h1le : C1 * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 /
          (B : ℝ) ^ 2 ≤ max C1 0 * ((blockLen B : ℝ) ^ 2 *
          Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) ^ 2) := by
        calc
          _ = C1 * ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 /
              (B : ℝ) ^ 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hA0
      have h2le : C2 * ((blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) ≤
          max C2 0 * ((blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hB0 hD0)
      have hx1 : 0 ≤ max C1 0 *
          ((blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) :=
        mul_nonneg (le_max_right _ _) (add_nonneg hB0 hD0)
      have hx2 : 0 ≤ max C2 0 * ((blockLen B : ℝ) ^ 2 *
          Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) ^ 2) :=
        mul_nonneg (le_max_right _ _) hA0
      have hx3 : 0 ≤ C3 * ((blockLen B : ℝ) ^ 2 *
          Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) :=
        mul_nonneg hC30 (add_nonneg hA0 hD0)
      have hexpand : (max C1 0 + max C2 0 + C3) *
          ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) ^ 2 +
            (blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) =
          max C1 0 * ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 /
            (B : ℝ) ^ 2) +
          max C2 0 * ((blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) +
          C3 * ((blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2) +
          (max C1 0 * ((blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) +
            max C2 0 * ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 /
              (B : ℝ) ^ 2) +
            C3 * ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 /
              (B : ℝ) ^ 2 + 1 / (B : ℝ))) := by ring
      have hexpand3 : 3 * (max C1 0 + max C2 0 + C3) *
          ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) ^ 2 +
            (blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) =
          3 * (max C1 0 * ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 /
              (B : ℝ) ^ 2) +
            max C2 0 * ((blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) +
            C3 * ((blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2) +
            (max C1 0 * ((blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) +
              max C2 0 * ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 /
                (B : ℝ) ^ 2) +
              C3 * ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 /
                (B : ℝ) ^ 2 + 1 / (B : ℝ)))) := by
        rw [mul_assoc, hexpand]
      dsimp only [C]
      rw [hexpand3]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      refine (add_le_add (add_le_add h1le h2le) le_rfl).trans ?_
      ring_nf at hx1 hx2 hx3 ⊢
      nlinarith [hx1, hx2, hx3]

/-- `lem:app-dyn-martingale` (cr-2026-10-23). Let `b⋆` be a block index (`bstar : Ω → ℕ`) such that, for every
`b`, whether `b < b⋆` is decided by `𝓕_{t_b}`, and such that `Δ_{t_b} ∈ 𝒜` for `b < b⋆`; `I_b = 𝟙_{b<b⋆}`,
`‖f‖_∞, ‖g‖_∞ ≤ 1` (sup over `[0, C_Σ]`). For every `T > 0`,
`𝔼 max_{j ≤ TB/L} |∑_{b<j} I_b ξ_b|² ≤ C(T+1){L log²(2B)/B + L³/B + 1/L}`. The constant `K` is independent of
`T`, of `f,g,b⋆` and of the dimensions; `B₀` is the threshold of the subsection. Integrability of each
`I_b ξ_b`, of the maximum, and the expectation are conjuncts. Statement verbatim from `section.tex`
(ll. 1786–1797):
```latex
\begin{lemma}[Block martingale]\label{lem:app-dyn-martingale}
Let $b_\star$ be a block index such that whether $b<b_\star$ is decided by the
past $\cF_{t_b}$, and such that $\Delta_{t_b}\in\mathcal A$ for $b<b_\star$; put
$I_b\defeq\mathbf 1_{b<b_\star}$. Let $\norm f_\infty,\norm g_\infty\le1$ and
\[
\xi_b\defeq X_{f,g}(\Delta_{t_{b+1}})-X_{f,g}(\Delta_{t_b})-\EE_{t_b}\big[X_{f,g}(\Delta_{t_{b+1}})-X_{f,g}(\Delta_{t_b})\big].
\]
Then for every $T>0$,
\[
\EE\max_{j\le TB/L}\Big|\sum_{b<j}I_b\xi_b\Big|^2\le C(T+1)\Big\{\frac{L\log^2(2B)}{B}+\frac{L^3}{B}+\frac1L\Big\}.
\]
\end{lemma}
```
-/
theorem lem_app_dyn_martingale (certP : Muon.External.GaussianPoincare) (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∃ B0 : ℕ, ∃ K : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B) (f g : ℝ → ℝ) (bstar : Ω → ℕ),
      B0 ≤ B →
      (∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1) → (∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1) →
      (∀ b : ℕ, MeasurableSet[dynPast S (b * blockLen B)] {ω | b < bstar ω}) →
      (∀ (b : ℕ) (ω : Ω), b < bstar ω → dynDelta S (b * blockLen B) ω ∈ admA p S.C) →
        (∀ b : ℕ, Integrable (blockMartDiff p f g S bstar b) P) ∧
        ∀ T : ℝ, 0 < T →
          Integrable (blockMaxSq p f g S bstar T) P ∧
          ∫ ω, blockMaxSq p f g S bstar T ω ∂P ≤
            K * (T + 1) * ((blockLen B : ℝ) * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ)
              + (blockLen B : ℝ) ^ 3 / (B : ℝ) + 1 / (blockLen B : ℝ)) := by
  obtain ⟨B1, C, hC⟩ := concentration_blockMartDiff_sq_bound certP certOp p
  refine ⟨max B1 1, 4 * C, ?_⟩
  intro Ω mΩ P hP m n B S f g bstar hB hf hg hbstar hadm
  let ℱ : Filtration ℕ mΩ := (concentration_blockFiltration_exists S).choose
  have hℱ : ∀ b, ℱ b = dynPast S (b * blockLen B) :=
    (concentration_blockFiltration_exists S).choose_spec
  let d : ℕ → Ω → ℝ := fun b => blockMartDiff p f g S bstar b
  have hdmem : ∀ b, MemLp (d b) 2 P := fun b =>
    concentration_blockMartDiff_memLp p S f g bstar hbstar b
  have hdint : ∀ b, Integrable (d b) P := fun b => (hdmem b).integrable one_le_two
  have hdmeas : ∀ b, StronglyMeasurable[ℱ (b + 1)] (d b) := by
    intro b
    rw [hℱ]
    have hset : MeasurableSet[dynPast S ((b + 1) * blockLen B)] {ω | b < bstar ω} :=
      (concentration_past_mono S (Nat.mul_le_mul_right _ (Nat.le_succ b))) _ (hbstar b)
    have hraw : StronglyMeasurable[dynPast S ((b + 1) * blockLen B)]
        (blockIncr p f g S b) := (concentration_blockIncr_meas S f g b).stronglyMeasurable
    have hcond : StronglyMeasurable[dynPast S ((b + 1) * blockLen B)]
        (condExp (dynPast S (b * blockLen B)) P (blockIncr p f g S b)) :=
      stronglyMeasurable_condExp.mono
        (concentration_past_mono S (Nat.mul_le_mul_right _ (Nat.le_succ b)))
    change StronglyMeasurable[dynPast S ((b + 1) * blockLen B)]
      (blockMartDiff p f g S bstar b)
    rw [concentration_blockMartDiff_eq_indicator]
    exact (hraw.sub hcond).indicator hset
  have hdcenter : ∀ b, condExp (ℱ b) P (d b) =ᵐ[P] 0 := by
    intro b
    rw [hℱ]
    exact concentration_blockMartDiff_centered p S f g bstar hbstar b
  have hmart : Martingale (fun j ω => ∑ b ∈ Finset.range j, d b ω) ℱ P :=
    martingale_finset_partialSums ℱ d hdmeas hdint hdcenter
  refine ⟨hdint, ?_⟩
  intro T hT
  let N := ⌊T * (B : ℝ) / (blockLen B : ℝ)⌋₊
  let M : ℕ → Ω → ℝ := fun j ω => ∑ b ∈ Finset.range j, d b ω
  have hMmem : ∀ j, MemLp (M j) 2 P := fun j => memLp_finset_partialSums d hdmem j
  obtain ⟨hmaxint, hmax⟩ := doob_finset_max_sq ℱ M hmart hMmem N
  have hB1 : B1 ≤ B := (le_max_left B1 1).trans hB
  have hBone : 1 ≤ B := (le_max_right B1 1).trans hB
  have hLpos : 0 < blockLen B := concentration_blockLen_pos (lt_of_lt_of_le Nat.zero_lt_one hBone)
  have hsquares := hC Ω P m n B S f g bstar hB1 hf hg hbstar hadm
  have hsum := integral_sq_finset_partialSums ℱ d hdmeas hdmem hdcenter N
  have hN : (N : ℝ) ≤ T * (B : ℝ) / (blockLen B : ℝ) := by
    exact_mod_cast Nat.floor_le (by positivity : 0 ≤ T * (B : ℝ) / (blockLen B : ℝ))
  have hA0 : 0 ≤ (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) ^ 2 +
      (blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ) := by positivity
  have hC0 : 0 ≤ C := by
    have hz := hsquares 0
    have hi : 0 ≤ ∫ ω, d 0 ω ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
    by_contra hn
    have : C < 0 := lt_of_not_ge hn
    have hApos : 0 < (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) ^ 2 +
        (blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ) := by positivity
    nlinarith
  refine ⟨?_, ?_⟩
  · change Integrable (fun ω => (Finset.range (N + 1)).sup'
        Finset.nonempty_range_add_one (fun j => (M j ω) ^ 2)) P
    exact hmaxint
  · change ∫ ω, (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        (fun j => (M j ω) ^ 2) ∂P ≤ _
    calc
      _ ≤ 4 * ∫ ω, (M N ω) ^ 2 ∂P := hmax
      _ = 4 * ∑ b ∈ Finset.range N, ∫ ω, d b ω ^ 2 ∂P := by rw [hsum]
      _ ≤ 4 * ((N : ℝ) * (C * ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 /
          (B : ℝ) ^ 2 + (blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)))) := by
        gcongr
        simpa only [Finset.card_range, nsmul_eq_mul] using
          Finset.sum_le_card_nsmul (Finset.range N) (fun b => ∫ ω, d b ω ^ 2 ∂P)
            _ (fun b _ => hsquares b)
      _ ≤ (4 * C) * (T + 1) * ((blockLen B : ℝ) * Real.log (2 * (B : ℝ)) ^ 2 /
          (B : ℝ) + (blockLen B : ℝ) ^ 3 / (B : ℝ) + 1 / (blockLen B : ℝ)) := by
        have hBr : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hBone)
        have hLr : (0 : ℝ) < blockLen B := by exact_mod_cast hLpos
        have hscale : (N : ℝ) * ((blockLen B : ℝ) / B) ≤ T + 1 := by
          calc
            (N : ℝ) * ((blockLen B : ℝ) / B) ≤
                (T * (B : ℝ) / (blockLen B : ℝ)) * ((blockLen B : ℝ) / B) :=
              mul_le_mul_of_nonneg_right hN (by positivity)
            _ = T := by field_simp
            _ ≤ T + 1 := by linarith
        have hid : ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) ^ 2 +
              (blockLen B : ℝ) ^ 4 / (B : ℝ) ^ 2 + 1 / (B : ℝ)) =
            ((blockLen B : ℝ) / B) * ((blockLen B : ℝ) * Real.log (2 * (B : ℝ)) ^ 2 /
              (B : ℝ) + (blockLen B : ℝ) ^ 3 / (B : ℝ) + 1 / (blockLen B : ℝ)) := by
          field_simp
        rw [hid]
        have hR0 : 0 ≤ (blockLen B : ℝ) * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) +
            (blockLen B : ℝ) ^ 3 / (B : ℝ) + 1 / (blockLen B : ℝ) := by positivity
        calc
          4 * ((N : ℝ) * (C * ((blockLen B : ℝ) / B *
              ((blockLen B : ℝ) * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) +
                (blockLen B : ℝ) ^ 3 / (B : ℝ) + 1 / (blockLen B : ℝ))))) =
              ((N : ℝ) * ((blockLen B : ℝ) / B)) *
                (4 * C * ((blockLen B : ℝ) * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) +
                  (blockLen B : ℝ) ^ 3 / (B : ℝ) + 1 / (blockLen B : ℝ))) := by ring
          _ ≤ (T + 1) * (4 * C * ((blockLen B : ℝ) * Real.log (2 * (B : ℝ)) ^ 2 /
                (B : ℝ) + (blockLen B : ℝ) ^ 3 / (B : ℝ) + 1 / (blockLen B : ℝ))) :=
            mul_le_mul_of_nonneg_right hscale (mul_nonneg (mul_nonneg (by norm_num) hC0) hR0)
          _ = (4 * C) * (T + 1) * ((blockLen B : ℝ) * Real.log (2 * (B : ℝ)) ^ 2 /
              (B : ℝ) + (blockLen B : ℝ) ^ 3 / (B : ℝ) + 1 / (blockLen B : ℝ)) := by ring

/-! ## Helpers for `lem:app-dyn-prefix` (P-E.10.P3) -/

private lemma prefix_indep_sup {Ω : Type*} (A M F G : MeasurableSpace Ω)
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

private lemma prefix_indep_past_future {p : DynParams} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) :
    Indep (dynPast S t) (chainFuture S.cs t) P := by
  refine prefix_indep_sup _ _ _
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

private lemma prefix_Ahat_norm {m n : ℕ} (C : Covariances m n) (D : Mat m n)
    (hD : 0 < riskSigma C D) : fro (Ahat C D) = 1 := by
  have hsq : ∀ (c : ℝ) (K : Mat m n), fro (c • K) ^ 2 = c ^ 2 * fro K ^ 2 := by
    intro c K
    have hf : ∀ K : Mat m n, fro K ^ 2 = ∑ i, ∑ j, K i j ^ 2 := by
      intro K
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


private theorem prefix_stat_rand_aesm {m n B : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ)
    (D : Ω → Mat m n) (hD : Measurable D)
    (hs : ∀ᵐ ω ∂P, Summable (fun j : ℕ =>
      emaW p.β j • batchGrad (D ω) (physBatch C (cs.aux (t : ℤ) j) ω))) (k : ℕ) :
    AEStronglyMeasurable (fun ω => (def_app_dyn_chains p C cs t (D ω) 0 ω).stat k) P := by
  have hcG : Continuous (fun x : Mat m n × (Fin B → Vec m × Vec n) =>
      batchGrad x.1 (fun a => phys C (x.2 a))) := by
    unfold batchGrad grad resid phys outer
    fun_prop
  have hb : ∀ s : ℤ, Measurable (fun ω => batchGrad (D ω) (physBatch C (cs.act s) ω)) := by
    intro s
    have h1 : Measurable (fun ω => (D ω, fun a => cs.act s a ω)) :=
      hD.prodMk (measurable_pi_iff.mpr fun a => cs.meas_act s a)
    have h2 := hcG.measurable.comp h1
    have e : (fun ω => batchGrad (D ω) (physBatch C (cs.act s) ω)) =
        (fun x : Mat m n × (Fin B → Vec m × Vec n) => batchGrad x.1 (fun a => phys C (x.2 a))) ∘
          (fun ω => (D ω, fun a => cs.act s a ω)) := by
      funext ω; rfl
    rw [e]; exact h2
  induction k with
  | zero =>
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
      ∑ j ∈ Finset.range N,
        emaW p.β j • batchGrad (D ω) (physBatch C (cs.aux (t : ℤ) j) ω))
      (fun N => ?_) ?_
    · refine (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ => ?_).aestronglyMeasurable
      have h1 : Measurable (fun ω => (D ω, fun a => cs.aux (t : ℤ) j a ω)) :=
        hD.prodMk (measurable_pi_iff.mpr fun a => cs.meas_aux (t : ℤ) j a)
      exact (hcG.measurable.comp h1).stronglyMeasurable.const_smul (emaW p.β j)
    · filter_upwards [hs] with ω hω
      exact hω.hasSum.tendsto_sum_nat
  | succ k ih =>
    exact (ih.const_smul p.β).add ((hb ((t : ℤ) + k + 1)).stronglyMeasurable.aestronglyMeasurable.const_smul (1 - p.β))

private theorem prefix_statV_rand_aem {m n B : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ)
    (D : Ω → Mat m n) (hD : Measurable D)
    (hs : ∀ᵐ ω ∂P, Summable (fun j : ℕ =>
      emaW p.β j • batchGrad (D ω) (physBatch C (cs.aux (t : ℤ) j) ω))) (k : ℕ) :
    AEMeasurable (fun ω => (def_app_dyn_chains p C cs t (D ω) 0 ω).statV k) P := by
  have hrisk : Continuous (fun D : Mat m n => riskSigma C D) := by
    unfold riskSigma pairSigma
    fun_prop
  have hρ : ∀ ω, 0 ≤ physRidge p C (D ω) := fun ω => by
    unfold physRidge
    rw [eqn_app_setup_whitened_risk]
    have := p.hϱ
    positivity
  have hρm : Measurable (fun ω => (⟨physRidge p C (D ω), hρ ω⟩ : Set.Ici (0 : ℝ))) := by
    unfold physRidge
    exact (((hrisk.measurable.comp hD).const_mul 2).mul_const p.ϱ).subtype_mk
  have hst := (prefix_stat_rand_aesm p C cs t D hD hs k).aemeasurable
  exact (measurable_Q (m := m) (n := n)).comp_aemeasurable (hρm.aemeasurable.prodMk hst)


private lemma prefix_vbar_bound (p : DynParams) :
    ∃ CV : ℝ, 0 ≤ CV ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B) (t r : ℕ) (D : Mat m n), 0 < riskSigma S.C D →
      fro (Muon.mean P (fun ω => stationaryV p S.C S.cs t D r ω)) ≤ CV := by
  obtain ⟨CV, hCV⟩ := lem_app_dyn_mean_iii_ema p.γstar p.CSig p.ϱ p.ϱ p.hϱ le_rfl
  refine ⟨max CV 0, le_max_right _ _, ?_⟩
  intro Ω _ P _ m n B S t r D hD
  have hBpos : 0 < B := projection_batch_pos_of_risk_pos p S.C S.size D hD
  let F : Muon.Setup.FrozenParams m n B :=
    ⟨S.C, Ahat S.C D, prefix_Ahat_norm S.C D hD, p.β, p.hβ, hBpos⟩
  let P0 : Measure ((ℤ × Fin B) → Vec m × Vec n) :=
    Measure.infinitePi fun _ : ℤ × Fin B =>
      (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)
  have : IsProbabilityMeasure P0 := by
    dsimp only [P0]
    infer_instance
  let S' : Muon.Setup.FrozenSamples P0 m n B := Classical.choice (frozenSamples_nonempty m n B)
  have hlaw := lem_app_dyn_chains_i p S.C S.cs t D 0 hD F rfl rfl rfl S'
  have hsum := (lem_app_dyn_chains_iii p S.C S.cs t D 0 hD S.size).1
  have hmeasV : ∀ k, AEMeasurable (fun ω => (def_app_dyn_chains p S.C S.cs t D 0 ω).statV k) P := by
    intro k
    exact prefix_statV_rand_aem p S.C S.cs t (fun _ => D) measurable_const hsum k
  have hpath : AEMeasurable (fun ω (k : ℕ) => (def_app_dyn_chains p S.C S.cs t D 0 ω).statV k) P :=
    aemeasurable_pi_iff.mpr hmeasV
  have hridge : 0 ≤ p.ϱ := p.hϱ.le
  have hQm : Measurable (fun K : Mat m n => Q p.ϱ K) :=
    measurable_Q.comp ((measurable_const (a := (⟨p.ϱ, hridge⟩ : Set.Ici (0 : ℝ)))).prodMk
      measurable_id)
  have hbufpath : AEMeasurable (fun ω' (s : ℤ) => frozenBuf F S' s ω') P0 :=
    (lem_app_setup_ema_law_ii F S').2.1
  have hpath' : AEMeasurable (fun ω' (k : ℕ) => frozenUpd F S' p.ϱ ((t : ℤ) + (k : ℤ) - 1) ω') P0 := by
    refine aemeasurable_pi_iff.mpr fun k => ?_
    exact hQm.comp_aemeasurable ((measurable_pi_apply ((t : ℤ) + (k : ℤ) - 1)).comp_aemeasurable hbufpath)
  have hmean : Muon.mean P (fun ω => stationaryV p S.C S.cs t D r ω) =
      Muon.mean P0 (fun ω' => frozenUpd F S' p.ϱ ((t : ℤ) + (r : ℤ)) ω') := by
    ext i j
    simp only [Muon.mean, Matrix.of_apply]
    have hf : Continuous (fun y : ℕ → Mat m n => y (r + 1) i j) := by fun_prop
    have e1 := integral_map hpath hf.aestronglyMeasurable
    have e2 := integral_map hpath' hf.aestronglyMeasurable
    rw [hlaw.2.2.1] at e1
    have e3 := e1.symm.trans e2
    have e4 : (t : ℤ) + ((r + 1 : ℕ) : ℤ) - 1 = (t : ℤ) + r := by push_cast; ring
    simp only [e4] at e3
    exact e3
  rw [hmean]
  have hb := (hCV m n B (ℤ × Fin B → Vec m × Vec n) P0 S' F ((t : ℤ) + (r : ℤ)) (by simpa using S.size.1) S.size.2.1 S.size.2.2).2.2.2 p.ϱ
    ⟨le_rfl, le_rfl⟩
  have h0 : 0 ≤ fro (Muon.mean P0 (fun ω => dQ p.ϱ (frozenBuf F S' ((t : ℤ) + (r : ℤ)) ω))) :=
    Real.sqrt_nonneg _
  calc fro (Muon.mean P0 (fun ω' => frozenUpd F S' p.ϱ ((t : ℤ) + (r : ℤ)) ω')) ≤ CV := by
        change fro (Muon.mean P0 (fun ω => Q p.ϱ (frozenBuf F S' ((t : ℤ) + (r : ℤ)) ω))) ≤ CV
        linarith
    _ ≤ max CV 0 := le_max_left _ _


private lemma prefix_risk_nonneg {m n : ℕ} (C : Covariances m n)
    (D : Mat m n) : 0 ≤ riskSigma C D := by
  rw [eqn_app_setup_whitened_risk]
  positivity

private lemma prefix_abs_entry_le_fro {m n : ℕ} (A : Mat m n)
    (i : Fin m) (j : Fin n) : |A i j| ≤ fro A := by
  unfold fro
  apply Real.abs_le_sqrt
  have h1 : ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖A i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  simpa [Real.norm_eq_abs, sq_abs] using h1.trans h2

private lemma prefix_frobIP_eq_sum {m n : ℕ} (T M : Mat m n) :
    frobIP T M = ∑ i, ∑ j, T i j * M i j := by
  simp only [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]

private lemma prefix_statV_fro_sq {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t r : ℕ) (D : Mat m n)
    (ω : Ω) : fro (stationaryV p C cs t D r ω) ^ 2 ≤ ((min m n : ℕ) : ℝ) := by
  have hridge : 0 ≤ physRidge p C D := by
    unfold physRidge
    have := prefix_risk_nonneg C D
    have := p.hϱ
    positivity
  have hfilter := lem_app_setup_filter_i _ hridge (stationaryN p C cs t D r ω)
  have hrank : ((stationaryN p C cs t D r ω).rank : ℝ) ≤ ((min m n : ℕ) : ℝ) :=
    Nat.cast_le.mpr hfilter.2.2.1
  exact hfilter.2.1.trans hrank


private lemma prefix_second_moment (certP : Muon.External.GaussianPoincare)
    (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) (rlo rhi : ℝ)
    (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B) (t r : ℕ) (D T : Mat m n),
      rlo ≤ riskSigma S.C D → riskSigma S.C D ≤ rhi →
        Integrable (fun ω => frobIP T (stationaryV p S.C S.cs t D r ω) ^ 2) P ∧
        ∫ ω, frobIP T (stationaryV p S.C S.cs t D r ω) ^ 2 ∂P ≤
          K * (Real.log (2 * (B : ℝ)) ^ 2 + 1) * fro T ^ 2 := by
  obtain ⟨KP, hKP⟩ := lem_app_dyn_poincare_i p rlo rhi hrlo hle certP certOp
  obtain ⟨CV, hCV0, hCV⟩ := prefix_vbar_bound p
  refine ⟨max KP 0 + CV ^ 2, by positivity, ?_⟩
  intro Ω _ P _ m n B S t r D T hlo hhi
  have hD : 0 < riskSigma S.C D := hrlo.trans_le hlo
  obtain ⟨hmem, hvar⟩ := hKP Ω P m n B S t r D T hlo hhi
  have hX2 : Integrable (fun ω => frobIP T (stationaryV p S.C S.cs t D r ω) ^ 2) P :=
    hmem.integrable_sq
  refine ⟨hX2, ?_⟩
  have hsum := (lem_app_dyn_chains_iii p S.C S.cs t D 0 hD S.size).1
  have hmeasV : AEMeasurable (fun ω => stationaryV p S.C S.cs t D r ω) P :=
    prefix_statV_rand_aem p S.C S.cs t (fun _ => D) measurable_const hsum (r + 1)
  have hent : ∀ i j, Integrable (fun ω => stationaryV p S.C S.cs t D r ω i j) P := by
    intro i j
    refine Integrable.of_bound (C := Real.sqrt ((min m n : ℕ) : ℝ)) ?_ (ae_of_all _ fun ω => ?_)
    · have hc : Continuous (fun K : Mat m n => K i j) := by fun_prop
      exact (hc.measurable.comp_aemeasurable hmeasV).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact (prefix_abs_entry_le_fro _ i j).trans
        (Real.le_sqrt_of_sq_le (prefix_statV_fro_sq p S.C S.cs t r D ω))
  have hmean : ∫ ω, frobIP T (stationaryV p S.C S.cs t D r ω) ∂P =
      frobIP T (Muon.mean P (fun ω => stationaryV p S.C S.cs t D r ω)) := by
    simp only [prefix_frobIP_eq_sum, Muon.mean, Matrix.of_apply]
    refine (integral_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum _ fun j _ => (hent i j).const_mul _)).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (integral_finsetSum Finset.univ (fun j _ => (hent i j).const_mul _)).trans ?_
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have hmeanle : (∫ ω, frobIP T (stationaryV p S.C S.cs t D r ω) ∂P) ^ 2 ≤ CV ^ 2 * fro T ^ 2 := by
    rw [hmean]
    have h1 := projection_frobIP_le T (Muon.mean P (fun ω => stationaryV p S.C S.cs t D r ω))
    have h2 := hCV Ω P m n B S t r D hD
    have h3 : |frobIP T (Muon.mean P (fun ω => stationaryV p S.C S.cs t D r ω))| ≤ CV * fro T := by
      calc _ ≤ fro T * fro (Muon.mean P (fun ω => stationaryV p S.C S.cs t D r ω)) := h1
        _ ≤ fro T * CV := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
        _ = CV * fro T := mul_comm _ _
    calc _ = |frobIP T (Muon.mean P (fun ω => stationaryV p S.C S.cs t D r ω))| ^ 2 := (sq_abs _).symm
      _ ≤ (CV * fro T) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      _ = CV ^ 2 * fro T ^ 2 := by ring
  have hvar2 := variance_eq_sub (μ := P) hmem
  have hint : ∫ ω, frobIP T (stationaryV p S.C S.cs t D r ω) ^ 2 ∂P =
      variance (fun ω => frobIP T (stationaryV p S.C S.cs t D r ω)) P +
        (∫ ω, frobIP T (stationaryV p S.C S.cs t D r ω) ∂P) ^ 2 := by
    rw [hvar2]
    simp only [Pi.pow_apply]
    ring
  rw [hint]
  have hfT : 0 ≤ fro T ^ 2 := sq_nonneg _
  have hKP0 : KP ≤ max KP 0 := le_max_left _ _
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) ^ 2 := sq_nonneg _
  calc _ ≤ KP * Real.log (2 * (B : ℝ)) ^ 2 * fro T ^ 2 + CV ^ 2 * fro T ^ 2 := add_le_add hvar hmeanle
    _ ≤ (max KP 0 + CV ^ 2) * (Real.log (2 * (B : ℝ)) ^ 2 + 1) * fro T ^ 2 := by
      have h1 : KP * Real.log (2 * (B : ℝ)) ^ 2 ≤ max KP 0 * Real.log (2 * (B : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hKP0 hlog
      have h2 : 0 ≤ max KP 0 := le_max_right _ _
      nlinarith [mul_nonneg h2 hfT, mul_nonneg (sq_nonneg CV) hfT, mul_nonneg (sq_nonneg CV) (mul_nonneg hlog hfT), mul_le_mul_of_nonneg_right h1 hfT]


private lemma prefix_amgm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f P) (hf0 : ∀ ω, 0 ≤ f ω)
    (hsq : Integrable (fun ω => f ω ^ 2) P) (q : ℝ) (hq : 0 < q) :
    Integrable f P ∧ ∫ ω, f ω ∂P ≤ ((∫ ω, f ω ^ 2 ∂P) + q ^ 2) / (2 * q) := by
  have hg : Integrable (fun ω => (f ω ^ 2 + q ^ 2) / (2 * q)) P :=
    (hsq.add (integrable_const _)).div_const _
  have hle : ∀ ω, f ω ≤ (f ω ^ 2 + q ^ 2) / (2 * q) := by
    intro ω
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (f ω - q)]
  have hint : Integrable f P :=
    hg.mono' hf (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]; exact hle ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω, f ω ∂P ≤ ∫ ω, (f ω ^ 2 + q ^ 2) / (2 * q) ∂P := integral_mono hint hg hle
    _ = _ := by
      rw [integral_div, integral_add hsq (integrable_const _)]
      simp

private lemma prefix_cond_transfer {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (𝓕 : MeasurableSpace Ω) (h𝓕 : 𝓕 ≤ mΩ)
    (K I : Set Ω) (F R : Ω → ℝ) (hI : MeasurableSet[𝓕] I) (hIK : I ⊆ K)
    (hFint : Integrable (K.indicator F) P) (hR : Integrable (I.indicator R) P)
    (hcond : ∀ᵐ ω ∂P, ω ∈ K → condExp 𝓕 P (K.indicator F) ω ≤ R ω) :
    Integrable (I.indicator F) P ∧ ∫ ω, I.indicator F ω ∂P ≤ ∫ ω, I.indicator R ω ∂P := by
  have hIam : @MeasurableSet Ω mΩ I := h𝓕 _ hI
  have heq : I.indicator F = I.indicator (K.indicator F) := by
    funext ω
    by_cases hω : ω ∈ I
    · simp [Set.indicator_of_mem hω, Set.indicator_of_mem (hIK hω)]
    · simp [Set.indicator_of_notMem hω]
  rw [heq]
  refine ⟨hFint.indicator hIam, ?_⟩
  rw [integral_indicator hIam, integral_indicator hIam (f := R), ← setIntegral_condExp h𝓕 hFint hI]
  apply integral_mono_ae integrable_condExp.integrableOn ((integrable_indicator_iff hIam).1 hR)
  exact (ae_restrict_iff' hIam).2 (hcond.mono fun ω hω hωI => hω (hIK hωI))

private lemma prefix_C0_ge_one (β : ℝ) : 1 ≤ C0 β := by
  unfold C0
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

private lemma prefix_q_ge_log (β : ℝ) (B : ℕ) (hB : 1 ≤ B) :
    Real.log (2 * (B : ℝ)) ≤ (prefixLen β B : ℝ) ∧ 1 ≤ prefixLen β B := by
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hl : 0 < Real.log (2 * (B : ℝ)) := Real.log_pos (by linarith)
  have hC := prefix_C0_ge_one β
  have h1 : C0 β * Real.log (2 * (B : ℝ)) ≤ (prefixLen β B : ℝ) := Nat.le_ceil _
  refine ⟨by nlinarith, ?_⟩
  exact Nat.ceil_pos.mpr (by positivity)

private lemma prefix_beta_pow (β : ℝ) (hβ : 0 ≤ β ∧ β < 1) (B : ℕ) (hB : 1 ≤ B) :
    β ^ (2 * (prefixLen β B + 1)) * (B : ℝ) ≤ 1 := by
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  obtain ⟨hq1, hq2⟩ := prefix_q_ge_log β B hB
  by_cases h0 : β = 0
  · subst h0
    simp
  have hpos : 0 < β := lt_of_le_of_ne hβ.1 (Ne.symm h0)
  have hlogneg : Real.log β < 0 := Real.log_neg hpos hβ.2
  have hlog1 : 0 < Real.log (1 / β) := Real.log_pos (by rw [lt_div_iff₀ hpos]; linarith [hβ.2])
  have hC : 2 / Real.log (1 / β) ≤ C0 β := by
    unfold C0; rw [if_neg h0]; exact le_max_right _ _
  have hL2 : 0 < Real.log (2 * (B : ℝ)) := Real.log_pos (by linarith)
  have hq : (prefixLen β B : ℝ) ≥ C0 β * Real.log (2 * (B : ℝ)) := Nat.le_ceil _
  have h2 : 2 * Real.log (2 * (B : ℝ)) ≤ (prefixLen β B : ℝ) * Real.log (1 / β) := by
    have : 2 / Real.log (1 / β) * Real.log (2 * (B : ℝ)) ≤ (prefixLen β B : ℝ) :=
      (mul_le_mul_of_nonneg_right hC hL2.le).trans hq
    rw [div_mul_eq_mul_div, div_le_iff₀ hlog1] at this
    exact this
  have hlogβ : Real.log (1 / β) = - Real.log β := by
    rw [one_div, Real.log_inv]
  have hexp : β ^ (prefixLen β B) = Real.exp ((prefixLen β B : ℝ) * Real.log β) := by
    rw [Real.exp_nat_mul, Real.exp_log hpos]
  have h3 : β ^ (prefixLen β B) ≤ Real.exp (-(2 * Real.log (2 * (B : ℝ)))) := by
    rw [hexp]
    apply Real.exp_le_exp.mpr
    rw [hlogβ] at h2
    linarith
  have h4 : Real.exp (-(2 * Real.log (2 * (B : ℝ)))) = ((2 * (B : ℝ)) ^ 2)⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    rw [show 2 * Real.log (2 * (B : ℝ)) = ((2 : ℕ) : ℝ) * Real.log (2 * (B : ℝ)) by norm_num,
      Real.exp_nat_mul, Real.exp_log (by linarith)]
  have h5 : β ^ (2 * (prefixLen β B + 1)) ≤ β ^ (prefixLen β B) :=
    pow_le_pow_of_le_one hβ.1 hβ.2.le (by omega)
  have h6 : β ^ (2 * (prefixLen β B + 1)) ≤ ((2 * (B : ℝ)) ^ 2)⁻¹ := by
    rw [← h4]; exact h5.trans h3
  calc β ^ (2 * (prefixLen β B + 1)) * (B : ℝ) ≤ ((2 * (B : ℝ)) ^ 2)⁻¹ * B :=
        mul_le_mul_of_nonneg_right h6 (by linarith)
    _ ≤ 1 := by
        rw [inv_mul_le_iff₀ (by positivity)]
        nlinarith

private lemma prefix_cond_stationary (certP : Muon.External.GaussianPoincare)
    (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) (rlo rhi E : ℝ)
    (hrlo : 0 < rlo) (hle : rlo ≤ rhi) (cW : ℝ) (hcW : 0 ≤ cW) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B) (W : Mat m n →ₗ[ℝ] Mat m n),
      (∀ X : Mat m n, fro (W X) ≤ cW * fro X) → ∀ (a r : ℕ) (I : Set Ω),
      MeasurableSet[dynPast S a] I →
      (∀ ω ∈ I, dynDelta S a ω ∈ admSetOf S.C (rlo, rhi, E)) →
      AEMeasurable (I.indicator (fun ω => stationaryV p S.C S.cs a (dynDelta S a ω) r ω)) P ∧
      Integrable (I.indicator (fun ω =>
        frobIP (W (dynDelta S a ω)) (stationaryV p S.C S.cs a (dynDelta S a ω) r ω) ^ 2)) P ∧
      ∫ ω, I.indicator (fun ω =>
        frobIP (W (dynDelta S a ω)) (stationaryV p S.C S.cs a (dynDelta S a ω) r ω) ^ 2) ω ∂P ≤
        K * (Real.log (2 * (B : ℝ)) ^ 2 + 1) := by
  obtain ⟨K2, hK20, hK2⟩ := prefix_second_moment certP certOp p rlo rhi hrlo hle
  refine ⟨K2 * (cW ^ 2 * max E 0), by positivity, ?_⟩
  intro Ω mΩ P hP m n B S W hW a r I hI hIK
  have h𝓕 : dynPast S a ≤ mΩ := concentration_past_le S a
  have hIam : MeasurableSet I := h𝓕 _ hI
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) ^ 2 + 1 := by positivity
  by_cases hne : I.Nonempty
  swap
  · have hI0 : I = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst hI0
    simp only [Set.indicator_empty]
    refine ⟨aemeasurable_const, integrable_zero _ _ _, ?_⟩
    simp only [integral_zero]
    positivity
  obtain ⟨ω0, hω0⟩ := hne
  let D0 : Mat m n := dynDelta S a ω0
  have hD0 : D0 ∈ admSetOf S.C (rlo, rhi, E) := hIK ω0 hω0
  classical
  let D' : Ω → Mat m n := fun ω => if ω ∈ I then dynDelta S a ω else D0
  have hD'F : Measurable[dynPast S a] D' :=
    Measurable.ite hI (concentration_delta_meas S a) measurable_const
  have hD'm : Measurable D' := hD'F.mono h𝓕 le_rfl
  have hD'mem : ∀ ω, D' ω ∈ admSetOf S.C (rlo, rhi, E) := by
    intro ω
    by_cases hω : ω ∈ I
    · simp only [D', if_pos hω]; exact hIK ω hω
    · simp only [D', if_neg hω]; exact hD0
  have hD'pos : ∀ ω, 0 < riskSigma S.C (D' ω) := fun ω => hrlo.trans_le (hD'mem ω).1
  have hD'eq : ∀ ω ∈ I, D' ω = dynDelta S a ω := fun ω hω => by simp only [D', if_pos hω]
  have hDint : Integrable (fun ω => riskSigma S.C (D' ω)) P := by
    refine Integrable.of_bound (C := rhi)
      ((concentration_risk_cont S.C).measurable.comp hD'm).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (prefix_risk_nonneg _ _)]
    exact (hD'mem ω).2.1
  have hind := prefix_indep_past_future S a
  have hiv := lem_app_dyn_chains_iv (dynPast S a) p S.C S.cs a S.size h𝓕 hind
    D' (dynBuf S a) hD'F (concentration_state_meas S a).2 (ae_of_all _ hD'pos) hDint
  have hVm : AEMeasurable (fun ω => stationaryV p S.C S.cs a (D' ω) r ω) P :=
    prefix_statV_rand_aem p S.C S.cs a D' hD'm hiv.1 (r + 1)
  have hWc : Continuous (fun X : Mat m n => W X) := LinearMap.continuous_of_finiteDimensional W
  have hWc' : Continuous (fun x : Mat m n × Mat m n => W x.1) := hWc.comp continuous_fst
  have hfc : Continuous (fun x : Mat m n × Mat m n => frobIP (W x.1) x.2) := by
    have e : (fun x : Mat m n × Mat m n => frobIP (W x.1) x.2) =
        fun x => ∑ i, ∑ j, (W x.1) i j * x.2 i j := funext fun x => prefix_frobIP_eq_sum _ _
    rw [e]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp hWc')).mul
      ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))
  have hΦc : Continuous (fun x : Mat m n × Mat m n => frobIP (W x.1) x.2 ^ 2) := hfc.pow 2
  let Φ : Mat m n → (ℕ → Mat m n) → ℝ := fun D x => frobIP (W D) (x r) ^ 2
  have hΦ : Measurable (Function.uncurry Φ) := by
    have h3 : Continuous (fun z : Mat m n × (ℕ → Mat m n) => frobIP (W z.1) (z.2 r) ^ 2) := by
      have e : (fun z : Mat m n × (ℕ → Mat m n) => frobIP (W z.1) (z.2 r)) =
          fun z => ∑ i, ∑ j, (W z.1) i j * (z.2 r) i j := funext fun z => prefix_frobIP_eq_sum _ _
      have hW1 : Continuous (fun z : Mat m n × (ℕ → Mat m n) => W z.1) := hWc.comp continuous_fst
      have hc : Continuous (fun z : Mat m n × (ℕ → Mat m n) => frobIP (W z.1) (z.2 r)) := by
        rw [e]
        refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
        exact ((continuous_apply j).comp ((continuous_apply i).comp hW1)).mul
          ((continuous_apply j).comp ((continuous_apply i).comp
            ((continuous_apply r).comp continuous_snd)))
      exact hc.pow 2
    exact h3.measurable
  have hEnn : ∀ ω, fro (D' ω) ^ 2 ≤ max E 0 := fun ω => (hD'mem ω).2.2.trans (le_max_left _ _)
  have hWD : ∀ ω, fro (W (D' ω)) ^ 2 ≤ cW ^ 2 * max E 0 := by
    intro ω
    have h1 := hW (D' ω)
    have h0 : 0 ≤ fro (W (D' ω)) := Real.sqrt_nonneg _
    calc fro (W (D' ω)) ^ 2 ≤ (cW * fro (D' ω)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = cW ^ 2 * fro (D' ω) ^ 2 := by ring
      _ ≤ cW ^ 2 * max E 0 := mul_le_mul_of_nonneg_left (hEnn ω) (sq_nonneg _)
  have hint : Integrable (fun ω => Φ (D' ω) (fun r' => stationaryV p S.C S.cs a (D' ω) r' ω)) P := by
    refine Integrable.of_bound (C := cW ^ 2 * max E 0 * ((min m n : ℕ) : ℝ))
      ((hΦc.measurable.comp_aemeasurable (hD'm.aemeasurable.prodMk hVm)).aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    change |frobIP (W (D' ω)) (stationaryV p S.C S.cs a (D' ω) r ω) ^ 2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    have h1 := projection_frobIP_le (W (D' ω)) (stationaryV p S.C S.cs a (D' ω) r ω)
    have h2 := mul_self_le_mul_self (abs_nonneg _) h1
    have h3 := prefix_statV_fro_sq p S.C S.cs a r (D' ω) ω
    calc |frobIP (W (D' ω)) (stationaryV p S.C S.cs a (D' ω) r ω)| ^ 2
        ≤ (fro (W (D' ω)) * fro (stationaryV p S.C S.cs a (D' ω) r ω)) ^ 2 := by
          simpa only [pow_two] using h2
      _ = fro (W (D' ω)) ^ 2 * fro (stationaryV p S.C S.cs a (D' ω) r ω) ^ 2 := by ring
      _ ≤ (cW ^ 2 * max E 0) * ((min m n : ℕ) : ℝ) :=
          mul_le_mul (hWD ω) h3 (sq_nonneg _) (by positivity)
  have hfrz := stationary_freezing_condExp (dynPast S a) p S.C S.cs a h𝓕 hind D' hD'F Φ hΦ hint
  have hcb : ∀ ω, ∫ ω', Φ (D' ω) (fun r' => stationaryV p S.C S.cs a (D' ω) r' ω') ∂P ≤
      K2 * (cW ^ 2 * max E 0) * (Real.log (2 * (B : ℝ)) ^ 2 + 1) := by
    intro ω
    have hm := (hK2 Ω P m n B S a r (D' ω) (W (D' ω)) (hD'mem ω).1 (hD'mem ω).2.1).2
    change ∫ ω', frobIP (W (D' ω)) (stationaryV p S.C S.cs a (D' ω) r ω') ^ 2 ∂P ≤ _
    calc _ ≤ K2 * (Real.log (2 * (B : ℝ)) ^ 2 + 1) * fro (W (D' ω)) ^ 2 := hm
      _ ≤ K2 * (Real.log (2 * (B : ℝ)) ^ 2 + 1) * (cW ^ 2 * max E 0) :=
          mul_le_mul_of_nonneg_left (hWD ω) (by positivity)
      _ = _ := by ring
  have hind_eq : I.indicator (fun ω =>
      frobIP (W (dynDelta S a ω)) (stationaryV p S.C S.cs a (dynDelta S a ω) r ω) ^ 2) =
      I.indicator (fun ω => Φ (D' ω) (fun r' => stationaryV p S.C S.cs a (D' ω) r' ω)) := by
    funext ω
    by_cases hω : ω ∈ I
    · simp only [Set.indicator_of_mem hω, hD'eq ω hω, Φ]
    · simp [Set.indicator_of_notMem hω]
  have hindV : I.indicator (fun ω => stationaryV p S.C S.cs a (dynDelta S a ω) r ω) =
      I.indicator (fun ω => stationaryV p S.C S.cs a (D' ω) r ω) := by
    funext ω
    by_cases hω : ω ∈ I
    · simp only [Set.indicator_of_mem hω, hD'eq ω hω]
    · simp [Set.indicator_of_notMem hω]
  rw [hind_eq, hindV]
  refine ⟨hVm.indicator hIam, hint.indicator hIam, ?_⟩
  rw [integral_indicator hIam, ← setIntegral_condExp h𝓕 hint hI]
  calc ∫ ω in I, condExp (dynPast S a) P (fun ω => Φ (D' ω) (fun r' =>
        stationaryV p S.C S.cs a (D' ω) r' ω)) ω ∂P
      ≤ ∫ _ω in I, K2 * (cW ^ 2 * max E 0) * (Real.log (2 * (B : ℝ)) ^ 2 + 1) ∂P := by
        apply integral_mono_ae integrable_condExp.integrableOn (integrable_const _).integrableOn
        exact (ae_restrict_iff' hIam).2 (hfrz.mono fun ω hω _ => by rw [hω]; exact hcb ω)
    _ = P.real I * (K2 * (cW ^ 2 * max E 0) * (Real.log (2 * (B : ℝ)) ^ 2 + 1)) := by
        rw [setIntegral_const, smul_eq_mul]
    _ ≤ K2 * (cW ^ 2 * max E 0) * (Real.log (2 * (B : ℝ)) ^ 2 + 1) := by
        have hc : 0 ≤ K2 * (cW ^ 2 * max E 0) * (Real.log (2 * (B : ℝ)) ^ 2 + 1) := by positivity
        nlinarith [(measureReal_nonneg : 0 ≤ P.real I), measureReal_le_one (μ := P) (s := I)]

private lemma prefix_buffer_bound (p : DynParams) :
    ∃ Cbuf : ℝ, 0 ≤ Cbuf ∧ ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (m n B : ℕ) (S : DynSetup p P m n B) (a : ℕ) (I : Set Ω),
      MeasurableSet I → (∀ ω ∈ I, (a : ℕ∞) ≤ tauPlus p S ω) →
      Integrable (I.indicator (fun ω => fro (dynBuf S a ω) ^ 2)) P ∧
      ∫ ω, I.indicator (fun ω => fro (dynBuf S a ω) ^ 2) ω ∂P ≤ Cbuf * (B : ℝ) := by
  have hrlo' : 0 < (enl (admBase p)).1 := by
    simp only [enl, admBase]; linarith [p.hr0]
  have hle' : (enl (admBase p)).1 ≤ (enl (admBase p)).2.1 := by
    simp only [enl, admBase]; linarith [p.hr0, p.hr]
  have hrhi' : 0 ≤ (enl (admBase p)).2.1 := hrlo'.le.trans hle'
  have hcm : 0 ≤ cMConst p.CSig p.γstar := by
    unfold cMConst
    positivity
  refine ⟨2 * p.cM + 4 * cMConst p.CSig p.γstar * (enl (admBase p)).2.1,
    add_nonneg (mul_nonneg (by norm_num) p.hcM) (mul_nonneg (mul_nonneg (by norm_num) hcm) hrhi'), ?_⟩
  intro Ω mΩ P hP m n B S a I hIam hIJ
  have hbuf := lem_app_dyn_buffer_i p (enl (admBase p)).1 (enl (admBase p)).2.1
    (enl (admBase p)).2.2 hrlo' hle' Ω P m n B S (tauPlus p S) (concentration_tauPlus_meas S)
    (by
      intro s ω hs
      exact (concentration_tauPlus_iff S s ω).1 hs s le_rfl) a
  let J : Set Ω := {ω | (a : ℕ∞) ≤ tauPlus p S ω}
  have hIJ' : I ⊆ J := fun ω hω => hIJ ω hω
  have hsqmeas : Measurable (fun ω => fro (dynBuf S a ω) ^ 2) := by
    have hc : Continuous (fun M : Mat m n => fro M ^ 2) := by
      simp_rw [projection_fro_sq]
      fun_prop
    exact hc.measurable.comp ((concentration_state_meas S a).2.mono
      (concentration_past_le S a) le_rfl)
  have hdom : ∀ ω, I.indicator (fun ω => fro (dynBuf S a ω) ^ 2) ω ≤
      J.indicator (fun ω => fro (dynBuf S a ω) ^ 2) ω := by
    intro ω
    by_cases hω : ω ∈ I
    · have hωJ := hIJ' hω
      simp [Set.indicator, hω, hωJ]
    · by_cases hωJ : ω ∈ J
      · simp [Set.indicator, hω, hωJ]
        positivity
      · simp [Set.indicator, hω, hωJ]
  have hint : Integrable (I.indicator (fun ω => fro (dynBuf S a ω) ^ 2)) P := by
    apply hbuf.1.mono' ((hsqmeas.indicator hIam).aestronglyMeasurable)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hdom ω
    · by_cases hω : ω ∈ I <;> simp [Set.indicator, hω]
      positivity
  refine ⟨hint, ?_⟩
  calc _ ≤ ∫ ω, J.indicator (fun ω => fro (dynBuf S a ω) ^ 2) ω ∂P :=
        integral_mono hint hbuf.1 hdom
    _ ≤ _ := by
        have := hbuf.2
        simp only [J] at this ⊢
        push_cast at this ⊢
        linarith

private lemma prefix_q_le_L (β : ℝ) :
    ∃ B1 : ℕ, ∀ B : ℕ, B1 ≤ B → 1 ≤ B ∧ prefixLen β B ≤ blockLen B := by
  have hC := prefix_C0_ge_one β
  have ht : Tendsto (fun B : ℕ => (B : ℝ) ^ ((1 : ℝ) / 16)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually_ge_atTop (17 * C0 β + 3))
  refine ⟨max N 1, fun B hB => ⟨le_trans (le_max_right _ _) hB, ?_⟩⟩
  have hBN := hN B (le_trans (le_max_left _ _) hB)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast le_trans (le_max_right _ _) hB
  set v : ℝ := (B : ℝ) ^ ((1 : ℝ) / 16) with hv
  have hv1 : 1 ≤ v := by linarith
  have hvpos : 0 < v := by linarith
  have hvB : (B : ℝ) = v ^ 16 := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hv8 : (B : ℝ) ^ ((1 : ℝ) / 8) = v ^ 2 := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hlogv : Real.log v ≤ v - 1 := Real.log_le_sub_one_of_pos hvpos
  have hlogB : Real.log (B : ℝ) = 16 * Real.log v := by
    rw [hvB, Real.log_pow]; push_cast; ring
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hL2 : Real.log (2 * (B : ℝ)) ≤ 1 + 16 * v := by
    rw [Real.log_mul (by norm_num) (by linarith), hlogB]
    linarith
  have hL2pos : 0 ≤ Real.log (2 * (B : ℝ)) := Real.log_nonneg (by linarith)
  have hq : (prefixLen β B : ℝ) < C0 β * Real.log (2 * (B : ℝ)) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hL : v ^ 2 < (blockLen B : ℝ) + 1 := by
    rw [← hv8]; exact Nat.lt_floor_add_one _
  have h1 : C0 β * Real.log (2 * (B : ℝ)) ≤ C0 β * (1 + 16 * v) :=
    mul_le_mul_of_nonneg_left hL2 (by linarith)
  have h2 : (17 * C0 β + 3) * v ≤ v ^ 2 := by nlinarith
  have : (prefixLen β B : ℝ) < blockLen B := by nlinarith
  exact_mod_cast this.le

private lemma prefix_move_term (p : DynParams) :
    ∃ Bm : ℕ, ∃ Kmv : ℝ, 0 ≤ Kmv ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (m n B : ℕ) (S : DynSetup p P m n B) (cW : ℝ) (W : Mat m n →ₗ[ℝ] Mat m n),
      Bm ≤ B → 0 < B → (∀ X : Mat m n, fro (W X) ≤ cW * fro X) → ∀ (a r : ℕ) (ω : Ω),
      r ≤ 4 * blockLen B → dynDelta S a ω ∈ admAplus p S.C →
      |frobIP (W (dynDelta S (a + r) ω - dynDelta S a ω)) (dynUpd S (a + r) ω)| ≤
        Kmv * |cW| * (r : ℝ) := by
  have hrlo : 0 < (enl (admBase p)).1 := by
    simp only [enl, admBase]; linarith [p.hr0]
  have hle : (enl (admBase p)).1 ≤ (enl (admBase p)).2.1 := by
    simp only [enl, admBase]; linarith [p.hr0, p.hr]
  obtain ⟨Bm, hm⟩ := lem_app_dyn_movement_ii p (enl (admBase p)).1 (enl (admBase p)).2.1
    (enl (admBase p)).2.2 hrlo hle
  refine ⟨Bm, p.h * p.γstar, mul_nonneg p.hh.le p.hγ, ?_⟩
  intro Ω _ P m n B S cW W hBm hB hW a r ω hr hD
  have hstop := (hm Ω P m n B S hBm ω a hD).1
  have hlt : ((a + r : ℕ) : ℕ∞) < dynStop S ω :=
    lt_of_le_of_lt (by exact_mod_cast Nat.add_le_add_left hr a) hstop
  obtain ⟨-, hfro, -⟩ := lem_app_dyn_movement_i p S ω a (a + r) (Nat.le_add_right a r) hlt
  have hcast : (((a + r : ℕ) : ℝ) - (a : ℝ)) = (r : ℝ) := by push_cast; ring
  rw [hcast] at hfro
  have hBr : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hB)
  have hU := concentration_dynUpd_fro_bound p S ω (a + r)
  rw [Real.sqrt_mul p.hγ] at hU
  have hip := projection_frobIP_le (W (dynDelta S (a + r) ω - dynDelta S a ω)) (dynUpd S (a + r) ω)
  have hWb : fro (W (dynDelta S (a + r) ω - dynDelta S a ω)) ≤
      |cW| * (p.h * Real.sqrt p.γstar * (r : ℝ) / Real.sqrt (B : ℝ)) :=
    (hW _).trans (by
      calc cW * fro (dynDelta S (a + r) ω - dynDelta S a ω) ≤
          |cW| * fro (dynDelta S (a + r) ω - dynDelta S a ω) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hfro (abs_nonneg _))
  calc _ ≤ fro (W (dynDelta S (a + r) ω - dynDelta S a ω)) * fro (dynUpd S (a + r) ω) := hip
    _ ≤ (|cW| * (p.h * Real.sqrt p.γstar * (r : ℝ) / Real.sqrt (B : ℝ))) *
        (Real.sqrt p.γstar * Real.sqrt (B : ℝ)) :=
        mul_le_mul hWb hU (Real.sqrt_nonneg _)
          (mul_nonneg (abs_nonneg _) (div_nonneg (mul_nonneg (mul_nonneg p.hh.le (Real.sqrt_nonneg _)) (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)))
    _ = p.h * p.γstar * |cW| * (r : ℝ) := by
        have hs2 : Real.sqrt p.γstar ^ 2 = p.γstar := Real.sq_sqrt p.hγ
        field_simp
        rw [hs2]
        ring

private lemma prefix_frobIP_add_left {m n : ℕ} (X Y Z : Mat m n) :
    frobIP (X + Y) Z = frobIP X Z + frobIP Y Z := by
  simp only [prefix_frobIP_eq_sum, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

private lemma prefix_frobIP_add_right {m n : ℕ} (X Y Z : Mat m n) :
    frobIP X (Y + Z) = frobIP X Y + frobIP X Z := by
  simp only [prefix_frobIP_eq_sum, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

private lemma prefix_frobIP_sub_right {m n : ℕ} (X Y Z : Mat m n) :
    frobIP X (Y - Z) = frobIP X Y - frobIP X Z := by
  simp only [prefix_frobIP_eq_sum, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma prefix_fro_add {m n : ℕ} (X Y : Mat m n) : fro (X + Y) ≤ fro X + fro Y := by
  open scoped Matrix.Norms.Frobenius in
    simpa only [fro_eq_norm] using norm_add_le X Y

private lemma prefix_frobIP_cont {m n : ℕ} (W : Mat m n →ₗ[ℝ] Mat m n) :
    Continuous (fun x : Mat m n × Mat m n => frobIP (W x.1) x.2) := by
  have hWc : Continuous (fun X : Mat m n => W X) := LinearMap.continuous_of_finiteDimensional W
  have hWc' : Continuous (fun x : Mat m n × Mat m n => W x.1) := hWc.comp continuous_fst
  have e : (fun x : Mat m n × Mat m n => frobIP (W x.1) x.2) =
      fun x => ∑ i, ∑ j, (W x.1) i j * x.2 i j := funext fun x => prefix_frobIP_eq_sum _ _
  rw [e]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply j).comp ((continuous_apply i).comp hWc')).mul
    ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))

private lemma prefix_fro_cont {m n : ℕ} : Continuous (fun X : Mat m n => fro X) := by
  unfold fro
  fun_prop

private lemma prefix_meas_frobIP {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}
    (W : Mat m n →ₗ[ℝ] Mat m n) (D V : Ω → Mat m n) (hD : Measurable D)
    (hV : AEMeasurable V P) : AEMeasurable (fun ω => frobIP (W (D ω)) (V ω)) P := by
  have hg : Measurable (fun x : Mat m n × Mat m n => frobIP (W x.1) x.2) :=
    (prefix_frobIP_cont W).measurable
  have h2 : AEMeasurable (fun ω => (D ω, V ω)) P := hD.aemeasurable.prodMk hV
  have h3 := hg.comp_aemeasurable h2
  exact h3

private lemma prefix_meas_abs_frobIP {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}
    (W : Mat m n →ₗ[ℝ] Mat m n) (D V : Ω → Mat m n) (hD : Measurable D)
    (hV : AEMeasurable V P) : AEMeasurable (fun ω => |frobIP (W (D ω)) (V ω)|) P := by
  have hg : Measurable (fun x : Mat m n × Mat m n => |frobIP (W x.1) x.2|) :=
    (continuous_abs.comp (prefix_frobIP_cont W)).measurable
  have h2 : AEMeasurable (fun ω => (D ω, V ω)) P := hD.aemeasurable.prodMk hV
  have h3 := hg.comp_aemeasurable h2
  exact h3

/-! ## `lem:app-dyn-prefix` and `eqn:app-dyn-envelope` -/

set_option maxHeartbeats 4000000 in
private lemma prefix_i_core (certP : Muon.External.GaussianPoincare) (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∀ cW : ℝ, 0 ≤ cW → ∃ B0 : ℕ, ∃ K : ℝ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (m n B : ℕ) (S : DynSetup p P m n B) (W : Mat m n →ₗ[ℝ] Mat m n),
        B0 ≤ B → (∀ X : Mat m n, fro (W X) ≤ cW * fro X) →
        ∀ u : ℕ, prefixLen p.β B ≤ u →
          Integrable ({ω | ((u - prefixLen p.β B : ℕ) : ℕ∞) < tauPlus p S ω}.indicator
            (fun ω => |frobIP (W (dynDelta S u ω)) (dynUpd S u ω)|)) P ∧
          ∫ ω, {ω | ((u - prefixLen p.β B : ℕ) : ℕ∞) < tauPlus p S ω}.indicator
            (fun ω => |frobIP (W (dynDelta S u ω)) (dynUpd S u ω)|) ω ∂P
            ≤ K * (prefixLen p.β B : ℝ) := by
  intro cW hcW
  have hrlo : 0 < (enl (admBase p)).1 := by
    simp only [enl, admBase]; linarith [p.hr0]
  have hle : (enl (admBase p)).1 ≤ (enl (admBase p)).2.1 := by
    simp only [enl, admBase]; linarith [p.hr0, p.hr]
  have hEpos : 0 < (enl (admBase p)).2.2 := by
    simp only [enl, admBase]; linarith [p.hE]
  obtain ⟨Bc1, K1, hc1⟩ := lem_app_dyn_coupling_i certOp p (enl (admBase p)).1
    (enl (admBase p)).2.1 (enl (admBase p)).2.2 hrlo hle
  obtain ⟨Bc2, K2, hc2⟩ := lem_app_dyn_coupling_ii certOp p (enl (admBase p)).1
    (enl (admBase p)).2.1 (enl (admBase p)).2.2 hrlo hle
  obtain ⟨Ks, hKs0, hKs⟩ := prefix_cond_stationary certP certOp p (enl (admBase p)).1
    (enl (admBase p)).2.1 (enl (admBase p)).2.2 hrlo hle cW hcW
  obtain ⟨Cbuf, hCbuf0, hbuf⟩ := prefix_buffer_bound p
  obtain ⟨B1, hB1⟩ := prefix_q_le_L p.β
  obtain ⟨Bmv, Kmv, hKmv0, hmv⟩ := prefix_move_term p
  let K1' := max K1 0
  let K2' := max K2 0
  let Tb := cW * Real.sqrt (enl (admBase p)).2.2
  let c2 := 2 * K1' + 2 * K2' * (Cbuf + 1)
  have hK1' : 0 ≤ K1' := le_max_right _ _
  have hK2' : 0 ≤ K2' := le_max_right _ _
  have hTb : 0 ≤ Tb := mul_nonneg hcW (Real.sqrt_nonneg _)
  refine ⟨max (max (max Bc1 Bc2) (max B1 Bmv)) 1,
    (2 * Ks + 1) / 2 + Tb * (c2 + 1) / 2 + Kmv * |cW|, ?_⟩
  intro Ω mΩ P hP m n B S W hBge hW u hu
  have hBs : ((Bc1 ≤ B ∧ Bc2 ≤ B) ∧ (B1 ≤ B ∧ Bmv ≤ B)) ∧ 1 ≤ B := by
    simpa only [max_le_iff] using hBge
  obtain ⟨⟨⟨hBc1, hBc2⟩, ⟨hB1', hBmv⟩⟩, hB1le⟩ := hBs
  obtain ⟨-, hqL⟩ := hB1 B hB1'
  have hBpos : 0 < B := hB1le
  obtain ⟨hlogq, hq1⟩ := prefix_q_ge_log p.β B hB1le
  have hbeta := prefix_beta_pow p.β p.hβ B hB1le
  have hlog0 : 0 ≤ Real.log (2 * (B : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ B := by exact_mod_cast hB1le
    linarith
  set q := prefixLen p.β B with hqdef
  have hq4 : q ≤ 4 * blockLen B := by omega
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < q := by linarith
  set a := u - q with ha
  have hau : a + q = u := by omega
  set A : Set Ω := {ω | (a : ℕ∞) < tauPlus p S ω} with hA
  have hAF : MeasurableSet[dynPast S a] A := concentration_tauPlus_meas S a
  have hAam : MeasurableSet A := concentration_past_le S a _ hAF
  have hAK : ∀ ω ∈ A, dynDelta S a ω ∈ admSetOf S.C ((enl (admBase p)).1,
      (enl (admBase p)).2.1, (enl (admBase p)).2.2) := by
    intro ω hω
    exact (concentration_tauPlus_iff S a ω).1 hω a le_rfl
  have hAJ : ∀ ω ∈ A, (a : ℕ∞) ≤ tauPlus p S ω := fun ω hω => le_of_lt hω
  have hΔa : Measurable (dynDelta S a) :=
    (concentration_delta_meas S a).mono (concentration_past_le S a) le_rfl
  have hupd : Measurable (dynUpd S u) :=
    (concentration_upd_meas S u).mono (concentration_past_le S (u + 1)) le_rfl
  have hΔu : Measurable (dynDelta S u) :=
    (concentration_delta_meas S u).mono (concentration_past_le S u) le_rfl
  have hfc := prefix_frobIP_cont W
  let V : Ω → Mat m n := fun ω => stationaryV p S.C S.cs a (dynDelta S a ω) q ω
  obtain ⟨hVm, hf1sq, hf1bd⟩ := hKs Ω P m n B S W hW a q A hAF hAK
  -- the first term
  let f1 : Ω → ℝ := A.indicator (fun ω => |frobIP (W (dynDelta S a ω)) (V ω)|)
  have hf1eq : f1 = fun ω => |frobIP (W (dynDelta S a ω)) (A.indicator V ω)| := by
    funext ω
    by_cases hω : ω ∈ A
    · simp only [f1, Set.indicator_of_mem hω]
    · simp [f1, Set.indicator_of_notMem hω, prefix_frobIP_eq_sum]
  have hf1meas : AEMeasurable f1 P := by
    rw [hf1eq]
    exact prefix_meas_abs_frobIP W _ _ hΔa hVm
  have hf1sqeq : (fun ω => f1 ω ^ 2) = A.indicator (fun ω =>
      frobIP (W (dynDelta S a ω)) (stationaryV p S.C S.cs a (dynDelta S a ω) q ω) ^ 2) := by
    funext ω
    by_cases hω : ω ∈ A
    · simp only [f1, Set.indicator_of_mem hω, sq_abs, V]
    · simp [f1, Set.indicator_of_notMem hω]
  have hf1sq' : Integrable (fun ω => f1 ω ^ 2) P := by rw [hf1sqeq]; exact hf1sq
  have hf10 : ∀ ω, 0 ≤ f1 ω := by
    intro ω
    by_cases hω : ω ∈ A <;> simp [f1, Set.indicator, hω]
  obtain ⟨hf1int, hf1le⟩ := prefix_amgm f1 hf1meas.aestronglyMeasurable hf10 hf1sq' q hqpos
  have hf1sqle : ∫ ω, f1 ω ^ 2 ∂P ≤ 2 * Ks * (q : ℝ) ^ 2 := by
    rw [hf1sqeq]
    refine hf1bd.trans ?_
    have hl2 : Real.log (2 * (B : ℝ)) ^ 2 ≤ (q : ℝ) ^ 2 := pow_le_pow_left₀ hlog0 hlogq 2
    have h1 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hl2 h1) hKs0]
  -- the second term
  obtain ⟨⟨hFint, hFcond⟩, -⟩ := hc1 Ω P m n B S hBc1 a q hq4
  obtain ⟨⟨hGint, hGcond⟩, -⟩ := hc2 Ω P m n B S hBc2 a q hq4
  have hAKsub : A ⊆ dynInK S a ((enl (admBase p)).1, (enl (admBase p)).2.1,
      (enl (admBase p)).2.2) := fun ω hω => hAK ω hω
  have hconstA : ∀ c : ℝ, 0 ≤ c → Integrable (A.indicator (fun _ => c)) P ∧
      ∫ ω, A.indicator (fun _ => c) ω ∂P ≤ c := by
    intro c hc
    refine ⟨(integrable_const c).indicator hAam, ?_⟩
    rw [integral_indicator hAam, setIntegral_const, smul_eq_mul]
    nlinarith [(measureReal_nonneg : 0 ≤ P.real A), measureReal_le_one (μ := P) (s := A)]
  obtain ⟨hFAint, hFAle⟩ := prefix_cond_transfer (dynPast S a) (concentration_past_le S a)
    (dynInK S a ((enl (admBase p)).1, (enl (admBase p)).2.1, (enl (admBase p)).2.2)) A
    (fun ω => fro (dynErrM p S a q ω) ^ 2 + fro (dynErrS p S a q ω) ^ 2)
    (fun _ => K1' * (q : ℝ) ^ 2) hAF hAKsub hFint
    (hconstA _ (by positivity)).1
    (hFcond.mono fun ω hω hωK => (hω hωK).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
  have hFA : ∫ ω, A.indicator (fun ω => fro (dynErrM p S a q ω) ^ 2 +
      fro (dynErrS p S a q ω) ^ 2) ω ∂P ≤ K1' * (q : ℝ) ^ 2 :=
    hFAle.trans (hconstA _ (by positivity)).2
  obtain ⟨hbi, hbb⟩ := hbuf Ω P m n B S a A hAam hAJ
  have hc0 : 0 ≤ K2' * p.β ^ (2 * (q + 1)) := mul_nonneg hK2' (pow_nonneg p.hβ.1 _)
  have hReq : A.indicator (fun ω => K2' * p.β ^ (2 * (q + 1)) *
      (fro (dynBuf S a ω) ^ 2 + (B : ℝ))) = fun ω =>
      K2' * p.β ^ (2 * (q + 1)) * A.indicator (fun ω => fro (dynBuf S a ω) ^ 2) ω +
      K2' * p.β ^ (2 * (q + 1)) * (B : ℝ) * A.indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω]; ring
    · simp [Set.indicator_of_notMem hω]
  have hRint : Integrable (A.indicator (fun ω => K2' * p.β ^ (2 * (q + 1)) *
      (fro (dynBuf S a ω) ^ 2 + (B : ℝ)))) P := by
    rw [hReq]
    exact (hbi.const_mul _).add (((hconstA 1 zero_le_one).1).const_mul _)
  obtain ⟨hGAint, hGAle⟩ := prefix_cond_transfer (dynPast S a) (concentration_past_le S a)
    (dynInK S a ((enl (admBase p)).1, (enl (admBase p)).2.1, (enl (admBase p)).2.2)) A
    (fun ω => fro (dynErrV p S a q ω) ^ 2)
    (fun ω => K2' * p.β ^ (2 * (q + 1)) * (fro (dynBuf S a ω) ^ 2 + (B : ℝ)))
    hAF hAKsub hGint hRint
    (hGcond.mono fun ω hω hωK => (hω hωK).trans (by
      have hnn : 0 ≤ p.β ^ (2 * (q + 1)) * (fro (dynBuf S a ω) ^ 2 + (B : ℝ)) :=
        mul_nonneg (pow_nonneg p.hβ.1 _) (by positivity)
      calc K2 * p.β ^ (2 * (q + 1)) * (fro (dynBuf S a ω) ^ 2 + (B : ℝ)) =
          K2 * (p.β ^ (2 * (q + 1)) * (fro (dynBuf S a ω) ^ 2 + (B : ℝ))) := by ring
        _ ≤ K2' * (p.β ^ (2 * (q + 1)) * (fro (dynBuf S a ω) ^ 2 + (B : ℝ))) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
        _ = _ := by ring))
  have hGA : ∫ ω, A.indicator (fun ω => fro (dynErrV p S a q ω) ^ 2) ω ∂P ≤
      K2' * (Cbuf + 1) := by
    refine hGAle.trans ?_
    rw [hReq, integral_add ((hbi.const_mul _)) (((hconstA 1 zero_le_one).1).const_mul _),
      integral_const_mul, integral_const_mul]
    have h1 := hbb
    have h2 := (hconstA 1 zero_le_one).2
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    have hbB : p.β ^ (2 * (q + 1)) * (B : ℝ) ≤ 1 := hbeta
    have e3 : K2' * p.β ^ (2 * (q + 1)) * (B : ℝ) = K2' * (p.β ^ (2 * (q + 1)) * (B : ℝ)) := by ring
    have hI1 : ∫ ω, A.indicator (fun ω => fro (dynBuf S a ω) ^ 2) ω ∂P ≤ Cbuf * (B : ℝ) := h1
    have hm1 : K2' * p.β ^ (2 * (q + 1)) * ∫ ω, A.indicator (fun ω => fro (dynBuf S a ω) ^ 2) ω ∂P ≤
        K2' * p.β ^ (2 * (q + 1)) * (Cbuf * (B : ℝ)) := mul_le_mul_of_nonneg_left hI1 hc0
    have hm2 : K2' * p.β ^ (2 * (q + 1)) * (B : ℝ) * ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂P ≤
        K2' * p.β ^ (2 * (q + 1)) * (B : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hc0 hB0)
    have hm3 : K2' * (p.β ^ (2 * (q + 1)) * (B : ℝ)) ≤ K2' * 1 :=
      mul_le_mul_of_nonneg_left hbB hK2'
    have hm4 : K2' * (p.β ^ (2 * (q + 1)) * (B : ℝ)) * Cbuf ≤ K2' * 1 * Cbuf :=
      mul_le_mul_of_nonneg_right hm3 hCbuf0
    nlinarith
  -- f2
  let f2 : Ω → ℝ := A.indicator (fun ω => fro (dynUpd S u ω - V ω))
  have hf2eq : f2 = fun ω => fro (A.indicator (dynUpd S u) ω - A.indicator V ω) := by
    funext ω
    by_cases hω : ω ∈ A
    · simp only [f2, Set.indicator_of_mem hω]
    · simp [f2, Set.indicator_of_notMem hω, fro]
  have hf2meas : AEMeasurable f2 P := by
    rw [hf2eq]
    have h2 : AEMeasurable (fun ω => A.indicator (dynUpd S u) ω - A.indicator V ω) P :=
      (hupd.indicator hAam).aemeasurable.sub hVm
    have h3 := (prefix_fro_cont (m := m) (n := n)).measurable.comp_aemeasurable h2
    exact h3
  have hf20 : ∀ ω, 0 ≤ f2 ω := by
    intro ω
    by_cases hω : ω ∈ A <;> simp [f2, Set.indicator, hω, fro]
  have hTot : ∀ ω, dynUpd S u ω - V ω = dynErrS p S a q ω + dynErrV p S a q ω := by
    intro ω
    simp only [dynErrS, dynErrV, V, hau]
    abel
  have hpt2 : ∀ ω, f2 ω ^ 2 ≤ 2 * A.indicator (fun ω => fro (dynErrM p S a q ω) ^ 2 +
      fro (dynErrS p S a q ω) ^ 2) ω + 2 * A.indicator (fun ω => fro (dynErrV p S a q ω) ^ 2) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [f2, Set.indicator_of_mem hω]
      rw [hTot ω]
      have h1 := prefix_fro_add (dynErrS p S a q ω) (dynErrV p S a q ω)
      have h0 : 0 ≤ fro (dynErrS p S a q ω + dynErrV p S a q ω) := Real.sqrt_nonneg _
      have h2 := pow_le_pow_left₀ h0 h1 2
      have hM : 0 ≤ fro (dynErrM p S a q ω) ^ 2 := sq_nonneg _
      nlinarith [sq_nonneg (fro (dynErrS p S a q ω) - fro (dynErrV p S a q ω))]
    · simp [f2, Set.indicator_of_notMem hω]
  have hg2int : Integrable (fun ω => 2 * A.indicator (fun ω => fro (dynErrM p S a q ω) ^ 2 +
      fro (dynErrS p S a q ω) ^ 2) ω + 2 * A.indicator (fun ω => fro (dynErrV p S a q ω) ^ 2) ω) P :=
    (hFAint.const_mul 2).add (hGAint.const_mul 2)
  have hf2sq' : Integrable (fun ω => f2 ω ^ 2) P := by
    refine hg2int.mono' (hf2meas.pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt2 ω
  have hf2sqle : ∫ ω, f2 ω ^ 2 ∂P ≤ c2 * (q : ℝ) ^ 2 := by
    calc ∫ ω, f2 ω ^ 2 ∂P ≤ ∫ ω, (2 * A.indicator (fun ω => fro (dynErrM p S a q ω) ^ 2 +
          fro (dynErrS p S a q ω) ^ 2) ω + 2 * A.indicator (fun ω => fro (dynErrV p S a q ω) ^ 2) ω) ∂P :=
        integral_mono hf2sq' hg2int hpt2
      _ = 2 * ∫ ω, A.indicator (fun ω => fro (dynErrM p S a q ω) ^ 2 +
          fro (dynErrS p S a q ω) ^ 2) ω ∂P + 2 * ∫ ω, A.indicator (fun ω => fro (dynErrV p S a q ω) ^ 2) ω ∂P := by
        rw [integral_add (hFAint.const_mul 2) (hGAint.const_mul 2), integral_const_mul, integral_const_mul]
      _ ≤ c2 * (q : ℝ) ^ 2 := by
        have h1 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
        have hc : 0 ≤ K2' * (Cbuf + 1) := by positivity
        simp only [c2]
        nlinarith [mul_le_mul_of_nonneg_left h1 hc]
  obtain ⟨hf2int, hf2le⟩ := prefix_amgm f2 hf2meas.aestronglyMeasurable hf20 hf2sq' q hqpos
  -- pointwise domination
  have key : ∀ ω ∈ A, |frobIP (W (dynDelta S u ω)) (dynUpd S u ω)| ≤
      |frobIP (W (dynDelta S a ω)) (V ω)| + Tb * fro (dynUpd S u ω - V ω) +
        Kmv * |cW| * (q : ℝ) := by
    intro ω hω
    have hD := hAK ω hω
    have hD' : dynDelta S a ω ∈ admAplus p S.C := hD
    have hmvb := hmv Ω P m n B S cW W hBmv hBpos hW a q ω hq4 hD'
    rw [hau] at hmvb
    have e1 : dynDelta S u ω = dynDelta S a ω + (dynDelta S u ω - dynDelta S a ω) := by abel
    have e2 : frobIP (W (dynDelta S a ω)) (dynUpd S u ω) =
        frobIP (W (dynDelta S a ω)) (V ω) +
          frobIP (W (dynDelta S a ω)) (dynUpd S u ω - V ω) := by
      rw [← prefix_frobIP_add_right]; congr 1; abel
    have hWD : fro (W (dynDelta S a ω)) ≤ Tb := by
      refine (hW _).trans ?_
      have : fro (dynDelta S a ω) ≤ Real.sqrt (enl (admBase p)).2.2 :=
        Real.le_sqrt_of_sq_le hD.2.2
      exact mul_le_mul_of_nonneg_left this hcW
    have h3 : |frobIP (W (dynDelta S a ω)) (dynUpd S u ω - V ω)| ≤ Tb * fro (dynUpd S u ω - V ω) :=
      (projection_frobIP_le _ _).trans (mul_le_mul_of_nonneg_right hWD (Real.sqrt_nonneg _))
    calc |frobIP (W (dynDelta S u ω)) (dynUpd S u ω)|
        = |frobIP (W (dynDelta S a ω + (dynDelta S u ω - dynDelta S a ω))) (dynUpd S u ω)| := by
          rw [← e1]
      _ = |frobIP (W (dynDelta S a ω)) (V ω) +
            frobIP (W (dynDelta S a ω)) (dynUpd S u ω - V ω) +
            frobIP (W (dynDelta S u ω - dynDelta S a ω)) (dynUpd S u ω)| := by
          rw [map_add, prefix_frobIP_add_left, e2]
      _ ≤ |frobIP (W (dynDelta S a ω)) (V ω)| +
            |frobIP (W (dynDelta S a ω)) (dynUpd S u ω - V ω)| +
            |frobIP (W (dynDelta S u ω - dynDelta S a ω)) (dynUpd S u ω)| := abs_add_three _ _ _
      _ ≤ _ := by linarith
  set X : Ω → ℝ := A.indicator (fun ω => |frobIP (W (dynDelta S u ω)) (dynUpd S u ω)|) with hX
  have hdomint : Integrable (fun ω => f1 ω + Tb * f2 ω +
      A.indicator (fun _ => Kmv * |cW| * (q : ℝ)) ω) P :=
    (hf1int.add (hf2int.const_mul Tb)).add (hconstA _ (by positivity)).1
  have hXmeas : AEStronglyMeasurable X P :=
    ((prefix_meas_abs_frobIP W (dynDelta S u) (dynUpd S u) hΔu hupd.aemeasurable).indicator
      hAam).aestronglyMeasurable
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => Set.indicator_nonneg (fun _ _ => abs_nonneg _) ω
  have hXle : ∀ ω, X ω ≤ f1 ω + Tb * f2 ω + A.indicator (fun _ => Kmv * |cW| * (q : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [X, f1, f2, Set.indicator_of_mem hω]
      exact key ω hω
    · simp [X, f1, f2, Set.indicator_of_notMem hω]
  have hXint : Integrable X P :=
    hdomint.mono' hXmeas (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]; exact hXle ω)
  refine ⟨hXint, ?_⟩
  have e1 : ∫ ω, f1 ω ∂P ≤ (2 * Ks + 1) / 2 * (q : ℝ) := by
    refine hf1le.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have e2 : ∫ ω, f2 ω ∂P ≤ (c2 + 1) / 2 * (q : ℝ) := by
    refine hf2le.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have e3 := (hconstA (Kmv * |cW| * (q : ℝ)) (by positivity)).2
  calc ∫ ω, X ω ∂P ≤ ∫ ω, (f1 ω + Tb * f2 ω +
        A.indicator (fun _ => Kmv * |cW| * (q : ℝ)) ω) ∂P := integral_mono hXint hdomint hXle
    _ = ∫ ω, f1 ω ∂P + Tb * ∫ ω, f2 ω ∂P + ∫ ω, A.indicator (fun _ => Kmv * |cW| * (q : ℝ)) ω ∂P := by
      have i1 : Integrable (fun ω => f1 ω + Tb * f2 ω) P := hf1int.add (hf2int.const_mul Tb)
      have h1 := integral_add i1 (hconstA (Kmv * |cW| * (q : ℝ)) (by positivity)).1
      have h2 := integral_add hf1int (hf2int.const_mul Tb)
      rw [h1, h2, integral_const_mul]
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left e2 hTb
      nlinarith

/-- `lem:app-dyn-prefix` (cr-2026-10-23), part (i). Let `𝒲` be a linear map with `‖𝒲‖_{F→F} ≤ c_W`, i.e.
`‖𝒲X‖_F ≤ c_W ‖X‖_F` for all `X`. For every `u ≥ 𝗊`, `𝔼[𝟙_{u−𝗊<τ⁺} |⟨𝒲Δ_u, 𝖲_u⟩|] ≤ C𝗊`. The constant `K` depends on
the fixed parameters and `c_W`. Statement verbatim from `section.tex` (ll. 1837–1853):
```latex
\begin{lemma}[Delayed projections and prefixes]\label{lem:app-dyn-prefix}
Let $\mathcal W$ be a linear map on $\R^{\Nout\times\Nin}$ with $\norm{\mathcal W}_{\F\to\F}\le c_W$.
\begin{enumerate}[label=(\roman*)]
\item For every $u\ge\mathsf q$, $\EE\big[\mathbf 1_{u-\mathsf q<\tau^+}\abs{\langle\mathcal W\Delta_u,{\mathsf S}_u\rangle}\big]\le C\mathsf q$.
\item For every $t\ge\mathsf q$, $\EE\big[\mathbf 1_{t<\tau^+}\big|\sum_{r<\mathsf q}\langle\mathcal W\Dt,{\mathsf S}_{t+r}\rangle\big|\big]\le C\mathsf q^2$.
\item For every $t\ge\mathsf q$, with the chains at time $t$ and $0\le r\le\mathsf q$,
$\EE\big[\mathbf 1_{t<\tau^+}\abs{\langle\Sigmaout\Dt\Sigmain,\widehat V_r-V_r\rangle}\big]\le\min\big(C\mathsf q,\ C\sqrt B\bmom^{r+1}\big)$,
and for every $r\ge0$ the second bound holds.
\end{enumerate}
Consequently, with $\Omega_\bmom(\epsilon)\defeq\sum_{r\ge0}\min(\epsilon,\bmom^{r+1})$
and $\epsilon_B\defeq\mathsf q/\sqrt B$,
\begin{equation}\label{eqn:app-dyn-envelope}
\frac{1}{\sqrt B}\sum_{r<L}\EE\big[\mathbf 1_{t<\tau^+}\abs{\langle\Sigmaout\Dt\Sigmain,\widehat V_r-V_r\rangle}\big]\le C\big(\Omega_\bmom(\epsilon_B)+\bmom^{\mathsf q}\big),
\end{equation}
and $\Omega_\bmom(\epsilon)\le C\epsilon(1+\log(1/\epsilon))$ for $0<\epsilon\le1$, with
$\Omega_0=0$.
\end{lemma}
```
-/
theorem lem_app_dyn_prefix_i (certP : Muon.External.GaussianPoincare) (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∀ cW : ℝ, 0 ≤ cW → ∃ B0 : ℕ, ∃ K : ℝ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (m n B : ℕ) (S : DynSetup p P m n B) (W : Mat m n →ₗ[ℝ] Mat m n),
        B0 ≤ B → (∀ X : Mat m n, fro (W X) ≤ cW * fro X) →
        ∀ u : ℕ, prefixLen p.β B ≤ u →
          Integrable ({ω | ((u - prefixLen p.β B : ℕ) : ℕ∞) < tauPlus p S ω}.indicator
            (fun ω => |frobIP (W (dynDelta S u ω)) (dynUpd S u ω)|)) P ∧
          ∫ ω, {ω | ((u - prefixLen p.β B : ℕ) : ℕ∞) < tauPlus p S ω}.indicator
            (fun ω => |frobIP (W (dynDelta S u ω)) (dynUpd S u ω)|) ω ∂P
            ≤ K * (prefixLen p.β B : ℝ) := by
  exact prefix_i_core certP certOp p

/-- `lem:app-dyn-prefix` (cr-2026-10-23), part (ii). With `𝒲` as in part (i), for every `t ≥ 𝗊`,
`𝔼[𝟙_{t<τ⁺} |∑_{r<𝗊} ⟨𝒲Δ_t, 𝖲_{t+r}⟩|] ≤ C𝗊²`. Statement verbatim from `section.tex` (ll. 1837–1853):
```latex
\begin{lemma}[Delayed projections and prefixes]\label{lem:app-dyn-prefix}
Let $\mathcal W$ be a linear map on $\R^{\Nout\times\Nin}$ with $\norm{\mathcal W}_{\F\to\F}\le c_W$.
\begin{enumerate}[label=(\roman*)]
\item For every $u\ge\mathsf q$, $\EE\big[\mathbf 1_{u-\mathsf q<\tau^+}\abs{\langle\mathcal W\Delta_u,{\mathsf S}_u\rangle}\big]\le C\mathsf q$.
\item For every $t\ge\mathsf q$, $\EE\big[\mathbf 1_{t<\tau^+}\big|\sum_{r<\mathsf q}\langle\mathcal W\Dt,{\mathsf S}_{t+r}\rangle\big|\big]\le C\mathsf q^2$.
\item For every $t\ge\mathsf q$, with the chains at time $t$ and $0\le r\le\mathsf q$,
$\EE\big[\mathbf 1_{t<\tau^+}\abs{\langle\Sigmaout\Dt\Sigmain,\widehat V_r-V_r\rangle}\big]\le\min\big(C\mathsf q,\ C\sqrt B\bmom^{r+1}\big)$,
and for every $r\ge0$ the second bound holds.
\end{enumerate}
Consequently, with $\Omega_\bmom(\epsilon)\defeq\sum_{r\ge0}\min(\epsilon,\bmom^{r+1})$
and $\epsilon_B\defeq\mathsf q/\sqrt B$,
\begin{equation}\label{eqn:app-dyn-envelope}
\frac{1}{\sqrt B}\sum_{r<L}\EE\big[\mathbf 1_{t<\tau^+}\abs{\langle\Sigmaout\Dt\Sigmain,\widehat V_r-V_r\rangle}\big]\le C\big(\Omega_\bmom(\epsilon_B)+\bmom^{\mathsf q}\big),
\end{equation}
and $\Omega_\bmom(\epsilon)\le C\epsilon(1+\log(1/\epsilon))$ for $0<\epsilon\le1$, with
$\Omega_0=0$.
\end{lemma}
```
-/
theorem lem_app_dyn_prefix_ii (certP : Muon.External.GaussianPoincare) (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∀ cW : ℝ, 0 ≤ cW → ∃ B0 : ℕ, ∃ K : ℝ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (m n B : ℕ) (S : DynSetup p P m n B) (W : Mat m n →ₗ[ℝ] Mat m n),
        B0 ≤ B → (∀ X : Mat m n, fro (W X) ≤ cW * fro X) →
        ∀ t : ℕ, prefixLen p.β B ≤ t →
          Integrable ({ω | (t : ℕ∞) < tauPlus p S ω}.indicator
            (fun ω => |(∑ r ∈ Finset.range (prefixLen p.β B), frobIP (W (dynDelta S t ω)) (dynUpd S (t + r) ω))|)) P ∧
          ∫ ω, {ω | (t : ℕ∞) < tauPlus p S ω}.indicator
            (fun ω => |(∑ r ∈ Finset.range (prefixLen p.β B), frobIP (W (dynDelta S t ω)) (dynUpd S (t + r) ω))|) ω ∂P
            ≤ K * (prefixLen p.β B : ℝ) ^ 2 := by
  intro cW hcW
  obtain ⟨B0i, Ki, hi⟩ := lem_app_dyn_prefix_i certP certOp p cW hcW
  obtain ⟨Bmv, Kmv, hKmv0, hmv⟩ := prefix_move_term p
  obtain ⟨B1, hB1⟩ := prefix_q_le_L p.β
  refine ⟨max (max B0i Bmv) (max B1 1), Ki + Kmv * |cW|, ?_⟩
  intro Ω mΩ P hP m n B S W hBge hW t ht
  have hBs : (B0i ≤ B ∧ Bmv ≤ B) ∧ (B1 ≤ B ∧ 1 ≤ B) := by
    simpa only [max_le_iff] using hBge
  obtain ⟨⟨hBi, hBmv⟩, hB1', hB1le⟩ := hBs
  obtain ⟨-, hqL⟩ := hB1 B hB1'
  have hBpos : 0 < B := hB1le
  set q := prefixLen p.β B with hqdef
  have hq4 : q ≤ 4 * blockLen B := by omega
  have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  set A : Set Ω := {ω | (t : ℕ∞) < tauPlus p S ω} with hA
  have hAam : MeasurableSet A := concentration_past_le S t _ (concentration_tauPlus_meas S t)
  have hfr : ∀ r ∈ Finset.range q, Integrable ({ω | ((t + r - q : ℕ) : ℕ∞) < tauPlus p S ω}.indicator
        (fun ω => |frobIP (W (dynDelta S (t + r) ω)) (dynUpd S (t + r) ω)|)) P ∧
      ∫ ω, {ω | ((t + r - q : ℕ) : ℕ∞) < tauPlus p S ω}.indicator
        (fun ω => |frobIP (W (dynDelta S (t + r) ω)) (dynUpd S (t + r) ω)|) ω ∂P ≤ Ki * (q : ℝ) :=
    fun r hr => hi Ω P m n B S W hBi hW (t + r) (by omega)
  let fr : ℕ → Ω → ℝ := fun r => {ω | ((t + r - q : ℕ) : ℕ∞) < tauPlus p S ω}.indicator
        (fun ω => |frobIP (W (dynDelta S (t + r) ω)) (dynUpd S (t + r) ω)|)
  have hcpos : 0 ≤ Kmv * |cW| * (q : ℝ) ^ 2 := by positivity
  have hconstA : Integrable (A.indicator (fun _ => Kmv * |cW| * (q : ℝ) ^ 2)) P ∧
      ∫ ω, A.indicator (fun _ => Kmv * |cW| * (q : ℝ) ^ 2) ω ∂P ≤ Kmv * |cW| * (q : ℝ) ^ 2 := by
    refine ⟨(integrable_const _).indicator hAam, ?_⟩
    rw [integral_indicator hAam, setIntegral_const, smul_eq_mul]
    nlinarith [(measureReal_nonneg : 0 ≤ P.real A), measureReal_le_one (μ := P) (s := A)]
  have hdomint : Integrable (fun ω => ∑ r ∈ Finset.range q, fr r ω +
      A.indicator (fun _ => Kmv * |cW| * (q : ℝ) ^ 2) ω) P :=
    (integrable_finsetSum _ fun r hr => (hfr r hr).1).add hconstA.1
  set Y : Ω → ℝ := A.indicator (fun ω =>
    |(∑ r ∈ Finset.range q, frobIP (W (dynDelta S t ω)) (dynUpd S (t + r) ω))|) with hY
  have hfc := prefix_frobIP_cont W
  have hΔt : Measurable (dynDelta S t) :=
    (concentration_delta_meas S t).mono (concentration_past_le S t) le_rfl
  have hYmeas : AEStronglyMeasurable Y P := by
    have hm : AEMeasurable (fun ω => |(∑ r ∈ Finset.range q,
        frobIP (W (dynDelta S t ω)) (dynUpd S (t + r) ω))|) P := by
      have hs : AEMeasurable (fun ω => ∑ r ∈ Finset.range q,
          frobIP (W (dynDelta S t ω)) (dynUpd S (t + r) ω)) P := by
        refine Finset.aemeasurable_fun_sum _ fun r _ => ?_
        have hu : Measurable (dynUpd S (t + r)) :=
          (concentration_upd_meas S (t + r)).mono (concentration_past_le S (t + r + 1)) le_rfl
        exact prefix_meas_frobIP W (dynDelta S t) (dynUpd S (t + r)) hΔt hu.aemeasurable
      exact continuous_abs.measurable.comp_aemeasurable hs
    exact (hm.indicator hAam).aestronglyMeasurable
  have hYle : ∀ ω, Y ω ≤ ∑ r ∈ Finset.range q, fr r ω +
      A.indicator (fun _ => Kmv * |cW| * (q : ℝ) ^ 2) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [hY, Set.indicator_of_mem hω]
      have hD : dynDelta S t ω ∈ admAplus p S.C := (concentration_tauPlus_iff S t ω).1 hω t le_rfl
      have hterm : ∀ r ∈ Finset.range q,
          |frobIP (W (dynDelta S t ω)) (dynUpd S (t + r) ω)| ≤ fr r ω + Kmv * |cW| * (r : ℝ) := by
        intro r hr
        have hrq : r < q := Finset.mem_range.1 hr
        have hmvb := hmv Ω P m n B S cW W hBmv hBpos hW t r ω (by omega) hD
        have hmem : ω ∈ {ω | ((t + r - q : ℕ) : ℕ∞) < tauPlus p S ω} := by
          change ((t + r - q : ℕ) : ℕ∞) < tauPlus p S ω
          rw [concentration_tauPlus_iff]
          intro s hs
          exact (concentration_tauPlus_iff S t ω).1 hω s (by omega)
        have hfr' : fr r ω = |frobIP (W (dynDelta S (t + r) ω)) (dynUpd S (t + r) ω)| := by
          simp only [fr, Set.indicator_of_mem hmem]
        rw [hfr']
        have e1 : frobIP (W (dynDelta S (t + r) ω)) (dynUpd S (t + r) ω) =
            frobIP (W (dynDelta S t ω)) (dynUpd S (t + r) ω) +
            frobIP (W (dynDelta S (t + r) ω - dynDelta S t ω)) (dynUpd S (t + r) ω) := by
          rw [← prefix_frobIP_add_left, ← map_add]; congr 2; abel
        have e2 : frobIP (W (dynDelta S t ω)) (dynUpd S (t + r) ω) =
            frobIP (W (dynDelta S (t + r) ω)) (dynUpd S (t + r) ω) -
            frobIP (W (dynDelta S (t + r) ω - dynDelta S t ω)) (dynUpd S (t + r) ω) := by
          linarith
        rw [e2]
        calc _ ≤ |frobIP (W (dynDelta S (t + r) ω)) (dynUpd S (t + r) ω)| +
              |frobIP (W (dynDelta S (t + r) ω - dynDelta S t ω)) (dynUpd S (t + r) ω)| := abs_sub _ _
          _ ≤ _ := by linarith
      calc |∑ r ∈ Finset.range q, frobIP (W (dynDelta S t ω)) (dynUpd S (t + r) ω)|
          ≤ ∑ r ∈ Finset.range q, |frobIP (W (dynDelta S t ω)) (dynUpd S (t + r) ω)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ r ∈ Finset.range q, (fr r ω + Kmv * |cW| * (r : ℝ)) := Finset.sum_le_sum hterm
        _ = ∑ r ∈ Finset.range q, fr r ω + Kmv * |cW| * ∑ r ∈ Finset.range q, (r : ℝ) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ _ := by
            have hs : ∑ r ∈ Finset.range q, (r : ℝ) ≤ (q : ℝ) ^ 2 := by
              calc ∑ r ∈ Finset.range q, (r : ℝ) ≤ ∑ _r ∈ Finset.range q, (q : ℝ) :=
                    Finset.sum_le_sum fun r hr => by exact_mod_cast (Finset.mem_range.1 hr).le
                _ = (q : ℝ) ^ 2 := by simp [sq]
            have := mul_le_mul_of_nonneg_left hs (mul_nonneg hKmv0 (abs_nonneg cW))
            linarith
    · simp only [hY, Set.indicator_of_notMem hω]
      have : 0 ≤ ∑ r ∈ Finset.range q, fr r ω :=
        Finset.sum_nonneg fun r _ => Set.indicator_nonneg (fun _ _ => abs_nonneg _) ω
      simpa using this
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => Set.indicator_nonneg (fun _ _ => abs_nonneg _) ω
  have hYint : Integrable Y P :=
    hdomint.mono' hYmeas (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hY0 ω)]; exact hYle ω)
  refine ⟨hYint, ?_⟩
  calc ∫ ω, Y ω ∂P ≤ ∫ ω, (∑ r ∈ Finset.range q, fr r ω +
        A.indicator (fun _ => Kmv * |cW| * (q : ℝ) ^ 2) ω) ∂P := integral_mono hYint hdomint hYle
    _ = ∑ r ∈ Finset.range q, ∫ ω, fr r ω ∂P +
        ∫ ω, A.indicator (fun _ => Kmv * |cW| * (q : ℝ) ^ 2) ω ∂P := by
      rw [integral_add (integrable_finsetSum _ fun r hr => (hfr r hr).1) hconstA.1,
        integral_finsetSum _ fun r hr => (hfr r hr).1]
    _ ≤ ∑ _r ∈ Finset.range q, Ki * (q : ℝ) + Kmv * |cW| * (q : ℝ) ^ 2 :=
      add_le_add (Finset.sum_le_sum fun r hr => (hfr r hr).2) hconstA.2
    _ = (Ki + Kmv * |cW|) * (q : ℝ) ^ 2 := by simp; ring

private def prefixSigmaLM {m n : ℕ} (C : Covariances m n) :
    Mat m n →ₗ[ℝ] Mat m n where
  toFun X := C.Sout * X * C.Sin
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

private lemma prefixSigmaLM_apply {m n : ℕ} (C : Covariances m n) (X : Mat m n) :
    prefixSigmaLM C X = C.Sout * X * C.Sin := rfl

open scoped Matrix.Norms.L2Operator in
private lemma prefixSigmaLM_bound (p : DynParams) {m n B : ℕ}
    (C : Covariances m n) (hsize : SizeFin C B p.γstar p.CSig) (X : Mat m n) :
    fro (prefixSigmaLM C X) ≤ p.CSig ^ 2 * fro X := by
  have ho0 : 0 ≤ opNorm C.Sout := by rw [opNorm_eq_norm]; exact norm_nonneg _
  have hi0 : 0 ≤ opNorm C.Sin := by rw [opNorm_eq_norm]; exact norm_nonneg _
  have hC0 : 0 ≤ p.CSig := le_trans zero_le_one p.hC
  have ho2 : opNorm C.Sout ^ 2 ≤ p.CSig ^ 2 := by nlinarith [hsize.2.1]
  have hi2 : opNorm C.Sin ^ 2 ≤ p.CSig ^ 2 := by nlinarith [hsize.2.2]
  have hleft := projection_fro_mul_sq_le_left C.Sout X
  have hright := projection_fro_mul_sq_le_right (C.Sout * X) C.Sin
  have hleft' : fro (C.Sout * X) ^ 2 ≤ p.CSig ^ 2 * fro X ^ 2 :=
    hleft.trans (mul_le_mul_of_nonneg_right ho2 (sq_nonneg _))
  have hright' : fro (C.Sout * X * C.Sin) ^ 2 ≤
      (p.CSig ^ 2 * fro X ^ 2) * p.CSig ^ 2 :=
    hright.trans (mul_le_mul hleft' hi2 (sq_nonneg _) (by positivity))
  rw [prefixSigmaLM_apply]
  have h0 : 0 ≤ fro (C.Sout * X * C.Sin) := Real.sqrt_nonneg _
  have h1 : 0 ≤ p.CSig ^ 2 * fro X := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [sq_nonneg (p.CSig ^ 2 * fro X)]

private lemma prefix_risk_comp_meas {Ω : Type*} {σ : MeasurableSpace Ω} {m n : ℕ}
    (C : Covariances m n) {D : Ω → Mat m n} (hD : Measurable[σ] D) :
    Measurable[σ] (fun ω => riskSigma C (D ω)) :=
  (show Continuous (fun D : Mat m n => riskSigma C D) by
    unfold riskSigma pairSigma
    fun_prop).measurable.comp hD

private lemma prefix_phys_meas {Ω : Type*} [MeasurableSpace Ω] {m n B : ℕ}
    (C : Covariances m n) {z : Fin B → Ω → Vec m × Vec n} (hz : ∀ a, Measurable (z a)) :
    Measurable (fun ω => physBatch C z ω) := by
  refine measurable_pi_iff.mpr (fun a => ?_)
  exact (show Continuous (fun z : Vec m × Vec n => phys C z) by
    unfold phys
    fun_prop).measurable.comp (hz a)

set_option maxHeartbeats 1000000 in
private lemma prefix_ema_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ)
    {D : Ω → Mat m n} (hD : Measurable D) {init : Ω → Mat m n} (hinit : Measurable init)
    (k : ℕ) :
    Measurable (fun ω => emaChain p.β (D ω) (fun s => physBatch S.C (S.cs.act s) ω) t (init ω) k) := by
  induction k with
  | zero => simpa [emaChain] using hinit
  | succ k ih =>
    have hb : Measurable (fun ω => batchGrad (D ω)
        (physBatch S.C (S.cs.act ((t : ℤ) + k + 1)) ω)) :=
      concentration_grad_meas hD (prefix_phys_meas S.C (fun a => S.cs.meas_act _ a))
    simp only [emaChain]
    exact (ih.const_smul p.β).add (hb.const_smul (1 - p.β))

set_option maxHeartbeats 1000000 in
private lemma prefix_chainInit_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
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
  exact concentration_grad_meas hD (prefix_phys_meas S.C (fun a => S.cs.meas_aux _ j a))

private lemma prefix_Q_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B)
    {D : Ω → Mat m n} (hD : Measurable D) {M : Ω → Mat m n} (hM : Measurable M) :
    Measurable (fun ω => Q (physRidge p S.C (D ω)) (M ω)) := by
  have hρ : ∀ ω, 0 ≤ physRidge p S.C (D ω) := fun ω => by
    unfold physRidge
    exact mul_nonneg (mul_nonneg (by norm_num)
      (by rw [eqn_app_setup_whitened_risk]; positivity)) p.hϱ.le
  have hρm : Measurable (fun ω => (⟨physRidge p S.C (D ω), hρ ω⟩ : Set.Ici (0 : ℝ))) :=
    (((prefix_risk_comp_meas S.C hD).const_mul 2).mul_const p.ϱ).subtype_mk
  exact measurable_Q.comp (hρm.prodMk hM)

private lemma prefix_errV_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t r : ℕ) :
    Measurable (dynErrV p S t r) := by
  have hD : Measurable (dynDelta S t) :=
    (concentration_delta_meas S t).mono (concentration_past_le S t) le_rfl
  have hM : Measurable (dynBuf S t) :=
    (concentration_state_meas S t).2.mono (concentration_past_le S t) le_rfl
  have hhatN : Measurable (dynHatN p S t r) :=
    prefix_ema_meas S t hD hM (r + 1)
  have hhatV : Measurable (dynHatV p S t r) := prefix_Q_meas S hD hhatN
  have hinit : Measurable (fun ω => chainInit p.β S.C (dynDelta S t ω)
      (S.cs.aux (t : ℤ)) ω) := prefix_chainInit_meas S t hD
  have hstatN : Measurable (fun ω => emaChain p.β (dynDelta S t ω)
      (fun s => physBatch S.C (S.cs.act s) ω) t
      (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1)) :=
    prefix_ema_meas S t hD hinit (r + 1)
  have hstatV : Measurable (fun ω => stationaryV p S.C S.cs t (dynDelta S t ω) r ω) :=
    prefix_Q_meas S hD hstatN
  exact hhatV.sub hstatV

private lemma prefix_errS_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (hB : 0 < B) (t r : ℕ) :
    Measurable (dynErrS p S t r) := by
  have hD : Measurable (dynDelta S t) :=
    (concentration_delta_meas S t).mono (concentration_past_le S t) le_rfl
  have hM : Measurable (dynBuf S t) :=
    (concentration_state_meas S t).2.mono (concentration_past_le S t) le_rfl
  have hhatN : Measurable (dynHatN p S t r) :=
    prefix_ema_meas S t hD hM (r + 1)
  have hhatV : Measurable (dynHatV p S t r) := prefix_Q_meas S hD hhatN
  have hu : Measurable (dynUpd S (t + r)) :=
    (concentration_upd_meas S (t + r)).mono (concentration_past_le S (t + r + 1)) le_rfl
  exact hu.sub hhatV

private lemma prefix_sq_integral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    (hfsq : Integrable (fun ω => f ω ^ 2) P) :
    (∫ ω, f ω ∂P) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂P := by
  have hmem : MemLp f 2 P := (memLp_two_iff_integrable_sq hf).2 hfsq
  have h1 := variance_eq_sub hmem
  have h2 := variance_nonneg f P
  simp only [Pi.pow_apply] at h1
  nlinarith

private lemma prefix_rpow_sq {x : ℝ} (hx : 0 < x) :
    (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num
  exact Real.rpow_neg_one x

private lemma prefix_errV_path (p : DynParams) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (rlo : ℝ) (hrlo : 0 < rlo)
    (t r : ℕ) (ω : Ω) (h0 : rlo ≤ riskSigma S.C (dynDelta S t ω)) :
    fro (dynErrV p S t r ω) ^ 2 ≤
      2 * (rlo * p.ϱ)⁻¹ * p.β ^ (2 * (r + 1)) *
        (fro (dynBuf S t ω) ^ 2 +
          fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2) := by
  have hϱo : 0 < rlo * p.ϱ := mul_pos hrlo p.hϱ
  have hϱ0 : rlo * p.ϱ ≤ physRidge p S.C (dynDelta S t ω) := by
    unfold physRidge
    nlinarith
  have hρpos : 0 < physRidge p S.C (dynDelta S t ω) := lt_of_lt_of_le hϱo hϱ0
  have h1 := lem_app_setup_filter_iii _ hρpos (dynHatN p S t r ω)
    (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
      (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1))
  have hdiff := lem_app_dyn_chains_ii p S.C S.cs t (dynDelta S t ω) (dynBuf S t ω) ω (r + 1)
  have h1' : fro (dynErrV p S t r ω) ≤
      (physRidge p S.C (dynDelta S t ω)) ^ (-(1 / 2 : ℝ)) *
        fro ((p.β ^ (r + 1)) • (dynBuf S t ω -
          chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) := by
    change fro (Q (physRidge p S.C (dynDelta S t ω)) (dynHatN p S t r ω) -
      Q (physRidge p S.C (dynDelta S t ω))
        (emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
          (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1))) ≤ _
    calc
      _ ≤ (physRidge p S.C (dynDelta S t ω)) ^ (-(1 / 2 : ℝ)) *
          fro (dynHatN p S t r ω -
            emaChain p.β (dynDelta S t ω) (fun s => physBatch S.C (S.cs.act s) ω) t
              (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) (r + 1)) := h1
      _ = _ := congrArg (fun X =>
        (physRidge p S.C (dynDelta S t ω)) ^ (-(1 / 2 : ℝ)) * fro X) hdiff
  have hsmul : fro ((p.β ^ (r + 1)) •
      (dynBuf S t ω - chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) =
      p.β ^ (r + 1) * fro (dynBuf S t ω -
        chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) := by
    open scoped Matrix.Norms.Frobenius in
      simp only [fro_eq_norm, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg p.hβ.1 _)]
  rw [hsmul] at h1'
  have hsub : fro (dynBuf S t ω -
      chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ≤
      fro (dynBuf S t ω) +
        fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) := by
    open scoped Matrix.Norms.Frobenius in
      simpa only [fro_eq_norm] using norm_sub_le (dynBuf S t ω)
        (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)
  have hq : (physRidge p S.C (dynDelta S t ω)) ^ (-(1 / 2 : ℝ)) ≤
      (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hϱo hϱ0 (by norm_num)
  have hb0 := pow_nonneg p.hβ.1 (r + 1)
  have hbound : fro (dynErrV p S t r ω) ≤
      (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) * p.β ^ (r + 1) *
      (fro (dynBuf S t ω) +
        fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) := by
    refine h1'.trans ?_
    calc
      _ ≤ (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) *
          (p.β ^ (r + 1) * fro (dynBuf S t ω -
            chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) :=
        mul_le_mul_of_nonneg_right hq
          (mul_nonneg hb0 (Real.sqrt_nonneg _))
      _ ≤ (rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) *
          (p.β ^ (r + 1) * (fro (dynBuf S t ω) +
            fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsub hb0)
          (Real.rpow_nonneg hϱo.le _)
      _ = _ := by ring
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hbound 2
  have hadd : (fro (dynBuf S t ω) +
      fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω)) ^ 2 ≤
      2 * (fro (dynBuf S t ω) ^ 2 +
        fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2) := by
    nlinarith [sq_nonneg (fro (dynBuf S t ω) -
      fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω))]
  refine hsq.trans ?_
  have hr2 := prefix_rpow_sq hϱo
  have hb2 : p.β ^ (2 * (r + 1)) = (p.β ^ (r + 1)) ^ 2 := by
    rw [← pow_mul]
    ring_nf
  rw [hb2, mul_pow, mul_pow, hr2]
  have hc : 0 ≤ (rlo * p.ϱ)⁻¹ * (p.β ^ (r + 1)) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hadd hc]

private lemma prefix_chainInit_bound (p : DynParams) :
    ∃ Cinit : ℝ, 0 ≤ Cinit ∧ ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (m n B : ℕ) (S : DynSetup p P m n B) (t : ℕ) (A : Set Ω),
      MeasurableSet[dynPast S t] A →
      (∀ ω ∈ A, dynDelta S t ω ∈ admSetOf S.C (enl (admBase p))) →
      Integrable (A.indicator (fun ω => fro (chainInit p.β S.C (dynDelta S t ω)
        (S.cs.aux (t : ℤ)) ω) ^ 2)) P ∧
      ∫ ω, A.indicator (fun ω => fro (chainInit p.β S.C (dynDelta S t ω)
        (S.cs.aux (t : ℤ)) ω) ^ 2) ω ∂P ≤ Cinit * (B : ℝ) := by
  let rhi := (enl (admBase p)).2.1
  let CM := cMConst p.CSig p.γstar
  have hrlo : 0 < (enl (admBase p)).1 := by
    simp only [enl, admBase]
    linarith [p.hr0]
  have hrhi : 0 ≤ rhi := by
    dsimp [rhi]
    simp only [enl, admBase]
    linarith [p.hr0, p.hr]
  have hCM : 0 ≤ CM := by unfold CM cMConst; positivity
  refine ⟨2 * rhi * CM, by positivity, ?_⟩
  intro Ω mΩ P hP m n B S t A hAF hAK
  have hAm : MeasurableSet A := concentration_past_le S t _ hAF
  by_cases hne : A.Nonempty
  swap
  · have hA0 : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst hA0
    simp
    positivity
  obtain ⟨ω0, hω0⟩ := hne
  classical
  let D0 := dynDelta S t ω0
  let D' : Ω → Mat m n := fun ω => if ω ∈ A then dynDelta S t ω else D0
  have hD'F : Measurable[dynPast S t] D' :=
    Measurable.ite hAF (concentration_delta_meas S t) measurable_const
  have hD'm : Measurable D' := hD'F.mono (concentration_past_le S t) le_rfl
  have hD'mem : ∀ ω, D' ω ∈ admSetOf S.C (enl (admBase p)) := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [D', if_pos hω]
      exact hAK ω hω
    · simp only [D', if_neg hω, D0]
      exact hAK ω0 hω0
  have hDpos : ∀ ω, 0 < riskSigma S.C (D' ω) :=
    fun ω => hrlo.trans_le (hD'mem ω).1
  have hDint : Integrable (fun ω => riskSigma S.C (D' ω)) P := by
    refine Integrable.of_bound (C := rhi)
      ((concentration_risk_cont S.C).measurable.comp hD'm).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (prefix_risk_nonneg _ _)]
    exact (hD'mem ω).2.1
  have hiv := lem_app_dyn_chains_iv (dynPast S t) p S.C S.cs t S.size
    (concentration_past_le S t) (prefix_indep_past_future S t) D' (dynBuf S t)
    hD'F (concentration_state_meas S t).2 (ae_of_all _ hDpos) hDint
  have hinit : Integrable (fun ω => fro (chainInit p.β S.C (D' ω)
      (S.cs.aux (t : ℤ)) ω) ^ 2) P := by
    simpa only [def_app_dyn_chains, emaChain] using hiv.2.1
  have hcond : ∀ᵐ ω ∂P, condExp (dynPast S t) P (fun ω =>
      fro (chainInit p.β S.C (D' ω) (S.cs.aux (t : ℤ)) ω) ^ 2) ω ≤
      2 * rhi * CM * (B : ℝ) := by
    filter_upwards [hiv.2.2.1] with ω hω
    simpa only [def_app_dyn_chains, emaChain, CM] using
      hω.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (hD'mem ω).2.1 (by norm_num)) hCM) (Nat.cast_nonneg B))
  have hAint : Integrable (A.indicator (fun ω => fro (chainInit p.β S.C (D' ω)
      (S.cs.aux (t : ℤ)) ω) ^ 2)) P := hinit.indicator hAm
  have hAle : ∫ ω, A.indicator (fun ω => fro (chainInit p.β S.C (D' ω)
      (S.cs.aux (t : ℤ)) ω) ^ 2) ω ∂P ≤ 2 * rhi * CM * (B : ℝ) := by
    rw [integral_indicator hAm, ← setIntegral_condExp (concentration_past_le S t) hinit hAF]
    calc
      _ ≤ ∫ _ω in A, 2 * rhi * CM * (B : ℝ) ∂P := by
        apply integral_mono_ae integrable_condExp.integrableOn (integrable_const _).integrableOn
        exact (ae_restrict_iff' hAm).2 (hcond.mono fun ω hω _ => hω)
      _ = P.real A * (2 * rhi * CM * (B : ℝ)) := by
        rw [setIntegral_const, smul_eq_mul]
      _ ≤ _ := by
        have hc : 0 ≤ 2 * rhi * CM * (B : ℝ) := by positivity
        nlinarith [(measureReal_nonneg : 0 ≤ P.real A),
          measureReal_le_one (μ := P) (s := A)]
  have heq : A.indicator (fun ω => fro (chainInit p.β S.C (D' ω)
      (S.cs.aux (t : ℤ)) ω) ^ 2) = A.indicator (fun ω =>
      fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2) := by
    funext ω
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω, D', if_pos hω]
    · simp [Set.indicator_of_notMem hω]
  rw [← heq]
  exact ⟨hAint, hAle⟩

set_option maxHeartbeats 4000000 in
/-- `lem:app-dyn-prefix` (cr-2026-10-23), part (iii). For every `t ≥ 𝗊`, with the chains at time `t`
(`dynHatV`, `stationaryV` at `D = Δ_t`, `m = M°_{t-1}`) and every `r ≥ 0`: for `r ≤ 𝗊`,
`𝔼[𝟙_{t<τ⁺} |⟨Σ_out Δ_t Σ_in, V̂_r − V_r⟩|] ≤ C𝗊` and `≤ C√B β^{r+1}` (the minimum of the two bounds), and for every
`r ≥ 0` the second bound holds. Statement verbatim from `section.tex` (ll. 1837–1853):
```latex
\begin{lemma}[Delayed projections and prefixes]\label{lem:app-dyn-prefix}
Let $\mathcal W$ be a linear map on $\R^{\Nout\times\Nin}$ with $\norm{\mathcal W}_{\F\to\F}\le c_W$.
\begin{enumerate}[label=(\roman*)]
\item For every $u\ge\mathsf q$, $\EE\big[\mathbf 1_{u-\mathsf q<\tau^+}\abs{\langle\mathcal W\Delta_u,{\mathsf S}_u\rangle}\big]\le C\mathsf q$.
\item For every $t\ge\mathsf q$, $\EE\big[\mathbf 1_{t<\tau^+}\big|\sum_{r<\mathsf q}\langle\mathcal W\Dt,{\mathsf S}_{t+r}\rangle\big|\big]\le C\mathsf q^2$.
\item For every $t\ge\mathsf q$, with the chains at time $t$ and $0\le r\le\mathsf q$,
$\EE\big[\mathbf 1_{t<\tau^+}\abs{\langle\Sigmaout\Dt\Sigmain,\widehat V_r-V_r\rangle}\big]\le\min\big(C\mathsf q,\ C\sqrt B\bmom^{r+1}\big)$,
and for every $r\ge0$ the second bound holds.
\end{enumerate}
Consequently, with $\Omega_\bmom(\epsilon)\defeq\sum_{r\ge0}\min(\epsilon,\bmom^{r+1})$
and $\epsilon_B\defeq\mathsf q/\sqrt B$,
\begin{equation}\label{eqn:app-dyn-envelope}
\frac{1}{\sqrt B}\sum_{r<L}\EE\big[\mathbf 1_{t<\tau^+}\abs{\langle\Sigmaout\Dt\Sigmain,\widehat V_r-V_r\rangle}\big]\le C\big(\Omega_\bmom(\epsilon_B)+\bmom^{\mathsf q}\big),
\end{equation}
and $\Omega_\bmom(\epsilon)\le C\epsilon(1+\log(1/\epsilon))$ for $0<\epsilon\le1$, with
$\Omega_0=0$.
\end{lemma}
```
-/
theorem lem_app_dyn_prefix_iii (certP : Muon.External.GaussianPoincare) (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∃ B0 : ℕ, ∃ K : ℝ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (m n B : ℕ) (S : DynSetup p P m n B),
        B0 ≤ B → ∀ t : ℕ, prefixLen p.β B ≤ t → ∀ r : ℕ,
          Integrable ({ω | (t : ℕ∞) < tauPlus p S ω}.indicator
            (fun ω => |frobIP (S.C.Sout * dynDelta S t ω * S.C.Sin) (dynErrV p S t r ω)|)) P ∧
          (r ≤ prefixLen p.β B →
            ∫ ω, {ω | (t : ℕ∞) < tauPlus p S ω}.indicator
              (fun ω => |frobIP (S.C.Sout * dynDelta S t ω * S.C.Sin) (dynErrV p S t r ω)|) ω ∂P
              ≤ K * (prefixLen p.β B : ℝ)) ∧
          ∫ ω, {ω | (t : ℕ∞) < tauPlus p S ω}.indicator
            (fun ω => |frobIP (S.C.Sout * dynDelta S t ω * S.C.Sin) (dynErrV p S t r ω)|) ω ∂P
            ≤ K * Real.sqrt (B : ℝ) * p.β ^ (r + 1) := by
  have hrlo : 0 < (enl (admBase p)).1 := by
    simp only [enl, admBase]
    linarith [p.hr0]
  have hle : (enl (admBase p)).1 ≤ (enl (admBase p)).2.1 := by
    simp only [enl, admBase]
    linarith [p.hr0, p.hr]
  let cW := p.CSig ^ 2
  have hcW : 0 ≤ cW := sq_nonneg _
  obtain ⟨Bc1, K1, hc1⟩ := lem_app_dyn_coupling_i certOp p (enl (admBase p)).1
    (enl (admBase p)).2.1 (enl (admBase p)).2.2 hrlo hle
  obtain ⟨Bpi, Ki, hpi⟩ := lem_app_dyn_prefix_i certP certOp p cW hcW
  obtain ⟨Ks, hKs0, hKs⟩ := prefix_cond_stationary certP certOp p
    (enl (admBase p)).1 (enl (admBase p)).2.1 (enl (admBase p)).2.2
    hrlo hle cW hcW
  obtain ⟨Cbuf, hCbuf0, hbuf⟩ := prefix_buffer_bound p
  obtain ⟨Cinit, hCinit0, hinit⟩ := prefix_chainInit_bound p
  obtain ⟨Bq, hBq⟩ := prefix_q_le_L p.β
  obtain ⟨Bmv, Kmv, hKmv0, hmv⟩ := prefix_move_term p
  let K1' := max K1 0
  let Ki' := max Ki 0
  let Tb := cW * Real.sqrt (enl (admBase p)).2.2
  let cdec := 2 * ((enl (admBase p)).1 * p.ϱ)⁻¹
  let Kfirst := Ki' + Kmv * |cW| + Tb * (K1' + 1) / 2 + (2 * Ks + 1) / 2
  let Kdec := Tb * (cdec + Cbuf + Cinit + 1)
  have hK1' : 0 ≤ K1' := le_max_right _ _
  have hKi' : 0 ≤ Ki' := le_max_right _ _
  have hTb : 0 ≤ Tb := mul_nonneg hcW (Real.sqrt_nonneg _)
  have hcdec : 0 ≤ cdec := by
    dsimp [cdec]
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (mul_pos hrlo p.hϱ).le)
  have hKfirst : 0 ≤ Kfirst := by dsimp [Kfirst]; positivity
  have hKdec : 0 ≤ Kdec := by dsimp [Kdec]; positivity
  refine ⟨max (max (max Bc1 Bpi) (max Bq Bmv)) 1, Kfirst + Kdec, ?_⟩
  intro Ω mΩ P hP m n B S hBge t ht r
  have hBs : ((Bc1 ≤ B ∧ Bpi ≤ B) ∧ (Bq ≤ B ∧ Bmv ≤ B)) ∧ 1 ≤ B := by
    simpa only [max_le_iff] using hBge
  obtain ⟨⟨⟨hBc1, hBpi⟩, ⟨hBq', hBmv⟩⟩, hB1⟩ := hBs
  obtain ⟨-, hqL⟩ := hBq B hBq'
  have hBpos : 0 < B := hB1
  obtain ⟨hlogq, hq1⟩ := prefix_q_ge_log p.β B hB1
  let q := prefixLen p.β B
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq4 : q ≤ 4 * blockLen B := by omega
  let W : Mat m n →ₗ[ℝ] Mat m n := prefixSigmaLM S.C
  have hW : ∀ X : Mat m n, fro (W X) ≤ cW * fro X := by
    intro X
    exact prefixSigmaLM_bound p S.C S.size X
  let A : Set Ω := {ω | (t : ℕ∞) < tauPlus p S ω}
  have hAF : MeasurableSet[dynPast S t] A := concentration_tauPlus_meas S t
  have hAm : MeasurableSet A := concentration_past_le S t _ hAF
  have hAK : ∀ ω ∈ A, dynDelta S t ω ∈ admSetOf S.C (enl (admBase p)) := by
    intro ω hω
    exact (concentration_tauPlus_iff S t ω).1 hω t le_rfl
  have hAJ : ∀ ω ∈ A, (t : ℕ∞) ≤ tauPlus p S ω :=
    fun ω hω => le_of_lt hω
  have hΔt : Measurable (dynDelta S t) :=
    (concentration_delta_meas S t).mono (concentration_past_le S t) le_rfl
  have herrV : Measurable (dynErrV p S t r) := prefix_errV_meas S t r
  obtain ⟨hbufint, hbufbd⟩ := hbuf Ω P m n B S t A hAm hAJ
  obtain ⟨hinitint, hinitbd⟩ := hinit Ω P m n B S t A hAF hAK
  let e2 : Ω → ℝ := A.indicator (fun ω => fro (dynErrV p S t r ω) ^ 2)
  let g2 : Ω → ℝ := fun ω => cdec * p.β ^ (2 * (r + 1)) *
    (A.indicator (fun ω => fro (dynBuf S t ω) ^ 2) ω +
      A.indicator (fun ω => fro (chainInit p.β S.C (dynDelta S t ω)
        (S.cs.aux (t : ℤ)) ω) ^ 2) ω)
  have hg2int : Integrable g2 P := by
    dsimp only [g2]
    exact (hbufint.add hinitint).const_mul _
  have he2meas : AEStronglyMeasurable e2 P := by
    have hm : Measurable (fun ω => fro (dynErrV p S t r ω) ^ 2) := by
      exact ((prefix_fro_cont (m := m) (n := n)).measurable.comp herrV).pow_const 2
    exact (hm.indicator hAm).aestronglyMeasurable
  have he2le : ∀ ω, e2 ω ≤ g2 ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [e2, g2, Set.indicator_of_mem hω]
      exact prefix_errV_path p S (enl (admBase p)).1 hrlo t r ω (hAK ω hω).1
    · simp [e2, g2, Set.indicator_of_notMem hω]
  have he20 : ∀ ω, 0 ≤ e2 ω :=
    fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
  have he2int : Integrable e2 P :=
    hg2int.mono' he2meas (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (he20 ω)]
      exact he2le ω)
  have he2bd : ∫ ω, e2 ω ∂P ≤
      cdec * (Cbuf + Cinit) * p.β ^ (2 * (r + 1)) * (B : ℝ) := by
    calc
      _ ≤ ∫ ω, g2 ω ∂P := integral_mono he2int hg2int he2le
      _ = cdec * p.β ^ (2 * (r + 1)) *
          (∫ ω, A.indicator (fun ω => fro (dynBuf S t ω) ^ 2) ω ∂P +
            ∫ ω, A.indicator (fun ω => fro (chainInit p.β S.C (dynDelta S t ω)
              (S.cs.aux (t : ℤ)) ω) ^ 2) ω ∂P) := by
        rw [integral_const_mul, integral_add hbufint hinitint]
      _ ≤ _ := by
        have hc : 0 ≤ cdec * p.β ^ (2 * (r + 1)) :=
          mul_nonneg hcdec (pow_nonneg p.hβ.1 _)
        have := mul_le_mul_of_nonneg_left (add_le_add hbufbd hinitbd) hc
        nlinarith
  let f : Ω → ℝ := A.indicator (fun ω =>
    |frobIP (W (dynDelta S t ω)) (dynErrV p S t r ω)|)
  have hfmeas : AEStronglyMeasurable f P :=
    ((prefix_meas_abs_frobIP W (dynDelta S t) (dynErrV p S t r) hΔt
      herrV.aemeasurable).indicator hAm).aestronglyMeasurable
  have hf0 : ∀ ω, 0 ≤ f ω :=
    fun ω => Set.indicator_nonneg (fun _ _ => abs_nonneg _) ω
  have hf2le : ∀ ω, f ω ^ 2 ≤ Tb ^ 2 * e2 ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [f, e2, Set.indicator_of_mem hω, sq_abs]
      have hWD : fro (W (dynDelta S t ω)) ≤ Tb := by
        refine (hW _).trans ?_
        exact mul_le_mul_of_nonneg_left
          (Real.le_sqrt_of_sq_le (hAK ω hω).2.2) hcW
      have hip := projection_frobIP_le (W (dynDelta S t ω)) (dynErrV p S t r ω)
      have hs := pow_le_pow_left₀ (abs_nonneg _) hip 2
      have hm : fro (W (dynDelta S t ω)) * fro (dynErrV p S t r ω) ≤
          Tb * fro (dynErrV p S t r ω) :=
        mul_le_mul_of_nonneg_right hWD (Real.sqrt_nonneg _)
      simpa only [mul_pow, sq_abs] using hs.trans (pow_le_pow_left₀
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hm 2)
    · simp [f, e2, Set.indicator_of_notMem hω]
  have hf2int : Integrable (fun ω => f ω ^ 2) P := by
    refine (he2int.const_mul (Tb ^ 2)).mono' (hfmeas.pow 2)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f ω))]
    exact hf2le ω
  obtain ⟨hfint, -⟩ := prefix_amgm f hfmeas hf0 hf2int 1 zero_lt_one
  have hfint0 : 0 ≤ ∫ ω, f ω ∂P := integral_nonneg hf0
  have hfsq : (∫ ω, f ω ∂P) ^ 2 ≤
      Tb ^ 2 * cdec * (Cbuf + Cinit) * p.β ^ (2 * (r + 1)) * (B : ℝ) := by
    refine (prefix_sq_integral_le hfmeas hf2int).trans ?_
    calc
      _ ≤ ∫ ω, Tb ^ 2 * e2 ω ∂P := integral_mono hf2int (he2int.const_mul _) hf2le
      _ = Tb ^ 2 * ∫ ω, e2 ω ∂P := integral_const_mul _ _
      _ ≤ Tb ^ 2 * (cdec * (Cbuf + Cinit) * p.β ^ (2 * (r + 1)) * (B : ℝ)) :=
        mul_le_mul_of_nonneg_left he2bd (sq_nonneg _)
      _ = _ := by ring
  have hcoef : cdec * (Cbuf + Cinit) ≤ (cdec + Cbuf + Cinit + 1) ^ 2 := by
    nlinarith [sq_nonneg (cdec - (Cbuf + Cinit)), hCbuf0, hCinit0]
  have hBcast : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hβpow : 0 ≤ p.β ^ (r + 1) := pow_nonneg p.hβ.1 _
  have hBrsq : Real.sqrt (B : ℝ) ^ 2 = (B : ℝ) := Real.sq_sqrt hBcast
  have hβsq : (p.β ^ (r + 1)) ^ 2 = p.β ^ (2 * (r + 1)) := by
    rw [← pow_mul]
    ring_nf
  have hdec : ∫ ω, f ω ∂P ≤ Kdec * Real.sqrt (B : ℝ) * p.β ^ (r + 1) := by
    have hmul1 := mul_le_mul_of_nonneg_left hcoef (sq_nonneg Tb)
    have hmul := mul_le_mul_of_nonneg_right hmul1
      (mul_nonneg (pow_nonneg p.hβ.1 (2 * (r + 1))) hBcast)
    have hright : 0 ≤ Kdec * Real.sqrt (B : ℝ) * p.β ^ (r + 1) := by positivity
    have hsqright :
        Tb ^ 2 * cdec * (Cbuf + Cinit) * p.β ^ (2 * (r + 1)) * (B : ℝ) ≤
          (Kdec * Real.sqrt (B : ℝ) * p.β ^ (r + 1)) ^ 2 := by
      calc
        Tb ^ 2 * cdec * (Cbuf + Cinit) * p.β ^ (2 * (r + 1)) * (B : ℝ) =
            Tb ^ 2 * (cdec * (Cbuf + Cinit)) *
              (p.β ^ (2 * (r + 1)) * (B : ℝ)) := by ring
        _ ≤ Tb ^ 2 * (cdec + Cbuf + Cinit + 1) ^ 2 *
              (p.β ^ (2 * (r + 1)) * (B : ℝ)) := hmul
        _ = (Kdec * Real.sqrt (B : ℝ) * p.β ^ (r + 1)) ^ 2 := by
          dsimp only [Kdec]
          calc
            Tb ^ 2 * (cdec + Cbuf + Cinit + 1) ^ 2 *
                (p.β ^ (2 * (r + 1)) * (B : ℝ)) =
                Tb ^ 2 * (cdec + Cbuf + Cinit + 1) ^ 2 *
                  Real.sqrt (B : ℝ) ^ 2 * (p.β ^ (r + 1)) ^ 2 := by
              rw [hBrsq, hβsq]
              ring
            _ = (Tb * (cdec + Cbuf + Cinit + 1) * Real.sqrt (B : ℝ)) ^ 2 *
                  (p.β ^ (r + 1)) ^ 2 := by ring
            _ = (Tb * (cdec + Cbuf + Cinit + 1) * Real.sqrt (B : ℝ) *
                  p.β ^ (r + 1)) ^ 2 := by ring
    have hsquares := hfsq.trans hsqright
    nlinarith [sq_nonneg ((∫ ω, f ω ∂P) +
      Kdec * Real.sqrt (B : ℝ) * p.β ^ (r + 1))]
  have hfirst : r ≤ q → ∫ ω, f ω ∂P ≤ Kfirst * (q : ℝ) := by
    intro hrq
    have hr4 : r ≤ 4 * blockLen B := by omega
    let J : Set Ω := {ω | ((t + r - q : ℕ) : ℕ∞) < tauPlus p S ω}
    have hAJsub : A ⊆ J := by
      intro ω hω
      change ((t + r - q : ℕ) : ℕ∞) < tauPlus p S ω
      rw [concentration_tauPlus_iff]
      intro s hs
      exact (concentration_tauPlus_iff S t ω).1 hω s (by omega)
    obtain ⟨huintJ, hubdJ⟩ := hpi Ω P m n B S W hBpi hW (t + r) (by omega)
    let fu : Ω → ℝ := A.indicator (fun ω =>
      |frobIP (W (dynDelta S (t + r) ω)) (dynUpd S (t + r) ω)|)
    have hfuint : Integrable fu P := by
      have heq : fu = A.indicator (J.indicator (fun ω =>
          |frobIP (W (dynDelta S (t + r) ω)) (dynUpd S (t + r) ω)|)) := by
        funext ω
        by_cases hω : ω ∈ A
        · simp only [fu, Set.indicator_of_mem hω, Set.indicator_of_mem (hAJsub hω)]
        · simp [fu, Set.indicator_of_notMem hω]
      rw [heq]
      exact huintJ.indicator hAm
    have hfubd : ∫ ω, fu ω ∂P ≤ Ki' * (q : ℝ) := by
      have hdom : ∀ ω, fu ω ≤ J.indicator (fun ω =>
          |frobIP (W (dynDelta S (t + r) ω)) (dynUpd S (t + r) ω)|) ω := by
        intro ω
        by_cases hω : ω ∈ A
        · simp only [fu, Set.indicator_of_mem hω, Set.indicator_of_mem (hAJsub hω)]
          exact le_rfl
        · simp [fu, Set.indicator_of_notMem hω]
          exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) ω
      refine (integral_mono hfuint huintJ hdom).trans (hubdJ.trans ?_)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
    obtain ⟨⟨hS2intK, hScond⟩, -⟩ := hc1 Ω P m n B S hBc1 t r hr4
    have hAKsub : A ⊆ dynInK S t (enl (admBase p)) := fun ω hω => hAK ω hω
    have hconst : Integrable (A.indicator (fun _ => K1' * (r : ℝ) ^ 2)) P ∧
        ∫ ω, A.indicator (fun _ => K1' * (r : ℝ) ^ 2) ω ∂P ≤ K1' * (r : ℝ) ^ 2 := by
      refine ⟨(integrable_const _).indicator hAm, ?_⟩
      rw [integral_indicator hAm, setIntegral_const, smul_eq_mul]
      have hc : 0 ≤ K1' * (r : ℝ) ^ 2 := by positivity
      nlinarith [(measureReal_nonneg : 0 ≤ P.real A),
        measureReal_le_one (μ := P) (s := A)]
    obtain ⟨hS2int, hS2bd'⟩ := prefix_cond_transfer (dynPast S t)
      (concentration_past_le S t) (dynInK S t (enl (admBase p))) A
      (fun ω => fro (dynErrM p S t r ω) ^ 2 + fro (dynErrS p S t r ω) ^ 2)
      (fun _ => K1' * (r : ℝ) ^ 2) hAF hAKsub hS2intK hconst.1
      (hScond.mono fun ω hω hωK => (hω hωK).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
    have hS2bd : ∫ ω, A.indicator (fun ω => fro (dynErrS p S t r ω) ^ 2) ω ∂P ≤
        K1' * (r : ℝ) ^ 2 := by
      have hsmall : ∀ ω, A.indicator (fun ω => fro (dynErrS p S t r ω) ^ 2) ω ≤
          A.indicator (fun ω => fro (dynErrM p S t r ω) ^ 2 +
            fro (dynErrS p S t r ω) ^ 2) ω := by
        intro ω
        by_cases hω : ω ∈ A
        · simp only [Set.indicator_of_mem hω]
          exact le_add_of_nonneg_left (sq_nonneg _)
        · simp [Set.indicator_of_notMem hω]
      have hsmallint : Integrable (A.indicator (fun ω => fro (dynErrS p S t r ω) ^ 2)) P := by
        refine hS2int.mono' ?_ (ae_of_all _ fun ω => ?_)
        · exact ((((prefix_fro_cont (m := m) (n := n)).measurable.comp
            (prefix_errS_meas S hBpos t r)).pow_const 2).indicator hAm).aestronglyMeasurable
        · have hl : 0 ≤ A.indicator (fun ω => fro (dynErrS p S t r ω) ^ 2) ω :=
            Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
          have hr : 0 ≤ A.indicator (fun ω => fro (dynErrM p S t r ω) ^ 2 +
              fro (dynErrS p S t r ω) ^ 2) ω :=
            Set.indicator_nonneg (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) ω
          simpa only [Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hr] using hsmall ω
      exact (integral_mono hsmallint hS2int hsmall).trans (hS2bd'.trans hconst.2)
    let fs : Ω → ℝ := A.indicator (fun ω => fro (dynErrS p S t r ω))
    have hfsmeas : AEMeasurable fs P :=
      (((prefix_fro_cont (m := m) (n := n)).measurable.comp
        (prefix_errS_meas S hBpos t r)).indicator hAm).aemeasurable
    have hfs0 : ∀ ω, 0 ≤ fs ω := fun ω =>
      Set.indicator_nonneg (fun _ _ => Real.sqrt_nonneg _) ω
    have hfsqeq : (fun ω => fs ω ^ 2) =
        A.indicator (fun ω => fro (dynErrS p S t r ω) ^ 2) := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [fs, Set.indicator, hω]
    have hfsqint : Integrable (fun ω => fs ω ^ 2) P := by
      rw [hfsqeq]
      exact hS2int.mono' (((((prefix_fro_cont (m := m) (n := n)).measurable.comp
        (prefix_errS_meas S hBpos t r)).pow_const 2).indicator hAm).aestronglyMeasurable)
        (ae_of_all _ fun ω => by
          have hl : 0 ≤ A.indicator (fun ω => fro (dynErrS p S t r ω) ^ 2) ω :=
            Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
          have hr : 0 ≤ A.indicator (fun ω => fro (dynErrM p S t r ω) ^ 2 +
              fro (dynErrS p S t r ω) ^ 2) ω :=
            Set.indicator_nonneg (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) ω
          simp only [Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hr]
          by_cases hω : ω ∈ A
          · simp only [Set.indicator_of_mem hω]
            exact le_add_of_nonneg_left (sq_nonneg _)
          · simp [Set.indicator_of_notMem hω])
    obtain ⟨hfsint, hfsbd0⟩ := prefix_amgm fs hfsmeas.aestronglyMeasurable hfs0
      hfsqint q hqpos
    have hfsbd : ∫ ω, fs ω ∂P ≤ (K1' + 1) / 2 * (q : ℝ) := by
      refine hfsbd0.trans ?_
      rw [div_le_iff₀ (by positivity)]
      have hrqR : (r : ℝ) ≤ q := by exact_mod_cast hrq
      have hsqle : (r : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hrqR 2
      have hfsqbd : ∫ ω, fs ω ^ 2 ∂P ≤ K1' * (q : ℝ) ^ 2 := by
        rw [hfsqeq]
        exact hS2bd.trans (mul_le_mul_of_nonneg_left hsqle hK1')
      nlinarith
    obtain ⟨hVm, hVsqint, hVsqbd⟩ := hKs Ω P m n B S W hW t r A hAF hAK
    let fv : Ω → ℝ := A.indicator (fun ω =>
      |frobIP (W (dynDelta S t ω))
        (stationaryV p S.C S.cs t (dynDelta S t ω) r ω)|)
    have hfvmeas : AEMeasurable fv P := by
      have heq : fv = fun ω => |frobIP (W (dynDelta S t ω))
          (A.indicator (fun ω => stationaryV p S.C S.cs t
            (dynDelta S t ω) r ω) ω)| := by
        funext ω
        by_cases hω : ω ∈ A
        · simp only [fv, Set.indicator_of_mem hω]
        · simp [fv, Set.indicator_of_notMem hω, prefix_frobIP_eq_sum]
      rw [heq]
      exact prefix_meas_abs_frobIP W _ _ hΔt hVm
    have hfv0 : ∀ ω, 0 ≤ fv ω := fun ω =>
      Set.indicator_nonneg (fun _ _ => abs_nonneg _) ω
    have hfvsqeq : (fun ω => fv ω ^ 2) = A.indicator (fun ω =>
        frobIP (W (dynDelta S t ω))
          (stationaryV p S.C S.cs t (dynDelta S t ω) r ω) ^ 2) := by
      funext ω
      by_cases hω : ω ∈ A
      · simp only [fv, Set.indicator_of_mem hω, sq_abs]
      · simp [fv, Set.indicator_of_notMem hω]
    have hfvsqint : Integrable (fun ω => fv ω ^ 2) P := by
      rw [hfvsqeq]
      exact hVsqint
    obtain ⟨hfvint, hfvbd0⟩ := prefix_amgm fv hfvmeas.aestronglyMeasurable hfv0
      hfvsqint q hqpos
    have hfvbd : ∫ ω, fv ω ∂P ≤ (2 * Ks + 1) / 2 * (q : ℝ) := by
      refine hfvbd0.trans ?_
      rw [div_le_iff₀ (by positivity)]
      have hlog0 : 0 ≤ Real.log (2 * (B : ℝ)) := by
        apply Real.log_nonneg
        have : (1 : ℝ) ≤ B := by exact_mod_cast hB1
        linarith
      have hl2 : Real.log (2 * (B : ℝ)) ^ 2 ≤ (q : ℝ) ^ 2 :=
        pow_le_pow_left₀ hlog0 hlogq 2
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
      have hqR1 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
      have hfvsqbd : ∫ ω, fv ω ^ 2 ∂P ≤ 2 * Ks * (q : ℝ) ^ 2 := by
        rw [hfvsqeq]
        refine hVsqbd.trans ?_
        have := mul_le_mul_of_nonneg_left (add_le_add hl2 hqR1) hKs0
        nlinarith
      nlinarith
    have hmove : ∀ ω ∈ A,
        |frobIP (W (dynDelta S (t + r) ω - dynDelta S t ω))
          (dynUpd S (t + r) ω)| ≤ Kmv * |cW| * (r : ℝ) := by
      intro ω hω
      exact hmv Ω P m n B S cW W hBmv hBpos hW t r ω hr4 (hAK ω hω)
    have hpoint : ∀ ω, f ω ≤ fu ω + Tb * fs ω + fv ω +
        A.indicator (fun _ => Kmv * |cW| * (r : ℝ)) ω := by
      intro ω
      by_cases hω : ω ∈ A
      · simp only [f, fu, fs, fv, Set.indicator_of_mem hω]
        have hWD : fro (W (dynDelta S t ω)) ≤ Tb := by
          refine (hW _).trans ?_
          exact mul_le_mul_of_nonneg_left
            (Real.le_sqrt_of_sq_le (hAK ω hω).2.2) hcW
        have hSIP := (projection_frobIP_le (W (dynDelta S t ω))
          (dynErrS p S t r ω)).trans
            (mul_le_mul_of_nonneg_right hWD (Real.sqrt_nonneg _))
        have eu : frobIP (W (dynDelta S t ω)) (dynUpd S (t + r) ω) =
            frobIP (W (dynDelta S (t + r) ω)) (dynUpd S (t + r) ω) -
              frobIP (W (dynDelta S (t + r) ω - dynDelta S t ω))
                (dynUpd S (t + r) ω) := by
          have e1 : frobIP (W (dynDelta S (t + r) ω)) (dynUpd S (t + r) ω) =
              frobIP (W (dynDelta S t ω)) (dynUpd S (t + r) ω) +
              frobIP (W (dynDelta S (t + r) ω - dynDelta S t ω))
                (dynUpd S (t + r) ω) := by
            rw [← prefix_frobIP_add_left, ← map_add]
            congr 2
            abel
          linarith
        have ev : dynErrV p S t r ω = dynUpd S (t + r) ω -
            dynErrS p S t r ω -
              stationaryV p S.C S.cs t (dynDelta S t ω) r ω := by
          simp only [dynErrV, dynErrS]
          abel
        have etarget : frobIP (W (dynDelta S t ω)) (dynErrV p S t r ω) =
            frobIP (W (dynDelta S t ω)) (dynUpd S (t + r) ω) -
              frobIP (W (dynDelta S t ω)) (dynErrS p S t r ω) -
              frobIP (W (dynDelta S t ω))
                (stationaryV p S.C S.cs t (dynDelta S t ω) r ω) := by
          rw [ev]
          rw [prefix_frobIP_sub_right, prefix_frobIP_sub_right]
        rw [etarget, eu]
        calc
          _ ≤ |frobIP (W (dynDelta S (t + r) ω)) (dynUpd S (t + r) ω)| +
              |frobIP (W (dynDelta S (t + r) ω - dynDelta S t ω))
                (dynUpd S (t + r) ω)| +
              |frobIP (W (dynDelta S t ω)) (dynErrS p S t r ω)| +
              |frobIP (W (dynDelta S t ω))
                (stationaryV p S.C S.cs t (dynDelta S t ω) r ω)| := by
            have h1 := abs_sub (frobIP (W (dynDelta S (t + r) ω))
              (dynUpd S (t + r) ω))
              (frobIP (W (dynDelta S (t + r) ω - dynDelta S t ω))
                (dynUpd S (t + r) ω))
            have h2 := abs_sub
              (frobIP (W (dynDelta S (t + r) ω)) (dynUpd S (t + r) ω) -
                frobIP (W (dynDelta S (t + r) ω - dynDelta S t ω))
                  (dynUpd S (t + r) ω))
              (frobIP (W (dynDelta S t ω)) (dynErrS p S t r ω))
            have h3 := abs_sub
              ((frobIP (W (dynDelta S (t + r) ω)) (dynUpd S (t + r) ω) -
                frobIP (W (dynDelta S (t + r) ω - dynDelta S t ω))
                  (dynUpd S (t + r) ω)) -
                frobIP (W (dynDelta S t ω)) (dynErrS p S t r ω))
              (frobIP (W (dynDelta S t ω))
                (stationaryV p S.C S.cs t (dynDelta S t ω) r ω))
            linarith
          _ ≤ _ := by linarith [hmove ω hω]
      · simp [f, fu, fs, fv, Set.indicator_of_notMem hω]
    have hconstint : Integrable (A.indicator (fun _ => Kmv * |cW| * (r : ℝ))) P :=
      (integrable_const _).indicator hAm
    have hdomint : Integrable (fun ω => fu ω + Tb * fs ω + fv ω +
        A.indicator (fun _ => Kmv * |cW| * (r : ℝ)) ω) P :=
      ((hfuint.add (hfsint.const_mul Tb)).add hfvint).add hconstint
    calc
      ∫ ω, f ω ∂P ≤ ∫ ω, (fu ω + Tb * fs ω + fv ω +
          A.indicator (fun _ => Kmv * |cW| * (r : ℝ)) ω) ∂P :=
        integral_mono hfint hdomint hpoint
      _ = ∫ ω, fu ω ∂P + Tb * ∫ ω, fs ω ∂P + ∫ ω, fv ω ∂P +
          ∫ ω, A.indicator (fun _ => Kmv * |cW| * (r : ℝ)) ω ∂P := by
        rw [integral_add, integral_add, integral_add, integral_const_mul]
        all_goals fun_prop
      _ ≤ Ki' * (q : ℝ) + Tb * ((K1' + 1) / 2 * (q : ℝ)) +
          (2 * Ks + 1) / 2 * (q : ℝ) + Kmv * |cW| * (r : ℝ) := by
        have hcbd : ∫ ω, A.indicator (fun _ => Kmv * |cW| * (r : ℝ)) ω ∂P ≤
            Kmv * |cW| * (r : ℝ) := by
          rw [integral_indicator hAm, setIntegral_const, smul_eq_mul]
          have hc : 0 ≤ Kmv * |cW| * (r : ℝ) := by positivity
          nlinarith [(measureReal_nonneg : 0 ≤ P.real A),
            measureReal_le_one (μ := P) (s := A)]
        have hsbd := mul_le_mul_of_nonneg_left hfsbd hTb
        linarith
      _ ≤ Kfirst * (q : ℝ) := by
        have hrqR : (r : ℝ) ≤ q := by exact_mod_cast hrq
        have hm := mul_le_mul_of_nonneg_left hrqR
          (mul_nonneg hKmv0 (abs_nonneg cW))
        dsimp [Kfirst]
        nlinarith
  have htarget : f = A.indicator (fun ω =>
      |frobIP (S.C.Sout * dynDelta S t ω * S.C.Sin) (dynErrV p S t r ω)|) := by
    funext ω
    simp only [f, W, prefixSigmaLM_apply]
  rw [← htarget]
  refine ⟨hfint, ?_, ?_⟩
  · intro hr
    exact (hfirst hr).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hKdec) (Nat.cast_nonneg _))
  · refine hdec.trans ?_
    have hk : Kdec ≤ Kfirst + Kdec := le_add_of_nonneg_left hKfirst
    gcongr

private lemma prefix_sum_pow_le (p : DynParams) (k : ℕ) :
    ∑ r ∈ Finset.range k, p.β ^ r ≤ (1 - p.β)⁻¹ := by
  rw [← tsum_geometric_of_lt_one p.hβ.1 p.hβ.2]
  exact (summable_geometric_of_lt_one p.hβ.1 p.hβ.2).sum_le_tsum _
    (fun r _ => pow_nonneg p.hβ.1 r)

private lemma prefix_tail_sum (p : DynParams) (q L : ℕ) :
    ∑ r ∈ (Finset.range L).filter (fun r => q ≤ r), p.β ^ (r + 1) ≤
      (1 - p.β)⁻¹ * p.β ^ q := by
  by_cases hqL : q ≤ L
  swap
  · have he : (Finset.range L).filter (fun r => q ≤ r) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro r hr hqr
      have hrlt := Finset.mem_range.mp hr
      omega
    rw [he]
    simp only [Finset.sum_empty]
    exact mul_nonneg (inv_nonneg.mpr (sub_pos.mpr p.hβ.2).le) (pow_nonneg p.hβ.1 _)
  obtain ⟨T, rfl⟩ := Nat.exists_eq_add_of_le hqL
  have hfilter : (Finset.range (q + T)).filter (fun r => q ≤ r) = Finset.Ico q (q + T) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    tauto
  rw [hfilter, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  calc
    ∑ r ∈ Finset.range T, p.β ^ (q + r + 1) =
        p.β ^ q * ∑ r ∈ Finset.range T, p.β ^ (r + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [← pow_add]
      congr 1
    _ ≤ p.β ^ q * ∑ r ∈ Finset.range T, p.β ^ r := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun r _ =>
          pow_le_pow_of_le_one p.hβ.1 p.hβ.2.le (Nat.le_succ r))
        (pow_nonneg p.hβ.1 _)
    _ ≤ p.β ^ q * (1 - p.β)⁻¹ :=
      mul_le_mul_of_nonneg_left (prefix_sum_pow_le p T) (pow_nonneg p.hβ.1 _)
    _ = _ := by ring

private lemma prefix_min_summable (p : DynParams) (ε : ℝ) (hε : 0 ≤ ε) :
    Summable (fun r : ℕ => min ε (p.β ^ (r + 1))) := by
  have hgeom : Summable (fun r : ℕ => p.β ^ (r + 1)) := by
    have h := (summable_geometric_of_lt_one p.hβ.1 p.hβ.2).mul_left p.β
    simpa only [pow_succ', mul_comm] using h
  exact Summable.of_nonneg_of_le
    (fun r => le_min hε (pow_nonneg p.hβ.1 _))
    (fun r => min_le_right _ _) hgeom

/-- `eqn:app-dyn-envelope` (cr-2026-10-23), part of `lem:app-dyn-prefix`: for `t ≥ 𝗊`,
`(1/√B) ∑_{r<L} 𝔼[𝟙_{t<τ⁺} |⟨Σ_out Δ_t Σ_in, V̂_r − V_r⟩|] ≤ C(Ω_β(ε_B) + β^𝗊)` with `ε_B = 𝗊/√B`, each summand
integrable. Statement verbatim from `section.tex` (ll. 1848–1850):
```latex
\begin{equation}\label{eqn:app-dyn-envelope}
\frac{1}{\sqrt B}\sum_{r<L}\EE\big[\mathbf 1_{t<\tau^+}\abs{\langle\Sigmaout\Dt\Sigmain,\widehat V_r-V_r\rangle}\big]\le C\big(\Omega_\bmom(\epsilon_B)+\bmom^{\mathsf q}\big),
\end{equation}
```
-/
theorem eqn_app_dyn_envelope (certP : Muon.External.GaussianPoincare) (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∃ B0 : ℕ, ∃ K : ℝ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (m n B : ℕ) (S : DynSetup p P m n B),
        B0 ≤ B → ∀ t : ℕ, prefixLen p.β B ≤ t →
          (∀ r ∈ Finset.range (blockLen B),
            Integrable ({ω | (t : ℕ∞) < tauPlus p S ω}.indicator
              (fun ω => |frobIP (S.C.Sout * dynDelta S t ω * S.C.Sin) (dynErrV p S t r ω)|)) P) ∧
          (1 / Real.sqrt (B : ℝ)) * ∑ r ∈ Finset.range (blockLen B),
            ∫ ω, {ω | (t : ℕ∞) < tauPlus p S ω}.indicator
              (fun ω => |frobIP (S.C.Sout * dynDelta S t ω * S.C.Sin) (dynErrV p S t r ω)|) ω ∂P
            ≤ K * (omegaBeta p.β ((prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ)) + p.β ^ prefixLen p.β B) := by
  obtain ⟨B0, K, hpre⟩ := lem_app_dyn_prefix_iii certP certOp p
  let K' := max K 0
  let cg := (1 - p.β)⁻¹
  have hK' : 0 ≤ K' := le_max_right _ _
  have hcg : 0 ≤ cg := by
    dsimp [cg]
    exact inv_nonneg.mpr (sub_pos.mpr p.hβ.2).le
  refine ⟨max B0 1, K' * (1 + cg), ?_⟩
  intro Ω mΩ P hP m n B S hBge t ht
  have hB0 : B0 ≤ B := (le_max_left _ _).trans hBge
  have hB1 : 1 ≤ B := (le_max_right _ _).trans hBge
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast hB1
  have hsqrt : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBpos
  let q := prefixLen p.β B
  let L := blockLen B
  let ε := (q : ℝ) / Real.sqrt (B : ℝ)
  have hε : 0 ≤ ε := div_nonneg (Nat.cast_nonneg _) hsqrt.le
  have hp := hpre Ω P m n B S hB0 t ht
  refine ⟨fun r hr => (hp r).1, ?_⟩
  let E : ℕ → ℝ := fun r => ∫ ω, {ω | (t : ℕ∞) < tauPlus p S ω}.indicator
    (fun ω => |frobIP (S.C.Sout * dynDelta S t ω * S.C.Sin)
      (dynErrV p S t r ω)|) ω ∂P
  have hE0 : ∀ r, 0 ≤ E r := fun r => integral_nonneg fun ω =>
    Set.indicator_nonneg (fun _ _ => abs_nonneg _) ω
  have hdec : ∀ r, E r ≤ K' * Real.sqrt (B : ℝ) * p.β ^ (r + 1) := by
    intro r
    refine (hp r).2.2.trans ?_
    have hk : K ≤ K' := le_max_left _ _
    have hf : 0 ≤ Real.sqrt (B : ℝ) * p.β ^ (r + 1) :=
      mul_nonneg hsqrt.le (pow_nonneg p.hβ.1 _)
    calc
      K * Real.sqrt (B : ℝ) * p.β ^ (r + 1) =
          K * (Real.sqrt (B : ℝ) * p.β ^ (r + 1)) := by ring
      _ ≤ K' * (Real.sqrt (B : ℝ) * p.β ^ (r + 1)) :=
        mul_le_mul_of_nonneg_right hk hf
      _ = _ := by ring
  have hshort : ∀ r, r < q → E r ≤ K' * Real.sqrt (B : ℝ) *
      min ε (p.β ^ (r + 1)) := by
    intro r hr
    have hk : K ≤ K' := le_max_left _ _
    have hqbd : E r ≤ K' * (q : ℝ) := ((hp r).2.1 hr.le).trans
      (mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg q))
    by_cases hm : ε ≤ p.β ^ (r + 1)
    · rw [min_eq_left hm]
      dsimp [ε]
      field_simp
      simpa only [q] using hqbd
    · rw [min_eq_right (le_of_not_ge hm)]
      exact hdec r
  classical
  have hsplit : ∑ r ∈ Finset.range L, E r =
      ∑ r ∈ (Finset.range L).filter (fun r => r < q), E r +
      ∑ r ∈ (Finset.range L).filter (fun r => q ≤ r), E r := by
    have heq : (Finset.range L).filter (fun r => q ≤ r) =
        (Finset.range L).filter (fun r => ¬ r < q) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    calc
      _ = ∑ r ∈ (Finset.range L).filter (fun r => r < q), E r +
          ∑ r ∈ (Finset.range L).filter (fun r => ¬ r < q), E r :=
        (Finset.sum_filter_add_sum_filter_not (Finset.range L) (fun r => r < q) E).symm
      _ = _ := by rw [← heq]
  have hsum : ∑ r ∈ Finset.range L, E r ≤ K' * Real.sqrt (B : ℝ) *
      (omegaBeta p.β ε + cg * p.β ^ q) := by
    rw [hsplit]
    calc
      _ ≤ ∑ r ∈ (Finset.range L).filter (fun r => r < q),
            K' * Real.sqrt (B : ℝ) * min ε (p.β ^ (r + 1)) +
          ∑ r ∈ (Finset.range L).filter (fun r => q ≤ r),
            K' * Real.sqrt (B : ℝ) * p.β ^ (r + 1) :=
        add_le_add (Finset.sum_le_sum fun r hr => hshort r (Finset.mem_filter.1 hr).2)
          (Finset.sum_le_sum fun r _ => hdec r)
      _ = K' * Real.sqrt (B : ℝ) *
          (∑ r ∈ (Finset.range L).filter (fun r => r < q),
              min ε (p.β ^ (r + 1)) +
            ∑ r ∈ (Finset.range L).filter (fun r => q ≤ r), p.β ^ (r + 1)) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      _ ≤ K' * Real.sqrt (B : ℝ) *
          (omegaBeta p.β ε + cg * p.β ^ q) := by
        gcongr
        · unfold omegaBeta
          exact (prefix_min_summable p ε hε).sum_le_tsum _
            (fun r _ => le_min hε (pow_nonneg p.hβ.1 _))
        · exact prefix_tail_sum p q L
  change (1 / Real.sqrt (B : ℝ)) * ∑ r ∈ Finset.range L, E r ≤ _
  calc
    _ ≤ (1 / Real.sqrt (B : ℝ)) *
        (K' * Real.sqrt (B : ℝ) * (omegaBeta p.β ε + cg * p.β ^ q)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = K' * (omegaBeta p.β ε + cg * p.β ^ q) := by field_simp
    _ ≤ K' * (1 + cg) * (omegaBeta p.β ε + p.β ^ q) := by
      have hΩ : 0 ≤ omegaBeta p.β ε := tsum_nonneg fun r =>
        le_min hε (pow_nonneg p.hβ.1 _)
      have hβq : 0 ≤ p.β ^ q := pow_nonneg p.hβ.1 _
      nlinarith [mul_nonneg hcg hΩ, mul_nonneg hcg hβq]

private lemma omegaBeta_split (p : DynParams) (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) :
    omegaBeta p.β ε ≤ N * ε + p.β ^ (N + 1) * (1 - p.β)⁻¹ := by
  unfold omegaBeta
  have hs := prefix_min_summable p ε hε
  rw [← Summable.sum_add_tsum_nat_add N hs]
  have hsh : Summable (fun i : ℕ => min ε (p.β ^ (i + N + 1))) := (summable_nat_add_iff N).mpr hs
  have hg : Summable (fun i : ℕ => p.β ^ (N + 1) * p.β ^ i) :=
    (summable_geometric_of_lt_one p.hβ.1 p.hβ.2).mul_left _
  have htail : ∑' i : ℕ, min ε (p.β ^ (i + N + 1)) ≤ p.β ^ (N + 1) * (1 - p.β)⁻¹ := by
    calc ∑' i : ℕ, min ε (p.β ^ (i + N + 1)) ≤ ∑' i : ℕ, p.β ^ (N + 1) * p.β ^ i :=
          Summable.tsum_le_tsum (fun i => by
            refine (min_le_right _ _).trans (le_of_eq ?_)
            rw [← pow_add]
            congr 1
            omega) hsh hg
      _ = p.β ^ (N + 1) * (1 - p.β)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one p.hβ.1 p.hβ.2]
  have hhead : ∑ i ∈ Finset.range N, min ε (p.β ^ (i + 1)) ≤ N * ε := by
    calc ∑ i ∈ Finset.range N, min ε (p.β ^ (i + 1)) ≤ ∑ i ∈ Finset.range N, ε :=
          Finset.sum_le_sum fun i _ => min_le_left _ _
      _ = N * ε := by simp
  linarith

/-- `lem:app-dyn-prefix` (cr-2026-10-23), part (iv): the bound `Ω_β(ε) ≤ C ε(1 + log(1/ε))` for `0 < ε ≤ 1`, with
`Ω_0 = 0`, where `Ω_β(ε) = ∑_{r≥0} min(ε, β^{r+1})`. The constant depends on `β` only. Statement from
`section.tex` (ll. 1848–1852):
```latex
\begin{lemma}[Delayed projections and prefixes]\label{lem:app-dyn-prefix}
Let $\mathcal W$ be a linear map on $\R^{\Nout\times\Nin}$ with $\norm{\mathcal W}_{\F\to\F}\le c_W$.
\begin{enumerate}[label=(\roman*)]
\item For every $u\ge\mathsf q$, $\EE\big[\mathbf 1_{u-\mathsf q<\tau^+}\abs{\langle\mathcal W\Delta_u,{\mathsf S}_u\rangle}\big]\le C\mathsf q$.
\item For every $t\ge\mathsf q$, $\EE\big[\mathbf 1_{t<\tau^+}\big|\sum_{r<\mathsf q}\langle\mathcal W\Dt,{\mathsf S}_{t+r}\rangle\big|\big]\le C\mathsf q^2$.
\item For every $t\ge\mathsf q$, with the chains at time $t$ and $0\le r\le\mathsf q$,
$\EE\big[\mathbf 1_{t<\tau^+}\abs{\langle\Sigmaout\Dt\Sigmain,\widehat V_r-V_r\rangle}\big]\le\min\big(C\mathsf q,\ C\sqrt B\bmom^{r+1}\big)$,
and for every $r\ge0$ the second bound holds.
\end{enumerate}
Consequently, with $\Omega_\bmom(\epsilon)\defeq\sum_{r\ge0}\min(\epsilon,\bmom^{r+1})$
and $\epsilon_B\defeq\mathsf q/\sqrt B$,
\begin{equation}\label{eqn:app-dyn-envelope}
\frac{1}{\sqrt B}\sum_{r<L}\EE\big[\mathbf 1_{t<\tau^+}\abs{\langle\Sigmaout\Dt\Sigmain,\widehat V_r-V_r\rangle}\big]\le C\big(\Omega_\bmom(\epsilon_B)+\bmom^{\mathsf q}\big),
\end{equation}
and $\Omega_\bmom(\epsilon)\le C\epsilon(1+\log(1/\epsilon))$ for $0<\epsilon\le1$, with
$\Omega_0=0$.
\end{lemma}
```
-/
theorem lem_app_dyn_prefix_iv (p : DynParams) :
    ∃ K : ℝ, (∀ ε : ℝ, 0 < ε → ε ≤ 1 → omegaBeta p.β ε ≤ K * ε * (1 + Real.log (1 / ε))) ∧
      (∀ ε : ℝ, 0 ≤ ε → omegaBeta 0 ε = 0) := by
  have key0 : ∀ ε : ℝ, 0 ≤ ε → omegaBeta 0 ε = 0 := by
    intro ε hε
    have hz : ∀ r : ℕ, min ε ((0 : ℝ) ^ (r + 1)) = 0 := fun r => by
      rw [zero_pow (Nat.succ_ne_zero r)]
      exact min_eq_right hε
    unfold omegaBeta
    simp only [hz, tsum_zero]
  rcases eq_or_lt_of_le p.hβ.1 with h0 | hpos
  · refine ⟨0, fun ε hε _ => ?_, key0⟩
    rw [← h0, key0 ε hε.le]
    simp
  · have hβ1 : p.β < 1 := p.hβ.2
    have hlogβ : Real.log p.β < 0 := Real.log_neg hpos hβ1
    have hu : 0 ≤ 1 / (-Real.log p.β) := div_nonneg zero_le_one (by linarith)
    have hc : 0 ≤ (1 - p.β)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hβ1).le
    refine ⟨1 / (-Real.log p.β) + 1 + (1 - p.β)⁻¹, fun ε hε0 hε1 => ?_, key0⟩
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.log ε / Real.log p.β := ⟨_, rfl⟩
    have hq0 : 0 ≤ q := by
      rw [hq]
      exact div_nonneg_of_nonpos (Real.log_nonpos hε0.le hε1) hlogβ.le
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈q⌉₊ := ⟨_, rfl⟩
    have hNq : q ≤ N := by
      rw [hN]
      exact Nat.le_ceil q
    have hNq' : (N : ℝ) < q + 1 := by
      rw [hN]
      exact Nat.ceil_lt_add_one hq0
    have hβN : p.β ^ N ≤ ε := by
      rw [← Real.log_le_log_iff (pow_pos hpos N) hε0, Real.log_pow]
      have h1 : (N : ℝ) * Real.log p.β ≤ q * Real.log p.β :=
        mul_le_mul_of_nonpos_right hNq hlogβ.le
      have h2 : q * Real.log p.β = Real.log ε := by
        rw [hq]
        exact div_mul_cancel₀ _ hlogβ.ne
      linarith
    have hβN1 : p.β ^ (N + 1) ≤ ε := by
      rw [pow_succ]
      exact (mul_le_of_le_one_right (pow_nonneg hpos.le N) hβ1.le).trans hβN
    have hsplit := omegaBeta_split p ε hε0.le N
    have hterm : p.β ^ (N + 1) * (1 - p.β)⁻¹ ≤ ε * (1 - p.β)⁻¹ :=
      mul_le_mul_of_nonneg_right hβN1 hc
    have hNε : (N : ℝ) * ε ≤ (q + 1) * ε := mul_le_mul_of_nonneg_right hNq'.le hε0.le
    have hL0 : 0 ≤ Real.log (1 / ε) := by
      rw [one_div, Real.log_inv]
      linarith [Real.log_nonpos hε0.le hε1]
    have hqL : q = Real.log (1 / ε) * (1 / (-Real.log p.β)) := by
      rw [hq, one_div ε, Real.log_inv, mul_one_div, neg_div_neg_eq]
    rw [hqL] at hNε
    nlinarith [mul_nonneg hε0.le hu, mul_nonneg hε0.le hL0,
      mul_nonneg (mul_nonneg hε0.le hc) hL0, mul_nonneg hε0.le hc]

/-! ## Helpers for `prop:app-dyn-transport` (P-E.10.P6) -/

section TrDX
open Muon.DetEquiv
open scoped Matrix.Norms.L2Operator

private lemma tr_unit {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    IsUnit (K * Kᵀ + s • (1 : Mat m m)) := by
  have h1 : (K * Kᵀ).PosSemidef := by simpa using Matrix.posSemidef_self_mul_conjTranspose K
  have h2 : (s • (1 : Mat m m)).PosDef := Matrix.PosDef.one.smul hs
  exact (Matrix.PosDef.add_posSemidef h2 h1 |> fun h => by rwa [add_comm] at h : (K * Kᵀ + s • (1 : Mat m m)).PosDef).isUnit

/-- explicit derivative of `Xs` along a direction -/
private def trdX {m n : ℕ} (K R : Mat m n) (s : ℝ) : Mat m n :=
  Rs K s * R - Rs K s * (R * Kᵀ + K * Rᵀ) * (Rs K s * K)

private lemma tr_Xs_hasDerivAt {m n : ℕ} (K R : Mat m n) {s : ℝ} (hs : 0 < s) (t0 : ℝ) :
    HasDerivAt (fun t : ℝ => Xs (K + t • R) s) (trdX (K + t0 • R) R s) t0 := by
  set K0 := K + t0 • R with hK0
  have hu := tr_unit K0 hs
  have hS : HasDerivAt (fun t : ℝ => (K + t • R) * (K + t • R)ᵀ + s • (1 : Mat m m))
      (R * K0ᵀ + K0 * Rᵀ) t0 := by
    have hexp : (fun t : ℝ => (K + t • R) * (K + t • R)ᵀ + s • (1 : Mat m m)) =
        fun t : ℝ => (K * Kᵀ + s • (1 : Mat m m)) + t • (R * Kᵀ + K * Rᵀ) + (t ^ 2) • (R * Rᵀ) := by
      funext t
      simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add]
      rw [sq]; abel
    rw [hexp]
    have h1 := ((hasDerivAt_id' t0).smul_const (R * Kᵀ + K * Rᵀ)).const_add (K * Kᵀ + s • (1 : Mat m m))
    have h2 := (hasDerivAt_pow 2 t0).smul_const (R * Rᵀ)
    refine (h1.add h2).congr_deriv ?_
    rw [hK0]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.smul_mul, Matrix.mul_smul, one_smul]
    norm_num
    module
  have h2 := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  have h3 := h2.comp_hasDerivAt t0 hS
  have e : ∀ t : ℝ, Rs (K + t • R) s = Ring.inverse ((K + t • R) * (K + t • R)ᵀ + s • (1 : Mat m m)) :=
    fun t => by unfold Rs; rw [Matrix.nonsing_inv_eq_ringInverse]
  have e2 : (hu.unit⁻¹ : Units (Mat m m)).val = Rs K0 s := by
    rw [show Rs K0 s = Ring.inverse (K0 * K0ᵀ + s • (1 : Mat m m)) by
      unfold Rs; rw [Matrix.nonsing_inv_eq_ringInverse], ← Ring.inverse_unit hu.unit]
    rfl
  have hR : HasDerivAt (fun t : ℝ => Rs (K + t • R) s)
      (-(Rs K0 s * (R * K0ᵀ + K0 * Rᵀ) * Rs K0 s)) t0 := by
    have hfun : (fun t : ℝ => Rs (K + t • R) s) =
        Ring.inverse ∘ fun t : ℝ => (K + t • R) * (K + t • R)ᵀ + s • (1 : Mat m m) :=
      funext fun t => e t
    rw [hfun]
    convert h3 using 1
    simp [ContinuousLinearMap.mulLeftRight_apply, e2, Matrix.mul_assoc]
  let LK : Mat m m →L[ℝ] Mat m n := LinearMap.toContinuousLinearMap
    { toFun := fun M => M * K, map_add' := fun _ _ => Matrix.add_mul _ _ _,
      map_smul' := fun _ _ => Matrix.smul_mul _ _ _ }
  let LR : Mat m m →L[ℝ] Mat m n := LinearMap.toContinuousLinearMap
    { toFun := fun M => M * R, map_add' := fun _ _ => Matrix.add_mul _ _ _,
      map_smul' := fun _ _ => Matrix.smul_mul _ _ _ }
  have hA : HasDerivAt (fun t : ℝ => Rs (K + t • R) s * K)
      (-(Rs K0 s * (R * K0ᵀ + K0 * Rᵀ) * Rs K0 s) * K) t0 :=
    LK.hasFDerivAt.comp_hasDerivAt t0 hR
  have hB : HasDerivAt (fun t : ℝ => t • (Rs (K + t • R) s * R))
      (t0 • (-(Rs K0 s * (R * K0ᵀ + K0 * Rᵀ) * Rs K0 s) * R) + (1 : ℝ) • (Rs K0 s * R)) t0 :=
    (hasDerivAt_id t0).smul (LR.hasFDerivAt.comp_hasDerivAt t0 hR)
  have hfun : (fun t : ℝ => Xs (K + t • R) s) =
      fun t => Rs (K + t • R) s * K + t • (Rs (K + t • R) s * R) := by
    funext t; unfold Xs; rw [Matrix.mul_add, Matrix.mul_smul]
  rw [hfun]
  convert hA.add hB using 1
  unfold trdX
  simp only [K0, Matrix.neg_mul, Matrix.mul_assoc, one_smul, Matrix.mul_add, Matrix.mul_smul, smul_neg]
  abel

private lemma tr_Xs_entry_hasDerivAt {m n : ℕ} (K R : Mat m n) {s : ℝ} (hs : 0 < s) (t0 : ℝ)
    (i : Fin m) (j : Fin n) :
    HasDerivAt (fun t : ℝ => Xs (K + t • R) s i j) (trdX (K + t0 • R) R s i j) t0 := by
  let L : Mat m n →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact L.hasFDerivAt.comp_hasDerivAt t0 (tr_Xs_hasDerivAt K R hs t0)

private lemma tr_dirX_eq {m n : ℕ} (K R : Mat m n) {s : ℝ} (hs : 0 < s) :
    dirX K R s = trdX K R s := by
  ext i j
  unfold dirX
  simp only [Matrix.of_apply]
  have := (tr_Xs_entry_hasDerivAt K R hs 0 i j).deriv
  simpa using this


end TrDX

section TrMain
open Muon.DetEquiv

open scoped Matrix.Norms.L2Operator in
private lemma tr_opNorm_one_le {n : ℕ} : opNorm (1 : Mat n n) ≤ 1 := by
  rw [opNorm_eq_norm, ← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun i => by simp

open scoped Matrix.Norms.L2Operator in
private lemma tr_opNorm_mul {a b c : ℕ} (A : Mat a b) (M : Mat b c) :
    opNorm (A * M) ≤ opNorm A * opNorm M := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A M

open scoped Matrix.Norms.L2Operator in
private lemma tr_opNorm_nonneg {a b : ℕ} (A : Mat a b) : 0 ≤ opNorm A := by
  rw [opNorm_eq_norm]; exact norm_nonneg _

private lemma tr_fro_nonneg {a b : ℕ} (A : Mat a b) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma tr_fro_mul_left {a b c : ℕ} (A : Mat a b) (M : Mat b c) :
    fro (A * M) ≤ opNorm A * fro M := by
  have h := projection_fro_mul_sq_le_left A M
  rw [← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (tr_fro_nonneg _) (mul_nonneg (tr_opNorm_nonneg _) (tr_fro_nonneg _))
    (by norm_num)).mp h

private lemma tr_fro_mul_right {a b c : ℕ} (M : Mat a b) (A : Mat b c) :
    fro (M * A) ≤ fro M * opNorm A := by
  have h := projection_fro_mul_sq_le_right M A
  rw [← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (tr_fro_nonneg _) (mul_nonneg (tr_fro_nonneg _) (tr_opNorm_nonneg _))
    (by norm_num)).mp h

private lemma tr_fro_sub_le {a b : ℕ} (A M : Mat a b) : fro (A - M) ≤ fro A + fro M := by
  open scoped Matrix.Norms.Frobenius in
  rw [fro_eq_norm, fro_eq_norm, fro_eq_norm]; exact norm_sub_le _ _

private lemma tr_fro_add_le {a b : ℕ} (A M : Mat a b) : fro (A + M) ≤ fro A + fro M := by
  open scoped Matrix.Norms.Frobenius in
  rw [fro_eq_norm, fro_eq_norm, fro_eq_norm]; exact norm_add_le _ _

private lemma tr_fro_smul {a b : ℕ} (c : ℝ) (A : Mat a b) : fro (c • A) = |c| * fro A := by
  open scoped Matrix.Norms.Frobenius in
  rw [fro_eq_norm, fro_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma tr_KRK_le {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    opNorm (Kᵀ * Rs K s * K) ≤ 2 := by
  obtain ⟨-, h2, -, -, h5, -, -⟩ := Muon.DetEquiv.lem_app_de_resolvent K s hs
  rw [h5]
  have : opNorm ((1 : Mat n n) - s • Rts K s) ≤ opNorm (1 : Mat n n) + s * opNorm (Rts K s) := by
    open scoped Matrix.Norms.L2Operator in
    rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  refine this.trans ?_
  have h1 := tr_opNorm_one_le (n := n)
  have : s * opNorm (Rts K s) ≤ 1 := by
    calc s * opNorm (Rts K s) ≤ s * (1 / s) := mul_le_mul_of_nonneg_left h2 hs.le
      _ = 1 := by field_simp
  linarith

private lemma tr_trdX_bound {m n : ℕ} (K R : Mat m n) {s : ℝ} (hs : 0 < s) :
    fro (trdX K R s) ≤ (13 / 4) / s * fro R := by
  obtain ⟨h1, -, h3, -, -, -, -⟩ := Muon.DetEquiv.lem_app_de_resolvent K s hs
  have hRK := tr_KRK_le K hs
  have he : trdX K R s = Rs K s * R - Rs K s * R * (Kᵀ * Rs K s * K) - Xs K s * Rᵀ * Xs K s := by
    unfold trdX Xs
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [he]
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hX2 : opNorm (Xs K s) * opNorm (Xs K s) ≤ 1 / (4 * s) := by
    have h0 := tr_opNorm_nonneg (Xs K s)
    calc opNorm (Xs K s) * opNorm (Xs K s) ≤ (1 / (2 * Real.sqrt s)) * (1 / (2 * Real.sqrt s)) :=
          mul_le_mul h3 h3 h0 (by positivity)
      _ = 1 / (4 * s) := by
          field_simp
          rw [Real.sq_sqrt hs.le]; ring
  have hfR := tr_fro_nonneg R
  have hRs0 := tr_opNorm_nonneg (Rs K s)
  have t1 : fro (Rs K s * R) ≤ 1 / s * fro R :=
    (tr_fro_mul_left _ _).trans (mul_le_mul_of_nonneg_right h1 hfR)
  have t2 : fro (Rs K s * R * (Kᵀ * Rs K s * K)) ≤ 1 / s * fro R * 2 :=
    (tr_fro_mul_right _ _).trans (mul_le_mul t1 hRK (tr_opNorm_nonneg _) (by positivity))
  have t3 : fro (Xs K s * Rᵀ * Xs K s) ≤ 1 / (4 * s) * fro R := by
    refine (tr_fro_mul_right _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (tr_fro_mul_left _ _) (tr_opNorm_nonneg _)).trans ?_
    rw [projection_fro_transpose]
    calc opNorm (Xs K s) * fro R * opNorm (Xs K s) = (opNorm (Xs K s) * opNorm (Xs K s)) * fro R := by ring
      _ ≤ 1 / (4 * s) * fro R := mul_le_mul_of_nonneg_right hX2 hfR
  calc fro (Rs K s * R - Rs K s * R * (Kᵀ * Rs K s * K) - Xs K s * Rᵀ * Xs K s)
      ≤ fro (Rs K s * R) + fro (Rs K s * R * (Kᵀ * Rs K s * K)) + fro (Xs K s * Rᵀ * Xs K s) :=
        (tr_fro_sub_le (Rs K s * R - Rs K s * R * (Kᵀ * Rs K s * K)) (Xs K s * Rᵀ * Xs K s)).trans
          (add_le_add_left (tr_fro_sub_le (Rs K s * R) (Rs K s * R * (Kᵀ * Rs K s * K))) _)
    _ ≤ 1 / s * fro R + 1 / s * fro R * 2 + 1 / (4 * s) * fro R := add_le_add (add_le_add t1 t2) t3
    _ = (13 / 4) / s * fro R := by
        have hs' : s ≠ 0 := hs.ne'
        field_simp
        ring

private lemma tr_abs_entry_le_fro {a b : ℕ} (A : Mat a b) (i : Fin a) (j : Fin b) :
    |A i j| ≤ fro A := by
  unfold fro
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have h1 : ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ j', ‖A i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  have h3 : A i j ^ 2 = ‖A i j‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  linarith

private lemma tr_Rs_meas {m n : ℕ} {α : Type*} [MeasurableSpace α] {f : α → Mat m n} {g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => Rs (f x) (g x)) := by
  have hc : Continuous (fun p : Mat m n × ℝ => p.1 * p.1ᵀ + p.2 • (1 : Mat m m)) := by
    fun_prop
  have hA : Measurable (fun x => f x * (f x)ᵀ + g x • (1 : Mat m m)) :=
    hc.measurable.comp (hf.prodMk hg)
  have hdet : Measurable (fun x => (f x * (f x)ᵀ + g x • (1 : Mat m m)).det) :=
    (continuous_id.matrix_det).measurable.comp hA
  have hadj : Measurable (fun x => (f x * (f x)ᵀ + g x • (1 : Mat m m)).adjugate) :=
    (continuous_id.matrix_adjugate).measurable.comp hA
  have he : (fun x => Rs (f x) (g x)) = fun x =>
      (f x * (f x)ᵀ + g x • (1 : Mat m m)).det⁻¹ • (f x * (f x)ᵀ + g x • (1 : Mat m m)).adjugate := by
    funext x
    unfold Rs
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [he]
  exact hdet.inv.smul hadj

private lemma tr_mat_mul_meas {a b c : ℕ} {α : Type*} [MeasurableSpace α] {f : α → Mat a b}
    {g : α → Mat b c} (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => f x * g x) :=
  (continuous_fst.matrix_mul continuous_snd).measurable.comp (hf.prodMk hg)

private lemma tr_mat_T_meas {a b : ℕ} {α : Type*} [MeasurableSpace α] {f : α → Mat a b}
    (hf : Measurable f) : Measurable (fun x => (f x)ᵀ) :=
  continuous_id.matrix_transpose.measurable.comp hf

private lemma tr_trdX_meas {m n : ℕ} {α : Type*} [MeasurableSpace α] {f g : α → Mat m n} {h : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable (fun x => trdX (f x) (g x) (h x)) := by
  have hR := tr_Rs_meas hf hh
  unfold trdX
  exact (tr_mat_mul_meas hR hg).sub (tr_mat_mul_meas (tr_mat_mul_meas hR
    ((tr_mat_mul_meas hg (tr_mat_T_meas hf)).add (tr_mat_mul_meas hf (tr_mat_T_meas hg))))
    (tr_mat_mul_meas hR hf))

private lemma tr_inv_sq_integrable {ϱ : ℝ} (hϱ : 0 < ϱ) :
    IntegrableOn (fun u : ℝ => (ϱ + u ^ 2)⁻¹) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (max 1 ϱ⁻¹)).integrableOn) ?_ ?_
  · exact (Continuous.inv₀ (by fun_prop) (fun u => by positivity)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u => ?_
    have h1 : 0 < ϱ + u ^ 2 := by positivity
    have h2 : 0 < 1 + u ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h1)]
    rw [inv_le_iff_one_le_mul₀ h1]
    have hc1 : 1 ≤ max 1 ϱ⁻¹ := le_max_left _ _
    have hc2 : ϱ⁻¹ ≤ max 1 ϱ⁻¹ := le_max_right _ _
    have hcϱ : 1 ≤ max 1 ϱ⁻¹ * ϱ := by
      calc (1 : ℝ) = ϱ⁻¹ * ϱ := (inv_mul_cancel₀ hϱ.ne').symm
        _ ≤ max 1 ϱ⁻¹ * ϱ := mul_le_mul_of_nonneg_right hc2 hϱ.le
    have he : max 1 ϱ⁻¹ * (1 + u ^ 2)⁻¹ * (ϱ + u ^ 2) = max 1 ϱ⁻¹ * (ϱ + u ^ 2) / (1 + u ^ 2) := by
      field_simp
    rw [he, le_div_iff₀ h2]
    nlinarith [sq_nonneg u]

private lemma tr_dirDeriv_integral {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (N R : Mat m n) (i : Fin m) (j : Fin n) :
    IntegrableOn (fun u : ℝ => trdX N R (ϱ + u ^ 2) i j) (Ioi (0 : ℝ)) ∧
    dirDeriv ϱ N R i j = (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), trdX N R (ϱ + u ^ 2) i j := by
  have hs : ∀ u : ℝ, 0 < ϱ + u ^ 2 := fun u => by positivity
  set F : ℝ → ℝ → ℝ := fun t u => Xs (N + t • R) (ϱ + u ^ 2) i j with hF
  set F' : ℝ → ℝ → ℝ := fun t u => trdX (N + t • R) R (ϱ + u ^ 2) i j with hF'
  have hQ : (fun t : ℝ => Q ϱ (N + t • R) i j) = fun t => (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), F t u := by
    funext t
    exact (Muon.Setup.lem_app_setup_contour ϱ hϱ (N + t • R)).1 i j
  have hmeasF : ∀ t, AEStronglyMeasurable (F t) (volume.restrict (Ioi (0 : ℝ))) := by
    intro t
    have : Measurable (fun u : ℝ => Rs (N + t • R) (ϱ + u ^ 2) * (N + t • R)) :=
      tr_mat_mul_meas (tr_Rs_meas measurable_const (by fun_prop)) measurable_const
    exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp this)).aestronglyMeasurable
  have hmeasF' : ∀ t, AEStronglyMeasurable (F' t) (volume.restrict (Ioi (0 : ℝ))) := by
    intro t
    have : Measurable (fun u : ℝ => trdX (N + t • R) R (ϱ + u ^ 2)) :=
      tr_trdX_meas measurable_const measurable_const (by fun_prop)
    exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp this)).aestronglyMeasurable
  have hbound_int : Integrable (fun u : ℝ => (13 / 4) * fro R * (ϱ + u ^ 2)⁻¹) (volume.restrict (Ioi (0 : ℝ))) :=
    (tr_inv_sq_integrable hϱ).const_mul _
  have hbd : ∀ t u, ‖F' t u‖ ≤ (13 / 4) * fro R * (ϱ + u ^ 2)⁻¹ := by
    intro t u
    rw [Real.norm_eq_abs]
    refine (tr_abs_entry_le_fro _ i j).trans ((tr_trdX_bound _ R (hs u)).trans (le_of_eq ?_))
    field_simp
  have hint0 : Integrable (F 0) (volume.restrict (Ioi (0 : ℝ))) := by
    have := (Muon.Setup.lem_app_setup_contour ϱ hϱ (N + (0 : ℝ) • R)).2.1 i j
    exact this
  obtain ⟨hint', hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := F) (F' := F') (x₀ := 0) (s := univ)
    (bound := fun u => (13 / 4) * fro R * (ϱ + u ^ 2)⁻¹) Filter.univ_mem
    (Filter.Eventually.of_forall hmeasF) hint0 (hmeasF' 0)
    (Filter.Eventually.of_forall fun u t _ => hbd t u) hbound_int
    (Filter.Eventually.of_forall fun u t _ => tr_Xs_entry_hasDerivAt N R (hs u) t i j)
  have hF'0 : F' 0 = fun u => trdX N R (ϱ + u ^ 2) i j := by
    funext u; simp [hF']
  rw [hF'0] at hint' hderiv
  refine ⟨hint', ?_⟩
  unfold dirDeriv
  simp only [Matrix.of_apply]
  rw [hQ]
  exact (hderiv.const_mul (2 / Real.pi)).deriv

/-! ### Independence of the batch of step `t + j` from the other samples -/

private lemma tr_indep_other_batch {m n B : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (cs : ChainSamples P m n B) (t j : ℕ) :
    Indep (otherSigma cs t j) (batchSigma cs t j) P := by
  have hind := (iIndepFun_iff_iIndep _ _ _).mp cs.indep
  have hle : ∀ i, MeasurableSpace.comap
      (Sum.elim (fun q : ℤ × Fin B => cs.act q.1 q.2)
        (fun q : ℤ × ℕ × Fin B => cs.aux q.1 q.2.1 q.2.2) i : Ω → Vec m × Vec n) inferInstance ≤ mΩ := by
    intro i
    rcases i with q | q
    · exact (cs.meas_act q.1 q.2).comap_le
    · exact (cs.meas_aux q.1 q.2.1 q.2.2).comap_le
  have hdisj : Disjoint
      {i : (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B) | (∃ q : ℤ × Fin B, i = Sum.inl q ∧ q.1 ≠ (t : ℤ) + j + 1) ∨
        (∃ q : ℤ × ℕ × Fin B, i = Sum.inr q)}
      {i | ∃ q : ℤ × Fin B, i = Sum.inl q ∧ q.1 = (t : ℤ) + j + 1} := by
    rw [Set.disjoint_left]
    rintro i (⟨q, rfl, h1⟩ | ⟨q, rfl⟩) ⟨q', hq', h3⟩
    · cases hq'; exact h1 h3
    · cases hq'
  have := indep_iSup_of_disjoint hle hind hdisj
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left this ?_) ?_
  · refine sup_le (iSup_le fun s => iSup_le fun hs => iSup_le fun a => ?_)
      (iSup_le fun t' => iSup_le fun i => iSup_le fun a => ?_)
    · exact le_iSup₂_of_le (Sum.inl (s, a)) (Or.inl ⟨(s, a), rfl, hs⟩) le_rfl
    · exact le_iSup₂_of_le (Sum.inr (t', i, a)) (Or.inr ⟨(t', i, a), rfl⟩) le_rfl
  · refine iSup_le fun a => ?_
    exact le_iSup₂_of_le (Sum.inl (((t : ℤ) + j + 1), a)) ⟨(((t : ℤ) + j + 1), a), rfl, rfl⟩ le_rfl

private lemma tr_indep_lintegral {Ω α β : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [MeasurableSpace α] [MeasurableSpace β] {X : Ω → α} {Y : Ω → β}
    (hX : Measurable X) (hY : Measurable Y) (hind : IndepFun X Y P)
    (f : α → β → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) :
    ∫⁻ ω, f (X ω) (Y ω) ∂P = ∫⁻ x, ∫⁻ y, f x y ∂(P.map Y) ∂(P.map X) := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hind
  have h1 : ∫⁻ ω, f (X ω) (Y ω) ∂P = ∫⁻ z, Function.uncurry f z ∂(P.map (fun ω => (X ω, Y ω))) := by
    rw [lintegral_map hf (hX.prodMk hY)]
    rfl
  rw [h1, hmap, lintegral_prod _ hf.aemeasurable]
  rfl

private lemma tr_batchSigma_meas {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (cs : ChainSamples P m n B) (t j : ℕ) :
    Measurable[batchSigma cs t j] (fun ω (a : Fin B) => cs.act ((t : ℤ) + j + 1) a ω) := by
  refine @Measurable.of_eval Ω (Fin B) (fun _ => Vec m × Vec n) (batchSigma cs t j) _ _ fun a => ?_
  exact (measurable_iff_comap_le.2 (le_iSup (fun a => MeasurableSpace.comap
    (cs.act ((t : ℤ) + j + 1) a) inferInstance) a))

private lemma tr_iid_act {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (cs : ChainSamples P m n B) (s : ℤ) :
    IIDBatch P ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) (cs.act s) := by
  refine ⟨fun a => (cs.meas_act _ a).aemeasurable, fun a => cs.law_act _ a, ?_⟩
  exact cs.indep.precomp (g := fun a : Fin B => Sum.inl (s, a))
    (fun a b h => congrArg Prod.snd (Sum.inl.inj h))

private lemma tr_batchGrad_cont {m n B : ℕ} (C : Covariances m n) :
    Continuous (fun x : Mat m n × (Fin B → Vec m × Vec n) => batchGrad x.1 (fun a => phys C (x.2 a))) := by
  unfold batchGrad grad resid phys outer
  fun_prop

private lemma tr_fro_cont {m n : ℕ} : Continuous (fun M : Mat m n => fro M) := by
  open scoped Matrix.Norms.Frobenius in
  have h : (fun M : Mat m n => fro M) = fun M => ‖M‖ := funext fro_eq_norm
  rw [h]
  exact continuous_norm

private lemma tr_fro_sq_cont {m n : ℕ} : Continuous (fun M : Mat m n => fro M ^ 2) := by
  simp_rw [projection_fro_sq]
  fun_prop

private def trGsq {m n B : ℕ} (C : Covariances m n) (x : Mat m n) (y : Fin B → Vec m × Vec n) : ℝ :=
  fro (batchGrad x (fun a => phys C (y a))) ^ 2

private lemma trGsq_meas {m n B : ℕ} (C : Covariances m n) :
    Measurable (Function.uncurry (trGsq (B := B) C)) :=
  (tr_fro_sq_cont.comp (tr_batchGrad_cont C)).measurable

private lemma trGsq_meas_right {m n B : ℕ} (C : Covariances m n) (x : Mat m n) :
    Measurable (fun y : Fin B → Vec m × Vec n => trGsq C x y) :=
  (trGsq_meas (B := B) C).of_uncurry_left

private lemma trGsq_nonneg {m n B : ℕ} (C : Covariances m n) (x : Mat m n) (y : Fin B → Vec m × Vec n) :
    0 ≤ trGsq C x y := sq_nonneg _

/-- Second moment of the gradient of the batch of step `t + j` at a random matrix independent of it. -/
private lemma tr_batch_sq_bound {m n B : ℕ} {Ω : Type*} (𝓖 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (C : Covariances m n) (γstar CSig : ℝ) (hB : 0 < B)
    (hS : SizeFin C B γstar CSig) (cs : ChainSamples P m n B) (t j : ℕ) (h𝓖 : 𝓖 ≤ mΩ) (hind : Indep 𝓖 (batchSigma cs t j) P)
    (X : Ω → Mat m n) (hX : Measurable[𝓖] X) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ ω, fro (rOut C * X ω * rIn C) ≤ c) :
    Integrable (fun ω => fro (batchGrad (X ω) (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) ^ 2) P ∧
    ∫ ω, fro (batchGrad (X ω) (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) ^ 2 ∂P ≤
      cMConst CSig γstar * (B : ℝ) * c ^ 2 := by
  set Y : Ω → (Fin B → Vec m × Vec n) := fun ω a => cs.act ((t : ℤ) + j + 1) a ω with hYdef
  have hYb := tr_batchSigma_meas cs t j
  have hble : batchSigma cs t j ≤ mΩ := iSup_le fun a => (cs.meas_act _ a).comap_le
  have hY : Measurable Y := hYb.mono hble le_rfl
  have hXm : Measurable X := hX.mono h𝓖 le_rfl
  have hindXY : IndepFun X Y P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind (measurable_iff_comap_le.1 hX))
      (measurable_iff_comap_le.1 hYb)
  have hcM : 0 ≤ cMConst CSig γstar := by unfold cMConst; positivity
  have hgm := trGsq_meas (B := B) C
  have hfeq : (fun ω => fro (batchGrad (X ω) (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) ^ 2) =
      fun ω => trGsq C (X ω) (Y ω) := rfl
  have hinner : ∀ x : Mat m n, ∫⁻ y, ENNReal.ofReal (trGsq C x y) ∂(P.map Y) ≤
      ENNReal.ofReal (cMConst CSig γstar * (B : ℝ) * fro (rOut C * x * rIn C) ^ 2) := by
    intro x
    have hb := lem_app_dyn_batch_i C γstar CSig hB hS (cs.act ((t : ℤ) + j + 1)) (tr_iid_act cs _) x
    have hgx : Measurable (fun y => ENNReal.ofReal (trGsq C x y)) :=
      ENNReal.measurable_ofReal.comp (trGsq_meas_right (B := B) C x)
    rw [lintegral_map hgx hY]
    change ∫⁻ ω, ENNReal.ofReal (fro (batchGrad x (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) ^ 2) ∂P ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hb.1 (Eventually.of_forall fun ω => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hb.2
  have hlint : ∫⁻ ω, ENNReal.ofReal (trGsq C (X ω) (Y ω)) ∂P ≤ ENNReal.ofReal (cMConst CSig γstar * (B : ℝ) * c ^ 2) := by
    rw [tr_indep_lintegral hXm hY hindXY (fun x y => ENNReal.ofReal (trGsq C x y))
      (ENNReal.measurable_ofReal.comp hgm)]
    have hmX : Measurable (fun x : Mat m n => ENNReal.ofReal (cMConst CSig γstar * (B : ℝ) * fro (rOut C * x * rIn C) ^ 2)) := by
      refine ENNReal.measurable_ofReal.comp (Measurable.const_mul ?_ _)
      exact (tr_fro_sq_cont.comp (by fun_prop : Continuous (fun x : Mat m n => rOut C * x * rIn C))).measurable
    calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (trGsq C x y) ∂(P.map Y) ∂(P.map X)
        ≤ ∫⁻ x, ENNReal.ofReal (cMConst CSig γstar * (B : ℝ) * fro (rOut C * x * rIn C) ^ 2) ∂(P.map X) :=
          lintegral_mono hinner
      _ = ∫⁻ ω, ENNReal.ofReal (cMConst CSig γstar * (B : ℝ) * fro (rOut C * X ω * rIn C) ^ 2) ∂P :=
          lintegral_map hmX hXm
      _ ≤ ∫⁻ _ω, ENNReal.ofReal (cMConst CSig γstar * (B : ℝ) * c ^ 2) ∂P := by
          refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
          have h1 := hc ω
          have h0 := tr_fro_nonneg (rOut C * X ω * rIn C)
          have : fro (rOut C * X ω * rIn C) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ h0 h1 2
          have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
          exact mul_le_mul_of_nonneg_left this (mul_nonneg hcM hB0)
      _ = ENNReal.ofReal (cMConst CSig γstar * (B : ℝ) * c ^ 2) := by
          rw [lintegral_const, measure_univ, mul_one]
  have hmeas : AEStronglyMeasurable (fun ω => trGsq C (X ω) (Y ω)) P :=
    (hgm.comp (hXm.prodMk hY)).aestronglyMeasurable
  have hint : Integrable (fun ω => trGsq C (X ω) (Y ω)) P := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => trGsq_nonneg C _ _)]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  rw [hfeq]
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => trGsq_nonneg C _ _) hmeas]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) hlint

/-! ### Scaling of the chains -/

private lemma tr_pairSigma_eq {m n : ℕ} (C : Covariances m n) (D E : Mat m n) :
    pairSigma C D E = frobIP (Arot C D) (Arot C E) := by
  have hO : rOut C * rOut C = C.Sout :=
    CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)
  have hI : rIn C * rIn C = C.Sin :=
    CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)
  unfold pairSigma frobIP Arot
  rw [Matrix.transpose_mul, Matrix.transpose_mul, projection_rOut_transpose, projection_rIn_transpose]
  have e : rOut C * D * rIn C * (rIn C * (Eᵀ * rOut C)) =
      (rOut C * D * (rIn C * rIn C) * Eᵀ) * rOut C := by simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm (rOut C * D * (rIn C * rIn C) * Eᵀ), hI]
  have e2 : rOut C * (rOut C * D * C.Sin * Eᵀ) = (rOut C * rOut C) * D * C.Sin * Eᵀ := by
    simp only [Matrix.mul_assoc]
  rw [e2, hO]

private lemma tr_fro_Arot_eq {m n : ℕ} (C : Covariances m n) (D : Mat m n) :
    fro (Arot C D) = Real.sqrt (2 * riskSigma C D) := by
  rw [eqn_app_setup_whitened_risk, mul_div_cancel₀ _ (two_ne_zero' ℝ), Real.sqrt_sq (tr_fro_nonneg _)]

private lemma tr_pairSigma_smul_left {m n : ℕ} (C : Covariances m n) (c : ℝ) (V W : Mat m n) :
    pairSigma C (c • V) W = c * pairSigma C V W := by
  unfold pairSigma
  simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]

private lemma tr_pairSigma_smul_right {m n : ℕ} (C : Covariances m n) (c : ℝ) (V W : Mat m n) :
    pairSigma C V (c • W) = c * pairSigma C V W := by
  unfold pairSigma
  simp [Matrix.mul_smul, Matrix.transpose_smul, Matrix.trace_smul]

private lemma tr_risk_smul {m n : ℕ} (C : Covariances m n) (c : ℝ) (D : Mat m n) :
    riskSigma C (c • D) = c ^ 2 * riskSigma C D := by
  unfold riskSigma
  rw [tr_pairSigma_smul_left, tr_pairSigma_smul_right]
  ring

private lemma tr_batchGrad_smul {m n B : ℕ} (c : ℝ) (D : Mat m n) (b : Batch m n B) :
    batchGrad (c • D) b = c • batchGrad D b := by
  unfold batchGrad grad resid
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring_nf

private lemma tr_batchGrad_sub {m n B : ℕ} (D D' : Mat m n) (b : Batch m n B) :
    batchGrad (D - D') b = batchGrad D b - batchGrad D' b := by
  unfold batchGrad grad resid
  simp only [Matrix.sub_mulVec, dotProduct_sub, sub_smul, Finset.sum_sub_distrib, smul_sub]

private lemma tr_chainInit_smul {m n B : ℕ} {Ω : Type*} (β : ℝ) (C : Covariances m n) (c : ℝ)
    (D : Mat m n) (aux : ℕ → Fin B → Ω → Vec m × Vec n) (ω : Ω) :
    chainInit β C (c • D) aux ω = c • chainInit β C D aux ω := by
  unfold chainInit
  simp_rw [tr_batchGrad_smul, smul_comm (emaW β _) c]
  exact tsum_const_smul'' (f := fun j => emaW β j • batchGrad D (physBatch C (aux j) ω)) c

private lemma tr_emaChain_smul {m n B : ℕ} (β : ℝ) (c : ℝ) (D : Mat m n) (G : ℤ → Batch m n B)
    (t : ℕ) (init : Mat m n) (k : ℕ) :
    emaChain β (c • D) G t (c • init) k = c • emaChain β D G t init k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [emaChain, ih, tr_batchGrad_smul, smul_add, smul_comm β c, smul_comm (1 - β) c]

private lemma tr_emaChain_sub {m n B : ℕ} (β : ℝ) (D : Mat m n) (G : ℤ → Batch m n B)
    (t : ℕ) (M init : Mat m n) (k : ℕ) :
    emaChain β D G t M k - emaChain β D G t init k = (β ^ k) • (M - init) := by
  induction k with
  | zero => simp [emaChain]
  | succ k ih =>
    have h : emaChain β D G t M (k + 1) - emaChain β D G t init (k + 1) =
        β • (emaChain β D G t M k - emaChain β D G t init k) := by
      simp only [emaChain, smul_sub]
      abel
    rw [h, ih, smul_smul, ← pow_succ']

/-- Scaling of the directional derivative of the filter: `D Q_{c²ϱ}(cN)[R] = c⁻¹ D Q_ϱ(N)[R]`. -/
private lemma tr_dirDeriv_scale {m n : ℕ} {ϱ c : ℝ} (hϱ : 0 < ϱ) (hc : 0 < c) (N R : Mat m n) :
    dirDeriv (c ^ 2 * ϱ) (c • N) R = c⁻¹ • dirDeriv ϱ N R := by
  ext i j
  unfold dirDeriv
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have hfun : (fun t : ℝ => Q (c ^ 2 * ϱ) (c • N + t • R) i j) =
      fun t : ℝ => Q ϱ (N + (c⁻¹ * t) • R) i j := by
    funext t
    have h1 : c • N + t • R = c • (N + (c⁻¹ * t) • R) := by
      rw [smul_add, smul_smul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    rw [h1, Muon.Setup.prop_app_setup_scaling_i _ (by positivity) _ c hc]
    congr 2
    field_simp
  rw [hfun]
  have hd := projection_Q_contDiff (m := m) (n := n) hϱ
  have hdiff : DifferentiableAt ℝ (fun t : ℝ => Q ϱ (N + t • R) i j) (c⁻¹ * 0) := by
    have hQd := (hd.differentiable (by simp)) (fun a b => N a b + (c⁻¹ * 0) * R a b)
    have hl : DifferentiableAt ℝ (fun t : ℝ => fun a b => N a b + t * R a b) (c⁻¹ * 0) := by
      fun_prop
    have := ((differentiableAt_pi.mp ((differentiableAt_pi.mp (hQd.comp _ hl)) i)) j)
    convert this using 1
    funext t
    rfl
  have := (hdiff.hasDerivAt.comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul c⁻¹))
  rw [show (fun t : ℝ => Q ϱ (N + (c⁻¹ * t) • R) i j) =
    (fun t : ℝ => Q ϱ (N + t • R) i j) ∘ (HMul.hMul c⁻¹) from rfl, this.deriv]
  simp only [mul_zero, mul_one]
  ring

/-! ### Measurability of the frozen chains with respect to sub-σ-algebras -/

private lemma tr_bg_meas {m n B : ℕ} {Ω : Type*} (𝓖 : MeasurableSpace Ω) [MeasurableSpace Ω]
    {P : Measure Ω} (C : Covariances m n) (cs : ChainSamples P m n B) (D : Mat m n) (s : ℤ)
    (hs : ∀ a, Measurable[𝓖] (cs.act s a)) :
    Measurable[𝓖] (fun ω => batchGrad D (physBatch C (cs.act s) ω)) := by
  have h1 : Measurable[𝓖] (fun ω => (D, fun a => cs.act s a ω)) :=
    measurable_const.prodMk (@Measurable.of_eval Ω (Fin B) (fun _ => Vec m × Vec n) 𝓖 _ _ fun a => hs a)
  have e : (fun ω => batchGrad D (physBatch C (cs.act s) ω)) =
      (fun x : Mat m n × (Fin B → Vec m × Vec n) => batchGrad x.1 (fun a => phys C (x.2 a))) ∘
        (fun ω => (D, fun a => cs.act s a ω)) := by
    funext ω; rfl
  rw [e]
  exact (tr_batchGrad_cont C).measurable.comp h1

private lemma tr_ema_meas {m n B : ℕ} {Ω : Type*} (𝓖 : MeasurableSpace Ω) [MeasurableSpace Ω]
    {P : Measure Ω} (β : ℝ) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n)
    (init : Ω → Mat m n) (hinit : Measurable[𝓖] init) (k : ℕ)
    (hk : ∀ i < k, ∀ a, Measurable[𝓖] (cs.act ((t : ℤ) + i + 1) a)) :
    Measurable[𝓖] (fun ω => emaChain β D (fun s => physBatch C (cs.act s) ω) t (init ω) k) := by
  induction k with
  | zero => exact hinit
  | succ k ih =>
    have ih' := ih (fun i hi a => hk i (by omega) a)
    have hb := tr_bg_meas 𝓖 C cs D ((t : ℤ) + k + 1) (hk k (by omega))
    exact (ih'.const_smul β).add (hb.const_smul (1 - β))

private lemma tr_N0_meas {m n B : ℕ} {Ω : Type*} (𝓖 : MeasurableSpace Ω) [MeasurableSpace Ω]
    {P : Measure Ω} (β : ℝ) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n)
    (haux : ∀ j a, Measurable[𝓖] (cs.aux (t : ℤ) j a)) :
    Measurable[𝓖] (fun ω => chainInit β C D (cs.aux (t : ℤ)) ω) := by
  have : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  have : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  have : MeasurableAdd₂ (Mat m n) :=
    inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  unfold chainInit
  have hb : ∀ j, Measurable[𝓖] (fun ω => batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) := by
    intro j
    have h1 : Measurable[𝓖] (fun ω => (D, fun a => cs.aux (t : ℤ) j a ω)) :=
      measurable_const.prodMk (@Measurable.of_eval Ω (Fin B) (fun _ => Vec m × Vec n) 𝓖 _ _ fun a => haux j a)
    have e : (fun ω => batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) =
        (fun x : Mat m n × (Fin B → Vec m × Vec n) => batchGrad x.1 (fun a => phys C (x.2 a))) ∘
          (fun ω => (D, fun a => cs.aux (t : ℤ) j a ω)) := by
      funext ω; rfl
    rw [e]
    exact (tr_batchGrad_cont C).measurable.comp h1
  have hb' : ∀ j, Measurable[𝓖] (fun ω => emaW β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) :=
    fun j => (hb j).const_smul (emaW β j)
  exact @Measurable.tsum Ω (Mat m n) ℕ 𝓖 _ _ _ _ _ _ _ _ _ _ _ _ hb'

private lemma tr_Q_meas {m n : ℕ} {Ω : Type*} (𝓖 : MeasurableSpace Ω) (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    {f : Ω → Mat m n} (hf : Measurable[𝓖] f) : Measurable[𝓖] (fun ω => Q ℓ (f ω)) := by
  have h1 : Measurable[𝓖] (fun ω => ((⟨ℓ, hℓ⟩ : Ici (0 : ℝ)), f ω)) := measurable_const.prodMk hf
  exact (measurable_Q (m := m) (n := n)).comp h1

private lemma tr_act_other {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (cs : ChainSamples P m n B) (t j : ℕ) (s : ℤ) (hs : s ≠ (t : ℤ) + j + 1) (a : Fin B) :
    Measurable[otherSigma cs t j] (cs.act s a) := by
  refine measurable_iff_comap_le.2 (le_sup_of_le_left ?_)
  exact le_iSup₂_of_le s hs (le_iSup_of_le a le_rfl)

private lemma tr_aux_other {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (cs : ChainSamples P m n B) (t j : ℕ) (t' : ℤ) (i : ℕ) (a : Fin B) :
    Measurable[otherSigma cs t j] (cs.aux t' i a) := by
  refine measurable_iff_comap_le.2 (le_sup_of_le_right ?_)
  exact le_iSup_of_le t' (le_iSup_of_le i (le_iSup_of_le a le_rfl))

private lemma tr_other_le {m n B : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (cs : ChainSamples P m n B) (t j : ℕ) : otherSigma cs t j ≤ mΩ :=
  sup_le (iSup_le fun s' => iSup_le fun _ => iSup_le fun b => (cs.meas_act s' b).comap_le)
    (iSup_le fun t' => iSup_le fun i => iSup_le fun b => (cs.meas_aux t' i b).comap_le)

/-- The frozen updates `V̂_k` (initial buffer `m`) and `V_k` (stationary) before step `t + j` are measurable
with respect to the samples other than the batch of step `t + j`. -/
private lemma tr_frozenV_other {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t j k : ℕ) (hkj : k < j)
    (D : Mat m n) (hℓ : 0 ≤ physRidge p C D) (init : Ω → Mat m n)
    (hinit : Measurable[otherSigma cs t j] init) :
    Measurable[otherSigma cs t j] (fun ω => Q (physRidge p C D)
      (emaChain p.β D (fun s => physBatch C (cs.act s) ω) t (init ω) (k + 1))) := by
  refine tr_Q_meas _ _ hℓ (tr_ema_meas _ p.β C cs t D init hinit (k + 1) fun i hi a => ?_)
  exact tr_act_other cs t j _ (by omega) a

/-! ### Frobenius pairing helpers -/

private lemma tr_frobIP_eq_sum {m n : ℕ} (X Y : Mat m n) :
    frobIP X Y = ∑ i, ∑ j, X i j * Y i j := by
  simp [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply]

private lemma tr_frobIP_smul_right {m n : ℕ} (X Y : Mat m n) (c : ℝ) :
    frobIP X (c • Y) = c * frobIP X Y := by
  simp [frobIP, Matrix.transpose_smul, Matrix.mul_smul, Matrix.trace_smul]

private lemma tr_frobIP_add_right {m n : ℕ} (X Y Z : Mat m n) :
    frobIP X (Y + Z) = frobIP X Y + frobIP X Z := by
  simp [frobIP, Matrix.transpose_add, Matrix.mul_add, Matrix.trace_add]

private lemma tr_frobIP_sub_right {m n : ℕ} (X Y Z : Mat m n) :
    frobIP X (Y - Z) = frobIP X Y - frobIP X Z := by
  simp [frobIP, Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub]

private lemma tr_frobIP_neg_right {m n : ℕ} (X Y : Mat m n) :
    frobIP X (-Y) = -frobIP X Y := by
  simp [frobIP, Matrix.transpose_neg, Matrix.mul_neg, Matrix.trace_neg]

private lemma tr_frobIP_sum_right {m n : ℕ} {ι : Type*} (X : Mat m n) (s : Finset ι) (Y : ι → Mat m n) :
    frobIP X (∑ i ∈ s, Y i) = ∑ i ∈ s, frobIP X (Y i) := by
  simp [frobIP, Matrix.transpose_sum, Matrix.mul_sum, Matrix.trace_sum]

private lemma tr_frobIP_cont {m n : ℕ} (X : Mat m n) : Continuous (fun Y : Mat m n => frobIP X Y) := by
  unfold frobIP; fun_prop

private lemma tr_frobIP_dirDeriv_eq {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (T N R : Mat m n) :
    IntegrableOn (fun u : ℝ => frobIP T (trdX N R (ϱ + u ^ 2))) (Ioi (0 : ℝ)) ∧
    frobIP T (dirDeriv ϱ N R) = (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), frobIP T (trdX N R (ϱ + u ^ 2)) := by
  have hrep := fun i j => tr_dirDeriv_integral hϱ N R i j
  simp_rw [tr_frobIP_eq_sum]
  have hint : ∀ i j, IntegrableOn (fun u : ℝ => T i j * trdX N R (ϱ + u ^ 2) i j) (Ioi (0 : ℝ)) :=
    fun i j => (hrep i j).1.const_mul _
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(hrep i j).2, integral_const_mul]
  ring

private lemma tr_integrable_of_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f P) (hf0 : ∀ ω, 0 ≤ f ω)
    (hsq : Integrable (fun ω => f ω ^ 2) P) (q : ℝ) (hq : 0 < q) :
    Integrable f P ∧ ∫ ω, f ω ∂P ≤ ((∫ ω, f ω ^ 2 ∂P) + q ^ 2) / (2 * q) := by
  have hg : Integrable (fun ω => (f ω ^ 2 + q ^ 2) / (2 * q)) P :=
    (hsq.add (integrable_const _)).div_const _
  have hle : ∀ ω, f ω ≤ (f ω ^ 2 + q ^ 2) / (2 * q) := by
    intro ω
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (f ω - q)]
  have hint : Integrable f P :=
    hg.mono' hf (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]; exact hle ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω, f ω ∂P ≤ ∫ ω, (f ω ^ 2 + q ^ 2) / (2 * q) ∂P := integral_mono hint hg hle
    _ = _ := by
      rw [integral_div, integral_add hsq (integrable_const _)]
      simp

private lemma tr_emaW_mem {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (j : ℕ) : emaW β j ∈ Icc (0 : ℝ) 1 := by
  unfold emaW
  have h1 : 0 ≤ 1 - β := by linarith
  have h2 : β ^ j ≤ 1 := pow_le_one₀ hβ.1 hβ.2.le
  have h3 : 0 ≤ β ^ j := pow_nonneg hβ.1 j
  constructor
  · positivity
  · nlinarith

private lemma tr_Q_bounds {m n : ℕ} (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (K : Mat m n) :
    opNorm (Q ℓ K) ≤ 1 ∧ fro (Q ℓ K) ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
  obtain ⟨h1, h2, h3, -⟩ := lem_app_setup_filter_i ℓ hℓ K
  refine ⟨h1, ?_⟩
  rw [← Real.sqrt_sq (tr_fro_nonneg _)]
  exact Real.sqrt_le_sqrt (h2.trans (by exact_mod_cast h3))

private lemma tr_min_le {m n B : ℕ} (C : Covariances m n) (γ CS : ℝ) (hS : SizeFin C B γ CS) :
    ((min m n : ℕ) : ℝ) ≤ γ * B ∧ (m : ℝ) ≤ γ * B ∧ (n : ℝ) ≤ γ * B := by
  have h := hS.1
  rw [Nat.cast_max] at h
  refine ⟨?_, (le_max_left _ _).trans h, (le_max_right _ _).trans h⟩
  rw [Nat.cast_min]
  exact (min_le_left _ _).trans ((le_max_left _ _).trans h)

/-! ### The frozen objects -/

/-- The stationary chain `N_{k-1}` at `(t, D)` (index `k`). -/
private def trNs (p : DynParams) {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n) (k : ℕ) (ω : Ω) : Mat m n :=
  emaChain p.β D (fun s => physBatch C (cs.act s) ω) t (chainInit p.β C D (cs.aux (t : ℤ)) ω) k

/-- The same-buffer chain `N̂_{k-1}` at `(t, D, M)` (index `k`). -/
private def trNh (p : DynParams) {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n) (k : ℕ) (ω : Ω) : Mat m n :=
  emaChain p.β D (fun s => physBatch C (cs.act s) ω) t M k

/-- The startup difference `A_k = V̂_k − V_k`. -/
private def trA (p : DynParams) {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n) (k : ℕ) (ω : Ω) : Mat m n :=
  Q (physRidge p C D) (trNh p C cs t D M (k + 1) ω) - Q (physRidge p C D) (trNs p C cs t D (k + 1) ω)

private lemma tr_ridge_nonneg (p : DynParams) {m n : ℕ} (C : Covariances m n) (D : Mat m n) :
    0 ≤ physRidge p C D := by
  unfold physRidge
  rw [eqn_app_setup_whitened_risk]
  have := p.hϱ
  positivity

private lemma tr_trA_other {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t j k : ℕ) (hkj : k < j)
    (D M : Mat m n) : Measurable[otherSigma cs t j] (trA p C cs t D M k) := by
  have h1 := tr_frozenV_other p C cs t j k hkj D (tr_ridge_nonneg p C D) (fun _ => M) measurable_const
  have h2 := tr_frozenV_other p C cs t j k hkj D (tr_ridge_nonneg p C D) _
    (tr_N0_meas _ p.β C cs t D fun i a => tr_aux_other cs t j _ i a)
  exact h1.sub h2

private lemma tr_trA_bounds {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n) (k : ℕ)
    (hS : SizeFin C B p.γstar p.CSig) (ω : Ω) :
    opNorm (trA p C cs t D M k ω) ≤ 2 ∧
      fro (trA p C cs t D M k ω) ≤ 2 * Real.sqrt p.γstar * Real.sqrt B := by
  have hℓ := tr_ridge_nonneg p C D
  obtain ⟨o1, f1⟩ := tr_Q_bounds _ hℓ (trNh p C cs t D M (k + 1) ω)
  obtain ⟨o2, f2⟩ := tr_Q_bounds _ hℓ (trNs p C cs t D (k + 1) ω)
  have hmin := (tr_min_le C _ _ hS).1
  have hsq : Real.sqrt ((min m n : ℕ) : ℝ) ≤ Real.sqrt p.γstar * Real.sqrt B := by
    rw [← Real.sqrt_mul' _ (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt hmin
  constructor
  · unfold trA
    rw [opNorm_eq_norm]
    open scoped Matrix.Norms.L2Operator in
    refine (norm_sub_le _ _).trans ?_
    rw [← opNorm_eq_norm, ← opNorm_eq_norm]
    linarith
  · unfold trA
    refine (tr_fro_sub_le _ _).trans ?_
    linarith

private lemma tr_stationaryN_eq {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n) (r : ℕ) (ω : Ω) :
    stationaryN p C cs t D r ω = trNs p C cs t D (r + 1) ω := rfl

private lemma tr_trNs_smul {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (c : ℝ) (D : Mat m n)
    (k : ℕ) (ω : Ω) : trNs p C cs t (c • D) k ω = c • trNs p C cs t D k ω := by
  unfold trNs
  rw [tr_chainInit_smul, tr_emaChain_smul]

private lemma tr_inv_sq_integral_le {ϱ : ℝ} (hϱ : 0 < ϱ) :
    ∫ u in Ioi (0 : ℝ), (ϱ + u ^ 2)⁻¹ ≤ max 1 ϱ⁻¹ * (Real.pi / 2) := by
  have hle : ∀ u : ℝ, (ϱ + u ^ 2)⁻¹ ≤ max 1 ϱ⁻¹ * (1 + u ^ 2)⁻¹ := by
    intro u
    have h1 : 0 < ϱ + u ^ 2 := by positivity
    have h2 : 0 < 1 + u ^ 2 := by positivity
    rw [inv_le_iff_one_le_mul₀ h1]
    have hc2 : ϱ⁻¹ ≤ max 1 ϱ⁻¹ := le_max_right _ _
    have hc1 : 1 ≤ max 1 ϱ⁻¹ := le_max_left _ _
    have hcϱ : 1 ≤ max 1 ϱ⁻¹ * ϱ := by
      calc (1 : ℝ) = ϱ⁻¹ * ϱ := (inv_mul_cancel₀ hϱ.ne').symm
        _ ≤ max 1 ϱ⁻¹ * ϱ := mul_le_mul_of_nonneg_right hc2 hϱ.le
    have he : max 1 ϱ⁻¹ * (1 + u ^ 2)⁻¹ * (ϱ + u ^ 2) = max 1 ϱ⁻¹ * (ϱ + u ^ 2) / (1 + u ^ 2) := by
      field_simp
    rw [he, le_div_iff₀ h2]
    nlinarith [sq_nonneg u]
  calc ∫ u in Ioi (0 : ℝ), (ϱ + u ^ 2)⁻¹ ≤ ∫ u in Ioi (0 : ℝ), max 1 ϱ⁻¹ * (1 + u ^ 2)⁻¹ :=
        setIntegral_mono (tr_inv_sq_integrable hϱ) (integrable_inv_one_add_sq.integrableOn.const_mul _) hle
    _ = max 1 ϱ⁻¹ * (Real.pi / 2) := by
        rw [integral_const_mul, integral_Ioi_inv_one_add_sq]
        simp

set_option maxHeartbeats 4000000 in
/-- The change of the argument, one pair `k < j`: `prop:app-dyn-reduction` with `E = A_k`, after the
integral representation of `D Q_ℓ` (`lem:app-setup-contour`) and the scaling `2𝓡(D) = 1`. -/
private lemma tr_T2 (certQ : Muon.External.GaussianQuadFormLp) (p : DynParams) (cP rlo : ℝ) (hrlo : 0 < rlo) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (C : Covariances m n) (cs : ChainSamples P m n B) (t j k r : ℕ) (D M Pt : Mat m n),
      SizeFin C B p.γstar p.CSig → 0 < B → rlo ≤ riskSigma C D →
      fro Pt ≤ cP → opNorm Pt ≤ cP → k < j → j ≤ r →
      Integrable (fun ω => frobIP Pt (dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
          (emaW p.β (r - j) • batchGrad (trA p C cs t D M k ω) (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)))) P ∧
      |∫ ω, frobIP Pt (dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
          (emaW p.β (r - j) • batchGrad (trA p C cs t D M k ω) (physBatch C (cs.act ((t : ℤ) + j + 1)) ω))) ∂P|
        ≤ K * (Real.sqrt B * emaW p.β (r - j) +
          Real.sqrt B * emaW p.β (r - j) ^ 2 * ∫ ω, |pairSigma C D (trA p C cs t D M k ω)| ∂P) := by
  set cE : ℝ := 2 * max 1 (Real.sqrt p.γstar) with hcE
  obtain ⟨Cred, hred⟩ := prop_app_dyn_reduction certQ p.γstar p.CSig p.ϱ cP cE p.hϱ
  obtain ⟨Cm, hmin⟩ := lem_app_dyn_minor cP p.γstar p.CSig p.ϱ p.hϱ
  set Iϱ : ℝ := ∫ u in Ioi (0 : ℝ), (p.ϱ + u ^ 2)⁻¹ with hIϱ
  have hIϱ0 : 0 ≤ Iϱ := setIntegral_nonneg measurableSet_Ioi (fun u _ => by have := p.hϱ; positivity)
  set clo : ℝ := Real.sqrt (2 * rlo) with hclo
  have hclo0 : 0 < clo := Real.sqrt_pos.mpr (by linarith)
  set Cr : ℝ := max Cred 0 with hCr
  set Cm' : ℝ := max Cm 0 with hCm'
  have hCr0 : 0 ≤ Cr := le_max_right _ _
  have hCm0 : 0 ≤ Cm' := le_max_right _ _
  have hϱh : 0 ≤ p.ϱ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg p.hϱ.le _
  refine ⟨clo⁻¹ * (2 / Real.pi) * Iϱ * (Cr + Cm' * p.ϱ ^ (-(1 / 2 : ℝ)) * clo⁻¹), by positivity, ?_⟩
  intro Ω _ P _ m n B C cs t j k r D M Pt hS hB hR hPf hPo hkj hjr
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hsB : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBr
  obtain ⟨hmin', hm, hn⟩ := tr_min_le C _ _ hS
  set ϖ : ℝ := emaW p.β (r - j) with hϖdef
  have hϖ := tr_emaW_mem p.hβ (r - j)
  set A : Ω → Mat m n := trA p C cs t D M k with hAdef
  set R' : Ω → Mat m n := fun ω => ϖ • batchGrad (A ω) (physBatch C (cs.act ((t : ℤ) + j + 1)) ω) with hR'def
  -- measurability
  have hAo : Measurable[otherSigma cs t j] A := tr_trA_other p C cs t j k hkj D M
  have hAm : Measurable A := hAo.mono (tr_other_le cs t j) le_rfl
  have hGm : Measurable (fun ω => batchGrad (A ω) (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) := by
    have h1 : Measurable (fun ω => (A ω, fun a => cs.act ((t : ℤ) + j + 1) a ω)) :=
      hAm.prodMk (measurable_pi_iff.mpr fun a => cs.meas_act _ a)
    have e : (fun ω => batchGrad (A ω) (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) =
        (fun x : Mat m n × (Fin B → Vec m × Vec n) => batchGrad x.1 (fun a => phys C (x.2 a))) ∘
          (fun ω => (A ω, fun a => cs.act ((t : ℤ) + j + 1) a ω)) := by
      funext ω; rfl
    rw [e]
    exact (tr_batchGrad_cont C).measurable.comp h1
  have hR'm : Measurable R' := hGm.const_smul ϖ
  -- second moment of the gradient at `A`
  have hAbd := fun ω => tr_trA_bounds p C cs t D M k hS ω
  have hArot : ∀ ω, fro (rOut C * A ω * rIn C) ≤ p.CSig * (2 * Real.sqrt p.γstar * Real.sqrt B) := by
    intro ω
    exact (projection_Arot_fro_le p C hS (A ω)).trans
      (mul_le_mul_of_nonneg_left (hAbd ω).2 (le_trans zero_le_one p.hC))
  have hG2 := tr_batch_sq_bound (otherSigma cs t j) C p.γstar p.CSig hB hS cs t j (tr_other_le cs t j)
    (tr_indep_other_batch cs t j) A hAo _ (by have := le_trans zero_le_one p.hC; positivity) hArot
  have hfroG : Integrable (fun ω => fro (batchGrad (A ω) (physBatch C (cs.act ((t : ℤ) + j + 1)) ω))) P :=
    (tr_integrable_of_sq _ (tr_fro_cont.measurable.comp hGm).aestronglyMeasurable
      (fun ω => tr_fro_nonneg _) hG2.1 1 one_pos).1
  have hfroR' : Integrable (fun ω => fro (R' ω)) P := by
    have : (fun ω => fro (R' ω)) = fun ω => |ϖ| * fro (batchGrad (A ω) (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) := by
      funext ω; simp only [hR'def, tr_fro_smul]
    rw [this]; exact hfroG.const_mul _
  -- the scaling `2𝓡(D) = 1`
  have hRpos : 0 < riskSigma C D := lt_of_lt_of_le hrlo hR
  set c : ℝ := Real.sqrt (2 * riskSigma C D) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hcsq : c ^ 2 = 2 * riskSigma C D := Real.sq_sqrt (by linarith)
  have hclo_le : clo ≤ c := Real.sqrt_le_sqrt (by linarith)
  have hcinv : c⁻¹ ≤ clo⁻¹ := inv_anti₀ hclo0 hclo_le
  obtain ⟨D', hD'def⟩ : ∃ D' : Mat m n, D' = c⁻¹ • D := ⟨_, rfl⟩
  have hDD : D = c • D' := by rw [hD'def, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hD' : riskSigma C D' = 1 / 2 := by
    rw [hD'def, tr_risk_smul, inv_pow, hcsq]
    field_simp
  have hℓ : physRidge p C D = c ^ 2 * p.ϱ := by unfold physRidge; rw [hcsq]
  have hNs : ∀ ω, trNs p C cs t D (r + 1) ω = c • stationaryN p C cs t D' r ω := by
    intro ω
    rw [tr_stationaryN_eq, ← tr_trNs_smul, ← hDD]
  have hg' : ∀ ω, pairSigma C D' (A ω) = c⁻¹ * pairSigma C D (A ω) := by
    intro ω; rw [hD'def, tr_pairSigma_smul_left]
  set N' : Ω → Mat m n := fun ω => stationaryN p C cs t D' r ω with hN'def
  have hN'm : Measurable N' := by
    have h0 := tr_N0_meas (P := P) ‹MeasurableSpace Ω› p.β C cs t D' fun i a => cs.meas_aux _ i a
    exact tr_ema_meas ‹MeasurableSpace Ω› p.β C cs t D' _ h0 (r + 1) fun i _ a => cs.meas_act _ a
  set F : Ω → ℝ → ℝ := fun ω u => frobIP Pt (trdX (N' ω) (R' ω) (p.ϱ + u ^ 2)) with hFdef
  have hpt : ∀ ω, frobIP Pt (dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω) (R' ω)) =
      c⁻¹ * ((2 / Real.pi) * ∫ u in Ioi (0 : ℝ), F ω u) := by
    intro ω
    rw [hℓ, hNs, tr_dirDeriv_scale p.hϱ hc, tr_frobIP_smul_right,
      (tr_frobIP_dirDeriv_eq p.hϱ Pt (N' ω) (R' ω)).2]
  -- joint measurability and integrability of `F`
  have hFm : Measurable (Function.uncurry F) := by
    have h1 : Measurable (fun z : Ω × ℝ => trdX (N' z.1) (R' z.1) (p.ϱ + z.2 ^ 2)) :=
      tr_trdX_meas (hN'm.comp measurable_fst) (hR'm.comp measurable_fst) (by fun_prop)
    exact (tr_frobIP_cont Pt).measurable.comp h1
  have hPf0 : 0 ≤ fro Pt := tr_fro_nonneg _
  have hFbd : ∀ ω u, |F ω u| ≤ (fro Pt * (13 / 4) * fro (R' ω)) * (p.ϱ + u ^ 2)⁻¹ := by
    intro ω u
    have hs : 0 < p.ϱ + u ^ 2 := by have := p.hϱ; positivity
    refine (projection_frobIP_le _ _).trans ?_
    calc fro Pt * fro (trdX (N' ω) (R' ω) (p.ϱ + u ^ 2))
        ≤ fro Pt * ((13 / 4) / (p.ϱ + u ^ 2) * fro (R' ω)) :=
          mul_le_mul_of_nonneg_left (tr_trdX_bound _ _ hs) hPf0
      _ = _ := by field_simp
  have hFint : Integrable (Function.uncurry F) (P.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hprod := ((hfroR'.const_mul (fro Pt * (13 / 4))).mul_prod (tr_inv_sq_integrable p.hϱ))
    refine hprod.mono' hFm.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    exact hFbd z.1 z.2
  -- the reduction at each `s = ϱ + u²`
  set Eg : ℝ := ∫ ω, |pairSigma C D (A ω)| ∂P with hEg
  have hEg0 : 0 ≤ Eg := integral_nonneg fun ω => abs_nonneg _
  have hEbd : ∀ ω, opNorm (A ω) ≤ cE ∧ fro (A ω) ≤ cE * Real.sqrt B := by
    intro ω
    obtain ⟨h1, h2⟩ := hAbd ω
    have hγ : Real.sqrt p.γstar ≤ max 1 (Real.sqrt p.γstar) := le_max_right _ _
    constructor
    · rw [hcE]; linarith [le_max_left 1 (Real.sqrt p.γstar)]
    · rw [hcE]
      calc fro (A ω) ≤ 2 * Real.sqrt p.γstar * Real.sqrt B := h2
        _ ≤ 2 * max 1 (Real.sqrt p.γstar) * Real.sqrt B := by gcongr
  have hEent : ∀ (i : Fin m) (l : Fin n), Measurable fun ω => A ω i l :=
    fun i l => (measurable_pi_apply l).comp ((measurable_pi_apply i).comp hAm)
  have hEind : Indep ((⨆ (i : Fin m) (l : Fin n), MeasurableSpace.comap (fun ω => A ω i l) inferInstance) ⊔
      otherSigma cs t j) (batchSigma cs t j) P := by
    have hle : (⨆ (i : Fin m) (l : Fin n), MeasurableSpace.comap (fun ω => A ω i l) inferInstance) ≤
        otherSigma cs t j :=
      iSup₂_le fun i l => measurable_iff_comap_le.1
        ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp hAo))
    rw [sup_eq_right.mpr hle]
    exact tr_indep_other_batch cs t j
  have hAh : fro (Ahat C D') = 1 := prefix_Ahat_norm C D' (by rw [hD']; norm_num)
  set Λ : ℝ := Cr * Real.sqrt B * ϖ + ϖ ^ 2 * Cm' * Real.sqrt B * p.ϱ ^ (-(1 / 2 : ℝ)) * c⁻¹ * Eg with hΛ
  have hu : ∀ u : ℝ, ‖∫ ω, F ω u ∂P‖ ≤ Λ * (p.ϱ + u ^ 2)⁻¹ := by
    intro u
    set s : ℝ := p.ϱ + u ^ 2 with hsdef
    have hs0 : p.ϱ ≤ s := by rw [hsdef]; nlinarith [sq_nonneg u]
    have hspos : 0 < s := lt_of_lt_of_le p.hϱ hs0
    have hFeq : (fun ω => F ω u) = fun ω => frobIP Pt (dirX (stationaryN p C cs t D' r ω)
        (emaW p.β (r - j) • batchGrad (A ω) (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) s) := by
      funext ω
      rw [tr_dirX_eq _ _ hspos]
    obtain ⟨-, hIa, hred'⟩ := hred p rfl rfl m n B Ω P C cs t j r D' Pt A cP s hm hn hS.2.1 hS.2.2 hB hD'
      ⟨hPf, hPo, le_rfl⟩ hjr hs0 hEbd hEent hEind
    have hFs : ∀ (a : Fin B) ω, |Fs C B (Ahat C D') Pt ϖ s (sampleRemainder p C cs t j r D' a ω)| ≤
        Cm' * Real.sqrt B * s ^ (-(3 / 2 : ℝ)) := by
      intro a ω
      have h := (hmin m n B C (Ahat C D') Pt (sampleRemainder p C cs t j r D' a ω)
        (sampleRemainder p C cs t j r D' a ω) ϖ s cP hB hS.2.1 hS.2.2 hm hn hAh ⟨hPf, hPo, le_rfl⟩ hϖ hs0).2.1
      refine h.trans ?_
      gcongr
      exact le_max_left _ _
    have hsr : s ^ (-(3 / 2 : ℝ)) ≤ p.ϱ ^ (-(1 / 2 : ℝ)) * s⁻¹ := by
      rw [show (-(3 / 2 : ℝ)) = -(1 / 2 : ℝ) + (-1 : ℝ) by norm_num, Real.rpow_add hspos, Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos p.hϱ hs0 (by norm_num))
        (inv_nonneg.mpr hspos.le)
    have hIabd : ∀ a : Fin B, |∫ ω, Fs C B (Ahat C D') Pt ϖ s (sampleRemainder p C cs t j r D' a ω) *
        pairSigma C D' (A ω) ∂P| ≤ Cm' * Real.sqrt B * (p.ϱ ^ (-(1 / 2 : ℝ)) * s⁻¹) * (c⁻¹ * Eg) := by
      intro a
      have hgI : Integrable (fun ω => |pairSigma C D (A ω)|) P := by
        refine Integrable.of_bound ?_ (fro (Arot C D) * (p.CSig * (2 * Real.sqrt p.γstar * Real.sqrt B)))
          (Eventually.of_forall fun ω => ?_)
        · exact ((continuous_abs.comp (show Continuous (fun M : Mat m n => pairSigma C D M) by
            unfold pairSigma; fun_prop)).measurable.comp hAm).aestronglyMeasurable
        · rw [Real.norm_eq_abs, abs_abs, tr_pairSigma_eq]
          refine (projection_frobIP_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_left (hArot ω) (tr_fro_nonneg _)
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ ω, |Fs C B (Ahat C D') Pt ϖ s (sampleRemainder p C cs t j r D' a ω) * pairSigma C D' (A ω)| ∂P
          ≤ ∫ ω, Cm' * Real.sqrt B * (p.ϱ ^ (-(1 / 2 : ℝ)) * s⁻¹) * (c⁻¹ * |pairSigma C D (A ω)|) ∂P := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _)
              ((hgI.const_mul c⁻¹).const_mul _) (Eventually.of_forall fun ω => ?_)
            show |Fs C B (Ahat C D') Pt ϖ s (sampleRemainder p C cs t j r D' a ω) * pairSigma C D' (A ω)| ≤
              Cm' * Real.sqrt B * (p.ϱ ^ (-(1 / 2 : ℝ)) * s⁻¹) * (c⁻¹ * |pairSigma C D (A ω)|)
            rw [abs_mul, hg' ω, abs_mul, abs_of_pos (inv_pos.mpr hc)]
            exact mul_le_mul ((hFs a ω).trans (mul_le_mul_of_nonneg_left hsr (by positivity)))
              le_rfl (by positivity) (by positivity)
        _ = _ := by rw [integral_const_mul, integral_const_mul]
    have hsum : |(emaW p.β (r - j)) ^ 2 / (B : ℝ) * ∑ a : Fin B,
        (∫ ω, Fs C B (Ahat C D') Pt (emaW p.β (r - j)) s
          (sampleRemainder p C cs t j r D' a ω) * pairSigma C D' (A ω) ∂P)| ≤
        ϖ ^ 2 * (Cm' * Real.sqrt B * (p.ϱ ^ (-(1 / 2 : ℝ)) * s⁻¹) * (c⁻¹ * Eg)) := by
      rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos hBr]
      have h1 : |∑ a : Fin B, (∫ ω, Fs C B (Ahat C D') Pt (emaW p.β (r - j)) s
          (sampleRemainder p C cs t j r D' a ω) * pairSigma C D' (A ω) ∂P)| ≤
          ∑ _a : Fin B, Cm' * Real.sqrt B * (p.ϱ ^ (-(1 / 2 : ℝ)) * s⁻¹) * (c⁻¹ * Eg) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => hIabd a)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
      calc ϖ ^ 2 / (B : ℝ) * |∑ a : Fin B, (∫ ω, Fs C B (Ahat C D') Pt (emaW p.β (r - j)) s
          (sampleRemainder p C cs t j r D' a ω) * pairSigma C D' (A ω) ∂P)|
          ≤ ϖ ^ 2 / (B : ℝ) * ((B : ℝ) * (Cm' * Real.sqrt B * (p.ϱ ^ (-(1 / 2 : ℝ)) * s⁻¹) * (c⁻¹ * Eg))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := by field_simp
    rw [hFeq, Real.norm_eq_abs]
    have hCred : Cred * Real.sqrt B * emaW p.β (r - j) / s ≤ Cr * Real.sqrt B * ϖ * s⁻¹ := by
      have h0 : 0 ≤ Real.sqrt B * ϖ * s⁻¹ := by have := hϖ.1; positivity
      calc Cred * Real.sqrt B * emaW p.β (r - j) / s = Cred * (Real.sqrt B * ϖ * s⁻¹) := by
            rw [hϖdef]; ring
        _ ≤ Cr * (Real.sqrt B * ϖ * s⁻¹) := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
        _ = Cr * Real.sqrt B * ϖ * s⁻¹ := by ring
    have hfin : |∫ ω, frobIP Pt (dirX (stationaryN p C cs t D' r ω)
        (emaW p.β (r - j) • batchGrad (A ω) (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) s) ∂P| ≤
        Cr * Real.sqrt B * ϖ * s⁻¹ + ϖ ^ 2 * (Cm' * Real.sqrt B * (p.ϱ ^ (-(1 / 2 : ℝ)) * s⁻¹) * (c⁻¹ * Eg)) := by
      have h3 := abs_sub (∫ ω, frobIP Pt (dirX (stationaryN p C cs t D' r ω)
        (emaW p.β (r - j) • batchGrad (A ω) (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) s) ∂P +
        (emaW p.β (r - j)) ^ 2 / (B : ℝ) * ∑ a : Fin B,
          (∫ ω, Fs C B (Ahat C D') Pt (emaW p.β (r - j)) s
            (sampleRemainder p C cs t j r D' a ω) * pairSigma C D' (A ω) ∂P))
        ((emaW p.β (r - j)) ^ 2 / (B : ℝ) * ∑ a : Fin B,
          (∫ ω, Fs C B (Ahat C D') Pt (emaW p.β (r - j)) s
            (sampleRemainder p C cs t j r D' a ω) * pairSigma C D' (A ω) ∂P))
      rw [add_sub_cancel_right] at h3
      exact h3.trans (add_le_add (hred'.trans hCred) hsum)
    refine hfin.trans (le_of_eq ?_)
    rw [hΛ]
    ring
  -- assembly
  have hint_u : Integrable (fun ω => ∫ u in Ioi (0 : ℝ), F ω u) P := hFint.integral_prod_left
  have hfun : (fun ω => frobIP Pt (dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω) (R' ω))) =
      fun ω => c⁻¹ * ((2 / Real.pi) * ∫ u in Ioi (0 : ℝ), F ω u) := funext hpt
  refine ⟨?_, ?_⟩
  · change Integrable (fun ω => frobIP Pt (dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω) (R' ω))) P
    rw [hfun]
    exact (hint_u.const_mul _).const_mul _
  · change |∫ ω, frobIP Pt (dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω) (R' ω)) ∂P| ≤ _
    rw [hfun, integral_const_mul, integral_const_mul, integral_integral_swap hFint]
    have hΛ0 : 0 ≤ Λ := by have := hϖ.1; positivity
    have hbound : ‖∫ u in Ioi (0 : ℝ), ∫ ω, F ω u ∂P‖ ≤ ∫ u in Ioi (0 : ℝ), Λ * (p.ϱ + u ^ 2)⁻¹ :=
      norm_integral_le_of_norm_le ((tr_inv_sq_integrable p.hϱ).const_mul Λ) (Eventually.of_forall hu)
    rw [integral_const_mul] at hbound
    rw [Real.norm_eq_abs] at hbound
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hc), abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi)]
    have hΛle : Λ ≤ (Cr + Cm' * p.ϱ ^ (-(1 / 2 : ℝ)) * clo⁻¹) *
        (Real.sqrt B * ϖ + Real.sqrt B * ϖ ^ 2 * Eg) := by
      rw [hΛ]
      have h1 : Cm' * p.ϱ ^ (-(1 / 2 : ℝ)) * c⁻¹ ≤ Cm' * p.ϱ ^ (-(1 / 2 : ℝ)) * clo⁻¹ :=
        mul_le_mul_of_nonneg_left hcinv (by positivity)
      have h2 : 0 ≤ Real.sqrt B * ϖ ^ 2 * Eg := by positivity
      have h3 : 0 ≤ Real.sqrt B * ϖ := by have := hϖ.1; positivity
      have h4 : 0 ≤ Cm' * p.ϱ ^ (-(1 / 2 : ℝ)) * clo⁻¹ := by positivity
      calc Cr * Real.sqrt B * ϖ + ϖ ^ 2 * Cm' * Real.sqrt B * p.ϱ ^ (-(1 / 2 : ℝ)) * c⁻¹ * Eg
          = Cr * (Real.sqrt B * ϖ) + (Cm' * p.ϱ ^ (-(1 / 2 : ℝ)) * c⁻¹) * (Real.sqrt B * ϖ ^ 2 * Eg) := by ring
        _ ≤ Cr * (Real.sqrt B * ϖ) + (Cm' * p.ϱ ^ (-(1 / 2 : ℝ)) * clo⁻¹) * (Real.sqrt B * ϖ ^ 2 * Eg) := by
            gcongr
        _ ≤ _ := by
            have e : (Cr + Cm' * p.ϱ ^ (-(1 / 2 : ℝ)) * clo⁻¹) * (Real.sqrt B * ϖ + Real.sqrt B * ϖ ^ 2 * Eg) =
                Cr * (Real.sqrt B * ϖ) + (Cm' * p.ϱ ^ (-(1 / 2 : ℝ)) * clo⁻¹) * (Real.sqrt B * ϖ ^ 2 * Eg) +
                (Cr * (Real.sqrt B * ϖ ^ 2 * Eg) + (Cm' * p.ϱ ^ (-(1 / 2 : ℝ)) * clo⁻¹) * (Real.sqrt B * ϖ)) := by ring
            rw [e]
            have := add_nonneg (mul_nonneg hCr0 h2) (mul_nonneg h4 h3)
            linarith
    calc c⁻¹ * (2 / Real.pi * |∫ u in Ioi (0 : ℝ), ∫ ω, F ω u ∂P|)
        ≤ clo⁻¹ * (2 / Real.pi * (Λ * Iϱ)) := by
          gcongr
      _ ≤ clo⁻¹ * (2 / Real.pi * ((Cr + Cm' * p.ϱ ^ (-(1 / 2 : ℝ)) * clo⁻¹) *
          (Real.sqrt B * ϖ + Real.sqrt B * ϖ ^ 2 * Eg) * Iϱ)) := by
          gcongr
      _ = _ := by ring

/-! ### Deterministic algebra of the causal tangent -/

private lemma tr_opNorm_le_fro {m n : ℕ} (K : Mat m n) : opNorm K ≤ fro K := by
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

/-- Cauchy–Schwarz for nonnegative functions with bounded second moments. -/
private lemma tr_cs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (a b : Ω → ℝ) (ha : AEStronglyMeasurable a P) (hb : AEStronglyMeasurable b P)
    (ha0 : ∀ ω, 0 ≤ a ω) (hb0 : ∀ ω, 0 ≤ b ω)
    (ha2 : Integrable (fun ω => a ω ^ 2) P) (hb2 : Integrable (fun ω => b ω ^ 2) P)
    (A Bb : ℝ) (hA : 0 ≤ A) (hBb : 0 ≤ Bb)
    (hA2 : ∫ ω, a ω ^ 2 ∂P ≤ A ^ 2) (hB2 : ∫ ω, b ω ^ 2 ∂P ≤ Bb ^ 2) :
    Integrable (fun ω => a ω * b ω) P ∧ ∫ ω, a ω * b ω ∂P ≤ A * Bb := by
  have hint : Integrable (fun ω => a ω * b ω) P := by
    refine ((ha2.add hb2).div_const 2).mono' (ha.mul hb) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha0 ω) (hb0 ω))]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (a ω - b ω)]
  refine ⟨hint, ?_⟩
  have key : ∀ ε : ℝ, 0 < ε → ∫ ω, a ω * b ω ∂P ≤ (A + ε) * (Bb + ε) := by
    intro ε hε
    set l : ℝ := (Bb + ε) / (A + ε) with hl
    have hl0 : 0 < l := by positivity
    have hpt : ∀ ω, a ω * b ω ≤ (l * a ω ^ 2 + b ω ^ 2 / l) / 2 := by
      intro ω
      have : 0 ≤ (l * a ω - b ω) ^ 2 / l := by positivity
      have e : (l * a ω - b ω) ^ 2 / l = l * a ω ^ 2 + b ω ^ 2 / l - 2 * (a ω * b ω) := by
        field_simp; ring
      linarith
    have hI : Integrable (fun ω => (l * a ω ^ 2 + b ω ^ 2 / l) / 2) P :=
      ((ha2.const_mul l).add (hb2.div_const l)).div_const 2
    calc ∫ ω, a ω * b ω ∂P ≤ ∫ ω, (l * a ω ^ 2 + b ω ^ 2 / l) / 2 ∂P := integral_mono hint hI hpt
      _ = (l * ∫ ω, a ω ^ 2 ∂P + (∫ ω, b ω ^ 2 ∂P) / l) / 2 := by
          rw [integral_div, integral_add (ha2.const_mul l) (hb2.div_const l), integral_const_mul,
            integral_div]
      _ ≤ (l * (A + ε) ^ 2 + (Bb + ε) ^ 2 / l) / 2 := by
          have h1 : A ^ 2 ≤ (A + ε) ^ 2 := by nlinarith
          have h2 : Bb ^ 2 ≤ (Bb + ε) ^ 2 := by nlinarith
          gcongr
          · exact hA2.trans h1
          · exact hB2.trans h2
      _ = (A + ε) * (Bb + ε) := by
          rw [hl]; field_simp; ring
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  obtain ⟨ε, hε, hεδ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * (A + Bb + 1) < δ := by
    refine ⟨δ / (2 * (A + Bb + 1)), by positivity, ?_⟩
    have e : δ / (2 * (A + Bb + 1)) * (A + Bb + 1) = δ / 2 := by field_simp
    rw [e]; linarith
  have hε1 : ε ≤ 1 ∨ 1 < ε := le_or_gt ε 1
  have := key (min ε 1) (lt_min hε one_pos)
  have hm : min ε 1 ≤ ε := min_le_left _ _
  have hm1 : min ε 1 ≤ 1 := min_le_right _ _
  have hm0 : 0 < min ε 1 := lt_min hε one_pos
  calc ∫ ω, a ω * b ω ∂P ≤ (A + min ε 1) * (Bb + min ε 1) := this
    _ = A * Bb + min ε 1 * (A + Bb + min ε 1) := by ring
    _ ≤ A * Bb + ε * (A + Bb + 1) := by gcongr
    _ < A * Bb + δ := by linarith

private lemma tr_emaW_sum_le {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (r : ℕ) :
    ∑ j ∈ Finset.range (r + 1), emaW β (r - j) ≤ 1 := by
  have e : ∑ j ∈ Finset.range (r + 1), emaW β (r - j) =
      ∑ j ∈ Finset.range (r + 1), emaW β (r + 1 - 1 - j) :=
    Finset.sum_congr rfl fun j _ => by congr 1
  rw [e, Finset.sum_range_reflect (fun i => emaW β i) (r + 1)]
  unfold emaW
  rw [← Finset.mul_sum]
  have h := geom_sum_mul β (r + 1)
  have hb : 0 ≤ β ^ (r + 1) := pow_nonneg hβ.1 _
  have e : (1 - β) * ∑ i ∈ Finset.range (r + 1), β ^ i = 1 - β ^ (r + 1) := by linarith
  linarith

private lemma tr_dirDeriv_lin {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (N : Mat m n) :
    ∃ L : Mat m n →ₗ[ℝ] Mat m n, ∀ R, dirDeriv ℓ N R = L R := by
  let F := fderiv ℝ (fun M : Fin m → Fin n → ℝ => fun i j => Q ℓ (Matrix.of M) i j) N
  let L : Mat m n →ₗ[ℝ] Mat m n :=
    { toFun := fun R => Matrix.of (F (fun i j => R i j))
      map_add' := fun R R' => by
        have : (fun i j => (R + R') i j) = (fun i j => R i j) + (fun i j => R' i j) := rfl
        rw [this, map_add]; rfl
      map_smul' := fun c R => by
        have : (fun i j => (c • R) i j) = c • (fun i j => R i j) := rfl
        rw [this, map_smul]; rfl }
  refine ⟨L, fun R => ?_⟩
  exact (projection_filter_fderiv hℓ N R).symm

private lemma tr_dirDeriv_sub {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (N R R' : Mat m n) :
    dirDeriv ℓ N (R - R') = dirDeriv ℓ N R - dirDeriv ℓ N R' := by
  obtain ⟨L, hL⟩ := tr_dirDeriv_lin hℓ N
  rw [hL, hL, hL, map_sub]

private lemma tr_dirDeriv_neg {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (N R : Mat m n) :
    dirDeriv ℓ N (-R) = -dirDeriv ℓ N R := by
  obtain ⟨L, hL⟩ := tr_dirDeriv_lin hℓ N
  rw [hL, hL, map_neg]

private lemma tr_dirDeriv_sum {m n : ℕ} {ι : Type*} {ℓ : ℝ} (hℓ : 0 < ℓ) (N : Mat m n) (s : Finset ι)
    (R : ι → Mat m n) : dirDeriv ℓ N (∑ i ∈ s, R i) = ∑ i ∈ s, dirDeriv ℓ N (R i) := by
  obtain ⟨L, hL⟩ := tr_dirDeriv_lin hℓ N
  rw [hL, map_sum]
  exact Finset.sum_congr rfl fun i _ => (hL _).symm

private lemma tr_causalDot_eq {m n B : ℕ} (p : DynParams) (C : Covariances m n) (G : ℤ → Batch m n B)
    (t : ℕ) (D m0 : Mat m n) (hD : 0 < riskSigma C D) (r : ℕ) :
    causalDot p C G t D m0 r =
      dirDeriv (physRidge p C D) (emaChain p.β D G t m0 (r + 1)) (tangentM p C G t D m0 r)
        + (-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r, frozenV p C G t D m0 k))) •
          ridgeDeriv (physRidge p C D) (emaChain p.β D G t m0 (r + 1)) := by
  ext i j
  unfold causalDot
  simp only [Matrix.of_apply]
  exact ((lem_app_dyn_tangent p C G t D m0 hD).2.2 r i j).deriv

private lemma tr_tangentM_sub {m n B : ℕ} (p : DynParams) (C : Covariances m n) (G : ℤ → Batch m n B)
    (t : ℕ) (D m0 m1 : Mat m n) (r : ℕ) :
    tangentM p C G t D m0 r - tangentM p C G t D m1 r =
      -∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
        emaW p.β (r - j) • batchGrad (frozenV p C G t D m0 k - frozenV p C G t D m1 k) (G ((t : ℤ) + j + 1)) := by
  unfold tangentM
  rw [neg_sub_neg, ← neg_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tr_batchGrad_sub, smul_sub]

private lemma tr_dd_cont {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Continuous (fun q : Mat m n × Mat m n => dirDeriv ℓ q.1 q.2) := by
  have hF := projection_Q_contDiff (m := m) (n := n) hℓ
  have hc : Continuous (fun q : (Fin m → Fin n → ℝ) × (Fin m → Fin n → ℝ) =>
      (fderiv ℝ (fun M : Fin m → Fin n → ℝ => fun i j => Q ℓ (Matrix.of M) i j) q.1) q.2) :=
    ((hF.continuous_fderiv (by simp)).comp continuous_fst).clm_apply continuous_snd
  have e : (fun q : Mat m n × Mat m n => dirDeriv ℓ q.1 q.2) =
      fun q => Matrix.of ((fderiv ℝ (fun M : Fin m → Fin n → ℝ => fun i j => Q ℓ (Matrix.of M) i j) q.1) q.2) := by
    funext q
    exact (projection_filter_fderiv hℓ q.1 q.2).symm
  rw [e]
  exact hc

private lemma tr_rd_cont {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Continuous (fun N : Mat m n => ridgeDeriv ℓ N) := by
  obtain ⟨C4, hC4⟩ := lem_app_dyn_second_iv hℓ le_rfl
  open scoped Matrix.Norms.Frobenius in
  refine Metric.continuous_iff.mpr fun N ε hε => ?_
  refine ⟨ε / (max C4 0 + 1), by positivity, fun N' hN' => ?_⟩
  rw [dist_eq_norm] at hN' ⊢
  rw [← fro_eq_norm] at hN' ⊢
  have h := (hC4 ℓ ⟨le_rfl, le_rfl⟩ N' N).2.2
  have h0 := tr_fro_nonneg (N' - N)
  calc fro (ridgeDeriv ℓ N' - ridgeDeriv ℓ N) ≤ C4 * fro (N' - N) := h
    _ ≤ max C4 0 * fro (N' - N) := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ ≤ max C4 0 * (ε / (max C4 0 + 1)) := mul_le_mul_of_nonneg_left hN'.le (le_max_right _ _)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [le_max_right C4 0]

/-! ### Frozen-world measurability and moment bounds -/

private lemma tr_fro_sum_le {m n : ℕ} {ι : Type*} (s : Finset ι) (X : ι → Mat m n) :
    fro (∑ i ∈ s, X i) ≤ ∑ i ∈ s, fro (X i) := by
  open scoped Matrix.Norms.Frobenius in
  simp only [fro_eq_norm]
  exact norm_sum_le _ _

private lemma tr_trNs_meas {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n) (k : ℕ) :
    Measurable (trNs p C cs t D k) := by
  unfold trNs
  have h0 := tr_N0_meas (P := P) ‹MeasurableSpace Ω› p.β C cs t D fun i a => cs.meas_aux _ i a
  exact tr_ema_meas ‹MeasurableSpace Ω› p.β C cs t D _ h0 k fun i _ a => cs.meas_act _ a

private lemma tr_trNh_meas {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n) (k : ℕ) :
    Measurable (trNh p C cs t D M k) := by
  unfold trNh
  exact tr_ema_meas ‹MeasurableSpace Ω› p.β C cs t D (fun _ => M) measurable_const k fun i _ a => cs.meas_act _ a

private lemma tr_tangentM_meas {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n)
    (init : Ω → Mat m n) (hinit : Measurable init) (r : ℕ) :
    Measurable (fun ω => tangentM p C (fun s => physBatch C (cs.act s) ω) t D (init ω) r) := by
  unfold tangentM
  refine Measurable.neg (Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_)
  refine Measurable.const_smul ?_ (emaW p.β (r - j))
  have hV : Measurable (fun ω => frozenV p C (fun s => physBatch C (cs.act s) ω) t D (init ω) k) :=
    tr_Q_meas _ _ (tr_ridge_nonneg p C D)
      (tr_ema_meas ‹MeasurableSpace Ω› p.β C cs t D init hinit (k + 1) fun i _ a => cs.meas_act _ a)
  have h1 : Measurable (fun ω => (frozenV p C (fun s => physBatch C (cs.act s) ω) t D (init ω) k,
      fun a => cs.act ((t : ℤ) + j + 1) a ω)) :=
    hV.prodMk (measurable_pi_iff.mpr fun a => cs.meas_act _ a)
  have e : (fun ω => batchGrad (frozenV p C (fun s => physBatch C (cs.act s) ω) t D (init ω) k)
      ((fun s => physBatch C (cs.act s) ω) ((t : ℤ) + j + 1))) =
      (fun x : Mat m n × (Fin B → Vec m × Vec n) => batchGrad x.1 (fun a => phys C (x.2 a))) ∘
        (fun ω => (frozenV p C (fun s => physBatch C (cs.act s) ω) t D (init ω) k,
          fun a => cs.act ((t : ℤ) + j + 1) a ω)) := by
    funext ω; rfl
  rw [e]
  exact (tr_batchGrad_cont C).measurable.comp h1

/-- Second moment of the gradient of the batch of step `t + j` at the same-buffer update `V̂_k`, `k < j`. -/
private lemma tr_Ghat_sq {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (hS : SizeFin C B p.γstar p.CSig)
    (hB : 0 < B) (t j k : ℕ) (hkj : k < j) (D : Mat m n) (init : Ω → Mat m n)
    (hinit : Measurable[otherSigma cs t j] init) :
    Integrable (fun ω => fro (batchGrad (frozenV p C (fun s => physBatch C (cs.act s) ω) t D (init ω) k)
      (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) ^ 2) P ∧
    ∫ ω, fro (batchGrad (frozenV p C (fun s => physBatch C (cs.act s) ω) t D (init ω) k)
      (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) ^ 2 ∂P ≤
      cMConst p.CSig p.γstar * (B : ℝ) * (p.CSig * (Real.sqrt p.γstar * Real.sqrt B)) ^ 2 := by
  have hX := tr_frozenV_other p C cs t j k hkj D (tr_ridge_nonneg p C D) init hinit
  have hmin := (tr_min_le C _ _ hS).1
  have hsq : Real.sqrt ((min m n : ℕ) : ℝ) ≤ Real.sqrt p.γstar * Real.sqrt B := by
    rw [← Real.sqrt_mul' _ (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt hmin
  refine tr_batch_sq_bound (otherSigma cs t j) C p.γstar p.CSig hB hS cs t j (tr_other_le cs t j)
    (tr_indep_other_batch cs t j) _ hX _ (by have := le_trans zero_le_one p.hC; positivity) fun ω => ?_
  refine (projection_Arot_fro_le p C hS _).trans ?_
  exact mul_le_mul_of_nonneg_left ((tr_Q_bounds _ (tr_ridge_nonneg p C D) _).2.trans hsq)
    (le_trans zero_le_one p.hC)

/-- Moments of the gradient at `V̂_k` (`k < j`): its mean, and its product with `‖N_{-1}‖_F`. -/
private lemma tr_Ghat_moments {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (hS : SizeFin C B p.γstar p.CSig)
    (hB : 0 < B) (t j k : ℕ) (hkj : k < j) (D M : Mat m n) (hD : 0 < riskSigma C D) :
    Integrable (fun ω => fro (batchGrad (frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)
      (physBatch C (cs.act ((t : ℤ) + j + 1)) ω))) P ∧
    ∫ ω, fro (batchGrad (frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)
      (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) ∂P ≤
      Real.sqrt (cMConst p.CSig p.γstar) * (p.CSig * Real.sqrt p.γstar) * B ∧
    Integrable (fun ω => fro (chainInit p.β C D (cs.aux (t : ℤ)) ω) *
      fro (batchGrad (frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)
      (physBatch C (cs.act ((t : ℤ) + j + 1)) ω))) P ∧
    ∫ ω, fro (chainInit p.β C D (cs.aux (t : ℤ)) ω) *
      fro (batchGrad (frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)
      (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) ∂P ≤
      Real.sqrt (2 * riskSigma C D * cMConst p.CSig p.γstar * B) *
        (Real.sqrt (cMConst p.CSig p.γstar) * (p.CSig * Real.sqrt p.γstar) * B) := by
  have hcM : 0 ≤ cMConst p.CSig p.γstar := by unfold cMConst; positivity
  have hC0 : 0 ≤ p.CSig := le_trans zero_le_one p.hC
  have hBr : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  obtain ⟨hG2, hG2b⟩ := tr_Ghat_sq p C cs hS hB t j k hkj D (fun _ => M) measurable_const
  set Bb : ℝ := Real.sqrt (cMConst p.CSig p.γstar) * (p.CSig * Real.sqrt p.γstar) * B with hBb
  have hBb0 : 0 ≤ Bb := by positivity
  have hBb2 : cMConst p.CSig p.γstar * (B : ℝ) * (p.CSig * (Real.sqrt p.γstar * Real.sqrt B)) ^ 2 = Bb ^ 2 := by
    rw [hBb, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hcM, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  rw [hBb2] at hG2b
  have hGm : Measurable (fun ω => fro (batchGrad (frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)
      (physBatch C (cs.act ((t : ℤ) + j + 1)) ω))) := by
    have hV : Measurable (fun ω => frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k) :=
      tr_Q_meas _ _ (tr_ridge_nonneg p C D)
        (tr_ema_meas ‹MeasurableSpace Ω› p.β C cs t D (fun _ => M) measurable_const (k + 1)
          fun i _ a => cs.meas_act _ a)
    have h1 : Measurable (fun ω => (frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k,
        fun a => cs.act ((t : ℤ) + j + 1) a ω)) :=
      hV.prodMk (measurable_pi_iff.mpr fun a => cs.meas_act _ a)
    have e : (fun ω => batchGrad (frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)
        (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) =
        (fun x : Mat m n × (Fin B → Vec m × Vec n) => batchGrad x.1 (fun a => phys C (x.2 a))) ∘
          (fun ω => (frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k,
            fun a => cs.act ((t : ℤ) + j + 1) a ω)) := by
      funext ω; rfl
    have h2 : Measurable (fun ω => batchGrad (frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)
        (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) := by
      rw [e]; exact (tr_batchGrad_cont C).measurable.comp h1
    exact tr_fro_cont.measurable.comp h2
  obtain ⟨-, hN2, hN2b⟩ := lem_app_dyn_chains_iii p C cs t D M hD hS
  have hNm : Measurable (fun ω => fro (chainInit p.β C D (cs.aux (t : ℤ)) ω)) :=
    tr_fro_cont.measurable.comp (tr_N0_meas (P := P) ‹MeasurableSpace Ω› p.β C cs t D
      fun i a => cs.meas_aux _ i a)
  have h1 := tr_cs (fun _ => (1 : ℝ)) _ aestronglyMeasurable_const hGm.aestronglyMeasurable
    (fun _ => zero_le_one) (fun ω => tr_fro_nonneg _) (integrable_const _) hG2 1 Bb zero_le_one hBb0
    (by simp) hG2b
  simp only [one_mul] at h1
  have hA0 : 0 ≤ 2 * riskSigma C D * cMConst p.CSig p.γstar * B := by positivity
  have h2 := tr_cs _ _ hNm.aestronglyMeasurable hGm.aestronglyMeasurable
    (fun ω => tr_fro_nonneg _) (fun ω => tr_fro_nonneg _) hN2 hG2 _ Bb (Real.sqrt_nonneg _) hBb0
    (by rw [Real.sq_sqrt hA0]; exact hN2b) hG2b
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩


end TrMain


section TrMain
open Muon.DetEquiv

private lemma tr_dd_meas {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f g : Ω → Mat m n} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => dirDeriv ℓ (f ω) (g ω)) := by
  have h := (tr_dd_cont (m := m) (n := n) hℓ).measurable.comp (hf.prodMk hg)
  exact h

private lemma tr_rd_meas {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f : Ω → Mat m n} (hf : Measurable f) :
    Measurable (fun ω => ridgeDeriv ℓ (f ω)) := by
  have h := (tr_rd_cont (m := m) (n := n) hℓ).measurable.comp hf
  exact h

private lemma tr_frobIP_meas {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (X : Mat m n)
    {f : Ω → Mat m n} (hf : Measurable f) :
    Measurable (fun ω => frobIP X (f ω)) := by
  have h := (tr_frobIP_cont X).measurable.comp hf
  exact h

private lemma tr_integral_dsum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (r : ℕ)
    (f : ℕ → ℕ → Ω → ℝ) (hf : ∀ j ∈ Finset.range (r + 1), ∀ k ∈ Finset.range j, Integrable (f j k) P) :
    Integrable (fun ω => ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, f j k ω) P ∧
    ∫ ω, ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, f j k ω ∂P =
      ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, ∫ ω, f j k ω ∂P := by
  have hi : ∀ j ∈ Finset.range (r + 1), Integrable (fun ω => ∑ k ∈ Finset.range j, f j k ω) P :=
    fun j hj => integrable_finsetSum _ fun k hk => hf j hj k hk
  refine ⟨integrable_finsetSum _ hi, ?_⟩
  rw [integral_finsetSum _ hi]
  exact Finset.sum_congr rfl fun j hj => integral_finsetSum _ fun k hk => hf j hj k hk

private lemma tr_double_sum_emaW_le {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (r : ℕ) :
    ∑ j ∈ Finset.range (r + 1), ∑ _k ∈ Finset.range j, emaW β (r - j) ≤ r := by
  have h : ∀ j ∈ Finset.range (r + 1), ∑ _k ∈ Finset.range j, emaW β (r - j) ≤ (r : ℝ) * emaW β (r - j) := by
    intro j hj
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      (tr_emaW_mem hβ _).1
  refine (Finset.sum_le_sum h).trans ?_
  rw [← Finset.mul_sum]
  calc (r : ℝ) * ∑ j ∈ Finset.range (r + 1), emaW β (r - j) ≤ r * 1 :=
        mul_le_mul_of_nonneg_left (tr_emaW_sum_le hβ r) (Nat.cast_nonneg _)
    _ = r := mul_one _

private lemma tr_fro_tangentM_le {m n B : ℕ} (p : DynParams) (C : Covariances m n) (G : ℤ → Batch m n B)
    (t : ℕ) (D m0 : Mat m n) (r : ℕ) :
    fro (tangentM p C G t D m0 r) ≤ ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
      emaW p.β (r - j) * fro (batchGrad (frozenV p C G t D m0 k) (G ((t : ℤ) + j + 1))) := by
  unfold tangentM
  rw [show fro (-∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
      emaW p.β (r - j) • batchGrad (frozenV p C G t D m0 k) (G ((t : ℤ) + j + 1))) =
      fro (∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
      emaW p.β (r - j) • batchGrad (frozenV p C G t D m0 k) (G ((t : ℤ) + j + 1))) by
    rw [← neg_one_smul ℝ, tr_fro_smul]; simp]
  refine (tr_fro_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (tr_fro_sum_le _ _).trans
    (Finset.sum_le_sum fun k _ => ?_))
  rw [tr_fro_smul, abs_of_nonneg (tr_emaW_mem p.hβ _).1]

set_option maxHeartbeats 4000000 in
/-- The change of the derivative operators, first term (`lem:app-dyn-second`(iii), `lem:app-dyn-chains`(ii)). -/
private lemma tr_T1 (p : DynParams) (cP rlo rhi : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (C : Covariances m n) (cs : ChainSamples P m n B) (t r : ℕ) (D M Pt : Mat m n),
      SizeFin C B p.γstar p.CSig → 0 < B → rlo ≤ riskSigma C D → riskSigma C D ≤ rhi →
      fro Pt ≤ cP →
      Integrable (fun ω => frobIP Pt (dirDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r) -
        dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r))) P ∧
      ∫ ω, |frobIP Pt (dirDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r) -
        dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r))| ∂P ≤
        K * (B : ℝ) * ((r : ℝ) * p.β ^ (r + 1) * (fro M + Real.sqrt B)) := by
  have hℓlo : 0 < 2 * rlo * p.ϱ := by have := p.hϱ; positivity
  obtain ⟨C3, hC3⟩ := lem_app_dyn_second_iii hℓlo (show 2 * rlo * p.ϱ ≤ 2 * rhi * p.ϱ by
    have := p.hϱ; nlinarith)
  set C3' : ℝ := max C3 0 with hC3'
  set cP' : ℝ := max cP 0 with hcP'
  have hcM : 0 ≤ cMConst p.CSig p.γstar := by unfold cMConst; positivity
  have hC0 : 0 ≤ p.CSig := le_trans zero_le_one p.hC
  set cG : ℝ := Real.sqrt (cMConst p.CSig p.γstar) * (p.CSig * Real.sqrt p.γstar) with hcG
  set c1 : ℝ := Real.sqrt (2 * rhi * cMConst p.CSig p.γstar) with hc1
  have hcG0 : 0 ≤ cG := by positivity
  have hc10 : 0 ≤ c1 := Real.sqrt_nonneg _
  refine ⟨cP' * C3' * cG * max 1 c1, by positivity, ?_⟩
  intro Ω _ P _ m n B C cs t r D M Pt hS hB hR hRhi hPf
  have hRpos : 0 < riskSigma C D := lt_of_lt_of_le hrlo hR
  have hℓ : physRidge p C D ∈ Icc (2 * rlo * p.ϱ) (2 * rhi * p.ϱ) := by
    unfold physRidge; have := p.hϱ
    constructor <;> nlinarith
  have hℓpos : 0 < physRidge p C D := lt_of_lt_of_le hℓlo hℓ.1
  have hβ0 : 0 ≤ p.β ^ (r + 1) := pow_nonneg p.hβ.1 _
  -- the pointwise bound
  set g : ℕ → ℕ → Ω → ℝ := fun j k ω => fro (batchGrad (frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)
      (physBatch C (cs.act ((t : ℤ) + j + 1)) ω)) with hg
  set N0 : Ω → ℝ := fun ω => fro (chainInit p.β C D (cs.aux (t : ℤ)) ω) with hN0
  have hpt : ∀ ω, |frobIP Pt (dirDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r) -
        dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r))| ≤
      cP' * C3' * p.β ^ (r + 1) * ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
        emaW p.β (r - j) * (fro M * g j k ω + N0 ω * g j k ω) := by
    intro ω
    refine (projection_frobIP_le _ _).trans ?_
    have h1 := hC3 _ hℓ (trNh p C cs t D M (r + 1) ω) (trNs p C cs t D (r + 1) ω)
      (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r)
    have hdiff : trNh p C cs t D M (r + 1) ω - trNs p C cs t D (r + 1) ω =
        p.β ^ (r + 1) • (M - chainInit p.β C D (cs.aux (t : ℤ)) ω) := by
      unfold trNh trNs; exact tr_emaChain_sub _ _ _ _ _ _ _
    have hop : opNorm (trNh p C cs t D M (r + 1) ω - trNs p C cs t D (r + 1) ω) ≤
        p.β ^ (r + 1) * (fro M + N0 ω) := by
      rw [hdiff, opNorm_eq_norm]
      open scoped Matrix.Norms.L2Operator in
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ0, ← opNorm_eq_norm]
      exact mul_le_mul_of_nonneg_left ((tr_opNorm_le_fro _).trans (tr_fro_sub_le _ _)) hβ0
    have hM := tr_fro_tangentM_le p C (fun s => physBatch C (cs.act s) ω) t D M r
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
        emaW p.β (r - j) * g j k ω :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
        mul_nonneg (tr_emaW_mem p.hβ _).1 (tr_fro_nonneg _)
    have hC3le : C3 ≤ C3' := le_max_left _ _
    have hC30 : 0 ≤ C3' := le_max_right _ _
    have hPf' : fro Pt ≤ cP' := hPf.trans (le_max_left _ _)
    have hN00 : 0 ≤ N0 ω := tr_fro_nonneg _
    have hfM := tr_fro_nonneg M
    have hre : ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
        emaW p.β (r - j) * (fro M * g j k ω + N0 ω * g j k ω) =
        (fro M + N0 ω) * ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
        emaW p.β (r - j) * g j k ω := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hre]
    calc fro Pt * fro (dirDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r) -
        dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r))
        ≤ cP' * (C3' * (p.β ^ (r + 1) * (fro M + N0 ω)) *
            ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, emaW p.β (r - j) * g j k ω) := by
          refine mul_le_mul hPf' (h1.trans ?_) (tr_fro_nonneg _) (le_max_right _ _)
          refine mul_le_mul (mul_le_mul hC3le hop (tr_opNorm_nonneg _) hC30) hM (tr_fro_nonneg _)
            (mul_nonneg hC30 (by positivity))
      _ = _ := by ring
  -- integrability of the bound
  have hmom : ∀ j ∈ Finset.range (r + 1), ∀ k ∈ Finset.range j,
      Integrable (g j k) P ∧ ∫ ω, g j k ω ∂P ≤ cG * B ∧
      Integrable (fun ω => N0 ω * g j k ω) P ∧
      ∫ ω, N0 ω * g j k ω ∂P ≤ Real.sqrt (2 * riskSigma C D * cMConst p.CSig p.γstar * B) * (cG * B) := by
    intro j _ k hk
    have h := tr_Ghat_moments p C cs hS hB t j k (Finset.mem_range.mp hk) D M hRpos
    exact ⟨h.1, by rw [hcG]; exact h.2.1, h.2.2.1, by rw [hcG]; exact h.2.2.2⟩
  have hbint : Integrable (fun ω => cP' * C3' * p.β ^ (r + 1) * ∑ j ∈ Finset.range (r + 1),
      ∑ k ∈ Finset.range j, emaW p.β (r - j) * (fro M * g j k ω + N0 ω * g j k ω)) P := by
    refine Integrable.const_mul (integrable_finsetSum _ fun j hj => integrable_finsetSum _ fun k hk => ?_) _
    exact (((hmom j hj k hk).1.const_mul (fro M)).add (hmom j hj k hk).2.2.1).const_mul _
  have hNhm := tr_trNh_meas p C cs t D M (r + 1)
  have hNsm := tr_trNs_meas p C cs t D (r + 1)
  have hMhm := tr_tangentM_meas p C cs t D (fun _ => M) measurable_const r
  have hT1m : Measurable (fun ω => frobIP Pt (dirDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r) -
        dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r))) := by
    exact tr_frobIP_meas Pt ((tr_dd_meas hℓpos hNhm hMhm).sub (tr_dd_meas hℓpos hNsm hMhm))
  have hT1int := hbint.mono' hT1m.aestronglyMeasurable (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hpt ω)
  refine ⟨hT1int, ?_⟩
  have hBr : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hsqrt : Real.sqrt (2 * riskSigma C D * cMConst p.CSig p.γstar * B) ≤ c1 * Real.sqrt B := by
    rw [hc1, ← Real.sqrt_mul (mul_nonneg (by linarith) hcM) B]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hcM) hBr)
  have hfM := tr_fro_nonneg M
  calc ∫ ω, |frobIP Pt (dirDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r) -
        dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r))| ∂P
      ≤ ∫ ω, cP' * C3' * p.β ^ (r + 1) * ∑ j ∈ Finset.range (r + 1),
          ∑ k ∈ Finset.range j, emaW p.β (r - j) * (fro M * g j k ω + N0 ω * g j k ω) ∂P :=
        integral_mono hT1int.abs hbint hpt
    _ = cP' * C3' * p.β ^ (r + 1) * ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
          emaW p.β (r - j) * (fro M * ∫ ω, g j k ω ∂P + ∫ ω, N0 ω * g j k ω ∂P) := by
        rw [integral_const_mul, (tr_integral_dsum r (fun j k ω => emaW p.β (r - j) * (fro M * g j k ω + N0 ω * g j k ω))
          fun j hj k hk => (((hmom j hj k hk).1.const_mul (fro M)).add (hmom j hj k hk).2.2.1).const_mul _).2]
        congr 1
        refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
        rw [integral_const_mul, integral_add ((hmom j hj k hk).1.const_mul (fro M)) (hmom j hj k hk).2.2.1,
          integral_const_mul]
    _ ≤ cP' * C3' * p.β ^ (r + 1) * ∑ j ∈ Finset.range (r + 1), ∑ _k ∈ Finset.range j,
          emaW p.β (r - j) * ((fro M + c1 * Real.sqrt B) * (cG * B)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_)
          (by have := le_max_right C3 0; have := le_max_right cP 0; positivity)
        refine mul_le_mul_of_nonneg_left ?_ (tr_emaW_mem p.hβ _).1
        have h1 := mul_le_mul_of_nonneg_left (hmom j hj k hk).2.1 hfM
        have h2 := (hmom j hj k hk).2.2.2.trans (mul_le_mul_of_nonneg_right hsqrt (by positivity))
        nlinarith
    _ = cP' * C3' * p.β ^ (r + 1) * ((fro M + c1 * Real.sqrt B) * (cG * B)) *
          ∑ j ∈ Finset.range (r + 1), ∑ _k ∈ Finset.range j, emaW p.β (r - j) := by
        have e : ∀ j, ∑ _k ∈ Finset.range j, emaW p.β (r - j) * ((fro M + c1 * Real.sqrt B) * (cG * B)) =
            (∑ _k ∈ Finset.range j, emaW p.β (r - j)) * ((fro M + c1 * Real.sqrt B) * (cG * B)) :=
          fun j => (Finset.sum_mul _ _ _).symm
        simp_rw [e, ← Finset.sum_mul]
        ring
    _ ≤ cP' * C3' * p.β ^ (r + 1) * ((fro M + c1 * Real.sqrt B) * (cG * B)) * r :=
        mul_le_mul_of_nonneg_left (tr_double_sum_emaW_le p.hβ r)
          (by have := le_max_right C3 0; have := le_max_right cP 0; positivity)
    _ ≤ cP' * C3' * p.β ^ (r + 1) * ((max 1 c1 * (fro M + Real.sqrt B)) * (cG * B)) * r := by
        have h1 : fro M + c1 * Real.sqrt B ≤ max 1 c1 * (fro M + Real.sqrt B) := by
          have := le_max_left 1 c1; have := le_max_right 1 c1
          nlinarith [Real.sqrt_nonneg (B : ℝ)]
        gcongr
    _ = cP' * C3' * cG * max 1 c1 * (B : ℝ) * ((r : ℝ) * p.β ^ (r + 1) * (fro M + Real.sqrt B)) := by ring

end TrMain

private lemma tr_pairSigma_sum_right {m n : ℕ} {ι : Type*} (C : Covariances m n) (D : Mat m n)
    (s : Finset ι) (V : ι → Mat m n) : pairSigma C D (∑ i ∈ s, V i) = ∑ i ∈ s, pairSigma C D (V i) := by
  unfold pairSigma
  simp [Matrix.transpose_sum, Matrix.mul_sum, Matrix.trace_sum]

private lemma tr_pairSigma_sub_right {m n : ℕ} (C : Covariances m n) (D V W : Mat m n) :
    pairSigma C D (V - W) = pairSigma C D V - pairSigma C D W := by
  unfold pairSigma
  simp [Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub]

private lemma tr_pairSigma_bound {m n B : ℕ} (p : DynParams) (C : Covariances m n)
    (hS : SizeFin C B p.γstar p.CSig) (D V : Mat m n) :
    |pairSigma C D V| ≤ Real.sqrt (2 * riskSigma C D) * (p.CSig * fro V) := by
  rw [tr_pairSigma_eq]
  refine (projection_frobIP_le _ _).trans ?_
  rw [tr_fro_Arot_eq]
  exact mul_le_mul_of_nonneg_left (projection_Arot_fro_le p C hS V) (Real.sqrt_nonneg _)

private lemma tr_frozenV_fro {m n B : ℕ} (p : DynParams) (C : Covariances m n)
    (hS : SizeFin C B p.γstar p.CSig) (G : ℤ → Batch m n B) (t : ℕ) (D m0 : Mat m n) (k : ℕ) :
    fro (frozenV p C G t D m0 k) ≤ Real.sqrt p.γstar * Real.sqrt B := by
  have hmin := (tr_min_le C _ _ hS).1
  refine (tr_Q_bounds _ (tr_ridge_nonneg p C D) _).2.trans ?_
  rw [← Real.sqrt_mul' _ (Nat.cast_nonneg _)]
  exact Real.sqrt_le_sqrt hmin

/-- `|ℓ̂̇_r| ≤ 2ϱ r √(2rhi) C_Σ √γ √B`. -/
private lemma tr_lam_bound {m n B : ℕ} (p : DynParams) (C : Covariances m n)
    (hS : SizeFin C B p.γstar p.CSig) (G : ℤ → Batch m n B) (t : ℕ) (D m0 : Mat m n) (r : ℕ)
    (rhi : ℝ) (hR : riskSigma C D ≤ rhi) :
    |2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r, frozenV p C G t D m0 k)| ≤
      2 * p.ϱ * r * (Real.sqrt (2 * rhi) * (p.CSig * (Real.sqrt p.γstar * Real.sqrt B))) := by
  have hϱ := p.hϱ
  have hC0 : 0 ≤ p.CSig := le_trans zero_le_one p.hC
  rw [tr_pairSigma_sum_right, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * p.ϱ),
    show 2 * p.ϱ * (r : ℝ) * (Real.sqrt (2 * rhi) * (p.CSig * (Real.sqrt p.γstar * Real.sqrt B))) =
      2 * p.ϱ * ((r : ℝ) * (Real.sqrt (2 * rhi) * (p.CSig * (Real.sqrt p.γstar * Real.sqrt B)))) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ 2 * p.ϱ)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ k ∈ Finset.range r, |pairSigma C D (frozenV p C G t D m0 k)| ≤
      Real.sqrt (2 * rhi) * (p.CSig * (Real.sqrt p.γstar * Real.sqrt B)) := by
    intro k _
    refine (tr_pairSigma_bound p C hS D _).trans ?_
    exact mul_le_mul (Real.sqrt_le_sqrt (by linarith)) (mul_le_mul_of_nonneg_left
      (tr_frozenV_fro p C hS G t D m0 k) hC0) (mul_nonneg hC0 (tr_fro_nonneg _)) (Real.sqrt_nonneg _)
  refine (Finset.sum_le_sum h).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

private lemma tr_lam_meas {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n)
    (init : Ω → Mat m n) (hinit : Measurable init) (r : ℕ) :
    Measurable (fun ω => -(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
      frozenV p C (fun s => physBatch C (cs.act s) ω) t D (init ω) k))) := by
  have hV : ∀ k, Measurable (fun ω => frozenV p C (fun s => physBatch C (cs.act s) ω) t D (init ω) k) :=
    fun k => tr_Q_meas _ _ (tr_ridge_nonneg p C D)
      (tr_ema_meas ‹MeasurableSpace Ω› p.β C cs t D init hinit (k + 1) fun i _ a => cs.meas_act _ a)
  have hs : Measurable (fun ω => ∑ k ∈ Finset.range r,
      frozenV p C (fun s => physBatch C (cs.act s) ω) t D (init ω) k) :=
    Finset.measurable_sum _ fun k _ => hV k
  have hc : Continuous (fun V : Mat m n => pairSigma C D V) := by unfold pairSigma; fun_prop
  have h := hc.measurable.comp hs
  exact (h.const_mul (2 * p.ϱ)).neg

private lemma tr_E_fro_N0 {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (hS : SizeFin C B p.γstar p.CSig)
    (t : ℕ) (D : Mat m n) (hD : 0 < riskSigma C D) :
    Integrable (fun ω => fro (chainInit p.β C D (cs.aux (t : ℤ)) ω)) P ∧
    ∫ ω, fro (chainInit p.β C D (cs.aux (t : ℤ)) ω) ∂P ≤
      Real.sqrt (2 * riskSigma C D * cMConst p.CSig p.γstar * B) := by
  obtain ⟨-, hN2, hN2b⟩ := lem_app_dyn_chains_iii p C cs t D 0 hD hS
  have hcM : 0 ≤ cMConst p.CSig p.γstar := by unfold cMConst; positivity
  have hNm : Measurable (fun ω => fro (chainInit p.β C D (cs.aux (t : ℤ)) ω)) :=
    tr_fro_cont.measurable.comp (tr_N0_meas (P := P) ‹MeasurableSpace Ω› p.β C cs t D
      fun i a => cs.meas_aux _ i a)
  have hA0 : 0 ≤ 2 * riskSigma C D * cMConst p.CSig p.γstar * B := by positivity
  have h := tr_cs (fun _ => (1 : ℝ)) _ aestronglyMeasurable_const hNm.aestronglyMeasurable
    (fun _ => zero_le_one) (fun ω => tr_fro_nonneg _) (integrable_const _) hN2 1 _ zero_le_one
    (Real.sqrt_nonneg _) (by simp) (by rw [Real.sq_sqrt hA0]; exact hN2b)
  simp only [one_mul] at h
  exact h

set_option maxHeartbeats 4000000 in
/-- The change of the ridge derivative, third term (`lem:app-dyn-second`(iv), `lem:app-dyn-chains`(ii)). -/
private lemma tr_T3 (p : DynParams) (cP rlo rhi : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (C : Covariances m n) (cs : ChainSamples P m n B) (t r : ℕ) (D M Pt : Mat m n),
      SizeFin C B p.γstar p.CSig → 0 < B → rlo ≤ riskSigma C D → riskSigma C D ≤ rhi →
      fro Pt ≤ cP →
      Integrable (fun ω => frobIP Pt ((-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k))) •
        (ridgeDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω) -
          ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)))) P ∧
      ∫ ω, |frobIP Pt ((-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k))) •
        (ridgeDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω) -
          ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)))| ∂P ≤
        K * Real.sqrt B * ((r : ℝ) * p.β ^ (r + 1) * (fro M + Real.sqrt B)) := by
  have hℓlo : 0 < 2 * rlo * p.ϱ := by have := p.hϱ; positivity
  obtain ⟨C4, hC4⟩ := lem_app_dyn_second_iv hℓlo (show 2 * rlo * p.ϱ ≤ 2 * rhi * p.ϱ by
    have := p.hϱ; nlinarith)
  set C4' : ℝ := max C4 0 with hC4'
  set cP' : ℝ := max cP 0 with hcP'
  have hcM : 0 ≤ cMConst p.CSig p.γstar := by unfold cMConst; positivity
  have hC0 : 0 ≤ p.CSig := le_trans zero_le_one p.hC
  have hϱ := p.hϱ
  set c1 : ℝ := Real.sqrt (2 * rhi * cMConst p.CSig p.γstar) with hc1
  set L : ℝ := 2 * p.ϱ * (Real.sqrt (2 * rhi) * (p.CSig * Real.sqrt p.γstar)) with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨L * cP' * C4' * max 1 c1, by positivity, ?_⟩
  intro Ω _ P _ m n B C cs t r D M Pt hS hB hR hRhi hPf
  have hRpos : 0 < riskSigma C D := lt_of_lt_of_le hrlo hR
  have hℓ : physRidge p C D ∈ Icc (2 * rlo * p.ϱ) (2 * rhi * p.ϱ) := by
    unfold physRidge
    constructor <;> nlinarith
  have hℓpos : 0 < physRidge p C D := lt_of_lt_of_le hℓlo hℓ.1
  have hβ0 : 0 ≤ p.β ^ (r + 1) := pow_nonneg p.hβ.1 _
  have hBr : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hsB := Real.sqrt_nonneg (B : ℝ)
  set N0 : Ω → ℝ := fun ω => fro (chainInit p.β C D (cs.aux (t : ℤ)) ω) with hN0
  have hpt : ∀ ω, |frobIP Pt ((-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k))) •
        (ridgeDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω) -
          ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)))| ≤
      (L * r * Real.sqrt B) * cP' * C4' * p.β ^ (r + 1) * (fro M + N0 ω) := by
    intro ω
    rw [tr_frobIP_smul_right, abs_mul, abs_neg]
    have hlam := tr_lam_bound p C hS (fun s => physBatch C (cs.act s) ω) t D M r rhi hRhi
    have hlam' : |2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
        frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)| ≤ L * r * Real.sqrt B := by
      refine hlam.trans (le_of_eq ?_); rw [hL]; ring
    have hdiff : trNh p C cs t D M (r + 1) ω - trNs p C cs t D (r + 1) ω =
        p.β ^ (r + 1) • (M - chainInit p.β C D (cs.aux (t : ℤ)) ω) := by
      unfold trNh trNs; exact tr_emaChain_sub _ _ _ _ _ _ _
    have hrd := (hC4 _ hℓ (trNh p C cs t D M (r + 1) ω) (trNs p C cs t D (r + 1) ω)).2.2
    rw [hdiff, tr_fro_smul, abs_of_nonneg hβ0] at hrd
    have hfr : fro (ridgeDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω) -
        ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)) ≤
        C4' * (p.β ^ (r + 1) * (fro M + N0 ω)) :=
      hrd.trans (mul_le_mul (le_max_left _ _) (mul_le_mul_of_nonneg_left (tr_fro_sub_le _ _) hβ0)
        (mul_nonneg hβ0 (tr_fro_nonneg _)) (le_max_right _ _))
    have hip := (projection_frobIP_le Pt _).trans (mul_le_mul (hPf.trans (le_max_left cP 0)) hfr
      (tr_fro_nonneg _) (le_max_right _ _))
    calc |2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)| *
        |frobIP Pt (ridgeDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω) -
          ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω))|
        ≤ (L * r * Real.sqrt B) * (cP' * (C4' * (p.β ^ (r + 1) * (fro M + N0 ω)))) :=
          mul_le_mul hlam' hip (abs_nonneg _) (by positivity)
      _ = _ := by ring
  obtain ⟨hN0i, hN0b⟩ := tr_E_fro_N0 p C cs hS t D hRpos
  have hbint : Integrable (fun ω => (L * r * Real.sqrt B) * cP' * C4' * p.β ^ (r + 1) * (fro M + N0 ω)) P :=
    ((integrable_const _).add hN0i).const_mul _
  have hNhm := tr_trNh_meas p C cs t D M (r + 1)
  have hNsm := tr_trNs_meas p C cs t D (r + 1)
  have hlm := tr_lam_meas p C cs t D (fun _ => M) measurable_const r
  have hm : Measurable (fun ω => frobIP Pt ((-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k))) •
        (ridgeDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω) -
          ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)))) :=
    tr_frobIP_meas Pt (hlm.smul ((tr_rd_meas hℓpos hNhm).sub (tr_rd_meas hℓpos hNsm)))
  have hint := hbint.mono' hm.aestronglyMeasurable (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hpt ω)
  refine ⟨hint, ?_⟩
  have hsqrt : Real.sqrt (2 * riskSigma C D * cMConst p.CSig p.γstar * B) ≤ c1 * Real.sqrt B := by
    rw [hc1, ← Real.sqrt_mul (mul_nonneg (by linarith) hcM) B]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hcM) hBr)
  have hfM := tr_fro_nonneg M
  calc ∫ ω, |frobIP Pt ((-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k))) •
        (ridgeDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω) -
          ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)))| ∂P
      ≤ ∫ ω, (L * r * Real.sqrt B) * cP' * C4' * p.β ^ (r + 1) * (fro M + N0 ω) ∂P :=
        integral_mono hint.abs hbint hpt
    _ = (L * r * Real.sqrt B) * cP' * C4' * p.β ^ (r + 1) * (fro M + ∫ ω, N0 ω ∂P) := by
        rw [integral_const_mul, integral_add (integrable_const _) hN0i, integral_const]
        simp only [probReal_univ, one_smul]
        rfl
    _ ≤ (L * r * Real.sqrt B) * cP' * C4' * p.β ^ (r + 1) * (max 1 c1 * (fro M + Real.sqrt B)) := by
        have h1 : fro M + ∫ ω, N0 ω ∂P ≤ max 1 c1 * (fro M + Real.sqrt B) := by
          have := le_max_left 1 c1; have := le_max_right 1 c1
          have := hN0b.trans hsqrt
          nlinarith
        have : 0 ≤ (L * r * Real.sqrt B) * cP' * C4' * p.β ^ (r + 1) := by
          have := le_max_right C4 0; have := le_max_right cP 0; positivity
        exact mul_le_mul_of_nonneg_left h1 this
    _ = L * cP' * C4' * max 1 c1 * Real.sqrt B * ((r : ℝ) * p.β ^ (r + 1) * (fro M + Real.sqrt B)) := by ring

private lemma tr_lam_diff {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n) (r : ℕ) (ω : Ω) :
    -(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
        frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)) -
      -(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
        frozenV p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) k)) =
      -(2 * p.ϱ * ∑ k ∈ Finset.range r, pairSigma C D (trA p C cs t D M k ω)) := by
  have e : ∀ x y : ℝ, -(2 * p.ϱ * x) - -(2 * p.ϱ * y) = -(2 * p.ϱ * (x - y)) := fun x y => by ring
  rw [e, ← tr_pairSigma_sub_right, ← Finset.sum_sub_distrib, tr_pairSigma_sum_right]
  rfl

private lemma tr_trA_meas {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n) (k : ℕ) :
    Measurable (trA p C cs t D M k) :=
  (tr_trA_other p C cs t (k + 1) k (Nat.lt_succ_self k) D M).mono (tr_other_le cs t (k + 1)) le_rfl

private lemma tr_g_integrable {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B)
    (hS : SizeFin C B p.γstar p.CSig) (t : ℕ) (D M : Mat m n) (k : ℕ) :
    Integrable (fun ω => |pairSigma C D (trA p C cs t D M k ω)|) P := by
  have hc : Continuous (fun V : Mat m n => |pairSigma C D V|) :=
    continuous_abs.comp (by unfold pairSigma; fun_prop)
  refine Integrable.of_bound (hc.measurable.comp (tr_trA_meas p C cs t D M k)).aestronglyMeasurable
    (Real.sqrt (2 * riskSigma C D) * (p.CSig * (2 * Real.sqrt p.γstar * Real.sqrt B)))
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_abs]
  refine (tr_pairSigma_bound p C hS D _).trans ?_
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (tr_trA_bounds p C cs t D M k hS ω).2
    (le_trans zero_le_one p.hC)) (Real.sqrt_nonneg _)

set_option maxHeartbeats 4000000 in
/-- The change of the ridge scalar, fourth term. -/
private lemma tr_T4 (p : DynParams) (cP rlo rhi : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (C : Covariances m n) (cs : ChainSamples P m n B) (t r : ℕ) (D M Pt : Mat m n),
      SizeFin C B p.γstar p.CSig → 0 < B → rlo ≤ riskSigma C D → riskSigma C D ≤ rhi →
      fro Pt ≤ cP →
      Integrable (fun ω => frobIP Pt ((-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)) -
        -(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) k))) •
        ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω))) P ∧
      ∫ ω, |frobIP Pt ((-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)) -
        -(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) k))) •
        ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω))| ∂P ≤
        K * Real.sqrt B * ∑ k ∈ Finset.range r, ∫ ω, |pairSigma C D (trA p C cs t D M k ω)| ∂P := by
  have hℓlo : 0 < 2 * rlo * p.ϱ := by have := p.hϱ; positivity
  obtain ⟨C4, hC4⟩ := lem_app_dyn_second_iv hℓlo (show 2 * rlo * p.ϱ ≤ 2 * rhi * p.ϱ by
    have := p.hϱ; nlinarith)
  set C4' : ℝ := max C4 0 with hC4'
  set cP' : ℝ := max cP 0 with hcP'
  have hϱ := p.hϱ
  refine ⟨2 * p.ϱ * cP' * C4' * Real.sqrt p.γstar, by positivity, ?_⟩
  intro Ω _ P _ m n B C cs t r D M Pt hS hB hR hRhi hPf
  have hℓ : physRidge p C D ∈ Icc (2 * rlo * p.ϱ) (2 * rhi * p.ϱ) := by
    unfold physRidge
    constructor <;> nlinarith
  have hℓpos : 0 < physRidge p C D := lt_of_lt_of_le hℓlo hℓ.1
  have hmin := (tr_min_le C _ _ hS).1
  have hsq : Real.sqrt ((min m n : ℕ) : ℝ) ≤ Real.sqrt p.γstar * Real.sqrt B := by
    rw [← Real.sqrt_mul' _ (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt hmin
  set g : ℕ → Ω → ℝ := fun k ω => |pairSigma C D (trA p C cs t D M k ω)| with hg
  have hpt : ∀ ω, |frobIP Pt ((-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)) -
        -(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) k))) •
        ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω))| ≤
      (2 * p.ϱ * cP' * C4' * Real.sqrt p.γstar * Real.sqrt B) * ∑ k ∈ Finset.range r, g k ω := by
    intro ω
    rw [tr_lam_diff, tr_frobIP_smul_right, abs_mul, abs_neg, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * p.ϱ)]
    have h1 : |∑ k ∈ Finset.range r, pairSigma C D (trA p C cs t D M k ω)| ≤ ∑ k ∈ Finset.range r, g k ω :=
      Finset.abs_sum_le_sum_abs _ _
    have hrd := (hC4 _ hℓ (trNs p C cs t D (r + 1) ω) (trNs p C cs t D (r + 1) ω)).2.1
    have hrd' : fro (ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)) ≤
        C4' * (Real.sqrt p.γstar * Real.sqrt B) := by
      have := tr_fro_nonneg (ridgeDeriv2 (physRidge p C D) (trNs p C cs t D (r + 1) ω))
      calc fro (ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)) ≤ C4 * Real.sqrt ((min m n : ℕ) : ℝ) := by
            linarith
        _ ≤ C4' * (Real.sqrt p.γstar * Real.sqrt B) :=
            mul_le_mul (le_max_left _ _) hsq (Real.sqrt_nonneg _) (le_max_right _ _)
    have hip := (projection_frobIP_le Pt _).trans (mul_le_mul (hPf.trans (le_max_left cP 0)) hrd'
      (tr_fro_nonneg _) (le_max_right _ _))
    have hs0 : 0 ≤ ∑ k ∈ Finset.range r, g k ω := Finset.sum_nonneg fun k _ => abs_nonneg _
    calc 2 * p.ϱ * |∑ k ∈ Finset.range r, pairSigma C D (trA p C cs t D M k ω)| *
        |frobIP Pt (ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω))|
        ≤ 2 * p.ϱ * (∑ k ∈ Finset.range r, g k ω) * (cP' * (C4' * (Real.sqrt p.γstar * Real.sqrt B))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) hip (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hgi : ∀ k ∈ Finset.range r, Integrable (g k) P := fun k _ => tr_g_integrable p C cs hS t D M k
  have hbint : Integrable (fun ω => (2 * p.ϱ * cP' * C4' * Real.sqrt p.γstar * Real.sqrt B) *
      ∑ k ∈ Finset.range r, g k ω) P := (integrable_finsetSum _ hgi).const_mul _
  have hNsm := tr_trNs_meas p C cs t D (r + 1)
  have hl1 := tr_lam_meas p C cs t D (fun _ => M) measurable_const r
  have hl2 := tr_lam_meas p C cs t D (fun ω => chainInit p.β C D (cs.aux (t : ℤ)) ω)
    (tr_N0_meas (P := P) ‹MeasurableSpace Ω› p.β C cs t D fun i a => cs.meas_aux _ i a) r
  have hm := tr_frobIP_meas Pt ((hl1.sub hl2).smul (tr_rd_meas hℓpos hNsm))
  have hint := hbint.mono' hm.aestronglyMeasurable (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hpt ω)
  refine ⟨hint, ?_⟩
  calc _ ≤ ∫ ω, (2 * p.ϱ * cP' * C4' * Real.sqrt p.γstar * Real.sqrt B) * ∑ k ∈ Finset.range r, g k ω ∂P :=
        integral_mono hint.abs hbint hpt
    _ = _ := by rw [integral_const_mul, integral_finsetSum _ hgi]

set_option maxHeartbeats 4000000 in
/-- The change of the argument, summed over `0 ≤ k < j ≤ r`. -/
private lemma tr_T2sum (certQ : Muon.External.GaussianQuadFormLp) (p : DynParams) (cP rlo : ℝ) (hrlo : 0 < rlo) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (C : Covariances m n) (cs : ChainSamples P m n B) (t r : ℕ) (D M Pt : Mat m n),
      SizeFin C B p.γstar p.CSig → 0 < B → rlo ≤ riskSigma C D →
      fro Pt ≤ cP → opNorm Pt ≤ cP →
      Integrable (fun ω => frobIP Pt (dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
        (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r -
          tangentM p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) r))) P ∧
      |∫ ω, frobIP Pt (dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
        (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r -
          tangentM p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) r)) ∂P| ≤
        K * Real.sqrt B * ((r : ℝ) + ∑ k ∈ Finset.range r, ∫ ω, |pairSigma C D (trA p C cs t D M k ω)| ∂P) := by
  obtain ⟨K2, hK2, hT2⟩ := tr_T2 certQ p cP rlo hrlo
  refine ⟨K2, hK2, ?_⟩
  intro Ω _ P _ m n B C cs t r D M Pt hS hB hR hPf hPo
  have hRpos : 0 < riskSigma C D := lt_of_lt_of_le hrlo hR
  have hℓpos : 0 < physRidge p C D := by unfold physRidge; have := p.hϱ; positivity
  set f : ℕ → ℕ → Ω → ℝ := fun j k ω => frobIP Pt (dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
      (emaW p.β (r - j) • batchGrad (trA p C cs t D M k ω) (physBatch C (cs.act ((t : ℤ) + j + 1)) ω))) with hf
  have hpt : ∀ ω, frobIP Pt (dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
        (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r -
          tangentM p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) r)) =
      -∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, f j k ω := by
    intro ω
    rw [tr_tangentM_sub, tr_dirDeriv_neg hℓpos, tr_frobIP_neg_right, tr_dirDeriv_sum hℓpos, tr_frobIP_sum_right]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tr_dirDeriv_sum hℓpos, tr_frobIP_sum_right]
    rfl
  have hfi : ∀ j ∈ Finset.range (r + 1), ∀ k ∈ Finset.range j, Integrable (f j k) P := by
    intro j hj k hk
    exact (hT2 Ω P m n B C cs t j k r D M Pt hS hB hR hPf hPo (Finset.mem_range.mp hk)
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1
  obtain ⟨hsi, hse⟩ := tr_integral_dsum r f hfi
  have hfun : (fun ω => frobIP Pt (dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
        (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r -
          tangentM p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) r))) =
      fun ω => -∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, f j k ω := funext hpt
  rw [hfun]
  refine ⟨hsi.neg, ?_⟩
  rw [integral_neg, abs_neg, hse]
  set S : ℝ := ∑ k ∈ Finset.range r, ∫ ω, |pairSigma C D (trA p C cs t D M k ω)| ∂P with hSdef
  have hEg0 : ∀ k, 0 ≤ ∫ ω, |pairSigma C D (trA p C cs t D M k ω)| ∂P := fun k =>
    integral_nonneg fun ω => abs_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => hEg0 k
  have hsB := Real.sqrt_nonneg (B : ℝ)
  have hterm : ∀ j ∈ Finset.range (r + 1), ∀ k ∈ Finset.range j,
      |∫ ω, f j k ω ∂P| ≤ K2 * (Real.sqrt B * emaW p.β (r - j) +
        Real.sqrt B * emaW p.β (r - j) ^ 2 * ∫ ω, |pairSigma C D (trA p C cs t D M k ω)| ∂P) := by
    intro j hj k hk
    exact (hT2 Ω P m n B C cs t j k r D M Pt hS hB hR hPf hPo (Finset.mem_range.mp hk)
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2
  have hinner : ∀ j ∈ Finset.range (r + 1),
      ∑ k ∈ Finset.range j, ∫ ω, |pairSigma C D (trA p C cs t D M k ω)| ∂P ≤ S := by
    intro j hj
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.lt_succ_iff.mp
      (Finset.mem_range.mp hj))) fun k _ _ => hEg0 k
  calc |∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, ∫ ω, f j k ω ∂P|
      ≤ ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, |∫ ω, f j k ω ∂P| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, K2 * (Real.sqrt B * emaW p.β (r - j) +
          Real.sqrt B * emaW p.β (r - j) ^ 2 * ∫ ω, |pairSigma C D (trA p C cs t D M k ω)| ∂P) :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => hterm j hj k hk
    _ = K2 * Real.sqrt B * (∑ j ∈ Finset.range (r + 1), ∑ _k ∈ Finset.range j, emaW p.β (r - j) +
          ∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) ^ 2 *
            ∑ k ∈ Finset.range j, ∫ ω, |pairSigma C D (trA p C cs t D M k ω)| ∂P) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ ≤ K2 * Real.sqrt B * ((r : ℝ) + ∑ j ∈ Finset.range (r + 1), emaW p.β (r - j) * S) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (tr_double_sum_emaW_le p.hβ r)
          (Finset.sum_le_sum fun j hj => ?_)) (by positivity)
        have hw := tr_emaW_mem p.hβ (r - j)
        have hw2 : emaW p.β (r - j) ^ 2 ≤ emaW p.β (r - j) := by nlinarith [hw.1, hw.2]
        have hI := hinner j hj
        have hI0 : 0 ≤ ∑ k ∈ Finset.range j, ∫ ω, |pairSigma C D (trA p C cs t D M k ω)| ∂P :=
          Finset.sum_nonneg fun k _ => hEg0 k
        exact mul_le_mul hw2 hI hI0 hw.1
    _ ≤ K2 * Real.sqrt B * ((r : ℝ) + S) := by
        refine mul_le_mul_of_nonneg_left (add_le_add_right ?_ _) (by positivity)
        rw [← Finset.sum_mul]
        calc (∑ j ∈ Finset.range (r + 1), emaW p.β (r - j)) * S ≤ 1 * S :=
              mul_le_mul_of_nonneg_right (tr_emaW_sum_le p.hβ r) hS0
          _ = S := one_mul S

private lemma tr_integral_add4 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (f1 f2 f3 f4 : Ω → ℝ)
    (h1 : Integrable f1 P) (h2 : Integrable f2 P) (h3 : Integrable f3 P) (h4 : Integrable f4 P) :
    Integrable (fun ω => f1 ω + f2 ω + f3 ω + f4 ω) P ∧
    ∫ ω, (f1 ω + f2 ω + f3 ω + f4 ω) ∂P = ∫ ω, f1 ω ∂P + ∫ ω, f2 ω ∂P + ∫ ω, f3 ω ∂P + ∫ ω, f4 ω ∂P := by
  have h12 : Integrable (fun ω => f1 ω + f2 ω) P := h1.add h2
  have h123 : Integrable (fun ω => f1 ω + f2 ω + f3 ω) P := h12.add h3
  refine ⟨h123.add h4, ?_⟩
  rw [integral_add h123 h4, integral_add h12 h3, integral_add h1 h2]

set_option maxHeartbeats 4000000 in
/-- The frozen form of `prop:app-dyn-transport`: deterministic `D`, `m`, `Π`. -/
private lemma tr_frozen (certQ : Muon.External.GaussianQuadFormLp) (p : DynParams) (cP rlo rhi : ℝ)
    (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (C : Covariances m n) (cs : ChainSamples P m n B) (t r : ℕ) (D M Pt : Mat m n),
      SizeFin C B p.γstar p.CSig → 0 < B → rlo ≤ riskSigma C D → riskSigma C D ≤ rhi →
      fro Pt ≤ cP → opNorm Pt ≤ cP →
      Integrable (fun ω => frobIP Pt (causalDot p C (fun s => physBatch C (cs.act s) ω) t D M r -
        causalDot p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) r)) P ∧
      (p.h / (B : ℝ)) * |∫ ω, frobIP Pt (causalDot p C (fun s => physBatch C (cs.act s) ω) t D M r -
        causalDot p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) r) ∂P| ≤
        K * ((r : ℝ) / Real.sqrt B + (1 / Real.sqrt B) *
          ∑ k ∈ Finset.range r, ∫ ω, |pairSigma C D (trA p C cs t D M k ω)| ∂P +
          (r : ℝ) * p.β ^ (r + 1) * (fro M + Real.sqrt B)) := by
  obtain ⟨K1, hK1, hT1⟩ := tr_T1 p cP rlo rhi hrlo hle
  obtain ⟨K2, hK2, hT2⟩ := tr_T2sum certQ p cP rlo hrlo
  obtain ⟨K3, hK3, hT3⟩ := tr_T3 p cP rlo rhi hrlo hle
  obtain ⟨K4, hK4, hT4⟩ := tr_T4 p cP rlo rhi hrlo hle
  have hh := p.hh
  refine ⟨p.h * (K1 + K2 + K3 + K4), by positivity, ?_⟩
  intro Ω _ P _ m n B C cs t r D M Pt hS hB hR hRhi hPf hPo
  have hRpos : 0 < riskSigma C D := lt_of_lt_of_le hrlo hR
  have hℓpos : 0 < physRidge p C D := by unfold physRidge; have := p.hϱ; positivity
  obtain ⟨i1, b1⟩ := hT1 Ω P m n B C cs t r D M Pt hS hB hR hRhi hPf
  obtain ⟨i2, b2⟩ := hT2 Ω P m n B C cs t r D M Pt hS hB hR hPf hPo
  obtain ⟨i3, b3⟩ := hT3 Ω P m n B C cs t r D M Pt hS hB hR hRhi hPf
  obtain ⟨i4, b4⟩ := hT4 Ω P m n B C cs t r D M Pt hS hB hR hRhi hPf
  have hpt : ∀ ω, frobIP Pt (causalDot p C (fun s => physBatch C (cs.act s) ω) t D M r -
        causalDot p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) r) =
      frobIP Pt (dirDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r) -
        dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r)) +
      frobIP Pt (dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
        (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r -
          tangentM p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) r)) +
      frobIP Pt ((-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k))) •
        (ridgeDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω) -
          ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω))) +
      frobIP Pt ((-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)) -
        -(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) k))) •
        ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)) := by
    intro ω
    rw [tr_causalDot_eq p C _ t D M hRpos r, tr_causalDot_eq p C _ t D _ hRpos r, tr_dirDeriv_sub hℓpos,
      ← tr_frobIP_add_right, ← tr_frobIP_add_right, ← tr_frobIP_add_right]
    congr 1
    simp only [trNh, trNs, smul_sub, sub_smul]
    abel
  have hfun : (fun ω => frobIP Pt (causalDot p C (fun s => physBatch C (cs.act s) ω) t D M r -
        causalDot p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) r)) =
      fun ω => _ := funext hpt
  rw [hfun]
  obtain ⟨hi4, he4⟩ := tr_integral_add4 _ _ _ _ i1 i2 i3 i4
  refine ⟨hi4, ?_⟩
  rw [he4]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hsB : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBr
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hsBB : Real.sqrt B / B ≤ 1 := by
    rw [div_le_one hBr]
    calc Real.sqrt B ≤ Real.sqrt B * Real.sqrt B := le_mul_of_one_le_right hsB.le (Real.one_le_sqrt.mpr hB1)
      _ = B := Real.mul_self_sqrt hBr.le
  have hsBB' : Real.sqrt B / B = 1 / Real.sqrt B := by
    rw [div_eq_div_iff hBr.ne' hsB.ne', one_mul, Real.mul_self_sqrt hBr.le]
  set S : ℝ := ∑ k ∈ Finset.range r, ∫ ω, |pairSigma C D (trA p C cs t D M k ω)| ∂P with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => integral_nonneg fun ω => abs_nonneg _
  set W : ℝ := (r : ℝ) * p.β ^ (r + 1) * (fro M + Real.sqrt B) with hW
  have hW0 : 0 ≤ W := by have := pow_nonneg p.hβ.1 (r + 1); have := tr_fro_nonneg M; positivity
  have a1 := (abs_integral_le_integral_abs (μ := P)).trans b1
  have a3 := (abs_integral_le_integral_abs (μ := P)).trans b3
  have a4 := (abs_integral_le_integral_abs (μ := P)).trans b4
  set I1 := ∫ ω, frobIP Pt (dirDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r) -
        dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
          (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r)) ∂P
  set I2 := ∫ ω, frobIP Pt (dirDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)
        (tangentM p C (fun s => physBatch C (cs.act s) ω) t D M r -
          tangentM p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) r)) ∂P
  set I3 := ∫ ω, frobIP Pt ((-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k))) •
        (ridgeDeriv (physRidge p C D) (trNh p C cs t D M (r + 1) ω) -
          ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω))) ∂P
  set I4 := ∫ ω, frobIP Pt ((-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D M k)) -
        -(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
          frozenV p C (fun s => physBatch C (cs.act s) ω) t D (chainInit p.β C D (cs.aux (t : ℤ)) ω) k))) •
        ridgeDeriv (physRidge p C D) (trNs p C cs t D (r + 1) ω)) ∂P
  have htri : |I1 + I2 + I3 + I4| ≤ |I1| + |I2| + |I3| + |I4| := by
    have := abs_add_le (I1 + I2 + I3) I4
    have := abs_add_le (I1 + I2) I3
    have := abs_add_le I1 I2
    linarith
  have hhB : 0 ≤ p.h / B := by positivity
  calc p.h / B * |I1 + I2 + I3 + I4| ≤ p.h / B * (|I1| + |I2| + |I3| + |I4|) :=
        mul_le_mul_of_nonneg_left htri hhB
    _ ≤ p.h / B * (K1 * B * W + K2 * Real.sqrt B * (r + S) + K3 * Real.sqrt B * W + K4 * Real.sqrt B * S) := by
        gcongr
    _ = p.h * (K1 * W + K2 * (Real.sqrt B / B) * (r + S) + K3 * (Real.sqrt B / B) * W +
          K4 * (Real.sqrt B / B) * S) := by
        field_simp
    _ ≤ p.h * (K1 * W + K2 * (1 / Real.sqrt B) * (r + S) + K3 * 1 * W + K4 * (1 / Real.sqrt B) * S) := by
        rw [hsBB']
        rw [hsBB'] at hsBB
        gcongr
    _ ≤ p.h * (K1 + K2 + K3 + K4) * ((r : ℝ) / Real.sqrt B + (1 / Real.sqrt B) * S + W) := by
        have e1 : (r : ℝ) / Real.sqrt B = (1 / Real.sqrt B) * r := by ring
        rw [e1]
        have h1 : 0 ≤ (1 / Real.sqrt B) * (r : ℝ) := by positivity
        have h2 : 0 ≤ (1 / Real.sqrt B) * S := by positivity
        nlinarith [mul_nonneg hK1 h1, mul_nonneg hK1 h2, mul_nonneg hK2 hW0, mul_nonneg hK3 h1,
          mul_nonneg hK3 h2, mul_nonneg hK4 h1, mul_nonneg hK4 hW0, mul_nonneg hh.le hK1]


/-! ### Pointwise bound of the batch gradient and its integrability -/

private lemma tr_fro_outer {a b : ℕ} (x : Vec a) (y : Vec b) :
    fro (outer x y) = Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ j, y j ^ 2) := by
  rw [← Real.sqrt_mul (by positivity), Finset.sum_mul]
  unfold fro outer
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.vecMulVec_apply, mul_pow]

private lemma tr_resid_le {m n : ℕ} (V : Mat m n) (x : Vec m × Vec n) :
    |resid V x| ≤ Real.sqrt (∑ i, x.1 i ^ 2) * fro V * Real.sqrt (∑ j, x.2 j ^ 2) := by
  unfold resid
  have h1 : |x.1 ⬝ᵥ (V *ᵥ x.2)| ≤ Real.sqrt (∑ i, x.1 i ^ 2) * Real.sqrt (∑ i, (V *ᵥ x.2) i ^ 2) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h2 : Real.sqrt (∑ i, (V *ᵥ x.2) i ^ 2) ≤ fro V * Real.sqrt (∑ j, x.2 j ^ 2) := by
    rw [← Real.sqrt_sq (tr_fro_nonneg V), ← Real.sqrt_mul (sq_nonneg _)]
    refine Real.sqrt_le_sqrt ((projection_sum_sq_mulVec_le V x.2).trans ?_)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (tr_opNorm_nonneg _) (tr_opNorm_le_fro V) 2)
      (by positivity)
  calc |x.1 ⬝ᵥ (V *ᵥ x.2)| ≤ Real.sqrt (∑ i, x.1 i ^ 2) * Real.sqrt (∑ i, (V *ᵥ x.2) i ^ 2) := h1
    _ ≤ Real.sqrt (∑ i, x.1 i ^ 2) * (fro V * Real.sqrt (∑ j, x.2 j ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = _ := by ring

private lemma tr_grad_fro_le {m n B : ℕ} (V : Mat m n) (b : Batch m n B) :
    fro (batchGrad V b) ≤ fro V * ((B : ℝ)⁻¹ * ∑ a, (∑ i, (b a).1 i ^ 2) * (∑ j, (b a).2 j ^ 2)) := by
  unfold batchGrad grad
  rw [tr_fro_smul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  have hB0 : (0 : ℝ) ≤ (B : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  refine (mul_le_mul_of_nonneg_left (tr_fro_sum_le _ _) hB0).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [tr_fro_smul, tr_fro_outer]
  have h := tr_resid_le V (b a)
  have hx := Real.sq_sqrt (show 0 ≤ ∑ i, (b a).1 i ^ 2 by positivity)
  have hy := Real.sq_sqrt (show 0 ≤ ∑ j, (b a).2 j ^ 2 by positivity)
  have hsx := Real.sqrt_nonneg (∑ i, (b a).1 i ^ 2)
  have hsy := Real.sqrt_nonneg (∑ j, (b a).2 j ^ 2)
  calc (B : ℝ)⁻¹ * (|resid V (b a)| * (Real.sqrt (∑ i, (b a).1 i ^ 2) * Real.sqrt (∑ j, (b a).2 j ^ 2)))
      ≤ (B : ℝ)⁻¹ * ((Real.sqrt (∑ i, (b a).1 i ^ 2) * fro V * Real.sqrt (∑ j, (b a).2 j ^ 2)) *
          (Real.sqrt (∑ i, (b a).1 i ^ 2) * Real.sqrt (∑ j, (b a).2 j ^ 2))) := by
        gcongr
    _ = fro V * ((B : ℝ)⁻¹ * ((Real.sqrt (∑ i, (b a).1 i ^ 2)) ^ 2 * (Real.sqrt (∑ j, (b a).2 j ^ 2)) ^ 2)) := by
        ring
    _ = _ := by rw [hx, hy]

private lemma tr_phys_sq_le {m n : ℕ} (C : Covariances m n) (CS : ℝ) (hC : opNorm C.Sout ≤ CS)
    (hCi : opNorm C.Sin ≤ CS) (z : Vec m × Vec n) :
    (∑ i, (phys C z).1 i ^ 2) ≤ CS * ∑ i, z.1 i ^ 2 ∧ (∑ j, (phys C z).2 j ^ 2) ≤ CS * ∑ j, z.2 j ^ 2 := by
  have ho := projection_sqrt_opNorm_sq C.Sout C.psdOut
  have hi := projection_sqrt_opNorm_sq C.Sin C.psdIn
  constructor
  · refine (projection_sum_sq_mulVec_le (rOut C) z.1).trans ?_
    exact mul_le_mul_of_nonneg_right (by unfold rOut; rw [ho]; exact hC) (by positivity)
  · refine (projection_sum_sq_mulVec_le (rIn C) z.2).trans ?_
    exact mul_le_mul_of_nonneg_right (by unfold rIn; rw [hi]; exact hCi) (by positivity)

/-- The batch-norm functional `H_s = B⁻¹ ∑_a ‖z_a‖² ‖w_a‖²` of the whitened samples of `cs.act s`. -/
private lemma tr_physGrad_le {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Covariances m n) (CS : ℝ) (hC0 : 0 ≤ CS) (hC : opNorm C.Sout ≤ CS) (hCi : opNorm C.Sin ≤ CS)
    (cs : ChainSamples P m n B) (s : ℤ) (V : Mat m n) (ω : Ω) :
    fro (batchGrad V (physBatch C (cs.act s) ω)) ≤ fro V * (CS ^ 2 * ((B : ℝ)⁻¹ *
      ∑ a, (∑ i, (cs.act s a ω).1 i ^ 2) * (∑ j, (cs.act s a ω).2 j ^ 2))) := by
  refine (tr_grad_fro_le V _).trans (mul_le_mul_of_nonneg_left ?_ (tr_fro_nonneg _))
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  obtain ⟨h1, h2⟩ := tr_phys_sq_le C CS hC hCi (cs.act s a ω)
  have hB0 : (0 : ℝ) ≤ (B : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  change (B : ℝ)⁻¹ * ((∑ i, (phys C (cs.act s a ω)).1 i ^ 2) * (∑ j, (phys C (cs.act s a ω)).2 j ^ 2)) ≤ _
  calc (B : ℝ)⁻¹ * ((∑ i, (phys C (cs.act s a ω)).1 i ^ 2) * (∑ j, (phys C (cs.act s a ω)).2 j ^ 2))
      ≤ (B : ℝ)⁻¹ * ((CS * ∑ i, (cs.act s a ω).1 i ^ 2) * (CS * ∑ j, (cs.act s a ω).2 j ^ 2)) := by
        gcongr
    _ = _ := by ring

private lemma tr_H_integrable {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (cs : ChainSamples P m n B) (s : ℤ) :
    Integrable (fun ω => (B : ℝ)⁻¹ * ∑ a, (∑ i, (cs.act s a ω).1 i ^ 2) * (∑ j, (cs.act s a ω).2 j ^ 2)) P := by
  refine (integrable_finsetSum _ fun a _ => ?_).const_mul _
  have hg : Integrable (fun z : Vec m × Vec n => (∑ i, z.1 i ^ 2) * (∑ j, z.2 j ^ 2))
      ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) := by
    have h1 := (memLp_one_iff_integrable.mp (projection_gaussian_sqnorm_memLp m 1 (by simp)))
    have h2 := (memLp_one_iff_integrable.mp (projection_gaussian_sqnorm_memLp n 1 (by simp)))
    exact h1.mul_prod h2
  have hmeas : AEStronglyMeasurable (fun z : Vec m × Vec n => (∑ i, z.1 i ^ 2) * (∑ j, z.2 j ^ 2))
      (P.map (cs.act s a)) := by
    exact (by fun_prop : Continuous (fun z : Vec m × Vec n => (∑ i, z.1 i ^ 2) * (∑ j, z.2 j ^ 2))).aestronglyMeasurable
  rw [← cs.law_act s a] at hg
  exact (integrable_map_measure hmeas (cs.meas_act s a).aemeasurable).mp hg

/-! ### Joint measurability of the filter derivatives -/

private lemma tr_Qmax_cont {m n : ℕ} {c : ℝ} (hc : 0 < c) (i : Fin m) (j : Fin n) :
    Continuous (fun p : ℝ × Mat m n => Q (max p.1 c) p.2 i j) := by
  have h1 : Continuous (fun p : ℝ × Mat m n => (max p.1 c, p.2)) :=
    (continuous_fst.max continuous_const).prodMk continuous_snd
  have h2 := (continuousOn_Q_pos (m := m) (n := n)).comp_continuous h1
    (fun p => ⟨lt_of_lt_of_le hc (le_max_right _ _), Set.mem_univ _⟩)
  exact (continuous_apply j).comp ((continuous_apply i).comp h2)

private lemma tr_dd_joint {m n : ℕ} {c : ℝ} (hc : 0 < c) :
    Measurable (fun q : ℝ × Mat m n × Mat m n => dirDeriv (max q.1 c) q.2.1 q.2.2) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  let f : (ℝ × Mat m n × Mat m n) → ℝ → ℝ := fun q τ => Q (max q.1 c) (q.2.1 + τ • q.2.2) i j
  have hf : Continuous (Function.uncurry f) := by
    have h1 : Continuous (fun z : (ℝ × Mat m n × Mat m n) × ℝ => (z.1.1, z.1.2.1 + z.2 • z.1.2.2)) := by
      fun_prop
    exact (tr_Qmax_cont hc i j).comp h1
  have hm := (measurable_deriv_with_param hf).comp (measurable_id.prodMk measurable_const :
    Measurable (fun q : ℝ × Mat m n × Mat m n => (q, (0 : ℝ))))
  exact hm

private lemma tr_rd_joint {m n : ℕ} {c : ℝ} (hc : 0 < c) :
    Measurable (fun q : ℝ × Mat m n => ridgeDeriv (max q.1 (2 * c)) q.2) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  let f : Mat m n → ℝ → ℝ := fun N x => Q (max x c) N i j
  have hf : Continuous (Function.uncurry f) := by
    have h1 : Continuous (fun z : Mat m n × ℝ => (z.2, z.1)) := by fun_prop
    exact (tr_Qmax_cont hc i j).comp h1
  have hm := (measurable_deriv_with_param hf).comp ((measurable_snd.prodMk
    (measurable_fst.max measurable_const)) :
    Measurable (fun q : ℝ × Mat m n => (q.2, max q.1 (2 * c))))
  have e : (fun q : ℝ × Mat m n => ridgeDeriv (max q.1 (2 * c)) q.2 i j) =
      (fun p : Mat m n × ℝ => deriv (f p.1) p.2) ∘ (fun q : ℝ × Mat m n => (q.2, max q.1 (2 * c))) := by
    funext q
    have hx : c < max q.1 (2 * c) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hev : f q.2 =ᶠ[𝓝 (max q.1 (2 * c))] fun x => Q x q.2 i j := by
      filter_upwards [lt_mem_nhds hx] with x hx'
      simp only [f, max_eq_left hx'.le]
    change ridgeDeriv (max q.1 (2 * c)) q.2 i j = deriv (f q.2) (max q.1 (2 * c))
    rw [hev.deriv_eq]
    rfl
  rw [e]
  exact hm

/-! ### Joint measurability of the chains as functions of the state and the future samples -/

private lemma tr_bg_joint {m n B : ℕ} {α : Type*} [MeasurableSpace α] (C : Covariances m n)
    {D : α → Mat m n} {z : α → Fin B → Vec m × Vec n} (hD : Measurable D) (hz : Measurable z) :
    Measurable (fun x => batchGrad (D x) (fun a => phys C (z x a))) := by
  have h := (tr_batchGrad_cont (B := B) C).measurable.comp (hD.prodMk hz)
  exact h

private lemma tr_y_ema_meas {m n B : ℕ} {α : Type*} [MeasurableSpace α] (β : ℝ) (C : Covariances m n)
    (t : ℕ) {D m0 : α → Mat m n} {y : α → ℤ → Fin B → Vec m × Vec n} (hD : Measurable D)
    (hm0 : Measurable m0) (hy : Measurable y) (k : ℕ) :
    Measurable (fun x => emaChain β (D x) (fun s a => phys C (y x s a)) t (m0 x) k) := by
  induction k with
  | zero => exact hm0
  | succ k ih =>
    have hyk : Measurable (fun x => y x ((t : ℤ) + k + 1)) := (measurable_pi_apply ((t : ℤ) + k + 1)).comp hy
    have hb := tr_bg_joint C hD hyk
    exact (ih.const_smul β).add (hb.const_smul (1 - β))

private lemma tr_y_Q_meas {m n : ℕ} {α : Type*} [MeasurableSpace α] (p : DynParams) (C : Covariances m n)
    {D f : α → Mat m n} (hD : Measurable D) (hf : Measurable f) :
    Measurable (fun x => Q (physRidge p C (D x)) (f x)) := by
  have hrisk : Continuous (fun D : Mat m n => riskSigma C D) := by
    unfold riskSigma pairSigma; fun_prop
  have hρm : Measurable (fun x => (⟨physRidge p C (D x), tr_ridge_nonneg p C (D x)⟩ : Set.Ici (0 : ℝ))) := by
    unfold physRidge
    exact (((hrisk.measurable.comp hD).const_mul 2).mul_const p.ϱ).subtype_mk
  have h := (measurable_Q (m := m) (n := n)).comp (hρm.prodMk hf)
  exact h

private lemma tr_y_N0_meas {m n B : ℕ} {α : Type*} [MeasurableSpace α] (β : ℝ) (C : Covariances m n)
    {D : α → Mat m n} {y : α → ℕ → Fin B → Vec m × Vec n} (hD : Measurable D) (hy : Measurable y) :
    Measurable (fun x => ∑' j : ℕ, emaW β j • batchGrad (D x) (fun a => phys C (y x j a))) := by
  have : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  have : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  have : MeasurableAdd₂ (Mat m n) :=
    inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hb : ∀ j, Measurable (fun x => emaW β j • batchGrad (D x) (fun a => phys C (y x j a))) :=
    fun j => by
      have hyj : Measurable (fun x => y x j) := (measurable_pi_apply j).comp hy
      have h := tr_bg_joint C hD hyj
      exact h.const_smul (emaW β j)
  exact Measurable.tsum hb

private lemma tr_y_frozenV_meas {m n B : ℕ} {α : Type*} [MeasurableSpace α] (p : DynParams)
    (C : Covariances m n) (t : ℕ) {D m0 : α → Mat m n} {y : α → ℤ → Fin B → Vec m × Vec n}
    (hD : Measurable D) (hm0 : Measurable m0) (hy : Measurable y) (k : ℕ) :
    Measurable (fun x => frozenV p C (fun s a => phys C (y x s a)) t (D x) (m0 x) k) :=
  tr_y_Q_meas p C hD (tr_y_ema_meas p.β C t hD hm0 hy (k + 1))

private lemma tr_y_tangentM_meas {m n B : ℕ} {α : Type*} [MeasurableSpace α] (p : DynParams)
    (C : Covariances m n) (t : ℕ) {D m0 : α → Mat m n} {y : α → ℤ → Fin B → Vec m × Vec n}
    (hD : Measurable D) (hm0 : Measurable m0) (hy : Measurable y) (r : ℕ) :
    Measurable (fun x => tangentM p C (fun s a => phys C (y x s a)) t (D x) (m0 x) r) := by
  unfold tangentM
  refine Measurable.neg (Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_)
  refine Measurable.const_smul ?_ (emaW p.β (r - j))
  have hyj : Measurable (fun x => y x ((t : ℤ) + j + 1)) := (measurable_pi_apply ((t : ℤ) + j + 1)).comp hy
  exact tr_bg_joint C (tr_y_frozenV_meas p C t hD hm0 hy k) hyj

private lemma tr_y_lam_meas {m n B : ℕ} {α : Type*} [MeasurableSpace α] (p : DynParams)
    (C : Covariances m n) (t : ℕ) {D m0 : α → Mat m n} {y : α → ℤ → Fin B → Vec m × Vec n}
    (hD : Measurable D) (hm0 : Measurable m0) (hy : Measurable y) (r : ℕ) :
    Measurable (fun x => -(2 * p.ϱ * pairSigma C (D x) (∑ k ∈ Finset.range r,
      frozenV p C (fun s a => phys C (y x s a)) t (D x) (m0 x) k))) := by
  have hs : Measurable (fun x => ∑ k ∈ Finset.range r, frozenV p C (fun s a => phys C (y x s a)) t (D x) (m0 x) k) :=
    Finset.measurable_sum _ fun k _ => tr_y_frozenV_meas p C t hD hm0 hy k
  have hc : Continuous (fun q : Mat m n × Mat m n => pairSigma C q.1 q.2) := by unfold pairSigma; fun_prop
  have h := hc.measurable.comp (hD.prodMk hs)
  exact (h.const_mul (2 * p.ϱ)).neg

/-- The causal tangent written with clamped ridge `max ϱ°(D) c`; it is `causalDot` when `ϱ°(D) ≥ c`. -/
private lemma tr_y_tan_meas {m n B : ℕ} {α : Type*} [MeasurableSpace α] (p : DynParams)
    (C : Covariances m n) (t : ℕ) {c : ℝ} (hc : 0 < c) {D m0 : α → Mat m n}
    {y : α → ℤ → Fin B → Vec m × Vec n} (hD : Measurable D) (hm0 : Measurable m0) (hy : Measurable y) (r : ℕ) :
    Measurable (fun x => dirDeriv (max (physRidge p C (D x)) c)
        (emaChain p.β (D x) (fun s a => phys C (y x s a)) t (m0 x) (r + 1))
        (tangentM p C (fun s a => phys C (y x s a)) t (D x) (m0 x) r)
      + (-(2 * p.ϱ * pairSigma C (D x) (∑ k ∈ Finset.range r,
          frozenV p C (fun s a => phys C (y x s a)) t (D x) (m0 x) k))) •
        ridgeDeriv (max (physRidge p C (D x)) c)
          (emaChain p.β (D x) (fun s a => phys C (y x s a)) t (m0 x) (r + 1))) := by
  have hρ : Measurable (fun x => physRidge p C (D x)) := by
    have hrisk : Continuous (fun D : Mat m n => riskSigma C D) := by
      unfold riskSigma pairSigma; fun_prop
    unfold physRidge
    exact ((hrisk.measurable.comp hD).const_mul 2).mul_const p.ϱ
  have hN := tr_y_ema_meas p.β C t hD hm0 hy (r + 1)
  have hM := tr_y_tangentM_meas p C t hD hm0 hy r
  have h1 : Measurable (fun x => dirDeriv (max (physRidge p C (D x)) c)
      (emaChain p.β (D x) (fun s a => phys C (y x s a)) t (m0 x) (r + 1))
      (tangentM p C (fun s a => phys C (y x s a)) t (D x) (m0 x) r)) := by
    have h := (tr_dd_joint (m := m) (n := n) hc).comp (hρ.prodMk (hN.prodMk hM))
    exact h
  have h2 : Measurable (fun x => ridgeDeriv (max (physRidge p C (D x)) c)
      (emaChain p.β (D x) (fun s a => phys C (y x s a)) t (m0 x) (r + 1))) := by
    have h := (tr_rd_joint (m := m) (n := n) (half_pos hc)).comp (hρ.prodMk hN)
    have e : (fun x => ridgeDeriv (max (physRidge p C (D x)) c)
        (emaChain p.β (D x) (fun s a => phys C (y x s a)) t (m0 x) (r + 1))) =
        (fun q : ℝ × Mat m n => ridgeDeriv (max q.1 (2 * (c / 2))) q.2) ∘
          (fun x => (physRidge p C (D x), emaChain p.β (D x) (fun s a => phys C (y x s a)) t (m0 x) (r + 1))) := by
      funext x; simp only [Function.comp, mul_div_cancel₀ c (two_ne_zero' ℝ)]
    rw [e]; exact h
  exact h1.add ((tr_y_lam_meas p C t hD hm0 hy r).smul h2)

/-! ### Congruence: the causal chain reads only the batches of the steps `≥ t` -/

private lemma tr_causalState_congr {m n B : ℕ} (p : DynParams) (C : Covariances m n)
    (G G' : ℤ → Batch m n B) (t : ℕ) (hG : ∀ i : ℕ, G ((t : ℤ) + i + 1) = G' ((t : ℤ) + i + 1))
    (D m0 : Mat m n) (ε : ℝ) (r : ℕ) :
    causalState p C G t D m0 ε r = causalState p C G' t D m0 ε r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [causalState, ih, hG r]

private lemma tr_causalDot_congr {m n B : ℕ} (p : DynParams) (C : Covariances m n)
    (G G' : ℤ → Batch m n B) (t : ℕ) (hG : ∀ i : ℕ, G ((t : ℤ) + i + 1) = G' ((t : ℤ) + i + 1))
    (D m0 : Mat m n) (r : ℕ) :
    causalDot p C G t D m0 r = causalDot p C G' t D m0 r := by
  unfold causalDot causalS
  simp only [tr_causalState_congr p C G G' t hG]

private lemma tr_emaChain_congr {m n B : ℕ} (β : ℝ) (D : Mat m n)
    (G G' : ℤ → Batch m n B) (t : ℕ) (hG : ∀ i : ℕ, G ((t : ℤ) + i + 1) = G' ((t : ℤ) + i + 1))
    (m0 : Mat m n) (k : ℕ) :
    emaChain β D G t m0 k = emaChain β D G' t m0 k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [emaChain, ih, hG k]

/-! ### The future samples after time `t` -/

private lemma tr_Y_meas {m n B : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (cs : ChainSamples P m n B) (t : ℕ) :
    Measurable[chainFuture cs t] (fun ω => ((fun (s : ℤ) (a : Fin B) =>
      if (t : ℤ) < s then cs.act s a ω else (0 : Vec m × Vec n)), fun (j : ℕ) (a : Fin B) => cs.aux (t : ℤ) j a ω)) := by
  refine Measurable.prodMk ?_ ?_
  · refine @Measurable.of_eval _ _ _ (chainFuture cs t) _ _ fun s => ?_
    refine @Measurable.of_eval _ _ _ (chainFuture cs t) _ _ fun a => ?_
    by_cases hs : (t : ℤ) < s
    · simp only [hs, ite_true]
      refine measurable_iff_comap_le.2 (le_sup_of_le_left ?_)
      exact le_iSup₂_of_le s hs (le_iSup_of_le a le_rfl)
    · simp only [hs, ite_false]
      exact measurable_const
  · refine @Measurable.of_eval _ _ _ (chainFuture cs t) _ _ fun j => ?_
    refine @Measurable.of_eval _ _ _ (chainFuture cs t) _ _ fun a => ?_
    refine measurable_iff_comap_le.2 (le_sup_of_le_right ?_)
    exact le_iSup_of_le j (le_iSup_of_le a le_rfl)

private lemma tr_Y_batch {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (ω : Ω) (i : ℕ) :
    (fun (s : ℤ) (a : Fin B) => phys C (if (t : ℤ) < s then cs.act s a ω else (0 : Vec m × Vec n)))
      ((t : ℤ) + i + 1) = (fun s => physBatch C (cs.act s) ω) ((t : ℤ) + i + 1) := by
  funext a
  have : (t : ℤ) < (t : ℤ) + i + 1 := by omega
  simp only [this, ite_true]
  rfl

/-! ### The freezing functionals -/

/-- The future samples after time `t`: actual batches of the steps `≥ t` and the auxiliary batches of `t`. -/
private def trY {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (cs : ChainSamples P m n B) (t : ℕ) (ω : Ω) :
    (ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n) :=
  ((fun (s : ℤ) (a : Fin B) => if (t : ℤ) < s then cs.act s a ω else (0 : Vec m × Vec n)),
    fun (j : ℕ) (a : Fin B) => cs.aux (t : ℤ) j a ω)

/-- The stationary initial buffer as a function of the state and the auxiliary samples. -/
private def trN0F {m n B : ℕ} (β : ℝ) (C : Covariances m n) (D : Mat m n)
    (y : ℕ → Fin B → Vec m × Vec n) : Mat m n :=
  ∑' j : ℕ, emaW β j • batchGrad D (fun a => phys C (y j a))

/-- The causal tangent with clamped ridge, as a function of the state, the buffer and the batches. -/
private def trTanF (p : DynParams) {m n B : ℕ} (C : Covariances m n) (t r : ℕ) (c : ℝ) (D m0 : Mat m n)
    (y : ℤ → Fin B → Vec m × Vec n) : Mat m n :=
  dirDeriv (max (physRidge p C D) c)
      (emaChain p.β D (fun s a => phys C (y s a)) t m0 (r + 1))
      (tangentM p C (fun s a => phys C (y s a)) t D m0 r)
    + (-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r,
        frozenV p C (fun s a => phys C (y s a)) t D m0 k))) •
      ridgeDeriv (max (physRidge p C D) c)
        (emaChain p.β D (fun s a => phys C (y s a)) t m0 (r + 1))

/-- The freezing functional of the tested tangent difference. -/
private def trPsi (p : DynParams) {m n B : ℕ} (C : Covariances m n) (t r : ℕ) (c : ℝ)
    (x : Mat m n × Mat m n × Mat m n)
    (y : (ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) : ℝ :=
  {x : Mat m n × Mat m n × Mat m n | x.1 ∈ admAplus p C}.indicator (fun x =>
    frobIP x.2.2 (trTanF p C t r c x.1 x.2.1 y.1 - trTanF p C t r c x.1 (trN0F p.β C x.1 y.2) y.1)) x

/-- The freezing functional of the startup projection `|⟨Σ_out D Σ_in, V̂_k − V_k⟩|`. -/
private def trPsik (p : DynParams) {m n B : ℕ} (C : Covariances m n) (t k : ℕ)
    (x : Mat m n × Mat m n × Mat m n)
    (y : (ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) : ℝ :=
  {x : Mat m n × Mat m n × Mat m n | x.1 ∈ admAplus p C}.indicator (fun x =>
    |pairSigma C x.1 (Q (physRidge p C x.1) (emaChain p.β x.1 (fun s a => phys C (y.1 s a)) t x.2.1 (k + 1)) -
      Q (physRidge p C x.1) (emaChain p.β x.1 (fun s a => phys C (y.1 s a)) t (trN0F p.β C x.1 y.2) (k + 1)))|) x

private lemma tr_Aplus_meas {m n : ℕ} (p : DynParams) (C : Covariances m n) :
    MeasurableSet (admAplus p C) := concentration_admSet_meas C _

private lemma tr_Psi_meas (p : DynParams) {m n B : ℕ} (C : Covariances m n) (t r : ℕ) {c : ℝ} (hc : 0 < c) :
    Measurable (Function.uncurry (trPsi (B := B) p C t r c)) := by
  have hD : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.1.1) := measurable_fst.comp measurable_fst
  have hm : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hP : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hy1 : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.2.1) := measurable_fst.comp measurable_snd
  have hy2 : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.2.2) := measurable_snd.comp measurable_snd
  have hN0 := tr_y_N0_meas p.β C hD hy2
  have h1 := tr_y_tan_meas p C t hc hD hm hy1 r
  have h2 := tr_y_tan_meas p C t hc hD hN0 hy1 r
  have hc' : Continuous (fun q : Mat m n × Mat m n => frobIP q.1 q.2) := by unfold frobIP; fun_prop
  have h3 := hc'.measurable.comp (hP.prodMk (h1.sub h2))
  have hset : MeasurableSet {z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) | z.1.1 ∈ admAplus p C} :=
    hD (tr_Aplus_meas p C)
  have e : Function.uncurry (trPsi (B := B) p C t r c) = {z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) | z.1.1 ∈ admAplus p C}.indicator
      (fun z => frobIP z.1.2.2 (trTanF p C t r c z.1.1 z.1.2.1 z.2.1 -
        trTanF p C t r c z.1.1 (trN0F p.β C z.1.1 z.2.2) z.2.1)) := by
    funext z
    by_cases hz : z.1.1 ∈ admAplus p C
    · simp [Function.uncurry, trPsi, Set.indicator, hz]
    · simp [Function.uncurry, trPsi, Set.indicator, hz]
  rw [e]
  exact h3.indicator hset

private lemma tr_Psik_meas (p : DynParams) {m n B : ℕ} (C : Covariances m n) (t k : ℕ) :
    Measurable (Function.uncurry (trPsik (B := B) p C t k)) := by
  have hD : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.1.1) := measurable_fst.comp measurable_fst
  have hm : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hy1 : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.2.1) := measurable_fst.comp measurable_snd
  have hy2 : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.2.2) := measurable_snd.comp measurable_snd
  have hN0 := tr_y_N0_meas p.β C hD hy2
  have h1 := tr_y_Q_meas p C hD (tr_y_ema_meas p.β C t hD hm hy1 (k + 1))
  have h2 := tr_y_Q_meas p C hD (tr_y_ema_meas p.β C t hD hN0 hy1 (k + 1))
  have hc' : Continuous (fun q : Mat m n × Mat m n => |pairSigma C q.1 q.2|) :=
    continuous_abs.comp (by unfold pairSigma; fun_prop)
  have h3 := hc'.measurable.comp (hD.prodMk (h1.sub h2))
  have hset : MeasurableSet {z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) | z.1.1 ∈ admAplus p C} :=
    hD (tr_Aplus_meas p C)
  have e : Function.uncurry (trPsik (B := B) p C t k) = {z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) | z.1.1 ∈ admAplus p C}.indicator
      (fun z => |pairSigma C z.1.1 (Q (physRidge p C z.1.1)
        (emaChain p.β z.1.1 (fun s a => phys C (z.2.1 s a)) t z.1.2.1 (k + 1)) -
        Q (physRidge p C z.1.1) (emaChain p.β z.1.1 (fun s a => phys C (z.2.1 s a)) t
          (trN0F p.β C z.1.1 z.2.2) (k + 1)))|) := by
    funext z
    by_cases hz : z.1.1 ∈ admAplus p C
    · simp [Function.uncurry, trPsik, Set.indicator, hz]
    · simp [Function.uncurry, trPsik, Set.indicator, hz]
  rw [e]
  exact h3.indicator hset

private lemma tr_Psi_eq (p : DynParams) {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Covariances m n) (cs : ChainSamples P m n B) (t r : ℕ) {c : ℝ}
    (x : Mat m n × Mat m n × Mat m n) (hx : x.1 ∈ admAplus p C) (hR : 0 < riskSigma C x.1)
    (hc : c ≤ physRidge p C x.1) (ω : Ω) :
    trPsi p C t r c x (trY cs t ω) = frobIP x.2.2
      (causalDot p C (fun s => physBatch C (cs.act s) ω) t x.1 x.2.1 r -
        causalDot p C (fun s => physBatch C (cs.act s) ω) t x.1 (chainInit p.β C x.1 (cs.aux (t : ℤ)) ω) r) := by
  have hG := tr_Y_batch C cs t ω
  have hT : ∀ m0 : Mat m n, trTanF p C t r c x.1 m0 (trY cs t ω).1 =
      causalDot p C (fun s => physBatch C (cs.act s) ω) t x.1 m0 r := by
    intro m0
    unfold trTanF
    rw [max_eq_left hc, ← tr_causalDot_eq p C _ t x.1 m0 hR r]
    exact tr_causalDot_congr p C _ _ t hG x.1 m0 r
  unfold trPsi
  rw [Set.indicator_of_mem (show x ∈ {x : Mat m n × Mat m n × Mat m n | x.1 ∈ admAplus p C} from hx)]
  rw [hT, hT]
  rfl

private lemma tr_Psi_zero (p : DynParams) {m n B : ℕ} (C : Covariances m n) (t r : ℕ) (c : ℝ)
    (x : Mat m n × Mat m n × Mat m n) (hx : x.1 ∉ admAplus p C)
    (y : (ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) : trPsi p C t r c x y = 0 := by
  unfold trPsi
  exact Set.indicator_of_notMem (show x ∉ {x : Mat m n × Mat m n × Mat m n | x.1 ∈ admAplus p C} from hx) _

private lemma tr_Psik_eq (p : DynParams) {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Covariances m n) (cs : ChainSamples P m n B) (t k : ℕ)
    (x : Mat m n × Mat m n × Mat m n) (hx : x.1 ∈ admAplus p C) (ω : Ω) :
    trPsik p C t k x (trY cs t ω) = |pairSigma C x.1 (trA p C cs t x.1 x.2.1 k ω)| := by
  have hG := tr_Y_batch C cs t ω
  unfold trPsik
  rw [Set.indicator_of_mem (show x ∈ {x : Mat m n × Mat m n × Mat m n | x.1 ∈ admAplus p C} from hx)]
  have hG' : ∀ i : ℕ, (fun s a => phys C ((trY cs t ω).1 s a)) ((t : ℤ) + i + 1) =
      (fun s => physBatch C (cs.act s) ω) ((t : ℤ) + i + 1) := fun i => hG i
  have e1 := tr_emaChain_congr p.β x.1 (fun s a => phys C ((trY cs t ω).1 s a))
    (fun s => physBatch C (cs.act s) ω) t hG' x.2.1 (k + 1)
  have e2 := tr_emaChain_congr p.β x.1 (fun s a => phys C ((trY cs t ω).1 s a))
    (fun s => physBatch C (cs.act s) ω) t hG' (trN0F p.β C x.1 (trY cs t ω).2) (k + 1)
  rw [e1, e2]
  rfl

private lemma tr_Psik_zero (p : DynParams) {m n B : ℕ} (C : Covariances m n) (t k : ℕ)
    (x : Mat m n × Mat m n × Mat m n) (hx : x.1 ∉ admAplus p C)
    (y : (ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) : trPsik p C t k x y = 0 := by
  unfold trPsik
  exact Set.indicator_of_notMem (show x ∉ {x : Mat m n × Mat m n × Mat m n | x.1 ∈ admAplus p C} from hx) _

/-- A crude pointwise bound of the causal tangent, uniform in the buffer. -/
private lemma tr_causalDot_bound (p : DynParams) (rlo rhi : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m n B : ℕ) (C : Covariances m n) (G : ℤ → Batch m n B) (t r : ℕ) (D m0 : Mat m n),
      SizeFin C B p.γstar p.CSig → rlo ≤ riskSigma C D → riskSigma C D ≤ rhi →
      fro (causalDot p C G t D m0 r) ≤ K * (∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
        emaW p.β (r - j) * fro (batchGrad (frozenV p C G t D m0 k) (G ((t : ℤ) + j + 1))) + r * B) := by
  have hℓlo : 0 < 2 * rlo * p.ϱ := by have := p.hϱ; positivity
  have hℓle : 2 * rlo * p.ϱ ≤ 2 * rhi * p.ϱ := by have := p.hϱ; nlinarith
  obtain ⟨C4, hC4⟩ := lem_app_dyn_second_iv hℓlo hℓle
  have hϱ := p.hϱ
  have hC0 : 0 ≤ p.CSig := le_trans zero_le_one p.hC
  set K1 : ℝ := (2 * rlo * p.ϱ) ^ (-(1 / 2 : ℝ)) with hK1
  set K2 : ℝ := 2 * p.ϱ * (Real.sqrt (2 * rhi) * (p.CSig * Real.sqrt p.γstar)) * (max C4 0 * Real.sqrt p.γstar)
    with hK2
  have hK10 : 0 ≤ K1 := Real.rpow_nonneg hℓlo.le _
  have hK20 : 0 ≤ K2 := by have := le_max_right C4 0; positivity
  refine ⟨K1 + K2, by positivity, ?_⟩
  intro m n B C G t r D m0 hS hR hRhi
  have hRpos : 0 < riskSigma C D := lt_of_lt_of_le hrlo hR
  have hℓ : physRidge p C D ∈ Icc (2 * rlo * p.ϱ) (2 * rhi * p.ϱ) := by
    unfold physRidge
    constructor <;> nlinarith
  rw [tr_causalDot_eq p C G t D m0 hRpos r]
  have hmin := (tr_min_le C _ _ hS).1
  have hsq : Real.sqrt ((min m n : ℕ) : ℝ) ≤ Real.sqrt p.γstar * Real.sqrt B := by
    rw [← Real.sqrt_mul' _ (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt hmin
  set Ssum := ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
        emaW p.β (r - j) * fro (batchGrad (frozenV p C G t D m0 k) (G ((t : ℤ) + j + 1))) with hSs
  have hSs0 : 0 ≤ Ssum := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
    mul_nonneg (tr_emaW_mem p.hβ _).1 (tr_fro_nonneg _)
  have h1 : fro (dirDeriv (physRidge p C D) (emaChain p.β D G t m0 (r + 1)) (tangentM p C G t D m0 r)) ≤
      K1 * Ssum := by
    refine (lem_app_dyn_second_i hℓlo hℓle _ hℓ _ _).trans ?_
    refine mul_le_mul (Real.rpow_le_rpow_of_nonpos hℓlo hℓ.1 (by norm_num))
      (tr_fro_tangentM_le p C G t D m0 r) (tr_fro_nonneg _) hK10
  have h2 : fro ((-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r, frozenV p C G t D m0 k))) •
      ridgeDeriv (physRidge p C D) (emaChain p.β D G t m0 (r + 1))) ≤ K2 * (r * B) := by
    rw [tr_fro_smul, abs_neg]
    have hl := tr_lam_bound p C hS G t D m0 r rhi hRhi
    have hrd := (hC4 _ hℓ (emaChain p.β D G t m0 (r + 1)) (emaChain p.β D G t m0 (r + 1))).2.1
    have hrd' : fro (ridgeDeriv (physRidge p C D) (emaChain p.β D G t m0 (r + 1))) ≤
        max C4 0 * (Real.sqrt p.γstar * Real.sqrt B) := by
      have := tr_fro_nonneg (ridgeDeriv2 (physRidge p C D) (emaChain p.β D G t m0 (r + 1)))
      calc _ ≤ C4 * Real.sqrt ((min m n : ℕ) : ℝ) := by linarith
        _ ≤ _ := mul_le_mul (le_max_left _ _) hsq (Real.sqrt_nonneg _) (le_max_right _ _)
    have hB := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) B)
    calc _ ≤ (2 * p.ϱ * r * (Real.sqrt (2 * rhi) * (p.CSig * (Real.sqrt p.γstar * Real.sqrt B)))) *
          (max C4 0 * (Real.sqrt p.γstar * Real.sqrt B)) :=
          mul_le_mul hl hrd' (tr_fro_nonneg _) (by positivity)
      _ = K2 * (r * (Real.sqrt B * Real.sqrt B)) := by rw [hK2]; ring
      _ = K2 * (r * B) := by rw [hB]
  calc _ ≤ K1 * Ssum + K2 * (r * B) := (tr_fro_add_le _ _).trans (add_le_add h1 h2)
    _ ≤ (K1 + K2) * (Ssum + r * B) := by
        have : 0 ≤ (r : ℝ) * B := by positivity
        nlinarith

private lemma tr_chainFuture_le {m n B : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} (cs : ChainSamples P m n B) (t : ℕ) : chainFuture cs t ≤ mΩ := by
  refine sup_le (iSup_le fun s => iSup_le fun _ => iSup_le fun a => ?_)
    (iSup_le fun j => iSup_le fun a => ?_)
  · exact (cs.meas_act s a).comap_le
  · exact (cs.meas_aux (t : ℤ) j a).comap_le

private lemma tr_frobIP_sub_le {m n : ℕ} (T X Y : Mat m n) :
    |frobIP T (X - Y)| ≤ fro T * (fro X + fro Y) :=
  (projection_frobIP_le _ _).trans (mul_le_mul_of_nonneg_left (tr_fro_sub_le _ _) (tr_fro_nonneg _))

/-- Integrability of the freezing functional along the process. -/
private lemma tr_Psi_integrable (p : DynParams) (cPi rlo rhi : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {m n B : ℕ} (C : Covariances m n) (cs : ChainSamples P m n B) (t r : ℕ) (c : ℝ) (X : Ω → Mat m n × Mat m n × Mat m n),
      SizeFin C B p.γstar p.CSig → admAplus p C ⊆ {D | rlo ≤ riskSigma C D ∧ riskSigma C D ≤ rhi} →
      c ≤ 2 * rlo * p.ϱ → Measurable X → (∀ ω, fro (X ω).2.2 ≤ cPi) →
      Measurable (Function.uncurry (trPsi (B := B) p C t r c)) →
      Integrable (fun ω => trPsi p C t r c (X ω) (trY cs t ω)) P := by
  obtain ⟨Kb, hKb0, hKb⟩ := tr_causalDot_bound p rlo rhi hrlo hle
  refine ⟨Kb, hKb0, ?_⟩
  intro Ω _ P _ m n B C cs t r c X hS hA hc hX hPi hΨm
  have hC0 : 0 ≤ p.CSig := le_trans zero_le_one p.hC
  set cPi' : ℝ := max cPi 0 with hcPi'
  set H : ℕ → Ω → ℝ := fun j ω => (B : ℝ)⁻¹ * ∑ a, (∑ i, (cs.act ((t : ℤ) + j + 1) a ω).1 i ^ 2) *
    (∑ l, (cs.act ((t : ℤ) + j + 1) a ω).2 l ^ 2) with hH
  have hH0 : ∀ j ω, 0 ≤ H j ω := fun j ω => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun a _ => by positivity)
  set bnd : Ω → ℝ := fun ω => cPi' * (2 * (Kb * (∑ j ∈ Finset.range (r + 1), ∑ _k ∈ Finset.range j,
      emaW p.β (r - j) * ((Real.sqrt p.γstar * Real.sqrt B) * (p.CSig ^ 2 * H j ω)) + r * B))) with hbnd
  have hbint : Integrable bnd P := by
    refine (((integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => ?_).add
      (integrable_const _)).const_mul _ |>.const_mul _).const_mul _
    exact (((tr_H_integrable cs ((t : ℤ) + j + 1)).const_mul _).const_mul _).const_mul _
  have hmeas : AEStronglyMeasurable (fun ω => trPsi p C t r c (X ω) (trY cs t ω)) P := by
    have hY := (tr_Y_meas cs t).mono (tr_chainFuture_le cs t) le_rfl
    exact (hΨm.comp (hX.prodMk hY)).aestronglyMeasurable
  refine hbint.mono' hmeas (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  by_cases hx : (X ω).1 ∈ admAplus p C
  · obtain ⟨hR1, hR2⟩ := hA hx
    have hRpos : 0 < riskSigma C (X ω).1 := lt_of_lt_of_le hrlo hR1
    have hcℓ : c ≤ physRidge p C (X ω).1 := by
      unfold physRidge; have := p.hϱ; nlinarith
    rw [tr_Psi_eq p C cs t r (X ω) hx hRpos hcℓ ω]
    have hG : ∀ (m0 : Mat m n), fro (causalDot p C (fun s => physBatch C (cs.act s) ω) t (X ω).1 m0 r) ≤
        Kb * (∑ j ∈ Finset.range (r + 1), ∑ _k ∈ Finset.range j,
          emaW p.β (r - j) * ((Real.sqrt p.γstar * Real.sqrt B) * (p.CSig ^ 2 * H j ω)) + r * B) := by
      intro m0
      refine (hKb m n B C _ t r (X ω).1 m0 hS hR1 hR2).trans (mul_le_mul_of_nonneg_left
        (add_le_add_left (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_) _) hKb0)
      refine mul_le_mul_of_nonneg_left ?_ (tr_emaW_mem p.hβ _).1
      refine (tr_physGrad_le C p.CSig hC0 hS.2.1 hS.2.2 cs _ _ ω).trans ?_
      exact mul_le_mul_of_nonneg_right (tr_frozenV_fro p C hS _ t (X ω).1 m0 k)
        (mul_nonneg (sq_nonneg _) (hH0 j ω))
    refine (tr_frobIP_sub_le _ _ _).trans ?_
    have h2 := add_le_add (hG (X ω).2.1) (hG (chainInit p.β C (X ω).1 (cs.aux (t : ℤ)) ω))
    refine (mul_le_mul ((hPi ω).trans (le_max_left _ _)) h2 (add_nonneg (tr_fro_nonneg _) (tr_fro_nonneg _))
      (le_max_right _ _)).trans
      (le_of_eq ?_)
    rw [hbnd]; ring
  · rw [tr_Psi_zero p C t r c (X ω) hx, abs_zero]
    have : 0 ≤ ∑ j ∈ Finset.range (r + 1), ∑ _k ∈ Finset.range j,
        emaW p.β (r - j) * ((Real.sqrt p.γstar * Real.sqrt B) * (p.CSig ^ 2 * H j ω)) :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
        mul_nonneg (tr_emaW_mem p.hβ _).1 (mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (hH0 j ω)))
    have := le_max_right cPi 0
    show 0 ≤ bnd ω
    rw [hbnd]; positivity

private lemma tr_Psik_integrable (p : DynParams) (rhi : ℝ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (C : Covariances m n) (cs : ChainSamples P m n B) (t k : ℕ)
    (X : Ω → Mat m n × Mat m n × Mat m n) (hS : SizeFin C B p.γstar p.CSig)
    (hA : admAplus p C ⊆ {D | riskSigma C D ≤ rhi}) (hX : Measurable X) :
    Integrable (fun ω => trPsik p C t k (X ω) (trY cs t ω)) P := by
  have hY := (tr_Y_meas cs t).mono (tr_chainFuture_le cs t) le_rfl
  refine Integrable.of_bound ((tr_Psik_meas (B := B) p C t k).comp (hX.prodMk hY)).aestronglyMeasurable
    (Real.sqrt (2 * rhi) * (p.CSig * (2 * Real.sqrt p.γstar * Real.sqrt B))) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  by_cases hx : (X ω).1 ∈ admAplus p C
  · rw [tr_Psik_eq p C cs t k (X ω) hx ω, abs_abs]
    refine (tr_pairSigma_bound p C hS _ _).trans ?_
    exact mul_le_mul (Real.sqrt_le_sqrt (by have := hA hx; simp only [Set.mem_ofPred_eq] at this; linarith))
      (mul_le_mul_of_nonneg_left (tr_trA_bounds p C cs t _ _ k hS ω).2 (le_trans zero_le_one p.hC))
      (mul_nonneg (le_trans zero_le_one p.hC) (tr_fro_nonneg _)) (Real.sqrt_nonneg _)
  · rw [tr_Psik_zero p C t k (X ω) hx, abs_zero]
    have := le_trans zero_le_one p.hC
    positivity

private lemma tr_integral_lin {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (r : ℕ) (K c1 c2 c3 c4 : ℝ) (a : ℕ → Ω → ℝ) (b : Ω → ℝ) (ha : ∀ k, Integrable (a k) P)
    (hb : Integrable b P) :
    Integrable (fun ω => K * (c1 + c2 * ∑ k ∈ Finset.range r, a k ω + c3 * (b ω + c4))) P ∧
    ∫ ω, K * (c1 + c2 * ∑ k ∈ Finset.range r, a k ω + c3 * (b ω + c4)) ∂P =
      K * (c1 + c2 * ∑ k ∈ Finset.range r, ∫ ω, a k ω ∂P + c3 * (∫ ω, b ω ∂P + c4)) := by
  have hs : Integrable (fun ω => ∑ k ∈ Finset.range r, a k ω) P := integrable_finsetSum _ fun k _ => ha k
  have h1 : Integrable (fun ω => c2 * ∑ k ∈ Finset.range r, a k ω) P := hs.const_mul _
  have h2 : Integrable (fun ω => b ω + c4) P := hb.add (integrable_const _)
  have h3 : Integrable (fun ω => c3 * (b ω + c4)) P := h2.const_mul _
  have h4 : Integrable (fun ω => c1 + c2 * ∑ k ∈ Finset.range r, a k ω) P := (integrable_const _).add h1
  refine ⟨(h4.add h3).const_mul _, ?_⟩
  rw [integral_const_mul, integral_add h4 h3, integral_add (integrable_const _) h1, integral_const_mul,
    integral_const_mul, integral_add hb (integrable_const _), integral_finsetSum _ fun k _ => ha k]
  simp only [integral_const, probReal_univ, one_smul]

set_option maxHeartbeats 8000000 in
private theorem tr_transport_main (certQ : Muon.External.GaussianQuadFormLp) (certOp : Muon.External.GaussianOpNormL6) (certP : Muon.External.GaussianPoincare) (p : DynParams) (cPi : ℝ) :
    ∃ B0 : ℕ, ∃ K : ℝ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (m n B : ℕ) (S : DynSetup p P m n B) (t : ℕ) (Pt : Ω → Mat m n),
        B0 ≤ B → prefixLen p.β B ≤ t →
        (∀ ω, fro (Pt ω) ≤ cPi ∧ opNorm (Pt ω) ≤ cPi) →
        (∀ i j, Measurable[dynPast S t] (fun ω => Pt ω i j)) →
        ∀ r : ℕ, r < blockLen B →
          Integrable ({ω | (t : ℕ∞) < tauPlus p S ω}.indicator
            (fun ω => frobIP (Pt ω) (dynTangent p S t r ω - dynStatTangent p S t r ω))) P ∧
          Integrable ({ω | (t : ℕ∞) < tauPlus p S ω}.indicator
            (fun ω => |condExp (dynPast S t) P ({ω' | (t : ℕ∞) < tauPlus p S ω'}.indicator (fun ω' => frobIP (Pt ω') (dynTangent p S t r ω' - dynStatTangent p S t r ω'))) ω|)) P ∧
          (p.h / (B : ℝ)) * ∫ ω, {ω | (t : ℕ∞) < tauPlus p S ω}.indicator
            (fun ω => |condExp (dynPast S t) P ({ω' | (t : ℕ∞) < tauPlus p S ω'}.indicator (fun ω' => frobIP (Pt ω') (dynTangent p S t r ω' - dynStatTangent p S t r ω'))) ω|) ω ∂P
            ≤ K * ((r : ℝ) / Real.sqrt (B : ℝ) + omegaBeta p.β ((prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ))
              + p.β ^ prefixLen p.β B + Real.sqrt (B : ℝ) * (r : ℝ) * p.β ^ (r + 1)) := by
  set rlo : ℝ := (enl (admBase p)).1 with hrlodef
  set rhi : ℝ := (enl (admBase p)).2.1 with hrhidef
  have hrlo : 0 < rlo := by simp only [hrlodef, enl, admBase]; linarith [p.hr0]
  have hle : rlo ≤ rhi := by simp only [hrlodef, hrhidef, enl, admBase]; linarith [p.hr0, p.hr]
  set c : ℝ := 2 * rlo * p.ϱ with hcdef
  have hc : 0 < c := by have := p.hϱ; positivity
  obtain ⟨Kf, hKf0, hfz⟩ := tr_frozen certQ p cPi rlo rhi hrlo hle
  obtain ⟨Kp, -, hPsiI⟩ := tr_Psi_integrable p cPi rlo rhi hrlo hle
  obtain ⟨Be, Ke, henv⟩ := eqn_app_dyn_envelope certP certOp p
  obtain ⟨Cbuf, hCbuf0, hbuf⟩ := prefix_buffer_bound p
  set Ke' : ℝ := max Ke 0 with hKe'
  refine ⟨max Be 1, Kf * (2 + Ke' + Real.sqrt Cbuf), ?_⟩
  intro Ω _ P _ m n B S t Pt hB ht hPt hPtm r hr
  have hB0 : 0 < B := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hB)
  have hBe : Be ≤ B := (le_max_left _ _).trans hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB0
  have hsB : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBr
  -- the event `t < τ⁺` and the state
  set I : Set Ω := {ω | (t : ℕ∞) < tauPlus p S ω} with hIdef
  have hI : MeasurableSet[dynPast S t] I := concentration_tauPlus_meas S t
  have hIm : MeasurableSet I := concentration_past_le S t _ hI
  have hIA : ∀ ω ∈ I, dynDelta S t ω ∈ admAplus p S.C := fun ω hω =>
    (concentration_tauPlus_iff S t ω).1 hω t le_rfl
  have hA : admAplus p S.C ⊆ {D | rlo ≤ riskSigma S.C D ∧ riskSigma S.C D ≤ rhi} :=
    fun D hD => ⟨hD.1, hD.2.1⟩
  have hPtF : Measurable[dynPast S t] Pt :=
    @Measurable.of_eval Ω (Fin m) (fun _ => Fin n → ℝ) (dynPast S t) _ Pt fun i =>
      @Measurable.of_eval Ω (Fin n) (fun _ => ℝ) (dynPast S t) _ (fun ω => Pt ω i) fun j => hPtm i j
  set X : Ω → Mat m n × Mat m n × Mat m n := fun ω => (dynDelta S t ω, dynBuf S t ω, Pt ω) with hXdef
  have hXF : Measurable[dynPast S t] X :=
    (concentration_delta_meas S t).prodMk ((concentration_state_meas S t).2.prodMk hPtF)
  have hX : Measurable X := hXF.mono (concentration_past_le S t) le_rfl
  set Y := trY S.cs t with hYdef
  have hYF : Measurable[chainFuture S.cs t] Y := tr_Y_meas S.cs t
  have hY : Measurable Y := hYF.mono (tr_chainFuture_le S.cs t) le_rfl
  have hind : Indep (dynPast S t) (MeasurableSpace.comap Y inferInstance) P :=
    indep_of_indep_of_le_right (prefix_indep_past_future S t) (measurable_iff_comap_le.1 hYF)
  -- the freezing functional along the process
  have hΨm := tr_Psi_meas (B := B) p S.C t r hc
  set g : Ω → ℝ := fun ω => trPsi p S.C t r c (X ω) (Y ω) with hgdef
  have hgint : Integrable g P := hPsiI S.C S.cs t r c X S.size hA le_rfl hX (fun ω => (hPt ω).1) hΨm
  have hfg : I.indicator (fun ω => frobIP (Pt ω) (dynTangent p S t r ω - dynStatTangent p S t r ω)) =
      I.indicator g := by
    funext ω
    by_cases hω : ω ∈ I
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      have hx := hIA ω hω
      have hRpos : 0 < riskSigma S.C (dynDelta S t ω) := lt_of_lt_of_le hrlo hx.1
      have hcℓ : c ≤ physRidge p S.C (dynDelta S t ω) := by
        unfold physRidge; have := p.hϱ; nlinarith [hx.1]
      rw [hgdef]
      simp only
      rw [tr_Psi_eq p S.C S.cs t r (X ω) hx hRpos hcℓ ω]
      rfl
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
  refine ⟨by rw [hfg]; exact hgint.indicator hIm, integrable_condExp.abs.indicator hIm, ?_⟩
  -- freezing
  have hle𝓕 := concentration_past_le S t
  have hce : condExp (dynPast S t) P (I.indicator
      (fun ω => frobIP (Pt ω) (dynTangent p S t r ω - dynStatTangent p S t r ω))) =ᵐ[P]
      I.indicator (condExp (dynPast S t) P g) := by
    rw [hfg]; exact condExp_indicator hgint hI
  have hfr : condExp (dynPast S t) P g =ᵐ[P] fun ω => ∫ y, trPsi p S.C t r c (X ω) y ∂(P.map Y) :=
    Muon.Foundations.freezing_condExp (dynPast S t) hle𝓕 hXF hY hind hΨm hgint
  set gk : ℕ → Ω → ℝ := fun k ω => trPsik p S.C t k (X ω) (Y ω) with hgkdef
  have hgkint : ∀ k, Integrable (gk k) P := fun k =>
    tr_Psik_integrable p rhi S.C S.cs t k X S.size (fun D hD => hD.2.1) hX
  have hfrk : ∀ k, condExp (dynPast S t) P (gk k) =ᵐ[P]
      fun ω => ∫ y, trPsik p S.C t k (X ω) y ∂(P.map Y) := fun k =>
    Muon.Foundations.freezing_condExp (dynPast S t) hle𝓕 hXF hY hind (tr_Psik_meas (B := B) p S.C t k) (hgkint k)
  set Φk : ℕ → Ω → ℝ := fun k ω => ∫ y, trPsik p S.C t k (X ω) y ∂(P.map Y) with hΦkdef
  have hΦk0 : ∀ k ω, 0 ≤ Φk k ω := fun k ω => integral_nonneg fun y => by
    unfold trPsik; exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
  -- the pointwise frozen bound on `I`
  have hpt : ∀ ω ∈ I, (p.h / (B : ℝ)) * |∫ y, trPsi p S.C t r c (X ω) y ∂(P.map Y)| ≤
      Kf * ((r : ℝ) / Real.sqrt B + (1 / Real.sqrt B) * ∑ k ∈ Finset.range r, Φk k ω +
        (r : ℝ) * p.β ^ (r + 1) * (fro (dynBuf S t ω) + Real.sqrt B)) := by
    intro ω hω
    have hx := hIA ω hω
    have hRpos : 0 < riskSigma S.C (dynDelta S t ω) := lt_of_lt_of_le hrlo hx.1
    have hcℓ : c ≤ physRidge p S.C (dynDelta S t ω) := by
      unfold physRidge; have := p.hϱ; nlinarith [hx.1]
    have hΨx : Measurable (trPsi (B := B) p S.C t r c (X ω)) := hΨm.of_uncurry_left
    rw [integral_map hY.aemeasurable hΨx.aestronglyMeasurable]
    have e1 : (fun ω' => trPsi p S.C t r c (X ω) (Y ω')) = fun ω' => frobIP (Pt ω)
        (causalDot p S.C (fun s => physBatch S.C (S.cs.act s) ω') t (dynDelta S t ω) (dynBuf S t ω) r -
          causalDot p S.C (fun s => physBatch S.C (S.cs.act s) ω') t (dynDelta S t ω)
            (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω') r) := by
      funext ω'
      exact tr_Psi_eq p S.C S.cs t r (X ω) hx hRpos hcℓ ω'
    have e2 : ∀ k, Φk k ω = ∫ ω', |pairSigma S.C (dynDelta S t ω)
        (trA p S.C S.cs t (dynDelta S t ω) (dynBuf S t ω) k ω')| ∂P := by
      intro k
      rw [hΦkdef]
      simp only
      rw [integral_map hY.aemeasurable (tr_Psik_meas (B := B) p S.C t k).of_uncurry_left.aestronglyMeasurable]
      exact integral_congr_ae (Eventually.of_forall fun ω' => tr_Psik_eq p S.C S.cs t k (X ω) hx ω')
    rw [e1]
    simp_rw [e2]
    exact (hfz Ω P m n B S.C S.cs t r (dynDelta S t ω) (dynBuf S t ω) (Pt ω) S.size hB0 hx.1 hx.2.1
      (hPt ω).1 (hPt ω).2).2
  -- integrability of the pieces
  have hΦkint : ∀ k, Integrable (I.indicator (Φk k)) P := fun k =>
    ((integrable_condExp (m := dynPast S t) (μ := P) (f := gk k)).congr (hfrk k)).indicator hIm
  have hbm : Measurable (fun ω => fro (dynBuf S t ω)) :=
    tr_fro_cont.measurable.comp ((concentration_state_meas S t).2.mono hle𝓕 le_rfl)
  obtain ⟨hbuf2i, hbuf2⟩ := hbuf Ω P m n B S t I hIm (fun ω hω => le_of_lt hω)
  have hsq : (fun ω => (I.indicator (fun ω => fro (dynBuf S t ω)) ω) ^ 2) =
      I.indicator (fun ω => fro (dynBuf S t ω) ^ 2) := by
    funext ω; by_cases hω : ω ∈ I <;> simp [Set.indicator, hω]
  have hCB : 0 ≤ Cbuf * B := by positivity
  obtain ⟨hbi, hbb⟩ := tr_cs (fun _ => (1 : ℝ)) (I.indicator (fun ω => fro (dynBuf S t ω)))
    aestronglyMeasurable_const (hbm.indicator hIm).aestronglyMeasurable (fun _ => zero_le_one)
    (fun ω => Set.indicator_nonneg (fun _ _ => tr_fro_nonneg _) _) (integrable_const _)
    (by rw [hsq]; exact hbuf2i) 1 (Real.sqrt (Cbuf * B)) zero_le_one (Real.sqrt_nonneg _) (by simp)
    (by rw [hsq, Real.sq_sqrt hCB]; exact hbuf2)
  simp only [one_mul] at hbi hbb
  -- the main inequality
  have hβ0 : 0 ≤ p.β ^ (r + 1) := pow_nonneg p.hβ.1 _
  obtain ⟨hFi, hFe⟩ := tr_integral_lin r Kf ((r : ℝ) / Real.sqrt B) (1 / Real.sqrt B)
    ((r : ℝ) * p.β ^ (r + 1)) (Real.sqrt B) (fun k => I.indicator (Φk k))
    (I.indicator (fun ω => fro (dynBuf S t ω))) hΦkint hbi
  have hae : ∀ᵐ ω ∂P, (p.h / (B : ℝ)) * I.indicator (fun ω => |condExp (dynPast S t) P (I.indicator
      (fun ω' => frobIP (Pt ω') (dynTangent p S t r ω' - dynStatTangent p S t r ω'))) ω|) ω ≤
      Kf * ((r : ℝ) / Real.sqrt B + (1 / Real.sqrt B) * ∑ k ∈ Finset.range r, I.indicator (Φk k) ω +
        (r : ℝ) * p.β ^ (r + 1) * (I.indicator (fun ω => fro (dynBuf S t ω)) ω + Real.sqrt B)) := by
    filter_upwards [hce, hfr] with ω h1 h2
    by_cases hω : ω ∈ I
    · rw [Set.indicator_of_mem hω, h1, Set.indicator_of_mem hω, h2, Set.indicator_of_mem hω]
      simp only [Set.indicator_of_mem hω]
      exact hpt ω hω
    · rw [Set.indicator_of_notMem hω, mul_zero]
      simp only [Set.indicator_of_notMem hω, Finset.sum_const_zero, mul_zero, zero_add]
      have := hsB.le
      positivity
  have hLHSi : Integrable (fun ω => (p.h / (B : ℝ)) * I.indicator (fun ω => |condExp (dynPast S t) P (I.indicator
      (fun ω' => frobIP (Pt ω') (dynTangent p S t r ω' - dynStatTangent p S t r ω'))) ω|) ω) P :=
    (integrable_condExp.abs.indicator hIm).const_mul _
  have hmain := integral_mono_ae hLHSi hFi hae
  rw [integral_const_mul, hFe] at hmain
  -- the startup projections and the envelope
  have hΦI : ∀ k, ∫ ω, I.indicator (Φk k) ω ∂P = ∫ ω, I.indicator
      (fun ω => |frobIP (S.C.Sout * dynDelta S t ω * S.C.Sin) (dynErrV p S t k ω)|) ω ∂P := by
    intro k
    have e1 : ∫ ω, I.indicator (Φk k) ω ∂P = ∫ ω, I.indicator (condExp (dynPast S t) P (gk k)) ω ∂P :=
      integral_congr_ae ((hfrk k).mono fun ω hω => by
        by_cases hωI : ω ∈ I
        · simp only [Set.indicator_of_mem hωI]; exact hω.symm
        · simp only [Set.indicator_of_notMem hωI])
    rw [e1, integral_indicator hIm, setIntegral_condExp hle𝓕 (hgkint k) hI, ← integral_indicator hIm]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hωI : ω ∈ I
    · simp only [Set.indicator_of_mem hωI]
      rw [hgkdef]
      simp only
      rw [tr_Psik_eq p S.C S.cs t k (X ω) (hIA ω hωI) ω]
      rfl
    · simp only [Set.indicator_of_notMem hωI]
  obtain ⟨-, henv'⟩ := henv Ω P m n B S hBe t ht
  have hsum_le : (1 / Real.sqrt B) * ∑ k ∈ Finset.range r, ∫ ω, I.indicator (Φk k) ω ∂P ≤
      Ke' * (omegaBeta p.β ((prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ)) + p.β ^ prefixLen p.β B) := by
    simp_rw [hΦI]
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr hr.le) fun k _ _ => integral_nonneg fun ω =>
        Set.indicator_nonneg (fun _ _ => abs_nonneg _) _) (by positivity)) ?_
    refine henv'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    refine add_nonneg (tsum_nonneg fun k => le_min (by positivity) (pow_nonneg p.hβ.1 _)) (pow_nonneg p.hβ.1 _)
  set Om : ℝ := omegaBeta p.β ((prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ)) with hOm
  have hOm0 : 0 ≤ Om := tsum_nonneg fun k => le_min (by positivity) (pow_nonneg p.hβ.1 _)
  have hq0 : 0 ≤ p.β ^ prefixLen p.β B := pow_nonneg p.hβ.1 _
  have hKe0 : 0 ≤ Ke' := le_max_right _ _
  have hCb : Real.sqrt (Cbuf * B) = Real.sqrt Cbuf * Real.sqrt B := Real.sqrt_mul hCbuf0 _
  rw [hCb] at hbb
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hX1 : 0 ≤ (r : ℝ) / Real.sqrt B := by positivity
  have hX4 : 0 ≤ Real.sqrt B * r * p.β ^ (r + 1) := by positivity
  have hsC := Real.sqrt_nonneg Cbuf
  refine hmain.trans ?_
  calc Kf * ((r : ℝ) / Real.sqrt B + (1 / Real.sqrt B) * ∑ k ∈ Finset.range r, ∫ ω, I.indicator (Φk k) ω ∂P +
        (r : ℝ) * p.β ^ (r + 1) * (∫ ω, I.indicator (fun ω => fro (dynBuf S t ω)) ω ∂P + Real.sqrt B))
      ≤ Kf * ((r : ℝ) / Real.sqrt B + Ke' * (Om + p.β ^ prefixLen p.β B) +
        (r : ℝ) * p.β ^ (r + 1) * (Real.sqrt Cbuf * Real.sqrt B + Real.sqrt B)) := by
        gcongr
    _ = Kf * ((r : ℝ) / Real.sqrt B + Ke' * (Om + p.β ^ prefixLen p.β B) +
        (Real.sqrt Cbuf + 1) * (Real.sqrt B * r * p.β ^ (r + 1))) := by ring
    _ ≤ Kf * (2 + Ke' + Real.sqrt Cbuf) * ((r : ℝ) / Real.sqrt B + Om + p.β ^ prefixLen p.β B +
        Real.sqrt B * r * p.β ^ (r + 1)) := by
        rw [mul_assoc Kf (2 + Ke' + Real.sqrt Cbuf)]
        refine mul_le_mul_of_nonneg_left ?_ hKf0
        nlinarith [mul_nonneg hKe0 hX1, mul_nonneg hKe0 hX4, mul_nonneg hsC hX1, mul_nonneg hsC hOm0,
          mul_nonneg hsC hq0, mul_nonneg hKe0 hOm0, mul_nonneg hKe0 hq0]

/-! ## `prop:app-dyn-transport` -/

/-- `prop:app-dyn-transport` (cr-2026-10-23). Let `t ≥ 𝗊`, the chains at time `t` be those with `D = Δ_t` and
`m = M°_{t-1}`, and let `Π_t` be determined by `𝓕_t` with `‖Π_t‖_F, ‖Π_t‖ ≤ c_Π`. Then for `0 ≤ r < L`,
`l 𝔼[𝟙_{t<τ⁺} |𝔼_t⟨Π_t, V̇̂_r − V̇_r⟩|] ≤ C{r/√B + Ω_β(ε_B) + β^𝗊 + √B r β^{r+1}}`, with `l = η = h/B`. The
tangents are `dynTangent` (same-buffer chain) and `dynStatTangent` (stationary chain). The constant `K` depends on
`c_Π` and the fixed parameters. Integrability of the tested tangent and of the indicator-weighted conditional
expectation are conjuncts. Statement verbatim from `section.tex` (ll. 1907–1916):
```latex
\begin{proposition}[Tangent transport]\label{prop:app-dyn-transport}
Let $t\ge\mathsf q$, let the chains at time $t$ be those of
\cref{def:app-dyn-chains} with $D=\Dt$ and $m=M^\circ_{t-1}$, and let $\Pi_t$
be a matrix determined by the past $\cF_t$ with $\norm{\Pi_t}_\F,\norm{\Pi_t}\le c_\Pi$.
Then for $0\le r<L$,
\[
\lr\,\EE\Big[\mathbf 1_{t<\tau^+}\big|\EE_t\langle\Pi_t,\dot{\widehat V}_r-\dot V_r\rangle\big|\Big]
\le C\Big\{\frac{r}{\sqrt B}+\Omega_\bmom(\epsilon_B)+\bmom^{\mathsf q}+\sqrt B\,r\bmom^{r+1}\Big\}.
\]
\end{proposition}
```
-/
theorem prop_app_dyn_transport (certQ : Muon.External.GaussianQuadFormLp) (certOp : Muon.External.GaussianOpNormL6) (certP : Muon.External.GaussianPoincare) (p : DynParams) (cPi : ℝ) :
    ∃ B0 : ℕ, ∃ K : ℝ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (m n B : ℕ) (S : DynSetup p P m n B) (t : ℕ) (Pt : Ω → Mat m n),
        B0 ≤ B → prefixLen p.β B ≤ t →
        (∀ ω, fro (Pt ω) ≤ cPi ∧ opNorm (Pt ω) ≤ cPi) →
        (∀ i j, Measurable[dynPast S t] (fun ω => Pt ω i j)) →
        ∀ r : ℕ, r < blockLen B →
          Integrable ({ω | (t : ℕ∞) < tauPlus p S ω}.indicator
            (fun ω => frobIP (Pt ω) (dynTangent p S t r ω - dynStatTangent p S t r ω))) P ∧
          Integrable ({ω | (t : ℕ∞) < tauPlus p S ω}.indicator
            (fun ω => |condExp (dynPast S t) P ({ω' | (t : ℕ∞) < tauPlus p S ω'}.indicator (fun ω' => frobIP (Pt ω') (dynTangent p S t r ω' - dynStatTangent p S t r ω'))) ω|)) P ∧
          (p.h / (B : ℝ)) * ∫ ω, {ω | (t : ℕ∞) < tauPlus p S ω}.indicator
            (fun ω => |condExp (dynPast S t) P ({ω' | (t : ℕ∞) < tauPlus p S ω'}.indicator (fun ω' => frobIP (Pt ω') (dynTangent p S t r ω' - dynStatTangent p S t r ω'))) ω|) ω ∂P
            ≤ K * ((r : ℝ) / Real.sqrt (B : ℝ) + omegaBeta p.β ((prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ))
              + p.β ^ prefixLen p.β B + Real.sqrt (B : ℝ) * (r : ℝ) * p.β ^ (r + 1)) := by
  exact tr_transport_main certQ certOp certP p cPi

/-! ### Helpers of `prop:app-dyn-response` -/

/-- Pull a bounded `𝓕`-measurable test matrix out of the entrywise conditional expectation. -/
private lemma rs_pullout {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (𝓕 : MeasurableSpace Ω) (h𝓕 : 𝓕 ≤ mΩ) {m n : ℕ} (Pt X : Ω → Mat m n) (c : ℝ)
    (hPtm : ∀ i j, Measurable[𝓕] (fun ω => Pt ω i j)) (hPtb : ∀ ω i j, |Pt ω i j| ≤ c)
    (hX : ∀ i j, Integrable (fun ω => X ω i j) P) :
    ∀ᵐ ω ∂P, frobIP (Pt ω) (Muon.Foundations.condExpMat 𝓕 P X ω) =
      condExp 𝓕 P (fun ω => frobIP (Pt ω) (X ω)) ω := by
  have hprod : ∀ i j, Integrable (fun ω => Pt ω i j * X ω i j) P := fun i j =>
    (hX i j).bdd_mul ((hPtm i j).mono h𝓕 le_rfl).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hPtb ω i j)
  have hrow : ∀ i, Integrable (fun ω => ∑ j, Pt ω i j * X ω i j) P := fun i =>
    integrable_finsetSum _ fun j _ => hprod i j
  have hmul : ∀ i j, condExp 𝓕 P (fun ω => Pt ω i j * X ω i j) =ᵐ[P]
      fun ω => Pt ω i j * condExp 𝓕 P (fun ω => X ω i j) ω := fun i j =>
    condExp_mul_of_stronglyMeasurable_left (f := fun ω => Pt ω i j) (g := fun ω => X ω i j)
      (hPtm i j).stronglyMeasurable (hprod i j) (hX i j)
  have hin : ∀ i, condExp 𝓕 P (fun ω => ∑ j, Pt ω i j * X ω i j) =ᵐ[P]
      fun ω => ∑ j, condExp 𝓕 P (fun ω => Pt ω i j * X ω i j) ω := by
    intro i
    have e : (fun ω => ∑ j, Pt ω i j * X ω i j) = ∑ j, (fun ω => Pt ω i j * X ω i j) := by
      funext ω; simp only [Finset.sum_apply]
    rw [e]
    filter_upwards [condExp_finsetSum (s := Finset.univ) (fun j _ => hprod i j) 𝓕] with ω h
    rw [h, Finset.sum_apply]
  have hout : condExp 𝓕 P (fun ω => frobIP (Pt ω) (X ω)) =ᵐ[P]
      fun ω => ∑ i, condExp 𝓕 P (fun ω => ∑ j, Pt ω i j * X ω i j) ω := by
    have e : (fun ω => frobIP (Pt ω) (X ω)) = ∑ i, (fun ω => ∑ j, Pt ω i j * X ω i j) := by
      funext ω; simp only [Finset.sum_apply, prefix_frobIP_eq_sum]
    rw [e]
    filter_upwards [condExp_finsetSum (s := Finset.univ) (fun i _ => hrow i) 𝓕] with ω h
    rw [h, Finset.sum_apply]
  have hall1 : ∀ᵐ ω ∂P, ∀ i, condExp 𝓕 P (fun ω => ∑ j, Pt ω i j * X ω i j) ω =
      ∑ j, condExp 𝓕 P (fun ω => Pt ω i j * X ω i j) ω := ae_all_iff.2 hin
  have hall2 : ∀ᵐ ω ∂P, ∀ i j, condExp 𝓕 P (fun ω => Pt ω i j * X ω i j) ω =
      Pt ω i j * condExp 𝓕 P (fun ω => X ω i j) ω :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => hmul i j
  filter_upwards [hout, hall1, hall2] with ω h0 h1 h2
  rw [h0, prefix_frobIP_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h1 i]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h2 i j, Muon.Foundations.condExpMat_apply]

/-- Linear identity of conditional expectations on an `𝓕`-measurable event. -/
private lemma rs_lin_identity {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (𝓕 : MeasurableSpace Ω) (G : Set Ω) (hG : MeasurableSet[𝓕] G) (lam : ℝ)
    (fS f1 f2 f3 f4 f5 v : Ω → ℝ)
    (hsum : ∀ ω, fS ω = f1 ω + f2 ω + lam * f3 ω + lam * f4 ω + f5 ω)
    (hS : Integrable fS P) (h1 : Integrable (G.indicator f1) P) (h2 : Integrable (G.indicator f2) P)
    (h3 : Integrable (G.indicator f3) P) (h4 : Integrable (G.indicator f4) P)
    (h5 : Integrable (G.indicator f5) P)
    (hv : ∀ᵐ ω ∂P, ω ∈ G → condExp 𝓕 P (G.indicator f5) ω = v ω) :
    ∀ᵐ ω ∂P, ω ∈ G → condExp 𝓕 P fS ω - v ω = condExp 𝓕 P (G.indicator f1) ω +
      condExp 𝓕 P (G.indicator f2) ω + lam * condExp 𝓕 P (G.indicator f3) ω +
      lam * condExp 𝓕 P (G.indicator f4) ω := by
  have e : G.indicator fS = G.indicator f1 + G.indicator f2 + lam • G.indicator f3 +
      lam • G.indicator f4 + G.indicator f5 := by
    funext ω
    by_cases hω : ω ∈ G
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Set.indicator_of_mem hω, hsum ω]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Set.indicator_of_notMem hω, mul_zero, add_zero]
  have i3 := h3.smul lam
  have i4 := h4.smul lam
  have ce1 := condExp_add (((h1.add h2).add i3).add i4) h5 𝓕
  have ce2 := condExp_add ((h1.add h2).add i3) i4 𝓕
  have ce3 := condExp_add (h1.add h2) i3 𝓕
  have ce4 := condExp_add h1 h2 𝓕
  have cs3 := condExp_smul (μ := P) lam (G.indicator f3) 𝓕
  have cs4 := condExp_smul (μ := P) lam (G.indicator f4) 𝓕
  have hind := condExp_indicator hS hG
  rw [e] at hind
  filter_upwards [hind, ce1, ce2, ce3, ce4, cs3, cs4, hv] with ω k0 k1 k2 k3 k4 k5 k6 k7 hω
  rw [Set.indicator_of_mem hω] at k0
  rw [← k0, k1, Pi.add_apply, k2, Pi.add_apply, k3, Pi.add_apply, k4, Pi.add_apply, k5, k6, k7 hω]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma rs_integral_sum2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}
    (a : Fin m → Fin n → ℝ) (v : Ω → Fin m → Fin n → ℝ) (hv : ∀ i j, Integrable (fun ω => v ω i j) P) :
    ∫ ω, ∑ i, ∑ j, a i j * v ω i j ∂P = ∑ i, ∑ j, a i j * ∫ ω, v ω i j ∂P := by
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hv i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hv i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]

/-- Integral of a pairing with a fixed matrix. -/
private lemma rs_integral_frobIP {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}
    (T : Mat m n) (V : Ω → Mat m n) (hV : ∀ i j, Integrable (fun ω => V ω i j) P) :
    ∫ ω, frobIP T (V ω) ∂P = frobIP T (Muon.mean P V) := by
  simp only [prefix_frobIP_eq_sum, Muon.mean, Matrix.of_apply]
  exact rs_integral_sum2 (fun i j => T i j) (fun ω i j => V ω i j) hV

/-- The freezing functional of the tested stationary tangent. -/
private def trPsiS (p : DynParams) {m n B : ℕ} (C : Covariances m n) (t r : ℕ) (c : ℝ)
    (x : Mat m n × Mat m n × Mat m n)
    (y : (ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) : ℝ :=
  {x : Mat m n × Mat m n × Mat m n | x.1 ∈ admAplus p C}.indicator (fun x =>
    frobIP x.2.2 (trTanF p C t r c x.1 (trN0F p.β C x.1 y.2) y.1)) x

/-- The freezing functional of the tested stationary update `⟨Π, V_r⟩`. -/
private def trPsiV (p : DynParams) {m n B : ℕ} (C : Covariances m n) (t r : ℕ)
    (x : Mat m n × Mat m n × Mat m n)
    (y : (ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) : ℝ :=
  {x : Mat m n × Mat m n × Mat m n | x.1 ∈ admAplus p C}.indicator (fun x =>
    frobIP x.2.2 (Q (physRidge p C x.1)
      (emaChain p.β x.1 (fun s a => phys C (y.1 s a)) t (trN0F p.β C x.1 y.2) (r + 1)))) x

private lemma rs_PsiS_meas (p : DynParams) {m n B : ℕ} (C : Covariances m n) (t r : ℕ) {c : ℝ} (hc : 0 < c) :
    Measurable (Function.uncurry (trPsiS (B := B) p C t r c)) := by
  have hD : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.1.1) := measurable_fst.comp measurable_fst
  have hP : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hy1 : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.2.1) := measurable_fst.comp measurable_snd
  have hy2 : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.2.2) := measurable_snd.comp measurable_snd
  have hN0 := tr_y_N0_meas p.β C hD hy2
  have h2 := tr_y_tan_meas p C t hc hD hN0 hy1 r
  have hc' : Continuous (fun q : Mat m n × Mat m n => frobIP q.1 q.2) := by unfold frobIP; fun_prop
  have h3 := hc'.measurable.comp (hP.prodMk h2)
  have hset : MeasurableSet {z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) | z.1.1 ∈ admAplus p C} :=
    hD (tr_Aplus_meas p C)
  have e : Function.uncurry (trPsiS (B := B) p C t r c) = {z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) | z.1.1 ∈ admAplus p C}.indicator
      (fun z => frobIP z.1.2.2 (trTanF p C t r c z.1.1 (trN0F p.β C z.1.1 z.2.2) z.2.1)) := by
    funext z
    by_cases hz : z.1.1 ∈ admAplus p C
    · simp [Function.uncurry, trPsiS, Set.indicator, hz]
    · simp [Function.uncurry, trPsiS, Set.indicator, hz]
  rw [e]
  exact h3.indicator hset

private lemma rs_PsiV_meas (p : DynParams) {m n B : ℕ} (C : Covariances m n) (t r : ℕ) :
    Measurable (Function.uncurry (trPsiV (B := B) p C t r)) := by
  have hD : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.1.1) := measurable_fst.comp measurable_fst
  have hP : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hy1 : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.2.1) := measurable_fst.comp measurable_snd
  have hy2 : Measurable (fun z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) => z.2.2) := measurable_snd.comp measurable_snd
  have hN0 := tr_y_N0_meas p.β C hD hy2
  have h2 := tr_y_Q_meas p C hD (tr_y_ema_meas p.β C t hD hN0 hy1 (r + 1))
  have hc' : Continuous (fun q : Mat m n × Mat m n => frobIP q.1 q.2) := by unfold frobIP; fun_prop
  have h3 := hc'.measurable.comp (hP.prodMk h2)
  have hset : MeasurableSet {z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) | z.1.1 ∈ admAplus p C} :=
    hD (tr_Aplus_meas p C)
  have e : Function.uncurry (trPsiV (B := B) p C t r) = {z : (Mat m n × Mat m n × Mat m n) ×
      ((ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) | z.1.1 ∈ admAplus p C}.indicator
      (fun z => frobIP z.1.2.2 (Q (physRidge p C z.1.1)
        (emaChain p.β z.1.1 (fun s a => phys C (z.2.1 s a)) t (trN0F p.β C z.1.1 z.2.2) (r + 1)))) := by
    funext z
    by_cases hz : z.1.1 ∈ admAplus p C
    · simp [Function.uncurry, trPsiV, Set.indicator, hz]
    · simp [Function.uncurry, trPsiV, Set.indicator, hz]
  rw [e]
  exact h3.indicator hset

private lemma rs_PsiS_eq (p : DynParams) {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Covariances m n) (cs : ChainSamples P m n B) (t r : ℕ) {c : ℝ}
    (x : Mat m n × Mat m n × Mat m n) (hx : x.1 ∈ admAplus p C) (hR : 0 < riskSigma C x.1)
    (hc : c ≤ physRidge p C x.1) (ω : Ω) :
    trPsiS p C t r c x (trY cs t ω) = frobIP x.2.2
      (causalDot p C (fun s => physBatch C (cs.act s) ω) t x.1 (chainInit p.β C x.1 (cs.aux (t : ℤ)) ω) r) := by
  have hG := tr_Y_batch C cs t ω
  have hT : ∀ m0 : Mat m n, trTanF p C t r c x.1 m0 (trY cs t ω).1 =
      causalDot p C (fun s => physBatch C (cs.act s) ω) t x.1 m0 r := by
    intro m0
    unfold trTanF
    rw [max_eq_left hc, ← tr_causalDot_eq p C _ t x.1 m0 hR r]
    exact tr_causalDot_congr p C _ _ t hG x.1 m0 r
  unfold trPsiS
  rw [Set.indicator_of_mem (show x ∈ {x : Mat m n × Mat m n × Mat m n | x.1 ∈ admAplus p C} from hx)]
  rw [hT]
  rfl

private lemma rs_PsiS_zero (p : DynParams) {m n B : ℕ} (C : Covariances m n) (t r : ℕ) (c : ℝ)
    (x : Mat m n × Mat m n × Mat m n) (hx : x.1 ∉ admAplus p C)
    (y : (ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) : trPsiS p C t r c x y = 0 := by
  unfold trPsiS
  exact Set.indicator_of_notMem (show x ∉ {x : Mat m n × Mat m n × Mat m n | x.1 ∈ admAplus p C} from hx) _

private lemma rs_PsiV_eq (p : DynParams) {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Covariances m n) (cs : ChainSamples P m n B) (t r : ℕ)
    (x : Mat m n × Mat m n × Mat m n) (hx : x.1 ∈ admAplus p C) (ω : Ω) :
    trPsiV p C t r x (trY cs t ω) = frobIP x.2.2 (stationaryV p C cs t x.1 r ω) := by
  have hG := tr_Y_batch C cs t ω
  unfold trPsiV
  rw [Set.indicator_of_mem (show x ∈ {x : Mat m n × Mat m n × Mat m n | x.1 ∈ admAplus p C} from hx)]
  have hG' : ∀ i : ℕ, (fun s a => phys C ((trY cs t ω).1 s a)) ((t : ℤ) + i + 1) =
      (fun s => physBatch C (cs.act s) ω) ((t : ℤ) + i + 1) := fun i => hG i
  have e2 := tr_emaChain_congr p.β x.1 (fun s a => phys C ((trY cs t ω).1 s a))
    (fun s => physBatch C (cs.act s) ω) t hG' (trN0F p.β C x.1 (trY cs t ω).2) (r + 1)
  rw [e2]
  rfl

private lemma rs_PsiV_bound (p : DynParams) {m n B : ℕ} (C : Covariances m n) (t r : ℕ)
    (x : Mat m n × Mat m n × Mat m n)
    (y : (ℤ → Fin B → Vec m × Vec n) × (ℕ → Fin B → Vec m × Vec n)) :
    |trPsiV p C t r x y| ≤ fro x.2.2 * Real.sqrt ((min m n : ℕ) : ℝ) := by
  unfold trPsiV
  by_cases hx : x.1 ∈ admAplus p C
  · rw [Set.indicator_of_mem (show x ∈ {x : Mat m n × Mat m n × Mat m n | x.1 ∈ admAplus p C} from hx)]
    refine (projection_frobIP_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (tr_Q_bounds _ (tr_ridge_nonneg p C x.1) _).2 (tr_fro_nonneg _)
  · rw [Set.indicator_of_notMem (show x ∉ {x : Mat m n × Mat m n × Mat m n | x.1 ∈ admAplus p C} from hx),
      abs_zero]
    exact mul_nonneg (tr_fro_nonneg _) (Real.sqrt_nonneg _)

/-- Integrability of the stationary-tangent freezing functional along the process. -/
private lemma rs_PsiS_integrable (p : DynParams) (cPi rlo rhi : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n B : ℕ} (C : Covariances m n) (cs : ChainSamples P m n B) (t r : ℕ) (c : ℝ)
    (X : Ω → Mat m n × Mat m n × Mat m n)
    (hS : SizeFin C B p.γstar p.CSig) (hA : admAplus p C ⊆ {D | rlo ≤ riskSigma C D ∧ riskSigma C D ≤ rhi})
    (hc : c ≤ 2 * rlo * p.ϱ) (hX : Measurable X) (hPi : ∀ ω, fro (X ω).2.2 ≤ cPi)
    (hΨm : Measurable (Function.uncurry (trPsiS (B := B) p C t r c))) :
    Integrable (fun ω => trPsiS p C t r c (X ω) (trY cs t ω)) P := by
  obtain ⟨Kb, hKb0, hKb⟩ := tr_causalDot_bound p rlo rhi hrlo hle
  have hC0 : 0 ≤ p.CSig := le_trans zero_le_one p.hC
  set cPi' : ℝ := max cPi 0 with hcPi'
  set H : ℕ → Ω → ℝ := fun j ω => (B : ℝ)⁻¹ * ∑ a, (∑ i, (cs.act ((t : ℤ) + j + 1) a ω).1 i ^ 2) *
    (∑ l, (cs.act ((t : ℤ) + j + 1) a ω).2 l ^ 2) with hH
  have hH0 : ∀ j ω, 0 ≤ H j ω := fun j ω => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun a _ => by positivity)
  set bnd : Ω → ℝ := fun ω => cPi' * (Kb * (∑ j ∈ Finset.range (r + 1), ∑ _k ∈ Finset.range j,
      emaW p.β (r - j) * ((Real.sqrt p.γstar * Real.sqrt B) * (p.CSig ^ 2 * H j ω)) + r * B)) with hbnd
  have hbint : Integrable bnd P := by
    refine (((integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => ?_).add
      (integrable_const _)).const_mul _).const_mul _
    exact (((tr_H_integrable cs ((t : ℤ) + j + 1)).const_mul _).const_mul _).const_mul _
  have hmeas : AEStronglyMeasurable (fun ω => trPsiS p C t r c (X ω) (trY cs t ω)) P := by
    have hY := (tr_Y_meas cs t).mono (tr_chainFuture_le cs t) le_rfl
    exact (hΨm.comp (hX.prodMk hY)).aestronglyMeasurable
  refine hbint.mono' hmeas (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  have hS0 : 0 ≤ ∑ j ∈ Finset.range (r + 1), ∑ _k ∈ Finset.range j,
      emaW p.β (r - j) * ((Real.sqrt p.γstar * Real.sqrt B) * (p.CSig ^ 2 * H j ω)) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (tr_emaW_mem p.hβ _).1 (mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (hH0 j ω)))
  by_cases hx : (X ω).1 ∈ admAplus p C
  · obtain ⟨hR1, hR2⟩ := hA hx
    have hRpos : 0 < riskSigma C (X ω).1 := lt_of_lt_of_le hrlo hR1
    have hcℓ : c ≤ physRidge p C (X ω).1 := by
      unfold physRidge; have := p.hϱ; nlinarith
    rw [rs_PsiS_eq p C cs t r (X ω) hx hRpos hcℓ ω]
    have hG : fro (causalDot p C (fun s => physBatch C (cs.act s) ω) t (X ω).1
        (chainInit p.β C (X ω).1 (cs.aux (t : ℤ)) ω) r) ≤
        Kb * (∑ j ∈ Finset.range (r + 1), ∑ _k ∈ Finset.range j,
          emaW p.β (r - j) * ((Real.sqrt p.γstar * Real.sqrt B) * (p.CSig ^ 2 * H j ω)) + r * B) := by
      refine (hKb m n B C _ t r (X ω).1 _ hS hR1 hR2).trans (mul_le_mul_of_nonneg_left
        (add_le_add_left (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_) _) hKb0)
      refine mul_le_mul_of_nonneg_left ?_ (tr_emaW_mem p.hβ _).1
      refine (tr_physGrad_le C p.CSig hC0 hS.2.1 hS.2.2 cs _ _ ω).trans ?_
      exact mul_le_mul_of_nonneg_right (tr_frozenV_fro p C hS _ t (X ω).1 _ k)
        (mul_nonneg (sq_nonneg _) (hH0 j ω))
    refine (projection_frobIP_le _ _).trans ?_
    exact mul_le_mul ((hPi ω).trans (le_max_left _ _)) hG (tr_fro_nonneg _) (le_max_right _ _)
  · rw [rs_PsiS_zero p C t r c (X ω) hx, abs_zero]
    have := le_max_right cPi 0
    show 0 ≤ bnd ω
    rw [hbnd]; positivity

/-- `𝔼 V_r = V̄(D)`: the stationary chain has a time-invariant mean. -/
private lemma rs_mean_shift (p : DynParams) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (t r : ℕ) (D : Mat m n)
    (hD : 0 < riskSigma S.C D) :
    Muon.mean P (fun ω => stationaryV p S.C S.cs t D r ω) = dynVbar p S t D := by
  have hBpos : 0 < B := projection_batch_pos_of_risk_pos p S.C S.size D hD
  let F : Muon.Setup.FrozenParams m n B :=
    ⟨S.C, Ahat S.C D, prefix_Ahat_norm S.C D hD, p.β, p.hβ, hBpos⟩
  let P0 : Measure ((ℤ × Fin B) → Vec m × Vec n) :=
    Measure.infinitePi fun _ : ℤ × Fin B =>
      (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)
  have : IsProbabilityMeasure P0 := by
    dsimp only [P0]
    infer_instance
  let S' : Muon.Setup.FrozenSamples P0 m n B := Classical.choice (frozenSamples_nonempty m n B)
  have hlaw := lem_app_dyn_chains_i p S.C S.cs t D 0 hD F rfl rfl rfl S'
  have hsum := (lem_app_dyn_chains_iii p S.C S.cs t D 0 hD S.size).1
  have hmeasV : ∀ k, AEMeasurable (fun ω => (def_app_dyn_chains p S.C S.cs t D 0 ω).statV k) P := by
    intro k
    exact prefix_statV_rand_aem p S.C S.cs t (fun _ => D) measurable_const hsum k
  have hpath : AEMeasurable (fun ω (k : ℕ) => (def_app_dyn_chains p S.C S.cs t D 0 ω).statV k) P :=
    aemeasurable_pi_iff.mpr hmeasV
  have hridge : 0 ≤ p.ϱ := p.hϱ.le
  have hQm : Measurable (fun K : Mat m n => Q p.ϱ K) :=
    measurable_Q.comp ((measurable_const (a := (⟨p.ϱ, hridge⟩ : Set.Ici (0 : ℝ)))).prodMk
      measurable_id)
  have hbufpath : AEMeasurable (fun ω' (s : ℤ) => frozenBuf F S' s ω') P0 :=
    (lem_app_setup_ema_law_ii F S').2.1
  have hpath' : AEMeasurable (fun ω' (k : ℕ) => frozenUpd F S' p.ϱ ((t : ℤ) + (k : ℤ) - 1) ω') P0 := by
    refine aemeasurable_pi_iff.mpr fun k => ?_
    exact hQm.comp_aemeasurable ((measurable_pi_apply ((t : ℤ) + (k : ℤ) - 1)).comp_aemeasurable hbufpath)
  have hmean : ∀ r : ℕ, Muon.mean P (fun ω => stationaryV p S.C S.cs t D r ω) =
      Muon.mean P0 (fun ω' => frozenUpd F S' p.ϱ ((t : ℤ) + (r : ℤ)) ω') := by
    intro r
    ext i j
    simp only [Muon.mean, Matrix.of_apply]
    have hf : Continuous (fun y : ℕ → Mat m n => y (r + 1) i j) := by fun_prop
    have e1 := integral_map hpath hf.aestronglyMeasurable
    have e2 := integral_map hpath' hf.aestronglyMeasurable
    rw [hlaw.2.2.1] at e1
    have e3 := e1.symm.trans e2
    have e4 : (t : ℤ) + ((r + 1 : ℕ) : ℤ) - 1 = (t : ℤ) + r := by push_cast; ring
    simp only [e4] at e3
    exact e3
  have hshift : ∀ k : ℤ, Muon.mean P0 (fun ω' => frozenUpd F S' p.ϱ k ω') =
      Muon.mean P0 (fun ω' => frozenUpd F S' p.ϱ 0 ω') := by
    intro k
    ext i j
    simp only [Muon.mean, Matrix.of_apply]
    have hst := (lem_app_setup_ema_law_ii F S').2.2 k
    have hB2 : AEMeasurable (fun ω (s : ℤ) => frozenBuf F S' (s + k) ω) P0 := by
      have : Measurable (fun (x : ℤ → Mat m n) (s : ℤ) => x (s + k)) :=
        Measurable.of_eval fun s => measurable_pi_apply (s + k)
      exact this.comp_aemeasurable hbufpath
    have hΨ : Measurable (fun x : ℤ → Mat m n => Q p.ϱ (x 0) i j) := by
      have h0 : Measurable (fun x : ℤ → Mat m n => Q p.ϱ (x 0)) := hQm.comp (measurable_pi_apply 0)
      have he : Measurable (fun M : Mat m n => M i j) := by fun_prop
      exact he.comp h0
    have e1 := integral_map hB2 hΨ.aestronglyMeasurable
    have e2 := integral_map hbufpath hΨ.aestronglyMeasurable
    rw [hst] at e1
    have e3 : ∫ ω, Q p.ϱ (frozenBuf F S' (0 + k) ω) i j ∂P0 =
        ∫ ω, Q p.ϱ (frozenBuf F S' 0 ω) i j ∂P0 := e1.symm.trans e2
    rw [zero_add] at e3
    exact e3
  calc Muon.mean P (fun ω => stationaryV p S.C S.cs t D r ω)
      = Muon.mean P0 (fun ω' => frozenUpd F S' p.ϱ ((t : ℤ) + (r : ℤ)) ω') := hmean r
    _ = Muon.mean P0 (fun ω' => frozenUpd F S' p.ϱ 0 ω') := hshift _
    _ = Muon.mean P0 (fun ω' => frozenUpd F S' p.ϱ ((t : ℤ) + ((0 : ℕ) : ℤ)) ω') := (hshift _).symm
    _ = Muon.mean P (fun ω => stationaryV p S.C S.cs t D 0 ω) := (hmean 0).symm
    _ = dynVbar p S t D := rfl

/-- The coupling error `𝔼[𝟙_{t<τ⁺}‖V̂_r − V_r‖_F] ≤ K √B β^{r+1}`. -/
private lemma rs_errV_bound (p : DynParams) :
    ∃ K2 : ℝ, 0 ≤ K2 ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B) (t r : ℕ),
      Integrable ({ω | (t : ℕ∞) < tauPlus p S ω}.indicator (fun ω => fro (dynErrV p S t r ω))) P ∧
      ∫ ω, {ω | (t : ℕ∞) < tauPlus p S ω}.indicator (fun ω => fro (dynErrV p S t r ω)) ω ∂P
        ≤ K2 * Real.sqrt (B : ℝ) * p.β ^ (r + 1) := by
  have hrlo : 0 < (enl (admBase p)).1 := by simp only [enl, admBase]; linarith [p.hr0]
  obtain ⟨Cbuf, hCbuf0, hbuf⟩ := prefix_buffer_bound p
  obtain ⟨Cinit, hCinit0, hinit⟩ := prefix_chainInit_bound p
  set cdec : ℝ := 2 * ((enl (admBase p)).1 * p.ϱ)⁻¹ with hcdec_def
  have hcdec : 0 ≤ cdec := mul_nonneg (by norm_num) (inv_nonneg.mpr (mul_pos hrlo p.hϱ).le)
  refine ⟨Real.sqrt (cdec * (Cbuf + Cinit)), Real.sqrt_nonneg _, ?_⟩
  intro Ω _ P _ m n B S t r
  set A : Set Ω := {ω | (t : ℕ∞) < tauPlus p S ω} with hAdef
  have hAF : MeasurableSet[dynPast S t] A := concentration_tauPlus_meas S t
  have hAm : MeasurableSet A := concentration_past_le S t _ hAF
  have hAK : ∀ ω ∈ A, dynDelta S t ω ∈ admSetOf S.C (enl (admBase p)) := fun ω hω =>
    (concentration_tauPlus_iff S t ω).1 hω t le_rfl
  have herrV : Measurable (dynErrV p S t r) := prefix_errV_meas S t r
  obtain ⟨hbufint, hbufbd⟩ := hbuf Ω P m n B S t A hAm (fun ω hω => le_of_lt hω)
  obtain ⟨hinitint, hinitbd⟩ := hinit Ω P m n B S t A hAF hAK
  set f : Ω → ℝ := A.indicator (fun ω => fro (dynErrV p S t r ω)) with hfdef
  set g2 : Ω → ℝ := fun ω => cdec * p.β ^ (2 * (r + 1)) *
    (A.indicator (fun ω => fro (dynBuf S t ω) ^ 2) ω +
      A.indicator (fun ω => fro (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω) ^ 2) ω)
    with hg2def
  have hg2int : Integrable g2 P := (hbufint.add hinitint).const_mul _
  have hfmeas : AEStronglyMeasurable f P :=
    (((prefix_fro_cont (m := m) (n := n)).measurable.comp herrV).indicator hAm).aestronglyMeasurable
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => Set.indicator_nonneg (fun _ _ => tr_fro_nonneg _) ω
  have hf2le : ∀ ω, f ω ^ 2 ≤ g2 ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [hfdef, hg2def, Set.indicator_of_mem hω]
      exact prefix_errV_path p S (enl (admBase p)).1 hrlo t r ω (hAK ω hω).1
    · simp [hfdef, hg2def, Set.indicator_of_notMem hω]
  have hf2int : Integrable (fun ω => f ω ^ 2) P :=
    hg2int.mono' (hfmeas.pow 2) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hf2le ω)
  obtain ⟨hfint, -⟩ := prefix_amgm f hfmeas hf0 hf2int 1 zero_lt_one
  refine ⟨hfint, ?_⟩
  have hsq : (∫ ω, f ω ∂P) ^ 2 ≤ cdec * (Cbuf + Cinit) * p.β ^ (2 * (r + 1)) * (B : ℝ) := by
    refine (prefix_sq_integral_le hfmeas hf2int).trans ?_
    calc ∫ ω, f ω ^ 2 ∂P ≤ ∫ ω, g2 ω ∂P := integral_mono hf2int hg2int hf2le
      _ = cdec * p.β ^ (2 * (r + 1)) * (∫ ω, A.indicator (fun ω => fro (dynBuf S t ω) ^ 2) ω ∂P +
            ∫ ω, A.indicator (fun ω => fro (chainInit p.β S.C (dynDelta S t ω)
              (S.cs.aux (t : ℤ)) ω) ^ 2) ω ∂P) := by
          rw [hg2def, integral_const_mul, integral_add hbufint hinitint]
      _ ≤ cdec * p.β ^ (2 * (r + 1)) * (Cbuf * B + Cinit * B) :=
          mul_le_mul_of_nonneg_left (add_le_add hbufbd hinitbd) (mul_nonneg hcdec (pow_nonneg p.hβ.1 _))
      _ = _ := by ring
  have hR0 : 0 ≤ Real.sqrt (cdec * (Cbuf + Cinit)) * Real.sqrt (B : ℝ) * p.β ^ (r + 1) := by
    have := pow_nonneg p.hβ.1 (r + 1); positivity
  have hRsq : (Real.sqrt (cdec * (Cbuf + Cinit)) * Real.sqrt (B : ℝ) * p.β ^ (r + 1)) ^ 2 =
      cdec * (Cbuf + Cinit) * p.β ^ (2 * (r + 1)) * (B : ℝ) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (Nat.cast_nonneg _), ← pow_mul]
    ring_nf
  have hI0 : 0 ≤ ∫ ω, f ω ∂P := integral_nonneg hf0
  rw [← hRsq] at hsq
  exact (pow_le_pow_iff_left₀ hI0 hR0 two_ne_zero).1 hsq

private lemma rs_Pt_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (t : ℕ) (Pt : Ω → Mat m n)
    (hPtm : ∀ i j, Measurable[dynPast S t] (fun ω => Pt ω i j)) : Measurable[dynPast S t] Pt :=
  @Measurable.of_eval Ω (Fin m) (fun _ => Fin n → ℝ) (dynPast S t) _ Pt fun i =>
    @Measurable.of_eval Ω (Fin n) (fun _ => ℝ) (dynPast S t) _ (fun ω => Pt ω i) fun j => hPtm i j

/-- `𝔼_t[𝟙_{t<τ⁺}⟨Π_t, V_r⟩] = ⟨Π_t, V̄(Δ_t)⟩` on `{t < τ⁺}`. -/
private lemma rs_statV_cond (p : DynParams) (cPi : ℝ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (t r : ℕ) (Pt : Ω → Mat m n)
    (hPt : ∀ ω, fro (Pt ω) ≤ cPi) (hPtm : ∀ i j, Measurable[dynPast S t] (fun ω => Pt ω i j)) :
    Integrable ({ω | (t : ℕ∞) < tauPlus p S ω}.indicator
      (fun ω => frobIP (Pt ω) (stationaryV p S.C S.cs t (dynDelta S t ω) r ω))) P ∧
    ∀ᵐ ω ∂P, ω ∈ {ω | (t : ℕ∞) < tauPlus p S ω} →
      condExp (dynPast S t) P ({ω | (t : ℕ∞) < tauPlus p S ω}.indicator
        (fun ω => frobIP (Pt ω) (stationaryV p S.C S.cs t (dynDelta S t ω) r ω))) ω =
      frobIP (Pt ω) (dynVbar p S t (dynDelta S t ω)) := by
  have hrlo : 0 < (enl (admBase p)).1 := by simp only [enl, admBase]; linarith [p.hr0]
  set I : Set Ω := {ω | (t : ℕ∞) < tauPlus p S ω} with hIdef
  have hI : MeasurableSet[dynPast S t] I := concentration_tauPlus_meas S t
  have hIm : MeasurableSet I := concentration_past_le S t _ hI
  have hIA : ∀ ω ∈ I, dynDelta S t ω ∈ admAplus p S.C := fun ω hω =>
    (concentration_tauPlus_iff S t ω).1 hω t le_rfl
  have hPtF : Measurable[dynPast S t] Pt := rs_Pt_meas S t Pt hPtm
  set X : Ω → Mat m n × Mat m n × Mat m n := fun ω => (dynDelta S t ω, dynBuf S t ω, Pt ω) with hXdef
  have hXF : Measurable[dynPast S t] X :=
    (concentration_delta_meas S t).prodMk ((concentration_state_meas S t).2.prodMk hPtF)
  have hX : Measurable X := hXF.mono (concentration_past_le S t) le_rfl
  set Y := trY S.cs t with hYdef
  have hYF : Measurable[chainFuture S.cs t] Y := tr_Y_meas S.cs t
  have hY : Measurable Y := hYF.mono (tr_chainFuture_le S.cs t) le_rfl
  have hind : Indep (dynPast S t) (MeasurableSpace.comap Y inferInstance) P :=
    indep_of_indep_of_le_right (prefix_indep_past_future S t) (measurable_iff_comap_le.1 hYF)
  have hΨm := rs_PsiV_meas (B := B) p S.C t r
  set g : Ω → ℝ := fun ω => trPsiV p S.C t r (X ω) (Y ω) with hgdef
  have hgint : Integrable g P := by
    refine Integrable.of_bound (hΨm.comp (hX.prodMk hY)).aestronglyMeasurable
      (max cPi 0 * Real.sqrt ((min m n : ℕ) : ℝ)) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    refine (rs_PsiV_bound p S.C t r (X ω) (Y ω)).trans ?_
    exact mul_le_mul_of_nonneg_right ((hPt ω).trans (le_max_left _ _)) (Real.sqrt_nonneg _)
  have hfg : I.indicator (fun ω => frobIP (Pt ω) (stationaryV p S.C S.cs t (dynDelta S t ω) r ω)) =
      I.indicator g := by
    funext ω
    by_cases hω : ω ∈ I
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      exact (rs_PsiV_eq p S.C S.cs t r (X ω) (hIA ω hω) ω).symm
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
  refine ⟨by rw [hfg]; exact hgint.indicator hIm, ?_⟩
  have hce := condExp_indicator hgint hI
  have hfr : condExp (dynPast S t) P g =ᵐ[P] fun ω => ∫ y, trPsiV p S.C t r (X ω) y ∂(P.map Y) :=
    Muon.Foundations.freezing_condExp (dynPast S t) (concentration_past_le S t) hXF hY hind hΨm hgint
  rw [hfg]
  filter_upwards [hce, hfr] with ω h1 h2 hω
  rw [h1, Set.indicator_of_mem hω, h2]
  have hx := hIA ω hω
  have hΨx : Measurable (trPsiV (B := B) p S.C t r (X ω)) := hΨm.of_uncurry_left
  rw [integral_map hY.aemeasurable hΨx.aestronglyMeasurable]
  have e1 : (fun ω' => trPsiV p S.C t r (X ω) (Y ω')) =
      fun ω' => frobIP (Pt ω) (stationaryV p S.C S.cs t (dynDelta S t ω) r ω') := by
    funext ω'; exact rs_PsiV_eq p S.C S.cs t r (X ω) hx ω'
  rw [e1]
  have hVint : ∀ i j, Integrable (fun ω' => stationaryV p S.C S.cs t (dynDelta S t ω) r ω' i j) P := by
    intro i j
    have hD : Measurable (fun _ : Ω => dynDelta S t ω) := measurable_const
    have hstatN := prefix_ema_meas S t hD (prefix_chainInit_meas S t hD) (r + 1)
    have hstatV : Measurable (fun ω' => stationaryV p S.C S.cs t (dynDelta S t ω) r ω') :=
      prefix_Q_meas S hD hstatN
    have he : Measurable (fun M : Mat m n => M i j) := by fun_prop
    refine Integrable.of_bound (he.comp hstatV).aestronglyMeasurable (Real.sqrt ((min m n : ℕ) : ℝ))
      (Eventually.of_forall fun ω' => ?_)
    rw [Real.norm_eq_abs]
    exact (prefix_abs_entry_le_fro _ i j).trans ((le_abs_self _).trans
      (Real.abs_le_sqrt (prefix_statV_fro_sq p S.C S.cs t r _ ω')))
  rw [rs_integral_frobIP _ _ hVint, rs_mean_shift p S t r _ (lt_of_lt_of_le hrlo hx.1)]

/-- `𝔼_t[𝟙_{t<τ⁺}⟨Π_t, V̇_r⟩]` is the frozen stationary-tangent integral on `{t < τ⁺}`. -/
private lemma rs_statTan_cond (p : DynParams) (cPi : ℝ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (t r : ℕ) (Pt : Ω → Mat m n)
    (hPt : ∀ ω, fro (Pt ω) ≤ cPi) (hPtm : ∀ i j, Measurable[dynPast S t] (fun ω => Pt ω i j)) :
    Integrable ({ω | (t : ℕ∞) < tauPlus p S ω}.indicator
      (fun ω => frobIP (Pt ω) (dynStatTangent p S t r ω))) P ∧
    ∀ᵐ ω ∂P, ω ∈ {ω | (t : ℕ∞) < tauPlus p S ω} →
      condExp (dynPast S t) P ({ω | (t : ℕ∞) < tauPlus p S ω}.indicator
        (fun ω => frobIP (Pt ω) (dynStatTangent p S t r ω))) ω =
      ∫ ω', frobIP (Pt ω) (causalDot p S.C (fun s => physBatch S.C (S.cs.act s) ω') t (dynDelta S t ω)
        (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω') r) ∂P := by
  set rlo : ℝ := (enl (admBase p)).1 with hrlodef
  set rhi : ℝ := (enl (admBase p)).2.1 with hrhidef
  have hrlo : 0 < rlo := by simp only [hrlodef, enl, admBase]; linarith [p.hr0]
  have hle : rlo ≤ rhi := by simp only [hrlodef, hrhidef, enl, admBase]; linarith [p.hr0, p.hr]
  set c : ℝ := 2 * rlo * p.ϱ with hcdef
  have hc : 0 < c := by have := p.hϱ; positivity
  have hA : admAplus p S.C ⊆ {D | rlo ≤ riskSigma S.C D ∧ riskSigma S.C D ≤ rhi} :=
    fun D hD => ⟨hD.1, hD.2.1⟩
  set I : Set Ω := {ω | (t : ℕ∞) < tauPlus p S ω} with hIdef
  have hI : MeasurableSet[dynPast S t] I := concentration_tauPlus_meas S t
  have hIm : MeasurableSet I := concentration_past_le S t _ hI
  have hIA : ∀ ω ∈ I, dynDelta S t ω ∈ admAplus p S.C := fun ω hω =>
    (concentration_tauPlus_iff S t ω).1 hω t le_rfl
  have hPtF : Measurable[dynPast S t] Pt := rs_Pt_meas S t Pt hPtm
  set X : Ω → Mat m n × Mat m n × Mat m n := fun ω => (dynDelta S t ω, dynBuf S t ω, Pt ω) with hXdef
  have hXF : Measurable[dynPast S t] X :=
    (concentration_delta_meas S t).prodMk ((concentration_state_meas S t).2.prodMk hPtF)
  have hX : Measurable X := hXF.mono (concentration_past_le S t) le_rfl
  set Y := trY S.cs t with hYdef
  have hYF : Measurable[chainFuture S.cs t] Y := tr_Y_meas S.cs t
  have hY : Measurable Y := hYF.mono (tr_chainFuture_le S.cs t) le_rfl
  have hind : Indep (dynPast S t) (MeasurableSpace.comap Y inferInstance) P :=
    indep_of_indep_of_le_right (prefix_indep_past_future S t) (measurable_iff_comap_le.1 hYF)
  have hΨm := rs_PsiS_meas (B := B) p S.C t r hc
  set g : Ω → ℝ := fun ω => trPsiS p S.C t r c (X ω) (Y ω) with hgdef
  have hgint : Integrable g P :=
    rs_PsiS_integrable p cPi rlo rhi hrlo hle S.C S.cs t r c X S.size hA le_rfl hX (fun ω => hPt ω) hΨm
  have hpos : ∀ ω ∈ I, 0 < riskSigma S.C (dynDelta S t ω) ∧ c ≤ physRidge p S.C (dynDelta S t ω) := by
    intro ω hω
    have hx := hIA ω hω
    refine ⟨lt_of_lt_of_le hrlo hx.1, ?_⟩
    unfold physRidge; have := p.hϱ; nlinarith [hx.1]
  have hfg : I.indicator (fun ω => frobIP (Pt ω) (dynStatTangent p S t r ω)) = I.indicator g := by
    funext ω
    by_cases hω : ω ∈ I
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      exact (rs_PsiS_eq p S.C S.cs t r (X ω) (hIA ω hω) (hpos ω hω).1 (hpos ω hω).2 ω).symm
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
  refine ⟨by rw [hfg]; exact hgint.indicator hIm, ?_⟩
  have hce := condExp_indicator hgint hI
  have hfr : condExp (dynPast S t) P g =ᵐ[P] fun ω => ∫ y, trPsiS p S.C t r c (X ω) y ∂(P.map Y) :=
    Muon.Foundations.freezing_condExp (dynPast S t) (concentration_past_le S t) hXF hY hind hΨm hgint
  rw [hfg]
  filter_upwards [hce, hfr] with ω h1 h2 hω
  rw [h1, Set.indicator_of_mem hω, h2]
  have hΨx : Measurable (trPsiS (B := B) p S.C t r c (X ω)) := hΨm.of_uncurry_left
  rw [integral_map hY.aemeasurable hΨx.aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun ω' => ?_)
  exact rs_PsiS_eq p S.C S.cs t r (X ω) (hIA ω hω) (hpos ω hω).1 (hpos ω hω).2 ω'

private lemma rs_frobIP_decomp {m n : ℕ} (T U H Vd Vs Vr : Mat m n) (l : ℝ) :
    frobIP T U = frobIP T (U - H - l • Vd) + frobIP T (H - Vr) + l * frobIP T (Vd - Vs) +
      l * frobIP T Vs + frobIP T Vr := by
  simp only [prefix_frobIP_eq_sum, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma rs_diffuseness_meas {m n : ℕ} (C : Covariances m n) :
    Measurable (fun Δ : Mat m n => diffuseness C Δ) := by
  unfold diffuseness normState Ahat
  have h1 : Measurable (fun Δ : Mat m n => (Real.sqrt (2 * riskSigma C Δ))⁻¹) :=
    (((concentration_risk_cont C).measurable.const_mul 2).sqrt).inv
  have h2 : Continuous (fun Δ : Mat m n => Arot C Δ) := by unfold Arot; fun_prop
  exact projection_opNorm_continuous.measurable.comp (h1.smul h2.measurable)

set_option maxHeartbeats 8000000 in
private theorem rs_main (certQ : Muon.External.GaussianQuadFormLp) (certOp : Muon.External.GaussianOpNormL6) (certP : Muon.External.GaussianPoincare) (p : DynParams) (cPi : ℝ) (δ : ℕ → ℝ) (hδ : Antitone δ)
    (hδ0 : Tendsto δ atTop (𝓝 0)) :
    ∃ B0 : ℕ, ∃ K : ℝ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (m n B : ℕ) (S : DynSetup p P m n B) (t : ℕ) (Pt : Ω → Mat m n),
        B0 ≤ B → prefixLen p.β B ≤ t →
        (∀ ω, fro (Pt ω) ≤ cPi ∧ opNorm (Pt ω) ≤ cPi) →
        (∀ i j, Measurable[dynPast S t] (fun ω => Pt ω i j)) →
          Integrable ({ω | (t : ℕ∞) < tauPlus p S ω ∧ diffuseness S.C (dynDelta S t ω) ≤ δ B}.indicator
            (fun ω => |((1 / (blockLen B : ℝ)) * ∑ r ∈ Finset.Ico (prefixLen p.β B) (blockLen B),
              frobIP (Pt ω) (Muon.Foundations.condExpMat (dynPast S t) P (dynUpd S (t + r)) ω
                - dynVbar p S t (dynDelta S t ω)))|)) P ∧
          ∫ ω, {ω | (t : ℕ∞) < tauPlus p S ω ∧ diffuseness S.C (dynDelta S t ω) ≤ δ B}.indicator
            (fun ω => |((1 / (blockLen B : ℝ)) * ∑ r ∈ Finset.Ico (prefixLen p.β B) (blockLen B),
              frobIP (Pt ω) (Muon.Foundations.condExpMat (dynPast S t) P (dynUpd S (t + r)) ω
                - dynVbar p S t (dynDelta S t ω)))|) ω ∂P
            ≤ responseRho p K cPi δ B := by
  set κ : ℝ × ℝ × ℝ := enl (admBase p) with hκ
  have hrlo : 0 < κ.1 := by simp only [hκ, enl, admBase]; linarith [p.hr0]
  have hle : κ.1 ≤ κ.2.1 := by simp only [hκ, enl, admBase]; linarith [p.hr0, p.hr]
  obtain ⟨BT, KT, hT⟩ := lem_app_dyn_taylor certOp p κ.1 κ.2.1 κ.2.2 hrlo hle
  obtain ⟨Btr, Ktr, htr⟩ := prop_app_dyn_transport certQ certOp certP p cPi
  obtain ⟨Cst, hst⟩ := prop_app_dyn_stationary_tangent certQ p cPi κ.1 κ.2.1
  obtain ⟨K2, hK20, herr⟩ := rs_errV_bound p
  obtain ⟨Bq, hBq⟩ := prefix_q_le_L p.β
  have hδB : ∀ B : ℕ, 0 ≤ δ B := fun B => hδ.le_of_tendsto hδ0 B
  refine ⟨max (max BT Btr) (max Bq 1),
    max cPi 0 * max KT 0 + max cPi 0 * K2 + max Ktr 0 + max Cst 0, ?_⟩
  intro Ω _ P _ m n B S t Pt hB ht hPt hPtm
  set cPi' : ℝ := max cPi 0 with hcPi'
  set KT' : ℝ := max KT 0 with hKT'
  set Ktr' : ℝ := max Ktr 0 with hKtr'
  set Cst' : ℝ := max Cst 0 with hCst'
  have hKT0 : 0 ≤ KT' := le_max_right _ _
  have hKtr0 : 0 ≤ Ktr' := le_max_right _ _
  have hCst0 : 0 ≤ Cst' := le_max_right _ _
  have hcPi0' : 0 ≤ cPi' := le_max_right _ _
  have hBT : BT ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  have hBtr : Btr ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hBq' : Bq ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hB1 : 1 ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  obtain ⟨-, hqL⟩ := hBq B hBq'
  obtain ⟨-, hq1⟩ := prefix_q_ge_log p.β B hB1
  have hB0 : 0 < B := hB1
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB0
  have hBr1 : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hsB : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBr
  have hL1 : 1 ≤ blockLen B := hq1.trans hqL
  have hL1r : (1 : ℝ) ≤ blockLen B := by exact_mod_cast hL1
  have hLr : (0 : ℝ) < blockLen B := by linarith
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) := Real.log_nonneg (by linarith)
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure P
  have hcPi : 0 ≤ cPi := (tr_fro_nonneg _).trans (hPt ω0).1
  have hlam : 0 ≤ p.h / (B : ℝ) := div_nonneg p.hh.le hBr.le
  have hβ0 := p.hβ.1
  have hOm0 : 0 ≤ omegaBeta p.β ((prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ)) :=
    tsum_nonneg fun k => le_min (by positivity) (pow_nonneg p.hβ.1 _)
  have hδ0B := hδB B
  set G : Set Ω := {ω | (t : ℕ∞) < tauPlus p S ω} with hGdef
  set 𝔈 : Set Ω := {ω | (t : ℕ∞) < tauPlus p S ω ∧ diffuseness S.C (dynDelta S t ω) ≤ δ B} with h𝔈def
  have hGF : MeasurableSet[dynPast S t] G := concentration_tauPlus_meas S t
  have hGm : MeasurableSet G := concentration_past_le S t _ hGF
  have hGA : ∀ ω ∈ G, dynDelta S t ω ∈ admAplus p S.C := fun ω hω =>
    (concentration_tauPlus_iff S t ω).1 hω t le_rfl
  have h𝔈G : 𝔈 ⊆ G := fun ω hω => hω.1
  have h𝔈m : MeasurableSet 𝔈 := by
    have hd : Measurable (fun ω => diffuseness S.C (dynDelta S t ω)) :=
      (rs_diffuseness_meas S.C).comp ((concentration_delta_meas S t).mono (concentration_past_le S t) le_rfl)
    have e : 𝔈 = G ∩ {ω | diffuseness S.C (dynDelta S t ω) ≤ δ B} := rfl
    rw [e]
    exact hGm.inter (measurableSet_le hd measurable_const)
  have hPtF := rs_Pt_meas S t Pt hPtm
  have hPtM : Measurable Pt := hPtF.mono (concentration_past_le S t) le_rfl
  have hPtb : ∀ ω i j, |Pt ω i j| ≤ cPi := fun ω i j => (prefix_abs_entry_le_fro _ i j).trans (hPt ω).1
  have hPt' : ∀ ω, fro (Pt ω) ≤ cPi' := fun ω => (hPt ω).1.trans (le_max_left _ _)
  have hfrobc : Continuous (fun q : Mat m n × Mat m n => frobIP q.1 q.2) := by unfold frobIP; fun_prop
  set c1 : ℕ → Ω → ℝ := fun r => condExp (dynPast S t) P (G.indicator (fun ω => frobIP (Pt ω)
    (dynUpd S (t + r) ω - dynHatV p S t r ω - (p.h / (B : ℝ)) • dynTangent p S t r ω))) with hc1
  set c2 : ℕ → Ω → ℝ := fun r => condExp (dynPast S t) P (G.indicator (fun ω => frobIP (Pt ω)
    (dynErrV p S t r ω))) with hc2
  set c3 : ℕ → Ω → ℝ := fun r => condExp (dynPast S t) P (G.indicator (fun ω => frobIP (Pt ω)
    (dynTangent p S t r ω - dynStatTangent p S t r ω))) with hc3
  set c4 : ℕ → Ω → ℝ := fun r => condExp (dynPast S t) P (G.indicator (fun ω => frobIP (Pt ω)
    (dynStatTangent p S t r ω))) with hc4
  have key : ∀ r, r < blockLen B →
      (∀ᵐ ω ∂P, ω ∈ G → frobIP (Pt ω) (Muon.Foundations.condExpMat (dynPast S t) P (dynUpd S (t + r)) ω
        - dynVbar p S t (dynDelta S t ω)) =
          c1 r ω + c2 r ω + (p.h / (B : ℝ)) * c3 r ω + (p.h / (B : ℝ)) * c4 r ω) ∧
      (∀ᵐ ω ∂P, ω ∈ 𝔈 → (p.h / (B : ℝ)) * |c4 r ω| ≤
        Cst' * ((r : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ) + δ B * (cPi + δ B))) ∧
      ∫ ω, |c1 r ω| ∂P ≤ cPi' * (KT' * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ)) ∧
      ∫ ω, |c2 r ω| ∂P ≤ cPi' * (K2 * Real.sqrt (B : ℝ) * p.β ^ (r + 1)) ∧
      (p.h / (B : ℝ)) * ∫ ω, G.indicator (fun ω => |c3 r ω|) ω ∂P
        ≤ Ktr * ((r : ℝ) / Real.sqrt (B : ℝ) + omegaBeta p.β ((prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ))
          + p.β ^ prefixLen p.β B + Real.sqrt (B : ℝ) * (r : ℝ) * p.β ^ (r + 1)) := by
    intro r hr
    obtain ⟨hi3, -, hb3⟩ := htr Ω P m n B S t Pt hBtr ht hPt hPtm r hr
    obtain ⟨hi4, hcd4⟩ := rs_statTan_cond p cPi S t r Pt (fun ω => (hPt ω).1) hPtm
    obtain ⟨hi5, hcd5⟩ := rs_statV_cond p cPi S t r Pt (fun ω => (hPt ω).1) hPtm
    obtain ⟨he2i, he2b⟩ := herr Ω P m n B S t r
    have hUm : Measurable (dynUpd S (t + r)) :=
      (concentration_upd_meas S (t + r)).mono (concentration_past_le S (t + r + 1)) le_rfl
    have hUb : ∀ ω, fro (dynUpd S (t + r) ω) ≤ Real.sqrt (p.γstar * B) := fun ω =>
      concentration_dynUpd_fro_bound p S ω (t + r)
    have hSi : Integrable (fun ω => frobIP (Pt ω) (dynUpd S (t + r) ω)) P := by
      refine Integrable.of_bound (hfrobc.measurable.comp (hPtM.prodMk hUm)).aestronglyMeasurable
        (cPi' * Real.sqrt (p.γstar * B)) (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      exact (projection_frobIP_le _ _).trans (mul_le_mul (hPt' ω) (hUb ω) (tr_fro_nonneg _) hcPi0')
    have hi2 : Integrable (G.indicator (fun ω => frobIP (Pt ω) (dynErrV p S t r ω))) P := by
      refine (he2i.const_mul cPi').mono'
        ((hfrobc.measurable.comp (hPtM.prodMk (prefix_errV_meas S t r))).indicator hGm).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      by_cases hω : (t : ℕ∞) < tauPlus p S ω
      · have hωG : ω ∈ G := hω
        have hωS : ω ∈ {ω | (t : ℕ∞) < tauPlus p S ω} := hω
        simp only [Set.indicator_of_mem hωG, Set.indicator_of_mem hωS]
        exact (projection_frobIP_le _ _).trans (mul_le_mul_of_nonneg_right (hPt' ω) (tr_fro_nonneg _))
      · have hωG : ω ∉ G := hω
        have hωS : ω ∉ {ω | (t : ℕ∞) < tauPlus p S ω} := hω
        simp only [Set.indicator_of_notMem hωG, Set.indicator_of_notMem hωS, abs_zero, mul_zero, le_refl]
    have hsum : ∀ ω, frobIP (Pt ω) (dynUpd S (t + r) ω) =
        frobIP (Pt ω) (dynUpd S (t + r) ω - dynHatV p S t r ω - (p.h / (B : ℝ)) • dynTangent p S t r ω) +
        frobIP (Pt ω) (dynErrV p S t r ω) +
        (p.h / (B : ℝ)) * frobIP (Pt ω) (dynTangent p S t r ω - dynStatTangent p S t r ω) +
        (p.h / (B : ℝ)) * frobIP (Pt ω) (dynStatTangent p S t r ω) +
        frobIP (Pt ω) (stationaryV p S.C S.cs t (dynDelta S t ω) r ω) := fun ω =>
      rs_frobIP_decomp (Pt ω) (dynUpd S (t + r) ω) (dynHatV p S t r ω) (dynTangent p S t r ω)
        (dynStatTangent p S t r ω) (stationaryV p S.C S.cs t (dynDelta S t ω) r ω) (p.h / (B : ℝ))
    have hi1 : Integrable (G.indicator (fun ω => frobIP (Pt ω)
        (dynUpd S (t + r) ω - dynHatV p S t r ω - (p.h / (B : ℝ)) • dynTangent p S t r ω))) P := by
      refine (((((hSi.indicator hGm).sub hi2).sub (hi3.const_mul (p.h / (B : ℝ)))).sub
        (hi4.const_mul (p.h / (B : ℝ)))).sub hi5).congr (Eventually.of_forall fun ω => ?_)
      by_cases hω : (t : ℕ∞) < tauPlus p S ω
      · have hωG : ω ∈ G := hω
        have hωS : ω ∈ {ω | (t : ℕ∞) < tauPlus p S ω} := hω
        simp only [Pi.sub_apply, Set.indicator_of_mem hωG, Set.indicator_of_mem hωS]
        rw [hsum ω]; ring
      · have hωG : ω ∉ G := hω
        have hωS : ω ∉ {ω | (t : ℕ∞) < tauPlus p S ω} := hω
        simp only [Pi.sub_apply, Set.indicator_of_notMem hωG, Set.indicator_of_notMem hωS]; ring
    have he : ∀ i j, Measurable (fun M : Mat m n => M i j) := fun i j => by fun_prop
    have hpull := rs_pullout (P := P) (dynPast S t) (concentration_past_le S t) Pt (dynUpd S (t + r)) cPi hPtm hPtb
      (fun i j => Integrable.of_bound ((he i j).comp hUm).aestronglyMeasurable (Real.sqrt (p.γstar * B))
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]; exact (prefix_abs_entry_le_fro _ i j).trans (hUb ω)))
    have hlin := rs_lin_identity (dynPast S t) G hGF (p.h / (B : ℝ))
      (fun ω => frobIP (Pt ω) (dynUpd S (t + r) ω))
      (fun ω => frobIP (Pt ω) (dynUpd S (t + r) ω - dynHatV p S t r ω - (p.h / (B : ℝ)) • dynTangent p S t r ω))
      (fun ω => frobIP (Pt ω) (dynErrV p S t r ω))
      (fun ω => frobIP (Pt ω) (dynTangent p S t r ω - dynStatTangent p S t r ω))
      (fun ω => frobIP (Pt ω) (dynStatTangent p S t r ω))
      (fun ω => frobIP (Pt ω) (stationaryV p S.C S.cs t (dynDelta S t ω) r ω))
      (fun ω => frobIP (Pt ω) (dynVbar p S t (dynDelta S t ω))) hsum hSi hi1 hi2 hi3 hi4 hi5 hcd5
    refine ⟨?_, ?_, ?_, ?_, hb3⟩
    · filter_upwards [hpull, hlin] with ω h1 h2 hω
      rw [prefix_frobIP_sub_right, h1]
      exact h2 hω
    · filter_upwards [hcd4] with ω h hω
      have hωG := h𝔈G hω
      have hx := hGA ω hωG
      have h' : c4 r ω = ∫ ω', frobIP (Pt ω) (causalDot p S.C (fun s => physBatch S.C (S.cs.act s) ω') t
          (dynDelta S t ω) (chainInit p.β S.C (dynDelta S t ω) (S.cs.aux (t : ℤ)) ω') r) ∂P := h hωG
      rw [h']
      have hm : (m : ℝ) ≤ p.γstar * B := le_trans (by exact_mod_cast le_max_left m n) S.size.1
      have hn : (n : ℝ) ≤ p.γstar * B := le_trans (by exact_mod_cast le_max_right m n) S.size.1
      have hs := (hst m n B Ω P S.C S.cs t r (dynDelta S t ω) (Pt ω) cPi hm hn S.size.2.1 S.size.2.2 hB0
        hrlo hx.1 hx.2.1 ⟨(hPt ω).1, (hPt ω).2, le_rfl⟩).2
      have hd0 : 0 ≤ diffuseness S.C (dynDelta S t ω) := tr_opNorm_nonneg _
      have hdδ : diffuseness S.C (dynDelta S t ω) ≤ δ B := hω.2
      have hX0 : 0 ≤ (r : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ) +
          diffuseness S.C (dynDelta S t ω) * (cPi + diffuseness S.C (dynDelta S t ω)) := by positivity
      refine hs.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hX0).trans
        (mul_le_mul_of_nonneg_left ?_ hCst0))
      exact add_le_add le_rfl (mul_le_mul hdδ (add_le_add le_rfl hdδ) (add_nonneg hcPi hd0) hδ0B)
    · obtain ⟨hTi, hTc⟩ := hT Ω P m n B S hBT t r (by omega)
      have hGK : G ⊆ dynInK S t (κ.1, κ.2.1, κ.2.2) := fun ω hω => hGA ω hω
      have hR1 : 0 ≤ KT' * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ) :=
        div_nonneg (mul_nonneg (mul_nonneg hKT0 (sq_nonneg _)) hlog) hsB.le
      obtain ⟨hFi, hFle⟩ := prefix_cond_transfer (dynPast S t) (concentration_past_le S t)
        (dynInK S t (κ.1, κ.2.1, κ.2.2)) G
        (fun ω => fro (dynUpd S (t + r) ω - dynHatV p S t r ω - (p.h / (B : ℝ)) • dynTangent p S t r ω))
        (fun _ => KT' * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ)) hGF hGK hTi
        ((integrable_const _).indicator hGm) (by
          filter_upwards [hTc] with ω h hω
          refine (h hω).trans ?_
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)) hlog) hsB.le)
      have hconst : ∫ ω, G.indicator (fun _ => KT' * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) /
          Real.sqrt (B : ℝ)) ω ∂P ≤ KT' * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ) := by
        rw [integral_indicator hGm, setIntegral_const, smul_eq_mul]
        have h1 := measureReal_le_one (μ := P) (s := G)
        have h2 := (measureReal_nonneg : 0 ≤ P.real G)
        nlinarith
      calc ∫ ω, |c1 r ω| ∂P ≤ ∫ ω, |G.indicator (fun ω => frobIP (Pt ω)
            (dynUpd S (t + r) ω - dynHatV p S t r ω - (p.h / (B : ℝ)) • dynTangent p S t r ω)) ω| ∂P :=
            integral_abs_condExp_le _
        _ ≤ ∫ ω, cPi' * G.indicator (fun ω => fro (dynUpd S (t + r) ω - dynHatV p S t r ω -
            (p.h / (B : ℝ)) • dynTangent p S t r ω)) ω ∂P := by
            refine integral_mono hi1.abs (hFi.const_mul _) fun ω => ?_
            by_cases hω : ω ∈ G
            · simp only [Set.indicator_of_mem hω]
              exact (projection_frobIP_le _ _).trans (mul_le_mul_of_nonneg_right (hPt' ω) (tr_fro_nonneg _))
            · simp only [Set.indicator_of_notMem hω, abs_zero, mul_zero, le_refl]
        _ = cPi' * ∫ ω, G.indicator (fun ω => fro (dynUpd S (t + r) ω - dynHatV p S t r ω -
            (p.h / (B : ℝ)) • dynTangent p S t r ω)) ω ∂P := integral_const_mul _ _
        _ ≤ cPi' * (KT' * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ)) :=
            mul_le_mul_of_nonneg_left (hFle.trans hconst) hcPi0'
    · calc ∫ ω, |c2 r ω| ∂P ≤ ∫ ω, |G.indicator (fun ω => frobIP (Pt ω) (dynErrV p S t r ω)) ω| ∂P :=
            integral_abs_condExp_le _
        _ ≤ ∫ ω, cPi' * G.indicator (fun ω => fro (dynErrV p S t r ω)) ω ∂P := by
            refine integral_mono hi2.abs (he2i.const_mul _) fun ω => ?_
            by_cases hω : ω ∈ G
            · simp only [Set.indicator_of_mem hω]
              exact (projection_frobIP_le _ _).trans (mul_le_mul_of_nonneg_right (hPt' ω) (tr_fro_nonneg _))
            · simp only [Set.indicator_of_notMem hω, abs_zero, mul_zero, le_refl]
        _ = cPi' * ∫ ω, G.indicator (fun ω => fro (dynErrV p S t r ω)) ω ∂P := integral_const_mul _ _
        _ ≤ cPi' * (K2 * Real.sqrt (B : ℝ) * p.β ^ (r + 1)) := mul_le_mul_of_nonneg_left he2b hcPi0'
  -- collect the almost sure statements
  have hall : ∀ᵐ ω ∂P, ∀ r : ℕ, r < blockLen B →
      (ω ∈ G → frobIP (Pt ω) (Muon.Foundations.condExpMat (dynPast S t) P (dynUpd S (t + r)) ω
        - dynVbar p S t (dynDelta S t ω)) =
          c1 r ω + c2 r ω + (p.h / (B : ℝ)) * c3 r ω + (p.h / (B : ℝ)) * c4 r ω) ∧
      (ω ∈ 𝔈 → (p.h / (B : ℝ)) * |c4 r ω| ≤
        Cst' * ((r : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ) + δ B * (cPi + δ B))) := by
    refine ae_all_iff.2 fun r => ?_
    by_cases hr : r < blockLen B
    · filter_upwards [(key r hr).1, (key r hr).2.1] with ω h1 h2 _
      exact ⟨h1, h2⟩
    · exact ae_of_all _ fun ω h => absurd h hr
  have hb40 : ∀ r : ℕ, 0 ≤ Cst' * ((r : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ) + δ B * (cPi + δ B)) :=
    fun r => mul_nonneg hCst0 (add_nonneg (add_nonneg (div_nonneg (Nat.cast_nonneg _) hsB.le)
      (div_nonneg zero_le_one hBr.le)) (mul_nonneg hδ0B (add_nonneg hcPi hδ0B)))
  set Φ : Ω → ℝ := 𝔈.indicator (fun ω => |(1 / (blockLen B : ℝ)) * ∑ r ∈ Finset.Ico (prefixLen p.β B) (blockLen B),
    (c1 r ω + c2 r ω + (p.h / (B : ℝ)) * c3 r ω + (p.h / (B : ℝ)) * c4 r ω)|) with hΦdef
  have hFΦ : 𝔈.indicator (fun ω => |((1 / (blockLen B : ℝ)) * ∑ r ∈ Finset.Ico (prefixLen p.β B) (blockLen B),
      frobIP (Pt ω) (Muon.Foundations.condExpMat (dynPast S t) P (dynUpd S (t + r)) ω
        - dynVbar p S t (dynDelta S t ω)))|) =ᵐ[P] Φ := by
    filter_upwards [hall] with ω h
    by_cases hω : ω ∈ 𝔈
    · rw [hΦdef, Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      congr 2
      exact Finset.sum_congr rfl fun r hr => (h r (Finset.mem_Ico.1 hr).2).1 (h𝔈G hω)
    · rw [hΦdef, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
  have hΦint : Integrable Φ P := by
    refine (Integrable.abs ?_).indicator h𝔈m
    refine (integrable_finsetSum _ fun r _ => ?_).const_mul _
    exact ((integrable_condExp.add integrable_condExp).add (integrable_condExp.const_mul _)).add
      (integrable_condExp.const_mul _)
  refine ⟨hΦint.congr hFΦ.symm, ?_⟩
  refine (integral_congr_ae hFΦ).le.trans ?_
  set H : Ω → ℝ := fun ω => (1 / (blockLen B : ℝ)) * ∑ r ∈ Finset.Ico (prefixLen p.β B) (blockLen B),
    (|c1 r ω| + |c2 r ω| + (p.h / (B : ℝ)) * G.indicator (fun ω => |c3 r ω|) ω +
      Cst' * ((r : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ) + δ B * (cPi + δ B))) with hHdef
  have hHint : Integrable H P :=
    (integrable_finsetSum _ fun r _ => ((integrable_condExp.abs.add integrable_condExp.abs).add
      ((integrable_condExp.abs.indicator hGm).const_mul _)).add (integrable_const _)).const_mul _
  have hΦH : Φ ≤ᵐ[P] H := by
    filter_upwards [hall] with ω h
    have hHnn : 0 ≤ H ω := mul_nonneg (by positivity) (Finset.sum_nonneg fun r _ =>
      add_nonneg (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg hlam (Set.indicator_nonneg (fun _ _ => abs_nonneg _) _))) (hb40 r))
    by_cases hω : ω ∈ 𝔈
    · rw [hΦdef, Set.indicator_of_mem hω, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (blockLen B : ℝ))]
      refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun r hr => ?_)) (by positivity)
      have hrL := (Finset.mem_Ico.1 hr).2
      have h4 := (h r hrL).2 hω
      rw [Set.indicator_of_mem (h𝔈G hω)]
      have ha := abs_add_le (c1 r ω + c2 r ω + (p.h / (B : ℝ)) * c3 r ω) ((p.h / (B : ℝ)) * c4 r ω)
      have hb := abs_add_le (c1 r ω + c2 r ω) ((p.h / (B : ℝ)) * c3 r ω)
      have hc := abs_add_le (c1 r ω) (c2 r ω)
      rw [abs_mul, abs_of_nonneg hlam] at ha hb
      linarith
    · rw [hΦdef, Set.indicator_of_notMem hω]
      exact hHnn
  refine (integral_mono_ae hΦint hHint hΦH).trans ?_
  have hHeq : ∫ ω, H ω ∂P = (1 / (blockLen B : ℝ)) * ∑ r ∈ Finset.Ico (prefixLen p.β B) (blockLen B),
      (∫ ω, |c1 r ω| ∂P + ∫ ω, |c2 r ω| ∂P + (p.h / (B : ℝ)) * ∫ ω, G.indicator (fun ω => |c3 r ω|) ω ∂P +
        Cst' * ((r : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ) + δ B * (cPi + δ B))) := by
    rw [hHdef, integral_const_mul, integral_finsetSum _ fun r _ => ((integrable_condExp.abs.add
      integrable_condExp.abs).add ((integrable_condExp.abs.indicator hGm).const_mul _)).add (integrable_const _)]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [integral_add ((integrable_condExp.abs.add integrable_condExp.abs).add
        ((integrable_condExp.abs.indicator hGm).const_mul _)) (integrable_const _),
      integral_add (integrable_condExp.abs.add integrable_condExp.abs)
        ((integrable_condExp.abs.indicator hGm).const_mul _),
      integral_add integrable_condExp.abs integrable_condExp.abs, integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul]
    rfl
  rw [hHeq]
  set X : ℝ := cPi' * (KT' * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ)) +
    cPi' * (K2 * Real.sqrt (B : ℝ) * (blockLen B : ℝ) * p.β ^ prefixLen p.β B) +
    Ktr' * ((blockLen B : ℝ) / Real.sqrt (B : ℝ) + omegaBeta p.β ((prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ))
      + p.β ^ prefixLen p.β B + Real.sqrt (B : ℝ) * (blockLen B : ℝ) * p.β ^ prefixLen p.β B) +
    Cst' * ((blockLen B : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ) + δ B * (cPi + δ B)) with hXdef
  have hq0 : 0 ≤ p.β ^ prefixLen p.β B := pow_nonneg hβ0 _
  have hA1 : 0 ≤ (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ) := by positivity
  have hA2 : 0 ≤ (blockLen B : ℝ) / Real.sqrt (B : ℝ) := by positivity
  have hA3 : 0 ≤ 1 / (B : ℝ) := by positivity
  have hA4 : 0 ≤ δ B * (cPi + δ B) := mul_nonneg hδ0B (add_nonneg hcPi hδ0B)
  have hA7 : 0 ≤ Real.sqrt (B : ℝ) * (blockLen B : ℝ) * p.β ^ prefixLen p.β B := by positivity
  have hper : ∀ r ∈ Finset.Ico (prefixLen p.β B) (blockLen B),
      ∫ ω, |c1 r ω| ∂P + ∫ ω, |c2 r ω| ∂P + (p.h / (B : ℝ)) * ∫ ω, G.indicator (fun ω => |c3 r ω|) ω ∂P +
        Cst' * ((r : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ) + δ B * (cPi + δ B)) ≤ X := by
    intro r hr
    obtain ⟨hqr, hrL⟩ := Finset.mem_Ico.1 hr
    obtain ⟨-, -, k1, k2, k3⟩ := key r hrL
    have hrL' : (r : ℝ) ≤ blockLen B := by exact_mod_cast hrL.le
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have hpow : p.β ^ (r + 1) ≤ p.β ^ prefixLen p.β B := pow_le_pow_of_le_one hβ0 p.hβ.2.le (by omega)
    have hpowL : p.β ^ (r + 1) ≤ (blockLen B : ℝ) * p.β ^ prefixLen p.β B :=
      hpow.trans (le_mul_of_one_le_left hq0 hL1r)
    have hrpow : (r : ℝ) * p.β ^ (r + 1) ≤ (blockLen B : ℝ) * p.β ^ prefixLen p.β B :=
      mul_le_mul hrL' hpow (pow_nonneg hβ0 _) hLr.le
    have hrB : (r : ℝ) / Real.sqrt (B : ℝ) ≤ (blockLen B : ℝ) / Real.sqrt (B : ℝ) :=
      div_le_div_of_nonneg_right hrL' hsB.le
    have t1 : cPi' * (KT' * (r : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ)) ≤
        cPi' * (KT' * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrL' 2) hKT0) hlog) hsB.le) hcPi0'
    have t2 : cPi' * (K2 * Real.sqrt (B : ℝ) * p.β ^ (r + 1)) ≤
        cPi' * (K2 * Real.sqrt (B : ℝ) * (blockLen B : ℝ) * p.β ^ prefixLen p.β B) := by
      have := mul_le_mul_of_nonneg_left hpowL (mul_nonneg hK20 hsB.le)
      refine mul_le_mul_of_nonneg_left ?_ hcPi0'
      calc K2 * Real.sqrt (B : ℝ) * p.β ^ (r + 1) ≤ K2 * Real.sqrt (B : ℝ) *
            ((blockLen B : ℝ) * p.β ^ prefixLen p.β B) := this
        _ = _ := by ring
    have hY0 : 0 ≤ (r : ℝ) / Real.sqrt (B : ℝ) + omegaBeta p.β ((prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ))
        + p.β ^ prefixLen p.β B + Real.sqrt (B : ℝ) * (r : ℝ) * p.β ^ (r + 1) := by
      have := pow_nonneg hβ0 (r + 1); positivity
    have t3 : (p.h / (B : ℝ)) * ∫ ω, G.indicator (fun ω => |c3 r ω|) ω ∂P ≤
        Ktr' * ((blockLen B : ℝ) / Real.sqrt (B : ℝ) + omegaBeta p.β ((prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ))
          + p.β ^ prefixLen p.β B + Real.sqrt (B : ℝ) * (blockLen B : ℝ) * p.β ^ prefixLen p.β B) := by
      refine k3.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hY0).trans
        (mul_le_mul_of_nonneg_left ?_ hKtr0))
      have h7 : Real.sqrt (B : ℝ) * (r : ℝ) * p.β ^ (r + 1) ≤
          Real.sqrt (B : ℝ) * (blockLen B : ℝ) * p.β ^ prefixLen p.β B := by
        have := mul_le_mul_of_nonneg_left hrpow hsB.le
        calc _ = Real.sqrt (B : ℝ) * ((r : ℝ) * p.β ^ (r + 1)) := by ring
          _ ≤ Real.sqrt (B : ℝ) * ((blockLen B : ℝ) * p.β ^ prefixLen p.β B) := this
          _ = _ := by ring
      linarith
    have t4 : Cst' * ((r : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ) + δ B * (cPi + δ B)) ≤
        Cst' * ((blockLen B : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ) + δ B * (cPi + δ B)) :=
      mul_le_mul_of_nonneg_left (by linarith) hCst0
    rw [hXdef]
    linarith [k1.trans t1, k2.trans t2]
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    have := mul_nonneg hcPi0' (div_nonneg (mul_nonneg (mul_nonneg hKT0 (sq_nonneg (blockLen B : ℝ))) hlog) hsB.le)
    have := mul_nonneg hcPi0' (mul_nonneg (mul_nonneg (mul_nonneg hK20 hsB.le) hLr.le) hq0)
    have := mul_nonneg hKtr0 (add_nonneg (add_nonneg (add_nonneg hA2 hOm0) hq0) hA7)
    have := mul_nonneg hCst0 (add_nonneg (add_nonneg hA2 hA3) hA4)
    linarith
  have hcard : (((Finset.Ico (prefixLen p.β B) (blockLen B)).card : ℕ) : ℝ) ≤ (blockLen B : ℝ) := by
    rw [Nat.card_Ico]; exact_mod_cast Nat.sub_le _ _
  calc (1 / (blockLen B : ℝ)) * ∑ r ∈ Finset.Ico (prefixLen p.β B) (blockLen B),
        (∫ ω, |c1 r ω| ∂P + ∫ ω, |c2 r ω| ∂P + (p.h / (B : ℝ)) * ∫ ω, G.indicator (fun ω => |c3 r ω|) ω ∂P +
          Cst' * ((r : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ) + δ B * (cPi + δ B)))
      ≤ (1 / (blockLen B : ℝ)) * ∑ r ∈ Finset.Ico (prefixLen p.β B) (blockLen B), X :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = (1 / (blockLen B : ℝ)) * (((Finset.Ico (prefixLen p.β B) (blockLen B)).card : ℕ) * X) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 / (blockLen B : ℝ)) * ((blockLen B : ℝ) * X) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hX0) (by positivity)
    _ = X := by field_simp
    _ ≤ responseRho p (cPi' * KT' + cPi' * K2 + Ktr' + Cst') cPi δ B := by
        unfold responseRho
        rw [hXdef]
        have e1 := mul_nonneg (mul_nonneg hcPi0' hKT0)
          (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg hA2 hA3) hA4) hOm0) hq0) hA7)
        have e2 := mul_nonneg (mul_nonneg hcPi0' hK20)
          (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg hA1 hA2) hA3) hA4) hOm0) hq0)
        have e3 := mul_nonneg hKtr0 (add_nonneg (add_nonneg hA1 hA3) hA4)
        have e4 := mul_nonneg hCst0 (add_nonneg (add_nonneg (add_nonneg hA1 hOm0) hq0) hA7)
        have r1 : cPi' * (KT' * (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ)) =
            cPi' * KT' * ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ)) := by ring
        have r2 : cPi' * (K2 * Real.sqrt (B : ℝ) * (blockLen B : ℝ) * p.β ^ prefixLen p.β B) =
            cPi' * K2 * (Real.sqrt (B : ℝ) * (blockLen B : ℝ) * p.β ^ prefixLen p.β B) := by ring
        rw [r1, r2]
        nlinarith [e1, e2, e3, e4]

/-! ## `prop:app-dyn-response` -/

/-- `prop:app-dyn-response` (cr-2026-10-23), bound. Let `δ_B ↓ 0` be a deterministic sequence (`δ : ℕ → ℝ`,
`Antitone δ`, `δ → 0`). Let `t ≥ 𝗊`, `Π_t` be determined by `𝓕_t` with `‖Π_t‖_F, ‖Π_t‖ ≤ c_Π`, and
`𝔈_t = {t < τ⁺, δ(Δ_t) ≤ δ_B}`. Then
`𝔼[𝟙_{𝔈_t} |(1/L) ∑_{r=𝗊}^{L-1} ⟨Π_t, 𝔼_t 𝖲_{t+r} − V̄(Δ_t)⟩|] ≤ ρ_B` with `ρ_B = responseRho` (the constant `K`
is chosen before the dimensions). `V̄(Δ_t)` is `dynVbar`. The integrability of the indicator-weighted absolute value is a
conjunct. Statement verbatim from `section.tex` (ll. 1966–1977):
```latex
\begin{proposition}[Post-prefix response]\label{prop:app-dyn-response}
Let $\delta_B\downarrow0$ be a deterministic sequence. Let $t\ge\mathsf q$, let
$\Pi_t$ be determined by $\cF_t$ with $\norm{\Pi_t}_\F,\norm{\Pi_t}\le c_\Pi$,
and let $\mathfrak E_t\defeq\{t<\tau^+,\ \delta(\Dt)\le\delta_B\}$. Then
\[
\EE\Big[\mathbf 1_{\mathfrak E_t}\Big|\frac1L\sum_{r=\mathsf q}^{L-1}\big\langle\Pi_t,\EE_t{\mathsf S}_{t+r}-\overline V(\Dt)\big\rangle\Big|\Big]\le\rho_B,
\]
\[
\rho_B\defeq C\Big\{\frac{L^2\log(2B)}{\sqrt B}+\frac{L}{\sqrt B}+\frac1B+\delta_B(c_\Pi+\delta_B)+\Omega_\bmom(\epsilon_B)+\bmom^{\mathsf q}+\sqrt B\,L\bmom^{\mathsf q}\Big\},
\]
and $\rho_B\to0$.
\end{proposition}
```
-/
theorem prop_app_dyn_response_i (certQ : Muon.External.GaussianQuadFormLp) (certOp : Muon.External.GaussianOpNormL6) (certP : Muon.External.GaussianPoincare) (p : DynParams) (cPi : ℝ) (δ : ℕ → ℝ) (hδ : Antitone δ)
    (hδ0 : Tendsto δ atTop (𝓝 0)) :
    ∃ B0 : ℕ, ∃ K : ℝ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (m n B : ℕ) (S : DynSetup p P m n B) (t : ℕ) (Pt : Ω → Mat m n),
        B0 ≤ B → prefixLen p.β B ≤ t →
        (∀ ω, fro (Pt ω) ≤ cPi ∧ opNorm (Pt ω) ≤ cPi) →
        (∀ i j, Measurable[dynPast S t] (fun ω => Pt ω i j)) →
          Integrable ({ω | (t : ℕ∞) < tauPlus p S ω ∧ diffuseness S.C (dynDelta S t ω) ≤ δ B}.indicator
            (fun ω => |((1 / (blockLen B : ℝ)) * ∑ r ∈ Finset.Ico (prefixLen p.β B) (blockLen B),
              frobIP (Pt ω) (Muon.Foundations.condExpMat (dynPast S t) P (dynUpd S (t + r)) ω
                - dynVbar p S t (dynDelta S t ω)))|)) P ∧
          ∫ ω, {ω | (t : ℕ∞) < tauPlus p S ω ∧ diffuseness S.C (dynDelta S t ω) ≤ δ B}.indicator
            (fun ω => |((1 / (blockLen B : ℝ)) * ∑ r ∈ Finset.Ico (prefixLen p.β B) (blockLen B),
              frobIP (Pt ω) (Muon.Foundations.condExpMat (dynPast S t) P (dynUpd S (t + r)) ω
                - dynVbar p S t (dynDelta S t ω)))|) ω ∂P
            ≤ responseRho p K cPi δ B := by
  exact rs_main certQ certOp certP p cPi δ hδ hδ0

private lemma response_beta_pow_q (β : ℝ) (hβ : 0 ≤ β ∧ β < 1) (B : ℕ) (hB : 1 ≤ B) :
    β ^ prefixLen β B ≤ ((2 * (B : ℝ)) ^ 2)⁻¹ := by
  obtain ⟨_, _⟩ := prefix_q_ge_log β B hB
  by_cases h0 : β = 0
  · subst h0
    rw [zero_pow (by omega)]
    positivity
  have hpos : 0 < β := lt_of_le_of_ne hβ.1 (Ne.symm h0)
  have hlogneg : Real.log β < 0 := Real.log_neg hpos hβ.2
  have hlog1 : 0 < Real.log (1 / β) := Real.log_pos (by rw [lt_div_iff₀ hpos]; linarith [hβ.2])
  have hC : 2 / Real.log (1 / β) ≤ C0 β := by
    unfold C0; rw [if_neg h0]; exact le_max_right _ _
  have hL2 : 0 < Real.log (2 * (B : ℝ)) := Real.log_pos (by
    have : (1 : ℝ) ≤ B := by exact_mod_cast hB
    linarith)
  have hq : (prefixLen β B : ℝ) ≥ C0 β * Real.log (2 * (B : ℝ)) := Nat.le_ceil _
  have h2 : 2 * Real.log (2 * (B : ℝ)) ≤ (prefixLen β B : ℝ) * Real.log (1 / β) := by
    have : 2 / Real.log (1 / β) * Real.log (2 * (B : ℝ)) ≤ (prefixLen β B : ℝ) :=
      (mul_le_mul_of_nonneg_right hC hL2.le).trans hq
    rw [div_mul_eq_mul_div, div_le_iff₀ hlog1] at this
    exact this
  have hlogβ : Real.log (1 / β) = -Real.log β := by
    rw [one_div, Real.log_inv]
  have hexp : β ^ prefixLen β B = Real.exp ((prefixLen β B : ℝ) * Real.log β) := by
    rw [Real.exp_nat_mul, Real.exp_log hpos]
  have h3 : β ^ prefixLen β B ≤ Real.exp (-(2 * Real.log (2 * (B : ℝ)))) := by
    rw [hexp]
    apply Real.exp_le_exp.mpr
    rw [hlogβ] at h2
    linarith
  have h4 : Real.exp (-(2 * Real.log (2 * (B : ℝ)))) = ((2 * (B : ℝ)) ^ 2)⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    rw [show 2 * Real.log (2 * (B : ℝ)) = ((2 : ℕ) : ℝ) * Real.log (2 * (B : ℝ)) by norm_num,
      Real.exp_nat_mul, Real.exp_log (by
        have : (1 : ℝ) ≤ B := by exact_mod_cast hB
        linarith)]
  rw [← h4]
  exact h3

private lemma response_v_facts (B : ℕ) (hB : 1 ≤ B) :
    let v := (B : ℝ) ^ ((1 : ℝ) / 16)
    1 ≤ v ∧ (B : ℝ) = v ^ 16 ∧ Real.sqrt (B : ℝ) = v ^ 8 ∧
      (blockLen B : ℝ) ≤ v ^ 2 ∧ Real.log (2 * (B : ℝ)) ≤ 1 + 16 * v := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  set v : ℝ := (B : ℝ) ^ ((1 : ℝ) / 16) with hv
  have hv1 : 1 ≤ v := by
    rw [hv]
    exact Real.one_le_rpow hB1 (by norm_num)
  have hvpos : 0 < v := lt_of_lt_of_le zero_lt_one hv1
  have hvB : (B : ℝ) = v ^ 16 := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hv8 : (B : ℝ) ^ ((1 : ℝ) / 8) = v ^ 2 := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hsqrt : Real.sqrt (B : ℝ) = v ^ 8 := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (pow_nonneg hvpos.le 8)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg B)]
    nlinarith [hvB]
  have hL : (blockLen B : ℝ) ≤ v ^ 2 := by
    unfold blockLen
    rw [← hv8]
    exact_mod_cast Nat.floor_le (by positivity : 0 ≤ (B : ℝ) ^ ((1 : ℝ) / 8))
  have hlogv : Real.log v ≤ v - 1 := Real.log_le_sub_one_of_pos hvpos
  have hlogB : Real.log (B : ℝ) = 16 * Real.log v := by
    rw [hvB, Real.log_pow]; push_cast; ring
  have hlog2 : Real.log 2 < 1 := by
    linarith [Real.log_two_lt_d9]
  have hlog : Real.log (2 * (B : ℝ)) ≤ 1 + 16 * v := by
    rw [Real.log_mul (by norm_num) (by linarith), hlogB]
    linarith
  exact ⟨hv1, hvB, hsqrt, hL, hlog⟩

set_option maxHeartbeats 1000000 in
private lemma response_terms_le (p : DynParams) :
    ∃ B0 : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ B : ℕ, B0 ≤ B →
      0 ≤ (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ)
          + (blockLen B : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ)
          + omegaBeta p.β ((prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ))
          + p.β ^ prefixLen p.β B
          + Real.sqrt (B : ℝ) * (blockLen B : ℝ) * p.β ^ prefixLen p.β B ∧
      (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ)
          + (blockLen B : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ)
          + omegaBeta p.β ((prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ))
          + p.β ^ prefixLen p.β B
          + Real.sqrt (B : ℝ) * (blockLen B : ℝ) * p.β ^ prefixLen p.β B
        ≤ c * ((B : ℝ) ^ ((1 : ℝ) / 16))⁻¹ := by
  obtain ⟨B0, hB0⟩ := prefix_q_le_L p.β
  obtain ⟨K, hK, _⟩ := lem_app_dyn_prefix_iv p
  set K0 : ℝ := max K 0 with hK0def
  have hK0 : 0 ≤ K0 := le_max_right _ _
  refine ⟨B0, 21 + 9 * K0, by positivity, ?_⟩
  intro B hBge
  obtain ⟨hB, hqLnat⟩ := hB0 B hBge
  obtain ⟨hv1, hvB, hsqrt, hLv, hlog⟩ := response_v_facts B hB
  set v : ℝ := (B : ℝ) ^ ((1 : ℝ) / 16) with hvdef
  have hvpos : 0 < v := lt_of_lt_of_le zero_lt_one hv1
  have hL0 : 0 ≤ (blockLen B : ℝ) := Nat.cast_nonneg _
  have hq0 : 0 ≤ (prefixLen p.β B : ℝ) := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.log (2 * (B : ℝ)) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ B := by exact_mod_cast hB
    linarith)
  have hlog17 : Real.log (2 * (B : ℝ)) ≤ 17 * v := by linarith
  have hLsq : (blockLen B : ℝ) ^ 2 ≤ v ^ 4 := by
    convert pow_le_pow_left₀ hL0 hLv 2 using 1 <;> ring
  have hnum : (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) ≤ 17 * v ^ 5 := by
    calc
      _ ≤ v ^ 4 * (17 * v) := mul_le_mul hLsq hlog17 hlog0 (pow_nonneg hvpos.le 4)
      _ = 17 * v ^ 5 := by ring
  have ht1 : (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ) ≤
      17 * (1 / v) := by
    rw [hsqrt]
    calc
      _ ≤ (17 * v ^ 5) / v ^ 8 := div_le_div_of_nonneg_right hnum (pow_nonneg hvpos.le 8)
      _ = 17 * (1 / v ^ 3) := by field_simp
      _ ≤ 17 * (1 / v) := mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le hvpos (le_self_pow₀ hv1 (by norm_num : (3 : ℕ) ≠ 0))) (by norm_num)
  have hv2v7 : v ^ 2 ≤ v ^ 7 := pow_le_pow_right₀ hv1 (by omega)
  have ht2 : (blockLen B : ℝ) / Real.sqrt (B : ℝ) ≤ 1 / v := by
    rw [hsqrt, div_le_iff₀ (pow_pos hvpos 8)]
    calc
      (blockLen B : ℝ) ≤ v ^ 7 := hLv.trans hv2v7
      _ = (1 / v) * v ^ 8 := by field_simp
  have hvv16 : v ≤ v ^ 16 := le_self_pow₀ hv1 (by norm_num)
  have ht3 : 1 / (B : ℝ) ≤ 1 / v := by
    rw [hvB]
    exact one_div_le_one_div_of_le hvpos hvv16
  have hq1nat : 1 ≤ prefixLen p.β B := (prefix_q_ge_log p.β B hB).2
  have hq1 : (1 : ℝ) ≤ prefixLen p.β B := by exact_mod_cast hq1nat
  have hqL : (prefixLen p.β B : ℝ) ≤ blockLen B := by exact_mod_cast hqLnat
  set ε : ℝ := (prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact div_pos (lt_of_lt_of_le zero_lt_one hq1) (by rw [hsqrt]; positivity)
  have hεlower : 1 / v ^ 8 ≤ ε := by
    rw [hεdef, hsqrt]
    exact div_le_div_of_nonneg_right hq1 (pow_nonneg hvpos.le 8)
  have hεupper : ε ≤ 1 / v ^ 6 := by
    rw [hεdef, hsqrt, div_le_iff₀ (pow_pos hvpos 8)]
    calc
      (prefixLen p.β B : ℝ) ≤ v ^ 2 := hqL.trans hLv
      _ = (1 / v ^ 6) * v ^ 8 := by field_simp
  have hv6 : 1 ≤ v ^ 6 := one_le_pow₀ hv1
  have hε1 : ε ≤ 1 := hεupper.trans (by
    simpa only [div_eq_mul_inv, one_mul] using (inv_le_one₀ (by positivity : 0 < v ^ 6)).2 hv6)
  have hinvε : 1 / ε ≤ v ^ 8 := by
    have := one_div_le_one_div_of_le (by positivity : 0 < 1 / v ^ 8) hεlower
    convert this using 1 <;> field_simp
  have hlogε0 : 0 ≤ Real.log (1 / ε) := by
    rw [one_div, Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hεpos.le hε1)
  have hlogε : Real.log (1 / ε) ≤ 8 * v := by
    calc
      Real.log (1 / ε) ≤ Real.log (v ^ 8) := Real.log_le_log (by positivity) hinvε
      _ = 8 * Real.log v := by rw [Real.log_pow]; norm_num
      _ ≤ 8 * v := by nlinarith [Real.log_le_sub_one_of_pos hvpos]
  have hfac0 : 0 ≤ 1 + Real.log (1 / ε) := by linarith
  have hfac : 1 + Real.log (1 / ε) ≤ 9 * v := by linarith
  have hεfac : ε * (1 + Real.log (1 / ε)) ≤ 9 * (1 / v) := by
    calc
      _ ≤ (1 / v ^ 6) * (9 * v) := mul_le_mul hεupper hfac hfac0 (by positivity)
      _ = 9 * (1 / v ^ 5) := by field_simp
      _ ≤ 9 * (1 / v) := mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le hvpos (le_self_pow₀ hv1 (by norm_num : (5 : ℕ) ≠ 0))) (by norm_num)
  have hOm0 : 0 ≤ omegaBeta p.β ε := tsum_nonneg fun r =>
    le_min hεpos.le (pow_nonneg p.hβ.1 _)
  have hOm : omegaBeta p.β ε ≤ (9 * K0) * (1 / v) := by
    calc
      omegaBeta p.β ε ≤ K * ε * (1 + Real.log (1 / ε)) := hK ε hεpos hε1
      _ ≤ K0 * ε * (1 + Real.log (1 / ε)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left K 0) hεpos.le) hfac0
      _ ≤ K0 * (9 * (1 / v)) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hεfac hK0
      _ = (9 * K0) * (1 / v) := by ring
  have hpowB : p.β ^ prefixLen p.β B ≤ ((B : ℝ))⁻¹ := by
    refine (response_beta_pow_q p.β p.hβ B hB).trans ?_
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
    nlinarith
  have ht5 : p.β ^ prefixLen p.β B ≤ 1 / v := by
    exact hpowB.trans (by simpa only [one_div] using ht3)
  have hdec : v ^ 8 * v ^ 2 * (v ^ 16)⁻¹ ≤ 1 / v := by
    rw [← div_eq_mul_inv, div_le_iff₀ (pow_pos hvpos 16)]
    calc
      v ^ 8 * v ^ 2 = v ^ 10 := by ring
      _ ≤ v ^ 15 := pow_le_pow_right₀ hv1 (by omega)
      _ = (1 / v) * v ^ 16 := by field_simp
  have ht6 : Real.sqrt (B : ℝ) * (blockLen B : ℝ) * p.β ^ prefixLen p.β B ≤ 1 / v := by
    calc
      _ ≤ Real.sqrt (B : ℝ) * (blockLen B : ℝ) * ((B : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hpowB (mul_nonneg (Real.sqrt_nonneg _) hL0)
      _ ≤ v ^ 8 * v ^ 2 * (v ^ 16)⁻¹ := by
        rw [hsqrt, hvB]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLv (pow_nonneg hvpos.le 8)) (inv_nonneg.mpr (pow_nonneg hvpos.le 16))
      _ ≤ 1 / v := hdec
  have hnonneg : 0 ≤
      (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ)
        + (blockLen B : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ)
        + omegaBeta p.β ((prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ))
        + p.β ^ prefixLen p.β B
        + Real.sqrt (B : ℝ) * (blockLen B : ℝ) * p.β ^ prefixLen p.β B := by
    have ht10 : 0 ≤ (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ) :=
      div_nonneg (mul_nonneg (sq_nonneg _) hlog0) (Real.sqrt_nonneg _)
    have ht20 : 0 ≤ (blockLen B : ℝ) / Real.sqrt (B : ℝ) :=
      div_nonneg hL0 (Real.sqrt_nonneg _)
    have ht30 : 0 ≤ 1 / (B : ℝ) := by positivity
    have ht50 : 0 ≤ p.β ^ prefixLen p.β B := pow_nonneg p.hβ.1 _
    have ht60 : 0 ≤ Real.sqrt (B : ℝ) * (blockLen B : ℝ) * p.β ^ prefixLen p.β B := by
      positivity
    rw [← hεdef]
    nlinarith
  refine ⟨hnonneg, ?_⟩
  rw [show ((B : ℝ) ^ ((1 : ℝ) / 16))⁻¹ = 1 / v by simp only [hvdef, one_div]]
  nlinarith

/-- `prop:app-dyn-response` (cr-2026-10-23), the limit `ρ_B → 0`, for every constant `K`. The sequence
`B ↦ responseRho p K cPi δ B` is the `ρ_B` of part (i). Statement verbatim from `section.tex` (ll. 1966–1977):
```latex
\begin{proposition}[Post-prefix response]\label{prop:app-dyn-response}
Let $\delta_B\downarrow0$ be a deterministic sequence. Let $t\ge\mathsf q$, let
$\Pi_t$ be determined by $\cF_t$ with $\norm{\Pi_t}_\F,\norm{\Pi_t}\le c_\Pi$,
and let $\mathfrak E_t\defeq\{t<\tau^+,\ \delta(\Dt)\le\delta_B\}$. Then
\[
\EE\Big[\mathbf 1_{\mathfrak E_t}\Big|\frac1L\sum_{r=\mathsf q}^{L-1}\big\langle\Pi_t,\EE_t{\mathsf S}_{t+r}-\overline V(\Dt)\big\rangle\Big|\Big]\le\rho_B,
\]
\[
\rho_B\defeq C\Big\{\frac{L^2\log(2B)}{\sqrt B}+\frac{L}{\sqrt B}+\frac1B+\delta_B(c_\Pi+\delta_B)+\Omega_\bmom(\epsilon_B)+\bmom^{\mathsf q}+\sqrt B\,L\bmom^{\mathsf q}\Big\},
\]
and $\rho_B\to0$.
\end{proposition}
```
-/
theorem prop_app_dyn_response_ii (certQ : Muon.External.GaussianQuadFormLp) (certOp : Muon.External.GaussianOpNormL6) (certP : Muon.External.GaussianPoincare) (p : DynParams) (cPi : ℝ) (δ : ℕ → ℝ) (hδ : Antitone δ)
    (hδ0 : Tendsto δ atTop (𝓝 0)) :
    ∀ K : ℝ, Tendsto (fun B : ℕ => responseRho p K cPi δ B) atTop (𝓝 0) := by
  intro K
  let X : ℕ → ℝ := fun B =>
    (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ)
      + (blockLen B : ℝ) / Real.sqrt (B : ℝ) + 1 / (B : ℝ)
      + omegaBeta p.β ((prefixLen p.β B : ℝ) / Real.sqrt (B : ℝ))
      + p.β ^ prefixLen p.β B
      + Real.sqrt (B : ℝ) * (blockLen B : ℝ) * p.β ^ prefixLen p.β B
  obtain ⟨B0, c, hc, hXbd⟩ := response_terms_le p
  have hv : Tendsto (fun B : ℕ => (B : ℝ) ^ ((1 : ℝ) / 16)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun B : ℕ => ((B : ℝ) ^ ((1 : ℝ) / 16))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hv
  have hupper : Tendsto (fun B : ℕ => c * ((B : ℝ) ^ ((1 : ℝ) / 16))⁻¹) atTop (𝓝 0) := by
    simpa using hinv.const_mul c
  have hXt : Tendsto X atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
    · filter_upwards [eventually_ge_atTop B0] with B hB
      exact (hXbd B hB).1
    · filter_upwards [eventually_ge_atTop B0] with B hB
      exact (hXbd B hB).2
  have hδt : Tendsto (fun B : ℕ => δ B * (cPi + δ B)) atTop (𝓝 0) := by
    simpa using hδ0.mul (tendsto_const_nhds.add hδ0)
  have ht := (hXt.add hδt).const_mul K
  convert ht using 1
  · funext B
    unfold responseRho X
    ring
  · ring

end Muon.Dynamics

end

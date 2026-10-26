import Mathlib
import Muon.SignSGD.HalfVolatility

/-!
# Appendix I (SignSGD): fourth moments of sums, column norms, the corrected row volatility and the
half-anisotropic recursion (task L-I.11)

Interface for work package L-I.11 (card `sections/08-signsgd/CARD.md` §3 rows 28–31, §5 row L-I.11).
Source of record: snapshot `cr-2026-10-23`, `sections/08-signsgd/section.tex`. Labels:
`lem:app-sgd-partition` (l. 1197–1209), `lem:app-sgd-column-norm` (l. 1242–1248),
`thm:app-sgd-modes` (l. 1292–1312, split into four declarations `_i`…`_iv`) and
`prop:signsgd-recursion-anisotropic` (l. 1353–1367). Docstrings carry the LaTeX statements verbatim
(copied by script from `section.tex`).

Choices:
* Haar measure: a probability `ν` on `O(n)` with `Muon.Foundations.IsOrthHaar ν` (coordinator Q1).
  Joint expectations over `(U, batch)` use `ν.prod (batchLaw n m B)`. `lem_app_sgd_column_norm`
  integrates over the batch alone, since `hCol` is a function of the batch (`H` independent of `U`,
  coordinator Q2).
* `lem_app_sgd_partition` lives on an abstract probability space `Ω : Type`: `Zs b` are i.i.d. copies
  of `Z` (`iIndepFun`, `IdentDistrib`). The hypotheses on `Z` are the centring, the covariance `V`, the
  moments of `eqn:app-sgd-dir` and `eqn:app-sgd-vec` with constants `A4, A8 ≥ 0` and dimension `n`
  (clarifying correction, card §6.9). The two-sided sums `S_s`, `W`, `𝒟_B` are helper defs.
* Admissible constants: `∀ P : HaarParams, ∃ C, …`, with `C` chosen after `P` and before the
  dimensions, the state and the Haar measure.
* Moments of nonnegative quantities are `∫⁻` of `ENNReal.ofReal`. Real-valued expectations are Bochner
  integrals, each accompanied by an `Integrable` conjunct so that no junk value satisfies a bound.
* Lean division is `x / 0 = 0`. The a.s. definedness of the ratio in `lem_app_sgd_column_norm` is a
  conjunct. `x₀ = 2ℛ Tr Λ / B` is `haarX0`, with `2ℛ = twoR`.
* `Tr Σout` is written `∑ k, μ k`: `Σout = U Λ Uᵀ` has the same trace for every `U`.
* `𝒬_i(Δ) = ‖Δᵀ u_i‖²` is `sgdRowEnergy` (the form of `Muon.Setup.rowQ`, which needs spectral data
  that the Haar model does not carry). In the Haar model `𝒬_i(UD) = Σ_j D_ij²`, which is the form used on
  the deterministic right-hand sides.
* `vCorr` is `𝔳_i^{corr}` (`eqn:app-sgd-corr`), `haarRawRow` is `𝔳_i^{raw}` (`eqn:app-sgd-actual-row`),
  `haarDcoef` is `𝔡_i = μ_i 𝒩_B / √(π μ̄)`, and `vSgd` (from `HalfVolatility`) is `𝔳_i^{s-SGD}`.
* `prop_signsgd_recursion_anisotropic`: the residuals `E_i` are the explicit differences of the
  displayed identity (card §6.13), and `E_η` is the explicit difference of the risk identity.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace Muon.SignSGD

/-! ## Generic sums of i.i.d. vectors (`lem:app-sgd-partition`) -/

/-- `S_s = Σ_{b ≤ s} Z_b` (l. 1201, first display), for the copies `Zs b` of `Z`. -/
noncomputable def partSum {Ω : Type} {n B : ℕ} (Zs : Fin B → Ω → (Fin n → ℝ)) (s : ℕ) (ω : Ω) :
    Fin n → ℝ :=
  ∑ b ∈ Finset.univ.filter (fun b : Fin B => (b : ℕ) < s), Zs b ω

/-- `𝒲 = Σ_{b ≠ b'} ⟨Z_b, Z_{b'}⟩` (l. 1201, first display). -/
noncomputable def offDiagSum {Ω : Type} {n B : ℕ} (Zs : Fin B → Ω → (Fin n → ℝ)) (ω : Ω) : ℝ :=
  ∑ b : Fin B, ∑ b' ∈ Finset.univ.filter (fun b' : Fin B => b' ≠ b), (Zs b ω ⬝ᵥ Zs b' ω)

/-- `𝒟_B = Σ_b (‖Z_b‖² − Tr V)` (l. 1201, first display). -/
noncomputable def diagDevSum {Ω : Type} {n B : ℕ} (V : Matrix (Fin n) (Fin n) ℝ)
    (Zs : Fin B → Ω → (Fin n → ℝ)) (ω : Ω) : ℝ :=
  ∑ b : Fin B, ((∑ i, Zs b ω i ^ 2) - ∑ i, V i i)

section RVPartitionHelpers

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

private lemma rvp_pw_int {X : Ω → ℝ} (hX : Measurable X) (h4 : Integrable (fun ω => X ω ^ 4) P)
    (k : ℕ) (hk : k ≤ 4) : Integrable (fun ω => X ω ^ k) P := by
  refine Integrable.mono' (h4.add (integrable_const (1 : ℝ))) (hX.pow_const k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_pow, Pi.add_apply]
  have h4' : |X ω| ^ 4 = X ω ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  rw [← h4']
  by_cases h : |X ω| ≤ 1
  · have := pow_le_one₀ (abs_nonneg (X ω)) h (n := k)
    have h0 : 0 ≤ |X ω| ^ 4 := by positivity
    linarith
  · push_neg at h
    have := pow_le_pow_right₀ h.le hk
    linarith

private lemma rvp_ind_pow_mul {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hind : IndepFun X Y P)
    (hX4 : Integrable (fun ω => X ω ^ 4) P) (hY4 : Integrable (fun ω => Y ω ^ 4) P)
    (i j : ℕ) (hi : i ≤ 4) (hj : j ≤ 4) :
    Integrable (fun ω => X ω ^ i * Y ω ^ j) P ∧
      ∫ ω, X ω ^ i * Y ω ^ j ∂P = (∫ ω, X ω ^ i ∂P) * ∫ ω, Y ω ^ j ∂P := by
  constructor
  · have h := (hind.comp (measurable_id.pow_const i) (measurable_id.pow_const j)).integrable_mul
      (rvp_pw_int hX hX4 i hi) (rvp_pw_int hY hY4 j hj)
    exact h
  · exact hind.integral_fun_comp_mul_comp hX.aemeasurable hY.aemeasurable
      (measurable_id.pow_const i).aestronglyMeasurable (measurable_id.pow_const j).aestronglyMeasurable

private lemma rvp_fourth_step {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hind : IndepFun X Y P)
    (hX4 : Integrable (fun ω => X ω ^ 4) P) (hY4 : Integrable (fun ω => Y ω ^ 4) P)
    (hX0 : ∫ ω, X ω ∂P = 0) (hY0 : ∫ ω, Y ω ∂P = 0) :
    Integrable (fun ω => (X ω + Y ω) ^ 4) P ∧
    (∫ ω, (X ω + Y ω) ^ 4 ∂P = ∫ ω, X ω ^ 4 ∂P + 6 * ((∫ ω, X ω ^ 2 ∂P) * ∫ ω, Y ω ^ 2 ∂P)
        + ∫ ω, Y ω ^ 4 ∂P) ∧
    (∫ ω, (X ω + Y ω) ^ 2 ∂P = ∫ ω, X ω ^ 2 ∂P + ∫ ω, Y ω ^ 2 ∂P) := by
  have h31 := rvp_ind_pow_mul hX hY hind hX4 hY4 3 1 (by norm_num) (by norm_num)
  have h22 := rvp_ind_pow_mul hX hY hind hX4 hY4 2 2 (by norm_num) (by norm_num)
  have h13 := rvp_ind_pow_mul hX hY hind hX4 hY4 1 3 (by norm_num) (by norm_num)
  have h11 := rvp_ind_pow_mul hX hY hind hX4 hY4 1 1 (by norm_num) (by norm_num)
  simp only [pow_one] at h31 h13 h11
  rw [hY0, mul_zero] at h31
  rw [hX0, zero_mul] at h13 h11
  have iX2 := rvp_pw_int hX hX4 2 (by norm_num)
  have iY2 := rvp_pw_int hY hY4 2 (by norm_num)
  have e4 : ∀ ω, (X ω + Y ω) ^ 4 = X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) + 6 * (X ω ^ 2 * Y ω ^ 2)
      + 4 * (X ω * Y ω ^ 3) + Y ω ^ 4 := fun ω => by ring
  have e2 : ∀ ω, (X ω + Y ω) ^ 2 = X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2 := fun ω => by ring
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [e4]
    exact (((hX4.add (h31.1.const_mul 4)).add (h22.1.const_mul 6)).add (h13.1.const_mul 4)).add hY4
  · simp_rw [e4]
    rw [integral_add, integral_add, integral_add, integral_add, integral_const_mul,
      integral_const_mul, integral_const_mul, h31.2, h13.2, h22.2]
    · ring
    all_goals first
      | exact hX4
      | exact hY4
      | exact h31.1.const_mul 4
      | exact h22.1.const_mul 6
      | exact h13.1.const_mul 4
      | exact (hX4.add (h31.1.const_mul 4))
      | exact ((hX4.add (h31.1.const_mul 4)).add (h22.1.const_mul 6))
      | exact (((hX4.add (h31.1.const_mul 4)).add (h22.1.const_mul 6)).add (h13.1.const_mul 4))
  · simp_rw [e2]
    rw [integral_add, integral_add, integral_const_mul, h11.2]
    · ring
    all_goals first
      | exact iX2
      | exact iY2
      | exact h11.1.const_mul 2
      | exact (iX2.add (h11.1.const_mul 2))


private lemma rvp_sum_fourth {ι : Type} [DecidableEq ι] {Y : ι → Ω → ℝ} (hmeas : ∀ b, Measurable (Y b))
    (hind : iIndepFun Y P) (h4 : ∀ b, Integrable (fun ω => Y b ω ^ 4) P)
    (h0 : ∀ b, ∫ ω, Y b ω ∂P = 0) (σ m : ℝ) (hσ : ∀ b, ∫ ω, Y b ω ^ 2 ∂P = σ)
    (hm : ∀ b, ∫ ω, Y b ω ^ 4 ∂P = m) (I : Finset ι) :
    Integrable (fun ω => (∑ b ∈ I, Y b ω) ^ 4) P ∧
    (∫ ω, (∑ b ∈ I, Y b ω) ^ 4 ∂P = I.card * m + 3 * I.card * (I.card - 1) * σ ^ 2) ∧
    (∫ ω, (∑ b ∈ I, Y b ω) ^ 2 ∂P = I.card * σ) ∧ (∫ ω, (∑ b ∈ I, Y b ω) ∂P = 0) := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert j I hj ih =>
    obtain ⟨i4, e4, e2, e0⟩ := ih
    have hmT : Measurable (fun ω => ∑ b ∈ I, Y b ω) := Finset.measurable_sum _ (fun b _ => hmeas b)
    have hind' : IndepFun (fun ω => ∑ b ∈ I, Y b ω) (Y j) P := by
      have := hind.indepFun_finsetSum_of_notMem hmeas hj
      simpa [Finset.sum_fn] using this
    obtain ⟨j4, f4, f2⟩ := rvp_fourth_step hmT (hmeas j) hind' i4 (h4 j) e0 (h0 j)
    have es : ∀ ω, ∑ b ∈ insert j I, Y b ω = (∑ b ∈ I, Y b ω) + Y j ω := fun ω => by
      rw [Finset.sum_insert hj, add_comm]
    simp_rw [es]
    refine ⟨j4, ?_, ?_, ?_⟩
    · rw [f4, e4, e2, hσ, hm, Finset.card_insert_of_notMem hj]; push_cast; ring
    · rw [f2, e2, hσ, Finset.card_insert_of_notMem hj]; push_cast; ring
    · have iT : Integrable (fun ω => ∑ b ∈ I, Y b ω) P := by
        refine integrable_finset_sum _ (fun b _ => ?_)
        exact (rvp_pw_int (hmeas b) (h4 b) 1 (by norm_num)).congr (by simp)
      have iY : Integrable (Y j) P := (rvp_pw_int (hmeas j) (h4 j) 1 (by norm_num)).congr (by simp)
      rw [integral_add iT iY, e0, h0 j, add_zero]


private lemma rvp_iid_transfer {n B : ℕ} {Z : Ω → (Fin n → ℝ)} {Zs : Fin B → Ω → (Fin n → ℝ)}
    (hZs : ∀ b, Measurable (Zs b)) (hind : iIndepFun Zs P)
    (hid : ∀ b, IdentDistrib (Zs b) Z P P) {g : (Fin n → ℝ) → ℝ} (hg : Measurable g)
    (g4 : Integrable (fun ω => g (Z ω) ^ 4) P) (g0 : ∫ ω, g (Z ω) ∂P = 0)
    (I : Finset (Fin B)) :
    Integrable (fun ω => (∑ b ∈ I, g (Zs b ω)) ^ 4) P ∧
    (∫ ω, (∑ b ∈ I, g (Zs b ω)) ^ 4 ∂P = I.card * (∫ ω, g (Z ω) ^ 4 ∂P)
      + 3 * I.card * (I.card - 1) * (∫ ω, g (Z ω) ^ 2 ∂P) ^ 2) ∧
    (∫ ω, (∑ b ∈ I, g (Zs b ω)) ^ 2 ∂P = I.card * ∫ ω, g (Z ω) ^ 2 ∂P) := by
  have hY : ∀ k : ℕ, ∀ b, IdentDistrib (fun ω => g (Zs b ω) ^ k) (fun ω => g (Z ω) ^ k) P P :=
    fun k b => (hid b).comp (hg.pow_const k)
  have hY1 : ∀ b, IdentDistrib (fun ω => g (Zs b ω)) (fun ω => g (Z ω)) P P :=
    fun b => (hid b).comp hg
  obtain ⟨a, b, c, _⟩ := rvp_sum_fourth (P := P) (Y := fun b ω => g (Zs b ω))
    (fun b => hg.comp (hZs b)) (hind.comp (fun _ => g) (fun _ => hg))
    (fun b => (hY 4 b).symm.integrable_snd g4) (fun b => by rw [(hY1 b).integral_eq]; exact g0)
    (∫ ω, g (Z ω) ^ 2 ∂P) (∫ ω, g (Z ω) ^ 4 ∂P) (fun b => (hY 2 b).integral_eq)
    (fun b => (hY 4 b).integral_eq) I
  exact ⟨a, b, c⟩


private lemma rvp_meas_dot {n : ℕ} (a : Fin n → ℝ) : Measurable (fun z : Fin n → ℝ => a ⬝ᵥ z) := by
  unfold dotProduct
  fun_prop

private lemma rvp_int_of_lint {f : Ω → ℝ} (hf : Measurable f) (h0 : ∀ ω, 0 ≤ f ω) (c : ℝ) (hc : 0 ≤ c)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal c) : Integrable f P ∧ ∫ ω, f ω ∂P ≤ c := by
  have hfin : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P < ⊤ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hi : Integrable f P := ⟨hf.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall h0)).2 hfin⟩
  refine ⟨hi, ?_⟩
  have := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall h0)
  exact (ENNReal.ofReal_le_ofReal_iff hc).1 (this.symm ▸ h)

private lemma rvp_sq_int_le {f : Ω → ℝ} (hf : Integrable f P) (hf2 : Integrable (fun ω => f ω ^ 2) P) :
    (∫ ω, f ω ∂P) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂P := by
  set c := ∫ ω, f ω ∂P with hc
  have h0 : 0 ≤ ∫ ω, (f ω - c) ^ 2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
  have e : ∀ ω, (f ω - c) ^ 2 = (f ω ^ 2 - 2 * c * f ω) + c ^ 2 := fun ω => by ring
  simp_rw [e] at h0
  have i1 : Integrable (fun ω => f ω ^ 2 - 2 * c * f ω) P := hf2.sub (hf.const_mul _)
  rw [integral_add i1 (integrable_const _), integral_sub hf2
    (hf.const_mul _), integral_const_mul] at h0
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h0
  nlinarith


private lemma rvp_dir_facts {n : ℕ} (A4 : ℝ) (hA4 : 0 ≤ A4) (Z : Ω → (Fin n → ℝ)) (hZ : Measurable Z)
    (hdir4 : ∀ a : Fin n → ℝ,
      ∫⁻ ω, ENNReal.ofReal ((a ⬝ᵥ Z ω) ^ 4) ∂P ≤ ENNReal.ofReal (A4 * (∑ i, a i ^ 2) ^ 2))
    (a : Fin n → ℝ) :
    Integrable (fun ω => (a ⬝ᵥ Z ω) ^ 4) P ∧ ∫ ω, (a ⬝ᵥ Z ω) ^ 4 ∂P ≤ A4 * (∑ i, a i ^ 2) ^ 2 :=
  rvp_int_of_lint (((rvp_meas_dot a).comp hZ).pow_const 4) (fun ω => by positivity) _
    (by positivity) (hdir4 a)

private lemma rvp_dir_zero {n : ℕ} (A4 : ℝ) (hA4 : 0 ≤ A4) (Z : Ω → (Fin n → ℝ)) (hZ : Measurable Z)
    (hcent : ∀ i, ∫ ω, Z ω i ∂P = 0)
    (hdir4 : ∀ a : Fin n → ℝ,
      ∫⁻ ω, ENNReal.ofReal ((a ⬝ᵥ Z ω) ^ 4) ∂P ≤ ENNReal.ofReal (A4 * (∑ i, a i ^ 2) ^ 2))
    (a : Fin n → ℝ) : ∫ ω, (a ⬝ᵥ Z ω) ∂P = 0 := by
  have hi : ∀ i, Integrable (fun ω => Z ω i) P := by
    intro i
    have h := rvp_dir_facts A4 hA4 Z hZ hdir4 (Pi.single i 1)
    have h1 := rvp_pw_int (((rvp_meas_dot (Pi.single i (1:ℝ))).comp hZ)) h.1 1 (by norm_num)
    refine h1.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [single_dotProduct]
  unfold dotProduct
  rw [integral_finsetSum _ (fun i _ => (hi i).const_mul (a i))]
  simp [integral_const_mul, hcent]


private lemma rvp_dir4_gen {n B : ℕ} (A4 : ℝ) (hA4 : 0 ≤ A4) (Z : Ω → (Fin n → ℝ)) (hZ : Measurable Z)
    (hcent : ∀ i, ∫ ω, Z ω i ∂P = 0)
    (hdir4 : ∀ a : Fin n → ℝ,
      ∫⁻ ω, ENNReal.ofReal ((a ⬝ᵥ Z ω) ^ 4) ∂P ≤ ENNReal.ofReal (A4 * (∑ i, a i ^ 2) ^ 2))
    (Zs : Fin B → Ω → (Fin n → ℝ)) (hZs : ∀ b, Measurable (Zs b))
    (hind : iIndepFun Zs P) (hid : ∀ b, IdentDistrib (Zs b) Z P P)
    (a : Fin n → ℝ) (I : Finset (Fin B)) :
    ∫⁻ ω, ENNReal.ofReal ((a ⬝ᵥ ∑ b ∈ I, Zs b ω) ^ 4) ∂P
      ≤ ENNReal.ofReal (3 * A4 * (I.card : ℝ) ^ 2 * (∑ i, a i ^ 2) ^ 2) := by
  obtain ⟨i4, m4⟩ := rvp_dir_facts A4 hA4 Z hZ hdir4 a
  have h0 := rvp_dir_zero A4 hA4 Z hZ hcent hdir4 a
  obtain ⟨j4, f4, -⟩ := rvp_iid_transfer (P := P) hZs hind hid (rvp_meas_dot a) i4 h0 I
  have iZ2 : Integrable (fun ω => (a ⬝ᵥ Z ω) ^ 2) P := rvp_pw_int ((rvp_meas_dot a).comp hZ) i4 2 (by norm_num)
  have hs : (∫ ω, (a ⬝ᵥ Z ω) ^ 2 ∂P) ^ 2 ≤ ∫ ω, (a ⬝ᵥ Z ω) ^ 4 ∂P := by
    have := rvp_sq_int_le (f := fun ω => (a ⬝ᵥ Z ω) ^ 2) iZ2 (by simpa [← pow_mul] using i4)
    simpa [← pow_mul] using this
  have hm0 : 0 ≤ ∫ ω, (a ⬝ᵥ Z ω) ^ 4 ∂P := integral_nonneg (fun ω => by positivity)
  have e : ∀ ω, (a ⬝ᵥ ∑ b ∈ I, Zs b ω) = ∑ b ∈ I, (a ⬝ᵥ Zs b ω) := fun ω => by
    rw [dotProduct_sum]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal j4 (Filter.Eventually.of_forall fun ω => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [f4]
  set k : ℝ := (I.card : ℝ)
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hk1 : 0 ≤ k * (k - 1) := by
    rcases Nat.eq_zero_or_pos I.card with h | h
    · simp [k, h]
    · have : (1 : ℝ) ≤ k := by
        show (1 : ℝ) ≤ (I.card : ℝ)
        exact_mod_cast Nat.one_le_iff_ne_zero.2 h.ne'
      nlinarith
  set m := ∫ ω, (a ⬝ᵥ Z ω) ^ 4 ∂P
  set σ := ∫ ω, (a ⬝ᵥ Z ω) ^ 2 ∂P
  have : 3 * k * (k - 1) * σ ^ 2 ≤ 3 * k * (k - 1) * (A4 * (∑ i, a i ^ 2) ^ 2) := by
    apply mul_le_mul_of_nonneg_left (hs.trans m4)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left m4 hk]


private lemma rvp_vec4_gen {n B : ℕ} (A4 : ℝ) (hA4 : 0 ≤ A4) (Z : Ω → (Fin n → ℝ)) (hZ : Measurable Z)
    (hcent : ∀ i, ∫ ω, Z ω i ∂P = 0)
    (hdir4 : ∀ a : Fin n → ℝ,
      ∫⁻ ω, ENNReal.ofReal ((a ⬝ᵥ Z ω) ^ 4) ∂P ≤ ENNReal.ofReal (A4 * (∑ i, a i ^ 2) ^ 2))
    (Zs : Fin B → Ω → (Fin n → ℝ)) (hZs : ∀ b, Measurable (Zs b))
    (hind : iIndepFun Zs P) (hid : ∀ b, IdentDistrib (Zs b) Z P P)
    (I : Finset (Fin B)) :
    ∫⁻ ω, ENNReal.ofReal ((∑ i, (∑ b ∈ I, Zs b ω i) ^ 2) ^ 2) ∂P
      ≤ ENNReal.ofReal (3 * A4 * (I.card : ℝ) ^ 2 * (n : ℝ) ^ 2) := by
  have hS : ∀ i, Measurable (fun ω => ∑ b ∈ I, Zs b ω i) := fun i =>
    Finset.measurable_sum _ (fun b _ => (measurable_pi_apply i).comp (hZs b))
  have e1 : ∀ (ω : Ω) (i : Fin n), (∑ b ∈ I, Zs b ω i)
      = (Pi.single i (1 : ℝ)) ⬝ᵥ ∑ b ∈ I, Zs b ω := fun ω i => by
    rw [single_dotProduct, one_mul, Finset.sum_apply]
  have hpt : ∀ ω, ENNReal.ofReal ((∑ i, (∑ b ∈ I, Zs b ω i) ^ 2) ^ 2)
      ≤ ∑ i : Fin n, ENNReal.ofReal ((n : ℝ) * ((Pi.single i (1 : ℝ)) ⬝ᵥ ∑ b ∈ I, Zs b ω) ^ 4) := by
    intro ω
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => (∑ b ∈ I, Zs b ω i) ^ 2)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    rw [← Finset.mul_sum]
    simp_rw [← e1]
    convert h using 3
    all_goals ring
  have hmeas : ∀ i : Fin n, Measurable (fun ω => ENNReal.ofReal
      ((n : ℝ) * ((Pi.single i (1 : ℝ)) ⬝ᵥ ∑ b ∈ I, Zs b ω) ^ 4)) := by
    intro i
    simp_rw [← e1]
    exact ENNReal.measurable_ofReal.comp (((hS i).pow_const 4).const_mul _)
  calc ∫⁻ ω, ENNReal.ofReal ((∑ i, (∑ b ∈ I, Zs b ω i) ^ 2) ^ 2) ∂P
      ≤ ∫⁻ ω, ∑ i : Fin n, ENNReal.ofReal
        ((n : ℝ) * ((Pi.single i (1 : ℝ)) ⬝ᵥ ∑ b ∈ I, Zs b ω) ^ 4) ∂P := lintegral_mono hpt
    _ = ∑ i : Fin n, ∫⁻ ω, ENNReal.ofReal
        ((n : ℝ) * ((Pi.single i (1 : ℝ)) ⬝ᵥ ∑ b ∈ I, Zs b ω) ^ 4) ∂P :=
        lintegral_finsetSum _ (fun i _ => hmeas i)
    _ ≤ ∑ i : Fin n, ENNReal.ofReal ((n : ℝ) * (3 * A4 * (I.card : ℝ) ^ 2 *
          (∑ j, (Pi.single i (1 : ℝ) : Fin n → ℝ) j ^ 2) ^ 2)) := by
        apply Finset.sum_le_sum
        intro i _
        have hh := rvp_dir4_gen A4 hA4 Z hZ hcent hdir4 Zs hZs hind hid (Pi.single i (1 : ℝ)) I
        simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg n)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr
    _ = ENNReal.ofReal (3 * A4 * (I.card : ℝ) ^ 2 * (n : ℝ) ^ 2) := by
        have h1 : ∀ i : Fin n, (∑ j, (Pi.single i (1 : ℝ) : Fin n → ℝ) j ^ 2) = 1 := by
          intro i
          simp [Pi.single_apply]
        simp_rw [h1]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
        congr 1
        ring


private lemma rvp_var_expand {f : Ω → ℝ} (hf : Integrable f P) (hf2 : Integrable (fun ω => f ω ^ 2) P) :
    ∫ ω, (f ω - ∫ ω', f ω' ∂P) ^ 2 ∂P = (∫ ω, f ω ^ 2 ∂P) - (∫ ω, f ω ∂P) ^ 2 := by
  set c := ∫ ω, f ω ∂P with hc
  have e : ∀ ω, (f ω - c) ^ 2 = (f ω ^ 2 - 2 * c * f ω) + c ^ 2 := fun ω => by ring
  simp_rw [e]
  have i1 : Integrable (fun ω => f ω ^ 2 - 2 * c * f ω) P := hf2.sub (hf.const_mul _)
  rw [integral_add i1 (integrable_const _), integral_sub hf2
    (hf.const_mul _), integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [← hc]; ring

private lemma rvp_pt_fourth {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) : (x - t) ^ 4 ≤ 2 * x ^ 4 + 2 * t ^ 4 := by
  have h1 : (x - t) ^ 2 ≤ x ^ 2 + t ^ 2 := by nlinarith [mul_nonneg hx ht]
  have h2 : ((x - t) ^ 2) ^ 2 ≤ (x ^ 2 + t ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
  nlinarith [sq_nonneg (x ^ 2 - t ^ 2)]

private lemma rvp_diag_gen {n B : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (A4 A8 : ℝ)
    (hA4 : 0 ≤ A4) (hA8 : 0 ≤ A8) (Z : Ω → (Fin n → ℝ)) (hZ : Measurable Z)
    (hcov : ∀ i k, ∫ ω, Z ω i * Z ω k ∂P = V i k)
    (hvec4 : ∫⁻ ω, ENNReal.ofReal ((∑ i, Z ω i ^ 2) ^ 2) ∂P ≤ ENNReal.ofReal (A4 * (n : ℝ) ^ 2))
    (hvec8 : ∫⁻ ω, ENNReal.ofReal ((∑ i, Z ω i ^ 2) ^ 4) ∂P ≤ ENNReal.ofReal (A8 * (n : ℝ) ^ 4))
    (Zs : Fin B → Ω → (Fin n → ℝ)) (hZs : ∀ b, Measurable (Zs b))
    (hind : iIndepFun Zs P) (hid : ∀ b, IdentDistrib (Zs b) Z P P) :
    ∫⁻ ω, ENNReal.ofReal ((∑ b : Fin B, ((∑ i, Zs b ω i ^ 2) - ∑ i, V i i)) ^ 4) ∂P
      ≤ ENNReal.ofReal ((16 * A8 + 3 * A4 ^ 2) * (B : ℝ) ^ 2 * (n : ℝ) ^ 4) := by
  set X : Ω → ℝ := fun ω => ∑ i, Z ω i ^ 2 with hXdef
  have hXm : Measurable X := Finset.measurable_sum _ (fun i _ =>
    ((measurable_pi_apply i).comp hZ).pow_const 2)
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => Finset.sum_nonneg (fun i _ => sq_nonneg _)
  obtain ⟨iX4, mX4⟩ := rvp_int_of_lint (f := fun ω => X ω ^ 4) (hXm.pow_const 4)
    (fun ω => by have := hX0 ω; positivity) _ (by positivity) hvec8
  obtain ⟨iX2, mX2⟩ := rvp_int_of_lint (f := fun ω => X ω ^ 2) (hXm.pow_const 2)
    (fun ω => by have := hX0 ω; positivity) _ (by positivity) hvec4
  have iX1 : Integrable X P := (rvp_pw_int hXm iX4 1 (by norm_num)).congr
    (Filter.Eventually.of_forall fun ω => by simp)
  have iZi : ∀ i, Integrable (fun ω => Z ω i ^ 2) P := by
    intro i
    refine Integrable.mono' iX1 (((measurable_pi_apply i).comp hZ).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Z ω i))]
    exact Finset.single_le_sum (f := fun j => Z ω j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  set t : ℝ := ∑ i, V i i with ht
  have htX : ∫ ω, X ω ∂P = t := by
    simp only [hXdef]
    rw [integral_finsetSum _ (fun i _ => iZi i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hcov i i]; simp [sq]
  have ht0 : 0 ≤ t := by rw [← htX]; exact integral_nonneg hX0
  -- moment facts
  have hsq1 : t ^ 2 ≤ ∫ ω, X ω ^ 2 ∂P := by rw [← htX]; exact rvp_sq_int_le iX1 iX2
  have hsq2 : (∫ ω, X ω ^ 2 ∂P) ^ 2 ≤ ∫ ω, X ω ^ 4 ∂P := by
    have := rvp_sq_int_le (f := fun ω => X ω ^ 2) iX2 (by simpa [← pow_mul] using iX4)
    simpa [← pow_mul] using this
  have ht4 : t ^ 4 ≤ ∫ ω, X ω ^ 4 ∂P := by
    calc t ^ 4 = (t ^ 2) ^ 2 := by ring
      _ ≤ (∫ ω, X ω ^ 2 ∂P) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hsq1 2
      _ ≤ _ := hsq2
  have iG4 : Integrable (fun ω => (X ω - t) ^ 4) P := by
    refine Integrable.mono' ((iX4.const_mul 2).add (integrable_const (2 * t ^ 4)))
      ((hXm.sub_const t).pow_const 4).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (X ω - t) ^ 4)]
    exact rvp_pt_fourth (hX0 ω) ht0
  have mG4 : ∫ ω, (X ω - t) ^ 4 ∂P ≤ 4 * (A8 * (n : ℝ) ^ 4) := by
    calc ∫ ω, (X ω - t) ^ 4 ∂P ≤ ∫ ω, (2 * X ω ^ 4 + 2 * t ^ 4) ∂P :=
          integral_mono iG4 ((iX4.const_mul 2).add (integrable_const _))
            (fun ω => rvp_pt_fourth (hX0 ω) ht0)
      _ = 2 * ∫ ω, X ω ^ 4 ∂P + 2 * t ^ 4 := by
          rw [integral_add (iX4.const_mul 2) (integrable_const _), integral_const_mul]
          simp
      _ ≤ 4 * (A8 * (n : ℝ) ^ 4) := by linarith
  have hGvar : ∫ ω, (X ω - t) ^ 2 ∂P = (∫ ω, X ω ^ 2 ∂P) - t ^ 2 := by
    have := rvp_var_expand iX1 iX2
    rwa [htX] at this
  have mG2 : ∫ ω, (X ω - t) ^ 2 ∂P ≤ A4 * (n : ℝ) ^ 2 := by
    rw [hGvar]; nlinarith [sq_nonneg t]
  have pG2 : 0 ≤ ∫ ω, (X ω - t) ^ 2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
  have g0 : ∫ ω, (X ω - t) ∂P = 0 := by
    rw [integral_sub iX1 (integrable_const _)]; simp [htX]
  obtain ⟨j4, f4, -⟩ := rvp_iid_transfer (P := P) (g := fun z : Fin n → ℝ => (∑ i, z i ^ 2) - t)
    hZs hind hid (by
      refine Measurable.sub (Finset.measurable_sum _ (fun i _ => ?_)) measurable_const
      exact ((measurable_pi_apply i)).pow_const 2) iG4 g0 Finset.univ
  rw [← ofReal_integral_eq_lintegral_ofReal j4 (Filter.Eventually.of_forall fun ω => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [f4]
  simp only [Finset.card_univ, Fintype.card_fin]
  have hm : ∫ ω, (∑ i, Z ω i ^ 2 - t) ^ 4 ∂P ≤ 4 * (A8 * (n : ℝ) ^ 4) := mG4
  have hs : ∫ ω, (∑ i, Z ω i ^ 2 - t) ^ 2 ∂P ≤ A4 * (n : ℝ) ^ 2 := mG2
  have hs0 : 0 ≤ ∫ ω, (∑ i, Z ω i ^ 2 - t) ^ 2 ∂P := pG2
  set m := ∫ ω, (∑ i, Z ω i ^ 2 - t) ^ 4 ∂P
  set σ := ∫ ω, (∑ i, Z ω i ^ 2 - t) ^ 2 ∂P
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hB1 : (B : ℝ) ≤ (B : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos B with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ B := by exact_mod_cast h
      nlinarith
  have hσ2 : σ ^ 2 ≤ (A4 * (n : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  have hn4 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
  have hA : 0 ≤ A8 * (n : ℝ) ^ 4 := by positivity
  have e1 : (B : ℝ) * m ≤ (B : ℝ) * (4 * (A8 * (n : ℝ) ^ 4)) := mul_le_mul_of_nonneg_left hm hB0
  have e2 : 3 * (B : ℝ) * ((B : ℝ) - 1) * σ ^ 2 ≤ 3 * (B : ℝ) ^ 2 * (A4 * (n : ℝ) ^ 2) ^ 2 := by
    have hh : 3 * (B : ℝ) * ((B : ℝ) - 1) ≤ 3 * (B : ℝ) ^ 2 := by nlinarith
    have hh0 : 0 ≤ 3 * (B : ℝ) * ((B : ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos B with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ B := by exact_mod_cast h
        nlinarith
    calc 3 * (B : ℝ) * ((B : ℝ) - 1) * σ ^ 2 ≤ 3 * (B : ℝ) * ((B : ℝ) - 1) * (A4 * (n : ℝ) ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hσ2 hh0
      _ ≤ 3 * (B : ℝ) ^ 2 * (A4 * (n : ℝ) ^ 2) ^ 2 := mul_le_mul_of_nonneg_right hh (by positivity)
  have e3 : (B : ℝ) * (4 * (A8 * (n : ℝ) ^ 4)) ≤ (B : ℝ) ^ 2 * (16 * A8 * (n : ℝ) ^ 4) := by
    have : (B : ℝ) * (4 * (A8 * (n : ℝ) ^ 4)) ≤ (B : ℝ) ^ 2 * (4 * (A8 * (n : ℝ) ^ 4)) :=
      mul_le_mul_of_nonneg_right hB1 (by positivity)
    nlinarith
  nlinarith


private lemma rvp_lint_indep_bound {E F : Type} [MeasurableSpace E] [MeasurableSpace F]
    {X : Ω → E} {Y : Ω → F} (hX : Measurable X) (hY : Measurable Y) (hind : IndepFun X Y P)
    (Φ : E → F → ENNReal) (hΦ : Measurable (fun p : E × F => Φ p.1 p.2))
    (ψ : F → ENNReal) (hψ : Measurable ψ)
    (h : ∀ y, ∫⁻ ω, Φ (X ω) y ∂P ≤ ψ y) :
    ∫⁻ ω, Φ (X ω) (Y ω) ∂P ≤ ∫⁻ ω, ψ (Y ω) ∂P := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hind
  have hXY : Measurable (fun ω => (X ω, Y ω)) := hX.prodMk hY
  have e1 : ∫⁻ ω, Φ (X ω) (Y ω) ∂P = ∫⁻ p, Φ p.1 p.2 ∂((P.map X).prod (P.map Y)) := by
    rw [← hmap, lintegral_map hΦ hXY]
  rw [e1, lintegral_prod_symm _ hΦ.aemeasurable, ← lintegral_map hψ hY]
  refine lintegral_mono (fun y => ?_)
  calc ∫⁻ x, Φ x y ∂(P.map X) = ∫⁻ ω, Φ (X ω) y ∂P :=
        lintegral_map (hΦ.comp (measurable_id.prodMk measurable_const)) hX
    _ ≤ ψ y := h y


private lemma rvp_cross4 {n B : ℕ} (A4 : ℝ) (hA4 : 0 ≤ A4) (Z : Ω → (Fin n → ℝ)) (hZ : Measurable Z)
    (hcent : ∀ i, ∫ ω, Z ω i ∂P = 0)
    (hdir4 : ∀ a : Fin n → ℝ,
      ∫⁻ ω, ENNReal.ofReal ((a ⬝ᵥ Z ω) ^ 4) ∂P ≤ ENNReal.ofReal (A4 * (∑ i, a i ^ 2) ^ 2))
    (Zs : Fin B → Ω → (Fin n → ℝ)) (hZs : ∀ b, Measurable (Zs b))
    (hind : iIndepFun Zs P) (hid : ∀ b, IdentDistrib (Zs b) Z P P) (I : Finset (Fin B)) :
    ∫⁻ ω, ENNReal.ofReal (((∑ b ∈ I, Zs b ω) ⬝ᵥ (∑ b ∈ Iᶜ, Zs b ω)) ^ 4) ∂P
      ≤ ENNReal.ofReal (9 * A4 ^ 2 * (I.card : ℝ) ^ 2 * (Iᶜ.card : ℝ) ^ 2 * (n : ℝ) ^ 2) := by
  have hXm : Measurable (fun ω => ∑ b ∈ I, Zs b ω) := Finset.measurable_sum _ (fun b _ => hZs b)
  have hYm : Measurable (fun ω => ∑ b ∈ Iᶜ, Zs b ω) := Finset.measurable_sum _ (fun b _ => hZs b)
  have hI : IndepFun (fun ω => ∑ b ∈ I, Zs b ω) (fun ω => ∑ b ∈ Iᶜ, Zs b ω) P := by
    have h := hind.indepFun_finset I Iᶜ disjoint_compl_right hZs
    have h2 := h.comp (φ := fun f : (I → Fin n → ℝ) => ∑ i, f i)
      (ψ := fun f : (↥Iᶜ → Fin n → ℝ) => ∑ i, f i)
      (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
      (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
    have e1 : (fun ω => ∑ b ∈ I, Zs b ω) = (fun ω => ∑ i : I, Zs i ω) := by
      funext ω; exact (Finset.sum_coe_sort I (fun b => Zs b ω)).symm
    have e2 : (fun ω => ∑ b ∈ Iᶜ, Zs b ω) = (fun ω => ∑ i : (Iᶜ : Finset (Fin B)), Zs i ω) := by
      funext ω; exact (Finset.sum_coe_sort Iᶜ (fun b => Zs b ω)).symm
    rw [e1, e2]; exact h2
  have hΦ : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      ENNReal.ofReal ((p.1 ⬝ᵥ p.2) ^ 4)) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.pow_const ?_ 4)
    unfold dotProduct
    fun_prop
  set c : ℝ := 3 * A4 * (I.card : ℝ) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hψ : Measurable (fun y : Fin n → ℝ => ENNReal.ofReal (c * (∑ i, y i ^ 2) ^ 2)) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.const_mul (Measurable.pow_const ?_ 2) _)
    exact Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).pow_const 2)
  have key := rvp_lint_indep_bound hXm hYm hI (fun x y => ENNReal.ofReal ((x ⬝ᵥ y) ^ 4)) hΦ _ hψ (fun y => by
    have := rvp_dir4_gen A4 hA4 Z hZ hcent hdir4 Zs hZs hind hid y I
    simp_rw [dotProduct_comm _ y]
    simpa [hc, mul_assoc] using this)
  refine key.trans ?_
  have hv := rvp_vec4_gen A4 hA4 Z hZ hcent hdir4 Zs hZs hind hid Iᶜ
  simp_rw [ENNReal.ofReal_mul hc0]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal ((∑ i, (∑ b ∈ Iᶜ, Zs b ω) i ^ 2) ^ 2) ∂P
      ≤ ENNReal.ofReal c * ENNReal.ofReal (3 * A4 * (Iᶜ.card : ℝ) ^ 2 * (n : ℝ) ^ 2) := by
        gcongr
        simpa [Finset.sum_apply] using hv
    _ = _ := by
        rw [← ENNReal.ofReal_mul hc0]; congr 1; rw [hc]; ring

private lemma rvp_cnt {B : ℕ} (b b' : Fin B) (h : b ≠ b') :
    4 * ((Finset.univ : Finset (Finset (Fin B))).filter (fun I => b ∈ I ∧ b' ∉ I)).card = 2 ^ B := by
  set T : Finset (Fin B) := Finset.univ \ {b, b'} with hT
  have hsub : ({b, b'} : Finset (Fin B)) ⊆ Finset.univ := Finset.subset_univ _
  have hTc : T.card = B - 2 := by
    rw [hT, Finset.card_sdiff_of_subset hsub, Finset.card_univ, Fintype.card_fin,
      Finset.card_pair h]
  have hB2 : 2 ≤ B := by
    have := Finset.card_le_univ ({b, b'} : Finset (Fin B))
    rwa [Finset.card_pair h, Fintype.card_fin] at this
  have hF : (Finset.univ : Finset (Finset (Fin B))).filter (fun I => b ∈ I ∧ b' ∉ I)
      = T.powerset.image (insert b) := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_powerset]
    constructor
    · rintro ⟨hb, hb'⟩
      refine ⟨I.erase b, ?_, Finset.insert_erase hb⟩
      intro x hx
      rw [Finset.mem_erase] at hx
      simp only [hT, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        true_and, not_or]
      exact ⟨hx.1, fun hxb' => hb' (hxb' ▸ hx.2)⟩
    · rintro ⟨J, hJ, rfl⟩
      have hbJ : b ∉ J := fun hbJ => by
        have := hJ hbJ; simp [hT] at this
      have hb'J : b' ∉ J := fun hbJ => by
        have := hJ hbJ; simp [hT] at this
      exact ⟨Finset.mem_insert_self _ _, by simp [Finset.mem_insert, hb'J, h.symm]⟩
  rw [hF, Finset.card_image_of_injOn, Finset.card_powerset, hTc]
  · obtain ⟨k, rfl⟩ : ∃ k, B = k + 2 := ⟨B - 2, by omega⟩
    simp [pow_add]; ring
  · intro J hJ J' hJ' hEq
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at hJ hJ'
    have hbJ : b ∉ J := fun hbJ => by
      have := hJ hbJ; simp [hT] at this
    have hbJ' : b ∉ J' := fun hbJ => by
      have := hJ' hbJ; simp [hT] at this
    have := congrArg (fun K => Finset.erase K b) hEq
    simpa [Finset.erase_insert hbJ, Finset.erase_insert hbJ'] using this

private lemma rvp_sum_mem_ite {B : ℕ} (s : Finset (Fin B)) (g : Fin B → ℝ) :
    ∑ b ∈ s, g b = ∑ b : Fin B, if b ∈ s then g b else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

private lemma rvp_offdiag_id {B : ℕ} (f : Fin B → Fin B → ℝ) :
    (2 : ℝ) ^ B * ∑ b : Fin B, ∑ b' ∈ Finset.univ.filter (fun b' : Fin B => b' ≠ b), f b b'
      = 4 * ∑ I : Finset (Fin B), ∑ b ∈ I, ∑ b' ∈ Iᶜ, f b b' := by
  have e1 : ∀ I : Finset (Fin B), ∑ b ∈ I, ∑ b' ∈ Iᶜ, f b b'
      = ∑ b : Fin B, ∑ b' : Fin B, if (b ∈ I ∧ b' ∉ I) then f b b' else 0 := by
    intro I
    rw [rvp_sum_mem_ite]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hb : b ∈ I
    · rw [if_pos hb, rvp_sum_mem_ite]
      refine Finset.sum_congr rfl (fun b' _ => ?_)
      simp [hb]
    · simp [hb]
  simp_rw [e1]
  have e2 : ∑ I : Finset (Fin B), ∑ b : Fin B, ∑ b' : Fin B, (if (b ∈ I ∧ b' ∉ I) then f b b' else 0)
      = ∑ b : Fin B, ∑ b' : Fin B, ∑ I : Finset (Fin B),
        (if (b ∈ I ∧ b' ∉ I) then f b b' else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
  rw [e2, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b' _ => ?_)
  by_cases hbb : b' = b
  · subst hbb
    simp
  · have hc := rvp_cnt b b' (Ne.symm hbb)
    have : ∑ I : Finset (Fin B), (if (b ∈ I ∧ b' ∉ I) then f b b' else 0)
        = (((Finset.univ : Finset (Finset (Fin B))).filter (fun I => b ∈ I ∧ b' ∉ I)).card : ℝ)
          * f b b' := by
      rw [← Finset.sum_filter]; simp
    rw [this, if_pos hbb]
    have hc' : (4 : ℝ) * ((((Finset.univ : Finset (Finset (Fin B))).filter
        (fun I => b ∈ I ∧ b' ∉ I)).card : ℕ) : ℝ) = 2 ^ B := by exact_mod_cast hc
    rw [← hc']; ring


private lemma rvp_jensen4 {ι : Type} (s : Finset ι) (g : ι → ℝ) :
    (∑ i ∈ s, g i) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, g i ^ 4 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := s) (f := g)
  have h2 := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => g i ^ 2)
  have h0 : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have h3 : (∑ i ∈ s, g i) ^ 4 = ((∑ i ∈ s, g i) ^ 2) ^ 2 := by ring
  rw [h3]
  calc ((∑ i ∈ s, g i) ^ 2) ^ 2 ≤ ((s.card : ℝ) * ∑ i ∈ s, g i ^ 2) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = (s.card : ℝ) ^ 2 * (∑ i ∈ s, g i ^ 2) ^ 2 := by ring
    _ ≤ (s.card : ℝ) ^ 2 * ((s.card : ℝ) * ∑ i ∈ s, (g i ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (s.card : ℝ) ^ 3 * ∑ i ∈ s, g i ^ 4 := by
        simp_rw [← pow_mul]; ring

private lemma rvp_meas_G {n B : ℕ} (Zs : Fin B → Ω → (Fin n → ℝ)) (hZs : ∀ b, Measurable (Zs b))
    (I J : Finset (Fin B)) :
    Measurable (fun ω => (∑ b ∈ I, Zs b ω) ⬝ᵥ (∑ b ∈ J, Zs b ω)) := by
  unfold dotProduct
  refine Finset.measurable_sum _ (fun i _ => Measurable.mul ?_ ?_)
  · exact (measurable_pi_apply i).comp (Finset.measurable_sum I (fun b _ => hZs b))
  · exact (measurable_pi_apply i).comp (Finset.measurable_sum J (fun b _ => hZs b))

private lemma rvp_offdiag_gen {n B : ℕ} (A4 : ℝ) (hA4 : 0 ≤ A4) (Z : Ω → (Fin n → ℝ)) (hZ : Measurable Z)
    (hcent : ∀ i, ∫ ω, Z ω i ∂P = 0)
    (hdir4 : ∀ a : Fin n → ℝ,
      ∫⁻ ω, ENNReal.ofReal ((a ⬝ᵥ Z ω) ^ 4) ∂P ≤ ENNReal.ofReal (A4 * (∑ i, a i ^ 2) ^ 2))
    (Zs : Fin B → Ω → (Fin n → ℝ)) (hZs : ∀ b, Measurable (Zs b))
    (hind : iIndepFun Zs P) (hid : ∀ b, IdentDistrib (Zs b) Z P P) :
    ∫⁻ ω, ENNReal.ofReal ((∑ b : Fin B, ∑ b' ∈ Finset.univ.filter (fun b' : Fin B => b' ≠ b),
        (Zs b ω ⬝ᵥ Zs b' ω)) ^ 4) ∂P
      ≤ ENNReal.ofReal (144 * A4 ^ 2 * (B : ℝ) ^ 4 * (n : ℝ) ^ 2) := by
  set G : Finset (Fin B) → Ω → ℝ := fun I ω => (∑ b ∈ I, Zs b ω) ⬝ᵥ (∑ b ∈ Iᶜ, Zs b ω) with hG
  set N : ℝ := (2 : ℝ) ^ B with hN
  have hN0 : 0 < N := by positivity
  have hcard : ((Finset.univ : Finset (Finset (Fin B))).card : ℝ) = N := by
    simp [hN]
  have hid2 : ∀ ω, N * (∑ b : Fin B, ∑ b' ∈ Finset.univ.filter (fun b' : Fin B => b' ≠ b),
        (Zs b ω ⬝ᵥ Zs b' ω)) = 4 * ∑ I : Finset (Fin B), G I ω := by
    intro ω
    rw [hN, rvp_offdiag_id (fun b b' => Zs b ω ⬝ᵥ Zs b' ω)]
    congr 1
    refine Finset.sum_congr rfl (fun I _ => ?_)
    simp only [hG]
    rw [sum_dotProduct]
    exact Finset.sum_congr rfl (fun b _ => (dotProduct_sum _ _ _).symm)
  have hpt : ∀ ω, ENNReal.ofReal ((∑ b : Fin B, ∑ b' ∈ Finset.univ.filter (fun b' : Fin B => b' ≠ b),
        (Zs b ω ⬝ᵥ Zs b' ω)) ^ 4)
      ≤ ENNReal.ofReal (256 / N) * ∑ I : Finset (Fin B), ENNReal.ofReal (G I ω ^ 4) := by
    intro ω
    rw [← ENNReal.ofReal_sum_of_nonneg (fun I _ => by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    set W := ∑ b : Fin B, ∑ b' ∈ Finset.univ.filter (fun b' : Fin B => b' ≠ b),
        (Zs b ω ⬝ᵥ Zs b' ω)
    have hj := rvp_jensen4 (Finset.univ : Finset (Finset (Fin B))) (fun I => G I ω)
    rw [hcard] at hj
    have h4 : N ^ 4 * W ^ 4 = 256 * (∑ I : Finset (Fin B), G I ω) ^ 4 := by
      have : (N * W) ^ 4 = (4 * ∑ I : Finset (Fin B), G I ω) ^ 4 := by rw [hid2]
      calc N ^ 4 * W ^ 4 = (N * W) ^ 4 := by ring
        _ = _ := by rw [this]; ring
    rw [div_mul_eq_mul_div, le_div_iff₀ hN0]
    have h5 : N ^ 3 * (N * W ^ 4) ≤ N ^ 3 * (256 * ∑ I : Finset (Fin B), G I ω ^ 4) := by
      calc N ^ 3 * (N * W ^ 4) = N ^ 4 * W ^ 4 := by ring
        _ = 256 * (∑ I : Finset (Fin B), G I ω) ^ 4 := h4
        _ ≤ 256 * (N ^ 3 * ∑ I : Finset (Fin B), G I ω ^ 4) := by linarith
        _ = _ := by ring
    have := le_of_mul_le_mul_left h5 (by positivity)
    linarith
  have hGm : ∀ I : Finset (Fin B), Measurable (fun ω => ENNReal.ofReal (G I ω ^ 4)) := fun I =>
    ENNReal.measurable_ofReal.comp ((rvp_meas_G Zs hZs I Iᶜ).pow_const 4)
  set c : ℝ := 9 / 16 * A4 ^ 2 * (B : ℝ) ^ 4 * (n : ℝ) ^ 2 with hc
  have hper : ∀ I : Finset (Fin B), ∫⁻ ω, ENNReal.ofReal (G I ω ^ 4) ∂P ≤ ENNReal.ofReal c := by
    intro I
    refine (rvp_cross4 A4 hA4 Z hZ hcent hdir4 Zs hZs hind hid I).trans (ENNReal.ofReal_le_ofReal ?_)
    have hpq : (I.card : ℝ) + (Iᶜ.card : ℝ) = B := by
      have := Finset.card_add_card_compl I
      simp only [Fintype.card_fin] at this
      exact_mod_cast this
    set p : ℝ := (I.card : ℝ)
    set q : ℝ := (Iᶜ.card : ℝ)
    have hp : 0 ≤ p := Nat.cast_nonneg _
    have hq : 0 ≤ q := Nat.cast_nonneg _
    have h1 : p * q ≤ (B : ℝ) ^ 2 / 4 := by rw [← hpq]; nlinarith [sq_nonneg (p - q)]
    have h2 : (p * q) ^ 2 ≤ ((B : ℝ) ^ 2 / 4) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : 0 ≤ A4 ^ 2 * (n : ℝ) ^ 2 := by positivity
    calc 9 * A4 ^ 2 * p ^ 2 * q ^ 2 * (n : ℝ) ^ 2 = 9 * (A4 ^ 2 * (n : ℝ) ^ 2) * (p * q) ^ 2 := by ring
      _ ≤ 9 * (A4 ^ 2 * (n : ℝ) ^ 2) * (((B : ℝ) ^ 2 / 4) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = c := by rw [hc]; ring
  calc ∫⁻ ω, ENNReal.ofReal ((∑ b : Fin B, ∑ b' ∈ Finset.univ.filter (fun b' : Fin B => b' ≠ b),
        (Zs b ω ⬝ᵥ Zs b' ω)) ^ 4) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (256 / N) * ∑ I : Finset (Fin B), ENNReal.ofReal (G I ω ^ 4) ∂P :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (256 / N) * ∑ I : Finset (Fin B), ∫⁻ ω, ENNReal.ofReal (G I ω ^ 4) ∂P := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum _ (fun I _ => hGm I)]
    _ ≤ ENNReal.ofReal (256 / N) * ∑ I : Finset (Fin B), ENNReal.ofReal c := by
        gcongr with I _
        exact hper I
    _ = ENNReal.ofReal (144 * A4 ^ 2 * (B : ℝ) ^ 4 * (n : ℝ) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), hcard]
        congr 1
        rw [hc]
        field_simp
        ring


end RVPartitionHelpers

/-- **lem:app-sgd-partition** `Muon.SignSGD.lem_app_sgd_partition`.

cr-2026-10-23. LaTeX statement (verbatim):
\begin{lemma}[Fourth moments of sums]\label{lem:app-sgd-partition}
Let $Z\in\R^{\Nout}$ be centered with covariance $V$ and satisfy
\cref{eqn:app-sgd-dir,eqn:app-sgd-vec}, let $Z_1,\dots,Z_B$ be independent copies, and put
$S_s\defeq\sum_{b\le s}Z_b$,
\[
\mathcal W\defeq\sum_{b\ne b'}\langle Z_b,Z_{b'}\rangle,\qquad \mathcal D_B\defeq\sum_{b=1}^B\big(\norm{Z_b}^2-\Tr V\big).
\]
Then, for $0\le s\le B$ and $a\in\R^{\Nout}$,
\begin{gather*}
\EE\norm{S_s}^4\le3A_4s^2\Nout^2,\qquad \EE(a^\T S_s)^4\le3A_4s^2\norm a^4,\\
\EE\mathcal W^4\le144A_4^2B^4\Nout^2,\qquad \EE\mathcal D_B^4\le(16A_8+3A_4^2)B^2\Nout^4 .
\end{gather*}
\end{lemma}
-/
theorem lem_app_sgd_partition {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n B : ℕ) (V : Matrix (Fin n) (Fin n) ℝ) (A4 A8 : ℝ)
    (hA4 : 0 ≤ A4) (hA8 : 0 ≤ A8)
    (Z : Ω → (Fin n → ℝ)) (hZ : Measurable Z)
    (hcent : ∀ i, ∫ ω, Z ω i ∂P = 0)
    (hcov : ∀ i k, ∫ ω, Z ω i * Z ω k ∂P = V i k)
    (hdir4 : ∀ a : Fin n → ℝ,
      ∫⁻ ω, ENNReal.ofReal ((a ⬝ᵥ Z ω) ^ 4) ∂P ≤ ENNReal.ofReal (A4 * (∑ i, a i ^ 2) ^ 2))
    (hdir8 : ∀ a : Fin n → ℝ,
      ∫⁻ ω, ENNReal.ofReal ((a ⬝ᵥ Z ω) ^ 8) ∂P ≤ ENNReal.ofReal (A8 * (∑ i, a i ^ 2) ^ 4))
    (hvec4 : ∫⁻ ω, ENNReal.ofReal ((∑ i, Z ω i ^ 2) ^ 2) ∂P ≤ ENNReal.ofReal (A4 * (n : ℝ) ^ 2))
    (hvec8 : ∫⁻ ω, ENNReal.ofReal ((∑ i, Z ω i ^ 2) ^ 4) ∂P ≤ ENNReal.ofReal (A8 * (n : ℝ) ^ 4))
    (Zs : Fin B → Ω → (Fin n → ℝ)) (hZs : ∀ b, Measurable (Zs b))
    (hind : iIndepFun Zs P) (hid : ∀ b, IdentDistrib (Zs b) Z P P) :
    (∀ s : ℕ, s ≤ B →
      (∫⁻ ω, ENNReal.ofReal ((∑ i, partSum Zs s ω i ^ 2) ^ 2) ∂P
          ≤ ENNReal.ofReal (3 * A4 * (s : ℝ) ^ 2 * (n : ℝ) ^ 2)) ∧
      ∀ a : Fin n → ℝ,
        ∫⁻ ω, ENNReal.ofReal ((a ⬝ᵥ partSum Zs s ω) ^ 4) ∂P
          ≤ ENNReal.ofReal (3 * A4 * (s : ℝ) ^ 2 * (∑ i, a i ^ 2) ^ 2)) ∧
    (∫⁻ ω, ENNReal.ofReal (offDiagSum Zs ω ^ 4) ∂P
      ≤ ENNReal.ofReal (144 * A4 ^ 2 * (B : ℝ) ^ 4 * (n : ℝ) ^ 2)) ∧
    (∫⁻ ω, ENNReal.ofReal (diagDevSum V Zs ω ^ 4) ∂P
      ≤ ENNReal.ofReal ((16 * A8 + 3 * A4 ^ 2) * (B : ℝ) ^ 2 * (n : ℝ) ^ 4)) := by
  have hcard : ∀ s : ℕ, s ≤ B → (Finset.univ.filter (fun b : Fin B => (b : ℕ) < s)).card = s := by
    intro s hs
    have := Fin.card_filter_val_lt (n := B) (m := s)
    simpa [Nat.min_eq_right hs] using this
  refine ⟨fun s hs => ⟨?_, fun a => ?_⟩, ?_, ?_⟩
  · have h := rvp_vec4_gen A4 hA4 Z hZ hcent hdir4 Zs hZs hind hid
      (Finset.univ.filter (fun b : Fin B => (b : ℕ) < s))
    rw [hcard s hs] at h
    simpa [partSum, Finset.sum_apply] using h
  · have h := rvp_dir4_gen A4 hA4 Z hZ hcent hdir4 Zs hZs hind hid a
      (Finset.univ.filter (fun b : Fin B => (b : ℕ) < s))
    rw [hcard s hs] at h
    simpa [partSum] using h
  · exact rvp_offdiag_gen A4 hA4 Z hZ hcent hdir4 Zs hZs hind hid
  · exact rvp_diag_gen V A4 A8 hA4 hA8 Z hZ hcov hvec4 hvec8 Zs hZs hind hid

/-! ## Column norms (`lem:app-sgd-column-norm`) -/

/-- `x₀ = 2ℛ Tr Λ / B` of `lem:app-sgd-column-norm` (l. 1244), with `2ℛ = twoR μ D`. -/
noncomputable def haarX0 {n m : ℕ} (B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  twoR μ D * (∑ i, μ i) / (B : ℝ)

/-! ### Proof helpers for `lem:app-sgd-column-norm` (private) -/

private lemma rvq_meas_dot {n : ℕ} (a : Fin n → ℝ) : Measurable (fun z : Fin n → ℝ => a ⬝ᵥ z) := by
  unfold dotProduct
  fun_prop

private lemma rvp_colZ_meas {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) :
    Measurable (colZ μ D j) := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold colZ colSample resA colMeanVec
  simp only [Pi.sub_apply]
  fun_prop

private lemma rvp_batchLaw_prob (n m B : ℕ) : IsProbabilityMeasure (batchLaw n m B) := by
  have : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  unfold batchLaw; infer_instance

private lemma rvp_hCol_eq {n m B : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m)
    (hB : 0 < B) (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) (i : Fin n) :
    hCol μ D β j i = colMeanVec μ D j i
      + (1 / (B : ℝ)) * partSum (fun (b : Fin B) (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
          colZ μ D j (β b)) B β i := by
  have hB' : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  unfold hCol partSum
  rw [Finset.filter_true_of_mem (fun b _ => b.2), Finset.sum_apply]
  simp only [colZ, Pi.sub_apply]
  have : ∑ a : Fin B, colSample μ D j (β a) i
      = ∑ a : Fin B, (colSample μ D j (β a) i - colMeanVec μ D j i) + B * colMeanVec μ D j i := by
    rw [Finset.sum_sub_distrib]; simp
  rw [this]; field_simp; ring

/-- the partition lemma applied to the column samples -/
private lemma rvp_col_partition (A4 A8 : ℝ) (hA4 : 0 ≤ A4) (hA8 : 0 ≤ A8) {n m B : ℕ}
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (hB : 0 < B)
    (hcent : ∀ i, ∫ p, colZ μ D j p i ∂(gaussBatch n m) = 0)
    (hdir4 : ∀ a : Fin n → ℝ,
      ∫⁻ p, ENNReal.ofReal ((a ⬝ᵥ colZ μ D j p) ^ 4) ∂(gaussBatch n m)
        ≤ ENNReal.ofReal (A4 * (∑ i, a i ^ 2) ^ 2))
    (hdir8 : ∀ a : Fin n → ℝ,
      ∫⁻ p, ENNReal.ofReal ((a ⬝ᵥ colZ μ D j p) ^ 8) ∂(gaussBatch n m)
        ≤ ENNReal.ofReal (A8 * (∑ i, a i ^ 2) ^ 4))
    (hvec4 : ∫⁻ p, ENNReal.ofReal ((∑ i, colZ μ D j p i ^ 2) ^ 2) ∂(gaussBatch n m)
      ≤ ENNReal.ofReal (A4 * (n : ℝ) ^ 2))
    (hvec8 : ∫⁻ p, ENNReal.ofReal ((∑ i, colZ μ D j p i ^ 2) ^ 4) ∂(gaussBatch n m)
      ≤ ENNReal.ofReal (A8 * (n : ℝ) ^ 4)) :
    let Zs : Fin B → (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ) :=
      fun b β => colZ μ D j (β b)
    (∀ s : ℕ, s ≤ B →
      (∫⁻ ω, ENNReal.ofReal ((∑ i, partSum Zs s ω i ^ 2) ^ 2) ∂(batchLaw n m B)
          ≤ ENNReal.ofReal (3 * A4 * (s : ℝ) ^ 2 * (n : ℝ) ^ 2)) ∧
      ∀ a : Fin n → ℝ,
        ∫⁻ ω, ENNReal.ofReal ((a ⬝ᵥ partSum Zs s ω) ^ 4) ∂(batchLaw n m B)
          ≤ ENNReal.ofReal (3 * A4 * (s : ℝ) ^ 2 * (∑ i, a i ^ 2) ^ 2)) ∧
    (∫⁻ ω, ENNReal.ofReal (offDiagSum Zs ω ^ 4) ∂(batchLaw n m B)
      ≤ ENNReal.ofReal (144 * A4 ^ 2 * (B : ℝ) ^ 4 * (n : ℝ) ^ 2)) ∧
    (∫⁻ ω, ENNReal.ofReal (diagDevSum (colCov μ D j) Zs ω ^ 4) ∂(batchLaw n m B)
      ≤ ENNReal.ofReal ((16 * A8 + 3 * A4 ^ 2) * (B : ℝ) ^ 2 * (n : ℝ) ^ 4)) := by
  intro Zs
  have := rvp_batchLaw_prob n m B
  have : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  have hcz := rvp_colZ_meas μ D j
  let i0 : Fin B := ⟨0, hB⟩
  have hev : ∀ b : Fin B, MeasurePreserving (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => β b)
      (batchLaw n m B) (gaussBatch n m) := fun b =>
    measurePreserving_eval (fun _ : Fin B => gaussBatch n m) b
  have hlint : ∀ (F : (Fin n → ℝ) → ENNReal), Measurable F →
      ∫⁻ β, F (colZ μ D j (β i0)) ∂(batchLaw n m B) = ∫⁻ p, F (colZ μ D j p) ∂(gaussBatch n m) :=
    fun F hF => (hev i0).lintegral_comp (hF.comp hcz)
  refine lem_app_sgd_partition (batchLaw n m B) n B (colCov μ D j) A4 A8 hA4 hA8
    (fun β => colZ μ D j (β i0)) (hcz.comp (measurable_pi_apply i0)) ?_ ?_ ?_ ?_ ?_ ?_
    Zs (fun b => hcz.comp (measurable_pi_apply b)) ?_ ?_
  · intro i
    have h := integral_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := i0)
      (f := fun p => colZ μ D j p i)
      (((measurable_pi_apply i).comp hcz).aestronglyMeasurable)
    simpa [batchLaw] using h.trans (hcent i)
  · intro i k
    have h := integral_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := i0)
      (f := fun p => colZ μ D j p i * colZ μ D j p k)
      ((((measurable_pi_apply i).comp hcz).mul
        ((measurable_pi_apply k).comp hcz)).aestronglyMeasurable)
    simp only [batchLaw]
    refine h.trans ?_
    simp [colCov]
  · intro a
    exact (le_of_eq (hlint (fun z => ENNReal.ofReal ((a ⬝ᵥ z) ^ 4))
      (((rvq_meas_dot a).pow_const 4).ennreal_ofReal))).trans (hdir4 a)
  · intro a
    exact (le_of_eq (hlint (fun z => ENNReal.ofReal ((a ⬝ᵥ z) ^ 8))
      (((rvq_meas_dot a).pow_const 8).ennreal_ofReal))).trans (hdir8 a)
  · refine (le_of_eq (hlint (fun z => ENNReal.ofReal ((∑ i, z i ^ 2) ^ 2)) ?_)).trans hvec4
    exact ((Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).pow_const 2)).pow_const
      2).ennreal_ofReal
  · refine (le_of_eq (hlint (fun z => ENNReal.ofReal ((∑ i, z i ^ 2) ^ 4)) ?_)).trans hvec8
    exact ((Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).pow_const 2)).pow_const
      4).ennreal_ofReal
  · exact iIndepFun_pi (μ := fun _ : Fin B => gaussBatch n m) (X := fun _ => colZ μ D j)
      (fun _ => hcz.aemeasurable)
  · intro b
    refine ⟨(hcz.comp (measurable_pi_apply b)).aemeasurable,
      (hcz.comp (measurable_pi_apply i0)).aemeasurable, ?_⟩
    have e : ∀ b : Fin B, Measure.map (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => colZ μ D j (β b))
        (batchLaw n m B) = (gaussBatch n m).map (colZ μ D j) := by
      intro b
      have := Measure.map_map hcz (measurable_pi_apply (X := fun _ : Fin B =>
        (Fin n → ℝ) × (Fin m → ℝ)) b) (μ := batchLaw n m B)
      rw [(hev b).map_eq] at this
      exact this.symm
    exact (e b).trans (e i0).symm

private lemma rvq_norm_expand {n B : ℕ} (hB : 0 < B) (z : Fin B → (Fin n → ℝ)) (m : Fin n → ℝ)
    (T : ℝ) :
    (m + (1 / (B : ℝ)) • ∑ b, z b) ⬝ᵥ (m + (1 / (B : ℝ)) • ∑ b, z b)
      = (m ⬝ᵥ m + T / B) + (2 / B) * (m ⬝ᵥ ∑ b, z b)
        + (1 / (B : ℝ) ^ 2) * (∑ b : Fin B, ((∑ i, z b i ^ 2) - T)
          + ∑ b : Fin B, ∑ b' ∈ Finset.univ.filter (fun b' : Fin B => b' ≠ b), (z b ⬝ᵥ z b')) := by
  have hB' : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  have hSS : (∑ b, z b) ⬝ᵥ (∑ b, z b) = ∑ b : Fin B, (∑ i, z b i ^ 2)
      + ∑ b : Fin B, ∑ b' ∈ Finset.univ.filter (fun b' : Fin B => b' ≠ b), (z b ⬝ᵥ z b') := by
    rw [sum_dotProduct]
    simp_rw [dotProduct_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b' => b' = b)]
    congr 1
    · simp [dotProduct, pow_two, Finset.filter_eq']
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (∑ b, z b) m, hSS, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

private lemma rvq_lint_comb {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f u1 u2 u3 : Ω → ℝ) (hu1 : Measurable u1) (hu2 : Measurable u2) (hu3 : Measurable u3)
    (hu1' : ∀ ω, 0 ≤ u1 ω) (hu2' : ∀ ω, 0 ≤ u2 ω) (hu3' : ∀ ω, 0 ≤ u3 ω)
    (c0 c1 c2 c3 E1 E2 E3 : ℝ) (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3)
    (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) (hE3 : 0 ≤ E3)
    (hpt : ∀ ω, f ω ≤ c0 + c1 * u1 ω + c2 * u2 ω + c3 * u3 ω)
    (b1 : ∫⁻ ω, ENNReal.ofReal (u1 ω) ∂P ≤ ENNReal.ofReal E1)
    (b2 : ∫⁻ ω, ENNReal.ofReal (u2 ω) ∂P ≤ ENNReal.ofReal E2)
    (b3 : ∫⁻ ω, ENNReal.ofReal (u3 ω) ∂P ≤ ENNReal.ofReal E3) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal (c0 + c1 * E1 + c2 * E2 + c3 * E3) := by
  have m1 := hu1.ennreal_ofReal.const_mul (ENNReal.ofReal c1)
  have m2 := hu2.ennreal_ofReal.const_mul (ENNReal.ofReal c2)
  have m3 := hu3.ennreal_ofReal.const_mul (ENNReal.ofReal c3)
  calc ∫⁻ ω, ENNReal.ofReal (f ω) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal c0 + ENNReal.ofReal c1 * ENNReal.ofReal (u1 ω)
          + ENNReal.ofReal c2 * ENNReal.ofReal (u2 ω)
          + ENNReal.ofReal c3 * ENNReal.ofReal (u3 ω)) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_mul h3,
          ← ENNReal.ofReal_add h0 (by have := hu1' ω; positivity),
          ← ENNReal.ofReal_add (by have := hu1' ω; positivity) (by have := hu2' ω; positivity),
          ← ENNReal.ofReal_add (by have := hu1' ω; have := hu2' ω; positivity)
            (by have := hu3' ω; positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal c0 + ENNReal.ofReal c1 * ∫⁻ ω, ENNReal.ofReal (u1 ω) ∂P
          + ENNReal.ofReal c2 * ∫⁻ ω, ENNReal.ofReal (u2 ω) ∂P
          + ENNReal.ofReal c3 * ∫⁻ ω, ENNReal.ofReal (u3 ω) ∂P := by
        rw [lintegral_add_right _ m3, lintegral_add_right _ m2, lintegral_add_right _ m1,
          lintegral_const, lintegral_const_mul _ hu1.ennreal_ofReal,
          lintegral_const_mul _ hu2.ennreal_ofReal, lintegral_const_mul _ hu3.ennreal_ofReal]
        simp
    _ ≤ ENNReal.ofReal c0 + ENNReal.ofReal c1 * ENNReal.ofReal E1
          + ENNReal.ofReal c2 * ENNReal.ofReal E2 + ENNReal.ofReal c3 * ENNReal.ofReal E3 := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_mul h3,
          ← ENNReal.ofReal_add h0 (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

private lemma rvq_d2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : Ω → ℝ) (hd : Measurable d) (k Q4 : ℝ) (hk : 0 < k) (hQ4 : 0 ≤ Q4)
    (h4 : ∫⁻ ω, ENNReal.ofReal (d ω ^ 4) ∂P ≤ ENNReal.ofReal (Q4 / k ^ 2)) :
    ∫⁻ ω, ENNReal.ofReal (d ω ^ 2) ∂P ≤ ENNReal.ofReal ((Q4 + 1) / 2 / k) := by
  have := rvq_lint_comb P (fun ω => d ω ^ 2) (fun ω => d ω ^ 4) (fun _ => 0) (fun _ => 0)
    (hd.pow_const 4) measurable_const measurable_const (fun ω => by positivity) (fun _ => le_rfl)
    (fun _ => le_rfl) (1 / (2 * k)) (k / 2) 0 0 (Q4 / k ^ 2) 0 0 (by positivity) (by positivity)
    le_rfl le_rfl (by positivity) le_rfl le_rfl (fun ω => by
      simp only [mul_zero, add_zero]
      have : 0 ≤ (k * d ω ^ 2 - 1) ^ 2 := sq_nonneg _
      have e : d ω ^ 2 ≤ 1 / (2 * k) + k / 2 * d ω ^ 4 := by
        rw [← sub_nonneg]
        have : 1 / (2 * k) + k / 2 * d ω ^ 4 - d ω ^ 2 = (k * d ω ^ 2 - 1) ^ 2 / (2 * k) := by
          field_simp; ring
        rw [this]; positivity
      exact e) h4 (by simp) (by simp)
  refine this.trans (le_of_eq ?_)
  congr 1
  field_simp
  ring

private lemma rvq_pow4_four (x y z w : ℝ) :
    (x + y + z + w) ^ 4 ≤ 64 * (x ^ 4 + y ^ 4 + z ^ 4 + w ^ 4) := by
  have h1 : (x + y + z + w) ^ 2 ≤ 4 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - w), sq_nonneg (y - z),
      sq_nonneg (y - w), sq_nonneg (z - w)]
  have h2 : (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) ^ 2 ≤ 4 * (x ^ 4 + y ^ 4 + z ^ 4 + w ^ 4) := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 - z ^ 2), sq_nonneg (x ^ 2 - w ^ 2),
      sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (y ^ 2 - w ^ 2), sq_nonneg (z ^ 2 - w ^ 2)]
  have h3 : ((x + y + z + w) ^ 2) ^ 2 ≤ (4 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  nlinarith

private lemma rvq_trace_TD {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) :
    (TD μ D).trace = ∑ i, μ i * (μ i * ∑ j, D i j ^ 2) := by
  unfold TD
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.mul_apply, pow_two]
  ring

private lemma rvq_trace_cov (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m) :
    ∑ i, colCov μ D j i i = (twoR μ D + 2 * colC μ D j) * (∑ i, μ i) + 2 * (TD μ D).trace
      + 3 * ∑ i, colMeanVec μ D j i ^ 2 := by
  have h := (lem_app_sgd_column_i P μ D hP j).2
  have : ∀ i, colCov μ D j i i = (twoR μ D + 2 * colC μ D j) * μ i + 2 * TD μ D i i
      + 3 * colMeanVec μ D j i ^ 2 := by
    intro i; rw [h i i]; simp [pow_two]
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  rfl

private lemma rvq_bias (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m)
    (hm : ∑ i, colMeanVec μ D j i ^ 2 ≤ P.L ^ 2 * P.Ccol / (kOf n m B : ℝ)) :
    0 ≤ (∑ i, colMeanVec μ D j i ^ 2 + (∑ i, colCov μ D j i i) / (B : ℝ)) - haarX0 B μ D ∧
    (∑ i, colMeanVec μ D j i ^ 2 + (∑ i, colCov μ D j i i) / (B : ℝ)) - haarX0 B μ D
      ≤ (2 * P.L ^ 2 * P.K * P.Ccol + 2 * haarH0 P + 4 * (P.L ^ 2 * P.Ccol))
          / (kOf n m B : ℝ) := by
  have hbd := haar_bounds P n m B μ D hP
  have hP' := hP
  unfold def_app_sgd_state_law at hP'
  obtain ⟨⟨hn0, hm0, hB0⟩, hk2, hnK, -, hBK, hμ, -, -, hcol⟩ := hP'
  have hk : (2 : ℝ) ≤ (kOf n m B : ℝ) := by exact_mod_cast hk2
  have hkpos : (0 : ℝ) < (kOf n m B : ℝ) := by linarith
  have hkB : (kOf n m B : ℝ) ≤ (B : ℝ) := by
    have : kOf n m B ≤ B := le_trans (min_le_right _ _) (min_le_right _ _)
    exact_mod_cast this
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB0
  have hLpos : 0 < P.L := lt_of_lt_of_le P.c_pos P.c_le_L
  have hmu0 : ∀ i, 0 ≤ μ i := fun i => le_trans P.c_pos.le (hμ i).1
  have hmuL : ∀ i, μ i ≤ P.L := fun i => (hμ i).2
  set k : ℝ := (kOf n m B : ℝ) with hkdef
  set Lt : ℝ := ∑ i, μ i with hLt
  set mm : ℝ := ∑ i, colMeanVec μ D j i ^ 2 with hmm
  set C : ℝ := colC μ D j with hC
  have hmm0 : 0 ≤ mm := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hLt0 : 0 ≤ Lt := Finset.sum_nonneg fun i _ => hmu0 i
  have hLt1 : Lt ≤ (n : ℝ) * P.L := by
    calc Lt ≤ ∑ _i : Fin n, P.L := Finset.sum_le_sum fun i _ => hmuL i
      _ = (n : ℝ) * P.L := by simp
  have hLt2 : Lt ≤ P.K * k * P.L := by
    calc Lt ≤ (n : ℝ) * P.L := hLt1
      _ ≤ P.K * k * P.L := by gcongr
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => mul_nonneg (hmu0 i) (sq_nonneg _)
  have hC1 : C ≤ P.L * P.Ccol / k := by
    calc C = ∑ i, μ i * D i j ^ 2 := rfl
      _ ≤ ∑ i, P.L * D i j ^ 2 := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hmuL i) (sq_nonneg _)
      _ = P.L * ∑ i, D i j ^ 2 := by rw [Finset.mul_sum]
      _ ≤ P.L * (P.Ccol / k) := mul_le_mul_of_nonneg_left (hcol j) hLpos.le
      _ = P.L * P.Ccol / k := by ring
  have hTD0 : 0 ≤ (TD μ D).trace := by
    rw [rvq_trace_TD]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hmu0 i)
      (mul_nonneg (hmu0 i) (Finset.sum_nonneg fun j _ => sq_nonneg _))
  have hTD1 : (TD μ D).trace ≤ haarH0 P := hbd.2.2.1
  have hT := rvq_trace_cov P μ D hP j
  unfold haarX0
  rw [hT]
  have e1 : mm + ((twoR μ D + 2 * C) * Lt + 2 * (TD μ D).trace + 3 * mm) / (B : ℝ)
      - twoR μ D * Lt / (B : ℝ)
      = mm + (2 * C * Lt + 2 * (TD μ D).trace + 3 * mm) / (B : ℝ) := by
    field_simp; ring
  rw [show mm + ((twoR μ D + 2 * C) * Lt + 2 * (TD μ D).trace + 3 * mm) / (B : ℝ)
      - twoR μ D * Lt / (B : ℝ) = _ from e1]
  constructor
  · positivity
  · have hCL : C * Lt ≤ P.L ^ 2 * P.Ccol * P.K := by
      calc C * Lt ≤ (P.L * P.Ccol / k) * (P.K * k * P.L) :=
            mul_le_mul hC1 hLt2 hLt0 (by positivity [P.Ccol_pos])
        _ = P.L ^ 2 * P.Ccol * P.K := by field_simp
    have hnum : 2 * C * Lt + 2 * (TD μ D).trace + 3 * mm
        ≤ 2 * P.L ^ 2 * P.K * P.Ccol + 2 * haarH0 P + 3 * (P.L ^ 2 * P.Ccol) := by
      have : mm ≤ P.L ^ 2 * P.Ccol := by
        refine hm.trans ?_
        rw [div_le_iff₀ hkpos]
        nlinarith [mul_pos (pow_pos hLpos 2) P.Ccol_pos]
      nlinarith
    have hnum0 : 0 ≤ 2 * C * Lt + 2 * (TD μ D).trace + 3 * mm := by positivity
    have h1 : (2 * C * Lt + 2 * (TD μ D).trace + 3 * mm) / (B : ℝ)
        ≤ (2 * P.L ^ 2 * P.K * P.Ccol + 2 * haarH0 P + 3 * (P.L ^ 2 * P.Ccol)) / k := by
      calc _ ≤ (2 * C * Lt + 2 * (TD μ D).trace + 3 * mm) / k :=
            div_le_div_of_nonneg_left hnum0 hkpos hkB
        _ ≤ _ := by gcongr
    calc mm + (2 * C * Lt + 2 * (TD μ D).trace + 3 * mm) / (B : ℝ)
        ≤ P.L ^ 2 * P.Ccol / k
          + (2 * P.L ^ 2 * P.K * P.Ccol + 2 * haarH0 P + 3 * (P.L ^ 2 * P.Ccol)) / k :=
          add_le_add hm h1
      _ = _ := by ring

private lemma rvq_x0_lower (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D) :
    haarPminus P * P.c / P.K ≤ haarX0 B μ D := by
  have hbd := haar_bounds P n m B μ D hP
  have hP' := hP
  unfold def_app_sgd_state_law at hP'
  obtain ⟨⟨hn0, hm0, hB0⟩, hk2, hnK, -, hBK, hμ, -, -, hcol⟩ := hP'
  have hkn : (kOf n m B : ℝ) ≤ (n : ℝ) := by
    have : kOf n m B ≤ n := min_le_left _ _
    exact_mod_cast this
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB0
  have hKpos : 0 < P.K := lt_of_lt_of_le one_pos P.one_le_K
  have hPm : 0 < haarPminus P := by unfold haarPminus; have := P.c_pos; have := P.fMin_pos; positivity
  have hBn : (B : ℝ) ≤ P.K * n := hBK.trans (by gcongr)
  have hLt : (n : ℝ) * P.c ≤ ∑ i, μ i := by
    calc (n : ℝ) * P.c = ∑ _i : Fin n, P.c := by simp
      _ ≤ ∑ i, μ i := Finset.sum_le_sum fun i _ => (hμ i).1
  unfold haarX0
  have h1 : haarPminus P * ((n : ℝ) * P.c) ≤ twoR μ D * ∑ i, μ i :=
    mul_le_mul hbd.1 hLt (by have := P.c_pos; positivity) (hPm.le.trans hbd.1)
  calc haarPminus P * P.c / P.K = haarPminus P * ((n : ℝ) * P.c) / (P.K * n) := by
        field_simp
    _ ≤ twoR μ D * (∑ i, μ i) / (P.K * n) := by gcongr
    _ ≤ twoR μ D * (∑ i, μ i) / (B : ℝ) := by
        apply div_le_div_of_nonneg_left (le_trans (mul_nonneg hPm.le (by have := P.c_pos; positivity)) h1) hBpos hBn

private lemma rvq_arith (A4 A8 K M b0 mm n B k w : ℝ) (hA4 : 0 ≤ A4) (hA8 : 0 ≤ A8) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hb0 : 0 ≤ b0) (hk1 : 1 ≤ k) (hkB : k ≤ B) (hn0 : 0 ≤ n) (hnK : n ≤ K * k)
    (hmm0 : 0 ≤ mm) (hmm : mm ≤ M / k) (hw0 : 0 ≤ w) (hw : w ≤ b0 / k) :
    64 * w ^ 4 + 64 * (2 / B) ^ 4 * (3 * A4 * B ^ 2 * mm ^ 2)
      + 64 * (1 / B ^ 2) ^ 4 * ((16 * A8 + 3 * A4 ^ 2) * B ^ 2 * n ^ 4)
      + 64 * (1 / B ^ 2) ^ 4 * (144 * A4 ^ 2 * B ^ 4 * n ^ 2)
    ≤ (64 * b0 ^ 4 + 3072 * A4 * M ^ 2 + 64 * (16 * A8 + 3 * A4 ^ 2) * K ^ 4
        + 9216 * A4 ^ 2 * K ^ 2) / k ^ 2 := by
  have hk0 : 0 < k := by linarith
  have hB0 : 0 < B := by linarith
  have hk2 : 1 ≤ k ^ 2 := by nlinarith
  -- term 0
  have t0 : 64 * w ^ 4 ≤ 64 * b0 ^ 4 / k ^ 2 := by
    have h1 : w ^ 4 ≤ (b0 / k) ^ 4 := pow_le_pow_left₀ hw0 hw 4
    have h2 : (b0 / k) ^ 4 ≤ b0 ^ 4 / k ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ b0 ^ 4 := by positivity
      nlinarith [mul_nonneg this (sub_nonneg.2 hk2)]
    calc 64 * w ^ 4 ≤ 64 * (b0 ^ 4 / k ^ 2) := by linarith
      _ = _ := by ring
  -- term 1
  have t1 : 64 * (2 / B) ^ 4 * (3 * A4 * B ^ 2 * mm ^ 2) ≤ 3072 * A4 * M ^ 2 / k ^ 2 := by
    have e : 64 * (2 / B) ^ 4 * (3 * A4 * B ^ 2 * mm ^ 2) = 3072 * A4 * mm ^ 2 / B ^ 2 := by
      field_simp; ring
    rw [e]
    have h1 : mm ^ 2 ≤ (M / k) ^ 2 := pow_le_pow_left₀ hmm0 hmm 2
    have h2 : 3072 * A4 * mm ^ 2 / B ^ 2 ≤ 3072 * A4 * (M / k) ^ 2 / k ^ 2 := by
      calc 3072 * A4 * mm ^ 2 / B ^ 2 ≤ 3072 * A4 * (M / k) ^ 2 / B ^ 2 := by gcongr
        _ ≤ 3072 * A4 * (M / k) ^ 2 / k ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact pow_le_pow_left₀ hk0.le hkB 2
    refine h2.trans ?_
    rw [div_pow, mul_div_assoc', div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ 3072 * A4 * M ^ 2 := by positivity
    nlinarith [mul_nonneg this (sub_nonneg.2 hk2), sq_nonneg k, mul_nonneg this (sq_nonneg k)]
  -- term 2
  have t2 : 64 * (1 / B ^ 2) ^ 4 * ((16 * A8 + 3 * A4 ^ 2) * B ^ 2 * n ^ 4)
      ≤ 64 * (16 * A8 + 3 * A4 ^ 2) * K ^ 4 / k ^ 2 := by
    have e : 64 * (1 / B ^ 2) ^ 4 * ((16 * A8 + 3 * A4 ^ 2) * B ^ 2 * n ^ 4)
        = 64 * (16 * A8 + 3 * A4 ^ 2) * n ^ 4 / B ^ 6 := by field_simp
    rw [e]
    have h1 : n ^ 4 ≤ (K * k) ^ 4 := pow_le_pow_left₀ hn0 hnK 4
    have h2 : k ^ 6 ≤ B ^ 6 := pow_le_pow_left₀ hk0.le hkB 6
    calc 64 * (16 * A8 + 3 * A4 ^ 2) * n ^ 4 / B ^ 6
        ≤ 64 * (16 * A8 + 3 * A4 ^ 2) * (K * k) ^ 4 / B ^ 6 := by gcongr
      _ ≤ 64 * (16 * A8 + 3 * A4 ^ 2) * (K * k) ^ 4 / k ^ 6 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h2
      _ = _ := by field_simp
  -- term 3
  have t3 : 64 * (1 / B ^ 2) ^ 4 * (144 * A4 ^ 2 * B ^ 4 * n ^ 2)
      ≤ 9216 * A4 ^ 2 * K ^ 2 / k ^ 2 := by
    have e : 64 * (1 / B ^ 2) ^ 4 * (144 * A4 ^ 2 * B ^ 4 * n ^ 2)
        = 9216 * A4 ^ 2 * n ^ 2 / B ^ 4 := by field_simp; ring
    rw [e]
    have h1 : n ^ 2 ≤ (K * k) ^ 2 := pow_le_pow_left₀ hn0 hnK 2
    have h2 : k ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ hk0.le hkB 4
    calc 9216 * A4 ^ 2 * n ^ 2 / B ^ 4 ≤ 9216 * A4 ^ 2 * (K * k) ^ 2 / B ^ 4 := by gcongr
      _ ≤ 9216 * A4 ^ 2 * (K * k) ^ 2 / k ^ 4 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h2
      _ = _ := by field_simp
  calc _ ≤ 64 * b0 ^ 4 / k ^ 2 + 3072 * A4 * M ^ 2 / k ^ 2
        + 64 * (16 * A8 + 3 * A4 ^ 2) * K ^ 4 / k ^ 2 + 9216 * A4 ^ 2 * K ^ 2 / k ^ 2 := by linarith
    _ = _ := by ring

private lemma rvp_ratio_pw (x n x0 a0 s : ℝ) (hx : 0 ≤ x) (hxn : x ≤ n) (ha0 : 0 < a0)
    (hax : a0 ≤ x0) (hs : 0 < s) :
    |x / n - x / x0| ≤ (1 / a0 ^ 2) * (s * x ^ 2 + (n - x0) ^ 2 / s)
      + (16 * (1 + 1 / (2 * a0)) / a0 ^ 4) * (n - x0) ^ 4 + x ^ 2 / (2 * a0) := by
  have hx0 : 0 < x0 := lt_of_lt_of_le ha0 hax
  have hn0 : 0 ≤ n := le_trans hx hxn
  have t1 : 0 ≤ (1 / a0 ^ 2) * (s * x ^ 2 + (n - x0) ^ 2 / s) := by positivity
  have t2 : 0 ≤ (16 * (1 + 1 / (2 * a0)) / a0 ^ 4) * (n - x0) ^ 4 := by positivity
  have t3 : 0 ≤ x ^ 2 / (2 * a0) := by positivity
  by_cases hn : x0 / 2 ≤ n
  · have hnp : 0 < n := by linarith
    have e : x / n - x / x0 = x * (x0 - n) / (n * x0) := by field_simp
    rw [e, abs_div, abs_mul, abs_of_nonneg hx, abs_of_pos (mul_pos hnp hx0)]
    have h1 : x * |x0 - n| / (n * x0) ≤ 2 * x * |n - x0| / a0 ^ 2 := by
      rw [div_le_div_iff₀ (mul_pos hnp hx0) (by positivity), abs_sub_comm]
      have : a0 ^ 2 ≤ x0 ^ 2 := by nlinarith
      have h2 : 0 ≤ x * |n - x0| := by positivity
      nlinarith [mul_nonneg h2 (sub_nonneg.2 this), mul_nonneg h2 (sub_nonneg.2 hn),
        mul_nonneg h2 hx0.le]
    have h3 : 2 * x * |n - x0| ≤ s * x ^ 2 + (n - x0) ^ 2 / s := by
      rw [← sq_abs (n - x0)]
      have : 2 * x * |n - x0| * s ≤ s ^ 2 * x ^ 2 + |n - x0| ^ 2 := by
        nlinarith [sq_nonneg (s * x - |n - x0|)]
      rw [← sub_nonneg]
      have : 0 ≤ (s ^ 2 * x ^ 2 + |n - x0| ^ 2 - 2 * x * |n - x0| * s) / s := by
        apply div_nonneg <;> nlinarith
      have e2 : (s ^ 2 * x ^ 2 + |n - x0| ^ 2 - 2 * x * |n - x0| * s) / s
          = s * x ^ 2 + |n - x0| ^ 2 / s - 2 * x * |n - x0| := by field_simp
      linarith
    calc x * |x0 - n| / (n * x0) ≤ 2 * x * |n - x0| / a0 ^ 2 := h1
      _ ≤ (s * x ^ 2 + (n - x0) ^ 2 / s) / a0 ^ 2 := by gcongr
      _ = (1 / a0 ^ 2) * (s * x ^ 2 + (n - x0) ^ 2 / s) := by ring
      _ ≤ _ := by linarith
  · have hn := not_le.mp hn
    by_cases hn0' : n = 0
    · have : x = 0 := by linarith
      subst this; simp [hn0']
      positivity
    · have hnp : 0 < n := lt_of_le_of_ne hn0 (Ne.symm hn0')
      have hxn1 : x / n ≤ 1 := (div_le_one hnp).2 hxn
      have hxn0 : 0 ≤ x / n := by positivity
      have hxx : 0 ≤ x / x0 := by positivity
      have hxa : x / x0 ≤ x / a0 := div_le_div_of_nonneg_left hx ha0 hax
      have h4 : a0 ^ 4 / 16 ≤ (n - x0) ^ 4 := by
        have : a0 / 2 ≤ x0 - n := by linarith
        have h5 : (a0 / 2) ^ 4 ≤ (x0 - n) ^ 4 := pow_le_pow_left₀ (by positivity) this 4
        calc a0 ^ 4 / 16 = (a0 / 2) ^ 4 := by ring
          _ ≤ (x0 - n) ^ 4 := h5
          _ = (n - x0) ^ 4 := by ring
      have h6 : 1 ≤ 16 / a0 ^ 4 * (n - x0) ^ 4 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
      have h7 : x / a0 ≤ x ^ 2 / (2 * a0) + 1 / (2 * a0) := by
        rw [← add_div]; rw [div_le_div_iff₀ ha0 (by positivity)]
        nlinarith [sq_nonneg (x - 1), ha0]
      have h8 : abs (x / n - x / x0) ≤ x / n + x / x0 := by
        rw [abs_le]; constructor <;> linarith
      have h9 : 1 / (2 * a0) ≤ 1 / (2 * a0) * (16 / a0 ^ 4 * (n - x0) ^ 4) := by
        have : 0 ≤ 1 / (2 * a0) := by positivity
        nlinarith
      have e3 : (16 * (1 + 1 / (2 * a0)) / a0 ^ 4) * (n - x0) ^ 4
          = 16 / a0 ^ 4 * (n - x0) ^ 4 + 1 / (2 * a0) * (16 / a0 ^ 4 * (n - x0) ^ 4) := by ring
      linarith

private lemma rvp_ratio_abs {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X N : Ω → ℝ) (hXm : Measurable X) (hNm : Measurable N) (hX0 : ∀ ω, 0 ≤ X ω)
    (hXN : ∀ ω, X ω ≤ N ω) (x0 a0 s k H4 S2 Q4 : ℝ) (ha0 : 0 < a0) (hax : a0 ≤ x0)
    (hs : 0 < s) (hk : 0 < k) (hH4 : 0 ≤ H4) (hS2 : 0 ≤ S2) (hQ4 : 0 ≤ Q4)
    (hX2 : ∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂P ≤ ENNReal.ofReal (H4 / k ^ 2))
    (hd2 : ∫⁻ ω, ENNReal.ofReal ((N ω - x0) ^ 2) ∂P ≤ ENNReal.ofReal (S2 / k))
    (hd4 : ∫⁻ ω, ENNReal.ofReal ((N ω - x0) ^ 4) ∂P ≤ ENNReal.ofReal (Q4 / k ^ 2)) :
    ∫⁻ ω, ENNReal.ofReal |X ω / N ω - X ω / x0| ∂P
      ≤ ENNReal.ofReal ((1 / a0 ^ 2) * s * (H4 / k ^ 2) + (1 / a0 ^ 2) / s * (S2 / k)
          + (16 * (1 + 1 / (2 * a0)) / a0 ^ 4) * (Q4 / k ^ 2) + 1 / (2 * a0) * (H4 / k ^ 2)) := by
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 1 / a0 ^ 2 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = 16 * (1 + 1 / (2 * a0)) / a0 ^ 4 := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = 1 / (2 * a0) := ⟨_, rfl⟩
  rw [← hα, ← hβ, ← hγ]
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
  have hmX2 : Measurable fun ω => ENNReal.ofReal (X ω ^ 2) := (hXm.pow_const 2).ennreal_ofReal
  have hmd2 : Measurable fun ω => ENNReal.ofReal ((N ω - x0) ^ 2) :=
    ((hNm.sub_const x0).pow_const 2).ennreal_ofReal
  have hmd4 : Measurable fun ω => ENNReal.ofReal ((N ω - x0) ^ 4) :=
    ((hNm.sub_const x0).pow_const 4).ennreal_ofReal
  have hpt : ∀ ω, ENNReal.ofReal |X ω / N ω - X ω / x0|
      ≤ ENNReal.ofReal (α * s) * ENNReal.ofReal (X ω ^ 2)
        + ENNReal.ofReal (α / s) * ENNReal.ofReal ((N ω - x0) ^ 2)
        + ENNReal.ofReal β * ENNReal.ofReal ((N ω - x0) ^ 4)
        + ENNReal.ofReal γ * ENNReal.ofReal (X ω ^ 2) := by
    intro ω
    have h0 := rvp_ratio_pw (X ω) (N ω) x0 a0 s (hX0 ω) (hXN ω) ha0 hax hs
    have h : |X ω / N ω - X ω / x0| ≤ α * (s * X ω ^ 2 + (N ω - x0) ^ 2 / s)
        + β * (N ω - x0) ^ 4 + γ * X ω ^ 2 := by
      rw [hα, hβ, hγ]; convert h0 using 2; ring
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hβ0, ← ENNReal.ofReal_mul hγ0, ← ENNReal.ofReal_add (by positivity)
        (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : α * s * X ω ^ 2 + α / s * (N ω - x0) ^ 2 = α * (s * X ω ^ 2 + (N ω - x0) ^ 2 / s) := by
      field_simp
    linarith
  have ma := hmX2.const_mul (ENNReal.ofReal (α * s))
  have mb := hmd2.const_mul (ENNReal.ofReal (α / s))
  have mc := hmd4.const_mul (ENNReal.ofReal β)
  have md := hmX2.const_mul (ENNReal.ofReal γ)
  calc ∫⁻ ω, ENNReal.ofReal |X ω / N ω - X ω / x0| ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (α * s) * ENNReal.ofReal (X ω ^ 2)
        + ENNReal.ofReal (α / s) * ENNReal.ofReal ((N ω - x0) ^ 2)
        + ENNReal.ofReal β * ENNReal.ofReal ((N ω - x0) ^ 4)
        + ENNReal.ofReal γ * ENNReal.ofReal (X ω ^ 2)) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (α * s) * ∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂P
        + ENNReal.ofReal (α / s) * ∫⁻ ω, ENNReal.ofReal ((N ω - x0) ^ 2) ∂P
        + ENNReal.ofReal β * ∫⁻ ω, ENNReal.ofReal ((N ω - x0) ^ 4) ∂P
        + ENNReal.ofReal γ * ∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂P := by
      rw [lintegral_add_right _ md, lintegral_add_right _ mc, lintegral_add_right _ mb,
        lintegral_const_mul _ hmX2,
        lintegral_const_mul _ hmd2, lintegral_const_mul _ hmd4, lintegral_const_mul _ hmX2]
    _ ≤ ENNReal.ofReal (α * s) * ENNReal.ofReal (H4 / k ^ 2)
        + ENNReal.ofReal (α / s) * ENNReal.ofReal (S2 / k)
        + ENNReal.ofReal β * ENNReal.ofReal (Q4 / k ^ 2)
        + ENNReal.ofReal γ * ENNReal.ofReal (H4 / k ^ 2) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul hβ0, ← ENNReal.ofReal_mul hγ0,
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]


private lemma rvq_cent (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m)
    (i : Fin n) : ∫ p, colZ μ D j p i ∂(gaussBatch n m) = 0 := by
  have : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  have h := (lem_app_sgd_column_i P μ D hP j).1 i
  have e : (fun p => colZ μ D j p i)
      = fun p => colSample μ D j p i - colMeanVec μ D j i := by
    funext p; simp [colZ]
  rw [e]
  by_cases hI : Integrable (fun p => colSample μ D j p i) (gaussBatch n m)
  · rw [integral_sub hI (integrable_const _), h]; simp
  · have : ¬ Integrable (fun p => colSample μ D j p i - colMeanVec μ D j i) (gaussBatch n m) := by
      intro h2
      apply hI
      exact (h2.add (integrable_const (colMeanVec μ D j i))).congr
        (Filter.Eventually.of_forall fun p => by simp)
    exact integral_undef this


private lemma rvq_pow4_two (p q : ℝ) : (p + q) ^ 4 ≤ 8 * (p ^ 4 + q ^ 4) := by
  have h1 : (p + q) ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) := by nlinarith [sq_nonneg (p - q)]
  have h2 : (p ^ 2 + q ^ 2) ^ 2 ≤ 2 * (p ^ 4 + q ^ 4) := by nlinarith [sq_nonneg (p ^ 2 - q ^ 2)]
  have h3 : ((p + q) ^ 2) ^ 2 ≤ (2 * (p ^ 2 + q ^ 2)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
  nlinarith

private lemma rvq_final_arith (a0 H4 S2 Q4 k s : ℝ) (hs : 0 < s) (hks : s ^ 2 = k) :
    1 / a0 ^ 2 * s * (H4 / k ^ 2) + 1 / a0 ^ 2 / s * (S2 / k)
      + 16 * (1 + 1 / (2 * a0)) / a0 ^ 4 * (Q4 / k ^ 2) + 1 / (2 * a0) * (H4 / k ^ 2)
    = (1 / a0 ^ 2 * (H4 + S2)) / (k * s)
      + (16 * (1 + 1 / (2 * a0)) / a0 ^ 4 * Q4 + 1 / (2 * a0) * H4) / k ^ 2 := by
  subst hks
  by_cases ha : a0 = 0
  · subst ha; simp
  · field_simp
    ring

private lemma rvq_main (P : HaarParams) (A4 A8 : ℝ) (hA4 : 0 ≤ A4) (hA8 : 0 ≤ A8)
    (H4 Q4 : ℝ) (hH4 : H4 = 8 * (P.L ^ 2 * P.Ccol) ^ 2 + 24 * A4)
    (hQ4 : Q4 = 64 * (2 * P.L ^ 2 * P.K * P.Ccol + 2 * haarH0 P + 4 * (P.L ^ 2 * P.Ccol)) ^ 4
        + 3072 * A4 * (P.L ^ 2 * P.Ccol) ^ 2 + 64 * (16 * A8 + 3 * A4 ^ 2) * P.K ^ 4
        + 9216 * A4 ^ 2 * P.K ^ 2)
    {n m B : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m) (i : Fin n)
    (hdir4 : ∀ a : Fin n → ℝ,
      ∫⁻ p, ENNReal.ofReal ((a ⬝ᵥ colZ μ D j p) ^ 4) ∂(gaussBatch n m)
        ≤ ENNReal.ofReal (A4 * (∑ i, a i ^ 2) ^ 2))
    (hdir8 : ∀ a : Fin n → ℝ,
      ∫⁻ p, ENNReal.ofReal ((a ⬝ᵥ colZ μ D j p) ^ 8) ∂(gaussBatch n m)
        ≤ ENNReal.ofReal (A8 * (∑ i, a i ^ 2) ^ 4))
    (hvec4 : ∫⁻ p, ENNReal.ofReal ((∑ i, colZ μ D j p i ^ 2) ^ 2) ∂(gaussBatch n m)
      ≤ ENNReal.ofReal (A4 * (n : ℝ) ^ 2))
    (hvec8 : ∫⁻ p, ENNReal.ofReal ((∑ i, colZ μ D j p i ^ 2) ^ 4) ∂(gaussBatch n m)
      ≤ ENNReal.ofReal (A8 * (n : ℝ) ^ 4))
    (hm : ∑ i, colMeanVec μ D j i ^ 2 ≤ P.L ^ 2 * P.Ccol / (kOf n m B : ℝ)) :
    ∫⁻ β, ENNReal.ofReal
        |hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j) - hCol μ D β j i ^ 2 / haarX0 B μ D|
      ∂(batchLaw n m B)
      ≤ ENNReal.ofReal ((1 / (haarPminus P * P.c / P.K) ^ 2 * (H4 + (Q4 + 1) / 2))
            / ((kOf n m B : ℝ) * Real.sqrt (kOf n m B : ℝ))
          + (16 * (1 + 1 / (2 * (haarPminus P * P.c / P.K))) / (haarPminus P * P.c / P.K) ^ 4 * Q4
              + 1 / (2 * (haarPminus P * P.c / P.K)) * H4) / (kOf n m B : ℝ) ^ 2) := by
  have hP' := hP
  unfold def_app_sgd_state_law at hP'
  obtain ⟨⟨hn0, hm0, hB0⟩, hk2, hnK, -, hBK, hμ, -, -, hcol⟩ := hP'
  have hk : (2 : ℝ) ≤ (kOf n m B : ℝ) := by exact_mod_cast hk2
  have hkB : (kOf n m B : ℝ) ≤ (B : ℝ) := by
    have : kOf n m B ≤ B := le_trans (min_le_right _ _) (min_le_right _ _)
    exact_mod_cast this
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB0
  have hKpos : 0 < P.K := lt_of_lt_of_le one_pos P.one_le_K
  have hLpos : 0 < P.L := lt_of_lt_of_le P.c_pos P.c_le_L
  have hPm : 0 < haarPminus P := by
    unfold haarPminus; have := P.c_pos; have := P.fMin_pos; positivity
  have ha0 : 0 < haarPminus P * P.c / P.K := by have := P.c_pos; positivity
  have hax := rvq_x0_lower P μ D hP
  have hbias := rvq_bias P μ D hP j hm
  have hprob := rvp_batchLaw_prob n m B
  have hprobg : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  set k : ℝ := (kOf n m B : ℝ) with hkdef
  set x0 : ℝ := haarX0 B μ D with hx0
  set a0 : ℝ := haarPminus P * P.c / P.K with ha0def
  set M : ℝ := P.L ^ 2 * P.Ccol with hMdef
  set b0 : ℝ := 2 * P.L ^ 2 * P.K * P.Ccol + 2 * haarH0 P + 4 * M with hb0def
  have hMpos : 0 < M := by have := P.Ccol_pos; positivity
  have hH0 : 0 ≤ haarH0 P := by unfold haarH0; positivity
  have hb0pos : 0 ≤ b0 := by have := P.Ccol_pos; positivity
  have hkpos : 0 < k := by linarith
  -- partition
  have hpart := rvp_col_partition A4 A8 hA4 hA8 μ D j hB0 (rvq_cent P μ D hP j) hdir4 hdir8 hvec4 hvec8
  simp only at hpart
  have hS := (hpart.1 B le_rfl).2
  have hW := hpart.2.1
  have hDB := hpart.2.2
  set V := colCov μ D j with hV
  set T : ℝ := ∑ i, colCov μ D j i i with hT
  set mv := colMeanVec μ D j with hmv
  set mm : ℝ := ∑ i, mv i ^ 2 with hmmdef
  have hmm0 : 0 ≤ mm := Finset.sum_nonneg fun i _ => sq_nonneg _
  set Zs : Fin B → (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ) :=
    fun b β => colZ μ D j (β b) with hZsdef
  have hcz := rvp_colZ_meas μ D j
  have hZm : ∀ b, Measurable (Zs b) := fun b => hcz.comp (measurable_pi_apply b)
  have hSm : Measurable (partSum Zs B) := by
    unfold partSum; exact Finset.measurable_sum _ fun b _ => hZm b
  have hdotS : ∀ a : Fin n → ℝ, Measurable (fun ω => a ⬝ᵥ partSum Zs B ω) :=
    fun a => (rvq_meas_dot a).comp hSm
  have hDBm : Measurable (diagDevSum V Zs) := by
    unfold diagDevSum
    exact Finset.measurable_sum _ fun b _ => (Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (hZm b)).pow_const 2).sub_const _
  have hWm : Measurable (offDiagSum Zs) := by
    unfold offDiagSum
    refine Finset.measurable_sum _ fun b _ => Finset.measurable_sum _ fun b' _ => ?_
    unfold dotProduct
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (hZm b)).mul ((measurable_pi_apply i).comp (hZm b'))
  have hvec : ∀ ω, hCol μ D ω j = mv + (1 / (B : ℝ)) • partSum Zs B ω := by
    intro ω; funext l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact rvp_hCol_eq μ D j hB0 ω l
  have hSsum : ∀ ω, partSum Zs B ω = ∑ b, Zs b ω := by
    intro ω; unfold partSum; rw [Finset.filter_true_of_mem (fun b _ => b.2)]
  have hmm' : mv ⬝ᵥ mv = mm := by simp [dotProduct, pow_two, hmmdef]
  have hN : ∀ ω, hCol μ D ω j ⬝ᵥ hCol μ D ω j = (mm + T / B) + (2 / B) * (mv ⬝ᵥ partSum Zs B ω)
      + (1 / (B : ℝ) ^ 2) * (diagDevSum V Zs ω + offDiagSum Zs ω) := by
    intro ω
    rw [hvec ω, hSsum ω]
    refine (rvq_norm_expand hB0 (fun b => Zs b ω) mv T).trans ?_
    rw [hmm']; rfl
  obtain ⟨hw0, hw1⟩ := hbias
  have hdelta : ∀ ω, hCol μ D ω j ⬝ᵥ hCol μ D ω j - x0
      = (2 / B) * (mv ⬝ᵥ partSum Zs B ω) + (1 / (B : ℝ) ^ 2) * diagDevSum V Zs ω
        + (1 / (B : ℝ) ^ 2) * offDiagSum Zs ω + ((mm + T / B) - x0) := by
    intro ω; rw [hN ω]; ring
  -- measurability of the data
  have hcs : ∀ l, Measurable (fun p : (Fin n → ℝ) × (Fin m → ℝ) => colSample μ D j p l) := by
    intro l; unfold colSample resA; fun_prop
  have hh : ∀ l, Measurable (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => hCol μ D β j l) := by
    intro l; unfold hCol
    exact measurable_const.mul (Finset.measurable_sum _ fun a _ => (hcs l).comp (measurable_pi_apply a))
  have hNm : Measurable (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => hCol μ D β j ⬝ᵥ hCol μ D β j) := by
    unfold dotProduct; exact Finset.measurable_sum _ fun l _ => (hh l).mul (hh l)
  have hXm : Measurable (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => hCol μ D β j i ^ 2) :=
    (hh i).pow_const 2
  have hX0 : ∀ β : Fin B → (Fin n → ℝ) × (Fin m → ℝ), 0 ≤ hCol μ D β j i ^ 2 := fun β => sq_nonneg _
  have hXN : ∀ β : Fin B → (Fin n → ℝ) × (Fin m → ℝ),
      hCol μ D β j i ^ 2 ≤ hCol μ D β j ⬝ᵥ hCol μ D β j := by
    intro β
    unfold dotProduct
    calc hCol μ D β j i ^ 2 = hCol μ D β j i * hCol μ D β j i := by ring
      _ ≤ _ := Finset.single_le_sum (f := fun l => hCol μ D β j l * hCol μ D β j l)
          (fun l _ => mul_self_nonneg _) (Finset.mem_univ i)
  have hQ40 : 0 ≤ Q4 := by rw [hQ4]; positivity
  have hH40 : 0 ≤ H4 := by rw [hH4]; positivity
  -- fourth moment of the centred norm
  have hd4 : ∫⁻ β, ENNReal.ofReal ((hCol μ D β j ⬝ᵥ hCol μ D β j - x0) ^ 4) ∂(batchLaw n m B)
      ≤ ENNReal.ofReal (Q4 / k ^ 2) := by
    have hBr : (0 : ℝ) < B := hBpos
    have key := rvq_lint_comb (batchLaw n m B)
      (fun β => (hCol μ D β j ⬝ᵥ hCol μ D β j - x0) ^ 4)
      (fun ω => (mv ⬝ᵥ partSum Zs B ω) ^ 4) (fun ω => diagDevSum V Zs ω ^ 4)
      (fun ω => offDiagSum Zs ω ^ 4) ((hdotS mv).pow_const 4) (hDBm.pow_const 4)
      (hWm.pow_const 4) (fun ω => by positivity) (fun ω => by positivity) (fun ω => by positivity)
      (64 * ((mm + T / B) - x0) ^ 4) (64 * (2 / (B : ℝ)) ^ 4) (64 * (1 / (B : ℝ) ^ 2) ^ 4)
      (64 * (1 / (B : ℝ) ^ 2) ^ 4) (3 * A4 * (B : ℝ) ^ 2 * (∑ i, mv i ^ 2) ^ 2)
      ((16 * A8 + 3 * A4 ^ 2) * (B : ℝ) ^ 2 * (n : ℝ) ^ 4)
      (144 * A4 ^ 2 * (B : ℝ) ^ 4 * (n : ℝ) ^ 2) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity) (by positivity) (fun ω => by
        beta_reduce
        rw [hdelta ω]
        refine (rvq_pow4_four _ _ _ _).trans ?_
        simp only [mul_pow]
        linarith) (hS mv) hDB hW
    refine key.trans (ENNReal.ofReal_le_ofReal ?_)
    exact rvq_arith A4 A8 P.K M b0 mm n B k ((mm + T / B) - x0) hA4 hA8 hKpos.le hMpos.le hb0pos
      (by linarith) hkB (Nat.cast_nonneg _) hnK hmm0 hm hw0 hw1 |> fun h => by rw [hQ4]; exact h
  have hd2 := rvq_d2 (batchLaw n m B)
    (fun β => hCol μ D β j ⬝ᵥ hCol μ D β j - x0) (hNm.sub_const x0) k Q4 hkpos hQ40 hd4
  -- fourth moment of a coordinate
  have hX2 : ∫⁻ β, ENNReal.ofReal ((hCol μ D β j i ^ 2) ^ 2) ∂(batchLaw n m B)
      ≤ ENNReal.ofReal (H4 / k ^ 2) := by
    have hBr : (0 : ℝ) < B := hBpos
    have hsa : (∑ l, (Pi.single i (1 : ℝ) : Fin n → ℝ) l ^ 2) = 1 := by
      simp [Pi.single_apply]
    have key := rvq_lint_comb (batchLaw n m B)
      (fun β => (hCol μ D β j i ^ 2) ^ 2)
      (fun ω => ((Pi.single i (1 : ℝ) : Fin n → ℝ) ⬝ᵥ partSum Zs B ω) ^ 4) (fun _ => 0) (fun _ => 0)
      ((hdotS _).pow_const 4) measurable_const measurable_const (fun ω => by positivity)
      (fun _ => le_rfl) (fun _ => le_rfl)
      (8 * mv i ^ 4) (8 * (1 / (B : ℝ)) ^ 4) 0 0
      (3 * A4 * (B : ℝ) ^ 2 * (∑ l, (Pi.single i (1 : ℝ) : Fin n → ℝ) l ^ 2) ^ 2) 0 0
      (by positivity) (by positivity) le_rfl le_rfl (by positivity) le_rfl le_rfl
      (fun ω => by
        beta_reduce
        have e : hCol μ D ω j i = mv i + (1 / (B : ℝ)) *
            ((Pi.single i (1 : ℝ) : Fin n → ℝ) ⬝ᵥ partSum Zs B ω) := by
          rw [hvec ω]; simp [single_dotProduct]
        rw [← pow_mul, e]
        refine (rvq_pow4_two _ _).trans ?_
        rw [mul_pow]; linarith)
      (hS _) (by simp) (by simp)
    refine key.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hsa, hH4]
    have h1 : mv i ^ 2 ≤ mm := Finset.single_le_sum (f := fun l => mv l ^ 2)
      (fun l _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : mv i ^ 4 ≤ (M / k) ^ 2 := by
      calc mv i ^ 4 = (mv i ^ 2) ^ 2 := by ring
        _ ≤ mm ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
        _ ≤ (M / k) ^ 2 := pow_le_pow_left₀ hmm0 hm 2
    have h3 : 8 * (1 / (B : ℝ)) ^ 4 * (3 * A4 * (B : ℝ) ^ 2 * 1 ^ 2) ≤ 24 * A4 / k ^ 2 := by
      have e : 8 * (1 / (B : ℝ)) ^ 4 * (3 * A4 * (B : ℝ) ^ 2 * 1 ^ 2) = 24 * A4 / (B : ℝ) ^ 2 := by
        field_simp; ring
      rw [e]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hkpos.le hkB 2)
    calc 8 * mv i ^ 4 + 8 * (1 / (B : ℝ)) ^ 4 * (3 * A4 * (B : ℝ) ^ 2 * 1 ^ 2) + 0 * 0 + 0 * 0
        ≤ 8 * (M / k) ^ 2 + 24 * A4 / k ^ 2 := by linarith
      _ = (8 * M ^ 2 + 24 * A4) / k ^ 2 := by ring
  have key := rvp_ratio_abs (batchLaw n m B)
    (fun β => hCol μ D β j i ^ 2) (fun β => hCol μ D β j ⬝ᵥ hCol μ D β j) hXm hNm hX0 hXN x0 a0
    (Real.sqrt k) k H4 ((Q4 + 1) / 2) Q4 ha0 hax (Real.sqrt_pos.2 hkpos) hkpos hH40
    (by positivity) hQ40 hX2 hd2 hd4
  refine key.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  exact rvq_final_arith a0 H4 ((Q4 + 1) / 2) Q4 k (Real.sqrt k) (Real.sqrt_pos.2 hkpos)
    (Real.sq_sqrt hkpos.le)

/-- **lem:app-sgd-column-norm** `Muon.SignSGD.lem_app_sgd_column_norm`.

cr-2026-10-23. LaTeX statement (verbatim):
\begin{lemma}[Column norms]\label{lem:app-sgd-column-norm}
In the Haar model put $x_0\defeq2\cR\Tr\Lambda/B$. There are admissible
constants $C_{\rm good}$, $C_{\rm bad}$ such that, for every column $j$ and row $i$,
\begin{equation}\label{eqn:app-sgd-ratio}
\EE\Big|\frac{(h_j)_i^2}{\norm{h_j}^2}-\frac{(h_j)_i^2}{x_0}\Big|\le\frac{C_{\rm good}}{k^{3/2}}+\frac{C_{\rm bad}}{k^2}.
\end{equation}
\end{lemma}
-/
theorem lem_app_sgd_column_norm (P : HaarParams) :
    ∃ Cgood Cbad : ℝ, 0 ≤ Cgood ∧ 0 ≤ Cbad ∧
      ∀ (n m B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ),
        def_app_sgd_state_law P n m B μ D → ∀ (j : Fin m) (i : Fin n),
          (∀ᵐ β ∂(batchLaw n m B), hCol μ D β j ≠ 0) ∧
          ∫⁻ β, ENNReal.ofReal
              |hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j) - hCol μ D β j i ^ 2 / haarX0 B μ D|
            ∂(batchLaw n m B)
            ≤ ENNReal.ofReal (Cgood / ((kOf n m B : ℝ) * Real.sqrt (kOf n m B : ℝ))
                + Cbad / (kOf n m B : ℝ) ^ 2) := by
  obtain ⟨V0, A4, A8, hV0, hA4, hA8, hv⟩ := lem_app_sgd_column_v P
  obtain ⟨H4, hH4⟩ : ∃ H4 : ℝ, H4 = 8 * (P.L ^ 2 * P.Ccol) ^ 2 + 24 * A4 := ⟨_, rfl⟩
  obtain ⟨Q4, hQ4⟩ : ∃ Q4 : ℝ, Q4 = 64 * (2 * P.L ^ 2 * P.K * P.Ccol + 2 * haarH0 P
      + 4 * (P.L ^ 2 * P.Ccol)) ^ 4 + 3072 * A4 * (P.L ^ 2 * P.Ccol) ^ 2
      + 64 * (16 * A8 + 3 * A4 ^ 2) * P.K ^ 4 + 9216 * A4 ^ 2 * P.K ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 < haarPminus P * P.c / P.K := by
    have := P.c_pos; have := P.fMin_pos
    have hK : 0 < P.K := lt_of_lt_of_le one_pos P.one_le_K
    unfold haarPminus; positivity
  have hH40 : 0 ≤ H4 := by rw [hH4]; positivity
  have hQ40 : 0 ≤ Q4 := by rw [hQ4]; positivity
  refine ⟨1 / (haarPminus P * P.c / P.K) ^ 2 * (H4 + (Q4 + 1) / 2),
    16 * (1 + 1 / (2 * (haarPminus P * P.c / P.K))) / (haarPminus P * P.c / P.K) ^ 4 * Q4
      + 1 / (2 * (haarPminus P * P.c / P.K)) * H4, by positivity, by positivity, ?_⟩
  intro n m B μ D hP j i
  refine ⟨lem_app_sgd_column_iv P μ D hP j, ?_⟩
  obtain ⟨-, -, hm, hdir, hvec4, hvec8⟩ := hv n m B μ D hP j
  exact rvq_main P A4 A8 hA4 hA8 H4 Q4 hH4 hQ4 μ D hP j i (fun a => (hdir a).1)
    (fun a => (hdir a).2) hvec4 hvec8 hm

/-! ## Corrected row volatility (`thm:app-sgd-modes`) -/

/-- The row energy `𝒬_i(Δ) = ‖Δᵀ u_i‖²` as a function of `Δ` and the vector `u`
(`eqn:app-sgd-Q`/`Muon.Setup.rowQ` at explicit `u`). -/
noncomputable def sgdRowEnergy {n m : ℕ} (Δ : Matrix (Fin n) (Fin m) ℝ) (u : Fin n → ℝ) : ℝ :=
  ∑ k, ((Δᵀ *ᵥ u) k) ^ 2

/-- `𝔳_i^{raw} = E‖Sᵀ u_i‖²` in the Haar model, annealed over `ν ⊗ batch` (l. 1296,
`eqn:app-sgd-actual-row`). -/
noncomputable def haarRawRow {n m : ℕ} (B : ℕ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) : ℝ :=
  ∫ p, sgdRowEnergy (haarSign μ D p.1 p.2) (haarCol p.1 i) ∂(ν.prod (batchLaw n m B))

/-- `𝔳_i^{corr} = Nin(1 − 2/π) + (2/π) Nout [(Nin+2) μ_i / Tr Λ + (B+2Nin+3)(T_D)_{ii} / (2ℛ Tr Λ)]`
(l. 1297, `eqn:app-sgd-corr`). Here `n = Nout`, `m = Nin`. -/
noncomputable def vCorr (n m B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) :
    ℝ :=
  (m : ℝ) * (1 - 2 / Real.pi) + 2 / Real.pi * (n : ℝ) *
    (((m : ℝ) + 2) * μ i / (∑ k, μ k)
      + ((B : ℝ) + 2 * (m : ℝ) + 3) * TD μ D i i / (twoR μ D * ∑ k, μ k))

/-- `𝔡_i = μ_i 𝒩_B / √(π μ̄)` (l. 1265–1266 of the proposition, `def:app-sgd-state-law` l. 633). -/
noncomputable def haarDcoef {n : ℕ} (B : ℕ) (μ : Fin n → ℝ) (i : Fin n) : ℝ :=
  μ i * batchConst B / Real.sqrt (Real.pi * muBar μ)

private lemma rvr_hcol_meas {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (i : Fin n) :
    Measurable (fun β => hCol (B := B) μ D β j i) := by
  unfold hCol colSample resA
  fun_prop

private lemma rvr_ratio_int {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (i : Fin n) :
    Integrable (fun β => hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j))
      (batchLaw n m B) := by
  letI := rvp_batchLaw_prob n m B
  have hm : Measurable (fun β => hCol (B := B) μ D β j ⬝ᵥ hCol μ D β j) := by
    unfold dotProduct
    exact Finset.measurable_sum _ fun l _ => (rvr_hcol_meas μ D j l).mul (rvr_hcol_meas μ D j l)
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (((rvr_hcol_meas μ D j i).pow_const 2).div hm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun β => ?_)
  have h0 : 0 ≤ hCol μ D β j ⬝ᵥ hCol μ D β j := by
    unfold dotProduct; exact Finset.sum_nonneg fun l _ => mul_self_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) h0)]
  apply div_le_one_of_le₀
  · simpa [dotProduct, pow_two] using
      (Finset.single_le_sum (f := fun l => hCol μ D β j l ^ 2)
        (fun l _ => sq_nonneg _) (Finset.mem_univ i))
  · exact h0

private lemma rvr_raw_identity (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    (hν : Muon.Foundations.IsOrthHaar ν) (hP : def_app_sgd_state_law P n m B μ D)
    (i : Fin n) :
    haarRawRow B ν μ D i = (m : ℝ) * (1 - 2 / Real.pi)
      + 2 / Real.pi * (n : ℝ) * ∑ j, ∫ β,
        hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j) ∂(batchLaw n m B) := by
  simpa [haarRawRow, sgdRowEnergy, dotProduct, pow_two] using
    lem_app_sgd_reduction_v P μ D ν hν hP i

private lemma rvr_column_error {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (i : Fin n) (E : ℝ) (hE : 0 ≤ E)
    (hb : ∫⁻ β, ENNReal.ofReal
      |hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j)
        - hCol μ D β j i ^ 2 / haarX0 B μ D| ∂(batchLaw n m B) ≤ ENNReal.ofReal E) :
    Integrable (fun β => hCol μ D β j i ^ 2 / haarX0 B μ D) (batchLaw n m B) ∧
    |(∫ β, hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j) ∂(batchLaw n m B))
      - ∫ β, hCol μ D β j i ^ 2 / haarX0 B μ D ∂(batchLaw n m B)| ≤ E := by
  letI := rvp_batchLaw_prob n m B
  have hm : Measurable (fun β => hCol (B := B) μ D β j ⬝ᵥ hCol μ D β j) := by
    unfold dotProduct
    exact Finset.measurable_sum _ fun l _ => (rvr_hcol_meas μ D j l).mul (rvr_hcol_meas μ D j l)
  have hd := (((rvr_hcol_meas μ D j i).pow_const 2).div hm).sub
    (((rvr_hcol_meas μ D j i).pow_const 2).div_const (haarX0 B μ D))
  obtain ⟨hi, he⟩ := rvp_int_of_lint hd.abs (fun _ => abs_nonneg _) E hE hb
  have hi' := (integrable_norm_iff hd.aestronglyMeasurable).1
    (by simpa only [Real.norm_eq_abs] using hi)
  have hq := rvr_ratio_int (B := B) μ D j i
  have hx : Integrable (fun β => hCol μ D β j i ^ 2 / haarX0 B μ D) (batchLaw n m B) := by
    convert hq.sub hi' using 1 <;> ext β <;> dsimp <;> ring
  refine ⟨hx, ?_⟩
  rw [← integral_sub hq hx]
  exact abs_integral_le_integral_abs.trans he

private lemma rvr_error_scale (a K g b n m k : ℝ) (ha : 0 ≤ a) (hg : 0 ≤ g)
    (hb : 0 ≤ b) (hm : 0 ≤ m) (hk : 1 ≤ k) (hn : n ≤ K * k) (hn0 : 0 ≤ n) :
    a * n * (m * (g / (k * Real.sqrt k) + b / k ^ 2))
      ≤ (a * K * (g + b)) * m / Real.sqrt k := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hs0 : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
  have hs : Real.sqrt k ≤ k := Real.sqrt_le_self_iff.mpr (Or.inr hk)
  have he : g / (k * Real.sqrt k) + b / k ^ 2 ≤ (g + b) / (k * Real.sqrt k) := by
    rw [add_div]
    exact add_le_add le_rfl
      (div_le_div_of_nonneg_left hb (mul_pos hk0 hs0) (by nlinarith))
  calc
    a * n * (m * (g / (k * Real.sqrt k) + b / k ^ 2))
      ≤ a * n * (m * ((g + b) / (k * Real.sqrt k))) := by gcongr
    _ ≤ a * (K * k) * (m * ((g + b) / (k * Real.sqrt k))) := by gcongr
    _ = _ := by field_simp <;> ring

/-- **thm:app-sgd-modes**, row part (`_i`): `Muon.SignSGD.thm_app_sgd_modes_i`.

cr-2026-10-23. LaTeX statement (verbatim, all four parts of the theorem):
\begin{theorem}[Corrected row volatility]\label{thm:app-sgd-modes}
In the Haar model of \cref{def:app-sgd-state-law}, define the raw annealed
row volatility of the update and the corrected array
\begin{align}
\volraw_i&\defeq\EE\norm{S^\T u_i}^2,\label{eqn:app-sgd-actual-row}\\
\mathfrak v_i^{\rm corr}&\defeq\Nin\Big(1-\frac2\pi\Big)+\frac2\pi\,\Nout\Big[\frac{(\Nin+2)\,\mu_i}{\Tr\Lambda}+\frac{(B+2\Nin+3)\,(T_D)_{ii}}{2\cR\,\Tr\Lambda}\Big].\label{eqn:app-sgd-corr}
\end{align}
There is an admissible constant $C_{\rm row}$ such that, for every $i$,
\begin{equation}\label{eqn:app-sgd-modes}
\abs{\volraw_i-\mathfrak v_i^{\rm corr}}\le C_{\rm row}\,\frac{\Nin}{\sqrt k},\qquad
\Big|\frac{\volraw_i}{\mathfrak v_i^{\rm corr}}-1\Big|\le\frac{C_{\rm row}}{(1-2/\pi)\sqrt k}.
\end{equation}
The actual total is exact, $\sum_i\volraw_i=\Nout\Nin$, while
\begin{equation}\label{eqn:app-sgd-excess}
\sum_i\mathfrak v_i^{\rm corr}-\Nout\Nin=\frac2\pi\,\Nout\Big[2+\frac{(B+2\Nin+3)\Tr T_D}{2\cR\,\Tr\Lambda}\Big]\in\Big(0,\ \frac2\pi\Nout\big[2+(3K+3)L/c\big]\Big].
\end{equation}
The corrected array exceeds the main text's array row by row:
\begin{equation}\label{eqn:app-sgd-difference}
\mathfrak v_i^{\rm corr}-\mathfrak v_i^{\text{s-SGD}}=\frac2\pi\,\Nout\Big[\frac{2\mu_i}{\Tr\Sigmaout}+\frac{(B+2\Nin+3)\,(\Lambda DD^\T\Lambda)_{ii}}{2\cR\,\Tr\Sigmaout}\Big]\ge0 .
\end{equation}
\end{theorem}
-/
theorem thm_app_sgd_modes_i (P : HaarParams) :
    ∃ Crow : ℝ, 0 ≤ Crow ∧
      ∀ (n m B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
        (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)),
        Muon.Foundations.IsOrthHaar ν → def_app_sgd_state_law P n m B μ D → ∀ i : Fin n,
          Integrable (fun p => sgdRowEnergy (haarSign μ D p.1 p.2) (haarCol p.1 i))
              (ν.prod (batchLaw n m B)) ∧
          0 < vCorr n m B μ D i ∧
          |haarRawRow B ν μ D i - vCorr n m B μ D i|
            ≤ Crow * (m : ℝ) / Real.sqrt (kOf n m B : ℝ) ∧
          |haarRawRow B ν μ D i / vCorr n m B μ D i - 1|
            ≤ Crow / ((1 - 2 / Real.pi) * Real.sqrt (kOf n m B : ℝ)) := by
  obtain ⟨g, b, hg, hb, hcol⟩ := lem_app_sgd_column_norm P
  refine ⟨2 / Real.pi * P.K * (g + b), by positivity [P.one_le_K], ?_⟩
  intro n m B μ D ν hν hP i
  letI := rvp_batchLaw_prob n m B
  have hP' := hP
  obtain ⟨⟨hn, hm, hB⟩, hk, hnK, -, -, hμ, -, -, -⟩ := hP'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hk1 : (1 : ℝ) ≤ (kOf n m B : ℝ) := by exact_mod_cast (by omega : 1 ≤ kOf n m B)
  have hs0 : 0 < Real.sqrt (kOf n m B : ℝ) := by positivity
  have ha : 0 < 2 / Real.pi := by positivity
  have hbase : 0 < 1 - 2 / Real.pi := by
    have := Real.pi_gt_three
    rw [sub_pos, div_lt_one₀ Real.pi_pos]
    linarith
  have hr := rvr_raw_identity P μ D ν hν hP i
  have hrawpos : 0 < haarRawRow B ν μ D i := by
    rw [hr]
    have he : 0 ≤ ∑ j : Fin m, ∫ β,
        hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j) ∂(batchLaw n m B) := by
      apply Finset.sum_nonneg
      intro j _
      apply integral_nonneg
      intro β
      exact div_nonneg (sq_nonneg _) (by
        unfold dotProduct; exact Finset.sum_nonneg fun l _ => mul_self_nonneg _)
    exact add_pos_of_pos_of_nonneg (mul_pos hm0 hbase) (by positivity)
  have hint : Integrable (fun p => sgdRowEnergy (haarSign μ D p.1 p.2) (haarCol p.1 i))
      (ν.prod (batchLaw n m B)) := Integrable.of_integral_ne_zero hrawpos.ne'
  have htrace : 0 < ∑ l, μ l := by
    have hlow : (n : ℝ) * P.c ≤ ∑ l, μ l := by
      simpa using (Finset.sum_le_sum (s := Finset.univ) fun l _ => (hμ l).1)
    exact lt_of_lt_of_le (mul_pos (by exact_mod_cast hn) P.c_pos) hlow
  have hR : 0 < twoR μ D := by
    have hp : 0 < haarPminus P := by
      unfold haarPminus; have := P.c_pos; have := P.fMin_pos; positivity
    exact hp.trans_le (haar_bounds P n m B μ D hP).1
  have hTD : 0 ≤ TD μ D i i := by
    have he : TD μ D i i = μ i * (∑ j, D i j * D i j) * μ i := by
      simp [TD, Matrix.mul_apply, Matrix.diagonal, Finset.mul_sum, Finset.sum_mul]
    rw [he]
    have hh : 0 ≤ ∑ j, D i j * D i j :=
      Finset.sum_nonneg fun j _ => mul_self_nonneg _
    have hmi : 0 ≤ μ i := P.c_pos.le.trans (hμ i).1
    positivity
  have hvc : (m : ℝ) * (1 - 2 / Real.pi) ≤ vCorr n m B μ D i := by
    unfold vCorr
    have hmi : 0 ≤ μ i := P.c_pos.le.trans (hμ i).1
    exact le_add_of_nonneg_right (by positivity)
  have hvpos : 0 < vCorr n m B μ D i := (mul_pos hm0 hbase).trans_le hvc
  let E := g / ((kOf n m B : ℝ) * Real.sqrt (kOf n m B : ℝ))
      + b / (kOf n m B : ℝ) ^ 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hc := fun j => rvr_column_error μ D j i E hE (hcol n m B μ D hP j i).2
  have hsum : (∑ j, ∫ β, hCol μ D β j i ^ 2 / haarX0 B μ D ∂(batchLaw n m B))
      = ((m : ℝ) + 2) * μ i / (∑ l, μ l)
        + ((B : ℝ) + 2 * (m : ℝ) + 3) * TD μ D i i / (twoR μ D * ∑ l, μ l) := by
    rw [← integral_finsetSum _ (fun j _ => (hc j).1)]
    simp_rw [← Finset.sum_div]
    rw [integral_div]
    have heq : (fun β => ∑ j, hCol (B := B) μ D β j i ^ 2) =
        fun β => (hMatrix μ D β * (hMatrix μ D β)ᵀ) i i := by
      ext β; simp [Matrix.mul_apply, hMatrix, pow_two]
    rw [heq, lem_app_sgd_column_iii P μ D hP, Matrix.diagonal_apply_eq]
    unfold haarX0
    field_simp
    <;> ring
  have herr : |haarRawRow B ν μ D i - vCorr n m B μ D i|
      ≤ (2 / Real.pi * P.K * (g + b)) * (m : ℝ) / Real.sqrt (kOf n m B : ℝ) := by
    have he : |(∑ j, ∫ β, hCol μ D β j i ^ 2 /
        (hCol μ D β j ⬝ᵥ hCol μ D β j) ∂(batchLaw n m B))
        - ∑ j, ∫ β, hCol μ D β j i ^ 2 / haarX0 B μ D ∂(batchLaw n m B)|
        ≤ (m : ℝ) * E := by
      rw [← Finset.sum_sub_distrib]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (by
        simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hc j).2))
    rw [hr]
    change |(_ + 2 / Real.pi * (n : ℝ) * _) -
      ((m : ℝ) * (1 - 2 / Real.pi) + 2 / Real.pi * (n : ℝ) * _)| ≤ _
    rw [← hsum]
    have halg : ∀ x y : ℝ, (m : ℝ) * (1 - 2 / Real.pi) + 2 / Real.pi * (n : ℝ) * x
        - ((m : ℝ) * (1 - 2 / Real.pi) + 2 / Real.pi * (n : ℝ) * y)
        = (2 / Real.pi * (n : ℝ)) * (x - y) := by intros; ring
    rw [halg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 / Real.pi * (n : ℝ))]
    exact (mul_le_mul_of_nonneg_left he (by positivity)).trans
      (rvr_error_scale _ _ _ _ _ _ _ ha.le hg hb hm0.le hk1 hnK (Nat.cast_nonneg _))
  refine ⟨hint, hvpos, herr, ?_⟩
  have heq : haarRawRow B ν μ D i / vCorr n m B μ D i - 1 =
      (haarRawRow B ν μ D i - vCorr n m B μ D i) / vCorr n m B μ D i := by
    field_simp
  rw [heq, abs_div, abs_of_pos hvpos]
  calc
    _ ≤ ((2 / Real.pi * P.K * (g + b)) * (m : ℝ) /
        Real.sqrt (kOf n m B : ℝ)) / vCorr n m B μ D i := by gcongr
    _ ≤ ((2 / Real.pi * P.K * (g + b)) * (m : ℝ) /
        Real.sqrt (kOf n m B : ℝ)) / ((m : ℝ) * (1 - 2 / Real.pi)) :=
      div_le_div_of_nonneg_left (by positivity [P.one_le_K]) (mul_pos hm0 hbase) hvc
    _ = _ := by field_simp <;> ring

/-- **thm:app-sgd-modes**, total part (`_ii`): `Muon.SignSGD.thm_app_sgd_modes_ii`.

cr-2026-10-23. LaTeX statement (verbatim, all four parts of the theorem):
\begin{theorem}[Corrected row volatility]\label{thm:app-sgd-modes}
In the Haar model of \cref{def:app-sgd-state-law}, define the raw annealed
row volatility of the update and the corrected array
\begin{align}
\volraw_i&\defeq\EE\norm{S^\T u_i}^2,\label{eqn:app-sgd-actual-row}\\
\mathfrak v_i^{\rm corr}&\defeq\Nin\Big(1-\frac2\pi\Big)+\frac2\pi\,\Nout\Big[\frac{(\Nin+2)\,\mu_i}{\Tr\Lambda}+\frac{(B+2\Nin+3)\,(T_D)_{ii}}{2\cR\,\Tr\Lambda}\Big].\label{eqn:app-sgd-corr}
\end{align}
There is an admissible constant $C_{\rm row}$ such that, for every $i$,
\begin{equation}\label{eqn:app-sgd-modes}
\abs{\volraw_i-\mathfrak v_i^{\rm corr}}\le C_{\rm row}\,\frac{\Nin}{\sqrt k},\qquad
\Big|\frac{\volraw_i}{\mathfrak v_i^{\rm corr}}-1\Big|\le\frac{C_{\rm row}}{(1-2/\pi)\sqrt k}.
\end{equation}
The actual total is exact, $\sum_i\volraw_i=\Nout\Nin$, while
\begin{equation}\label{eqn:app-sgd-excess}
\sum_i\mathfrak v_i^{\rm corr}-\Nout\Nin=\frac2\pi\,\Nout\Big[2+\frac{(B+2\Nin+3)\Tr T_D}{2\cR\,\Tr\Lambda}\Big]\in\Big(0,\ \frac2\pi\Nout\big[2+(3K+3)L/c\big]\Big].
\end{equation}
The corrected array exceeds the main text's array row by row:
\begin{equation}\label{eqn:app-sgd-difference}
\mathfrak v_i^{\rm corr}-\mathfrak v_i^{\text{s-SGD}}=\frac2\pi\,\Nout\Big[\frac{2\mu_i}{\Tr\Sigmaout}+\frac{(B+2\Nin+3)\,(\Lambda DD^\T\Lambda)_{ii}}{2\cR\,\Tr\Sigmaout}\Big]\ge0 .
\end{equation}
\end{theorem}
-/
theorem thm_app_sgd_modes_ii (P : HaarParams) :
    ∀ (n m B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
      (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)),
      Muon.Foundations.IsOrthHaar ν → def_app_sgd_state_law P n m B μ D →
        ∑ i, haarRawRow B ν μ D i = (n : ℝ) * (m : ℝ) := by
  intro n m B μ D ν hν hP
  letI := rvp_batchLaw_prob n m B
  have hr : ∀ i, haarRawRow B ν μ D i = (m : ℝ) * (1 - 2 / Real.pi)
      + 2 / Real.pi * (n : ℝ) * ∑ j, ∫ β,
        hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j) ∂(batchLaw n m B) := by
    intro i
    simpa [haarRawRow, sgdRowEnergy, dotProduct, pow_two] using
      lem_app_sgd_reduction_v P μ D ν hν hP i
  have hs : ∀ j : Fin m, (∑ i, ∫ β,
      hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j) ∂(batchLaw n m B)) = 1 := by
    intro j
    rw [← integral_finsetSum _ (fun i _ => rvr_ratio_int μ D j i)]
    have he : (fun β => ∑ i, hCol μ D β j i ^ 2 /
        (hCol μ D β j ⬝ᵥ hCol μ D β j)) =ᵐ[batchLaw n m B] fun _ => (1 : ℝ) := by
      filter_upwards [lem_app_sgd_column_iv P μ D hP j] with β hβ
      rw [← Finset.sum_div]
      have hn : hCol μ D β j ⬝ᵥ hCol μ D β j ≠ 0 := by
        exact fun hh => hβ (dotProduct_self_eq_zero.mp hh)
      simpa [dotProduct, pow_two] using div_self hn
    rw [integral_congr_ae he]
    simp
  simp_rw [hr]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma rvr_TD_diag_nonneg {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (i : Fin n) : 0 ≤ TD μ D i i := by
  have he : TD μ D i i = μ i * (∑ j, D i j ^ 2) * μ i := by
    simp [TD, Matrix.mul_apply, Matrix.diagonal, Finset.mul_sum, Finset.sum_mul, pow_two]
  rw [he]
  exact mul_nonneg (mul_nonneg (hμ i) (Finset.sum_nonneg fun j _ => sq_nonneg _)) (hμ i)

private lemma rvr_trace_TD_le (P : HaarParams) {n m : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hμ : ∀ i, P.c ≤ μ i ∧ μ i ≤ P.L) :
    (TD μ D).trace ≤ P.L * twoR μ D := by
  have hR : twoR μ D = ∑ i, μ i * ∑ j, D i j ^ 2 := by
    unfold twoR
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp [Matrix.mul_apply, pow_two]
  rw [rvq_trace_TD, hR, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hs : 0 ≤ ∑ j, D i j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hμ0 : 0 ≤ μ i := P.c_pos.le.trans (hμ i).1
  have := mul_le_mul_of_nonneg_right (hμ i).2 hμ0
  nlinarith

/-- **thm:app-sgd-modes**, excess part (`_iii`): `Muon.SignSGD.thm_app_sgd_modes_iii`.

cr-2026-10-23. LaTeX statement (verbatim, all four parts of the theorem):
\begin{theorem}[Corrected row volatility]\label{thm:app-sgd-modes}
In the Haar model of \cref{def:app-sgd-state-law}, define the raw annealed
row volatility of the update and the corrected array
\begin{align}
\volraw_i&\defeq\EE\norm{S^\T u_i}^2,\label{eqn:app-sgd-actual-row}\\
\mathfrak v_i^{\rm corr}&\defeq\Nin\Big(1-\frac2\pi\Big)+\frac2\pi\,\Nout\Big[\frac{(\Nin+2)\,\mu_i}{\Tr\Lambda}+\frac{(B+2\Nin+3)\,(T_D)_{ii}}{2\cR\,\Tr\Lambda}\Big].\label{eqn:app-sgd-corr}
\end{align}
There is an admissible constant $C_{\rm row}$ such that, for every $i$,
\begin{equation}\label{eqn:app-sgd-modes}
\abs{\volraw_i-\mathfrak v_i^{\rm corr}}\le C_{\rm row}\,\frac{\Nin}{\sqrt k},\qquad
\Big|\frac{\volraw_i}{\mathfrak v_i^{\rm corr}}-1\Big|\le\frac{C_{\rm row}}{(1-2/\pi)\sqrt k}.
\end{equation}
The actual total is exact, $\sum_i\volraw_i=\Nout\Nin$, while
\begin{equation}\label{eqn:app-sgd-excess}
\sum_i\mathfrak v_i^{\rm corr}-\Nout\Nin=\frac2\pi\,\Nout\Big[2+\frac{(B+2\Nin+3)\Tr T_D}{2\cR\,\Tr\Lambda}\Big]\in\Big(0,\ \frac2\pi\Nout\big[2+(3K+3)L/c\big]\Big].
\end{equation}
The corrected array exceeds the main text's array row by row:
\begin{equation}\label{eqn:app-sgd-difference}
\mathfrak v_i^{\rm corr}-\mathfrak v_i^{\text{s-SGD}}=\frac2\pi\,\Nout\Big[\frac{2\mu_i}{\Tr\Sigmaout}+\frac{(B+2\Nin+3)\,(\Lambda DD^\T\Lambda)_{ii}}{2\cR\,\Tr\Sigmaout}\Big]\ge0 .
\end{equation}
\end{theorem}
-/
theorem thm_app_sgd_modes_iii (P : HaarParams) :
    ∀ (n m B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ),
      def_app_sgd_state_law P n m B μ D →
        (∑ i, vCorr n m B μ D i - (n : ℝ) * (m : ℝ)
            = 2 / Real.pi * (n : ℝ) * (2 + ((B : ℝ) + 2 * (m : ℝ) + 3) * (TD μ D).trace
                / (twoR μ D * ∑ k, μ k))) ∧
        0 < 2 / Real.pi * (n : ℝ) * (2 + ((B : ℝ) + 2 * (m : ℝ) + 3) * (TD μ D).trace
                / (twoR μ D * ∑ k, μ k)) ∧
        2 / Real.pi * (n : ℝ) * (2 + ((B : ℝ) + 2 * (m : ℝ) + 3) * (TD μ D).trace
                / (twoR μ D * ∑ k, μ k))
          ≤ 2 / Real.pi * (n : ℝ) * (2 + (3 * P.K + 3) * P.L / P.c) := by
  intro n m B μ D hP
  have hP' := hP
  unfold def_app_sgd_state_law at hP'
  obtain ⟨⟨hn, hm, hB⟩, hk, hnK, hmK, hBK, hμ, -, -, -⟩ := hP'
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have htrace : 0 < ∑ i, μ i := by
    have hlow : (n : ℝ) * P.c ≤ ∑ i, μ i := by
      simpa using (Finset.sum_le_sum (s := Finset.univ) fun i _ => (hμ i).1)
    exact lt_of_lt_of_le (mul_pos hn0 P.c_pos) hlow
  have hR : 0 < twoR μ D := by
    have hp : 0 < haarPminus P := by
      unfold haarPminus
      exact mul_pos P.c_pos (sq_pos_of_pos P.fMin_pos)
    exact hp.trans_le (haar_bounds P n m B μ D hP).1
  have hT0 : 0 ≤ (TD μ D).trace := by
    rw [Matrix.trace]
    exact Finset.sum_nonneg fun i _ => rvr_TD_diag_nonneg μ D
      (fun l => P.c_pos.le.trans (hμ l).1) i
  have hcoef0 : 0 ≤ (B : ℝ) + 2 * (m : ℝ) + 3 := by positivity
  have hid : ∑ i, vCorr n m B μ D i - (n : ℝ) * (m : ℝ)
      = 2 / Real.pi * (n : ℝ) * (2 + ((B : ℝ) + 2 * (m : ℝ) + 3) * (TD μ D).trace
          / (twoR μ D * ∑ k, μ k)) := by
    have hmuSum : (∑ i, ((m : ℝ) + 2) * μ i / (∑ k, μ k)) = (m : ℝ) + 2 := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
      field_simp
    have hTsum : (∑ i, ((B : ℝ) + 2 * (m : ℝ) + 3) * TD μ D i i /
        (twoR μ D * ∑ k, μ k)) =
        ((B : ℝ) + 2 * (m : ℝ) + 3) * (TD μ D).trace /
          (twoR μ D * ∑ k, μ k) := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
      rfl
    simp_rw [vCorr]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib, hmuSum, hTsum]
    ring
  refine ⟨hid, ?_, ?_⟩
  · have hfrac : 0 ≤ ((B : ℝ) + 2 * (m : ℝ) + 3) * (TD μ D).trace /
        (twoR μ D * ∑ k, μ k) := by positivity
    positivity
  · have hkN : (kOf n m B : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (min_le_left n (min m B))
    have hcoef : (B : ℝ) + 2 * (m : ℝ) + 3 ≤ (3 * P.K + 3) * (n : ℝ) := by
      have hK0 : 0 ≤ P.K := le_trans (by norm_num) P.one_le_K
      have hBn : (B : ℝ) ≤ P.K * (n : ℝ) := hBK.trans (mul_le_mul_of_nonneg_left hkN hK0)
      have hmn : (m : ℝ) ≤ P.K * (n : ℝ) := hmK.trans (mul_le_mul_of_nonneg_left hkN hK0)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      calc
        (B : ℝ) + 2 * (m : ℝ) + 3 ≤ 3 * (P.K * (n : ℝ)) + 3 := by linarith
        _ ≤ (3 * P.K + 3) * (n : ℝ) := by nlinarith
    have hT := rvr_trace_TD_le P μ D hμ
    have hfrac : ((B : ℝ) + 2 * (m : ℝ) + 3) * (TD μ D).trace /
          (twoR μ D * ∑ k, μ k) ≤ (3 * P.K + 3) * P.L / P.c := by
      rw [div_le_iff₀ (mul_pos hR htrace)]
      have hsumlow : (n : ℝ) * P.c ≤ ∑ k, μ k := by
        simpa using (Finset.sum_le_sum (s := Finset.univ) fun i _ => (hμ i).1)
      have hL0 : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
      have hA0 : 0 ≤ 3 * P.K + 3 := by positivity [P.one_le_K]
      calc
        ((B : ℝ) + 2 * (m : ℝ) + 3) * (TD μ D).trace
            ≤ ((B : ℝ) + 2 * (m : ℝ) + 3) * (P.L * twoR μ D) :=
          mul_le_mul_of_nonneg_left hT hcoef0
        _ ≤ ((3 * P.K + 3) * (n : ℝ)) * (P.L * twoR μ D) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg hL0 hR.le)
        _ = ((3 * P.K + 3) * P.L / P.c) * (twoR μ D * ((n : ℝ) * P.c)) := by
          field_simp [P.c_pos.ne']
        _ ≤ ((3 * P.K + 3) * P.L / P.c) * (twoR μ D * ∑ k, μ k) := by
          apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumlow hR.le)
          exact div_nonneg (mul_nonneg hA0 hL0) P.c_pos.le
    gcongr

/-- **thm:app-sgd-modes**, difference part (`_iv`): `Muon.SignSGD.thm_app_sgd_modes_iv`.

cr-2026-10-23. LaTeX statement (verbatim, all four parts of the theorem):
\begin{theorem}[Corrected row volatility]\label{thm:app-sgd-modes}
In the Haar model of \cref{def:app-sgd-state-law}, define the raw annealed
row volatility of the update and the corrected array
\begin{align}
\volraw_i&\defeq\EE\norm{S^\T u_i}^2,\label{eqn:app-sgd-actual-row}\\
\mathfrak v_i^{\rm corr}&\defeq\Nin\Big(1-\frac2\pi\Big)+\frac2\pi\,\Nout\Big[\frac{(\Nin+2)\,\mu_i}{\Tr\Lambda}+\frac{(B+2\Nin+3)\,(T_D)_{ii}}{2\cR\,\Tr\Lambda}\Big].\label{eqn:app-sgd-corr}
\end{align}
There is an admissible constant $C_{\rm row}$ such that, for every $i$,
\begin{equation}\label{eqn:app-sgd-modes}
\abs{\volraw_i-\mathfrak v_i^{\rm corr}}\le C_{\rm row}\,\frac{\Nin}{\sqrt k},\qquad
\Big|\frac{\volraw_i}{\mathfrak v_i^{\rm corr}}-1\Big|\le\frac{C_{\rm row}}{(1-2/\pi)\sqrt k}.
\end{equation}
The actual total is exact, $\sum_i\volraw_i=\Nout\Nin$, while
\begin{equation}\label{eqn:app-sgd-excess}
\sum_i\mathfrak v_i^{\rm corr}-\Nout\Nin=\frac2\pi\,\Nout\Big[2+\frac{(B+2\Nin+3)\Tr T_D}{2\cR\,\Tr\Lambda}\Big]\in\Big(0,\ \frac2\pi\Nout\big[2+(3K+3)L/c\big]\Big].
\end{equation}
The corrected array exceeds the main text's array row by row:
\begin{equation}\label{eqn:app-sgd-difference}
\mathfrak v_i^{\rm corr}-\mathfrak v_i^{\text{s-SGD}}=\frac2\pi\,\Nout\Big[\frac{2\mu_i}{\Tr\Sigmaout}+\frac{(B+2\Nin+3)\,(\Lambda DD^\T\Lambda)_{ii}}{2\cR\,\Tr\Sigmaout}\Big]\ge0 .
\end{equation}
\end{theorem}
-/
theorem thm_app_sgd_modes_iv (P : HaarParams) :
    ∀ (n m B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ),
      def_app_sgd_state_law P n m B μ D → ∀ i : Fin n,
        vCorr n m B μ D i - vSgd n m μ i
            = 2 / Real.pi * (n : ℝ) * (2 * μ i / (∑ k, μ k)
                + ((B : ℝ) + 2 * (m : ℝ) + 3) * TD μ D i i / (twoR μ D * ∑ k, μ k)) ∧
        0 ≤ 2 / Real.pi * (n : ℝ) * (2 * μ i / (∑ k, μ k)
                + ((B : ℝ) + 2 * (m : ℝ) + 3) * TD μ D i i / (twoR μ D * ∑ k, μ k)) := by
  intro n m B μ D hP i
  have hP' := hP
  unfold def_app_sgd_state_law at hP'
  obtain ⟨⟨hn, -, -⟩, -, -, -, -, hμ, -, -, -⟩ := hP'
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have htrace : 0 < ∑ k, μ k := by
    have hlow : (n : ℝ) * P.c ≤ ∑ k, μ k := by
      simpa using (Finset.sum_le_sum (s := Finset.univ) fun k _ => (hμ k).1)
    exact lt_of_lt_of_le (mul_pos hn0 P.c_pos) hlow
  have hR : 0 < twoR μ D := by
    have hp : 0 < haarPminus P := by
      unfold haarPminus
      exact mul_pos P.c_pos (sq_pos_of_pos P.fMin_pos)
    exact hp.trans_le (haar_bounds P n m B μ D hP).1
  constructor
  · unfold vCorr vSgd muBar
    field_simp
    ring
  · have hTD : 0 ≤ TD μ D i i :=
      rvr_TD_diag_nonneg μ D (fun l => P.c_pos.le.trans (hμ l).1) i
    have hμi : 0 ≤ μ i := P.c_pos.le.trans (hμ i).1
    have hfirst : 0 ≤ 2 * μ i / (∑ k, μ k) := div_nonneg (by positivity) htrace.le
    have hsecond : 0 ≤ ((B : ℝ) + 2 * (m : ℝ) + 3) * TD μ D i i /
        (twoR μ D * ∑ k, μ k) := by positivity
    exact mul_nonneg (by positivity) (add_nonneg hfirst hsecond)

private lemma rvr_sign_measurable : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const)

private lemma rvr_haar_row_vec {n m : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) :
    (haarDelta U D)ᵀ *ᵥ haarCol U i = fun j => D i j := by
  have hUt : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
  have hDA : (haarDelta U D)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ) = Dᵀ := by
    unfold haarDelta
    rw [Matrix.transpose_mul, Matrix.mul_assoc, hUt, Matrix.mul_one]
  funext j
  have h := congrFun (congrFun hDA j) i
  rw [Matrix.mul_apply] at h
  simpa [Matrix.mulVec, dotProduct, haarCol, Matrix.transpose_apply] using h

private lemma rvr_risk_eq_weighted_rows {n m : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (mu : Fin n → ℝ) (A : Matrix (Fin n) (Fin m) ℝ) :
    riskTwo (haarSigmaOut U mu) A = ∑ i, mu i * sgdRowEnergy A (haarCol U i) := by
  unfold riskTwo pairIdIn haarSigmaOut sgdRowEnergy
  rw [show (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal mu *
      (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * A * Aᵀ =
      (U : Matrix (Fin n) (Fin n) ℝ) *
        (Matrix.diagonal mu * (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * A * Aᵀ) by
        simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm (U : Matrix (Fin n) (Fin n) ℝ)]
  simp only [Matrix.mul_assoc, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, haarCol]
  simp [Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  let f : Fin n → Fin n → Fin m → ℝ := fun y x k =>
    (U : Matrix (Fin n) (Fin n) ℝ) y i * (A y k * A x k) *
      (U : Matrix (Fin n) (Fin n) ℝ) x i
  change (∑ x, ∑ y, ∑ k, f y x k) = _
  calc
    _ = ∑ x, ∑ k, ∑ y, f y x k := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ x, ∑ y, f y x k := by rw [Finset.sum_comm]
    _ = ∑ k, ∑ y, ∑ x, f y x k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      dsimp [f]
      ring

private lemma rvr_LB_mul_mu {n m : ℕ} (B : ℕ) (mu : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hR : 0 < twoR mu D) (hbar : 0 < muBar mu)
    (i : Fin n) :
    LB B mu D * mu i = haarDcoef B mu i / Real.sqrt (twoR mu D / 2) := by
  have hR0 : 0 ≤ twoR mu D := hR.le
  have hbar0 : 0 ≤ muBar mu := hbar.le
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsR : 0 < Real.sqrt (twoR mu D / 2) := Real.sqrt_pos.2 (by positivity)
  have hsbar : 0 < Real.sqrt (Real.pi * muBar mu) := Real.sqrt_pos.2 (by positivity)
  have hsprod : Real.sqrt (twoR mu D * muBar mu)
      = Real.sqrt (twoR mu D) * Real.sqrt (muBar mu) := Real.sqrt_mul hR0 _
  have hsRtwo : Real.sqrt (twoR mu D)
      = Real.sqrt 2 * Real.sqrt (twoR mu D / 2) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
    congr 1
    field_simp
  have hspi : Real.sqrt (Real.pi * muBar mu)
      = Real.sqrt Real.pi * Real.sqrt (muBar mu) := Real.sqrt_mul hpi.le _
  have hs2pi : Real.sqrt (2 / Real.pi) = Real.sqrt 2 / Real.sqrt Real.pi := by
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2)]
  unfold LB haarDcoef
  rw [hsprod, hsRtwo, hspi, hs2pi]
  field_simp [Real.sqrt_ne_zero'.2 (by positivity : (0 : ℝ) < 2),
    Real.sqrt_ne_zero'.2 hpi, hsR.ne', hsbar.ne',
    Real.sqrt_ne_zero'.2 hbar]

private lemma rvr_frob_diag_sq {n m : ℕ} (mu : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) :
    frobNorm (Matrix.diagonal mu * D) ^ 2 = ∑ i, mu i ^ 2 * ∑ j, D i j ^ 2 := by
  rw [show frobNorm (Matrix.diagonal mu * D) ^ 2 =
      ∑ i, ∑ j, (Matrix.diagonal mu * D) i j ^ 2 from
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Finset.mul_sum]
  ring

/-! ## Half-anisotropic recursion (`prop:signsgd-recursion-anisotropic`) -/

/-- **prop:signsgd-recursion-anisotropic** `Muon.SignSGD.prop_signsgd_recursion_anisotropic`.

cr-2026-10-23. LaTeX statement (verbatim):
\begin{proposition}[Half-anisotropic \SignSGD recursion]\label{prop:signsgd-recursion-anisotropic}
In the Haar model of \cref{def:app-sgd-state-law} with $k\ge k_*$, let
$\lr\ge0$ be deterministic and $\Delta^+=\Delta-\lr S$. Then, with
$\mathfrak d_i\defeq\mu_i\mathcal N_B/\sqrt{\pi\bar\mu}$, there are real numbers
$E_1,\dots,E_{\Nout}$ such that
\begin{equation}\label{eqn:signsgd-risk-recursion-anisotropic}
\EE\,\CMscr Q_i(\Delta^+)=\CMscr Q_i(\Delta)-\frac{2\lr\,\mathfrak d_i}{\sqrt\cR}\,\CMscr Q_i(\Delta)+\lr^2\,\mathfrak v_i^{\rm corr}+E_i,\qquad
\sum_i\abs{E_i}\le2\lr f_+\sqrt{C_*}+\lr^2C_{\rm row}\,\frac{\Nout\Nin}{\sqrt k}.
\end{equation}
The risk satisfies
\begin{equation}\label{eqn:app-sgd-aniso-risk}
\EE\,\cR(\Delta^+)=\cR-\lr\sum_i\frac{\mu_i\,\mathfrak d_i}{\sqrt\cR}\,\CMscr Q_i(\Delta)+\frac{\lr^2}2\sum_i\mu_i\,\mathfrak v_i^{\text{s-SGD}}+\mathcal E_\lr,
\end{equation}
with $\mathcal E_\lr$ bounded as in \cref{cor:app-sgd-half-risk}.
\end{proposition}
-/
theorem prop_signsgd_recursion_anisotropic (P : HaarParams) :
    ∃ Cstar Crow Cvol : ℝ, 0 ≤ Cstar ∧ 0 ≤ Crow ∧ 0 ≤ Cvol ∧
      ∀ (n m B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
        (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)),
        Muon.Foundations.IsOrthHaar ν → def_app_sgd_state_law P n m B μ D →
        haarKStar P ≤ kOf n m B → ∀ η : ℝ, 0 ≤ η →
          -- row recursion: the residuals `E_i` are the differences of the displayed identity
          (∀ i : Fin n,
            Integrable (fun p => sgdRowEnergy
                (def_app_sgd_update η (haarDelta p.1 D) (haarBatch μ p.1 p.2)) (haarCol p.1 i))
              (ν.prod (batchLaw n m B))) ∧
          (∑ i, |(∫ p, sgdRowEnergy
                (def_app_sgd_update η (haarDelta p.1 D) (haarBatch μ p.1 p.2)) (haarCol p.1 i)
                ∂(ν.prod (batchLaw n m B)))
              - ((∑ j, D i j ^ 2)
                  - 2 * η * (haarDcoef B μ i / Real.sqrt (twoR μ D / 2)) * (∑ j, D i j ^ 2)
                  + η ^ 2 * vCorr n m B μ D i)|
            ≤ 2 * η * P.fMax * Real.sqrt Cstar
              + η ^ 2 * Crow * ((n : ℝ) * (m : ℝ)) / Real.sqrt (kOf n m B : ℝ)) ∧
          -- risk: `E_η` is the difference of the displayed risk identity
          Integrable (fun p => riskTwo (haarSigmaOut p.1 μ)
              (def_app_sgd_update η (haarDelta p.1 D) (haarBatch μ p.1 p.2)) / 2)
            (ν.prod (batchLaw n m B)) ∧
          |(∫ p, riskTwo (haarSigmaOut p.1 μ)
                (def_app_sgd_update η (haarDelta p.1 D) (haarBatch μ p.1 p.2)) / 2
              ∂(ν.prod (batchLaw n m B)))
            - (twoR μ D / 2
                - η * (∑ i, μ i * (haarDcoef B μ i / Real.sqrt (twoR μ D / 2)) * (∑ j, D i j ^ 2))
                + η ^ 2 / 2 * (∑ i, μ i * vSgd n m μ i))|
            ≤ η * (P.L * P.fMax) * Real.sqrt Cstar
              + η ^ 2 / 2 * Cvol * ((n : ℝ) * (m : ℝ)) / Real.sqrt (kOf n m B : ℝ) := by
  obtain ⟨Cdrift, hCdrift, hdrift⟩ := cor_app_sgd_half_pairings P
  obtain ⟨Crisk, Cvol, hCrisk, hCvol, hrisk⟩ := cor_app_sgd_half_risk P
  obtain ⟨Crow, hCrow, hrow⟩ := thm_app_sgd_modes_i P
  refine ⟨max Cdrift Crisk, Crow, Cvol, hCdrift.trans (le_max_left _ _), hCrow, hCvol, ?_⟩
  intro n m B mu D nu hnu hstate hk eta heta
  letI : IsProbabilityMeasure nu := hnu.1
  letI := rvp_batchLaw_prob n m B
  have hstate' := hstate
  obtain ⟨⟨hn, hm, -⟩, hk2, -, -, -, -, -, -, -⟩ := hstate'
  have hR : 0 < twoR mu D := by
    have hp : 0 < haarPminus P := mul_pos P.c_pos (sq_pos_of_pos P.fMin_pos)
    exact hp.trans_le (haar_bounds P n m B mu D hstate).1
  have hbar : 0 < muBar mu :=
    P.c_pos.trans_le (haar_bounds P n m B mu D hstate).2.2.2.1
  have hsqrtk : 0 < Real.sqrt (kOf n m B : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hk2))
  have hmode := hrow n m B mu D nu hnu hstate
  have hpair := hdrift n m B mu D nu hnu hstate hk
  have hriske := hrisk n m B mu D nu hnu hstate hk eta heta
  have hsignMeas (a : Fin n) (j : Fin m) :
      Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
        (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
          haarSign (B := B) mu D p.1 p.2 a j) := by
    unfold haarSign
    simp only [Matrix.map_apply]
    apply rvr_sign_measurable.comp
    have hgrad : Continuous (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
        (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
          physGrad (haarDelta p.1 D) (haarBatch mu p.1 p.2) a j) := by
      unfold physGrad residual haarBatch linBatch haarDelta Matrix.mulVec dotProduct
      fun_prop
    exact hgrad.measurable
  have hprojMeas (i : Fin n) (j : Fin m) : Measurable (fun p :
      Matrix.orthogonalGroup (Fin n) ℝ × (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
      ((haarSign (B := B) mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i) j) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, haarCol]
    exact Finset.measurable_sum _ fun a _ => (hsignMeas a j).mul
      ((continuous_subtype_val.matrix_elem a i).comp continuous_fst).measurable
  have hprojInt (i : Fin n) (j : Fin m) : Integrable (fun p =>
      ((haarSign (B := B) mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i) j)
      (nu.prod (batchLaw n m B)) := by
    let y := fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
        (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
      ((haarSign (B := B) mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i) j
    let q := fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
        (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
      sgdRowEnergy (haarSign (B := B) mu D p.1 p.2) (haarCol p.1 i)
    refine Integrable.mono' ((hmode i).1.add (integrable_const (1 : ℝ)))
      (hprojMeas i j).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    have hsq : y p ^ 2 ≤ q p := by
      exact Finset.single_le_sum (f := fun k =>
        ((haarSign (B := B) mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i) k ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have habs : |y p| ≤ y p ^ 2 + 1 := by
      nlinarith [sq_nonneg (|y p| - 1), sq_abs (y p)]
    have hq0 : 0 ≤ q p := Finset.sum_nonneg fun k _ => sq_nonneg _
    simp only [Pi.add_apply, Real.norm_eq_abs]
    change |y p| ≤ q p + 1
    nlinarith
  have hcrossInt (i : Fin n) : Integrable (fun p =>
      ((haarDelta p.1 D)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
        ((haarSign (B := B) mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i))
      (nu.prod (batchLaw n m B)) := by
    have hi : Integrable (fun p => ∑ j, D i j *
        ((haarSign (B := B) mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i) j)
        (nu.prod (batchLaw n m B)) :=
      integrable_finset_sum _ fun j _ => (hprojInt i j).const_mul _
    refine hi.congr (Filter.Eventually.of_forall fun p => ?_)
    change (∑ j, D i j *
      ((haarSign (B := B) mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i) j) =
      ((haarDelta p.1 D)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
        ((haarSign (B := B) mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i)
    rw [rvr_haar_row_vec]
    rfl
  have hstep (i : Fin n) (p : Matrix.orthogonalGroup (Fin n) ℝ ×
      (Fin B → (Fin n → ℝ) × (Fin m → ℝ))) :
      sgdRowEnergy (def_app_sgd_update eta (haarDelta p.1 D) (haarBatch mu p.1 p.2))
          (haarCol p.1 i)
        = (∑ j, D i j ^ 2)
          - 2 * eta * (((haarDelta p.1 D)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
            ((haarSign mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i))
          + eta ^ 2 * sgdRowEnergy (haarSign mu D p.1 p.2) (haarCol p.1 i) := by
    simpa [sgdRowEnergy, haarSign, def_app_sgd_update, rvr_haar_row_vec] using
      rowEnergy_step (haarDelta p.1 D) (haarSign mu D p.1 p.2) (haarCol p.1 i) eta
  have hupdateInt (i : Fin n) : Integrable (fun p => sgdRowEnergy
      (def_app_sgd_update eta (haarDelta p.1 D) (haarBatch mu p.1 p.2)) (haarCol p.1 i))
      (nu.prod (batchLaw n m B)) := by
    have hi := ((integrable_const (∑ j, D i j ^ 2)).sub
      ((hcrossInt i).const_mul (2 * eta))).add ((hmode i).1.const_mul (eta ^ 2))
    exact hi.congr (Filter.Eventually.of_forall fun p => (hstep i p).symm)
  have hrowEq (i : Fin n) :
      (∫ p, sgdRowEnergy
          (def_app_sgd_update eta (haarDelta p.1 D) (haarBatch mu p.1 p.2)) (haarCol p.1 i)
          ∂(nu.prod (batchLaw n m B)))
        = (∑ j, D i j ^ 2) - 2 * eta * (∫ p,
            ((haarDelta p.1 D)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
              ((haarSign mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i)
            ∂(nu.prod (batchLaw n m B))) + eta ^ 2 * haarRawRow B nu mu D i := by
    calc
      _ = ∫ p, ((∑ j, D i j ^ 2) - 2 * eta *
          (((haarDelta p.1 D)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
            ((haarSign mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i))) +
          eta ^ 2 * sgdRowEnergy (haarSign mu D p.1 p.2) (haarCol p.1 i)
        ∂(nu.prod (batchLaw n m B)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun p => hstep i p)
      _ = (∫ p, (∑ j, D i j ^ 2) - 2 * eta *
            (((haarDelta p.1 D)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
              ((haarSign mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i))
          ∂(nu.prod (batchLaw n m B))) +
          ∫ p, eta ^ 2 * sgdRowEnergy (haarSign mu D p.1 p.2) (haarCol p.1 i)
            ∂(nu.prod (batchLaw n m B)) :=
          integral_add ((integrable_const _).sub ((hcrossInt i).const_mul _))
            ((hmode i).1.const_mul _)
      _ = ((∫ _p, ∑ j, D i j ^ 2 ∂(nu.prod (batchLaw n m B))) -
          ∫ p, 2 * eta * (((haarDelta p.1 D)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
            ((haarSign mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i))
            ∂(nu.prod (batchLaw n m B))) +
          ∫ p, eta ^ 2 * sgdRowEnergy (haarSign mu D p.1 p.2) (haarCol p.1 i)
            ∂(nu.prod (batchLaw n m B)) := by
          rw [integral_sub (integrable_const _) ((hcrossInt i).const_mul _)]
      _ = _ := by
          rw [integral_const_mul, integral_const_mul]
          simp [haarRawRow]
  have hRiskInt : Integrable (fun p => riskTwo (haarSigmaOut p.1 mu)
      (def_app_sgd_update eta (haarDelta p.1 D) (haarBatch mu p.1 p.2)) / 2)
      (nu.prod (batchLaw n m B)) := by
    have hi : Integrable (fun p => (∑ i, mu i * sgdRowEnergy
        (def_app_sgd_update eta (haarDelta p.1 D) (haarBatch mu p.1 p.2))
          (haarCol p.1 i)) / 2) (nu.prod (batchLaw n m B)) :=
      (integrable_finset_sum _ fun i _ => (hupdateInt i).const_mul _).div_const 2
    refine hi.congr (Filter.Eventually.of_forall fun p => ?_)
    exact congrArg (fun x : ℝ => x / 2)
      (rvr_risk_eq_weighted_rows p.1 mu
        (def_app_sgd_update eta (haarDelta p.1 D) (haarBatch mu p.1 p.2))).symm
  refine ⟨hupdateInt, ?_, hRiskInt, ?_⟩
  · have hcoef (i : Fin n) :
        LB B mu D * mu i = haarDcoef B mu i / Real.sqrt (twoR mu D / 2) :=
      rvr_LB_mul_mu B mu D hR hbar i
    have hdiff (i : Fin n) :
        (∫ p, sgdRowEnergy
            (def_app_sgd_update eta (haarDelta p.1 D) (haarBatch mu p.1 p.2))
              (haarCol p.1 i) ∂(nu.prod (batchLaw n m B)))
          - ((∑ j, D i j ^ 2)
              - 2 * eta * (haarDcoef B mu i / Real.sqrt (twoR mu D / 2)) *
                (∑ j, D i j ^ 2) + eta ^ 2 * vCorr n m B mu D i)
        = -2 * eta * ((∫ p,
              ((haarDelta p.1 D)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
                ((haarSign mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i)
              ∂(nu.prod (batchLaw n m B)))
            - LB B mu D * mu i * (∑ j, D i j ^ 2))
          + eta ^ 2 * (haarRawRow B nu mu D i - vCorr n m B mu D i) := by
      rw [hrowEq i, ← hcoef i]
      ring
    have hDrift : (∑ i, |(∫ p,
          ((haarDelta p.1 D)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
            ((haarSign mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i)
          ∂(nu.prod (batchLaw n m B)))
        - LB B mu D * mu i * (∑ j, D i j ^ 2)|)
        ≤ P.fMax * Real.sqrt (max Cdrift Crisk) := by
      calc
        _ ≤ P.fMax * Real.sqrt Cdrift := hpair.2.1
        _ ≤ P.fMax * Real.sqrt (max Cdrift Crisk) := by
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_max_left _ _))
            (P.fMin_pos.trans_le P.fMin_le_fMax).le
    have hVol : (∑ i, |haarRawRow B nu mu D i - vCorr n m B mu D i|)
        ≤ Crow * ((n : ℝ) * (m : ℝ)) / Real.sqrt (kOf n m B : ℝ) := by
      calc
        _ ≤ ∑ _i : Fin n, Crow * (m : ℝ) / Real.sqrt (kOf n m B : ℝ) :=
          Finset.sum_le_sum fun i _ => (hmode i).2.2.1
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    have htri (i : Fin n) :
        |-2 * eta * ((∫ p,
              ((haarDelta p.1 D)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
                ((haarSign mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i)
              ∂(nu.prod (batchLaw n m B)))
            - LB B mu D * mu i * (∑ j, D i j ^ 2))
          + eta ^ 2 * (haarRawRow B nu mu D i - vCorr n m B mu D i)|
        ≤ 2 * eta * |(∫ p,
              ((haarDelta p.1 D)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
                ((haarSign mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i)
              ∂(nu.prod (batchLaw n m B)))
            - LB B mu D * mu i * (∑ j, D i j ^ 2)|
          + eta ^ 2 * |haarRawRow B nu mu D i - vCorr n m B mu D i| := by
      calc
        _ ≤ |-2 * eta * ((∫ p,
              ((haarDelta p.1 D)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
                ((haarSign mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i)
              ∂(nu.prod (batchLaw n m B)))
            - LB B mu D * mu i * (∑ j, D i j ^ 2))| +
            |eta ^ 2 * (haarRawRow B nu mu D i - vCorr n m B mu D i)| := abs_add_le _ _
        _ = _ := by
          simp only [abs_mul, abs_neg, abs_of_nonneg heta,
            abs_of_nonneg (sq_nonneg eta)]
          norm_num
    calc
      _ = ∑ i, |-2 * eta * ((∫ p,
              ((haarDelta p.1 D)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
                ((haarSign mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i)
              ∂(nu.prod (batchLaw n m B)))
            - LB B mu D * mu i * (∑ j, D i j ^ 2))
          + eta ^ 2 * (haarRawRow B nu mu D i - vCorr n m B mu D i)| := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hdiff i]
      _ ≤ ∑ i, (2 * eta * |(∫ p,
              ((haarDelta p.1 D)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
                ((haarSign mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i)
              ∂(nu.prod (batchLaw n m B)))
            - LB B mu D * mu i * (∑ j, D i j ^ 2)|
          + eta ^ 2 * |haarRawRow B nu mu D i - vCorr n m B mu D i|) :=
            Finset.sum_le_sum fun i _ => htri i
      _ = 2 * eta * (∑ i, |(∫ p,
              ((haarDelta p.1 D)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
                ((haarSign mu D p.1 p.2)ᵀ *ᵥ haarCol p.1 i)
              ∂(nu.prod (batchLaw n m B)))
            - LB B mu D * mu i * (∑ j, D i j ^ 2)|)
          + eta ^ 2 * (∑ i, |haarRawRow B nu mu D i - vCorr n m B mu D i|) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * eta * (P.fMax * Real.sqrt (max Cdrift Crisk))
          + eta ^ 2 * (Crow * ((n : ℝ) * (m : ℝ)) /
            Real.sqrt (kOf n m B : ℝ)) := by
            gcongr
      _ = _ := by ring
  · have hlead : LB B mu D * frobNorm (Matrix.diagonal mu * D) ^ 2
        = ∑ i, mu i * (haarDcoef B mu i / Real.sqrt (twoR mu D / 2)) *
          (∑ j, D i j ^ 2) := by
      rw [rvr_frob_diag_sq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← rvr_LB_mul_mu B mu D hR hbar i]
      ring
    rw [show eta * LB B mu D * frobNorm (Matrix.diagonal mu * D) ^ 2 =
      eta * (LB B mu D * frobNorm (Matrix.diagonal mu * D) ^ 2) by ring,
      hlead, qPrint_eq_sum] at hriske
    calc
      _ ≤ eta * (P.L * P.fMax) * Real.sqrt Crisk
          + eta ^ 2 / 2 * (Cvol * ((n : ℝ) * (m : ℝ)) /
            Real.sqrt (kOf n m B : ℝ)) := hriske
      _ ≤ eta * (P.L * P.fMax) * Real.sqrt (max Cdrift Crisk)
          + eta ^ 2 / 2 * (Cvol * ((n : ℝ) * (m : ℝ)) /
            Real.sqrt (kOf n m B : ℝ)) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_max_right _ _))
                (mul_nonneg heta (mul_nonneg
                  (P.c_pos.le.trans P.c_le_L) (P.fMin_pos.trans_le P.fMin_le_fMax).le)))
              le_rfl
      _ = _ := by ring

end Muon.SignSGD

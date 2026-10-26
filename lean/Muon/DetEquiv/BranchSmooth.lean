import Muon.DetEquiv.Branch

/-!
# Appendix B: smoothness of the branch in `s` (task L-B.4)

Snapshot `cr-2026-10-23`. Source: `sections/02-deterministic-equivalents/section.tex`,
"The weighted fixed-point system" (l.164–201, `thm:app-de-branch`), part (iv) only
(smoothness in `s`, l.195–199). Parts (i)–(iii) belong to `Muon/DetEquiv/Branch.lean`
(L-B.2) and `Muon/DetEquiv/BranchStability.lean` (L-B.3).

Representation choices (CARD §2, §3 row `thm:app-de-branch`, ruling L2):

* The solution map is `branchSol (Fw w) ν ν' s` from `Muon.DetEquiv.Branch`, the total map
  that equals the solution of `eqn:app-de-system` for `s > 0` (`branchSol_spec`, part (i)).
* Part (iv) is stated for the paper's weight sequence `w` (`WeightSeq w`, the hypothesis of
  the theorem), with `F = Fw w`, not for an abstract `AdmissibleWeightFn F`: the smoothness in
  `s` needs the smoothness of `F_w` on `(0, ∞)` from `lem:app-de-scalar`(ii).
* "`C^∞` on `(0,∞)`" is `ContDiffOn ℝ (⊤ : ℕ∞)` on the open set `Ioi 0`.
* `q(-s) = s σ σ̃` is the `let`-bound `q`, a function of `s` with `s > 0`; `q'(s)` is
  `deriv q s`, which is the genuine derivative because `q` is differentiable on the open set
  `Ioi 0`.
* The hypotheses `∫ x dν > 0`, `∫ x dν̃ > 0` are the paper's, on `ν`, `ν̃` as `Measure ℝ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Matrix MatrixOrder ContDiff

noncomputable section

namespace Muon.DetEquiv

/-! ### Private helpers for `thm_app_de_branch_iv` -/

private lemma bs_pt {Cs α t : ℝ} (k : ℕ) (hα : 0 ≤ α) (ht : t ∈ Icc 0 Cs) :
    0 ≤ (t / (α * t + 1)) ^ (k + 1) ∧ (t / (α * t + 1)) ^ (k + 1) ≤ Cs ^ (k + 1) := by
  obtain ⟨h0, h1⟩ := ht
  have hd : 0 < α * t + 1 := by nlinarith [mul_nonneg hα h0]
  have hu0 : 0 ≤ t / (α * t + 1) := div_nonneg h0 hd.le
  have hu1 : t / (α * t + 1) ≤ Cs := by
    rw [div_le_iff₀ hd]; nlinarith [mul_nonneg hα h0, mul_nonneg h0 (sub_nonneg.2 h1)]
  exact ⟨pow_nonneg hu0 _, pow_le_pow_left₀ hu0 hu1 _⟩

private lemma bs_meas (k : ℕ) (α : ℝ) :
    Measurable fun t : ℝ => (t / (α * t + 1)) ^ (k + 1) := by fun_prop

private lemma bs_ae {μ : Measure ℝ} {Cs : ℝ} (hsupp : μ (Icc 0 Cs)ᶜ = 0) :
    ∀ᵐ t ∂μ, t ∈ Icc (0:ℝ) Cs := by
  rw [MeasureTheory.ae_iff]; exact hsupp

private lemma bs_integrable {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs α : ℝ} (k : ℕ) (hα : 0 ≤ α)
    (hsupp : μ (Icc 0 Cs)ᶜ = 0) :
    Integrable (fun t : ℝ => (t / (α * t + 1)) ^ (k + 1)) μ := by
  refine Integrable.mono' (integrable_const (Cs ^ (k + 1))) (bs_meas k α).aestronglyMeasurable ?_
  filter_upwards [bs_ae hsupp] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (bs_pt k hα ht).1]
  exact (bs_pt k hα ht).2

private lemma bs_cont {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs : ℝ} (k : ℕ)
    (hsupp : μ (Icc 0 Cs)ᶜ = 0) :
    ContinuousOn (fun α : ℝ => ∫ t, (t / (α * t + 1)) ^ (k + 1) ∂μ) (Ioi 0) := by
  refine continuousOn_of_dominated (bound := fun _ => Cs ^ (k + 1)) ?_ ?_ (integrable_const _) ?_
  · intro α _
    exact (bs_meas k α).aestronglyMeasurable
  · intro α hα
    filter_upwards [bs_ae hsupp] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (bs_pt k (le_of_lt hα) ht).1]
    exact (bs_pt k (le_of_lt hα) ht).2
  · filter_upwards [bs_ae hsupp] with t ht
    have h0 := ht.1
    refine ContinuousOn.pow (ContinuousOn.div (by fun_prop) (by fun_prop) ?_) _
    intro α hα
    have : 0 < α * t + 1 := by nlinarith [mul_nonneg (le_of_lt (show (0:ℝ) < α from hα)) h0]
    exact this.ne'

private lemma bs_pt_deriv (k : ℕ) {α : ℝ} (hα : 0 < α) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun α : ℝ => (t / (α * t + 1)) ^ (k + 1))
      (-((k + 1 : ℝ) * (t / (α * t + 1)) ^ (k + 1 + 1))) α := by
  have hd : 0 < α * t + 1 := by nlinarith [mul_nonneg hα.le ht]
  have h1 : HasDerivAt (fun α : ℝ => α * t + 1) t α := by
    simpa using ((hasDerivAt_id α).mul_const t).add_const 1
  have h3 := (hasDerivAt_const α t).div h1 hd.ne'
  have h4 := h3.pow (k + 1)
  refine h4.congr_deriv ?_
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.div_apply]
  have e : (0 * (α * t + 1) - t * t) / (α * t + 1) ^ 2 = -((t / (α * t + 1)) ^ 2) := by
    field_simp; ring
  rw [e]
  ring

private lemma bs_hasDerivAt {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs : ℝ} (k : ℕ) {α : ℝ}
    (hα : 0 < α) (hsupp : μ (Icc 0 Cs)ᶜ = 0) :
    HasDerivAt (fun α : ℝ => ∫ t, (t / (α * t + 1)) ^ (k + 1) ∂μ)
      (-((k + 1 : ℝ) * ∫ t, (t / (α * t + 1)) ^ (k + 1 + 1) ∂μ)) α := by
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun α t => (t / (α * t + 1)) ^ (k + 1))
    (F' := fun α t => -((k + 1 : ℝ) * (t / (α * t + 1)) ^ (k + 1 + 1)))
    (bound := fun _ => (k + 1 : ℝ) * Cs ^ (k + 1 + 1))
    (s := Ioo (α / 2) (α + α / 2)) (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun y => (bs_meas k y).aestronglyMeasurable)
    (bs_integrable k hα.le hsupp)
    (((bs_meas (k + 1) α).const_mul _).neg).aestronglyMeasurable ?_ (integrable_const _) ?_).2
  · rw [integral_neg, integral_const_mul] at h
    exact h
  · filter_upwards [bs_ae hsupp] with t ht y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have := bs_pt (k + 1) hy0.le ht
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (by have := this.1; positivity)]
    exact mul_le_mul_of_nonneg_left this.2 (by positivity)
  · filter_upwards [bs_ae hsupp] with t ht y hy
    exact bs_pt_deriv k (by linarith [hy.1]) ht.1

private lemma bs_contDiffOn {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs : ℝ}
    (hsupp : μ (Icc 0 Cs)ᶜ = 0) : ∀ (n k : ℕ),
    ContDiffOn ℝ n (fun α : ℝ => ∫ t, (t / (α * t + 1)) ^ (k + 1) ∂μ) (Ioi 0) := by
  intro n
  induction n with
  | zero =>
    intro k
    exact contDiffOn_zero.2 (bs_cont k hsupp)
  | succ n ih =>
    intro k
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun x hx => (bs_hasDerivAt k hx hsupp).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    refine ((ih (k + 1)).const_smul (-((k + 1 : ℝ)))).congr ?_
    intro x hx
    rw [(bs_hasDerivAt k hx hsupp).deriv]
    simp only [smul_eq_mul]
    ring


private lemma bs_fderiv (g gt R : ℝ → ℝ) {α γ q s g' gt' R' : ℝ}
    (hg : HasDerivAt g g' α) (hgt : HasDerivAt gt gt' γ) (hR : HasDerivAt R R' q) :
    ∃ L : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ,
      HasFDerivAt (fun p : ℝ × ℝ × ℝ × ℝ => (p.2.1 * g p.2.1 - R p.2.2.2,
        p.2.2.1 * gt p.2.2.1 - R p.2.2.2, p.1 * p.2.2.2 - g p.2.1 * gt p.2.2.1)) L (s, α, γ, q) ∧
      ∀ d x y z : ℝ, L (d, x, y, z) = ((g α + α * g') * x - R' * z,
        (gt γ + γ * gt') * y - R' * z, d * q + s * z - g' * gt γ * x - g α * gt' * y) := by
  have hp1 : HasFDerivAt (fun p : ℝ × ℝ × ℝ × ℝ => p.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ)) (s, α, γ, q) :=
    hasFDerivAt_fst
  have hs2 : HasFDerivAt (fun p : ℝ × ℝ × ℝ × ℝ => p.2) (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))
      (s, α, γ, q) := hasFDerivAt_snd
  have ha1 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
      (α, γ, q) := hasFDerivAt_fst
  have hb1 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2) (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
      (α, γ, q) := hasFDerivAt_snd
  have hc1 : HasFDerivAt (fun x : ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (γ, q) :=
    hasFDerivAt_fst
  have hd1 : HasFDerivAt (fun x : ℝ × ℝ => x.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (γ, q) :=
    hasFDerivAt_snd
  have hpα : HasFDerivAt (fun p : ℝ × ℝ × ℝ × ℝ => p.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))))
      (s, α, γ, q) := ha1.comp (s, α, γ, q) hs2
  have hb2 : HasFDerivAt (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2) 
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))))
      (s, α, γ, q) := hb1.comp (s, α, γ, q) hs2
  have hpγ : HasFDerivAt (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)))))
      (s, α, γ, q) := hc1.comp (s, α, γ, q) hb2
  have hpq : HasFDerivAt (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)))))
      (s, α, γ, q) := hd1.comp (s, α, γ, q) hb2
  have hgα := hg.comp_hasFDerivAt (s, α, γ, q) hpα
  have hgtγ := hgt.comp_hasFDerivAt (s, α, γ, q) hpγ
  have hRq := hR.comp_hasFDerivAt (s, α, γ, q) hpq
  have c1 := (hpα.mul hgα).sub hRq
  have c2 := (hpγ.mul hgtγ).sub hRq
  have c3 := (hp1.mul hpq).sub (hgα.mul hgtγ)
  refine ⟨_, (c1.prodMk (c2.prodMk c3)), ?_⟩
  intro d x y z
  simp
  refine ⟨by ring, by ring, by ring⟩

private lemma bs_cd (g gt R : ℝ → ℝ) {α γ q s : ℝ} {n : WithTop ℕ∞}
    (hg : ContDiffAt ℝ n g α) (hgt : ContDiffAt ℝ n gt γ) (hR : ContDiffAt ℝ n R q) :
    ContDiffAt ℝ n (fun p : ℝ × ℝ × ℝ × ℝ => (p.2.1 * g p.2.1 - R p.2.2.2,
        p.2.2.1 * gt p.2.2.1 - R p.2.2.2, p.1 * p.2.2.2 - g p.2.1 * gt p.2.2.1)) (s, α, γ, q) := by
  have h1 : ContDiffAt ℝ n (fun p : ℝ × ℝ × ℝ × ℝ => p.2.1) (s, α, γ, q) := by fun_prop
  have h2 : ContDiffAt ℝ n (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.1) (s, α, γ, q) := by fun_prop
  have h3 : ContDiffAt ℝ n (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2) (s, α, γ, q) := by fun_prop
  have h4 : ContDiffAt ℝ n (fun p : ℝ × ℝ × ℝ × ℝ => p.1) (s, α, γ, q) := by fun_prop
  have g1 := hg.comp (s, α, γ, q) h1
  have g2 := hgt.comp (s, α, γ, q) h2
  have g3 := hR.comp (s, α, γ, q) h3
  exact ((h1.mul g1).sub g3).prodMk (((h2.mul g2).sub g3).prodMk ((h4.mul h3).sub (g1.mul g2)))

private lemma bs_isInv (f : ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ) (h : Function.Injective f) :
    f.IsInvertible := by
  have hs : Function.Surjective (f : ℝ × ℝ × ℝ →ₗ[ℝ] ℝ × ℝ × ℝ) :=
    LinearMap.injective_iff_surjective.1 h
  refine ⟨ContinuousLinearEquiv.ofBijective f (LinearMap.ker_eq_bot.2 h)
    (LinearMap.range_eq_top.2 hs), ?_⟩
  exact ContinuousLinearEquiv.coe_ofBijective _ _ _

/-- key algebra: `a1,a2 ≥ 0`, `r ≥ 0`, `h,h' > 0`, `s > 0`. -/
private lemma bs_alg {s a1 a2 r h h' x y z w : ℝ} (hh : 0 < h) (hh' : 0 < h') (e1 : h * x = r * z) (e2 : h' * y = r * z)
    (e3 : a1 * x + a2 * y + s * z = w) :
    z * (s + a1 * (r / h) + a2 * (r / h')) = w := by
  have hx : x = r * z / h := by field_simp; linarith
  have hy : y = r * z / h' := by field_simp; linarith
  rw [← e3, hx, hy]; ring


private lemma bs_mu_pos {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs : ℝ} (hsupp : μ (Icc 0 Cs)ᶜ = 0)
    (hν : 0 < ∫ t, t ∂μ) : μ (Ioi 0) ≠ 0 := by
  intro h0
  have h1 : ∀ᵐ t ∂μ, t = 0 := by
    have h2 : ∀ᵐ t ∂μ, ¬ (t ∈ Ioi (0:ℝ)) := by
      rw [MeasureTheory.ae_iff]; simp only [not_not]; exact h0
    filter_upwards [bs_ae hsupp, h2] with t ht1 ht2
    exact le_antisymm (not_lt.1 ht2) ht1.1
  have : ∫ t, t ∂μ = 0 := by
    rw [integral_eq_zero_of_ae]
    filter_upwards [h1] with t ht; simpa using ht
  linarith

private lemma bs_g_pos {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs α : ℝ} (hα : 0 ≤ α)
    (hsupp : μ (Icc 0 Cs)ᶜ = 0) (hμ : μ (Ioi 0) ≠ 0) :
    0 < ∫ t, t / (α * t + 1) ∂μ := by
  have hi : Integrable (fun t : ℝ => t / (α * t + 1)) μ := by
    simpa using bs_integrable (μ := μ) (Cs := Cs) 0 hα hsupp
  rw [integral_pos_iff_support_of_nonneg_ae _ hi]
  · refine lt_of_lt_of_le (pos_iff_ne_zero.2 hμ) (measure_mono (fun t ht => ?_))
    have ht' : 0 < t := ht
    have : 0 < α * t + 1 := by nlinarith [mul_nonneg hα ht'.le]
    exact (div_pos ht' this).ne'
  · filter_upwards [bs_ae hsupp] with t ht
    have := (bs_pt (Cs := Cs) 0 hα ht).1
    simpa using this

private lemma bs_g_nonneg {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs α : ℝ} (hα : 0 ≤ α)
    (hsupp : μ (Icc 0 Cs)ᶜ = 0) :
    0 ≤ ∫ t, t / (α * t + 1) ∂μ := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [bs_ae hsupp] with t ht
  have := (bs_pt (Cs := Cs) 0 hα ht).1
  simpa using this

private lemma bs_g_deriv {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs α : ℝ} (hα : 0 < α)
    (hsupp : μ (Icc 0 Cs)ᶜ = 0) :
    HasDerivAt (fun α : ℝ => ∫ t, t / (α * t + 1) ∂μ)
      (-∫ t, (t / (α * t + 1)) ^ 2 ∂μ) α := by
  simpa using bs_hasDerivAt (μ := μ) (Cs := Cs) 0 hα hsupp

private lemma bs_g_cdiff {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs α : ℝ} (hα : 0 < α)
    (hsupp : μ (Icc 0 Cs)ᶜ = 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun α : ℝ => ∫ t, t / (α * t + 1) ∂μ) α := by
  have h := contDiffOn_infty.2 (fun n => bs_contDiffOn (μ := μ) hsupp n 0)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun α : ℝ => ∫ t, t / (α * t + 1) ∂μ) (Ioi 0) := by
    refine h.congr ?_
    intro x _
    simp
  exact h2.contDiffAt (isOpen_Ioi.mem_nhds hα)

private lemma bs_h_pos {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs α : ℝ} (hα : 0 < α)
    (hsupp : μ (Icc 0 Cs)ᶜ = 0) (hμ : μ (Ioi 0) ≠ 0) :
    0 < (∫ t, t / (α * t + 1) ∂μ) + α * (-∫ t, (t / (α * t + 1)) ^ 2 ∂μ) := by
  have hi1 : Integrable (fun t : ℝ => t / (α * t + 1)) μ := by
    simpa using bs_integrable (μ := μ) (Cs := Cs) 0 hα.le hsupp
  have hi2 : Integrable (fun t : ℝ => (t / (α * t + 1)) ^ 2) μ := by
    simpa using bs_integrable (μ := μ) (Cs := Cs) 1 hα.le hsupp
  have e : (∫ t, t / (α * t + 1) ∂μ) + α * (-∫ t, (t / (α * t + 1)) ^ 2 ∂μ)
      = ∫ t, t / (α * t + 1) ^ 2 ∂μ := by
    rw [mul_neg, ← integral_const_mul, ← sub_eq_add_neg, ← integral_sub hi1 (hi2.const_mul α)]
    congr 1
    ext t
    have hd : 0 < α * t + 1 ∨ True := Or.inr trivial
    by_cases hd : α * t + 1 = 0
    · simp [hd]
    · field_simp
      ring
  rw [e]
  have hi3 : Integrable (fun t : ℝ => t / (α * t + 1) ^ 2) μ := by
    refine Integrable.mono' (integrable_const (Cs)) (by fun_prop : Measurable fun t : ℝ => t / (α * t + 1) ^ 2).aestronglyMeasurable ?_
    filter_upwards [bs_ae hsupp] with t ht
    obtain ⟨h0, h1⟩ := ht
    have hd : 1 ≤ (α * t + 1) ^ 2 := by nlinarith [mul_nonneg hα.le h0]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h0 (by positivity))]
    calc t / (α * t + 1) ^ 2 ≤ t := div_le_self h0 hd
      _ ≤ Cs := h1
  rw [integral_pos_iff_support_of_nonneg_ae _ hi3]
  · refine lt_of_lt_of_le (pos_iff_ne_zero.2 hμ) (measure_mono (fun t ht => ?_))
    have ht' : 0 < t := ht
    have : 0 < α * t + 1 := by nlinarith [mul_nonneg hα.le ht'.le]
    exact (div_pos ht' (by positivity)).ne'
  · filter_upwards [bs_ae hsupp] with t ht
    have : 0 ≤ α * t + 1 := by nlinarith [mul_nonneg hα.le ht.1]
    exact div_nonneg ht.1 (by positivity)

private lemma bs_conv {μ : Measure ℝ} {s a : ℝ} (hs : 0 < s) :
    ∫ t, t / (a * t + s) ∂μ = (∫ t, t / ((a / s) * t + 1) ∂μ) / s := by
  rw [← integral_div]
  congr 1
  ext t
  field_simp


private lemma bs_fwd {w : ℕ → ℝ} (hw : WeightSeq w) {Cs : ℝ} {ν ν' : FiniteMeasure ℝ}
    (hs1 : (ν : Measure ℝ) (Icc 0 Cs)ᶜ = 0) (hs2 : (ν' : Measure ℝ) (Icc 0 Cs)ᶜ = 0)
    (hμ : (ν : Measure ℝ) (Ioi 0) ≠ 0) (hμ' : (ν' : Measure ℝ) (Ioi 0) ≠ 0)
    {s σ σ' a c : ℝ} (hs : 0 < s) (hsol : IsBranchSol (Fw w) ν ν' s (σ, σ', a, c)) :
    0 < σ ∧ 0 < σ' ∧ 0 < a ∧ 0 < c ∧ 0 < s * σ * σ' ∧
      (∫ t, t / ((a / s) * t + 1) ∂(ν : Measure ℝ)) = s * σ ∧
      (∫ t, t / ((c / s) * t + 1) ∂(ν' : Measure ℝ)) = s * σ' ∧
      (a / s) * (s * σ) = rW w (s * σ * σ') ∧ (c / s) * (s * σ') = rW w (s * σ * σ') := by
  obtain ⟨hσ0, hσ'0, ha0, hc0, hσ, hσ', ha, hc⟩ := hsol
  have hgs : (∫ t, t / ((a / s) * t + 1) ∂(ν : Measure ℝ)) = s * σ := by
    rw [hσ, bs_conv hs]
    generalize (∫ t, t / ((a / s) * t + 1) ∂(ν : Measure ℝ)) = I
    field_simp
  have hgs' : (∫ t, t / ((c / s) * t + 1) ∂(ν' : Measure ℝ)) = s * σ' := by
    rw [hσ', bs_conv hs]
    generalize (∫ t, t / ((c / s) * t + 1) ∂(ν' : Measure ℝ)) = I
    field_simp
  have hgp : 0 < ∫ t, t / ((a / s) * t + 1) ∂(ν : Measure ℝ) :=
    bs_g_pos (div_nonneg ha0 hs.le) hs1 hμ
  have hgp' : 0 < ∫ t, t / ((c / s) * t + 1) ∂(ν' : Measure ℝ) :=
    bs_g_pos (div_nonneg hc0 hs.le) hs2 hμ'
  have hσp : 0 < σ := by
    have h1 : 0 < s * σ := hgs ▸ hgp
    by_contra h
    push Not at h
    nlinarith
  have hσ'p : 0 < σ' := by
    have h1 : 0 < s * σ' := hgs' ▸ hgp'
    by_contra h
    push Not at h
    nlinarith
  have hq : 0 < s * σ * σ' := by positivity
  have hF : 0 < Fw w (s * σ * σ') := (Fw_admissible hw).pos _ hq.le
  have hap : 0 < a := by rw [ha]; positivity
  have hcp : 0 < c := by rw [hc]; positivity
  refine ⟨hσp, hσ'p, hap, hcp, hq, hgs, hgs', ?_, ?_⟩
  · unfold rW
    rw [ha]; field_simp
  · unfold rW
    rw [hc]; field_simp

private lemma bs_bwd {w : ℕ → ℝ} {ν ν' : FiniteMeasure ℝ} {s α γ q : ℝ} (hs : 0 < s)
    (hα : 0 < α) (hγ : 0 < γ)
    (hg : 0 < ∫ t, t / (α * t + 1) ∂(ν : Measure ℝ))
    (hgt : 0 < ∫ t, t / (γ * t + 1) ∂(ν' : Measure ℝ))
    (e1 : α * (∫ t, t / (α * t + 1) ∂(ν : Measure ℝ)) = rW w q)
    (e2 : γ * (∫ t, t / (γ * t + 1) ∂(ν' : Measure ℝ)) = rW w q)
    (e3 : s * q = (∫ t, t / (α * t + 1) ∂(ν : Measure ℝ)) *
      (∫ t, t / (γ * t + 1) ∂(ν' : Measure ℝ))) :
    IsBranchSol (Fw w) ν ν' s ((∫ t, t / (α * t + 1) ∂(ν : Measure ℝ)) / s,
      (∫ t, t / (γ * t + 1) ∂(ν' : Measure ℝ)) / s, s * α, s * γ) := by
  set g := ∫ t, t / (α * t + 1) ∂(ν : Measure ℝ) with hgdef
  set gt := ∫ t, t / (γ * t + 1) ∂(ν' : Measure ℝ) with hgtdef
  have hq : s * (g / s) * (gt / s) = q := by
    field_simp; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · positivity
  · positivity
  · rw [bs_conv hs, mul_div_cancel_left₀ α hs.ne']
  · rw [bs_conv hs, mul_div_cancel_left₀ γ hs.ne']
  · rw [hq]
    unfold rW at e1
    have : g * (s * α) = g * (gt * Fw w q) := by
      calc g * (s * α) = s * (α * g) := by ring
        _ = s * (q * Fw w q) := by rw [e1]
        _ = (s * q) * Fw w q := by ring
        _ = g * gt * Fw w q := by rw [e3]
        _ = g * (gt * Fw w q) := by ring
    have := mul_left_cancel₀ hg.ne' this
    field_simp
    linarith
  · rw [hq]
    unfold rW at e2
    have : gt * (s * γ) = gt * (g * Fw w q) := by
      calc gt * (s * γ) = s * (γ * gt) := by ring
        _ = s * (q * Fw w q) := by rw [e2]
        _ = (s * q) * Fw w q := by ring
        _ = g * gt * Fw w q := by rw [e3]
        _ = gt * (g * Fw w q) := by ring
    have := mul_left_cancel₀ hgt.ne' this
    field_simp
    linarith

private lemma bs_local {w : ℕ → ℝ} (hw : WeightSeq w) {Cs gam : ℝ}
    (hC : 0 < Cs) (hgam : 0 < gam) {ν ν' : FiniteMeasure ℝ} (hp : (ν, ν') ∈ classK Cs gam)
    (hν : 0 < ∫ t, t ∂(ν : Measure ℝ)) (hν' : 0 < ∫ t, t ∂(ν' : Measure ℝ))
    {s0 : ℝ} (hs0 : 0 < s0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => branchSol (Fw w) ν ν' s) s0 ∧
    ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ =>
      s * (branchSol (Fw w) ν ν' s).1 * (branchSol (Fw w) ν ν' s).2.1) s0 ∧
    |deriv (fun s : ℝ => s * (branchSol (Fw w) ν ν' s).1 * (branchSol (Fw w) ν ν' s).2.1) s0|
      ≤ (s0 * (branchSol (Fw w) ν ν' s0).1 * (branchSol (Fw w) ν ν' s0).2.1) / s0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hp : (ν, ν') ∈ classK Cs gam := ⟨h1, h2, h3, h4⟩
  have hμ := bs_mu_pos h2 hν
  have hμ' := bs_mu_pos h4 hν'
  have hsol0 := branchSol_spec (Fw_admissible hw) hC hgam hp hs0
  rcases hx : branchSol (Fw w) ν ν' s0 with ⟨σ, σ', a, c⟩
  rw [hx] at hsol0
  obtain ⟨hσ, hσ', ha, hc, hq0, hg0, hgt0, e1, e2⟩ := bs_fwd hw h2 h4 hμ hμ' hs0 hsol0
  set α0 := a / s0 with hα0def
  set γ1 := c / s0 with hγ1def
  set q0 := s0 * σ * σ' with hq0def
  have hα0 : 0 < α0 := div_pos ha hs0
  have hγ1 : 0 < γ1 := div_pos hc hs0
  -- the scalar functions
  set g : ℝ → ℝ := fun α => ∫ t, t / (α * t + 1) ∂(ν : Measure ℝ) with hgdef
  set gt : ℝ → ℝ := fun α => ∫ t, t / (α * t + 1) ∂(ν' : Measure ℝ) with hgtdef
  have hgd : HasDerivAt g (-∫ t, (t / (α0 * t + 1)) ^ 2 ∂(ν : Measure ℝ)) α0 :=
    bs_g_deriv hα0 h2
  have hgtd : HasDerivAt gt (-∫ t, (t / (γ1 * t + 1)) ^ 2 ∂(ν' : Measure ℝ)) γ1 :=
    bs_g_deriv hγ1 h4
  have hR := (lem_app_de_scalar_iii hw).2.2.2.1 q0 hq0
  have hR' := (lem_app_de_scalar_iii hw).2.2.2.2.1 q0 hq0
  set R' := ∑' j, w j ^ 2 * ∫ g, g ^ 2 / (1 + w j ^ 2 * q0 * g ^ 2) ^ 2 ∂(gaussianReal 0 1)
    with hR'def
  obtain ⟨L, hL, hLval⟩ := bs_fderiv g gt (rW w) (s := s0) hgd hgtd hR
  -- positivity facts at the base point
  have hP2 : 0 ≤ ∫ t, (t / (α0 * t + 1)) ^ 2 ∂(ν : Measure ℝ) := integral_nonneg (fun t => sq_nonneg _)
  have hP2t : 0 ≤ ∫ t, (t / (γ1 * t + 1)) ^ 2 ∂(ν' : Measure ℝ) :=
    integral_nonneg (fun t => sq_nonneg _)
  have hH : 0 < g α0 + α0 * (-∫ t, (t / (α0 * t + 1)) ^ 2 ∂(ν : Measure ℝ)) :=
    bs_h_pos hα0 h2 hμ
  have hHt : 0 < gt γ1 + γ1 * (-∫ t, (t / (γ1 * t + 1)) ^ 2 ∂(ν' : Measure ℝ)) :=
    bs_h_pos hγ1 h4 hμ'
  have hgnn : 0 ≤ g α0 := bs_g_nonneg hα0.le h2
  have hgtnn : 0 ≤ gt γ1 := bs_g_nonneg hγ1.le h4
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hFcd : ContDiffAt ℝ (⊤ : ℕ∞) (Fw w) q0 :=
    ((lem_app_de_scalar_ii hw).2.2.2.2.1).contDiffAt (Ici_mem_nhds hq0)
  have hRcd : ContDiffAt ℝ (⊤ : ℕ∞) (rW w) q0 := contDiffAt_id.mul hFcd
  have cdf := bs_cd g gt (rW w) (s := s0) (bs_g_cdiff hα0 h2) (bs_g_cdiff hγ1 h4) hRcd
  have hf0 : (fun p : ℝ × ℝ × ℝ × ℝ => (p.2.1 * g p.2.1 - rW w p.2.2.2,
      p.2.2.1 * gt p.2.2.1 - rW w p.2.2.2, p.1 * p.2.2.2 - g p.2.1 * gt p.2.2.1))
        (s0, α0, γ1, q0) = 0 := by
    have hg0' : g α0 = s0 * σ := hg0
    have hgt0' : gt γ1 = s0 * σ' := hgt0
    simp only [Prod.mk_eq_zero]
    refine ⟨?_, ?_, ?_⟩
    · rw [hg0']; linarith
    · rw [hgt0']; linarith
    · rw [hg0', hgt0', hq0def]; ring
  set κ1 := -(-∫ t, (t / (α0 * t + 1)) ^ 2 ∂(ν : Measure ℝ)) * gt γ1 with hκ1
  set κ2 := -(g α0 * -∫ t, (t / (γ1 * t + 1)) ^ 2 ∂(ν' : Measure ℝ)) with hκ2
  have hκ1p : 0 ≤ κ1 := by rw [hκ1]; exact mul_nonneg (by linarith) hgtnn
  have hκ2p : 0 ≤ κ2 := by rw [hκ2]; exact by nlinarith [mul_nonneg hgnn hP2t]
  have hR'p : 0 < R' := hR'
  have hkap : 0 < s0 + κ1 * (R' / (g α0 + α0 * (-∫ t, (t / (α0 * t + 1)) ^ 2 ∂(ν : Measure ℝ))))
      + κ2 * (R' / (gt γ1 + γ1 * (-∫ t, (t / (γ1 * t + 1)) ^ 2 ∂(ν' : Measure ℝ)))) := by
    have := mul_nonneg hκ1p (div_nonneg hR'p.le hH.le)
    have := mul_nonneg hκ2p (div_nonneg hR'p.le hHt.le)
    linarith
  have if₂ : (fderiv ℝ (fun p : ℝ × ℝ × ℝ × ℝ => (p.2.1 * g p.2.1 - rW w p.2.2.2,
      p.2.2.1 * gt p.2.2.1 - rW w p.2.2.2, p.1 * p.2.2.2 - g p.2.1 * gt p.2.2.1))
        (s0, α0, γ1, q0) ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ × ℝ)).IsInvertible := by
    rw [hL.fderiv]
    apply bs_isInv
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, y, z⟩ hv
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hv
    rw [hLval] at hv
    simp only [Prod.mk_eq_zero] at hv
    obtain ⟨v1, v2, v3⟩ := hv
    have hz := bs_alg (s := s0) (a1 := κ1) (a2 := κ2) (r := R') (x := x) (y := y) (z := z)
      (w := 0) hH hHt (by linarith) (by linarith) (by rw [hκ1, hκ2]; linarith)
    have hz0 : z = 0 := by
      rcases mul_eq_zero.1 hz with h | h
      · exact h
      · linarith
    have hx0 : x = 0 := by
      have : (g α0 + α0 * (-∫ t, (t / (α0 * t + 1)) ^ 2 ∂(ν : Measure ℝ))) * x = 0 := by
        rw [hz0] at v1; linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact h
    have hy0 : y = 0 := by
      have : (gt γ1 + γ1 * (-∫ t, (t / (γ1 * t + 1)) ^ 2 ∂(ν' : Measure ℝ))) * y = 0 := by
        rw [hz0] at v2; linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact h
    rw [hx0, hy0, hz0]; rfl
  have hψ := cdf.contDiffAt_implicitFunction hn if₂
  have hψ0 : (cdf.implicitFunction hn if₂) s0 = (α0, γ1, q0) :=
    cdf.implicitFunction_apply_self hn if₂
  have hev := cdf.eventually_apply_implicitFunction hn if₂
  set ψ := cdf.implicitFunction hn if₂ with hψdef
  have hψc : ContinuousAt ψ s0 := hψ.continuousAt
  have ev0 : ∀ᶠ s in 𝓝 s0, 0 < s := eventually_gt_nhds hs0
  have ev1 : ∀ᶠ s in 𝓝 s0, 0 < (ψ s).1 := by
    have h : ContinuousAt (fun s => (ψ s).1) s0 := continuous_fst.continuousAt.comp hψc
    refine Filter.Tendsto.eventually h (eventually_gt_nhds ?_)
    show 0 < (ψ s0).1
    rw [hψ0]; exact hα0
  have ev2 : ∀ᶠ s in 𝓝 s0, 0 < (ψ s).2.1 := by
    have h : ContinuousAt (fun s => (ψ s).2.1) s0 :=
      (continuous_fst.comp continuous_snd).continuousAt.comp hψc
    refine Filter.Tendsto.eventually h (eventually_gt_nhds ?_)
    show 0 < (ψ s0).2.1
    rw [hψ0]; exact hγ1
  have hglue : ∀ᶠ s in 𝓝 s0, branchSol (Fw w) ν ν' s =
      (g (ψ s).1 / s, gt (ψ s).2.1 / s, s * (ψ s).1, s * (ψ s).2.1) ∧
      s * (branchSol (Fw w) ν ν' s).1 * (branchSol (Fw w) ν ν' s).2.1 = (ψ s).2.2 := by
    filter_upwards [hev, ev0, ev1, ev2] with s hfs hs hα hγ
    have hfs' := hfs.trans hf0
    simp only [Prod.mk_eq_zero] at hfs'
    obtain ⟨k1, k2, k3⟩ := hfs'
    have hsolΦ := bs_bwd (w := w) (ν := ν) (ν' := ν') (q := (ψ s).2.2) hs hα hγ
      (bs_g_pos hα.le h2 hμ) (bs_g_pos hγ.le h4 hμ') (by linarith) (by linarith) (by linarith)
    have huniq := (thm_app_de_branch_i (Fw_admissible hw) hC hgam ν ν' hp s hs).1.unique
      (branchSol_spec (Fw_admissible hw) hC hgam hp hs) hsolΦ
    refine ⟨huniq, ?_⟩
    rw [huniq]
    show s * (g (ψ s).1 / s) * (gt (ψ s).2.1 / s) = (ψ s).2.2
    field_simp
    linarith
  have hψ1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun s => (ψ s).1) s0 := contDiffAt_fst.comp s0 hψ
  have hψ2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun s => (ψ s).2.1) s0 :=
    contDiffAt_fst.comp s0 (contDiffAt_snd.comp s0 hψ)
  have hψ3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun s => (ψ s).2.2) s0 :=
    contDiffAt_snd.comp s0 (contDiffAt_snd.comp s0 hψ)
  have hgc : ContDiffAt ℝ (⊤ : ℕ∞) g (ψ s0).1 := by
    rw [hψ0]; exact bs_g_cdiff hα0 h2
  have hgtc : ContDiffAt ℝ (⊤ : ℕ∞) gt (ψ s0).2.1 := by
    rw [hψ0]; exact bs_g_cdiff hγ1 h4
  have c1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => g (ψ s).1 / s) s0 :=
    ContDiffAt.div (f := fun s : ℝ => g (ψ s).1) (g := fun s : ℝ => s)
      (ContDiffAt.comp (g := g) (f := fun s : ℝ => (ψ s).1) s0 hgc hψ1) contDiffAt_id hs0.ne'
  have c2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => gt (ψ s).2.1 / s) s0 :=
    ContDiffAt.div (f := fun s : ℝ => gt (ψ s).2.1) (g := fun s : ℝ => s)
      (ContDiffAt.comp (g := gt) (f := fun s : ℝ => (ψ s).2.1) s0 hgtc hψ2) contDiffAt_id hs0.ne'
  have c3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => s * (ψ s).1) s0 := contDiffAt_id.mul hψ1
  have c4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => s * (ψ s).2.1) s0 := contDiffAt_id.mul hψ2
  have hΦ : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ =>
      (g (ψ s).1 / s, gt (ψ s).2.1 / s, s * (ψ s).1, s * (ψ s).2.1)) s0 :=
    c1.prodMk (c2.prodMk (c3.prodMk c4))
  refine ⟨hΦ.congr_of_eventuallyEq (hglue.mono fun s h => h.1),
    hψ3.congr_of_eventuallyEq (hglue.mono fun s h => h.2), ?_⟩
  -- the derivative bound
  have hψd : HasDerivAt ψ (fderiv ℝ ψ s0 1) s0 := (hψ.differentiableAt hn).hasFDerivAt.hasDerivAt
  set ψ' := fderiv ℝ ψ s0 1 with hψ'def
  have hL'' : HasFDerivAt (fun p : ℝ × ℝ × ℝ × ℝ => (p.2.1 * g p.2.1 - rW w p.2.2.2,
      p.2.2.1 * gt p.2.2.1 - rW w p.2.2.2, p.1 * p.2.2.2 - g p.2.1 * gt p.2.2.1)) L
      ((fun s => (s, ψ s)) s0) := by
    show HasFDerivAt _ L (s0, ψ s0)
    rw [hψ0]; exact hL
  have hcomp := hL''.comp_hasDerivAt s0 ((hasDerivAt_id s0).prodMk hψd)
  have hzero : L (1, ψ') = 0 :=
    hcomp.unique ((hasDerivAt_const s0 (0 : ℝ × ℝ × ℝ)).congr_of_eventuallyEq
      (hev.mono fun s hs => hs.trans hf0))
  have hz := (hLval 1 ψ'.1 ψ'.2.1 ψ'.2.2).symm.trans hzero
  simp only [Prod.mk_eq_zero] at hz
  obtain ⟨z1, z2, z3⟩ := hz
  have hk := bs_alg (s := s0) (a1 := κ1) (a2 := κ2) (r := R') (x := ψ'.1) (y := ψ'.2.1)
    (z := ψ'.2.2) (w := -q0) hH hHt (by linarith) (by linarith) (by rw [hκ1, hκ2]; linarith)
  have hq' : HasDerivAt (fun s => (ψ s).2.2) ψ'.2.2 s0 := by
    have h1 : HasDerivAt (fun s => (ψ s).2) ψ'.2 s0 := by
      exact HasFDerivAt.comp_hasDerivAt (l := Prod.snd) (f := ψ) s0
        (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ × ℝ)) hψd
    exact HasFDerivAt.comp_hasDerivAt (l := Prod.snd) (f := fun s => (ψ s).2) s0
        (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ)) h1
  have hqeq : (fun s : ℝ => s * (branchSol (Fw w) ν ν' s).1 * (branchSol (Fw w) ν ν' s).2.1)
      =ᶠ[𝓝 s0] fun s => (ψ s).2.2 := hglue.mono fun s h => h.2
  have hderiv : deriv (fun s : ℝ => s * (branchSol (Fw w) ν ν' s).1 *
      (branchSol (Fw w) ν ν' s).2.1) s0 = ψ'.2.2 := by
    rw [hqeq.deriv_eq]; exact hq'.deriv
  rw [hderiv]
  have hDpos := hkap
  have hzq : ψ'.2.2 = -q0 / (s0 + κ1 * (R' / (g α0 + α0 * (-∫ t, (t / (α0 * t + 1)) ^ 2 ∂(ν : Measure ℝ))))
      + κ2 * (R' / (gt γ1 + γ1 * (-∫ t, (t / (γ1 * t + 1)) ^ 2 ∂(ν' : Measure ℝ))))) :=
    eq_div_of_mul_eq hDpos.ne' hk
  have hDge : s0 ≤ s0 + κ1 * (R' / (g α0 + α0 * (-∫ t, (t / (α0 * t + 1)) ^ 2 ∂(ν : Measure ℝ))))
      + κ2 * (R' / (gt γ1 + γ1 * (-∫ t, (t / (γ1 * t + 1)) ^ 2 ∂(ν' : Measure ℝ)))) := by
    have := mul_nonneg hκ1p (div_nonneg hR'p.le hH.le)
    have := mul_nonneg hκ2p (div_nonneg hR'p.le hHt.le)
    linarith
  rw [hzq, abs_div, abs_neg, abs_of_pos hq0, abs_of_pos hDpos]
  exact div_le_div_of_nonneg_left hq0.le hs0 hDge

/-- `thm:app-de-branch`(iv), snapshot `cr-2026-10-23`. LaTeX
(`sections/02-deterministic-equivalents/section.tex` l.164–201; part (iv) is
`\item (Smoothness in $s$.)` at l.196–199; the whole theorem is given as in the source):
```
\begin{theorem}[The weighted branch]\label{thm:app-de-branch}
Let $w$ be nonnegative, summable and not all zero, and let $C_\Sigma,\gamma_\star>0$.
\begin{enumerate}[label=(\roman*)]
\item (Existence and uniqueness.) For every $(\nu,\tilde\nu)\in\mathcal K$ and
every $s>0$ the system \cref{eqn:app-de-system} at $z=-s$ has exactly one
solution in $[0,\infty)^4$. It satisfies
\begin{equation}\label{eqn:app-de-box}
\sigma,\tilde\sigma\le\frac{\gamma_\star C_\Sigma}{s},\qquad
\tilde s_1,s_1\le\gamma_\star C_\Sigma\,\sw2,\qquad q\le\frac{(\gamma_\star C_\Sigma)^2}{s}.
\end{equation}
\item (Continuity.) Equip $\mathcal K$ with the topology of weak convergence
against $C([0,C_\Sigma])$ in each coordinate. The solution map
$(s,\nu,\tilde\nu)\mapsto(\sigma,\tilde\sigma,\tilde s_1,s_1)$ is continuous on
$(0,\infty)\times\mathcal K$, and for every compact $I\subset(0,\infty)$ it is
uniformly continuous on $I\times\mathcal K$.
\item (Stability under approximate roots.) Let $I\subset(0,\infty)$ be compact
with $s_-\defeq\min I$. For every $\epsilon>0$ there is $\delta>0$, depending
only on $(\epsilon,I,C_\Sigma,\gamma_\star,w)$, with the following property.
If $(\nu,\tilde\nu)\in\mathcal K$, $s\in I$, and
$(\sigma',\tilde\sigma',a',c')\in[0,\gamma_\star C_\Sigma/s_-]^2\times[0,\gamma_\star C_\Sigma\sw2]^2$
satisfy, with $q'=s\sigma'\tilde\sigma'$,
\[
\begin{gathered}
\Big|\sigma'-\int\frac{x}{s+a'x}\,\nu(dx)\Big|\le\delta,\qquad
\Big|\tilde\sigma'-\int\frac{x}{s+c'x}\,\tilde\nu(dx)\Big|\le\delta,\\
\abs{a'-s\tilde\sigma'F_w(q')}\le\delta,\qquad
\abs{c'-s\sigma'F_w(q')}\le\delta,
\end{gathered}
\]
then $\abs{\sigma'-\sigma}+\abs{\tilde\sigma'-\tilde\sigma}+\abs{a'-\tilde s_1}+\abs{c'-s_1}\le\epsilon$,
where $(\sigma,\tilde\sigma,\tilde s_1,s_1)$ is the solution of
\cref{eqn:app-de-system} at $z=-s$ for $(\nu,\tilde\nu)$.
\item (Smoothness in $s$.) Fix $(\nu,\tilde\nu)\in\mathcal K$ with
$\int x\,\nu(dx)>0$ and $\int x\,\tilde\nu(dx)>0$. Then
$s\mapsto(\sigma,\tilde\sigma,\tilde s_1,s_1,q)(-s)$ is $C^\infty$ on $(0,\infty)$,
and $\abs{q'(s)}\le q(s)/s$.
\end{enumerate}
\end{theorem}
```
Encoding: `(σ, σ̃, s̃₁, s₁)(-s)` is `branchSol (Fw w) ν ν' s`; `q(-s) = s σ σ̃` is the `let`-bound `q`. The hypotheses `hw`, `hC`, `hγ`, `hp` are the theorem's preamble and the class `𝒦` of `eqn:app-de-class`; `hν`, `hν'` are `∫ x dν > 0`, `∫ x dν̃ > 0`. The conclusion is the smoothness on `(0,∞)` of the solution tuple and of `q`, and the bound `|q'(s)| ≤ q(s)/s` for every `s > 0`. -/
theorem thm_app_de_branch_iv {w : ℕ → ℝ} (hw : WeightSeq w) {Cs γ : ℝ}
    (hC : 0 < Cs) (hγ : 0 < γ) {ν ν' : FiniteMeasure ℝ} (hp : (ν, ν') ∈ classK Cs γ)
    (hν : 0 < ∫ t, t ∂(ν : Measure ℝ)) (hν' : 0 < ∫ t, t ∂(ν' : Measure ℝ)) :
    let q : ℝ → ℝ := fun s =>
      s * (branchSol (Fw w) ν ν' s).1 * (branchSol (Fw w) ν ν' s).2.1
    ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => branchSol (Fw w) ν ν' s) (Ioi 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) q (Ioi 0) ∧
      ∀ s : ℝ, 0 < s → |deriv q s| ≤ q s / s := by
  intro q
  refine ⟨fun s hs => (bs_local hw hC hγ hp hν hν' hs).1.contDiffWithinAt,
    fun s hs => (bs_local hw hC hγ hp hν hν' hs).2.1.contDiffWithinAt,
    fun s hs => (bs_local hw hC hγ hp hν hν' hs).2.2⟩

end Muon.DetEquiv

end

import Muon.PowerLaw.VolMeso

set_option linter.style.longLine false

/-!
# Appendix G: supercritical volatility, part-form (work package L-G.9)

Snapshot `cr-2026-10-23`. Source: `sections/06-power-law/section.tex`: `lem:app-pl-supervol`
(l.2271-2277, proof l.2279-2360); part (iii) of `thm:app-pl-volatility` (l.911-940); the volatility
half for `1 < α` of `thm:app-pl-triple` (l.866-872), declared as `triple_vol_gt_one`; the endpoint laws
of `G_{α,β}` in `prop:app-pl-profiles`(ii) (l.839-846). Card: `sections/06-power-law/CARD.md` §2, §3, §5
(L-G.9), §6 #1, #10, #15.

Representation choices:

* Standing regime `assum_app_pl_regime` (`Muon.PowerLaw.Continuum`) for every row statement, plus the
  source's `1 < α` (`hα1`). Profile statements with no row sequence take `0 < β < 1` (`hβ0`, `hβ1`), as
  in `VolKernel`.
* Profiles are reused: `profG` (`G_{α,β}`, `eqn:app-pl-G`), `profGamma` (`Γ_α`), `profTheta`, `profDelta`,
  `profZeta`, `profT` of `Muon.PowerLaw.Profiles`, and `DLag`, `MLag`, `Qm`, `Efun` of `Muon.PowerLaw.Weights`.
  `Kc α` is `K_α` and `icCross α B = B / K_α` is `i_c` (`Continuum`). Rows `rowIdx`, `rowFrac` and the
  hypotheses `volHBound` are those of `Muon.PowerLaw.VolMeso`.
* The source's `X ≝ i/i_c = K_α i/B` (l.2269) is written inline as `rowIdx (i n) / icCross α (B n)`. It is
  not a new definition.
* `vPart` stands for `𝔳_i(0)` (part form, card §2). Its identification with the limit of `𝔳_i(0)` is
  `prop:app-pl-vol-zero` (L-G.13). The `lem:app-pl-supervol` claims use only `vPart`, and need no
  hypothesis: their proof is a finite-dimensional integral estimate.
* Finiteness of `G_{α,β}` (`lem:app-pl-supervol`, "finite") is stated as `Integrable` of each lag integrand on
  `(0,∞)²` (product Lebesgue measure) and `Summable` of the lag sums, so no `tsum` or Bochner junk value is
  asserted. Positivity and continuity are stated on `Ioi 0`.
* Endpoint laws of `G_{α,β}` are `Tendsto` at `𝓝[>] 0` and `IsEquivalent atTop`, as in `eqn:app-pl-crossover-ends`.
* `Γ_α(x) ∼ 4K_α²/(α-1) x` as `x ↓ 0` is `IsEquivalent (𝓝[>] 0)`.
* Quantifiers. Row claims are `∀`-over-row-sequences: the row sequence `i : ∀ n, Fin (N n)` is fixed first,
  then `rowIdx (i n) → ∞` (`i → ∞`), then the limit hypothesis on `X`. The source's "`X → X_0`" is the
  sequential `Tendsto` form.
* `thm_app_pl_volatility_iii_part` carries `volHBound` (card §5) because its bulk conjunct uses part (i)
  (`thm_app_pl_volatility_i_part`). `volHPSD` (card §5) is not included: no step of part (iii) uses
  `lem:app-pl-pieces`. This is recorded in the result JSON.
* `triple_vol_gt_one` is the volatility half of `thm:app-pl-triple` for `1 < α` with the super approximant
  `vhatSuper` (`eqn:app-pl-approx-super`, second display, defined here), in the uniform form of
  `triple_vol_le_one`.

-/

open MeasureTheory Filter Topology Set Asymptotics

noncomputable section

namespace Muon.PowerLaw

/-! ## Super approximant -/

/-- `v̂_i` for `α > 1` (`eqn:app-pl-approx-super`, second display; snapshot `cr-2026-10-23`). LaTeX,
verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-approx-super}
\sqrt2\,\widehat{\mathfrak d}_i\defeq b_N\,\Phi_{\alpha,\bmom}\Big(\Big(\frac{i_{\mathrm c}}{i}\Big)^\alpha\Big)\,
\frac{\Psi_\alpha(i/N)}{d_\alpha\sqrt{K_\alpha}\,(i/N)^{-(\alpha-1)/2}},\qquad
\widehat{\mathfrak v}_i\defeq G_{\alpha,\bmom}\Big(\frac{i}{i_{\mathrm c}}\Big)\,
\frac{\Gamma_\alpha(i/N)}{4K_\alpha^2(i/N)/(\alpha-1)} .
\end{equation}
-/
def vhatSuper (β α : ℝ) (B : ℕ) {N : ℕ} (i : Fin N) : ℝ :=
  profG α β (rowIdx i / icCross α B) * profGamma α (rowFrac i) /
    (4 * Kc α ^ 2 * rowFrac i / (α - 1))

/-! ## Private helpers for `lem_app_pl_supervol_i_*` (fully proved) -/

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_emaW_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (a : ℕ) : 0 < emaW β a := by
  unfold emaW
  exact mul_pos (by linarith) (pow_pos hβ0 a)

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_w2_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Summable (fun a : ℕ => emaW β a ^ 2) := by
  have hr : β ^ 2 < 1 := pow_lt_one₀ hβ0.le hβ1 (by norm_num)
  have key : (fun j : ℕ => emaW β j ^ 2) = fun j => (1 - β) ^ 2 * (β ^ 2) ^ j := by
    funext j
    unfold emaW
    rw [mul_pow, pow_right_comm β j 2]
  rw [key]
  exact (summable_geometric_of_lt_one (by positivity) hr).mul_left _

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_weightSeq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : WeightSeq (emaW β) := by
  refine ⟨fun j => (vs_emaW_pos hβ0 hβ1 j).le, ?_, ⟨0, (vs_emaW_pos hβ0 hβ1 0).ne'⟩⟩
  have key : emaW β = fun j => (1 - β) * β ^ j := by
    funext j; rfl
  rw [key]
  exact (summable_geometric_of_lt_one hβ0.le hβ1).mul_left _

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_range {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := by
  have hcont : ContinuousOn (rW (emaW β)) (Ici 0) :=
    continuousOn_id.mul (lem_app_de_scalar_ii (vs_weightSeq hβ0 hβ1)).2.2.1
  have hr0 := (lem_app_de_scalar_iii (vs_weightSeq hβ0 hβ1)).2.2.1
  have hT := (lem_app_de_scalar_iii (vs_weightSeq hβ0 hβ1)).2.2.2.2.2.2
  have hinf : {j : ℕ | 0 < emaW β j} = Set.univ := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact vs_emaW_pos hβ0 hβ1 j
  have hTop : (Set.encard {j : ℕ | 0 < emaW β j}).toENNReal = ⊤ := by
    rw [hinf, Set.encard_univ, ENat.card_eq_top_of_infinite]
    rfl
  rw [hTop] at hT
  have hev : ∀ᶠ q in atTop, ENNReal.ofReal m < ENNReal.ofReal (rW (emaW β) q) :=
    hT.eventually (Ioi_mem_nhds ENNReal.ofReal_lt_top)
  obtain ⟨Q0, hQ0⟩ := (hev.and (eventually_ge_atTop (1:ℝ))).exists
  have hlt : ENNReal.ofReal m < ENNReal.ofReal (rW (emaW β) Q0) := hQ0.1
  have hmQ : m < rW (emaW β) Q0 := (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1
  have hmem : m ∈ Icc (rW (emaW β) 0) (rW (emaW β) Q0) :=
    ⟨by rw [hr0]; exact hm.le, hmQ.le⟩
  obtain ⟨q, hq, hqe⟩ := intermediate_value_Icc (by linarith [hQ0.2] : (0:ℝ) ≤ Q0)
    (hcont.mono Icc_subset_Ici_self) hmem
  have hqpos : 0 < q := by
    rcases hq.1.eq_or_lt with h | h
    · rw [← h, hr0] at hqe
      linarith
    · exact h
  exact ⟨q, hqpos, hqe⟩

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_Qm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Qm β m ∧ rW (emaW β) (Qm β m) = m := by
  have hex : ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := vs_range hβ0 hβ1 hm
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_Qm_mono {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    MonotoneOn (Qm β) (Ioi 0) := by
  intro a ha b hb hab
  obtain ⟨hQa, hra⟩ := vs_Qm hβ0 hβ1 ha
  obtain ⟨hQb, hrb⟩ := vs_Qm hβ0 hβ1 hb
  by_contra h
  have h := not_le.1 h
  have := (lem_app_de_scalar_iii (vs_weightSeq hβ0 hβ1)).2.1 (Set.mem_Ici.2 hQb.le)
    (Set.mem_Ici.2 hQa.le) h
  rw [hra, hrb] at this
  linarith [this, hab]

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_Fw_anti {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q q' : ℝ} (hq : 0 ≤ q)
    (hqq : q ≤ q') : Fw (emaW β) q' ≤ Fw (emaW β) q := by
  have hJ := lem_app_de_scalar_i
  have hsum : ∀ x : ℝ, 0 ≤ x → Summable (fun j : ℕ => emaW β j ^ 2 * J (emaW β j ^ 2 * x)) := by
    intro x hx
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (vs_w2_summable hβ0 hβ1)
    · exact mul_nonneg (sq_nonneg _) (hJ.2.2.1 _ (mul_nonneg (sq_nonneg _) hx)).1.le
    · exact mul_le_of_le_one_right (sq_nonneg _) (hJ.2.2.1 _ (mul_nonneg (sq_nonneg _) hx)).2
  unfold Fw
  refine Summable.tsum_le_tsum (fun j => ?_) (hsum q' (hq.trans hqq)) (hsum q hq)
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact hJ.2.1.antitoneOn (Set.mem_Ici.2 (mul_nonneg (sq_nonneg _) hq))
    (Set.mem_Ici.2 (mul_nonneg (sq_nonneg _) (hq.trans hqq)))
    (mul_le_mul_of_nonneg_left hqq (sq_nonneg _))

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_Qm_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) :
    Qm β m ≤ Qm β 1 * m := by
  obtain ⟨hQ, hr⟩ := vs_Qm hβ0 hβ1 hm
  obtain ⟨hQ1, hr1⟩ := vs_Qm hβ0 hβ1 (zero_lt_one : (0:ℝ) < 1)
  have hle : Qm β m ≤ Qm β 1 := vs_Qm_mono hβ0 hβ1 hm (zero_lt_one : (0:ℝ) < 1) hm1
  have hF := vs_Fw_anti hβ0 hβ1 hQ.le hle
  have e1 : Qm β m * Fw (emaW β) (Qm β m) = m := hr
  have e2 : Qm β 1 * Fw (emaW β) (Qm β 1) = 1 := hr1
  have : Qm β m * Fw (emaW β) (Qm β 1) ≤ m := by
    have := mul_le_mul_of_nonneg_left hF hQ.le
    linarith
  have h2 : Qm β m * (Qm β 1 * Fw (emaW β) (Qm β 1)) ≤ Qm β 1 * m := by
    nlinarith
  rw [e2] at h2
  linarith


open Muon.DetEquiv ProbabilityTheory in
private lemma vs_emaW_le_one {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (a : ℕ) : emaW β a ≤ 1 := by
  unfold emaW
  have : β ^ a ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  nlinarith [pow_nonneg hβ0.le a]

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_cont_tsum {S : Set (ℝ × ℝ)} {f : ℕ → ℝ → ℝ × ℝ → ℝ} {c : ℕ → ℝ} {H : ℝ → ℝ}
    (hc : Summable c) (hH : Integrable H (gaussianReal 0 1)) (hH0 : ∀ g, 0 ≤ H g)
    (hmeas : ∀ a q, q ∈ S → AEStronglyMeasurable (fun g => f a g q) (gaussianReal 0 1))
    (hcont : ∀ a g, ContinuousOn (f a g) S)
    (hbd : ∀ a q, q ∈ S → ∀ g, |f a g q| ≤ c a * H g) :
    ContinuousOn (fun q => ∑' a, ∫ g, f a g q ∂(gaussianReal 0 1)) S := by
  refine continuousOn_tsum (u := fun a => c a * ∫ g, H g ∂(gaussianReal 0 1)) (fun a => ?_)
    (hc.mul_right _) (fun a q hq => ?_)
  · exact continuousOn_of_dominated (F := fun q g => f a g q) (bound := fun g => c a * H g)
      (fun q hq => hmeas a q hq)
      (fun q hq => Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs]; exact hbd a q hq g)
      (hH.const_mul _) (Filter.Eventually.of_forall fun g => hcont a g)
  · calc ‖∫ g, f a g q ∂(gaussianReal 0 1)‖ ≤ ∫ g, c a * H g ∂(gaussianReal 0 1) :=
          norm_integral_le_of_norm_le (hH.const_mul _) (Filter.Eventually.of_forall fun g => by
            rw [Real.norm_eq_abs]; exact hbd a q hq g)
      _ = c a * ∫ g, H g ∂(gaussianReal 0 1) := integral_const_mul _ _


open Muon.DetEquiv ProbabilityTheory in
private lemma vs_D_cont_R {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℕ) (R : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => DLagNat β q.1 q.2 ℓ)
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ R ∧ 0 ≤ q.2 ∧ q.2 ≤ R} := by
  unfold DLagNat
  have hρ0 : 0 ≤ β ^ ℓ := pow_nonneg hβ0.le ℓ
  have hρ1 : β ^ ℓ ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hs0 : 0 ≤ β ^ (2 * ℓ) := pow_nonneg hβ0.le _
  refine vs_cont_tsum (c := fun a => R * emaW β a ^ 2) (H := fun g => g ^ 2)
    ((vs_w2_summable hβ0 hβ1).mul_left R) (Muon.Foundations.gaussian_integrable_pow 2)
    (fun g => sq_nonneg g) ?_ ?_ ?_
  · intro a q hq
    refine Continuous.aestronglyMeasurable ?_
    have hq1 : 0 ≤ q.1 := hq.1
    have hq2 : 0 ≤ q.2 := hq.2.2.1
    have hd : ∀ g : ℝ, (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2) ≠ 0 := fun g => by
      have : 0 < (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2) := by positivity
      exact this.ne'
    exact (by fun_prop : Continuous fun g : ℝ => β ^ ℓ * Real.sqrt (q.1 * q.2) *
        emaW β a ^ 2 * g ^ 2).div (by fun_prop) hd
  · intro a g
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (by fun_prop : Continuous fun q : ℝ × ℝ => β ^ ℓ * Real.sqrt (q.1 * q.2) *
        emaW β a ^ 2 * g ^ 2).continuousOn
    · exact (by fun_prop : Continuous fun q : ℝ × ℝ => (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2)).continuousOn
    · intro q hq
      have hq1 : 0 ≤ q.1 := hq.1
      have hq2 : 0 ≤ q.2 := hq.2.2.1
      have : 0 < (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2) := by positivity
      exact this.ne'
  · intro a q hq g
    obtain ⟨hq1, hq1R, hq2, hq2R⟩ := hq
    have hden : 1 ≤ (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2) := by
      have h1 : 0 ≤ q.1 * emaW β a ^ 2 * g ^ 2 := by positivity
      have h2 : 0 ≤ β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2 := by positivity
      nlinarith [mul_nonneg h1 h2]
    have hn0 : 0 ≤ β ^ ℓ * Real.sqrt (q.1 * q.2) * emaW β a ^ 2 * g ^ 2 := by positivity
    rw [abs_of_nonneg (by positivity)]
    refine (div_le_self hn0 hden).trans ?_
    have hsq : Real.sqrt (q.1 * q.2) ≤ R := by
      rw [Real.sqrt_le_iff]
      refine ⟨by linarith, ?_⟩
      nlinarith [mul_le_mul hq1R hq2R hq2 (by linarith : (0:ℝ) ≤ R)]
    have : β ^ ℓ * Real.sqrt (q.1 * q.2) ≤ R := by
      calc _ ≤ 1 * R := mul_le_mul hρ1 hsq (Real.sqrt_nonneg _) zero_le_one
        _ = R := one_mul R
    have h3 : 0 ≤ emaW β a ^ 2 * g ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right this h3]


open Muon.DetEquiv ProbabilityTheory in
private lemma vs_M_cont_R {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℕ) (R : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => MLagNat β q.1 q.2 ℓ)
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ R ∧ 0 ≤ q.2 ∧ q.2 ≤ R} := by
  unfold MLagNat
  have hs0 : 0 ≤ β ^ (2 * ℓ) := pow_nonneg hβ0.le _
  have hs1 : β ^ (2 * ℓ) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  refine vs_cont_tsum (c := fun a => R ^ 2 * emaW β a ^ 2) (H := fun g => g ^ 4)
    ((vs_w2_summable hβ0 hβ1).mul_left (R ^ 2)) (Muon.Foundations.gaussian_integrable_pow 4)
    (fun g => by positivity) ?_ ?_ ?_
  · intro a q hq
    refine Continuous.aestronglyMeasurable ?_
    have hq1 : 0 ≤ q.1 := hq.1
    have hq2 : 0 ≤ q.2 := hq.2.2.1
    have hd : ∀ g : ℝ, (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2) ≠ 0 := fun g => by
      have : 0 < (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2) := by positivity
      exact this.ne'
    exact (by fun_prop : Continuous fun g : ℝ => β ^ (2 * ℓ) * q.1 * q.2 *
        emaW β a ^ 4 * g ^ 4).div (by fun_prop) hd
  · intro a g
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (by fun_prop : Continuous fun q : ℝ × ℝ => β ^ (2 * ℓ) * q.1 * q.2 *
        emaW β a ^ 4 * g ^ 4).continuousOn
    · exact (by fun_prop : Continuous fun q : ℝ × ℝ => (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2)).continuousOn
    · intro q hq
      have hq1 : 0 ≤ q.1 := hq.1
      have hq2 : 0 ≤ q.2 := hq.2.2.1
      have : 0 < (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2) := by positivity
      exact this.ne'
  · intro a q hq g
    obtain ⟨hq1, hq1R, hq2, hq2R⟩ := hq
    have hden : 1 ≤ (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2) := by
      have h1 : 0 ≤ q.1 * emaW β a ^ 2 * g ^ 2 := by positivity
      have h2 : 0 ≤ β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2 := by positivity
      nlinarith [mul_nonneg h1 h2]
    have hn0 : 0 ≤ β ^ (2 * ℓ) * q.1 * q.2 * emaW β a ^ 4 * g ^ 4 := by positivity
    rw [abs_of_nonneg (by positivity)]
    refine (div_le_self hn0 hden).trans ?_
    have hw1 := vs_emaW_le_one hβ0 hβ1 a
    have hw0 := (vs_emaW_pos hβ0 hβ1 a).le
    have hw4 : emaW β a ^ 4 ≤ emaW β a ^ 2 := by
      have : emaW β a ^ 2 ≤ 1 := pow_le_one₀ hw0 hw1
      nlinarith [sq_nonneg (emaW β a)]
    have hqq : q.1 * q.2 ≤ R ^ 2 := by
      nlinarith [mul_le_mul hq1R hq2R hq2 (by linarith : (0:ℝ) ≤ R)]
    have hqq0 : 0 ≤ q.1 * q.2 := mul_nonneg hq1 hq2
    have e : β ^ (2 * ℓ) * q.1 * q.2 * emaW β a ^ 4 * g ^ 4 =
        β ^ (2 * ℓ) * (q.1 * q.2) * (emaW β a ^ 4 * g ^ 4) := by ring
    rw [e]
    have h4 : 0 ≤ emaW β a ^ 4 * g ^ 4 := by positivity
    calc β ^ (2 * ℓ) * (q.1 * q.2) * (emaW β a ^ 4 * g ^ 4)
        ≤ 1 * (R ^ 2) * (emaW β a ^ 2 * g ^ 4) := by
          refine mul_le_mul (mul_le_mul hs1 hqq hqq0 zero_le_one) ?_ h4 (by positivity)
          exact mul_le_mul_of_nonneg_right hw4 (by positivity)
      _ = R ^ 2 * emaW β a ^ 2 * g ^ 4 := by ring

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_cont_of_R {F : ℝ × ℝ → ℝ}
    (h : ∀ R : ℝ, ContinuousOn F {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ R ∧ 0 ≤ q.2 ∧ q.2 ≤ R}) :
    ContinuousOn F {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} := by
  intro x hx
  refine ((h (max x.1 x.2 + 1)) x ⟨hx.1, ?_, hx.2, ?_⟩).mono_of_mem_nhdsWithin ?_
  · linarith [le_max_left x.1 x.2]
  · linarith [le_max_right x.1 x.2]
  · have h1 : {q : ℝ × ℝ | q.1 < max x.1 x.2 + 1 ∧ q.2 < max x.1 x.2 + 1} ∈ 𝓝 x := by
      refine IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_const |>.inter
        (isOpen_lt continuous_snd continuous_const)) ⟨?_, ?_⟩
      · show x.1 < _
        linarith [le_max_left x.1 x.2]
      · show x.2 < _
        linarith [le_max_right x.1 x.2]
    filter_upwards [mem_nhdsWithin_of_mem_nhds h1, self_mem_nhdsWithin] with q hq hq'
    exact ⟨hq'.1, hq.1.le, hq'.2, hq.2.le⟩

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_DLag_cont {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℤ) :
    ContinuousOn (fun q : ℝ × ℝ => DLag β q.1 q.2 ℓ) {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} := by
  by_cases hℓ : 0 ≤ ℓ
  · have : (fun q : ℝ × ℝ => DLag β q.1 q.2 ℓ) = fun q => DLagNat β q.1 q.2 ℓ.toNat := by
      funext q; simp [DLag, hℓ]
    rw [this]
    exact vs_cont_of_R (fun R => vs_D_cont_R hβ0 hβ1 _ R)
  · have : (fun q : ℝ × ℝ => DLag β q.1 q.2 ℓ) = fun q => DLagNat β q.2 q.1 (-ℓ).toNat := by
      funext q; simp [DLag, hℓ]
    rw [this]
    have h2 : ContinuousOn (fun q : ℝ × ℝ => DLagNat β q.1 q.2 (-ℓ).toNat)
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} :=
      vs_cont_of_R (fun R => vs_D_cont_R hβ0 hβ1 _ R)
    exact h2.comp continuous_swap.continuousOn (fun q hq => ⟨hq.2, hq.1⟩)

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_MLag_cont {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℤ) :
    ContinuousOn (fun q : ℝ × ℝ => MLag β q.1 q.2 ℓ) {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} := by
  by_cases hℓ : 0 ≤ ℓ
  · have : (fun q : ℝ × ℝ => MLag β q.1 q.2 ℓ) = fun q => MLagNat β q.1 q.2 ℓ.toNat := by
      funext q; simp [MLag, hℓ]
    rw [this]
    exact vs_cont_of_R (fun R => vs_M_cont_R hβ0 hβ1 _ R)
  · have : (fun q : ℝ × ℝ => MLag β q.1 q.2 ℓ) = fun q => MLagNat β q.2 q.1 (-ℓ).toNat := by
      funext q; simp [MLag, hℓ]
    rw [this]
    have h2 : ContinuousOn (fun q : ℝ × ℝ => MLagNat β q.1 q.2 (-ℓ).toNat)
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} :=
      vs_cont_of_R (fun R => vs_M_cont_R hβ0 hβ1 _ R)
    exact h2.comp continuous_swap.continuousOn (fun q hq => ⟨hq.2, hq.1⟩)


open Muon.DetEquiv ProbabilityTheory in
private lemma vs_int_summ {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {f : ℕ → ℝ → ℝ} {c : ℝ}
    (hcont : ∀ a, Continuous (f a)) (h0 : ∀ a g, 0 ≤ f a g)
    (hle : ∀ a g, f a g ≤ c * (emaW β a ^ 2 * g ^ 2)) :
    (∀ a, Integrable (f a) (gaussianReal 0 1)) ∧
      Summable (fun a => ∫ g, f a g ∂(gaussianReal 0 1)) := by
  have hi2 := Muon.Foundations.gaussian_integrable_pow 2
  have hb : ∀ a, Integrable (fun g : ℝ => c * (emaW β a ^ 2 * g ^ 2)) (gaussianReal 0 1) :=
    fun a => (hi2.const_mul (emaW β a ^ 2)).const_mul c
  have hint : ∀ a, Integrable (f a) (gaussianReal 0 1) := fun a =>
    Integrable.mono' (hb a) (hcont a).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 a g)]
        exact hle a g)
  refine ⟨hint, ?_⟩
  refine Summable.of_nonneg_of_le (fun a => integral_nonneg (h0 a)) (fun a => ?_)
    ((vs_w2_summable hβ0 hβ1).mul_left c)
  calc ∫ g, f a g ∂(gaussianReal 0 1) ≤ ∫ g, c * (emaW β a ^ 2 * g ^ 2) ∂(gaussianReal 0 1) :=
        integral_mono (hint a) (hb a) (hle a)
    _ = c * emaW β a ^ 2 := by
        rw [integral_const_mul, integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one,
          mul_comm]

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_D_terms {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ} (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (ℓ : ℕ) :
    (∀ a, Integrable (fun g : ℝ => β ^ ℓ * Real.sqrt (q1 * q2) * emaW β a ^ 2 * g ^ 2 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2)))
      (gaussianReal 0 1)) ∧
    Summable (fun a : ℕ => ∫ g : ℝ, β ^ ℓ * Real.sqrt (q1 * q2) * emaW β a ^ 2 * g ^ 2 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2))
      ∂(gaussianReal 0 1)) := by
  have hρ0 : 0 ≤ β ^ ℓ := pow_nonneg hβ0.le ℓ
  have hρ1 : β ^ ℓ ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hs0 : 0 ≤ β ^ (2 * ℓ) := pow_nonneg hβ0.le _
  refine vs_int_summ hβ0 hβ1 (c := Real.sqrt (q1 * q2)) ?_ ?_ ?_
  · intro a
    have hd : ∀ g : ℝ, (1 + q1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2) ≠ 0 := fun g => by
      have : 0 < (1 + q1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2) := by positivity
      exact this.ne'
    exact (by fun_prop : Continuous fun g : ℝ => β ^ ℓ * Real.sqrt (q1 * q2) *
        emaW β a ^ 2 * g ^ 2).div (by fun_prop) hd
  · intro a g
    positivity
  · intro a g
    have hden : 1 ≤ (1 + q1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2) := by
      have h1 : 0 ≤ q1 * emaW β a ^ 2 * g ^ 2 := by positivity
      have h2 : 0 ≤ β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2 := by positivity
      nlinarith [mul_nonneg h1 h2]
    have hn0 : 0 ≤ β ^ ℓ * Real.sqrt (q1 * q2) * emaW β a ^ 2 * g ^ 2 := by positivity
    refine (div_le_self hn0 hden).trans ?_
    have h3 : 0 ≤ emaW β a ^ 2 * g ^ 2 := by positivity
    have : β ^ ℓ * Real.sqrt (q1 * q2) ≤ Real.sqrt (q1 * q2) :=
      mul_le_of_le_one_left (Real.sqrt_nonneg _) hρ1
    nlinarith [mul_le_mul_of_nonneg_right this h3]

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_DNat_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ} (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (ℓ : ℕ) : 0 ≤ DLagNat β q1 q2 ℓ := by
  unfold DLagNat
  refine tsum_nonneg fun a => integral_nonneg fun g => ?_
  have := hq1; have := hq2; have : 0 ≤ β ^ ℓ := pow_nonneg hβ0.le ℓ
  have : 0 ≤ β ^ (2 * ℓ) := pow_nonneg hβ0.le _
  positivity

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_DLag_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ} (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (ℓ : ℤ) : 0 ≤ DLag β q1 q2 ℓ := by
  unfold DLag
  split_ifs
  · exact vs_DNat_nonneg hβ0 hβ1 hq1 hq2 _
  · exact vs_DNat_nonneg hβ0 hβ1 hq2 hq1 _

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_DLag_zero_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ} (hq1 : 0 < q1)
    (hq2 : 0 < q2) : 0 < DLag β q1 q2 0 := by
  have hD : DLag β q1 q2 0 = DLagNat β q1 q2 0 := by simp [DLag]
  rw [hD]
  obtain ⟨hint, hsum⟩ := vs_D_terms hβ0 hβ1 hq1.le hq2.le 0
  unfold DLagNat
  have hnn : ∀ a : ℕ, 0 ≤ ∫ g : ℝ, β ^ 0 * Real.sqrt (q1 * q2) * emaW β a ^ 2 * g ^ 2 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + β ^ (2 * 0) * q2 * emaW β a ^ 2 * g ^ 2))
      ∂(gaussianReal 0 1) := fun a => integral_nonneg fun g => by
    have := hq1; have := hq2; positivity
  refine lt_of_lt_of_le ?_ (hsum.le_tsum 0 (fun j _ => hnn j))
  have hw := vs_emaW_pos hβ0 hβ1 0
  have hsq : 0 < Real.sqrt (q1 * q2) := Real.sqrt_pos.2 (mul_pos hq1 hq2)
  rw [integral_pos_iff_support_of_nonneg (fun g => by have := hq1; have := hq2; positivity)
    (hint 0)]
  have hae : ∀ᵐ g ∂(gaussianReal 0 1), g ≠ 0 :=
    (gaussianReal_absolutelyContinuous 0 one_ne_zero).ae_le
      (Measure.ae_ne volume (0:ℝ))
  have hsub : ∀ᵐ g ∂(gaussianReal 0 1), g ∈ Function.support (fun g : ℝ =>
      β ^ 0 * Real.sqrt (q1 * q2) * emaW β 0 ^ 2 * g ^ 2 /
      ((1 + q1 * emaW β 0 ^ 2 * g ^ 2) * (1 + β ^ (2 * 0) * q2 * emaW β 0 ^ 2 * g ^ 2))) := by
    filter_upwards [hae] with g hg
    have hg2 : 0 < g ^ 2 := by positivity
    have : 0 < β ^ 0 * Real.sqrt (q1 * q2) * emaW β 0 ^ 2 * g ^ 2 /
      ((1 + q1 * emaW β 0 ^ 2 * g ^ 2) * (1 + β ^ (2 * 0) * q2 * emaW β 0 ^ 2 * g ^ 2)) := by
      have := hq1; have := hq2; positivity
    exact this.ne'
  rw [pos_iff_ne_zero]
  intro h0
  have h1 : (gaussianReal 0 1) (Function.support (fun g : ℝ =>
      β ^ 0 * Real.sqrt (q1 * q2) * emaW β 0 ^ 2 * g ^ 2 /
      ((1 + q1 * emaW β 0 ^ 2 * g ^ 2) * (1 + β ^ (2 * 0) * q2 * emaW β 0 ^ 2 * g ^ 2))))ᶜ = 0 :=
    mem_ae_iff.1 hsub
  have := measure_union_null h0 h1
  rw [union_compl_self] at this
  simp at this


private lemma vs_cs {D SA SB : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ SA) (hB : 0 ≤ SB)
    (h : ∀ t : ℝ, 0 < t → 2 * D ≤ t * SA + SB / t) : D ^ 2 ≤ SA * SB := by
  rcases hD.eq_or_lt with h0 | hpos
  · rw [← h0]; nlinarith [mul_nonneg hA hB]
  · rcases hA.eq_or_lt with hA0 | hApos
    · exfalso
      have := h ((SB + 1) / D) (by positivity)
      rw [← hA0, mul_zero, zero_add, div_div_eq_mul_div] at this
      have h2 : SB * D / (SB + 1) < D := by
        rw [div_lt_iff₀ (by linarith)]; nlinarith
      linarith
    · have := h (D / SA) (by positivity)
      have e : D / SA * SA + SB / (D / SA) = D + SB * SA / D := by
        field_simp
      rw [e] at this
      have : D ≤ SB * SA / D := by linarith
      rw [le_div_iff₀ hpos] at this
      nlinarith


private lemma vs_w_sq {u : ℝ} (hu : 0 < u) : min (Real.sqrt u) 1 ^ 2 = min u 1 := by
  by_cases h : u ≤ 1
  · have hs : Real.sqrt u ≤ 1 := by rw [Real.sqrt_le_one]; exact h
    rw [min_eq_left hs, min_eq_left h, Real.sq_sqrt hu.le]
  · have h1 : 1 ≤ Real.sqrt u := by rw [Real.one_le_sqrt]; exact (not_le.1 h).le
    rw [min_eq_right h1, min_eq_right (not_le.1 h).le]; norm_num

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_D_bd {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ℝ, 0 < u → 0 < v → ∀ s : Finset ℤ,
      ∑ ℓ ∈ s, DLag β (Qm β u) (Qm β v) ℓ ≤ C * min (Real.sqrt u) 1 * min (Real.sqrt v) 1 := by
  obtain ⟨C0, hC0⟩ := (lem_app_pl_age_i hβ0 hβ1).1
  have hage := (lem_app_pl_age_i hβ0 hβ1).2
  have hC0nn : 0 ≤ C0 := (abs_nonneg _).trans (hC0 1 0 one_pos)
  obtain ⟨hQ1, -⟩ := vs_Qm hβ0 hβ1 (zero_lt_one : (0:ℝ) < 1)
  set C1 := max (Qm β 1) (C0 ^ 2) with hC1
  have hC1nn : 0 ≤ C1 := (sq_nonneg C0).trans (le_max_right _ _)
  -- second moment bound
  have hSA : ∀ u : ℝ, 0 < u → ∫ g : ℝ, Zg β g (Qm β u) ^ 2 ∂(gaussianReal 0 1) ≤ C1 * min u 1 := by
    intro u hu
    obtain ⟨hQ, -⟩ := vs_Qm hβ0 hβ1 hu
    obtain ⟨hint, hle⟩ := hage (Qm β u) hQ
    by_cases h1 : u ≤ 1
    · rw [min_eq_left h1]
      have := vs_Qm_le hβ0 hβ1 hu h1
      calc _ ≤ Qm β u := hle
        _ ≤ Qm β 1 * u := this
        _ ≤ C1 * u := mul_le_mul_of_nonneg_right (le_max_left _ _) hu.le
    · rw [min_eq_right (not_le.1 h1).le, mul_one]
      calc _ ≤ ∫ g : ℝ, C0 ^ 2 ∂(gaussianReal 0 1) :=
            integral_mono hint (integrable_const _) (fun g => by
              have := hC0 (Qm β u) g hQ
              have h2 : |Zg β g (Qm β u)| ^ 2 ≤ C0 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
              rwa [sq_abs] at h2)
        _ = C0 ^ 2 := by simp
        _ ≤ C1 := le_max_right _ _
  refine ⟨C1, hC1nn, fun u v hu hv s => ?_⟩
  obtain ⟨hQu, -⟩ := vs_Qm hβ0 hβ1 hu
  obtain ⟨hQv, -⟩ := vs_Qm hβ0 hβ1 hv
  obtain ⟨hint, hsum⟩ := lem_app_pl_age_iii hβ0 hβ1 u v hu hv
  obtain ⟨hiu, -⟩ := hage (Qm β u) hQu
  obtain ⟨hiv, -⟩ := hage (Qm β v) hQv
  set Dt := ∫ g : ℝ, Zg β g (Qm β u) * Zg β g (Qm β v) ∂(gaussianReal 0 1) with hDt
  have hDnn : ∀ ℓ' : ℤ, 0 ≤ DLag β (Qm β u) (Qm β v) ℓ' := fun ℓ' =>
    vs_DLag_nonneg hβ0 hβ1 hQu.le hQv.le ℓ'
  have hDt0 : 0 ≤ Dt := hsum.nonneg hDnn
  have hle : ∑ ℓ ∈ s, DLag β (Qm β u) (Qm β v) ℓ ≤ Dt :=
    sum_le_hasSum s (fun j _ => hDnn j) hsum
  have hSAn : 0 ≤ ∫ g : ℝ, Zg β g (Qm β u) ^ 2 ∂(gaussianReal 0 1) :=
    integral_nonneg fun g => sq_nonneg _
  have hSBn : 0 ≤ ∫ g : ℝ, Zg β g (Qm β v) ^ 2 ∂(gaussianReal 0 1) :=
    integral_nonneg fun g => sq_nonneg _
  have hcs : Dt ^ 2 ≤ (∫ g : ℝ, Zg β g (Qm β u) ^ 2 ∂(gaussianReal 0 1)) *
      (∫ g : ℝ, Zg β g (Qm β v) ^ 2 ∂(gaussianReal 0 1)) := by
    refine vs_cs hDt0 hSAn hSBn (fun t ht => ?_)
    have h1 : 2 * Dt = ∫ g : ℝ, 2 * (Zg β g (Qm β u) * Zg β g (Qm β v)) ∂(gaussianReal 0 1) := by
      rw [integral_const_mul]
    have h2 : t * (∫ g : ℝ, Zg β g (Qm β u) ^ 2 ∂(gaussianReal 0 1)) +
        (∫ g : ℝ, Zg β g (Qm β v) ^ 2 ∂(gaussianReal 0 1)) / t =
        ∫ g : ℝ, (t * Zg β g (Qm β u) ^ 2 + Zg β g (Qm β v) ^ 2 / t) ∂(gaussianReal 0 1) := by
      rw [integral_add (hiu.const_mul t) (hiv.div_const t), integral_const_mul, integral_div]
    rw [h1, h2]
    refine integral_mono (hint.const_mul 2) ((hiu.const_mul t).add (hiv.div_const t)) (fun g => ?_)
    change 2 * (Zg β g (Qm β u) * Zg β g (Qm β v)) ≤ t * Zg β g (Qm β u) ^ 2 + Zg β g (Qm β v) ^ 2 / t
    have key : 0 ≤ (t * Zg β g (Qm β u) - Zg β g (Qm β v)) ^ 2 / t := by positivity
    have e : (t * Zg β g (Qm β u) - Zg β g (Qm β v)) ^ 2 / t =
        t * Zg β g (Qm β u) ^ 2 + Zg β g (Qm β v) ^ 2 / t -
          2 * (Zg β g (Qm β u) * Zg β g (Qm β v)) := by
      field_simp; ring
    linarith
  have hbd : Dt ^ 2 ≤ (C1 * min (Real.sqrt u) 1 * min (Real.sqrt v) 1) ^ 2 := by
    calc Dt ^ 2 ≤ _ := hcs
      _ ≤ (C1 * min u 1) * (C1 * min v 1) :=
          mul_le_mul (hSA u hu) (hSA v hv) hSBn (by have := min_le_right u 1; positivity)
      _ = (C1 * min (Real.sqrt u) 1 * min (Real.sqrt v) 1) ^ 2 := by
          rw [mul_pow, mul_pow, vs_w_sq hu, vs_w_sq hv]; ring
  have hRnn : 0 ≤ C1 * min (Real.sqrt u) 1 * min (Real.sqrt v) 1 :=
    mul_nonneg (mul_nonneg hC1nn (le_min (Real.sqrt_nonneg _) zero_le_one))
      (le_min (Real.sqrt_nonneg _) zero_le_one)
  exact hle.trans ((pow_le_pow_iff_left₀ hDt0 hRnn two_ne_zero).1 hbd)


open Muon.DetEquiv ProbabilityTheory in
private lemma vs_ae_pos {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] :
    ∀ᵐ p ∂((μ.restrict (Ioi 0)).prod (ν.restrict (Ioi 0))), 0 < p.1 ∧ 0 < p.2 := by
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  exact hp

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_F_meas {α β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (X : ℝ) (ℓ : ℤ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
          Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2))
        ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  have hae : ∀ᵐ p ∂μ, 0 < p.1 ∧ 0 < p.2 := vs_ae_pos
  have hQm : AEMeasurable (Qm β) (volume.restrict (Ioi (0:ℝ))) :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Ioi (vs_Qm_mono hβ0 hβ1)
  have hQ1 : AEMeasurable (fun p : ℝ × ℝ => Qm β p.1) μ := hQm.comp_fst
  have hQ2 : AEMeasurable (fun p : ℝ × ℝ => Qm β p.2) μ := hQm.comp_snd
  have hpair : AEMeasurable (fun p : ℝ × ℝ => (Qm β p.1, Qm β p.2)) μ := hQ1.prodMk hQ2
  have hSm : MeasurableSet {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)
  have hcomp : ∀ G : ℝ × ℝ → ℝ, ContinuousOn G {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} →
      AEMeasurable (fun p : ℝ × ℝ => G (Qm β p.1, Qm β p.2)) μ := by
    intro G hG
    classical
    have hg : Measurable ({q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}.piecewise G 0) :=
      ContinuousOn.measurable_piecewise hG continuousOn_const hSm
    refine (hg.comp_aemeasurable hpair).congr ?_
    filter_upwards [hae] with p hp
    have h1 := (vs_Qm hβ0 hβ1 hp.1).1
    have h2 := (vs_Qm hβ0 hβ1 hp.2).1
    simp only [Function.comp]
    rw [Set.piecewise_eq_of_mem _ _ _ (show (Qm β p.1, Qm β p.2) ∈
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} from ⟨h1.le, h2.le⟩)]
  have hD := hcomp _ (vs_DLag_cont hβ0 hβ1 ℓ)
  have hM := hcomp _ (vs_MLag_cont hβ0 hβ1 ℓ)
  have hE : AEMeasurable (Efun β) (volume.restrict (Ioi (0:ℝ))) := by
    unfold Efun
    exact hQm.mul ((measurable_deriv (rW (emaW β))).comp_aemeasurable hQm)
  have hTh : AEMeasurable (profTheta α β) (volume.restrict (Ioi (0:ℝ))) := by
    unfold profTheta
    exact (aemeasurable_const.div hE).add (measurable_const.div measurable_id).aemeasurable
  have hT : Measurable (fun p : ℝ × ℝ => profT α p.1 p.2) := by
    unfold profT
    refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) ?_ ?_
    · exact (measurable_const.mul measurable_fst).div_const _
    · exact (((measurable_snd.pow_const α).mul measurable_fst).sub
        ((measurable_fst.pow_const α).mul measurable_snd)).div
        ((measurable_snd.pow_const α).sub (measurable_fst.pow_const α))
  have hZ : ∀ x : ℝ, Measurable (fun u : ℝ => profZeta α X u) := fun x => by
    unfold profZeta
    exact (measurable_id.pow_const α).div (measurable_const.add (measurable_id.pow_const α))
  have hZ1 : Measurable (fun p : ℝ × ℝ => profZeta α X p.1) := (hZ X).comp measurable_fst
  have hZ2 : Measurable (fun p : ℝ × ℝ => profZeta α X p.2) := (hZ X).comp measurable_snd
  have hDelta : AEMeasurable (fun p : ℝ × ℝ => profDelta α β ℓ p.1 p.2) μ := by
    unfold profDelta
    refine aemeasurable_const.sub ?_
    exact (hT.aemeasurable.mul hM).div (measurable_fst.mul measurable_snd).aemeasurable
  refine AEMeasurable.aestronglyMeasurable ?_
  refine AEMeasurable.mul (AEMeasurable.div ?_ ?_) (AEMeasurable.div ?_ hDelta)
  · exact Real.continuous_sqrt.measurable.comp_aemeasurable
      (((hZ1.mul (measurable_const.sub hZ1)).mul (hZ2.mul (measurable_const.sub hZ2))).aemeasurable)
  · exact Real.continuous_sqrt.measurable.comp_aemeasurable (measurable_fst.mul measurable_snd).aemeasurable
  · exact (hD.mul hTh.comp_fst).mul hTh.comp_snd


private lemma vs_T_aux {α : ℝ} (hα1 : 1 < α) {u v : ℝ} (hv : 0 < v) (hvu : v < u) :
    (v ^ α * u - u ^ α * v) / (v ^ α - u ^ α) ≤ (1 - 1 / α) * u := by
  have hu : 0 < u := hv.trans hvu
  have hα0 : 0 < α := by linarith
  have hden : v ^ α - u ^ α < 0 := by
    have := Real.rpow_lt_rpow hv.le hvu hα0
    linarith
  rw [div_le_iff_of_neg hden]
  set r := v / u with hr
  have hr0 : 0 < r := div_pos hv hu
  have hr1 : r < 1 := (div_lt_one hu).2 hvu
  have hvr : v = u * r := by rw [hr]; field_simp
  have hvα : v ^ α = u ^ α * r ^ α := by
    rw [hvr, Real.mul_rpow hu.le hr0.le]
  have hB : 1 + α * (r - 1) ≤ r ^ α := by
    have := one_add_mul_self_le_rpow_one_add (s := r - 1) (by linarith) hα1.le
    simpa using this
  have hP : 0 < u ^ α := Real.rpow_pos_of_pos hu α
  rw [hvα]
  have hvr' : u ^ α * r ^ α * u - u ^ α * (u * r) = u ^ α * u * (r ^ α - r) := by ring
  rw [hvr] at *
  have key : (1 - 1 / α) * (u ^ α * r ^ α - u ^ α) * u ≤ u ^ α * u * (r ^ α - r) := by
    have h1 : (1 - 1 / α) = (α - 1) / α := by field_simp
    rw [h1]
    have : (α - 1) * (r ^ α - 1) ≤ α * (r ^ α - r) := by nlinarith
    have h2 : (α - 1) / α * (r ^ α - 1) ≤ (r ^ α - r) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hα0]; linarith
    have := mul_le_mul_of_nonneg_left h2 (mul_pos hP hu).le
    nlinarith
  nlinarith [key]

private lemma vs_T_le {α : ℝ} (hα1 : 1 < α) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    profT α u v ≤ (1 - 1 / α) * max u v := by
  have hα0 : 0 < α := by linarith
  unfold profT
  split_ifs with h
  · subst h
    rw [max_self]
    have : (1 - 1 / α) = (α - 1) / α := by field_simp
    rw [this]; ring_nf; exact le_refl _
  · rcases lt_or_gt_of_ne h with h1 | h1
    · -- u < v
      have := vs_T_aux hα1 hu h1
      have e : (v ^ α * u - u ^ α * v) / (v ^ α - u ^ α)
          = (u ^ α * v - v ^ α * u) / (u ^ α - v ^ α) := by
        rw [← neg_div_neg_eq]; ring_nf
      rw [e, max_eq_right h1.le]
      exact this
    · have := vs_T_aux hα1 hv h1
      rw [max_eq_left h1.le]
      exact this


private lemma vs_M_bd {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (ℓ : ℤ) : 0 ≤ MLag β (Qm β u) (Qm β v) ℓ ∧ MLag β (Qm β u) (Qm β v) ℓ ≤ min u v := by
  have hN : (0:ℕ) < ⌈max u v⌉₊ + 1 := Nat.succ_pos _
  have hlt : max u v < (⌈max u v⌉₊ + 1 : ℕ) := by
    have := Nat.le_ceil (max u v)
    push_cast
    linarith
  have hg : gammaOf (⌈max u v⌉₊ + 1) 1 = ((⌈max u v⌉₊ + 1 : ℕ) : ℝ) := by
    unfold gammaOf; simp
  have := lem_app_pl_determinant_i (α := 1) one_pos hβ0 hβ1 (⌈max u v⌉₊ + 1) 1 1 hN one_pos
    one_pos ℓ u v
    (by rw [hg]; exact ⟨hu, lt_of_le_of_lt (le_max_left _ _) hlt⟩)
    (by rw [hg]; exact ⟨hv, lt_of_le_of_lt (le_max_right _ _) hlt⟩)
  exact ⟨this.1, this.2.1⟩

private lemma vs_Delta_ge {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (ℓ : ℤ) : 1 / α ≤ profDelta α β ℓ u v := by
  have hα0 : 0 < α := by linarith
  obtain ⟨hM0, hM1⟩ := vs_M_bd hβ0 hβ1 hu hv ℓ
  have hT := vs_T_le hα1 hu hv
  unfold profDelta
  set M := MLag β (Qm β u) (Qm β v) ℓ
  set T := profT α u v
  have huv : 0 < u * v := mul_pos hu hv
  have hc : 0 ≤ 1 - 1 / α := by
    have : 1 / α ≤ 1 := by rw [div_le_one hα0]; linarith
    linarith
  have key : T * M ≤ (1 - 1 / α) * (u * v) := by
    rcases le_total T 0 with h | h
    · have : T * M ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hM0
      have : 0 ≤ (1 - 1 / α) * (u * v) := by positivity
      linarith
    · have h1 : T * M ≤ T * min u v := mul_le_mul_of_nonneg_left hM1 h
      have h2 : T * min u v ≤ ((1 - 1 / α) * max u v) * min u v :=
        mul_le_mul_of_nonneg_right hT (le_min hu.le hv.le)
      have h3 : max u v * min u v = u * v := by
        rcases le_total u v with h | h
        · rw [max_eq_right h, min_eq_left h]; ring
        · rw [max_eq_left h, min_eq_right h]
      nlinarith
  have : T * M / (u * v) ≤ 1 - 1 / α := by
    rw [div_le_iff₀ huv]; exact key
  linarith


private lemma vs_sq_half {x α : ℝ} (hx : 0 ≤ x) : (x ^ (α / 2)) ^ 2 = x ^ α := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1; push_cast; ring

private lemma vs_zeta_bd {α X u : ℝ} (hα0 : 0 < α) (hX : 0 < X) (hu : 0 < u) :
    0 < profZeta α X u ∧ profZeta α X u < 1 := by
  unfold profZeta
  have h1 : 0 < X ^ α := Real.rpow_pos_of_pos hX α
  have h2 : 0 < u ^ α := Real.rpow_pos_of_pos hu α
  exact ⟨div_pos h2 (by linarith), by rw [div_lt_one (by linarith)]; linarith⟩

/-- first bound: `√(ζ(1-ζ)) ≤ u^{α/2}/a^{α/2}` when `a ≤ X`. -/
private lemma vs_S_small {α a X u : ℝ} (hα0 : 0 < α) (ha : 0 < a) (haX : a ≤ X) (hu : 0 < u) :
    Real.sqrt (profZeta α X u * (1 - profZeta α X u)) ≤ u ^ (α / 2) / a ^ (α / 2) := by
  have hX : 0 < X := ha.trans_le haX
  obtain ⟨hz0, hz1⟩ := vs_zeta_bd hα0 hX hu
  have h1 : 0 < X ^ α := Real.rpow_pos_of_pos hX α
  have h2 : 0 < u ^ α := Real.rpow_pos_of_pos hu α
  have h3 : 0 < a ^ α := Real.rpow_pos_of_pos ha α
  have h4 : a ^ α ≤ X ^ α := Real.rpow_le_rpow ha.le haX hα0.le
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [div_pow, vs_sq_half hu.le, vs_sq_half ha.le]
  have hz : profZeta α X u ≤ u ^ α / a ^ α := by
    unfold profZeta
    calc u ^ α / (X ^ α + u ^ α) ≤ u ^ α / X ^ α :=
          div_le_div_of_nonneg_left h2.le h1 (by linarith)
      _ ≤ u ^ α / a ^ α := div_le_div_of_nonneg_left h2.le h3 h4
  nlinarith

/-- second bound: `√(ζ(1-ζ)) ≤ b^{α/2}/u^{α/2}` when `X ≤ b`. -/
private lemma vs_S_large {α b X u : ℝ} (hα0 : 0 < α) (hX : 0 < X) (hXb : X ≤ b) (hu : 0 < u) :
    Real.sqrt (profZeta α X u * (1 - profZeta α X u)) ≤ b ^ (α / 2) / u ^ (α / 2) := by
  obtain ⟨hz0, hz1⟩ := vs_zeta_bd hα0 hX hu
  have hb : 0 < b := hX.trans_le hXb
  have h1 : 0 < X ^ α := Real.rpow_pos_of_pos hX α
  have h2 : 0 < u ^ α := Real.rpow_pos_of_pos hu α
  have h4 : X ^ α ≤ b ^ α := Real.rpow_le_rpow hX.le hXb hα0.le
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [div_pow, vs_sq_half hb.le, vs_sq_half hu.le]
  have hz : 1 - profZeta α X u ≤ b ^ α / u ^ α := by
    unfold profZeta
    have e : 1 - u ^ α / (X ^ α + u ^ α) = X ^ α / (X ^ α + u ^ α) := by
      field_simp; ring
    rw [e]
    calc X ^ α / (X ^ α + u ^ α) ≤ X ^ α / u ^ α :=
          div_le_div_of_nonneg_left h1.le h2 (by linarith)
      _ ≤ b ^ α / u ^ α := div_le_div_of_nonneg_right h4 h2.le
  nlinarith

private lemma vs_E_lb {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℝ, 0 < m → c * min m 1 ≤ Efun β m := by
  obtain ⟨c, C, hc, -, h⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  exact ⟨c, hc, fun m hm => (h m hm).1⟩

private lemma vs_theta_bd {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ, 0 < u →
      0 < profTheta α β u ∧ profTheta α β u ≤ K / min u 1 := by
  obtain ⟨c, hc, h⟩ := vs_E_lb hβ0 hβ1
  refine ⟨1 / c + (α - 1), by have : 0 < 1 / c := by positivity
                              linarith, fun u hu => ?_⟩
  have hm : 0 < min u 1 := lt_min hu one_pos
  have hE : c * min u 1 ≤ Efun β u := h u hu
  have hE0 : 0 < Efun β u := lt_of_lt_of_le (mul_pos hc hm) hE
  unfold profTheta
  refine ⟨by have : 0 < (α - 1) / u := div_pos (by linarith) hu
             have : 0 < 1 / Efun β u := by positivity
             linarith, ?_⟩
  have e1 : 1 / Efun β u ≤ (1 / c) / min u 1 := by
    rw [div_div, div_le_div_iff₀ hE0 (mul_pos hc hm)]; nlinarith
  have e2 : (α - 1) / u ≤ (α - 1) / min u 1 :=
    div_le_div_of_nonneg_left (by linarith) hm (min_le_left _ _)
  calc 1 / Efun β u + (α - 1) / u ≤ (1 / c) / min u 1 + (α - 1) / min u 1 := add_le_add e1 e2
    _ = (1 / c + (α - 1)) / min u 1 := by ring


private lemma vs_k_int {α K A B : ℝ} (hα1 : 1 < α) :
    IntegrableOn (fun u : ℝ => if u ≤ 1 then K * A * u ^ (α / 2 - 1)
      else K * B * u ^ (-((α + 1) / 2))) (Ioi 0) := by
  have h1 : IntegrableOn (fun u : ℝ => K * A * u ^ (α / 2 - 1)) (Ioc 0 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (r := α / 2 - 1) (by linarith)).const_mul (K * A)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
  have h2 : IntegrableOn (fun u : ℝ => K * B * u ^ (-((α + 1) / 2))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul (K * B)
  have e : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [e]
  refine IntegrableOn.union ?_ ?_
  · refine h1.congr_fun (fun u hu => ?_) measurableSet_Ioc
    simp [hu.2]
  · refine h2.congr_fun (fun u hu => ?_) measurableSet_Ioi
    have : ¬ u ≤ 1 := not_le.2 hu
    simp [this]

private lemma vs_sigma_le {α β a b X K : ℝ} (hα1 : 1 < α) (ha : 0 < a) (haX : a ≤ X) (hXb : X ≤ b)
    (hK : ∀ u : ℝ, 0 < u → 0 < profTheta α β u ∧ profTheta α β u ≤ K / min u 1)
    {u : ℝ} (hu : 0 < u) :
    0 ≤ Real.sqrt (profZeta α X u * (1 - profZeta α X u)) / Real.sqrt u * profTheta α β u *
        min (Real.sqrt u) 1 ∧
    Real.sqrt (profZeta α X u * (1 - profZeta α X u)) / Real.sqrt u * profTheta α β u *
        min (Real.sqrt u) 1 ≤
      (if u ≤ 1 then K * (1 / a ^ (α / 2)) * u ^ (α / 2 - 1)
        else K * b ^ (α / 2) * u ^ (-((α + 1) / 2))) := by
  have hα0 : 0 < α := by linarith
  have hX : 0 < X := ha.trans_le haX
  obtain ⟨hθ0, hθ⟩ := hK u hu
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hS0 := Real.sqrt_nonneg (profZeta α X u * (1 - profZeta α X u))
  refine ⟨by positivity, ?_⟩
  by_cases hu1 : u ≤ 1
  · have hs1 : Real.sqrt u ≤ 1 := by
      rw [Real.sqrt_le_one]; exact hu1
    rw [min_eq_left hs1]
    have hmin : min u 1 = u := min_eq_left hu1
    rw [hmin] at hθ
    rw [if_pos hu1]
    have hS := vs_S_small (α := α) (X := X) hα0 ha haX hu
    have e : Real.sqrt (profZeta α X u * (1 - profZeta α X u)) / Real.sqrt u * profTheta α β u *
        Real.sqrt u = Real.sqrt (profZeta α X u * (1 - profZeta α X u)) * profTheta α β u := by
      field_simp
    rw [e]
    have hK0 : 0 ≤ K := by
      have := hθ0.le.trans hθ
      have h' : 0 ≤ K / u := this
      exact (div_nonneg_iff.1 h').elim (fun h => h.1) (fun h => by linarith [h.2, hu])
    calc Real.sqrt (profZeta α X u * (1 - profZeta α X u)) * profTheta α β u
        ≤ (u ^ (α / 2) / a ^ (α / 2)) * (K / u) :=
          mul_le_mul hS hθ hθ0.le (by positivity)
      _ = K * (1 / a ^ (α / 2)) * u ^ (α / 2 - 1) := by
          rw [Real.rpow_sub_one hu.ne']
          field_simp
  · have hu1' : 1 < u := not_le.1 hu1
    have hs1 : 1 ≤ Real.sqrt u := by
      rw [Real.one_le_sqrt]; exact hu1'.le
    rw [min_eq_right hs1, mul_one]
    have hmin : min u 1 = 1 := min_eq_right hu1'.le
    rw [hmin, div_one] at hθ
    rw [if_neg hu1]
    have hS := vs_S_large (α := α) (b := b) hα0 hX hXb hu
    have hK0 : 0 ≤ K := hθ0.le.trans hθ
    have hb : 0 < b := hX.trans_le hXb
    have hup : 0 < u ^ (α / 2) := Real.rpow_pos_of_pos hu _
    have e2 : u ^ (-((α + 1) / 2)) = (u ^ (α / 2) * Real.sqrt u)⁻¹ := by
      rw [Real.rpow_neg hu.le, Real.sqrt_eq_rpow, ← Real.rpow_add hu]
      congr 2; ring
    calc Real.sqrt (profZeta α X u * (1 - profZeta α X u)) / Real.sqrt u * profTheta α β u
        ≤ (b ^ (α / 2) / u ^ (α / 2)) / Real.sqrt u * K :=
          mul_le_mul (div_le_div_of_nonneg_right hS hsu.le) hθ hθ0.le (by positivity)
      _ = K * b ^ (α / 2) * u ^ (-((α + 1) / 2)) := by
          rw [e2]; field_simp



open Muon.DetEquiv ProbabilityTheory in
private lemma vs_pointwise {α β a b X K : ℝ} (kf : ℝ → ℝ)
    (hkf : ∀ u, kf u = if u ≤ 1 then K * (1 / a ^ (α / 2)) * u ^ (α / 2 - 1)
        else K * b ^ (α / 2) * u ^ (-((α + 1) / 2)))
    (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (ha : 0 < a) (haX : a ≤ X) (hXb : X ≤ b)
    (hK : ∀ u : ℝ, 0 < u → 0 < profTheta α β u ∧ profTheta α β u ≤ K / min u 1)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (ℓ : ℤ) :
    0 ≤ Real.sqrt (profZeta α X u * (1 - profZeta α X u) *
              (profZeta α X v * (1 - profZeta α X v))) / Real.sqrt (u * v) *
            (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v /
              profDelta α β ℓ u v) ∧
    Real.sqrt (profZeta α X u * (1 - profZeta α X u) *
              (profZeta α X v * (1 - profZeta α X v))) / Real.sqrt (u * v) *
            (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v /
              profDelta α β ℓ u v) ≤
      α * DLag β (Qm β u) (Qm β v) ℓ * (kf u / min (Real.sqrt u) 1) *
        (kf v / min (Real.sqrt v) 1) := by
  have hα0 : 0 < α := by linarith
  have hX : 0 < X := ha.trans_le haX
  obtain ⟨hz1, hz1'⟩ := vs_zeta_bd hα0 hX hu
  obtain ⟨hz2, hz2'⟩ := vs_zeta_bd hα0 hX hv
  have hA1 : 0 ≤ profZeta α X u * (1 - profZeta α X u) := mul_nonneg hz1.le (by linarith)
  have hA2 : 0 ≤ profZeta α X v * (1 - profZeta α X v) := mul_nonneg hz2.le (by linarith)
  obtain ⟨hQu, -⟩ := vs_Qm hβ0 hβ1 hu
  obtain ⟨hQv, -⟩ := vs_Qm hβ0 hβ1 hv
  have hD := vs_DLag_nonneg hβ0 hβ1 hQu.le hQv.le ℓ
  have hΔ := vs_Delta_ge hα1 hβ0 hβ1 hu hv ℓ
  have hΔ0 : 0 < profDelta α β ℓ u v := lt_of_lt_of_le (by positivity) hΔ
  obtain ⟨hθ1, -⟩ := hK u hu
  obtain ⟨hθ2, -⟩ := hK v hv
  obtain ⟨hs1, hs1'⟩ := vs_sigma_le (α := α) (β := β) (a := a) (b := b) (X := X) (K := K) hα1 ha haX hXb hK hu
  obtain ⟨hs2, hs2'⟩ := vs_sigma_le (α := α) (β := β) (a := a) (b := b) (X := X) (K := K) hα1 ha haX hXb hK hv
  rw [← hkf] at hs1' hs2'
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hw1 : 0 < min (Real.sqrt u) 1 := lt_min hsu one_pos
  have hw2 : 0 < min (Real.sqrt v) 1 := lt_min hsv one_pos
  have e : Real.sqrt (profZeta α X u * (1 - profZeta α X u) *
              (profZeta α X v * (1 - profZeta α X v))) / Real.sqrt (u * v) =
      Real.sqrt (profZeta α X u * (1 - profZeta α X u)) / Real.sqrt u *
        (Real.sqrt (profZeta α X v * (1 - profZeta α X v)) / Real.sqrt v) := by
    rw [Real.sqrt_mul hA1, Real.sqrt_mul hu.le]
    field_simp
  rw [e]
  set s1 := Real.sqrt (profZeta α X u * (1 - profZeta α X u)) / Real.sqrt u with hs1def
  set s2 := Real.sqrt (profZeta α X v * (1 - profZeta α X v)) / Real.sqrt v with hs2def
  have hs1n : 0 ≤ s1 := by positivity
  have hs2n : 0 ≤ s2 := by positivity
  set D := DLag β (Qm β u) (Qm β v) ℓ
  set Δ := profDelta α β ℓ u v
  set θ1 := profTheta α β u
  set θ2 := profTheta α β v
  refine ⟨by positivity, ?_⟩
  have hDΔ : D / Δ ≤ α * D := by
    rw [div_le_iff₀ hΔ0]
    have : 1 ≤ α * Δ := by
      have := mul_le_mul_of_nonneg_left hΔ hα0.le
      rwa [mul_one_div_cancel hα0.ne'] at this
    nlinarith
  have hb1 : s1 * θ1 ≤ kf u / min (Real.sqrt u) 1 := by
    rw [le_div_iff₀ hw1]; exact hs1'
  have hb2 : s2 * θ2 ≤ kf v / min (Real.sqrt v) 1 := by
    rw [le_div_iff₀ hw2]; exact hs2'
  have e2 : s1 * s2 * (D * θ1 * θ2 / Δ) = (s1 * θ1) * (s2 * θ2) * (D / Δ) := by ring
  rw [e2]
  have h1 : 0 ≤ (s1 * θ1) * (s2 * θ2) := by positivity
  calc (s1 * θ1) * (s2 * θ2) * (D / Δ) ≤ (s1 * θ1) * (s2 * θ2) * (α * D) :=
        mul_le_mul_of_nonneg_left hDΔ h1
    _ = α * D * (s1 * θ1) * (s2 * θ2) := by ring
    _ ≤ α * D * (kf u / min (Real.sqrt u) 1) * (kf v / min (Real.sqrt v) 1) := by
        have hαD : 0 ≤ α * D := by positivity
        refine mul_le_mul (mul_le_mul_of_nonneg_left hb1 hαD) hb2 (by positivity) (by
          have : 0 ≤ s1 * θ1 := by positivity
          have : 0 ≤ kf u / min (Real.sqrt u) 1 := this.trans hb1
          positivity)


open Muon.DetEquiv ProbabilityTheory in
private lemma vs_D_aem {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℤ) :
    AEMeasurable (fun p : ℝ × ℝ => DLag β (Qm β p.1) (Qm β p.2) ℓ)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  have hae : ∀ᵐ p ∂μ, 0 < p.1 ∧ 0 < p.2 := vs_ae_pos
  have hQm : AEMeasurable (Qm β) (volume.restrict (Ioi (0:ℝ))) :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Ioi (vs_Qm_mono hβ0 hβ1)
  have hQ1 : AEMeasurable (fun p : ℝ × ℝ => Qm β p.1) μ := hQm.comp_fst
  have hQ2 : AEMeasurable (fun p : ℝ × ℝ => Qm β p.2) μ := hQm.comp_snd
  have hpair : AEMeasurable (fun p : ℝ × ℝ => (Qm β p.1, Qm β p.2)) μ := hQ1.prodMk hQ2
  have hSm : MeasurableSet {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)
  classical
  have hg : Measurable ({q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}.piecewise
      (fun q : ℝ × ℝ => DLag β q.1 q.2 ℓ) 0) :=
    ContinuousOn.measurable_piecewise (vs_DLag_cont hβ0 hβ1 ℓ) continuousOn_const hSm
  refine (hg.comp_aemeasurable hpair).congr ?_
  filter_upwards [hae] with p hp
  have h1 := (vs_Qm hβ0 hβ1 hp.1).1
  have h2 := (vs_Qm hβ0 hβ1 hp.2).1
  simp only [Function.comp]
  rw [Set.piecewise_eq_of_mem _ _ _ (show (Qm β p.1, Qm β p.2) ∈
    {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} from ⟨h1.le, h2.le⟩)]

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_core {α β a b K : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (ha : 0 < a) (hab : a ≤ b)
    (hK : ∀ u : ℝ, 0 < u → 0 < profTheta α β u ∧ profTheta α β u ≤ K / min u 1) :
    ∃ bl : ℤ → ℝ × ℝ → ℝ,
      (∀ ℓ, Integrable (bl ℓ) ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) ∧
      Summable (fun ℓ : ℤ => ∫ p, bl ℓ p ∂((volume.restrict (Ioi (0:ℝ))).prod
        (volume.restrict (Ioi (0:ℝ))))) ∧
      ∀ X : ℝ, a ≤ X → X ≤ b → ∀ ℓ : ℤ, ∀ᵐ p ∂((volume.restrict (Ioi (0:ℝ))).prod
        (volume.restrict (Ioi (0:ℝ)))),
        0 ≤ Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2) ∧
        Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2) ≤ bl ℓ p := by
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  have hα0 : 0 < α := by linarith
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨kf, hkf⟩ : ∃ kf : ℝ → ℝ, ∀ u, kf u = if u ≤ 1 then K * (1 / a ^ (α / 2)) * u ^ (α / 2 - 1)
        else K * b ^ (α / 2) * u ^ (-((α + 1) / 2)) := ⟨_, fun _ => rfl⟩
  obtain ⟨C, hC0, hC⟩ := vs_D_bd hβ0 hβ1
  have hK0 : 0 ≤ K := by
    have := hK 1 one_pos
    simp only [min_self, div_one] at this
    exact this.1.le.trans this.2
  have hkf0 : ∀ u, 0 < u → 0 ≤ kf u := by
    intro u hu
    rw [hkf]
    split_ifs
    · have : 0 < a ^ (α / 2) := Real.rpow_pos_of_pos ha _
      positivity
    · have : 0 < b ^ (α / 2) := Real.rpow_pos_of_pos hb _
      positivity
  have hkint : Integrable kf (volume.restrict (Ioi (0:ℝ))) := by
    have := vs_k_int (α := α) (K := K) (A := 1 / a ^ (α / 2)) (B := b ^ (α / 2)) hα1
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp [hkf]
  have hkm : Measurable kf := by
    have : kf = fun u => if u ≤ 1 then K * (1 / a ^ (α / 2)) * u ^ (α / 2 - 1)
        else K * b ^ (α / 2) * u ^ (-((α + 1) / 2)) := funext hkf
    rw [this]
    refine Measurable.ite measurableSet_Iic ?_ ?_
    · exact measurable_const.mul (measurable_id.pow_const _)
    · exact measurable_const.mul (measurable_id.pow_const _)
  have hwm : Measurable (fun u : ℝ => min (Real.sqrt u) 1) :=
    (Real.continuous_sqrt.measurable).min measurable_const
  have hbig : Integrable (fun p : ℝ × ℝ => α * C * (kf p.1 * kf p.2)) μ :=
    (hkint.mul_prod hkint).const_mul _
  have hae : ∀ᵐ p ∂μ, 0 < p.1 ∧ 0 < p.2 := vs_ae_pos
  have hq : Measurable (fun u : ℝ => kf u / min (Real.sqrt u) 1) := hkm.div hwm
  have hint : ∀ ℓ : ℤ, Integrable (fun p : ℝ × ℝ => α * DLag β (Qm β p.1) (Qm β p.2) ℓ *
      (kf p.1 / min (Real.sqrt p.1) 1) * (kf p.2 / min (Real.sqrt p.2) 1)) μ := by
    intro ℓ
    have hmeas : AEMeasurable (fun p : ℝ × ℝ => α * DLag β (Qm β p.1) (Qm β p.2) ℓ *
        (kf p.1 / min (Real.sqrt p.1) 1) * (kf p.2 / min (Real.sqrt p.2) 1)) μ :=
      (((vs_D_aem hβ0 hβ1 ℓ).const_mul α).mul
        (hq.comp measurable_fst).aemeasurable).mul
        (hq.comp measurable_snd).aemeasurable
    refine Integrable.mono' hbig hmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with p hp
    obtain ⟨hQu, -⟩ := vs_Qm hβ0 hβ1 hp.1
    obtain ⟨hQv, -⟩ := vs_Qm hβ0 hβ1 hp.2
    have hD := vs_DLag_nonneg hβ0 hβ1 hQu.le hQv.le ℓ
    have hDb := hC p.1 p.2 hp.1 hp.2 {ℓ}
    rw [Finset.sum_singleton] at hDb
    have hw1 : 0 < min (Real.sqrt p.1) 1 := lt_min (Real.sqrt_pos.2 hp.1) one_pos
    have hw2 : 0 < min (Real.sqrt p.2) 1 := lt_min (Real.sqrt_pos.2 hp.2) one_pos
    have hk1 := hkf0 p.1 hp.1
    have hk2 := hkf0 p.2 hp.2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc α * DLag β (Qm β p.1) (Qm β p.2) ℓ * (kf p.1 / min (Real.sqrt p.1) 1) *
          (kf p.2 / min (Real.sqrt p.2) 1)
        ≤ α * (C * min (Real.sqrt p.1) 1 * min (Real.sqrt p.2) 1) *
            (kf p.1 / min (Real.sqrt p.1) 1) * (kf p.2 / min (Real.sqrt p.2) 1) := by
          gcongr
      _ = α * C * (kf p.1 * kf p.2) := by field_simp
  refine ⟨fun ℓ p => α * DLag β (Qm β p.1) (Qm β p.2) ℓ * (kf p.1 / min (Real.sqrt p.1) 1) *
    (kf p.2 / min (Real.sqrt p.2) 1), hint, ?_, ?_⟩
  · refine summable_of_sum_le (c := ∫ p, α * C * (kf p.1 * kf p.2) ∂μ) (fun ℓ => ?_) (fun s => ?_)
    · refine integral_nonneg_of_ae ?_
      filter_upwards [hae] with p hp
      obtain ⟨hQu, -⟩ := vs_Qm hβ0 hβ1 hp.1
      obtain ⟨hQv, -⟩ := vs_Qm hβ0 hβ1 hp.2
      have hD := vs_DLag_nonneg hβ0 hβ1 hQu.le hQv.le ℓ
      have hw1 : 0 < min (Real.sqrt p.1) 1 := lt_min (Real.sqrt_pos.2 hp.1) one_pos
      have hw2 : 0 < min (Real.sqrt p.2) 1 := lt_min (Real.sqrt_pos.2 hp.2) one_pos
      have hk1 := hkf0 p.1 hp.1
      have hk2 := hkf0 p.2 hp.2
      change 0 ≤ α * DLag β (Qm β p.1) (Qm β p.2) ℓ * (kf p.1 / min (Real.sqrt p.1) 1) *
        (kf p.2 / min (Real.sqrt p.2) 1)
      positivity
    · rw [← integral_finset_sum _ (fun ℓ _ => hint ℓ)]
      refine integral_mono_ae (integrable_finset_sum _ (fun ℓ _ => hint ℓ)) hbig ?_
      filter_upwards [hae] with p hp
      obtain ⟨hQu, -⟩ := vs_Qm hβ0 hβ1 hp.1
      obtain ⟨hQv, -⟩ := vs_Qm hβ0 hβ1 hp.2
      have hDb := hC p.1 p.2 hp.1 hp.2 s
      have hw1 : 0 < min (Real.sqrt p.1) 1 := lt_min (Real.sqrt_pos.2 hp.1) one_pos
      have hw2 : 0 < min (Real.sqrt p.2) 1 := lt_min (Real.sqrt_pos.2 hp.2) one_pos
      have hk1 := hkf0 p.1 hp.1
      have hk2 := hkf0 p.2 hp.2
      have e : ∑ ℓ ∈ s, α * DLag β (Qm β p.1) (Qm β p.2) ℓ * (kf p.1 / min (Real.sqrt p.1) 1) *
          (kf p.2 / min (Real.sqrt p.2) 1) =
          α * (∑ ℓ ∈ s, DLag β (Qm β p.1) (Qm β p.2) ℓ) * (kf p.1 / min (Real.sqrt p.1) 1) *
          (kf p.2 / min (Real.sqrt p.2) 1) := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      rw [e]
      refine le_trans (b := α * (C * min (Real.sqrt p.1) 1 * min (Real.sqrt p.2) 1) *
            (kf p.1 / min (Real.sqrt p.1) 1) * (kf p.2 / min (Real.sqrt p.2) 1)) (by gcongr)
        (le_of_eq (by field_simp))
  · intro X haX hXb ℓ
    filter_upwards [hae] with p hp
    have := vs_pointwise kf hkf hα1 hβ0 hβ1 ha haX hXb hK hp.1 hp.2 ℓ
    exact this


open Muon.DetEquiv ProbabilityTheory in
private lemma vs_iter_eq {α β X : ℝ} (ℓ : ℤ)
    (hint : Integrable (fun p : ℝ × ℝ =>
          Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2))
        ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) :
    (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
        Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) =
    ∫ p : ℝ × ℝ,
          Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2)
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
  (integral_prod _ hint).symm

open Muon.DetEquiv ProbabilityTheory in
private lemma vs_finite_all {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (X : ℝ) (hX : 0 < X) :
    (∀ ℓ : ℤ, Integrable
        (fun p : ℝ × ℝ =>
          Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2))
        ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) ∧
    Summable (fun ℓ : ℤ => ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
        Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) := by
  obtain ⟨K, hK0, hK⟩ := vs_theta_bd hα1 hβ0 hβ1
  obtain ⟨bl, hbl, hbls, hbd⟩ := vs_core hα1 hβ0 hβ1 hX (le_refl X) hK
  have hint : ∀ ℓ : ℤ, Integrable
        (fun p : ℝ × ℝ =>
          Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2))
        ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := fun ℓ =>
    Integrable.mono' (hbl ℓ) (vs_F_meas hβ0 hβ1 X ℓ) (by
      filter_upwards [hbd X le_rfl le_rfl ℓ] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
      exact hp.2)
  refine ⟨hint, ?_⟩
  refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_) hbls
  · rw [vs_iter_eq ℓ (hint ℓ)]
    exact integral_nonneg_of_ae (by filter_upwards [hbd X le_rfl le_rfl ℓ] with p hp using hp.1)
  · rw [vs_iter_eq ℓ (hint ℓ)]
    exact integral_mono_ae (hint ℓ) (hbl ℓ)
      (by filter_upwards [hbd X le_rfl le_rfl ℓ] with p hp using hp.2)


open Muon.DetEquiv ProbabilityTheory in
private lemma vs_pos_all {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (X : ℝ) (hX : 0 < X) : 0 < profG α β X := by
  have hα0 : 0 < α := by linarith
  obtain ⟨hint, hsum⟩ := vs_finite_all hα1 hβ0 hβ1 X hX
  obtain ⟨K, hK0, hK⟩ := vs_theta_bd hα1 hβ0 hβ1
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  have hae : ∀ᵐ p ∂μ, 0 < p.1 ∧ 0 < p.2 := vs_ae_pos
  -- pointwise positivity of the lag-0 integrand
  have hpos : ∀ p : ℝ × ℝ, 0 < p.1 → 0 < p.2 →
      0 < Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) 0 * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β 0 p.1 p.2) := by
    intro p hp1 hp2
    obtain ⟨hz1, hz1'⟩ := vs_zeta_bd hα0 hX hp1
    obtain ⟨hz2, hz2'⟩ := vs_zeta_bd hα0 hX hp2
    have hA1 : 0 < profZeta α X p.1 * (1 - profZeta α X p.1) := mul_pos hz1 (by linarith)
    have hA2 : 0 < profZeta α X p.2 * (1 - profZeta α X p.2) := mul_pos hz2 (by linarith)
    obtain ⟨hQu, -⟩ := vs_Qm hβ0 hβ1 hp1
    obtain ⟨hQv, -⟩ := vs_Qm hβ0 hβ1 hp2
    have hD := vs_DLag_zero_pos hβ0 hβ1 hQu hQv
    have hΔ := vs_Delta_ge hα1 hβ0 hβ1 hp1 hp2 0
    have hΔ0 : 0 < profDelta α β 0 p.1 p.2 := lt_of_lt_of_le (by positivity) hΔ
    have hθ1 := (hK p.1 hp1).1
    have hθ2 := (hK p.2 hp2).1
    have : 0 < Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) :=
      Real.sqrt_pos.2 (mul_pos hA1 hA2)
    have : 0 < Real.sqrt (p.1 * p.2) := Real.sqrt_pos.2 (mul_pos hp1 hp2)
    positivity
  have h0pos : 0 < ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
        Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) 0 * profTheta α β u * profTheta α β v / profDelta α β 0 u v) := by
    rw [vs_iter_eq 0 (hint 0)]
    rw [integral_pos_iff_support_of_nonneg_ae
      (by filter_upwards [hae] with p hp using (hpos p hp.1 hp.2).le) (hint 0)]
    rw [pos_iff_ne_zero]
    intro h0
    have hsub : ∀ᵐ p ∂μ, p ∈ Function.support (fun p : ℝ × ℝ =>
        Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) 0 * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β 0 p.1 p.2)) := by
      filter_upwards [hae] with p hp using (hpos p hp.1 hp.2).ne'
    have h1 : μ (Function.support (fun p : ℝ × ℝ =>
        Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) 0 * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β 0 p.1 p.2)))ᶜ = 0 := mem_ae_iff.1 hsub
    have := measure_union_null h0 h1
    rw [union_compl_self] at this
    have hu : μ Set.univ = ⊤ := by
      rw [hμ, ← Set.univ_prod_univ, Measure.prod_prod]
      simp
    rw [hu] at this
    exact ENNReal.top_ne_zero this
  unfold profG
  refine mul_pos (by positivity) ?_
  refine lt_of_lt_of_le h0pos (hsum.le_tsum 0 (fun ℓ _ => ?_))
  rw [vs_iter_eq ℓ (hint ℓ)]
  obtain ⟨bl, hbl, hbls, hbd⟩ := vs_core hα1 hβ0 hβ1 hX (le_refl X) hK
  exact integral_nonneg_of_ae (by filter_upwards [hbd X le_rfl le_rfl ℓ] with p hp using hp.1)


open Muon.DetEquiv ProbabilityTheory in
private lemma vs_cont_Icc {α β a b : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (ha : 0 < a) (hab : a ≤ b) : ContinuousOn (fun X : ℝ => profG α β X) (Icc a b) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨K, hK0, hK⟩ := vs_theta_bd hα1 hβ0 hβ1
  obtain ⟨bl, hbl, hbls, hbd⟩ := vs_core hα1 hβ0 hβ1 ha hab hK
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  have hae : ∀ᵐ p ∂μ, 0 < p.1 ∧ 0 < p.2 := vs_ae_pos
  have hFint : ∀ X ∈ Icc a b, ∀ ℓ : ℤ, Integrable
        (fun p : ℝ × ℝ =>
          Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2)) μ := fun X hX ℓ =>
    Integrable.mono' (hbl ℓ) (vs_F_meas hβ0 hβ1 X ℓ) (by
      filter_upwards [hbd X hX.1 hX.2 ℓ] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
      exact hp.2)
  have hcont : ContinuousOn (fun X : ℝ => ∑' ℓ : ℤ, ∫ p : ℝ × ℝ,
          Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2) ∂μ) (Icc a b) := by
    refine continuousOn_tsum (u := fun ℓ => ∫ p, bl ℓ p ∂μ) (fun ℓ => ?_) hbls (fun ℓ X hX => ?_)
    · refine continuousOn_of_dominated (bound := bl ℓ)
        (fun X hX => vs_F_meas hβ0 hβ1 X ℓ) (fun X hX => ?_) (hbl ℓ) ?_
      · filter_upwards [hbd X hX.1 hX.2 ℓ] with p hp
        rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
        exact hp.2
      · filter_upwards [hae] with p hp
        have hζ : ∀ u : ℝ, 0 < u → ContinuousOn (fun X : ℝ => profZeta α X u) (Icc a b) := by
          intro u hu
          unfold profZeta
          refine continuousOn_const.div (((Real.continuous_rpow_const hα0.le).continuousOn).add
            continuousOn_const) (fun X hX => ?_)
          have h1 : 0 < X ^ α := Real.rpow_pos_of_pos (ha.trans_le hX.1) α
          have h2 : 0 ≤ u ^ α := Real.rpow_nonneg hu.le α
          change X ^ α + u ^ α ≠ 0
          linarith
        have h1 := hζ p.1 hp.1
        have h2 := hζ p.2 hp.2
        exact ((Real.continuous_sqrt.comp_continuousOn ((h1.mul (continuousOn_const.sub h1)).mul
          (h2.mul (continuousOn_const.sub h2)))).div_const _).mul continuousOn_const
    · refine (norm_integral_le_of_norm_le (hbl ℓ) ?_)
      filter_upwards [hbd X hX.1 hX.2 ℓ] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
      exact hp.2
  have heq : ∀ X ∈ Icc a b, profG α β X = (1 / Real.pi ^ 2) * ∑' ℓ : ℤ, ∫ p : ℝ × ℝ,
          Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2) ∂μ := by
    intro X hX
    unfold profG
    congr 1
    exact tsum_congr fun ℓ => vs_iter_eq ℓ (hFint X hX ℓ)
  exact (continuousOn_const.mul hcont).congr heq


/-! ## Profile of the supercritical crossover -/

/-- `lem:app-pl-supervol`, finiteness of `G_{α,β}` (part of the first sentence; snapshot `cr-2026-10-23`).
The integrand of `eqn:app-pl-G` for the lag `ℓ`, integrable on `(0,∞)²` for every `ℓ`, with the lag sum
summable. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Supercritical volatility]\label{lem:app-pl-supervol}
The function $G_{\alpha,\bmom}$ is finite, positive and continuous on $(0,\infty)$ and satisfies the
two endpoint laws of \cref{eqn:app-pl-crossover-ends}. Under \cref{assum:app-pl-regime}, for
every row sequence $i\to\infty$: if $X\to X_0\in(0,\infty)$ then $\mathfrak v_i(0)\to G_{\alpha,\bmom}(X_0)$; if
$X\to0$ then $\mathfrak v_i(0)\to1/\sw2$; if $X\to\infty$ and $i/N\to0$ then
$\mathfrak v_i(0)\sim\frac{4K_\alpha}{\alpha-1}X$. Moreover $\Gamma_\alpha(x)\sim\frac{4K_\alpha^2}{\alpha-1}x$ as $x\downarrow0$.
\end{lemma}
-/
theorem lem_app_pl_supervol_i_finite {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (X : ℝ) (hX : 0 < X) :
    (∀ ℓ : ℤ, Integrable
        (fun p : ℝ × ℝ =>
          Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2))
        ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) ∧
    Summable (fun ℓ : ℤ => ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
        Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) := by
  exact vs_finite_all hα1 hβ0 hβ1 X hX

/-- `lem:app-pl-supervol`, positivity of `G_{α,β}` on `(0,∞)` (snapshot `cr-2026-10-23`). LaTeX, verbatim
from `sections/06-power-law/section.tex`:

\begin{lemma}[Supercritical volatility]\label{lem:app-pl-supervol}
The function $G_{\alpha,\bmom}$ is finite, positive and continuous on $(0,\infty)$ and satisfies the
two endpoint laws of \cref{eqn:app-pl-crossover-ends}. Under \cref{assum:app-pl-regime}, for
every row sequence $i\to\infty$: if $X\to X_0\in(0,\infty)$ then $\mathfrak v_i(0)\to G_{\alpha,\bmom}(X_0)$; if
$X\to0$ then $\mathfrak v_i(0)\to1/\sw2$; if $X\to\infty$ and $i/N\to0$ then
$\mathfrak v_i(0)\sim\frac{4K_\alpha}{\alpha-1}X$. Moreover $\Gamma_\alpha(x)\sim\frac{4K_\alpha^2}{\alpha-1}x$ as $x\downarrow0$.
\end{lemma}
-/
theorem lem_app_pl_supervol_i_pos {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ X : ℝ, 0 < X → 0 < profG α β X := by
  intro X hX
  exact vs_pos_all hα1 hβ0 hβ1 X hX

/-- `lem:app-pl-supervol`, continuity of `G_{α,β}` on `(0,∞)` (snapshot `cr-2026-10-23`). LaTeX, verbatim
from `sections/06-power-law/section.tex`:

\begin{lemma}[Supercritical volatility]\label{lem:app-pl-supervol}
The function $G_{\alpha,\bmom}$ is finite, positive and continuous on $(0,\infty)$ and satisfies the
two endpoint laws of \cref{eqn:app-pl-crossover-ends}. Under \cref{assum:app-pl-regime}, for
every row sequence $i\to\infty$: if $X\to X_0\in(0,\infty)$ then $\mathfrak v_i(0)\to G_{\alpha,\bmom}(X_0)$; if
$X\to0$ then $\mathfrak v_i(0)\to1/\sw2$; if $X\to\infty$ and $i/N\to0$ then
$\mathfrak v_i(0)\sim\frac{4K_\alpha}{\alpha-1}X$. Moreover $\Gamma_\alpha(x)\sim\frac{4K_\alpha^2}{\alpha-1}x$ as $x\downarrow0$.
\end{lemma}
-/
theorem lem_app_pl_supervol_i_cont {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (fun X : ℝ => profG α β X) (Ioi 0) := by
  intro X0 hX0
  have h := vs_cont_Icc hα1 hβ0 hβ1 (a := X0 / 2) (b := 2 * X0) (by have := hX0; simp only [mem_Ioi] at this; linarith) (by have := hX0; simp only [mem_Ioi] at this; linarith)
  have hX0' : (0:ℝ) < X0 := hX0
  exact (h.continuousAt (Icc_mem_nhds (by linarith) (by linarith))).continuousWithinAt

private lemma vz_rescale {X : ℝ} (hX : 0 < X) (g : ℝ × ℝ → ℝ) :
    ∫ p, g (X • p) ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) =
      (X ^ 2)⁻¹ * ∫ p, g p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  set S : Set (ℝ × ℝ) := Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) with hS
  have hSm : MeasurableSet S := measurableSet_Ioi.prod measurableSet_Ioi
  have hpre : ∀ p : ℝ × ℝ, X • p ∈ S ↔ p ∈ S := by
    intro p
    simp only [hS, mem_prod, mem_Ioi, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(pos_iff_pos_of_mul_pos h1).1 hX, (pos_iff_pos_of_mul_pos h2).1 hX⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos hX h1, mul_pos hX h2⟩
  rw [← integral_indicator hSm, ← integral_indicator hSm]
  have e : (S.indicator fun p => g (X • p)) = fun p => (S.indicator g) (X • p) := by
    funext p
    by_cases h : p ∈ S
    · simp [Set.indicator_of_mem h, Set.indicator_of_mem ((hpre p).2 h)]
    · simp [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hpre p).1 h'))]
  rw [e, Measure.integral_comp_smul]
  have : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [this, abs_of_pos (by positivity), smul_eq_mul]

private lemma vz_k_integral {α : ℝ} (hα : 0 < α) :
    ∫ r in Ioi (0:ℝ), α * r ^ (α / 2 - 1) / (1 + r ^ α) = Real.pi := by
  have h := integral_comp_rpow_Ioi (fun y : ℝ => (1 + y ^ 2)⁻¹) (p := α / 2) (by positivity)
  rw [integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero] at h
  have e : ∀ r ∈ Ioi (0:ℝ), α * r ^ (α / 2 - 1) / (1 + r ^ α) =
      2 * ((|α / 2| * r ^ (α / 2 - 1)) • (fun y : ℝ => (1 + y ^ 2)⁻¹) (r ^ (α / 2))) := by
    intro r hr
    have hr0 : 0 ≤ r := le_of_lt hr
    have : (r ^ (α / 2)) ^ 2 = r ^ α := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr0]; congr 1; push_cast; ring
    simp only [smul_eq_mul, this, abs_of_pos (by positivity : 0 < α / 2)]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, h]
  ring

private lemma vz_beta_sum {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    HasSum (fun ℓ : ℤ => β ^ ℓ.natAbs) (1 / sPow β 2) := by
  have h1 : HasSum (fun n : ℕ => β ^ n) (1 - β)⁻¹ := hasSum_geometric_of_lt_one hβ0.le hβ1
  have h2 : HasSum (fun n : ℕ => β ^ (n + 1)) (β * (1 - β)⁻¹) := by
    have := h1.mul_left β
    simpa [pow_succ, mul_comm] using this
  have e : ∀ n : ℕ, (-((n:ℤ) + 1)).natAbs = n + 1 := fun n => by omega
  have h3 : HasSum (fun ℓ : ℤ => β ^ ℓ.natAbs) ((1 - β)⁻¹ + β * (1 - β)⁻¹) :=
    HasSum.of_nat_of_neg_add_one (f := fun ℓ : ℤ => β ^ ℓ.natAbs)
      (by simpa using h1) (by
        convert h2 using 1
        funext n
        show β ^ (-((n:ℤ) + 1)).natAbs = β ^ (n + 1)
        rw [e])
  have hq : (0:ℝ) < 1 - β := by linarith
  convert h3 using 1
  rw [sPow_two hβ0.le hβ1]
  field_simp


private lemma vz_wp_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {p : ℕ} (hp : 1 ≤ p) :
    Summable (fun a : ℕ => emaW β a ^ p) := by
  have hr : β ^ p < 1 := pow_lt_one₀ hβ0.le hβ1 (by omega)
  have key : (fun j : ℕ => emaW β j ^ p) = fun j => (1 - β) ^ p * (β ^ p) ^ j := by
    funext j
    unfold emaW
    rw [mul_pow, pow_right_comm β j p]
  rw [key]
  exact (summable_geometric_of_lt_one (by positivity) hr).mul_left _

open Muon.DetEquiv ProbabilityTheory in
private lemma vz_DNat_approx {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ} (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (ℓ : ℕ) :
    0 ≤ β ^ ℓ * Real.sqrt (q1 * q2) * sPow β 2 - DLagNat β q1 q2 ℓ ∧
    β ^ ℓ * Real.sqrt (q1 * q2) * sPow β 2 - DLagNat β q1 q2 ℓ ≤
      3 * sPow β 4 * (Real.sqrt (q1 * q2) * (q1 + q2)) := by
  obtain ⟨hint, hsum⟩ := vs_D_terms hβ0 hβ1 hq1 hq2 ℓ
  set c : ℝ := β ^ ℓ * Real.sqrt (q1 * q2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hρ1 : β ^ ℓ ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  set p : ℝ := β ^ (2 * ℓ) * q2 with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ q2 := by
    have : β ^ (2 * ℓ) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
    nlinarith
  have hi2 := Muon.Foundations.gaussian_integrable_pow 2
  have hi4 := Muon.Foundations.gaussian_integrable_pow 4
  -- the term and its comparison functions
  set t : ℕ → ℝ → ℝ := fun a g => c * emaW β a ^ 2 * g ^ 2 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + p * emaW β a ^ 2 * g ^ 2)) with ht
  have htD : DLagNat β q1 q2 ℓ = ∑' a, ∫ g, t a g ∂(gaussianReal 0 1) := by
    unfold DLagNat
    refine tsum_congr fun a => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [ht, hc, hp]
  have hts : Summable (fun a => ∫ g, t a g ∂(gaussianReal 0 1)) := by
    refine hsum.congr fun a => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [ht, hc, hp]
  have hti : ∀ a, Integrable (t a) (gaussianReal 0 1) := by
    intro a
    refine (hint a).congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [ht, hc, hp]
  have hu_int : ∀ a, Integrable (fun g : ℝ => c * emaW β a ^ 2 * g ^ 2) (gaussianReal 0 1) :=
    fun a => hi2.const_mul _
  have hv_int : ∀ a, Integrable (fun g : ℝ => c * (q1 + p) * emaW β a ^ 4 * g ^ 4)
      (gaussianReal 0 1) := fun a => hi4.const_mul _
  have hu_val : ∀ a, ∫ g, c * emaW β a ^ 2 * g ^ 2 ∂(gaussianReal 0 1) = c * emaW β a ^ 2 := by
    intro a
    have : (fun g : ℝ => c * emaW β a ^ 2 * g ^ 2) = fun g => (c * emaW β a ^ 2) * g ^ 2 := rfl
    rw [this, integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one]
  have hv_val : ∀ a, ∫ g, c * (q1 + p) * emaW β a ^ 4 * g ^ 4 ∂(gaussianReal 0 1) =
      3 * (c * (q1 + p)) * emaW β a ^ 4 := by
    intro a
    have : (fun g : ℝ => c * (q1 + p) * emaW β a ^ 4 * g ^ 4) =
        fun g => (c * (q1 + p) * emaW β a ^ 4) * g ^ 4 := rfl
    rw [this, integral_const_mul, Muon.Foundations.gaussian_moment_four]
    ring
  -- pointwise
  have hpt : ∀ a g, 0 ≤ c * emaW β a ^ 2 * g ^ 2 - t a g ∧
      c * emaW β a ^ 2 * g ^ 2 - t a g ≤ c * (q1 + p) * emaW β a ^ 4 * g ^ 4 := by
    intro a g
    have hA : 0 ≤ q1 * emaW β a ^ 2 * g ^ 2 := by positivity
    have hB : 0 ≤ p * emaW β a ^ 2 * g ^ 2 := by positivity
    have hden : 1 + (q1 * emaW β a ^ 2 * g ^ 2 + p * emaW β a ^ 2 * g ^ 2) ≤
        (1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + p * emaW β a ^ 2 * g ^ 2) := by
      nlinarith [mul_nonneg hA hB]
    have hd0 : 0 < (1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + p * emaW β a ^ 2 * g ^ 2) := by positivity
    have hn : 0 ≤ c * emaW β a ^ 2 * g ^ 2 := by positivity
    set D := (1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + p * emaW β a ^ 2 * g ^ 2) with hD
    have hD1 : 1 ≤ D := by nlinarith
    have e : c * emaW β a ^ 2 * g ^ 2 - t a g = c * emaW β a ^ 2 * g ^ 2 * (D - 1) / D := by
      rw [show t a g = c * emaW β a ^ 2 * g ^ 2 / D from rfl]
      field_simp
    constructor
    · rw [e]; exact div_nonneg (mul_nonneg hn (by linarith)) hd0.le
    · rw [e, div_le_iff₀ hd0]
      have hS : D - 1 ≤ D * (q1 * emaW β a ^ 2 * g ^ 2 + p * emaW β a ^ 2 * g ^ 2) := by
        have : D ≤ D := le_rfl
        nlinarith
      calc c * emaW β a ^ 2 * g ^ 2 * (D - 1)
          ≤ c * emaW β a ^ 2 * g ^ 2 * (D * (q1 * emaW β a ^ 2 * g ^ 2 + p * emaW β a ^ 2 * g ^ 2)) :=
            mul_le_mul_of_nonneg_left hS hn
        _ = c * (q1 + p) * emaW β a ^ 4 * g ^ 4 * D := by ring
  have hdiff : ∀ a, 0 ≤ ∫ g, (c * emaW β a ^ 2 * g ^ 2 - t a g) ∂(gaussianReal 0 1) ∧
      ∫ g, (c * emaW β a ^ 2 * g ^ 2 - t a g) ∂(gaussianReal 0 1) ≤
        3 * (c * (q1 + p)) * emaW β a ^ 4 := by
    intro a
    refine ⟨integral_nonneg fun g => (hpt a g).1, ?_⟩
    rw [← hv_val a]
    exact integral_mono ((hu_int a).sub (hti a)) (hv_int a) fun g => (hpt a g).2
  have hdi : ∀ a, ∫ g, (c * emaW β a ^ 2 * g ^ 2 - t a g) ∂(gaussianReal 0 1) =
      c * emaW β a ^ 2 - ∫ g, t a g ∂(gaussianReal 0 1) := by
    intro a
    rw [integral_sub (hu_int a) (hti a), hu_val]
  have hw2 : Summable (fun a => c * emaW β a ^ 2) := (vz_wp_summable hβ0 hβ1 (p := 2) (by norm_num)).mul_left c
  have hw4 : Summable (fun a => 3 * (c * (q1 + p)) * emaW β a ^ 4) :=
    (vz_wp_summable hβ0 hβ1 (p := 4) (by norm_num)).mul_left _
  have hsub : Summable (fun a => c * emaW β a ^ 2 - ∫ g, t a g ∂(gaussianReal 0 1)) :=
    hw2.sub hts
  have hs2 : ∑' a, c * emaW β a ^ 2 = c * sPow β 2 := by
    unfold sPow; rw [tsum_mul_left]
  have hs4 : ∑' a, 3 * (c * (q1 + p)) * emaW β a ^ 4 = 3 * (c * (q1 + p)) * sPow β 4 := by
    unfold sPow; rw [tsum_mul_left]
  have hkey : c * sPow β 2 - DLagNat β q1 q2 ℓ =
      ∑' a, (c * emaW β a ^ 2 - ∫ g, t a g ∂(gaussianReal 0 1)) := by
    rw [hw2.tsum_sub hts, hs2, htD]
  have hfin : β ^ ℓ * Real.sqrt (q1 * q2) * sPow β 2 = c * sPow β 2 := rfl
  rw [hfin, hkey]
  refine ⟨tsum_nonneg fun a => ?_, ?_⟩
  · rw [← hdi a]; exact (hdiff a).1
  · calc ∑' a, (c * emaW β a ^ 2 - ∫ g, t a g ∂(gaussianReal 0 1))
        ≤ ∑' a, 3 * (c * (q1 + p)) * emaW β a ^ 4 := by
          refine Summable.tsum_le_tsum (fun a => ?_) hsub hw4
          rw [← hdi a]; exact (hdiff a).2
      _ = 3 * (c * (q1 + p)) * sPow β 4 := hs4
      _ ≤ 3 * sPow β 4 * (Real.sqrt (q1 * q2) * (q1 + q2)) := by
          have hs4n : 0 ≤ sPow β 4 := tsum_nonneg fun a => by
            have := vs_emaW_pos hβ0 hβ1 a; positivity
          have h1 : c ≤ Real.sqrt (q1 * q2) := mul_le_of_le_one_left (Real.sqrt_nonneg _) hρ1
          have h2 : c * (q1 + p) ≤ Real.sqrt (q1 * q2) * (q1 + q2) :=
            mul_le_mul h1 (by linarith) (by positivity) (Real.sqrt_nonneg _)
          nlinarith


open Muon.DetEquiv ProbabilityTheory in
private lemma vz_MNat_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ} (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (ℓ : ℕ) : 0 ≤ MLagNat β q1 q2 ℓ ∧ MLagNat β q1 q2 ℓ ≤ 3 * sPow β 4 * (q1 * q2) := by
  have hi4 := Muon.Foundations.gaussian_integrable_pow 4
  set f : ℕ → ℝ → ℝ := fun a g => β ^ (2 * ℓ) * q1 * q2 * emaW β a ^ 4 * g ^ 4 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2)) with hf
  have hρ : 0 ≤ β ^ (2 * ℓ) := pow_nonneg hβ0.le _
  have hρ1 : β ^ (2 * ℓ) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hf0 : ∀ a g, 0 ≤ f a g := fun a g => by simp only [hf]; positivity
  have hfle : ∀ a g, f a g ≤ q1 * q2 * emaW β a ^ 4 * g ^ 4 := by
    intro a g
    have hden : 1 ≤ (1 + q1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2) := by
      have h1 : 0 ≤ q1 * emaW β a ^ 2 * g ^ 2 := by positivity
      have h2 : 0 ≤ β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2 := by positivity
      nlinarith [mul_nonneg h1 h2]
    have hn : 0 ≤ β ^ (2 * ℓ) * q1 * q2 * emaW β a ^ 4 * g ^ 4 := by positivity
    refine (div_le_self hn hden).trans ?_
    have h3 : 0 ≤ q1 * q2 * emaW β a ^ 4 * g ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hρ1 h3]
  have hcont : ∀ a, Continuous (f a) := by
    intro a
    have hd : ∀ g : ℝ, (1 + q1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2) ≠ 0 := fun g => by
      have : 0 < (1 + q1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2) := by positivity
      exact this.ne'
    exact (by fun_prop : Continuous fun g : ℝ => β ^ (2 * ℓ) * q1 * q2 * emaW β a ^ 4 * g ^ 4).div
      (by fun_prop) hd
  have hb : ∀ a, Integrable (fun g : ℝ => q1 * q2 * emaW β a ^ 4 * g ^ 4) (gaussianReal 0 1) :=
    fun a => hi4.const_mul _
  have hint : ∀ a, Integrable (f a) (gaussianReal 0 1) := fun a =>
    Integrable.mono' (hb a) (hcont a).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 a g)]; exact hfle a g)
  have hbv : ∀ a, ∫ g, q1 * q2 * emaW β a ^ 4 * g ^ 4 ∂(gaussianReal 0 1) =
      3 * (q1 * q2) * emaW β a ^ 4 := by
    intro a
    have : (fun g : ℝ => q1 * q2 * emaW β a ^ 4 * g ^ 4) =
        fun g => (q1 * q2 * emaW β a ^ 4) * g ^ 4 := rfl
    rw [this, integral_const_mul, Muon.Foundations.gaussian_moment_four]; ring
  have hw4 : Summable (fun a => 3 * (q1 * q2) * emaW β a ^ 4) :=
    (vz_wp_summable hβ0 hβ1 (p := 4) (by norm_num)).mul_left _
  have hle : ∀ a, ∫ g, f a g ∂(gaussianReal 0 1) ≤ 3 * (q1 * q2) * emaW β a ^ 4 := by
    intro a
    rw [← hbv a]
    exact integral_mono (hint a) (hb a) (hfle a)
  have hsum : Summable (fun a => ∫ g, f a g ∂(gaussianReal 0 1)) :=
    Summable.of_nonneg_of_le (fun a => integral_nonneg (hf0 a)) hle hw4
  have hM : MLagNat β q1 q2 ℓ = ∑' a, ∫ g, f a g ∂(gaussianReal 0 1) := rfl
  refine ⟨hM ▸ tsum_nonneg fun a => integral_nonneg (hf0 a), ?_⟩
  rw [hM]
  calc ∑' a, ∫ g, f a g ∂(gaussianReal 0 1) ≤ ∑' a, 3 * (q1 * q2) * emaW β a ^ 4 :=
        Summable.tsum_le_tsum hle hsum hw4
    _ = 3 * sPow β 4 * (q1 * q2) := by
        unfold sPow; rw [tsum_mul_left]; ring

open Muon.DetEquiv ProbabilityTheory in
private lemma vz_D_approx {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ} (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (ℓ : ℤ) :
    0 ≤ β ^ ℓ.natAbs * Real.sqrt (q1 * q2) * sPow β 2 - DLag β q1 q2 ℓ ∧
    β ^ ℓ.natAbs * Real.sqrt (q1 * q2) * sPow β 2 - DLag β q1 q2 ℓ ≤
      3 * sPow β 4 * (Real.sqrt (q1 * q2) * (q1 + q2)) := by
  unfold DLag
  split_ifs with h
  · have e : ℓ.natAbs = ℓ.toNat := by omega
    rw [e]
    exact vz_DNat_approx hβ0 hβ1 hq1 hq2 _
  · have e : ℓ.natAbs = (-ℓ).toNat := by omega
    rw [e]
    have := vz_DNat_approx hβ0 hβ1 hq2 hq1 (-ℓ).toNat
    rw [mul_comm q2 q1, add_comm q2 q1] at this
    exact this

open Muon.DetEquiv ProbabilityTheory in
private lemma vz_M_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ} (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (ℓ : ℤ) : 0 ≤ MLag β q1 q2 ℓ ∧ MLag β q1 q2 ℓ ≤ 3 * sPow β 4 * (q1 * q2) := by
  unfold MLag
  split_ifs with h
  · exact vz_MNat_le hβ0 hβ1 hq1 hq2 _
  · have := vz_MNat_le hβ0 hβ1 hq2 hq1 (-ℓ).toNat
    rw [mul_comm q2 q1] at this
    exact this


private lemma vz_mul_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun X : ℝ => X * r) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun X : ℝ => X * r) (𝓝 0) (𝓝 (0 * r)) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with X hX
    exact mul_pos hX hr

private lemma vz_Qratio {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun m : ℝ => Qm β m / m) (𝓝[>] (0:ℝ)) (𝓝 (1 / sPow β 2)) := by
  have hs2 : 0 < sPow β 2 := by
    rw [sPow_two hβ0.le hβ1]
    have : (0:ℝ) < 1 - β := by linarith
    positivity
  have h := lem_app_pl_weights_i_Q hβ0.le hβ1
  have hne : ∀ᶠ m : ℝ in 𝓝[>] (0:ℝ), m / sPow β 2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with m hm
    have : (0:ℝ) < m := hm
    positivity
  have h2 := (isEquivalent_iff_tendsto_one hne).1 h
  have h3 := h2.mul_const (1 / sPow β 2)
  rw [one_mul] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with m hm
  have hm0 : (0:ℝ) < m := hm
  simp only [Pi.div_apply]
  field_simp


private lemma vz_s2_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 < sPow β 2 := by
  rw [sPow_two hβ0.le hβ1]
  have : (0:ℝ) < 1 - β := by linarith
  positivity

private lemma vz_Qr {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun X : ℝ => Qm β (X * r) / X) (𝓝[>] (0:ℝ)) (𝓝 (r / sPow β 2)) := by
  have h := ((vz_Qratio hβ0 hβ1).comp (vz_mul_tendsto hr)).mul_const r
  have e : 1 / sPow β 2 * r = r / sPow β 2 := by ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with X hX
  have hX0 : (0:ℝ) < X := hX
  simp only [Function.comp]
  field_simp

open Muon.DetEquiv ProbabilityTheory in
private lemma vz_Dlim {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (ℓ : ℤ) :
    Tendsto (fun X : ℝ => DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ / X) (𝓝[>] (0:ℝ))
      (𝓝 (β ^ ℓ.natAbs * Real.sqrt (r * s))) := by
  have hs2 := vz_s2_pos hβ0 hβ1
  set a : ℝ → ℝ := fun X => Qm β (X * r) / X with ha
  set b : ℝ → ℝ := fun X => Qm β (X * s) / X with hb
  have hat : Tendsto a (𝓝[>] (0:ℝ)) (𝓝 (r / sPow β 2)) := vz_Qr hβ0 hβ1 hr
  have hbt : Tendsto b (𝓝[>] (0:ℝ)) (𝓝 (s / sPow β 2)) := vz_Qr hβ0 hβ1 hs
  have hq : ∀ X : ℝ, 0 < X → 0 < Qm β (X * r) ∧ 0 < Qm β (X * s) := fun X hX =>
    ⟨(vs_Qm hβ0 hβ1 (mul_pos hX hr)).1, (vs_Qm hβ0 hβ1 (mul_pos hX hs)).1⟩
  have hab : Tendsto (fun X => Real.sqrt (a X * b X)) (𝓝[>] (0:ℝ))
      (𝓝 (Real.sqrt (r * s) / sPow β 2)) := by
    have := (Real.continuous_sqrt.tendsto _).comp (hat.mul hbt)
    have e : Real.sqrt (r / sPow β 2 * (s / sPow β 2)) = Real.sqrt (r * s) / sPow β 2 := by
      rw [show r / sPow β 2 * (s / sPow β 2) = (r * s) / sPow β 2 ^ 2 by ring,
        Real.sqrt_div (mul_pos hr hs).le, Real.sqrt_sq hs2.le]
    rw [e] at this
    exact this
  -- main term
  set Lm : ℝ → ℝ := fun X => β ^ ℓ.natAbs * sPow β 2 * Real.sqrt (a X * b X) with hLm
  have hLmt : Tendsto Lm (𝓝[>] (0:ℝ)) (𝓝 (β ^ ℓ.natAbs * Real.sqrt (r * s))) := by
    have := hab.const_mul (β ^ ℓ.natAbs * sPow β 2)
    have e : β ^ ℓ.natAbs * sPow β 2 * (Real.sqrt (r * s) / sPow β 2) =
        β ^ ℓ.natAbs * Real.sqrt (r * s) := by field_simp
    rw [e] at this
    exact this
  -- error term
  set er : ℝ → ℝ := fun X => Lm X - DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ / X with her
  have hbd : ∀ X : ℝ, 0 < X → 0 ≤ er X ∧ er X ≤ 3 * sPow β 4 * (Real.sqrt (a X * b X) * (X * (a X + b X))) := by
    intro X hX
    obtain ⟨h1, h2⟩ := hq X hX
    obtain ⟨hlo, hhi⟩ := vz_D_approx hβ0 hβ1 h1.le h2.le ℓ
    have hsq : Real.sqrt (Qm β (X * r) * Qm β (X * s)) = X * Real.sqrt (a X * b X) := by
      have : Qm β (X * r) * Qm β (X * s) = X ^ 2 * (a X * b X) := by
        simp only [ha, hb]; field_simp
      rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hX.le]
    have hsum : Qm β (X * r) + Qm β (X * s) = X * (a X + b X) := by
      simp only [ha, hb]; field_simp
    have e : er X = (β ^ ℓ.natAbs * Real.sqrt (Qm β (X * r) * Qm β (X * s)) * sPow β 2 -
        DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ) / X := by
      simp only [her, hLm, hsq]; field_simp
    rw [e]
    refine ⟨div_nonneg hlo hX.le, ?_⟩
    rw [div_le_iff₀ hX]
    refine hhi.trans (le_of_eq ?_)
    rw [hsq, hsum]; ring
  have hert : Tendsto er (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hX0 : Tendsto (fun X : ℝ => X) (𝓝[>] (0:ℝ)) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
      (continuous_id.tendsto 0)
    have h1 := (hab.mul (hX0.mul (hat.add hbt))).const_mul (3 * sPow β 4)
    rw [zero_mul, mul_zero, mul_zero] at h1
    refine squeeze_zero' ?_ ?_ h1
    · filter_upwards [self_mem_nhdsWithin] with X hX using (hbd X hX).1
    · filter_upwards [self_mem_nhdsWithin] with X hX using (hbd X hX).2
  have := hLmt.sub hert
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards with X
  simp only [her]; ring


private lemma vz_T_hom {α X u v : ℝ} (hX : 0 < X) (hu : 0 < u) (hv : 0 < v) :
    profT α (X * u) (X * v) = X * profT α u v := by
  unfold profT
  by_cases h : u = v
  · subst h
    simp only [if_true]
    ring
  · have h' : ¬ (X * u = X * v) := fun h2 => h (mul_left_cancel₀ hX.ne' h2)
    simp only [if_neg h, if_neg h']
    have hXa : 0 < X ^ α := Real.rpow_pos_of_pos hX α
    rw [Real.mul_rpow hX.le hu.le, Real.mul_rpow hX.le hv.le]
    have : (X ^ α * v ^ α * (X * u) - X ^ α * u ^ α * (X * v)) =
        X ^ α * (X * (v ^ α * u - u ^ α * v)) := by ring
    rw [this, show X ^ α * v ^ α - X ^ α * u ^ α = X ^ α * (v ^ α - u ^ α) by ring,
      mul_div_mul_left _ _ hXa.ne', mul_div_assoc]

private lemma vz_zeta_scale {α X r : ℝ} (hα : 0 < α) (hX : 0 < X) (hr : 0 < r) :
    profZeta α X (X * r) = r ^ α / (1 + r ^ α) := by
  unfold profZeta
  have hXa : 0 < X ^ α := Real.rpow_pos_of_pos hX α
  rw [Real.mul_rpow hX.le hr.le]
  field_simp

private lemma vz_sigma {α r : ℝ} (hα : 0 < α) (hr : 0 < r) :
    Real.sqrt (r ^ α / (1 + r ^ α) * (1 - r ^ α / (1 + r ^ α))) = r ^ (α / 2) / (1 + r ^ α) := by
  have hra : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  have e1 : r ^ α / (1 + r ^ α) * (1 - r ^ α / (1 + r ^ α)) = (r ^ (α / 2) / (1 + r ^ α)) ^ 2 := by
    rw [div_pow, vs_sq_half hr.le]
    field_simp
    ring
  rw [e1, Real.sqrt_sq (by positivity)]

private lemma vz_theta_lim {α β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun X : ℝ => X * r * profTheta α β (X * r)) (𝓝[>] (0:ℝ)) (𝓝 α) := by
  have hE := lem_app_pl_weights_i_E hβ0.le hβ1
  have hne : ∀ᶠ m : ℝ in 𝓝[>] (0:ℝ), m ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with m hm
    exact (show (0:ℝ) < m from hm).ne'
  have h2 := (isEquivalent_iff_tendsto_one hne).1 hE
  have h3 : Tendsto (fun m : ℝ => m / Efun β m) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have := h2.inv₀ one_ne_zero
    rw [inv_one] at this
    refine this.congr' ?_
    filter_upwards with m
    simp [Pi.div_apply]
  have h4 := ((h3.comp (vz_mul_tendsto hr)).add_const (α - 1))
  rw [show (1:ℝ) + (α - 1) = α by ring] at h4
  refine h4.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with X hX
  have hX0 : (0:ℝ) < X := hX
  have hXr : X * r ≠ 0 := (mul_pos hX0 hr).ne'
  simp only [Function.comp, profTheta]
  rw [mul_add, mul_one_div]
  congr 1
  field_simp


open Muon.DetEquiv ProbabilityTheory in
private lemma vz_Delta_lim {α β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) (ℓ : ℤ) :
    Tendsto (fun X : ℝ => profDelta α β ℓ (X * r) (X * s)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hat := vz_Qr hβ0 hβ1 hr
  have hbt := vz_Qr hβ0 hβ1 hs
  have hX0 : Tendsto (fun X : ℝ => X) (𝓝[>] (0:ℝ)) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 0)
  set a : ℝ → ℝ := fun X => Qm β (X * r) / X with ha
  set b : ℝ → ℝ := fun X => Qm β (X * s) / X with hb
  set bound : ℝ → ℝ := fun X => X * |profT α r s| * (3 * sPow β 4) * (a X * b X) / (r * s) with hbound
  have hbt0 : Tendsto bound (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have := (((hX0.mul_const |profT α r s|).mul_const (3 * sPow β 4)).mul (hat.mul hbt)).div_const (r * s)
    simp only [zero_mul, zero_div] at this
    exact this
  have hmain : Tendsto (fun X : ℝ => profT α (X * r) (X * s) *
      MLag β (Qm β (X * r)) (Qm β (X * s)) ℓ / ((X * r) * (X * s))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbt0
    filter_upwards [self_mem_nhdsWithin] with X hX
    have hX0' : (0:ℝ) < X := hX
    obtain ⟨hq1, -⟩ := vs_Qm hβ0 hβ1 (mul_pos hX0' hr)
    obtain ⟨hq2, -⟩ := vs_Qm hβ0 hβ1 (mul_pos hX0' hs)
    obtain ⟨hM0, hM1⟩ := vz_M_le hβ0 hβ1 hq1.le hq2.le ℓ
    rw [vz_T_hom hX0' hr hs]
    have hq1e : Qm β (X * r) = X * a X := by simp only [ha]; field_simp
    have hq2e : Qm β (X * s) = X * b X := by simp only [hb]; field_simp
    have hab0 : 0 ≤ a X * b X := by
      have : 0 ≤ a X := by simp only [ha]; exact div_nonneg hq1.le hX0'.le
      have : 0 ≤ b X := by simp only [hb]; exact div_nonneg hq2.le hX0'.le
      positivity
    have huv : 0 < (X * r) * (X * s) := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_of_pos hX0', abs_of_pos huv,
      abs_of_nonneg hM0, div_le_iff₀ huv]
    simp only [hbound]
    have hM2 : MLag β (Qm β (X * r)) (Qm β (X * s)) ℓ ≤ 3 * sPow β 4 * (X ^ 2 * (a X * b X)) := by
      refine hM1.trans (le_of_eq ?_)
      rw [hq1e, hq2e]; ring
    have h1 : X * |profT α r s| * MLag β (Qm β (X * r)) (Qm β (X * s)) ℓ ≤
        X * |profT α r s| * (3 * sPow β 4 * (X ^ 2 * (a X * b X))) :=
      mul_le_mul_of_nonneg_left hM2 (by positivity)
    refine h1.trans (le_of_eq ?_)
    field_simp
  have := hmain.const_sub 1
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards with X
  rfl


/-- Scaled algebra: for `X > 0`, the rescaled lag integrand factors. -/
private lemma vz_scaled_eq {α β : ℝ} (hα0 : 0 < α) {X r s : ℝ} (hX0 : 0 < X) (hr : 0 < r)
    (hs : 0 < s) (ℓ : ℤ) :
    X ^ 2 *
      (Real.sqrt (profZeta α X (X * r) * (1 - profZeta α X (X * r)) *
              (profZeta α X (X * s) * (1 - profZeta α X (X * s)))) / Real.sqrt ((X * r) * (X * s)) *
        (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ * profTheta α β (X * r) * profTheta α β (X * s) /
          profDelta α β ℓ (X * r) (X * s))) =
    (r ^ (α / 2) / (1 + r ^ α)) * (s ^ (α / 2) / (1 + s ^ α)) / (Real.sqrt (r * s) * (r * s)) *
      ((X * r * profTheta α β (X * r) * (X * s * profTheta α β (X * s)) *
        (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ / X)) / profDelta α β ℓ (X * r) (X * s)) := by
  have hrs : 0 < Real.sqrt (r * s) := Real.sqrt_pos.2 (mul_pos hr hs)
  rw [vz_zeta_scale hα0 hX0 hr, vz_zeta_scale hα0 hX0 hs]
  have hz : ∀ t : ℝ, 0 < t → 0 ≤ t ^ α / (1 + t ^ α) * (1 - t ^ α / (1 + t ^ α)) := by
    intro t ht
    have h1 := Real.rpow_pos_of_pos ht α
    have : t ^ α / (1 + t ^ α) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have : 0 < t ^ α / (1 + t ^ α) := by positivity
    nlinarith
  have hsq : Real.sqrt (r ^ α / (1 + r ^ α) * (1 - r ^ α / (1 + r ^ α)) *
      (s ^ α / (1 + s ^ α) * (1 - s ^ α / (1 + s ^ α)))) =
      r ^ (α / 2) / (1 + r ^ α) * (s ^ (α / 2) / (1 + s ^ α)) := by
    rw [Real.sqrt_mul (hz r hr), vz_sigma hα0 hr, vz_sigma hα0 hs]
  have hsq2 : Real.sqrt ((X * r) * (X * s)) = X * Real.sqrt (r * s) := by
    rw [show (X * r) * (X * s) = X ^ 2 * (r * s) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hX0.le]
  rw [hsq, hsq2]
  have h1 : (0:ℝ) < 1 + r ^ α := by have := Real.rpow_pos_of_pos hr α; linarith
  have h2 : (0:ℝ) < 1 + s ^ α := by have := Real.rpow_pos_of_pos hs α; linarith
  field_simp

open Muon.DetEquiv ProbabilityTheory in
private lemma vz_pt_lim {α β : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ℓ : ℤ) :
    Tendsto (fun X : ℝ => X ^ 2 *
      (Real.sqrt (profZeta α X (X * r) * (1 - profZeta α X (X * r)) *
              (profZeta α X (X * s) * (1 - profZeta α X (X * s)))) / Real.sqrt ((X * r) * (X * s)) *
        (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ * profTheta α β (X * r) * profTheta α β (X * s) /
          profDelta α β ℓ (X * r) (X * s)))) (𝓝[>] (0:ℝ))
      (𝓝 (β ^ ℓ.natAbs * ((α * r ^ (α / 2 - 1) / (1 + r ^ α)) * (α * s ^ (α / 2 - 1) / (1 + s ^ α))))) := by
  have hrs : 0 < Real.sqrt (r * s) := Real.sqrt_pos.2 (mul_pos hr hs)
  have hL := ((((vz_theta_lim (α := α) hβ0 hβ1 hr).mul (vz_theta_lim (α := α) hβ0 hβ1 hs)).mul
    (vz_Dlim hβ0 hβ1 hr hs ℓ)).div (vz_Delta_lim (α := α) hβ0 hβ1 hr hs ℓ) one_ne_zero).const_mul
    ((r ^ (α / 2) / (1 + r ^ α)) * (s ^ (α / 2) / (1 + s ^ α)) / (Real.sqrt (r * s) * (r * s)))
  have e : (r ^ (α / 2) / (1 + r ^ α)) * (s ^ (α / 2) / (1 + s ^ α)) / (Real.sqrt (r * s) * (r * s)) *
      (α * α * (β ^ ℓ.natAbs * Real.sqrt (r * s)) / 1) =
      β ^ ℓ.natAbs * ((α * r ^ (α / 2 - 1) / (1 + r ^ α)) * (α * s ^ (α / 2 - 1) / (1 + s ^ α))) := by
    rw [Real.rpow_sub_one hr.ne', Real.rpow_sub_one hs.ne']
    have h1 : (0:ℝ) < 1 + r ^ α := by have := Real.rpow_pos_of_pos hr α; linarith
    have h2 : (0:ℝ) < 1 + s ^ α := by have := Real.rpow_pos_of_pos hs α; linarith
    field_simp
  rw [e] at hL
  refine hL.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with X hX
  have hX0 : (0:ℝ) < X := hX
  rw [vz_scaled_eq hα0 hX0 hr hs ℓ]
  simp only [Pi.div_apply]


private lemma vz_ab_lim {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Tendsto (fun X : ℝ => Real.sqrt (Qm β (X * r) / X * (Qm β (X * s) / X))) (𝓝[>] (0:ℝ))
      (𝓝 (Real.sqrt (r * s) / sPow β 2)) := by
  have hs2 := vz_s2_pos hβ0 hβ1
  have := (Real.continuous_sqrt.tendsto _).comp ((vz_Qr hβ0 hβ1 hr).mul (vz_Qr hβ0 hβ1 hs))
  have e : Real.sqrt (r / sPow β 2 * (s / sPow β 2)) = Real.sqrt (r * s) / sPow β 2 := by
    rw [show r / sPow β 2 * (s / sPow β 2) = (r * s) / sPow β 2 ^ 2 by ring,
      Real.sqrt_div (mul_pos hr hs).le, Real.sqrt_sq hs2.le]
  rw [e] at this
  exact this

open Muon.DetEquiv ProbabilityTheory in
private lemma vz_term_bd {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {X r s : ℝ}
    (hX0 : 0 < X) (hr : 0 < r) (hs : 0 < s) (ℓ : ℤ) :
    0 ≤ X ^ 2 *
      (Real.sqrt (profZeta α X (X * r) * (1 - profZeta α X (X * r)) *
              (profZeta α X (X * s) * (1 - profZeta α X (X * s)))) / Real.sqrt ((X * r) * (X * s)) *
        (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ * profTheta α β (X * r) * profTheta α β (X * s) /
          profDelta α β ℓ (X * r) (X * s))) ∧
    X ^ 2 *
      (Real.sqrt (profZeta α X (X * r) * (1 - profZeta α X (X * r)) *
              (profZeta α X (X * s) * (1 - profZeta α X (X * s)))) / Real.sqrt ((X * r) * (X * s)) *
        (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ * profTheta α β (X * r) * profTheta α β (X * s) /
          profDelta α β ℓ (X * r) (X * s))) ≤
    ((r ^ (α / 2) / (1 + r ^ α)) * (s ^ (α / 2) / (1 + s ^ α)) / (Real.sqrt (r * s) * (r * s)) *
      (X * r * profTheta α β (X * r) * (X * s * profTheta α β (X * s)) *
        (α * sPow β 2 * Real.sqrt (Qm β (X * r) / X * (Qm β (X * s) / X))))) * β ^ ℓ.natAbs := by
  have hα0 : 0 < α := by linarith
  rw [vz_scaled_eq hα0 hX0 hr hs ℓ]
  obtain ⟨K, hK0, hK⟩ := vs_theta_bd hα1 hβ0 hβ1
  have hu : 0 < X * r := mul_pos hX0 hr
  have hv : 0 < X * s := mul_pos hX0 hs
  obtain ⟨hq1, -⟩ := vs_Qm hβ0 hβ1 hu
  obtain ⟨hq2, -⟩ := vs_Qm hβ0 hβ1 hv
  have hD0 := vs_DLag_nonneg hβ0 hβ1 hq1.le hq2.le ℓ
  have hD1 := (vz_D_approx hβ0 hβ1 hq1.le hq2.le ℓ).1
  have hΔ := vs_Delta_ge hα1 hβ0 hβ1 hu hv ℓ
  have hΔ0 : 0 < profDelta α β ℓ (X * r) (X * s) := lt_of_lt_of_le (by positivity) hΔ
  have hθ1 := (hK (X * r) hu).1
  have hθ2 := (hK (X * s) hv).1
  have hrs : 0 < Real.sqrt (r * s) := Real.sqrt_pos.2 (mul_pos hr hs)
  have hra := Real.rpow_pos_of_pos hr (α / 2)
  have hsa := Real.rpow_pos_of_pos hs (α / 2)
  have hra' := Real.rpow_pos_of_pos hr α
  have hsa' := Real.rpow_pos_of_pos hs α
  have hC0 : 0 ≤ (r ^ (α / 2) / (1 + r ^ α)) * (s ^ (α / 2) / (1 + s ^ α)) /
      (Real.sqrt (r * s) * (r * s)) := by positivity
  set D := DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ with hD
  set Δ := profDelta α β ℓ (X * r) (X * s) with hΔd
  set T1 := X * r * profTheta α β (X * r) with hT1
  set T2 := X * s * profTheta α β (X * s) with hT2
  have hT1n : 0 ≤ T1 := by positivity
  have hT2n : 0 ≤ T2 := by positivity
  have hDX : D / X ≤ β ^ ℓ.natAbs * (sPow β 2 * Real.sqrt (Qm β (X * r) / X * (Qm β (X * s) / X))) := by
    have hsq : Real.sqrt (Qm β (X * r) * Qm β (X * s)) =
        X * Real.sqrt (Qm β (X * r) / X * (Qm β (X * s) / X)) := by
      have : Qm β (X * r) * Qm β (X * s) = X ^ 2 * (Qm β (X * r) / X * (Qm β (X * s) / X)) := by
        field_simp
      rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hX0.le]
    rw [div_le_iff₀ hX0]
    have : D ≤ β ^ ℓ.natAbs * Real.sqrt (Qm β (X * r) * Qm β (X * s)) * sPow β 2 := by linarith
    rw [hsq] at this
    nlinarith
  have hDX0 : 0 ≤ D / X := div_nonneg hD0 hX0.le
  have hinvΔ : 1 / Δ ≤ α := by
    rw [div_le_iff₀ hΔ0]
    have := mul_le_mul_of_nonneg_left hΔ hα0.le
    rw [mul_one_div_cancel hα0.ne'] at this
    nlinarith
  have hsum0 : 0 ≤ T1 * T2 * (D / X) / Δ := by positivity
  refine ⟨by positivity, ?_⟩
  have e : T1 * T2 * (D / X) / Δ = T1 * T2 * (D / X) * (1 / Δ) := by ring
  have hbnd : T1 * T2 * (D / X) / Δ ≤ T1 * T2 * (α * sPow β 2 * Real.sqrt (Qm β (X * r) / X *
      (Qm β (X * s) / X))) * β ^ ℓ.natAbs := by
    rw [e]
    have hs2 := vz_s2_pos hβ0 hβ1
    calc T1 * T2 * (D / X) * (1 / Δ) ≤ T1 * T2 * (β ^ ℓ.natAbs * (sPow β 2 *
          Real.sqrt (Qm β (X * r) / X * (Qm β (X * s) / X)))) * α := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hDX (by positivity)) hinvΔ (by positivity) (by positivity)
      _ = _ := by ring
  calc _ ≤ _ := mul_le_mul_of_nonneg_left hbnd hC0
    _ = _ := by ring


open Muon.DetEquiv ProbabilityTheory in
private lemma vz_sum_lim {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    Tendsto (fun X : ℝ => ∑' ℓ : ℤ, X ^ 2 *
      (Real.sqrt (profZeta α X (X * r) * (1 - profZeta α X (X * r)) *
              (profZeta α X (X * s) * (1 - profZeta α X (X * s)))) / Real.sqrt ((X * r) * (X * s)) *
        (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ * profTheta α β (X * r) * profTheta α β (X * s) /
          profDelta α β ℓ (X * r) (X * s)))) (𝓝[>] (0:ℝ))
      (𝓝 (1 / sPow β 2 * ((α * r ^ (α / 2 - 1) / (1 + r ^ α)) * (α * s ^ (α / 2 - 1) / (1 + s ^ α))))) := by
  have hα0 : 0 < α := by linarith
  have hs2 := vz_s2_pos hβ0 hβ1
  set C0 : ℝ := (r ^ (α / 2) / (1 + r ^ α)) * (s ^ (α / 2) / (1 + s ^ α)) /
    (Real.sqrt (r * s) * (r * s)) with hC0
  set Bd : ℝ → ℝ := fun X => C0 * (X * r * profTheta α β (X * r) * (X * s * profTheta α β (X * s)) *
        (α * sPow β 2 * Real.sqrt (Qm β (X * r) / X * (Qm β (X * s) / X)))) with hBd
  have hBdt : Tendsto Bd (𝓝[>] (0:ℝ)) (𝓝 (C0 * (α * α * (α * sPow β 2 * (Real.sqrt (r * s) / sPow β 2))))) := by
    exact (((vz_theta_lim (α := α) hβ0 hβ1 hr).mul (vz_theta_lim (α := α) hβ0 hβ1 hs)).mul
      ((vz_ab_lim hβ0 hβ1 hr hs).const_mul (α * sPow β 2))).const_mul C0
  set L0 : ℝ := C0 * (α * α * (α * sPow β 2 * (Real.sqrt (r * s) / sPow β 2))) with hL0
  have hev : ∀ᶠ X in 𝓝[>] (0:ℝ), Bd X < L0 + 1 :=
    hBdt.eventually (gt_mem_nhds (by linarith))
  have hsum := vz_beta_sum hβ0 hβ1
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0:ℝ))
    (f := fun (X : ℝ) (ℓ : ℤ) => X ^ 2 *
      (Real.sqrt (profZeta α X (X * r) * (1 - profZeta α X (X * r)) *
              (profZeta α X (X * s) * (1 - profZeta α X (X * s)))) / Real.sqrt ((X * r) * (X * s)) *
        (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ * profTheta α β (X * r) * profTheta α β (X * s) /
          profDelta α β ℓ (X * r) (X * s))))
    (g := fun ℓ : ℤ => β ^ ℓ.natAbs * ((α * r ^ (α / 2 - 1) / (1 + r ^ α)) * (α * s ^ (α / 2 - 1) / (1 + s ^ α))))
    (bound := fun ℓ : ℤ => (L0 + 1) * β ^ ℓ.natAbs)
    (hsum.summable.mul_left _)
    (fun ℓ => vz_pt_lim hα0 hβ0 hβ1 hr hs ℓ)
    (by
      filter_upwards [hev, self_mem_nhdsWithin] with X hX hX0 ℓ
      have hX0' : (0:ℝ) < X := hX0
      obtain ⟨h1, h2⟩ := vz_term_bd hα1 hβ0 hβ1 hX0' hr hs ℓ
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      refine h2.trans ?_
      have hb0 : 0 ≤ β ^ ℓ.natAbs := by positivity
      have : Bd X ≤ L0 + 1 := hX.le
      calc _ = Bd X * β ^ ℓ.natAbs := rfl
        _ ≤ _ := mul_le_mul_of_nonneg_right this hb0)
  rw [tsum_mul_right, hsum.tsum_eq] at hlim
  exact hlim


private lemma vz_g_bd {α K X r θ : ℝ} (hα0 : 0 < α) (hX0 : 0 < X) (hX1 : X ≤ 1) (hr : 0 < r)
    (hθ0 : 0 < θ) (hθ : θ ≤ K / min (X * r) 1) :
    r ^ (α / 2) / (1 + r ^ α) * (X * r * θ) * min (Real.sqrt (X * r)) 1 /
        (Real.sqrt X * (r * Real.sqrt r)) ≤
      if r ≤ 1 then K * r ^ (α / 2 - 1) else K * r ^ (-((α + 1) / 2)) := by
  have hu : 0 < X * r := mul_pos hX0 hr
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hX0
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hra := Real.rpow_pos_of_pos hr α
  have hrh := Real.rpow_pos_of_pos hr (α / 2)
  have hK0 : 0 ≤ K := by
    have h1 : 0 < min (X * r) 1 := lt_min hu one_pos
    have := hθ0.le.trans hθ
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => by linarith [h.2])
  have hσ : r ^ (α / 2) / (1 + r ^ α) ≤ r ^ (α / 2) := div_le_self hrh.le (by linarith)
  have hσ' : r ^ (α / 2) / (1 + r ^ α) ≤ r ^ (-(α / 2)) := by
    rw [Real.rpow_neg hr.le]
    have : r ^ (α / 2) / (1 + r ^ α) ≤ r ^ (α / 2) / r ^ α :=
      div_le_div_of_nonneg_left hrh.le hra (by linarith)
    refine this.trans (le_of_eq ?_)
    have : r ^ α = r ^ (α / 2) * r ^ (α / 2) := by
      rw [← Real.rpow_add hr]; congr 1; ring
    rw [this]; field_simp
  have hσ0 : 0 ≤ r ^ (α / 2) / (1 + r ^ α) := by positivity
  have hsqu : Real.sqrt (X * r) = Real.sqrt X * Real.sqrt r := Real.sqrt_mul hX0.le r
  by_cases hu1 : X * r ≤ 1
  · have hmin : min (X * r) 1 = X * r := min_eq_left hu1
    rw [hmin] at hθ
    have hs1 : Real.sqrt (X * r) ≤ 1 := by rw [Real.sqrt_le_one]; exact hu1
    rw [min_eq_left hs1]
    have hT : X * r * θ ≤ K := by
      calc X * r * θ ≤ X * r * (K / (X * r)) := mul_le_mul_of_nonneg_left hθ hu.le
        _ = K := by field_simp
    have e : r ^ (α / 2) / (1 + r ^ α) * (X * r * θ) * Real.sqrt (X * r) /
        (Real.sqrt X * (r * Real.sqrt r)) =
        r ^ (α / 2) / (1 + r ^ α) * (X * r * θ) / r := by
      rw [hsqu]; field_simp
    rw [e]
    have h1 : r ^ (α / 2) / (1 + r ^ α) * (X * r * θ) / r ≤ r ^ (α / 2) / (1 + r ^ α) * K / r := by
      gcongr
    refine h1.trans ?_
    by_cases hr1 : r ≤ 1
    · rw [if_pos hr1, Real.rpow_sub_one hr.ne']
      have : r ^ (α / 2) / (1 + r ^ α) * K / r ≤ r ^ (α / 2) * K / r := by gcongr
      refine this.trans (le_of_eq ?_)
      field_simp
    · rw [if_neg hr1]
      have hr1' : 1 ≤ r := (not_le.1 hr1).le
      have : r ^ (α / 2) / (1 + r ^ α) * K / r ≤ r ^ (-(α / 2)) * K / r := by gcongr
      refine this.trans ?_
      have e2 : r ^ (-(α / 2)) * K / r = K * r ^ (-(α / 2) - 1) := by
        rw [Real.rpow_sub_one hr.ne']; field_simp
      rw [e2]
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hr1' ?_) hK0
      linarith
  · have hu1' : 1 < X * r := not_le.1 hu1
    have hmin : min (X * r) 1 = 1 := min_eq_right hu1'.le
    rw [hmin, div_one] at hθ
    have hs1 : 1 ≤ Real.sqrt (X * r) := by rw [Real.one_le_sqrt]; exact hu1'.le
    rw [min_eq_right hs1]
    have hr1 : 1 < r := by nlinarith
    rw [if_neg (not_le.2 hr1)]
    have e : r ^ (α / 2) / (1 + r ^ α) * (X * r * θ) * 1 / (Real.sqrt X * (r * Real.sqrt r)) =
        r ^ (α / 2) / (1 + r ^ α) * θ * (Real.sqrt X / Real.sqrt r) := by
      have hXs : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
      field_simp
      rw [Real.sq_sqrt hX0.le]
    rw [e]
    have hsX1 : Real.sqrt X ≤ 1 := by rw [Real.sqrt_le_one]; exact hX1
    have h2 : Real.sqrt X / Real.sqrt r ≤ 1 / Real.sqrt r :=
      div_le_div_of_nonneg_right hsX1 hsr.le
    have h3 : r ^ (α / 2) / (1 + r ^ α) * θ * (Real.sqrt X / Real.sqrt r) ≤
        r ^ (-(α / 2)) * K * (1 / Real.sqrt r) := by
      refine mul_le_mul (mul_le_mul hσ' hθ hθ0.le (by positivity)) h2 (by positivity) (by positivity)
    refine h3.trans (le_of_eq ?_)
    have e2 : r ^ (-((α + 1) / 2)) = r ^ (-(α / 2)) * (1 / Real.sqrt r) := by
      rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hr.le, ← Real.rpow_add hr]
      congr 1; ring
    rw [e2]; ring


open Muon.DetEquiv ProbabilityTheory in
private lemma vz_tsum_bd {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧ ∀ X r s : ℝ, 0 < X → X ≤ 1 → 0 < r → 0 < s →
      Summable (fun ℓ : ℤ => X ^ 2 *
        (Real.sqrt (profZeta α X (X * r) * (1 - profZeta α X (X * r)) *
              (profZeta α X (X * s) * (1 - profZeta α X (X * s)))) / Real.sqrt ((X * r) * (X * s)) *
        (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ * profTheta α β (X * r) * profTheta α β (X * s) /
          profDelta α β ℓ (X * r) (X * s)))) ∧
      ∑' ℓ : ℤ, X ^ 2 *
        (Real.sqrt (profZeta α X (X * r) * (1 - profZeta α X (X * r)) *
              (profZeta α X (X * s) * (1 - profZeta α X (X * s)))) / Real.sqrt ((X * r) * (X * s)) *
        (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ * profTheta α β (X * r) * profTheta α β (X * s) /
          profDelta α β ℓ (X * r) (X * s))) ≤
      α * C * ((if r ≤ 1 then K * r ^ (α / 2 - 1) else K * r ^ (-((α + 1) / 2))) *
        (if s ≤ 1 then K * s ^ (α / 2 - 1) else K * s ^ (-((α + 1) / 2)))) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨K, hK0, hK⟩ := vs_theta_bd hα1 hβ0 hβ1
  obtain ⟨C, hC0, hC⟩ := vs_D_bd hβ0 hβ1
  refine ⟨K, C, hK0, hC0, fun X r s hX0 hX1 hr hs => ?_⟩
  have hu : 0 < X * r := mul_pos hX0 hr
  have hv : 0 < X * s := mul_pos hX0 hs
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hX0
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  obtain ⟨hθ1, hθ1'⟩ := hK (X * r) hu
  obtain ⟨hθ2, hθ2'⟩ := hK (X * s) hv
  have hg1 := vz_g_bd (α := α) (K := K) hα0 hX0 hX1 hr hθ1 hθ1'
  have hg2 := vz_g_bd (α := α) (K := K) hα0 hX0 hX1 hs hθ2 hθ2'
  set h1 := (if r ≤ 1 then K * r ^ (α / 2 - 1) else K * r ^ (-((α + 1) / 2))) with hh1
  set h2 := (if s ≤ 1 then K * s ^ (α / 2 - 1) else K * s ^ (-((α + 1) / 2))) with hh2
  have hw1 : 0 < min (Real.sqrt (X * r)) 1 := lt_min (Real.sqrt_pos.2 hu) one_pos
  have hw2 : 0 < min (Real.sqrt (X * s)) 1 := lt_min (Real.sqrt_pos.2 hv) one_pos
  have hra := Real.rpow_pos_of_pos hr (α / 2)
  have hsa := Real.rpow_pos_of_pos hs (α / 2)
  have hra' := Real.rpow_pos_of_pos hr α
  have hsa' := Real.rpow_pos_of_pos hs α
  have hh1n : 0 ≤ h1 := by
    simp only [hh1]; split_ifs <;> positivity
  have hh2n : 0 ≤ h2 := by
    simp only [hh2]; split_ifs <;> positivity
  -- finite-sum bound
  have hfin : ∀ S : Finset ℤ, ∑ ℓ ∈ S, X ^ 2 *
      (Real.sqrt (profZeta α X (X * r) * (1 - profZeta α X (X * r)) *
              (profZeta α X (X * s) * (1 - profZeta α X (X * s)))) / Real.sqrt ((X * r) * (X * s)) *
        (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ * profTheta α β (X * r) * profTheta α β (X * s) /
          profDelta α β ℓ (X * r) (X * s))) ≤ α * C * (h1 * h2) := by
    intro S
    set C0 : ℝ := (r ^ (α / 2) / (1 + r ^ α)) * (s ^ (α / 2) / (1 + s ^ α)) /
      (Real.sqrt (r * s) * (r * s)) with hC0def
    set T1 := X * r * profTheta α β (X * r) with hT1
    set T2 := X * s * profTheta α β (X * s) with hT2
    have hC0n : 0 ≤ C0 := by positivity
    have hT1n : 0 ≤ T1 := by positivity
    have hT2n : 0 ≤ T2 := by positivity
    have hterm : ∀ ℓ ∈ S, X ^ 2 *
      (Real.sqrt (profZeta α X (X * r) * (1 - profZeta α X (X * r)) *
              (profZeta α X (X * s) * (1 - profZeta α X (X * s)))) / Real.sqrt ((X * r) * (X * s)) *
        (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ * profTheta α β (X * r) * profTheta α β (X * s) /
          profDelta α β ℓ (X * r) (X * s))) ≤
        C0 * (T1 * T2 * (α * DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ / X)) := by
      intro ℓ _
      rw [vz_scaled_eq hα0 hX0 hr hs ℓ]
      obtain ⟨hq1, -⟩ := vs_Qm hβ0 hβ1 hu
      obtain ⟨hq2, -⟩ := vs_Qm hβ0 hβ1 hv
      have hD0 := vs_DLag_nonneg hβ0 hβ1 hq1.le hq2.le ℓ
      have hΔ := vs_Delta_ge hα1 hβ0 hβ1 hu hv ℓ
      have hΔ0 : 0 < profDelta α β ℓ (X * r) (X * s) := lt_of_lt_of_le (by positivity) hΔ
      refine mul_le_mul_of_nonneg_left ?_ hC0n
      have hinvΔ : 1 / profDelta α β ℓ (X * r) (X * s) ≤ α := by
        rw [div_le_iff₀ hΔ0]
        have := mul_le_mul_of_nonneg_left hΔ hα0.le
        rw [mul_one_div_cancel hα0.ne'] at this
        nlinarith
      have hDX0 : 0 ≤ DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ / X := div_nonneg hD0 hX0.le
      have e : T1 * T2 * (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ / X) /
          profDelta α β ℓ (X * r) (X * s) = T1 * T2 * (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ / X) *
          (1 / profDelta α β ℓ (X * r) (X * s)) := by ring
      change T1 * T2 * (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ / X) /
          profDelta α β ℓ (X * r) (X * s) ≤ _
      rw [e]
      calc _ ≤ T1 * T2 * (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ / X) * α :=
            mul_le_mul_of_nonneg_left hinvΔ (by positivity)
        _ = _ := by ring
    obtain ⟨hq1, -⟩ := vs_Qm hβ0 hβ1 hu
    obtain ⟨hq2, -⟩ := vs_Qm hβ0 hβ1 hv
    have hDS := hC (X * r) (X * s) hu hv S
    calc _ ≤ ∑ ℓ ∈ S, C0 * (T1 * T2 * (α * DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ / X)) :=
          Finset.sum_le_sum hterm
      _ = C0 * (T1 * T2 * (α * (∑ ℓ ∈ S, DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ) / X)) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum]
      _ ≤ C0 * (T1 * T2 * (α * (C * min (Real.sqrt (X * r)) 1 * min (Real.sqrt (X * s)) 1) / X)) := by
          gcongr
      _ = α * C * ((r ^ (α / 2) / (1 + r ^ α) * (X * r * profTheta α β (X * r)) *
            min (Real.sqrt (X * r)) 1 / (Real.sqrt X * (r * Real.sqrt r))) *
          (s ^ (α / 2) / (1 + s ^ α) * (X * s * profTheta α β (X * s)) *
            min (Real.sqrt (X * s)) 1 / (Real.sqrt X * (s * Real.sqrt s)))) := by
          simp only [hC0def, hT1, hT2]
          rw [Real.sqrt_mul hr.le]
          have hX2 : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
          have h1' : (0:ℝ) < 1 + r ^ α := by linarith
          have h2' : (0:ℝ) < 1 + s ^ α := by linarith
          generalize Real.sqrt X = sx at *
          subst hX2
          field_simp
      _ ≤ α * C * (h1 * h2) := by
          have hga : 0 ≤ r ^ (α / 2) / (1 + r ^ α) * (X * r * profTheta α β (X * r)) *
            min (Real.sqrt (X * r)) 1 / (Real.sqrt X * (r * Real.sqrt r)) := by positivity
          have hgb : 0 ≤ s ^ (α / 2) / (1 + s ^ α) * (X * s * profTheta α β (X * s)) *
            min (Real.sqrt (X * s)) 1 / (Real.sqrt X * (s * Real.sqrt s)) := by positivity
          have : 0 ≤ α * C := by positivity
          exact mul_le_mul_of_nonneg_left (mul_le_mul hg1 hg2 hgb hh1n) this
  have hnn : ∀ ℓ : ℤ, 0 ≤ X ^ 2 *
      (Real.sqrt (profZeta α X (X * r) * (1 - profZeta α X (X * r)) *
              (profZeta α X (X * s) * (1 - profZeta α X (X * s)))) / Real.sqrt ((X * r) * (X * s)) *
        (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ * profTheta α β (X * r) * profTheta α β (X * s) /
          profDelta α β ℓ (X * r) (X * s))) := fun ℓ =>
    (vz_term_bd hα1 hβ0 hβ1 hX0 hr hs ℓ).1
  have hsm := summable_of_sum_le hnn hfin
  exact ⟨hsm, hsm.tsum_le_of_sum_le hfin⟩


private lemma vz_qmp {X : ℝ} (hX : 0 < X) :
    Measure.QuasiMeasurePreserving (fun p : ℝ × ℝ => X • p)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have h := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure (ℝ × ℝ))) hX.ne'
  refine h.restrict ?_
  intro p hp
  simp only [mem_prod, mem_Ioi, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hp ⊢
  exact ⟨mul_pos hX hp.1, mul_pos hX hp.2⟩

open Muon.DetEquiv ProbabilityTheory in
private lemma vz_Phi_meas {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {X : ℝ}
    (hX0 : 0 < X) (hX1 : X ≤ 1) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => ∑' ℓ : ℤ, X ^ 2 *
      (Real.sqrt (profZeta α X (X * p.1) * (1 - profZeta α X (X * p.1)) *
              (profZeta α X (X * p.2) * (1 - profZeta α X (X * p.2)))) /
          Real.sqrt ((X * p.1) * (X * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ * profTheta α β (X * p.1) *
          profTheta α β (X * p.2) / profDelta α β ℓ (X * p.1) (X * p.2))))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  obtain ⟨K, C, hK, hC, hbd⟩ := vz_tsum_bd (α := α) hα1 hβ0 hβ1
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  have hterm : ∀ ℓ : ℤ, AEStronglyMeasurable (fun p : ℝ × ℝ => X ^ 2 *
      (Real.sqrt (profZeta α X (X * p.1) * (1 - profZeta α X (X * p.1)) *
              (profZeta α X (X * p.2) * (1 - profZeta α X (X * p.2)))) /
          Real.sqrt ((X * p.1) * (X * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ * profTheta α β (X * p.1) *
          profTheta α β (X * p.2) / profDelta α β ℓ (X * p.1) (X * p.2)))) μ := by
    intro ℓ
    have h := (vs_F_meas (α := α) hβ0 hβ1 X ℓ).comp_quasiMeasurePreserving (vz_qmp hX0)
    exact h.const_mul (X ^ 2)
  have hae : ∀ᵐ p ∂μ, 0 < p.1 ∧ 0 < p.2 := vs_ae_pos
  refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ℤ))
    (f := fun (S : Finset ℤ) (p : ℝ × ℝ) => ∑ ℓ ∈ S, X ^ 2 *
      (Real.sqrt (profZeta α X (X * p.1) * (1 - profZeta α X (X * p.1)) *
              (profZeta α X (X * p.2) * (1 - profZeta α X (X * p.2)))) /
          Real.sqrt ((X * p.1) * (X * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ * profTheta α β (X * p.1) *
          profTheta α β (X * p.2) / profDelta α β ℓ (X * p.1) (X * p.2))))
    (fun S => Finset.aestronglyMeasurable_fun_sum S (fun ℓ _ => hterm ℓ)) ?_
  filter_upwards [hae] with p hp
  exact (hbd X p.1 p.2 hX0 hX1 hp.1 hp.2).1.hasSum

private lemma vz_bnd_int {α K : ℝ} (hα1 : 1 < α) :
    Integrable (fun p : ℝ × ℝ => (if p.1 ≤ 1 then K * p.1 ^ (α / 2 - 1) else K * p.1 ^ (-((α + 1) / 2))) *
        (if p.2 ≤ 1 then K * p.2 ^ (α / 2 - 1) else K * p.2 ^ (-((α + 1) / 2))))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have h := vs_k_int (α := α) (K := K) (A := 1) (B := 1) hα1
  have h' : Integrable (fun u : ℝ => if u ≤ 1 then K * u ^ (α / 2 - 1) else K * u ^ (-((α + 1) / 2)))
      (volume.restrict (Ioi (0:ℝ))) := by
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [mul_one]
  exact h'.mul_prod h'


open Muon.DetEquiv ProbabilityTheory in
private lemma vz_G_rep {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {X : ℝ} (hX : 0 < X) :
    profG α β X = (1 / Real.pi ^ 2) *
      ∫ p : ℝ × ℝ, ∑' ℓ : ℤ, X ^ 2 *
        (Real.sqrt (profZeta α X (X * p.1) * (1 - profZeta α X (X * p.1)) *
                (profZeta α X (X * p.2) * (1 - profZeta α X (X * p.2)))) /
            Real.sqrt ((X * p.1) * (X * p.2)) *
          (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ * profTheta α β (X * p.1) *
            profTheta α β (X * p.2) / profDelta α β ℓ (X * p.1) (X * p.2)))
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  obtain ⟨hint, hsum⟩ := vs_finite_all hα1 hβ0 hβ1 X hX
  obtain ⟨K, hK0, hK⟩ := vs_theta_bd hα1 hβ0 hβ1
  obtain ⟨bl, hbl, hbls, hbd⟩ := vs_core hα1 hβ0 hβ1 hX (le_refl X) hK
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  set Fl : ℤ → ℝ × ℝ → ℝ := fun ℓ p =>
    Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2) with hFl
  have hnn : ∀ ℓ, ∀ᵐ p ∂μ, 0 ≤ Fl ℓ p := fun ℓ => by
    filter_upwards [hbd X le_rfl le_rfl ℓ] with p hp using hp.1
  have hI : ∀ ℓ : ℤ, (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
        Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) =
      ∫ p, Fl ℓ p ∂μ := fun ℓ => vs_iter_eq ℓ (hint ℓ)
  have hnorm : Summable (fun ℓ : ℤ => ∫ p, ‖Fl ℓ p‖ ∂μ) := by
    refine hsum.congr fun ℓ => ?_
    rw [hI ℓ]
    refine integral_congr_ae ?_
    filter_upwards [hnn ℓ] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
  have h1 : ∑' ℓ : ℤ, ∫ p, Fl ℓ p ∂μ = ∫ p, ∑' ℓ : ℤ, Fl ℓ p ∂μ :=
    integral_tsum_of_summable_integral_norm hint hnorm
  have h2 : ∫ p, ∑' ℓ : ℤ, Fl ℓ p ∂μ =
      X ^ 2 * ∫ p : ℝ × ℝ, ∑' ℓ : ℤ, Fl ℓ (X • p) ∂μ := by
    rw [vz_rescale hX (fun p => ∑' ℓ : ℤ, Fl ℓ p)]
    field_simp
    rfl
  unfold profG
  rw [tsum_congr hI, h1, h2, ← integral_const_mul]
  congr 2
  funext p
  rw [← tsum_mul_left]
  rfl


/-! ## Private helpers for `lem_app_pl_supervol_iv_gamma` -/

private lemma vg_cont_on {α V : ℝ} (hα : 0 < α) (hV : 0 < V) :
    ContinuousOn (fun t : ℝ => V / (V + t ^ α)) (Set.uIcc 0 1) := by
  apply ContinuousOn.div continuousOn_const
  · exact (continuous_const.add (Real.continuous_rpow_const hα.le)).continuousOn
  · intro t ht
    have ht' : (0:ℝ) ≤ t := (by rwa [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)] at ht : t ∈ Set.Icc (0:ℝ) 1).1
    have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht' α
    exact (by linarith : (0:ℝ) < V + t ^ α).ne'

private lemma vg_ci {α : ℝ} (hα : 0 < α) {G : ℝ → ℝ} (hG : ContinuousOn G (Ici 0)) :
    IntervalIntegrable (fun t : ℝ => G (t ^ α)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  refine hG.comp ((Real.continuous_rpow_const hα.le).continuousOn) ?_
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  exact Real.rpow_nonneg ht.1 α

private lemma vg_K1 {α V W : ℝ} (hα : 0 < α) (hV : 0 < V) (hVW : V ≤ W) :
    V * contS α W ≤ W * contS α V := by
  have hW : 0 < W := lt_of_lt_of_le hV hVW
  unfold contS
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact ((vg_cont_on hα hW).const_smul V).intervalIntegrable
  · exact ((vg_cont_on hα hV).const_smul W).intervalIntegrable
  intro t ht
  have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1 α
  rw [← mul_div_assoc, ← mul_div_assoc]
  have : V * W / (W + t ^ α) ≤ W * V / (V + t ^ α) := by
    rw [mul_comm W V]
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  exact this

private lemma vg_K2 {α V W : ℝ} (hα : 0 < α) (hV : 0 < V) (hVW : V ≤ W) :
    (W - V) * Tcont α W ≤ W * (contS α W - contS α V) := by
  have hW : 0 < W := lt_of_lt_of_le hV hVW
  unfold Tcont
  have hiT : IntervalIntegrable (fun t : ℝ => W * t ^ α / (W + t ^ α) ^ 2) volume 0 1 := by
    have := vg_ci hα (G := fun a => W * a / (W + a) ^ 2) (by
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro a ha
      have : (0:ℝ) ≤ a := ha
      positivity)
    exact this
  have hiS : IntervalIntegrable (fun t : ℝ => W / (W + t ^ α) - V / (V + t ^ α)) volume 0 1 :=
    ((vg_cont_on hα hW).sub (vg_cont_on hα hV)).intervalIntegrable
  have hiS2 : IntervalIntegrable (fun t : ℝ => W * (W / (W + t ^ α) - V / (V + t ^ α))) volume 0 1 :=
    hiS.const_mul W
  have e1 : W * (contS α W - contS α V) = ∫ t in (0:ℝ)..1, W * (W / (W + t ^ α) - V / (V + t ^ α)) := by
    unfold contS
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      (vg_cont_on hα hW).intervalIntegrable (vg_cont_on hα hV).intervalIntegrable]
  rw [e1, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on zero_le_one (hiT.const_mul (W - V)) hiS2
  intro t ht
  have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1 α
  have h1 : 0 < V + t ^ α := by linarith
  have h2 : 0 < W + t ^ α := by linarith
  have e : W * (W / (W + t ^ α) - V / (V + t ^ α)) = W * (W - V) * t ^ α / ((W + t ^ α) * (V + t ^ α)) := by
    field_simp
    ring
  have e2 : (W - V) * (W * t ^ α / (W + t ^ α) ^ 2) = W * (W - V) * t ^ α / (W + t ^ α) ^ 2 := by ring
  rw [e, e2]
  apply div_le_div_of_nonneg_left (by have := sub_nonneg.2 hVW; positivity) (by positivity)
  nlinarith

/-- Facts on `V_α = S_α⁻¹` used below. -/
private lemma vg_V_spec {α p : ℝ} (hα : 0 < α) (hp : p ∈ Ioo (0:ℝ) 1) :
    0 < contV α p ∧ contS α (contV α p) = p := by
  have h : ∃ a ∈ Ioi (0:ℝ), contS α a = p := (def_app_pl_profiles_S_bij hα).2.surjOn hp
  exact ⟨Set.mem_Ioi.1 (Function.invFunOn_mem h), Function.invFunOn_eq h⟩

private lemma vg_V_lt {α p q : ℝ} (hα : 0 < α) (hp : p ∈ Ioo (0:ℝ) 1) (hq : q ∈ Ioo (0:ℝ) 1)
    (hpq : p < q) : contV α p < contV α q := by
  have hp' := vg_V_spec hα hp
  have hq' := vg_V_spec hα hq
  by_contra h
  have := (def_app_pl_profiles_S_bij hα).1.monotoneOn (Set.mem_Ioi.2 hq'.1) (Set.mem_Ioi.2 hp'.1)
    (not_lt.1 h)
  rw [hp'.2, hq'.2] at this
  linarith

private lemma vg_V_mono {α : ℝ} (hα : 0 < α) : MonotoneOn (contV α) (Ioo (0:ℝ) 1) := by
  intro p hp q hq hpq
  rcases hpq.eq_or_lt with h | h
  · rw [h]
  · exact (vg_V_lt hα hp hq h).le

private lemma vg_V_cont {α : ℝ} (hα : 0 < α) : ContinuousOn (contV α) (Ioo (0:ℝ) 1) := by
  intro a ha
  apply ContinuousAt.continuousWithinAt
  have hs : Ioo (0:ℝ) 1 ∈ 𝓝 a := Ioo_mem_nhds ha.1 ha.2
  refine continuousAt_of_monotoneOn_of_image_mem_nhds (vg_V_mono hα) hs ?_
  have himg : contV α '' Ioo (0:ℝ) 1 = Ioi 0 := by
    ext V
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (vg_V_spec hα hp).1
    · intro hV
      have hm : contS α V ∈ Ioo (0:ℝ) 1 := (def_app_pl_profiles_S_bij hα).2.mapsTo hV
      refine ⟨contS α V, hm, ?_⟩
      have h := vg_V_spec hα hm
      exact (def_app_pl_profiles_S_bij hα).1.injOn (Set.mem_Ioi.2 h.1) hV h.2
  rw [himg]
  exact Ioi_mem_nhds (vg_V_spec hα ha).1

private lemma vg_h_eq {V W p q s : ℝ} (hV : 0 < V) (hVW : V < W) (hp : 0 < p) (hpq : p < q)
    (hq : q < 1) (hs : 0 < s) :
    (W / (W + s) - V / (V + s)) / (q - p) *
        Real.sqrt ((V / (p * (1 - p))) / (W / (q * (1 - q)))) =
      s * (Real.sqrt ((1 - p) / (p * V)) * (V / (V + s))) *
        (Real.sqrt ((1 - q) / (q * W)) * (W / (W + s))) *
        (q * (W - V) / ((1 - p) * W * (q - p))) := by
  have hW : 0 < W := by linarith
  have hq0 : 0 < q := by linarith
  have h1p : 0 < 1 - p := by linarith
  have h1q : 0 < 1 - q := by linarith
  have hqp : 0 < q - p := by linarith
  have hX : (V / (p * (1 - p))) / (W / (q * (1 - q))) =
      ((1 - p) / (p * V) * ((1 - q) / (q * W))) * (V * q / (1 - p)) ^ 2 := by
    field_simp
  have hYn : 0 ≤ (1 - p) / (p * V) * ((1 - q) / (q * W)) := by positivity
  rw [hX, Real.sqrt_mul hYn, Real.sqrt_sq (by positivity), Real.sqrt_mul (by positivity)]
  have hVs : 0 < V + s := by linarith
  have hWs : 0 < W + s := by linarith
  field_simp
  ring

private lemma vg_D_el {c V W p q T : ℝ} (hc : 0 < c) (hV : 0 < V) (hVW : V < W) (hp : 0 < p)
    (hpq : p < q) (hq : q < 1) (hT : c * (q * (1 - q)) ≤ T) (hK2 : (W - V) * T ≤ W * (q - p)) :
    q * (W - V) / ((1 - p) * W * (q - p)) ≤ 1 / (c * ((1 - p) * (1 - q))) := by
  have hW : 0 < W := by linarith
  have h1p : 0 < 1 - p := by linarith
  have h1q : 0 < 1 - q := by linarith
  have hq0 : 0 < q := by linarith
  have hqp : 0 < q - p := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (W - V) * (c * (q * (1 - q))) ≤ W * (q - p) :=
    le_trans (mul_le_mul_of_nonneg_left hT (by linarith)) hK2
  nlinarith [mul_le_mul_of_nonneg_left h1 h1p.le]

/-- the product form `H = x^α w(p) w(q) D(p,q)` -/
private lemma vg_h_conc {α x p q : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : 0 < p) (hpq : p < q)
    (hq : q < 1) :
    (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) / x ^ α =
      (Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) *
        (Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q) *
        (q * (contV α q - contV α p) / ((1 - p) * contV α q * (q - p))) := by
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp, by linarith⟩
  have hq' : q ∈ Ioo (0:ℝ) 1 := ⟨by linarith, hq⟩
  have hV := (vg_V_spec hα hp').1
  have hlt := vg_V_lt hα hp' hq' hpq
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have := vg_h_eq (s := x ^ α) hV hlt hp hpq hq hs
  unfold profF profU
  rw [this]
  field_simp

private lemma vg_f_le_one {α x p : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : p ∈ Ioo (0:ℝ) 1) :
    0 ≤ profF α x p ∧ profF α x p ≤ 1 := by
  have hV := (vg_V_spec hα hp).1
  have : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  unfold profF
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  linarith

/-- the bound `D ≤ 1/(c(1-p)(1-q))` -/
private lemma vg_D_bd {α c p q : ℝ} (hα : 0 < α) (hc : 0 < c)
    (hT : ∀ V : ℝ, 0 < V → c * (contS α V * (1 - contS α V)) ≤ Tcont α V)
    (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    0 ≤ q * (contV α q - contV α p) / ((1 - p) * contV α q * (q - p)) ∧
    q * (contV α q - contV α p) / ((1 - p) * contV α q * (q - p)) ≤
      1 / (c * ((1 - p) * (1 - q))) := by
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp, by linarith⟩
  have hq' : q ∈ Ioo (0:ℝ) 1 := ⟨by linarith, hq⟩
  have hV := vg_V_spec hα hp'
  have hW := vg_V_spec hα hq'
  have hlt := vg_V_lt hα hp' hq' hpq
  have h1p : 0 < 1 - p := by linarith
  have hqp : 0 < q - p := by linarith
  have hq0 : 0 < q := by linarith
  refine ⟨?_, ?_⟩
  · have := sub_pos.2 hlt
    have := hW.1
    positivity
  · have hK2 := vg_K2 hα hV.1 hlt.le
    rw [hV.2, hW.2] at hK2
    have hT' := hT (contV α q) hW.1
    rw [hW.2] at hT'
    exact vg_D_el hc hV.1 hlt hp hpq hq hT' hK2

/-- the pointwise bound for `H` -/
private lemma vg_H_bd {α x c p q : ℝ} (hα : 0 < α) (hx : 0 < x) (hc : 0 < c)
    (hT : ∀ V : ℝ, 0 < V → c * (contS α V * (1 - contS α V)) ≤ Tcont α V)
    (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    0 ≤ (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) ∧
    (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) ≤
      x ^ α / c * ((Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p) *
        (Real.sqrt ((1 - q) / (q * contV α q)) / (1 - q) * profF α x q)) := by
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp, by linarith⟩
  have hq' : q ∈ Ioo (0:ℝ) 1 := ⟨by linarith, hq⟩
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have h1p : 0 < 1 - p := by linarith
  have h1q : 0 < 1 - q := by linarith
  have hconc := vg_h_conc hα hx hp hpq hq
  obtain ⟨hD0, hD1⟩ := vg_D_bd hα hc hT hp hpq hq
  have hVp := (vg_V_spec hα hp').1
  have hVq := (vg_V_spec hα hq').1
  have hfp := vg_f_le_one hα hx hp'
  have hfq := vg_f_le_one hα hx hq'
  set gp := Real.sqrt ((1 - p) / (p * contV α p)) with hgp
  set gq := Real.sqrt ((1 - q) / (q * contV α q)) with hgq
  have hgp0 : 0 ≤ gp := Real.sqrt_nonneg _
  have hgq0 : 0 ≤ gq := Real.sqrt_nonneg _
  set Dd := q * (contV α q - contV α p) / ((1 - p) * contV α q * (q - p)) with hDd
  have hnn : 0 ≤ (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) := by
    have : 0 ≤ (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) / x ^ α := by
      rw [hconc]
      exact mul_nonneg (mul_nonneg (mul_nonneg hgp0 hfp.1) (mul_nonneg hgq0 hfq.1)) hD0
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => by
      exfalso; linarith [h.2, hs])
  refine ⟨hnn, ?_⟩
  have e : (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) =
      x ^ α * ((gp * profF α x p) * (gq * profF α x q) * Dd) := by
    rw [← hconc]; field_simp
  rw [e]
  have h2 : 0 ≤ (gp * profF α x p) * (gq * profF α x q) :=
    mul_nonneg (mul_nonneg hgp0 hfp.1) (mul_nonneg hgq0 hfq.1)
  calc x ^ α * ((gp * profF α x p) * (gq * profF α x q) * Dd)
      ≤ x ^ α * ((gp * profF α x p) * (gq * profF α x q) * (1 / (c * ((1 - p) * (1 - q))))) := by
        gcongr
    _ = _ := by field_simp


private lemma vg_K_pos {α : ℝ} (hα1 : 1 < α) : 0 < Kc α := by
  have hα0 : 0 < α := by linarith
  unfold Kc
  have hsin : 0 < Real.sin (Real.pi / α) :=
    Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hα0) (div_lt_self Real.pi_pos hα1)
  exact div_pos Real.pi_pos (mul_pos hα0 hsin)

/-- two-sided power bounds for `V_α` on `(0,1/2]` -/
private lemma vg_V_bounds {α : ℝ} (hα1 : 1 < α) :
    ∃ c1 C1 : ℝ, 0 < c1 ∧ 0 < C1 ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 2 →
      c1 * p ^ α ≤ contV α p ∧ contV α p ≤ C1 * p ^ α := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  have hE := lem_app_pl_continuum_iii_gt hα1
  have hne : ∀ᶠ p : ℝ in 𝓝[>] (0:ℝ), (p / Kc α) ^ α ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have : (0:ℝ) < p := hp
    exact (Real.rpow_pos_of_pos (by positivity) α).ne'
  have h1 := (isEquivalent_iff_tendsto_one hne).1 hE
  have hev : ∀ᶠ p : ℝ in 𝓝[>] (0:ℝ), (1 / 2 : ℝ) < (contV α / fun p => (p / Kc α) ^ α) p ∧
      (contV α / fun p => (p / Kc α) ^ α) p < 2 := by
    have := h1.eventually (Ioo_mem_nhds (by norm_num : (1/2:ℝ) < 1) (by norm_num : (1:ℝ) < 2))
    filter_upwards [this] with p hp using hp
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  have hu0 : (0:ℝ) < u := hu
  set δ : ℝ := min u 1 / 2 with hδ
  have hδ0 : 0 < δ := by have := lt_min hu0 one_pos; positivity
  have hδu : δ < u := by
    have : min u 1 ≤ u := min_le_left _ _
    linarith
  have hδ1 : δ ≤ 1 / 2 := by
    have : min u 1 ≤ 1 := min_le_right _ _
    linarith
  have hδI : δ ∈ Ioo (0:ℝ) 1 := ⟨hδ0, by linarith⟩
  have h12 : (1 / 2 : ℝ) ∈ Ioo (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hVδ := (vg_V_spec hα0 hδI).1
  have hV12 := (vg_V_spec hα0 h12).1
  have hKa : 0 < Kc α ^ α := Real.rpow_pos_of_pos hK α
  have hδa : 0 < δ ^ α := Real.rpow_pos_of_pos hδ0 α
  have h2a : 0 < (1 / 2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  refine ⟨min (1 / (2 * Kc α ^ α)) (contV α δ / (1 / 2 : ℝ) ^ α),
    max (2 / Kc α ^ α) (contV α (1 / 2) / δ ^ α),
    lt_min (by positivity) (by positivity), lt_max_of_lt_left (by positivity), ?_⟩
  intro p hp hp12
  have hpI : p ∈ Ioo (0:ℝ) 1 := ⟨hp, by linarith⟩
  have hVp := (vg_V_spec hα0 hpI).1
  have hpa : 0 < p ^ α := Real.rpow_pos_of_pos hp α
  by_cases hpδ : p < δ
  · -- small `p`
    have hmem : p ∈ Ioo (0:ℝ) u := ⟨hp, by linarith⟩
    obtain ⟨hlo, hhi⟩ := hsub hmem
    have hg : 0 < (p / Kc α) ^ α := Real.rpow_pos_of_pos (by positivity) α
    have hgeq : (p / Kc α) ^ α = p ^ α / Kc α ^ α := Real.div_rpow hp.le hK.le α
    simp only [Pi.div_apply] at hlo hhi
    rw [lt_div_iff₀ hg] at hlo
    rw [div_lt_iff₀ hg] at hhi
    rw [hgeq] at hlo hhi
    constructor
    · refine le_trans ?_ hlo.le
      calc min (1 / (2 * Kc α ^ α)) (contV α δ / (1 / 2 : ℝ) ^ α) * p ^ α
          ≤ 1 / (2 * Kc α ^ α) * p ^ α := by
            gcongr; exact min_le_left _ _
        _ = 1 / 2 * (p ^ α / Kc α ^ α) := by field_simp
    · refine hhi.le.trans ?_
      calc 2 * (p ^ α / Kc α ^ α) = 2 / Kc α ^ α * p ^ α := by field_simp
        _ ≤ max (2 / Kc α ^ α) (contV α (1 / 2) / δ ^ α) * p ^ α := by
            gcongr; exact le_max_left _ _
  · -- `p ∈ [δ, 1/2]`
    have hδp : δ ≤ p := not_lt.1 hpδ
    have hmono := vg_V_mono hα0
    have hlo : contV α δ ≤ contV α p := hmono hδI hpI hδp
    have hhi : contV α p ≤ contV α (1 / 2) := hmono hpI h12 hp12
    have hpa1 : p ^ α ≤ (1 / 2 : ℝ) ^ α := Real.rpow_le_rpow hp.le hp12 hα0.le
    have hpa2 : δ ^ α ≤ p ^ α := Real.rpow_le_rpow hδ0.le hδp hα0.le
    constructor
    · calc min (1 / (2 * Kc α ^ α)) (contV α δ / (1 / 2 : ℝ) ^ α) * p ^ α
          ≤ (contV α δ / (1 / 2 : ℝ) ^ α) * p ^ α := by
            gcongr; exact min_le_right _ _
        _ ≤ (contV α δ / (1 / 2 : ℝ) ^ α) * (1 / 2 : ℝ) ^ α := by gcongr
        _ = contV α δ := by field_simp
        _ ≤ contV α p := hlo
    · calc contV α p ≤ contV α (1 / 2) := hhi
        _ = (contV α (1 / 2) / δ ^ α) * δ ^ α := by field_simp
        _ ≤ (contV α (1 / 2) / δ ^ α) * p ^ α := by gcongr
        _ ≤ max (2 / Kc α ^ α) (contV α (1 / 2) / δ ^ α) * p ^ α := by
            gcongr; exact le_max_right _ _


private lemma vg_R_lim {α a : ℝ} (hα1 : 1 < α) (ha : 0 < a) :
    Tendsto (fun x : ℝ => contV α (x * a) / x ^ α) (𝓝[>] (0:ℝ)) (𝓝 ((a / Kc α) ^ α)) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  have hE := lem_app_pl_continuum_iii_gt hα1
  have hne : ∀ᶠ p : ℝ in 𝓝[>] (0:ℝ), (p / Kc α) ^ α ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have : (0:ℝ) < p := hp
    exact (Real.rpow_pos_of_pos (by positivity) α).ne'
  have h1 := (isEquivalent_iff_tendsto_one hne).1 hE
  have h2 := (h1.comp (vz_mul_tendsto ha)).mul_const ((a / Kc α) ^ α)
  rw [one_mul] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (0:ℝ) < x := hx
  simp only [Function.comp, Pi.div_apply]
  have hxa : 0 < (x * a / Kc α) ^ α := Real.rpow_pos_of_pos (by positivity) α
  have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  have e : (x * a / Kc α) ^ α = x ^ α * (a / Kc α) ^ α := by
    rw [show x * a / Kc α = x * (a / Kc α) by ring, Real.mul_rpow hx0.le (by positivity)]
  rw [e]
  field_simp

private lemma vg_f_le_pow {α C1 x p a : ℝ} (hα0 : 0 < α) (hC1 : 0 < C1) (hx : 0 < x) (hp : 0 < p)
    {V : ℝ} (hV : 0 < V) (hVle : V ≤ C1 * p ^ α) (ha0 : 0 ≤ a) (haα : a ≤ α) :
    V / (V + x ^ α) ≤ C1 ^ (a / α) * (p / x) ^ a := by
  have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  set u : ℝ := C1 * (p / x) ^ α with hu
  have hu0 : 0 < u := by positivity
  have hf1 : V / (V + x ^ α) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hfu : V / (V + x ^ α) ≤ u := by
    have : V / (V + x ^ α) ≤ V / x ^ α := div_le_div_of_nonneg_left hV.le hxα (by linarith)
    refine this.trans ?_
    rw [div_le_iff₀ hxα, hu, Real.div_rpow hp.le hx.le]
    calc V ≤ C1 * p ^ α := hVle
      _ = C1 * (p ^ α / x ^ α) * x ^ α := by field_simp
  have hexp0 : 0 ≤ a / α := div_nonneg ha0 hα0.le
  have hexp1 : a / α ≤ 1 := (div_le_one hα0).2 haα
  have hfu' : V / (V + x ^ α) ≤ u ^ (a / α) := by
    by_cases h1 : u ≤ 1
    · calc V / (V + x ^ α) ≤ u := hfu
        _ = u ^ (1:ℝ) := (Real.rpow_one u).symm
        _ ≤ u ^ (a / α) := Real.rpow_le_rpow_of_exponent_ge hu0 h1 hexp1
    · exact hf1.trans (Real.one_le_rpow (not_le.1 h1).le hexp0)
  refine hfu'.trans (le_of_eq ?_)
  rw [hu, Real.mul_rpow hC1.le (by positivity), ← Real.rpow_mul (by positivity)]
  congr 2
  field_simp

private lemma vg_bh_small {α : ℝ} (hα1 : 1 < α) {a : ℝ} (ha0 : 0 ≤ a) (haα : a ≤ α) :
    ∃ A : ℝ, 0 < A ∧ ∀ x p : ℝ, 0 < x → 0 < p → p ≤ 1 / 2 →
      Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p ≤
        A * p ^ (-((α + 1) / 2)) * (p / x) ^ a := by
  have hα0 : 0 < α := by linarith
  obtain ⟨c1, C1, hc1, hC1, hV⟩ := vg_V_bounds hα1
  refine ⟨2 * (Real.sqrt c1⁻¹) * C1 ^ (a / α), by positivity, fun x p hx hp hp12 => ?_⟩
  have hpI : p ∈ Ioo (0:ℝ) 1 := ⟨hp, by linarith⟩
  obtain ⟨hVlo, hVhi⟩ := hV p hp hp12
  have hVp := (vg_V_spec hα0 hpI).1
  have hf := vg_f_le_pow (x := x) hα0 hC1 hx hp hVp hVhi ha0 haα
  have hf0 : 0 ≤ profF α x p := (vg_f_le_one hα0 hx hpI).1
  have hf' : profF α x p ≤ C1 ^ (a / α) * (p / x) ^ a := hf
  have h1p : 0 < 1 - p := by linarith
  have hpa : 0 < p ^ α := Real.rpow_pos_of_pos hp α
  set s : ℝ := p ^ (-((α + 1) / 2)) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hp _
  have hs2 : s ^ 2 = p⁻¹ * (p ^ α)⁻¹ := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hp.le,
      show -((α + 1) / 2) * ((2:ℕ):ℝ) = -1 + -α by push_cast; ring, Real.rpow_add hp,
      Real.rpow_neg_one, Real.rpow_neg hp.le]
  have hsq : Real.sqrt ((1 - p) / (p * contV α p)) ≤ Real.sqrt c1⁻¹ * s := by
    rw [← Real.sqrt_sq hs0.le, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [hs2]
    have : (1 - p) / (p * contV α p) ≤ 1 / (p * (c1 * p ^ α)) := by
      calc (1 - p) / (p * contV α p) ≤ 1 / (p * contV α p) := by
            gcongr; linarith
        _ ≤ 1 / (p * (c1 * p ^ α)) := by gcongr
    refine this.trans (le_of_eq ?_)
    field_simp
  have hinv : 1 / (1 - p) ≤ 2 := by
    rw [div_le_iff₀ h1p]; linarith
  calc Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p
      = Real.sqrt ((1 - p) / (p * contV α p)) * (1 / (1 - p)) * profF α x p := by ring
    _ ≤ (Real.sqrt c1⁻¹ * s) * 2 * (C1 ^ (a / α) * (p / x) ^ a) := by
        gcongr
    _ = _ := by ring

private lemma vg_bh_cont {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    ContinuousOn (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p)
      (Ioo (0:ℝ) 1) := by
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hV := vg_V_cont hα
  have h1 : ContinuousOn (fun p : ℝ => (1 - p) / (p * contV α p)) (Ioo (0:ℝ) 1) := by
    refine (continuousOn_const.sub continuousOn_id).div (continuousOn_id.mul hV) ?_
    intro p hp
    have := (vg_V_spec hα hp).1
    have := hp.1
    positivity
  have h2 : ContinuousOn (fun p : ℝ => (1 - p)) (Ioo (0:ℝ) 1) := continuousOn_const.sub continuousOn_id
  have h3 : ContinuousOn (profF α x) (Ioo (0:ℝ) 1) := by
    unfold profF
    refine hV.div (hV.add continuousOn_const) ?_
    intro p hp
    have := (vg_V_spec hα hp).1
    linarith
  refine ((Real.continuous_sqrt.comp_continuousOn h1).div h2 (fun p hp => ?_)).mul h3
  have : p < 1 := hp.2
  linarith

private lemma vg_bh_large {α : ℝ} (hα : 0 < α) :
    ∃ A2 : ℝ, 0 < A2 ∧ ∀ x p : ℝ, 0 < x → 1 / 2 ≤ p → p < 1 →
      Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p ≤ A2 * (1 - p) ^ (-(1 / 2 : ℝ)) := by
  have h12 : (1 / 2 : ℝ) ∈ Ioo (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hv0 := (vg_V_spec hα h12).1
  refine ⟨Real.sqrt (4 / contV α (1 / 2)), by positivity, fun x p hx hp1 hp2 => ?_⟩
  have hpI : p ∈ Ioo (0:ℝ) 1 := ⟨by linarith, hp2⟩
  have hVp := (vg_V_spec hα hpI).1
  have hmono : contV α (1 / 2) ≤ contV α p := vg_V_mono hα h12 hpI hp1
  have h1p : 0 < 1 - p := by linarith
  have hf := vg_f_le_one hα hx hpI
  have hsq : 0 < Real.sqrt (1 - p) := Real.sqrt_pos.2 h1p
  have e : (1 - p) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (1 - p))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h1p.le]
  rw [e]
  have key : Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) ≤ Real.sqrt (4 / contV α (1 / 2)) * (Real.sqrt (1 - p))⁻¹ := by
    have h1 : (1 - p) / (p * contV α p) ≤ (1 - p) * (4 / contV α (1 / 2)) := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 / 2 * contV α (1 / 2) ≤ p * contV α p := by
        calc 1 / 2 * contV α (1 / 2) ≤ p * contV α (1 / 2) := by gcongr
          _ ≤ p * contV α p := by gcongr
      have hh : (1 - p) * (4 / contV α (1 / 2)) * (p * contV α p) ≥ (1 - p) * (4 / contV α (1 / 2)) * (1 / 2 * contV α (1 / 2)) := by
        gcongr
      have h2' : (1 - p) * (4 / contV α (1 / 2)) * (1 / 2 * contV α (1 / 2)) = 2 * (1 - p) := by
        field_simp
        ring
      linarith
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_mul h1p.le] at h2
    have hr : (Real.sqrt (1 - p))⁻¹ * (1 - p) = Real.sqrt (1 - p) := by
      have := Real.sq_sqrt h1p.le
      field_simp
      linarith
    rw [div_le_iff₀ h1p]
    calc Real.sqrt ((1 - p) / (p * contV α p)) ≤ Real.sqrt (1 - p) * Real.sqrt (4 / contV α (1 / 2)) := h2
      _ = Real.sqrt (4 / contV α (1 / 2)) * (Real.sqrt (1 - p))⁻¹ * (1 - p) := by
        rw [mul_assoc, hr]; ring
  calc Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p
      ≤ Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * 1 := by gcongr; exact hf.2
    _ ≤ _ := by rw [mul_one]; exact key


private lemma vg_int_rpow_Ioc {e : ℝ} (he : -1 < e) (b : ℝ) :
    IntegrableOn (fun p : ℝ => p ^ e) (Ioc 0 b) := by
  rcases le_or_gt b 0 with hb | hb
  · rw [Ioc_eq_empty (not_lt.2 hb)]; exact integrableOn_empty
  · have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b) he)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).1 this

private lemma vg_int_one_sub_Ioo :
    IntegrableOn (fun p : ℝ => (1 - p) ^ (-(1 / 2 : ℝ))) (Ioo (1 / 2) 1) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 / 2) (r := -(1 / 2 : ℝ))
    (by norm_num)).comp_sub_left 1
  simp only [sub_zero] at h
  have h2 : IntervalIntegrable (fun p : ℝ => (1 - p) ^ (-(1 / 2 : ℝ))) volume (1 / 2) 1 := by
    have := h.symm
    convert this using 2
    norm_num
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 h2).mono_set Ioo_subset_Ioc_self

private lemma vg_bh_int {α a : ℝ} (hα1 : 1 < α) (ha1 : (α - 1) / 2 < a) (haα : a ≤ α) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      IntegrableOn (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p)
        (Ioo 0 1) ∧
      ∫ p in Ioo (0:ℝ) 1, Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p ≤
        M * x ^ (-a) := by
  have hα0 : 0 < α := by linarith
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨A, hA, hS⟩ := vg_bh_small hα1 ha0 haα
  obtain ⟨A2, hA2, hL⟩ := vg_bh_large hα0
  set e1 : ℝ := a - (α + 1) / 2 with he1
  have he1' : -1 < e1 := by rw [he1]; linarith
  set I1 : ℝ := ∫ p in Ioc (0:ℝ) (1 / 2), p ^ (-((α + 1) / 2) + a) with hI1
  set I2 : ℝ := ∫ p in Ioo (1 / 2 : ℝ) 1, (1 - p) ^ (-(1 / 2 : ℝ)) with hI2
  have hI1n : 0 ≤ I1 := setIntegral_nonneg measurableSet_Ioc (fun p hp => Real.rpow_nonneg hp.1.le _)
  have hI2n : 0 ≤ I2 := setIntegral_nonneg measurableSet_Ioo
    (fun p hp => Real.rpow_nonneg (by linarith [hp.2]) _)
  have hint1 : IntegrableOn (fun p : ℝ => p ^ (-((α + 1) / 2) + a)) (Ioc 0 (1 / 2)) :=
    vg_int_rpow_Ioc (by linarith) _
  refine ⟨A * I1 + A2 * I2 + 1, by positivity, fun x hx hx1 => ?_⟩
  have hxa : 1 ≤ x ^ (-a) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx hx1 (by linarith)
  have hxa0 : 0 < x ^ (-a) := Real.rpow_pos_of_pos hx _
  set bh : ℝ → ℝ := fun p => Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p with hbh
  set b1 : ℝ → ℝ := (Ioc (0:ℝ) (1 / 2)).indicator (fun p => A * x ^ (-a) * p ^ (-((α + 1) / 2) + a)) with hb1
  set b2 : ℝ → ℝ := (Ioo (1 / 2 : ℝ) 1).indicator (fun p => A2 * (1 - p) ^ (-(1 / 2 : ℝ))) with hb2
  have hb1i : IntegrableOn b1 (Ioo 0 1) :=
    (IntegrableOn.integrable_indicator (hint1.const_mul (A * x ^ (-a))) measurableSet_Ioc).integrableOn
  have hb2i : IntegrableOn b2 (Ioo 0 1) :=
    (IntegrableOn.integrable_indicator (vg_int_one_sub_Ioo.const_mul A2) measurableSet_Ioo).integrableOn
  have hb1n : ∀ p, 0 ≤ b1 p := fun p => by
    simp only [hb1, Set.indicator]; split_ifs with h
    · exact mul_nonneg (by positivity) (Real.rpow_nonneg (le_of_lt h.1) _)
    · exact le_rfl
  have hb2n : ∀ p, 0 ≤ b2 p := fun p => by
    simp only [hb2, Set.indicator]; split_ifs with h
    · exact mul_nonneg hA2.le (Real.rpow_nonneg (by linarith [h.2]) _)
    · exact le_rfl
  have hle : ∀ p ∈ Ioo (0:ℝ) 1, bh p ≤ b1 p + b2 p := by
    intro p hp
    by_cases hp12 : p ≤ 1 / 2
    · have h1 : p ∈ Ioc (0:ℝ) (1 / 2) := ⟨hp.1, hp12⟩
      have h2 : p ∉ Ioo (1 / 2 : ℝ) 1 := fun h => by linarith [h.1]
      simp only [hb1, hb2, Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero]
      refine (hS x p hx hp.1 hp12).trans (le_of_eq ?_)
      rw [Real.div_rpow hp.1.le hx.le, Real.rpow_neg hx.le, Real.rpow_add hp.1]
      field_simp
    · have hp12' : 1 / 2 < p := not_le.1 hp12
      have h1 : p ∉ Ioc (0:ℝ) (1 / 2) := fun h => by linarith [h.2]
      have h2 : p ∈ Ioo (1 / 2 : ℝ) 1 := ⟨hp12', hp.2⟩
      simp only [hb1, hb2, Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_add]
      exact hL x p hx hp12'.le hp.2
  have hbh0 : ∀ p ∈ Ioo (0:ℝ) 1, 0 ≤ bh p := by
    intro p hp
    have h1p : 0 < 1 - p := by linarith [hp.2]
    have := (vg_f_le_one hα0 hx hp).1
    simp only [hbh]
    positivity
  have hmeas : AEStronglyMeasurable bh (volume.restrict (Ioo (0:ℝ) 1)) :=
    (vg_bh_cont hα0 hx).aestronglyMeasurable measurableSet_Ioo
  have hbhi : IntegrableOn bh (Ioo 0 1) := by
    refine Integrable.mono' (hb1i.add hb2i) hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun p hp => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hbh0 p hp)]
    exact hle p hp
  refine ⟨hbhi, ?_⟩
  have hv1 : ∫ p in Ioo (0:ℝ) 1, b1 p = A * x ^ (-a) * I1 := by
    rw [hb1, setIntegral_indicator measurableSet_Ioc]
    have : Ioo (0:ℝ) 1 ∩ Ioc 0 (1 / 2) = Ioc 0 (1 / 2) := by
      ext p; simp only [mem_inter_iff, mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, h1, h2⟩
    rw [this, integral_const_mul]
  have hv2 : ∫ p in Ioo (0:ℝ) 1, b2 p = A2 * I2 := by
    rw [hb2, setIntegral_indicator measurableSet_Ioo]
    have : Ioo (0:ℝ) 1 ∩ Ioo (1 / 2) 1 = Ioo (1 / 2) 1 := by
      ext p; simp only [mem_inter_iff, mem_Ioo]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1, h2⟩
    rw [this, integral_const_mul]
  calc ∫ p in Ioo (0:ℝ) 1, bh p ≤ ∫ p in Ioo (0:ℝ) 1, (b1 p + b2 p) :=
        setIntegral_mono_on hbhi (hb1i.add hb2i) measurableSet_Ioo hle
    _ = A * x ^ (-a) * I1 + A2 * I2 := by rw [integral_add hb1i hb2i, hv1, hv2]
    _ ≤ (A * I1 + A2 * I2 + 1) * x ^ (-a) := by
        have h1 : A2 * I2 ≤ A2 * I2 * x ^ (-a) := le_mul_of_one_le_right (by positivity) hxa
        nlinarith [mul_nonneg hA.le hI1n]


private lemma vg_shear_mp : MeasurePreserving (fun z : ℝ × ℝ => (z.2, z.2 + z.1))
    (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) := by
  have h := measurePreserving_prod_add_swap (volume : Measure ℝ) (volume : Measure ℝ)
  rw [← Measure.volume_eq_prod] at h
  exact h

private lemma vg_shear_emb : MeasurableEmbedding (fun z : ℝ × ℝ => (z.2, z.2 + z.1)) := by
  have : (fun z : ℝ × ℝ => (z.2, z.2 + z.1)) =
      ⇑((MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).trans (MeasurableEquiv.shearAddRight ℝ)) := by
    funext z; rfl
  rw [this]
  exact MeasurableEquiv.measurableEmbedding _

private lemma vg_Hf_cont {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    ContinuousOn (fun z : ℝ × ℝ => (profF α x z.2 - profF α x z.1) / (z.2 - z.1) *
        Real.sqrt (profU α z.1 / profU α z.2))
      {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < z.2 ∧ z.2 < 1} := by
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hV := vg_V_cont hα
  have hF : ContinuousOn (profF α x) (Ioo (0:ℝ) 1) := by
    unfold profF
    refine hV.div (hV.add continuousOn_const) ?_
    intro p hp
    have := (vg_V_spec hα hp).1
    linarith
  have hU : ContinuousOn (profU α) (Ioo (0:ℝ) 1) := by
    unfold profU
    refine hV.div (by fun_prop) ?_
    intro p hp
    have : 0 < 1 - p := by linarith [hp.2]
    have := hp.1
    positivity
  have m1 : MapsTo (fun z : ℝ × ℝ => z.1) {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < z.2 ∧ z.2 < 1} (Ioo 0 1) :=
    fun z hz => ⟨hz.1, by linarith [hz.2.1, hz.2.2]⟩
  have m2 : MapsTo (fun z : ℝ × ℝ => z.2) {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < z.2 ∧ z.2 < 1} (Ioo 0 1) :=
    fun z hz => ⟨by linarith [hz.1, hz.2.1], hz.2.2⟩
  have cF1 := hF.comp (by fun_prop : Continuous fun z : ℝ × ℝ => z.1).continuousOn m1
  have cF2 := hF.comp (by fun_prop : Continuous fun z : ℝ × ℝ => z.2).continuousOn m2
  have cU1 := hU.comp (by fun_prop : Continuous fun z : ℝ × ℝ => z.1).continuousOn m1
  have cU2 := hU.comp (by fun_prop : Continuous fun z : ℝ × ℝ => z.2).continuousOn m2
  refine ((cF2.sub cF1).div ((by fun_prop : Continuous fun z : ℝ × ℝ => z.2 - z.1).continuousOn)
    (fun z hz => (sub_pos.2 hz.2.1).ne')).mul (Real.continuous_sqrt.comp_continuousOn (cU1.div cU2 ?_))
  intro z hz
  have h := m2 hz
  have hV2 := (vg_V_spec hα h).1
  unfold profU
  have : 0 < 1 - z.2 := by linarith [hz.2.2]
  have : 0 < z.2 := h.1
  positivity

open Muon.DetEquiv ProbabilityTheory in
private lemma vg_Hhat_int {α x : ℝ} (hα1 : 1 < α) (hx : 0 < x) (hx1 : x ≤ 1) :
    Integrable (Set.indicator {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < z.2 ∧ z.2 < 1}
      (fun z : ℝ × ℝ => (profF α x z.2 - profF α x z.1) / (z.2 - z.1) *
        Real.sqrt (profU α z.1 / profU α z.2))) volume := by
  have hα0 : 0 < α := by linarith
  obtain ⟨c, C, hc, -, hT⟩ := lem_app_pl_continuum_ii hα0
  have hT' : ∀ V : ℝ, 0 < V → c * (contS α V * (1 - contS α V)) ≤ Tcont α V :=
    fun V hV => (hT V hV).1
  obtain ⟨M, -, hM⟩ := vg_bh_int hα1 (a := 3 * ((α - 1) / 2) / 2) (by linarith) (by linarith)
  obtain ⟨hbi, -⟩ := hM x hx hx1
  set bh : ℝ → ℝ := fun p => Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p with hbh
  have hbhat : Integrable (Set.indicator (Ioo (0:ℝ) 1) bh) volume :=
    IntegrableOn.integrable_indicator hbi measurableSet_Ioo
  have hbig : Integrable (fun z : ℝ × ℝ => x ^ α / c *
      (Set.indicator (Ioo (0:ℝ) 1) bh z.1 * Set.indicator (Ioo (0:ℝ) 1) bh z.2)) volume := by
    rw [Measure.volume_eq_prod]
    exact (hbhat.mul_prod hbhat).const_mul _
  have hTm : MeasurableSet {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < z.2 ∧ z.2 < 1} := by
    refine MeasurableSet.inter (measurableSet_lt measurable_const measurable_fst) ?_
    exact MeasurableSet.inter (measurableSet_lt measurable_fst measurable_snd)
      (measurableSet_lt measurable_snd measurable_const)
  refine Integrable.mono' hbig ?_ ?_
  · exact (aestronglyMeasurable_indicator_iff hTm).2 ((vg_Hf_cont hα0 hx).aestronglyMeasurable hTm)
  · refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < z.2 ∧ z.2 < 1}
    · rw [Set.indicator_of_mem hz, Real.norm_eq_abs]
      obtain ⟨h0, h1⟩ := vg_H_bd hα0 hx hc hT' hz.1 hz.2.1 hz.2.2
      rw [abs_of_nonneg h0]
      refine h1.trans (le_of_eq ?_)
      have e1 : z.1 ∈ Ioo (0:ℝ) 1 := ⟨hz.1, by linarith [hz.2.1, hz.2.2]⟩
      have e2 : z.2 ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hz.1, hz.2.1], hz.2.2⟩
      rw [Set.indicator_of_mem e1, Set.indicator_of_mem e2]
    · rw [Set.indicator_of_notMem hz, norm_zero]
      have hpos : ∀ w : ℝ, 0 ≤ Set.indicator (Ioo (0:ℝ) 1) bh w := by
        intro w
        by_cases hw : w ∈ Ioo (0:ℝ) 1
        · rw [Set.indicator_of_mem hw]
          have h1p : 0 < 1 - w := by linarith [hw.2]
          have := (vg_f_le_one hα0 hx hw).1
          simp only [hbh]; positivity
        · rw [Set.indicator_of_notMem hw]
      have := hpos z.1; have := hpos z.2
      positivity


open Muon.DetEquiv ProbabilityTheory in
private lemma vg_repr {α x : ℝ} (hα1 : 1 < α) (hx : 0 < x) (hx1 : x ≤ 1) :
    profGamma α x = 2 * ∫ q in Ioo (0:ℝ) 1, q * ∫ ρ in Ioo (0:ℝ) 1,
      (profF α x q - profF α x (ρ * q)) / (q - ρ * q) *
        Real.sqrt (profU α (ρ * q) / profU α q) ∧
    IntegrableOn (fun q : ℝ => q * ∫ ρ in Ioo (0:ℝ) 1,
      (profF α x q - profF α x (ρ * q)) / (q - ρ * q) *
        Real.sqrt (profU α (ρ * q) / profU α q)) (Ioo (0:ℝ) 1) := by
  have hα0 : 0 < α := by linarith
  have hint := vg_Hhat_int hα1 hx hx1
  set T : Set (ℝ × ℝ) := {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < z.2 ∧ z.2 < 1} with hT
  set Hh : ℝ × ℝ → ℝ := Set.indicator T
    (fun z : ℝ × ℝ => (profF α x z.2 - profF α x z.1) / (z.2 - z.1) *
        Real.sqrt (profU α z.1 / profU α z.2)) with hHh
  -- step a
  have ha : ∀ τ : ℝ, ∫ p, Hh (p, p + τ) =
      Set.indicator (Ioo (0:ℝ) 1) (fun τ => profC α x τ) τ := by
    intro τ
    by_cases hτ : τ ∈ Ioo (0:ℝ) 1
    · rw [Set.indicator_of_mem hτ]
      have e : (fun p : ℝ => Hh (p, p + τ)) = Set.indicator (Ioo (0:ℝ) (1 - τ))
          (fun p => (profF α x (p + τ) - profF α x p) / τ *
            Real.sqrt (profU α p / profU α (p + τ))) := by
        funext p
        by_cases hp : p ∈ Ioo (0:ℝ) (1 - τ)
        · have : (p, p + τ) ∈ T := ⟨hp.1, by linarith [hτ.1], by linarith [hp.2]⟩
          rw [hHh, Set.indicator_of_mem this, Set.indicator_of_mem hp]
          simp only [add_sub_cancel_left]
        · have : (p, p + τ) ∉ T := fun h => hp ⟨h.1, by linarith [h.2.2]⟩
          rw [hHh, Set.indicator_of_notMem this, Set.indicator_of_notMem hp]
      rw [e, integral_indicator measurableSet_Ioo]
      unfold profC
      rw [intervalIntegral.integral_of_le (by linarith [hτ.2]), integral_Ioc_eq_integral_Ioo]
    · rw [Set.indicator_of_notMem hτ]
      have : ∀ p : ℝ, Hh (p, p + τ) = 0 := by
        intro p
        have : (p, p + τ) ∉ T := by
          intro h
          apply hτ
          refine ⟨by linarith [h.2.1], ?_⟩
          linarith [h.1, h.2.2]
        rw [hHh, Set.indicator_of_notMem this]
      simp [this]
  -- steps b-e
  have hintE : Integrable (fun z : ℝ × ℝ => Hh (z.2, z.2 + z.1)) volume := by
    have := (vg_shear_mp.integrable_comp_emb vg_shear_emb (g := Hh)).2 hint
    exact this
  have hb : ∫ z : ℝ × ℝ, Hh z = ∫ τ in (0:ℝ)..1, profC α x τ := by
    calc ∫ z : ℝ × ℝ, Hh z = ∫ z : ℝ × ℝ, Hh (z.2, z.2 + z.1) :=
          (vg_shear_mp.integral_comp vg_shear_emb Hh).symm
      _ = ∫ τ : ℝ, ∫ p : ℝ, Hh (p, p + τ) := by
          have hintE' : Integrable (fun z : ℝ × ℝ => Hh (z.2, z.2 + z.1)) (volume.prod volume) := by
            rwa [← Measure.volume_eq_prod]
          rw [Measure.volume_eq_prod, integral_prod _ hintE']
      _ = ∫ τ : ℝ, Set.indicator (Ioo (0:ℝ) 1) (fun τ => profC α x τ) τ := by
          simp_rw [ha]
      _ = ∫ τ in Ioo (0:ℝ) 1, profC α x τ := integral_indicator measurableSet_Ioo
      _ = ∫ τ in (0:ℝ)..1, profC α x τ := by
          rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  -- step e: swap
  have hc : ∫ z : ℝ × ℝ, Hh z = ∫ q : ℝ, ∫ p : ℝ, Hh (p, q) := by
    have hint' : Integrable Hh (volume.prod volume) := by rwa [← Measure.volume_eq_prod]
    rw [Measure.volume_eq_prod, integral_prod_symm _ hint']
  -- step f: inner integral
  have hf : ∀ q : ℝ, ∫ p : ℝ, Hh (p, q) = Set.indicator (Ioo (0:ℝ) 1)
      (fun q => q * ∫ ρ in Ioo (0:ℝ) 1, (profF α x q - profF α x (ρ * q)) / (q - ρ * q) *
        Real.sqrt (profU α (ρ * q) / profU α q)) q := by
    intro q
    by_cases hq : q ∈ Ioo (0:ℝ) 1
    · rw [Set.indicator_of_mem hq]
      have e : (fun p : ℝ => Hh (p, q)) = Set.indicator (Ioo (0:ℝ) q)
          (fun p => (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q)) := by
        funext p
        by_cases hp : p ∈ Ioo (0:ℝ) q
        · have : (p, q) ∈ T := ⟨hp.1, hp.2, hq.2⟩
          rw [hHh, Set.indicator_of_mem this, Set.indicator_of_mem hp]
        · have : (p, q) ∉ T := fun h => hp ⟨h.1, h.2.1⟩
          rw [hHh, Set.indicator_of_notMem this, Set.indicator_of_notMem hp]
      rw [e, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hq.1.le]
      have := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (c := q)
        (fun p : ℝ => (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q))
        hq.1.ne'
      simp only [mul_zero, mul_one] at this
      simp_rw [mul_comm q] at this
      have h2 : ∫ (x_1 : ℝ) in (0:ℝ)..q, (profF α x q - profF α x x_1) / (q - x_1) *
          Real.sqrt (profU α x_1 / profU α q) = q * ∫ (ρ : ℝ) in (0:ℝ)..1,
          (profF α x q - profF α x (ρ * q)) / (q - ρ * q) * Real.sqrt (profU α (ρ * q) / profU α q) := by
        rw [this, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hq.1.ne', one_mul]
      rw [h2, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    · rw [Set.indicator_of_notMem hq]
      have : ∀ p : ℝ, Hh (p, q) = 0 := by
        intro p
        have : (p, q) ∉ T := fun h => hq ⟨by linarith [h.1, h.2.1], h.2.2⟩
        rw [hHh, Set.indicator_of_notMem this]
      simp [this]
  refine ⟨?_, ?_⟩
  · unfold profGamma
    rw [← hb, hc]
    congr 1
    simp_rw [hf]
    exact (integral_indicator measurableSet_Ioo)
  · have hint' : Integrable Hh (volume.prod volume) := by rwa [← Measure.volume_eq_prod]
    have h1 := hint'.swap.integral_prod_left
    have h2 : Integrable (Set.indicator (Ioo (0:ℝ) 1) (fun q : ℝ => q * ∫ ρ in Ioo (0:ℝ) 1,
      (profF α x q - profF α x (ρ * q)) / (q - ρ * q) *
        Real.sqrt (profU α (ρ * q) / profU α q))) volume := by
      refine h1.congr (Filter.Eventually.of_forall fun q => ?_)
      exact hf q
    exact (integrable_indicator_iff measurableSet_Ioo).1 h2


open Muon.DetEquiv ProbabilityTheory in
private lemma vg_F_gen {α : ℝ} (hα1 : 1 < α) {ap aq : ℝ} (hap0 : 0 ≤ ap) (hapα : ap ≤ α)
    (haq0 : 0 ≤ aq) (haqα : aq ≤ α) :
    ∃ A : ℝ, 0 < A ∧ ∀ x ρ y : ℝ, 0 < x → 0 < ρ → ρ < 1 → 0 < y → x * Kc α * y ≤ 1 / 2 →
      0 ≤ Kc α * (x * Kc α * y) *
        ((profF α x (x * Kc α * y) - profF α x (ρ * (x * Kc α * y))) /
          (x * Kc α * y - ρ * (x * Kc α * y)) *
          Real.sqrt (profU α (ρ * (x * Kc α * y)) / profU α (x * Kc α * y))) ∧
      Kc α * (x * Kc α * y) *
        ((profF α x (x * Kc α * y) - profF α x (ρ * (x * Kc α * y))) /
          (x * Kc α * y - ρ * (x * Kc α * y)) *
          Real.sqrt (profU α (ρ * (x * Kc α * y)) / profU α (x * Kc α * y))) ≤
      A * (ρ ^ (ap - (α + 1) / 2) * (Kc α * y) ^ (ap + aq - α)) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  obtain ⟨c, C, hc, -, hT⟩ := lem_app_pl_continuum_ii hα0
  have hT' : ∀ V : ℝ, 0 < V → c * (contS α V * (1 - contS α V)) ≤ Tcont α V :=
    fun V hV => (hT V hV).1
  obtain ⟨Ap, hAp, hSp⟩ := vg_bh_small hα1 hap0 hapα
  obtain ⟨Aq, hAq, hSq⟩ := vg_bh_small hα1 haq0 haqα
  refine ⟨Kc α * Ap * Aq / c, by positivity, fun x ρ y hx hρ0 hρ1 hy hq => ?_⟩
  set t : ℝ := Kc α * y with ht
  have ht0 : 0 < t := by positivity
  set q : ℝ := x * Kc α * y with hqdef
  have hqt : q = x * t := by rw [hqdef, ht]; ring
  have hq0 : 0 < q := by rw [hqt]; positivity
  have hp0 : 0 < ρ * q := by positivity
  have hpq : ρ * q < q := by nlinarith
  have hq1 : q < 1 := by linarith
  obtain ⟨hH0, hH1⟩ := vg_H_bd hα0 hx hc hT' hp0 hpq hq1
  have hp12 : ρ * q ≤ 1 / 2 := by nlinarith
  have hbq := hSq x q hx hq0 hq
  have hbp := hSp x (ρ * q) hx hp0 hp12
  have hbq0 : 0 ≤ Real.sqrt ((1 - q) / (q * contV α q)) / (1 - q) * profF α x q := by
    have hqI : q ∈ Ioo (0:ℝ) 1 := ⟨hq0, hq1⟩
    have := (vg_f_le_one hα0 hx hqI).1
    have : 0 < 1 - q := by linarith
    positivity
  have hbp0 : 0 ≤ Real.sqrt ((1 - ρ * q) / (ρ * q * contV α (ρ * q))) / (1 - ρ * q) * profF α x (ρ * q) := by
    have hpI : ρ * q ∈ Ioo (0:ℝ) 1 := ⟨hp0, by linarith⟩
    have := (vg_f_le_one hα0 hx hpI).1
    have : 0 < 1 - ρ * q := by linarith
    positivity
  have hKq : 0 ≤ Kc α * q := by positivity
  refine ⟨mul_nonneg hKq hH0, ?_⟩
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  calc Kc α * q * ((profF α x q - profF α x (ρ * q)) / (q - ρ * q) *
          Real.sqrt (profU α (ρ * q) / profU α q))
      ≤ Kc α * q * (x ^ α / c * ((Real.sqrt ((1 - ρ * q) / (ρ * q * contV α (ρ * q))) / (1 - ρ * q) *
          profF α x (ρ * q)) * (Real.sqrt ((1 - q) / (q * contV α q)) / (1 - q) * profF α x q))) :=
        mul_le_mul_of_nonneg_left hH1 hKq
    _ ≤ Kc α * q * (x ^ α / c * ((Ap * (ρ * q) ^ (-((α + 1) / 2)) * (ρ * q / x) ^ ap) *
          (Aq * q ^ (-((α + 1) / 2)) * (q / x) ^ aq))) := by
        gcongr
    _ = _ := by
        have e1 : (ρ * q) ^ (-((α + 1) / 2)) = ρ ^ (-((α + 1) / 2)) * q ^ (-((α + 1) / 2)) :=
          Real.mul_rpow hρ0.le hq0.le
        have e2 : ρ * q / x = ρ * t := by rw [hqt]; field_simp
        have e3 : q / x = t := by rw [hqt]; field_simp
        have e4 : (ρ * t) ^ ap = ρ ^ ap * t ^ ap := Real.mul_rpow hρ0.le ht0.le
        rw [e1, e2, e3, e4]
        -- collect powers
        have hxq : q ^ (-((α + 1) / 2)) * q ^ (-((α + 1) / 2)) * q = q ^ (-α) := by
          rw [← Real.rpow_add hq0, ← Real.rpow_add_one hq0.ne']
          congr 1; ring
        have hxqt : q ^ (-α) * x ^ α = t ^ (-α) := by
          rw [hqt, Real.mul_rpow hx.le ht0.le, Real.rpow_neg hx.le, Real.rpow_neg ht0.le]
          field_simp
        have hρe : ρ ^ ap * ρ ^ (-((α + 1) / 2)) = ρ ^ (ap - (α + 1) / 2) := by
          rw [← Real.rpow_add hρ0, sub_eq_add_neg]
        have hte : t ^ (-α) * t ^ ap * t ^ aq = t ^ (ap + aq - α) := by
          rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]; congr 1; ring
        calc Kc α * q * (x ^ α / c * (Ap * (ρ ^ (-((α + 1) / 2)) * q ^ (-((α + 1) / 2))) * (ρ ^ ap * t ^ ap) *
              (Aq * q ^ (-((α + 1) / 2)) * t ^ aq)))
            = Kc α * Ap * Aq / c * ((ρ ^ ap * ρ ^ (-((α + 1) / 2))) *
                ((q ^ (-((α + 1) / 2)) * q ^ (-((α + 1) / 2)) * q) * x ^ α) * t ^ ap * t ^ aq) := by
              field_simp
          _ = _ := by rw [hxq, hxqt, hρe, ← hte]; ring


open Muon.DetEquiv ProbabilityTheory in
private lemma vg_F_bd {α : ℝ} (hα1 : 1 < α) :
    ∃ Cb : ℝ, 0 < Cb ∧ ∀ x ρ y : ℝ, 0 < x → 0 < ρ → ρ < 1 → 0 < y → x * Kc α * y ≤ 1 / 2 →
      0 ≤ Kc α * (x * Kc α * y) *
        ((profF α x (x * Kc α * y) - profF α x (ρ * (x * Kc α * y))) /
          (x * Kc α * y - ρ * (x * Kc α * y)) *
          Real.sqrt (profU α (ρ * (x * Kc α * y)) / profU α (x * Kc α * y))) ∧
      Kc α * (x * Kc α * y) *
        ((profF α x (x * Kc α * y) - profF α x (ρ * (x * Kc α * y))) /
          (x * Kc α * y - ρ * (x * Kc α * y)) *
          Real.sqrt (profU α (ρ * (x * Kc α * y)) / profU α (x * Kc α * y))) ≤
      Cb * (ρ ^ ((α - 1) / 4 - 1) * (if y ≤ 1 then y ^ α else y ^ (-((α - 1) / 4) - 1))) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  obtain ⟨A1, hA1, h1⟩ := vg_F_gen hα1 (ap := α) (aq := α) hα0.le le_rfl hα0.le le_rfl
  obtain ⟨A2, hA2, h2⟩ := vg_F_gen hα1 (ap := 3 * ((α - 1) / 2) / 2) (aq := 0)
    (by linarith) (by linarith) le_rfl hα0.le
  refine ⟨max (A1 * Kc α ^ α) (A2 * Kc α ^ (3 * ((α - 1) / 2) / 2 + 0 - α)), lt_max_of_lt_left
    (by positivity), fun x ρ y hx hρ0 hρ1 hy hq => ?_⟩
  by_cases hy1 : y ≤ 1
  · obtain ⟨hlo, hhi⟩ := h1 x ρ y hx hρ0 hρ1 hy hq
    refine ⟨hlo, hhi.trans ?_⟩
    rw [if_pos hy1]
    have e1 : (Kc α * y) ^ (α + α - α) = Kc α ^ α * y ^ α := by
      rw [show α + α - α = α by ring, Real.mul_rpow hK.le hy.le]
    have e2 : ρ ^ (α - (α + 1) / 2) ≤ ρ ^ ((α - 1) / 4 - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1.le (by linarith)
    have hy0 : 0 < y ^ α := Real.rpow_pos_of_pos hy α
    have hKa : 0 < Kc α ^ α := Real.rpow_pos_of_pos hK α
    calc A1 * (ρ ^ (α - (α + 1) / 2) * (Kc α * y) ^ (α + α - α))
        = (A1 * Kc α ^ α) * (ρ ^ (α - (α + 1) / 2) * y ^ α) := by rw [e1]; ring
      _ ≤ max (A1 * Kc α ^ α) (A2 * Kc α ^ (3 * ((α - 1) / 2) / 2 + 0 - α)) * (ρ ^ ((α - 1) / 4 - 1) * y ^ α) := by
          gcongr
          exact le_max_left _ _
  · have hy1' : 1 < y := not_le.1 hy1
    obtain ⟨hlo, hhi⟩ := h2 x ρ y hx hρ0 hρ1 hy hq
    refine ⟨hlo, hhi.trans ?_⟩
    rw [if_neg hy1]
    have e1 : (Kc α * y) ^ (3 * ((α - 1) / 2) / 2 + 0 - α) =
        Kc α ^ (3 * ((α - 1) / 2) / 2 + 0 - α) * y ^ (-((α - 1) / 4) - 1) := by
      rw [Real.mul_rpow hK.le hy.le]
      congr 2; ring
    have e2 : ρ ^ (3 * ((α - 1) / 2) / 2 - (α + 1) / 2) = ρ ^ ((α - 1) / 4 - 1) := by
      congr 1; ring
    calc A2 * (ρ ^ (3 * ((α - 1) / 2) / 2 - (α + 1) / 2) * (Kc α * y) ^ (3 * ((α - 1) / 2) / 2 + 0 - α))
        = (A2 * Kc α ^ (3 * ((α - 1) / 2) / 2 + 0 - α)) * (ρ ^ ((α - 1) / 4 - 1) * y ^ (-((α - 1) / 4) - 1)) := by
          rw [e1, e2]; ring
      _ ≤ _ := by
          have : 0 ≤ ρ ^ ((α - 1) / 4 - 1) * y ^ (-((α - 1) / 4) - 1) := by positivity
          gcongr
          exact le_max_right _ _


private lemma vg_n_int {α : ℝ} (hα1 : 1 < α) :
    IntegrableOn (fun y : ℝ => if y ≤ 1 then y ^ α else y ^ (-((α - 1) / 4) - 1)) (Ioi 0) := by
  have hα0 : 0 < α := by linarith
  have h1 : IntegrableOn (fun y : ℝ => y ^ α) (Ioc 0 1) := vg_int_rpow_Ioc (by linarith) 1
  have h2 : IntegrableOn (fun y : ℝ => y ^ (-((α - 1) / 4) - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have e : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [e]
  refine IntegrableOn.union ?_ ?_
  · refine h1.congr_fun (fun u hu => ?_) measurableSet_Ioc
    simp [hu.2]
  · refine h2.congr_fun (fun u hu => ?_) measurableSet_Ioi
    have : ¬ u ≤ 1 := not_le.2 hu
    simp [this]

private lemma vg_maj_int {α Cb : ℝ} (hα1 : 1 < α) :
    Integrable (fun z : ℝ × ℝ => Cb * (z.1 ^ ((α - 1) / 4 - 1) *
      (if z.2 ≤ 1 then z.2 ^ α else z.2 ^ (-((α - 1) / 4) - 1))))
      ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have h1 : Integrable (fun ρ : ℝ => ρ ^ ((α - 1) / 4 - 1)) (volume.restrict (Ioo (0:ℝ) 1)) := by
    have := vg_int_rpow_Ioc (e := (α - 1) / 4 - 1) (by linarith) 1
    exact this.mono_set Ioo_subset_Ioc_self
  exact (h1.mul_prod (vg_n_int hα1)).const_mul Cb

open Muon.DetEquiv ProbabilityTheory in
private lemma vg_Fl_meas {α x : ℝ} (hα1 : 1 < α) (hx : 0 < x) :
    AEStronglyMeasurable (Set.indicator {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ x * Kc α * z.2 ≤ 1 / 2}
      (fun z : ℝ × ℝ => Kc α * (x * Kc α * z.2) *
        ((profF α x (x * Kc α * z.2) - profF α x (z.1 * (x * Kc α * z.2))) /
          (x * Kc α * z.2 - z.1 * (x * Kc α * z.2)) *
          Real.sqrt (profU α (z.1 * (x * Kc α * z.2)) / profU α (x * Kc α * z.2)))))
      ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  set R : Set (ℝ × ℝ) := {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ x * Kc α * z.2 ≤ 1 / 2} with hR
  have hRm : MeasurableSet R := by
    refine MeasurableSet.inter (measurableSet_lt measurable_const measurable_fst) ?_
    refine MeasurableSet.inter (measurableSet_lt measurable_fst measurable_const) ?_
    exact MeasurableSet.inter (measurableSet_lt measurable_const measurable_snd)
      (measurableSet_le (measurable_const.mul measurable_snd) measurable_const)
  have hcont : ContinuousOn (fun z : ℝ × ℝ => Kc α * (x * Kc α * z.2) *
        ((profF α x (x * Kc α * z.2) - profF α x (z.1 * (x * Kc α * z.2))) /
          (x * Kc α * z.2 - z.1 * (x * Kc α * z.2)) *
          Real.sqrt (profU α (z.1 * (x * Kc α * z.2)) / profU α (x * Kc α * z.2)))) R := by
    have hH := vg_Hf_cont hα0 hx
    have hmap : MapsTo (fun z : ℝ × ℝ => (z.1 * (x * Kc α * z.2), x * Kc α * z.2)) R
        {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < z.2 ∧ z.2 < 1} := by
      intro z hz
      have hq : 0 < x * Kc α * z.2 := by have := hz.2.2.1; positivity
      refine ⟨mul_pos hz.1 hq, ?_, by linarith [hz.2.2.2]⟩
      nlinarith [hz.2.1]
    have hc := hH.comp (by fun_prop : Continuous fun z : ℝ × ℝ =>
      (z.1 * (x * Kc α * z.2), x * Kc α * z.2)).continuousOn hmap
    exact (continuousOn_const.mul (by fun_prop : Continuous fun z : ℝ × ℝ => x * Kc α * z.2).continuousOn).mul hc
  have hcm : AEStronglyMeasurable (Set.indicator R _) volume :=
    (aestronglyMeasurable_indicator_iff hRm).2 (hcont.aestronglyMeasurable hRm)
  refine hcm.mono_measure ?_
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact Measure.restrict_le_self


private lemma vg_ae_mem {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∀ᵐ z ∂((μ.restrict s).prod (ν.restrict t)), z.1 ∈ s ∧ z.2 ∈ t := by
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (hs.prod ht)] with z hz using hz

open Muon.DetEquiv ProbabilityTheory in
private lemma vg_Fl_int {α x : ℝ} (hα1 : 1 < α) (hx : 0 < x) :
    ∃ Cb : ℝ, 0 < Cb ∧ Integrable (Set.indicator {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ x * Kc α * z.2 ≤ 1 / 2}
      (fun z : ℝ × ℝ => Kc α * (x * Kc α * z.2) *
        ((profF α x (x * Kc α * z.2) - profF α x (z.1 * (x * Kc α * z.2))) /
          (x * Kc α * z.2 - z.1 * (x * Kc α * z.2)) *
          Real.sqrt (profU α (z.1 * (x * Kc α * z.2)) / profU α (x * Kc α * z.2)))))
      ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))) := by
  obtain ⟨Cb, hCb, hF⟩ := vg_F_bd hα1
  refine ⟨Cb, hCb, Integrable.mono' (vg_maj_int (Cb := Cb) hα1) (vg_Fl_meas hα1 hx) ?_⟩
  filter_upwards [vg_ae_mem (μ := volume) (ν := volume) measurableSet_Ioo measurableSet_Ioi] with z hz
  have hρ : 0 < z.1 ∧ z.1 < 1 := hz.1
  have hy : 0 < z.2 := hz.2
  have hnn : 0 ≤ Cb * (z.1 ^ ((α - 1) / 4 - 1) *
      (if z.2 ≤ 1 then z.2 ^ α else z.2 ^ (-((α - 1) / 4) - 1))) := by
    have := hρ.1; have := hy
    split_ifs <;> positivity
  by_cases hq : x * Kc α * z.2 ≤ 1 / 2
  · rw [Set.indicator_of_mem (show z ∈ {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ x * Kc α * z.2 ≤ 1 / 2}
      from ⟨hρ.1, hρ.2, hy, hq⟩), Real.norm_eq_abs]
    obtain ⟨h0, h1⟩ := hF x z.1 z.2 hx hρ.1 hρ.2 hy hq
    rw [abs_of_nonneg h0]; exact h1
  · rw [Set.indicator_of_notMem (fun h => hq h.2.2.2), norm_zero]; exact hnn

open Muon.DetEquiv ProbabilityTheory in
private lemma vg_Lo_eq {α x : ℝ} (hα1 : 1 < α) (hx : 0 < x) :
    ∫ q in Ioc (0:ℝ) (1 / 2), q * ∫ ρ in Ioo (0:ℝ) 1,
      (profF α x q - profF α x (ρ * q)) / (q - ρ * q) * Real.sqrt (profU α (ρ * q) / profU α q) =
    x * ∫ z : ℝ × ℝ, Set.indicator {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ x * Kc α * z.2 ≤ 1 / 2}
      (fun z : ℝ × ℝ => Kc α * (x * Kc α * z.2) *
        ((profF α x (x * Kc α * z.2) - profF α x (z.1 * (x * Kc α * z.2))) /
          (x * Kc α * z.2 - z.1 * (x * Kc α * z.2)) *
          Real.sqrt (profU α (z.1 * (x * Kc α * z.2)) / profU α (x * Kc α * z.2)))) z
      ∂((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hK := vg_K_pos hα1
  obtain ⟨Cb, hCb, hint⟩ := vg_Fl_int hα1 hx
  set b : ℝ := x * Kc α with hb
  have hb0 : 0 < b := by positivity
  set J : ℝ → ℝ := fun q => q * ∫ ρ in Ioo (0:ℝ) 1,
      (profF α x q - profF α x (ρ * q)) / (q - ρ * q) * Real.sqrt (profU α (ρ * q) / profU α q) with hJ
  set g : ℝ → ℝ := Set.indicator (Iic (1 / 2)) J with hg
  have h1 : ∫ q in Ioc (0:ℝ) (1 / 2), J q = ∫ q in Ioi (0:ℝ), g q := by
    rw [hg, setIntegral_indicator measurableSet_Iic]
    congr 1
  have h2 : ∫ q in Ioi (0:ℝ), g q = b * ∫ y in Ioi (0:ℝ), g (b * y) := by
    have := integral_comp_mul_left_Ioi g 0 hb0
    rw [mul_zero] at this
    rw [this, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hb0.ne', one_mul]
  rw [integral_prod_symm _ hint]
  have h3 : ∀ y ∈ Ioi (0:ℝ), ∫ ρ in Ioo (0:ℝ) 1, Set.indicator
      {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ x * Kc α * z.2 ≤ 1 / 2}
      (fun z : ℝ × ℝ => Kc α * (x * Kc α * z.2) *
        ((profF α x (x * Kc α * z.2) - profF α x (z.1 * (x * Kc α * z.2))) /
          (x * Kc α * z.2 - z.1 * (x * Kc α * z.2)) *
          Real.sqrt (profU α (z.1 * (x * Kc α * z.2)) / profU α (x * Kc α * z.2)))) (ρ, y)
      = Kc α * g (b * y) := by
    intro y hy
    have hy0 : (0:ℝ) < y := hy
    by_cases hq : b * y ≤ 1 / 2
    · have hq' : x * Kc α * y ≤ 1 / 2 := hq
      have e : ∫ ρ in Ioo (0:ℝ) 1, Set.indicator
          {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ x * Kc α * z.2 ≤ 1 / 2}
          (fun z : ℝ × ℝ => Kc α * (x * Kc α * z.2) *
            ((profF α x (x * Kc α * z.2) - profF α x (z.1 * (x * Kc α * z.2))) /
              (x * Kc α * z.2 - z.1 * (x * Kc α * z.2)) *
              Real.sqrt (profU α (z.1 * (x * Kc α * z.2)) / profU α (x * Kc α * z.2)))) (ρ, y)
          = ∫ ρ in Ioo (0:ℝ) 1, Kc α * (x * Kc α * y) *
            ((profF α x (x * Kc α * y) - profF α x (ρ * (x * Kc α * y))) /
              (x * Kc α * y - ρ * (x * Kc α * y)) *
              Real.sqrt (profU α (ρ * (x * Kc α * y)) / profU α (x * Kc α * y))) := by
        refine setIntegral_congr_fun (measurableSet_Ioo : MeasurableSet (Ioo (0:ℝ) 1)) (fun ρ hρ => ?_)
        exact Set.indicator_of_mem (show (ρ, y) ∈ {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ x * Kc α * z.2 ≤ 1 / 2}
          from ⟨hρ.1, hρ.2, hy0, hq'⟩) _
      rw [e, integral_const_mul, hg, Set.indicator_of_mem (show b * y ∈ Iic (1 / 2 : ℝ) from hq), hJ]
      simp only [hb]
      ring
    · have hq' : ¬ x * Kc α * y ≤ 1 / 2 := hq
      rw [hg, Set.indicator_of_notMem (show b * y ∉ Iic (1 / 2 : ℝ) from hq), mul_zero]
      rw [setIntegral_congr_fun (measurableSet_Ioo : MeasurableSet (Ioo (0:ℝ) 1)) (g := fun _ => (0:ℝ)) (fun ρ hρ => ?_)]
      · simp
      · simp only []
        rw [Set.indicator_of_notMem (fun h => hq' h.2.2.2)]
  rw [setIntegral_congr_fun measurableSet_Ioi h3, integral_const_mul, h1, h2]
  simp only [hb]
  ring


private lemma vg_bh_nonneg {α x : ℝ} (hα0 : 0 < α) (hx : 0 < x) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    0 ≤ Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p := by
  have h1p : 0 < 1 - p := by linarith [hp.2]
  have := (vg_f_le_one hα0 hx hp).1
  positivity

open Muon.DetEquiv ProbabilityTheory in
private lemma vg_Hi_bd {α x c : ℝ} (hα1 : 1 < α) (hx : 0 < x) (hx1 : x ≤ 1) (hc : 0 < c)
    (hT' : ∀ V : ℝ, 0 < V → c * (contS α V * (1 - contS α V)) ≤ Tcont α V) :
    0 ≤ ∫ q in Ioo (1 / 2 : ℝ) 1, q * ∫ ρ in Ioo (0:ℝ) 1,
      (profF α x q - profF α x (ρ * q)) / (q - ρ * q) * Real.sqrt (profU α (ρ * q) / profU α q) ∧
    ∫ q in Ioo (1 / 2 : ℝ) 1, q * ∫ ρ in Ioo (0:ℝ) 1,
      (profF α x q - profF α x (ρ * q)) / (q - ρ * q) * Real.sqrt (profU α (ρ * q) / profU α q) ≤
    x ^ α / c * ((∫ p in Ioo (0:ℝ) 1, Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p) *
      ∫ p in Ioo (1 / 2 : ℝ) 1, Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p) := by
  have hα0 : 0 < α := by linarith
  have hint := vg_Hhat_int hα1 hx hx1
  obtain ⟨M, -, hM⟩ := vg_bh_int hα1 (a := 3 * ((α - 1) / 2) / 2) (by linarith) (by linarith)
  obtain ⟨hbi, -⟩ := hM x hx hx1
  set bh : ℝ → ℝ := fun p => Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p with hbh
  set T : Set (ℝ × ℝ) := {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < z.2 ∧ z.2 < 1} with hT
  set Hh : ℝ × ℝ → ℝ := Set.indicator T
    (fun z : ℝ × ℝ => (profF α x z.2 - profF α x z.1) / (z.2 - z.1) *
        Real.sqrt (profU α z.1 / profU α z.2)) with hHh
  set S : Set ℝ := Ioo (1 / 2 : ℝ) 1 with hS
  have hSm : MeasurableSet S := measurableSet_Ioo
  have hSsub : S ⊆ Ioo (0:ℝ) 1 := fun q hq => ⟨by linarith [hq.1], hq.2⟩
  have hbhat : Integrable (Set.indicator (Ioo (0:ℝ) 1) bh) volume :=
    IntegrableOn.integrable_indicator hbi measurableSet_Ioo
  have hbS : Integrable (Set.indicator S bh) volume :=
    IntegrableOn.integrable_indicator (hbi.mono_set hSsub) hSm
  -- the inner integral
  have hf : ∀ q ∈ S, ∫ p : ℝ, Hh (p, q) = q * ∫ ρ in Ioo (0:ℝ) 1,
      (profF α x q - profF α x (ρ * q)) / (q - ρ * q) * Real.sqrt (profU α (ρ * q) / profU α q) := by
    intro q hqS
    have hq : q ∈ Ioo (0:ℝ) 1 := hSsub hqS
    have e : (fun p : ℝ => Hh (p, q)) = Set.indicator (Ioo (0:ℝ) q)
        (fun p => (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q)) := by
      funext p
      by_cases hp : p ∈ Ioo (0:ℝ) q
      · have : (p, q) ∈ T := ⟨hp.1, hp.2, hq.2⟩
        rw [hHh, Set.indicator_of_mem this, Set.indicator_of_mem hp]
      · have : (p, q) ∉ T := fun h => hp ⟨h.1, h.2.1⟩
        rw [hHh, Set.indicator_of_notMem this, Set.indicator_of_notMem hp]
    rw [e, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hq.1.le]
    have := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (c := q)
      (fun p : ℝ => (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q))
      hq.1.ne'
    simp only [mul_zero, mul_one] at this
    simp_rw [mul_comm q] at this
    have h2 : ∫ (x_1 : ℝ) in (0:ℝ)..q, (profF α x q - profF α x x_1) / (q - x_1) *
        Real.sqrt (profU α x_1 / profU α q) = q * ∫ (ρ : ℝ) in (0:ℝ)..1,
        (profF α x q - profF α x (ρ * q)) / (q - ρ * q) * Real.sqrt (profU α (ρ * q) / profU α q) := by
      rw [this, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hq.1.ne', one_mul]
    rw [h2, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  -- the cut-off function
  set W : ℝ × ℝ → ℝ := Set.indicator (univ ×ˢ S) Hh with hW
  have hWint : Integrable W volume := by
    have : univ ×ˢ S = {z : ℝ × ℝ | z.2 ∈ S} := by ext z; simp
    exact hint.indicator (MeasurableSet.univ.prod hSm)
  have hWeq : ∫ z : ℝ × ℝ, W z = ∫ q in S, q * ∫ ρ in Ioo (0:ℝ) 1,
      (profF α x q - profF α x (ρ * q)) / (q - ρ * q) * Real.sqrt (profU α (ρ * q) / profU α q) := by
    have hWint' : Integrable W (volume.prod volume) := by rwa [← Measure.volume_eq_prod]
    rw [Measure.volume_eq_prod, integral_prod_symm _ hWint', ← integral_indicator hSm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    by_cases hqS : q ∈ S
    · rw [Set.indicator_of_mem hqS, ← hf q hqS]
      show ∫ p : ℝ, W (p, q) = _
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      show W (p, q) = Hh (p, q)
      exact Set.indicator_of_mem (show (p, q) ∈ univ ×ˢ S from ⟨mem_univ _, hqS⟩) Hh
    · rw [Set.indicator_of_notMem hqS]
      have : ∀ p : ℝ, W (p, q) = 0 := fun p => by
        rw [hW, Set.indicator_of_notMem (show (p, q) ∉ univ ×ˢ S from fun h => hqS h.2)]
      simp [this]
  -- the majorant
  set Mj : ℝ × ℝ → ℝ := fun z => x ^ α / c * (Set.indicator (Ioo (0:ℝ) 1) bh z.1 * Set.indicator S bh z.2) with hMj
  have hMjint : Integrable Mj volume := by
    rw [Measure.volume_eq_prod]
    exact (hbhat.mul_prod hbS).const_mul _
  have hpos : ∀ w : ℝ, 0 ≤ Set.indicator (Ioo (0:ℝ) 1) bh w := by
    intro w
    by_cases hw : w ∈ Ioo (0:ℝ) 1
    · rw [Set.indicator_of_mem hw]; exact vg_bh_nonneg hα0 hx hw
    · rw [Set.indicator_of_notMem hw]
  have hposS : ∀ w : ℝ, 0 ≤ Set.indicator S bh w := by
    intro w
    by_cases hw : w ∈ S
    · rw [Set.indicator_of_mem hw]; exact vg_bh_nonneg hα0 hx (hSsub hw)
    · rw [Set.indicator_of_notMem hw]
  have hle : ∀ z, W z ≤ Mj z := by
    intro z
    have hM0 : 0 ≤ Mj z := by
      have := hpos z.1; have := hposS z.2
      simp only [hMj]; positivity
    by_cases hz : z ∈ univ ×ˢ S
    · rw [hW, Set.indicator_of_mem hz]
      by_cases hzT : z ∈ T
      · rw [hHh, Set.indicator_of_mem hzT]
        obtain ⟨-, h1⟩ := vg_H_bd hα0 hx hc hT' hzT.1 hzT.2.1 hzT.2.2
        refine h1.trans (le_of_eq ?_)
        have e1 : z.1 ∈ Ioo (0:ℝ) 1 := ⟨hzT.1, by linarith [hzT.2.1, hzT.2.2]⟩
        simp only [hMj]
        rw [Set.indicator_of_mem e1, Set.indicator_of_mem hz.2]
      · rw [hHh, Set.indicator_of_notMem hzT]; exact hM0
    · rw [hW, Set.indicator_of_notMem hz]; exact hM0
  have hMjval : ∫ z : ℝ × ℝ, Mj z = x ^ α / c * ((∫ p in Ioo (0:ℝ) 1, bh p) * ∫ p in S, bh p) := by
    simp only [hMj]
    rw [integral_const_mul]
    congr 1
    rw [Measure.volume_eq_prod, integral_prod_mul, integral_indicator measurableSet_Ioo, integral_indicator hSm]
  have hW0 : ∀ z, 0 ≤ W z := by
    intro z
    by_cases hz : z ∈ univ ×ˢ S
    · rw [hW, Set.indicator_of_mem hz]
      by_cases hzT : z ∈ T
      · rw [hHh, Set.indicator_of_mem hzT]
        exact (vg_H_bd hα0 hx hc hT' hzT.1 hzT.2.1 hzT.2.2).1
      · rw [hHh, Set.indicator_of_notMem hzT]
    · rw [hW, Set.indicator_of_notMem hz]
  refine ⟨hWeq ▸ integral_nonneg hW0, ?_⟩
  calc ∫ q in S, q * ∫ ρ in Ioo (0:ℝ) 1,
        (profF α x q - profF α x (ρ * q)) / (q - ρ * q) * Real.sqrt (profU α (ρ * q) / profU α q)
      = ∫ z : ℝ × ℝ, W z := hWeq.symm
    _ ≤ ∫ z : ℝ × ℝ, Mj z := integral_mono hWint hMjint hle
    _ = _ := hMjval


private lemma vg_bhS {α : ℝ} (hα0 : 0 < α) :
    ∃ M2 : ℝ, ∀ x : ℝ, 0 < x →
      ∫ p in Ioo (1 / 2 : ℝ) 1, Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p ≤ M2 := by
  obtain ⟨A2, hA2, hL⟩ := vg_bh_large hα0
  refine ⟨∫ p in Ioo (1 / 2 : ℝ) 1, A2 * (1 - p) ^ (-(1 / 2 : ℝ)), fun x hx => ?_⟩
  have hSsub : Ioo (1 / 2 : ℝ) 1 ⊆ Ioo (0:ℝ) 1 := fun q hq => ⟨by linarith [hq.1], hq.2⟩
  have hbi : IntegrableOn (fun p : ℝ => A2 * (1 - p) ^ (-(1 / 2 : ℝ))) (Ioo (1 / 2) 1) :=
    vg_int_one_sub_Ioo.const_mul A2
  have hmeas : IntegrableOn (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p)
      (Ioo (1 / 2) 1) := by
    refine Integrable.mono' hbi ?_ ?_
    · exact ((vg_bh_cont hα0 hx).mono hSsub).aestronglyMeasurable measurableSet_Ioo
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun p hp => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (vg_bh_nonneg hα0 hx (hSsub hp))]
      exact hL x p hx hp.1.le hp.2
  exact setIntegral_mono_on hmeas hbi measurableSet_Ioo (fun p hp => hL x p hx hp.1.le hp.2)

private lemma vg_Hi_small {α : ℝ} (hα1 : 1 < α) :
    ∃ C' : ℝ, ∀ x : ℝ, 0 < x → x ≤ 1 →
      0 ≤ ∫ q in Ioo (1 / 2 : ℝ) 1, q * ∫ ρ in Ioo (0:ℝ) 1,
        (profF α x q - profF α x (ρ * q)) / (q - ρ * q) * Real.sqrt (profU α (ρ * q) / profU α q) ∧
      ∫ q in Ioo (1 / 2 : ℝ) 1, q * ∫ ρ in Ioo (0:ℝ) 1,
        (profF α x q - profF α x (ρ * q)) / (q - ρ * q) * Real.sqrt (profU α (ρ * q) / profU α q) ≤
      C' * x ^ ((α + 3) / 4) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨M, hMpos, hM⟩ := vg_bh_int hα1 (a := 3 * ((α - 1) / 2) / 2) (by linarith) (by linarith)
  obtain ⟨M2, hM2⟩ := vg_bhS hα0
  obtain ⟨c, C0, hc, -, hT⟩ := lem_app_pl_continuum_ii hα0
  have hT' : ∀ V : ℝ, 0 < V → c * (contS α V * (1 - contS α V)) ≤ Tcont α V :=
    fun V hV => (hT V hV).1
  refine ⟨M * M2 / c, fun x hx hx1 => ?_⟩
  obtain ⟨h0, h1⟩ := vg_Hi_bd hα1 hx hx1 hc hT'
  refine ⟨h0, ?_⟩
  obtain ⟨-, hMb⟩ := hM x hx hx1
  have hB1 : 0 ≤ ∫ p in Ioo (0:ℝ) 1, Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p :=
    setIntegral_nonneg measurableSet_Ioo (fun p hp => vg_bh_nonneg hα0 hx hp)
  have hB2 : 0 ≤ ∫ p in Ioo (1 / 2 : ℝ) 1, Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p :=
    setIntegral_nonneg measurableSet_Ioo (fun p hp => vg_bh_nonneg hα0 hx ⟨by linarith [hp.1], hp.2⟩)
  have hS2 := hM2 x hx
  refine h1.trans ?_
  have hxa : x ^ α * x ^ (-(3 * ((α - 1) / 2) / 2)) = x ^ ((α + 3) / 4) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have hxn : 0 ≤ x ^ α / c := by positivity
  calc x ^ α / c * ((∫ p in Ioo (0:ℝ) 1, Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p) *
        ∫ p in Ioo (1 / 2 : ℝ) 1, Real.sqrt ((1 - p) / (p * contV α p)) / (1 - p) * profF α x p)
      ≤ x ^ α / c * ((M * x ^ (-(3 * ((α - 1) / 2) / 2))) * M2) := by
        gcongr
    _ = (M * M2 / c) * x ^ ((α + 3) / 4) := by
        rw [← hxa]; field_simp


open Muon.DetEquiv ProbabilityTheory in
private lemma vg_F_rep {α x ρ q : ℝ} (hα0 : 0 < α) (hx : 0 < x) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    (profF α x q - profF α x (ρ * q)) / (q - ρ * q) * Real.sqrt (profU α (ρ * q) / profU α q) =
      Real.sqrt (ρ⁻¹ * ((1 - ρ * q) * (1 - q)) /
          ((contV α (ρ * q) / x ^ α) * (contV α q / x ^ α))) *
        ((contV α (ρ * q) / x ^ α) / (contV α (ρ * q) / x ^ α + 1)) *
        ((contV α q / x ^ α) / (contV α q / x ^ α + 1)) *
        ((1 - (contV α (ρ * q) / x ^ α) / (contV α q / x ^ α)) / ((1 - ρ * q) * (1 - ρ))) / q := by
  have hp0 : 0 < ρ * q := mul_pos hρ0 hq0
  have hpq : ρ * q < q := by nlinarith
  have hpI : ρ * q ∈ Ioo (0:ℝ) 1 := ⟨hp0, by linarith⟩
  have hqI : q ∈ Ioo (0:ℝ) 1 := ⟨hq0, hq1⟩
  have hVp := (vg_V_spec hα0 hpI).1
  have hVq := (vg_V_spec hα0 hqI).1
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hconc := vg_h_conc hα0 hx hp0 hpq hq1
  have h1p : 0 < 1 - ρ * q := by linarith
  have h1q : 0 < 1 - q := by linarith
  have h1r : 0 < 1 - ρ := by linarith
  rw [div_eq_iff hs.ne'] at hconc
  rw [hconc]
  set Vp := contV α (ρ * q) with hVpdef
  set Vq := contV α q with hVqdef
  have hP : Real.sqrt ((1 - ρ * q) / (ρ * q * Vp)) * Real.sqrt ((1 - q) / (q * Vq)) * (x ^ α * q) =
      Real.sqrt (ρ⁻¹ * ((1 - ρ * q) * (1 - q)) / ((Vp / x ^ α) * (Vq / x ^ α))) := by
    rw [← Real.sqrt_mul (by positivity)]
    have : (x ^ α * q) = Real.sqrt ((x ^ α * q) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    rw [this, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hf : ∀ V : ℝ, 0 < V → V / (V + x ^ α) = (V / x ^ α) / (V / x ^ α + 1) := by
    intro V hV
    field_simp
  unfold profF
  rw [hf Vp hVp, hf Vq hVq]
  have hD : (1 - (Vp / x ^ α) / (Vq / x ^ α)) / ((1 - ρ * q) * (1 - ρ)) =
      q * (Vq - Vp) / ((1 - ρ * q) * Vq * (q - ρ * q)) := by
    have : q - ρ * q = q * (1 - ρ) := by ring
    rw [this]
    field_simp
  rw [← hD]
  rw [← hP]
  field_simp


private lemma vg_lim_alg {α ρ y : ℝ} (hα0 : 0 < α) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hy : 0 < y) :
    Real.sqrt (ρ⁻¹ * ((1 - 0) * (1 - 0)) / ((ρ * y) ^ α * y ^ α)) *
      ((ρ * y) ^ α / ((ρ * y) ^ α + 1)) * (y ^ α / (y ^ α + 1)) *
      ((1 - (ρ * y) ^ α / y ^ α) / ((1 - 0) * (1 - ρ))) =
    ρ ^ ((α - 1) / 2) * y ^ α * ((1 - ρ ^ α) / (1 - ρ)) /
      (((ρ * y) ^ α + 1) * (y ^ α + 1)) := by
  simp only [sub_zero, one_mul, mul_one]
  have hra := Real.rpow_pos_of_pos hρ0 α
  have hya := Real.rpow_pos_of_pos hy α
  have h1r : 0 < 1 - ρ := by linarith
  have hu : (ρ * y) ^ α = ρ ^ α * y ^ α := Real.mul_rpow hρ0.le hy.le
  have hrho : Real.sqrt (ρ ^ α / ρ) = ρ ^ ((α - 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub_one hρ0.ne', ← Real.rpow_mul hρ0.le]
    congr 1; ring
  rw [hu, ← hrho]
  have hs12 : Real.sqrt (ρ * ρ ^ α) * Real.sqrt (ρ ^ α / ρ) = ρ ^ α := by
    rw [← Real.sqrt_mul (by positivity)]
    have : ρ * ρ ^ α * (ρ ^ α / ρ) = (ρ ^ α) ^ 2 := by field_simp
    rw [this, Real.sqrt_sq hra.le]
  have hs1 : 0 < Real.sqrt (ρ * ρ ^ α) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt (ρ⁻¹ / (ρ ^ α * y ^ α * y ^ α)) =
      (y ^ α * Real.sqrt (ρ * ρ ^ α))⁻¹ := by
    have : ρ⁻¹ / (ρ ^ α * y ^ α * y ^ α) =
        ((y ^ α * Real.sqrt (ρ * ρ ^ α))⁻¹) ^ 2 := by
      rw [inv_pow, mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  rw [hsq]
  generalize Real.sqrt (ρ * ρ ^ α) = s1 at *
  generalize Real.sqrt (ρ ^ α / ρ) = s2 at *
  generalize ρ ^ α = r at *
  subst hs12
  field_simp


open Muon.DetEquiv ProbabilityTheory in
private lemma vg_F_eq_at {α x ρ y : ℝ} (hα0 : 0 < α) (hx : 0 < x) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hy : 0 < y) (hq : x * Kc α * y ≤ 1 / 2) (hK : 0 < Kc α) :
    Set.indicator {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ x * Kc α * z.2 ≤ 1 / 2}
      (fun z : ℝ × ℝ => Kc α * (x * Kc α * z.2) *
        ((profF α x (x * Kc α * z.2) - profF α x (z.1 * (x * Kc α * z.2))) /
          (x * Kc α * z.2 - z.1 * (x * Kc α * z.2)) *
          Real.sqrt (profU α (z.1 * (x * Kc α * z.2)) / profU α (x * Kc α * z.2)))) (ρ, y) =
    Kc α * (Real.sqrt (ρ⁻¹ * ((1 - ρ * (x * Kc α * y)) * (1 - x * Kc α * y)) /
        ((contV α (ρ * (x * Kc α * y)) / x ^ α) * (contV α (x * Kc α * y) / x ^ α))) *
      ((contV α (ρ * (x * Kc α * y)) / x ^ α) / (contV α (ρ * (x * Kc α * y)) / x ^ α + 1)) *
      ((contV α (x * Kc α * y) / x ^ α) / (contV α (x * Kc α * y) / x ^ α + 1)) *
      ((1 - (contV α (ρ * (x * Kc α * y)) / x ^ α) / (contV α (x * Kc α * y) / x ^ α)) /
        ((1 - ρ * (x * Kc α * y)) * (1 - ρ)))) := by
  have hq0 : 0 < x * Kc α * y := by positivity
  have hmem : (ρ, y) ∈ {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ x * Kc α * z.2 ≤ 1 / 2} :=
    ⟨hρ0, hρ1, hy, hq⟩
  rw [Set.indicator_of_mem hmem]
  have := vg_F_rep hα0 hx hρ0 hρ1 hq0 (by linarith)
  simp only []
  rw [this]
  field_simp

open Muon.DetEquiv ProbabilityTheory in
private lemma vg_F_lim {α ρ y : ℝ} (hα1 : 1 < α) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hy : 0 < y) :
    Tendsto (fun x : ℝ => Set.indicator
      {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ x * Kc α * z.2 ≤ 1 / 2}
      (fun z : ℝ × ℝ => Kc α * (x * Kc α * z.2) *
        ((profF α x (x * Kc α * z.2) - profF α x (z.1 * (x * Kc α * z.2))) /
          (x * Kc α * z.2 - z.1 * (x * Kc α * z.2)) *
          Real.sqrt (profU α (z.1 * (x * Kc α * z.2)) / profU α (x * Kc α * z.2)))) (ρ, y))
      (𝓝[>] (0:ℝ))
      (𝓝 (Kc α * (ρ ^ ((α - 1) / 2) * y ^ α * ((1 - ρ ^ α) / (1 - ρ)) /
        (((ρ * y) ^ α + 1) * (y ^ α + 1))))) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  have hKy : 0 < Kc α * y := by positivity
  -- ingredients
  have hq : Tendsto (fun x : ℝ => x * Kc α * y) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => x * Kc α * y) (𝓝 0) (𝓝 (0 * Kc α * y)) :=
      ((continuous_id.mul continuous_const).mul continuous_const).tendsto 0
    rw [zero_mul, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun x : ℝ => ρ * (x * Kc α * y)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using hq.const_mul ρ
  have ha : Tendsto (fun x : ℝ => contV α (ρ * (x * Kc α * y)) / x ^ α) (𝓝[>] (0:ℝ))
      (𝓝 ((ρ * y) ^ α)) := by
    have := vg_R_lim hα1 (a := ρ * Kc α * y) (by positivity)
    have e : (ρ * Kc α * y / Kc α) = ρ * y := by field_simp
    rw [e] at this
    refine this.congr' ?_
    filter_upwards with x
    congr 2; ring
  have hb : Tendsto (fun x : ℝ => contV α (x * Kc α * y) / x ^ α) (𝓝[>] (0:ℝ))
      (𝓝 (y ^ α)) := by
    have := vg_R_lim hα1 (a := Kc α * y) hKy
    have e : (Kc α * y / Kc α) = y := by field_simp
    rw [e] at this
    refine this.congr' ?_
    filter_upwards with x
    congr 2; ring
  have hra := Real.rpow_pos_of_pos (mul_pos hρ0 hy) α
  have hya := Real.rpow_pos_of_pos hy α
  have h1r : 0 < 1 - ρ := by linarith
  have hΦ := (((((((tendsto_const_nhds (x := ρ⁻¹)).mul (((tendsto_const_nhds (x := (1:ℝ))).sub hp).mul
      ((tendsto_const_nhds (x := (1:ℝ))).sub hq))).div (ha.mul hb) (by positivity)).sqrt).mul
      (ha.div (ha.add_const 1) (by positivity))).mul (hb.div (hb.add_const 1) (by positivity))).mul
      (((tendsto_const_nhds (x := (1:ℝ))).sub (ha.div hb (by positivity))).div
        (((tendsto_const_nhds (x := (1:ℝ))).sub hp).mul (tendsto_const_nhds (x := 1 - ρ))) (by simp; positivity)))
  have hΦ' := hΦ.const_mul (Kc α)
  have hlim := vg_lim_alg hα0 hρ0 hρ1 hy
  rw [hlim] at hΦ'
  refine hΦ'.congr' ?_
  have hev : ∀ᶠ x in 𝓝[>] (0:ℝ), 0 < x ∧ x * Kc α * y ≤ 1 / 2 := by
    filter_upwards [self_mem_nhdsWithin, hq.eventually (Iic_mem_nhds (by norm_num : (0:ℝ) < 1 / 2))] with x hx hx2
    exact ⟨hx, hx2⟩
  filter_upwards [hev] with x hx
  exact (vg_F_eq_at hα0 hx.1 hρ0 hρ1 hy hx.2 hK).symm

open Muon.DetEquiv ProbabilityTheory in
private lemma vg_Lo_lim {α : ℝ} (hα1 : 1 < α) :
    Tendsto (fun x : ℝ => ∫ z : ℝ × ℝ, Set.indicator
      {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ x * Kc α * z.2 ≤ 1 / 2}
      (fun z : ℝ × ℝ => Kc α * (x * Kc α * z.2) *
        ((profF α x (x * Kc α * z.2) - profF α x (z.1 * (x * Kc α * z.2))) /
          (x * Kc α * z.2 - z.1 * (x * Kc α * z.2)) *
          Real.sqrt (profU α (z.1 * (x * Kc α * z.2)) / profU α (x * Kc α * z.2)))) z
      ∂((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))))
      (𝓝[>] (0:ℝ))
      (𝓝 (∫ z : ℝ × ℝ, Kc α * (z.1 ^ ((α - 1) / 2) * z.2 ^ α * ((1 - z.1 ^ α) / (1 - z.1)) /
        (((z.1 * z.2) ^ α + 1) * (z.2 ^ α + 1)))
      ∂((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))))) := by
  obtain ⟨Cb, hCb, hF⟩ := vg_F_bd hα1
  refine tendsto_integral_filter_of_dominated_convergence
    (bound := fun z : ℝ × ℝ => Cb * (z.1 ^ ((α - 1) / 4 - 1) *
      (if z.2 ≤ 1 then z.2 ^ α else z.2 ^ (-((α - 1) / 4) - 1)))) ?_ ?_ (vg_maj_int hα1) ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact vg_Fl_meas hα1 hx
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0:ℝ) < x := hx
    filter_upwards [vg_ae_mem (μ := volume) (ν := volume) measurableSet_Ioo measurableSet_Ioi] with z hz
    have hρ : 0 < z.1 ∧ z.1 < 1 := hz.1
    have hy : 0 < z.2 := hz.2
    have hnn : 0 ≤ Cb * (z.1 ^ ((α - 1) / 4 - 1) *
        (if z.2 ≤ 1 then z.2 ^ α else z.2 ^ (-((α - 1) / 4) - 1))) := by
      have := hρ.1; have := hy
      split_ifs <;> positivity
    by_cases hq : x * Kc α * z.2 ≤ 1 / 2
    · rw [Set.indicator_of_mem (show z ∈ {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ x * Kc α * z.2 ≤ 1 / 2}
        from ⟨hρ.1, hρ.2, hy, hq⟩), Real.norm_eq_abs]
      obtain ⟨h0, h1⟩ := hF x z.1 z.2 hx' hρ.1 hρ.2 hy hq
      rw [abs_of_nonneg h0]; exact h1
    · rw [Set.indicator_of_notMem (fun h => hq h.2.2.2), norm_zero]; exact hnn
  · filter_upwards [vg_ae_mem (μ := volume) (ν := volume) measurableSet_Ioo measurableSet_Ioi] with z hz
    exact vg_F_lim hα1 hz.1.1 hz.1.2 hz.2


private lemma vg_J {α : ℝ} (hα1 : 1 < α) : ∫ s in Ioi (0:ℝ), 1 / (1 + s ^ α) = Kc α := by
  have hα0 : 0 < α := by linarith
  have hne : α ≠ 0 := hα0.ne'
  have hsinpos : 0 < Real.sin (Real.pi / α) := by
    apply Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hα0)
    rw [div_lt_iff₀ hα0]
    nlinarith [Real.pi_pos]
  have hb1 : 0 < 1 / α := one_div_pos.mpr hα0
  have hb2 : 0 < 1 - 1 / α := by
    have : 1 / α < 1 := by rw [div_lt_one hα0]; exact hα1
    linarith
  unfold Kc
  have hb := Muon.Foundations.betaHalfLine hb1 hb2
  rw [show (1 / α + (1 - 1 / α)) = (1:ℝ) by ring] at hb
  simp only [Real.rpow_neg_one] at hb
  rw [Real.Gamma_one, div_one, Real.Gamma_mul_Gamma_one_sub, mul_one_div] at hb
  have hcv : ∫ x in Ioi (0:ℝ), (α * x ^ (α - 1)) • ((x ^ α) ^ (1 / α - 1) * (1 + x ^ α)⁻¹)
      = ∫ y in Ioi (0:ℝ), y ^ (1 / α - 1) * (1 + y)⁻¹ :=
    integral_comp_rpow_Ioi_of_pos (g := fun y : ℝ => y ^ (1 / α - 1) * (1 + y)⁻¹) hα0
  have hpt : ∀ x ∈ Ioi (0:ℝ), (α * x ^ (α - 1)) • ((x ^ α) ^ (1 / α - 1) * (1 + x ^ α)⁻¹)
      = α * (1 / (1 + x ^ α)) := by
    intro x hx
    have hx' : (0:ℝ) < x := hx
    have e1 : (x ^ α) ^ (1 / α - 1) = x ^ (1 - α) := by
      rw [← Real.rpow_mul hx'.le, mul_sub, mul_one_div_cancel hne, mul_one]
    have e2 : x ^ (α - 1) * x ^ (1 - α) = 1 := by
      rw [← Real.rpow_add hx', show α - 1 + (1 - α) = 0 by ring, Real.rpow_zero]
    rw [smul_eq_mul, e1]
    linear_combination (α * (1 + x ^ α)⁻¹) * e2
  have hcongr := setIntegral_congr_fun (μ := volume) measurableSet_Ioi hpt
  rw [hcv, integral_const_mul] at hcongr
  rw [hb] at hcongr
  field_simp at hcongr ⊢
  linarith

private lemma vg_J_int {α : ℝ} (hα1 : 1 < α) : IntegrableOn (fun s : ℝ => 1 / (1 + s ^ α)) (Ioi 0) := by
  by_contra hn
  have := vg_J hα1
  rw [integral_undef hn] at this
  have := vg_K_pos hα1
  linarith


private lemma vg_inner_y {α ρ : ℝ} (hα1 : 1 < α) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∫ y in Ioi (0:ℝ), y ^ α / (((ρ * y) ^ α + 1) * (y ^ α + 1)) =
      Kc α * (1 - ρ) / (ρ * (1 - ρ ^ α)) := by
  have hα0 : 0 < α := by linarith
  have hra : ρ ^ α < 1 := Real.rpow_lt_one hρ0.le hρ1 hα0
  have hra0 : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ0 α
  have h1 : 0 < 1 - ρ ^ α := by linarith
  have hJi := vg_J_int hα1
  have hJ := vg_J hα1
  have hi1 : IntegrableOn (fun y : ℝ => 1 / (1 + (ρ * y) ^ α)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun s : ℝ => 1 / (1 + s ^ α)) 0 hρ0).2
      (by rwa [mul_zero])
    exact this
  have hc1 : ∫ y in Ioi (0:ℝ), 1 / (1 + (ρ * y) ^ α) = Kc α / ρ := by
    have := integral_comp_mul_left_Ioi (fun s : ℝ => 1 / (1 + s ^ α)) 0 hρ0
    rw [mul_zero, hJ, smul_eq_mul] at this
    rw [this]; field_simp
  have hpt : ∀ y ∈ Ioi (0:ℝ), y ^ α / (((ρ * y) ^ α + 1) * (y ^ α + 1)) =
      (1 / (1 - ρ ^ α)) * (1 / (1 + (ρ * y) ^ α) - 1 / (1 + y ^ α)) := by
    intro y hy
    have hya : 0 < y ^ α := Real.rpow_pos_of_pos hy α
    rw [Real.mul_rpow hρ0.le (le_of_lt hy)]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, integral_sub hi1 hJi, hc1, hJ]
  field_simp


private lemma vg_I0 {α : ℝ} (hα1 : 1 < α) :
    ∫ z : ℝ × ℝ, Kc α * (z.1 ^ ((α - 1) / 2) * z.2 ^ α * ((1 - z.1 ^ α) / (1 - z.1)) /
        (((z.1 * z.2) ^ α + 1) * (z.2 ^ α + 1)))
      ∂((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))) =
    Kc α ^ 2 * (2 / (α - 1)) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  set f : ℝ × ℝ → ℝ := fun z => Kc α * (z.1 ^ ((α - 1) / 2) * z.2 ^ α * ((1 - z.1 ^ α) / (1 - z.1)) /
        (((z.1 * z.2) ^ α + 1) * (z.2 ^ α + 1))) with hf
  -- integrability
  have hint : Integrable f ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))) := by
    obtain ⟨Cb, hCb, hF⟩ := vg_F_bd hα1
    have hmeas : Measurable f := by
      simp only [hf]
      fun_prop
    refine Integrable.mono' (vg_maj_int (Cb := Cb) hα1) hmeas.aestronglyMeasurable ?_
    filter_upwards [vg_ae_mem (μ := volume) (ν := volume) measurableSet_Ioo measurableSet_Ioi] with z hz
    have hρ : 0 < z.1 ∧ z.1 < 1 := hz.1
    have hy : 0 < z.2 := hz.2
    have hpos : 0 ≤ f z := by
      simp only [hf]
      have h1 := Real.rpow_pos_of_pos hρ.1 ((α - 1) / 2)
      have h2 := Real.rpow_pos_of_pos hy α
      have h4 : 0 ≤ 1 - z.1 ^ α := by
        have := Real.rpow_lt_one hρ.1.le hρ.2 hα0
        linarith
      have h5 : 0 < 1 - z.1 := by linarith
      have h6 := Real.rpow_pos_of_pos (mul_pos hρ.1 hy) α
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    refine le_of_tendsto (vg_F_lim hα1 hρ.1 hρ.2 hy) ?_
    filter_upwards [self_mem_nhdsWithin, (show Tendsto (fun x : ℝ => x * Kc α * z.2) (𝓝[>] (0:ℝ)) (𝓝 0) from by
      have : Tendsto (fun x : ℝ => x * Kc α * z.2) (𝓝 0) (𝓝 (0 * Kc α * z.2)) :=
        ((continuous_id.mul continuous_const).mul continuous_const).tendsto 0
      rw [zero_mul, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds).eventually (Iic_mem_nhds (by norm_num : (0:ℝ) < 1 / 2))]
      with x hx hx2
    have hx' : (0:ℝ) < x := hx
    have hmem : (z.1, z.2) ∈ {w : ℝ × ℝ | 0 < w.1 ∧ w.1 < 1 ∧ 0 < w.2 ∧ x * Kc α * w.2 ≤ 1 / 2} :=
      ⟨hρ.1, hρ.2, hy, hx2⟩
    rw [Set.indicator_of_mem hmem]
    exact (hF x z.1 z.2 hx' hρ.1 hρ.2 hy hx2).2
  rw [integral_prod _ hint]
  have hinner : ∀ ρ ∈ Ioo (0:ℝ) 1, ∫ y in Ioi (0:ℝ), f (ρ, y) = Kc α ^ 2 * ρ ^ ((α - 1) / 2 - 1) := by
    intro ρ hρ
    have hra : ρ ^ α < 1 := Real.rpow_lt_one hρ.1.le hρ.2 hα0
    have h1 : 0 < 1 - ρ ^ α := by linarith
    have h5 : 0 < 1 - ρ := by linarith [hρ.2]
    have e : ∀ y : ℝ, f (ρ, y) = Kc α * (ρ ^ ((α - 1) / 2) * ((1 - ρ ^ α) / (1 - ρ))) *
        (y ^ α / (((ρ * y) ^ α + 1) * (y ^ α + 1))) := by
      intro y; simp only [hf]; ring
    simp_rw [e]
    rw [integral_const_mul, vg_inner_y hα1 hρ.1 hρ.2, Real.rpow_sub_one hρ.1.ne']
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hinner, integral_const_mul]
  have : ∫ ρ in Ioo (0:ℝ) 1, ρ ^ ((α - 1) / 2 - 1) = 2 / (α - 1) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith))]
    rw [Real.one_rpow, Real.zero_rpow (by linarith)]
    field_simp
    ring
  rw [this]


open Muon.DetEquiv ProbabilityTheory in
private lemma vg_Gamma_lim {α : ℝ} (hα1 : 1 < α) :
    Tendsto (fun x : ℝ => profGamma α x / x) (𝓝[>] (0:ℝ)) (𝓝 (4 * Kc α ^ 2 / (α - 1))) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨C', hC'⟩ := vg_Hi_small hα1
  have hHi : Tendsto (fun x : ℝ => (∫ q in Ioo (1 / 2 : ℝ) 1, q * ∫ ρ in Ioo (0:ℝ) 1,
      (profF α x q - profF α x (ρ * q)) / (q - ρ * q) * Real.sqrt (profU α (ρ * q) / profU α q)) / x)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hexp : 0 < (α + 3) / 4 - 1 := by linarith
    have hlim : Tendsto (fun x : ℝ => C' * x ^ ((α + 3) / 4 - 1)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hc : Continuous fun x : ℝ => C' * x ^ ((α + 3) / 4 - 1) :=
        continuous_const.mul (Real.continuous_rpow_const hexp.le)
      have := hc.tendsto 0
      rw [Real.zero_rpow hexp.ne', mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with x hx
      exact div_nonneg (hC' x hx.1 hx.2).1 hx.1.le
    · filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with x hx
      rw [div_le_iff₀ hx.1]
      refine (hC' x hx.1 hx.2).2.trans (le_of_eq ?_)
      rw [mul_assoc, ← Real.rpow_add_one hx.1.ne']
      congr 2; ring
  have hLo := (vg_Lo_lim hα1).const_mul 2
  rw [vg_I0 hα1] at hLo
  have hsum := hLo.add (hHi.const_mul 2)
  have e : 2 * (Kc α ^ 2 * (2 / (α - 1))) + 2 * 0 = 4 * Kc α ^ 2 / (α - 1) := by ring
  rw [e] at hsum
  refine hsum.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with x hx
  obtain ⟨hrep, hJint⟩ := vg_repr hα1 hx.1 hx.2
  set J : ℝ → ℝ := fun q => q * ∫ ρ in Ioo (0:ℝ) 1,
      (profF α x q - profF α x (ρ * q)) / (q - ρ * q) * Real.sqrt (profU α (ρ * q) / profU α q) with hJ
  have hsplit : Ioo (0:ℝ) 1 = Ioc 0 (1 / 2) ∪ Ioo (1 / 2) 1 := by
    ext q; simp only [mem_Ioo, mem_union, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : q ≤ 1 / 2
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨not_le.1 h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨by linarith, h2⟩
  have hdis : Disjoint (Ioc (0:ℝ) (1 / 2)) (Ioo (1 / 2) 1) :=
    Set.disjoint_left.2 fun q h1 h2 => by linarith [h1.2, h2.1]
  have hJ1 : IntegrableOn J (Ioc (0:ℝ) (1 / 2)) :=
    hJint.mono_set (by rw [hsplit]; exact subset_union_left)
  have hJ2 : IntegrableOn J (Ioo (1 / 2 : ℝ) 1) :=
    hJint.mono_set (by rw [hsplit]; exact subset_union_right)
  have hint_split : ∫ q in Ioo (0:ℝ) 1, J q = (∫ q in Ioc (0:ℝ) (1 / 2), J q) + ∫ q in Ioo (1 / 2 : ℝ) 1, J q := by
    conv_lhs => rw [hsplit]
    exact setIntegral_union hdis measurableSet_Ioo hJ1 hJ2
  have hLoeq : ∫ q in Ioc (0:ℝ) (1 / 2), J q = x * ∫ z : ℝ × ℝ, Set.indicator
      {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ x * Kc α * z.2 ≤ 1 / 2}
      (fun z : ℝ × ℝ => Kc α * (x * Kc α * z.2) *
        ((profF α x (x * Kc α * z.2) - profF α x (z.1 * (x * Kc α * z.2))) /
          (x * Kc α * z.2 - z.1 * (x * Kc α * z.2)) *
          Real.sqrt (profU α (z.1 * (x * Kc α * z.2)) / profU α (x * Kc α * z.2)))) z
      ∂((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))) := vg_Lo_eq hα1 hx.1
  rw [hrep, hint_split, hLoeq]
  have key : ∀ (I H x : ℝ), x ≠ 0 → 2 * I + 2 * (H / x) = 2 * (x * I + H) / x := by
    intro I H x hx0; field_simp
  exact key _ _ _ hx.1.ne'

/-! ## Private helpers for the large-`X` endpoint -/

/-- The age-weighted elasticity decreases under dilation, after replacing it by its
uniform bound. This is the one-variable estimate needed for large-`X` tails. -/
private lemma vi_theta_weight_bd {K X r θ : ℝ} (hK : 0 < K) (hX : 1 ≤ X)
    (hr : 0 < r) (hθ : θ ≤ K / min (X * r) 1) :
    θ * min (Real.sqrt (X * r)) 1 ≤
      (K / min r 1) * min (Real.sqrt r) 1 := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hur : 0 < X * r := mul_pos hX0 hr
  have hw : 0 < min (Real.sqrt r) 1 := lt_min (Real.sqrt_pos.2 hr) one_pos
  have hwX : 0 < min (Real.sqrt (X * r)) 1 :=
    lt_min (Real.sqrt_pos.2 hur) one_pos
  have hwle : min (Real.sqrt r) 1 ≤ min (Real.sqrt (X * r)) 1 := by
    apply min_le_min_right
    apply Real.sqrt_le_sqrt
    nlinarith
  have hθ' : θ ≤ K / min (Real.sqrt (X * r)) 1 ^ 2 := by
    simpa only [vs_w_sq hur] using hθ
  calc θ * min (Real.sqrt (X * r)) 1 ≤
        (K / min (Real.sqrt (X * r)) 1 ^ 2) * min (Real.sqrt (X * r)) 1 :=
      mul_le_mul_of_nonneg_right hθ' hwX.le
    _ = K / min (Real.sqrt (X * r)) 1 := by field_simp
    _ ≤ K / min (Real.sqrt r) 1 := div_le_div_of_nonneg_left hK.le hw hwle
    _ = (K / min r 1) * min (Real.sqrt r) 1 := by
      rw [← vs_w_sq hr]
      field_simp

private lemma vi_g_bd {α K X r θ : ℝ} (hα0 : 0 < α) (hK : 0 < K)
    (hX : 1 ≤ X) (hr : 0 < r) (hθ : θ ≤ K / min (X * r) 1) :
    r ^ (α / 2) / (1 + r ^ α) * θ * min (Real.sqrt (X * r)) 1 / Real.sqrt r ≤
      if r ≤ 1 then K * r ^ (α / 2 - 1) else K * r ^ (-((α + 1) / 2)) := by
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hra := Real.rpow_pos_of_pos hr α
  have hrh := Real.rpow_pos_of_pos hr (α / 2)
  have hmin : 0 < min r 1 := lt_min hr one_pos
  have hbd := vz_g_bd (α := α) (K := K) (X := 1) (θ := K / min r 1)
    hα0 zero_lt_one le_rfl hr (div_pos hK hmin) (by simp)
  simp only [one_mul, Real.sqrt_one] at hbd
  refine le_trans ?_ hbd
  have hw := vi_theta_weight_bd hK hX hr hθ
  calc r ^ (α / 2) / (1 + r ^ α) * θ * min (Real.sqrt (X * r)) 1 / Real.sqrt r
      ≤ r ^ (α / 2) / (1 + r ^ α) *
          ((K / min r 1) * min (Real.sqrt r) 1) / Real.sqrt r := by
        exact div_le_div_of_nonneg_right
          (by nlinarith [mul_le_mul_of_nonneg_left hw (by positivity :
            0 ≤ r ^ (α / 2) / (1 + r ^ α))]) hsr.le
    _ = _ := by field_simp

open Muon.DetEquiv ProbabilityTheory in
/-- A uniform integrable product majorant for the normalized large-`X` lag sum. -/
private lemma vi_tsum_bd {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧ ∀ X r s : ℝ, 1 ≤ X → 0 < r → 0 < s →
      Summable (fun ℓ : ℤ =>
        ((r ^ (α / 2) / (1 + r ^ α)) * (s ^ (α / 2) / (1 + s ^ α)) / Real.sqrt (r * s)) *
          (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ *
            profTheta α β (X * r) * profTheta α β (X * s) /
              profDelta α β ℓ (X * r) (X * s))) ∧
      (∑' ℓ : ℤ,
        ((r ^ (α / 2) / (1 + r ^ α)) * (s ^ (α / 2) / (1 + s ^ α)) / Real.sqrt (r * s)) *
          (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ *
            profTheta α β (X * r) * profTheta α β (X * s) /
              profDelta α β ℓ (X * r) (X * s))) ≤
        α * C * ((if r ≤ 1 then K * r ^ (α / 2 - 1) else K * r ^ (-((α + 1) / 2))) *
          (if s ≤ 1 then K * s ^ (α / 2 - 1) else K * s ^ (-((α + 1) / 2)))) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨K, hK0, hK⟩ := vs_theta_bd hα1 hβ0 hβ1
  obtain ⟨C, hC0, hC⟩ := vs_D_bd hβ0 hβ1
  refine ⟨K, C, hK0, hC0, fun X r s hX hr hs => ?_⟩
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hu : 0 < X * r := mul_pos hX0 hr
  have hv : 0 < X * s := mul_pos hX0 hs
  obtain ⟨hθr, hθr'⟩ := hK (X * r) hu
  obtain ⟨hθs, hθs'⟩ := hK (X * s) hv
  obtain ⟨hqr, -⟩ := vs_Qm hβ0 hβ1 hu
  obtain ⟨hqs, -⟩ := vs_Qm hβ0 hβ1 hv
  have hra := Real.rpow_pos_of_pos hr α
  have hsa := Real.rpow_pos_of_pos hs α
  have hrh := Real.rpow_pos_of_pos hr (α / 2)
  have hsh := Real.rpow_pos_of_pos hs (α / 2)
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  let A : ℝ := (r ^ (α / 2) / (1 + r ^ α)) * (s ^ (α / 2) / (1 + s ^ α)) /
    Real.sqrt (r * s) * (profTheta α β (X * r) * profTheta α β (X * s))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let f : ℤ → ℝ := fun ℓ =>
    ((r ^ (α / 2) / (1 + r ^ α)) * (s ^ (α / 2) / (1 + s ^ α)) / Real.sqrt (r * s)) *
      (DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ *
        profTheta α β (X * r) * profTheta α β (X * s) /
          profDelta α β ℓ (X * r) (X * s))
  have hterm : ∀ ℓ, 0 ≤ f ℓ ∧ f ℓ ≤ A * α * DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ := by
    intro ℓ
    have hD := vs_DLag_nonneg hβ0 hβ1 hqr.le hqs.le ℓ
    have hΔ := vs_Delta_ge hα1 hβ0 hβ1 hu hv ℓ
    have hΔ0 : 0 < profDelta α β ℓ (X * r) (X * s) :=
      lt_of_lt_of_le (by positivity) hΔ
    have hΔinv : 1 / profDelta α β ℓ (X * r) (X * s) ≤ α := by
      rw [div_le_iff₀ hΔ0]
      have := mul_le_mul_of_nonneg_left hΔ hα0.le
      rw [mul_one_div_cancel hα0.ne'] at this
      nlinarith
    have he : f ℓ = A * DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ *
        (1 / profDelta α β ℓ (X * r) (X * s)) := by dsimp [f, A]; ring
    rw [he]
    refine ⟨by positivity, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_left hΔinv (mul_nonneg hA hD)]
  have hfin : ∀ S : Finset ℤ, ∑ ℓ ∈ S, f ℓ ≤
      α * C * ((if r ≤ 1 then K * r ^ (α / 2 - 1) else K * r ^ (-((α + 1) / 2))) *
        (if s ≤ 1 then K * s ^ (α / 2 - 1) else K * s ^ (-((α + 1) / 2)))) := by
    intro S
    have hgr := vi_g_bd hα0 hK0 hX hr hθr'
    have hgs := vi_g_bd hα0 hK0 hX hs hθs'
    calc ∑ ℓ ∈ S, f ℓ ≤ ∑ ℓ ∈ S, A * α * DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ :=
          Finset.sum_le_sum fun ℓ _ => (hterm ℓ).2
      _ = A * α * ∑ ℓ ∈ S, DLag β (Qm β (X * r)) (Qm β (X * s)) ℓ :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ A * α * (C * min (Real.sqrt (X * r)) 1 * min (Real.sqrt (X * s)) 1) :=
          mul_le_mul_of_nonneg_left (hC (X * r) (X * s) hu hv S) (by positivity)
      _ = α * C *
          ((r ^ (α / 2) / (1 + r ^ α) * profTheta α β (X * r) *
            min (Real.sqrt (X * r)) 1 / Real.sqrt r) *
           (s ^ (α / 2) / (1 + s ^ α) * profTheta α β (X * s) *
            min (Real.sqrt (X * s)) 1 / Real.sqrt s)) := by
          dsimp [A]
          rw [Real.sqrt_mul hr.le]
          ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hα0.le hC0)
          apply mul_le_mul hgr hgs
          · positivity
          · split_ifs <;> positivity
  have hsm := summable_of_sum_le (fun ℓ => (hterm ℓ).1) hfin
  exact ⟨hsm, hsm.tsum_le_of_sum_le hfin⟩

/-- The determinant appearing on the limiting positive-lag shell stays uniformly positive. -/
private lemma vi_shell_delta {α r s : ℝ} (hα1 : 1 < α) (hr : 0 < r) (hrs : r < s) :
    1 / α ≤ 1 - profT α r s / s := by
  have hα0 : 0 < α := by linarith
  have hs : 0 < s := hr.trans hrs
  have hT := vs_T_le hα1 hr hs
  rw [max_eq_right hrs.le] at hT
  have hdiv : profT α r s / s ≤ 1 - 1 / α := by
    rw [div_le_iff₀ hs]
    exact hT
  linarith

/-- Algebra identifying the localized lag integrand with the divided difference
in the paper's half-line shell profile. -/
private lemma vi_shell_eq {α r s : ℝ} (hα1 : 1 < α) (hr : 0 < r) (hrs : r < s) :
    ((r ^ (α / 2) / (1 + r ^ α)) * (s ^ (α / 2) / (1 + s ^ α)) /
      Real.sqrt (r * s)) / (1 - profT α r s / s) =
        (profZeta α 1 s - profZeta α 1 r) / (s - r) *
          (r / s) ^ ((α - 1) / 2) := by
  have hα0 : 0 < α := by linarith
  have hs : 0 < s := hr.trans hrs
  have hra := Real.rpow_pos_of_pos hr α
  have hsa := Real.rpow_pos_of_pos hs α
  have hdiff : s ^ α - r ^ α ≠ 0 :=
    (sub_pos.mpr (Real.rpow_lt_rpow hr.le hrs hα0)).ne'
  have hδ : 1 - profT α r s / s ≠ 0 :=
    (lt_of_lt_of_le (by positivity) (vi_shell_delta hα1 hr hrs)).ne'
  have hp : ∀ t : ℝ, 0 < t → t ^ (α / 2) = t ^ ((α - 1) / 2) * Real.sqrt t := by
    intro t ht
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]
    congr 1
    ring
  have hsν : 0 < s ^ ((α - 1) / 2) := Real.rpow_pos_of_pos hs _
  have hsp : s ^ α = (s ^ ((α - 1) / 2)) ^ 2 * s := by
    calc s ^ α = s ^ (((α - 1) / 2) * 2 + 1) := by congr 1; ring
      _ = s ^ (((α - 1) / 2) * 2) * s ^ (1:ℝ) := Real.rpow_add hs _ _
      _ = (s ^ ((α - 1) / 2)) ^ 2 * s := by
        rw [Real.rpow_mul hs.le, Real.rpow_two, Real.rpow_one]
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  rw [hp r hr, hp s hs, Real.sqrt_mul hr.le, Real.div_rpow hr.le hs.le]
  simp only [profZeta, Real.one_rpow, profT, if_neg (ne_of_lt hrs)]
  have hd1 : 1 + r ^ α ≠ 0 := by positivity
  have hd2 : 1 + s ^ α ≠ 0 := by positivity
  have hde : 1 - (s ^ α * r - r ^ α * s) / (s ^ α - r ^ α) / s =
      s ^ α * (s - r) / (s * (s ^ α - r ^ α)) := by
    field_simp
    ring
  rw [hde]
  field_simp [hd1, hd2, hdiff, hs.ne', hsν.ne', hsr.ne', hss.ne', (sub_pos.mpr hrs).ne']
  linear_combination -(s ^ α - r ^ α) * hsp

open Muon.DetEquiv ProbabilityTheory in
/-- A normalized representation of `G(X)/X`, using the same product measure and
one-variable majorant as `vi_tsum_bd`. -/
private lemma vi_G_rep {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    {X : ℝ} (hX : 0 < X) :
    profG α β X / X = (1 / Real.pi ^ 2) *
      ∫ p : ℝ × ℝ, ∑' ℓ : ℤ,
        ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
          Real.sqrt (p.1 * p.2)) *
          (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
            profTheta α β (X * p.1) * profTheta α β (X * p.2) /
              profDelta α β ℓ (X * p.1) (X * p.2))
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hα0 : 0 < α := by linarith
  rw [vz_G_rep hα1 hβ0 hβ1 hX]
  have he : (∫ p : ℝ × ℝ, ∑' ℓ : ℤ, X ^ 2 *
      (Real.sqrt (profZeta α X (X * p.1) * (1 - profZeta α X (X * p.1)) *
        (profZeta α X (X * p.2) * (1 - profZeta α X (X * p.2)))) /
          Real.sqrt ((X * p.1) * (X * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β ℓ (X * p.1) (X * p.2)))
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) =
      X * ∫ p : ℝ × ℝ, ∑' ℓ : ℤ,
        ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
          Real.sqrt (p.1 * p.2)) *
          (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
            profTheta α β (X * p.1) * profTheta α β (X * p.2) /
              profDelta α β ℓ (X * p.1) (X * p.2))
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [vs_ae_pos (μ := volume) (ν := volume)] with p hp
    rw [← tsum_mul_left]
    apply tsum_congr
    intro ℓ
    rw [vz_scaled_eq hα0 hX hp.1 hp.2 ℓ]
    have hΔ := vs_Delta_ge hα1 hβ0 hβ1 (mul_pos hX hp.1) (mul_pos hX hp.2) ℓ
    have hΔ0 : profDelta α β ℓ (X * p.1) (X * p.2) ≠ 0 :=
      (lt_of_lt_of_le (by positivity) hΔ).ne'
    have hsr : Real.sqrt (p.1 * p.2) ≠ 0 := (Real.sqrt_pos.2 (mul_pos hp.1 hp.2)).ne'
    have hra := Real.rpow_pos_of_pos hp.1 α
    have hsa := Real.rpow_pos_of_pos hp.2 α
    have hd1 : 1 + p.1 ^ α ≠ 0 := by positivity
    have hd2 : 1 + p.2 ^ α ≠ 0 := by positivity
    field_simp [hp.1.ne', hp.2.ne', hΔ0, hsr, hd1, hd2]
  rw [he]
  field_simp

/-- In particular the large-`X` profile has at most linear growth; the majorant
is independent of `X ≥ 1` and is integrable at both endpoints. -/
private lemma vi_G_linear_bound {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ M : ℝ, ∀ X : ℝ, 1 ≤ X → 0 ≤ profG α β X / X ∧ profG α β X / X ≤ M := by
  obtain ⟨K, C, hK, hC, hbd⟩ := vi_tsum_bd (α := α) hα1 hβ0 hβ1
  let μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))
  let H : ℝ × ℝ → ℝ := fun p => α * C *
    ((if p.1 ≤ 1 then K * p.1 ^ (α / 2 - 1) else K * p.1 ^ (-((α + 1) / 2))) *
      (if p.2 ≤ 1 then K * p.2 ^ (α / 2 - 1) else K * p.2 ^ (-((α + 1) / 2))))
  have hHint : Integrable H μ := (vz_bnd_int (K := K) hα1).const_mul (α * C)
  refine ⟨(1 / Real.pi ^ 2) * ∫ p, H p ∂μ, fun X hX => ?_⟩
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hnonneg : 0 ≤ profG α β X / X :=
    div_nonneg (lem_app_pl_supervol_i_pos hα1 hβ0 hβ1 X hX0).le hX0.le
  refine ⟨hnonneg, ?_⟩
  rw [vi_G_rep hα1 hβ0 hβ1 hX0]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine integral_mono_of_nonneg ?_ hHint ?_
  · filter_upwards [vs_ae_pos (μ := volume) (ν := volume)] with p hp
    have hu : 0 < X * p.1 := mul_pos hX0 hp.1
    have hv : 0 < X * p.2 := mul_pos hX0 hp.2
    obtain ⟨K', -, hθ⟩ := vs_theta_bd hα1 hβ0 hβ1
    obtain ⟨hq1, -⟩ := vs_Qm hβ0 hβ1 hu
    obtain ⟨hq2, -⟩ := vs_Qm hβ0 hβ1 hv
    have hθ1 := (hθ _ hu).1
    have hθ2 := (hθ _ hv).1
    have hp1 : 0 < p.1 := hp.1
    have hp2 : 0 < p.2 := hp.2
    have hra := Real.rpow_pos_of_pos hp.1 α
    have hsa := Real.rpow_pos_of_pos hp.2 α
    apply tsum_nonneg
    intro ℓ
    have hD := vs_DLag_nonneg hβ0 hβ1 hq1.le hq2.le ℓ
    have hΔ := vs_Delta_ge hα1 hβ0 hβ1 hu hv ℓ
    have hΔ0 : 0 < profDelta α β ℓ (X * p.1) (X * p.2) :=
      lt_of_lt_of_le (one_div_pos.mpr (by linarith : 0 < α)) hΔ
    positivity
  · filter_upwards [vs_ae_pos (μ := volume) (ν := volume)] with p hp
    exact (hbd X p.1 p.2 hX hp.1 hp.2).2

/-- The elasticity correction in the localized profile is uniformly `O(1/m)`. -/
private lemma vi_theta_error {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℝ, 0 < m →
      |Efun β m * profTheta α β m - 1| ≤ C / m := by
  obtain ⟨c, C, hc, hcC, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  have hC : 0 < C := hc.trans_le hcC
  refine ⟨(α - 1) * C, mul_pos (by linarith) hC, fun m hm => ?_⟩
  have hEm : 0 < Efun β m :=
    lt_of_lt_of_le (mul_pos hc (lt_min hm one_pos)) (hE m hm).1
  have hEmC : Efun β m ≤ C :=
    (hE m hm).2.trans (mul_le_of_le_one_right hC.le (min_le_right _ _))
  have he : Efun β m * profTheta α β m - 1 = (α - 1) * Efun β m / m := by
    unfold profTheta
    field_simp
    ring
  have hα : 0 ≤ α - 1 := by linarith
  rw [he, abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hEmC (by linarith)) hm.le

private lemma vi_theta_lim {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun X : ℝ => Efun β (X * r) * profTheta α β (X * r)) atTop (𝓝 1) := by
  obtain ⟨C, hC, hbd⟩ := vi_theta_error hα1 hβ0 hβ1
  have hlim : Tendsto (fun X : ℝ => C / (X * r)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.atTop_mul_const hr)
  have herr : Tendsto (fun X : ℝ => Efun β (X * r) * profTheta α β (X * r) - 1)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    simpa only [Real.norm_eq_abs] using hbd (X * r) (mul_pos hX hr)
  have := herr.add_const 1
  simpa only [sub_add_cancel, zero_add] using this

open Muon.DetEquiv ProbabilityTheory in
/-- A comparison with the diagonal resolvent bounds the deficit of the lag kernel. -/
private lemma vi_M_deficit {β q₁ q₂ d : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (h₁ : 0 < q₁) (h₂ : 0 < q₂) (ℓ : ℕ) (hd : 1 ≤ d)
    (hr : q₁ ≤ d * (β ^ (2 * ℓ) * q₂)) :
    |Muon.DetEquiv.rW (emaW β) q₁ - MLagNat β q₁ q₂ ℓ| ≤
      d * (q₁ * deriv (Muon.DetEquiv.rW (emaW β)) q₁) := by
  let X : ℕ → ℝ → ℝ := fun a g => q₁ * emaW β a ^ 2 * g ^ 2
  let Y : ℕ → ℝ → ℝ := fun a g => β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2
  have hX : ∀ a g, 0 ≤ X a g := fun a g => by dsimp [X]; positivity
  have hY : ∀ a g, 0 ≤ Y a g := fun a g => by dsimp [Y]; positivity
  have hden : ∀ a g, 0 < (1 + X a g) * (1 + Y a g) := fun a g => by
    have := hX a g; have := hY a g; positivity
  have hbound : ∀ a g, X a g / ((1 + X a g) * (1 + Y a g)) ≤
      q₁ * (emaW β a ^ 2 * g ^ 2) := by
    intro a g
    have hx := hX a g; have hy := hY a g
    have : 1 ≤ (1 + X a g) * (1 + Y a g) := by nlinarith
    exact (div_le_self hx this).trans_eq (by dsimp [X]; ring)
  have hA := vs_int_summ hβ0 hβ1
    (f := fun a g => X a g / ((1 + X a g) * (1 + Y a g)))
    (fun a => by
      refine Continuous.div (by dsimp [X]; fun_prop) (by dsimp [X, Y]; fun_prop) ?_
      exact fun g => (hden a g).ne')
    (fun a g => div_nonneg (hX a g) (hden a g).le) hbound
  have hM := vs_int_summ hβ0 hβ1
    (f := fun a g => X a g * Y a g / ((1 + X a g) * (1 + Y a g))) (c := q₁)
    (fun a => by
      refine Continuous.div (by dsimp [X, Y]; fun_prop) (by dsimp [X, Y]; fun_prop) ?_
      exact fun g => (hden a g).ne')
    (fun a g => div_nonneg (mul_nonneg (hX a g) (hY a g)) (hden a g).le)
    (fun a g => by
      have hx := hX a g; have hy := hY a g
      refine le_trans ?_ (show X a g = q₁ * (emaW β a ^ 2 * g ^ 2) by dsimp [X]; ring).le
      rw [div_le_iff₀ (hden a g)]
      nlinarith [mul_nonneg hx hy, mul_nonneg (sq_nonneg (X a g)) hy])
  have hE := vs_int_summ hβ0 hβ1
    (f := fun a g => X a g / (1 + X a g) ^ 2) (c := q₁)
    (fun a => by
      refine Continuous.div (by dsimp [X]; fun_prop) (by dsimp [X]; fun_prop) ?_
      intro g; have := hX a g; positivity)
    (fun a g => div_nonneg (hX a g) (sq_nonneg _))
    (fun a g => by
      have hx := hX a g
      exact (div_le_self hx (by nlinarith : 1 ≤ (1 + X a g) ^ 2)).trans_eq
        (by dsimp [X]; ring))
  have hMeq : MLagNat β q₁ q₂ ℓ =
      ∑' a, ∫ g, X a g * Y a g / ((1 + X a g) * (1 + Y a g)) ∂(gaussianReal 0 1) := by
    unfold MLagNat
    refine tsum_congr fun a => ?_
    congr 1; funext g; dsimp [X, Y]; ring
  have hsplit : Muon.DetEquiv.rW (emaW β) q₁ =
      (∑' a, ∫ g, X a g / ((1 + X a g) * (1 + Y a g)) ∂(gaussianReal 0 1)) +
        MLagNat β q₁ q₂ ℓ := by
    rw [(Muon.DetEquiv.lem_app_de_scalar_iii (vs_weightSeq hβ0 hβ1)).1 q₁ h₁.le,
      hMeq, ← hA.2.tsum_add hM.2]
    refine tsum_congr fun a => ?_
    rw [← integral_add (hA.1 a) (hM.1 a)]
    congr 1; funext g
    have hx := hX a g; have hy := hY a g
    have heq : emaW β a ^ 2 * q₁ * g ^ 2 = X a g := by dsimp [X]; ring
    rw [heq]
    field_simp
    <;> ring
  have hdiag : q₁ * deriv (Muon.DetEquiv.rW (emaW β)) q₁ =
      ∑' a, ∫ g, X a g / (1 + X a g) ^ 2 ∂(gaussianReal 0 1) := by
    rw [((Muon.DetEquiv.lem_app_de_scalar_iii (vs_weightSeq hβ0 hβ1)).2.2.2.1 q₁ h₁).deriv,
      ← tsum_mul_left]
    refine tsum_congr fun a => ?_
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1; funext g; dsimp [X]; ring
  have hnonneg : 0 ≤ Muon.DetEquiv.rW (emaW β) q₁ - MLagNat β q₁ q₂ ℓ := by
    rw [hsplit, add_sub_cancel_right]
    exact tsum_nonneg fun a => integral_nonneg fun g => div_nonneg (hX a g) (hden a g).le
  rw [abs_of_nonneg hnonneg, hsplit, add_sub_cancel_right, hdiag, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ hA.2 (hE.2.mul_left d)
  intro a
  rw [← integral_const_mul]
  apply integral_mono (hA.1 a) ((hE.1 a).const_mul d)
  intro g
  have hx := hX a g; have hy := hY a g
  have hxy : X a g ≤ d * Y a g := by
    have := mul_le_mul_of_nonneg_right hr (mul_nonneg (sq_nonneg (emaW β a)) (sq_nonneg g))
    simpa [X, Y, mul_assoc] using this
  have hd0 : 0 ≤ d := by linarith
  dsimp only
  rw [← mul_div_assoc, div_le_div_iff₀ (hden a g) (by positivity)]
  nlinarith [mul_nonneg hx (show 0 ≤ d * (1 + Y a g) - (1 + X a g) by linarith),
    mul_nonneg (sq_nonneg (X a g)) (show 0 ≤ d * (1 + Y a g) - (1 + X a g) by linarith)]

/-- A shell-deficit bound independent of any finite-dimensional regime. -/
private lemma vi_M_shell {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℕ) (u v : ℝ), 1 ≤ u → 1 ≤ v →
      |u - v + (ℓ : ℝ)| ≤ A →
        |u - MLag β (Qm β u) (Qm β v) (ℓ : ℤ)| ≤ C := by
  obtain ⟨CQ, hCQ⟩ := lem_app_pl_weights_iii_logQ hβ0 hβ1
  obtain ⟨cE, CE, hcE, hcCE, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  let L := 2 * |CQ| + 2 * |Real.log β| * max A 0
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨Real.exp L * CE, mul_pos (Real.exp_pos _) (hcE.trans_le hcCE),
    fun ℓ u v hu hv huv => ?_⟩
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  obtain ⟨hq₁, hr₁⟩ := vs_Qm hβ0 hβ1 hu0
  obtain ⟨hq₂, -⟩ := vs_Qm hβ0 hβ1 hv0
  have hpow : 0 < β ^ (2 * ℓ) * Qm β v := mul_pos (pow_pos hβ0 _) hq₂
  have hrat : 0 < Qm β u / (β ^ (2 * ℓ) * Qm β v) := div_pos hq₁ hpow
  have hlog : Real.log (Qm β u / (β ^ (2 * ℓ) * Qm β v)) ≤ L := by
    rw [Real.log_div hq₁.ne' hpow.ne', Real.log_mul (pow_pos hβ0 _).ne' hq₂.ne',
      Real.log_pow]
    push_cast
    have h₁ := (abs_le.mp (hCQ _ hu)).2
    have h₂ := (abs_le.mp (hCQ _ hv)).1
    have hb : Real.log β = -|Real.log β| := by
      rw [abs_of_neg (Real.log_neg hβ0 hβ1)]
      ring
    have hh : u - v + (ℓ : ℝ) ≤ max A 0 :=
      (le_abs_self _).trans (huv.trans (le_max_left _ _))
    rw [hb]
    dsimp [L]
    nlinarith [le_abs_self CQ, mul_le_mul_of_nonneg_left hh
      (by positivity : 0 ≤ 2 * |Real.log β|)]
  have hratle : Qm β u ≤ Real.exp L * (β ^ (2 * ℓ) * Qm β v) := by
    apply (div_le_iff₀ hpow).mp
    calc _ = Real.exp (Real.log (Qm β u / (β ^ (2 * ℓ) * Qm β v))) :=
          (Real.exp_log hrat).symm
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hlog
  have hdef := vi_M_deficit hβ0 hβ1 hq₁ hq₂ ℓ (Real.one_le_exp_iff.mpr hL) hratle
  rw [hr₁] at hdef
  have hEb : Efun β u ≤ CE :=
    (hE _ hu0).2.trans (mul_le_of_le_one_right (hcE.le.trans hcCE) (min_le_right _ _))
  simp only [MLag, Int.natCast_nonneg, ite_true, Int.toNat_natCast]
  exact hdef.trans (mul_le_mul_of_nonneg_left hEb (Real.exp_pos L).le)

/-- Quantitative replacement of the determinant on bounded-width positive-lag shells. -/
private lemma vi_delta_shell_error {α β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℕ) (u v : ℝ), 1 ≤ u → 1 ≤ v →
      |u - v + (ℓ : ℝ)| ≤ A →
        |profDelta α β (ℓ : ℤ) u v - (1 - profT α u v / v)| ≤
          |profT α u v / (u * v)| * C := by
  obtain ⟨C, hC0, hC⟩ := vi_M_shell hβ0 hβ1 A
  refine ⟨C, hC0, fun ℓ u v hu hv huv => ?_⟩
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have he : profDelta α β (ℓ : ℤ) u v - (1 - profT α u v / v) =
      (profT α u v / (u * v)) * (u - MLag β (Qm β u) (Qm β v) (ℓ : ℤ)) := by
    unfold profDelta
    field_simp
    ring
  rw [he, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC ℓ u v hu hv huv) (abs_nonneg _)

private lemma vi_T_nonneg {α u v : ℝ} (hα1 : 1 < α) (hu : 0 < u) (hv : 0 < v) :
    0 ≤ profT α u v := by
  have hα0 : 0 < α := by linarith
  have hlt : ∀ a b : ℝ, 0 < a → a < b →
      0 ≤ (b ^ α * a - a ^ α * b) / (b ^ α - a ^ α) := by
    intro a b ha hab
    have hb := ha.trans hab
    have hpow := Real.rpow_le_rpow ha.le hab.le (by linarith : 0 ≤ α - 1)
    rw [Real.rpow_sub_one ha.ne', Real.rpow_sub_one hb.ne'] at hpow
    have hnum : 0 ≤ b ^ α * a - a ^ α * b := by
      have := (div_le_div_iff₀ ha hb).mp hpow
      linarith
    have hden : 0 < b ^ α - a ^ α := sub_pos.mpr (Real.rpow_lt_rpow ha.le hab hα0)
    exact div_nonneg hnum hden.le
  unfold profT
  split_ifs with h
  · positivity
  · rcases lt_or_gt_of_ne h with hlt' | hgt'
    · exact hlt u v hu hlt'
    · have he : (v ^ α * u - u ^ α * v) / (v ^ α - u ^ α) =
          (u ^ α * v - v ^ α * u) / (u ^ α - v ^ α) := by
        rw [← neg_div_neg_eq]
        ring_nf
      rw [he]
      exact hlt v u hv hgt'

/-- Away from the coordinate axes the homogeneous determinant coefficient is bounded. -/
private lemma vi_T_ratio_bd {α δ u v : ℝ} (hα1 : 1 < α) (hδ : 0 < δ)
    (hu : δ ≤ u) (hv : δ ≤ v) :
    0 ≤ profT α u v / (u * v) ∧ profT α u v / (u * v) ≤ 1 / δ := by
  have hu0 : 0 < u := hδ.trans_le hu
  have hv0 : 0 < v := hδ.trans_le hv
  have hα0 : 0 < α := by linarith
  have hT0 := vi_T_nonneg hα1 hu0 hv0
  have hT : profT α u v ≤ max u v := by
    refine (vs_T_le hα1 hu0 hv0).trans ?_
    have hmax : 0 ≤ max u v := hu0.le.trans (le_max_left _ _)
    have : 0 ≤ 1 / α := by positivity
    nlinarith
  have hmax : δ * max u v ≤ u * v := by
    rcases le_total u v with huv | hvu
    · rw [max_eq_right huv]
      exact mul_le_mul_of_nonneg_right hu hv0.le
    · rw [max_eq_left hvu]
      nlinarith [mul_le_mul_of_nonneg_left hv hu0.le]
  refine ⟨div_nonneg hT0 (mul_pos hu0 hv0).le, ?_⟩
  rw [div_le_div_iff₀ (mul_pos hu0 hv0) hδ]
  nlinarith [mul_le_mul_of_nonneg_left hT hδ.le]

/-- Uniform determinant replacement on rescaled bounded-width shells. -/
private lemma vi_delta_scaled_error {α β δ : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 < δ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r s : ℝ) (ℓ : ℕ), 0 < X → δ ≤ r → δ ≤ s →
      1 ≤ X * r → 1 ≤ X * s → |X * r - X * s + (ℓ : ℝ)| ≤ A →
        |profDelta α β (ℓ : ℤ) (X * r) (X * s) - (1 - profT α r s / s)| ≤
          C / (X * δ) := by
  obtain ⟨C, hC0, hC⟩ := vi_delta_shell_error (α := α) hβ0 hβ1 A
  refine ⟨C, hC0, fun X r s ℓ hX hr hs hu hv huv => ?_⟩
  have hr0 : 0 < r := hδ.trans_le hr
  have hs0 : 0 < s := hδ.trans_le hs
  have hT := vi_T_ratio_bd hα1 hδ hr hs
  have he1 : profT α (X * r) (X * s) / (X * s) = profT α r s / s := by
    rw [vz_T_hom hX hr0 hs0]
    field_simp
  have he2 : profT α (X * r) (X * s) / ((X * r) * (X * s)) =
      (profT α r s / (r * s)) / X := by
    rw [vz_T_hom hX hr0 hs0]
    field_simp
  have hcoeff : |profT α (X * r) (X * s) / ((X * r) * (X * s))| ≤ 1 / (X * δ) := by
    rw [he2, abs_of_nonneg (div_nonneg hT.1 hX.le)]
    calc (profT α r s / (r * s)) / X ≤ (1 / δ) / X :=
          div_le_div_of_nonneg_right hT.2 hX.le
      _ = 1 / (X * δ) := by ring
  have hmain := hC ℓ (X * r) (X * s) hu hv huv
  rw [he1] at hmain
  refine hmain.trans ?_
  calc _ ≤ 1 / (X * δ) * C := mul_le_mul_of_nonneg_right hcoeff hC0.le
    _ = C / (X * δ) := by ring

/-- Localization written directly in the rescaled variables used by `vi_G_rep`.
This statement has no finite-dimensional row parameters. -/
private lemma vi_localization_scaled {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (Xn : ℕ → ℝ) (ℓn : ℕ → ℤ) (hX : ∀ n, 0 < Xn n)
    (hXT : Tendsto Xn atTop atTop) {τ : ℝ} (hτ : 0 < τ)
    (hℓ : Tendsto (fun n => (ℓn n : ℝ) / Xn n) atTop (𝓝 τ))
    (φ : ℝ × ℝ → ℝ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφsupp : tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0) :
    Tendsto (fun n => ∫ p : ℝ × ℝ, φ p * Xn n *
      DLag β (Qm β (Xn n * p.1)) (Qm β (Xn n * p.2)) (ℓn n) /
        (Real.pi ^ 2 * Efun β (Xn n * p.1) * Efun β (Xn n * p.2)))
      atTop (𝓝 (∫ r : ℝ, φ (r, r + τ))) := by
  have hγ : Tendsto (fun n => (Xn n * Xn n) / Xn n) atTop atTop := by
    convert hXT using 1
    funext n
    exact mul_div_cancel_right₀ _ (hX n).ne'
  have hloc := (lem_app_pl_localization_iii_top hβ0 hβ1
    (fun n => Xn n * Xn n) ℓn Xn hX hXT hτ hγ hℓ φ hφc hφs hφsupp).2
  refine hloc.congr' (Filter.Eventually.of_forall fun n => ?_)
  let f : ℝ × ℝ → ℝ := fun p => φ (p.1 / Xn n, p.2 / Xn n) *
    DLag β (Qm β p.1) (Qm β p.2) (ℓn n) /
      (Real.pi ^ 2 * Xn n * Efun β p.1 * Efun β p.2)
  have hscale := Measure.integral_comp_smul (μ := (volume : Measure (ℝ × ℝ))) f (Xn n)
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hdim, abs_of_pos (inv_pos.mpr (pow_pos (hX n) 2)), smul_eq_mul] at hscale
  have he : ∫ p : ℝ × ℝ, f p = (Xn n) ^ 2 * ∫ p : ℝ × ℝ, f (Xn n • p) := by
    rw [hscale]
    field_simp [(hX n).ne']
  change (∫ p : ℝ × ℝ, f p) = _
  rw [he, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  dsimp [f]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    mul_div_cancel_left₀ _ (hX n).ne']
  field_simp
  <;> ring

private lemma vi_shell_k_int {α : ℝ} (hα1 : 1 < α) :
    IntegrableOn (fun r : ℝ => r ^ (α / 2) / (1 + r ^ α) / Real.sqrt r) (Ioi 0) := by
  have hα0 : 0 < α := by linarith
  have hmaj := vs_k_int (α := α) (K := 1) (A := 1) (B := 1) hα1
  have hmeas : Measurable (fun r : ℝ => r ^ (α / 2) / (1 + r ^ α) / Real.sqrt r) := by
    fun_prop
  refine Integrable.mono' hmaj hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := hr
  have hra := Real.rpow_pos_of_pos hr0 α
  have hrh := Real.rpow_pos_of_pos hr0 (α / 2)
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hw : 0 < min (Real.sqrt r) 1 := lt_min hsr one_pos
  have he : (1 / min r 1) * min (Real.sqrt r) 1 = 1 / min (Real.sqrt r) 1 := by
    rw [← vs_w_sq hr0]
    field_simp
  have hfac : 1 ≤ (1 / min r 1) * min (Real.sqrt r) 1 := by
    rw [he, le_div_iff₀ hw]
    simpa only [one_mul] using min_le_right (Real.sqrt r) 1
  have hbd := vi_g_bd (α := α) (K := 1) (X := 1) (θ := 1 / min r 1)
    hα0 one_pos le_rfl hr0 (by simp)
  simp only [one_mul] at hbd ⊢
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine le_trans ?_ hbd
  have hnum : 0 ≤ r ^ (α / 2) / (1 + r ^ α) := by positivity
  have := mul_le_mul_of_nonneg_left hfac hnum
  rw [mul_one] at this
  exact div_le_div_of_nonneg_right (by nlinarith) hsr.le

/-- Integrability of the half-line shell integrand on the open triangle `0 < r < s`. -/
private lemma vi_shell_triangle_int {α : ℝ} (hα1 : 1 < α) :
    Integrable (Set.indicator {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < z.2}
      (fun z : ℝ × ℝ => (profZeta α 1 z.2 - profZeta α 1 z.1) / (z.2 - z.1) *
        (z.1 / z.2) ^ ((α - 1) / 2))) volume := by
  have hα0 : 0 < α := by linarith
  let k : ℝ → ℝ := (Ioi (0:ℝ)).indicator
    (fun r : ℝ => r ^ (α / 2) / (1 + r ^ α) / Real.sqrt r)
  have hk : Integrable k volume := (integrable_indicator_iff measurableSet_Ioi).2
    (vi_shell_k_int hα1)
  have hk0 : ∀ r, 0 ≤ k r := by
    intro r
    by_cases hr : 0 < r
    · rw [show k r = r ^ (α / 2) / (1 + r ^ α) / Real.sqrt r from
        Set.indicator_of_mem hr _]
      have hra := Real.rpow_pos_of_pos hr α
      positivity
    · exact (Set.indicator_of_notMem hr _).ge
  let T : Set (ℝ × ℝ) := {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < z.2}
  have hTm : MeasurableSet T :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  have hmeas : Measurable (T.indicator (fun z : ℝ × ℝ =>
      (profZeta α 1 z.2 - profZeta α 1 z.1) / (z.2 - z.1) *
        (z.1 / z.2) ^ ((α - 1) / 2))) := by
    apply Measurable.indicator _ hTm
    unfold profZeta
    fun_prop
  rw [Measure.volume_eq_prod]
  refine Integrable.mono' ((hk.mul_prod hk).const_mul α) hmeas.aestronglyMeasurable ?_
  filter_upwards with z
  by_cases hz : z ∈ T
  · have hr : 0 < z.1 := hz.1
    have hrs : z.1 < z.2 := hz.2
    have hs : 0 < z.2 := hr.trans hrs
    rw [Set.indicator_of_mem hz, ← vi_shell_eq hα1 hr hrs]
    have hd := vi_shell_delta hα1 hr hrs
    have hd0 : 0 < 1 - profT α z.1 z.2 / z.2 :=
      lt_of_lt_of_le (one_div_pos.mpr hα0) hd
    have hra := Real.rpow_pos_of_pos hr α
    have hsa := Real.rpow_pos_of_pos hs α
    have hrh := Real.rpow_pos_of_pos hr (α / 2)
    have hsh := Real.rpow_pos_of_pos hs (α / 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hnum : 0 ≤ (z.1 ^ (α / 2) / (1 + z.1 ^ α)) *
        (z.2 ^ (α / 2) / (1 + z.2 ^ α)) / Real.sqrt (z.1 * z.2) := by positivity
    have hinv : 1 / (1 - profT α z.1 z.2 / z.2) ≤ α := by
      rw [div_le_iff₀ hd0]
      have := mul_le_mul_of_nonneg_left hd hα0.le
      rw [mul_one_div_cancel hα0.ne'] at this
      nlinarith
    have hprod := mul_le_mul_of_nonneg_left hinv hnum
    simp only [k, Set.indicator_of_mem (show z.1 ∈ Ioi (0:ℝ) from hr),
      Set.indicator_of_mem (show z.2 ∈ Ioi (0:ℝ) from hs)]
    rw [Real.sqrt_mul hr.le] at hprod ⊢
    convert hprod using 1 <;> ring
  · rw [Set.indicator_of_notMem hz, norm_zero]
    exact mul_nonneg hα0.le (mul_nonneg (hk0 _) (hk0 _))

private lemma vi_coefficient_scale {α X r s : ℝ} (hα0 : 0 < α) (hX : 0 < X)
    (hr : 0 < r) (hs : 0 < s) :
    X * (Real.sqrt (profZeta α X (X * r) * (1 - profZeta α X (X * r)) *
      (profZeta α X (X * s) * (1 - profZeta α X (X * s)))) /
        Real.sqrt ((X * r) * (X * s))) =
      (r ^ (α / 2) / (1 + r ^ α)) * (s ^ (α / 2) / (1 + s ^ α)) /
        Real.sqrt (r * s) := by
  rw [vz_zeta_scale hα0 hX hr, vz_zeta_scale hα0 hX hs]
  have hz : ∀ t : ℝ, 0 < t → 0 ≤ t ^ α / (1 + t ^ α) * (1 - t ^ α / (1 + t ^ α)) := by
    intro t ht
    have hta := Real.rpow_pos_of_pos ht α
    have hd : 0 < 1 + t ^ α := by positivity
    have he : t ^ α / (1 + t ^ α) * (1 - t ^ α / (1 + t ^ α)) =
        t ^ α / (1 + t ^ α) ^ 2 := by field_simp; ring
    rw [he]
    positivity
  rw [Real.sqrt_mul (hz r hr), vz_sigma hα0 hr, vz_sigma hα0 hs]
  have he : Real.sqrt ((X * r) * (X * s)) = X * Real.sqrt (r * s) := by
    rw [show (X * r) * (X * s) = X ^ 2 * (r * s) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hX.le]
  rw [he]
  rw [← mul_div_assoc]
  exact mul_div_mul_left _ _ hX.ne'

/-- The normalized lag sum is measurable and integrable for every `X ≥ 1`.
Together with `vi_tsum_bd`, this justifies compact spatial truncations uniformly in `X`. -/
private lemma vi_sum_integrable {α β X : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hX : 1 ≤ X) :
    Integrable (fun p : ℝ × ℝ => ∑' ℓ : ℤ,
      ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
        Real.sqrt (p.1 * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β ℓ (X * p.1) (X * p.2)))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hα0 : 0 < α := by linarith
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  obtain ⟨K, C, hK, hC, hbd⟩ := vi_tsum_bd (α := α) hα1 hβ0 hβ1
  let μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))
  let F : ℤ → ℝ × ℝ → ℝ := fun ℓ p =>
    ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
      Real.sqrt (p.1 * p.2)) *
      (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
        profTheta α β (X * p.1) * profTheta α β (X * p.2) /
          profDelta α β ℓ (X * p.1) (X * p.2))
  have hterm : ∀ ℓ : ℤ, AEStronglyMeasurable (F ℓ) μ := by
    intro ℓ
    have hm := ((vs_F_meas (α := α) hβ0 hβ1 X ℓ).comp_quasiMeasurePreserving
      (vz_qmp hX0)).const_mul X
    refine hm.congr ?_
    filter_upwards [vs_ae_pos (μ := volume) (ν := volume)] with p hp
    change X * (_ * _) = F ℓ p
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [← mul_assoc, vi_coefficient_scale hα0 hX0 hp.1 hp.2]
  have hmeas : AEStronglyMeasurable (fun p => ∑' ℓ, F ℓ p) μ := by
    refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ℤ))
      (f := fun (S : Finset ℤ) (p : ℝ × ℝ) => ∑ ℓ ∈ S, F ℓ p)
      (fun S => Finset.aestronglyMeasurable_fun_sum S (fun ℓ _ => hterm ℓ)) ?_
    filter_upwards [vs_ae_pos (μ := volume) (ν := volume)] with p hp
    exact (hbd X p.1 p.2 hX hp.1 hp.2).1.hasSum
  refine Integrable.mono' ((vz_bnd_int (K := K) hα1).const_mul (α * C)) hmeas ?_
  filter_upwards [vs_ae_pos (μ := volume) (ν := volume)] with p hp
  have hr : 0 < p.1 := hp.1
  have hs : 0 < p.2 := hp.2
  have hra := Real.rpow_pos_of_pos hr α
  have hsa := Real.rpow_pos_of_pos hs α
  have hu : 0 < X * p.1 := mul_pos hX0 hr
  have hv : 0 < X * p.2 := mul_pos hX0 hs
  obtain ⟨K', -, hθ⟩ := vs_theta_bd hα1 hβ0 hβ1
  have hθ1 := (hθ _ hu).1
  have hθ2 := (hθ _ hv).1
  obtain ⟨hq1, -⟩ := vs_Qm hβ0 hβ1 hu
  obtain ⟨hq2, -⟩ := vs_Qm hβ0 hβ1 hv
  have hnn : 0 ≤ ∑' ℓ, F ℓ p := by
    apply tsum_nonneg
    intro ℓ
    have hD := vs_DLag_nonneg hβ0 hβ1 hq1.le hq2.le ℓ
    have hΔ := vs_Delta_ge hα1 hβ0 hβ1 hu hv ℓ
    have hΔ0 : 0 < profDelta α β ℓ (X * p.1) (X * p.2) :=
      lt_of_lt_of_le (one_div_pos.mpr hα0) hΔ
    dsimp [F]
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact (hbd X p.1 p.2 hX hr hs).2

/-- The half-line shell mass in ratio coordinates, including the factor for both lag signs. -/
private lemma vi_shell_mass {α : ℝ} (hα1 : 1 < α) :
    2 * (∫ ρ in Ioo (0:ℝ) 1, ∫ s in Ioi (0:ℝ),
      ρ ^ ((α - 1) / 2) / (1 - ρ) *
        (profZeta α 1 s - profZeta α 1 (ρ * s))) = 4 * Kc α / (α - 1) := by
  have hα0 : 0 < α := by linarith
  have hinner : ∀ ρ ∈ Ioo (0:ℝ) 1,
      (∫ s in Ioi (0:ℝ), ρ ^ ((α - 1) / 2) / (1 - ρ) *
        (profZeta α 1 s - profZeta α 1 (ρ * s))) =
          Kc α * ρ ^ ((α - 1) / 2 - 1) := by
    intro ρ hρ
    have hra : ρ ^ α < 1 := Real.rpow_lt_one hρ.1.le hρ.2 hα0
    have h1 : 0 < 1 - ρ ^ α := by linarith
    have h2 : 0 < 1 - ρ := by linarith [hρ.2]
    have he : ∀ s ∈ Ioi (0:ℝ),
        ρ ^ ((α - 1) / 2) / (1 - ρ) * (profZeta α 1 s - profZeta α 1 (ρ * s)) =
        (ρ ^ ((α - 1) / 2) * ((1 - ρ ^ α) / (1 - ρ))) *
          (s ^ α / (((ρ * s) ^ α + 1) * (s ^ α + 1))) := by
      intro s hs
      have hsa := Real.rpow_pos_of_pos hs α
      have hrsa := Real.rpow_pos_of_pos (mul_pos hρ.1 hs) α
      simp only [profZeta, Real.one_rpow]
      rw [Real.mul_rpow hρ.1.le (le_of_lt hs)]
      have hr0 := Real.rpow_pos_of_pos hρ.1 α
      have hd1 : 1 + ρ ^ α * s ^ α ≠ 0 := by positivity
      have hd2 : ρ ^ α * s ^ α + 1 ≠ 0 := by positivity
      field_simp [hd1, hd2]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul,
      vg_inner_y hα1 hρ.1 hρ.2, Real.rpow_sub_one hρ.1.ne']
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hinner, integral_const_mul]
  have he : (∫ ρ in Ioo (0:ℝ) 1, ρ ^ ((α - 1) / 2 - 1)) = 2 / (α - 1) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith))]
    rw [Real.one_rpow, Real.zero_rpow (by linarith)]
    field_simp
    ring
  rw [he]
  ring

private lemma vi_shell_ratio_int {α : ℝ} (hα1 : 1 < α) :
    Integrable (fun z : ℝ × ℝ => z.1 ^ ((α - 1) / 2) / (1 - z.1) *
      (profZeta α 1 z.2 - profZeta α 1 (z.1 * z.2)))
      ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  let f : ℝ × ℝ → ℝ := fun z => Kc α *
    (z.1 ^ ((α - 1) / 2) * z.2 ^ α * ((1 - z.1 ^ α) / (1 - z.1)) /
      (((z.1 * z.2) ^ α + 1) * (z.2 ^ α + 1)))
  have hf : Integrable f
      ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))) := by
    by_contra hn
    have hval := vg_I0 hα1
    change (∫ z, f z ∂((volume.restrict (Ioo (0:ℝ) 1)).prod
      (volume.restrict (Ioi (0:ℝ))))) = _ at hval
    rw [integral_undef hn] at hval
    have hpos : 0 < Kc α ^ 2 * (2 / (α - 1)) := by
      have : 0 < α - 1 := by linarith
      positivity
    linarith
  refine (hf.div_const (Kc α)).congr ?_
  filter_upwards [vg_ae_mem (μ := volume) (ν := volume) measurableSet_Ioo measurableSet_Ioi]
    with z hz
  have hρ0 : 0 < z.1 := hz.1.1
  have hρ1 : z.1 < 1 := hz.1.2
  have hs : 0 < z.2 := hz.2
  have hra := Real.rpow_pos_of_pos hρ0 α
  have hsa := Real.rpow_pos_of_pos hs α
  have hd1 : 1 + z.1 ^ α * z.2 ^ α ≠ 0 := by positivity
  have hd2 : z.1 ^ α * z.2 ^ α + 1 ≠ 0 := by positivity
  have hd3 : z.2 ^ α + 1 ≠ 0 := by positivity
  have hd4 : 1 + z.2 ^ α ≠ 0 := by positivity
  dsimp [f]
  simp only [profZeta, Real.one_rpow]
  rw [Real.mul_rpow hρ0.le hs.le]
  field_simp [hd1, hd2, hd3, hd4, hK.ne']
  ring

/-- Evaluation of the full positive-lag half-line shell profile. -/
private lemma vi_shell_integral {α : ℝ} (hα1 : 1 < α) :
    2 * (∫ τ in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ),
      (profZeta α 1 (r + τ) - profZeta α 1 r) / τ *
        (r / (r + τ)) ^ ((α - 1) / 2)) = 4 * Kc α / (α - 1) := by
  let T : Set (ℝ × ℝ) := {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < z.2}
  let H : ℝ × ℝ → ℝ := T.indicator (fun z : ℝ × ℝ =>
    (profZeta α 1 z.2 - profZeta α 1 z.1) / (z.2 - z.1) *
      (z.1 / z.2) ^ ((α - 1) / 2))
  let F : ℝ × ℝ → ℝ := fun z => z.1 ^ ((α - 1) / 2) / (1 - z.1) *
    (profZeta α 1 z.2 - profZeta α 1 (z.1 * z.2))
  have hH : Integrable H volume := vi_shell_triangle_int hα1
  have hHp : Integrable H (volume.prod volume) := by rwa [← Measure.volume_eq_prod]
  have hF : Integrable F
      ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))) :=
    vi_shell_ratio_int hα1
  have hline : ∀ τ : ℝ, (∫ r : ℝ, H (r, r + τ)) =
      (Ioi (0:ℝ)).indicator (fun τ => ∫ r in Ioi (0:ℝ),
        (profZeta α 1 (r + τ) - profZeta α 1 r) / τ *
          (r / (r + τ)) ^ ((α - 1) / 2)) τ := by
    intro τ
    by_cases hτ : 0 < τ
    · rw [Set.indicator_of_mem (show τ ∈ Ioi (0:ℝ) from hτ)]
      have he : (fun r : ℝ => H (r, r + τ)) = (Ioi (0:ℝ)).indicator
          (fun r : ℝ => (profZeta α 1 (r + τ) - profZeta α 1 r) / τ *
            (r / (r + τ)) ^ ((α - 1) / 2)) := by
        funext r
        by_cases hr : 0 < r
        · have hmem : (r, r + τ) ∈ T := ⟨hr, by linarith⟩
          simp only [H, Set.indicator_of_mem hmem, Set.indicator_of_mem (show r ∈ Ioi (0:ℝ) from hr)]
          simp only [add_sub_cancel_left]
        · have hmem : (r, r + τ) ∉ T := fun h => hr h.1
          simp only [H, Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show r ∉ Ioi (0:ℝ) from hr)]
      rw [he, integral_indicator measurableSet_Ioi]
    · rw [Set.indicator_of_notMem (show τ ∉ Ioi (0:ℝ) from hτ)]
      have hz : ∀ r : ℝ, H (r, r + τ) = 0 := by
        intro r
        have hmem : (r, r + τ) ∉ T := fun h => hτ (by linarith [h.2])
        exact Set.indicator_of_notMem hmem _
      simp only [hz, integral_zero]
  have hshear : (∫ z : ℝ × ℝ, H z) = ∫ τ in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ),
      (profZeta α 1 (r + τ) - profZeta α 1 r) / τ *
        (r / (r + τ)) ^ ((α - 1) / 2) := by
    have hi : Integrable (fun z : ℝ × ℝ => H (z.2, z.2 + z.1)) volume :=
      (vg_shear_mp.integrable_comp_emb vg_shear_emb).2 hH
    calc (∫ z : ℝ × ℝ, H z) = ∫ z : ℝ × ℝ, H (z.2, z.2 + z.1) :=
          (vg_shear_mp.integral_comp vg_shear_emb H).symm
      _ = ∫ τ : ℝ, ∫ r : ℝ, H (r, r + τ) := by
          rw [Measure.volume_eq_prod] at hi ⊢
          exact integral_prod _ hi
      _ = _ := by
          simp_rw [hline]
          exact integral_indicator measurableSet_Ioi
  have hratio : ∀ s : ℝ, (∫ r : ℝ, H (r, s)) =
      (Ioi (0:ℝ)).indicator (fun s => ∫ ρ in Ioo (0:ℝ) 1, F (ρ, s)) s := by
    intro s
    by_cases hs : 0 < s
    · rw [Set.indicator_of_mem (show s ∈ Ioi (0:ℝ) from hs)]
      have he : (fun r : ℝ => H (r, s)) = (Ioo (0:ℝ) s).indicator
          (fun r : ℝ => (profZeta α 1 s - profZeta α 1 r) / (s - r) *
            (r / s) ^ ((α - 1) / 2)) := by
        funext r
        by_cases hr : r ∈ Ioo (0:ℝ) s
        · simp only [H, Set.indicator_of_mem (show (r, s) ∈ T from hr), Set.indicator_of_mem hr]
        · simp only [H, Set.indicator_of_notMem (show (r, s) ∉ T from hr), Set.indicator_of_notMem hr]
      rw [he, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hs.le]
      have hcv := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (c := s)
        (fun r : ℝ => (profZeta α 1 s - profZeta α 1 r) / (s - r) *
          (r / s) ^ ((α - 1) / 2)) hs.ne'
      simp only [mul_zero, mul_one] at hcv
      simp_rw [mul_comm s] at hcv
      have hcv' : (∫ r in (0:ℝ)..s, (profZeta α 1 s - profZeta α 1 r) / (s - r) *
          (r / s) ^ ((α - 1) / 2)) = s * ∫ ρ in (0:ℝ)..1,
          (profZeta α 1 s - profZeta α 1 (ρ * s)) / (s - ρ * s) *
            (ρ * s / s) ^ ((α - 1) / 2) := by
        rw [hcv, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
      rw [hcv', intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
        ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro ρ hρ
      dsimp [F]
      rw [mul_div_cancel_right₀ _ hs.ne']
      field_simp
      <;> ring
    · rw [Set.indicator_of_notMem (show s ∉ Ioi (0:ℝ) from hs)]
      have hz : ∀ r : ℝ, H (r, s) = 0 := by
        intro r
        have hmem : (r, s) ∉ T := fun h => hs (lt_trans h.1 h.2)
        exact Set.indicator_of_notMem hmem _
      simp only [hz, integral_zero]
  have hswap : (∫ z : ℝ × ℝ, H z) = ∫ s in Ioi (0:ℝ), ∫ ρ in Ioo (0:ℝ) 1, F (ρ, s) := by
    rw [Measure.volume_eq_prod, integral_prod_symm _ hHp]
    simp_rw [hratio]
    exact integral_indicator measurableSet_Ioi
  rw [← hshear, hswap]
  rw [← integral_prod_symm _ hF, integral_prod _ hF]
  exact vi_shell_mass hα1

private lemma vi_shell_k_le_one {α r : ℝ} (hα1 : 1 < α) (hr : 0 < r) :
    r ^ (α / 2) / (1 + r ^ α) / Real.sqrt r ≤ 1 := by
  have hra := Real.rpow_pos_of_pos hr α
  have he : r ^ (α / 2) / (1 + r ^ α) / Real.sqrt r =
      r ^ ((α - 1) / 2) / (1 + r ^ α) := by
    rw [div_right_comm, Real.sqrt_eq_rpow, ← Real.rpow_sub hr]
    congr 2
    ring
  rw [he, div_le_one (by positivity)]
  by_cases hr1 : r ≤ 1
  · have := Real.rpow_le_one hr.le hr1 (by linarith : 0 ≤ (α - 1) / 2)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le (not_le.mp hr1).le
      (by linarith : (α - 1) / 2 ≤ α)
    linarith

private lemma vi_shell_point_bound {α r τ : ℝ} (hα1 : 1 < α) (hr : 0 < r) (hτ : 0 < τ) :
    0 ≤ (profZeta α 1 (r + τ) - profZeta α 1 r) / τ *
        (r / (r + τ)) ^ ((α - 1) / 2) ∧
    (profZeta α 1 (r + τ) - profZeta α 1 r) / τ *
        (r / (r + τ)) ^ ((α - 1) / 2) ≤
      α * (r ^ (α / 2) / (1 + r ^ α) / Real.sqrt r) := by
  have hα0 : 0 < α := by linarith
  have hs : 0 < r + τ := add_pos hr hτ
  have hrs : r < r + τ := by linarith
  have hd := vi_shell_delta hα1 hr hrs
  have hd0 : 0 < 1 - profT α r (r + τ) / (r + τ) :=
    lt_of_lt_of_le (one_div_pos.mpr hα0) hd
  have hra := Real.rpow_pos_of_pos hr α
  have hsa := Real.rpow_pos_of_pos hs α
  have hrh := Real.rpow_pos_of_pos hr (α / 2)
  have hsh := Real.rpow_pos_of_pos hs (α / 2)
  have he := vi_shell_eq hα1 hr hrs
  rw [add_sub_cancel_left] at he
  rw [← he]
  refine ⟨by positivity, ?_⟩
  have hinv : 1 / (1 - profT α r (r + τ) / (r + τ)) ≤ α := by
    rw [div_le_iff₀ hd0]
    have := mul_le_mul_of_nonneg_left hd hα0.le
    rw [mul_one_div_cancel hα0.ne'] at this
    nlinarith
  have hnum : 0 ≤ (r ^ (α / 2) / (1 + r ^ α)) *
      ((r + τ) ^ (α / 2) / (1 + (r + τ) ^ α)) / Real.sqrt (r * (r + τ)) := by positivity
  have hmain := mul_le_mul_of_nonneg_left hinv hnum
  have hk := vi_shell_k_le_one hα1 hs
  have hk0 : 0 ≤ r ^ (α / 2) / (1 + r ^ α) / Real.sqrt r := by positivity
  calc _ ≤ α * (r ^ (α / 2) / (1 + r ^ α) / Real.sqrt r) *
        ((r + τ) ^ (α / 2) / (1 + (r + τ) ^ α) / Real.sqrt (r + τ)) := by
          rw [Real.sqrt_mul hr.le] at hmain ⊢
          convert hmain using 1 <;> ring
    _ ≤ α * (r ^ (α / 2) / (1 + r ^ α) / Real.sqrt r) :=
      mul_le_of_le_one_right (mul_nonneg hα0.le hk0) hk

private lemma vi_shell_profile_cont {α : ℝ} (hα1 : 1 < α) :
    ContinuousOn (fun τ : ℝ => ∫ r in Ioi (0:ℝ),
      (profZeta α 1 (r + τ) - profZeta α 1 r) / τ *
        (r / (r + τ)) ^ ((α - 1) / 2)) (Ioi 0) := by
  have hα0 : 0 < α := by linarith
  refine continuousOn_of_dominated
    (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun τ r : ℝ => (profZeta α 1 (r + τ) - profZeta α 1 r) / τ *
      (r / (r + τ)) ^ ((α - 1) / 2))
    (bound := fun r : ℝ => α * (r ^ (α / 2) / (1 + r ^ α) / Real.sqrt r)) ?_ ?_
    ((vi_shell_k_int hα1).const_mul α) ?_
  · intro τ hτ
    have hm : Measurable (fun r : ℝ => (profZeta α 1 (r + τ) - profZeta α 1 r) / τ *
        (r / (r + τ)) ^ ((α - 1) / 2)) := by
      unfold profZeta
      fun_prop
    exact hm.aestronglyMeasurable
  · intro τ hτ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hb := vi_shell_point_bound hα1 hr hτ
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have hp : Continuous (fun τ : ℝ => (r + τ) ^ α) :=
      (continuous_const.add continuous_id).rpow_const (fun _ => Or.inr hα0.le)
    have hz : ContinuousOn (fun τ : ℝ => profZeta α 1 (r + τ)) (Ioi 0) := by
      unfold profZeta
      simp only [Real.one_rpow]
      refine hp.continuousOn.div (continuousOn_const.add hp.continuousOn) ?_
      intro τ hτ
      have := Real.rpow_pos_of_pos (add_pos hr0 hτ) α
      positivity
    have hrat : ContinuousOn (fun τ : ℝ => r / (r + τ)) (Ioi 0) :=
      continuousOn_const.div (continuousOn_const.add continuousOn_id)
        (fun τ hτ => (add_pos hr0 hτ).ne')
    exact ((hz.sub continuousOn_const).div continuousOn_id (fun τ hτ => ne_of_gt hτ)).mul
      (hrat.rpow_const (fun _ _ => Or.inr (by linarith)))

private lemma vi_shell_profile_int {α : ℝ} (hα1 : 1 < α) :
    IntegrableOn (fun τ : ℝ => ∫ r in Ioi (0:ℝ),
      (profZeta α 1 (r + τ) - profZeta α 1 r) / τ *
        (r / (r + τ)) ^ ((α - 1) / 2)) (Ioi 0) := by
  by_contra hn
  have hv := vi_shell_integral hα1
  rw [integral_undef hn, mul_zero] at hv
  have hK := vg_K_pos hα1
  have hpos : 0 < 4 * Kc α / (α - 1) := by
    have : 0 < α - 1 := by linarith
    positivity
  linarith

/-- An integrable product majorant removes compact spatial truncations uniformly
in the large parameter. This applies to the normalized sum in `vi_G_rep`. -/
private lemma vi_uniform_square_tail (F : ℝ → ℝ × ℝ → ℝ) (H : ℝ × ℝ → ℝ)
    (hH : Integrable H ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))))
    (hF : ∀ X : ℝ, 1 ≤ X → Integrable (F X)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))))
    (hbd : ∀ X : ℝ, 1 ≤ X → ∀ᵐ p ∂((volume.restrict (Ioi (0:ℝ))).prod
      (volume.restrict (Ioi (0:ℝ)))), ‖F X p‖ ≤ H p) :
    ∀ ε > 0, ∃ R : ℝ, 1 ≤ R ∧ ∀ X : ℝ, 1 ≤ X →
      |(∫ p : ℝ × ℝ, F X p ∂((volume.restrict (Ioi (0:ℝ))).prod
          (volume.restrict (Ioi (0:ℝ))))) -
        ∫ p in Icc (1 / R) R ×ˢ Icc (1 / R) R, F X p
          ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))| ≤ ε := by
  let μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))
  let S : ℝ → Set (ℝ × ℝ) := fun R => Icc (1 / R) R ×ˢ Icc (1 / R) R
  have hS : ∀ R, MeasurableSet (S R) := fun _ => measurableSet_Icc.prod measurableSet_Icc
  have hlim : Tendsto (fun R : ℝ => ∫ p, (S R)ᶜ.indicator H p ∂μ) atTop (𝓝 0) := by
    have hi : Tendsto (fun R : ℝ => 1 / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hdct : Tendsto (fun R : ℝ => ∫ p, (S R)ᶜ.indicator H p ∂μ) atTop
        (𝓝 (∫ _p : ℝ × ℝ, (0:ℝ) ∂μ)) := by
      refine tendsto_integral_filter_of_dominated_convergence (bound := fun p => ‖H p‖)
        (Filter.Eventually.of_forall fun R => hH.aestronglyMeasurable.indicator (hS R).compl)
        (Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun p => ?_)
        hH.norm ?_
      · by_cases hp : p ∈ (S R)ᶜ
        · rw [Set.indicator_of_mem hp]
        · rw [Set.indicator_of_notMem hp, norm_zero]
          exact norm_nonneg _
      · filter_upwards [vs_ae_pos (μ := volume) (ν := volume)] with p hp
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hi.eventually (Iio_mem_nhds hp.1), hi.eventually (Iio_mem_nhds hp.2),
          eventually_ge_atTop p.1, eventually_ge_atTop p.2] with R h1 h2 h3 h4
        have hpS : p ∈ S R := ⟨⟨h1.le, h3⟩, ⟨h2.le, h4⟩⟩
        rw [Set.indicator_of_notMem (show p ∉ (S R)ᶜ from fun h => h hpS)]
    simpa only [integral_zero] using hdct
  intro ε hε
  obtain ⟨R, hR, hRε⟩ := ((eventually_ge_atTop (1:ℝ)).and
    (hlim.eventually (Iio_mem_nhds hε))).exists
  refine ⟨R, hR, fun X hX => ?_⟩
  change |(∫ p, F X p ∂μ) - ∫ p in S R, F X p ∂μ| ≤ ε
  have he : (∫ p, F X p ∂μ) - ∫ p in S R, F X p ∂μ =
      ∫ p in (S R)ᶜ, F X p ∂μ := by
    have := integral_add_compl (hS R) (hF X hX)
    linarith
  rw [he, ← integral_indicator (hS R).compl, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hH.indicator (hS R).compl) ?_).trans hRε.le
  filter_upwards [hbd X hX] with p hp
  by_cases hpS : p ∈ (S R)ᶜ
  · rw [Set.indicator_of_mem hpS, Set.indicator_of_mem hpS]
    exact hp
  · rw [Set.indicator_of_notMem hpS, Set.indicator_of_notMem hpS, norm_zero]

/-- Once the normalized large-`X` limit is known, the stated endpoint equivalence
is a purely algebraic consequence. -/
private lemma vi_endpoint_of_ratio {α β : ℝ} (hα1 : 1 < α)
    (hlim : Tendsto (fun X : ℝ => profG α β X / X) atTop
      (𝓝 (4 * Kc α / (α - 1)))) :
    IsEquivalent atTop (fun X : ℝ => profG α β X)
      (fun X : ℝ => 4 * Kc α / (α - 1) * X) := by
  have hK := vg_K_pos hα1
  have hc : 0 < 4 * Kc α / (α - 1) := by
    have : 0 < α - 1 := by linarith
    positivity
  refine isEquivalent_of_tendsto_one ?_
  have h := hlim.div_const (4 * Kc α / (α - 1))
  rw [div_self hc.ne'] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  simp only [Pi.div_apply]
  field_simp

/-! ## Private helpers for the large-`X` endpoint: lag summation (`vl_*`) -/

private lemma vl_mu_vol (f : ℝ × ℝ → ℝ) (hf : ∀ p : ℝ × ℝ, ¬ (0 < p.1 ∧ 0 < p.2) → f p = 0) :
    ∫ p, f p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) = ∫ p, f p := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => hf p (by simpa using hp))

private lemma vl_xexp {q x : ℝ} (hq : 0 < q) (hx : 0 ≤ x) :
    (1 + x) * Real.exp (-q * x) ≤ (1 + 2 / q) * Real.exp (-(q / 2) * x) := by
  have h1 : 1 + q / 2 * x ≤ Real.exp (q / 2 * x) := by linarith [Real.add_one_le_exp (q / 2 * x)]
  have h2 : Real.exp (-q * x) = Real.exp (-(q / 2) * x) * Real.exp (-(q / 2 * x)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-(q / 2 * x)) * Real.exp (q / 2 * x) = 1 := by
    rw [← Real.exp_add]; simp
  have hE : 0 < Real.exp (-(q / 2 * x)) := Real.exp_pos _
  have hE2 : 0 < Real.exp (-(q / 2) * x) := Real.exp_pos _
  have hkey : (1 + x) * Real.exp (-(q / 2 * x)) ≤ (1 + 2 / q) := by
    have : (1 + x) ≤ (1 + 2 / q) * Real.exp (q / 2 * x) := by
      have hq2 : 0 < 2 / q := by positivity
      have : (1 + 2 / q) * (1 + q / 2 * x) = 1 + x + 2 / q + q / 2 * x := by
        field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 1 + 2 / q)]
    calc (1 + x) * Real.exp (-(q / 2 * x)) ≤ ((1 + 2 / q) * Real.exp (q / 2 * x)) * Real.exp (-(q / 2 * x)) :=
          mul_le_mul_of_nonneg_right this hE.le
      _ = 1 + 2 / q := by rw [mul_assoc, mul_comm (Real.exp (q / 2 * x)), h3, mul_one]
  rw [h2]
  calc (1 + x) * (Real.exp (-(q / 2) * x) * Real.exp (-(q / 2 * x)))
      = ((1 + x) * Real.exp (-(q / 2 * x))) * Real.exp (-(q / 2) * x) := by ring
    _ ≤ (1 + 2 / q) * Real.exp (-(q / 2) * x) := mul_le_mul_of_nonneg_right hkey hE2.le

private lemma vl_D_exp {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (ℓ : ℤ) (u v : ℝ), 0 < u → 0 < v →
      0 ≤ DLag β (Qm β u) (Qm β v) ℓ ∧
        DLag β (Qm β u) (Qm β v) ℓ ≤ C * Real.exp (-c * |u - v + (ℓ : ℝ)|) := by
  obtain ⟨-, -, C0, hC0⟩ := lem_app_pl_localization_i hβ0 hβ1
  have hq : 0 < -Real.log β := by
    have := Real.log_neg hβ0 hβ1
    linarith
  have hqa : |Real.log β| = -Real.log β := abs_of_neg (Real.log_neg hβ0 hβ1)
  refine ⟨|C0| * (1 + 2 / (-Real.log β)) + 1, -Real.log β / 2, by positivity, by positivity,
    fun ℓ u v hu hv => ?_⟩
  have hbd : ∀ (n : ℕ) (a b : ℝ), 0 < a → 0 < b →
      DLagNat β (Qm β a) (Qm β b) n ≤ (|C0| * (1 + 2 / (-Real.log β)) + 1) *
        Real.exp (-(-Real.log β / 2) * |a - b + (n : ℝ)|) := by
    intro n a b ha hb
    have h := hC0 n a b ha hb
    rw [hqa] at h
    have hx : 0 ≤ |a - b + (n : ℝ)| := abs_nonneg _
    have hsq : Real.sqrt (min (min a b) 1) ≤ 1 := by
      rw [Real.sqrt_le_one]; exact (min_le_right _ _)
    have hsq0 : 0 ≤ Real.sqrt (min (min a b) 1) := Real.sqrt_nonneg _
    have hex := vl_xexp hq hx
    calc _ ≤ C0 * Real.sqrt (min (min a b) 1) * (1 + |a - b + (n : ℝ)|) *
          Real.exp (-(-Real.log β) * |a - b + (n : ℝ)|) := h
      _ ≤ |C0| * 1 * ((1 + |a - b + (n : ℝ)|) * Real.exp (-(-Real.log β) * |a - b + (n : ℝ)|)) := by
          have e1 : C0 * Real.sqrt (min (min a b) 1) ≤ |C0| * 1 :=
            mul_le_mul (le_abs_self C0) hsq hsq0 (abs_nonneg _)
          have e2 : 0 ≤ (1 + |a - b + (n : ℝ)|) * Real.exp (-(-Real.log β) * |a - b + (n : ℝ)|) := by positivity
          calc _ = (C0 * Real.sqrt (min (min a b) 1)) * ((1 + |a - b + (n : ℝ)|) *
                Real.exp (-(-Real.log β) * |a - b + (n : ℝ)|)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right e1 e2
      _ ≤ |C0| * 1 * ((1 + 2 / (-Real.log β)) * Real.exp (-(-Real.log β / 2) * |a - b + (n : ℝ)|)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : -(-Real.log β / 2) = -((-Real.log β) / 2) := by ring
          rw [this]; exact hex
      _ ≤ _ := by
          have hE := Real.exp_pos (-(-Real.log β / 2) * |a - b + (n : ℝ)|)
          nlinarith [mul_pos hE hE]
  obtain ⟨hq1, -⟩ := vs_Qm hβ0 hβ1 hu
  obtain ⟨hq2, -⟩ := vs_Qm hβ0 hβ1 hv
  refine ⟨vs_DLag_nonneg hβ0 hβ1 hq1.le hq2.le ℓ, ?_⟩
  by_cases hℓ : 0 ≤ ℓ
  · have h := hbd ℓ.toNat u v hu hv
    have hc : ((ℓ.toNat : ℕ) : ℝ) = (ℓ : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hℓ
    rw [hc] at h
    simpa only [DLag, hℓ, ite_true] using h
  · have h := hbd (-ℓ).toNat v u hv hu
    have hc : (((-ℓ).toNat : ℕ) : ℝ) = -(ℓ : ℝ) := by
      have : (((-ℓ).toNat : ℕ) : ℤ) = -ℓ := Int.toNat_of_nonneg (by omega)
      have h2 : ((((-ℓ).toNat : ℕ) : ℤ) : ℝ) = ((-ℓ : ℤ) : ℝ) := by rw [this]
      rw [Int.cast_natCast] at h2
      rw [h2]; push_cast; ring
    rw [hc] at h
    have he : |v - u + -(ℓ : ℝ)| = |u - v + (ℓ : ℝ)| := by
      rw [← abs_neg]; congr 1; ring
    rw [he] at h
    simpa only [DLag, hℓ, ite_false] using h

private lemma vl_laplace_int {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => Real.exp (-c * |u|)) := by
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (-c * |u|)) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).congr_fun (fun u hu => ?_)
      measurableSet_Ioi
    simp only [abs_of_pos (show 0 < u from hu)]
  have h2 : IntegrableOn (fun u : ℝ => Real.exp (-c * |u|)) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := c) hc 0).congr_fun (fun u hu => ?_) measurableSet_Iic
    simp only [abs_of_nonpos (show u ≤ 0 from hu)]
    congr 1; ring
  have := h1.union h2
  rwa [Ioi_union_Iic, integrableOn_univ] at this

private lemma vl_shift_int {c X b : ℝ} (hc : 0 < c) (hX : 0 < X) :
    Integrable (fun s : ℝ => Real.exp (-c * |X * s - b|)) ∧
    ∫ s : ℝ, Real.exp (-c * |X * s - b|) = (∫ u : ℝ, Real.exp (-c * |u|)) / X := by
  have hg := vl_laplace_int hc
  have hg2 : Integrable (fun y : ℝ => Real.exp (-c * |y - b|)) := hg.comp_sub_right b
  refine ⟨hg2.comp_mul_left' hX.ne', ?_⟩
  have h1 := Measure.integral_comp_mul_left (fun y : ℝ => Real.exp (-c * |y - b|)) X
  have h2 : ∫ y : ℝ, Real.exp (-c * |y - b|) = ∫ u : ℝ, Real.exp (-c * |u|) :=
    integral_sub_right_eq_self (fun u : ℝ => Real.exp (-c * |u|)) b
  rw [h1, h2, abs_of_pos (inv_pos.mpr hX), smul_eq_mul]
  field_simp

private lemma vl_expint {c : ℝ} (hc : 0 < c) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (X S ℓ a : ℝ), 0 < X → a ≤ S →
      ∫ p in Icc a S ×ˢ Icc a S, Real.exp (-c * |X * (p.1 - p.2) + ℓ|) ≤
        (S - a) * (G / X) := by
  refine ⟨∫ u : ℝ, Real.exp (-c * |u|), integral_nonneg (fun u => (Real.exp_pos _).le),
    fun X S ℓ a hX haS => ?_⟩
  have hcont : Continuous (fun p : ℝ × ℝ => Real.exp (-c * |X * (p.1 - p.2) + ℓ|)) := by
    fun_prop
  have hint : IntegrableOn (fun p : ℝ × ℝ => Real.exp (-c * |X * (p.1 - p.2) + ℓ|))
      (Icc a S ×ˢ Icc a S) volume :=
    hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod, setIntegral_prod _ (by rwa [← Measure.volume_eq_prod])]
  have hinner : ∀ r : ℝ, ‖∫ s in Icc a S, Real.exp (-c * |X * (r - s) + ℓ|)‖ ≤
      (∫ u : ℝ, Real.exp (-c * |u|)) / X := by
    intro r
    obtain ⟨hi, hv⟩ := vl_shift_int (c := c) (X := X) (b := X * r + ℓ) hc hX
    have he : ∀ s : ℝ, Real.exp (-c * |X * (r - s) + ℓ|) =
        Real.exp (-c * |X * s - (X * r + ℓ)|) := by
      intro s
      rw [← abs_neg]; congr 3; ring
    simp only [he]
    rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Icc
      (fun s _ => (Real.exp_pos _).le))]
    calc _ ≤ ∫ s : ℝ, Real.exp (-c * |X * s - (X * r + ℓ)|) :=
          setIntegral_le_integral hi (Filter.Eventually.of_forall fun s => (Real.exp_pos _).le)
      _ = _ := hv
  have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ)) (s := Icc a S)
    (f := fun r => ∫ s in Icc a S, Real.exp (-c * |X * (r - s) + ℓ|))
    (C := (∫ u : ℝ, Real.exp (-c * |u|)) / X) (by simp) (fun r _ => hinner r)
  refine le_trans (le_abs_self _) ?_
  refine (Real.norm_eq_abs _ ▸ this).trans ?_
  rw [Real.volume_real_Icc_of_le haS]
  linarith [le_refl ((S - a) * ((∫ u : ℝ, Real.exp (-c * |u|)) / X))]

open Muon.DetEquiv ProbabilityTheory in
private lemma vl_DE_meas {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {X : ℝ} (hX : 0 < X) (ℓ : ℤ) :
    AEMeasurable (fun p : ℝ × ℝ => DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ∧
    AEMeasurable (fun p : ℝ × ℝ => Efun β (X * p.1))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ∧
    AEMeasurable (fun p : ℝ × ℝ => Efun β (X * p.2))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  have hae : ∀ᵐ p ∂μ, 0 < p.1 ∧ 0 < p.2 := vs_ae_pos
  have hQm : AEMeasurable (Qm β) (volume.restrict (Ioi (0:ℝ))) :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Ioi (vs_Qm_mono hβ0 hβ1)
  have hQ1 : AEMeasurable (fun p : ℝ × ℝ => Qm β p.1) μ := hQm.comp_fst
  have hQ2 : AEMeasurable (fun p : ℝ × ℝ => Qm β p.2) μ := hQm.comp_snd
  have hpair : AEMeasurable (fun p : ℝ × ℝ => (Qm β p.1, Qm β p.2)) μ := hQ1.prodMk hQ2
  have hSm : MeasurableSet {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)
  have hD : AEMeasurable (fun p : ℝ × ℝ => DLag β (Qm β p.1) (Qm β p.2) ℓ) μ := by
    classical
    have hg : Measurable ({q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}.piecewise
        (fun q : ℝ × ℝ => DLag β q.1 q.2 ℓ) 0) :=
      ContinuousOn.measurable_piecewise (vs_DLag_cont hβ0 hβ1 ℓ) continuousOn_const hSm
    refine (hg.comp_aemeasurable hpair).congr ?_
    filter_upwards [hae] with p hp
    have h1 := (vs_Qm hβ0 hβ1 hp.1).1
    have h2 := (vs_Qm hβ0 hβ1 hp.2).1
    simp only [Function.comp]
    rw [Set.piecewise_eq_of_mem _ _ _ (show (Qm β p.1, Qm β p.2) ∈
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} from ⟨h1.le, h2.le⟩)]
  have hE : AEMeasurable (Efun β) (volume.restrict (Ioi (0:ℝ))) := by
    unfold Efun
    exact hQm.mul ((measurable_deriv (rW (emaW β))).comp_aemeasurable hQm)
  have hq := vz_qmp hX
  have hE1 : AEMeasurable (fun p : ℝ × ℝ => Efun β p.1) μ :=
    hE.comp_fst (ν := volume.restrict (Ioi (0:ℝ)))
  have hE2 : AEMeasurable (fun p : ℝ × ℝ => Efun β p.2) μ :=
    hE.comp_snd (μ := volume.restrict (Ioi (0:ℝ)))
  have h1 := hD.comp_quasiMeasurePreserving hq
  have h2 := hE1.comp_quasiMeasurePreserving hq
  have h3 := hE2.comp_quasiMeasurePreserving hq
  simp only [Function.comp_def, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

open Muon.DetEquiv ProbabilityTheory in
private lemma vl_term_meas {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {X : ℝ}
    (hX : 0 < X) (ℓ : ℤ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
        Real.sqrt (p.1 * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β ℓ (X * p.1) (X * p.2)))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hα0 : 0 < α := by linarith
  have hm := ((vs_F_meas (α := α) hβ0 hβ1 X ℓ).comp_quasiMeasurePreserving
    (vz_qmp hX)).const_mul X
  refine hm.congr ?_
  filter_upwards [vs_ae_pos (μ := volume) (ν := volume)] with p hp
  change X * (_ * _) = _
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [← mul_assoc, vi_coefficient_scale hα0 hX hp.1 hp.2]

private lemma vl_a_le_one {α r s : ℝ} (hα1 : 1 < α) (hr : 0 < r) (hs : 0 < s) :
    0 ≤ (r ^ (α / 2) / (1 + r ^ α)) * (s ^ (α / 2) / (1 + s ^ α)) / Real.sqrt (r * s) ∧
    (r ^ (α / 2) / (1 + r ^ α)) * (s ^ (α / 2) / (1 + s ^ α)) / Real.sqrt (r * s) ≤ 1 := by
  have hra := Real.rpow_pos_of_pos hr α
  have hsa := Real.rpow_pos_of_pos hs α
  have hrh := Real.rpow_pos_of_pos hr (α / 2)
  have hsh := Real.rpow_pos_of_pos hs (α / 2)
  refine ⟨by positivity, ?_⟩
  have h1 := vi_shell_k_le_one hα1 hr
  have h2 := vi_shell_k_le_one hα1 hs
  have hk1 : 0 ≤ r ^ (α / 2) / (1 + r ^ α) / Real.sqrt r := by positivity
  have hk2 : 0 ≤ s ^ (α / 2) / (1 + s ^ α) / Real.sqrt s := by positivity
  have := mul_le_mul h1 h2 hk2 zero_le_one
  rw [Real.sqrt_mul hr.le]
  calc _ = r ^ (α / 2) / (1 + r ^ α) / Real.sqrt r * (s ^ (α / 2) / (1 + s ^ α) / Real.sqrt s) := by
        field_simp
    _ ≤ 1 := by linarith

open Muon.DetEquiv ProbabilityTheory in
private lemma vl_T_bound {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (T : ℝ → ℤ → ℝ × ℝ → ℝ)
    (hT : ∀ X ℓ p, T X ℓ p =
      ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
        Real.sqrt (p.1 * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β ℓ (X * p.1) (X * p.2))) :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ (X S : ℝ) (ℓ : ℤ) (p : ℝ × ℝ), 1 ≤ S → S ≤ X →
      p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S →
      0 ≤ T X ℓ p ∧ T X ℓ p ≤ M * Real.exp (-c * |X * (p.1 - p.2) + ℓ|) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨K, hK0, hK⟩ := vs_theta_bd hα1 hβ0 hβ1
  obtain ⟨C0, c0, hC0, hc0, hD⟩ := vl_D_exp hβ0 hβ1
  refine ⟨α * K * K * C0, c0, by positivity, hc0, fun X S ℓ p hS hSX hp => ?_⟩
  have hS0 : 0 < S := by linarith
  have hr : 1 / S ≤ p.1 := hp.1.1
  have hs : 1 / S ≤ p.2 := hp.2.1
  have hr0 : 0 < p.1 := lt_of_lt_of_le (by positivity) hr
  have hs0 : 0 < p.2 := lt_of_lt_of_le (by positivity) hs
  have hX0 : 0 < X := by linarith
  have hu : 0 < X * p.1 := mul_pos hX0 hr0
  have hv : 0 < X * p.2 := mul_pos hX0 hs0
  have h1u : 1 ≤ X * p.1 := by
    have : 1 ≤ S * p.1 := by
      have := mul_le_mul_of_nonneg_left hr hS0.le
      rwa [mul_one_div_cancel hS0.ne'] at this
    nlinarith
  have h1v : 1 ≤ X * p.2 := by
    have : 1 ≤ S * p.2 := by
      have := mul_le_mul_of_nonneg_left hs hS0.le
      rwa [mul_one_div_cancel hS0.ne'] at this
    nlinarith
  obtain ⟨hθ1, hθ1'⟩ := hK _ hu
  obtain ⟨hθ2, hθ2'⟩ := hK _ hv
  rw [min_eq_right h1u, div_one] at hθ1'
  rw [min_eq_right h1v, div_one] at hθ2'
  obtain ⟨hq1, -⟩ := vs_Qm hβ0 hβ1 hu
  obtain ⟨hq2, -⟩ := vs_Qm hβ0 hβ1 hv
  obtain ⟨hD0, hD1⟩ := hD ℓ (X * p.1) (X * p.2) hu hv
  have hΔ := vs_Delta_ge hα1 hβ0 hβ1 hu hv ℓ
  have hΔ0 : 0 < profDelta α β ℓ (X * p.1) (X * p.2) := lt_of_lt_of_le (by positivity) hΔ
  have hinv : 1 / profDelta α β ℓ (X * p.1) (X * p.2) ≤ α := by
    rw [div_le_iff₀ hΔ0]
    have := mul_le_mul_of_nonneg_left hΔ hα0.le
    rw [mul_one_div_cancel hα0.ne'] at this
    nlinarith
  obtain ⟨ha0, ha1⟩ := vl_a_le_one hα1 hr0 hs0
  have hexp : Real.exp (-c0 * |X * p.1 - X * p.2 + (ℓ : ℝ)|) =
      Real.exp (-c0 * |X * (p.1 - p.2) + ℓ|) := by congr 3; ring
  rw [hT]
  have hDn : 0 ≤ DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ * profTheta α β (X * p.1) *
      profTheta α β (X * p.2) / profDelta α β ℓ (X * p.1) (X * p.2) := by positivity
  refine ⟨by positivity, ?_⟩
  have hmain : DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ * profTheta α β (X * p.1) *
      profTheta α β (X * p.2) / profDelta α β ℓ (X * p.1) (X * p.2) ≤
      (C0 * Real.exp (-c0 * |X * (p.1 - p.2) + ℓ|)) * K * K * α := by
    rw [← hexp] at *
    have e1 : DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ * profTheta α β (X * p.1) *
        profTheta α β (X * p.2) ≤ (C0 * Real.exp (-c0 * |X * p.1 - X * p.2 + (ℓ : ℝ)|)) * K * K :=
      mul_le_mul (mul_le_mul hD1 hθ1' hθ1.le (le_trans hD0 hD1)) hθ2' hθ2.le
        (by positivity)
    calc _ = (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ * profTheta α β (X * p.1) *
          profTheta α β (X * p.2)) * (1 / profDelta α β ℓ (X * p.1) (X * p.2)) := by ring
      _ ≤ ((C0 * Real.exp (-c0 * |X * p.1 - X * p.2 + (ℓ : ℝ)|)) * K * K) * α :=
          mul_le_mul e1 hinv (by positivity) (by positivity)
  calc _ ≤ 1 * ((C0 * Real.exp (-c0 * |X * (p.1 - p.2) + ℓ|)) * K * K * α) :=
        mul_le_mul ha1 hmain hDn zero_le_one
    _ = _ := by ring

private lemma vl_profT_symm {α u v : ℝ} : profT α u v = profT α v u := by
  unfold profT
  by_cases h : u = v
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), ← neg_div_neg_eq]
    congr 1 <;> ring

open Muon.DetEquiv ProbabilityTheory in
private lemma vl_T_neg {α β : ℝ}
    (T : ℝ → ℤ → ℝ × ℝ → ℝ)
    (hT : ∀ X ℓ p, T X ℓ p =
      ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
        Real.sqrt (p.1 * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β ℓ (X * p.1) (X * p.2)))
    (X : ℝ) (m : ℕ) (hm : 1 ≤ m) (p : ℝ × ℝ) :
    T X (-(m : ℤ)) p = T X (m : ℤ) p.swap := by
  have hn : ¬ (0 : ℤ) ≤ -(m : ℤ) := by omega
  have hD : DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) (-(m : ℤ)) =
      DLag β (Qm β (X * p.2)) (Qm β (X * p.1)) (m : ℤ) := by
    have hm0 : m ≠ 0 := by omega
    simp [DLag, hm0]
  have hM : MLag β (Qm β (X * p.1)) (Qm β (X * p.2)) (-(m : ℤ)) =
      MLag β (Qm β (X * p.2)) (Qm β (X * p.1)) (m : ℤ) := by
    have hm0 : m ≠ 0 := by omega
    simp [MLag, hm0]
  have hΔ : profDelta α β (-(m : ℤ)) (X * p.1) (X * p.2) =
      profDelta α β (m : ℤ) (X * p.2) (X * p.1) := by
    unfold profDelta
    rw [hM, vl_profT_symm (u := X * p.1), mul_comm (X * p.1)]
  rw [hT, hT, hD, hΔ]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [mul_comm p.2 p.1]
  ring_nf

private lemma vl_B_symm {α β : ℝ}
    (T : ℝ → ℤ → ℝ × ℝ → ℝ)
    (hT : ∀ X ℓ p, T X ℓ p =
      ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
        Real.sqrt (p.1 * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β ℓ (X * p.1) (X * p.2)))
    (χ : ℝ × ℝ → ℝ) (hχ : ∀ p, χ p.swap = χ p) (X : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ∫ p, χ p * T X (-(m : ℤ)) p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) =
    ∫ p, χ p * T X (m : ℤ) p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have h1 : ∀ p, χ p * T X (-(m : ℤ)) p = (fun z => χ z * T X (m : ℤ) z) p.swap := by
    intro p
    simp only [hχ p, vl_T_neg T hT X m hm p]
  simp_rw [h1]
  exact integral_prod_swap (fun z : ℝ × ℝ => χ z * T X (m : ℤ) z)
    (μ := volume.restrict (Ioi (0:ℝ))) (ν := volume.restrict (Ioi (0:ℝ)))

open Muon.DetEquiv ProbabilityTheory in
private lemma vl_B_bd {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (T : ℝ → ℤ → ℝ × ℝ → ℝ)
    (hT : ∀ X ℓ p, T X ℓ p =
      ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
        Real.sqrt (p.1 * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β ℓ (X * p.1) (X * p.2))) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (X S : ℝ) (ℓ : ℤ) (χ : ℝ × ℝ → ℝ), 1 ≤ S → S ≤ X →
      (∀ p, 0 ≤ χ p) → (∀ p, χ p ≤ 1) →
      (∀ p, χ p ≠ 0 → p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S) →
      0 ≤ ∫ p, χ p * T X ℓ p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ∧
      ∫ p, χ p * T X ℓ p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ≤
        C * S / X ∧
      (2 * S * X ≤ |(ℓ : ℝ)| →
        ∫ p, χ p * T X ℓ p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ≤
          C * S / X * Real.exp (-c * |(ℓ : ℝ)|)) := by
  obtain ⟨M, c0, hM, hc0, hTb⟩ := vl_T_bound hα1 hβ0 hβ1 T hT
  obtain ⟨G1, hG1, hG1b⟩ := vl_expint (c := c0) hc0
  obtain ⟨G2, hG2, hG2b⟩ := vl_expint (c := c0 / 2) (by positivity)
  refine ⟨M * (G1 + G2) + 1, c0 / 4, by positivity, by positivity,
    fun X S ℓ χ hS hSX hχ0 hχ1 hχS => ?_⟩
  have hS0 : 0 < S := by linarith
  have hX0 : 0 < X := by linarith
  have hSq : MeasurableSet (Icc (1 / S) S ×ˢ Icc (1 / S) S) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hSsub : ∀ p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S, 0 < p.1 ∧ 0 < p.2 := by
    intro p hp
    exact ⟨lt_of_lt_of_le (by positivity) hp.1.1, lt_of_lt_of_le (by positivity) hp.2.1⟩
  have hnn : 0 ≤ ∫ p, χ p * T X ℓ p ∂((volume.restrict (Ioi (0:ℝ))).prod
      (volume.restrict (Ioi (0:ℝ)))) := by
    apply integral_nonneg_of_ae
    filter_upwards with p
    by_cases h : χ p = 0
    · simp [h]
    · exact mul_nonneg (hχ0 p) (hTb X S ℓ p hS hSX (hχS p h)).1
  -- generic comparison with an exponential majorant
  have key : ∀ (K c : ℝ), 0 ≤ K → 0 < c →
      (∀ p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S,
        T X ℓ p ≤ K * Real.exp (-c * |X * (p.1 - p.2) + ℓ|)) →
      ∀ G : ℝ, (∫ p in Icc (1 / S) S ×ˢ Icc (1 / S) S,
        Real.exp (-c * |X * (p.1 - p.2) + ℓ|)) ≤ S * (G / X) → 0 ≤ G →
      ∫ p, χ p * T X ℓ p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ≤
        K * (S * (G / X)) := by
    intro K c hK hc hpt G hint hG
    set g : ℝ × ℝ → ℝ := (Icc (1 / S) S ×ˢ Icc (1 / S) S).indicator
      (fun p => K * Real.exp (-c * |X * (p.1 - p.2) + ℓ|)) with hg
    have hgc : Continuous (fun p : ℝ × ℝ => K * Real.exp (-c * |X * (p.1 - p.2) + ℓ|)) := by
      fun_prop
    have hgi : Integrable g volume :=
      (hgc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).integrable_indicator hSq
    have hgi' : Integrable g ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hgi.mono_measure Measure.restrict_le_self
    refine le_trans (integral_mono_of_nonneg ?_ hgi' ?_) ?_
    · filter_upwards with p
      by_cases h : χ p = 0
      · simp [h]
      · exact mul_nonneg (hχ0 p) (hTb X S ℓ p hS hSX (hχS p h)).1
    · filter_upwards with p
      by_cases h : χ p = 0
      · simp only [h, zero_mul, hg]
        exact Set.indicator_nonneg (fun q _ => by positivity) p
      · have hp := hχS p h
        simp only [hg, Set.indicator_of_mem hp]
        calc χ p * T X ℓ p ≤ 1 * T X ℓ p :=
              mul_le_mul_of_nonneg_right (hχ1 p) (hTb X S ℓ p hS hSX hp).1
          _ ≤ _ := by rw [one_mul]; exact hpt p hp
    · rw [vl_mu_vol g (fun p hp => by
        simp only [hg]
        apply Set.indicator_of_notMem
        intro h; exact hp (hSsub p h)), hg, integral_indicator hSq, integral_const_mul]
      exact mul_le_mul_of_nonneg_left hint hK
  have hrel : ∀ (G : ℝ), 0 ≤ G → (S - 1 / S) * (G / X) ≤ S * (G / X) := by
    intro G hG
    have : 0 < 1 / S := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hb1 := key M c0 hM.le hc0 (fun p hp => (hTb X S ℓ p hS hSX hp).2) G1
    ((hG1b X S ℓ (1 / S) hX0 (by rw [div_le_iff₀ hS0]; nlinarith)).trans (hrel G1 hG1)) hG1
  refine ⟨hnn, ?_, fun hℓ => ?_⟩
  · refine hb1.trans ?_
    have : M * (S * (G1 / X)) ≤ (M * (G1 + G2) + 1) * S / X := by
      rw [show (M * (G1 + G2) + 1) * S / X = (M * (G1 + G2) + 1) * (S / X) by ring]
      rw [show M * (S * (G1 / X)) = (M * G1) * (S / X) by ring]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    exact this
  · -- tail
    have hpt : ∀ p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S,
        T X ℓ p ≤ (M * Real.exp (-(c0 / 2) * (|(ℓ : ℝ)| / 2))) *
          Real.exp (-(c0 / 2) * |X * (p.1 - p.2) + ℓ|) := by
      intro p hp
      have h1 := (hTb X S ℓ p hS hSX hp).2
      have hdiff : |p.1 - p.2| ≤ S := by
        rw [abs_le]
        have := hp.1.2; have := hp.2.2; have := hp.1.1; have := hp.2.1
        have hS1 : 1 / S ≤ S := by rw [div_le_iff₀ hS0]; nlinarith
        have hS2 : 0 < 1 / S := by positivity
        constructor <;> linarith
      have ht : |(ℓ : ℝ)| / 2 ≤ |X * (p.1 - p.2) + ℓ| := by
        have h2 : |(ℓ : ℝ)| ≤ |X * (p.1 - p.2) + ℓ| + |X * (p.1 - p.2)| := by
          have := abs_sub (X * (p.1 - p.2) + ℓ) (X * (p.1 - p.2))
          have e : (X * (p.1 - p.2) + ℓ) - X * (p.1 - p.2) = (ℓ : ℝ) := by ring
          rwa [e] at this
        have h3 : |X * (p.1 - p.2)| ≤ S * X := by
          rw [abs_mul, abs_of_pos hX0]; nlinarith [abs_nonneg (p.1 - p.2)]
        linarith
      refine h1.trans ?_
      have : Real.exp (-c0 * |X * (p.1 - p.2) + ℓ|) ≤
          Real.exp (-(c0 / 2) * (|(ℓ : ℝ)| / 2)) * Real.exp (-(c0 / 2) * |X * (p.1 - p.2) + ℓ|) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left ht hc0.le]
      calc M * Real.exp (-c0 * |X * (p.1 - p.2) + ℓ|) ≤ M * (Real.exp (-(c0 / 2) * (|(ℓ : ℝ)| / 2)) *
            Real.exp (-(c0 / 2) * |X * (p.1 - p.2) + ℓ|)) := mul_le_mul_of_nonneg_left this hM.le
        _ = _ := by ring
    have hb2 := key (M * Real.exp (-(c0 / 2) * (|(ℓ : ℝ)| / 2))) (c0 / 2) (by positivity)
      (by positivity) hpt G2
      ((hG2b X S ℓ (1 / S) hX0 (by rw [div_le_iff₀ hS0]; nlinarith)).trans (hrel G2 hG2)) hG2
    refine hb2.trans ?_
    have he : Real.exp (-(c0 / 2) * (|(ℓ : ℝ)| / 2)) = Real.exp (-(c0 / 4) * |(ℓ : ℝ)|) := by
      congr 1; ring
    rw [he]
    have : M * Real.exp (-(c0 / 4) * |(ℓ : ℝ)|) * (S * (G2 / X)) ≤
        (M * (G1 + G2) + 1) * S / X * Real.exp (-(c0 / 4) * |(ℓ : ℝ)|) := by
      have hE := (Real.exp_pos (-(c0 / 4) * |(ℓ : ℝ)|)).le
      calc _ = (M * G2) * (S / X) * Real.exp (-(c0 / 4) * |(ℓ : ℝ)|) := by ring
        _ ≤ ((M * (G1 + G2) + 1) * (S / X)) * Real.exp (-(c0 / 4) * |(ℓ : ℝ)|) := by
            apply mul_le_mul_of_nonneg_right _ hE
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            nlinarith
        _ = _ := by ring
    exact this

set_option maxHeartbeats 1000000 in
open Muon.DetEquiv ProbabilityTheory in
private lemma vl_bracket {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (S k A : ℝ) (hS : 1 ≤ S) (hk : 1 ≤ k) (hA : 0 ≤ A) :
    ∃ Cb X1 : ℝ, 0 ≤ Cb ∧ S ≤ X1 ∧ ∀ (X : ℝ) (ℓ : ℕ) (p : ℝ × ℝ) (ω : ℝ),
      X1 ≤ X → X / k ≤ (ℓ : ℝ) → p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S →
      0 ≤ ω → ω ≤ 1 → (1 / (2 * k) ≤ p.2 - p.1 → ω = 1) → (ω ≠ 0 → p.1 < p.2) →
      |((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
          Real.sqrt (p.1 * p.2)) *
          ((Efun β (X * p.1) * profTheta α β (X * p.1)) *
            (Efun β (X * p.2) * profTheta α β (X * p.2))) /
              profDelta α β (ℓ : ℤ) (X * p.1) (X * p.2) -
        ω * ((profZeta α 1 p.2 - profZeta α 1 p.1) / (p.2 - p.1) *
          (p.1 / p.2) ^ ((α - 1) / 2))| ≤ 5 * α ∧
      (|X * (p.1 - p.2) + (ℓ : ℝ)| ≤ A →
        |((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
          Real.sqrt (p.1 * p.2)) *
          ((Efun β (X * p.1) * profTheta α β (X * p.1)) *
            (Efun β (X * p.2) * profTheta α β (X * p.2))) /
              profDelta α β (ℓ : ℤ) (X * p.1) (X * p.2) -
        ω * ((profZeta α 1 p.2 - profZeta α 1 p.1) / (p.2 - p.1) *
          (p.1 / p.2) ^ ((α - 1) / 2))| ≤ Cb / X) := by
  have hα0 : 0 < α := by linarith
  have hS0 : 0 < S := by linarith
  have hk0 : 0 < k := by linarith
  have hδ : 0 < 1 / S := by positivity
  obtain ⟨Cθ, hCθ, hθ⟩ := vi_theta_error hα1 hβ0 hβ1
  obtain ⟨CΔ, hCΔ, hΔ⟩ := vi_delta_scaled_error hα1 hβ0 hβ1 hδ A
  refine ⟨3 * Cθ * S * α + α ^ 2 * (CΔ * S), max (max S (2 * Cθ * S)) (2 * k * A),
    by positivity, (le_max_left _ _).trans (le_max_left _ _), ?_⟩
  intro X ℓ p ω hX hℓ hp hωnn hω1 hω hωp
  have hXS : S ≤ X := ((le_max_left _ _).trans (le_max_left _ _)).trans hX
  have hXC : 2 * Cθ * S ≤ X := ((le_max_right _ _).trans (le_max_left _ _)).trans hX
  have hXA : 2 * k * A ≤ X := (le_max_right _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hr : 1 / S ≤ p.1 := hp.1.1
  have hs : 1 / S ≤ p.2 := hp.2.1
  have hr0 : 0 < p.1 := lt_of_lt_of_le hδ hr
  have hs0 : 0 < p.2 := lt_of_lt_of_le hδ hs
  have hu : 0 < X * p.1 := mul_pos hX0 hr0
  have hv : 0 < X * p.2 := mul_pos hX0 hs0
  have h1u : 1 ≤ X * p.1 := by
    have : 1 ≤ S * p.1 := by
      have := mul_le_mul_of_nonneg_left hr hS0.le
      rwa [mul_one_div_cancel hS0.ne'] at this
    nlinarith
  have h1v : 1 ≤ X * p.2 := by
    have : 1 ≤ S * p.2 := by
      have := mul_le_mul_of_nonneg_left hs hS0.le
      rwa [mul_one_div_cancel hS0.ne'] at this
    nlinarith
  -- bounds on the elasticity products
  have heb : ∀ q : ℝ, 1 / S ≤ q → 0 < q → |Efun β (X * q) * profTheta α β (X * q) - 1| ≤ Cθ * S / X := by
    intro q hq hq0
    refine (hθ (X * q) (mul_pos hX0 hq0)).trans ?_
    rw [div_le_div_iff₀ (mul_pos hX0 hq0) hX0]
    have : 1 ≤ S * q := by
      have := mul_le_mul_of_nonneg_left hq hS0.le
      rwa [mul_one_div_cancel hS0.ne'] at this
    nlinarith [mul_nonneg hCθ.le (sub_nonneg.2 this), mul_pos hX0 hCθ]
  have he1 := heb p.1 hr hr0
  have he2 := heb p.2 hs hs0
  have hsmall : Cθ * S / X ≤ 1 / 2 := by
    rw [div_le_iff₀ hX0]; nlinarith
  have hE1 : Efun β (X * p.1) * profTheta α β (X * p.1) ≤ 3 / 2 := by
    have := (abs_le.1 (he1.trans hsmall)).2; linarith
  have hE2 : Efun β (X * p.2) * profTheta α β (X * p.2) ≤ 3 / 2 := by
    have := (abs_le.1 (he2.trans hsmall)).2; linarith
  have hE1' : 0 ≤ Efun β (X * p.1) * profTheta α β (X * p.1) := by
    have := (abs_le.1 (he1.trans hsmall)).1; linarith
  have hE2' : 0 ≤ Efun β (X * p.2) * profTheta α β (X * p.2) := by
    have := (abs_le.1 (he2.trans hsmall)).1; linarith
  have hprod : |(Efun β (X * p.1) * profTheta α β (X * p.1)) *
      (Efun β (X * p.2) * profTheta α β (X * p.2)) - 1| ≤ 3 * (Cθ * S / X) := by
    set e1 := Efun β (X * p.1) * profTheta α β (X * p.1)
    set e2 := Efun β (X * p.2) * profTheta α β (X * p.2)
    have : e1 * e2 - 1 = (e1 - 1) * e2 + (e2 - 1) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hE2']
    have h3 : |e1 - 1| * e2 ≤ (Cθ * S / X) * (3 / 2) :=
      mul_le_mul he1 hE2 hE2' (by positivity)
    have hq0 : 0 ≤ Cθ * S / X := by positivity
    linarith
  -- determinant and coefficient
  have hΔg := vs_Delta_ge hα1 hβ0 hβ1 hu hv (ℓ : ℤ)
  have hΔ0 : 0 < profDelta α β (ℓ : ℤ) (X * p.1) (X * p.2) := lt_of_lt_of_le (by positivity) hΔg
  have hinv : 1 / profDelta α β (ℓ : ℤ) (X * p.1) (X * p.2) ≤ α := by
    rw [div_le_iff₀ hΔ0]
    have := mul_le_mul_of_nonneg_left hΔg hα0.le
    rw [mul_one_div_cancel hα0.ne'] at this
    nlinarith
  obtain ⟨ha0, ha1⟩ := vl_a_le_one hα1 hr0 hs0
  set a := (p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
    Real.sqrt (p.1 * p.2) with ha
  set Δ := profDelta α β (ℓ : ℤ) (X * p.1) (X * p.2) with hΔdef
  set e1 := Efun β (X * p.1) * profTheta α β (X * p.1)
  set e2 := Efun β (X * p.2) * profTheta α β (X * p.2)
  have hx0 : 0 ≤ a * (e1 * e2) / Δ := by positivity
  have hx1 : a * (e1 * e2) / Δ ≤ 9 / 4 * α := by
    have h12 : e1 * e2 ≤ 9 / 4 := by nlinarith
    calc a * (e1 * e2) / Δ = (a * (e1 * e2)) * (1 / Δ) := by ring
      _ ≤ (1 * (9 / 4)) * α := by
          apply mul_le_mul _ hinv (by positivity) (by norm_num)
          exact mul_le_mul ha1 h12 (by positivity) zero_le_one
      _ = _ := by ring
  -- shell bound
  have hshell : ∀ q : ℝ × ℝ, ω ≠ 0 → q = p →
      0 ≤ (profZeta α 1 q.2 - profZeta α 1 q.1) / (q.2 - q.1) * (q.1 / q.2) ^ ((α - 1) / 2) ∧
      (profZeta α 1 q.2 - profZeta α 1 q.1) / (q.2 - q.1) * (q.1 / q.2) ^ ((α - 1) / 2) ≤ α := by
    intro q hω0 hq
    subst hq
    have hlt := hωp hω0
    have heq := vi_shell_eq hα1 hr0 hlt
    have hd := vi_shell_delta hα1 hr0 hlt
    have hd0 : 0 < 1 - profT α q.1 q.2 / q.2 := lt_of_lt_of_le (by positivity) hd
    rw [← heq]
    refine ⟨by positivity, ?_⟩
    have hinv' : 1 / (1 - profT α q.1 q.2 / q.2) ≤ α := by
      rw [div_le_iff₀ hd0]
      have := mul_le_mul_of_nonneg_left hd hα0.le
      rw [mul_one_div_cancel hα0.ne'] at this
      nlinarith
    calc a / (1 - profT α q.1 q.2 / q.2) = a * (1 / (1 - profT α q.1 q.2 / q.2)) := by ring
      _ ≤ 1 * α := mul_le_mul ha1 hinv' (by positivity) zero_le_one
      _ = α := one_mul _
  have hy : 0 ≤ ω * ((profZeta α 1 p.2 - profZeta α 1 p.1) / (p.2 - p.1) *
          (p.1 / p.2) ^ ((α - 1) / 2)) ∧
      ω * ((profZeta α 1 p.2 - profZeta α 1 p.1) / (p.2 - p.1) *
          (p.1 / p.2) ^ ((α - 1) / 2)) ≤ α := by
    by_cases hω0 : ω = 0
    · simp [hω0]; exact hα0.le
    · obtain ⟨h1, h2⟩ := hshell p hω0 rfl
      exact ⟨mul_nonneg hωnn h1, (mul_le_mul_of_nonneg_right hω1 h1).trans (by linarith)⟩
  refine ⟨?_, fun hA' => ?_⟩
  · rw [abs_le]
    constructor <;> linarith [hy.1, hy.2, hx0, hx1]
  · -- good region
    have hgap : 1 / (2 * k) ≤ p.2 - p.1 := by
      have h1 := (abs_le.1 hA').2
      have h2 : X / k - A ≤ X * (p.2 - p.1) := by linarith
      have h3 : X / (2 * k) ≤ X / k - A := by
        have : A ≤ X / (2 * k) := by rw [le_div_iff₀ (by positivity)]; nlinarith
        have e : X / k = X / (2 * k) + X / (2 * k) := by field_simp; ring
        linarith
      have h4 : X / (2 * k) ≤ X * (p.2 - p.1) := h3.trans h2
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * k)] at h4
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * k)]
      nlinarith
    have hω1' : ω = 1 := hω hgap
    have hlt : p.1 < p.2 := by
      have : 0 < 1 / (2 * k) := by positivity
      linarith
    have heq := vi_shell_eq hα1 hr0 hlt
    have hd := vi_shell_delta hα1 hr0 hlt
    set Δ' := 1 - profT α p.1 p.2 / p.2 with hΔ'
    have hd0 : 0 < Δ' := lt_of_lt_of_le (by positivity) hd
    have hinv' : 1 / Δ' ≤ α := by
      rw [div_le_iff₀ hd0]
      have := mul_le_mul_of_nonneg_left hd hα0.le
      rw [mul_one_div_cancel hα0.ne'] at this
      nlinarith
    rw [hω1', one_mul, ← heq]
    have hdiff := hΔ X p.1 p.2 ℓ hX0 hr hs h1u h1v (by
      have : X * p.1 - X * p.2 + (ℓ : ℝ) = X * (p.1 - p.2) + ℓ := by ring
      rw [this]; exact hA')
    have hdiff' : |Δ - Δ'| ≤ CΔ * S / X := by
      refine hdiff.trans (le_of_eq ?_)
      field_simp
    have hid : a * (e1 * e2) / Δ - a / Δ' =
        a * ((e1 * e2 - 1) * (1 / Δ)) + a * ((1 / Δ - 1 / Δ')) := by
      field_simp
      ring
    have hd1 : |1 / Δ - 1 / Δ'| ≤ α ^ 2 * (CΔ * S / X) := by
      have : 1 / Δ - 1 / Δ' = (Δ' - Δ) / (Δ * Δ') := by
        field_simp
      rw [this, abs_div, abs_mul, abs_of_pos hΔ0, abs_of_pos hd0, abs_sub_comm]
      rw [div_le_iff₀ (mul_pos hΔ0 hd0)]
      have hΔα : 1 / α ≤ Δ := hΔg
      have hΔ'α : 1 / α ≤ Δ' := hd
      have hprod' : 1 / α ^ 2 ≤ Δ * Δ' := by
        calc 1 / α ^ 2 = (1 / α) * (1 / α) := by ring
          _ ≤ Δ * Δ' := mul_le_mul hΔα hΔ'α (by positivity) hΔ0.le
      calc |Δ - Δ'| ≤ CΔ * S / X := hdiff'
        _ = α ^ 2 * (CΔ * S / X) * (1 / α ^ 2) := by field_simp
        _ ≤ α ^ 2 * (CΔ * S / X) * (Δ * Δ') :=
            mul_le_mul_of_nonneg_left hprod' (by positivity)
    rw [hid]
    refine (abs_add_le _ _).trans ?_
    have t1 : |a * ((e1 * e2 - 1) * (1 / Δ))| ≤ 3 * (Cθ * S / X) * α := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_pos (by positivity : 0 < 1 / Δ)]
      calc a * (|e1 * e2 - 1| * (1 / Δ)) ≤ 1 * ((3 * (Cθ * S / X)) * α) :=
            mul_le_mul ha1 (mul_le_mul hprod hinv (by positivity) (by positivity))
              (by positivity) zero_le_one
        _ = _ := by ring
    have t2 : |a * (1 / Δ - 1 / Δ')| ≤ α ^ 2 * (CΔ * S / X) := by
      rw [abs_mul, abs_of_nonneg ha0]
      calc a * |1 / Δ - 1 / Δ'| ≤ 1 * (α ^ 2 * (CΔ * S / X)) :=
            mul_le_mul ha1 hd1 (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    refine (add_le_add t1 t2).trans (le_of_eq ?_)
    field_simp

private lemma vl_dom {c : ℝ} (hc : 0 < c) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (K X S ℓ : ℝ) (F : ℝ × ℝ → ℝ), 0 ≤ K → 0 < X → 1 ≤ S →
      AEStronglyMeasurable F ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) →
      (∀ p, F p ≠ 0 → p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S) →
      (∀ p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S,
        ‖F p‖ ≤ K * Real.exp (-c * |X * (p.1 - p.2) + ℓ|)) →
      Integrable F ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ∧
      ‖∫ p, F p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))‖ ≤
        K * (S * (G / X)) := by
  obtain ⟨G, hG, hGb⟩ := vl_expint (c := c) hc
  refine ⟨G, hG, fun K X S ℓ F hK hX hS hFm hFS hFb => ?_⟩
  have hS0 : 0 < S := by linarith
  have hSq : MeasurableSet (Icc (1 / S) S ×ˢ Icc (1 / S) S) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hSsub : ∀ p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S, 0 < p.1 ∧ 0 < p.2 := by
    intro p hp
    exact ⟨lt_of_lt_of_le (by positivity) hp.1.1, lt_of_lt_of_le (by positivity) hp.2.1⟩
  set g : ℝ × ℝ → ℝ := (Icc (1 / S) S ×ˢ Icc (1 / S) S).indicator
    (fun p => K * Real.exp (-c * |X * (p.1 - p.2) + ℓ|)) with hg
  have hgc : Continuous (fun p : ℝ × ℝ => K * Real.exp (-c * |X * (p.1 - p.2) + ℓ|)) := by
    fun_prop
  have hgi : Integrable g volume :=
    (hgc.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).integrable_indicator hSq
  have hgi' : Integrable g ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hgi.mono_measure Measure.restrict_le_self
  have hdom : ∀ p, ‖F p‖ ≤ g p := by
    intro p
    by_cases h : F p = 0
    · rw [h, norm_zero]
      exact Set.indicator_nonneg (fun q _ => by positivity) p
    · have hp := hFS p h
      simp only [hg, Set.indicator_of_mem hp]
      exact hFb p hp
  refine ⟨Integrable.mono' hgi' hFm (Filter.Eventually.of_forall hdom), ?_⟩
  refine (norm_integral_le_of_norm_le hgi' (Filter.Eventually.of_forall hdom)).trans ?_
  rw [vl_mu_vol g (fun p hp => by
        simp only [hg]
        apply Set.indicator_of_notMem
        intro h; exact hp (hSsub p h)), hg, integral_indicator hSq, integral_const_mul]
  have hrel : (S - 1 / S) * (G / X) ≤ S * (G / X) := by
    have : 0 < 1 / S := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  exact mul_le_mul_of_nonneg_left
    ((hGb X S ℓ (1 / S) hX (by rw [div_le_iff₀ hS0]; nlinarith)).trans hrel) hK

set_option maxHeartbeats 1600000 in
open Muon.DetEquiv ProbabilityTheory in
private lemma vl_L2 {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (T : ℝ → ℤ → ℝ × ℝ → ℝ)
    (hT : ∀ X ℓ p, T X ℓ p =
      ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
        Real.sqrt (p.1 * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β ℓ (X * p.1) (X * p.2)))
    (S k : ℝ) (hS : 1 ≤ S) (hk : 1 ≤ k)
    (χ ω φ : ℝ × ℝ → ℝ) (hχc : Continuous χ) (hχ0 : ∀ p, 0 ≤ χ p) (hχ1 : ∀ p, χ p ≤ 1)
    (hχS : ∀ p, χ p ≠ 0 → p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S)
    (hω0 : ∀ p, 0 ≤ ω p) (hω1 : ∀ p, ω p ≤ 1) (hωm : Measurable ω)
    (hωe : ∀ p : ℝ × ℝ, 1 / (2 * k) ≤ p.2 - p.1 → ω p = 1)
    (hωp : ∀ p : ℝ × ℝ, ω p ≠ 0 → p.1 < p.2)
    (hφ : ∀ p : ℝ × ℝ, φ p = χ p * ω p *
      ((profZeta α 1 p.2 - profZeta α 1 p.1) / (p.2 - p.1) * (p.1 / p.2) ^ ((α - 1) / 2))) :
    ∀ ε > 0, ∃ X0 : ℝ, S ≤ X0 ∧ ∀ (X : ℝ) (ℓ : ℕ), X0 ≤ X → X / k ≤ (ℓ : ℝ) →
      |X * ((1 / Real.pi ^ 2) * ∫ p, χ p * T X (ℓ : ℤ) p
          ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) -
        ∫ p : ℝ × ℝ, φ p * X * DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) (ℓ : ℤ) /
          (Real.pi ^ 2 * Efun β (X * p.1) * Efun β (X * p.2))| ≤ ε := by
  have hα0 : 0 < α := by linarith
  have hS0 : 0 < S := by linarith
  have hk0 : 0 < k := by linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨C₁, c₁, hC₁, hc₁, hD⟩ := vl_D_exp hβ0 hβ1
  obtain ⟨cE, hcE, hEl⟩ := vs_E_lb hβ0 hβ1
  obtain ⟨M, c0, hM, hc0, hTb⟩ := vl_T_bound hα1 hβ0 hβ1 T hT
  obtain ⟨G0, hG0, hdom0⟩ := vl_dom (c := c0) hc0
  obtain ⟨G, hG, hdom⟩ := vl_dom (c := c₁ / 2) (by positivity)
  set K₃ : ℝ := C₁ / (Real.pi ^ 2 * cE ^ 2) with hK₃
  have hK₃0 : 0 < K₃ := by positivity
  intro ε hε
  set W : ℝ := K₃ * S * G * (5 * α) + 1 with hW
  have hW0 : 0 < W := by positivity
  set δ : ℝ := ε / (2 * W) with hδ
  have hδ0 : 0 < δ := by positivity
  set A : ℝ := 2 / (c₁ * δ) with hA
  have hA0 : 0 ≤ A := by positivity
  have hexpA : Real.exp (-(c₁ * A / 2)) ≤ δ := by
    have h1 : c₁ * A / 2 = 1 / δ := by rw [hA]; field_simp
    rw [h1]
    have := Real.add_one_le_exp (1 / δ)
    have h2 : 0 < Real.exp (1 / δ) := Real.exp_pos _
    rw [Real.exp_neg, inv_le_comm₀ h2 hδ0]
    have : 1 / δ ≤ Real.exp (1 / δ) := by linarith
    rwa [inv_eq_one_div]
  obtain ⟨Cb, X1, hCb, hX1S, hbr⟩ := vl_bracket hα1 hβ0 hβ1 S k A hS hk hA0
  refine ⟨max X1 (2 * K₃ * S * G * Cb / ε), hX1S.trans (le_max_left _ _), ?_⟩
  intro X ℓ hX hℓ
  have hXX1 : X1 ≤ X := (le_max_left _ _).trans hX
  have hXε : 2 * K₃ * S * G * Cb / ε ≤ X := (le_max_right _ _).trans hX
  have hXS : S ≤ X := hX1S.trans hXX1
  have hX0 : 0 < X := by linarith
  have hSq : ∀ p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S, 0 < p.1 ∧ 0 < p.2 := by
    intro p hp
    exact ⟨lt_of_lt_of_le (by positivity) hp.1.1, lt_of_lt_of_le (by positivity) hp.2.1⟩
  have hmeasD := vl_DE_meas hβ0 hβ1 hX0 (ℓ : ℤ)
  have hTm := vl_term_meas hα1 hβ0 hβ1 hX0 (ℓ : ℤ)
  -- the two integrands
  set f₁ : ℝ × ℝ → ℝ := fun p => X * ((1 / Real.pi ^ 2) * (χ p * T X (ℓ : ℤ) p)) with hf₁
  set Gf : ℝ × ℝ → ℝ := fun p => φ p * X * DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) (ℓ : ℤ) /
    (Real.pi ^ 2 * Efun β (X * p.1) * Efun β (X * p.2)) with hGf
  have hφ0 : ∀ p, χ p = 0 → φ p = 0 := by intro p h; rw [hφ, h]; simp
  have hshellm : Measurable (fun p : ℝ × ℝ => (profZeta α 1 p.2 - profZeta α 1 p.1) / (p.2 - p.1) *
      (p.1 / p.2) ^ ((α - 1) / 2)) := by
    unfold profZeta
    fun_prop
  have hφm : Measurable φ := by
    have : φ = fun p => χ p * ω p * ((profZeta α 1 p.2 - profZeta α 1 p.1) / (p.2 - p.1) *
      (p.1 / p.2) ^ ((α - 1) / 2)) := funext hφ
    rw [this]
    exact ((hχc.measurable.mul hωm).mul hshellm)
  have hTm' : AEStronglyMeasurable (T X (ℓ : ℤ))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    have : T X (ℓ : ℤ) = fun p : ℝ × ℝ =>
      ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
        Real.sqrt (p.1 * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) (ℓ : ℤ) *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β (ℓ : ℤ) (X * p.1) (X * p.2)) := funext (hT X (ℓ : ℤ))
    rw [this]; exact hTm
  -- integrability of f₁
  have hf₁int : Integrable f₁ ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine (hdom0 (X * (1 / Real.pi ^ 2) * M) X S ℓ f₁ (by positivity) hX0 hS ?_ ?_ ?_).1
    · exact ((hχc.aestronglyMeasurable.mul hTm').const_mul (1 / Real.pi ^ 2)).const_mul X
    · intro p hp
      by_contra hc
      apply hp
      by_cases h : χ p = 0
      · simp [hf₁, h]
      · exact absurd (hχS p h) hc
    · intro p hp
      obtain ⟨hT0, hT1⟩ := hTb X S (ℓ : ℤ) p hS hXS hp
      rw [Int.cast_natCast] at hT1
      have hχp1 := hχ1 p
      have hχp0 := hχ0 p
      simp only [hf₁]
      have e1 : χ p * T X (ℓ : ℤ) p ≤ M * Real.exp (-c0 * |X * (p.1 - p.2) + (ℓ : ℝ)|) :=
        (mul_le_mul_of_nonneg_right hχp1 hT0).trans (by rw [one_mul]; exact hT1)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc X * (1 / Real.pi ^ 2 * (χ p * T X (ℓ : ℤ) p))
          ≤ X * (1 / Real.pi ^ 2 * (M * Real.exp (-c0 * |X * (p.1 - p.2) + (ℓ : ℝ)|))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e1 (by positivity)) hX0.le
        _ = _ := by ring
  -- common positivity facts on the square
  have hpt : ∀ p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S,
      ‖f₁ p - Gf p‖ ≤ (K₃ * Cb + X * (K₃ * (5 * α) * δ)) *
        Real.exp (-(c₁ / 2) * |X * (p.1 - p.2) + (ℓ : ℝ)|) := by
    intro p hp
    obtain ⟨hr0, hs0⟩ := hSq p hp
    have hr : 1 / S ≤ p.1 := hp.1.1
    have hs : 1 / S ≤ p.2 := hp.2.1
    have hu : 0 < X * p.1 := mul_pos hX0 hr0
    have hv : 0 < X * p.2 := mul_pos hX0 hs0
    have h1u : 1 ≤ X * p.1 := by
      have : 1 ≤ S * p.1 := by
        have := mul_le_mul_of_nonneg_left hr hS0.le
        rwa [mul_one_div_cancel hS0.ne'] at this
      nlinarith
    have h1v : 1 ≤ X * p.2 := by
      have : 1 ≤ S * p.2 := by
        have := mul_le_mul_of_nonneg_left hs hS0.le
        rwa [mul_one_div_cancel hS0.ne'] at this
      nlinarith
    obtain ⟨hD0, hD1⟩ := hD (ℓ : ℤ) (X * p.1) (X * p.2) hu hv
    rw [Int.cast_natCast] at hD1
    have hE1 : cE ≤ Efun β (X * p.1) := by
      have := hEl (X * p.1) hu; rwa [min_eq_right h1u, mul_one] at this
    have hE2 : cE ≤ Efun β (X * p.2) := by
      have := hEl (X * p.2) hv; rwa [min_eq_right h1v, mul_one] at this
    have hE10 : 0 < Efun β (X * p.1) := lt_of_lt_of_le hcE hE1
    have hE20 : 0 < Efun β (X * p.2) := lt_of_lt_of_le hcE hE2
    have hΔg := vs_Delta_ge hα1 hβ0 hβ1 hu hv (ℓ : ℤ)
    have hΔ0 : 0 < profDelta α β (ℓ : ℤ) (X * p.1) (X * p.2) := lt_of_lt_of_le (by positivity) hΔg
    have hsr : 0 < Real.sqrt (p.1 * p.2) := Real.sqrt_pos.2 (mul_pos hr0 hs0)
    have hd1 : 0 < 1 + p.1 ^ α := by have := Real.rpow_pos_of_pos hr0 α; positivity
    have hd2 : 0 < 1 + p.2 ^ α := by have := Real.rpow_pos_of_pos hs0 α; positivity
    have hkey : f₁ p - Gf p = (X / Real.pi ^ 2) * χ p *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) (ℓ : ℤ) / (Efun β (X * p.1) * Efun β (X * p.2))) *
        (((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
          Real.sqrt (p.1 * p.2)) *
          ((Efun β (X * p.1) * profTheta α β (X * p.1)) *
            (Efun β (X * p.2) * profTheta α β (X * p.2))) /
              profDelta α β (ℓ : ℤ) (X * p.1) (X * p.2) -
        ω p * ((profZeta α 1 p.2 - profZeta α 1 p.1) / (p.2 - p.1) *
          (p.1 / p.2) ^ ((α - 1) / 2))) := by
      simp only [hf₁, hGf, hT, hφ]
      field_simp
    rw [hkey]
    have hY0 : 0 ≤ DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) (ℓ : ℤ) /
        (Efun β (X * p.1) * Efun β (X * p.2)) := by positivity
    have hY1 : DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) (ℓ : ℤ) /
        (Efun β (X * p.1) * Efun β (X * p.2)) ≤
        (C₁ / cE ^ 2) * Real.exp (-c₁ * |X * (p.1 - p.2) + (ℓ : ℝ)|) := by
      have hEE : cE ^ 2 ≤ Efun β (X * p.1) * Efun β (X * p.2) := by
        rw [sq]; exact mul_le_mul hE1 hE2 hcE.le hE10.le
      have hexp : Real.exp (-c₁ * |X * p.1 - X * p.2 + (ℓ : ℝ)|) =
          Real.exp (-c₁ * |X * (p.1 - p.2) + (ℓ : ℝ)|) := by congr 3; ring
      rw [hexp] at hD1
      calc _ ≤ DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) (ℓ : ℤ) / cE ^ 2 :=
            div_le_div_of_nonneg_left hD0 (by positivity) hEE
        _ ≤ (C₁ * Real.exp (-c₁ * |X * (p.1 - p.2) + (ℓ : ℝ)|)) / cE ^ 2 :=
            div_le_div_of_nonneg_right hD1 (by positivity)
        _ = _ := by ring
    have hcoef : 0 ≤ (X / Real.pi ^ 2) * χ p := by have := hχ0 p; positivity
    have hcoef1 : (X / Real.pi ^ 2) * χ p ≤ X / Real.pi ^ 2 := by
      have := hχ1 p
      have h0 : 0 ≤ X / Real.pi ^ 2 := by positivity
      nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hcoef, abs_of_nonneg hY0]
    set tt : ℝ := |X * (p.1 - p.2) + (ℓ : ℝ)| with htt
    have htt0 : 0 ≤ tt := abs_nonneg _
    obtain ⟨hbr5, hbrA⟩ := hbr X ℓ p (ω p) hXX1 hℓ hp (hω0 p) (hω1 p) (hωe p) (hωp p)
    have hexp2 : Real.exp (-c₁ * tt) ≤ Real.exp (-(c₁ / 2) * tt) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hYb : DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) (ℓ : ℤ) /
        (Efun β (X * p.1) * Efun β (X * p.2)) ≤ (C₁ / cE ^ 2) * Real.exp (-c₁ * tt) := hY1
    by_cases hA' : tt ≤ A
    · have hBr := hbrA hA'
      calc (X / Real.pi ^ 2 * χ p) * (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) (ℓ : ℤ) /
            (Efun β (X * p.1) * Efun β (X * p.2))) * _
          ≤ (X / Real.pi ^ 2) * ((C₁ / cE ^ 2) * Real.exp (-c₁ * tt)) * (Cb / X) := by
            apply mul_le_mul _ hBr (abs_nonneg _) (by positivity)
            exact mul_le_mul hcoef1 hYb hY0 (by positivity)
        _ = (K₃ * Cb) * Real.exp (-c₁ * tt) := by rw [hK₃]; field_simp
        _ ≤ (K₃ * Cb) * Real.exp (-(c₁ / 2) * tt) :=
            mul_le_mul_of_nonneg_left hexp2 (by positivity)
        _ ≤ (K₃ * Cb + X * (K₃ * (5 * α) * δ)) * Real.exp (-(c₁ / 2) * tt) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            have : 0 ≤ X * (K₃ * (5 * α) * δ) := by positivity
            linarith
    · have hAt : A < tt := not_le.1 hA'
      have hexpB : Real.exp (-c₁ * tt) ≤ δ * Real.exp (-(c₁ / 2) * tt) := by
        have : -c₁ * tt = -(c₁ * A / 2) + -(c₁ / 2) * tt + (-(c₁ / 2) * (tt - A) + -(c₁ / 2) * (A - A)) := by ring
        have h3 : Real.exp (-c₁ * tt) = Real.exp (-(c₁ / 2) * tt) * Real.exp (-(c₁ / 2) * tt) := by
          rw [← Real.exp_add]; congr 1; ring
        have h4 : Real.exp (-(c₁ / 2) * tt) ≤ Real.exp (-(c₁ * A / 2)) := by
          apply Real.exp_le_exp.mpr; nlinarith
        rw [h3, mul_comm]
        exact mul_le_mul (h4.trans hexpA) le_rfl (Real.exp_pos _).le hδ0.le
      calc (X / Real.pi ^ 2 * χ p) * (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) (ℓ : ℤ) /
            (Efun β (X * p.1) * Efun β (X * p.2))) * _
          ≤ (X / Real.pi ^ 2) * ((C₁ / cE ^ 2) * Real.exp (-c₁ * tt)) * (5 * α) := by
            apply mul_le_mul _ hbr5 (abs_nonneg _) (by positivity)
            exact mul_le_mul hcoef1 hYb hY0 (by positivity)
        _ = X * (K₃ * (5 * α)) * Real.exp (-c₁ * tt) := by rw [hK₃]; field_simp
        _ ≤ X * (K₃ * (5 * α)) * (δ * Real.exp (-(c₁ / 2) * tt)) :=
            mul_le_mul_of_nonneg_left hexpB (by positivity)
        _ = (X * (K₃ * (5 * α) * δ)) * Real.exp (-(c₁ / 2) * tt) := by ring
        _ ≤ (K₃ * Cb + X * (K₃ * (5 * α) * δ)) * Real.exp (-(c₁ / 2) * tt) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            have : 0 ≤ K₃ * Cb := by positivity
            linarith
  -- measurability of Gf and integrability of the difference
  have hGm : AEStronglyMeasurable Gf
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    have : AEMeasurable Gf ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
      ((hφm.aemeasurable.mul_const X).mul hmeasD.1).div
        ((aemeasurable_const.mul hmeasD.2.1).mul hmeasD.2.2)
    exact this.aestronglyMeasurable
  have hdiffm : AEStronglyMeasurable (fun p => f₁ p - Gf p)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
    hf₁int.aestronglyMeasurable.sub hGm
  have hzero : ∀ p : ℝ × ℝ, (fun p => f₁ p - Gf p) p ≠ 0 → p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S := by
    intro p hp
    by_contra hc
    apply hp
    have hχ : χ p = 0 := by
      by_contra h; exact hc (hχS p h)
    simp [hf₁, hGf, hχ, hφ0 p hχ]
  have hKnn : 0 ≤ K₃ * Cb + X * (K₃ * (5 * α) * δ) := by positivity
  obtain ⟨hdint, hdnorm⟩ := hdom (K₃ * Cb + X * (K₃ * (5 * α) * δ)) X S ((ℓ : ℝ))
    (fun p => f₁ p - Gf p) hKnn hX0 hS hdiffm hzero (fun p hp => hpt p hp)
  have hGint : Integrable Gf ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    have := hf₁int.sub hdint
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp
  have hGzero : ∀ p : ℝ × ℝ, ¬ (0 < p.1 ∧ 0 < p.2) → Gf p = 0 := by
    intro p hp
    have hχ : χ p = 0 := by
      by_contra h
      exact hp (hSq p (hχS p h))
    simp [hGf, hφ0 p hχ]
  have h1 : X * ((1 / Real.pi ^ 2) * ∫ p, χ p * T X (ℓ : ℤ) p
      ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) =
      ∫ p, f₁ p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    simp only [hf₁]
    rw [integral_const_mul, integral_const_mul]
  have h2 : ∫ p : ℝ × ℝ, φ p * X * DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) (ℓ : ℤ) /
          (Real.pi ^ 2 * Efun β (X * p.1) * Efun β (X * p.2)) =
      ∫ p, Gf p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
    (vl_mu_vol Gf hGzero).symm
  rw [h1, h2, ← integral_sub hf₁int hGint, ← Real.norm_eq_abs]
  refine hdnorm.trans ?_
  have hXS' : 0 ≤ K₃ * S * G := by positivity
  have e1 : (K₃ * Cb) * (S * (G / X)) ≤ ε / 2 := by
    have : K₃ * S * G * Cb / X ≤ ε / 2 := by
      rw [div_le_iff₀ hX0]
      have := (div_le_iff₀ hε).1 hXε
      nlinarith
    calc _ = K₃ * S * G * Cb / X := by ring
      _ ≤ _ := this
  have e2 : X * (K₃ * (5 * α) * δ) * (S * (G / X)) ≤ ε / 2 := by
    have : X * (K₃ * (5 * α) * δ) * (S * (G / X)) = (K₃ * S * G * (5 * α)) * δ := by
      field_simp
    rw [this]
    have hδW : W * δ = ε / 2 := by rw [hδ]; field_simp
    have : K₃ * S * G * (5 * α) ≤ W := by rw [hW]; linarith
    calc _ ≤ W * δ := mul_le_mul_of_nonneg_right this hδ0.le
      _ = _ := hδW
  calc _ = (K₃ * Cb) * (S * (G / X)) + X * (K₃ * (5 * α) * δ) * (S * (G / X)) := by ring
    _ ≤ ε / 2 + ε / 2 := add_le_add e1 e2
    _ = ε := by ring

private lemma vl_unif (Xn : ℕ → ℝ) (K : Set ℝ) (hK : IsCompact K) (cn : ℕ → ℤ → ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c K)
    (hseq : ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ (ℓ : ℕ → ℤ) (τ : ℝ), τ ∈ K →
      Tendsto (fun k => (ℓ k : ℝ) / Xn (ψ k)) atTop (𝓝 τ) →
        Tendsto (fun k => cn (ψ k) (ℓ k)) atTop (𝓝 (c τ))) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ ℓ : ℤ, (ℓ : ℝ) / Xn n ∈ K → |cn n ℓ - c ((ℓ : ℝ) / Xn n)| ≤ ε := by
  intro ε hε
  by_contra hcon
  have hfreq : ∃ᶠ n in atTop, ∃ ℓ : ℤ, (ℓ : ℝ) / Xn n ∈ K ∧ ε < |cn n ℓ - c ((ℓ : ℝ) / Xn n)| := by
    rw [Filter.not_eventually] at hcon
    refine hcon.mono (fun n hn => ?_)
    simp only [not_forall, not_le, exists_prop] at hn
    obtain ⟨ℓ, h1, h2⟩ := hn
    exact ⟨ℓ, h1, h2⟩
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose ℓ hℓK hℓε using hφP
  have hτK : ∀ k, (ℓ k : ℝ) / Xn (φ k) ∈ K := hℓK
  obtain ⟨a, haK, φ', hφ', hlim⟩ := hK.tendsto_subseq hτK
  have hψ : StrictMono (φ ∘ φ') := hφ.comp hφ'
  have h1 := hseq (φ ∘ φ') hψ (ℓ ∘ φ') a haK hlim
  have h2 : Tendsto (fun k => c ((ℓ (φ' k) : ℝ) / Xn (φ (φ' k)))) atTop (𝓝 (c a)) := by
    have := (hc a haK).tendsto
    exact this.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Filter.Eventually.of_forall (fun k => hτK (φ' k))⟩)
  have h3 : Tendsto (fun k => |cn (φ (φ' k)) (ℓ (φ' k)) - c ((ℓ (φ' k) : ℝ) / Xn (φ (φ' k)))|)
      atTop (𝓝 0) := by
    have := (h1.sub h2)
    rw [sub_self] at this
    simpa using this.abs
  have h4 : ε ≤ 0 := ge_of_tendsto h3 (Filter.Eventually.of_forall (fun k => (hℓε (φ' k)).le))
  linarith

private lemma vl_cont_param {φ : ℝ × ℝ → ℝ} (hφ : Continuous φ) {a b : ℝ}
    (hs : ∀ p, φ p ≠ 0 → p.1 ∈ Icc a b) :
    Continuous (fun τ : ℝ => ∫ r : ℝ, φ (r, r + τ)) := by
  have h1 : ∀ τ : ℝ, (∫ r : ℝ, φ (r, r + τ)) = ∫ r in Icc a b, φ (r, r + τ) := by
    intro τ
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    by_contra h
    exact hr (hs _ h)
  simp_rw [h1]
  exact continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun (τ : ℝ) (r : ℝ) => φ (r, r + τ)) (by fun_prop) isCompact_Icc

private lemma vl_cont_mul {f g : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hf : Continuous f) (hg : ContinuousOn g U) (hsupp : tsupport f ⊆ U) :
    Continuous (fun p => f p * g p) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ U
  · exact hf.continuousAt.mul (hg.continuousAt (hU.mem_nhds hp))
  · have hp' : p ∉ tsupport f := fun h => hp (hsupp h)
    have hnhds : (tsupport f)ᶜ ∈ 𝓝 p := (isClosed_tsupport f).isOpen_compl.mem_nhds hp'
    have : (fun q => f q * g q) =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
      filter_upwards [hnhds] with q hq
      rw [image_eq_zero_of_notMem_tsupport hq, zero_mul]
    exact continuousAt_const.congr this.symm

private lemma vl_psi (j : ℝ) (hj : 1 ≤ j) :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ (∀ r, 0 ≤ ψ r) ∧ (∀ r, ψ r ≤ 1) ∧
      (∀ r ∈ Icc (1 / j) j, ψ r = 1) ∧ (∀ r, ψ r ≠ 0 → r ∈ Icc (1 / (2 * j)) (2 * j)) := by
  have hj0 : 0 < j := by linarith
  refine ⟨fun r => max 0 (min 1 (min (2 * j * r - 1) ((2 * j - r) / j))), by fun_prop,
    fun r => le_max_left _ _, fun r => max_le zero_le_one (min_le_left _ _), ?_, ?_⟩
  · intro r hr
    have h1 : 1 ≤ 2 * j * r - 1 := by
      have := mul_le_mul_of_nonneg_left hr.1 hj0.le
      rw [mul_one_div_cancel hj0.ne'] at this
      nlinarith
    have h2 : 1 ≤ (2 * j - r) / j := by
      rw [le_div_iff₀ hj0]; nlinarith [hr.2]
    show max 0 (min 1 (min (2 * j * r - 1) ((2 * j - r) / j))) = 1
    rw [min_eq_left (le_min h1 h2), max_eq_right zero_le_one]
  · intro r hr
    by_contra hc
    have hc' : r < 1 / (2 * j) ∨ 2 * j < r := by
      by_contra h
      push Not at h
      exact hc ⟨h.1, h.2⟩
    apply hr
    rcases hc' with h | h
    · have : 2 * j * r - 1 < 0 := by
        have := mul_lt_mul_of_pos_left h (by positivity : 0 < 2 * j)
        rw [mul_one_div_cancel (by positivity)] at this
        linarith
      have : min 1 (min (2 * j * r - 1) ((2 * j - r) / j)) ≤ 2 * j * r - 1 :=
        (min_le_right _ _).trans (min_le_left _ _)
      exact max_eq_left (by linarith)
    · have : (2 * j - r) / j < 0 := by
        rw [div_neg_iff]; right; exact ⟨by linarith, hj0⟩
      have : min 1 (min (2 * j * r - 1) ((2 * j - r) / j)) ≤ (2 * j - r) / j :=
        (min_le_right _ _).trans (min_le_right _ _)
      exact max_eq_left (by linarith)

private lemma vl_shell_cont {α : ℝ} (hα1 : 1 < α) :
    ContinuousOn (fun p : ℝ × ℝ => (profZeta α 1 p.2 - profZeta α 1 p.1) / (p.2 - p.1) *
      (p.1 / p.2) ^ ((α - 1) / 2)) {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
  have hα0 : 0 < α := by linarith
  have hz : ∀ f : ℝ × ℝ → ℝ, Continuous f → (∀ p ∈ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2}, 0 < f p) →
      ContinuousOn (fun p => profZeta α 1 (f p)) {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
    intro f hf hpos
    unfold profZeta
    simp only [Real.one_rpow]
    have hp : Continuous (fun p => (f p) ^ α) := hf.rpow_const (fun _ => Or.inr hα0.le)
    refine hp.continuousOn.div (continuousOn_const.add hp.continuousOn) ?_
    intro p hp'
    have := Real.rpow_pos_of_pos (hpos p hp') α
    positivity
  have h1 := hz (fun p => p.2) continuous_snd (fun p hp => hp.1.trans hp.2)
  have h2 := hz (fun p => p.1) continuous_fst (fun p hp => hp.1)
  refine ((h1.sub h2).div (continuousOn_snd.sub continuousOn_fst) ?_).mul ?_
  · intro p hp; exact (sub_pos.2 hp.2).ne'
  · refine ContinuousOn.rpow_const (continuousOn_fst.div continuousOn_snd ?_) ?_
    · intro p hp; exact (hp.1.trans hp.2).ne'
    · intro p hp; right; linarith

private lemma vl_setup {α : ℝ} (hα1 : 1 < α) (j k : ℝ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    ∃ χ ω φ : ℝ × ℝ → ℝ, Continuous χ ∧ (∀ p, 0 ≤ χ p) ∧ (∀ p, χ p ≤ 1) ∧
      (∀ p : ℝ × ℝ, χ p.swap = χ p) ∧
      (∀ p ∈ Icc (1 / j) j ×ˢ Icc (1 / j) j, χ p = 1) ∧
      (∀ p, χ p ≠ 0 → p ∈ Icc (1 / (2 * j)) (2 * j) ×ˢ Icc (1 / (2 * j)) (2 * j)) ∧
      (∀ p, 0 ≤ ω p) ∧ (∀ p, ω p ≤ 1) ∧ Measurable ω ∧
      (∀ p : ℝ × ℝ, 1 / (2 * k) ≤ p.2 - p.1 → ω p = 1) ∧ (∀ p : ℝ × ℝ, ω p ≠ 0 → p.1 < p.2) ∧
      (∀ p : ℝ × ℝ, φ p = χ p * ω p *
        ((profZeta α 1 p.2 - profZeta α 1 p.1) / (p.2 - p.1) * (p.1 / p.2) ^ ((α - 1) / 2))) ∧
      Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0 := by
  have hj0 : 0 < j := by linarith
  have hk0 : 0 < k := by linarith
  obtain ⟨ψ, hψc, hψ0, hψ1, hψone, hψS⟩ := vl_psi j hj
  set χ : ℝ × ℝ → ℝ := fun p => ψ p.1 * ψ p.2 with hχ
  set ω : ℝ × ℝ → ℝ := fun p => max 0 (min 1 (4 * k * (p.2 - p.1) - 1)) with hω
  have hχc : Continuous χ := by fun_prop
  have hωc : Continuous ω := by fun_prop
  have hω0 : ∀ p, 0 ≤ ω p := fun p => le_max_left _ _
  have hω1 : ∀ p, ω p ≤ 1 := fun p => max_le zero_le_one (min_le_left _ _)
  have hωp : ∀ p : ℝ × ℝ, ω p ≠ 0 → p.1 < p.2 := by
    intro p hp
    by_contra h
    apply hp
    have : 4 * k * (p.2 - p.1) - 1 < 0 := by nlinarith
    have : min 1 (4 * k * (p.2 - p.1) - 1) ≤ 4 * k * (p.2 - p.1) - 1 := min_le_right _ _
    exact max_eq_left (by linarith)
  have hωgap : ∀ p : ℝ × ℝ, ω p ≠ 0 → 1 / (4 * k) ≤ p.2 - p.1 := by
    intro p hp
    by_contra h
    apply hp
    push Not at h
    have h' : p.2 - p.1 < 1 / (4 * k) := h
    have : 4 * k * (p.2 - p.1) - 1 < 0 := by
      have := mul_lt_mul_of_pos_left h' (by positivity : 0 < 4 * k)
      rw [mul_one_div_cancel (by positivity)] at this
      linarith
    have : min 1 (4 * k * (p.2 - p.1) - 1) ≤ 4 * k * (p.2 - p.1) - 1 := min_le_right _ _
    exact max_eq_left (by linarith)
  have hωe : ∀ p : ℝ × ℝ, 1 / (2 * k) ≤ p.2 - p.1 → ω p = 1 := by
    intro p hp
    have h1 : 1 ≤ 4 * k * (p.2 - p.1) - 1 := by
      have := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 4 * k)
      have e : 4 * k * (1 / (2 * k)) = 2 := by field_simp; ring
      rw [e] at this
      linarith
    show max 0 (min 1 (4 * k * (p.2 - p.1) - 1)) = 1
    rw [min_eq_left h1, max_eq_right zero_le_one]
  set sh : ℝ × ℝ → ℝ := fun p => (profZeta α 1 p.2 - profZeta α 1 p.1) / (p.2 - p.1) *
    (p.1 / p.2) ^ ((α - 1) / 2) with hsh
  set φ : ℝ × ℝ → ℝ := fun p => χ p * ω p * sh p with hφ
  -- the support set
  set K0 : Set (ℝ × ℝ) := (Icc (1 / (2 * j)) (2 * j) ×ˢ Icc (1 / (2 * j)) (2 * j)) ∩
    {p : ℝ × ℝ | 1 / (4 * k) ≤ p.2 - p.1} with hK0
  have hK0c : IsCompact K0 := by
    refine (isCompact_Icc.prod isCompact_Icc).inter_right ?_
    exact isClosed_le continuous_const (continuous_snd.sub continuous_fst)
  have hK0U : K0 ⊆ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
    intro p hp
    refine ⟨lt_of_lt_of_le (by positivity) hp.1.1.1, ?_⟩
    have : 0 < 1 / (4 * k) := by positivity
    have h2 : 1 / (4 * k) ≤ p.2 - p.1 := hp.2
    linarith
  have hfne : ∀ p, χ p * ω p ≠ 0 → p ∈ K0 := by
    intro p hp
    have hχp : χ p ≠ 0 := left_ne_zero_of_mul hp
    have hωp' : ω p ≠ 0 := right_ne_zero_of_mul hp
    refine ⟨?_, hωgap p hωp'⟩
    have h1 := hψS _ (left_ne_zero_of_mul hχp)
    have h2 := hψS _ (right_ne_zero_of_mul hχp)
    exact ⟨h1, h2⟩
  have hts : tsupport (fun p => χ p * ω p) ⊆ K0 := by
    apply closure_minimal
    · intro p hp; exact hfne p hp
    · exact hK0c.isClosed
  have hφne : ∀ p, φ p ≠ 0 → p ∈ K0 := by
    intro p hp
    apply hfne
    intro h
    apply hp
    simp only [hφ, h, zero_mul]
  refine ⟨χ, ω, φ, hχc, fun p => mul_nonneg (hψ0 _) (hψ0 _),
    fun p => mul_le_one₀ (hψ1 _) (hψ0 _) (hψ1 _), fun p => by simp [hχ, mul_comm],
    fun p hp => by simp only [hχ, hψone _ hp.1, hψone _ hp.2, one_mul],
    fun p hp => ⟨hψS _ (left_ne_zero_of_mul hp), hψS _ (right_ne_zero_of_mul hp)⟩,
    hω0, hω1, hωc.measurable, hωe, hωp, fun p => rfl, ?_, ?_, ?_⟩
  · exact vl_cont_mul (U := {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2})
      ((isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_snd))
      (hχc.mul hωc) (vl_shell_cont hα1) (hts.trans hK0U)
  · apply HasCompactSupport.intro hK0c
    intro p hp
    by_contra h
    exact hp (hφne p h)
  · have : tsupport φ ⊆ K0 := by
      apply closure_minimal
      · intro p hp; exact hφne p hp
      · exact hK0c.isClosed
    intro p hp
    have := hK0U (this hp)
    exact ⟨this.1, this.1.trans this.2⟩

private lemma vl_J_lim {α : ℝ} (hα1 : 1 < α) (χ : ℕ → ℝ × ℝ → ℝ) (hm : ∀ n, Measurable (χ n))
    (h0 : ∀ n p, 0 ≤ χ n p) (h1 : ∀ n p, χ n p ≤ 1)
    (hone : ∀ p : ℝ × ℝ, 0 < p.1 → 0 < p.2 → ∀ᶠ n in atTop, χ n p = 1)
    (kk : ℕ → ℝ) (hkk : Tendsto kk atTop atTop) (hk0 : ∀ n, 0 < kk n) :
    Tendsto (fun n => ∫ τ in Ioi (1 / kk n), ∫ r in Ioi (0:ℝ), χ n (r, r + τ) *
      ((profZeta α 1 (r + τ) - profZeta α 1 r) / τ * (r / (r + τ)) ^ ((α - 1) / 2)))
      atTop (𝓝 (∫ τ in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ),
        (profZeta α 1 (r + τ) - profZeta α 1 r) / τ * (r / (r + τ)) ^ ((α - 1) / 2))) := by
  have hα0 : 0 < α := by linarith
  set Sh : ℝ → ℝ → ℝ := fun r τ => (profZeta α 1 (r + τ) - profZeta α 1 r) / τ *
    (r / (r + τ)) ^ ((α - 1) / 2) with hSh
  have hShm : Measurable (Function.uncurry fun τ r => Sh r τ) := by
    unfold Sh profZeta
    fun_prop
  have hint_k := (vi_shell_k_int hα1).const_mul α
  -- inner integral facts
  have hgen : ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ p, 0 ≤ g p) → (∀ p, g p ≤ 1) →
      ∀ τ : ℝ, 0 < τ →
      Integrable (fun r => g (r, r + τ) * Sh r τ) (volume.restrict (Ioi (0:ℝ))) := by
    intro g hg hg0 hg1 τ hτ
    refine Integrable.mono' hint_k ?_ ?_
    · have : Measurable (fun r : ℝ => g (r, r + τ) * Sh r τ) := by
        have h := hg.comp (by fun_prop : Measurable fun r : ℝ => (r, r + τ))
        have h2 : Measurable (fun r : ℝ => Sh r τ) := by
          unfold Sh profZeta
          fun_prop
        exact h.mul h2
      exact this.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hb := vi_shell_point_bound hα1 hr hτ
      have e : Sh r τ = (profZeta α 1 (r + τ) - profZeta α 1 r) / τ * (r / (r + τ)) ^ ((α - 1) / 2) := rfl
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 _) (e ▸ hb.1))]
      calc g (r, r + τ) * Sh r τ ≤ 1 * Sh r τ :=
            mul_le_mul_of_nonneg_right (hg1 _) (e ▸ hb.1)
        _ ≤ _ := by rw [one_mul, e]; exact hb.2
  have hSh0 : ∀ r τ : ℝ, 0 < r → 0 < τ → 0 ≤ Sh r τ := fun r τ hr hτ =>
    (vi_shell_point_bound hα1 hr hτ).1
  set Φ : ℝ → ℝ := fun τ => ∫ r in Ioi (0:ℝ), Sh r τ with hΦ
  set Gn : ℕ → ℝ → ℝ := fun n τ => ∫ r in Ioi (0:ℝ), χ n (r, r + τ) * Sh r τ with hGn
  have hΦint : IntegrableOn Φ (Ioi (0:ℝ)) := vi_shell_profile_int hα1
  have hGn_le : ∀ n τ, 0 < τ → 0 ≤ Gn n τ ∧ Gn n τ ≤ Φ τ := by
    intro n τ hτ
    have hi1 := hgen (χ n) (hm n) (h0 n) (h1 n) τ hτ
    have hi2 := hgen (fun _ => 1) measurable_const (fun _ => zero_le_one) (fun _ => le_rfl) τ hτ
    simp only [one_mul] at hi2
    refine ⟨setIntegral_nonneg measurableSet_Ioi (fun r hr => mul_nonneg (h0 n _) (hSh0 r τ hr hτ)), ?_⟩
    refine setIntegral_mono_on hi1 hi2 measurableSet_Ioi (fun r hr => ?_)
    calc χ n (r, r + τ) * Sh r τ ≤ 1 * Sh r τ :=
          mul_le_mul_of_nonneg_right (h1 n _) (hSh0 r τ hr hτ)
      _ = Sh r τ := one_mul _
  have hGn_lim : ∀ τ : ℝ, 0 < τ → Tendsto (fun n => Gn n τ) atTop (𝓝 (Φ τ)) := by
    intro τ hτ
    refine tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioi (0:ℝ)))
      (bound := fun r : ℝ => α * (r ^ (α / 2) / (1 + r ^ α) / Real.sqrt r)) ?_ hint_k ?_ ?_
    · intro n
      exact (hgen (χ n) (hm n) (h0 n) (h1 n) τ hτ).aestronglyMeasurable
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hb := vi_shell_point_bound hα1 hr hτ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 n _) (hSh0 r τ hr hτ))]
      calc χ n (r, r + τ) * Sh r τ ≤ 1 * Sh r τ :=
            mul_le_mul_of_nonneg_right (h1 n _) (hSh0 r τ hr hτ)
        _ ≤ _ := by rw [one_mul]; exact hb.2
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hev := hone (r, r + τ) hr (by simp only; linarith [show (0:ℝ) < r from hr])
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      rw [hn, one_mul]
  have hFm : ∀ n, AEStronglyMeasurable ((Ioi (1 / kk n)).indicator (Gn n))
      (volume.restrict (Ioi (0:ℝ))) := by
    intro n
    refine AEStronglyMeasurable.indicator ?_ measurableSet_Ioi
    have hsm : StronglyMeasurable (fun z : ℝ × ℝ => χ n (z.2, z.2 + z.1) * Sh z.2 z.1) := by
      have : Measurable (fun z : ℝ × ℝ => χ n (z.2, z.2 + z.1) * Sh z.2 z.1) := by
        have h := (hm n).comp (by fun_prop : Measurable fun z : ℝ × ℝ => (z.2, z.2 + z.1))
        exact h.mul (by unfold Sh profZeta; fun_prop)
      exact this.stronglyMeasurable
    exact (hsm.integral_prod_right' (ν := volume.restrict (Ioi (0:ℝ)))).aestronglyMeasurable
  have hconv : ∀ n, (∫ τ in Ioi (1 / kk n), Gn n τ) =
      ∫ τ in Ioi (0:ℝ), (Ioi (1 / kk n)).indicator (Gn n) τ := by
    intro n
    rw [setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.2 (Ioi_subset_Ioi (by have := hk0 n; positivity))]
  have hmain : Tendsto (fun n => ∫ τ in Ioi (0:ℝ), (Ioi (1 / kk n)).indicator (Gn n) τ) atTop
      (𝓝 (∫ τ in Ioi (0:ℝ), Φ τ)) := by
    refine tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioi (0:ℝ)))
      (bound := Φ) hFm hΦint ?_ ?_
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
      by_cases hmem : τ ∈ Ioi (1 / kk n)
      · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_of_nonneg (hGn_le n τ hτ).1]
        exact (hGn_le n τ hτ).2
      · rw [Set.indicator_of_notMem hmem, norm_zero]
        exact (hGn_le 0 τ hτ).1.trans (hGn_le 0 τ hτ).2
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
      have hev : ∀ᶠ n in atTop, 1 / kk n < τ := by
        have h1' : Tendsto (fun n => 1 / kk n) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop hkk
        exact h1'.eventually (Iio_mem_nhds hτ)
      refine (hGn_lim τ hτ).congr' ?_
      filter_upwards [hev] with n hn
      rw [Set.indicator_of_mem (show τ ∈ Ioi (1 / kk n) from hn)]
  have := hmain
  simp only [← hconv] at this
  exact this

private lemma vl_C_form {α : ℝ} (j k : ℝ) (hj : 1 ≤ j) (hk : 1 ≤ k)
    (χ ω φ : ℝ × ℝ → ℝ)
    (hχS : ∀ p, χ p ≠ 0 → p ∈ Icc (1 / (2 * j)) (2 * j) ×ˢ Icc (1 / (2 * j)) (2 * j))
    (hωe : ∀ p : ℝ × ℝ, 1 / (2 * k) ≤ p.2 - p.1 → ω p = 1)
    (hφ : ∀ p : ℝ × ℝ, φ p = χ p * ω p *
      ((profZeta α 1 p.2 - profZeta α 1 p.1) / (p.2 - p.1) * (p.1 / p.2) ^ ((α - 1) / 2))) :
    (∀ τ : ℝ, 1 / (2 * k) ≤ τ → ∫ r : ℝ, φ (r, r + τ) =
      ∫ r in Ioi (0:ℝ), χ (r, r + τ) *
        ((profZeta α 1 (r + τ) - profZeta α 1 r) / τ * (r / (r + τ)) ^ ((α - 1) / 2))) ∧
    (∀ τ : ℝ, 2 * j ≤ τ → ∫ r : ℝ, φ (r, r + τ) = 0) := by
  have hj0 : 0 < j := by linarith
  have hk0 : 0 < k := by linarith
  constructor
  · intro τ hτ
    have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ
    have h1 : (∫ r : ℝ, φ (r, r + τ)) = ∫ r in Ioi (0:ℝ), φ (r, r + τ) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro r hr
      by_contra h
      have hφne : χ (r, r + τ) ≠ 0 := by
        intro h0; apply h; rw [hφ, h0]; simp
      have := (hχS _ hφne).1.1
      have h2 : (0:ℝ) < 1 / (2 * j) := by positivity
      exact hr (lt_of_lt_of_le h2 this)
    rw [h1]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    have hω := hωe (r, r + τ) (by simpa using hτ)
    simp only [hφ, hω, mul_one]
    congr 2
    ring_nf
  · intro τ hτ
    have : ∀ r : ℝ, φ (r, r + τ) = 0 := by
      intro r
      by_cases h : χ (r, r + τ) = 0
      · rw [hφ, h]; simp
      · exfalso
        have hp := hχS _ h
        have h1 : 1 / (2 * j) ≤ r := hp.1.1
        have h2 : r + τ ≤ 2 * j := hp.2.2
        have : (0:ℝ) < 1 / (2 * j) := by positivity
        linarith
    simp [this]

private lemma vl_C_interval {α : ℝ} (j k U : ℝ) (hj : 1 ≤ j) (hk : 1 ≤ k) (hU : 2 * j ≤ U)
    (hkU : 1 / k ≤ U)
    (χ ω φ : ℝ × ℝ → ℝ)
    (hχS : ∀ p, χ p ≠ 0 → p ∈ Icc (1 / (2 * j)) (2 * j) ×ˢ Icc (1 / (2 * j)) (2 * j))
    (hωe : ∀ p : ℝ × ℝ, 1 / (2 * k) ≤ p.2 - p.1 → ω p = 1)
    (hφ : ∀ p : ℝ × ℝ, φ p = χ p * ω p *
      ((profZeta α 1 p.2 - profZeta α 1 p.1) / (p.2 - p.1) * (p.1 / p.2) ^ ((α - 1) / 2))) :
    (∫ τ in (1 / k)..U, ∫ r : ℝ, φ (r, r + τ)) =
      ∫ τ in Ioi (1 / k), ∫ r in Ioi (0:ℝ), χ (r, r + τ) *
        ((profZeta α 1 (r + τ) - profZeta α 1 r) / τ * (r / (r + τ)) ^ ((α - 1) / 2)) := by
  have hj0 : 0 < j := by linarith
  have hk0 : 0 < k := by linarith
  obtain ⟨hform, hzero⟩ := vl_C_form (α := α) j k hj hk χ ω φ hχS hωe hφ
  have hge : ∀ τ ∈ Ioi (1 / k), 1 / (2 * k) ≤ τ := by
    intro τ hτ
    have : 1 / (2 * k) ≤ 1 / k := by
      rw [div_le_div_iff₀ (by positivity) hk0]; linarith
    exact this.trans (le_of_lt hτ)
  rw [intervalIntegral.integral_of_le hkU]
  have h1 : (∫ τ in Ioc (1 / k) U, ∫ r : ℝ, φ (r, r + τ)) =
      ∫ τ in Ioi (1 / k), ∫ r : ℝ, φ (r, r + τ) := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Ioc_subset_Ioi_self
    intro τ hτ
    have hτU : U < τ := by
      by_contra h
      exact hτ.2 ⟨hτ.1, not_lt.1 h⟩
    exact hzero τ (by linarith)
  rw [h1]
  exact setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => hform τ (hge τ hτ))

set_option maxHeartbeats 1600000 in
open Muon.DetEquiv ProbabilityTheory in
private lemma vl_window {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (T : ℝ → ℤ → ℝ × ℝ → ℝ)
    (hT : ∀ X ℓ p, T X ℓ p =
      ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
        Real.sqrt (p.1 * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β ℓ (X * p.1) (X * p.2)))
    (j k : ℝ) (hj : 1 ≤ j) (hk : 1 ≤ k)
    (χ ω φ : ℝ × ℝ → ℝ) (hχc : Continuous χ) (hχ0 : ∀ p, 0 ≤ χ p) (hχ1 : ∀ p, χ p ≤ 1)
    (hχS : ∀ p, χ p ≠ 0 → p ∈ Icc (1 / (2 * j)) (2 * j) ×ˢ Icc (1 / (2 * j)) (2 * j))
    (hω0 : ∀ p, 0 ≤ ω p) (hω1 : ∀ p, ω p ≤ 1) (hωm : Measurable ω)
    (hωe : ∀ p : ℝ × ℝ, 1 / (2 * k) ≤ p.2 - p.1 → ω p = 1)
    (hωp : ∀ p : ℝ × ℝ, ω p ≠ 0 → p.1 < p.2)
    (hφ : ∀ p : ℝ × ℝ, φ p = χ p * ω p *
      ((profZeta α 1 p.2 - profZeta α 1 p.1) / (p.2 - p.1) * (p.1 / p.2) ^ ((α - 1) / 2)))
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφt : tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0)
    (Xn : ℕ → ℝ) (hXpos : ∀ m, 0 < Xn m) (hXn : Tendsto Xn atTop atTop) :
    Tendsto (fun m => ∑ ℓ ∈ Finset.Icc ⌈(1 / (k * (8 * j))) * ((8 * j) * Xn m)⌉
        ⌊(1 - 1 / (k * (8 * j))) * ((8 * j) * Xn m)⌋,
        (1 / Real.pi ^ 2) * ∫ p, χ p * T (Xn m) ℓ p
          ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))))
      atTop (𝓝 (∫ τ in Ioi (1 / k), ∫ r in Ioi (0:ℝ), χ (r, r + τ) *
        ((profZeta α 1 (r + τ) - profZeta α 1 r) / τ * (r / (r + τ)) ^ ((α - 1) / 2)))) := by
  have hj0 : 0 < j := by linarith
  have hk0 : 0 < k := by linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  set M : ℝ := 8 * j with hM
  have hM0 : 0 < M := by positivity
  set γ : ℕ → ℝ := fun m => M * Xn m with hγ
  have hγT : Tendsto γ atTop atTop := hXn.const_mul_atTop hM0
  set η₁ : ℝ := 1 / (k * M) with hη₁
  have hη0 : 0 < η₁ := by positivity
  have hη1 : η₁ < 1 / 2 := by
    rw [hη₁, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set cn : ℕ → ℤ → ℝ := fun m ℓ => γ m * ((1 / Real.pi ^ 2) * ∫ p, χ p * T (Xn m) ℓ p
    ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) with hcn
  set Cfun : ℝ → ℝ := fun τ => ∫ r : ℝ, φ (r, r + τ) with hCfun
  set c : ℝ → ℝ := fun t => M * Cfun (M * t) with hc
  have hCc : Continuous Cfun :=
    vl_cont_param hφc (a := 1 / (2 * j)) (b := 2 * j) (fun p hp => by
      have hχp : χ p ≠ 0 := by
        intro h0; apply hp; rw [hφ, h0]; simp
      exact (hχS p hχp).1)
  have hcc : ContinuousOn c (Icc η₁ (1 - η₁)) := by
    have : Continuous c := continuous_const.mul (hCc.comp (continuous_const.mul continuous_id))
    exact this.continuousOn
  -- uniform localization
  set K : Set ℝ := Icc (1 / k) (M * (1 - η₁)) with hK
  have hKc : IsCompact K := isCompact_Icc
  have hKpos : ∀ τ ∈ K, 0 < τ := fun τ hτ => lt_of_lt_of_le (by positivity) hτ.1
  set cn' : ℕ → ℤ → ℝ := fun m ℓ => ∫ p : ℝ × ℝ, φ p * Xn m *
    DLag β (Qm β (Xn m * p.1)) (Qm β (Xn m * p.2)) ℓ /
      (Real.pi ^ 2 * Efun β (Xn m * p.1) * Efun β (Xn m * p.2)) with hcn'
  have hloc : ∀ ε > 0, ∀ᶠ m in atTop, ∀ ℓ : ℤ, (ℓ : ℝ) / Xn m ∈ K →
      |cn' m ℓ - Cfun ((ℓ : ℝ) / Xn m)| ≤ ε := by
    refine vl_unif Xn K hKc cn' Cfun hCc.continuousOn ?_
    intro ψ hψ ℓ τ hτ hℓτ
    exact vi_localization_scaled hβ0 hβ1 (fun n => Xn (ψ n)) ℓ (fun n => hXpos _)
      (hXn.comp hψ.tendsto_atTop) (hKpos τ hτ) hℓτ φ hφc hφs hφt
  have hunif : ∀ ε > 0, ∀ᶠ m in atTop, ∀ ℓ : ℤ, (ℓ : ℝ) / γ m ∈ Icc η₁ (1 - η₁) →
      |cn m ℓ - c ((ℓ : ℝ) / γ m)| ≤ ε := by
    intro ε hε
    have hε' : 0 < ε / (2 * M) := by positivity
    obtain ⟨X0, hX0S, hL2⟩ := vl_L2 hα1 hβ0 hβ1 T hT (2 * j) k (by linarith) hk χ ω φ hχc hχ0 hχ1
      hχS hω0 hω1 hωm hωe hωp hφ _ hε'
    filter_upwards [hloc _ hε', hXn.eventually_ge_atTop X0] with m hm1 hm2 ℓ hℓ
    have hX0 : 0 < Xn m := hXpos m
    have hγm : γ m = M * Xn m := rfl
    have hγpos : 0 < γ m := by rw [hγm]; positivity
    have hℓ1 : η₁ * γ m ≤ (ℓ : ℝ) := by
      have := hℓ.1
      rwa [le_div_iff₀ hγpos] at this
    have hℓ2 : (ℓ : ℝ) ≤ (1 - η₁) * γ m := by
      have := hℓ.2
      rwa [div_le_iff₀ hγpos] at this
    have hηγ : η₁ * γ m = Xn m / k := by
      rw [hη₁, hγm]; field_simp
    have hℓ0 : 0 ≤ ℓ := by
      have : (0:ℝ) ≤ (ℓ : ℝ) := by
        have : 0 ≤ η₁ * γ m := by positivity
        linarith
      exact_mod_cast this
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hℓ0
    have hℓn : Xn m / k ≤ (n : ℝ) := by
      have : ((n : ℤ) : ℝ) = (n : ℝ) := Int.cast_natCast n
      rw [← hηγ]; rw [this] at hℓ1; exact hℓ1
    have hLL := hL2 (Xn m) n hm2 hℓn
    have hτK : ((((n : ℕ) : ℤ) : ℝ)) / Xn m ∈ K := by
      have e : ((((n : ℕ) : ℤ) : ℝ)) / Xn m = M * ((((n : ℕ) : ℤ) : ℝ) / γ m) := by
        rw [hγm]; field_simp
      rw [e]
      constructor
      · calc 1 / k = M * η₁ := by rw [hη₁]; field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hℓ.1 hM0.le
      · exact mul_le_mul_of_nonneg_left hℓ.2 hM0.le
    have hLU := hm1 _ hτK
    have e2 : M * Cfun ((((n : ℕ) : ℤ) : ℝ) / Xn m) =
        c ((((n : ℕ) : ℤ) : ℝ) / γ m) := by
      simp only [hc]
      congr 2
      rw [hγm]; field_simp
    have e3 : cn m ((n : ℕ) : ℤ) = M * (Xn m * ((1 / Real.pi ^ 2) * ∫ p, χ p * T (Xn m) ((n : ℕ) : ℤ) p
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))))) := by
      simp only [hcn, hγm]
      ring
    rw [e3, ← e2, ← mul_sub]
    rw [abs_mul, abs_of_pos hM0]
    have : |Xn m * ((1 / Real.pi ^ 2) * ∫ p, χ p * T (Xn m) ((n : ℕ) : ℤ) p
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) -
        Cfun ((((n : ℕ) : ℤ) : ℝ) / Xn m)| ≤ ε / M := by
      have := abs_sub_le (Xn m * ((1 / Real.pi ^ 2) * ∫ p, χ p * T (Xn m) ((n : ℕ) : ℤ) p
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))))) (cn' m ((n : ℕ) : ℤ))
        (Cfun ((((n : ℕ) : ℤ) : ℝ) / Xn m))
      have h1 : |Xn m * ((1 / Real.pi ^ 2) * ∫ p, χ p * T (Xn m) ((n : ℕ) : ℤ) p
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) - cn' m ((n : ℕ) : ℤ)|
          ≤ ε / (2 * M) := by simpa only [Int.cast_natCast] using hLL
      have h2 := hLU
      calc _ ≤ _ := this
        _ ≤ ε / (2 * M) + ε / (2 * M) := add_le_add h1 h2
        _ = ε / M := by field_simp; ring
    calc M * _ ≤ M * (ε / M) := mul_le_mul_of_nonneg_left this hM0.le
      _ = ε := by field_simp
  have hR := riemann_lag_sum γ hγT cn c hη0 hη1 hcc hunif
  have hint : (∫ t in η₁..(1 - η₁), c t) = ∫ τ in (1 / k)..(M * (1 - η₁)), Cfun τ := by
    simp only [hc]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left Cfun hM0.ne']
    have e : M * η₁ = 1 / k := by rw [hη₁]; field_simp
    rw [e, smul_eq_mul]
    field_simp
  rw [hint] at hR
  have hU : 2 * j ≤ M * (1 - η₁) := by
    have : η₁ ≤ 1 / 8 := by
      rw [hη₁, hM, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    rw [hM]; nlinarith
  have hkU : 1 / k ≤ M * (1 - η₁) := by
    have : 1 / k ≤ 1 := by rw [div_le_one hk0]; exact hk
    have : 1 ≤ 2 * j := by linarith
    linarith
  rw [vl_C_interval (α := α) j k (M * (1 - η₁)) hj hk hU hkU χ ω φ hχS hωe hφ] at hR
  refine hR.congr' ?_
  filter_upwards [Filter.Eventually.of_forall hXpos] with m hm
  have hγpos : 0 < γ m := by simp only [hγ]; positivity
  simp only [hcn]
  rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hγpos.ne', one_mul]

private lemma vl_tsum_sym (b : ℤ → ℝ) (hs : Summable b)
    (hsym : ∀ m : ℕ, b (-((m : ℤ) + 1)) = b ((m : ℤ) + 1)) :
    ∑' ℓ : ℤ, b ℓ = b 0 + 2 * ∑' m : ℕ, b ((m : ℤ) + 1) := by
  have h1 : Summable (fun n : ℕ => b (n : ℤ)) :=
    hs.comp_injective Nat.cast_injective
  have h2 : Summable (fun n : ℕ => b (-((n : ℤ) + 1))) := by
    have : (fun n : ℕ => b (-((n : ℤ) + 1))) = fun n : ℕ => b ((n : ℤ) + 1) := funext hsym
    rw [this]
    exact hs.comp_injective (fun x y h => by simpa using h)
  rw [tsum_of_nat_of_neg_add_one h1 h2]
  have h3 : ∑' n : ℕ, b (-((n : ℤ) + 1)) = ∑' n : ℕ, b ((n : ℤ) + 1) := tsum_congr hsym
  rw [h3]
  have h4 : Summable (fun n : ℕ => b ((n : ℤ) + 1)) := by
    have : (fun n : ℕ => b (-((n : ℤ) + 1))) = fun n : ℕ => b ((n : ℤ) + 1) := funext hsym
    rwa [this] at h2
  rw [Summable.tsum_eq_zero_add h1]
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one]
  ring

private lemma vl_icc_ico (f : ℤ → ℝ) (lo hi : ℤ) (hlo : 1 ≤ lo) (hlh : lo - 1 ≤ hi) :
    ∑ ℓ ∈ Finset.Icc lo hi, f ℓ =
      ∑ m ∈ Finset.Ico (lo - 1).toNat hi.toNat, f ((m : ℤ) + 1) := by
  refine Finset.sum_nbij' (fun ℓ => (ℓ - 1).toNat) (fun m => (m : ℤ) + 1) ?_ ?_ ?_ ?_ ?_
  · intro ℓ hℓ
    simp only [Finset.mem_Icc] at hℓ
    simp only [Finset.mem_Ico]
    omega
  · intro m hm
    simp only [Finset.mem_Ico] at hm
    simp only [Finset.mem_Icc]
    omega
  · intro ℓ hℓ
    simp only [Finset.mem_Icc] at hℓ
    omega
  · intro m hm
    omega
  · intro ℓ hℓ
    simp only [Finset.mem_Icc] at hℓ
    congr 1
    omega

private lemma vl_nat_split (a : ℕ → ℝ) (ha0 : ∀ m, 0 ≤ a m) (hs : Summable a) (N₁ N₂ : ℕ)
    (h12 : N₁ ≤ N₂) (A₁ D ρ : ℝ) (ha1 : ∀ m, a m ≤ A₁) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hD : 0 ≤ D) (htail : ∀ m, N₂ ≤ m → a m ≤ D * ρ ^ m) :
    ∑ m ∈ Finset.Ico N₁ N₂, a m ≤ ∑' m, a m ∧
      ∑' m, a m ≤ ∑ m ∈ Finset.Ico N₁ N₂, a m + N₁ * A₁ + D * ρ ^ N₂ / (1 - ρ) := by
  have hsplit : ∑ m ∈ Finset.range N₂, a m + ∑' m, a (m + N₂) = ∑' m, a m :=
    hs.sum_add_tsum_nat_add N₂
  have hr : ∑ m ∈ Finset.range N₂, a m =
      ∑ m ∈ Finset.range N₁, a m + ∑ m ∈ Finset.Ico N₁ N₂, a m :=
    (Finset.sum_range_add_sum_Ico a h12).symm
  have hs1 : 0 ≤ ∑ m ∈ Finset.range N₁, a m := Finset.sum_nonneg (fun m _ => ha0 m)
  have ht0 : 0 ≤ ∑' m, a (m + N₂) := tsum_nonneg (fun m => ha0 _)
  constructor
  · rw [← hsplit, hr]; linarith
  · rw [← hsplit, hr]
    have h1 : ∑ m ∈ Finset.range N₁, a m ≤ N₁ * A₁ := by
      calc _ ≤ ∑ m ∈ Finset.range N₁, A₁ := Finset.sum_le_sum (fun m _ => ha1 m)
        _ = N₁ * A₁ := by simp
    have h2 : ∑' m, a (m + N₂) ≤ D * ρ ^ N₂ / (1 - ρ) := by
      have hg : Summable (fun m : ℕ => D * ρ ^ N₂ * ρ ^ m) :=
        (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
      calc ∑' m, a (m + N₂) ≤ ∑' m : ℕ, D * ρ ^ N₂ * ρ ^ m := by
            refine Summable.tsum_le_tsum (fun m => ?_) (hs.comp_injective (add_left_injective N₂)) hg
            calc a (m + N₂) ≤ D * ρ ^ (m + N₂) := htail _ (by omega)
              _ = D * ρ ^ N₂ * ρ ^ m := by ring
        _ = D * ρ ^ N₂ * (1 - ρ)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
        _ = _ := by rw [div_eq_mul_inv]
    linarith

open Muon.DetEquiv ProbabilityTheory in
private lemma vl_exchange {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (T : ℝ → ℤ → ℝ × ℝ → ℝ)
    (hT : ∀ X ℓ p, T X ℓ p =
      ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
        Real.sqrt (p.1 * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β ℓ (X * p.1) (X * p.2)))
    (X S : ℝ) (hS : 1 ≤ S) (hSX : S ≤ X) (χ : ℝ × ℝ → ℝ) (hχc : Continuous χ)
    (hχ0 : ∀ p, 0 ≤ χ p) (hχ1 : ∀ p, χ p ≤ 1)
    (hχS : ∀ p, χ p ≠ 0 → p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S) :
    Summable (fun ℓ : ℤ => ∫ p, χ p * T X ℓ p
      ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) ∧
    ∫ p, χ p * (∑' ℓ : ℤ, T X ℓ p)
      ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) =
    ∑' ℓ : ℤ, ∫ p, χ p * T X ℓ p
      ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hα0 : 0 < α := by linarith
  have hS0 : 0 < S := by linarith
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  obtain ⟨M, c0, hM, hc0, hTb⟩ := vl_T_bound hα1 hβ0 hβ1 T hT
  obtain ⟨G0, hG0, hdom0⟩ := vl_dom (c := c0) hc0
  obtain ⟨K, C, hK, hC, hbd⟩ := vi_tsum_bd (α := α) hα1 hβ0 hβ1
  have hSq : ∀ p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S, 0 < p.1 ∧ 0 < p.2 := by
    intro p hp
    exact ⟨lt_of_lt_of_le (by positivity) hp.1.1, lt_of_lt_of_le (by positivity) hp.2.1⟩
  have hTm : ∀ ℓ : ℤ, AEStronglyMeasurable (T X ℓ)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    intro ℓ
    have : T X ℓ = fun p : ℝ × ℝ =>
      ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
        Real.sqrt (p.1 * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β ℓ (X * p.1) (X * p.2)) := funext (hT X ℓ)
    rw [this]; exact vl_term_meas hα1 hβ0 hβ1 hX0 ℓ
  have hint : ∀ ℓ : ℤ, Integrable (fun p => χ p * T X ℓ p)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    intro ℓ
    refine (hdom0 M X S ((ℓ : ℤ) : ℝ) (fun p => χ p * T X ℓ p) hM.le hX0 hS
      (hχc.aestronglyMeasurable.mul (hTm ℓ)) ?_ ?_).1
    · intro p hp
      by_contra hc
      apply hp
      by_cases h : χ p = 0
      · simp [h]
      · exact absurd (hχS p h) hc
    · intro p hp
      obtain ⟨hT0, hT1⟩ := hTb X S ℓ p hS hSX hp
      have hχp1 := hχ1 p
      have hχp0 := hχ0 p
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hχp0 hT0)]
      exact (mul_le_mul_of_nonneg_right hχp1 hT0).trans (by rw [one_mul]; exact hT1)
  have hnn : ∀ ℓ : ℤ, ∀ p : ℝ × ℝ, 0 ≤ χ p * T X ℓ p := by
    intro ℓ p
    by_cases h : χ p = 0
    · simp [h]
    · exact mul_nonneg (hχ0 p) (hTb X S ℓ p hS hSX (hχS p h)).1
  set H : ℝ × ℝ → ℝ := fun p => α * C *
    ((if p.1 ≤ 1 then K * p.1 ^ (α / 2 - 1) else K * p.1 ^ (-((α + 1) / 2))) *
      (if p.2 ≤ 1 then K * p.2 ^ (α / 2 - 1) else K * p.2 ^ (-((α + 1) / 2)))) with hH
  have hHint : Integrable H ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
    (vz_bnd_int (K := K) hα1).const_mul (α * C)
  have hsum : Summable (fun ℓ : ℤ => ∫ p, χ p * T X ℓ p
      ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) := by
    refine summable_of_sum_le (c := ∫ p, H p ∂((volume.restrict (Ioi (0:ℝ))).prod
      (volume.restrict (Ioi (0:ℝ))))) (fun ℓ => integral_nonneg (fun p => hnn ℓ p)) ?_
    intro u
    rw [← integral_finset_sum _ (fun ℓ _ => hint ℓ)]
    refine integral_mono_of_nonneg ?_ hHint ?_
    · filter_upwards with p
      exact Finset.sum_nonneg (fun ℓ _ => hnn ℓ p)
    · filter_upwards [vs_ae_pos (μ := volume) (ν := volume)] with p hp
      obtain ⟨hsm, hle⟩ := hbd X p.1 p.2 hX1 hp.1 hp.2
      have hT0 : ∀ ℓ : ℤ, 0 ≤ T X ℓ p := by
        intro ℓ
        rw [hT]
        have hr := hp.1
        have hs := hp.2
        have hu : 0 < X * p.1 := mul_pos hX0 hr
        have hv : 0 < X * p.2 := mul_pos hX0 hs
        obtain ⟨K', -, hθ⟩ := vs_theta_bd hα1 hβ0 hβ1
        have hθ1 := (hθ _ hu).1
        have hθ2 := (hθ _ hv).1
        obtain ⟨hq1, -⟩ := vs_Qm hβ0 hβ1 hu
        obtain ⟨hq2, -⟩ := vs_Qm hβ0 hβ1 hv
        have hD := vs_DLag_nonneg hβ0 hβ1 hq1.le hq2.le ℓ
        have hΔ := vs_Delta_ge hα1 hβ0 hβ1 hu hv ℓ
        have hΔ0 : 0 < profDelta α β ℓ (X * p.1) (X * p.2) :=
          lt_of_lt_of_le (one_div_pos.mpr hα0) hΔ
        have hra := Real.rpow_pos_of_pos hr α
        have hsa := Real.rpow_pos_of_pos hs α
        positivity
      have h1 : ∑ ℓ ∈ u, χ p * T X ℓ p ≤ ∑' ℓ : ℤ, T X ℓ p := by
        calc _ ≤ ∑ ℓ ∈ u, T X ℓ p := Finset.sum_le_sum (fun ℓ _ => by
              calc χ p * T X ℓ p ≤ 1 * T X ℓ p := mul_le_mul_of_nonneg_right (hχ1 p) (hT0 ℓ)
                _ = T X ℓ p := one_mul _)
          _ ≤ _ := by
              have hsm' : Summable (fun ℓ : ℤ => T X ℓ p) := by
                have : (fun ℓ : ℤ => T X ℓ p) = fun ℓ : ℤ =>
                  ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
                    Real.sqrt (p.1 * p.2)) *
                    (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
                      profTheta α β (X * p.1) * profTheta α β (X * p.2) /
                        profDelta α β ℓ (X * p.1) (X * p.2)) := funext (hT X · p)
                rw [this]; exact hsm
              exact hsm'.sum_le_tsum u (fun ℓ _ => hT0 ℓ)
      have h2 : ∑' ℓ : ℤ, T X ℓ p ≤ H p := by
        have : (∑' ℓ : ℤ, T X ℓ p) = ∑' ℓ : ℤ,
                  ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
                    Real.sqrt (p.1 * p.2)) *
                    (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
                      profTheta α β (X * p.1) * profTheta α β (X * p.2) /
                        profDelta α β ℓ (X * p.1) (X * p.2)) := tsum_congr (fun ℓ => hT X ℓ p)
        rw [this]; exact hle
      exact h1.trans h2
  refine ⟨hsum, ?_⟩
  have hnorm : Summable (fun ℓ : ℤ => ∫ p, ‖χ p * T X ℓ p‖
      ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) := by
    refine hsum.congr (fun ℓ => ?_)
    congr 1
    funext p
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn ℓ p)]
  have := integral_tsum_of_summable_integral_norm hint hnorm
  rw [this]
  congr 1
  funext p
  rw [tsum_mul_left]

private lemma vl_cut (F χ : ℝ × ℝ → ℝ) (Q : Set (ℝ × ℝ)) (hQ : MeasurableSet Q)
    (μ : Measure (ℝ × ℝ)) (hF : Integrable F μ) (hF0 : ∀ᵐ p ∂μ, 0 ≤ F p) (hχc : Continuous χ)
    (hχ0 : ∀ p, 0 ≤ χ p) (hχ1 : ∀ p, χ p ≤ 1) (hχQ : ∀ p ∈ Q, χ p = 1) :
    0 ≤ (∫ p, F p ∂μ) - ∫ p, χ p * F p ∂μ ∧
      (∫ p, F p ∂μ) - ∫ p, χ p * F p ∂μ ≤ (∫ p, F p ∂μ) - ∫ p in Q, F p ∂μ := by
  have hχF : Integrable (fun p => χ p * F p) μ := by
    refine Integrable.mono' hF (hχc.aestronglyMeasurable.mul hF.aestronglyMeasurable) ?_
    filter_upwards [hF0] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hχ0 p) hp)]
    calc χ p * F p ≤ 1 * F p := mul_le_mul_of_nonneg_right (hχ1 p) hp
      _ = F p := one_mul _
  constructor
  · have : ∫ p, χ p * F p ∂μ ≤ ∫ p, F p ∂μ := by
      refine integral_mono_ae hχF hF ?_
      filter_upwards [hF0] with p hp
      calc χ p * F p ≤ 1 * F p := mul_le_mul_of_nonneg_right (hχ1 p) hp
        _ = F p := one_mul _
    linarith
  · have : ∫ p in Q, F p ∂μ ≤ ∫ p, χ p * F p ∂μ := by
      rw [← integral_indicator hQ]
      refine integral_mono_ae (hF.indicator hQ) hχF ?_
      filter_upwards [hF0] with p hp0
      by_cases hp : p ∈ Q
      · rw [Set.indicator_of_mem hp, hχQ p hp, one_mul]
      · rw [Set.indicator_of_notMem hp]
        exact mul_nonneg (hχ0 p) hp0
    linarith

private lemma vl_floor_facts (j k X : ℝ) (hj : 1 ≤ j) (hk : 1 ≤ k) (hX : 1 ≤ X) :
    1 ≤ ⌈(1 / (k * (8 * j))) * ((8 * j) * X)⌉ ∧
    ⌈(1 / (k * (8 * j))) * ((8 * j) * X)⌉ - 1 ≤ ⌊(1 - 1 / (k * (8 * j))) * ((8 * j) * X)⌋ ∧
    (((⌈(1 / (k * (8 * j))) * ((8 * j) * X)⌉ - 1).toNat : ℕ) : ℝ) ≤ X / k ∧
    7 * j * X ≤ ((⌊(1 - 1 / (k * (8 * j))) * ((8 * j) * X)⌋.toNat : ℕ) : ℝ) + 1 := by
  have hj0 : 0 < j := by linarith
  have hk0 : 0 < k := by linarith
  have hX0 : 0 < X := by linarith
  have e1 : (1 / (k * (8 * j))) * ((8 * j) * X) = X / k := by field_simp
  have hη : 1 / (k * (8 * j)) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hηpos : 0 < 1 / (k * (8 * j)) := by positivity
  rw [e1]
  have hXk : 0 < X / k := by positivity
  have hlo : 1 ≤ ⌈X / k⌉ := Int.one_le_ceil_iff.2 hXk
  have hlt : (⌈X / k⌉ : ℝ) < X / k + 1 := Int.ceil_lt_add_one _
  have hy : X / k ≤ (1 - 1 / (k * (8 * j))) * ((8 * j) * X) := by
    have : (1 - 1 / (k * (8 * j))) * ((8 * j) * X) = (8 * j) * X - X / k := by
      rw [sub_mul, one_mul, e1]
    rw [this]
    have h1 : X / k ≤ X := div_le_self hX0.le hk
    nlinarith
  have hfl : ⌈X / k⌉ - 1 ≤ ⌊(1 - 1 / (k * (8 * j))) * ((8 * j) * X)⌋ := by
    apply Int.le_floor.2
    push_cast
    linarith
  refine ⟨hlo, hfl, ?_, ?_⟩
  · have h0 : (0:ℤ) ≤ ⌈X / k⌉ - 1 := by omega
    have h2 : (((⌈X / k⌉ - 1).toNat : ℕ) : ℝ) = (((⌈X / k⌉ - 1 : ℤ)) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h0
    rw [h2]; push_cast; linarith
  · have hfl0 : (0:ℤ) ≤ ⌊(1 - 1 / (k * (8 * j))) * ((8 * j) * X)⌋ := by
      apply Int.floor_nonneg.2
      have : 0 ≤ X / k := hXk.le
      linarith
    have h2 : (((⌊(1 - 1 / (k * (8 * j))) * ((8 * j) * X)⌋.toNat : ℕ)) : ℝ) =
        ((⌊(1 - 1 / (k * (8 * j))) * ((8 * j) * X)⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hfl0
    rw [h2]
    have h3 := Int.sub_one_lt_floor ((1 - 1 / (k * (8 * j))) * ((8 * j) * X))
    have h4 : (1 - 1 / (k * (8 * j))) * ((8 * j) * X) ≥ 7 * j * X := by
      have : (1 - 1 / (k * (8 * j))) * ((8 * j) * X) = (8 * j) * X - X / k := by
        rw [sub_mul, one_mul, e1]
      rw [this]
      have h1 : X / k ≤ j * X := by
        rw [div_le_iff₀ hk0]; nlinarith
      nlinarith
    linarith

set_option maxHeartbeats 1600000 in
open Muon.DetEquiv ProbabilityTheory in
private lemma vl_fixed {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (T : ℝ → ℤ → ℝ × ℝ → ℝ)
    (hT : ∀ X ℓ p, T X ℓ p =
      ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
        Real.sqrt (p.1 * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β ℓ (X * p.1) (X * p.2)))
    (C₃ c₃ : ℝ) (hC₃ : 0 < C₃) (hc₃ : 0 < c₃)
    (hBb : ∀ (X S : ℝ) (ℓ : ℤ) (χ : ℝ × ℝ → ℝ), 1 ≤ S → S ≤ X →
      (∀ p, 0 ≤ χ p) → (∀ p, χ p ≤ 1) →
      (∀ p, χ p ≠ 0 → p ∈ Icc (1 / S) S ×ˢ Icc (1 / S) S) →
      0 ≤ ∫ p, χ p * T X ℓ p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ∧
      ∫ p, χ p * T X ℓ p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ≤
        C₃ * S / X ∧
      (2 * S * X ≤ |(ℓ : ℝ)| →
        ∫ p, χ p * T X ℓ p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ≤
          C₃ * S / X * Real.exp (-c₃ * |(ℓ : ℝ)|)))
    (j k : ℝ) (hj : 1 ≤ j) (hk : 1 ≤ k)
    (χ : ℝ × ℝ → ℝ) (hχc : Continuous χ) (hχ0 : ∀ p, 0 ≤ χ p) (hχ1 : ∀ p, χ p ≤ 1)
    (hχsymm : ∀ p : ℝ × ℝ, χ p.swap = χ p)
    (hχS : ∀ p, χ p ≠ 0 → p ∈ Icc (1 / (2 * j)) (2 * j) ×ˢ Icc (1 / (2 * j)) (2 * j))
    (X : ℝ) (hX : 1 ≤ X) (hjX : 2 * j ≤ X) (e1 : ℝ)
    (hcut0 : 0 ≤ (∫ p, (∑' ℓ : ℤ, T X ℓ p)
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) -
      ∫ p, χ p * (∑' ℓ : ℤ, T X ℓ p)
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))))
    (hcut : (∫ p, (∑' ℓ : ℤ, T X ℓ p)
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) -
      ∫ p, χ p * (∑' ℓ : ℤ, T X ℓ p)
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ≤ e1) :
    0 ≤ profG α β X / X - 2 * ∑ ℓ ∈ Finset.Icc ⌈(1 / (k * (8 * j))) * ((8 * j) * X)⌉
        ⌊(1 - 1 / (k * (8 * j))) * ((8 * j) * X)⌋,
        (1 / Real.pi ^ 2) * ∫ p, χ p * T X ℓ p
          ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ∧
    profG α β X / X - 2 * ∑ ℓ ∈ Finset.Icc ⌈(1 / (k * (8 * j))) * ((8 * j) * X)⌉
        ⌊(1 - 1 / (k * (8 * j))) * ((8 * j) * X)⌋,
        (1 / Real.pi ^ 2) * ∫ p, χ p * T X ℓ p
          ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ≤
      e1 / Real.pi ^ 2 + C₃ * (2 * j) / (Real.pi ^ 2 * X) + 2 * (C₃ * (2 * j) / (Real.pi ^ 2 * k)) +
        2 * (C₃ * (2 * j) / Real.pi ^ 2 * Real.exp (-c₃ * X) / (1 - Real.exp (-c₃))) := by
  have hj0 : 0 < j := by linarith
  have hk0 : 0 < k := by linarith
  have hX0 : 0 < X := by linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπ2 : 0 < Real.pi ^ 2 := by positivity
  have hS1 : 1 ≤ 2 * j := by linarith
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  set Sx : ℝ × ℝ → ℝ := fun p => ∑' ℓ : ℤ, T X ℓ p with hSx
  obtain ⟨hsum, hexch⟩ := vl_exchange hα1 hβ0 hβ1 T hT X (2 * j) hS1 hjX χ hχc hχ0 hχ1 hχS
  -- profile representation
  have hG : profG α β X / X = (1 / Real.pi ^ 2) * ∫ p, Sx p ∂μ := by
    rw [vi_G_rep hα1 hβ0 hβ1 hX0]
    congr 2
    funext p
    exact tsum_congr (fun ℓ => (hT X ℓ p).symm)
  -- the coefficient sequence
  set b : ℤ → ℝ := fun ℓ => (1 / Real.pi ^ 2) * ∫ p, χ p * T X ℓ p ∂μ with hb
  have hbs : Summable b := hsum.mul_left _
  have hSig : ∑' ℓ : ℤ, b ℓ = (1 / Real.pi ^ 2) * ∫ p, χ p * Sx p ∂μ := by
    simp only [hb]
    rw [tsum_mul_left, ← hexch]
  have hbound := fun (ℓ : ℤ) => hBb X (2 * j) ℓ χ hS1 hjX hχ0 hχ1 hχS
  have hb0 : ∀ ℓ, 0 ≤ b ℓ := fun ℓ => by
    simp only [hb]; exact mul_nonneg (by positivity) (hbound ℓ).1
  have hb1 : ∀ ℓ, b ℓ ≤ (1 / Real.pi ^ 2) * (C₃ * (2 * j) / X) := fun ℓ => by
    simp only [hb]
    exact mul_le_mul_of_nonneg_left (hbound ℓ).2.1 (by positivity)
  have hsym : ∀ m : ℕ, b (-((m : ℤ) + 1)) = b ((m : ℤ) + 1) := by
    intro m
    have := vl_B_symm T hT χ hχsymm X (m + 1) (by omega)
    simp only [hb]
    push_cast at this
    rw [this]
  have hSig' := vl_tsum_sym b hbs hsym
  -- floors
  obtain ⟨hlo, hlh, hN1, hN2⟩ := vl_floor_facts j k X hj hk hX
  set lo : ℤ := ⌈(1 / (k * (8 * j))) * ((8 * j) * X)⌉ with hlo_def
  set hi : ℤ := ⌊(1 - 1 / (k * (8 * j))) * ((8 * j) * X)⌋ with hhi_def
  set N₁ : ℕ := (lo - 1).toNat with hN₁
  set N₂ : ℕ := hi.toNat with hN₂
  have hN12 : N₁ ≤ N₂ := by omega
  set a : ℕ → ℝ := fun m => b ((m : ℤ) + 1) with ha
  have ha0 : ∀ m, 0 ≤ a m := fun m => hb0 _
  have has : Summable a := hbs.comp_injective (fun x y h => by simpa using h)
  set A₁ : ℝ := (1 / Real.pi ^ 2) * (C₃ * (2 * j) / X) with hA₁
  set ρ : ℝ := Real.exp (-c₃) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by rw [hρ, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  set D : ℝ := A₁ * ρ with hD
  have hD0 : 0 ≤ D := by positivity
  have htail : ∀ m : ℕ, N₂ ≤ m → a m ≤ D * ρ ^ m := by
    intro m hm
    have h2 : 2 * (2 * j) * X ≤ |(((m : ℤ) + 1 : ℤ) : ℝ)| := by
      have hmr : (N₂ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      rw [abs_of_nonneg (by positivity)]
      push_cast
      nlinarith
    have := (hbound ((m : ℤ) + 1)).2.2 h2
    simp only [ha, hb]
    calc (1 / Real.pi ^ 2) * ∫ p, χ p * T X ((m : ℤ) + 1) p ∂μ
        ≤ (1 / Real.pi ^ 2) * (C₃ * (2 * j) / X * Real.exp (-c₃ * |(((m : ℤ) + 1 : ℤ) : ℝ)|)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = D * ρ ^ m := by
          have hpos : (0:ℝ) ≤ (((m : ℤ) + 1 : ℤ) : ℝ) := by positivity
          rw [abs_of_nonneg hpos]
          have e : Real.exp (-c₃ * (((m : ℤ) + 1 : ℤ) : ℝ)) = ρ * ρ ^ m := by
            rw [hρ, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
          rw [e, hD, hA₁]; ring
  obtain ⟨hs1, hs2⟩ := vl_nat_split a ha0 has N₁ N₂ hN12 A₁ D ρ (fun m => hb1 _) hρ0 hρ1 hD0 htail
  have hW : ∑ ℓ ∈ Finset.Icc lo hi, b ℓ = ∑ m ∈ Finset.Ico N₁ N₂, a m :=
    vl_icc_ico b lo hi hlo hlh
  change 0 ≤ profG α β X / X - 2 * ∑ ℓ ∈ Finset.Icc lo hi, b ℓ ∧
    profG α β X / X - 2 * ∑ ℓ ∈ Finset.Icc lo hi, b ℓ ≤ _
  rw [hW]
  have hI : profG α β X / X - ∑' ℓ : ℤ, b ℓ =
      (1 / Real.pi ^ 2) * ((∫ p, Sx p ∂μ) - ∫ p, χ p * Sx p ∂μ) := by
    rw [hG, hSig]; ring
  have hI0 : 0 ≤ profG α β X / X - ∑' ℓ : ℤ, b ℓ := by
    rw [hI]; exact mul_nonneg (by positivity) hcut0
  have hI1 : profG α β X / X - ∑' ℓ : ℤ, b ℓ ≤ e1 / Real.pi ^ 2 := by
    rw [hI]
    calc _ ≤ (1 / Real.pi ^ 2) * e1 := mul_le_mul_of_nonneg_left hcut (by positivity)
      _ = _ := by ring
  have hb0' : b 0 ≤ C₃ * (2 * j) / (Real.pi ^ 2 * X) := by
    refine (hb1 0).trans (le_of_eq ?_)
    show (1 / Real.pi ^ 2) * (C₃ * (2 * j) / X) = _
    field_simp
  have hN1A : (N₁ : ℝ) * A₁ ≤ C₃ * (2 * j) / (Real.pi ^ 2 * k) := by
    have hA0 : 0 ≤ A₁ := by positivity
    calc (N₁ : ℝ) * A₁ ≤ (X / k) * A₁ := mul_le_mul_of_nonneg_right hN1 hA0
      _ = _ := by
        show (X / k) * ((1 / Real.pi ^ 2) * (C₃ * (2 * j) / X)) = _
        field_simp
  have hTail : D * ρ ^ N₂ / (1 - ρ) ≤ C₃ * (2 * j) / Real.pi ^ 2 * Real.exp (-c₃ * X) / (1 - ρ) := by
    have h1ρ : 0 < 1 - ρ := by linarith
    apply div_le_div_of_nonneg_right _ h1ρ.le
    have e : D * ρ ^ N₂ = A₁ * Real.exp (-c₃ * ((N₂ : ℝ) + 1)) := by
      rw [hD, hρ, mul_assoc, ← pow_succ', ← Real.exp_nat_mul]
      congr 2
      push_cast; ring
    rw [e]
    have hexp : Real.exp (-c₃ * ((N₂ : ℝ) + 1)) ≤ Real.exp (-c₃ * X) := by
      apply Real.exp_le_exp.2
      have : X ≤ (N₂ : ℝ) + 1 := by nlinarith
      nlinarith
    have hA : A₁ ≤ C₃ * (2 * j) / Real.pi ^ 2 := by
      rw [hA₁]
      have : C₃ * (2 * j) / X ≤ C₃ * (2 * j) := div_le_self (by positivity) hX
      calc _ ≤ (1 / Real.pi ^ 2) * (C₃ * (2 * j)) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    calc A₁ * Real.exp (-c₃ * ((N₂ : ℝ) + 1)) ≤ A₁ * Real.exp (-c₃ * X) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
  have hb00 := hb0 0
  constructor
  · linarith
  · linarith

open Muon.DetEquiv ProbabilityTheory in
private lemma vl_T_nn {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (T : ℝ → ℤ → ℝ × ℝ → ℝ)
    (hT : ∀ X ℓ p, T X ℓ p =
      ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
        Real.sqrt (p.1 * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β ℓ (X * p.1) (X * p.2)))
    {X : ℝ} (hX0 : 0 < X) (ℓ : ℤ) {p : ℝ × ℝ} (hp : 0 < p.1 ∧ 0 < p.2) : 0 ≤ T X ℓ p := by
  have hα0 : 0 < α := by linarith
  rw [hT]
  have hr := hp.1
  have hs := hp.2
  have hu : 0 < X * p.1 := mul_pos hX0 hr
  have hv : 0 < X * p.2 := mul_pos hX0 hs
  obtain ⟨K', -, hθ⟩ := vs_theta_bd hα1 hβ0 hβ1
  have hθ1 := (hθ _ hu).1
  have hθ2 := (hθ _ hv).1
  obtain ⟨hq1, -⟩ := vs_Qm hβ0 hβ1 hu
  obtain ⟨hq2, -⟩ := vs_Qm hβ0 hβ1 hv
  have hD := vs_DLag_nonneg hβ0 hβ1 hq1.le hq2.le ℓ
  have hΔ := vs_Delta_ge hα1 hβ0 hβ1 hu hv ℓ
  have hΔ0 : 0 < profDelta α β ℓ (X * p.1) (X * p.2) :=
    lt_of_lt_of_le (one_div_pos.mpr hα0) hΔ
  have hra := Real.rpow_pos_of_pos hr α
  have hsa := Real.rpow_pos_of_pos hs α
  positivity

set_option maxHeartbeats 3200000 in
open Muon.DetEquiv ProbabilityTheory in
private lemma vl_core {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (Xn : ℕ → ℝ) (hXn1 : ∀ m, 1 ≤ Xn m) (hXn : Tendsto Xn atTop atTop) :
    Tendsto (fun m => profG α β (Xn m) / Xn m) atTop (𝓝 (4 * Kc α / (α - 1))) := by
  have hα0 : 0 < α := by linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπ2 : 0 < Real.pi ^ 2 := by positivity
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  set T : ℝ → ℤ → ℝ × ℝ → ℝ := fun X ℓ p =>
      ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
        Real.sqrt (p.1 * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β ℓ (X * p.1) (X * p.2)) with hTdef
  have hT : ∀ X ℓ p, T X ℓ p =
      ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
        Real.sqrt (p.1 * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ *
          profTheta α β (X * p.1) * profTheta α β (X * p.2) /
            profDelta α β ℓ (X * p.1) (X * p.2)) := fun _ _ _ => rfl
  obtain ⟨C₃, c₃, hC₃, hc₃, hBb⟩ := vl_B_bd hα1 hβ0 hβ1 T hT
  -- cut-off data
  obtain ⟨K, C, hK, hC, hbd⟩ := vi_tsum_bd (α := α) hα1 hβ0 hβ1
  set H : ℝ × ℝ → ℝ := fun p => α * C *
    ((if p.1 ≤ 1 then K * p.1 ^ (α / 2 - 1) else K * p.1 ^ (-((α + 1) / 2))) *
      (if p.2 ≤ 1 then K * p.2 ^ (α / 2 - 1) else K * p.2 ^ (-((α + 1) / 2)))) with hH
  have hHint : Integrable H μ := (vz_bnd_int (K := K) hα1).const_mul (α * C)
  set F : ℝ → ℝ × ℝ → ℝ := fun X p => ∑' ℓ : ℤ, T X ℓ p with hF
  have hFint : ∀ X : ℝ, 1 ≤ X → Integrable (F X) μ := fun X hX =>
    vi_sum_integrable hα1 hβ0 hβ1 hX
  have hFnn : ∀ X : ℝ, 1 ≤ X → ∀ᵐ p ∂μ, 0 ≤ F X p := by
    intro X hX
    filter_upwards [vs_ae_pos (μ := volume) (ν := volume)] with p hp
    exact tsum_nonneg (fun ℓ => vl_T_nn hα1 hβ0 hβ1 T hT (by linarith) ℓ hp)
  have hFbd : ∀ X : ℝ, 1 ≤ X → ∀ᵐ p ∂μ, ‖F X p‖ ≤ H p := by
    intro X hX
    filter_upwards [hFnn X hX, vs_ae_pos (μ := volume) (ν := volume)] with p h0 hp
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact (hbd X p.1 p.2 hX hp.1 hp.2).2
  have hcutR := vi_uniform_square_tail F H hHint hFint hFbd
  -- the limit constant
  have hvi := vi_shell_integral hα1
  set Jsh : ℝ := ∫ τ in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ),
    (profZeta α 1 (r + τ) - profZeta α 1 r) / τ * (r / (r + τ)) ^ ((α - 1) / 2) with hJsh
  -- the family of cutoffs
  have hsetup : ∀ n : ℕ, ∃ χ ω φ : ℝ × ℝ → ℝ, Continuous χ ∧ (∀ p, 0 ≤ χ p) ∧ (∀ p, χ p ≤ 1) ∧
      (∀ p : ℝ × ℝ, χ p.swap = χ p) ∧
      (∀ p ∈ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ×ˢ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1), χ p = 1) ∧
      (∀ p, χ p ≠ 0 → p ∈ Icc (1 / (2 * ((n : ℝ) + 1))) (2 * ((n : ℝ) + 1)) ×ˢ
        Icc (1 / (2 * ((n : ℝ) + 1))) (2 * ((n : ℝ) + 1))) ∧
      (∀ p, 0 ≤ ω p) ∧ (∀ p, ω p ≤ 1) ∧ Measurable ω ∧
      (∀ p : ℝ × ℝ, 1 / (2 * ((n : ℝ) + 1) ^ 2) ≤ p.2 - p.1 → ω p = 1) ∧
      (∀ p : ℝ × ℝ, ω p ≠ 0 → p.1 < p.2) ∧
      (∀ p : ℝ × ℝ, φ p = χ p * ω p *
        ((profZeta α 1 p.2 - profZeta α 1 p.1) / (p.2 - p.1) * (p.1 / p.2) ^ ((α - 1) / 2))) ∧
      Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0 := by
    intro n
    exact vl_setup hα1 ((n : ℝ) + 1) (((n : ℝ) + 1) ^ 2) (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
      (by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  choose χ ω φ hχc hχ0 hχ1 hχsw hχone hχS hω0 hω1 hωm hωe hωp hφ hφc hφs hφt using hsetup
  -- the J-limit
  set Jn : ℕ → ℝ := fun n => ∫ τ in Ioi (1 / (((n : ℝ) + 1) ^ 2)), ∫ r in Ioi (0:ℝ), χ n (r, r + τ) *
      ((profZeta α 1 (r + τ) - profZeta α 1 r) / τ * (r / (r + τ)) ^ ((α - 1) / 2)) with hJn
  have hj1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hnT : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hkkT : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp hnT
  have hone : ∀ p : ℝ × ℝ, 0 < p.1 → 0 < p.2 → ∀ᶠ n in atTop, χ n p = 1 := by
    intro p hp1 hp2
    filter_upwards [hnT.eventually_ge_atTop (max (max p.1 p.2) (max (1 / p.1) (1 / p.2)))] with n hn
    apply hχone n p
    have h1 : p.1 ≤ (n : ℝ) + 1 := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
    have h2 : p.2 ≤ (n : ℝ) + 1 := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
    have h3 : 1 / p.1 ≤ (n : ℝ) + 1 := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
    have h4 : 1 / p.2 ≤ (n : ℝ) + 1 := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
    have hnn : 0 < (n : ℝ) + 1 := by linarith [hj1 n]
    refine ⟨⟨?_, h1⟩, ⟨?_, h2⟩⟩
    · rw [div_le_iff₀ hnn]; rw [div_le_iff₀ hp1] at h3; linarith
    · rw [div_le_iff₀ hnn]; rw [div_le_iff₀ hp2] at h4; linarith
  have hJ : Tendsto Jn atTop (𝓝 Jsh) :=
    vl_J_lim hα1 χ (fun n => (hχc n).measurable) hχ0 hχ1 hone (fun n => ((n : ℝ) + 1) ^ 2)
      hkkT (fun n => by have := hj1 n; positivity)
  have hdecay : Tendsto (fun n : ℕ => 4 * C₃ / (Real.pi ^ 2 * ((n : ℝ) + 1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hnT.const_mul_atTop hπ2)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR1, hRcut⟩ := hcutR (Real.pi ^ 2 * ε / 8) (by positivity)
  have hev := ((hnT.eventually_ge_atTop R).and
    (Metric.tendsto_nhds.1 hJ (ε / 16) (by positivity))).and
    (hdecay.eventually (Iio_mem_nhds (by positivity : (0:ℝ) < ε / 8)))
  obtain ⟨n, ⟨hn1, hn2⟩, hn3⟩ := hev.exists
  have hj1' : 1 ≤ (n : ℝ) + 1 := hj1 n
  have hk1 : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hwin := vl_window hα1 hβ0 hβ1 T hT ((n : ℝ) + 1) (((n : ℝ) + 1) ^ 2) hj1' hk1 (χ n) (ω n) (φ n)
    (hχc n) (hχ0 n) (hχ1 n) (hχS n) (hω0 n) (hω1 n) (hωm n) (hωe n) (hωp n) (hφ n) (hφc n)
    (hφs n) (hφt n) Xn (fun m => lt_of_lt_of_le one_pos (hXn1 m)) hXn
  have hdist := Metric.tendsto_nhds.1 hwin (ε / 16) (by positivity)
  have hA₀ : 0 < C₃ * (2 * ((n : ℝ) + 1)) := by positivity
  have hρ1 : Real.exp (-c₃) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have h1ρ : 0 < 1 - Real.exp (-c₃) := by linarith
  have hexpT : Tendsto (fun m => Real.exp (-c₃ * Xn m)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hXn.const_mul_atTop_of_neg (by linarith : -c₃ < 0))
  have hδ' : (0:ℝ) < Real.pi ^ 2 * ε * (1 - Real.exp (-c₃)) / (16 * (C₃ * (2 * ((n : ℝ) + 1)))) := by
    positivity
  have hev2 := (hdist.and (hXn.eventually_ge_atTop
      (max (2 * ((n : ℝ) + 1)) (8 * (C₃ * (2 * ((n : ℝ) + 1))) / (Real.pi ^ 2 * ε))))).and
    (hexpT.eventually (Iio_mem_nhds hδ'))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev2
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨⟨hm1, hm2⟩, hm3⟩ := hN m hm
  have hX1 := hXn1 m
  have hm2a : 2 * ((n : ℝ) + 1) ≤ Xn m := (le_max_left _ _).trans hm2
  have hm2b : 8 * (C₃ * (2 * ((n : ℝ) + 1))) / (Real.pi ^ 2 * ε) ≤ Xn m := (le_max_right _ _).trans hm2
  -- cut-off estimate
  have hFm := hFint (Xn m) hX1
  obtain ⟨hc0, hc1⟩ := vl_cut (F (Xn m)) (χ n) (Icc (1 / R) R ×ˢ Icc (1 / R) R)
    (measurableSet_Icc.prod measurableSet_Icc) μ hFm (hFnn _ hX1) (hχc n) (hχ0 n) (hχ1 n)
    (fun p hp => by
      apply hχone n p
      have hRn : R ≤ (n : ℝ) + 1 := hn1
      have hR0 : 0 < R := by linarith
      have hj0 : 0 < (n : ℝ) + 1 := by linarith
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / R := one_div_le_one_div_of_le hR0 hRn
      exact ⟨⟨h1.trans hp.1.1, hp.1.2.trans hRn⟩, ⟨h1.trans hp.2.1, hp.2.2.trans hRn⟩⟩)
  have hRc := hRcut (Xn m) hX1
  have hcut : (∫ p, F (Xn m) p ∂μ) - ∫ p, χ n p * F (Xn m) p ∂μ ≤ Real.pi ^ 2 * ε / 8 :=
    hc1.trans ((le_abs_self _).trans hRc)
  obtain ⟨hlow, hup⟩ := vl_fixed hα1 hβ0 hβ1 T hT C₃ c₃ hC₃ hc₃ hBb ((n : ℝ) + 1)
    (((n : ℝ) + 1) ^ 2) hj1' hk1 (χ n) (hχc n) (hχ0 n) (hχ1 n) (hχsw n) (hχS n) (Xn m) hX1 hm2a
    (Real.pi ^ 2 * ε / 8) hc0 hcut
  rw [Real.dist_eq, ← hvi]
  have b1 : Real.pi ^ 2 * ε / 8 / Real.pi ^ 2 = ε / 8 := by field_simp
  have b2 : C₃ * (2 * ((n : ℝ) + 1)) / (Real.pi ^ 2 * Xn m) ≤ ε / 8 := by
    rw [div_le_iff₀ (by positivity)]
    have := (div_le_iff₀ (by positivity : 0 < Real.pi ^ 2 * ε)).1 hm2b
    nlinarith
  have b3 : 2 * (C₃ * (2 * ((n : ℝ) + 1)) / (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2)) < ε / 8 := by
    have e : 2 * (C₃ * (2 * ((n : ℝ) + 1)) / (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2)) =
        4 * C₃ / (Real.pi ^ 2 * ((n : ℝ) + 1)) := by
      have : (n : ℝ) + 1 ≠ 0 := by linarith
      field_simp; ring
    rw [e]; exact hn3
  have b4 : 2 * (C₃ * (2 * ((n : ℝ) + 1)) / Real.pi ^ 2 * Real.exp (-c₃ * Xn m) /
      (1 - Real.exp (-c₃))) ≤ ε / 8 := by
    have hm3' : Real.exp (-c₃ * Xn m) < Real.pi ^ 2 * ε * (1 - Real.exp (-c₃)) /
        (16 * (C₃ * (2 * ((n : ℝ) + 1)))) := hm3
    rw [lt_div_iff₀ (by positivity)] at hm3'
    have hq : C₃ * (2 * ((n : ℝ) + 1)) / Real.pi ^ 2 * Real.exp (-c₃ * Xn m) /
        (1 - Real.exp (-c₃)) ≤ ε / 16 := by
      rw [div_le_iff₀ h1ρ, div_mul_eq_mul_div, div_le_iff₀ hπ2]
      nlinarith
    linarith
  have hW := (abs_lt.1 (Real.dist_eq _ _ ▸ hm1))
  have hJ := (abs_lt.1 (Real.dist_eq _ _ ▸ hn2))
  rw [abs_lt]
  constructor <;> linarith [hW.1, hW.2, hJ.1, hJ.2]

/-- `lem:app-pl-supervol`, the endpoint `G_{α,β}(X) → 1/s_2` as `X ↓ 0` of `eqn:app-pl-crossover-ends`
(snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-crossover-ends}
\begin{gathered}
\Phi_{\alpha,\bmom}(y)\sim\sqrt{y/\sw2}\ (y\to\infty),\quad
\Phi_{\alpha,\bmom}(y)\sim d_\alpha\,y^{\frac{\alpha-1}{2\alpha}}\ (y\downarrow0),\\
G_{\alpha,\bmom}(X)\to\frac1{\sw2}\ (X\downarrow0),\quad
G_{\alpha,\bmom}(X)\sim\frac{4K_\alpha}{\alpha-1}X\ (X\to\infty).
\end{gathered}
\end{equation}
-/
theorem lem_app_pl_supervol_ii_zero {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun X : ℝ => profG α β X) (𝓝[>] (0:ℝ)) (𝓝 (1 / sPow β 2)) := by
  have hα0 : 0 < α := by linarith
  have hs2 := vz_s2_pos hβ0 hβ1
  obtain ⟨K, C, hK, hC, hbd⟩ := vz_tsum_bd (α := α) hα1 hβ0 hβ1
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  have hae : ∀ᵐ p ∂μ, 0 < p.1 ∧ 0 < p.2 := vs_ae_pos
  have hDCT : Tendsto (fun X : ℝ => ∫ p : ℝ × ℝ, ∑' ℓ : ℤ, X ^ 2 *
      (Real.sqrt (profZeta α X (X * p.1) * (1 - profZeta α X (X * p.1)) *
              (profZeta α X (X * p.2) * (1 - profZeta α X (X * p.2)))) /
          Real.sqrt ((X * p.1) * (X * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ * profTheta α β (X * p.1) *
          profTheta α β (X * p.2) / profDelta α β ℓ (X * p.1) (X * p.2))) ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ p : ℝ × ℝ, 1 / sPow β 2 *
        ((α * p.1 ^ (α / 2 - 1) / (1 + p.1 ^ α)) * (α * p.2 ^ (α / 2 - 1) / (1 + p.2 ^ α))) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (bound := fun p : ℝ × ℝ => α * C * ((if p.1 ≤ 1 then K * p.1 ^ (α / 2 - 1) else K * p.1 ^ (-((α + 1) / 2))) *
        (if p.2 ≤ 1 then K * p.2 ^ (α / 2 - 1) else K * p.2 ^ (-((α + 1) / 2))))) ?_ ?_ ?_ ?_
    · filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with X hX
      exact vz_Phi_meas hα1 hβ0 hβ1 hX.1 hX.2
    · filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with X hX
      filter_upwards [hae] with p hp
      obtain ⟨-, hle⟩ := hbd X p.1 p.2 hX.1 hX.2 hp.1 hp.2
      have h0 : 0 ≤ ∑' ℓ : ℤ, X ^ 2 *
        (Real.sqrt (profZeta α X (X * p.1) * (1 - profZeta α X (X * p.1)) *
              (profZeta α X (X * p.2) * (1 - profZeta α X (X * p.2)))) /
          Real.sqrt ((X * p.1) * (X * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ * profTheta α β (X * p.1) *
          profTheta α β (X * p.2) / profDelta α β ℓ (X * p.1) (X * p.2))) :=
        tsum_nonneg fun ℓ => (vz_term_bd hα1 hβ0 hβ1 hX.1 hp.1 hp.2 ℓ).1
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hle
    · exact (vz_bnd_int (K := K) hα1).const_mul (α * C)
    · filter_upwards [hae] with p hp
      exact vz_sum_lim hα1 hβ0 hβ1 hp.1 hp.2
  have hval : ∫ p : ℝ × ℝ, 1 / sPow β 2 *
      ((α * p.1 ^ (α / 2 - 1) / (1 + p.1 ^ α)) * (α * p.2 ^ (α / 2 - 1) / (1 + p.2 ^ α))) ∂μ =
      Real.pi ^ 2 / sPow β 2 := by
    rw [integral_const_mul]
    have := integral_prod_mul (μ := volume.restrict (Ioi (0:ℝ))) (ν := volume.restrict (Ioi (0:ℝ)))
      (fun r : ℝ => α * r ^ (α / 2 - 1) / (1 + r ^ α)) (fun r : ℝ => α * r ^ (α / 2 - 1) / (1 + r ^ α))
    rw [hμ, this]
    have hk := vz_k_integral hα0
    rw [show (∫ x : ℝ, α * x ^ (α / 2 - 1) / (1 + x ^ α) ∂(volume.restrict (Ioi (0:ℝ)))) = Real.pi from hk]
    ring
  rw [hval] at hDCT
  have hfin := hDCT.const_mul (1 / Real.pi ^ 2)
  have hpi : (1 / Real.pi ^ 2) * (Real.pi ^ 2 / sPow β 2) = 1 / sPow β 2 := by
    have := Real.pi_pos
    field_simp
  rw [hpi] at hfin
  refine hfin.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with X hX
  exact (vz_G_rep hα1 hβ0 hβ1 (show (0:ℝ) < X from hX)).symm

/-- `lem:app-pl-supervol`, the endpoint `G_{α,β}(X) ∼ 4K_α X/(α-1)` as `X → ∞` of `eqn:app-pl-crossover-ends`
(snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-crossover-ends}
\begin{gathered}
\Phi_{\alpha,\bmom}(y)\sim\sqrt{y/\sw2}\ (y\to\infty),\quad
\Phi_{\alpha,\bmom}(y)\sim d_\alpha\,y^{\frac{\alpha-1}{2\alpha}}\ (y\downarrow0),\\
G_{\alpha,\bmom}(X)\to\frac1{\sw2}\ (X\downarrow0),\quad
G_{\alpha,\bmom}(X)\sim\frac{4K_\alpha}{\alpha-1}X\ (X\to\infty).
\end{gathered}
\end{equation}
-/
theorem lem_app_pl_supervol_ii_inf {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsEquivalent atTop (fun X : ℝ => profG α β X) (fun X : ℝ => 4 * Kc α / (α - 1) * X) := by
  refine vi_endpoint_of_ratio hα1 ?_
  rw [Filter.tendsto_iff_seq_tendsto]
  intro x hx
  have hx' : Tendsto (fun n => max (x n) 1) atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_left _ _) hx
  have hcore := vl_core hα1 hβ0 hβ1 (fun n => max (x n) 1) (fun n => le_max_right _ _) hx'
  refine hcore.congr' ?_
  filter_upwards [hx.eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply]
  rw [max_eq_left hn]

/-- `lem:app-pl-supervol`, the Gamma law `Γ_α(x) ∼ 4K_α²x/(α-1)` as `x ↓ 0` (snapshot `cr-2026-10-23`).
LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-bulk-small}
\begin{gathered}
\Psi_\alpha(x)\sim\begin{cases}\dfrac{c_0}{\sqrt{1-\alpha}}\log(x^{-\alpha}),&\alpha<1,\\[6pt]
\dfrac23c_0\big[\log(1/x)\big]^{3/2},&\alpha=1,\\[6pt]
d_\alpha\sqrt{K_\alpha}\,x^{-(\alpha-1)/2},&\alpha>1,\end{cases}
\\
\Gamma_\alpha(x)\sim\begin{cases}\dfrac{x^\alpha\big[\log(x^{-\alpha})\big]^2}{1-\alpha},&\alpha<1,\\[6pt]
\dfrac49x\big[\log(1/x)\big]^3,&\alpha=1,\\[6pt]
\dfrac{4K_\alpha^2}{\alpha-1}\,x,&\alpha>1.\end{cases}
\end{gathered}
\end{equation}
-/
theorem lem_app_pl_supervol_iv_gamma {α : ℝ} (hα1 : 1 < α) :
    IsEquivalent (𝓝[>] (0:ℝ)) (fun x : ℝ => profGamma α x) (fun x : ℝ => 4 * Kc α ^ 2 / (α - 1) * x) := by
  have hK := vg_K_pos hα1
  have hL : 0 < 4 * Kc α ^ 2 / (α - 1) := by
    have : 0 < α - 1 := by linarith
    positivity
  refine isEquivalent_of_tendsto_one ?_
  have h := (vg_Gamma_lim hα1).div_const (4 * Kc α ^ 2 / (α - 1))
  rw [div_self hL.ne'] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (0:ℝ) < x := hx
  simp only [Pi.div_apply]
  field_simp

/-! ## Volatility in the supercritical regime (part-form) -/

private lemma pg9_Kc_pos {α : ℝ} (hα1 : 1 < α) : 0 < Kc α := by
  unfold Kc
  have hα0 : 0 < α := by linarith
  have hs : 0 < Real.sin (Real.pi / α) :=
    Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hα0)
      (div_lt_self Real.pi_pos hα1)
  positivity

private lemma pg9_rowFrac_zero_of_X_tendsto {α β X0 : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α)
    (i : ∀ n, Fin (N n))
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 X0)) :
    Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0) := by
  have hK : 0 < Kc α := pg9_Kc_pos hα1
  have hden : Tendsto (fun n => Kc α * gammaOf (N n) (B n)) atTop atTop :=
    R.hγ.const_mul_atTop hK
  have h := hX.div_atTop hden
  refine h.congr (fun n => ?_)
  have hB : (B n : ℝ) ≠ 0 := by exact_mod_cast (R.hBpos n).ne'
  have hN : (N n : ℝ) ≠ 0 := by exact_mod_cast (R.hNpos n).ne'
  have hK0 : Kc α ≠ 0 := hK.ne'
  unfold rowFrac icCross gammaOf
  field_simp

-- PG9-HELPERS-BEGIN
/-- `ψ_a(y) = 1/(1+(y/a)^α)` is integrable on `(0,∞)` with integral `a K_α`. -/
private lemma pg9_psi_int {α a : ℝ} (hα1 : 1 < α) (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => 1 / (1 + (y / a) ^ α)) (Ioi 0) ∧
      ∫ y in Ioi (0:ℝ), 1 / (1 + (y / a) ^ α) = a * Kc α := by
  have hai : 0 < a⁻¹ := inv_pos.2 ha
  have e : ∀ y : ℝ, y / a = a⁻¹ * y := fun y => by rw [div_eq_inv_mul]
  simp only [e]
  refine ⟨?_, ?_⟩
  · have := (integrableOn_Ioi_comp_mul_left_iff (fun s : ℝ => 1 / (1 + s ^ α)) 0 hai).2
      (by rw [mul_zero]; exact vg_J_int hα1)
    exact this
  · have := integral_comp_mul_left_Ioi (fun s : ℝ => 1 / (1 + s ^ α)) 0 hai
    rw [mul_zero, vg_J hα1, smul_eq_mul, inv_inv] at this
    exact this

private lemma pg9_psi_sq {α : ℝ} (hα1 : 1 < α) :
    IntegrableOn (fun s : ℝ => (1 / (1 + s ^ α)) ^ 2) (Ioi 0) ∧
      ∫ s in Ioi (0:ℝ), (1 / (1 + s ^ α)) ^ 2 = (α - 1) / α * Kc α := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  have hJi := vg_J_int hα1
  have hJ := vg_J hα1
  have hle : ∀ s ∈ Ioi (0:ℝ), (1 / (1 + s ^ α)) ^ 2 ≤ 1 / (1 + s ^ α) := by
    intro s hs
    have hsa : 0 < s ^ α := Real.rpow_pos_of_pos hs α
    have h1 : 1 / (1 + s ^ α) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h0 : 0 ≤ 1 / (1 + s ^ α) := by positivity
    nlinarith
  have hint : IntegrableOn (fun s : ℝ => (1 / (1 + s ^ α)) ^ 2) (Ioi 0) := by
    refine Integrable.mono' hJi ?_ ?_
    · exact (by fun_prop : Measurable fun s : ℝ => (1 / (1 + s ^ α)) ^ 2).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have h0 : 0 ≤ (1 / (1 + s ^ α)) ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hle s hs
  refine ⟨hint, ?_⟩
  -- derivative of s/(1+s^α)
  set f : ℝ → ℝ := fun s => s / (1 + s ^ α) with hf
  set f' : ℝ → ℝ := fun s => (1 - α) * (1 / (1 + s ^ α)) + α * (1 / (1 + s ^ α)) ^ 2 with hf'
  have hderiv : ∀ s ∈ Ioi (0:ℝ), HasDerivAt f (f' s) s := by
    intro s hs
    have hs0 : (0:ℝ) < s := hs
    have hsa : 0 < s ^ α := Real.rpow_pos_of_pos hs0 α
    have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ α) (α * s ^ (α - 1)) s := by
      simpa using (Real.hasDerivAt_rpow_const (Or.inl hs0.ne') : HasDerivAt (fun x : ℝ => x ^ α) (α * s ^ (α - 1)) s).const_add 1
    have h2 := (hasDerivAt_id s).div h1 (by positivity)
    refine h2.congr_deriv ?_
    simp only [hf', id]
    have e : s ^ (α - 1) * s = s ^ α := by
      rw [← Real.rpow_add_one hs0.ne']; congr 1; ring
    have hp : 0 < 1 + s ^ α := by linarith
    field_simp
    rw [mul_comm s, ← e]
    ring
  have hf'int : IntegrableOn f' (Ioi 0) := (hJi.const_mul (1 - α)).add (hint.const_mul α)
  have hlim : Tendsto f atTop (𝓝 0) := by
    have hb : Tendsto (fun s : ℝ => s ^ (1 - α)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (y := α - 1) (by linarith)).congr (fun s => by congr 1; ring)
    refine squeeze_zero' ?_ ?_ hb
    · filter_upwards [eventually_gt_atTop 0] with s hs
      have : 0 < s ^ α := Real.rpow_pos_of_pos hs α
      simp only [hf]; positivity
    · filter_upwards [eventually_gt_atTop 0] with s hs
      have hsa : 0 < s ^ α := Real.rpow_pos_of_pos hs α
      simp only [hf]
      have : s ^ (1 - α) = s / s ^ α := by
        rw [Real.rpow_sub hs, Real.rpow_one]
      rw [this]
      exact div_le_div_of_nonneg_left hs.le hsa (by linarith)
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    have : ContinuousAt f 0 := by
      refine ContinuousAt.div continuousAt_id ?_ (by simp [Real.zero_rpow hα0.ne'])
      exact continuousAt_const.add (Real.continuousAt_rpow_const 0 α (Or.inr hα0.le))
    exact this.continuousWithinAt
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hf'int hlim
  have h0 : f 0 = 0 := by simp [hf]
  rw [h0, sub_zero] at key
  simp only [hf'] at key
  rw [integral_add (hJi.const_mul (1 - α)) (hint.const_mul α), integral_const_mul, integral_const_mul, hJ] at key
  have : α * ∫ s in Ioi (0:ℝ), (1 / (1 + s ^ α)) ^ 2 = (α - 1) * Kc α := by linarith
  rw [div_mul_eq_mul_div, eq_div_iff hα0.ne']
  linarith

private lemma pg9_psi_prod {α a b : ℝ} (hα1 : 1 < α) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun y : ℝ => 1 / (1 + (y / a) ^ α) * (1 / (1 + (y / b) ^ α))) (Ioi 0) ∧
      ∫ y in Ioi (0:ℝ), 1 / (1 + (y / a) ^ α) * (1 / (1 + (y / b) ^ α)) = Kc α * profT α a b := by
  have hα0 : 0 < α := by linarith
  obtain ⟨hia, hca⟩ := pg9_psi_int hα1 ha
  obtain ⟨hib, hcb⟩ := pg9_psi_int hα1 hb
  have hint : IntegrableOn (fun y : ℝ => 1 / (1 + (y / a) ^ α) * (1 / (1 + (y / b) ^ α))) (Ioi 0) := by
    refine Integrable.mono' hia ?_ ?_
    · exact (by fun_prop : Measurable fun y : ℝ => 1 / (1 + (y / a) ^ α) * (1 / (1 + (y / b) ^ α))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 : (0:ℝ) < y := hy
      have h1 : 0 < (y / b) ^ α := Real.rpow_pos_of_pos (div_pos hy0 hb) α
      have h2 : 0 < (y / a) ^ α := Real.rpow_pos_of_pos (div_pos hy0 ha) α
      have h3 : 1 / (1 + (y / b) ^ α) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have h4 : 0 ≤ 1 / (1 + (y / a) ^ α) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right h4 h3
  refine ⟨hint, ?_⟩
  by_cases hab : a = b
  · subst hab
    have hsq := pg9_psi_sq hα1
    have e : ∀ y : ℝ, 1 / (1 + (y / a) ^ α) * (1 / (1 + (y / a) ^ α)) =
        (fun s : ℝ => (1 / (1 + s ^ α)) ^ 2) (a⁻¹ * y) := fun y => by
      simp only [div_eq_inv_mul, sq]
    simp only [e]
    have hai : 0 < a⁻¹ := inv_pos.2 ha
    have := integral_comp_mul_left_Ioi (fun s : ℝ => (1 / (1 + s ^ α)) ^ 2) 0 hai
    rw [mul_zero, hsq.2, smul_eq_mul, inv_inv] at this
    rw [this]
    unfold profT
    simp only [↓reduceIte]
    field_simp
  · have hne : b ^ α - a ^ α ≠ 0 := by
      intro h
      apply hab
      have : a ^ α = b ^ α := by linarith
      exact ((Real.rpow_left_inj ha.le hb.le hα0.ne').1 this)
    have hpt : ∀ y ∈ Ioi (0:ℝ), 1 / (1 + (y / a) ^ α) * (1 / (1 + (y / b) ^ α)) =
        (b ^ α / (b ^ α - a ^ α)) * (1 / (1 + (y / a) ^ α)) -
          (a ^ α / (b ^ α - a ^ α)) * (1 / (1 + (y / b) ^ α)) := by
      intro y hy
      have hy0 : (0:ℝ) < y := hy
      have h1 : 0 < y ^ α := Real.rpow_pos_of_pos hy0 α
      have h2 : 0 < a ^ α := Real.rpow_pos_of_pos ha α
      have h3 : 0 < b ^ α := Real.rpow_pos_of_pos hb α
      rw [Real.div_rpow hy0.le ha.le, Real.div_rpow hy0.le hb.le]
      field_simp
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub (hia.const_mul _) (hib.const_mul _),
      integral_const_mul, integral_const_mul, hca, hcb]
    unfold profT
    simp only [hab, ↓reduceIte]
    field_simp

private lemma pg9_g_anti {α a b : ℝ} (hα0 : 0 < α) (ha : 0 < a) (hb : 0 < b) :
    AntitoneOn (fun y : ℝ => 1 / (1 + (y / a) ^ α) * (1 / (1 + (y / b) ^ α))) (Ici 0) := by
  intro x hx y hy hxy
  have hx0 : (0:ℝ) ≤ x := hx
  have h1 : (x / a) ^ α ≤ (y / a) ^ α :=
    Real.rpow_le_rpow (div_nonneg hx0 ha.le) (div_le_div_of_nonneg_right hxy ha.le) hα0.le
  have h2 : (x / b) ^ α ≤ (y / b) ^ α :=
    Real.rpow_le_rpow (div_nonneg hx0 hb.le) (div_le_div_of_nonneg_right hxy hb.le) hα0.le
  have p1 : 0 ≤ (x / a) ^ α := Real.rpow_nonneg (div_nonneg hx0 ha.le) α
  have p2 : 0 ≤ (x / b) ^ α := Real.rpow_nonneg (div_nonneg hx0 hb.le) α
  have p3 : 0 ≤ (y / b) ^ α := Real.rpow_nonneg (div_nonneg (hx0.trans hxy) hb.le) α
  simp only
  have e1 : 1 / (1 + (y / a) ^ α) ≤ 1 / (1 + (x / a) ^ α) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have e2 : 1 / (1 + (y / b) ^ α) ≤ 1 / (1 + (x / b) ^ α) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  exact mul_le_mul e1 e2 (div_nonneg zero_le_one (by linarith)) (div_nonneg zero_le_one (by linarith))

private lemma pg9_riem_up {α a b : ℝ} (hα1 : 1 < α) (ha : 0 < a) (hb : 0 < b) (N B : ℕ)
    (hB : 0 < B) :
    (B : ℝ)⁻¹ * ∑ j : Fin N, (1 / (1 + ((((j : ℕ) : ℝ) + 1) / B / a) ^ α) *
        (1 / (1 + ((((j : ℕ) : ℝ) + 1) / B / b) ^ α))) ≤ Kc α * profT α a b := by
  have hα0 : 0 < α := by linarith
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  set g : ℝ → ℝ := fun y => 1 / (1 + (y / a) ^ α) * (1 / (1 + (y / b) ^ α)) with hg
  obtain ⟨hint, hval⟩ := pg9_psi_prod (α := α) hα1 ha hb
  have hgnn : ∀ y, 0 ≤ y → 0 ≤ g y := fun y hy => by
    have := Real.rpow_nonneg (div_nonneg hy ha.le) α
    have := Real.rpow_nonneg (div_nonneg hy hb.le) α
    simp only [hg]; positivity
  have hanti := pg9_g_anti (α := α) hα0 ha hb
  have hf : AntitoneOn (fun x : ℝ => g (x / B)) (Icc 0 (0 + (N:ℝ))) := by
    intro x hx y hy hxy
    exact hanti (by simp only [mem_Ici]; exact div_nonneg hx.1 hBr.le)
      (by simp only [mem_Ici]; exact div_nonneg hy.1 hBr.le) (div_le_div_of_nonneg_right hxy hBr.le)
  have h1 := hf.sum_le_integral
  rw [Fin.sum_univ_eq_sum_range (fun i => g (((i:ℝ) + 1) / B)) N]
  have h2 : ∑ i ∈ Finset.range N, (fun x : ℝ => g (x / B)) (0 + ((i + 1 : ℕ) : ℝ)) =
      ∑ i ∈ Finset.range N, g (((i:ℝ) + 1) / B) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [zero_add]; push_cast; rfl
  rw [h2] at h1
  rw [intervalIntegral.integral_comp_div (fun y => g y) hBr.ne'] at h1
  simp only [zero_add, zero_div, smul_eq_mul] at h1
  have h3 : ∫ y in (0:ℝ)..(N:ℝ) / B, g y ≤ ∫ y in Ioi (0:ℝ), g y := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    refine setIntegral_mono_set hint ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact hgnn y hy.le
    · exact (Ioc_subset_Ioi_self).eventuallyLE
  have : (B:ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (((i:ℝ) + 1) / B) ≤ ∫ y in Ioi (0:ℝ), g y := by
    rw [inv_mul_le_iff₀ hBr]
    calc _ ≤ B * ∫ y in (0:ℝ)..(N:ℝ) / B, g y := h1
      _ ≤ B * ∫ y in Ioi (0:ℝ), g y := mul_le_mul_of_nonneg_left h3 hBr.le
  rw [hval] at this
  exact this
private lemma pg9_riem_low {α a b : ℝ} (hα1 : 1 < α) (ha : 0 < a) (hb : 0 < b) (N B : ℕ)
    (hB : 0 < B) :
    Kc α * profT α a b - (a * b) ^ α * ((((N : ℝ) + 1) / B) ^ (1 - 2 * α) / (2 * α - 1)) - 1 / B ≤
      (B : ℝ)⁻¹ * ∑ j : Fin N, (1 / (1 + ((((j : ℕ) : ℝ) + 1) / B / a) ^ α) *
        (1 / (1 + ((((j : ℕ) : ℝ) + 1) / B / b) ^ α))) := by
  have hα0 : 0 < α := by linarith
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  set g : ℝ → ℝ := fun y => 1 / (1 + (y / a) ^ α) * (1 / (1 + (y / b) ^ α)) with hg
  obtain ⟨hint, hval⟩ := pg9_psi_prod (α := α) hα1 ha hb
  have hgnn : ∀ y, 0 ≤ y → 0 ≤ g y := fun y hy => by
    have := Real.rpow_nonneg (div_nonneg hy ha.le) α
    have := Real.rpow_nonneg (div_nonneg hy hb.le) α
    simp only [hg]; positivity
  have hg1 : ∀ y, 0 ≤ y → g y ≤ 1 := fun y hy => by
    have p1 := Real.rpow_nonneg (div_nonneg hy ha.le) α
    have p2 := Real.rpow_nonneg (div_nonneg hy hb.le) α
    have e1 : 1 / (1 + (y / a) ^ α) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have e2 : 1 / (1 + (y / b) ^ α) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have := mul_le_mul e1 e2 (div_nonneg zero_le_one (by linarith)) zero_le_one
    simpa [hg] using this
  have hanti := pg9_g_anti (α := α) hα0 ha hb
  set T0 : ℝ := ((N : ℝ) + 1) / B with hT0
  have hBT : 1 / (B:ℝ) ≤ T0 := by
    rw [hT0]; exact div_le_div_of_nonneg_right (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]) hBr.le
  have hT0pos : 0 < T0 := lt_of_lt_of_le (by positivity) hBT
  -- discrete sum vs integral
  have hf : AntitoneOn (fun x : ℝ => g (x / B)) (Icc 1 (1 + (N:ℝ))) := by
    intro x hx y hy hxy
    exact hanti (by simp only [mem_Ici]; exact div_nonneg (by linarith [hx.1]) hBr.le)
      (by simp only [mem_Ici]; exact div_nonneg (by linarith [hy.1]) hBr.le) (div_le_div_of_nonneg_right hxy hBr.le)
  have h1 := hf.integral_le_sum
  rw [Fin.sum_univ_eq_sum_range (fun i => g (((i:ℝ) + 1) / B)) N]
  have h2 : ∑ i ∈ Finset.range N, (fun x : ℝ => g (x / B)) (1 + (i : ℝ)) =
      ∑ i ∈ Finset.range N, g (((i:ℝ) + 1) / B) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only; rw [add_comm]
  rw [h2] at h1
  rw [intervalIntegral.integral_comp_div (fun y => g y) hBr.ne'] at h1
  simp only [smul_eq_mul] at h1
  have hupper : (1 + (N:ℝ)) / B = T0 := by rw [hT0, add_comm]
  rw [hupper] at h1
  -- split the half-line integral
  have hgi : ∀ s : Set ℝ, s ⊆ Ioi 0 → IntegrableOn g s := fun s hs => hint.mono_set hs
  have hsplit1 : ∫ y in Ioi (0:ℝ), g y = (∫ y in Ioc (0:ℝ) (1 / B), g y) + ∫ y in Ioi (1 / (B:ℝ)), g y := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi
      (hgi _ (Ioc_subset_Ioi_self)) (hgi _ (Ioi_subset_Ioi (by positivity)))]
    rw [Ioc_union_Ioi_eq_Ioi (by positivity)]
  have hsplit2 : ∫ y in Ioi (1 / (B:ℝ)), g y = (∫ y in Ioc (1 / (B:ℝ)) T0, g y) + ∫ y in Ioi T0, g y := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi
      (hgi _ (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by positivity))))
      (hgi _ (Ioi_subset_Ioi hT0pos.le))]
    rw [Ioc_union_Ioi_eq_Ioi hBT]
  have hA : ∫ y in Ioc (0:ℝ) (1 / B), g y ≤ 1 / B := by
    have : ∫ y in Ioc (0:ℝ) (1 / B), g y ≤ ∫ y in Ioc (0:ℝ) (1 / B), (1:ℝ) := by
      refine setIntegral_mono_on (hgi _ Ioc_subset_Ioi_self) (integrableOn_const (by simp)) measurableSet_Ioc ?_
      intro y hy; exact hg1 y hy.1.le
    simpa using this
  have hC : ∫ y in Ioi T0, g y ≤ (a * b) ^ α * (T0 ^ (1 - 2 * α) / (2 * α - 1)) := by
    have hrint : IntegrableOn (fun y : ℝ => y ^ (-(2 * α))) (Ioi T0) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hT0pos
    have hrv : ∫ y in Ioi T0, y ^ (-(2 * α)) = T0 ^ (1 - 2 * α) / (2 * α - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) hT0pos]
      have : -(2 * α) + 1 = 1 - 2 * α := by ring
      rw [this]
      rw [show (2 * α - 1) = -(1 - 2 * α) by ring, div_neg, neg_div]
    have := setIntegral_mono_on (hgi _ (Ioi_subset_Ioi hT0pos.le)) (hrint.const_mul ((a * b) ^ α))
      measurableSet_Ioi (fun y hy => by
        have hy0 : (0:ℝ) < y := lt_trans hT0pos hy
        have hya : 0 < (y / a) ^ α := Real.rpow_pos_of_pos (div_pos hy0 ha) α
        have hyb : 0 < (y / b) ^ α := Real.rpow_pos_of_pos (div_pos hy0 hb) α
        have e1 : 1 / (1 + (y / a) ^ α) ≤ (a / y) ^ α := by
          have : (a / y) ^ α = ((y / a) ^ α)⁻¹ := by
            rw [← Real.inv_rpow (div_pos hy0 ha).le, inv_div]
          rw [this, ← one_div]
          exact one_div_le_one_div_of_le hya (by linarith)
        have e2 : 1 / (1 + (y / b) ^ α) ≤ (b / y) ^ α := by
          have : (b / y) ^ α = ((y / b) ^ α)⁻¹ := by
            rw [← Real.inv_rpow (div_pos hy0 hb).le, inv_div]
          rw [this, ← one_div]
          exact one_div_le_one_div_of_le hyb (by linarith)
        have e3 : (a / y) ^ α * (b / y) ^ α = (a * b) ^ α * y ^ (-(2 * α)) := by
          have hyp : 0 < y ^ α := Real.rpow_pos_of_pos hy0 α
          rw [Real.div_rpow ha.le hy0.le, Real.div_rpow hb.le hy0.le, Real.mul_rpow ha.le hb.le,
            Real.rpow_neg hy0.le, two_mul, Real.rpow_add hy0]
          field_simp
        calc g y ≤ (a / y) ^ α * (b / y) ^ α :=
              mul_le_mul e1 e2 (div_nonneg zero_le_one (by linarith)) (by positivity)
          _ = (a * b) ^ α * y ^ (-(2 * α)) := e3)
    rw [integral_const_mul, hrv] at this
    exact this
  have hmid : ∫ y in Ioc (1 / (B:ℝ)) T0, g y = ∫ y in (1 / (B:ℝ))..T0, g y :=
    (intervalIntegral.integral_of_le hBT).symm
  have hI : ∫ y in Ioi (0:ℝ), g y = Kc α * profT α a b := hval
  have hlow : (B:ℝ) * ∫ y in (1 / (B:ℝ))..T0, g y ≤ ∑ i ∈ Finset.range N, g (((i:ℝ) + 1) / B) := h1
  have h3 : ∫ y in (1 / (B:ℝ))..T0, g y ≤ (B:ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (((i:ℝ) + 1) / B) := by
    rw [le_inv_mul_iff₀ hBr]; exact hlow
  linarith

private lemma pg9_plSpec_pos {α c : ℝ} (hc : 0 < c) (N : ℕ) (i : Fin N) : 0 < plSpec α c N i := by
  unfold plSpec
  have : (0:ℝ) < ((i : ℕ) : ℝ) + 1 := by positivity
  exact mul_pos hc (Real.rpow_pos_of_pos this _)

private lemma pg9_lam_pos {α c : ℝ} {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) {m : ℝ}
    (hm : m ∈ Ioo 0 (gammaOf N B)) : 0 < partLam B (plSpec α c N) m :=
  (def_app_pl_participation_bij (plSpec α c N) hB hN (pg9_plSpec_pos hc N)).2.1.mapsTo hm

private lemma pg9_partF_eq {α c : ℝ} {N B : ℕ} (hα0 : 0 < α) (hB : 0 < B) (hc : 0 < c)
    (j : Fin N) {m : ℝ} (hΛ : 0 < partLam B (plSpec α c N) m) :
    partF B (plSpec α c N) j m =
      1 / (1 + ((((j : ℕ) : ℝ) + 1) / B /
        ((c * partLam B (plSpec α c N) m) ^ (1 / α) / B)) ^ α) := by
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  set Λ := partLam B (plSpec α c N) m with hΛdef
  set s := c * Λ with hs
  have hs0 : 0 < s := mul_pos hc hΛ
  have hj : (0:ℝ) < ((j : ℕ) : ℝ) + 1 := by positivity
  have hsr : 0 < s ^ (1 / α) := Real.rpow_pos_of_pos hs0 _
  have e1 : (((j : ℕ) : ℝ) + 1) / B / (s ^ (1 / α) / B) = (((j : ℕ) : ℝ) + 1) / s ^ (1 / α) := by
    field_simp
  rw [e1, Real.div_rpow hj.le hsr.le, ← Real.rpow_mul hs0.le, one_div_mul_cancel hα0.ne',
    Real.rpow_one]
  have hja : 0 < (((j : ℕ) : ℝ) + 1) ^ α := Real.rpow_pos_of_pos hj α
  have hμ : plSpec α c N j = c * (((j : ℕ) : ℝ) + 1) ^ (-α) := rfl
  unfold partF
  rw [hμ, Real.rpow_neg hj.le, ← hΛdef]
  simp only [hs]
  field_simp
  ring

private lemma pg9_psi_nonneg {α a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    0 ≤ 1 / (1 + (y / a) ^ α) := by
  have := Real.rpow_nonneg (div_nonneg hy ha.le) α
  positivity

private lemma pg9_psi_mono {α a a' y : ℝ} (hα0 : 0 < α) (ha : 0 < a) (haa : a ≤ a') (hy : 0 ≤ y) :
    1 / (1 + (y / a) ^ α) ≤ 1 / (1 + (y / a') ^ α) := by
  have h1 : (y / a') ^ α ≤ (y / a) ^ α :=
    Real.rpow_le_rpow (div_nonneg hy (ha.le.trans haa)) (div_le_div_of_nonneg_left hy ha haa) hα0.le
  have h2 : 0 ≤ (y / a') ^ α := Real.rpow_nonneg (div_nonneg hy (ha.le.trans haa)) α
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

private lemma pg9_TN_bounds {α c : ℝ} (hα1 : 1 < α) {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) {m₁ m₂ : ℝ} (hm₁ : m₁ ∈ Ioo 0 (gammaOf N B)) (hm₂ : m₂ ∈ Ioo 0 (gammaOf N B))
    {a₁ a₂ A₁ A₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (h₁ : a₁ ≤ (c * partLam B (plSpec α c N) m₁) ^ (1 / α) / B)
    (h₂ : a₂ ≤ (c * partLam B (plSpec α c N) m₂) ^ (1 / α) / B)
    (h₁' : (c * partLam B (plSpec α c N) m₁) ^ (1 / α) / B ≤ A₁)
    (h₂' : (c * partLam B (plSpec α c N) m₂) ^ (1 / α) / B ≤ A₂) :
    Kc α * profT α a₁ a₂ - (a₁ * a₂) ^ α * ((((N : ℝ) + 1) / B) ^ (1 - 2 * α) / (2 * α - 1)) - 1 / B ≤
        TNpart B (plSpec α c N) m₁ m₂ ∧
      TNpart B (plSpec α c N) m₁ m₂ ≤ Kc α * profT α A₁ A₂ := by
  have hα0 : 0 < α := by linarith
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hΛ₁ := pg9_lam_pos (α := α) hN hB hc hm₁
  have hΛ₂ := pg9_lam_pos (α := α) hN hB hc hm₂
  set a₁' := (c * partLam B (plSpec α c N) m₁) ^ (1 / α) / B with hdef₁
  set a₂' := (c * partLam B (plSpec α c N) m₂) ^ (1 / α) / B with hdef₂
  have hp₁ : 0 < a₁' := lt_of_lt_of_le ha₁ h₁
  have hp₂ : 0 < a₂' := lt_of_lt_of_le ha₂ h₂
  have hTN : TNpart B (plSpec α c N) m₁ m₂ = (B : ℝ)⁻¹ * ∑ j : Fin N,
      (1 / (1 + ((((j : ℕ) : ℝ) + 1) / B / a₁') ^ α) *
        (1 / (1 + ((((j : ℕ) : ℝ) + 1) / B / a₂') ^ α))) := by
    unfold TNpart
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pg9_partF_eq hα0 hB hc j hΛ₁, pg9_partF_eq hα0 hB hc j hΛ₂]
  rw [hTN]
  constructor
  · refine le_trans (pg9_riem_low hα1 ha₁ ha₂ N B hB) ?_
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)
    have hy : 0 ≤ (((j : ℕ) : ℝ) + 1) / B := by positivity
    exact mul_le_mul (pg9_psi_mono hα0 ha₁ h₁ hy) (pg9_psi_mono hα0 ha₂ h₂ hy)
      (pg9_psi_nonneg ha₂ hy) (pg9_psi_nonneg hp₁ hy)
  · refine le_trans ?_ (pg9_riem_up hα1 (hp₁.trans_le h₁') (hp₂.trans_le h₂') N B hB)
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)
    have hy : 0 ≤ (((j : ℕ) : ℝ) + 1) / B := by positivity
    exact mul_le_mul (pg9_psi_mono hα0 hp₁ h₁' hy) (pg9_psi_mono hα0 hp₂ h₂' hy)
      (pg9_psi_nonneg hp₂ hy) (pg9_psi_nonneg (hp₁.trans_le h₁') hy)

private lemma pg9_profT_lb {α u v : ℝ} (hα1 : 1 < α) (hu : 0 < u) (hv : 0 < v) :
    min u v / (4 * Kc α) ≤ profT α u v := by
  have hK := vg_K_pos hα1
  have hα0 : 0 < α := by linarith
  obtain ⟨hint, hval⟩ := pg9_psi_prod (α := α) hα1 hu hv
  set m := min u v with hm
  have hm0 : 0 < m := lt_min hu hv
  have hmu : m ≤ u := min_le_left _ _
  have hmv : m ≤ v := min_le_right _ _
  have hlow : ∫ y in Ioc (0:ℝ) m, (1:ℝ) / 4 ≤
      ∫ y in Ioi (0:ℝ), 1 / (1 + (y / u) ^ α) * (1 / (1 + (y / v) ^ α)) := by
    have h1 : ∫ y in Ioc (0:ℝ) m, (1:ℝ) / 4 ≤
        ∫ y in Ioc (0:ℝ) m, 1 / (1 + (y / u) ^ α) * (1 / (1 + (y / v) ^ α)) := by
      refine setIntegral_mono_on (integrableOn_const (by simp)) (hint.mono_set Ioc_subset_Ioi_self)
        measurableSet_Ioc ?_
      intro y hy
      have hy0 : (0:ℝ) < y := hy.1
      have e : ∀ w : ℝ, 0 < w → m ≤ w → 1 / 2 ≤ 1 / (1 + (y / w) ^ α) := by
        intro w hw hmw
        have : (y / w) ^ α ≤ 1 := by
          apply Real.rpow_le_one (div_nonneg hy0.le hw.le) _ hα0.le
          rw [div_le_one hw]; exact hy.2.trans hmw
        have h0 : 0 ≤ (y / w) ^ α := Real.rpow_nonneg (div_nonneg hy0.le hw.le) α
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
      have := mul_le_mul (e u hu hmu) (e v hv hmv) (by norm_num) (pg9_psi_nonneg hu hy0.le)
      calc (1:ℝ) / 4 = 1 / 2 * (1 / 2) := by norm_num
        _ ≤ _ := this
    refine h1.trans (setIntegral_mono_set hint ?_ (Ioc_subset_Ioi_self).eventuallyLE)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg (pg9_psi_nonneg hu (le_of_lt hy)) (pg9_psi_nonneg hv (le_of_lt hy))
  rw [hval] at hlow
  simp only [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul, sub_zero,
    max_eq_left hm0.le] at hlow
  rw [div_le_iff₀ (by positivity)]
  nlinarith

private lemma pg9_scale_bounds {α s B' x ε : ℝ} (hα0 : 0 < α) (hB' : 0 < B') (hx : 0 < x)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hlo : (1 - ε) * (B' * x) ^ α ≤ s) (hhi : s ≤ (1 + ε) * (B' * x) ^ α) :
    (1 - ε) ^ (1 / α) * x ≤ s ^ (1 / α) / B' ∧ s ^ (1 / α) / B' ≤ (1 + ε) ^ (1 / α) * x := by
  have hBx : 0 < B' * x := mul_pos hB' hx
  have hpow : ∀ y : ℝ, 0 ≤ y → ((B' * x) ^ α * y) ^ (1 / α) = B' * x * y ^ (1 / α) := by
    intro y hy
    rw [Real.mul_rpow (Real.rpow_nonneg hBx.le α) hy, ← Real.rpow_mul hBx.le,
      mul_one_div_cancel hα0.ne', Real.rpow_one]
  have h1 : (1 - ε) ^ (1 / α) * (B' * x) ≤ s ^ (1 / α) := by
    have := Real.rpow_le_rpow (mul_nonneg (by linarith) (Real.rpow_nonneg hBx.le α)) hlo
      (one_div_pos.2 hα0).le
    rw [mul_comm (1 - ε), hpow _ (by linarith)] at this
    linarith [this]
  have h2 : s ^ (1 / α) ≤ (1 + ε) ^ (1 / α) * (B' * x) := by
    have hs0 : 0 ≤ s := by
      have : 0 ≤ (1 - ε) * (B' * x) ^ α := mul_nonneg (by linarith) (Real.rpow_nonneg hBx.le α)
      linarith
    have := Real.rpow_le_rpow hs0 hhi (one_div_pos.2 hα0).le
    rw [mul_comm (1 + ε), hpow _ (by linarith)] at this
    linarith [this]
  constructor
  · rw [le_div_iff₀ hB']; nlinarith
  · rw [div_le_iff₀ hB']; nlinarith

private lemma pg9_uv_bd {α u v : ℝ} (hα1 : 1 < α) (hu : 0 < u) (hv : 0 < v) :
    (u * v) ^ α ≤ min u v * max u v ^ (2 * α - 1) := by
  have hα0 : 0 < α := by linarith
  have hp : 0 < min u v := lt_min hu hv
  have hq : 0 < max u v := lt_max_of_lt_left hu
  have hpq : min u v ≤ max u v := min_le_max
  rw [← min_mul_max u v, Real.mul_rpow hp.le hq.le]
  have e1 : min u v ^ α = min u v * min u v ^ (α - 1) := by
    rw [Real.rpow_sub_one hp.ne']; field_simp
  have e2 : max u v ^ (2 * α - 1) = max u v ^ α * max u v ^ (α - 1) := by
    rw [← Real.rpow_add hq]; congr 1; ring
  have h3 : min u v ^ (α - 1) ≤ max u v ^ (α - 1) := Real.rpow_le_rpow hp.le hpq (by linarith)
  rw [e1, e2]
  have : 0 ≤ max u v ^ α := Real.rpow_nonneg hq.le α
  nlinarith [mul_le_mul_of_nonneg_left h3 (mul_nonneg hp.le this)]

private lemma pg9_E_det {α u v γ B' : ℝ} (hα1 : 1 < α) (hu : 0 < u) (hv : 0 < v) (hγ : 0 < γ)
    (hB' : 0 < B') :
    ((u * v / Kc α ^ 2) ^ α * (γ ^ (1 - 2 * α) / (2 * α - 1)) + 1 / B') / profT α u v ≤
      4 * Kc α * ((max u v / γ) ^ (2 * α - 1) / ((Kc α ^ 2) ^ α * (2 * α - 1)) +
        1 / (B' * min u v)) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  have hp : 0 < min u v := lt_min hu hv
  have hq : 0 < max u v := lt_max_of_lt_left hu
  have hlb := pg9_profT_lb hα1 hu hv
  have hT : 0 < profT α u v := lt_of_lt_of_le (by positivity) hlb
  have h2α : 0 < 2 * α - 1 := by linarith
  have hK2 : 0 < (Kc α ^ 2) ^ α := Real.rpow_pos_of_pos (by positivity) α
  set p := min u v with hpdef
  set q := max u v with hqdef
  have hA0 : 0 ≤ (u * v / Kc α ^ 2) ^ α * (γ ^ (1 - 2 * α) / (2 * α - 1)) + 1 / B' := by
    have := Real.rpow_nonneg (div_nonneg (mul_pos hu hv).le (by positivity : (0:ℝ) ≤ Kc α ^ 2)) α
    have := Real.rpow_nonneg hγ.le (1 - 2 * α)
    positivity
  rw [div_le_iff₀ hT]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hlb (by positivity))
  have hA : (u * v / Kc α ^ 2) ^ α * (γ ^ (1 - 2 * α) / (2 * α - 1)) ≤
      p * ((q / γ) ^ (2 * α - 1) / ((Kc α ^ 2) ^ α * (2 * α - 1))) := by
    rw [Real.div_rpow (mul_pos hu hv).le (by positivity), Real.div_rpow hq.le hγ.le]
    have h1 := pg9_uv_bd hα1 hu hv
    have e : γ ^ (1 - 2 * α) = (γ ^ (2 * α - 1))⁻¹ := by
      rw [← Real.rpow_neg hγ.le]; congr 1; ring
    have hγp : 0 < γ ^ (2 * α - 1) := Real.rpow_pos_of_pos hγ _
    rw [e]
    have hq2 : 0 ≤ q ^ (2 * α - 1) := Real.rpow_nonneg hq.le _
    calc (u * v) ^ α / (Kc α ^ 2) ^ α * ((γ ^ (2 * α - 1))⁻¹ / (2 * α - 1))
        = (u * v) ^ α * (1 / ((Kc α ^ 2) ^ α * (2 * α - 1) * γ ^ (2 * α - 1))) := by
          field_simp
      _ ≤ (p * q ^ (2 * α - 1)) * (1 / ((Kc α ^ 2) ^ α * (2 * α - 1) * γ ^ (2 * α - 1))) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = p * (q ^ (2 * α - 1) / γ ^ (2 * α - 1) / ((Kc α ^ 2) ^ α * (2 * α - 1))) := by
          field_simp
  have : 1 / B' = p * (1 / (B' * p)) := by field_simp
  calc _ ≤ p * ((q / γ) ^ (2 * α - 1) / ((Kc α ^ 2) ^ α * (2 * α - 1))) + p * (1 / (B' * p)) := by
        linarith
    _ = _ := by field_simp

private lemma pg9_cl_bounds {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (m : ℕ → ℝ)
    (hBm : Tendsto (fun n => ((B n : ℕ) : ℝ) * m n) atTop atTop)
    (hmγ : Tendsto (fun n => m n / gammaOf (N n) (B n)) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (1 - ε) * (((B n : ℕ) : ℝ) * m n / Kc α) ^ α ≤ c n * partLam (B n) (plSpec α (c n) (N n)) (m n) ∧
      c n * partLam (B n) (plSpec α (c n) (N n)) (m n) ≤ (1 + ε) * (((B n : ℕ) : ℝ) * m n / Kc α) ^ α := by
  have hK := vg_K_pos hα1
  have h := lem_app_pl_finite_inverse_iv_i R hα1 m hBm hmγ
  have hBm1 : ∀ᶠ n in atTop, (1:ℝ) ≤ ((B n : ℕ) : ℝ) * m n := hBm.eventually_ge_atTop 1
  have hg : ∀ᶠ n in atTop, (((B n : ℕ) : ℝ) * m n / Kc α) ^ α ≠ 0 := by
    filter_upwards [hBm1] with n hn
    exact (Real.rpow_pos_of_pos (div_pos (by linarith) hK) α).ne'
  have hlim := (isEquivalent_iff_tendsto_one hg).1 h
  have h1 := (tendsto_order.1 hlim).1 (1 - ε) (by linarith)
  have h2 := (tendsto_order.1 hlim).2 (1 + ε) (by linarith)
  filter_upwards [h1, h2, hg, hBm1] with n a b g0 hB1
  have gp : 0 < (((B n : ℕ) : ℝ) * m n / Kc α) ^ α :=
    Real.rpow_pos_of_pos (div_pos (by linarith) hK) α
  simp only [Pi.div_apply] at a b
  rw [lt_div_iff₀ gp] at a
  rw [div_lt_iff₀ gp] at b
  exact ⟨a.le, b.le⟩

private lemma pg9_E_lim {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (u v : ℕ → ℝ)
    (hBu : Tendsto (fun n => ((B n : ℕ) : ℝ) * u n) atTop atTop)
    (hBv : Tendsto (fun n => ((B n : ℕ) : ℝ) * v n) atTop atTop)
    (huγ : Tendsto (fun n => u n / gammaOf (N n) (B n)) atTop (𝓝 0))
    (hvγ : Tendsto (fun n => v n / gammaOf (N n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => 4 * Kc α * ((max (u n) (v n) / gammaOf (N n) (B n)) ^ (2 * α - 1) /
      ((Kc α ^ 2) ^ α * (2 * α - 1)) + 1 / (((B n : ℕ) : ℝ) * min (u n) (v n)))) atTop (𝓝 0) := by
  have hα0 : 0 < α := by linarith
  have h2α : 0 < 2 * α - 1 := by linarith
  have h1 : Tendsto (fun n => max (u n) (v n) / gammaOf (N n) (B n)) atTop (𝓝 0) := by
    have := huγ.max hvγ
    simp only [max_self] at this
    refine this.congr (fun n => ?_)
    have hγ : 0 < gammaOf (N n) (B n) := by
      unfold gammaOf
      exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
    simp only [div_eq_mul_inv]
    rw [max_mul_of_nonneg _ _ (inv_nonneg.2 hγ.le)]
  have h2 : Tendsto (fun n => (max (u n) (v n) / gammaOf (N n) (B n)) ^ (2 * α - 1)) atTop (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ => x ^ (2 * α - 1)) 0 :=
      Real.continuousAt_rpow_const 0 (2 * α - 1) (Or.inr h2α.le)
    have := hc.tendsto.comp h1
    rwa [Real.zero_rpow h2α.ne'] at this
  have h3 : Tendsto (fun n => ((B n : ℕ) : ℝ) * min (u n) (v n)) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hBu.eventually_ge_atTop b, hBv.eventually_ge_atTop b] with n a b'
    rw [mul_min_of_nonneg _ _ (Nat.cast_nonneg (B n))]
    exact le_min a b'
  have h4 : Tendsto (fun n => 1 / (((B n : ℕ) : ℝ) * min (u n) (v n))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h3
  have := ((h2.div_const ((Kc α ^ 2) ^ α * (2 * α - 1))).add h4).const_mul (4 * Kc α)
  simpa using this

private lemma pg9_TN_ratio {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (u v : ℕ → ℝ)
    (hu0 : ∀ n, 0 < u n) (hv0 : ∀ n, 0 < v n)
    (hBu : Tendsto (fun n => ((B n : ℕ) : ℝ) * u n) atTop atTop)
    (hBv : Tendsto (fun n => ((B n : ℕ) : ℝ) * v n) atTop atTop)
    (huγ : Tendsto (fun n => u n / gammaOf (N n) (B n)) atTop (𝓝 0))
    (hvγ : Tendsto (fun n => v n / gammaOf (N n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => TNpart (B n) (plSpec α (c n) (N n)) (u n) (v n) / profT α (u n) (v n))
      atTop (𝓝 1) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  have hγ : ∀ n, 0 < gammaOf (N n) (B n) := fun n => by
    unfold gammaOf
    exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
  have hBr : ∀ n, (0:ℝ) < (B n : ℝ) := fun n => by exact_mod_cast R.hBpos n
  have hTpos : ∀ n, 0 < profT α (u n) (v n) := fun n =>
    lt_of_lt_of_le (div_pos (lt_min (hu0 n) (hv0 n)) (by positivity)) (pg9_profT_lb hα1 (hu0 n) (hv0 n))
  have hElim := pg9_E_lim R hα1 u v hBu hBv huγ hvγ
  have hin : ∀ᶠ n in atTop, u n ∈ Ioo 0 (gammaOf (N n) (B n)) ∧ v n ∈ Ioo 0 (gammaOf (N n) (B n)) := by
    filter_upwards [(tendsto_order.1 huγ).2 1 one_pos, (tendsto_order.1 hvγ).2 1 one_pos] with n a b
    rw [div_lt_one (hγ n)] at a b
    exact ⟨⟨hu0 n, a⟩, ⟨hv0 n, b⟩⟩
  -- common ε-bounds
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n in atTop,
      TNpart (B n) (plSpec α (c n) (N n)) (u n) (v n) ≤ (1 + ε) ^ (1 / α) * profT α (u n) (v n) ∧
      (1 - ε) ^ (1 / α) * profT α (u n) (v n) -
        4 * Kc α * ((max (u n) (v n) / gammaOf (N n) (B n)) ^ (2 * α - 1) /
          ((Kc α ^ 2) ^ α * (2 * α - 1)) + 1 / (((B n : ℕ) : ℝ) * min (u n) (v n))) *
          profT α (u n) (v n) ≤ TNpart (B n) (plSpec α (c n) (N n)) (u n) (v n) := by
    intro ε hε0 hε1
    filter_upwards [pg9_cl_bounds R hα1 u hBu huγ hε0, pg9_cl_bounds R hα1 v hBv hvγ hε0, hin]
      with n hu hv hmem
    have hNpos := R.hNpos n
    have hBpos := R.hBpos n
    have hcpos := R.hcpos n
    obtain ⟨hmu, hmv⟩ := hmem
    have hxu : 0 < u n / Kc α := div_pos (hu0 n) hK
    have hxv : 0 < v n / Kc α := div_pos (hv0 n) hK
    have e1 : ((B n : ℕ) : ℝ) * (u n / Kc α) = ((B n : ℕ) : ℝ) * u n / Kc α := by ring
    have e2 : ((B n : ℕ) : ℝ) * (v n / Kc α) = ((B n : ℕ) : ℝ) * v n / Kc α := by ring
    obtain ⟨su1, su2⟩ := pg9_scale_bounds (s := c n * partLam (B n) (plSpec α (c n) (N n)) (u n)) hα0 (hBr n) hxu hε0 hε1 (by rw [e1]; exact hu.1) (by rw [e1]; exact hu.2)
    obtain ⟨sv1, sv2⟩ := pg9_scale_bounds (s := c n * partLam (B n) (plSpec α (c n) (N n)) (v n)) hα0 (hBr n) hxv hε0 hε1 (by rw [e2]; exact hv.1) (by rw [e2]; exact hv.2)
    have hθ1 : 0 < (1 - ε) ^ (1 / α) := Real.rpow_pos_of_pos (by linarith) _
    obtain ⟨hlo, hhi⟩ := pg9_TN_bounds hα1 hNpos hBpos hcpos hmu hmv
      (a₁ := (1 - ε) ^ (1 / α) * (u n / Kc α)) (a₂ := (1 - ε) ^ (1 / α) * (v n / Kc α))
      (A₁ := (1 + ε) ^ (1 / α) * (u n / Kc α)) (A₂ := (1 + ε) ^ (1 / α) * (v n / Kc α))
      (mul_pos hθ1 hxu) (mul_pos hθ1 hxv) su1 sv1 su2 sv2
    constructor
    · refine hhi.trans (le_of_eq ?_)
      have e : ∀ x : ℝ, (1 + ε) ^ (1 / α) * (x / Kc α) = ((1 + ε) ^ (1 / α) / Kc α) * x := fun x => by ring
      rw [e, e, vz_T_hom (div_pos (Real.rpow_pos_of_pos (by linarith) _) hK) (hu0 n) (hv0 n)]
      field_simp
    · -- lower
      have e : ∀ x : ℝ, (1 - ε) ^ (1 / α) * (x / Kc α) = ((1 - ε) ^ (1 / α) / Kc α) * x := fun x => by ring
      rw [e, e, vz_T_hom (div_pos hθ1 hK) (hu0 n) (hv0 n)] at hlo
      have hEd := pg9_E_det hα1 (hu0 n) (hv0 n) (hγ n) (hBr n)
      have hT := hTpos n
      have htail : ((1 - ε) ^ (1 / α) / Kc α * u n * ((1 - ε) ^ (1 / α) / Kc α * v n)) ^ α *
          (((((N n : ℕ) : ℝ) + 1) / (B n : ℝ)) ^ (1 - 2 * α) / (2 * α - 1)) ≤
          (u n * v n / Kc α ^ 2) ^ α * (gammaOf (N n) (B n) ^ (1 - 2 * α) / (2 * α - 1)) := by
        have h2α : 0 < 2 * α - 1 := by linarith
        have hθ : (1 - ε) ^ (1 / α) ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) (one_div_pos.2 hα0).le
        have hg1 : gammaOf (N n) (B n) ≤ (((N n : ℕ) : ℝ) + 1) / (B n : ℝ) := by
          unfold gammaOf
          exact div_le_div_of_nonneg_right (by linarith) (hBr n).le
        have hA : (1 - ε) ^ (1 / α) / Kc α * u n * ((1 - ε) ^ (1 / α) / Kc α * v n) ≤
            u n * v n / Kc α ^ 2 := by
          have : (1 - ε) ^ (1 / α) / Kc α * u n * ((1 - ε) ^ (1 / α) / Kc α * v n) =
              ((1 - ε) ^ (1 / α)) ^ 2 * (u n * v n / Kc α ^ 2) := by ring
          rw [this]
          have h0 : 0 ≤ u n * v n / Kc α ^ 2 := by have := hu0 n; have := hv0 n; positivity
          have : ((1 - ε) ^ (1 / α)) ^ 2 ≤ 1 := by nlinarith
          nlinarith
        have hP : 0 ≤ (1 - ε) ^ (1 / α) / Kc α * u n * ((1 - ε) ^ (1 / α) / Kc α * v n) := by
          have := hu0 n; have := hv0 n; positivity
        have h1 := Real.rpow_le_rpow hP hA hα0.le
        have h2 : ((((N n : ℕ) : ℝ) + 1) / (B n : ℝ)) ^ (1 - 2 * α) ≤ gammaOf (N n) (B n) ^ (1 - 2 * α) :=
          Real.rpow_le_rpow_of_nonpos (hγ n) hg1 (by linarith)
        have hpos : 0 ≤ (u n * v n / Kc α ^ 2) ^ α := by
          have := hu0 n; have := hv0 n; positivity
        have h3 : 0 ≤ ((((N n : ℕ) : ℝ) + 1) / (B n : ℝ)) ^ (1 - 2 * α) / (2 * α - 1) :=
          div_nonneg (Real.rpow_nonneg (by have := hBr n; positivity) _) h2α.le
        exact mul_le_mul h1 (div_le_div_of_nonneg_right h2 h2α.le) h3 hpos
      have hdiv : (u n * v n / Kc α ^ 2) ^ α * (gammaOf (N n) (B n) ^ (1 - 2 * α) / (2 * α - 1)) +
          1 / (B n : ℝ) ≤ 4 * Kc α * ((max (u n) (v n) / gammaOf (N n) (B n)) ^ (2 * α - 1) /
            ((Kc α ^ 2) ^ α * (2 * α - 1)) + 1 / (((B n : ℕ) : ℝ) * min (u n) (v n))) *
            profT α (u n) (v n) := by
        rwa [div_le_iff₀ hT] at hEd
      have hKθ : Kc α * ((1 - ε) ^ (1 / α) / Kc α * profT α (u n) (v n)) =
          (1 - ε) ^ (1 / α) * profT α (u n) (v n) := by field_simp
      rw [hKθ] at hlo
      linarith
  rw [tendsto_order]
  constructor
  · intro a' ha'
    set a'' : ℝ := (1 + max a' 0) / 2 with ha''
    have h1 : a' < a'' := by
      have := le_max_left a' 0; linarith
    have h2 : a'' < 1 := by
      have : max a' 0 < 1 := max_lt ha' one_pos
      linarith
    have h3 : 0 < a'' := by
      have := le_max_right a' 0; linarith
    have h4 : a'' ^ α < 1 := Real.rpow_lt_one h3.le h2 hα0
    have h5 : 0 < a'' ^ α := Real.rpow_pos_of_pos h3 α
    set ε : ℝ := (1 - a'' ^ α) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hε1 : ε < 1 := by rw [hε]; linarith
    have hθ : a'' < (1 - ε) ^ (1 / α) := by
      have : a'' ^ α < 1 - ε := by rw [hε]; linarith
      have h6 := Real.rpow_lt_rpow (Real.rpow_nonneg h3.le α) this (one_div_pos.2 hα0)
      rwa [← Real.rpow_mul h3.le, mul_one_div_cancel hα0.ne', Real.rpow_one] at h6
    have hEn := (tendsto_order.1 hElim).2 ((1 - ε) ^ (1 / α) - a') (by linarith)
    filter_upwards [key ε hε0 hε1, hEn] with n hk hE
    have hT := hTpos n
    rw [lt_div_iff₀ hT]
    have := hk.2
    nlinarith
  · intro a' ha'
    have h0 : 1 < a' ^ α := Real.one_lt_rpow ha' hα0
    set ε : ℝ := min (1 / 2) ((a' ^ α - 1) / 2) with hε
    have hε0 : 0 < ε := lt_min (by norm_num) (by linarith)
    have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hθ : (1 + ε) ^ (1 / α) < a' := by
      have : 1 + ε < a' ^ α := by
        have := min_le_right (1 / 2 : ℝ) ((a' ^ α - 1) / 2); linarith
      have h6 := Real.rpow_lt_rpow (by linarith) this (one_div_pos.2 hα0)
      rwa [← Real.rpow_mul (by linarith), mul_one_div_cancel hα0.ne', Real.rpow_one] at h6
    filter_upwards [key ε hε0 hε1] with n hk
    have hT := hTpos n
    rw [div_lt_iff₀ hT]
    have := hk.1
    nlinarith

private lemma pg9_TN_comm {B : ℕ} {N : ℕ} (μ : Fin N → ℝ) (m₁ m₂ : ℝ) :
    TNpart B μ m₁ m₂ = TNpart B μ m₂ m₁ := by
  unfold TNpart
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private lemma pg9_lagInt_neg {β : ℝ} {B : ℕ} {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (ℓ : ℕ)
    (m₁ m₂ : ℝ) :
    lagIntegrand β B μ i (-((ℓ : ℤ) + 1)) m₁ m₂ = lagIntegrand β B μ i ((ℓ : ℤ) + 1) m₂ m₁ := by
  have h1 : ¬ (0 ≤ -((ℓ : ℤ) + 1)) := by omega
  have h2 : (0 : ℤ) ≤ (ℓ : ℤ) + 1 := by omega
  have h3 : (-(-((ℓ : ℤ) + 1))).toNat = ℓ + 1 := by omega
  have h4 : ((ℓ : ℤ) + 1).toNat = ℓ + 1 := by omega
  unfold lagIntegrand lagNumer deltaN DLag MLag
  simp only [h1, h2, ite_false, ite_true, h3, h4]
  rw [pg9_TN_comm μ m₁ m₂]
  have e1 : Wpart β B μ i m₁ * Wpart β B μ i m₂ = Wpart β B μ i m₂ * Wpart β B μ i m₁ := mul_comm _ _
  have e2 : gammaOf N B * m₁ * m₂ = gammaOf N B * m₂ * m₁ := by ring
  rw [e1, mul_comm m₁ m₂, e2]

private lemma pg9_lagTerm_neg {α β c : ℝ} {N B : ℕ} (i : Fin N) (ℓ : ℕ)
    (hint : IntegrableOn (fun p : ℝ × ℝ => lagIntegrand β B (plSpec α c N) i ((ℓ : ℤ) + 1) p.1 p.2)
      (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B))) :
    lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) (-((ℓ : ℤ) + 1)) =
      lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ((ℓ : ℤ) + 1) := by
  unfold lagTerm
  simp only [pg9_lagInt_neg]
  have hI : Integrable (Function.uncurry fun a b : ℝ =>
      lagIntegrand β B (plSpec α c N) i ((ℓ : ℤ) + 1) a b)
      ((volume.restrict (Ioo 0 (gammaOf N B))).prod (volume.restrict (Ioo 0 (gammaOf N B)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hint
  exact (integral_integral_swap (f := fun a b : ℝ =>
      lagIntegrand β B (plSpec α c N) i ((ℓ : ℤ) + 1) a b) hI).symm

private lemma pg9_vPart_rep {α β c : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N)
    (hZ : CbarPart β B (plSpec α c N) i 0 = 1) :
    vPart β B (plSpec α c N) i = (Real.pi ^ 2)⁻¹ *
      ∑' ℓ : ℤ, lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ := by
  obtain ⟨-, -, hint, hsum, -⟩ := lem_app_pl_age_iv hα hβ0 hβ1 N B c hN hB hc i
  have hfun : (fun ℓ : ℤ => lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B))
      (Ioo 0 (gammaOf N B)) ℓ) = fun ℓ => lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B))
      (Ioo 0 (gammaOf N B)) ℓ := rfl
  have hs1 : Summable (fun n : ℕ => lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B))
      (Ioo 0 (gammaOf N B)) ((n : ℤ) + 1)) :=
    hsum.comp_injective (i := fun n : ℕ => (n : ℤ) + 1) (fun a b h => by simpa using h)
  have hs2 : Summable (fun n : ℕ => lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B))
      (Ioo 0 (gammaOf N B)) (-((n : ℤ) + 1))) :=
    hsum.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1)) (fun a b h => by simpa using h)
  rw [tsum_of_add_one_of_neg_add_one hs1 hs2]
  have hneg : ∀ n : ℕ, lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B))
      (-((n : ℤ) + 1)) = lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B))
      (Ioo 0 (gammaOf N B)) ((n : ℤ) + 1) := fun n => pg9_lagTerm_neg i n (hint _)
  simp only [hneg]
  have h0 : lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) 0 =
      Real.pi ^ 2 := by
    unfold CbarPart at hZ
    have hp : Real.pi ^ 2 ≠ 0 := by positivity
    field_simp at hZ
    linarith
  rw [h0]
  unfold vPart CbarPart
  rw [tsum_mul_left]
  have hp : Real.pi ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private lemma pg9_lamlim {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) {m : ℝ} (hm : 0 < m) :
    Tendsto (fun n => c n * partLam (B n) (plSpec α (c n) (N n)) m /
      (((B n : ℕ) : ℝ) * m / Kc α) ^ α) atTop (𝓝 1) := by
  have hK := vg_K_pos hα1
  have hBm : Tendsto (fun n => ((B n : ℕ) : ℝ) * (fun _ => m) n) atTop atTop :=
    R.hB.atTop_mul_const hm
  have hmγ : Tendsto (fun n => (fun _ : ℕ => m) n / gammaOf (N n) (B n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop R.hγ
  have h := lem_app_pl_finite_inverse_iv_i R hα1 (fun _ => m) hBm hmγ
  have hg : ∀ᶠ n in atTop, (((B n : ℕ) : ℝ) * m / Kc α) ^ α ≠ 0 := by
    filter_upwards [R.hB.eventually_ge_atTop 1] with n hn
    exact (Real.rpow_pos_of_pos (div_pos (mul_pos (by linarith) hm) hK) α).ne'
  exact (isEquivalent_iff_tendsto_one hg).1 h

private lemma pg9_elaslim {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) {m : ℝ} (hm : 0 < m) :
    Tendsto (fun n => m * deriv (partLam (B n) (plSpec α (c n) (N n))) m /
      partLam (B n) (plSpec α (c n) (N n)) m) atTop (𝓝 α) := by
  have hBm : Tendsto (fun n => ((B n : ℕ) : ℝ) * (fun _ => m) n) atTop atTop :=
    R.hB.atTop_mul_const hm
  have hmγ : Tendsto (fun n => (fun _ : ℕ => m) n / gammaOf (N n) (B n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop R.hγ
  exact lem_app_pl_finite_inverse_iv_ii R hα1 (fun _ => m) hBm hmγ

private lemma pg9_theta_lim {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) {m : ℝ} (hm : 0 < m) :
    Tendsto (fun n => thetaN β (B n) (plSpec α (c n) (N n)) m) atTop (𝓝 (profTheta α β m)) := by
  have h1 := (pg9_elaslim R hα1 hm).div_const m
  have h2 : Tendsto (fun n => 1 / (gammaOf (N n) (B n) - m)) atTop (𝓝 0) := by
    have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
    have : Tendsto (fun n => gammaOf (N n) (B n) - m) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-m) hg
    exact tendsto_const_nhds.div_atTop this
  have h3 := ((tendsto_const_nhds (x := 1 / Efun β m)).add h1).add h2 |>.sub
    (tendsto_const_nhds (x := 1 / m))
  have e : profTheta α β m = 1 / Efun β m + α / m + 0 - 1 / m := by
    unfold profTheta; field_simp; ring
  rw [e]
  refine h3.congr (fun n => ?_)
  unfold thetaN
  have hm0 : m ≠ 0 := hm.ne'
  by_cases hΛ : partLam (B n) (plSpec α (c n) (N n)) m = 0
  · simp [hΛ]
  · field_simp

private lemma pg9_x_lim {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (i : ∀ n, Fin (N n)) (X0 : ℝ)
    (hX0 : 0 < X0)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 X0)) {m : ℝ} (hm : 0 < m) :
    Tendsto (fun n => plSpec α (c n) (N n) (i n) * partLam (B n) (plSpec α (c n) (N n)) m)
      atTop (𝓝 ((m / X0) ^ α)) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  have h1 := pg9_lamlim R hα1 hm
  have h2 : Tendsto (fun n => (m / (rowIdx (i n) / icCross α (B n))) ^ α) atTop (𝓝 ((m / X0) ^ α)) := by
    have hc : ContinuousAt (fun x : ℝ => (m / x) ^ α) X0 := by
      apply ContinuousAt.rpow_const (continuousAt_const.div continuousAt_id hX0.ne')
      exact Or.inr hα0.le
    exact hc.tendsto.comp hX
  have h3 := h1.mul h2
  rw [one_mul] at h3
  refine h3.congr' ?_
  filter_upwards [R.hB.eventually_ge_atTop 1] with n hn
  have hBr : (0:ℝ) < (B n : ℝ) := by linarith
  have hρ : 0 < rowIdx (i n) := by unfold rowIdx; positivity
  have hp : 0 < (((B n : ℕ) : ℝ) * m / Kc α) := div_pos (mul_pos hBr hm) hK
  have hp' : 0 < (((B n : ℕ) : ℝ) * m / Kc α) ^ α := Real.rpow_pos_of_pos hp α
  have e1 : (m / (rowIdx (i n) / icCross α (B n))) ^ α =
      (((B n : ℕ) : ℝ) * m / Kc α) ^ α * rowIdx (i n) ^ (-α) := by
    have : m / (rowIdx (i n) / icCross α (B n)) = ((B n : ℕ) : ℝ) * m / Kc α / rowIdx (i n) := by
      unfold icCross; field_simp
    rw [this, Real.div_rpow hp.le hρ.le, Real.rpow_neg hρ.le]
    ring
  rw [e1]
  unfold plSpec
  have : (((i n : ℕ) : ℝ) + 1) = rowIdx (i n) := rfl
  rw [this]
  field_simp

private lemma pg9_sig_x {α X m : ℝ} (hα : 0 < α) (hX : 0 < X) (hm : 0 < m) :
    Real.sqrt (profZeta α X m * (1 - profZeta α X m)) =
      Real.sqrt ((m / X) ^ α) / (1 + (m / X) ^ α) := by
  have hr : 0 < m / X := div_pos hm hX
  have h := vz_zeta_scale (α := α) hα hX hr
  have e : X * (m / X) = m := by field_simp
  rw [e] at h
  rw [h]
  have := vz_sigma (α := α) hα hr
  rw [this, Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]
  congr 2
  ring

private lemma pg9_W_lim {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (i : ∀ n, Fin (N n)) (X0 : ℝ)
    (hX0 : 0 < X0)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 X0)) {m : ℝ} (hm : 0 < m) :
    Tendsto (fun n => Wpart β (B n) (plSpec α (c n) (N n)) (i n) m) atTop
      (𝓝 (Real.sqrt (profZeta α X0 m * (1 - profZeta α X0 m)) / Real.sqrt m * profTheta α β m)) := by
  have hα0 : 0 < α := by linarith
  have hx := pg9_x_lim R hα1 i X0 hX0 hX hm
  have hx0 : 0 < (m / X0) ^ α := Real.rpow_pos_of_pos (div_pos hm hX0) α
  have hs : Tendsto (fun n => Real.sqrt (plSpec α (c n) (N n) (i n) *
      partLam (B n) (plSpec α (c n) (N n)) m)) atTop (𝓝 (Real.sqrt ((m / X0) ^ α))) :=
    (Real.continuous_sqrt.tendsto _).comp hx
  have hd : Tendsto (fun n => Real.sqrt m * (1 + plSpec α (c n) (N n) (i n) *
      partLam (B n) (plSpec α (c n) (N n)) m)) atTop (𝓝 (Real.sqrt m * (1 + (m / X0) ^ α))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add hx)
  have hq : Tendsto (fun n => Real.sqrt (plSpec α (c n) (N n) (i n) *
      partLam (B n) (plSpec α (c n) (N n)) m) / (Real.sqrt m * (1 + plSpec α (c n) (N n) (i n) *
      partLam (B n) (plSpec α (c n) (N n)) m))) atTop
      (𝓝 (Real.sqrt ((m / X0) ^ α) / (Real.sqrt m * (1 + (m / X0) ^ α)))) :=
    hs.div hd (by have := Real.sqrt_pos.2 hm; positivity)
  have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  have hr : Tendsto (fun n => Real.sqrt (1 - m / gammaOf (N n) (B n))) atTop (𝓝 1) := by
    have : Tendsto (fun n => m / gammaOf (N n) (B n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hg
    have h2 := (Real.continuous_sqrt.tendsto (1 - 0)).comp (tendsto_const_nhds.sub this)
    simpa [Function.comp_def] using h2
  have hθ := pg9_theta_lim R hα1 hm
  have := (hq.mul hr).mul hθ
  rw [mul_one] at this
  rw [pg9_sig_x hα0 hX0 hm]
  convert this using 1
  · rfl
  · field_simp

private lemma pg9_TN_lim_fixed {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) {m₁ m₂ : ℝ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    Tendsto (fun n => TNpart (B n) (plSpec α (c n) (N n)) m₁ m₂) atTop (𝓝 (profT α m₁ m₂)) := by
  have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  have h := pg9_TN_ratio R hα1 (fun _ => m₁) (fun _ => m₂) (fun _ => h₁) (fun _ => h₂)
    (R.hB.atTop_mul_const h₁) (R.hB.atTop_mul_const h₂)
    (tendsto_const_nhds.div_atTop hg) (tendsto_const_nhds.div_atTop hg)
  have hT : 0 < profT α m₁ m₂ :=
    lt_of_lt_of_le (div_pos (lt_min h₁ h₂) (by have := vg_K_pos hα1; positivity))
      (pg9_profT_lb hα1 h₁ h₂)
  have := h.mul_const (profT α m₁ m₂)
  rw [one_mul] at this
  refine this.congr (fun n => ?_)
  field_simp

private lemma pg9_delta_lim {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) {m₁ m₂ : ℝ} (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (ℓ : ℤ) :
    Tendsto (fun n => deltaN β (B n) (plSpec α (c n) (N n)) ℓ m₁ m₂) atTop
      (𝓝 (profDelta α β ℓ m₁ m₂)) := by
  have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  have hT := pg9_TN_lim_fixed R hα1 h₁ h₂
  have hinv : Tendsto (fun n => (gammaOf (N n) (B n))⁻¹) atTop (𝓝 0) := hg.inv_tendsto_atTop
  set M := MLag β (Qm β m₁) (Qm β m₂) ℓ
  set D := DLag β (Qm β m₁) (Qm β m₂) ℓ
  have h1 : Tendsto (fun n => (1 - TNpart (B n) (plSpec α (c n) (N n)) m₁ m₂ * M / (m₁ * m₂)) *
      (1 - M * (gammaOf (N n) (B n))⁻¹) -
      TNpart (B n) (plSpec α (c n) (N n)) m₁ m₂ * D ^ 2 * (gammaOf (N n) (B n))⁻¹ / (m₁ * m₂))
      atTop (𝓝 ((1 - profT α m₁ m₂ * M / (m₁ * m₂)) * (1 - M * 0) - profT α m₁ m₂ * D ^ 2 * 0 /
        (m₁ * m₂))) := by
    refine Tendsto.sub (Tendsto.mul ?_ ?_) ?_
    · exact tendsto_const_nhds.sub ((hT.mul_const M).div_const _)
    · exact tendsto_const_nhds.sub (hinv.const_mul M)
    · exact (((hT.mul_const (D ^ 2)).mul hinv).div_const _)
  unfold profDelta
  simp only [mul_zero, zero_div, sub_zero, mul_one] at h1
  refine h1.congr (fun n => ?_)
  unfold deltaN
  have hγn : 0 < gammaOf (N n) (B n) := by
    unfold gammaOf
    exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
  field_simp
  rfl

private lemma pg9_theta_pos {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ Cθ : ℝ, 0 < Cθ ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c →
      ∀ m ∈ Ioo 0 (gammaOf N B), 0 < thetaN β B (plSpec α c N) m ∧
        thetaN β B (plSpec α c N) m ≤ Cθ * (1 + 1 / m + 1 / (gammaOf N B - m)) := by
  obtain ⟨C, hC⟩ := lem_app_pl_elasticity_ii hα hβ0 hβ1
  obtain ⟨cE, hcE, hE⟩ := vs_E_lb hβ0 hβ1
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun N B c hN hB hc m hm => ?_⟩
  obtain ⟨h1, h2⟩ := hC N B c hN hB hc m hm
  have hE0 : 0 < Efun β m := lt_of_lt_of_le (mul_pos hcE (lt_min hm.1 one_pos)) (hE m hm.1)
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    have : Efun β m * thetaN β B (plSpec α c N) m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hE0.le h
    linarith
  · refine h1.trans ?_
    have hp : 0 ≤ 1 + 1 / m + 1 / (gammaOf N B - m) := by
      have : 0 < gammaOf N B - m := by linarith [hm.2]
      have : 0 < 1 / m := one_div_pos.2 hm.1
      positivity
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hp

private lemma pg9_W_nonneg {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) {c : ℝ} (hc : 0 < c) (i : Fin N) {m : ℝ}
    (hm : m ∈ Ioo 0 (gammaOf N B)) : 0 ≤ Wpart β B (plSpec α c N) i m := by
  obtain ⟨Cθ, hCθ, h⟩ := pg9_theta_pos hα hβ0 hβ1
  have hθ := (h N B c hN hB hc m hm).1
  unfold Wpart
  have : 0 ≤ Real.sqrt (1 - m / gammaOf N B) := Real.sqrt_nonneg _
  have hm0 := hm.1
  have hΛ := pg9_lam_pos (α := α) hN hB hc hm
  have hμ := pg9_plSpec_pos (α := α) hc N i
  have : 0 < plSpec α c N i * partLam B (plSpec α c N) m := mul_pos hμ hΛ
  positivity

private lemma pg9_delta_lb {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ cα : ℝ, 0 < cα ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ (ℓ : ℤ) (m₁ m₂ : ℝ),
      m₁ ∈ Ioo 0 (gammaOf N B) → m₂ ∈ Ioo 0 (gammaOf N B) →
      m₁ ≤ gammaOf N B / 2 → m₂ ≤ gammaOf N B / 2 →
      cα / 4 ≤ deltaN β B (plSpec α c N) ℓ m₁ m₂ := by
  obtain ⟨cα, hcα, hch⟩ := lem_app_pl_determinant_ii_chain hα
  refine ⟨cα, hcα, fun N B c hN hB hc ℓ m₁ m₂ hm₁ hm₂ h1 h2 => ?_⟩
  have h3 := hch N B c hN hB hc m₁ m₂ hm₁ hm₂
  have h4 := lem_app_pl_determinant_ii (β := β) hα hβ0 hβ1 N B c hN hB hc ℓ m₁ m₂ hm₁ hm₂
  have hγ : 0 < gammaOf N B := lt_trans hm₁.1 hm₁.2
  have e1 : 1 / 2 ≤ 1 - m₁ / gammaOf N B := by
    have : m₁ / gammaOf N B ≤ 1 / 2 := by rw [div_le_iff₀ hγ]; linarith
    linarith
  have e2 : 1 / 2 ≤ 1 - m₂ / gammaOf N B := by
    have : m₂ / gammaOf N B ≤ 1 / 2 := by rw [div_le_iff₀ hγ]; linarith
    linarith
  have : cα / 4 ≤ cα * ((1 - m₁ / gammaOf N B) * (1 - m₂ / gammaOf N B)) := by
    have := mul_le_mul e1 e2 (by norm_num) (by linarith)
    nlinarith
  linarith

open Muon.DetEquiv ProbabilityTheory in
private lemma pg9_D_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Summable (fun ℓ : ℤ => DLag β (Qm β u) (Qm β v) ℓ) :=
  (lem_app_pl_age_iii hβ0 hβ1 u v hu hv).2.summable

private lemma pg9_term_lim {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (i : ∀ n, Fin (N n)) (X0 : ℝ)
    (hX0 : 0 < X0)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 X0)) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (ℓ : ℤ) :
    Tendsto (fun n => lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ u v) atTop
      (𝓝 (Real.sqrt (profZeta α X0 u * (1 - profZeta α X0 u) *
              (profZeta α X0 v * (1 - profZeta α X0 v))) / Real.sqrt (u * v) *
            (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v /
              profDelta α β ℓ u v))) := by
  have hα0 : 0 < α := by linarith
  have hWu := pg9_W_lim R hα1 i X0 hX0 hX hu
  have hWv := pg9_W_lim R hα1 i X0 hX0 hX hv
  have hΔ := pg9_delta_lim R hα1 hu hv ℓ
  have hΔ0 : profDelta α β ℓ u v ≠ 0 := by
    have := vs_Delta_ge hα1 R.hβ0 R.hβ1 hu hv ℓ
    have : 0 < 1 / α := by positivity
    linarith
  have h := ((hWu.mul hWv).mul_const (DLag β (Qm β u) (Qm β v) ℓ)).div hΔ hΔ0
  unfold lagIntegrand lagNumer
  convert h using 2
  obtain ⟨hz1, hz1'⟩ := vs_zeta_bd hα0 hX0 hu
  obtain ⟨hz2, hz2'⟩ := vs_zeta_bd hα0 hX0 hv
  have hA1 : 0 ≤ profZeta α X0 u * (1 - profZeta α X0 u) := mul_nonneg hz1.le (by linarith)
  rw [Real.sqrt_mul hA1, Real.sqrt_mul hu.le]
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  field_simp

private lemma pg9_S_lim {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (i : ∀ n, Fin (N n)) (X0 : ℝ)
    (hX0 : 0 < X0)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 X0)) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    Tendsto (fun n => ∑' ℓ : ℤ, lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ u v) atTop
      (𝓝 (∑' ℓ : ℤ, Real.sqrt (profZeta α X0 u * (1 - profZeta α X0 u) *
              (profZeta α X0 v * (1 - profZeta α X0 v))) / Real.sqrt (u * v) *
            (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v /
              profDelta α β ℓ u v))) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨cα, hcα, hδ⟩ := pg9_delta_lb hα0 R.hβ0 R.hβ1
  have hWu := pg9_W_lim R hα1 i X0 hX0 hX hu
  have hWv := pg9_W_lim R hα1 i X0 hX0 hX hv
  set Wu := Real.sqrt (profZeta α X0 u * (1 - profZeta α X0 u)) / Real.sqrt u * profTheta α β u
  set Wv := Real.sqrt (profZeta α X0 v * (1 - profZeta α X0 v)) / Real.sqrt v * profTheta α β v
  have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun ℓ => (Wu + 1) * (Wv + 1) * (4 / cα) * DLag β (Qm β u) (Qm β v) ℓ) ?_ ?_ ?_
  · exact (pg9_D_summable R.hβ0 R.hβ1 hu hv).mul_left _
  · intro ℓ
    exact pg9_term_lim R hα1 i X0 hX0 hX hu hv ℓ
  · filter_upwards [(tendsto_order.1 hWu).2 (Wu + 1) (by linarith),
      (tendsto_order.1 hWv).2 (Wv + 1) (by linarith),
      hg.eventually_gt_atTop (2 * u), hg.eventually_gt_atTop (2 * v)] with n h1 h2 h3 h4 ℓ
    have hmu : u ∈ Ioo 0 (gammaOf (N n) (B n)) := ⟨hu, by linarith⟩
    have hmv : v ∈ Ioo 0 (gammaOf (N n) (B n)) := ⟨hv, by linarith⟩
    have hΔ := hδ (N n) (B n) (c n) (R.hNpos n) (R.hBpos n) (R.hcpos n) ℓ u v hmu hmv
      (by linarith) (by linarith)
    have hW1 := pg9_W_nonneg hα0 R.hβ0 R.hβ1 (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n) hmu
    have hW2 := pg9_W_nonneg hα0 R.hβ0 R.hβ1 (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n) hmv
    obtain ⟨hQu, -⟩ := vs_Qm R.hβ0 R.hβ1 hu
    obtain ⟨hQv, -⟩ := vs_Qm R.hβ0 R.hβ1 hv
    have hD := vs_DLag_nonneg R.hβ0 R.hβ1 hQu.le hQv.le ℓ
    unfold lagIntegrand lagNumer
    have hΔ0 : 0 < deltaN β (B n) (plSpec α (c n) (N n)) ℓ u v := lt_of_lt_of_le (by positivity) hΔ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    set W1 := Wpart β (B n) (plSpec α (c n) (N n)) (i n) u
    set W2 := Wpart β (B n) (plSpec α (c n) (N n)) (i n) v
    set D := DLag β (Qm β u) (Qm β v) ℓ
    have e1 : D / deltaN β (B n) (plSpec α (c n) (N n)) ℓ u v ≤ (4 / cα) * D := by
      rw [div_le_iff₀ hΔ0]
      have : 1 ≤ (4 / cα) * deltaN β (B n) (plSpec α (c n) (N n)) ℓ u v := by
        have := mul_le_mul_of_nonneg_left hΔ (by positivity : 0 ≤ 4 / cα)
        have e : 4 / cα * (cα / 4) = 1 := by field_simp
        linarith
      nlinarith
    have e2 : W1 * W2 * D / deltaN β (B n) (plSpec α (c n) (N n)) ℓ u v =
        W1 * W2 * (D / deltaN β (B n) (plSpec α (c n) (N n)) ℓ u v) := by ring
    rw [e2]
    calc W1 * W2 * (D / deltaN β (B n) (plSpec α (c n) (N n)) ℓ u v) ≤ (Wu + 1) * (Wv + 1) * ((4 / cα) * D) := by
          apply mul_le_mul (mul_le_mul h1.le h2.le hW2 (by linarith)) e1 (by positivity) (by nlinarith)
      _ = _ := by ring

private lemma pg9_W_core {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ Cθ : ℝ, 0 < Cθ ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ (i : Fin N) (m : ℝ),
      0 < m → m ≤ gammaOf N B / 2 →
      0 ≤ Wpart β B (plSpec α c N) i m ∧
      Wpart β B (plSpec α c N) i m ≤
        Real.sqrt (plSpec α c N i * partLam B (plSpec α c N) m) /
            (1 + plSpec α c N i * partLam B (plSpec α c N) m) *
          (m ^ (-(1 / 2 : ℝ)) * (Cθ * (1 + 1 / m + 2 / gammaOf N B))) := by
  obtain ⟨Cθ, hCθ, h⟩ := pg9_theta_pos hα hβ0 hβ1
  refine ⟨Cθ, hCθ, fun N B c hN hB hc i m hm hmγ => ?_⟩
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by unfold gammaOf; positivity
  have hmem : m ∈ Ioo 0 (gammaOf N B) := ⟨hm, by linarith⟩
  refine ⟨pg9_W_nonneg hα hβ0 hβ1 hN hB hc i hmem, ?_⟩
  obtain ⟨hθ0, hθ⟩ := h N B c hN hB hc m hmem
  have hΛ := pg9_lam_pos (α := α) hN hB hc hmem
  have hμ := pg9_plSpec_pos (α := α) hc N i
  set x := plSpec α c N i * partLam B (plSpec α c N) m with hx
  have hx0 : 0 < x := mul_pos hμ hΛ
  have h1γ : 1 / (gammaOf N B - m) ≤ 2 / gammaOf N B := by
    rw [div_le_div_iff₀ (by linarith) hγ]; linarith
  have hθ' : thetaN β B (plSpec α c N) m ≤ Cθ * (1 + 1 / m + 2 / gammaOf N B) := by
    refine hθ.trans (mul_le_mul_of_nonneg_left (by linarith) hCθ.le)
  have hs : Real.sqrt (1 - m / gammaOf N B) ≤ 1 := by
    rw [Real.sqrt_le_one]
    have : 0 ≤ m / gammaOf N B := by positivity
    linarith
  have hm12 : m ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt m := by
    rw [Real.rpow_neg hm.le, Real.sqrt_eq_rpow]; simp
  unfold Wpart
  rw [← hx, hm12]
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have e : Real.sqrt x / (Real.sqrt m * (1 + x)) * Real.sqrt (1 - m / gammaOf N B) *
      thetaN β B (plSpec α c N) m =
      Real.sqrt x / (1 + x) * (1 / Real.sqrt m) *
        (Real.sqrt (1 - m / gammaOf N B) * thetaN β B (plSpec α c N) m) := by
    field_simp
  rw [e]
  have hS0 : 0 ≤ Real.sqrt x / (1 + x) := by positivity
  have hmm : 0 ≤ 1 / Real.sqrt m := by positivity
  have hprod : Real.sqrt (1 - m / gammaOf N B) * thetaN β B (plSpec α c N) m ≤
      Cθ * (1 + 1 / m + 2 / gammaOf N B) := by
    calc _ ≤ 1 * thetaN β B (plSpec α c N) m := mul_le_mul_of_nonneg_right hs hθ0.le
      _ ≤ _ := by linarith
  have hprod0 : 0 ≤ Real.sqrt (1 - m / gammaOf N B) * thetaN β B (plSpec α c N) m :=
    mul_nonneg (Real.sqrt_nonneg _) hθ0.le
  calc Real.sqrt x / (1 + x) * (1 / Real.sqrt m) *
        (Real.sqrt (1 - m / gammaOf N B) * thetaN β B (plSpec α c N) m)
      ≤ Real.sqrt x / (1 + x) * (1 / Real.sqrt m) * (Cθ * (1 + 1 / m + 2 / gammaOf N B)) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg hS0 hmm)
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private lemma pg9_k_bd {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ (i : Fin N) (m aL aU : ℝ),
      1 ≤ gammaOf N B → 0 < m → m ≤ gammaOf N B / 2 → 0 < aL →
      aL ≤ (((i : ℕ) : ℝ) + 1) / B → (((i : ℕ) : ℝ) + 1) / B ≤ aU →
      Wpart β B (plSpec α c N) i m * min (Real.sqrt m) 1 ≤
        A * ((if m < 1 / (B : ℝ) then Real.sqrt (B : ℝ) * (((i : ℕ) : ℝ) + 1) ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ))
              else 0) +
          (if m ≤ 1 then 1 / aL ^ (α / 2) * m ^ (α / 2 - 1) else aU ^ (α / 2) * m ^ (-((α + 1) / 2)))) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨Cθ, hCθ, hW⟩ := pg9_W_core hα0 hβ0 hβ1
  obtain ⟨C₁, C₂, hC₁, hC₂, hv1⟩ := lem_app_pl_finite_inverse_v_i hα1
  obtain ⟨D₁, D₂, hD₁, hD₂, hv2⟩ := lem_app_pl_finite_inverse_v_ii hα1
  set M0 : ℝ := max (max (Real.sqrt C₂) (1 / Real.sqrt C₁)) (Real.sqrt D₂) with hM0
  have hM2 : Real.sqrt C₂ ≤ M0 := (le_max_left _ _).trans (le_max_left _ _)
  have hM1 : 1 / Real.sqrt C₁ ≤ M0 := (le_max_right _ _).trans (le_max_left _ _)
  have hM3 : Real.sqrt D₂ ≤ M0 := le_max_right _ _
  have hs2 : 0 < Real.sqrt C₂ := Real.sqrt_pos.2 hC₂
  have hM0pos : 0 < M0 := lt_of_lt_of_le hs2 hM2
  refine ⟨4 * Cθ * M0, by positivity, fun N B c hN hB hc i m aL aU hγ1 hm hmγ haL h1 h2 => ?_⟩
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hB1 : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by linarith
  have hmem : m ∈ Ioo 0 (gammaOf N B) := ⟨hm, by linarith⟩
  obtain ⟨hW0, hWb⟩ := hW N B c hN hB hc i m hm hmγ
  set ρ : ℝ := ((i : ℕ) : ℝ) + 1 with hρ
  have hρ0 : 0 < ρ := by positivity
  set x := plSpec α c N i * partLam B (plSpec α c N) m with hx
  have hΛ := pg9_lam_pos (α := α) hN hB hc hmem
  have hx0 : 0 < x := mul_pos (pg9_plSpec_pos (α := α) hc N i) hΛ
  have hxe : x = (c * partLam B (plSpec α c N) m) * ρ ^ (-α) := by
    rw [hx]; unfold plSpec; rw [← hρ]; ring
  have hwm : 0 ≤ min (Real.sqrt m) 1 := le_min (Real.sqrt_nonneg _) zero_le_one
  have hSx : 0 ≤ Real.sqrt x / (1 + x) := by positivity
  have ht0 : 0 < (B : ℝ) * m / ρ := by positivity
  set t : ℝ := (B : ℝ) * m / ρ with ht
  have htl : t ≤ m / aL := by
    have h3 : (B : ℝ) / ρ ≤ 1 / aL := by
      rw [div_le_div_iff₀ hρ0 haL]
      have := (le_div_iff₀ hBr).1 h1
      nlinarith
    calc t = m * ((B : ℝ) / ρ) := by rw [ht]; ring
      _ ≤ m * (1 / aL) := mul_le_mul_of_nonneg_left h3 hm.le
      _ = m / aL := by ring
  have htu : 1 / t ≤ aU / m := by
    have : ρ / B ≤ aU := h2
    rw [ht, one_div_div, div_le_div_iff₀ (by positivity) hm]
    have := (div_le_iff₀ hBr).1 this
    nlinarith
  have hsq : ∀ s : ℝ, 0 < s → Real.sqrt (s ^ α) = s ^ (α / 2) := by
    intro s hs
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]; congr 1; ring
  have hcl : ∀ K : ℝ, 0 ≤ K → c * partLam B (plSpec α c N) m ≤ K * ((B : ℝ) * m) ^ α →
      Real.sqrt x ≤ Real.sqrt K * t ^ (α / 2) := by
    intro K hK hle
    have : x ≤ K * t ^ α := by
      rw [hxe, ht, Real.div_rpow (by positivity) hρ0.le]
      calc c * partLam B (plSpec α c N) m * ρ ^ (-α) ≤ K * ((B : ℝ) * m) ^ α * ρ ^ (-α) :=
            mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hρ0.le _)
        _ = K * (((B : ℝ) * m) ^ α / ρ ^ α) := by rw [Real.rpow_neg hρ0.le]; ring
    calc Real.sqrt x ≤ Real.sqrt (K * t ^ α) := Real.sqrt_le_sqrt this
      _ = Real.sqrt K * t ^ (α / 2) := by rw [Real.sqrt_mul hK, hsq t ht0]
  have hms : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hmh : m ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt m := by
    rw [Real.rpow_neg hm.le, Real.sqrt_eq_rpow]; simp
  have hsqm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
  have hdiv : Real.sqrt m / m = m ^ (-(1 / 2 : ℝ)) := by
    rw [hmh, div_eq_div_iff hm.ne' hms.ne', one_mul]; exact hsqm
  have hT1 : 0 ≤ (if m < 1 / (B : ℝ) then Real.sqrt (B : ℝ) * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) := by
    split_ifs
    · positivity
    · exact le_rfl
  have hT2 : 0 ≤ (if m ≤ 1 then 1 / aL ^ (α / 2) * m ^ (α / 2 - 1) else aU ^ (α / 2) * m ^ (-((α + 1) / 2))) := by
    have : 0 < aU := lt_of_lt_of_le haL (h1.trans h2)
    split_ifs
    · positivity
    · positivity
  have hS1 : Real.sqrt x / (1 + x) ≤ Real.sqrt x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Real.sqrt_nonneg x]
  have hS2 : Real.sqrt x / (1 + x) ≤ 1 / Real.sqrt x := by
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hsxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    calc Real.sqrt x / (1 + x) ≤ Real.sqrt x / x :=
          div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hx0 (by linarith)
      _ = 1 / Real.sqrt x := by
          rw [div_eq_div_iff hx0.ne' hsx.ne', one_mul]; exact hsxx
  by_cases hm1 : m ≤ 1
  · have hw : min (Real.sqrt m) 1 = Real.sqrt m := min_eq_left (by rw [Real.sqrt_le_one]; exact hm1)
    have hq : 1 + 1 / m + 2 / gammaOf N B ≤ 4 / m := by
      have h2γ : 2 / gammaOf N B ≤ 2 := by rw [div_le_iff₀ hγ]; linarith
      have h1m : 1 ≤ 1 / m := by rw [le_div_iff₀ hm]; linarith
      have h2m : 2 ≤ 2 / m := by rw [le_div_iff₀ hm]; linarith
      have e4 : 4 / m = 4 * (1 / m) := by ring
      have e2 : 2 / m = 2 * (1 / m) := by ring
      linarith
    have key : Wpart β B (plSpec α c N) i m * min (Real.sqrt m) 1 ≤
        Real.sqrt x / (1 + x) * (Cθ * (4 / m)) := by
      rw [hw]
      calc Wpart β B (plSpec α c N) i m * Real.sqrt m
          ≤ Real.sqrt x / (1 + x) * (m ^ (-(1 / 2 : ℝ)) * (Cθ * (1 + 1 / m + 2 / gammaOf N B))) *
              Real.sqrt m := mul_le_mul_of_nonneg_right hWb hms.le
        _ = Real.sqrt x / (1 + x) * (Cθ * (1 + 1 / m + 2 / gammaOf N B)) := by
            rw [hmh]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hCθ.le) hSx
    by_cases hmB : m < 1 / (B : ℝ)
    · -- small m
      have hv := (hv2 N B c m hN hB hc hm (by linarith) hmγ).2
      have hxle : Real.sqrt x ≤ Real.sqrt D₂ * (Real.sqrt B * Real.sqrt m * ρ ^ (-(α / 2))) := by
        have : x ≤ D₂ * (B * m) * ρ ^ (-α) := by
          rw [hxe]; exact mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg hρ0.le _)
        calc Real.sqrt x ≤ Real.sqrt (D₂ * (B * m) * ρ ^ (-α)) := Real.sqrt_le_sqrt this
          _ = Real.sqrt D₂ * (Real.sqrt B * Real.sqrt m * ρ ^ (-(α / 2))) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hD₂.le, Real.sqrt_mul hBr.le,
              Real.sqrt_eq_rpow (ρ ^ (-α)), ← Real.rpow_mul hρ0.le]
            rw [show (-α) * (1 / 2) = -(α / 2) by ring]; ring
      have h3 : Wpart β B (plSpec α c N) i m * min (Real.sqrt m) 1 ≤
          4 * Cθ * M0 * (Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ))) := by
        refine key.trans ?_
        calc Real.sqrt x / (1 + x) * (Cθ * (4 / m)) ≤ Real.sqrt x * (Cθ * (4 / m)) :=
              mul_le_mul_of_nonneg_right hS1 (by positivity)
          _ ≤ Real.sqrt D₂ * (Real.sqrt B * Real.sqrt m * ρ ^ (-(α / 2))) * (Cθ * (4 / m)) :=
              mul_le_mul_of_nonneg_right hxle (by positivity)
          _ = 4 * Cθ * Real.sqrt D₂ * (Real.sqrt B * ρ ^ (-(α / 2)) * (Real.sqrt m / m)) := by ring
          _ = 4 * Cθ * Real.sqrt D₂ * (Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ))) := by
              rw [hdiv]
          _ ≤ _ := by
              have : 0 ≤ Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) := by positivity
              have := mul_le_mul_of_nonneg_right hM3 this
              have h4 : 0 ≤ 4 * Cθ := by positivity
              nlinarith
      have hT2' := hT2
      rw [if_pos hm1] at hT2'
      rw [if_pos hmB, if_pos hm1]
      calc _ ≤ 4 * Cθ * M0 * (Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ))) := h3
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hT2') (by positivity)
    · have hmB' : 1 / (B : ℝ) ≤ m := not_lt.1 hmB
      have hv := (hv1 N B c m hN hB hc hmB' hmγ).2
      have hxle := hcl C₂ hC₂.le hv
      have ht1 : t ^ (α / 2) ≤ (m / aL) ^ (α / 2) := Real.rpow_le_rpow ht0.le htl (by positivity)
      rw [Real.div_rpow hm.le haL.le] at ht1
      have hmα : m ^ (α / 2 - 1) = m ^ (α / 2) / m := Real.rpow_sub_one hm.ne' _
      have hLHS : Wpart β B (plSpec α c N) i m * min (Real.sqrt m) 1 ≤
          4 * Cθ * Real.sqrt C₂ * (1 / aL ^ (α / 2) * m ^ (α / 2 - 1)) := by
        refine key.trans ?_
        have haLp : 0 < aL ^ (α / 2) := Real.rpow_pos_of_pos haL _
        calc Real.sqrt x / (1 + x) * (Cθ * (4 / m)) ≤ Real.sqrt x * (Cθ * (4 / m)) :=
              mul_le_mul_of_nonneg_right hS1 (by positivity)
          _ ≤ (Real.sqrt C₂ * (m ^ (α / 2) / aL ^ (α / 2))) * (Cθ * (4 / m)) := by
              refine mul_le_mul_of_nonneg_right (hxle.trans ?_) (by positivity)
              exact mul_le_mul_of_nonneg_left ht1 (Real.sqrt_nonneg _)
          _ = _ := by rw [hmα]; field_simp
      have hT2' := hT2
      rw [if_pos hm1] at hT2'
      rw [if_pos hm1]
      have hT1' := hT1
      calc _ ≤ 4 * Cθ * Real.sqrt C₂ * (1 / aL ^ (α / 2) * m ^ (α / 2 - 1)) := hLHS
        _ ≤ 4 * Cθ * M0 * (1 / aL ^ (α / 2) * m ^ (α / 2 - 1)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM2 (by positivity)) hT2'
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hT1') (by positivity)
  · have hm1' : 1 < m := not_le.1 hm1
    have hmB' : 1 / (B : ℝ) ≤ m := by
      have : 1 / (B : ℝ) ≤ 1 := by rw [div_le_one hBr]; exact hB1
      linarith
    have hv := (hv1 N B c m hN hB hc hmB' hmγ).1
    have hw : min (Real.sqrt m) 1 = 1 := min_eq_right (by rw [Real.one_le_sqrt]; exact hm1'.le)
    have hq : 1 + 1 / m + 2 / gammaOf N B ≤ 4 := by
      have h2γ : 2 / gammaOf N B ≤ 2 := by rw [div_le_iff₀ hγ]; linarith
      have h1m : 1 / m ≤ 1 := by rw [div_le_one hm]; exact hm1'.le
      linarith
    -- lower bound for x
    have hxlo : Real.sqrt C₁ * t ^ (α / 2) ≤ Real.sqrt x := by
      have : C₁ * t ^ α ≤ x := by
        rw [hxe, ht, Real.div_rpow (by positivity) hρ0.le]
        calc C₁ * (((B : ℝ) * m) ^ α / ρ ^ α) = C₁ * ((B : ℝ) * m) ^ α * ρ ^ (-α) := by
              rw [Real.rpow_neg hρ0.le]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg hρ0.le _)
      calc Real.sqrt C₁ * t ^ (α / 2) = Real.sqrt (C₁ * t ^ α) := by
            rw [Real.sqrt_mul hC₁.le, hsq t ht0]
        _ ≤ Real.sqrt x := Real.sqrt_le_sqrt this
    have hs1 : 0 < Real.sqrt C₁ := Real.sqrt_pos.2 hC₁
    have htp : 0 < t ^ (α / 2) := Real.rpow_pos_of_pos ht0 _
    have hSx' : Real.sqrt x / (1 + x) ≤ 1 / Real.sqrt C₁ * (aU / m) ^ (α / 2) := by
      refine hS2.trans ?_
      have h5 : 1 / Real.sqrt x ≤ 1 / (Real.sqrt C₁ * t ^ (α / 2)) :=
        one_div_le_one_div_of_le (by positivity) hxlo
      refine h5.trans ?_
      have h6 : 1 / t ^ (α / 2) = (1 / t) ^ (α / 2) := by rw [Real.div_rpow zero_le_one ht0.le, Real.one_rpow]
      have h7 : (1 / t) ^ (α / 2) ≤ (aU / m) ^ (α / 2) :=
        Real.rpow_le_rpow (by positivity) htu (by positivity)
      calc 1 / (Real.sqrt C₁ * t ^ (α / 2)) = 1 / Real.sqrt C₁ * (1 / t ^ (α / 2)) := by
            rw [one_div_mul_one_div]
        _ ≤ _ := by rw [h6]; exact mul_le_mul_of_nonneg_left h7 (by positivity)
    have hau : 0 < aU := lt_of_lt_of_le haL (h1.trans h2)
    have hpos' : 0 ≤ m ^ (-(1 / 2 : ℝ)) * (Cθ * (1 + 1 / m + 2 / gammaOf N B)) := by
      have := hγ; positivity
    have hLHS : Wpart β B (plSpec α c N) i m * min (Real.sqrt m) 1 ≤
        4 * Cθ * (1 / Real.sqrt C₁) * (aU ^ (α / 2) * m ^ (-((α + 1) / 2))) := by
      rw [hw, mul_one]
      calc Wpart β B (plSpec α c N) i m
          ≤ Real.sqrt x / (1 + x) * (m ^ (-(1 / 2 : ℝ)) * (Cθ * (1 + 1 / m + 2 / gammaOf N B))) := hWb
        _ ≤ (1 / Real.sqrt C₁ * (aU / m) ^ (α / 2)) * (m ^ (-(1 / 2 : ℝ)) * (Cθ * 4)) := by
            refine mul_le_mul hSx' (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hCθ.le)
              (by positivity)) hpos' (by positivity)
        _ = _ := by
            rw [Real.div_rpow hau.le hm.le, show -((α + 1) / 2) = -(α / 2) + -(1 / 2 : ℝ) by ring,
              Real.rpow_add hm, Real.rpow_neg hm.le (α / 2)]
            field_simp
    have hT1' := hT1
    rw [if_neg hm1]
    rw [if_neg hm1] at hT2
    calc _ ≤ 4 * Cθ * (1 / Real.sqrt C₁) * (aU ^ (α / 2) * m ^ (-((α + 1) / 2))) := hLHS
      _ ≤ 4 * Cθ * M0 * (aU ^ (α / 2) * m ^ (-((α + 1) / 2))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM1 (by positivity)) hT2
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hT1') (by positivity)

private lemma pg9_int_rpow_Ioc {e : ℝ} (he : -1 < e) {b : ℝ} (hb : 0 < b) :
    ∫ m in Ioc (0:ℝ) b, m ^ e = b ^ (e + 1) / (e + 1) := by
  have h := integral_rpow (a := 0) (b := b) (r := e) (Or.inl he)
  rw [intervalIntegral.integral_of_le hb.le] at h
  rw [h, Real.zero_rpow (by linarith)]
  ring

private lemma pg9_P_int {α B ρ : ℝ} (hB : 0 < B) :
    Integrable (fun m : ℝ => if m < 1 / B then Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0)
        (volume.restrict (Ioi (0:ℝ))) ∧
      ∫ m in Ioi (0:ℝ), (if m < 1 / B then Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) =
        2 * ρ ^ (-(α / 2)) := by
  have hb : 0 < 1 / B := by positivity
  set f : ℝ → ℝ := fun m => Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) with hf
  have e1 : (fun m : ℝ => if m < 1 / B then f m else 0) = Set.indicator (Iio (1 / B)) f := by
    funext m
    simp only [Set.indicator_apply, mem_Iio]
  have hfi : IntegrableOn f (Ioc 0 (1 / B)) :=
    (vg_int_rpow_Ioc (e := -(1 / 2 : ℝ)) (by norm_num) (1 / B)).const_mul _
  have hfi' : IntegrableOn f (Ioo 0 (1 / B)) := hfi.mono_set Ioo_subset_Ioc_self
  have e2 : Ioi (0:ℝ) ∩ Iio (1 / B) = Ioo 0 (1 / B) := by
    ext x; simp [and_comm]
  change Integrable (fun m : ℝ => if m < 1 / B then f m else 0) (volume.restrict (Ioi (0:ℝ))) ∧
    ∫ m in Ioi (0:ℝ), (if m < 1 / B then f m else 0) = _
  rw [e1]
  refine ⟨?_, ?_⟩
  · rw [integrable_indicator_iff measurableSet_Iio]
    change Integrable f ((volume.restrict (Ioi (0:ℝ))).restrict (Iio (1 / B)))
    rw [Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, e2]
    exact hfi'
  · rw [setIntegral_indicator measurableSet_Iio, e2, integral_Ioc_eq_integral_Ioo.symm]
    simp only [hf]
    rw [integral_const_mul, pg9_int_rpow_Ioc (by norm_num) hb]
    have hs : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
    have : (1 / B) ^ (-(1 / 2 : ℝ) + 1) = 1 / Real.sqrt B := by
      rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Real.div_rpow zero_le_one hB.le,
        Real.one_rpow, Real.sqrt_eq_rpow]
    rw [this]
    field_simp
    norm_num

set_option maxHeartbeats 800000 in
private lemma pg9_W_top {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C5 : ℝ, 0 < C5 ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ (i : Fin N) (m : ℝ),
      2 ≤ gammaOf N B → gammaOf N B / 2 ≤ m → m < gammaOf N B →
      Wpart β B (plSpec α c N) i m ≤
        C5 * ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ (α / 2) * m ^ (-(1 / 2 : ℝ)) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨Cθ, hCθ, hθ⟩ := pg9_theta_pos hα0 hβ0 hβ1
  obtain ⟨c3, C3, hc3, hC3, hV⟩ := lem_app_pl_finite_inverse_iii hα0
  refine ⟨3 / 2 * Cθ * (1 / Real.sqrt c3), by positivity, fun N B c hN hB hc i m hγ2 hmγ1 hmγ2 => ?_⟩
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by linarith
  have hm0 : 0 < m := by linarith
  have hmem : m ∈ Ioo 0 (gammaOf N B) := ⟨hm0, hmγ2⟩
  obtain ⟨hθ0, hθb⟩ := hθ N B c hN hB hc m hmem
  set ρ : ℝ := ((i : ℕ) : ℝ) + 1 with hρ
  have hρ0 : 0 < ρ := by positivity
  set p : ℝ := m / gammaOf N B with hp
  have hp1 : 1 / 2 ≤ p := by rw [hp, le_div_iff₀ hγ]; linarith
  have hp2 : p < 1 := by rw [hp, div_lt_one hγ]; exact hmγ2
  have hq0 : 0 < 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 / 2 := by linarith
  have hVb := (hV N hN p hp1 hp2).1
  set V := finV α N p with hVdef
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hVb
  have hΛ := eqn_app_pl_Lambda_V (α := α) (N := N) (B := B) c hN hB hc hmem
  rw [← hp, ← hVdef] at hΛ
  set x := plSpec α c N i * partLam B (plSpec α c N) m with hx
  have hxe : x = ((N : ℝ) / ρ) ^ α * V := by
    rw [hx, hΛ]
    unfold plSpec
    rw [← hρ, Real.div_rpow hNr.le hρ0.le, Real.rpow_neg hρ0.le]
    field_simp
  have hx0 : 0 < x := by rw [hxe]; positivity
  have hNρ : 0 < ((N : ℝ) / ρ) ^ (α / 2) := by positivity
  have hsx : Real.sqrt x = ((N : ℝ) / ρ) ^ (α / 2) * Real.sqrt V := by
    rw [hxe, Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (((N : ℝ) / ρ) ^ α),
      ← Real.rpow_mul (by positivity)]
    congr 3; ring
  have hsV : Real.sqrt c3 / Real.sqrt (1 - p) ≤ Real.sqrt V := by
    rw [← Real.sqrt_div hc3.le]
    exact Real.sqrt_le_sqrt hVb
  have hS : Real.sqrt x / (1 + x) ≤ (ρ / (N : ℝ)) ^ (α / 2) * (Real.sqrt (1 - p) / Real.sqrt c3) := by
    have hsxp : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hsxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    calc Real.sqrt x / (1 + x) ≤ Real.sqrt x / x :=
          div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hx0 (by linarith)
      _ = 1 / Real.sqrt x := by
          rw [div_eq_div_iff hx0.ne' hsxp.ne', one_mul]; exact hsxx
      _ ≤ 1 / (((N : ℝ) / ρ) ^ (α / 2) * (Real.sqrt c3 / Real.sqrt (1 - p))) := by
          rw [hsx]
          refine one_div_le_one_div_of_le (by have := Real.sqrt_pos.2 hc3
                                              have := Real.sqrt_pos.2 hq0; positivity) ?_
          exact mul_le_mul_of_nonneg_left hsV hNρ.le
      _ = (ρ / (N : ℝ)) ^ (α / 2) * (Real.sqrt (1 - p) / Real.sqrt c3) := by
          have h1 : ((N : ℝ) / ρ) ^ (α / 2) = ((ρ / (N : ℝ)) ^ (α / 2))⁻¹ := by
            rw [← Real.inv_rpow (by positivity), inv_div]
          have hs3 := Real.sqrt_pos.2 hc3
          have hs4 := Real.sqrt_pos.2 hq0
          rw [h1]; field_simp
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  have hm12 : m ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt m := by
    rw [Real.rpow_neg hm0.le, Real.sqrt_eq_rpow]; simp
  have hWeq : Wpart β B (plSpec α c N) i m = Real.sqrt x / (1 + x) * (1 / Real.sqrt m) *
      (Real.sqrt (1 - p) * thetaN β B (plSpec α c N) m) := by
    unfold Wpart
    rw [← hx, ← hp]
    field_simp
  have hγm : gammaOf N B - m = gammaOf N B * (1 - p) := by
    rw [hp]; field_simp
  have hθ2 : thetaN β B (plSpec α c N) m ≤ Cθ * (1 + 1 / m + 1 / (gammaOf N B * (1 - p))) := by
    rw [← hγm]; exact hθb
  have hS0 : 0 ≤ Real.sqrt x / (1 + x) := by positivity
  have hs4 := Real.sqrt_pos.2 hq0
  have hs3 := Real.sqrt_pos.2 hc3
  have hbr : (1 - p) * (1 + 1 / m + 1 / (gammaOf N B * (1 - p))) ≤ 3 / 2 := by
    have h1m : 1 / m ≤ 1 := by
      rw [div_le_one hm0]; linarith
    have e : (1 - p) * (1 + 1 / m + 1 / (gammaOf N B * (1 - p))) =
        (1 - p) * (1 + 1 / m) + 1 / gammaOf N B := by
      field_simp
    rw [e]
    have : 1 / gammaOf N B ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hγ (by norm_num)]; linarith
    have h2 : (1 - p) * (1 + 1 / m) ≤ 1 / 2 * 2 := by
      apply mul_le_mul hq1 (by linarith) (by positivity) (by norm_num)
    linarith
  rw [hWeq, hm12]
  calc Real.sqrt x / (1 + x) * (1 / Real.sqrt m) * (Real.sqrt (1 - p) * thetaN β B (plSpec α c N) m)
      ≤ (ρ / (N : ℝ)) ^ (α / 2) * (Real.sqrt (1 - p) / Real.sqrt c3) * (1 / Real.sqrt m) *
          (Real.sqrt (1 - p) * (Cθ * (1 + 1 / m + 1 / (gammaOf N B * (1 - p))))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hS (by positivity)) _ (by positivity)
          (by positivity)
        exact mul_le_mul_of_nonneg_left hθ2 hs4.le
    _ = (ρ / (N : ℝ)) ^ (α / 2) * (1 / Real.sqrt c3) * (1 / Real.sqrt m) * Cθ *
          ((1 - p) * (1 + 1 / m + 1 / (gammaOf N B * (1 - p)))) := by
        have h44 : Real.sqrt (1 - p) * Real.sqrt (1 - p) = 1 - p := Real.mul_self_sqrt hq0.le
        set s4 := Real.sqrt (1 - p) with hs4def
        set T := 1 + 1 / m + 1 / (gammaOf N B * (1 - p)) with hT
        rw [← h44]
        field_simp
    _ ≤ (ρ / (N : ℝ)) ^ (α / 2) * (1 / Real.sqrt c3) * (1 / Real.sqrt m) * Cθ * (3 / 2) := by
        apply mul_le_mul_of_nonneg_left hbr (by positivity)
    _ = _ := by ring

private lemma pg9_prod_bound {E1 E2 : Set ℝ} (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    {f : ℝ × ℝ → ℝ} {M1 M2 : ℝ → ℝ} {C : ℝ}
    (hf : IntegrableOn f (E1 ×ˢ E2)) (hM1 : IntegrableOn M1 E1) (hM2 : IntegrableOn M2 E2)
    (hle : ∀ p ∈ E1 ×ˢ E2, f p ≤ C * (M1 p.1 * M2 p.2)) :
    ∫ p in E1 ×ˢ E2, f p ≤ C * ((∫ x in E1, M1 x) * ∫ y in E2, M2 y) := by
  have hprod : IntegrableOn (fun p : ℝ × ℝ => M1 p.1 * M2 p.2) (E1 ×ˢ E2) := by
    have := hM1.mul_prod hM2
    rwa [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have h1 := setIntegral_mono_on hf (hprod.const_mul C) (hE1.prod hE2) hle
  have h2 := setIntegral_prod_mul (μ := volume) (ν := volume) M1 M2 E1 E2
  have h2' : ∫ z in E1 ×ˢ E2, M1 z.1 * M2 z.2 =
      (∫ x in E1, M1 x) * ∫ y in E2, M2 y := by
    rw [Measure.volume_eq_prod]; exact h2
  rw [integral_const_mul, h2'] at h1
  exact h1

private lemma pg9_sumF_le {α β : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ CD : ℝ, 0 < CD ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ (i : Fin N) (s : Finset ℤ)
      (m₁ m₂ δ0 : ℝ), m₁ ∈ Ioo 0 (gammaOf N B) → m₂ ∈ Ioo 0 (gammaOf N B) → 0 < δ0 →
      (∀ ℓ : ℤ, δ0 ≤ deltaN β B (plSpec α c N) ℓ m₁ m₂) →
      0 ≤ ∑ ℓ ∈ s, lagIntegrand β B (plSpec α c N) i ℓ m₁ m₂ ∧
      ∑ ℓ ∈ s, lagIntegrand β B (plSpec α c N) i ℓ m₁ m₂ ≤
        CD / δ0 * ((Wpart β B (plSpec α c N) i m₁ * min (Real.sqrt m₁) 1) *
          (Wpart β B (plSpec α c N) i m₂ * min (Real.sqrt m₂) 1)) := by
  obtain ⟨C, hC0, hC⟩ := vs_D_bd hβ0 hβ1
  refine ⟨C + 1, by linarith, fun N B c hN hB hc i s m₁ m₂ δ0 hm₁ hm₂ hδ0 hΔ => ?_⟩
  have hW1 := pg9_W_nonneg hα0 hβ0 hβ1 hN hB hc i hm₁
  have hW2 := pg9_W_nonneg hα0 hβ0 hβ1 hN hB hc i hm₂
  obtain ⟨hQ1, -⟩ := vs_Qm hβ0 hβ1 hm₁.1
  obtain ⟨hQ2, -⟩ := vs_Qm hβ0 hβ1 hm₂.1
  have hD : ∀ ℓ : ℤ, 0 ≤ DLag β (Qm β m₁) (Qm β m₂) ℓ := fun ℓ =>
    vs_DLag_nonneg hβ0 hβ1 hQ1.le hQ2.le ℓ
  have hw1 : 0 ≤ min (Real.sqrt m₁) 1 := le_min (Real.sqrt_nonneg _) zero_le_one
  have hw2 : 0 ≤ min (Real.sqrt m₂) 1 := le_min (Real.sqrt_nonneg _) zero_le_one
  have hterm : ∀ ℓ ∈ s, 0 ≤ lagIntegrand β B (plSpec α c N) i ℓ m₁ m₂ ∧
      lagIntegrand β B (plSpec α c N) i ℓ m₁ m₂ ≤
        Wpart β B (plSpec α c N) i m₁ * Wpart β B (plSpec α c N) i m₂ *
          DLag β (Qm β m₁) (Qm β m₂) ℓ / δ0 := by
    intro ℓ _
    have hΔ0 : 0 < deltaN β B (plSpec α c N) ℓ m₁ m₂ := lt_of_lt_of_le hδ0 (hΔ ℓ)
    unfold lagIntegrand lagNumer
    refine ⟨by have := hD ℓ; positivity, ?_⟩
    exact div_le_div_of_nonneg_left (by have := hD ℓ; positivity) hδ0 (hΔ ℓ)
  refine ⟨Finset.sum_nonneg (fun ℓ hℓ => (hterm ℓ hℓ).1), ?_⟩
  calc ∑ ℓ ∈ s, lagIntegrand β B (plSpec α c N) i ℓ m₁ m₂
      ≤ ∑ ℓ ∈ s, Wpart β B (plSpec α c N) i m₁ * Wpart β B (plSpec α c N) i m₂ *
          DLag β (Qm β m₁) (Qm β m₂) ℓ / δ0 := Finset.sum_le_sum fun ℓ hℓ => (hterm ℓ hℓ).2
    _ = Wpart β B (plSpec α c N) i m₁ * Wpart β B (plSpec α c N) i m₂ *
          (∑ ℓ ∈ s, DLag β (Qm β m₁) (Qm β m₂) ℓ) / δ0 := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
    _ ≤ Wpart β B (plSpec α c N) i m₁ * Wpart β B (plSpec α c N) i m₂ *
          (C * min (Real.sqrt m₁) 1 * min (Real.sqrt m₂) 1) / δ0 := by
        apply div_le_div_of_nonneg_right _ hδ0.le
        exact mul_le_mul_of_nonneg_left (hC m₁ m₂ hm₁.1 hm₂.1 s) (by positivity)
    _ ≤ (C + 1) / δ0 * ((Wpart β B (plSpec α c N) i m₁ * min (Real.sqrt m₁) 1) *
          (Wpart β B (plSpec α c N) i m₂ * min (Real.sqrt m₂) 1)) := by
        have : 0 ≤ (Wpart β B (plSpec α c N) i m₁ * min (Real.sqrt m₁) 1) *
            (Wpart β B (plSpec α c N) i m₂ * min (Real.sqrt m₂) 1) := by positivity
        have e : Wpart β B (plSpec α c N) i m₁ * Wpart β B (plSpec α c N) i m₂ *
          (C * min (Real.sqrt m₁) 1 * min (Real.sqrt m₂) 1) / δ0 =
            C / δ0 * ((Wpart β B (plSpec α c N) i m₁ * min (Real.sqrt m₁) 1) *
          (Wpart β B (plSpec α c N) i m₂ * min (Real.sqrt m₂) 1)) := by ring
        rw [e]
        refine mul_le_mul_of_nonneg_right ?_ this
        exact div_le_div_of_nonneg_right (by linarith) hδ0.le

private lemma pg9_delta_R {α β : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) {c : ℝ} (hc : 0 < c) (ℓ : ℤ) {m₁ m₂ : ℝ}
    (hm₁ : m₁ ∈ Ioo 0 (gammaOf N B)) (hm₂ : m₂ ∈ Ioo 0 (gammaOf N B))
    (hsmall : min m₁ m₂ ≤ gammaOf N B / 8) (hbig : gammaOf N B / 2 ≤ max m₁ m₂) :
    1 / 2 ≤ deltaN β B (plSpec α c N) ℓ m₁ m₂ := by
  have h := lem_app_pl_determinant_iii hα0 hβ0 hβ1 N B c hN hB hc ℓ m₁ m₂ hm₁ hm₂
  have hγ : 0 < gammaOf N B := lt_trans hm₁.1 hm₁.2
  have hp : 0 < min m₁ m₂ := lt_min hm₁.1 hm₂.1
  have hq : 0 < max m₁ m₂ := lt_max_of_lt_left hm₁.1
  have h1 : min m₁ m₂ / max m₁ m₂ ≤ 1 / 4 := by
    rw [div_le_iff₀ hq]; linarith
  have h2 : 2 * min m₁ m₂ / gammaOf N B ≤ 1 / 4 := by
    rw [div_le_iff₀ hγ]; linarith
  linarith [h.2]

private lemma pg9_region {α β : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ CD : ℝ, 0 < CD ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ (i : Fin N) (s : Finset ℤ)
      (E1 E2 : Set ℝ) (M1 M2 : ℝ → ℝ) (δ0 : ℝ), MeasurableSet E1 → MeasurableSet E2 →
      E1 ⊆ Ioo 0 (gammaOf N B) → E2 ⊆ Ioo 0 (gammaOf N B) → 0 < δ0 →
      IntegrableOn (fun p : ℝ × ℝ => ∑ ℓ ∈ s, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2) (E1 ×ˢ E2) →
      IntegrableOn M1 E1 → IntegrableOn M2 E2 →
      (∀ m ∈ E1, Wpart β B (plSpec α c N) i m * min (Real.sqrt m) 1 ≤ M1 m) →
      (∀ m ∈ E2, Wpart β B (plSpec α c N) i m * min (Real.sqrt m) 1 ≤ M2 m) →
      (∀ p ∈ E1 ×ˢ E2, ∀ ℓ : ℤ, δ0 ≤ deltaN β B (plSpec α c N) ℓ p.1 p.2) →
      ∫ p in E1 ×ˢ E2, ∑ ℓ ∈ s, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 ≤
        CD / δ0 * ((∫ x in E1, M1 x) * ∫ y in E2, M2 y) := by
  obtain ⟨CD, hCD, h⟩ := pg9_sumF_le hα0 hβ0 hβ1
  refine ⟨CD, hCD, fun N B c hN hB hc i s E1 E2 M1 M2 δ0 hE1 hE2 hs1 hs2 hδ0 hG hM1 hM2 hk1 hk2 hΔ => ?_⟩
  refine pg9_prod_bound hE1 hE2 hG hM1 hM2 (fun p hp => ?_)
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨-, hle⟩ := h N B c hN hB hc i s p.1 p.2 δ0 (hs1 hp1) (hs2 hp2) hδ0 (fun ℓ => hΔ p ⟨hp1, hp2⟩ ℓ)
  refine hle.trans ?_
  have hW1 := pg9_W_nonneg hα0 hβ0 hβ1 hN hB hc i (hs1 hp1)
  have hW2 := pg9_W_nonneg hα0 hβ0 hβ1 hN hB hc i (hs2 hp2)
  have hw1 : 0 ≤ min (Real.sqrt p.1) 1 := le_min (Real.sqrt_nonneg _) zero_le_one
  have hw2 : 0 ≤ min (Real.sqrt p.2) 1 := le_min (Real.sqrt_nonneg _) zero_le_one
  have e : CD / δ0 * ((Wpart β B (plSpec α c N) i p.1 * min (Real.sqrt p.1) 1) *
      (Wpart β B (plSpec α c N) i p.2 * min (Real.sqrt p.2) 1)) ≤
      CD / δ0 * (M1 p.1 * M2 p.2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul (hk1 p.1 hp1) (hk2 p.2 hp2) (by positivity)
      (le_trans (by positivity) (hk1 p.1 hp1))
  exact e.trans (le_of_eq (by ring))

private lemma pg9_delta_pos {α β : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) {c : ℝ} (hc : 0 < c) (ℓ : ℤ) {m₁ m₂ : ℝ}
    (hm₁ : m₁ ∈ Ioo 0 (gammaOf N B)) (hm₂ : m₂ ∈ Ioo 0 (gammaOf N B)) :
    0 < deltaN β B (plSpec α c N) ℓ m₁ m₂ := by
  obtain ⟨cα, hcα, hch⟩ := lem_app_pl_determinant_ii_chain hα0
  have h3 := hch N B c hN hB hc m₁ m₂ hm₁ hm₂
  have h4 := lem_app_pl_determinant_ii (β := β) hα0 hβ0 hβ1 N B c hN hB hc ℓ m₁ m₂ hm₁ hm₂
  have hγ : 0 < gammaOf N B := lt_trans hm₁.1 hm₁.2
  have e1 : 0 < 1 - m₁ / gammaOf N B := by
    have : m₁ / gammaOf N B < 1 := by rw [div_lt_one hγ]; exact hm₁.2
    linarith
  have e2 : 0 < 1 - m₂ / gammaOf N B := by
    have : m₂ / gammaOf N B < 1 := by rw [div_lt_one hγ]; exact hm₂.2
    linarith
  have : 0 < cα * ((1 - m₁ / gammaOf N B) * (1 - m₂ / gammaOf N B)) := by positivity
  linarith

private lemma pg9_F_nonneg {α β : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) {c : ℝ} (hc : 0 < c) (i : Fin N) (ℓ : ℤ) {m₁ m₂ : ℝ}
    (hm₁ : m₁ ∈ Ioo 0 (gammaOf N B)) (hm₂ : m₂ ∈ Ioo 0 (gammaOf N B)) :
    0 ≤ lagIntegrand β B (plSpec α c N) i ℓ m₁ m₂ := by
  have hΔ := pg9_delta_pos hα0 hβ0 hβ1 hN hB hc ℓ hm₁ hm₂
  have hW1 := pg9_W_nonneg hα0 hβ0 hβ1 hN hB hc i hm₁
  have hW2 := pg9_W_nonneg hα0 hβ0 hβ1 hN hB hc i hm₂
  obtain ⟨hQ1, -⟩ := vs_Qm hβ0 hβ1 hm₁.1
  obtain ⟨hQ2, -⟩ := vs_Qm hβ0 hβ1 hm₂.1
  have hD := vs_DLag_nonneg hβ0 hβ1 hQ1.le hQ2.le ℓ
  unfold lagIntegrand lagNumer
  positivity

private lemma pg9_lagTerm_prod {β : ℝ} {B : ℕ} {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (I J : Set ℝ) (ℓ : ℤ)
    (hint : IntegrableOn (fun p : ℝ × ℝ => lagIntegrand β B μ i ℓ p.1 p.2) (I ×ˢ J)) :
    lagTerm β B μ i I J ℓ = ∫ p in I ×ˢ J, lagIntegrand β B μ i ℓ p.1 p.2 := by
  unfold lagTerm
  have h : Integrable (Function.uncurry fun a b : ℝ => lagIntegrand β B μ i ℓ a b)
      ((volume.restrict I).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hint
  have := integral_prod (Function.uncurry fun a b : ℝ => lagIntegrand β B μ i ℓ a b) h
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at this
  exact this.symm

private lemma pg9_lagTerm_Ico_Ioo {β : ℝ} {B : ℕ} {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (a b : ℝ) (ℓ : ℤ) :
    lagTerm β B μ i (Ico a b) (Ico a b) ℓ = lagTerm β B μ i (Ioo a b) (Ioo a b) ℓ := by
  unfold lagTerm
  have h1 : ∀ m₁ : ℝ, ∫ m₂ in Ico a b, lagIntegrand β B μ i ℓ m₁ m₂ =
      ∫ m₂ in Ioo a b, lagIntegrand β B μ i ℓ m₁ m₂ := fun m₁ =>
    setIntegral_congr_set Ioo_ae_eq_Ico.symm
  simp_rw [h1]
  exact setIntegral_congr_set Ioo_ae_eq_Ico.symm

private lemma pg9_regS {α β : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) {c : ℝ} (hc : 0 < c) (i : Fin N) (s : Finset ℤ) (Cup : ℝ)
    (hint : ∀ ℓ : ℤ, IntegrableOn (fun p : ℝ × ℝ => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2)
      (Ico (gammaOf N B / 8) (gammaOf N B) ×ˢ Ico (gammaOf N B / 8) (gammaOf N B)))
    (hsum : Summable (fun ℓ : ℤ => lagTerm β B (plSpec α c N) i
      (Ico (gammaOf N B / 8) (gammaOf N B)) (Ico (gammaOf N B / 8) (gammaOf N B)) ℓ))
    (hv : vIJ β B (plSpec α c N) i (Ico (gammaOf N B / 8) (gammaOf N B))
      (Ico (gammaOf N B / 8) (gammaOf N B)) ≤
        Cup * gammaOf N B * ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α) :
    ∫ p in Ioo (gammaOf N B / 8) (gammaOf N B) ×ˢ Ioo (gammaOf N B / 8) (gammaOf N B),
        ∑ ℓ ∈ s, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 ≤
      Real.pi ^ 2 * (Cup * gammaOf N B * ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by unfold gammaOf; positivity
  set S : Set (ℝ × ℝ) := Ioo (gammaOf N B / 8) (gammaOf N B) ×ˢ Ioo (gammaOf N B / 8) (gammaOf N B)
    with hS
  have hSsub : S ⊆ Ico (gammaOf N B / 8) (gammaOf N B) ×ˢ Ico (gammaOf N B / 8) (gammaOf N B) :=
    prod_mono Ioo_subset_Ico_self Ioo_subset_Ico_self
  have hSint : ∀ ℓ : ℤ, IntegrableOn (fun p : ℝ × ℝ => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2) S :=
    fun ℓ => (hint ℓ).mono_set hSsub
  have hSpos : ∀ p ∈ S, ∀ ℓ : ℤ, 0 ≤ lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 := by
    intro p hp ℓ
    exact pg9_F_nonneg hα0 hβ0 hβ1 hN hB hc i ℓ ⟨by linarith [hp.1.1], hp.1.2⟩
      ⟨by linarith [hp.2.1], hp.2.2⟩
  have hterm : ∀ ℓ : ℤ, ∫ p in S, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 =
      lagTerm β B (plSpec α c N) i (Ico (gammaOf N B / 8) (gammaOf N B))
        (Ico (gammaOf N B / 8) (gammaOf N B)) ℓ := by
    intro ℓ
    rw [pg9_lagTerm_Ico_Ioo, pg9_lagTerm_prod _ i _ _ ℓ (hSint ℓ)]
  rw [integral_finset_sum _ (fun ℓ _ => hSint ℓ)]
  simp only [hterm]
  have hnn : ∀ ℓ : ℤ, 0 ≤ lagTerm β B (plSpec α c N) i (Ico (gammaOf N B / 8) (gammaOf N B))
      (Ico (gammaOf N B / 8) (gammaOf N B)) ℓ := fun ℓ => by
    rw [← hterm ℓ]
    exact setIntegral_nonneg (hS ▸ measurableSet_Ioo.prod measurableSet_Ioo) (hSpos · · ℓ)
  calc ∑ ℓ ∈ s, lagTerm β B (plSpec α c N) i (Ico (gammaOf N B / 8) (gammaOf N B))
        (Ico (gammaOf N B / 8) (gammaOf N B)) ℓ
      ≤ ∑' ℓ : ℤ, lagTerm β B (plSpec α c N) i (Ico (gammaOf N B / 8) (gammaOf N B))
        (Ico (gammaOf N B / 8) (gammaOf N B)) ℓ := hsum.sum_le_tsum s (fun ℓ _ => hnn ℓ)
    _ = Real.pi ^ 2 * vIJ β B (plSpec α c N) i (Ico (gammaOf N B / 8) (gammaOf N B))
        (Ico (gammaOf N B / 8) (gammaOf N B)) := by
        unfold vIJ
        have : Real.pi ^ 2 ≠ 0 := by positivity
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)

private lemma pg9_W_le_Q {α β : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ Cθ : ℝ, 0 < Cθ ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → 2 ≤ gammaOf N B →
      ∀ (i : Fin N) (δ m : ℝ), 0 < δ → δ ≤ m → m ≤ gammaOf N B / 2 →
      0 ≤ Wpart β B (plSpec α c N) i m ∧
      Wpart β B (plSpec α c N) i m ≤ Cθ * (δ ^ (-(1 / 2 : ℝ)) * (2 + 1 / δ)) := by
  obtain ⟨Cθ, hCθ, hW⟩ := pg9_W_core hα0 hβ0 hβ1
  refine ⟨Cθ, hCθ, fun N B c hN hB hc hγ i δ m hδ hδm hmγ => ?_⟩
  have hm : 0 < m := lt_of_lt_of_le hδ hδm
  obtain ⟨h0, h1⟩ := hW N B c hN hB hc i m hm hmγ
  refine ⟨h0, h1.trans ?_⟩
  set x := plSpec α c N i * partLam B (plSpec α c N) m with hx
  have hmem : m ∈ Ioo 0 (gammaOf N B) := ⟨hm, by linarith⟩
  have hx0 : 0 < x := mul_pos (pg9_plSpec_pos (α := α) hc N i) (pg9_lam_pos (α := α) hN hB hc hmem)
  have hS : Real.sqrt x / (1 + x) ≤ 1 := by
    have h2 : Real.sqrt x ≤ 1 + x := by
      nlinarith [Real.sq_sqrt hx0.le, sq_nonneg (Real.sqrt x - 1), Real.sqrt_nonneg x]
    rw [div_le_one (by linarith)]; exact h2
  have hmh : m ^ (-(1 / 2 : ℝ)) ≤ δ ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hδ hδm (by norm_num)
  have hγ2 : 2 / gammaOf N B ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have h1m : 1 / m ≤ 1 / δ := one_div_le_one_div_of_le hδ hδm
  have hpos : 0 ≤ m ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hm.le _
  have hpos2 : 0 ≤ δ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hδ.le _
  calc Real.sqrt x / (1 + x) * (m ^ (-(1 / 2 : ℝ)) * (Cθ * (1 + 1 / m + 2 / gammaOf N B)))
      ≤ 1 * (δ ^ (-(1 / 2 : ℝ)) * (Cθ * (2 + 1 / δ))) := by
        apply mul_le_mul hS _ (by positivity) zero_le_one
        apply mul_le_mul hmh _ (by have := hγ2; have : 0 ≤ 1 / m := by positivity
                                   have : 0 ≤ 2 / gammaOf N B := by positivity
                                   positivity) hpos2
        exact mul_le_mul_of_nonneg_left (by linarith) hCθ.le
    _ = Cθ * (δ ^ (-(1 / 2 : ℝ)) * (2 + 1 / δ)) := by ring

private lemma pg9_F_le_Q {α β : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ CF : ℝ, 0 < CF ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → 2 ≤ gammaOf N B →
      ∀ (i : Fin N) (ℓ : ℤ) (δ m₁ m₂ : ℝ), 0 < δ → δ ≤ m₁ → δ ≤ m₂ →
      m₁ ≤ gammaOf N B / 2 → m₂ ≤ gammaOf N B / 2 →
      0 ≤ lagIntegrand β B (plSpec α c N) i ℓ m₁ m₂ ∧
      lagIntegrand β B (plSpec α c N) i ℓ m₁ m₂ ≤
        CF * (δ ^ (-(1 / 2 : ℝ)) * (2 + 1 / δ)) ^ 2 * DLag β (Qm β m₁) (Qm β m₂) ℓ := by
  obtain ⟨Cθ, hCθ, hW⟩ := pg9_W_le_Q hα0 hβ0 hβ1
  obtain ⟨cα, hcα, hδ⟩ := pg9_delta_lb hα0 hβ0 hβ1
  refine ⟨Cθ ^ 2 * (4 / cα), by positivity, fun N B c hN hB hc hγ i ℓ δ m₁ m₂ hδ0 h1 h2 h3 h4 => ?_⟩
  have hm₁ : m₁ ∈ Ioo 0 (gammaOf N B) := ⟨lt_of_lt_of_le hδ0 h1, by linarith⟩
  have hm₂ : m₂ ∈ Ioo 0 (gammaOf N B) := ⟨lt_of_lt_of_le hδ0 h2, by linarith⟩
  obtain ⟨hW10, hW1⟩ := hW N B c hN hB hc hγ i δ m₁ hδ0 h1 h3
  obtain ⟨hW20, hW2⟩ := hW N B c hN hB hc hγ i δ m₂ hδ0 h2 h4
  have hΔ := hδ N B c hN hB hc ℓ m₁ m₂ hm₁ hm₂ h3 h4
  have hΔ0 : 0 < deltaN β B (plSpec α c N) ℓ m₁ m₂ := lt_of_lt_of_le (by positivity) hΔ
  obtain ⟨hQ1, -⟩ := vs_Qm hβ0 hβ1 hm₁.1
  obtain ⟨hQ2, -⟩ := vs_Qm hβ0 hβ1 hm₂.1
  have hD := vs_DLag_nonneg hβ0 hβ1 hQ1.le hQ2.le ℓ
  unfold lagIntegrand lagNumer
  refine ⟨by positivity, ?_⟩
  set D := DLag β (Qm β m₁) (Qm β m₂) ℓ
  have e1 : D / deltaN β B (plSpec α c N) ℓ m₁ m₂ ≤ (4 / cα) * D := by
    rw [div_le_iff₀ hΔ0]
    have : 1 ≤ (4 / cα) * deltaN β B (plSpec α c N) ℓ m₁ m₂ := by
      have := mul_le_mul_of_nonneg_left hΔ (by positivity : 0 ≤ 4 / cα)
      have e : 4 / cα * (cα / 4) = 1 := by field_simp
      linarith
    nlinarith
  have e2 : Wpart β B (plSpec α c N) i m₁ * Wpart β B (plSpec α c N) i m₂ * D /
      deltaN β B (plSpec α c N) ℓ m₁ m₂ =
      Wpart β B (plSpec α c N) i m₁ * Wpart β B (plSpec α c N) i m₂ *
        (D / deltaN β B (plSpec α c N) ℓ m₁ m₂) := by ring
  rw [e2]
  have hb : 0 ≤ δ ^ (-(1 / 2 : ℝ)) * (2 + 1 / δ) := by positivity
  calc Wpart β B (plSpec α c N) i m₁ * Wpart β B (plSpec α c N) i m₂ *
        (D / deltaN β B (plSpec α c N) ℓ m₁ m₂)
      ≤ (Cθ * (δ ^ (-(1 / 2 : ℝ)) * (2 + 1 / δ))) * (Cθ * (δ ^ (-(1 / 2 : ℝ)) * (2 + 1 / δ))) *
          ((4 / cα) * D) := by
        apply mul_le_mul (mul_le_mul hW1 hW2 hW20 (by positivity)) e1 (by positivity) (by positivity)
    _ = _ := by ring

open Muon.DetEquiv ProbabilityTheory in
private lemma pg9_D_intQ {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {δ R : ℝ} (hδ : 0 < δ) :
    (∀ ℓ : ℤ, IntegrableOn (fun p : ℝ × ℝ => DLag β (Qm β p.1) (Qm β p.2) ℓ)
      (Icc δ R ×ˢ Icc δ R)) ∧
    Summable (fun ℓ : ℤ => ∫ p in Icc δ R ×ˢ Icc δ R, DLag β (Qm β p.1) (Qm β p.2) ℓ) := by
  obtain ⟨C, hC0, hC⟩ := vs_D_bd hβ0 hβ1
  set Q : Set (ℝ × ℝ) := Icc δ R ×ˢ Icc δ R with hQ
  have hQsub : Q ⊆ Ioi 0 ×ˢ Ioi 0 := fun p hp => ⟨lt_of_lt_of_le hδ hp.1.1, lt_of_lt_of_le hδ hp.2.1⟩
  have hQm : MeasurableSet Q := measurableSet_Icc.prod measurableSet_Icc
  have hfin : volume Q < ⊤ := by
    rw [hQ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  have hbd : ∀ p ∈ Q, ∀ ℓ : ℤ, DLag β (Qm β p.1) (Qm β p.2) ℓ ≤ C := by
    intro p hp ℓ
    have hp1 : 0 < p.1 := lt_of_lt_of_le hδ hp.1.1
    have hp2 : 0 < p.2 := lt_of_lt_of_le hδ hp.2.1
    have := hC p.1 p.2 hp1 hp2 {ℓ}
    rw [Finset.sum_singleton] at this
    have h1 : min (Real.sqrt p.1) 1 ≤ 1 := min_le_right _ _
    have h2 : min (Real.sqrt p.2) 1 ≤ 1 := min_le_right _ _
    have h3 : 0 ≤ min (Real.sqrt p.1) 1 := le_min (Real.sqrt_nonneg _) zero_le_one
    have h4 : 0 ≤ min (Real.sqrt p.2) 1 := le_min (Real.sqrt_nonneg _) zero_le_one
    calc _ ≤ C * min (Real.sqrt p.1) 1 * min (Real.sqrt p.2) 1 := this
      _ ≤ C * 1 * 1 := by gcongr
      _ = C := by ring
  have hnn : ∀ p ∈ Q, ∀ ℓ : ℤ, 0 ≤ DLag β (Qm β p.1) (Qm β p.2) ℓ := by
    intro p hp ℓ
    obtain ⟨h1, -⟩ := vs_Qm hβ0 hβ1 (lt_of_lt_of_le hδ hp.1.1)
    obtain ⟨h2, -⟩ := vs_Qm hβ0 hβ1 (lt_of_lt_of_le hδ hp.2.1)
    exact vs_DLag_nonneg hβ0 hβ1 h1.le h2.le ℓ
  have hint : ∀ ℓ : ℤ, IntegrableOn (fun p : ℝ × ℝ => DLag β (Qm β p.1) (Qm β p.2) ℓ) Q := by
    intro ℓ
    have hae := (vs_D_aem hβ0 hβ1 ℓ)
    have hle : (volume.restrict Q : Measure (ℝ × ℝ)) ≤
        (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact Measure.restrict_mono hQsub le_rfl
    have hae' := hae.mono_measure hle
    haveI : IsFiniteMeasure (volume.restrict Q) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
    refine Integrable.mono' (g := fun _ => C) (integrable_const C) hae'.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hQm] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn p hp ℓ)]
    exact hbd p hp ℓ
  refine ⟨hint, ?_⟩
  have hnn' : ∀ ℓ : ℤ, 0 ≤ ∫ p in Q, DLag β (Qm β p.1) (Qm β p.2) ℓ := fun ℓ =>
    setIntegral_nonneg hQm (hnn · · ℓ)
  have hsumbd : ∀ p ∈ Q, ∀ s : Finset ℤ, ∑ ℓ ∈ s, DLag β (Qm β p.1) (Qm β p.2) ℓ ≤ C := by
    intro p hp s
    have hp1 : 0 < p.1 := lt_of_lt_of_le hδ hp.1.1
    have hp2 : 0 < p.2 := lt_of_lt_of_le hδ hp.2.1
    have := hC p.1 p.2 hp1 hp2 s
    have h1 : min (Real.sqrt p.1) 1 ≤ 1 := min_le_right _ _
    have h2 : min (Real.sqrt p.2) 1 ≤ 1 := min_le_right _ _
    have h3 : 0 ≤ min (Real.sqrt p.1) 1 := le_min (Real.sqrt_nonneg _) zero_le_one
    have h4 : 0 ≤ min (Real.sqrt p.2) 1 := le_min (Real.sqrt_nonneg _) zero_le_one
    calc _ ≤ C * min (Real.sqrt p.1) 1 * min (Real.sqrt p.2) 1 := this
      _ ≤ C * 1 * 1 := by gcongr
      _ = C := by ring
  refine summable_of_sum_le (c := C * (volume Q).toReal) hnn' (fun s => ?_)
  rw [← integral_finset_sum _ (fun ℓ _ => hint ℓ)]
  have hc : IntegrableOn (fun _ : ℝ × ℝ => C) Q := integrableOn_const hfin.ne
  calc ∫ p in Q, ∑ ℓ ∈ s, DLag β (Qm β p.1) (Qm β p.2) ℓ ≤ ∫ p in Q, C :=
        setIntegral_mono_on (integrable_finset_sum _ (fun ℓ _ => hint ℓ)) hc hQm
          (fun p hp => hsumbd p hp s)
    _ = C * (volume Q).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl

open Muon.DetEquiv ProbabilityTheory in
private lemma pg9_compact_lim {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (i : ∀ n, Fin (N n)) (X0 : ℝ)
    (hX0 : 0 < X0)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 X0)) {δ Rr : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => ∑' ℓ : ℤ, ∫ p in Icc δ Rr ×ˢ Icc δ Rr,
        lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2) atTop
      (𝓝 (∑' ℓ : ℤ, ∫ p in Icc δ Rr ×ˢ Icc δ Rr,
        Real.sqrt (profZeta α X0 p.1 * (1 - profZeta α X0 p.1) *
              (profZeta α X0 p.2 * (1 - profZeta α X0 p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2))) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨CF, hCF, hF⟩ := pg9_F_le_Q hα0 R.hβ0 R.hβ1
  obtain ⟨hDint, hDsum⟩ := pg9_D_intQ (δ := δ) (R := Rr) R.hβ0 R.hβ1 hδ
  set Q : Set (ℝ × ℝ) := Icc δ Rr ×ˢ Icc δ Rr with hQ
  have hQm : MeasurableSet Q := measurableSet_Icc.prod measurableSet_Icc
  have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  set CF' : ℝ := CF * (δ ^ (-(1 / 2 : ℝ)) * (2 + 1 / δ)) ^ 2 with hCF'
  have hCF'0 : 0 ≤ CF' := by positivity
  have hev : ∀ᶠ n in atTop, 2 ≤ gammaOf (N n) (B n) ∧ 2 * Rr < gammaOf (N n) (B n) :=
    (hg.eventually_ge_atTop 2).and (hg.eventually_gt_atTop (2 * Rr))
  have hper : ∀ ℓ : ℤ, Tendsto (fun n => ∫ p in Q,
      lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2) atTop
      (𝓝 (∫ p in Q, Real.sqrt (profZeta α X0 p.1 * (1 - profZeta α X0 p.1) *
              (profZeta α X0 p.2 * (1 - profZeta α X0 p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2))) := by
    intro ℓ
    have h1 : ∀ᶠ n in atTop, AEStronglyMeasurable (fun p : ℝ × ℝ =>
        lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2) (volume.restrict Q) := by
      filter_upwards [hev] with n hn
      have hint := (lem_app_pl_age_iv hα0 R.hβ0 R.hβ1 (N n) (B n) (c n) (R.hNpos n) (R.hBpos n)
        (R.hcpos n) (i n)).2.2.1 ℓ
      refine (hint.mono_set ?_).aestronglyMeasurable
      intro p hp
      exact ⟨⟨lt_of_lt_of_le hδ hp.1.1, by linarith [hp.1.2]⟩, ⟨lt_of_lt_of_le hδ hp.2.1, by linarith [hp.2.2]⟩⟩
    have h2 : ∀ᶠ n in atTop, ∀ᵐ p ∂(volume.restrict Q),
        ‖lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2‖ ≤
          CF' * DLag β (Qm β p.1) (Qm β p.2) ℓ := by
      filter_upwards [hev] with n hn
      filter_upwards [ae_restrict_mem hQm] with p hp
      obtain ⟨h0, h1⟩ := hF (N n) (B n) (c n) (R.hNpos n) (R.hBpos n) (R.hcpos n) hn.1 (i n) ℓ δ
        p.1 p.2 hδ hp.1.1 hp.2.1 (by linarith [hp.1.2]) (by linarith [hp.2.2])
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1
    have h3 : ∀ᵐ p ∂(volume.restrict Q), Tendsto (fun n =>
        lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2) atTop
        (𝓝 (Real.sqrt (profZeta α X0 p.1 * (1 - profZeta α X0 p.1) *
              (profZeta α X0 p.2 * (1 - profZeta α X0 p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2))) := by
      filter_upwards [ae_restrict_mem hQm] with p hp
      exact pg9_term_lim R hα1 i X0 hX0 hX (lt_of_lt_of_le hδ hp.1.1) (lt_of_lt_of_le hδ hp.2.1) ℓ
    exact tendsto_integral_filter_of_dominated_convergence
      (fun p : ℝ × ℝ => CF' * DLag β (Qm β p.1) (Qm β p.2) ℓ) h1 h2 ((hDint ℓ).const_mul CF') h3
  refine tendsto_tsum_of_dominated_convergence (bound := fun ℓ => CF' * ∫ p in Q,
    DLag β (Qm β p.1) (Qm β p.2) ℓ) (hDsum.mul_left CF') hper ?_
  filter_upwards [hev] with n hn ℓ
  have hQsub : ∀ p ∈ Q, ∀ ℓ : ℤ, 0 ≤ lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2 ∧
      lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2 ≤
        CF' * DLag β (Qm β p.1) (Qm β p.2) ℓ := by
    intro p hp ℓ
    exact hF (N n) (B n) (c n) (R.hNpos n) (R.hBpos n) (R.hcpos n) hn.1 (i n) ℓ δ
        p.1 p.2 hδ hp.1.1 hp.2.1 (by linarith [hp.1.2]) (by linarith [hp.2.2])
  have hnn : 0 ≤ ∫ p in Q, lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2 :=
    setIntegral_nonneg hQm (fun p hp => (hQsub p hp ℓ).1)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, ← integral_const_mul]
  have hint := (lem_app_pl_age_iv hα0 R.hβ0 R.hβ1 (N n) (B n) (c n) (R.hNpos n) (R.hBpos n)
        (R.hcpos n) (i n)).2.2.1 ℓ
  refine setIntegral_mono_on (hint.mono_set ?_) ((hDint ℓ).const_mul CF') hQm
    (fun p hp => (hQsub p hp ℓ).2)
  intro p hp
  exact ⟨⟨lt_of_lt_of_le hδ hp.1.1, by linarith [hp.1.2]⟩, ⟨lt_of_lt_of_le hδ hp.2.1, by linarith [hp.2.2]⟩⟩

open Muon.DetEquiv ProbabilityTheory in
private lemma pg9_cont_trunc {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    {X : ℝ} (hX : 0 < X) :
    Tendsto (fun k : ℕ => ∑' ℓ : ℤ, ∫ p in Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ
        Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1),
        Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2)) atTop
      (𝓝 (∑' ℓ : ℤ, ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
        Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
          Real.sqrt (u * v) *
          (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v))) := by
  obtain ⟨hint, hsum⟩ := vs_finite_all hα1 hβ0 hβ1 X hX
  obtain ⟨K, hK0, hK⟩ := vs_theta_bd hα1 hβ0 hβ1
  obtain ⟨bl, hbl, hbls, hbd⟩ := vs_core hα1 hβ0 hβ1 hX (le_refl X) hK
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  have hμ' : μ = volume.restrict (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := by
    rw [hμ, Measure.prod_restrict, ← Measure.volume_eq_prod]
  set Fl : ℤ → ℝ × ℝ → ℝ := fun ℓ p =>
    Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2) with hFl
  set Qk : ℕ → Set (ℝ × ℝ) := fun k => Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ
        Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) with hQk
  have hQm : ∀ k, MeasurableSet (Qk k) := fun k => measurableSet_Icc.prod measurableSet_Icc
  have hQmono : Monotone Qk := by
    intro k l hkl p hp
    have hk : (k : ℝ) + 1 ≤ (l : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hkl
    have hk0 : (0:ℝ) < (k : ℝ) + 1 := by positivity
    have h1 : 1 / ((l : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := one_div_le_one_div_of_le hk0 hk
    exact ⟨⟨h1.trans hp.1.1, hp.1.2.trans hk⟩, ⟨h1.trans hp.2.1, hp.2.2.trans hk⟩⟩
  have hQsub : ∀ k, Qk k ⊆ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) := by
    intro k p hp
    have hk0 : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    exact ⟨lt_of_lt_of_le hk0 hp.1.1, lt_of_lt_of_le hk0 hp.2.1⟩
  have hQun : (⋃ k, Qk k) = Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) := by
    apply Subset.antisymm (iUnion_subset hQsub)
    intro p hp
    obtain ⟨k1, hk1⟩ := exists_nat_gt (max (1 / p.1) p.1)
    obtain ⟨k2, hk2⟩ := exists_nat_gt (max (1 / p.2) p.2)
    refine mem_iUnion.2 ⟨max k1 k2, ?_⟩
    have hm1 : (k1 : ℝ) ≤ ((max k1 k2 : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    have hm2 : (k2 : ℝ) ≤ ((max k1 k2 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    have hp1 : 0 < p.1 := hp.1
    have hp2 : 0 < p.2 := hp.2
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [div_le_iff₀ (by positivity)]
      have h1 : 1 / p.1 < ((max k1 k2 : ℕ) : ℝ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hk1) hm1
      rw [div_lt_iff₀ hp1] at h1
      nlinarith
    · have := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hk1) hm1; linarith
    · rw [div_le_iff₀ (by positivity)]
      have h1 : 1 / p.2 < ((max k1 k2 : ℕ) : ℝ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hk2) hm2
      rw [div_lt_iff₀ hp2] at h1
      nlinarith
    · have := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hk2) hm2; linarith
  have hnn : ∀ ℓ, ∀ᵐ p ∂μ, 0 ≤ Fl ℓ p := fun ℓ => by
    filter_upwards [hbd X le_rfl le_rfl ℓ] with p hp using hp.1
  have hper : ∀ ℓ : ℤ, Tendsto (fun k => ∫ p in Qk k, Fl ℓ p) atTop
      (𝓝 (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
        Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
          Real.sqrt (u * v) *
          (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v))) := by
    intro ℓ
    rw [vs_iter_eq ℓ (hint ℓ)]
    have h := tendsto_setIntegral_of_monotone (μ := μ) (f := Fl ℓ) hQm hQmono (hint ℓ).integrableOn
    rw [hQun] at h
    have e1 : ∀ k, ∫ a in Qk k, Fl ℓ a ∂μ = ∫ a in Qk k, Fl ℓ a := by
      intro k
      rw [hμ', Measure.restrict_restrict (hQm k), inter_eq_left.2 (hQsub k)]
    have e2 : ∫ a in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), Fl ℓ a ∂μ = ∫ a, Fl ℓ a ∂μ := by
      rw [hμ', Measure.restrict_restrict (measurableSet_Ioi.prod measurableSet_Ioi), inter_self]
    simp only [e1, e2] at h
    exact h
  refine tendsto_tsum_of_dominated_convergence (bound := fun ℓ => ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
    Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
        Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v))
    hsum hper (Eventually.of_forall fun k ℓ => ?_)
  rw [vs_iter_eq ℓ (hint ℓ)]
  have e1 : ∫ a in Qk k, Fl ℓ a = ∫ a in Qk k, Fl ℓ a ∂μ := by
    rw [hμ', Measure.restrict_restrict (hQm k), inter_eq_left.2 (hQsub k)]
  have h0 : 0 ≤ ∫ a in Qk k, Fl ℓ a := by
    rw [e1]
    exact integral_nonneg_of_ae (ae_restrict_of_ae (hnn ℓ))
  rw [Real.norm_eq_abs, abs_of_nonneg h0, e1]
  exact setIntegral_le_integral (hint ℓ) (hnn ℓ)

private lemma pg9_union_le {E : Type*} [MeasurableSpace E] {μ : Measure E} {s t : Set E}
    (ht : MeasurableSet t) (hs : MeasurableSet s) {f : E → ℝ} (hf : IntegrableOn f (s ∪ t) μ)
    (hnn : ∀ x ∈ s ∪ t, 0 ≤ f x) :
    ∫ x in s ∪ t, f x ∂μ ≤ (∫ x in s, f x ∂μ) + ∫ x in t, f x ∂μ := by
  have hdisj : Disjoint s (t \ s) := Set.disjoint_sdiff_right
  have hu : s ∪ t = s ∪ (t \ s) := (Set.union_diff_self).symm
  have hts : IntegrableOn f (t \ s) μ := hf.mono_set (by rw [hu]; exact Set.subset_union_right)
  have hss : IntegrableOn f s μ := hf.mono_set Set.subset_union_left
  have htt : IntegrableOn f t μ := hf.mono_set Set.subset_union_right
  rw [hu, setIntegral_union hdisj (ht.diff hs) hss hts]
  have : ∫ x in t \ s, f x ∂μ ≤ ∫ x in t, f x ∂μ := by
    refine setIntegral_mono_set htt ?_ (Eventually.of_forall Set.diff_subset)
    filter_upwards [ae_restrict_mem ht] with x hx
    exact hnn x (Or.inr hx)
  linarith

private lemma pg9_union5_le {E : Type*} [MeasurableSpace E] {μ : Measure E} {U Q T1 T2 T3 T4 T5 : Set E}
    (h1 : MeasurableSet T1) (h2 : MeasurableSet T2) (h3 : MeasurableSet T3) (h4 : MeasurableSet T4)
    (h5 : MeasurableSet T5)
    (hcov : U \ Q ⊆ T1 ∪ T2 ∪ T3 ∪ T4 ∪ T5)
    (hsub : T1 ∪ T2 ∪ T3 ∪ T4 ∪ T5 ⊆ U) {f : E → ℝ} (hf : IntegrableOn f U μ)
    (hnn : ∀ x ∈ U, 0 ≤ f x) :
    ∫ x in U \ Q, f x ∂μ ≤ (∫ x in T1, f x ∂μ) + (∫ x in T2, f x ∂μ) + (∫ x in T3, f x ∂μ) +
      (∫ x in T4, f x ∂μ) + ∫ x in T5, f x ∂μ := by
  have hint : IntegrableOn f (T1 ∪ T2 ∪ T3 ∪ T4 ∪ T5) μ := hf.mono_set hsub
  have hnn' : ∀ x ∈ T1 ∪ T2 ∪ T3 ∪ T4 ∪ T5, 0 ≤ f x := fun x hx => hnn x (hsub hx)
  have step1 : ∫ x in U \ Q, f x ∂μ ≤ ∫ x in T1 ∪ T2 ∪ T3 ∪ T4 ∪ T5, f x ∂μ := by
    refine setIntegral_mono_set hint ?_ (Eventually.of_forall hcov)
    filter_upwards [ae_restrict_mem ((((h1.union h2).union h3).union h4).union h5)] with x hx
    exact hnn' x hx
  refine step1.trans ?_
  have i12 : IntegrableOn f (T1 ∪ T2) μ := hint.mono_set (by intro x hx; exact Or.inl (Or.inl (Or.inl hx)))
  have i123 : IntegrableOn f (T1 ∪ T2 ∪ T3) μ := hint.mono_set (by
    intro x hx; exact Or.inl (Or.inl hx))
  have i1234 : IntegrableOn f (T1 ∪ T2 ∪ T3 ∪ T4) μ := hint.mono_set (by intro x hx; exact Or.inl hx)
  have a5 := pg9_union_le (μ := μ) h5 (((h1.union h2).union h3).union h4) hint hnn'
  have a4 := pg9_union_le (μ := μ) h4 ((h1.union h2).union h3) i1234
    (fun x hx => hnn' x (Or.inl hx))
  have a3 := pg9_union_le (μ := μ) h3 (h1.union h2) i123 (fun x hx => hnn' x (Or.inl (Or.inl hx)))
  have a2 := pg9_union_le (μ := μ) h2 h1 i12 (fun x hx => hnn' x (Or.inl (Or.inl (Or.inl hx))))
  linarith

private lemma pg9_cover {γ δ R : ℝ} :
    (Ioo 0 γ ×ˢ Ioo 0 γ) \ (Icc δ R ×ˢ Icc δ R) ⊆
      ((Ioc 0 (γ / 2) \ Icc δ R) ×ˢ Ioc 0 (γ / 2) ∪ Ioc 0 (γ / 2) ×ˢ (Ioc 0 (γ / 2) \ Icc δ R) ∪
        Ioc 0 (γ / 8) ×ˢ Ioo (γ / 2) γ ∪ Ioo (γ / 2) γ ×ˢ Ioc 0 (γ / 8) ∪
        Ioo (γ / 8) γ ×ˢ Ioo (γ / 8) γ) := by
  intro p hp
  obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, hQ⟩ := hp
  by_cases ha : p.1 ≤ γ / 2
  · by_cases hb : p.2 ≤ γ / 2
    · by_cases hc : p.1 ∈ Icc δ R
      · have hd : p.2 ∉ Icc δ R := fun hd => hQ ⟨hc, hd⟩
        refine Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨h1, ha⟩, ⟨⟨h3, hb⟩, hd⟩⟩)))
      · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨⟨⟨h1, ha⟩, hc⟩, ⟨h3, hb⟩⟩)))
    · have hb' : γ / 2 < p.2 := not_le.1 hb
      by_cases hd : p.1 ≤ γ / 8
      · exact Or.inl (Or.inl (Or.inr ⟨⟨h1, hd⟩, ⟨hb', h4⟩⟩))
      · exact Or.inr ⟨⟨not_le.1 hd, h2⟩, ⟨by linarith, h4⟩⟩
  · have ha' : γ / 2 < p.1 := not_le.1 ha
    by_cases hd : p.2 ≤ γ / 8
    · exact Or.inl (Or.inr ⟨⟨ha', h2⟩, ⟨h3, hd⟩⟩)
    · exact Or.inr ⟨⟨by linarith, h2⟩, ⟨not_le.1 hd, h4⟩⟩

private lemma pg9_cover_sub {γ δ R : ℝ} :
    ((Ioc 0 (γ / 2) \ Icc δ R) ×ˢ Ioc 0 (γ / 2) ∪ Ioc 0 (γ / 2) ×ˢ (Ioc 0 (γ / 2) \ Icc δ R) ∪
        Ioc 0 (γ / 8) ×ˢ Ioo (γ / 2) γ ∪ Ioo (γ / 2) γ ×ˢ Ioc 0 (γ / 8) ∪
        Ioo (γ / 8) γ ×ˢ Ioo (γ / 8) γ) ⊆ Ioo 0 γ ×ˢ Ioo 0 γ := by
  intro p hp
  rcases hp with ((((⟨⟨⟨h1, h2⟩, _⟩, ⟨h3, h4⟩⟩) | (⟨⟨h1, h2⟩, ⟨⟨h3, h4⟩, _⟩⟩)) |
    (⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩)) | (⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩)) | (⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩)
  · exact ⟨⟨h1, by linarith⟩, ⟨h3, by linarith⟩⟩
  · exact ⟨⟨h1, by linarith⟩, ⟨h3, by linarith⟩⟩
  · exact ⟨⟨h1, by linarith⟩, ⟨by linarith, h4⟩⟩
  · exact ⟨⟨by linarith, h2⟩, ⟨h3, by linarith⟩⟩
  · exact ⟨⟨by linarith, h2⟩, ⟨by linarith, h4⟩⟩

private lemma pg9_M_int {α B ρ aL aU A : ℝ} (hα1 : 1 < α) (hB : 0 < B) (haL : 0 < aL) (haU : 0 < aU)
    (hA : 0 ≤ A) (hρ : 0 < ρ) {S : Set ℝ} (hS : S ⊆ Ioi 0) (hSm : MeasurableSet S) :
    IntegrableOn (fun m : ℝ => A * ((if m < 1 / B then Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ))
          else 0) +
        (if m ≤ 1 then 1 / aL ^ (α / 2) * m ^ (α / 2 - 1) else aU ^ (α / 2) * m ^ (-((α + 1) / 2))))) S ∧
    ∫ m in S, A * ((if m < 1 / B then Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) +
        (if m ≤ 1 then 1 / aL ^ (α / 2) * m ^ (α / 2 - 1) else aU ^ (α / 2) * m ^ (-((α + 1) / 2)))) ≤
      A * (2 * ρ ^ (-(α / 2)) + ∫ m in S, (if m ≤ 1 then 1 / aL ^ (α / 2) * m ^ (α / 2 - 1)
        else aU ^ (α / 2) * m ^ (-((α + 1) / 2)))) := by
  obtain ⟨hPi, hPv⟩ := pg9_P_int (α := α) (ρ := ρ) hB
  have hkf := vs_k_int (α := α) (K := 1) (A := 1 / aL ^ (α / 2)) (B := aU ^ (α / 2)) hα1
  have hkf' : Integrable (fun m : ℝ => if m ≤ 1 then 1 / aL ^ (α / 2) * m ^ (α / 2 - 1)
      else aU ^ (α / 2) * m ^ (-((α + 1) / 2))) (volume.restrict (Ioi (0:ℝ))) := by
    refine hkf.congr (Eventually.of_forall fun m => ?_)
    simp only [one_mul]
  have hPi' : IntegrableOn (fun m : ℝ => if m < 1 / B then Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ))
      else 0) (Ioi 0) := hPi
  have hkf'' : IntegrableOn (fun m : ℝ => if m ≤ 1 then 1 / aL ^ (α / 2) * m ^ (α / 2 - 1)
      else aU ^ (α / 2) * m ^ (-((α + 1) / 2))) (Ioi 0) := hkf'
  have hPS : IntegrableOn (fun m : ℝ => if m < 1 / B then Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ))
      else 0) S := hPi'.mono_set hS
  have hkS : IntegrableOn (fun m : ℝ => if m ≤ 1 then 1 / aL ^ (α / 2) * m ^ (α / 2 - 1)
      else aU ^ (α / 2) * m ^ (-((α + 1) / 2))) S := hkf''.mono_set hS
  refine ⟨(hPS.add hkS).const_mul A, ?_⟩
  rw [integral_const_mul, integral_add hPS hkS]
  refine mul_le_mul_of_nonneg_left ?_ hA
  have hPnn : ∀ m ∈ Ioi (0:ℝ), 0 ≤ (if m < 1 / B then Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ))
      else 0) := by
    intro m hm
    split_ifs
    · have : 0 < m := hm
      positivity
    · exact le_rfl
  have hP1 : ∫ m in S, (if m < 1 / B then Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) ≤
      ∫ m in Ioi (0:ℝ), (if m < 1 / B then Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) := by
    refine setIntegral_mono_set hPi' ?_ hS.eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with m hm
    exact hPnn m hm
  rw [hPv] at hP1
  linarith

private lemma pg9_E_H {A ε K τ δ R b : ℝ} {kf M : ℝ → ℝ} (hδ : 0 < δ) (hδR : δ ≤ R) (hb : 0 < b)
    (hA : 0 ≤ A)
    (hMnn : ∀ m : ℝ, 0 < m → 0 ≤ M m)
    (hMint : ∀ S : Set ℝ, S ⊆ Ioi 0 → MeasurableSet S →
      IntegrableOn M S ∧ ∫ m in S, M m ≤ A * (ε + ∫ m in S, kf m))
    (hkf_nn : ∀ m : ℝ, 0 < m → 0 ≤ kf m) (hkf_int : IntegrableOn kf (Ioi 0))
    (hK : ∫ m in Ioi (0:ℝ), kf m = K) (hτ : (∫ m in Ioc (0:ℝ) δ, kf m) + (∫ m in Ioi R, kf m) = τ) :
    IntegrableOn M (Ioc 0 b \ Icc δ R) ∧ (∫ m in Ioc 0 b \ Icc δ R, M m) ≤ A * (2 * ε + τ) ∧
    IntegrableOn M (Ioc 0 b) ∧ (∫ m in Ioc 0 b, M m) ≤ A * (ε + K) := by
  have hR : 0 < R := lt_of_lt_of_le hδ hδR
  have hEsub : Ioc 0 b \ Icc δ R ⊆ Ioc 0 δ ∪ Ioi R := by
    intro m hm
    obtain ⟨⟨h1, h2⟩, h3⟩ := hm
    by_cases h : m ≤ δ
    · exact Or.inl ⟨h1, h⟩
    · right
      by_contra h'
      exact h3 ⟨le_of_lt (not_le.1 h), not_lt.1 h'⟩
  have hj1 : Ioc (0:ℝ) δ ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hj2 : Ioi R ⊆ Ioi (0:ℝ) := Ioi_subset_Ioi hR.le
  obtain ⟨hi1, hv1⟩ := hMint (Ioc 0 δ) hj1 measurableSet_Ioc
  obtain ⟨hi2, hv2⟩ := hMint (Ioi R) hj2 measurableSet_Ioi
  have hdisj : Disjoint (Ioc (0:ℝ) δ) (Ioi R) := by
    rw [Set.disjoint_left]
    intro m hm1 hm2
    have : m ≤ δ := hm1.2
    have : R < m := hm2
    linarith
  have hunion : IntegrableOn M (Ioc 0 δ ∪ Ioi R) := hi1.union hi2
  have hEint : IntegrableOn M (Ioc 0 b \ Icc δ R) := hunion.mono_set hEsub
  refine ⟨hEint, ?_, ?_, ?_⟩
  · have h1 : ∫ m in Ioc 0 b \ Icc δ R, M m ≤ ∫ m in Ioc 0 δ ∪ Ioi R, M m := by
      refine setIntegral_mono_set hunion ?_ (Eventually.of_forall hEsub)
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.union measurableSet_Ioi)] with m hm
      rcases hm with hm | hm
      · exact hMnn m hm.1
      · exact hMnn m (lt_of_le_of_lt hR.le hm)
    rw [setIntegral_union hdisj measurableSet_Ioi hi1 hi2] at h1
    have : (∫ m in Ioc (0:ℝ) δ, kf m) + (∫ m in Ioi R, kf m) = τ := hτ
    nlinarith
  · exact (hMint (Ioc 0 b) Ioc_subset_Ioi_self measurableSet_Ioc).1
  · refine (hMint (Ioc 0 b) Ioc_subset_Ioi_self measurableSet_Ioc).2.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hA
    have : ∫ m in Ioc 0 b, kf m ≤ ∫ m in Ioi 0, kf m := by
      refine setIntegral_mono_set hkf_int ?_ Ioc_subset_Ioi_self.eventuallyLE
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with m hm using hkf_nn m hm
    linarith

set_option maxHeartbeats 1600000 in
private lemma pg9_tail_fin {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ (i : Fin N)
      (s : Finset ℤ) (δ R A ε K τ Sb : ℝ) (kf M : ℝ → ℝ),
      2 ≤ gammaOf N B → 0 < δ → δ ≤ R → 0 ≤ A → 0 ≤ ε → 0 ≤ K →
      (∀ ℓ : ℤ, IntegrableOn (fun p : ℝ × ℝ => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2)
        (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B))) →
      (∀ m : ℝ, 0 < m → 0 ≤ M m) →
      (∀ S : Set ℝ, S ⊆ Ioi 0 → MeasurableSet S →
        IntegrableOn M S ∧ ∫ m in S, M m ≤ A * (ε + ∫ m in S, kf m)) →
      (∀ m : ℝ, 0 < m → 0 ≤ kf m) → IntegrableOn kf (Ioi 0) →
      (∀ m ∈ Ioc 0 (gammaOf N B / 2), Wpart β B (plSpec α c N) i m * min (Real.sqrt m) 1 ≤ M m) →
      (∫ m in Ioi (0:ℝ), kf m = K) → ((∫ m in Ioc (0:ℝ) δ, kf m) + (∫ m in Ioi R, kf m) = τ) →
      (∫ p in Ioo (gammaOf N B / 8) (gammaOf N B) ×ˢ Ioo (gammaOf N B / 8) (gammaOf N B),
        ∑ ℓ ∈ s, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 ≤ Sb) →
      ∫ p in (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) \ (Icc δ R ×ˢ Icc δ R),
          ∑ ℓ ∈ s, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 ≤
        C1 * A ^ 2 * ((2 * ε + τ) * (ε + K)) +
          C2 * A * (ε + K) * ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ (α / 2) * Real.sqrt (gammaOf N B) + Sb := by
  have hα0 : 0 < α := by linarith
  obtain ⟨CD, hCD, hreg⟩ := pg9_region hα0 hβ0 hβ1
  obtain ⟨cα, hcα, hdl⟩ := pg9_delta_lb hα0 hβ0 hβ1
  obtain ⟨C5, hC5, hW5⟩ := pg9_W_top hα1 hβ0 hβ1
  refine ⟨8 * CD / cα, 8 * CD * C5, by positivity, by positivity, ?_⟩
  intro N B c hN hB hc i s δ R A ε K τ Sb kf M hγ hδ hδR hA hε hK0 hU hMnn hMint hkf_nn hkf_int hkM hK hτ hSb
  have hγ0 : 0 < gammaOf N B := by linarith
  set γ := gammaOf N B with hγdef
  set G : ℝ × ℝ → ℝ := fun p => ∑ ℓ ∈ s, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 with hG
  set U : Set (ℝ × ℝ) := Ioo 0 γ ×ˢ Ioo 0 γ with hU'
  have hGint : IntegrableOn G U := integrable_finset_sum _ (fun ℓ _ => hU ℓ)
  have hGnn : ∀ p ∈ U, 0 ≤ G p := fun p hp =>
    Finset.sum_nonneg (fun ℓ _ => pg9_F_nonneg hα0 hβ0 hβ1 hN hB hc i ℓ hp.1 hp.2)
  have hHγ : Ioc (0:ℝ) (γ / 2) ⊆ Ioo 0 γ := fun m hm => ⟨hm.1, by linarith [hm.2]⟩
  have hH8 : Ioc (0:ℝ) (γ / 8) ⊆ Ioc 0 (γ / 2) := Ioc_subset_Ioc_right (by linarith)
  have hmid : Ioo (γ / 2) γ ⊆ Ioo 0 γ := fun m hm => ⟨by linarith [hm.1], hm.2⟩
  set E : Set ℝ := Ioc 0 (γ / 2) \ Icc δ R with hE
  have hEm : MeasurableSet E := measurableSet_Ioc.diff measurableSet_Icc
  have hEsub : E ⊆ Ioo 0 γ := fun m hm => hHγ hm.1
  obtain ⟨hEi, hEv, hHi, hHv⟩ := pg9_E_H (kf := kf) (M := M) (b := γ / 2) (A := A) (ε := ε) (K := K)
    (τ := τ) hδ hδR (by linarith) hA hMnn hMint hkf_nn hkf_int hK hτ
  obtain ⟨hH8i, hH8v⟩ := (pg9_E_H (kf := kf) (M := M) (b := γ / 8) (A := A) (ε := ε) (K := K)
    (τ := τ) hδ hδR (by linarith) hA hMnn hMint hkf_nn hkf_int hK hτ).2.2
  have hMnn' : ∀ S : Set ℝ, S ⊆ Ioi 0 → MeasurableSet S → 0 ≤ ∫ m in S, M m :=
    fun S hS hSm => setIntegral_nonneg hSm (fun m hm => hMnn m (hS hm))
  have hEnn := hMnn' E (fun m hm => hEsub hm |>.1) hEm
  have hHnn := hMnn' (Ioc 0 (γ / 2)) Ioc_subset_Ioi_self measurableSet_Ioc
  have hH8nn := hMnn' (Ioc 0 (γ / 8)) Ioc_subset_Ioi_self measurableSet_Ioc
  have hsmall : CD / (cα / 4) * ((∫ x in E, M x) * ∫ y in Ioc 0 (γ / 2), M y) ≤
      CD / (cα / 4) * (A * (2 * ε + τ) * (A * (ε + K))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hEv hHv hHnn (by
      have := hEnn; nlinarith [hEv])) (by positivity)
  -- T1
  have hT1 : ∫ p in E ×ˢ Ioc 0 (γ / 2), G p ≤ CD / (cα / 4) * (A * (2 * ε + τ) * (A * (ε + K))) := by
    refine le_trans (hreg N B c hN hB hc i s E (Ioc 0 (γ / 2)) M M (cα / 4) hEm measurableSet_Ioc
      hEsub hHγ (by positivity) (hGint.mono_set (prod_mono hEsub hHγ)) hEi hHi
      (fun m hm => hkM m hm.1) (fun m hm => hkM m hm)
      (fun p hp ℓ => hdl N B c hN hB hc ℓ p.1 p.2 (hEsub hp.1) (hHγ hp.2) hp.1.1.2 hp.2.2)) hsmall
  have hT2 : ∫ p in Ioc 0 (γ / 2) ×ˢ E, G p ≤ CD / (cα / 4) * (A * (2 * ε + τ) * (A * (ε + K))) := by
    refine le_trans (hreg N B c hN hB hc i s (Ioc 0 (γ / 2)) E M M (cα / 4) measurableSet_Ioc hEm
      hHγ hEsub (by positivity) (hGint.mono_set (prod_mono hHγ hEsub)) hHi hEi
      (fun m hm => hkM m hm) (fun m hm => hkM m hm.1)
      (fun p hp ℓ => hdl N B c hN hB hc ℓ p.1 p.2 (hHγ hp.1) (hEsub hp.2) hp.1.2 hp.2.1.2)) ?_
    have := mul_le_mul hHv hEv hEnn (by nlinarith [hHnn, hHv])
    calc CD / (cα / 4) * ((∫ x in Ioc 0 (γ / 2), M x) * ∫ y in E, M y)
        ≤ CD / (cα / 4) * (A * (ε + K) * (A * (2 * ε + τ))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  -- T3 / T4 data
  set ρN : ℝ := (((i : ℕ) : ℝ) + 1) / (N : ℝ) with hρN
  set M2 : ℝ → ℝ := fun m => C5 * ρN ^ (α / 2) * m ^ (-(1 / 2 : ℝ)) with hM2
  have hmidm : MeasurableSet (Ioo (γ / 2) γ) := measurableSet_Ioo
  have hrint : IntegrableOn (fun m : ℝ => m ^ (-(1 / 2 : ℝ))) (Ioc 0 γ) :=
    vg_int_rpow_Ioc (e := -(1 / 2 : ℝ)) (by norm_num) γ
  have hM2i : IntegrableOn M2 (Ioo (γ / 2) γ) :=
    (hrint.mono_set (fun m hm => ⟨by linarith [hm.1], hm.2.le⟩)).const_mul _
  have hρN0 : 0 ≤ ρN := by positivity
  have hM2v : ∫ m in Ioo (γ / 2) γ, M2 m ≤ C5 * ρN ^ (α / 2) * (2 * Real.sqrt γ) := by
    simp only [hM2]
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : ∫ m in Ioo (γ / 2) γ, m ^ (-(1 / 2 : ℝ)) ≤ ∫ m in Ioc 0 γ, m ^ (-(1 / 2 : ℝ)) := by
      refine setIntegral_mono_set hrint ?_ (Eventually.of_forall (fun m hm => ⟨by linarith [hm.1], hm.2.le⟩))
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with m hm
      exact Real.rpow_nonneg hm.1.le _
    rw [pg9_int_rpow_Ioc (by norm_num) hγ0] at h1
    refine h1.trans (le_of_eq ?_)
    rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
    ring
  have hM2nn : 0 ≤ ∫ m in Ioo (γ / 2) γ, M2 m := setIntegral_nonneg hmidm (fun m hm => by
    have : 0 < m := by linarith [hm.1]
    simp only [hM2]; positivity)
  have hkM2 : ∀ m ∈ Ioo (γ / 2) γ,
      Wpart β B (plSpec α c N) i m * min (Real.sqrt m) 1 ≤ M2 m := by
    intro m hm
    have h1 : 1 ≤ Real.sqrt m := by
      rw [Real.one_le_sqrt]; linarith [hm.1]
    rw [min_eq_right h1, mul_one]
    exact hW5 N B c hN hB hc i m hγ hm.1.le hm.2
  have hT3 : ∫ p in Ioc 0 (γ / 8) ×ˢ Ioo (γ / 2) γ, G p ≤
      CD / (1 / 2) * (A * (ε + K) * (C5 * ρN ^ (α / 2) * (2 * Real.sqrt γ))) := by
    refine le_trans (hreg N B c hN hB hc i s (Ioc 0 (γ / 8)) (Ioo (γ / 2) γ) M M2 (1 / 2)
      measurableSet_Ioc hmidm (hH8.trans hHγ) hmid (by norm_num)
      (hGint.mono_set (prod_mono (hH8.trans hHγ) hmid)) hH8i hM2i
      (fun m hm => hkM m (hH8 hm)) hkM2 ?_) ?_
    · intro p hp ℓ
      exact pg9_delta_R hα0 hβ0 hβ1 hN hB hc ℓ (hHγ (hH8 hp.1)) (hmid hp.2)
        ((min_le_left _ _).trans hp.1.2) (by
          have := le_max_right p.1 p.2; linarith [hp.2.1])
    · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul hH8v hM2v hM2nn (mul_nonneg hA (add_nonneg hε hK0))
  have hT4 : ∫ p in Ioo (γ / 2) γ ×ˢ Ioc 0 (γ / 8), G p ≤
      CD / (1 / 2) * (A * (ε + K) * (C5 * ρN ^ (α / 2) * (2 * Real.sqrt γ))) := by
    refine le_trans (hreg N B c hN hB hc i s (Ioo (γ / 2) γ) (Ioc 0 (γ / 8)) M2 M (1 / 2)
      hmidm measurableSet_Ioc hmid (hH8.trans hHγ) (by norm_num)
      (hGint.mono_set (prod_mono hmid (hH8.trans hHγ))) hM2i hH8i
      hkM2 (fun m hm => hkM m (hH8 hm)) ?_) ?_
    · intro p hp ℓ
      exact pg9_delta_R hα0 hβ0 hβ1 hN hB hc ℓ (hmid hp.1) (hHγ (hH8 hp.2))
        ((min_le_right _ _).trans hp.2.2) (by
          have := le_max_left p.1 p.2; linarith [hp.1.1])
    · have := mul_le_mul hM2v hH8v hH8nn (by positivity)
      calc CD / (1 / 2) * ((∫ x in Ioo (γ / 2) γ, M2 x) * ∫ y in Ioc 0 (γ / 8), M y)
          ≤ CD / (1 / 2) * (C5 * ρN ^ (α / 2) * (2 * Real.sqrt γ) * (A * (ε + K))) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
  have hmeas1 : MeasurableSet (E ×ˢ Ioc 0 (γ / 2)) := hEm.prod measurableSet_Ioc
  have hmeas2 : MeasurableSet (Ioc 0 (γ / 2) ×ˢ E) := measurableSet_Ioc.prod hEm
  have hmeas3 : MeasurableSet (Ioc 0 (γ / 8) ×ˢ Ioo (γ / 2) γ) := measurableSet_Ioc.prod hmidm
  have hmeas4 : MeasurableSet (Ioo (γ / 2) γ ×ˢ Ioc 0 (γ / 8)) := hmidm.prod measurableSet_Ioc
  have hmeas5 : MeasurableSet (Ioo (γ / 8) γ ×ˢ Ioo (γ / 8) γ) := measurableSet_Ioo.prod measurableSet_Ioo
  have hunion := pg9_union5_le (μ := (volume : Measure (ℝ × ℝ))) (U := U) (Q := Icc δ R ×ˢ Icc δ R)
    hmeas1 hmeas2 hmeas3 hmeas4 hmeas5 (pg9_cover (γ := γ) (δ := δ) (R := R))
    (pg9_cover_sub (γ := γ) (δ := δ) (R := R)) hGint hGnn
  have hT5 : ∫ p in Ioo (γ / 8) γ ×ˢ Ioo (γ / 8) γ, G p ≤ Sb := hSb
  have hfin : 8 * CD / cα * A ^ 2 * ((2 * ε + τ) * (ε + K)) +
      8 * CD * C5 * A * (ε + K) * ρN ^ (α / 2) * Real.sqrt γ + Sb =
      (CD / (cα / 4) * (A * (2 * ε + τ) * (A * (ε + K)))) +
      (CD / (cα / 4) * (A * (2 * ε + τ) * (A * (ε + K)))) +
      (CD / (1 / 2) * (A * (ε + K) * (C5 * ρN ^ (α / 2) * (2 * Real.sqrt γ)))) +
      (CD / (1 / 2) * (A * (ε + K) * (C5 * ρN ^ (α / 2) * (2 * Real.sqrt γ)))) + Sb := by
    field_simp
    ring
  rw [hfin]
  linarith

private lemma pg9_decay_bounds {α : ℝ} (hα1 : 1 < α) {N B : ℕ} (hN : 0 < N) (hB : 0 < B) {ρ aU : ℝ}
    (hρ : 0 < ρ) (haU : ρ / B ≤ aU) :
    (ρ / (N : ℝ)) ^ (α / 2) * Real.sqrt (gammaOf N B) ≤
      aU ^ (α / 2) * gammaOf N B ^ (-((α - 1) / 2)) ∧
    gammaOf N B * (ρ / (N : ℝ)) ^ α ≤ aU ^ α * gammaOf N B ^ (-(α - 1)) := by
  have hα0 : 0 < α := by linarith
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by unfold gammaOf; positivity
  have hρN : ρ / (N : ℝ) = (ρ / B) / gammaOf N B := by
    unfold gammaOf; field_simp
  have ha0 : 0 ≤ ρ / B := by positivity
  have h1 : ρ / (N : ℝ) ≤ aU / gammaOf N B := by
    rw [hρN]; exact div_le_div_of_nonneg_right haU hγ.le
  have haU0 : 0 ≤ aU := ha0.trans haU
  constructor
  · have h2 : (ρ / (N : ℝ)) ^ (α / 2) ≤ (aU / gammaOf N B) ^ (α / 2) :=
      Real.rpow_le_rpow (by positivity) h1 (by positivity)
    rw [Real.div_rpow haU0 hγ.le] at h2
    calc (ρ / (N : ℝ)) ^ (α / 2) * Real.sqrt (gammaOf N B)
        ≤ aU ^ (α / 2) / gammaOf N B ^ (α / 2) * Real.sqrt (gammaOf N B) :=
          mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
      _ = aU ^ (α / 2) * gammaOf N B ^ (-((α - 1) / 2)) := by
          rw [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_assoc, ← Real.rpow_neg hγ.le, ← Real.rpow_add hγ]
          congr 2; ring
  · have h2 : (ρ / (N : ℝ)) ^ α ≤ (aU / gammaOf N B) ^ α :=
      Real.rpow_le_rpow (by positivity) h1 hα0.le
    rw [Real.div_rpow haU0 hγ.le] at h2
    calc gammaOf N B * (ρ / (N : ℝ)) ^ α ≤ gammaOf N B * (aU ^ α / gammaOf N B ^ α) :=
          mul_le_mul_of_nonneg_left h2 hγ.le
      _ = aU ^ α * gammaOf N B ^ (-(α - 1)) := by
          have : gammaOf N B ^ (-(α - 1)) = gammaOf N B / gammaOf N B ^ α := by
            rw [Real.rpow_neg hγ.le, Real.rpow_sub_one hγ.ne']
            field_simp
          rw [this]; ring

private lemma pg9_tauk_lim {α aL aU : ℝ} (hα1 : 1 < α) (haL : 0 < aL) (haU : 0 < aU) :
    Tendsto (fun k : ℕ => (∫ m in Ioc (0:ℝ) (1 / ((k : ℝ) + 1)),
        (if m ≤ 1 then 1 / aL ^ (α / 2) * m ^ (α / 2 - 1) else aU ^ (α / 2) * m ^ (-((α + 1) / 2)))) +
      ∫ m in Ioi ((k : ℝ) + 1),
        (if m ≤ 1 then 1 / aL ^ (α / 2) * m ^ (α / 2 - 1) else aU ^ (α / 2) * m ^ (-((α + 1) / 2))))
      atTop (𝓝 0) := by
  have hkf := vs_k_int (α := α) (K := 1) (A := 1 / aL ^ (α / 2)) (B := aU ^ (α / 2)) hα1
  have hkf' : IntegrableOn (fun m : ℝ => if m ≤ 1 then 1 / aL ^ (α / 2) * m ^ (α / 2 - 1)
      else aU ^ (α / 2) * m ^ (-((α + 1) / 2))) (Ioi 0) := by
    refine hkf.congr (Eventually.of_forall fun m => ?_)
    simp only [one_mul]
  set f : ℝ → ℝ := fun m => if m ≤ 1 then 1 / aL ^ (α / 2) * m ^ (α / 2 - 1)
      else aU ^ (α / 2) * m ^ (-((α + 1) / 2)) with hf
  have h1 : Tendsto (fun k : ℕ => ∫ m in Ioc (0:ℝ) (1 / ((k : ℝ) + 1)), f m) atTop (𝓝 0) := by
    have := tendsto_setIntegral_of_antitone (μ := volume) (f := f)
      (s := fun k : ℕ => Ioc (0:ℝ) (1 / ((k : ℝ) + 1))) (fun k => measurableSet_Ioc) ?_
      ⟨0, hkf'.mono_set (Ioc_subset_Ioi_self)⟩
    · have e : (⋂ k : ℕ, Ioc (0:ℝ) (1 / ((k : ℝ) + 1))) = ∅ := by
        ext x
        simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
        by_cases hx : 0 < x
        · obtain ⟨k, hk⟩ := exists_nat_gt (1 / x)
          refine ⟨k, fun h => ?_⟩
          have h2 : x ≤ 1 / ((k : ℝ) + 1) := h.2
          have h3 : 1 / x < (k : ℝ) + 1 := by linarith
          rw [div_lt_iff₀ hx] at h3
          rw [le_div_iff₀ (by positivity)] at h2
          linarith
        · exact ⟨0, fun h => hx h.1⟩
      rw [e] at this
      simpa using this
    · intro k l hkl
      apply Ioc_subset_Ioc_right
      have hk : (k : ℝ) + 1 ≤ (l : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hkl
      exact one_div_le_one_div_of_le (by positivity) hk
  have h2 : Tendsto (fun k : ℕ => ∫ m in Ioi ((k : ℝ) + 1), f m) atTop (𝓝 0) := by
    have := tendsto_setIntegral_of_antitone (μ := volume) (f := f)
      (s := fun k : ℕ => Ioi ((k : ℝ) + 1)) (fun k => measurableSet_Ioi) ?_
      ⟨0, hkf'.mono_set (Ioi_subset_Ioi (by positivity))⟩
    · have e : (⋂ k : ℕ, Ioi ((k : ℝ) + 1)) = ∅ := by
        ext x
        simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
        obtain ⟨k, hk⟩ := exists_nat_gt x
        exact ⟨k, fun h => by have : x > (k : ℝ) + 1 := h; linarith⟩
      rw [e] at this
      simpa using this
    · intro k l hkl
      apply Ioi_subset_Ioi
      have hk : (k : ℝ) + 1 ≤ (l : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hkl
      exact hk
  simpa using h1.add h2

set_option maxHeartbeats 3200000 in
private lemma pg9_tail_seq {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop) (X0 : ℝ) (hX0 : 0 < X0)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 X0)) :
    ∀ ε' > 0, ∃ k0 : ℕ, ∀ k ≥ k0, ∀ᶠ n in atTop, ∀ s : Finset ℤ,
      ∫ p in (Ioo 0 (gammaOf (N n) (B n)) ×ˢ Ioo 0 (gammaOf (N n) (B n))) \
        (Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1)),
        ∑ ℓ ∈ s, lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2 ≤ ε' := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  obtain ⟨C1, C2, hC1, hC2, htail⟩ := pg9_tail_fin hα1 R.hβ0 R.hβ1
  obtain ⟨A, hA, hkbd⟩ := pg9_k_bd hα1 R.hβ0 R.hβ1
  obtain ⟨Cup, hup⟩ := lem_app_pl_upper (α := α) (β := β) (1 / 8) (by norm_num) (by norm_num)
  have hupn := hup N B c R
  set aL : ℝ := X0 / (2 * Kc α) with haLdef
  set aU : ℝ := 2 * X0 / Kc α with haUdef
  have haL : 0 < aL := by positivity
  have haU : 0 < aU := by positivity
  set kf0 : ℝ → ℝ := fun m => if m ≤ 1 then 1 / aL ^ (α / 2) * m ^ (α / 2 - 1)
      else aU ^ (α / 2) * m ^ (-((α + 1) / 2)) with hkf0
  have hkfi : IntegrableOn kf0 (Ioi 0) := by
    have hkf := vs_k_int (α := α) (K := 1) (A := 1 / aL ^ (α / 2)) (B := aU ^ (α / 2)) hα1
    refine hkf.congr (Eventually.of_forall fun m => ?_)
    simp only [hkf0, one_mul]
  have hkfnn : ∀ m : ℝ, 0 < m → 0 ≤ kf0 m := by
    intro m hm
    simp only [hkf0]
    split_ifs
    · positivity
    · positivity
  set Kf : ℝ := ∫ m in Ioi (0:ℝ), kf0 m with hKf
  have hKf0 : 0 ≤ Kf := setIntegral_nonneg measurableSet_Ioi (fun m hm => hkfnn m hm)
  have hτ := pg9_tauk_lim (α := α) hα1 haL haU
  intro ε' hε'
  set Cu : ℝ := max Cup 0 with hCu
  have hCu0 : 0 ≤ Cu := le_max_right _ _
  -- choose k0
  have hLk : ∀ᶠ k : ℕ in atTop, C1 * A ^ 2 * (((∫ m in Ioc (0:ℝ) (1 / ((k : ℝ) + 1)), kf0 m) +
      ∫ m in Ioi ((k : ℝ) + 1), kf0 m) * Kf) < ε' := by
    have := ((hτ.mul_const Kf).const_mul (C1 * A ^ 2))
    simp only [zero_mul, mul_zero] at this
    exact this.eventually (gt_mem_nhds hε')
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 hLk
  refine ⟨k0, fun k hk => ?_⟩
  have hLk' := hk0 k hk
  set τk : ℝ := (∫ m in Ioc (0:ℝ) (1 / ((k : ℝ) + 1)), kf0 m) + ∫ m in Ioi ((k : ℝ) + 1), kf0 m
    with hτk
  have hδ : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hδR : 1 / ((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
    have h1 : (1:ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    calc 1 / ((k : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; exact h1
      _ ≤ _ := h1
  -- the limit of the explicit bound
  have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  have hρ0 : Tendsto (fun n => (rowIdx (i n)) ^ (-(α / 2))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity)).comp hi
  have hrb : Tendsto (fun n => aU ^ (α / 2) * gammaOf (N n) (B n) ^ (-((α - 1) / 2))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (y := (α - 1) / 2) (by linarith)).comp hg).const_mul (aU ^ (α / 2))
    simpa using this
  have hsb : Tendsto (fun n => aU ^ α * gammaOf (N n) (B n) ^ (-(α - 1))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (y := α - 1) (by linarith)).comp hg).const_mul (aU ^ α)
    simpa using this
  have hεn : Tendsto (fun n => 2 * (rowIdx (i n)) ^ (-(α / 2))) atTop (𝓝 0) := by
    simpa using hρ0.const_mul 2
  have hbn : Tendsto (fun n => C1 * A ^ 2 * ((2 * (2 * (rowIdx (i n)) ^ (-(α / 2))) + τk) *
      (2 * (rowIdx (i n)) ^ (-(α / 2)) + Kf)) +
      C2 * A * (2 * (rowIdx (i n)) ^ (-(α / 2)) + Kf) *
        (aU ^ (α / 2) * gammaOf (N n) (B n) ^ (-((α - 1) / 2))) +
      Real.pi ^ 2 * (Cu * (aU ^ α * gammaOf (N n) (B n) ^ (-(α - 1))))) atTop
      (𝓝 (C1 * A ^ 2 * ((2 * 0 + τk) * (0 + Kf)) + C2 * A * (0 + Kf) * 0 + Real.pi ^ 2 * (Cu * 0))) := by
    refine Tendsto.add (Tendsto.add ?_ ?_) ?_
    · exact (((hεn.const_mul 2).add_const τk).mul (hεn.add_const Kf)).const_mul _
    · exact ((hεn.add_const Kf).const_mul (C2 * A)).mul hrb
    · exact (hsb.const_mul Cu).const_mul _
  have hbn' : ∀ᶠ n in atTop, C1 * A ^ 2 * ((2 * (2 * (rowIdx (i n)) ^ (-(α / 2))) + τk) *
      (2 * (rowIdx (i n)) ^ (-(α / 2)) + Kf)) +
      C2 * A * (2 * (rowIdx (i n)) ^ (-(α / 2)) + Kf) *
        (aU ^ (α / 2) * gammaOf (N n) (B n) ^ (-((α - 1) / 2))) +
      Real.pi ^ 2 * (Cu * (aU ^ α * gammaOf (N n) (B n) ^ (-(α - 1)))) < ε' := by
    refine hbn.eventually (gt_mem_nhds ?_)
    simp only [mul_zero, zero_add, add_zero]
    calc C1 * A ^ 2 * (τk * Kf) = C1 * A ^ 2 * (τk * Kf) := rfl
      _ < ε' := hLk'
  have hX' : ∀ᶠ n in atTop, X0 / 2 < rowIdx (i n) / icCross α (B n) ∧
      rowIdx (i n) / icCross α (B n) < 2 * X0 :=
    ((tendsto_order.1 hX).1 _ (by linarith)).and ((tendsto_order.1 hX).2 _ (by linarith))
  filter_upwards [hbn', hX', hg.eventually_ge_atTop 2, hupn, hi.eventually_gt_atTop 0] with n h1 h2 h3 h4 h5
  intro s
  have hN := R.hNpos n
  have hB := R.hBpos n
  have hc := R.hcpos n
  have hBr : (0:ℝ) < (B n : ℝ) := by exact_mod_cast hB
  set ρ : ℝ := ((i n : ℕ) : ℝ) + 1 with hρ
  have hρdef : rowIdx (i n) = ρ := rfl
  have hρ0 : 0 < ρ := by positivity
  rw [hρdef] at h1
  have key : rowIdx (i n) / icCross α (B n) = Kc α * (ρ / (B n : ℝ)) := by
    unfold icCross; rw [hρdef]; field_simp
  rw [key] at h2
  have haLρ : aL ≤ ρ / (B n : ℝ) := by
    have := h2.1
    rw [haLdef, div_le_iff₀ (by positivity)]
    nlinarith
  have hρaU : ρ / (B n : ℝ) ≤ aU := by
    have := h2.2
    rw [haUdef, le_div_iff₀ hK]
    nlinarith
  obtain ⟨hUp1, hUp2, hUp3⟩ := h4 (i n)
  have hγ0 : 0 < gammaOf (N n) (B n) := by linarith
  set γ := gammaOf (N n) (B n) with hγdef
  have hε0 : 0 ≤ 2 * ρ ^ (-(α / 2)) := by positivity
  set M : ℝ → ℝ := fun m => A * ((if m < 1 / (B n : ℝ) then
      Real.sqrt (B n : ℝ) * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) + kf0 m) with hM
  have hMint : ∀ S : Set ℝ, S ⊆ Ioi 0 → MeasurableSet S →
      IntegrableOn M S ∧ ∫ m in S, M m ≤ A * (2 * ρ ^ (-(α / 2)) + ∫ m in S, kf0 m) :=
    fun S hS hSm => pg9_M_int (α := α) (B := (B n : ℝ)) (ρ := ρ) (aL := aL) (aU := aU) (A := A)
      hα1 hBr haL haU hA.le hρ0 hS hSm
  have hMnn : ∀ m : ℝ, 0 < m → 0 ≤ M m := by
    intro m hm
    simp only [hM]
    have := hkfnn m hm
    have : 0 ≤ (if m < 1 / (B n : ℝ) then
      Real.sqrt (B n : ℝ) * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) := by
      split_ifs
      · positivity
      · exact le_rfl
    positivity
  have hkM : ∀ m ∈ Ioc 0 (gammaOf (N n) (B n) / 2),
      Wpart β (B n) (plSpec α (c n) (N n)) (i n) m * min (Real.sqrt m) 1 ≤ M m := by
    intro m hm
    exact hkbd (N n) (B n) (c n) hN hB hc (i n) m aL aU (by linarith) hm.1 hm.2 haL haLρ hρaU
  have hUint := (lem_app_pl_age_iv hα0 R.hβ0 R.hβ1 (N n) (B n) (c n) hN hB hc (i n)).2.2.1
  have hSb := pg9_regS hα0 R.hβ0 R.hβ1 hN hB hc (i n) s Cup (by
    intro ℓ; have := (hUp1 ℓ); rwa [show (1 / 8 : ℝ) * gammaOf (N n) (B n) = gammaOf (N n) (B n) / 8 by ring] at this)
    (by have := hUp2; rwa [show (1 / 8 : ℝ) * gammaOf (N n) (B n) = gammaOf (N n) (B n) / 8 by ring] at this)
    (by have := hUp3; rwa [show (1 / 8 : ℝ) * gammaOf (N n) (B n) = gammaOf (N n) (B n) / 8 by ring] at this)
  have hfin := htail (N n) (B n) (c n) hN hB hc (i n) s (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) A
    (2 * ρ ^ (-(α / 2))) Kf τk _ kf0 M h3 hδ hδR hA.le hε0 hKf0 hUint hMnn hMint hkfnn hkfi hkM
    rfl rfl hSb
  obtain ⟨hd1, hd2⟩ := pg9_decay_bounds hα1 hN hB hρ0 hρaU
  have hq0 : 0 ≤ C2 * A * (2 * ρ ^ (-(α / 2)) + Kf) := by positivity
  have hS1 : Cup * γ * (ρ / (N n : ℝ)) ^ α ≤ Cu * (aU ^ α * γ ^ (-(α - 1))) := by
    have hpos : 0 ≤ γ * (ρ / (N n : ℝ)) ^ α := by positivity
    calc Cup * γ * (ρ / (N n : ℝ)) ^ α = Cup * (γ * (ρ / (N n : ℝ)) ^ α) := by ring
      _ ≤ Cu * (γ * (ρ / (N n : ℝ)) ^ α) := mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
      _ ≤ Cu * (aU ^ α * γ ^ (-(α - 1))) := mul_le_mul_of_nonneg_left hd2 hCu0
  have h6 : C2 * A * (2 * ρ ^ (-(α / 2)) + Kf) * (ρ / (N n : ℝ)) ^ (α / 2) * Real.sqrt γ ≤
      C2 * A * (2 * ρ ^ (-(α / 2)) + Kf) * (aU ^ (α / 2) * γ ^ (-((α - 1) / 2))) := by
    rw [mul_assoc _ ((ρ / (N n : ℝ)) ^ (α / 2))]
    exact mul_le_mul_of_nonneg_left hd1 hq0
  have h7 : Real.pi ^ 2 * (Cup * γ * (ρ / (N n : ℝ)) ^ α) ≤ Real.pi ^ 2 * (Cu * (aU ^ α * γ ^ (-(α - 1)))) :=
    mul_le_mul_of_nonneg_left hS1 (by positivity)
  linarith

private lemma pg9_split {α β : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) {c : ℝ} (hc : 0 < c) (i : Fin N) {Q : Set (ℝ × ℝ)}
    (hQm : MeasurableSet Q) (hQU : Q ⊆ Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) {ε₃ : ℝ}
    (htail : ∀ s : Finset ℤ, ∫ p in (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) \ Q,
        ∑ ℓ ∈ s, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 ≤ ε₃) :
    0 ≤ (∑' ℓ : ℤ, lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ) -
        ∑' ℓ : ℤ, ∫ p in Q, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 ∧
    (∑' ℓ : ℤ, lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ) -
        (∑' ℓ : ℤ, ∫ p in Q, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2) ≤ ε₃ ∧
    (∀ ℓ : ℤ, 0 ≤ lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ -
        (∫ p in Q, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2) ∧
      lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ -
        (∫ p in Q, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2) ≤ ε₃) ∧
    Summable (fun ℓ : ℤ => ∫ p in Q, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2) := by
  obtain ⟨-, -, hint, hsum, -⟩ := lem_app_pl_age_iv hα0 hβ0 hβ1 N B c hN hB hc i
  set U : Set (ℝ × ℝ) := Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B) with hU
  have hUm : MeasurableSet U := measurableSet_Ioo.prod measurableSet_Ioo
  set F : ℤ → ℝ × ℝ → ℝ := fun ℓ p => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 with hF
  have hFnn : ∀ ℓ, ∀ p ∈ U, 0 ≤ F ℓ p := fun ℓ p hp =>
    pg9_F_nonneg hα0 hβ0 hβ1 hN hB hc i ℓ hp.1 hp.2
  have ht : ∀ ℓ, lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ =
      ∫ p in U, F ℓ p := fun ℓ => pg9_lagTerm_prod _ i _ _ ℓ (hint ℓ)
  have hdiff : ∀ ℓ, ∫ p in U \ Q, F ℓ p = (∫ p in U, F ℓ p) - ∫ p in Q, F ℓ p := fun ℓ =>
    setIntegral_diff hQm (hint ℓ) hQU
  have hq0 : ∀ ℓ, 0 ≤ ∫ p in Q, F ℓ p := fun ℓ =>
    setIntegral_nonneg hQm (fun p hp => hFnn ℓ p (hQU hp))
  have hr0 : ∀ ℓ, 0 ≤ ∫ p in U \ Q, F ℓ p := fun ℓ =>
    setIntegral_nonneg (hUm.diff hQm) (fun p hp => hFnn ℓ p hp.1)
  have hq1 : ∀ ℓ, ∫ p in Q, F ℓ p ≤ ∫ p in U, F ℓ p := fun ℓ => by
    have := hdiff ℓ; have := hr0 ℓ; linarith
  have hr1 : ∀ ℓ, ∫ p in U \ Q, F ℓ p ≤ ∫ p in U, F ℓ p := fun ℓ => by
    have := hdiff ℓ; have := hq0 ℓ; linarith
  have hsumU : Summable (fun ℓ : ℤ => ∫ p in U, F ℓ p) := by
    refine hsum.congr (fun ℓ => ?_)
    exact ht ℓ
  have hsq : Summable (fun ℓ : ℤ => ∫ p in Q, F ℓ p) :=
    Summable.of_nonneg_of_le hq0 hq1 hsumU
  have hsr : Summable (fun ℓ : ℤ => ∫ p in U \ Q, F ℓ p) :=
    Summable.of_nonneg_of_le hr0 hr1 hsumU
  have hsplit : (∑' ℓ : ℤ, ∫ p in U, F ℓ p) =
      (∑' ℓ : ℤ, ∫ p in Q, F ℓ p) + ∑' ℓ : ℤ, ∫ p in U \ Q, F ℓ p := by
    rw [← hsq.tsum_add hsr]
    refine tsum_congr (fun ℓ => ?_)
    rw [hdiff ℓ]; ring
  have hrle : (∑' ℓ : ℤ, ∫ p in U \ Q, F ℓ p) ≤ ε₃ := by
    refine hsr.tsum_le_of_sum_le (fun s => ?_)
    rw [← integral_finset_sum _ (fun ℓ _ => (hint ℓ).mono_set diff_subset)]
    exact htail s
  have hrnn : 0 ≤ ∑' ℓ : ℤ, ∫ p in U \ Q, F ℓ p := tsum_nonneg hr0
  have e : (∑' ℓ : ℤ, lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ) =
      ∑' ℓ : ℤ, ∫ p in U, F ℓ p := tsum_congr ht
  refine ⟨?_, ?_, fun ℓ => ?_, hsq⟩
  · rw [e]; linarith
  · rw [e]; linarith
  · have h1 : lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ -
        (∫ p in Q, F ℓ p) = ∫ p in U \ Q, F ℓ p := by rw [ht ℓ, hdiff ℓ]
    have h2 : ∫ p in U \ Q, F ℓ p ≤ ∑' ℓ : ℤ, ∫ p in U \ Q, F ℓ p :=
      hsr.le_tsum ℓ (fun j _ => hr0 j)
    exact ⟨by rw [h1]; exact hr0 ℓ, by rw [h1]; linarith⟩

private lemma pg9_mid_main {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (hZero : volHZero α β N B c)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (X0 : ℝ) (hX0 : 0 < X0)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 X0)) :
    Tendsto (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n)) atTop (𝓝 (profG α β X0)) := by
  have hα0 : 0 < α := by linarith
  have hπ : 0 < Real.pi ^ 2 := by positivity
  have hrep : ∀ n, vPart β (B n) (plSpec α (c n) (N n)) (i n) = (Real.pi ^ 2)⁻¹ *
      ∑' ℓ : ℤ, lagTerm β (B n) (plSpec α (c n) (N n)) (i n) (Ioo 0 (gammaOf (N n) (B n)))
        (Ioo 0 (gammaOf (N n) (B n))) ℓ := fun n =>
    pg9_vPart_rep hα0 R.hβ0 R.hβ1 (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n) (hZero n (i n))
  have hG : profG α β X0 = (Real.pi ^ 2)⁻¹ * ∑' ℓ : ℤ, ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      Real.sqrt (profZeta α X0 u * (1 - profZeta α X0 u) * (profZeta α X0 v * (1 - profZeta α X0 v))) /
        Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v) := by
    unfold profG; rw [one_div]
  simp only [hrep]
  rw [hG]
  rw [Metric.tendsto_nhds]
  intro ε hε
  set P : ℝ := ∑' ℓ : ℤ, ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      Real.sqrt (profZeta α X0 u * (1 - profZeta α X0 u) * (profZeta α X0 v * (1 - profZeta α X0 v))) /
        Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v) with hP
  set η : ℝ := Real.pi ^ 2 * ε / 4 with hη
  have hη0 : 0 < η := by positivity
  -- (a) continuum truncation
  have ha := (pg9_cont_trunc hα1 R.hβ0 R.hβ1 hX0).eventually (Metric.ball_mem_nhds _ hη0)
  obtain ⟨k1, hk1⟩ := eventually_atTop.1 ha
  -- (b) tails
  obtain ⟨k0, hk0⟩ := pg9_tail_seq R hα1 i hi X0 hX0 hX η hη0
  set k : ℕ := max k0 k1 with hk
  have hkk0 : k ≥ k0 := le_max_left _ _
  have hkk1 : k ≥ k1 := le_max_right _ _
  have hSinf := Metric.mem_ball.1 (hk1 k hkk1)
  -- (c) compact convergence
  have hδ : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hc := (pg9_compact_lim R hα1 i X0 hX0 hX (δ := 1 / ((k : ℝ) + 1)) (Rr := (k : ℝ) + 1) hδ).eventually
    (Metric.ball_mem_nhds _ hη0)
  have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  filter_upwards [hk0 k hkk0, hc, hg.eventually_gt_atTop ((k : ℝ) + 1)] with n h1 h2 h3
  have h2 := Metric.mem_ball.1 h2
  have hQ : Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ⊆
      Ioo 0 (gammaOf (N n) (B n)) ×ˢ Ioo 0 (gammaOf (N n) (B n)) := by
    intro p hp
    exact ⟨⟨lt_of_lt_of_le hδ hp.1.1, lt_of_le_of_lt hp.1.2 h3⟩,
      ⟨lt_of_lt_of_le hδ hp.2.1, lt_of_le_of_lt hp.2.2 h3⟩⟩
  obtain ⟨hs0, hs1, -⟩ := pg9_split hα0 R.hβ0 R.hβ1 (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n)
    (measurableSet_Icc.prod measurableSet_Icc) hQ h1
  rw [Real.dist_eq] at hSinf h2 ⊢
  set Pn : ℝ := ∑' ℓ : ℤ, lagTerm β (B n) (plSpec α (c n) (N n)) (i n) (Ioo 0 (gammaOf (N n) (B n)))
        (Ioo 0 (gammaOf (N n) (B n))) ℓ with hPn
  set Sn : ℝ := ∑' ℓ : ℤ, ∫ p in Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1),
        lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2 with hSn
  have h3' := abs_lt.1 hSinf
  have h2' := abs_lt.1 h2
  have : (Real.pi ^ 2)⁻¹ * Pn - (Real.pi ^ 2)⁻¹ * P = (Real.pi ^ 2)⁻¹ * (Pn - P) := by ring
  rw [this, abs_mul, abs_of_pos (inv_pos.2 hπ)]
  have hbd : |Pn - P| < 3 * η := by
    rw [abs_lt]; constructor <;> linarith [h3'.1, h3'.2, h2'.1, h2'.2]
  calc (Real.pi ^ 2)⁻¹ * |Pn - P| < (Real.pi ^ 2)⁻¹ * (3 * η) :=
        mul_lt_mul_of_pos_left hbd (inv_pos.2 hπ)
    _ = 3 * ε / 4 := by rw [hη]; field_simp
    _ < ε := by linarith

set_option maxHeartbeats 1600000 in
private lemma pg9_k_bd2 {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ (i : Fin N) (m : ℝ),
      1 ≤ gammaOf N B → 0 < m → m ≤ gammaOf N B / 2 →
      Wpart β B (plSpec α c N) i m * min (Real.sqrt m) 1 ≤
        A * ((if m < 1 / (B : ℝ) then
              Real.sqrt (B : ℝ) * (((i : ℕ) : ℝ) + 1) ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) +
          (if 1 / (B : ℝ) ≤ m then
            min (((B : ℝ) * m / (((i : ℕ) : ℝ) + 1)) ^ (α / 2))
              (((B : ℝ) * m / (((i : ℕ) : ℝ) + 1)) ^ (-(α / 2))) *
              (if m ≤ 1 then 1 / m else m ^ (-(1 / 2 : ℝ))) else 0)) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨Cθ, hCθ, hW⟩ := pg9_W_core hα0 hβ0 hβ1
  obtain ⟨C₁, C₂, hC₁, hC₂, hv1⟩ := lem_app_pl_finite_inverse_v_i hα1
  obtain ⟨D₁, D₂, hD₁, hD₂, hv2⟩ := lem_app_pl_finite_inverse_v_ii hα1
  set M0 : ℝ := max (max (Real.sqrt C₂) (1 / Real.sqrt C₁)) (Real.sqrt D₂) with hM0
  have hM2 : Real.sqrt C₂ ≤ M0 := (le_max_left _ _).trans (le_max_left _ _)
  have hM1 : 1 / Real.sqrt C₁ ≤ M0 := (le_max_right _ _).trans (le_max_left _ _)
  have hM3 : Real.sqrt D₂ ≤ M0 := le_max_right _ _
  have hs2 : 0 < Real.sqrt C₂ := Real.sqrt_pos.2 hC₂
  have hM0pos : 0 < M0 := lt_of_lt_of_le hs2 hM2
  refine ⟨4 * Cθ * M0, by positivity, fun N B c hN hB hc i m hγ1 hm hmγ => ?_⟩
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hB1 : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by linarith
  have hmem : m ∈ Ioo 0 (gammaOf N B) := ⟨hm, by linarith⟩
  obtain ⟨hW0, hWb⟩ := hW N B c hN hB hc i m hm hmγ
  set ρ : ℝ := ((i : ℕ) : ℝ) + 1 with hρ
  have hρ0 : 0 < ρ := by positivity
  set x := plSpec α c N i * partLam B (plSpec α c N) m with hx
  have hΛ := pg9_lam_pos (α := α) hN hB hc hmem
  have hx0 : 0 < x := mul_pos (pg9_plSpec_pos (α := α) hc N i) hΛ
  have hxe : x = (c * partLam B (plSpec α c N) m) * ρ ^ (-α) := by
    rw [hx]; unfold plSpec; rw [← hρ]; ring
  have hms : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hmh : m ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt m := by
    rw [Real.rpow_neg hm.le, Real.sqrt_eq_rpow]; simp
  have hsqm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
  have hdiv : Real.sqrt m / m = m ^ (-(1 / 2 : ℝ)) := by
    rw [hmh, div_eq_div_iff hm.ne' hms.ne', one_mul]; exact hsqm
  have hSx : 0 ≤ Real.sqrt x / (1 + x) := by positivity
  have hS1 : Real.sqrt x / (1 + x) ≤ Real.sqrt x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Real.sqrt_nonneg x]
  have hS2 : Real.sqrt x / (1 + x) ≤ 1 / Real.sqrt x := by
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hsxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    calc Real.sqrt x / (1 + x) ≤ Real.sqrt x / x :=
          div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hx0 (by linarith)
      _ = 1 / Real.sqrt x := by
          rw [div_eq_div_iff hx0.ne' hsx.ne', one_mul]; exact hsxx
  have hw0 : 0 ≤ min (Real.sqrt m) 1 := le_min (Real.sqrt_nonneg _) zero_le_one
  -- the key bound
  have hkey : Wpart β B (plSpec α c N) i m * min (Real.sqrt m) 1 ≤
      Real.sqrt x / (1 + x) * (4 * Cθ) * (if m ≤ 1 then 1 / m else m ^ (-(1 / 2 : ℝ))) := by
    by_cases hm1 : m ≤ 1
    · have hw : min (Real.sqrt m) 1 = Real.sqrt m := min_eq_left (by rw [Real.sqrt_le_one]; exact hm1)
      have hq : 1 + 1 / m + 2 / gammaOf N B ≤ 4 / m := by
        have h2γ : 2 / gammaOf N B ≤ 2 := by rw [div_le_iff₀ hγ]; linarith
        have h1m : 1 ≤ 1 / m := by rw [le_div_iff₀ hm]; linarith
        have h2m : 2 ≤ 2 / m := by rw [le_div_iff₀ hm]; linarith
        have e4 : 4 / m = 4 * (1 / m) := by ring
        have e2 : 2 / m = 2 * (1 / m) := by ring
        linarith
      rw [if_pos hm1, hw]
      calc Wpart β B (plSpec α c N) i m * Real.sqrt m
          ≤ Real.sqrt x / (1 + x) * (m ^ (-(1 / 2 : ℝ)) * (Cθ * (1 + 1 / m + 2 / gammaOf N B))) *
              Real.sqrt m := mul_le_mul_of_nonneg_right hWb hms.le
        _ = Real.sqrt x / (1 + x) * (Cθ * (1 + 1 / m + 2 / gammaOf N B)) := by
            rw [hmh]; field_simp
        _ ≤ Real.sqrt x / (1 + x) * (Cθ * (4 / m)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hCθ.le) hSx
        _ = _ := by ring
    · have hm1' : 1 < m := not_le.1 hm1
      have hw : min (Real.sqrt m) 1 = 1 := min_eq_right (by rw [Real.one_le_sqrt]; exact hm1'.le)
      have hq : 1 + 1 / m + 2 / gammaOf N B ≤ 4 := by
        have h2γ : 2 / gammaOf N B ≤ 2 := by rw [div_le_iff₀ hγ]; linarith
        have h1m : 1 / m ≤ 1 := by rw [div_le_one hm]; exact hm1'.le
        linarith
      rw [if_neg hm1, hw, mul_one]
      calc Wpart β B (plSpec α c N) i m
          ≤ Real.sqrt x / (1 + x) * (m ^ (-(1 / 2 : ℝ)) * (Cθ * (1 + 1 / m + 2 / gammaOf N B))) := hWb
        _ ≤ Real.sqrt x / (1 + x) * (m ^ (-(1 / 2 : ℝ)) * (Cθ * 4)) := by
            apply mul_le_mul_of_nonneg_left _ hSx
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hCθ.le)
              (Real.rpow_nonneg hm.le _)
        _ = _ := by ring
  have hvm0 : 0 ≤ (if m ≤ 1 then 1 / m else m ^ (-(1 / 2 : ℝ))) := by
    split_ifs
    · positivity
    · exact Real.rpow_nonneg hm.le _
  by_cases hmB : m < 1 / (B : ℝ)
  · -- small m (then m < 1)
    have hm1 : m ≤ 1 := by
      have : 1 / (B : ℝ) ≤ 1 := by rw [div_le_one hBr]; exact hB1
      linarith
    have hv := (hv2 N B c m hN hB hc hm (by linarith) hmγ).2
    have hxle : Real.sqrt x ≤ Real.sqrt D₂ * (Real.sqrt B * Real.sqrt m * ρ ^ (-(α / 2))) := by
      have : x ≤ D₂ * (B * m) * ρ ^ (-α) := by
        rw [hxe]; exact mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg hρ0.le _)
      calc Real.sqrt x ≤ Real.sqrt (D₂ * (B * m) * ρ ^ (-α)) := Real.sqrt_le_sqrt this
        _ = Real.sqrt D₂ * (Real.sqrt B * Real.sqrt m * ρ ^ (-(α / 2))) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hD₂.le, Real.sqrt_mul hBr.le,
            Real.sqrt_eq_rpow (ρ ^ (-α)), ← Real.rpow_mul hρ0.le]
          rw [show (-α) * (1 / 2) = -(α / 2) by ring]; ring
    rw [if_pos hmB, if_neg (not_le.2 hmB)]
    simp only [add_zero]
    refine hkey.trans ?_
    rw [if_pos hm1]
    calc Real.sqrt x / (1 + x) * (4 * Cθ) * (1 / m)
        ≤ Real.sqrt x * (4 * Cθ) * (1 / m) := by gcongr
      _ ≤ Real.sqrt D₂ * (Real.sqrt B * Real.sqrt m * ρ ^ (-(α / 2))) * (4 * Cθ) * (1 / m) := by gcongr
      _ = 4 * Cθ * Real.sqrt D₂ * (Real.sqrt B * ρ ^ (-(α / 2)) * (Real.sqrt m / m)) := by
          field_simp
      _ = 4 * Cθ * Real.sqrt D₂ * (Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ))) := by
          rw [hdiv]
      _ ≤ _ := by
          have : 0 ≤ Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) := by positivity
          have := mul_le_mul_of_nonneg_right hM3 this
          have h4 : 0 ≤ 4 * Cθ := by positivity
          nlinarith
  · have hmB' : 1 / (B : ℝ) ≤ m := not_lt.1 hmB
    have hv := (hv1 N B c m hN hB hc hmB' hmγ)
    set t : ℝ := (B : ℝ) * m / ρ with ht
    have ht0 : 0 < t := by positivity
    have hsq : ∀ s : ℝ, 0 < s → Real.sqrt (s ^ α) = s ^ (α / 2) := by
      intro s hs
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]; congr 1; ring
    have hxup : x ≤ C₂ * t ^ α := by
      rw [hxe, ht, Real.div_rpow (by positivity) hρ0.le]
      calc c * partLam B (plSpec α c N) m * ρ ^ (-α) ≤ C₂ * ((B : ℝ) * m) ^ α * ρ ^ (-α) :=
            mul_le_mul_of_nonneg_right hv.2 (Real.rpow_nonneg hρ0.le _)
        _ = C₂ * (((B : ℝ) * m) ^ α / ρ ^ α) := by rw [Real.rpow_neg hρ0.le]; ring
    have hxlo : C₁ * t ^ α ≤ x := by
      rw [hxe, ht, Real.div_rpow (by positivity) hρ0.le]
      calc C₁ * (((B : ℝ) * m) ^ α / ρ ^ α) = C₁ * ((B : ℝ) * m) ^ α * ρ ^ (-α) := by
            rw [Real.rpow_neg hρ0.le]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hv.1 (Real.rpow_nonneg hρ0.le _)
    have hsx1 : Real.sqrt x ≤ Real.sqrt C₂ * t ^ (α / 2) := by
      calc Real.sqrt x ≤ Real.sqrt (C₂ * t ^ α) := Real.sqrt_le_sqrt hxup
        _ = _ := by rw [Real.sqrt_mul hC₂.le, hsq t ht0]
    have hsx2 : Real.sqrt C₁ * t ^ (α / 2) ≤ Real.sqrt x := by
      calc Real.sqrt C₁ * t ^ (α / 2) = Real.sqrt (C₁ * t ^ α) := by
            rw [Real.sqrt_mul hC₁.le, hsq t ht0]
        _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hxlo
    have hs1 : 0 < Real.sqrt C₁ := Real.sqrt_pos.2 hC₁
    have htp : 0 < t ^ (α / 2) := Real.rpow_pos_of_pos ht0 _
    have hSa : Real.sqrt x / (1 + x) ≤ M0 * t ^ (α / 2) :=
      hS1.trans (hsx1.trans (mul_le_mul_of_nonneg_right hM2 htp.le))
    have hSb : Real.sqrt x / (1 + x) ≤ M0 * t ^ (-(α / 2)) := by
      refine hS2.trans ?_
      have h5 : 1 / Real.sqrt x ≤ 1 / (Real.sqrt C₁ * t ^ (α / 2)) :=
        one_div_le_one_div_of_le (by positivity) hsx2
      refine h5.trans ?_
      have e : 1 / (Real.sqrt C₁ * t ^ (α / 2)) = 1 / Real.sqrt C₁ * t ^ (-(α / 2)) := by
        rw [Real.rpow_neg ht0.le]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right hM1 (Real.rpow_nonneg ht0.le _)
    have hmin : Real.sqrt x / (1 + x) ≤ M0 * min (t ^ (α / 2)) (t ^ (-(α / 2))) := by
      rw [mul_min_of_nonneg _ _ hM0pos.le]; exact le_min hSa hSb
    rw [if_neg hmB, if_pos hmB']
    simp only [zero_add]
    refine hkey.trans ?_
    calc Real.sqrt x / (1 + x) * (4 * Cθ) * (if m ≤ 1 then 1 / m else m ^ (-(1 / 2 : ℝ)))
        ≤ M0 * min (t ^ (α / 2)) (t ^ (-(α / 2))) * (4 * Cθ) *
            (if m ≤ 1 then 1 / m else m ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmin (by positivity)) hvm0
      _ = 4 * Cθ * M0 * (min (t ^ (α / 2)) (t ^ (-(α / 2))) *
            (if m ≤ 1 then 1 / m else m ^ (-(1 / 2 : ℝ)))) := by ring

private lemma pg9_M_int2 {α B ρ A : ℝ} (hB : 0 < B) (hA : 0 ≤ A) (hρ : 0 < ρ) {kf : ℝ → ℝ}
    (hkf : IntegrableOn kf (Ioi 0)) {S : Set ℝ} (hS : S ⊆ Ioi 0) :
    IntegrableOn (fun m : ℝ => A * ((if m < 1 / B then Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ))
          else 0) + kf m)) S ∧
    ∫ m in S, A * ((if m < 1 / B then Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) +
        kf m) ≤ A * (2 * ρ ^ (-(α / 2)) + ∫ m in S, kf m) := by
  obtain ⟨hPi, hPv⟩ := pg9_P_int (α := α) (ρ := ρ) hB
  have hPi' : IntegrableOn (fun m : ℝ => if m < 1 / B then Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ))
      else 0) (Ioi 0) := hPi
  have hPS := hPi'.mono_set hS
  have hkS := hkf.mono_set hS
  refine ⟨(hPS.add hkS).const_mul A, ?_⟩
  rw [integral_const_mul, integral_add hPS hkS]
  refine mul_le_mul_of_nonneg_left ?_ hA
  have hPnn : ∀ m ∈ Ioi (0:ℝ), 0 ≤ (if m < 1 / B then Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ))
      else 0) := by
    intro m hm
    split_ifs
    · have : 0 < m := hm
      positivity
    · exact le_rfl
  have hP1 : ∫ m in S, (if m < 1 / B then Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) ≤
      ∫ m in Ioi (0:ℝ), (if m < 1 / B then Real.sqrt B * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) := by
    refine setIntegral_mono_set hPi' ?_ hS.eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with m hm
    exact hPnn m hm
  rw [hPv] at hP1
  linarith

private lemma pg9_g0_int {α : ℝ} (hα1 : 1 < α) :
    IntegrableOn (fun r : ℝ => if r ≤ 1 then r ^ (α / 2 - 1) else r ^ (-((α + 1) / 2))) (Ioi 0) := by
  have hkf := vs_k_int (α := α) (K := 1) (A := 1) (B := 1) hα1
  refine hkf.congr (Eventually.of_forall fun m => ?_)
  simp only [one_mul]

private lemma pg9_g0_nonneg {α : ℝ} {r : ℝ} (hr : 0 < r) :
    0 ≤ (if r ≤ 1 then r ^ (α / 2 - 1) else r ^ (-((α + 1) / 2))) := by
  split_ifs
  · exact Real.rpow_nonneg hr.le _
  · exact Real.rpow_nonneg hr.le _

private lemma pg9_g0_scale_Ioc {α X b : ℝ} (hX : 0 < X) (hb : 0 < b) :
    ∫ m in Ioc (0:ℝ) b, (if m / X ≤ 1 then (m / X) ^ (α / 2 - 1) else (m / X) ^ (-((α + 1) / 2))) =
      X * ∫ r in Ioc (0:ℝ) (b / X), (if r ≤ 1 then r ^ (α / 2 - 1) else r ^ (-((α + 1) / 2))) := by
  rw [← intervalIntegral.integral_of_le hb.le, ← intervalIntegral.integral_of_le (by positivity)]
  rw [intervalIntegral.integral_comp_div (fun r : ℝ => if r ≤ 1 then r ^ (α / 2 - 1) else r ^ (-((α + 1) / 2))) hX.ne']
  simp only [zero_div, smul_eq_mul]

private lemma pg9_g0_scale_Ioi {α X b : ℝ} (hX : 0 < X) :
    ∫ m in Ioi b, (if m / X ≤ 1 then (m / X) ^ (α / 2 - 1) else (m / X) ^ (-((α + 1) / 2))) =
      X * ∫ r in Ioi (b / X), (if r ≤ 1 then r ^ (α / 2 - 1) else r ^ (-((α + 1) / 2))) := by
  have := integral_comp_mul_left_Ioi (fun r : ℝ => if r ≤ 1 then r ^ (α / 2 - 1) else r ^ (-((α + 1) / 2)))
    b (inv_pos.2 hX)
  simp only [inv_inv, smul_eq_mul] at this
  have e : ∀ m : ℝ, m / X = X⁻¹ * m := fun m => by rw [div_eq_inv_mul]
  simp only [e]
  rw [this, div_eq_inv_mul]

private lemma pg9_zero_maj {α Kp X m : ℝ} (hα0 : 0 < α) (hKp : 0 < Kp) (hX : 0 < X) (hX1 : X ≤ 1)
    (hm : 0 < m) :
    min ((Kp * m / X) ^ (α / 2)) ((Kp * m / X) ^ (-(α / 2))) *
        (if m ≤ 1 then 1 / m else m ^ (-(1 / 2 : ℝ))) ≤
      max (Kp ^ (α / 2)) (Kp ^ (-(α / 2))) *
        (X⁻¹ * (if m / X ≤ 1 then (m / X) ^ (α / 2 - 1) else (m / X) ^ (-((α + 1) / 2)))) := by
  set r : ℝ := m / X with hr
  have hr0 : 0 < r := div_pos hm hX
  have hKr : Kp * m / X = Kp * r := by rw [hr]; ring
  have hmX : m = X * r := by rw [hr]; field_simp
  rw [hKr]
  have hc1 : Kp ^ (α / 2) ≤ max (Kp ^ (α / 2)) (Kp ^ (-(α / 2))) := le_max_left _ _
  have hc2 : Kp ^ (-(α / 2)) ≤ max (Kp ^ (α / 2)) (Kp ^ (-(α / 2))) := le_max_right _ _
  have hKpa : 0 < Kp ^ (α / 2) := Real.rpow_pos_of_pos hKp _
  have hKpb : 0 < Kp ^ (-(α / 2)) := Real.rpow_pos_of_pos hKp _
  have hra : 0 < r ^ (α / 2) := Real.rpow_pos_of_pos hr0 _
  have hrb : 0 < r ^ (-(α / 2)) := Real.rpow_pos_of_pos hr0 _
  have e1 : (Kp * r) ^ (α / 2) = Kp ^ (α / 2) * r ^ (α / 2) := Real.mul_rpow hKp.le hr0.le
  have e2 : (Kp * r) ^ (-(α / 2)) = Kp ^ (-(α / 2)) * r ^ (-(α / 2)) := Real.mul_rpow hKp.le hr0.le
  have hXi : 0 < X⁻¹ := inv_pos.2 hX
  by_cases hm1 : m ≤ 1
  · rw [if_pos hm1]
    have h1m : 1 / m = X⁻¹ * (1 / r) := by rw [hmX]; field_simp
    rw [h1m]
    by_cases hr1 : r ≤ 1
    · rw [if_pos hr1]
      have : min ((Kp * r) ^ (α / 2)) ((Kp * r) ^ (-(α / 2))) ≤ Kp ^ (α / 2) * r ^ (α / 2) :=
        (min_le_left _ _).trans (le_of_eq e1)
      calc min ((Kp * r) ^ (α / 2)) ((Kp * r) ^ (-(α / 2))) * (X⁻¹ * (1 / r))
          ≤ Kp ^ (α / 2) * r ^ (α / 2) * (X⁻¹ * (1 / r)) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = Kp ^ (α / 2) * (X⁻¹ * r ^ (α / 2 - 1)) := by
            rw [Real.rpow_sub_one hr0.ne']; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hc1 (by positivity)
    · rw [if_neg hr1]
      have hr1' : 1 < r := not_le.1 hr1
      have : min ((Kp * r) ^ (α / 2)) ((Kp * r) ^ (-(α / 2))) ≤ Kp ^ (-(α / 2)) * r ^ (-(α / 2)) :=
        (min_le_right _ _).trans (le_of_eq e2)
      calc min ((Kp * r) ^ (α / 2)) ((Kp * r) ^ (-(α / 2))) * (X⁻¹ * (1 / r))
          ≤ Kp ^ (-(α / 2)) * r ^ (-(α / 2)) * (X⁻¹ * (1 / r)) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = Kp ^ (-(α / 2)) * (X⁻¹ * r ^ (-(α / 2) - 1)) := by
            rw [Real.rpow_sub_one hr0.ne']; field_simp
        _ ≤ Kp ^ (-(α / 2)) * (X⁻¹ * r ^ (-((α + 1) / 2))) := by
            apply mul_le_mul_of_nonneg_left _ hKpb.le
            apply mul_le_mul_of_nonneg_left _ hXi.le
            exact Real.rpow_le_rpow_of_exponent_le hr1'.le (by linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_right hc2 (by positivity)
  · have hm1' : 1 < m := not_le.1 hm1
    rw [if_neg hm1]
    have hr1' : 1 < r := by
      rw [hr, lt_div_iff₀ hX]; linarith
    rw [if_neg (not_le.2 hr1')]
    have : min ((Kp * r) ^ (α / 2)) ((Kp * r) ^ (-(α / 2))) ≤ Kp ^ (-(α / 2)) * r ^ (-(α / 2)) :=
      (min_le_right _ _).trans (le_of_eq e2)
    have hmh : m ^ (-(1 / 2 : ℝ)) = X ^ (-(1 / 2 : ℝ)) * r ^ (-(1 / 2 : ℝ)) := by
      rw [hmX, Real.mul_rpow hX.le hr0.le]
    have hXh : X ^ (-(1 / 2 : ℝ)) ≤ X⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_ge hX hX1 (by norm_num)
    have hrr : r ^ (-(α / 2)) * r ^ (-(1 / 2 : ℝ)) = r ^ (-((α + 1) / 2)) := by
      rw [← Real.rpow_add hr0]; congr 1; ring
    calc min ((Kp * r) ^ (α / 2)) ((Kp * r) ^ (-(α / 2))) * m ^ (-(1 / 2 : ℝ))
        ≤ Kp ^ (-(α / 2)) * r ^ (-(α / 2)) * (X ^ (-(1 / 2 : ℝ)) * r ^ (-(1 / 2 : ℝ))) := by
          rw [hmh]
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = Kp ^ (-(α / 2)) * (X ^ (-(1 / 2 : ℝ)) * r ^ (-((α + 1) / 2))) := by
          rw [← hrr]; ring
      _ ≤ Kp ^ (-(α / 2)) * (X⁻¹ * r ^ (-((α + 1) / 2))) := by
          apply mul_le_mul_of_nonneg_left _ hKpb.le
          exact mul_le_mul_of_nonneg_right hXh (Real.rpow_nonneg hr0.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hc2 (by positivity)

set_option maxHeartbeats 3200000 in
private lemma pg9_tail_seq0 {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 0)) :
    ∀ ε' > 0, ∃ k0 : ℕ, ∀ k ≥ k0, ∀ᶠ n in atTop, ∀ s : Finset ℤ,
      ∫ p in (Ioo 0 (gammaOf (N n) (B n)) ×ˢ Ioo 0 (gammaOf (N n) (B n))) \
        (Icc (rowIdx (i n) / icCross α (B n) / ((k : ℝ) + 1))
            (rowIdx (i n) / icCross α (B n) * ((k : ℝ) + 1)) ×ˢ
          Icc (rowIdx (i n) / icCross α (B n) / ((k : ℝ) + 1))
            (rowIdx (i n) / icCross α (B n) * ((k : ℝ) + 1))),
        ∑ ℓ ∈ s, lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2 ≤ ε' := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  obtain ⟨C1, C2, hC1, hC2, htail⟩ := pg9_tail_fin hα1 R.hβ0 R.hβ1
  obtain ⟨A, hA, hkbd⟩ := pg9_k_bd2 hα1 R.hβ0 R.hβ1
  obtain ⟨Cup, hup⟩ := lem_app_pl_upper (α := α) (β := β) (1 / 8) (by norm_num) (by norm_num)
  have hupn := hup N B c R
  set g0 : ℝ → ℝ := fun r => if r ≤ 1 then r ^ (α / 2 - 1) else r ^ (-((α + 1) / 2)) with hg0
  have hg0i : IntegrableOn g0 (Ioi 0) := pg9_g0_int hα1
  set cK : ℝ := max (Kc α ^ (α / 2)) (Kc α ^ (-(α / 2))) with hcK
  have hcK0 : 0 < cK := lt_of_lt_of_le (Real.rpow_pos_of_pos hK _) (le_max_left _ _)
  set Kg : ℝ := ∫ r in Ioi (0:ℝ), g0 r with hKg
  have hKg0 : 0 ≤ Kg := setIntegral_nonneg measurableSet_Ioi (fun r hr => pg9_g0_nonneg hr)
  set Kf : ℝ := cK * Kg with hKf
  have hKf0 : 0 ≤ Kf := by positivity
  have hτ := pg9_tauk_lim (α := α) hα1 (aL := 1) (aU := 1) one_pos one_pos
  simp only [Real.one_rpow, div_one, one_mul] at hτ
  intro ε' hε'
  set Cu : ℝ := max Cup 0 with hCu
  have hCu0 : 0 ≤ Cu := le_max_right _ _
  set τg : ℕ → ℝ := fun k => (∫ r in Ioc (0:ℝ) (1 / ((k : ℝ) + 1)), g0 r) +
    ∫ r in Ioi ((k : ℝ) + 1), g0 r with hτg
  have hτg' : Tendsto τg atTop (𝓝 0) := hτ
  have hLk : ∀ᶠ k : ℕ in atTop, C1 * A ^ 2 * ((cK * τg k) * Kf) < ε' := by
    have := ((hτg'.const_mul cK).mul_const Kf).const_mul (C1 * A ^ 2)
    simp only [mul_zero, zero_mul] at this
    exact this.eventually (gt_mem_nhds hε')
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 hLk
  refine ⟨k0, fun k hk => ?_⟩
  have hLk' := hk0 k hk
  set τk : ℝ := cK * τg k with hτk
  have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  have hρ0 : Tendsto (fun n => (rowIdx (i n)) ^ (-(α / 2))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity)).comp hi
  have hrb : Tendsto (fun n => (1:ℝ) ^ (α / 2) * gammaOf (N n) (B n) ^ (-((α - 1) / 2))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (y := (α - 1) / 2) (by linarith)).comp hg).const_mul ((1:ℝ) ^ (α / 2))
    simpa using this
  have hsb : Tendsto (fun n => (1:ℝ) ^ α * gammaOf (N n) (B n) ^ (-(α - 1))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (y := α - 1) (by linarith)).comp hg).const_mul ((1:ℝ) ^ α)
    simpa using this
  have hεn : Tendsto (fun n => 2 * (rowIdx (i n)) ^ (-(α / 2))) atTop (𝓝 0) := by
    simpa using hρ0.const_mul 2
  have hbn : Tendsto (fun n => C1 * A ^ 2 * ((2 * (2 * (rowIdx (i n)) ^ (-(α / 2))) + τk) *
      (2 * (rowIdx (i n)) ^ (-(α / 2)) + Kf)) +
      C2 * A * (2 * (rowIdx (i n)) ^ (-(α / 2)) + Kf) *
        ((1:ℝ) ^ (α / 2) * gammaOf (N n) (B n) ^ (-((α - 1) / 2))) +
      Real.pi ^ 2 * (Cu * ((1:ℝ) ^ α * gammaOf (N n) (B n) ^ (-(α - 1))))) atTop
      (𝓝 (C1 * A ^ 2 * ((2 * 0 + τk) * (0 + Kf)) + C2 * A * (0 + Kf) * 0 + Real.pi ^ 2 * (Cu * 0))) := by
    refine Tendsto.add (Tendsto.add ?_ ?_) ?_
    · exact (((hεn.const_mul 2).add_const τk).mul (hεn.add_const Kf)).const_mul _
    · exact ((hεn.add_const Kf).const_mul (C2 * A)).mul hrb
    · exact (hsb.const_mul Cu).const_mul _
  have hbn' : ∀ᶠ n in atTop, C1 * A ^ 2 * ((2 * (2 * (rowIdx (i n)) ^ (-(α / 2))) + τk) *
      (2 * (rowIdx (i n)) ^ (-(α / 2)) + Kf)) +
      C2 * A * (2 * (rowIdx (i n)) ^ (-(α / 2)) + Kf) *
        ((1:ℝ) ^ (α / 2) * gammaOf (N n) (B n) ^ (-((α - 1) / 2))) +
      Real.pi ^ 2 * (Cu * ((1:ℝ) ^ α * gammaOf (N n) (B n) ^ (-(α - 1)))) < ε' := by
    refine hbn.eventually (gt_mem_nhds ?_)
    simp only [mul_zero, zero_add, add_zero]
    exact hLk'
  have hX' : ∀ᶠ n in atTop, rowIdx (i n) / icCross α (B n) < min 1 (Kc α) :=
    (tendsto_order.1 hX).2 _ (lt_min one_pos hK)
  have hXp : ∀ᶠ n in atTop, 0 < rowIdx (i n) / icCross α (B n) := by
    filter_upwards [hi.eventually_gt_atTop 0, R.hB.eventually_gt_atTop 0] with n h1 h2
    unfold icCross; positivity
  filter_upwards [hbn', hX', hXp, hg.eventually_ge_atTop 2, hupn, hi.eventually_gt_atTop 0]
    with n h1 h2 hXp' h3 h4 h5
  intro s
  have hN := R.hNpos n
  have hB := R.hBpos n
  have hc := R.hcpos n
  have hBr : (0:ℝ) < (B n : ℝ) := by exact_mod_cast hB
  set ρ : ℝ := ((i n : ℕ) : ℝ) + 1 with hρ
  have hρdef : rowIdx (i n) = ρ := rfl
  have hρ0 : 0 < ρ := by positivity
  rw [hρdef] at h1
  set X : ℝ := rowIdx (i n) / icCross α (B n) with hXdef
  have key : X = Kc α * (ρ / (B n : ℝ)) := by
    rw [hXdef]; unfold icCross; rw [hρdef]; field_simp
  have hX1 : X ≤ 1 := (lt_of_lt_of_le h2 (min_le_left _ _)).le
  have hρaU : ρ / (B n : ℝ) ≤ 1 := by
    have : X < Kc α := lt_of_lt_of_le h2 (min_le_right _ _)
    rw [key] at this
    rw [div_le_one hBr]
    have h' : ρ / (B n : ℝ) < 1 := by
      by_contra h; push_neg at h; nlinarith
    rw [div_lt_one hBr] at h'
    exact h'.le
  obtain ⟨hUp1, hUp2, hUp3⟩ := h4 (i n)
  have hγ0 : 0 < gammaOf (N n) (B n) := by linarith
  set γ := gammaOf (N n) (B n) with hγdef
  have hε0 : 0 ≤ 2 * ρ ^ (-(α / 2)) := by positivity
  set kfn : ℝ → ℝ := fun m => cK * (X⁻¹ * g0 (m / X)) with hkfn
  have hkfi : IntegrableOn kfn (Ioi 0) := by
    have h1 : IntegrableOn (fun m : ℝ => g0 (X⁻¹ * m)) (Ioi 0) :=
      (integrableOn_Ioi_comp_mul_left_iff g0 0 (inv_pos.2 hXp')).2 (by rw [mul_zero]; exact hg0i)
    have h2 : IntegrableOn (fun m : ℝ => cK * (X⁻¹ * g0 (X⁻¹ * m))) (Ioi 0) :=
      (h1.const_mul X⁻¹).const_mul cK
    refine h2.congr_fun (fun m _ => ?_) measurableSet_Ioi
    simp only [hkfn, div_eq_inv_mul]
  have hkfnn : ∀ m : ℝ, 0 < m → 0 ≤ kfn m := by
    intro m hm
    simp only [hkfn]
    have := pg9_g0_nonneg (α := α) (div_pos hm hXp')
    positivity
  have hKfv : ∫ m in Ioi (0:ℝ), kfn m = Kf := by
    simp only [hkfn, hg0]
    rw [integral_const_mul, integral_const_mul, pg9_g0_scale_Ioi hXp']
    simp only [zero_div, hKf, hKg, hg0]
    field_simp
  have hτv : (∫ m in Ioc (0:ℝ) (X / ((k : ℝ) + 1)), kfn m) + (∫ m in Ioi (X * ((k : ℝ) + 1)), kfn m) = τk := by
    simp only [hkfn, hg0]
    rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      pg9_g0_scale_Ioc hXp' (by positivity), pg9_g0_scale_Ioi hXp']
    have e1 : X / ((k : ℝ) + 1) / X = 1 / ((k : ℝ) + 1) := by field_simp
    have e2 : X * ((k : ℝ) + 1) / X = (k : ℝ) + 1 := by field_simp
    rw [e1, e2, hτk]
    simp only [hτg, hg0]
    have hXX : X⁻¹ * X = 1 := inv_mul_cancel₀ hXp'.ne'
    rw [← mul_assoc X⁻¹ X, hXX, one_mul, ← mul_assoc X⁻¹ X, hXX, one_mul]
    ring
  have hδ : (0:ℝ) < X / ((k : ℝ) + 1) := by positivity
  have hδR : X / ((k : ℝ) + 1) ≤ X * ((k : ℝ) + 1) := by
    have h1 : (1:ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ hXp'.le
    calc ((k : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
      _ ≤ _ := h1
  set M : ℝ → ℝ := fun m => A * ((if m < 1 / (B n : ℝ) then
      Real.sqrt (B n : ℝ) * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) + kfn m) with hM
  have hMint : ∀ S : Set ℝ, S ⊆ Ioi 0 → MeasurableSet S →
      IntegrableOn M S ∧ ∫ m in S, M m ≤ A * (2 * ρ ^ (-(α / 2)) + ∫ m in S, kfn m) :=
    fun S hS hSm => pg9_M_int2 (α := α) (B := (B n : ℝ)) (ρ := ρ) (A := A) hBr hA.le hρ0 hkfi hS
  have hMnn : ∀ m : ℝ, 0 < m → 0 ≤ M m := by
    intro m hm
    simp only [hM]
    have := hkfnn m hm
    have : 0 ≤ (if m < 1 / (B n : ℝ) then
      Real.sqrt (B n : ℝ) * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) := by
      split_ifs
      · positivity
      · exact le_rfl
    positivity
  have hkM : ∀ m ∈ Ioc 0 (gammaOf (N n) (B n) / 2),
      Wpart β (B n) (plSpec α (c n) (N n)) (i n) m * min (Real.sqrt m) 1 ≤ M m := by
    intro m hm
    refine (hkbd (N n) (B n) (c n) hN hB hc (i n) m (by linarith) hm.1 hm.2).trans ?_
    simp only [hM]
    refine mul_le_mul_of_nonneg_left (add_le_add (le_of_eq rfl) ?_) hA.le
    by_cases hmB : 1 / (B n : ℝ) ≤ m
    · rw [if_pos hmB]
      have hmaj := pg9_zero_maj (α := α) (Kp := Kc α) (X := X) (m := m) hα0 hK hXp' hX1 hm.1
      have e : Kc α * m / X = (B n : ℝ) * m / ρ := by
        rw [key]; field_simp
      rw [e] at hmaj
      exact hmaj
    · rw [if_neg hmB]; exact hkfnn m hm.1
  have hUint := (lem_app_pl_age_iv hα0 R.hβ0 R.hβ1 (N n) (B n) (c n) hN hB hc (i n)).2.2.1
  have hSb := pg9_regS hα0 R.hβ0 R.hβ1 hN hB hc (i n) s Cup (by
    intro ℓ; have := (hUp1 ℓ); rwa [show (1 / 8 : ℝ) * gammaOf (N n) (B n) = gammaOf (N n) (B n) / 8 by ring] at this)
    (by have := hUp2; rwa [show (1 / 8 : ℝ) * gammaOf (N n) (B n) = gammaOf (N n) (B n) / 8 by ring] at this)
    (by have := hUp3; rwa [show (1 / 8 : ℝ) * gammaOf (N n) (B n) = gammaOf (N n) (B n) / 8 by ring] at this)
  have hfin := htail (N n) (B n) (c n) hN hB hc (i n) s (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) A
    (2 * ρ ^ (-(α / 2))) Kf τk _ kfn M h3 hδ hδR hA.le hε0 hKf0 hUint hMnn hMint hkfnn hkfi hkM
    hKfv hτv hSb
  obtain ⟨hd1, hd2⟩ := pg9_decay_bounds hα1 hN hB hρ0 hρaU
  have hq0 : 0 ≤ C2 * A * (2 * ρ ^ (-(α / 2)) + Kf) := by positivity
  have hS1 : Cup * γ * (ρ / (N n : ℝ)) ^ α ≤ Cu * ((1:ℝ) ^ α * γ ^ (-(α - 1))) := by
    have hpos : 0 ≤ γ * (ρ / (N n : ℝ)) ^ α := by positivity
    calc Cup * γ * (ρ / (N n : ℝ)) ^ α = Cup * (γ * (ρ / (N n : ℝ)) ^ α) := by ring
      _ ≤ Cu * (γ * (ρ / (N n : ℝ)) ^ α) := mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
      _ ≤ Cu * ((1:ℝ) ^ α * γ ^ (-(α - 1))) := mul_le_mul_of_nonneg_left hd2 hCu0
  have h6 : C2 * A * (2 * ρ ^ (-(α / 2)) + Kf) * (ρ / (N n : ℝ)) ^ (α / 2) * Real.sqrt γ ≤
      C2 * A * (2 * ρ ^ (-(α / 2)) + Kf) * ((1:ℝ) ^ (α / 2) * γ ^ (-((α - 1) / 2))) := by
    rw [mul_assoc _ ((ρ / (N n : ℝ)) ^ (α / 2))]
    exact mul_le_mul_of_nonneg_left hd1 hq0
  have h7 : Real.pi ^ 2 * (Cup * γ * (ρ / (N n : ℝ)) ^ α) ≤
      Real.pi ^ 2 * (Cu * ((1:ℝ) ^ α * γ ^ (-(α - 1)))) :=
    mul_le_mul_of_nonneg_left hS1 (by positivity)
  linarith

private lemma pg9_S_ratio {r x' : ℕ → ℝ} (hx' : ∀ n, 0 < x' n) (hr : Tendsto r atTop (𝓝 1))
    (hr0 : ∀ n, 0 < r n) :
    Tendsto (fun n => (Real.sqrt (r n * x' n) / (1 + r n * x' n)) /
      (Real.sqrt (x' n) / (1 + x' n))) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 1).comp hr
  have h2 : Tendsto (fun n => (1 + x' n) / (1 + r n * x' n)) atTop (𝓝 1) := by
    have hb : ∀ n, (1 + x' n) / (1 + r n * x' n) = 1 + (1 - r n) * (x' n / (1 + r n * x' n)) := by
      intro n
      have := hx' n; have := hr0 n
      field_simp; ring
    have h3 : Tendsto (fun n => (1 - r n) * (x' n / (1 + r n * x' n))) atTop (𝓝 0) := by
      -- bounded by |1 - r n| / r n
      have h4 : Tendsto (fun n => |1 - r n| / r n) atTop (𝓝 0) := by
        have : Tendsto (fun n => |1 - r n|) atTop (𝓝 0) := by
          have := (tendsto_const_nhds (x := (1:ℝ))).sub hr
          simpa using this.abs
        simpa [Pi.div_def] using this.div hr one_ne_zero
      refine squeeze_zero_norm (fun n => ?_) h4
      have := hx' n; have := hr0 n
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ x' n / (1 + r n * x' n))]
      have : x' n / (1 + r n * x' n) ≤ 1 / r n := by
        rw [div_le_div_iff₀ (by positivity) (hr0 n)]; nlinarith
      calc |1 - r n| * (x' n / (1 + r n * x' n)) ≤ |1 - r n| * (1 / r n) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = _ := by ring
    simp only [hb]
    simpa using h3.const_add 1
  have e : ∀ n, (Real.sqrt (r n * x' n) / (1 + r n * x' n)) / (Real.sqrt (x' n) / (1 + x' n)) =
      Real.sqrt (r n) * ((1 + x' n) / (1 + r n * x' n)) := by
    intro n
    have := hx' n; have := hr0 n
    have hs : 0 < Real.sqrt (x' n) := Real.sqrt_pos.2 (hx' n)
    rw [Real.sqrt_mul (hr0 n).le]
    field_simp
  simp only [e]
  simpa using h1.mul h2

private lemma pg9_theta_ratio {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (m : ℕ → ℝ) (hm0 : ∀ n, 0 < m n)
    (hBm : Tendsto (fun n => ((B n : ℕ) : ℝ) * m n) atTop atTop)
    (hmγ : Tendsto (fun n => m n / gammaOf (N n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => thetaN β (B n) (plSpec α (c n) (N n)) (m n) / profTheta α β (m n))
      atTop (𝓝 1) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨cE, hcE, hE⟩ := vs_E_lb R.hβ0 R.hβ1
  have hii := lem_app_pl_finite_inverse_iv_ii R hα1 m hBm hmγ
  have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  have hmg : Tendsto (fun n => m n / (gammaOf (N n) (B n) - m n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => 1 - m n / gammaOf (N n) (B n)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hmγ
    have h2 := hmγ.div h1 one_ne_zero
    simp only [zero_div] at h2
    refine h2.congr' ?_
    filter_upwards [hmγ.eventually (gt_mem_nhds (zero_lt_one' ℝ)), hg.eventually_gt_atTop 0] with n h1 h2
    simp only [Pi.div_apply]
    have : 0 < 1 - m n / gammaOf (N n) (B n) := by linarith
    field_simp
  have he : Tendsto (fun n => (m n * deriv (partLam (B n) (plSpec α (c n) (N n))) (m n) /
      partLam (B n) (plSpec α (c n) (N n)) (m n) - α) + m n / (gammaOf (N n) (B n) - m n))
      atTop (𝓝 0) := by
    simpa using (hii.sub_const α).add hmg
  have hpos : ∀ n, α - 1 ≤ m n * profTheta α β (m n) := by
    intro n
    have hE0 : 0 < Efun β (m n) := lt_of_lt_of_le (mul_pos hcE (lt_min (hm0 n) one_pos)) (hE _ (hm0 n))
    unfold profTheta
    have : 0 < 1 / Efun β (m n) := by positivity
    have hmne : m n ≠ 0 := (hm0 n).ne'
    have e : m n * (1 / Efun β (m n) + (α - 1) / m n) = m n * (1 / Efun β (m n)) + (α - 1) := by
      field_simp
    rw [e]
    nlinarith [mul_pos (hm0 n) this]
  have hlim : Tendsto (fun n => ((m n * deriv (partLam (B n) (plSpec α (c n) (N n))) (m n) /
      partLam (B n) (plSpec α (c n) (N n)) (m n) - α) + m n / (gammaOf (N n) (B n) - m n)) /
      (m n * profTheta α β (m n))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (by simpa using he.norm.div_const (α - 1))
    rw [Real.norm_eq_abs, abs_div]
    have h1 : α - 1 ≤ |m n * profTheta α β (m n)| := (hpos n).trans (le_abs_self _)
    have h2 : 0 < α - 1 := by linarith
    exact div_le_div_of_nonneg_left (abs_nonneg _) h2 h1
  have := hlim.const_add 1
  simp only [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hg.eventually_gt_atTop 0, hmγ.eventually (gt_mem_nhds (zero_lt_one' ℝ))] with n hγ hq
  have hmn := hm0 n
  have hγm : 0 < gammaOf (N n) (B n) - m n := by
    have : m n / gammaOf (N n) (B n) < 1 := hq
    rw [div_lt_one hγ] at this; linarith
  have hθ0 : 0 < profTheta α β (m n) := by
    have := hpos n
    by_contra h
    push_neg at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hmn.le h]
  have hmne : m n ≠ 0 := hmn.ne'
  have hkey : thetaN β (B n) (plSpec α (c n) (N n)) (m n) - profTheta α β (m n) =
      ((m n * deriv (partLam (B n) (plSpec α (c n) (N n))) (m n) /
        partLam (B n) (plSpec α (c n) (N n)) (m n) - α) + m n / (gammaOf (N n) (B n) - m n)) / m n := by
    unfold thetaN profTheta
    have hγm' : gammaOf (N n) (B n) - m n ≠ 0 := hγm.ne'
    field_simp
    ring
  have hθne : profTheta α β (m n) ≠ 0 := hθ0.ne'
  have hm1 : m n * profTheta α β (m n) ≠ 0 := mul_ne_zero hmne hθne
  have hkey' : thetaN β (B n) (plSpec α (c n) (N n)) (m n) = profTheta α β (m n) +
      ((m n * deriv (partLam (B n) (plSpec α (c n) (N n))) (m n) /
        partLam (B n) (plSpec α (c n) (N n)) (m n) - α) + m n / (gammaOf (N n) (B n) - m n)) / m n := by
    linarith [hkey]
  rw [hkey']
  field_simp

private lemma pg9_delta_close {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (u v : ℕ → ℝ) (ℓ : ℕ → ℤ)
    (hu0 : ∀ n, 0 < u n) (hv0 : ∀ n, 0 < v n)
    (hBu : Tendsto (fun n => ((B n : ℕ) : ℝ) * u n) atTop atTop)
    (hBv : Tendsto (fun n => ((B n : ℕ) : ℝ) * v n) atTop atTop)
    (huγ : Tendsto (fun n => u n / gammaOf (N n) (B n)) atTop (𝓝 0))
    (hvγ : Tendsto (fun n => v n / gammaOf (N n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) (u n) (v n) -
      profDelta α β (ℓ n) (u n) (v n)) atTop (𝓝 0) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  have hratio := pg9_TN_ratio R hα1 u v hu0 hv0 hBu hBv huγ hvγ
  have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  have hγpos : ∀ n, 0 < gammaOf (N n) (B n) := fun n => by
    unfold gammaOf; exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
  have hqγ : Tendsto (fun n => max (u n) (v n) / gammaOf (N n) (B n)) atTop (𝓝 0) := by
    have := huγ.max hvγ
    simp only [max_self] at this
    refine this.congr (fun n => ?_)
    simp only [div_eq_mul_inv]
    rw [max_mul_of_nonneg _ _ (inv_nonneg.2 (hγpos n).le)]
  have hT1 : Tendsto (fun n => |TNpart (B n) (plSpec α (c n) (N n)) (u n) (v n) /
      profT α (u n) (v n) - 1|) atTop (𝓝 0) := by
    simpa using (hratio.sub_const 1).abs
  have hbd : Tendsto (fun n => |TNpart (B n) (plSpec α (c n) (N n)) (u n) (v n) /
      profT α (u n) (v n) - 1| + 4 * (max (u n) (v n) / gammaOf (N n) (B n))) atTop (𝓝 0) := by
    simpa using hT1.add (hqγ.const_mul 4)
  refine squeeze_zero_norm' ?_ hbd
  filter_upwards [hratio.eventually (gt_mem_nhds (by norm_num : (1:ℝ) < 2)),
    hratio.eventually (lt_mem_nhds (zero_lt_one' ℝ)),
    huγ.eventually (gt_mem_nhds (zero_lt_one' ℝ)), hvγ.eventually (gt_mem_nhds (zero_lt_one' ℝ))]
    with n hT2 hT0 hu1 hv1
  have hN := R.hNpos n
  have hB := R.hBpos n
  have hc := R.hcpos n
  have hγ := hγpos n
  have hu := hu0 n
  have hv := hv0 n
  have hum : u n ∈ Ioo 0 (gammaOf (N n) (B n)) := ⟨hu, by
    have : u n / gammaOf (N n) (B n) < 1 := hu1
    rwa [div_lt_one hγ] at this⟩
  have hvm : v n ∈ Ioo 0 (gammaOf (N n) (B n)) := ⟨hv, by
    have : v n / gammaOf (N n) (B n) < 1 := hv1
    rwa [div_lt_one hγ] at this⟩
  obtain ⟨hM0, hMm, hD⟩ := lem_app_pl_determinant_i (α := α) (β := β) hα0 R.hβ0 R.hβ1 (N n) (B n) (c n)
    hN hB hc (ℓ n) (u n) (v n) hum hvm
  set M := MLag β (Qm β (u n)) (Qm β (v n)) (ℓ n) with hM
  set D := DLag β (Qm β (u n)) (Qm β (v n)) (ℓ n) with hDdef
  set T := TNpart (B n) (plSpec α (c n) (N n)) (u n) (v n) with hT
  set t := profT α (u n) (v n) with ht
  set q := max (u n) (v n) with hq
  set p := min (u n) (v n) with hp
  have hp0 : 0 < p := lt_min hu hv
  have hq0 : 0 < q := lt_of_lt_of_le hu (le_max_left _ _)
  have hpq : p * q = u n * v n := min_mul_max _ _
  have htpos : 0 < t := lt_of_lt_of_le (div_pos hp0 (by positivity)) (pg9_profT_lb hα1 hu hv)
  have htq : t ≤ q := by
    have := vs_T_le hα1 hu hv
    have h1 : (1 - 1 / α) * max (u n) (v n) ≤ max (u n) (v n) := by
      have : 0 ≤ 1 / α * max (u n) (v n) := by positivity
      nlinarith
    exact this.trans h1
  have hTt : 0 ≤ T / t := hT0.le
  have hTnn : 0 ≤ T := by
    have := mul_nonneg hTt htpos.le
    rwa [div_mul_cancel₀ _ htpos.ne'] at this
  have hT2' : T ≤ 2 * t := by
    have := (div_le_iff₀ htpos).1 hT2.le
    linarith
  have huv : 0 < u n * v n := mul_pos hu hv
  have hMp : M ≤ p := hMm
  have hTMuv : T * M / (u n * v n) ≤ 2 := by
    rw [div_le_iff₀ huv, ← hpq]
    have h1 : T * M ≤ (2 * t) * p := mul_le_mul hT2' hMp hM0 (by positivity)
    have h2 : t * p ≤ q * p := mul_le_mul_of_nonneg_right htq hp0.le
    nlinarith
  have hTMnn : 0 ≤ T * M / (u n * v n) := by positivity
  -- decomposition
  have hdecomp : deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) (u n) (v n) -
      profDelta α β (ℓ n) (u n) (v n) =
      (t - T) * M / (u n * v n) - (1 - T * M / (u n * v n)) * (M / gammaOf (N n) (B n)) -
        T * D ^ 2 / (gammaOf (N n) (B n) * u n * v n) := by
    unfold deltaN profDelta
    field_simp
    ring
  rw [Real.norm_eq_abs, hdecomp]
  have ha : |(t - T) * M / (u n * v n)| ≤ |T / t - 1| := by
    have e1 : |(t - T) * M / (u n * v n)| = |t - T| * M / (u n * v n) := by
      rw [abs_div, abs_mul, abs_of_nonneg hM0, abs_of_pos huv]
    have e2 : |T / t - 1| = |t - T| / t := by
      rw [show T / t - 1 = (T - t) / t by field_simp, abs_div, abs_of_pos htpos, abs_sub_comm]
    rw [e1, e2]
    calc |t - T| * M / (u n * v n) ≤ |t - T| * p / (u n * v n) := by
          apply div_le_div_of_nonneg_right _ huv.le
          exact mul_le_mul_of_nonneg_left hMp (abs_nonneg _)
      _ = |t - T| / q := by rw [← hpq]; field_simp
      _ ≤ |t - T| / t := div_le_div_of_nonneg_left (abs_nonneg _) htpos htq
  have hqγ0 : 0 ≤ q / gammaOf (N n) (B n) := by positivity
  have hb : |(1 - T * M / (u n * v n)) * (M / gammaOf (N n) (B n))| ≤ q / gammaOf (N n) (B n) := by
    rw [abs_mul]
    have h1 : |1 - T * M / (u n * v n)| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have h2 : |M / gammaOf (N n) (B n)| ≤ q / gammaOf (N n) (B n) := by
      rw [abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_right (hMp.trans (min_le_max)) hγ.le
    calc |1 - T * M / (u n * v n)| * |M / gammaOf (N n) (B n)| ≤ 1 * (q / gammaOf (N n) (B n)) :=
          mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hc' : |T * D ^ 2 / (gammaOf (N n) (B n) * u n * v n)| ≤ 2 * (q / gammaOf (N n) (B n)) := by
    rw [abs_of_nonneg (by positivity)]
    have hD2 : D ^ 2 ≤ u n * v n := by
      refine hD.trans ?_
      have h1 : u n - M ≤ u n := by linarith
      have h2 : v n - M ≤ v n := by linarith
      have h3 : 0 ≤ u n - M := by have := min_le_left (u n) (v n); linarith
      have h4 : 0 ≤ v n - M := by have := min_le_right (u n) (v n); linarith
      exact mul_le_mul h1 h2 h4 hu.le
    rw [div_le_iff₀ (by positivity)]
    have h5 : T * D ^ 2 ≤ T * (u n * v n) := mul_le_mul_of_nonneg_left hD2 hTnn
    have h6 : T ≤ 2 * q := hT2'.trans (by linarith)
    have h7 : 2 * (q / gammaOf (N n) (B n)) * (gammaOf (N n) (B n) * u n * v n) =
        2 * q * (u n * v n) := by field_simp
    rw [h7]
    nlinarith [mul_le_mul_of_nonneg_right h6 huv.le]
  calc |(t - T) * M / (u n * v n) - (1 - T * M / (u n * v n)) * (M / gammaOf (N n) (B n)) -
        T * D ^ 2 / (gammaOf (N n) (B n) * u n * v n)|
      ≤ |(t - T) * M / (u n * v n)| + |(1 - T * M / (u n * v n)) * (M / gammaOf (N n) (B n))| +
        |T * D ^ 2 / (gammaOf (N n) (B n) * u n * v n)| := by
        exact (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ |T / t - 1| + q / gammaOf (N n) (B n) + 2 * (q / gammaOf (N n) (B n)) := by linarith
    _ ≤ _ := by linarith [hqγ0]

private lemma pg9_W_alg {x r m θI sg θN : ℝ} (hx : 0 < x) (hr : 0 < r) (hm : 0 < m) (hθ : 0 < θI) :
    Real.sqrt (r * x) / (1 + r * x) / (Real.sqrt x / (1 + x)) * sg * (θN / θI) =
      Real.sqrt (r * x) / (Real.sqrt m * (1 + r * x)) * sg * θN /
        (Real.sqrt x / (1 + x) / Real.sqrt m * θI) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hrx : 0 < r * x := mul_pos hr hx
  have hsr : 0 < Real.sqrt (r * x) := Real.sqrt_pos.2 hrx
  field_simp

set_option maxHeartbeats 1600000 in
private lemma pg9_ratio_W {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (i : ∀ n, Fin (N n)) (m : ℕ → ℝ)
    (hm0 : ∀ n, 0 < m n)
    (hBm : Tendsto (fun n => ((B n : ℕ) : ℝ) * m n) atTop atTop)
    (hmγ : Tendsto (fun n => m n / gammaOf (N n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => Wpart β (B n) (plSpec α (c n) (N n)) (i n) (m n) /
      (Real.sqrt (profZeta α (rowIdx (i n) / icCross α (B n)) (m n) *
        (1 - profZeta α (rowIdx (i n) / icCross α (B n)) (m n))) / Real.sqrt (m n) *
        profTheta α β (m n))) atTop (𝓝 1) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  have hγpos : ∀ n, 0 < gammaOf (N n) (B n) := fun n => by
    unfold gammaOf; exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
  have hρ : ∀ n, 0 < rowIdx (i n) := fun n => by unfold rowIdx; positivity
  have hX : ∀ n, 0 < rowIdx (i n) / icCross α (B n) := fun n => by
    unfold icCross
    have := R.hBpos n
    have : (0:ℝ) < (B n : ℝ) := by exact_mod_cast this
    have := hρ n
    positivity
  set x' : ℕ → ℝ := fun n => (m n / (rowIdx (i n) / icCross α (B n))) ^ α with hx'
  have hx'0 : ∀ n, 0 < x' n := fun n => Real.rpow_pos_of_pos (div_pos (hm0 n) (hX n)) α
  set x : ℕ → ℝ := fun n => plSpec α (c n) (N n) (i n) * partLam (B n) (plSpec α (c n) (N n)) (m n)
    with hx
  have hΛ : ∀ n, 0 < partLam (B n) (plSpec α (c n) (N n)) (m n) → True := fun _ _ => trivial
  -- r = x / x' tends to 1
  have hlam := lem_app_pl_finite_inverse_iv_i R hα1 m hBm hmγ
  have hBm1 : ∀ᶠ n in atTop, (1:ℝ) ≤ ((B n : ℕ) : ℝ) * m n := hBm.eventually_ge_atTop 1
  have hg0 : ∀ᶠ n in atTop, (((B n : ℕ) : ℝ) * m n / Kc α) ^ α ≠ 0 := by
    filter_upwards [hBm1] with n hn
    exact (Real.rpow_pos_of_pos (div_pos (by linarith) hK) α).ne'
  have hr := (isEquivalent_iff_tendsto_one hg0).1 hlam
  have hxeq : ∀ n, x n = (c n * partLam (B n) (plSpec α (c n) (N n)) (m n) /
      (((B n : ℕ) : ℝ) * m n / Kc α) ^ α) * x' n := by
    intro n
    have hB' : (0:ℝ) < ((B n : ℕ) : ℝ) := by exact_mod_cast R.hBpos n
    have hp : 0 < (((B n : ℕ) : ℝ) * m n / Kc α) := div_pos (mul_pos hB' (hm0 n)) hK
    have hp' : 0 < (((B n : ℕ) : ℝ) * m n / Kc α) ^ α := Real.rpow_pos_of_pos hp α
    have e1 : x' n = (((B n : ℕ) : ℝ) * m n / Kc α) ^ α * rowIdx (i n) ^ (-α) := by
      have : m n / (rowIdx (i n) / icCross α (B n)) = ((B n : ℕ) : ℝ) * m n / Kc α / rowIdx (i n) := by
        unfold icCross; field_simp
      simp only [hx']
      rw [this, Real.div_rpow hp.le (hρ n).le, Real.rpow_neg (hρ n).le]
      ring
    rw [e1]
    simp only [hx]
    unfold plSpec
    have : (((i n : ℕ) : ℝ) + 1) = rowIdx (i n) := rfl
    rw [this]
    field_simp
  have hrn : ∀ n, x n / x' n = c n * partLam (B n) (plSpec α (c n) (N n)) (m n) /
      (((B n : ℕ) : ℝ) * m n / Kc α) ^ α := by
    intro n
    rw [hxeq n]
    field_simp [(hx'0 n).ne']
  have hrlim : Tendsto (fun n => x n / x' n) atTop (𝓝 1) := by
    refine hr.congr (fun n => ?_)
    simp only [Pi.div_apply]
    exact (hrn n).symm
  have hmem : ∀ᶠ n in atTop, m n ∈ Ioo 0 (gammaOf (N n) (B n)) := by
    filter_upwards [hmγ.eventually (gt_mem_nhds (zero_lt_one' ℝ))] with n hn
    refine ⟨hm0 n, ?_⟩
    have : m n / gammaOf (N n) (B n) < 1 := hn
    rwa [div_lt_one (hγpos n)] at this
  have hxpos : ∀ᶠ n in atTop, 0 < x n := by
    filter_upwards [hmem] with n hn
    exact mul_pos (pg9_plSpec_pos (α := α) (R.hcpos n) (N n) (i n))
      (pg9_lam_pos (α := α) (R.hNpos n) (R.hBpos n) (R.hcpos n) hn)
  set r' : ℕ → ℝ := fun n => if 0 < x n / x' n then x n / x' n else 1 with hr'
  have hr'0 : ∀ n, 0 < r' n := by
    intro n; simp only [hr']; split_ifs with h
    · exact h
    · exact one_pos
  have hr'ev : ∀ᶠ n in atTop, r' n = x n / x' n := by
    filter_upwards [hxpos] with n hn
    simp only [hr']
    rw [if_pos (div_pos hn (hx'0 n))]
  have hr'lim : Tendsto r' atTop (𝓝 1) := hrlim.congr' (hr'ev.mono fun n h => h.symm)
  have hS := pg9_S_ratio hx'0 hr'lim hr'0
  have hsq : Tendsto (fun n => Real.sqrt (1 - m n / gammaOf (N n) (B n))) atTop (𝓝 1) := by
    have h2 := (Real.continuous_sqrt.tendsto (1 - 0)).comp ((tendsto_const_nhds (x := (1:ℝ))).sub hmγ)
    simpa [Function.comp_def] using h2
  have hθ := pg9_theta_ratio R hα1 m hm0 hBm hmγ
  have hprod := (hS.mul hsq).mul hθ
  simp only [one_mul, mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [hmem, hxpos, hr'ev] with n hn hxn hrn'
  have hθ0 : 0 < profTheta α β (m n) := by
    unfold profTheta
    obtain ⟨cE, hcE, hE⟩ := vs_E_lb R.hβ0 R.hβ1
    have hE0 : 0 < Efun β (m n) := lt_of_lt_of_le (mul_pos hcE (lt_min (hm0 n) one_pos)) (hE _ (hm0 n))
    have : 0 < (α - 1) / m n := div_pos (by linarith) (hm0 n)
    have : 0 < 1 / Efun β (m n) := by positivity
    linarith
  have hsig := pg9_sig_x hα0 (hX n) (hm0 n)
  have hsm := Real.sqrt_pos.2 (hm0 n)
  have hxx : r' n * x' n = x n := by
    rw [hrn']; field_simp [(hx'0 n).ne']
  rw [hsig]
  unfold Wpart
  have hxx' : plSpec α (c n) (N n) (i n) * partLam (B n) (plSpec α (c n) (N n)) (m n) =
      r' n * (m n / (rowIdx (i n) / icCross α (B n))) ^ α := hxx.symm
  simp only [hx']
  rw [hxx']
  exact pg9_W_alg (hx'0 n) (hr'0 n) (hm0 n) hθ0

private lemma pg9_F_eq_ratio {α β : ℝ} {N B : ℕ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hN : 0 < N) (hB : 0 < B) {c : ℝ} (hc : 0 < c) (i : Fin N) {X u v : ℝ} (hX : 0 < X)
    (hu : u ∈ Ioo 0 (gammaOf N B)) (hv : v ∈ Ioo 0 (gammaOf N B)) (ℓ : ℤ) :
    lagIntegrand β B (plSpec α c N) i ℓ u v =
      Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
          Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v) *
      (Wpart β B (plSpec α c N) i u / (Real.sqrt (profZeta α X u * (1 - profZeta α X u)) /
          Real.sqrt u * profTheta α β u)) *
      (Wpart β B (plSpec α c N) i v / (Real.sqrt (profZeta α X v * (1 - profZeta α X v)) /
          Real.sqrt v * profTheta α β v)) *
      (profDelta α β ℓ u v / deltaN β B (plSpec α c N) ℓ u v) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨hz1, hz1'⟩ := vs_zeta_bd hα0 hX hu.1
  obtain ⟨hz2, hz2'⟩ := vs_zeta_bd hα0 hX hv.1
  have hA1 : 0 < profZeta α X u * (1 - profZeta α X u) := mul_pos hz1 (by linarith)
  have hA2 : 0 < profZeta α X v * (1 - profZeta α X v) := mul_pos hz2 (by linarith)
  have hΔ := pg9_delta_pos hα0 hβ0 hβ1 hN hB hc ℓ hu hv
  have hΔ' : 0 < profDelta α β ℓ u v :=
    lt_of_lt_of_le (by positivity) (vs_Delta_ge hα1 hβ0 hβ1 hu.1 hv.1 ℓ)
  obtain ⟨hθu, -⟩ := (vs_theta_bd hα1 hβ0 hβ1).choose_spec.2 u hu.1
  obtain ⟨hθv, -⟩ := (vs_theta_bd hα1 hβ0 hβ1).choose_spec.2 v hv.1
  have hsu := Real.sqrt_pos.2 hu.1
  have hsv := Real.sqrt_pos.2 hv.1
  have hs1 := Real.sqrt_pos.2 hA1
  have hs2 := Real.sqrt_pos.2 hA2
  unfold lagIntegrand lagNumer
  rw [Real.sqrt_mul hA1.le, Real.sqrt_mul hu.1.le]
  field_simp

private lemma pg9_div_ratio {a d : ℕ → ℝ} {α : ℝ} (hα : 0 < α) (ha : ∀ n, 1 / α ≤ a n)
    (hd : Tendsto d atTop (𝓝 0)) : Tendsto (fun n => a n / (a n + d n)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n => d n / a n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hd.norm.const_mul α)
    have hapos : 0 < a n := lt_of_lt_of_le (by positivity) (ha n)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hapos, div_le_iff₀ hapos]
    have : 1 ≤ α * a n := by
      have := mul_le_mul_of_nonneg_left (ha n) hα.le
      rwa [mul_one_div_cancel hα.ne'] at this
    nlinarith [abs_nonneg (d n)]
  have h2 : Tendsto (fun n => (1 + d n / a n)⁻¹) atTop (𝓝 1) := by
    have := (h1.const_add 1).inv₀ (by norm_num)
    simpa using this
  refine h2.congr' ?_
  filter_upwards [] with n
  have hapos : 0 < a n := lt_of_lt_of_le (by positivity) (ha n)
  by_cases h : a n + d n = 0
  · have : d n = -a n := by linarith
    simp [this, hapos.ne']
  · field_simp

private lemma pg9_Rn_lim {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (i : ∀ n, Fin (N n)) (u v : ℕ → ℝ)
    (ℓ : ℕ → ℤ) (hu0 : ∀ n, 0 < u n) (hv0 : ∀ n, 0 < v n)
    (hBu : Tendsto (fun n => ((B n : ℕ) : ℝ) * u n) atTop atTop)
    (hBv : Tendsto (fun n => ((B n : ℕ) : ℝ) * v n) atTop atTop)
    (huγ : Tendsto (fun n => u n / gammaOf (N n) (B n)) atTop (𝓝 0))
    (hvγ : Tendsto (fun n => v n / gammaOf (N n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (Wpart β (B n) (plSpec α (c n) (N n)) (i n) (u n) /
        (Real.sqrt (profZeta α (rowIdx (i n) / icCross α (B n)) (u n) *
          (1 - profZeta α (rowIdx (i n) / icCross α (B n)) (u n))) / Real.sqrt (u n) *
          profTheta α β (u n))) *
      (Wpart β (B n) (plSpec α (c n) (N n)) (i n) (v n) /
        (Real.sqrt (profZeta α (rowIdx (i n) / icCross α (B n)) (v n) *
          (1 - profZeta α (rowIdx (i n) / icCross α (B n)) (v n))) / Real.sqrt (v n) *
          profTheta α β (v n))) *
      (profDelta α β (ℓ n) (u n) (v n) / deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) (u n) (v n)))
      atTop (𝓝 1) := by
  have hα0 : 0 < α := by linarith
  have h1 := pg9_ratio_W R hα1 i u hu0 hBu huγ
  have h2 := pg9_ratio_W R hα1 i v hv0 hBv hvγ
  have h3 := pg9_delta_close R hα1 u v ℓ hu0 hv0 hBu hBv huγ hvγ
  have h4 := pg9_div_ratio (a := fun n => profDelta α β (ℓ n) (u n) (v n))
    (d := fun n => deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) (u n) (v n) -
      profDelta α β (ℓ n) (u n) (v n)) hα0
    (fun n => vs_Delta_ge hα1 R.hβ0 R.hβ1 (hu0 n) (hv0 n) (ℓ n)) h3
  have h5 : ∀ n, profDelta α β (ℓ n) (u n) (v n) + (deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n)
      (u n) (v n) - profDelta α β (ℓ n) (u n) (v n)) =
      deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) (u n) (v n) := fun n => by ring
  simp only [h5] at h4
  simpa using (h1.mul h2).mul h4

set_option maxHeartbeats 1600000 in
private lemma pg9_unif_close {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hXγ : Tendsto (fun n => rowIdx (i n) / icCross α (B n) / gammaOf (N n) (B n)) atTop (𝓝 0))
    {δ Rr : ℝ} (hδ : 0 < δ) (hδR : δ ≤ Rr) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ u v : ℝ,
      δ * (rowIdx (i n) / icCross α (B n)) ≤ u → u ≤ Rr * (rowIdx (i n) / icCross α (B n)) →
      δ * (rowIdx (i n) / icCross α (B n)) ≤ v → v ≤ Rr * (rowIdx (i n) / icCross α (B n)) →
      ∀ ℓ : ℤ,
      |lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ u v -
        Real.sqrt (profZeta α (rowIdx (i n) / icCross α (B n)) u *
          (1 - profZeta α (rowIdx (i n) / icCross α (B n)) u) *
          (profZeta α (rowIdx (i n) / icCross α (B n)) v *
          (1 - profZeta α (rowIdx (i n) / icCross α (B n)) v))) / Real.sqrt (u * v) *
          (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v /
            profDelta α β ℓ u v)| ≤
      η * (Real.sqrt (profZeta α (rowIdx (i n) / icCross α (B n)) u *
          (1 - profZeta α (rowIdx (i n) / icCross α (B n)) u) *
          (profZeta α (rowIdx (i n) / icCross α (B n)) v *
          (1 - profZeta α (rowIdx (i n) / icCross α (B n)) v))) / Real.sqrt (u * v) *
          (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v /
            profDelta α β ℓ u v)) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  set X : ℕ → ℝ := fun n => rowIdx (i n) / icCross α (B n) with hXdef
  have hρ : ∀ n, 0 < rowIdx (i n) := fun n => by unfold rowIdx; positivity
  have hBr : ∀ n, (0:ℝ) < (B n : ℝ) := fun n => by exact_mod_cast R.hBpos n
  have hXpos : ∀ n, 0 < X n := fun n => by
    simp only [hXdef]; unfold icCross; have := hBr n; have := hρ n; positivity
  have hBX : ∀ n, ((B n : ℕ) : ℝ) * X n = Kc α * rowIdx (i n) := fun n => by
    simp only [hXdef]; unfold icCross; have := hBr n; field_simp
  have hBXlim : Tendsto (fun n => ((B n : ℕ) : ℝ) * X n) atTop atTop := by
    simp only [hBX]; exact hi.const_mul_atTop hK
  have hγpos : ∀ n, 0 < gammaOf (N n) (B n) := fun n => by
    unfold gammaOf; exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  classical
  have hex : ∀ n, ∃ (p : ℝ × ℝ) (ℓ : ℤ), δ * X n ≤ p.1 ∧ p.1 ≤ Rr * X n ∧ δ * X n ≤ p.2 ∧
      p.2 ≤ Rr * X n ∧ ((¬ ∀ u v : ℝ, δ * X n ≤ u → u ≤ Rr * X n → δ * X n ≤ v → v ≤ Rr * X n →
        ∀ ℓ : ℤ, |lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ u v -
        Real.sqrt (profZeta α (X n) u * (1 - profZeta α (X n) u) *
          (profZeta α (X n) v * (1 - profZeta α (X n) v))) / Real.sqrt (u * v) *
          (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v /
            profDelta α β ℓ u v)| ≤
        η * (Real.sqrt (profZeta α (X n) u * (1 - profZeta α (X n) u) *
          (profZeta α (X n) v * (1 - profZeta α (X n) v))) / Real.sqrt (u * v) *
          (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v /
            profDelta α β ℓ u v))) →
        η * (Real.sqrt (profZeta α (X n) p.1 * (1 - profZeta α (X n) p.1) *
          (profZeta α (X n) p.2 * (1 - profZeta α (X n) p.2))) / Real.sqrt (p.1 * p.2) *
          (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
            profDelta α β ℓ p.1 p.2)) <
        |lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2 -
        Real.sqrt (profZeta α (X n) p.1 * (1 - profZeta α (X n) p.1) *
          (profZeta α (X n) p.2 * (1 - profZeta α (X n) p.2))) / Real.sqrt (p.1 * p.2) *
          (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
            profDelta α β ℓ p.1 p.2)|) := by
    intro n
    by_cases hP : ∀ u v : ℝ, δ * X n ≤ u → u ≤ Rr * X n → δ * X n ≤ v → v ≤ Rr * X n →
        ∀ ℓ : ℤ, |lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ u v -
        Real.sqrt (profZeta α (X n) u * (1 - profZeta α (X n) u) *
          (profZeta α (X n) v * (1 - profZeta α (X n) v))) / Real.sqrt (u * v) *
          (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v /
            profDelta α β ℓ u v)| ≤
        η * (Real.sqrt (profZeta α (X n) u * (1 - profZeta α (X n) u) *
          (profZeta α (X n) v * (1 - profZeta α (X n) v))) / Real.sqrt (u * v) *
          (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v /
            profDelta α β ℓ u v))
    · refine ⟨(δ * X n, δ * X n), 0, le_rfl, ?_, le_rfl, ?_, fun h => absurd hP h⟩
      · have := hXpos n; nlinarith
      · have := hXpos n; nlinarith
    · push_neg at hP
      obtain ⟨u, v, h1, h2, h3, h4, ℓ, hbad⟩ := hP
      exact ⟨(u, v), ℓ, h1, h2, h3, h4, fun _ => hbad⟩
  choose p ℓ h1 h2 h3 h4 hbad using hex
  -- the sequences
  have hu0 : ∀ n, 0 < (p n).1 := fun n => lt_of_lt_of_le (mul_pos hδ (hXpos n)) (h1 n)
  have hv0 : ∀ n, 0 < (p n).2 := fun n => lt_of_lt_of_le (mul_pos hδ (hXpos n)) (h3 n)
  have hBu : Tendsto (fun n => ((B n : ℕ) : ℝ) * (p n).1) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) (hBXlim.const_mul_atTop hδ)
    have := hBr n
    have := mul_le_mul_of_nonneg_left (h1 n) this.le
    nlinarith
  have hBv : Tendsto (fun n => ((B n : ℕ) : ℝ) * (p n).2) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) (hBXlim.const_mul_atTop hδ)
    have := hBr n
    have := mul_le_mul_of_nonneg_left (h3 n) this.le
    nlinarith
  have hbound : ∀ q : ℕ → ℝ, (∀ n, 0 ≤ q n) → (∀ n, q n ≤ Rr * X n) →
      Tendsto (fun n => q n / gammaOf (N n) (B n)) atTop (𝓝 0) := by
    intro q hq0 hq
    have := hXγ.const_mul Rr
    simp only [mul_zero] at this
    refine squeeze_zero (fun n => div_nonneg (hq0 n) (hγpos n).le) (fun n => ?_) this
    have e : Rr * (X n / gammaOf (N n) (B n)) = Rr * X n / gammaOf (N n) (B n) := by ring
    simp only [hXdef] at e ⊢
    rw [e]
    exact div_le_div_of_nonneg_right (hq n) (hγpos n).le
  have huγ := hbound (fun n => (p n).1) (fun n => (hu0 n).le) h2
  have hvγ := hbound (fun n => (p n).2) (fun n => (hv0 n).le) h4
  have hRn := pg9_Rn_lim R hα1 i (fun n => (p n).1) (fun n => (p n).2) ℓ hu0 hv0 hBu hBv huγ hvγ
  have hev1 : ∀ᶠ n in atTop, |(Wpart β (B n) (plSpec α (c n) (N n)) (i n) (p n).1 /
        (Real.sqrt (profZeta α (X n) (p n).1 * (1 - profZeta α (X n) (p n).1)) /
          Real.sqrt (p n).1 * profTheta α β (p n).1)) *
      (Wpart β (B n) (plSpec α (c n) (N n)) (i n) (p n).2 /
        (Real.sqrt (profZeta α (X n) (p n).2 * (1 - profZeta α (X n) (p n).2)) /
          Real.sqrt (p n).2 * profTheta α β (p n).2)) *
      (profDelta α β (ℓ n) (p n).1 (p n).2 /
        deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) (p n).1 (p n).2) - 1| < η := by
    have := (hRn.sub_const 1).abs
    simp only [sub_self, abs_zero] at this
    exact this.eventually (gt_mem_nhds hη)
  have hgood : ∀ᶠ n in atTop, Rr * (X n / gammaOf (N n) (B n)) < 1 := by
    have := hXγ.const_mul Rr
    simp only [mul_zero] at this
    exact this.eventually (gt_mem_nhds (zero_lt_one' ℝ))
  obtain ⟨n, hn1, hn2, hn3⟩ := (hcon.and_eventually (hev1.and hgood)).exists
  have hbn := hbad n hn1
  -- positions are inside (0, γ)
  have hγn := hγpos n
  have hRX : Rr * X n < gammaOf (N n) (B n) := by
    have : Rr * (X n / gammaOf (N n) (B n)) < 1 := hn3
    rw [← mul_div_assoc, div_lt_one hγn] at this; exact this
  have hum : (p n).1 ∈ Ioo 0 (gammaOf (N n) (B n)) := ⟨hu0 n, lt_of_le_of_lt (h2 n) hRX⟩
  have hvm : (p n).2 ∈ Ioo 0 (gammaOf (N n) (B n)) := ⟨hv0 n, lt_of_le_of_lt (h4 n) hRX⟩
  rw [pg9_F_eq_ratio hα1 R.hβ0 R.hβ1 (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n) (hXpos n) hum hvm (ℓ n)]
    at hbn
  set Fc := Real.sqrt (profZeta α (X n) (p n).1 * (1 - profZeta α (X n) (p n).1) *
          (profZeta α (X n) (p n).2 * (1 - profZeta α (X n) (p n).2))) / Real.sqrt ((p n).1 * (p n).2) *
          (DLag β (Qm β (p n).1) (Qm β (p n).2) (ℓ n) * profTheta α β (p n).1 * profTheta α β (p n).2 /
            profDelta α β (ℓ n) (p n).1 (p n).2) with hFc
  have hFc0 : 0 ≤ Fc := by
    obtain ⟨hq1, -⟩ := vs_Qm R.hβ0 R.hβ1 (hu0 n)
    obtain ⟨hq2, -⟩ := vs_Qm R.hβ0 R.hβ1 (hv0 n)
    have hD := vs_DLag_nonneg R.hβ0 R.hβ1 hq1.le hq2.le (ℓ n)
    obtain ⟨hθu, -⟩ := (vs_theta_bd hα1 R.hβ0 R.hβ1).choose_spec.2 _ (hu0 n)
    obtain ⟨hθv, -⟩ := (vs_theta_bd hα1 R.hβ0 R.hβ1).choose_spec.2 _ (hv0 n)
    have hΔ := lt_of_lt_of_le (by positivity : 0 < 1 / α)
      (vs_Delta_ge hα1 R.hβ0 R.hβ1 (hu0 n) (hv0 n) (ℓ n))
    simp only [hFc]
    positivity
  have hrew : Fc * (Wpart β (B n) (plSpec α (c n) (N n)) (i n) (p n).1 /
        (Real.sqrt (profZeta α (X n) (p n).1 * (1 - profZeta α (X n) (p n).1)) /
          Real.sqrt (p n).1 * profTheta α β (p n).1)) *
      (Wpart β (B n) (plSpec α (c n) (N n)) (i n) (p n).2 /
        (Real.sqrt (profZeta α (X n) (p n).2 * (1 - profZeta α (X n) (p n).2)) /
          Real.sqrt (p n).2 * profTheta α β (p n).2)) *
      (profDelta α β (ℓ n) (p n).1 (p n).2 /
        deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) (p n).1 (p n).2) - Fc =
      Fc * ((Wpart β (B n) (plSpec α (c n) (N n)) (i n) (p n).1 /
        (Real.sqrt (profZeta α (X n) (p n).1 * (1 - profZeta α (X n) (p n).1)) /
          Real.sqrt (p n).1 * profTheta α β (p n).1)) *
      (Wpart β (B n) (plSpec α (c n) (N n)) (i n) (p n).2 /
        (Real.sqrt (profZeta α (X n) (p n).2 * (1 - profZeta α (X n) (p n).2)) /
          Real.sqrt (p n).2 * profTheta α β (p n).2)) *
      (profDelta α β (ℓ n) (p n).1 (p n).2 /
        deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) (p n).1 (p n).2) - 1) := by ring
  rw [hrew, abs_mul, abs_of_nonneg hFc0] at hbn
  have := mul_le_mul_of_nonneg_left hn2.le hFc0
  linarith

private lemma pg9_tsum_cmp {a b : ℤ → ℝ} {η : ℝ} (ha : Summable a) (hb : Summable b)
    (hη : 0 ≤ η) (hab : ∀ ℓ, |a ℓ - b ℓ| ≤ η * b ℓ) :
    |(∑' ℓ, a ℓ) - ∑' ℓ, b ℓ| ≤ η * ∑' ℓ, b ℓ := by
  have hs : Summable (fun ℓ => a ℓ - b ℓ) := ha.sub hb
  have hs2 : Summable (fun ℓ => η * b ℓ) := hb.mul_left η
  have hsn : Summable (fun ℓ => |a ℓ - b ℓ|) :=
    Summable.of_nonneg_of_le (fun ℓ => abs_nonneg _) hab hs2
  have hsn' : Summable (fun ℓ => ‖a ℓ - b ℓ‖) := by simpa [Real.norm_eq_abs] using hsn
  rw [← ha.tsum_sub hb, ← tsum_mul_left]
  calc |∑' ℓ, (a ℓ - b ℓ)| = ‖∑' ℓ, (a ℓ - b ℓ)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' ℓ, ‖a ℓ - b ℓ‖ := norm_tsum_le_tsum_norm hsn'
    _ ≤ ∑' ℓ, η * b ℓ := by
        refine hsn'.tsum_le_tsum (fun ℓ => ?_) hs2
        exact (Real.norm_eq_abs _).le.trans (hab ℓ)

private lemma pg9_cmp_Q {f g : ℤ → ℝ × ℝ → ℝ} {Q : Set (ℝ × ℝ)} (hQ : MeasurableSet Q) {η : ℝ}
    (hη : 0 ≤ η) (hf : ∀ ℓ, IntegrableOn (f ℓ) Q) (hg : ∀ ℓ, IntegrableOn (g ℓ) Q)
    (hfs : Summable (fun ℓ => ∫ p in Q, f ℓ p)) (hgs : Summable (fun ℓ => ∫ p in Q, g ℓ p))
    (hpt : ∀ p ∈ Q, ∀ ℓ, |f ℓ p - g ℓ p| ≤ η * g ℓ p) :
    (∀ ℓ, |(∫ p in Q, f ℓ p) - ∫ p in Q, g ℓ p| ≤ η * ∫ p in Q, g ℓ p) ∧
    |(∑' ℓ, ∫ p in Q, f ℓ p) - ∑' ℓ, ∫ p in Q, g ℓ p| ≤ η * ∑' ℓ, ∫ p in Q, g ℓ p := by
  have hab : ∀ ℓ, |(∫ p in Q, f ℓ p) - ∫ p in Q, g ℓ p| ≤ η * ∫ p in Q, g ℓ p := by
    intro ℓ
    rw [← integral_sub (hf ℓ) (hg ℓ), ← integral_const_mul]
    calc |∫ p in Q, (f ℓ p - g ℓ p)| = ‖∫ p in Q, (f ℓ p - g ℓ p)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ p in Q, ‖f ℓ p - g ℓ p‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ p in Q, η * g ℓ p := by
          refine setIntegral_mono_on (hf ℓ |>.sub (hg ℓ) |>.norm) ((hg ℓ).const_mul η) hQ ?_
          intro p hp
          exact (Real.norm_eq_abs _).le.trans (hpt p hp ℓ)
  exact ⟨hab, pg9_tsum_cmp hfs hgs hη hab⟩

open Muon.DetEquiv ProbabilityTheory in
set_option maxHeartbeats 1600000 in
private lemma pg9_cont_tail {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ H : ℝ × ℝ → ℝ, Integrable H ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ∧
      ∀ (k : ℕ) (X : ℝ), 0 < X → X ≤ 1 →
        0 ≤ (∑' ℓ : ℤ, ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
          Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
            Real.sqrt (u * v) *
            (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) -
          (∑' ℓ : ℤ, ∫ p in Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) ×ˢ
              Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)),
            Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2)) ∧
        (∑' ℓ : ℤ, ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
          Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
            Real.sqrt (u * v) *
            (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) -
          (∑' ℓ : ℤ, ∫ p in Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) ×ˢ
              Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)),
            Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2)) ≤
          ∫ p, (Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1))ᶜ.indicator H p
            ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ∧
        (∀ ℓ : ℤ, 0 ≤ (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
          Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
            Real.sqrt (u * v) *
            (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) -
          (∫ p in Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) ×ˢ
              Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)),
            Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2)) ∧
        (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
          Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
            Real.sqrt (u * v) *
            (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) -
          (∫ p in Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) ×ˢ
              Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)),
            Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2)) ≤
          ∫ p, (Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1))ᶜ.indicator H p
            ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) ∧
        Summable (fun ℓ : ℤ => ∫ p in Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) ×ˢ
              Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)),
            Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2)) := by
  obtain ⟨K, C, hK, hC, hbd⟩ := vz_tsum_bd (α := α) hα1 hβ0 hβ1
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  have hμ' : μ = volume.restrict (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := by
    rw [hμ, Measure.prod_restrict, ← Measure.volume_eq_prod]
  set H : ℝ × ℝ → ℝ := fun p => α * C *
    ((if p.1 ≤ 1 then K * p.1 ^ (α / 2 - 1) else K * p.1 ^ (-((α + 1) / 2))) *
      (if p.2 ≤ 1 then K * p.2 ^ (α / 2 - 1) else K * p.2 ^ (-((α + 1) / 2)))) with hH
  have hHint : Integrable H μ := (vz_bnd_int (K := K) hα1).const_mul (α * C)
  refine ⟨H, hHint, fun k X hX hX1 => ?_⟩
  obtain ⟨hint, hsum⟩ := vs_finite_all hα1 hβ0 hβ1 X hX
  obtain ⟨K', hK0, hK'⟩ := vs_theta_bd hα1 hβ0 hβ1
  obtain ⟨bl, hbl, hbls, hbdd⟩ := vs_core hα1 hβ0 hβ1 hX (le_refl X) hK'
  set Fl : ℤ → ℝ × ℝ → ℝ := fun ℓ p =>
    Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2) with hFl
  have hnn : ∀ ℓ, ∀ᵐ p ∂μ, 0 ≤ Fl ℓ p := fun ℓ => by
    filter_upwards [hbdd X le_rfl le_rfl ℓ] with p hp using hp.1
  have hgℓ : ∀ ℓ : ℤ, (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
        Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) =
      ∫ p, Fl ℓ p ∂μ := fun ℓ => vs_iter_eq ℓ (hint ℓ)
  set Qx : Set (ℝ × ℝ) := Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) ×ˢ
    Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) with hQx
  set Q1 : Set (ℝ × ℝ) := Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ
    Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) with hQ1
  have hQxm : MeasurableSet Qx := measurableSet_Icc.prod measurableSet_Icc
  have hQ1m : MeasurableSet Q1 := measurableSet_Icc.prod measurableSet_Icc
  have hQxsub : Qx ⊆ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) := by
    intro p hp
    have h0 : 0 < X / ((k : ℝ) + 1) := by positivity
    exact ⟨lt_of_lt_of_le h0 hp.1.1, lt_of_lt_of_le h0 hp.2.1⟩
  have hqℓ : ∀ ℓ : ℤ, ∫ p in Qx, Fl ℓ p = ∫ p in Qx, Fl ℓ p ∂μ := fun ℓ => by
    rw [hμ', Measure.restrict_restrict hQxm, inter_eq_left.2 hQxsub]
  -- tail family
  set g' : ℤ → ℝ × ℝ → ℝ := fun ℓ => Qxᶜ.indicator (Fl ℓ) with hg'
  have hg'int : ∀ ℓ, Integrable (g' ℓ) μ := fun ℓ => (hint ℓ).indicator hQxm.compl
  have hg'norm : Summable (fun ℓ : ℤ => ∫ p, ‖g' ℓ p‖ ∂μ) := by
    have h0 : Summable (fun ℓ : ℤ => ∫ p, ‖Fl ℓ p‖ ∂μ) := by
      refine hsum.congr fun ℓ => ?_
      rw [hgℓ ℓ]
      refine integral_congr_ae ?_
      filter_upwards [hnn ℓ] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg hp]
    refine Summable.of_nonneg_of_le (fun ℓ => integral_nonneg fun p => norm_nonneg _) (fun ℓ => ?_) h0
    refine integral_mono (hg'int ℓ).norm (hint ℓ).norm (fun p => ?_)
    simp only [hg']
    by_cases hp : p ∈ Qxᶜ
    · rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, norm_zero]; exact norm_nonneg _
  have hT : ∑' ℓ : ℤ, ∫ p, g' ℓ p ∂μ = ∫ p, ∑' ℓ : ℤ, g' ℓ p ∂μ :=
    integral_tsum_of_summable_integral_norm hg'int hg'norm
  have hsplitℓ : ∀ ℓ : ℤ, ∫ p, g' ℓ p ∂μ = (∫ p, Fl ℓ p ∂μ) - ∫ p in Qx, Fl ℓ p ∂μ := by
    intro ℓ
    have := integral_add_compl hQxm (hint ℓ)
    simp only [hg']
    rw [integral_indicator hQxm.compl]
    linarith
  have hg0 : Summable (fun ℓ : ℤ => ∫ p, Fl ℓ p ∂μ) := by
    refine hsum.congr fun ℓ => ?_
    exact (hgℓ ℓ)
  have hqsum : Summable (fun ℓ : ℤ => ∫ p in Qx, Fl ℓ p) := by
    refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_) hg0
    · rw [hqℓ ℓ]; exact integral_nonneg_of_ae (ae_restrict_of_ae (hnn ℓ))
    · rw [hqℓ ℓ]; exact setIntegral_le_integral (hint ℓ) (hnn ℓ)
  have hdiff : (∑' ℓ : ℤ, ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
        Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) -
      (∑' ℓ : ℤ, ∫ p in Qx, Fl ℓ p) = ∫ p, ∑' ℓ : ℤ, g' ℓ p ∂μ := by
    calc _ = (∑' ℓ : ℤ, ∫ p, Fl ℓ p ∂μ) - ∑' ℓ : ℤ, ∫ p in Qx, Fl ℓ p := by rw [tsum_congr hgℓ]
      _ = ∑' ℓ : ℤ, ((∫ p, Fl ℓ p ∂μ) - ∫ p in Qx, Fl ℓ p) := (hg0.tsum_sub hqsum).symm
      _ = ∑' ℓ : ℤ, ∫ p, g' ℓ p ∂μ := tsum_congr (fun ℓ => by rw [hsplitℓ ℓ, hqℓ ℓ])
      _ = _ := hT
  -- sign and bound of the tail integrand
  have hae : ∀ᵐ p ∂μ, 0 < p.1 ∧ 0 < p.2 := vs_ae_pos
  have htailnn : ∀ᵐ p ∂μ, 0 ≤ ∑' ℓ : ℤ, g' ℓ p := by
    have hall : ∀ᵐ p ∂μ, ∀ ℓ, 0 ≤ Fl ℓ p := by
      rw [ae_all_iff]; exact hnn
    filter_upwards [hall] with p hp
    refine tsum_nonneg fun ℓ => ?_
    simp only [hg']
    by_cases h : p ∈ Qxᶜ
    · rw [Set.indicator_of_mem h]; exact hp ℓ
    · rw [Set.indicator_of_notMem h]
  have hmain : ∫ p, ∑' ℓ : ℤ, g' ℓ p ∂μ ≤ ∫ p, Q1ᶜ.indicator H p ∂μ := by
    set G : ℝ × ℝ → ℝ := fun p => ∑' ℓ : ℤ, g' ℓ p with hG
    have hmemiff : ∀ p : ℝ × ℝ, X • p ∈ Qx ↔ p ∈ Q1 := by
      intro p
      simp only [hQx, hQ1, mem_prod, mem_Icc, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      have hk0 : (0:ℝ) < (k : ℝ) + 1 := by positivity
      have e1 : ∀ t : ℝ, (X / ((k : ℝ) + 1) ≤ X * t ↔ 1 / ((k : ℝ) + 1) ≤ t) := fun t => by
        rw [div_eq_mul_one_div]; exact mul_le_mul_iff_right₀ hX
      have e2 : ∀ t : ℝ, (X * t ≤ X * ((k : ℝ) + 1) ↔ t ≤ (k : ℝ) + 1) := fun t =>
        mul_le_mul_iff_right₀ hX
      simp only [e1, e2]
    have hGsc : ∀ p : ℝ × ℝ, G (X • p) = Q1ᶜ.indicator (fun p => ∑' ℓ : ℤ, Fl ℓ (X • p)) p := by
      intro p
      simp only [hG, hg']
      by_cases hp : p ∈ Q1
      · have hp' : X • p ∈ Qx := (hmemiff p).2 hp
        have : p ∉ Q1ᶜ := fun h => h hp
        rw [Set.indicator_of_notMem this]
        refine (tsum_congr fun ℓ => ?_).trans tsum_zero
        exact Set.indicator_of_notMem (fun h : X • p ∈ Qxᶜ => h hp') _
      · have hp' : X • p ∉ Qx := fun h => hp ((hmemiff p).1 h)
        have : p ∈ Q1ᶜ := hp
        rw [Set.indicator_of_mem this]
        exact tsum_congr fun ℓ => Set.indicator_of_mem hp' _
    have hresc := vz_rescale hX G
    have hX2 : 0 < X ^ 2 := by positivity
    have hGint : ∫ p, G p ∂μ = X ^ 2 * ∫ p, G (X • p) ∂μ := by
      rw [hresc]; field_simp; rfl
    have hbnd : ∀ᵐ p ∂μ, 0 ≤ X ^ 2 * G (X • p) ∧
        X ^ 2 * G (X • p) ≤ Q1ᶜ.indicator H p := by
      filter_upwards [hae] with p hp
      obtain ⟨hs, hle⟩ := hbd X p.1 p.2 hX hX1 hp.1 hp.2
      have hsc : ∑' ℓ : ℤ, X ^ 2 * Fl ℓ (X • p) = X ^ 2 * ∑' ℓ : ℤ, Fl ℓ (X • p) := tsum_mul_left
      have hnn' : 0 ≤ ∑' ℓ : ℤ, X ^ 2 * Fl ℓ (X • p) :=
        tsum_nonneg fun ℓ => (vz_term_bd hα1 hβ0 hβ1 hX hp.1 hp.2 ℓ).1
      have hle' : X ^ 2 * ∑' ℓ : ℤ, Fl ℓ (X • p) ≤ H p := by
        rw [← hsc]; exact hle
      rw [hGsc p]
      by_cases hq : p ∈ Q1ᶜ
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
        rw [hsc] at hnn'
        exact ⟨hnn', hle'⟩
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
        simp
    rw [hGint, ← integral_const_mul]
    refine integral_mono_of_nonneg (hbnd.mono fun p hp => hp.1) ?_ (hbnd.mono fun p hp => hp.2)
    exact hHint.indicator (hQ1m.compl)
  rw [hdiff]
  refine ⟨integral_nonneg_of_ae htailnn, hmain, fun ℓ => ?_, hqsum⟩
  have hs1 : Summable (fun ℓ : ℤ => ∫ p, g' ℓ p ∂μ) := by
    refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_) hg'norm
    · refine integral_nonneg_of_ae ?_
      filter_upwards [hnn ℓ] with p hp
      simp only [hg']
      by_cases h : p ∈ Qxᶜ
      · rw [Set.indicator_of_mem h]; exact hp
      · rw [Set.indicator_of_notMem h]; exact le_rfl
    · exact integral_mono (hg'int ℓ) (hg'int ℓ).norm (fun p => le_abs_self _ |>.trans (Real.norm_eq_abs _).ge)
  have hnnℓ : 0 ≤ ∫ p, g' ℓ p ∂μ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hnn ℓ] with p hp
    simp only [hg']
    by_cases h : p ∈ Qxᶜ
    · rw [Set.indicator_of_mem h]; exact hp
    · rw [Set.indicator_of_notMem h]; exact le_rfl
  have hfin : (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
        Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) -
      (∫ p in Qx, Fl ℓ p) = ∫ p, g' ℓ p ∂μ := by
    rw [hsplitℓ ℓ, hqℓ ℓ, hgℓ ℓ]
  rw [hfin]
  refine ⟨hnnℓ, ?_⟩
  have h2 : ∫ p, g' ℓ p ∂μ ≤ ∑' ℓ : ℤ, ∫ p, g' ℓ p ∂μ := hs1.le_tsum ℓ (fun j _ => ?_)
  · rw [hT] at h2; exact h2.trans hmain
  · refine integral_nonneg_of_ae ?_
    filter_upwards [hnn j] with p hp
    simp only [hg']
    by_cases h : p ∈ Qxᶜ
    · rw [Set.indicator_of_mem h]; exact hp
    · rw [Set.indicator_of_notMem h]; exact le_rfl

private lemma pg9_vPart_rep2 {α β c : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N) :
    vPart β B (plSpec α c N) i = 1 + (Real.pi ^ 2)⁻¹ *
      ((∑' ℓ : ℤ, lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ) -
        lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) 0) := by
  obtain ⟨-, -, hint, hsum, -⟩ := lem_app_pl_age_iv hα hβ0 hβ1 N B c hN hB hc i
  have hs1 : Summable (fun n : ℕ => lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B))
      (Ioo 0 (gammaOf N B)) ((n : ℤ) + 1)) :=
    hsum.comp_injective (i := fun n : ℕ => (n : ℤ) + 1) (fun a b h => by simpa using h)
  have hs2 : Summable (fun n : ℕ => lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B))
      (Ioo 0 (gammaOf N B)) (-((n : ℤ) + 1))) :=
    hsum.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1)) (fun a b h => by simpa using h)
  rw [tsum_of_add_one_of_neg_add_one hs1 hs2]
  have hneg : ∀ n : ℕ, lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B))
      (-((n : ℤ) + 1)) = lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B))
      (Ioo 0 (gammaOf N B)) ((n : ℤ) + 1) := fun n => pg9_lagTerm_neg i n (hint _)
  simp only [hneg]
  unfold vPart CbarPart
  rw [tsum_mul_left]
  have hp : Real.pi ^ 2 ≠ 0 := by positivity
  field_simp
  ring

open Muon.DetEquiv ProbabilityTheory in
set_option maxHeartbeats 1600000 in
private lemma pg9_cont_l0 {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun X : ℝ => (1 / Real.pi ^ 2) * ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
        Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) 0 * profTheta α β u * profTheta α β v / profDelta α β 0 u v))
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨K, C, hK, hC, hbd⟩ := vz_tsum_bd (α := α) hα1 hβ0 hβ1
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  have hae : ∀ᵐ p ∂μ, 0 < p.1 ∧ 0 < p.2 := vs_ae_pos
  have hDCT : Tendsto (fun X : ℝ => ∫ p : ℝ × ℝ, X ^ 2 *
      (Real.sqrt (profZeta α X (X * p.1) * (1 - profZeta α X (X * p.1)) *
              (profZeta α X (X * p.2) * (1 - profZeta α X (X * p.2)))) /
          Real.sqrt ((X * p.1) * (X * p.2)) *
        (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) (0:ℤ) * profTheta α β (X * p.1) *
          profTheta α β (X * p.2) / profDelta α β (0:ℤ) (X * p.1) (X * p.2))) ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ p : ℝ × ℝ,
        ((α * p.1 ^ (α / 2 - 1) / (1 + p.1 ^ α)) * (α * p.2 ^ (α / 2 - 1) / (1 + p.2 ^ α))) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (bound := fun p : ℝ × ℝ => α * C * ((if p.1 ≤ 1 then K * p.1 ^ (α / 2 - 1) else K * p.1 ^ (-((α + 1) / 2))) *
        (if p.2 ≤ 1 then K * p.2 ^ (α / 2 - 1) else K * p.2 ^ (-((α + 1) / 2))))) ?_ ?_ ?_ ?_
    · filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with X hX
      have h := (vs_F_meas (α := α) hβ0 hβ1 X 0).comp_quasiMeasurePreserving (vz_qmp hX.1)
      exact h.const_mul (X ^ 2)
    · filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with X hX
      filter_upwards [hae] with p hp
      obtain ⟨hs, hle⟩ := hbd X p.1 p.2 hX.1 hX.2 hp.1 hp.2
      have h0 := (vz_term_bd hα1 hβ0 hβ1 hX.1 hp.1 hp.2 0).1
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      refine le_trans ?_ hle
      exact hs.le_tsum 0 (fun j _ => (vz_term_bd hα1 hβ0 hβ1 hX.1 hp.1 hp.2 j).1)
    · exact (vz_bnd_int (K := K) hα1).const_mul (α * C)
    · filter_upwards [hae] with p hp
      have := vz_pt_lim (α := α) hα0 hβ0 hβ1 hp.1 hp.2 0
      simpa using this
  have hval : ∫ p : ℝ × ℝ,
      ((α * p.1 ^ (α / 2 - 1) / (1 + p.1 ^ α)) * (α * p.2 ^ (α / 2 - 1) / (1 + p.2 ^ α))) ∂μ =
      Real.pi ^ 2 := by
    have := integral_prod_mul (μ := volume.restrict (Ioi (0:ℝ))) (ν := volume.restrict (Ioi (0:ℝ)))
      (fun r : ℝ => α * r ^ (α / 2 - 1) / (1 + r ^ α)) (fun r : ℝ => α * r ^ (α / 2 - 1) / (1 + r ^ α))
    rw [hμ, this]
    have hk := vz_k_integral hα0
    rw [show (∫ x : ℝ, α * x ^ (α / 2 - 1) / (1 + x ^ α) ∂(volume.restrict (Ioi (0:ℝ)))) = Real.pi from hk]
    ring
  rw [hval] at hDCT
  have hfin := hDCT.const_mul (1 / Real.pi ^ 2)
  have hpi : (1 / Real.pi ^ 2) * Real.pi ^ 2 = 1 := by
    have := Real.pi_pos
    field_simp
  rw [hpi] at hfin
  refine hfin.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with X hX
  have hX0 : (0:ℝ) < X := hX
  obtain ⟨hint, hsum⟩ := vs_finite_all hα1 hβ0 hβ1 X hX0
  rw [vs_iter_eq 0 (hint 0)]
  have := vz_rescale hX0 (fun p : ℝ × ℝ =>
    Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) * (profZeta α X p.2 * (1 - profZeta α X p.2))) /
      Real.sqrt (p.1 * p.2) *
      (DLag β (Qm β p.1) (Qm β p.2) 0 * profTheta α β p.1 * profTheta α β p.2 / profDelta α β 0 p.1 p.2))
  congr 1
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at this
  rw [integral_const_mul, this]
  have hX2 : X ^ 2 ≠ 0 := by positivity
  field_simp

private lemma pg9_Tk_lim {H : ℝ × ℝ → ℝ}
    (hH : Integrable H ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) :
    Tendsto (fun k : ℕ => ∫ p, (Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ
        Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1))ᶜ.indicator H p
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) atTop (𝓝 0) := by
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  have hae : ∀ᵐ p ∂μ, 0 < p.1 ∧ 0 < p.2 := vs_ae_pos
  have hQm : ∀ k : ℕ, MeasurableSet (Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ
      Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1)) := fun k => measurableSet_Icc.prod measurableSet_Icc
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (F := fun (k : ℕ) (p : ℝ × ℝ) =>
    (Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1))ᶜ.indicator H p)
    (f := fun _ => 0) (bound := fun p => ‖H p‖)
    (fun k => (hH.1.indicator (hQm k).compl)) hH.norm
    (fun k => Eventually.of_forall fun p => by
      by_cases hp : p ∈ (Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ
        Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1))ᶜ
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp, norm_zero]; exact norm_nonneg _)
    (by
      filter_upwards [hae] with p hp
      obtain ⟨k1, hk1⟩ := exists_nat_gt (max (max (1 / p.1) p.1) (max (1 / p.2) p.2))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop k1] with k hk
      have hkk : (k1 : ℝ) ≤ k := by exact_mod_cast hk
      have hin : p ∈ Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) := by
        have h1 : 1 / p.1 < (k : ℝ) + 1 := by
          have := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hk1; linarith
        have h2 : p.1 < (k : ℝ) + 1 := by
          have := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hk1; linarith
        have h3 : 1 / p.2 < (k : ℝ) + 1 := by
          have := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hk1; linarith
        have h4 : p.2 < (k : ℝ) + 1 := by
          have := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hk1; linarith
        refine ⟨⟨?_, h2.le⟩, ⟨?_, h4.le⟩⟩
        · rw [div_le_iff₀ (by positivity)]
          rw [div_lt_iff₀ hp.1] at h1; nlinarith
        · rw [div_le_iff₀ (by positivity)]
          rw [div_lt_iff₀ hp.2] at h3; nlinarith
      have : p ∉ (Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ
        Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1))ᶜ := fun h => h hin
      exact (Set.indicator_of_notMem this _).symm)
  simpa using h

private lemma pg9_int_vol {f : ℝ × ℝ → ℝ} {Q : Set (ℝ × ℝ)} (hQ : MeasurableSet Q)
    (hsub : Q ⊆ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))
    (hf : Integrable f ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) :
    IntegrableOn f Q := by
  have h := hf.integrableOn (s := Q)
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  unfold IntegrableOn at h ⊢
  rwa [Measure.restrict_restrict hQ, inter_eq_left.2 hsub] at h

open Muon.DetEquiv ProbabilityTheory in
set_option maxHeartbeats 6400000 in
private lemma pg9_zero_main {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n)) atTop (𝓝 (1 / sPow β 2)) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  have hπ : 0 < Real.pi ^ 2 := by positivity
  have hs2 := vz_s2_pos R.hβ0 R.hβ1
  set X : ℕ → ℝ := fun n => rowIdx (i n) / icCross α (B n) with hXdef
  have hρ : ∀ n, 0 < rowIdx (i n) := fun n => by unfold rowIdx; positivity
  have hXpos : ∀ n, 0 < X n := fun n => by
    simp only [hXdef]; unfold icCross
    have : (0:ℝ) < (B n : ℝ) := by exact_mod_cast R.hBpos n
    have := hρ n; positivity
  have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  have hXγ : Tendsto (fun n => rowIdx (i n) / icCross α (B n) / gammaOf (N n) (B n)) atTop (𝓝 0) := by
    simpa using hX.div_atTop hg
  -- continuum limits
  have hXnhds : Tendsto X atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hX, Eventually.of_forall hXpos⟩
  have hGlim : Tendsto (fun n => profG α β (X n)) atTop (𝓝 (1 / sPow β 2)) :=
    (lem_app_pl_supervol_ii_zero hα1 R.hβ0 R.hβ1).comp hXnhds
  have hg0lim := (pg9_cont_l0 hα1 R.hβ0 R.hβ1).comp hXnhds
  obtain ⟨H, hHint, hcont⟩ := pg9_cont_tail hα1 R.hβ0 R.hβ1
  have hTk := pg9_Tk_lim hHint
  -- notation for the continuum quantities
  set Gm : ℕ → ℝ := fun n => ∑' ℓ : ℤ, ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
    Real.sqrt (profZeta α (X n) u * (1 - profZeta α (X n) u) *
      (profZeta α (X n) v * (1 - profZeta α (X n) v))) / Real.sqrt (u * v) *
    (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v) with hGm
  set g0 : ℕ → ℝ := fun n => ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
    Real.sqrt (profZeta α (X n) u * (1 - profZeta α (X n) u) *
      (profZeta α (X n) v * (1 - profZeta α (X n) v))) / Real.sqrt (u * v) *
    (DLag β (Qm β u) (Qm β v) 0 * profTheta α β u * profTheta α β v / profDelta α β 0 u v) with hg0
  have hGprofG : ∀ n, profG α β (X n) = (1 / Real.pi ^ 2) * Gm n := fun n => by
    simp only [hGm]; unfold profG; rfl
  have hGlim' : Tendsto (fun n => (1 / Real.pi ^ 2) * Gm n) atTop (𝓝 (1 / sPow β 2)) := by
    simpa [hGprofG] using hGlim
  have hg0lim' : Tendsto (fun n => (1 / Real.pi ^ 2) * g0 n) atTop (𝓝 1) := hg0lim
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η3 : ℝ := Real.pi ^ 2 * ε / 16 with hη3
  have hη3pos : 0 < η3 := by positivity
  set Mb : ℝ := Real.pi ^ 2 * (1 / sPow β 2 + 1) + 2 * Real.pi ^ 2 with hMb
  have hMb0 : 0 < Mb := by positivity
  set η : ℝ := η3 / (Mb + 1) with hη
  have hηpos : 0 < η := by positivity
  have hηMb : η * Mb ≤ η3 := by
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  -- bounds on the continuum quantities
  have hGbd : ∀ᶠ n in atTop, Gm n ≤ Mb := by
    filter_upwards [hGlim'.eventually (gt_mem_nhds (by linarith : 1 / sPow β 2 < 1 / sPow β 2 + 1))]
      with n hn
    have : Gm n ≤ Real.pi ^ 2 * (1 / sPow β 2 + 1) := by
      have h1 : (1 / Real.pi ^ 2) * Gm n < 1 / sPow β 2 + 1 := hn
      rw [one_div, inv_mul_lt_iff₀ hπ] at h1
      linarith
    have : 0 ≤ 2 * Real.pi ^ 2 := by positivity
    linarith
  have hg0bd : ∀ᶠ n in atTop, g0 n ≤ Mb := by
    filter_upwards [hg0lim'.eventually (gt_mem_nhds (by norm_num : (1:ℝ) < 2))] with n hn
    have h1 : (1 / Real.pi ^ 2) * g0 n < 2 := hn
    rw [one_div, inv_mul_lt_iff₀ hπ] at h1
    have : 0 ≤ Real.pi ^ 2 * (1 / sPow β 2 + 1) := by positivity
    linarith
  -- choice of k
  obtain ⟨k1, hk1⟩ := eventually_atTop.1 (hTk.eventually (gt_mem_nhds hη3pos))
  obtain ⟨k0, hk0⟩ := pg9_tail_seq0 R hα1 i hi hX η3 hη3pos
  set k : ℕ := max k0 k1 with hk
  have hkk0 : k ≥ k0 := le_max_left _ _
  have hkk1 : k ≥ k1 := le_max_right _ _
  have hTkk := hk1 k hkk1
  have hδ : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hδR : 1 / ((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
    have h1 : (1:ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    calc 1 / ((k : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; exact h1
      _ ≤ _ := h1
  have hunif := pg9_unif_close R hα1 i hi hXγ hδ hδR hηpos
  have hXsmall : ∀ᶠ n in atTop, X n * ((k : ℝ) + 1) < 1 ∧ X n ≤ 1 := by
    have h1 := (hX.mul_const ((k : ℝ) + 1))
    simp only [zero_mul] at h1
    filter_upwards [h1.eventually (gt_mem_nhds (zero_lt_one' ℝ)),
      hX.eventually (ge_mem_nhds (zero_lt_one' ℝ))] with n a b
    exact ⟨a, b⟩
  have h1' := (hg0lim'.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 4)))
  have h2' := (hGlim'.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 4)))
  filter_upwards [hk0 k hkk0, hunif, hXsmall, hGbd, hg0bd, h1', h2', hg.eventually_gt_atTop 1]
    with n htail hu hxs hG hg0b hlim1 hlim2 hγ1
  have hN := R.hNpos n
  have hB := R.hBpos n
  have hc := R.hcpos n
  have hXn := hXpos n
  have hγn : 1 < gammaOf (N n) (B n) := hγ1
  set Q : Set (ℝ × ℝ) := Icc (X n / ((k : ℝ) + 1)) (X n * ((k : ℝ) + 1)) ×ˢ
    Icc (X n / ((k : ℝ) + 1)) (X n * ((k : ℝ) + 1)) with hQ
  have hQm : MeasurableSet Q := measurableSet_Icc.prod measurableSet_Icc
  have hk0pos : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hXk0 : 0 < X n / ((k : ℝ) + 1) := by positivity
  have hQsub0 : Q ⊆ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) := fun p hp =>
    ⟨lt_of_lt_of_le hXk0 hp.1.1, lt_of_lt_of_le hXk0 hp.2.1⟩
  have hQU : Q ⊆ Ioo 0 (gammaOf (N n) (B n)) ×ˢ Ioo 0 (gammaOf (N n) (B n)) := fun p hp =>
    ⟨⟨lt_of_lt_of_le hXk0 hp.1.1, lt_of_le_of_lt hp.1.2 (lt_trans hxs.1 hγn)⟩,
      ⟨lt_of_lt_of_le hXk0 hp.2.1, lt_of_le_of_lt hp.2.2 (lt_trans hxs.1 hγn)⟩⟩
  obtain ⟨hs0, hs1, hsℓ, hsq⟩ := pg9_split hα0 R.hβ0 R.hβ1 hN hB hc (i n) hQm hQU htail
  obtain ⟨hc0, hc1, hcℓ, hcsum⟩ := hcont k (X n) hXn hxs.2
  obtain ⟨hint, -⟩ := vs_finite_all hα1 R.hβ0 R.hβ1 (X n) hXn
  have hUint := (lem_app_pl_age_iv hα0 R.hβ0 R.hβ1 (N n) (B n) (c n) hN hB hc (i n)).2.2.1
  have hcmp := pg9_cmp_Q (Q := Q)
    (f := fun ℓ p => lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2)
    (g := fun ℓ p => Real.sqrt (profZeta α (X n) p.1 * (1 - profZeta α (X n) p.1) *
              (profZeta α (X n) p.2 * (1 - profZeta α (X n) p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2)) hQm hηpos.le
    (fun ℓ => (hUint ℓ).mono_set hQU) (fun ℓ => pg9_int_vol hQm hQsub0 (hint ℓ)) hsq hcsum
    (by
      intro p hp ℓ
      have e1 : (1 / ((k : ℝ) + 1)) * X n = X n / ((k : ℝ) + 1) := by ring
      have e2 : ((k : ℝ) + 1) * X n = X n * ((k : ℝ) + 1) := by ring
      exact hu p.1 p.2 (by rw [e1]; exact hp.1.1) (by rw [e2]; exact hp.1.2)
        (by rw [e1]; exact hp.2.1) (by rw [e2]; exact hp.2.2) ℓ)
  obtain ⟨hcmpℓ, hcmps⟩ := hcmp
  have hrep := pg9_vPart_rep2 hα0 R.hβ0 R.hβ1 hN hB hc (i n)
  have hℓ0 := hsℓ 0
  have hcℓ0 := hcℓ 0
  have hcmpℓ0 := hcmpℓ 0
  set Pn : ℝ := ∑' ℓ : ℤ, lagTerm β (B n) (plSpec α (c n) (N n)) (i n)
    (Ioo 0 (gammaOf (N n) (B n))) (Ioo 0 (gammaOf (N n) (B n))) ℓ with hPn
  set Pn0 : ℝ := lagTerm β (B n) (plSpec α (c n) (N n)) (i n)
    (Ioo 0 (gammaOf (N n) (B n))) (Ioo 0 (gammaOf (N n) (B n))) 0 with hPn0
  set Sn : ℝ := ∑' ℓ : ℤ, ∫ p in Q, lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2
    with hSn
  set Sn0 : ℝ := ∫ p in Q, lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) 0 p.1 p.2 with hSn0
  set Sc : ℝ := ∑' ℓ : ℤ, ∫ p in Q, Real.sqrt (profZeta α (X n) p.1 * (1 - profZeta α (X n) p.1) *
              (profZeta α (X n) p.2 * (1 - profZeta α (X n) p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2) with hSc
  set Sc0 : ℝ := ∫ p in Q, Real.sqrt (profZeta α (X n) p.1 * (1 - profZeta α (X n) p.1) *
              (profZeta α (X n) p.2 * (1 - profZeta α (X n) p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) 0 * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β 0 p.1 p.2) with hSc0
  have hTk3 : ∫ p, (Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ
        Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1))ᶜ.indicator H p
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) < η3 := hTkk
  have hSc_nn : 0 ≤ Sc := by
    have := abs_nonneg (Sn - Sc)
    have h2 : 0 ≤ η * Sc := this.trans hcmps
    exact (mul_nonneg_iff_of_pos_left hηpos).1 h2
  have hSc0_nn : 0 ≤ Sc0 := by
    have := abs_nonneg (Sn0 - Sc0)
    have h2 : 0 ≤ η * Sc0 := this.trans hcmpℓ0
    exact (mul_nonneg_iff_of_pos_left hηpos).1 h2
  have hηSc : η * Sc ≤ η3 := by
    have : η * Sc ≤ η * Mb := mul_le_mul_of_nonneg_left (by linarith [hc0]) hηpos.le
    linarith
  have hηSc0 : η * Sc0 ≤ η3 := by
    have : η * Sc0 ≤ η * Mb := mul_le_mul_of_nonneg_left (by linarith [hcℓ0.1]) hηpos.le
    linarith
  have hB1 : |Pn - Gm n| ≤ 2 * η3 := by
    have h1 := abs_le.1 (hcmps.trans hηSc)
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, hs0, hs1, hc0, hc1]
  have hB2 : |Pn0 - g0 n| ≤ 2 * η3 := by
    have h1 := abs_le.1 (hcmpℓ0.trans hηSc0)
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, hℓ0.1, hℓ0.2, hcℓ0.1, hcℓ0.2]
  have e : vPart β (B n) (plSpec α (c n) (N n)) (i n) - 1 / sPow β 2 =
      (1 - (1 / Real.pi ^ 2) * g0 n) + (1 / Real.pi ^ 2) * (g0 n - Pn0) +
        (1 / Real.pi ^ 2) * (Pn - Gm n) + ((1 / Real.pi ^ 2) * Gm n - 1 / sPow β 2) := by
    rw [hrep]; simp only [hPn, hPn0]; ring
  rw [Real.dist_eq, e]
  have h1 : |1 - (1 / Real.pi ^ 2) * g0 n| < ε / 4 := by
    have := Metric.mem_ball.1 hlim1
    rw [Real.dist_eq] at this
    rwa [abs_sub_comm]
  have h4 : |(1 / Real.pi ^ 2) * Gm n - 1 / sPow β 2| < ε / 4 := by
    have := Metric.mem_ball.1 hlim2
    rwa [Real.dist_eq] at this
  have hpe : (1 / Real.pi ^ 2) * (2 * η3) = ε / 8 := by rw [hη3]; field_simp; norm_num
  have hp1 : 0 < 1 / Real.pi ^ 2 := by positivity
  have h2 : |(1 / Real.pi ^ 2) * (g0 n - Pn0)| ≤ ε / 8 := by
    rw [abs_mul, abs_of_pos hp1, abs_sub_comm, ← hpe]
    exact mul_le_mul_of_nonneg_left hB2 hp1.le
  have h3 : |(1 / Real.pi ^ 2) * (Pn - Gm n)| ≤ ε / 8 := by
    rw [abs_mul, abs_of_pos hp1, ← hpe]
    exact mul_le_mul_of_nonneg_left hB1 hp1.le
  calc |(1 - (1 / Real.pi ^ 2) * g0 n) + (1 / Real.pi ^ 2) * (g0 n - Pn0) +
        (1 / Real.pi ^ 2) * (Pn - Gm n) + ((1 / Real.pi ^ 2) * Gm n - 1 / sPow β 2)|
      ≤ |1 - (1 / Real.pi ^ 2) * g0 n| + |(1 / Real.pi ^ 2) * (g0 n - Pn0)| +
        |(1 / Real.pi ^ 2) * (Pn - Gm n)| + |(1 / Real.pi ^ 2) * Gm n - 1 / sPow β 2| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)) le_rfl)
    _ < ε := by linarith

open Muon.DetEquiv ProbabilityTheory in
set_option maxHeartbeats 1600000 in
private lemma pg9_cont_tail_inf {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ H : ℝ × ℝ → ℝ, Integrable H ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ∧
      ∀ (k : ℕ) (X : ℝ), 1 ≤ X →
        0 ≤ (∑' ℓ : ℤ, ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
          Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
            Real.sqrt (u * v) *
            (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) -
          (∑' ℓ : ℤ, ∫ p in Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) ×ˢ
              Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)),
            Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2)) ∧
        (∑' ℓ : ℤ, ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
          Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
            Real.sqrt (u * v) *
            (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) -
          (∑' ℓ : ℤ, ∫ p in Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) ×ˢ
              Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)),
            Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2)) ≤
          X * ∫ p, (Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1))ᶜ.indicator H p
            ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ∧
        (∀ ℓ : ℤ, 0 ≤ (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
          Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
            Real.sqrt (u * v) *
            (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) -
          (∫ p in Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) ×ˢ
              Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)),
            Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2)) ∧
        (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
          Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
            Real.sqrt (u * v) *
            (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) -
          (∫ p in Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) ×ˢ
              Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)),
            Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2)) ≤
          X * ∫ p, (Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1))ᶜ.indicator H p
            ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) ∧
        Summable (fun ℓ : ℤ => ∫ p in Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) ×ˢ
              Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)),
            Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2)) := by
  obtain ⟨K, C, hK, hC, hbd⟩ := vi_tsum_bd (α := α) hα1 hβ0 hβ1
  set μ := (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) with hμ
  have hμ' : μ = volume.restrict (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := by
    rw [hμ, Measure.prod_restrict, ← Measure.volume_eq_prod]
  set H : ℝ × ℝ → ℝ := fun p => α * C *
    ((if p.1 ≤ 1 then K * p.1 ^ (α / 2 - 1) else K * p.1 ^ (-((α + 1) / 2))) *
      (if p.2 ≤ 1 then K * p.2 ^ (α / 2 - 1) else K * p.2 ^ (-((α + 1) / 2)))) with hH
  have hHint : Integrable H μ := (vz_bnd_int (K := K) hα1).const_mul (α * C)
  refine ⟨H, hHint, fun k X hX1 => ?_⟩
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  obtain ⟨hint, hsum⟩ := vs_finite_all hα1 hβ0 hβ1 X hX
  obtain ⟨K', hK0, hK'⟩ := vs_theta_bd hα1 hβ0 hβ1
  obtain ⟨bl, hbl, hbls, hbdd⟩ := vs_core hα1 hβ0 hβ1 hX (le_refl X) hK'
  set Fl : ℤ → ℝ × ℝ → ℝ := fun ℓ p =>
    Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2) with hFl
  have hnn : ∀ ℓ, ∀ᵐ p ∂μ, 0 ≤ Fl ℓ p := fun ℓ => by
    filter_upwards [hbdd X le_rfl le_rfl ℓ] with p hp using hp.1
  have hgℓ : ∀ ℓ : ℤ, (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
        Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) =
      ∫ p, Fl ℓ p ∂μ := fun ℓ => vs_iter_eq ℓ (hint ℓ)
  set Qx : Set (ℝ × ℝ) := Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) ×ˢ
    Icc (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) with hQx
  set Q1 : Set (ℝ × ℝ) := Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ
    Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) with hQ1
  have hQxm : MeasurableSet Qx := measurableSet_Icc.prod measurableSet_Icc
  have hQ1m : MeasurableSet Q1 := measurableSet_Icc.prod measurableSet_Icc
  have hQxsub : Qx ⊆ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) := by
    intro p hp
    have h0 : 0 < X / ((k : ℝ) + 1) := by positivity
    exact ⟨lt_of_lt_of_le h0 hp.1.1, lt_of_lt_of_le h0 hp.2.1⟩
  have hqℓ : ∀ ℓ : ℤ, ∫ p in Qx, Fl ℓ p = ∫ p in Qx, Fl ℓ p ∂μ := fun ℓ => by
    rw [hμ', Measure.restrict_restrict hQxm, inter_eq_left.2 hQxsub]
  -- tail family
  set g' : ℤ → ℝ × ℝ → ℝ := fun ℓ => Qxᶜ.indicator (Fl ℓ) with hg'
  have hg'int : ∀ ℓ, Integrable (g' ℓ) μ := fun ℓ => (hint ℓ).indicator hQxm.compl
  have hg'norm : Summable (fun ℓ : ℤ => ∫ p, ‖g' ℓ p‖ ∂μ) := by
    have h0 : Summable (fun ℓ : ℤ => ∫ p, ‖Fl ℓ p‖ ∂μ) := by
      refine hsum.congr fun ℓ => ?_
      rw [hgℓ ℓ]
      refine integral_congr_ae ?_
      filter_upwards [hnn ℓ] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg hp]
    refine Summable.of_nonneg_of_le (fun ℓ => integral_nonneg fun p => norm_nonneg _) (fun ℓ => ?_) h0
    refine integral_mono (hg'int ℓ).norm (hint ℓ).norm (fun p => ?_)
    simp only [hg']
    by_cases hp : p ∈ Qxᶜ
    · rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, norm_zero]; exact norm_nonneg _
  have hT : ∑' ℓ : ℤ, ∫ p, g' ℓ p ∂μ = ∫ p, ∑' ℓ : ℤ, g' ℓ p ∂μ :=
    integral_tsum_of_summable_integral_norm hg'int hg'norm
  have hsplitℓ : ∀ ℓ : ℤ, ∫ p, g' ℓ p ∂μ = (∫ p, Fl ℓ p ∂μ) - ∫ p in Qx, Fl ℓ p ∂μ := by
    intro ℓ
    have := integral_add_compl hQxm (hint ℓ)
    simp only [hg']
    rw [integral_indicator hQxm.compl]
    linarith
  have hg0 : Summable (fun ℓ : ℤ => ∫ p, Fl ℓ p ∂μ) := by
    refine hsum.congr fun ℓ => ?_
    exact (hgℓ ℓ)
  have hqsum : Summable (fun ℓ : ℤ => ∫ p in Qx, Fl ℓ p) := by
    refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_) hg0
    · rw [hqℓ ℓ]; exact integral_nonneg_of_ae (ae_restrict_of_ae (hnn ℓ))
    · rw [hqℓ ℓ]; exact setIntegral_le_integral (hint ℓ) (hnn ℓ)
  have hdiff : (∑' ℓ : ℤ, ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
        Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) -
      (∑' ℓ : ℤ, ∫ p in Qx, Fl ℓ p) = ∫ p, ∑' ℓ : ℤ, g' ℓ p ∂μ := by
    calc _ = (∑' ℓ : ℤ, ∫ p, Fl ℓ p ∂μ) - ∑' ℓ : ℤ, ∫ p in Qx, Fl ℓ p := by rw [tsum_congr hgℓ]
      _ = ∑' ℓ : ℤ, ((∫ p, Fl ℓ p ∂μ) - ∫ p in Qx, Fl ℓ p) := (hg0.tsum_sub hqsum).symm
      _ = ∑' ℓ : ℤ, ∫ p, g' ℓ p ∂μ := tsum_congr (fun ℓ => by rw [hsplitℓ ℓ, hqℓ ℓ])
      _ = _ := hT
  -- sign and bound of the tail integrand
  have hae : ∀ᵐ p ∂μ, 0 < p.1 ∧ 0 < p.2 := vs_ae_pos
  have htailnn : ∀ᵐ p ∂μ, 0 ≤ ∑' ℓ : ℤ, g' ℓ p := by
    have hall : ∀ᵐ p ∂μ, ∀ ℓ, 0 ≤ Fl ℓ p := by
      rw [ae_all_iff]; exact hnn
    filter_upwards [hall] with p hp
    refine tsum_nonneg fun ℓ => ?_
    simp only [hg']
    by_cases h : p ∈ Qxᶜ
    · rw [Set.indicator_of_mem h]; exact hp ℓ
    · rw [Set.indicator_of_notMem h]
  have hmain : ∫ p, ∑' ℓ : ℤ, g' ℓ p ∂μ ≤ X * ∫ p, Q1ᶜ.indicator H p ∂μ := by
    set G : ℝ × ℝ → ℝ := fun p => ∑' ℓ : ℤ, g' ℓ p with hG
    have hmemiff : ∀ p : ℝ × ℝ, X • p ∈ Qx ↔ p ∈ Q1 := by
      intro p
      simp only [hQx, hQ1, mem_prod, mem_Icc, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      have hk0 : (0:ℝ) < (k : ℝ) + 1 := by positivity
      have e1 : ∀ t : ℝ, (X / ((k : ℝ) + 1) ≤ X * t ↔ 1 / ((k : ℝ) + 1) ≤ t) := fun t => by
        rw [div_eq_mul_one_div]; exact mul_le_mul_iff_right₀ hX
      have e2 : ∀ t : ℝ, (X * t ≤ X * ((k : ℝ) + 1) ↔ t ≤ (k : ℝ) + 1) := fun t =>
        mul_le_mul_iff_right₀ hX
      simp only [e1, e2]
    have hGsc : ∀ p : ℝ × ℝ, G (X • p) = Q1ᶜ.indicator (fun p => ∑' ℓ : ℤ, Fl ℓ (X • p)) p := by
      intro p
      simp only [hG, hg']
      by_cases hp : p ∈ Q1
      · have hp' : X • p ∈ Qx := (hmemiff p).2 hp
        have : p ∉ Q1ᶜ := fun h => h hp
        rw [Set.indicator_of_notMem this]
        refine (tsum_congr fun ℓ => ?_).trans tsum_zero
        exact Set.indicator_of_notMem (fun h : X • p ∈ Qxᶜ => h hp') _
      · have hp' : X • p ∉ Qx := fun h => hp ((hmemiff p).1 h)
        have : p ∈ Q1ᶜ := hp
        rw [Set.indicator_of_mem this]
        exact tsum_congr fun ℓ => Set.indicator_of_mem hp' _
    have hresc := vz_rescale hX G
    have hX2 : 0 < X ^ 2 := by positivity
    have hGint : ∫ p, G p ∂μ = X ^ 2 * ∫ p, G (X • p) ∂μ := by
      rw [hresc]; field_simp; rfl
    have hbnd : ∀ᵐ p ∂μ, 0 ≤ X * G (X • p) ∧
        X * G (X • p) ≤ Q1ᶜ.indicator H p := by
      filter_upwards [hae] with p hp
      obtain ⟨hs, hle⟩ := hbd X p.1 p.2 hX1 hp.1 hp.2
      have hα0 : 0 < α := by linarith
      have heq : ∀ ℓ : ℤ, ((p.1 ^ (α / 2) / (1 + p.1 ^ α)) * (p.2 ^ (α / 2) / (1 + p.2 ^ α)) /
          Real.sqrt (p.1 * p.2)) *
          (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ * profTheta α β (X * p.1) *
            profTheta α β (X * p.2) / profDelta α β ℓ (X * p.1) (X * p.2)) = X * Fl ℓ (X • p) := by
        intro ℓ
        have h2 := vz_scaled_eq (β := β) hα0 hX hp.1 hp.2 ℓ
        have hΔ := vs_Delta_ge hα1 hβ0 hβ1 (mul_pos hX hp.1) (mul_pos hX hp.2) ℓ
        have hΔ0 : profDelta α β ℓ (X * p.1) (X * p.2) ≠ 0 :=
          (lt_of_lt_of_le (by positivity) hΔ).ne'
        have hsr : Real.sqrt (p.1 * p.2) ≠ 0 := (Real.sqrt_pos.2 (mul_pos hp.1 hp.2)).ne'
        have hra := Real.rpow_pos_of_pos hp.1 α
        have hsa := Real.rpow_pos_of_pos hp.2 α
        have hd1 : 1 + p.1 ^ α ≠ 0 := by positivity
        have hd2 : 1 + p.2 ^ α ≠ 0 := by positivity
        have hp1 : p.1 ≠ 0 := hp.1.ne'
        have hp2 : p.2 ≠ 0 := hp.2.ne'
        simp only [hFl, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have e : X * (Real.sqrt (profZeta α X (X * p.1) * (1 - profZeta α X (X * p.1)) *
              (profZeta α X (X * p.2) * (1 - profZeta α X (X * p.2)))) / Real.sqrt ((X * p.1) * (X * p.2)) *
            (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ * profTheta α β (X * p.1) *
              profTheta α β (X * p.2) / profDelta α β ℓ (X * p.1) (X * p.2))) =
            X⁻¹ * (X ^ 2 * (Real.sqrt (profZeta α X (X * p.1) * (1 - profZeta α X (X * p.1)) *
              (profZeta α X (X * p.2) * (1 - profZeta α X (X * p.2)))) / Real.sqrt ((X * p.1) * (X * p.2)) *
            (DLag β (Qm β (X * p.1)) (Qm β (X * p.2)) ℓ * profTheta α β (X * p.1) *
              profTheta α β (X * p.2) / profDelta α β ℓ (X * p.1) (X * p.2)))) := by
          field_simp
        rw [e, h2]
        field_simp
      have hsc : ∑' ℓ : ℤ, X * Fl ℓ (X • p) = X * ∑' ℓ : ℤ, Fl ℓ (X • p) := tsum_mul_left
      have hnn' : 0 ≤ ∑' ℓ : ℤ, X * Fl ℓ (X • p) := by
        refine tsum_nonneg fun ℓ => ?_
        have := (vz_term_bd hα1 hβ0 hβ1 hX hp.1 hp.2 ℓ).1
        have h3 : 0 ≤ X⁻¹ * (X ^ 2 * Fl ℓ (X • p)) := mul_nonneg (inv_nonneg.2 hX.le) this
        have e : X⁻¹ * (X ^ 2 * Fl ℓ (X • p)) = X * Fl ℓ (X • p) := by field_simp
        rw [← e]; exact h3
      have hle' : X * ∑' ℓ : ℤ, Fl ℓ (X • p) ≤ H p := by
        rw [← hsc, ← tsum_congr heq]; exact hle
      rw [hGsc p]
      by_cases hq : p ∈ Q1ᶜ
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
        rw [hsc] at hnn'
        exact ⟨hnn', hle'⟩
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
        simp
    have hGint' : ∫ p, G p ∂μ = X * ∫ p, X * G (X • p) ∂μ := by
      rw [hGint, integral_const_mul]; ring
    rw [hGint']
    refine mul_le_mul_of_nonneg_left ?_ hX.le
    refine integral_mono_of_nonneg (hbnd.mono fun p hp => hp.1) ?_ (hbnd.mono fun p hp => hp.2)
    exact hHint.indicator (hQ1m.compl)
  rw [hdiff]
  refine ⟨integral_nonneg_of_ae htailnn, hmain, fun ℓ => ?_, hqsum⟩
  have hs1 : Summable (fun ℓ : ℤ => ∫ p, g' ℓ p ∂μ) := by
    refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_) hg'norm
    · refine integral_nonneg_of_ae ?_
      filter_upwards [hnn ℓ] with p hp
      simp only [hg']
      by_cases h : p ∈ Qxᶜ
      · rw [Set.indicator_of_mem h]; exact hp
      · rw [Set.indicator_of_notMem h]; exact le_rfl
    · exact integral_mono (hg'int ℓ) (hg'int ℓ).norm (fun p => le_abs_self _ |>.trans (Real.norm_eq_abs _).ge)
  have hnnℓ : 0 ≤ ∫ p, g' ℓ p ∂μ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hnn ℓ] with p hp
    simp only [hg']
    by_cases h : p ∈ Qxᶜ
    · rw [Set.indicator_of_mem h]; exact hp
    · rw [Set.indicator_of_notMem h]; exact le_rfl
  have hfin : (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
        Real.sqrt (u * v) *
        (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)) -
      (∫ p in Qx, Fl ℓ p) = ∫ p, g' ℓ p ∂μ := by
    rw [hsplitℓ ℓ, hqℓ ℓ, hgℓ ℓ]
  rw [hfin]
  refine ⟨hnnℓ, ?_⟩
  have h2 : ∫ p, g' ℓ p ∂μ ≤ ∑' ℓ : ℤ, ∫ p, g' ℓ p ∂μ := hs1.le_tsum ℓ (fun j _ => ?_)
  · rw [hT] at h2; exact h2.trans hmain
  · refine integral_nonneg_of_ae ?_
    filter_upwards [hnn j] with p hp
    simp only [hg']
    by_cases h : p ∈ Qxᶜ
    · rw [Set.indicator_of_mem h]; exact hp
    · rw [Set.indicator_of_notMem h]; exact le_rfl

private lemma pg9_P2_int {α a : ℝ} (hα0 : 0 < α) :
    IntegrableOn (fun m : ℝ => if m ≤ 1 then a ^ (-(α / 2)) * m ^ (α / 2 - 1) else 0) (Ioi 0) ∧
      ∫ m in Ioi (0:ℝ), (if m ≤ 1 then a ^ (-(α / 2)) * m ^ (α / 2 - 1) else 0) =
        a ^ (-(α / 2)) * (2 / α) := by
  set f : ℝ → ℝ := fun m => a ^ (-(α / 2)) * m ^ (α / 2 - 1) with hf
  have e1 : (fun m : ℝ => if m ≤ 1 then f m else 0) = Set.indicator (Iic 1) f := by
    funext m; simp only [Set.indicator_apply, mem_Iic]
  have hfi : IntegrableOn f (Ioc 0 1) :=
    (vg_int_rpow_Ioc (e := α / 2 - 1) (by linarith) 1).const_mul _
  have e2 : Ioi (0:ℝ) ∩ Iic 1 = Ioc 0 1 := by ext x; simp [and_comm]
  change IntegrableOn (fun m : ℝ => if m ≤ 1 then f m else 0) (Ioi 0) ∧
    ∫ m in Ioi (0:ℝ), (if m ≤ 1 then f m else 0) = _
  rw [e1]
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic]
    change Integrable f ((volume.restrict (Ioi (0:ℝ))).restrict (Iic 1))
    rw [Measure.restrict_restrict measurableSet_Iic, Set.inter_comm, e2]
    exact hfi
  · rw [setIntegral_indicator measurableSet_Iic, e2]
    simp only [hf]
    rw [integral_const_mul, pg9_int_rpow_Ioc (by linarith) one_pos]
    rw [Real.one_rpow, show α / 2 - 1 + 1 = α / 2 by ring]
    congr 1
    field_simp

private lemma pg9_M_int3 {P kf : ℝ → ℝ} {A εP : ℝ} (hA : 0 ≤ A) (hP : IntegrableOn P (Ioi 0))
    (hPnn : ∀ m : ℝ, 0 < m → 0 ≤ P m) (hPv : ∫ m in Ioi (0:ℝ), P m = εP)
    (hkf : IntegrableOn kf (Ioi 0)) {S : Set ℝ} (hS : S ⊆ Ioi 0) :
    IntegrableOn (fun m : ℝ => A * (P m + kf m)) S ∧
    ∫ m in S, A * (P m + kf m) ≤ A * (εP + ∫ m in S, kf m) := by
  have hPS := hP.mono_set hS
  have hkS := hkf.mono_set hS
  refine ⟨(hPS.add hkS).const_mul A, ?_⟩
  rw [integral_const_mul, integral_add hPS hkS]
  refine mul_le_mul_of_nonneg_left ?_ hA
  have hP1 : ∫ m in S, P m ≤ ∫ m in Ioi (0:ℝ), P m := by
    refine setIntegral_mono_set hP ?_ hS.eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with m hm
    exact hPnn m hm
  rw [hPv] at hP1
  linarith

private lemma pg9_inf_maj {α Kp X m : ℝ} (hα0 : 0 < α) (hKp : 0 < Kp) (hX : 0 < X) (hm : 0 < m) :
    min ((Kp * m / X) ^ (α / 2)) ((Kp * m / X) ^ (-(α / 2))) *
        (if m ≤ 1 then 1 / m else m ^ (-(1 / 2 : ℝ))) ≤
      (if m ≤ 1 then (X / Kp) ^ (-(α / 2)) * m ^ (α / 2 - 1) else 0) +
      max (Kp ^ (α / 2)) (Kp ^ (-(α / 2))) *
        (X ^ (-(1 / 2 : ℝ)) * (if m / X ≤ 1 then (m / X) ^ (α / 2 - 1) else (m / X) ^ (-((α + 1) / 2)))) := by
  set r : ℝ := m / X with hr
  have hr0 : 0 < r := div_pos hm hX
  have hKr : Kp * m / X = Kp * r := by rw [hr]; ring
  have hmX : m = X * r := by rw [hr]; field_simp
  rw [hKr]
  have hc1 : Kp ^ (α / 2) ≤ max (Kp ^ (α / 2)) (Kp ^ (-(α / 2))) := le_max_left _ _
  have hc2 : Kp ^ (-(α / 2)) ≤ max (Kp ^ (α / 2)) (Kp ^ (-(α / 2))) := le_max_right _ _
  have hKpa : 0 < Kp ^ (α / 2) := Real.rpow_pos_of_pos hKp _
  have hKpb : 0 < Kp ^ (-(α / 2)) := Real.rpow_pos_of_pos hKp _
  have hra : 0 < r ^ (α / 2) := Real.rpow_pos_of_pos hr0 _
  have hrb : 0 < r ^ (-(α / 2)) := Real.rpow_pos_of_pos hr0 _
  have e1 : (Kp * r) ^ (α / 2) = Kp ^ (α / 2) * r ^ (α / 2) := Real.mul_rpow hKp.le hr0.le
  have e2 : (Kp * r) ^ (-(α / 2)) = Kp ^ (-(α / 2)) * r ^ (-(α / 2)) := Real.mul_rpow hKp.le hr0.le
  have hXh : 0 < X ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hX _
  have hg0 : 0 ≤ (if r ≤ 1 then r ^ (α / 2 - 1) else r ^ (-((α + 1) / 2))) := by
    split_ifs
    · exact Real.rpow_nonneg hr0.le _
    · exact Real.rpow_nonneg hr0.le _
  have hmax0 : 0 ≤ max (Kp ^ (α / 2)) (Kp ^ (-(α / 2))) := hKpa.le.trans hc1
  by_cases hm1 : m ≤ 1
  · rw [if_pos hm1, if_pos hm1]
    have hlow : 0 ≤ max (Kp ^ (α / 2)) (Kp ^ (-(α / 2))) *
        (X ^ (-(1 / 2 : ℝ)) * (if r ≤ 1 then r ^ (α / 2 - 1) else r ^ (-((α + 1) / 2)))) := by positivity
    have hmin : min ((Kp * r) ^ (α / 2)) ((Kp * r) ^ (-(α / 2))) ≤ (Kp * r) ^ (α / 2) := min_le_left _ _
    have ha : (X / Kp) ^ (-(α / 2)) * m ^ (α / 2 - 1) = (Kp * r) ^ (α / 2) * (1 / m) := by
      have hXK : X / Kp = m / (Kp * r) := by rw [hmX]; field_simp
      rw [hXK, Real.rpow_neg (by positivity), Real.div_rpow hm.le (by positivity),
        Real.rpow_sub_one hm.ne']
      have hmp : 0 < m ^ (α / 2) := Real.rpow_pos_of_pos hm _
      have hkp : 0 < (Kp * r) ^ (α / 2) := by positivity
      field_simp
    calc min ((Kp * r) ^ (α / 2)) ((Kp * r) ^ (-(α / 2))) * (1 / m)
        ≤ (Kp * r) ^ (α / 2) * (1 / m) :=
          mul_le_mul_of_nonneg_right hmin (by positivity)
      _ = (X / Kp) ^ (-(α / 2)) * m ^ (α / 2 - 1) := ha.symm
      _ ≤ _ := le_add_of_nonneg_right hlow
  · have hm1' : 1 < m := not_le.1 hm1
    rw [if_neg hm1, if_neg hm1]
    simp only [zero_add]
    have hmh : m ^ (-(1 / 2 : ℝ)) = X ^ (-(1 / 2 : ℝ)) * r ^ (-(1 / 2 : ℝ)) := by
      rw [hmX, Real.mul_rpow hX.le hr0.le]
    by_cases hr1 : r ≤ 1
    · rw [if_pos hr1]
      have hmin : min ((Kp * r) ^ (α / 2)) ((Kp * r) ^ (-(α / 2))) ≤ Kp ^ (α / 2) * r ^ (α / 2) :=
        (min_le_left _ _).trans (le_of_eq e1)
      have hrr : r ^ (α / 2) * r ^ (-(1 / 2 : ℝ)) = r ^ (α / 2 - 1 / 2) := by
        rw [← Real.rpow_add hr0]; congr 1
      have hle : r ^ (α / 2 - 1 / 2) ≤ r ^ (α / 2 - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
      calc min ((Kp * r) ^ (α / 2)) ((Kp * r) ^ (-(α / 2))) * m ^ (-(1 / 2 : ℝ))
          ≤ Kp ^ (α / 2) * r ^ (α / 2) * (X ^ (-(1 / 2 : ℝ)) * r ^ (-(1 / 2 : ℝ))) := by
            rw [hmh]; exact mul_le_mul_of_nonneg_right hmin (by positivity)
        _ = Kp ^ (α / 2) * (X ^ (-(1 / 2 : ℝ)) * r ^ (α / 2 - 1 / 2)) := by rw [← hrr]; ring
        _ ≤ Kp ^ (α / 2) * (X ^ (-(1 / 2 : ℝ)) * r ^ (α / 2 - 1)) := by
            apply mul_le_mul_of_nonneg_left _ hKpa.le
            exact mul_le_mul_of_nonneg_left hle hXh.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hc1 (by positivity)
    · rw [if_neg hr1]
      have hr1' : 1 < r := not_le.1 hr1
      have hmin : min ((Kp * r) ^ (α / 2)) ((Kp * r) ^ (-(α / 2))) ≤ Kp ^ (-(α / 2)) * r ^ (-(α / 2)) :=
        (min_le_right _ _).trans (le_of_eq e2)
      have hrr : r ^ (-(α / 2)) * r ^ (-(1 / 2 : ℝ)) = r ^ (-((α + 1) / 2)) := by
        rw [← Real.rpow_add hr0]; congr 1; ring
      calc min ((Kp * r) ^ (α / 2)) ((Kp * r) ^ (-(α / 2))) * m ^ (-(1 / 2 : ℝ))
          ≤ Kp ^ (-(α / 2)) * r ^ (-(α / 2)) * (X ^ (-(1 / 2 : ℝ)) * r ^ (-(1 / 2 : ℝ))) := by
            rw [hmh]; exact mul_le_mul_of_nonneg_right hmin (by positivity)
        _ = Kp ^ (-(α / 2)) * (X ^ (-(1 / 2 : ℝ)) * r ^ (-((α + 1) / 2))) := by rw [← hrr]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hc2 (by positivity)

private lemma pg9_inf_alg {α Kp y γ X : ℝ} (hKp : 0 < Kp) (hy : 0 < y) (hγ : 0 < γ) (hX : 0 < X)
    (hrel : γ / X = 1 / (Kp * y)) :
    y ^ (α / 2) * Real.sqrt γ / Real.sqrt X = Kp ^ (-(1 / 2 : ℝ)) * y ^ ((α - 1) / 2) ∧
    γ * y ^ α / X = Kp⁻¹ * y ^ (α - 1) := by
  constructor
  · have h1 : Real.sqrt γ / Real.sqrt X = Real.sqrt (γ / X) := (Real.sqrt_div hγ.le X).symm
    have h2 : Real.sqrt (γ / X) = (Kp * y) ^ (-(1 / 2 : ℝ)) := by
      rw [hrel, Real.sqrt_eq_rpow, one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
    calc y ^ (α / 2) * Real.sqrt γ / Real.sqrt X = y ^ (α / 2) * (Real.sqrt γ / Real.sqrt X) := by ring
      _ = y ^ (α / 2) * (Kp * y) ^ (-(1 / 2 : ℝ)) := by rw [h1, h2]
      _ = Kp ^ (-(1 / 2 : ℝ)) * y ^ ((α - 1) / 2) := by
        rw [Real.mul_rpow hKp.le hy.le]
        have : y ^ (α / 2) * y ^ (-(1 / 2 : ℝ)) = y ^ ((α - 1) / 2) := by
          rw [← Real.rpow_add hy]; congr 1; ring
        rw [← this]; ring
  · have : γ * y ^ α / X = y ^ α * (γ / X) := by ring
    rw [this, hrel]
    have hya : y ^ α = y ^ (α - 1) * y := by
      rw [Real.rpow_sub_one hy.ne']; field_simp
    rw [hya]; field_simp

set_option maxHeartbeats 6400000 in
private lemma pg9_tail_seqInf {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    ∀ ε' > 0, ∃ k0 : ℕ, ∀ k ≥ k0, ∀ᶠ n in atTop, ∀ s : Finset ℤ,
      ∫ p in (Ioo 0 (gammaOf (N n) (B n)) ×ˢ Ioo 0 (gammaOf (N n) (B n))) \
        (Icc (rowIdx (i n) / icCross α (B n) / ((k : ℝ) + 1))
            (rowIdx (i n) / icCross α (B n) * ((k : ℝ) + 1)) ×ˢ
          Icc (rowIdx (i n) / icCross α (B n) / ((k : ℝ) + 1))
            (rowIdx (i n) / icCross α (B n) * ((k : ℝ) + 1))),
        ∑ ℓ ∈ s, lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2 ≤
          ε' * (rowIdx (i n) / icCross α (B n)) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  obtain ⟨C1, C2, hC1, hC2, htail⟩ := pg9_tail_fin hα1 R.hβ0 R.hβ1
  obtain ⟨A, hA, hkbd⟩ := pg9_k_bd2 hα1 R.hβ0 R.hβ1
  obtain ⟨Cup, hup⟩ := lem_app_pl_upper (α := α) (β := β) (1 / 8) (by norm_num) (by norm_num)
  have hupn := hup N B c R
  set g0 : ℝ → ℝ := fun r => if r ≤ 1 then r ^ (α / 2 - 1) else r ^ (-((α + 1) / 2)) with hg0
  have hg0i : IntegrableOn g0 (Ioi 0) := pg9_g0_int hα1
  set cK : ℝ := max (Kc α ^ (α / 2)) (Kc α ^ (-(α / 2))) with hcK
  have hcK0 : 0 < cK := lt_of_lt_of_le (Real.rpow_pos_of_pos hK _) (le_max_left _ _)
  set Kg : ℝ := ∫ r in Ioi (0:ℝ), g0 r with hKg
  have hKg0 : 0 ≤ Kg := setIntegral_nonneg measurableSet_Ioi (fun r hr => pg9_g0_nonneg hr)
  have hτ := pg9_tauk_lim (α := α) hα1 (aL := 1) (aU := 1) one_pos one_pos
  simp only [Real.one_rpow, div_one, one_mul] at hτ
  intro ε' hε'
  set Cu : ℝ := max Cup 0 with hCu
  have hCu0 : 0 ≤ Cu := le_max_right _ _
  set τg : ℕ → ℝ := fun k => (∫ r in Ioc (0:ℝ) (1 / ((k : ℝ) + 1)), g0 r) +
    ∫ r in Ioi ((k : ℝ) + 1), g0 r with hτg
  have hτg' : Tendsto τg atTop (𝓝 0) := hτ
  have hLk : ∀ᶠ k : ℕ in atTop, C1 * A ^ 2 * ((cK * τg k) * (cK * Kg)) < ε' := by
    have := ((hτg'.const_mul cK).mul_const (cK * Kg)).const_mul (C1 * A ^ 2)
    simp only [mul_zero, zero_mul] at this
    exact this.eventually (gt_mem_nhds hε')
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 hLk
  refine ⟨k0, fun k hk => ?_⟩
  have hLk' := hk0 k hk
  set τk : ℝ := cK * τg k with hτk
  set Kf : ℝ := cK * Kg with hKf
  have hKf0 : 0 ≤ Kf := by positivity
  have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  have hρpos : ∀ n, 0 < rowIdx (i n) := fun n => by unfold rowIdx; positivity
  have hBr : ∀ n, (0:ℝ) < (B n : ℝ) := fun n => by exact_mod_cast R.hBpos n
  have hNr : ∀ n, (0:ℝ) < (N n : ℝ) := fun n => by exact_mod_cast R.hNpos n
  have hXdef : ∀ n, rowIdx (i n) / icCross α (B n) = Kc α * (rowIdx (i n) / (B n : ℝ)) := fun n => by
    unfold icCross; have := hBr n; field_simp
  -- sequences
  have hρ0 : Tendsto (fun n => (rowIdx (i n)) ^ (-(α / 2))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity)).comp hi
  have ha : Tendsto (fun n => rowIdx (i n) / (B n : ℝ)) atTop atTop := by
    have := hX.const_mul_atTop (inv_pos.2 hK)
    refine this.congr (fun n => ?_)
    rw [hXdef n]; field_simp
  have haneg : Tendsto (fun n => (rowIdx (i n) / (B n : ℝ)) ^ (-(α / 2))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity)).comp ha
  have hεn : Tendsto (fun n => 2 * (rowIdx (i n)) ^ (-(α / 2)) +
      (rowIdx (i n) / (B n : ℝ)) ^ (-(α / 2)) * (2 / α)) atTop (𝓝 0) := by
    simpa using (hρ0.const_mul 2).add (haneg.mul_const (2 / α))
  have hsqX : Tendsto (fun n => Real.sqrt (rowIdx (i n) / icCross α (B n))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hX
  have he1 : Tendsto (fun n => (2 * (rowIdx (i n)) ^ (-(α / 2)) +
      (rowIdx (i n) / (B n : ℝ)) ^ (-(α / 2)) * (2 / α)) /
      Real.sqrt (rowIdx (i n) / icCross α (B n))) atTop (𝓝 0) := hεn.div_atTop hsqX
  have hy0 : ∀ n, 0 < rowFrac (i n) := fun n => by unfold rowFrac; have := hρpos n; have := hNr n; positivity
  have hrel : ∀ n, gammaOf (N n) (B n) / (rowIdx (i n) / icCross α (B n)) =
      1 / (Kc α * rowFrac (i n)) := fun n => by
    unfold gammaOf rowFrac icCross
    have := hBr n; have := hNr n; have := hρpos n
    field_simp
  have hγpos : ∀ n, 0 < gammaOf (N n) (B n) := fun n => by
    unfold gammaOf; exact div_pos (hNr n) (hBr n)
  have hXposn : ∀ n, 0 < rowIdx (i n) / icCross α (B n) := fun n => by
    rw [hXdef n]; have := hρpos n; have := hBr n; positivity
  have hr1eq : ∀ n, (rowFrac (i n)) ^ (α / 2) * Real.sqrt (gammaOf (N n) (B n)) /
      Real.sqrt (rowIdx (i n) / icCross α (B n)) = Kc α ^ (-(1 / 2 : ℝ)) * (rowFrac (i n)) ^ ((α - 1) / 2) :=
    fun n => (pg9_inf_alg hK (hy0 n) (hγpos n) (hXposn n) (hrel n)).1
  have hs1eq : ∀ n, gammaOf (N n) (B n) * (rowFrac (i n)) ^ α / (rowIdx (i n) / icCross α (B n)) =
      (Kc α)⁻¹ * (rowFrac (i n)) ^ (α - 1) :=
    fun n => (pg9_inf_alg hK (hy0 n) (hγpos n) (hXposn n) (hrel n)).2
  have hy1 : Tendsto (fun n => (rowFrac (i n)) ^ ((α - 1) / 2)) atTop (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ => x ^ ((α - 1) / 2)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr (by linarith))
    simpa [Real.zero_rpow (by linarith : (α - 1) / 2 ≠ 0), Function.comp_def] using hc.tendsto.comp hx
  have hy2 : Tendsto (fun n => (rowFrac (i n)) ^ (α - 1)) atTop (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ => x ^ (α - 1)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr (by linarith))
    simpa [Real.zero_rpow (by linarith : α - 1 ≠ 0), Function.comp_def] using hc.tendsto.comp hx
  have hr1 : Tendsto (fun n => (rowFrac (i n)) ^ (α / 2) * Real.sqrt (gammaOf (N n) (B n)) /
      Real.sqrt (rowIdx (i n) / icCross α (B n))) atTop (𝓝 0) := by
    simp only [hr1eq]; simpa using hy1.const_mul (Kc α ^ (-(1 / 2 : ℝ)))
  have hs1 : Tendsto (fun n => gammaOf (N n) (B n) * (rowFrac (i n)) ^ α /
      (rowIdx (i n) / icCross α (B n))) atTop (𝓝 0) := by
    simp only [hs1eq]; simpa using hy2.const_mul (Kc α)⁻¹
  have hbn : Tendsto (fun n =>
      C1 * A ^ 2 * ((2 * ((2 * (rowIdx (i n)) ^ (-(α / 2)) +
          (rowIdx (i n) / (B n : ℝ)) ^ (-(α / 2)) * (2 / α)) /
          Real.sqrt (rowIdx (i n) / icCross α (B n))) + τk) *
        (((2 * (rowIdx (i n)) ^ (-(α / 2)) +
          (rowIdx (i n) / (B n : ℝ)) ^ (-(α / 2)) * (2 / α)) /
          Real.sqrt (rowIdx (i n) / icCross α (B n))) + Kf)) +
      C2 * A * (((2 * (rowIdx (i n)) ^ (-(α / 2)) +
          (rowIdx (i n) / (B n : ℝ)) ^ (-(α / 2)) * (2 / α)) /
          Real.sqrt (rowIdx (i n) / icCross α (B n))) + Kf) *
        ((rowFrac (i n)) ^ (α / 2) * Real.sqrt (gammaOf (N n) (B n)) /
          Real.sqrt (rowIdx (i n) / icCross α (B n))) +
      Real.pi ^ 2 * (Cu * (gammaOf (N n) (B n) * (rowFrac (i n)) ^ α /
        (rowIdx (i n) / icCross α (B n))))) atTop
      (𝓝 (C1 * A ^ 2 * ((2 * 0 + τk) * (0 + Kf)) + C2 * A * (0 + Kf) * 0 + Real.pi ^ 2 * (Cu * 0))) := by
    refine Tendsto.add (Tendsto.add ?_ ?_) ?_
    · exact (((he1.const_mul 2).add_const τk).mul (he1.add_const Kf)).const_mul _
    · exact ((he1.add_const Kf).const_mul (C2 * A)).mul hr1
    · exact (hs1.const_mul Cu).const_mul _
  have hbn' : ∀ᶠ n in atTop,
      C1 * A ^ 2 * ((2 * ((2 * (rowIdx (i n)) ^ (-(α / 2)) +
          (rowIdx (i n) / (B n : ℝ)) ^ (-(α / 2)) * (2 / α)) /
          Real.sqrt (rowIdx (i n) / icCross α (B n))) + τk) *
        (((2 * (rowIdx (i n)) ^ (-(α / 2)) +
          (rowIdx (i n) / (B n : ℝ)) ^ (-(α / 2)) * (2 / α)) /
          Real.sqrt (rowIdx (i n) / icCross α (B n))) + Kf)) +
      C2 * A * (((2 * (rowIdx (i n)) ^ (-(α / 2)) +
          (rowIdx (i n) / (B n : ℝ)) ^ (-(α / 2)) * (2 / α)) /
          Real.sqrt (rowIdx (i n) / icCross α (B n))) + Kf) *
        ((rowFrac (i n)) ^ (α / 2) * Real.sqrt (gammaOf (N n) (B n)) /
          Real.sqrt (rowIdx (i n) / icCross α (B n))) +
      Real.pi ^ 2 * (Cu * (gammaOf (N n) (B n) * (rowFrac (i n)) ^ α /
        (rowIdx (i n) / icCross α (B n)))) < ε' := by
    refine hbn.eventually (gt_mem_nhds ?_)
    simp only [mul_zero, zero_add, add_zero]
    have : C1 * A ^ 2 * (τk * Kf) = C1 * A ^ 2 * ((cK * τg k) * (cK * Kg)) := rfl
    rw [this]; exact hLk'
  filter_upwards [hbn', hX.eventually_ge_atTop 1, hg.eventually_ge_atTop 2, hupn,
    hi.eventually_gt_atTop 0] with n h1 hX1 h3 h4 h5
  intro s
  have hN := R.hNpos n
  have hB := R.hBpos n
  have hc := R.hcpos n
  have hBr' := hBr n
  set ρ : ℝ := rowIdx (i n) with hρ
  have hρ0 : 0 < ρ := hρpos n
  set X : ℝ := rowIdx (i n) / icCross α (B n) with hXn
  have hXp : 0 < X := hXposn n
  set a : ℝ := ρ / (B n : ℝ) with ha_def
  have ha0 : 0 < a := by positivity
  have key : X = Kc α * a := hXdef n
  have hγ0 : 0 < gammaOf (N n) (B n) := hγpos n
  set γ := gammaOf (N n) (B n) with hγdef
  set y : ℝ := rowFrac (i n) with hydef
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hXp
  have hsXX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hXp.le
  obtain ⟨hUp1, hUp2, hUp3⟩ := h4 (i n)
  -- the pieces
  set ε : ℝ := 2 * ρ ^ (-(α / 2)) + a ^ (-(α / 2)) * (2 / α) with hε
  have hε0 : 0 ≤ ε := by positivity
  set P : ℝ → ℝ := fun m =>
    (if m < 1 / (B n : ℝ) then Real.sqrt (B n : ℝ) * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) +
    (if m ≤ 1 then a ^ (-(α / 2)) * m ^ (α / 2 - 1) else 0) with hP
  obtain ⟨hP1i, hP1v⟩ := pg9_P_int (α := α) (ρ := ρ) hBr'
  obtain ⟨hP2i, hP2v⟩ := pg9_P2_int (α := α) (a := a) hα0
  have hP1i' : IntegrableOn (fun m : ℝ => if m < 1 / (B n : ℝ) then
      Real.sqrt (B n : ℝ) * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) (Ioi 0) := hP1i
  have hPi : IntegrableOn P (Ioi 0) := hP1i'.add hP2i
  have hPv : ∫ m in Ioi (0:ℝ), P m = ε := by
    simp only [hP]
    rw [integral_add hP1i' hP2i, hP1v, hP2v]
  have hPnn : ∀ m : ℝ, 0 < m → 0 ≤ P m := by
    intro m hm
    simp only [hP]
    have h1 : 0 ≤ (if m < 1 / (B n : ℝ) then
      Real.sqrt (B n : ℝ) * ρ ^ (-(α / 2)) * m ^ (-(1 / 2 : ℝ)) else 0) := by
      split_ifs
      · positivity
      · exact le_rfl
    have h2 : 0 ≤ (if m ≤ 1 then a ^ (-(α / 2)) * m ^ (α / 2 - 1) else 0) := by
      split_ifs
      · positivity
      · exact le_rfl
    exact add_nonneg h1 h2
  set kfn : ℝ → ℝ := fun m => cK * (X ^ (-(1 / 2 : ℝ)) * g0 (m / X)) with hkfn
  have hkfi : IntegrableOn kfn (Ioi 0) := by
    have h1 : IntegrableOn (fun m : ℝ => g0 (X⁻¹ * m)) (Ioi 0) :=
      (integrableOn_Ioi_comp_mul_left_iff g0 0 (inv_pos.2 hXp)).2 (by rw [mul_zero]; exact hg0i)
    have h2 : IntegrableOn (fun m : ℝ => cK * (X ^ (-(1 / 2 : ℝ)) * g0 (X⁻¹ * m))) (Ioi 0) :=
      (h1.const_mul (X ^ (-(1 / 2 : ℝ)))).const_mul cK
    refine h2.congr_fun (fun m _ => ?_) measurableSet_Ioi
    simp only [hkfn, div_eq_inv_mul]
  have hkfnn : ∀ m : ℝ, 0 < m → 0 ≤ kfn m := by
    intro m hm
    simp only [hkfn]
    have := pg9_g0_nonneg (α := α) (div_pos hm hXp)
    have := Real.rpow_nonneg hXp.le (-(1 / 2 : ℝ))
    positivity
  have hXs : X ^ (-(1 / 2 : ℝ)) * X = Real.sqrt X := by
    calc X ^ (-(1 / 2 : ℝ)) * X = X ^ (-(1 / 2 : ℝ)) * X ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = X ^ (-(1 / 2 : ℝ) + 1) := (Real.rpow_add hXp _ _).symm
      _ = Real.sqrt X := by rw [Real.sqrt_eq_rpow]; norm_num
  set Kn : ℝ := cK * (Real.sqrt X * Kg) with hKn
  have hKn0 : 0 ≤ Kn := by positivity
  have hKfv : ∫ m in Ioi (0:ℝ), kfn m = Kn := by
    simp only [hkfn, hg0]
    rw [integral_const_mul, integral_const_mul, pg9_g0_scale_Ioi hXp]
    simp only [zero_div, hKn, hKg, hg0]
    rw [← hXs]; ring
  set τn : ℝ := cK * (Real.sqrt X * τg k) with hτn
  have hτv : (∫ m in Ioc (0:ℝ) (X / ((k : ℝ) + 1)), kfn m) +
      (∫ m in Ioi (X * ((k : ℝ) + 1)), kfn m) = τn := by
    simp only [hkfn, hg0]
    rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      pg9_g0_scale_Ioc hXp (by positivity), pg9_g0_scale_Ioi hXp]
    have e1 : X / ((k : ℝ) + 1) / X = 1 / ((k : ℝ) + 1) := by field_simp
    have e2 : X * ((k : ℝ) + 1) / X = (k : ℝ) + 1 := by field_simp
    rw [e1, e2, hτn]
    simp only [hτg, hg0]
    rw [← hXs]; ring
  have hδ : (0:ℝ) < X / ((k : ℝ) + 1) := by positivity
  have hδR : X / ((k : ℝ) + 1) ≤ X * ((k : ℝ) + 1) := by
    have h1 : (1:ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    rw [div_eq_mul_one_div]
    apply mul_le_mul_of_nonneg_left _ hXp.le
    calc 1 / ((k : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; exact h1
      _ ≤ _ := h1
  set M : ℝ → ℝ := fun m => A * (P m + kfn m) with hM
  have hMint : ∀ S : Set ℝ, S ⊆ Ioi 0 → MeasurableSet S →
      IntegrableOn M S ∧ ∫ m in S, M m ≤ A * (ε + ∫ m in S, kfn m) :=
    fun S hS hSm => pg9_M_int3 hA.le hPi hPnn hPv hkfi hS
  have hMnn : ∀ m : ℝ, 0 < m → 0 ≤ M m := fun m hm => by
    simp only [hM]; have := hPnn m hm; have := hkfnn m hm; positivity
  have hkM : ∀ m ∈ Ioc 0 (gammaOf (N n) (B n) / 2),
      Wpart β (B n) (plSpec α (c n) (N n)) (i n) m * min (Real.sqrt m) 1 ≤ M m := by
    intro m hm
    refine (hkbd (N n) (B n) (c n) hN hB hc (i n) m (by linarith) hm.1 hm.2).trans ?_
    simp only [hM, hP]
    have hρeq : ((i n : ℕ) : ℝ) + 1 = ρ := rfl
    rw [hρeq]
    refine mul_le_mul_of_nonneg_left ?_ hA.le
    have hP2nn : 0 ≤ (if m ≤ 1 then a ^ (-(α / 2)) * m ^ (α / 2 - 1) else 0) := by
      split_ifs
      · have := hm.1; positivity
      · exact le_rfl
    have hkn := hkfnn m hm.1
    by_cases hmB : 1 / (B n : ℝ) ≤ m
    · rw [if_pos hmB]
      have hmaj := pg9_inf_maj (α := α) (Kp := Kc α) (X := X) (m := m) hα0 hK hXp hm.1
      have e : Kc α * m / X = (B n : ℝ) * m / ρ := by
        rw [key, ha_def]; field_simp
      have e' : X / Kc α = a := by rw [key]; field_simp
      rw [e, e'] at hmaj
      have : (if m ≤ 1 then a ^ (-(α / 2)) * m ^ (α / 2 - 1) else 0) + kfn m =
          (if m ≤ 1 then a ^ (-(α / 2)) * m ^ (α / 2 - 1) else 0) +
          max (Kc α ^ (α / 2)) (Kc α ^ (-(α / 2))) *
            (X ^ (-(1 / 2 : ℝ)) * (if m / X ≤ 1 then (m / X) ^ (α / 2 - 1)
              else (m / X) ^ (-((α + 1) / 2)))) := rfl
      linarith
    · rw [if_neg hmB]
      linarith
  have hUint := (lem_app_pl_age_iv hα0 R.hβ0 R.hβ1 (N n) (B n) (c n) hN hB hc (i n)).2.2.1
  have hSb := pg9_regS hα0 R.hβ0 R.hβ1 hN hB hc (i n) s Cup (by
    intro ℓ; have := (hUp1 ℓ); rwa [show (1 / 8 : ℝ) * gammaOf (N n) (B n) = gammaOf (N n) (B n) / 8 by ring] at this)
    (by have := hUp2; rwa [show (1 / 8 : ℝ) * gammaOf (N n) (B n) = gammaOf (N n) (B n) / 8 by ring] at this)
    (by have := hUp3; rwa [show (1 / 8 : ℝ) * gammaOf (N n) (B n) = gammaOf (N n) (B n) / 8 by ring] at this)
  have hfin := htail (N n) (B n) (c n) hN hB hc (i n) s (X / ((k : ℝ) + 1)) (X * ((k : ℝ) + 1)) A
    ε Kn τn _ kfn M h3 hδ hδR hA.le hε0 hKn0 hUint hMnn hMint hkfnn hkfi hkM hKfv hτv hSb
  have hyeq : (((i n : ℕ) : ℝ) + 1) / (N n : ℝ) = y := rfl
  rw [hyeq] at hfin
  set e1 : ℝ := ε / Real.sqrt X with he1def
  set r1 : ℝ := y ^ (α / 2) * Real.sqrt γ / Real.sqrt X with hr1def
  set s1 : ℝ := γ * y ^ α / X with hs1def
  have hε' : ε = Real.sqrt X * e1 := by rw [he1def]; field_simp
  have hτn' : τn = Real.sqrt X * τk := by rw [hτn, hτk]; ring
  have hKn' : Kn = Real.sqrt X * Kf := by rw [hKn, hKf]; ring
  have hr1' : y ^ (α / 2) * Real.sqrt γ = Real.sqrt X * r1 := by rw [hr1def]; field_simp
  have hs1' : γ * y ^ α = X * s1 := by rw [hs1def]; field_simp
  have hq1 : (2 * ε + τn) * (ε + Kn) = X * ((2 * e1 + τk) * (e1 + Kf)) := by
    rw [hτn', hKn', hε']
    have : (2 * (Real.sqrt X * e1) + Real.sqrt X * τk) * (Real.sqrt X * e1 + Real.sqrt X * Kf) =
        (Real.sqrt X * Real.sqrt X) * ((2 * e1 + τk) * (e1 + Kf)) := by ring
    rw [this, hsXX]
  have hq2 : C2 * A * (ε + Kn) * y ^ (α / 2) * Real.sqrt γ = X * (C2 * A * (e1 + Kf) * r1) := by
    have : C2 * A * (ε + Kn) * y ^ (α / 2) * Real.sqrt γ =
        C2 * A * (ε + Kn) * (y ^ (α / 2) * Real.sqrt γ) := by ring
    rw [this, hr1', hKn', hε']
    have : C2 * A * (Real.sqrt X * e1 + Real.sqrt X * Kf) * (Real.sqrt X * r1) =
        (Real.sqrt X * Real.sqrt X) * (C2 * A * (e1 + Kf) * r1) := by ring
    rw [this, hsXX]
  have hSb' : Real.pi ^ 2 * (Cup * γ * y ^ α) ≤ Real.pi ^ 2 * (Cu * (X * s1)) := by
    have hpos : 0 ≤ γ * y ^ α := by have := hy0 n; positivity
    have : Cup * γ * y ^ α ≤ Cu * (X * s1) := by
      rw [← hs1']
      calc Cup * γ * y ^ α = Cup * (γ * y ^ α) := by ring
        _ ≤ Cu * (γ * y ^ α) := mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hXpos' := hXp
  have hmain : C1 * A ^ 2 * ((2 * ε + τn) * (ε + Kn)) +
      C2 * A * (ε + Kn) * y ^ (α / 2) * Real.sqrt γ + Real.pi ^ 2 * (Cup * γ * y ^ α) ≤
      X * (C1 * A ^ 2 * ((2 * e1 + τk) * (e1 + Kf)) + C2 * A * (e1 + Kf) * r1 +
        Real.pi ^ 2 * (Cu * s1)) := by
    rw [hq1, hq2]
    have : Real.pi ^ 2 * (Cu * (X * s1)) = X * (Real.pi ^ 2 * (Cu * s1)) := by ring
    nlinarith [hSb', this]
  calc _ ≤ _ := hfin
    _ ≤ _ := hmain
    _ ≤ ε' * X := by
        have := mul_lt_mul_of_pos_left h1 hXp
        linarith

open Muon.DetEquiv ProbabilityTheory in
set_option maxHeartbeats 6400000 in
private lemma pg9_inf_rel {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (hBound : volHBound α β N B c)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, |vPart β (B n) (plSpec α (c n) (N n)) (i n) -
      profG α β (rowIdx (i n) / icCross α (B n))| ≤ δ * (rowIdx (i n) / icCross α (B n)) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  have hπ : 0 < Real.pi ^ 2 := by positivity
  set X : ℕ → ℝ := fun n => rowIdx (i n) / icCross α (B n) with hXdef
  have hρ : ∀ n, 0 < rowIdx (i n) := fun n => by unfold rowIdx; positivity
  have hBr : ∀ n, (0:ℝ) < (B n : ℝ) := fun n => by exact_mod_cast R.hBpos n
  have hNr : ∀ n, (0:ℝ) < (N n : ℝ) := fun n => by exact_mod_cast R.hNpos n
  have hXpos : ∀ n, 0 < X n := fun n => by
    simp only [hXdef]; unfold icCross
    have := hBr n; have := hρ n; positivity
  have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  have hγpos : ∀ n, 0 < gammaOf (N n) (B n) := fun n => by
    unfold gammaOf; exact div_pos (hNr n) (hBr n)
  have hXγ : Tendsto (fun n => rowIdx (i n) / icCross α (B n) / gammaOf (N n) (B n)) atTop (𝓝 0) := by
    have : ∀ n, rowIdx (i n) / icCross α (B n) / gammaOf (N n) (B n) = Kc α * rowFrac (i n) := fun n => by
      unfold icCross gammaOf rowFrac
      have := hBr n; have := hNr n; have := hρ n
      field_simp
    simp only [this]; simpa using hx.const_mul (Kc α)
  -- continuum asymptotics
  have hII := lem_app_pl_supervol_ii_inf hα1 R.hβ0 R.hβ1
  set cinf : ℝ := 4 * Kc α / (α - 1) with hcinf
  have hcinf0 : 0 < cinf := by
    rw [hcinf]; have : 0 < α - 1 := by linarith
    positivity
  have hGr : Tendsto (fun n => profG α β (X n) / (cinf * X n)) atTop (𝓝 1) := by
    have h := hII.comp_tendsto hX
    refine (isEquivalent_iff_tendsto_one ?_).1 h
    filter_upwards [hX.eventually_gt_atTop 0] with n hn
    exact (mul_pos hcinf0 hn).ne'
  obtain ⟨H, hHint, hcont⟩ := pg9_cont_tail_inf hα1 R.hβ0 R.hβ1
  have hTk := pg9_Tk_lim hHint
  set Gm : ℕ → ℝ := fun n => ∑' ℓ : ℤ, ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
    Real.sqrt (profZeta α (X n) u * (1 - profZeta α (X n) u) *
      (profZeta α (X n) v * (1 - profZeta α (X n) v))) / Real.sqrt (u * v) *
    (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v) with hGm
  have hGprofG : ∀ n, profG α β (X n) = (1 / Real.pi ^ 2) * Gm n := fun n => by
    simp only [hGm]; unfold profG; rfl
  set ε3 : ℝ := Real.pi ^ 2 * δ / 8 with hε3
  have hε3pos : 0 < ε3 := by positivity
  set Mb : ℝ := 2 * Real.pi ^ 2 * cinf with hMb
  have hMb0 : 0 < Mb := by positivity
  set η : ℝ := ε3 / (Mb + 1) with hη
  have hηpos : 0 < η := by positivity
  have hηMb : η * Mb ≤ ε3 := by
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  have hGbd : ∀ᶠ n in atTop, Gm n ≤ Mb * X n := by
    filter_upwards [hGr.eventually (gt_mem_nhds (by norm_num : (1:ℝ) < 2)), hX.eventually_gt_atTop 0]
      with n hn hXn
    have h1 : profG α β (X n) < 2 * (cinf * X n) := by
      rw [div_lt_iff₀ (mul_pos hcinf0 hXn)] at hn; linarith
    rw [hGprofG n] at h1
    have : Gm n < 2 * Real.pi ^ 2 * (cinf * X n) := by
      have h2 : (1 / Real.pi ^ 2) * Gm n < 2 * (cinf * X n) := h1
      rw [one_div, inv_mul_lt_iff₀ hπ] at h2; linarith
    rw [hMb]; nlinarith
  obtain ⟨k1, hk1⟩ := eventually_atTop.1 (hTk.eventually (gt_mem_nhds hε3pos))
  obtain ⟨k0, hk0⟩ := pg9_tail_seqInf R hα1 i hi hX hx ε3 hε3pos
  set k : ℕ := max k0 k1 with hk
  have hkk0 : k ≥ k0 := le_max_left _ _
  have hkk1 : k ≥ k1 := le_max_right _ _
  have hTkk := hk1 k hkk1
  have hδk : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hδR : 1 / ((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
    have h1 : (1:ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    calc 1 / ((k : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; exact h1
      _ ≤ _ := h1
  have hunif := pg9_unif_close R hα1 i hi hXγ hδk hδR hηpos
  have hXsmall : ∀ᶠ n in atTop, X n * ((k : ℝ) + 1) < gammaOf (N n) (B n) := by
    have : ∀ n, X n * ((k : ℝ) + 1) < gammaOf (N n) (B n) ↔
        ((k : ℝ) + 1) * (X n / gammaOf (N n) (B n)) < 1 := fun n => by
      rw [← mul_div_assoc, div_lt_one (hγpos n)]; constructor <;> intro h <;> linarith
    have h1 := hXγ.const_mul ((k : ℝ) + 1)
    simp only [mul_zero] at h1
    filter_upwards [h1.eventually (gt_mem_nhds (zero_lt_one' ℝ))] with n hn
    exact (this n).2 hn
  filter_upwards [hk0 k hkk0, hunif, hXsmall, hGbd, hX.eventually_ge_atTop (8 / δ), hX.eventually_ge_atTop 1,
    hX.eventually_gt_atTop 0] with n htail hu hxs hG hX8 hX1 hXn0
  have hN := R.hNpos n
  have hB := R.hBpos n
  have hc := R.hcpos n
  have hXn := hXpos n
  set Q : Set (ℝ × ℝ) := Icc (X n / ((k : ℝ) + 1)) (X n * ((k : ℝ) + 1)) ×ˢ
    Icc (X n / ((k : ℝ) + 1)) (X n * ((k : ℝ) + 1)) with hQ
  have hQm : MeasurableSet Q := measurableSet_Icc.prod measurableSet_Icc
  have hk0pos : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hXk0 : 0 < X n / ((k : ℝ) + 1) := by positivity
  have hQsub0 : Q ⊆ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) := fun p hp =>
    ⟨lt_of_lt_of_le hXk0 hp.1.1, lt_of_lt_of_le hXk0 hp.2.1⟩
  have hQU : Q ⊆ Ioo 0 (gammaOf (N n) (B n)) ×ˢ Ioo 0 (gammaOf (N n) (B n)) := fun p hp =>
    ⟨⟨lt_of_lt_of_le hXk0 hp.1.1, lt_of_le_of_lt hp.1.2 hxs⟩,
      ⟨lt_of_lt_of_le hXk0 hp.2.1, lt_of_le_of_lt hp.2.2 hxs⟩⟩
  obtain ⟨hs0, hs1, -, hsq⟩ := pg9_split hα0 R.hβ0 R.hβ1 hN hB hc (i n) hQm hQU htail
  obtain ⟨hc0, hc1, -, hcsum⟩ := hcont k (X n) hX1
  obtain ⟨hint, -⟩ := vs_finite_all hα1 R.hβ0 R.hβ1 (X n) hXn
  have hUint := (lem_app_pl_age_iv hα0 R.hβ0 R.hβ1 (N n) (B n) (c n) hN hB hc (i n)).2.2.1
  have hcmp := pg9_cmp_Q (Q := Q)
    (f := fun ℓ p => lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2)
    (g := fun ℓ p => Real.sqrt (profZeta α (X n) p.1 * (1 - profZeta α (X n) p.1) *
              (profZeta α (X n) p.2 * (1 - profZeta α (X n) p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2)) hQm hηpos.le
    (fun ℓ => (hUint ℓ).mono_set hQU) (fun ℓ => pg9_int_vol hQm hQsub0 (hint ℓ)) hsq hcsum
    (by
      intro p hp ℓ
      have e1 : (1 / ((k : ℝ) + 1)) * X n = X n / ((k : ℝ) + 1) := by ring
      have e2 : ((k : ℝ) + 1) * X n = X n * ((k : ℝ) + 1) := by ring
      exact hu p.1 p.2 (by rw [e1]; exact hp.1.1) (by rw [e2]; exact hp.1.2)
        (by rw [e1]; exact hp.2.1) (by rw [e2]; exact hp.2.2) ℓ)
  obtain ⟨-, hcmps⟩ := hcmp
  have hrep := pg9_vPart_rep2 hα0 R.hβ0 R.hβ1 hN hB hc (i n)
  have hB0 := hBound n (i n) 0
  set Pn : ℝ := ∑' ℓ : ℤ, lagTerm β (B n) (plSpec α (c n) (N n)) (i n)
    (Ioo 0 (gammaOf (N n) (B n))) (Ioo 0 (gammaOf (N n) (B n))) ℓ with hPn
  set Pn0 : ℝ := lagTerm β (B n) (plSpec α (c n) (N n)) (i n)
    (Ioo 0 (gammaOf (N n) (B n))) (Ioo 0 (gammaOf (N n) (B n))) 0 with hPn0
  set Sn : ℝ := ∑' ℓ : ℤ, ∫ p in Q, lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) ℓ p.1 p.2
    with hSn
  set Sc : ℝ := ∑' ℓ : ℤ, ∫ p in Q, Real.sqrt (profZeta α (X n) p.1 * (1 - profZeta α (X n) p.1) *
              (profZeta α (X n) p.2 * (1 - profZeta α (X n) p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2) with hSc
  have hTk3 : ∫ p, (Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ
        Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1))ᶜ.indicator H p
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) < ε3 := hTkk
  have hc1' : Gm n - Sc ≤ ε3 * X n := by
    have : X n * ∫ p, (Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ
        Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1))ᶜ.indicator H p
        ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) ≤ X n * ε3 :=
      mul_le_mul_of_nonneg_left hTk3.le hXn.le
    linarith
  have hSc_nn : 0 ≤ Sc := by
    have := abs_nonneg (Sn - Sc)
    have h2 : 0 ≤ η * Sc := this.trans hcmps
    exact (mul_nonneg_iff_of_pos_left hηpos).1 h2
  have hηSc : η * Sc ≤ ε3 * X n := by
    have h1 : η * Sc ≤ η * (Mb * X n) := mul_le_mul_of_nonneg_left (by linarith [hc0]) hηpos.le
    have h2 : η * (Mb * X n) = (η * Mb) * X n := by ring
    have h3 : (η * Mb) * X n ≤ ε3 * X n := mul_le_mul_of_nonneg_right hηMb hXn.le
    linarith
  have hB1 : |Pn - Gm n| ≤ 3 * (ε3 * X n) := by
    have h1 := abs_le.1 (hcmps.trans hηSc)
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, hs0, hs1, hc0, hc1']
  have hC0 : 0 ≤ Pn0 ∧ Pn0 ≤ Real.pi ^ 2 := by
    unfold CbarPart at hB0
    obtain ⟨h0, h1⟩ := hB0
    have hpi' : 0 < (Real.pi ^ 2)⁻¹ := inv_pos.2 hπ
    constructor
    · exact (mul_nonneg_iff_of_pos_left hpi').1 h0
    · have := (inv_mul_le_iff₀ hπ).1 (by simpa using h1)
      simpa using this
  have e : vPart β (B n) (plSpec α (c n) (N n)) (i n) - profG α β (X n) =
      (1 - (1 / Real.pi ^ 2) * Pn0) + (1 / Real.pi ^ 2) * (Pn - Gm n) := by
    rw [hrep, hGprofG n]; simp only [hPn, hPn0]; ring
  show |vPart β (B n) (plSpec α (c n) (N n)) (i n) - profG α β (X n)| ≤ δ * X n
  rw [e]
  have hp1 : 0 < 1 / Real.pi ^ 2 := by positivity
  have h1 : |1 - (1 / Real.pi ^ 2) * Pn0| ≤ 1 := by
    rw [abs_le]; constructor
    · have : (1 / Real.pi ^ 2) * Pn0 ≤ 1 := by
        rw [one_div, inv_mul_le_iff₀ hπ]; linarith [hC0.2]
      linarith
    · have : 0 ≤ (1 / Real.pi ^ 2) * Pn0 := mul_nonneg hp1.le hC0.1
      linarith
  have h2 : |(1 / Real.pi ^ 2) * (Pn - Gm n)| ≤ 3 / 8 * δ * X n := by
    rw [abs_mul, abs_of_pos hp1]
    calc (1 / Real.pi ^ 2) * |Pn - Gm n| ≤ (1 / Real.pi ^ 2) * (3 * (ε3 * X n)) :=
          mul_le_mul_of_nonneg_left hB1 hp1.le
      _ = 3 / 8 * δ * X n := by rw [hε3]; field_simp
  have hX8' : 8 ≤ δ * X n := by
    have := mul_le_mul_of_nonneg_left hX8 hδ.le
    rwa [mul_div_cancel₀ _ hδ.ne'] at this
  calc |(1 - (1 / Real.pi ^ 2) * Pn0) + (1 / Real.pi ^ 2) * (Pn - Gm n)|
      ≤ |1 - (1 / Real.pi ^ 2) * Pn0| + |(1 / Real.pi ^ 2) * (Pn - Gm n)| := abs_add_le _ _
    _ ≤ δ * X n := by linarith

private lemma pg9_inf_main {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (hBound : volHBound α β N B c)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    IsEquivalent atTop (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => 4 * Kc α / (α - 1) * (rowIdx (i n) / icCross α (B n))) := by
  have hα0 : 0 < α := by linarith
  have hK := vg_K_pos hα1
  set cinf : ℝ := 4 * Kc α / (α - 1) with hcinf
  have hcinf0 : 0 < cinf := by
    rw [hcinf]; have : 0 < α - 1 := by linarith
    positivity
  set X : ℕ → ℝ := fun n => rowIdx (i n) / icCross α (B n) with hXdef
  have hXp : ∀ᶠ n in atTop, 0 < X n := hX.eventually_gt_atTop 0
  have hII := lem_app_pl_supervol_ii_inf hα1 R.hβ0 R.hβ1
  have hGr : Tendsto (fun n => profG α β (X n) / (cinf * X n)) atTop (𝓝 1) := by
    have h := hII.comp_tendsto hX
    refine (isEquivalent_iff_tendsto_one ?_).1 h
    filter_upwards [hXp] with n hn
    exact (mul_pos hcinf0 hn).ne'
  have h0 : Tendsto (fun n => (vPart β (B n) (plSpec α (c n) (N n)) (i n) - profG α β (X n)) /
      (cinf * X n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hδ : 0 < ε * cinf / 2 := by positivity
    filter_upwards [pg9_inf_rel R hα1 hBound i hi hX hx hδ, hXp] with n hn hXn
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (mul_pos hcinf0 hXn), div_lt_iff₀ (mul_pos hcinf0 hXn)]
    have : ε * cinf / 2 * X n < ε * (cinf * X n) := by
      have : 0 < ε * (cinf * X n) := by positivity
      nlinarith
    exact lt_of_le_of_lt hn this
  have h1 := h0.add hGr
  simp only [zero_add] at h1
  refine isEquivalent_of_tendsto_one ?_
  refine h1.congr' ?_
  filter_upwards [hXp] with n hn
  simp only [Pi.div_apply]
  rw [← add_div, sub_add_cancel]
-- PG9-HELPERS-END

/-- `lem:app-pl-supervol`, regime `X → X_0 ∈ (0,∞)` (snapshot `cr-2026-10-23`), with `vPart` for `𝔳_i(0)`
and `X = rowIdx i / icCross α B = i/i_c`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Supercritical volatility]\label{lem:app-pl-supervol}
The function $G_{\alpha,\bmom}$ is finite, positive and continuous on $(0,\infty)$ and satisfies the
two endpoint laws of \cref{eqn:app-pl-crossover-ends}. Under \cref{assum:app-pl-regime}, for
every row sequence $i\to\infty$: if $X\to X_0\in(0,\infty)$ then $\mathfrak v_i(0)\to G_{\alpha,\bmom}(X_0)$; if
$X\to0$ then $\mathfrak v_i(0)\to1/\sw2$; if $X\to\infty$ and $i/N\to0$ then
$\mathfrak v_i(0)\sim\frac{4K_\alpha}{\alpha-1}X$. Moreover $\Gamma_\alpha(x)\sim\frac{4K_\alpha^2}{\alpha-1}x$ as $x\downarrow0$.
\end{lemma}
-/
theorem lem_app_pl_supervol_iii_mid {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (hZero : volHZero α β N B c)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (X0 : ℝ) (hX0 : 0 < X0)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 X0)) :
    Tendsto (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n)) atTop (𝓝 (profG α β X0)) := by
  exact pg9_mid_main R hα1 hZero i hi X0 hX0 hX

/-- `lem:app-pl-supervol`, regime `X → 0` (snapshot `cr-2026-10-23`), with `vPart` for `𝔳_i(0)`. LaTeX,
verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Supercritical volatility]\label{lem:app-pl-supervol}
The function $G_{\alpha,\bmom}$ is finite, positive and continuous on $(0,\infty)$ and satisfies the
two endpoint laws of \cref{eqn:app-pl-crossover-ends}. Under \cref{assum:app-pl-regime}, for
every row sequence $i\to\infty$: if $X\to X_0\in(0,\infty)$ then $\mathfrak v_i(0)\to G_{\alpha,\bmom}(X_0)$; if
$X\to0$ then $\mathfrak v_i(0)\to1/\sw2$; if $X\to\infty$ and $i/N\to0$ then
$\mathfrak v_i(0)\sim\frac{4K_\alpha}{\alpha-1}X$. Moreover $\Gamma_\alpha(x)\sim\frac{4K_\alpha^2}{\alpha-1}x$ as $x\downarrow0$.
\end{lemma}
-/
theorem lem_app_pl_supervol_iii_zero {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n)) atTop (𝓝 (1 / sPow β 2)) := by
  exact pg9_zero_main R hα1 i hi hX

/-- `lem:app-pl-supervol`, regime `X → ∞` with `i/N → 0` (snapshot `cr-2026-10-23`), with `vPart` for
`𝔳_i(0)`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Supercritical volatility]\label{lem:app-pl-supervol}
The function $G_{\alpha,\bmom}$ is finite, positive and continuous on $(0,\infty)$ and satisfies the
two endpoint laws of \cref{eqn:app-pl-crossover-ends}. Under \cref{assum:app-pl-regime}, for
every row sequence $i\to\infty$: if $X\to X_0\in(0,\infty)$ then $\mathfrak v_i(0)\to G_{\alpha,\bmom}(X_0)$; if
$X\to0$ then $\mathfrak v_i(0)\to1/\sw2$; if $X\to\infty$ and $i/N\to0$ then
$\mathfrak v_i(0)\sim\frac{4K_\alpha}{\alpha-1}X$. Moreover $\Gamma_\alpha(x)\sim\frac{4K_\alpha^2}{\alpha-1}x$ as $x\downarrow0$.
\end{lemma}
-/
theorem lem_app_pl_supervol_iii_inf {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (hBound : volHBound α β N B c)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    IsEquivalent atTop (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => 4 * Kc α / (α - 1) * (rowIdx (i n) / icCross α (B n))) := by
  exact pg9_inf_main R hα1 hBound i hi hX hx

/-! ## Private helpers for `thm_app_pl_volatility_iii_part` and `triple_vol_gt_one` (P-G.9.P4) -/

private lemma pg4_regime_comp {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    assum_app_pl_regime α β (N ∘ φ) (B ∘ φ) (c ∘ φ) where
  hα := R.hα
  hβ0 := R.hβ0
  hβ1 := R.hβ1
  hNpos n := R.hNpos (φ n)
  hBpos n := R.hBpos (φ n)
  hcpos n := R.hcpos (φ n)
  hN := R.hN.comp hφ.tendsto_atTop
  hB := R.hB.comp hφ.tendsto_atTop
  hγ := R.hγ.comp hφ.tendsto_atTop

private lemma pg4_zero_of_subseq (u : ℕ → ℝ)
    (h : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (u ∘ φ ∘ ψ) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra hn
  push Not at hn
  have hfreq : ∃ᶠ n in atTop, ¬dist (u n) 0 < ε := by
    rw [frequently_atTop]
    intro N
    obtain ⟨n, hnN, hnε⟩ := hn N
    exact ⟨n, hnN, not_lt_of_ge hnε⟩
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ψ, hψ, hlim⟩ := h φ hφ
  have hev := (Metric.tendsto_atTop.1 hlim) ε hε
  obtain ⟨n, hn⟩ := hev
  exact hbad (ψ n) (hn n le_rfl)

private lemma pg4_unif_of_seq {ι : ℕ → Type} {cond : ∀ n, ι n → Prop} {F : ∀ n, ι n → ℝ}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ z : ∀ k, ι (φ k), (∀ k, cond (φ k) (z k)) →
      Tendsto (fun k => |F (φ k) (z k)|) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : ι n, cond n i → |F n i| ≤ ε := by
  intro ε hε
  by_contra hcon
  have hfreq : ∃ᶠ n in atTop, ∃ i : ι n, cond n i ∧ ε < |F n i| := by
    refine (Filter.not_eventually.1 hcon).mono ?_
    intro n hn
    push_neg at hn
    exact hn
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose z hz1 hz2 using hφP
  have hT := h φ hφ z hz1
  have hev : ∀ᶠ k in atTop, |F (φ k) (z k)| < ε :=
    (Metric.tendsto_nhds.1 hT ε hε).mono (fun k hk => by simpa [abs_abs] using hk)
  obtain ⟨k, hk⟩ := hev.exists
  linarith [hz2 k]

private lemma pg4_bdd_or_subseq (u : ℕ → ℝ) :
    (∃ L : ℝ, ∀ᶠ n in atTop, u n ≤ L) ∨
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop atTop := by
  by_cases hb : ∃ L : ℝ, ∀ᶠ n in atTop, u n ≤ L
  · exact Or.inl hb
  · right
    have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop, (k : ℝ) < u n := by
      intro k
      by_contra hk
      have hev : ∀ᶠ n in atTop, ¬(k : ℝ) < u n := not_frequently.1 hk
      apply hb
      exact ⟨k, hev.mono fun n hn => le_of_not_gt hn⟩
    obtain ⟨φ, hφ, hlarge⟩ := extraction_forall_of_frequently hfreq
    refine ⟨φ, hφ, ?_⟩
    exact tendsto_atTop_mono' atTop (Eventually.of_forall fun n => (hlarge n).le)
      tendsto_natCast_atTop_atTop

private lemma pg4_rowFrac_bounds {N : ℕ} (i : Fin N) : 0 < rowFrac i ∧ rowFrac i ≤ 1 := by
  have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hi : (0:ℝ) < rowIdx i := by unfold rowIdx; positivity
  refine ⟨by unfold rowFrac; positivity, ?_⟩
  unfold rowFrac
  rw [div_le_one hNr]
  unfold rowIdx
  have := i.isLt
  have : ((i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast this
  exact this

private lemma pg4_equiv_of_subseq {v w : ℕ → ℝ} (hw : ∀ n, w n ≠ 0)
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      IsEquivalent atTop (v ∘ φ ∘ ψ) (w ∘ φ ∘ ψ)) : IsEquivalent atTop v w := by
  rw [isEquivalent_iff_tendsto_one (Eventually.of_forall hw)]
  have h0 : Tendsto (fun n => v n / w n - 1) atTop (𝓝 0) := by
    apply pg4_zero_of_subseq
    intro φ hφ
    obtain ⟨ψ, hψ, he⟩ := h φ hφ
    refine ⟨ψ, hψ, ?_⟩
    have h1 := (isEquivalent_iff_tendsto_one
      (Eventually.of_forall fun k => hw (φ (ψ k)))).1 he
    have h2 := h1.sub_const 1
    simpa [Function.comp_def] using h2
  have h3 := h0.add_const 1
  simpa [Pi.div_def] using h3

private lemma pg4_Kc_pos {α : ℝ} (hα1 : 1 < α) : 0 < Kc α := pg9_Kc_pos hα1

private lemma pg4_X_pos {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (i : ∀ n, Fin (N n)) (n : ℕ) :
    0 < rowIdx (i n) / icCross α (B n) := by
  have hB : (0:ℝ) < B n := by exact_mod_cast R.hBpos n
  have hK := pg4_Kc_pos hα1
  have : 0 < rowIdx (i n) := by unfold rowIdx; positivity
  unfold icCross
  positivity

private lemma pg4_gamma_pos {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (n : ℕ) : 0 < gammaOf (N n) (B n) := by
  unfold gammaOf
  exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)

private lemma pg4_Xeq {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (i : ∀ n, Fin (N n)) (n : ℕ) :
    rowIdx (i n) / icCross α (B n) = Kc α * gammaOf (N n) (B n) * rowFrac (i n) := by
  have hB : (B n : ℝ) ≠ 0 := by exact_mod_cast (R.hBpos n).ne'
  have hN : (N n : ℝ) ≠ 0 := by exact_mod_cast (R.hNpos n).ne'
  have hK : Kc α ≠ 0 := (pg4_Kc_pos hα1).ne'
  unfold rowFrac icCross gammaOf
  field_simp

private lemma pg4_vhat_pos {α β : ℝ} (hα1 : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    {N : ℕ} (B : ℕ) (hB : 0 < B) (i : Fin N) (hX : True) :
    0 < vhatSuper β α B i := by
  have hG : 0 < profG α β (rowIdx i / icCross α B) := by
    apply lem_app_pl_supervol_i_pos hα1 hβ0 hβ1
    have hB' : (0:ℝ) < B := by exact_mod_cast hB
    have hK := pg4_Kc_pos hα1
    have : 0 < rowIdx i := by unfold rowIdx; positivity
    unfold icCross
    positivity
  have hΓ := lem_app_pl_Gamma_helper_pos (by linarith : 0 < α) _
    ⟨(pg4_rowFrac_bounds i).1, (pg4_rowFrac_bounds i).2⟩
  have hK := pg4_Kc_pos hα1
  have hα' : 0 < α - 1 := by linarith
  have hr := (pg4_rowFrac_bounds i).1
  unfold vhatSuper
  positivity

private lemma pg4_Q_tendsto {α : ℝ} (hα1 : 1 < α) (rf : ℕ → ℝ)
    (hrf : Tendsto rf atTop (𝓝 0)) (hpos : ∀ n, 0 < rf n) :
    Tendsto (fun n => profGamma α (rf n) / (4 * Kc α ^ 2 * rf n / (α - 1))) atTop (𝓝 1) := by
  have hK := pg4_Kc_pos hα1
  have hα' : 0 < α - 1 := by linarith
  have hG := (lem_app_pl_supervol_iv_gamma hα1).comp_tendsto
    (k := rf) (tendsto_nhdsWithin_iff.2 ⟨hrf, Eventually.of_forall hpos⟩)
  have hne : ∀ᶠ n in atTop, (fun x : ℝ => 4 * Kc α ^ 2 / (α - 1) * x) (rf n) ≠ 0 :=
    Eventually.of_forall fun n => by have := hpos n; positivity
  have h1 := (isEquivalent_iff_tendsto_one hne).1 hG
  refine h1.congr (fun n => ?_)
  have := (hpos n).ne'
  simp only [Pi.div_apply, Function.comp_apply]
  field_simp

private lemma pg4_equiv_bulk {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (hBound : volHBound α β N B c)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop atTop) :
    IsEquivalent atTop (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n))) := by
  have hα0 : 0 < α := by linarith
  have hw : ∀ n, gammaOf (N n) (B n) * profGamma α (rowFrac (i n)) ≠ 0 := fun n =>
    (mul_pos (pg4_gamma_pos R n) (lem_app_pl_Gamma_helper_pos hα0 _
      ⟨(pg4_rowFrac_bounds _).1, (pg4_rowFrac_bounds _).2⟩)).ne'
  apply pg4_equiv_of_subseq hw
  intro φ hφ
  have hxmem : ∀ k, rowFrac (i (φ k)) ∈ Icc (0:ℝ) 1 := fun k =>
    ⟨(pg4_rowFrac_bounds (i (φ k))).1.le, (pg4_rowFrac_bounds (i (φ k))).2⟩
  obtain ⟨x, hxI, χ, hχ, hx⟩ := isCompact_Icc.tendsto_subseq hxmem
  refine ⟨χ, hχ, ?_⟩
  have hθ : StrictMono (φ ∘ χ) := hφ.comp hχ
  rcases eq_or_lt_of_le hxI.1 with hx0 | hx0
  · subst hx0
    have R'' := pg4_regime_comp R hθ
    have hB'' : volHBound α β (N ∘ φ ∘ χ) (B ∘ φ ∘ χ) (c ∘ φ ∘ χ) :=
      fun k q ℓ => hBound (φ (χ k)) q ℓ
    have hj : Tendsto (fun k => rowIdx (i (φ (χ k)))) atTop atTop := hi.comp hθ.tendsto_atTop
    have hXj : Tendsto (fun k => rowIdx (i (φ (χ k))) / icCross α (B (φ (χ k)))) atTop atTop :=
      hX.comp hθ.tendsto_atTop
    have h1 := lem_app_pl_supervol_iii_inf R'' hα1 hB'' (fun k => i (φ (χ k))) hj hXj hx
    have hG := (lem_app_pl_supervol_iv_gamma hα1).comp_tendsto
      (k := fun k => rowFrac (i (φ (χ k))))
      (tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall fun k => (pg4_rowFrac_bounds _).1⟩)
    have h2 := IsEquivalent.mul
      (IsEquivalent.refl (u := fun k => gammaOf (N (φ (χ k))) (B (φ (χ k)))) (l := atTop)) hG
    have h3 : IsEquivalent atTop
        (fun k => gammaOf (N (φ (χ k))) (B (φ (χ k))) * profGamma α (rowFrac (i (φ (χ k)))))
        (fun k => 4 * Kc α / (α - 1) * (rowIdx (i (φ (χ k))) / icCross α (B (φ (χ k))))) := by
      refine (h2.congr_left (Eventually.of_forall fun k => rfl)).congr_right
        (Eventually.of_forall fun k => ?_)
      have hB : (B (φ (χ k)) : ℝ) ≠ 0 := by exact_mod_cast (R.hBpos _).ne'
      have hN : (N (φ (χ k)) : ℝ) ≠ 0 := by exact_mod_cast (R.hNpos _).ne'
      have hK : Kc α ≠ 0 := (pg4_Kc_pos hα1).ne'
      have hα' : α - 1 ≠ 0 := by intro h; linarith
      simp only [Pi.mul_apply, Function.comp_apply]
      unfold rowFrac icCross gammaOf
      field_simp
    exact h1.trans h3.symm
  · have hcont := lem_app_pl_Gamma_helper_cont hα0 x ⟨hx0, hxI.2⟩
    have hrfIoc : ∀ k, rowFrac (i (φ (χ k))) ∈ Ioc (0:ℝ) 1 := fun k =>
      ⟨(pg4_rowFrac_bounds _).1, (pg4_rowFrac_bounds _).2⟩
    have hΓ : Tendsto (fun k => profGamma α (rowFrac (i (φ (χ k))))) atTop
        (𝓝 (profGamma α x)) :=
      hcont.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall hrfIoc⟩)
    have hΓx : 0 < profGamma α x := lem_app_pl_Gamma_helper_pos hα0 x ⟨hx0, hxI.2⟩
    have hu := (thm_app_pl_volatility_i_part R hBound).2 (Icc (x / 2) 1)
      (fun t ht => ⟨by linarith [ht.1], ht.2⟩) isCompact_Icc
    have hmem : ∀ᶠ k in atTop, rowFrac (i (φ (χ k))) ∈ Icc (x / 2) 1 := by
      have : ∀ᶠ k in atTop, x / 2 < rowFrac (i (φ (χ k))) :=
        hx.eventually (lt_mem_nhds (by linarith))
      exact this.mono fun k hk => ⟨hk.le, (pg4_rowFrac_bounds _).2⟩
    have herr : Tendsto (fun k => vPart β (B (φ (χ k))) (plSpec α (c (φ (χ k))) (N (φ (χ k))))
        (i (φ (χ k))) / gammaOf (N (φ (χ k))) (B (φ (χ k))) -
          profGamma α (rowFrac (i (φ (χ k))))) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have h1 := (hu (ε / 2) (by linarith)).filter_mono hθ.tendsto_atTop
      filter_upwards [h1, hmem] with k hk1 hk2
      have := hk1 (i (φ (χ k))) hk2
      rw [Real.dist_eq, sub_zero]
      have this' : |vPart β (B (φ (χ k))) (plSpec α (c (φ (χ k))) (N (φ (χ k))))
          (i (φ (χ k))) / gammaOf (N (φ (χ k))) (B (φ (χ k))) -
            profGamma α (rowFrac (i (φ (χ k))))| ≤ ε / 2 := this
      exact lt_of_le_of_lt this' (by linarith)
    have hv : Tendsto (fun k => vPart β (B (φ (χ k))) (plSpec α (c (φ (χ k))) (N (φ (χ k))))
        (i (φ (χ k))) / gammaOf (N (φ (χ k))) (B (φ (χ k)))) atTop (𝓝 (profGamma α x)) := by
      have := herr.add hΓ
      simpa using this
    have hr := hv.div hΓ hΓx.ne'
    rw [div_self hΓx.ne'] at hr
    show IsEquivalent atTop
      (fun k => vPart β (B (φ (χ k))) (plSpec α (c (φ (χ k))) (N (φ (χ k)))) (i (φ (χ k))))
      (fun k => gammaOf (N (φ (χ k))) (B (φ (χ k))) * profGamma α (rowFrac (i (φ (χ k)))))
    rw [isEquivalent_iff_tendsto_one (Eventually.of_forall fun k => hw (φ (χ k)))]
    refine hr.congr (fun k => ?_)
    simp only [Pi.div_apply, Function.comp_apply]
    rw [div_div]

private lemma pg4_vhat_decomp {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (i : ∀ n, Fin (N n)) (n : ℕ) :
    vhatSuper β α (B n) (i n) = profG α β (rowIdx (i n) / icCross α (B n)) *
      (profGamma α (rowFrac (i n)) / (4 * Kc α ^ 2 * rowFrac (i n) / (α - 1))) := by
  unfold vhatSuper
  rw [mul_div_assoc]

private lemma pg4_sPow_ne {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 1 / sPow β 2 ≠ 0 := by
  rw [sPow_two hβ0.le hβ1]
  have : 0 < (1 + β) / (1 - β) := div_pos (by linarith) (by linarith)
  have h2 : (0:ℝ) < 1 / ((1 - β) / (1 + β)) := by
    apply one_div_pos.2
    exact div_pos (by linarith) (by linarith)
  exact h2.ne'

private lemma pg4_T_lim {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α)
    (i : ∀ n, Fin (N n)) (L : ℝ)
    (hv : Tendsto (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n)) atTop (𝓝 L))
    (hG : Tendsto (fun n => profG α β (rowIdx (i n) / icCross α (B n))) atTop (𝓝 L))
    (hL : L ≠ 0)
    {X0 : ℝ}
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 X0)) :
    IsEquivalent atTop (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => vhatSuper β α (B n) (i n)) := by
  have hrf := pg9_rowFrac_zero_of_X_tendsto R hα1 i hX
  have hQ := pg4_Q_tendsto hα1 (fun n => rowFrac (i n)) hrf (fun n => (pg4_rowFrac_bounds _).1)
  have hw := hG.mul hQ
  rw [mul_one] at hw
  have h1 := (isEquivalent_const_iff_tendsto hL).2 hv
  have h2 := (isEquivalent_const_iff_tendsto hL).2
    (hw.congr (fun n => (pg4_vhat_decomp (β := β) (α := α) (B := B) (c := c) i n).symm))
  exact h1.trans h2.symm

private lemma pg4_T_inf {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (hBound : volHBound α β N B c)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hX : Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop atTop) :
    IsEquivalent atTop (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => vhatSuper β α (B n) (i n)) := by
  have h1 := pg4_equiv_bulk R hα1 hBound i hi hX
  have hGe := (lem_app_pl_supervol_ii_inf hα1 R.hβ0 R.hβ1).comp_tendsto hX
  have h2 := IsEquivalent.mul hGe
    (IsEquivalent.refl (u := fun n => profGamma α (rowFrac (i n)) /
      (4 * Kc α ^ 2 * rowFrac (i n) / (α - 1))) (l := atTop))
  have h3 : IsEquivalent atTop
      (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n)))
      (fun n => vhatSuper β α (B n) (i n)) := by
    have h4 := h2.symm
    refine (h4.congr_left (Eventually.of_forall fun n => ?_)).congr_right
      (Eventually.of_forall fun n => ?_)
    · have hK : Kc α ≠ 0 := (pg4_Kc_pos hα1).ne'
      have hα' : α - 1 ≠ 0 := by intro h; linarith
      have hr : rowFrac (i n) ≠ 0 := (pg4_rowFrac_bounds _).1.ne'
      simp only [Pi.mul_apply, Function.comp_apply]
      rw [pg4_Xeq R hα1 i n]
      field_simp
    · simp only [Pi.mul_apply, Function.comp_apply]
      exact (pg4_vhat_decomp (β := β) (α := α) (B := B) (c := c) i n).symm
  exact h1.trans h3

private lemma pg4_equiv_vhat {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α)
    (hBound : volHBound α β N B c) (hZero : volHZero α β N B c)
    (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop) :
    IsEquivalent atTop (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => vhatSuper β α (B n) (i n)) := by
  apply pg4_equiv_of_subseq (fun n => (pg4_vhat_pos hα1 R.hβ0 R.hβ1 (B n) (R.hBpos n) (i n) trivial).ne')
  intro φ hφ
  rcases pg4_bdd_or_subseq (fun k => rowIdx (i (φ k)) / icCross α (B (φ k))) with
    ⟨L, hL⟩ | ⟨χ, hχ, hχtop⟩
  · have hmem : ∃ᶠ k in atTop, rowIdx (i (φ k)) / icCross α (B (φ k)) ∈ Icc 0 L :=
      (hL.mono fun k hk => ⟨(pg4_X_pos R hα1 i (φ k)).le, hk⟩).frequently
    obtain ⟨X0, hX0, χ, hχ, hX⟩ := tendsto_subseq_of_frequently_bounded
      (Metric.isBounded_Icc 0 L) hmem
    rw [isClosed_Icc.closure_eq] at hX0
    refine ⟨χ, hχ, ?_⟩
    have hθ : StrictMono (φ ∘ χ) := hφ.comp hχ
    have R'' := pg4_regime_comp R hθ
    have hj : Tendsto (fun k => rowIdx (i (φ (χ k)))) atTop atTop := hi.comp hθ.tendsto_atTop
    have hXj : Tendsto (fun k => rowIdx (i (φ (χ k))) / icCross α (B (φ (χ k)))) atTop (𝓝 X0) :=
      hX
    rcases eq_or_lt_of_le hX0.1 with h0 | h0
    · subst h0
      have hv := lem_app_pl_supervol_iii_zero R'' hα1 (fun k => i (φ (χ k))) hj hXj
      have hG := (lem_app_pl_supervol_ii_zero hα1 R.hβ0 R.hβ1).comp
        (tendsto_nhdsWithin_iff.2 ⟨hXj, Eventually.of_forall fun k =>
          pg4_X_pos R'' hα1 (fun k => i (φ (χ k))) k⟩)
      exact pg4_T_lim R'' hα1 (fun k => i (φ (χ k))) _ hv hG (pg4_sPow_ne R.hβ0 R.hβ1) hXj
    · have hZ'' : volHZero α β (N ∘ φ ∘ χ) (B ∘ φ ∘ χ) (c ∘ φ ∘ χ) :=
        fun k q => hZero (φ (χ k)) q
      have hv := lem_app_pl_supervol_iii_mid R'' hα1 hZ'' (fun k => i (φ (χ k))) hj X0 h0 hXj
      have hG := ((lem_app_pl_supervol_i_cont hα1 R.hβ0 R.hβ1).continuousAt
        (Ioi_mem_nhds h0)).tendsto.comp hXj
      have hGpos := lem_app_pl_supervol_i_pos hα1 R.hβ0 R.hβ1 X0 h0
      exact pg4_T_lim R'' hα1 (fun k => i (φ (χ k))) _ hv hG hGpos.ne' hXj
  · refine ⟨χ, hχ, ?_⟩
    have hθ : StrictMono (φ ∘ χ) := hφ.comp hχ
    have R'' := pg4_regime_comp R hθ
    have hB'' : volHBound α β (N ∘ φ ∘ χ) (B ∘ φ ∘ χ) (c ∘ φ ∘ χ) :=
      fun k q ℓ => hBound (φ (χ k)) q ℓ
    exact pg4_T_inf R'' hα1 hB'' (fun k => i (φ (χ k))) (hi.comp hθ.tendsto_atTop) hχtop

/-- `thm:app-pl-volatility`, part (iii) (supercritical), in part-form (snapshot `cr-2026-10-23`). The four
conjuncts are, in order: the regime `X → X_0 ∈ (0,∞)`; `X → 0`; `X → ∞` with the bulk approximant
`γΓ_α(i/N)`; and `X → ∞` with `i/N → 0` and the endpoint `4K_α²/(α-1)·i/B`. The first two are
`lem_app_pl_supervol_iii_mid`, `_iii_zero`; the third uses part (i) (`thm_app_pl_volatility_i_part`) for
`i/N` away from zero and `lem_app_pl_supervol_iii_inf` after passing to subsequences; the fourth is the
endpoint of `lem_app_pl_supervol_iii_inf`. The statement is sequential, as in the source. LaTeX, verbatim
from `sections/06-power-law/section.tex` (whole theorem; this declaration states part (iii) only):

\begin{theorem}[Volatility crossover and bulk profile]\label{thm:app-pl-volatility}
Assume \cref{assum:app-pl-regime} and let $i=i_N$ be a row sequence.
\begin{enumerate}[label=(\roman*)]
\item (Bulk.) If $i/N\to x\in(0,1]$ and $\ell=\ell_N$ are integers with
$\ell/\gamma\to\tau\in(0,1)$, then
\[
\overline C_{i,\ell}(0)\longrightarrow C_{\alpha,x}(\tau),\qquad \frac{\mathfrak v_i(0)}{\gamma}\longrightarrow\Gamma_\alpha(x),
\]
locally uniformly in $x\in(0,1]$ and $\tau\in(0,1)$.
\item Let $0<\alpha\le1$, let $i\to\infty$, and put
\begin{equation}\label{eqn:app-pl-icv}
i_{\mathrm c,\mathfrak v}\defeq c_0^{2/\alpha}\,i_{\mathrm c,\mathfrak d}=\begin{cases}N\big[(1-\alpha)/(\sw2\gamma\log^2\gamma)\big]^{1/\alpha},&\alpha<1,\\ 9B/(4\sw2\log^3\gamma),&\alpha=1.\end{cases}
\end{equation}
If $i/i_{\mathrm c,\mathfrak v}\to y\in(0,\infty)$, then
$\sw2\,\mathfrak v_i(0)\to1+2c_0y^{\alpha/2}+y^\alpha$, uniformly for $y$ in compact subsets of
$(0,\infty)$. If $i/i_{\mathrm c,\mathfrak v}\to0$, then $\mathfrak v_i(0)\to1/\sw2$. If
$i/i_{\mathrm c,\mathfrak v}\to\infty$, then $\mathfrak v_i(0)\sim\gamma\Gamma_\alpha(i/N)$, and if moreover
$i/N\to0$,
\[
\mathfrak v_i(0)\sim\frac{\gamma(i/N)^\alpha\big[\log((N/i)^\alpha)\big]^2}{1-\alpha}\quad(\alpha<1),\qquad
\mathfrak v_i(0)\sim\frac49\,\frac iB\,\big[\log(N/i)\big]^3\quad(\alpha=1).
\]
\item Let $\alpha>1$ and $i\to\infty$. If $i/i_{\mathrm c}\to X_0\in(0,\infty)$, then
$\mathfrak v_i(0)\to G_{\alpha,\bmom}(X_0)$. If $i/i_{\mathrm c}\to0$, then $\mathfrak v_i(0)\to1/\sw2$. If
$i/i_{\mathrm c}\to\infty$, then $\mathfrak v_i(0)\sim\gamma\Gamma_\alpha(i/N)$, and if moreover $i/N\to0$,
\[
\mathfrak v_i(0)\sim\frac{4K_\alpha^2}{\alpha-1}\,\frac iB .
\]
\end{enumerate}
\end{theorem}
-/
theorem thm_app_pl_volatility_iii_part {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α)
    (hBound : volHBound α β N B c) (hZero : volHZero α β N B c) :
    ∀ i : ∀ n, Fin (N n), Tendsto (fun n => rowIdx (i n)) atTop atTop →
      (∀ X0 : ℝ, 0 < X0 → Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 X0) →
        Tendsto (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n)) atTop (𝓝 (profG α β X0))) ∧
      (Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 0) →
        Tendsto (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n)) atTop (𝓝 (1 / sPow β 2))) ∧
      (Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop atTop →
        IsEquivalent atTop (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n)))) ∧
      (Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop atTop →
        Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0) →
        IsEquivalent atTop (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => 4 * Kc α ^ 2 / (α - 1) * (rowIdx (i n) / (B n : ℝ)))) := by
  intro i hi
  refine ⟨fun X0 hX0 hX => lem_app_pl_supervol_iii_mid R hα1 hZero i hi X0 hX0 hX,
    fun hX => lem_app_pl_supervol_iii_zero R hα1 i hi hX,
    fun hX => pg4_equiv_bulk R hα1 hBound i hi hX, fun hX hx => ?_⟩
  refine (lem_app_pl_supervol_iii_inf R hα1 hBound i hi hX hx).congr_right
    (Eventually.of_forall fun n => ?_)
  have hB : (B n : ℝ) ≠ 0 := by exact_mod_cast (R.hBpos n).ne'
  have hK : Kc α ≠ 0 := (pg4_Kc_pos hα1).ne'
  have hα' : α - 1 ≠ 0 := by intro h; linarith
  unfold icCross
  field_simp

/-! ## The volatility half of `thm:app-pl-triple` for `α > 1` -/

/-- `triple_vol_gt_one` (card §5, L-G.9; helper). The volatility half for `1 < α` of `thm:app-pl-triple`
(snapshot `cr-2026-10-23`), with the super approximant `vhatSuper`. LaTeX, verbatim from
`sections/06-power-law/section.tex`:

\begin{theorem}[The coefficient pair]\label{thm:app-pl-triple}
Under \cref{assum:app-pl-regime}, for every sequence of integers $1\le n_N\le N$
with $n_N\to\infty$,
\begin{equation}\label{eqn:app-pl-triple}
\sup_{n_N\le i\le N}\max\Big\{\Big|\frac{\mathfrak d_i(0)}{\widehat{\mathfrak d}_i}-1\Big|,\ \Big|\frac{\mathfrak v_i(0)}{\widehat{\mathfrak v}_i}-1\Big|\Big\}\longrightarrow0 .
\end{equation}
\end{theorem}

Lean form of the supremum: for every `ε > 0`, eventually in `n`, every row `i ≥ nn n` (1-based) satisfies the
bound, as in `triple_vol_le_one`. -/
theorem triple_vol_gt_one {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α)
    (hBound : volHBound α β N B c) (hZero : volHZero α β N B c)
    (nn : ℕ → ℕ) (hnn : ∀ᶠ n in atTop, 1 ≤ nn n ∧ nn n ≤ N n)
    (hnnTop : Tendsto nn atTop atTop) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : Fin (N n), nn n ≤ (i : ℕ) + 1 →
      |vPart β (B n) (plSpec α (c n) (N n)) i / vhatSuper β α (B n) i - 1| ≤ ε := by
  intro ε hε
  apply pg4_unif_of_seq (ι := fun n => Fin (N n))
    (cond := fun n i => nn n ≤ (i : ℕ) + 1)
    (F := fun n i => vPart β (B n) (plSpec α (c n) (N n)) i /
      vhatSuper β α (B n) i - 1) ?_ ε hε
  intro φ hφ z hz
  have R' := pg4_regime_comp R hφ
  have hnn' : Tendsto (nn ∘ φ) atTop atTop := hnnTop.comp hφ.tendsto_atTop
  have hcast : Tendsto (fun k => ((nn (φ k) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnn'
  have hi : Tendsto (fun k => rowIdx (z k)) atTop atTop :=
    tendsto_atTop_mono' atTop (Eventually.of_forall fun k => by
      have hk := hz k
      change (nn (φ k) : ℝ) ≤ ((z k : ℕ) : ℝ) + 1
      exact_mod_cast hk) hcast
  have hB' : volHBound α β (N ∘ φ) (B ∘ φ) (c ∘ φ) := fun k q ℓ => hBound (φ k) q ℓ
  have hZ' : volHZero α β (N ∘ φ) (B ∘ φ) (c ∘ φ) := fun k q => hZero (φ k) q
  have heq := pg4_equiv_vhat R' hα1 hB' hZ' z hi
  have hratio := (isEquivalent_iff_tendsto_one (Eventually.of_forall fun k =>
    (pg4_vhat_pos hα1 R.hβ0 R.hβ1 (B (φ k)) (R.hBpos (φ k)) (z k) trivial).ne')).1 heq
  have herr := (hratio.sub_const 1).abs
  have h0 : |(1:ℝ) - 1| = 0 := by simp
  rw [h0] at herr
  exact herr

end Muon.PowerLaw

end

import Muon.PowerLaw.VolKernel
import Muon.PowerLaw.Profiles
import Muon.PowerLaw.VolShell

/-!
# Appendix G: bulk volatility profile, part-form (work package L-G.7)

Snapshot `cr-2026-10-23`. Source: `sections/06-power-law/section.tex`, `thm:app-pl-volatility`
(l.911-940), part (i) only ("Bulk"). Parts (ii) and (iii) belong to L-G.8 and L-G.9. Card:
`sections/06-power-law/CARD.md` §2, §3, §5 (L-G.7), §6 #1.

Representation choices:

* Part-form. The coefficients are `CbarPart` and `vPart` of `Muon.PowerLaw.VolKernel` (the
  participation-form integrals, card §2 helpers). `vPart` stands in for `𝔳_i(0)`; the identification
  with the limits `C̄_{i,ℓ}(0)`, `𝔳_i(0)` is `prop:app-pl-vol-zero`(iii) (L-G.13), not this file.
* Hypothesis `hBound` (card §5, `0 ≤ C̄_{i,ℓ}(0) ≤ 1`, the source's l.2260) is an explicit
  hypothesis, for every row and every lag. It is discharged in L-G.13.
* Uniformity (card §6 #1, a clarifying item resolved by the interface). The source's
  "$i/N\to x$, locally uniformly in $x$" is not a statement about a single row sequence. The
  statement is the uniform form: for every compact `K ⊆ (0,1]` and compact `L ⊆ (0,1)`, the
  supremum over rows with `i/N ∈ K` and lags with `ℓ/γ ∈ L` of the error tends to zero. In the
  `∀ ε > 0, ∀ᶠ n, ∀ i, ∀ ℓ` form. The sequential form of the source follows from it.
* Row `i : Fin (N n)` is 1-based as `((i : ℕ) : ℝ) + 1` (the convention of `rowNum` in
  `DriftAsymptotics`, which is not imported here, so the expression is written out).
* The Stein lemma used by the proof is `Muon.Foundations.gaussian_stein` (proved in
  `Foundations/Gaussian.lean`), so this file uses no `Muon.External` certificate.
* `profC`, `profGamma` are `C_{α,x}(τ)` and `Γ_α(x)` of `Muon.PowerLaw.Profiles`, reused.
* No definition in this file. The statement is a single theorem with two conjuncts.
-/

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set Asymptotics

noncomputable section

namespace Muon.PowerLaw

/-- Sequential-to-uniform: if along every subsequence and every choice of admissible indices the
error tends to zero, then the error is eventually uniformly small over admissible indices. -/
private lemma vb_unif_of_seq {ι : ℕ → Type} {cond : ∀ n, ι n → Prop} {F : ∀ n, ι n → ℝ}
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
  have hev : ∀ᶠ k in atTop, |F (φ k) (z k)| < ε := (Metric.tendsto_nhds.1 hT) ε hε |>.mono
    (fun k hk => by simpa [abs_abs] using hk)
  obtain ⟨k, hk⟩ := hev.exists
  linarith [hz2 k]

/-- Passing to an increasing subsequence preserves the power-law regime. -/
private lemma vb_regime_subseq {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    assum_app_pl_regime α β (N ∘ φ) (B ∘ φ) (c ∘ φ) := by
  exact ⟨R.hα, R.hβ0, R.hβ1, fun n => R.hNpos (φ n),
    fun n => R.hBpos (φ n), fun n => R.hcpos (φ n),
    R.hN.comp hφ.tendsto_atTop, R.hB.comp hφ.tendsto_atTop,
    R.hγ.comp hφ.tendsto_atTop⟩

/-- A sequential limit on a compact parameter set gives a uniform approximation to a
continuous profile, even when the finite index types depend on the dimension. -/
private lemma vb_compact_uniform {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {ι : ℕ → Type} (K : Set X) (hK : IsCompact K) (u : ∀ n, ι n → X)
    (A : ∀ n, ι n → ℝ) (f : X → ℝ) (hf : ContinuousOn f K)
    (hseq : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ z : ∀ k, ι (φ k),
      (∀ k, u (φ k) (z k) ∈ K) → ∀ x ∈ K,
      Tendsto (fun k => u (φ k) (z k)) atTop (𝓝 x) →
      Tendsto (fun k => A (φ k) (z k)) atTop (𝓝 (f x))) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ z : ι n, u n z ∈ K → |A n z - f (u n z)| ≤ ε := by
  intro ε hε
  by_contra hcon
  have hfreq : ∃ᶠ n in atTop, ∃ z : ι n, u n z ∈ K ∧ ε < |A n z - f (u n z)| := by
    refine (Filter.not_eventually.1 hcon).mono ?_
    intro n hn
    push Not at hn
    exact hn
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose z hzK hzerr using hφP
  obtain ⟨x, hxK, ψ, hψ, hψx⟩ := hK.tendsto_subseq hzK
  have hlim := hseq (φ ∘ ψ) (hφ.comp hψ) (fun k => z (ψ k))
    (fun k => hzK (ψ k)) x hxK hψx
  have hprof : Tendsto (fun k => f (u (φ (ψ k)) (z (ψ k)))) atTop (𝓝 (f x)) :=
    (hf x hxK).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hψx, Filter.Eventually.of_forall (fun k => hzK (ψ k))⟩)
  have herr : Tendsto (fun k => |A (φ (ψ k)) (z (ψ k)) -
      f (u (φ (ψ k)) (z (ψ k)))|) atTop (𝓝 0) := by
    simpa using (hlim.sub hprof).abs
  have hev : ∀ᶠ k in atTop, |A (φ (ψ k)) (z (ψ k)) -
      f (u (φ (ψ k)) (z (ψ k)))| < ε :=
    (Metric.tendsto_nhds.1 herr ε hε).mono (fun k hk => by simpa [abs_abs] using hk)
  obtain ⟨k, hk⟩ := hev.exists
  exact (not_lt_of_ge hk.le) (hzerr (ψ k))

/-- A compact lag set stays uniformly away from both endpoints. -/
private lemma vb_lag_compact (L : Set ℝ) (hL : L ⊆ Ioo 0 1) (hLc : IsCompact L) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ L ⊆ Icc η (1 - η) := by
  rcases L.eq_empty_or_nonempty with h | h
  · exact ⟨1 / 4, by norm_num, by norm_num, by simp [h]⟩
  obtain ⟨a, ha, hamin⟩ := hLc.exists_isMinOn h continuousOn_id
  obtain ⟨b, hb, hbmax⟩ := hLc.exists_isMaxOn h continuousOn_id
  refine ⟨min a (1 - b) / 2, half_pos (lt_min (hL ha).1 (by linarith [(hL hb).2])),
    ?_, ?_⟩
  · have := min_le_left a (1 - b)
    linarith [(hL ha).2]
  · intro p hp
    have hmin := min_le_left a (1 - b)
    have hmax := min_le_right a (1 - b)
    have hpmin := isMinOn_iff.1 hamin p hp
    have hpmax := isMaxOn_iff.1 hbmax p hp
    dsimp only [id] at hpmin hpmax
    constructor <;> linarith [(hL ha).1, (hL hb).2]

/-- Joint continuity on the compact row and lag sets appearing in the target. -/
private lemma vb_profile_continuous {α : ℝ} (hα : 0 < α)
    (K L : Set ℝ) (hK : K ⊆ Ioc 0 1) (hKc : IsCompact K)
    (hL : L ⊆ Ioo 0 1) (hLc : IsCompact L) :
    ContinuousOn (fun q : ℝ × ℝ => profC α q.1 q.2) (K ×ˢ L) := by
  obtain ⟨η, hη0, hη1, hηL⟩ := vb_lag_compact L hL hLc
  exact (profC_continuousOn hα K hK hKc hη0 hη1).mono
    (fun _ hq => ⟨hq.1, hηL hq.2⟩)

/-- The first uniform conclusion reduces to the full, unrestricted sequential bulk limit. -/
private lemma vb_bulk_uniform_of_seq {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (hseq : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ (i : ∀ k, Fin (N (φ k))) (ℓ : ℕ → ℤ),
      ∀ x ∈ Ioc (0 : ℝ) 1, ∀ τ ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun k => rowFrac (i k)) atTop (𝓝 x) →
      Tendsto (fun k => (ℓ k : ℝ) / gammaOf (N (φ k)) (B (φ k))) atTop (𝓝 τ) →
      Tendsto (fun k => CbarPart β (B (φ k)) (plSpec α (c (φ k)) (N (φ k))) (i k) (ℓ k))
        atTop (𝓝 (profC α x τ))) :
    ∀ K : Set ℝ, K ⊆ Ioc 0 1 → IsCompact K → ∀ L : Set ℝ, L ⊆ Ioo 0 1 → IsCompact L →
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (N n)) (ℓ : ℤ),
        rowFrac i ∈ K → (ℓ : ℝ) / gammaOf (N n) (B n) ∈ L →
          |CbarPart β (B n) (plSpec α (c n) (N n)) i ℓ -
            profC α (rowFrac i) ((ℓ : ℝ) / gammaOf (N n) (B n))| ≤ ε := by
  intro K hK hKc L hL hLc ε hε
  have h := vb_compact_uniform (ι := fun n => Fin (N n) × ℤ) (K ×ˢ L) (hKc.prod hLc)
    (fun n z => (rowFrac z.1, (z.2 : ℝ) / gammaOf (N n) (B n)))
    (fun n z => CbarPart β (B n) (plSpec α (c n) (N n)) z.1 z.2)
    (fun q => profC α q.1 q.2) (vb_profile_continuous R.hα K L hK hKc hL hLc) ?_ ε hε
  · filter_upwards [h] with n hn i ℓ hi hℓ
    exact hn (i, ℓ) ⟨hi, hℓ⟩
  · intro φ hφ z _ q hq hqT
    exact hseq φ hφ (fun k => (z k).1) (fun k => (z k).2)
      q.1 (hK hq.1) q.2 (hL hq.2) ((continuous_fst.tendsto q).comp hqT) ((continuous_snd.tendsto q).comp hqT)

/-- The second uniform conclusion reduces to the sequential normalized variance limit. -/
private lemma vb_variance_uniform_of_seq {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (hseq : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ i : ∀ k, Fin (N (φ k)),
      ∀ x ∈ Ioc (0 : ℝ) 1, Tendsto (fun k => rowFrac (i k)) atTop (𝓝 x) →
      Tendsto (fun k => vPart β (B (φ k)) (plSpec α (c (φ k)) (N (φ k))) (i k) /
        gammaOf (N (φ k)) (B (φ k))) atTop (𝓝 (profGamma α x))) :
    ∀ K : Set ℝ, K ⊆ Ioc 0 1 → IsCompact K → ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ i : Fin (N n), rowFrac i ∈ K →
        |vPart β (B n) (plSpec α (c n) (N n)) i / gammaOf (N n) (B n) -
          profGamma α (rowFrac i)| ≤ ε := by
  intro K hK hKc
  apply vb_compact_uniform K hKc (fun _ i => rowFrac i)
    (fun n i => vPart β (B n) (plSpec α (c n) (N n)) i / gammaOf (N n) (B n))
    (profGamma α) ((lem_app_pl_Gamma_helper_cont R.hα).mono hK)
  intro φ hφ i _ x hx hix
  exact hseq φ hφ i x (hK hx) hix

/-- The age lemma already supplies absolute convergence of the lag series, at every dimension. -/
private lemma vb_Cbar_summable {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (n : ℕ) (i : Fin (N n)) :
    Summable (fun ℓ : ℤ => CbarPart β (B n) (plSpec α (c n) (N n)) i ℓ) := by
  exact ((lem_app_pl_age_iv R.hα R.hβ0 R.hβ1 (N n) (B n) (c n)
    (R.hNpos n) (R.hBpos n) (R.hcpos n) i).2.2.2.1).mul_left _

/-- Any natural-number tail of the positive-lag series is summable. -/
private lemma vb_positive_lags_summable {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (n M : ℕ) (i : Fin (N n)) :
    Summable (fun j : ℕ => CbarPart β (B n) (plSpec α (c n) (N n)) i ((j + M : ℕ) : ℤ)) := by
  exact (vb_Cbar_summable R n i).comp_injective (by
    intro a b hab
    exact Nat.add_right_cancel (Int.ofNat_injective hab))

/-- A geometric estimate for an entire late-lag tail, with its normalization cancelled. -/
private lemma vb_geometric_tail {a C γ : ℝ} (ha : 0 < a) (hγ : 0 < γ)
    (f : ℕ → ℝ) (hf0 : ∀ j, 0 ≤ f j) (M : ℕ)
    (hbound : ∀ j, f (j + M) ≤ C * γ * Real.exp (-a * ((j + M : ℕ) - γ))) :
    γ⁻¹ * ∑' j : ℕ, f (j + M) ≤
      C * Real.exp (-a * ((M : ℝ) - γ)) / (1 - Real.exp (-a)) := by
  have hq : Real.exp (-a) < 1 := Real.exp_lt_one_iff.2 (neg_neg_of_pos ha)
  have hq0 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hgeom := summable_geometric_of_lt_one hq0 hq
  have hrewrite (j : ℕ) :
      C * γ * Real.exp (-a * ((j + M : ℕ) - γ)) =
        (C * γ * Real.exp (-a * ((M : ℝ) - γ))) * Real.exp (-a) ^ j := by
    rw [Nat.cast_add, ← Real.exp_nat_mul]
    have he : -a * ((j : ℝ) + M - γ) = -a * ((M : ℝ) - γ) + (j : ℝ) * -a := by ring
    rw [he, Real.exp_add]
    ring
  have hmajor : Summable (fun j : ℕ =>
      (C * γ * Real.exp (-a * ((M : ℝ) - γ))) * Real.exp (-a) ^ j) := hgeom.mul_left _
  have hle (j : ℕ) : f (j + M) ≤
      (C * γ * Real.exp (-a * ((M : ℝ) - γ))) * Real.exp (-a) ^ j := by
    simpa only [hrewrite j] using hbound j
  have hsum := hmajor.of_nonneg_of_le (fun j => hf0 (j + M)) hle
  have h := mul_le_mul_of_nonneg_left (hsum.tsum_le_tsum hle hmajor) (inv_nonneg.2 hγ.le)
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq] at h
  convert h using 1; field_simp

/-- Lags beyond `(1+η)γ` have vanishing normalized total mass along any bulk row sequence. -/
private lemma vb_late_lag_tail_tendsto {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (hBound : ∀ n : ℕ, ∀ (i : Fin (N n)) (ℓ : ℤ),
      0 ≤ CbarPart β (B n) (plSpec α (c n) (N n)) i ℓ ∧
        CbarPart β (B n) (plSpec α (c n) (N n)) i ℓ ≤ 1)
    {x : ℝ} (hx : x ∈ Ioc 0 1) (i : ∀ n, Fin (N n))
    (hix : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 x))
    {η : ℝ} (hη : 0 < η) (M : ℕ → ℕ)
    (hM : ∀ᶠ n in atTop, (1 + η) * gammaOf (N n) (B n) ≤ (M n : ℝ)) :
    Tendsto (fun n => (gammaOf (N n) (B n))⁻¹ *
      ∑' j : ℕ, CbarPart β (B n) (plSpec α (c n) (N n)) (i n) ((j + M n : ℕ) : ℤ))
      atTop (𝓝 0) := by
  have ha : 0 < |Real.log β| := abs_pos.2 (ne_of_lt (Real.log_neg R.hβ0 R.hβ1))
  have hxhalf : x / 2 ∈ Ioc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨C₀, C, hC⟩ := large_lag_bound (α := α) (β := β) (x / 2) hxhalf
  have hrow : ∀ᶠ n in atTop, x / 2 ≤ rowFrac (i n) :=
    ((tendsto_order.1 hix).1 (x / 2) (by linarith [hx.1])).mono (fun _ h => h.le)
  have hcut : ∀ᶠ n in atTop, C₀ / η ≤ gammaOf (N n) (B n) := R.hγ.eventually_ge_atTop _
  have hupper : Tendsto (fun n => |C| *
      Real.exp (-(|Real.log β| * η * gammaOf (N n) (B n))) /
        (1 - Real.exp (-|Real.log β|))) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (R.hγ.const_mul_atTop (mul_pos ha hη))
    simpa [gammaOf] using (tendsto_const_nhds.mul he).div_const (1 - Real.exp (-|Real.log β|))
  apply squeeze_zero' ?_ ?_ hupper
  · exact Filter.Eventually.of_forall (fun n => mul_nonneg (by unfold gammaOf; positivity)
      (tsum_nonneg (fun j => (hBound n (i n) _).1)))
  · filter_upwards [hC N B c R, hrow, hcut, hM] with n hn hni hncut hnM
    have hγ : 0 < gammaOf (N n) (B n) := by
      unfold gammaOf
      exact div_pos (Nat.cast_pos.2 (R.hNpos n)) (Nat.cast_pos.2 (R.hBpos n))
    have hcut' : gammaOf (N n) (B n) + C₀ ≤ (M n : ℝ) := by
      have := (div_le_iff₀ hη).1 hncut
      nlinarith
    have ht := vb_geometric_tail ha hγ
      (fun j => CbarPart β (B n) (plSpec α (c n) (N n)) (i n) (j : ℤ))
      (fun j => (hBound n (i n) (j : ℤ)).1) (M n) (fun j => by
        have hh := (hn (i n) hni (j + M n) (by push_cast; linarith [hcut'])).2
        exact hh.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self C) hγ.le) (Real.exp_nonneg _)))
    refine ht.trans ?_
    apply div_le_div_of_nonneg_right ?_ (by linarith [Real.exp_lt_one_iff.2 (neg_neg_of_pos ha)])
    apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
    apply Real.exp_le_exp.2
    nlinarith

/-- Continuity of the profile controls a moving bulk row uniformly over compact lag intervals. -/
private lemma vb_profile_uniform_row {α : ℝ} (hα : 0 < α)
    (K : Set ℝ) (hK : K ⊆ Ioc 0 1) (hKc : IsCompact K)
    {x : ℝ} (hx : x ∈ K) (xn : ℕ → ℝ) (hxn : Tendsto xn atTop (𝓝 x))
    (hxnK : ∀ᶠ n in atTop, xn n ∈ K)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ τ ∈ Icc η (1 - η),
      |profC α (xn n) τ - profC α x τ| ≤ ε := by
  intro ε hε
  have hcont := (hKc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (profC_continuousOn hα K hK hKc hη0 hη1)
  obtain ⟨δ, hδ, hδP⟩ := Metric.uniformContinuousOn_iff.1 hcont ε hε
  filter_upwards [hxnK, (Metric.tendsto_nhds.1 hxn) δ hδ] with n hnK hnδ τ hτ
  have hh := hδP (xn n, τ) ⟨hnK, hτ⟩ (x, τ) ⟨hx, hτ⟩
    (by simpa only [dist_prod_same_right] using hnδ)
  simpa only [Real.dist_eq] using hh.le

/-- On compact lag intervals, the sequential bulk limit supplies exactly the uniform input
needed by the frozen Riemann-sum lemma. -/
private lemma vb_interior_lag_sum {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {x : ℝ} (hx : x ∈ Ioc 0 1)
    (i : ∀ n, Fin (N n)) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 2)
    (hseq : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ ℓ : ℕ → ℤ, ∀ τ ∈ Icc η (1 - η),
      Tendsto (fun k => (ℓ k : ℝ) / gammaOf (N (φ k)) (B (φ k))) atTop (𝓝 τ) →
      Tendsto (fun k => CbarPart β (B (φ k)) (plSpec α (c (φ k)) (N (φ k))) (i (φ k)) (ℓ k))
        atTop (𝓝 (profC α x τ))) :
    Tendsto (fun n => (gammaOf (N n) (B n))⁻¹ *
        ∑ ℓ ∈ Finset.Icc ⌈η * gammaOf (N n) (B n)⌉ ⌊(1 - η) * gammaOf (N n) (B n)⌋,
          CbarPart β (B n) (plSpec α (c n) (N n)) (i n) ℓ)
      atTop (𝓝 (∫ τ in η..(1 - η), profC α x τ)) := by
  have hc : ContinuousOn (fun τ => profC α x τ) (Icc η (1 - η)) := by
    apply (profC_continuousOn R.hα {x} (by simpa) isCompact_singleton hη0 hη1).comp
      (continuousOn_const.prodMk continuousOn_id)
    intro τ hτ
    exact ⟨by simp, hτ⟩
  apply riemann_lag_sum _ R.hγ _ _ hη0 hη1 hc
  apply vb_compact_uniform (Icc η (1 - η)) isCompact_Icc
    (fun n (ℓ : ℤ) => (ℓ : ℝ) / gammaOf (N n) (B n))
    (fun n ℓ => CbarPart β (B n) (plSpec α (c n) (N n)) (i n) ℓ) (profC α x) hc
  intro φ hφ ℓ _ τ hτ hℓ
  exact hseq φ hφ ℓ τ hτ hℓ

/-- The first `ηγ` positive lags contribute at most `η` after normalization. -/
private lemma vb_small_lags_bound {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η)
    (f : ℕ → ℝ) (hf0 : ∀ j, 0 ≤ f j) (hf1 : ∀ j, f j ≤ 1) :
    0 ≤ γ⁻¹ * ∑ j ∈ Finset.range ⌊η * γ⌋₊, f (j + 1) ∧
      γ⁻¹ * ∑ j ∈ Finset.range ⌊η * γ⌋₊, f (j + 1) ≤ η := by
  constructor
  · exact mul_nonneg (inv_nonneg.2 hγ.le) (Finset.sum_nonneg (fun j _ => hf0 (j + 1)))
  · have hs : ∑ j ∈ Finset.range ⌊η * γ⌋₊, f (j + 1) ≤ (⌊η * γ⌋₊ : ℝ) := by
      simpa using Finset.sum_le_sum (s := Finset.range ⌊η * γ⌋₊) (fun j _ => hf1 (j + 1))
    have hfloor := Nat.floor_le (mul_nonneg hη hγ.le)
    have := mul_le_mul_of_nonneg_left (hs.trans hfloor) (inv_nonneg.2 hγ.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hγ.ne', one_mul, mul_comm η γ] using this

/-- The omitted endpoint integrals of an interval-integrable function vanish. -/
private lemma vb_integral_cutoff {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hf : IntervalIntegrable f volume 0 b) (δ : ℕ → ℝ)
    (hδ : ∀ j, δ j ∈ Icc 0 (b / 2)) (hδ0 : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun j => ∫ p in δ j..(b - δ j), f p) atTop (𝓝 (∫ p in 0..b, f p)) := by
  have hc : ContinuousOn (fun t => ∫ p in 0..t, f p) (Icc 0 b) := by
    simpa only [uIcc_of_le hb.le] using
      (intervalIntegral.continuousOn_primitive_interval' hf left_mem_uIcc)
  have hδmem (j : ℕ) : δ j ∈ Icc 0 b := ⟨(hδ j).1, by linarith [(hδ j).2]⟩
  have hbδmem (j : ℕ) : b - δ j ∈ Icc 0 b := by
    constructor <;> linarith [(hδ j).1, (hδ j).2]
  have ht0 := (hc 0 ⟨le_rfl, hb.le⟩).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hδ0, Filter.Eventually.of_forall hδmem⟩)
  have htb := (hc b ⟨hb.le, le_rfl⟩).tendsto.comp
    (tendsto_nhdsWithin_iff.2
      ⟨by simpa using tendsto_const_nhds.sub hδ0, Filter.Eventually.of_forall hbδmem⟩)
  have hlim := htb.sub ht0
  have hsub (t : ℝ) (ht : t ∈ Icc 0 b) : IntervalIntegrable f volume 0 t := by
    apply hf.mono_set
    rw [uIcc_of_le ht.1, uIcc_of_le hb.le]
    exact Icc_subset_Icc le_rfl ht.2
  simpa only [Function.comp_apply, intervalIntegral.integral_interval_sub_left (hsub _ (hbδmem _))
    (hsub _ (hδmem _)), intervalIntegral.integral_same, sub_zero] using hlim

/-- Sending the lag cutoff to zero recovers the Gamma profile. -/
private lemma vb_Gamma_cutoff {α x : ℝ} (hα : 0 < α) (hx : x ∈ Ioc 0 1)
    (η : ℕ → ℝ) (hη : ∀ j, η j ∈ Icc 0 (1 / 2)) (hη0 : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun j => 2 * ∫ τ in η j..(1 - η j), profC α x τ)
      atTop (𝓝 (profGamma α x)) := by
  exact (vb_integral_cutoff zero_lt_one (lem_app_pl_Gamma_helper_integrable hα x hx)
    η hη hη0).const_mul 2

/-- A limit of compact truncations, together with uniformly vanishing remainders, is a limit
of the unrestricted quantities. -/
private lemma vb_tendsto_of_truncations (A : ℕ → ℝ) (T : ℕ → ℕ → ℝ) (t : ℕ → ℝ) (a : ℝ)
    (ht : Tendsto t atTop (𝓝 a))
    (hT : ∀ j, Tendsto (T j) atTop (𝓝 (t j)))
    (hrem : ∀ ε > 0, ∃ J : ℕ, ∀ j ≥ J, ∀ᶠ n in atTop, |A n - T j n| ≤ ε) :
    Tendsto A atTop (𝓝 a) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨J, hJ⟩ := hrem (ε / 3) (by positivity)
  obtain ⟨j, hjJ, hj⟩ := ((eventually_ge_atTop J).and
    ((Metric.tendsto_nhds.1 ht) (ε / 3) (by positivity))).exists
  filter_upwards [hJ j hjJ, (Metric.tendsto_nhds.1 (hT j)) (ε / 3) (by positivity)] with n hn hnT
  rw [Real.dist_eq] at hj hnT ⊢
  have hab : |A n - a| ≤ |A n - T j n| + |T j n - t j| + |t j - a| := by
    calc
      |A n - a| = |(A n - T j n) + (T j n - t j) + (t j - a)| := by congr 1; ring
      _ ≤ |A n - T j n| + |T j n - t j| + |t j - a| := abs_add_three _ _ _
  linarith

/-- The remaining analytic input for the bulk lag limit is just removal of the compact
shell restriction; all compact limits and the limiting endpoint integrals are already known. -/
private lemma vb_bulk_limit_of_shell_remainders {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {x : ℝ} (hx : x ∈ Ioc 0 1)
    (i : ∀ n, Fin (N n)) (hix : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 x))
    {τ : ℝ} (hτ : τ ∈ Ioo 0 1) (ℓ : ℕ → ℤ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / gammaOf (N n) (B n)) atTop (𝓝 τ))
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j ∧ δ j < (1 - τ) / 2)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hrem : ∀ ε > 0, ∃ J : ℕ, ∀ j ≥ J, ∀ᶠ n in atTop,
      |CbarPart β (B n) (plSpec α (c n) (N n)) (i n) (ℓ n) -
        (Real.pi ^ 2)⁻¹ * lagTerm β (B n) (plSpec α (c n) (N n)) (i n)
          ((fun p => gammaOf (N n) (B n) * p) '' Icc (δ j) (1 - τ - δ j))
          (Ioo 0 (gammaOf (N n) (B n))) (ℓ n)| ≤ ε) :
    Tendsto (fun n => CbarPart β (B n) (plSpec α (c n) (N n)) (i n) (ℓ n))
      atTop (𝓝 (profC α x τ)) := by
  have hprof := profC_eq_integral_A R.hα hx hτ
  apply vb_tendsto_of_truncations _ _
    (fun j => ∫ p in δ j..(1 - τ - δ j),
      profA α x p * profA α x (p + τ) / profDeltaC α p (p + τ))
    (profC α x τ) ?_ ?_ hrem
  · rw [hprof.2]
    exact vb_integral_cutoff (by linarith [hτ.2]) hprof.1 δ
      (fun j => ⟨(hδ j).1.le, (hδ j).2.le⟩) hδ0
  · intro j
    have hj : δ j ≤ 1 - τ - δ j := by linarith [(hδ j).2]
    have hK : Icc (δ j) (1 - τ - δ j) ⊆ Ioo 0 (1 - τ) := by
      intro p hp
      exact ⟨lt_of_lt_of_le (hδ j).1 hp.1, by linarith [hp.2, (hδ j).1]⟩
    simpa only [intervalIntegral.integral_of_le hj, ← integral_Icc_eq_integral_Ioc] using
      bulk_compact_limit R hx i hix hτ ℓ hℓ (δ j) (1 - τ - δ j) hK

/-- Once the interior lag limits are available, only the discarded-lag remainder is needed
to reconstruct the normalized variance. -/
private lemma vb_variance_limit_of_lag_remainders {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {x : ℝ} (hx : x ∈ Ioc 0 1)
    (i : ∀ n, Fin (N n)) (η : ℕ → ℝ)
    (hη : ∀ j, 0 < η j ∧ η j < 1 / 2) (hη0 : Tendsto η atTop (𝓝 0))
    (hseq : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ ℓ : ℕ → ℤ, ∀ τ ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun k => (ℓ k : ℝ) / gammaOf (N (φ k)) (B (φ k))) atTop (𝓝 τ) →
      Tendsto (fun k => CbarPart β (B (φ k)) (plSpec α (c (φ k)) (N (φ k))) (i (φ k)) (ℓ k))
        atTop (𝓝 (profC α x τ)))
    (hrem : ∀ ε > 0, ∃ J : ℕ, ∀ j ≥ J, ∀ᶠ n in atTop,
      |vPart β (B n) (plSpec α (c n) (N n)) (i n) / gammaOf (N n) (B n) -
        2 * ((gammaOf (N n) (B n))⁻¹ *
          ∑ ℓ ∈ Finset.Icc ⌈η j * gammaOf (N n) (B n)⌉ ⌊(1 - η j) * gammaOf (N n) (B n)⌋,
            CbarPart β (B n) (plSpec α (c n) (N n)) (i n) ℓ)| ≤ ε) :
    Tendsto (fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n) /
        gammaOf (N n) (B n)) atTop (𝓝 (profGamma α x)) := by
  apply vb_tendsto_of_truncations _ _
    (fun j => 2 * ∫ τ in η j..(1 - η j), profC α x τ) (profGamma α x) ?_ ?_ hrem
  · exact vb_Gamma_cutoff R.hα hx η (fun j => ⟨(hη j).1.le, (hη j).2.le⟩) hη0
  · intro j
    apply (vb_interior_lag_sum R hx i (hη j).1 (hη j).2 ?_).const_mul 2
    intro φ hφ ℓ τ hτ hℓ
    exact hseq φ hφ ℓ τ ⟨lt_of_lt_of_le (hη j).1 hτ.1, by linarith [hτ.2, (hη j).1]⟩ hℓ

/-- Outside a compact first-coordinate shell, a point is in the small-age region, the
second-coordinate endpoint region, or the exponentially small off-shell region. These are
exactly the three regions controlled by `majorant_shell_mass`. -/
private lemma vb_shell_remainder_cover {γ δ τ ℓ m₁ m₂ : ℝ} (hγ : 0 < γ)
    (hℓ : (τ - δ) * γ ≤ ℓ)
    (hm₁ : m₁ ∉ (fun p : ℝ => γ * p) '' Icc δ (1 - τ - δ)) :
    m₁ < δ * γ ∨ (1 - 3 * δ) * γ < m₂ ∨ δ * γ ≤ |m₁ - m₂ + ℓ| := by
  by_contra h
  push Not at h
  obtain ⟨hlo, hhi, hoff⟩ := h
  apply hm₁
  refine ⟨m₁ / γ, ⟨(le_div_iff₀ hγ).2 hlo, (div_le_iff₀ hγ).2 ?_⟩, ?_⟩
  · have := (abs_lt.1 hoff).2
    nlinarith
  · exact mul_div_cancel₀ m₁ hγ.ne'

/-- A three-region integrable majorant controls removal of a measurable cutoff. -/
private lemma vb_integral_remainder_bound
    (f g : ℝ × ℝ → ℝ) (S K A B D : Set (ℝ × ℝ))
    (hS : MeasurableSet S) (hK : MeasurableSet K) (hKS : K ⊆ S)
    (hf : IntegrableOn f S) (hg : ∀ q, 0 ≤ g q)
    (hA : IntegrableOn g A) (hB : IntegrableOn g B) (hD : IntegrableOn g D)
    (hcover : S \ K ⊆ (A ∪ B) ∪ D)
    {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ q ∈ S, |f q| ≤ C * g q) :
    |(∫ q in S, f q) - ∫ q in K, f q| ≤
      C * ((∫ q in A, g q) + (∫ q in B, g q) + ∫ q in D, g q) := by
  have hmeasure : volume.restrict (S \ K) ≤
      (volume.restrict A + volume.restrict B) + volume.restrict D :=
    (Measure.restrict_mono hcover le_rfl).trans
      ((Measure.restrict_union_le _ _).trans
        (add_le_add (Measure.restrict_union_le _ _) le_rfl))
  have hgsum := Integrable.add_measure (Integrable.add_measure hA hB) hD
  have hgrest : IntegrableOn g (S \ K) := hgsum.mono_measure hmeasure
  have hmass := integral_mono_measure hmeasure (Filter.Eventually.of_forall hg) hgsum
  rw [integral_add_measure (Integrable.add_measure hA hB) hD, integral_add_measure hA hB] at hmass
  rw [← setIntegral_sdiff hK hf hKS]
  calc
    |∫ q in S \ K, f q| ≤ ∫ q in S \ K, |f q| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm f (μ := volume.restrict (S \ K)))
    _ ≤ ∫ q in S \ K, C * g q :=
      setIntegral_mono_on (hf.mono_set sdiff_subset).norm (hgrest.const_mul C)
        (hS.diff hK) (fun q hq => hfg q hq.1)
    _ = C * ∫ q in S \ K, g q := integral_const_mul C g
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass hC

/-- Fubini in the ambient Euclidean volume convention. -/
private lemma vb_fubini (f : ℝ × ℝ → ℝ) (I J : Set ℝ)
    (hf : IntegrableOn f (I ×ˢ J)) :
    (∫ q in I ×ˢ J, f q) = ∫ a in I, ∫ b in J, f (a, b) := by
  rw [Measure.volume_eq_prod] at hf ⊢
  exact setIntegral_prod f hf

/-- Nonnegativity of the shell majorant. -/
private lemma vb_majorant_nonneg {β : ℝ} {N B : ℕ} {μ : Fin N → ℝ}
    (i : Fin N) (ℓ : ℤ) (a b : ℝ) : 0 ≤ lagMajorant β B μ i ℓ a b := by
  unfold lagMajorant gRow gammaOf
  positivity

/-- Quantitative removal of a compact first-coordinate shell. -/
private lemma vb_shell_error {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {x : ℝ} (hx : x ∈ Ioc 0 1)
    (i : ∀ n, Fin (N n)) (hix : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 x))
    {τ : ℝ} (hτ : τ ∈ Ioo 0 1) (ℓ : ℕ → ℤ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / gammaOf (N n) (B n)) atTop (𝓝 τ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ < (1 - τ) / 2 → 3 * δ < 1 / 2 →
      ∀ᶠ n in atTop,
      |CbarPart β (B n) (plSpec α (c n) (N n)) (i n) (ℓ n) -
        (Real.pi ^ 2)⁻¹ * lagTerm β (B n) (plSpec α (c n) (N n)) (i n)
          ((fun p => gammaOf (N n) (B n) * p) '' Icc δ (1 - τ - δ))
          (Ioo 0 (gammaOf (N n) (B n))) (ℓ n)| ≤
        C * (4 * δ + Real.log (gammaOf (N n) (B n)) / gammaOf (N n) (B n) +
          gammaOf (N n) (B n) * Real.exp (-|Real.log β| *
            (δ * gammaOf (N n) (B n)) / 2)) := by
  have hxhalf : x / 2 ∈ Ioc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hτhalf : 0 < τ / 2 := by linarith [hτ.1]
  obtain ⟨C₁, hd⟩ := lag_integrand_majorant (α := α) (β := β) (x / 2) (τ / 2) hxhalf hτhalf
  obtain ⟨C₂, hm⟩ := majorant_shell_mass (α := α) (β := β) (x / 2) (τ / 2) hxhalf hτhalf
  refine ⟨(Real.pi ^ 2)⁻¹ * |C₁| * |C₂|, by positivity, ?_⟩
  intro δ hδ hδτ hδsmall
  have hrow : ∀ᶠ n in atTop, x / 2 ≤ rowFrac (i n) :=
    ((tendsto_order.1 hix).1 _ (by linarith [hx.1])).mono (fun _ h => h.le)
  have hlag : ∀ᶠ n in atTop, τ / 2 ≤ (ℓ n : ℝ) / gammaOf (N n) (B n) :=
    ((tendsto_order.1 hℓ).1 _ (by linarith [hτ.1])).mono (fun _ h => h.le)
  have hlagδ : ∀ᶠ n in atTop, τ - δ ≤ (ℓ n : ℝ) / gammaOf (N n) (B n) :=
    ((tendsto_order.1 hℓ).1 _ (by linarith)).mono (fun _ h => h.le)
  filter_upwards [hd N B c R, hm N B c R δ hδ (by linarith),
    hm N B c R (3 * δ) (by positivity) hδsmall, hrow, hlag, hlagδ,
    R.hγ.eventually_ge_atTop 1] with n hdn hmn hm3n hr hl hlδ hγ1
  have hγ : 0 < gammaOf (N n) (B n) := lt_of_lt_of_le zero_lt_one hγ1
  have hl' := (le_div_iff₀ hγ).1 hl
  have hlδ' := (le_div_iff₀ hγ).1 hlδ
  obtain ⟨ha, hma, _, _, he, hme⟩ := hmn (i n) hr (ℓ n) hl'
  obtain ⟨_, _, hb, hmb, _, _⟩ := hm3n (i n) hr (ℓ n) hl'
  let γ := gammaOf (N n) (B n)
  let I := Ioo (0 : ℝ) γ
  let K := (fun p : ℝ => γ * p) '' Icc δ (1 - τ - δ)
  let f := fun q : ℝ × ℝ => lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) (ℓ n) q.1 q.2
  let g := fun q : ℝ × ℝ => lagMajorant β (B n) (plSpec α (c n) (N n)) (i n) (ℓ n) q.1 q.2
  have hKmeas : MeasurableSet K := (isCompact_Icc.image (continuous_const.mul continuous_id)).measurableSet
  have hKI : K ⊆ I := by
    rintro _ ⟨p, hp, rfl⟩
    constructor
    · exact mul_pos hγ (lt_of_lt_of_le hδ hp.1)
    · have : p < 1 := by linarith [hp.2, hτ.1]
      simpa only [mul_one] using mul_lt_mul_of_pos_left this hγ
  have hf : IntegrableOn f (I ×ˢ I) :=
    (lem_app_pl_age_iv R.hα R.hβ0 R.hβ1 (N n) (B n) (c n)
      (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n)).2.2.1 (ℓ n)
  have hbnd := vb_integral_remainder_bound f g (I ×ˢ I) (K ×ˢ I)
    (Ioo 0 (δ * γ) ×ˢ I) (I ×ˢ Ioo ((1 - 3 * δ) * γ) γ)
    {q | q ∈ I ×ˢ I ∧ δ * γ ≤ |q.1 - q.2 + (ℓ n : ℝ)|}
    (measurableSet_Ioo.prod measurableSet_Ioo) (hKmeas.prod measurableSet_Ioo)
    (Set.prod_mono hKI Subset.rfl) hf (fun q => vb_majorant_nonneg _ _ _ _) ha hb he ?_
    (abs_nonneg C₁) ?_
  · have hsum : (∫ q in Ioo 0 (δ * γ) ×ˢ I, g q) +
        (∫ q in I ×ˢ Ioo ((1 - 3 * δ) * γ) γ, g q) +
        (∫ q in {q | q ∈ I ×ˢ I ∧ δ * γ ≤ |q.1 - q.2 + (ℓ n : ℝ)|}, g q) ≤
        |C₂| * (4 * δ + Real.log γ / γ + γ * Real.exp (-|Real.log β| * (δ * γ) / 2)) := by
      rw [vb_fubini g _ _ ha, vb_fubini g _ _ hb]
      have hlog : 0 ≤ Real.log γ / γ := div_nonneg (Real.log_nonneg hγ1) hγ.le
      have hle := add_le_add (add_le_add hma hmb) hme
      have he0 : 0 ≤ γ * Real.exp (-|Real.log β| * (δ * γ) / 2) := by positivity
      calc
        _ ≤ C₂ * (4 * δ + Real.log γ / γ + γ * Real.exp (-|Real.log β| * (δ * γ) / 2)) := by
          convert hle using 1 <;> dsimp only [γ] <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_abs_self C₂) (by positivity)
    rw [vb_fubini f I I hf, vb_fubini f K I (hf.mono_set (Set.prod_mono hKI Subset.rfl))] at hbnd
    have hpi : 0 ≤ (Real.pi ^ 2)⁻¹ := by positivity
    have hfinal := mul_le_mul_of_nonneg_left
      (hbnd.trans (mul_le_mul_of_nonneg_left hsum (abs_nonneg C₁))) hpi
    simpa only [CbarPart, lagTerm, ← mul_sub, abs_mul, abs_of_nonneg hpi, mul_assoc,
      f, I, K, γ] using hfinal
  · rintro q ⟨hq, hqK⟩
    have hq1 : q.1 ∉ K := fun h => hqK ⟨h, hq.2⟩
    rcases vb_shell_remainder_cover hγ hlδ' hq1 with h | h | h
    · exact Or.inl (Or.inl ⟨⟨hq.1.1, h⟩, hq.2⟩)
    · exact Or.inl (Or.inr ⟨hq.1, h, hq.2.2⟩)
    · exact Or.inr ⟨hq, h⟩
  · intro q hq
    exact (hdn (i n) hr (ℓ n) hl' q.1 hq.1 q.2 hq.2).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C₁) (vb_majorant_nonneg _ _ _ _))

/-- The three discarded shell regions vanish as the cutoff tends to zero. -/
private lemma vb_shell_remainders {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {x : ℝ} (hx : x ∈ Ioc 0 1)
    (i : ∀ n, Fin (N n)) (hix : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 x))
    {τ : ℝ} (hτ : τ ∈ Ioo 0 1) (ℓ : ℕ → ℤ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / gammaOf (N n) (B n)) atTop (𝓝 τ))
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j ∧ δ j < (1 - τ) / 2)
    (hδ0 : Tendsto δ atTop (𝓝 0)) :
    ∀ ε > 0, ∃ J : ℕ, ∀ j ≥ J, ∀ᶠ n in atTop,
      |CbarPart β (B n) (plSpec α (c n) (N n)) (i n) (ℓ n) -
        (Real.pi ^ 2)⁻¹ * lagTerm β (B n) (plSpec α (c n) (N n)) (i n)
          ((fun p => gammaOf (N n) (B n) * p) '' Icc (δ j) (1 - τ - δ j))
          (Ioo 0 (gammaOf (N n) (B n))) (ℓ n)| ≤ ε := by
  obtain ⟨C, hC, herr⟩ := vb_shell_error R hx i hix hτ ℓ hℓ
  have hlog : Tendsto (fun n => Real.log (gammaOf (N n) (B n)) /
      gammaOf (N n) (B n)) atTop (𝓝 0) := by
    simpa [Function.comp_def, gammaOf] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp R.hγ
  have ha : 0 < |Real.log β| := abs_pos.2 (ne_of_lt (Real.log_neg R.hβ0 R.hβ1))
  intro ε hε
  have hcδ : Tendsto (fun j => C * (4 * δ j)) atTop (𝓝 0) := by
    simpa using (hδ0.const_mul 4).const_mul C
  obtain ⟨J, hJ⟩ := eventually_atTop.1
    (((tendsto_order.1 hδ0).2 (1 / 6) (by norm_num)).and
      ((tendsto_order.1 hcδ).2 ε hε))
  refine ⟨J, fun j hj => ?_⟩
  have hjδ : 3 * δ j < 1 / 2 := by linarith [(hJ j hj).1]
  have he : Tendsto (fun n => gammaOf (N n) (B n) * Real.exp
      (-|Real.log β| * (δ j * gammaOf (N n) (B n)) / 2)) atTop (𝓝 0) := by
    have hb : 0 < |Real.log β| * δ j / 2 := div_pos (mul_pos ha (hδ j).1) (by norm_num)
    have ht := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (R.hγ.const_mul_atTop hb)).const_mul (|Real.log β| * δ j / 2)⁻¹
    convert ht using 1
    · ext n
      simp only [pow_one, Function.comp_apply]
      have heq : -|Real.log β| * (δ j * gammaOf (N n) (B n)) / 2 =
          -(|Real.log β| * δ j / 2 * gammaOf (N n) (B n)) := by ring
      rw [heq]
      change gammaOf (N n) (B n) * Real.exp _ =
        (|Real.log β| * δ j / 2)⁻¹ *
          ((|Real.log β| * δ j / 2) * gammaOf (N n) (B n) * Real.exp _)
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul]
      rfl
    · simp
  have ht : Tendsto (fun n => C * (4 * δ j + Real.log (gammaOf (N n) (B n)) /
      gammaOf (N n) (B n) + gammaOf (N n) (B n) * Real.exp
        (-|Real.log β| * (δ j * gammaOf (N n) (B n)) / 2)))
      atTop (𝓝 (C * (4 * δ j))) := by
    simpa using ((tendsto_const_nhds.add hlog).add he).const_mul C
  filter_upwards [herr (δ j) (hδ j).1 (hδ j).2 hjδ,
    (tendsto_order.1 ht).2 ε (hJ j hj).2] with n hn hnε
  exact hn.trans hnε.le

/-- A positive cutoff sequence contained in any prescribed positive interval. -/
private lemma vb_cutoff_sequence {b : ℝ} (hb : 0 < b) :
    ∃ δ : ℕ → ℝ, (∀ j, 0 < δ j ∧ δ j < b) ∧ Tendsto δ atTop (𝓝 0) := by
  refine ⟨fun j => (b / 2) * (1 / ((j : ℝ) + 1)), ?_, ?_⟩
  · intro j
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    constructor
    · positivity
    · have hle : 1 / ((j : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).2 hj
      have := mul_le_mul_of_nonneg_left hle (show 0 ≤ b / 2 by positivity)
      linarith
  · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (b / 2)

/-- The unrestricted sequential bulk lag limit. -/
private lemma vb_bulk_limit {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {x : ℝ} (hx : x ∈ Ioc 0 1)
    (i : ∀ n, Fin (N n)) (hix : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 x))
    {τ : ℝ} (hτ : τ ∈ Ioo 0 1) (ℓ : ℕ → ℤ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / gammaOf (N n) (B n)) atTop (𝓝 τ)) :
    Tendsto (fun n => CbarPart β (B n) (plSpec α (c n) (N n)) (i n) (ℓ n))
      atTop (𝓝 (profC α x τ)) := by
  obtain ⟨δ, hδ, hδ0⟩ := vb_cutoff_sequence (show 0 < (1 - τ) / 2 by linarith [hτ.2])
  exact vb_bulk_limit_of_shell_remainders R hx i hix hτ ℓ hℓ δ hδ hδ0
    (vb_shell_remainders R hx i hix hτ ℓ hℓ δ hδ hδ0)

/-- Counting the omitted lags in a finite positive-lag prefix. -/
private lemma vb_lag_count_bound (f : ℤ → ℝ) (hf0 : ∀ k, 0 ≤ f k)
    (hf1 : ∀ k, f k ≤ 1) (hf : Summable (fun k : ℕ => f ((k : ℤ) + 1)))
    (M : ℕ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b + 1) (hb : b ≤ M) :
    0 ≤ (∑' k : ℕ, f ((k : ℤ) + 1)) - ∑ l ∈ Finset.Icc a b, f l ∧
    (∑' k : ℕ, f ((k : ℤ) + 1)) - ∑ l ∈ Finset.Icc a b, f l ≤
      (M : ℝ) - ((b : ℝ) + 1 - a) + ∑' k : ℕ, f ((k + M : ℕ) + 1) := by
  have hsub : Finset.Icc a b ⊆ Finset.Icc (1 : ℤ) M := by
    intro l hl
    simp only [Finset.mem_Icc] at hl ⊢
    exact ⟨ha.trans hl.1, hl.2.trans hb⟩
  have hprefix : (∑ l ∈ Finset.Icc (1 : ℤ) M, f l) =
      ∑ k ∈ Finset.range M, f ((k : ℤ) + 1) := by
    rw [Int.Icc_eq_finset_map, Finset.sum_map]
    simp [add_comm]
  have hsplit := hf.sum_add_tsum_nat_add M
  rw [← hprefix] at hsplit
  have hsd := Finset.sum_sdiff hsub (f := f)
  have htail0 : 0 ≤ ∑' k : ℕ, f ((k + M : ℕ) + 1) := tsum_nonneg (fun _ => hf0 _)
  have hdiff0 : 0 ≤ ∑ l ∈ Finset.Icc (1 : ℤ) M \ Finset.Icc a b, f l :=
    Finset.sum_nonneg (fun l _ => hf0 l)
  have hdiff1 : (∑ l ∈ Finset.Icc (1 : ℤ) M \ Finset.Icc a b, f l) ≤
      (M : ℝ) - ((b : ℝ) + 1 - a) := by
    have h := Finset.sum_le_sum (s := Finset.Icc (1 : ℤ) M \ Finset.Icc a b)
      (fun l _ => hf1 l)
    have hcardP : (Finset.Icc (1 : ℤ) M).card = M := by simp [Int.card_Icc]
    have hcardS : ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - a := by
      exact_mod_cast Int.card_Icc_of_le a b hab
    have hcardle : (Finset.Icc a b).card ≤ M := by
      simpa only [hcardP] using Finset.card_le_card hsub
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_sdiff_of_subset hsub, hcardP, Nat.cast_sub hcardle, hcardS] using h
  constructor <;> linarith

/-- The variance error consists of at most `3ηγ + O(1)` bounded lags and a late tail. -/
private lemma vb_discarded_lags_bound (f : ℤ → ℝ) (hf0 : ∀ k, 0 ≤ f k)
    (hf1 : ∀ k, f k ≤ 1) (hf : Summable (fun k : ℕ => f ((k : ℤ) + 1)))
    {γ η : ℝ} (hγ : 0 < γ) (hη : 0 < η) (hη1 : η < 1 / 2)
    (hgap : 2 ≤ (1 - 2 * η) * γ) :
    |(1 + 2 * ∑' k : ℕ, f ((k : ℤ) + 1)) / γ -
      2 * (γ⁻¹ * ∑ l ∈ Finset.Icc ⌈η * γ⌉ ⌊(1 - η) * γ⌋, f l)| ≤
      6 * η + 5 / γ + 2 * (γ⁻¹ *
        ∑' k : ℕ, f ((k + ⌈(1 + η) * γ⌉₊ : ℕ) + 1)) := by
  let M := ⌈(1 + η) * γ⌉₊
  let a := ⌈η * γ⌉
  let b := ⌊(1 - η) * γ⌋
  have ha0 : (0 : ℤ) < a := Int.lt_ceil.2 (by simpa using mul_pos hη hγ)
  have ha1 : 1 ≤ a := by omega
  have haU : (a : ℝ) < η * γ + 1 := Int.ceil_lt_add_one _
  have hbL : (1 - η) * γ - 1 < (b : ℝ) := Int.sub_one_lt_floor _
  have hab : a ≤ b + 1 := by
    exact_mod_cast (show (a : ℝ) ≤ (b : ℝ) + 1 by nlinarith)
  have hbU : (b : ℝ) ≤ (1 - η) * γ := Int.floor_le _
  have hML : (1 + η) * γ ≤ (M : ℝ) := Nat.le_ceil _
  have hMU : (M : ℝ) < (1 + η) * γ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hbM : b ≤ (M : ℤ) := by
    exact_mod_cast (show (b : ℝ) ≤ (M : ℝ) by nlinarith)
  obtain ⟨hlo, hhi⟩ := vb_lag_count_bound f hf0 hf1 hf M a b ha1 hab hbM
  have hcount : (M : ℝ) - ((b : ℝ) + 1 - a) ≤ 3 * η * γ + 2 := by nlinarith
  have hhi' := hhi.trans (add_le_add hcount le_rfl)
  have hγ0 : 0 ≤ γ⁻¹ := inv_nonneg.2 hγ.le
  have heq : (1 + 2 * ∑' k : ℕ, f ((k : ℤ) + 1)) / γ -
      2 * (γ⁻¹ * ∑ l ∈ Finset.Icc a b, f l) =
      γ⁻¹ * (1 + 2 * ((∑' k : ℕ, f ((k : ℤ) + 1)) - ∑ l ∈ Finset.Icc a b, f l)) := by
    ring
  rw [heq, abs_of_nonneg (mul_nonneg hγ0 (by linarith))]
  calc
    _ ≤ γ⁻¹ * (1 + 2 * (3 * η * γ + 2 +
        ∑' k : ℕ, f ((k + M : ℕ) + 1))) :=
      mul_le_mul_of_nonneg_left (by linarith [hhi']) hγ0
    _ = _ := by
      dsimp only [M]
      field_simp
      <;> ring

/-- The normalized mass of all discarded lags vanishes with the cutoff. -/
private lemma vb_lag_remainders {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (hBound : ∀ n : ℕ, ∀ (i : Fin (N n)) (ℓ : ℤ),
      0 ≤ CbarPart β (B n) (plSpec α (c n) (N n)) i ℓ ∧
        CbarPart β (B n) (plSpec α (c n) (N n)) i ℓ ≤ 1)
    {x : ℝ} (hx : x ∈ Ioc 0 1) (i : ∀ n, Fin (N n))
    (hix : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 x))
    (η : ℕ → ℝ) (hη : ∀ j, 0 < η j ∧ η j < 1 / 2)
    (hη0 : Tendsto η atTop (𝓝 0)) :
    ∀ ε > 0, ∃ J : ℕ, ∀ j ≥ J, ∀ᶠ n in atTop,
      |vPart β (B n) (plSpec α (c n) (N n)) (i n) / gammaOf (N n) (B n) -
        2 * ((gammaOf (N n) (B n))⁻¹ *
          ∑ ℓ ∈ Finset.Icc ⌈η j * gammaOf (N n) (B n)⌉ ⌊(1 - η j) * gammaOf (N n) (B n)⌋,
            CbarPart β (B n) (plSpec α (c n) (N n)) (i n) ℓ)| ≤ ε := by
  intro ε hε
  have hηlim : Tendsto (fun j => 6 * η j) atTop (𝓝 0) := by simpa using hη0.const_mul 6
  obtain ⟨J, hJ⟩ := eventually_atTop.1 ((tendsto_order.1 hηlim).2 ε hε)
  refine ⟨J, fun j hj => ?_⟩
  have hgap0 : 0 < 1 - 2 * η j := by linarith [(hη j).2]
  have hgap : ∀ᶠ n in atTop, 2 ≤ (1 - 2 * η j) * gammaOf (N n) (B n) := by
    filter_upwards [R.hγ.eventually_ge_atTop (2 / (1 - 2 * η j))] with n hn
    have := (div_le_iff₀ hgap0).1 hn
    simpa only [gammaOf, mul_comm] using this
  have htail := vb_late_lag_tail_tendsto R hBound hx i hix (hη j).1
    (fun n => ⌈(1 + η j) * gammaOf (N n) (B n)⌉₊ + 1)
    (Filter.Eventually.of_forall (fun n => (Nat.le_ceil _).trans (by push_cast; linarith)))
  have hinv : Tendsto (fun n => 5 / gammaOf (N n) (B n)) atTop (𝓝 0) := by
    simpa [gammaOf, div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp R.hγ).const_mul (5 : ℝ)
  have hlim := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 6 * η j) atTop
    (𝓝 (6 * η j))).add hinv).add (htail.const_mul 2)
  have hlim' : Tendsto (fun n => 6 * η j + 5 / gammaOf (N n) (B n) +
      2 * ((gammaOf (N n) (B n))⁻¹ * ∑' k : ℕ,
        CbarPart β (B n) (plSpec α (c n) (N n)) (i n)
          ((k + (⌈(1 + η j) * gammaOf (N n) (B n)⌉₊ + 1) : ℕ) : ℤ)))
      atTop (𝓝 (6 * η j)) := by simpa using hlim
  filter_upwards [hgap, (tendsto_order.1 hlim').2 ε (hJ j hj)] with n hn hnε
  have hγ : 0 < gammaOf (N n) (B n) := by
    unfold gammaOf
    exact div_pos (Nat.cast_pos.2 (R.hNpos n)) (Nat.cast_pos.2 (R.hBpos n))
  have hs : Summable (fun k : ℕ =>
      CbarPart β (B n) (plSpec α (c n) (N n)) (i n) ((k : ℤ) + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using vb_positive_lags_summable R n 1 (i n)
  have he := vb_discarded_lags_bound
    (fun l => CbarPart β (B n) (plSpec α (c n) (N n)) (i n) l)
    (fun l => (hBound n (i n) l).1) (fun l => (hBound n (i n) l).2)
    hs hγ (hη j).1 (hη j).2 hn
  apply le_trans he
  simpa only [vPart, Nat.cast_add, Nat.cast_one, add_assoc] using hnε.le

/-- `thm:app-pl-volatility`, part (i) (bulk), in part-form with hypothesis `hBound`
(snapshot `cr-2026-10-23`). The statement is uniform in the rows `i`, as explained in the module
header. LaTeX, verbatim from `sections/06-power-law/section.tex` (whole theorem; this file
states part (i) only):

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
theorem thm_app_pl_volatility_i_part {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (hBound : ∀ n : ℕ, ∀ (i : Fin (N n)) (ℓ : ℤ),
      0 ≤ CbarPart β (B n) (plSpec α (c n) (N n)) i ℓ ∧
        CbarPart β (B n) (plSpec α (c n) (N n)) i ℓ ≤ 1) :
    (∀ K : Set ℝ, K ⊆ Ioc 0 1 → IsCompact K → ∀ L : Set ℝ, L ⊆ Ioo 0 1 → IsCompact L →
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (N n)) (ℓ : ℤ),
        (((i : ℕ) : ℝ) + 1) / (N n : ℝ) ∈ K →
        (ℓ : ℝ) / gammaOf (N n) (B n) ∈ L →
          |CbarPart β (B n) (plSpec α (c n) (N n)) i ℓ -
            profC α ((((i : ℕ) : ℝ) + 1) / (N n : ℝ)) ((ℓ : ℝ) / gammaOf (N n) (B n))| ≤ ε) ∧
    (∀ K : Set ℝ, K ⊆ Ioc 0 1 → IsCompact K → ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (N n)),
      (((i : ℕ) : ℝ) + 1) / (N n : ℝ) ∈ K →
        |vPart β (B n) (plSpec α (c n) (N n)) i / gammaOf (N n) (B n) -
          profGamma α ((((i : ℕ) : ℝ) + 1) / (N n : ℝ))| ≤ ε) := by
  constructor
  · apply vb_bulk_uniform_of_seq R
    intro φ hφ i ℓ x hx τ hτ hi hℓ
    exact vb_bulk_limit (vb_regime_subseq R hφ) hx i hi hτ ℓ hℓ
  · apply vb_variance_uniform_of_seq R
    intro φ hφ i x hx hi
    have R' := vb_regime_subseq R hφ
    obtain ⟨η, hη, hη0⟩ := vb_cutoff_sequence (show (0 : ℝ) < 1 / 2 by norm_num)
    apply vb_variance_limit_of_lag_remainders R' hx i η hη hη0
    · intro ψ hψ ℓ τ hτ hℓ
      exact vb_bulk_limit (vb_regime_subseq R' hψ) hx (fun k => i (ψ k))
        (hi.comp hψ.tendsto_atTop) hτ ℓ hℓ
    · exact vb_lag_remainders R' (fun n i ℓ => hBound (φ n) i ℓ) hx i hi η hη hη0

end Muon.PowerLaw

end

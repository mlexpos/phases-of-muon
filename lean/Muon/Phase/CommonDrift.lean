import Mathlib
import Muon.Phase.Clock

/-!
# Appendix H: common drift and matched floors (task L-H.11)

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`,
`prop:app-phase-common` (l.539–563) and `thm:app-phase-matched` (l.603–618).
Card: `sections/07-phase-comparison/CARD.md` §2, §3, §5 (L-H.11), §6 items 7, 8.

Reused, not redefined: `Muon.Phase.RowModel` (fields (M1), `RowModel.F0`, `RowModel.S`,
`RowModel.risk`, `RowModel.forcing`, `RowModel.kernel`), `Muon.Phase.IsRowSolution` (M3),
`Muon.Phase.firstHit` (values in `ℝ≥0∞`, `inf ∅ = ⊤`), and the clock theorem
`Muon.Phase.thm_app_phase_clock` (used only for existence of a global solution, which the
paper's proof takes from it).

New declarations are the common-drift constants `commonVtot`, `commonA`, `commonB`, `matchedX`
and the predicate `IsGlobalRowSolution`. The paper's `a_∘, b_∘, u_0` are `commonA`, `commonB`,
`Real.sqrt m.F0`.

Index set: the paper's "finite index set" is `[Fintype ι]`; sums `∑ i` are then finite sums.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Muon.Phase

variable {ι : Type*}

/-- `𝔳_tot = ∑_i μ_i 𝔳_i` of `prop:app-phase-common` (the volatility `𝔳` of
`eqn:comparison-general-form`). -/
def commonVtot [Fintype ι] (m : RowModel ι) : ℝ := ∑ i, m.μ i * m.v i

/-- A row solution that exists on every interval `[0, t₁)`, i.e. a solution of (M3) on
`[0, ∞)`; the model's global solution is the one of `thm_app_phase_clock` when `𝒮 > 0`. -/
def IsGlobalRowSolution (m : RowModel ι) (Q : ι → ℝ → ℝ) : Prop :=
  ∀ t₁ : ℝ, IsRowSolution m t₁ Q

/-- `a_∘ = η 𝔡` of `prop:app-phase-common`. -/
def commonA (m : RowModel ι) (d : ℝ) : ℝ := m.η * d

/-- `b_∘ = η 𝔳_tot / (4 𝔡) = η 𝒮 / 2` of `prop:app-phase-common`. -/
def commonB [Fintype ι] (m : RowModel ι) (d : ℝ) : ℝ := m.η * commonVtot m / (4 * d)

/-- `√(F_0 / ε)` of `thm:app-phase-matched`. -/
def matchedX (F0 ε : ℝ) : ℝ := Real.sqrt (F0 / ε)

/-- Private: forcing under equal drifts, `F(s) = F_0 e^{-2𝔡 s}`. -/
private lemma common_forcing [Fintype ι] (m : RowModel ι) (d : ℝ) (hdi : ∀ i, m.d i = d)
    (s : ℝ) : m.forcing s = m.F0 * Real.exp (-(2 * d * s)) := by
  unfold RowModel.forcing RowModel.F0
  rw [tsum_fintype, tsum_fintype]
  simp only [hdi, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Private: kernel under equal drifts, `k(s) = (η 𝔳_tot / 2) e^{-2𝔡 s}`. -/
private lemma common_kernel [Fintype ι] (m : RowModel ι) (d : ℝ) (hdi : ∀ i, m.d i = d)
    (s : ℝ) : m.kernel s = m.η * commonVtot m / 2 * Real.exp (-(2 * d * s)) := by
  unfold RowModel.kernel commonVtot
  rw [tsum_fintype]
  simp only [hdi]
  rw [← Finset.sum_mul]
  ring

/-- Private: `𝒮 = 𝔳_tot / (2 𝔡)` under equal drifts. -/
private lemma common_S [Fintype ι] (m : RowModel ι) (d : ℝ) (hdi : ∀ i, m.d i = d) :
    m.S = commonVtot m / (2 * d) := by
  unfold RowModel.S commonVtot
  rw [tsum_fintype, Finset.sum_div]
  simp only [hdi]

/-- Private: a global row solution exists when `𝒮 > 0`, from `thm_app_phase_volterra_i` and
`thm_app_phase_clock` (`tStar = ⊤`). -/
private lemma common_exists_global [Fintype ι] (m : RowModel ι) (hS : 0 < m.S) :
    ∃ Q : ι → ℝ → ℝ, IsGlobalRowSolution m Q := by
  obtain ⟨Q, hQ, -⟩ := thm_app_phase_volterra_i m
  obtain ⟨-, -, -, -, -, -, hsol, -, -, hSpos, -⟩ := thm_app_phase_clock m Q hQ
  have htop : tStar m Q = ⊤ := (hSpos hS).1
  refine ⟨rowsInStepTime m Q, ?_⟩
  intro t₁
  apply hsol t₁
  rw [htop]
  exact le_top

/-- Private: the risk of a global row solution has derivative
`-2𝔡η√𝔑 + η²𝔳_tot/2` within `[0, t₁)`. -/
private lemma common_risk_deriv [Fintype ι] (m : RowModel ι) (d : ℝ) (hdi : ∀ i, m.d i = d)
    (Q : ι → ℝ → ℝ) (hQ : IsGlobalRowSolution m Q) (t₁ : ℝ) (t : ℝ) (ht : t ∈ Ico (0:ℝ) t₁) :
    HasDerivWithinAt (m.risk Q)
      (-(2 * m.η * d) * Real.sqrt (m.risk Q t) + m.η ^ 2 * commonVtot m / 2)
      (Ico (0 : ℝ) t₁) t := by
  obtain ⟨-, -, -, hpos, hder⟩ := hQ t₁
  have hfun : m.risk Q = fun s => (1 / 2 : ℝ) * ∑ i, m.μ i * Q i s := by
    funext s
    unfold RowModel.risk
    rw [tsum_fintype]
  have hRpos := hpos t ht
  have hsum : HasDerivWithinAt (fun s => ∑ i, m.μ i * Q i s)
      (∑ i, m.μ i * (-(2 * m.η * m.d i) / Real.sqrt (m.risk Q t) * Q i t + m.η ^ 2 * m.v i))
      (Ico (0 : ℝ) t₁) t := by
    convert HasDerivWithinAt.sum (u := Finset.univ)
      (fun i (_ : i ∈ Finset.univ) => (hder t ht i).const_mul (m.μ i)) using 1
    funext s
    simp [Finset.sum_apply]
  have key := hsum.const_mul (1 / 2 : ℝ)
  rw [hfun]
  refine key.congr_deriv ?_
  simp only [hdi]
  have e1 : ∑ i, m.μ i * (-(2 * m.η * d) / Real.sqrt (m.risk Q t) * Q i t + m.η ^ 2 * m.v i)
      = -(2 * m.η * d) / Real.sqrt (m.risk Q t) * (∑ i, m.μ i * Q i t)
        + m.η ^ 2 * commonVtot m := by
    unfold commonVtot
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : (1 / 2 : ℝ) * ∑ i, m.μ i * Q i t = m.risk Q t := by
    unfold RowModel.risk
    rw [tsum_fintype]
  have e3 : ∑ i, m.μ i * Q i t = 2 * m.risk Q t := by
    rw [← e2]
    ring
  have hsq : Real.sqrt (m.risk Q t) ^ 2 = m.risk Q t := Real.sq_sqrt hRpos.le
  have hsqpos : 0 < Real.sqrt (m.risk Q t) := Real.sqrt_pos.2 hRpos
  rw [e1, e3]
  have hRs : m.risk Q t / Real.sqrt (m.risk Q t) = Real.sqrt (m.risk Q t) := by
    rw [div_eq_iff hsqpos.ne']
    exact (Real.mul_self_sqrt hRpos.le).symm
  have hexpr : -(2 * m.η * d) / Real.sqrt (m.risk Q t) * (2 * m.risk Q t)
      = -(2 * m.η * d) * 2 * (m.risk Q t / Real.sqrt (m.risk Q t)) := by ring
  rw [hexpr, hRs]
  ring

/-- Private: at `t = 0` the risk of a global solution is `F_0`, so `t_a = 0` when `F_0 ≤ a`
(`prop:app-phase-common`(ii), first clause). -/
private lemma common_firstHit_zero [Fintype ι] (m : RowModel ι) (Q : ι → ℝ → ℝ)
    (hQ : IsGlobalRowSolution m Q) (a : ℝ) (ha : m.F0 ≤ a) :
    firstHit (m.risk Q) a = 0 := by
  have h := (hQ 1).1
  have h0 : m.risk Q 0 = m.F0 := by
    unfold RowModel.risk RowModel.F0
    simp only [h]
  have h0le : m.risk Q ((0 : ℝ≥0) : ℝ) ≤ a := by
    simp [h0, ha]
  apply le_antisymm
  · unfold firstHit
    exact le_trans (iInf₂_le (0 : ℝ≥0) h0le) (by simp)
  · exact zero_le


private lemma cp_gron (u : ℝ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hpos : ∀ t, 0 ≤ t → 0 < u t) (hcont : ContinuousOn u (Ici 0))
    (hder : ∀ t, 0 < t → HasDerivAt u (-(a * (u t - b) / u t)) t) (T : ℝ) (hT : 0 < T) :
    ∃ K : ℝ, (u 0 - b) ^ 2 ≤ (u T - b) ^ 2 * Real.exp (2 * K * T) := by
  have hcT : ContinuousOn u (Icc 0 T) := hcont.mono (fun x hx => hx.1)
  obtain ⟨x0, hx0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT.le) hcT
  have hδ : 0 < u x0 := hpos x0 hx0.1
  refine ⟨a / u x0, ?_⟩
  set K := a / u x0 with hK
  let f : ℝ → ℝ := fun t => (u t - b) ^ 2 * Real.exp (2 * K * t)
  have hfc : ContinuousOn f (Icc 0 T) :=
    ((hcT.sub continuousOn_const).pow 2).mul (by fun_prop)
  have hfd : ∀ t ∈ Ioo (0:ℝ) T, HasDerivAt f
      ((2 * (u t - b) * (-(a * (u t - b) / u t))) * Real.exp (2 * K * t)
        + (u t - b) ^ 2 * (Real.exp (2 * K * t) * (2 * K))) t := by
    intro t ht
    have h1 := (((hder t ht.1).sub_const b).pow 2)
    have h2 := (((hasDerivAt_id t).const_mul (2 * K)).exp)
    refine HasDerivAt.congr_deriv (f := f) (h1.mul h2) ?_
    simp
  have hmono : MonotoneOn f (Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hfc
    · intro t ht
      rw [interior_Icc] at ht
      exact (hfd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hfd t ht).deriv]
      have hu : 0 < u t := hpos t ht.1.le
      have hle : u x0 ≤ u t := hmin (show t ∈ Icc 0 T from ⟨ht.1.le, ht.2.le⟩)
      have hKle : a / u t ≤ K := div_le_div_of_nonneg_left ha.le hδ hle
      have : (2 * (u t - b) * (-(a * (u t - b) / u t))) * Real.exp (2 * K * t)
          + (u t - b) ^ 2 * (Real.exp (2 * K * t) * (2 * K))
          = (u t - b) ^ 2 * Real.exp (2 * K * t) * (2 * (K - a / u t)) := by
        field_simp
        ring
      rw [this]
      have : 0 ≤ K - a / u t := sub_nonneg.2 hKle
      positivity
  have := hmono (left_mem_Icc.2 hT.le) (right_mem_Icc.2 hT.le) hT.le
  simp only [f] at this
  simpa using this

private lemma cp_ne (u : ℝ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hpos : ∀ t, 0 ≤ t → 0 < u t) (hcont : ContinuousOn u (Ici 0))
    (hder : ∀ t, 0 < t → HasDerivAt u (-(a * (u t - b) / u t)) t) (h0 : u 0 ≠ b) :
    ∀ t, 0 ≤ t → u t ≠ b := by
  intro t ht
  rcases ht.eq_or_lt with rfl | ht
  · exact h0
  obtain ⟨K, hK⟩ := cp_gron u a b ha hpos hcont hder t ht
  intro h
  rw [h] at hK
  have : 0 < (u 0 - b) ^ 2 := by
    have : u 0 - b ≠ 0 := sub_ne_zero.2 h0
    positivity
  simp at hK
  exact h0 (by linarith)

private lemma cp_const (u : ℝ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hpos : ∀ t, 0 ≤ t → 0 < u t) (hcont : ContinuousOn u (Ici 0))
    (hder : ∀ t, 0 < t → HasDerivAt u (-(a * (u t - b) / u t)) t) (h0 : u 0 = b) :
    ∀ t, 0 ≤ t → u t = b := by
  let g : ℝ → ℝ := fun t => (u t - b) ^ 2
  have hgc : ContinuousOn g (Ici 0) := (hcont.sub continuousOn_const).pow 2
  have hgd : ∀ t, 0 < t → HasDerivAt g (2 * (u t - b) * (-(a * (u t - b) / u t))) t := by
    intro t ht
    have h := ((hder t ht).sub_const b).pow 2
    refine HasDerivAt.congr_deriv (f := g) h ?_
    simp
  have hanti : AntitoneOn g (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hgc
    · intro t ht
      rw [interior_Ici] at ht
      exact (hgd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hgd t ht).deriv]
      have hu : 0 < u t := hpos t ht.le
      have : 2 * (u t - b) * (-(a * (u t - b) / u t)) = -(2 * a / u t * (u t - b) ^ 2) := by
        field_simp
      rw [this]
      have : 0 ≤ 2 * a / u t * (u t - b) ^ 2 := by positivity
      linarith
  intro t ht
  have h1 : g t ≤ g 0 := hanti (Set.mem_Ici.2 le_rfl) ht ht
  have h2 : g 0 = 0 := by simp [g, h0]
  have h3 : (u t - b) ^ 2 ≤ 0 := by simpa [g, h2] using h1
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h3 (sq_nonneg _))
  linarith


private lemma cp_side_gt (u : ℝ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hpos : ∀ t, 0 ≤ t → 0 < u t) (hcont : ContinuousOn u (Ici 0))
    (hder : ∀ t, 0 < t → HasDerivAt u (-(a * (u t - b) / u t)) t) (h0 : b < u 0) :
    ∀ t, 0 ≤ t → b < u t := by
  have hne := cp_ne u a b ha hpos hcont hder h0.ne'
  intro t ht
  by_contra hlt
  push Not at hlt
  have hc : ContinuousOn u (Icc 0 t) := hcont.mono (fun x hx => hx.1)
  obtain ⟨s, hs, hsb⟩ := intermediate_value_Icc' ht hc ⟨hlt, h0.le⟩
  exact hne s hs.1 hsb

private lemma cp_side_lt (u : ℝ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hpos : ∀ t, 0 ≤ t → 0 < u t) (hcont : ContinuousOn u (Ici 0))
    (hder : ∀ t, 0 < t → HasDerivAt u (-(a * (u t - b) / u t)) t) (h0 : u 0 < b) :
    ∀ t, 0 ≤ t → u t < b := by
  have hne := cp_ne u a b ha hpos hcont hder h0.ne
  intro t ht
  by_contra hlt
  push Not at hlt
  have hc : ContinuousOn u (Icc 0 t) := hcont.mono (fun x hx => hx.1)
  obtain ⟨s, hs, hsb⟩ := intermediate_value_Icc ht hc ⟨h0.le, hlt⟩
  exact hne s hs.1 hsb

private lemma cp_anti (u : ℝ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hpos : ∀ t, 0 ≤ t → 0 < u t) (hcont : ContinuousOn u (Ici 0))
    (hder : ∀ t, 0 < t → HasDerivAt u (-(a * (u t - b) / u t)) t) (h0 : b < u 0) :
    StrictAntiOn u (Ici 0) ∧ Tendsto u atTop (𝓝 b) := by
  have hgt := cp_side_gt u a b ha hpos hcont hder h0
  have hanti : StrictAntiOn u (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0) hcont
    intro t ht
    rw [interior_Ici] at ht
    rw [(hder t ht).deriv]
    have h1 := hpos t ht.le
    have h2 := hgt t ht.le
    have : 0 < a * (u t - b) / u t := by
      have : 0 < u t - b := by linarith
      positivity
    linarith
  refine ⟨hanti, ?_⟩
  have key : ∀ ε : ℝ, 0 < ε → ∃ t, 0 ≤ t ∧ u t - b < ε := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    set c := a * ε / u 0 with hc
    have hcpos : 0 < c := by
      have := hpos 0 le_rfl
      positivity
    let g : ℝ → ℝ := fun t => u t + c * t
    have hgc : ContinuousOn g (Ici 0) := hcont.add (by fun_prop)
    have hgd : ∀ t, 0 < t → HasDerivAt g (-(a * (u t - b) / u t) + c * 1) t := by
      intro t ht
      exact (hder t ht).add ((hasDerivAt_id t).const_mul c)
    have hgm : AntitoneOn g (Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hgc
      · intro t ht
        rw [interior_Ici] at ht
        exact (hgd t ht).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        rw [(hgd t ht).deriv]
        have hle : u t ≤ u 0 := hanti.antitoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht.le) ht.le
        have hu := hpos t ht.le
        have h0' := hpos 0 le_rfl
        have : c ≤ a * (u t - b) / u t := by
          calc c = a * ε / u 0 := rfl
            _ ≤ a * ε / u t := div_le_div_of_nonneg_left (by positivity) hu hle
            _ ≤ a * (u t - b) / u t :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hcon t ht.le) ha.le) hu.le
        linarith
    have hT : (0:ℝ) ≤ u 0 / c := by
      have := hpos 0 le_rfl
      positivity
    have h1 : g (u 0 / c) ≤ g 0 := hgm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hT) hT
    simp only [g] at h1
    have : c * (u 0 / c) = u 0 := by field_simp
    have h2 := hpos (u 0 / c) hT
    simp at h1
    linarith
  rw [tendsto_order]
  constructor
  · intro a' ha'
    filter_upwards [eventually_ge_atTop 0] with t ht
    have := hgt t ht
    linarith
  · intro a' ha'
    obtain ⟨t0, ht0, hlt⟩ := key (a' - b) (by linarith)
    filter_upwards [eventually_ge_atTop t0] with t ht
    have := hanti.antitoneOn (Set.mem_Ici.2 ht0) (Set.mem_Ici.2 (ht0.trans ht)) ht
    linarith

private lemma cp_mono (u : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hpos : ∀ t, 0 ≤ t → 0 < u t) (hcont : ContinuousOn u (Ici 0))
    (hder : ∀ t, 0 < t → HasDerivAt u (-(a * (u t - b) / u t)) t) (h0 : u 0 < b) :
    StrictMonoOn u (Ici 0) ∧ Tendsto u atTop (𝓝 b) := by
  have hlt := cp_side_lt u a b ha hpos hcont hder h0
  have hmono : StrictMonoOn u (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hcont
    intro t ht
    rw [interior_Ici] at ht
    rw [(hder t ht).deriv]
    have h1 := hpos t ht.le
    have h2 := hlt t ht.le
    have : a * (u t - b) / u t < 0 := by
      have : u t - b < 0 := by linarith
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha this) h1
    linarith
  refine ⟨hmono, ?_⟩
  have key : ∀ ε : ℝ, 0 < ε → ∃ t, 0 ≤ t ∧ b - u t < ε := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    set c := a * ε / b with hc
    have hcpos : 0 < c := by positivity
    let g : ℝ → ℝ := fun t => u t - c * t
    have hgc : ContinuousOn g (Ici 0) := hcont.sub (by fun_prop)
    have hgd : ∀ t, 0 < t → HasDerivAt g (-(a * (u t - b) / u t) - c * 1) t := by
      intro t ht
      exact (hder t ht).sub ((hasDerivAt_id t).const_mul c)
    have hgm : MonotoneOn g (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hgc
      · intro t ht
        rw [interior_Ici] at ht
        exact (hgd t ht).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        rw [(hgd t ht).deriv]
        have hu := hpos t ht.le
        have hub := hlt t ht.le
        have : c ≤ a * (b - u t) / u t := by
          calc c = a * ε / b := rfl
            _ ≤ a * ε / u t := div_le_div_of_nonneg_left (by positivity) hu hub.le
            _ ≤ a * (b - u t) / u t :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hcon t ht.le) ha.le) hu.le
        have e : -(a * (u t - b) / u t) = a * (b - u t) / u t := by ring
        linarith
    have hT : (0:ℝ) ≤ b / c := by positivity
    have h1 : g 0 ≤ g (b / c) := hgm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hT) hT
    simp only [g] at h1
    have : c * (b / c) = b := by field_simp
    have h2 := hlt (b / c) hT
    have h3 := hpos 0 le_rfl
    simp at h1
    linarith
  rw [tendsto_order]
  constructor
  · intro a' ha'
    obtain ⟨t0, ht0, hlt'⟩ := key (b - a') (by linarith)
    filter_upwards [eventually_ge_atTop t0] with t ht
    have := hmono.monotoneOn (Set.mem_Ici.2 ht0) (Set.mem_Ici.2 (ht0.trans ht)) ht
    linarith
  · intro a' ha'
    filter_upwards [eventually_ge_atTop 0] with t ht
    have := hlt t ht
    linarith

private lemma cp_impl (u : ℝ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hpos : ∀ t, 0 ≤ t → 0 < u t) (hcont : ContinuousOn u (Ici 0))
    (hder : ∀ t, 0 < t → HasDerivAt u (-(a * (u t - b) / u t)) t) (h0 : u 0 ≠ b) :
    ∀ t, 0 ≤ t → a * t = u 0 - u t + b * Real.log (|u 0 - b| / |u t - b|) := by
  have hne := cp_ne u a b ha hpos hcont hder h0
  let G : ℝ → ℝ := fun t => u t + b * Real.log (u t - b) + a * t
  have hGc : ContinuousOn G (Ici 0) := by
    refine (hcont.add (continuousOn_const.mul ?_)).add (by fun_prop)
    exact (hcont.sub continuousOn_const).log (fun t ht => sub_ne_zero.2 (hne t ht))
  have hGd : ∀ t, 0 < t → HasDerivAt G 0 t := by
    intro t ht
    have h1 := (hder t ht).sub_const b
    have hw : u t - b ≠ 0 := sub_ne_zero.2 (hne t ht.le)
    have h2 := (h1.log hw).const_mul b
    have h3 := ((hder t ht).add h2).add ((hasDerivAt_id t).const_mul a)
    have hu := hpos t ht.le
    refine HasDerivAt.congr_deriv (f := G) h3 ?_
    field_simp
    ring
  have hG0 : ∀ t, 0 ≤ t → G t = G 0 := by
    intro t ht
    have hm : MonotoneOn G (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hGc
      · intro x hx
        rw [interior_Ici] at hx
        exact (hGd x hx).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ici] at hx
        rw [(hGd x hx).deriv]
    have ha' : AntitoneOn G (Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hGc
      · intro x hx
        rw [interior_Ici] at hx
        exact (hGd x hx).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ici] at hx
        rw [(hGd x hx).deriv]
    exact le_antisymm (ha' (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht)
      (hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht)
  intro t ht
  have h := hG0 t ht
  simp only [G] at h
  have e : Real.log (|u 0 - b| / |u t - b|) = Real.log (u 0 - b) - Real.log (u t - b) := by
    rw [Real.log_div (abs_ne_zero.2 (sub_ne_zero.2 h0)) (abs_ne_zero.2 (sub_ne_zero.2 (hne t ht))),
      Real.log_abs, Real.log_abs]
  rw [e]
  simp at h
  linarith


/-- Private: `risk Q 0 = F_0` for a global solution. -/
private lemma common_risk_zero [Fintype ι] (m : RowModel ι) (Q : ι → ℝ → ℝ)
    (hQ : IsGlobalRowSolution m Q) : m.risk Q 0 = m.F0 := by
  have h := (hQ 1).1
  unfold RowModel.risk RowModel.F0
  simp only [h]

/-- Private: `u = √𝔑` satisfies the hypotheses of the abstract lemmas `cp_*`. -/
private lemma common_bridge [Fintype ι] (m : RowModel ι) (d : ℝ) (hd : 0 < d)
    (hdi : ∀ i, m.d i = d) (hv : 0 < commonVtot m) (Q : ι → ℝ → ℝ)
    (hQ : IsGlobalRowSolution m Q) :
    (∀ t : ℝ, 0 ≤ t → 0 < Real.sqrt (m.risk Q t)) ∧
    ContinuousOn (fun t => Real.sqrt (m.risk Q t)) (Ici (0 : ℝ)) ∧
    (∀ t : ℝ, 0 < t → HasDerivAt (fun s => Real.sqrt (m.risk Q s))
      (-(commonA m d * (Real.sqrt (m.risk Q t) - commonB m d) / Real.sqrt (m.risk Q t))) t) := by
  have hRpos : ∀ t : ℝ, 0 ≤ t → 0 < m.risk Q t := fun t ht =>
    (hQ (t + 1)).2.2.2.1 t ⟨ht, by linarith⟩
  refine ⟨fun t ht => Real.sqrt_pos.2 (hRpos t ht), ?_, ?_⟩
  · intro x hx
    have hx' : (0 : ℝ) ≤ x := hx
    have hc := ((hQ (x + 1)).2.2.1 x ⟨hx', by linarith⟩)
    have hmem : Ico (0 : ℝ) (x + 1) ∈ 𝓝[Ici (0 : ℝ)] x :=
      mem_nhdsWithin.2 ⟨Iio (x + 1), isOpen_Iio, by simp, fun y hy => ⟨hy.2, hy.1⟩⟩
    exact (Real.continuous_sqrt.continuousAt.comp_continuousWithinAt
      (hc.mono_of_mem_nhdsWithin hmem))
  · intro t ht
    have hmem : Ico (0 : ℝ) (t + 1) ∈ 𝓝 t := Ico_mem_nhds ht (by linarith)
    have hd1 := (common_risk_deriv m d hdi Q hQ (t + 1) t ⟨ht.le, by linarith⟩).hasDerivAt hmem
    have h2 := hd1.sqrt (hRpos t ht.le).ne'
    refine HasDerivAt.congr_deriv h2 ?_
    have hs : 0 < Real.sqrt (m.risk Q t) := Real.sqrt_pos.2 (hRpos t ht.le)
    unfold commonA commonB
    field_simp
    ring

private lemma common_hit_eq (R : ℝ → ℝ) (a t : ℝ) (ht : 0 ≤ t)
    (h : ∀ s : ℝ, 0 ≤ s → (R s ≤ a ↔ t ≤ s)) : firstHit R a = ENNReal.ofReal t := by
  unfold firstHit
  apply le_antisymm
  · have h1 : R ((t.toNNReal : ℝ≥0) : ℝ) ≤ a := by
      rw [Real.coe_toNNReal t ht]
      exact (h t ht).2 le_rfl
    exact iInf₂_le t.toNNReal h1
  · refine le_iInf₂ fun s hs => ?_
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2
    have := (h s hs0).1 hs
    calc ENNReal.ofReal t ≤ ENNReal.ofReal (s : ℝ) := ENNReal.ofReal_le_ofReal this
      _ = (s : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

/-- `prop:app-phase-common`, snapshot `cr-2026-10-23`. Part (i) carries the preamble of the
statement (the explicit forcing, kernel and `𝒮`, the existence of a global solution, and the
risk ODE `eqn:app-phase-scalar-ode`), which holds for every model in the setting; the
implicit formula `eqn:app-phase-implicit` and the monotonicity/limit claims are the clauses
(i) of the source.

LaTeX (verbatim, `section.tex` l.539–563):
```
\begin{proposition}[Common drift]\label{prop:app-phase-common}
Assume (M1) with a finite index set, $\mathfrak d_i=\mathfrak d>0$ for all $i$
and $\mathfrak v_{\rm tot}>0$. Then
\[
F(s)=F_0e^{-2\mathfrak ds},\qquad k(s)=\frac{\lr\mathfrak v_{\rm tot}}2e^{-2\mathfrak ds},\qquad \mathcal S=\frac{\mathfrak v_{\rm tot}}{2\mathfrak d},
\]
and the risk solves
\begin{equation}\label{eqn:app-phase-scalar-ode}
\frac{\dif\fRisk}{\dif t}=-2\lr\mathfrak d\sqrt{\fRisk}+\frac{\lr^2\mathfrak v_{\rm tot}}2 .
\end{equation}
Put $a_\circ\defeq\lr\mathfrak d$, $b_\circ\defeq\lr\mathfrak v_{\rm tot}/(4\mathfrak d)=\lr\mathcal S/2$ and
$u_0\defeq\sqrt{F_0}$.
\begin{enumerate}[label=(\roman*)]
\item If $u_0\ne b_\circ$, then for every $t\ge0$
\begin{equation}\label{eqn:app-phase-implicit}
a_\circ t=u_0-\sqrt{\fRisk(t)}+b_\circ\log\frac{\abs{u_0-b_\circ}}{\abs{\sqrt{\fRisk(t)}-b_\circ}} ,
\end{equation}
and $\sqrt{\fRisk}$ is strictly decreasing with limit $b_\circ$ if $u_0>b_\circ$,
strictly increasing with limit $b_\circ$ if $u_0<b_\circ$, and never equal to
$b_\circ$. If $u_0=b_\circ$, then $\fRisk\equiv b_\circ^2$.
\item Let $a\ge0$. If $F_0\le a$, then $t_a=0$. If $F_0>a$, then $t_a<\infty$
if and only if $a>b_\circ^2$, and then $t_a$ is given by
\cref{eqn:app-phase-implicit} with $\sqrt{\fRisk(t)}=\sqrt a$.
\end{enumerate}
\end{proposition}
```
-/
theorem prop_app_phase_common_i [Fintype ι] (m : RowModel ι) (d : ℝ) (hd : 0 < d)
    (hdi : ∀ i, m.d i = d) (hv : 0 < commonVtot m) :
    (∀ s : ℝ, 0 ≤ s → m.forcing s = m.F0 * Real.exp (-(2 * d * s))) ∧
    (∀ s : ℝ, 0 ≤ s → m.kernel s = m.η * commonVtot m / 2 * Real.exp (-(2 * d * s))) ∧
    m.S = commonVtot m / (2 * d) ∧
    (∃ Q : ι → ℝ → ℝ, IsGlobalRowSolution m Q) ∧
    (∀ Q : ι → ℝ → ℝ, IsGlobalRowSolution m Q → ∀ t₁ : ℝ, ∀ t ∈ Ico (0 : ℝ) t₁,
      HasDerivWithinAt (m.risk Q)
        (-(2 * m.η * d) * Real.sqrt (m.risk Q t) + m.η ^ 2 * commonVtot m / 2)
        (Ico (0 : ℝ) t₁) t) ∧
    (∀ Q : ι → ℝ → ℝ, IsGlobalRowSolution m Q →
      (Real.sqrt m.F0 ≠ commonB m d →
        (∀ t : ℝ, 0 ≤ t →
          commonA m d * t = Real.sqrt m.F0 - Real.sqrt (m.risk Q t)
            + commonB m d * Real.log (|Real.sqrt m.F0 - commonB m d|
              / |Real.sqrt (m.risk Q t) - commonB m d|)) ∧
        (∀ t : ℝ, 0 ≤ t → Real.sqrt (m.risk Q t) ≠ commonB m d) ∧
        (commonB m d < Real.sqrt m.F0 →
          StrictAntiOn (fun t => Real.sqrt (m.risk Q t)) (Ici (0 : ℝ)) ∧
          Tendsto (fun t => Real.sqrt (m.risk Q t)) atTop (𝓝 (commonB m d))) ∧
        (Real.sqrt m.F0 < commonB m d →
          StrictMonoOn (fun t => Real.sqrt (m.risk Q t)) (Ici (0 : ℝ)) ∧
          Tendsto (fun t => Real.sqrt (m.risk Q t)) atTop (𝓝 (commonB m d)))) ∧
      (Real.sqrt m.F0 = commonB m d → ∀ t : ℝ, 0 ≤ t → m.risk Q t = commonB m d ^ 2)) := by
  have hη := m.η_pos
  have hA : 0 < commonA m d := mul_pos hη hd
  have hB : 0 < commonB m d := by
    unfold commonB
    have := m.η_pos
    positivity
  refine ⟨fun s _ => common_forcing m d hdi s, fun s _ => common_kernel m d hdi s,
    common_S m d hdi, ?_, fun Q hQ t₁ t ht => common_risk_deriv m d hdi Q hQ t₁ t ht, ?_⟩
  · exact common_exists_global m (by rw [common_S m d hdi]; positivity)
  intro Q hQ
  obtain ⟨hpos, hcont, hder⟩ := common_bridge m d hd hdi hv Q hQ
  have hR0 := common_risk_zero m Q hQ
  have hu0 : (fun t => Real.sqrt (m.risk Q t)) 0 = Real.sqrt m.F0 := by simp [hR0]
  refine ⟨fun hne => ?_, fun heq t ht => ?_⟩
  · have hne' : (fun t => Real.sqrt (m.risk Q t)) 0 ≠ commonB m d := by rw [hu0]; exact hne
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      have := cp_impl _ _ _ hA hpos hcont hder hne' t ht
      simp only [hR0] at this
      exact this
    · exact cp_ne _ _ _ hA hpos hcont hder hne'
    · intro hlt
      have hlt' : commonB m d < (fun t => Real.sqrt (m.risk Q t)) 0 := by rw [hu0]; exact hlt
      exact cp_anti _ _ _ hA hpos hcont hder hlt'
    · intro hlt
      have hlt' : (fun t => Real.sqrt (m.risk Q t)) 0 < commonB m d := by rw [hu0]; exact hlt
      exact cp_mono _ _ _ hA hB hpos hcont hder hlt'
  · have h0' : (fun t => Real.sqrt (m.risk Q t)) 0 = commonB m d := by rw [hu0]; exact heq
    have := cp_const _ _ _ hA hpos hcont hder h0' t ht
    have hRt := hpos t ht
    have e : m.risk Q t = Real.sqrt (m.risk Q t) ^ 2 := by
      rw [Real.sq_sqrt]
      by_contra hneg
      push Not at hneg
      have := Real.sqrt_eq_zero_of_nonpos hneg.le
      linarith
    rw [e]
    rw [this]

/-- `prop:app-phase-common`, snapshot `cr-2026-10-23`, part (ii): the first-hit times `t_a`
of the risk of a global solution, for `a ≥ 0`. `firstHit` is `ℝ≥0∞`-valued, so `inf ∅ = ⊤`
is the paper's convention (l.47–48).

LaTeX (verbatim, `section.tex` l.539–563, the same proposition as part (i)):
```
\begin{proposition}[Common drift]\label{prop:app-phase-common}
Assume (M1) with a finite index set, $\mathfrak d_i=\mathfrak d>0$ for all $i$
and $\mathfrak v_{\rm tot}>0$. Then
\[
F(s)=F_0e^{-2\mathfrak ds},\qquad k(s)=\frac{\lr\mathfrak v_{\rm tot}}2e^{-2\mathfrak ds},\qquad \mathcal S=\frac{\mathfrak v_{\rm tot}}{2\mathfrak d},
\]
and the risk solves
\begin{equation}\label{eqn:app-phase-scalar-ode}
\frac{\dif\fRisk}{\dif t}=-2\lr\mathfrak d\sqrt{\fRisk}+\frac{\lr^2\mathfrak v_{\rm tot}}2 .
\end{equation}
Put $a_\circ\defeq\lr\mathfrak d$, $b_\circ\defeq\lr\mathfrak v_{\rm tot}/(4\mathfrak d)=\lr\mathcal S/2$ and
$u_0\defeq\sqrt{F_0}$.
\begin{enumerate}[label=(\roman*)]
\item If $u_0\ne b_\circ$, then for every $t\ge0$
\begin{equation}\label{eqn:app-phase-implicit}
a_\circ t=u_0-\sqrt{\fRisk(t)}+b_\circ\log\frac{\abs{u_0-b_\circ}}{\abs{\sqrt{\fRisk(t)}-b_\circ}} ,
\end{equation}
and $\sqrt{\fRisk}$ is strictly decreasing with limit $b_\circ$ if $u_0>b_\circ$,
strictly increasing with limit $b_\circ$ if $u_0<b_\circ$, and never equal to
$b_\circ$. If $u_0=b_\circ$, then $\fRisk\equiv b_\circ^2$.
\item Let $a\ge0$. If $F_0\le a$, then $t_a=0$. If $F_0>a$, then $t_a<\infty$
if and only if $a>b_\circ^2$, and then $t_a$ is given by
\cref{eqn:app-phase-implicit} with $\sqrt{\fRisk(t)}=\sqrt a$.
\end{enumerate}
\end{proposition}
```
-/
theorem prop_app_phase_common_ii [Fintype ι] (m : RowModel ι) (d : ℝ) (hd : 0 < d)
    (hdi : ∀ i, m.d i = d) (hv : 0 < commonVtot m) :
    ∀ Q : ι → ℝ → ℝ, IsGlobalRowSolution m Q → ∀ a : ℝ, 0 ≤ a →
      (m.F0 ≤ a → firstHit (m.risk Q) a = 0) ∧
      (a < m.F0 →
        (firstHit (m.risk Q) a ≠ ⊤ ↔ commonB m d ^ 2 < a) ∧
        (commonB m d ^ 2 < a →
          ∃ t : ℝ, 0 ≤ t ∧ firstHit (m.risk Q) a = ENNReal.ofReal t ∧
            commonA m d * t = Real.sqrt m.F0 - Real.sqrt a
              + commonB m d * Real.log (|Real.sqrt m.F0 - commonB m d|
                / |Real.sqrt a - commonB m d|))) := by
  intro Q hQ a ha
  have hη := m.η_pos
  have hA : 0 < commonA m d := mul_pos hη hd
  have hB : 0 < commonB m d := by
    unfold commonB
    positivity
  obtain ⟨hpos, hcont, hder⟩ := common_bridge m d hd hdi hv Q hQ
  have hR0 := common_risk_zero m Q hQ
  have hu0 : (fun t => Real.sqrt (m.risk Q t)) 0 = Real.sqrt m.F0 := by simp [hR0]
  refine ⟨common_firstHit_zero m Q hQ a, fun hlt => ?_⟩
  have hsa : Real.sqrt a < Real.sqrt m.F0 := Real.sqrt_lt_sqrt ha hlt
  have hle_iff : ∀ s : ℝ, 0 ≤ s → (m.risk Q s ≤ a ↔ Real.sqrt (m.risk Q s) ≤ Real.sqrt a) := by
    intro s hs
    exact (Real.sqrt_le_sqrt_iff ha).symm
  by_cases hba : commonB m d ^ 2 < a
  · have hBs : commonB m d < Real.sqrt a := (Real.lt_sqrt hB.le).2 hba
    have hlt' : commonB m d < (fun t => Real.sqrt (m.risk Q t)) 0 := by
      rw [hu0]; exact hBs.trans hsa
    obtain ⟨hanti, hlim⟩ := cp_anti _ _ _ hA hpos hcont hder hlt'
    have hev := (tendsto_order.1 hlim).2 (Real.sqrt a) hBs
    obtain ⟨T0, hT0⟩ := eventually_atTop.1 hev
    set T := max T0 0 with hT
    have hT0' : 0 ≤ T := le_max_right _ _
    have hcT : ContinuousOn (fun t => Real.sqrt (m.risk Q t)) (Icc 0 T) :=
      hcont.mono (fun x hx => hx.1)
    have hmem : Real.sqrt a ∈ Icc ((fun t => Real.sqrt (m.risk Q t)) T)
        ((fun t => Real.sqrt (m.risk Q t)) 0) := by
      refine ⟨(hT0 T (le_max_left _ _)).le, ?_⟩
      rw [hu0]; exact hsa.le
    obtain ⟨t, ht, htv⟩ := intermediate_value_Icc' hT0' hcT hmem
    have ht0 : 0 ≤ t := ht.1
    have hhit : firstHit (m.risk Q) a = ENNReal.ofReal t := by
      apply common_hit_eq _ _ _ ht0
      intro s hs
      rw [hle_iff s hs]
      rw [← htv]
      exact hanti.le_iff_ge (Set.mem_Ici.2 hs) (Set.mem_Ici.2 ht0)
    refine ⟨⟨fun _ => hba, fun _ => ?_⟩, fun _ => ⟨t, ht0, hhit, ?_⟩⟩
    · rw [hhit]; exact ENNReal.ofReal_ne_top
    · have hne' : (fun t => Real.sqrt (m.risk Q t)) 0 ≠ commonB m d := by
        rw [hu0]; exact (hBs.trans hsa).ne'
      have := cp_impl _ _ _ hA hpos hcont hder hne' t ht0
      simp only [hR0] at this
      simp only at this htv
      rw [htv] at this
      exact this
  · push Not at hba
    have hsB : Real.sqrt a ≤ commonB m d := by
      calc Real.sqrt a ≤ Real.sqrt (commonB m d ^ 2) := Real.sqrt_le_sqrt hba
        _ = commonB m d := Real.sqrt_sq hB.le
    have hall : ∀ t : ℝ, 0 ≤ t → Real.sqrt a < Real.sqrt (m.risk Q t) := by
      intro t ht
      rcases lt_trichotomy ((fun t => Real.sqrt (m.risk Q t)) 0) (commonB m d) with h | h | h
      · obtain ⟨hmo, -⟩ := cp_mono _ _ _ hA hB hpos hcont hder h
        have := hmo.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
        simp only [hR0] at this
        linarith
      · have := cp_const _ _ _ hA hpos hcont hder h t ht
        rw [hu0] at h
        linarith
      · have := cp_side_gt _ _ _ hA hpos hcont hder h t ht
        linarith
    have hfh : firstHit (m.risk Q) a = ⊤ := by
      unfold firstHit
      refine iInf_eq_top.2 fun s => iInf_eq_top.2 fun hs => ?_
      exfalso
      have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2
      have := hall s hs0
      have := (hle_iff s hs0).1 hs
      linarith
    refine ⟨⟨fun h => absurd hfh h, fun h => absurd h (not_lt.2 hba)⟩, fun h => absurd h (not_lt.2 hba)⟩

/-- Private: the matched step gives floor `commonB = √ε` and `commonA = 4𝔡²√ε/𝔳_tot`. -/
private lemma matched_consts [Fintype ι] (m : RowModel ι) (d : ℝ) (hd : 0 < d)
    (hdi : ∀ i, m.d i = d) (hv : 0 < commonVtot m) (ε : ℝ)
    (hη : m.η = 2 * Real.sqrt ε / m.S) :
    commonB m d = Real.sqrt ε ∧ commonA m d = 4 * d ^ 2 * Real.sqrt ε / commonVtot m := by
  have hS := (prop_app_phase_common_i m d hd hdi hv).2.2.1
  have hv' : commonVtot m ≠ 0 := hv.ne'
  have hd' : d ≠ 0 := hd.ne'
  rw [hS] at hη
  constructor
  · unfold commonB
    rw [hη]
    field_simp
    ring
  · unfold commonA
    rw [hη]
    field_simp
    ring

/-- Private: `√F₀ = X √ε` with `X = √(F₀/ε)`. -/
private lemma matched_sqrt_F0 (F0 ε : ℝ) (hF0 : 0 ≤ F0) (hε : 0 < ε) :
    Real.sqrt F0 = matchedX F0 ε * Real.sqrt ε := by
  unfold matchedX
  rw [← Real.sqrt_mul (div_nonneg hF0 hε.le), div_mul_cancel₀ _ hε.ne']

/-- Private: `1 < √T < X`. -/
private lemma matched_X_facts (F0 ε T : ℝ) (hε : 0 < ε) (hT : 1 < T) (hF : T * ε < F0) :
    1 < Real.sqrt T ∧ Real.sqrt T < matchedX F0 ε := by
  refine ⟨(Real.lt_sqrt zero_le_one).2 (by norm_num; linarith), ?_⟩
  unfold matchedX
  apply Real.sqrt_lt_sqrt (by linarith)
  rw [lt_div_iff₀ hε]
  exact hF

/-- Private: the bracket `X - √T + log((X-1)/(√T-1))` is positive when `1 < √T < X`. -/
private lemma matched_B_pos (X T : ℝ) (h1 : 1 < Real.sqrt T) (h2 : Real.sqrt T < X) :
    0 < X - Real.sqrt T + Real.log ((X - 1) / (Real.sqrt T - 1)) := by
  have hq : 1 ≤ (X - 1) / (Real.sqrt T - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have := Real.log_nonneg hq
  linarith

/-- Private: the exact matched hitting time `t_{Tε}`. -/
private lemma matched_hit [Fintype ι] (m : RowModel ι) (d : ℝ) (hd : 0 < d)
    (hdi : ∀ i, m.d i = d) (hv : 0 < commonVtot m) (ε T : ℝ) (hε : 0 < ε) (hT : 1 < T)
    (hF : T * ε < m.F0) (hη : m.η = 2 * Real.sqrt ε / m.S) (Q : ι → ℝ → ℝ)
    (hQ : IsGlobalRowSolution m Q) :
    firstHit (m.risk Q) (T * ε) = ENNReal.ofReal (commonVtot m / (4 * d ^ 2) *
      (matchedX m.F0 ε - Real.sqrt T + Real.log ((matchedX m.F0 ε - 1) / (Real.sqrt T - 1)))) := by
  obtain ⟨hB, hA⟩ := matched_consts m d hd hdi hv ε hη
  obtain ⟨h1, h2⟩ := matched_X_facts m.F0 ε T hε hT hF
  have hF0 : 0 ≤ m.F0 := by nlinarith
  have hTε : 0 ≤ T * ε := by nlinarith
  have hb2 : commonB m d ^ 2 < T * ε := by
    rw [hB, Real.sq_sqrt hε.le]
    nlinarith
  obtain ⟨t, ht0, hfh, hform⟩ :=
    ((prop_app_phase_common_ii m d hd hdi hv Q hQ (T * ε) hTε).2 hF).2 hb2
  have hsF := matched_sqrt_F0 m.F0 ε hF0 hε
  have hsT : Real.sqrt (T * ε) = Real.sqrt T * Real.sqrt ε := Real.sqrt_mul (by linarith) ε
  rw [hB, hsF, hsT] at hform
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hXs : 0 < matchedX m.F0 ε - 1 := by linarith
  have hTs : 0 < Real.sqrt T - 1 := by linarith
  have e1 : |matchedX m.F0 ε * Real.sqrt ε - Real.sqrt ε|
      = Real.sqrt ε * (matchedX m.F0 ε - 1) := by
    rw [show matchedX m.F0 ε * Real.sqrt ε - Real.sqrt ε
      = Real.sqrt ε * (matchedX m.F0 ε - 1) by ring]
    exact abs_of_pos (mul_pos hs hXs)
  have e2 : |Real.sqrt T * Real.sqrt ε - Real.sqrt ε| = Real.sqrt ε * (Real.sqrt T - 1) := by
    rw [show Real.sqrt T * Real.sqrt ε - Real.sqrt ε = Real.sqrt ε * (Real.sqrt T - 1) by ring]
    exact abs_of_pos (mul_pos hs hTs)
  rw [e1, e2, mul_div_mul_left _ _ hs.ne', hA] at hform
  have hd2 : 0 < 4 * d ^ 2 := by have := pow_pos hd 2; linarith
  have hc : 4 * d ^ 2 * Real.sqrt ε / commonVtot m ≠ 0 :=
    (div_pos (mul_pos hd2 hs) hv).ne'
  have key : t = commonVtot m / (4 * d ^ 2) *
      (matchedX m.F0 ε - Real.sqrt T + Real.log ((matchedX m.F0 ε - 1) / (Real.sqrt T - 1))) := by
    apply mul_left_cancel₀ hc
    rw [hform]
    field_simp
  rw [hfh, key]

/-- `thm:app-phase-matched`, snapshot `cr-2026-10-23`: matched floors, the exact hitting time
`t_{Tε}`, its error bound, and the two-model ratio. The matched step is
`η = 2√ε/𝒮` (`= 4𝔡√ε/𝔳_tot`, which is the same number by `prop_app_phase_common_i`).
The ratio clause takes a second model `m₂` in the same setting with the same `F_0`.

LaTeX (verbatim, `section.tex` l.603–618):
```
\begin{theorem}[Matched floors]\label{thm:app-phase-matched}
In the setting of \cref{prop:app-phase-common}, let $\epsilon>0$, $T>1$ and
$F_0>T\epsilon$, and take the matched step $\lr=2\sqrt\epsilon/\mathcal S=4\mathfrak d\sqrt\epsilon/\mathfrak v_{\rm tot}$.
Put $X\defeq\sqrt{F_0/\epsilon}>\sqrt T$. Then the floor is $\epsilon$ and
\begin{equation}\label{eqn:app-phase-iso-time}
t_{T\epsilon}=\frac{\mathfrak v_{\rm tot}}{4\mathfrak d^2}\Big[X-\sqrt T+\log\frac{X-1}{\sqrt T-1}\Big].
\end{equation}
If $x\defeq1/X\le\frac12$, then
\begin{equation}\label{eqn:app-phase-iso-error}
\Big|\frac{t_{T\epsilon}}{\frac{\mathfrak v_{\rm tot}}{4\mathfrak d^2}\sqrt{F_0/\epsilon}}-1\Big|\le x\Big[\sqrt T+\abs{\log(\sqrt T-1)}+\log\frac1x+2x\Big].
\end{equation}
For two such models with the same $F_0$, $\epsilon$ and $T$,
\[
\frac{t^{(1)}_{T\epsilon}}{t^{(2)}_{T\epsilon}}=\frac{\mathfrak v^{(1)}_{\rm tot}/(\mathfrak d^{(1)})^2}{\mathfrak v^{(2)}_{\rm tot}/(\mathfrak d^{(2)})^2} .
\]
\end{theorem}
```
-/
theorem thm_app_phase_matched [Fintype ι] (m : RowModel ι) (d : ℝ) (hd : 0 < d)
    (hdi : ∀ i, m.d i = d) (hv : 0 < commonVtot m) (ε T : ℝ) (hε : 0 < ε) (hT : 1 < T)
    (hF : T * ε < m.F0) (hη : m.η = 2 * Real.sqrt ε / m.S)
    {ι₂ : Type*} [Fintype ι₂] (m₂ : RowModel ι₂) (d₂ : ℝ) (hd₂ : 0 < d₂)
    (hdi₂ : ∀ i, m₂.d i = d₂) (hv₂ : 0 < commonVtot m₂)
    (hη₂ : m₂.η = 2 * Real.sqrt ε / m₂.S) (hF₂ : T * ε < m₂.F0) (hF₂eq : m₂.F0 = m.F0) :
    (∀ Q : ι → ℝ → ℝ, IsGlobalRowSolution m Q →
      Tendsto (m.risk Q) atTop (𝓝 ε) ∧
      firstHit (m.risk Q) (T * ε) =
        ENNReal.ofReal (commonVtot m / (4 * d ^ 2) *
          (matchedX m.F0 ε - Real.sqrt T
            + Real.log ((matchedX m.F0 ε - 1) / (Real.sqrt T - 1)))) ∧
      (1 / matchedX m.F0 ε ≤ 1 / 2 →
        |(firstHit (m.risk Q) (T * ε)).toReal / (commonVtot m / (4 * d ^ 2) * matchedX m.F0 ε)
            - 1|
          ≤ (1 / matchedX m.F0 ε) * (Real.sqrt T + |Real.log (Real.sqrt T - 1)|
            + Real.log (matchedX m.F0 ε) + 2 * (1 / matchedX m.F0 ε)))) ∧
    (∀ Q : ι → ℝ → ℝ, IsGlobalRowSolution m Q →
      ∀ Q₂ : ι₂ → ℝ → ℝ, IsGlobalRowSolution m₂ Q₂ →
        (firstHit (m.risk Q) (T * ε)).toReal / (firstHit (m₂.risk Q₂) (T * ε)).toReal
          = (commonVtot m / d ^ 2) / (commonVtot m₂ / d₂ ^ 2)) := by
  obtain ⟨h1, h2⟩ := matched_X_facts m.F0 ε T hε hT hF
  have hF0 : 0 ≤ m.F0 := by nlinarith
  have hsF := matched_sqrt_F0 m.F0 ε hF0 hε
  have hX1 : 1 < matchedX m.F0 ε := by linarith
  have hXpos : 0 < matchedX m.F0 ε := by linarith
  have hBpos := matched_B_pos (matchedX m.F0 ε) T h1 h2
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hFgt : Real.sqrt ε < Real.sqrt m.F0 := by
    rw [hsF]
    exact lt_mul_of_one_lt_left hsε hX1
  have hd2 : 0 < 4 * d ^ 2 := by have := pow_pos hd 2; linarith
  have hcpos : 0 < commonVtot m / (4 * d ^ 2) := div_pos hv hd2
  refine ⟨fun Q hQ => ⟨?_, matched_hit m d hd hdi hv ε T hε hT hF hη Q hQ, ?_⟩,
    fun Q hQ Q₂ hQ₂ => ?_⟩
  · -- floor: the risk tends to `ε`
    have hB := (matched_consts m d hd hdi hv ε hη).1
    have hne : Real.sqrt m.F0 ≠ commonB m d := by
      rw [hB]
      exact hFgt.ne'
    have hlt : commonB m d < Real.sqrt m.F0 := by
      rw [hB]
      exact hFgt
    have h5 := (prop_app_phase_common_i m d hd hdi hv).2.2.2.2.2 Q hQ
    have hlim : Tendsto (fun t => Real.sqrt (m.risk Q t)) atTop (𝓝 (commonB m d)) :=
      ((h5.1 hne).2.2.1 hlt).2
    rw [hB] at hlim
    have hsq := hlim.pow 2
    rw [Real.sq_sqrt hε.le] at hsq
    refine Tendsto.congr' ?_ hsq
    refine eventually_atTop.2 ⟨0, fun t ht => ?_⟩
    exact Real.sq_sqrt (Real.sqrt_pos.1 ((common_bridge m d hd hdi hv Q hQ).1 t ht)).le
  · -- error bound
    intro hx
    rw [matched_hit m d hd hdi hv ε T hε hT hF hη Q hQ,
      ENNReal.toReal_ofReal (mul_pos hcpos hBpos).le]
    set X := matchedX m.F0 ε with hXd
    set c := commonVtot m / (4 * d ^ 2) with hcd
    have hcne : c ≠ 0 := hcpos.ne'
    have hXne : X ≠ 0 := hXpos.ne'
    have hXi : 0 < 1 / X := one_div_pos.2 hXpos
    have hyp : 0 < 1 - 1 / X := by linarith
    have hsplit : Real.log (X - 1) = Real.log X + Real.log (1 - 1 / X) := by
      rw [← Real.log_mul hXne hyp.ne']
      congr 1
      rw [mul_sub, mul_one, mul_one_div_cancel hXne]
    have hTne : Real.sqrt T - 1 ≠ 0 := (by linarith : (0 : ℝ) < Real.sqrt T - 1).ne'
    have hXm1 : X - 1 ≠ 0 := (by linarith : (0 : ℝ) < X - 1).ne'
    have hL : Real.log ((X - 1) / (Real.sqrt T - 1))
        = Real.log X + Real.log (1 - 1 / X) - Real.log (Real.sqrt T - 1) := by
      rw [Real.log_div hXm1 hTne, hsplit]
    have hl1a : -(2 * (1 / X)) ≤ Real.log (1 - 1 / X) := by
      have h1' := Real.one_sub_inv_le_log_of_pos hyp
      have hinv : (1 - 1 / X)⁻¹ ≤ 1 + 2 * (1 / X) := by
        rw [inv_eq_one_div, div_le_iff₀ hyp]
        nlinarith [mul_nonneg hXi.le (by linarith : (0 : ℝ) ≤ 1 - 2 * (1 / X))]
      linarith
    have hl1b : Real.log (1 - 1 / X) ≤ 0 := Real.log_nonpos hyp.le (by linarith)
    have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX1.le
    have hsT0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
    rw [hL]
    have hEq : c * (X - Real.sqrt T + (Real.log X + Real.log (1 - 1 / X)
        - Real.log (Real.sqrt T - 1))) / (c * X) - 1
        = (-Real.sqrt T + Real.log X + Real.log (1 - 1 / X) - Real.log (Real.sqrt T - 1))
          * (1 / X) := by
      field_simp
      ring
    rw [hEq, abs_mul, abs_of_pos hXi]
    have hE : |-Real.sqrt T + Real.log X + Real.log (1 - 1 / X) - Real.log (Real.sqrt T - 1)|
        ≤ Real.sqrt T + |Real.log (Real.sqrt T - 1)| + Real.log X + 2 * (1 / X) := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (Real.log (Real.sqrt T - 1)), le_abs_self (Real.log (Real.sqrt T - 1))]
      · linarith [neg_le_abs (Real.log (Real.sqrt T - 1)), neg_abs_le (Real.log (Real.sqrt T - 1))]
    calc |-Real.sqrt T + Real.log X + Real.log (1 - 1 / X) - Real.log (Real.sqrt T - 1)| * (1 / X)
        = (1 / X) * |-Real.sqrt T + Real.log X + Real.log (1 - 1 / X)
            - Real.log (Real.sqrt T - 1)| := mul_comm _ _
      _ ≤ (1 / X) * (Real.sqrt T + |Real.log (Real.sqrt T - 1)| + Real.log X + 2 * (1 / X)) :=
          mul_le_mul_of_nonneg_left hE hXi.le
  · -- ratio of two models with the same `F₀`
    have e1 := matched_hit m d hd hdi hv ε T hε hT hF hη Q hQ
    have e2 := matched_hit m₂ d₂ hd₂ hdi₂ hv₂ ε T hε hT hF₂ hη₂ Q₂ hQ₂
    rw [hF₂eq] at e2
    have hd2' : 0 < 4 * d₂ ^ 2 := by have := pow_pos hd₂ 2; linarith
    have hc2 : 0 < commonVtot m₂ / (4 * d₂ ^ 2) := div_pos hv₂ hd2'
    rw [e1, e2, ENNReal.toReal_ofReal (mul_pos hcpos hBpos).le,
      ENNReal.toReal_ofReal (mul_pos hc2 hBpos).le, mul_div_mul_right _ _ hBpos.ne']
    have hdne : d ≠ 0 := hd.ne'
    have hd2ne : d₂ ≠ 0 := hd₂.ne'
    have hvne : commonVtot m₂ ≠ 0 := hv₂.ne'
    field_simp

end Muon.Phase

end

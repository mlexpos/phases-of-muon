import Mathlib
import Muon.Phase.Model
import Muon.Phase.Volterra


/-!
# Appendix H: clock, row equations and hitting times (task L-H.3)

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`,
subsection "The Volterra equation of the risk": `thm:app-phase-clock` (l.377–399) and
`thm:app-phase-hitting` (l.445–470). Card: `sections/07-phase-comparison/CARD.md`
§2, §3, §5 (L-H.3).

Encoding decisions:
* The model is `Muon.Phase.RowModel ι` with `forcing`, `kernel`, `kbar`, `F0`, `S`; the row
  predicate is `Muon.Phase.IsRowSolution` (derivative within `Ico 0 t₁`); first hitting times are
  `Muon.Phase.firstHit : ℝ → ℝ → ℝ≥0∞` (`inf ∅ = +∞`); the Volterra solution is
  `Muon.Phase.IsVolterraSol`, and `k * √Q` is `Muon.Foundations.oneSidedConv (√Q) kernel`.
  All reused unchanged from `Muon/Phase/Model.lean` and `Muon/Phase/Volterra.lean`.
* `Q` is the solution of `thm:app-phase-volterra` given as a hypothesis `IsVolterraSol m Q`
  (uniqueness is `thm_app_phase_volterra_i`).
* Intrinsic time `s`, step time `t`. `E_i`, `t(·)`, the clock `ϕ` and the step-time risk are
  the definitions `rowEnergy`, `clockTime`, `clock`, `riskClock`. `clock` is the inverse of
  `clockTime` on `[0,∞)` (`Function.invFunOn`); the paper's inverse-identity
  `ϕ(t)=∫_0^t η/√𝔑` is a clause of `thm_app_phase_clock`, not a definition.
* `t_* = lim_{s→∞} t(s) ∈ (0,∞]` is `tStar`, the supremum over `s ≥ 0` in `ℝ≥0∞`. Since
  `clockTime` is nondecreasing this supremum is the limit. The clauses `0 < tStar` and the
  equality of the `S = 0` limit are stated in `ℝ≥0∞`; the `S = 0` value is a `lintegral`, so
  non-integrability is not silently read as `0`.
* The row solutions are stated on every real `t₁` with `ENNReal.ofReal t₁ ≤ t_*`, since
  `IsRowSolution` takes a real endpoint; `[0,t_*)` is the union of those intervals. Maximality
  is the nonexistence of a solution on any `[0,t₁)` with `t_* < ofReal t₁`.
* The sum `∑' μ_i E_i(s)` is stated with `tsum`. Its summability is implied by the identity:
  `Q(s) > 0` by `thm_app_phase_volterra_iii`, so a non-summable family (read as `0`) would
  contradict it.
* `thm:app-phase-hitting` has two declarations: `_i` (hitting-time comparison and the clock
  identity for `t_a`) and `_ii` (the sandwich). Shared hypotheses `S > 0`, `ε > 0` and
  `η = 2√ε/S` are repeated in both, as in the source's top line. `H_Q(a)`, `H_F(a)` and `t_a`
  are `firstHit`, in `ℝ≥0∞`. The integrals `∫_0^{H_F(a)}` take `toReal` of `H_F(a)`, which is
  finite since `F` is strictly decreasing to `0` (`lem_app_phase_kernel_i`).
* `s_c` is a hypothesis: `0 ≤ sc` with `F(sc) = c₀ ε`. Existence and uniqueness follow from
  `lem_app_phase_kernel_i` (`F` strictly decreasing, `F(0) = F_0 > c₀ ε`, `F → 0`).
* `C_*` is `cstar` (`sSup` of the ratio over `[0,s_c]`, which is attained by continuity) and
  `m_*` is `mstar`. The ratio is `hitRatio`, with `(k * √F)(s) = oneSidedConv (√F) kernel s`.
-/

-- The LaTeX of the source statements is quoted verbatim in docstrings; some display lines are long.
set_option linter.style.longLine false

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ENNReal NNReal
open Muon.Foundations

noncomputable section

namespace Muon.Phase

variable {ι : Type*}

/-- Row energy in intrinsic time, `E_i(s)` of `thm:app-phase-clock` (l.377–399, display
`E_i(s)` there), given the Volterra solution `Q`:
`E_i(s) = 𝔔_i(0) e^{-2𝔡_i s} + η 𝔳_i ∫_0^s e^{-2𝔡_i (s-v)} √(Q(v)) dv`. -/
def rowEnergy (m : RowModel ι) (Q : ℝ → ℝ) (i : ι) (s : ℝ) : ℝ :=
  m.Q0 i * Real.exp (-(2 * m.d i * s)) +
    m.η * m.v i * ∫ v in (0:ℝ)..s, Real.exp (-(2 * m.d i * (s - v))) * Real.sqrt (Q v)

/-- The step-count time `t(s) = η⁻¹ ∫_0^s √(Q(v)) dv` as a function of intrinsic time `s`
(`thm:app-phase-clock`, l.377–399). -/
def clockTime (m : RowModel ι) (Q : ℝ → ℝ) (s : ℝ) : ℝ :=
  (1 / m.η) * ∫ v in (0:ℝ)..s, Real.sqrt (Q v)

/-- The limit `t_* = lim_{s→∞} t(s) ∈ (0, ∞]` (`thm:app-phase-clock`, l.377–399), as the
supremum over `s ≥ 0` in `ℝ≥0∞`; `clockTime` is nondecreasing, so this supremum is the limit. -/
def tStar (m : RowModel ι) (Q : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ s ∈ Ici (0:ℝ), ENNReal.ofReal (clockTime m Q s)

/-- The clock `ϕ` of `eqn:app-phase-clock` (l.381–390), the inverse of `clockTime` on `[0,∞)`:
`clockTime (clock t) = t` for `t ∈ [0, t_*)`. Its integral formula is a clause of
`thm_app_phase_clock`. -/
def clock (m : RowModel ι) (Q : ℝ → ℝ) (t : ℝ) : ℝ :=
  Function.invFunOn (clockTime m Q) (Ici (0:ℝ)) t

/-- Row energies in step time, `𝔔_i(t) := E_i(ϕ(t))` (`thm:app-phase-clock`, l.377–399). -/
def rowsInStepTime (m : RowModel ι) (Q : ℝ → ℝ) (i : ι) (t : ℝ) : ℝ :=
  rowEnergy m Q i (clock m Q t)

/-- Risk in step time, `𝔑(t) := Q(ϕ(t))` (`thm:app-phase-clock`, l.377–399). -/
def riskClock (m : RowModel ι) (Q : ℝ → ℝ) (t : ℝ) : ℝ :=
  Q (clock m Q t)

/-- The ratio `(k * √F)(s) / √(ε F(s))` whose maximum over `[0, s_c]` is `C_*`
(`thm:app-phase-hitting`(ii), l.455–459). The convolution is `oneSidedConv (√F) kernel`. -/
def hitRatio (m : RowModel ι) (ε s : ℝ) : ℝ :=
  oneSidedConv (fun u => Real.sqrt (m.forcing u)) m.kernel s / Real.sqrt (ε * m.forcing s)

/-- `C_* = max_{0 ≤ s ≤ s_c} (k * √F)(s) / √(ε F(s))` (`thm:app-phase-hitting`(ii), l.455–459),
realized as `sSup` of `hitRatio` over `[0, s_c]`, which is attained by continuity. -/
def cstar (m : RowModel ι) (ε sc : ℝ) : ℝ :=
  sSup (hitRatio m ε '' Icc (0:ℝ) sc)

/-- `m_* = C_* / (1 - 1/(2√c₀))` (`thm:app-phase-hitting`(ii), l.455–459). -/
def mstar (m : RowModel ι) (c₀ ε sc : ℝ) : ℝ :=
  cstar m ε sc / (1 - 1 / (2 * Real.sqrt c₀))

/-- Private: a solution is strictly positive on `[0,∞)` (from `thm_app_phase_volterra_iii`). -/
lemma aux_Q_pos [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    {s : ℝ} (hs : 0 ≤ s) : 0 < Q s :=
  lt_of_lt_of_le (thm_app_phase_volterra_iii m Q hQ s hs).1
    (thm_app_phase_volterra_iii m Q hQ s hs).2.1

/-- Private: `√Q` is interval-integrable on any interval inside `[0,∞)`. -/
lemma aux_sqrtQ_intInt [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun v => Real.sqrt (Q v)) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine (hQ.1.sqrt).mono ?_
  intro x hx
  rw [Set.mem_uIcc] at hx
  change 0 ≤ x
  rcases hx with h | h <;> linarith [h.1, h.2]

/-- Private: `clockTime` is strictly increasing on `[0,∞)`. -/
lemma aux_clockTime_strictMonoOn [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ)
    (hQ : IsVolterraSol m Q) : StrictMonoOn (clockTime m Q) (Ici (0:ℝ)) := by
  intro a ha b hb hab
  have ha0 : (0:ℝ) ≤ a := ha
  have hb0 : (0:ℝ) ≤ b := hb
  have hsplit : ∫ v in (0:ℝ)..b, Real.sqrt (Q v) =
      (∫ v in (0:ℝ)..a, Real.sqrt (Q v)) + ∫ v in a..b, Real.sqrt (Q v) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (aux_sqrtQ_intInt m Q hQ le_rfl ha0) (aux_sqrtQ_intInt m Q hQ ha0 hb0)).symm
  have hJ : 0 < ∫ v in a..b, Real.sqrt (Q v) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (aux_sqrtQ_intInt m Q hQ ha0 hb0) _ hab
    intro x hx
    exact Real.sqrt_pos.2 (aux_Q_pos m Q hQ (le_of_lt (lt_of_le_of_lt ha0 hx.1)))
  have hη : 0 < 1 / m.η := one_div_pos.2 m.η_pos
  unfold clockTime
  rw [hsplit]
  exact mul_lt_mul_of_pos_left (by linarith) hη

/-- Private: `t_* > 0` (the supremum dominates the value at `s = 1`, which is positive). -/
lemma aux_tStar_pos [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ)
    (hQ : IsVolterraSol m Q) : 0 < tStar m Q := by
  have h1 : (0:ℝ) ∈ Ici (0:ℝ) := Set.mem_Ici.2 le_rfl
  have hmono := aux_clockTime_strictMonoOn m Q hQ
  have h0 : clockTime m Q 0 = 0 := by simp [clockTime]
  have hpos : 0 < clockTime m Q 1 := by
    rw [← h0]; exact hmono h1 (show (1:ℝ) ∈ Ici (0:ℝ) by norm_num) one_pos
  have hle : ENNReal.ofReal (clockTime m Q 1) ≤ tStar m Q :=
    le_iSup₂ (f := fun s (_ : s ∈ Ici (0:ℝ)) => ENNReal.ofReal (clockTime m Q s)) 1
      (show (1:ℝ) ∈ Ici (0:ℝ) by norm_num)
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 hpos) hle

/-- Private: inverse-function derivative for a `C¹`-type function with positive derivative
everywhere on `ℝ`; the inverse is `Function.invFun`. -/
lemma aux_inv_hasDerivAt (c c' : ℝ → ℝ) (hc : ∀ x, HasDerivAt c (c' x) x)
    (hpos : ∀ x, 0 < c' x) (x : ℝ) :
    HasDerivAt (Function.invFun c) (c' x)⁻¹ (c x) := by
  have hmono : StrictMono c := strictMono_of_deriv_pos (fun y => by
    rw [(hc y).deriv]; exact hpos y)
  have hcont : Continuous c := continuous_iff_continuousAt.2 (fun y => (hc y).continuousAt)
  have hinj : Function.Injective c := hmono.injective
  have hleft : ∀ y, Function.invFun c (c y) = y := Function.leftInverse_invFun hinj
  have hrange : Set.Ioo (c (x - 1)) (c (x + 1)) ⊆ Set.range c := by
    intro y hy
    have := intermediate_value_Icc (show x - 1 ≤ x + 1 by linarith) hcont.continuousOn
    obtain ⟨z, _, hz⟩ := this (Set.Ioo_subset_Icc_self hy)
    exact ⟨z, hz⟩
  have hnhds : Set.Ioo (c (x - 1)) (c (x + 1)) ∈ 𝓝 (c x) :=
    Ioo_mem_nhds (hmono (by linarith)) (hmono (by linarith))
  have hfg : ∀ᶠ y in 𝓝 (c x), c (Function.invFun c y) = y := by
    filter_upwards [hnhds] with y hy
    obtain ⟨z, hz⟩ := hrange hy
    rw [← hz, hleft]
  have hgmono : MonotoneOn (Function.invFun c) (Set.Ioo (c (x - 1)) (c (x + 1))) := by
    intro y1 h1 y2 h2 h12
    obtain ⟨z1, hz1⟩ := hrange h1
    obtain ⟨z2, hz2⟩ := hrange h2
    rw [← hz1, ← hz2, hleft, hleft]
    rw [← hz1, ← hz2] at h12
    exact hmono.le_iff_le.1 h12
  have himg : Function.invFun c '' Set.Ioo (c (x - 1)) (c (x + 1)) ∈ 𝓝 (Function.invFun c (c x)) := by
    rw [hleft]
    refine Filter.mem_of_superset (Ioo_mem_nhds (by linarith : x - 1 < x) (by linarith : x < x + 1)) ?_
    intro z hz
    refine ⟨c z, ⟨hmono hz.1, hmono hz.2⟩, hleft z⟩
  have hgcont : ContinuousAt (Function.invFun c) (c x) :=
    continuousAt_of_monotoneOn_of_image_mem_nhds hgmono hnhds himg
  refine HasDerivAt.of_local_left_inverse hgcont ?_ (hpos x).ne' hfg
  rw [hleft]; exact hc x

/-- Private: `∫_0^s e^{-2d(s-v)} dv = (1 - e^{-2ds})/(2d)`. -/
lemma aux_exp_int (d s : ℝ) (hd : 0 < d) :
    ∫ v in (0:ℝ)..s, Real.exp (-(2 * d * (s - v))) = (1 - Real.exp (-(2 * d * s))) / (2 * d) := by
  have hd2 : (2 * d) ≠ 0 := by positivity
  have hder : ∀ x ∈ Set.uIcc (0:ℝ) s,
      HasDerivAt (fun v => (1 / (2 * d)) * Real.exp (-(2 * d * (s - v))))
        (Real.exp (-(2 * d * (s - x)))) x := by
    intro x _
    have h1 : HasDerivAt (fun v : ℝ => -(2 * d * (s - v))) (2 * d) x := by
      have := (((hasDerivAt_id x).const_sub s).const_mul (2 * d)).neg
      refine this.congr_deriv ?_
      simp
    have h2 := (h1.exp).const_mul (1 / (2 * d))
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [sub_zero, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
  field_simp

/-- Private: swapping `tsum` and the Volterra integral, for any `r` continuous on `[0,s]`. -/
lemma aux_sw [Countable ι] (m : RowModel ι) (r : ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (hr : ContinuousOn r (Set.Icc 0 s)) :
    Summable (fun i => m.μ i * (m.Q0 i * Real.exp (-(2 * m.d i * s)) +
        m.η * m.v i * ∫ v in (0:ℝ)..s, Real.exp (-(2 * m.d i * (s - v))) * r v)) ∧
    (1 / 2 : ℝ) * ∑' i, m.μ i * (m.Q0 i * Real.exp (-(2 * m.d i * s)) +
        m.η * m.v i * ∫ v in (0:ℝ)..s, Real.exp (-(2 * m.d i * (s - v))) * r v)
      = m.forcing s + oneSidedConv r m.kernel s := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hr
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 ⟨le_rfl, hs⟩)
  have hη := m.η_pos
  have hd2 : ∀ i, 0 < 2 * m.d i := fun i => by linarith [m.d_pos i]
  set a : ι → ℝ := fun i => ∫ v in (0:ℝ)..s, Real.exp (-(2 * m.d i * (s - v))) * r v with ha
  -- bound on `a i`
  have hbound : ∀ i, ∫ v in (0:ℝ)..s, ‖Real.exp (-(2 * m.d i * (s - v))) * r v‖ ≤ C / (2 * m.d i) := by
    intro i
    have h1 : ∫ v in (0:ℝ)..s, ‖Real.exp (-(2 * m.d i * (s - v))) * r v‖ ≤
        ∫ v in (0:ℝ)..s, C * Real.exp (-(2 * m.d i * (s - v))) := by
      apply intervalIntegral.integral_mono_on hs
      · apply ContinuousOn.intervalIntegrable
        have : ContinuousOn (fun v => Real.exp (-(2 * m.d i * (s - v)))) (Set.uIcc 0 s) :=
          (by fun_prop : Continuous fun v : ℝ => Real.exp (-(2 * m.d i * (s - v)))).continuousOn
        rw [Set.uIcc_of_le hs]
        exact (this.mono (by rw [Set.uIcc_of_le hs])).mul hr |>.norm
      · exact (by apply Continuous.intervalIntegrable; fun_prop)
      · intro v hv
        rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
        exact mul_le_mul_of_nonneg_right (hC v hv) (Real.exp_pos _).le
    rw [intervalIntegral.integral_const_mul, aux_exp_int _ _ (m.d_pos i)] at h1
    refine h1.trans ?_
    have : 0 ≤ Real.exp (-(2 * m.d i * s)) := (Real.exp_pos _).le
    calc C * ((1 - Real.exp (-(2 * m.d i * s))) / (2 * m.d i))
        ≤ C * (1 / (2 * m.d i)) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          exact div_le_div_of_nonneg_right (by linarith) (hd2 i).le
      _ = C / (2 * m.d i) := by ring
  have habs : ∀ i, |a i| ≤ C / (2 * m.d i) := fun i =>
    (intervalIntegral.abs_integral_le_integral_abs hs).trans (by simpa using hbound i)
  -- summability
  have hA : Summable (fun i => m.μ i * (m.Q0 i * Real.exp (-(2 * m.d i * s)))) := by
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (m.μ_pos i).le
      (mul_nonneg (m.Q0_nonneg i) (Real.exp_pos _).le)) (fun i => ?_) m.summable_μQ0
    have hexp : Real.exp (-(2 * m.d i * s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ 2 * m.d i * s := mul_nonneg (hd2 i).le hs
      linarith
    calc m.μ i * (m.Q0 i * Real.exp (-(2 * m.d i * s))) ≤ m.μ i * (m.Q0 i * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (m.Q0_nonneg i)) (m.μ_pos i).le
      _ = m.μ i * m.Q0 i := by ring
  have hB : Summable (fun i => m.μ i * (m.η * m.v i * a i)) := by
    refine Summable.of_norm_bounded ((m.summable_S.mul_left (C * m.η))) (fun i => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (m.μ_pos i), abs_of_pos hη,
      abs_of_nonneg (m.v_nonneg i)]
    have h2 := habs i
    have hpos : 0 ≤ m.μ i * (m.η * m.v i) :=
      mul_nonneg (m.μ_pos i).le (mul_nonneg hη.le (m.v_nonneg i))
    calc m.μ i * (m.η * m.v i * |a i|) = (m.μ i * (m.η * m.v i)) * |a i| := by ring
      _ ≤ (m.μ i * (m.η * m.v i)) * (C / (2 * m.d i)) := mul_le_mul_of_nonneg_left h2 hpos
      _ = C * m.η * (m.μ i * m.v i / (2 * m.d i)) := by ring
  have hsum : Summable (fun i => m.μ i * (m.Q0 i * Real.exp (-(2 * m.d i * s)) +
      m.η * m.v i * a i)) := by
    refine (hA.add hB).congr (fun i => ?_)
    ring
  refine ⟨hsum, ?_⟩
  -- the convolution as a series
  have hconv : oneSidedConv r m.kernel s = ∑' i, (m.η / 2) * (m.μ i * m.v i) * a i := by
    have hrev : oneSidedConv r m.kernel s = ∫ v in (0:ℝ)..s, r v * m.kernel (s - v) := by
      unfold oneSidedConv
      have := intervalIntegral.integral_comp_sub_left (fun x => r x * m.kernel (s - x)) (a := 0) (b := s) s
      simp only [sub_sub_cancel, sub_self, sub_zero] at this
      exact this
    rw [hrev]
    have hfun : (fun v => r v * m.kernel (s - v)) = fun v => ∑' i,
        r v * (m.η / 2 * (m.μ i * m.v i) * Real.exp (-(2 * m.d i * (s - v)))) := by
      funext v
      unfold RowModel.kernel
      rw [← tsum_mul_left, ← tsum_mul_left]
      exact tsum_congr (fun i => by ring)
    have hInt : ∀ i, Integrable (fun v => r v *
        (m.η / 2 * (m.μ i * m.v i) * Real.exp (-(2 * m.d i * (s - v)))))
        (volume.restrict (Set.Ioc 0 s)) := by
      intro i
      have hc : ContinuousOn (fun v => r v *
          (m.η / 2 * (m.μ i * m.v i) * Real.exp (-(2 * m.d i * (s - v))))) (Set.Icc 0 s) :=
        hr.mul (by fun_prop : Continuous fun v : ℝ =>
          m.η / 2 * (m.μ i * m.v i) * Real.exp (-(2 * m.d i * (s - v)))).continuousOn
      exact (hc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hcoef : ∀ i, 0 ≤ m.η / 2 * (m.μ i * m.v i) := fun i =>
      mul_nonneg (by linarith) (mul_nonneg (m.μ_pos i).le (m.v_nonneg i))
    have hSum : Summable (fun i => ∫ v, ‖r v *
        (m.η / 2 * (m.μ i * m.v i) * Real.exp (-(2 * m.d i * (s - v))))‖
          ∂(volume.restrict (Set.Ioc 0 s))) := by
      refine Summable.of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _))
        (fun i => ?_) ((m.summable_S.mul_left (C * (m.η / 2))))
      rw [← intervalIntegral.integral_of_le hs]
      have h1 : ∫ v in (0:ℝ)..s, ‖r v * (m.η / 2 * (m.μ i * m.v i) *
          Real.exp (-(2 * m.d i * (s - v))))‖ =
          (m.η / 2 * (m.μ i * m.v i)) *
            ∫ v in (0:ℝ)..s, ‖Real.exp (-(2 * m.d i * (s - v))) * r v‖ := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro v _
        simp only [norm_mul, Real.norm_of_nonneg (hcoef i), Real.norm_of_nonneg (Real.exp_pos _).le]
        ring
      rw [h1]
      calc (m.η / 2 * (m.μ i * m.v i)) * ∫ v in (0:ℝ)..s, ‖Real.exp (-(2 * m.d i * (s - v))) * r v‖
          ≤ (m.η / 2 * (m.μ i * m.v i)) * (C / (2 * m.d i)) :=
            mul_le_mul_of_nonneg_left (hbound i) (hcoef i)
        _ = C * (m.η / 2) * (m.μ i * m.v i / (2 * m.d i)) := by ring
    rw [hfun, intervalIntegral.integral_of_le hs,
      ← integral_tsum_of_summable_integral_norm hInt hSum]
    refine tsum_congr (fun i => ?_)
    rw [← intervalIntegral.integral_of_le hs, ha]
    simp only
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    simp only
    ring
  rw [hconv]
  unfold RowModel.forcing
  have hA' : Summable (fun i => m.μ i * m.Q0 i * Real.exp (-(2 * m.d i * s))) :=
    hA.congr (fun i => by ring)
  have e1 : ∑' i, m.μ i * (m.Q0 i * Real.exp (-(2 * m.d i * s)) + m.η * m.v i * a i) =
      ∑' i, m.μ i * m.Q0 i * Real.exp (-(2 * m.d i * s)) + ∑' i, m.μ i * (m.η * m.v i * a i) := by
    rw [← hA'.tsum_add hB]
    exact tsum_congr (fun i => by ring)
  rw [e1]
  have e2 : ∑' i, m.μ i * (m.η * m.v i * a i) = 2 * ∑' i, (m.η / 2) * (m.μ i * m.v i) * a i := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun i => by ring)
  rw [e2]
  ring

lemma aux_sqrt_cont [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    {s : ℝ} (hs : 0 ≤ s) : ContinuousOn (fun v => Real.sqrt (Q v)) (Icc 0 s) :=
  (hQ.1.sqrt).mono (fun x hx => hx.1)

/-- Private: clause 1 (identity) and the summability of the weighted row energies. -/
lemma aux_clause1 [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    {s : ℝ} (hs : 0 ≤ s) :
    Summable (fun i => m.μ i * rowEnergy m Q i s) ∧
      (1 / 2 : ℝ) * ∑' i, m.μ i * rowEnergy m Q i s = Q s := by
  have h := aux_sw m (fun v => Real.sqrt (Q v)) hs (aux_sqrt_cont m Q hQ hs)
  refine ⟨h.1, ?_⟩
  unfold rowEnergy
  rw [h.2, ← hQ.2.2 s hs]

/-- Private: the clock is a left inverse of `clockTime` on `[0,∞)`. -/
lemma aux_clock_left [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    {s : ℝ} (hs : 0 ≤ s) : clock m Q (clockTime m Q s) = s :=
  (aux_clockTime_strictMonoOn m Q hQ).injOn.leftInvOn_invFunOn (Set.mem_Ici.2 hs)

/-- Private: an everywhere-defined `C¹` extension of `clockTime` and its inverse. -/
lemma aux_inverse_deriv [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ)
    (hQ : IsVolterraSol m Q) :
    ∃ g : ℝ → ℝ, (∀ s, 0 ≤ s → g (clockTime m Q s) = s) ∧
      ∀ s, 0 ≤ s → HasDerivAt g (m.η / Real.sqrt (Q s)) (clockTime m Q s) := by
  set Qe : ℝ → ℝ := fun v => Real.sqrt (Q (max v 0)) with hQe
  have hQe_cont : Continuous Qe := by
    have : Continuous (fun v : ℝ => Q (max v 0)) :=
      hQ.1.comp_continuous (continuous_id.max continuous_const) (fun x => Set.mem_Ici.2 (le_max_right _ _))
    exact this.sqrt
  have hQe_pos : ∀ v, 0 < Qe v := fun v =>
    Real.sqrt_pos.2 (aux_Q_pos m Q hQ (le_max_right _ _))
  set ce : ℝ → ℝ := fun s => (1 / m.η) * ∫ v in (0:ℝ)..s, Qe v with hce
  have hce_deriv : ∀ x, HasDerivAt ce (Qe x / m.η) x := by
    intro x
    have h1 := (hQe_cont.integral_hasStrictDerivAt 0 x).hasDerivAt
    have h2 := h1.const_mul (1 / m.η)
    refine h2.congr_deriv ?_
    field_simp
  have hce_eq : ∀ s, 0 ≤ s → ce s = clockTime m Q s := by
    intro s hs
    unfold clockTime
    rw [hce]
    simp only
    congr 1
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le hs] at hv
    simp only [hQe]
    rw [max_eq_left hv.1]
  refine ⟨Function.invFun ce, ?_, ?_⟩
  · intro s hs
    rw [← hce_eq s hs]
    exact Function.leftInverse_invFun
      (strictMono_of_deriv_pos (fun y => by
        rw [(hce_deriv y).deriv]; exact div_pos (hQe_pos y) m.η_pos)).injective s
  · intro s hs
    have := aux_inv_hasDerivAt ce (fun x => Qe x / m.η) hce_deriv
      (fun x => div_pos (hQe_pos x) m.η_pos) s
    rw [hce_eq s hs] at this
    refine this.congr_deriv ?_
    simp only [hQe, max_eq_left hs]
    have : 0 < Real.sqrt (Q s) := Real.sqrt_pos.2 (aux_Q_pos m Q hQ hs)
    field_simp

/-- Private: clause 3, `clockTime` is `C¹` on `[0,∞)`. -/
lemma aux_clause3 [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ)
    (hQ : IsVolterraSol m Q) : ContDiffOn ℝ 1 (clockTime m Q) (Ici (0:ℝ)) := by
  set Qe : ℝ → ℝ := fun v => Real.sqrt (Q (max v 0)) with hQe
  have hQe_cont : Continuous Qe := by
    have : Continuous (fun v : ℝ => Q (max v 0)) :=
      hQ.1.comp_continuous (continuous_id.max continuous_const)
        (fun x => Set.mem_Ici.2 (le_max_right _ _))
    exact this.sqrt
  set ce : ℝ → ℝ := fun s => (1 / m.η) * ∫ v in (0:ℝ)..s, Qe v with hce
  have hce_deriv : ∀ x, HasDerivAt ce (Qe x / m.η) x := by
    intro x
    have h1 := (hQe_cont.integral_hasStrictDerivAt 0 x).hasDerivAt
    have h2 := h1.const_mul (1 / m.η)
    refine h2.congr_deriv ?_
    field_simp
  have hcd : ContDiff ℝ 1 ce := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x => (hce_deriv x).differentiableAt, ?_⟩
    have : deriv ce = fun x => Qe x / m.η := funext (fun x => (hce_deriv x).deriv)
    rw [this]
    exact hQe_cont.div_const _
  refine hcd.contDiffOn.congr (fun s hs => ?_)
  have hs' : 0 ≤ s := hs
  unfold clockTime
  rw [hce]
  simp only
  congr 1
  apply intervalIntegral.integral_congr
  intro v hv
  rw [Set.uIcc_of_le hs'] at hv
  simp only [hQe]
  rw [max_eq_left hv.1]

lemma aux_clockTime_zero (m : RowModel ι) (Q : ℝ → ℝ) : clockTime m Q 0 = 0 := by
  simp [clockTime]

lemma aux_ofReal_le_tStar [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ENNReal.ofReal (clockTime m Q s) ≤ tStar m Q :=
  le_iSup₂ (f := fun s (_ : s ∈ Ici (0:ℝ)) => ENNReal.ofReal (clockTime m Q s)) s
    (Set.mem_Ici.2 hs)

/-- Private: clause 5, the image of `[0,∞)` under `clockTime` is `[0,t_*)`. -/
lemma aux_clause5 [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ)
    (hQ : IsVolterraSol m Q) :
    clockTime m Q '' Ici (0:ℝ) = {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < tStar m Q} := by
  have hmono := aux_clockTime_strictMonoOn m Q hQ
  have hcont : ContinuousOn (clockTime m Q) (Ici (0:ℝ)) := (aux_clause3 m Q hQ).continuousOn
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs0 : (0:ℝ) ≤ s := hs
    have h0 : clockTime m Q 0 ≤ clockTime m Q s := hmono.monotoneOn (Set.mem_Ici.2 le_rfl) hs hs0
    rw [aux_clockTime_zero] at h0
    have h1 : clockTime m Q s < clockTime m Q (s + 1) :=
      hmono hs (Set.mem_Ici.2 (by linarith)) (by linarith)
    refine ⟨h0, lt_of_lt_of_le ?_ (aux_ofReal_le_tStar m Q (show 0 ≤ s + 1 by linarith))⟩
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 h1
  · rintro ⟨ht0, ht⟩
    unfold tStar at ht
    obtain ⟨s, hs⟩ := lt_iSup_iff.1 ht
    obtain ⟨hs', hlt⟩ := lt_iSup_iff.1 hs
    have hs0 : (0:ℝ) ≤ s := hs'
    have hlt' := (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1
    have := intermediate_value_Icc hs0 (hcont.mono (Set.Icc_subset_Ici_self))
    obtain ⟨u, hu, hut⟩ := this (show t ∈ Icc (clockTime m Q 0) (clockTime m Q s) from
      ⟨by rw [aux_clockTime_zero]; exact ht0, hlt'.le⟩)
    exact ⟨u, Set.mem_Ici.2 hu.1, hut⟩

lemma aux_clock_spec [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t < tStar m Q) :
    0 ≤ clock m Q t ∧ clockTime m Q (clock m Q t) = t := by
  have : t ∈ clockTime m Q '' Ici (0:ℝ) := by
    rw [aux_clause5 m Q hQ]; exact ⟨ht0, ht⟩
  obtain ⟨s, hs, rfl⟩ := this
  rw [aux_clock_left m Q hQ hs]
  exact ⟨hs, rfl⟩

lemma aux_g_clock [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q) :
    ∃ g : ℝ → ℝ, ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < tStar m Q →
      g t = clock m Q t ∧ HasDerivAt g (m.η / Real.sqrt (Q (clock m Q t))) t := by
  obtain ⟨g, hg1, hg2⟩ := aux_inverse_deriv m Q hQ
  refine ⟨g, fun t ht0 ht => ?_⟩
  obtain ⟨h0, h1⟩ := aux_clock_spec m Q hQ ht0 ht
  have e : g t = clock m Q t := by
    have := hg1 _ h0
    rw [h1] at this
    exact this
  refine ⟨e, ?_⟩
  have := hg2 _ h0
  rw [h1] at this
  exact this

lemma aux_clock_zero [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q) :
    clock m Q 0 = 0 := by
  have := aux_clock_left m Q hQ (le_refl (0:ℝ))
  rwa [aux_clockTime_zero] at this

/-- Private: clause 6, the integral formula for the clock. -/
lemma aux_clause6 [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t < tStar m Q) :
    clock m Q t = ∫ t' in (0:ℝ)..t, m.η / Real.sqrt (riskClock m Q t') := by
  obtain ⟨g, hg⟩ := aux_g_clock m Q hQ
  have hmem : ∀ x ∈ Set.uIcc (0:ℝ) t, 0 ≤ x ∧ ENNReal.ofReal x < tStar m Q := by
    intro x hx
    rw [Set.uIcc_of_le ht0] at hx
    refine ⟨hx.1, lt_of_le_of_lt ?_ ht⟩
    exact ENNReal.ofReal_le_ofReal hx.2
  have hder : ∀ x ∈ Set.uIcc (0:ℝ) t, HasDerivAt g (m.η / Real.sqrt (riskClock m Q x)) x :=
    fun x hx => (hg x (hmem x hx).1 (hmem x hx).2).2
  have hcont_g : ContinuousOn g (Set.uIcc 0 t) := fun x hx => (hder x hx).continuousAt.continuousWithinAt
  have hcont_clock : ContinuousOn (clock m Q) (Set.uIcc 0 t) := by
    refine hcont_g.congr (fun x hx => ?_)
    exact ((hg x (hmem x hx).1 (hmem x hx).2).1).symm
  have hint : IntervalIntegrable (fun x => m.η / Real.sqrt (riskClock m Q x)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    have hQc : ContinuousOn (fun x => Q (clock m Q x)) (Set.uIcc 0 t) :=
      hQ.1.comp hcont_clock (fun x hx => Set.mem_Ici.2 (aux_clock_spec m Q hQ (hmem x hx).1 (hmem x hx).2).1)
    refine continuousOn_const.div hQc.sqrt (fun x hx => ?_)
    exact (Real.sqrt_pos.2 (aux_Q_pos m Q hQ
      (aux_clock_spec m Q hQ (hmem x hx).1 (hmem x hx).2).1)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
  have h0 := (hg 0 le_rfl (by simpa using aux_tStar_pos m Q hQ)).1
  rw [h0, aux_clock_zero m Q hQ, sub_zero]
  exact ((hg t ht0 ht).1).symm

/-- Private: derivative of a row energy within `[0,∞)`. -/
lemma aux_E_deriv [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    (i : ι) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (rowEnergy m Q i)
      (-(2 * m.d i) * rowEnergy m Q i s + m.η * m.v i * Real.sqrt (Q s)) (Ici 0) s := by
  set Qe : ℝ → ℝ := fun v => Real.sqrt (Q (max v 0)) with hQe
  have hQe_cont : Continuous Qe := by
    have : Continuous (fun v : ℝ => Q (max v 0)) :=
      hQ.1.comp_continuous (continuous_id.max continuous_const)
        (fun x => Set.mem_Ici.2 (le_max_right _ _))
    exact this.sqrt
  set A : ℝ → ℝ := fun s => Real.exp (-(2 * m.d i * s)) with hA
  set I : ℝ → ℝ := fun s => ∫ v in (0:ℝ)..s, Real.exp (2 * m.d i * v) * Qe v with hI
  have hAd : ∀ x, HasDerivAt A (-(2 * m.d i) * A x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => -(2 * m.d i * y)) (-(2 * m.d i)) x := by
      have := ((hasDerivAt_id x).const_mul (2 * m.d i)).neg
      refine this.congr_deriv ?_
      simp
    have h2 := h1.exp
    refine h2.congr_deriv ?_
    simp only [hA]; ring
  have hIcont : Continuous (fun v : ℝ => Real.exp (2 * m.d i * v) * Qe v) := by
    have : Continuous fun v : ℝ => Real.exp (2 * m.d i * v) := by fun_prop
    exact this.mul hQe_cont
  have hId : ∀ x, HasDerivAt I (Real.exp (2 * m.d i * x) * Qe x) x := fun x =>
    (hIcont.integral_hasStrictDerivAt 0 x).hasDerivAt
  set Ee : ℝ → ℝ := fun s => m.Q0 i * A s + (m.η * m.v i) * (A s * I s) with hEe
  have hEed : HasDerivAt Ee (m.Q0 i * (-(2 * m.d i) * A s) + (m.η * m.v i) *
      ((-(2 * m.d i) * A s) * I s + A s * (Real.exp (2 * m.d i * s) * Qe s))) s :=
    ((hAd s).const_mul (m.Q0 i)).add (((hAd s).mul (hId s)).const_mul (m.η * m.v i))
  have hint : ∀ x, 0 ≤ x → ∫ v in (0:ℝ)..x, Real.exp (-(2 * m.d i * (x - v))) * Real.sqrt (Q v)
      = A x * I x := by
    intro x hx
    simp only [hA, hI]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le hx] at hv
    simp only [hQe, max_eq_left hv.1]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hEq : ∀ x, 0 ≤ x → rowEnergy m Q i x = Ee x := by
    intro x hx
    unfold rowEnergy
    rw [hint x hx]
  have hAe : A s * Real.exp (2 * m.d i * s) = 1 := by
    simp only [hA]
    rw [← Real.exp_add]; simp
  refine (hEed.hasDerivWithinAt (s := Ici 0)).congr (fun y hy => hEq y hy) (hEq s hs) |>.congr_deriv ?_
  rw [hEq s hs]
  simp only [hEe, hQe, max_eq_left hs]
  have : A s * (Real.exp (2 * m.d i * s) * Real.sqrt (Q s)) = Real.sqrt (Q s) := by
    rw [← mul_assoc, hAe, one_mul]
  linear_combination (m.η * m.v i) * this

lemma aux_mem_Ico [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) {t₁ t : ℝ}
    (h₁ : ENNReal.ofReal t₁ ≤ tStar m Q) (ht : t ∈ Ico (0:ℝ) t₁) :
    0 ≤ t ∧ ENNReal.ofReal t < tStar m Q :=
  ⟨ht.1, lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith [ht.1, ht.2])).2 ht.2) h₁⟩

lemma aux_risk_eq [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t < tStar m Q) :
    m.risk (rowsInStepTime m Q) t = Q (clock m Q t) :=
  (aux_clause1 m Q hQ (aux_clock_spec m Q hQ ht0 ht).1).2

/-- Private: clause 7, the step-time rows solve (M3) on `[0,t₁)` for `t₁ ≤ t_*`. -/
lemma aux_clause7 [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    {t₁ : ℝ} (h₁ : ENNReal.ofReal t₁ ≤ tStar m Q) :
    IsRowSolution m t₁ (rowsInStepTime m Q) := by
  obtain ⟨g, hg⟩ := aux_g_clock m Q hQ
  have hmem := fun t (ht : t ∈ Ico (0:ℝ) t₁) => aux_mem_Ico m Q h₁ ht
  have hcont_clock : ContinuousOn (clock m Q) (Ico 0 t₁) := by
    have : ContinuousOn g (Ico 0 t₁) := fun t ht =>
      (hg t (hmem t ht).1 (hmem t ht).2).2.continuousAt.continuousWithinAt
    exact this.congr (fun t ht => ((hg t (hmem t ht).1 (hmem t ht).2).1).symm)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    unfold rowsInStepTime rowEnergy
    rw [aux_clock_zero m Q hQ]
    simp
  · intro t ht
    exact (aux_clause1 m Q hQ (aux_clock_spec m Q hQ (hmem t ht).1 (hmem t ht).2).1).1
  · have : ContinuousOn (fun t => Q (clock m Q t)) (Ico 0 t₁) :=
      hQ.1.comp hcont_clock (fun t ht => Set.mem_Ici.2
        (aux_clock_spec m Q hQ (hmem t ht).1 (hmem t ht).2).1)
    exact this.congr (fun t ht => aux_risk_eq m Q hQ (hmem t ht).1 (hmem t ht).2)
  · intro t ht
    rw [aux_risk_eq m Q hQ (hmem t ht).1 (hmem t ht).2]
    exact aux_Q_pos m Q hQ (aux_clock_spec m Q hQ (hmem t ht).1 (hmem t ht).2).1
  · intro t ht i
    have h0 := (aux_clock_spec m Q hQ (hmem t ht).1 (hmem t ht).2).1
    have hE := aux_E_deriv m Q hQ i h0
    have hgd := (hg t (hmem t ht).1 (hmem t ht).2).2.hasDerivWithinAt (s := Ico 0 t₁)
    have hgeq : ∀ y ∈ Ico (0:ℝ) t₁, g y = clock m Q y := fun y hy =>
      (hg y (hmem y hy).1 (hmem y hy).2).1
    have hmaps : MapsTo (clock m Q) (Ico 0 t₁) (Ici 0) := fun y hy =>
      Set.mem_Ici.2 (aux_clock_spec m Q hQ (hmem y hy).1 (hmem y hy).2).1
    have hgd' : HasDerivWithinAt (clock m Q) (m.η / Real.sqrt (Q (clock m Q t))) (Ico 0 t₁) t :=
      hgd.congr (fun y hy => (hgeq y hy).symm) ((hgeq t ht).symm)
    have hcomp := HasDerivWithinAt.scomp t hE hgd' hmaps
    rw [aux_risk_eq m Q hQ (hmem t ht).1 (hmem t ht).2]
    refine (show HasDerivWithinAt (rowsInStepTime m Q i) _ (Ico 0 t₁) t from hcomp).congr_deriv ?_
    unfold rowsInStepTime
    have hpos : 0 < Real.sqrt (Q (clock m Q t)) := Real.sqrt_pos.2 (aux_Q_pos m Q hQ h0)
    simp only [smul_eq_mul]
    field_simp

/-- Private: large intrinsic times correspond to large step times. -/
lemma aux_clock_large [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    {s₀ t : ℝ} (hs₀ : 0 ≤ s₀) (h : clockTime m Q s₀ ≤ t) (ht0 : 0 ≤ t)
    (ht : ENNReal.ofReal t < tStar m Q) : s₀ ≤ clock m Q t := by
  obtain ⟨h0, h1⟩ := aux_clock_spec m Q hQ ht0 ht
  by_contra hlt
  push_neg at hlt
  have := aux_clockTime_strictMonoOn m Q hQ (Set.mem_Ici.2 h0) (Set.mem_Ici.2 hs₀) hlt
  rw [h1] at this
  linarith

/-- Private: clause 10. -/
lemma aux_clause10 [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    (hS : 0 < m.S) :
    tStar m Q = ⊤ ∧
      Tendsto (m.risk (rowsInStepTime m Q)) atTop (𝓝 (m.η ^ 2 * m.S ^ 2 / 4)) := by
  obtain ⟨hlim, hkb⟩ := thm_app_phase_volterra_iv m Q hQ
  have hη := m.η_pos
  have hkbpos : 0 < m.kbar := by unfold RowModel.kbar; positivity
  have hk2 : 0 < m.kbar ^ 2 := by positivity
  have hev := (hlim.eventually_const_lt (show m.kbar ^ 2 / 4 < m.kbar ^ 2 by linarith))
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop (0:ℝ)))
  have hs₀0 : 0 ≤ s₀ := (hs₀ s₀ le_rfl).2
  have hsqrt : ∀ s, s₀ ≤ s → m.kbar / 2 ≤ Real.sqrt (Q s) := by
    intro s hs
    apply Real.le_sqrt_of_sq_le
    have := (hs₀ s hs).1
    nlinarith
  have hlow : ∀ s, s₀ ≤ s → m.kbar / (2 * m.η) * (s - s₀) ≤ clockTime m Q s := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans hs₀0 hs
    unfold clockTime
    have hsplit : ∫ v in (0:ℝ)..s, Real.sqrt (Q v) =
        (∫ v in (0:ℝ)..s₀, Real.sqrt (Q v)) + ∫ v in s₀..s, Real.sqrt (Q v) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (aux_sqrtQ_intInt m Q hQ le_rfl hs₀0) (aux_sqrtQ_intInt m Q hQ hs₀0 hs0)).symm
    have h1 : 0 ≤ ∫ v in (0:ℝ)..s₀, Real.sqrt (Q v) :=
      intervalIntegral.integral_nonneg hs₀0 (fun _ _ => Real.sqrt_nonneg _)
    have h2 : ∫ v in s₀..s, (m.kbar / 2) ≤ ∫ v in s₀..s, Real.sqrt (Q v) :=
      intervalIntegral.integral_mono_on hs (by simp) (aux_sqrtQ_intInt m Q hQ hs₀0 hs0)
        (fun v hv => hsqrt v hv.1)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h2
    rw [hsplit]
    have : m.kbar / (2 * m.η) * (s - s₀) = (1 / m.η) * ((s - s₀) * (m.kbar / 2)) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have htop : tStar m Q = ⊤ := by
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro r
    set s := s₀ + (r : ℝ) * (2 * m.η / m.kbar) with hsdef
    have hs : s₀ ≤ s := by
      have : 0 ≤ (r : ℝ) * (2 * m.η / m.kbar) := by positivity
      linarith
    have h1 := hlow s hs
    have h2 : (r : ℝ) ≤ clockTime m Q s := by
      refine le_trans (le_of_eq ?_) h1
      rw [hsdef]
      field_simp
      ring
    calc (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
      _ ≤ ENNReal.ofReal (clockTime m Q s) := ENNReal.ofReal_le_ofReal h2
      _ ≤ tStar m Q := aux_ofReal_le_tStar m Q (le_trans hs₀0 hs)
  refine ⟨htop, ?_⟩
  have hclock : Tendsto (clock m Q) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨max (clockTime m Q (max b 0)) 0, fun t ht => ?_⟩
    have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
    have := aux_clock_large m Q hQ (le_max_right b 0) (le_trans (le_max_left _ _) ht) ht0
      (by rw [htop]; exact ENNReal.ofReal_lt_top)
    exact le_trans (le_max_left _ _) this
  have hcomp := hlim.comp hclock
  rw [hkb] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  exact (aux_risk_eq m Q hQ ht (by rw [htop]; exact ENNReal.ofReal_lt_top)).symm

lemma aux_kernel_zero [Countable ι] (m : RowModel ι) (hS : m.S = 0) (s : ℝ) :
    m.kernel s = 0 := by
  have hnn : ∀ i, 0 ≤ m.μ i * m.v i / (2 * m.d i) := fun i =>
    div_nonneg (mul_nonneg (m.μ_pos i).le (m.v_nonneg i)) (by linarith [m.d_pos i])
  have hz : (fun i => m.μ i * m.v i / (2 * m.d i)) = 0 := by
    have h := (m.summable_S.hasSum)
    unfold RowModel.S at hS
    rw [hS] at h
    exact (hasSum_zero_iff_of_nonneg hnn).1 h
  have hv : ∀ i, m.v i = 0 := by
    intro i
    have := congrFun hz i
    simp only [Pi.zero_apply] at this
    have hd : 0 < 2 * m.d i := by linarith [m.d_pos i]
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h (m.μ_pos i).ne'
      · exact h
    · exact absurd h hd.ne'
  unfold RowModel.kernel
  simp [hv]

lemma aux_Q_eq_F [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    (hS : m.S = 0) {s : ℝ} (hs : 0 ≤ s) : Q s = m.forcing s := by
  rw [hQ.2.2 s hs]
  have : oneSidedConv (fun u => Real.sqrt (Q u)) m.kernel s = 0 := by
    unfold oneSidedConv
    simp [aux_kernel_zero m hS]
  rw [this, add_zero]

/-- Private: clause 11. -/
lemma aux_clause11 [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    (hS : m.S = 0) :
    tStar m Q = ENNReal.ofReal (m.η⁻¹) *
          ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (Real.sqrt (m.forcing s)) ∧
        (tStar m Q ≠ ⊤ →
          Tendsto (m.risk (rowsInStepTime m Q)) (𝓝[<] (tStar m Q).toReal) (𝓝 0)) := by
  have hη := m.η_pos
  have hFc : ContinuousOn m.forcing (Ici 0) := (lem_app_phase_kernel_i m).1
  have hclock_eq : ∀ s, 0 ≤ s → ENNReal.ofReal (clockTime m Q s) =
      ENNReal.ofReal (m.η⁻¹) * ∫⁻ x in Ioc (0:ℝ) s, ENNReal.ofReal (Real.sqrt (m.forcing x)) := by
    intro s hs
    have h1 : ∫ v in (0:ℝ)..s, Real.sqrt (Q v) = ∫ v in (0:ℝ)..s, Real.sqrt (m.forcing v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le hs] at hv
      simp only [aux_Q_eq_F m Q hQ hS hv.1]
    have hint : IntegrableOn (fun x => Real.sqrt (m.forcing x)) (Ioc 0 s) := by
      have : ContinuousOn (fun x => Real.sqrt (m.forcing x)) (Icc 0 s) :=
        (hFc.sqrt).mono (fun x hx => hx.1)
      exact (this.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    unfold clockTime
    rw [h1, intervalIntegral.integral_of_le hs, ENNReal.ofReal_mul (by positivity),
      ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (fun x => Real.sqrt_nonneg _))]
    simp [one_div]
  have hmain : tStar m Q = ENNReal.ofReal (m.η⁻¹) *
          ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (Real.sqrt (m.forcing s)) := by
    have hU : (⋃ n : ℕ, Ioc (0:ℝ) (n : ℝ)) = Ioi 0 := by
      ext x
      simp only [mem_iUnion, mem_Ioc, mem_Ioi]
      constructor
      · rintro ⟨n, h, _⟩; exact h
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_ge x
        exact ⟨n, h, hn⟩
    have hdir : Directed (· ⊆ ·) (fun n : ℕ => Ioc (0:ℝ) (n : ℝ)) := by
      apply Monotone.directed_le
      intro a b hab
      exact Ioc_subset_Ioc_right (by exact_mod_cast hab)
    have hlint := setLIntegral_iUnion_of_directed (μ := volume)
      (fun x => ENNReal.ofReal (Real.sqrt (m.forcing x))) hdir
    rw [hU] at hlint
    rw [hlint, ENNReal.mul_iSup]
    apply le_antisymm
    · apply iSup₂_le
      intro s hs
      rw [hclock_eq s hs]
      obtain ⟨n, hn⟩ := exists_nat_ge s
      exact le_trans (mul_le_mul' le_rfl (lintegral_mono_set (Ioc_subset_Ioc_right hn)))
        (le_iSup (fun n : ℕ => ENNReal.ofReal (m.η⁻¹) *
          ∫⁻ x in Ioc (0:ℝ) (n : ℝ), ENNReal.ofReal (Real.sqrt (m.forcing x))) n)
    · apply iSup_le
      intro n
      rw [← hclock_eq n (Nat.cast_nonneg n)]
      exact aux_ofReal_le_tStar m Q (Nat.cast_nonneg n)
  refine ⟨hmain, fun hfin => ?_⟩
  obtain ⟨hlim, hkb⟩ := thm_app_phase_volterra_iv m Q hQ
  have hk0 : m.kbar ^ 2 = 0 := by rw [hkb, hS]; ring
  rw [hk0] at hlim
  set T := (tStar m Q).toReal with hT
  have hlt : ∀ x, 0 ≤ x → (ENNReal.ofReal x < tStar m Q ↔ x < T) := fun x hx =>
    ENNReal.ofReal_lt_iff_lt_toReal hx hfin
  have hclock : Tendsto (clock m Q) (𝓝[<] T) atTop := by
    rw [tendsto_atTop]
    intro b
    set s₀ := max b 0 with hs₀
    have hs₀0 : 0 ≤ s₀ := le_max_right _ _
    have hcs : clockTime m Q s₀ < T := by
      have h1 : clockTime m Q s₀ < clockTime m Q (s₀ + 1) :=
        aux_clockTime_strictMonoOn m Q hQ (Set.mem_Ici.2 hs₀0) (Set.mem_Ici.2 (by linarith))
          (by linarith)
      have h0 : 0 ≤ clockTime m Q s₀ := by
        have := (aux_clockTime_strictMonoOn m Q hQ).monotoneOn (Set.mem_Ici.2 le_rfl)
          (Set.mem_Ici.2 hs₀0) hs₀0
        rwa [aux_clockTime_zero] at this
      rw [← hlt _ h0]
      refine lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 h1) ?_
      exact aux_ofReal_le_tStar m Q (by linarith)
    filter_upwards [Ioo_mem_nhdsLT hcs] with t ht
    have h0 : 0 ≤ clockTime m Q s₀ := by
      have := (aux_clockTime_strictMonoOn m Q hQ).monotoneOn (Set.mem_Ici.2 le_rfl)
        (Set.mem_Ici.2 hs₀0) hs₀0
      rwa [aux_clockTime_zero] at this
    have ht0 : 0 ≤ t := by linarith [ht.1]
    exact le_trans (le_max_left _ _)
      (aux_clock_large m Q hQ hs₀0 ht.1.le ht0 ((hlt t ht0).2 ht.2))
  have hcomp := hlim.comp hclock
  refine hcomp.congr' ?_
  have hT0 : 0 < T := ENNReal.toReal_pos (aux_tStar_pos m Q hQ).ne' hfin
  have hmem : ∀ᶠ t in 𝓝[<] T, 0 ≤ t ∧ t < T := by
    filter_upwards [Ioo_mem_nhdsLT hT0] with t ht
    exact ⟨ht.1.le, ht.2⟩
  filter_upwards [hmem] with t ht
  exact (aux_risk_eq m Q hQ ht.1 ((hlt t ht.1).2 ht.2)).symm

/-- Private: the reparametrization `ψ(u) = ∫_0^u η/√Re` of a continuous positive `Re`, with its
inverse `χ`. -/
lemma aux_reparam (η : ℝ) (hη : 0 < η) (Re : ℝ → ℝ) (hc : Continuous Re)
    (hpos : ∀ u, 0 < Re u) :
    ∃ ψ χ : ℝ → ℝ, ψ 0 = 0 ∧ StrictMono ψ ∧
      (∀ u, HasDerivAt ψ (η / Real.sqrt (Re u)) u) ∧ (∀ u, χ (ψ u) = u) ∧
      ∀ u, HasDerivAt χ (Real.sqrt (Re u) / η) (ψ u) := by
  have hcont : Continuous (fun v => η / Real.sqrt (Re v)) :=
    continuous_const.div hc.sqrt (fun v => (Real.sqrt_pos.2 (hpos v)).ne')
  have hψ : ∀ u, HasDerivAt (fun u => ∫ v in (0:ℝ)..u, η / Real.sqrt (Re v))
      (η / Real.sqrt (Re u)) u := fun u => (hcont.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hp : ∀ u, 0 < η / Real.sqrt (Re u) := fun u => div_pos hη (Real.sqrt_pos.2 (hpos u))
  have hmono : StrictMono (fun u => ∫ v in (0:ℝ)..u, η / Real.sqrt (Re v)) :=
    strictMono_of_deriv_pos (fun y => by rw [(hψ y).deriv]; exact hp y)
  refine ⟨fun u => ∫ v in (0:ℝ)..u, η / Real.sqrt (Re v),
    Function.invFun (fun u => ∫ v in (0:ℝ)..u, η / Real.sqrt (Re v)), by simp, hmono, hψ,
    fun u => Function.leftInverse_invFun hmono.injective u, fun u => ?_⟩
  have := aux_inv_hasDerivAt _ _ hψ hp u
  refine this.congr_deriv ?_
  have := Real.sqrt_pos.2 (hpos u)
  field_simp

/-- Private: Duhamel formula in the reparametrized time. -/
lemma aux_duhamel [Countable ι] (m : RowModel ι) (Q' : ι → ℝ → ℝ) {t₁ T : ℝ}
    (hT : T ∈ Ico (0:ℝ) t₁) (hsol : IsRowSolution m t₁ Q') (Re ψ : ℝ → ℝ)
    (hRe : ∀ u ∈ Icc (0:ℝ) T, Re u = m.risk Q' u)
    (hψ : ∀ u, HasDerivAt ψ (m.η / Real.sqrt (Re u)) u) (hψ0 : ψ 0 = 0) (i : ι) :
    ∀ u ∈ Icc (0:ℝ) T, Q' i u = Real.exp (-(2 * m.d i * ψ u)) * m.Q0 i +
      m.η ^ 2 * m.v i * ∫ w in (0:ℝ)..u, Real.exp (-(2 * m.d i * (ψ u - ψ w))) := by
  intro u hu
  obtain ⟨hQ0, -, -, hrpos, hder⟩ := hsol
  have huT : u ∈ Icc (0:ℝ) T := hu
  have hsub : Icc (0:ℝ) u ⊆ Ico (0:ℝ) t₁ := fun w hw => ⟨hw.1, lt_of_le_of_lt hw.2 (lt_of_le_of_lt hu.2 hT.2)⟩
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 (fun x => (hψ x).continuousAt)
  have hQc : ContinuousOn (Q' i) (Icc 0 u) := fun w hw =>
    (hder w (hsub hw) i).continuousWithinAt.mono hsub
  set y : ℝ → ℝ := fun w => Real.exp (2 * m.d i * ψ w) * Q' i w with hy
  have hyc : ContinuousOn y (Icc 0 u) :=
    ((by fun_prop : Continuous fun w => Real.exp (2 * m.d i * ψ w)).continuousOn).mul hQc
  have hyd : ∀ w ∈ Ioo (0:ℝ) u, HasDerivWithinAt y
      (Real.exp (2 * m.d i * ψ w) * m.η ^ 2 * m.v i) (Ioi w) w := by
    intro w hw
    have hwT : w ∈ Icc (0:ℝ) T := ⟨hw.1.le, le_trans hw.2.le hu.2⟩
    have hwI : w ∈ Ico (0:ℝ) t₁ := hsub ⟨hw.1.le, hw.2.le⟩
    have hQd : HasDerivAt (Q' i) (-(2 * m.η * m.d i) / Real.sqrt (m.risk Q' w) * Q' i w
        + m.η ^ 2 * m.v i) w :=
      (hder w hwI i).hasDerivAt (Ico_mem_nhds hw.1 (lt_of_lt_of_le hw.2 (le_trans hu.2 hT.2.le)))
    have h1 : HasDerivAt (fun w => Real.exp (2 * m.d i * ψ w))
        (Real.exp (2 * m.d i * ψ w) * (2 * m.d i * (m.η / Real.sqrt (Re w)))) w :=
      (((hψ w).const_mul (2 * m.d i)).exp)
    have h2 := h1.mul hQd
    refine (h2.hasDerivWithinAt).congr_deriv ?_
    rw [hRe w hwT]
    have hpos : 0 < Real.sqrt (m.risk Q' w) := Real.sqrt_pos.2 (hrpos w hwI)
    field_simp
    ring
  have hyint : IntervalIntegrable (fun w => Real.exp (2 * m.d i * ψ w) * m.η ^ 2 * m.v i)
      volume 0 u := by
    apply Continuous.intervalIntegrable; fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hu.1 hyc hyd hyint
  have hy0 : y 0 = m.Q0 i := by
    simp [hy, hψ0, hQ0 i]
  have hyu : Real.exp (2 * m.d i * ψ u) * Q' i u = m.Q0 i +
      ∫ w in (0:ℝ)..u, Real.exp (2 * m.d i * ψ w) * m.η ^ 2 * m.v i := by
    have h1 : y u = (∫ w in (0:ℝ)..u, Real.exp (2 * m.d i * ψ w) * m.η ^ 2 * m.v i) + y 0 := by
      linarith [hftc]
    calc Real.exp (2 * m.d i * ψ u) * Q' i u = y u := rfl
      _ = _ := h1
      _ = _ := by rw [hy0]; ring
  have hq : Q' i u = Real.exp (-(2 * m.d i * ψ u)) *
      (m.Q0 i + ∫ w in (0:ℝ)..u, Real.exp (2 * m.d i * ψ w) * m.η ^ 2 * m.v i) := by
    rw [← hyu, ← mul_assoc, ← Real.exp_add]
    simp
  rw [hq, mul_add, mul_comm _ (m.Q0 i)]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  have : m.η ^ 2 * m.v i * ∫ w in (0:ℝ)..u, Real.exp (-(2 * m.d i * (ψ u - ψ w))) =
      ∫ w in (0:ℝ)..u, m.η ^ 2 * m.v i * Real.exp (-(2 * m.d i * (ψ u - ψ w))) :=
    (intervalIntegral.integral_const_mul _ _).symm
  rw [this]
  apply intervalIntegral.integral_congr
  intro w _
  simp only
  have e : Real.exp (-(2 * m.d i * (ψ u - ψ w))) =
      Real.exp (-(2 * m.d i * ψ u)) * Real.exp (2 * m.d i * ψ w) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]; ring

/-- Private: change of variables `z = ψ(w)` in the Duhamel integral. -/
lemma aux_subst (η : ℝ) (hη : 0 < η) (Re ψ χ : ℝ → ℝ) (hc : Continuous Re)
    (hpos : ∀ u, 0 < Re u) (hψ0 : ψ 0 = 0)
    (hψ : ∀ u, HasDerivAt ψ (η / Real.sqrt (Re u)) u) (hχψ : ∀ u, χ (ψ u) = u)
    (hχ : ∀ u, HasDerivAt χ (Real.sqrt (Re u) / η) (ψ u)) (d u : ℝ) :
    ∫ w in (0:ℝ)..u, Real.exp (-(2 * d * (ψ u - ψ w))) =
      (1 / η) * ∫ z in (0:ℝ)..ψ u, Real.exp (-(2 * d * (ψ u - z))) * Real.sqrt (Re (χ z)) := by
  have hcont' : Continuous (fun v => η / Real.sqrt (Re v)) :=
    continuous_const.div hc.sqrt (fun v => (Real.sqrt_pos.2 (hpos v)).ne')
  have hgc : ContinuousOn (fun z => Real.exp (-(2 * d * (ψ u - z))) * Real.sqrt (Re (χ z)) / η)
      (ψ '' Set.uIcc 0 u) := by
    rintro z ⟨w, -, rfl⟩
    have hχc : ContinuousAt χ (ψ w) := (hχ w).continuousAt
    have h1 : ContinuousAt (fun z => Real.sqrt (Re (χ z))) (ψ w) :=
      (hc.sqrt.continuousAt).comp hχc
    have h2 : Continuous (fun z : ℝ => Real.exp (-(2 * d * (ψ u - z)))) := by fun_prop
    exact ((h2.continuousAt.mul h1).div_const η).continuousWithinAt
  have key := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := u) (f := ψ)
    (f' := fun w => η / Real.sqrt (Re w)) (g := fun z => Real.exp (-(2 * d * (ψ u - z))) *
      Real.sqrt (Re (χ z)) / η) (fun x _ => hψ x) hcont'.continuousOn hgc
  rw [hψ0] at key
  have hl : ∫ w in (0:ℝ)..u, Real.exp (-(2 * d * (ψ u - ψ w))) =
      ∫ x in (0:ℝ)..u, ((fun z => Real.exp (-(2 * d * (ψ u - z))) *
        Real.sqrt (Re (χ z)) / η) ∘ ψ) x * (η / Real.sqrt (Re x)) := by
    apply intervalIntegral.integral_congr
    intro w _
    simp only [Function.comp, hχψ]
    have := Real.sqrt_pos.2 (hpos w)
    field_simp
  rw [hl, key, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro z _
  simp only
  ring

/-- Private: the core of uniqueness and maximality. Any row solution on `[0,t₁)` and any
`T ∈ [0,t₁)` give an intrinsic time `σ` with `t(σ) = T` at which the rows are the `E_i`. -/
lemma aux_uniq [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    (Q' : ι → ℝ → ℝ) {t₁ T : ℝ} (hT : T ∈ Ico (0:ℝ) t₁) (hsol : IsRowSolution m t₁ Q') :
    ∃ σ : ℝ, 0 ≤ σ ∧ clockTime m Q σ = T ∧ ∀ i, Q' i T = rowEnergy m Q i σ := by
  have hη := m.η_pos
  rcases hT.1.eq_or_lt with h0 | hTpos
  · refine ⟨0, le_rfl, ?_, fun i => ?_⟩
    · rw [aux_clockTime_zero, ← h0]
    · rw [← h0, hsol.1 i]
      simp [rowEnergy]
  have hsol' := hsol
  obtain ⟨hQ0, -, hrc, hrpos, -⟩ := hsol
  -- clamped risk
  set cl : ℝ → ℝ := fun u => min (max u 0) T with hcl
  have hclc : Continuous cl := (continuous_id.max continuous_const).min continuous_const
  have hclmem : ∀ u, cl u ∈ Ico (0:ℝ) t₁ := fun u =>
    ⟨le_min (le_max_right _ _) hT.1, lt_of_le_of_lt (min_le_right _ _) hT.2⟩
  set Re : ℝ → ℝ := fun u => m.risk Q' (cl u) with hRe
  have hRec : Continuous Re := hrc.comp_continuous hclc hclmem
  have hRepos : ∀ u, 0 < Re u := fun u => hrpos _ (hclmem u)
  have hReeq : ∀ u ∈ Icc (0:ℝ) T, Re u = m.risk Q' u := by
    intro u hu
    simp only [hRe, hcl, max_eq_left hu.1, min_eq_left hu.2]
  obtain ⟨ψ, χ, hψ0, hψmono, hψd, hχψ, hχd⟩ := aux_reparam m.η hη Re hRec hRepos
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 (fun x => (hψd x).continuousAt)
  set σ := ψ T with hσdef
  have hσpos : 0 < σ := by rw [← hψ0]; exact hψmono hTpos
  -- surjectivity onto [0,σ]
  have hrange : ∀ s ∈ Icc (0:ℝ) σ, ∃ w ∈ Icc (0:ℝ) T, ψ w = s := by
    intro s hs
    have := intermediate_value_Icc hT.1 hψc.continuousOn
    rw [hψ0] at this
    exact this hs
  have hχcont : ∀ s ∈ Icc (0:ℝ) σ, ContinuousAt χ s := by
    intro s hs
    obtain ⟨w, -, rfl⟩ := hrange s hs
    exact (hχd w).continuousAt
  have hψmem : ∀ u ∈ Icc (0:ℝ) T, ψ u ∈ Icc (0:ℝ) σ := by
    intro u hu
    refine ⟨?_, hψmono.monotone hu.2⟩
    rw [← hψ0]; exact hψmono.monotone hu.1
  -- Duhamel and substitution, for each row
  have hrow : ∀ i, ∀ u ∈ Icc (0:ℝ) T, Q' i u = Real.exp (-(2 * m.d i * ψ u)) * m.Q0 i +
      m.η * m.v i * ∫ z in (0:ℝ)..ψ u, Real.exp (-(2 * m.d i * (ψ u - z))) *
        Real.sqrt (Re (χ z)) := by
    intro i u hu
    rw [aux_duhamel m Q' hT hsol' Re ψ hReeq hψd hψ0 i u hu,
      aux_subst m.η hη Re ψ χ hRec hRepos hψ0 hψd hχψ hχd (m.d i) u]
    field_simp
  -- the Volterra equation for the reparametrized risk
  have hVol : ∀ u ∈ Icc (0:ℝ) T, Re u = m.forcing (ψ u) +
      oneSidedConv (fun z => Real.sqrt (Re (χ z))) m.kernel (ψ u) := by
    intro u hu
    have hs : 0 ≤ ψ u := (hψmem u hu).1
    have hrcont : ContinuousOn (fun z => Real.sqrt (Re (χ z))) (Icc 0 (ψ u)) := by
      intro z hz
      have hz' : z ∈ Icc (0:ℝ) σ := ⟨hz.1, le_trans hz.2 (hψmem u hu).2⟩
      exact ((hRec.sqrt.continuousAt).comp (hχcont z hz')).continuousWithinAt
    have h := (aux_sw m (fun z => Real.sqrt (Re (χ z))) hs hrcont).2
    rw [← h, hReeq u hu]
    unfold RowModel.risk
    congr 1
    refine tsum_congr (fun i => ?_)
    rw [hrow i u hu]
    ring
  -- apply local uniqueness
  have hsolR : IsVolterraSolOn m σ (fun z => Re (χ z)) := by
    refine ⟨?_, fun s _ => (hRepos _).le, ?_⟩
    · intro s hs
      exact ((hRec.continuousAt).comp (hχcont s hs)).continuousWithinAt
    · intro s hs
      obtain ⟨w, hw, rfl⟩ := hrange s hs
      simp only [hχψ]
      exact hVol w hw
  have hsolQ : IsVolterraSolOn m σ Q :=
    ⟨hQ.1.mono Icc_subset_Ici_self, fun s hs => hQ.2.1 s hs.1, fun s hs => hQ.2.2 s hs.1⟩
  have hEq := thm_app_phase_volterra_ii m σ hσpos _ _ hsolR hsolQ
  -- identify the inverse with `clockTime`
  have hχclock : ∀ s ∈ Icc (0:ℝ) σ, χ s = clockTime m Q s := by
    intro s hs
    have hsub : Set.uIcc (0:ℝ) s ⊆ Icc 0 σ := by
      rw [Set.uIcc_of_le hs.1]; exact Icc_subset_Icc le_rfl hs.2
    have hder : ∀ x ∈ Set.uIcc (0:ℝ) s, HasDerivAt χ (Real.sqrt (Q x) / m.η) x := by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hrange x (hsub hx)
      have := hEq (ψ w) (hψmem w hw)
      simp only [hχψ] at this
      rw [← this]
      exact hχd w
    have hint : IntervalIntegrable (fun x => Real.sqrt (Q x) / m.η) volume 0 s :=
      (aux_sqrtQ_intInt m Q hQ le_rfl hs.1).div_const _
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
    have hχ0 : χ 0 = 0 := by simpa [hψ0] using hχψ 0
    rw [hχ0, sub_zero] at this
    rw [← this]
    unfold clockTime
    rw [intervalIntegral.integral_div, one_div, inv_mul_eq_div]
  refine ⟨σ, hσpos.le, ?_, fun i => ?_⟩
  · rw [← hχclock σ ⟨hσpos.le, le_rfl⟩, hσdef, hχψ]
  · rw [hrow i T ⟨hT.1, le_rfl⟩]
    unfold rowEnergy
    rw [mul_comm, ← hσdef]
    congr 2
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le hσpos.le] at hz
    simp only
    have := hEq z hz
    rw [← this]

/-- Private: clause 8, uniqueness. -/
lemma aux_clause8 [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q) :
    ∀ t₁ : ℝ, ENNReal.ofReal t₁ ≤ tStar m Q → ∀ Q' : ι → ℝ → ℝ, IsRowSolution m t₁ Q' →
      ∀ i : ι, ∀ t ∈ Ico (0:ℝ) t₁, Q' i t = rowsInStepTime m Q i t := by
  intro t₁ _ Q' hsol i t ht
  obtain ⟨σ, hσ, hcσ, hrow⟩ := aux_uniq m Q hQ Q' ht hsol
  rw [hrow i]
  unfold rowsInStepTime
  congr 1
  rw [← hcσ, aux_clock_left m Q hQ hσ]

/-- Private: clause 9, maximality. -/
lemma aux_clause9 [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q) :
    ∀ t₁ : ℝ, tStar m Q < ENNReal.ofReal t₁ → ∀ Q' : ι → ℝ → ℝ, ¬ IsRowSolution m t₁ Q' := by
  intro t₁ h Q' hsol
  have hfin : tStar m Q ≠ ⊤ := ne_top_of_lt h
  have hT0 : 0 < (tStar m Q).toReal := ENNReal.toReal_pos (aux_tStar_pos m Q hQ).ne' hfin
  have hT1 : (tStar m Q).toReal < t₁ := (ENNReal.toReal_lt_of_lt_ofReal h)
  obtain ⟨σ, hσ, hcσ, -⟩ := aux_uniq m Q hQ Q' (T := (tStar m Q).toReal) ⟨hT0.le, hT1⟩ hsol
  have hmem : (tStar m Q).toReal ∈ clockTime m Q '' Ici (0:ℝ) := ⟨σ, Set.mem_Ici.2 hσ, hcσ⟩
  rw [aux_clause5 m Q hQ] at hmem
  have := hmem.2
  rw [ENNReal.ofReal_toReal hfin] at this
  exact lt_irrefl _ this

/-- `thm:app-phase-clock`, snapshot `cr-2026-10-23`: one declaration of record, a conjunction
of the clauses of the source statement.

LaTeX (verbatim, `section.tex` l.377–399):
```
\begin{theorem}[Clock and row equations]\label{thm:app-phase-clock}
Assume (M1) and let $Q$ be the solution of \cref{thm:app-phase-volterra}.
For $i\in\mathcal I$ and $s\ge0$ put
\[
E_i(s)\defeq\fQ_i(0)e^{-2\mathfrak d_is}+\lr\mathfrak v_i\int_0^se^{-2\mathfrak d_i(s-v)}\sqrt{Q(v)}\,\dif v,\qquad
t(s)\defeq\frac1\lr\int_0^s\sqrt{Q(v)}\,\dif v,
\]
and $t_*\defeq\lim_{s\to\infty}t(s)\in(0,\infty]$. Then
$\frac12\sum_i\mu_iE_i(s)=Q(s)$ for every $s$, and $t$ is continuously
differentiable and strictly increasing from $[0,\infty)$ onto $[0,t_*)$. Its
inverse is the clock
\begin{equation}\label{eqn:app-phase-clock}
\clock(t)=\int_0^t\frac{\lr}{\sqrt{\fRisk(t')}}\,\dif t',
\end{equation}
where $\fQ_i(t)\defeq E_i(\clock(t))$ and $\fRisk(t)\defeq Q(\clock(t))$ solve
\cref{eqn:app-phase-rows} on $[0,t_*)$ with continuous positive risk. Every
solution of \cref{eqn:app-phase-rows} with continuous positive risk on an
interval $[0,t_1)$ agrees with this one there, and $[0,t_*)$ is the maximal
such interval. If $\mathcal S>0$, then $t_*=\infty$ and
$\fRisk(t)\to\lr^2\mathcal S^2/4$ as $t\to\infty$. If $\mathcal S=0$, then
$t_*=\lr^{-1}\int_0^\infty\sqrt{F(s)}\,\dif s$, and $\fRisk(t)\to0$ as
$t\uparrow t_*$ when $t_*<\infty$.
\end{theorem}
```
Part (identity): `(1/2) ∑ μ_i E_i(s) = Q(s)` for `s ≥ 0`. Part (`t(·)`): `t` is `C¹`, strictly
increasing, from `[0,∞)` onto `[0,t_*)`, with `0 < t_*`. Part (clock): `ϕ(t) = ∫_0^t η/√𝔑`.
Part (rows): the rows `𝔔_i(t) = E_i(ϕ(t))` solve (M3) on each `[0,t₁)` with `t_* ≥ t₁`.
Part (uniqueness): any solution of (M3) on `[0,t₁)` with `t₁ ≤ t_*` agrees with them.
Part (maximality): no solution of (M3) on `[0,t₁)` with `t₁ > t_*`. Part (limits): for
`𝒮 > 0`, `t_* = ∞` and `𝔑(t) → η²𝒮²/4`; for `𝒮 = 0`, `t_*` is the lintegral
`η⁻¹ ∫_0^∞ √F`, and `𝔑(t) → 0` as `t ↑ t_*` when `t_* < ∞`. -/
theorem thm_app_phase_clock [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ)
    (hQ : IsVolterraSol m Q) :
    (∀ s ∈ Ici (0:ℝ), (1 / 2 : ℝ) * ∑' i, m.μ i * rowEnergy m Q i s = Q s) ∧
    (0 < tStar m Q) ∧
    ContDiffOn ℝ 1 (clockTime m Q) (Ici (0:ℝ)) ∧
    StrictMonoOn (clockTime m Q) (Ici (0:ℝ)) ∧
    (clockTime m Q '' Ici (0:ℝ) = {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < tStar m Q}) ∧
    (∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < tStar m Q →
      clock m Q t = ∫ t' in (0:ℝ)..t, m.η / Real.sqrt (riskClock m Q t')) ∧
    (∀ t₁ : ℝ, ENNReal.ofReal t₁ ≤ tStar m Q → IsRowSolution m t₁ (rowsInStepTime m Q)) ∧
    (∀ t₁ : ℝ, ENNReal.ofReal t₁ ≤ tStar m Q → ∀ Q' : ι → ℝ → ℝ, IsRowSolution m t₁ Q' →
      ∀ i : ι, ∀ t ∈ Ico (0:ℝ) t₁, Q' i t = rowsInStepTime m Q i t) ∧
    (∀ t₁ : ℝ, tStar m Q < ENNReal.ofReal t₁ → ∀ Q' : ι → ℝ → ℝ, ¬ IsRowSolution m t₁ Q') ∧
    (0 < m.S → tStar m Q = ⊤ ∧
      Tendsto (m.risk (rowsInStepTime m Q)) atTop (𝓝 (m.η ^ 2 * m.S ^ 2 / 4))) ∧
    (m.S = 0 →
      tStar m Q = ENNReal.ofReal (m.η⁻¹) *
          ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (Real.sqrt (m.forcing s)) ∧
        (tStar m Q ≠ ⊤ →
          Tendsto (m.risk (rowsInStepTime m Q)) (𝓝[<] (tStar m Q).toReal) (𝓝 0))) := by
  exact ⟨fun s hs => (aux_clause1 m Q hQ hs).2, aux_tStar_pos m Q hQ, aux_clause3 m Q hQ,
    aux_clockTime_strictMonoOn m Q hQ, aux_clause5 m Q hQ,
    fun t ht0 ht => aux_clause6 m Q hQ ht0 ht,
    fun t₁ h => aux_clause7 m Q hQ h, aux_clause8 m Q hQ, aux_clause9 m Q hQ,
    fun hS => aux_clause10 m Q hQ hS, fun hS => aux_clause11 m Q hQ hS⟩

/-- Private: the first hitting time is at most any real point `u ≥ 0` where the level is reached. -/
lemma aux_firstHit_le (R : ℝ → ℝ) (a u : ℝ) (hu : 0 ≤ u) (h : R u ≤ a) :
    firstHit R a ≤ ENNReal.ofReal u := by
  unfold firstHit
  have h' : R ((u.toNNReal : ℝ≥0) : ℝ) ≤ a := by rw [Real.coe_toNNReal _ hu]; exact h
  exact iInf₂_le (f := fun (t : ℝ≥0) (_ : R t ≤ a) => (t : ℝ≥0∞)) u.toNNReal h'

/-- Private: lower bound for the step-time hitting time. If every real `u ≥ 0` with `Q u ≤ a`
satisfies `x ≤ u`, then `ofReal (clockTime x) ≤ t_a`. -/
lemma aux_hit_le_clock [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    (a x : ℝ) (hx : 0 ≤ x) (hA : ∀ u : ℝ, 0 ≤ u → Q u ≤ a → x ≤ u) :
    ENNReal.ofReal (clockTime m Q x) ≤ firstHit (riskClock m Q) a := by
  refine le_iInf₂ fun (t : ℝ≥0) (ht : riskClock m Q t ≤ a) => ?_
  by_cases hk : ENNReal.ofReal (t : ℝ) < tStar m Q
  · obtain ⟨hc0, hcl⟩ := aux_clock_spec m Q hQ t.coe_nonneg hk
    have hmono := aux_clockTime_strictMonoOn m Q hQ
    have hxle : x ≤ clock m Q t := hA _ hc0 ht
    have h1 : clockTime m Q x ≤ clockTime m Q (clock m Q t) :=
      hmono.monotoneOn (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hc0) hxle
    rw [hcl] at h1
    calc ENNReal.ofReal (clockTime m Q x) ≤ ENNReal.ofReal (t : ℝ) :=
          ENNReal.ofReal_le_ofReal h1
      _ = (t : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
  · exact le_trans (aux_ofReal_le_tStar m Q hx) ((not_lt.1 hk).trans_eq ENNReal.ofReal_coe_nnreal)

/-- Private: the level is attained at `s = H_Q(a)` when that hitting time is finite. -/
lemma aux_hit_attained (Q : ℝ → ℝ) (a : ℝ) (hQ0 : ContinuousOn Q (Ici 0))
    (hfin : firstHit Q a ≠ ⊤) : Q (firstHit Q a).toReal ≤ a := by
  have hs0 : (0:ℝ) ≤ (firstHit Q a).toReal := ENNReal.toReal_nonneg
  have hH : ENNReal.ofReal (firstHit Q a).toReal = firstHit Q a := ENNReal.ofReal_toReal hfin
  by_contra hlt
  push_neg at hlt
  have hev : ∀ᶠ u in 𝓝[Ici (0:ℝ)] (firstHit Q a).toReal, a < Q u :=
    ((hQ0 _ hs0).tendsto).eventually (lt_mem_nhds hlt)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  have hlt2 : firstHit Q a < ENNReal.ofReal ((firstHit Q a).toReal + δ) := by
    have h3 : ENNReal.ofReal (firstHit Q a).toReal < ENNReal.ofReal ((firstHit Q a).toReal + δ) :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    rwa [hH] at h3
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (⨅ (_ : Q t ≤ a), (t : ℝ≥0∞)) < ENNReal.ofReal ((firstHit Q a).toReal + δ) := by
    unfold firstHit at hlt2
    exact iInf_lt_iff.1 hlt2
  obtain ⟨hQt, htlt⟩ := iInf_lt_iff.1 ht
  have hle : firstHit Q a ≤ (t : ℝ≥0∞) := iInf₂_le (f := fun (t : ℝ≥0) (_ : Q t ≤ a) => (t : ℝ≥0∞)) t hQt
  have hst : (firstHit Q a).toReal ≤ (t : ℝ) := by
    have h2 : ENNReal.ofReal (firstHit Q a).toReal ≤ ENNReal.ofReal (t : ℝ) := by
      rw [hH, ENNReal.ofReal_coe_nnreal]; exact hle
    exact (ENNReal.ofReal_le_ofReal_iff t.coe_nonneg).1 h2
  have htlt' : (t : ℝ) < (firstHit Q a).toReal + δ := by
    rw [← ENNReal.ofReal_coe_nnreal] at htlt
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 htlt
  have hmem : (t : ℝ) ∈ Metric.ball ((firstHit Q a).toReal) δ ∩ Ici (0:ℝ) := by
    refine ⟨?_, Set.mem_Ici.2 t.coe_nonneg⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have := hball hmem
  simp only [Set.mem_setOf_eq] at this
  linarith

/-- Private: `∫_0^f √F ≤ ∫_0^f √Q` for `f ≥ 0`, since `F ≤ Q` on `[0,∞)`. -/
lemma aux_sqrtF_le_sqrtQ [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    {f : ℝ} (hf : 0 ≤ f) :
    ∫ v in (0:ℝ)..f, Real.sqrt (m.forcing v) ≤ ∫ v in (0:ℝ)..f, Real.sqrt (Q v) := by
  have hFQ : ∀ x ∈ Icc (0:ℝ) f, Real.sqrt (m.forcing x) ≤ Real.sqrt (Q x) := fun x hx =>
    Real.sqrt_le_sqrt ((thm_app_phase_volterra_iii m Q hQ x (Set.mem_Ici.2 hx.1)).2.1)
  by_cases hF : IntervalIntegrable (fun v => Real.sqrt (m.forcing v)) MeasureTheory.volume 0 f
  · exact intervalIntegral.integral_mono_on hf hF (aux_sqrtQ_intInt m Q hQ le_rfl hf) hFQ
  · rw [intervalIntegral.integral_undef hF]
    exact intervalIntegral.integral_nonneg hf (fun u _ => Real.sqrt_nonneg _)

/-- `thm:app-phase-hitting`, part (i) of 2, snapshot `cr-2026-10-23`.
Under `𝒮 > 0`, `ε > 0` and `η = 2√ε/𝒮` (so `k̄ = √ε`), for every `a > 0`:
`H_Q(a) ≥ H_F(a)`, `t_a ≥ η⁻¹ ∫_0^{H_F(a)} √F`, and `t_a = t(H_Q(a))` when `H_Q(a) < ∞`.
Here `H_Q(a) = firstHit Q a`, `H_F(a) = firstHit F a` and `t_a = firstHit (riskClock) a`.

LaTeX (verbatim, `section.tex` l.445–470):
```
\begin{theorem}[Hitting times]\label{thm:app-phase-hitting}
Assume (M1) and $\mathcal S>0$, fix $\epsilon>0$, and take
$\lr=2\sqrt\epsilon/\mathcal S$, so that $\bar k=\sqrt\epsilon$.
\begin{enumerate}[label=(\roman*)]
\item For every $a>0$, $H_Q(a)\ge H_F(a)$ and
\[
t_a\ge\frac1\lr\int_0^{H_F(a)}\sqrt{F(s)}\,\dif s .
\]
If $H_Q(a)<\infty$, then $t_a=t(H_Q(a))$ with $t(\cdot)$ of
\cref{thm:app-phase-clock}.
\item Fix $c_0>1$ with $F_0>c_0\epsilon$, let $s_c$ be the time with
$F(s_c)=c_0\epsilon$, and put
\[
C_\ast\defeq\max_{0\le s\le s_c}\frac{(k*\sqrt F)(s)}{\sqrt{\epsilon F(s)}},\qquad
m_\ast\defeq\frac{C_\ast}{1-1/(2\sqrt{c_0})} .
\]
Then $0\le C_\ast\le\sqrt{F_0/(c_0\epsilon)}$ and
\begin{equation}\label{eqn:app-phase-upper}
Q(s)\le F(s)+m_\ast\sqrt{\epsilon F(s)}\qquad(0\le s\le s_c).
\end{equation}
Consequently, for every $T\ge c_0+m_\ast\sqrt{c_0}$,
\begin{equation}\label{eqn:app-phase-sandwich}
\frac1\lr\int_0^{H_F(T\epsilon)}\sqrt{F(s)}\,\dif s\ \le\ t_{T\epsilon}\ \le\ \frac1\lr\int_0^{s_c}\sqrt{F(s)+m_\ast\sqrt{\epsilon F(s)}}\,\dif s .
\end{equation}
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_phase_hitting_i [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ)
    (hQ : IsVolterraSol m Q) (hS : 0 < m.S) (ε : ℝ) (hε : 0 < ε)
    (hη : m.η = 2 * Real.sqrt ε / m.S) :
    ∀ a : ℝ, 0 < a →
      firstHit Q a ≥ firstHit m.forcing a ∧
      ENNReal.ofReal ((1 / m.η) *
          ∫ s in (0:ℝ)..(firstHit m.forcing a).toReal, Real.sqrt (m.forcing s))
        ≤ firstHit (riskClock m Q) a ∧
      (firstHit Q a ≠ ⊤ →
        firstHit (riskClock m Q) a = ENNReal.ofReal (clockTime m Q (firstHit Q a).toReal)) := by
  intro a _ha
  have hF_le : ∀ s ∈ Ici (0:ℝ), m.forcing s ≤ Q s := fun s hs =>
    (thm_app_phase_volterra_iii m Q hQ s hs).2.1
  refine ⟨?_, ?_, ?_⟩
  · -- (i) `H_Q(a) ≥ H_F(a)`
    have key : ∀ t : ℝ≥0, Q t ≤ a → firstHit m.forcing a ≤ (t : ℝ≥0∞) := fun t ht =>
      iInf₂_le (f := fun (s : ℝ≥0) (_ : m.forcing s ≤ a) => (s : ℝ≥0∞)) t
        (le_trans (hF_le (t : ℝ) (Set.mem_Ici.2 t.coe_nonneg)) ht)
    exact le_iInf₂ fun (t : ℝ≥0) (ht : Q t ≤ a) => key t ht
  · -- (i) the lower bound on `t_a`
    have hx : (0:ℝ) ≤ (firstHit m.forcing a).toReal := ENNReal.toReal_nonneg
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (aux_hit_le_clock m Q hQ a _ hx (fun u hu hQu => ?_))
    · unfold clockTime
      exact mul_le_mul_of_nonneg_left (aux_sqrtF_le_sqrtQ m Q hQ hx)
        (one_div_nonneg.2 m.η_pos.le)
    · have h1 : firstHit m.forcing a ≤ ENNReal.ofReal u :=
        aux_firstHit_le m.forcing a u hu (le_trans (hF_le u hu) hQu)
      exact ENNReal.toReal_le_of_le_ofReal hu h1
  · -- (i) the clock identity when `H_Q(a) < ∞`
    intro hfin
    have hs0 : (0:ℝ) ≤ (firstHit Q a).toReal := ENNReal.toReal_nonneg
    apply le_antisymm
    · have hQs := aux_hit_attained Q a hQ.1 hfin
      have hct0 : 0 ≤ clockTime m Q (firstHit Q a).toReal := by
        unfold clockTime
        exact mul_nonneg (one_div_nonneg.2 m.η_pos.le)
          (intervalIntegral.integral_nonneg hs0 (fun u _ => Real.sqrt_nonneg _))
        
      have h1 : riskClock m Q ((clockTime m Q (firstHit Q a).toReal).toNNReal : ℝ) ≤ a := by
        rw [Real.coe_toNNReal _ hct0]
        unfold riskClock
        rw [aux_clock_left m Q hQ hs0]
        exact hQs
      unfold firstHit
      exact iInf₂_le (f := fun (t : ℝ≥0) (_ : riskClock m Q t ≤ a) => (t : ℝ≥0∞))
        (clockTime m Q (firstHit Q a).toReal).toNNReal h1
    · refine aux_hit_le_clock m Q hQ a _ hs0 (fun u hu hQu => ?_)
      have h1 := aux_firstHit_le Q a u hu hQu
      rw [← ENNReal.ofReal_toReal hfin] at h1
      exact (ENNReal.ofReal_le_ofReal_iff hu).1 h1

/-- Private (P-H.3.P3): the kernel is nonnegative. -/
lemma aux_h_kernel_nonneg (m : RowModel ι) (s : ℝ) : 0 ≤ m.kernel s := by
  unfold RowModel.kernel
  exact mul_nonneg (by linarith [m.η_pos])
    (tsum_nonneg fun i => mul_nonneg (mul_nonneg (m.μ_pos i).le (m.v_nonneg i)) (Real.exp_pos _).le)

/-- Private (P-H.3.P3): the kernel is interval integrable on `[0,s]`. -/
lemma aux_h_kernel_int [Countable ι] (m : RowModel ι) {s : ℝ} (hs : 0 ≤ s) :
    IntervalIntegrable m.kernel volume 0 s :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hs).2
    ((lem_app_phase_kernel_ii m).1.mono_set Ioc_subset_Ioi_self)

/-- Private (P-H.3.P3): `∫_0^s k ≤ k̄`. -/
lemma aux_h_kernel_total [Countable ι] (m : RowModel ι) {s : ℝ} (hs : 0 ≤ s) :
    ∫ v in (0:ℝ)..s, m.kernel v ≤ m.kbar := by
  rw [intervalIntegral.integral_of_le hs, ← (lem_app_phase_kernel_ii m).2.1]
  exact setIntegral_mono_set (lem_app_phase_kernel_ii m).1
    (Filter.Eventually.of_forall fun v => aux_h_kernel_nonneg m v)
    (Filter.Eventually.of_forall fun v hv => Ioc_subset_Ioi_self hv)

/-- Private (P-H.3.P3): integrability of a continuous profile against the kernel. -/
lemma aux_h_conv_int [Countable ι] (m : RowModel ι) {sc s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ sc) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 sc)) :
    IntervalIntegrable (fun v => g (s - v) * m.kernel v) volume 0 s := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hs0]
  have hk : IntegrableOn m.kernel (Icc 0 s) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hs0).1 (aux_h_kernel_int m hs0)
  have hgc : ContinuousOn (fun v => g (s - v)) (Icc 0 s) := by
    refine hg.comp (continuous_const.sub continuous_id).continuousOn ?_
    intro v hv
    exact ⟨by linarith [hv.2], by linarith [hv.1]⟩
  exact IntegrableOn.continuousOn_mul hgc hk isCompact_Icc

/-- Private (P-H.3.P3): monotonicity of the convolution in the profile. -/
lemma aux_h_conv_mono [Countable ι] (m : RowModel ι) {sc s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ sc) (g1 g2 : ℝ → ℝ) (h1 : ContinuousOn g1 (Icc 0 sc))
    (h2 : ContinuousOn g2 (Icc 0 sc)) (hle : ∀ u ∈ Icc (0:ℝ) sc, g1 u ≤ g2 u) :
    oneSidedConv g1 m.kernel s ≤ oneSidedConv g2 m.kernel s := by
  unfold oneSidedConv
  refine intervalIntegral.integral_mono_on hs0 (aux_h_conv_int m hs0 hs g1 h1)
    (aux_h_conv_int m hs0 hs g2 h2) (fun v hv => ?_)
  exact mul_le_mul_of_nonneg_right
    (hle _ ⟨by linarith [hv.2], by linarith [hv.1]⟩) (aux_h_kernel_nonneg m v)

/-- Private (P-H.3.P3): nonnegativity of the convolution. -/
lemma aux_h_conv_nonneg [Countable ι] (m : RowModel ι) {s : ℝ} (hs0 : 0 ≤ s)
    (g : ℝ → ℝ) (hg : ∀ u ∈ Icc (0:ℝ) s, 0 ≤ g u) :
    0 ≤ oneSidedConv g m.kernel s := by
  unfold oneSidedConv
  refine intervalIntegral.integral_nonneg hs0 (fun v hv => ?_)
  exact mul_nonneg (hg _ ⟨by linarith [hv.2], by linarith [hv.1]⟩) (aux_h_kernel_nonneg m v)

/-- Private (P-H.3.P3): convolution with a constant. -/
lemma aux_h_conv_const (m : RowModel ι) (c s : ℝ) :
    oneSidedConv (fun _ => c) m.kernel s = c * ∫ v in (0:ℝ)..s, m.kernel v := by
  unfold oneSidedConv
  exact intervalIntegral.integral_const_mul _ _

/-- Private (P-H.3.P3): convolution with a profile shifted by a constant. -/
lemma aux_h_conv_add [Countable ι] (m : RowModel ι) {sc s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ sc) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 sc)) (c : ℝ) :
    oneSidedConv (fun u => g u + c) m.kernel s =
      oneSidedConv g m.kernel s + c * ∫ v in (0:ℝ)..s, m.kernel v := by
  rw [← aux_h_conv_const m c s]
  unfold oneSidedConv
  rw [← intervalIntegral.integral_add (aux_h_conv_int m hs0 hs g hg)
    (by simpa using aux_h_conv_int m hs0 hs (fun _ => c) continuousOn_const)]
  congr 1
  funext v
  ring

/-- Private (P-H.3.P3): `k̄ = √ε` under `η = 2√ε/𝒮`. -/
lemma aux_h_kbar (m : RowModel ι) (hS : 0 < m.S) (ε : ℝ)
    (hη : m.η = 2 * Real.sqrt ε / m.S) : m.kbar = Real.sqrt ε := by
  unfold RowModel.kbar
  rw [hη]
  field_simp

/-- Private (P-H.3.P3): conjuncts 1–2 of part (ii), and the pointwise bound by `C_*`. -/
lemma aux_h_cstar [Countable ι] (m : RowModel ι) (hS : 0 < m.S) (ε : ℝ) (hε : 0 < ε)
    (hη : m.η = 2 * Real.sqrt ε / m.S)
    (c₀ sc : ℝ) (hc₀ : 1 < c₀)
    (hsc : 0 ≤ sc) (hFsc : m.forcing sc = c₀ * ε) :
    0 ≤ cstar m ε sc ∧ cstar m ε sc ≤ Real.sqrt (m.F0 / (c₀ * ε)) ∧
    (∀ s ∈ Icc (0:ℝ) sc,
      oneSidedConv (fun u => Real.sqrt (m.forcing u)) m.kernel s ≤
        cstar m ε sc * Real.sqrt (ε * m.forcing s)) := by
  obtain ⟨hFc, hFanti, hF0eq, hFpos, -⟩ := lem_app_phase_kernel_i m
  have hkbar := aux_h_kbar m hS ε hη
  have hsF : ContinuousOn (fun u => Real.sqrt (m.forcing u)) (Icc 0 sc) :=
    (hFc.mono Icc_subset_Ici_self).sqrt
  have hFge : ∀ s ∈ Icc (0:ℝ) sc, c₀ * ε ≤ m.forcing s := fun s hs => by
    rw [← hFsc]
    exact hFanti.antitoneOn (Set.mem_Ici.2 hs.1) (Set.mem_Ici.2 hsc) hs.2
  have hFle : ∀ s ∈ Icc (0:ℝ) sc, m.forcing s ≤ m.F0 := fun s hs => by
    rw [← hF0eq]
    exact hFanti.antitoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs.1) hs.1
  have hF0pos : 0 < m.F0 := by rw [← hF0eq]; exact hFpos 0 (Set.mem_Ici.2 le_rfl)
  have hc0ε : 0 < c₀ * ε := mul_pos (by linarith) hε
  -- conv ≤ √F0 √ε
  have hconv : ∀ s ∈ Icc (0:ℝ) sc,
      oneSidedConv (fun u => Real.sqrt (m.forcing u)) m.kernel s ≤
        Real.sqrt m.F0 * Real.sqrt ε := by
    intro s hs
    calc oneSidedConv (fun u => Real.sqrt (m.forcing u)) m.kernel s
        ≤ oneSidedConv (fun _ => Real.sqrt m.F0) m.kernel s :=
          aux_h_conv_mono m hs.1 hs.2 _ _ hsF continuousOn_const (fun u hu =>
            Real.sqrt_le_sqrt (hFle u hu))
      _ = Real.sqrt m.F0 * ∫ v in (0:ℝ)..s, m.kernel v := aux_h_conv_const m _ _
      _ ≤ Real.sqrt m.F0 * Real.sqrt ε := by
          rw [← hkbar]
          exact mul_le_mul_of_nonneg_left (aux_h_kernel_total m hs.1) (Real.sqrt_nonneg _)
  have hratio : ∀ s ∈ Icc (0:ℝ) sc, hitRatio m ε s ≤ Real.sqrt (m.F0 / (c₀ * ε)) := by
    intro s hs
    have hFs : 0 < m.forcing s := hFpos s (Set.mem_Ici.2 hs.1)
    have hden : 0 < Real.sqrt (ε * m.forcing s) := Real.sqrt_pos.2 (mul_pos hε hFs)
    unfold hitRatio
    rw [div_le_iff₀ hden]
    refine (hconv s hs).trans ?_
    rw [← Real.sqrt_mul hF0pos.le, ← Real.sqrt_mul (div_nonneg hF0pos.le hc0ε.le)]
    apply Real.sqrt_le_sqrt
    have h1 := hFge s hs
    have : m.F0 / (c₀ * ε) * (ε * m.forcing s) = m.F0 * m.forcing s / c₀ := by
      field_simp
    rw [this, le_div_iff₀ (by linarith)]
    nlinarith [hF0pos, mul_le_mul_of_nonneg_left h1 hF0pos.le]
  have hbdd : BddAbove (hitRatio m ε '' Icc (0:ℝ) sc) :=
    ⟨_, by rintro _ ⟨s, hs, rfl⟩; exact hratio s hs⟩
  refine ⟨?_, ?_, ?_⟩
  · refine Real.sSup_nonneg ?_
    rintro _ ⟨s, hs, rfl⟩
    unfold hitRatio
    exact div_nonneg (aux_h_conv_nonneg m hs.1 _ (fun u _ => Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  · refine Real.sSup_le ?_ (Real.sqrt_nonneg _)
    rintro _ ⟨s, hs, rfl⟩
    exact hratio s hs
  · intro s hs
    have hFs : 0 < m.forcing s := hFpos s (Set.mem_Ici.2 hs.1)
    have hden : 0 < Real.sqrt (ε * m.forcing s) := Real.sqrt_pos.2 (mul_pos hε hFs)
    have h := le_csSup hbdd ⟨s, hs, rfl⟩
    unfold hitRatio at h
    rwa [div_le_iff₀ hden] at h

/-- Private (P-H.3.P3): conjunct 3 of part (ii), the supersolution bound. -/
lemma aux_h_upper [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ)
    (hQ : IsVolterraSol m Q) (hS : 0 < m.S) (ε : ℝ) (hε : 0 < ε)
    (hη : m.η = 2 * Real.sqrt ε / m.S)
    (c₀ sc : ℝ) (hc₀ : 1 < c₀) (hF₀ : c₀ * ε < m.F0)
    (hsc : 0 ≤ sc) (hFsc : m.forcing sc = c₀ * ε) :
    ∀ s ∈ Icc (0:ℝ) sc, Q s ≤ m.forcing s + mstar m c₀ ε sc * Real.sqrt (ε * m.forcing s) := by
  obtain ⟨hFc, hFanti, hF0eq, hFpos, -⟩ := lem_app_phase_kernel_i m
  obtain ⟨hC0, -, hCle⟩ := aux_h_cstar m hS ε hε hη c₀ sc hc₀ hsc hFsc
  have hkbar := aux_h_kbar m hS ε hη
  have hsc_pos : 0 < sc := by
    rcases hsc.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, hF0eq] at hFsc
      linarith
  have hsF : ContinuousOn (fun u => Real.sqrt (m.forcing u)) (Icc 0 sc) :=
    (hFc.mono Icc_subset_Ici_self).sqrt
  have hFge : ∀ s ∈ Icc (0:ℝ) sc, c₀ * ε ≤ m.forcing s := fun s hs => by
    rw [← hFsc]
    exact hFanti.antitoneOn (Set.mem_Ici.2 hs.1) (Set.mem_Ici.2 hsc) hs.2
  have hc0ε : 0 < c₀ * ε := mul_pos (by linarith) hε
  have hsqc : 1 < Real.sqrt c₀ := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hc₀
  have hδ : 0 < 1 - 1 / (2 * Real.sqrt c₀) := by
    have : 1 / (2 * Real.sqrt c₀) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    linarith
  set μs := mstar m c₀ ε sc with hμs
  have hμ : μs * (1 - 1 / (2 * Real.sqrt c₀)) = cstar m ε sc := by
    rw [hμs]; unfold mstar; exact div_mul_cancel₀ _ hδ.ne'
  have hμ0 : 0 ≤ μs := by
    rw [hμs]; unfold mstar; exact div_nonneg hC0 hδ.le
  set y : ℝ → ℝ := fun s => m.forcing s + μs * Real.sqrt (ε * m.forcing s) with hy
  have hFcI : ContinuousOn m.forcing (Icc 0 sc) := hFc.mono Icc_subset_Ici_self
  have hycont : ContinuousOn y (Icc 0 sc) :=
    hFcI.add (continuousOn_const.mul (continuousOn_const.mul hFcI).sqrt)
  have hFpos' : ∀ s ∈ Icc (0:ℝ) sc, 0 < m.forcing s := fun s hs =>
    hFpos s (Set.mem_Ici.2 hs.1)
  have hy_nonneg : ∀ s ∈ Icc (0:ℝ) sc, 0 ≤ y s := fun s hs =>
    add_nonneg (hFpos' s hs).le (mul_nonneg hμ0 (Real.sqrt_nonneg _))
  have hy_ge : ∀ s ∈ Icc (0:ℝ) sc, c₀ * ε ≤ y s := fun s hs => by
    have := mul_nonneg hμ0 (Real.sqrt_nonneg (ε * m.forcing s))
    have := hFge s hs
    show c₀ * ε ≤ m.forcing s + μs * Real.sqrt (ε * m.forcing s)
    linarith
  -- √y ≤ √F + μs √ε / 2
  have hsqrt_y : ∀ s ∈ Icc (0:ℝ) sc,
      Real.sqrt (y s) ≤ Real.sqrt (m.forcing s) + μs * Real.sqrt ε / 2 := by
    intro s hs
    have hFs := hFpos' s hs
    have hc : 0 ≤ μs * Real.sqrt ε / 2 := by positivity
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h1 : Real.sqrt (ε * m.forcing s) = Real.sqrt ε * Real.sqrt (m.forcing s) :=
      Real.sqrt_mul hε.le _
    have h2 := Real.sq_sqrt hFs.le
    show m.forcing s + μs * Real.sqrt (ε * m.forcing s) ≤ _
    rw [h1]
    nlinarith [sq_nonneg (μs * Real.sqrt ε / 2)]
  have hsub : ∀ s ∈ Icc (0:ℝ) sc,
      m.forcing s + oneSidedConv (fun u => Real.sqrt (y u)) m.kernel s ≤ y s := by
    intro s hs
    have hFs := hFpos' s hs
    have hr : 0 < Real.sqrt (ε * m.forcing s) := Real.sqrt_pos.2 (mul_pos hε hFs)
    have hy_sqrt_cont : ContinuousOn (fun u => Real.sqrt (y u)) (Icc 0 sc) := hycont.sqrt
    have hcc : 0 ≤ μs * Real.sqrt ε / 2 := by positivity
    have step1 : oneSidedConv (fun u => Real.sqrt (y u)) m.kernel s ≤
        oneSidedConv (fun u => Real.sqrt (m.forcing u) + μs * Real.sqrt ε / 2) m.kernel s :=
      aux_h_conv_mono m hs.1 hs.2 _ _ hy_sqrt_cont (hsF.add continuousOn_const)
        (fun u hu => hsqrt_y u hu)
    rw [aux_h_conv_add m hs.1 hs.2 _ hsF] at step1
    have hint : ∫ v in (0:ℝ)..s, m.kernel v ≤ Real.sqrt ε := hkbar ▸ aux_h_kernel_total m hs.1
    have step2 : μs * Real.sqrt ε / 2 * ∫ v in (0:ℝ)..s, m.kernel v ≤
        μs * Real.sqrt ε / 2 * Real.sqrt ε := mul_le_mul_of_nonneg_left hint hcc
    have hsq : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
    have hle := hCle s hs
    -- ε √c₀ ≤ √(ε F s)
    have hεr : ε * Real.sqrt c₀ ≤ Real.sqrt (ε * m.forcing s) := by
      rw [Real.le_sqrt (by positivity) (mul_pos hε hFs).le]
      have h3 := Real.sq_sqrt (by linarith : (0:ℝ) ≤ c₀)
      have h4 := mul_le_mul_of_nonneg_left (hFge s hs) hε.le
      calc (ε * Real.sqrt c₀) ^ 2 = ε * (c₀ * ε) := by rw [mul_pow, h3]; ring
        _ ≤ ε * m.forcing s := h4
    have hA : ε / 2 ≤ 1 / (2 * Real.sqrt c₀) * Real.sqrt (ε * m.forcing s) := by
      rw [one_div_mul_eq_div, le_div_iff₀ (by linarith)]
      nlinarith
    have hB : μs * (ε / 2) ≤ μs * (1 / (2 * Real.sqrt c₀) * Real.sqrt (ε * m.forcing s)) :=
      mul_le_mul_of_nonneg_left hA hμ0
    have hcs : cstar m ε sc * Real.sqrt (ε * m.forcing s) =
        (μs * (1 - 1 / (2 * Real.sqrt c₀))) * Real.sqrt (ε * m.forcing s) := by rw [hμ]
    show m.forcing s + _ ≤ m.forcing s + μs * Real.sqrt (ε * m.forcing s)
    have e1 : μs * Real.sqrt ε / 2 * Real.sqrt ε = μs * (ε / 2) := by
      linear_combination (μs / 2) * hsq
    nlinarith
  intro s hs
  have hmono := lem_app_phase_comparison sc hsc_pos m.kernel
    (fun s _ => aux_h_kernel_nonneg m s)
    ((lem_app_phase_kernel_ii m).1.mono_set Ioo_subset_Ioi_self)
    m.forcing hFcI (fun s hs => (hFpos' s hs).le) (c₀ * ε) hc0ε
    Q y (hQ.1.mono Icc_subset_Ici_self) (fun s hs => hQ.2.1 s (Set.mem_Ici.2 hs.1))
    hycont hy_nonneg hy_ge
    (fun s hs => (hQ.2.2 s (Set.mem_Ici.2 hs.1)).le) hsub s hs
  exact hmono

/-- Private (P-H.3.P3): `m_* ≥ 0` when `C_* ≥ 0` and `c₀ > 1`. -/
lemma aux_h_mstar_nonneg (m : RowModel ι) (ε sc c₀ : ℝ) (hc₀ : 1 < c₀)
    (hC0 : 0 ≤ cstar m ε sc) : 0 ≤ mstar m c₀ ε sc := by
  have hsqc : 1 < Real.sqrt c₀ := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hc₀
  have hδ : 0 < 1 - 1 / (2 * Real.sqrt c₀) := by
    have : 1 / (2 * Real.sqrt c₀) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    linarith
  unfold mstar
  exact div_nonneg hC0 hδ.le

/-- `thm:app-phase-hitting`, part (ii) of 2, snapshot `cr-2026-10-23`.
Under the same hypotheses as part (i), with `c₀ > 1`, `F_0 > c₀ ε`, and `s_c ≥ 0` with
`F(s_c) = c₀ ε`: `0 ≤ C_* ≤ √(F_0/(c₀ε))`; `Q(s) ≤ F(s) + m_* √(ε F(s))` on `[0, s_c]`; and for
every `T ≥ c₀ + m_* √c₀`, the sandwich
`η⁻¹ ∫_0^{H_F(Tε)} √F ≤ t_{Tε} ≤ η⁻¹ ∫_0^{s_c} √(F + m_* √(εF))`.

LaTeX (verbatim, `section.tex` l.445–470):
```
\begin{theorem}[Hitting times]\label{thm:app-phase-hitting}
Assume (M1) and $\mathcal S>0$, fix $\epsilon>0$, and take
$\lr=2\sqrt\epsilon/\mathcal S$, so that $\bar k=\sqrt\epsilon$.
\begin{enumerate}[label=(\roman*)]
\item For every $a>0$, $H_Q(a)\ge H_F(a)$ and
\[
t_a\ge\frac1\lr\int_0^{H_F(a)}\sqrt{F(s)}\,\dif s .
\]
If $H_Q(a)<\infty$, then $t_a=t(H_Q(a))$ with $t(\cdot)$ of
\cref{thm:app-phase-clock}.
\item Fix $c_0>1$ with $F_0>c_0\epsilon$, let $s_c$ be the time with
$F(s_c)=c_0\epsilon$, and put
\[
C_\ast\defeq\max_{0\le s\le s_c}\frac{(k*\sqrt F)(s)}{\sqrt{\epsilon F(s)}},\qquad
m_\ast\defeq\frac{C_\ast}{1-1/(2\sqrt{c_0})} .
\]
Then $0\le C_\ast\le\sqrt{F_0/(c_0\epsilon)}$ and
\begin{equation}\label{eqn:app-phase-upper}
Q(s)\le F(s)+m_\ast\sqrt{\epsilon F(s)}\qquad(0\le s\le s_c).
\end{equation}
Consequently, for every $T\ge c_0+m_\ast\sqrt{c_0}$,
\begin{equation}\label{eqn:app-phase-sandwich}
\frac1\lr\int_0^{H_F(T\epsilon)}\sqrt{F(s)}\,\dif s\ \le\ t_{T\epsilon}\ \le\ \frac1\lr\int_0^{s_c}\sqrt{F(s)+m_\ast\sqrt{\epsilon F(s)}}\,\dif s .
\end{equation}
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_phase_hitting_ii [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ)
    (hQ : IsVolterraSol m Q) (hS : 0 < m.S) (ε : ℝ) (hε : 0 < ε)
    (hη : m.η = 2 * Real.sqrt ε / m.S)
    (c₀ sc : ℝ) (hc₀ : 1 < c₀) (hF₀ : c₀ * ε < m.F0)
    (hsc : 0 ≤ sc) (hFsc : m.forcing sc = c₀ * ε) :
    0 ≤ cstar m ε sc ∧ cstar m ε sc ≤ Real.sqrt (m.F0 / (c₀ * ε)) ∧
    (∀ s ∈ Icc (0:ℝ) sc, Q s ≤ m.forcing s + mstar m c₀ ε sc * Real.sqrt (ε * m.forcing s)) ∧
    ∀ T : ℝ, c₀ + mstar m c₀ ε sc * Real.sqrt c₀ ≤ T →
      ENNReal.ofReal ((1 / m.η) *
          ∫ s in (0:ℝ)..(firstHit m.forcing (T * ε)).toReal, Real.sqrt (m.forcing s))
        ≤ firstHit (riskClock m Q) (T * ε) ∧
      firstHit (riskClock m Q) (T * ε) ≤
        ENNReal.ofReal ((1 / m.η) *
          ∫ s in (0:ℝ)..sc,
            Real.sqrt (m.forcing s + mstar m c₀ ε sc * Real.sqrt (ε * m.forcing s))) := by
  obtain ⟨hC0, hCle, -⟩ := aux_h_cstar m hS ε hε hη c₀ sc hc₀ hsc hFsc
  have hup := aux_h_upper m Q hQ hS ε hε hη c₀ sc hc₀ hF₀ hsc hFsc
  have hμ0 := aux_h_mstar_nonneg m ε sc c₀ hc₀ hC0
  obtain ⟨hFc, -, -, hFpos, -⟩ := lem_app_phase_kernel_i m
  refine ⟨hC0, hCle, hup, fun T hT => ⟨?_, ?_⟩⟩
  · have hsq0 : 0 ≤ mstar m c₀ ε sc * Real.sqrt c₀ := mul_nonneg hμ0 (Real.sqrt_nonneg _)
    exact (thm_app_phase_hitting_i m Q hQ hS ε hε hη (T * ε)
      (mul_pos (by linarith) hε)).2.1
  · set μs := mstar m c₀ ε sc with hμs
    have hFcI : ContinuousOn m.forcing (Icc 0 sc) := hFc.mono Icc_subset_Ici_self
    have hycont : ContinuousOn
        (fun s => Real.sqrt (m.forcing s + μs * Real.sqrt (ε * m.forcing s))) (Icc 0 sc) :=
      (hFcI.add (continuousOn_const.mul (continuousOn_const.mul hFcI).sqrt)).sqrt
    have hu0 : 0 ≤ clockTime m Q sc := by
      unfold clockTime
      exact mul_nonneg (one_div_nonneg.2 m.η_pos.le)
        (intervalIntegral.integral_nonneg hsc (fun u _ => Real.sqrt_nonneg _))
    have hQsc : Q sc ≤ T * ε := by
      have h1 := hup sc ⟨hsc, le_rfl⟩
      rw [hFsc] at h1
      have h2 : Real.sqrt (ε * (c₀ * ε)) = ε * Real.sqrt c₀ := by
        rw [show ε * (c₀ * ε) = ε ^ 2 * c₀ by ring, Real.sqrt_mul (sq_nonneg ε),
          Real.sqrt_sq hε.le]
      rw [h2] at h1
      nlinarith [mul_le_mul_of_nonneg_right hT hε.le]
    have hrisk : riskClock m Q (clockTime m Q sc) ≤ T * ε := by
      unfold riskClock
      rw [aux_clock_left m Q hQ hsc]
      exact hQsc
    refine (aux_firstHit_le (riskClock m Q) (T * ε) _ hu0 hrisk).trans
      (ENNReal.ofReal_le_ofReal ?_)
    unfold clockTime
    refine mul_le_mul_of_nonneg_left ?_ (one_div_nonneg.2 m.η_pos.le)
    refine intervalIntegral.integral_mono_on hsc (aux_sqrtQ_intInt m Q hQ le_rfl hsc)
      (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le hsc]
          exact hycont.integrableOn_Icc) (fun s hs => ?_)
    exact Real.sqrt_le_sqrt (hup s hs)

end Muon.Phase

end

import Mathlib
import Muon.Phase.Model
import Muon.Foundations.RealAnalysis

/-!
# Appendix H: kernel, tail, comparison and the Volterra equation (task L-H.2)

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`,
subsection "The Volterra equation of the risk" (l.181–315): `lem:app-phase-kernel` (l.203),
`lem:app-phase-tail` (l.246), `lem:app-phase-comparison` (l.272), `thm:app-phase-volterra`
(l.303), with the Volterra equation `eqn:app-phase-volterra` (l.197–201).
Card: `sections/07-phase-comparison/CARD.md` §2, §3, §5 (L-H.2).

Encoding decisions:
* The model `(M1)` is `Muon.Phase.RowModel ι`; `forcing`, `kernel`, `kbar`, `F0`, `S` are
  the project definitions of `Muon/Phase/Model.lean`, reused unchanged. Every statement
  assumes `[Countable ι]`, the paper's index set `{1,…,N}` or `ℕ`.
* The paper's one-sided convolution `(g*h)(u)=∫_0^u g(v)h(u-v)dv` is
  `Muon.Foundations.oneSidedConv h g` (its definition is `∫ s in 0..t, f (t-s) * g s`), so
  `k*f` is `oneSidedConv f m.kernel` and `k*√Q` is `oneSidedConv (fun u => √(Q u)) m.kernel`.
* `kernel` is meaningful only at `s > 0` (Lean's value at `0` is a `tsum` artifact); every
  statement about `k` restricts to `s > 0`, or to integrals over `Ioi 0` / `Ioo 0 S'`.
* Lean helper hypothesis (not a correction, card §3): `f` in `lem:app-phase-kernel` and
  `lem:app-phase-tail` is `Measurable`; the paper leaves measurability implicit.
* Solutions of the Volterra equation are predicates `IsVolterraSol` (on `[0,∞)`) and
  `IsVolterraSolOn` (on `[0,S']`), exposing local uniqueness (card §2, §5 L-H.2).
* `thm:app-phase-volterra` is split into parts `_i`–`_v`: existence with global uniqueness
  (`_i`), local uniqueness on `[0,S']` (`_ii`), bounds (`_iii`), the limit (`_iv`) and the
  floor/matched-step formula (`_v`). The bounds, limit and floor are stated for every solution
  `Q`; by `_i` this is the same as for the unique solution.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open Muon.Foundations

noncomputable section

namespace Muon.Phase

variable {ι : Type*}

/-- Global solution of the Volterra equation `eqn:app-phase-volterra`, `Q = F + k * √Q`
(`section.tex` l.197–201): a continuous, nonnegative function on `[0,∞)` satisfying the
equation at every `s ≥ 0`. The convolution is `oneSidedConv (√Q) k`, the paper's `k * √Q`. -/
def IsVolterraSol (m : RowModel ι) (Q : ℝ → ℝ) : Prop :=
  ContinuousOn Q (Ici 0) ∧ (∀ s ∈ Ici (0 : ℝ), 0 ≤ Q s) ∧
    ∀ s ∈ Ici (0 : ℝ), Q s = m.forcing s + oneSidedConv (fun u => Real.sqrt (Q u)) m.kernel s

/-- Local solution of the Volterra equation on `[0,S']`: the same conditions as
`IsVolterraSol`, with `[0,∞)` replaced by `[0,S']` (used by `thm:app-phase-volterra` local
uniqueness and by `thm:app-phase-clock`, l.427–429). -/
def IsVolterraSolOn (m : RowModel ι) (S' : ℝ) (Q : ℝ → ℝ) : Prop :=
  ContinuousOn Q (Icc 0 S') ∧ (∀ s ∈ Icc (0 : ℝ) S', 0 ≤ Q s) ∧
    ∀ s ∈ Icc (0 : ℝ) S', Q s = m.forcing s + oneSidedConv (fun u => Real.sqrt (Q u)) m.kernel s

/-- Private proof of `b e^{-bs} ≤ 1/(e s)` for `b, s > 0` (the `Muon.Foundations` copy is
still unproved). -/
lemma aux_mul_exp_neg_le {b s : ℝ} (hb : 0 < b) (hs : 0 < s) :
    b * Real.exp (-(b * s)) ≤ 1 / (Real.exp 1 * s) := by
  have hx : 0 < b * s := mul_pos hb hs
  have h1 : b * s ≤ Real.exp (b * s - 1) := by
    linarith [Real.add_one_le_exp (b * s - 1)]
  have h2 : Real.exp (b * s - 1) * Real.exp (-(b * s)) = 1 / Real.exp 1 := by
    rw [← Real.exp_add, show b * s - 1 + -(b * s) = -1 by ring, Real.exp_neg, one_div]
  have h3 : b * s * Real.exp (-(b * s)) ≤ 1 / Real.exp 1 := by
    calc b * s * Real.exp (-(b * s)) ≤ Real.exp (b * s - 1) * Real.exp (-(b * s)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 1 / Real.exp 1 := h2
  have h4 : b * Real.exp (-(b * s)) = (b * s * Real.exp (-(b * s))) / s := by
    field_simp
  calc b * Real.exp (-(b * s)) = (b * s * Real.exp (-(b * s))) / s := h4
    _ ≤ (1 / Real.exp 1) / s := by gcongr
    _ = 1 / (Real.exp 1 * s) := by rw [div_div]

/-- `lem:app-phase-kernel`, part (i) of 4, snapshot `cr-2026-10-23`.
Forcing `F` (`forcing`): continuity, strict decrease, `F(0) = F_0`, positivity, decay to `0`.
Source: `section.tex` l.203–215.

LaTeX (verbatim, `section.tex` l.203–215):
```
\begin{lemma}[Forcing and kernel]\label{lem:app-phase-kernel}
Assume (M1). The forcing $F$ is continuous and strictly decreasing on
$[0,\infty)$, with $F(0)=F_0$, $F>0$ and $F(s)\to0$ as $s\to\infty$. The kernel
satisfies
\[
\int_0^\infty k(s)\,\dif s=\bar k,\qquad k(s)\le\frac{\bar k}{e\,s}\quad(s>0).
\]
For every $S'>0$ and every bounded function $f$ on $[0,S']$, the
convolution $k*f$ is continuous on $[0,S']$, vanishes at $0$, and
\begin{equation}\label{eqn:app-phase-convbound}
\sup_{0\le s\le S'}\abs{(k*f)(s)}\le\bar k\,\sup_{0\le s\le S'}\abs{f(s)} .
\end{equation}
\end{lemma}
``` -/

theorem lem_app_phase_kernel_i
    [Countable ι] (m : RowModel ι) :
    ContinuousOn m.forcing (Ici 0) ∧ StrictAntiOn m.forcing (Ici 0) ∧
      m.forcing 0 = m.F0 ∧ (∀ s ∈ Ici (0 : ℝ), 0 < m.forcing s) ∧
      Tendsto m.forcing atTop (𝓝 0) := by
  have hbound : ∀ s : ℝ, 0 ≤ s → ∀ i,
      ‖m.μ i * m.Q0 i * Real.exp (-(2 * m.d i * s))‖ ≤ m.μ i * m.Q0 i := by
    intro s hs i
    have hc : 0 ≤ m.μ i * m.Q0 i := mul_nonneg (m.μ_pos i).le (m.Q0_nonneg i)
    rw [Real.norm_of_nonneg (mul_nonneg hc (Real.exp_pos _).le)]
    have hexp : Real.exp (-(2 * m.d i * s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ 2 * m.d i * s := mul_nonneg (by linarith [m.d_pos i]) hs
      linarith
    calc m.μ i * m.Q0 i * Real.exp (-(2 * m.d i * s)) ≤ m.μ i * m.Q0 i * 1 :=
          mul_le_mul_of_nonneg_left hexp hc
      _ = m.μ i * m.Q0 i := mul_one _
  obtain ⟨i0, hi0⟩ : ∃ i, 0 < m.μ i * m.Q0 i := by
    by_contra h
    push_neg at h
    have hz : ∑' i, m.μ i * m.Q0 i = 0 := by
      have : (fun i => m.μ i * m.Q0 i) = fun _ => (0 : ℝ) := by
        funext i
        exact le_antisymm (h i) (mul_nonneg (m.μ_pos i).le (m.Q0_nonneg i))
      rw [this, tsum_zero]
    have := m.F0_pos
    rw [hz, mul_zero] at this
    exact lt_irrefl _ this
  have hsum : ∀ s : ℝ, 0 ≤ s →
      Summable (fun i => m.μ i * m.Q0 i * Real.exp (-(2 * m.d i * s))) :=
    fun s hs => Summable.of_norm_bounded m.summable_μQ0 (hbound s hs)
  have hcont : ContinuousOn m.forcing (Ici 0) := by
    unfold RowModel.forcing
    refine continuousOn_const.mul (continuousOn_tsum (fun i => ?_) m.summable_μQ0
      (fun n x hx => hbound x hx n))
    exact (by fun_prop : Continuous fun s : ℝ =>
      m.μ i * m.Q0 i * Real.exp (-(2 * m.d i * s))).continuousOn
  have hstrict : StrictAntiOn m.forcing (Ici 0) := by
    intro a ha b hb hab
    have ha' : 0 ≤ a := ha
    have hb' : 0 ≤ b := hb
    unfold RowModel.forcing
    refine mul_lt_mul_of_pos_left ?_ (by norm_num)
    refine Summable.tsum_lt_tsum (i := i0) (fun i => ?_) ?_ (hsum b hb') (hsum a ha')
    · exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [m.d_pos i]))
        (mul_nonneg (m.μ_pos i).le (m.Q0_nonneg i))
    · exact mul_lt_mul_of_pos_left
        (Real.exp_lt_exp.mpr (by nlinarith [m.d_pos i0])) hi0
  have hpos : ∀ s ∈ Ici (0 : ℝ), 0 < m.forcing s := by
    intro s hs
    unfold RowModel.forcing
    refine mul_pos (by norm_num) (Summable.tsum_pos (hsum s hs) (fun i => ?_) i0 ?_)
    · exact mul_nonneg (mul_nonneg (m.μ_pos i).le (m.Q0_nonneg i)) (Real.exp_pos _).le
    · exact mul_pos hi0 (Real.exp_pos _)
  have hzero : m.forcing 0 = m.F0 := by
    unfold RowModel.forcing RowModel.F0
    simp
  have htend : Tendsto m.forcing atTop (𝓝 0) := by
    have hexp : ∀ k, Tendsto (fun s : ℝ => m.μ k * m.Q0 k * Real.exp (-(2 * m.d k * s)))
        atTop (𝓝 0) := by
      intro k
      have h1 : Tendsto (fun s : ℝ => 2 * m.d k * s) atTop atTop :=
        Tendsto.const_mul_atTop (by linarith [m.d_pos k]) tendsto_id
      have h2 : Tendsto (fun s : ℝ => Real.exp (-(2 * m.d k * s))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
      have h3 := h2.const_mul (m.μ k * m.Q0 k)
      rwa [mul_zero] at h3
    have hT := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun s i => m.μ i * m.Q0 i * Real.exp (-(2 * m.d i * s)))
      (g := fun _ => (0 : ℝ)) (bound := fun i => m.μ i * m.Q0 i) m.summable_μQ0 hexp
      (Filter.eventually_atTop.2 ⟨0, fun s hs i => hbound s hs i⟩)
    have hT2 := hT.const_mul (1 / 2 : ℝ)
    simp only [tsum_zero, mul_zero] at hT2
    unfold RowModel.forcing
    exact hT2
  exact ⟨hcont, hstrict, hzero, hpos, htend⟩

/-- `lem:app-phase-kernel`, part (ii) of 4, snapshot `cr-2026-10-23`.
Kernel: integrability on `(0,∞)`, `∫_0^∞ k = k̄` (`kernel` is used
on `s > 0` only), and `k(s) ≤ k̄/(e s)`.
Source: `section.tex` l.203–215.

LaTeX (verbatim, `section.tex` l.203–215):
```
\begin{lemma}[Forcing and kernel]\label{lem:app-phase-kernel}
Assume (M1). The forcing $F$ is continuous and strictly decreasing on
$[0,\infty)$, with $F(0)=F_0$, $F>0$ and $F(s)\to0$ as $s\to\infty$. The kernel
satisfies
\[
\int_0^\infty k(s)\,\dif s=\bar k,\qquad k(s)\le\frac{\bar k}{e\,s}\quad(s>0).
\]
For every $S'>0$ and every bounded function $f$ on $[0,S']$, the
convolution $k*f$ is continuous on $[0,S']$, vanishes at $0$, and
\begin{equation}\label{eqn:app-phase-convbound}
\sup_{0\le s\le S'}\abs{(k*f)(s)}\le\bar k\,\sup_{0\le s\le S'}\abs{f(s)} .
\end{equation}
\end{lemma}
``` -/

theorem lem_app_phase_kernel_ii
    [Countable ι] (m : RowModel ι) :
    IntegrableOn m.kernel (Ioi 0) ∧ ∫ s in Ioi (0 : ℝ), m.kernel s = m.kbar ∧
      ∀ s : ℝ, 0 < s → m.kernel s ≤ m.kbar / (Real.exp 1 * s) := by
  have hnn : ∀ i s, 0 ≤ m.μ i * m.v i * Real.exp (-(2 * m.d i * s)) := fun i s =>
    mul_nonneg (mul_nonneg (m.μ_pos i).le (m.v_nonneg i)) (Real.exp_pos _).le
  have hcont : ∀ i, Continuous (fun s : ℝ => m.μ i * m.v i * Real.exp (-(2 * m.d i * s))) :=
    fun i => by fun_prop
  have hI : ∀ i, ∫ s in Ioi (0 : ℝ), m.μ i * m.v i * Real.exp (-(2 * m.d i * s))
      = m.μ i * m.v i / (2 * m.d i) := by
    intro i
    have hd := m.d_pos i
    have hneg : -(2 * m.d i) < 0 := by linarith
    have h := integral_exp_mul_Ioi hneg 0
    have e1 : (fun s : ℝ => Real.exp (-(2 * m.d i) * s))
        = fun s => Real.exp (-(2 * m.d i * s)) := by
      funext s
      congr 1
      ring
    rw [e1] at h
    rw [integral_const_mul, h]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  have hIi : ∀ i, IntegrableOn (fun s : ℝ => m.μ i * m.v i * Real.exp (-(2 * m.d i * s)))
      (Ioi 0) := by
    intro i
    have hd := m.d_pos i
    have h : IntegrableOn (fun s : ℝ => m.μ i * m.v i * Real.exp (-(2 * m.d i) * s)) (Ioi 0) :=
      Integrable.const_mul (integrableOn_exp_mul_Ioi (a := -(2 * m.d i)) (by linarith) 0)
        (m.μ i * m.v i)
    exact IntegrableOn.congr_fun h (fun s _ => by simp only [neg_mul]) measurableSet_Ioi
  have hnorm : ∀ i, ∫ s in Ioi (0 : ℝ), ‖m.μ i * m.v i * Real.exp (-(2 * m.d i * s))‖
      = m.μ i * m.v i / (2 * m.d i) := by
    intro i
    rw [← hI i]
    exact setIntegral_congr_fun measurableSet_Ioi (fun s _ => Real.norm_of_nonneg (hnn i s))
  have hsumI : Summable (fun i => ∫ s in Ioi (0 : ℝ),
      ‖m.μ i * m.v i * Real.exp (-(2 * m.d i * s))‖) :=
    m.summable_S.congr (fun i => (hnorm i).symm)
  have hKint : IntegrableOn (fun s : ℝ => ∑' i, m.μ i * m.v i * Real.exp (-(2 * m.d i * s)))
      (Ioi 0) := by
    refine ⟨(Measurable.tsum (fun i => (hcont i).measurable)).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono (fun s => enorm_tsum_le_tsum_enorm)) ?_
    rw [lintegral_tsum (fun i => (hcont i).measurable.enorm.aemeasurable)]
    have hval : ∀ i, ∫⁻ s in Ioi (0 : ℝ), ‖m.μ i * m.v i * Real.exp (-(2 * m.d i * s))‖ₑ
        = ENNReal.ofReal (m.μ i * m.v i / (2 * m.d i)) := by
      intro i
      rw [← ofReal_integral_norm_eq_lintegral_enorm (hIi i), hnorm i]
    simp only [hval]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun i => div_nonneg (mul_nonneg (m.μ_pos i).le (m.v_nonneg i))
        (by linarith [m.d_pos i])) m.summable_S]
    exact ENNReal.ofReal_lt_top
  have hIntK : ∫ s in Ioi (0 : ℝ), ∑' i, m.μ i * m.v i * Real.exp (-(2 * m.d i * s)) = m.S := by
    rw [← integral_tsum_of_summable_integral_norm hIi hsumI, tsum_congr hI]
    rfl
  have hkint : ∫ s in Ioi (0 : ℝ), m.kernel s = m.kbar := by
    simp only [RowModel.kernel, RowModel.kbar]
    rw [integral_const_mul, hIntK]
    ring
  refine ⟨?_, hkint, ?_⟩
  · exact hKint.const_mul (m.η / 2)
  · intro s hs
    have hterm : ∀ i, m.μ i * m.v i * Real.exp (-(2 * m.d i * s))
        ≤ m.μ i * m.v i / (2 * m.d i) * (1 / (Real.exp 1 * s)) := by
      intro i
      have hd := m.d_pos i
      have key := aux_mul_exp_neg_le (b := 2 * m.d i) (s := s) (by linarith) hs
      have e : m.μ i * m.v i * Real.exp (-(2 * m.d i * s))
          = m.μ i * m.v i / (2 * m.d i) * (2 * m.d i * Real.exp (-(2 * m.d i * s))) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left key
        (div_nonneg (mul_nonneg (m.μ_pos i).le (m.v_nonneg i)) (by linarith))
    have hgs : Summable (fun i => m.μ i * m.v i / (2 * m.d i) * (1 / (Real.exp 1 * s))) :=
      m.summable_S.mul_right _
    have hfs : Summable (fun i => m.μ i * m.v i * Real.exp (-(2 * m.d i * s))) :=
      Summable.of_norm_bounded hgs (fun i => by
        rw [Real.norm_of_nonneg (hnn i s)]
        exact hterm i)
    have hle := Summable.tsum_le_tsum hterm hfs hgs
    rw [tsum_mul_right] at hle
    have hle2 : m.η / 2 * ∑' i, m.μ i * m.v i * Real.exp (-(2 * m.d i * s))
        ≤ m.η / 2 * (m.S * (1 / (Real.exp 1 * s))) :=
      mul_le_mul_of_nonneg_left hle (by linarith [m.η_pos])
    unfold RowModel.kernel RowModel.kbar
    calc m.η / 2 * ∑' i, m.μ i * m.v i * Real.exp (-(2 * m.d i * s))
        ≤ m.η / 2 * (m.S * (1 / (Real.exp 1 * s))) := hle2
      _ = m.η * m.S / 2 / (Real.exp 1 * s) := by ring

/-- Closed form of a one-sided convolution with one exponential term (substitution `s ↦ t - s`). -/
lemma aux_osc_exp (f : ℝ → ℝ) (c b t : ℝ) :
    ∫ s in (0:ℝ)..t, f (t - s) * (c * Real.exp (-(b * s)))
      = c * Real.exp (-(b * t)) * ∫ u in (0:ℝ)..t, f u * Real.exp (b * u) := by
  have h := intervalIntegral.integral_comp_sub_left
    (f := fun u => f u * (c * Real.exp (-(b * (t - u))))) (a := (0:ℝ)) (b := t) t
  simp only [sub_self, sub_zero, sub_sub_cancel] at h
  rw [h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  rw [show -(b * (t - u)) = -(b * t) + b * u by ring, Real.exp_add]
  ring

/-- `∫_0^t e^{-bs} ds ≤ 1/b` for `b > 0`, `t ≥ 0`. -/
lemma aux_exp_integral_le {b t : ℝ} (hb : 0 < b) (_ht : 0 ≤ t) :
    ∫ s in (0:ℝ)..t, Real.exp (-(b * s)) ≤ 1 / b := by
  have hF : ∀ x ∈ uIcc (0:ℝ) t,
      HasDerivAt (fun s => -Real.exp (-(b * s)) / b) (Real.exp (-(b * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => -(b * s)) (-b) x := by
      have h := ((hasDerivAt_id' x).const_mul b).neg
      rw [mul_one] at h
      exact h
    have h2 := ((h1.exp).neg).div_const b
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun s : ℝ => Real.exp (-(b * s))).intervalIntegrable 0 t)]
  have h3 : 0 ≤ Real.exp (-(b * t)) := (Real.exp_pos _).le
  have h4 : -Real.exp (-(b * t)) / b ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hb.le
  simp only [mul_zero, neg_zero, Real.exp_zero]
  calc _ = 1 / b - Real.exp (-(b * t)) / b := by ring
    _ ≤ 1 / b := sub_le_self _ (div_nonneg h3 hb.le)

/-- Integrability of `s ↦ f(t-s) g(s)` on `(0,t]` for measurable `f` bounded on `[0,S']`. -/
lemma aux_osc_integrable {f : ℝ → ℝ} {S' C : ℝ} (hf : Measurable f)
    (hC : ∀ s ∈ Icc (0:ℝ) S', |f s| ≤ C) {t : ℝ} (_ht0 : 0 ≤ t) (htS : t ≤ S')
    (g : ℝ → ℝ) (hg : Continuous g) :
    IntegrableOn (fun s => f (t - s) * g s) (Ioc 0 t) := by
  have hgI : IntegrableOn g (Ioc 0 t) := (hg.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  refine Integrable.bdd_mul (f := fun s => f (t - s)) (c := C) hgI
    (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall (fun s hs => ?_)
  rw [Real.norm_eq_abs]
  exact hC _ ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-- Pointwise-in-`t` bound `∫_0^t |f(t-s)| c e^{-bs} ds ≤ C c / b`. -/
lemma aux_osc_term_le {f : ℝ → ℝ} {S' C : ℝ} (hf : Measurable f)
    (hC : ∀ s ∈ Icc (0:ℝ) S', |f s| ≤ C) {t : ℝ} (ht0 : 0 ≤ t) (htS : t ≤ S')
    {c b : ℝ} (hc : 0 ≤ c) (hb : 0 < b) :
    ∫ s in (0:ℝ)..t, ‖f (t - s) * (c * Real.exp (-(b * s)))‖ ≤ C * (c / b) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC t ⟨ht0, htS⟩)
  have hint1 : IntervalIntegrable (fun s => f (t - s) * (c * Real.exp (-(b * s)))) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht0).2
      (aux_osc_integrable hf hC ht0 htS _ (by fun_prop))
  have hint2 : IntervalIntegrable (fun s => C * c * Real.exp (-(b * s))) volume 0 t :=
    (by fun_prop : Continuous fun s : ℝ => C * c * Real.exp (-(b * s))).intervalIntegrable 0 t
  calc ∫ s in (0:ℝ)..t, ‖f (t - s) * (c * Real.exp (-(b * s)))‖
      ≤ ∫ s in (0:ℝ)..t, C * c * Real.exp (-(b * s)) := by
        refine intervalIntegral.integral_mono_on ht0 hint1.norm hint2 (fun s hs => ?_)
        have hpos : 0 ≤ c * Real.exp (-(b * s)) := mul_nonneg hc (Real.exp_pos _).le
        have hfs := hC (t - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
        rw [norm_mul, Real.norm_of_nonneg hpos, Real.norm_eq_abs]
        calc |f (t - s)| * (c * Real.exp (-(b * s)))
            ≤ C * (c * Real.exp (-(b * s))) := mul_le_mul_of_nonneg_right hfs hpos
          _ = C * c * Real.exp (-(b * s)) := by ring
    _ = C * c * ∫ s in (0:ℝ)..t, Real.exp (-(b * s)) := intervalIntegral.integral_const_mul _ _
    _ ≤ C * c * (1 / b) :=
        mul_le_mul_of_nonneg_left (aux_exp_integral_le hb ht0) (mul_nonneg hC0 hc)
    _ = C * (c / b) := by ring

/-- `lem:app-phase-kernel`, part (iii) of 4, snapshot `cr-2026-10-23`.
Convolution `k * f` on `[0,S']` for bounded measurable `f`: continuity
on `[0,S']` and vanishing at `0`.
Source: `section.tex` l.203–215.

LaTeX (verbatim, `section.tex` l.203–215):
```
\begin{lemma}[Forcing and kernel]\label{lem:app-phase-kernel}
Assume (M1). The forcing $F$ is continuous and strictly decreasing on
$[0,\infty)$, with $F(0)=F_0$, $F>0$ and $F(s)\to0$ as $s\to\infty$. The kernel
satisfies
\[
\int_0^\infty k(s)\,\dif s=\bar k,\qquad k(s)\le\frac{\bar k}{e\,s}\quad(s>0).
\]
For every $S'>0$ and every bounded function $f$ on $[0,S']$, the
convolution $k*f$ is continuous on $[0,S']$, vanishes at $0$, and
\begin{equation}\label{eqn:app-phase-convbound}
\sup_{0\le s\le S'}\abs{(k*f)(s)}\le\bar k\,\sup_{0\le s\le S'}\abs{f(s)} .
\end{equation}
\end{lemma}
``` -/

theorem lem_app_phase_kernel_iii
    [Countable ι] (m : RowModel ι) (S' : ℝ) (hS' : 0 < S') (f : ℝ → ℝ) (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) S', |f s| ≤ C) :
    ContinuousOn (oneSidedConv f m.kernel) (Icc 0 S') ∧ oneSidedConv f m.kernel 0 = 0 := by
  obtain ⟨C, hC⟩ := hb
  have hη2 : 0 ≤ m.η / 2 := by linarith [m.η_pos]
  have hc_nonneg : ∀ i, 0 ≤ m.η / 2 * (m.μ i * m.v i) := fun i =>
    mul_nonneg hη2 (mul_nonneg (m.μ_pos i).le (m.v_nonneg i))
  have hb_pos : ∀ i, 0 < 2 * m.d i := fun i => by linarith [m.d_pos i]
  -- summable majorant `C · c_i / b_i`
  have hsumw : Summable (fun i => C * (m.η / 2 * (m.μ i * m.v i) / (2 * m.d i))) :=
    (m.summable_S.mul_left (C * (m.η / 2))).congr (fun i => by ring)
  -- one-sided convolution as a series of per-term integrals on `[0,t]`
  have hrep : ∀ t ∈ Icc (0:ℝ) S', oneSidedConv f m.kernel t =
      ∑' i, ∫ s in (0:ℝ)..t,
        f (t - s) * (m.η / 2 * (m.μ i * m.v i) * Real.exp (-(2 * m.d i * s))) := by
    intro t ht
    have ht0 := ht.1
    have htS := ht.2
    have hfun : (fun s => f (t - s) * (m.η / 2 * ∑' i, m.μ i * m.v i * Real.exp (-(2 * m.d i * s))))
        = fun s => ∑' i, f (t - s) * (m.η / 2 * (m.μ i * m.v i) * Real.exp (-(2 * m.d i * s))) := by
      funext s
      rw [← tsum_mul_left, ← tsum_mul_left]
      exact tsum_congr (fun i => by ring)
    have hInt : ∀ i, Integrable (fun s => f (t - s) *
        (m.η / 2 * (m.μ i * m.v i) * Real.exp (-(2 * m.d i * s))))
        (volume.restrict (Ioc 0 t)) := fun i =>
      aux_osc_integrable hf hC ht0 htS _ (by fun_prop)
    have hSum : Summable (fun i => ∫ s, ‖f (t - s) *
        (m.η / 2 * (m.μ i * m.v i) * Real.exp (-(2 * m.d i * s)))‖ ∂(volume.restrict (Ioc 0 t))) := by
      refine Summable.of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _))
        (fun i => ?_) hsumw
      rw [← intervalIntegral.integral_of_le ht0]
      exact aux_osc_term_le hf hC ht0 htS (hc_nonneg i) (hb_pos i)
    unfold oneSidedConv RowModel.kernel
    rw [hfun, intervalIntegral.integral_of_le ht0,
      ← integral_tsum_of_summable_integral_norm hInt hSum]
    exact tsum_congr (fun i => by rw [intervalIntegral.integral_of_le ht0])
  -- each term is continuous on `[0,S']`
  have hH_cont : ∀ i, ContinuousOn (fun t => ∫ s in (0:ℝ)..t,
      f (t - s) * (m.η / 2 * (m.μ i * m.v i) * Real.exp (-(2 * m.d i * s)))) (Icc 0 S') := by
    intro i
    have hint : IntegrableOn (fun u => f u * Real.exp (2 * m.d i * u)) (uIcc 0 S') := by
      rw [Set.uIcc_of_le hS'.le]
      refine Integrable.bdd_mul (f := f) (c := C) ((by fun_prop :
          Continuous fun u : ℝ => Real.exp (2 * m.d i * u)).integrableOn_Icc) hf.aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall (fun u hu => by
        rw [Real.norm_eq_abs]; exact hC u hu)
    have hP := intervalIntegral.continuousOn_primitive_interval hint
    rw [Set.uIcc_of_le hS'.le] at hP
    have hcont : ContinuousOn (fun t => m.η / 2 * (m.μ i * m.v i) * Real.exp (-(2 * m.d i * t))
        * ∫ u in (0:ℝ)..t, f u * Real.exp (2 * m.d i * u)) (Icc 0 S') :=
      ((by fun_prop : Continuous fun t : ℝ =>
        m.η / 2 * (m.μ i * m.v i) * Real.exp (-(2 * m.d i * t))).continuousOn).mul hP
    refine hcont.congr (fun t _ => ?_)
    exact aux_osc_exp f _ _ t
  refine ⟨?_, ?_⟩
  · have hsum_cont : ContinuousOn (fun t => ∑' i, ∫ s in (0:ℝ)..t,
        f (t - s) * (m.η / 2 * (m.μ i * m.v i) * Real.exp (-(2 * m.d i * s)))) (Icc 0 S') := by
      refine continuousOn_tsum hH_cont hsumw (fun i t ht => ?_)
      refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
      exact aux_osc_term_le hf hC ht.1 ht.2 (hc_nonneg i) (hb_pos i)
    exact hsum_cont.congr (fun t ht => hrep t ht)
  · unfold oneSidedConv
    exact intervalIntegral.integral_same

/-- `lem:app-phase-kernel`, part (iv) of 4, snapshot `cr-2026-10-23`.
Convolution bound `sup_{0≤s≤S'} |k*f| ≤ k̄ sup_{0≤v≤S'} |f|` for bounded measurable `f`.
Source: `section.tex` l.203–215.

LaTeX (verbatim, `section.tex` l.203–215):
```
\begin{lemma}[Forcing and kernel]\label{lem:app-phase-kernel}
Assume (M1). The forcing $F$ is continuous and strictly decreasing on
$[0,\infty)$, with $F(0)=F_0$, $F>0$ and $F(s)\to0$ as $s\to\infty$. The kernel
satisfies
\[
\int_0^\infty k(s)\,\dif s=\bar k,\qquad k(s)\le\frac{\bar k}{e\,s}\quad(s>0).
\]
For every $S'>0$ and every bounded function $f$ on $[0,S']$, the
convolution $k*f$ is continuous on $[0,S']$, vanishes at $0$, and
\begin{equation}\label{eqn:app-phase-convbound}
\sup_{0\le s\le S'}\abs{(k*f)(s)}\le\bar k\,\sup_{0\le s\le S'}\abs{f(s)} .
\end{equation}
\end{lemma}
``` -/

theorem lem_app_phase_kernel_iv
    [Countable ι] (m : RowModel ι) (S' : ℝ) (hS' : 0 < S') (f : ℝ → ℝ) (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) S', |f s| ≤ C) :
    ∀ s ∈ Icc (0 : ℝ) S', |oneSidedConv f m.kernel s| ≤ m.kbar * ⨆ v ∈ Icc (0 : ℝ) S', |f v| := by
  obtain ⟨C, hC⟩ := hb
  have hKint : IntegrableOn m.kernel (Ioi 0) := (lem_app_phase_kernel_ii m).1
  have hKtot : ∫ s in Ioi (0 : ℝ), m.kernel s = m.kbar := (lem_app_phase_kernel_ii m).2.1
  have hKnn : ∀ s, 0 ≤ m.kernel s := fun s => by
    unfold RowModel.kernel
    exact mul_nonneg (by linarith [m.η_pos])
      (tsum_nonneg fun i => mul_nonneg (mul_nonneg (m.μ_pos i).le (m.v_nonneg i)) (Real.exp_pos _).le)
  have hC0 : ∀ v ∈ Icc (0:ℝ) S', |f v| ≤ C := hC
  -- the supremum `M`
  have hbdd : ∀ v : ℝ, (⨆ (_ : v ∈ Icc (0:ℝ) S'), |f v|) ≤ C := by
    intro v
    exact Real.iSup_le (fun hv => hC0 v hv) (le_trans (abs_nonneg _) (hC0 0 ⟨le_refl 0, hS'.le⟩))
  have hMbdd : BddAbove (Set.range fun v : ℝ => ⨆ (_ : v ∈ Icc (0:ℝ) S'), |f v|) :=
    ⟨C, by rintro _ ⟨v, rfl⟩; exact hbdd v⟩
  have hfM : ∀ v ∈ Icc (0:ℝ) S', |f v| ≤ ⨆ w ∈ Icc (0:ℝ) S', |f w| := fun v hv =>
    calc |f v| = ⨆ (_ : v ∈ Icc (0:ℝ) S'), |f v| :=
          (ciSup_pos (f := fun _ : v ∈ Icc (0:ℝ) S' => |f v|) hv).symm
      _ ≤ ⨆ w ∈ Icc (0:ℝ) S', |f w| := le_ciSup hMbdd v
  have hM0 : 0 ≤ ⨆ w ∈ Icc (0:ℝ) S', |f w| :=
    le_trans (abs_nonneg _) (hfM 0 ⟨le_refl 0, hS'.le⟩)
  intro s hs
  have hs0 : 0 ≤ s := hs.1
  have hsS : s ≤ S' := hs.2
  have hKintI : IntervalIntegrable m.kernel volume 0 s :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hs0).2 (hKint.mono_set Ioc_subset_Ioi_self)
  have hint : IntervalIntegrable (fun x => f (s - x) * m.kernel x) volume 0 s := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs0]
    refine Integrable.bdd_mul (f := fun x => f (s - x)) (c := C)
      (hKint.mono_set Ioc_subset_Ioi_self)
      (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Real.norm_eq_abs]
    exact hC _ ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hKle : ∫ x in (0:ℝ)..s, m.kernel x ≤ m.kbar := by
    rw [intervalIntegral.integral_of_le hs0, ← hKtot]
    exact setIntegral_mono_set hKint (Filter.Eventually.of_forall hKnn)
      (Filter.Eventually.of_forall (fun x hx => Ioc_subset_Ioi_self hx))
  calc |oneSidedConv f m.kernel s|
      = |∫ x in (0:ℝ)..s, f (s - x) * m.kernel x| := rfl
    _ ≤ ∫ x in (0:ℝ)..s, |f (s - x) * m.kernel x| := intervalIntegral.abs_integral_le_integral_abs hs0
    _ ≤ ∫ x in (0:ℝ)..s, (⨆ w ∈ Icc (0:ℝ) S', |f w|) * m.kernel x := by
        refine intervalIntegral.integral_mono_on hs0 hint.abs (hKintI.const_mul _) (fun x hx => ?_)
        rw [abs_mul, abs_of_nonneg (hKnn x)]
        exact mul_le_mul_of_nonneg_right
          (hfM _ ⟨by linarith [hx.2], by linarith [hx.1]⟩) (hKnn x)
    _ = (⨆ w ∈ Icc (0:ℝ) S', |f w|) * ∫ x in (0:ℝ)..s, m.kernel x :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (⨆ w ∈ Icc (0:ℝ) S', |f w|) * m.kbar := mul_le_mul_of_nonneg_left hKle hM0
    _ = m.kbar * ⨆ w ∈ Icc (0:ℝ) S', |f w| := mul_comm _ _

/-- Private: `liminf (u + v) = liminf u` and `limsup (u + v) = limsup u` when `v → 0` and
`u` is bounded. -/
lemma aux_liminf_limsup_add_zero (u v : ℝ → ℝ) (hv : Tendsto v atTop (𝓝 0))
    (hu_up : IsBoundedUnder (· ≤ ·) atTop u) (hu_lo : IsBoundedUnder (· ≥ ·) atTop u) :
    Filter.liminf (u + v) atTop = Filter.liminf u atTop ∧
      Filter.limsup (u + v) atTop = Filter.limsup u atTop := by
  have hv_up : IsBoundedUnder (· ≤ ·) atTop v := hv.isBoundedUnder_le
  have hv_lo : IsBoundedUnder (· ≥ ·) atTop v := hv.isBoundedUnder_ge
  have hv_co_up : IsCoboundedUnder (· ≤ ·) atTop v := hv.isCoboundedUnder_le
  have hv_co_lo : IsCoboundedUnder (· ≥ ·) atTop v := hv.isCoboundedUnder_ge
  have hu_co_up : IsCoboundedUnder (· ≤ ·) atTop u := hu_lo.isCoboundedUnder_le
  have hu_co_lo : IsCoboundedUnder (· ≥ ·) atTop u := hu_up.isCoboundedUnder_ge
  have hl1 := le_liminf_add (f := atTop) (u := v) (v := u) hv_lo hv_up hu_lo hu_co_lo
  have hl2 := liminf_add_le (f := atTop) (u := v) (v := u) hv_lo hv_up hu_lo hu_co_lo
  have hL1 := limsup_add_le (f := atTop) (u := u) (v := v) hu_lo hu_up hv_co_up hv_up
  have hL2 := le_limsup_add (f := atTop) (u := u) (v := v) hu_up hu_co_up hv_up hv_lo
  rw [add_comm v u] at hl1 hl2
  simp only [hv.liminf_eq, hv.limsup_eq] at hl1 hl2 hL1 hL2
  constructor
  · linarith
  · linarith

/-- Private: the kernel is nonnegative (same argument as in `lem_app_phase_kernel_iv`). -/
lemma aux_kernel_nonneg_tail (m : RowModel ι) (s : ℝ) : 0 ≤ m.kernel s := by
  unfold RowModel.kernel
  exact mul_nonneg (by linarith [m.η_pos])
    (tsum_nonneg fun i => mul_nonneg (mul_nonneg (m.μ_pos i).le (m.v_nonneg i)) (Real.exp_pos _).le)

/-- Private: `k̄ ≥ 0`. -/
lemma aux_kbar_nonneg_tail [Countable ι] (m : RowModel ι) : 0 ≤ m.kbar := by
  rw [← (lem_app_phase_kernel_ii m).2.1]
  exact setIntegral_nonneg measurableSet_Ioi (fun s _ => aux_kernel_nonneg_tail m s)

/-- Private: the one-sided convolution of a bounded `f` is bounded by `k̄ C` on `[0,∞)`. -/
lemma aux_conv_abs_le [Countable ι] (m : RowModel ι) (f : ℝ → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ s ∈ Ici (0 : ℝ), |f s| ≤ C) (t : ℝ) (ht : 0 ≤ t) :
    |oneSidedConv f m.kernel t| ≤ m.kbar * C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 (Set.mem_Ici.2 le_rfl))
  have h := lem_app_phase_kernel_iv m (t + 1) (by linarith) f hf
    ⟨C, fun s hs => hC s (Set.mem_Ici.2 hs.1)⟩ t ⟨ht, by linarith⟩
  have hsup : (⨆ v ∈ Icc (0 : ℝ) (t + 1), |f v|) ≤ C :=
    Real.iSup_le (fun v => Real.iSup_le (fun hv => hC v (Set.mem_Ici.2 hv.1)) hC0) hC0
  exact h.trans (mul_le_mul_of_nonneg_left hsup (aux_kbar_nonneg_tail m))

/-- Private: `liminf (-g) = -limsup g` for a real function bounded at `atTop`. -/
lemma aux_liminf_neg (g : ℝ → ℝ) (hup : IsBoundedUnder (· ≤ ·) atTop g)
    (hlo : IsBoundedUnder (· ≥ ·) atTop g) :
    Filter.liminf (fun t => -g t) atTop = -Filter.limsup g atTop := by
  have := Antitone.map_limsup_of_continuousAt (F := atTop) (f := fun x : ℝ => -x)
    (fun a b h => neg_le_neg h) g continuous_neg.continuousAt hup hlo.isCoboundedUnder_le
  simpa [Function.comp_def] using this.symm

/-- Private lower tail bound: for bounded measurable `f`, `k̄ · liminf f ≤ liminf (k*f)`. -/
lemma aux_tail_lower [Countable ι] (m : RowModel ι) (f : ℝ → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ s ∈ Ici (0 : ℝ), |f s| ≤ C) :
    m.kbar * Filter.liminf f atTop ≤ Filter.liminf (oneSidedConv f m.kernel) atTop := by
  have hKint : IntegrableOn m.kernel (Ioi 0) := (lem_app_phase_kernel_ii m).1
  have hKtot : ∫ s in Ioi (0 : ℝ), m.kernel s = m.kbar := (lem_app_phase_kernel_ii m).2.1
  have hKnn := aux_kernel_nonneg_tail m
  have hkb : 0 ≤ m.kbar := aux_kbar_nonneg_tail m
  have hKI : ∀ a b : ℝ, 0 ≤ a → a ≤ b → IntervalIntegrable m.kernel volume a b :=
    fun a b ha hab => (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (hKint.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha)))
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 (Set.mem_Ici.2 le_rfl))
  have hfup : IsBoundedUnder (· ≤ ·) atTop f :=
    isBoundedUnder_of_eventually_le (a := C) (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      exact (abs_le.1 (hC s (Set.mem_Ici.2 hs))).2)
  have hflo : IsBoundedUnder (· ≥ ·) atTop f :=
    isBoundedUnder_of_eventually_ge (a := -C) (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      exact (abs_le.1 (hC s (Set.mem_Ici.2 hs))).1)
  have hT : Tendsto (fun t : ℝ => ∫ s in (0:ℝ)..t, m.kernel s) atTop (𝓝 m.kbar) := by
    rw [← hKtot]; exact intervalIntegral_tendsto_integral_Ioi 0 hKint tendsto_id
  have hkey : ∀ ε : ℝ, 0 < ε →
      m.kbar * (Filter.liminf f atTop - ε) ≤ Filter.liminf (oneSidedConv f m.kernel) atTop := by
    intro ε hε
    obtain ⟨U0, hU0⟩ := eventually_atTop.1
      (Filter.eventually_lt_of_lt_liminf (show Filter.liminf f atTop - ε < Filter.liminf f atTop by
        linarith) hflo)
    set L := Filter.liminf f atTop with hL
    set U := max U0 0 with hUdef
    have hU : ∀ x, U ≤ x → L - ε < f x := fun x hx => hU0 x ((le_max_left _ _).trans hx)
    have hU0' : 0 ≤ U := le_max_right _ _
    have hsub : Tendsto (fun t : ℝ => t - U) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-U) tendsto_id
    have hI : Tendsto (fun t : ℝ => ∫ s in (0:ℝ)..(t - U), m.kernel s) atTop (𝓝 m.kbar) := by
      rw [← hKtot]; exact intervalIntegral_tendsto_integral_Ioi 0 hKint hsub
    have hJ : Tendsto (fun t : ℝ => ∫ s in (t - U)..t, m.kernel s) atTop (𝓝 0) := by
      have h0 := hT.sub hI
      rw [sub_self] at h0
      refine Tendsto.congr' ?_ h0
      filter_upwards [eventually_ge_atTop U] with t ht
      exact intervalIntegral.integral_interval_sub_left (hKI 0 t le_rfl (by linarith))
        (hKI 0 (t - U) le_rfl (by linarith))
    have hH : Tendsto (fun t : ℝ => (L - ε) * (∫ s in (0:ℝ)..(t - U), m.kernel s)
        - C * ∫ s in (t - U)..t, m.kernel s) atTop (𝓝 ((L - ε) * m.kbar - C * 0)) :=
      (hI.const_mul (L - ε)).sub (hJ.const_mul C)
    have hev : ∀ᶠ t in atTop, (L - ε) * (∫ s in (0:ℝ)..(t - U), m.kernel s)
        - C * ∫ s in (t - U)..t, m.kernel s ≤ oneSidedConv f m.kernel t := by
      filter_upwards [eventually_ge_atTop U] with t ht
      have ha : 0 ≤ t - U := by linarith
      have hgI : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ t →
          IntervalIntegrable (fun s => f (t - s) * m.kernel s) volume a b := by
        intro a b ha0 hab hbt
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
        refine Integrable.bdd_mul (f := fun s => f (t - s)) (c := C)
          (hKint.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha0)))
          (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
        rw [ae_restrict_iff' measurableSet_Ioc]
        refine Filter.Eventually.of_forall (fun s hs => ?_)
        rw [Real.norm_eq_abs]
        exact hC _ (Set.mem_Ici.2 (by linarith [hs.2]))
      have hsplit : oneSidedConv f m.kernel t
          = (∫ s in (0:ℝ)..(t - U), f (t - s) * m.kernel s)
            + ∫ s in (t - U)..t, f (t - s) * m.kernel s := by
        unfold oneSidedConv
        rw [intervalIntegral.integral_add_adjacent_intervals
          (hgI 0 (t - U) le_rfl ha (by linarith)) (hgI (t - U) t ha (by linarith) le_rfl)]
      have hlo : (L - ε) * (∫ s in (0:ℝ)..(t - U), m.kernel s)
          ≤ ∫ s in (0:ℝ)..(t - U), f (t - s) * m.kernel s := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_mono_on ha
          ((hKI 0 (t - U) le_rfl ha).const_mul _) (hgI 0 (t - U) le_rfl ha (by linarith)) ?_
        intro x hx
        exact mul_le_mul_of_nonneg_right (hU (t - x) (by linarith [hx.2]) |>.le) (hKnn x)
      have hhi : -(C * ∫ s in (t - U)..t, m.kernel s)
          ≤ ∫ s in (t - U)..t, f (t - s) * m.kernel s := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
        refine intervalIntegral.integral_mono_on (by linarith)
          (((hKI (t - U) t ha (by linarith)).const_mul C).neg)
          (hgI (t - U) t ha (by linarith) le_rfl) ?_
        intro x hx
        have hb := (abs_le.1 (hC (t - x) (Set.mem_Ici.2 (by linarith [hx.2])))).1
        have := mul_le_mul_of_nonneg_right hb (hKnn x)
        linarith
      rw [hsplit]
      linarith [hlo, hhi]
    have hu_up : IsBoundedUnder (· ≤ ·) atTop (oneSidedConv f m.kernel) :=
      isBoundedUnder_of_eventually_le (a := m.kbar * C) (by
        filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
        exact (abs_le.1 (aux_conv_abs_le m f hf C hC t ht)).2)
    have hlim := Filter.liminf_le_liminf hev (hH.isBoundedUnder_ge) hu_up.isCoboundedUnder_ge
    rw [hH.liminf_eq] at hlim
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  have hδ := hkey (ε / (m.kbar + 1)) (div_pos hε (by linarith))
  have hprod : m.kbar * (ε / (m.kbar + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  linarith [hδ, hprod]

/-- `lem:app-phase-tail`, snapshot `cr-2026-10-23`.
Hypotheses: `f ≥ 0` and bounded on `[0,∞)` (`Filter.liminf`/`limsup` at `atTop`
are then the paper's `ℓ_±`); `f` measurable (Lean helper hypothesis).
Source: `section.tex` l.246–253.

LaTeX (verbatim, `section.tex` l.246–253):
```
\begin{lemma}[Tail of a convolution]\label{lem:app-phase-tail}
Assume (M1), and let $f\ge0$ be bounded on $[0,\infty)$ with
$\ell_-\defeq\liminf_{s\to\infty}f(s)$ and $\ell_+\defeq\limsup_{s\to\infty}f(s)$.
Then
\[
\bar k\,\ell_-\le\liminf_{s\to\infty}(k*f)(s)\le\limsup_{s\to\infty}(k*f)(s)\le\bar k\,\ell_+ .
\]
\end{lemma}
``` -/

theorem lem_app_phase_tail
    [Countable ι] (m : RowModel ι) (f : ℝ → ℝ) (hf : Measurable f)
    (hnn : ∀ s ∈ Ici (0 : ℝ), 0 ≤ f s) (hb : ∃ C : ℝ, ∀ s ∈ Ici (0 : ℝ), |f s| ≤ C) :
    m.kbar * Filter.liminf f atTop ≤ Filter.liminf (oneSidedConv f m.kernel) atTop ∧
      Filter.liminf (oneSidedConv f m.kernel) atTop ≤
        Filter.limsup (oneSidedConv f m.kernel) atTop ∧
      Filter.limsup (oneSidedConv f m.kernel) atTop ≤ m.kbar * Filter.limsup f atTop := by
  obtain ⟨C, hC⟩ := hb
  have hC' : ∀ s ∈ Ici (0 : ℝ), |f s| ≤ C := hC
  have hu_up : IsBoundedUnder (· ≤ ·) atTop (oneSidedConv f m.kernel) :=
    isBoundedUnder_of_eventually_le (a := m.kbar * C) (by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
      exact (abs_le.1 (aux_conv_abs_le m f hf C hC' t ht)).2)
  have hu_lo : IsBoundedUnder (· ≥ ·) atTop (oneSidedConv f m.kernel) :=
    isBoundedUnder_of_eventually_ge (a := -(m.kbar * C)) (by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
      exact (abs_le.1 (aux_conv_abs_le m f hf C hC' t ht)).1)
  have hfup : IsBoundedUnder (· ≤ ·) atTop f :=
    isBoundedUnder_of_eventually_le (a := C) (by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
      exact (abs_le.1 (hC' s (Set.mem_Ici.2 hs))).2)
  have hflo : IsBoundedUnder (· ≥ ·) atTop f :=
    isBoundedUnder_of_eventually_ge (a := -C) (by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
      exact (abs_le.1 (hC' s (Set.mem_Ici.2 hs))).1)
  have h2 := aux_tail_lower m (fun s => -f s) hf.neg C (fun s hs => by
    simp only [abs_neg]; exact hC' s hs)
  have hconv_neg : oneSidedConv (fun s => -f s) m.kernel = fun t => -oneSidedConv f m.kernel t := by
    funext t
    simp only [oneSidedConv, neg_mul, intervalIntegral.integral_neg]
  rw [hconv_neg, aux_liminf_neg f hfup hflo, aux_liminf_neg _ hu_up hu_lo] at h2
  refine ⟨aux_tail_lower m f hf C hC', Filter.liminf_le_limsup hu_up hu_lo, ?_⟩
  linarith

lemma aux_cmp_sqrt_sub_le {a b m : ℝ} (hm : 0 < m) (hb : m ≤ b) (ha : 0 ≤ a) (hb0 : 0 ≤ b) :
    Real.sqrt a - Real.sqrt b ≤ 1 / Real.sqrt m * max (a - b) 0 := by
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hsb : Real.sqrt m ≤ Real.sqrt b := Real.sqrt_le_sqrt hb
  rw [one_div_mul_eq_div]
  rcases le_total a b with hab | hab
  · have h1 : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
    have : 0 ≤ max (a - b) 0 / Real.sqrt m := div_nonneg (le_max_right _ _) hsm.le
    linarith
  · have hb' : 0 < Real.sqrt b := lt_of_lt_of_le hsm hsb
    have hne : 0 < Real.sqrt a + Real.sqrt b := by have := Real.sqrt_nonneg a; linarith
    have key : Real.sqrt a - Real.sqrt b = (a - b) / (Real.sqrt a + Real.sqrt b) := by
      rw [eq_div_iff hne.ne']
      linear_combination Real.sq_sqrt ha - Real.sq_sqrt hb0
    rw [key, max_eq_left (sub_nonneg.2 hab)]
    exact div_le_div_of_nonneg_left (sub_nonneg.2 hab) hsm (by linarith [Real.sqrt_nonneg a])

lemma aux_cmp_ae_ne (c : ℝ) : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ c := by
  simp [ae_iff]

/-- `lem:app-phase-comparison`, snapshot `cr-2026-10-23`.
Here `𝗄` is the kernel of the lemma (Lean name `kc`), `m` is the positive constant of
the lemma, and `G` the forcing-type term; `𝗄 * √x` is `oneSidedConv (√x) kc`. Positivity
and integrability of `kc` are on `Ioo 0 S'`, where the paper's kernel lives.
Source: `section.tex` l.272–280.

LaTeX (verbatim, `section.tex` l.272–280):
```
\begin{lemma}[Comparison]\label{lem:app-phase-comparison}
Let $S'>0$, let $\mathsf k\ge0$ be integrable on $(0,S')$, let $G\ge0$ be
continuous on $[0,S']$, and let $m>0$. Let $x$ and $y$ be continuous and
nonnegative on $[0,S']$, with $y\ge m$ and
\[
x\le G+\mathsf k*\sqrt x,\qquad y\ge G+\mathsf k*\sqrt y\qquad\text{on }[0,S'].
\]
Then $x\le y$ on $[0,S']$.
\end{lemma}
``` -/

theorem lem_app_phase_comparison
    (S' : ℝ) (hS' : 0 < S') (kc : ℝ → ℝ)
    (hkc_nonneg : ∀ s ∈ Ioo (0 : ℝ) S', 0 ≤ kc s) (hkc_int : IntegrableOn kc (Ioo 0 S'))
    (G : ℝ → ℝ) (hG : ContinuousOn G (Icc 0 S')) (hG_nonneg : ∀ s ∈ Icc (0 : ℝ) S', 0 ≤ G s)
    (m : ℝ) (hm : 0 < m)
    (x y : ℝ → ℝ) (hx : ContinuousOn x (Icc 0 S')) (hx_nonneg : ∀ s ∈ Icc (0 : ℝ) S', 0 ≤ x s)
    (hy : ContinuousOn y (Icc 0 S')) (hy_nonneg : ∀ s ∈ Icc (0 : ℝ) S', 0 ≤ y s)
    (hym : ∀ s ∈ Icc (0 : ℝ) S', m ≤ y s)
    (hxsub : ∀ s ∈ Icc (0 : ℝ) S', x s ≤ G s + oneSidedConv (fun u => Real.sqrt (x u)) kc s)
    (hysub : ∀ s ∈ Icc (0 : ℝ) S', G s + oneSidedConv (fun u => Real.sqrt (y u)) kc s ≤ y s) :
    ∀ s ∈ Icc (0 : ℝ) S', x s ≤ y s := by
  have hS0 : (0 : ℝ) ≤ S' := hS'.le
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hkc_ii : IntervalIntegrable kc volume 0 S' := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hS0]; exact hkc_int
  -- a.e. membership in the open interval, on [0,b] with b ≤ S'
  have hae : ∀ b : ℝ, b ≤ S' → ∀ᵐ u ∂(volume.restrict (Icc (0 : ℝ) b)), u ∈ Ioo (0 : ℝ) S' := by
    intro b hb
    filter_upwards [ae_restrict_of_ae (aux_cmp_ae_ne 0), ae_restrict_of_ae (aux_cmp_ae_ne S'),
      ae_restrict_mem measurableSet_Icc] with u h0 hS h
    exact ⟨lt_of_le_of_ne h.1 (Ne.symm h0), lt_of_le_of_ne (le_trans h.2 hb) hS⟩
  have hkcnn : ∀ b : ℝ, b ≤ S' → ∀ᵐ u ∂(volume.restrict (Icc (0 : ℝ) b)), 0 ≤ kc u := by
    intro b hb
    filter_upwards [hae b hb] with u hu using hkc_nonneg u hu
  have hkc_sub : ∀ t ∈ Icc (0 : ℝ) S', IntervalIntegrable kc volume 0 t := by
    intro t ht
    refine hkc_ii.mono_set ?_
    rw [uIcc_of_le hS0, uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hsubs : ∀ t ∈ Icc (0 : ℝ) S', ∀ u ∈ uIcc (0 : ℝ) t, t - u ∈ Icc (0 : ℝ) S' := by
    intro t ht u hu
    rw [uIcc_of_le ht.1] at hu
    exact ⟨by linarith [hu.2], by linarith [hu.1, ht.2]⟩
  have hcomp : ∀ f : ℝ → ℝ, ContinuousOn f (Icc 0 S') → ∀ t ∈ Icc (0 : ℝ) S',
      ContinuousOn (fun u => f (t - u)) (uIcc 0 t) := by
    intro f hf t ht
    exact hf.comp (continuousOn_const.sub continuousOn_id) (fun u hu => hsubs t ht u hu)
  -- nonnegativity of the one-sided convolution of a nonnegative function
  have hnn_int : ∀ f : ℝ → ℝ, (∀ u ∈ Icc (0 : ℝ) S', 0 ≤ f u) → ∀ t ∈ Icc (0 : ℝ) S',
      0 ≤ ∫ u in (0 : ℝ)..t, f (t - u) * kc u := by
    intro f hf t ht
    refine intervalIntegral.integral_nonneg_of_ae_restrict ht.1 ?_
    filter_upwards [hkcnn t ht.2, ae_restrict_mem measurableSet_Icc] with u hu hu'
    have hmem : u ∈ uIcc (0 : ℝ) t := by rw [uIcc_of_le ht.1]; exact hu'
    exact mul_nonneg (hf _ (hsubs t ht u hmem)) hu
  -- weighted-exponential limit of the kernel mass
  have hlim : Tendsto (fun lam : ℝ => ∫ u in (0 : ℝ)..S', Real.exp (-(lam * u)) * kc u)
      atTop (𝓝 0) := by
    have hint : ∀ lam : ℝ, IntervalIntegrable (fun u => Real.exp (-(lam * u)) * kc u) volume 0 S' :=
      fun lam => hkc_ii.continuousOn_mul (by fun_prop : Continuous fun u : ℝ => Real.exp (-(lam * u))).continuousOn
    have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := (0 : ℝ)) (b := S') (l := atTop)
      (F := fun (lam : ℝ) (u : ℝ) => Real.exp (-(lam * u)) * kc u) (f := fun _ => (0 : ℝ))
      (fun u => |kc u|)
      (Eventually.of_forall fun lam => by
        rw [uIoc_of_le hS0]; exact (hint lam).1.aestronglyMeasurable)
      (eventually_ge_atTop (0 : ℝ) |>.mono fun lam hlam => Eventually.of_forall fun u hu => by
        rw [uIoc_of_le hS0] at hu
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_of_le_one_left (abs_nonneg _)
          (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hlam hu.1.le))))
      hkc_ii.abs
      (Eventually.of_forall fun u hu => by
        rw [uIoc_of_le hS0] at hu
        have h1 : Tendsto (fun lam : ℝ => -(lam * u)) atTop atBot :=
          tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hu.1)
        have h2 := (Real.tendsto_exp_atBot.comp h1).mul_const (kc u)
        rw [zero_mul] at h2
        exact h2)
    simpa using h
  -- the positive part d = (x-y)_+
  set d : ℝ → ℝ := fun u => max (x u - y u) 0 with hd_def
  have hd_cont : ContinuousOn d (Icc 0 S') := ContinuousOn.sup (hx.sub hy) continuousOn_const
  have hd_nn : ∀ u, 0 ≤ d u := fun u => le_max_right _ _
  -- one-step bound: x t - y t <= (sqrt m)⁻¹ * int_0^t d(t-u) kc(u) du
  have hstep : ∀ t ∈ Icc (0 : ℝ) S', x t - y t ≤
      (Real.sqrt m)⁻¹ * ∫ u in (0 : ℝ)..t, d (t - u) * kc u := by
    intro t ht
    have ht0 := ht.1
    have hcx : ContinuousOn (fun u => Real.sqrt (x (t - u))) (uIcc 0 t) :=
      Real.continuous_sqrt.comp_continuousOn (hcomp x hx t ht)
    have hcy : ContinuousOn (fun u => Real.sqrt (y (t - u))) (uIcc 0 t) :=
      Real.continuous_sqrt.comp_continuousOn (hcomp y hy t ht)
    have hA : oneSidedConv (fun u => Real.sqrt (x u)) kc t
        - oneSidedConv (fun u => Real.sqrt (y u)) kc t
        = ∫ u in (0 : ℝ)..t, (Real.sqrt (x (t - u)) - Real.sqrt (y (t - u))) * kc u := by
      simp only [oneSidedConv]
      rw [← intervalIntegral.integral_sub
        ((hkc_sub t ht).continuousOn_mul hcx) ((hkc_sub t ht).continuousOn_mul hcy)]
      congr 1
      funext u
      ring
    have hmono : ∫ u in (0 : ℝ)..t, (Real.sqrt (x (t - u)) - Real.sqrt (y (t - u))) * kc u
        ≤ ∫ u in (0 : ℝ)..t, (Real.sqrt m)⁻¹ * d (t - u) * kc u := by
      refine intervalIntegral.integral_mono_ae_restrict ht0
        ((hkc_sub t ht).continuousOn_mul (hcx.sub hcy))
        ((hkc_sub t ht).continuousOn_mul ((continuousOn_const.mul (hcomp d hd_cont t ht))) ) ?_
      filter_upwards [hkcnn t ht.2, ae_restrict_mem measurableSet_Icc] with u hu hu'
      have hmem : u ∈ uIcc (0 : ℝ) t := by rw [uIcc_of_le ht0]; exact hu'
      have hsq := aux_cmp_sqrt_sub_le hm (hym _ (hsubs t ht u hmem))
        (hx_nonneg _ (hsubs t ht u hmem)) (hy_nonneg _ (hsubs t ht u hmem))
      have hsq' : Real.sqrt (x (t - u)) - Real.sqrt (y (t - u)) ≤ (Real.sqrt m)⁻¹ * d (t - u) := by
        rw [← one_div]; exact hsq
      exact mul_le_mul_of_nonneg_right hsq' hu
    have hsplit : ∫ u in (0 : ℝ)..t, (Real.sqrt m)⁻¹ * d (t - u) * kc u
        = (Real.sqrt m)⁻¹ * ∫ u in (0 : ℝ)..t, d (t - u) * kc u := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext u
      ring
    have hG' := hxsub t ht
    have hH' := hysub t ht
    calc x t - y t ≤ oneSidedConv (fun u => Real.sqrt (x u)) kc t
          - oneSidedConv (fun u => Real.sqrt (y u)) kc t := by linarith
      _ = _ := hA
      _ ≤ _ := hmono
      _ = _ := hsplit
  -- the weight: choose lam >= 0 with (sqrt m)⁻¹ * C(lam) < 1/2
  obtain ⟨lam, hlam_lt, hlam0⟩ := ((hlim.eventually (gt_mem_nhds
      (half_pos hsm))).and (eventually_ge_atTop (0 : ℝ))).exists
  set C : ℝ := ∫ u in (0 : ℝ)..S', Real.exp (-(lam * u)) * kc u with hC_def
  have hκ : (Real.sqrt m)⁻¹ * C ≤ 1 / 2 := by
    rw [inv_mul_le_iff₀ hsm]; linarith
  -- the maximiser of the weighted positive part
  set g : ℝ → ℝ := fun u => Real.exp (-(lam * u)) * d u with hg_def
  have hgc : ContinuousOn g (Icc 0 S') :=
    (by fun_prop : Continuous fun u : ℝ => Real.exp (-(lam * u))).continuousOn.mul hd_cont
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hS0) hgc
  have hD0 : 0 ≤ g t0 := mul_nonneg (Real.exp_pos _).le (hd_nn t0)
  -- key bound: g s <= (sqrt m)⁻¹ * (g t0 * C) for s in [0,S']
  have hkey : ∀ s ∈ Icc (0 : ℝ) S', g s ≤ (Real.sqrt m)⁻¹ * (g t0 * C) := by
    intro s hs
    have hds : d s ≤ (Real.sqrt m)⁻¹ * ∫ u in (0 : ℝ)..s, d (s - u) * kc u :=
      max_le (hstep s hs) (mul_nonneg (inv_nonneg.2 hsm.le) (hnn_int d (fun u hu => hd_nn u) s hs))
    have hcm : Real.exp (-(lam * s)) * ∫ u in (0 : ℝ)..s, d (s - u) * kc u
        = ∫ u in (0 : ℝ)..s, (Real.exp (-(lam * s)) * d (s - u)) * kc u := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext u
      ring
    have hint_F : IntervalIntegrable (fun u => (Real.exp (-(lam * s)) * d (s - u)) * kc u) volume 0 s :=
      (hkc_sub s hs).continuousOn_mul (continuousOn_const.mul (hcomp d hd_cont s hs))
    have hint_D : IntervalIntegrable (fun u => g t0 * (Real.exp (-(lam * u)) * kc u)) volume 0 s :=
      ((hkc_sub s hs).continuousOn_mul
        (by fun_prop : Continuous fun u : ℝ => Real.exp (-(lam * u))).continuousOn).const_mul (g t0)
    have hint_h : IntervalIntegrable (fun u => Real.exp (-(lam * u)) * kc u) volume 0 S' :=
      hkc_ii.continuousOn_mul (by fun_prop : Continuous fun u : ℝ => Real.exp (-(lam * u))).continuousOn
    have hpt : ∫ u in (0 : ℝ)..s, (Real.exp (-(lam * s)) * d (s - u)) * kc u
        ≤ ∫ u in (0 : ℝ)..s, g t0 * (Real.exp (-(lam * u)) * kc u) := by
      refine intervalIntegral.integral_mono_ae_restrict hs.1 hint_F hint_D ?_
      filter_upwards [hae s hs.2, ae_restrict_mem measurableSet_Icc] with u hu hu'
      have hmem : u ∈ uIcc (0 : ℝ) s := by rw [uIcc_of_le hs.1]; exact hu'
      have hgle : g (s - u) ≤ g t0 := isMaxOn_iff.1 hmax (s - u) (hsubs s hs u hmem)
      have hexp : Real.exp (-(lam * s)) * d (s - u) = Real.exp (-(lam * u)) * g (s - u) := by
        have hgu : g (s - u) = Real.exp (-(lam * (s - u))) * d (s - u) := rfl
        rw [hgu, ← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      calc (Real.exp (-(lam * s)) * d (s - u)) * kc u
          = (Real.exp (-(lam * u)) * g (s - u)) * kc u := by rw [hexp]
        _ ≤ (Real.exp (-(lam * u)) * g t0) * kc u :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgle (Real.exp_pos _).le)
              (hkc_nonneg u hu)
        _ = g t0 * (Real.exp (-(lam * u)) * kc u) := by ring
    have hae_nn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) S')] fun u => Real.exp (-(lam * u)) * kc u := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self (hkcnn S' le_rfl)]
        with u hu
      exact mul_nonneg (Real.exp_pos _).le hu
    have hIs : ∫ u in (0 : ℝ)..s, Real.exp (-(lam * u)) * kc u ≤ C :=
      intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2 hae_nn hint_h
    calc g s = Real.exp (-(lam * s)) * d s := rfl
      _ ≤ Real.exp (-(lam * s)) * ((Real.sqrt m)⁻¹ * ∫ u in (0 : ℝ)..s, d (s - u) * kc u) :=
          mul_le_mul_of_nonneg_left hds (Real.exp_pos _).le
      _ = (Real.sqrt m)⁻¹ * (Real.exp (-(lam * s)) * ∫ u in (0 : ℝ)..s, d (s - u) * kc u) := by
          ring
      _ = (Real.sqrt m)⁻¹ * ∫ u in (0 : ℝ)..s, (Real.exp (-(lam * s)) * d (s - u)) * kc u := by
          rw [hcm]
      _ ≤ (Real.sqrt m)⁻¹ * ∫ u in (0 : ℝ)..s, g t0 * (Real.exp (-(lam * u)) * kc u) :=
          mul_le_mul_of_nonneg_left hpt (inv_nonneg.2 hsm.le)
      _ = (Real.sqrt m)⁻¹ * (g t0 * ∫ u in (0 : ℝ)..s, Real.exp (-(lam * u)) * kc u) := by
          rw [intervalIntegral.integral_const_mul]
      _ ≤ (Real.sqrt m)⁻¹ * (g t0 * C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIs hD0) (inv_nonneg.2 hsm.le)
  -- the maximum is nonpositive, hence the positive part vanishes everywhere
  have hbound : ∀ s ∈ Icc (0 : ℝ) S', g s ≤ g t0 / 2 := by
    intro s hs
    refine (hkey s hs).trans ?_
    calc (Real.sqrt m)⁻¹ * (g t0 * C) = g t0 * ((Real.sqrt m)⁻¹ * C) := by ring
      _ ≤ g t0 * (1 / 2) := mul_le_mul_of_nonneg_left hκ hD0
      _ = g t0 / 2 := by ring
  have hgt0 : g t0 ≤ 0 := by linarith [hbound t0 ht0]
  intro s hs
  have hgs : g s ≤ 0 := by linarith [hbound s hs]
  have hds : d s ≤ 0 := by
    by_contra hc
    rw [not_le] at hc
    have := mul_pos (Real.exp_pos (-(lam * s))) hc
    linarith
  have h3 : x s - y s ≤ d s := le_max_left _ _
  linarith

/-- `thm:app-phase-volterra`, part (ii) of 5: local uniqueness on [0,S'], snapshot `cr-2026-10-23`.
Uniqueness of local solutions on each `[0,S']`, `S' > 0` (the local uniqueness
used by `thm:app-phase-clock`).
Source: `section.tex` l.303–315.

LaTeX (verbatim, `section.tex` l.303–315):
```
\begin{theorem}[Existence, uniqueness and floor]\label{thm:app-phase-volterra}
Assume (M1). The Volterra equation \cref{eqn:app-phase-volterra} has a unique solution
$Q$ on $[0,\infty)$. It satisfies
\begin{equation}\label{eqn:app-phase-Mbound}
0<F(s)\le Q(s)\le M\defeq\Big(\frac{\bar k+\sqrt{\bar k^2+4F_0}}2\Big)^2\qquad(s\ge0),
\end{equation}
and
\[
\lim_{s\to\infty}Q(s)=\bar k^2=\frac{\lr^2\mathcal S^2}4 .
\]
If $\mathcal S>0$ and $\epsilon>0$, the unique step $\lr>0$ with floor
$\lr^2\mathcal S^2/4=\epsilon$ is $\lr=2\sqrt\epsilon/\mathcal S$.
\end{theorem}
``` -/

theorem thm_app_phase_volterra_ii
    [Countable ι] (m : RowModel ι) (S' : ℝ) (hS' : 0 < S') (Q₁ Q₂ : ℝ → ℝ)
    (h₁ : IsVolterraSolOn m S' Q₁) (h₂ : IsVolterraSolOn m S' Q₂) :
    ∀ s ∈ Icc (0 : ℝ) S', Q₁ s = Q₂ s := by
  have hK := lem_app_phase_kernel_i m
  have hKii := lem_app_phase_kernel_ii m
  have hkc_int : IntegrableOn m.kernel (Ioo 0 S') := hKii.1.mono_set Ioo_subset_Ioi_self
  have hkc_nonneg : ∀ s ∈ Ioo (0 : ℝ) S', 0 ≤ m.kernel s := fun s _ => aux_kernel_nonneg_tail m s
  have hG : ContinuousOn m.forcing (Icc 0 S') := hK.1.mono Icc_subset_Ici_self
  have hG_nn : ∀ s ∈ Icc (0 : ℝ) S', 0 ≤ m.forcing s :=
    fun s hs => (hK.2.2.2.1 s (Set.mem_Ici.2 hs.1)).le
  have hFpos : 0 < m.forcing S' := hK.2.2.2.1 S' (Set.mem_Ici.2 hS'.le)
  have hFanti : ∀ s ∈ Icc (0 : ℝ) S', m.forcing S' ≤ m.forcing s :=
    fun s hs => hK.2.1.antitoneOn (Set.mem_Ici.2 hs.1) (Set.mem_Ici.2 hS'.le) hs.2
  -- lower bound Q >= F on [0,S'] for any local solution
  have hQge : ∀ Q : ℝ → ℝ, IsVolterraSolOn m S' Q → ∀ s ∈ Icc (0 : ℝ) S', m.forcing s ≤ Q s := by
    intro Q hQ s hs
    have hEq := hQ.2.2 s hs
    have hconv : 0 ≤ oneSidedConv (fun u => Real.sqrt (Q u)) m.kernel s := by
      unfold oneSidedConv
      exact intervalIntegral.integral_nonneg hs.1
        (fun x _ => mul_nonneg (Real.sqrt_nonneg _) (aux_kernel_nonneg_tail m x))
    linarith
  -- comparison: any two local solutions are ordered
  have key : ∀ A B : ℝ → ℝ, IsVolterraSolOn m S' A → IsVolterraSolOn m S' B →
      ∀ s ∈ Icc (0 : ℝ) S', A s ≤ B s := by
    intro A B hA hB
    refine lem_app_phase_comparison S' hS' m.kernel hkc_nonneg hkc_int m.forcing hG hG_nn
      (m.forcing S') hFpos A B hA.1 hA.2.1 hB.1 hB.2.1 ?_ ?_ ?_
    · intro s hs
      exact (hFanti s hs).trans (hQge B hB s hs)
    · intro s hs
      exact le_of_eq (hA.2.2 s hs)
    · intro s hs
      exact le_of_eq (hB.2.2 s hs).symm
  intro s hs
  exact le_antisymm (key Q₁ Q₂ h₁ h₂ s hs) (key Q₂ Q₁ h₂ h₁ s hs)

/-- Private: interval integrability of `x ↦ f(t-x) k(x)` for measurable `f` bounded by `C`. -/
lemma aux_conv_intble [Countable ι] (m : RowModel ι) {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ s, |f s| ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun x => f (t - x) * m.kernel x) volume 0 t := by
  have hKint : IntegrableOn m.kernel (Ioi 0) := (lem_app_phase_kernel_ii m).1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  refine Integrable.bdd_mul (f := fun x => f (t - x)) (c := C)
    (hKint.mono_set Ioc_subset_Ioi_self)
    (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall (fun x _ => ?_)
  rw [Real.norm_eq_abs]
  exact hC _

/-- Private: continuity on `Icc 0 S'` for all `S' > 0` gives continuity on `Ici 0`. -/
lemma aux_contOn_Ici_of_Icc {h : ℝ → ℝ}
    (H : ∀ S' : ℝ, 0 < S' → ContinuousOn h (Icc 0 S')) : ContinuousOn h (Ici 0) := by
  intro x hx
  have hx0 : 0 ≤ x := hx
  have h1 := H (x + 1) (by linarith) x ⟨hx0, by linarith⟩
  refine h1.mono_of_mem_nhdsWithin ?_
  exact mem_nhdsWithin.2 ⟨Iio (x + 1), isOpen_Iio, by simp, fun y hy => ⟨hy.2, le_of_lt hy.1⟩⟩

/-- Private: convolution with the kernel of a bounded measurable function is continuous on
`[0,∞)`. -/
lemma aux_conv_contOn_Ici [Countable ι] (m : RowModel ι) {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ s, |f s| ≤ C) : ContinuousOn (oneSidedConv f m.kernel) (Ici 0) :=
  aux_contOn_Ici_of_Icc (fun S' hS' =>
    (lem_app_phase_kernel_iii m S' hS' f hf ⟨C, fun s _ => hC s⟩).1)

/-- Private: one Picard step preserves continuity, the bounds `0 ≤ · ≤ r²`, and dominates `F`. -/
lemma aux_step [Countable ι] (m : RowModel ι) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ^ 2 = m.kbar * r + m.F0) {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ s, 0 ≤ g s)
    (hgr : ∀ s, g s ≤ r ^ 2) :
    Continuous (fun s => m.forcing (max s 0) + oneSidedConv (fun u => Real.sqrt (g u)) m.kernel (max s 0)) ∧
    ∀ s, m.forcing (max s 0) ≤ m.forcing (max s 0) + oneSidedConv (fun u => Real.sqrt (g u)) m.kernel (max s 0) ∧
      m.forcing (max s 0) + oneSidedConv (fun u => Real.sqrt (g u)) m.kernel (max s 0) ≤ r ^ 2 := by
  have hsq : Continuous fun u => Real.sqrt (g u) := Real.continuous_sqrt.comp hg
  have hsqb : ∀ s, |Real.sqrt (g s)| ≤ r := fun s => by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (g s) ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt (hgr s)
      _ = r := Real.sqrt_sq hr0
  have hK := lem_app_phase_kernel_i m
  have hclamp : Continuous fun s : ℝ => max s 0 := continuous_id.max continuous_const
  refine ⟨?_, fun s => ⟨?_, ?_⟩⟩
  · exact (hK.1.comp_continuous hclamp (fun s => le_max_right s 0)).add
      ((aux_conv_contOn_Ici m hsq.measurable hsqb).comp_continuous hclamp
        (fun s => le_max_right s 0))
  · have : 0 ≤ oneSidedConv (fun u => Real.sqrt (g u)) m.kernel (max s 0) := by
      unfold oneSidedConv
      exact intervalIntegral.integral_nonneg (le_max_right s 0)
        (fun x _ => mul_nonneg (Real.sqrt_nonneg _) (aux_kernel_nonneg_tail m x))
    linarith
  · have ht : 0 ≤ max s 0 := le_max_right s 0
    have hFle : m.forcing (max s 0) ≤ m.F0 := by
      rw [← hK.2.2.1]
      exact hK.2.1.antitoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
    have hc := (le_abs_self _).trans
      (aux_conv_abs_le m _ hsq.measurable r (fun s _ => hsqb s) (max s 0) ht)
    linarith

/-- Private: the Picard step is monotone. -/
lemma aux_step_mono [Countable ι] (m : RowModel ι) {r : ℝ} (hr0 : 0 ≤ r)
    {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h) (hg0 : ∀ s, 0 ≤ g s)
    (hh0 : ∀ s, 0 ≤ h s) (hgr : ∀ s, g s ≤ r ^ 2) (hhr : ∀ s, h s ≤ r ^ 2)
    (hgh : ∀ s, g s ≤ h s) (s : ℝ) :
    m.forcing (max s 0) + oneSidedConv (fun u => Real.sqrt (g u)) m.kernel (max s 0) ≤
      m.forcing (max s 0) + oneSidedConv (fun u => Real.sqrt (h u)) m.kernel (max s 0) := by
  have hsqb : ∀ (g : ℝ → ℝ), (∀ s, g s ≤ r ^ 2) → ∀ s, |Real.sqrt (g s)| ≤ r := fun g hgr s => by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (g s) ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt (hgr s)
      _ = r := Real.sqrt_sq hr0
  have ht : 0 ≤ max s 0 := le_max_right s 0
  have := intervalIntegral.integral_mono_on ht
    (aux_conv_intble m (Real.continuous_sqrt.comp hg).measurable (hsqb g hgr) ht)
    (aux_conv_intble m (Real.continuous_sqrt.comp hh).measurable (hsqb h hhr) ht)
    (fun x _ => mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hgh _))
      (aux_kernel_nonneg_tail m x))
  unfold oneSidedConv
  exact add_le_add_right this _

/-- `thm:app-phase-volterra`, part (i) of 5, snapshot `cr-2026-10-23`.
Existence of a solution on `[0,∞)` and global uniqueness among solutions on `[0,∞)`.
Source: `section.tex` l.303–315.

LaTeX (verbatim, `section.tex` l.303–315):
```
\begin{theorem}[Existence, uniqueness and floor]\label{thm:app-phase-volterra}
Assume (M1). The Volterra equation \cref{eqn:app-phase-volterra} has a unique solution
$Q$ on $[0,\infty)$. It satisfies
\begin{equation}\label{eqn:app-phase-Mbound}
0<F(s)\le Q(s)\le M\defeq\Big(\frac{\bar k+\sqrt{\bar k^2+4F_0}}2\Big)^2\qquad(s\ge0),
\end{equation}
and
\[
\lim_{s\to\infty}Q(s)=\bar k^2=\frac{\lr^2\mathcal S^2}4 .
\]
If $\mathcal S>0$ and $\epsilon>0$, the unique step $\lr>0$ with floor
$\lr^2\mathcal S^2/4=\epsilon$ is $\lr=2\sqrt\epsilon/\mathcal S$.
\end{theorem}
``` -/

theorem thm_app_phase_volterra_i
    [Countable ι] (m : RowModel ι) :
    ∃ Q : ℝ → ℝ, IsVolterraSol m Q ∧
      ∀ Q' : ℝ → ℝ, IsVolterraSol m Q' → ∀ s ∈ Ici (0 : ℝ), Q' s = Q s := by
  have hkb := aux_kbar_nonneg_tail m
  have hK := lem_app_phase_kernel_i m
  have hF0pos := m.F0_pos
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ r ^ 2 = m.kbar * r + m.F0 := by
    have hw := Real.sq_sqrt (show 0 ≤ m.kbar ^ 2 + 4 * m.F0 by positivity)
    have hw0 := Real.sqrt_nonneg (m.kbar ^ 2 + 4 * m.F0)
    refine ⟨(m.kbar + Real.sqrt (m.kbar ^ 2 + 4 * m.F0)) / 2, by positivity, ?_⟩
    linear_combination (1 / 4) * hw
  have hclamp : Continuous fun s : ℝ => max s 0 := continuous_id.max continuous_const
  have hsqb : ∀ (g : ℝ → ℝ), (∀ s, g s ≤ r ^ 2) → ∀ s, |Real.sqrt (g s)| ≤ r := fun g hgr s => by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (g s) ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt (hgr s)
      _ = r := Real.sqrt_sq hr0
  obtain ⟨Q, hQ0, hQs⟩ : ∃ Q : ℕ → ℝ → ℝ, Q 0 = (fun s => m.forcing (max s 0)) ∧
      ∀ n, Q (n + 1) = fun s => m.forcing (max s 0) +
        oneSidedConv (fun u => Real.sqrt (Q n u)) m.kernel (max s 0) :=
    ⟨fun n => Nat.rec (fun s => m.forcing (max s 0))
      (fun _ qn s => m.forcing (max s 0) + oneSidedConv (fun u => Real.sqrt (qn u)) m.kernel (max s 0)) n,
      rfl, fun n => rfl⟩
  have hFle : ∀ s, m.forcing (max s 0) ≤ m.F0 := fun s => by
    rw [← hK.2.2.1]
    exact hK.2.1.antitoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (le_max_right s 0))
      (le_max_right s 0)
  have hinv : ∀ n, Continuous (Q n) ∧ ∀ s, 0 ≤ Q n s ∧ Q n s ≤ r ^ 2 := by
    intro n
    induction n with
    | zero =>
      rw [hQ0]
      refine ⟨hK.1.comp_continuous hclamp (fun s => le_max_right s 0), fun s => ⟨?_, ?_⟩⟩
      · exact (hK.2.2.2.1 _ (Set.mem_Ici.2 (le_max_right s 0))).le
      · have := hFle s
        nlinarith [mul_nonneg hkb hr0]
    | succ n ih =>
      have h := aux_step m hr0 hr ih.1 (fun s => (ih.2 s).1) (fun s => (ih.2 s).2)
      rw [hQs n]
      refine ⟨h.1, fun s => ⟨?_, (h.2 s).2⟩⟩
      exact (hK.2.2.2.1 _ (Set.mem_Ici.2 (le_max_right s 0))).le.trans (h.2 s).1
  have hmono : ∀ n s, Q n s ≤ Q (n + 1) s := by
    intro n
    induction n with
    | zero =>
      intro s
      have h := aux_step m hr0 hr (hinv 0).1 (fun s => ((hinv 0).2 s).1) (fun s => ((hinv 0).2 s).2)
      exact (congrFun hQ0 s).le.trans ((h.2 s).1.trans (congrFun (hQs 0) s).symm.le)
    | succ n ih =>
      intro s
      exact (congrFun (hQs n) s).le.trans
        ((aux_step_mono m hr0 (hinv n).1 (hinv (n + 1)).1 (fun s => ((hinv n).2 s).1)
          (fun s => ((hinv (n + 1)).2 s).1) (fun s => ((hinv n).2 s).2)
          (fun s => ((hinv (n + 1)).2 s).2) ih s).trans (congrFun (hQs (n + 1)) s).symm.le)
  have hbdd : ∀ s, BddAbove (Set.range fun n => Q n s) := fun s =>
    ⟨r ^ 2, by rintro _ ⟨n, rfl⟩; exact ((hinv n).2 s).2⟩
  obtain ⟨Qi, hQi⟩ : ∃ Qi : ℝ → ℝ, ∀ s, Qi s = ⨆ n, Q n s := ⟨_, fun _ => rfl⟩
  have hlim : ∀ s, Tendsto (fun n => Q n s) atTop (𝓝 (Qi s)) := fun s => by
    rw [hQi]
    exact tendsto_atTop_ciSup (monotone_nat_of_le_succ (fun n => hmono n s)) (hbdd s)
  have hQi0 : ∀ s, 0 ≤ Qi s := fun s => by
    rw [hQi]; exact ((hinv 0).2 s).1.trans (le_ciSup (hbdd s) 0)
  have hQir : ∀ s, Qi s ≤ r ^ 2 := fun s => by
    rw [hQi]; exact ciSup_le (fun n => ((hinv n).2 s).2)
  have hQipos : ∀ s, 0 < Qi s := fun s => by
    rw [hQi]
    refine lt_of_lt_of_le ?_ (le_ciSup (hbdd s) 0)
    rw [hQ0]
    exact hK.2.2.2.1 _ (Set.mem_Ici.2 (le_max_right s 0))
  have hQim : Measurable Qi :=
    measurable_of_tendsto_metrizable (fun n => (hinv n).1.measurable) (tendsto_pi_nhds.2 hlim)
  have hsqm : Measurable fun u => Real.sqrt (Qi u) := hQim.sqrt
  have hconv_lim : ∀ s : ℝ, 0 ≤ s → Tendsto
      (fun n => oneSidedConv (fun u => Real.sqrt (Q n u)) m.kernel s) atTop
      (𝓝 (oneSidedConv (fun u => Real.sqrt (Qi u)) m.kernel s)) := by
    intro s hs
    have hKint : IntegrableOn m.kernel (Ioi 0) := (lem_app_phase_kernel_ii m).1
    have hKI : IntervalIntegrable m.kernel volume 0 s :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hs).2 (hKint.mono_set Ioc_subset_Ioi_self)
    unfold oneSidedConv
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun x => r * m.kernel x) (Filter.Eventually.of_forall (fun n => ?_))
      (Filter.Eventually.of_forall (fun n => Filter.Eventually.of_forall (fun x _ => ?_)))
      (hKI.const_mul r) (Filter.Eventually.of_forall (fun x _ => ?_))
    · exact (aux_conv_intble m (Real.continuous_sqrt.comp (hinv n).1).measurable
        (hsqb (Q n) (fun s => ((hinv n).2 s).2)) hs).def'.aestronglyMeasurable
    · rw [norm_mul, Real.norm_of_nonneg (aux_kernel_nonneg_tail m x), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hsqb (Q n) (fun s => ((hinv n).2 s).2) _)
        (aux_kernel_nonneg_tail m x)
    · exact ((Real.continuous_sqrt.tendsto _).comp (hlim (s - x))).mul_const _
  have heq : ∀ s ∈ Ici (0 : ℝ), Qi s = m.forcing s + oneSidedConv (fun u => Real.sqrt (Qi u)) m.kernel s := by
    intro s hs
    have hs0 : 0 ≤ s := hs
    have h1 : Tendsto (fun n => Q (n + 1) s) atTop (𝓝 (Qi s)) :=
      (hlim s).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => Q (n + 1) s) atTop
        (𝓝 (m.forcing s + oneSidedConv (fun u => Real.sqrt (Qi u)) m.kernel s)) := by
      refine (tendsto_congr (fun n => ?_)).2 ((hconv_lim s hs0).const_add (m.forcing s))
      rw [congrFun (hQs n) s]
      simp only [max_eq_left hs0]
    exact tendsto_nhds_unique h1 h2
  have hsolQ : IsVolterraSol m Qi := by
    refine ⟨?_, fun s _ => hQi0 s, heq⟩
    exact (hK.1.add (aux_conv_contOn_Ici m hsqm (hsqb Qi hQir))).congr (fun s hs => heq s hs)
  refine ⟨Qi, hsolQ, fun Q' hQ' s hs => ?_⟩
  have restrict : ∀ P : ℝ → ℝ, IsVolterraSol m P → IsVolterraSolOn m (s + 1) P := fun P hP =>
    ⟨hP.1.mono Icc_subset_Ici_self, fun t ht => hP.2.1 t (Set.mem_Ici.2 ht.1),
      fun t ht => hP.2.2 t (Set.mem_Ici.2 ht.1)⟩
  exact thm_app_phase_volterra_ii m (s + 1) (by have : 0 ≤ s := hs; linarith) Q' Qi
    (restrict Q' hQ') (restrict Qi hsolQ) s ⟨hs, by linarith⟩

/-- `thm:app-phase-volterra`, part (iii) of 5: bounds, snapshot `cr-2026-10-23`.
Bounds `0 < F(s) ≤ Q(s) ≤ M` for every solution, with `M = ((k̄ + √(k̄² + 4F_0))/2)²`.
Source: `section.tex` l.303–315.

LaTeX (verbatim, `section.tex` l.303–315):
```
\begin{theorem}[Existence, uniqueness and floor]\label{thm:app-phase-volterra}
Assume (M1). The Volterra equation \cref{eqn:app-phase-volterra} has a unique solution
$Q$ on $[0,\infty)$. It satisfies
\begin{equation}\label{eqn:app-phase-Mbound}
0<F(s)\le Q(s)\le M\defeq\Big(\frac{\bar k+\sqrt{\bar k^2+4F_0}}2\Big)^2\qquad(s\ge0),
\end{equation}
and
\[
\lim_{s\to\infty}Q(s)=\bar k^2=\frac{\lr^2\mathcal S^2}4 .
\]
If $\mathcal S>0$ and $\epsilon>0$, the unique step $\lr>0$ with floor
$\lr^2\mathcal S^2/4=\epsilon$ is $\lr=2\sqrt\epsilon/\mathcal S$.
\end{theorem}
``` -/

theorem thm_app_phase_volterra_iii
    [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q) :
    ∀ s ∈ Ici (0 : ℝ), 0 < m.forcing s ∧ m.forcing s ≤ Q s ∧
      Q s ≤ ((m.kbar + Real.sqrt (m.kbar ^ 2 + 4 * m.F0)) / 2) ^ 2 := by
  have hK := lem_app_phase_kernel_i m
  have hKii := lem_app_phase_kernel_ii m
  have hkb := aux_kbar_nonneg_tail m
  have hF0 : 0 < m.F0 := m.F0_pos
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = (m.kbar + Real.sqrt (m.kbar ^ 2 + 4 * m.F0)) / 2 := ⟨_, rfl⟩
  rw [← hrdef]
  have hsq : 0 < Real.sqrt (m.kbar ^ 2 + 4 * m.F0) :=
    Real.sqrt_pos.2 (by nlinarith [sq_nonneg m.kbar])
  have hr0 : 0 ≤ r := by rw [hrdef]; linarith
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hr : r ^ 2 = m.kbar * r + m.F0 := by
    have hw := Real.sq_sqrt (show 0 ≤ m.kbar ^ 2 + 4 * m.F0 by nlinarith [sq_nonneg m.kbar])
    rw [hrdef]
    linear_combination (1 / 4) * hw
  have hFle : ∀ t : ℝ, 0 ≤ t → m.forcing t ≤ m.F0 := fun t ht => by
    rw [← hK.2.2.1]
    exact hK.2.1.antitoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  intro s hs
  have hs0 : (0 : ℝ) ≤ s := hs
  refine ⟨hK.2.2.2.1 s hs, ?_, ?_⟩
  · have hEq := hQ.2.2 s hs
    have hconv : 0 ≤ oneSidedConv (fun u => Real.sqrt (Q u)) m.kernel s := by
      unfold oneSidedConv
      exact intervalIntegral.integral_nonneg hs0
        (fun x _ => mul_nonneg (Real.sqrt_nonneg _) (aux_kernel_nonneg_tail m x))
    linarith
  · have hkc_int : IntegrableOn m.kernel (Ioo 0 (s + 1)) := hKii.1.mono_set Ioo_subset_Ioi_self
    have hkc_nonneg : ∀ t ∈ Ioo (0 : ℝ) (s + 1), 0 ≤ m.kernel t :=
      fun t _ => aux_kernel_nonneg_tail m t
    have hG : ContinuousOn m.forcing (Icc 0 (s + 1)) := hK.1.mono Icc_subset_Ici_self
    have hG_nn : ∀ t ∈ Icc (0 : ℝ) (s + 1), 0 ≤ m.forcing t :=
      fun t ht => (hK.2.2.2.1 t (Set.mem_Ici.2 ht.1)).le
    have hx : ContinuousOn Q (Icc 0 (s + 1)) := hQ.1.mono Icc_subset_Ici_self
    have hx_nn : ∀ t ∈ Icc (0 : ℝ) (s + 1), 0 ≤ Q t :=
      fun t ht => hQ.2.1 t (Set.mem_Ici.2 ht.1)
    have hy : ContinuousOn (fun _ : ℝ => r ^ 2) (Icc 0 (s + 1)) := continuousOn_const
    have hy_nn : ∀ t ∈ Icc (0 : ℝ) (s + 1), 0 ≤ (fun _ : ℝ => r ^ 2) t :=
      fun t _ => (pow_pos hrpos 2).le
    have hym : ∀ t ∈ Icc (0 : ℝ) (s + 1), r ^ 2 ≤ (fun _ : ℝ => r ^ 2) t :=
      fun t _ => le_rfl
    have hxsub : ∀ t ∈ Icc (0 : ℝ) (s + 1),
        Q t ≤ m.forcing t + oneSidedConv (fun u => Real.sqrt (Q u)) m.kernel t :=
      fun t ht => le_of_eq (hQ.2.2 t (Set.mem_Ici.2 ht.1))
    have hysub : ∀ t ∈ Icc (0 : ℝ) (s + 1),
        m.forcing t + oneSidedConv (fun u => Real.sqrt ((fun _ : ℝ => r ^ 2) u)) m.kernel t
          ≤ r ^ 2 := by
      intro t ht
      have hfun : (fun u => Real.sqrt ((fun _ : ℝ => r ^ 2) u)) = fun _ : ℝ => r := by
        funext u
        exact Real.sqrt_sq hr0
      have hc : oneSidedConv (fun u => Real.sqrt ((fun _ : ℝ => r ^ 2) u)) m.kernel t
          ≤ m.kbar * r := by
        rw [hfun]
        exact (le_abs_self _).trans
          (aux_conv_abs_le m (fun _ : ℝ => r) measurable_const r
            (fun _ _ => (abs_of_nonneg hr0).le) t ht.1)
      have hf := hFle t ht.1
      linarith
    exact lem_app_phase_comparison (s + 1) (by linarith) m.kernel hkc_nonneg hkc_int
      m.forcing hG hG_nn (r ^ 2) (pow_pos hrpos 2) Q (fun _ => r ^ 2) hx hx_nn hy hy_nn hym
      hxsub hysub s ⟨hs0, by linarith⟩

/-- Private: the ODE comparison `z' = -b z + c g ≥ -b z + c √z` gives
`√z(s) ≥ c/b + (√z(1) - c/b) e^{-b(s-1)/2}` for `s ≥ 1`. -/
lemma aux_ode_sqrt {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (g z : ℝ → ℝ)
    (hz : ∀ s : ℝ, 0 < s → HasDerivAt z (-b * z s + c * g s) s)
    (hzpos : ∀ s : ℝ, 0 < s → 0 < z s)
    (hgz : ∀ s : ℝ, 0 < s → Real.sqrt (z s) ≤ g s) (s : ℝ) (hs : 1 ≤ s) :
    c / b + (Real.sqrt (z 1) - c / b) * Real.exp (-(b / 2 * (s - 1))) ≤ Real.sqrt (z s) := by
  set u : ℝ → ℝ := fun t => Real.exp (b / 2 * t) * (Real.sqrt (z t) - c / b) with hu
  have hder : ∀ t : ℝ, 0 < t → HasDerivAt u
      (Real.exp (b / 2 * t) * (b / 2 * (Real.sqrt (z t) - c / b)) +
        Real.exp (b / 2 * t) * ((-b * z t + c * g t) / (2 * Real.sqrt (z t)))) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (b / 2 * t)) (Real.exp (b / 2 * t) * (b / 2)) t := by
      simpa using ((hasDerivAt_id t).const_mul (b / 2)).exp
    have h2 : HasDerivAt (fun t => Real.sqrt (z t) - c / b)
        ((-b * z t + c * g t) / (2 * Real.sqrt (z t))) t :=
      ((hz t ht).sqrt (hzpos t ht).ne').sub_const _
    have := h1.mul h2
    convert this using 1
    ring
  have hnn : ∀ t : ℝ, 0 < t → 0 ≤ deriv u t := by
    intro t ht
    rw [(hder t ht).deriv]
    have hr := Real.sqrt_pos.2 (hzpos t ht)
    have hsq := Real.sq_sqrt (hzpos t ht).le
    have hg := hgz t ht
    have hE := Real.exp_pos (b / 2 * t)
    have : 0 ≤ (b / 2 * (Real.sqrt (z t) - c / b)) +
        ((-b * z t + c * g t) / (2 * Real.sqrt (z t))) := by
      have e : (b / 2 * (Real.sqrt (z t) - c / b)) +
          ((-b * z t + c * g t) / (2 * Real.sqrt (z t))) =
          (c * (g t - Real.sqrt (z t))) / (2 * Real.sqrt (z t)) := by
        generalize Real.sqrt (z t) = r at hr hsq ⊢
        rw [← hsq]
        field_simp
        ring
      rw [e]
      exact div_nonneg (mul_nonneg hc.le (sub_nonneg.2 hg)) (by positivity)
    nlinarith [mul_nonneg hE.le this]
  have hmono : MonotoneOn u (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro t ht
      exact (hder t (by linarith [Set.mem_Ici.1 ht])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hder t (by linarith [Set.mem_Ioi.1 ht])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact hnn t (by linarith [Set.mem_Ioi.1 ht])
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs) hs
  simp only [hu] at h
  have hE : Real.exp (b / 2 * s) * Real.exp (-(b / 2 * (s - 1))) = Real.exp (b / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hEp := Real.exp_pos (b / 2 * s)
  have h1 : Real.exp (b / 2 * s) * ((Real.sqrt (z 1) - c / b) * Real.exp (-(b / 2 * (s - 1))))
      ≤ Real.exp (b / 2 * s) * (Real.sqrt (z s) - c / b) := by
    have : Real.exp (b / 2 * s) * ((Real.sqrt (z 1) - c / b) * Real.exp (-(b / 2 * (s - 1))))
        = Real.exp (b / 2 * 1) * (Real.sqrt (z 1) - c / b) := by
      rw [show Real.exp (b / 2 * s) * ((Real.sqrt (z 1) - c / b) * Real.exp (-(b / 2 * (s - 1))))
        = (Real.exp (b / 2 * s) * Real.exp (-(b / 2 * (s - 1)))) * (Real.sqrt (z 1) - c / b) by ring,
        hE]
      simp
    rw [this]; exact h
  have := le_of_mul_le_mul_left h1 hEp
  linarith

/-- Private: positivity of the liminf when `k̄ > 0` (`section.tex` l.345–362, the ODE step). -/
lemma aux_liminf_pos [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ)
    (hQ : IsVolterraSol m Q) (hk : 0 < m.kbar) : 0 < Filter.liminf Q atTop := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, 0 < m.v j := by
    by_contra hcon
    push_neg at hcon
    have h0 : ∀ i, m.v i = 0 := fun i => le_antisymm (hcon i) (m.v_nonneg i)
    have : m.kbar = 0 := by
      unfold RowModel.kbar RowModel.S
      simp [h0]
    linarith
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = 2 * m.d j := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = m.η / 2 * (m.μ j * m.v j) := ⟨_, rfl⟩
  have hdj := m.d_pos j
  have hb : 0 < b := by rw [hbdef]; positivity
  have hc : 0 < c := by
    have := m.η_pos; have := m.μ_pos j
    rw [hcdef]; positivity
  have hker : ∀ x : ℝ, 0 < x → c * Real.exp (-(b * x)) ≤ m.kernel x := by
    intro x hx
    have hnn : ∀ i, 0 ≤ m.μ i * m.v i * Real.exp (-(2 * m.d i * x)) := fun i =>
      mul_nonneg (mul_nonneg (m.μ_pos i).le (m.v_nonneg i)) (Real.exp_pos _).le
    have hsum : Summable (fun i => m.μ i * m.v i * Real.exp (-(2 * m.d i * x))) := by
      refine Summable.of_nonneg_of_le hnn (fun i => ?_)
        (m.summable_S.mul_right (1 / (Real.exp 1 * x)))
      have hd := m.d_pos i
      have h1 := aux_mul_exp_neg_le (b := 2 * m.d i) (by positivity) hx
      have hμv : 0 ≤ m.μ i * m.v i := mul_nonneg (m.μ_pos i).le (m.v_nonneg i)
      calc m.μ i * m.v i * Real.exp (-(2 * m.d i * x))
          = (m.μ i * m.v i / (2 * m.d i)) * (2 * m.d i * Real.exp (-(2 * m.d i * x))) := by
            field_simp
        _ ≤ m.μ i * m.v i / (2 * m.d i) * (1 / (Real.exp 1 * x)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    have hle := hsum.le_tsum j (fun i _ => hnn i)
    unfold RowModel.kernel
    have hη := m.η_pos
    calc c * Real.exp (-(b * x))
        = m.η / 2 * (m.μ j * m.v j * Real.exp (-(2 * m.d j * x))) := by
          rw [hcdef, hbdef]; ring
      _ ≤ m.η / 2 * ∑' i, m.μ i * m.v i * Real.exp (-(2 * m.d i * x)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
  have hK := lem_app_phase_kernel_i m
  have hIII := thm_app_phase_volterra_iii m Q hQ
  have hQpos : ∀ s ∈ Ici (0 : ℝ), 0 < Q s := fun s hs =>
    (hIII s hs).1.trans_le (hIII s hs).2.1
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (m.kbar + Real.sqrt (m.kbar ^ 2 + 4 * m.F0)) / 2 :=
    ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    have := Real.sqrt_nonneg (m.kbar ^ 2 + 4 * m.F0)
    rw [hR]; linarith
  have hQle : ∀ s ∈ Ici (0 : ℝ), Q s ≤ R ^ 2 := fun s hs => by
    rw [hR]; exact (hIII s hs).2.2
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ, g = fun u => Real.sqrt (Q u) := ⟨_, rfl⟩
  have hgc : ContinuousOn g (Ici 0) := by
    rw [hgdef]; exact Real.continuous_sqrt.comp_continuousOn hQ.1
  have hgpos : ∀ s ∈ Ici (0 : ℝ), 0 < g s := fun s hs => by
    rw [hgdef]; exact Real.sqrt_pos.2 (hQpos s hs)
  have hgb : ∀ s ∈ Ici (0 : ℝ), |g s| ≤ R := fun s hs => by
    rw [hgdef]
    show |Real.sqrt (Q s)| ≤ R
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (Q s) ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt (hQle s hs)
      _ = R := Real.sqrt_sq hR0
  obtain ⟨gp, hgpdef⟩ : ∃ gp : ℝ → ℝ,
      gp = (Ici (0 : ℝ)).piecewise g (fun _ => 0) := ⟨_, rfl⟩
  have hgpm : Measurable gp := by
    rw [hgpdef]
    exact ContinuousOn.measurable_piecewise hgc continuousOn_const measurableSet_Ici
  have hgp : ∀ s ∈ Ici (0 : ℝ), gp s = g s := fun s hs => by
    rw [hgpdef]; exact Set.piecewise_eq_of_mem _ _ _ hs
  have hgpb : ∀ s, |gp s| ≤ R := fun s => by
    by_cases hs : s ∈ Ici (0 : ℝ)
    · rw [hgp s hs]; exact hgb s hs
    · rw [hgpdef, Set.piecewise_eq_of_notMem _ _ _ hs]; simpa using hR0
  -- the auxiliary function
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, G = fun s => ∫ v in (0 : ℝ)..s, Real.exp (b * v) * g v :=
    ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ → ℝ, z = fun s => c * (Real.exp (-(b * s)) * G s) := ⟨_, rfl⟩
  have hint : ∀ s : ℝ, 0 ≤ s → IntervalIntegrable (fun v => Real.exp (b * v) * g v) volume 0 s :=
    fun s hs => by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hs]
      exact (by fun_prop : Continuous fun v : ℝ => Real.exp (b * v)).continuousOn.mul
        (hgc.mono (fun v hv => hv.1))
  have hGpos : ∀ s : ℝ, 0 < s → 0 < G s := fun s hs => by
    rw [hGdef]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (hint s hs.le) (fun v hv =>
      mul_pos (Real.exp_pos _) (hgpos v (Set.mem_Ici.2 hv.1.le))) hs
  have hzpos : ∀ s : ℝ, 0 < s → 0 < z s := fun s hs => by
    rw [hzdef]; exact mul_pos hc (mul_pos (Real.exp_pos _) (hGpos s hs))
  have hzeq : ∀ s : ℝ, z s = c * ∫ x in (0 : ℝ)..s, g (s - x) * Real.exp (-(b * x)) := by
    intro s
    have e1 : (∫ x in (0 : ℝ)..s, g (s - x) * Real.exp (-(b * x)))
        = ∫ x in (0 : ℝ)..s, (fun y => g y * Real.exp (-(b * (s - y)))) (s - x) := by
      congr 1; funext x; simp
    rw [e1, intervalIntegral.integral_comp_sub_left (fun y => g y * Real.exp (-(b * (s - y)))) s]
    simp only [sub_self, sub_zero]
    have e2 : (∫ y in (0 : ℝ)..s, g y * Real.exp (-(b * (s - y))))
        = Real.exp (-(b * s)) * ∫ v in (0 : ℝ)..s, Real.exp (b * v) * g v := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext y
      rw [show -(b * (s - y)) = -(b * s) + b * y by ring, Real.exp_add]; ring
    rw [e2, hzdef, hGdef]
  have hzle : ∀ s : ℝ, 0 ≤ s → z s ≤ Q s := by
    intro s hs
    rcases hs.eq_or_lt with h0 | hspos
    · subst h0
      rw [hzdef, hGdef]; simp only [intervalIntegral.integral_same, mul_zero]
      exact (hQpos 0 (Set.mem_Ici.2 le_rfl)).le
    · have hE := hQ.2.2 s (Set.mem_Ici.2 hs)
      have hFp := (hIII s (Set.mem_Ici.2 hs)).1
      have hconv : (fun x => g (s - x) * (c * Real.exp (-(b * x)))) =
          fun x => c * (g (s - x) * Real.exp (-(b * x))) := by funext x; ring
      have hI1 : IntervalIntegrable (fun x => g (s - x) * (c * Real.exp (-(b * x)))) volume 0 s := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hs]
        refine ContinuousOn.mul ?_ (by fun_prop : Continuous fun x : ℝ => c * Real.exp (-(b * x))).continuousOn
        exact hgc.comp (by fun_prop : Continuous fun x : ℝ => s - x).continuousOn
          (fun x hx => Set.mem_Ici.2 (by linarith [hx.2]))
      have hI2 : IntervalIntegrable (fun x => gp (s - x) * m.kernel x) volume 0 s :=
        aux_conv_intble m hgpm hgpb hs
      have hle : (∫ x in (0 : ℝ)..s, g (s - x) * (c * Real.exp (-(b * x)))) ≤
          ∫ x in (0 : ℝ)..s, gp (s - x) * m.kernel x := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hs hI1 hI2
        intro x hx
        rw [hgp (s - x) (Set.mem_Ici.2 (by linarith [hx.2]))]
        exact mul_le_mul_of_nonneg_left (hker x hx.1)
          (hgpos (s - x) (Set.mem_Ici.2 (by linarith [hx.2]))).le
      have hcv : oneSidedConv (fun u => Real.sqrt (Q u)) m.kernel s =
          ∫ x in (0 : ℝ)..s, gp (s - x) * m.kernel x := by
        unfold oneSidedConv
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hs] at hx
        show Real.sqrt (Q (s - x)) * m.kernel x = gp (s - x) * m.kernel x
        rw [hgp (s - x) (Set.mem_Ici.2 (by linarith [hx.2])), hgdef]
      rw [hzeq s, hE, hcv]
      rw [hconv, intervalIntegral.integral_const_mul] at hle
      linarith
  -- derivative of z
  have hzder : ∀ s : ℝ, 0 < s → HasDerivAt z (-b * z s + c * g s) s := by
    intro s hs
    have hcont : ContinuousAt (fun v => Real.exp (b * v) * g v) s := by
      have : ContinuousAt g s := hgc.continuousAt (Ici_mem_nhds hs)
      exact (by fun_prop : Continuous fun v : ℝ => Real.exp (b * v)).continuousAt.mul this
    have hmeas : StronglyMeasurableAtFilter (fun v => Real.exp (b * v) * g v) (𝓝 s) := by
      refine ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi ?_ s hs
      exact (by fun_prop : Continuous fun v : ℝ => Real.exp (b * v)).continuousOn.mul
        (hgc.mono (fun v hv => Set.mem_Ici.2 (le_of_lt hv)))
    have hG : HasDerivAt G (Real.exp (b * s) * g s) s := by
      rw [hGdef]
      exact intervalIntegral.integral_hasDerivAt_right (hint s hs.le) hmeas hcont
    have hE : HasDerivAt (fun t : ℝ => Real.exp (-(b * t))) (Real.exp (-(b * s)) * (-b)) s := by
      simpa using (((hasDerivAt_id s).const_mul b).neg).exp
    have := (hE.mul hG).const_mul c
    rw [hzdef]
    convert this using 1
    have h1 : Real.exp (-(b * s)) * Real.exp (b * s) = 1 := by
      rw [← Real.exp_add]; simp
    simp only [hzdef]
    linear_combination (-(c * g s)) * h1
  have hgz : ∀ s : ℝ, 0 < s → Real.sqrt (z s) ≤ g s := fun s hs => by
    rw [hgdef]
    exact Real.sqrt_le_sqrt (hzle s hs.le)
  have hode := aux_ode_sqrt hb hc g z hzder hzpos hgz
  -- conclude
  have hA : Tendsto (fun s : ℝ => (Real.sqrt (z 1) - c / b) * Real.exp (-(b / 2 * (s - 1))))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => -(b / 2 * (s - 1))) atTop atBot := by
      apply tendsto_neg_atTop_atBot.comp
      apply Filter.Tendsto.const_mul_atTop (by positivity)
      exact tendsto_atTop_add_const_right _ _ tendsto_id
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (Real.sqrt (z 1) - c / b)
  have hcb : 0 < c / b := div_pos hc hb
  have hev : ∀ᶠ s in atTop, c / (2 * b) ≤ Real.sqrt (z s) := by
    filter_upwards [hA.eventually (lt_mem_nhds (show -(c / (2 * b)) < 0 by
      have : 0 < c / (2 * b) := by positivity
      linarith)), eventually_ge_atTop (1 : ℝ)] with s hs1 hs2
    have := hode s hs2
    have e : c / (2 * b) = c / b - c / (2 * b) := by field_simp; ring
    linarith
  have hQup : IsBoundedUnder (· ≤ ·) atTop Q :=
    isBoundedUnder_of_eventually_le (a := R ^ 2) (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      exact hQle s hs)
  have hlow : ∀ᶠ s in atTop, (c / (2 * b)) ^ 2 ≤ Q s := by
    filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with s hs1 hs2
    have hzs := hzpos s (by linarith)
    have h0 : 0 ≤ c / (2 * b) := by positivity
    calc (c / (2 * b)) ^ 2 ≤ Real.sqrt (z s) ^ 2 := by gcongr
      _ = z s := Real.sq_sqrt hzs.le
      _ ≤ Q s := hzle s (by linarith)
  have := Filter.le_liminf_of_le hQup.isCoboundedUnder_ge hlow
  have hp : 0 < (c / (2 * b)) ^ 2 := by positivity
  linarith

/-- Private: the limit of a solution, given the positivity `liminf Q > 0` when `k̄ > 0`
(`section.tex` l.345–362, the ODE step, is the one input not proved here). -/
lemma aux_limit_of_pos [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ)
    (hQ : IsVolterraSol m Q) (hpos : 0 < m.kbar → 0 < Filter.liminf Q atTop) :
    Tendsto Q atTop (𝓝 (m.kbar ^ 2)) := by
  classical
  have hK := lem_app_phase_kernel_i m
  have hF : Tendsto m.forcing atTop (𝓝 0) := hK.2.2.2.2
  have hkb := aux_kbar_nonneg_tail m
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (m.kbar + Real.sqrt (m.kbar ^ 2 + 4 * m.F0)) / 2 :=
    ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    have := Real.sqrt_nonneg (m.kbar ^ 2 + 4 * m.F0)
    rw [hR]; linarith
  have hQle : ∀ s ∈ Ici (0 : ℝ), Q s ≤ R ^ 2 := by
    intro s hs
    rw [hR]
    exact (thm_app_phase_volterra_iii m Q hQ s hs).2.2
  have hQnn : ∀ s ∈ Ici (0 : ℝ), 0 ≤ Q s := hQ.2.1
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ,
      g = (Ici (0 : ℝ)).piecewise (fun u => Real.sqrt (Q u)) (fun _ => 0) := ⟨_, rfl⟩
  have hgm : Measurable g := by
    rw [hgdef]
    exact ContinuousOn.measurable_piecewise (Real.continuous_sqrt.comp_continuousOn hQ.1)
      continuousOn_const measurableSet_Ici
  have hg : ∀ s ∈ Ici (0 : ℝ), g s = Real.sqrt (Q s) := fun s hs => by
    rw [hgdef]; exact Set.piecewise_eq_of_mem _ _ _ hs
  have hgnn : ∀ s ∈ Ici (0 : ℝ), 0 ≤ g s := fun s hs => by
    rw [hg s hs]; exact Real.sqrt_nonneg _
  have hgb : ∀ s ∈ Ici (0 : ℝ), |g s| ≤ R := fun s hs => by
    rw [hg s hs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (Q s) ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt (hQle s hs)
      _ = R := Real.sqrt_sq hR0
  have hconv : ∀ t : ℝ, 0 ≤ t → oneSidedConv g m.kernel t = Q t - m.forcing t := by
    intro t ht
    have hE := hQ.2.2 t (Set.mem_Ici.2 ht)
    have hc : oneSidedConv g m.kernel t = oneSidedConv (fun u => Real.sqrt (Q u)) m.kernel t := by
      unfold oneSidedConv
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le ht] at hx
      show g (t - x) * m.kernel x = Real.sqrt (Q (t - x)) * m.kernel x
      rw [hg (t - x) (Set.mem_Ici.2 (by linarith [hx.2]))]
    linarith
  have hcb : ∀ t ∈ Ici (0 : ℝ), |oneSidedConv g m.kernel t| ≤ m.kbar * R :=
    fun t ht => aux_conv_abs_le m g hgm R hgb t ht
  have hcup : IsBoundedUnder (· ≤ ·) atTop (oneSidedConv g m.kernel) :=
    isBoundedUnder_of_eventually_le (a := m.kbar * R) (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact (abs_le.1 (hcb t (Set.mem_Ici.2 ht))).2)
  have hclo : IsBoundedUnder (· ≥ ·) atTop (oneSidedConv g m.kernel) :=
    isBoundedUnder_of_eventually_ge (a := -(m.kbar * R)) (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact (abs_le.1 (hcb t (Set.mem_Ici.2 ht))).1)
  have hQup : IsBoundedUnder (· ≤ ·) atTop Q :=
    isBoundedUnder_of_eventually_le (a := R ^ 2) (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      exact hQle s hs)
  have hQlo : IsBoundedUnder (· ≥ ·) atTop Q :=
    isBoundedUnder_of_eventually_ge (a := 0) (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      exact hQnn s hs)
  have hQeq : (oneSidedConv g m.kernel + m.forcing) =ᶠ[atTop] Q := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Pi.add_apply, hconv t ht]; ring
  obtain ⟨hliminf_eq, hlimsup_eq⟩ :=
    aux_liminf_limsup_add_zero (oneSidedConv g m.kernel) m.forcing hF hcup hclo
  have hLconv : Filter.liminf (oneSidedConv g m.kernel) atTop = Filter.liminf Q atTop := by
    rw [← hliminf_eq]; exact Filter.liminf_congr hQeq
  have hUconv : Filter.limsup (oneSidedConv g m.kernel) atTop = Filter.limsup Q atTop := by
    rw [← hlimsup_eq]; exact Filter.limsup_congr hQeq
  have hmono : Monotone Real.sqrt := fun a b hab => Real.sqrt_le_sqrt hab
  have hcont : ContinuousAt Real.sqrt (Filter.liminf Q atTop) :=
    Real.continuous_sqrt.continuousAt
  have hcont' : ContinuousAt Real.sqrt (Filter.limsup Q atTop) :=
    Real.continuous_sqrt.continuousAt
  have e1 := Monotone.map_liminf_of_continuousAt hmono Q hcont hQup.isCoboundedUnder_ge hQlo
  have e2 := Monotone.map_limsup_of_continuousAt hmono Q hcont' hQup hQlo.isCoboundedUnder_le
  have hLg : Filter.liminf g atTop = Real.sqrt (Filter.liminf Q atTop) := by
    rw [e1]
    exact Filter.liminf_congr (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hg t ht)
  have hUg : Filter.limsup g atTop = Real.sqrt (Filter.limsup Q atTop) := by
    rw [e2]
    exact Filter.limsup_congr (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hg t ht)
  obtain ⟨h1, -, h3⟩ := lem_app_phase_tail m g hgm hgnn ⟨R, hgb⟩
  rw [hLg, hLconv] at h1
  rw [hUg, hUconv] at h3
  have hL0 : 0 ≤ Filter.liminf Q atTop :=
    Filter.le_liminf_of_le hQup.isCoboundedUnder_ge (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs using hQnn s hs)
  have hLU : Filter.liminf Q atTop ≤ Filter.limsup Q atTop := Filter.liminf_le_limsup hQup hQlo
  have hU0 : 0 ≤ Filter.limsup Q atTop := hL0.trans hLU
  have hlow : m.kbar ^ 2 ≤ Filter.liminf Q atTop := by
    rcases hkb.eq_or_lt with h0 | hkpos
    · rw [← h0]; simpa using hL0
    · have hLpos := hpos hkpos
      have hs : 0 < Real.sqrt (Filter.liminf Q atTop) := Real.sqrt_pos.2 hLpos
      have hks : m.kbar ≤ Real.sqrt (Filter.liminf Q atTop) := by
        apply le_of_mul_le_mul_right _ hs
        rw [Real.mul_self_sqrt hL0]
        exact h1
      nlinarith [mul_le_mul hks hks hkb hs.le, Real.mul_self_sqrt hL0]
  have hup : Filter.limsup Q atTop ≤ m.kbar ^ 2 := by
    rcases (Real.sqrt_nonneg (Filter.limsup Q atTop)).eq_or_lt with h0 | hpos0
    · have h00 := Real.sq_sqrt hU0
      rw [← h0] at h00
      nlinarith [hkb, sq_nonneg m.kbar]
    · have htk : Real.sqrt (Filter.limsup Q atTop) ≤ m.kbar := by
        apply le_of_mul_le_mul_right _ hpos0
        rw [Real.mul_self_sqrt hU0]
        nlinarith [Real.sq_sqrt hU0, h3]
      nlinarith [mul_le_mul htk htk (Real.sqrt_nonneg _) hkb, Real.mul_self_sqrt hU0]
  exact tendsto_of_liminf_eq_limsup (le_antisymm (hLU.trans hup) hlow)
    (le_antisymm hup (hlow.trans hLU)) hQup hQlo

/-- `thm:app-phase-volterra`, part (iv) of 5: limit, snapshot `cr-2026-10-23`.
Limit `Q(s) → k̄² = η²𝒮²/4` as `s → ∞` for every solution.
Source: `section.tex` l.303–315.

LaTeX (verbatim, `section.tex` l.303–315):
```
\begin{theorem}[Existence, uniqueness and floor]\label{thm:app-phase-volterra}
Assume (M1). The Volterra equation \cref{eqn:app-phase-volterra} has a unique solution
$Q$ on $[0,\infty)$. It satisfies
\begin{equation}\label{eqn:app-phase-Mbound}
0<F(s)\le Q(s)\le M\defeq\Big(\frac{\bar k+\sqrt{\bar k^2+4F_0}}2\Big)^2\qquad(s\ge0),
\end{equation}
and
\[
\lim_{s\to\infty}Q(s)=\bar k^2=\frac{\lr^2\mathcal S^2}4 .
\]
If $\mathcal S>0$ and $\epsilon>0$, the unique step $\lr>0$ with floor
$\lr^2\mathcal S^2/4=\epsilon$ is $\lr=2\sqrt\epsilon/\mathcal S$.
\end{theorem}
``` -/

theorem thm_app_phase_volterra_iv
    [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q) :
    Tendsto Q atTop (𝓝 (m.kbar ^ 2)) ∧ m.kbar ^ 2 = m.η ^ 2 * m.S ^ 2 / 4 := by
  exact ⟨aux_limit_of_pos m Q hQ (aux_liminf_pos m Q hQ), by unfold RowModel.kbar; ring⟩

/-- `thm:app-phase-volterra`, part (v) of 5: floor and matched step, snapshot `cr-2026-10-23`.
If `𝒮 > 0` and `ε > 0`, the step `η' > 0` with floor `η'²𝒮²/4 = ε` is exactly `η' = 2√ε/𝒮`.
Source: `section.tex` l.303–315.

LaTeX (verbatim, `section.tex` l.303–315):
```
\begin{theorem}[Existence, uniqueness and floor]\label{thm:app-phase-volterra}
Assume (M1). The Volterra equation \cref{eqn:app-phase-volterra} has a unique solution
$Q$ on $[0,\infty)$. It satisfies
\begin{equation}\label{eqn:app-phase-Mbound}
0<F(s)\le Q(s)\le M\defeq\Big(\frac{\bar k+\sqrt{\bar k^2+4F_0}}2\Big)^2\qquad(s\ge0),
\end{equation}
and
\[
\lim_{s\to\infty}Q(s)=\bar k^2=\frac{\lr^2\mathcal S^2}4 .
\]
If $\mathcal S>0$ and $\epsilon>0$, the unique step $\lr>0$ with floor
$\lr^2\mathcal S^2/4=\epsilon$ is $\lr=2\sqrt\epsilon/\mathcal S$.
\end{theorem}
``` -/

theorem thm_app_phase_volterra_v
    [Countable ι] (m : RowModel ι) (ε : ℝ) (hε : 0 < ε) (hS : 0 < m.S) :
    ∀ η' : ℝ, 0 < η' → (η' ^ 2 * m.S ^ 2 / 4 = ε ↔ η' = 2 * Real.sqrt ε / m.S) := by
  intro η' hη'
  have hSne : m.S ≠ 0 := hS.ne'
  constructor
  · intro h
    have hsq : Real.sqrt ε = η' * m.S / 2 := by
      rw [← h, show η' ^ 2 * m.S ^ 2 / 4 = (η' * m.S / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rw [hsq]
    field_simp
  · intro h
    rw [h]
    have hsq := Real.sq_sqrt hε.le
    field_simp
    linear_combination (4 : ℝ) * hsq

end Muon.Phase

end

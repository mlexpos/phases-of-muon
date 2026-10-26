import Mathlib
import Muon.Phase.FirstHit
import Muon.Phase.Kernels
import Muon.Phase.Volterra
import Muon.Phase.PowerSums

/-!
# Appendix H: two-phase bounds, the S-GD kernel below the critical exponent, kernel templates

Task L-H.14. Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`,
l.3112–3420: `lem:app-phase-square-tail` (l.3112), `lem:app-phase-restart` (l.3142),
`lem:app-phase-twophase` (l.3187), `lem:app-phase-split` (l.3232),
`lem:app-phase-G-small` (l.3275), `lem:app-phase-templates` (l.3369).
Card: `sections/07-phase-comparison/CARD.md` §2, §3, §5 (L-H.14), §6.2.

Encoding decisions:
* The paper's one-sided convolution `g * h` is `oneSidedConv h g` (`Muon.Foundations`), as in
  `Muon.Phase.FirstHit` and `Muon.Phase.Volterra`.
* The tail weight `w` of `lem:app-phase-square-tail` is named `wt` here, because `w` is the
  mixture weight vector of `lem:app-phase-mixture` in the same file.
* The proof-local `G` of `lem:app-phase-square-tail` is `sqTailG` (pointwise in `u`).
* The S-GD dimensionless kernel `g_{s-SGD}` of `eqn:app-phase-kernels` is `sgdKernel`
  (new here: no Lean definition existed). The S-SVD kernel is `Muon.Phase.svdKernel`.
* The template display `eqn:app-phase-template` is `phaseTemplate`, on the domain `0 ≤ v ≤ U0`.
* The mixture setting of `lem:app-phase-twophase` and `lem:app-phase-restart` is restated
  hypothesis by hypothesis, as in `Muon.Phase.lem_app_phase_mixture`; `mixF`, `mixG`, `firstHit`
  are reused.
* `lem:app-phase-twophase`(b): "`û ≤ H`" is `firstHit Y (T ε) ≤ ENNReal.ofReal H`, since the
  hit is only known to be attained in part (c).
* `lem:app-phase-restart`: the `J̃`, `d̃` of the paper are `restartJ`, `restartD`.
* `lem:app-phase-templates`(iii),(iv): stated as written. CORRECTIONS #2 is pending (ruling
  Q5): the constants `4/π` in the second terms are not established by the proof (card §6.2).
* Templates (i)–(v) are separate declarations (one per part); (v) is written out because its
  bound holds for all `v ≥ 0`.
-/

set_option linter.style.longLine false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open Muon.Foundations

noncomputable section

namespace Muon.Phase

/-! ## Helpers -/

/-- The S-GD dimensionless kernel `g_{s-SGD} = (2(1-2/π)/N) L_{N,α,α} + (4/(π H_N(α))) L_{N,2α,α}`
(`eqn:app-phase-kernels`, second entry). Source: `section.tex` l.1138–1141. -/
def sgdKernel (α : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α u
    + 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α u

/-- The pointwise bound `G(u) = 2h(u) + w(u)²/√ε + 2w(u) + √ε` of `lem:app-phase-square-tail`
(a proof-local `\defeq` of the paper; the tail weight `w` is `wt` here). -/
def sqTailG (h wt : ℝ → ℝ) (ε u : ℝ) : ℝ :=
  2 * h u + wt u ^ 2 / Real.sqrt ε + 2 * wt u + Real.sqrt ε

/-- The template bound `g(v) ≤ K_f(1+v)^{-υ} + K_s N^{-q}((1+v)/N^q)^{-b}` for `0 ≤ v ≤ U0`
(`eqn:app-phase-template`). -/
def phaseTemplate (g : ℝ → ℝ) (N U0 q Kf Ks υ b : ℝ) : Prop :=
  ∀ v : ℝ, 0 ≤ v → v ≤ U0 →
    g v ≤ Kf * (1 + v) ^ (-υ) + Ks * N ^ (-q) * ((1 + v) / N ^ q) ^ (-b)

/-- `J̃ = ∫_{u_0}^∞ √f + (2/b_min) ε^{1/4} G_0^{1/2}` of `lem:app-phase-restart`, with
`G_0 = (g*√Y)(u_0)` passed as `G0`. -/
def restartJ (f : ℝ → ℝ) (bmin ε G0 u0 : ℝ) : ℝ :=
  (∫ u in Ioi u0, Real.sqrt (f u)) + (2 / bmin) * ε ^ (1 / 4 : ℝ) * Real.sqrt G0

/-- `d̃ = (2/b_min) √ε log(Y(u_0)/ε)` of `lem:app-phase-restart`. -/
def restartD (bmin ε Yu0 : ℝ) : ℝ := (2 / bmin) * Real.sqrt ε * Real.log (Yu0 / ε)

/-! ## Comparison with a tail term and restart -/

/-- Helper (P-H.14.P1): the one-sided convolution is linear in a constant factor of the kernel. -/
lemma sqt_osc_const_mul (F g : ℝ → ℝ) (c t : ℝ) :
    oneSidedConv F (fun s => c * g s) t = c * oneSidedConv F g t := by
  unfold oneSidedConv
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext s
  ring

/-- Helper (P-H.14.P1): convolution with a constant function. -/
lemma sqt_osc_const (c : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    oneSidedConv (fun _ => c) g t = c * ∫ s in (0:ℝ)..t, g s := by
  unfold oneSidedConv
  rw [← intervalIntegral.integral_const_mul]

/-- Helper (P-H.14.P1): integrability of the convolution integrand. -/
lemma sqt_int (F g : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) (hF : ContinuousOn F (Icc 0 t))
    (hg : IntervalIntegrable g volume 0 t) :
    IntervalIntegrable (fun s => F (t - s) * g s) volume 0 t := by
  have hc : ContinuousOn (fun s => F (t - s)) (uIcc 0 t) := by
    rw [uIcc_of_le ht]
    refine hF.comp (continuous_const.sub continuous_id).continuousOn ?_
    intro s hs
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  exact hg.continuousOn_mul hc

/-- Helper (P-H.14.P1): monotonicity of the one-sided convolution in its first argument. -/
lemma sqt_osc_mono (F1 F2 g : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) (hF1 : ContinuousOn F1 (Icc 0 t))
    (hF2 : ContinuousOn F2 (Icc 0 t)) (hg : IntervalIntegrable g volume 0 t)
    (hgn : ∀ s ∈ Icc (0:ℝ) t, 0 ≤ g s) (hle : ∀ x ∈ Icc (0:ℝ) t, F1 x ≤ F2 x) :
    oneSidedConv F1 g t ≤ oneSidedConv F2 g t := by
  unfold oneSidedConv
  refine intervalIntegral.integral_mono_on ht (sqt_int F1 g t ht hF1 hg)
    (sqt_int F2 g t ht hF2 hg) ?_
  intro s hs
  have hmem : t - s ∈ Icc (0:ℝ) t := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  exact mul_le_mul_of_nonneg_right (hle _ hmem) (hgn s hs)

/-- Helper (P-H.14.P1): additivity of the one-sided convolution in the first argument. -/
lemma sqt_osc_add (F1 F2 g : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) (hF1 : ContinuousOn F1 (Icc 0 t))
    (hF2 : ContinuousOn F2 (Icc 0 t)) (hg : IntervalIntegrable g volume 0 t) :
    oneSidedConv (fun u => F1 u + F2 u) g t = oneSidedConv F1 g t + oneSidedConv F2 g t := by
  unfold oneSidedConv
  rw [← intervalIntegral.integral_add (sqt_int F1 g t ht hF1 hg) (sqt_int F2 g t ht hF2 hg)]
  congr 1
  funext s
  dsimp only
  ring

/-- Helper (P-H.14.P1): `∫_0^t g ≤ 1` for `t ≥ 0`. -/
lemma sqt_int_le_one (g : ℝ → ℝ) (hg_int : IntegrableOn g (Ioi 0))
    (hg_nonneg : ∀ u ∈ Ici (0:ℝ), 0 ≤ g u) (hg_mass : ∫ u in Ioi (0:ℝ), g u ≤ 1) (t : ℝ)
    (ht : 0 ≤ t) : ∫ s in (0:ℝ)..t, g s ≤ 1 := by
  rw [intervalIntegral.integral_of_le ht]
  refine le_trans ?_ hg_mass
  refine setIntegral_mono_set hg_int ?_
    (Filter.Eventually.of_forall fun x hx => Ioc_subset_Ioi_self hx)
  exact (ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun x hx => hg_nonneg x (Set.mem_Ici.2 hx.le))

/-- `lem:app-phase-square-tail`, snapshot `cr-2026-10-23`.
Source: `sections/07-phase-comparison/section.tex` l.3112–3123.

LaTeX (verbatim, `section.tex` l.3112–3123):
```latex
\begin{lemma}[Square supersolution with a tail term]\label{lem:app-phase-square-tail}
Let $g\ge0$ be continuous with $\int_0^\infty g\le1$, let $\epsilon>0$ and $u_0>0$,
and let $f,h,w\ge0$ be continuous on $[0,u_0]$ with
\[
f\le h^2,\qquad g*h\le2h+\frac{w^2}{\sqrt\epsilon},\qquad g*w\le2w\qquad\text{on }[0,u_0].
\]
If $Y>0$ is continuous and $Y=f+\sqrt\epsilon\,g*\sqrt Y$ on $[0,u_0]$, then on $[0,u_0]$
\[
Y\le(h+w+\sqrt\epsilon)^2\qquad\text{and}\qquad
g*\sqrt Y\le G\defeq2h+\frac{w^2}{\sqrt\epsilon}+2w+\sqrt\epsilon .
\]
\end{lemma}
```
-/
theorem lem_app_phase_square_tail
    {ε u0 : ℝ} (hε : 0 < ε) (hu0 : 0 < u0)
    {f h wt g Y : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Ici 0)) (hg_nonneg : ∀ u ∈ Ici (0 : ℝ), 0 ≤ g u)
    (hg_int : IntegrableOn g (Ioi 0)) (hg_mass : ∫ u in Ioi (0 : ℝ), g u ≤ 1)
    (hf_cont : ContinuousOn f (Icc 0 u0)) (hf_nonneg : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ f u)
    (hh_cont : ContinuousOn h (Icc 0 u0)) (hh_nonneg : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ h u)
    (hw_cont : ContinuousOn wt (Icc 0 u0)) (hw_nonneg : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ wt u)
    (hfh : ∀ u ∈ Icc (0 : ℝ) u0, f u ≤ h u ^ 2)
    (hgh : ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv h g u ≤ 2 * h u + wt u ^ 2 / Real.sqrt ε)
    (hgw : ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv wt g u ≤ 2 * wt u)
    (hY_cont : ContinuousOn Y (Icc 0 u0)) (hY_pos : ∀ u ∈ Icc (0 : ℝ) u0, 0 < Y u)
    (hY : ∀ u ∈ Icc (0 : ℝ) u0,
      Y u = f u + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) g u) :
    (∀ u ∈ Icc (0 : ℝ) u0, Y u ≤ (h u + wt u + Real.sqrt ε) ^ 2) ∧
      ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv (fun v => Real.sqrt (Y v)) g u ≤ sqTailG h wt ε u := by
  have hq0 : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hq2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hgI : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable g volume 0 t := fun t ht =>
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht).2 (hg_int.mono_set Ioo_subset_Ioi_self)
  have hnn : ∀ x ∈ Icc (0 : ℝ) u0, 0 ≤ h x + wt x + Real.sqrt ε := fun x hx => by
    linarith [hh_nonneg x hx, hw_nonneg x hx, Real.sqrt_nonneg ε]
  -- Step A: the tail-weighted bound on the convolution of `h + w + √ε`.
  have hA : ∀ s ∈ Icc (0 : ℝ) u0,
      oneSidedConv (fun u => h u + wt u + Real.sqrt ε) g s ≤ sqTailG h wt ε s := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hsub : Icc (0 : ℝ) s ⊆ Icc 0 u0 := Icc_subset_Icc le_rfl hs.2
    have hc0 : ContinuousOn h (Icc 0 s) := hh_cont.mono hsub
    have hc3 : ContinuousOn wt (Icc 0 s) := hw_cont.mono hsub
    have hsplit : oneSidedConv (fun u => h u + wt u + Real.sqrt ε) g s
        = oneSidedConv h g s + oneSidedConv wt g s + Real.sqrt ε * ∫ x in (0:ℝ)..s, g x := by
      have e1 := sqt_osc_add (fun u => h u + wt u) (fun _ => Real.sqrt ε) g s hs0
        (hc0.add hc3) continuousOn_const (hgI s hs0)
      have e2 := sqt_osc_add h wt g s hs0 hc0 hc3 (hgI s hs0)
      rw [sqt_osc_const] at e1
      rw [e1, e2]
    have hC : ∫ x in (0:ℝ)..s, g x ≤ 1 := sqt_int_le_one g hg_int hg_nonneg hg_mass s hs0
    have hgh' := hgh s hs
    have hgw' := hgw s hs
    unfold sqTailG
    rw [hsplit]
    linarith [mul_le_of_le_one_right hq0.le hC]
  -- Step B: `Y ≤ (h + w + √ε)²` by the comparison lemma.
  have hYU : ∀ u ∈ Icc (0 : ℝ) u0, Y u ≤ (h u + wt u + Real.sqrt ε) ^ 2 := by
    refine lem_app_phase_comparison u0 hu0 (fun s => Real.sqrt ε * g s)
      (fun s hs => mul_nonneg hq0.le (hg_nonneg s (Set.mem_Ici.2 hs.1.le)))
      ((hg_int.mono_set Ioo_subset_Ioi_self).const_mul (Real.sqrt ε))
      f hf_cont hf_nonneg ε hε Y (fun u => (h u + wt u + Real.sqrt ε) ^ 2) hY_cont
      (fun s hs => (hY_pos s hs).le)
      (((hh_cont.add hw_cont).add continuousOn_const).pow 2)
      (fun s _ => sq_nonneg _)
      (fun s hs => by
        have ha : Real.sqrt ε ≤ h s + wt s + Real.sqrt ε := by
          linarith [hh_nonneg s hs, hw_nonneg s hs]
        nlinarith [mul_self_le_mul_self hq0.le ha, hq2])
      (fun s hs => by
        rw [sqt_osc_const_mul]
        exact le_of_eq (hY s hs))
      (fun s hs => by
        rw [sqt_osc_const_mul]
        have hsub : Icc (0 : ℝ) s ⊆ Icc 0 u0 := Icc_subset_Icc le_rfl hs.2
        have hm1 : oneSidedConv (fun u => Real.sqrt ((h u + wt u + Real.sqrt ε) ^ 2)) g s
            ≤ oneSidedConv (fun u => h u + wt u + Real.sqrt ε) g s := by
          refine sqt_osc_mono _ _ g s hs.1
            ((((hh_cont.mono hsub).add (hw_cont.mono hsub)).add continuousOn_const).pow 2).sqrt
            (((hh_cont.mono hsub).add (hw_cont.mono hsub)).add continuousOn_const)
            (hgI s hs.1) (fun x hx => hg_nonneg x (Set.mem_Ici.2 hx.1))
            (fun x hx => le_of_eq (Real.sqrt_sq (hnn x ⟨hx.1, hx.2.trans hs.2⟩)))
        have hfin := mul_le_mul_of_nonneg_left (hm1.trans (hA s hs)) hq0.le
        have key : Real.sqrt ε * sqTailG h wt ε s
            = 2 * Real.sqrt ε * h s + wt s ^ 2 + 2 * Real.sqrt ε * wt s + ε := by
          unfold sqTailG
          have hinv : Real.sqrt ε * (wt s ^ 2 / Real.sqrt ε) = wt s ^ 2 := by
            field_simp
          have hmm : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
          linear_combination hinv + hmm
        nlinarith [hfin, key, hf_nonneg s hs, hfh s hs, mul_nonneg (hh_nonneg s hs) (hw_nonneg s hs),
          hq2])
  refine ⟨fun u hu => hYU u hu, fun u hu => ?_⟩
  have hmono : oneSidedConv (fun v => Real.sqrt (Y v)) g u
      ≤ oneSidedConv (fun v => h v + wt v + Real.sqrt ε) g u := by
    refine sqt_osc_mono _ _ g u hu.1
      (hY_cont.mono (Icc_subset_Icc le_rfl hu.2)).sqrt
      (((hh_cont.mono (Icc_subset_Icc le_rfl hu.2)).add
        (hw_cont.mono (Icc_subset_Icc le_rfl hu.2))).add continuousOn_const)
      (hgI u hu.1) (fun x hx => hg_nonneg x (Set.mem_Ici.2 hx.1)) (fun x hx => ?_)
    have hxU := hYU x ⟨hx.1, hx.2.trans hu.2⟩
    calc Real.sqrt (Y x) ≤ Real.sqrt ((h x + wt x + Real.sqrt ε) ^ 2) :=
          Real.sqrt_le_sqrt hxU
      _ = h x + wt x + Real.sqrt ε := Real.sqrt_sq (hnn x ⟨hx.1, hx.2.trans hu.2⟩)
  exact hmono.trans (hA u hu)

/-! ### Helpers for `lem_app_phase_restart` (P-H.14.P1) -/

/-- Copy of `Muon.Phase.mx_F_nonneg` (private there). -/
lemma rs_mx_F_nonneg {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (u : ℝ) :
    0 ≤ mixF a b u :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (Real.exp_pos _).le

/-- Copy of `mx_bound_integrable` (private in FirstHit). -/
lemma rs_mx_bound_integrable {bmin c : ℝ} (hbmin : 0 < bmin) :
    IntegrableOn (fun u : ℝ => c * Real.exp (-(bmin * u) / 2)) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => c * Real.exp (-(bmin / 2) * u)) (Ioi 0) :=
    Integrable.const_mul (exp_neg_integrableOn_Ioi 0 (b := bmin / 2) (by positivity)) c
  refine IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
  rw [show -(bmin * u) / 2 = -(bmin / 2) * u by ring]

/-- Copy of `mx_bound_integral` (private in FirstHit). -/
lemma rs_mx_bound_integral {bmin c : ℝ} (hbmin : 0 < bmin) :
    ∫ u in Ioi (0 : ℝ), c * Real.exp (-(bmin * u) / 2) = c * (2 / bmin) := by
  rw [integral_const_mul]
  congr 1
  have h := integral_exp_mul_Ioi (a := -(bmin / 2)) (by linarith) 0
  have e : (fun u : ℝ => Real.exp (-(bmin * u) / 2)) = fun u => Real.exp (-(bmin / 2) * u) := by
    funext u; congr 1; ring
  rw [e, h]
  simp

/-- Copy of `mx_F_le` (private in FirstHit). -/
lemma rs_mx_F_le {n : ℕ} (a b : Fin n → ℝ) (bmin : ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, bmin ≤ b i) {u : ℝ} (hu : 0 ≤ u) :
    mixF a b u ≤ (∑ i, a i) * Real.exp (-(bmin * u)) := by
  unfold mixF
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ha i)
  apply Real.exp_le_exp.2
  have := mul_le_mul_of_nonneg_right (hb i) hu
  linarith

/-- Copy of `mx_sqrt_le` (private in FirstHit). -/
lemma rs_mx_sqrt_le {n : ℕ} (a b : Fin n → ℝ) (bmin : ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, bmin ≤ b i) {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt (mixF a b u) ≤ Real.sqrt (∑ i, a i) * Real.exp (-(bmin * u) / 2) := by
  have hF0 : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha i
  have hsq : Real.exp (-(bmin * u) / 2) ^ 2 = Real.exp (-(bmin * u)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le, ?_⟩
  rw [mul_pow, Real.sq_sqrt hF0, hsq]
  exact rs_mx_F_le a b bmin ha hb hu

/-- Copy of `mx_sqrt_integrable` (private in FirstHit). -/
lemma rs_mx_sqrt_integrable {n : ℕ} (a b : Fin n → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, bmin ≤ b i) :
    IntegrableOn (fun u => Real.sqrt (mixF a b u)) (Ioi 0) := by
  refine Integrable.mono' (rs_mx_bound_integrable (c := Real.sqrt (∑ i, a i)) hbmin) ?_ ?_
  · exact (by unfold mixF; fun_prop : Continuous fun u => Real.sqrt (mixF a b u)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact rs_mx_sqrt_le a b bmin ha hb (le_of_lt hu)

/-- Splitting `mixF` of an appended coefficient list. -/
lemma rs_mixF_append {n n' : ℕ} (A : Fin n → ℝ) (B : Fin n' → ℝ) (b : Fin n → ℝ)
    (c : Fin n' → ℝ) (z : ℝ) :
    mixF (Fin.append A B) (Fin.append b c) z
      = (∑ i, A i * Real.exp (-(b i * z))) + ∑ l, B l * Real.exp (-(c l * z)) := by
  unfold mixF
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- Step 1 (memory integral): the memory of `g * √Y` at `u0 + z` on `[z, u0+z]`, for one
exponential rate `c`. -/
lemma rs_memory (Y : ℝ → ℝ) (u0 z c : ℝ) :
    ∫ x in z..(u0 + z), Real.sqrt (Y (u0 + z - x)) * (c * Real.exp (-(c * x)))
      = Real.exp (-(c * z))
        * ∫ v in (0:ℝ)..u0, Real.sqrt (Y v) * (c * Real.exp (-(c * (u0 - v)))) := by
  have h1 := intervalIntegral.integral_comp_sub_left
    (fun v => Real.sqrt (Y v) * (c * Real.exp (-(c * (u0 + z - v))))) (u0 + z) (a := z) (b := u0 + z)
  have e1 : u0 + z - (u0 + z) = 0 := by ring
  have e2 : u0 + z - z = u0 := by ring
  rw [e1, e2] at h1
  have h2 : ∀ v : ℝ, Real.sqrt (Y v) * (c * Real.exp (-(c * (u0 + z - v))))
      = Real.exp (-(c * z)) * (Real.sqrt (Y v) * (c * Real.exp (-(c * (u0 - v))))) := by
    intro v
    rw [show -(c * (u0 + z - v)) = -(c * z) + -(c * (u0 - v)) by ring, Real.exp_add]
    ring
  have h4 : (∫ x in z..(u0 + z), Real.sqrt (Y (u0 + z - x)) * (c * Real.exp (-(c * x))))
      = ∫ x in z..(u0 + z), (fun v => Real.sqrt (Y v) * (c * Real.exp (-(c * (u0 + z - v)))))
          (u0 + z - x) := by
    apply intervalIntegral.integral_congr
    intro x _
    show _ = Real.sqrt (Y (u0 + z - x)) * (c * Real.exp (-(c * (u0 + z - (u0 + z - x)))))
    rw [show u0 + z - (u0 + z - x) = x by ring]
  refine h4.trans (h1.trans ?_)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _
  exact h2 v

/-- Step 3 input: `oneSidedConv (√Y) (mixG w c) u0 = ∑_l w_l ∫_0^{u0} √Y(v) c_l e^{-c_l(u0-v)} dv`. -/
lemma rs_G0 {n' : ℕ} (Y : ℝ → ℝ) (u0 : ℝ) (hu0 : 0 ≤ u0)
    (hYc : ContinuousOn Y (Icc 0 u0)) (w c : Fin n' → ℝ) :
    oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0
      = ∑ l, w l * ∫ v in (0:ℝ)..u0, Real.sqrt (Y v) * (c l * Real.exp (-(c l * (u0 - v)))) := by
  have hF : ContinuousOn (fun v => Real.sqrt (Y v)) (Icc 0 u0) := hYc.sqrt
  have hint : ∀ l, IntervalIntegrable
      (fun s => Real.sqrt (Y (u0 - s)) * (w l * (c l * Real.exp (-(c l * s))))) volume 0 u0 :=
    fun l => sqt_int (fun v => Real.sqrt (Y v)) (fun s => w l * (c l * Real.exp (-(c l * s)))) u0
      hu0 hF ((by fun_prop : Continuous fun s => w l * (c l * Real.exp (-(c l * s)))).intervalIntegrable _ _)
  have hexp : ∀ s, Real.sqrt (Y (u0 - s)) * mixG w c s
      = ∑ l, Real.sqrt (Y (u0 - s)) * (w l * (c l * Real.exp (-(c l * s)))) := by
    intro s
    unfold mixG
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [oneSidedConv]
  simp only [hexp]
  rw [intervalIntegral.integral_finset_sum (fun l _ => hint l)]
  apply Finset.sum_congr rfl
  intro l _
  have hcs : ∫ x in (0:ℝ)..u0, Real.sqrt (Y (u0 - x)) * (c l * Real.exp (-(c l * x)))
      = ∫ v in (0:ℝ)..u0, Real.sqrt (Y v) * (c l * Real.exp (-(c l * (u0 - v)))) := by
    calc ∫ x in (0:ℝ)..u0, Real.sqrt (Y (u0 - x)) * (c l * Real.exp (-(c l * x)))
        = ∫ x in (0:ℝ)..u0, (fun v => Real.sqrt (Y v) * (c l * Real.exp (-(c l * (u0 - v)))))
            (u0 - x) := by
          apply intervalIntegral.integral_congr
          intro x _
          show _ = Real.sqrt (Y (u0 - x)) * (c l * Real.exp (-(c l * (u0 - (u0 - x)))))
          rw [sub_sub_cancel]
      _ = ∫ x in (u0 - u0)..(u0 - 0), Real.sqrt (Y x) * (c l * Real.exp (-(c l * (u0 - x)))) :=
          intervalIntegral.integral_comp_sub_left
            (fun v => Real.sqrt (Y v) * (c l * Real.exp (-(c l * (u0 - v))))) u0
      _ = ∫ v in (0:ℝ)..u0, Real.sqrt (Y v) * (c l * Real.exp (-(c l * (u0 - v)))) := by
          rw [sub_self, sub_zero]
  have hmul : ∫ x in (0:ℝ)..u0, Real.sqrt (Y (u0 - x)) * (w l * (c l * Real.exp (-(c l * x))))
      = w l * ∫ x in (0:ℝ)..u0, Real.sqrt (Y (u0 - x)) * (c l * Real.exp (-(c l * x))) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  rw [hmul, hcs]

/-- Step 2 (splitting the convolution at `u0`): `g * √Y (u0+z) = g * √Ỹ (z) + ∑_l w_l e^{-c_l z} y_l`. -/
lemma rs_split {n' : ℕ} (Y : ℝ → ℝ) (u0 z : ℝ) (hu0 : 0 ≤ u0) (hz : 0 ≤ z)
    (hYc : ContinuousOn Y (Ici 0)) (w c : Fin n' → ℝ) (Yl : Fin n' → ℝ)
    (hYl : ∀ l, Yl l = ∫ v in (0:ℝ)..u0, Real.sqrt (Y v) * (c l * Real.exp (-(c l * (u0 - v))))) :
    oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) (u0 + z)
      = oneSidedConv (fun v => Real.sqrt (Y (u0 + v))) (mixG w c) z
        + ∑ l, w l * (Real.exp (-(c l * z)) * Yl l) := by
  have hYc' : ContinuousOn Y (Icc 0 (u0 + z)) := hYc.mono Icc_subset_Ici_self
  have hF : ContinuousOn (fun v => Real.sqrt (Y v)) (Icc 0 (u0 + z)) := hYc'.sqrt
  have hG : Continuous (mixG w c) := by unfold mixG; fun_prop
  have hI : IntervalIntegrable (fun s => Real.sqrt (Y (u0 + z - s)) * mixG w c s) volume 0 (u0 + z) :=
    sqt_int (fun v => Real.sqrt (Y v)) (mixG w c) (u0 + z) (by linarith) hF (hG.intervalIntegrable _ _)
  have hI1 : IntervalIntegrable (fun s => Real.sqrt (Y (u0 + z - s)) * mixG w c s) volume 0 z :=
    hI.mono_set (Set.uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨le_rfl, by linarith⟩))
      (Set.mem_uIcc.2 (Or.inl ⟨hz, by linarith⟩)))
  have hI2 : IntervalIntegrable (fun s => Real.sqrt (Y (u0 + z - s)) * mixG w c s) volume z (u0 + z) :=
    hI.mono_set (Set.uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨hz, by linarith⟩))
      (Set.mem_uIcc.2 (Or.inl ⟨by linarith, le_rfl⟩)))
  simp only [oneSidedConv]
  rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
  have hA : ∫ s in (0:ℝ)..z, Real.sqrt (Y (u0 + z - s)) * mixG w c s
      = ∫ s in (0:ℝ)..z, Real.sqrt (Y (u0 + (z - s))) * mixG w c s := by
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [show u0 + z - s = u0 + (z - s) by ring]
  rw [hA]
  have hii : ∀ l, IntervalIntegrable
      (fun s => Real.sqrt (Y (u0 + z - s)) * (w l * (c l * Real.exp (-(c l * s))))) volume z (u0 + z) := by
    intro l
    have h0 := sqt_int (fun v => Real.sqrt (Y v)) (fun s => w l * (c l * Real.exp (-(c l * s))))
      (u0 + z) (by linarith) hF
      ((by fun_prop : Continuous fun s => w l * (c l * Real.exp (-(c l * s)))).intervalIntegrable _ _)
    exact h0.mono_set (Set.uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨hz, by linarith⟩))
      (Set.mem_uIcc.2 (Or.inl ⟨by linarith, le_rfl⟩)))
  have hB : ∫ s in z..(u0 + z), Real.sqrt (Y (u0 + z - s)) * mixG w c s
      = ∑ l, w l * (Real.exp (-(c l * z)) * Yl l) := by
    have hsum : ∀ s, Real.sqrt (Y (u0 + z - s)) * mixG w c s
        = ∑ l, Real.sqrt (Y (u0 + z - s)) * (w l * (c l * Real.exp (-(c l * s)))) := by
      intro s
      unfold mixG
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    simp only [hsum]
    rw [intervalIntegral.integral_finset_sum (fun l _ => hii l)]
    apply Finset.sum_congr rfl
    intro l _
    have hmul : ∫ s in z..(u0 + z), Real.sqrt (Y (u0 + z - s)) * (w l * (c l * Real.exp (-(c l * s))))
        = w l * ∫ s in z..(u0 + z), Real.sqrt (Y (u0 + z - s)) * (c l * Real.exp (-(c l * s))) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext s
      ring
    rw [hmul, hYl l, rs_memory Y u0 z (c l)]
  rw [hB]

/-- `e^{-x/2}` squared. -/
lemma rs_exp_half_sq (x : ℝ) : Real.exp (-x / 2) ^ 2 = Real.exp (-x) := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- `(ε^{1/4})² = √ε`. -/
lemma rs_eps_quarter (ε : ℝ) (hε : 0 < ε) : (ε ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt ε := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, Real.sqrt_eq_rpow]
  norm_num

/-- Nonnegativity of the appended coefficient list (Step 4 input). -/
lemma rs_app_nonneg {n n' : ℕ} (a b : Fin n → ℝ) (w c : Fin n' → ℝ) (ε u0 : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hw : ∀ l, 0 ≤ w l) (Yl : Fin n' → ℝ) (hYl : ∀ l, 0 ≤ Yl l) :
    ∀ j, 0 ≤ Fin.append (fun i => a i * Real.exp (-(b i * u0)))
      (fun l => Real.sqrt ε * (w l * Yl l)) j := by
  intro j
  induction j using Fin.addCases with
  | left i =>
    simp only [Fin.append_left]
    exact mul_nonneg (ha i) (Real.exp_pos _).le
  | right l =>
    simp only [Fin.append_right]
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (hw l) (hYl l))

/-- Rates of the appended list dominate `bmin`. -/
lemma rs_app_bound {n n' : ℕ} (b : Fin n → ℝ) (c : Fin n' → ℝ) (bmin : ℝ)
    (hb : ∀ i, bmin ≤ b i) (hc : ∀ l, bmin ≤ c l) : ∀ j, bmin ≤ (Fin.append b c) j := by
  intro j
  induction j using Fin.addCases with
  | left i =>
    simp only [Fin.append_left]
    exact hb i
  | right l =>
    simp only [Fin.append_right]
    exact hc l

/-- Shift invariance of the integral over `(u0, ∞)`. -/
lemma rs_shift (φ : ℝ → ℝ) (u0 : ℝ) :
    ∫ z in Ioi (0:ℝ), φ (u0 + z) = ∫ u in Ioi u0, φ u := by
  have h1 : ∀ z : ℝ, (Ioi (0:ℝ)).indicator (fun z => φ (u0 + z)) z
      = (Ioi u0).indicator φ (u0 + z) := by
    intro z
    simp [Set.indicator_apply]
  calc ∫ z in Ioi (0:ℝ), φ (u0 + z)
      = ∫ z, (Ioi (0:ℝ)).indicator (fun z => φ (u0 + z)) z :=
        (integral_indicator measurableSet_Ioi).symm
    _ = ∫ z, (Ioi u0).indicator φ (u0 + z) := integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = ∫ z, (Ioi u0).indicator φ z := integral_add_left_eq_self (fun z => (Ioi u0).indicator φ z) u0
    _ = ∫ u in Ioi u0, φ u := integral_indicator measurableSet_Ioi

/-- Step 6: the tail integral of the shifted mixture is bounded by the restart's `J~`. -/
lemma rs_mixJ_le {n n' : ℕ} (a b : Fin n → ℝ) (w c : Fin n' → ℝ) (bmin : ℝ)
    (hbmin : 0 < bmin) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, bmin ≤ b i) (hw : ∀ l, 0 ≤ w l)
    (hc : ∀ l, bmin ≤ c l) {u0 ε : ℝ} (hu0 : 0 ≤ u0) (hε : 0 < ε) (Yl : Fin n' → ℝ)
    (hYl : ∀ l, 0 ≤ Yl l) :
    mixJ (Fin.append (fun i => a i * Real.exp (-(b i * u0))) (fun l => Real.sqrt ε * (w l * Yl l)))
        (Fin.append b c)
      ≤ (∫ u in Ioi u0, Real.sqrt (mixF a b u))
        + (2 / bmin) * ε ^ (1 / 4 : ℝ) * Real.sqrt (∑ l, w l * Yl l) := by
  have hG0 : 0 ≤ ∑ l, w l * Yl l := Finset.sum_nonneg fun l _ => mul_nonneg (hw l) (hYl l)
  have hK2 : (ε ^ (1 / 4 : ℝ) * Real.sqrt (∑ l, w l * Yl l)) ^ 2 = Real.sqrt ε * ∑ l, w l * Yl l := by
    rw [mul_pow, rs_eps_quarter ε hε, Real.sq_sqrt hG0]
  have hK : 0 ≤ ε ^ (1 / 4 : ℝ) * Real.sqrt (∑ l, w l * Yl l) :=
    mul_nonneg (Real.rpow_nonneg hε.le _) (Real.sqrt_nonneg _)
  have hpt : ∀ z ∈ Ioi (0:ℝ),
      Real.sqrt (mixF (Fin.append (fun i => a i * Real.exp (-(b i * u0)))
          (fun l => Real.sqrt ε * (w l * Yl l))) (Fin.append b c) z)
        ≤ Real.sqrt (mixF a b (u0 + z))
          + (ε ^ (1 / 4 : ℝ) * Real.sqrt (∑ l, w l * Yl l)) * Real.exp (-(bmin * z) / 2) := by
    intro z hz
    have hz0 : 0 ≤ z := le_of_lt hz
    have e1 : (∑ i, a i * Real.exp (-(b i * u0)) * Real.exp (-(b i * z))) = mixF a b (u0 + z) := by
      unfold mixF
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
    have e2 : ∑ l, Real.sqrt ε * (w l * Yl l) * Real.exp (-(c l * z))
        ≤ Real.sqrt ε * (∑ l, w l * Yl l) * Real.exp (-(bmin * z)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro l _
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
        (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (hw l) (hYl l)))
      have := mul_le_mul_of_nonneg_right (hc l) hz0
      linarith
    have hA : mixF (Fin.append (fun i => a i * Real.exp (-(b i * u0)))
          (fun l => Real.sqrt ε * (w l * Yl l))) (Fin.append b c) z
        ≤ mixF a b (u0 + z) + Real.sqrt ε * (∑ l, w l * Yl l) * Real.exp (-(bmin * z)) := by
      rw [rs_mixF_append, ← e1]
      linarith [e2]
    have hEe := rs_exp_half_sq (bmin * z)
    have hAnn := rs_mx_F_nonneg a b ha (u0 + z)
    refine Real.sqrt_le_iff.2 ⟨add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hK (Real.exp_pos _).le), ?_⟩
    have hKE : ((ε ^ (1 / 4 : ℝ) * Real.sqrt (∑ l, w l * Yl l)) * Real.exp (-(bmin * z) / 2)) ^ 2
        = Real.sqrt ε * (∑ l, w l * Yl l) * Real.exp (-(bmin * z)) := by
      rw [mul_pow, hK2, hEe]
    nlinarith [hA, hKE, Real.sq_sqrt hAnn,
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg (mixF a b (u0 + z))) hK)
        (Real.exp_pos (-(bmin * z) / 2)).le]
  have hint1 := rs_mx_sqrt_integrable _ _ bmin hbmin
    (rs_app_nonneg a b w c ε u0 ha hw Yl hYl) (rs_app_bound b c bmin hb hc)
  have hcontA : Continuous (fun z : ℝ => Real.sqrt (mixF a b (u0 + z))) := by
    unfold mixF
    fun_prop
  have hintA : IntegrableOn (fun z : ℝ => Real.sqrt (mixF a b (u0 + z))) (Ioi 0) := by
    refine Integrable.mono' (rs_mx_bound_integrable (bmin := bmin) (c := Real.sqrt (∑ i, a i)) hbmin)
      hcontA.aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => ?_
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hz0 : (0:ℝ) ≤ z := le_of_lt (Set.mem_Ioi.1 hz)
    have h1 := rs_mx_sqrt_le a b bmin ha hb (u := u0 + z) (by linarith)
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.sqrt_nonneg _))
    nlinarith [mul_nonneg hbmin.le hu0]
  have hintK := rs_mx_bound_integrable (bmin := bmin)
    (c := ε ^ (1 / 4 : ℝ) * Real.sqrt (∑ l, w l * Yl l)) hbmin
  unfold mixJ
  calc ∫ z in Ioi (0:ℝ), Real.sqrt (mixF (Fin.append (fun i => a i * Real.exp (-(b i * u0)))
          (fun l => Real.sqrt ε * (w l * Yl l))) (Fin.append b c) z)
      ≤ ∫ z in Ioi (0:ℝ), (Real.sqrt (mixF a b (u0 + z))
          + (ε ^ (1 / 4 : ℝ) * Real.sqrt (∑ l, w l * Yl l)) * Real.exp (-(bmin * z) / 2)) :=
        setIntegral_mono_on hint1 (hintA.add hintK) measurableSet_Ioi (fun z hz => hpt z hz)
    _ = (∫ z in Ioi (0:ℝ), Real.sqrt (mixF a b (u0 + z)))
          + (ε ^ (1 / 4 : ℝ) * Real.sqrt (∑ l, w l * Yl l)) * (2 / bmin) := by
        rw [integral_add hintA hintK, rs_mx_bound_integral hbmin]
    _ = (∫ u in Ioi u0, Real.sqrt (mixF a b u))
          + (2 / bmin) * ε ^ (1 / 4 : ℝ) * Real.sqrt (∑ l, w l * Yl l) := by
        rw [rs_shift (fun u => Real.sqrt (mixF a b u)) u0]
        ring

/-- Step 5 (transfer of the first hit): the first hit of `Y` is `u0` plus that of the shift. -/
lemma rs_firstHit_shift (Y : ℝ → ℝ) (u0 a û : ℝ) (hu0 : 0 ≤ u0) (hû : 0 ≤ û)
    (hhi : ∀ u ∈ Icc (0:ℝ) u0, a < Y u) (hatt : Y (u0 + û) = a)
    (hfh : firstHit (fun z => Y (u0 + z)) a = ENNReal.ofReal û) :
    firstHit Y a = ENNReal.ofReal (u0 + û) := by
  apply le_antisymm
  · unfold firstHit
    refine iInf₂_le (Real.toNNReal (u0 + û)) ?_
    show Y ((Real.toNNReal (u0 + û) : NNReal) : ℝ) ≤ a
    rw [Real.coe_toNNReal _ (by linarith)]
    exact le_of_eq hatt
  · refine le_iInf₂ fun t ht => ?_
    have ht_gt : u0 < (t : ℝ) := by
      by_contra hcon
      push_neg at hcon
      have := hhi (t : ℝ) ⟨NNReal.coe_nonneg t, hcon⟩
      have ht' : Y (t : ℝ) ≤ a := ht
      linarith
    have hs : ((Real.toNNReal ((t : ℝ) - u0) : NNReal) : ℝ) = (t : ℝ) - u0 :=
      Real.coe_toNNReal _ (by linarith)
    have hle : firstHit (fun z => Y (u0 + z)) a ≤ ((Real.toNNReal ((t : ℝ) - u0) : NNReal) : ENNReal) := by
      unfold firstHit
      refine iInf₂_le (Real.toNNReal ((t : ℝ) - u0)) ?_
      show Y (u0 + ((Real.toNNReal ((t : ℝ) - u0) : NNReal) : ℝ)) ≤ a
      rw [hs, show u0 + ((t : ℝ) - u0) = (t : ℝ) by ring]
      exact ht
    rw [hfh] at hle
    have h2 : û ≤ ((Real.toNNReal ((t : ℝ) - u0) : NNReal) : ℝ) := by
      have := (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).1 hle
      simpa using this
    refine (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).2 ?_
    rw [ENNReal.coe_toReal]
    linarith [h2, hs]

/-- `lem:app-phase-restart`, snapshot `cr-2026-10-23`.
Source: `sections/07-phase-comparison/section.tex` l.3142–3154.

LaTeX (verbatim, `section.tex` l.3142–3154):
```latex
\begin{lemma}[Restart]\label{lem:app-phase-restart}
Assume the setting of \cref{lem:app-phase-mixture}, with any $\epsilon>0$. Let
$u_0\ge0$, suppose that $Y>T\epsilon$ on $[0,u_0]$, and put
$G_0\defeq(g*\sqrt Y)(u_0)$. Then the first $T\epsilon$ hit $\hat u$ is attained
in $\big(u_0,u_0+\frac2{b_{\min}}\log\frac{Y(u_0)}\epsilon\big]$, and
\[
\begin{gathered}
\int_{u_0}^{\hat u}\sqrt Y\,\dif u\le\big(\tilde{\mathsf J}^{1/2}+\tilde{\mathsf d}^{1/2}\big)^2,\\
\tilde{\mathsf J}\defeq\int_{u_0}^\infty\sqrt f\,\dif u+\frac2{b_{\min}}\,\epsilon^{1/4}G_0^{1/2},\qquad
\tilde{\mathsf d}\defeq\frac2{b_{\min}}\sqrt\epsilon\,\log\frac{Y(u_0)}\epsilon .
\end{gathered}
\]
\end{lemma}
```
-/
theorem lem_app_phase_restart
    {n n' : ℕ} (a b : Fin n → ℝ) (w c : Fin n' → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (ha : ∀ i, 0 ≤ a i) (hF0 : 0 < ∑ i, a i) (hb : ∀ i, bmin ≤ b i)
    (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (hc : ∀ l, bmin ≤ c l)
    {T ε u0 : ℝ} (hT : 4 ≤ T) (hε : 0 < ε) (hu0 : 0 ≤ u0)
    {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Ici 0)) (hYpos : ∀ u ∈ Ici (0 : ℝ), 0 < Y u)
    (hY : ∀ u ∈ Ici (0 : ℝ),
      Y u = mixF a b u + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u)
    (hYT : ∀ u ∈ Icc (0 : ℝ) u0, T * ε < Y u) :
    ∃ û : ℝ, firstHit Y (T * ε) = ENNReal.ofReal û ∧ u0 < û ∧
      û ≤ u0 + (2 / bmin) * Real.log (Y u0 / ε) ∧
      ∫ u in u0..û, Real.sqrt (Y u) ≤
        (Real.sqrt (restartJ (mixF a b) bmin ε
            (oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0) u0)
          + Real.sqrt (restartD bmin ε (Y u0))) ^ 2 := by
  obtain ⟨Yl, hYl⟩ : ∃ Yl : Fin n' → ℝ, ∀ l, Yl l
      = ∫ v in (0:ℝ)..u0, Real.sqrt (Y v) * (c l * Real.exp (-(c l * (u0 - v)))) :=
    ⟨fun l => ∫ v in (0:ℝ)..u0, Real.sqrt (Y v) * (c l * Real.exp (-(c l * (u0 - v)))), fun l => rfl⟩
  have hYcI : ContinuousOn Y (Icc 0 u0) := hYc.mono Icc_subset_Ici_self
  -- Step 3: the memory at u0.
  have hG0 : oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0 = ∑ l, w l * Yl l := by
    rw [rs_G0 Y u0 hu0 hYcI w c]
    exact Finset.sum_congr rfl fun l _ => by rw [hYl l]
  have hYl_nn : ∀ l, 0 ≤ Yl l := by
    intro l
    rw [hYl l]
    exact intervalIntegral.integral_nonneg hu0 fun v _ =>
      mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by linarith [hc l]) (Real.exp_pos _).le)
  have hYu0 : Y u0 = mixF a b u0 + Real.sqrt ε * ∑ l, w l * Yl l := by
    rw [← hG0]
    exact hY u0 (Set.mem_Ici.2 hu0)
  -- Step 2: the shifted equation.
  have hSplit : ∀ z, 0 ≤ z → Y (u0 + z)
      = mixF (Fin.append (fun i => a i * Real.exp (-(b i * u0))) (fun l => Real.sqrt ε * (w l * Yl l)))
          (Fin.append b c) z
        + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y (u0 + v))) (mixG w c) z := by
    intro z hz
    rw [hY (u0 + z) (Set.mem_Ici.2 (by linarith)), rs_split Y u0 z hu0 hz hYc w c Yl hYl,
      rs_mixF_append, mul_add]
    have e1 : mixF a b (u0 + z) = ∑ i, a i * Real.exp (-(b i * u0)) * Real.exp (-(b i * z)) := by
      unfold mixF
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
    have hsumE : Real.sqrt ε * ∑ l, w l * (Real.exp (-(c l * z)) * Yl l)
        = ∑ l, Real.sqrt ε * (w l * Yl l) * Real.exp (-(c l * z)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e1, hsumE]
    ring
  -- Step 3 (sum): the total initial value of the shifted problem is `Y u0`.
  have hSa : ∑ j, Fin.append (fun i => a i * Real.exp (-(b i * u0)))
      (fun l => Real.sqrt ε * (w l * Yl l)) j = Y u0 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hYu0]
    unfold mixF
    rw [Finset.mul_sum]
  have hTpos : 0 < T := by linarith
  have hYT0 : T * ε < Y u0 := hYT u0 ⟨hu0, le_rfl⟩
  have hSpos : 0 < ∑ j, Fin.append (fun i => a i * Real.exp (-(b i * u0)))
      (fun l => Real.sqrt ε * (w l * Yl l)) j := by
    rw [hSa]
    exact lt_trans (mul_pos hTpos hε) hYT0
  have hεF : ε < (∑ j, Fin.append (fun i => a i * Real.exp (-(b i * u0)))
      (fun l => Real.sqrt ε * (w l * Yl l)) j) / T := by
    rw [hSa, lt_div_iff₀ hTpos]
    linarith [mul_comm ε T]
  have hYc' : ContinuousOn (fun z => Y (u0 + z)) (Ici 0) :=
    hYc.comp (by fun_prop : Continuous fun z : ℝ => u0 + z).continuousOn
      (fun z hz => Set.mem_Ici.2 (by linarith [Set.mem_Ici.1 hz]))
  have hYpos' : ∀ u ∈ Ici (0:ℝ), 0 < (fun z => Y (u0 + z)) u := fun u hu =>
    hYpos _ (Set.mem_Ici.2 (by linarith [Set.mem_Ici.1 hu]))
  have hYtil : ∀ u ∈ Ici (0:ℝ), (fun z => Y (u0 + z)) u
      = mixF (Fin.append (fun i => a i * Real.exp (-(b i * u0))) (fun l => Real.sqrt ε * (w l * Yl l)))
          (Fin.append b c) u
        + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt ((fun z => Y (u0 + z)) v)) (mixG w c) u :=
    fun u hu => hSplit u (Set.mem_Ici.1 hu)
  -- Step 4: the mixture lemma for the shifted problem.
  obtain ⟨hJpos, hJle, û', hfh', hû'pos, hû'H, hYû', _, hup⟩ :=
    lem_app_phase_mixture
      (Fin.append (fun i => a i * Real.exp (-(b i * u0))) (fun l => Real.sqrt ε * (w l * Yl l)))
      (Fin.append b c) w c bmin hbmin
      (rs_app_nonneg a b w c ε u0 ha hw Yl hYl_nn) hSpos (rs_app_bound b c bmin hb hc)
      hw hw1 hc hT hε hεF rfl rfl hYc' hYpos' hYtil
  -- Step 5: transfer of the first hit.
  have hfirst : firstHit Y (T * ε) = ENNReal.ofReal (u0 + û') :=
    rs_firstHit_shift Y u0 (T * ε) û' hu0 hû'pos.le (fun u hu => hYT u hu) hYû' hfh'
  have hsub : ∫ u in u0..(u0 + û'), Real.sqrt (Y u) = ∫ x in (0:ℝ)..û', Real.sqrt (Y (u0 + x)) := by
    have htr := intervalIntegral.integral_comp_add_left (fun u => Real.sqrt (Y u)) u0
      (a := 0) (b := û')
    simp only [add_zero] at htr
    exact htr.symm
  -- Step 6: the tail bound.
  have hJ' := rs_mixJ_le a b w c bmin hbmin ha hb hw hc hu0 hε Yl hYl_nn
  have hHsum : (2 / bmin) * Real.log ((∑ j, Fin.append (fun i => a i * Real.exp (-(b i * u0)))
      (fun l => Real.sqrt ε * (w l * Yl l)) j) / ε) = (2 / bmin) * Real.log (Y u0 / ε) := by
    rw [hSa]
  rw [hHsum] at hû'H hup
  have hD0 : 0 ≤ Real.sqrt ε * ((2 / bmin) * Real.log (Y u0 / ε)) :=
    mul_nonneg (Real.sqrt_nonneg _) (le_trans hû'pos.le hû'H)
  refine ⟨u0 + û', hfirst, by linarith, by linarith, ?_⟩
  rw [hsub]
  unfold restartJ restartD
  rw [hG0]
  have hDeq : (2 / bmin) * Real.sqrt ε * Real.log (Y u0 / ε)
      = Real.sqrt ε * ((2 / bmin) * Real.log (Y u0 / ε)) := by ring
  rw [hDeq]
  have hJnn : 0 ≤ (∫ u in Ioi u0, Real.sqrt (mixF a b u))
      + (2 / bmin) * ε ^ (1 / 4 : ℝ) * Real.sqrt (∑ l, w l * Yl l) := le_trans hJpos.le hJ'
  have hsqrtmul : Real.sqrt (Real.sqrt ε * ((2 / bmin) * Real.log (Y u0 / ε))
      * mixJ (Fin.append (fun i => a i * Real.exp (-(b i * u0))) (fun l => Real.sqrt ε * (w l * Yl l)))
          (Fin.append b c))
      ≤ Real.sqrt (Real.sqrt ε * ((2 / bmin) * Real.log (Y u0 / ε)))
        * Real.sqrt ((∫ u in Ioi u0, Real.sqrt (mixF a b u))
          + (2 / bmin) * ε ^ (1 / 4 : ℝ) * Real.sqrt (∑ l, w l * Yl l)) := by
    rw [← Real.sqrt_mul hD0]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hJ' hD0)
  nlinarith [hup, hsqrtmul, hJ', hJnn, Real.sq_sqrt hJnn, Real.sq_sqrt hD0]

/-! ## Two-phase bound -/

/-- Copy of `mx_g_term` (private in `FirstHit`). -/
lemma tp_g_term (w c : ℝ) (hw : 0 ≤ w) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => w * c * Real.exp (-(c * u))) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), w * c * Real.exp (-(c * u)) = w := by
  have e : (fun u : ℝ => Real.exp (-(c * u))) = fun u => Real.exp ((-c) * u) := by
    funext u; congr 1; ring
  refine ⟨?_, ?_⟩
  · have := Integrable.const_mul (exp_neg_integrableOn_Ioi 0 hc) (w * c)
    refine IntegrableOn.congr_fun this (fun u _ => ?_) measurableSet_Ioi
    simp only [neg_mul]
  · rw [integral_const_mul, e, integral_exp_mul_Ioi (by linarith) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp

/-- Copy of `mx_g_int` (private in `FirstHit`): the mixed kernel has unit mass. -/
lemma tp_g_int {n' : ℕ} (w c : Fin n' → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (hc : ∀ l, bmin ≤ c l) :
    IntegrableOn (mixG w c) (Ioi 0) ∧ ∫ u in Ioi (0 : ℝ), mixG w c u = 1 := by
  have hcp : ∀ l, 0 < c l := fun l => lt_of_lt_of_le hbmin (hc l)
  refine ⟨?_, ?_⟩
  · unfold mixG
    exact integrable_finset_sum _ fun l _ => (tp_g_term (w l) (c l) (hw l) (hcp l)).1
  · unfold mixG
    rw [integral_finset_sum _ fun l _ => (tp_g_term (w l) (c l) (hw l) (hcp l)).1]
    simp_rw [fun l => (tp_g_term (w l) (c l) (hw l) (hcp l)).2]
    exact hw1

/-- Copy of `mx_g_nonneg` (private in `FirstHit`). -/
lemma tp_g_nonneg {n' : ℕ} (w c : Fin n' → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (hw : ∀ l, 0 ≤ w l) (hc : ∀ l, bmin ≤ c l) (u : ℝ) : 0 ≤ mixG w c u :=
  Finset.sum_nonneg fun l _ =>
    mul_nonneg (mul_nonneg (hw l) (by linarith [hc l])) (Real.exp_pos _).le

/-- `√(x + y) ≤ √x + √y` for nonnegative `x, y`. -/
lemma tp_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

/-- A point of the sublevel set bounds the first hit from above. -/
lemma tp_firstHit_le (R : ℝ → ℝ) (a H : ℝ) (hH : 0 ≤ H) (hR : R H ≤ a) :
    firstHit R a ≤ ENNReal.ofReal H := by
  unfold firstHit
  refine iInf₂_le (Real.toNNReal H) ?_
  show R ((Real.toNNReal H : NNReal) : ℝ) ≤ a
  rw [Real.coe_toNNReal _ hH]
  exact hR

/-- Shared square-supersolution bounds for the mixture setting: `Y ≤ (h+w+√ε)^2`,
`√Y ≤ √f + ε^{1/4} √G` and `g * √Y ≤ G` on `[0,u0]` (from `lem_app_phase_square_tail`). -/
lemma tp_square {n n' : ℕ} (a b : Fin n → ℝ) (w c : Fin n' → ℝ) (bmin : ℝ)
    (hbmin : 0 < bmin) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, bmin ≤ b i)
    (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (hc : ∀ l, bmin ≤ c l)
    {ε u0 : ℝ} (hε : 0 < ε) (hu0 : 0 < u0)
    {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Ici 0)) (hYpos : ∀ u ∈ Ici (0 : ℝ), 0 < Y u)
    (hY : ∀ u ∈ Ici (0 : ℝ),
      Y u = mixF a b u + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u)
    {h wt : ℝ → ℝ}
    (hh_cont : ContinuousOn h (Icc 0 u0)) (hh_nonneg : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ h u)
    (hw_cont : ContinuousOn wt (Icc 0 u0)) (hw_nonneg : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ wt u)
    (hfh : ∀ u ∈ Icc (0 : ℝ) u0, mixF a b u ≤ h u ^ 2)
    (hgh : ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv h (mixG w c) u ≤ 2 * h u + wt u ^ 2 / Real.sqrt ε)
    (hgw : ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv wt (mixG w c) u ≤ 2 * wt u) :
    (∀ u ∈ Icc (0 : ℝ) u0, Y u ≤ (h u + wt u + Real.sqrt ε) ^ 2) ∧
      (∀ u ∈ Icc (0 : ℝ) u0, Real.sqrt (Y u) ≤
        Real.sqrt (mixF a b u) + ε ^ (1 / 4 : ℝ) * Real.sqrt (sqTailG h wt ε u)) ∧
      (∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u
        ≤ sqTailG h wt ε u) := by
  obtain ⟨hint, hmass⟩ := tp_g_int w c bmin hbmin hw hw1 hc
  have hgc : ContinuousOn (mixG w c) (Ici 0) := by
    have : Continuous (mixG w c) := by unfold mixG; fun_prop
    exact this.continuousOn
  have hfc : ContinuousOn (mixF a b) (Icc 0 u0) := by
    have : Continuous (mixF a b) := by unfold mixF; fun_prop
    exact this.continuousOn
  have hYcI : ContinuousOn Y (Icc 0 u0) := hYc.mono Icc_subset_Ici_self
  have hYposI : ∀ u ∈ Icc (0 : ℝ) u0, 0 < Y u := fun u hu => hYpos u (Set.mem_Ici.2 hu.1)
  have hYeq : ∀ u ∈ Icc (0 : ℝ) u0, Y u
      = mixF a b u + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u :=
    fun u hu => hY u (Set.mem_Ici.2 hu.1)
  obtain ⟨hA, hC⟩ := lem_app_phase_square_tail (f := mixF a b) (h := h) (wt := wt)
    (g := mixG w c) (Y := Y) hε hu0 hgc (fun u _ => tp_g_nonneg w c bmin hbmin hw hc u)
    hint hmass.le hfc (fun u hu => rs_mx_F_nonneg a b ha u) hh_cont hh_nonneg hw_cont hw_nonneg
    hfh hgh hgw hYcI hYposI hYeq
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hq0 : 0 ≤ ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hε.le _
  have hq2 : (ε ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt ε := rs_eps_quarter ε hε
  have hGnn : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ sqTailG h wt ε u := by
    intro u hu
    unfold sqTailG
    have h1 := hh_nonneg u hu
    have h2 := hw_nonneg u hu
    have h3 : 0 ≤ wt u ^ 2 / Real.sqrt ε := div_nonneg (sq_nonneg _) hsε.le
    linarith
  have hB : ∀ u ∈ Icc (0 : ℝ) u0, Real.sqrt (Y u) ≤
      Real.sqrt (mixF a b u) + ε ^ (1 / 4 : ℝ) * Real.sqrt (sqTailG h wt ε u) := by
    intro u hu
    have hle : Y u ≤ mixF a b u + Real.sqrt ε * sqTailG h wt ε u := by
      rw [hYeq u hu]
      have := mul_le_mul_of_nonneg_left (hC u hu) hsε.le
      linarith
    have hf0 : 0 ≤ mixF a b u := rs_mx_F_nonneg a b ha u
    have hG0 : 0 ≤ Real.sqrt ε * sqTailG h wt ε u := mul_nonneg hsε.le (hGnn u hu)
    have hsqrt : Real.sqrt (Real.sqrt ε * sqTailG h wt ε u)
        = ε ^ (1 / 4 : ℝ) * Real.sqrt (sqTailG h wt ε u) := by
      rw [← hq2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq0]
    calc Real.sqrt (Y u)
        ≤ Real.sqrt (mixF a b u + Real.sqrt ε * sqTailG h wt ε u) := Real.sqrt_le_sqrt hle
      _ ≤ Real.sqrt (mixF a b u) + Real.sqrt (Real.sqrt ε * sqTailG h wt ε u) :=
          tp_sqrt_add_le hf0 hG0
      _ = Real.sqrt (mixF a b u) + ε ^ (1 / 4 : ℝ) * Real.sqrt (sqTailG h wt ε u) := by
          rw [hsqrt]
  exact ⟨hA, hB, hC⟩

/-- `lem:app-phase-twophase`, part (a) of 3, snapshot `cr-2026-10-23`.
Source: `sections/07-phase-comparison/section.tex` l.3187–3206.

LaTeX (verbatim, `section.tex` l.3187–3206):
```latex
\begin{lemma}[Two-phase bound]\label{lem:app-phase-twophase}
Assume the setting of \cref{lem:app-phase-mixture}. Let $u_0>0$, and let
$h,w\ge0$ be continuous on $[0,u_0]$ and satisfy the three hypotheses of
\cref{lem:app-phase-square-tail} there. Let $G$ be as in that lemma and
\[
\Theta_0\defeq1+\frac{h(u_0)+w(u_0)}{\sqrt\epsilon} .
\]
\begin{enumerate}[label=(\alph*)]
\item On $[0,u_0]$, $Y\le(h+w+\sqrt\epsilon)^2$ and $\sqrt Y\le\sqrt f+\epsilon^{1/4}G^{1/2}$.
\item If $h(H)+w(H)\le\sqrt\epsilon$ for some $H\in[0,u_0]$, then $\hat u\le H$.
\item With $\mathsf I\defeq\int_0^{\hat u}\sqrt Y$,
\[
\begin{gathered}
\mathsf I\le\int_0^{u_0}\sqrt Y\,\dif u+\big(\tilde{\mathsf J}^{1/2}+\tilde{\mathsf d}^{1/2}\big)^2,\\
\tilde{\mathsf J}\le\int_{u_0}^\infty\sqrt f\,\dif u+\frac2{b_{\min}}\sqrt\epsilon\,\Theta_0,\qquad
\tilde{\mathsf d}\le\frac4{b_{\min}}\sqrt\epsilon\,\log\Theta_0 .
\end{gathered}
\]
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_twophase_i
    {n n' : ℕ} (a b : Fin n → ℝ) (w c : Fin n' → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (ha : ∀ i, 0 ≤ a i) (hF0 : 0 < ∑ i, a i) (hb : ∀ i, bmin ≤ b i)
    (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (hc : ∀ l, bmin ≤ c l)
    {T ε u0 : ℝ} (hT : 4 ≤ T) (hε : 0 < ε) (hεF : ε < (∑ i, a i) / T) (hu0 : 0 < u0)
    {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Ici 0)) (hYpos : ∀ u ∈ Ici (0 : ℝ), 0 < Y u)
    (hY : ∀ u ∈ Ici (0 : ℝ),
      Y u = mixF a b u + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u)
    {h wt : ℝ → ℝ}
    (hh_cont : ContinuousOn h (Icc 0 u0)) (hh_nonneg : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ h u)
    (hw_cont : ContinuousOn wt (Icc 0 u0)) (hw_nonneg : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ wt u)
    (hfh : ∀ u ∈ Icc (0 : ℝ) u0, mixF a b u ≤ h u ^ 2)
    (hgh : ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv h (mixG w c) u ≤ 2 * h u + wt u ^ 2 / Real.sqrt ε)
    (hgw : ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv wt (mixG w c) u ≤ 2 * wt u) :
    ∀ u ∈ Icc (0 : ℝ) u0, Y u ≤ (h u + wt u + Real.sqrt ε) ^ 2 ∧
      Real.sqrt (Y u) ≤
        Real.sqrt (mixF a b u) + ε ^ (1 / 4 : ℝ) * Real.sqrt (sqTailG h wt ε u) := by
  obtain ⟨hA, hB, -⟩ := tp_square a b w c bmin hbmin ha hb hw hw1 hc hε hu0 hYc hYpos hY
    hh_cont hh_nonneg hw_cont hw_nonneg hfh hgh hgw
  exact fun u hu => ⟨hA u hu, hB u hu⟩

/-- `lem:app-phase-twophase`, part (b) of 3, snapshot `cr-2026-10-23`.
Source: `sections/07-phase-comparison/section.tex` l.3187–3206.

LaTeX (verbatim, `section.tex` l.3187–3206):
```latex
\begin{lemma}[Two-phase bound]\label{lem:app-phase-twophase}
Assume the setting of \cref{lem:app-phase-mixture}. Let $u_0>0$, and let
$h,w\ge0$ be continuous on $[0,u_0]$ and satisfy the three hypotheses of
\cref{lem:app-phase-square-tail} there. Let $G$ be as in that lemma and
\[
\Theta_0\defeq1+\frac{h(u_0)+w(u_0)}{\sqrt\epsilon} .
\]
\begin{enumerate}[label=(\alph*)]
\item On $[0,u_0]$, $Y\le(h+w+\sqrt\epsilon)^2$ and $\sqrt Y\le\sqrt f+\epsilon^{1/4}G^{1/2}$.
\item If $h(H)+w(H)\le\sqrt\epsilon$ for some $H\in[0,u_0]$, then $\hat u\le H$.
\item With $\mathsf I\defeq\int_0^{\hat u}\sqrt Y$,
\[
\begin{gathered}
\mathsf I\le\int_0^{u_0}\sqrt Y\,\dif u+\big(\tilde{\mathsf J}^{1/2}+\tilde{\mathsf d}^{1/2}\big)^2,\\
\tilde{\mathsf J}\le\int_{u_0}^\infty\sqrt f\,\dif u+\frac2{b_{\min}}\sqrt\epsilon\,\Theta_0,\qquad
\tilde{\mathsf d}\le\frac4{b_{\min}}\sqrt\epsilon\,\log\Theta_0 .
\end{gathered}
\]
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_twophase_ii
    {n n' : ℕ} (a b : Fin n → ℝ) (w c : Fin n' → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (ha : ∀ i, 0 ≤ a i) (hF0 : 0 < ∑ i, a i) (hb : ∀ i, bmin ≤ b i)
    (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (hc : ∀ l, bmin ≤ c l)
    {T ε u0 : ℝ} (hT : 4 ≤ T) (hε : 0 < ε) (hεF : ε < (∑ i, a i) / T) (hu0 : 0 < u0)
    {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Ici 0)) (hYpos : ∀ u ∈ Ici (0 : ℝ), 0 < Y u)
    (hY : ∀ u ∈ Ici (0 : ℝ),
      Y u = mixF a b u + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u)
    {h wt : ℝ → ℝ}
    (hh_cont : ContinuousOn h (Icc 0 u0)) (hh_nonneg : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ h u)
    (hw_cont : ContinuousOn wt (Icc 0 u0)) (hw_nonneg : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ wt u)
    (hfh : ∀ u ∈ Icc (0 : ℝ) u0, mixF a b u ≤ h u ^ 2)
    (hgh : ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv h (mixG w c) u ≤ 2 * h u + wt u ^ 2 / Real.sqrt ε)
    (hgw : ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv wt (mixG w c) u ≤ 2 * wt u) :
    ∀ H ∈ Icc (0 : ℝ) u0, h H + wt H ≤ Real.sqrt ε → firstHit Y (T * ε) ≤ ENNReal.ofReal H := by
  intro H hH hhw
  obtain ⟨hA, -, -⟩ := tp_square a b w c bmin hbmin ha hb hw hw1 hc hε hu0 hYc hYpos hY
    hh_cont hh_nonneg hw_cont hw_nonneg hfh hgh hgw
  have hYH := hA H hH
  have hsn := Real.sqrt_nonneg ε
  have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hx0 : 0 ≤ h H + wt H + Real.sqrt ε := by linarith [hh_nonneg H hH, hw_nonneg H hH]
  have hx : h H + wt H + Real.sqrt ε ≤ 2 * Real.sqrt ε := by linarith
  have hsq2 : (h H + wt H + Real.sqrt ε) ^ 2 ≤ (2 * Real.sqrt ε) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (add_nonneg hx0 (by linarith : (0:ℝ) ≤ 2 * Real.sqrt ε))]
  apply tp_firstHit_le Y (T * ε) H hH.1
  nlinarith [mul_nonneg (sub_nonneg.2 hT) hε.le]

/-- `lem:app-phase-twophase`, part (c) of 3, snapshot `cr-2026-10-23`.
Source: `sections/07-phase-comparison/section.tex` l.3187–3206.

LaTeX (verbatim, `section.tex` l.3187–3206):
```latex
\begin{lemma}[Two-phase bound]\label{lem:app-phase-twophase}
Assume the setting of \cref{lem:app-phase-mixture}. Let $u_0>0$, and let
$h,w\ge0$ be continuous on $[0,u_0]$ and satisfy the three hypotheses of
\cref{lem:app-phase-square-tail} there. Let $G$ be as in that lemma and
\[
\Theta_0\defeq1+\frac{h(u_0)+w(u_0)}{\sqrt\epsilon} .
\]
\begin{enumerate}[label=(\alph*)]
\item On $[0,u_0]$, $Y\le(h+w+\sqrt\epsilon)^2$ and $\sqrt Y\le\sqrt f+\epsilon^{1/4}G^{1/2}$.
\item If $h(H)+w(H)\le\sqrt\epsilon$ for some $H\in[0,u_0]$, then $\hat u\le H$.
\item With $\mathsf I\defeq\int_0^{\hat u}\sqrt Y$,
\[
\begin{gathered}
\mathsf I\le\int_0^{u_0}\sqrt Y\,\dif u+\big(\tilde{\mathsf J}^{1/2}+\tilde{\mathsf d}^{1/2}\big)^2,\\
\tilde{\mathsf J}\le\int_{u_0}^\infty\sqrt f\,\dif u+\frac2{b_{\min}}\sqrt\epsilon\,\Theta_0,\qquad
\tilde{\mathsf d}\le\frac4{b_{\min}}\sqrt\epsilon\,\log\Theta_0 .
\end{gathered}
\]
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_twophase_iii
    {n n' : ℕ} (a b : Fin n → ℝ) (w c : Fin n' → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (ha : ∀ i, 0 ≤ a i) (hF0 : 0 < ∑ i, a i) (hb : ∀ i, bmin ≤ b i)
    (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (hc : ∀ l, bmin ≤ c l)
    {T ε u0 : ℝ} (hT : 4 ≤ T) (hε : 0 < ε) (hεF : ε < (∑ i, a i) / T) (hu0 : 0 < u0)
    {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Ici 0)) (hYpos : ∀ u ∈ Ici (0 : ℝ), 0 < Y u)
    (hY : ∀ u ∈ Ici (0 : ℝ),
      Y u = mixF a b u + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u)
    {h wt : ℝ → ℝ}
    (hh_cont : ContinuousOn h (Icc 0 u0)) (hh_nonneg : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ h u)
    (hw_cont : ContinuousOn wt (Icc 0 u0)) (hw_nonneg : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ wt u)
    (hfh : ∀ u ∈ Icc (0 : ℝ) u0, mixF a b u ≤ h u ^ 2)
    (hgh : ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv h (mixG w c) u ≤ 2 * h u + wt u ^ 2 / Real.sqrt ε)
    (hgw : ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv wt (mixG w c) u ≤ 2 * wt u) :
    ∃ û : ℝ, firstHit Y (T * ε) = ENNReal.ofReal û ∧
      ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) ≤
        (∫ u in (0 : ℝ)..u0, Real.sqrt (Y u)) +
          (Real.sqrt (restartJ (mixF a b) bmin ε
              (oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0) u0)
            + Real.sqrt (restartD bmin ε (Y u0))) ^ 2 ∧
      restartJ (mixF a b) bmin ε (oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0) u0 ≤
        (∫ u in Ioi u0, Real.sqrt (mixF a b u)) +
          (2 / bmin) * Real.sqrt ε * (1 + (h u0 + wt u0) / Real.sqrt ε) ∧
      restartD bmin ε (Y u0) ≤
        (4 / bmin) * Real.sqrt ε * Real.log (1 + (h u0 + wt u0) / Real.sqrt ε) := by
  obtain ⟨hA, -, hC⟩ := tp_square a b w c bmin hbmin ha hb hw hw1 hc hε hu0 hYc hYpos hY
    hh_cont hh_nonneg hw_cont hw_nonneg hfh hgh hgw
  have hu0c : u0 ∈ Icc (0 : ℝ) u0 := ⟨hu0.le, le_rfl⟩
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hsn : 0 ≤ Real.sqrt ε := hsε.le
  have hbi : 0 ≤ 2 / bmin := div_nonneg zero_le_two hbmin.le
  have hΘ : 0 ≤ (h u0 + wt u0) / Real.sqrt ε :=
    div_nonneg (add_nonneg (hh_nonneg u0 hu0c) (hw_nonneg u0 hu0c)) hsn
  have hΘ0 : 0 < 1 + (h u0 + wt u0) / Real.sqrt ε := by linarith
  have hkey : Real.sqrt ε * (1 + (h u0 + wt u0) / Real.sqrt ε) ^ 2 - sqTailG h wt ε u0
      = (h u0 ^ 2 + 2 * h u0 * wt u0) / Real.sqrt ε := by
    unfold sqTailG
    field_simp <;> ring
  have hkey2 : sqTailG h wt ε u0 ≤ Real.sqrt ε * (1 + (h u0 + wt u0) / Real.sqrt ε) ^ 2 := by
    have hnn : 0 ≤ (h u0 ^ 2 + 2 * h u0 * wt u0) / Real.sqrt ε :=
      div_nonneg (by nlinarith [mul_nonneg (hh_nonneg u0 hu0c) (hw_nonneg u0 hu0c), sq_nonneg (h u0)]) hsn
    linarith
  have hq0 : 0 ≤ ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hε.le _
  have hq2 : (ε ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt ε := rs_eps_quarter ε hε
  have hG0 := hC u0 hu0c
  have hsqrtG : Real.sqrt (oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0)
      ≤ ε ^ (1 / 4 : ℝ) * (1 + (h u0 + wt u0) / Real.sqrt ε) := by
    have h1 : oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0
        ≤ (ε ^ (1 / 4 : ℝ) * (1 + (h u0 + wt u0) / Real.sqrt ε)) ^ 2 := by
      rw [mul_pow, hq2]; linarith
    calc Real.sqrt (oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0)
        ≤ Real.sqrt ((ε ^ (1 / 4 : ℝ) * (1 + (h u0 + wt u0) / Real.sqrt ε)) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = ε ^ (1 / 4 : ℝ) * (1 + (h u0 + wt u0) / Real.sqrt ε) :=
          Real.sqrt_sq (mul_nonneg hq0 hΘ0.le)
  have hJ_bound : restartJ (mixF a b) bmin ε
      (oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0) u0
      ≤ (∫ u in Ioi u0, Real.sqrt (mixF a b u))
        + (2 / bmin) * Real.sqrt ε * (1 + (h u0 + wt u0) / Real.sqrt ε) := by
    unfold restartJ
    have hfin : ε ^ (1 / 4 : ℝ) * Real.sqrt (oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0)
        ≤ Real.sqrt ε * (1 + (h u0 + wt u0) / Real.sqrt ε) := by
      calc _ ≤ ε ^ (1 / 4 : ℝ) * (ε ^ (1 / 4 : ℝ) * (1 + (h u0 + wt u0) / Real.sqrt ε)) :=
            mul_le_mul_of_nonneg_left hsqrtG hq0
        _ = Real.sqrt ε * (1 + (h u0 + wt u0) / Real.sqrt ε) := by
            rw [← hq2]; ring
    have := mul_le_mul_of_nonneg_left hfin hbi
    linarith
  have hD_bound : restartD bmin ε (Y u0)
      ≤ (4 / bmin) * Real.sqrt ε * Real.log (1 + (h u0 + wt u0) / Real.sqrt ε) := by
    unfold restartD
    have hYu := hA u0 hu0c
    have hsΘ : Real.sqrt ε * (1 + (h u0 + wt u0) / Real.sqrt ε) = h u0 + wt u0 + Real.sqrt ε := by
      field_simp <;> ring
    have hYΘ : Y u0 ≤ (1 + (h u0 + wt u0) / Real.sqrt ε) ^ 2 * ε := by
      have h2 := hYu
      rw [← hsΘ, mul_pow, Real.sq_sqrt hε.le] at h2
      linarith
    have hratio : Y u0 / ε ≤ (1 + (h u0 + wt u0) / Real.sqrt ε) ^ 2 := by
      rw [div_le_iff₀ hε]; exact hYΘ
    have hlog : Real.log (Y u0 / ε) ≤ 2 * Real.log (1 + (h u0 + wt u0) / Real.sqrt ε) := by
      have h1 := Real.log_le_log (div_pos (hYpos u0 (Set.mem_Ici.2 hu0.le)) hε) hratio
      rw [Real.log_pow] at h1
      push_cast at h1
      linarith
    have hfac : 0 ≤ (2 / bmin) * Real.sqrt ε := mul_nonneg hbi hsn
    have := mul_le_mul_of_nonneg_left hlog hfac
    have e : (4 / bmin) * Real.sqrt ε * Real.log (1 + (h u0 + wt u0) / Real.sqrt ε)
        = (2 / bmin) * Real.sqrt ε * (2 * Real.log (1 + (h u0 + wt u0) / Real.sqrt ε)) := by ring
    rw [e]
    exact this
  by_cases hex : ∃ u ∈ Icc (0 : ℝ) u0, Y u ≤ T * ε
  · obtain ⟨u1, hu1, hYu1⟩ := hex
    obtain ⟨-, -, û, hfirst, hûpos, -, -, -, -⟩ := lem_app_phase_mixture a b w c bmin hbmin ha hF0
      hb hw hw1 hc hT hε hεF rfl rfl hYc hYpos hY
    have hle : firstHit Y (T * ε) ≤ ENNReal.ofReal u1 := tp_firstHit_le Y (T * ε) u1 hu1.1 hYu1
    have hû : û ≤ u0 := by
      rw [hfirst] at hle
      exact (ENNReal.ofReal_le_ofReal_iff hu0.le).1 (hle.trans (ENNReal.ofReal_le_ofReal hu1.2))
    have hcont : ContinuousOn (fun v => Real.sqrt (Y v)) (Ici 0) :=
      Real.continuous_sqrt.comp_continuousOn hYc
    have hint0 : IntervalIntegrable (fun v => Real.sqrt (Y v)) volume 0 u0 :=
      ContinuousOn.intervalIntegrable_of_Icc hu0.le (hcont.mono fun x hx => Set.mem_Ici.2 hx.1)
    have hmono : ∫ u in (0:ℝ)..û, Real.sqrt (Y u) ≤ ∫ u in (0:ℝ)..u0, Real.sqrt (Y u) :=
      intervalIntegral.integral_mono_interval le_rfl hûpos.le hû
        (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg (Y x)) hint0
    exact ⟨û, hfirst, le_add_of_le_of_nonneg hmono (sq_nonneg _), hJ_bound, hD_bound⟩
  · push_neg at hex
    obtain ⟨û, hfirst, hû0, -, hint⟩ := lem_app_phase_restart a b w c bmin hbmin ha hF0 hb hw hw1 hc
      hT hε hu0.le hYc hYpos hY hex
    have hcont : ContinuousOn (fun v => Real.sqrt (Y v)) (Ici 0) :=
      Real.continuous_sqrt.comp_continuousOn hYc
    have hi1 : IntervalIntegrable (fun v => Real.sqrt (Y v)) volume 0 u0 :=
      ContinuousOn.intervalIntegrable_of_Icc hu0.le (hcont.mono fun x hx => Set.mem_Ici.2 hx.1)
    have hi2 : IntervalIntegrable (fun v => Real.sqrt (Y v)) volume u0 û :=
      ContinuousOn.intervalIntegrable_of_Icc hû0.le
        (hcont.mono fun x hx => Set.mem_Ici.2 (le_trans hu0.le hx.1))
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    refine ⟨û, hfirst, ?_, hJ_bound, hD_bound⟩
    rw [← hsplit]
    linarith

/-! ## Kernels with a slow part -/

lemma ir_le_aux (r x : ℝ) (hr : r < 1) (hx : 0 ≤ x) :
    ∫ w in (0 : ℝ)..x, (1 + w) ^ (-r) ≤ (1 + x) ^ (1 - r) / (1 - r) := by
  have hr1 : (1 - r) ≠ 0 := by linarith
  have hpos : 0 < 1 - r := by linarith
  have hderiv : ∀ w ∈ uIcc (0:ℝ) x,
      HasDerivAt (fun y : ℝ => (1 + y) ^ (1 - r) / (1 - r)) ((1 + w) ^ (-r)) w := by
    intro w hw
    have hw0 : 0 ≤ w := by
      rcases Set.mem_uIcc.1 hw with h | h
      · exact h.1
      · linarith [h.1]
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 w := by
      simpa using (hasDerivAt_id w).const_add 1
    have h2 := (h1.rpow_const (p := 1 - r) (Or.inl (by linarith)))
    have h3 := h2.div_const (1 - r)
    convert h3 using 1
    field_simp
    ring_nf
  have hint : IntervalIntegrable (fun w : ℝ => (1 + w) ^ (-r)) volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const
    · exact (continuousOn_const.add continuousOn_id)
    · intro w hw
      left
      have : 0 ≤ w := by
        rcases Set.mem_uIcc.1 hw with h | h
        · exact h.1
        · linarith [h.1]
      linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h0 : (1 + (0:ℝ)) ^ (1 - r) / (1 - r) = 1 / (1 - r) := by simp
  rw [h0]
  have : 0 ≤ (1 + x) ^ (1 - r) := Real.rpow_nonneg (by linarith) _
  have hle : (1:ℝ) / (1 - r) ≤ 0 ∨ True := Or.inr trivial
  have h5 : 0 ≤ 1 / (1 - r) := by positivity
  have h6 : (1 + x) ^ (1 - r) / (1 - r) - 1 / (1 - r) ≤ (1 + x) ^ (1 - r) / (1 - r) := by
    linarith
  exact h6


lemma split_tail_aux {r0 Ks d b N q D C u I : ℝ} (hr0 : r0 < 1) (hKs : 0 ≤ Ks)
    (hd : 0 ≤ d) (hN : 1 ≤ N) (hD : 1 ≤ D) (hC : 0 < C) (hu : 0 ≤ u)
    (hI : I ≤ (1 + u / D) ^ (1 - r0) / (1 - r0)) :
    Ks * d ^ (-b) * N ^ (-q) * ((D + u) / N ^ q) ^ (-b) * (C * D * I)
      ≤ Ks * d ^ (-b) / (1 - r0) * ((D + u) / N ^ q) ^ (1 - b) * (C * (1 + u / D) ^ (-r0)) := by
  have hN0 : 0 < N := by linarith
  have hDpos : 0 < D := by linarith
  have hr1 : 0 < 1 - r0 := by linarith
  have hP : 0 < 1 + u / D := by have := div_nonneg hu hDpos.le; linarith
  set x := u / D with hx
  set P := 1 + x with hPdef
  set H := P ^ (-r0) with hH
  have hH0 : 0 ≤ H := Real.rpow_nonneg hP.le _
  have hPpow : P ^ (1 - r0) = H * P := by
    rw [hH, show (1 - r0) = -r0 + 1 by ring, Real.rpow_add hP, Real.rpow_one]
  have hS : D * P = D + u := by
    rw [hPdef, hx]; field_simp
  set S := D + u with hSdef
  set M := N ^ (-q) with hM
  have hM0 : 0 ≤ M := Real.rpow_nonneg hN0.le _
  have hMq : M = (N ^ q)⁻¹ := by rw [hM, Real.rpow_neg hN0.le]
  set A := S / N ^ q with hAdef
  have hA : A = M * S := by rw [hAdef, hMq]; ring
  have hApos : 0 < A := by
    rw [hAdef]; apply div_pos _ (Real.rpow_pos_of_pos hN0 _); linarith
  have hA0 : 0 ≤ A := hApos.le
  set X := A ^ (-b) with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg hA0 _
  have hA1 : A ^ (1 - b) = X * A := by
    rw [hX, show (1 - b) = -b + 1 by ring, Real.rpow_add hApos, Real.rpow_one]
  have hQ : 0 ≤ Ks * d ^ (-b) := mul_nonneg hKs (Real.rpow_nonneg hd _)
  have hDI : D * I ≤ S * H / (1 - r0) := by
    have h1 : D * I ≤ D * (P ^ (1 - r0) / (1 - r0)) := mul_le_mul_of_nonneg_left hI hDpos.le
    have h2 : D * (P ^ (1 - r0) / (1 - r0)) = S * H / (1 - r0) := by
      rw [hPpow, ← hS]; ring
    linarith
  calc Ks * d ^ (-b) * N ^ (-q) * A ^ (-b) * (C * D * I)
      = (Ks * d ^ (-b)) * M * X * (C * (D * I)) := by rw [hX, hAdef]; ring
    _ ≤ (Ks * d ^ (-b)) * M * X * (C * (S * H / (1 - r0))) := by
        apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDI hC.le)
        positivity
    _ = Ks * d ^ (-b) / (1 - r0) * (X * A) * (C * H) := by rw [hA]; ring
    _ = Ks * d ^ (-b) / (1 - r0) * A ^ (1 - b) * (C * H) := by rw [hA1]
    _ = _ := by rw [hH]



lemma tp_delta_facts (r0 : ℝ) (hr0 : 0 < r0) :
    0 < dilDelta r0 ∧ dilDelta r0 < 1 ∧ (1 - dilDelta r0) ^ r0 = 2 / 3 := by
  have hpos : (0:ℝ) < (2 / 3 : ℝ) ^ (1 / r0) := Real.rpow_pos_of_pos (by norm_num) _
  have hlt : (2 / 3 : ℝ) ^ (1 / r0) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  refine ⟨by unfold dilDelta; linarith, by unfold dilDelta; linarith, ?_⟩
  unfold dilDelta
  rw [show 1 - (1 - (2 / 3 : ℝ) ^ (1 / r0)) = (2 / 3 : ℝ) ^ (1 / r0) by ring,
    ← Real.rpow_mul (by norm_num), one_div_mul_cancel hr0.ne', Real.rpow_one]

lemma tp_early_ratio (a δ r0 s : ℝ) (ha : 0 < a) (hr0 : 0 < r0)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hδr : (1 - δ) ^ r0 = 2 / 3)
    (hs0 : 0 ≤ s) (hs : s ≤ δ * a) :
    (a - s) ^ (-r0) * a ^ r0 ≤ 3 / 2 := by
  have h1a : 0 < (1 - δ) * a := mul_pos (by linarith) ha
  have hle : (1 - δ) * a ≤ a - s := by nlinarith
  have hpow : (a - s) ^ (-r0) ≤ ((1 - δ) * a) ^ (-r0) :=
    Real.rpow_le_rpow_of_nonpos h1a hle (by linarith)
  have hmul : ((1 - δ) * a) ^ (-r0) = (1 - δ) ^ (-r0) * a ^ (-r0) :=
    Real.mul_rpow (by linarith) ha.le
  have harp : a ^ r0 * a ^ (-r0) = 1 := by
    rw [Real.rpow_neg ha.le]; field_simp
  have hinv : (1 - δ) ^ (-r0) = 3 / 2 := by
    rw [Real.rpow_neg (by linarith), hδr]; norm_num
  have hpos : 0 ≤ a ^ r0 := Real.rpow_nonneg ha.le _
  calc (a - s) ^ (-r0) * a ^ r0 ≤ ((1 - δ) * a) ^ (-r0) * a ^ r0 :=
        mul_le_mul_of_nonneg_right hpow hpos
    _ = (1 - δ) ^ (-r0) * (a ^ (-r0) * a ^ r0) := by rw [hmul]; ring
    _ = 3 / 2 := by rw [mul_comm (a ^ (-r0)), harp, hinv, mul_one]

lemma tp_ratio_id (u D s r0 : ℝ) (hD : 0 < D) (hu : 0 ≤ u) (hs : s ≤ u) :
    (1 + (u - s) / D) ^ (-r0) = (1 + u / D) ^ (-r0) * ((D + u - s) ^ (-r0) * (D + u) ^ r0) := by
  have h1 : 1 + (u - s) / D = (D + u - s) / D := by field_simp; ring
  have h2 : 1 + u / D = (D + u) / D := by field_simp
  have hp1 : 0 ≤ D + u - s := by linarith
  have hp2 : 0 ≤ D + u := by linarith
  have harp : (D + u) ^ (-r0) * (D + u) ^ r0 = 1 := by
    rw [Real.rpow_neg (by linarith)]; field_simp
  rw [h1, h2, Real.div_rpow hp1 hD.le, Real.div_rpow hp2 hD.le]
  rw [show (D + u) ^ (-r0) / D ^ (-r0) * ((D + u - s) ^ (-r0) * (D + u) ^ r0)
      = ((D + u) ^ (-r0) * (D + u) ^ r0) * (D + u - s) ^ (-r0) / D ^ (-r0) by ring, harp, one_mul]

lemma tp_log_sup (x c : ℝ) (hx : 0 < x) (hc : 0 < c) :
    x ^ (-c) * Real.log x ≤ 1 / (Real.exp 1 * c) := by
  have hl : ∀ y : ℝ, 0 < y → Real.log y ≤ y / Real.exp 1 := by
    intro y hy
    have := Real.log_le_sub_one_of_pos (div_pos hy (Real.exp_pos 1))
    rw [Real.log_div hy.ne' (Real.exp_pos 1).ne', Real.log_exp] at this
    linarith
  have h2 : c * Real.log x ≤ x ^ c / Real.exp 1 := by
    rw [← Real.log_rpow hx]; exact hl _ (Real.rpow_pos_of_pos hx c)
  have h3 : Real.exp 1 * (c * Real.log x) ≤ x ^ c := by
    have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le
    rwa [mul_div_cancel₀ _ (Real.exp_pos 1).ne'] at this
  have h4 : Real.log x ≤ x ^ c / (Real.exp 1 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h5 : x ^ (-c) * (x ^ c / (Real.exp 1 * c)) = 1 / (Real.exp 1 * c) := by
    rw [Real.rpow_neg hx.le]
    field_simp
  calc x ^ (-c) * Real.log x ≤ x ^ (-c) * (x ^ c / (Real.exp 1 * c)) :=
        mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hx.le _)
    _ = 1 / (Real.exp 1 * c) := h5

lemma tp_J_gt (D M r0 : ℝ) (hD : 0 < D) (hDM : D ≤ M) (hr1 : 1 < r0) :
    ∫ t in D..M, t ^ (-r0) ≤ D ^ (1 - r0) / (r0 - 1) := by
  have hn : (1 - r0) ≠ 0 := by intro h; linarith
  have hp : (r0 - 1) ≠ 0 := by intro h; linarith
  rw [integral_rpow (Or.inr ⟨by intro h; linarith, fun h => by
      rw [uIcc_of_le hDM] at h; linarith [h.1]⟩), show -r0 + 1 = 1 - r0 by ring]
  have e : (M ^ (1 - r0) - D ^ (1 - r0)) / (1 - r0)
      = (D ^ (1 - r0) - M ^ (1 - r0)) / (r0 - 1) := by
    rw [div_eq_div_iff hn hp]; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith [Real.rpow_nonneg (le_trans hD.le hDM) (1 - r0)]

lemma tp_Ir_eq (r z : ℝ) :
    Ir r z = ∫ x in (1 : ℝ)..(1 + z), x ^ (-r) := by
  unfold Ir
  have key : ∫ w in (0 : ℝ)..z, (1 + w) ^ (-r) = ∫ x in (1 + 0 : ℝ)..(1 + z), x ^ (-r) :=
    intervalIntegral.integral_comp_add_left (fun x : ℝ => x ^ (-r)) 1
  rw [key, add_zero]

/-- the bound `(1+z)^{r0-υ} I_{r0}(z) ≤ b(r0,υ)` from the proof of `lem:app-phase-dilation`. -/
lemma tp_fast_bound (r0 υ z : ℝ) (hr0 : 0 < r0) (hυ : 1 < υ) (hr0υ : r0 ≤ υ)
    (hz : 0 ≤ z) : (1 + z) ^ (r0 - υ) * Ir r0 z ≤ dilB r0 υ := by
  have hP : 0 < 1 + z := by linarith
  have hP1 : 1 ≤ 1 + z := by linarith
  rcases lt_trichotomy r0 1 with hr | hr | hr
  · have hb : dilB r0 υ = (1 - r0)⁻¹ := by unfold dilB; simp [hr]
    rw [hb]
    have hI := ir_le_aux r0 z hr hz
    have hr' : 0 < 1 - r0 := by linarith
    have h1 : (1 + z) ^ (r0 - υ) * (1 + z) ^ (1 - r0) ≤ 1 := by
      rw [← Real.rpow_add hP]
      exact Real.rpow_le_one_of_one_le_of_nonpos hP1 (by linarith)
    have hnn : 0 ≤ (1 + z) ^ (r0 - υ) := Real.rpow_nonneg hP.le _
    calc (1 + z) ^ (r0 - υ) * Ir r0 z
        ≤ (1 + z) ^ (r0 - υ) * ((1 + z) ^ (1 - r0) / (1 - r0)) :=
          mul_le_mul_of_nonneg_left hI hnn
      _ = ((1 + z) ^ (r0 - υ) * (1 + z) ^ (1 - r0)) / (1 - r0) := by ring
      _ ≤ 1 / (1 - r0) := div_le_div_of_nonneg_right h1 hr'.le
      _ = (1 - r0)⁻¹ := by rw [one_div]
  · subst hr
    have hb : dilB 1 υ = (Real.exp 1 * (υ - 1))⁻¹ := by unfold dilB; simp
    rw [hb]
    have hI : Ir 1 z = Real.log (1 + z) := by
      rw [tp_Ir_eq]
      simp only [Real.rpow_neg_one]
      rw [integral_inv_of_pos one_pos hP]
      simp
    rw [hI]
    have hc : 0 < υ - 1 := by linarith
    have := tp_log_sup (1 + z) (υ - 1) hP hc
    rw [show (1 : ℝ) - υ = -(υ - 1) by ring]
    rw [one_div] at this
    exact this
  · have hb : dilB r0 υ = (r0 - 1)⁻¹ := by
      unfold dilB
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by linarith)), if_neg (by linarith)]
    rw [hb]
    have hp : 0 < r0 - 1 := by linarith
    have hJ := tp_J_gt 1 (1 + z) r0 one_pos hP1 hr
    have hI : Ir r0 z ≤ (r0 - 1)⁻¹ := by
      rw [tp_Ir_eq]
      calc _ ≤ (1 : ℝ) ^ (1 - r0) / (r0 - 1) := hJ
        _ = (r0 - 1)⁻¹ := by rw [Real.one_rpow, one_div]
    have h1 : (1 + z) ^ (r0 - υ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hP1 (by linarith)
    have hnn : 0 ≤ (1 + z) ^ (r0 - υ) := Real.rpow_nonneg hP.le _
    have hIn : 0 ≤ Ir r0 z := by
      unfold Ir
      exact intervalIntegral.integral_nonneg hz (fun w hw => Real.rpow_nonneg (by linarith [hw.1]) _)
    calc (1 + z) ^ (r0 - υ) * Ir r0 z ≤ 1 * (r0 - 1)⁻¹ :=
          mul_le_mul h1 hI hIn (by norm_num)
      _ = (r0 - 1)⁻¹ := one_mul _


lemma tp_conv_core
    {g : ℝ → ℝ} {u D C r0 δ M : ℝ} (hu0 : 0 ≤ u)
    (hgcu : ContinuousOn g (Icc 0 u)) (hgnn : ∀ v ∈ Icc (0 : ℝ) u, 0 ≤ g v)
    (hD : 0 < D) (hC : 0 < C) (hr0 : 0 < r0)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδr : (1 - δ) ^ r0 = 2 / 3) (hM0 : 0 ≤ M)
    (hgM : ∀ s ∈ Icc (0 : ℝ) u, δ * (D + u) < s → g s ≤ M) :
    oneSidedConv (fun w => C * (1 + w / D) ^ (-r0)) g u
      ≤ 3 / 2 * (∫ s in (0:ℝ)..u, g s) * (C * (1 + u / D) ^ (-r0))
        + M * (C * D * Ir r0 (u / D)) := by
  have hDp := hD
  set a := D + u with hadef
  have ha : 0 < a := by linarith
  have hδa : 0 < δ * a := mul_pos hδ0 ha
  set hu := C * (1 + u / D) ^ (-r0) with hhu
  have hz : 0 ≤ u / D := div_nonneg hu0 hDp.le
  have hP : 0 < 1 + u / D := by linarith
  have hhu0 : 0 ≤ hu := mul_nonneg hC.le (Real.rpow_nonneg hP.le _)
  set h' : ℝ → ℝ := fun s => C * (1 + (u - s) / D) ^ (-r0) with hh'
  have hh'nn : ∀ s, s ≤ u → 0 ≤ h' s := by
    intro s hs
    have : 0 ≤ (u - s) / D := div_nonneg (by linarith) hDp.le
    exact mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
  have hh'c : ContinuousOn h' (Icc 0 u) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const (by fun_prop)
    intro s hs
    left
    have : 0 ≤ (u - s) / D := div_nonneg (by linarith [hs.2]) hDp.le
    have : 0 < 1 + (u - s) / D := by linarith
    exact this.ne'
  have hgI : IntervalIntegrable g volume 0 u :=
    ContinuousOn.intervalIntegrable_of_Icc hu0 hgcu
  have hh'I : IntervalIntegrable h' volume 0 u :=
    ContinuousOn.intervalIntegrable_of_Icc hu0 hh'c
  have hpt : ∀ s ∈ Icc (0 : ℝ) u, h' s * g s ≤ (3 / 2 * hu) * g s + M * h' s := by
    intro s hs
    have hgs := hgnn s hs
    have hh's := hh'nn s hs.2
    by_cases hsc : s ≤ δ * a
    · have hR := tp_early_ratio a δ r0 s ha hr0 hδ0 hδ1 hδr hs.1 hsc
      have hid : h' s = hu * ((a - s) ^ (-r0) * a ^ r0) := by
        simp only [hh', hhu]
        rw [tp_ratio_id u D s r0 hDp hu0 hs.2]
        ring
      have h1 : h' s * g s ≤ (3 / 2 * hu) * g s := by
        rw [hid]
        have : hu * ((a - s) ^ (-r0) * a ^ r0) ≤ hu * (3 / 2) :=
          mul_le_mul_of_nonneg_left hR hhu0
        nlinarith
      have h2 : 0 ≤ M * h' s := mul_nonneg hM0 hh's
      linarith
    · push_neg at hsc
      have hgM' : g s ≤ M := hgM s hs hsc
      have h1 : h' s * g s ≤ M * h' s := by nlinarith
      have h2 : 0 ≤ (3 / 2 * hu) * g s := mul_nonneg (by linarith) hgs
      linarith
  have hconv : oneSidedConv (fun w => C * (1 + w / D) ^ (-r0)) g u = ∫ s in (0:ℝ)..u, h' s * g s := rfl
  have hint1 : ∫ s in (0:ℝ)..u, h' s * g s
      ≤ ∫ s in (0:ℝ)..u, ((3 / 2 * hu) * g s + M * h' s) := by
    apply intervalIntegral.integral_mono_on hu0
    · exact (hh'c.mul hgcu).intervalIntegrable_of_Icc hu0
    · exact (hgI.const_mul _).add (hh'I.const_mul _)
    · exact hpt
  have hsum : ∫ s in (0:ℝ)..u, ((3 / 2 * hu) * g s + M * h' s)
      = (3 / 2 * hu) * (∫ s in (0:ℝ)..u, g s) + M * (∫ s in (0:ℝ)..u, h' s) := by
    rw [intervalIntegral.integral_add (hgI.const_mul _) (hh'I.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hh'int : ∫ s in (0:ℝ)..u, h' s = C * D * Ir r0 (u / D) := by
    have e1 : ∫ s in (0:ℝ)..u, h' s = ∫ x in (u - u)..(u - 0), C * (1 + x / D) ^ (-r0) :=
      intervalIntegral.integral_comp_sub_left (fun x : ℝ => C * (1 + x / D) ^ (-r0)) u
    rw [e1, sub_self, sub_zero, intervalIntegral.integral_const_mul]
    have e2 : ∫ x in (0:ℝ)..u, (1 + x / D) ^ (-r0) = D * ∫ x in (0 / D)..(u / D), (1 + x) ^ (-r0) :=
      by
        have := intervalIntegral.integral_comp_div (a := (0:ℝ)) (b := u) (fun x : ℝ => (1 + x) ^ (-r0)) hDp.ne'
        simpa using this
    rw [e2]; unfold Ir; rw [zero_div]; ring
  rw [hconv]
  rw [hh'int] at hsum
  calc _ ≤ _ := hint1
    _ = _ := by rw [hsum]; ring

lemma tp_split_conv
    {g : ℝ → ℝ} {u : ℝ} (hu0 : 0 ≤ u)
    (hgcu : ContinuousOn g (Icc 0 u)) (hgnn : ∀ v ∈ Icc (0 : ℝ) u, 0 ≤ g v)
    (hgm : ∫ s in (0:ℝ)..u, g s ≤ 1)
    {Kf Ks υ b N q D C r0 : ℝ} (hKf : 0 ≤ Kf) (hKs : 0 ≤ Ks) (hυ : 1 < υ)
    (hb0 : 0 ≤ b) (hN : 1 ≤ N)
    (hr0 : 0 < r0) (hr0υ : r0 ≤ υ) (hD : 1 ≤ D) (hC : 0 < C)
    (htemp : ∀ v : ℝ, 0 ≤ v → v ≤ u →
      g v ≤ Kf * (1 + v) ^ (-υ) + Ks * N ^ (-q) * ((1 + v) / N ^ q) ^ (-b)) :
    oneSidedConv (fun w => C * (1 + w / D) ^ (-r0)) g u
          ≤ (3 / 2 + Kf * dilDelta r0 ^ (-υ) * D ^ (1 - υ) * dilB r0 υ) * (C * (1 + u / D) ^ (-r0))
            + Ks * dilDelta r0 ^ (-b) * N ^ (-q) * ((D + u) / N ^ q) ^ (-b)
              * (C * D * Ir r0 (u / D)) := by
  obtain ⟨hδ0, hδ1, hδr⟩ := tp_delta_facts r0 hr0
  set δ := dilDelta r0 with hδdef
  have hDp : 0 < D := by linarith
  have hN0 : 0 < N := by linarith
  have hNq : 0 < N ^ q := Real.rpow_pos_of_pos hN0 _
  set a := D + u with hadef
  have ha : 0 < a := by linarith
  have hδa : 0 < δ * a := mul_pos hδ0 ha
  set hu := C * (1 + u / D) ^ (-r0) with hhu
  have hz : 0 ≤ u / D := div_nonneg hu0 hDp.le
  have hP : 0 < 1 + u / D := by linarith
  have hhu0 : 0 ≤ hu := mul_nonneg hC.le (Real.rpow_nonneg hP.le _)
  set M := Kf * (δ * a) ^ (-υ) + Ks * N ^ (-q) * (δ * a / N ^ q) ^ (-b) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    have h1 : 0 ≤ Kf * (δ * a) ^ (-υ) := mul_nonneg hKf (Real.rpow_nonneg hδa.le _)
    have h2 : 0 ≤ Ks * N ^ (-q) * (δ * a / N ^ q) ^ (-b) :=
      mul_nonneg (mul_nonneg hKs (Real.rpow_nonneg hN0.le _))
        (Real.rpow_nonneg (div_nonneg hδa.le hNq.le) _)
    linarith
  have hgM : ∀ s ∈ Icc (0 : ℝ) u, δ * (D + u) < s → g s ≤ M := by
    intro s hs hsc
    have hgT := htemp s hs.1 hs.2
    have hpow1 : (1 + s) ^ (-υ) ≤ (δ * a) ^ (-υ) :=
      Real.rpow_le_rpow_of_nonpos hδa (by linarith) (by linarith)
    have hpow2 : ((1 + s) / N ^ q) ^ (-b) ≤ (δ * a / N ^ q) ^ (-b) :=
      Real.rpow_le_rpow_of_nonpos (div_pos hδa hNq)
        (div_le_div_of_nonneg_right (by linarith) hNq.le) (by linarith)
    have e1 : Kf * (1 + s) ^ (-υ) ≤ Kf * (δ * a) ^ (-υ) :=
      mul_le_mul_of_nonneg_left hpow1 hKf
    have e2 : Ks * N ^ (-q) * ((1 + s) / N ^ q) ^ (-b)
        ≤ Ks * N ^ (-q) * (δ * a / N ^ q) ^ (-b) :=
      mul_le_mul_of_nonneg_left hpow2 (mul_nonneg hKs (Real.rpow_nonneg hN0.le _))
    rw [hM]; linarith
  have hcore := tp_conv_core hu0 hgcu hgnn hDp hC hr0 hδ0 hδ1 hδr hM0 hgM
  have hgnn' : 0 ≤ ∫ s in (0:ℝ)..u, g s := intervalIntegral.integral_nonneg hu0
      (fun v hv => hgnn v hv)
  have hstep1 : oneSidedConv (fun w => C * (1 + w / D) ^ (-r0)) g u
      ≤ 3 / 2 * hu + M * (C * D * Ir r0 (u / D)) := by
    have : 3 / 2 * (∫ s in (0:ℝ)..u, g s) * hu ≤ 3 / 2 * hu := by
      have := mul_le_mul_of_nonneg_left hgm (by linarith : 0 ≤ 3 / 2 * hu)
      nlinarith
    linarith [hcore]
  -- final algebra
  have hIr0 : 0 ≤ Ir r0 (u / D) := by
    unfold Ir
    exact intervalIntegral.integral_nonneg hz (fun w hw => Real.rpow_nonneg (by linarith [hw.1]) _)
  have haD : a = D * (1 + u / D) := by rw [hadef]; field_simp
  have hmulδ : (δ * a) ^ (-υ) = δ ^ (-υ) * a ^ (-υ) := Real.mul_rpow hδ0.le ha.le
  have hmulδ2 : (δ * a / N ^ q) ^ (-b) = δ ^ (-b) * (a / N ^ q) ^ (-b) := by
    rw [mul_div_assoc]; exact Real.mul_rpow hδ0.le (div_pos ha hNq).le
  have hfast : Kf * (δ * a) ^ (-υ) * (C * D * Ir r0 (u / D))
      ≤ Kf * δ ^ (-υ) * D ^ (1 - υ) * dilB r0 υ * hu := by
    have hB := tp_fast_bound r0 υ (u / D) hr0 hυ hr0υ hz
    have hsplit : a ^ (-υ) = D ^ (-υ) * (1 + u / D) ^ (-υ) := by
      rw [haD]; exact Real.mul_rpow hDp.le hP.le
    have hDD : D * D ^ (-υ) = D ^ (1 - υ) := by
      rw [show (1 - υ) = 1 + -υ by ring, Real.rpow_add hDp, Real.rpow_one]
    have hPe : (1 + u / D) ^ (-υ) = (1 + u / D) ^ (-r0) * (1 + u / D) ^ (r0 - υ) := by
      rw [← Real.rpow_add hP]; congr 1; ring
    have hKd : 0 ≤ Kf * δ ^ (-υ) := mul_nonneg hKf (Real.rpow_nonneg hδ0.le _)
    have hPr : 0 ≤ (1 + u / D) ^ (-r0) := Real.rpow_nonneg hP.le _
    calc Kf * (δ * a) ^ (-υ) * (C * D * Ir r0 (u / D))
        = (Kf * δ ^ (-υ)) * (D * D ^ (-υ)) * C * ((1 + u / D) ^ (-r0) * ((1 + u / D) ^ (r0 - υ) * Ir r0 (u / D))) := by
          rw [hmulδ, hsplit, hPe]; ring
      _ ≤ (Kf * δ ^ (-υ)) * (D * D ^ (-υ)) * C * ((1 + u / D) ^ (-r0) * dilB r0 υ) := by
          apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hPr)
          have := Real.rpow_nonneg hDp.le (-υ)
          positivity
      _ = Kf * δ ^ (-υ) * D ^ (1 - υ) * dilB r0 υ * hu := by
          rw [hDD, hhu]; ring
  have hslow : Ks * N ^ (-q) * (δ * a / N ^ q) ^ (-b) * (C * D * Ir r0 (u / D))
      = Ks * δ ^ (-b) * N ^ (-q) * ((D + u) / N ^ q) ^ (-b) * (C * D * Ir r0 (u / D)) := by
    rw [hmulδ2]; ring
  have hMe : M * (C * D * Ir r0 (u / D)) = Kf * (δ * a) ^ (-υ) * (C * D * Ir r0 (u / D))
      + Ks * N ^ (-q) * (δ * a / N ^ q) ^ (-b) * (C * D * Ir r0 (u / D)) := by
    rw [hM]; ring
  rw [hMe] at hstep1
  rw [hslow] at hstep1
  linarith

lemma tp_slow_le {Ks r0 b N q D C u : ℝ} (hr1 : r0 < 1) (hr0 : 0 < r0) (hKs : 0 ≤ Ks)
    (hN : 1 ≤ N) (hD : 1 ≤ D) (hC : 0 < C) (hu0 : 0 ≤ u) :
    Ks * dilDelta r0 ^ (-b) * N ^ (-q) * ((D + u) / N ^ q) ^ (-b) * (C * D * Ir r0 (u / D))
      ≤ Ks * dilDelta r0 ^ (-b) / (1 - r0) * ((D + u) / N ^ q) ^ (1 - b)
        * (C * (1 + u / D) ^ (-r0)) := by
  have hδ : 0 ≤ dilDelta r0 := (tp_delta_facts r0 hr0).1.le
  have hI : Ir r0 (u / D) ≤ (1 + u / D) ^ (1 - r0) / (1 - r0) := by
    unfold Ir
    exact ir_le_aux r0 (u / D) hr1 (div_nonneg hu0 (by linarith))
  exact split_tail_aux hr1 hKs hδ hN hD hC hu0 hI

/-- `lem:app-phase-split`, snapshot `cr-2026-10-23`.
Source: `sections/07-phase-comparison/section.tex` l.3232–3248.

LaTeX (verbatim, `section.tex` l.3232–3248):
```latex
\begin{lemma}[Kernel with a slow part]\label{lem:app-phase-split}
Let $g\ge0$ be continuous with $\int_0^\infty g\le1$, and suppose that for
$0\le v\le U_0$
\begin{equation}\label{eqn:app-phase-template}
g(v)\le K_f(1+v)^{-\upsilon}+K_sN^{-q}\Big(\frac{1+v}{N^q}\Big)^{-\mathsf b},
\end{equation}
with $K_f,K_s\ge0$, $\upsilon>1$, $0\le\mathsf b<1$, $N\ge1$ and $q>0$. Let
$0<r_0\le\upsilon$, $D\ge1$, $C>0$, $h(u)\defeq C(1+u/D)^{-r_0}$,
$\delta_\circ=1-(2/3)^{1/r_0}$ and
$\mathsf k_f\defeq K_f\delta_\circ^{-\upsilon}D^{1-\upsilon}b(r_0,\upsilon)$, with $b(r_0,\upsilon)$ of
\cref{eqn:app-phase-dilation}. Then for $0\le u\le U_0$,
\[
(g*h)(u)\le\Big(\frac32+\mathsf k_f\Big)h(u)+K_s\delta_\circ^{-\mathsf b}N^{-q}\Big(\frac{D+u}{N^q}\Big)^{-\mathsf b}C\,D\,I_{r_0}(u/D),
\]
and if $r_0<1$ the last term is at most
$\frac{K_s\delta_\circ^{-\mathsf b}}{1-r_0}\big(\frac{D+u}{N^q}\big)^{1-\mathsf b}h(u)$.
\end{lemma}
```
-/
theorem lem_app_phase_split
    {g : ℝ → ℝ} (hgc : ContinuousOn g (Ici 0)) (hgnn : ∀ v ∈ Ici (0 : ℝ), 0 ≤ g v)
    (hgi : IntegrableOn g (Ioi 0)) (hgint : ∫ v in Ioi (0 : ℝ), g v ≤ 1)
    {Kf Ks υ b N q U0 D C r0 : ℝ} (hKf : 0 ≤ Kf) (hKs : 0 ≤ Ks) (hυ : 1 < υ)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hN : 1 ≤ N) (hq : 0 < q)
    (hr0 : 0 < r0) (hr0υ : r0 ≤ υ) (hD : 1 ≤ D) (hC : 0 < C)
    (htemp : phaseTemplate g N U0 q Kf Ks υ b) :
    (∀ u : ℝ, 0 ≤ u → u ≤ U0 →
        oneSidedConv (fun w => C * (1 + w / D) ^ (-r0)) g u
          ≤ (3 / 2 + Kf * dilDelta r0 ^ (-υ) * D ^ (1 - υ) * dilB r0 υ) * (C * (1 + u / D) ^ (-r0))
            + Ks * dilDelta r0 ^ (-b) * N ^ (-q) * ((D + u) / N ^ q) ^ (-b)
              * (C * D * Ir r0 (u / D))) ∧
      (r0 < 1 → ∀ u : ℝ, 0 ≤ u → u ≤ U0 →
        Ks * dilDelta r0 ^ (-b) * N ^ (-q) * ((D + u) / N ^ q) ^ (-b) * (C * D * Ir r0 (u / D))
          ≤ Ks * dilDelta r0 ^ (-b) / (1 - r0) * ((D + u) / N ^ q) ^ (1 - b)
            * (C * (1 + u / D) ^ (-r0))) := by
  refine ⟨fun u hu0 huU => ?_, fun hr1 u hu0 _ => ?_⟩
  · have hgcu : ContinuousOn g (Icc 0 u) := hgc.mono (fun v hv => hv.1)
    have hgnn' : ∀ v ∈ Icc (0 : ℝ) u, 0 ≤ g v := fun v hv => hgnn v (Set.mem_Ici.mpr hv.1)
    have hgm : ∫ s in (0:ℝ)..u, g s ≤ 1 := by
      rw [intervalIntegral.integral_of_le hu0]
      refine le_trans ?_ hgint
      apply setIntegral_mono_set hgi
      · exact (ae_restrict_iff' measurableSet_Ioi).mpr
          (Filter.Eventually.of_forall fun v hv => hgnn v (Set.mem_Ici.mpr (Set.mem_Ioi.mp hv).le))
      · exact Filter.Eventually.of_forall (fun x (hx : x ∈ Ioc (0:ℝ) u) => (hx.1 : x ∈ Ioi 0))
    exact tp_split_conv hu0 hgcu hgnn' hgm hKf hKs hυ hb0 hN hr0 hr0υ hD hC
      (fun v hv0 hvu => htemp v hv0 (le_trans hvu huU))
  · exact tp_slow_le hr1 hr0 hKs hN hD hC hu0


lemma tp_Lsum_fin (N : ℕ) (a q u : ℝ) :
    Lsum (N : ℕ∞) a q u
      = ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) := by
  unfold Lsum
  rw [tsum_eq_sum (s := Finset.Icc 1 N)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h1 : 0 < n ∧ ((n : ℕ∞) ≤ (N : ℕ∞)) := ⟨by omega, by exact_mod_cast hn.2⟩
    rw [if_pos h1]
  · intro b hb
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hb
    rw [Finset.mem_Icc]
    exact ⟨by omega, by exact_mod_cast h2⟩

lemma tp_Lsum_cont (N : ℕ) (a q : ℝ) : Continuous (Lsum (N : ℕ∞) a q) := by
  have : Lsum (N : ℕ∞) a q = fun u => ∑ i ∈ Finset.Icc 1 N,
      (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) := funext (tp_Lsum_fin N a q)
  rw [this]
  fun_prop

lemma tp_Lsum_nonneg (N : ℕ) (a q u : ℝ) : 0 ≤ Lsum (N : ℕ∞) a q u := by
  rw [tp_Lsum_fin]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _)
    (Real.exp_pos _).le)

lemma tp_Lsum_anti (N : ℕ) (a q : ℝ) : Antitone (Lsum (N : ℕ∞) a q) := by
  intro x y hxy
  rw [tp_Lsum_fin, tp_Lsum_fin]
  apply Finset.sum_le_sum
  intro i _
  have hk : 0 ≤ (i : ℝ) ^ (-q) := Real.rpow_nonneg (Nat.cast_nonneg i) _
  have hexp : Real.exp (-(2 * y) * (i : ℝ) ^ (-q)) ≤ Real.exp (-(2 * x) * (i : ℝ) ^ (-q)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hxy hk])
  exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg (Nat.cast_nonneg i) _)

lemma tp_Lsum_mass (N : ℕ) (a q u : ℝ) (hq : 0 < q) :
    ∫ v in (0 : ℝ)..u, Lsum (N : ℕ∞) a q v
      = ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-a)
          * ((1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-q))) / (2 * (i : ℝ) ^ (-q))) := by
  have hfun : (fun v => Lsum (N : ℕ∞) a q v) = fun v => ∑ i ∈ Finset.Icc 1 N,
      (i : ℝ) ^ (-a) * Real.exp (-(2 * v) * (i : ℝ) ^ (-q)) := funext (tp_Lsum_fin N a q)
  rw [hfun, intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
    have hk : 0 < (i : ℝ) ^ (-q) := Real.rpow_pos_of_pos hi0 _
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have e : ∀ v : ℝ, Real.exp (-(2 * v) * (i : ℝ) ^ (-q))
        = Real.exp ((-(2 * (i : ℝ) ^ (-q))) * v) := fun v => by congr 1; ring
    simp_rw [e]
    have hne : (-(2 * (i : ℝ) ^ (-q))) ≠ 0 := by
      intro h0; linarith
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) hne]
    rw [integral_exp]
    simp only [mul_zero, Real.exp_zero, smul_eq_mul]
    field_simp
    ring_nf
  · intro i _
    apply Continuous.intervalIntegrable
    fun_prop


lemma tp_Hsum_ge_one (α : ℝ) (N : ℕ) (hN : 1 ≤ N) : 1 ≤ Hsum α N := by
  unfold Hsum
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have := Finset.single_le_sum (f := fun i : ℕ => (i : ℝ) ^ (-α))
    (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _) h1
  simpa using this

lemma tp_pi_facts : 0 ≤ 1 - 2 / Real.pi ∧ 1 - 2 / Real.pi ≤ 1 ∧ 0 < 2 / Real.pi ∧ 2 / Real.pi ≤ 1 := by
  have h3 := Real.pi_gt_three
  have hp : 0 < Real.pi := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : 2 / Real.pi ≤ 1 := by rw [div_le_one hp]; linarith
    linarith
  · have : 0 < 2 / Real.pi := by positivity
    linarith
  · positivity
  · rw [div_le_one hp]; linarith

lemma tp_g1_cont (α : ℝ) (N : ℕ) :
    Continuous (fun u => 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α u) :=
  continuous_const.mul (tp_Lsum_cont N α α)

lemma tp_g2_cont (α : ℝ) (N : ℕ) :
    Continuous (fun u => 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α u) :=
  continuous_const.mul (tp_Lsum_cont N (2 * α) α)

lemma tp_g1_nonneg (α : ℝ) (N : ℕ) (u : ℝ) :
    0 ≤ 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α u :=
  mul_nonneg (div_nonneg (mul_nonneg zero_le_two tp_pi_facts.1) (Nat.cast_nonneg N))
    (tp_Lsum_nonneg N α α u)

lemma tp_g2_nonneg (α : ℝ) (N : ℕ) (hN : 1 ≤ N) (u : ℝ) :
    0 ≤ 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α u := by
  have h1 := tp_Hsum_ge_one α N hN
  have hp := Real.pi_gt_three
  exact mul_nonneg (div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith)))
    (tp_Lsum_nonneg N _ _ u)

lemma tp_g1_anti (α : ℝ) (N : ℕ) :
    Antitone (fun u => 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α u) := fun x y hxy =>
  mul_le_mul_of_nonneg_left (tp_Lsum_anti N α α hxy)
    (div_nonneg (mul_nonneg zero_le_two tp_pi_facts.1) (Nat.cast_nonneg N))

lemma tp_g2_anti (α : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    Antitone (fun u => 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α u) := by
  have h1 := tp_Hsum_ge_one α N hN
  have hp := Real.pi_gt_three
  intro x y hxy
  exact mul_le_mul_of_nonneg_left (tp_Lsum_anti N _ _ hxy)
    (div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith)))

lemma tp_mass1 (α : ℝ) (N : ℕ) (hN : 1 ≤ N) (u : ℝ) (hα : 0 < α) (B : ℕ → ℝ)
    (hB : ∀ i ∈ Finset.Icc 1 N, 1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-α)) ≤ B i) :
    ∫ v in (0 : ℝ)..u, 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α v
      ≤ (1 - 2 / Real.pi) / (N : ℝ) * ∑ i ∈ Finset.Icc 1 N, B i := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [intervalIntegral.integral_const_mul, tp_Lsum_mass N α α u hα]
  have hterm : ∀ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-α)
      * ((1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-α))) / (2 * (i : ℝ) ^ (-α)))
      = (1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-α))) / 2 := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
    have hk : 0 < (i : ℝ) ^ (-α) := Real.rpow_pos_of_pos hi0 _
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  have hle : ∑ i ∈ Finset.Icc 1 N, (1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-α)))
      ≤ ∑ i ∈ Finset.Icc 1 N, B i := Finset.sum_le_sum hB
  have hc : 0 ≤ 2 * (1 - 2 / Real.pi) / (N : ℝ) :=
    div_nonneg (mul_nonneg zero_le_two tp_pi_facts.1) hNp.le
  calc 2 * (1 - 2 / Real.pi) / (N : ℝ) * ((∑ i ∈ Finset.Icc 1 N, (1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-α)))) / 2)
      ≤ 2 * (1 - 2 / Real.pi) / (N : ℝ) * ((∑ i ∈ Finset.Icc 1 N, B i) / 2) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hle zero_le_two) hc
    _ = _ := by ring

lemma tp_mass2 (α : ℝ) (N : ℕ) (hN : 1 ≤ N) (u : ℝ) (hα : 0 < α) (B : ℕ → ℝ)
    (hB : ∀ i ∈ Finset.Icc 1 N, 1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-α)) ≤ B i) :
    ∫ v in (0 : ℝ)..u, 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α v
      ≤ 2 / (Real.pi * Hsum α N) * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-α) * B i := by
  have h1 := tp_Hsum_ge_one α N hN
  have hp := Real.pi_gt_three
  have hc : 0 ≤ 4 / (Real.pi * Hsum α N) :=
    div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
  rw [intervalIntegral.integral_const_mul, tp_Lsum_mass N (2 * α) α u hα]
  have hterm : ∀ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-(2 * α))
      * ((1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-α))) / (2 * (i : ℝ) ^ (-α)))
      = (i : ℝ) ^ (-α) * (1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-α))) / 2 := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
    have hk : 0 < (i : ℝ) ^ (-α) := Real.rpow_pos_of_pos hi0 _
    have e : (i : ℝ) ^ (-(2 * α)) = (i : ℝ) ^ (-α) * (i : ℝ) ^ (-α) := by
      rw [← Real.rpow_add hi0]; congr 1; ring
    rw [e]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  have hle : ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-α) * (1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-α)))
      ≤ ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-α) * B i :=
    Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hB i hi)
      (Real.rpow_nonneg (Nat.cast_nonneg i) _))
  calc 4 / (Real.pi * Hsum α N) * ((∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-α) * (1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-α)))) / 2)
      ≤ 4 / (Real.pi * Hsum α N) * ((∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-α) * B i) / 2) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hle zero_le_two) hc
    _ = _ := by ring


lemma tp_mass_total (α : ℝ) (N : ℕ) (hN : 1 ≤ N) (u : ℝ) (hα : 0 < α) :
    (∫ v in (0 : ℝ)..u, 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α v)
        ≤ 1 - 2 / Real.pi
      ∧ (∫ v in (0 : ℝ)..u, 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α v)
        ≤ 2 / Real.pi := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := tp_Hsum_ge_one α N hN
  have hp := Real.pi_gt_three
  have hB : ∀ i ∈ Finset.Icc 1 N, 1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-α)) ≤ 1 := by
    intro i _
    have := Real.exp_pos (-(2 * u) * (i : ℝ) ^ (-α))
    linarith
  constructor
  · have := tp_mass1 α N hN u hα (fun _ => 1) hB
    refine this.trans (le_of_eq ?_)
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
    field_simp
  · have := tp_mass2 α N hN u hα (fun _ => 1) hB
    refine this.trans (le_of_eq ?_)
    simp only [mul_one]
    have hH : ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-α) = Hsum α N := rfl
    rw [hH]
    have : Hsum α N ≠ 0 := by linarith
    field_simp

lemma tp_term_bd (α : ℝ) (N : ℕ) (δ u : ℝ) (hα : 0 < α) (hδ : 0 < δ) (hu : 0 ≤ u)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 N) :
    1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-α))
      ≤ (if i ≤ ⌊δ * (N : ℝ)⌋₊ then (1 : ℝ) else 0) + 2 * u * (δ * (N : ℝ)) ^ (-α) := by
  rw [Finset.mem_Icc] at hi
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
  have hc : 0 ≤ 2 * u * (δ * (N : ℝ)) ^ (-α) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (mul_nonneg hδ.le (Nat.cast_nonneg N)) _)
  by_cases h : i ≤ ⌊δ * (N : ℝ)⌋₊
  · rw [if_pos h]
    have := Real.exp_pos (-(2 * u) * (i : ℝ) ^ (-α))
    linarith
  · rw [if_neg h]
    push_neg at h
    have hlt : δ * (N : ℝ) < (i : ℝ) := by
      have h1 := Nat.lt_floor_add_one (δ * (N : ℝ))
      have h2 : ((⌊δ * (N : ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast h
      linarith
    have hNp : 0 < δ * (N : ℝ) := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · omega
      · exact mul_pos hδ (by exact_mod_cast h0)
    have hpow : (i : ℝ) ^ (-α) ≤ (δ * (N : ℝ)) ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos hNp hlt.le (by linarith)
    have := Real.add_one_le_exp (2 * u * (i : ℝ) ^ (-α) * (-1))
    have e : -(2 * u) * (i : ℝ) ^ (-α) = 2 * u * (i : ℝ) ^ (-α) * (-1) := by ring
    rw [e]
    have h3 : 2 * u * (i : ℝ) ^ (-α) ≤ 2 * u * (δ * (N : ℝ)) ^ (-α) :=
      mul_le_mul_of_nonneg_left hpow (by linarith)
    nlinarith

lemma tp_mass_delta (α : ℝ) (N : ℕ) (hN : 1 ≤ N) (δ u : ℝ) (hα : 0 < α) (hδ : 0 < δ)
    (hu : 0 ≤ u) :
    (∫ v in (0 : ℝ)..u, 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α v)
        ≤ (1 - 2 / Real.pi) * (δ + 2 * u * δ ^ (-α) * (N : ℝ) ^ (-α))
      ∧ (∫ v in (0 : ℝ)..u, 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α v)
        ≤ 2 / Real.pi * (Hsum α ⌊δ * (N : ℝ)⌋₊ / Hsum α N + 2 * u * δ ^ (-α) * (N : ℝ) ^ (-α)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := tp_Hsum_ge_one α N hN
  have hp := Real.pi_gt_three
  have hcm : (δ * (N : ℝ)) ^ (-α) = δ ^ (-α) * (N : ℝ) ^ (-α) := Real.mul_rpow hδ.le hNp.le
  set J := ⌊δ * (N : ℝ)⌋₊ with hJ
  have hJle : (J : ℝ) ≤ δ * N := Nat.floor_le (mul_nonneg hδ.le hNp.le)
  set c := 2 * u * (δ * (N : ℝ)) ^ (-α) with hcdef
  have hc : 0 ≤ c := mul_nonneg (by linarith) (Real.rpow_nonneg (mul_nonneg hδ.le hNp.le) _)
  have hB := tp_term_bd α N δ u hα hδ hu
  have hsub : (Finset.Icc 1 N).filter (fun i => i ≤ J) ⊆ Finset.Icc 1 J := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_Icc] at hi
    rw [Finset.mem_Icc]; omega
  constructor
  · have := tp_mass1 α N hN u hα _ hB
    refine this.trans ?_
    have hs : ∑ i ∈ Finset.Icc 1 N, ((if i ≤ J then (1 : ℝ) else 0) + c) ≤ δ * N + N * c := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel]
      have : (((Finset.Icc 1 N).filter (fun i => i ≤ J)).card : ℝ) ≤ J := by
        exact_mod_cast (Finset.card_le_card hsub).trans (by simp)
      linarith
    have hcoef : 0 ≤ (1 - 2 / Real.pi) / (N : ℝ) := div_nonneg tp_pi_facts.1 hNp.le
    calc (1 - 2 / Real.pi) / (N : ℝ) * ∑ i ∈ Finset.Icc 1 N, ((if i ≤ J then (1 : ℝ) else 0) + c)
        ≤ (1 - 2 / Real.pi) / (N : ℝ) * (δ * N + N * c) := mul_le_mul_of_nonneg_left hs hcoef
      _ = (1 - 2 / Real.pi) * (δ + 2 * u * δ ^ (-α) * (N : ℝ) ^ (-α)) := by
          rw [hcdef, hcm]; field_simp
  · have := tp_mass2 α N hN u hα _ hB
    refine this.trans ?_
    have hs : ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-α) * ((if i ≤ J then (1 : ℝ) else 0) + c)
        ≤ Hsum α J + c * Hsum α N := by
      have e : ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-α) * ((if i ≤ J then (1 : ℝ) else 0) + c)
          = (∑ i ∈ Finset.Icc 1 N, if i ≤ J then (i : ℝ) ^ (-α) else 0) + c * Hsum α N := by
        unfold Hsum
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring
      rw [e, ← Finset.sum_filter]
      have : ∑ i ∈ (Finset.Icc 1 N).filter (fun i => i ≤ J), (i : ℝ) ^ (-α) ≤ Hsum α J := by
        unfold Hsum
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i _ _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
      linarith
    have hcoef : 0 ≤ 2 / (Real.pi * Hsum α N) := div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
    calc 2 / (Real.pi * Hsum α N) * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-α) * ((if i ≤ J then (1 : ℝ) else 0) + c)
        ≤ 2 / (Real.pi * Hsum α N) * (Hsum α J + c * Hsum α N) := mul_le_mul_of_nonneg_left hs hcoef
      _ = 2 / Real.pi * (Hsum α J / Hsum α N + 2 * u * δ ^ (-α) * (N : ℝ) ^ (-α)) := by
          have : Hsum α N ≠ 0 := by linarith
          rw [hcdef, hcm]; field_simp

/-! ## The S-GD kernel below the critical exponent -/


lemma tp_sgd_cont (α : ℝ) (N : ℕ) : Continuous (sgdKernel α N) := by
  have : sgdKernel α N = fun u => 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α u
      + 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α u := rfl
  rw [this]
  exact (tp_g1_cont α N).add (tp_g2_cont α N)

lemma tp_sgd_nonneg (α : ℝ) (N : ℕ) (hN : 1 ≤ N) (u : ℝ) : 0 ≤ sgdKernel α N u :=
  add_nonneg (tp_g1_nonneg α N u) (tp_g2_nonneg α N hN u)

lemma tp_sgd_anti (α : ℝ) (N : ℕ) (hN : 1 ≤ N) : Antitone (sgdKernel α N) := by
  intro x y hxy
  exact add_le_add (tp_g1_anti α N hxy) (tp_g2_anti α N hN hxy)

lemma tp_sgd_int (α : ℝ) (N : ℕ) (u : ℝ) :
    ∫ v in (0 : ℝ)..u, sgdKernel α N v
      = (∫ v in (0 : ℝ)..u, 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α v)
        + ∫ v in (0 : ℝ)..u, 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α v := by
  have : sgdKernel α N = fun u => 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α u
      + 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α u := rfl
  rw [this]
  exact intervalIntegral.integral_add ((tp_g1_cont α N).intervalIntegrable _ _)
    ((tp_g2_cont α N).intervalIntegrable _ _)

lemma tp_harm_ratio (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (N : ℕ) (hN : 1 ≤ N) (δ : ℝ)
    (hδ : 0 < δ) :
    Hsum α ⌊δ * (N : ℝ)⌋₊ / Hsum α N ≤ (N : ℝ) ^ (α - 1) + δ ^ (1 - α) / (1 - α) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < 1 - α := by linarith
  set J := ⌊δ * (N : ℝ)⌋₊ with hJ
  have hJle : (J : ℝ) ≤ δ * N := Nat.floor_le (mul_nonneg hδ.le hNp.le)
  have hHJ : Hsum α J ≤ 1 + (J : ℝ) ^ (1 - α) / (1 - α) := by
    rcases Nat.eq_zero_or_pos J with h0 | h0
    · rw [h0]
      simp [Hsum, Real.zero_rpow hc.ne']
    · have h := (lem_app_phase_harmonic_i hα0 J h0).2
      have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast h0
      have hint : ∫ x in (1 : ℝ)..(J : ℝ), x ^ (-α) = ((J : ℝ) ^ (1 - α) - 1) / (1 - α) := by
        rw [integral_rpow (Or.inl (by linarith)), show -α + 1 = 1 - α by ring, Real.one_rpow]
      rw [hint] at h
      have : ((J : ℝ) ^ (1 - α) - 1) / (1 - α) ≤ (J : ℝ) ^ (1 - α) / (1 - α) :=
        div_le_div_of_nonneg_right (by linarith) hc.le
      linarith
  have hHN := lem_app_phase_harmonic_ii hα0 hα1.le N hN
  have hNpow : 0 < (N : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos hNp _
  have hJpow : (J : ℝ) ^ (1 - α) ≤ δ ^ (1 - α) * (N : ℝ) ^ (1 - α) := by
    rw [← Real.mul_rpow hδ.le hNp.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg J) hJle hc.le
  have hHJ0 : 0 ≤ Hsum α J := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
  calc Hsum α J / Hsum α N ≤ Hsum α J / (N : ℝ) ^ (1 - α) :=
        div_le_div_of_nonneg_left hHJ0 hNpow hHN
    _ ≤ (1 + δ ^ (1 - α) * (N : ℝ) ^ (1 - α) / (1 - α)) / (N : ℝ) ^ (1 - α) := by
        apply div_le_div_of_nonneg_right _ hNpow.le
        have : (J : ℝ) ^ (1 - α) / (1 - α) ≤ δ ^ (1 - α) * (N : ℝ) ^ (1 - α) / (1 - α) :=
          div_le_div_of_nonneg_right hJpow hc.le
        linarith
    _ = (N : ℝ) ^ (α - 1) + δ ^ (1 - α) / (1 - α) := by
        have e : (N : ℝ) ^ (α - 1) = ((N : ℝ) ^ (1 - α))⁻¹ := by
          rw [← Real.rpow_neg hNp.le]; congr 1; ring
        rw [e]
        field_simp


lemma tp_G_lt {α r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ DG τG : ℝ, 1 ≤ DG ∧ 0 < τG ∧ ∃ NG : ℕ, ∀ N : ℕ, NG ≤ N → ∀ C : ℝ, 0 < C →
      ∀ u ∈ Icc (0 : ℝ) (τG * (N : ℝ) ^ α),
        oneSidedConv (fun w => C * (1 + w / DG) ^ (-r)) (sgdKernel α N) u
          ≤ 2 * (C * (1 + u / DG) ^ (-r)) := by
  have hc : 0 < 1 - α := by linarith
  set ε := 1 - r with hε
  have hε0 : 0 < ε := by linarith
  have hε1 : ε < 1 := by linarith
  set Y := ε * (1 - α) / 4 with hY
  have hY0 : 0 < Y := by positivity
  have hY1 : Y < 1 := by rw [hY]; nlinarith
  set δ := Y ^ (1 / (1 - α)) with hδdef
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hY0 _
  have hδ1 : δ < 1 := Real.rpow_lt_one hY0.le hY1 (by positivity)
  have hδY : δ ^ (1 - α) = Y := by
    rw [hδdef, ← Real.rpow_mul hY0.le, one_div_mul_cancel hc.ne', Real.rpow_one]
  have hδle : δ ≤ δ ^ (1 - α) := by
    have := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (show 1 - α ≤ 1 by linarith)
    simpa using this
  have hδα : 0 < δ ^ α := Real.rpow_pos_of_pos hδ0 _
  refine ⟨1, ε * δ ^ α / 16, le_rfl, by positivity, ⌈(4 / ε) ^ (1 / (1 - α))⌉₊ + 1, ?_⟩
  intro N hN C hC u hu
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hu0, huτ⟩ := hu
  -- N^(α-1) ≤ ε/4
  have hNge : (4 / ε) ^ (1 / (1 - α)) ≤ (N : ℝ) := by
    have h1 : (4 / ε) ^ (1 / (1 - α)) ≤ (⌈(4 / ε) ^ (1 / (1 - α))⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(4 / ε) ^ (1 / (1 - α))⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    push_cast at h2
    linarith
  have hNpow : 4 / ε ≤ (N : ℝ) ^ (1 - α) := by
    have := Real.rpow_le_rpow (by positivity) hNge hc.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hc.ne', Real.rpow_one] at this
  have hNα : (N : ℝ) ^ (α - 1) ≤ ε / 4 := by
    have e : (N : ℝ) ^ (α - 1) = ((N : ℝ) ^ (1 - α))⁻¹ := by
      rw [← Real.rpow_neg hNp.le]; congr 1; ring
    rw [e]
    have hpos : 0 < (N : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos hNp _
    calc ((N : ℝ) ^ (1 - α))⁻¹ ≤ (4 / ε)⁻¹ := inv_anti₀ (by positivity) hNpow
      _ = ε / 4 := by rw [inv_div]
  -- X bound
  have hX : 2 * u * δ ^ (-α) * (N : ℝ) ^ (-α) ≤ ε / 8 := by
    have hNa : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNp _
    have e1 : (N : ℝ) ^ (-α) = ((N : ℝ) ^ α)⁻¹ := Real.rpow_neg hNp.le _
    have e2 : δ ^ (-α) = (δ ^ α)⁻¹ := Real.rpow_neg hδ0.le _
    rw [e1, e2]
    have : u ≤ ε * δ ^ α / 16 * (N : ℝ) ^ α := huτ
    have h3 : 2 * u / ((δ ^ α) * (N : ℝ) ^ α) ≤ ε / 8 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc 2 * u * (δ ^ α)⁻¹ * ((N : ℝ) ^ α)⁻¹ = 2 * u / ((δ ^ α) * (N : ℝ) ^ α) := by
          field_simp
      _ ≤ ε / 8 := h3
  obtain ⟨hm1, hm2⟩ := tp_mass_delta α N hN1 δ u hα hδ0 hu0
  have hR := tp_harm_ratio α hα hα1 N hN1 δ hδ0
  have hR0 : 0 ≤ Hsum α ⌊δ * (N : ℝ)⌋₊ / Hsum α N := by
    apply div_nonneg
    · exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
    · linarith [tp_Hsum_ge_one α N hN1]
  have hX0 : 0 ≤ 2 * u * δ ^ (-α) * (N : ℝ) ^ (-α) :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hδ0.le _)) (Real.rpow_nonneg hNp.le _)
  obtain ⟨hp1, hp2, hp3, hp4⟩ := tp_pi_facts
  have hmass : (∫ v in (0 : ℝ)..u, sgdKernel α N v) ≤ 1 - r := by
    rw [tp_sgd_int]
    have a1 : (1 - 2 / Real.pi) * (δ + 2 * u * δ ^ (-α) * (N : ℝ) ^ (-α))
        ≤ δ + 2 * u * δ ^ (-α) * (N : ℝ) ^ (-α) := by nlinarith
    have a2 : 2 / Real.pi * (Hsum α ⌊δ * (N : ℝ)⌋₊ / Hsum α N + 2 * u * δ ^ (-α) * (N : ℝ) ^ (-α))
        ≤ Hsum α ⌊δ * (N : ℝ)⌋₊ / Hsum α N + 2 * u * δ ^ (-α) * (N : ℝ) ^ (-α) := by nlinarith
    have a3 : δ ^ (1 - α) / (1 - α) = ε / 4 := by
      rw [hδY, hY]; field_simp
    have a4 : δ ≤ ε / 4 := by
      have : Y ≤ ε / 4 := by rw [hY]; nlinarith
      linarith
    linarith
  have hm := lem_app_phase_mass (sgdKernel α N) (tp_sgd_cont α N).continuousOn
    (fun v _ => tp_sgd_nonneg α N hN1 v) (fun x _ y _ hxy => tp_sgd_anti α N hN1 hxy)
    C 1 r hC one_pos hr0 hr1 u hu0
  simp only [div_one] at hm ⊢
  have hh : 0 ≤ C * (1 + u) ^ (-r) := mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
  have hr' : 0 < 1 - r := by linarith
  have hratio : (∫ v in (0:ℝ)..u, sgdKernel α N v) / (1 - r) ≤ 1 := by
    rw [div_le_iff₀ hr']; linarith
  calc _ ≤ _ := hm
    _ ≤ 1 * (C * (1 + u) ^ (-r)) := mul_le_mul_of_nonneg_right hratio hh
    _ ≤ 2 * (C * (1 + u) ^ (-r)) := by linarith


lemma tp_Epq_nonneg (a q : ℝ) (ha : 1 < a) : 0 ≤ Epq a q := by
  unfold Epq
  refine le_trans ?_ (le_max_left _ _)
  have hZ : 0 < Za a := by
    unfold Za
    have := div_pos one_pos (show (0 : ℝ) < a - 1 by linarith)
    linarith
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hZ.le

lemma tp_template_gt {α : ℝ} (hα : 1 < α) (N : ℕ) (hN : 1 ≤ N) (v : ℝ) (hv : 0 ≤ v) :
    sgdKernel α N v
      ≤ 4 / Real.pi * Epq (2 * α) α * (1 + v) ^ (-(2 - 1 / α))
        + 2 * (1 - 2 / Real.pi) * Epq α α * (N : ℝ) ^ (-α)
          * ((1 + v) / (N : ℝ) ^ α) ^ (-(1 - 1 / α)) := by
  have hα0 : 0 < α := by linarith
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hH := tp_Hsum_ge_one α N hN
  have hp := Real.pi_gt_three
  have hP : 0 < 1 + v := by linarith
  -- piece 2
  have h2 : 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α v
      ≤ 4 / Real.pi * Epq (2 * α) α * (1 + v) ^ (-(2 - 1 / α)) := by
    have hs := lem_app_phase_sums_i (a := 2 * α) (q := α) (by linarith) hα0 (N : ℕ∞) hv
    have hd : dAQ (2 * α) α = 2 - 1 / α := by unfold dAQ; field_simp
    rw [hd] at hs
    have hc1 : 4 / (Real.pi * Hsum α N) ≤ 4 / Real.pi := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
      nlinarith
    calc 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α v
        ≤ 4 / Real.pi * Lsum (N : ℕ∞) (2 * α) α v :=
          mul_le_mul_of_nonneg_right hc1 (tp_Lsum_nonneg N _ _ v)
      _ ≤ 4 / Real.pi * (Epq (2 * α) α * (1 + v) ^ (-(2 - 1 / α))) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  -- piece 1
  have h1 : 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α v
      ≤ 2 * (1 - 2 / Real.pi) * Epq α α * (N : ℝ) ^ (-α)
          * ((1 + v) / (N : ℝ) ^ α) ^ (-(1 - 1 / α)) := by
    have hs := lem_app_phase_sums_i (a := α) (q := α) hα hα0 (N : ℕ∞) hv
    have hd : dAQ α α = 1 - 1 / α := by unfold dAQ; field_simp
    rw [hd] at hs
    have hNa : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNp _
    have hNN : (N : ℝ) ^ (-α) * (N : ℝ) ^ (α - 1) = (N : ℝ)⁻¹ := by
      rw [← Real.rpow_add hNp]
      rw [show -α + (α - 1) = -1 by ring, Real.rpow_neg_one]
    have e : (N : ℝ) ^ (-α) * ((1 + v) / (N : ℝ) ^ α) ^ (-(1 - 1 / α))
        = (N : ℝ)⁻¹ * (1 + v) ^ (-(1 - 1 / α)) := by
      rw [Real.div_rpow hP.le hNa.le, Real.rpow_neg hNa.le, ← Real.rpow_mul hNp.le,
        show α * (1 - 1 / α) = α - 1 by field_simp, div_inv_eq_mul]
      calc (N : ℝ) ^ (-α) * ((1 + v) ^ (-(1 - 1 / α)) * (N : ℝ) ^ (α - 1))
          = ((N : ℝ) ^ (-α) * (N : ℝ) ^ (α - 1)) * (1 + v) ^ (-(1 - 1 / α)) := by ring
        _ = _ := by rw [hNN]
    have hKc : 0 ≤ 2 * (1 - 2 / Real.pi) / (N : ℝ) := div_nonneg (mul_nonneg zero_le_two tp_pi_facts.1) hNp.le
    calc 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α v
        ≤ 2 * (1 - 2 / Real.pi) / (N : ℝ) * (Epq α α * (1 + v) ^ (-(1 - 1 / α))) :=
          mul_le_mul_of_nonneg_left hs hKc
      _ = 2 * (1 - 2 / Real.pi) * Epq α α * ((N : ℝ)⁻¹ * (1 + v) ^ (-(1 - 1 / α))) := by ring
      _ = _ := by rw [← e]; ring
  have hsgd : sgdKernel α N v = 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α v
      + 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α v := rfl
  rw [hsgd]
  linarith


lemma tp_G_gt {α r : ℝ} (hα : 1 < α) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ DG τG : ℝ, 1 ≤ DG ∧ 0 < τG ∧ ∃ NG : ℕ, ∀ N : ℕ, NG ≤ N → ∀ C : ℝ, 0 < C →
      ∀ u ∈ Icc (0 : ℝ) (τG * (N : ℝ) ^ α),
        oneSidedConv (fun w => C * (1 + w / DG) ^ (-r)) (sgdKernel α N) u
          ≤ 2 * (C * (1 + u / DG) ^ (-r)) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨hp1, hp2, hp3, hp4⟩ := tp_pi_facts
  have hr' : 0 < 1 - r := by linarith
  obtain ⟨hδ0, hδ1, hδr⟩ := tp_delta_facts r hr0
  set δ := dilDelta r with hδdef
  set Kf := 4 / Real.pi * Epq (2 * α) α with hKf
  set Ks := 2 * (1 - 2 / Real.pi) * Epq α α with hKs
  set υ := 2 - 1 / α with hυ
  set b := 1 - 1 / α with hb
  have hinv : 1 / α < 1 := by rw [div_lt_one hα0]; exact hα
  have hinv0 : 0 < 1 / α := by positivity
  have hυ1 : 1 < υ := by rw [hυ]; linarith
  have hb0 : 0 < b := by rw [hb]; linarith
  have hKf0 : 0 ≤ Kf := mul_nonneg (by positivity) (tp_Epq_nonneg _ _ (by linarith))
  have hKs0 : 0 ≤ Ks := mul_nonneg (mul_nonneg zero_le_two hp1) (tp_Epq_nonneg _ _ hα)
  set X := 4 * Kf * δ ^ (-υ) / (1 - r) with hX
  have hX0 : 0 ≤ X := by
    rw [hX]; exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKf0) (Real.rpow_nonneg hδ0.le _)) hr'.le
  set D := max 1 (X ^ (1 / (υ - 1))) with hD
  have hD1 : 1 ≤ D := le_max_left _ _
  have hDp : 0 < D := by linarith
  have hXD : X ≤ D ^ (υ - 1) := by
    have h1 : X ^ (1 / (υ - 1)) ≤ D := le_max_right _ _
    have := Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) h1 (by linarith : 0 ≤ υ - 1)
    rwa [← Real.rpow_mul hX0, one_div_mul_cancel (by linarith : υ - 1 ≠ 0), Real.rpow_one] at this
  have hkf : Kf * δ ^ (-υ) * D ^ (1 - υ) * dilB r υ ≤ 1 / 4 := by
    have hB : dilB r υ = (1 - r)⁻¹ := by unfold dilB; simp [hr1]
    rw [hB]
    have hDD : D ^ (υ - 1) * D ^ (1 - υ) = 1 := by
      rw [← Real.rpow_add hDp]; simp
    have hDn : 0 ≤ D ^ (1 - υ) := Real.rpow_nonneg hDp.le _
    have hXe : Kf * δ ^ (-υ) * (1 - r)⁻¹ = X / 4 := by rw [hX]; field_simp
    calc Kf * δ ^ (-υ) * D ^ (1 - υ) * (1 - r)⁻¹
        = (Kf * δ ^ (-υ) * (1 - r)⁻¹) * D ^ (1 - υ) := by ring
      _ = X / 4 * D ^ (1 - υ) := by rw [hXe]
      _ ≤ D ^ (υ - 1) / 4 * D ^ (1 - υ) := by
          apply mul_le_mul_of_nonneg_right _ hDn
          linarith
      _ = 1 / 4 := by
          calc D ^ (υ - 1) / 4 * D ^ (1 - υ) = (D ^ (υ - 1) * D ^ (1 - υ)) / 4 := by ring
            _ = 1 / 4 := by rw [hDD]
  set θ := (1 - r) * δ ^ b / (4 * (Ks + 1)) with hθ
  have hθ0 : 0 < θ := by
    rw [hθ]; have := Real.rpow_pos_of_pos hδ0 b; positivity
  set τ' := θ ^ α with hτ'
  have hτ'0 : 0 < τ' := Real.rpow_pos_of_pos hθ0 _
  refine ⟨D, τ' / 2, hD1, by positivity, ⌈(2 * D / τ') ^ (1 / α)⌉₊ + 1, ?_⟩
  intro N hN C hC u hu
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hu0, huτ⟩ := hu
  have hNge : (2 * D / τ') ^ (1 / α) ≤ (N : ℝ) := by
    have h1 : (2 * D / τ') ^ (1 / α) ≤ (⌈(2 * D / τ') ^ (1 / α)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(2 * D / τ') ^ (1 / α)⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    push_cast at h2
    linarith
  have hNα : 2 * D / τ' ≤ (N : ℝ) ^ α := by
    have := Real.rpow_le_rpow (by positivity) hNge hα0.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hα0.ne', Real.rpow_one] at this
  have hNa : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNp _
  have hDle : D ≤ τ' / 2 * (N : ℝ) ^ α := by
    rw [div_le_iff₀ hτ'0] at hNα
    linarith
  have hYle : (D + u) / (N : ℝ) ^ α ≤ τ' := by
    rw [div_le_iff₀ hNa]
    linarith
  -- apply split
  have hgcu : ContinuousOn (sgdKernel α N) (Icc 0 u) := (tp_sgd_cont α N).continuousOn
  have hgnn : ∀ v ∈ Icc (0 : ℝ) u, 0 ≤ sgdKernel α N v := fun v _ => tp_sgd_nonneg α N hN1 v
  have hgm : ∫ s in (0:ℝ)..u, sgdKernel α N s ≤ 1 := by
    rw [tp_sgd_int]
    have := tp_mass_total α N hN1 u hα0
    linarith [this.1, this.2]
  have hsplit := tp_split_conv (Kf := Kf) (Ks := Ks) (υ := υ) (b := b) (N := (N : ℝ)) (q := α)
    (D := D) (C := C) (r0 := r) hu0 hgcu hgnn hgm hKf0 hKs0 hυ1 hb0.le (by exact_mod_cast hN1)
    hr0 (by linarith) hD1 hC (fun v hv _ => tp_template_gt hα N hN1 v hv)
  have hslow := tp_slow_le (Ks := Ks) (b := b) (N := (N : ℝ)) (q := α) (D := D) (C := C) (u := u)
    hr1 hr0 hKs0 (by exact_mod_cast hN1) hD1 hC hu0
  -- bound the slow factor
  have hY0 : 0 ≤ (D + u) / (N : ℝ) ^ α := div_nonneg (by linarith) hNa.le
  have h1b : 1 - b = 1 / α := by rw [hb]; ring
  have hYb : ((D + u) / (N : ℝ) ^ α) ^ (1 - b) ≤ θ := by
    rw [h1b]
    have := Real.rpow_le_rpow hY0 hYle hinv0.le
    rwa [hτ', ← Real.rpow_mul hθ0.le, mul_one_div_cancel hα0.ne', Real.rpow_one] at this
  have hP : 0 < 1 + u / D := by have := div_nonneg hu0 hDp.le; linarith
  have hh : 0 ≤ C * (1 + u / D) ^ (-r) := mul_nonneg hC.le (Real.rpow_nonneg hP.le _)
  have hcoef : Ks * δ ^ (-b) / (1 - r) * ((D + u) / (N : ℝ) ^ α) ^ (1 - b) ≤ 1 / 4 := by
    have hδb : 0 < δ ^ b := Real.rpow_pos_of_pos hδ0 b
    have hδnb : δ ^ (-b) = (δ ^ b)⁻¹ := Real.rpow_neg hδ0.le b
    have hnn : 0 ≤ Ks * δ ^ (-b) / (1 - r) := div_nonneg (mul_nonneg hKs0 (Real.rpow_nonneg hδ0.le _)) hr'.le
    calc Ks * δ ^ (-b) / (1 - r) * ((D + u) / (N : ℝ) ^ α) ^ (1 - b)
        ≤ Ks * δ ^ (-b) / (1 - r) * θ := mul_le_mul_of_nonneg_left hYb hnn
      _ = Ks / (4 * (Ks + 1)) := by
          rw [hθ, hδnb]; field_simp
      _ ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hslow2 : Ks * δ ^ (-b) / (1 - r) * ((D + u) / (N : ℝ) ^ α) ^ (1 - b)
      * (C * (1 + u / D) ^ (-r)) ≤ 1 / 4 * (C * (1 + u / D) ^ (-r)) :=
    mul_le_mul_of_nonneg_right hcoef hh
  have hk : (Kf * δ ^ (-υ) * D ^ (1 - υ) * dilB r υ) * (C * (1 + u / D) ^ (-r))
      ≤ 1 / 4 * (C * (1 + u / D) ^ (-r)) := mul_le_mul_of_nonneg_right hkf hh
  linarith


lemma tp_conv_add {g1 g2 : ℝ → ℝ} (h1 : Continuous g1) (h2 : Continuous g2)
    {u D C r : ℝ} (hD : 0 < D) (hu : 0 ≤ u) :
    oneSidedConv (fun w => C * (1 + w / D) ^ (-r)) (fun v => g1 v + g2 v) u
      = oneSidedConv (fun w => C * (1 + w / D) ^ (-r)) g1 u
        + oneSidedConv (fun w => C * (1 + w / D) ^ (-r)) g2 u := by
  have hh'c : ContinuousOn (fun s => C * (1 + (u - s) / D) ^ (-r)) (Icc 0 u) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const (by fun_prop)
    intro s hs
    left
    have : 0 ≤ (u - s) / D := div_nonneg (by linarith [hs.2]) hD.le
    have : 0 < 1 + (u - s) / D := by linarith
    exact this.ne'
  unfold oneSidedConv
  simp only [mul_add]
  exact intervalIntegral.integral_add
    ((hh'c.mul h1.continuousOn).intervalIntegrable_of_Icc hu)
    ((hh'c.mul h2.continuousOn).intervalIntegrable_of_Icc hu)

lemma tp_G_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ DG τG : ℝ, 1 ≤ DG ∧ 0 < τG ∧ ∃ NG : ℕ, ∀ N : ℕ, NG ≤ N → ∀ C : ℝ, 0 < C →
      ∀ u ∈ Icc (0 : ℝ) (τG * (N : ℝ) ^ (1 : ℝ)),
        oneSidedConv (fun w => C * (1 + w / DG) ^ (-r)) (sgdKernel 1 N) u
          ≤ 2 * (C * (1 + u / DG) ^ (-r)) := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := tp_pi_facts
  have hpi := Real.pi_gt_three
  have hr' : 0 < 1 - r := by linarith
  obtain ⟨hδ0, hδ1, hδr⟩ := tp_delta_facts r hr0
  set δo := dilDelta r with hδo
  set ε := 1 - r with hε
  set E := Epq (2 * 1) 1 with hE
  have hE0 : 0 ≤ E := tp_Epq_nonneg _ _ (by norm_num)
  set L := 16 * E / (Real.pi * δo * ε) with hL
  set δ1 := ε / 8 with hδ1def
  have hδ10 : 0 < δ1 := by positivity
  refine ⟨1, δ1 * ε / 16, le_rfl, by positivity, ⌈Real.exp L⌉₊ + 1, ?_⟩
  intro N hN C hC u hu
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hu0, huτ⟩ := hu
  rw [Real.rpow_one] at huτ
  have hHlog : L ≤ Hsum 1 N := by
    have h1 : Real.exp L ≤ (N : ℝ) + 1 := by
      have h1 : Real.exp L ≤ (⌈Real.exp L⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈Real.exp L⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      push_cast at h2
      linarith
    have h2 : L ≤ Real.log ((N : ℝ) + 1) := (Real.le_log_iff_exp_le (by linarith)).2 h1
    have h3 := (lem_app_phase_harmonic_i (a := 1) one_pos N hN1).1
    have h4 : ∫ x in (1 : ℝ)..((N : ℝ) + 1), x ^ (-(1 : ℝ)) = Real.log ((N : ℝ) + 1) := by
      simp only [Real.rpow_neg_one]
      rw [integral_inv_of_pos one_pos (by linarith)]
      simp
    linarith
  have hH1 := tp_Hsum_ge_one 1 N hN1
  -- g1 part
  have hm1 := (tp_mass_delta 1 N hN1 δ1 u one_pos hδ10 hu0).1
  have hmass1 : (∫ v in (0 : ℝ)..u, 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) 1 1 v)
      ≤ (1 - r) := by
    refine hm1.trans ?_
    have hX : 2 * u * δ1 ^ (-(1 : ℝ)) * (N : ℝ) ^ (-(1 : ℝ)) ≤ ε / 8 := by
      simp only [Real.rpow_neg_one]
      have : u ≤ δ1 * ε / 16 * N := huτ
      rw [show 2 * u * δ1⁻¹ * (N : ℝ)⁻¹ = 2 * u / (δ1 * N) by field_simp]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have : (1 - 2 / Real.pi) * (δ1 + 2 * u * δ1 ^ (-(1 : ℝ)) * (N : ℝ) ^ (-(1 : ℝ)))
        ≤ δ1 + ε / 8 := by
      have hX0 : 0 ≤ 2 * u * δ1 ^ (-(1 : ℝ)) * (N : ℝ) ^ (-(1 : ℝ)) :=
        mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hδ10.le _)) (Real.rpow_nonneg hNp.le _)
      nlinarith
    have e : δ1 + ε / 8 = ε / 4 := by rw [hδ1def]; ring
    linarith
  have hconv1 : oneSidedConv (fun w => C * (1 + w / 1) ^ (-r))
      (fun v => 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) 1 1 v) u
      ≤ 1 / 4 * (C * (1 + u / 1) ^ (-r)) := by
    have hm := lem_app_phase_mass _ (tp_g1_cont 1 N).continuousOn
      (fun v _ => tp_g1_nonneg 1 N v) (fun x _ y _ hxy => tp_g1_anti 1 N hxy)
      C 1 r hC one_pos hr0 hr1 u hu0
    have hh : 0 ≤ C * (1 + u / 1) ^ (-r) := mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
    refine hm.trans ?_
    have hI : (∫ v in (0:ℝ)..u, 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) 1 1 v) / (1 - r) ≤ 1 / 4 := by
      rw [div_le_iff₀ hr']
      have : ε / 4 = (1 - r) / 4 := rfl
      have hm1' : (∫ v in (0 : ℝ)..u, 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) 1 1 v)
          ≤ (1 - 2 / Real.pi) * (δ1 + 2 * u * δ1 ^ (-(1 : ℝ)) * (N : ℝ) ^ (-(1 : ℝ))) := hm1
      have hX : 2 * u * δ1 ^ (-(1 : ℝ)) * (N : ℝ) ^ (-(1 : ℝ)) ≤ ε / 8 := by
        simp only [Real.rpow_neg_one]
        have : u ≤ δ1 * ε / 16 * N := huτ
        rw [show 2 * u * δ1⁻¹ * (N : ℝ)⁻¹ = 2 * u / (δ1 * N) by field_simp]
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have hX0 : 0 ≤ 2 * u * δ1 ^ (-(1 : ℝ)) * (N : ℝ) ^ (-(1 : ℝ)) :=
        mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hδ10.le _)) (Real.rpow_nonneg hNp.le _)
      have : (1 - 2 / Real.pi) * (δ1 + 2 * u * δ1 ^ (-(1 : ℝ)) * (N : ℝ) ^ (-(1 : ℝ)))
          ≤ δ1 + ε / 8 := by nlinarith
      have e : δ1 + ε / 8 = ε / 4 := by rw [hδ1def]; ring
      have hεe : ε = 1 - r := rfl
      nlinarith
    calc _ ≤ 1 / 4 * (C * (1 + u / 1) ^ (-r)) := mul_le_mul_of_nonneg_right hI hh
      _ = _ := rfl
  -- g2 part
  set A := 4 / (Real.pi * Hsum 1 N) * E with hA
  have hHp : 0 < Hsum 1 N := by linarith
  have hA0 : 0 ≤ A := mul_nonneg (div_nonneg (by norm_num) (mul_nonneg (by linarith) hHp.le)) hE0
  have hg2pt : ∀ v : ℝ, 0 ≤ v →
      4 / (Real.pi * Hsum 1 N) * Lsum (N : ℕ∞) (2 * 1) 1 v ≤ A * (1 + v)⁻¹ := by
    intro v hv
    have hs := lem_app_phase_sums_i (a := 2 * 1) (q := 1) (by norm_num) one_pos (N : ℕ∞) hv
    have hd : dAQ (2 * 1) 1 = 1 := by unfold dAQ; norm_num
    rw [hd, Real.rpow_neg_one] at hs
    calc _ ≤ 4 / (Real.pi * Hsum 1 N) * (E * (1 + v)⁻¹) :=
          mul_le_mul_of_nonneg_left hs (div_nonneg (by norm_num) (mul_nonneg (by linarith) hHp.le))
      _ = A * (1 + v)⁻¹ := by rw [hA]; ring
  have hM0 : 0 ≤ A / (δo * (1 + u)) := div_nonneg hA0 (by positivity)
  have hgM : ∀ s ∈ Icc (0 : ℝ) u, δo * (1 + u) < s →
      4 / (Real.pi * Hsum 1 N) * Lsum (N : ℕ∞) (2 * 1) 1 s ≤ A / (δo * (1 + u)) := by
    intro s hs hsc
    have h1 := hg2pt s hs.1
    have hpos : 0 < δo * (1 + u) := by positivity
    have h2 : (1 + s)⁻¹ ≤ (δo * (1 + u))⁻¹ := inv_anti₀ hpos (by linarith)
    calc _ ≤ A * (1 + s)⁻¹ := h1
      _ ≤ A * (δo * (1 + u))⁻¹ := mul_le_mul_of_nonneg_left h2 hA0
      _ = _ := by rw [div_eq_mul_inv]
  have hcore := tp_conv_core (g := fun v => 4 / (Real.pi * Hsum 1 N) * Lsum (N : ℕ∞) (2 * 1) 1 v)
    (u := u) (D := 1) (C := C) (r0 := r) (δ := δo) (M := A / (δo * (1 + u))) hu0
    (tp_g2_cont 1 N).continuousOn (fun v _ => tp_g2_nonneg 1 N hN1 v) one_pos hC hr0 hδ0 hδ1 hδr hM0
    (by simpa using hgM)
  have hmass2 := (tp_mass_total 1 N hN1 u one_pos).2
  have hpos1 : 0 < 1 + u := by linarith
  have hh : 0 ≤ C * (1 + u / 1) ^ (-r) := mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
  have hI : Ir r (u / 1) ≤ (1 + u / 1) ^ (1 - r) / (1 - r) := by
    unfold Ir; exact ir_le_aux r (u / 1) hr1 (by linarith)
  simp only [div_one] at hcore hI hh ⊢
  have hlate : A / (δo * (1 + u)) * (C * 1 * Ir r u) ≤ 1 / 4 * (C * (1 + u) ^ (-r)) := by
    have hPe : (1 + u) ^ (1 - r) = (1 + u) ^ (-r) * (1 + u) := by
      rw [show 1 - r = -r + 1 by ring, Real.rpow_add hpos1, Real.rpow_one]
    have hAc : A / (δo * ε) ≤ 1 / 4 := by
      have hcL : L * (Real.pi * δo * ε) = 16 * E := by
        rw [hL]; field_simp
      have hpd : 0 < Real.pi * δo * ε := by positivity
      have h16 : 16 * E ≤ Hsum 1 N * (Real.pi * δo * ε) := by
        rw [← hcL]; exact mul_le_mul_of_nonneg_right hHlog hpd.le
      have hpH : 0 < Hsum 1 N * (Real.pi * δo * ε) := mul_pos hHp hpd
      have e : A / (δo * ε) = 4 * E / (Hsum 1 N * (Real.pi * δo * ε)) := by
        rw [hA]; field_simp
      rw [e, div_le_iff₀ hpH]
      linarith
    have hnn : 0 ≤ A / (δo * (1 + u)) * C := mul_nonneg hM0 hC.le
    calc A / (δo * (1 + u)) * (C * 1 * Ir r u)
        ≤ A / (δo * (1 + u)) * (C * 1 * ((1 + u) ^ (1 - r) / (1 - r))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI (by linarith)) hM0
      _ = (A / (δo * ε)) * (C * (1 + u) ^ (-r)) := by
          rw [hPe, hε]; field_simp
      _ ≤ 1 / 4 * (C * (1 + u) ^ (-r)) := mul_le_mul_of_nonneg_right hAc hh
  have hsum := tp_conv_add (tp_g1_cont 1 N) (tp_g2_cont 1 N) (u := u) (D := 1) (C := C) (r := r)
    one_pos hu0
  have hsgd : sgdKernel 1 N = fun v => 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) 1 1 v
      + 4 / (Real.pi * Hsum 1 N) * Lsum (N : ℕ∞) (2 * 1) 1 v := rfl
  rw [hsgd]
  simp only [div_one] at hsum hconv1
  rw [hsum]
  have hm2 : 3 / 2 * (∫ s in (0:ℝ)..u, 4 / (Real.pi * Hsum 1 N) * Lsum (N : ℕ∞) (2 * 1) 1 s)
      * (C * (1 + u) ^ (-r)) ≤ 3 / 2 * (C * (1 + u) ^ (-r)) := by
    have : (∫ s in (0:ℝ)..u, 4 / (Real.pi * Hsum 1 N) * Lsum (N : ℕ∞) (2 * 1) 1 s) ≤ 1 := by linarith
    exact mul_le_mul_of_nonneg_right (by linarith) hh
  linarith

/-- `lem:app-phase-G-small`, snapshot `cr-2026-10-23`.
Source: `sections/07-phase-comparison/section.tex` l.3275–3282.

LaTeX (verbatim, `section.tex` l.3275–3282):
```latex
\begin{lemma}[\SignSGD kernel below the critical exponent]\label{lem:app-phase-G-small}
Let $\alpha>0$ and $0<r<1$, and write $g=g_{\text{s-SGD}}$. There are
$D_{\rm G}\ge1$, $\tau_{\rm G}>0$ and $N_{\rm G}$, depending only on $\alpha$ and $r$,
such that for $N\ge N_{\rm G}$, $C>0$ and $h(u)=C(1+u/D_{\rm G})^{-r}$,
\[
g*h\le2h\qquad\text{on }[0,\tau_{\rm G}N^\alpha] .
\]
\end{lemma}
```
-/
theorem lem_app_phase_G_small {α r : ℝ} (hα : 0 < α) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ DG τG : ℝ, 1 ≤ DG ∧ 0 < τG ∧ ∃ NG : ℕ, ∀ N : ℕ, NG ≤ N → ∀ C : ℝ, 0 < C →
      ∀ u ∈ Icc (0 : ℝ) (τG * (N : ℝ) ^ α),
        oneSidedConv (fun w => C * (1 + w / DG) ^ (-r)) (sgdKernel α N) u
          ≤ 2 * (C * (1 + u / DG) ^ (-r)) := by
  rcases lt_trichotomy α 1 with h | h | h
  · exact tp_G_lt hα h hr0 hr1
  · subst h
    exact tp_G_one hr0 hr1
  · exact tp_G_gt h hr0 hr1

/-! ## Kernel templates -/

lemma tp_Lsum_zero (N : ℕ) (a q : ℝ) : Lsum (N : ℕ∞) a q 0 = Hsum a N := by
  rw [tp_Lsum_fin]
  unfold Hsum
  simp

lemma tp_H_upper {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (N : ℕ) (hN : 1 ≤ N) :
    Hsum a N ≤ 1 + ((N : ℝ) ^ (1 - a) - 1) / (1 - a) := by
  have h := (lem_app_phase_harmonic_i ha N hN).2
  have hint : ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-a) = ((N : ℝ) ^ (1 - a) - 1) / (1 - a) := by
    rw [integral_rpow (Or.inl (by linarith)), show -a + 1 = 1 - a by ring, Real.one_rpow]
  rw [hint] at h
  exact h

lemma tp_H_lower {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (N : ℕ) (hN : 1 ≤ N)
    (h2 : 2 ≤ (N : ℝ) ^ (1 - a)) :
    (N : ℝ) ^ (1 - a) / (2 * (1 - a)) ≤ Hsum a N := by
  have h := (lem_app_phase_harmonic_i ha N hN).1
  have hc : 0 < 1 - a := by linarith
  have hint : ∫ x in (1 : ℝ)..((N : ℝ) + 1), x ^ (-a)
      = (((N : ℝ) + 1) ^ (1 - a) - 1) / (1 - a) := by
    rw [integral_rpow (Or.inl (by linarith)), show -a + 1 = 1 - a by ring, Real.one_rpow]
  rw [hint] at h
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hmono : (N : ℝ) ^ (1 - a) ≤ ((N : ℝ) + 1) ^ (1 - a) :=
    Real.rpow_le_rpow hN0 (by linarith) hc.le
  have hkey : (N : ℝ) ^ (1 - a) / (2 * (1 - a)) ≤ (((N : ℝ) + 1) ^ (1 - a) - 1) / (1 - a) := by
    rw [div_le_div_iff₀ (by linarith) hc]
    nlinarith [mul_nonneg hc.le (sub_nonneg.2 hmono), mul_nonneg hc.le (sub_nonneg.2 h2)]
  linarith

lemma tp_big_N (c : ℝ) (hc : 0 < c) : ∃ NT : ℕ, ∀ N : ℕ, NT ≤ N → 2 ≤ (N : ℝ) ^ c := by
  refine ⟨⌈(2 : ℝ) ^ (1 / c)⌉₊, fun N hN => ?_⟩
  have h1 : (2 : ℝ) ^ (1 / c) ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have h2 : ((2 : ℝ) ^ (1 / c)) ^ c ≤ (N : ℝ) ^ c :=
    Real.rpow_le_rpow (by positivity) h1 hc.le
  rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hc.ne', Real.rpow_one] at h2
  exact h2

lemma tp_templ_id (N q b v : ℝ) (hN : 0 < N) (hv : 0 ≤ v) :
    N ^ (-q) * ((1 + v) / N ^ q) ^ (-b) = N ^ (q * b - q) * (1 + v) ^ (-b) := by
  have hNq : 0 < N ^ q := Real.rpow_pos_of_pos hN q
  have hNqb : 0 < N ^ (q * b) := Real.rpow_pos_of_pos hN (q * b)
  have h1v : 0 < 1 + v := by linarith
  rw [Real.div_rpow h1v.le hNq.le, ← Real.rpow_mul hN.le, mul_neg, Real.rpow_neg hN.le,
    Real.rpow_neg hN.le, Real.rpow_sub hN]
  field_simp


/-- `lem:app-phase-templates`, part (i) of 5, snapshot `cr-2026-10-23`.
Source: `sections/07-phase-comparison/section.tex` l.3369–3384.

LaTeX (verbatim, `section.tex` l.3369–3384):
```latex
\begin{lemma}[Kernel templates]\label{lem:app-phase-templates}
In each of the following cases there are constants $N_{\rm T}$, $K_f\ge0$,
$K_s>0$, $\upsilon>1$ and $\mathsf b\in(0,1)$, depending only on $\alpha$, such that for
$N\ge N_{\rm T}$ the kernel $g_j$ satisfies \cref{eqn:app-phase-template} with
$q=q_j$ on $0\le v\le N^{q_j}-1$:
\begin{enumerate}[label=(\roman*)]
\item \SignSVD, $0<\alpha<1$: $K_f=0$, $K_s=4(1-\frac\alpha2)/(1-\alpha)$, $\mathsf b=\frac12$;
\item \SignSVD, $1<\alpha<2$: $K_f=0$, $K_s=4(1-\frac\alpha2)E_{\alpha,\alpha/2}$, $\mathsf b=2-\frac2\alpha$;
\item \SignSGD, $0<\alpha<\frac12$: $K_f=0$,
$K_s=2(1-\frac2\pi)/(1-\alpha)+\frac4\pi(1-\alpha)/(1-2\alpha)$, $\mathsf b=\frac12$;
\item \SignSGD, $\frac12<\alpha<1$: $K_f=0$,
$K_s=2(1-\frac2\pi)/(1-\alpha)+\frac4\pi(1-\alpha)E_{2\alpha,\alpha}$,
$\mathsf b=\max\{2-\frac1\alpha,\frac12\}$;
\item \SignSGD, $\alpha>1$: the constants \cref{eqn:app-phase-Gtemplate}, for all $v\ge0$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_templates_i {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ NT : ℕ, ∃ υ : ℝ, 1 < υ ∧ ∀ N : ℕ, NT ≤ N →
      phaseTemplate (svdKernel α N) (N : ℝ) ((N : ℝ) ^ (α / 2) - 1) (α / 2)
        0 (4 * (1 - α / 2) / (1 - α)) υ (1 / 2) := by
  refine ⟨1, 2, by norm_num, ?_⟩
  intro N hN
  unfold phaseTemplate
  intro v hv0 hvU
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hc : 0 < 1 - α := by linarith
  have hRpos : (0 : ℝ) < (N : ℝ) ^ (1 - α / 2) := Real.rpow_pos_of_pos hNpos _
  have hHhalf1 := tp_Hsum_ge_one (α / 2) N hN
  have hHhalf_lb := lem_app_phase_harmonic_ii (a := α / 2) (by linarith) (by linarith) N hN
  have hHa := tp_H_upper hα0 hα1 N hN
  have hY0 : 0 ≤ (N : ℝ) ^ (1 - α) := Real.rpow_nonneg hNpos.le _
  have hHa' : Hsum α N ≤ (2 - α) / (1 - α) * (N : ℝ) ^ (1 - α) := by
    have e : (2 - α) / (1 - α) * (N : ℝ) ^ (1 - α) - (1 + ((N : ℝ) ^ (1 - α) - 1) / (1 - α))
        = (N : ℝ) ^ (1 - α) + α / (1 - α) := by
      field_simp
      ring
    have hα' : 0 ≤ α / (1 - α) := div_nonneg hα0.le hc.le
    linarith
  have hR : (N : ℝ) ^ (1 - α) = (N : ℝ) ^ (1 - α / 2) * (N : ℝ) ^ (-(α / 2)) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  rw [hR] at hHa'
  have hLv : svdKernel α N v ≤ 2 / Hsum (α / 2) N * Hsum α N := by
    unfold svdKernel
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) (by linarith))
    calc Lsum (N : ℕ∞) α (α / 2) v ≤ Lsum (N : ℕ∞) α (α / 2) 0 := tp_Lsum_anti N α (α / 2) hv0
      _ = Hsum α N := tp_Lsum_zero N α (α / 2)
  have h1 : 2 / Hsum (α / 2) N ≤ 2 / (N : ℝ) ^ (1 - α / 2) :=
    div_le_div_of_nonneg_left (by norm_num) hRpos hHhalf_lb
  have hfin : 2 / Hsum (α / 2) N * Hsum α N
      ≤ 4 * (1 - α / 2) / (1 - α) * (N : ℝ) ^ (-(α / 2)) := by
    have hH1 : (0 : ℝ) ≤ Hsum α N := by linarith [tp_Hsum_ge_one α N hN]
    calc 2 / Hsum (α / 2) N * Hsum α N
        ≤ 2 / (N : ℝ) ^ (1 - α / 2) * Hsum α N := mul_le_mul_of_nonneg_right h1 hH1
      _ ≤ 2 / (N : ℝ) ^ (1 - α / 2) * ((2 - α) / (1 - α) *
            ((N : ℝ) ^ (1 - α / 2) * (N : ℝ) ^ (-(α / 2)))) :=
          mul_le_mul_of_nonneg_left hHa' (by positivity)
      _ = 4 * (1 - α / 2) / (1 - α) * (N : ℝ) ^ (-(α / 2)) := by
          field_simp
          ring
  have hQpos : (0 : ℝ) < (N : ℝ) ^ (α / 2) := Real.rpow_pos_of_pos hNpos _
  have hle : (1 + v) / (N : ℝ) ^ (α / 2) ≤ 1 := (div_le_one hQpos).2 (by linarith)
  have hX : 1 ≤ ((1 + v) / (N : ℝ) ^ (α / 2)) ^ (-(1 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (div_pos (by linarith) hQpos) hle (by norm_num)
  have hKs : 0 ≤ 4 * (1 - α / 2) / (1 - α) := div_nonneg (by linarith) hc.le
  have hT : 0 ≤ (N : ℝ) ^ (-(α / 2)) := Real.rpow_nonneg hNpos.le _
  rw [zero_mul, zero_add]
  calc svdKernel α N v ≤ 4 * (1 - α / 2) / (1 - α) * (N : ℝ) ^ (-(α / 2)) := hLv.trans hfin
    _ ≤ 4 * (1 - α / 2) / (1 - α) * (N : ℝ) ^ (-(α / 2))
          * ((1 + v) / (N : ℝ) ^ (α / 2)) ^ (-(1 / 2 : ℝ)) :=
        le_mul_of_one_le_right (mul_nonneg hKs hT) hX

/-- `lem:app-phase-templates`, part (ii) of 5, snapshot `cr-2026-10-23`.
Source: `sections/07-phase-comparison/section.tex` l.3369–3384.

LaTeX (verbatim, `section.tex` l.3369–3384):
```latex
\begin{lemma}[Kernel templates]\label{lem:app-phase-templates}
In each of the following cases there are constants $N_{\rm T}$, $K_f\ge0$,
$K_s>0$, $\upsilon>1$ and $\mathsf b\in(0,1)$, depending only on $\alpha$, such that for
$N\ge N_{\rm T}$ the kernel $g_j$ satisfies \cref{eqn:app-phase-template} with
$q=q_j$ on $0\le v\le N^{q_j}-1$:
\begin{enumerate}[label=(\roman*)]
\item \SignSVD, $0<\alpha<1$: $K_f=0$, $K_s=4(1-\frac\alpha2)/(1-\alpha)$, $\mathsf b=\frac12$;
\item \SignSVD, $1<\alpha<2$: $K_f=0$, $K_s=4(1-\frac\alpha2)E_{\alpha,\alpha/2}$, $\mathsf b=2-\frac2\alpha$;
\item \SignSGD, $0<\alpha<\frac12$: $K_f=0$,
$K_s=2(1-\frac2\pi)/(1-\alpha)+\frac4\pi(1-\alpha)/(1-2\alpha)$, $\mathsf b=\frac12$;
\item \SignSGD, $\frac12<\alpha<1$: $K_f=0$,
$K_s=2(1-\frac2\pi)/(1-\alpha)+\frac4\pi(1-\alpha)E_{2\alpha,\alpha}$,
$\mathsf b=\max\{2-\frac1\alpha,\frac12\}$;
\item \SignSGD, $\alpha>1$: the constants \cref{eqn:app-phase-Gtemplate}, for all $v\ge0$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_templates_ii {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    ∃ NT : ℕ, ∃ υ : ℝ, 1 < υ ∧ ∀ N : ℕ, NT ≤ N →
      phaseTemplate (svdKernel α N) (N : ℝ) ((N : ℝ) ^ (α / 2) - 1) (α / 2)
        0 (4 * (1 - α / 2) * Epq α (α / 2)) υ (2 - 2 / α) := by
  obtain ⟨NT, hNT⟩ := tp_big_N (1 - α / 2) (by linarith)
  refine ⟨NT + 1, 2, by norm_num, ?_⟩
  intro N hN
  unfold phaseTemplate
  intro v hv0 _
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h2 := hNT N (by omega)
  have hHlb := tp_H_lower (a := α / 2) (by linarith) (by linarith) N hN1 h2
  have hS := lem_app_phase_sums_i (a := α) (q := α / 2) hα1 (by linarith) (N : ℕ∞) hv0
  have hαne : α ≠ 0 := (by linarith : (0 : ℝ) < α).ne'
  have hd : dAQ α (α / 2) = 2 - 2 / α := by
    unfold dAQ
    field_simp
  rw [hd] at hS
  have hE := tp_Epq_nonneg α (α / 2) hα1
  have hRpos : (0 : ℝ) < (N : ℝ) ^ (1 - α / 2) := Real.rpow_pos_of_pos hNpos _
  have hHpos : 0 < (N : ℝ) ^ (1 - α / 2) / (2 * (1 - α / 2)) := div_pos hRpos (by linarith)
  have hinv : α * (1 / α) = 1 := mul_one_div_cancel hαne
  have hexp : (α / 2) * (2 - 2 / α) - α / 2 = -(1 - α / 2) := by
    linear_combination (-1 : ℝ) * hinv
  have hH2 : 2 / Hsum (α / 2) N ≤ 4 * (1 - α / 2) * (N : ℝ) ^ ((α / 2) * (2 - 2 / α) - α / 2) := by
    rw [hexp, Real.rpow_neg hNpos.le]
    have h1 : 2 / Hsum (α / 2) N ≤ 2 / ((N : ℝ) ^ (1 - α / 2) / (2 * (1 - α / 2))) :=
      div_le_div_of_nonneg_left (by norm_num) hHpos hHlb
    have h2' : 2 / ((N : ℝ) ^ (1 - α / 2) / (2 * (1 - α / 2)))
        = 4 * (1 - α / 2) * ((N : ℝ) ^ (1 - α / 2))⁻¹ := by
      rw [div_div_eq_mul_div]
      ring
    linarith
  have hcoef : 0 ≤ 2 / Hsum (α / 2) N :=
    div_nonneg (by norm_num) (by linarith [tp_Hsum_ge_one (α / 2) N hN1])
  have ht := tp_templ_id (N : ℝ) (α / 2) (2 - 2 / α) v hNpos hv0
  rw [zero_mul, zero_add]
  calc svdKernel α N v = 2 / Hsum (α / 2) N * Lsum (N : ℕ∞) α (α / 2) v := rfl
    _ ≤ 2 / Hsum (α / 2) N * (Epq α (α / 2) * (1 + v) ^ (-(2 - 2 / α))) :=
        mul_le_mul_of_nonneg_left hS hcoef
    _ ≤ 4 * (1 - α / 2) * (N : ℝ) ^ ((α / 2) * (2 - 2 / α) - α / 2)
          * (Epq α (α / 2) * (1 + v) ^ (-(2 - 2 / α))) :=
        mul_le_mul_of_nonneg_right hH2 (mul_nonneg hE (Real.rpow_nonneg (by linarith) _))
    _ = 4 * (1 - α / 2) * Epq α (α / 2) * (N : ℝ) ^ (-(α / 2))
          * ((1 + v) / (N : ℝ) ^ (α / 2)) ^ (-(2 - 2 / α)) := by
        linear_combination (-(4 * (1 - α / 2) * Epq α (α / 2))) * ht

lemma tp_H_lower_deficit {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (N : ℕ) (hN : 1 ≤ N) :
    ((N : ℝ) ^ (1 - a) - 1) / (1 - a) ≤ Hsum a N := by
  have h := (lem_app_phase_harmonic_i ha N hN).1
  rw [integral_rpow (Or.inl (by linarith)),
    show -a + 1 = 1 - a by ring, Real.one_rpow] at h
  refine le_trans ?_ h
  apply div_le_div_of_nonneg_right _ (by linarith)
  have := Real.rpow_le_rpow (Nat.cast_nonneg N)
    (show (N : ℝ) ≤ (N : ℝ) + 1 by linarith) (show 0 ≤ 1 - a by linarith)
  linarith

lemma tp_g1_bound {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (N : ℕ) (hN : 1 ≤ N) (v : ℝ) (hv : 0 ≤ v) :
    2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α v
      ≤ (2 * (1 - 2 / Real.pi) / (1 - α)) * (N : ℝ) ^ (-α) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < 1 - α := by linarith
  have hH : Hsum α N ≤ (N : ℝ) ^ (1 - α) / (1 - α) := by
    have hu := tp_H_upper hα0 hα1 N hN
    have he : 1 + ((N : ℝ) ^ (1 - α) - 1) / (1 - α)
        = ((N : ℝ) ^ (1 - α) - α) / (1 - α) := by field_simp; ring
    rw [he] at hu
    exact hu.trans (div_le_div_of_nonneg_right (by linarith) hc.le)
  have hL : Lsum (N : ℕ∞) α α v ≤ Hsum α N := by
    rw [← tp_Lsum_zero N α α]
    exact tp_Lsum_anti N α α hv
  have hcoef : 0 ≤ 2 * (1 - 2 / Real.pi) / (N : ℝ) :=
    div_nonneg (mul_nonneg zero_le_two tp_pi_facts.1) hNp.le
  calc _ ≤ 2 * (1 - 2 / Real.pi) / (N : ℝ) * ((N : ℝ) ^ (1 - α) / (1 - α)) :=
      mul_le_mul_of_nonneg_left (hL.trans hH) hcoef
    _ = _ := by
      rw [Real.rpow_sub hNp, Real.rpow_one, Real.rpow_neg hNp.le]
      field_simp

lemma tp_H_ratio_subcritical {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 2)
    (N : ℕ) (hN : 1 ≤ N) (hsmall : (N : ℝ) ^ (-α) ≤ 2 * α) :
    Hsum (2 * α) N / Hsum α N
      ≤ (1 - α) / (1 - 2 * α) * (N : ℝ) ^ (-α) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < 1 - α := by linarith
  have hb : 0 < 1 - 2 * α := by linarith
  have hH : 0 < Hsum α N := lt_of_lt_of_le zero_lt_one (tp_Hsum_ge_one α N hN)
  have hupper := tp_H_upper (a := 2 * α) (by linarith) (by linarith) N hN
  have hlower := tp_H_lower_deficit hα0 (by linarith) N hN
  have hu : (1 - 2 * α) * Hsum (2 * α) N ≤ (N : ℝ) ^ (1 - 2 * α) - 2 * α := by
    have he : 1 + ((N : ℝ) ^ (1 - 2 * α) - 1) / (1 - 2 * α)
        = ((N : ℝ) ^ (1 - 2 * α) - 2 * α) / (1 - 2 * α) := by field_simp; ring
    rw [he] at hupper
    have := (le_div_iff₀ hb).1 hupper
    nlinarith
  have hl : (N : ℝ) ^ (1 - α) - 1 ≤ (1 - α) * Hsum α N := by
    have := (div_le_iff₀ hc).1 hlower
    nlinarith
  have hp : (N : ℝ) ^ (-α) * (N : ℝ) ^ (1 - α) = (N : ℝ) ^ (1 - 2 * α) := by
    rw [← Real.rpow_add hNp]; congr 1; ring
  have hm := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hNp.le (-α))
  rw [mul_sub, hp, mul_one] at hm
  rw [div_le_iff₀ hH]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hb]
  nlinarith

/-- `lem:app-phase-templates`, part (iii) of 5, snapshot `cr-2026-10-23`.
Source: `sections/07-phase-comparison/section.tex` l.3369–3384.

LaTeX (verbatim, `section.tex` l.3369–3384):
```latex
\begin{lemma}[Kernel templates]\label{lem:app-phase-templates}
In each of the following cases there are constants $N_{\rm T}$, $K_f\ge0$,
$K_s>0$, $\upsilon>1$ and $\mathsf b\in(0,1)$, depending only on $\alpha$, such that for
$N\ge N_{\rm T}$ the kernel $g_j$ satisfies \cref{eqn:app-phase-template} with
$q=q_j$ on $0\le v\le N^{q_j}-1$:
\begin{enumerate}[label=(\roman*)]
\item \SignSVD, $0<\alpha<1$: $K_f=0$, $K_s=4(1-\frac\alpha2)/(1-\alpha)$, $\mathsf b=\frac12$;
\item \SignSVD, $1<\alpha<2$: $K_f=0$, $K_s=4(1-\frac\alpha2)E_{\alpha,\alpha/2}$, $\mathsf b=2-\frac2\alpha$;
\item \SignSGD, $0<\alpha<\frac12$: $K_f=0$,
$K_s=2(1-\frac2\pi)/(1-\alpha)+\frac4\pi(1-\alpha)/(1-2\alpha)$, $\mathsf b=\frac12$;
\item \SignSGD, $\frac12<\alpha<1$: $K_f=0$,
$K_s=2(1-\frac2\pi)/(1-\alpha)+\frac4\pi(1-\alpha)E_{2\alpha,\alpha}$,
$\mathsf b=\max\{2-\frac1\alpha,\frac12\}$;
\item \SignSGD, $\alpha>1$: the constants \cref{eqn:app-phase-Gtemplate}, for all $v\ge0$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_templates_iii {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 2) :
    ∃ NT : ℕ, ∃ υ : ℝ, 1 < υ ∧ ∀ N : ℕ, NT ≤ N →
      phaseTemplate (sgdKernel α N) (N : ℝ) ((N : ℝ) ^ α - 1) α
        0 (2 * (1 - 2 / Real.pi) / (1 - α) + 4 / Real.pi * (1 - α) / (1 - 2 * α)) υ (1 / 2) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα0).comp tendsto_natCast_atTop_atTop
  obtain ⟨NT, hNT⟩ := eventually_atTop.1 (hpow.eventually (eventually_ge_atTop (1 / (2 * α))))
  refine ⟨max NT 1, 2, by norm_num, ?_⟩
  intro N hN v hv0 hvU
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsmall : (N : ℝ) ^ (-α) ≤ 2 * α := by
    rw [Real.rpow_neg hNp.le, inv_eq_one_div, div_le_iff₀ (Real.rpow_pos_of_pos hNp _)]
    have := (div_le_iff₀ (show 0 < 2 * α by linarith)).1 (hNT N (le_trans (le_max_left _ _) hN))
    nlinarith
  have hratio := tp_H_ratio_subcritical hα0 hα1 N hN1 hsmall
  have hg1 := tp_g1_bound hα0 (by linarith) N hN1 v hv0
  have hg2 : 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α v
      ≤ (4 / Real.pi * (1 - α) / (1 - 2 * α)) * (N : ℝ) ^ (-α) := by
    have hH : 0 < Hsum α N := lt_of_lt_of_le zero_lt_one (tp_Hsum_ge_one α N hN1)
    have hL : Lsum (N : ℕ∞) (2 * α) α v ≤ Hsum (2 * α) N := by
      rw [← tp_Lsum_zero N (2 * α) α]
      exact tp_Lsum_anti N (2 * α) α hv0
    calc _ ≤ 4 / (Real.pi * Hsum α N) * Hsum (2 * α) N :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      _ = (4 / Real.pi) * (Hsum (2 * α) N / Hsum α N) := by ring
      _ ≤ (4 / Real.pi) * ((1 - α) / (1 - 2 * α) * (N : ℝ) ^ (-α)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  have hX : 1 ≤ ((1 + v) / (N : ℝ) ^ α) ^ (-(1 / 2 : ℝ)) := by
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    · exact div_pos (by linarith) (Real.rpow_pos_of_pos hNp _)
    · exact (div_le_one (Real.rpow_pos_of_pos hNp _)).2 (by linarith)
    · norm_num
  have hK : 0 ≤ 2 * (1 - 2 / Real.pi) / (1 - α) + 4 / Real.pi * (1 - α) / (1 - 2 * α) := by
    have hp := tp_pi_facts.1
    have hc : 0 < 1 - α := by linarith
    have hb : 0 < 1 - 2 * α := by linarith
    positivity
  change sgdKernel α N v ≤ _
  rw [zero_mul, zero_add]
  calc sgdKernel α N v ≤
      (2 * (1 - 2 / Real.pi) / (1 - α) + 4 / Real.pi * (1 - α) / (1 - 2 * α))
        * (N : ℝ) ^ (-α) := by unfold sgdKernel; nlinarith [hg1, hg2]
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hK (Real.rpow_nonneg hNp.le _)) hX


lemma tp_Lsum_deficit {a : ℝ} (ha : 1 < a) (q : ℝ)
    (N : ℕ) (hN : 1 ≤ N) (v : ℝ) (hv : 0 ≤ v) :
    Lsum (N : ℕ∞) a q v ≤ Za a - 1 + Real.exp (-(2 * v)) := by
  have hH : Hsum a N ≤ Za a := by
    have h1 := (lem_app_phase_harmonic_vi ha N hN).1
    have h2 := (lem_app_phase_harmonic_vi ha 1 le_rfl).2
    have he : Hsum a 1 = 1 := by simp [Hsum]
    rw [he, Nat.cast_one, Real.one_rpow] at h2
    unfold Za
    linarith
  have hnn : ∀ i ∈ Finset.Icc 1 N,
      0 ≤ (i : ℝ) ^ (-a) - (i : ℝ) ^ (-a) * Real.exp (-(2 * v) * (i : ℝ) ^ (-q)) := by
    intro i _
    have hexp : Real.exp (-(2 * v) * (i : ℝ) ^ (-q)) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg i) (-q)]
    have := mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg (Nat.cast_nonneg i) (-a))
    linarith
  have hsingle := Finset.single_le_sum hnn (Finset.mem_Icc.2 ⟨le_rfl, hN⟩)
  simp only [Nat.cast_one, Real.one_rpow, one_mul, mul_one] at hsingle
  rw [Finset.sum_sub_distrib, ← tp_Lsum_fin] at hsingle
  change 1 - Real.exp (-(2 * v)) ≤ Hsum a N - Lsum (N : ℕ∞) a q v at hsingle
  linarith

-- Copies of the private summability helpers in PowerSums.
lemma tp_ps_summable {a : ℝ} (ha : 1 < a) :
    Summable (fun i : ℕ => if 0 < i then (i : ℝ) ^ (-a) else 0) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    (Real.summable_nat_rpow.mpr (by linarith : -a < -1))
  · split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg i) _
    · exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (Nat.cast_nonneg i) _

lemma tp_ps_term_summable {a q u : ℝ} (ha : 1 < a) (hu : 0 ≤ u) :
    Summable (fun i : ℕ =>
      if 0 < i then (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (tp_ps_summable ha)
  · split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le
    · exact le_rfl
  · split_ifs
    · have hx : -(2 * u) * (i : ℝ) ^ (-q) ≤ 0 := by
        nlinarith [mul_nonneg hu (Real.rpow_nonneg (Nat.cast_nonneg i) (-q))]
      exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg i) _)
        (Real.exp_le_one_iff.mpr hx)
    · exact le_rfl

lemma tp_Lsum_laplace {a q : ℝ} (ha : 1 < a) (hq : 0 < q)
    (N : ℕ) (u : ℝ) (hu : 1 ≤ u) :
    Lsum (N : ℕ∞) a q u ≤ Epq a q * (2 * u) ^ (-dAQ a q) := by
  have hu0 : 0 < u := by linarith
  have hsum := tp_ps_term_summable (q := q) ha hu0.le
  have hL : Lsum (N : ℕ∞) a q u ≤ ∑' i : ℕ,
      (if 0 < i then (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) := by
    rw [tp_Lsum_fin]
    convert hsum.sum_le_tsum (Finset.Icc 1 N) (fun i _ => ?_) using 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [if_pos (by have := (Finset.mem_Icc.1 hi).1; omega)]
    · split_ifs
      · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le
      · exact le_rfl
  have hlap := (abs_le.mp (lem_app_phase_laplace_i (p := a) (q := q)
    (a := 2 * u) ha hq (by positivity))).2
  have hd : dAQ a q = (a - 1) / q := rfl
  have he : -(a / q) = -(1 / q) + -dAQ a q := by unfold dAQ; ring
  have hpow : (2 * u) ^ (-(1 / q)) ≤ (2 : ℝ) ^ (-(1 / q)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (neg_nonpos.2 (by positivity))
  have hM : 0 ≤ Mpq a q := by unfold Mpq; positivity
  have herror : 2 * Mpq a q * (2 * u) ^ (-(a / q))
      ≤ (2 : ℝ) ^ (1 - 1 / q) * Mpq a q * (2 * u) ^ (-dAQ a q) := by
    rw [he, Real.rpow_add (by positivity)]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (mul_nonneg zero_le_two hM))
      (Real.rpow_nonneg (by positivity : 0 ≤ 2 * u) (-dAQ a q))
    have hk : (2 : ℝ) ^ (1 - 1 / q) = 2 * (2 : ℝ) ^ (-(1 / q)) := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
    rw [hk]
    nlinarith [hh]
  rw [← hd] at hlap
  calc Lsum (N : ℕ∞) a q u ≤
        (Real.Gamma (dAQ a q) / q + (2 : ℝ) ^ (1 - 1 / q) * Mpq a q)
          * (2 * u) ^ (-dAQ a q) := by nlinarith [hL, hlap, herror]
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)

lemma tp_Lsum_envelope_slack {a q : ℝ} (ha : 1 < a) (hq : 0 < q) :
    ∃ E : ℝ, 0 ≤ E ∧ E < Epq a q ∧ ∀ N : ℕ, 1 ≤ N → ∀ v : ℝ, 0 ≤ v →
      Lsum (N : ℕ∞) a q v ≤ E * (1 + v) ^ (-dAQ a q) := by
  let d := dAQ a q
  let Z := Za a
  let B := Z - 1 + Real.exp (-1)
  have hd : 0 < d := div_pos (by linarith) hq
  have hZ : 1 < Z := by
    dsimp [Z, Za]
    have := div_pos one_pos (show 0 < a - 1 by linarith)
    linarith
  have hB0 : 0 < B := by dsimp [B]; positivity
  have hBZ : B < Z := by
    have := Real.exp_lt_one_iff.2 (show (-1 : ℝ) < 0 by norm_num)
    dsimp [B]; linarith
  have hE : 0 < Epq a q := lt_of_lt_of_le (mul_pos (by positivity) (by linarith : 0 < Z))
    (show (2 : ℝ) ^ d * Z ≤ Epq a q from le_max_left _ _)
  have hbase : (1 + (1 : ℝ)) ^ d * B < (2 : ℝ) ^ d * Z := by
    norm_num only [one_add_one_eq_two]
    exact mul_lt_mul_of_pos_left hBZ (by positivity)
  have hcont : ContinuousAt (fun x : ℝ => (1 + x) ^ d * B) 1 := by
    apply ContinuousAt.mul_const
    exact (continuousAt_const.add continuousAt_id).rpow_const (Or.inr hd.le)
  obtain ⟨ε, hε, hεlt⟩ := Metric.eventually_nhds_iff.1
    (hcont.tendsto.eventually_lt_const hbase)
  let r : ℝ := 1 + ε / 2
  have hr : 1 < r := by dsimp [r]; linarith
  have hrB : (1 + r) ^ d * B < (2 : ℝ) ^ d * Z := by
    apply hεlt
    rw [Real.dist_eq, abs_of_pos (by dsimp [r]; linarith : 0 < r - 1)]
    dsimp [r]; linarith
  let R := ((1 + r) / (2 * r)) ^ d
  have hR0 : 0 < R := Real.rpow_pos_of_pos (by positivity) _
  have hR1 : R < 1 := Real.rpow_lt_one (by positivity)
    ((div_lt_one (by positivity)).2 (by linarith)) hd
  let E := max (max ((3 / 2 : ℝ) ^ d * Z) ((1 + r) ^ d * B)) (Epq a q * R)
  have hsmall : (3 / 2 : ℝ) ^ d * Z < Epq a q := by
    apply lt_of_lt_of_le _ (show (2 : ℝ) ^ d * Z ≤ Epq a q from le_max_left _ _)
    exact mul_lt_mul_of_pos_right (Real.rpow_lt_rpow (by norm_num) (by norm_num) hd) (by linarith)
  have hmid : (1 + r) ^ d * B < Epq a q :=
    hrB.trans_le (le_max_left _ _)
  have hlarge : Epq a q * R < Epq a q := mul_lt_of_lt_one_right hE hR1
  have hE0 : 0 ≤ E := le_trans (by positivity : 0 ≤ (3 / 2 : ℝ) ^ d * Z)
    ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨E, hE0, max_lt (max_lt hsmall hmid) hlarge, ?_⟩
  intro N hN v hv
  have hvp : 0 < 1 + v := by linarith
  have hnorm : Lsum (N : ℕ∞) a q v * (1 + v) ^ d ≤ E := by
    by_cases hvsmall : v ≤ 1 / 2
    · have hL : Lsum (N : ℕ∞) a q v ≤ Z := by
        have hh := tp_Lsum_deficit ha q N hN v hv
        have := Real.exp_le_one_iff.2 (show -(2 * v) ≤ 0 by linarith)
        dsimp [Z]; linarith
      have hp : (1 + v) ^ d ≤ (3 / 2 : ℝ) ^ d :=
        Real.rpow_le_rpow hvp.le (by linarith) hd.le
      have hEs : (3 / 2 : ℝ) ^ d * Z ≤ E :=
        (le_max_left _ _).trans (le_max_left _ _)
      exact (mul_le_mul hL hp (Real.rpow_nonneg hvp.le _) (by linarith : 0 ≤ Z)).trans
        (by simpa only [mul_comm] using hEs)
    · have hvhalf : 1 / 2 ≤ v := by linarith
      by_cases hvr : v ≤ r
      · have hL : Lsum (N : ℕ∞) a q v ≤ B := by
          have hh := tp_Lsum_deficit ha q N hN v hv
          have hx := Real.exp_le_exp.2 (show -(2 * v) ≤ -1 by linarith)
          dsimp [B, Z]; linarith
        have hp : (1 + v) ^ d ≤ (1 + r) ^ d :=
          Real.rpow_le_rpow hvp.le (by linarith) hd.le
        have hEm : (1 + r) ^ d * B ≤ E :=
          (le_max_right _ _).trans (le_max_left _ _)
        exact (mul_le_mul hL hp (Real.rpow_nonneg hvp.le _) hB0.le).trans
          (by simpa only [mul_comm] using hEm)
      · have hrv : r ≤ v := by linarith
        have hv1 : 1 ≤ v := by linarith
        have hL := tp_Lsum_laplace ha hq N v hv1
        have hratio : (1 + v) / (2 * v) ≤ (1 + r) / (2 * r) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have hp : (2 * v) ^ (-d) * (1 + v) ^ d ≤ R := by
          rw [Real.rpow_neg (by positivity : 0 ≤ 2 * v), inv_mul_eq_div,
            ← Real.div_rpow hvp.le (by positivity)]
          exact Real.rpow_le_rpow (by positivity) hratio hd.le
        have hm := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hvp.le d)
        have hfinal := mul_le_mul_of_nonneg_left hp hE.le
        exact (by dsimp [d] at *; nlinarith : Lsum (N : ℕ∞) a q v * (1 + v) ^ d ≤ Epq a q * R).trans
          (le_max_right _ _)
  have hcancel : (1 + v) ^ d * (1 + v) ^ (-d) = 1 := by
    rw [← Real.rpow_add hvp, add_neg_cancel, Real.rpow_zero]
  have := mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg hvp.le (-d))
  simpa only [mul_assoc, hcancel, mul_one] using this

/-- `lem:app-phase-templates`, part (iv) of 5, snapshot `cr-2026-10-23`.
Source: `sections/07-phase-comparison/section.tex` l.3369–3384.

LaTeX (verbatim, `section.tex` l.3369–3384):
```latex
\begin{lemma}[Kernel templates]\label{lem:app-phase-templates}
In each of the following cases there are constants $N_{\rm T}$, $K_f\ge0$,
$K_s>0$, $\upsilon>1$ and $\mathsf b\in(0,1)$, depending only on $\alpha$, such that for
$N\ge N_{\rm T}$ the kernel $g_j$ satisfies \cref{eqn:app-phase-template} with
$q=q_j$ on $0\le v\le N^{q_j}-1$:
\begin{enumerate}[label=(\roman*)]
\item \SignSVD, $0<\alpha<1$: $K_f=0$, $K_s=4(1-\frac\alpha2)/(1-\alpha)$, $\mathsf b=\frac12$;
\item \SignSVD, $1<\alpha<2$: $K_f=0$, $K_s=4(1-\frac\alpha2)E_{\alpha,\alpha/2}$, $\mathsf b=2-\frac2\alpha$;
\item \SignSGD, $0<\alpha<\frac12$: $K_f=0$,
$K_s=2(1-\frac2\pi)/(1-\alpha)+\frac4\pi(1-\alpha)/(1-2\alpha)$, $\mathsf b=\frac12$;
\item \SignSGD, $\frac12<\alpha<1$: $K_f=0$,
$K_s=2(1-\frac2\pi)/(1-\alpha)+\frac4\pi(1-\alpha)E_{2\alpha,\alpha}$,
$\mathsf b=\max\{2-\frac1\alpha,\frac12\}$;
\item \SignSGD, $\alpha>1$: the constants \cref{eqn:app-phase-Gtemplate}, for all $v\ge0$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_templates_iv {α : ℝ} (hα1 : 1 / 2 < α) (hα2 : α < 1) :
    ∃ NT : ℕ, ∃ υ : ℝ, 1 < υ ∧ ∀ N : ℕ, NT ≤ N →
      phaseTemplate (sgdKernel α N) (N : ℝ) ((N : ℝ) ^ α - 1) α
        0 (2 * (1 - 2 / Real.pi) / (1 - α) + 4 / Real.pi * (1 - α) * Epq (2 * α) α) υ
        (max (2 - 1 / α) (1 / 2)) := by
  have hα0 : 0 < α := by linarith
  have hc : 0 < 1 - α := by linarith
  have ha : 1 < 2 * α := by linarith
  obtain ⟨E, hE0, hEE, henv⟩ := tp_Lsum_envelope_slack ha hα0
  have hEp : 0 < Epq (2 * α) α := lt_of_le_of_lt hE0 hEE
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - α)) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  obtain ⟨NT, hNT⟩ := eventually_atTop.1 (hpow.eventually
    (eventually_ge_atTop (Epq (2 * α) α / (Epq (2 * α) α - E))))
  refine ⟨max NT 1, 2, by norm_num, ?_⟩
  intro N hN v hv0 hvU
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hH : 0 < Hsum α N := lt_of_lt_of_le zero_lt_one (tp_Hsum_ge_one α N hN1)
  have hR : 0 < (N : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos hNp _
  have hcoef : E / Hsum α N ≤ (1 - α) * Epq (2 * α) α / (N : ℝ) ^ (1 - α) := by
    have hl := (div_le_iff₀ hc).1 (tp_H_lower_deficit hα0 hα2 N hN1)
    have hlarge := (div_le_iff₀ (sub_pos.2 hEE)).1
      (hNT N (le_trans (le_max_left _ _) hN))
    rw [div_le_div_iff₀ hH hR]
    nlinarith
  let b := max (2 - 1 / α) (1 / 2)
  have hb : 0 ≤ b := le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_max_right _ _)
  have hd : dAQ (2 * α) α = 2 - 1 / α := by
    unfold dAQ
    field_simp [hα0.ne']
    <;> ring
  have hidentity : α * (2 - 1 / α) - α = -(1 - α) := by
    field_simp [hα0.ne']
    <;> ring
  have hg1 := tp_g1_bound hα0 hα2 N hN1 v hv0
  have hg2 : 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α v
      ≤ (4 / Real.pi * (1 - α) * Epq (2 * α) α) * (N : ℝ) ^ (-α)
        * ((1 + v) / (N : ℝ) ^ α) ^ (-(2 - 1 / α)) := by
    have henvN := henv N hN1 v hv0
    rw [hd] at henvN
    have ht := tp_templ_id (N : ℝ) α (2 - 1 / α) v hNp hv0
    rw [hidentity] at ht
    calc _ ≤ 4 / (Real.pi * Hsum α N) * (E * (1 + v) ^ (-(2 - 1 / α))) :=
        mul_le_mul_of_nonneg_left henvN (by positivity)
      _ = (4 / Real.pi) * (E / Hsum α N) * (1 + v) ^ (-(2 - 1 / α)) := by ring
      _ ≤ (4 / Real.pi) * ((1 - α) * Epq (2 * α) α / (N : ℝ) ^ (1 - α))
            * (1 + v) ^ (-(2 - 1 / α)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef (by positivity))
          (Real.rpow_nonneg (by linarith) _)
      _ = _ := by
        calc _ = (4 / Real.pi * (1 - α) * Epq (2 * α) α)
              * (((N : ℝ) ^ (1 - α))⁻¹ * (1 + v) ^ (-(2 - 1 / α))) := by ring
          _ = _ := by rw [← Real.rpow_neg hNp.le (1 - α), ← ht]; ring
  have hXp : 0 < (1 + v) / (N : ℝ) ^ α :=
    div_pos (by linarith) (Real.rpow_pos_of_pos hNp _)
  have hX1 : (1 + v) / (N : ℝ) ^ α ≤ 1 :=
    (div_le_one (Real.rpow_pos_of_pos hNp _)).2 (by linarith)
  have hX : 1 ≤ ((1 + v) / (N : ℝ) ^ α) ^ (-b) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hXp hX1 (neg_nonpos.2 hb)
  have hmono : ((1 + v) / (N : ℝ) ^ α) ^ (-(2 - 1 / α))
      ≤ ((1 + v) / (N : ℝ) ^ α) ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_ge hXp hX1 (neg_le_neg (le_max_left _ _))
  have hC1 : 0 ≤ 2 * (1 - 2 / Real.pi) / (1 - α) :=
    div_nonneg (mul_nonneg zero_le_two tp_pi_facts.1) hc.le
  have hC2 : 0 ≤ 4 / Real.pi * (1 - α) * Epq (2 * α) α := by positivity
  have hg1' := hg1.trans (le_mul_of_one_le_right
    (mul_nonneg hC1 (Real.rpow_nonneg hNp.le (-α))) hX)
  have hg2' := hg2.trans (mul_le_mul_of_nonneg_left hmono
    (mul_nonneg hC2 (Real.rpow_nonneg hNp.le (-α))))
  change sgdKernel α N v ≤ _
  rw [zero_mul, zero_add]
  dsimp only [b] at hg1' hg2'
  unfold sgdKernel
  nlinarith [hg1', hg2']


/-- `lem:app-phase-templates`, part (v) of 5, snapshot `cr-2026-10-23`.
Source: `sections/07-phase-comparison/section.tex` l.3369–3384.

LaTeX (verbatim, `section.tex` l.3369–3384):
```latex
\begin{lemma}[Kernel templates]\label{lem:app-phase-templates}
In each of the following cases there are constants $N_{\rm T}$, $K_f\ge0$,
$K_s>0$, $\upsilon>1$ and $\mathsf b\in(0,1)$, depending only on $\alpha$, such that for
$N\ge N_{\rm T}$ the kernel $g_j$ satisfies \cref{eqn:app-phase-template} with
$q=q_j$ on $0\le v\le N^{q_j}-1$:
\begin{enumerate}[label=(\roman*)]
\item \SignSVD, $0<\alpha<1$: $K_f=0$, $K_s=4(1-\frac\alpha2)/(1-\alpha)$, $\mathsf b=\frac12$;
\item \SignSVD, $1<\alpha<2$: $K_f=0$, $K_s=4(1-\frac\alpha2)E_{\alpha,\alpha/2}$, $\mathsf b=2-\frac2\alpha$;
\item \SignSGD, $0<\alpha<\frac12$: $K_f=0$,
$K_s=2(1-\frac2\pi)/(1-\alpha)+\frac4\pi(1-\alpha)/(1-2\alpha)$, $\mathsf b=\frac12$;
\item \SignSGD, $\frac12<\alpha<1$: $K_f=0$,
$K_s=2(1-\frac2\pi)/(1-\alpha)+\frac4\pi(1-\alpha)E_{2\alpha,\alpha}$,
$\mathsf b=\max\{2-\frac1\alpha,\frac12\}$;
\item \SignSGD, $\alpha>1$: the constants \cref{eqn:app-phase-Gtemplate}, for all $v\ge0$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_templates_v {α : ℝ} (hα : 1 < α) :
    ∃ NT : ℕ, ∀ N : ℕ, NT ≤ N → ∀ v : ℝ, 0 ≤ v →
      sgdKernel α N v
        ≤ 4 / Real.pi * Epq (2 * α) α * (1 + v) ^ (-(2 - 1 / α))
          + 2 * (1 - 2 / Real.pi) * Epq α α * (N : ℝ) ^ (-α)
            * ((1 + v) / (N : ℝ) ^ α) ^ (-(1 - 1 / α)) :=
  ⟨1, fun N hN v hv => tp_template_gt hα N hN v hv⟩

end Muon.Phase

end

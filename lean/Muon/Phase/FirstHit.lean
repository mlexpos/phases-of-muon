import Mathlib
import Muon.Foundations.RealAnalysis
import Muon.Phase.Model
import Muon.Phase.Volterra
import Muon.Phase.PowerSums

/-!
# Appendix H: square supersolutions, the clock integral, finite mixtures, forcing integrals

Task L-H.6. Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`, l.1931–2185:
`lem:app-phase-square` (l.1931), `lem:app-phase-clock-integral` (l.2008),
`lem:app-phase-mixture` (l.2111), `lem:app-phase-forcing-integrals` (l.2173).
Card: `sections/07-phase-comparison/CARD.md` §2, §3, §5 (L-H.6), §6.

Encoding decisions:
* The paper's one-sided convolution `g * h` is `Muon.Foundations.oneSidedConv h g`
  (`oneSidedConv f g t = ∫_0^t f(t-s) g(s) ds`), as in `Muon.Phase.Volterra`.
* `lem:app-phase-square`: the case split "either (a) or (b) on `[0,H]`" is a disjunction of
  the two global bounds on `[0,H]`. The clauses that exist only under (b) are stated as
  implications from the (b)-bound.
* The first hit is `Muon.Phase.firstHit` (`ℝ≥0∞`, `inf ∅ = ∞`). A real hit time `û` is
  given by `firstHit Y (T*ε) = ENNReal.ofReal û` with `0 < û`; in the square lemma `û` is
  existentially quantified (it is the first hit of the given solution `Y`).
* `lem:app-phase-square` takes the solution `Y` of the equation as a hypothesis (the
  paper's "let `Y>0` be continuous on `[0,∞)` with `Y=f+√ε g*√Y`"); no existence is asserted.
* `lem:app-phase-mixture`: `Y` is the continuous positive solution, assumed as a hypothesis
  (the paper's "let `Y>0` be the continuous solution"). Existence and uniqueness of that
  solution is the separate declaration `lem_app_phase_mixture_solution` (source l.2130–2131,
  "by `thm:app-phase-volterra`").
  `f`, `g` are the finite sums `mixF`, `mixG`; `H`, `d` are variables with their defining
  equations as hypotheses.
* Helpers introduced here (not in other modules): `aQ` (`a_q`), `Ir` (`I_r`, to be reused by
  L-H.5), `clockEps0` (`ε_0(p,q,T)`, proof-local in the paper), `mixF`, `mixG`, `mixJ`.
  Everything else is reused from `Muon.Phase.PowerSums` (`fNq`, `Lsum`, `rq`, `Cpq`,
  `Aconst`, `Mpq`, `Jpq`, `JN`) and `Muon.Phase.Model` (`firstHit`).
* The rate lemma `lem_app_phase_clock_integral_rate` is the displayed `J − J_N` bound of
  `lem:app-phase-clock-integral`(iii) (l.2096–2100), exposed as its own declaration.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open Muon.Foundations

noncomputable section

namespace Muon.Phase

/-! ## Helpers -/

/-- `a_q = (8q)^{-1/2}` (`lem:app-phase-clock-integral` proof-local constants, l.2001–2004). -/
def aQ (q : ℝ) : ℝ := (8 * q) ^ (-(1 / 2 : ℝ))

/-- `I_r(x) = ∫_0^x (1+w)^{-r} dw` (`section.tex` l.1112–1114). Shared with L-H.5 (prefactors). -/
def Ir (r x : ℝ) : ℝ := ∫ w in (0 : ℝ)..x, (1 + w) ^ (-r)

/-- The proof-local threshold `ε_0(p,q,T)` (`section.tex` l.2001–2004): the minimum of `1/4`,
`1/(8T)`, `C_{p,q}²`, `(A_p/T)²` and `A_p/(T 2^{2r/(1-r)})`, the last entry omitted if `r ≥ 1`. -/
def clockEps0 (p q T : ℝ) : ℝ :=
  if rq p q < 1 then
    min (min (min (min (1 / 4) (1 / (8 * T))) (Cpq p q ^ 2)) ((Aconst p / T) ^ 2))
      (Aconst p / (T * (2 : ℝ) ^ (2 * rq p q / (1 - rq p q))))
  else min (min (min (1 / 4) (1 / (8 * T))) (Cpq p q ^ 2)) ((Aconst p / T) ^ 2)

/-- `f(u) = ∑_{i=1}^n a_i e^{-b_i u}` (`lem:app-phase-mixture`). -/
def mixF {n : ℕ} (a b : Fin n → ℝ) (u : ℝ) : ℝ := ∑ i, a i * Real.exp (-(b i * u))

/-- `g(u) = ∑_{l=1}^{n'} w_l c_l e^{-c_l u}` (`lem:app-phase-mixture`). -/
def mixG {n' : ℕ} (w c : Fin n' → ℝ) (u : ℝ) : ℝ :=
  ∑ l, w l * c l * Real.exp (-(c l * u))

/-- `𝖩 = ∫_0^∞ √f(u) du` (`lem:app-phase-mixture`). -/
def mixJ {n : ℕ} (a b : Fin n → ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), Real.sqrt (mixF a b u)

/-! ## Square supersolution -/

/-- Nonnegativity of the one-sided convolution of nonnegative functions. -/
lemma aux_osc_nonneg {F g : ℝ → ℝ} (hF : ∀ u ∈ Ici (0 : ℝ), 0 ≤ F u)
    (hg : ∀ u ∈ Ici (0 : ℝ), 0 ≤ g u) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ oneSidedConv F g t := by
  unfold oneSidedConv
  refine intervalIntegral.integral_nonneg ht fun s hs => mul_nonneg ?_ ?_
  · exact hF _ (Set.mem_Ici.2 (sub_nonneg.2 hs.2))
  · exact hg _ (Set.mem_Ici.2 hs.1)

lemma aux_refl_cont {F : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hF : ContinuousOn F (Icc 0 t)) :
    ContinuousOn (fun s => F (t - s)) (uIcc 0 t) := by
  rw [uIcc_of_le ht]
  exact hF.comp (continuousOn_const.sub continuousOn_id)
    (fun s hs => ⟨sub_nonneg.2 hs.2, sub_le_self t hs.1⟩)

/-- Monotonicity of the one-sided convolution in its first argument. -/
lemma aux_osc_mono {F₁ F₂ g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hF₁ : ContinuousOn F₁ (Icc 0 t)) (hF₂ : ContinuousOn F₂ (Icc 0 t))
    (hle : ∀ v ∈ Icc (0 : ℝ) t, F₁ v ≤ F₂ v)
    (hg : ∀ u ∈ Ici (0 : ℝ), 0 ≤ g u) (hgi : IntervalIntegrable g volume 0 t) :
    oneSidedConv F₁ g t ≤ oneSidedConv F₂ g t := by
  unfold oneSidedConv
  refine intervalIntegral.integral_mono_on ht (hgi.continuousOn_mul (aux_refl_cont ht hF₁))
    (hgi.continuousOn_mul (aux_refl_cont ht hF₂)) fun s hs => mul_le_mul_of_nonneg_right ?_ ?_
  · exact hle _ ⟨sub_nonneg.2 hs.2, sub_le_self t hs.1⟩
  · exact hg _ (Set.mem_Ici.2 hs.1)

/-- The one-sided convolution is invariant under pointwise equal first arguments. -/
lemma aux_osc_congr {F₁ F₂ g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hEq : ∀ v ∈ Icc (0 : ℝ) t, F₁ v = F₂ v) :
    oneSidedConv F₁ g t = oneSidedConv F₂ g t := by
  unfold oneSidedConv
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  show F₁ (t - s) * g s = F₂ (t - s) * g s
  rw [hEq (t - s) ⟨sub_nonneg.2 hs.2, sub_le_self t hs.1⟩]

lemma aux_osc_const_mul (F g : ℝ → ℝ) (c t : ℝ) :
    oneSidedConv F (fun u => c * g u) t = c * oneSidedConv F g t := by
  unfold oneSidedConv
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun s _ => by
    show F (t - s) * (c * g s) = c * (F (t - s) * g s)
    ring

lemma aux_osc_add_const {F g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (c : ℝ)
    (hF : ContinuousOn F (Icc 0 t)) (hgi : IntervalIntegrable g volume 0 t) :
    oneSidedConv (fun v => F v + c) g t = oneSidedConv F g t + c * ∫ u in (0 : ℝ)..t, g u := by
  have h1 : IntervalIntegrable (fun s => F (t - s) * g s) volume 0 t :=
    hgi.continuousOn_mul (aux_refl_cont ht hF)
  have h2 : IntervalIntegrable (fun s => c * g s) volume 0 t := hgi.const_mul c
  unfold oneSidedConv
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add h1 h2]
  exact intervalIntegral.integral_congr fun s _ => by
    show (F (t - s) + c) * g s = F (t - s) * g s + c * g s
    ring

/-- Shared core of `lem:app-phase-square` (i) and (ii): the two-sided bounds on `[0,H]`. -/
lemma aux_square_core {ε H : ℝ} (hε : 0 < ε) (hH : 0 < H)
    {f g h Y : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Ici 0)) (hg_nonneg : ∀ u ∈ Ici (0 : ℝ), 0 ≤ g u)
    (hg_int : IntegrableOn g (Ioi 0)) (hg_mass : ∫ u in Ioi (0 : ℝ), g u ≤ 1)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_nonneg : ∀ u ∈ Ici (0 : ℝ), 0 ≤ f u)
    (hY_cont : ContinuousOn Y (Ici 0)) (hY_pos : ∀ u ∈ Ici (0 : ℝ), 0 < Y u)
    (hY : ∀ u ∈ Ici (0 : ℝ),
      Y u = f u + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) g u)
    (hh_cont : ContinuousOn h (Icc 0 H)) (hh_ge : ∀ u ∈ Icc (0 : ℝ) H, Real.sqrt ε ≤ h u)
    (hfh : ∀ u ∈ Icc (0 : ℝ) H, f u ≤ h u ^ 2)
    (hab : (∀ u ∈ Icc (0 : ℝ) H, oneSidedConv h g u ≤ 2 * h u) ∨
      (∀ u ∈ Icc (0 : ℝ) H, oneSidedConv h g u ≤ Real.sqrt ε)) :
    (∀ u ∈ Icc (0 : ℝ) H, f u ≤ Y u ∧ Y u ≤ (h u + Real.sqrt ε) ^ 2 ∧
        Y u - f u ≤ 2 * Real.sqrt ε * h u + ε) ∧
      ((∀ u ∈ Icc (0 : ℝ) H, oneSidedConv h g u ≤ Real.sqrt ε) →
        ∀ u ∈ Icc (0 : ℝ) H, Y u - f u ≤ 2 * ε) := by
  have hS : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hS2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hgi : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable g volume 0 t := fun t ht =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 (hg_int.mono_set Ioc_subset_Ioi_self)
  have hM : ∀ s ∈ Icc (0 : ℝ) H, ∫ u in (0 : ℝ)..s, g u ≤ 1 := by
    intro s hs
    rw [intervalIntegral.integral_of_le hs.1]
    exact le_trans (setIntegral_mono_set hg_int
      (ae_restrict_of_forall_mem measurableSet_Ioi
        fun x hx => hg_nonneg x (Set.Ioi_subset_Ici_self hx))
      (Filter.Eventually.of_forall fun x hx => Ioc_subset_Ioi_self hx)) hg_mass
  have hYf : ∀ u ∈ Icc (0 : ℝ) H, f u ≤ Y u := by
    intro u hu
    have h1 := aux_osc_nonneg (F := fun v => Real.sqrt (Y v))
      (fun v _ => Real.sqrt_nonneg _) hg_nonneg hu.1
    rw [hY u (Set.mem_Ici.2 hu.1)]
    nlinarith [mul_nonneg hS.le h1]
  have hcase : ∀ v ∈ Icc (0 : ℝ) H, Real.sqrt ε * oneSidedConv h g v ≤ 2 * Real.sqrt ε * h v := by
    intro v hv
    rcases hab with ha | hb
    · nlinarith [mul_le_mul_of_nonneg_left (ha v hv) hS.le]
    · nlinarith [mul_le_mul_of_nonneg_left (hb v hv) hS.le,
        mul_le_mul_of_nonneg_left (hh_ge v hv) (by positivity : (0:ℝ) ≤ 2 * Real.sqrt ε),
        mul_nonneg hS.le hS.le]
  have hYup : ∀ v ∈ Icc (0 : ℝ) H, Y v ≤ (h v + Real.sqrt ε) ^ 2 := by
    have hkc_nonneg : ∀ w ∈ Ioo (0 : ℝ) H, 0 ≤ Real.sqrt ε * g w := fun w hw =>
      mul_nonneg hS.le (hg_nonneg w (Set.mem_Ici.2 hw.1.le))
    have hkc_int : IntegrableOn (fun w => Real.sqrt ε * g w) (Ioo 0 H) :=
      Integrable.const_mul (hg_int.mono_set Ioo_subset_Ioi_self) _
    have hG : ContinuousOn f (Icc 0 H) := hf_cont.mono Icc_subset_Ici_self
    have hGn : ∀ w ∈ Icc (0 : ℝ) H, 0 ≤ f w := fun w hw => hf_nonneg w (Set.mem_Ici.2 hw.1)
    have hx : ContinuousOn Y (Icc 0 H) := hY_cont.mono Icc_subset_Ici_self
    have hxn : ∀ w ∈ Icc (0 : ℝ) H, 0 ≤ Y w := fun w hw => (hY_pos w (Set.mem_Ici.2 hw.1)).le
    have hy : ContinuousOn (fun u => (h u + Real.sqrt ε) ^ 2) (Icc 0 H) :=
      (hh_cont.add continuousOn_const).pow 2
    have hyn : ∀ w ∈ Icc (0 : ℝ) H, 0 ≤ (h w + Real.sqrt ε) ^ 2 := fun w _ => sq_nonneg _
    have hym : ∀ w ∈ Icc (0 : ℝ) H, ε ≤ (h w + Real.sqrt ε) ^ 2 := by
      intro w hw
      have hh0 : 0 ≤ h w := by linarith [hh_ge w hw]
      nlinarith [mul_nonneg hh0 hh0, mul_nonneg hh0 hS.le]
    have hxsub : ∀ w ∈ Icc (0 : ℝ) H, Y w ≤
        f w + oneSidedConv (fun u => Real.sqrt (Y u)) (fun v => Real.sqrt ε * g v) w := by
      intro w hw
      rw [aux_osc_const_mul]
      exact (hY w (Set.mem_Ici.2 hw.1)).le
    have hysub : ∀ w ∈ Icc (0 : ℝ) H,
        f w + oneSidedConv (fun u => Real.sqrt ((h u + Real.sqrt ε) ^ 2))
          (fun v => Real.sqrt ε * g v) w ≤ (h w + Real.sqrt ε) ^ 2 := by
      intro w hw
      have hsq : oneSidedConv (fun u => Real.sqrt ((h u + Real.sqrt ε) ^ 2)) g w
          = oneSidedConv (fun u => h u + Real.sqrt ε) g w :=
        aux_osc_congr (F₁ := fun u => Real.sqrt ((h u + Real.sqrt ε) ^ 2))
          (F₂ := fun u => h u + Real.sqrt ε) (g := g) hw.1
          (fun v hv => Real.sqrt_sq (by linarith [hh_ge v ⟨hv.1, hv.2.trans hw.2⟩, hS]))
      rw [aux_osc_const_mul, hsq,
        aux_osc_add_const hw.1 (Real.sqrt ε) (hh_cont.mono (Icc_subset_Icc le_rfl hw.2))
          (hgi w hw.1)]
      have hM1 := hM w hw
      nlinarith [hfh w hw, hcase w hw, mul_le_mul_of_nonneg_left hM1 (mul_nonneg hS.le hS.le)]
    have hcmp := lem_app_phase_comparison H hH (fun w => Real.sqrt ε * g w) hkc_nonneg hkc_int
      f hG hGn ε hε Y (fun u => (h u + Real.sqrt ε) ^ 2) hx hxn hy hyn hym hxsub hysub
    intro s hs
    exact hcmp s hs
  have hpt : ∀ v ∈ Icc (0 : ℝ) H, Y v - f v ≤ Real.sqrt ε * oneSidedConv h g v + ε := by
    intro v hv
    have hA : oneSidedConv (fun u => Real.sqrt (Y u)) g v
        ≤ oneSidedConv (fun u => h u + Real.sqrt ε) g v := by
      refine aux_osc_mono (F₁ := fun u => Real.sqrt (Y u)) (F₂ := fun u => h u + Real.sqrt ε)
        hv.1 ?_ ?_ ?_ hg_nonneg (hgi v hv.1)
      · exact (hY_cont.mono (Icc_subset_Ici_self)).sqrt
      · exact (hh_cont.mono (Icc_subset_Icc le_rfl hv.2)).add continuousOn_const
      · intro w hw
        exact (Real.sqrt_le_sqrt (hYup w ⟨hw.1, hw.2.trans hv.2⟩)).trans_eq
          (Real.sqrt_sq (by linarith [hh_ge w ⟨hw.1, hw.2.trans hv.2⟩, hS]))
    rw [aux_osc_add_const hv.1 (Real.sqrt ε) (hh_cont.mono (Icc_subset_Icc le_rfl hv.2))
      (hgi v hv.1)] at hA
    have e := hY v (Set.mem_Ici.2 hv.1)
    nlinarith [mul_le_mul_of_nonneg_left hA hS.le,
      mul_le_mul_of_nonneg_left (hM v hv) (mul_nonneg hS.le hS.le)]
  have hpart1 : ∀ v ∈ Icc (0 : ℝ) H, Y v - f v ≤ 2 * Real.sqrt ε * h v + ε := fun v hv => by
    nlinarith [hpt v hv, hcase v hv]
  refine ⟨fun v hv => ⟨hYf v hv, hYup v hv, hpart1 v hv⟩, fun hc v hv => ?_⟩
  nlinarith [hpt v hv, mul_le_mul_of_nonneg_left (hc v hv) hS.le, hS2]


/-- `lem:app-phase-square`, part (i) of 3, snapshot `cr-2026-10-23`.
Source: `section.tex` l.1931–1956.
LaTeX (verbatim, `section.tex` l.1931–1956):
```
\begin{lemma}[Square supersolution]\label{lem:app-phase-square}
Let $\epsilon>0$, $T\ge4$ and $H>0$. Let $g\ge0$ be continuous on $[0,\infty)$
with $\int_0^\infty g\le1$, let $f\ge0$ be continuous with $f(0)>T\epsilon$, and let
$Y>0$ be continuous on $[0,\infty)$ with $Y=f+\sqrt\epsilon\,g*\sqrt Y$. Let $h$ be
continuous on $[0,H]$ with $h\ge\sqrt\epsilon$, $h(H)=\sqrt\epsilon$ and
$f\le h^2$. Assume that on $[0,H]$ either
\[
\text{(a)}\ \ g*h\le2h,\qquad\text{or}\qquad\text{(b)}\ \ g*h\le\sqrt\epsilon .
\]
\begin{enumerate}[label=(\roman*)]
\item On $[0,H]$, $f\le Y\le(h+\sqrt\epsilon)^2$ and $Y-f\le2\sqrt\epsilon\,h+\epsilon$;
under (b), moreover $Y-f\le2\epsilon$.
\item The first hit $\hat u\defeq\inf\{u\ge0:\ Y(u)\le T\epsilon\}$ satisfies
$0<\hat u\le H$ and $Y(\hat u)=T\epsilon$, and
\[
0\le\mathcal E\defeq\int_0^{\hat u}\big(\sqrt Y-\sqrt f\big)\,\dif u\le\int_0^H\sqrt{2\sqrt\epsilon\,h+\epsilon}\,\dif u ;
\]
under (b), moreover $\mathcal E\le\sqrt{2\epsilon}\,H$.
\item Let $C>0$, $D\ge1$, $0<r_0<2$ and $0<\epsilon<C^2$, and take
$h(u)=C(1+u/D)^{-r_0}$ and $H=D[(C/\sqrt\epsilon)^{1/r_0}-1]$. Then $h\ge\sqrt\epsilon$
on $[0,H]$, $h(H)=\sqrt\epsilon$, $1+H\le D(C/\sqrt\epsilon)^{1/r_0}$, and
\begin{equation}\label{eqn:app-phase-noise-error}
\int_0^H\sqrt{2\sqrt\epsilon\,h+\epsilon}\,\dif u\le D\,C^{1/r_0}\Big[\frac{\sqrt2}{1-r_0/2}+1\Big]\epsilon^{(r_0-1)/(2r_0)} .
\end{equation}
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_square_i
    {ε T H : ℝ} (hε : 0 < ε) (hT : 4 ≤ T) (hH : 0 < H)
    {f g h Y : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Ici 0)) (hg_nonneg : ∀ u ∈ Ici (0 : ℝ), 0 ≤ g u)
    (hg_int : IntegrableOn g (Ioi 0)) (hg_mass : ∫ u in Ioi (0 : ℝ), g u ≤ 1)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_nonneg : ∀ u ∈ Ici (0 : ℝ), 0 ≤ f u)
    (hf0 : T * ε < f 0)
    (hY_cont : ContinuousOn Y (Ici 0)) (hY_pos : ∀ u ∈ Ici (0 : ℝ), 0 < Y u)
    (hY : ∀ u ∈ Ici (0 : ℝ),
      Y u = f u + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) g u)
    (hh_cont : ContinuousOn h (Icc 0 H)) (hh_ge : ∀ u ∈ Icc (0 : ℝ) H, Real.sqrt ε ≤ h u)
    (hh_H : h H = Real.sqrt ε) (hfh : ∀ u ∈ Icc (0 : ℝ) H, f u ≤ h u ^ 2)
    (hab : (∀ u ∈ Icc (0 : ℝ) H, oneSidedConv h g u ≤ 2 * h u) ∨
      (∀ u ∈ Icc (0 : ℝ) H, oneSidedConv h g u ≤ Real.sqrt ε)) :
    (∀ u ∈ Icc (0 : ℝ) H, f u ≤ Y u ∧ Y u ≤ (h u + Real.sqrt ε) ^ 2 ∧
        Y u - f u ≤ 2 * Real.sqrt ε * h u + ε) ∧
      ((∀ u ∈ Icc (0 : ℝ) H, oneSidedConv h g u ≤ Real.sqrt ε) →
        ∀ u ∈ Icc (0 : ℝ) H, Y u - f u ≤ 2 * ε) := by
  exact aux_square_core hε hH hg_cont hg_nonneg hg_int hg_mass hf_cont hf_nonneg hY_cont
    hY_pos hY hh_cont hh_ge hfh hab

/-- `lem:app-phase-square`, part (ii) of 3, snapshot `cr-2026-10-23`.
Source: `section.tex` l.1931–1956.
LaTeX (verbatim, `section.tex` l.1931–1956):
```
\begin{lemma}[Square supersolution]\label{lem:app-phase-square}
Let $\epsilon>0$, $T\ge4$ and $H>0$. Let $g\ge0$ be continuous on $[0,\infty)$
with $\int_0^\infty g\le1$, let $f\ge0$ be continuous with $f(0)>T\epsilon$, and let
$Y>0$ be continuous on $[0,\infty)$ with $Y=f+\sqrt\epsilon\,g*\sqrt Y$. Let $h$ be
continuous on $[0,H]$ with $h\ge\sqrt\epsilon$, $h(H)=\sqrt\epsilon$ and
$f\le h^2$. Assume that on $[0,H]$ either
\[
\text{(a)}\ \ g*h\le2h,\qquad\text{or}\qquad\text{(b)}\ \ g*h\le\sqrt\epsilon .
\]
\begin{enumerate}[label=(\roman*)]
\item On $[0,H]$, $f\le Y\le(h+\sqrt\epsilon)^2$ and $Y-f\le2\sqrt\epsilon\,h+\epsilon$;
under (b), moreover $Y-f\le2\epsilon$.
\item The first hit $\hat u\defeq\inf\{u\ge0:\ Y(u)\le T\epsilon\}$ satisfies
$0<\hat u\le H$ and $Y(\hat u)=T\epsilon$, and
\[
0\le\mathcal E\defeq\int_0^{\hat u}\big(\sqrt Y-\sqrt f\big)\,\dif u\le\int_0^H\sqrt{2\sqrt\epsilon\,h+\epsilon}\,\dif u ;
\]
under (b), moreover $\mathcal E\le\sqrt{2\epsilon}\,H$.
\item Let $C>0$, $D\ge1$, $0<r_0<2$ and $0<\epsilon<C^2$, and take
$h(u)=C(1+u/D)^{-r_0}$ and $H=D[(C/\sqrt\epsilon)^{1/r_0}-1]$. Then $h\ge\sqrt\epsilon$
on $[0,H]$, $h(H)=\sqrt\epsilon$, $1+H\le D(C/\sqrt\epsilon)^{1/r_0}$, and
\begin{equation}\label{eqn:app-phase-noise-error}
\int_0^H\sqrt{2\sqrt\epsilon\,h+\epsilon}\,\dif u\le D\,C^{1/r_0}\Big[\frac{\sqrt2}{1-r_0/2}+1\Big]\epsilon^{(r_0-1)/(2r_0)} .
\end{equation}
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_square_ii
    {ε T H : ℝ} (hε : 0 < ε) (hT : 4 ≤ T) (hH : 0 < H)
    {f g h Y : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Ici 0)) (hg_nonneg : ∀ u ∈ Ici (0 : ℝ), 0 ≤ g u)
    (hg_int : IntegrableOn g (Ioi 0)) (hg_mass : ∫ u in Ioi (0 : ℝ), g u ≤ 1)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_nonneg : ∀ u ∈ Ici (0 : ℝ), 0 ≤ f u)
    (hf0 : T * ε < f 0)
    (hY_cont : ContinuousOn Y (Ici 0)) (hY_pos : ∀ u ∈ Ici (0 : ℝ), 0 < Y u)
    (hY : ∀ u ∈ Ici (0 : ℝ),
      Y u = f u + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) g u)
    (hh_cont : ContinuousOn h (Icc 0 H)) (hh_ge : ∀ u ∈ Icc (0 : ℝ) H, Real.sqrt ε ≤ h u)
    (hh_H : h H = Real.sqrt ε) (hfh : ∀ u ∈ Icc (0 : ℝ) H, f u ≤ h u ^ 2)
    (hab : (∀ u ∈ Icc (0 : ℝ) H, oneSidedConv h g u ≤ 2 * h u) ∨
      (∀ u ∈ Icc (0 : ℝ) H, oneSidedConv h g u ≤ Real.sqrt ε)) :
    ∃ û : ℝ, firstHit Y (T * ε) = ENNReal.ofReal û ∧ 0 < û ∧ û ≤ H ∧ Y û = T * ε ∧
      0 ≤ ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (f u)) ∧
      ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (f u)) ≤
        ∫ u in (0 : ℝ)..H, Real.sqrt (2 * Real.sqrt ε * h u + ε) ∧
      ((∀ u ∈ Icc (0 : ℝ) H, oneSidedConv h g u ≤ Real.sqrt ε) →
        ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (f u)) ≤ Real.sqrt (2 * ε) * H) := by
  obtain ⟨hcore, hcoreb⟩ := aux_square_core hε hH hg_cont hg_nonneg hg_int hg_mass hf_cont
    hf_nonneg hY_cont hY_pos hY hh_cont hh_ge hfh hab
  have hYH : ContinuousOn Y (Icc 0 H) := hY_cont.mono Icc_subset_Ici_self
  have hfH : ContinuousOn f (Icc 0 H) := hf_cont.mono Icc_subset_Ici_self
  obtain ⟨K, hK⟩ : ∃ K : Set ℝ, K = Icc (0 : ℝ) H ∩ Y ⁻¹' Iic (T * ε) := ⟨_, rfl⟩
  have hmemK : ∀ u, u ∈ K ↔ (0 ≤ u ∧ u ≤ H) ∧ Y u ≤ T * ε := by
    intro u
    rw [hK]
    exact Iff.rfl
  have hKc : IsClosed K := by
    rw [hK]
    exact ContinuousOn.preimage_isClosed_of_isClosed hYH isClosed_Icc isClosed_Iic
  have hYH_le : Y H ≤ T * ε := by
    have h1 := (hcore H ⟨hH.le, le_rfl⟩).2.1
    rw [hh_H] at h1
    nlinarith [mul_nonneg (sub_nonneg.2 hT) hε.le, Real.sq_sqrt hε.le]
  have hKne : K.Nonempty := ⟨H, (hmemK H).2 ⟨⟨hH.le, le_rfl⟩, hYH_le⟩⟩
  have hBdd : BddBelow K := ⟨0, fun u hu => ((hmemK u).1 hu).1.1⟩
  obtain ⟨û, hûdef⟩ : ∃ û : ℝ, û = sInf K := ⟨_, rfl⟩
  have hûK : û ∈ K := by
    rw [hûdef]
    exact hKc.csInf_mem hKne hBdd
  obtain ⟨⟨hû0, hûH⟩, hYû_le⟩ := (hmemK û).1 hûK
  have hf0' : T * ε < Y 0 := lt_of_lt_of_le hf0 (hcore 0 ⟨le_rfl, hH.le⟩).1
  have hûpos : 0 < û := by
    refine lt_of_le_of_ne hû0 (fun h0 => ?_)
    rw [← h0] at hYû_le
    linarith
  have hYû : Y û = T * ε := by
    obtain ⟨c, hc, hYc⟩ := intermediate_value_Icc' hû0 (hYH.mono (Icc_subset_Icc le_rfl hûH))
      (show T * ε ∈ Icc (Y û) (Y 0) from ⟨hYû_le, hf0'.le⟩)
    have hcK : c ∈ K := (hmemK c).2 ⟨⟨hc.1, hc.2.trans hûH⟩, hYc.le⟩
    have hle : û ≤ c := by
      rw [hûdef]
      exact csInf_le hBdd hcK
    have hcû : c = û := le_antisymm hc.2 hle
    rw [← hcû]
    exact hYc
  have hfirst : firstHit Y (T * ε) = ENNReal.ofReal û := by
    unfold firstHit
    apply le_antisymm
    · have hc : Y ((Real.toNNReal û : NNReal) : ℝ) ≤ T * ε := by
        rw [Real.coe_toNNReal _ hû0]
        exact hYû.le
      exact iInf₂_le (Real.toNNReal û) hc
    · refine le_iInf₂ fun t ht => ?_
      have hle : û ≤ (t : ℝ) := by
        rcases le_total (t : ℝ) H with htH | htH
        · rw [hûdef]
          exact csInf_le hBdd ((hmemK _).2 ⟨⟨NNReal.coe_nonneg t, htH⟩, ht⟩)
        · linarith
      exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hle)
  have hcontF : ContinuousOn (fun u => Real.sqrt (Y u) - Real.sqrt (f u)) (Icc 0 H) :=
    (hYH.sqrt).sub (hfH.sqrt)
  have hFint : IntervalIntegrable (fun u => Real.sqrt (Y u) - Real.sqrt (f u)) volume 0 û :=
    (hcontF.mono (Icc_subset_Icc le_rfl hûH)).intervalIntegrable_of_Icc hû0
  have hG'cont : ContinuousOn (fun u => Real.sqrt (2 * Real.sqrt ε * h u + ε)) (Icc 0 H) :=
    ((continuousOn_const.mul hh_cont).add continuousOn_const).sqrt
  have hG'û : IntervalIntegrable (fun u => Real.sqrt (2 * Real.sqrt ε * h u + ε)) volume 0 û :=
    (hG'cont.mono (Icc_subset_Icc le_rfl hûH)).intervalIntegrable_of_Icc hû0
  have hG'ûH : IntervalIntegrable (fun u => Real.sqrt (2 * Real.sqrt ε * h u + ε)) volume û H :=
    (hG'cont.mono (Icc_subset_Icc hû0 le_rfl)).intervalIntegrable_of_Icc hûH
  have hFle : ∀ u ∈ Icc (0 : ℝ) û,
      Real.sqrt (Y u) - Real.sqrt (f u) ≤ Real.sqrt (2 * Real.sqrt ε * h u + ε) := fun u hu =>
    (Muon.Foundations.sqrt_sub_sqrt_le (hf_nonneg u (Set.mem_Ici.2 hu.1))
      (hcore u ⟨hu.1, hu.2.trans hûH⟩).1).trans
      (Real.sqrt_le_sqrt (hcore u ⟨hu.1, hu.2.trans hûH⟩).2.2)
  have hEle : ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (f u)) ≤
      ∫ u in (0 : ℝ)..û, Real.sqrt (2 * Real.sqrt ε * h u + ε) :=
    intervalIntegral.integral_mono_on hû0 hFint hG'û hFle
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hG'û hG'ûH
  have htail : 0 ≤ ∫ u in û..H, Real.sqrt (2 * Real.sqrt ε * h u + ε) :=
    intervalIntegral.integral_nonneg hûH fun u _ => Real.sqrt_nonneg _
  have hEnn : 0 ≤ ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (f u)) :=
    intervalIntegral.integral_nonneg hû0 fun u hu =>
      sub_nonneg.2 (Real.sqrt_le_sqrt (hcore u ⟨hu.1, hu.2.trans hûH⟩).1)
  refine ⟨û, hfirst, hûpos, hûH, hYû, hEnn, by linarith, ?_⟩
  intro hcb
  have hcb2 := hcoreb hcb
  have hconst : ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (f u))
      ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (2 * ε) :=
    intervalIntegral.integral_mono_on hû0 hFint intervalIntegrable_const fun u hu =>
      (Muon.Foundations.sqrt_sub_sqrt_le (hf_nonneg u (Set.mem_Ici.2 hu.1))
        (hcore u ⟨hu.1, hu.2.trans hûH⟩).1).trans
        (Real.sqrt_le_sqrt (hcb2 u ⟨hu.1, hu.2.trans hûH⟩))
  rw [intervalIntegral.integral_const, smul_eq_mul] at hconst
  nlinarith [mul_le_mul_of_nonneg_right hûH (Real.sqrt_nonneg (2 * ε))]

lemma aux_sq_rpow_cont {D a H : ℝ} (hD : 0 < D) (hH : 0 ≤ H) :
    ContinuousOn (fun u : ℝ => (1 + u / D) ^ (-a)) (uIcc 0 H) := by
  have hc : ContinuousOn (fun u : ℝ => 1 + u / D) (uIcc 0 H) := by fun_prop
  refine hc.rpow_const fun x hx => Or.inl (ne_of_gt ?_)
  rw [uIcc_of_le hH] at hx
  exact add_pos_of_pos_of_nonneg one_pos (div_nonneg hx.1 hD.le)

lemma aux_rpow_integral_le {D a H : ℝ} (hD : 0 < D) (ha : a < 1) (hH : 0 ≤ H) :
    ∫ u in (0:ℝ)..H, (1 + u / D) ^ (-a) ≤ D / (1 - a) * (1 + H / D) ^ (1 - a) := by
  have hpos : (0:ℝ) < 1 - a := by linarith
  have hne : (1 - a) ≠ 0 := hpos.ne'
  have hDne : D ≠ 0 := hD.ne'
  have hderiv : ∀ x ∈ uIcc (0:ℝ) H,
      HasDerivAt (fun u : ℝ => D / (1 - a) * (1 + u / D) ^ (1 - a)) ((1 + x / D) ^ (-a)) x := by
    intro x hx
    rw [uIcc_of_le hH] at hx
    have hb : 0 < 1 + x / D := add_pos_of_pos_of_nonneg one_pos (div_nonneg hx.1 hD.le)
    have h1 : HasDerivAt (fun u : ℝ => 1 + u / D) (1 / D) x :=
      ((hasDerivAt_id x).div_const D).const_add 1
    have h2 := (h1.rpow_const (p := 1 - a) (Or.inl (ne_of_gt hb))).const_mul (D / (1 - a))
    convert h2 using 1
    have e : 1 - a - 1 = -a := by ring
    rw [e]
    field_simp
  have hint : IntervalIntegrable (fun u : ℝ => (1 + u / D) ^ (-a)) volume 0 H :=
    (aux_sq_rpow_cont hD hH).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  show D / (1 - a) * (1 + H / D) ^ (1 - a) - D / (1 - a) * (1 + 0 / D) ^ (1 - a) ≤ _
  simp only [zero_div, add_zero, Real.one_rpow, mul_one]
  have : 0 ≤ D / (1 - a) := div_nonneg hD.le hpos.le
  linarith

/-- `lem:app-phase-square`, part (iii) of 3, snapshot `cr-2026-10-23`.
Source: `section.tex` l.1931–1956.
LaTeX (verbatim, `section.tex` l.1931–1956):
```
\begin{lemma}[Square supersolution]\label{lem:app-phase-square}
Let $\epsilon>0$, $T\ge4$ and $H>0$. Let $g\ge0$ be continuous on $[0,\infty)$
with $\int_0^\infty g\le1$, let $f\ge0$ be continuous with $f(0)>T\epsilon$, and let
$Y>0$ be continuous on $[0,\infty)$ with $Y=f+\sqrt\epsilon\,g*\sqrt Y$. Let $h$ be
continuous on $[0,H]$ with $h\ge\sqrt\epsilon$, $h(H)=\sqrt\epsilon$ and
$f\le h^2$. Assume that on $[0,H]$ either
\[
\text{(a)}\ \ g*h\le2h,\qquad\text{or}\qquad\text{(b)}\ \ g*h\le\sqrt\epsilon .
\]
\begin{enumerate}[label=(\roman*)]
\item On $[0,H]$, $f\le Y\le(h+\sqrt\epsilon)^2$ and $Y-f\le2\sqrt\epsilon\,h+\epsilon$;
under (b), moreover $Y-f\le2\epsilon$.
\item The first hit $\hat u\defeq\inf\{u\ge0:\ Y(u)\le T\epsilon\}$ satisfies
$0<\hat u\le H$ and $Y(\hat u)=T\epsilon$, and
\[
0\le\mathcal E\defeq\int_0^{\hat u}\big(\sqrt Y-\sqrt f\big)\,\dif u\le\int_0^H\sqrt{2\sqrt\epsilon\,h+\epsilon}\,\dif u ;
\]
under (b), moreover $\mathcal E\le\sqrt{2\epsilon}\,H$.
\item Let $C>0$, $D\ge1$, $0<r_0<2$ and $0<\epsilon<C^2$, and take
$h(u)=C(1+u/D)^{-r_0}$ and $H=D[(C/\sqrt\epsilon)^{1/r_0}-1]$. Then $h\ge\sqrt\epsilon$
on $[0,H]$, $h(H)=\sqrt\epsilon$, $1+H\le D(C/\sqrt\epsilon)^{1/r_0}$, and
\begin{equation}\label{eqn:app-phase-noise-error}
\int_0^H\sqrt{2\sqrt\epsilon\,h+\epsilon}\,\dif u\le D\,C^{1/r_0}\Big[\frac{\sqrt2}{1-r_0/2}+1\Big]\epsilon^{(r_0-1)/(2r_0)} .
\end{equation}
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_square_iii
    {C D r0 ε H : ℝ} {h : ℝ → ℝ} (hC : 0 < C) (hD : 1 ≤ D) (hr0 : 0 < r0) (hr2 : r0 < 2)
    (hε : 0 < ε) (hεC : ε < C ^ 2)
    (hh : ∀ u, h u = C * (1 + u / D) ^ (-r0))
    (hH : H = D * ((C / Real.sqrt ε) ^ (1 / r0) - 1)) :
    (∀ u ∈ Icc (0 : ℝ) H, Real.sqrt ε ≤ h u) ∧ h H = Real.sqrt ε ∧
      1 + H ≤ D * (C / Real.sqrt ε) ^ (1 / r0) ∧
      ∫ u in (0 : ℝ)..H, Real.sqrt (2 * Real.sqrt ε * h u + ε) ≤
        D * C ^ (1 / r0) * (Real.sqrt 2 / (1 - r0 / 2) + 1) * ε ^ ((r0 - 1) / (2 * r0)) := by
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt ε := ⟨_, rfl⟩
  rw [← hs_def] at hH ⊢
  have hs : 0 < s := hs_def ▸ Real.sqrt_pos.2 hε
  have hs2 : s ^ 2 = ε := hs_def ▸ Real.sq_sqrt hε.le
  have hsC : s < C := by nlinarith
  have hD0 : 0 < D := by linarith
  have hCs : 0 < C / s := div_pos hC hs
  have hX1 : 1 ≤ (C / s) ^ (1 / r0) :=
    Real.one_le_rpow ((one_le_div hs).2 hsC.le) (by positivity)
  have hHnn : 0 ≤ H := by rw [hH]; exact mul_nonneg hD0.le (by linarith)
  have hHD : H / D = (C / s) ^ (1 / r0) - 1 := by rw [hH]; field_simp
  have hXH : 1 + H / D = (C / s) ^ (1 / r0) := by rw [hHD]; ring
  have hXdiv : (C / s) ^ (1 / r0) = C ^ (1 / r0) / s ^ (1 / r0) :=
    Real.div_rpow hC.le hs.le _
  have hpow : ((C / s) ^ (1 / r0)) ^ (-r0) = s / C := by
    rw [← Real.rpow_mul hCs.le]
    have e : 1 / r0 * -r0 = -1 := by field_simp
    rw [e, Real.rpow_neg_one]
    field_simp
  have hhH : h H = s := by rw [hh, hXH, hpow]; field_simp
  -- part (i)
  have hpart1 : ∀ u ∈ Icc (0 : ℝ) H, s ≤ h u := by
    intro u hu
    rw [hh]
    have hb : 0 < 1 + u / D := add_pos_of_pos_of_nonneg one_pos (div_nonneg hu.1 hD0.le)
    have hle : 1 + u / D ≤ (C / s) ^ (1 / r0) := by
      rw [← hXH]
      have : u / D ≤ H / D := div_le_div_of_nonneg_right hu.2 hD0.le
      linarith
    have hmono := Real.rpow_le_rpow_of_nonpos hb hle (show -r0 ≤ 0 by linarith)
    rw [hpow] at hmono
    calc s = C * (s / C) := by field_simp
      _ ≤ C * (1 + u / D) ^ (-r0) := mul_le_mul_of_nonneg_left hmono hC.le
  refine ⟨hpart1, hhH, ?_, ?_⟩
  · have : H = D * ((C / s) ^ (1 / r0) - 1) := hH
    nlinarith
  -- part (iii) integral bound
  obtain ⟨k, hk_def⟩ : ∃ k, k = Real.sqrt (2 * s * C) := ⟨_, rfl⟩
  have hk0 : 0 ≤ k := hk_def ▸ Real.sqrt_nonneg _
  have hk2 : k ^ 2 = 2 * s * C :=
    hk_def ▸ Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) hs.le) hC.le)
  have hk_rpow : k = Real.sqrt 2 * C ^ (1 / (2:ℝ)) * s ^ (1 / (2:ℝ)) := by
    rw [hk_def, Real.sqrt_mul (mul_nonneg (by norm_num) hs.le) C,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) s, Real.sqrt_eq_rpow C, Real.sqrt_eq_rpow s]
    ring
  have hE : s ^ (1 - 1 / r0) = s / s ^ (1 / r0) := by
    rw [Real.rpow_sub hs, Real.rpow_one]
  have hεE : ε ^ ((r0 - 1) / (2 * r0)) = s ^ (1 - 1 / r0) := by
    rw [← hs2, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    congr 1
    push_cast
    field_simp
  have hXa : ((C / s) ^ (1 / r0)) ^ (1 - r0 / 2) = C ^ (1 / r0 - 1 / 2) / s ^ (1 / r0 - 1 / 2) := by
    have hexp : 1 / r0 * (1 - r0 / 2) = 1 / r0 - 1 / 2 := by
      have hr0ne : r0 ≠ 0 := hr0.ne'
      field_simp
    rw [← Real.rpow_mul hCs.le, hexp, Real.div_rpow hC.le hs.le]
  have hCC : C ^ (1 / (2:ℝ)) * C ^ (1 / r0 - 1 / 2) = C ^ (1 / r0) := by
    rw [← Real.rpow_add hC]; congr 1; ring
  have hss : s ^ (1 / (2:ℝ)) / s ^ (1 / r0 - 1 / 2) = s / s ^ (1 / r0) := by
    rw [← Real.rpow_sub hs, ← hE]; congr 1; ring
  have hT1 : k * (D / (1 - r0 / 2) * (1 + H / D) ^ (1 - r0 / 2))
      = Real.sqrt 2 * D / (1 - r0 / 2) * (C ^ (1 / r0) * s ^ (1 - 1 / r0)) := by
    rw [hXH, hXa, hk_rpow, hE]
    have hfinal : Real.sqrt 2 * C ^ (1 / (2:ℝ)) * s ^ (1 / (2:ℝ)) *
        (D / (1 - r0 / 2) * (C ^ (1 / r0 - 1 / 2) / s ^ (1 / r0 - 1 / 2)))
        = (Real.sqrt 2 * (D / (1 - r0 / 2))) *
          ((C ^ (1 / (2:ℝ)) * C ^ (1 / r0 - 1 / 2)) *
            (s ^ (1 / (2:ℝ)) / s ^ (1 / r0 - 1 / 2))) := by ring
    rw [hfinal, hCC, hss]
    ring
  have hB : s * H ≤ D * C ^ (1 / r0) * s ^ (1 - 1 / r0) := by
    have hHX : H ≤ D * (C / s) ^ (1 / r0) := by rw [hH]; nlinarith
    calc s * H ≤ s * (D * (C / s) ^ (1 / r0)) := mul_le_mul_of_nonneg_left hHX hs.le
      _ = D * C ^ (1 / r0) * s ^ (1 - 1 / r0) := by rw [hXdiv, hE]; ring
  have hFTC := aux_rpow_integral_le (a := r0 / 2) hD0 (by linarith) hHnn
  have hmulF := mul_le_mul_of_nonneg_left hFTC hk0
  have hpt : ∀ u ∈ uIcc (0 : ℝ) H,
      Real.sqrt (2 * s * h u + ε) ≤ k * (1 + u / D) ^ (-(r0 / 2)) + s := by
    intro u hu
    rw [uIcc_of_le hHnn] at hu
    have hb : 0 < 1 + u / D := add_pos_of_pos_of_nonneg one_pos (div_nonneg hu.1 hD0.le)
    have hp0 : 0 ≤ (1 + u / D) ^ (-(r0 / 2)) := Real.rpow_nonneg hb.le _
    have hp2 : ((1 + u / D) ^ (-(r0 / 2))) ^ 2 = (1 + u / D) ^ (-r0) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
      congr 1
      push_cast
      ring
    rw [hh, ← hp2, Real.sqrt_le_iff]
    refine ⟨add_nonneg (mul_nonneg hk0 hp0) hs.le, ?_⟩
    have hkP : k ^ 2 * ((1 + u / D) ^ (-(r0 / 2))) ^ 2 = 2 * s * C * ((1 + u / D) ^ (-(r0 / 2))) ^ 2 := by
      rw [hk2]
    nlinarith [hkP, mul_nonneg (mul_nonneg hk0 hp0) hs.le, hs2]
  have hcontp : ContinuousOn (fun u : ℝ => (1 + u / D) ^ (-(r0 / 2))) (uIcc 0 H) :=
    aux_sq_rpow_cont hD0 hHnn
  have hcontr : ContinuousOn (fun u : ℝ => (1 + u / D) ^ (-r0)) (uIcc 0 H) :=
    aux_sq_rpow_cont hD0 hHnn
  have hhc : ContinuousOn h (uIcc 0 H) := by
    have hfun : h = fun u => C * (1 + u / D) ^ (-r0) := funext hh
    rw [hfun]
    exact continuousOn_const.mul hcontr
  have hcontL : ContinuousOn (fun u => Real.sqrt (2 * s * h u + ε)) (uIcc 0 H) :=
    ((continuousOn_const.mul hhc).add continuousOn_const).sqrt
  have hintL : IntervalIntegrable (fun u => Real.sqrt (2 * s * h u + ε)) volume 0 H :=
    hcontL.intervalIntegrable
  have hintR : IntervalIntegrable (fun u => k * (1 + u / D) ^ (-(r0 / 2)) + s) volume 0 H :=
    ((continuousOn_const.mul hcontp).add continuousOn_const).intervalIntegrable
  have hmain := intervalIntegral.integral_mono_on hHnn hintL hintR
    (fun u hu => hpt u (by rw [uIcc_of_le hHnn]; exact hu))
  have hsplit : ∫ u in (0:ℝ)..H, (k * (1 + u / D) ^ (-(r0 / 2)) + s)
      = k * (∫ u in (0:ℝ)..H, (1 + u / D) ^ (-(r0 / 2))) + s * H := by
    have h1 : IntervalIntegrable (fun u : ℝ => k * (1 + u / D) ^ (-(r0 / 2))) volume 0 H :=
      (continuousOn_const.mul hcontp).intervalIntegrable
    have h2 : IntervalIntegrable (fun _ : ℝ => s) volume 0 H := intervalIntegrable_const
    rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      smul_eq_mul, sub_zero]
    ring
  rw [hεE]
  have hgoal : D * C ^ (1 / r0) * (Real.sqrt 2 / (1 - r0 / 2) + 1) * s ^ (1 - 1 / r0)
      = Real.sqrt 2 * D / (1 - r0 / 2) * (C ^ (1 / r0) * s ^ (1 - 1 / r0))
        + D * C ^ (1 / r0) * s ^ (1 - 1 / r0) := by ring
  rw [hgoal]
  linarith [hmain, hsplit, hmulF, hT1, hB]

/-! ## The clock integral -/

lemma fl_eq_sum (N : ℕ) (a q u : ℝ) :
    Lsum (N : ℕ∞) a q u
      = ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) := by
  unfold Lsum
  rw [tsum_eq_sum (s := Finset.Icc 1 N)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [if_pos ⟨by omega, by exact_mod_cast hi.2⟩]
  · intro i hi
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hi
    rw [Finset.mem_Icc]
    exact ⟨h1, by exact_mod_cast h2⟩

lemma fl_cont (N : ℕ) (p q : ℝ) : Continuous (fun u => fNq (N : ℕ∞) p q u) := by
  have h : (fun u => fNq (N : ℕ∞) p q u)
      = fun u => (1 / 2) * ∑ i ∈ Finset.Icc 1 N,
          (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) := by
    funext u
    unfold fNq
    rw [fl_eq_sum]
  rw [h]
  fun_prop

lemma ck_term_summable {p q u : ℝ} (hp : 1 < p) (hu : 0 ≤ u) :
    Summable (fun i : ℕ =>
      if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) := by
  have hs : Summable (fun i : ℕ => if 0 < i then (i : ℝ) ^ (-p) else 0) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
      (Real.summable_nat_rpow.mpr (by linarith : -p < -1))
    · split_ifs
      · exact Real.rpow_nonneg (Nat.cast_nonneg i) _
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (Nat.cast_nonneg i) _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hs
  · split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le
    · exact le_rfl
  · split_ifs
    · have hx : -(2 * u) * (i : ℝ) ^ (-q) ≤ 0 := by
        nlinarith [mul_nonneg hu (Real.rpow_nonneg (Nat.cast_nonneg i) (-q))]
      exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg i) _)
        (Real.exp_le_one_iff.mpr hx)
    · exact le_rfl

lemma ck_inf_eq (p q u : ℝ) :
    fNq ⊤ p q u = (1 / 2) * ∑' i : ℕ,
      (if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) := by
  unfold fNq Lsum
  congr 1
  apply tsum_congr
  intro i
  simp

lemma ck_diff {p q : ℝ} (hp : 1 < p) (N : ℕ) (hN : 1 ≤ N) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ fNq ⊤ p q u - fNq (N : ℕ∞) p q u ∧
    fNq ⊤ p q u - fNq (N : ℕ∞) p q u ≤ (N : ℝ) ^ (1 - p) / (2 * (p - 1)) := by
  have hsum := ck_term_summable (q := q) hp hu
  have hfin : Summable (fun i : ℕ =>
      if 0 < i ∧ ((i : ℕ∞) ≤ (N : ℕ∞)) then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hsum
    · split_ifs
      · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le
      · exact le_rfl
    · by_cases h : 0 < i
      · simp only [h, true_and, ite_true]
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le
      · simp [h]
  set tl : ℕ → ℝ := fun i =>
    if N < i then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0 with htl
  have htlnn : ∀ i, 0 ≤ tl i := by
    intro i; rw [htl]; dsimp only; split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le
    · exact le_rfl
  have hpt : ∀ i : ℕ, (if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0)
      = (if 0 < i ∧ ((i : ℕ∞) ≤ (N : ℕ∞)) then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0)
        + tl i := by
    intro i
    rw [htl]; dsimp only
    by_cases h0 : 0 < i
    · by_cases hN' : i ≤ N
      · have : ¬ N < i := by omega
        simp [h0, hN', this]
      · have : N < i := by omega
        have h2 : ¬ ((i : ℕ∞) ≤ (N : ℕ∞)) := by exact_mod_cast hN'
        simp [h0, h2, this]
    · have : ¬ N < i := by omega
      simp [h0, this]
  have hsumtl : Summable tl := by
    have := hsum.sub hfin
    refine this.congr (fun i => ?_)
    rw [hpt i]; ring
  have hdiff : fNq ⊤ p q u - fNq (N : ℕ∞) p q u = (1 / 2) * ∑' i, tl i := by
    rw [ck_inf_eq]
    unfold fNq Lsum
    have : (∑' i : ℕ, (if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0))
        = (∑' i : ℕ, (if 0 < i ∧ ((i : ℕ∞) ≤ (N : ℕ∞)) then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0))
          + ∑' i, tl i := by
      rw [← hfin.tsum_add hsumtl]
      exact tsum_congr hpt
    rw [this]; ring
  rw [hdiff]
  obtain ⟨_, htail⟩ := lem_app_phase_laplace_ii hp N hN
  have hle : ∑' i, tl i ≤ tailSum p N := by
    unfold tailSum
    refine hsumtl.tsum_le_tsum (fun i => ?_) ?_
    · rw [htl]; dsimp only; split_ifs
      · have hx : -(2 * u) * (i : ℝ) ^ (-q) ≤ 0 := by
          nlinarith [mul_nonneg hu (Real.rpow_nonneg (Nat.cast_nonneg i) (-q))]
        exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg i) _)
          (Real.exp_le_one_iff.mpr hx)
      · exact le_rfl
    · refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
        (Real.summable_nat_rpow.mpr (by linarith : -p < -1) : Summable (fun i : ℕ => (i : ℝ) ^ (-p)))
      · split_ifs
        · exact Real.rpow_nonneg (Nat.cast_nonneg i) _
        · exact le_rfl
      · split_ifs
        · exact le_rfl
        · exact Real.rpow_nonneg (Nat.cast_nonneg i) _
  have hp1 : 0 < p - 1 := by linarith
  have htn : 0 ≤ ∑' i, tl i := tsum_nonneg htlnn
  refine ⟨by linarith, ?_⟩
  calc (1 / 2) * ∑' i, tl i ≤ (1 / 2) * ((N : ℝ) ^ (1 - p) / (p - 1)) := by
        apply mul_le_mul_of_nonneg_left (le_trans hle htail) (by norm_num)
    _ = (N : ℝ) ^ (1 - p) / (2 * (p - 1)) := by field_simp


lemma ck_anti {p q : ℝ} (hp : 1 < p) :
    AntitoneOn (fun u => fNq ⊤ p q u) (Ici 0) := by
  intro u hu v hv huv
  simp only
  rw [ck_inf_eq, ck_inf_eq]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine (ck_term_summable (q := q) hp hv).tsum_le_tsum (fun i => ?_) (ck_term_summable (q := q) hp hu)
  split_ifs
  · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg i) _)
    apply Real.exp_le_exp.mpr
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg i : (0:ℝ) ≤ i) (-q)]
  · exact le_rfl

lemma ck_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

lemma ck_sqrt_diff {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : rq p q = 1)
    (N : ℕ) (hN : 1 ≤ N) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u) ∧
    Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u)
      ≤ (N : ℝ) ^ (-q) / Real.sqrt (2 * (p - 1)) := by
  obtain ⟨h1, h2⟩ := ck_diff (q := q) hp N hN hu
  have hpq : p - 1 = 2 * q := by unfold rq at hr; field_simp at hr; linarith
  refine ⟨by linarith [Real.sqrt_le_sqrt (by linarith : fNq (N : ℕ∞) p q u ≤ fNq ⊤ p q u)], ?_⟩
  have hf0 : 0 ≤ fNq (N : ℕ∞) p q u := by
    unfold fNq Lsum
    apply mul_nonneg (by norm_num)
    apply tsum_nonneg
    intro i; split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le
    · exact le_rfl
  have h3 : Real.sqrt (fNq ⊤ p q u)
      ≤ Real.sqrt (fNq ⊤ p q u - fNq (N : ℕ∞) p q u) + Real.sqrt (fNq (N : ℕ∞) p q u) := by
    have := ck_sqrt_add_le h1 hf0
    rwa [sub_add_cancel] at this
  have hp1 : 0 < p - 1 := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h4 : Real.sqrt (fNq ⊤ p q u - fNq (N : ℕ∞) p q u) ≤ (N : ℝ) ^ (-q) / Real.sqrt (2 * (p - 1)) := by
    calc Real.sqrt (fNq ⊤ p q u - fNq (N : ℕ∞) p q u)
        ≤ Real.sqrt ((N : ℝ) ^ (1 - p) / (2 * (p - 1))) := Real.sqrt_le_sqrt h2
      _ = (N : ℝ) ^ (-q) / Real.sqrt (2 * (p - 1)) := by
          rw [Real.sqrt_div (Real.rpow_nonneg hNpos.le _)]
          congr 1
          have : (N : ℝ) ^ (1 - p) = ((N : ℝ) ^ (-q)) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
            congr 1; push_cast; linarith
          rw [this, Real.sqrt_sq (Real.rpow_nonneg hNpos.le _)]
  linarith

lemma ck_aQ_pos {q : ℝ} (hq : 0 < q) : 0 < aQ q := by
  unfold aQ; exact Real.rpow_pos_of_pos (by linarith) _

lemma ck_aQ_sq {q : ℝ} (hq : 0 < q) : aQ q ^ 2 = 1 / (8 * q) := by
  unfold aQ
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  norm_num
  rw [Real.rpow_neg_one]; simp

lemma ck_asym {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : rq p q = 1) {u : ℝ} (hu : 0 < u) :
    |fNq ⊤ p q u - aQ q ^ 2 / u ^ 2| ≤ Mpq p q * (2 * u) ^ (-(p / q)) := by
  have hpq : p - 1 = 2 * q := by unfold rq at hr; field_simp at hr; linarith
  have h := lem_app_phase_laplace_i (p := p) (q := q) (a := 2 * u) hp hq (by linarith)
  have hd : (p - 1) / q = 2 := by rw [hpq]; field_simp
  rw [hd, Real.Gamma_two] at h
  have h2 : (2 * u) ^ (-(2 : ℝ)) = 1 / (4 * u ^ 2) := by
    rw [Real.rpow_neg (by linarith), show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    field_simp; ring
  rw [h2] at h
  have hsum : fNq ⊤ p q u = (1 / 2) * ∑' i : ℕ,
      (if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) := ck_inf_eq p q u
  have hc : aQ q ^ 2 / u ^ 2 = (1 / 2) * (1 / q * (1 / (4 * u ^ 2))) := by
    rw [ck_aQ_sq hq]; field_simp; ring
  rw [hsum, hc, ← mul_sub, abs_mul]
  have : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_pos (by norm_num)
  rw [this]
  have hM : 0 ≤ Mpq p q * (2 * u) ^ (-(p / q)) := by
    apply mul_nonneg
    · unfold Mpq; apply Real.rpow_nonneg; apply div_nonneg (by linarith)
      exact mul_nonneg (Real.exp_pos 1).le hq.le
    · exact Real.rpow_nonneg (by linarith) _
  nlinarith [h]


lemma ck_sqrt_le {p q : ℝ} (hp : 1 < p) (hq : 0 < q) {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt (fNq ⊤ p q u) ≤ Cpq p q := by
  have h := lem_app_phase_sums_i hp hq ⊤ hu
  have hd : 0 < dAQ p q := div_pos (by linarith) hq
  have h1 : (1 + u) ^ (-dAQ p q) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hE : 0 ≤ Epq p q := by
    unfold Epq
    refine le_trans ?_ (le_max_left _ _)
    unfold Za
    have : 0 < 1 / (p - 1) := div_pos one_pos (by linarith)
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
  have h2 : fNq ⊤ p q u ≤ Epq p q / 2 := by
    unfold fNq
    have : Lsum ⊤ p q u ≤ Epq p q := by
      calc Lsum ⊤ p q u ≤ Epq p q * (1 + u) ^ (-dAQ p q) := h
        _ ≤ Epq p q * 1 := mul_le_mul_of_nonneg_left h1 hE
        _ = Epq p q := mul_one _
    linarith
  exact Real.sqrt_le_sqrt h2

lemma ck_sqrt_asym {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : rq p q = 1) {u : ℝ} (hu : 1 ≤ u) :
    |Real.sqrt (fNq ⊤ p q u) - aQ q / u|
      ≤ (Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q) * u ^ (-1 - 1 / q) := by
  have hpq : p - 1 = 2 * q := by unfold rq at hr; field_simp at hr; linarith
  have hu0 : 0 < u := by linarith
  have haQ := ck_aQ_pos hq
  have hasy := ck_asym hp hq hr hu0
  set s := Real.sqrt (fNq ⊤ p q u) with hs
  have hf0 : 0 ≤ fNq ⊤ p q u := by
    rw [ck_inf_eq]
    apply mul_nonneg (by norm_num)
    apply tsum_nonneg
    intro i; split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le
    · exact le_rfl
  have hs2 : s ^ 2 = fNq ⊤ p q u := Real.sq_sqrt hf0
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set b := aQ q / u with hb
  have hbpos : 0 < b := div_pos haQ hu0
  have hb2 : b ^ 2 = aQ q ^ 2 / u ^ 2 := by rw [hb]; field_simp
  have h1 : |s - b| * b ≤ Mpq p q * (2 * u) ^ (-(p / q)) := by
    have : |s ^ 2 - b ^ 2| = |s - b| * (s + b) := by
      rw [show s ^ 2 - b ^ 2 = (s - b) * (s + b) by ring, abs_mul, abs_of_nonneg (by linarith : 0 ≤ s + b)]
    rw [hs2, hb2] at this
    calc |s - b| * b ≤ |s - b| * (s + b) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = |fNq ⊤ p q u - aQ q ^ 2 / u ^ 2| := this.symm
      _ ≤ _ := hasy
  have h2 : (2 * u) ^ (-(p / q)) = (2 : ℝ) ^ (-(p / q)) * u ^ (-(p / q)) :=
    Real.mul_rpow (by norm_num) hu0.le
  have h3 : u ^ (-(p / q)) * u = u ^ (-1 - 1 / q) := by
    have : -(p / q) + 1 = -1 - 1 / q := by
      have : p / q = 2 + 1 / q := by field_simp; linarith
      rw [this]; ring
    rw [← this, Real.rpow_add hu0, Real.rpow_one]
  have h4 : |s - b| ≤ Mpq p q * (2 * u) ^ (-(p / q)) / b := by
    rw [le_div_iff₀ hbpos]; exact h1
  refine le_trans h4 (le_of_eq ?_)
  rw [h2, hb, ← h3]
  field_simp


lemma ck_int_sqrt {p q : ℝ} (hp : 1 < p) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun u => Real.sqrt (fNq ⊤ p q u)) volume a b := by
  have hnn : ∀ x ∈ uIcc a b, 0 ≤ x := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with h | h <;> linarith [h.1]
  apply AntitoneOn.intervalIntegrable
  intro x hx y hy hxy
  exact Real.sqrt_le_sqrt (ck_anti (q := q) hp (hnn x hx) (hnn y hy) hxy)

lemma ck_G {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : rq p q = 1) {z : ℝ} (hz : 0 ≤ z) :
    |(∫ u in (0 : ℝ)..z, Real.sqrt (fNq ⊤ p q u)) - aQ q * Real.log (1 + z)|
      ≤ Cpq p q + aQ q * Real.log 2 + q * Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q := by
  have haQ := ck_aQ_pos hq
  have hK : 0 ≤ Cpq p q := Real.sqrt_nonneg _
  have hM : 0 ≤ Mpq p q := by
    unfold Mpq; apply Real.rpow_nonneg; apply div_nonneg (by linarith)
    exact mul_nonneg (Real.exp_pos 1).le hq.le
  have hB : 0 ≤ q * Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q := by positivity
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hint01 : 0 ≤ ∫ u in (0 : ℝ)..1, Real.sqrt (fNq ⊤ p q u) ∧
      ∫ u in (0 : ℝ)..1, Real.sqrt (fNq ⊤ p q u) ≤ Cpq p q := by
    refine ⟨intervalIntegral.integral_nonneg (by norm_num) (fun u _ => Real.sqrt_nonneg _), ?_⟩
    have := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      (ck_int_sqrt (q := q) hp le_rfl (by norm_num)) (intervalIntegrable_const (c := Cpq p q))
      (fun u hu => ck_sqrt_le hp hq hu.1)
    simpa using this
  rcases le_total z 1 with hz1 | hz1
  · have hI0 : 0 ≤ ∫ u in (0 : ℝ)..z, Real.sqrt (fNq ⊤ p q u) :=
      intervalIntegral.integral_nonneg hz (fun u _ => Real.sqrt_nonneg _)
    have hIz : ∫ u in (0 : ℝ)..z, Real.sqrt (fNq ⊤ p q u) ≤ Cpq p q := by
      have h1 : ∫ u in (0 : ℝ)..z, Real.sqrt (fNq ⊤ p q u) ≤ ∫ u in (0 : ℝ)..1, Real.sqrt (fNq ⊤ p q u) := by
        have := intervalIntegral.integral_interval_sub_left
          (ck_int_sqrt (q := q) hp le_rfl (by norm_num : (0:ℝ) ≤ 1)) (ck_int_sqrt (q := q) hp le_rfl hz)
        have hn : 0 ≤ ∫ u in z..1, Real.sqrt (fNq ⊤ p q u) :=
          intervalIntegral.integral_nonneg hz1 (fun u _ => Real.sqrt_nonneg _)
        linarith
      linarith [hint01.2]
    have hl0 : 0 ≤ Real.log (1 + z) := Real.log_nonneg (by linarith)
    have hl2 : Real.log (1 + z) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
    have : aQ q * Real.log (1 + z) ≤ aQ q * Real.log 2 := mul_le_mul_of_nonneg_left hl2 haQ.le
    have : 0 ≤ aQ q * Real.log (1 + z) := mul_nonneg haQ.le hl0
    rw [abs_le]; constructor <;> nlinarith
  · have hz0 : 0 < z := by linarith
    have hsplit : ∫ u in (0 : ℝ)..z, Real.sqrt (fNq ⊤ p q u)
        = (∫ u in (0 : ℝ)..1, Real.sqrt (fNq ⊤ p q u)) + ∫ u in (1 : ℝ)..z, Real.sqrt (fNq ⊤ p q u) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (ck_int_sqrt (q := q) hp le_rfl (by norm_num)) (ck_int_sqrt (q := q) hp (by norm_num) hz)).symm
    have hcint : ∫ u in (1 : ℝ)..z, aQ q / u = aQ q * Real.log z := by
      have : (fun u : ℝ => aQ q / u) = fun u => aQ q * u⁻¹ := by funext u; rw [div_eq_mul_inv]
      rw [this, intervalIntegral.integral_const_mul, integral_inv_of_pos (by norm_num) hz0, div_one]
    have hcI : IntervalIntegrable (fun u : ℝ => aQ q / u) volume 1 z := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le hz1] at hx
      have := hx.1
      simp only [id]; linarith
    set Bc := Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q with hBc
    have hBc0 : 0 ≤ Bc := by positivity
    have hpw : (-1 - 1 / q) + 1 = -(1 / q) := by ring
    have hrint : ∫ u in (1 : ℝ)..z, u ^ (-1 - 1 / q) = (z ^ (-(1 / q)) - 1) / (-(1 / q)) := by
      rw [integral_rpow (Or.inr ⟨by
        have : 0 < 1 / q := by positivity
        intro h; linarith, by
        rw [Set.mem_uIcc]; intro h; rcases h with h | h <;> linarith [h.1]⟩), hpw, Real.one_rpow]
    have hrle : ∫ u in (1 : ℝ)..z, u ^ (-1 - 1 / q) ≤ q := by
      rw [hrint]
      have hzp : 0 ≤ z ^ (-(1 / q)) := Real.rpow_nonneg hz0.le _
      have : (z ^ (-(1 / q)) - 1) / (-(1 / q)) = q * (1 - z ^ (-(1 / q))) := by
        field_simp; ring
      rw [this]; nlinarith
    have hrI : IntervalIntegrable (fun u : ℝ => u ^ (-1 - 1 / q)) volume 1 z := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le hz1] at hx
      left; simp only [id]; linarith [hx.1]
    have hdiffI : |∫ u in (1 : ℝ)..z, (Real.sqrt (fNq ⊤ p q u) - aQ q / u)|
        ≤ Bc * q := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le (a := 1) (b := z) hz1
        (f := fun u => Real.sqrt (fNq ⊤ p q u) - aQ q / u)
        (g := fun u => Bc * u ^ (-1 - 1 / q))
        (Filter.Eventually.of_forall fun u (hu : u ∈ Ioc (1:ℝ) z) => by
          have := ck_sqrt_asym hp hq hr hu.1.le
          simpa [Real.norm_eq_abs] using this)
        (hrI.const_mul _)
      rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs] at h1
      exact le_trans h1 (mul_le_mul_of_nonneg_left hrle hBc0)
    rw [intervalIntegral.integral_sub (ck_int_sqrt (q := q) hp (by norm_num) hz) hcI, hcint] at hdiffI
    have hl0 : Real.log z ≤ Real.log (1 + z) := Real.log_le_log hz0 (by linarith)
    have hl2 : Real.log (1 + z) ≤ Real.log 2 + Real.log z := by
      rw [← Real.log_mul (by norm_num) hz0.ne']
      exact Real.log_le_log (by linarith) (by linarith)
    have hm1 : aQ q * Real.log z ≤ aQ q * Real.log (1 + z) := mul_le_mul_of_nonneg_left hl0 haQ.le
    have hm2 : aQ q * Real.log (1 + z) ≤ aQ q * (Real.log 2 + Real.log z) :=
      mul_le_mul_of_nonneg_left hl2 haQ.le
    have hBq : Bc * q = q * Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q := by rw [hBc]; ring
    rw [hBq] at hdiffI
    rw [abs_le] at hdiffI ⊢
    rw [hsplit]
    constructor <;> nlinarith [hint01.1, hint01.2]

/-- `lem:app-phase-clock-integral`, part (i) of 3, snapshot `cr-2026-10-23`.
Source: `section.tex` l.2008–2030.
LaTeX (verbatim, `section.tex` l.2008–2030):
```
\begin{lemma}[The clock integral]\label{lem:app-phase-clock-integral}
Fix $p>1$, $q>0$ and $T\ge4$, and let $N\ge4$ and
$0<\epsilon<\epsilon_0(p,q,T)$. Let $Y$ be continuous on $[0,\infty)$ with
$Y\ge f_{N,q}$, and suppose that its first $T\epsilon$ hit $\hat u$ is
attained, $0<\hat u<\infty$ with $Y(\hat u)=T\epsilon$. Let $H\ge\hat u$ and
$\mathcal E\defeq\int_0^{\hat u}(\sqrt Y-\sqrt{f_{N,q}})\,\dif u$.
\begin{enumerate}[label=(\roman*)]
\item If $r<1$ and $H\le(N/4)^q$, then
\[
\frac{\sqrt A}{2(1-r)}\Big(\frac AT\Big)^{(1-r)/(2r)}\epsilon^{-(1-r)/(2r)}\le\int_0^{\hat u}\sqrt Y\,\dif u\le C\,I_r(H)+\mathcal E .
\]
\item If $r=1$ and $H\le(N/4)^q$, then $\int_0^{\hat u}\sqrt Y\,\dif u\ge\frac{\sqrt A}4\log\frac1\epsilon$, and
\[
\Big|\int_0^{\hat u}\sqrt Y\,\dif u-\frac{a_q}2\log\frac1\epsilon\Big|\le K_{p,q,T}+a_q\log_+\big((1+H)\sqrt\epsilon\big)+\frac{HN^{-q}}{\sqrt{2(p-1)}}+\mathcal E ,
\]
where $K_{p,q,T}\defeq C+a_q\log2+qM_{p,q}2^{-p/q}/a_q+\frac{a_q}2\log(T/A)$.
\item If $r>1$, then $\frac1{2\sqrt2}\le\int_0^{\hat u}\sqrt Y\,\dif u\le J(p,q)+\mathcal E$, and
\begin{multline*}
\Big|\int_0^{\hat u}\sqrt Y\,\dif u-J(p,q)\Big|\\
\le\Big[\frac1{\sqrt{2(p-1)}}+\frac C{r-1}\Big]N^{-q(r-1)}+\frac C{r-1}\Big(1+\frac12\log\frac1{2T\epsilon}\Big)^{1-r}+\mathcal E .
\end{multline*}
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_clock_integral_i
    {p q T ε H û : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (N : ℕ) (hN : 4 ≤ N)
    (hε : 0 < ε) (hε0 : ε < clockEps0 p q T)
    {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Ici 0))
    (hYf : ∀ u ∈ Ici (0 : ℝ), fNq (N : ℕ∞) p q u ≤ Y u)
    (hhit : firstHit Y (T * ε) = ENNReal.ofReal û) (hû0 : 0 < û) (hYû : Y û = T * ε)
    (hûH : û ≤ H) (hr : rq p q < 1) (hHN : H ≤ ((N : ℝ) / 4) ^ q) :
    Real.sqrt (Aconst p) / (2 * (1 - rq p q)) * (Aconst p / T) ^ ((1 - rq p q) / (2 * rq p q))
        * ε ^ (-((1 - rq p q) / (2 * rq p q)))
      ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) ∧
    ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) ≤
        Cpq p q * Ir (rq p q) H + ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N : ℕ∞) p q u)) := by
  have hp0 : 0 < p := by linarith
  have hT0 : 0 < T := by linarith
  have hN4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hr0 : 0 < rq p q := by unfold rq; exact div_pos (by linarith) (by linarith)
  have hr0' : rq p q ≠ 0 := hr0.ne'
  have hpos1 : 0 < 1 - rq p q := by linarith
  have hA0 : 0 < Aconst p := by unfold Aconst; positivity
  have hdr : dAQ p q = 2 * rq p q := by unfold dAQ rq; field_simp
  have hZa : 0 < Za p := by
    unfold Za
    have : 0 < 1 / (p - 1) := div_pos one_pos (by linarith)
    linarith
  have hE1 : (2 : ℝ) ^ dAQ p q * Za p ≤ Epq p q := by unfold Epq; exact le_max_left _ _
  have hE0 : 0 ≤ Epq p q := le_trans (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hZa.le) hE1
  have hsub : Icc (0 : ℝ) û ⊆ Ici 0 := fun x hx => hx.1
  have hcrH : ContinuousOn (fun w : ℝ => (1 + w) ^ (-rq p q)) (Icc 0 H) := by
    apply ContinuousOn.rpow_const
    · exact (continuous_const.add continuous_id).continuousOn
    · intro w hw
      left
      exact (show (0 : ℝ) < 1 + w by linarith [hw.1]).ne'
  have hcrH' : IntervalIntegrable (fun w : ℝ => (1 + w) ^ (-rq p q)) volume 0 H :=
    hcrH.intervalIntegrable_of_Icc (le_trans hû0.le hûH)
  have hcrû : IntervalIntegrable (fun w : ℝ => (1 + w) ^ (-rq p q)) volume 0 û :=
    (hcrH.mono (Icc_subset_Icc le_rfl hûH)).intervalIntegrable_of_Icc hû0.le
  have hIY : IntervalIntegrable (fun u => Real.sqrt (Y u)) volume 0 û :=
    ((hYc.mono hsub).sqrt).intervalIntegrable_of_Icc hû0.le
  have hIF : IntervalIntegrable (fun u => Real.sqrt (fNq (N : ℕ∞) p q u)) volume 0 û :=
    ((fl_cont N p q).sqrt).intervalIntegrable 0 û
  have hsplit : (∫ u in (0 : ℝ)..û, Real.sqrt (Y u))
      = (∫ u in (0 : ℝ)..û, Real.sqrt (fNq (N : ℕ∞) p q u))
        + ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N : ℕ∞) p q u)) := by
    have hdiff : ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N : ℕ∞) p q u))
        = (∫ u in (0 : ℝ)..û, Real.sqrt (Y u)) - ∫ u in (0 : ℝ)..û, Real.sqrt (fNq (N : ℕ∞) p q u) :=
      intervalIntegral.integral_sub hIY hIF
    rw [hdiff]
    ring
  have hnonneg : 0 ≤ ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N : ℕ∞) p q u)) := by
    apply intervalIntegral.integral_nonneg hû0.le
    intro u hu
    have h1 := hYf u hu.1
    have h2 := Real.sqrt_le_sqrt h1
    linarith
  -- lower envelope on [0, û]
  have hlow : ∀ w ∈ Icc (0 : ℝ) û,
      Real.sqrt (Aconst p) * (1 + w) ^ (-rq p q) ≤ Real.sqrt (fNq (N : ℕ∞) p q w) := by
    intro w hw
    have hw1 : (0 : ℝ) ≤ 1 + w := by linarith [hw.1]
    have hwN : w ≤ ((N : ℝ) / 4) ^ q := le_trans hw.2 (le_trans hûH hHN)
    have h := lem_app_phase_sums_ii hp hq N hN hw.1 hwN
    have hs : 0 ≤ (1 + w) ^ (-rq p q) := Real.rpow_nonneg hw1 _
    have hsq : (1 + w) ^ (-dAQ p q) = ((1 + w) ^ (-rq p q)) ^ 2 := by
      rw [hdr, ← Real.rpow_natCast, ← Real.rpow_mul hw1]
      congr 1
      push_cast
      ring
    rw [hsq] at h
    have hf : Aconst p * ((1 + w) ^ (-rq p q)) ^ 2 ≤ fNq (N : ℕ∞) p q w := by
      unfold fNq; linarith
    calc Real.sqrt (Aconst p) * (1 + w) ^ (-rq p q)
        = Real.sqrt ((Real.sqrt (Aconst p) * (1 + w) ^ (-rq p q)) ^ 2) :=
          (Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hs)).symm
      _ ≤ Real.sqrt (fNq (N : ℕ∞) p q w) :=
          Real.sqrt_le_sqrt (by rw [mul_pow, Real.sq_sqrt hA0.le]; exact hf)
  -- upper envelope on [0, û]
  have hup : ∀ w ∈ Icc (0 : ℝ) û,
      Real.sqrt (fNq (N : ℕ∞) p q w) ≤ Cpq p q * (1 + w) ^ (-rq p q) := by
    intro w hw
    have hw1 : (0 : ℝ) ≤ 1 + w := by linarith [hw.1]
    have h := lem_app_phase_sums_i hp hq (N : ℕ∞) hw.1
    have hs : 0 ≤ (1 + w) ^ (-rq p q) := Real.rpow_nonneg hw1 _
    have hsq : (1 + w) ^ (-dAQ p q) = ((1 + w) ^ (-rq p q)) ^ 2 := by
      rw [hdr, ← Real.rpow_natCast, ← Real.rpow_mul hw1]
      congr 1
      push_cast
      ring
    rw [hsq] at h
    have hf : fNq (N : ℕ∞) p q w ≤ (Epq p q / 2) * ((1 + w) ^ (-rq p q)) ^ 2 := by
      unfold fNq
      calc (1 / 2) * Lsum (N : ℕ∞) p q w
          ≤ (1 / 2) * (Epq p q * ((1 + w) ^ (-rq p q)) ^ 2) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ = (Epq p q / 2) * ((1 + w) ^ (-rq p q)) ^ 2 := by ring
    calc Real.sqrt (fNq (N : ℕ∞) p q w)
        ≤ Real.sqrt ((Epq p q / 2) * ((1 + w) ^ (-rq p q)) ^ 2) := Real.sqrt_le_sqrt hf
      _ = Real.sqrt (Epq p q / 2) * (1 + w) ^ (-rq p q) := by
          rw [Real.sqrt_mul (by linarith), Real.sqrt_sq hs]
      _ = Cpq p q * (1 + w) ^ (-rq p q) := by unfold Cpq; rfl
  -- integral bounds
  have hIlow : Real.sqrt (Aconst p) * Ir (rq p q) û
      ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (fNq (N : ℕ∞) p q u) := by
    unfold Ir
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hû0.le (hcrû.const_mul _) hIF (fun w hw => hlow w hw)
  have hIup : ∫ u in (0 : ℝ)..û, Real.sqrt (fNq (N : ℕ∞) p q u) ≤ Cpq p q * Ir (rq p q) H := by
    have h1 : ∫ u in (0 : ℝ)..û, Real.sqrt (fNq (N : ℕ∞) p q u)
        ≤ ∫ u in (0 : ℝ)..û, Cpq p q * (1 + u) ^ (-rq p q) :=
      intervalIntegral.integral_mono_on hû0.le hIF (hcrû.const_mul _) (fun w hw => hup w hw)
    have h2 : ∫ u in (0 : ℝ)..û, Cpq p q * (1 + u) ^ (-rq p q) = Cpq p q * Ir (rq p q) û := by
      unfold Ir
      rw [intervalIntegral.integral_const_mul]
    have h3 : Ir (rq p q) û ≤ Ir (rq p q) H := by
      unfold Ir
      have hsplit2 := intervalIntegral.integral_interval_sub_left hcrH' hcrû
      have hnn : 0 ≤ ∫ w in û..H, (1 + w) ^ (-rq p q) :=
        intervalIntegral.integral_nonneg hûH (fun w hw => Real.rpow_nonneg (by linarith [hw.1, hû0]) _)
      linarith
    have hC : 0 ≤ Cpq p q := Real.sqrt_nonneg _
    linarith [mul_le_mul_of_nonneg_left h3 hC]
  -- hit lower bound: 1 + û ≥ (A/(Tε))^{1/(2r)}, via A/(Tε) ≤ (1+û)^{2r}
  have hBpos : 0 < 1 + û := by linarith
  have hkey : Aconst p * (1 + û) ^ (-(2 * rq p q)) ≤ T * ε := by
    have h1 := hYf û hû0.le
    rw [hYû] at h1
    have h2 := lem_app_phase_sums_ii hp hq N hN hû0.le (le_trans hûH hHN)
    rw [hdr] at h2
    unfold fNq at h1
    linarith
  have hmul : (1 + û) ^ (-(2 * rq p q)) * (1 + û) ^ (2 * rq p q) = 1 := by
    rw [← Real.rpow_add hBpos]; simp
  have hA_le : Aconst p ≤ T * ε * (1 + û) ^ (2 * rq p q) := by
    have := mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg hBpos.le (2 * rq p q))
    rw [mul_assoc, hmul] at this
    linarith
  have hTε : 0 < T * ε := mul_pos hT0 hε
  have hdiv : Aconst p / (T * ε) ≤ (1 + û) ^ (2 * rq p q) := by
    rw [div_le_iff₀ hTε]
    linarith [mul_comm (T * ε) ((1 + û) ^ (2 * rq p q))]
  have hs0 : 0 ≤ (1 - rq p q) / (2 * rq p q) := div_nonneg hpos1.le (by linarith)
  have hW : (Aconst p / (T * ε)) ^ ((1 - rq p q) / (2 * rq p q)) ≤ (1 + û) ^ (1 - rq p q) := by
    calc (Aconst p / (T * ε)) ^ ((1 - rq p q) / (2 * rq p q))
        ≤ ((1 + û) ^ (2 * rq p q)) ^ ((1 - rq p q) / (2 * rq p q)) :=
          Real.rpow_le_rpow (div_nonneg hA0.le hTε.le) hdiv hs0
      _ = (1 + û) ^ (1 - rq p q) := by
          rw [← Real.rpow_mul hBpos.le]
          congr 1
          field_simp
  -- the constant 2 ≤ X
  have hK : (2 : ℝ) ≤ (Aconst p / (T * ε)) ^ ((1 - rq p q) / (2 * rq p q)) := by
    unfold clockEps0 at hε0
    rw [if_pos hr] at hε0
    have h4 : ε < Aconst p / (T * (2 : ℝ) ^ (2 * rq p q / (1 - rq p q))) :=
      lt_of_lt_of_le hε0 (min_le_right _ _)
    have hKpos : 0 < (2 : ℝ) ^ (2 * rq p q / (1 - rq p q)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h5 := (lt_div_iff₀ (mul_pos hT0 hKpos)).mp h4
    have h6 : (2 : ℝ) ^ (2 * rq p q / (1 - rq p q)) * (T * ε) < Aconst p := by
      calc (2 : ℝ) ^ (2 * rq p q / (1 - rq p q)) * (T * ε)
          = ε * (T * (2 : ℝ) ^ (2 * rq p q / (1 - rq p q))) := by ring
        _ < Aconst p := h5
    have h7 : (2 : ℝ) ^ (2 * rq p q / (1 - rq p q)) < Aconst p / (T * ε) :=
      (lt_div_iff₀ hTε).mpr h6
    have h8 : ((2 : ℝ) ^ (2 * rq p q / (1 - rq p q))) ^ ((1 - rq p q) / (2 * rq p q)) = 2 := by
      rw [← Real.rpow_mul (by norm_num)]
      have : 2 * rq p q / (1 - rq p q) * ((1 - rq p q) / (2 * rq p q)) = 1 := by
        field_simp
      rw [this, Real.rpow_one]
    calc (2 : ℝ) = ((2 : ℝ) ^ (2 * rq p q / (1 - rq p q))) ^ ((1 - rq p q) / (2 * rq p q)) := h8.symm
      _ ≤ (Aconst p / (T * ε)) ^ ((1 - rq p q) / (2 * rq p q)) :=
          Real.rpow_le_rpow hKpos.le h7.le hs0
  -- closed form of I_r(û)
  have hIr_val : Ir (rq p q) û = (((1 + û) ^ (1 - rq p q)) - 1) / (1 - rq p q) := by
    unfold Ir
    have key : ∫ w in (0 : ℝ)..û, (1 + w) ^ (-rq p q)
        = ∫ x in (1 + 0 : ℝ)..(1 + û), x ^ (-rq p q) :=
      intervalIntegral.integral_comp_add_left (fun x : ℝ => x ^ (-rq p q)) 1
    rw [key, add_zero, integral_rpow (Or.inl (by linarith)), Real.one_rpow]
    rw [show -rq p q + 1 = 1 - rq p q by ring]
  -- factor the target constant
  have hfac : (Aconst p / (T * ε)) ^ ((1 - rq p q) / (2 * rq p q))
      = (Aconst p / T) ^ ((1 - rq p q) / (2 * rq p q)) * ε ^ (-((1 - rq p q) / (2 * rq p q))) := by
    have hd' : Aconst p / (T * ε) = (Aconst p / T) * ε⁻¹ := by field_simp
    rw [hd', Real.mul_rpow (div_nonneg hA0.le hT0.le) (inv_nonneg.mpr hε.le),
      Real.inv_rpow hε.le, ← Real.rpow_neg hε.le]
  constructor
  · -- lower bound
    have hsA : 0 < Real.sqrt (Aconst p) := Real.sqrt_pos.mpr hA0
    have hlowI : Real.sqrt (Aconst p) * Ir (rq p q) û
        = Real.sqrt (Aconst p) * ((((1 + û) ^ (1 - rq p q)) - 1) / (1 - rq p q)) := by
      rw [hIr_val]
    set X := (Aconst p / (T * ε)) ^ ((1 - rq p q) / (2 * rq p q)) with hXdef
    set W := (1 + û) ^ (1 - rq p q) with hWdef
    have hiden : Real.sqrt (Aconst p) * ((W - 1) / (1 - rq p q))
        - Real.sqrt (Aconst p) / (2 * (1 - rq p q)) * X
        = (Real.sqrt (Aconst p) / (1 - rq p q)) * (W - 1 - X / 2) := by
      field_simp
    have hnn : 0 ≤ (Real.sqrt (Aconst p) / (1 - rq p q)) * (W - 1 - X / 2) :=
      mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hpos1.le) (by linarith)
    have hXW : Real.sqrt (Aconst p) * ((W - 1) / (1 - rq p q))
        ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) := by
      rw [hsplit, ← hlowI]
      exact le_trans hIlow (le_add_of_nonneg_right hnonneg)
    have hG : Real.sqrt (Aconst p) / (2 * (1 - rq p q)) * (Aconst p / T) ^ ((1 - rq p q) / (2 * rq p q))
        * ε ^ (-((1 - rq p q) / (2 * rq p q)))
        = Real.sqrt (Aconst p) / (2 * (1 - rq p q)) * X := by
      rw [hfac]; ring
    linarith [hiden, hnn, hXW, hG]
  · -- upper bound
    rw [hsplit]
    exact add_le_add hIup le_rfl

/-- `lem:app-phase-clock-integral`, part (ii) of 3, snapshot `cr-2026-10-23`.
Source: `section.tex` l.2008–2030.
LaTeX (verbatim, `section.tex` l.2008–2030):
```
\begin{lemma}[The clock integral]\label{lem:app-phase-clock-integral}
Fix $p>1$, $q>0$ and $T\ge4$, and let $N\ge4$ and
$0<\epsilon<\epsilon_0(p,q,T)$. Let $Y$ be continuous on $[0,\infty)$ with
$Y\ge f_{N,q}$, and suppose that its first $T\epsilon$ hit $\hat u$ is
attained, $0<\hat u<\infty$ with $Y(\hat u)=T\epsilon$. Let $H\ge\hat u$ and
$\mathcal E\defeq\int_0^{\hat u}(\sqrt Y-\sqrt{f_{N,q}})\,\dif u$.
\begin{enumerate}[label=(\roman*)]
\item If $r<1$ and $H\le(N/4)^q$, then
\[
\frac{\sqrt A}{2(1-r)}\Big(\frac AT\Big)^{(1-r)/(2r)}\epsilon^{-(1-r)/(2r)}\le\int_0^{\hat u}\sqrt Y\,\dif u\le C\,I_r(H)+\mathcal E .
\]
\item If $r=1$ and $H\le(N/4)^q$, then $\int_0^{\hat u}\sqrt Y\,\dif u\ge\frac{\sqrt A}4\log\frac1\epsilon$, and
\[
\Big|\int_0^{\hat u}\sqrt Y\,\dif u-\frac{a_q}2\log\frac1\epsilon\Big|\le K_{p,q,T}+a_q\log_+\big((1+H)\sqrt\epsilon\big)+\frac{HN^{-q}}{\sqrt{2(p-1)}}+\mathcal E ,
\]
where $K_{p,q,T}\defeq C+a_q\log2+qM_{p,q}2^{-p/q}/a_q+\frac{a_q}2\log(T/A)$.
\item If $r>1$, then $\frac1{2\sqrt2}\le\int_0^{\hat u}\sqrt Y\,\dif u\le J(p,q)+\mathcal E$, and
\begin{multline*}
\Big|\int_0^{\hat u}\sqrt Y\,\dif u-J(p,q)\Big|\\
\le\Big[\frac1{\sqrt{2(p-1)}}+\frac C{r-1}\Big]N^{-q(r-1)}+\frac C{r-1}\Big(1+\frac12\log\frac1{2T\epsilon}\Big)^{1-r}+\mathcal E .
\end{multline*}
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_clock_integral_ii
    {p q T ε H û : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (N : ℕ) (hN : 4 ≤ N)
    (hε : 0 < ε) (hε0 : ε < clockEps0 p q T)
    {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Ici 0))
    (hYf : ∀ u ∈ Ici (0 : ℝ), fNq (N : ℕ∞) p q u ≤ Y u)
    (hhit : firstHit Y (T * ε) = ENNReal.ofReal û) (hû0 : 0 < û) (hYû : Y û = T * ε)
    (hûH : û ≤ H) (hr : rq p q = 1) (hHN : H ≤ ((N : ℝ) / 4) ^ q) :
    Real.sqrt (Aconst p) / 4 * Real.log (1 / ε) ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) ∧
    |(∫ u in (0 : ℝ)..û, Real.sqrt (Y u)) - aQ q / 2 * Real.log (1 / ε)| ≤
        (Cpq p q + aQ q * Real.log 2 + q * Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q
          + aQ q / 2 * Real.log (T / Aconst p))
        + aQ q * max (Real.log ((1 + H) * Real.sqrt ε)) 0
        + H * (N : ℝ) ^ (-q) / Real.sqrt (2 * (p - 1))
        + ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N : ℕ∞) p q u)) := by
  have hp0 : 0 < p := by linarith
  have hT0 : 0 < T := by linarith
  have hN4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1 : 1 ≤ N := by omega
  have hA0 : 0 < Aconst p := by unfold Aconst; positivity
  have hA1 : Aconst p ≤ 1 := by
    unfold Aconst
    have h1 : (2 : ℝ) ^ (-(2 * p)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have h2 : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    calc (2 : ℝ) ^ (-(2 * p)) * Real.exp (-2) ≤ 1 * 1 :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
      _ = 1 := by norm_num
  have haQ := ck_aQ_pos hq
  have hsA : 0 < Real.sqrt (Aconst p) := Real.sqrt_pos.mpr hA0
  have hsub : Icc (0 : ℝ) û ⊆ Ici 0 := fun x hx => hx.1
  have hIY : IntervalIntegrable (fun u => Real.sqrt (Y u)) volume 0 û :=
    ((hYc.mono hsub).sqrt).intervalIntegrable_of_Icc hû0.le
  have hIF : IntervalIntegrable (fun u => Real.sqrt (fNq (N : ℕ∞) p q u)) volume 0 û :=
    ((fl_cont N p q).sqrt).intervalIntegrable 0 û
  have hsplit : (∫ u in (0 : ℝ)..û, Real.sqrt (Y u))
      = (∫ u in (0 : ℝ)..û, Real.sqrt (fNq (N : ℕ∞) p q u))
        + ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N : ℕ∞) p q u)) := by
    have hdiff : ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N : ℕ∞) p q u))
        = (∫ u in (0 : ℝ)..û, Real.sqrt (Y u)) - ∫ u in (0 : ℝ)..û, Real.sqrt (fNq (N : ℕ∞) p q u) :=
      intervalIntegral.integral_sub hIY hIF
    rw [hdiff]
    ring
  have hnonneg : 0 ≤ ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N : ℕ∞) p q u)) := by
    apply intervalIntegral.integral_nonneg hû0.le
    intro u hu
    have h1 := hYf u hu.1
    have h2 := Real.sqrt_le_sqrt h1
    linarith
  set D := ∫ u in (0 : ℝ)..û, Real.sqrt (fNq (N : ℕ∞) p q u) with hD
  set E := ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N : ℕ∞) p q u)) with hE
  -- lower envelope
  have hlow : ∀ w ∈ Icc (0 : ℝ) û,
      Real.sqrt (Aconst p) * (1 + w)⁻¹ ≤ Real.sqrt (fNq (N : ℕ∞) p q w) := by
    intro w hw
    have hw1 : (0 : ℝ) < 1 + w := by linarith [hw.1]
    have hwN : w ≤ ((N : ℝ) / 4) ^ q := le_trans hw.2 (le_trans hûH hHN)
    have h := lem_app_phase_sums_ii hp hq N hN hw.1 hwN
    have hdr : dAQ p q = 2 := by
      have : (p - 1) = 2 * q := by unfold rq at hr; field_simp at hr; linarith
      unfold dAQ; rw [this]; field_simp
    rw [hdr] at h
    have hsq : (1 + w) ^ (-(2 : ℝ)) = ((1 + w)⁻¹) ^ 2 := by
      rw [Real.rpow_neg hw1.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, inv_pow]
    rw [hsq] at h
    have hs : 0 ≤ (1 + w)⁻¹ := inv_nonneg.mpr hw1.le
    have hf : Aconst p * ((1 + w)⁻¹) ^ 2 ≤ fNq (N : ℕ∞) p q w := by
      unfold fNq; linarith
    calc Real.sqrt (Aconst p) * (1 + w)⁻¹
        = Real.sqrt ((Real.sqrt (Aconst p) * (1 + w)⁻¹) ^ 2) :=
          (Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hs)).symm
      _ ≤ Real.sqrt (fNq (N : ℕ∞) p q w) :=
          Real.sqrt_le_sqrt (by rw [mul_pow, Real.sq_sqrt hA0.le]; exact hf)
  have hcont : ContinuousOn (fun w : ℝ => (1 + w)⁻¹) (Icc 0 û) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro w hw; linarith [hw.1]
  have hintinv : IntervalIntegrable (fun w : ℝ => (1 + w)⁻¹) volume 0 û :=
    hcont.intervalIntegrable_of_Icc hû0.le
  have hIlog : ∫ w in (0 : ℝ)..û, (1 + w)⁻¹ = Real.log (1 + û) := by
    have key : ∫ w in (0 : ℝ)..û, (1 + w)⁻¹ = ∫ x in (1 + 0 : ℝ)..(1 + û), x⁻¹ :=
      intervalIntegral.integral_comp_add_left (fun x : ℝ => x⁻¹) 1
    rw [key, add_zero, integral_inv_of_pos (by norm_num) (by linarith), div_one]
  have hIlow : Real.sqrt (Aconst p) * Real.log (1 + û) ≤ D := by
    rw [← hIlog, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hû0.le (hintinv.const_mul _) hIF (fun w hw => hlow w hw)
  -- hit lower bound
  have hBpos : 0 < 1 + û := by linarith
  have hTε : 0 < T * ε := mul_pos hT0 hε
  have hdr2 : dAQ p q = 2 := by
    have : (p - 1) = 2 * q := by unfold rq at hr; field_simp at hr; linarith
    unfold dAQ; rw [this]; field_simp
  have hkey : Aconst p * ((1 + û)⁻¹) ^ 2 ≤ T * ε := by
    have h1 := hYf û hû0.le
    rw [hYû] at h1
    have h2 := lem_app_phase_sums_ii hp hq N hN hû0.le (le_trans hûH hHN)
    rw [hdr2] at h2
    have hsq : (1 + û) ^ (-(2 : ℝ)) = ((1 + û)⁻¹) ^ 2 := by
      rw [Real.rpow_neg hBpos.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, inv_pow]
    rw [hsq] at h2
    unfold fNq at h1
    linarith
  have hdiv : Aconst p / (T * ε) ≤ (1 + û) ^ 2 := by
    rw [div_le_iff₀ hTε]
    have h4 : ((1 + û)⁻¹) ^ 2 * (1 + û) ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hBpos.ne']; norm_num
    have h3 : Aconst p ≤ T * ε * (1 + û) ^ 2 :=
      calc Aconst p = Aconst p * (((1 + û)⁻¹) ^ 2 * (1 + û) ^ 2) := by rw [h4]; ring
        _ = (Aconst p * ((1 + û)⁻¹) ^ 2) * (1 + û) ^ 2 := by ring
        _ ≤ (T * ε) * (1 + û) ^ 2 := mul_le_mul_of_nonneg_right hkey (sq_nonneg _)
    linarith [mul_comm (T * ε) ((1 + û) ^ 2)]
  set ℓ := Real.log (1 + û) with hℓ
  set Lε := Real.log (1 / ε) with hLε
  set τ := Real.log (T / Aconst p) with hτdef
  have hτ0 : 0 ≤ τ := Real.log_nonneg (by rw [le_div_iff₀ hA0]; linarith)
  have hε1 : ε ≤ (Aconst p / T) ^ 2 := by
    have h := hε0
    unfold clockEps0 at h
    rw [if_neg (by rw [hr]; norm_num)] at h
    exact (lt_of_lt_of_le h (min_le_right _ _)).le
  have hLτ : 2 * τ ≤ Lε := by
    have h1 : (T / Aconst p) ^ 2 ≤ 1 / ε := by
      rw [le_div_iff₀ hε]
      have : (T / Aconst p) ^ 2 * (Aconst p / T) ^ 2 = 1 := by
        rw [← mul_pow, div_mul_div_comm, mul_comm T, div_self (by positivity)]; norm_num
      calc (T / Aconst p) ^ 2 * ε ≤ (T / Aconst p) ^ 2 * (Aconst p / T) ^ 2 :=
            mul_le_mul_of_nonneg_left hε1 (by positivity)
        _ = 1 := this
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hℓ1 : Lε - τ ≤ 2 * ℓ := by
    have h1 := Real.log_le_log (div_pos hA0 hTε) hdiv
    rw [Real.log_pow] at h1
    have h2 : Real.log (Aconst p / (T * ε)) = Lε - τ := by
      have : Aconst p / (T * ε) = (1 / ε) / (T / Aconst p) := by field_simp
      rw [this, Real.log_div (by positivity) (by positivity)]
    push_cast at h1
    linarith
  have hlogsq : Real.log ((1 + H) * Real.sqrt ε) = Real.log (1 + H) - Lε / 2 := by
    rw [Real.log_mul (by linarith) (Real.sqrt_pos.mpr hε).ne', Real.log_sqrt hε.le, hLε,
      one_div, Real.log_inv]
    ring
  have hℓ2 : ℓ ≤ Real.log ((1 + H) * Real.sqrt ε) + Lε / 2 := by
    rw [hlogsq]
    have : ℓ ≤ Real.log (1 + H) := Real.log_le_log hBpos (by linarith)
    linarith
  have hmx : Real.log ((1 + H) * Real.sqrt ε) ≤ max (Real.log ((1 + H) * Real.sqrt ε)) 0 := le_max_left _ _
  have hmx0 : 0 ≤ max (Real.log ((1 + H) * Real.sqrt ε)) 0 := le_max_right _ _
  constructor
  · have : D ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) := by rw [hsplit]; linarith
    have f1 := mul_le_mul_of_nonneg_left hℓ1 hsA.le
    have f2 := mul_le_mul_of_nonneg_left hLτ hsA.le
    linarith
  · -- constant
    have hG := ck_G (q := q) hp hq hr hû0.le
    have hsd : ∀ u ∈ Icc (0 : ℝ) û, 0 ≤ Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u) ∧
        Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u) ≤ (N : ℝ) ^ (-q) / Real.sqrt (2 * (p - 1)) :=
      fun u hu => ck_sqrt_diff hp hq hr N hN1 hu.1
    set c := (N : ℝ) ^ (-q) / Real.sqrt (2 * (p - 1)) with hc
    have hc0 : 0 ≤ c := by
      rw [hc]; apply div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.sqrt_nonneg _)
    have hIinf : IntervalIntegrable (fun u => Real.sqrt (fNq ⊤ p q u)) volume 0 û :=
      ck_int_sqrt (q := q) hp le_rfl hû0.le
    have hGD : (∫ u in (0 : ℝ)..û, Real.sqrt (fNq ⊤ p q u)) - D
        = ∫ u in (0 : ℝ)..û, (Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u)) :=
      (intervalIntegral.integral_sub hIinf hIF).symm
    have hGD0 : 0 ≤ ∫ u in (0 : ℝ)..û, (Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u)) :=
      intervalIntegral.integral_nonneg hû0.le (fun u hu => (hsd u hu).1)
    have hGD1 : ∫ u in (0 : ℝ)..û, (Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u)) ≤ H * c := by
      have := intervalIntegral.integral_mono_on hû0.le (hIinf.sub hIF)
        (intervalIntegrable_const (c := c)) (fun u hu => (hsd u hu).2)
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
      nlinarith
    set G := ∫ u in (0 : ℝ)..û, Real.sqrt (fNq ⊤ p q u) with hGdef
    rw [abs_le] at hG ⊢
    have hq' : (H * (N : ℝ) ^ (-q) / Real.sqrt (2 * (p - 1))) = H * c := by rw [hc]; ring
    rw [hq', hsplit]
    have e1 : aQ q * (Lε - τ) ≤ aQ q * (2 * ℓ) := mul_le_mul_of_nonneg_left hℓ1 haQ.le
    have e2 : aQ q * ℓ ≤ aQ q * (Real.log ((1 + H) * Real.sqrt ε) + Lε / 2) :=
      mul_le_mul_of_nonneg_left hℓ2 haQ.le
    have e3 : aQ q * Real.log ((1 + H) * Real.sqrt ε) ≤ aQ q * max (Real.log ((1 + H) * Real.sqrt ε)) 0 :=
      mul_le_mul_of_nonneg_left hmx haQ.le
    have e4 : 0 ≤ aQ q * max (Real.log ((1 + H) * Real.sqrt ε)) 0 := mul_nonneg haQ.le hmx0
    have e5 : 0 ≤ aQ q * τ := mul_nonneg haQ.le hτ0
    constructor <;> linarith [hG.1, hG.2]

/-! ## Clock integral (iii): private helpers (P-H.6.P4) -/

lemma cr_env {p q : ℝ} (hp : 1 < p) (hq : 0 < q) {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt (fNq ⊤ p q u) ≤ Cpq p q * (u + 1) ^ (-rq p q) := by
  have hL := lem_app_phase_sums_i hp hq ⊤ hu
  rw [add_comm 1 u] at hL
  have hq0 : q ≠ 0 := hq.ne'
  have hdr : dAQ p q = 2 * rq p q := by unfold dAQ rq; field_simp
  have hX : ((u + 1) ^ (-rq p q)) ^ 2 = (u + 1) ^ (-dAQ p q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : (0:ℝ) ≤ u + 1), hdr]
    congr 1
    push_cast
    ring
  have hZa : 0 < Za p := by
    unfold Za
    have : 0 < 1 / (p - 1) := div_pos one_pos (by linarith)
    linarith
  have hE1 : (2 : ℝ) ^ dAQ p q * Za p ≤ Epq p q := by unfold Epq; exact le_max_left _ _
  have hE0 : 0 ≤ Epq p q := le_trans (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hZa.le) hE1
  have hf : fNq ⊤ p q u ≤ (Epq p q / 2) * ((u + 1) ^ (-rq p q)) ^ 2 := by
    rw [hX]
    unfold fNq
    have := mul_le_mul_of_nonneg_left hL (by norm_num : (0:ℝ) ≤ 1 / 2)
    linarith
  have hX0 : 0 ≤ (u + 1) ^ (-rq p q) := Real.rpow_nonneg (by linarith) _
  calc Real.sqrt (fNq ⊤ p q u) ≤ Real.sqrt ((Epq p q / 2) * ((u + 1) ^ (-rq p q)) ^ 2) :=
        Real.sqrt_le_sqrt hf
    _ = Cpq p q * (u + 1) ^ (-rq p q) := by
        unfold Cpq
        rw [Real.sqrt_mul (by linarith), Real.sqrt_sq hX0]

lemma cr_summable_ind {p : ℝ} (hp : 1 < p) :
    Summable (fun i : ℕ => if 0 < i then (i : ℝ) ^ (-p) else 0) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
      (Real.summable_nat_rpow.mpr (by linarith : -p < -1))
  · split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg i) _
    · exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (Nat.cast_nonneg i) _

lemma cr_cont_inf {p q : ℝ} (hp : 1 < p) :
    ContinuousOn (fun u : ℝ => fNq ⊤ p q u) (Ici 0) := by
  have hcon : ContinuousOn (fun u : ℝ => ∑' i : ℕ,
      (if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0)) (Ici 0) := by
    refine continuousOn_tsum (f := fun (i : ℕ) (u : ℝ) =>
        if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0)
      (u := fun i : ℕ => if 0 < i then (i : ℝ) ^ (-p) else 0) (fun i => ?_)
      (cr_summable_ind hp) (fun n x hx => ?_)
    · by_cases h : 0 < i
      · simp only [h, if_true]
        exact (by fun_prop : Continuous (fun u : ℝ =>
          (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)))).continuousOn
      · simp only [h, if_false]
        exact continuousOn_const
    · have hx0 : 0 ≤ x := hx
      by_cases h : 0 < n
      · simp only [h, if_true]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          (Real.exp_pos _).le)]
        apply mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        apply Real.exp_le_one_iff.mpr
        nlinarith [mul_nonneg hx0 (Real.rpow_nonneg (Nat.cast_nonneg n) (-q))]
      · simp [h]
  have hfeq : (fun u : ℝ => fNq ⊤ p q u) = fun u : ℝ => (1 / 2) * ∑' i : ℕ,
      (if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) :=
    funext (fun u => ck_inf_eq p q u)
  rw [hfeq]
  exact continuousOn_const.mul hcon

lemma cr_sqrt_cont_inf {p q : ℝ} (hp : 1 < p) :
    ContinuousOn (fun u : ℝ => Real.sqrt (fNq ⊤ p q u)) (Ici 0) :=
  (cr_cont_inf hp).sqrt

lemma cr_int_inf {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : 1 < rq p q) :
    IntegrableOn (fun u : ℝ => Real.sqrt (fNq ⊤ p q u)) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable (fun u : ℝ => Real.sqrt (fNq ⊤ p q u))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((cr_sqrt_cont_inf hp).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  have hb : IntegrableOn (fun u : ℝ => Cpq p q * (u + 1) ^ (-rq p q)) (Ioi 0) :=
    Integrable.const_mul (integrableOn_add_rpow_Ioi_of_lt (a := -rq p q) (c := 0) (m := 1)
      (by linarith) (by norm_num)) _
  refine Integrable.mono' hb hmeas (ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => ?_))
  have hu0 : (0 : ℝ) ≤ u := (Set.mem_Ioi.mp hu).le
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact cr_env hp hq hu0

lemma cr_int_N {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : 1 < rq p q) (N : ℕ)
    (hN : 1 ≤ N) :
    IntegrableOn (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q u)) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q u))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((fl_cont N p q).sqrt).aestronglyMeasurable
  have hb : IntegrableOn (fun u : ℝ => Cpq p q * (u + 1) ^ (-rq p q)) (Ioi 0) :=
    Integrable.const_mul (integrableOn_add_rpow_Ioi_of_lt (a := -rq p q) (c := 0) (m := 1)
      (by linarith) (by norm_num)) _
  refine Integrable.mono' hb hmeas (ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => ?_))
  have hu0 : (0 : ℝ) ≤ u := (Set.mem_Ioi.mp hu).le
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact le_trans (Real.sqrt_le_sqrt (by linarith [(ck_diff (q := q) hp N hN hu0).1]))
    (cr_env hp hq hu0)

lemma cr_split {g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hg : IntegrableOn g (Ioi 0)) :
    ∫ u in Ioi (0 : ℝ), g u = (∫ u in (0 : ℝ)..a, g u) + ∫ u in Ioi a, g u := by
  rw [intervalIntegral.integral_of_le ha,
    ← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hg.mono_set Ioc_subset_Ioi_self) (hg.mono_set (Ioi_subset_Ioi ha)),
    Set.Ioc_union_Ioi_eq_Ioi ha]

lemma cr_lower_f {p q : ℝ} (N : ℕ) (hN : 1 ≤ N) {u : ℝ} (hu : 0 ≤ u) :
    (1 / 2) * Real.exp (-(2 * u)) ≤ fNq (N : ℕ∞) p q u := by
  unfold fNq
  rw [fl_eq_sum]
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hnn : ∀ i ∈ Finset.Icc 1 N,
      0 ≤ (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) :=
    fun i _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le
  have hs := Finset.single_le_sum
    (f := fun i : ℕ => (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q))) hnn h1
  simp only [Nat.cast_one, Real.one_rpow, one_mul, mul_one] at hs
  linarith

lemma cr_diff {p q : ℝ} (hp : 1 < p) (N : ℕ) (hN : 1 ≤ N) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u) ∧
    Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u)
      ≤ (N : ℝ) ^ ((1 - p) / 2) / Real.sqrt (2 * (p - 1)) := by
  obtain ⟨h1, h2⟩ := ck_diff (q := q) hp N hN hu
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hf0 : 0 ≤ fNq (N : ℕ∞) p q u := by
    unfold fNq Lsum
    apply mul_nonneg (by norm_num)
    apply tsum_nonneg
    intro i
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le
    · exact le_rfl
  have hle : Real.sqrt (fNq (N : ℕ∞) p q u) ≤ Real.sqrt (fNq ⊤ p q u) :=
    Real.sqrt_le_sqrt (by linarith)
  refine ⟨by linarith, ?_⟩
  have h3 : Real.sqrt (fNq ⊤ p q u)
      ≤ Real.sqrt (fNq ⊤ p q u - fNq (N : ℕ∞) p q u) + Real.sqrt (fNq (N : ℕ∞) p q u) := by
    have := ck_sqrt_add_le h1 hf0
    rwa [sub_add_cancel] at this
  have h4 : Real.sqrt (fNq ⊤ p q u - fNq (N : ℕ∞) p q u)
      ≤ (N : ℝ) ^ ((1 - p) / 2) / Real.sqrt (2 * (p - 1)) := by
    calc Real.sqrt (fNq ⊤ p q u - fNq (N : ℕ∞) p q u)
        ≤ Real.sqrt ((N : ℝ) ^ (1 - p) / (2 * (p - 1))) := Real.sqrt_le_sqrt h2
      _ = (N : ℝ) ^ ((1 - p) / 2) / Real.sqrt (2 * (p - 1)) := by
          rw [Real.sqrt_div (Real.rpow_nonneg hNpos.le _), Real.sqrt_eq_rpow ((N : ℝ) ^ (1 - p)),
            ← Real.rpow_mul hNpos.le, show (1 - p) * (1 / 2) = (1 - p) / 2 by ring]
  linarith

lemma cr_tail_int {r M : ℝ} (hr : 1 < r) (hM : 0 ≤ M) :
    ∫ t in Ioi M, (t + 1) ^ (-r) = (M + 1) ^ (1 - r) / (r - 1) := by
  have hr1 : (1 - r) ≠ 0 := (by linarith : 1 - r < 0).ne
  have hd : ∀ x ∈ Ici M, HasDerivAt (fun t : ℝ => (t + 1) ^ (1 - r) / (1 - r)) ((x + 1) ^ (-r)) x := by
    intro x hx
    have hxM : M ≤ x := hx
    have hx1 : (x + 1) ≠ 0 := (by linarith : (0 : ℝ) < x + 1).ne'
    have h1 : HasDerivAt (fun t : ℝ => t + 1) 1 x := (hasDerivAt_id x).add_const 1
    have h2 := (h1.rpow_const (p := 1 - r) (Or.inl hx1)).div_const (1 - r)
    convert h2 using 1
    rw [show 1 - r - 1 = -r by ring]
    field_simp
  have hint : IntegrableOn (fun t : ℝ => (t + 1) ^ (-r)) (Ioi M) :=
    integrableOn_add_rpow_Ioi_of_lt (a := -r) (c := M) (m := 1) (by linarith) (by linarith)
  have htend : Tendsto (fun t : ℝ => (t + 1) ^ (1 - r) / (1 - r)) atTop (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => (t + 1) ^ (-(r - 1))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith : 0 < r - 1)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_id)
    have h2 : Tendsto (fun t : ℝ => (t + 1) ^ (-(r - 1)) / (1 - r)) atTop (𝓝 (0 / (1 - r))) :=
      h.div_const (1 - r)
    rw [zero_div] at h2
    refine Tendsto.congr (fun t => ?_) h2
    rw [show -(r - 1) = 1 - r by ring]
  have hcont : ContinuousWithinAt (fun t : ℝ => (t + 1) ^ (1 - r) / (1 - r)) (Ici M) M :=
    (hd M (Set.mem_Ici.mpr le_rfl)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi M, HasDerivAt (fun t : ℝ => (t + 1) ^ (1 - r) / (1 - r)) ((x + 1) ^ (-r)) x :=
    fun x hx => hd x (Ioi_subset_Ici_self hx)
  have key : ∫ t in Ioi M, (t + 1) ^ (-r) = 0 - (M + 1) ^ (1 - r) / (1 - r) :=
    integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend
  rw [key, show (1 - r) = -(r - 1) by ring, div_neg]
  ring

lemma cr_tail {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : 1 < rq p q) {M : ℝ} (hM : 0 ≤ M) :
    ∫ u in Ioi M, Real.sqrt (fNq ⊤ p q u) ≤ Cpq p q / (rq p q - 1) * (M + 1) ^ (1 - rq p q) := by
  have hint := cr_int_inf hp hq hr
  have hb : IntegrableOn (fun u : ℝ => Cpq p q * (u + 1) ^ (-rq p q)) (Ioi M) :=
    Integrable.const_mul (integrableOn_add_rpow_Ioi_of_lt (a := -rq p q) (c := M) (m := 1)
      (by linarith) (by linarith)) _
  have h1 : ∫ u in Ioi M, Real.sqrt (fNq ⊤ p q u) ≤ ∫ u in Ioi M, Cpq p q * (u + 1) ^ (-rq p q) :=
    setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi hM)) hb measurableSet_Ioi
      (fun u hu => cr_env hp hq (le_trans hM (Set.mem_Ioi.mp hu).le))
  have h2 : ∫ u in Ioi M, Cpq p q * (u + 1) ^ (-rq p q)
      = Cpq p q * ((M + 1) ^ (1 - rq p q) / (rq p q - 1)) := by
    rw [integral_const_mul, cr_tail_int hr hM]
  calc _ ≤ _ := h1
    _ = _ := h2
    _ = Cpq p q / (rq p q - 1) * (M + 1) ^ (1 - rq p q) := by ring

lemma cr_rate {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : 1 < rq p q) (N : ℕ)
    (hN : 1 ≤ N) :
    0 ≤ Jpq p q - JN N p q ∧
      Jpq p q - JN N p q ≤
        (1 / Real.sqrt (2 * (p - 1)) + Cpq p q / (rq p q - 1)) * (N : ℝ) ^ (-(q * (rq p q - 1))) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hq0 : q ≠ 0 := hq.ne'
  have hM0 : (0 : ℝ) ≤ (N : ℝ) ^ q := (Real.rpow_pos_of_pos hNpos q).le
  have hCpq : 0 ≤ Cpq p q := by unfold Cpq; exact Real.sqrt_nonneg _
  have hint_inf := cr_int_inf hp hq hr
  have hint_N := cr_int_N hp hq hr N hN
  have hD : IntegrableOn (fun u : ℝ => Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u))
      (Ioi 0) :=
    Integrable.sub hint_inf hint_N
  have hJ : Jpq p q - JN N p q
      = ∫ u in Ioi (0 : ℝ), (Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u)) := by
    unfold Jpq JN
    exact (integral_sub hint_inf hint_N).symm
  have hnn : 0 ≤ Jpq p q - JN N p q := by
    rw [hJ]
    exact setIntegral_nonneg measurableSet_Ioi
      (fun u hu => (cr_diff hp N hN (Set.mem_Ioi.mp hu).le).1)
  have hsplit : ∫ u in Ioi (0 : ℝ), (Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u))
      = (∫ u in (0 : ℝ)..(N : ℝ) ^ q, (Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u)))
        + ∫ u in Ioi ((N : ℝ) ^ q),
          (Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u)) :=
    cr_split hM0 hD
  have hIM : IntervalIntegrable
      (fun u : ℝ => Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u)) volume 0 ((N : ℝ) ^ q) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hM0).2 (hD.mono_set Ioc_subset_Ioi_self)
  have hMc : (N : ℝ) ^ q * (N : ℝ) ^ ((1 - p) / 2) = (N : ℝ) ^ (-(q * (rq p q - 1))) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    unfold rq
    field_simp
    ring
  have hA : ∫ u in (0 : ℝ)..(N : ℝ) ^ q,
      (Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u))
      ≤ (N : ℝ) ^ (-(q * (rq p q - 1))) / Real.sqrt (2 * (p - 1)) := by
    have h := intervalIntegral.integral_mono_on hM0 hIM intervalIntegrable_const
      (fun u hu => (cr_diff hp N hN hu.1).2)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
    calc _ ≤ _ := h
      _ = (N : ℝ) ^ (-(q * (rq p q - 1))) / Real.sqrt (2 * (p - 1)) := by
        rw [← mul_div_assoc, hMc]
  have hpow : ((N : ℝ) ^ q + 1) ^ (1 - rq p q) ≤ (N : ℝ) ^ (-(q * (rq p q - 1))) := by
    have h3 := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNpos q)
      (le_add_of_nonneg_right zero_le_one : (N : ℝ) ^ q ≤ (N : ℝ) ^ q + 1)
      (by linarith : 1 - rq p q ≤ 0)
    rw [← Real.rpow_mul hNpos.le] at h3
    refine le_trans h3 (le_of_eq ?_)
    congr 1
    ring
  have hB : ∫ u in Ioi ((N : ℝ) ^ q),
      (Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u))
      ≤ Cpq p q / (rq p q - 1) * (N : ℝ) ^ (-(q * (rq p q - 1))) := by
    have h1 : ∫ u in Ioi ((N : ℝ) ^ q),
        (Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u))
        ≤ ∫ u in Ioi ((N : ℝ) ^ q), Real.sqrt (fNq ⊤ p q u) :=
      setIntegral_mono_on (hD.mono_set (Ioi_subset_Ioi hM0))
        (hint_inf.mono_set (Ioi_subset_Ioi hM0)) measurableSet_Ioi
        (fun u _ => sub_le_self _ (Real.sqrt_nonneg _))
    have h2 := cr_tail hp hq hr hM0
    have h4 : Cpq p q / (rq p q - 1) * ((N : ℝ) ^ q + 1) ^ (1 - rq p q)
        ≤ Cpq p q / (rq p q - 1) * (N : ℝ) ^ (-(q * (rq p q - 1))) :=
      mul_le_mul_of_nonneg_left hpow (div_nonneg hCpq (by linarith))
    linarith
  refine ⟨hnn, ?_⟩
  rw [hJ, hsplit]
  have e : (1 / Real.sqrt (2 * (p - 1)) + Cpq p q / (rq p q - 1)) * (N : ℝ) ^ (-(q * (rq p q - 1)))
      = (N : ℝ) ^ (-(q * (rq p q - 1))) / Real.sqrt (2 * (p - 1))
        + Cpq p q / (rq p q - 1) * (N : ℝ) ^ (-(q * (rq p q - 1))) := by
    ring
  rw [e]
  linarith [hA, hB]

/-- `lem:app-phase-clock-integral`, part (iii) of 3, snapshot `cr-2026-10-23`.
Source: `section.tex` l.2008–2030.
LaTeX (verbatim, `section.tex` l.2008–2030):
```
\begin{lemma}[The clock integral]\label{lem:app-phase-clock-integral}
Fix $p>1$, $q>0$ and $T\ge4$, and let $N\ge4$ and
$0<\epsilon<\epsilon_0(p,q,T)$. Let $Y$ be continuous on $[0,\infty)$ with
$Y\ge f_{N,q}$, and suppose that its first $T\epsilon$ hit $\hat u$ is
attained, $0<\hat u<\infty$ with $Y(\hat u)=T\epsilon$. Let $H\ge\hat u$ and
$\mathcal E\defeq\int_0^{\hat u}(\sqrt Y-\sqrt{f_{N,q}})\,\dif u$.
\begin{enumerate}[label=(\roman*)]
\item If $r<1$ and $H\le(N/4)^q$, then
\[
\frac{\sqrt A}{2(1-r)}\Big(\frac AT\Big)^{(1-r)/(2r)}\epsilon^{-(1-r)/(2r)}\le\int_0^{\hat u}\sqrt Y\,\dif u\le C\,I_r(H)+\mathcal E .
\]
\item If $r=1$ and $H\le(N/4)^q$, then $\int_0^{\hat u}\sqrt Y\,\dif u\ge\frac{\sqrt A}4\log\frac1\epsilon$, and
\[
\Big|\int_0^{\hat u}\sqrt Y\,\dif u-\frac{a_q}2\log\frac1\epsilon\Big|\le K_{p,q,T}+a_q\log_+\big((1+H)\sqrt\epsilon\big)+\frac{HN^{-q}}{\sqrt{2(p-1)}}+\mathcal E ,
\]
where $K_{p,q,T}\defeq C+a_q\log2+qM_{p,q}2^{-p/q}/a_q+\frac{a_q}2\log(T/A)$.
\item If $r>1$, then $\frac1{2\sqrt2}\le\int_0^{\hat u}\sqrt Y\,\dif u\le J(p,q)+\mathcal E$, and
\begin{multline*}
\Big|\int_0^{\hat u}\sqrt Y\,\dif u-J(p,q)\Big|\\
\le\Big[\frac1{\sqrt{2(p-1)}}+\frac C{r-1}\Big]N^{-q(r-1)}+\frac C{r-1}\Big(1+\frac12\log\frac1{2T\epsilon}\Big)^{1-r}+\mathcal E .
\end{multline*}
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_clock_integral_iii
    {p q T ε H û : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (N : ℕ) (hN : 4 ≤ N)
    (hε : 0 < ε) (hε0 : ε < clockEps0 p q T)
    {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Ici 0))
    (hYf : ∀ u ∈ Ici (0 : ℝ), fNq (N : ℕ∞) p q u ≤ Y u)
    (hhit : firstHit Y (T * ε) = ENNReal.ofReal û) (hû0 : 0 < û) (hYû : Y û = T * ε)
    (hûH : û ≤ H) (hr : 1 < rq p q) :
    1 / (2 * Real.sqrt 2) ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) ∧
    ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) ≤
        Jpq p q + ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N : ℕ∞) p q u)) ∧
    |(∫ u in (0 : ℝ)..û, Real.sqrt (Y u)) - Jpq p q| ≤
        (1 / Real.sqrt (2 * (p - 1)) + Cpq p q / (rq p q - 1)) * (N : ℝ) ^ (-(q * (rq p q - 1)))
        + Cpq p q / (rq p q - 1) * (1 + 1 / 2 * Real.log (1 / (2 * T * ε))) ^ (1 - rq p q)
        + ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N : ℕ∞) p q u)) := by
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hT0 : 0 < T := by linarith
  have hCpq : 0 ≤ Cpq p q := by unfold Cpq; exact Real.sqrt_nonneg _
  have hε8 : ε < 1 / (8 * T) :=
    lt_of_lt_of_le hε0 (by unfold clockEps0; split_ifs <;> simp [min_le_iff])
  have hεT : 8 * T * ε < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hε8
    linarith
  have hpos2 : 0 < 2 * T * ε := by positivity
  have hsub : Icc (0 : ℝ) û ⊆ Ici 0 := fun x hx => hx.1
  have hYû' : fNq (N : ℕ∞) p q û ≤ T * ε := by
    rw [← hYû]
    exact hYf û (Set.mem_Ici.mpr hû0.le)
  have hexp : Real.exp (-(2 * û)) ≤ 2 * T * ε := by
    have := cr_lower_f (p := p) (q := q) N hN1 hû0.le
    linarith
  have hl_le : 1 / 2 * Real.log (1 / (2 * T * ε)) ≤ û := by
    have hlog : -(2 * û) ≤ Real.log (2 * T * ε) := by
      have := Real.log_le_log (Real.exp_pos _) hexp
      rwa [Real.log_exp] at this
    have hinv : Real.log (1 / (2 * T * ε)) = -Real.log (2 * T * ε) := by
      rw [one_div, Real.log_inv]
    rw [hinv]
    linarith
  have hl_nonneg : 0 ≤ 1 / 2 * Real.log (1 / (2 * T * ε)) := by
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    rw [one_le_div hpos2]
    linarith
  have hTb : 0 ≤ Cpq p q / (rq p q - 1) * (1 + 1 / 2 * Real.log (1 / (2 * T * ε))) ^ (1 - rq p q) :=
    mul_nonneg (div_nonneg hCpq (by linarith)) (Real.rpow_nonneg (by linarith) _)
  have hexpû : Real.exp (-û) ≤ 1 / 2 := by
    have hsq : Real.exp (-(2 * û)) = Real.exp (-û) * Real.exp (-û) := by
      rw [← Real.exp_add]
      ring_nf
    have hpos := Real.exp_pos (-û)
    nlinarith [hexp, hsq, hεT, hpos]
  have hE : ∫ u in (0 : ℝ)..û, Real.exp (-u) = 1 - Real.exp (-û) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := û) (f := Real.exp)
    rw [h, integral_exp]
    simp
  have hlow_pt : ∀ u ∈ Icc (0 : ℝ) û, 1 / Real.sqrt 2 * Real.exp (-u) ≤ Real.sqrt (Y u) := by
    intro u hu
    have hY : 1 / 2 * Real.exp (-(2 * u)) ≤ Y u :=
      le_trans (cr_lower_f (p := p) (q := q) N hN1 hu.1) (hYf u hu.1)
    have e2 : (1 / Real.sqrt 2 * Real.exp (-u)) ^ 2 = 1 / 2 * Real.exp (-(2 * u)) := by
      rw [show Real.exp (-(2 * u)) = Real.exp (-u) * Real.exp (-u) by
        rw [← Real.exp_add]; ring_nf]
      rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have hx : 0 ≤ 1 / Real.sqrt 2 * Real.exp (-u) := by positivity
    rw [Real.le_sqrt hx (le_trans (by positivity) hY), e2]
    exact hY
  have hIY : IntervalIntegrable (fun u => Real.sqrt (Y u)) volume 0 û :=
    ((hYc.mono hsub).sqrt).intervalIntegrable_of_Icc hû0.le
  have hIF : IntervalIntegrable (fun u => Real.sqrt (fNq (N : ℕ∞) p q u)) volume 0 û :=
    ((fl_cont N p q).sqrt).intervalIntegrable 0 û
  have hIE : IntervalIntegrable (fun u => 1 / Real.sqrt 2 * Real.exp (-u)) volume 0 û :=
    (by fun_prop : Continuous (fun u : ℝ => 1 / Real.sqrt 2 * Real.exp (-u))).intervalIntegrable 0 û
  have hlow_int : 1 / Real.sqrt 2 * (1 - Real.exp (-û)) ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) := by
    rw [← hE, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hû0.le hIE hIY hlow_pt
  have hlow : 1 / (2 * Real.sqrt 2) ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) := by
    have h12 : 1 / (2 * Real.sqrt 2) = 1 / Real.sqrt 2 * (1 / 2) := by ring
    have hnn : 0 ≤ 1 / Real.sqrt 2 := by positivity
    rw [h12]
    exact le_trans (mul_le_mul_of_nonneg_left (by linarith) hnn) hlow_int
  have hsplitE := intervalIntegral.integral_sub hIY hIF
  have hEnn : 0 ≤ ∫ u in (0 : ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N : ℕ∞) p q u)) :=
    intervalIntegral.integral_nonneg hû0.le
      (fun u hu => sub_nonneg.mpr (Real.sqrt_le_sqrt (hYf u hu.1)))
  have hint_inf := cr_int_inf hp hq hr
  have hint_N := cr_int_N hp hq hr N hN1
  have hIinf : IntervalIntegrable (fun u => Real.sqrt (fNq ⊤ p q u)) volume 0 û :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hû0.le).2 (hint_inf.mono_set Ioc_subset_Ioi_self)
  have hAN_le : ∫ u in (0 : ℝ)..û, Real.sqrt (fNq (N : ℕ∞) p q u)
      ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (fNq ⊤ p q u) :=
    intervalIntegral.integral_mono_on hû0.le hIF hIinf
      (fun u hu => by linarith [(cr_diff (q := q) hp N hN1 hu.1).1])
  have hsplitInf := cr_split hû0.le hint_inf
  have hsplitN := cr_split hû0.le hint_N
  have hTnn : 0 ≤ ∫ u in Ioi û, Real.sqrt (fNq ⊤ p q u) :=
    setIntegral_nonneg measurableSet_Ioi (fun u _ => Real.sqrt_nonneg _)
  have hTdiff : 0 ≤ ∫ u in Ioi û, (Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u)) :=
    setIntegral_nonneg measurableSet_Ioi
      (fun u hu => (cr_diff hp N hN1 (le_of_lt (lt_of_le_of_lt hû0.le (Set.mem_Ioi.mp hu)))).1)
  have hTsplit := integral_sub (hint_inf.mono_set (Ioi_subset_Ioi hû0.le))
    (hint_N.mono_set (Ioi_subset_Ioi hû0.le))
  have hTail2 : (û + 1) ^ (1 - rq p q) ≤ (1 + 1 / 2 * Real.log (1 / (2 * T * ε))) ^ (1 - rq p q) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have hTail3 : ∫ u in Ioi û, Real.sqrt (fNq ⊤ p q u)
      ≤ Cpq p q / (rq p q - 1) * (1 + 1 / 2 * Real.log (1 / (2 * T * ε))) ^ (1 - rq p q) :=
    le_trans (cr_tail hp hq hr hû0.le)
      (mul_le_mul_of_nonneg_left hTail2 (div_nonneg hCpq (by linarith)))
  have hrate := cr_rate hp hq hr N hN1
  have hJdef : Jpq p q = ∫ u in Ioi (0 : ℝ), Real.sqrt (fNq ⊤ p q u) := rfl
  have hJNdef : JN N p q = ∫ u in Ioi (0 : ℝ), Real.sqrt (fNq (N : ℕ∞) p q u) := rfl
  have hJ_eq : Jpq p q - JN N p q
      = ((∫ u in (0 : ℝ)..û, Real.sqrt (fNq ⊤ p q u))
          - ∫ u in (0 : ℝ)..û, Real.sqrt (fNq (N : ℕ∞) p q u))
        + ((∫ u in Ioi û, Real.sqrt (fNq ⊤ p q u))
          - ∫ u in Ioi û, Real.sqrt (fNq (N : ℕ∞) p q u)) := by
    rw [hJdef, hJNdef, hsplitInf, hsplitN]
    ring
  refine ⟨hlow, ?_, ?_⟩
  · linarith [hsplitE, hAN_le, hsplitInf, hTnn, hJdef]
  · rw [abs_le]
    constructor
    · linarith [hrate.1, hrate.2, hJ_eq, hTdiff, hAN_le, hsplitE, hEnn, hTail3, hTnn, hTb]
    · linarith [hrate.1, hrate.2, hJ_eq, hTdiff, hAN_le, hsplitE, hEnn, hTail3, hTnn, hTb]

/-- `lem:app-phase-clock-integral`, part rate (displayed bound in part (iii)); declaration exposed for consumers `Jall`, `accfirst`, `frozen`, snapshot `cr-2026-10-23`.
Source: `section.tex` l.2096–2100.
LaTeX (verbatim, `section.tex` l.2096–2100):
```
On $[0,N^q]$ the pointwise bound $\sqrt{f_{\infty,q}}-\sqrt f\le N^{(1-p)/2}/\sqrt{2(p-1)}=N^{-qr}/\sqrt{2(p-1)}$
holds, and on $[N^q,\infty)$ the integrand is at most $C(1+u)^{-r}$; hence
\[
0\le J(p,q)-J_N(p,q)\le\Big[\frac1{\sqrt{2(p-1)}}+\frac C{r-1}\Big]N^{-q(r-1)} .
\]
```
-/
theorem lem_app_phase_clock_integral_rate
    {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : 1 < rq p q) (N : ℕ) (hN : 4 ≤ N) :
    0 ≤ Jpq p q - JN N p q ∧
      Jpq p q - JN N p q ≤
        (1 / Real.sqrt (2 * (p - 1)) + Cpq p q / (rq p q - 1)) * (N : ℝ) ^ (-(q * (rq p q - 1))) := by
  exact cr_rate hp hq hr N (by omega)

/-! ## The r = 1 integral bounds (proof of `lem:app-phase-clock-integral`(ii)) -/

/-- `lem:app-phase-clock-integral`, r = 1 integral bound for the infinite model, snapshot `cr-2026-10-23`.
Source: `section.tex` l.2059–2071 (proof of part (ii); the displayed bound for every `z ≥ 0`).
LaTeX (verbatim, `section.tex` l.2059–2071):
```
$p=2q+1$, so $d(p,q)=2$ and $\Gamma(2)=1$. \Cref{lem:app-phase-laplace} with
$2u$ in place of $a$, divided by $2$, gives
$\abs{f_{\infty,q}(u)-a_q^2u^{-2}}\le M_{p,q}(2u)^{-p/q}$. Dividing by
$\sqrt{f_{\infty,q}}+a_q/u\ge a_q/u$ gives, for $u\ge1$,
\[
\Big|\sqrt{f_{\infty,q}(u)}-\frac{a_q}u\Big|\le\frac{M_{p,q}2^{-p/q}}{a_q}\,u^{-1-1/q} .
\]
The right side has integral $qM_{p,q}2^{-p/q}/a_q$ over $[1,\infty)$, and
$\sqrt{f_{\infty,q}}\le C$ on $[0,1]$. Together with
$0\le\log(1+z)-\log z\le\log2$ for $z\ge1$, this gives, for every $z\ge0$,
\[
\Big|\int_0^z\sqrt{f_{\infty,q}}\,\dif u-a_q\log(1+z)\Big|\le C+a_q\log2+\frac{qM_{p,q}2^{-p/q}}{a_q} .
\]
```
-/
theorem lem_app_phase_clock_integral_r1_inf
    {p q : ℝ} (hq : 0 < q) (hp : p = 2 * q + 1) {z : ℝ} (hz : 0 ≤ z) :
    |(∫ u in (0 : ℝ)..z, Real.sqrt (fNq ⊤ p q u)) - aQ q * Real.log (1 + z)| ≤
      Cpq p q + aQ q * Real.log 2 + q * Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q := by
  have hr : rq p q = 1 := by
    unfold rq
    rw [hp, show 2 * q + 1 - 1 = 2 * q by ring]
    exact div_self (mul_pos two_pos hq).ne'
  have hp1 : 1 < p := by rw [hp]; linarith
  exact ck_G hp1 hq hr hz

/-- `lem:app-phase-clock-integral`, r = 1 finite-N integral bound, snapshot `cr-2026-10-23`.
Source: `section.tex` l.2072–2076 (proof of part (ii); there stated with `û` in place of `z`, here for
every `z ≥ 0`, and for every integer `N ≥ 1`, the range of `lem_app_phase_laplace_ii`).
LaTeX (verbatim, `section.tex` l.2072–2076):
```
The finite sum differs from the infinite one by
$0\le f_{\infty,q}-f\le N^{1-p}/(2(p-1))$ (\cref{lem:app-phase-laplace}), and
$N^{(1-p)/2}=N^{-q}$, so
\[
0\le\int_0^{\hat u}\big(\sqrt{f_{\infty,q}}-\sqrt f\big)\,\dif u\le\frac{\hat uN^{-q}}{\sqrt{2(p-1)}}\le\frac{HN^{-q}}{\sqrt{2(p-1)}} .
```
-/
theorem lem_app_phase_clock_integral_r1_diff
    {p q : ℝ} (hq : 0 < q) (hp : p = 2 * q + 1) (N : ℕ) (hN : 1 ≤ N) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ (∫ u in (0 : ℝ)..z, (Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u))) ∧
      (∫ u in (0 : ℝ)..z, (Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u))) ≤
        z * (N : ℝ) ^ (-q) / Real.sqrt (2 * (p - 1)) := by
  have hr : rq p q = 1 := by
    unfold rq
    rw [hp, show 2 * q + 1 - 1 = 2 * q by ring]
    exact div_self (mul_pos two_pos hq).ne'
  have hp1 : 1 < p := by rw [hp]; linarith
  have hi1 : IntervalIntegrable (fun u => Real.sqrt (fNq ⊤ p q u)) volume 0 z :=
    ck_int_sqrt hp1 le_rfl hz
  have hi2 : IntervalIntegrable (fun u => Real.sqrt (fNq (N : ℕ∞) p q u)) volume 0 z :=
    (Continuous.sqrt (fl_cont N p q)).intervalIntegrable 0 z
  have hi : IntervalIntegrable
      (fun u => Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u)) volume 0 z :=
    hi1.sub hi2
  have hc : IntervalIntegrable (fun _ : ℝ => (N : ℝ) ^ (-q) / Real.sqrt (2 * (p - 1)))
      volume 0 z := intervalIntegrable_const
  have hint : ∫ _ in (0 : ℝ)..z, (N : ℝ) ^ (-q) / Real.sqrt (2 * (p - 1))
      = z * (N : ℝ) ^ (-q) / Real.sqrt (2 * (p - 1)) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  constructor
  · exact intervalIntegral.integral_nonneg hz (fun u hu => (ck_sqrt_diff hp1 hq hr N hN hu.1).1)
  · calc (∫ u in (0 : ℝ)..z, (Real.sqrt (fNq ⊤ p q u) - Real.sqrt (fNq (N : ℕ∞) p q u)))
        ≤ ∫ _ in (0 : ℝ)..z, (N : ℝ) ^ (-q) / Real.sqrt (2 * (p - 1)) :=
          intervalIntegral.integral_mono_on hz hi hc
            (fun u hu => (ck_sqrt_diff hp1 hq hr N hN hu.1).2)
      _ = z * (N : ℝ) ^ (-q) / Real.sqrt (2 * (p - 1)) := hint

/-! ## Finite exponential mixtures -/

/-! Helpers for `lem_app_phase_mixture` (private, proved here). -/

lemma mx_exists_pos {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hF0 : 0 < ∑ i, a i) :
    ∃ i, 0 < a i := by
  by_contra h
  push_neg at h
  have : ∑ i, a i ≤ 0 := Finset.sum_nonpos fun i _ => h i
  linarith

lemma mx_F_nonneg {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (u : ℝ) :
    0 ≤ mixF a b u :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (Real.exp_pos _).le

lemma mx_F_pos {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hF0 : 0 < ∑ i, a i)
    (u : ℝ) : 0 < mixF a b u := by
  obtain ⟨i, hi⟩ := mx_exists_pos a ha hF0
  unfold mixF
  exact Finset.sum_pos' (fun j _ => mul_nonneg (ha j) (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩

lemma mx_F_le {n : ℕ} (a b : Fin n → ℝ) (bmin : ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, bmin ≤ b i) {u : ℝ} (hu : 0 ≤ u) :
    mixF a b u ≤ (∑ i, a i) * Real.exp (-(bmin * u)) := by
  unfold mixF
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ha i)
  apply Real.exp_le_exp.2
  have := mul_le_mul_of_nonneg_right (hb i) hu
  linarith

lemma mx_sqrt_le {n : ℕ} (a b : Fin n → ℝ) (bmin : ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, bmin ≤ b i) {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt (mixF a b u) ≤ Real.sqrt (∑ i, a i) * Real.exp (-(bmin * u) / 2) := by
  have hF0 : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha i
  have hsq : Real.exp (-(bmin * u) / 2) ^ 2 = Real.exp (-(bmin * u)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le, ?_⟩
  rw [mul_pow, Real.sq_sqrt hF0, hsq]
  exact mx_F_le a b bmin ha hb hu

lemma mx_bound_integrable {bmin c : ℝ} (hbmin : 0 < bmin) :
    IntegrableOn (fun u : ℝ => c * Real.exp (-(bmin * u) / 2)) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => c * Real.exp (-(bmin / 2) * u)) (Ioi 0) :=
    Integrable.const_mul (exp_neg_integrableOn_Ioi 0 (b := bmin / 2) (by positivity)) c
  refine IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
  rw [show -(bmin * u) / 2 = -(bmin / 2) * u by ring]

lemma mx_bound_integral {bmin c : ℝ} (hbmin : 0 < bmin) :
    ∫ u in Ioi (0 : ℝ), c * Real.exp (-(bmin * u) / 2) = c * (2 / bmin) := by
  rw [integral_const_mul]
  congr 1
  have h := integral_exp_mul_Ioi (a := -(bmin / 2)) (by linarith) 0
  have e : (fun u : ℝ => Real.exp (-(bmin * u) / 2)) = fun u => Real.exp (-(bmin / 2) * u) := by
    funext u; congr 1; ring
  rw [e, h]
  simp

lemma mx_sqrt_integrable {n : ℕ} (a b : Fin n → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, bmin ≤ b i) :
    IntegrableOn (fun u => Real.sqrt (mixF a b u)) (Ioi 0) := by
  refine Integrable.mono' (mx_bound_integrable (c := Real.sqrt (∑ i, a i)) hbmin)
    ?_ ?_
  · exact (by unfold mixF; fun_prop : Continuous fun u => Real.sqrt (mixF a b u)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mx_sqrt_le a b bmin ha hb (le_of_lt hu)

/-- `0 < 𝖩` (`lem:app-phase-mixture`). -/
lemma mx_J_pos {n : ℕ} (a b : Fin n → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (ha : ∀ i, 0 ≤ a i) (hF0 : 0 < ∑ i, a i) (hb : ∀ i, bmin ≤ b i) :
    0 < mixJ a b := by
  unfold mixJ
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have hsupp : Function.support (fun u => Real.sqrt (mixF a b u)) ∩ Ioi 0 = Ioi 0 := by
      ext u
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_Ioi]
      constructor
      · exact fun h => h.2
      · intro hu
        refine ⟨?_, hu⟩
        exact (Real.sqrt_pos.2 (mx_F_pos a b ha hF0 u)).ne'
    rw [hsupp, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · exact Filter.Eventually.of_forall fun u => Real.sqrt_nonneg _
  · exact mx_sqrt_integrable a b bmin hbmin ha hb

/-- `𝖩 ≤ 2 √F0 / bmin` (`lem:app-phase-mixture`). -/
lemma mx_J_le {n : ℕ} (a b : Fin n → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, bmin ≤ b i) :
    mixJ a b ≤ 2 * Real.sqrt (∑ i, a i) / bmin := by
  unfold mixJ
  have h := mx_bound_integral (bmin := bmin) (c := Real.sqrt (∑ i, a i)) hbmin
  have hle : ∫ u in Ioi (0 : ℝ), Real.sqrt (mixF a b u) ≤
      ∫ u in Ioi (0 : ℝ), Real.sqrt (∑ i, a i) * Real.exp (-(bmin * u) / 2) := by
    refine setIntegral_mono_on (mx_sqrt_integrable a b bmin hbmin ha hb)
      (mx_bound_integrable hbmin) measurableSet_Ioi fun u hu => ?_
    exact mx_sqrt_le a b bmin ha hb (le_of_lt hu)
  rw [h] at hle
  calc _ ≤ _ := hle
    _ = 2 * Real.sqrt (∑ i, a i) / bmin := by ring

/-- Single-exponential embedding bound: `(e^{-bmin(·)/4} ⋆ w c e^{-c ·})(t) ≤ (4/3) w K e^{-bmin t/4}`. -/
lemma mx_gh_single (K w c bmin t : ℝ) (hK : 0 ≤ K) (hw : 0 ≤ w) (hbmin : 0 < bmin)
    (hc : bmin ≤ c) (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, K * Real.exp (-(bmin * (t - s)) / 4) * (w * c * Real.exp (-(c * s)))
      ≤ 4 / 3 * (w * K * Real.exp (-(bmin * t) / 4)) := by
  have hc0 : 0 ≤ c := by linarith
  set d := c - bmin / 4 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  set C := K * w * c * Real.exp (-(bmin * t) / 4) with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (mul_nonneg (mul_nonneg hK hw) hc0) (Real.exp_pos _).le
  have key : ∀ s : ℝ, K * Real.exp (-(bmin * (t - s)) / 4) * (w * c * Real.exp (-(c * s)))
      = C * Real.exp ((-d) * s) := by
    intro s
    have h : Real.exp (-(bmin * (t - s)) / 4) * Real.exp (-(c * s))
        = Real.exp (-(bmin * t) / 4) * Real.exp ((-d) * s) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hd]
      ring
    rw [hC]
    calc K * Real.exp (-(bmin * (t - s)) / 4) * (w * c * Real.exp (-(c * s)))
        = K * w * c * (Real.exp (-(bmin * (t - s)) / 4) * Real.exp (-(c * s))) := by ring
      _ = K * w * c * Real.exp (-(bmin * t) / 4) * Real.exp ((-d) * s) := by rw [h]; ring
  simp_rw [key]
  have hJ : ∫ s in Ioi (0 : ℝ), C * Real.exp ((-d) * s) = C / d := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero]
    field_simp
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun s => C * Real.exp ((-d) * s) :=
    ae_of_all _ fun s => mul_nonneg hCnn (Real.exp_pos _).le
  have hfi : IntegrableOn (fun s => C * Real.exp ((-d) * s)) (Ioi 0) :=
    Integrable.const_mul (exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ) < d)) C
  rw [intervalIntegral.integral_of_le ht]
  calc ∫ s in Ioc (0 : ℝ) t, C * Real.exp ((-d) * s)
      ≤ ∫ s in Ioi (0 : ℝ), C * Real.exp ((-d) * s) :=
        setIntegral_mono_set hfi hnn (Filter.Eventually.of_forall fun x hx => hx.1)
    _ = C / d := hJ
    _ ≤ 4 / 3 * (w * K * Real.exp (-(bmin * t) / 4)) := by
        have hP : 0 ≤ w * K * Real.exp (-(bmin * t) / 4) :=
          mul_nonneg (mul_nonneg hw hK) (Real.exp_pos _).le
        rw [hC, div_le_iff₀ hdpos, hd]
        nlinarith [mul_nonneg hP (sub_nonneg.2 hc)]

lemma mx_conv_h {n' : ℕ} (w c : Fin n' → ℝ) (K bmin : ℝ) (hK : 0 ≤ K) (hbmin : 0 < bmin)
    (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (hc : ∀ l, bmin ≤ c l) {t : ℝ} (ht : 0 ≤ t) :
    oneSidedConv (fun u => K * Real.exp (-(bmin * u) / 4)) (mixG w c) t ≤
      4 / 3 * (K * Real.exp (-(bmin * t) / 4)) := by
  unfold oneSidedConv mixG
  have e1 : ∀ s : ℝ, K * Real.exp (-(bmin * (t - s)) / 4) * ∑ l, w l * c l * Real.exp (-(c l * s))
      = ∑ l, K * Real.exp (-(bmin * (t - s)) / 4) * (w l * c l * Real.exp (-(c l * s))) :=
    fun s => Finset.mul_sum _ _ _
  simp only [e1]
  rw [intervalIntegral.integral_finset_sum (fun l _ => (by fun_prop : Continuous fun s : ℝ =>
    K * Real.exp (-(bmin * (t - s)) / 4) * (w l * c l * Real.exp (-(c l * s)))).intervalIntegrable _ _)]
  calc ∑ l, ∫ s in (0 : ℝ)..t, K * Real.exp (-(bmin * (t - s)) / 4) * (w l * c l * Real.exp (-(c l * s)))
      ≤ ∑ l, 4 / 3 * (w l * K * Real.exp (-(bmin * t) / 4)) :=
        Finset.sum_le_sum fun l _ => mx_gh_single K (w l) (c l) bmin t hK (hw l) hbmin (hc l) ht
    _ = 4 / 3 * (K * Real.exp (-(bmin * t) / 4)) := by
        have : ∑ l, 4 / 3 * (w l * K * Real.exp (-(bmin * t) / 4))
            = 4 / 3 * (K * Real.exp (-(bmin * t) / 4)) * ∑ l, w l := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
        rw [this, hw1, mul_one]

lemma mx_g_term (w c : ℝ) (hw : 0 ≤ w) (hc : 0 < c) :
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

lemma mx_g_int {n' : ℕ} (w c : Fin n' → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (hc : ∀ l, bmin ≤ c l) :
    IntegrableOn (mixG w c) (Ioi 0) ∧ ∫ u in Ioi (0 : ℝ), mixG w c u = 1 := by
  have hcp : ∀ l, 0 < c l := fun l => lt_of_lt_of_le hbmin (hc l)
  refine ⟨?_, ?_⟩
  · unfold mixG
    exact integrable_finset_sum _ fun l _ => (mx_g_term (w l) (c l) (hw l) (hcp l)).1
  · unfold mixG
    rw [integral_finset_sum _ fun l _ => (mx_g_term (w l) (c l) (hw l) (hcp l)).1]
    simp_rw [fun l => (mx_g_term (w l) (c l) (hw l) (hcp l)).2]
    exact hw1

lemma mx_g_nonneg {n' : ℕ} (w c : Fin n' → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (hw : ∀ l, 0 ≤ w l) (hc : ∀ l, bmin ≤ c l) (u : ℝ) : 0 ≤ mixG w c u :=
  Finset.sum_nonneg fun l _ =>
    mul_nonneg (mul_nonneg (hw l) (by linarith [hc l])) (Real.exp_pos _).le

lemma mx_f_shift {n : ℕ} (a b : Fin n → ℝ) (bmin : ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, bmin ≤ b i) {s v : ℝ} (hs : 0 ≤ s) (hsv : s ≤ v) :
    mixF a b v ≤ mixF a b s * Real.exp (-(bmin * (v - s))) := by
  unfold mixF
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : a i * Real.exp (-(b i * v)) = a i * Real.exp (-(b i * s)) * Real.exp (-(b i * (v - s))) := by
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [h1]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (mul_nonneg (ha i) (Real.exp_pos _).le)
  have := mul_le_mul_of_nonneg_right (hb i) (sub_nonneg.2 hsv)
  linarith

lemma mx_quad {d J m I : ℝ} (hd : 0 ≤ d) (hJ : 0 ≤ J) (hm : 0 ≤ m) (hI : I ≤ J + m)
    (hm2 : m ^ 2 = d * I) : I ≤ J + 2 * Real.sqrt (d * J) + d := by
  have hr : m ≤ d + Real.sqrt (d * J) := by
    by_contra hlt
    push_neg at hlt
    have hs := Real.sq_sqrt (mul_nonneg hd hJ)
    have hs0 := Real.sqrt_nonneg (d * J)
    nlinarith [mul_nonneg hd hs0, mul_nonneg hd hJ]
  nlinarith [Real.sqrt_nonneg (d * J)]

lemma mx_sqrt_amgm {D μ : ℝ} (hD : 0 ≤ D) (hμ : 0 < μ) :
    Real.sqrt D ≤ μ / 2 + 1 / (2 * μ) * D := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h : (μ / 2 + 1 / (2 * μ) * D) ^ 2 - D = (μ / 2 - 1 / (2 * μ) * D) ^ 2 := by
    field_simp; ring
  nlinarith [sq_nonneg (μ / 2 - 1 / (2 * μ) * D)]

/-- `lem:app-phase-mixture`, snapshot `cr-2026-10-23`.
Source: `section.tex` l.2111–2127.
LaTeX (verbatim, `section.tex` l.2111–2127):
```
\begin{lemma}[Finite exponential mixtures]\label{lem:app-phase-mixture}
Let $b_{\min}>0$, let
\[
f(u)=\sum_{i=1}^{n}a_ie^{-b_iu},\qquad g(u)=\sum_{l=1}^{n'}w_l\,c_l\,e^{-c_lu},
\]
with $a_i\ge0$, $F_0\defeq\sum_ia_i>0$, $b_i,c_l\ge b_{\min}$, $w_l\ge0$ and
$\sum_lw_l=1$. Let $T\ge4$, $0<\epsilon<F_0/T$, and let $Y>0$ be the continuous
solution of $Y=f+\sqrt\epsilon\,g*\sqrt Y$. Put
\[
\mathsf J\defeq\int_0^\infty\sqrt{f(u)}\,\dif u,\qquad H\defeq\frac2{b_{\min}}\log\frac{F_0}\epsilon,\qquad\mathsf d\defeq\sqrt\epsilon\,H .
\]
Then $0<\mathsf J\le2\sqrt{F_0}/b_{\min}$, the first $T\epsilon$ hit $\hat u$
satisfies $0<\hat u\le H$ and $Y(\hat u)=T\epsilon$, and
\[
\mathsf J-\frac{2\sqrt{T\epsilon}}{b_{\min}}\le\int_0^{\hat u}\sqrt Y\,\dif u\le\mathsf J+2\sqrt{\mathsf d\,\mathsf J}+\mathsf d .
\]
\end{lemma}
```
-/
theorem lem_app_phase_mixture
    {n n' : ℕ} (a b : Fin n → ℝ) (w c : Fin n' → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (ha : ∀ i, 0 ≤ a i) (hF0 : 0 < ∑ i, a i) (hb : ∀ i, bmin ≤ b i)
    (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (hc : ∀ l, bmin ≤ c l)
    {T ε H d : ℝ} (hT : 4 ≤ T) (hε : 0 < ε) (hεF : ε < (∑ i, a i) / T)
    (hH : H = (2 / bmin) * Real.log ((∑ i, a i) / ε)) (hd : d = Real.sqrt ε * H)
    {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Ici 0)) (hYpos : ∀ u ∈ Ici (0 : ℝ), 0 < Y u)
    (hY : ∀ u ∈ Ici (0 : ℝ),
      Y u = mixF a b u + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u) :
    0 < mixJ a b ∧ mixJ a b ≤ 2 * Real.sqrt (∑ i, a i) / bmin ∧
    ∃ û : ℝ, firstHit Y (T * ε) = ENNReal.ofReal û ∧ 0 < û ∧ û ≤ H ∧ Y û = T * ε ∧
      mixJ a b - 2 * Real.sqrt (T * ε) / bmin ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) ∧
      ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) ≤ mixJ a b + 2 * Real.sqrt (d * mixJ a b) + d := by
  have hJpos := mx_J_pos a b bmin hbmin ha hF0 hb
  have hJle := mx_J_le a b bmin hbmin ha hb
  refine ⟨hJpos, hJle, ?_⟩
  set F0 : ℝ := ∑ i, a i with hF0def
  have hF0nn : 0 ≤ F0 := hF0.le
  have hTpos : 0 < T := by linarith
  have hTε : T * ε < F0 := by
    have := (lt_div_iff₀ hTpos).1 hεF
    linarith
  have hεlt : ε < F0 := by nlinarith
  have hLpos : 0 < Real.log (F0 / ε) := Real.log_pos ((one_lt_div hε).2 hεlt)
  have hHpos : 0 < H := by rw [hH]; positivity
  have hbH : bmin * H = 2 * Real.log (F0 / ε) := by
    rw [hH]; field_simp
  set hh : ℝ → ℝ := fun u => Real.sqrt F0 * Real.exp (-(bmin * u) / 4) with hhdef
  have hhnn : ∀ u, 0 ≤ hh u := fun u => mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  have hexp2 : ∀ u : ℝ, Real.exp (-(bmin * u) / 4) ^ 2 = Real.exp (-(bmin * u) / 2) := by
    intro u; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hhsq : ∀ u, hh u ^ 2 = F0 * Real.exp (-(bmin * u) / 2) := by
    intro u
    simp only [hhdef]
    rw [mul_pow, Real.sq_sqrt hF0nn, hexp2]
  have hhH : hh H = Real.sqrt ε := by
    have h1 : hh H ^ 2 = ε := by
      rw [hhsq]
      have : -(bmin * H) / 2 = -Real.log (F0 / ε) := by rw [hbH]; ring
      rw [this, Real.exp_neg, Real.exp_log (div_pos hF0 hε)]
      field_simp
    calc hh H = Real.sqrt (hh H ^ 2) := (Real.sqrt_sq (hhnn H)).symm
      _ = Real.sqrt ε := by rw [h1]
  have hg_c : Continuous (mixG w c) := by unfold mixG; fun_prop
  have hf_c : Continuous (mixF a b) := by unfold mixF; fun_prop
  have hh_c : Continuous hh := by simp only [hhdef]; fun_prop
  have hgn : ∀ u, 0 ≤ mixG w c u := mx_g_nonneg w c bmin hbmin hw hc
  obtain ⟨hgi, hgmass⟩ := mx_g_int w c bmin hbmin hw hw1 hc
  have hf0' : T * ε < mixF a b 0 := by
    have : mixF a b 0 = F0 := by simp [mixF, hF0def]
    rw [this]; exact hTε
  have hh_ge : ∀ u ∈ Icc (0 : ℝ) H, Real.sqrt ε ≤ hh u := by
    intro u hu
    rw [← hhH]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.sqrt_nonneg _)
    have := mul_le_mul_of_nonneg_left hu.2 hbmin.le
    linarith
  have hfh : ∀ u ∈ Icc (0 : ℝ) H, mixF a b u ≤ hh u ^ 2 := by
    intro u hu
    rw [hhsq]
    calc mixF a b u ≤ F0 * Real.exp (-(bmin * u)) := mx_F_le a b bmin ha hb hu.1
      _ ≤ F0 * Real.exp (-(bmin * u) / 2) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hF0nn
        have := mul_nonneg hbmin.le hu.1
        linarith
  have hab : ∀ u ∈ Icc (0 : ℝ) H, oneSidedConv hh (mixG w c) u ≤ 2 * hh u := by
    intro u hu
    have := mx_conv_h w c (Real.sqrt F0) bmin (Real.sqrt_nonneg _) hbmin hw hw1 hc hu.1
    have h2 := hhnn u
    change oneSidedConv (fun u => Real.sqrt F0 * Real.exp (-(bmin * u) / 4)) (mixG w c) u ≤ _ at this
    change _ ≤ 2 * (Real.sqrt F0 * Real.exp (-(bmin * u) / 4))
    simp only [hhdef] at h2
    linarith
  obtain ⟨û, hfirst, hû0, hûH, hYû, -, -, -⟩ := lem_app_phase_square_ii hε hT hHpos
    hg_c.continuousOn (fun u _ => hgn u) hgi hgmass.le hf_c.continuousOn
    (fun u _ => mx_F_nonneg a b ha u) hf0' hYc hYpos hY hh_c.continuousOn hh_ge hhH hfh
    (Or.inl hab)
  refine ⟨û, hfirst, hû0, hûH, hYû, ?_⟩
  have hYge : ∀ u ∈ Ici (0 : ℝ), mixF a b u ≤ Y u := by
    intro u hu
    rw [hY u hu]
    have := aux_osc_nonneg (F := fun v => Real.sqrt (Y v)) (g := mixG w c)
      (fun v _ => Real.sqrt_nonneg _) (fun v _ => hgn v) (Set.mem_Ici.1 hu)
    have := mul_nonneg (Real.sqrt_nonneg ε) this
    linarith
  have hfû : mixF a b û ≤ T * ε := hYû ▸ hYge û (Set.mem_Ici.2 hû0.le)
  have hsY : ContinuousOn (fun u => Real.sqrt (Y u)) (Ici 0) := hYc.sqrt
  have hsf_c : Continuous (fun u => Real.sqrt (mixF a b u)) := hf_c.sqrt
  have hsY_ii : IntervalIntegrable (fun u => Real.sqrt (Y u)) volume 0 û :=
    (hsY.mono (Icc_subset_Ici_self)).intervalIntegrable_of_Icc hû0.le
  have hsf_ii : IntervalIntegrable (fun u => Real.sqrt (mixF a b u)) volume 0 û :=
    hsf_c.intervalIntegrable _ _
  have hsfI := mx_sqrt_integrable a b bmin hbmin ha hb
  have hsplit := cr_split hû0.le hsfI
  have htail_nn : 0 ≤ ∫ v in Ioi û, Real.sqrt (mixF a b v) :=
    setIntegral_nonneg measurableSet_Ioi fun v _ => Real.sqrt_nonneg _
  have hA_le_I : ∫ u in (0 : ℝ)..û, Real.sqrt (mixF a b u) ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) :=
    intervalIntegral.integral_mono_on hû0.le hsf_ii hsY_ii fun u hu =>
      Real.sqrt_le_sqrt (hYge u (Set.mem_Ici.2 hu.1))
  constructor
  · -- lower bound
    have htail : ∫ v in Ioi û, Real.sqrt (mixF a b v) ≤ Real.sqrt (T * ε) * (2 / bmin) := by
      have hIc := integrableOn_exp_mul_Ioi (a := -(bmin / 2)) (by linarith) û
      set K : ℝ := Real.sqrt (T * ε) * Real.exp ((bmin / 2) * û) with hK
      have hB : IntegrableOn (fun v : ℝ => K * Real.exp (-(bmin / 2) * v)) (Ioi û) :=
        hIc.const_mul K
      have hle : ∫ v in Ioi û, Real.sqrt (mixF a b v) ≤
          ∫ v in Ioi û, K * Real.exp (-(bmin / 2) * v) := by
        refine setIntegral_mono_on (hsfI.mono_set (Ioi_subset_Ioi hû0.le)) hB measurableSet_Ioi
          fun v hv => ?_
        have hv' : û ≤ v := hv.le
        have e1 : K * Real.exp (-(bmin / 2) * v)
            = Real.sqrt (T * ε) * Real.exp (-(bmin / 2) * (v - û)) := by
          rw [hK, mul_assoc, ← Real.exp_add]; congr 2; ring
        have e2 : Real.exp (-(bmin / 2) * (v - û)) ^ 2 = Real.exp (-(bmin * (v - û))) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        have hTε0 : 0 ≤ T * ε := by positivity
        rw [e1, Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        rw [mul_pow, Real.sq_sqrt hTε0, e2]
        calc mixF a b v ≤ mixF a b û * Real.exp (-(bmin * (v - û))) :=
              mx_f_shift a b bmin ha hb hû0.le hv'
          _ ≤ T * ε * Real.exp (-(bmin * (v - û))) :=
              mul_le_mul_of_nonneg_right hfû (Real.exp_pos _).le
      have hval : ∫ v in Ioi û, K * Real.exp (-(bmin / 2) * v) = Real.sqrt (T * ε) * (2 / bmin) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) û]
        have hEE : Real.exp ((bmin / 2) * û) * Real.exp (-(bmin / 2) * û) = 1 := by
          rw [← Real.exp_add]; simp
        rw [hK]
        have h2 : Real.sqrt (T * ε) * Real.exp ((bmin / 2) * û) *
            (-Real.exp (-(bmin / 2) * û) / (-(bmin / 2))) = Real.sqrt (T * ε) * (2 / bmin) *
            (Real.exp ((bmin / 2) * û) * Real.exp (-(bmin / 2) * û)) := by
          field_simp
        rw [h2, hEE, mul_one]
      linarith
    have : 2 * Real.sqrt (T * ε) / bmin = Real.sqrt (T * ε) * (2 / bmin) := by ring
    unfold mixJ
    linarith
  · -- upper bound
    set I : ℝ := ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) with hI
    have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hû0.le fun u _ => Real.sqrt_nonneg _
    have hA_le_J : ∫ u in (0 : ℝ)..û, Real.sqrt (mixF a b u) ≤ mixJ a b := by
      unfold mixJ; linarith
    have hdpos : 0 < d := by rw [hd]; exact mul_pos (Real.sqrt_pos.2 hε) hHpos
    have hJ0 : 0 ≤ mixJ a b := hJpos.le
    obtain ⟨D, hDdef⟩ : ∃ D : ℝ → ℝ, D = fun u => Y u - mixF a b u := ⟨_, rfl⟩
    have hD_c : ContinuousOn D (Ici 0) := by
      rw [hDdef]; exact hYc.sub hf_c.continuousOn
    have hD_ii : IntervalIntegrable D volume 0 û :=
      (hD_c.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hû0.le
    have hmass : ∫ s in (0 : ℝ)..û, mixG w c s ≤ 1 := by
      rw [intervalIntegral.integral_of_le hû0.le]
      calc ∫ s in Ioc (0 : ℝ) û, mixG w c s ≤ ∫ s in Ioi (0 : ℝ), mixG w c s :=
            setIntegral_mono_set hgi (ae_of_all _ fun s => hgn s)
              (Filter.Eventually.of_forall fun x hx => hx.1)
        _ = 1 := hgmass
    have hC : ∫ u in (0 : ℝ)..û, oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u ≤ I := by
      have hf_int : ∀ T' : ℝ, IntegrableOn (fun v => Real.sqrt (Y v)) (Ioc 0 T') := by
        intro T'
        rcases le_or_gt T' 0 with h0 | h0
        · rw [Ioc_eq_empty (not_lt.2 h0)]; exact integrableOn_empty
        · exact (((hsY.mono Icc_subset_Ici_self).integrableOn_Icc :
            IntegrableOn (fun v => Real.sqrt (Y v)) (Icc 0 T'))).mono_set Ioc_subset_Icc_self
      rw [integral_oneSidedConv_eq hf_int hg_c.continuousOn hû0.le]
      by_cases hint : IntervalIntegrable
          (fun s => mixG w c s * ∫ v in (0 : ℝ)..(û - s), Real.sqrt (Y v)) volume 0 û
      · have hgii : IntervalIntegrable (fun s => mixG w c s * I) volume 0 û :=
          (hg_c.mul continuous_const).intervalIntegrable _ _
        calc ∫ s in (0 : ℝ)..û, mixG w c s * ∫ v in (0 : ℝ)..(û - s), Real.sqrt (Y v)
            ≤ ∫ s in (0 : ℝ)..û, mixG w c s * I := by
              refine intervalIntegral.integral_mono_on hû0.le hint hgii fun s hs => ?_
              refine mul_le_mul_of_nonneg_left ?_ (hgn s)
              have h1 : IntervalIntegrable (fun v => Real.sqrt (Y v)) volume 0 (û - s) :=
                (hsY.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc (by linarith [hs.2])
              have h2 : IntervalIntegrable (fun v => Real.sqrt (Y v)) volume (û - s) û :=
                (hsY.mono (fun v hv => Set.mem_Ici.2 (by linarith [hv.1, hs.2]))).intervalIntegrable_of_Icc
                  (by linarith [hs.1])
              have hsum := intervalIntegral.integral_add_adjacent_intervals h1 h2
              rw [← hI] at hsum
              have nn : 0 ≤ ∫ v in (û - s)..û, Real.sqrt (Y v) :=
                intervalIntegral.integral_nonneg (by linarith [hs.1]) fun v _ => Real.sqrt_nonneg _
              linarith
          _ = (∫ s in (0 : ℝ)..û, mixG w c s) * I := intervalIntegral.integral_mul_const _ _
          _ ≤ 1 * I := mul_le_mul_of_nonneg_right hmass hI0
          _ = I := one_mul _
      · rw [intervalIntegral.integral_undef hint]; exact hI0
    have hDint : ∫ u in (0 : ℝ)..û, D u = Real.sqrt ε *
        ∫ u in (0 : ℝ)..û, oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hû0.le] at hu
      have := hY u (Set.mem_Ici.2 hu.1)
      simp only [hDdef]
      linarith
    have key : ∀ μ : ℝ, 0 < μ → I ≤ mixJ a b + (μ * û + Real.sqrt ε * I / μ) / 2 := by
      intro μ hμ
      have hpt : ∀ u ∈ Icc (0 : ℝ) û,
          Real.sqrt (Y u) ≤ Real.sqrt (mixF a b u) + (μ / 2 + 1 / (2 * μ) * D u) := by
        intro u hu
        have hYu := hYge u (Set.mem_Ici.2 hu.1)
        have h1 := Muon.Foundations.sqrt_sub_sqrt_le (mx_F_nonneg a b ha u) hYu
        have h2 := mx_sqrt_amgm (D := Y u - mixF a b u) (sub_nonneg.2 hYu) hμ
        have e : D u = Y u - mixF a b u := by rw [hDdef]
        rw [e]
        linarith
      have hc_ii : IntervalIntegrable (fun u => μ / 2 + 1 / (2 * μ) * D u) volume 0 û :=
        intervalIntegrable_const.add (hD_ii.const_mul _)
      have hii : IntervalIntegrable
          (fun u => Real.sqrt (mixF a b u) + (μ / 2 + 1 / (2 * μ) * D u)) volume 0 û :=
        hsf_ii.add hc_ii
      have h1 := intervalIntegral.integral_mono_on hû0.le hsY_ii hii hpt
      rw [intervalIntegral.integral_add hsf_ii hc_ii,
        intervalIntegral.integral_add intervalIntegrable_const (hD_ii.const_mul _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hDint] at h1
      simp only [smul_eq_mul, sub_zero] at h1
      have h3 : 1 / (2 * μ) * (Real.sqrt ε *
          ∫ u in (0 : ℝ)..û, oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u)
          ≤ 1 / (2 * μ) * (Real.sqrt ε * I) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC (Real.sqrt_nonneg _)) (by positivity)
      have e : (μ * û + Real.sqrt ε * I / μ) / 2 = μ / 2 * û + 1 / (2 * μ) * (Real.sqrt ε * I) := by
        field_simp
      rw [e]
      linarith
    by_cases hIle : I ≤ 0
    · have := Real.sqrt_nonneg (d * mixJ a b)
      linarith
    · push_neg at hIle
      obtain ⟨l, hl⟩ : ∃ l : ℝ, l = Real.sqrt (I / d) := ⟨_, rfl⟩
      have hlpos : 0 < l := by rw [hl]; exact Real.sqrt_pos.2 (div_pos hIle hdpos)
      have hl2 : I = l ^ 2 * d := by
        have := Real.sq_sqrt (div_pos hIle hdpos).le
        rw [← hl] at this
        rw [this]; field_simp
      have hsε := Real.sqrt_pos.2 hε
      have hkey := key (l * Real.sqrt ε) (by positivity)
      have hû' : Real.sqrt ε * û ≤ d := by
        rw [hd]; exact mul_le_mul_of_nonneg_left hûH hsε.le
      have e1 : Real.sqrt ε * I / (l * Real.sqrt ε) = l * d := by
        rw [div_eq_iff (by positivity), hl2]; ring
      have e2 : l * Real.sqrt ε * û = l * (Real.sqrt ε * û) := by ring
      have h4 : l * (Real.sqrt ε * û) ≤ l * d := mul_le_mul_of_nonneg_left hû' hlpos.le
      have hIm : I ≤ mixJ a b + l * d := by
        rw [e1, e2] at hkey
        linarith
      exact mx_quad hdpos.le hJ0 (by positivity) hIm (by rw [mul_pow, hl2]; ring)

/-- The mixture equation `Y = f + √ε g*√Y` on `[0,∞)` with `Y` continuous and positive
(`lem:app-phase-mixture`, source l.2116–2117). -/
def IsMixtureSol {n n' : ℕ} (a b : Fin n → ℝ) (w c : Fin n' → ℝ) (ε : ℝ) (Y : ℝ → ℝ) : Prop :=
  ContinuousOn Y (Ici 0) ∧ (∀ u ∈ Ici (0 : ℝ), 0 < Y u) ∧
    ∀ u ∈ Ici (0 : ℝ),
      Y u = mixF a b u + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u

/-- `lem:app-phase-mixture`, existence and uniqueness of the solution `Y`, snapshot `cr-2026-10-23`.
Source: `section.tex` l.2116–2117 (the definite description "the continuous solution") and
l.2130–2131 (proof: existence and uniqueness by `thm:app-phase-volterra`).
LaTeX (verbatim, `section.tex` l.2116–2117 and l.2130–2131):
```
$\sum_lw_l=1$. Let $T\ge4$, $0<\epsilon<F_0/T$, and let $Y>0$ be the continuous
solution of $Y=f+\sqrt\epsilon\,g*\sqrt Y$. Put
The equation has a unique positive continuous solution by
\cref{thm:app-phase-volterra}, applied with the rates $b_i$ and $c_l$ and
```
-/
theorem lem_app_phase_mixture_solution
    {n n' : ℕ} (a b : Fin n → ℝ) (w c : Fin n' → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (ha : ∀ i, 0 ≤ a i) (hF0 : 0 < ∑ i, a i) (hb : ∀ i, bmin ≤ b i)
    (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (hc : ∀ l, bmin ≤ c l)
    {T ε : ℝ} (hT : 4 ≤ T) (hε : 0 < ε) (hεF : ε < (∑ i, a i) / T) :
    ∃ Y : ℝ → ℝ, IsMixtureSol a b w c ε Y ∧
      ∀ Y' : ℝ → ℝ, IsMixtureSol a b w c ε Y' → EqOn Y' Y (Ici 0) := by
  have hb0 : ∀ i, 0 < b i := fun i => lt_of_lt_of_le hbmin (hb i)
  have hc0 : ∀ l, 0 < c l := fun l => lt_of_lt_of_le hbmin (hc l)
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  -- the row model with rates `b_i/2`, `c_l/2`, zero coefficients on the other block
  let M : RowModel (Fin n ⊕ Fin n') :=
    { μ := fun _ => 1
      d := Sum.elim (fun i => b i / 2) (fun l => c l / 2)
      v := Sum.elim (fun _ => 0) (fun l => 2 * Real.sqrt ε * (w l * c l))
      Q0 := Sum.elim (fun i => 2 * a i) (fun _ => 0)
      η := 1
      μ_pos := fun _ => one_pos
      d_pos := by
        rintro (i | l)
        · exact half_pos (hb0 i)
        · exact half_pos (hc0 l)
      v_nonneg := by
        rintro (i | l)
        · exact le_refl _
        · exact mul_nonneg (mul_nonneg (by norm_num) hsε.le) (mul_nonneg (hw l) (hc0 l).le)
      Q0_nonneg := by
        rintro (i | l)
        · exact mul_nonneg (by norm_num) (ha i)
        · exact le_refl _
      η_pos := one_pos
      summable_μQ0 := Summable.of_finite
      F0_pos := by
        simp only [tsum_fintype, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul,
          Finset.sum_const_zero, add_zero]
        rw [← Finset.mul_sum]
        linarith
      summable_S := Summable.of_finite }
  have hFM : ∀ s, M.forcing s = mixF a b s := by
    intro s
    simp only [RowModel.forcing, M, tsum_fintype, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, mixF, one_mul, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show -(2 * (b i / 2) * s) = -(b i * s) by ring]
    ring
  have hKM : M.kernel = fun s => Real.sqrt ε * mixG w c s := by
    funext s
    simp only [RowModel.kernel, M, tsum_fintype, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, mixG, one_mul, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show -(2 * (c l / 2) * s) = -(c l * s) by ring]
    ring
  have hosc : ∀ (f : ℝ → ℝ) (t : ℝ), oneSidedConv f (fun s => Real.sqrt ε * mixG w c s) t
      = Real.sqrt ε * oneSidedConv f (mixG w c) t := by
    intro f t
    unfold oneSidedConv
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun s _ => by dsimp only; ring
  have hmixG : ∀ u, 0 ≤ mixG w c u := fun u => by
    unfold mixG
    exact Finset.sum_nonneg fun l _ => mul_nonneg (mul_nonneg (hw l) (hc0 l).le) (Real.exp_pos _).le
  have hmixF_pos : ∀ u ∈ Ici (0 : ℝ), 0 < mixF a b u := by
    intro u _
    obtain ⟨i, hi⟩ : ∃ i, 0 < a i := by
      by_contra h
      push_neg at h
      exact absurd hF0 (not_lt.2 (Finset.sum_nonpos fun i _ => h i))
    unfold mixF
    exact Finset.sum_pos' (fun j _ => mul_nonneg (ha j) (Real.exp_pos _).le)
      ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩
  have hmix_V : ∀ Y : ℝ → ℝ, IsMixtureSol a b w c ε Y → IsVolterraSol M Y := by
    intro Y hY
    obtain ⟨hc', hp, he⟩ := hY
    refine ⟨hc', fun s hs => (hp s hs).le, fun s hs => ?_⟩
    have h := he s hs
    rw [hFM, hKM, hosc]
    exact h
  have hV_mix : ∀ Y : ℝ → ℝ, IsVolterraSol M Y → (∀ u ∈ Ici (0 : ℝ), 0 < Y u) →
      IsMixtureSol a b w c ε Y := by
    intro Y hY hpos
    obtain ⟨hc', _, he⟩ := hY
    refine ⟨hc', hpos, fun s hs => ?_⟩
    have h := he s hs
    rw [hFM, hKM, hosc] at h
    exact h
  obtain ⟨Q, hQ, hQu⟩ := thm_app_phase_volterra_i M
  obtain ⟨hQc, _, hQe⟩ := hQ
  have hkern : ∀ u ∈ Ici (0 : ℝ), 0 ≤ M.kernel u := fun u _ => by
    rw [hKM]
    exact mul_nonneg hsε.le (hmixG u)
  have hQpos : ∀ u ∈ Ici (0 : ℝ), 0 < Q u := by
    intro u hu
    have h1 := hQe u hu
    rw [hFM] at h1
    have h2 := aux_osc_nonneg (F := fun u => Real.sqrt (Q u)) (fun _ _ => Real.sqrt_nonneg _)
      hkern hu
    linarith [hmixF_pos u hu]
  refine ⟨Q, hV_mix Q ⟨hQc, fun s hs => (hQpos s hs).le, hQe⟩ hQpos, fun Y' hY' => ?_⟩
  intro s hs
  exact hQu Y' (hmix_V Y' hY') s hs

/-! ## Two finite forcing integrals: private helpers (P-H.6.P6) -/

lemma fi_tail_pt {p q : ℝ} (N : ℕ) (hN : 1 ≤ N) (hq : 0 ≤ q) {u : ℝ}
    (hu : (N : ℝ) ^ q ≤ u) :
    fNq (N : ℕ∞) p q u ≤ fNq (N : ℕ∞) p q ((N : ℝ) ^ q)
      * Real.exp (-(2 * (u - (N : ℝ) ^ q) / (N : ℝ) ^ q)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLpos : 0 < (N : ℝ) ^ q := Real.rpow_pos_of_pos hNpos q
  have h2 : 0 ≤ 2 * (u - (N : ℝ) ^ q) := by linarith
  have e : 2 * (u - (N : ℝ) ^ q) / (N : ℝ) ^ q
      = 2 * (u - (N : ℝ) ^ q) * (1 / (N : ℝ) ^ q) := by ring
  rw [e]
  have hterm : ∀ i ∈ Finset.Icc 1 N,
      (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q))
        ≤ Real.exp (-(2 * (u - (N : ℝ) ^ q) * (1 / (N : ℝ) ^ q)))
          * ((i : ℝ) ^ (-p) * Real.exp (-(2 * (N : ℝ) ^ q) * (i : ℝ) ^ (-q))) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
    have hiN : (i : ℝ) ≤ N := by exact_mod_cast hi.2
    have ht : 1 / (N : ℝ) ^ q ≤ (i : ℝ) ^ (-q) := by
      have h1 : (N : ℝ) ^ (-q) ≤ (i : ℝ) ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos hi0 hiN (by linarith)
      rw [Real.rpow_neg hNpos.le] at h1
      rw [one_div]
      exact h1
    have hm : 2 * (u - (N : ℝ) ^ q) * (1 / (N : ℝ) ^ q)
        ≤ 2 * (u - (N : ℝ) ^ q) * (i : ℝ) ^ (-q) :=
      mul_le_mul_of_nonneg_left ht h2
    have heq : Real.exp (-(2 * u) * (i : ℝ) ^ (-q))
        = Real.exp (-(2 * (N : ℝ) ^ q) * (i : ℝ) ^ (-q))
          * Real.exp (-(2 * (u - (N : ℝ) ^ q)) * (i : ℝ) ^ (-q)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hle : Real.exp (-(2 * (u - (N : ℝ) ^ q)) * (i : ℝ) ^ (-q))
        ≤ Real.exp (-(2 * (u - (N : ℝ) ^ q) * (1 / (N : ℝ) ^ q))) :=
      Real.exp_le_exp.2 (by linarith)
    have hp0 : 0 ≤ (i : ℝ) ^ (-p) := Real.rpow_nonneg hi0.le _
    rw [heq]
    calc (i : ℝ) ^ (-p) * (Real.exp (-(2 * (N : ℝ) ^ q) * (i : ℝ) ^ (-q))
          * Real.exp (-(2 * (u - (N : ℝ) ^ q)) * (i : ℝ) ^ (-q)))
        ≤ (i : ℝ) ^ (-p) * (Real.exp (-(2 * (N : ℝ) ^ q) * (i : ℝ) ^ (-q))
          * Real.exp (-(2 * (u - (N : ℝ) ^ q) * (1 / (N : ℝ) ^ q)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le) hp0
      _ = _ := by ring
  unfold fNq
  rw [fl_eq_sum, fl_eq_sum]
  have key := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at key
  have h12 := mul_le_mul_of_nonneg_left key (by norm_num : (0:ℝ) ≤ 1 / 2)
  linarith

lemma fi_sqrt_tail_pt {p q : ℝ} (N : ℕ) (hN : 1 ≤ N) (hq : 0 ≤ q) {u : ℝ}
    (hu : (N : ℝ) ^ q ≤ u) :
    Real.sqrt (fNq (N : ℕ∞) p q u) ≤ Real.sqrt (fNq (N : ℕ∞) p q ((N : ℝ) ^ q))
      * Real.exp (-((u - (N : ℝ) ^ q) / (N : ℝ) ^ q)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLnn : (0 : ℝ) ≤ (N : ℝ) ^ q := Real.rpow_nonneg hNpos.le q
  have hL := fi_tail_pt (p := p) N hN hq hu
  have hf0 : 0 ≤ fNq (N : ℕ∞) p q ((N : ℝ) ^ q) := by
    have h1 := cr_lower_f (p := p) (q := q) N hN hLnn
    have h2 : 0 < (1 / 2 : ℝ) * Real.exp (-(2 * (N : ℝ) ^ q)) := by positivity
    linarith
  have hE : Real.exp (-(2 * (u - (N : ℝ) ^ q) / (N : ℝ) ^ q))
      = Real.exp (-((u - (N : ℝ) ^ q) / (N : ℝ) ^ q)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc Real.sqrt (fNq (N : ℕ∞) p q u)
      ≤ Real.sqrt (fNq (N : ℕ∞) p q ((N : ℝ) ^ q)
          * Real.exp (-(2 * (u - (N : ℝ) ^ q) / (N : ℝ) ^ q))) := Real.sqrt_le_sqrt hL
    _ = _ := by rw [hE, Real.sqrt_mul hf0, Real.sqrt_sq (Real.exp_pos _).le]

lemma fi_tail_dom {p q : ℝ} (N : ℕ) (hN : 1 ≤ N) (hq : 0 ≤ q) {u : ℝ}
    (hu : (N : ℝ) ^ q ≤ u) :
    Real.sqrt (fNq (N : ℕ∞) p q u)
      ≤ Real.sqrt (fNq (N : ℕ∞) p q ((N : ℝ) ^ q)) * Real.exp 1
          * Real.exp (-(1 / (N : ℝ) ^ q) * u) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLpos : 0 < (N : ℝ) ^ q := Real.rpow_pos_of_pos hNpos q
  have hL0 : (N : ℝ) ^ q ≠ 0 := hLpos.ne'
  have hx : -((u - (N : ℝ) ^ q) / (N : ℝ) ^ q) = 1 + (-(1 / (N : ℝ) ^ q) * u) := by
    field_simp; ring
  calc Real.sqrt (fNq (N : ℕ∞) p q u)
      ≤ Real.sqrt (fNq (N : ℕ∞) p q ((N : ℝ) ^ q)) * Real.exp (-((u - (N : ℝ) ^ q) / (N : ℝ) ^ q)) :=
        fi_sqrt_tail_pt (p := p) N hN hq hu
    _ = _ := by rw [hx, Real.exp_add]; ring

lemma fi_tail_int {p q : ℝ} (N : ℕ) (hN : 1 ≤ N) (hq : 0 ≤ q) :
    IntegrableOn (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q u)) (Ioi ((N : ℝ) ^ q)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLpos : 0 < (N : ℝ) ^ q := Real.rpow_pos_of_pos hNpos q
  have hb : (0 : ℝ) < 1 / (N : ℝ) ^ q := by positivity
  have hint : IntegrableOn (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q ((N : ℝ) ^ q)) * Real.exp 1
      * Real.exp (-(1 / (N : ℝ) ^ q) * u)) (Ioi ((N : ℝ) ^ q)) :=
    Integrable.const_mul (exp_neg_integrableOn_Ioi ((N : ℝ) ^ q) hb) _
  have hmeas : AEStronglyMeasurable (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q u))
      (volume.restrict (Ioi ((N : ℝ) ^ q))) :=
    ((fl_cont N p q).sqrt).aestronglyMeasurable
  refine Integrable.mono' hint hmeas (ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => ?_))
  have hu' : (N : ℝ) ^ q ≤ u := le_of_lt hu
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact fi_tail_dom (p := p) N hN hq hu'

lemma fi_tail_le {p q : ℝ} (N : ℕ) (hN : 1 ≤ N) (hq : 0 ≤ q) :
    ∫ u in Ioi ((N : ℝ) ^ q), Real.sqrt (fNq (N : ℕ∞) p q u)
      ≤ (N : ℝ) ^ q * Real.sqrt (fNq (N : ℕ∞) p q ((N : ℝ) ^ q)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLpos : 0 < (N : ℝ) ^ q := Real.rpow_pos_of_pos hNpos q
  have hb : (0 : ℝ) < 1 / (N : ℝ) ^ q := by positivity
  have hI : ∫ u in Ioi ((N : ℝ) ^ q), Real.exp (-(1 / (N : ℝ) ^ q) * u)
      = (N : ℝ) ^ q * Real.exp (-1) := by
    have h := integral_comp_mul_left_Ioi (fun y : ℝ => Real.exp (-y)) ((N : ℝ) ^ q) hb
    rw [show 1 / (N : ℝ) ^ q * (N : ℝ) ^ q = 1 by field_simp, integral_exp_neg_Ioi] at h
    simp only [neg_mul]
    rw [h, smul_eq_mul, one_div, inv_inv]
  have hee : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
  have hg : IntegrableOn (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q ((N : ℝ) ^ q)) * Real.exp 1
      * Real.exp (-(1 / (N : ℝ) ^ q) * u)) (Ioi ((N : ℝ) ^ q)) :=
    Integrable.const_mul (exp_neg_integrableOn_Ioi ((N : ℝ) ^ q) hb) _
  calc ∫ u in Ioi ((N : ℝ) ^ q), Real.sqrt (fNq (N : ℕ∞) p q u)
      ≤ ∫ u in Ioi ((N : ℝ) ^ q), Real.sqrt (fNq (N : ℕ∞) p q ((N : ℝ) ^ q)) * Real.exp 1
          * Real.exp (-(1 / (N : ℝ) ^ q) * u) :=
        setIntegral_mono_on (fi_tail_int (p := p) N hN hq) hg measurableSet_Ioi
          (fun u hu => fi_tail_dom (p := p) N hN hq (le_of_lt hu))
    _ = (Real.sqrt (fNq (N : ℕ∞) p q ((N : ℝ) ^ q)) * Real.exp 1) * ((N : ℝ) ^ q * Real.exp (-1)) := by
        rw [integral_const_mul, hI]
    _ = (N : ℝ) ^ q * Real.sqrt (fNq (N : ℕ∞) p q ((N : ℝ) ^ q)) := by
        linear_combination (Real.sqrt (fNq (N : ℕ∞) p q ((N : ℝ) ^ q)) * (N : ℝ) ^ q) * hee

lemma fi_int0 {p q : ℝ} (N : ℕ) (hN : 1 ≤ N) (hq : 0 ≤ q) :
    IntegrableOn (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q u)) (Ioi 0) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLnn : (0 : ℝ) ≤ (N : ℝ) ^ q := Real.rpow_nonneg hNpos.le q
  have h1 : IntegrableOn (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q u))
      (Ioc 0 ((N : ℝ) ^ q)) :=
    ((fl_cont N p q).sqrt.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [← Set.Ioc_union_Ioi_eq_Ioi hLnn]
  exact h1.union (fi_tail_int (p := p) N hN hq)

lemma fi_split {p q : ℝ} (N : ℕ) (hN : 1 ≤ N) (hq : 0 ≤ q) {a : ℝ} (ha : 0 ≤ a) :
    JN N p q = (∫ u in (0 : ℝ)..a, Real.sqrt (fNq (N : ℕ∞) p q u))
      + ∫ u in Ioi a, Real.sqrt (fNq (N : ℕ∞) p q u) := by
  unfold JN
  exact cr_split ha (fi_int0 (p := p) N hN hq)

lemma fi_env {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (N : ℕ) (hN : 1 ≤ N) {u : ℝ}
    (hu : 0 ≤ u) :
    Real.sqrt (fNq (N : ℕ∞) p q u) ≤ Cpq p q * (u + 1) ^ (-rq p q) :=
  le_trans (Real.sqrt_le_sqrt (by linarith [(ck_diff (q := q) hp N hN hu).1])) (cr_env hp hq hu)

lemma fi_rpow_int {r x : ℝ} (hx : 0 ≤ x) (hr : r ≠ -1) :
    ∫ u in (0 : ℝ)..x, (u + 1) ^ r = ((x + 1) ^ (r + 1) - 1) / (r + 1) := by
  have h := intervalIntegral.integral_comp_add_right (fun y : ℝ => y ^ r) (a := 0) (b := x) (1 : ℝ)
  simp only [zero_add] at h
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (x + 1) := by
    rw [Set.uIcc_of_le (show (1 : ℝ) ≤ x + 1 by linarith)]
    intro h0
    linarith [h0.1]
  rw [h, integral_rpow (Or.inr ⟨hr, h0⟩), Real.one_rpow]

lemma fi_rpow_ii {r x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (fun u : ℝ => (u + 1) ^ r) volume 0 x := by
  have hc : ContinuousOn (fun u : ℝ => u + 1) (Set.uIcc 0 x) :=
    continuousOn_id.add continuousOn_const
  refine ContinuousOn.intervalIntegrable (ContinuousOn.rpow_const hc ?_)
  intro u hu
  left
  rw [Set.uIcc_of_le hx] at hu
  show u + 1 ≠ 0
  exact ne_of_gt (by linarith [hu.1])

lemma fi_int_isqrt {x : ℝ} (hx : 0 ≤ x) :
    ∫ u in (0 : ℝ)..x, (u + 1) ^ (-(1 / 2 : ℝ)) = 2 * (Real.sqrt (x + 1) - 1) := by
  rw [fi_rpow_int hx (by norm_num)]
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
  ring

lemma fi_inf_log {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : rq p q = 1) {L : ℝ}
    (hL : 1 ≤ L) :
    |(∫ u in (0 : ℝ)..L, Real.sqrt (fNq ⊤ p q u)) - aQ q * Real.log L|
      ≤ Cpq p q + q * Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q := by
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have haQ := ck_aQ_pos hq
  have hM : 0 ≤ Mpq p q := by
    unfold Mpq; apply Real.rpow_nonneg; apply div_nonneg (by linarith)
    exact mul_nonneg (Real.exp_pos 1).le hq.le
  have hK0 : 0 ≤ Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q :=
    div_nonneg (mul_nonneg hM (Real.rpow_nonneg (by norm_num) _)) haQ.le
  have hqK : q * Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q
      = q * (Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q) := by ring
  rw [hqK]
  set K : ℝ := Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q with hKdef
  have hI01 : IntervalIntegrable (fun u => Real.sqrt (fNq ⊤ p q u)) volume 0 1 :=
    ck_int_sqrt (q := q) hp le_rfl zero_le_one
  have hI1L : IntervalIntegrable (fun u => Real.sqrt (fNq ⊤ p q u)) volume 1 L :=
    ck_int_sqrt (q := q) hp zero_le_one hL0
  rw [← intervalIntegral.integral_add_adjacent_intervals hI01 hI1L]
  have hA0 : 0 ≤ ∫ u in (0 : ℝ)..1, Real.sqrt (fNq ⊤ p q u) :=
    intervalIntegral.integral_nonneg zero_le_one (fun u _ => Real.sqrt_nonneg _)
  have hA1 : ∫ u in (0 : ℝ)..1, Real.sqrt (fNq ⊤ p q u) ≤ Cpq p q := by
    have h := intervalIntegral.integral_mono_on (zero_le_one : (0 : ℝ) ≤ 1) hI01
      (intervalIntegrable_const (c := Cpq p q))
      (fun u hu => ck_sqrt_le hp hq hu.1)
    simpa using h
  have hinv : IntervalIntegrable (fun u : ℝ => aQ q / u) volume 1 L := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro u hu
    rw [Set.uIcc_of_le hL] at hu
    show u ≠ 0
    exact ne_of_gt (by linarith [hu.1])
  have hint_eq : ∫ u in (1 : ℝ)..L, aQ q / u = aQ q * Real.log L := by
    have hf : (fun u : ℝ => aQ q / u) = fun u => aQ q * u⁻¹ :=
      funext fun u => div_eq_mul_inv _ _
    rw [hf, intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos (by linarith), div_one]
  have hsub : ∫ u in (1 : ℝ)..L, (Real.sqrt (fNq ⊤ p q u) - aQ q / u)
      = (∫ u in (1 : ℝ)..L, Real.sqrt (fNq ⊤ p q u)) - aQ q * Real.log L := by
    rw [intervalIntegral.integral_sub hI1L hinv, hint_eq]
  have hr' : (-1 - 1 / q) ≠ -1 := by
    intro h
    have h2 : 1 / q = 0 := by linarith
    exact (one_div_pos.mpr hq).ne' h2
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) L := by
    rw [Set.uIcc_of_le hL]
    intro h
    linarith [h.1]
  have hval : ∫ u in (1 : ℝ)..L, u ^ (-1 - 1 / q) = (L ^ (-(1 / q)) - 1) / (-(1 / q)) := by
    rw [integral_rpow (Or.inr ⟨hr', h0⟩), Real.one_rpow,
      show (-1 - 1 / q + 1) = -(1 / q) by ring]
  have hbnd : (L ^ (-(1 / q)) - 1) / (-(1 / q)) ≤ q := by
    have hy : 0 ≤ L ^ (-(1 / q)) := Real.rpow_nonneg hL0 _
    have e : (L ^ (-(1 / q)) - 1) / (-(1 / q)) = q * (1 - L ^ (-(1 / q))) := by
      field_simp
      ring
    rw [e]
    nlinarith
  have hcont : ContinuousOn (fun u : ℝ => u ^ (-1 - 1 / q)) (Set.uIcc 1 L) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro u hu
    left
    rw [Set.uIcc_of_le hL] at hu
    show u ≠ 0
    exact ne_of_gt (by linarith [hu.1])
  have hg_int : IntervalIntegrable (fun u : ℝ => K * u ^ (-1 - 1 / q)) volume 1 L :=
    (hcont.intervalIntegrable).const_mul K
  have hmain : ‖∫ u in (1 : ℝ)..L, (Real.sqrt (fNq ⊤ p q u) - aQ q / u)‖
      ≤ ∫ u in (1 : ℝ)..L, K * u ^ (-1 - 1 / q) :=
    intervalIntegral.norm_integral_le_of_norm_le hL
      (ae_of_all _ (fun u hu => by
        rw [Real.norm_eq_abs]
        exact ck_sqrt_asym hp hq hr (le_of_lt hu.1)))
      hg_int
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, hval] at hmain
  have hbound : |∫ u in (1 : ℝ)..L, (Real.sqrt (fNq ⊤ p q u) - aQ q / u)| ≤ q * K := by
    have := mul_le_mul_of_nonneg_left hbnd hK0
    nlinarith
  obtain ⟨hB1, hB2⟩ := abs_le.mp hbound
  rw [abs_le]
  constructor <;> linarith

/-! ## Two finite forcing integrals -/

/-- `lem:app-phase-forcing-integrals`, part (i) of 2, snapshot `cr-2026-10-23`.
Source: `section.tex` l.2173–2185.
LaTeX (verbatim, `section.tex` l.2173–2185):
```
\begin{lemma}[Two finite forcing integrals]\label{lem:app-phase-forcing-integrals}
Let $p>1$, $q>0$, $C=C_{p,q}$ and $A=A_p$.
\begin{enumerate}[label=(\roman*)]
\item If $p=2q+1$, then for every $N\ge1$
\[
\big|J_N(p,q)-a_q\,q\log N\big|\le2C+\frac{qM_{p,q}2^{-p/q}}{a_q}+\frac1{\sqrt{2(p-1)}} .
\]
\item If $p=q+1$, then for every $N\ge4\cdot4^{1/q}$
\[
\sqrt A\,4^{-q/2}N^{q/2}\le J_N(p,q)\le3C\,N^{q/2} .
\]
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_forcing_integrals_i
    {p q : ℝ} (hq : 0 < q) (hp : p = 2 * q + 1) (N : ℕ) (hN : 1 ≤ N) :
    |JN N p q - aQ q * q * Real.log (N : ℝ)| ≤
      2 * Cpq p q + q * Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q + 1 / Real.sqrt (2 * (p - 1)) := by
  have hp1 : 1 < p := by linarith
  have hr : rq p q = 1 := by
    unfold rq
    rw [div_eq_iff (mul_pos two_pos hq).ne']
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL1 : (1 : ℝ) ≤ (N : ℝ) ^ q := Real.one_le_rpow (by exact_mod_cast hN) hq.le
  have hLnn : (0 : ℝ) ≤ (N : ℝ) ^ q := by linarith
  have hsplit := fi_split (p := p) N hN hq.le hLnn
  have hcont_fin : Continuous (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q u)) :=
    (fl_cont N p q).sqrt
  have hint_fin : IntervalIntegrable (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q u)) volume
      0 ((N : ℝ) ^ q) := hcont_fin.intervalIntegrable _ _
  have hint_inf : IntervalIntegrable (fun u : ℝ => Real.sqrt (fNq ⊤ p q u)) volume
      0 ((N : ℝ) ^ q) := ck_int_sqrt (q := q) hp1 le_rfl hLnn
  have hdiff_int : IntervalIntegrable (fun u : ℝ => Real.sqrt (fNq ⊤ p q u)
      - Real.sqrt (fNq (N : ℕ∞) p q u)) volume 0 ((N : ℝ) ^ q) := hint_inf.sub hint_fin
  have hdiff_eq : ∫ u in (0 : ℝ)..(N : ℝ) ^ q, Real.sqrt (fNq (N : ℕ∞) p q u)
      = (∫ u in (0 : ℝ)..(N : ℝ) ^ q, Real.sqrt (fNq ⊤ p q u))
        - ∫ u in (0 : ℝ)..(N : ℝ) ^ q, (Real.sqrt (fNq ⊤ p q u)
          - Real.sqrt (fNq (N : ℕ∞) p q u)) := by
    rw [intervalIntegral.integral_sub hint_inf hint_fin]
    ring
  have hD0 : 0 ≤ ∫ u in (0 : ℝ)..(N : ℝ) ^ q, (Real.sqrt (fNq ⊤ p q u)
      - Real.sqrt (fNq (N : ℕ∞) p q u)) :=
    intervalIntegral.integral_nonneg hLnn (fun u hu => (cr_diff hp1 N hN hu.1).1)
  have hD1 : ∫ u in (0 : ℝ)..(N : ℝ) ^ q, (Real.sqrt (fNq ⊤ p q u)
      - Real.sqrt (fNq (N : ℕ∞) p q u)) ≤ 1 / Real.sqrt (2 * (p - 1)) := by
    have hI := intervalIntegral.integral_mono_on hLnn hdiff_int
      (intervalIntegrable_const (c := (N : ℝ) ^ ((1 - p) / 2) / Real.sqrt (2 * (p - 1))))
      (fun u hu => (cr_diff hp1 N hN hu.1).2)
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hI
    have hLc : (N : ℝ) ^ q * (N : ℝ) ^ ((1 - p) / 2) = 1 := by
      rw [← Real.rpow_add hNpos, show q + (1 - p) / 2 = 0 by rw [hp]; ring, Real.rpow_zero]
    calc _ ≤ _ := hI
      _ = 1 / Real.sqrt (2 * (p - 1)) := by rw [← mul_div_assoc, hLc]
  have hC0 : 0 ≤ Cpq p q := Real.sqrt_nonneg _
  have hC_bound : (N : ℝ) ^ q * Real.sqrt (fNq (N : ℕ∞) p q ((N : ℝ) ^ q)) ≤ Cpq p q := by
    have henv := fi_env (p := p) hp1 hq N hN hLnn
    rw [hr, Real.rpow_neg_one] at henv
    have hLr : (N : ℝ) ^ q * ((N : ℝ) ^ q + 1)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by linarith)]
      linarith
    calc (N : ℝ) ^ q * Real.sqrt (fNq (N : ℕ∞) p q ((N : ℝ) ^ q))
        ≤ (N : ℝ) ^ q * (Cpq p q * ((N : ℝ) ^ q + 1)⁻¹) :=
          mul_le_mul_of_nonneg_left henv hLnn
      _ = Cpq p q * ((N : ℝ) ^ q * ((N : ℝ) ^ q + 1)⁻¹) := by ring
      _ ≤ Cpq p q * 1 := mul_le_mul_of_nonneg_left hLr hC0
      _ = Cpq p q := mul_one _
  have hI2_nonneg : 0 ≤ ∫ u in Ioi ((N : ℝ) ^ q), Real.sqrt (fNq (N : ℕ∞) p q u) :=
    setIntegral_nonneg measurableSet_Ioi (fun u _ => Real.sqrt_nonneg _)
  have hI2_le := (fi_tail_le (p := p) N hN hq.le).trans hC_bound
  have hTinf := fi_inf_log (p := p) hp1 hq hr hL1
  have hlog : Real.log ((N : ℝ) ^ q) = q * Real.log (N : ℝ) := Real.log_rpow hNpos q
  have hgoal_expr : aQ q * q * Real.log (N : ℝ) = aQ q * Real.log ((N : ℝ) ^ q) := by
    rw [hlog]; ring
  rw [hsplit, hdiff_eq, hgoal_expr]
  obtain ⟨h1, h2⟩ := abs_le.mp hTinf
  rw [abs_le]
  constructor <;> linarith [hD0, hD1, hI2_nonneg, hI2_le]


/-- `lem:app-phase-forcing-integrals`, part (ii) of 2, snapshot `cr-2026-10-23`.
Source: `section.tex` l.2173–2185.
LaTeX (verbatim, `section.tex` l.2173–2185):
```
\begin{lemma}[Two finite forcing integrals]\label{lem:app-phase-forcing-integrals}
Let $p>1$, $q>0$, $C=C_{p,q}$ and $A=A_p$.
\begin{enumerate}[label=(\roman*)]
\item If $p=2q+1$, then for every $N\ge1$
\[
\big|J_N(p,q)-a_q\,q\log N\big|\le2C+\frac{qM_{p,q}2^{-p/q}}{a_q}+\frac1{\sqrt{2(p-1)}} .
\]
\item If $p=q+1$, then for every $N\ge4\cdot4^{1/q}$
\[
\sqrt A\,4^{-q/2}N^{q/2}\le J_N(p,q)\le3C\,N^{q/2} .
\]
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_phase_forcing_integrals_ii
    {p q : ℝ} (hq : 0 < q) (hp : p = q + 1) (N : ℕ) (hN : 4 * (4 : ℝ) ^ (1 / q) ≤ (N : ℝ)) :
    Real.sqrt (Aconst p) * (4 : ℝ) ^ (-(q / 2)) * (N : ℝ) ^ (q / 2) ≤ JN N p q ∧
      JN N p q ≤ 3 * Cpq p q * (N : ℝ) ^ (q / 2) := by
  have hp1 : 1 < p := by linarith
  have hr : rq p q = 1 / 2 := by
    unfold rq
    rw [div_eq_iff (mul_pos two_pos hq).ne']
    linarith
  have hd : dAQ p q = 1 := by
    unfold dAQ
    rw [div_eq_iff hq.ne']
    linarith
  have hN4 : (4 : ℝ) ≤ N := by
    have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ (1 / q) := Real.one_le_rpow (by norm_num) (by positivity)
    linarith
  have hN4' : 4 ≤ N := by exact_mod_cast hN4
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hV4 : (4 : ℝ) ≤ ((N : ℝ) / 4) ^ q := by
    have h1 : (4 : ℝ) ^ (1 / q) ≤ (N : ℝ) / 4 := by linarith
    have h2 := Real.rpow_le_rpow (by positivity) h1 hq.le
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4), one_div, inv_mul_cancel₀ hq.ne',
      Real.rpow_one] at h2
    exact h2
  have hV0 : (0 : ℝ) ≤ ((N : ℝ) / 4) ^ q := by linarith
  have hA0 : 0 ≤ Aconst p := by unfold Aconst; positivity
  have hsqrtV : Real.sqrt (((N : ℝ) / 4) ^ q)
      = (N : ℝ) ^ (q / 2) * (4 : ℝ) ^ (-(q / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (div_nonneg hNpos.le (by norm_num)),
      show q * (1 / 2) = q / 2 by ring, Real.div_rpow hNpos.le (by norm_num : (0 : ℝ) ≤ 4),
      div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
  have hsqrtL : Real.sqrt ((N : ℝ) ^ q) = (N : ℝ) ^ (q / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
    congr 1
    ring
  have hLnn : (0 : ℝ) ≤ (N : ℝ) ^ q := Real.rpow_nonneg hNpos.le q
  have hL1 : (1 : ℝ) ≤ (N : ℝ) ^ q := Real.one_le_rpow hN1r hq.le
  have hsplitL := fi_split (p := p) N hN1 hq.le hLnn
  have hcont_fin : Continuous (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q u)) :=
    (fl_cont N p q).sqrt
  have hint_fin : IntervalIntegrable (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q u)) volume
      0 ((N : ℝ) ^ q) := hcont_fin.intervalIntegrable _ _
  have henv : ∀ u : ℝ, 0 ≤ u → Real.sqrt (fNq (N : ℕ∞) p q u) ≤ Cpq p q * (u + 1) ^ (-(1 / 2 : ℝ)) := by
    intro u hu
    have := fi_env (p := p) hp1 hq N hN1 hu
    rwa [hr] at this
  have hC0 : 0 ≤ Cpq p q := Real.sqrt_nonneg _
  -- upper bound on the bulk integral
  have hI1_le : (∫ u in (0 : ℝ)..(N : ℝ) ^ q, Real.sqrt (fNq (N : ℕ∞) p q u))
      ≤ 2 * Cpq p q * Real.sqrt ((N : ℝ) ^ q) := by
    have hmono : (∫ u in (0 : ℝ)..(N : ℝ) ^ q, Real.sqrt (fNq (N : ℕ∞) p q u))
      ≤ ∫ u in (0 : ℝ)..(N : ℝ) ^ q, Cpq p q * (u + 1) ^ (-(1 / 2 : ℝ)) :=
    intervalIntegral.integral_mono_on hLnn hint_fin
      ((fi_rpow_ii (r := -(1 / 2 : ℝ)) hLnn).const_mul (Cpq p q))
      (fun u hu => henv u hu.1)
    rw [intervalIntegral.integral_const_mul, fi_int_isqrt hLnn] at hmono
    have hsq : Real.sqrt ((N : ℝ) ^ q + 1) ≤ Real.sqrt ((N : ℝ) ^ q) + 1 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      nlinarith [Real.sq_sqrt hLnn, Real.sqrt_nonneg ((N : ℝ) ^ q)]
    have := mul_le_mul_of_nonneg_left (by linarith : 2 * (Real.sqrt ((N : ℝ) ^ q + 1) - 1)
      ≤ 2 * Real.sqrt ((N : ℝ) ^ q)) hC0
    linarith
  -- upper bound on the tail
  have hI2_le : (∫ u in Ioi ((N : ℝ) ^ q), Real.sqrt (fNq (N : ℕ∞) p q u))
      ≤ Cpq p q * Real.sqrt ((N : ℝ) ^ q) := by
    refine (fi_tail_le (p := p) N hN1 hq.le).trans ?_
    have henvL := henv ((N : ℝ) ^ q) hLnn
    have hX0 : 0 ≤ ((N : ℝ) ^ q + 1) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hXt : ((N : ℝ) ^ q + 1) ^ (-(1 / 2 : ℝ)) * Real.sqrt ((N : ℝ) ^ q + 1) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add (show (0 : ℝ) < (N : ℝ) ^ q + 1 by linarith)]
      norm_num
    have hst : Real.sqrt ((N : ℝ) ^ q) ≤ Real.sqrt ((N : ℝ) ^ q + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsX : Real.sqrt ((N : ℝ) ^ q) * ((N : ℝ) ^ q + 1) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      have h1 := mul_le_mul_of_nonneg_right hst hX0
      have h2 : Real.sqrt ((N : ℝ) ^ q + 1) * ((N : ℝ) ^ q + 1) ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [mul_comm]; exact hXt
      linarith
    have hLX : (N : ℝ) ^ q * ((N : ℝ) ^ q + 1) ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt ((N : ℝ) ^ q) := by
      have hs2 : Real.sqrt ((N : ℝ) ^ q) ^ 2 = (N : ℝ) ^ q := Real.sq_sqrt hLnn
      calc (N : ℝ) ^ q * ((N : ℝ) ^ q + 1) ^ (-(1 / 2 : ℝ))
          = Real.sqrt ((N : ℝ) ^ q) ^ 2 * ((N : ℝ) ^ q + 1) ^ (-(1 / 2 : ℝ)) := by rw [hs2]
        _ = Real.sqrt ((N : ℝ) ^ q) * (Real.sqrt ((N : ℝ) ^ q) * ((N : ℝ) ^ q + 1) ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ Real.sqrt ((N : ℝ) ^ q) * 1 := mul_le_mul_of_nonneg_left hsX (Real.sqrt_nonneg _)
        _ = Real.sqrt ((N : ℝ) ^ q) := mul_one _
    calc (N : ℝ) ^ q * Real.sqrt (fNq (N : ℕ∞) p q ((N : ℝ) ^ q))
        ≤ (N : ℝ) ^ q * (Cpq p q * ((N : ℝ) ^ q + 1) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left henvL hLnn
      _ = Cpq p q * ((N : ℝ) ^ q * ((N : ℝ) ^ q + 1) ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ Cpq p q * Real.sqrt ((N : ℝ) ^ q) := mul_le_mul_of_nonneg_left hLX hC0
  -- upper bound
  have hupper : JN N p q ≤ 3 * Cpq p q * (N : ℝ) ^ (q / 2) := by
    rw [hsplitL, ← hsqrtL]
    linarith
  -- lower bound
  have hVnn : (0 : ℝ) ≤ ((N : ℝ) / 4) ^ q := hV0
  have hsplitV := fi_split (p := p) N hN1 hq.le hVnn
  have hint_V : IntervalIntegrable (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q u)) volume
      0 (((N : ℝ) / 4) ^ q) := hcont_fin.intervalIntegrable _ _
  have hpt : ∀ u : ℝ, 0 ≤ u → u ≤ ((N : ℝ) / 4) ^ q →
      Real.sqrt (Aconst p) * (u + 1) ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt (fNq (N : ℕ∞) p q u) := by
    intro u hu0 huV
    have hs := lem_app_phase_sums_ii (a := p) (q := q) hp1 hq N hN4' hu0 huV
    rw [hd] at hs
    have hf : Aconst p * (u + 1) ^ (-(1 : ℝ)) ≤ fNq (N : ℕ∞) p q u := by
      rw [add_comm u 1]; exact hs
    have hX0 : 0 ≤ (u + 1) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hsq : ((u + 1) ^ (-(1 / 2 : ℝ))) ^ 2 = (u + 1) ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (show (0 : ℝ) ≤ u + 1 by linarith)]
      norm_num
    calc Real.sqrt (Aconst p) * (u + 1) ^ (-(1 / 2 : ℝ))
        = Real.sqrt ((Real.sqrt (Aconst p) * (u + 1) ^ (-(1 / 2 : ℝ))) ^ 2) :=
          (Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hX0)).symm
      _ ≤ Real.sqrt (fNq (N : ℕ∞) p q u) := by
          apply Real.sqrt_le_sqrt
          rw [mul_pow, Real.sq_sqrt hA0, hsq]
          exact hf
  have hIlow : ∫ u in (0 : ℝ)..((N : ℝ) / 4) ^ q, Real.sqrt (Aconst p) * (u + 1) ^ (-(1 / 2 : ℝ))
      ≤ ∫ u in (0 : ℝ)..((N : ℝ) / 4) ^ q, Real.sqrt (fNq (N : ℕ∞) p q u) :=
    intervalIntegral.integral_mono_on hVnn
      ((fi_rpow_ii (r := -(1 / 2 : ℝ)) hVnn).const_mul (Real.sqrt (Aconst p))) hint_V
      (fun u hu => hpt u hu.1 hu.2)
  rw [intervalIntegral.integral_const_mul, fi_int_isqrt hVnn] at hIlow
  have hsV : Real.sqrt (((N : ℝ) / 4) ^ q) ^ 2 = ((N : ℝ) / 4) ^ q := Real.sq_sqrt hV0
  have hs0 : 0 ≤ Real.sqrt (((N : ℝ) / 4) ^ q) := Real.sqrt_nonneg _
  have hs2 : (2 : ℝ) ≤ Real.sqrt (((N : ℝ) / 4) ^ q) := by nlinarith
  have ht : 1 + Real.sqrt (((N : ℝ) / 4) ^ q) / 2 ≤ Real.sqrt (((N : ℝ) / 4) ^ q + 1) :=
    (Real.le_sqrt (by positivity) (by linarith)).mpr (by nlinarith)
  have hineq : Real.sqrt (((N : ℝ) / 4) ^ q) ≤ 2 * (Real.sqrt (((N : ℝ) / 4) ^ q + 1) - 1) := by
    linarith
  have key := mul_le_mul_of_nonneg_left hineq (Real.sqrt_nonneg (Aconst p))
  have e1 : Real.sqrt (Aconst p) * (4 : ℝ) ^ (-(q / 2)) * (N : ℝ) ^ (q / 2)
      = Real.sqrt (Aconst p) * Real.sqrt (((N : ℝ) / 4) ^ q) := by
    rw [hsqrtV]; ring
  have htail := setIntegral_nonneg (μ := volume) measurableSet_Ioi
    (fun u (_ : u ∈ Ioi (((N : ℝ) / 4) ^ q)) => Real.sqrt_nonneg (fNq (N : ℕ∞) p q u))
  refine ⟨?_, hupper⟩
  rw [e1]
  linarith [hsplitV, htail, key, hIlow]


end Muon.Phase
end

import Mathlib
import Muon.Foundations.RealAnalysis

/-!
# Appendix H: power sums, variation, Laplace bounds, harmonic sums

Snapshot `cr-2026-10-22`. Source: `sections/07-phase-comparison/section.tex`, subsection
"Power sums" (l.925–1060): `lem:app-phase-variation`, `lem:app-phase-laplace`,
`lem:app-phase-sums`, `lem:app-phase-harmonic`, with the definitions `M_{p,q}`, `f_a`,
`d(a,q)`, `Z_a`, `A_a`, `E_{a,q}`, `L_{N,a,q}`, `f_{N,q}`, `r_q`, `C_{p,q}`, `J`, `J_N`,
`H_N(a)`, `ζ(a)` (l.934–1046).

Pure real analysis; no probability. The unimodal sum–integral comparison and the
one-sided convolution live in `Muon.Foundations.RealAnalysis` (imported, not redefined).
-/

open MeasureTheory Set Filter Topology Asymptotics

noncomputable section

namespace Muon.Phase

/-! ## Objects -/

/-- `M_{p,q} = (p/(e q))^{p/q}` (`section.tex` l.934–935, the display `M_{p,q}≔(p/(eq))^{p/q}`).
The maximum constant of `f_a` in `lem:app-phase-variation`. -/
def Mpq (p q : ℝ) : ℝ := (p / (Real.exp 1 * q)) ^ (p / q)

/-- `f_a(x) = x^{-p} e^{-a x^{-q}}` for `x > 0`, and `f_a(0) := 0` (`lem:app-phase-variation`).
The value at `x ≤ 0` is `0` by convention and is never used by a statement at `x ≤ 0`
(all statements integrate over `[0, N]` or evaluate at `x > 0`). -/
def fa (p q a x : ℝ) : ℝ := if 0 < x then x ^ (-p) * Real.exp (-a * x ^ (-q)) else 0

/-- `L_{N,a,q}(u) = ∑_{i=1}^N i^{-a} e^{-2u i^{-q}}` for `u ≥ 0`, for `N ∈ ℕ ∪ {∞}`
(`eqn:app-phase-EA` l.~960–968). Encoded as a `tsum` over `i : ℕ` restricted to `1 ≤ i ≤ N`;
for finite `N` this is the finite sum, for `N = ∞` the series. -/
def Lsum (N : ℕ∞) (a q u : ℝ) : ℝ :=
  ∑' i : ℕ, if 0 < i ∧ ((i : ℕ∞) ≤ N) then
    (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0

/-- `H_N(a) = ∑_{i=1}^N i^{-a}` for an integer `N ≥ 1` (`lem:app-phase-harmonic`). -/
def Hsum (a : ℝ) (N : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-a)

/-- The real series `ζ(a) = ∑_{i ≥ 1} i^{-a}` (`lem:app-phase-harmonic`). This is the real
series, not `riemannZeta`; it is meaningful for `a > 1`. -/
def zetaR (a : ℝ) : ℝ := ∑' i : ℕ, if 0 < i then (i : ℝ) ^ (-a) else 0

/-- The tail `∑_{i > N} i^{-p}` of the series in `lem:app-phase-laplace`, for `N : ℕ`. -/
def tailSum (p : ℝ) (N : ℕ) : ℝ := ∑' i : ℕ, if N < i then (i : ℝ) ^ (-p) else 0

/-- `d(a,q) = (a-1)/q` (`eqn:app-phase-EA`). -/
def dAQ (a q : ℝ) : ℝ := (a - 1) / q

/-- `Z_a = 1 + 1/(a-1)` (`eqn:app-phase-EA`). -/
def Za (a : ℝ) : ℝ := 1 + 1 / (a - 1)

/-- `A_a = 2^{-2a} e^{-2}` (`eqn:app-phase-EA`). -/
def Aconst (a : ℝ) : ℝ := (2 : ℝ) ^ (-(2 * a)) * Real.exp (-2)

/-- `E_{a,q} = max{2^{d(a,q)} Z_a, Γ(d(a,q))/q + 2^{1-1/q} M_{a,q}}` (`eqn:app-phase-EA`). -/
def Epq (a q : ℝ) : ℝ :=
  max ((2 : ℝ) ^ dAQ a q * Za a) (Real.Gamma (dAQ a q) / q + (2 : ℝ) ^ (1 - 1 / q) * Mpq a q)

/-- `f_{N,q}(u) = (1/2) L_{N,p,q}(u)` (`eqn:app-phase-fNq`), the forcing exponent `p`
being the first slot. -/
def fNq (N : ℕ∞) (p q u : ℝ) : ℝ := (1 / 2) * Lsum N p q u

/-- `r_q = (p-1)/(2q)` (`eqn:app-phase-fNq`). -/
def rq (p q : ℝ) : ℝ := (p - 1) / (2 * q)

/-- `C_{p,q} = √(E_{p,q}/2)` (`eqn:app-phase-fNq`). -/
def Cpq (p q : ℝ) : ℝ := Real.sqrt (Epq p q / 2)

/-- `J(p,q) = ∫_0^∞ √(f_{∞,q}(u)) du` (`eqn:app-phase-J`). Meaningful when `r_q > 1`. -/
def Jpq (p q : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), Real.sqrt (fNq ⊤ p q u)

/-- `J_N(p,q) = ∫_0^∞ √(f_{N,q}(u)) du` for an integer `N` (`eqn:app-phase-fNq`). -/
def JN (N : ℕ) (p q : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), Real.sqrt (fNq (N : ℕ∞) p q u)

/-! ## Sum and integral -/

/-- `lem:app-phase-variation`: Sum and integral (`section.tex` l.944–954, Lean part (i)).

Let $p,q,a>0$ and $f_a(x)\defeq x^{-p}e^{-ax^{-q}}$ for $x>0$, $f_a(0)\defeq0$.
The function $f_a$ has a unique maximum, at $x=(qa/p)^{1/q}$, with value
$M_{p,q}a^{-p/q}$. For every integer $N\ge1$,
\begin{equation}\label{eqn:app-phase-variation}
\begin{gathered}
\Big|\sum_{i=1}^Nf_a(i)-\int_0^Nf_a(x)\,\dif x\Big|\le2M_{p,q}a^{-p/q},\\
\int_0^Nf_a(x)\,\dif x=\frac{a^{(1-p)/q}}q\int_{a/N^q}^\infty y^{(p-1)/q-1}e^{-y}\,\dif y .
\end{gathered}
\end{equation} -/
theorem lem_app_phase_variation_i {p q a : ℝ} (hp : 0 < p) (hq : 0 < q) (ha : 0 < a) :
    fa p q a ((q * a / p) ^ (1 / q)) = Mpq p q * a ^ (-(p / q)) ∧
      ∀ x : ℝ, 0 < x → x ≠ (q * a / p) ^ (1 / q) →
        fa p q a x < fa p q a ((q * a / p) ^ (1 / q)) := by
  have hc : 0 < q * a / p := div_pos (mul_pos hq ha) hp
  have hxs : 0 < (q * a / p) ^ (1 / q) := Real.rpow_pos_of_pos hc _
  have hLs : Real.log ((q * a / p) ^ (1 / q)) = Real.log (q * a / p) / q := by
    rw [Real.log_rpow hc]; ring
  have hfa : ∀ x : ℝ, 0 < x →
      fa p q a x = Real.exp (-p * Real.log x - a * Real.exp (-q * Real.log x)) := by
    intro x hx
    simp only [fa, hx, ↓reduceIte]
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx, ← Real.exp_add]
    congr 1
    ring_nf
  have hval : a * Real.exp (-q * Real.log ((q * a / p) ^ (1 / q))) = p / q := by
    rw [hLs, show -q * (Real.log (q * a / p) / q) = -Real.log (q * a / p) by field_simp,
      Real.exp_neg, Real.exp_log hc]
    field_simp
  have hpq : 0 < p / q := div_pos hp hq
  refine ⟨?_, ?_⟩
  · rw [hfa _ hxs]
    have hpe : 0 < p / (Real.exp 1 * q) := div_pos hp (mul_pos (Real.exp_pos 1) hq)
    have hpa : 0 < a := ha
    rw [hval]
    unfold Mpq
    rw [Real.rpow_def_of_pos hpe, Real.rpow_def_of_pos ha, ← Real.exp_add]
    congr 1
    have l1 : Real.log (q * a / p) = Real.log q + Real.log a - Real.log p := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    have l2 : Real.log (p / (Real.exp 1 * q)) = Real.log p - 1 - Real.log q := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_exp]
      ring
    rw [hLs, l1, l2]
    ring
  · intro x hx hne
    rw [hfa x hx, hfa _ hxs, Real.exp_lt_exp]
    have h2 : a * Real.exp (-q * Real.log x) =
        p / q * Real.exp (q * (Real.log ((q * a / p) ^ (1 / q)) - Real.log x)) := by
      rw [show Real.exp (-q * Real.log x) = Real.exp (-q * Real.log ((q * a / p) ^ (1 / q)))
          * Real.exp (q * (Real.log ((q * a / p) ^ (1 / q)) - Real.log x)) by
        rw [← Real.exp_add]; congr 1; ring, ← mul_assoc, hval]
    have hne' : Real.log x ≠ Real.log ((q * a / p) ^ (1 / q)) := by
      intro h
      apply hne
      exact Real.log_injOn_pos hx hxs h
    set u := q * (Real.log ((q * a / p) ^ (1 / q)) - Real.log x) with hu
    have hu0 : u ≠ 0 := by
      rw [hu]
      apply mul_ne_zero hq.ne'
      intro h; apply hne'; linarith
    have hk := Real.add_one_lt_exp hu0
    have hk2 := mul_lt_mul_of_pos_left hk hpq
    have hid : p * (Real.log ((q * a / p) ^ (1 / q)) - Real.log x) + p / q
        = p / q * (u + 1) := by
      rw [hu]; field_simp
    rw [h2]
    linarith [hval]

lemma pv_tele_Ico (g : ℕ → ℝ) (a b : ℕ) (h : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, (g (i+1) - g i) = g b - g a := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [Finset.sum_Ico_succ_top hn, ih]; ring

lemma pv_assemble {f : ℝ → ℝ} {L N : ℕ} (hLN : L < N) {M : ℝ}
    (hnn : ∀ x ∈ Icc (0:ℝ) N, 0 ≤ f x) (hbd : ∀ x ∈ Icc (0:ℝ) N, f x ≤ M)
    (hmeas : Measurable f) (hf0 : f 0 = 0)
    (hup : MonotoneOn f (Icc (0:ℝ) L)) (hdown : AntitoneOn f (Icc ((L:ℝ)+1) N)) :
    |(∑ i ∈ Finset.Icc 1 N, f (i : ℝ)) - ∫ x in (0 : ℝ)..(N : ℝ), f x| ≤ 2 * M := by
  have hM : 0 ≤ M := le_trans (hnn 0 ⟨le_refl _, by positivity⟩) (hbd 0 ⟨le_refl _, by positivity⟩)
  have hii : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ N → IntervalIntegrable f volume a b := by
    intro a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    refine Measure.integrableOn_of_bounded (M := M) (by simp) hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn x ⟨ha.trans hx.1, hx.2.trans hb⟩)]
    exact hbd x ⟨ha.trans hx.1, hx.2.trans hb⟩
  have hRN : L + 1 ≤ N := hLN
  have hLN' : (L:ℝ) ≤ N := by exact_mod_cast hLN.le
  have hR' : ((L+1 : ℕ):ℝ) ≤ N := by exact_mod_cast hRN
  -- split integral
  have hsplit : ∫ x in (0:ℝ)..(N:ℝ), f x =
      (∫ x in (0:ℝ)..(L:ℝ), f x) + (∫ x in (L:ℝ)..((L+1 : ℕ):ℝ), f x)
        + ∫ x in ((L+1 : ℕ):ℝ)..(N:ℝ), f x := by
    have h1 := hii 0 L le_rfl (by positivity) hLN'
    have h2 := hii L ((L+1:ℕ):ℝ) (by positivity) (by push_cast; linarith) hR'
    have h3 := hii ((L+1:ℕ):ℝ) N (by positivity) hR' le_rfl
    rw [intervalIntegral.integral_add_adjacent_intervals h1 h2,
      intervalIntegral.integral_add_adjacent_intervals (h1.trans h2) h3]
  -- sum split
  have hsum : ∑ i ∈ Finset.Icc 1 N, f (i : ℝ) =
      (∑ i ∈ Finset.Ico 0 L, f ((i+1 : ℕ) : ℝ)) + f ((L+1 : ℕ) : ℝ)
        + ∑ i ∈ Finset.Ico (L+1) N, f ((i+1 : ℕ) : ℝ) := by
    have e1 : ∑ i ∈ Finset.Icc 1 N, f (i : ℝ) = ∑ i ∈ Finset.Ico 0 N, f ((i+1 : ℕ) : ℝ) := by
      rw [Finset.sum_Ico_add' (fun i : ℕ => f (i:ℝ)) 0 N 1]
      rfl
    rw [e1, ← Finset.sum_Ico_consecutive _ (Nat.zero_le L) hLN.le,
      Finset.sum_eq_sum_Ico_succ_bot hLN, ← add_assoc]
  -- piece 1
  have hup' : MonotoneOn f (Icc ((0:ℕ):ℝ) (L:ℝ)) := by simpa using hup
  have hdown' : AntitoneOn f (Icc ((L+1:ℕ):ℝ) (N:ℝ)) := by simpa using hdown
  have p1a := hup'.sum_le_integral_Ico (Nat.zero_le L)
  have p1b := hup'.integral_le_sum_Ico (Nat.zero_le L)
  have p1t := pv_tele_Ico (fun i => f (i:ℝ)) 0 L (Nat.zero_le _)
  have p3a := hdown'.sum_le_integral_Ico hRN
  have p3b := hdown'.integral_le_sum_Ico hRN
  have p3t := pv_tele_Ico (fun i => f (i:ℝ)) (L+1) N hRN
  rw [Finset.sum_sub_distrib] at p1t p3t
  simp only [Nat.cast_zero] at p1a p1b p1t
  have hfL : f L ≤ M := hbd L ⟨by positivity, hLN'⟩
  have hfR : f ((L+1:ℕ):ℝ) ≤ M := hbd _ ⟨by positivity, hR'⟩
  have hfR0 : 0 ≤ f ((L+1:ℕ):ℝ) := hnn _ ⟨by positivity, hR'⟩
  have hfN0 : 0 ≤ f (N:ℝ) := hnn _ ⟨by positivity, le_rfl⟩
  have hLR : (L:ℝ) ≤ ((L+1:ℕ):ℝ) := by push_cast; linarith
  have h2 := hii L ((L+1:ℕ):ℝ) (by positivity) hLR hR'
  have hI2a : 0 ≤ ∫ x in (L:ℝ)..((L+1 : ℕ):ℝ), f x :=
    intervalIntegral.integral_nonneg hLR (fun x hx => hnn x ⟨(by positivity : (0:ℝ) ≤ L).trans hx.1, hx.2.trans hR'⟩)
  have hI2b : ∫ x in (L:ℝ)..((L+1 : ℕ):ℝ), f x ≤ M := by
    have := intervalIntegral.integral_mono_on hLR h2 (intervalIntegrable_const (c := M))
      (fun x hx => hbd x ⟨(by positivity : (0:ℝ) ≤ L).trans hx.1, hx.2.trans hR'⟩)
    simpa using this.trans (by push_cast; simp)
  rw [hsum, hsplit, abs_le]
  rw [hf0] at p1t
  constructor <;> linarith

lemma pv_fa_exp {p q a x : ℝ} (hx : 0 < x) :
    fa p q a x = Real.exp (-p * Real.log x - a * Real.exp (-q * Real.log x)) := by
  simp only [fa, hx, ↓reduceIte]
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx, ← Real.exp_add]
  congr 1
  ring_nf

lemma pv_fa_nonneg {p q a : ℝ} (x : ℝ) : 0 ≤ fa p q a x := by
  unfold fa
  split_ifs with h
  · exact mul_nonneg (Real.rpow_nonneg h.le _) (Real.exp_pos _).le
  · exact le_rfl

lemma pv_fa_zero {p q a : ℝ} : fa p q a 0 = 0 := by simp [fa]

lemma pv_fa_meas {p q a : ℝ} : Measurable (fa p q a) := by
  unfold fa
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  fun_prop

lemma pv_key {p q a : ℝ} (hp : 0 < p) (hq : 0 < q) (ha : 0 < a) :
    a * q * Real.exp (-q * Real.log ((q * a / p) ^ (1 / q))) = p := by
  have hc : 0 < q * a / p := div_pos (mul_pos hq ha) hp
  have hLs : Real.log ((q * a / p) ^ (1 / q)) = Real.log (q * a / p) / q := by
    rw [Real.log_rpow hc]; ring
  rw [hLs, show -q * (Real.log (q * a / p) / q) = -Real.log (q * a / p) by field_simp,
    Real.exp_neg, Real.exp_log hc]
  field_simp

lemma pv_mono {p q a x y : ℝ} (hp : 0 < p) (hq : 0 < q) (ha : 0 < a)
    (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ (q * a / p) ^ (1 / q)) :
    fa p q a x ≤ fa p q a y := by
  have hy0 : 0 < y := hx.trans_le hxy
  have hxs : 0 < (q * a / p) ^ (1 / q) := Real.rpow_pos_of_pos (div_pos (mul_pos hq ha) hp) _
  rw [pv_fa_exp hx, pv_fa_exp hy0, Real.exp_le_exp]
  have hk := pv_key hp hq ha
  set u := Real.log y - Real.log x with hu
  have hu0 : 0 ≤ u := by
    rw [hu]; linarith [Real.log_le_log hx hxy]
  have hw : Real.exp (-q * Real.log ((q * a / p) ^ (1 / q))) ≤ Real.exp (-q * Real.log y) := by
    rw [Real.exp_le_exp]
    have := Real.log_le_log hy0 hy
    nlinarith
  have hex : Real.exp (-q * Real.log x) = Real.exp (-q * Real.log y) * Real.exp (q * u) := by
    rw [← Real.exp_add]; congr 1; rw [hu]; ring
  have h1 := Real.add_one_le_exp (q * u)
  have hwy := Real.exp_pos (-q * Real.log y)
  rw [hex]
  have : a * q * Real.exp (-q * Real.log y) ≥ p := by
    rw [← hk]; exact mul_le_mul_of_nonneg_left hw (by positivity)
  nlinarith [mul_nonneg hu0 (sub_nonneg.2 this), mul_pos ha hwy, mul_nonneg (mul_pos ha hwy).le (sub_nonneg.2 h1)]

lemma pv_anti {p q a x y : ℝ} (hp : 0 < p) (hq : 0 < q) (ha : 0 < a)
    (hx : (q * a / p) ^ (1 / q) ≤ x) (hxy : x ≤ y) :
    fa p q a y ≤ fa p q a x := by
  have hxs : 0 < (q * a / p) ^ (1 / q) := Real.rpow_pos_of_pos (div_pos (mul_pos hq ha) hp) _
  have hx0 : 0 < x := hxs.trans_le hx
  have hy0 : 0 < y := hx0.trans_le hxy
  rw [pv_fa_exp hx0, pv_fa_exp hy0, Real.exp_le_exp]
  have hk := pv_key hp hq ha
  set u := Real.log y - Real.log x with hu
  have hu0 : 0 ≤ u := by
    rw [hu]; linarith [Real.log_le_log hx0 hxy]
  have hw : Real.exp (-q * Real.log x) ≤ Real.exp (-q * Real.log ((q * a / p) ^ (1 / q))) := by
    rw [Real.exp_le_exp]
    have := Real.log_le_log hxs hx
    nlinarith
  have hex : Real.exp (-q * Real.log y) = Real.exp (-q * Real.log x) * Real.exp (-(q * u)) := by
    rw [← Real.exp_add]; congr 1; rw [hu]; ring
  have h1 := Real.add_one_le_exp (-(q * u))
  have hwx := Real.exp_pos (-q * Real.log x)
  rw [hex]
  have : a * q * Real.exp (-q * Real.log x) ≤ p := by
    rw [← hk]; exact mul_le_mul_of_nonneg_left hw (by positivity)
  have hqu : 0 ≤ q * u := by positivity
  nlinarith [mul_nonneg hu0 (sub_nonneg.2 this), mul_pos ha hwx, mul_nonneg (mul_pos ha hwx).le (sub_nonneg.2 h1), mul_nonneg hqu (mul_pos ha hwx).le]

lemma pv_le_M {p q a : ℝ} (hp : 0 < p) (hq : 0 < q) (ha : 0 < a) (x : ℝ) (hx : 0 ≤ x) :
    fa p q a x ≤ Mpq p q * a ^ (-(p / q)) := by
  obtain ⟨h1, h2⟩ := lem_app_phase_variation_i hp hq ha
  rw [← h1]
  rcases hx.eq_or_lt with h | h
  · rw [← h, pv_fa_zero]; exact pv_fa_nonneg _
  · by_cases hxx : x = (q * a / p) ^ (1 / q)
    · rw [hxx]
    · exact (h2 x h hxx).le

/-- `lem:app-phase-variation`: Sum and integral, the error bound in `eqn:app-phase-variation`
(`section.tex` l.944–954). Part (ii) of the Lean split.

Let $p,q,a>0$ and $f_a(x)\defeq x^{-p}e^{-ax^{-q}}$ for $x>0$, $f_a(0)\defeq0$.
The function $f_a$ has a unique maximum, at $x=(qa/p)^{1/q}$, with value
$M_{p,q}a^{-p/q}$. For every integer $N\ge1$,
\begin{equation}\label{eqn:app-phase-variation}
\begin{gathered}
\Big|\sum_{i=1}^Nf_a(i)-\int_0^Nf_a(x)\,\dif x\Big|\le2M_{p,q}a^{-p/q},\\
\int_0^Nf_a(x)\,\dif x=\frac{a^{(1-p)/q}}q\int_{a/N^q}^\infty y^{(p-1)/q-1}e^{-y}\,\dif y .
\end{gathered}
\end{equation} -/
theorem lem_app_phase_variation_ii {p q a : ℝ} (hp : 0 < p) (hq : 0 < q) (ha : 0 < a)
    (N : ℕ) (hN : 1 ≤ N) :
    |(∑ i ∈ Finset.Icc 1 N, fa p q a (i : ℝ)) - ∫ x in (0 : ℝ)..(N : ℝ), fa p q a x|
      ≤ 2 * Mpq p q * a ^ (-(p / q)) := by
  have hxs : 0 < (q * a / p) ^ (1 / q) := Real.rpow_pos_of_pos (div_pos (mul_pos hq ha) hp) _
  have hM0 : 0 ≤ Mpq p q * a ^ (-(p / q)) :=
    le_trans (pv_fa_nonneg 0) (pv_le_M hp hq ha 0 le_rfl)
  have hnn : ∀ x ∈ Icc (0:ℝ) N, 0 ≤ fa p q a x := fun x _ => pv_fa_nonneg x
  have hbd : ∀ x ∈ Icc (0:ℝ) N, fa p q a x ≤ Mpq p q * a ^ (-(p / q)) :=
    fun x hx => pv_le_M hp hq ha x hx.1
  set m := ⌊(q * a / p) ^ (1 / q)⌋₊ with hm
  have hmx : (m : ℝ) ≤ (q * a / p) ^ (1 / q) := Nat.floor_le hxs.le
  have hxm : (q * a / p) ^ (1 / q) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hup : ∀ n : ℕ, (n : ℝ) ≤ (q * a / p) ^ (1 / q) → MonotoneOn (fa p q a) (Icc (0:ℝ) n) := by
    intro n hn x hx y hy hxy
    rcases hx.1.eq_or_lt with h | h
    · rw [← h, pv_fa_zero]; exact pv_fa_nonneg _
    · exact pv_mono hp hq ha h hxy (hy.2.trans hn)
  by_cases hmN : N ≤ m
  · have hmx' : (N : ℝ) ≤ (q * a / p) ^ (1 / q) := (by exact_mod_cast hmN : (N:ℝ) ≤ m).trans hmx
    have key := Muon.Foundations.unimodal_sum_sub_integral_le (f := fa p q a) (a := 0) (m := N) (b := N)
      (Nat.zero_le _) le_rfl (by simpa using hnn) (by simpa using hup N hmx')
      (fun x hx y hy hxy => by
        have : x = y := le_antisymm hxy (hy.2.trans hx.1)
        rw [this])
      (M := Mpq p q * a ^ (-(p / q))) (by simpa using hbd)
    have hs : ∑ k ∈ Finset.Icc 0 N, fa p q a (k : ℝ) = ∑ k ∈ Finset.Icc 1 N, fa p q a (k : ℝ) := by
      rw [← Finset.add_sum_erase (Finset.Icc 0 N) (fun k : ℕ => fa p q a (k : ℝ))
        (by simp : 0 ∈ Finset.Icc 0 N)]
      have : (Finset.Icc 0 N).erase 0 = Finset.Icc 1 N := by ext x; simp; omega
      rw [this]; simp [pv_fa_zero]
    simp only [Nat.cast_zero] at key
    rw [hs] at key
    calc _ ≤ _ := key
      _ ≤ _ := by linarith
  · push Not at hmN
    have h := pv_assemble hmN hnn hbd pv_fa_meas pv_fa_zero (hup m hmx) ?_
    · calc _ ≤ _ := h
        _ = _ := by rw [mul_assoc]
    intro x hx y hy hxy
    exact pv_anti hp hq ha (by push_cast at hx; linarith [hx.1]) hxy

/-- `lem:app-phase-variation`: Sum and integral, the integral identity in `eqn:app-phase-variation`
(`section.tex` l.944–954). Part (iii) of the Lean split.

Let $p,q,a>0$ and $f_a(x)\defeq x^{-p}e^{-ax^{-q}}$ for $x>0$, $f_a(0)\defeq0$.
The function $f_a$ has a unique maximum, at $x=(qa/p)^{1/q}$, with value
$M_{p,q}a^{-p/q}$. For every integer $N\ge1$,
\begin{equation}\label{eqn:app-phase-variation}
\begin{gathered}
\Big|\sum_{i=1}^Nf_a(i)-\int_0^Nf_a(x)\,\dif x\Big|\le2M_{p,q}a^{-p/q},\\
\int_0^Nf_a(x)\,\dif x=\frac{a^{(1-p)/q}}q\int_{a/N^q}^\infty y^{(p-1)/q-1}e^{-y}\,\dif y .
\end{gathered}
\end{equation} -/
lemma pt_iii {p q a x : ℝ} (hp : 0 < p) (hq : 0 < q) (ha : 0 < a) (hx : 0 < x) :
    x ^ (-p) = a ^ ((1 - p) / q) / q *
      (|a * (-q * x ^ (-q - 1))| * (a * x ^ (-q)) ^ ((p - 1) / q - 1)) := by
  have hpos : 0 < x ^ (-q - 1) := Real.rpow_pos_of_pos hx _
  have habs : |a * (-q * x ^ (-q - 1))| = a * q * x ^ (-q - 1) := by
    rw [abs_of_neg (by nlinarith [mul_pos (mul_pos ha hq) hpos])]
    ring
  rw [habs]
  have e1 : x ^ (-p) = x ^ (-q - 1) * x ^ (-q * ((p - 1) / q - 1)) := by
    rw [← Real.rpow_add hx]
    congr 1
    field_simp
    ring
  have e2 : (a * x ^ (-q)) ^ ((p - 1) / q - 1)
      = a ^ ((p - 1) / q - 1) * x ^ (-q * ((p - 1) / q - 1)) := by
    rw [Real.mul_rpow ha.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le]
  have e3 : a ^ ((1 - p) / q) * a ^ ((p - 1) / q - 1) * a = 1 := by
    rw [← Real.rpow_add ha, show (1 - p) / q + ((p - 1) / q - 1) = -1 by ring,
      Real.rpow_neg_one]
    field_simp
  rw [e1, e2]
  have e4 : a ^ ((1 - p) / q) / q * (a * q * x ^ (-q - 1) *
      (a ^ ((p - 1) / q - 1) * x ^ (-q * ((p - 1) / q - 1))))
      = x ^ (-q - 1) * x ^ (-q * ((p - 1) / q - 1)) *
        (a ^ ((1 - p) / q) * a ^ ((p - 1) / q - 1) * a) := by
    field_simp
  rw [e4, e3, mul_one]

theorem lem_app_phase_variation_iii {p q a : ℝ} (hp : 0 < p) (hq : 0 < q) (ha : 0 < a)
    (N : ℕ) (hN : 1 ≤ N) :
    ∫ x in (0 : ℝ)..(N : ℝ), fa p q a x =
      a ^ ((1 - p) / q) / q *
        ∫ y in Ioi (a / (N : ℝ) ^ q), y ^ ((p - 1) / q - 1) * Real.exp (-y) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNq : a * (N : ℝ) ^ (-q) = a / (N : ℝ) ^ q := by
    rw [Real.rpow_neg hN0.le]
    ring
  have hneg : -q < 0 := by linarith
  rw [intervalIntegral.integral_of_le hN0.le, integral_Ioc_eq_integral_Ioo]
  have hfeq : ∫ x in Ioo (0 : ℝ) N, fa p q a x
      = ∫ x in Ioo (0 : ℝ) N, x ^ (-p) * Real.exp (-a * x ^ (-q)) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    simp only [fa, hx.1, ↓reduceIte]
  rw [hfeq]
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) N,
      HasDerivWithinAt (fun x : ℝ => a * x ^ (-q)) ((fun x : ℝ => a * (-q * x ^ (-q - 1))) x)
        (Ioo (0 : ℝ) N) x := by
    intro x hx
    exact ((Real.hasDerivAt_rpow_const (Or.inl hx.1.ne')).const_mul a).hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ => a * x ^ (-q)) (Ioo (0 : ℝ) N) := by
    intro x hx y hy hxy
    have h1 : x ^ (-q) = y ^ (-q) := mul_left_cancel₀ ha.ne' hxy
    rcases lt_trichotomy x y with h | h | h
    · have := Real.rpow_lt_rpow_of_neg hx.1 h hneg
      linarith
    · exact h
    · have := Real.rpow_lt_rpow_of_neg hy.1 h hneg
      linarith
  have himg : (fun x : ℝ => a * x ^ (-q)) '' Ioo (0 : ℝ) N = Ioi (a / (N : ℝ) ^ q) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change a / (N : ℝ) ^ q < a * x ^ (-q)
      rw [← hNq]
      exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg hx.1 hx.2 hneg) ha
    · intro hy
      have hy' : a / (N : ℝ) ^ q < y := hy
      have hyp : 0 < y := lt_of_le_of_lt (div_nonneg ha.le (Real.rpow_nonneg hN0.le _)) hy'
      have hx0 : 0 < (a / y) ^ (1 / q) := Real.rpow_pos_of_pos (div_pos ha hyp) _
      have hxq : ((a / y) ^ (1 / q)) ^ (-q) = y / a := by
        rw [← Real.rpow_mul (div_pos ha hyp).le, show 1 / q * -q = (-1 : ℝ) by field_simp,
          Real.rpow_neg_one, inv_div]
      have hax : a * ((a / y) ^ (1 / q)) ^ (-q) = y := by
        rw [hxq]
        field_simp
      have hxN : (a / y) ^ (1 / q) < N := by
        by_contra hcon
        rw [not_lt] at hcon
        have hle : ((N : ℝ)) ^ (-q) ≥ ((a / y) ^ (1 / q)) ^ (-q) := by
          rcases hcon.eq_or_lt with h | h
          · rw [← h]
          · exact (Real.rpow_lt_rpow_of_neg hN0 h hneg).le
        have := mul_le_mul_of_nonneg_left hle ha.le
        linarith
      exact ⟨(a / y) ^ (1 / q), ⟨hx0, hxN⟩, hax⟩
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  simp only [smul_eq_mul]
  rw [pt_iii hp hq ha hx.1]
  ring

/-! ## Convergent power sums -/

lemma pv_range_Icc {g : ℕ → ℝ} (h0 : g 0 = 0) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), g i = ∑ i ∈ Finset.Icc 1 N, g i := by
  induction N with
  | zero => simp [h0]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

lemma pv_fa_le_rpow {p q a : ℝ} (hp : 0 < p) (ha : 0 < a) (x : ℝ) (hx : 0 ≤ x) :
    fa p q a x ≤ x ^ (-p) := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, pv_fa_zero, Real.zero_rpow (neg_ne_zero.mpr hp.ne')]
  · unfold fa
    rw [if_pos h]
    have h1 : 0 ≤ a * x ^ (-q) := mul_nonneg ha.le (Real.rpow_nonneg hx _)
    have h2 : Real.exp (-a * x ^ (-q)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [h1])
    calc x ^ (-p) * Real.exp (-a * x ^ (-q)) ≤ x ^ (-p) * 1 :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx _)
      _ = x ^ (-p) := mul_one _

/-- `lem:app-phase-laplace`: Convergent power sums (`section.tex` l.972–978), part (i).

Let $p>1$, $q>0$ and $d\defeq(p-1)/q$. For every $a>0$,
\begin{equation}\label{eqn:app-phase-laplace}
\Big|\sum_{i\ge1}i^{-p}e^{-ai^{-q}}-\frac{\Gamma(d)}q\,a^{-d}\Big|\le2M_{p,q}a^{-p/q},
\end{equation}
and for every integer $N\ge1$, $0\le\sum_{i>N}i^{-p}\le N^{1-p}/(p-1)$. -/
theorem lem_app_phase_laplace_i {p q a : ℝ} (hp : 1 < p) (hq : 0 < q) (ha : 0 < a) :
    |(∑' i : ℕ, if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-a * (i : ℝ) ^ (-q)) else 0)
        - Real.Gamma ((p - 1) / q) / q * a ^ (-((p - 1) / q))|
      ≤ 2 * Mpq p q * a ^ (-(p / q)) := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < (p - 1) / q := div_pos (by linarith) hq
  have hF : (fun i : ℕ => if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-a * (i : ℝ) ^ (-q)) else 0)
      = fun i : ℕ => fa p q a (i : ℝ) := by
    funext i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [fa]
    · have hi' : (0 : ℝ) < i := Nat.cast_pos.mpr hi
      simp [fa, hi, hi']
  rw [hF]
  have hsum_pow : Summable (fun i : ℕ => (i : ℝ) ^ (-p)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hgs : Summable (fun i : ℕ => fa p q a (i : ℝ)) :=
    Summable.of_nonneg_of_le (fun i => pv_fa_nonneg _)
      (fun i => pv_fa_le_rpow hp0 ha (i : ℝ) (Nat.cast_nonneg i)) hsum_pow
  have hS : Tendsto (fun N : ℕ => ∑ i ∈ Finset.Icc 1 N, fa p q a (i : ℝ)) atTop
      (𝓝 (∑' i : ℕ, fa p q a (i : ℝ))) := by
    have h := hgs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine Tendsto.congr (fun N => ?_) h
    exact pv_range_Icc (g := fun i : ℕ => fa p q a (i : ℝ)) (by simp [fa]) N
  -- the Gamma integral over (0, ∞) as a limit of integrals over (a/(n+1)^q, ∞)
  have hmono : Monotone (fun n : ℕ => Ioi (a / ((n : ℝ) + 1) ^ q)) := by
    intro m n hmn
    dsimp only
    apply Set.Ioi_subset_Ioi
    have hm : ((m : ℝ) + 1) ^ q ≤ ((n : ℝ) + 1) ^ q :=
      Real.rpow_le_rpow (by positivity)
        (by have : (m : ℝ) ≤ n := by exact_mod_cast hmn
            linarith) hq.le
    exact div_le_div_of_nonneg_left ha.le (Real.rpow_pos_of_pos (by positivity) _) hm
  have hu : (⋃ n : ℕ, Ioi (a / ((n : ℝ) + 1) ^ q)) = Ioi 0 := by
    ext y
    simp only [mem_iUnion, mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩
      exact lt_trans (by positivity) hn
    · intro hy
      have h1 : ∀ᶠ x : ℝ in atTop, a / y < x ^ q :=
        (tendsto_rpow_atTop hq).eventually_gt_atTop _
      have h2 : ∀ᶠ n : ℕ in atTop, a / y < ((n : ℝ) + 1) ^ q :=
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).eventually h1
      obtain ⟨n, hn⟩ := h2.exists
      refine ⟨n, ?_⟩
      have hX : 0 < ((n : ℝ) + 1) ^ q := Real.rpow_pos_of_pos (by positivity) _
      rw [div_lt_iff₀ hX]
      rw [div_lt_iff₀ hy] at hn
      linarith
  have hfi : IntegrableOn (fun y : ℝ => y ^ ((p - 1) / q - 1) * Real.exp (-y)) (Ioi 0) := by
    refine (Real.GammaIntegral_convergent hd).congr_fun (fun x _ => mul_comm _ _) measurableSet_Ioi
  have hK := tendsto_setIntegral_of_monotone (μ := volume)
    (f := fun y : ℝ => y ^ ((p - 1) / q - 1) * Real.exp (-y))
    (s := fun n : ℕ => Ioi (a / ((n : ℝ) + 1) ^ q)) (fun n => measurableSet_Ioi) hmono
    (by rw [hu]; exact hfi)
  rw [hu] at hK
  have hGam : ∫ y in Ioi (0 : ℝ), y ^ ((p - 1) / q - 1) * Real.exp (-y) = Real.Gamma ((p - 1) / q) := by
    rw [Real.Gamma_eq_integral hd]
    congr 1
    funext y
    ring
  rw [hGam] at hK
  have hI : Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..((n + 1 : ℕ) : ℝ), fa p q a x) atTop
      (𝓝 (a ^ ((1 - p) / q) / q * Real.Gamma ((p - 1) / q))) := by
    refine Tendsto.congr (fun n => ?_) (hK.const_mul (a ^ ((1 - p) / q) / q))
    rw [lem_app_phase_variation_iii hp0 hq ha (n + 1) (by omega), Nat.cast_add, Nat.cast_one]
  have hI' : Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ), fa p q a x) atTop
      (𝓝 (a ^ ((1 - p) / q) / q * Real.Gamma ((p - 1) / q))) :=
    (tendsto_add_atTop_iff_nat 1).mp hI
  have hval : a ^ ((1 - p) / q) / q * Real.Gamma ((p - 1) / q)
      = Real.Gamma ((p - 1) / q) / q * a ^ (-((p - 1) / q)) := by
    rw [show (1 - p) / q = -((p - 1) / q) by ring]
    ring
  rw [hval] at hI'
  have hlim : Tendsto (fun N : ℕ => |(∑ i ∈ Finset.Icc 1 N, fa p q a (i : ℝ))
      - ∫ x in (0 : ℝ)..(N : ℝ), fa p q a x|) atTop
      (𝓝 |(∑' i : ℕ, fa p q a (i : ℝ)) - Real.Gamma ((p - 1) / q) / q * a ^ (-((p - 1) / q))|) := by
    have h := hS.sub hI'
    exact h.abs
  have key := le_of_tendsto hlim (eventually_atTop.mpr ⟨1, fun N hN =>
    lem_app_phase_variation_ii hp0 hq ha N hN⟩)
  exact key

/-- `lem:app-phase-laplace`: Convergent power sums (`section.tex` l.972–978), part (ii).

Let $p>1$, $q>0$ and $d\defeq(p-1)/q$. For every $a>0$,
\begin{equation}\label{eqn:app-phase-laplace}
\Big|\sum_{i\ge1}i^{-p}e^{-ai^{-q}}-\frac{\Gamma(d)}q\,a^{-d}\Big|\le2M_{p,q}a^{-p/q},
\end{equation}
and for every integer $N\ge1$, $0\le\sum_{i>N}i^{-p}\le N^{1-p}/(p-1)$. -/
theorem lem_app_phase_laplace_ii {p : ℝ} (hp : 1 < p) (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ tailSum p N ∧ tailSum p N ≤ (N : ℝ) ^ (1 - p) / (p - 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum_pow : Summable (fun i : ℕ => (i : ℝ) ^ (-p)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, g = fun i => if N < i then (i : ℝ) ^ (-p) else 0 := ⟨_, rfl⟩
  have hTg : tailSum p N = ∑' i : ℕ, g i := by rw [hg]; rfl
  have hgnn : ∀ i, 0 ≤ g i := by
    intro i
    rw [hg]
    dsimp only
    split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg i) _
    · exact le_rfl
  have hgle : ∀ i, g i ≤ (i : ℝ) ^ (-p) := by
    intro i
    rw [hg]
    dsimp only
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (Nat.cast_nonneg i) _
  have hgs : Summable g := Summable.of_nonneg_of_le hgnn hgle hsum_pow
  have hzero : ∑ i ∈ Finset.range (N + 1), g i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i < N + 1 := Finset.mem_range.mp hi
    rw [hg]
    dsimp only
    rw [if_neg (by omega)]
  have hshift : ∀ n : ℕ, g (n + (N + 1)) = ((n + N + 1 : ℕ) : ℝ) ^ (-p) := by
    intro n
    rw [hg]
    dsimp only
    rw [if_pos (by omega), show n + (N + 1) = n + N + 1 by omega]
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-p)) (Set.Ici (N : ℝ)) := by
    intro x hx y _ hxy
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hNpos hx
    exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have hintegrable : IntegrableOn (fun x : ℝ => x ^ (-p)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hNpos
  have hnonneg : ∀ t ∈ Set.Ioi (N : ℝ), 0 ≤ t ^ (-p) := fun t ht =>
    Real.rpow_nonneg (lt_trans hNpos ht).le _
  have hint : ∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-p) ≤ ∫ x in Set.Ioi (N : ℝ), x ^ (-p) :=
    AntitoneOn.tsum_comp_add_le_integral N hanti hintegrable hnonneg
  rw [integral_Ioi_rpow_of_lt (by linarith) hNpos] at hint
  have hval : -(N : ℝ) ^ (-p + 1) / (-p + 1) = (N : ℝ) ^ (1 - p) / (p - 1) := by
    rw [show -p + 1 = 1 - p by ring, show (1 : ℝ) - p = -(p - 1) by ring, neg_div_neg_eq]
  rw [hval] at hint
  have hsplit : ∑' i : ℕ, g i = ∑' n : ℕ, g (n + (N + 1)) := by
    rw [← hgs.sum_add_tsum_nat_add (N + 1), hzero, zero_add]
  rw [hTg]
  refine ⟨tsum_nonneg hgnn, ?_⟩
  rw [hsplit]
  simp only [hshift]
  exact hint

/-! ## Finite power sums -/

lemma ps_summable {a : ℝ} (ha : 1 < a) :
    Summable (fun i : ℕ => if 0 < i then (i : ℝ) ^ (-a) else 0) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    (Real.summable_nat_rpow.mpr (by linarith : -a < -1))
  · split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg i) _
    · exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (Nat.cast_nonneg i) _

lemma ps_term_summable {a q u : ℝ} (ha : 1 < a) (hu : 0 ≤ u) :
    Summable (fun i : ℕ =>
      if 0 < i then (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (ps_summable ha)
  · split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le
    · exact le_rfl
  · split_ifs
    · have hx : -(2 * u) * (i : ℝ) ^ (-q) ≤ 0 := by
        nlinarith [mul_nonneg hu (Real.rpow_nonneg (Nat.cast_nonneg i) (-q))]
      exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg i) _)
        (Real.exp_le_one_iff.mpr hx)
    · exact le_rfl

lemma ps_zeta_le {a : ℝ} (ha : 1 < a) :
    ∑' i : ℕ, (if 0 < i then (i : ℝ) ^ (-a) else 0) ≤ Za a := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-a)) (Set.Ici ((1 : ℕ) : ℝ)) := by
    intro x hx y _ hxy
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos (by simpa using hx)
    exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have hintegrable : IntegrableOn (fun x : ℝ => x ^ (-a)) (Set.Ioi ((1 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hnonneg : ∀ t ∈ Set.Ioi ((1 : ℕ) : ℝ), 0 ≤ t ^ (-a) := fun t ht => by
    have h1 : (1 : ℝ) < t := by exact_mod_cast Set.mem_Ioi.mp ht
    exact Real.rpow_nonneg (by linarith) _
  have hval : ∫ x in Set.Ioi ((1 : ℕ) : ℝ), x ^ (-a) = 1 / (a - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) (by norm_num), Nat.cast_one, Real.one_rpow]
    rw [show -a + 1 = -(a - 1) by ring, neg_div_neg_eq]
  have hint : ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-a) ≤ 1 / (a - 1) :=
    (AntitoneOn.tsum_comp_add_le_integral 1 hanti hintegrable hnonneg).trans hval.le
  have hgs := ps_summable ha
  have hfin : ∑' i : ℕ, (if 0 < i then (i : ℝ) ^ (-a) else 0)
      = 1 + ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-a) := by
    rw [← hgs.sum_add_tsum_nat_add 2]
    have h2 : ∑ i ∈ Finset.range 2, (if 0 < i then (i : ℝ) ^ (-a) else 0) = 1 := by
      simp [Finset.sum_range_succ]
    have h3 : ∑' n : ℕ, (if 0 < n + 2 then ((n + 2 : ℕ) : ℝ) ^ (-a) else 0)
        = ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-a) :=
      tsum_congr (fun n => by
        simp only [show 0 < n + 2 by omega, if_true])
    rw [h2, h3]
  rw [hfin]
  unfold Za
  linarith [hint]

/-- `lem:app-phase-sums`: Finite power sums (`section.tex` l.1002–1010), part (i).

Let $a>1$ and $q>0$. For every $N\in\N\cup\{\infty\}$ and $u\ge0$,
$L_{N,a,q}(u)\le E_{a,q}(1+u)^{-d(a,q)}$. -/
theorem lem_app_phase_sums_i {a q : ℝ} (ha : 1 < a) (hq : 0 < q) (N : ℕ∞) {u : ℝ}
    (hu : 0 ≤ u) :
    Lsum N a q u ≤ Epq a q * (1 + u) ^ (-dAQ a q) := by
  have ha0 : 0 < a := by linarith
  have hq0 : q ≠ 0 := hq.ne'
  have hd_pos : 0 < dAQ a q := div_pos (by linarith) hq
  have hpow_pos : 0 < (1 + u) ^ (-dAQ a q) := Real.rpow_pos_of_pos (by linarith) _
  have hZa0 : 0 < Za a := by
    unfold Za
    have := div_pos one_pos (show (0 : ℝ) < a - 1 by linarith)
    linarith
  have h4 : (2 : ℝ) ^ dAQ a q * (2 : ℝ) ^ (-dAQ a q) = 1 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hEpq1 : (2 : ℝ) ^ dAQ a q * Za a ≤ Epq a q := by unfold Epq; exact le_max_left _ _
  have hEpq2 : Real.Gamma (dAQ a q) / q + (2 : ℝ) ^ (1 - 1 / q) * Mpq a q ≤ Epq a q := by
    unfold Epq; exact le_max_right _ _
  have hterm_le : ∀ i : ℕ,
      (if 0 < i ∧ ((i : ℕ∞) ≤ N) then (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0)
        ≤ (if 0 < i then (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) := by
    intro i
    by_cases h : 0 < i ∧ ((i : ℕ∞) ≤ N)
    · rw [if_pos h, if_pos h.1]
    · rw [if_neg h]
      split_ifs
      · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le
      · exact le_rfl
  have hsumS := ps_term_summable (q := q) ha hu
  have hsumL : Summable (fun i : ℕ =>
      if 0 < i ∧ ((i : ℕ∞) ≤ N) then (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) hterm_le hsumS
    by_cases h : 0 < i ∧ ((i : ℕ∞) ≤ N)
    · rw [if_pos h]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le
    · rw [if_neg h]
  have hL : Lsum N a q u ≤ ∑' i : ℕ,
      (if 0 < i then (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) := by
    unfold Lsum
    exact Summable.tsum_le_tsum hterm_le hsumL hsumS
  rcases le_total u 1 with hu1 | hu1
  · -- 0 ≤ u ≤ 1: integral comparison and (1+u)^{-d} ≥ 2^{-d}
    have hS1 : ∑' i : ℕ,
        (if 0 < i then (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) ≤ Za a := by
      refine le_trans (Summable.tsum_le_tsum (fun i => ?_) hsumS (ps_summable ha))
        (ps_zeta_le ha)
      split_ifs
      · exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg i) _)
          (Real.exp_le_one_iff.mpr (by
            nlinarith [mul_nonneg hu (Real.rpow_nonneg (Nat.cast_nonneg i) (-q))]))
      · exact le_rfl
    have hLu : Lsum N a q u ≤ Za a := le_trans hL hS1
    have hpow2 : (2 : ℝ) ^ (-dAQ a q) ≤ (1 + u) ^ (-dAQ a q) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    calc Lsum N a q u ≤ Za a := hLu
      _ = ((2 : ℝ) ^ dAQ a q * Za a) * (2 : ℝ) ^ (-dAQ a q) := by
          linear_combination (-Za a) * h4
      _ ≤ ((2 : ℝ) ^ dAQ a q * Za a) * (1 + u) ^ (-dAQ a q) :=
          mul_le_mul_of_nonneg_left hpow2 (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hZa0).le
      _ ≤ Epq a q * (1 + u) ^ (-dAQ a q) := mul_le_mul_of_nonneg_right hEpq1 hpow_pos.le
  · -- u ≥ 1: Laplace bound with 2u in place of a
    have hu0 : 0 < u := by linarith
    have hlap := lem_app_phase_laplace_i (p := a) (q := q) (a := 2 * u) ha hq (by linarith)
    have hupper := (abs_le.mp hlap).2
    have hdA : (a - 1) / q = dAQ a q := rfl
    rw [hdA] at hupper
    have hA : (2 * u) ^ (-dAQ a q) = (2 : ℝ) ^ (-dAQ a q) * u ^ (-dAQ a q) :=
      Real.mul_rpow (by norm_num) hu0.le
    have hB : (2 * u) ^ (-(a / q)) = (2 : ℝ) ^ (-(a / q)) * u ^ (-(a / q)) :=
      Real.mul_rpow (by norm_num) hu0.le
    have hC : u ^ (-(a / q)) ≤ u ^ (-dAQ a q) := by
      apply Real.rpow_le_rpow_of_exponent_le hu1
      unfold dAQ
      have : (a - 1) / q ≤ a / q := div_le_div_of_nonneg_right (by linarith) hq.le
      linarith
    have hD : u ^ (-dAQ a q) ≤ (2 : ℝ) ^ dAQ a q * (1 + u) ^ (-dAQ a q) := by
      have h1 : (2 * u) ^ (-dAQ a q) ≤ (1 + u) ^ (-dAQ a q) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
      rw [hA] at h1
      calc u ^ (-dAQ a q) = (2 : ℝ) ^ dAQ a q * ((2 : ℝ) ^ (-dAQ a q) * u ^ (-dAQ a q)) := by
            linear_combination (-(u ^ (-dAQ a q))) * h4
        _ ≤ (2 : ℝ) ^ dAQ a q * (1 + u) ^ (-dAQ a q) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos (by norm_num) _).le
    have hG0 : 0 ≤ Real.Gamma (dAQ a q) / q :=
      div_nonneg (Real.Gamma_pos_of_pos hd_pos).le hq.le
    have hM0 : 0 ≤ Mpq a q := by
      unfold Mpq
      exact Real.rpow_nonneg (div_nonneg ha0.le (mul_nonneg (Real.exp_pos 1).le hq.le)) _
    have hX0 : 0 ≤ 2 * Mpq a q * (2 : ℝ) ^ (-(a / q)) :=
      mul_nonneg (mul_nonneg (by norm_num) hM0) (Real.rpow_pos_of_pos (by norm_num) _).le
    have hG2 : 0 ≤ Real.Gamma (dAQ a q) / q * (2 : ℝ) ^ (-dAQ a q) :=
      mul_nonneg hG0 (Real.rpow_pos_of_pos (by norm_num) _).le
    have hS2 : ∑' i : ℕ,
        (if 0 < i then (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0)
        ≤ (Real.Gamma (dAQ a q) / q * (2 : ℝ) ^ (-dAQ a q)
            + 2 * Mpq a q * (2 : ℝ) ^ (-(a / q))) * u ^ (-dAQ a q) := by
      have hC' := mul_le_mul_of_nonneg_left hC hX0
      rw [hA, hB] at hupper
      linarith [hC', hupper]
    have hfinal : (Real.Gamma (dAQ a q) / q * (2 : ℝ) ^ (-dAQ a q)
            + 2 * Mpq a q * (2 : ℝ) ^ (-(a / q))) * u ^ (-dAQ a q)
        ≤ (Real.Gamma (dAQ a q) / q * (2 : ℝ) ^ (-dAQ a q)
            + 2 * Mpq a q * (2 : ℝ) ^ (-(a / q))) * ((2 : ℝ) ^ dAQ a q * (1 + u) ^ (-dAQ a q)) :=
      mul_le_mul_of_nonneg_left hD (add_nonneg hG2 hX0)
    have hkey : (2 : ℝ) ^ (1 - 1 / q) = (2 : ℝ) ^ dAQ a q * (2 * (2 : ℝ) ^ (-(a / q))) := by
      have e : (1 - 1 / q) = dAQ a q + (1 + -(a / q)) := by unfold dAQ; ring
      rw [e, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        Real.rpow_one]
    calc Lsum N a q u ≤ ∑' i : ℕ,
          (if 0 < i then (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) := hL
      _ ≤ (Real.Gamma (dAQ a q) / q * (2 : ℝ) ^ (-dAQ a q)
            + 2 * Mpq a q * (2 : ℝ) ^ (-(a / q))) * u ^ (-dAQ a q) := hS2
      _ ≤ (Real.Gamma (dAQ a q) / q * (2 : ℝ) ^ (-dAQ a q)
            + 2 * Mpq a q * (2 : ℝ) ^ (-(a / q))) * ((2 : ℝ) ^ dAQ a q * (1 + u) ^ (-dAQ a q)) :=
          hfinal
      _ = (Real.Gamma (dAQ a q) / q + (2 : ℝ) ^ (1 - 1 / q) * Mpq a q) * (1 + u) ^ (-dAQ a q) := by
          rw [hkey]
          linear_combination (Real.Gamma (dAQ a q) / q * (1 + u) ^ (-dAQ a q)) * h4
      _ ≤ Epq a q * (1 + u) ^ (-dAQ a q) :=
          mul_le_mul_of_nonneg_right (by linarith [hEpq2]) hpow_pos.le

/-- `lem:app-phase-sums`: Finite power sums (`section.tex` l.1002–1010), part (ii).

Let $a>1$ and $q>0$. For every integer $N\ge4$ and $0\le u\le(N/4)^q$,
$\frac12L_{N,a,q}(u)\ge A_a(1+u)^{-d(a,q)}$. -/
theorem lem_app_phase_sums_ii {a q : ℝ} (ha : 1 < a) (hq : 0 < q) (N : ℕ) (hN : 4 ≤ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ ((N : ℝ) / 4) ^ q) :
    Aconst a * (1 + u) ^ (-dAQ a q) ≤ (1 / 2) * Lsum (N : ℕ∞) a q u := by
  have ha0 : 0 < a := by linarith
  have hq0 : q ≠ 0 := hq.ne'
  have hd_pos : 0 < dAQ a q := div_pos (by linarith) hq
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hfin : Lsum (N : ℕ∞) a q u
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
  have hAc0 : 0 ≤ Aconst a := by
    unfold Aconst
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_pos _).le
  have hE2 : 0 ≤ Real.exp (-2) := (Real.exp_pos _).le
  rcases le_total u 1 with hu1 | hu1
  · -- 0 ≤ u ≤ 1: the i = 1 term alone gives the bound
    have hsingle : ((1 : ℕ) : ℝ) ^ (-a) * Real.exp (-(2 * u) * ((1 : ℕ) : ℝ) ^ (-q))
        ≤ ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) :=
      Finset.single_le_sum (f := fun i : ℕ => (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)))
        (fun i _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le)
        (by rw [Finset.mem_Icc]; omega)
    simp only [Nat.cast_one, Real.one_rpow, one_mul, mul_one] at hsingle
    have hexp : Real.exp (-2) ≤ Real.exp (-(2 * u)) := Real.exp_le_exp.mpr (by linarith)
    have hA2 : (2 : ℝ) ^ (-(2 * a)) ≤ 1 / 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show -(2 * a) ≤ (-2 : ℝ) by linarith)
      have h2 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]; norm_num
      calc (2 : ℝ) ^ (-(2 * a)) ≤ (2 : ℝ) ^ (-2 : ℝ) := h
        _ = 1 / 4 := h2
        _ ≤ 1 / 2 := by norm_num
    have hpow1 : (1 + u) ^ (-dAQ a q) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    calc Aconst a * (1 + u) ^ (-dAQ a q) ≤ Aconst a * 1 :=
          mul_le_mul_of_nonneg_left hpow1 hAc0
      _ = (2 : ℝ) ^ (-(2 * a)) * Real.exp (-2) := by unfold Aconst; ring
      _ ≤ (1 / 2) * Real.exp (-2) := mul_le_mul_of_nonneg_right hA2 hE2
      _ ≤ (1 / 2) * Real.exp (-(2 * u)) := mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ ≤ (1 / 2) * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) :=
          mul_le_mul_of_nonneg_left hsingle (by norm_num)
      _ = (1 / 2) * Lsum (N : ℕ∞) a q u := by rw [hfin]
  · -- 1 ≤ u ≤ (N/4)^q: j = ⌈u^{1/q}⌉ indices j ≤ i < 2j
    have ht0 : (0 : ℝ) ≤ u := by linarith
    set t : ℝ := u ^ q⁻¹ with ht_def
    have ht1 : 1 ≤ t := Real.one_le_rpow hu1 (inv_nonneg.mpr hq.le)
    have htq : t ^ q = u := Real.rpow_inv_rpow ht0 hq0
    have htN : t ≤ (N : ℝ) / 4 := by
      have h1 : u ^ q⁻¹ ≤ (((N : ℝ) / 4) ^ q) ^ q⁻¹ :=
        Real.rpow_le_rpow ht0 hu (inv_nonneg.mpr hq.le)
      rw [Real.rpow_rpow_inv (by positivity) hq0] at h1
      exact h1
    set j : ℕ := ⌈t⌉₊ with hj_def
    have hjt : t ≤ (j : ℝ) := Nat.le_ceil t
    have hjt' : (j : ℝ) < t + 1 := Nat.ceil_lt_add_one (by linarith)
    have hj1r : (1 : ℝ) ≤ j := by linarith
    have hj1 : 1 ≤ j := by exact_mod_cast hj1r
    have hj0 : (0 : ℝ) < j := by linarith
    have hj2 : 2 * j ≤ N := by
      have h : ((2 * j : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; linarith
      exact_mod_cast h
    have hterm : ∀ i ∈ Finset.Ico j (2 * j),
        ((2 : ℝ) * j) ^ (-a) * Real.exp (-2)
          ≤ (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i by omega)
      have hi0 : (0 : ℝ) < i := by linarith
      have hji : (j : ℝ) ≤ i := by exact_mod_cast hi.1
      have hi2j : (i : ℝ) ≤ 2 * j := by exact_mod_cast (show i ≤ 2 * j by omega)
      have hp1 : ((2 : ℝ) * j) ^ (-a) ≤ (i : ℝ) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos hi0 hi2j (by linarith)
      have hiq : u ≤ (i : ℝ) ^ q := by
        rw [← htq]
        exact Real.rpow_le_rpow (by linarith) (by linarith [hjt, hji]) hq.le
      have hu_inv : u * (i : ℝ) ^ (-q) ≤ 1 := by
        rw [Real.rpow_neg hi0.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hi0 q)]
        exact hiq
      have hexp2 : Real.exp (-2) ≤ Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) := by
        apply Real.exp_le_exp.mpr
        have e : -(2 * u) * (i : ℝ) ^ (-q) = -2 * (u * (i : ℝ) ^ (-q)) := by ring
        rw [e]
        linarith
      exact mul_le_mul hp1 hexp2 hE2 (Real.rpow_nonneg hi0.le _)
    have hsub : Finset.Ico j (2 * j) ⊆ Finset.Icc 1 N := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hcard : (Finset.Ico j (2 * j)).card = j := by
      rw [Nat.card_Ico]; omega
    have hLb : (j : ℝ) * (((2 : ℝ) * j) ^ (-a) * Real.exp (-2))
        ≤ Lsum (N : ℕ∞) a q u := by
      rw [hfin]
      calc (j : ℝ) * (((2 : ℝ) * j) ^ (-a) * Real.exp (-2))
          = ∑ i ∈ Finset.Ico j (2 * j), ((2 : ℝ) * j) ^ (-a) * Real.exp (-2) := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
        _ ≤ ∑ i ∈ Finset.Ico j (2 * j),
              (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) := Finset.sum_le_sum hterm
        _ ≤ ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun i _ _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le)
    have hmul : (j : ℝ) * (((2 : ℝ) * j) ^ (-a) * Real.exp (-2))
        = (2 : ℝ) ^ (-a) * (j : ℝ) ^ (-(a - 1)) * Real.exp (-2) := by
      have hQ : (j : ℝ) * (j : ℝ) ^ (-a) = (j : ℝ) ^ (-(a - 1)) := by
        rw [show -(a - 1) = 1 + -a by ring, Real.rpow_add hj0, Real.rpow_one]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hj0.le, ← hQ]
      ring
    have hjz : ((j : ℝ) / 2) ^ (-(a - 1)) = (2 : ℝ) ^ (a - 1) * (j : ℝ) ^ (-(a - 1)) := by
      rw [Real.div_rpow hj0.le (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      ring
    have hu_bd : (1 + u) ^ (-dAQ a q) ≤ (2 : ℝ) ^ (a - 1) * (j : ℝ) ^ (-(a - 1)) := by
      have h1 : (1 + u) ^ (-dAQ a q) ≤ u ^ (-dAQ a q) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
      have h2 : u ^ (-dAQ a q) = t ^ (-(a - 1)) := by
        rw [← htq, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ t)]
        congr 1
        unfold dAQ
        field_simp
      have h3 : t ^ (-(a - 1)) ≤ ((j : ℝ) / 2) ^ (-(a - 1)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
      rw [hjz] at h3
      linarith
    have hLs := hLb
    rw [hmul] at hLs
    have hpow2 : (2 : ℝ) ^ (-(2 * a)) * (2 : ℝ) ^ (a - 1) = (1 / 2) * (2 : ℝ) ^ (-a) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), show -(2 * a) + (a - 1) = -a + -1 by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_neg_one]
      ring
    calc Aconst a * (1 + u) ^ (-dAQ a q)
        ≤ Aconst a * ((2 : ℝ) ^ (a - 1) * (j : ℝ) ^ (-(a - 1))) :=
          mul_le_mul_of_nonneg_left hu_bd hAc0
      _ = (1 / 2) * ((2 : ℝ) ^ (-a) * (j : ℝ) ^ (-(a - 1)) * Real.exp (-2)) := by
          unfold Aconst
          linear_combination ((j : ℝ) ^ (-(a - 1)) * Real.exp (-2)) * hpow2
      _ ≤ (1 / 2) * Lsum (N : ℕ∞) a q u := mul_le_mul_of_nonneg_left hLs (by norm_num)

/-! ## Harmonic sums -/

lemma hh_anti {a : ℝ} (ha : 0 < a) {s : Set ℝ} (hs : s ⊆ Set.Ici 1) :
    AntitoneOn (fun x : ℝ => x ^ (-a)) s := by
  intro x hx y hy hxy
  have hx1 : (0 : ℝ) < x := lt_of_lt_of_le one_pos (Set.mem_Ici.mp (hs hx))
  exact Real.rpow_le_rpow_of_nonpos hx1 hxy (by linarith)

lemma hh_int {a : ℝ} (ha : 0 < a) {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    IntervalIntegrable (fun x : ℝ => x ^ (-a)) MeasureTheory.volume p q := by
  apply AntitoneOn.intervalIntegrable
  rw [Set.uIcc_of_le hpq]
  exact hh_anti ha (fun x hx => le_trans hp hx.1)

lemma hh_step_up {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    ∫ x in (n : ℝ)..((n : ℝ) + 1), x ^ (-a) ≤ (n : ℝ) ^ (-a) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-a)) (Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ)) :=
    hh_anti ha (fun x hx => le_trans (by exact_mod_cast hn) hx.1)
  have h := AntitoneOn.integral_le_sum_Ico (f := fun x : ℝ => x ^ (-a)) (a := n) (b := n + 1)
    (by omega) hanti
  rw [Nat.Ico_succ_singleton, Finset.sum_singleton] at h
  push_cast at h
  exact h

lemma hh_step_low {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) + 1) ^ (-a) ≤ ∫ x in (n : ℝ)..((n : ℝ) + 1), x ^ (-a) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-a)) (Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ)) :=
    hh_anti ha (fun x hx => le_trans (by exact_mod_cast hn) hx.1)
  have h := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x ^ (-a)) (a := n) (b := n + 1)
    (by omega) hanti
  rw [Nat.Ico_succ_singleton, Finset.sum_singleton] at h
  push_cast at h
  exact h

lemma hh_lower {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∫ x in (1 : ℝ)..((n : ℝ) + 1), x ^ (-a) ≤ Hsum a n := by
  induction n with
  | zero => simp [Hsum]
  | succ n ih =>
    have hn1 : 1 ≤ n + 1 := by omega
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hup := hh_step_up ha hn1
    push_cast at hup ⊢
    have hH : Hsum a (n + 1) = Hsum a n + ((n : ℝ) + 1) ^ (-a) := by
      unfold Hsum
      rw [Finset.sum_Icc_succ_top hn1]
      push_cast
      ring
    rw [hH, ← intervalIntegral.integral_add_adjacent_intervals
      (hh_int (p := 1) (q := (n : ℝ) + 1) ha le_rfl (by linarith))
      (hh_int (p := (n : ℝ) + 1) (q := (n : ℝ) + 1 + 1) ha (by linarith) (by linarith))]
    linarith

lemma hh_upper {a : ℝ} (ha : 0 < a) (n : ℕ) (hn : 1 ≤ n) :
    Hsum a n ≤ 1 + ∫ x in (1 : ℝ)..(n : ℝ), x ^ (-a) := by
  induction n, hn using Nat.le_induction with
  | base => simp [Hsum]
  | succ n hn ih =>
    have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hstep := hh_step_low ha hn
    have i1 : IntervalIntegrable (fun x : ℝ => x ^ (-a)) MeasureTheory.volume 1 (n : ℝ) :=
      hh_int ha le_rfl hn1r
    have i2 : IntervalIntegrable (fun x : ℝ => x ^ (-a)) MeasureTheory.volume (n : ℝ)
        ((n : ℝ) + 1) := hh_int ha hn1r (by linarith)
    have hsplit : ∫ x in (1 : ℝ)..((n : ℝ) + 1), x ^ (-a)
        = (∫ x in (1 : ℝ)..(n : ℝ), x ^ (-a)) + ∫ x in (n : ℝ)..((n : ℝ) + 1), x ^ (-a) :=
      (intervalIntegral.integral_add_adjacent_intervals i1 i2).symm
    have hH : Hsum a (n + 1) = Hsum a n + ((n : ℝ) + 1) ^ (-a) := by
      unfold Hsum
      rw [Finset.sum_Icc_succ_top (by omega)]
      push_cast
      ring
    push_cast
    rw [hH]
    linarith

/-- `lem:app-phase-harmonic`: Harmonic sums (`section.tex` l.1048–1057), part (i).

For $a>0$ and $N\ge1$ let $H_N(a)\defeq\sum_{i=1}^Ni^{-a}$. Then
$\int_1^{N+1}x^{-a}\,\dif x\le H_N(a)\le1+\int_1^Nx^{-a}\,\dif x$. -/
theorem lem_app_phase_harmonic_i {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 ≤ N) :
    ∫ x in (1 : ℝ)..((N : ℝ) + 1), x ^ (-a) ≤ Hsum a N ∧
      Hsum a N ≤ 1 + ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-a) :=
  ⟨hh_lower ha N, hh_upper ha N hN⟩

/-- `lem:app-phase-harmonic`: Harmonic sums (`section.tex` l.1048–1057), part (ii).

For $a>0$ and $N\ge1$ let $H_N(a)\defeq\sum_{i=1}^Ni^{-a}$. Then $H_N(a)\ge N^{1-a}$ for
$a\le1$. -/
theorem lem_app_phase_harmonic_ii {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (1 - a) ≤ Hsum a N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hterm : ∀ i ∈ Finset.Icc 1 N, (N : ℝ) ^ (-a) ≤ (i : ℝ) ^ (-a) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
    exact Real.rpow_le_rpow_of_nonpos hi0 (by exact_mod_cast hi.2) (by linarith)
  have hsum : (N : ℝ) ^ (1 - a) = ∑ _i ∈ Finset.Icc 1 N, (N : ℝ) ^ (-a) := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
      show (1 : ℝ) - a = 1 + -a by ring, Real.rpow_add hNpos, Real.rpow_one]
  unfold Hsum
  rw [hsum]
  exact Finset.sum_le_sum hterm

/-- `lem:app-phase-harmonic`: Harmonic sums (`section.tex` l.1048–1057), part (iii).

As $N\to\infty$, $H_N(a)\sim N^{1-a}/(1-a)$ for $0<a<1$. -/
theorem lem_app_phase_harmonic_iii {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    IsEquivalent atTop (fun N : ℕ => Hsum a N) (fun N : ℕ => (N : ℝ) ^ (1 - a) / (1 - a)) := by
  have hc : 0 < 1 - a := by linarith
  have hbounds : ∀ N : ℕ, 1 ≤ N →
      ((N : ℝ) ^ (1 - a) - 1) / (1 - a) ≤ Hsum a N ∧
        Hsum a N ≤ 1 + ((N : ℝ) ^ (1 - a) - 1) / (1 - a) := by
    intro N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hint : ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-a) = ((N : ℝ) ^ (1 - a) - 1) / (1 - a) := by
      rw [integral_rpow (Or.inl (by linarith)), show -a + 1 = 1 - a by ring, Real.one_rpow]
    have hint' : ((N : ℝ) ^ (1 - a) - 1) / (1 - a) ≤ ∫ x in (1 : ℝ)..((N : ℝ) + 1), x ^ (-a) := by
      rw [integral_rpow (Or.inl (by linarith)), show -a + 1 = 1 - a by ring, Real.one_rpow]
      refine div_le_div_of_nonneg_right ?_ hc.le
      have := Real.rpow_le_rpow (by positivity) (by linarith : (N : ℝ) ≤ (N : ℝ) + 1) hc.le
      linarith
    exact ⟨le_trans hint' (hh_lower ha N), by rw [← hint]; exact hh_upper ha N hN⟩
  have hNc : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - a)) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) ^ (1 - a))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hNc
  apply isEquivalent_of_tendsto_one
  have hlow : Tendsto (fun N : ℕ => 1 - ((N : ℝ) ^ (1 - a))⁻¹) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hinv)
  have hup : Tendsto (fun N : ℕ => 1 + (-a) * ((N : ℝ) ^ (1 - a))⁻¹) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
      (hinv.const_mul (-a)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    show 1 - ((N : ℝ) ^ (1 - a))⁻¹ ≤ Hsum a N / ((N : ℝ) ^ (1 - a) / (1 - a))
    have hNpos : (0 : ℝ) < N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hx : 0 < (N : ℝ) ^ (1 - a) := Real.rpow_pos_of_pos hNpos _
    have hb := (hbounds N hN).1
    rw [le_div_iff₀ (div_pos hx hc)]
    calc (1 - ((N : ℝ) ^ (1 - a))⁻¹) * ((N : ℝ) ^ (1 - a) / (1 - a))
        = (((N : ℝ) ^ (1 - a) - 1) / (1 - a)) := by
          field_simp
      _ ≤ Hsum a N := hb
  · filter_upwards [eventually_ge_atTop 1] with N hN
    show Hsum a N / ((N : ℝ) ^ (1 - a) / (1 - a)) ≤ 1 + (-a) * ((N : ℝ) ^ (1 - a))⁻¹
    have hNpos : (0 : ℝ) < N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hx : 0 < (N : ℝ) ^ (1 - a) := Real.rpow_pos_of_pos hNpos _
    have hb := (hbounds N hN).2
    calc Hsum a N / ((N : ℝ) ^ (1 - a) / (1 - a))
        ≤ (1 + ((N : ℝ) ^ (1 - a) - 1) / (1 - a)) / ((N : ℝ) ^ (1 - a) / (1 - a)) :=
          div_le_div_of_nonneg_right hb (div_nonneg hx.le hc.le)
      _ = 1 + (-a) * ((N : ℝ) ^ (1 - a))⁻¹ := by
          field_simp
          ring

/-- `lem:app-phase-harmonic`: Harmonic sums (`section.tex` l.1048–1057), part (iv).

As $N\to\infty$, $H_N(1)\sim\log N$. -/
lemma pH_int_inv {M : ℝ} (hM : 0 < M) :
    ∫ x in (1 : ℝ)..M, x ^ (-(1 : ℝ)) = Real.log M := by
  simp_rw [Real.rpow_neg_one]
  rw [integral_inv_of_pos one_pos hM, div_one]

theorem lem_app_phase_harmonic_iv :
    IsEquivalent atTop (fun N : ℕ => Hsum 1 N) (fun N : ℕ => Real.log N) := by
  have hbd : ∀ N : ℕ, 1 ≤ N → |Hsum 1 N - Real.log N| ≤ 1 := by
    intro N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hup := (lem_app_phase_harmonic_i (a := 1) one_pos N hN).2
    rw [pH_int_inv (by linarith : (0 : ℝ) < N)] at hup
    have hlow : Real.log ((N : ℝ) + 1) ≤ Hsum 1 N := by
      have h := (lem_app_phase_harmonic_i (a := 1) one_pos N hN).1
      rwa [pH_int_inv (by positivity : (0 : ℝ) < (N : ℝ) + 1)] at h
    have hlog : Real.log N ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [abs_le]
    constructor <;> linarith
  have hO : (fun N : ℕ => Hsum 1 N - Real.log N) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Real.norm_eq_abs, abs_one, mul_one]
    exact hbd N hN
  have hsmall : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun N : ℕ => Real.log N) :=
    Real.isLittleO_const_log_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  exact hO.trans_isLittleO hsmall

/-- `lem:app-phase-harmonic`: Harmonic sums (`section.tex` l.1048–1057), part (v).

$H_N(1)\ge\log(N+1)$ for every integer $N\ge1$ (the source proof gives it for all $N\ge1$ and
consumers use it at explicit $N$; review L-H.4 D1). -/
theorem lem_app_phase_harmonic_v :
    ∀ N : ℕ, 1 ≤ N → Real.log ((N : ℝ) + 1) ≤ Hsum 1 N := by
  intro N hN
  have h := (lem_app_phase_harmonic_i (a := 1) one_pos N hN).1
  rwa [pH_int_inv (by positivity : (0 : ℝ) < (N : ℝ) + 1)] at h

/-- `lem:app-phase-harmonic`: Harmonic sums (`section.tex` l.1048–1057), part (vi).

For $a>1$, as $N\to\infty$, $0\le\zeta(a)-H_N(a)\le N^{1-a}/(a-1)$, where
$\zeta(a)=\sum_{i\ge1}i^{-a}$; for every integer $N\ge1$ (review L-H.4 D1). -/
lemma pz_range {a : ℝ} (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), (if 0 < i then (i : ℝ) ^ (-a) else 0) = Hsum a N := by
  induction N with
  | zero => simp [Hsum]
  | succ n ih =>
    have hn1 : 1 ≤ n + 1 := by omega
    rw [Finset.sum_range_succ, ih]
    have hH : Hsum a (n + 1) = Hsum a n + ((n : ℝ) + 1) ^ (-a) := by
      unfold Hsum
      rw [Finset.sum_Icc_succ_top hn1]
      push_cast
      ring
    rw [hH, if_pos (Nat.succ_pos n)]
    push_cast
    ring

lemma pz_alg {a P Q : ℝ} (ha : 1 < a) (hQ : 0 ≤ Q) :
    (Q - P) / (1 - a) ≤ P / (a - 1) := by
  have hc : 0 < a - 1 := by linarith
  rw [show (1 - a) = -(a - 1) by ring, div_neg, ← neg_div, neg_sub]
  exact div_le_div_of_nonneg_right (by linarith) hc.le

lemma pz_tail_le {a : ℝ} (ha : 1 < a) {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i + (N + 1) : ℕ) : ℝ) ^ (-a) ≤ (N : ℝ) ^ (1 - a) / (a - 1) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-a)) (Set.Icc (N : ℝ) ((N + n : ℕ) : ℝ)) :=
    hh_anti (by linarith) (fun x hx => le_trans hN1 hx.1)
  have hcomp := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x ^ (-a)) (a := N)
    (b := N + n) (by omega) hanti
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at hcomp
  have hrw : ∑ i ∈ Finset.range n, ((i + (N + 1) : ℕ) : ℝ) ^ (-a)
      = ∑ i ∈ Finset.range n, ((N + i + 1 : ℕ) : ℝ) ^ (-a) :=
    Finset.sum_congr rfl (fun k _ => by rw [show k + (N + 1) = N + k + 1 by omega])
  have h0 : (0 : ℝ) ∉ Set.uIcc (N : ℝ) ((N + n : ℕ) : ℝ) := by
    rw [Set.uIcc_of_le (Nat.cast_le.mpr (by omega))]
    intro h
    linarith [h.1]
  have hint : ∫ x in (N : ℝ)..((N + n : ℕ) : ℝ), x ^ (-a)
      = (((N + n : ℕ) : ℝ) ^ (1 - a) - (N : ℝ) ^ (1 - a)) / (1 - a) := by
    rw [integral_rpow (Or.inr ⟨by intro h; linarith, h0⟩), show -a + 1 = 1 - a by ring]
  have hQ : 0 ≤ ((N + n : ℕ) : ℝ) ^ (1 - a) := Real.rpow_nonneg (by positivity) _
  rw [hint] at hcomp
  rw [hrw]
  exact le_trans hcomp (pz_alg ha hQ)

theorem lem_app_phase_harmonic_vi {a : ℝ} (ha : 1 < a) :
    ∀ N : ℕ, 1 ≤ N →
      0 ≤ zetaR a - Hsum a N ∧ zetaR a - Hsum a N ≤ (N : ℝ) ^ (1 - a) / (a - 1) := by
  intro N hN
  have hsplit := (ps_summable ha).sum_add_tsum_nat_add (N + 1)
  rw [pz_range N] at hsplit
  have hz : zetaR a = ∑' i : ℕ, (if 0 < i then (i : ℝ) ^ (-a) else 0) := rfl
  have hdiff : zetaR a - Hsum a N = ∑' i : ℕ,
      (if 0 < i + (N + 1) then ((i + (N + 1) : ℕ) : ℝ) ^ (-a) else 0) := by
    rw [hz]
    linarith
  have hnonneg : ∀ i : ℕ,
      0 ≤ (if 0 < i + (N + 1) then ((i + (N + 1) : ℕ) : ℝ) ^ (-a) else 0) := fun i => by
    split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · exact le_rfl
  have hconv : ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (if 0 < i + (N + 1) then ((i + (N + 1) : ℕ) : ℝ) ^ (-a) else 0)
        = ∑ i ∈ Finset.range n, ((i + (N + 1) : ℕ) : ℝ) ^ (-a) :=
    fun n => Finset.sum_congr rfl (fun i _ => by rw [if_pos (by omega : 0 < i + (N + 1))])
  have hT_nonneg : 0 ≤ ∑' i : ℕ, (if 0 < i + (N + 1) then ((i + (N + 1) : ℕ) : ℝ) ^ (-a) else 0) :=
    tsum_nonneg hnonneg
  have hT_le : ∑' i : ℕ, (if 0 < i + (N + 1) then ((i + (N + 1) : ℕ) : ℝ) ^ (-a) else 0)
      ≤ (N : ℝ) ^ (1 - a) / (a - 1) :=
    Real.tsum_le_of_sum_range_le hnonneg (fun n => by rw [hconv n]; exact pz_tail_le ha hN n)
  constructor
  · linarith
  · linarith

/-- `lem:app-phase-harmonic`: Harmonic sums (`section.tex` l.1048–1057), part (vii).

$\zeta(2)<2$. -/
theorem lem_app_phase_harmonic_vii : zetaR 2 < 2 := by
  have h := (lem_app_phase_harmonic_vi (a := 2) (by norm_num) 2 (by norm_num)).2
  have hH : Hsum 2 2 = 5 / 4 := by
    unfold Hsum
    norm_num [Finset.sum_Icc_succ_top, Real.rpow_neg_one]
  have hp : ((2 : ℕ) : ℝ) ^ (1 - (2 : ℝ)) / ((2 : ℝ) - 1) = 1 / 2 := by
    norm_num [Real.rpow_neg_one]
  linarith

end Muon.Phase

end

import Muon.DetEquiv.Scalar
import Muon.Foundations.Conventions
import Muon.Foundations.Gaussian
import Muon.Foundations.RealAnalysis

/-!
# Appendix F: scalar helpers of the isotropic case (task L-F.1)

Snapshot `cr-2026-10-23`. Source: `sections/05b-isotropic/section.tex`, the labels
`lem:app-iso-gaussian` (l.673–685), `lem:app-iso-weights` (l.1070–1096), `lem:app-iso-count`
(l.1188–1206), `lem:app-iso-constants` (l.1250–1258), `lem:app-iso-slope` (l.2435–2440),
`lem:app-iso-shifts` (l.2473–2482), with the definitions they use (l.106, 139, 1044–1057,
1191–1198, 2389–2420). Card: `sections/05b-isotropic/CARD.md` §2, §3, §5 (L-F.1), §6 (items 9, 10).

Reuse: `J`, `Fw`, `Lw`, `rW` of `Muon.DetEquiv` (B, `eqn:app-de-JFL`); the EMA weights
`Muon.emaW` and power sums `Muon.sPow` of `Muon.Foundations.Conventions`; `gaussianReal 0 1`
for the standard Gaussian. No project object is restated. The Gaussian-scalar objects below
(`isoPhi`, `isoF`, `isoPhiDeriv`) are named once here, for H and the later F files to import.

Every theorem is a statement only (`sorry`). Statements follow the source: where the source
gives a sup, `BddAbove` is stated explicitly next to the strict bound (card §6.9).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open Muon.DetEquiv (J Fw Lw rW)

noncomputable section

namespace Muon.Isotropic

/-! ## Definitions -/

/-- `Φ(v) = v J(v) = 𝔼[v g²/(1+v g²)]` (`eqn:app-iso-Phi`, `section.tex` l.106). -/
def isoPhi (v : ℝ) : ℝ := v * J v

/-- `Φ'(v) = 𝔼[g²(1+v g²)^{-2}]` (`lem:app-iso-gaussian`(ii), `section.tex` l.673–685). -/
def isoPhiDeriv (v : ℝ) : ℝ := ∫ g, g ^ 2 / (1 + v * g ^ 2) ^ 2 ∂(gaussianReal 0 1)

/-- `f(ξ) = 𝔼[g²/(g²+2ξ²)]` (the function of `prop:app-de-nomomentum` used in
`eqn:app-iso-closure-f` and `lem:app-iso-gaussian`(i), `section.tex` l.139). -/
def isoF (ξ : ℝ) : ℝ := ∫ g, g ^ 2 / (g ^ 2 + 2 * ξ ^ 2) ∂(gaussianReal 0 1)

/-- `Λ_β(q) = ∫_0^q x^{-1/2} L_β(x) dx` at the EMA weights (`section.tex` l.1056). -/
def isoLambda (β q : ℝ) : ℝ := ∫ x in (0 : ℝ)..q, x ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW β) x

/-- `𝗇_β(q) = log((1-β)² q) / (2 log(1/β))` (`lem:app-iso-count`, `section.tex` l.1191). -/
def isoN (β q : ℝ) : ℝ := Real.log ((1 - β) ^ 2 * q) / (2 * Real.log (1 / β))

/-- `𝖼_β = √(π/2)/(1-β)` (`lem:app-iso-count`, `section.tex` l.1192). -/
def isoC (β : ℝ) : ℝ := Real.sqrt (Real.pi / 2) / (1 - β)

/-- `𝖼'_β = 1 + 1/(1-β²)` (`lem:app-iso-count`, `section.tex` l.1193). -/
def isoC' (β : ℝ) : ℝ := 1 + 1 / (1 - β ^ 2)

/-- `𝖾^-_β = β² Φ'(1)` (`lem:app-iso-count`, `section.tex` l.1196). -/
def isoEminus (β : ℝ) : ℝ := β ^ 2 * isoPhiDeriv 1

/-- `𝖾^+_β = √(π/2)/(1-β) + 1/(1-β²)` (`lem:app-iso-count`, `section.tex` l.1197). -/
def isoEplus (β : ℝ) : ℝ := Real.sqrt (Real.pi / 2) / (1 - β) + 1 / (1 - β ^ 2)

/-- `ē_β = max(1, 1/4 + 1/(2 log(1/β)))` (`section.tex` l.2415). -/
def isoEbar (β : ℝ) : ℝ := max 1 (1 / 4 + 1 / (2 * Real.log (1 / β)))

/-- `e_β(y) = y r_β'(y)`, the slope of `r_β` in `log y` (`section.tex` l.2389). -/
def isoEslope (β y : ℝ) : ℝ := y * deriv (rW (Muon.emaW β)) y

/-- `γ°_β = 𝖼'_β + 1` (`section.tex` l.2417). -/
def isoGammaCirc (β : ℝ) : ℝ := isoC' β + 1

/-- `𝗀_β = sup_{q>0} √q L_β(q)` (`lem:app-iso-constants`(ii), `section.tex` l.1254). -/
def isoGSup (β : ℝ) : ℝ :=
  sSup ((fun q : ℝ => Real.sqrt q * Lw (Muon.emaW β) q) '' Ioi 0)

/-- `𝗀'_β = sup_{q>0} |Λ_β(q) - √(2π) r_β(q)|`
(`lem:app-iso-constants`(iii), `section.tex` l.1255). -/
def isoGPrimeSup (β : ℝ) : ℝ :=
  sSup ((fun q : ℝ => |isoLambda β q - Real.sqrt (2 * Real.pi) * rW (Muon.emaW β) q|) '' Ioi 0)

/-- `r_β'(q) = ∑_{j: w_j>0} w_j² Φ'(w_j² q)` at the EMA weights (`lem:app-iso-weights`(i),
`section.tex` l.1076). -/
def isoRderiv (β q : ℝ) : ℝ :=
  ∑' j : {j : ℕ | 0 < Muon.emaW β j}, Muon.emaW β j ^ 2 * isoPhiDeriv (Muon.emaW β j ^ 2 * q)

/-! ### Private helpers for `lem_app_iso_gaussian` (fully proved, task P-F.1.P1) -/

private lemma p1_den_pos {v : ℝ} (hv : 0 ≤ v) (g : ℝ) : 0 < 1 + v * g ^ 2 := by
  have := mul_nonneg hv (sq_nonneg g)
  linarith

private lemma p1_gauss_compl_zero_pos : (0 : ENNReal) < gaussianReal 0 1 ({(0 : ℝ)}ᶜ) := by
  have h0 : gaussianReal 0 1 {(0 : ℝ)} = 0 :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton
  have h1 : gaussianReal 0 1 ({(0 : ℝ)}ᶜ) = 1 := by
    rw [measure_compl (measurableSet_singleton 0) (by simp [h0]), h0]
    simp
  rw [h1]
  exact one_pos

private lemma p1_integral_pos {f : ℝ → ℝ} (h0 : ∀ g, 0 ≤ f g)
    (hfi : Integrable f (gaussianReal 0 1)) (hne : ∀ g : ℝ, g ≠ 0 → f g ≠ 0) :
    0 < ∫ g, f g ∂(gaussianReal 0 1) := by
  rw [integral_pos_iff_support_of_nonneg h0 hfi]
  refine lt_of_lt_of_le p1_gauss_compl_zero_pos (measure_mono ?_)
  intro g hg
  exact Function.mem_support.mpr (hne g (by simpa using hg))

private lemma p1_bound_of_le {f b : ℝ → ℝ} (hb : Integrable b (gaussianReal 0 1))
    (hm : Measurable f) (h : ∀ g, ‖f g‖ ≤ b g) : Integrable f (gaussianReal 0 1) :=
  Integrable.mono' hb hm.aestronglyMeasurable (Filter.Eventually.of_forall h)

private lemma p1_deriv_le {x : ℝ} (hx : 0 ≤ x) (g : ℝ) :
    g ^ 2 / (1 + x * g ^ 2) ^ 2 ≤ g ^ 2 := by
  have hd : 1 ≤ (1 + x * g ^ 2) ^ 2 := by
    nlinarith [mul_nonneg hx (sq_nonneg g), sq_nonneg (x * g ^ 2)]
  exact div_le_self (sq_nonneg g) hd

private lemma p1_deriv_norm_le {x : ℝ} (hx : 0 ≤ x) (g : ℝ) :
    ‖g ^ 2 / (1 + x * g ^ 2) ^ 2‖ ≤ g ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg g) (sq_nonneg _))]
  exact p1_deriv_le hx g

private lemma p1_deriv_int {v : ℝ} (hv : 0 ≤ v) :
    Integrable (fun g : ℝ => g ^ 2 / (1 + v * g ^ 2) ^ 2) (gaussianReal 0 1) :=
  p1_bound_of_le (Muon.Foundations.gaussian_integrable_pow 2) (by fun_prop)
    (fun g => p1_deriv_norm_le hv g)

private lemma p1_term_int {v : ℝ} (hv : 0 ≤ v) :
    Integrable (fun g : ℝ => v * g ^ 2 / (1 + v * g ^ 2)) (gaussianReal 0 1) := by
  refine p1_bound_of_le ((Muon.Foundations.gaussian_integrable_pow 2).const_mul v)
    (by fun_prop) (fun g => ?_)
  have hn : 0 ≤ v * g ^ 2 := mul_nonneg hv (sq_nonneg g)
  have hd : 1 ≤ 1 + v * g ^ 2 := le_add_of_nonneg_right hn
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn (by linarith))]
  exact div_le_self hn hd

private lemma p1_inv_int {v : ℝ} (hv : 0 ≤ v) :
    Integrable (fun g : ℝ => 1 / (1 + v * g ^ 2)) (gaussianReal 0 1) := by
  refine p1_bound_of_le (integrable_const (1 : ℝ)) (by fun_prop) (fun g => ?_)
  have hd : 1 ≤ 1 + v * g ^ 2 := le_add_of_nonneg_right (mul_nonneg hv (sq_nonneg g))
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one (by linarith))]
  exact div_le_self zero_le_one hd

private lemma p1_term_hasDeriv (g : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun v : ℝ => v * g ^ 2 / (1 + v * g ^ 2)) (g ^ 2 / (1 + x * g ^ 2) ^ 2) x := by
  have h1 : HasDerivAt (fun v : ℝ => v * g ^ 2) (1 * g ^ 2) x :=
    (hasDerivAt_id' x).mul_const (g ^ 2)
  have h2 : HasDerivAt (fun v : ℝ => 1 + v * g ^ 2) (1 * g ^ 2) x := h1.const_add 1
  have hne : 1 + x * g ^ 2 ≠ 0 := (p1_den_pos hx g).ne'
  refine (h1.div h2 hne).congr_deriv ?_
  congr 1
  ring

private lemma p1_isoPhi_eq (v : ℝ) :
    isoPhi v = ∫ g, v * g ^ 2 / (1 + v * g ^ 2) ∂(gaussianReal 0 1) := by
  unfold isoPhi Muon.DetEquiv.J
  rw [← integral_const_mul]
  congr 1
  ext g
  ring

private lemma p1_hasDeriv {v0 : ℝ} (hv0 : 0 < v0) :
    HasDerivAt isoPhi (isoPhiDeriv v0) v0 := by
  have hfun : isoPhi = fun v => ∫ g, v * g ^ 2 / (1 + v * g ^ 2) ∂(gaussianReal 0 1) :=
    funext p1_isoPhi_eq
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := fun v g => v * g ^ 2 / (1 + v * g ^ 2))
    (F' := fun v g => g ^ 2 / (1 + v * g ^ 2) ^ 2) (x₀ := v0) (bound := fun g => g ^ 2)
    (s := Ioi 0) (Ioi_mem_nhds hv0)
    (Filter.Eventually.of_forall fun v => (by fun_prop :
      Measurable fun g : ℝ => v * g ^ 2 / (1 + v * g ^ 2)).aestronglyMeasurable)
    (p1_term_int hv0.le)
    (by fun_prop : Measurable fun g : ℝ => g ^ 2 / (1 + v0 * g ^ 2) ^ 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => fun x hx =>
      p1_deriv_norm_le (Set.mem_Ioi.mp hx).le g)
    (Muon.Foundations.gaussian_integrable_pow 2)
    (Filter.Eventually.of_forall fun g => fun x hx =>
      p1_term_hasDeriv g (Set.mem_Ioi.mp hx).le)).2
  rw [hfun]
  unfold isoPhiDeriv
  exact hmain

private lemma p1_isoPhiDeriv_pos {v : ℝ} (hv : 0 < v) : 0 < isoPhiDeriv v := by
  unfold isoPhiDeriv
  refine p1_integral_pos (fun g => div_nonneg (sq_nonneg g) (sq_nonneg _))
    (p1_deriv_int hv.le) (fun g hg => ?_)
  exact div_ne_zero (pow_ne_zero 2 hg) (pow_ne_zero 2 (p1_den_pos hv.le g).ne')

private lemma p1_isoPhiDeriv_le_one {v : ℝ} (hv : 0 < v) : isoPhiDeriv v ≤ 1 := by
  unfold isoPhiDeriv
  have h := integral_mono (p1_deriv_int hv.le) (Muon.Foundations.gaussian_integrable_pow 2)
    (fun g => p1_deriv_le hv.le g)
  exact h.trans_eq Muon.Foundations.gaussian_moment_two

private lemma p1_isoPhi_pos {v : ℝ} (hv : 0 < v) : 0 < isoPhi v := by
  rw [p1_isoPhi_eq]
  refine p1_integral_pos
    (fun g => div_nonneg (mul_nonneg hv.le (sq_nonneg g)) (p1_den_pos hv.le g).le)
    (p1_term_int hv.le) (fun g hg => ?_)
  exact div_ne_zero (mul_ne_zero hv.ne' (pow_ne_zero 2 hg)) (p1_den_pos hv.le g).ne'

private lemma p1_isoPhi_lt_one {v : ℝ} (hv : 0 < v) : isoPhi v < 1 := by
  have hpos : 0 < ∫ g, 1 / (1 + v * g ^ 2) ∂(gaussianReal 0 1) :=
    p1_integral_pos (fun g => div_nonneg zero_le_one (p1_den_pos hv.le g).le)
      (p1_inv_int hv.le) (fun g _ => (one_div_pos.mpr (p1_den_pos hv.le g)).ne')
  have hsplit : isoPhi v = ∫ g, (1 - 1 / (1 + v * g ^ 2)) ∂(gaussianReal 0 1) := by
    rw [p1_isoPhi_eq]
    congr 1
    ext g
    rw [one_sub_div (p1_den_pos hv.le g).ne']
    congr 1
    ring
  have h1 : ∫ _g, (1 : ℝ) ∂(gaussianReal 0 1) = 1 := by simp
  rw [hsplit, integral_sub (integrable_const (1 : ℝ)) (p1_inv_int hv.le), h1]
  linarith

/-! ### Private helpers for `lem_app_iso_gaussian` (iii)-(iv) (fully proved, task P-F.1.P2) -/

private lemma p2_int_sq_div {v : ℝ} (hv : 0 ≤ v) :
    Integrable (fun g : ℝ => g ^ 2 / (1 + v * g ^ 2)) (gaussianReal 0 1) := by
  refine p1_bound_of_le (Muon.Foundations.gaussian_integrable_pow 2) (by fun_prop) (fun g => ?_)
  have hd : 1 ≤ 1 + v * g ^ 2 := le_add_of_nonneg_right (mul_nonneg hv (sq_nonneg g))
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg g) (p1_den_pos hv g).le)]
  exact div_le_self (sq_nonneg g) hd

private lemma p2_key {v : ℝ} (hv : 0 < v) :
    v - isoPhi v = ∫ g, v ^ 2 * g ^ 4 / (1 + v * g ^ 2) ∂(gaussianReal 0 1) := by
  rw [p1_isoPhi_eq]
  have hA : Integrable (fun g : ℝ => v * g ^ 2) (gaussianReal 0 1) :=
    (Muon.Foundations.gaussian_integrable_pow 2).const_mul v
  have hC : ∫ g, v * g ^ 2 ∂(gaussianReal 0 1) = v := by
    rw [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one]
  have hpt : (fun g : ℝ => v ^ 2 * g ^ 4 / (1 + v * g ^ 2))
      = fun g : ℝ => v * g ^ 2 - v * g ^ 2 / (1 + v * g ^ 2) := by
    funext g
    have hd := (p1_den_pos hv.le g).ne'
    field_simp
    ring
  rw [hpt, integral_sub hA (p1_term_int hv.le), hC]

private lemma p2_iii {v : ℝ} (hv : 0 < v) : 0 ≤ v - isoPhi v ∧ v - isoPhi v ≤ 3 * v ^ 2 := by
  rw [p2_key hv]
  have hint : Integrable (fun g : ℝ => v ^ 2 * g ^ 4 / (1 + v * g ^ 2)) (gaussianReal 0 1) := by
    refine p1_bound_of_le ((Muon.Foundations.gaussian_integrable_pow 4).const_mul (v ^ 2))
      (by fun_prop) (fun g => ?_)
    have hn : 0 ≤ v ^ 2 * g ^ 4 := mul_nonneg (sq_nonneg v) (by positivity)
    have hd : 1 ≤ 1 + v * g ^ 2 := le_add_of_nonneg_right (mul_nonneg hv.le (sq_nonneg g))
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn (p1_den_pos hv.le g).le)]
    exact div_le_self hn hd
  have h4 : ∫ g, v ^ 2 * g ^ 4 ∂(gaussianReal 0 1) = 3 * v ^ 2 := by
    rw [integral_const_mul, Muon.Foundations.gaussian_moment_four]
    ring
  constructor
  · apply integral_nonneg
    intro g
    exact div_nonneg (mul_nonneg (sq_nonneg v) (by positivity)) (p1_den_pos hv.le g).le
  · have hle : ∫ g, v ^ 2 * g ^ 4 / (1 + v * g ^ 2) ∂(gaussianReal 0 1)
        ≤ ∫ g, v ^ 2 * g ^ 4 ∂(gaussianReal 0 1) :=
      integral_mono hint ((Muon.Foundations.gaussian_integrable_pow 4).const_mul (v ^ 2))
        (fun g => by
          have hn : 0 ≤ v ^ 2 * g ^ 4 := mul_nonneg (sq_nonneg v) (by positivity)
          have hd : 1 ≤ 1 + v * g ^ 2 := le_add_of_nonneg_right (mul_nonneg hv.le (sq_nonneg g))
          exact div_le_self hn hd)
    linarith

private lemma p2_J_bounds {v : ℝ} (hv : 0 < v) :
    1 - 3 * v ≤ isoPhi v / v ∧ isoPhi v / v ≤ 1 := by
  have hr : isoPhi v / v = ∫ g, g ^ 2 / (1 + v * g ^ 2) ∂(gaussianReal 0 1) := by
    unfold isoPhi Muon.DetEquiv.J
    exact mul_div_cancel_left₀ _ hv.ne'
  rw [hr]
  have h2 : ∫ g : ℝ, g ^ 2 ∂(gaussianReal 0 1) = 1 := Muon.Foundations.gaussian_moment_two
  constructor
  · have hA : Integrable (fun g : ℝ => g ^ 2 - v * g ^ 4) (gaussianReal 0 1) :=
      (Muon.Foundations.gaussian_integrable_pow 2).sub
        ((Muon.Foundations.gaussian_integrable_pow 4).const_mul v)
    have hle : ∫ g, (g ^ 2 - v * g ^ 4) ∂(gaussianReal 0 1)
        ≤ ∫ g, g ^ 2 / (1 + v * g ^ 2) ∂(gaussianReal 0 1) :=
      integral_mono hA (p2_int_sq_div hv.le) (fun g => by
        have hd := p1_den_pos hv.le g
        rw [le_div_iff₀ hd]
        nlinarith [sq_nonneg (v * g ^ 3)])
    have hval : ∫ g, (g ^ 2 - v * g ^ 4) ∂(gaussianReal 0 1) = 1 - 3 * v := by
      rw [integral_sub (Muon.Foundations.gaussian_integrable_pow 2)
        ((Muon.Foundations.gaussian_integrable_pow 4).const_mul v), integral_const_mul,
        h2, Muon.Foundations.gaussian_moment_four]
      ring
    linarith
  · have hle : ∫ g, g ^ 2 / (1 + v * g ^ 2) ∂(gaussianReal 0 1)
        ≤ ∫ g, g ^ 2 ∂(gaussianReal 0 1) :=
      integral_mono (p2_int_sq_div hv.le) (Muon.Foundations.gaussian_integrable_pow 2)
        (fun g => by
          have hd : 1 ≤ 1 + v * g ^ 2 := le_add_of_nonneg_right (mul_nonneg hv.le (sq_nonneg g))
          exact div_le_self (sq_nonneg g) hd)
    linarith

private lemma p2_isoPhi_div_tendsto :
    Tendsto (fun v : ℝ => isoPhi v / v) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hc : Continuous (fun v : ℝ => 1 - 3 * v) := by fun_prop
  have hlow : Tendsto (fun v : ℝ => 1 - 3 * v) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · exact Filter.eventually_of_mem self_mem_nhdsWithin
      (fun v hv => (p2_J_bounds (Set.mem_Ioi.mp hv)).1)
  · exact Filter.eventually_of_mem self_mem_nhdsWithin
      (fun v hv => (p2_J_bounds (Set.mem_Ioi.mp hv)).2)

private lemma p2_isoPhi_tendsto_atTop :
    Tendsto isoPhi atTop (𝓝 1) := by
  have hfun : isoPhi = fun v => ∫ g, v * g ^ 2 / (1 + v * g ^ 2) ∂(gaussianReal 0 1) :=
    funext p1_isoPhi_eq
  rw [hfun]
  have hlim : ∀ g : ℝ, g ≠ 0 → Tendsto (fun v : ℝ => v * g ^ 2 / (1 + v * g ^ 2)) atTop (𝓝 1) := by
    intro g hg
    have hg2 : 0 < g ^ 2 := lt_of_le_of_ne (sq_nonneg g) (Ne.symm (pow_ne_zero 2 hg))
    have hinv : Tendsto (fun v : ℝ => (1 + v * g ^ 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_left atTop 1 (tendsto_id.atTop_mul_const hg2))
    have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    have hd : 1 + v * g ^ 2 ≠ 0 := (p1_den_pos hv g).ne'
    change 1 - (1 + v * g ^ 2)⁻¹ = v * g ^ 2 / (1 + v * g ^ 2)
    field_simp
    ring
  have hae : ∀ᵐ g ∂(gaussianReal 0 1), g ≠ 0 := by
    have h0 : gaussianReal 0 1 {(0 : ℝ)} = 0 :=
      gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton
    rw [ae_iff]
    simpa using h0
  have hlimae : ∀ᵐ g ∂(gaussianReal 0 1),
      Tendsto (fun v : ℝ => v * g ^ 2 / (1 + v * g ^ 2)) atTop (𝓝 ((fun _ : ℝ => (1 : ℝ)) g)) :=
    hae.mono (fun g hg => hlim g hg)
  have hbound : ∀ᶠ v in atTop, ∀ᵐ g ∂(gaussianReal 0 1),
      ‖v * g ^ 2 / (1 + v * g ^ 2)‖ ≤ (fun _ : ℝ => (1 : ℝ)) g := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    refine Filter.Eventually.of_forall (fun g => ?_)
    have hn : 0 ≤ v * g ^ 2 := mul_nonneg hv (sq_nonneg g)
    have hd := p1_den_pos hv g
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn hd.le)]
    exact (div_le_one hd).mpr (by linarith)
  have hmeas : ∀ᶠ v in atTop,
      AEStronglyMeasurable (fun g : ℝ => v * g ^ 2 / (1 + v * g ^ 2)) (gaussianReal 0 1) :=
    Filter.Eventually.of_forall fun v =>
      (by fun_prop : Measurable fun g : ℝ => v * g ^ 2 / (1 + v * g ^ 2)).aestronglyMeasurable
  have hT := tendsto_integral_filter_of_dominated_convergence (μ := gaussianReal 0 1)
    (l := atTop) (F := fun (v : ℝ) (g : ℝ) => v * g ^ 2 / (1 + v * g ^ 2))
    (f := fun _ : ℝ => (1 : ℝ)) (fun _ : ℝ => (1 : ℝ)) hmeas hbound (integrable_const (1 : ℝ))
    hlimae
  have h1 : ∫ _g, (1 : ℝ) ∂(gaussianReal 0 1) = 1 := by simp
  rw [h1] at hT
  exact hT

/-! ### Private helpers for `lem_app_iso_weights` (fully proved, task P-F.1.P3) -/

private lemma p3_isoPhi_zero : isoPhi 0 = 0 := by
  simp [isoPhi]

private lemma p3_J_eq {v : ℝ} (hv : 0 < v) : J v = isoPhi v / v := by
  unfold isoPhi
  rw [mul_div_cancel_left₀ _ hv.ne']

private lemma p3_isoPhi_bounds {v : ℝ} (hv : 0 ≤ v) : 0 ≤ isoPhi v ∧ isoPhi v ≤ v := by
  rcases hv.eq_or_lt with h | h
  · subst h
    simp [p3_isoPhi_zero]
  · refine ⟨(p1_isoPhi_pos h).le, ?_⟩
    have h1 := (p2_J_bounds h).2
    rwa [div_le_one h] at h1

private lemma p3_dPhi_bounds {v : ℝ} (hv : 0 ≤ v) : 0 ≤ isoPhiDeriv v ∧ isoPhiDeriv v ≤ 1 := by
  refine ⟨?_, ?_⟩
  · unfold isoPhiDeriv
    exact integral_nonneg fun g => div_nonneg (sq_nonneg g) (sq_nonneg _)
  · unfold isoPhiDeriv
    have h := integral_mono (p1_deriv_int hv) (Muon.Foundations.gaussian_integrable_pow 2)
      (fun g => p1_deriv_le hv g)
    exact h.trans_eq Muon.Foundations.gaussian_moment_two

private lemma p3_dPhi_pos {v : ℝ} (hv : 0 ≤ v) : 0 < isoPhiDeriv v := by
  rcases hv.eq_or_lt with h | h
  · subst h
    have h1 : isoPhiDeriv 0 = 1 := by
      unfold isoPhiDeriv
      simp only [zero_mul, add_zero, one_pow, div_one]
      exact Muon.Foundations.gaussian_moment_two
    rw [h1]
    exact one_pos
  · exact p1_isoPhiDeriv_pos h

private lemma p3_isoPhi_hasDerivWithinAt {v0 : ℝ} (hv0 : 0 ≤ v0) :
    HasDerivWithinAt isoPhi (isoPhiDeriv v0) (Ici 0) v0 := by
  rcases hv0.eq_or_lt with h | h
  · subst h
    have hup : Tendsto (fun v : ℝ => v) (𝓝[Ici 0] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hcont : ContinuousWithinAt isoPhi (Ici 0) 0 := by
      unfold ContinuousWithinAt
      rw [p3_isoPhi_zero]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with v hv
        exact (p3_isoPhi_bounds (Set.mem_Ici.mp hv)).1
      · filter_upwards [self_mem_nhdsWithin] with v hv
        exact (p3_isoPhi_bounds (Set.mem_Ici.mp hv)).2
    have hcg : ∀ g : ℝ, ContinuousAt (fun v : ℝ => g ^ 2 / (1 + v * g ^ 2) ^ 2) 0 := fun g =>
      ContinuousAt.div continuousAt_const (by fun_prop) (by simp)
    have hcontD : ContinuousWithinAt isoPhiDeriv (Ici 0) 0 := by
      have key := continuousWithinAt_of_dominated (μ := gaussianReal 0 1) (x₀ := (0 : ℝ))
        (s := Ici 0) (F := fun v g => g ^ 2 / (1 + v * g ^ 2) ^ 2) (bound := fun g => g ^ 2)
        (Filter.Eventually.of_forall fun v => (by fun_prop :
          Measurable fun g : ℝ => g ^ 2 / (1 + v * g ^ 2) ^ 2).aestronglyMeasurable)
        (by
          filter_upwards [self_mem_nhdsWithin] with v hv
          exact Filter.Eventually.of_forall fun g => p1_deriv_norm_le (Set.mem_Ici.mp hv) g)
        (Muon.Foundations.gaussian_integrable_pow 2)
        (Filter.Eventually.of_forall fun g => (hcg g).continuousWithinAt)
      exact key
    have hdiff : DifferentiableOn ℝ isoPhi (Ioi 0) := fun v hv =>
      (p1_hasDeriv hv).differentiableAt.differentiableWithinAt
    have hlim : Tendsto (fun x => deriv isoPhi x) (𝓝[>] (0 : ℝ)) (𝓝 (isoPhiDeriv 0)) := by
      have h1 : Tendsto isoPhiDeriv (𝓝[>] (0 : ℝ)) (𝓝 (isoPhiDeriv 0)) :=
        hcontD.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact ((p1_hasDeriv (Set.mem_Ioi.mp hv)).deriv).symm
    exact hasDerivWithinAt_Ici_of_tendsto_deriv hdiff (hcont.mono Ioi_subset_Ici_self)
      self_mem_nhdsWithin hlim
  · exact (p1_hasDeriv h).hasDerivWithinAt

private lemma p3_term_hasDerivWithinAt {a : ℝ} (ha : 0 ≤ a) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (fun q : ℝ => isoPhi (a * q)) (a * isoPhiDeriv (a * x)) (Ici 0) x := by
  have hlin : HasDerivWithinAt (fun q : ℝ => a * q) a (Ici 0) x :=
    ((hasDerivAt_id' x).const_mul a).hasDerivWithinAt.congr_deriv (mul_one a)
  have hmaps : MapsTo (fun q : ℝ => a * q) (Ici 0) (Ici 0) := fun q hq =>
    mul_nonneg ha (Set.mem_Ici.mp hq)
  refine ((p3_isoPhi_hasDerivWithinAt (mul_nonneg ha hx)).comp x hlin hmaps).congr_deriv ?_
  ring

private lemma p3_tsum_hasDerivWithinAt {ι : Type*} (T T' : ι → ℝ → ℝ) (u : ι → ℝ)
    (hu : Summable u)
    (hT : ∀ j, ∀ x : ℝ, 0 ≤ x → HasDerivWithinAt (T j) (T' j x) (Ici 0) x)
    (hb : ∀ j, ∀ x : ℝ, 0 ≤ x → ‖T' j x‖ ≤ u j)
    (hs : ∀ x : ℝ, 0 ≤ x → Summable (fun j => T j x)) {x0 : ℝ} (hx0 : 0 ≤ x0) :
    HasDerivWithinAt (fun q => ∑' j, T j q) (∑' j, T' j x0) (Ici 0) x0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hsl : (fun y => slope (fun q => ∑' j, T j q) x0 y) =ᶠ[𝓝[Ici 0 \ {x0}] x0]
      (fun y => ∑' j, slope (T j) x0 y) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [slope_def_field]
    rw [tsum_div_const, (hs y (Set.mem_Ici.mp hy.1)).tsum_sub (hs x0 hx0)]
  have hlim : Tendsto (fun y => ∑' j, slope (T j) x0 y) (𝓝[Ici 0 \ {x0}] x0)
      (𝓝 (∑' j, T' j x0)) := by
    refine tendsto_tsum_of_dominated_convergence hu (fun j => ?_) ?_
    · exact hasDerivWithinAt_iff_tendsto_slope.mp (hT j x0 hx0)
    · filter_upwards [self_mem_nhdsWithin] with y hy
      intro j
      have hyI : y ∈ Ici (0 : ℝ) := hy.1
      have hne : y - x0 ≠ 0 := sub_ne_zero.mpr hy.2
      have hmv := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun z hz => hT j z hz) (fun z hz => hb j z hz) (Set.mem_Ici.mpr hx0) hyI
      rw [slope_def_field, norm_div, div_le_iff₀ (norm_pos_iff.mpr hne)]
      exact hmv
  exact hlim.congr' hsl.symm

private lemma p3_emaW_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (j : ℕ) :
    0 ≤ Muon.emaW β j := by
  unfold Muon.emaW
  exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)

private lemma p3_emaW_le_one {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (j : ℕ) :
    Muon.emaW β j ≤ 1 := by
  unfold Muon.emaW
  have h1 : β ^ j ≤ 1 := pow_le_one₀ hβ0 hβ1.le
  calc (1 - β) * β ^ j ≤ 1 * β ^ j :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hβ0 j)
    _ ≤ 1 := by linarith

private lemma p3_emaW_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Summable (fun j : ℕ => Muon.emaW β j) := by
  unfold Muon.emaW
  exact (summable_geometric_of_lt_one hβ0 hβ1).mul_left (1 - β)

private lemma p3_sq_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Summable (fun j : ℕ => Muon.emaW β j ^ 2) :=
  Summable.of_nonneg_of_le (fun j => sq_nonneg _)
    (fun j => by
      have h0 := p3_emaW_nonneg hβ0 hβ1 j
      have h1 := p3_emaW_le_one hβ0 hβ1 j
      nlinarith)
    (p3_emaW_summable hβ0 hβ1)

private lemma p3_rW_eq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    rW (Muon.emaW β) q = ∑' j : {j : ℕ | 0 < Muon.emaW β j}, isoPhi (Muon.emaW β j ^ 2 * q) := by
  have hsupp : Function.support (fun j : ℕ => isoPhi (Muon.emaW β j ^ 2 * q)) ⊆
      {j : ℕ | 0 < Muon.emaW β j} := by
    intro j hj
    rcases (p3_emaW_nonneg hβ0 hβ1 j).eq_or_lt with h | h
    · exact absurd (show isoPhi (Muon.emaW β j ^ 2 * q) = 0 by rw [← h]; simp [p3_isoPhi_zero]) hj
    · exact h
  rw [tsum_subtype_eq_of_support_subset hsupp]
  unfold rW Fw
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  unfold isoPhi
  ring

private lemma p3_term_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun j : {j : ℕ | 0 < Muon.emaW β j} => isoPhi (Muon.emaW β j ^ 2 * x)) :=
  Summable.of_nonneg_of_le
    (fun j => (p3_isoPhi_bounds (mul_nonneg (sq_nonneg _) hx)).1)
    (fun j => (p3_isoPhi_bounds (mul_nonneg (sq_nonneg _) hx)).2)
    ((p3_sq_summable hβ0 hβ1).subtype _ |>.mul_right x)

private lemma p3_rW_hasDerivWithinAt {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    HasDerivWithinAt (rW (Muon.emaW β)) (isoRderiv β q) (Ici 0) q := by
  have hsqS : Summable (fun j : {j : ℕ | 0 < Muon.emaW β j} => Muon.emaW β j ^ 2) :=
    (p3_sq_summable hβ0 hβ1).subtype _
  have hD := p3_tsum_hasDerivWithinAt
    (fun (j : {j : ℕ | 0 < Muon.emaW β j}) (x : ℝ) => isoPhi (Muon.emaW β j ^ 2 * x))
    (fun (j : {j : ℕ | 0 < Muon.emaW β j}) (x : ℝ) =>
      Muon.emaW β j ^ 2 * isoPhiDeriv (Muon.emaW β j ^ 2 * x))
    (fun j => Muon.emaW β j ^ 2) hsqS
    (fun j x hx => p3_term_hasDerivWithinAt (sq_nonneg _) hx)
    (fun j x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (p3_dPhi_bounds (mul_nonneg (sq_nonneg _) hx)).1)]
      exact mul_le_of_le_one_right (sq_nonneg _) (p3_dPhi_bounds (mul_nonneg (sq_nonneg _) hx)).2)
    (fun x hx => p3_term_summable hβ0 hβ1 hx) hq
  refine hD.congr ?_ ?_
  · intro y hy
    exact p3_rW_eq hβ0 hβ1 (Set.mem_Ici.mp hy)
  · exact p3_rW_eq hβ0 hβ1 hq

private lemma p3_isoRderiv_pos {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    0 < isoRderiv β q := by
  unfold isoRderiv
  have hnn : ∀ j : {j : ℕ | 0 < Muon.emaW β j},
      0 ≤ Muon.emaW β j ^ 2 * isoPhiDeriv (Muon.emaW β j ^ 2 * q) := fun j =>
    mul_nonneg (sq_nonneg _) (p3_dPhi_bounds (mul_nonneg (sq_nonneg _) hq)).1
  have hsum : Summable (fun j : {j : ℕ | 0 < Muon.emaW β j} =>
      Muon.emaW β j ^ 2 * isoPhiDeriv (Muon.emaW β j ^ 2 * q)) :=
    Summable.of_nonneg_of_le hnn
      (fun j => mul_le_of_le_one_right (sq_nonneg _)
        (p3_dPhi_bounds (mul_nonneg (sq_nonneg _) hq)).2)
      ((p3_sq_summable hβ0 hβ1).subtype _)
  have h0 : 0 < Muon.emaW β 0 := by
    unfold Muon.emaW
    rw [pow_zero, mul_one]
    linarith
  have hj0 : (0 : ℕ) ∈ {j : ℕ | 0 < Muon.emaW β j} := h0
  exact hsum.tsum_pos hnn ⟨0, hj0⟩
    (mul_pos (pow_pos h0 2) (p3_dPhi_pos (mul_nonneg (sq_nonneg _) hq)))

private lemma p3_surj {f : ℝ → ℝ} {S : Set ℝ} (hS : S ⊆ Ici 0) (hc : ContinuousOn f (Ici 0))
    (h0 : f 0 = 0) (hbig : ∀ y ∈ S, ∃ Q : ℝ, 0 ≤ Q ∧ y < f Q) :
    ∀ y ∈ S, ∃ q : ℝ, 0 ≤ q ∧ f q = y := by
  intro y hy
  obtain ⟨Q, hQ, hyQ⟩ := hbig y hy
  have hy0 : 0 ≤ y := Set.mem_Ici.mp (hS hy)
  have hcI : ContinuousOn f (Icc 0 Q) := hc.mono Icc_subset_Ici_self
  obtain ⟨q, hq, hfq⟩ := intermediate_value_Icc hQ hcI
    ⟨by rw [h0]; exact hy0, hyQ.le⟩
  exact ⟨q, hq.1, hfq⟩

private lemma p3_rW_unbounded {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ y : ℝ, 0 ≤ y → ∃ Q : ℝ, 0 ≤ Q ∧ y < rW (Muon.emaW β) Q := by
  have hw : Muon.DetEquiv.WeightSeq (Muon.emaW β) :=
    ⟨fun j => p3_emaW_nonneg hβ0.le hβ1 j, p3_emaW_summable hβ0.le hβ1,
      0, ne_of_gt (by unfold Muon.emaW; rw [pow_zero, mul_one]; linarith)⟩
  obtain ⟨-, -, -, -, -, -, hlim⟩ := Muon.DetEquiv.lem_app_de_scalar_iii hw
  have hS : {j : ℕ | 0 < Muon.emaW β j} = Set.univ := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    unfold Muon.emaW
    exact mul_pos (by linarith) (pow_pos hβ0 j)
  rw [hS, Set.encard_univ, ENat.card_eq_top_of_infinite, ENat.toENNReal_top] at hlim
  intro y hy
  have hev := (ENNReal.tendsto_nhds_top_iff_nnreal.mp hlim y.toNNReal).and
    (eventually_ge_atTop (0 : ℝ))
  obtain ⟨Q, hQ1, hQ2⟩ := hev.exists
  refine ⟨Q, hQ2, ?_⟩
  have h1 : ENNReal.ofReal y < ENNReal.ofReal (rW (Muon.emaW β) Q) := hQ1
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp h1).1

private lemma p3_rW_zero (q : ℝ) : rW (Muon.emaW 0) q = isoPhi q := by
  have hz : ∀ j : ℕ, j ≠ 0 → Muon.emaW 0 j ^ 2 * J (Muon.emaW 0 j ^ 2 * q) = 0 := by
    intro j hj
    simp [Muon.emaW, zero_pow hj]
  unfold rW Fw
  rw [tsum_eq_single 0 hz]
  simp [Muon.emaW, isoPhi]

private lemma p3_inv_int_scaled {x : ℝ} (hx : 0 < x) :
    Integrable (fun y : ℝ => 1 / (1 + x * y ^ 2)) := by
  have h := integrable_inv_one_add_sq.comp_mul_left' (R := Real.sqrt x)
    (Real.sqrt_pos.mpr hx).ne'
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  show (1 + (Real.sqrt x * y) ^ 2)⁻¹ = 1 / (1 + x * y ^ 2)
  rw [mul_pow, Real.sq_sqrt hx.le, one_div]

private lemma p3_lebesgue_int {x : ℝ} (hx : 0 < x) :
    ∫ y : ℝ, 1 / (1 + x * y ^ 2) = Real.pi / Real.sqrt x := by
  have h := Measure.integral_comp_mul_left (fun z : ℝ => (1 + z ^ 2)⁻¹) (Real.sqrt x)
  have e : (fun y : ℝ => 1 / (1 + x * y ^ 2)) =
      fun y : ℝ => (fun z : ℝ => (1 + z ^ 2)⁻¹) (Real.sqrt x * y) := by
    funext y
    show 1 / (1 + x * y ^ 2) = (1 + (Real.sqrt x * y) ^ 2)⁻¹
    rw [mul_pow, Real.sq_sqrt hx.le, one_div]
  rw [e, h, integral_univ_inv_one_add_sq, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hx)),
    smul_eq_mul]
  ring

private lemma p3_one_sub_eq {x : ℝ} (hx : 0 < x) :
    1 - isoPhi x = ∫ g, 1 / (1 + x * g ^ 2) ∂(gaussianReal 0 1) := by
  have hsplit : isoPhi x = ∫ g, (1 - 1 / (1 + x * g ^ 2)) ∂(gaussianReal 0 1) := by
    rw [p1_isoPhi_eq]
    congr 1
    ext g
    rw [one_sub_div (p1_den_pos hx.le g).ne']
    congr 1
    ring
  rw [hsplit, integral_sub (integrable_const (1 : ℝ)) (p1_inv_int hx.le)]
  simp

private lemma p3_gauss_inv_le {x : ℝ} (hx : 0 < x) :
    ∫ g, 1 / (1 + x * g ^ 2) ∂(gaussianReal 0 1) ≤
      Real.sqrt (Real.pi / 2) * x ^ (-(1 / 2 : ℝ)) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hint : Integrable (fun g : ℝ => 1 / (1 + x * g ^ 2)) := p3_inv_int_scaled hx
  have hc0 : 0 ≤ 1 / Real.sqrt (2 * Real.pi) := by positivity
  have hpt : ∀ g : ℝ, gaussianPDFReal 0 1 g • (1 / (1 + x * g ^ 2)) ≤
      (1 / Real.sqrt (2 * Real.pi)) • (1 / (1 + x * g ^ 2)) := fun g => by
    rw [smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (Muon.Foundations.gaussian_pdf_le g)
      (div_nonneg zero_le_one (p1_den_pos hx.le g).le)
  have hmeas : AEStronglyMeasurable (fun g : ℝ => gaussianPDFReal 0 1 g • (1 / (1 + x * g ^ 2)))
      volume :=
    ((measurable_gaussianPDFReal 0 1).smul (by fun_prop)).aestronglyMeasurable
  have hI : Integrable (fun g : ℝ => gaussianPDFReal 0 1 g • (1 / (1 + x * g ^ 2))) :=
    Integrable.mono' (hint.const_mul (1 / Real.sqrt (2 * Real.pi))) hmeas
      (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg (mul_nonneg
          (gaussianPDFReal_nonneg 0 1 g) (div_nonneg zero_le_one (p1_den_pos hx.le g).le))]
        exact mul_le_mul_of_nonneg_right (Muon.Foundations.gaussian_pdf_le g)
          (div_nonneg zero_le_one (p1_den_pos hx.le g).le))
  have key : Real.sqrt (Real.pi / 2) * Real.sqrt (2 * Real.pi) = Real.pi := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show Real.pi / 2 * (2 * Real.pi) = Real.pi ^ 2 by ring]
    exact Real.sqrt_sq Real.pi_pos.le
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hs2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  calc ∫ g, gaussianPDFReal 0 1 g • (1 / (1 + x * g ^ 2))
      ≤ ∫ g, (1 / Real.sqrt (2 * Real.pi)) • (1 / (1 + x * g ^ 2)) :=
        integral_mono hI (hint.const_mul _) hpt
    _ = 1 / Real.sqrt (2 * Real.pi) * (Real.pi / Real.sqrt x) := by
        rw [integral_smul, smul_eq_mul, p3_lebesgue_int hx]
    _ = Real.sqrt (Real.pi / 2) * x ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
        field_simp
        linear_combination (-1 : ℝ) * key

private lemma p3_xdPhi_le {x : ℝ} (hx : 0 < x) : x * isoPhiDeriv x ≤ 1 - isoPhi x := by
  rw [p3_one_sub_eq hx, isoPhiDeriv, ← integral_const_mul]
  refine integral_mono ((p1_deriv_int hx.le).const_mul x) (p1_inv_int hx.le) (fun g => ?_)
  have hA := p1_den_pos hx.le g
  have e : x * (g ^ 2 / (1 + x * g ^ 2) ^ 2) = (x * g ^ 2) / (1 + x * g ^ 2) ^ 2 := by ring
  show x * (g ^ 2 / (1 + x * g ^ 2) ^ 2) ≤ 1 / (1 + x * g ^ 2)
  rw [e, div_le_div_iff₀ (pow_pos hA 2) hA]
  nlinarith [hA, mul_nonneg hx.le (sq_nonneg g)]

private lemma p3_g4_le {x : ℝ} (hx : 0 ≤ x) (g : ℝ) : g ^ 4 / (1 + x * g ^ 2) ^ 2 ≤ g ^ 4 := by
  have h1 : 1 ≤ (1 + x * g ^ 2) ^ 2 := by
    nlinarith [mul_nonneg hx (sq_nonneg g)]
  exact div_le_self (by positivity) h1

private lemma p3_norm_J'_le {x : ℝ} (hx : 0 ≤ x) (g : ℝ) :
    ‖-(g ^ 4 / (1 + x * g ^ 2) ^ 2)‖ ≤ g ^ 4 := by
  rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) (sq_nonneg _))]
  exact p3_g4_le hx g

private lemma p3_term_hasDerivJ (g : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun v : ℝ => g ^ 2 / (1 + v * g ^ 2)) (-(g ^ 4 / (1 + x * g ^ 2) ^ 2)) x := by
  have h1 : HasDerivAt (fun v : ℝ => v * g ^ 2) (1 * g ^ 2) x :=
    (hasDerivAt_id' x).mul_const (g ^ 2)
  have h2 : HasDerivAt (fun v : ℝ => 1 + v * g ^ 2) (1 * g ^ 2) x := h1.const_add 1
  have hne : 1 + x * g ^ 2 ≠ 0 := (p1_den_pos hx g).ne'
  refine ((hasDerivAt_const x (g ^ 2)).div h2 hne).congr_deriv ?_
  field_simp
  ring

private lemma p3_J_hasDeriv {x0 : ℝ} (hx0 : 0 < x0) :
    HasDerivAt J (∫ g, -(g ^ 4 / (1 + x0 * g ^ 2) ^ 2) ∂(gaussianReal 0 1)) x0 := by
  have hfun : J = fun v => ∫ g, g ^ 2 / (1 + v * g ^ 2) ∂(gaussianReal 0 1) := rfl
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := fun v g => g ^ 2 / (1 + v * g ^ 2))
    (F' := fun v g => -(g ^ 4 / (1 + v * g ^ 2) ^ 2)) (x₀ := x0) (bound := fun g => g ^ 4)
    (s := Ioi 0) (Ioi_mem_nhds hx0)
    (Filter.Eventually.of_forall fun v => (by fun_prop :
      Measurable fun g : ℝ => g ^ 2 / (1 + v * g ^ 2)).aestronglyMeasurable)
    (p2_int_sq_div hx0.le)
    (by fun_prop : Measurable fun g : ℝ => -(g ^ 4 / (1 + x0 * g ^ 2) ^ 2)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => fun x hx => p3_norm_J'_le (Set.mem_Ioi.mp hx).le g)
    (Muon.Foundations.gaussian_integrable_pow 4)
    (Filter.Eventually.of_forall fun g => fun x hx => p3_term_hasDerivJ g (Set.mem_Ioi.mp hx).le)).2
  rw [hfun]
  exact hmain

/-! ## Statements -/

/-! ### `lem:app-iso-gaussian` -/

/-- `lem:app-iso-gaussian`(i), snapshot `cr-2026-10-23`. Part (i) of the environment below.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[The Gaussian scalar]\label{lem:app-iso-gaussian}
For $v>0$:
\begin{enumerate}[label=(\roman*)]
\item $\Phi(v)=f\big((2v)^{-1/2}\big)$;
\item $\Phi$ is strictly increasing, with $\Phi'(v)=\EE\,g^2(1+vg^2)^{-2}\in(0,1]$, and $0<\Phi(v)<1$;
\item $0\le v-\Phi(v)\le3v^2$;
\item $\Phi(v)/v\to1$ as $v\downarrow0$ and $\Phi(v)\to1$ as $v\to\infty$.
\end{enumerate}
In particular, for real $\xi>0$,
\begin{equation}\label{eqn:app-iso-f-asymptotic}
\Big|f(\xi)-\frac{1}{2\xi^2}\Big|\le\frac{3}{4\xi^4}.
\end{equation}
\end{lemma}
```
-/
theorem lem_app_iso_gaussian_i :
    ∀ v : ℝ, 0 < v → isoPhi v = isoF ((2 * v) ^ (-(1 / 2 : ℝ))) := by
  intro v hv
  obtain ⟨h1, h2, -⟩ := Muon.DetEquiv.prop_app_de_nomomentum v _ hv rfl
  unfold isoPhi isoF
  exact h1.trans h2

/-- `lem:app-iso-gaussian`(ii), snapshot `cr-2026-10-23`. Part (ii) of the environment below
(the derivative is `isoPhiDeriv`, i.e. `Φ'(v) = 𝔼 g²(1+vg²)^{-2}`, and `Φ` is strictly increasing
on `(0,∞)`, the domain fixed by the lemma's preamble "For $v>0$").
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[The Gaussian scalar]\label{lem:app-iso-gaussian}
For $v>0$:
\begin{enumerate}[label=(\roman*)]
\item $\Phi(v)=f\big((2v)^{-1/2}\big)$;
\item $\Phi$ is strictly increasing, with $\Phi'(v)=\EE\,g^2(1+vg^2)^{-2}\in(0,1]$, and $0<\Phi(v)<1$;
\item $0\le v-\Phi(v)\le3v^2$;
\item $\Phi(v)/v\to1$ as $v\downarrow0$ and $\Phi(v)\to1$ as $v\to\infty$.
\end{enumerate}
In particular, for real $\xi>0$,
\begin{equation}\label{eqn:app-iso-f-asymptotic}
\Big|f(\xi)-\frac{1}{2\xi^2}\Big|\le\frac{3}{4\xi^4}.
\end{equation}
\end{lemma}
```
-/
theorem lem_app_iso_gaussian_ii :
    StrictMonoOn isoPhi (Ioi 0) ∧
    (∀ v : ℝ, 0 < v → HasDerivAt isoPhi (isoPhiDeriv v) v ∧
      0 < isoPhiDeriv v ∧ isoPhiDeriv v ≤ 1) ∧
    (∀ v : ℝ, 0 < v → 0 < isoPhi v ∧ isoPhi v < 1) := by
  have hd : ∀ v : ℝ, 0 < v → HasDerivAt isoPhi (isoPhiDeriv v) v :=
    fun v hv => p1_hasDeriv hv
  refine ⟨?_, fun v hv => ⟨hd v hv, p1_isoPhiDeriv_pos hv, p1_isoPhiDeriv_le_one hv⟩,
    fun v hv => ⟨p1_isoPhi_pos hv, p1_isoPhi_lt_one hv⟩⟩
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun v hv => (hd v (Set.mem_Ioi.mp hv)).continuousAt.continuousWithinAt) ?_
  intro v hv
  rw [interior_Ioi] at hv
  rw [(hd v (Set.mem_Ioi.mp hv)).deriv]
  exact p1_isoPhiDeriv_pos (Set.mem_Ioi.mp hv)

/-- `lem:app-iso-gaussian`(iii), snapshot `cr-2026-10-23`. Part (iii) of the environment below.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[The Gaussian scalar]\label{lem:app-iso-gaussian}
For $v>0$:
\begin{enumerate}[label=(\roman*)]
\item $\Phi(v)=f\big((2v)^{-1/2}\big)$;
\item $\Phi$ is strictly increasing, with $\Phi'(v)=\EE\,g^2(1+vg^2)^{-2}\in(0,1]$, and $0<\Phi(v)<1$;
\item $0\le v-\Phi(v)\le3v^2$;
\item $\Phi(v)/v\to1$ as $v\downarrow0$ and $\Phi(v)\to1$ as $v\to\infty$.
\end{enumerate}
In particular, for real $\xi>0$,
\begin{equation}\label{eqn:app-iso-f-asymptotic}
\Big|f(\xi)-\frac{1}{2\xi^2}\Big|\le\frac{3}{4\xi^4}.
\end{equation}
\end{lemma}
```
-/
theorem lem_app_iso_gaussian_iii :
    ∀ v : ℝ, 0 < v → 0 ≤ v - isoPhi v ∧ v - isoPhi v ≤ 3 * v ^ 2 := by
  intro v hv
  exact p2_iii hv

/-- `lem:app-iso-gaussian`(iv), snapshot `cr-2026-10-23`. Part (iv) of the environment below
(`Φ(v)/v → 1` as `v ↓ 0` and `Φ(v) → 1` as `v → ∞`).
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[The Gaussian scalar]\label{lem:app-iso-gaussian}
For $v>0$:
\begin{enumerate}[label=(\roman*)]
\item $\Phi(v)=f\big((2v)^{-1/2}\big)$;
\item $\Phi$ is strictly increasing, with $\Phi'(v)=\EE\,g^2(1+vg^2)^{-2}\in(0,1]$, and $0<\Phi(v)<1$;
\item $0\le v-\Phi(v)\le3v^2$;
\item $\Phi(v)/v\to1$ as $v\downarrow0$ and $\Phi(v)\to1$ as $v\to\infty$.
\end{enumerate}
In particular, for real $\xi>0$,
\begin{equation}\label{eqn:app-iso-f-asymptotic}
\Big|f(\xi)-\frac{1}{2\xi^2}\Big|\le\frac{3}{4\xi^4}.
\end{equation}
\end{lemma}
```
-/
theorem lem_app_iso_gaussian_iv :
    Tendsto (fun v : ℝ => isoPhi v / v) (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
    Tendsto isoPhi atTop (𝓝 1) :=
  ⟨p2_isoPhi_div_tendsto, p2_isoPhi_tendsto_atTop⟩

/-- `lem:app-iso-gaussian`, snapshot `cr-2026-10-23`: the displayed bound
`eqn:app-iso-f-asymptotic` ("In particular, for real ξ>0") of the environment below, stated as
part (v) of the declaration of record.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[The Gaussian scalar]\label{lem:app-iso-gaussian}
For $v>0$:
\begin{enumerate}[label=(\roman*)]
\item $\Phi(v)=f\big((2v)^{-1/2}\big)$;
\item $\Phi$ is strictly increasing, with $\Phi'(v)=\EE\,g^2(1+vg^2)^{-2}\in(0,1]$, and $0<\Phi(v)<1$;
\item $0\le v-\Phi(v)\le3v^2$;
\item $\Phi(v)/v\to1$ as $v\downarrow0$ and $\Phi(v)\to1$ as $v\to\infty$.
\end{enumerate}
In particular, for real $\xi>0$,
\begin{equation}\label{eqn:app-iso-f-asymptotic}
\Big|f(\xi)-\frac{1}{2\xi^2}\Big|\le\frac{3}{4\xi^4}.
\end{equation}
\end{lemma}
```
-/
theorem lem_app_iso_gaussian_v :
    ∀ ξ : ℝ, 0 < ξ → |isoF ξ - 1 / (2 * ξ ^ 2)| ≤ 3 / (4 * ξ ^ 4) := by
  intro ξ hξ
  have hv : 0 < 1 / (2 * ξ ^ 2) := by positivity
  have hF : isoF ξ = isoPhi (1 / (2 * ξ ^ 2)) := by
    rw [lem_app_iso_gaussian_i _ hv]
    congr 1
    have e : 2 * (1 / (2 * ξ ^ 2)) = (ξ ^ 2)⁻¹ := by field_simp
    rw [e, Real.inv_rpow (sq_nonneg ξ), Real.rpow_neg (sq_nonneg ξ), inv_inv,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos hξ]
  rw [hF]
  have hb := lem_app_iso_gaussian_iii _ hv
  have e : 3 * (1 / (2 * ξ ^ 2)) ^ 2 = 3 / (4 * ξ ^ 4) := by
    field_simp
    ring
  rw [abs_le]
  constructor <;> linarith [hb.1, hb.2, e]

/-! ### `lem:app-iso-weights` -/

/-- `lem:app-iso-weights`(i), snapshot `cr-2026-10-23`. Part (i) of the environment below.
The EMA weights are `Muon.emaW β`, `r_β = rW (Muon.emaW β)`, `β ∈ [0,1)`.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Scalar facts]\label{lem:app-iso-weights}
Let $\bmom\in[0,1)$.
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
r_\bmom(q)=\sum_{j:\,\emaw j>0}\Phi(\emaw j^2q),\qquad
r_\bmom'(q)=\sum_{j:\,\emaw j>0}\emaw j^2\,\Phi'(\emaw j^2q)>0 .
\]
For $\bmom>0$, $r_\bmom$ is an increasing bijection of $[0,\infty)$ onto
itself; at $\bmom=0$, $r_0=\Phi$ is an increasing bijection of $[0,\infty)$
onto $[0,1)$.
\item For $x>0$, $\Phi(x)\le\min(1,x)$, the derivative $\Phi'$ is decreasing, and
\[
1-\Phi(x)\le\sqrt{\frac\pi2}\,x^{-1/2},\qquad
x\,\Phi'(x)\le\min\Big(x,\sqrt{\frac\pi2}\,x^{-1/2}\Big).
\]
\item For $x>0$, $\Jfun(x)\le\min(1,1/x)$ and $-3\le\Jfun'(x)\le0$.
\item For $q,z\ge0$,
\[
\Lambda_\bmom(q)=\sum_{j:\,\emaw j>0}\Lambda_0(\emaw j^2q),\qquad
\Lambda_0(z)\le2\sqrt z,\qquad
0\le\sqrt{2\pi}-\Lambda_0(z)\le2z^{-1/2},
\]
and $\Lambda_0(z)\uparrow\sqrt{2\pi}$ as $z\to\infty$.
\item $\Fw\le\sw2$ and $\Lw\le1$, and $q\mapsto q\Lw(q)$ is strictly increasing.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_weights_i {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∀ q : ℝ, 0 ≤ q → rW (Muon.emaW β) q =
      ∑' j : {j : ℕ | 0 < Muon.emaW β j}, isoPhi (Muon.emaW β j ^ 2 * q)) ∧
    (∀ q : ℝ, 0 ≤ q →
      HasDerivWithinAt (rW (Muon.emaW β)) (isoRderiv β q) (Ici 0) q ∧ 0 < isoRderiv β q) ∧
    (0 < β → StrictMonoOn (rW (Muon.emaW β)) (Ici 0) ∧
      BijOn (rW (Muon.emaW β)) (Ici 0) (Ici 0)) ∧
    (β = 0 → (∀ q : ℝ, 0 ≤ q → rW (Muon.emaW β) q = isoPhi q) ∧
      StrictMonoOn (rW (Muon.emaW β)) (Ici 0) ∧
      BijOn (rW (Muon.emaW β)) (Ici 0) (Ico 0 1)) := by
  have hc : ContinuousOn (rW (Muon.emaW β)) (Ici 0) := fun q hq =>
    (p3_rW_hasDerivWithinAt hβ0 hβ1 (Set.mem_Ici.mp hq)).continuousWithinAt
  have hmono : StrictMonoOn (rW (Muon.emaW β)) (Ici 0) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0) hc (f' := isoRderiv β)
      (fun q hq => (p3_rW_hasDerivWithinAt hβ0 hβ1 (Set.mem_Ici.mp (interior_subset hq))).mono
        interior_subset)
      (fun q hq => p3_isoRderiv_pos hβ0 hβ1 (Set.mem_Ici.mp (interior_subset hq)))
  have hval0 : rW (Muon.emaW β) 0 = 0 := by
    unfold rW
    simp
  refine ⟨fun q hq => p3_rW_eq hβ0 hβ1 hq,
    fun q hq => ⟨p3_rW_hasDerivWithinAt hβ0 hβ1 hq, p3_isoRderiv_pos hβ0 hβ1 hq⟩,
    fun hpos => ⟨hmono, ⟨fun q hq => ?_, hmono.injOn, ?_⟩⟩, fun hz => ?_⟩
  · rw [p3_rW_eq hβ0 hβ1 (Set.mem_Ici.mp hq)]
    exact tsum_nonneg fun j => (p3_isoPhi_bounds (mul_nonneg (sq_nonneg _)
      (Set.mem_Ici.mp hq))).1
  · intro y hy
    obtain ⟨q, hq, e⟩ := p3_surj (S := Ici 0) subset_rfl hc hval0
      (p3_rW_unbounded hpos hβ1) y hy
    exact ⟨q, Set.mem_Ici.mpr hq, e⟩
  · subst hz
    refine ⟨fun q hq => p3_rW_zero q, hmono, ⟨fun q hq => ?_, hmono.injOn, ?_⟩⟩
    · rw [p3_rW_zero]
      rcases (Set.mem_Ici.mp hq).eq_or_lt with h | h
      · rw [← h, p3_isoPhi_zero]
        exact ⟨le_rfl, one_pos⟩
      · exact ⟨(p3_isoPhi_bounds (Set.mem_Ici.mp hq)).1, p1_isoPhi_lt_one h⟩
    · intro y hy
      obtain ⟨q, hq, e⟩ := p3_surj (S := Ico (0 : ℝ) 1) Ico_subset_Ici_self hc hval0
        (fun y hy => by
          simp only [p3_rW_zero]
          have hev := (p2_isoPhi_tendsto_atTop.eventually (lt_mem_nhds hy.2)).and
            (eventually_ge_atTop (0 : ℝ))
          obtain ⟨Q, h1, h2⟩ := hev.exists
          exact ⟨Q, h2, h1⟩) y hy
      exact ⟨q, Set.mem_Ici.mpr hq, e⟩

/-- `lem:app-iso-weights`(ii), snapshot `cr-2026-10-23`. Part (ii) of the environment below.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Scalar facts]\label{lem:app-iso-weights}
Let $\bmom\in[0,1)$.
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
r_\bmom(q)=\sum_{j:\,\emaw j>0}\Phi(\emaw j^2q),\qquad
r_\bmom'(q)=\sum_{j:\,\emaw j>0}\emaw j^2\,\Phi'(\emaw j^2q)>0 .
\]
For $\bmom>0$, $r_\bmom$ is an increasing bijection of $[0,\infty)$ onto
itself; at $\bmom=0$, $r_0=\Phi$ is an increasing bijection of $[0,\infty)$
onto $[0,1)$.
\item For $x>0$, $\Phi(x)\le\min(1,x)$, the derivative $\Phi'$ is decreasing, and
\[
1-\Phi(x)\le\sqrt{\frac\pi2}\,x^{-1/2},\qquad
x\,\Phi'(x)\le\min\Big(x,\sqrt{\frac\pi2}\,x^{-1/2}\Big).
\]
\item For $x>0$, $\Jfun(x)\le\min(1,1/x)$ and $-3\le\Jfun'(x)\le0$.
\item For $q,z\ge0$,
\[
\Lambda_\bmom(q)=\sum_{j:\,\emaw j>0}\Lambda_0(\emaw j^2q),\qquad
\Lambda_0(z)\le2\sqrt z,\qquad
0\le\sqrt{2\pi}-\Lambda_0(z)\le2z^{-1/2},
\]
and $\Lambda_0(z)\uparrow\sqrt{2\pi}$ as $z\to\infty$.
\item $\Fw\le\sw2$ and $\Lw\le1$, and $q\mapsto q\Lw(q)$ is strictly increasing.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_weights_ii :
    (∀ x : ℝ, 0 < x → isoPhi x ≤ min 1 x) ∧
    AntitoneOn isoPhiDeriv (Ioi 0) ∧
    (∀ x : ℝ, 0 < x →
      1 - isoPhi x ≤ Real.sqrt (Real.pi / 2) * x ^ (-(1 / 2 : ℝ)) ∧
      x * isoPhiDeriv x ≤ min x (Real.sqrt (Real.pi / 2) * x ^ (-(1 / 2 : ℝ)))) := by
  refine ⟨fun x hx => le_min (p1_isoPhi_lt_one hx).le (p3_isoPhi_bounds hx.le).2, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : (0 : ℝ) < a := ha
    have hb' : (0 : ℝ) < b := hb
    unfold isoPhiDeriv
    refine integral_mono (p1_deriv_int hb'.le) (p1_deriv_int ha'.le) (fun g => ?_)
    have hA := p1_den_pos ha'.le g
    have hAB : 1 + a * g ^ 2 ≤ 1 + b * g ^ 2 := by
      have := mul_le_mul_of_nonneg_right hab (sq_nonneg g)
      linarith
    exact div_le_div_of_nonneg_left (sq_nonneg g) (pow_pos hA 2) (by nlinarith)
  · intro x hx
    have hB : 1 - isoPhi x ≤ Real.sqrt (Real.pi / 2) * x ^ (-(1 / 2 : ℝ)) := by
      rw [p3_one_sub_eq hx]
      exact p3_gauss_inv_le hx
    exact ⟨hB, le_min (mul_le_of_le_one_right hx.le (p3_dPhi_bounds hx.le).2)
      ((p3_xdPhi_le hx).trans hB)⟩

/-- `lem:app-iso-weights`(iii), snapshot `cr-2026-10-23`. Part (iii) of the environment below.
The derivative of `J` is stated as `deriv J` together with `DifferentiableAt`.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Scalar facts]\label{lem:app-iso-weights}
Let $\bmom\in[0,1)$.
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
r_\bmom(q)=\sum_{j:\,\emaw j>0}\Phi(\emaw j^2q),\qquad
r_\bmom'(q)=\sum_{j:\,\emaw j>0}\emaw j^2\,\Phi'(\emaw j^2q)>0 .
\]
For $\bmom>0$, $r_\bmom$ is an increasing bijection of $[0,\infty)$ onto
itself; at $\bmom=0$, $r_0=\Phi$ is an increasing bijection of $[0,\infty)$
onto $[0,1)$.
\item For $x>0$, $\Phi(x)\le\min(1,x)$, the derivative $\Phi'$ is decreasing, and
\[
1-\Phi(x)\le\sqrt{\frac\pi2}\,x^{-1/2},\qquad
x\,\Phi'(x)\le\min\Big(x,\sqrt{\frac\pi2}\,x^{-1/2}\Big).
\]
\item For $x>0$, $\Jfun(x)\le\min(1,1/x)$ and $-3\le\Jfun'(x)\le0$.
\item For $q,z\ge0$,
\[
\Lambda_\bmom(q)=\sum_{j:\,\emaw j>0}\Lambda_0(\emaw j^2q),\qquad
\Lambda_0(z)\le2\sqrt z,\qquad
0\le\sqrt{2\pi}-\Lambda_0(z)\le2z^{-1/2},
\]
and $\Lambda_0(z)\uparrow\sqrt{2\pi}$ as $z\to\infty$.
\item $\Fw\le\sw2$ and $\Lw\le1$, and $q\mapsto q\Lw(q)$ is strictly increasing.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_weights_iii :
    (∀ x : ℝ, 0 < x → J x ≤ min 1 (1 / x)) ∧
    (∀ x : ℝ, 0 < x → DifferentiableAt ℝ J x ∧ -3 ≤ deriv J x ∧ deriv J x ≤ 0) := by
  refine ⟨fun x hx => le_min ?_ ?_, fun x hx => ⟨(p3_J_hasDeriv hx).differentiableAt, ?_⟩⟩
  · rw [p3_J_eq hx]
    exact (p2_J_bounds hx).2
  · rw [p3_J_eq hx]
    exact div_le_div_of_nonneg_right (p1_isoPhi_lt_one hx).le hx.le
  · have hd := (p3_J_hasDeriv hx).deriv
    have hI : Integrable (fun g : ℝ => g ^ 4 / (1 + x * g ^ 2) ^ 2) (gaussianReal 0 1) :=
      p1_bound_of_le (Muon.Foundations.gaussian_integrable_pow 4) (by fun_prop)
        (fun g => by
          rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) (sq_nonneg _))]
          exact p3_g4_le hx.le g)
    have h3 : ∫ g, -(g ^ 4) ∂(gaussianReal 0 1) = -3 := by
      rw [integral_neg, Muon.Foundations.gaussian_moment_four]
    have hle : ∫ g, -(g ^ 4) ∂(gaussianReal 0 1) ≤
        ∫ g, -(g ^ 4 / (1 + x * g ^ 2) ^ 2) ∂(gaussianReal 0 1) :=
      integral_mono (Muon.Foundations.gaussian_integrable_pow 4).neg hI.neg
        (fun g => neg_le_neg (p3_g4_le hx.le g))
    rw [hd]
    constructor
    · linarith
    · refine integral_nonpos (fun g => ?_)
      exact neg_nonpos.mpr (div_nonneg (by positivity) (sq_nonneg _))

/-! ### Private helpers for `lem_app_iso_weights` (v) (fully proved, task P-F.1.P4) -/

private lemma p4_J_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ J x := by
  unfold J
  exact integral_nonneg (fun g => div_nonneg (sq_nonneg g) (p1_den_pos hx g).le)

private lemma p4_J_le_one {x : ℝ} (hx : 0 ≤ x) : J x ≤ 1 := by
  rcases hx.eq_or_lt with h | h
  · rw [← h]
    unfold J
    simp only [zero_mul, add_zero, div_one]
    exact Muon.Foundations.gaussian_moment_two.le
  · exact ((lem_app_iso_weights_iii).1 x h).trans (min_le_left _ _)

private lemma p4_isoPhi_mono {v1 v2 : ℝ} (hv1 : 0 ≤ v1) (h : v1 ≤ v2) :
    isoPhi v1 ≤ isoPhi v2 := by
  rcases hv1.eq_or_lt with h0 | hpos
  · rw [← h0, p3_isoPhi_zero]
    exact (p3_isoPhi_bounds (le_trans hv1 h)).1
  · rcases h.eq_or_lt with heq | hlt
    · exact le_of_eq (congrArg isoPhi heq)
    · exact ((lem_app_iso_gaussian_ii).1 hpos (lt_trans hpos hlt) hlt).le

private lemma p4_isoPhi_strict {v1 v2 : ℝ} (hv1 : 0 ≤ v1) (h : v1 < v2) :
    isoPhi v1 < isoPhi v2 := by
  rcases hv1.eq_or_lt with h0 | hpos
  · rw [← h0, p3_isoPhi_zero]
    exact p1_isoPhi_pos (lt_of_le_of_lt hv1 h)
  · exact (lem_app_iso_gaussian_ii).1 hpos (lt_trans hpos h) h

private lemma p4_term_eq {w q : ℝ} (hw : 0 < w) :
    q * (w * J (w ^ 2 * q)) = isoPhi (w ^ 2 * q) / w := by
  unfold isoPhi
  rw [eq_div_iff hw.ne']
  ring

private lemma p4_term_mono {w q1 q2 : ℝ} (hw : 0 < w) (h1 : 0 ≤ q1) (h12 : q1 ≤ q2) :
    q1 * (w * J (w ^ 2 * q1)) ≤ q2 * (w * J (w ^ 2 * q2)) := by
  rw [p4_term_eq hw, p4_term_eq hw]
  exact div_le_div_of_nonneg_right
    (p4_isoPhi_mono (mul_nonneg (sq_nonneg w) h1) (mul_le_mul_of_nonneg_left h12 (sq_nonneg w)))
    hw.le

private lemma p4_term_strict {w q1 q2 : ℝ} (hw : 0 < w) (h1 : 0 ≤ q1) (h12 : q1 < q2) :
    q1 * (w * J (w ^ 2 * q1)) < q2 * (w * J (w ^ 2 * q2)) := by
  rw [p4_term_eq hw, p4_term_eq hw]
  exact div_lt_div_of_pos_right
    (p4_isoPhi_strict (mul_nonneg (sq_nonneg w) h1) (mul_lt_mul_of_pos_left h12 (pow_pos hw 2)))
    hw

/-! ### Private helpers for `lem_app_iso_weights` (iv) (fully proved, task P-F.1.P4) -/

private lemma p4_inner {a z : ℝ} (hz : 0 ≤ z) :
    ∫ x in (0 : ℝ)..z, x ^ (-(1 / 2 : ℝ)) * (a ^ 2 / (1 + x * a ^ 2))
      = 2 * |a| * Real.arctan (Real.sqrt z * |a|) := by
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) z, HasDerivAt (fun x : ℝ => 2 * |a| * Real.arctan (Real.sqrt x * |a|))
      (x ^ (-(1 / 2 : ℝ)) * (a ^ 2 / (1 + x * a ^ 2))) x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have h1 : HasDerivAt (fun x : ℝ => Real.sqrt x * |a|) (1 / (2 * Real.sqrt x) * |a|) x :=
      (Real.hasDerivAt_sqrt hx0.ne').mul_const _
    have h2 := (h1.arctan).const_mul (2 * |a|)
    convert h2 using 1
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, mul_pow, hsq, sq_abs]
    have : 0 < 1 + x * a ^ 2 := by positivity
    field_simp
    ring_nf
    exact (sq_abs a).symm
  have hcont : ContinuousOn (fun x : ℝ => 2 * |a| * Real.arctan (Real.sqrt x * |a|)) (Icc 0 z) := by
    apply Continuous.continuousOn
    fun_prop
  have hint : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * (a ^ 2 / (1 + x * a ^ 2)))
      volume 0 z := by
    refine (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).mul_continuousOn ?_
    intro x hx
    have : 0 < 1 + x * a ^ 2 := by
      have hx' : 0 ≤ x := by
        rw [Set.uIcc_of_le hz] at hx; exact hx.1
      positivity
    exact (ContinuousAt.div continuousAt_const (by fun_prop : ContinuousAt (fun x : ℝ => 1 + x * a ^ 2) x) this.ne').continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hz hcont
    (fun x hx => (hderiv x hx).hasDerivWithinAt) hint]
  simp

private lemma p4_Lw_zero (x : ℝ) : Lw (Muon.emaW 0) x = J x := by
  unfold Lw
  rw [tsum_eq_single 0]
  · simp [Muon.emaW]
  · intro j hj
    simp [Muon.emaW, zero_pow hj]

private lemma p4_gauss_abs_integrable : Integrable (fun g : ℝ => |g|) (gaussianReal 0 1) := by
  refine ((Muon.Foundations.gaussian_integrable_pow 2).add (integrable_const (1 : ℝ))).mono'
    (continuous_abs.aestronglyMeasurable) (Eventually.of_forall fun g => ?_)
  simp only [Real.norm_eq_abs, abs_abs, Pi.add_apply]
  nlinarith [sq_nonneg (|g| - 1), sq_abs g]

private lemma p4_lam_eq {z : ℝ} (hz : 0 ≤ z) :
    isoLambda 0 z = ∫ g, 2 * |g| * Real.arctan (Real.sqrt z * |g|) ∂(gaussianReal 0 1) := by
  have h1 : isoLambda 0 z = ∫ x in (0 : ℝ)..z, ∫ g, x ^ (-(1 / 2 : ℝ)) * (g ^ 2 / (1 + x * g ^ 2))
      ∂(gaussianReal 0 1) := by
    unfold isoLambda
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [p4_Lw_zero, J]
    rw [integral_const_mul]
  rw [h1, intervalIntegral.integral_of_le hz]
  have hmeas : Measurable (fun p : ℝ × ℝ => p.1 ^ (-(1 / 2 : ℝ)) * (p.2 ^ 2 / (1 + p.1 * p.2 ^ 2))) := by
    fun_prop
  have hint : Integrable (Function.uncurry fun (x g : ℝ) => x ^ (-(1 / 2 : ℝ)) * (g ^ 2 / (1 + x * g ^ 2)))
      ((volume.restrict (Ioc (0 : ℝ) z)).prod (gaussianReal 0 1)) := by
    have hb : Integrable (fun p : ℝ × ℝ => p.1 ^ (-(1 / 2 : ℝ)) * p.2 ^ 2)
        ((volume.restrict (Ioc (0 : ℝ) z)).prod (gaussianReal 0 1)) := by
      have h1 : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Ioc 0 z) :=
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).1
      exact Integrable.mul_prod (f := fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
        (g := fun g : ℝ => g ^ 2) h1 (Muon.Foundations.gaussian_integrable_pow 2)
    refine hb.mono' hmeas.aestronglyMeasurable ?_
    have hx : ∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) z)).prod (gaussianReal 0 1)), p.1 ∈ Ioc (0 : ℝ) z :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hx] with p hp
    have hp0 : 0 < p.1 := hp.1
    have hd : 0 < 1 + p.1 * p.2 ^ 2 := by positivity
    have hrp : 0 < p.1 ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hp0 _
    rw [Real.norm_eq_abs]
    show |p.1 ^ (-(1 / 2 : ℝ)) * (p.2 ^ 2 / (1 + p.1 * p.2 ^ 2))| ≤ _
    rw [abs_of_nonneg (by positivity)]
    gcongr
    calc p.2 ^ 2 / (1 + p.1 * p.2 ^ 2) ≤ p.2 ^ 2 / 1 :=
          div_le_div_of_nonneg_left (sq_nonneg _) one_pos (by nlinarith [sq_nonneg p.2])
      _ = p.2 ^ 2 := div_one _
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  rw [← intervalIntegral.integral_of_le hz]
  exact p4_inner hz

private lemma p4_integrand_integrable (z : ℝ) :
    Integrable (fun g : ℝ => 2 * |g| * Real.arctan (Real.sqrt z * |g|)) (gaussianReal 0 1) := by
  refine (p4_gauss_abs_integrable.const_mul Real.pi).mono'
    (by fun_prop : Continuous fun g : ℝ => 2 * |g| * Real.arctan (Real.sqrt z * |g|)).aestronglyMeasurable
    (Eventually.of_forall fun g => ?_)
  have h0 : 0 ≤ Real.arctan (Real.sqrt z * |g|) := Real.arctan_nonneg.mpr (by positivity)
  have h1 := Real.arctan_lt_pi_div_two (Real.sqrt z * |g|)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [abs_nonneg g]

private lemma p4_sqrt_eq : Real.sqrt (2 * Real.pi) = ∫ g, Real.pi * |g| ∂(gaussianReal 0 1) := by
  rw [integral_const_mul, Muon.Foundations.gaussian_abs_moment]
  have : 2 * Real.pi = Real.pi ^ 2 * (2 / Real.pi) := by
    field_simp
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq Real.pi_pos.le]

private lemma p4_lam_le {z : ℝ} (hz : 0 ≤ z) : isoLambda 0 z ≤ 2 * Real.sqrt z := by
  rw [p4_lam_eq hz]
  have hb : ∫ g, 2 * Real.sqrt z * g ^ 2 ∂(gaussianReal 0 1) = 2 * Real.sqrt z := by
    rw [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one]
  rw [← hb]
  refine integral_mono (p4_integrand_integrable z)
    ((Muon.Foundations.gaussian_integrable_pow 2).const_mul _) (fun g => ?_)
  have h := Real.arctan_le_self (x := Real.sqrt z * |g|) (by positivity)
  have : g ^ 2 = |g| * |g| := by rw [← sq_abs]; ring
  rw [this]
  nlinarith [abs_nonneg g, mul_le_mul_of_nonneg_left h (abs_nonneg g)]

private lemma p4_lam_mono {z1 z2 : ℝ} (h1 : 0 ≤ z1) (h : z1 ≤ z2) : isoLambda 0 z1 ≤ isoLambda 0 z2 := by
  rw [p4_lam_eq h1, p4_lam_eq (h1.trans h)]
  refine integral_mono (p4_integrand_integrable z1) (p4_integrand_integrable z2) (fun g => ?_)
  have := Real.arctan_le_arctan_iff.mpr (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h) (abs_nonneg g))
  nlinarith [abs_nonneg g, mul_le_mul_of_nonneg_left this (abs_nonneg g)]

private lemma p4_gap_eq {z : ℝ} (hz : 0 ≤ z) : Real.sqrt (2 * Real.pi) - isoLambda 0 z
    = ∫ g, 2 * |g| * (Real.pi / 2 - Real.arctan (Real.sqrt z * |g|)) ∂(gaussianReal 0 1) := by
  rw [p4_lam_eq hz, p4_sqrt_eq, ← integral_sub (p4_gauss_abs_integrable.const_mul Real.pi)
    (p4_integrand_integrable z)]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  ring

private lemma p4_gap_integrable (z : ℝ) :
    Integrable (fun g : ℝ => 2 * |g| * (Real.pi / 2 - Real.arctan (Real.sqrt z * |g|)))
      (gaussianReal 0 1) := by
  have := (p4_gauss_abs_integrable.const_mul Real.pi).sub (p4_integrand_integrable z)
  refine this.congr (Eventually.of_forall fun g => ?_)
  simp only [Pi.sub_apply]
  ring

private lemma p4_lam_tail {z : ℝ} (hz : 0 < z) :
    0 ≤ Real.sqrt (2 * Real.pi) - isoLambda 0 z ∧
      Real.sqrt (2 * Real.pi) - isoLambda 0 z ≤ 2 * z ^ (-(1 / 2 : ℝ)) := by
  rw [p4_gap_eq hz.le]
  have hs : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz
  refine ⟨integral_nonneg fun g => ?_, ?_⟩
  · have := Real.arctan_lt_pi_div_two (Real.sqrt z * |g|)
    simp only [Pi.zero_apply]
    exact mul_nonneg (by positivity) (by linarith)
  · have hc : ∫ g, (2 * z ^ (-(1 / 2 : ℝ))) ∂(gaussianReal 0 1) = 2 * z ^ (-(1 / 2 : ℝ)) := by
      simp
    rw [← hc]
    refine integral_mono (p4_gap_integrable z) (integrable_const _) (fun g => ?_)
    simp only
    have hz2 : z ^ (-(1 / 2 : ℝ)) = (Real.sqrt z)⁻¹ := by
      rw [Real.rpow_neg hz.le, ← Real.sqrt_eq_rpow]
    rw [hz2]
    rcases (abs_nonneg g).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hpos' : 0 < Real.sqrt z * |g| := mul_pos hs hpos
      have h1 : Real.pi / 2 - Real.arctan (Real.sqrt z * |g|) = Real.arctan (Real.sqrt z * |g|)⁻¹ := by
        rw [Real.arctan_inv_of_pos hpos']
      have h2 : Real.arctan (Real.sqrt z * |g|)⁻¹ ≤ (Real.sqrt z * |g|)⁻¹ :=
        Real.arctan_le_self (by positivity)
      rw [h1]
      calc 2 * |g| * Real.arctan (Real.sqrt z * |g|)⁻¹ ≤ 2 * |g| * (Real.sqrt z * |g|)⁻¹ :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2 * (Real.sqrt z)⁻¹ := by field_simp

private lemma p4_lam_tendsto :
    Tendsto (isoLambda 0) atTop (𝓝 (Real.sqrt (2 * Real.pi))) := by
  rw [p4_sqrt_eq]
  have hlim : Tendsto (fun z : ℝ => ∫ g, 2 * |g| * Real.arctan (Real.sqrt z * |g|) ∂(gaussianReal 0 1))
      atTop (𝓝 (∫ g, Real.pi * |g| ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun g => Real.pi * |g|)
      (Eventually.of_forall fun z => (p4_integrand_integrable z).aestronglyMeasurable)
      (eventually_ge_atTop 0 |>.mono fun z hz => Eventually.of_forall fun g => ?_)
      (p4_gauss_abs_integrable.const_mul Real.pi) (Eventually.of_forall fun g => ?_)
    · have h0 : 0 ≤ Real.arctan (Real.sqrt z * |g|) := Real.arctan_nonneg.mpr (by positivity)
      have h1 := Real.arctan_lt_pi_div_two (Real.sqrt z * |g|)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [abs_nonneg g]
    · rcases (abs_nonneg g).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have h1 : Tendsto (fun z : ℝ => Real.sqrt z * |g|) atTop atTop :=
          Real.tendsto_sqrt_atTop.atTop_mul_const hpos
        have h2 := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1).const_mul (2 * |g|)
        have : 2 * |g| * (Real.pi / 2) = Real.pi * |g| := by ring
        rw [this] at h2
        exact h2
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with z hz
  exact (p4_lam_eq hz).symm


private lemma p4_J_meas : Measurable J := by
  have h : StronglyMeasurable (fun p : ℝ × ℝ => p.2 ^ 2 / (1 + p.1 * p.2 ^ 2)) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ => p.2 ^ 2 / (1 + p.1 * p.2 ^ 2)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := gaussianReal 0 1)).measurable

private lemma p4_term_integral {w q : ℝ} (hw : 0 < w) (hq : 0 ≤ q) :
    ∫ t in (0 : ℝ)..q, t ^ (-(1 / 2 : ℝ)) * (w * J (w ^ 2 * t)) = isoLambda 0 (w ^ 2 * q) := by
  have hw2 : 0 < w ^ 2 := by positivity
  have h1 : ∀ t ∈ Set.uIcc (0 : ℝ) q, t ^ (-(1 / 2 : ℝ)) * (w * J (w ^ 2 * t))
      = w ^ 2 * ((w ^ 2 * t) ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW 0) (w ^ 2 * t)) := by
    intro t ht
    have ht0 : 0 ≤ t := by rw [Set.uIcc_of_le hq] at ht; exact ht.1
    rw [p4_Lw_zero, Real.mul_rpow hw2.le ht0, ← mul_assoc, ← mul_assoc]
    have : (w ^ 2) ^ (-(1 / 2 : ℝ)) = w⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
      norm_num
      exact Real.rpow_neg_one w
    rw [this]
    field_simp
  rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_const_mul]
  have := intervalIntegral.integral_comp_mul_left
    (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW 0) x) (a := 0) (b := q) hw2.ne'
  simp only [smul_eq_mul, mul_zero] at this
  rw [this]
  unfold isoLambda
  field_simp

private lemma p4_lam_sum {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    isoLambda β q = ∑' j : {j : ℕ | 0 < Muon.emaW β j}, isoLambda 0 (Muon.emaW β j ^ 2 * q) := by
  set F : ℕ → ℝ → ℝ := fun j t => t ^ (-(1 / 2 : ℝ)) * (Muon.emaW β j * J (Muon.emaW β j ^ 2 * t))
    with hF
  have hw0 := p3_emaW_nonneg hβ0 hβ1
  have hsum := p3_emaW_summable hβ0 hβ1
  have htot : ∑' j : ℕ, Muon.emaW β j = 1 := Muon.tsum_emaW hβ0 hβ1
  have hmeasF : ∀ j, Measurable (F j) := by
    intro j
    have := p4_J_meas
    fun_prop
  have hIoc : Set.uIoc (0 : ℝ) q = Ioc 0 q := Set.uIoc_of_le hq
  have key : HasSum (fun j => ∫ t in (0 : ℝ)..q, F j t)
      (∫ t in (0 : ℝ)..q, t ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW β) t) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun j t => t ^ (-(1 / 2 : ℝ)) * Muon.emaW β j) (fun j => (hmeasF j).aestronglyMeasurable)
      ?_ ?_ ?_ ?_
    · intro j
      refine Eventually.of_forall fun t ht => ?_
      rw [hIoc] at ht
      have ht0 : 0 < t := ht.1
      have hr : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht0 _
      have hJ0 := p4_J_nonneg (mul_nonneg (sq_nonneg (Muon.emaW β j)) ht0.le)
      have hJ1 := p4_J_le_one (mul_nonneg (sq_nonneg (Muon.emaW β j)) ht0.le)
      simp only [hF]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr.le (mul_nonneg (hw0 j) hJ0))]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (hw0 j) hJ1) hr.le
    · exact Eventually.of_forall fun t _ => hsum.mul_left _
    · have : (fun t : ℝ => ∑' j : ℕ, t ^ (-(1 / 2 : ℝ)) * Muon.emaW β j)
          = fun t => t ^ (-(1 / 2 : ℝ)) := by
        funext t
        rw [tsum_mul_left, htot, mul_one]
      rw [this]
      exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    · refine Eventually.of_forall fun t ht => ?_
      rw [hIoc] at ht
      have ht0 : 0 < t := ht.1
      have hs : Summable (fun j : ℕ => Muon.emaW β j * J (Muon.emaW β j ^ 2 * t)) :=
        Summable.of_nonneg_of_le
          (fun j => mul_nonneg (hw0 j) (p4_J_nonneg (mul_nonneg (sq_nonneg _) ht0.le)))
          (fun j => mul_le_of_le_one_right (hw0 j)
            (p4_J_le_one (mul_nonneg (sq_nonneg _) ht0.le))) hsum
      have := (hs.hasSum.mul_left (t ^ (-(1 / 2 : ℝ))))
      simpa only [hF, Lw] using this
  have h2 := key.tsum_eq
  have h3 : isoLambda β q = ∑' j : ℕ, ∫ t in (0 : ℝ)..q, F j t := by
    rw [h2]
    rfl
  rw [h3]
  rw [← tsum_subtype_eq_of_support_subset (s := {j : ℕ | 0 < Muon.emaW β j})]
  · refine tsum_congr fun j => ?_
    exact p4_term_integral j.2 hq
  · intro j hj
    by_contra hnot
    apply hj
    have hz : Muon.emaW β j = 0 := le_antisymm (not_lt.mp hnot) (hw0 j)
    simp [hF, hz]

/-- `lem:app-iso-weights`(iv), snapshot `cr-2026-10-23`. Part (iv) of the environment below.
`Λ_0 = isoLambda 0`. Part (iii) of the environment below is restricted to `z > 0`, since
`z^{-1/2}` is not defined at `z = 0` (card §6, interface note; `open_questions`).
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Scalar facts]\label{lem:app-iso-weights}
Let $\bmom\in[0,1)$.
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
r_\bmom(q)=\sum_{j:\,\emaw j>0}\Phi(\emaw j^2q),\qquad
r_\bmom'(q)=\sum_{j:\,\emaw j>0}\emaw j^2\,\Phi'(\emaw j^2q)>0 .
\]
For $\bmom>0$, $r_\bmom$ is an increasing bijection of $[0,\infty)$ onto
itself; at $\bmom=0$, $r_0=\Phi$ is an increasing bijection of $[0,\infty)$
onto $[0,1)$.
\item For $x>0$, $\Phi(x)\le\min(1,x)$, the derivative $\Phi'$ is decreasing, and
\[
1-\Phi(x)\le\sqrt{\frac\pi2}\,x^{-1/2},\qquad
x\,\Phi'(x)\le\min\Big(x,\sqrt{\frac\pi2}\,x^{-1/2}\Big).
\]
\item For $x>0$, $\Jfun(x)\le\min(1,1/x)$ and $-3\le\Jfun'(x)\le0$.
\item For $q,z\ge0$,
\[
\Lambda_\bmom(q)=\sum_{j:\,\emaw j>0}\Lambda_0(\emaw j^2q),\qquad
\Lambda_0(z)\le2\sqrt z,\qquad
0\le\sqrt{2\pi}-\Lambda_0(z)\le2z^{-1/2},
\]
and $\Lambda_0(z)\uparrow\sqrt{2\pi}$ as $z\to\infty$.
\item $\Fw\le\sw2$ and $\Lw\le1$, and $q\mapsto q\Lw(q)$ is strictly increasing.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_weights_iv {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∀ q : ℝ, 0 ≤ q → isoLambda β q =
      ∑' j : {j : ℕ | 0 < Muon.emaW β j}, isoLambda 0 (Muon.emaW β j ^ 2 * q)) ∧
    (∀ z : ℝ, 0 ≤ z → isoLambda 0 z ≤ 2 * Real.sqrt z) ∧
    (∀ z : ℝ, 0 < z →
      0 ≤ Real.sqrt (2 * Real.pi) - isoLambda 0 z ∧
      Real.sqrt (2 * Real.pi) - isoLambda 0 z ≤ 2 * z ^ (-(1 / 2 : ℝ))) ∧
    MonotoneOn (isoLambda 0) (Ici 0) ∧
    Tendsto (isoLambda 0) atTop (𝓝 (Real.sqrt (2 * Real.pi))) :=
  ⟨fun _ hq => p4_lam_sum hβ0 hβ1 hq, fun _ hz => p4_lam_le hz, fun _ hz => p4_lam_tail hz,
    fun _ h1 _ _ h => p4_lam_mono h1 h, p4_lam_tendsto⟩

/-- `lem:app-iso-weights`(v), snapshot `cr-2026-10-23`. Part (v) of the environment below.
The sums `s_2 = Muon.sPow β 2`; the bounds are for `q ≥ 0`, the domain of `F_w`, `L_w`.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Scalar facts]\label{lem:app-iso-weights}
Let $\bmom\in[0,1)$.
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
r_\bmom(q)=\sum_{j:\,\emaw j>0}\Phi(\emaw j^2q),\qquad
r_\bmom'(q)=\sum_{j:\,\emaw j>0}\emaw j^2\,\Phi'(\emaw j^2q)>0 .
\]
For $\bmom>0$, $r_\bmom$ is an increasing bijection of $[0,\infty)$ onto
itself; at $\bmom=0$, $r_0=\Phi$ is an increasing bijection of $[0,\infty)$
onto $[0,1)$.
\item For $x>0$, $\Phi(x)\le\min(1,x)$, the derivative $\Phi'$ is decreasing, and
\[
1-\Phi(x)\le\sqrt{\frac\pi2}\,x^{-1/2},\qquad
x\,\Phi'(x)\le\min\Big(x,\sqrt{\frac\pi2}\,x^{-1/2}\Big).
\]
\item For $x>0$, $\Jfun(x)\le\min(1,1/x)$ and $-3\le\Jfun'(x)\le0$.
\item For $q,z\ge0$,
\[
\Lambda_\bmom(q)=\sum_{j:\,\emaw j>0}\Lambda_0(\emaw j^2q),\qquad
\Lambda_0(z)\le2\sqrt z,\qquad
0\le\sqrt{2\pi}-\Lambda_0(z)\le2z^{-1/2},
\]
and $\Lambda_0(z)\uparrow\sqrt{2\pi}$ as $z\to\infty$.
\item $\Fw\le\sw2$ and $\Lw\le1$, and $q\mapsto q\Lw(q)$ is strictly increasing.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_weights_v {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∀ q : ℝ, 0 ≤ q → Fw (Muon.emaW β) q ≤ Muon.sPow β 2) ∧
    (∀ q : ℝ, 0 ≤ q → Lw (Muon.emaW β) q ≤ 1) ∧
    StrictMonoOn (fun q : ℝ => q * Lw (Muon.emaW β) q) (Ici 0) := by
  have hw0 : ∀ j : ℕ, 0 ≤ Muon.emaW β j := p3_emaW_nonneg hβ0 hβ1
  have hsum : Summable (fun j : ℕ => Muon.emaW β j) := p3_emaW_summable hβ0 hβ1
  have hsq : Summable (fun j : ℕ => Muon.emaW β j ^ 2) := p3_sq_summable hβ0 hβ1
  have htot : ∑' j : ℕ, Muon.emaW β j = 1 := tsum_emaW hβ0 hβ1
  have hpos0 : 0 < Muon.emaW β 0 := by
    unfold Muon.emaW
    rw [pow_zero, mul_one]
    linarith
  have hFw : ∀ q : ℝ, 0 ≤ q → Fw (Muon.emaW β) q ≤ Muon.sPow β 2 := by
    intro q hq
    have hJa : ∀ j : ℕ, 0 ≤ Muon.emaW β j ^ 2 * J (Muon.emaW β j ^ 2 * q) := fun j =>
      mul_nonneg (sq_nonneg _) (p4_J_nonneg (mul_nonneg (sq_nonneg _) hq))
    have hle : ∀ j : ℕ, Muon.emaW β j ^ 2 * J (Muon.emaW β j ^ 2 * q) ≤ Muon.emaW β j ^ 2 :=
      fun j => mul_le_of_le_one_right (sq_nonneg _) (p4_J_le_one (mul_nonneg (sq_nonneg _) hq))
    have hsumm : Summable (fun j : ℕ => Muon.emaW β j ^ 2 * J (Muon.emaW β j ^ 2 * q)) :=
      Summable.of_nonneg_of_le hJa hle hsq
    unfold Fw Muon.sPow
    exact Summable.tsum_le_tsum hle hsumm hsq
  have hLw : ∀ q : ℝ, 0 ≤ q → Lw (Muon.emaW β) q ≤ 1 := by
    intro q hq
    have hJa : ∀ j : ℕ, 0 ≤ Muon.emaW β j * J (Muon.emaW β j ^ 2 * q) := fun j =>
      mul_nonneg (hw0 j) (p4_J_nonneg (mul_nonneg (sq_nonneg _) hq))
    have hle : ∀ j : ℕ, Muon.emaW β j * J (Muon.emaW β j ^ 2 * q) ≤ Muon.emaW β j :=
      fun j => mul_le_of_le_one_right (hw0 j) (p4_J_le_one (mul_nonneg (sq_nonneg _) hq))
    have hsumm : Summable (fun j : ℕ => Muon.emaW β j * J (Muon.emaW β j ^ 2 * q)) :=
      Summable.of_nonneg_of_le hJa hle hsum
    unfold Lw
    exact (Summable.tsum_le_tsum hle hsumm hsum).trans htot.le
  refine ⟨fun q hq => hFw q hq, fun q hq => hLw q hq, ?_⟩
  have hqL : ∀ q : ℝ, 0 ≤ q → q * Lw (Muon.emaW β) q
      = ∑' j : ℕ, q * (Muon.emaW β j * J (Muon.emaW β j ^ 2 * q)) := by
    intro q _
    unfold Lw
    rw [tsum_mul_left]
  have hsumm : ∀ q : ℝ, 0 ≤ q →
      Summable (fun j : ℕ => q * (Muon.emaW β j * J (Muon.emaW β j ^ 2 * q))) := by
    intro q hq
    refine Summable.of_nonneg_of_le
      (fun j => mul_nonneg hq (mul_nonneg (hw0 j) (p4_J_nonneg (mul_nonneg (sq_nonneg _) hq))))
      (fun j => ?_) (hsum.mul_left q)
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (hw0 j) (p4_J_le_one (mul_nonneg (sq_nonneg _) hq))) hq
  intro q1 hq1 q2 hq2 hlt
  have h1 : (0 : ℝ) ≤ q1 := hq1
  have h2 : (0 : ℝ) ≤ q2 := hq2
  show q1 * Lw (Muon.emaW β) q1 < q2 * Lw (Muon.emaW β) q2
  rw [hqL q1 h1, hqL q2 h2]
  apply Summable.tsum_lt_tsum (i := 0) ?_ ?_ (hsumm q1 h1) (hsumm q2 h2)
  · intro j
    show q1 * (Muon.emaW β j * J (Muon.emaW β j ^ 2 * q1))
      ≤ q2 * (Muon.emaW β j * J (Muon.emaW β j ^ 2 * q2))
    rcases (hw0 j).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp
    · exact p4_term_mono hpos h1 hlt.le
  · show q1 * (Muon.emaW β 0 * J (Muon.emaW β 0 ^ 2 * q1))
      < q2 * (Muon.emaW β 0 * J (Muon.emaW β 0 ^ 2 * q2))
    exact p4_term_strict hpos0 h1 hlt

/-! ### `lem:app-iso-count` -/

/-! ### Private helpers for `lem_app_iso_count` (fully proved, task P-F.1.P5) -/

private lemma p5_tsum_subtype_nat {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (g : ℕ → ℝ) :
    ∑' j : {j : ℕ | 0 < Muon.emaW β j}, g j = ∑' j : ℕ, g j :=
  tsum_subtype_eq_of_support_subset (s := {j : ℕ | 0 < Muon.emaW β j})
    (fun j _ => by
      show 0 < Muon.emaW β j
      unfold Muon.emaW
      exact mul_pos (by linarith) (pow_pos hβ0 j))

private lemma p5_rW_nat {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    rW (Muon.emaW β) q = ∑' j : ℕ, isoPhi (Muon.emaW β j ^ 2 * q) := by
  rw [p3_rW_eq hβ0.le hβ1 hq]
  exact p5_tsum_subtype_nat hβ0 hβ1 (fun j => isoPhi (Muon.emaW β j ^ 2 * q))

private lemma p5_isoRderiv_nat {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (q : ℝ) :
    isoRderiv β q = ∑' j : ℕ, Muon.emaW β j ^ 2 * isoPhiDeriv (Muon.emaW β j ^ 2 * q) := by
  unfold isoRderiv
  exact p5_tsum_subtype_nat hβ0 hβ1
    (fun j => Muon.emaW β j ^ 2 * isoPhiDeriv (Muon.emaW β j ^ 2 * q))

private lemma p5_deriv_eq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    deriv (rW (Muon.emaW β)) q = isoRderiv β q :=
  ((p3_rW_hasDerivWithinAt hβ0.le hβ1 hq.le).hasDerivAt (Ici_mem_nhds hq)).deriv

private lemma p5_w_sq (β : ℝ) (j : ℕ) (q : ℝ) :
    Muon.emaW β j ^ 2 * q = (1 - β) ^ 2 * q * β ^ (2 * j) := by
  unfold Muon.emaW
  ring

private lemma p5_X_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) (j : ℕ) :
    0 < (1 - β) ^ 2 * q * β ^ (2 * j) :=
  mul_pos (mul_pos (pow_pos (sub_pos.mpr hβ1) 2) hq) (pow_pos hβ0 _)

private lemma p5_summable_phi {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    Summable (fun j : ℕ => isoPhi (Muon.emaW β j ^ 2 * q)) :=
  Summable.of_nonneg_of_le (fun j => (p3_isoPhi_bounds (mul_nonneg (sq_nonneg _) hq)).1)
    (fun j => (p3_isoPhi_bounds (mul_nonneg (sq_nonneg _) hq)).2)
    ((p3_sq_summable hβ0.le hβ1).mul_right q)

private lemma p5_X_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (c : ℝ) :
    Summable (fun j : ℕ => c * β ^ (2 * j)) := by
  simp only [pow_mul]
  exact (summable_geometric_of_lt_one (sq_nonneg β) (by nlinarith)).mul_left c

private lemma p5_X_tsum {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (c : ℝ) :
    ∑' j : ℕ, c * β ^ (2 * j) = c * (1 - β ^ 2)⁻¹ := by
  simp only [pow_mul]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg β) (by nlinarith)]

private lemma p5_geom_block {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), β ^ (k - j) ≤ 1 / (1 - β) := by
  have h := Finset.sum_range_reflect (fun i => β ^ i) (k + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [h, one_div]
  have hs := (summable_geometric_of_lt_one hβ0.le hβ1).sum_le_tsum (Finset.range (k + 1))
    (fun i _ => pow_nonneg hβ0.le i)
  rw [tsum_geometric_of_lt_one hβ0.le hβ1] at hs
  exact hs

private lemma p5_inv_sqrt_le {x t : ℝ} (hx : 0 < x) (ht : 0 < t) (h : 1 ≤ x * t ^ 2) :
    x ^ (-(1 / 2 : ℝ)) ≤ t := by
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hs' : Real.sqrt x ≠ 0 := hs.ne'
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hu2 : (t * Real.sqrt x) ^ 2 = x * t ^ 2 := by
    rw [mul_pow, hsq]
    ring
  have h1 : 1 ≤ t * Real.sqrt x := by nlinarith [mul_nonneg ht.le hs.le]
  calc (Real.sqrt x)⁻¹ ≤ (Real.sqrt x)⁻¹ * (t * Real.sqrt x) :=
        le_mul_of_one_le_right (inv_nonneg.2 hs.le) h1
    _ = t := by field_simp

private lemma p5_block_one {β : ℝ} {x0 : ℝ} {k j : ℕ} (hjk : j ≤ k)
    (hXk : 1 ≤ x0 * β ^ (2 * k)) : 1 ≤ x0 * β ^ (2 * j) * (β ^ (k - j)) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [Nat.add_sub_cancel_left]
  have e : x0 * β ^ (2 * (j + m)) = x0 * β ^ (2 * j) * (β ^ m) ^ 2 := by ring
  rw [← e]
  exact hXk

private lemma p5_ge_one_iff {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ}
    (hx0 : 1 ≤ (1 - β) ^ 2 * q) (j : ℕ) :
    1 ≤ (1 - β) ^ 2 * q * β ^ (2 * j) ↔ (j : ℝ) ≤ isoN β q := by
  have hx : 0 < (1 - β) ^ 2 * q := lt_of_lt_of_le one_pos hx0
  have hL : 0 < Real.log (1 / β) := Real.log_pos (one_lt_one_div hβ0 hβ1)
  have hlog : Real.log (1 / β) = - Real.log β := by
    rw [one_div, Real.log_inv]
  have hY : 0 < (1 - β) ^ 2 * q * β ^ (2 * j) := mul_pos hx (pow_pos hβ0 _)
  unfold isoN
  rw [← Real.log_nonneg_iff hY, Real.log_mul hx.ne' (pow_pos hβ0 _).ne', Real.log_pow,
    le_div_iff₀ (mul_pos two_pos hL), hlog]
  push_cast
  constructor <;> intro h <;> linarith

private lemma p5_floor {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ}
    (hx0 : 1 ≤ (1 - β) ^ 2 * q) :
    ∃ k : ℕ, 1 ≤ (1 - β) ^ 2 * q * β ^ (2 * k) ∧
      (1 - β) ^ 2 * q * β ^ (2 * (k + 1)) < 1 ∧
      (k : ℝ) ≤ isoN β q ∧ isoN β q < k + 1 := by
  have hL : 0 < Real.log (1 / β) := Real.log_pos (one_lt_one_div hβ0 hβ1)
  have hn : 0 ≤ isoN β q := by
    unfold isoN
    exact div_nonneg (Real.log_nonneg hx0) (mul_nonneg two_pos.le hL.le)
  refine ⟨⌊isoN β q⌋₊, ?_, ?_, Nat.floor_le hn, Nat.lt_floor_add_one _⟩
  · exact (p5_ge_one_iff hβ0 hβ1 hx0 _).2 (Nat.floor_le hn)
  · by_contra h
    push_neg at h
    have h' := (p5_ge_one_iff hβ0 hβ1 hx0 _).1 h
    push_cast at h'
    linarith [Nat.lt_floor_add_one (isoN β q)]

private lemma p5_count_i_main {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ}
    (hx0 : 1 ≤ (1 - β) ^ 2 * q) :
    isoN β q - isoC β < rW (Muon.emaW β) q ∧ rW (Muon.emaW β) q ≤ isoN β q + isoC' β := by
  have hq : 0 < q := by
    rcases le_or_gt q 0 with h | h
    · nlinarith [sq_nonneg (1 - β)]
    · exact h
  obtain ⟨k, hXk, hXk1, hk1, hk2⟩ := p5_floor hβ0 hβ1 hx0
  have hR : rW (Muon.emaW β) q = ∑' j : ℕ, isoPhi ((1 - β) ^ 2 * q * β ^ (2 * j)) := by
    rw [p5_rW_nat hβ0 hβ1 hq.le]
    simp only [p5_w_sq]
  have hsumX : Summable (fun j : ℕ => isoPhi ((1 - β) ^ 2 * q * β ^ (2 * j))) := by
    have := p5_summable_phi hβ0 hβ1 hq.le
    simpa only [p5_w_sq] using this
  have hblock : ∀ j ∈ Finset.range (k + 1),
      1 - Real.sqrt (Real.pi / 2) * β ^ (k - j) ≤ isoPhi ((1 - β) ^ 2 * q * β ^ (2 * j)) := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h1 := p5_block_one (β := β) hjk hXk
    have hsq := p5_inv_sqrt_le (p5_X_pos hβ0 hβ1 hq j) (pow_pos hβ0 (k - j)) h1
    have hw := (lem_app_iso_weights_ii.2.2 _ (p5_X_pos hβ0 hβ1 hq j)).1
    have hm := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg (Real.pi / 2))
    linarith
  have hlow : ((k : ℝ) + 1) - isoC β ≤ ∑' j : ℕ, isoPhi ((1 - β) ^ 2 * q * β ^ (2 * j)) := by
    have hg := mul_le_mul_of_nonneg_left (p5_geom_block hβ0 hβ1 k)
      (Real.sqrt_nonneg (Real.pi / 2))
    rw [mul_one_div] at hg
    have hsplit : ∑ j ∈ Finset.range (k + 1), (1 - Real.sqrt (Real.pi / 2) * β ^ (k - j))
        = ((k : ℝ) + 1) - Real.sqrt (Real.pi / 2) * ∑ j ∈ Finset.range (k + 1), β ^ (k - j) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      simp
    have hle1 := Finset.sum_le_sum hblock
    have hle2 : ∑ j ∈ Finset.range (k + 1), isoPhi ((1 - β) ^ 2 * q * β ^ (2 * j)) ≤
        ∑' j : ℕ, isoPhi ((1 - β) ^ 2 * q * β ^ (2 * j)) :=
      Summable.sum_le_tsum (Finset.range (k + 1))
        (fun j _ => (p3_isoPhi_bounds (p5_X_pos hβ0 hβ1 hq j).le).1) hsumX
    unfold isoC
    linarith
  have hup : ∑' j : ℕ, isoPhi ((1 - β) ^ 2 * q * β ^ (2 * j)) ≤ isoN β q + isoC' β := by
    rw [← Summable.sum_add_tsum_nat_add (k + 1) hsumX]
    have h1 : ∑ j ∈ Finset.range (k + 1), isoPhi ((1 - β) ^ 2 * q * β ^ (2 * j)) ≤
        ∑ j ∈ Finset.range (k + 1), (1 : ℝ) :=
      Finset.sum_le_sum fun j _ =>
        (lem_app_iso_weights_ii.1 _ (p5_X_pos hβ0 hβ1 hq j)).trans (min_le_left _ _)
    have hterm : ∀ i : ℕ, isoPhi ((1 - β) ^ 2 * q * β ^ (2 * (i + (k + 1)))) ≤
        ((1 - β) ^ 2 * q * β ^ (2 * (k + 1))) * β ^ (2 * i) := by
      intro i
      have e : (1 - β) ^ 2 * q * β ^ (2 * (i + (k + 1))) =
          ((1 - β) ^ 2 * q * β ^ (2 * (k + 1))) * β ^ (2 * i) := by ring
      exact ((lem_app_iso_weights_ii.1 _ (p5_X_pos hβ0 hβ1 hq (i + (k + 1)))).trans
        (min_le_right _ _)).trans e.le
    have hshift : Summable (fun i : ℕ => isoPhi ((1 - β) ^ 2 * q * β ^ (2 * (i + (k + 1))))) :=
      (summable_nat_add_iff (f := fun j : ℕ => isoPhi ((1 - β) ^ 2 * q * β ^ (2 * j))) (k + 1)).mpr
        hsumX
    have h2 := Summable.tsum_le_tsum hterm hshift
      (p5_X_summable hβ0 hβ1 ((1 - β) ^ 2 * q * β ^ (2 * (k + 1))))
    rw [p5_X_tsum hβ0 hβ1] at h2
    have hC' : isoC' β = 1 + (1 - β ^ 2)⁻¹ := by
      unfold isoC'
      rw [one_div]
    have h3 : (1 - β) ^ 2 * q * β ^ (2 * (k + 1)) * (1 - β ^ 2)⁻¹ ≤ 1 * (1 - β ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hXk1.le (inv_nonneg.2 (by nlinarith))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
    push_cast at h1
    linarith
  rw [hR]
  constructor
  · linarith
  · exact hup

private lemma p5_count_i_two {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    rW (Muon.emaW β) (1 / (1 - β) ^ 2) ≤ isoC' β := by
  have h1β : (1 - β) ≠ 0 := (sub_pos.mpr hβ1).ne'
  have hq : (0 : ℝ) < 1 / (1 - β) ^ 2 := by
    have : (0 : ℝ) < (1 - β) ^ 2 := pow_pos (sub_pos.mpr hβ1) 2
    positivity
  rw [p5_rW_nat hβ0 hβ1 hq.le]
  have e1 : ∀ j : ℕ, Muon.emaW β j ^ 2 * (1 / (1 - β) ^ 2) = 1 * β ^ (2 * j) := by
    intro j
    unfold Muon.emaW
    field_simp
    ring
  simp only [e1]
  have hC' : isoC' β = 1 + (1 - β ^ 2)⁻¹ := by
    unfold isoC'
    rw [one_div]
  have hpos : (0 : ℝ) ≤ (1 - β ^ 2)⁻¹ := inv_nonneg.2 (by nlinarith)
  have hnn : ∀ j : ℕ, 0 ≤ 1 * β ^ (2 * j) := fun j => by
    rw [one_mul]
    exact pow_nonneg hβ0.le _
  have hsum1 : Summable (fun j : ℕ => isoPhi (1 * β ^ (2 * j))) :=
    Summable.of_nonneg_of_le (fun j => (p3_isoPhi_bounds (hnn j)).1)
      (fun j => (p3_isoPhi_bounds (hnn j)).2) (p5_X_summable hβ0 hβ1 1)
  have h2 := Summable.tsum_le_tsum (fun j => (p3_isoPhi_bounds (hnn j)).2) hsum1
    (p5_X_summable hβ0 hβ1 1)
  rw [p5_X_tsum hβ0 hβ1] at h2
  linarith

private lemma p5_qr_eq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    q * isoRderiv β q = ∑' j : ℕ, (1 - β) ^ 2 * q * β ^ (2 * j) *
      isoPhiDeriv ((1 - β) ^ 2 * q * β ^ (2 * j)) := by
  rw [p5_isoRderiv_nat hβ0 hβ1, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [p5_w_sq]
  unfold Muon.emaW
  ring

private lemma p5_qr_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    Summable (fun j : ℕ => (1 - β) ^ 2 * q * β ^ (2 * j) *
      isoPhiDeriv ((1 - β) ^ 2 * q * β ^ (2 * j))) :=
  Summable.of_nonneg_of_le
    (fun j => mul_nonneg (p5_X_pos hβ0 hβ1 hq j).le
      (p3_dPhi_bounds (p5_X_pos hβ0 hβ1 hq j).le).1)
    (fun j => mul_le_of_le_one_right (p5_X_pos hβ0 hβ1 hq j).le
      (p3_dPhi_bounds (p5_X_pos hβ0 hβ1 hq j).le).2)
    (p5_X_summable hβ0 hβ1 ((1 - β) ^ 2 * q))

private lemma p5_count_ii_upper {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    q * isoRderiv β q ≤ isoEplus β := by
  rw [p5_qr_eq hβ0 hβ1 hq]
  have hsumQ := p5_qr_summable hβ0 hβ1 hq
  have hC0 : 0 ≤ Real.sqrt (Real.pi / 2) / (1 - β) :=
    div_nonneg (Real.sqrt_nonneg _) (sub_nonneg.2 hβ1.le)
  have hEp : isoEplus β = Real.sqrt (Real.pi / 2) / (1 - β) + (1 - β ^ 2)⁻¹ := by
    unfold isoEplus
    rw [one_div]
  have hβ2 : (0 : ℝ) ≤ (1 - β ^ 2)⁻¹ := inv_nonneg.2 (by nlinarith)
  by_cases hx : (1 - β) ^ 2 * q < 1
  · have hterm : ∀ j : ℕ, (1 - β) ^ 2 * q * β ^ (2 * j) *
        isoPhiDeriv ((1 - β) ^ 2 * q * β ^ (2 * j)) ≤ (1 - β) ^ 2 * q * β ^ (2 * j) :=
      fun j => mul_le_of_le_one_right (p5_X_pos hβ0 hβ1 hq j).le
        (p3_dPhi_bounds (p5_X_pos hβ0 hβ1 hq j).le).2
    have h1 := Summable.tsum_le_tsum hterm hsumQ (p5_X_summable hβ0 hβ1 ((1 - β) ^ 2 * q))
    rw [p5_X_tsum hβ0 hβ1] at h1
    have h2 : (1 - β) ^ 2 * q * (1 - β ^ 2)⁻¹ ≤ 1 * (1 - β ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hx.le hβ2
    linarith
  · push_neg at hx
    obtain ⟨k, hXk, hXk1, hk1, hk2⟩ := p5_floor hβ0 hβ1 hx
    have hblock : ∀ j ∈ Finset.range (k + 1), (1 - β) ^ 2 * q * β ^ (2 * j) *
        isoPhiDeriv ((1 - β) ^ 2 * q * β ^ (2 * j)) ≤
        Real.sqrt (Real.pi / 2) * β ^ (k - j) := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h1 := p5_block_one (β := β) hjk hXk
      have hsq := p5_inv_sqrt_le (p5_X_pos hβ0 hβ1 hq j) (pow_pos hβ0 (k - j)) h1
      have hw := (lem_app_iso_weights_ii.2.2 _ (p5_X_pos hβ0 hβ1 hq j)).2
      have hm := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg (Real.pi / 2))
      exact (hw.trans (min_le_right _ _)).trans hm
    have hsplit := Summable.sum_add_tsum_nat_add (k + 1) hsumQ
    rw [← hsplit]
    have hg := mul_le_mul_of_nonneg_left (p5_geom_block hβ0 hβ1 k) (Real.sqrt_nonneg (Real.pi / 2))
    rw [mul_one_div] at hg
    have hblock_sum := Finset.sum_le_sum hblock
    rw [← Finset.mul_sum] at hblock_sum
    have hshift : Summable (fun i : ℕ => (1 - β) ^ 2 * q * β ^ (2 * (i + (k + 1))) *
        isoPhiDeriv ((1 - β) ^ 2 * q * β ^ (2 * (i + (k + 1))))) :=
      (summable_nat_add_iff (f := fun j : ℕ => (1 - β) ^ 2 * q * β ^ (2 * j) *
        isoPhiDeriv ((1 - β) ^ 2 * q * β ^ (2 * j))) (k + 1)).mpr hsumQ
    have hterm : ∀ i : ℕ, (1 - β) ^ 2 * q * β ^ (2 * (i + (k + 1))) *
        isoPhiDeriv ((1 - β) ^ 2 * q * β ^ (2 * (i + (k + 1)))) ≤
        ((1 - β) ^ 2 * q * β ^ (2 * (k + 1))) * β ^ (2 * i) := by
      intro i
      have e : (1 - β) ^ 2 * q * β ^ (2 * (i + (k + 1))) =
          ((1 - β) ^ 2 * q * β ^ (2 * (k + 1))) * β ^ (2 * i) := by ring
      have hx' := p5_X_pos hβ0 hβ1 hq (i + (k + 1))
      have hd := (p3_dPhi_bounds hx'.le).2
      calc (1 - β) ^ 2 * q * β ^ (2 * (i + (k + 1))) *
            isoPhiDeriv ((1 - β) ^ 2 * q * β ^ (2 * (i + (k + 1))))
          ≤ (1 - β) ^ 2 * q * β ^ (2 * (i + (k + 1))) :=
            mul_le_of_le_one_right hx'.le hd
        _ = _ := e
    have htail := Summable.tsum_le_tsum hterm hshift
      (p5_X_summable hβ0 hβ1 ((1 - β) ^ 2 * q * β ^ (2 * (k + 1))))
    rw [p5_X_tsum hβ0 hβ1] at htail
    have h3 : (1 - β) ^ 2 * q * β ^ (2 * (k + 1)) * (1 - β ^ 2)⁻¹ ≤ 1 * (1 - β ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hXk1.le hβ2
    rw [hEp]
    linarith

private lemma p5_count_ii_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q)
    (hx0 : 1 ≤ (1 - β) ^ 2 * q) : isoEminus β ≤ q * isoRderiv β q := by
  obtain ⟨k, hXk, hXk1, -, -⟩ := p5_floor hβ0 hβ1 hx0
  rw [p5_qr_eq hβ0 hβ1 hq]
  have hle : (1 - β) ^ 2 * q * β ^ (2 * (k + 1)) *
      isoPhiDeriv ((1 - β) ^ 2 * q * β ^ (2 * (k + 1))) ≤
      ∑' j : ℕ, (1 - β) ^ 2 * q * β ^ (2 * j) *
        isoPhiDeriv ((1 - β) ^ 2 * q * β ^ (2 * j)) :=
    Summable.le_tsum (p5_qr_summable hβ0 hβ1 hq) (k + 1) fun j _ =>
      mul_nonneg (p5_X_pos hβ0 hβ1 hq j).le (p3_dPhi_bounds (p5_X_pos hβ0 hβ1 hq j).le).1
  have hX1 : β ^ 2 ≤ (1 - β) ^ 2 * q * β ^ (2 * (k + 1)) := by
    have e : (1 - β) ^ 2 * q * β ^ (2 * (k + 1)) = β ^ 2 * ((1 - β) ^ 2 * q * β ^ (2 * k)) := by
      ring
    rw [e]
    have hb : 0 ≤ β ^ 2 := sq_nonneg β
    nlinarith
  have hanti := lem_app_iso_weights_ii.2.1 (Set.mem_Ioi.mpr (p5_X_pos hβ0 hβ1 hq (k + 1)))
    (Set.mem_Ioi.mpr one_pos) hXk1.le
  have ha := (p3_dPhi_bounds zero_le_one).1
  have hA : β ^ 2 * isoPhiDeriv 1 ≤ (1 - β) ^ 2 * q * β ^ (2 * (k + 1)) * isoPhiDeriv 1 :=
    mul_le_mul_of_nonneg_right hX1 ha
  have hB : (1 - β) ^ 2 * q * β ^ (2 * (k + 1)) * isoPhiDeriv 1 ≤
      (1 - β) ^ 2 * q * β ^ (2 * (k + 1)) *
        isoPhiDeriv ((1 - β) ^ 2 * q * β ^ (2 * (k + 1))) :=
    mul_le_mul_of_nonneg_left hanti (p5_X_pos hβ0 hβ1 hq (k + 1)).le
  unfold isoEminus
  linarith

/-- `lem:app-iso-count`(i), snapshot `cr-2026-10-23`. Part (i) of the environment below.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Participation count]\label{lem:app-iso-count}
Let $\bmom\in(0,1)$ and put
\[
\mathsf n_\bmom(q)\defeq\frac{\log\big((1-\bmom)^2q\big)}{2\log(1/\bmom)},\qquad
\mathsf c_\bmom\defeq\frac{\sqrt{\pi/2}}{1-\bmom},\qquad
\mathsf c_\bmom'\defeq1+\frac1{1-\bmom^2},
\]
\[
\mathsf e_\bmom^-\defeq\bmom^2\,\Phi'(1),\qquad
\mathsf e_\bmom^+\defeq\frac{\sqrt{\pi/2}}{1-\bmom}+\frac1{1-\bmom^2}.
\]
\begin{enumerate}[label=(\roman*)]
\item If $(1-\bmom)^2q\ge1$, then
$\mathsf n_\bmom(q)-\mathsf c_\bmom<r_\bmom(q)\le\mathsf n_\bmom(q)+\mathsf c_\bmom'$.
Moreover $r_\bmom\big((1-\bmom)^{-2}\big)\le\mathsf c'_\bmom$.
\item For every $q>0$, $0<q\,r_\bmom'(q)\le\mathsf e_\bmom^+$. If $(1-\bmom)^2q\ge1$,
then $q\,r_\bmom'(q)\ge\mathsf e_\bmom^-$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_count_i {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ q : ℝ, 1 ≤ (1 - β) ^ 2 * q →
      isoN β q - isoC β < rW (Muon.emaW β) q ∧ rW (Muon.emaW β) q ≤ isoN β q + isoC' β) ∧
    rW (Muon.emaW β) (1 / (1 - β) ^ 2) ≤ isoC' β := by
  refine ⟨fun q hq => p5_count_i_main hβ0 hβ1 hq, p5_count_i_two hβ0 hβ1⟩

/-- `lem:app-iso-count`(ii), snapshot `cr-2026-10-23`. Part (ii) of the environment below.
The derivative `r_β'` is `deriv (rW (Muon.emaW β))`; it exists for `q > 0` by
`lem:app-iso-weights`(i).
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Participation count]\label{lem:app-iso-count}
Let $\bmom\in(0,1)$ and put
\[
\mathsf n_\bmom(q)\defeq\frac{\log\big((1-\bmom)^2q\big)}{2\log(1/\bmom)},\qquad
\mathsf c_\bmom\defeq\frac{\sqrt{\pi/2}}{1-\bmom},\qquad
\mathsf c_\bmom'\defeq1+\frac1{1-\bmom^2},
\]
\[
\mathsf e_\bmom^-\defeq\bmom^2\,\Phi'(1),\qquad
\mathsf e_\bmom^+\defeq\frac{\sqrt{\pi/2}}{1-\bmom}+\frac1{1-\bmom^2}.
\]
\begin{enumerate}[label=(\roman*)]
\item If $(1-\bmom)^2q\ge1$, then
$\mathsf n_\bmom(q)-\mathsf c_\bmom<r_\bmom(q)\le\mathsf n_\bmom(q)+\mathsf c_\bmom'$.
Moreover $r_\bmom\big((1-\bmom)^{-2}\big)\le\mathsf c'_\bmom$.
\item For every $q>0$, $0<q\,r_\bmom'(q)\le\mathsf e_\bmom^+$. If $(1-\bmom)^2q\ge1$,
then $q\,r_\bmom'(q)\ge\mathsf e_\bmom^-$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_count_ii {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ q : ℝ, 0 < q →
      0 < q * deriv (rW (Muon.emaW β)) q ∧ q * deriv (rW (Muon.emaW β)) q ≤ isoEplus β) ∧
    (∀ q : ℝ, 0 < q → 1 ≤ (1 - β) ^ 2 * q →
      isoEminus β ≤ q * deriv (rW (Muon.emaW β)) q) := by
  refine ⟨fun q hq => ?_, fun q hq hx0 => ?_⟩
  · rw [p5_deriv_eq hβ0 hβ1 hq]
    exact ⟨mul_pos hq (p3_isoRderiv_pos hβ0.le hβ1 hq.le), p5_count_ii_upper hβ0 hβ1 hq⟩
  · rw [p5_deriv_eq hβ0 hβ1 hq]
    exact p5_count_ii_lower hβ0 hβ1 hq hx0

/-! ### `lem:app-iso-constants` -/

/-! ### Private helpers for `lem_app_iso_constants` (task P-F.1.P6) -/

private lemma p6_min_ge_one {a : ℝ} (h : 1 ≤ a) : min a (1 / a) = 1 / a := by
  apply min_eq_right
  have ha : 0 < a := by linarith
  rw [div_le_iff₀ ha]
  nlinarith

private lemma p6_min_lt_one {a : ℝ} (h : a < 1) (ha : 0 < a) : min a (1 / a) = a := by
  apply min_eq_left
  rw [le_div_iff₀ ha]
  nlinarith

private lemma p6_min_le_one {s : ℝ} (hs : 0 < s) : min s (1 / s) ≤ 1 := by
  rcases le_total s 1 with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans ((div_le_one hs).2 h)

private lemma p6_geom_finite {β : ℝ} (hβ0 : 0 < β) (n : ℕ) (c : ℝ) (hc : 0 < c) :
    ∑ j ∈ Finset.range (n + 1), 1 / (c * β ^ j)
      = (1 / (c * β ^ n)) * ∑ k ∈ Finset.range (n + 1), β ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hG : ∑ k ∈ Finset.range (n + 1 + 1), β ^ k
        = 1 + β * ∑ k ∈ Finset.range (n + 1), β ^ k := by
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      congr 1
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [Finset.sum_range_succ, ih, hG]
    have hβn : 0 < β ^ n := pow_pos hβ0 n
    have hβn1 : 0 < β ^ (n + 1) := pow_pos hβ0 (n + 1)
    field_simp
    ring

private lemma p6_geom_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), β ^ k ≤ 1 / (1 - β) := by
  have h1 : 0 < 1 - β := by linarith
  have key : ∀ m : ℕ, (∑ k ∈ Finset.range (m + 1), β ^ k) * (1 - β) = 1 - β ^ (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  rw [le_div_iff₀ h1, key n]
  linarith [pow_pos hβ0 (n + 1)]

private lemma p6_key {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {c : ℝ} (hc : 0 < c) :
    Summable (fun j : ℕ => min (c * β ^ j) (1 / (c * β ^ j))) ∧
      ∑' j : ℕ, min (c * β ^ j) (1 / (c * β ^ j)) ≤ (1 + β) / (1 - β) := by
  have hex : ∃ n : ℕ, c * β ^ n < 1 := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hc) hβ1
    refine ⟨n, ?_⟩
    have h2 : β ^ n * c < 1 := (lt_div_iff₀ hc).1 hn
    linarith [mul_comm c (β ^ n)]
  obtain ⟨J, hJ, hmin⟩ : ∃ J : ℕ, c * β ^ J < 1 ∧ ∀ j < J, 1 ≤ c * β ^ j :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => not_lt.mp (Nat.find_min hex hj)⟩
  have hPos : 0 < c * β ^ J := mul_pos hc (pow_pos hβ0 J)
  have hsmall : ∀ n : ℕ, c * β ^ J * β ^ n < 1 := fun n =>
    lt_of_le_of_lt (mul_le_of_le_one_right hPos.le (pow_le_one₀ hβ0.le hβ1.le)) hJ
  have htail : ∀ n : ℕ, min (c * β ^ (n + J)) (1 / (c * β ^ (n + J))) = c * β ^ J * β ^ n := by
    intro n
    have hx : c * β ^ (n + J) = c * β ^ J * β ^ n := by ring
    rw [hx]
    exact p6_min_lt_one (hsmall n) (mul_pos hPos (pow_pos hβ0 n))
  have hgeom : Summable (fun n : ℕ => c * β ^ J * β ^ n) :=
    (summable_geometric_of_lt_one hβ0.le hβ1).mul_left _
  have hsum_tail : Summable (fun n : ℕ => min (c * β ^ (n + J)) (1 / (c * β ^ (n + J)))) := by
    simp only [htail]
    exact hgeom
  have hsumm : Summable (fun j : ℕ => min (c * β ^ j) (1 / (c * β ^ j))) :=
    (summable_nat_add_iff J).1 hsum_tail
  refine ⟨hsumm, ?_⟩
  have hsplit : ∑ j ∈ Finset.range J, min (c * β ^ j) (1 / (c * β ^ j))
      + ∑' n : ℕ, min (c * β ^ (n + J)) (1 / (c * β ^ (n + J)))
      = ∑' j : ℕ, min (c * β ^ j) (1 / (c * β ^ j)) :=
    Summable.sum_add_tsum_nat_add J hsumm
  have htail_sum : ∑' n : ℕ, min (c * β ^ (n + J)) (1 / (c * β ^ (n + J)))
      = c * β ^ J / (1 - β) := by
    simp only [htail]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0.le hβ1, div_eq_mul_inv]
  rw [← hsplit, htail_sum]
  have h1 : 0 < 1 - β := by linarith
  cases J with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, mul_one]
    have hc1 : c < 1 := by simpa using hJ
    refine div_le_div_of_nonneg_right ?_ h1.le
    linarith
  | succ m =>
    have ha1 : 1 ≤ c * β ^ m := hmin m (Nat.lt_succ_self m)
    have ha0 : 0 < c * β ^ m := mul_pos hc (pow_pos hβ0 m)
    have hβa : c * β ^ (m + 1) = (c * β ^ m) * β := by ring
    have hlt : (c * β ^ m) * β < 1 := by rw [← hβa]; exact hJ
    have hfin : ∑ j ∈ Finset.range (m + 1), min (c * β ^ j) (1 / (c * β ^ j))
        = ∑ j ∈ Finset.range (m + 1), 1 / (c * β ^ j) :=
      Finset.sum_congr rfl (fun j hj => p6_min_ge_one (hmin j (Finset.mem_range.mp hj)))
    rw [hfin, p6_geom_finite hβ0 m c hc]
    have hG := mul_le_mul_of_nonneg_left (p6_geom_le hβ0 hβ1 m)
      (div_nonneg zero_le_one ha0.le)
    have hkey : (1 / (c * β ^ m)) * (1 / (1 - β)) + c * β ^ (m + 1) / (1 - β)
        ≤ (1 + β) / (1 - β) := by
      rw [hβa]
      have hpoly : 1 / (c * β ^ m) + (c * β ^ m) * β ≤ 1 + β := by
        rw [div_add' _ _ _ ha0.ne', div_le_iff₀ ha0]
        nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hlt.le)]
      calc (1 / (c * β ^ m)) * (1 / (1 - β)) + (c * β ^ m) * β / (1 - β)
          = (1 / (c * β ^ m) + (c * β ^ m) * β) / (1 - β) := by ring
        _ ≤ (1 + β) / (1 - β) := div_le_div_of_nonneg_right hpoly h1.le
    linarith

private lemma p6_lam_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ isoLambda 0 z := by
  have h0 : isoLambda 0 0 = 0 := by simp [isoLambda]
  have := (lem_app_iso_weights_iv (le_refl (0:ℝ)) zero_lt_one).2.2.2.1
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hz) hz
  linarith

private lemma p6_phi_bound {z : ℝ} (hz : 0 < z) :
    |isoLambda 0 z - Real.sqrt (2 * Real.pi) * isoPhi z|
      ≤ Real.pi * min (Real.sqrt z) (1 / Real.sqrt z) := by
  obtain ⟨hPhi0, hPhiLe⟩ := p3_isoPhi_bounds hz.le
  have hLam2 : isoLambda 0 z ≤ 2 * Real.sqrt z :=
    (lem_app_iso_weights_iv (le_refl (0:ℝ)) zero_lt_one).2.1 z hz.le
  have hLam0 := p6_lam_nonneg hz.le
  have hs : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz
  have hss : Real.sqrt z * Real.sqrt z = z := Real.mul_self_sqrt hz.le
  have hpi2 : (2:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hsq2 : Real.sqrt (2 * Real.pi) ≤ Real.pi :=
    Real.sqrt_le_iff.mpr ⟨Real.pi_pos.le, by nlinarith [Real.pi_pos]⟩
  have hsq2nn : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have hid : isoLambda 0 z - Real.sqrt (2 * Real.pi) * isoPhi z
      = Real.sqrt (2 * Real.pi) * (1 - isoPhi z) - (Real.sqrt (2 * Real.pi) - isoLambda 0 z) := by
    ring
  rcases le_total z 1 with hz1 | hz1
  · have hmin : min (Real.sqrt z) (1 / Real.sqrt z) = Real.sqrt z := by
      apply min_eq_left
      rw [le_div_iff₀ hs]
      nlinarith
    rw [hmin]
    have hs1 : Real.sqrt z ≤ 1 := by nlinarith
    have hzs : z ≤ Real.sqrt z := by nlinarith
    have hB1 : Real.sqrt (2 * Real.pi) * isoPhi z ≤ Real.pi * Real.sqrt z :=
      (mul_le_mul_of_nonneg_right hsq2 hPhi0).trans
        (mul_le_mul_of_nonneg_left (hPhiLe.trans hzs) Real.pi_pos.le)
    have hA : isoLambda 0 z ≤ Real.pi * Real.sqrt z :=
      le_trans hLam2 (mul_le_mul_of_nonneg_right hpi2 hs.le)
    have hB0 : 0 ≤ Real.sqrt (2 * Real.pi) * isoPhi z := mul_nonneg hsq2nn hPhi0
    rw [abs_sub_le_iff]
    constructor <;> linarith
  · have hmin : min (Real.sqrt z) (1 / Real.sqrt z) = 1 / Real.sqrt z := by
      apply min_eq_right
      rw [div_le_iff₀ hs]
      nlinarith
    rw [hmin]
    have hpow : z ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt z := by
      rw [Real.rpow_neg hz.le, ← Real.sqrt_eq_rpow, one_div]
    have hT := (lem_app_iso_weights_iv (le_refl (0:ℝ)) zero_lt_one).2.2.1 z hz
    rw [hpow] at hT
    have hW := (lem_app_iso_weights_ii.2.2 z hz).1
    rw [hpow] at hW
    have hpp : Real.sqrt (2 * Real.pi) * Real.sqrt (Real.pi / 2) = Real.pi := by
      rw [← Real.sqrt_mul (show (0:ℝ) ≤ 2 * Real.pi by positivity)]
      rw [show 2 * Real.pi * (Real.pi / 2) = Real.pi ^ 2 by ring]
      exact Real.sqrt_sq Real.pi_pos.le
    have hPhi1 : isoPhi z ≤ 1 := (lem_app_iso_weights_ii.1 z hz).trans (min_le_left _ _)
    have hA0 : 0 ≤ Real.sqrt (2 * Real.pi) * (1 - isoPhi z) :=
      mul_nonneg hsq2nn (by linarith)
    have hinv : 0 ≤ 1 / Real.sqrt z := by positivity
    have hA1 : Real.sqrt (2 * Real.pi) * (1 - isoPhi z) ≤ Real.pi * (1 / Real.sqrt z) := by
      calc Real.sqrt (2 * Real.pi) * (1 - isoPhi z)
          ≤ Real.sqrt (2 * Real.pi) * (Real.sqrt (Real.pi / 2) * (1 / Real.sqrt z)) :=
            mul_le_mul_of_nonneg_left hW hsq2nn
        _ = Real.pi * (1 / Real.sqrt z) := by rw [← mul_assoc, hpp]
    have hB2 : Real.sqrt (2 * Real.pi) - isoLambda 0 z ≤ Real.pi * (1 / Real.sqrt z) :=
      hT.2.trans (mul_le_mul_of_nonneg_right hpi2 hinv)
    rw [hid, abs_sub_le_iff]
    constructor <;> linarith [hT.1]

private lemma p6_y_le {y : ℝ} (hy : 0 < y) : y * J (y ^ 2) ≤ min y (1 / y) := by
  have hJ := (lem_app_iso_weights_iii).1 (y ^ 2) (pow_pos hy 2)
  have hy0 : y ≠ 0 := hy.ne'
  apply le_min
  · exact mul_le_of_le_one_right hy.le (hJ.trans (min_le_left _ _))
  · calc y * J (y ^ 2) ≤ y * (1 / y ^ 2) :=
          mul_le_mul_of_nonneg_left (hJ.trans (min_le_right _ _)) hy.le
      _ = 1 / y := by
          rw [mul_one_div, div_eq_div_iff (pow_ne_zero 2 hy0) hy0]
          ring

private lemma p6_term_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) (j : ℕ) :
    Real.sqrt q * (Muon.emaW β j * J (Muon.emaW β j ^ 2 * q)) ≤
      min ((1 - β) * Real.sqrt q * β ^ j) (1 / ((1 - β) * Real.sqrt q * β ^ j)) := by
  have hw : 0 < Muon.emaW β j := by
    unfold Muon.emaW
    exact mul_pos (by linarith) (pow_pos hβ0 j)
  have hy : 0 < Real.sqrt q * Muon.emaW β j := mul_pos (Real.sqrt_pos.mpr hq) hw
  have hsq : Muon.emaW β j ^ 2 * q = (Real.sqrt q * Muon.emaW β j) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hq.le]
    ring
  have hc : (1 - β) * Real.sqrt q * β ^ j = Real.sqrt q * Muon.emaW β j := by
    unfold Muon.emaW
    ring
  have hL : Real.sqrt q * (Muon.emaW β j * J (Muon.emaW β j ^ 2 * q))
      = (Real.sqrt q * Muon.emaW β j) * J ((Real.sqrt q * Muon.emaW β j) ^ 2) := by
    rw [← hsq]
    ring
  rw [hL, hc]
  exact p6_y_le hy

private lemma p6_sum_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    Real.sqrt q * Lw (Muon.emaW β) q
      ≤ ∑' j : ℕ, min ((1 - β) * Real.sqrt q * β ^ j) (1 / ((1 - β) * Real.sqrt q * β ^ j)) := by
  have hc : 0 < (1 - β) * Real.sqrt q := mul_pos (by linarith) (Real.sqrt_pos.mpr hq)
  have hsum := (p6_key hβ0 hβ1 hc).1
  have hsumL : Summable (fun j : ℕ => Real.sqrt q * (Muon.emaW β j * J (Muon.emaW β j ^ 2 * q))) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
      ((p3_emaW_summable hβ0.le hβ1).mul_left (Real.sqrt q))
    · exact mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (p3_emaW_nonneg hβ0.le hβ1 j)
          (p4_J_nonneg (mul_nonneg (sq_nonneg _) hq.le)))
    · exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (p3_emaW_nonneg hβ0.le hβ1 j)
          (p4_J_le_one (mul_nonneg (sq_nonneg _) hq.le)))
        (Real.sqrt_nonneg _)
  have hLHS : Real.sqrt q * Lw (Muon.emaW β) q
      = ∑' j : ℕ, Real.sqrt q * (Muon.emaW β j * J (Muon.emaW β j ^ 2 * q)) := by
    unfold Lw
    rw [tsum_mul_left]
  rw [hLHS]
  exact Summable.tsum_le_tsum (fun j => p6_term_le hβ0 hβ1 hq j) hsumL hsum

private lemma p6_gsup_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    BddAbove ((fun q : ℝ => Real.sqrt q * Lw (Muon.emaW β) q) '' Ioi 0) ∧
      isoGSup β ≤ (1 + β) / (1 - β) := by
  have hb : ∀ q : ℝ, 0 < q → Real.sqrt q * Lw (Muon.emaW β) q ≤ (1 + β) / (1 - β) := by
    intro q hq
    have hc : 0 < (1 - β) * Real.sqrt q := mul_pos (by linarith) (Real.sqrt_pos.mpr hq)
    exact (p6_sum_le hβ0 hβ1 hq).trans (p6_key hβ0 hβ1 hc).2
  refine ⟨⟨(1 + β) / (1 - β), ?_⟩, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact hb q hq
  · unfold isoGSup
    apply csSup_le
    · exact ⟨_, Set.mem_image_of_mem _ (Set.mem_Ioi.mpr one_pos)⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact hb q hq

private lemma p6_gprime_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    |isoLambda β q - Real.sqrt (2 * Real.pi) * rW (Muon.emaW β) q|
      ≤ Real.pi * ((1 + β) / (1 - β)) := by
  have hΛ : isoLambda β q = ∑' j : ℕ, isoLambda 0 (Muon.emaW β j ^ 2 * q) := by
    rw [(lem_app_iso_weights_iv hβ0.le hβ1).1 q hq.le]
    exact p5_tsum_subtype_nat hβ0 hβ1 (fun j => isoLambda 0 (Muon.emaW β j ^ 2 * q))
  have hr : rW (Muon.emaW β) q = ∑' j : ℕ, isoPhi (Muon.emaW β j ^ 2 * q) :=
    p5_rW_nat hβ0 hβ1 hq.le
  have hw : ∀ j : ℕ, 0 < Muon.emaW β j := fun j => by
    unfold Muon.emaW
    exact mul_pos (by linarith) (pow_pos hβ0 j)
  have hz : ∀ j : ℕ, 0 < Muon.emaW β j ^ 2 * q := fun j => mul_pos (pow_pos (hw j) 2) hq
  have hsqrt' : ∀ j : ℕ, Real.sqrt (Muon.emaW β j ^ 2 * q) = Muon.emaW β j * Real.sqrt q := by
    intro j
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hw j).le]
  have hsqrt : ∀ j : ℕ, Real.sqrt (Muon.emaW β j ^ 2 * q)
      = (1 - β) * Real.sqrt q * β ^ j := by
    intro j
    rw [hsqrt' j]
    unfold Muon.emaW
    ring
  have hSΛ : Summable (fun j : ℕ => isoLambda 0 (Muon.emaW β j ^ 2 * q)) := by
    refine Summable.of_nonneg_of_le (fun j => p6_lam_nonneg (hz j).le) (fun j => ?_)
      ((p3_emaW_summable hβ0.le hβ1).mul_left (2 * Real.sqrt q))
    calc isoLambda 0 (Muon.emaW β j ^ 2 * q)
        ≤ 2 * Real.sqrt (Muon.emaW β j ^ 2 * q) :=
          (lem_app_iso_weights_iv (le_refl (0:ℝ)) zero_lt_one).2.1 _ (hz j).le
      _ = 2 * Real.sqrt q * Muon.emaW β j := by rw [hsqrt' j]; ring
  have hSP : Summable (fun j : ℕ => Real.sqrt (2 * Real.pi) * isoPhi (Muon.emaW β j ^ 2 * q)) := by
    refine Summable.mul_left _ (Summable.of_nonneg_of_le (fun j => (p3_isoPhi_bounds (hz j).le).1)
      (fun j => (p3_isoPhi_bounds (hz j).le).2) ((p3_sq_summable hβ0.le hβ1).mul_right q))
  have hcomb : ∑' j : ℕ, isoLambda 0 (Muon.emaW β j ^ 2 * q)
      - Real.sqrt (2 * Real.pi) * ∑' j : ℕ, isoPhi (Muon.emaW β j ^ 2 * q)
      = ∑' j : ℕ, (isoLambda 0 (Muon.emaW β j ^ 2 * q)
          - Real.sqrt (2 * Real.pi) * isoPhi (Muon.emaW β j ^ 2 * q)) := by
    rw [Summable.tsum_sub hSΛ hSP, tsum_mul_left]
  have hc : 0 < (1 - β) * Real.sqrt q := mul_pos (by linarith) (Real.sqrt_pos.mpr hq)
  have hsumt := (p6_key hβ0 hβ1 hc).1
  have hφ : ∀ j : ℕ, |isoLambda 0 (Muon.emaW β j ^ 2 * q)
      - Real.sqrt (2 * Real.pi) * isoPhi (Muon.emaW β j ^ 2 * q)|
        ≤ Real.pi * min ((1 - β) * Real.sqrt q * β ^ j) (1 / ((1 - β) * Real.sqrt q * β ^ j)) := by
    intro j
    have h := p6_phi_bound (hz j)
    rw [hsqrt j] at h
    exact h
  have hnorm : Summable (fun j : ℕ => ‖isoLambda 0 (Muon.emaW β j ^ 2 * q)
      - Real.sqrt (2 * Real.pi) * isoPhi (Muon.emaW β j ^ 2 * q)‖) := by
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) (hsumt.mul_left Real.pi)
    rw [Real.norm_eq_abs]
    exact hφ j
  rw [hΛ, hr, hcomb]
  have hA := norm_tsum_le_tsum_norm hnorm
  have hB : ∑' j : ℕ, ‖isoLambda 0 (Muon.emaW β j ^ 2 * q)
      - Real.sqrt (2 * Real.pi) * isoPhi (Muon.emaW β j ^ 2 * q)‖
        ≤ ∑' j : ℕ, Real.pi * min ((1 - β) * Real.sqrt q * β ^ j)
          (1 / ((1 - β) * Real.sqrt q * β ^ j)) :=
    Summable.tsum_le_tsum (fun j => by rw [Real.norm_eq_abs]; exact hφ j) hnorm
      (hsumt.mul_left Real.pi)
  rw [tsum_mul_left] at hB
  have hK := mul_le_mul_of_nonneg_left (p6_key hβ0 hβ1 hc).2 Real.pi_pos.le
  rw [Real.norm_eq_abs] at hA
  linarith

/-- `lem:app-iso-constants`(i), snapshot `cr-2026-10-23`. Part (i) of the environment below.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Two constants]\label{lem:app-iso-constants}
Let $\bmom\in(0,1)$.
\begin{enumerate}[label=(\roman*)]
\item If $y_0>0$ and $y_j=y_0\bmom^j$, then $\sum_{j\ge0}\min(y_j,1/y_j)<2/(1-\bmom)$.
\item $\displaystyle\mathsf g_\bmom\defeq\sup_{q>0}\sqrt q\,\Lw(q)<\frac2{1-\bmom}$.
\item $\displaystyle\mathsf g'_\bmom\defeq\sup_{q>0}\Big|\Lambda_\bmom(q)-\sqrt{2\pi}\,r_\bmom(q)\Big|<\frac{2\pi}{1-\bmom}$.
\end{enumerate}
At $\bmom=0$, $\sqrt q\,\Jfun(q)\le1$ and $\abs{\Lambda_0(q)-\sqrt{2\pi}\,\Phi(q)}\le\pi$ for every $q>0$.
\end{lemma}
```
-/
theorem lem_app_iso_constants_i {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ y0 : ℝ, 0 < y0 → ∑' j : ℕ, min (y0 * β ^ j) (1 / (y0 * β ^ j)) < 2 / (1 - β) := by
  intro y0 hy0
  exact (p6_key hβ0 hβ1 hy0).2.trans_lt (div_lt_div_of_pos_right (by linarith) (by linarith))

/-- `lem:app-iso-constants`(ii), snapshot `cr-2026-10-23`. Part (ii) of the environment below.
The supremum is `isoGSup β`; `BddAbove` is part of the claim, so that the strict bound is on a
supremum of a bounded set (card §6.9; `open_questions`).
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Two constants]\label{lem:app-iso-constants}
Let $\bmom\in(0,1)$.
\begin{enumerate}[label=(\roman*)]
\item If $y_0>0$ and $y_j=y_0\bmom^j$, then $\sum_{j\ge0}\min(y_j,1/y_j)<2/(1-\bmom)$.
\item $\displaystyle\mathsf g_\bmom\defeq\sup_{q>0}\sqrt q\,\Lw(q)<\frac2{1-\bmom}$.
\item $\displaystyle\mathsf g'_\bmom\defeq\sup_{q>0}\Big|\Lambda_\bmom(q)-\sqrt{2\pi}\,r_\bmom(q)\Big|<\frac{2\pi}{1-\bmom}$.
\end{enumerate}
At $\bmom=0$, $\sqrt q\,\Jfun(q)\le1$ and $\abs{\Lambda_0(q)-\sqrt{2\pi}\,\Phi(q)}\le\pi$ for every $q>0$.
\end{lemma}
```
-/
theorem lem_app_iso_constants_ii {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    BddAbove ((fun q : ℝ => Real.sqrt q * Lw (Muon.emaW β) q) '' Ioi 0) ∧
    isoGSup β < 2 / (1 - β) := by
  exact ⟨(p6_gsup_le hβ0 hβ1).1,
    (p6_gsup_le hβ0 hβ1).2.trans_lt (div_lt_div_of_pos_right (by linarith) (by linarith))⟩

/-- `lem:app-iso-constants`(iii), snapshot `cr-2026-10-23`. Part (iii) of the environment below.
The supremum is `isoGPrimeSup β`; `BddAbove` is part of the claim (card §6.9; `open_questions`).
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Two constants]\label{lem:app-iso-constants}
Let $\bmom\in(0,1)$.
\begin{enumerate}[label=(\roman*)]
\item If $y_0>0$ and $y_j=y_0\bmom^j$, then $\sum_{j\ge0}\min(y_j,1/y_j)<2/(1-\bmom)$.
\item $\displaystyle\mathsf g_\bmom\defeq\sup_{q>0}\sqrt q\,\Lw(q)<\frac2{1-\bmom}$.
\item $\displaystyle\mathsf g'_\bmom\defeq\sup_{q>0}\Big|\Lambda_\bmom(q)-\sqrt{2\pi}\,r_\bmom(q)\Big|<\frac{2\pi}{1-\bmom}$.
\end{enumerate}
At $\bmom=0$, $\sqrt q\,\Jfun(q)\le1$ and $\abs{\Lambda_0(q)-\sqrt{2\pi}\,\Phi(q)}\le\pi$ for every $q>0$.
\end{lemma}
```
-/
theorem lem_app_iso_constants_iii {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    BddAbove ((fun q : ℝ => |isoLambda β q - Real.sqrt (2 * Real.pi) * rW (Muon.emaW β) q|) ''
      Ioi 0) ∧
    isoGPrimeSup β < 2 * Real.pi / (1 - β) := by
  have hK : ∀ q : ℝ, 0 < q → |isoLambda β q - Real.sqrt (2 * Real.pi) * rW (Muon.emaW β) q|
      ≤ Real.pi * ((1 + β) / (1 - β)) := fun q hq => p6_gprime_le hβ0 hβ1 hq
  have h1 : (0:ℝ) < 1 - β := by linarith
  have hlt : Real.pi * ((1 + β) / (1 - β)) < 2 * Real.pi / (1 - β) := by
    rw [← mul_div_assoc, div_lt_div_iff_of_pos_right h1]
    nlinarith [mul_pos Real.pi_pos h1]
  refine ⟨⟨Real.pi * ((1 + β) / (1 - β)), ?_⟩, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact hK q hq
  · unfold isoGPrimeSup
    refine lt_of_le_of_lt (csSup_le ⟨_, Set.mem_image_of_mem _ (Set.mem_Ioi.mpr one_pos)⟩ ?_) hlt
    rintro _ ⟨q, hq, rfl⟩
    exact hK q hq

/-- `lem:app-iso-constants`, the closing sentence "At $\bmom=0$, …" of the environment below, as
part (iv) of the declaration of record. It has no `β` hypothesis: it is the `β = 0` case.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Two constants]\label{lem:app-iso-constants}
Let $\bmom\in(0,1)$.
\begin{enumerate}[label=(\roman*)]
\item If $y_0>0$ and $y_j=y_0\bmom^j$, then $\sum_{j\ge0}\min(y_j,1/y_j)<2/(1-\bmom)$.
\item $\displaystyle\mathsf g_\bmom\defeq\sup_{q>0}\sqrt q\,\Lw(q)<\frac2{1-\bmom}$.
\item $\displaystyle\mathsf g'_\bmom\defeq\sup_{q>0}\Big|\Lambda_\bmom(q)-\sqrt{2\pi}\,r_\bmom(q)\Big|<\frac{2\pi}{1-\bmom}$.
\end{enumerate}
At $\bmom=0$, $\sqrt q\,\Jfun(q)\le1$ and $\abs{\Lambda_0(q)-\sqrt{2\pi}\,\Phi(q)}\le\pi$ for every $q>0$.
\end{lemma}
```
-/
theorem lem_app_iso_constants_iv :
    ∀ q : ℝ, 0 < q →
      Real.sqrt q * J q ≤ 1 ∧ |isoLambda 0 q - Real.sqrt (2 * Real.pi) * isoPhi q| ≤ Real.pi := by
  intro q hq
  refine ⟨?_, ?_⟩
  · have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
    have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
    have hJ := (lem_app_iso_weights_iii).1 q hq
    have h1 : Real.sqrt q * J q ≤ Real.sqrt q :=
      mul_le_of_le_one_right hs.le (hJ.trans (min_le_left _ _))
    have h2 : Real.sqrt q * J q ≤ 1 / Real.sqrt q := by
      calc Real.sqrt q * J q ≤ Real.sqrt q * (1 / q) :=
            mul_le_mul_of_nonneg_left (hJ.trans (min_le_right _ _)) hs.le
        _ = 1 / Real.sqrt q := by
            rw [mul_one_div, div_eq_div_iff hq.ne' hs.ne', one_mul]
            exact hsq
    exact (le_min h1 h2).trans (p6_min_le_one hs)
  · exact (p6_phi_bound hq).trans
      (mul_le_of_le_one_right Real.pi_pos.le (p6_min_le_one (Real.sqrt_pos.mpr hq)))

/-! ### Private helpers for `lem_app_iso_slope` (task P-F.1.P7) -/


private lemma p7_l_eq (v : ℝ) :
    Real.exp v / (1 + Real.exp v) ^ 2 = 1 / (2 + 2 * Real.cosh v) := by
  have h0 : 0 < Real.exp v := Real.exp_pos v
  rw [Real.cosh_eq, Real.exp_neg]
  field_simp
  ring

private lemma p7_l_le_quarter (v : ℝ) : Real.exp v / (1 + Real.exp v) ^ 2 ≤ 1 / 4 := by
  rw [p7_l_eq]
  have := Real.one_le_cosh v
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

private lemma p7_l_nonneg (v : ℝ) : 0 ≤ Real.exp v / (1 + Real.exp v) ^ 2 :=
  div_nonneg (Real.exp_pos v).le (sq_nonneg _)

private lemma p7_l_anti {u v : ℝ} (h : |u| ≤ |v|) :
    Real.exp v / (1 + Real.exp v) ^ 2 ≤ Real.exp u / (1 + Real.exp u) ^ 2 := by
  rw [p7_l_eq, p7_l_eq]
  have := Real.cosh_le_cosh.mpr h
  have h1 := Real.one_le_cosh u
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

private lemma p7_sigma_deriv (v : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp v / (1 + Real.exp v))
      (Real.exp v / (1 + Real.exp v) ^ 2) v := by
  have h0 : 0 < 1 + Real.exp v := by linarith [Real.exp_pos v]
  have := (Real.hasDerivAt_exp v).div ((Real.hasDerivAt_exp v).const_add 1) h0.ne'
  convert this using 1
  field_simp
  ring

private lemma p7_K {a b v : ℝ} (hab : a < b) (hv : ∀ ξ ∈ Ioo a b, |ξ| ≤ |v|) :
    Real.exp v / (1 + Real.exp v) ^ 2 ≤
      (Real.exp b / (1 + Real.exp b) - Real.exp a / (1 + Real.exp a)) / (b - a) := by
  obtain ⟨ξ, hξ, hξ'⟩ := exists_hasDerivAt_eq_slope
    (fun v : ℝ => Real.exp v / (1 + Real.exp v))
    (fun v : ℝ => Real.exp v / (1 + Real.exp v) ^ 2) hab
    (fun x _ => (p7_sigma_deriv x).continuousAt.continuousWithinAt)
    (fun x _ => p7_sigma_deriv x)
  rw [← hξ']
  exact p7_l_anti (hv ξ hξ)

private lemma p7_sigma_bounds (v : ℝ) :
    0 ≤ Real.exp v / (1 + Real.exp v) ∧ Real.exp v / (1 + Real.exp v) ≤ 1 := by
  have h0 := Real.exp_pos v
  exact ⟨by positivity, by rw [div_le_one (by linarith)]; linarith⟩


private lemma p7_left_abs {l σ : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hK : ∀ a b v : ℝ, a < b → (∀ ξ ∈ Ioo a b, |ξ| ≤ |v|) → l v ≤ (σ b - σ a) / (b - a))
    (hσ : ∀ v, 0 ≤ σ v) {a : ℝ} (ha : a ≤ 0) (N : ℕ) :
    ∑ j ∈ Finset.range N, l (a - (j + 1) * h) ≤ σ a / h := by
  have key : ∀ j : ℕ, l (a - (j + 1) * h) ≤ (σ (a - j * h) - σ (a - (j + 1) * h)) / h := by
    intro j
    have hlt : a - (j + 1) * h < a - j * h := by nlinarith
    have := hK (a - (j + 1) * h) (a - j * h) (a - (j + 1) * h) hlt (fun ξ hξ => by
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have h1 : a - (j + 1) * h < ξ := hξ.1
      have h2 : ξ < a - j * h := hξ.2
      have h3 : ξ < 0 := by nlinarith
      rw [abs_of_neg h3, abs_of_neg (by nlinarith)]
      linarith)
    have e : a - j * h - (a - (j + 1) * h) = h := by ring
    rwa [e] at this
  have tel := Finset.sum_range_sub' (fun j : ℕ => σ (a - j * h)) N
  push_cast at tel
  calc _ ≤ ∑ j ∈ Finset.range N, (σ (a - j * h) - σ (a - (j + 1) * h)) / h :=
        Finset.sum_le_sum (fun j _ => key j)
    _ = (σ a - σ (a - N * h)) / h := by
        rw [← Finset.sum_div, tel]
        simp
    _ ≤ σ a / h := div_le_div_of_nonneg_right (by linarith [hσ (a - N * h)]) hh.le

private lemma p7_direct {l σ : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hK : ∀ a b v : ℝ, a < b → (∀ ξ ∈ Ioo a b, |ξ| ≤ |v|) → l v ≤ (σ b - σ a) / (b - a))
    (hσ : ∀ v, 0 ≤ σ v) (hl0 : ∀ v, 0 ≤ l v) (hl4 : ∀ v, l v ≤ 1 / 4)
    {c : ℝ} (hc : c < h) (N : ℕ) :
    ∑ j ∈ Finset.range N, l (c - j * h) ≤ 1 / 4 + σ c / h := by
  have hσc : 0 ≤ σ c / h := div_nonneg (hσ c) hh.le
  rcases le_or_gt c 0 with hc0 | hc0
  · -- everything on the increasing side
    have hs : ∑ j ∈ Finset.range (N + 1), l (c - j * h) ≤ 1 / 4 + σ c / h := by
      rw [Finset.sum_range_succ']
      have := p7_left_abs hh hK hσ hc0 N
      have e : ∀ j : ℕ, l (c - ((j + 1 : ℕ) : ℝ) * h) = l (c - (j + 1) * h) := by
        intro j; push_cast; rfl
      simp only [e]
      have h0 : l (c - ((0 : ℕ) : ℝ) * h) ≤ 1 / 4 := hl4 _
      linarith
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.le_succ N)) (fun j _ _ => hl0 _)) hs
  · -- c in (0,h): two straddling points
    have hs : ∑ j ∈ Finset.range (N + 2), l (c - j * h) ≤ 1 / 4 + σ c / h := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have ha : c - h ≤ 0 := by linarith
      have hL := p7_left_abs hh hK hσ ha N
      have e : ∀ j : ℕ, l (c - ((j + 1 + 1 : ℕ) : ℝ) * h) = l ((c - h) - (j + 1) * h) := by
        intro j; push_cast; congr 1; ring
      simp only [e]
      have e1 : l (c - ((0 + 1 : ℕ) : ℝ) * h) = l (c - h) := by simp
      have e0 : l (c - ((0 : ℕ) : ℝ) * h) = l c := by simp
      rw [e1, e0]
      -- middle comparison
      have hlt : c - h < c := by linarith
      have e2 : c - (c - h) = h := by ring
      have hmid : min (l c) (l (c - h)) ≤ (σ c - σ (c - h)) / h := by
        rcases le_total |c| |c - h| with hle | hle
        · have := hK (c - h) c (c - h) hlt (fun ξ hξ => by
            have h1 : c - h < ξ := hξ.1
            have h2 : ξ < c := hξ.2
            rw [abs_le]; constructor
            · linarith [le_abs_self (c - h), neg_abs_le (c - h), le_abs_self c]
            · linarith [le_abs_self c])
          rw [e2] at this
          exact (min_le_right _ _).trans this
        · have := hK (c - h) c c hlt (fun ξ hξ => by
            have h1 : c - h < ξ := hξ.1
            have h2 : ξ < c := hξ.2
            rw [abs_le]; constructor
            · linarith [neg_abs_le (c - h), le_abs_self (c - h)]
            · linarith [le_abs_self c])
          rw [e2] at this
          exact (min_le_left _ _).trans this
      have hq : l c + l (c - h) ≤ 1 / 4 + min (l c) (l (c - h)) := by
        rcases le_total (l c) (l (c - h)) with hh' | hh'
        · rw [min_eq_left hh']; linarith [hl4 (c - h)]
        · rw [min_eq_right hh']; linarith [hl4 c]
      have hsum : (σ c - σ (c - h)) / h + σ (c - h) / h = σ c / h := by ring
      linarith
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun j _ _ => hl0 _)) hs

private lemma p7_lattice {l σ : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hK : ∀ a b v : ℝ, a < b → (∀ ξ ∈ Ioo a b, |ξ| ≤ |v|) → l v ≤ (σ b - σ a) / (b - a))
    (hσ : ∀ v, 0 ≤ σ v) (hl0 : ∀ v, 0 ≤ l v) (hl4 : ∀ v, l v ≤ 1 / 4)
    (k : ℕ) : ∀ c : ℝ, c < (k + 1) * h → ∀ N : ℕ,
    ∑ j ∈ Finset.range N, l (c - j * h) ≤ 1 / 4 + σ c / h := by
  induction k with
  | zero => intro c hc N; exact p7_direct hh hK hσ hl0 hl4 (by simpa using hc) N
  | succ k ih =>
    intro c hc N
    rcases lt_or_ge c h with hch | hch
    · exact p7_direct hh hK hσ hl0 hl4 hch N
    · have hlt : c - h < c := by linarith
      have h1 := hK (c - h) c c hlt (fun ξ hξ => by
        have h1 : c - h < ξ := hξ.1
        have h2 : ξ < c := hξ.2
        rw [abs_of_nonneg (by linarith : 0 ≤ c), abs_le]; constructor <;> linarith)
      have e2 : c - (c - h) = h := by ring
      rw [e2] at h1
      have h2 := ih (c - h) (by push_cast at hc; linarith)
      cases N with
      | zero => simp; exact add_nonneg (by norm_num) (div_nonneg (hσ c) hh.le)
      | succ N =>
        rw [Finset.sum_range_succ']
        have e : ∀ j : ℕ, l (c - ((j + 1 : ℕ) : ℝ) * h) = l ((c - h) - j * h) := by
          intro j; push_cast; congr 1; ring
        simp only [e]
        have h0 : l (c - ((0 : ℕ) : ℝ) * h) = l c := by simp
        rw [h0]
        have hsum : (σ c - σ (c - h)) / h + σ (c - h) / h = σ c / h := by ring
        linarith [h2 N]

private lemma p7_pt {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∑ j ∈ Finset.range N, (a * β ^ (2 * j)) / (1 + a * β ^ (2 * j)) ^ 2
      ≤ 1 / 4 + 1 / (2 * Real.log (1 / β)) := by
  have hL : 0 < Real.log (1 / β) := Real.log_pos (by rw [lt_div_iff₀ hβ0]; linarith)
  have hh : 0 < 2 * Real.log (1 / β) := by linarith
  have hK : ∀ a b v : ℝ, a < b → (∀ ξ ∈ Ioo a b, |ξ| ≤ |v|) →
      Real.exp v / (1 + Real.exp v) ^ 2 ≤
        (Real.exp b / (1 + Real.exp b) - Real.exp a / (1 + Real.exp a)) / (b - a) :=
    fun a b v hab hv => p7_K hab hv
  obtain ⟨k, hk⟩ := exists_nat_gt (Real.log a / (2 * Real.log (1 / β)))
  have hk' : Real.log a < (k + 1) * (2 * Real.log (1 / β)) := by
    rw [div_lt_iff₀ hh] at hk
    nlinarith
  have key := p7_lattice (l := fun v => Real.exp v / (1 + Real.exp v) ^ 2)
    (σ := fun v => Real.exp v / (1 + Real.exp v)) hh hK
    (fun v => (p7_sigma_bounds v).1) p7_l_nonneg p7_l_le_quarter
    k (Real.log a) hk' N
  have hb : Real.exp (Real.log a) / (1 + Real.exp (Real.log a)) / (2 * Real.log (1 / β))
      ≤ 1 / (2 * Real.log (1 / β)) :=
    div_le_div_of_nonneg_right (p7_sigma_bounds _).2 hh.le
  have hterm : ∀ j : ℕ, Real.exp (Real.log a - j * (2 * Real.log (1 / β))) = a * β ^ (2 * j) := by
    intro j
    have e1 : Real.exp (j * (2 * Real.log (1 / β))) = (β⁻¹) ^ (2 * j) := by
      rw [show (j : ℝ) * (2 * Real.log (1 / β)) = ((2 * j : ℕ) : ℝ) * Real.log (1 / β) by
        push_cast; ring, Real.exp_nat_mul, Real.exp_log (by positivity), one_div]
    rw [Real.exp_sub, Real.exp_log ha, e1, inv_pow, div_inv_eq_mul]
  simp only [hterm] at key
  linarith

private lemma p7_term_int {β : ℝ} (j : ℕ) (y : ℝ) (hy : 0 < y) (hβ1 : β < 1) :
    Integrable (fun g : ℝ => (Muon.emaW β j ^ 2 * y) *
      (g ^ 2 / (1 + (Muon.emaW β j ^ 2 * y) * g ^ 2) ^ 2)) (gaussianReal 0 1) :=
  (p1_deriv_int (mul_nonneg (sq_nonneg _) hy.le)).const_mul _

/-! ### `lem:app-iso-slope` -/

/-- `lem:app-iso-slope`, snapshot `cr-2026-10-23`. The environment below; `β ∈ (0,1)` is the
standing hypothesis of the subsection (`section.tex` l.2380–2384).
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Participation slope]\label{lem:app-iso-slope}
For every $y>0$,
\[
\mathsf e_\bmom(y)\le\frac14+\frac1{2\log(1/\bmom)}\le\bar{\mathsf e}_\bmom .
\]
\end{lemma}
```
-/
theorem lem_app_iso_slope {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ y : ℝ, 0 < y →
      isoEslope β y ≤ 1 / 4 + 1 / (2 * Real.log (1 / β)) ∧
      1 / 4 + 1 / (2 * Real.log (1 / β)) ≤ isoEbar β := by
  intro y hy
  refine ⟨?_, le_max_right _ _⟩
  set B : ℝ := 1 / 4 + 1 / (2 * Real.log (1 / β)) with hB
  have hterm : ∀ j : ℕ, y * (Muon.emaW β j ^ 2 * isoPhiDeriv (Muon.emaW β j ^ 2 * y)) =
      ∫ g, (Muon.emaW β j ^ 2 * y) *
        (g ^ 2 / (1 + (Muon.emaW β j ^ 2 * y) * g ^ 2) ^ 2) ∂(gaussianReal 0 1) := by
    intro j
    rw [integral_const_mul]
    unfold isoPhiDeriv
    ring
  have hnn : ∀ j : ℕ, 0 ≤ y * (Muon.emaW β j ^ 2 * isoPhiDeriv (Muon.emaW β j ^ 2 * y)) := by
    intro j
    rw [hterm j]
    exact integral_nonneg (fun g => mul_nonneg (mul_nonneg (sq_nonneg _) hy.le)
      (div_nonneg (sq_nonneg g) (sq_nonneg _)))
  have hpt : ∀ (N : ℕ) (g : ℝ), ∑ j ∈ Finset.range N, (Muon.emaW β j ^ 2 * y) *
      (g ^ 2 / (1 + (Muon.emaW β j ^ 2 * y) * g ^ 2) ^ 2) ≤ B := by
    intro N g
    have hB0 : 0 ≤ B := by
      have hL : 0 < Real.log (1 / β) := Real.log_pos (by rw [lt_div_iff₀ hβ0]; linarith)
      rw [hB]; positivity
    by_cases hg : g = 0
    · subst hg
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
        Finset.sum_const_zero]
      exact hB0
    · have ha : 0 < (1 - β) ^ 2 * y * g ^ 2 :=
        mul_pos (mul_pos (pow_pos (sub_pos.mpr hβ1) 2) hy) (by positivity)
      have := p7_pt hβ0 hβ1 ha N
      refine le_trans (le_of_eq ?_) this
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have e : (Muon.emaW β j ^ 2 * y) * g ^ 2 = (1 - β) ^ 2 * y * g ^ 2 * β ^ (2 * j) := by
        unfold Muon.emaW; ring
      rw [← mul_div_assoc, e]
  unfold isoEslope
  rw [p5_deriv_eq hβ0 hβ1 hy, p5_isoRderiv_nat hβ0 hβ1 y, ← tsum_mul_left]
  refine Real.tsum_le_of_sum_range_le hnn (fun N => ?_)
  simp only [hterm]
  rw [← integral_finset_sum _ (fun j _ => p7_term_int j y hy hβ1)]
  calc _ ≤ ∫ g : ℝ, B ∂(gaussianReal 0 1) :=
        integral_mono (integrable_finset_sum _ (fun j _ => p7_term_int j y hy hβ1))
          (integrable_const B) (fun g => hpt N g)
    _ = B := by simp

/-! ### Private helpers for `lem_app_iso_shifts` (task P-F.1.P8) -/

private lemma p8_rW_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ rW (Muon.emaW β) q := by
  rw [p5_rW_nat hβ0 hβ1 hq]
  exact tsum_nonneg (fun j => (p3_isoPhi_bounds (mul_nonneg (sq_nonneg _) hq)).1)

private lemma p8_rW_mono {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : rW (Muon.emaW β) a ≤ rW (Muon.emaW β) b := by
  have hb : 0 ≤ b := ha.trans hab
  rw [p5_rW_nat hβ0 hβ1 ha, p5_rW_nat hβ0 hβ1 hb]
  exact Summable.tsum_le_tsum
    (fun j => p4_isoPhi_mono (mul_nonneg (sq_nonneg _) ha)
      (mul_le_mul_of_nonneg_left hab (sq_nonneg _)))
    (p5_summable_phi hβ0 hβ1 ha) (p5_summable_phi hβ0 hβ1 hb)

private lemma p8_shift_one {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : ℝ} (hQ : 0 ≤ Q) :
    rW (Muon.emaW β) (Q / β ^ 2) = rW (Muon.emaW β) Q + isoPhi ((1 - β) ^ 2 * Q / β ^ 2) := by
  have hne : β ≠ 0 := hβ0.ne'
  have hq : (0 : ℝ) ≤ Q / β ^ 2 := div_nonneg hQ (pow_nonneg hβ0.le 2)
  rw [p5_rW_nat hβ0 hβ1 hq, p5_rW_nat hβ0 hβ1 hQ,
    Summable.tsum_eq_zero_add (p5_summable_phi hβ0 hβ1 hq)]
  have e : ∀ j : ℕ, Muon.emaW β (j + 1) ^ 2 * (Q / β ^ 2) = Muon.emaW β j ^ 2 * Q := by
    intro j
    unfold Muon.emaW
    field_simp
    ring
  have e0 : Muon.emaW β 0 ^ 2 * (Q / β ^ 2) = (1 - β) ^ 2 * Q / β ^ 2 := by
    unfold Muon.emaW
    ring
  simp only [e, e0]
  ring

private lemma p8_shift_range {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (k : ℕ) :
    ∀ Q : ℝ, 0 < Q → rW (Muon.emaW β) (Q / β ^ (2 * k)) =
      rW (Muon.emaW β) Q + ∑ i ∈ Finset.range k, isoPhi ((1 - β) ^ 2 * Q / β ^ (2 * (1 + i))) := by
  induction k with
  | zero => intro Q hQ; simp
  | succ k ih =>
    intro Q hQ
    have hne : β ≠ 0 := hβ0.ne'
    have hQ2 : 0 < Q / β ^ 2 := div_pos hQ (pow_pos hβ0 2)
    have harg : Q / β ^ (2 * (k + 1)) = (Q / β ^ 2) / β ^ (2 * k) := by
      field_simp
      ring
    rw [harg, ih (Q / β ^ 2) hQ2, p8_shift_one hβ0 hβ1 hQ.le]
    have hsum : ∑ i ∈ Finset.range k, isoPhi ((1 - β) ^ 2 * (Q / β ^ 2) / β ^ (2 * (1 + i)))
        = ∑ i ∈ Finset.range k, isoPhi ((1 - β) ^ 2 * Q / β ^ (2 * (1 + (i + 1)))) :=
      Finset.sum_congr rfl (fun i _ => by
        congr 1
        field_simp
        ring)
    rw [Finset.sum_range_succ', hsum]
    have h0 : (1 - β) ^ 2 * Q / β ^ (2 * (1 + 0)) = (1 - β) ^ 2 * Q / β ^ 2 := by norm_num
    rw [h0]
    ring

private lemma p8_icc_range {β : ℝ} (Q : ℝ) (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 k, isoPhi ((1 - β) ^ 2 * Q / β ^ (2 * i)) =
      ∑ i ∈ Finset.range k, isoPhi ((1 - β) ^ 2 * Q / β ^ (2 * (1 + i))) := by
  have hI : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]

/-! ### `lem:app-iso-shifts` -/

/-- `lem:app-iso-shifts`(i), snapshot `cr-2026-10-23`. Part (i) of the environment below
(`r = rW (Muon.emaW β)`, `β^{-2k} Q` is `Q / β ^ (2 * k)`); the interval `[0,k]` is written as two
inequalities.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Shifts of the participation level]\label{lem:app-iso-shifts}
Let $Q,y,z>0$ and let $k\ge0$ be an integer.
\begin{enumerate}[label=(\roman*)]
\item $\displaystyle r(\bmom^{-2k}Q)-r(Q)=\sum_{i=1}^k\Phi\big((1-\bmom)^2\bmom^{-2i}Q\big)\in[0,k]$.
\item $r(\bmom^{-2k}Q)\ge\mathsf n_\bmom(Q)+k-\mathsf c_\bmom$.
\item $r(Q)\le\mathsf n_\bmom(Q)+\mathsf c'_\bmom+\mathsf n^-_\bmom(Q)$.
\item $\abs{r(y)-r(z)}\le\bar{\mathsf e}_\bmom\,\abs{\log(y/z)}$.
\item If $\gamma\ge\gamma^\circ_\bmom$ and $r(\bmom^{-2}z)<\gamma$, then $\mathsf A(z)>\Phi(1)$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_shifts_i {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ Q : ℝ, 0 < Q → ∀ k : ℕ,
      rW (Muon.emaW β) (Q / β ^ (2 * k)) - rW (Muon.emaW β) Q =
        ∑ i ∈ Finset.Icc 1 k, isoPhi ((1 - β) ^ 2 * Q / β ^ (2 * i)) ∧
      0 ≤ rW (Muon.emaW β) (Q / β ^ (2 * k)) - rW (Muon.emaW β) Q ∧
      rW (Muon.emaW β) (Q / β ^ (2 * k)) - rW (Muon.emaW β) Q ≤ (k : ℝ) := by
  intro Q hQ k
  have h1β : 0 < 1 - β := by linarith
  have hterm : ∀ i ∈ Finset.Icc 1 k, 0 < (1 - β) ^ 2 * Q / β ^ (2 * i) := fun i _ =>
    div_pos (mul_pos (pow_pos h1β 2) hQ) (pow_pos hβ0 _)
  have hdiff : rW (Muon.emaW β) (Q / β ^ (2 * k)) - rW (Muon.emaW β) Q =
      ∑ i ∈ Finset.Icc 1 k, isoPhi ((1 - β) ^ 2 * Q / β ^ (2 * i)) := by
    rw [p8_shift_range hβ0 hβ1 k Q hQ, p8_icc_range]
    ring
  refine ⟨hdiff, ?_, ?_⟩
  · rw [hdiff]
    exact Finset.sum_nonneg (fun i hi => (p3_isoPhi_bounds (hterm i hi).le).1)
  · rw [hdiff]
    have := Finset.sum_le_card_nsmul (Finset.Icc 1 k)
      (fun i => isoPhi ((1 - β) ^ 2 * Q / β ^ (2 * i))) 1
      (fun i hi => (p1_isoPhi_lt_one (hterm i hi)).le)
    simpa [Nat.card_Icc] using this

/-- `lem:app-iso-shifts`(ii), snapshot `cr-2026-10-23`. Part (ii) of the environment below.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Shifts of the participation level]\label{lem:app-iso-shifts}
Let $Q,y,z>0$ and let $k\ge0$ be an integer.
\begin{enumerate}[label=(\roman*)]
\item $\displaystyle r(\bmom^{-2k}Q)-r(Q)=\sum_{i=1}^k\Phi\big((1-\bmom)^2\bmom^{-2i}Q\big)\in[0,k]$.
\item $r(\bmom^{-2k}Q)\ge\mathsf n_\bmom(Q)+k-\mathsf c_\bmom$.
\item $r(Q)\le\mathsf n_\bmom(Q)+\mathsf c'_\bmom+\mathsf n^-_\bmom(Q)$.
\item $\abs{r(y)-r(z)}\le\bar{\mathsf e}_\bmom\,\abs{\log(y/z)}$.
\item If $\gamma\ge\gamma^\circ_\bmom$ and $r(\bmom^{-2}z)<\gamma$, then $\mathsf A(z)>\Phi(1)$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_shifts_ii {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ Q : ℝ, 0 < Q → ∀ k : ℕ,
      isoN β Q + (k : ℝ) - isoC β ≤ rW (Muon.emaW β) (Q / β ^ (2 * k)) := by
  intro Q hQ k
  have h1β : 0 < 1 - β := by linarith
  have hL : 0 < Real.log (1 / β) := Real.log_pos (one_lt_one_div hβ0 hβ1)
  have hL' : Real.log (1 / β) ≠ 0 := hL.ne'
  have hq' : 0 < Q / β ^ (2 * k) := div_pos hQ (pow_pos hβ0 _)
  have hN : isoN β (Q / β ^ (2 * k)) = isoN β Q + (k : ℝ) := by
    unfold isoN
    have hA : (1 - β) ^ 2 * (Q / β ^ (2 * k)) = (1 - β) ^ 2 * Q * (1 / β) ^ (2 * k) := by
      rw [one_div, inv_pow]
      ring
    rw [hA, Real.log_mul (mul_pos (pow_pos h1β 2) hQ).ne'
      (pow_pos (one_div_pos.2 hβ0) _).ne', Real.log_pow]
    push_cast
    field_simp
  have hC : 0 < isoC β := div_pos (Real.sqrt_pos.2 (by positivity)) h1β
  rcases le_or_gt 1 ((1 - β) ^ 2 * (Q / β ^ (2 * k))) with hx | hx
  · have := ((lem_app_iso_count_i hβ0 hβ1).1 _ hx).1
    rw [hN] at this
    linarith
  · have hpos : 0 < (1 - β) ^ 2 * (Q / β ^ (2 * k)) := mul_pos (pow_pos h1β 2) hq'
    have hlog : Real.log ((1 - β) ^ 2 * (Q / β ^ (2 * k))) < 0 := Real.log_neg hpos hx
    have hNneg : isoN β (Q / β ^ (2 * k)) < 0 := by
      unfold isoN
      exact div_neg_of_neg_of_pos hlog (by linarith)
    have := p8_rW_nonneg hβ0 hβ1 hq'.le
    linarith

/-- `lem:app-iso-shifts`(iii), snapshot `cr-2026-10-23`. Part (iii) of the environment below
(`𝗇^-_β(Q) = max(0, -𝗇_β(Q))`, `section.tex` l.2394).
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Shifts of the participation level]\label{lem:app-iso-shifts}
Let $Q,y,z>0$ and let $k\ge0$ be an integer.
\begin{enumerate}[label=(\roman*)]
\item $\displaystyle r(\bmom^{-2k}Q)-r(Q)=\sum_{i=1}^k\Phi\big((1-\bmom)^2\bmom^{-2i}Q\big)\in[0,k]$.
\item $r(\bmom^{-2k}Q)\ge\mathsf n_\bmom(Q)+k-\mathsf c_\bmom$.
\item $r(Q)\le\mathsf n_\bmom(Q)+\mathsf c'_\bmom+\mathsf n^-_\bmom(Q)$.
\item $\abs{r(y)-r(z)}\le\bar{\mathsf e}_\bmom\,\abs{\log(y/z)}$.
\item If $\gamma\ge\gamma^\circ_\bmom$ and $r(\bmom^{-2}z)<\gamma$, then $\mathsf A(z)>\Phi(1)$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_shifts_iii {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ Q : ℝ, 0 < Q →
      rW (Muon.emaW β) Q ≤ isoN β Q + isoC' β + max 0 (-isoN β Q) := by
  intro Q hQ
  have h1β : 0 < 1 - β := by linarith
  have hm1 : 0 ≤ max 0 (-isoN β Q) := le_max_left _ _
  have hm2 : -isoN β Q ≤ max 0 (-isoN β Q) := le_max_right _ _
  rcases le_or_gt 1 ((1 - β) ^ 2 * Q) with hx | hx
  · have := ((lem_app_iso_count_i hβ0 hβ1).1 Q hx).2
    linarith
  · have hle : Q ≤ 1 / (1 - β) ^ 2 := by
      rw [le_div_iff₀ (pow_pos h1β 2), mul_comm]
      exact hx.le
    have h1 := p8_rW_mono hβ0 hβ1 hQ.le hle
    have h2 := (lem_app_iso_count_i hβ0 hβ1).2
    linarith

/-- `lem:app-iso-shifts`(iv), snapshot `cr-2026-10-23`. Part (iv) of the environment below.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Shifts of the participation level]\label{lem:app-iso-shifts}
Let $Q,y,z>0$ and let $k\ge0$ be an integer.
\begin{enumerate}[label=(\roman*)]
\item $\displaystyle r(\bmom^{-2k}Q)-r(Q)=\sum_{i=1}^k\Phi\big((1-\bmom)^2\bmom^{-2i}Q\big)\in[0,k]$.
\item $r(\bmom^{-2k}Q)\ge\mathsf n_\bmom(Q)+k-\mathsf c_\bmom$.
\item $r(Q)\le\mathsf n_\bmom(Q)+\mathsf c'_\bmom+\mathsf n^-_\bmom(Q)$.
\item $\abs{r(y)-r(z)}\le\bar{\mathsf e}_\bmom\,\abs{\log(y/z)}$.
\item If $\gamma\ge\gamma^\circ_\bmom$ and $r(\bmom^{-2}z)<\gamma$, then $\mathsf A(z)>\Phi(1)$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_shifts_iv {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ y z : ℝ, 0 < y → 0 < z →
      |rW (Muon.emaW β) y - rW (Muon.emaW β) z| ≤ isoEbar β * |Real.log (y / z)| := by
  intro y z hy hz
  have hdiff : ∀ t : ℝ, HasDerivAt (fun t : ℝ => rW (Muon.emaW β) (Real.exp t))
      (isoRderiv β (Real.exp t) * Real.exp t) t := by
    intro t
    have hpos : 0 < Real.exp t := Real.exp_pos t
    have h1 : HasDerivAt (rW (Muon.emaW β)) (isoRderiv β (Real.exp t)) (Real.exp t) :=
      (p3_rW_hasDerivWithinAt hβ0.le hβ1 hpos.le).hasDerivAt (Ici_mem_nhds hpos)
    exact h1.comp t (Real.hasDerivAt_exp t)
  have hbound : ∀ t : ℝ, ‖isoRderiv β (Real.exp t) * Real.exp t‖ ≤ isoEbar β := by
    intro t
    have hpos : 0 < Real.exp t := Real.exp_pos t
    have hs := (lem_app_iso_slope hβ0 hβ1 (Real.exp t) hpos).1
    have hs2 := (lem_app_iso_slope hβ0 hβ1 (Real.exp t) hpos).2
    have hE : isoEslope β (Real.exp t) = Real.exp t * isoRderiv β (Real.exp t) := by
      unfold isoEslope
      rw [p5_deriv_eq hβ0 hβ1 hpos]
    have hR := p3_isoRderiv_pos hβ0.le hβ1 (Real.exp_pos t).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_pos hR hpos).le, mul_comm, ← hE]
    linarith
  have hlip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => rW (Muon.emaW β) (Real.exp t))
    (f' := fun t : ℝ => isoRderiv β (Real.exp t) * Real.exp t)
    (s := Set.univ) (x := Real.log z) (y := Real.log y) (C := isoEbar β)
    (fun t _ => (hdiff t).hasDerivWithinAt) (fun t _ => hbound t) convex_univ
    (Set.mem_univ _) (Set.mem_univ _)
  simp only [Real.exp_log hy, Real.exp_log hz, Real.norm_eq_abs] at hlip
  rw [Real.log_div hy.ne' hz.ne']
  exact hlip

/-- `lem:app-iso-shifts`(v), snapshot `cr-2026-10-23`. Part (v) of the environment below
(`A(z) = γ - r(z)`; `β^{-2} z` is `z / β ^ 2`; `γ` is a free real parameter, the aspect ratio
`N/B` of the subsection).
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Shifts of the participation level]\label{lem:app-iso-shifts}
Let $Q,y,z>0$ and let $k\ge0$ be an integer.
\begin{enumerate}[label=(\roman*)]
\item $\displaystyle r(\bmom^{-2k}Q)-r(Q)=\sum_{i=1}^k\Phi\big((1-\bmom)^2\bmom^{-2i}Q\big)\in[0,k]$.
\item $r(\bmom^{-2k}Q)\ge\mathsf n_\bmom(Q)+k-\mathsf c_\bmom$.
\item $r(Q)\le\mathsf n_\bmom(Q)+\mathsf c'_\bmom+\mathsf n^-_\bmom(Q)$.
\item $\abs{r(y)-r(z)}\le\bar{\mathsf e}_\bmom\,\abs{\log(y/z)}$.
\item If $\gamma\ge\gamma^\circ_\bmom$ and $r(\bmom^{-2}z)<\gamma$, then $\mathsf A(z)>\Phi(1)$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_shifts_v {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ γ z : ℝ, 0 < z → isoGammaCirc β ≤ γ →
      rW (Muon.emaW β) (z / β ^ 2) < γ → isoPhi 1 < γ - rW (Muon.emaW β) z := by
  intro γ z hz hγ hr
  unfold isoGammaCirc at hγ
  have h1β : 0 < 1 - β := by linarith
  have hshift := p8_shift_one hβ0 hβ1 hz.le
  have hx0 : 0 < (1 - β) ^ 2 * z / β ^ 2 :=
    div_pos (mul_pos (pow_pos h1β 2) hz) (pow_pos hβ0 2)
  have hA : isoPhi ((1 - β) ^ 2 * z / β ^ 2) < γ - rW (Muon.emaW β) z := by linarith
  rcases le_or_gt 1 ((1 - β) ^ 2 * z / β ^ 2) with hx | hx
  · have := p4_isoPhi_mono zero_le_one hx
    linarith
  · have hβ2 : β ^ 2 < 1 := by nlinarith
    have hx' : (1 - β) ^ 2 * z < β ^ 2 := (div_lt_one (pow_pos hβ0 2)).mp hx
    have hle : z ≤ 1 / (1 - β) ^ 2 := by
      rw [le_div_iff₀ (pow_pos h1β 2)]
      nlinarith
    have h1 := p8_rW_mono hβ0 hβ1 hz.le hle
    have h2 := (lem_app_iso_count_i hβ0 hβ1).2
    have h3 := p1_isoPhi_lt_one one_pos
    linarith

end Muon.Isotropic

end

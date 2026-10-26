import Muon.Isotropic.ZeroRidge
import Muon.Foundations.Conventions

/-!
# Appendix F: the Marchenko–Pastur limit, the small and large aspect laws, and the linear root

Task L-F.5 (interface). Snapshot `cr-2026-10-23`. Source: `sections/05b-isotropic/section.tex`.
Labels owned (ledger, card §5 L-F.5): `lem:app-iso-mp` (l.1444–1463), `prop:app-iso-reciprocity`
parts (ii) and (iii) (l.1589–1608), `thm:app-iso-small-momentum` (l.1954–1980), and the pair-free
helpers `C0_small_asymp`, `C0_large_bound`. `thm:app-iso-small` and `thm:app-iso-large` are L-F.6. Objects used: `S_ν(−t)` (l.784), `𝖬_r` and `J_r`
(l.1444, l.1520), `Y_{γin,γout}` and `𝔡_lin` (`eqn:app-iso-dlin`, l.1944–1952), `𝖷`
(`eqn:app-iso-chi`).

Reuse (never redefined here): `Muon.Isotropic.dIso`, `Muon.Isotropic.Cbeta` (= `C_β`, and
`C = Cbeta 0`), `Muon.Isotropic.isoPhi` (= `Φ`), `Muon.sPow` (= `\sw{p}`), `Muon.emaW`.
Every theorem is a statement only (`sorry`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

noncomputable section
open scoped Classical

namespace Muon.Isotropic

/-! ## Definitions -/

/-- `S_ν(−t) = ∫ ν(dx)/(x+t)` for `t > 0` (`sections/05b-isotropic/section.tex` l.784). -/
def isoNegStieltjes (ν : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ x, (x + t)⁻¹ ∂ν

/-- `a_r = (1−√r)²/r` (`lem:app-iso-mp`). -/
def isoMPa (r : ℝ) : ℝ := (1 - Real.sqrt r) ^ 2 / r

/-- `b_r = (1+√r)²/r` (`lem:app-iso-mp`). -/
def isoMPb (r : ℝ) : ℝ := (1 + Real.sqrt r) ^ 2 / r

/-- `ω_r = (1−1/r)_+` (`lem:app-iso-mp`). -/
def isoMPomega (r : ℝ) : ℝ := max (1 - 1 / r) 0

/-- The limiting law `𝖬_r` of `lem:app-iso-mp` (`eqn:app-iso-mp`):
`ω_r δ₀ + √((b_r−x)(x−a_r))/(2πx) 1_{(a_r,b_r)}(x) dx`. -/
def isoMP (r : ℝ) : Measure ℝ :=
  ENNReal.ofReal (isoMPomega r) • Measure.dirac 0 +
    (volume.restrict (Ioo (isoMPa r) (isoMPb r))).withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * x)))

/-- `J_r = ∫ √x 𝖬_r(dx)` (`thm:app-iso-small`(iii), l.1520; L-F.6). -/
def isoJr (r : ℝ) : ℝ := ∫ x, Real.sqrt x ∂(isoMP r)

/-- `Y_{γin,γout}(s)`: the root `Y < γ∧` of `sY = (γout−Y)(γin−Y)` (l.1944–1952), i.e. the
instance `r(q) = q` of `lem:app-iso-comparison`, which is `isoRoot` of `Closure.lean`. The paper's
closed form `2γinγout/(γin+γout+s+√((γin+γout+s)²−4γinγout))` is not encoded here. -/
def isoYroot (γin γout s : ℝ) : ℝ :=
  isoRoot (fun q : ℝ => q) γin γout s

/-- `𝔡_lin(γin,γout;ϱ) = √2/(π γin γout) ∫_0^∞ Y_{γin,γout}(ϱ+v²) dv` (`eqn:app-iso-dlin`). -/
def isoDlin (γin γout ϱ : ℝ) : ℝ :=
  Real.sqrt 2 / (Real.pi * γin * γout) * ∫ v in Ioi (0 : ℝ), isoYroot γin γout (ϱ + v ^ 2)

/-! ## Limiting law -/

/-! ### Helpers for `lem_app_iso_mp` -/
private theorem poisson_hasDerivAt (ρ θ : ℝ) (hρ : |ρ| < 1) :
    HasDerivAt (fun θ : ℝ => θ - 2 * Real.arctan (ρ * Real.sin θ / (1 + ρ * Real.cos θ)))
      ((1 - ρ ^ 2) / (1 + 2 * ρ * Real.cos θ + ρ ^ 2)) θ := by
  have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hpos : 0 < 1 + ρ * Real.cos θ := by
    have : |ρ * Real.cos θ| < 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg ρ, abs_nonneg (Real.cos θ)]
    linarith [(abs_lt.1 this).1]
  have hq : HasDerivAt (fun θ : ℝ => ρ * Real.sin θ / (1 + ρ * Real.cos θ))
      ((ρ * Real.cos θ * (1 + ρ * Real.cos θ) - ρ * Real.sin θ * (-(ρ * Real.sin θ))) /
        (1 + ρ * Real.cos θ) ^ 2) θ := by
    have h1 : HasDerivAt (fun θ : ℝ => ρ * Real.sin θ) (ρ * Real.cos θ) θ :=
      (Real.hasDerivAt_sin θ).const_mul ρ
    have h2 : HasDerivAt (fun θ : ℝ => 1 + ρ * Real.cos θ) (-(ρ * Real.sin θ)) θ := by
      have := ((Real.hasDerivAt_cos θ).const_mul ρ).const_add 1
      simpa [mul_neg] using this
    exact h1.div h2 hpos.ne'
  have ha := (hq.arctan)
  have hd : HasDerivAt (fun θ : ℝ => θ - 2 * Real.arctan (ρ * Real.sin θ / (1 + ρ * Real.cos θ)))
      (1 - 2 * (1 / (1 + (ρ * Real.sin θ / (1 + ρ * Real.cos θ)) ^ 2) *
          ((ρ * Real.cos θ * (1 + ρ * Real.cos θ) - ρ * Real.sin θ * (-(ρ * Real.sin θ))) /
            (1 + ρ * Real.cos θ) ^ 2))) θ :=
    (hasDerivAt_id θ).sub (ha.const_mul 2)
  refine hd.congr_deriv ?_
  have hs := Real.sin_sq_add_cos_sq θ
  have h1 : 1 + 2 * ρ * Real.cos θ + ρ ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (ρ + Real.cos θ), sq_nonneg (Real.sin θ), abs_lt.1 hρ]
  have h3 : (1 + (ρ * Real.sin θ / (1 + ρ * Real.cos θ)) ^ 2) =
      (1 + 2 * ρ * Real.cos θ + ρ ^ 2) / (1 + ρ * Real.cos θ) ^ 2 := by
    field_simp
    nlinarith [hs]
  rw [h3]
  field_simp
  linear_combination (-2 * ρ ^ 2) * hs

private theorem poisson_integral (ρ : ℝ) (hρ : |ρ| < 1) :
    ∫ θ in (0:ℝ)..Real.pi, (1 - ρ ^ 2) / (1 + 2 * ρ * Real.cos θ + ρ ^ 2) = Real.pi := by
  have hne : ∀ θ : ℝ, 1 + 2 * ρ * Real.cos θ + ρ ^ 2 ≠ 0 := by
    intro θ h
    have hs := Real.sin_sq_add_cos_sq θ
    have h1 : (ρ + Real.cos θ) ^ 2 + Real.sin θ ^ 2 = 0 := by nlinarith
    have h2 : Real.sin θ ^ 2 = 0 := by nlinarith [sq_nonneg (ρ + Real.cos θ), sq_nonneg (Real.sin θ)]
    have h3 : (ρ + Real.cos θ) ^ 2 = 0 := by nlinarith [sq_nonneg (ρ + Real.cos θ), sq_nonneg (Real.sin θ)]
    have h4 : ρ + Real.cos θ = 0 := by simpa using h3
    have h5 : Real.cos θ ^ 2 = 1 := by nlinarith
    have h6 : ρ ^ 2 = 1 := by have : ρ = -Real.cos θ := by linarith
                              rw [this]; nlinarith
    have := abs_lt.1 hρ
    nlinarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => poisson_hasDerivAt ρ θ hρ)]
  · simp
  · apply Continuous.intervalIntegrable
    exact Continuous.div (by fun_prop) (by fun_prop) hne

private theorem inv_cos_integral (α β : ℝ) (hβ : 0 < β) (hα : β < α) :
    ∫ θ in (0:ℝ)..Real.pi, 1 / (α + β * Real.cos θ) = Real.pi / Real.sqrt (α ^ 2 - β ^ 2) := by
  have hD2 : 0 < α ^ 2 - β ^ 2 := by nlinarith
  set D := Real.sqrt (α ^ 2 - β ^ 2) with hDdef
  have hDpos : 0 < D := Real.sqrt_pos.2 hD2
  have hDsq : D ^ 2 = α ^ 2 - β ^ 2 := Real.sq_sqrt hD2.le
  have hDlt : D < α := by nlinarith
  set ρ := (α - D) / β with hρdef
  have hρ0 : 0 < ρ := div_pos (by linarith) hβ
  have hρ1 : ρ < 1 := by
    rw [hρdef, div_lt_one hβ]; nlinarith
  have hρ : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  have key : ∀ θ : ℝ, 1 / (α + β * Real.cos θ) =
      (1 / D) * ((1 - ρ ^ 2) / (1 + 2 * ρ * Real.cos θ + ρ ^ 2)) := by
    intro θ
    have hc := Real.abs_cos_le_one θ
    have hden : α + β * Real.cos θ ≠ 0 := by
      nlinarith [abs_le.1 hc]
    have e1 : 1 + 2 * ρ * Real.cos θ + ρ ^ 2 = (2 * ρ / β) * (α + β * Real.cos θ) := by
      rw [hρdef]; field_simp; nlinarith [hDsq]
    have e2 : 1 - ρ ^ 2 = 2 * D * ρ / β := by
      rw [hρdef]; field_simp; nlinarith [hDsq]
    rw [e1, e2]
    field_simp
  simp_rw [key]
  rw [intervalIntegral.integral_const_mul, poisson_integral ρ hρ]
  field_simp

private theorem sin_sq_div_integral (α β : ℝ) (hβ : 0 < β) (hα : β < α) :
    ∫ θ in (0:ℝ)..Real.pi, Real.sin θ ^ 2 / (α + β * Real.cos θ) =
      Real.pi * (α - Real.sqrt (α ^ 2 - β ^ 2)) / β ^ 2 := by
  have hD2 : 0 < α ^ 2 - β ^ 2 := by nlinarith
  have hDpos : 0 < Real.sqrt (α ^ 2 - β ^ 2) := Real.sqrt_pos.2 hD2
  have hDsq : Real.sqrt (α ^ 2 - β ^ 2) ^ 2 = α ^ 2 - β ^ 2 := Real.sq_sqrt hD2.le
  have key : ∀ θ : ℝ, Real.sin θ ^ 2 / (α + β * Real.cos θ) =
      (-(1 / β) * Real.cos θ + α / β ^ 2) +
        ((β ^ 2 - α ^ 2) / β ^ 2) * (1 / (α + β * Real.cos θ)) := by
    intro θ
    have hc := Real.abs_cos_le_one θ
    have hden : α + β * Real.cos θ ≠ 0 := by nlinarith [abs_le.1 hc]
    have hs := Real.sin_sq_add_cos_sq θ
    field_simp
    nlinarith [hs]
  simp_rw [key]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, inv_cos_integral α β hβ hα]
  · simp only [integral_cos, Real.sin_pi, Real.sin_zero, intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    linear_combination Real.pi * hDsq
  all_goals
    first
    | (apply Continuous.intervalIntegrable; fun_prop)
    | (apply Continuous.intervalIntegrable
       exact continuous_const.mul (Continuous.div (by fun_prop) (by fun_prop) (fun θ => by
         have := Real.abs_cos_le_one θ
         nlinarith [abs_le.1 this])))

private theorem mpL_sq (r : ℝ) (hr : 0 < r) : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le

private theorem mpL_a (r : ℝ) (hr : 0 < r) : isoMPa r = (1 + 1 / r) - 2 / Real.sqrt r := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have h2 := mpL_sq r hr
  unfold isoMPa
  field_simp
  nlinarith [h2]

private theorem mpL_b (r : ℝ) (hr : 0 < r) : isoMPb r = (1 + 1 / r) + 2 / Real.sqrt r := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have h2 := mpL_sq r hr
  unfold isoMPb
  field_simp
  nlinarith [h2]

private theorem mpL_a_nonneg (r : ℝ) (hr : 0 < r) : 0 ≤ isoMPa r := by
  unfold isoMPa; positivity

/-- change of variables `x = c + d cos θ` -/
private theorem mpL_image (c d : ℝ) (hd : 0 < d) :
    (fun θ : ℝ => c + d * Real.cos θ) '' Ioo 0 Real.pi = Ioo (c - d) (c + d) := by
  ext x
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    have h1 : Real.cos θ < 1 := by
      rw [← Real.cos_zero]; exact Real.strictAntiOn_cos ⟨le_refl _, Real.pi_pos.le⟩
        ⟨hθ.1.le, hθ.2.le⟩ hθ.1
    have h2 : -1 < Real.cos θ := by
      rw [← Real.cos_pi]; exact Real.strictAntiOn_cos ⟨hθ.1.le, hθ.2.le⟩
        ⟨Real.pi_pos.le, le_refl _⟩ hθ.2
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    have hy1 : -1 < (x - c) / d := by rw [lt_div_iff₀ hd]; linarith
    have hy2 : (x - c) / d < 1 := by rw [div_lt_iff₀ hd]; linarith
    refine ⟨Real.arccos ((x - c) / d), ⟨Real.arccos_pos.2 hy2, Real.arccos_lt_pi.2 hy1⟩, ?_⟩
    simp only
    rw [Real.cos_arccos hy1.le hy2.le]
    field_simp
    ring

private theorem mpL_cov (c d : ℝ) (hd : 0 < d) (G : ℝ → ℝ) :
    ∫ x in Ioo (c - d) (c + d), G x =
      ∫ θ in Ioo 0 Real.pi, d * Real.sin θ * G (c + d * Real.cos θ) := by
  have := integral_image_eq_integral_abs_deriv_smul (s := Ioo 0 Real.pi)
    (f := fun θ : ℝ => c + d * Real.cos θ) (f' := fun θ => -(d * Real.sin θ)) measurableSet_Ioo
    (fun θ _ => by
      have := ((Real.hasDerivAt_cos θ).const_mul d).const_add c
      simpa [mul_neg] using this.hasDerivWithinAt)
    (fun x hx y hy hxy => by
      have : d * Real.cos x = d * Real.cos y := by simpa using hxy
      exact Real.injOn_cos ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ (by
        have := mul_left_cancel₀ hd.ne' this; exact this)) G
  rw [mpL_image c d hd] at this
  rw [this]
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  simp only [smul_eq_mul]
  rw [abs_neg, abs_of_pos (mul_pos hd hs)]

private theorem mpL_cov_int (c d : ℝ) (hd : 0 < d) (G : ℝ → ℝ) :
    IntegrableOn G (Ioo (c - d) (c + d)) ↔
      IntegrableOn (fun θ => d * Real.sin θ * G (c + d * Real.cos θ)) (Ioo 0 Real.pi) := by
  have := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Ioo 0 Real.pi)
    (f := fun θ : ℝ => c + d * Real.cos θ) (f' := fun θ => -(d * Real.sin θ)) measurableSet_Ioo
    (fun θ _ => by
      have := ((Real.hasDerivAt_cos θ).const_mul d).const_add c
      simpa [mul_neg] using this.hasDerivWithinAt)
    (fun x hx y hy hxy => by
      have : d * Real.cos x = d * Real.cos y := by simpa using hxy
      exact Real.injOn_cos ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ (by
        have := mul_left_cancel₀ hd.ne' this; exact this)) G
  rw [mpL_image c d hd] at this
  rw [this]
  refine integrableOn_congr_fun (fun θ hθ => ?_) measurableSet_Ioo
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  simp only [smul_eq_mul]
  rw [abs_neg, abs_of_pos (mul_pos hd hs)]

private theorem mpL_theta_form (c d : ℝ) (hd : 0 < d) (_hdc : d ≤ c) (h : ℝ → ℝ) :
    ∫ x in Ioo (c - d) (c + d),
        Real.sqrt (((c + d) - x) * (x - (c - d))) / (2 * Real.pi * x) * h x =
      ∫ θ in Ioo 0 Real.pi,
        d ^ 2 * Real.sin θ ^ 2 / (2 * Real.pi * (c + d * Real.cos θ)) * h (c + d * Real.cos θ) := by
  rw [mpL_cov c d hd]
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have e : ((c + d) - (c + d * Real.cos θ)) * ((c + d * Real.cos θ) - (c - d)) =
      (d * Real.sin θ) ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ
    linear_combination (-d ^ 2) * this
  rw [e, Real.sqrt_sq (mul_pos hd hs).le]
  ring

private theorem mpL_theta_bound (c d : ℝ) (hd : 0 < d) (hdc : d ≤ c) (θ : ℝ)
    (hθ : θ ∈ Ioo 0 Real.pi) :
    0 ≤ d ^ 2 * Real.sin θ ^ 2 / (2 * Real.pi * (c + d * Real.cos θ)) ∧
    d ^ 2 * Real.sin θ ^ 2 / (2 * Real.pi * (c + d * Real.cos θ)) ≤ d / Real.pi := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hc1 : Real.cos θ < 1 := by
    rw [← Real.cos_zero]; exact Real.strictAntiOn_cos ⟨le_refl _, Real.pi_pos.le⟩
        ⟨hθ.1.le, hθ.2.le⟩ hθ.1
  have hc2 : -1 < Real.cos θ := by
    rw [← Real.cos_pi]; exact Real.strictAntiOn_cos ⟨hθ.1.le, hθ.2.le⟩
        ⟨Real.pi_pos.le, le_refl _⟩ hθ.2
  have hX : d * (1 + Real.cos θ) ≤ c + d * Real.cos θ := by nlinarith
  have hXpos : 0 < c + d * Real.cos θ := by nlinarith
  have hpi := Real.pi_pos
  have hsin : Real.sin θ ^ 2 = (1 - Real.cos θ) * (1 + Real.cos θ) := by
    have := Real.sin_sq_add_cos_sq θ; nlinarith
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity) hpi]
    have : Real.sin θ ^ 2 * d ≤ 2 * (c + d * Real.cos θ) := by
      rw [hsin]
      nlinarith [mul_pos hd (show 0 < 1 + Real.cos θ by linarith)]
    nlinarith [mul_pos hd hpi, mul_pos (mul_pos hd hpi) hd]

private theorem mpL_dens_int (c d : ℝ) (hd : 0 < d) (hdc : d ≤ c) (h : ℝ → ℝ)
    (hh : Measurable h) (M : ℝ) (hM : ∀ x ∈ Ioo (c - d) (c + d), |h x| ≤ M) :
    IntegrableOn (fun x => Real.sqrt (((c + d) - x) * (x - (c - d))) / (2 * Real.pi * x) * h x)
      (Ioo (c - d) (c + d)) := by
  rw [mpL_cov_int c d hd]
  have e : EqOn (fun θ => d * Real.sin θ * (Real.sqrt (((c + d) - (c + d * Real.cos θ)) *
      ((c + d * Real.cos θ) - (c - d))) / (2 * Real.pi * (c + d * Real.cos θ)) *
        h (c + d * Real.cos θ)))
      (fun θ => d ^ 2 * Real.sin θ ^ 2 / (2 * Real.pi * (c + d * Real.cos θ)) *
        h (c + d * Real.cos θ)) (Ioo 0 Real.pi) := by
    intro θ hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have e : ((c + d) - (c + d * Real.cos θ)) * ((c + d * Real.cos θ) - (c - d)) =
        (d * Real.sin θ) ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ
      linear_combination (-d ^ 2) * this
    beta_reduce
    rw [e, Real.sqrt_sq (mul_pos hd hs).le]
    ring
  refine (integrableOn_congr_fun e measurableSet_Ioo).2 ?_
  have hmeas : Measurable (fun θ : ℝ => d ^ 2 * Real.sin θ ^ 2 / (2 * Real.pi * (c + d * Real.cos θ)) *
        h (c + d * Real.cos θ)) := by
    have : Measurable (fun θ : ℝ => c + d * Real.cos θ) := by fun_prop
    exact (by fun_prop : Measurable (fun θ : ℝ => d ^ 2 * Real.sin θ ^ 2 /
      (2 * Real.pi * (c + d * Real.cos θ)))).mul (hh.comp this)
  have hint : IntegrableOn (fun _ : ℝ => d / Real.pi * M) (Ioo 0 Real.pi) := by
    rw [integrableOn_const_iff]; right; simp
  refine Integrable.mono' hint hmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Filter.Eventually.of_forall (fun θ hθ => ?_)
  obtain ⟨h0, h1⟩ := mpL_theta_bound c d hd hdc θ hθ
  have hmem : c + d * Real.cos θ ∈ Ioo (c - d) (c + d) := by
    rw [← mpL_image c d hd]; exact ⟨θ, hθ, rfl⟩
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  have hM' := hM _ hmem
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM'
  exact mul_le_mul h1 hM' (abs_nonneg _) (by positivity)

private theorem mpL_S_Ioo (α β : ℝ) (hβ : 0 < β) (hα : β ≤ α) :
    ∫ θ in Ioo 0 Real.pi, Real.sin θ ^ 2 / (α + β * Real.cos θ) =
      Real.pi * (α - Real.sqrt (α ^ 2 - β ^ 2)) / β ^ 2 := by
  rcases hα.lt_or_eq with hlt | heq
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le Real.pi_pos.le]
    exact sin_sq_div_integral α β hβ hlt
  · subst heq
    have : ∫ θ in Ioo 0 Real.pi, Real.sin θ ^ 2 / (β + β * Real.cos θ) =
        ∫ θ in Ioo 0 Real.pi, (1 - Real.cos θ) / β := by
      refine setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
      have hc2 : -1 < Real.cos θ := by
        rw [← Real.cos_pi]; exact Real.strictAntiOn_cos ⟨hθ.1.le, hθ.2.le⟩
          ⟨Real.pi_pos.le, le_refl _⟩ hθ.2
      have hs := Real.sin_sq_add_cos_sq θ
      have h1 : 0 < 1 + Real.cos θ := by linarith
      field_simp
      nlinarith [hs]
    rw [this, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le Real.pi_pos.le]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub]
    · simp
      field_simp
    · simp
    · exact (Real.continuous_cos.intervalIntegrable _ _)

private theorem mpL_dens_one (c d : ℝ) (hd : 0 < d) (hdc : d ≤ c) :
    ∫ x in Ioo (c - d) (c + d),
        Real.sqrt (((c + d) - x) * (x - (c - d))) / (2 * Real.pi * x) * 1 =
      (c - Real.sqrt (c ^ 2 - d ^ 2)) / 2 := by
  have h := mpL_theta_form c d hd hdc (fun _ => 1)
  rw [h]
  have e : ∀ θ ∈ Ioo 0 Real.pi,
      d ^ 2 * Real.sin θ ^ 2 / (2 * Real.pi * (c + d * Real.cos θ)) * 1 =
        d ^ 2 / (2 * Real.pi) * (Real.sin θ ^ 2 / (c + d * Real.cos θ)) := by
    intro θ hθ
    have hpi := Real.pi_pos
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo e, integral_const_mul, mpL_S_Ioo c d hd hdc]
  have hpi := Real.pi_pos
  field_simp

private theorem mpL_dens_id (c d : ℝ) (hd : 0 < d) (hdc : d ≤ c) :
    ∫ x in Ioo (c - d) (c + d),
        Real.sqrt (((c + d) - x) * (x - (c - d))) / (2 * Real.pi * x) * x = d ^ 2 / 4 := by
  have h := mpL_theta_form c d hd hdc (fun x => x)
  rw [h]
  have e : ∀ θ ∈ Ioo 0 Real.pi,
      d ^ 2 * Real.sin θ ^ 2 / (2 * Real.pi * (c + d * Real.cos θ)) * (c + d * Real.cos θ) =
        d ^ 2 / (2 * Real.pi) * Real.sin θ ^ 2 := by
    intro θ hθ
    have hpi := Real.pi_pos
    have hc2 : -1 < Real.cos θ := by
      rw [← Real.cos_pi]; exact Real.strictAntiOn_cos ⟨hθ.1.le, hθ.2.le⟩
        ⟨Real.pi_pos.le, le_refl _⟩ hθ.2
    have : 0 < c + d * Real.cos θ := by nlinarith
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo e, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_sin_sq]
  have hpi := Real.pi_pos
  simp
  field_simp
  norm_num

private theorem mpL_theta_int1 (c d : ℝ) (hd : 0 < d) (hdc : d ≤ c) :
    IntegrableOn (fun θ : ℝ => d ^ 2 * Real.sin θ ^ 2 / (2 * Real.pi * (c + d * Real.cos θ)))
      (Ioo 0 Real.pi) := by
  have hint : IntegrableOn (fun _ : ℝ => d / Real.pi) (Ioo 0 Real.pi) := by
    rw [integrableOn_const_iff]; right; simp
  refine Integrable.mono' hint (by fun_prop : Measurable (fun θ : ℝ =>
    d ^ 2 * Real.sin θ ^ 2 / (2 * Real.pi * (c + d * Real.cos θ)))).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Filter.Eventually.of_forall (fun θ hθ => ?_)
  obtain ⟨h0, h1⟩ := mpL_theta_bound c d hd hdc θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

private theorem mpL_dens_inv (c d : ℝ) (hd : 0 < d) (hdc : d ≤ c) (t : ℝ) (ht : 0 < t) :
    ∫ x in Ioo (c - d) (c + d),
        Real.sqrt (((c + d) - x) * (x - (c - d))) / (2 * Real.pi * x) * (x + t)⁻¹ =
      (1 / t) * ((c - Real.sqrt (c ^ 2 - d ^ 2)) / 2 -
        ((c + t) - Real.sqrt ((c + t) ^ 2 - d ^ 2)) / 2) := by
  have hpi := Real.pi_pos
  have h := mpL_theta_form c d hd hdc (fun x => (x + t)⁻¹)
  rw [h]
  have e : ∀ θ ∈ Ioo 0 Real.pi,
      d ^ 2 * Real.sin θ ^ 2 / (2 * Real.pi * (c + d * Real.cos θ)) * (c + d * Real.cos θ + t)⁻¹ =
        (1 / t) * (d ^ 2 * Real.sin θ ^ 2 / (2 * Real.pi * (c + d * Real.cos θ)) -
          d ^ 2 / (2 * Real.pi) * (Real.sin θ ^ 2 / ((c + t) + d * Real.cos θ))) := by
    intro θ hθ
    have hc2 : -1 < Real.cos θ := by
      rw [← Real.cos_pi]; exact Real.strictAntiOn_cos ⟨hθ.1.le, hθ.2.le⟩
        ⟨Real.pi_pos.le, le_refl _⟩ hθ.2
    have h1 : 0 < c + d * Real.cos θ := by nlinarith
    have h2 : 0 < (c + t) + d * Real.cos θ := by linarith
    have h3 : 0 < c + d * Real.cos θ + t := by linarith
    field_simp
    ring
  have hcont : Continuous (fun θ : ℝ =>
      d ^ 2 / (2 * Real.pi) * (Real.sin θ ^ 2 / ((c + t) + d * Real.cos θ))) := by
    refine continuous_const.mul (Continuous.div (by fun_prop) (by fun_prop) (fun θ => ?_))
    have := Real.abs_cos_le_one θ
    nlinarith [abs_le.1 this]
  have hI2 : IntegrableOn (fun θ : ℝ =>
      d ^ 2 / (2 * Real.pi) * (Real.sin θ ^ 2 / ((c + t) + d * Real.cos θ))) (Ioo 0 Real.pi) :=
    (hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [setIntegral_congr_fun measurableSet_Ioo e, integral_const_mul,
    integral_sub (mpL_theta_int1 c d hd hdc) hI2, integral_const_mul,
    mpL_S_Ioo (c + t) d hd (by linarith)]
  have h1 := mpL_theta_form c d hd hdc (fun _ => 1)
  simp only [mul_one] at h1
  have h0 := mpL_dens_one c d hd hdc
  simp only [mul_one] at h0
  rw [← h1, h0]
  field_simp

private theorem mpL_omega_nonneg (r : ℝ) : 0 ≤ isoMPomega r := le_max_right _ _

private theorem mpL_meas_int (r : ℝ) (hr : 0 < r) (f : ℝ → ℝ)
    (hI : IntegrableOn (fun x => Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * x) * f x)
      (Ioo (isoMPa r) (isoMPb r))) :
    Integrable f (isoMP r) ∧ ∫ x, f x ∂(isoMP r) = isoMPomega r * f 0 +
      ∫ x in Ioo (isoMPa r) (isoMPb r),
        Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * x) * f x := by
  have ha := mpL_a_nonneg r hr
  have hφ : Measurable (fun x : ℝ =>
      ENNReal.ofReal (Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * x))) := by
    fun_prop
  have hflt : ∀ᵐ x ∂(volume.restrict (Ioo (isoMPa r) (isoMPb r))),
      ENNReal.ofReal (Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * x)) < ⊤ :=
    Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  have hae : ∀ᵐ x ∂(volume.restrict (Ioo (isoMPa r) (isoMPb r))),
      (ENNReal.ofReal (Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * x))).toReal
        = Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * x) := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hx0 : 0 < x := lt_of_le_of_lt ha hx.1
    exact ENNReal.toReal_ofReal (by positivity)
  have hB : Integrable f ((volume.restrict (Ioo (isoMPa r) (isoMPb r))).withDensity
      (fun x : ℝ => ENNReal.ofReal
        (Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * x)))) := by
    rw [integrable_withDensity_iff_integrable_smul' hφ hflt]
    refine (integrable_congr ?_).2 hI
    filter_upwards [hae] with x hx
    rw [hx, smul_eq_mul]
  have hA : Integrable f (ENNReal.ofReal (isoMPomega r) • Measure.dirac (0:ℝ)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  refine ⟨hA.add_measure hB, ?_⟩
  unfold isoMP
  rw [integral_add_measure hA hB, integral_smul_measure, integral_dirac,
    integral_withDensity_eq_integral_toReal_smul hφ hflt]
  rw [ENNReal.toReal_ofReal (mpL_omega_nonneg r), smul_eq_mul]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx, smul_eq_mul]

private theorem mpL_d_sq (r : ℝ) (hr : 0 < r) : (2 / Real.sqrt r) ^ 2 = 4 / r := by
  rw [div_pow, mpL_sq r hr]; norm_num

private theorem mpL_d_pos (r : ℝ) (hr : 0 < r) : 0 < 2 / Real.sqrt r := by
  have := Real.sqrt_pos.2 hr; positivity

private theorem mpL_d_le (r : ℝ) (hr : 0 < r) : 2 / Real.sqrt r ≤ 1 + 1 / r := by
  have := mpL_a_nonneg r hr
  rw [mpL_a r hr] at this
  linarith

private theorem mpL_disc (r : ℝ) (hr : 0 < r) :
    Real.sqrt ((1 + 1 / r) ^ 2 - (2 / Real.sqrt r) ^ 2) = |1 - 1 / r| := by
  rw [mpL_d_sq r hr]
  have : (1 + 1 / r) ^ 2 - 4 / r = |1 - 1 / r| ^ 2 := by
    rw [sq_abs]; field_simp; ring
  rw [this, Real.sqrt_sq (abs_nonneg _)]

private theorem mpL_wrap (r : ℝ) (hr : 0 < r) (h : ℝ → ℝ) (hh : Measurable h) (M : ℝ)
    (hM : ∀ x ∈ Ioo ((1 + 1 / r) - 2 / Real.sqrt r) ((1 + 1 / r) + 2 / Real.sqrt r), |h x| ≤ M) :
    Integrable h (isoMP r) ∧ ∫ x, h x ∂(isoMP r) = isoMPomega r * h 0 +
      ∫ x in Ioo ((1 + 1 / r) - 2 / Real.sqrt r) ((1 + 1 / r) + 2 / Real.sqrt r),
        Real.sqrt ((((1 + 1 / r) + 2 / Real.sqrt r) - x) * (x - ((1 + 1 / r) - 2 / Real.sqrt r))) /
          (2 * Real.pi * x) * h x := by
  have hI := mpL_dens_int (1 + 1 / r) (2 / Real.sqrt r) (mpL_d_pos r hr) (mpL_d_le r hr) h hh M hM
  have := mpL_meas_int r hr h (by rw [mpL_a r hr, mpL_b r hr]; exact hI)
  rw [mpL_a r hr, mpL_b r hr] at this
  exact this

private theorem mpL_omega_total (r : ℝ) (hr : 0 < r) :
    isoMPomega r + (1 + 1 / r - |1 - 1 / r|) / 2 = 1 := by
  unfold isoMPomega
  rcases le_or_gt 1 r with h | h
  · have h1 : 1 / r ≤ 1 := by rw [div_le_one hr]; exact h
    rw [max_eq_left (by linarith), abs_of_nonneg (by linarith)]; ring
  · have h1 : 1 < 1 / r := by rw [lt_div_iff₀ hr]; linarith
    rw [max_eq_right (by linarith), abs_of_nonpos (by linarith)]; ring

/-- `lem:app-iso-mp`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1444–1463):
```latex
\begin{lemma}[The limiting law]\label{lem:app-iso-mp}
For $r>0$ put
\[
a_r\defeq\frac{(1-\sqrt r)^2}{r},\qquad b_r\defeq\frac{(1+\sqrt r)^2}{r},\qquad
\omega_r\defeq\Big(1-\frac1r\Big)_+ .
\]
The measure
\begin{equation}\label{eqn:app-iso-mp}
\mathsf M_r(\dif x)\defeq\omega_r\,\delta_0(\dif x)+\frac{\sqrt{(b_r-x)(x-a_r)}}{2\pi x}\,\mathbf 1_{(a_r,b_r)}(x)\,\dif x
\end{equation}
is a probability measure with first moment $1/r$. For $t>0$ its transform
$m_r(t)\defeq S_{\mathsf M_r}(-t)$ is the unique positive root $m$ of
\begin{equation}\label{eqn:app-iso-mp-quadratic}
t\,m^2+\Big(t+\frac1r-1\Big)m-1=0 ,
\end{equation}
namely, with $A_r\defeq1+1/r$ and $D_r\defeq2/\sqrt r$,
\begin{equation}\label{eqn:app-iso-mp-transform}
m_r(t)=\frac{1-1/r-t+\sqrt{(A_r+t)^2-D_r^2}}{2t}.
\end{equation}
\end{lemma}
```

`𝖬_r` is `isoMP r` (`ω_r δ₀` plus the density on `(a_r,b_r)`), `m_r(t)` is `isoNegStieltjes (isoMP r) t`. The unique-root clause and the explicit formula are the two displayed claims of the lemma, both kept.
-/
theorem lem_app_iso_mp {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (isoMP r) ∧ Integrable (fun x : ℝ => x) (isoMP r) ∧
      (∫ x, x ∂(isoMP r)) = 1 / r ∧
      ∀ t : ℝ, 0 < t →
        (0 < isoNegStieltjes (isoMP r) t ∧
          t * isoNegStieltjes (isoMP r) t ^ 2 + (t + 1 / r - 1) * isoNegStieltjes (isoMP r) t - 1 = 0) ∧
        (∀ m : ℝ, 0 < m → t * m ^ 2 + (t + 1 / r - 1) * m - 1 = 0 →
          m = isoNegStieltjes (isoMP r) t) ∧
        isoNegStieltjes (isoMP r) t =
          (1 - 1 / r - t + Real.sqrt ((1 + 1 / r + t) ^ 2 - (2 / Real.sqrt r) ^ 2)) / (2 * t) := by
  have hd := mpL_d_pos r hr
  have hdc := mpL_d_le r hr
  have hW := mpL_omega_total r hr
  -- constant function
  obtain ⟨hint1, hval1⟩ := mpL_wrap r hr (fun _ => 1) measurable_const 1 (fun x _ => by simp)
  have hd1 := mpL_dens_one (1 + 1 / r) (2 / Real.sqrt r) hd hdc
  rw [mpL_disc r hr] at hd1
  simp only [mul_one] at hval1 hd1
  rw [hd1] at hval1
  have hprob : IsProbabilityMeasure (isoMP r) := by
    refine ⟨?_⟩
    have : (isoMP r Set.univ).toReal = 1 := by
      have h2 : ∫ x, (1:ℝ) ∂(isoMP r) = (isoMP r Set.univ).toReal := by simp [Measure.real]
      rw [h2] at hval1
      rw [hval1]; linarith
    exact (ENNReal.toReal_eq_one_iff _).1 this
  -- first moment
  obtain ⟨hint2, hval2⟩ := mpL_wrap r hr (fun x => x) measurable_id ((1 + 1 / r) + 2 / Real.sqrt r)
    (fun x hx => by
      rw [abs_of_pos (lt_of_le_of_lt (by linarith) hx.1)]; exact hx.2.le)
  have hd2 := mpL_dens_id (1 + 1 / r) (2 / Real.sqrt r) hd hdc
  rw [hd2, mpL_d_sq r hr] at hval2
  refine ⟨hprob, hint2, ?_, ?_⟩
  · rw [hval2]; simp; ring
  intro t ht
  obtain ⟨hint3, hval3⟩ := mpL_wrap r hr (fun x => (x + t)⁻¹) (by fun_prop) (1 / t)
    (fun x hx => by
      have hx0 : 0 < x := lt_of_le_of_lt (by linarith) hx.1
      rw [abs_of_pos (by positivity)]
      rw [one_div]; exact inv_anti₀ ht (by linarith))
  have hd3 := mpL_dens_inv (1 + 1 / r) (2 / Real.sqrt r) hd hdc t ht
  rw [mpL_disc r hr] at hd3
  rw [hd3] at hval3
  have hm : isoNegStieltjes (isoMP r) t =
      (1 - 1 / r - t + Real.sqrt ((1 + 1 / r + t) ^ 2 - (2 / Real.sqrt r) ^ 2)) / (2 * t) := by
    unfold isoNegStieltjes
    rw [hval3]
    generalize isoMPomega r = w at hW ⊢
    generalize |1 - 1 / r| = A at hW ⊢
    generalize Real.sqrt ((1 + 1 / r + t) ^ 2 - (2 / Real.sqrt r) ^ 2) = R
    generalize 1 / r = u at hW ⊢
    field_simp
    linear_combination (2 * t) * hW
  have hds := mpL_d_sq r hr
  have hu : 0 < 1 / r := by positivity
  have harg : 0 < (1 + 1 / r + t) ^ 2 - (2 / Real.sqrt r) ^ 2 := by
    nlinarith
  set R := Real.sqrt ((1 + 1 / r + t) ^ 2 - (2 / Real.sqrt r) ^ 2) with hRdef
  have hRpos : 0 < R := Real.sqrt_pos.2 harg
  have hR2 : R ^ 2 = (1 + 1 / r + t) ^ 2 - (2 / Real.sqrt r) ^ 2 := Real.sq_sqrt harg.le
  have hu4 : 4 / r = 4 * (1 / r) := by ring
  set L := 1 - 1 / r - t with hL
  have hR2' : R ^ 2 = L ^ 2 + 4 * t := by
    rw [hR2, hds, hu4, hL]; ring
  have hLR : 0 < L + R := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  have hmpos : 0 < (L + R) / (2 * t) := by positivity
  have hquad : t * ((L + R) / (2 * t)) ^ 2 + (t + 1 / r - 1) * ((L + R) / (2 * t)) - 1 = 0 := by
    have : t + 1 / r - 1 = -L := by rw [hL]; ring
    rw [this]
    field_simp
    nlinarith [hR2']
  rw [hm]
  refine ⟨⟨hmpos, hquad⟩, ?_, rfl⟩
  intro m hmp hmq
  set m0 := (L + R) / (2 * t)
  have hfac : (m - m0) * (t * (m + m0) + (t + 1 / r - 1)) = 0 := by
    linear_combination hmq - hquad
  rcases mul_eq_zero.1 hfac with h | h
  · linarith
  · exfalso
    have : t + 1 / r - 1 = -(t * (m + m0)) := by linarith
    rw [this] at hmq
    have e : t * m * m0 + 1 = 0 := by linear_combination (-1 : ℝ) * hmq
    have hp : 0 < t * m * m0 := by positivity
    linarith

/-! ## Reciprocity -/
/-! ### Helpers for `prop_app_iso_reciprocity_ii` -/
private theorem rcp_cov_Ioo (c a b : ℝ) (hc : 0 < c) (g : ℝ → ℝ) :
    ∫ x in Ioo (c * a) (c * b), g x = c * ∫ y in Ioo a b, g (c * y) := by
  rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioo]
  have key := Measure.integral_comp_mul_left ((Ioo (c * a) (c * b)).indicator g) c
  have h1 : ∀ y : ℝ, (Ioo a b).indicator (fun y => g (c * y)) y =
      (Ioo (c * a) (c * b)).indicator g (c * y) := by
    intro y
    by_cases h : a < y ∧ y < b
    · have h' : c * a < c * y ∧ c * y < c * b :=
        ⟨mul_lt_mul_of_pos_left h.1 hc, mul_lt_mul_of_pos_left h.2 hc⟩
      simp [Set.indicator, h, h']
    · have h' : ¬ (c * a < c * y ∧ c * y < c * b) := by
        rintro ⟨h1, h2⟩
        exact h ⟨lt_of_mul_lt_mul_left h1 hc.le, lt_of_mul_lt_mul_left h2 hc.le⟩
      simp [Set.indicator, h, h']
  simp only [h1]
  rw [key, abs_of_pos (inv_pos.2 hc), smul_eq_mul]
  field_simp

private theorem rcp_rpow (r : ℝ) (hr : 0 < r) : r ^ (3 / 2 : ℝ) = r * Real.sqrt r := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hr, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

private theorem rcp_mpa_inv (r : ℝ) (hr : 0 < r) :
    isoMPa (1 / r) = r * isoMPa r ∧ isoMPb (1 / r) = r * isoMPb r := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ r = s ^ 2 :=
    ⟨Real.sqrt r, Real.sqrt_pos.2 hr, (Real.sq_sqrt hr.le).symm⟩
  have e : Real.sqrt (1 / s ^ 2) = 1 / s := by
    rw [show (1 : ℝ) / s ^ 2 = (1 / s) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  unfold isoMPa isoMPb
  rw [e, Real.sqrt_sq hs.le]
  constructor <;> field_simp <;> ring

private theorem rcp_J_formula (r : ℝ) (hr : 0 < r) :
    isoJr r = ∫ x in Ioo (isoMPa r) (isoMPb r),
      Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * x) * Real.sqrt x := by
  have ha := mpL_a r hr
  have hb := mpL_b r hr
  have hI := mpL_dens_int (1 + 1 / r) (2 / Real.sqrt r) (mpL_d_pos r hr) (mpL_d_le r hr)
    Real.sqrt Real.continuous_sqrt.measurable (Real.sqrt ((1 + 1 / r) + 2 / Real.sqrt r))
    (fun x hx => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (le_of_lt hx.2))
  have hI' : IntegrableOn (fun x : ℝ =>
      Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * x) * Real.sqrt x)
      (Ioo (isoMPa r) (isoMPb r)) := by
    rw [ha, hb]; exact hI
  have h := mpL_meas_int r hr Real.sqrt hI'
  unfold isoJr
  rw [h.2]
  simp

private theorem rcp_part1 (r : ℝ) (hr : 0 < r) :
    isoJr (1 / r) = r ^ (3 / 2 : ℝ) * isoJr r := by
  obtain ⟨hA, hB⟩ := rcp_mpa_inv r hr
  rw [rcp_J_formula (1 / r) (by positivity), rcp_J_formula r hr, hA, hB,
    rcp_cov_Ioo r _ _ hr, rcp_rpow r hr]
  have hint : ∫ y in Ioo (isoMPa r) (isoMPb r),
      Real.sqrt ((r * isoMPb r - r * y) * (r * y - r * isoMPa r)) / (2 * Real.pi * (r * y))
        * Real.sqrt (r * y)
      = Real.sqrt r * ∫ y in Ioo (isoMPa r) (isoMPb r),
        Real.sqrt ((isoMPb r - y) * (y - isoMPa r)) / (2 * Real.pi * y) * Real.sqrt y := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo (fun y hy => ?_)
    have hy0 : 0 < y := lt_of_le_of_lt (mpL_a_nonneg r hr) hy.1
    have e1 : (r * isoMPb r - r * y) * (r * y - r * isoMPa r)
        = r ^ 2 * ((isoMPb r - y) * (y - isoMPa r)) := by ring
    rw [e1, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le, Real.sqrt_mul hr.le y]
    field_simp
  rw [hint]
  ring


/-- `prop:app-iso-reciprocity`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1589–1608):
```latex
\begin{proposition}[Reciprocity]\label{prop:app-iso-reciprocity}
\begin{enumerate}[label=(\roman*)]
\item Let $(\mathfrak m_{\mathrm{out}},\mathfrak m_{\mathrm{in}})$ be the isotropic measure
pair at $(\gin,\gout)$, let
$b=\gin\gout$, and let $\mathsf P$ be the image of $\mathfrak m_{\mathrm{out}}/\gout$
under $\lambda\mapsto\lambda/\gout$. Then $\mathsf P$ is the image of
$\widehat{\mathfrak m}_b/\gout$ under $x\mapsto\gin x$. If $\widehat{\mathfrak m}_b$
has a density $\widehat\rho$, then $\mathsf P$ has the density
$\widehat\rho(x/\gin)/(\gin\gout)$. Its transform and the constant are
\[
S_{\mathsf P}(-t)=\sigma(-\gout t)=\frac{1}{\gin\gout}\,S_{\widehat{\mathfrak m}_b}\Big(-\frac{t}{\gin}\Big),\qquad
C(\gin,\gout)=\frac{\sqrt{\gout}}{\sqrt2\,\gin}\int\sqrt x\,\mathsf P(\dif x).
\]
\item For every $r>0$, $J_{1/r}=r^{3/2}J_r$, and the right side of
\cref{eqn:app-iso-small} is unchanged when $\gin$ and $\gout$ are exchanged
(with $r$ replaced by $1/r$).
\item For every $r>0$ the endpoint pairs $\{(1\pm\sqrt r)^2/r\}$ and
$\{(1\pm1/\sqrt r)^2\}$ are equal.
\end{enumerate}
\end{proposition}
```

Part (ii) only. Part (i) is owned by L-F.6 (card §3, §5 item 6). The `r ↦ 1/r` exchange is written with `γin/γout` and `γout/γin`.
-/
theorem prop_app_iso_reciprocity_ii :
    (∀ r : ℝ, 0 < r → isoJr (1 / r) = r ^ (3 / 2 : ℝ) * isoJr r) ∧
      (∀ γin γout : ℝ, 0 < γin → 0 < γout →
        γout / γin * isoJr (γout / γin) / Real.sqrt (2 * γout) =
          γin / γout * isoJr (γin / γout) / Real.sqrt (2 * γin)) := by
  refine ⟨fun r hr => rcp_part1 r hr, ?_⟩
  intro γin γout hγin hγout
  have hr : 0 < γout / γin := div_pos hγout hγin
  have e : γin / γout = 1 / (γout / γin) := (one_div_div _ _).symm
  have h2 : Real.sqrt (2 * γout) = Real.sqrt (γout / γin) * Real.sqrt (2 * γin) := by
    rw [← Real.sqrt_mul hr.le]
    congr 1
    field_simp
  rw [e, rcp_part1 _ hr, rcp_rpow _ hr, h2]
  have hs := Real.sqrt_pos.2 hr
  have hA := Real.sqrt_pos.2 (show (0:ℝ) < 2 * γin by positivity)
  have hs2 := Real.sq_sqrt hr.le
  generalize γout / γin = r at *
  generalize Real.sqrt r = s at *
  generalize isoJr r = J at *
  generalize Real.sqrt (2 * γin) = A at *
  rw [← hs2]
  field_simp

/-- `prop:app-iso-reciprocity`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1589–1608):
```latex
\begin{proposition}[Reciprocity]\label{prop:app-iso-reciprocity}
\begin{enumerate}[label=(\roman*)]
\item Let $(\mathfrak m_{\mathrm{out}},\mathfrak m_{\mathrm{in}})$ be the isotropic measure
pair at $(\gin,\gout)$, let
$b=\gin\gout$, and let $\mathsf P$ be the image of $\mathfrak m_{\mathrm{out}}/\gout$
under $\lambda\mapsto\lambda/\gout$. Then $\mathsf P$ is the image of
$\widehat{\mathfrak m}_b/\gout$ under $x\mapsto\gin x$. If $\widehat{\mathfrak m}_b$
has a density $\widehat\rho$, then $\mathsf P$ has the density
$\widehat\rho(x/\gin)/(\gin\gout)$. Its transform and the constant are
\[
S_{\mathsf P}(-t)=\sigma(-\gout t)=\frac{1}{\gin\gout}\,S_{\widehat{\mathfrak m}_b}\Big(-\frac{t}{\gin}\Big),\qquad
C(\gin,\gout)=\frac{\sqrt{\gout}}{\sqrt2\,\gin}\int\sqrt x\,\mathsf P(\dif x).
\]
\item For every $r>0$, $J_{1/r}=r^{3/2}J_r$, and the right side of
\cref{eqn:app-iso-small} is unchanged when $\gin$ and $\gout$ are exchanged
(with $r$ replaced by $1/r$).
\item For every $r>0$ the endpoint pairs $\{(1\pm\sqrt r)^2/r\}$ and
$\{(1\pm1/\sqrt r)^2\}$ are equal.
\end{enumerate}
\end{proposition}
```

Part (iii). Equality of the endpoint pairs as sets `Set ℝ`.
-/
theorem prop_app_iso_reciprocity_iii :
    ∀ r : ℝ, 0 < r →
      ({(1 - Real.sqrt r) ^ 2 / r, (1 + Real.sqrt r) ^ 2 / r} : Set ℝ) =
        {(1 - 1 / Real.sqrt r) ^ 2, (1 + 1 / Real.sqrt r) ^ 2} := by
  intro r hr
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ r = s ^ 2 :=
    ⟨Real.sqrt r, Real.sqrt_pos.2 hr, (Real.sq_sqrt hr.le).symm⟩
  rw [Real.sqrt_sq hs.le]
  have h1 : (1 - 1 / s) ^ 2 = (1 - s) ^ 2 / s ^ 2 := by
    field_simp
    ring
  have h2 : (1 + 1 / s) ^ 2 = (1 + s) ^ 2 / s ^ 2 := by
    field_simp
    ring
  rw [h1, h2]

/-! ## Large aspect ratios -/

/-! ## Pair-free helpers for the C asymptotics (card §5 L-F.5, §6.8)

These are not declarations of record. They give the scalar asymptotics that the measure-pair
theorems `thm:app-iso-small` and `thm:app-iso-large` (L-F.6) reuse without the pair. -/

/-! ## Small aspect ratios with momentum -/

/-! ### Private helpers for `thm_app_iso_small_momentum_i` (task P-F.5.P2) -/

section SmallMomentumHelpers

open Muon.DetEquiv (rW Lw Fw J)


private theorem pf_link_c {c : ℝ} (hc : 0 < c) : IsIsoLink (fun q : ℝ => c * q) :=
  ⟨(continuous_const.mul continuous_id).continuousOn,
    fun _ _ _ _ hab => by simpa using mul_lt_mul_of_pos_left hab hc, by simp⟩

private theorem pf_link_id : IsIsoLink (fun q : ℝ => q) :=
  ⟨continuous_id.continuousOn, fun _ _ _ _ hab => hab, rfl⟩

private lemma pf_emaW_weightSeq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Muon.DetEquiv.WeightSeq (Muon.emaW β) := by
  refine ⟨fun j => ?_, ?_, 0, ?_⟩
  · unfold Muon.emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  · unfold Muon.emaW
    exact (summable_geometric_of_lt_one hβ0 hβ1).mul_left _
  · unfold Muon.emaW
    rw [pow_zero, mul_one]
    exact (by linarith : (0:ℝ) < 1 - β).ne'

private lemma pf_link_beta {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    IsIsoLink (rW (Muon.emaW β)) := by
  have hw := pf_emaW_weightSeq hβ0 hβ1
  refine ⟨ContinuousOn.mul continuousOn_id (Muon.DetEquiv.Fw_admissible hw).contOn,
    (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.1,
    (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.2.1⟩

/-- Root scaling. -/
private lemma pf_root_scale {c γin γout s : ℝ} (hc : 0 < c) (hγin : 0 < γin) (hγout : 0 < γout)
    (hs : 0 < s) :
    isoRoot (fun q : ℝ => c * q) γin γout s = isoYroot γin γout (s / c) / c := by
  have hsc : 0 < s / c := div_pos hs hc
  obtain ⟨hD, hG⟩ := (lem_app_iso_comparison_i pf_link_id hγin hγout).2.2.2.1 (s / c) hsc
  obtain ⟨_, hex, _⟩ := lem_app_iso_comparison_i (pf_link_c hc) hγin hγout
  obtain ⟨q0, _, hq0⟩ := hex s hs
  have h1 := (lem_app_iso_comparison_i (pf_link_c hc) hγin hγout).2.2.2.1 s hs
  have h2 : isoYroot γin γout (s / c) / c ∈ isoDr (fun q : ℝ => c * q) γin γout ∧
      isoG (fun q : ℝ => c * q) γin γout s (isoYroot γin γout (s / c) / c) = 0 := by
    unfold isoYroot
    unfold isoDr at hD ⊢
    unfold isoG at hG ⊢
    simp only [mem_ofPred_eq] at hD ⊢
    refine ⟨⟨div_nonneg hD.1 hc.le, ?_⟩, ?_⟩
    · rw [mul_div_cancel₀ _ hc.ne']; exact hD.2
    · rw [mul_div_cancel₀ _ hc.ne']
      have : s * (isoRoot (fun q : ℝ => q) γin γout (s / c) / c) =
          (s / c) * isoRoot (fun q : ℝ => q) γin γout (s / c) := by field_simp
      rw [this]; exact hG
  rw [hq0 _ h1, ← hq0 _ h2]

private lemma pf_Y_scale {t γin γout s : ℝ} (ht : 0 < t) (hγin : 0 < γin) (hγout : 0 < γout)
    (hs : 0 < s) :
    isoYroot (t * γin) (t * γout) (t * s) = t * isoYroot γin γout s := by
  have hts : 0 < t * s := mul_pos ht hs
  obtain ⟨hD, hG⟩ := (lem_app_iso_comparison_i pf_link_id hγin hγout).2.2.2.1 s hs
  obtain ⟨_, hex, _⟩ := lem_app_iso_comparison_i pf_link_id (mul_pos ht hγin) (mul_pos ht hγout)
  obtain ⟨q0, _, hq0⟩ := hex (t * s) hts
  have h1 := (lem_app_iso_comparison_i pf_link_id (mul_pos ht hγin) (mul_pos ht hγout)).2.2.2.1
    (t * s) hts
  have h2 : t * isoYroot γin γout s ∈ isoDr (fun q : ℝ => q) (t * γin) (t * γout) ∧
      isoG (fun q : ℝ => q) (t * γin) (t * γout) (t * s) (t * isoYroot γin γout s) = 0 := by
    unfold isoYroot
    unfold isoDr at hD ⊢
    unfold isoG at hG ⊢
    simp only [mem_ofPred_eq] at hD ⊢
    refine ⟨⟨mul_nonneg ht.le hD.1, ?_⟩, ?_⟩
    · rw [← mul_min_of_nonneg _ _ ht.le]; exact mul_lt_mul_of_pos_left hD.2 ht
    · have : t * s * (t * isoRoot (fun q : ℝ => q) γin γout s) -
          (t * γout - t * isoRoot (fun q : ℝ => q) γin γout s) *
            (t * γin - t * isoRoot (fun q : ℝ => q) γin γout s) =
          t ^ 2 * (s * isoRoot (fun q : ℝ => q) γin γout s -
            (γout - isoRoot (fun q : ℝ => q) γin γout s) *
              (γin - isoRoot (fun q : ℝ => q) γin γout s)) := by ring
      simp only at hG ⊢
      rw [this, hG, mul_zero]
  unfold isoYroot at h2 ⊢
  rw [hq0 _ h1, ← hq0 _ h2]



private lemma pf_J_lower {x : ℝ} (hx : 0 ≤ x) : 1 - 3 * x ≤ J x := by
  rcases hx.eq_or_lt with h | h
  · rw [← h]
    have : J 0 = 1 := by
      unfold J
      simp only [zero_mul, add_zero, div_one]
      exact Muon.Foundations.gaussian_moment_two
    rw [this]; norm_num
  · have h3 := (lem_app_iso_gaussian_iii x h).2
    have : isoPhi x = x * J x := rfl
    rw [this] at h3
    by_contra hlt
    push Not at hlt
    nlinarith [mul_lt_mul_of_pos_left hlt h]

private lemma pf_summable_pow {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun j : ℕ => Muon.emaW β j ^ k) := by
  have key : ∀ j : ℕ, Muon.emaW β j ^ k = (1 - β) ^ k * (β ^ k) ^ j := by
    intro j
    unfold Muon.emaW
    rw [mul_pow, pow_right_comm β j k]
  simp only [key]
  exact (summable_geometric_of_lt_one (pow_nonneg hβ0 k) (pow_lt_one₀ hβ0 hβ1 (by omega))).mul_left _

private lemma pf_emaW_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (j : ℕ) :
    0 ≤ Muon.emaW β j := by
  unfold Muon.emaW
  exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)

private lemma pf_J_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ J x := by
  unfold J
  refine integral_nonneg (fun g => div_nonneg (sq_nonneg g) ?_)
  nlinarith [mul_nonneg hx (sq_nonneg g)]

private lemma pf_J_le_one {x : ℝ} (hx : 0 ≤ x) : J x ≤ 1 := by
  rcases hx.eq_or_lt with h | h
  · rw [← h]
    unfold J
    simp only [zero_mul, add_zero, div_one]
    exact Muon.Foundations.gaussian_moment_two.le
  · exact ((lem_app_iso_weights_iii).1 x h).trans (min_le_left _ _)

private lemma pf_Fw_lower {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    Muon.sPow β 2 - 3 * Muon.sPow β 4 * q ≤ Fw (Muon.emaW β) q := by
  have h2 := pf_summable_pow hβ0 hβ1 (k := 2) (by norm_num)
  have h4 := pf_summable_pow hβ0 hβ1 (k := 4) (by norm_num)
  have hterm : ∀ j : ℕ, Muon.emaW β j ^ 2 - 3 * q * Muon.emaW β j ^ 4 ≤
      Muon.emaW β j ^ 2 * J (Muon.emaW β j ^ 2 * q) := by
    intro j
    have := pf_J_lower (mul_nonneg (sq_nonneg (Muon.emaW β j)) hq)
    nlinarith [sq_nonneg (Muon.emaW β j)]
  have hsum : Summable (fun j : ℕ => Muon.emaW β j ^ 2 * J (Muon.emaW β j ^ 2 * q)) :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (sq_nonneg _) (pf_J_nonneg (mul_nonneg (sq_nonneg _) hq)))
      (fun j => mul_le_of_le_one_right (sq_nonneg _) (pf_J_le_one (mul_nonneg (sq_nonneg _) hq)))
      h2
  have hlow : Summable (fun j : ℕ => Muon.emaW β j ^ 2 - 3 * q * Muon.emaW β j ^ 4) :=
    h2.sub (h4.mul_left _)
  have := Summable.tsum_le_tsum hterm hlow hsum
  rw [Summable.tsum_sub h2 (h4.mul_left _), tsum_mul_left] at this
  unfold Fw
  unfold Muon.sPow
  linarith

private lemma pf_Lw_lower {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    1 - 3 * Muon.sPow β 3 * q ≤ Lw (Muon.emaW β) q := by
  have h1 := pf_summable_pow hβ0 hβ1 (k := 1) (by norm_num)
  have h3 := pf_summable_pow hβ0 hβ1 (k := 3) (by norm_num)
  have hw0 := pf_emaW_nonneg hβ0 hβ1
  have hterm : ∀ j : ℕ, Muon.emaW β j - 3 * q * Muon.emaW β j ^ 3 ≤
      Muon.emaW β j * J (Muon.emaW β j ^ 2 * q) := by
    intro j
    have := pf_J_lower (mul_nonneg (sq_nonneg (Muon.emaW β j)) hq)
    have := mul_le_mul_of_nonneg_left this (hw0 j)
    nlinarith
  have hsum : Summable (fun j : ℕ => Muon.emaW β j * J (Muon.emaW β j ^ 2 * q)) :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (hw0 j) (pf_J_nonneg (mul_nonneg (sq_nonneg _) hq)))
      (fun j => mul_le_of_le_one_right (hw0 j) (pf_J_le_one (mul_nonneg (sq_nonneg _) hq)))
      (by simpa using h1)
  have h1' : Summable (fun j : ℕ => Muon.emaW β j) := by simpa using h1
  have hlow : Summable (fun j : ℕ => Muon.emaW β j - 3 * q * Muon.emaW β j ^ 3) :=
    h1'.sub (h3.mul_left _)
  have := Summable.tsum_le_tsum hterm hlow hsum
  rw [Summable.tsum_sub h1' (h3.mul_left _), tsum_mul_left, tsum_emaW hβ0 hβ1] at this
  unfold Lw
  unfold Muon.sPow
  linarith

private lemma pf_sPow_consts {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    0 < Muon.sPow β 2 ∧ Muon.sPow β 4 ≤ (1 - β ^ 2) * Muon.sPow β 2 ^ 2 ∧
      Muon.sPow β 3 ≤ (1 - β ^ 2) * Muon.sPow β 2 := by
  have hb : 0 < 1 - β := by linarith
  have hb2 : β ^ 2 < 1 := by nlinarith
  have h2 := Muon.sPow_eq hβ0 hβ1 (p := 2) le_rfl
  have h3 := Muon.sPow_eq hβ0 hβ1 (p := 3) (by norm_num)
  have h4 := Muon.sPow_eq hβ0 hβ1 (p := 4) (by norm_num)
  have hb3 : β ^ 3 ≤ β := by nlinarith [pow_nonneg hβ0 2, pow_nonneg hβ0 3]
  have hb4 : β ^ 4 ≤ β ^ 2 := by nlinarith [pow_nonneg hβ0 2]
  have hd2 : 0 < 1 - β ^ 2 := by linarith
  have hd3 : 0 < 1 - β ^ 3 := by linarith
  have hd4 : 0 < 1 - β ^ 4 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [h2]; positivity
  · rw [h4, h2, div_pow, mul_div_assoc', div_le_div_iff₀ hd4 (by positivity)]
    have : (1 - β ^ 2) ^ 2 = (1 - β ^ 2) * (1 - β ^ 2) := by ring
    nlinarith [pow_pos hb 4, mul_nonneg (pow_pos hb 4).le (sub_nonneg.2 hb4), mul_pos (pow_pos hb 4) hd2]
  · rw [h3, h2, mul_div_assoc', div_le_div_iff₀ hd3 hd2]
    nlinarith [pow_pos hb 3, mul_nonneg (pow_pos hb 3).le (sub_nonneg.2 hb3), pow_pos hb 2]


private lemma pf_pointwise {β γin γout S ε : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hS : S = Muon.sPow β 2)
    (hε : ε = 6 * min γin γout * (1 - β ^ 2)) (hε2 : ε ≤ 1 / 2) {s : ℝ} (hs : 0 < s) :
    0 ≤ isoGb β γin γout s ∧
    (1 - ε) * (isoYroot γin γout (s / S) / S) ≤ isoGb β γin γout s ∧
    isoGb β γin γout s ≤ isoYroot γin γout (s / (S * (1 - ε))) / (S * (1 - ε)) ∧
    isoGb β γin γout s ≤ 2 * min γin γout / S ∧
    s * isoGb β γin γout s ≤ γin * γout := by
  obtain ⟨hSpos, hS4, hS3⟩ := pf_sPow_consts hβ0 hβ1
  rw [← hS] at hSpos hS4 hS3
  have hm : 0 < min γin γout := lt_min hγin hγout
  have hb2 : 0 ≤ 1 - β ^ 2 := by nlinarith
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hc : 0 < S * (1 - ε) := mul_pos hSpos (by linarith)
  have hS4nn : 0 ≤ Muon.sPow β 4 :=
    tsum_nonneg (fun j => pow_nonneg (pf_emaW_nonneg hβ0 hβ1 j) 4)
  have hS3nn : 0 ≤ Muon.sPow β 3 :=
    tsum_nonneg (fun j => pow_nonneg (pf_emaW_nonneg hβ0 hβ1 j) 3)
  have hlink := pf_link_beta hβ0 hβ1
  have hw := pf_emaW_weightSeq hβ0 hβ1
  set q := qIso β γin γout s with hqdef
  have hspec := (lem_app_iso_comparison_i hlink hγin hγout).2.2.2.1 s hs
  have hqD : q ∈ isoDr (rW (Muon.emaW β)) γin γout := hspec.1
  have hqG : isoG (rW (Muon.emaW β)) γin γout s q = 0 := hspec.2
  obtain ⟨hq0, hrq⟩ : 0 ≤ q ∧ rW (Muon.emaW β) q < min γin γout := hqD
  unfold isoG at hqG
  have hFpos := (Muon.DetEquiv.Fw_admissible hw).pos
  have hFle := (lem_app_iso_weights_v hβ0 hβ1).1
  have hLle := (lem_app_iso_weights_v hβ0 hβ1).2.1
  have hrq0 : 0 ≤ rW (Muon.emaW β) q := by
    unfold rW; exact mul_nonneg hq0 (hFpos q hq0).le
  -- the product bound
  have hprod : s * q ≤ γin * γout := by
    have h1 : 0 < γout - rW (Muon.emaW β) q := by linarith [min_le_right γin γout]
    have h2 : 0 < γin - rW (Muon.emaW β) q := by linarith [min_le_left γin γout]
    have : s * q = (γout - rW (Muon.emaW β) q) * (γin - rW (Muon.emaW β) q) := by linarith
    rw [this, mul_comm γin γout]
    exact mul_le_mul (by linarith) (by linarith) h2.le hγout.le
  -- a priori bound
  have hqbar : q < 2 * min γin γout / S := by
    by_contra hge
    push Not at hge
    set qb := 2 * min γin γout / S with hqb
    have hqb0 : 0 ≤ qb := by positivity
    have hmono := (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.1
    have h1 : rW (Muon.emaW β) qb ≤ rW (Muon.emaW β) q :=
      hmono.monotoneOn (Set.mem_Ici.mpr hqb0) (Set.mem_Ici.mpr hq0) hge
    have h2 := pf_Fw_lower hβ0 hβ1 hqb0
    have h3 : S * qb = 2 * min γin γout := by rw [hqb]; field_simp
    have h4 : 3 * Muon.sPow β 4 * qb * qb ≤ min γin γout := by
      have : 3 * Muon.sPow β 4 * qb * qb ≤ 3 * ((1 - β ^ 2) * S ^ 2) * qb * qb := by
        have := mul_le_mul_of_nonneg_right hS4 (mul_nonneg hqb0 hqb0)
        nlinarith [mul_nonneg hqb0 hqb0]
      have h5 : S ^ 2 * (qb * qb) = (2 * min γin γout) ^ 2 := by rw [← h3]; ring
      have h6 : 3 * ((1 - β ^ 2) * S ^ 2) * qb * qb = 3 * (1 - β ^ 2) * (2 * min γin γout) ^ 2 := by
        rw [← h5]; ring
      have h7 : 3 * (1 - β ^ 2) * (2 * min γin γout) ^ 2 = 2 * min γin γout * ε := by
        rw [hε]; ring
      have h8 : 3 * Muon.sPow β 4 * qb * qb ≤ 2 * min γin γout * ε := by
        rw [← h7, ← h6]; exact this
      have h9 := mul_le_mul_of_nonneg_left hε2 hm.le
      linarith
    have h8 : rW (Muon.emaW β) qb ≥ min γin γout := by
      unfold rW
      have := mul_le_mul_of_nonneg_left h2 hqb0
      nlinarith
    linarith
  -- sandwich
  have hup : isoRoot (fun x : ℝ => S * x) γin γout s ≤ q := by
    have := lem_app_iso_comparison_ii (r₁ := rW (Muon.emaW β)) (r₂ := fun x : ℝ => S * x)
      hlink (pf_link_c hSpos) hγin hγout hs (Or.inl (by
        show rW (Muon.emaW β) q ≤ S * q
        unfold rW
        have := hFle q hq0
        rw [hS]
        nlinarith))
    exact this
  have hrlow : S * (1 - ε) * q ≤ rW (Muon.emaW β) q := by
    have h2 := pf_Fw_lower hβ0 hβ1 hq0
    have h3 : 3 * Muon.sPow β 4 * q ≤ ε * S := by
      have h5 : 3 * Muon.sPow β 4 * q ≤ 3 * Muon.sPow β 4 * (2 * min γin γout / S) :=
        mul_le_mul_of_nonneg_left hqbar.le (by positivity)
      have h6 : 3 * Muon.sPow β 4 * (2 * min γin γout / S) ≤
          3 * ((1 - β ^ 2) * S ^ 2) * (2 * min γin γout / S) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
      have h7 : 3 * ((1 - β ^ 2) * S ^ 2) * (2 * min γin γout / S) = ε * S := by
        rw [hε]; field_simp; ring
      linarith
    unfold rW
    have := mul_le_mul_of_nonneg_left h2 hq0
    nlinarith
  have hlow : q ≤ isoRoot (fun x : ℝ => S * (1 - ε) * x) γin γout s := by
    have := lem_app_iso_comparison_ii (r₁ := fun x : ℝ => S * (1 - ε) * x)
      (r₂ := rW (Muon.emaW β)) (pf_link_c hc) hlink hγin hγout hs
      (Or.inr (by
        show S * (1 - ε) * q ≤ rW (Muon.emaW β) q
        exact hrlow))
    exact this
  rw [pf_root_scale hSpos hγin hγout hs] at hup
  rw [pf_root_scale hc hγin hγout hs] at hlow
  have hLlow := pf_Lw_lower hβ0 hβ1 hq0
  have hL3 : 1 - ε ≤ Lw (Muon.emaW β) q := by
    have h6 : 3 * Muon.sPow β 3 * q ≤ ε := by
      have h5 : 3 * Muon.sPow β 3 * q ≤ 3 * Muon.sPow β 3 * (2 * min γin γout / S) :=
        mul_le_mul_of_nonneg_left hqbar.le (by positivity)
      have h6 : 3 * Muon.sPow β 3 * (2 * min γin γout / S) ≤
          3 * ((1 - β ^ 2) * S) * (2 * min γin γout / S) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
      have h7 : 3 * ((1 - β ^ 2) * S) * (2 * min γin γout / S) = ε := by
        rw [hε]; field_simp; ring
      linarith
    linarith
  have hg : isoGb β γin γout s = q * Lw (Muon.emaW β) q := rfl
  have hYS : 0 ≤ isoYroot γin γout (s / S) / S := by
    have : 0 ≤ isoRoot (fun x : ℝ => S * x) γin γout s :=
      (show s = s from rfl) ▸ ((lem_app_iso_comparison_i (pf_link_c hSpos) hγin hγout).2.2.2.1 s hs).1.1
    rw [pf_root_scale hSpos hγin hγout hs] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hg]; exact mul_nonneg hq0 (by linarith)
  · rw [hg]
    nlinarith [mul_le_mul_of_nonneg_left hL3 hq0, mul_le_mul_of_nonneg_left hup (by linarith : (0:ℝ) ≤ 1 - ε)]
  · rw [hg]
    calc q * Lw (Muon.emaW β) q ≤ q * 1 := mul_le_mul_of_nonneg_left (hLle q hq0) hq0
      _ ≤ _ := by linarith
  · rw [hg]
    calc q * Lw (Muon.emaW β) q ≤ q * 1 := mul_le_mul_of_nonneg_left (hLle q hq0) hq0
      _ ≤ _ := by linarith
  · rw [hg]
    calc s * (q * Lw (Muon.emaW β) q) ≤ s * (q * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hLle q hq0) hq0) hs.le
      _ ≤ _ := by linarith

private lemma pf_int_of_bounds {f : ℝ → ℝ} {M P : ℝ} (hM : 0 ≤ M) (hP : 0 ≤ P)
    (hmeas : AEMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    (h0 : ∀ w : ℝ, 0 < w → 0 ≤ f w) (h1 : ∀ w : ℝ, 0 < w → f w ≤ M)
    (h2 : ∀ w : ℝ, 0 < w → w ^ 2 * f w ≤ P) : IntegrableOn f (Ioi (0 : ℝ)) := by
  have hint : IntegrableOn (fun w : ℝ => 2 * (M + P) * (1 + w ^ 2)⁻¹) (Ioi (0 : ℝ)) :=
    (integrable_inv_one_add_sq.const_mul (2 * (M + P))).integrableOn
  refine Integrable.mono' hint hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  have hw' : 0 < w := hw
  rw [Real.norm_of_nonneg (h0 w hw')]
  have hpos : 0 < 1 + w ^ 2 := by positivity
  rw [mul_comm, ← div_eq_inv_mul, le_div_iff₀ hpos] at *
  by_cases hc : w ^ 2 ≤ 1
  · have := h1 w hw'
    have := h0 w hw'
    nlinarith
  · push Not at hc
    have := h2 w hw'
    have := h0 w hw'
    nlinarith

private lemma pf_Y_anti {γin γout : ℝ} (hγin : 0 < γin) (hγout : 0 < γout) :
    AntitoneOn (isoYroot γin γout) (Ioi 0) :=
  (lem_app_iso_comparison_i pf_link_id hγin hγout).2.2.2.2.2.antitoneOn

private lemma pf_Y_basic {γin γout s : ℝ} (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s) :
    0 ≤ isoYroot γin γout s ∧ isoYroot γin γout s ≤ min γin γout ∧
      s * isoYroot γin γout s ≤ γin * γout := by
  have hspec := (lem_app_iso_comparison_i pf_link_id hγin hγout).2.2.2.1 s hs
  obtain ⟨⟨hq0, hrq⟩, hG⟩ := hspec
  unfold isoG at hG
  have hq0' : 0 ≤ isoYroot γin γout s := hq0
  have hrq' : isoYroot γin γout s < min γin γout := hrq
  refine ⟨hq0', hrq'.le, ?_⟩
  have h1 : 0 < γout - isoYroot γin γout s := by linarith [min_le_right γin γout]
  have h2 : 0 < γin - isoYroot γin γout s := by linarith [min_le_left γin γout]
  have : s * isoYroot γin γout s =
      (γout - isoYroot γin γout s) * (γin - isoYroot γin γout s) := by
    unfold isoYroot; simp only at hG ⊢; linarith
  rw [this, mul_comm γin γout]
  exact mul_le_mul (by linarith) (by linarith) h2.le hγout.le

private lemma pf_Yc_integrable {γin γout c ϱ : ℝ} (hγin : 0 < γin) (hγout : 0 < γout)
    (hc : 0 < c) (hϱ : 0 ≤ ϱ) :
    IntegrableOn (fun u : ℝ => isoYroot γin γout ((ϱ + u ^ 2) / c)) (Ioi (0 : ℝ)) := by
  have hm : 0 < min γin γout := lt_min hγin hγout
  refine pf_int_of_bounds (M := min γin γout) (P := c * (γin * γout)) hm.le
    (by positivity) ?_ ?_ ?_ ?_
  · refine aemeasurable_restrict_of_antitoneOn measurableSet_Ioi ?_
    intro a ha b hb hab
    have ha' : (0 : ℝ) < a := ha
    have hb' : (0 : ℝ) < b := hb
    apply pf_Y_anti hγin hγout
    · exact div_pos (by positivity) hc
    · exact div_pos (by positivity) hc
    · apply div_le_div_of_nonneg_right _ hc.le
      nlinarith
  · intro w hw
    exact (pf_Y_basic hγin hγout (div_pos (by positivity) hc)).1
  · intro w hw
    exact (pf_Y_basic hγin hγout (div_pos (by positivity) hc)).2.1
  · intro w hw
    have hb := (pf_Y_basic hγin hγout (div_pos (by positivity : 0 < ϱ + w ^ 2) hc))
    have h1 := hb.2.2
    have h2 := hb.1
    have : w ^ 2 * isoYroot γin γout ((ϱ + w ^ 2) / c) ≤
        (ϱ + w ^ 2) * isoYroot γin γout ((ϱ + w ^ 2) / c) :=
      mul_le_mul_of_nonneg_right (by linarith) h2
    have h3 : (ϱ + w ^ 2) * isoYroot γin γout ((ϱ + w ^ 2) / c) ≤ c * (γin * γout) := by
      have : (ϱ + w ^ 2) / c * isoYroot γin γout ((ϱ + w ^ 2) / c) ≤ γin * γout := h1
      rw [div_mul_eq_mul_div, div_le_iff₀ hc] at this
      linarith
    linarith

private lemma pf_Y_scaleint {γin γout : ℝ} (c ϱ : ℝ) (hc : 0 < c) :
    ∫ u in Ioi (0 : ℝ), isoYroot γin γout ((ϱ + u ^ 2) / c) =
      Real.sqrt c * ∫ w in Ioi (0 : ℝ), isoYroot γin γout (ϱ / c + w ^ 2) := by
  have hr : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have h := integral_comp_mul_left_Ioi (fun w : ℝ => isoYroot γin γout (ϱ / c + w ^ 2)) 0
    (b := (Real.sqrt c)⁻¹) (inv_pos.2 hr)
  have hfun : ∀ u : ℝ, isoYroot γin γout ((ϱ + u ^ 2) / c) =
      isoYroot γin γout (ϱ / c + ((Real.sqrt c)⁻¹ * u) ^ 2) := by
    intro u
    congr 1
    rw [mul_pow, inv_pow, Real.sq_sqrt hc.le]
    field_simp
  simp only [hfun]
  rw [h]
  simp

private lemma pf_W_anti {γin γout a a' : ℝ} (hγin : 0 < γin) (hγout : 0 < γout)
    (ha : 0 ≤ a) (haa : a ≤ a') :
    ∫ w in Ioi (0 : ℝ), isoYroot γin γout (a' + w ^ 2) ≤
      ∫ w in Ioi (0 : ℝ), isoYroot γin γout (a + w ^ 2) := by
  have hint : ∀ b : ℝ, 0 ≤ b →
      IntegrableOn (fun w : ℝ => isoYroot γin γout (b + w ^ 2)) (Ioi (0 : ℝ)) := by
    intro b hb
    have := pf_Yc_integrable (γin := γin) (γout := γout) (c := 1) (ϱ := b) hγin hγout one_pos hb
    simpa using this
  refine setIntegral_mono_on (hint a' (ha.trans haa)) (hint a ha) measurableSet_Ioi ?_
  intro w hw
  have hw' : (0 : ℝ) < w := hw
  apply pf_Y_anti hγin hγout
  · show (0 : ℝ) < a + w ^ 2
    positivity
  · show (0 : ℝ) < a' + w ^ 2
    have : 0 ≤ a' := ha.trans haa
    positivity
  · linarith

private lemma pf_dlin_eq {γin γout S ϱ : ℝ} (hγin : 0 < γin) (hγout : 0 < γout) (hS : 0 < S)
    (hϱ : 0 ≤ ϱ) :
    isoDlin (S * γin) (S * γout) ϱ = Real.sqrt 2 / (Real.pi * γin * γout) *
      ((∫ w in Ioi (0 : ℝ), isoYroot γin γout (ϱ / S + w ^ 2)) / Real.sqrt S) := by
  unfold isoDlin
  have hcongr : ∫ v in Ioi (0 : ℝ), isoYroot (S * γin) (S * γout) (ϱ + v ^ 2) =
      ∫ v in Ioi (0 : ℝ), S * isoYroot γin γout ((ϱ + v ^ 2) / S) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
    have hv' : (0 : ℝ) < v := hv
    have hpos : 0 < (ϱ + v ^ 2) / S := div_pos (by positivity) hS
    have := pf_Y_scale hS hγin hγout hpos
    rw [mul_div_cancel₀ _ hS.ne'] at this
    exact this
  rw [hcongr, integral_const_mul, pf_Y_scaleint S ϱ hS]
  have hr : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  have hsq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS.le
  generalize (∫ w in Ioi (0 : ℝ), isoYroot γin γout (ϱ / S + w ^ 2)) = W
  generalize Real.sqrt S = r at hr hsq ⊢
  subst hsq
  field_simp

private lemma pf_g_integrable {β γin γout S ε ϱ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hS : S = Muon.sPow β 2)
    (hε : ε = 6 * min γin γout * (1 - β ^ 2)) (hε2 : ε ≤ 1 / 2) (hϱ : 0 ≤ ϱ) :
    IntegrableOn (fun u : ℝ => isoGb β γin γout (ϱ + u ^ 2)) (Ioi (0 : ℝ)) := by
  obtain ⟨hSpos, _, _⟩ := pf_sPow_consts hβ0 hβ1
  rw [← hS] at hSpos
  have hm : 0 < min γin γout := lt_min hγin hγout
  refine pf_int_of_bounds (M := 2 * min γin γout / S) (P := γin * γout) (by positivity)
    (by positivity) ?_ ?_ ?_ ?_
  · refine aemeasurable_restrict_of_antitoneOn measurableSet_Ioi ?_
    intro a ha b hb hab
    have ha' : (0 : ℝ) < a := ha
    have hb' : (0 : ℝ) < b := hb
    have hlink := pf_link_beta hβ0 hβ1
    have hqanti := (lem_app_iso_comparison_i hlink hγin hγout).2.2.2.2.2.antitoneOn
    have hqD := (lem_app_iso_comparison_i hlink hγin hγout).2.2.2.1
    have hmono := (lem_app_iso_weights_v hβ0 hβ1).2.2.monotoneOn
    have h1 : (0 : ℝ) < ϱ + a ^ 2 := by positivity
    have h2 : (0 : ℝ) < ϱ + b ^ 2 := by positivity
    have hq := hqanti (show ϱ + a ^ 2 ∈ Ioi (0 : ℝ) from h1) (show ϱ + b ^ 2 ∈ Ioi (0 : ℝ) from h2)
      (by nlinarith)
    have hqa : 0 ≤ qIso β γin γout (ϱ + a ^ 2) := ((hqD _ h1).1).1
    have hqb : 0 ≤ qIso β γin γout (ϱ + b ^ 2) := ((hqD _ h2).1).1
    exact hmono (Set.mem_Ici.mpr hqb) (Set.mem_Ici.mpr hqa) hq
  · intro w hw
    exact (pf_pointwise hβ0 hβ1 hγin hγout hS hε hε2 (by positivity : (0:ℝ) < ϱ + w ^ 2)).1
  · intro w hw
    exact (pf_pointwise hβ0 hβ1 hγin hγout hS hε hε2 (by positivity : (0:ℝ) < ϱ + w ^ 2)).2.2.2.1
  · intro w hw
    have hp := pf_pointwise hβ0 hβ1 hγin hγout hS hε hε2 (by positivity : (0:ℝ) < ϱ + w ^ 2)
    have h0 := hp.1
    have h5 := hp.2.2.2.2
    calc w ^ 2 * isoGb β γin γout (ϱ + w ^ 2) ≤ (ϱ + w ^ 2) * isoGb β γin γout (ϱ + w ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) h0
      _ ≤ γin * γout := h5

private lemma pf_main (β γin γout : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hε : 6 * min γin γout * (1 - β ^ 2) ≤ 1 / 2) :
    ∀ ϱ : ℝ, 0 ≤ ϱ → ∃ ϑ : ℝ,
      1 - 6 * min γin γout * (1 - β ^ 2) ≤ ϑ ∧
      ϑ ≤ (1 - 6 * min γin γout * (1 - β ^ 2)) ^ (-(1 / 2 : ℝ)) ∧
      dIso β γin γout ϱ = ϑ * isoDlin (Muon.sPow β 2 * γin) (Muon.sPow β 2 * γout) ϱ := by
  intro ϱ hϱ
  obtain ⟨hSpos, hS4, hS3⟩ := pf_sPow_consts hβ0 hβ1
  generalize hSdef : Muon.sPow β 2 = S at hSpos hS4 hS3
  generalize hεdef : 6 * min γin γout * (1 - β ^ 2) = ε at hε ⊢
  have hS : S = Muon.sPow β 2 := hSdef.symm
  have hε' : ε = 6 * min γin γout * (1 - β ^ 2) := hεdef.symm
  have hm : 0 < min γin γout := lt_min hγin hγout
  have hb2 : 0 ≤ 1 - β ^ 2 := by nlinarith
  have hε0 : 0 ≤ ε := by rw [hε']; positivity
  have hc : 0 < S * (1 - ε) := mul_pos hSpos (by linarith)
  have hcS : S * (1 - ε) ≤ S := by nlinarith
  set W := ∫ w in Ioi (0 : ℝ), isoYroot γin γout (ϱ / S + w ^ 2) with hW
  set I := ∫ u in Ioi (0 : ℝ), isoGb β γin γout (ϱ + u ^ 2) with hI
  have hW0 : 0 ≤ W := setIntegral_nonneg measurableSet_Ioi
    (fun w hw => (pf_Y_basic hγin hγout (by
      have : (0 : ℝ) < w := hw
      have : 0 ≤ ϱ / S := div_nonneg hϱ hSpos.le
      positivity)).1)
  have hr : 0 < Real.sqrt S := Real.sqrt_pos.2 hSpos
  have ht : 0 < Real.sqrt (1 - ε) := Real.sqrt_pos.2 (by linarith)
  have hrsq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hSpos.le
  have htsq : Real.sqrt (1 - ε) ^ 2 = 1 - ε := Real.sq_sqrt (by linarith)
  have hgint := pf_g_integrable (ϱ := ϱ) hβ0 hβ1 hγin hγout hS hε' hε hϱ
  have hpt : ∀ u : ℝ, 0 < u → _ := fun u hu =>
    pf_pointwise hβ0 hβ1 hγin hγout hS hε' hε (by positivity : (0:ℝ) < ϱ + u ^ 2)
  -- lower bound
  have hL : (1 - ε) * (W / Real.sqrt S) ≤ I := by
    have h1 : ∫ u in Ioi (0 : ℝ), (1 - ε) * (isoYroot γin γout ((ϱ + u ^ 2) / S) / S) =
        (1 - ε) * (W / Real.sqrt S) := by
      rw [integral_const_mul, integral_div, pf_Y_scaleint S ϱ hSpos, hW]
      generalize (∫ w in Ioi (0 : ℝ), isoYroot γin γout (ϱ / S + w ^ 2)) = W'
      generalize Real.sqrt S = r at hr hrsq ⊢
      subst hrsq
      field_simp
    rw [← h1]
    refine setIntegral_mono_on
      (((pf_Yc_integrable hγin hγout hSpos hϱ).div_const S).const_mul (1 - ε)) hgint
      measurableSet_Ioi ?_
    intro u hu
    exact (hpt u hu).2.1
  -- upper bound
  have hU : I ≤ W / (Real.sqrt S * Real.sqrt (1 - ε)) := by
    have hsc : Real.sqrt (S * (1 - ε)) = Real.sqrt S * Real.sqrt (1 - ε) :=
      Real.sqrt_mul hSpos.le _
    have h1 : I ≤ ∫ u in Ioi (0 : ℝ),
        isoYroot γin γout ((ϱ + u ^ 2) / (S * (1 - ε))) / (S * (1 - ε)) := by
      refine setIntegral_mono_on hgint
        ((pf_Yc_integrable hγin hγout hc hϱ).div_const _) measurableSet_Ioi ?_
      intro u hu
      exact (hpt u hu).2.2.1
    refine h1.trans ?_
    rw [integral_div, pf_Y_scaleint (S * (1 - ε)) ϱ hc, hsc]
    have h2 : ∫ w in Ioi (0 : ℝ), isoYroot γin γout (ϱ / (S * (1 - ε)) + w ^ 2) ≤ W :=
      pf_W_anti hγin hγout (div_nonneg hϱ hSpos.le)
        (div_le_div_of_nonneg_left hϱ hc hcS)
    generalize (∫ w in Ioi (0 : ℝ), isoYroot γin γout (ϱ / (S * (1 - ε)) + w ^ 2)) = W' at h2 ⊢
    have h3 : Real.sqrt S * Real.sqrt (1 - ε) * W' / (S * (1 - ε)) =
        W' / (Real.sqrt S * Real.sqrt (1 - ε)) := by
      generalize Real.sqrt S = r at hr hrsq ⊢
      generalize Real.sqrt (1 - ε) = t at ht htsq ⊢
      rw [← hrsq, ← htsq]
      field_simp
    rw [h3]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  have hD := pf_dlin_eq (S := S) hγin hγout hSpos hϱ
  have hdI : dIso β γin γout ϱ = Real.sqrt 2 / (Real.pi * γin * γout) * I := rfl
  have hK : 0 < Real.sqrt 2 / (Real.pi * γin * γout) := by positivity
  rw [← hW] at hD
  clear_value W I
  rw [hdI, hD]
  have hrp : (1 - ε) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (1 - ε))⁻¹ := by
    rw [Real.rpow_neg (by linarith), Real.sqrt_eq_rpow]
  rw [hrp]
  have ht1 : Real.sqrt (1 - ε) ≤ 1 := by
    calc Real.sqrt (1 - ε) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  rcases hW0.eq_or_lt with hW00 | hWpos
  · refine ⟨1, by linarith, ?_, ?_⟩
    · rw [le_inv_comm₀ one_pos ht]; simpa using ht1
    · rw [← hW00] at hL hU
      have : I = 0 := by
        apply le_antisymm
        · simpa using hU
        · simpa using hL
      rw [this, ← hW00]; simp
  · refine ⟨I * Real.sqrt S / W, ?_, ?_, ?_⟩
    · rw [le_div_iff₀ hWpos]
      rw [mul_div_assoc', div_le_iff₀ hr] at hL
      linarith
    · rw [div_le_iff₀ hWpos, inv_mul_eq_div, le_div_iff₀ ht]
      rw [le_div_iff₀ (by positivity)] at hU
      nlinarith
    · field_simp

end SmallMomentumHelpers

/-! ### Private helpers for `thm_app_iso_small_momentum_iii` (task P-F.5.P3) -/

private lemma pf_iii_sPow_zero : Muon.sPow 0 2 = 1 := by
  unfold Muon.sPow Muon.emaW
  rw [tsum_eq_single 0 (fun j hj => by simp [hj])]
  simp

private lemma pf_iii_dIso_zero (β γin γout : ℝ) :
    dIso β γin γout 0 = Cbeta β γin γout := by
  unfold dIso Cbeta
  simp only [zero_add]

private lemma pf_iii_dlin_scale {γin γout c : ℝ} (hc : 0 < c) (hγin : 0 < γin)
    (hγout : 0 < γout) :
    isoDlin (c * γin) (c * γout) 0 = c ^ (-(1 / 2 : ℝ)) * isoDlin γin γout 0 := by
  have hpt : EqOn (fun v : ℝ => isoYroot (c * γin) (c * γout) (0 + v ^ 2))
      (fun v : ℝ => c * isoYroot γin γout ((0 + v ^ 2) / c)) (Ioi (0 : ℝ)) := by
    intro v hv
    have hv' : (0 : ℝ) < v := hv
    have hs : 0 < (0 + v ^ 2) / c := by
      rw [zero_add]; exact div_pos (pow_pos hv' 2) hc
    have h := pf_Y_scale hc hγin hγout hs
    have e : c * ((0 + v ^ 2) / c) = 0 + v ^ 2 := by field_simp
    rw [e] at h
    exact h
  have hint : ∫ v in Ioi (0 : ℝ), isoYroot (c * γin) (c * γout) (0 + v ^ 2)
      = c * ∫ v in Ioi (0 : ℝ), isoYroot γin γout ((0 + v ^ 2) / c) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have hsc := pf_Y_scaleint (γin := γin) (γout := γout) c 0 hc
  have hsc' : ∫ v in Ioi (0 : ℝ), isoYroot γin γout ((0 + v ^ 2) / c)
      = Real.sqrt c * ∫ v in Ioi (0 : ℝ), isoYroot γin γout (v ^ 2) := by
    rw [hsc]; simp
  have hr : c ^ (-(1 / 2 : ℝ)) = (Real.sqrt c)⁻¹ := by
    rw [Real.rpow_neg hc.le, Real.sqrt_eq_rpow]
  unfold isoDlin
  rw [hint, hsc', hr]
  generalize hrdef : Real.sqrt c = r at *
  have hc2 : c = r ^ 2 := by rw [← hrdef, Real.sq_sqrt hc.le]
  subst hc2
  have hγin' := hγin.ne'
  have hγout' := hγout.ne'
  have hr0 : r ≠ 0 := by
    rintro rfl; norm_num at hc
  field_simp
  ring

private lemma pf_iii_Y_pos {γin γout s : ℝ} (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s) :
    0 < isoYroot γin γout s := by
  have hspec := (lem_app_iso_comparison_i pf_link_id hγin hγout).2.2.2.1 s hs
  obtain ⟨⟨hq0, hrq⟩, hG⟩ := hspec
  unfold isoG at hG
  have hq0' : 0 ≤ isoYroot γin γout s := hq0
  rcases hq0'.eq_or_lt with h0 | hpos
  · exfalso
    have : s * isoYroot γin γout s =
        (γout - isoYroot γin γout s) * (γin - isoYroot γin γout s) := by
      unfold isoYroot; simp only at hG ⊢; linarith
    rw [← h0] at this
    nlinarith [mul_pos hγin hγout]
  · exact hpos

private lemma pf_iii_dlin_pos {γin γout : ℝ} (hγin : 0 < γin) (hγout : 0 < γout) :
    0 < isoDlin γin γout 0 := by
  unfold isoDlin
  have hK : 0 < Real.sqrt 2 / (Real.pi * γin * γout) := by positivity
  refine mul_pos hK ?_
  have hint := pf_Yc_integrable (ϱ := 0) hγin hγout one_pos le_rfl
  simp only [div_one] at hint
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun v : ℝ => isoYroot γin γout (0 + v ^ 2)) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ (fun v hv => ?_)
    have hv' : (0 : ℝ) < v := hv
    exact (pf_Y_basic hγin hγout (by rw [zero_add]; exact pow_pos hv' 2)).1
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  have hsub : Ioi (0 : ℝ) ⊆
      Function.support (fun v : ℝ => isoYroot γin γout (0 + v ^ 2)) ∩ Ioi (0 : ℝ) := by
    intro v hv
    have hv' : (0 : ℝ) < v := hv
    refine ⟨Function.mem_support.2 ?_, hv⟩
    exact (pf_iii_Y_pos hγin hγout (by rw [zero_add]; exact pow_pos hv' 2)).ne'
  exact lt_of_lt_of_le (by simp) (measure_mono hsub)

/-! ### Private helpers for `thm_app_iso_small_momentum_ii` (task P-F.5.P3) -/

private lemma pf_ii_ae_nonneg {r : ℝ} (hr : 0 < r) : ∀ᵐ x ∂(isoMP r), 0 ≤ x := by
  have ha := mpL_a_nonneg r hr
  unfold isoMP
  refine ae_add_measure_iff.2 ⟨Measure.ae_smul_measure ((ae_dirac_iff (measurableSet_Ici (a := (0:ℝ)))).2 le_rfl) _, ?_⟩
  have h : ∀ᵐ x ∂(volume.restrict (Ioo (isoMPa r) (isoMPb r))), 0 ≤ x := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact ae_of_all _ (fun x hx => ha.trans hx.1.le)
  exact (withDensity_absolutelyContinuous _ _).ae_le h

private lemma pf_ii_int_sqrt {r : ℝ} (hr : 0 < r) : Integrable Real.sqrt (isoMP r) :=
  (mpL_wrap r hr Real.sqrt Real.continuous_sqrt.measurable
    (Real.sqrt ((1 + 1 / r) + 2 / Real.sqrt r))
    (fun x hx => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (le_of_lt hx.2))).1

private lemma pf_ii_atan {l : ℝ} (hl : 0 < l) :
    Integrable (fun w : ℝ => l / (l + w ^ 2)) (volume.restrict (Ioi 0)) ∧
      ∫ w in Ioi (0:ℝ), l / (l + w ^ 2) = Real.pi / 2 * Real.sqrt l := by
  have hs : 0 < Real.sqrt l := Real.sqrt_pos.2 hl
  have hfun : ∀ w : ℝ, l / (l + w ^ 2) = (1 + ((Real.sqrt l)⁻¹ * w) ^ 2)⁻¹ := by
    intro w
    rw [mul_pow, inv_pow, Real.sq_sqrt hl.le]
    field_simp
  simp_rw [hfun]
  refine ⟨(integrable_inv_one_add_mul_sq (inv_ne_zero hs.ne')).integrableOn, ?_⟩
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => (1 + x ^ 2)⁻¹) 0
    (b := (Real.sqrt l)⁻¹) (inv_pos.2 hs)
  simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero, inv_inv,
    smul_eq_mul] at h
  rw [h]
  ring

private lemma pf_ii_inv_int {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 < x) :
    Integrable (fun l : ℝ => (l + x)⁻¹) (isoMP r) := by
  haveI := (lem_app_iso_mp hr).1
  refine Integrable.mono' (integrable_const (x⁻¹)) ?_ ?_
  · exact ((measurable_id.add_const x).inv).aestronglyMeasurable
  · filter_upwards [pf_ii_ae_nonneg hr] with l hl
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_anti₀ hx (by linarith)

private lemma pf_ii_Y_eq {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 < x) :
    ∫ l, l / (l + x) ∂(isoMP r) = 1 - x * isoNegStieltjes (isoMP r) x := by
  haveI := (lem_app_iso_mp hr).1
  have hint := pf_ii_inv_int hr hx
  have hcongr : ∫ l, l / (l + x) ∂(isoMP r) = ∫ l, (1 - x * (l + x)⁻¹) ∂(isoMP r) := by
    refine integral_congr_ae ?_
    filter_upwards [pf_ii_ae_nonneg hr] with l hl
    have : l + x ≠ 0 := by positivity
    field_simp
    ring
  rw [hcongr, integral_sub (integrable_const _) (hint.const_mul x), integral_const_mul]
  simp [isoNegStieltjes, Measure.real]

private lemma pf_ii_Y_nonneg {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 < x) :
    0 ≤ ∫ l, l / (l + x) ∂(isoMP r) := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [pf_ii_ae_nonneg hr] with l hl
  positivity

private lemma pf_ii_root {γin γout s : ℝ} (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s) :
    isoYroot γin γout s = γout * ∫ l, l / (l + s / γout) ∂(isoMP (γout / γin)) := by
  have hr : 0 < γout / γin := div_pos hγout hγin
  have hinv : 1 / (γout / γin) = γin / γout := one_div_div _ _
  generalize hxdef : s / γout = x
  have hx0 : 0 < x := by rw [← hxdef]; exact div_pos hs hγout
  have hsx : s = γout * x := by rw [← hxdef]; field_simp
  obtain ⟨-, -, -, hall⟩ := lem_app_iso_mp hr
  obtain ⟨⟨hmpos, hquad⟩, -, -⟩ := hall x hx0
  have hYeq := pf_ii_Y_eq hr hx0
  have hY0 := pf_ii_Y_nonneg hr hx0
  generalize ∫ l, l / (l + x) ∂(isoMP (γout / γin)) = Y at hYeq hY0 ⊢
  generalize isoNegStieltjes (isoMP (γout / γin)) x = m at hYeq hquad hmpos
  rw [hinv] at hquad
  have hquadY : x * Y = (1 - Y) * (γin / γout - Y) := by
    rw [hYeq]
    linear_combination (-x) * hquad
  have hY1 : Y < 1 := by rw [hYeq]; nlinarith [mul_pos hx0 hmpos]
  have hYpos : 0 < Y := by
    rcases hY0.eq_or_lt with h | h
    · exfalso
      rw [← h] at hquadY
      have : 0 < γin / γout := div_pos hγin hγout
      nlinarith
    · exact h
  have hYr : Y < γin / γout := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith [mul_pos hx0 hYpos, mul_nonneg (sub_pos.2 hY1).le (sub_nonneg.2 hneg)]
  have hq1 : γout * Y < γout := by nlinarith
  have hq2 : γout * Y < γin := by
    have := mul_lt_mul_of_pos_left hYr hγout
    rwa [mul_div_cancel₀ _ hγout.ne'] at this
  obtain ⟨q0, -, hu⟩ := (lem_app_iso_comparison_i pf_link_id hγin hγout).2.1 s hs
  have hspec := (lem_app_iso_comparison_i pf_link_id hγin hγout).2.2.2.1 s hs
  have h1 := hu _ hspec
  have h2 := hu (γout * Y) ⟨⟨by positivity, lt_min hq2 hq1⟩, by
    unfold isoG
    simp only
    have e : (1 - Y) * (γin / γout - Y) * γout = (1 - Y) * (γin - γout * Y) := by
      field_simp
    rw [hsx]
    linear_combination (γout ^ 2) * hquadY + γout * e⟩
  unfold isoYroot
  rw [h1, h2]

private lemma pf_ii_fubini {r : ℝ} (hr : 0 < r) :
    ∫ w in Ioi (0:ℝ), (∫ l, l / (l + w ^ 2) ∂(isoMP r)) = Real.pi / 2 * isoJr r := by
  haveI := (lem_app_iso_mp hr).1
  have hae := pf_ii_ae_nonneg hr
  have hint := pf_ii_int_sqrt hr
  have hmeas : Measurable (fun p : ℝ × ℝ => p.1 / (p.1 + p.2 ^ 2)) := by fun_prop
  have hinner : ∀ l : ℝ, 0 ≤ l →
      ∫ w in Ioi (0:ℝ), l / (l + w ^ 2) = Real.pi / 2 * Real.sqrt l := by
    intro l hl
    rcases hl.eq_or_lt with h | h
    · subst h; simp
    · exact (pf_ii_atan h).2
  have hprod : Integrable (Function.uncurry fun (l w : ℝ) => l / (l + w ^ 2))
      ((isoMP r).prod (volume.restrict (Ioi 0))) := by
    change Integrable (fun p : ℝ × ℝ => p.1 / (p.1 + p.2 ^ 2)) _
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    constructor
    · filter_upwards [hae] with l hl
      rcases hl.eq_or_lt with h | h
      · subst h; simp [Function.uncurry]
      · exact (pf_ii_atan h).1
    · refine (hint.const_mul (Real.pi / 2)).congr ?_
      filter_upwards [hae] with l hl
      rw [← hinner l hl]
      refine integral_congr_ae ?_
      refine ae_of_all _ (fun w => ?_)
      simp only []
      rw [Real.norm_of_nonneg (div_nonneg hl (by positivity))]
  have hswap := integral_integral_swap hprod
  rw [← hswap]
  have : ∀ᵐ l ∂(isoMP r), ∫ w in Ioi (0:ℝ), l / (l + w ^ 2) = Real.pi / 2 * Real.sqrt l := by
    filter_upwards [hae] with l hl using hinner l hl
  rw [integral_congr_ae this, integral_const_mul]
  rfl

private lemma pf_ii_dlin_zero {γin γout : ℝ} (hγin : 0 < γin) (hγout : 0 < γout) :
    isoDlin γin γout 0 = γout / γin * isoJr (γout / γin) / Real.sqrt (2 * γout) := by
  have hr : 0 < γout / γin := div_pos hγout hγin
  have ha : 0 < Real.sqrt γout := Real.sqrt_pos.2 hγout
  have hsq : Real.sqrt γout ^ 2 = γout := Real.sq_sqrt hγout.le
  have hpt : ∀ v ∈ Ioi (0 : ℝ), isoYroot γin γout (0 + v ^ 2) =
      γout * (fun w : ℝ => ∫ l, l / (l + w ^ 2) ∂(isoMP (γout / γin))) ((Real.sqrt γout)⁻¹ * v) := by
    intro v hv
    have hv' : (0 : ℝ) < v := hv
    rw [pf_ii_root hγin hγout (by rw [zero_add]; positivity)]
    congr 2
    funext l
    rw [mul_pow, inv_pow, hsq, zero_add]
    congr 2
    field_simp
  have h := integral_comp_mul_left_Ioi
    (fun w : ℝ => ∫ l, l / (l + w ^ 2) ∂(isoMP (γout / γin))) 0
    (b := (Real.sqrt γout)⁻¹) (inv_pos.2 ha)
  unfold isoDlin
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [mul_zero] at h
  rw [h, pf_ii_fubini hr]
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hπ := Real.pi_pos
  generalize isoJr (γout / γin) = J
  generalize Real.sqrt γout = a at *
  subst hsq
  simp only [inv_inv, smul_eq_mul]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

private lemma pf_ii_J_one : isoJr 1 = 8 / (3 * Real.pi) := by
  have ha : isoMPa 1 = 0 := by unfold isoMPa; simp
  have hb : isoMPb 1 = 4 := by unfold isoMPb; norm_num
  rw [rcp_J_formula 1 one_pos, ha, hb]
  have hcongr : ∫ x in Ioo (0:ℝ) 4, Real.sqrt ((4 - x) * (x - 0)) / (2 * Real.pi * x) * Real.sqrt x
      = ∫ x in Ioo (0:ℝ) 4, Real.sqrt (4 - x) / (2 * Real.pi) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
    have hx0 : 0 < x := hx.1
    have hx4 : 0 ≤ 4 - x := by linarith [hx.2]
    simp only [sub_zero]
    rw [Real.sqrt_mul hx4]
    have hs := Real.sq_sqrt hx0.le
    have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    field_simp
    rw [hs]
    ring
  rw [hcongr, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_div]
  have h1 : ∫ x in (0:ℝ)..4, Real.sqrt (4 - x) = 16 / 3 := by
    have := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 4) (fun x : ℝ => Real.sqrt x) 4
    rw [this]
    simp only [sub_self, sub_zero]
    simp_rw [Real.sqrt_eq_rpow]
    rw [integral_rpow (by norm_num)]
    have : (4:ℝ) ^ ((1:ℝ) / 2 + 1) = 8 := by
      rw [show (1:ℝ) / 2 + 1 = 3 / 2 by norm_num,
        show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [this]
    norm_num
  rw [h1]
  have hπ := Real.pi_pos
  field_simp
  ring


/-- `thm:app-iso-small-momentum`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1954–1980):
```latex
\begin{theorem}[Small aspect ratios with momentum]\label{thm:app-iso-small-momentum}
Let $\bmom\in[0,1)$ and $\gin,\gout>0$, and assume
$\varepsilon_\bmom\defeq6\gamma_\wedge(1-\bmom^2)\le\frac12$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ridge\ge0$ there is $\vartheta\in\big[1-\varepsilon_\bmom,(1-\varepsilon_\bmom)^{-1/2}\big]$ with
\[
\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gin,\gout)=\vartheta\;\mathfrak d_{\mathrm{lin}}(\sw2\gin,\sw2\gout;\ridge).
\]
\item With $r\defeq\gout/\gin$ and $J_r$ of \cref{thm:app-iso-small},
\[
\mathfrak d_{\mathrm{lin}}(\gin,\gout;0)=\frac{r\,J_r}{\sqrt{2\gout}},\qquad
\mathfrak d_{\mathrm{lin}}(\gamma,\gamma;0)=\frac{8}{3\pi\sqrt{2\gamma}} .
\]
In particular, in the square case $C_\bmom(\gamma)=8\vartheta/(3\pi\sqrt{2\sw2\gamma})$
with $\vartheta$ of (i) at $\ridge=0$.
\item If $6\gamma_\wedge\le\frac12$, then for every $\bmom\in[0,1)$
\[
\big(1-6\gamma_\wedge\big)^{3/2}\le\frac{C_\bmom(\gin,\gout)}{\sw2^{-1/2}\,C_0(\gin,\gout)}\le\big(1-6\gamma_\wedge\big)^{-3/2}.
\]
\item For every $\ridge\ge0$,
\[
(1-\varepsilon_\bmom)\big(1-6\sw2\gamma_\wedge\big)^{1/2}\le
\frac{\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gin,\gout)}{\mathfrak d_{\mathrm{iso}}(\ridge;0,\sw2\gin,\sw2\gout)}\le
(1-\varepsilon_\bmom)^{-1/2}\big(1-6\sw2\gamma_\wedge\big)^{-1}.
\]
\end{enumerate}
\end{theorem}
```

Part (i). `d_iso` is `dIso` (Closure/ZeroRidge), `d_lin` is `isoDlin`, `sw2 = Muon.sPow β 2`, `γ∧ = min γin γout`. The standing hypothesis `hε` is `ε_β ≤ 1/2`.
-/
theorem thm_app_iso_small_momentum_i (β γin γout : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hε : 6 * min γin γout * (1 - β ^ 2) ≤ 1 / 2) :
    ∀ ϱ : ℝ, 0 ≤ ϱ → ∃ ϑ : ℝ,
      1 - 6 * min γin γout * (1 - β ^ 2) ≤ ϑ ∧
      ϑ ≤ (1 - 6 * min γin γout * (1 - β ^ 2)) ^ (-(1 / 2 : ℝ)) ∧
      dIso β γin γout ϱ = ϑ * isoDlin (Muon.sPow β 2 * γin) (Muon.sPow β 2 * γout) ϱ :=
  pf_main β γin γout hβ0 hβ1 hγin hγout hε

/-- `thm:app-iso-small-momentum`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1954–1980):
```latex
\begin{theorem}[Small aspect ratios with momentum]\label{thm:app-iso-small-momentum}
Let $\bmom\in[0,1)$ and $\gin,\gout>0$, and assume
$\varepsilon_\bmom\defeq6\gamma_\wedge(1-\bmom^2)\le\frac12$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ridge\ge0$ there is $\vartheta\in\big[1-\varepsilon_\bmom,(1-\varepsilon_\bmom)^{-1/2}\big]$ with
\[
\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gin,\gout)=\vartheta\;\mathfrak d_{\mathrm{lin}}(\sw2\gin,\sw2\gout;\ridge).
\]
\item With $r\defeq\gout/\gin$ and $J_r$ of \cref{thm:app-iso-small},
\[
\mathfrak d_{\mathrm{lin}}(\gin,\gout;0)=\frac{r\,J_r}{\sqrt{2\gout}},\qquad
\mathfrak d_{\mathrm{lin}}(\gamma,\gamma;0)=\frac{8}{3\pi\sqrt{2\gamma}} .
\]
In particular, in the square case $C_\bmom(\gamma)=8\vartheta/(3\pi\sqrt{2\sw2\gamma})$
with $\vartheta$ of (i) at $\ridge=0$.
\item If $6\gamma_\wedge\le\frac12$, then for every $\bmom\in[0,1)$
\[
\big(1-6\gamma_\wedge\big)^{3/2}\le\frac{C_\bmom(\gin,\gout)}{\sw2^{-1/2}\,C_0(\gin,\gout)}\le\big(1-6\gamma_\wedge\big)^{-3/2}.
\]
\item For every $\ridge\ge0$,
\[
(1-\varepsilon_\bmom)\big(1-6\sw2\gamma_\wedge\big)^{1/2}\le
\frac{\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gin,\gout)}{\mathfrak d_{\mathrm{iso}}(\ridge;0,\sw2\gin,\sw2\gout)}\le
(1-\varepsilon_\bmom)^{-1/2}\big(1-6\sw2\gamma_\wedge\big)^{-1}.
\]
\end{enumerate}
\end{theorem}
```

Part (ii). The square case of the `In particular` clause carries the same `ϑ` as part (i) at `ϱ = 0`; the link `C_β = d_iso(0)` is encoded by stating `dIso ... 0` and `Cbeta` both. Hypothesis `γin = γout` is the square case.
-/
theorem thm_app_iso_small_momentum_ii (β γin γout : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hε : 6 * min γin γout * (1 - β ^ 2) ≤ 1 / 2) :
    isoDlin γin γout 0 = γout / γin * isoJr (γout / γin) / Real.sqrt (2 * γout) ∧
      (∀ γ : ℝ, 0 < γ → isoDlin γ γ 0 = 8 / (3 * Real.pi * Real.sqrt (2 * γ))) ∧
      (γin = γout → ∃ ϑ : ℝ,
        1 - 6 * min γin γout * (1 - β ^ 2) ≤ ϑ ∧
        ϑ ≤ (1 - 6 * min γin γout * (1 - β ^ 2)) ^ (-(1 / 2 : ℝ)) ∧
        dIso β γin γout 0 = ϑ * isoDlin (Muon.sPow β 2 * γin) (Muon.sPow β 2 * γout) 0 ∧
        Cbeta β γin γout = 8 * ϑ / (3 * Real.pi * Real.sqrt (2 * Muon.sPow β 2 * γin))) := by
  have hsq : ∀ γ : ℝ, 0 < γ → isoDlin γ γ 0 = 8 / (3 * Real.pi * Real.sqrt (2 * γ)) := by
    intro γ hγ
    rw [pf_ii_dlin_zero hγ hγ, div_self hγ.ne', pf_ii_J_one, one_mul]
    have hπ := Real.pi_pos
    have hs : 0 < Real.sqrt (2 * γ) := Real.sqrt_pos.2 (by positivity)
    field_simp
  refine ⟨pf_ii_dlin_zero hγin hγout, hsq, ?_⟩
  rintro rfl
  obtain ⟨ϑ, h1, h2, h3⟩ := pf_main β γin γin hβ0 hβ1 hγin hγout hε 0 le_rfl
  refine ⟨ϑ, h1, h2, h3, ?_⟩
  have hS := (pf_sPow_consts hβ0 hβ1).1
  rw [← pf_iii_dIso_zero, h3, hsq _ (mul_pos hS hγin), mul_assoc 2]
  have hπ := Real.pi_pos
  have hs : 0 < Real.sqrt (2 * (Muon.sPow β 2 * γin)) :=
    Real.sqrt_pos.2 (by positivity)
  field_simp

/-- `thm:app-iso-small-momentum`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1954–1980):
```latex
\begin{theorem}[Small aspect ratios with momentum]\label{thm:app-iso-small-momentum}
Let $\bmom\in[0,1)$ and $\gin,\gout>0$, and assume
$\varepsilon_\bmom\defeq6\gamma_\wedge(1-\bmom^2)\le\frac12$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ridge\ge0$ there is $\vartheta\in\big[1-\varepsilon_\bmom,(1-\varepsilon_\bmom)^{-1/2}\big]$ with
\[
\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gin,\gout)=\vartheta\;\mathfrak d_{\mathrm{lin}}(\sw2\gin,\sw2\gout;\ridge).
\]
\item With $r\defeq\gout/\gin$ and $J_r$ of \cref{thm:app-iso-small},
\[
\mathfrak d_{\mathrm{lin}}(\gin,\gout;0)=\frac{r\,J_r}{\sqrt{2\gout}},\qquad
\mathfrak d_{\mathrm{lin}}(\gamma,\gamma;0)=\frac{8}{3\pi\sqrt{2\gamma}} .
\]
In particular, in the square case $C_\bmom(\gamma)=8\vartheta/(3\pi\sqrt{2\sw2\gamma})$
with $\vartheta$ of (i) at $\ridge=0$.
\item If $6\gamma_\wedge\le\frac12$, then for every $\bmom\in[0,1)$
\[
\big(1-6\gamma_\wedge\big)^{3/2}\le\frac{C_\bmom(\gin,\gout)}{\sw2^{-1/2}\,C_0(\gin,\gout)}\le\big(1-6\gamma_\wedge\big)^{-3/2}.
\]
\item For every $\ridge\ge0$,
\[
(1-\varepsilon_\bmom)\big(1-6\sw2\gamma_\wedge\big)^{1/2}\le
\frac{\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gin,\gout)}{\mathfrak d_{\mathrm{iso}}(\ridge;0,\sw2\gin,\sw2\gout)}\le
(1-\varepsilon_\bmom)^{-1/2}\big(1-6\sw2\gamma_\wedge\big)^{-1}.
\]
\end{enumerate}
\end{theorem}
```

Part (iii). Its own hypothesis `6γ∧ ≤ 1/2` is the premise, and `β'` ranges over `[0,1)` as in the paper. `C_0 = Cbeta 0`.
-/
theorem thm_app_iso_small_momentum_iii (β γin γout : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hε : 6 * min γin γout * (1 - β ^ 2) ≤ 1 / 2) :
    6 * min γin γout ≤ 1 / 2 →
      ∀ β' : ℝ, 0 ≤ β' → β' < 1 →
        (1 - 6 * min γin γout) ^ (3 / 2 : ℝ) ≤
            Cbeta β' γin γout / (Muon.sPow β' 2 ^ (-(1 / 2 : ℝ)) * Cbeta 0 γin γout) ∧
          Cbeta β' γin γout / (Muon.sPow β' 2 ^ (-(1 / 2 : ℝ)) * Cbeta 0 γin γout) ≤
            (1 - 6 * min γin γout) ^ (-(3 / 2 : ℝ)) := by
  intro h6 β' hβ'0 hβ'1
  have hm : 0 < min γin γout := lt_min hγin hγout
  have hD := pf_iii_dlin_pos hγin hγout
  have hS' := (pf_sPow_consts hβ'0 hβ'1).1
  have hε' : 6 * min γin γout * (1 - β' ^ 2) ≤ 1 / 2 := by
    nlinarith [mul_nonneg hm.le (sq_nonneg β')]
  have hε0 : 6 * min γin γout * (1 - (0 : ℝ) ^ 2) ≤ 1 / 2 := by
    have h01 : (1 : ℝ) - 0 ^ 2 = 1 := by norm_num
    rw [h01, mul_one]; exact h6
  obtain ⟨ϑ', hϑlo, hϑhi, hϑeq⟩ :=
    pf_main β' γin γout hβ'0 hβ'1 hγin hγout hε' 0 le_rfl
  obtain ⟨ϑ0, hϑ0lo, hϑ0hi, hϑ0eq⟩ :=
    pf_main 0 γin γout le_rfl zero_lt_one hγin hγout hε0 0 le_rfl
  rw [pf_iii_dIso_zero, pf_iii_dlin_scale hS' hγin hγout] at hϑeq
  rw [pf_iii_dIso_zero] at hϑ0eq
  simp only [pf_iii_sPow_zero, one_mul] at hϑ0eq
  have e0 : (1 - 6 * min γin γout * (1 - (0 : ℝ) ^ 2)) = 1 - 6 * min γin γout := by ring
  rw [e0] at hϑ0lo hϑ0hi
  have ha : 0 < 1 - 6 * min γin γout := by linarith
  have hk : 0 < Muon.sPow β' 2 ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hS' _
  have hratio : Cbeta β' γin γout / (Muon.sPow β' 2 ^ (-(1 / 2 : ℝ)) * Cbeta 0 γin γout)
      = ϑ' / ϑ0 := by
    have hϑ0pos : 0 < ϑ0 := by linarith
    rw [hϑeq, hϑ0eq]
    have hDne := hD.ne'
    have hkne := hk.ne'
    have hϑ0ne := hϑ0pos.ne'
    field_simp
  rw [hratio]
  have hϑ0pos : 0 < ϑ0 := by linarith
  have hpow_half : 0 < (1 - 6 * min γin γout) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ha _
  have h1 : (1 - 6 * min γin γout) ^ (-(1 / 2 : ℝ)) * (1 - 6 * min γin γout) ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add ha]; norm_num
  have hA32 : (1 - 6 * min γin γout) ^ (3 / 2 : ℝ)
      = (1 - 6 * min γin γout) * (1 - 6 * min γin γout) ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ha, Real.rpow_one]
  have hAm : (1 - 6 * min γin γout) ^ (-(1 / 2 : ℝ))
      = (1 - 6 * min γin γout) ^ (-(3 / 2 : ℝ)) * (1 - 6 * min γin γout) := by
    conv_lhs => rw [show (-(1 / 2 : ℝ)) = -(3 / 2) + 1 by norm_num]
    rw [Real.rpow_add ha, Real.rpow_one]
  have hϑ'lo' : 1 - 6 * min γin γout ≤ ϑ' := by
    nlinarith [mul_nonneg hm.le (sq_nonneg β')]
  have hϑ0hi' : ϑ0 * (1 - 6 * min γin γout) ^ (1 / 2 : ℝ) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hϑ0hi hpow_half.le
    linarith [h1, this]
  have hbase : 1 - 6 * min γin γout ≤ 1 - 6 * min γin γout * (1 - β' ^ 2) := by
    nlinarith [mul_nonneg hm.le (sq_nonneg β')]
  have hϑ'hi' : ϑ' ≤ (1 - 6 * min γin γout) ^ (-(1 / 2 : ℝ)) :=
    le_trans hϑhi (Real.rpow_le_rpow_of_nonpos ha hbase (by norm_num))
  constructor
  · rw [le_div_iff₀ hϑ0pos, hA32]
    nlinarith [mul_le_mul_of_nonneg_left hϑ0hi' ha.le]
  · rw [div_le_iff₀ hϑ0pos]
    calc ϑ' ≤ (1 - 6 * min γin γout) ^ (-(1 / 2 : ℝ)) := hϑ'hi'
      _ = (1 - 6 * min γin γout) ^ (-(3 / 2 : ℝ)) * (1 - 6 * min γin γout) := hAm
      _ ≤ (1 - 6 * min γin γout) ^ (-(3 / 2 : ℝ)) * ϑ0 :=
          mul_le_mul_of_nonneg_left hϑ0lo (Real.rpow_nonneg ha.le _)

/-- Pair-free helper (`thm:app-iso-small-momentum` at `β = 0`, card §6.8): the square
small-aspect asymptotic `C(γ) ∼ 8/(3π√(2γ))` as `γ ↓ 0`, with `C(γ) = Cbeta 0 γ γ`
(`thm:app-iso-small`(iii)). -/
theorem C0_small_asymp :
    Tendsto (fun γ : ℝ => Cbeta 0 γ γ / (8 / (3 * Real.pi * Real.sqrt (2 * γ))))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hlow : Tendsto (fun γ : ℝ => 1 - 6 * γ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous (fun γ : ℝ => 1 - 6 * γ) := by fun_prop
    have h : Tendsto (fun γ : ℝ => 1 - 6 * γ) (𝓝[>] (0 : ℝ)) (𝓝 (1 - 6 * 0)) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h
  have hup := hlow.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at hup
  have key : ∀ᶠ γ in 𝓝[>] (0 : ℝ),
      1 - 6 * γ ≤ Cbeta 0 γ γ / (8 / (3 * Real.pi * Real.sqrt (2 * γ))) ∧
        Cbeta 0 γ γ / (8 / (3 * Real.pi * Real.sqrt (2 * γ))) ≤ (1 - 6 * γ) ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 12)] with γ hγ
    have hγ0 : 0 < γ := hγ.1
    have hγ1 : γ < 1 / 12 := hγ.2
    have hεγ : 6 * min γ γ * (1 - (0 : ℝ) ^ 2) ≤ 1 / 2 := by
      rw [min_self]; nlinarith
    obtain ⟨ϑ, h1, h2, _, hC⟩ :=
      (thm_app_iso_small_momentum_ii 0 γ γ le_rfl zero_lt_one hγ0 hγ0 hεγ).2.2 rfl
    rw [show (1 : ℝ) - 6 * min γ γ * (1 - (0 : ℝ) ^ 2) = 1 - 6 * γ by rw [min_self]; ring] at h1 h2
    simp only [pf_iii_sPow_zero, mul_one] at hC
    have hratio : Cbeta 0 γ γ / (8 / (3 * Real.pi * Real.sqrt (2 * γ))) = ϑ := by
      rw [hC]
      have hπ := Real.pi_pos
      have hs : 0 < Real.sqrt (2 * γ) := Real.sqrt_pos.2 (by linarith)
      field_simp
    rw [hratio]
    exact ⟨h1, h2⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup (key.mono fun γ h => h.1)
    (key.mono fun γ h => h.2)

/-! ### Private helpers for `thm_app_iso_small_momentum_iv` (task P-F.5.P4) -/

private lemma pf_iv_min_scale {S γin γout : ℝ} (hS : 0 ≤ S) :
    S * min γin γout = min (S * γin) (S * γout) := by
  rcases le_total γin γout with h | h
  · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h hS)]
  · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h hS)]

private lemma pf_iv_dlin_pos {γin γout ϱ : ℝ} (hγin : 0 < γin) (hγout : 0 < γout)
    (hϱ : 0 ≤ ϱ) : 0 < isoDlin γin γout ϱ := by
  unfold isoDlin
  have hK : 0 < Real.sqrt 2 / (Real.pi * γin * γout) := by positivity
  refine mul_pos hK ?_
  have hint := pf_Yc_integrable (ϱ := ϱ) hγin hγout one_pos hϱ
  simp only [div_one] at hint
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun v : ℝ => isoYroot γin γout (ϱ + v ^ 2)) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ (fun v hv => ?_)
    have hv' : (0 : ℝ) < v := hv
    exact (pf_Y_basic hγin hγout (add_pos_of_nonneg_of_pos hϱ (pow_pos hv' 2))).1
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  have hsub : Ioi (0 : ℝ) ⊆
      Function.support (fun v : ℝ => isoYroot γin γout (ϱ + v ^ 2)) ∩ Ioi (0 : ℝ) := by
    intro v hv
    have hv' : (0 : ℝ) < v := hv
    refine ⟨Function.mem_support.2 ?_, hv⟩
    exact (pf_iii_Y_pos hγin hγout (add_pos_of_nonneg_of_pos hϱ (pow_pos hv' 2))).ne'
  exact lt_of_lt_of_le (by simp) (measure_mono hsub)

/-- `thm:app-iso-small-momentum`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1954–1980):
```latex
\begin{theorem}[Small aspect ratios with momentum]\label{thm:app-iso-small-momentum}
Let $\bmom\in[0,1)$ and $\gin,\gout>0$, and assume
$\varepsilon_\bmom\defeq6\gamma_\wedge(1-\bmom^2)\le\frac12$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ridge\ge0$ there is $\vartheta\in\big[1-\varepsilon_\bmom,(1-\varepsilon_\bmom)^{-1/2}\big]$ with
\[
\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gin,\gout)=\vartheta\;\mathfrak d_{\mathrm{lin}}(\sw2\gin,\sw2\gout;\ridge).
\]
\item With $r\defeq\gout/\gin$ and $J_r$ of \cref{thm:app-iso-small},
\[
\mathfrak d_{\mathrm{lin}}(\gin,\gout;0)=\frac{r\,J_r}{\sqrt{2\gout}},\qquad
\mathfrak d_{\mathrm{lin}}(\gamma,\gamma;0)=\frac{8}{3\pi\sqrt{2\gamma}} .
\]
In particular, in the square case $C_\bmom(\gamma)=8\vartheta/(3\pi\sqrt{2\sw2\gamma})$
with $\vartheta$ of (i) at $\ridge=0$.
\item If $6\gamma_\wedge\le\frac12$, then for every $\bmom\in[0,1)$
\[
\big(1-6\gamma_\wedge\big)^{3/2}\le\frac{C_\bmom(\gin,\gout)}{\sw2^{-1/2}\,C_0(\gin,\gout)}\le\big(1-6\gamma_\wedge\big)^{-3/2}.
\]
\item For every $\ridge\ge0$,
\[
(1-\varepsilon_\bmom)\big(1-6\sw2\gamma_\wedge\big)^{1/2}\le
\frac{\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gin,\gout)}{\mathfrak d_{\mathrm{iso}}(\ridge;0,\sw2\gin,\sw2\gout)}\le
(1-\varepsilon_\bmom)^{-1/2}\big(1-6\sw2\gamma_\wedge\big)^{-1}.
\]
\end{enumerate}
\end{theorem}
```

Part (iv). The ratio is `d_iso(ϱ;β,γin,γout) / d_iso(ϱ;0,sw2 γin,sw2 γout)`; the bound's `6 sw2 γ∧` uses `γ∧ = min γin γout` before scaling.
-/
theorem thm_app_iso_small_momentum_iv (β γin γout : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hε : 6 * min γin γout * (1 - β ^ 2) ≤ 1 / 2) :
    ∀ ϱ : ℝ, 0 ≤ ϱ →
      (1 - 6 * min γin γout * (1 - β ^ 2)) * (1 - 6 * Muon.sPow β 2 * min γin γout) ^ (1 / 2 : ℝ) ≤
          dIso β γin γout ϱ / dIso 0 (Muon.sPow β 2 * γin) (Muon.sPow β 2 * γout) ϱ ∧
        dIso β γin γout ϱ / dIso 0 (Muon.sPow β 2 * γin) (Muon.sPow β 2 * γout) ϱ ≤
          (1 - 6 * min γin γout * (1 - β ^ 2)) ^ (-(1 / 2 : ℝ)) *
            (1 - 6 * Muon.sPow β 2 * min γin γout)⁻¹ := by
  intro ϱ hϱ
  have hm : 0 < min γin γout := lt_min hγin hγout
  have hSpos : 0 < Muon.sPow β 2 := (pf_sPow_consts hβ0 hβ1).1
  have hS0 : 0 ≤ Muon.sPow β 2 := hSpos.le
  have hd2 : 0 < 1 - β ^ 2 := by nlinarith
  have hSeq : Muon.sPow β 2 = (1 - β) ^ 2 / (1 - β ^ 2) := Muon.sPow_eq hβ0 hβ1 le_rfl
  have hSle : Muon.sPow β 2 ≤ 1 - β ^ 2 := by
    rw [hSeq, div_le_iff₀ hd2]
    nlinarith [mul_nonneg (sq_nonneg (1 - β)) (add_nonneg (by linarith : (0:ℝ) ≤ 2 * β) (sq_nonneg β))]
  have hS6 : 6 * Muon.sPow β 2 * min γin γout ≤ 1 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hSle hm.le, hε]
  have ha : 0 < 1 - 6 * Muon.sPow β 2 * min γin γout := by linarith
  have hε1 : 0 ≤ 1 - 6 * min γin γout * (1 - β ^ 2) := by linarith
  have hmin := pf_iv_min_scale (γin := γin) (γout := γout) hS0
  have hεz : 6 * min (Muon.sPow β 2 * γin) (Muon.sPow β 2 * γout) * (1 - (0:ℝ) ^ 2) ≤ 1 / 2 := by
    rw [← hmin, show (1 : ℝ) - 0 ^ 2 = 1 by norm_num, mul_one]
    linarith [hS6]
  obtain ⟨ϑ, h1, h2, h3⟩ := pf_main β γin γout hβ0 hβ1 hγin hγout hε ϱ hϱ
  obtain ⟨ϑ0, g1, g2, g3⟩ := pf_main 0 (Muon.sPow β 2 * γin) (Muon.sPow β 2 * γout)
    le_rfl zero_lt_one (mul_pos hSpos hγin) (mul_pos hSpos hγout) hεz ϱ hϱ
  simp only [pf_iii_sPow_zero, one_mul] at g3
  have hA : (1 : ℝ) - 6 * min (Muon.sPow β 2 * γin) (Muon.sPow β 2 * γout) * (1 - (0:ℝ) ^ 2)
      = 1 - 6 * Muon.sPow β 2 * min γin γout := by
    rw [← hmin]; ring
  rw [hA] at g1 g2
  have hD := pf_iv_dlin_pos (mul_pos hSpos hγin) (mul_pos hSpos hγout) hϱ
  rw [h3, g3, mul_div_mul_right _ _ hD.ne']
  have hpow_half : 0 < (1 - 6 * Muon.sPow β 2 * min γin γout) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos ha _
  have hinv : (1 - 6 * Muon.sPow β 2 * min γin γout) ^ (-(1 / 2 : ℝ))
      * (1 - 6 * Muon.sPow β 2 * min γin γout) ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add ha]; norm_num
  have hk : ϑ0 * (1 - 6 * Muon.sPow β 2 * min γin γout) ^ (1 / 2 : ℝ) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right g2 hpow_half.le
    linarith [hinv]
  have hϑ0pos : 0 < ϑ0 := by linarith
  have hq : 1 ≤ (1 - 6 * Muon.sPow β 2 * min γin γout)⁻¹ * ϑ0 := by
    rw [inv_mul_eq_div, le_div_iff₀ ha]; linarith
  have hU0 : 0 ≤ (1 - 6 * min γin γout * (1 - β ^ 2)) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg hε1 _
  constructor
  · rw [le_div_iff₀ hϑ0pos]
    nlinarith [mul_le_mul_of_nonneg_left hk hε1]
  · rw [div_le_iff₀ hϑ0pos]
    nlinarith [mul_le_mul_of_nonneg_left hq hU0]

/-- `prop:app-iso-one-momentum`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.3754–3764):
```latex
\begin{proposition}[Aspect ratio one with momentum]\label{prop:app-iso-one-momentum}
Let $\bmom\in(0,1)$. Then
\[
C_\bmom(1)=\frac{\sqrt2}\pi\int_0^1\Big[\sqrt{Q_m}\,\Lw(Q_m)+\tfrac12\Lambda_\bmom(Q_m)\Big]\dif m,
\]
$C_\bmom(1)\to C_0(1)$ as $\bmom\downarrow0$, and if $1-\bmom^2\le\frac1{12}$, then
\[
C_\bmom(1)=\frac{8\vartheta}{3\pi\sqrt{2\sw2}}\qquad\text{for some}\quad
\vartheta\in\Big[1-6(1-\bmom^2),\ \big(1-6(1-\bmom^2)\big)^{-1/2}\Big].
\]
\end{proposition}
```

Part (iii): the closed form near `β = 1` with the bracket `ϑ`, using `Muon.sPow β 2 = Σ_2`. 
Relocated here from `Muon.Isotropic.ZeroRidge` by the coordinator (2026-10-24): its proof needs results of this
module, which imports the original one. -/
theorem prop_app_iso_one_momentum_iii {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : 1 - β ^ 2 ≤ 1 / 12) :
    ∃ ϑ : ℝ, (1 - 6 * (1 - β ^ 2) ≤ ϑ ∧ ϑ ≤ (1 - 6 * (1 - β ^ 2)) ^ (-(1 / 2 : ℝ))) ∧
      Cbeta β 1 1 = 8 * ϑ / (3 * Real.pi * Real.sqrt (2 * Muon.sPow β 2)) := by
  have hε : 6 * min (1 : ℝ) 1 * (1 - β ^ 2) ≤ 1 / 2 := by
    rw [min_self]; linarith
  obtain ⟨ϑ, h1, h2, -, h4⟩ := (thm_app_iso_small_momentum_ii β 1 1 hβ0.le hβ1
    one_pos one_pos hε).2.2 rfl
  simp only [min_self, mul_one] at h1 h2 h4
  exact ⟨ϑ, ⟨h1, h2⟩, h4⟩

end Muon.Isotropic

end

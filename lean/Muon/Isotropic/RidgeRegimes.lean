import Muon.Isotropic.VolRates

/-!
# Appendix F: ridge regimes (task L-F.11)

Snapshot `cr-2026-10-23`. Source: `sections/05b-isotropic/section.tex`. Labels of this package:
`lem:app-iso-ridge-excess`, `thm:app-iso-vol-ridge`, `thm:app-iso-fixed-ridge`,
`cor:app-iso-fixed-ridge`, `thm:app-iso-crossover`, with the constants and the participation split
they use. Card: `sections/05b-isotropic/CARD.md` §2, §3, §5 (L-F.11).

Reuse: `lagCoeff` (`C̄_{1,ℓ}(ϱ)`), `isoQpsi`, `isoDivDiff`, `isoWeightJ`, `isoUlev`, `isoDeltaHat`
of `VolKernels`; `psiIso`, `dIso` of `ZeroRidge`; `isoC`, `isoC'`, `isoCpp`, `isoKk`, `isoCpl`,
`isoLbar2`, `isoM1`, `isoM2`, `isoEbar`, `isoPhi`, `isoGammaCirc` of their modules.

Conventions of this file.
* The volatility `𝔳_iso(ϱ)` is `N · isoVolRatio β γ ϱ`, where `isoVolRatio` is the explicit object
  `ψ(ϱ)/γ + 2 ∑_{ℓ≥1} C̄_{1,ℓ}(ϱ)` (the displayed form of `thm:app-iso-vol-ridge` l.3424–3425,
  with `C̄_{1,0}(ϱ) = ψ(ϱ)/γ` as the definition). The record form `v_iso` and the identity
  `v_iso = N · isoVolRatio` are the bridge of L-F.12 and are not stated here.
  Every statement using a series carries an explicit `Summable` conjunct, so no `tsum` is
  left to junk values.
* The split `C̄_{1,ℓ}(ϱ) = C̄°_ℓ(ϱ) + C̄♯_ℓ(ϱ)` is taken at the level of the representation of
  `prop:app-iso-vol-representation` (an `ENNReal` lower integral), so the excess sum is a
  `tsum` in `ENNReal` with no junk values.
* `ψ(ϱ) ∈ (0, γ)` is not a hypothesis: it follows from `β ∈ (0,1)`, `γ > 0`, `ϱ > 0` via
  `lem_app_iso_weights_i` and `lem_app_iso_comparison_i`. The values of `𝒫` used are on `[0,1]`.
-/

open MeasureTheory Set Filter Topology Asymptotics

noncomputable section

namespace Muon.Isotropic

/-! ## Constants -/

/-
`𝖪_6` and `𝖪_J` (`section.tex` l.3146–3148). 

`section.tex` l.3146-3148 (snapshot `cr-2026-10-23`, verbatim):
\mathsf K_6\defeq\max\Big(8,\ \frac{32\,\bar{\mathsf e}_\bmom^2}{\Phi(1)^2}\Big),\qquad
\mathsf K_{\rm J}\defeq\frac{3.2+2\log2}{1-\bmom^2}+\big(9.6+4e^{1/2}\log2\big)\bar{\mathsf e}_\bmom,
\]
-/

/--
`𝖪_6 = max(8, 32 ē²/Φ(1)²)`. -/
def isoK6 (β : ℝ) : ℝ := max 8 (32 * isoEbar β ^ 2 / isoPhi 1 ^ 2)

/-- `𝖪_J = (3.2 + 2 log 2)/(1 − β²) + (9.6 + 4 e^{1/2} log 2) ē_β`. -/
def isoKJ (β : ℝ) : ℝ :=
  (3.2 + 2 * Real.log 2) / (1 - β ^ 2) + (9.6 + 4 * Real.exp (1 / 2) * Real.log 2) * isoEbar β

/-
The two excess constants `𝖪^♭_ex`, `𝖪^♯_ex` (`section.tex` l.3149–3157). 

`section.tex` l.3149-3157 (snapshot `cr-2026-10-23`, verbatim):
\[
\begin{aligned}
\mathsf K^\flat_{\rm ex}\defeq\frac{\mathsf K_6}{\pi^2}\Big[&\frac{\bar{\mathsf e}_\bmom}{2\log(1/\bmom)}\Big(\frac{\pi^4}6+56\,\zeta(3)\log2\Big)\\
&+4\log2\Big(\bar{\mathsf e}_\bmom(\pi^2+2\log2)(\mathsf c_\bmom+1)+\mathsf K_{\rm J}\Big(3.64+\frac3{\log(1/\bmom)}\Big)\Big)\Big],
\end{aligned}
\]
\[
\mathsf K^\sharp_{\rm ex}\defeq\frac{\mathsf K_6}{\pi^2}\,4\log2\;\bar{\mathsf e}_\bmom\big(\pi^2+2\log2\big).
\]
-/

/-- `𝖪^♭_ex` of `lem:app-iso-ridge-excess`. -/
def isoKexFlat (β : ℝ) : ℝ :=
  isoK6 β / Real.pi ^ 2 *
    (isoEbar β / (2 * Real.log (1 / β)) * (Real.pi ^ 4 / 6 + 56 * (riemannZeta 3).re * Real.log 2)
      + 4 * Real.log 2 *
        (isoEbar β * (Real.pi ^ 2 + 2 * Real.log 2) * (isoC β + 1)
          + isoKJ β * (3.64 + 3 / Real.log (1 / β))))

/-- `𝖪^♯_ex = (𝖪_6/π²) 4 log 2 ē_β (π² + 2 log 2)` of `lem:app-iso-ridge-excess`. -/
def isoKexSharp (β : ℝ) : ℝ :=
  isoK6 β / Real.pi ^ 2 * 4 * Real.log 2 * isoEbar β * (Real.pi ^ 2 + 2 * Real.log 2)

/-
`𝖪_7`, `𝖪_8`, `𝖪^∘`, `𝖪^♭`, `𝖪^♯` (`section.tex` l.3267–3278). 

`section.tex` l.3267-3278 (snapshot `cr-2026-10-23`, verbatim):
Define, with $\bar{\mathsf L}_2$ of \cref{lem:app-iso-low-levels},
\[
\mathsf K_7\defeq3\bar{\mathsf e}_\bmom+\frac{3\bar{\mathsf e}_\bmom^2}{\Phi(1)}+\big(\bar{\mathsf e}_\bmom+\mathsf c^+_\bmom+1\big)\Big(1+\frac{3\bar{\mathsf e}_\bmom}{\Phi(1)}\Big)+\frac{3\big(\bar{\mathsf e}_\bmom^2+(\mathsf c^+_\bmom)^2+1\big)}{2\Phi(1)},
\]
\[
\mathsf K_8\defeq6\bar{\mathsf e}_\bmom+\frac{6\bar{\mathsf e}_\bmom^2}{\Phi(1)}+4\mathsf K_7+\frac{8\bar{\mathsf e}_\bmom}{\Phi(1)}\big(3\bar{\mathsf e}_\bmom+\mathsf K_7\big),
\]
\[
\mathsf K^\circ_\bmom\defeq6\bar{\mathsf e}_\bmom(\mathsf M_1+1)+\frac32,\qquad
\mathsf K^\flat_\bmom\defeq\mathsf K_8\bar{\mathsf L}_2+\mathsf K^\flat_{\rm ex},\qquad
\mathsf K^\sharp_\bmom\defeq\mathsf K_8(1+\mathsf M_2)+\mathsf K^\sharp_{\rm ex},
\]
-/

/-- `𝖪_7` (with `c⁺_β = isoCpl β`). -/
def isoK7 (β : ℝ) : ℝ :=
  3 * isoEbar β + 3 * isoEbar β ^ 2 / isoPhi 1
    + (isoEbar β + isoCpl β + 1) * (1 + 3 * isoEbar β / isoPhi 1)
    + 3 * (isoEbar β ^ 2 + isoCpl β ^ 2 + 1) / (2 * isoPhi 1)

/-- `𝖪_8`. -/
def isoK8 (β : ℝ) : ℝ :=
  6 * isoEbar β + 6 * isoEbar β ^ 2 / isoPhi 1 + 4 * isoK7 β
    + 8 * isoEbar β / isoPhi 1 * (3 * isoEbar β + isoK7 β)

/-- `𝖪^∘_β = 6 ē_β (𝖬_1 + 1) + 3/2`. -/
def isoKcirc (β : ℝ) : ℝ := 6 * isoEbar β * (isoM1 + 1) + 3 / 2

/-- `𝖪^♭_β = 𝖪_8 L̄_2 + 𝖪^♭_ex`. -/
def isoKflat (β : ℝ) : ℝ := isoK8 β * isoLbar2 β + isoKexFlat β

/-- `𝖪^♯_β = 𝖪_8 (1 + 𝖬_2) + 𝖪^♯_ex`. -/
def isoKsharp (β : ℝ) : ℝ := isoK8 β * (1 + isoM2) + isoKexSharp β

/-! ## The participation split of the lag coefficient -/

/-- The representation integral of `prop:app-iso-vol-representation` with the factor
`u_ϱ(y) u_ϱ(z_ℓ)` replaced by `wt (u_ϱ(y) u_ϱ(z_ℓ))`, as an `ENNReal` lower integral:
`(1/(π²γ³)) ∫∫ 1{y<Q_ψ, z_ℓ<Q_ψ} 𝔇(y,z) 𝗃(y) 𝗃(z_ℓ)/Δ̂(y,z) · wt(u_ϱ(y)u_ϱ(z_ℓ)) dy dz`
with `z_ℓ = z/β^{2ℓ}`. With `wt = id` this is `C̄_{1,ℓ}(ϱ)` by `prop:app-iso-vol-representation`. -/
def isoRepCoeffEN (β γ ϱ : ℝ) (ℓ : ℕ) (wt : ℝ → ℝ) : ENNReal :=
  ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3)) *
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal
        ((if p.1 < isoQpsi β γ ϱ ∧ p.2 / β ^ (2 * ℓ) < isoQpsi β γ ϱ then (1 : ℝ) else 0) *
          (isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 * isoWeightJ β γ (p.2 / β ^ (2 * ℓ)) /
            isoDeltaHat β γ p.1 p.2) *
          wt (isoUlev β γ ϱ p.1 * isoUlev β γ ϱ (p.2 / β ^ (2 * ℓ))))

/-- `C̄°_ℓ(ϱ)`: the main part, with both factors `u_ϱ` replaced by `1`
(`section.tex` l.3136–3140, "$\overline C^{\,\circ}_{\ell}$ is the right side of
(representation) with both factors $\mathsf u_\ridge$ replaced by $1$"). -/
def isoCircLag (β γ ϱ : ℝ) (ℓ : ℕ) : ENNReal := isoRepCoeffEN β γ ϱ ℓ (fun _ => 1)

/-- `C̄♯_ℓ(ϱ)`: the excess, with the factor `u_ϱ(y)u_ϱ(z_ℓ) − 1 ≥ 0`
(`section.tex` l.3138–3142). -/
def isoSharpLag (β γ ϱ : ℝ) (ℓ : ℕ) : ENNReal := isoRepCoeffEN β γ ϱ ℓ (fun t => t - 1)

/-! ## Crossover functions and the explicit volatility object -/

/-- `𝒫(x)` of `eqn:app-iso-crossover-P` (`section.tex` l.3280–3282): `𝒫(x) = 1/2 − (1−x)²/2 + (1−x)² log(1−x)`
for `0 ≤ x < 1`, and `𝒫(1) = 1/2`. Its values for `x > 1` are not used. -/
def isoCrossP (x : ℝ) : ℝ :=
  if x < 1 then 1 / 2 - (1 - x) ^ 2 / 2 + (1 - x) ^ 2 * Real.log (1 - x) else 1 / 2

/-- `Ξ(c) = (c∧1)(1 − (c∧1)/2)/√π` of `thm:app-iso-crossover`. -/
def isoCrossXi (c : ℝ) : ℝ := min c 1 * (1 - min c 1 / 2) / Real.sqrt Real.pi

/-- `𝔭_β(ϱ) = log(1/ϱ)/(2 log(1/β))` (`section.tex` l.1932). -/
def isoPfrak (β ϱ : ℝ) : ℝ := Real.log (1 / ϱ) / (2 * Real.log (1 / β))

/-- `𝔭̂_β(ϱ) = log((1−β)² γ_in γ_out/ϱ)/(2 log(1/β))` (`eqn:app-iso-count-hat`). -/
def isoPhat (β γin γout ϱ : ℝ) : ℝ :=
  Real.log ((1 - β) ^ 2 * γin * γout / ϱ) / (2 * Real.log (1 / β))

/-- The fixed-ridge threshold `e_β = max(𝖼'_β, 𝖼_β + 2(𝔭̂ + 𝖼'_β)/(log(1/β) γ_∧))`
(`thm:app-iso-fixed-ridge`), with `g = γ_∧`, `p = 𝔭̂`. -/
def isoEfix (β g p : ℝ) : ℝ :=
  max (isoC' β) (isoC β + 2 * (p + isoC' β) / (Real.log (1 / β) * g))

/-- `v_iso(ϱ)/N` in explicit form `ψ(ϱ)/γ + 2 ∑_{ℓ≥1} C̄_{1,ℓ}(ϱ)`, the displayed form of
`thm:app-iso-vol-ridge` (`section.tex` l.3424–3425) with `C̄_{1,0}(ϱ) = ψ(ϱ)/γ` as definition.
The series is summable in each statement below by an explicit conjunct. -/
def isoVolRatio (β γ ϱ : ℝ) : ℝ :=
  psiIso β γ γ ϱ / γ + 2 * ∑' ℓ : ℕ, lagCoeff β γ ϱ (ℓ + 1)

/-! ## Private helpers for the ridge excess (task P-F.11.P1) -/

/-- `ϖ(ζ) = (1 − e^{−ζ})^{−1/2} − 1`. -/
private def rrVarpi (ζ : ℝ) : ℝ := (1 - Real.exp (-ζ)) ^ (-(1 / 2 : ℝ)) - 1

/-- `f(w) = (1 + w) e^{−w/2}`. -/
private def rrF (w : ℝ) : ℝ := (1 + w) * Real.exp (-w / 2)


private lemma rrS_pos {ζ : ℝ} (hζ : 0 < ζ) : 0 < 1 - Real.exp (-ζ) := by
  have : Real.exp (-ζ) < 1 := by simpa using Real.exp_lt_exp.mpr (neg_lt_zero.mpr hζ)
  linarith

private lemma rrS_lt_one (ζ : ℝ) : 1 - Real.exp (-ζ) < 1 := by
  have := Real.exp_pos (-ζ); linarith

private lemma rrVarpi_nonneg {ζ : ℝ} (hζ : 0 < ζ) : 0 ≤ rrVarpi ζ := by
  unfold rrVarpi
  have h0 := rrS_pos hζ
  have h1 := rrS_lt_one ζ
  have : (1:ℝ) ≤ (1 - Real.exp (-ζ)) ^ (-(1 / 2 : ℝ)) := by
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1.le (by norm_num)
  linarith

private lemma rrVarpi_antitoneOn : AntitoneOn rrVarpi (Ioi 0) := by
  intro a ha b hb hab
  unfold rrVarpi
  have ha' : 0 < a := ha
  have h0 := rrS_pos ha'
  have : 1 - Real.exp (-a) ≤ 1 - Real.exp (-b) := by
    have := Real.exp_le_exp.mpr (neg_le_neg hab); linarith
  have := Real.rpow_le_rpow_of_nonpos h0 this (by norm_num : -(1/2:ℝ) ≤ 0)
  linarith

private lemma rrVarpi_lt_of_one_le {ζ : ℝ} (hζ : 1 ≤ ζ) : rrVarpi ζ < 3 / 5 := by
  unfold rrVarpi
  have he : Real.exp (-ζ) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have he1 : Real.exp (-1) < 2 / 5 := by
    rw [Real.exp_neg]
    have := Real.exp_one_gt_d9
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have hx : (3 : ℝ) / 5 ≤ 1 - Real.exp (-ζ) := by linarith
  have h1 : (1 - Real.exp (-ζ)) ^ (-(1 / 2 : ℝ)) ≤ (3 / 5 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by norm_num)
  have h2 : (3 / 5 : ℝ) ^ (-(1 / 2 : ℝ)) < 8 / 5 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    have : (5 : ℝ) / 8 < Real.sqrt (3 / 5) := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    rw [inv_lt_comm₀ (by linarith) (by norm_num)]
    linarith
  linarith

private lemma rrVarpi_measurable : Measurable rrVarpi := by
  unfold rrVarpi
  fun_prop


private lemma rrG_deriv {ζ : ℝ} (hζ : 0 < ζ) :
    HasDerivAt (fun x : ℝ => 2 * Real.log (1 + Real.sqrt (1 - Real.exp (-x)))) (rrVarpi ζ) ζ := by
  have hs := rrS_pos hζ
  have h1 : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) (Real.exp (-ζ)) ζ := by
    have := (hasDerivAt_const ζ (1:ℝ)).sub ((Real.hasDerivAt_exp (-ζ)).comp ζ (hasDerivAt_neg ζ))
    convert this using 1
    · funext x; simp
    · ring
  have h2 := h1.sqrt hs.ne'
  have hq : 0 < Real.sqrt (1 - Real.exp (-ζ)) := Real.sqrt_pos.mpr hs
  have h3 := ((h2.const_add 1).log (by positivity)).const_mul 2
  refine h3.congr_deriv ?_
  unfold rrVarpi
  have hsq : Real.sqrt (1 - Real.exp (-ζ)) ^ 2 = 1 - Real.exp (-ζ) := Real.sq_sqrt hs.le
  have hr : (1 - Real.exp (-ζ)) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (1 - Real.exp (-ζ)))⁻¹ := by
    rw [Real.rpow_neg hs.le, Real.sqrt_eq_rpow]
  rw [hr]
  set q := Real.sqrt (1 - Real.exp (-ζ))
  have he : Real.exp (-ζ) = 1 - q ^ 2 := by linarith
  rw [he]
  field_simp
  ring

private lemma rrVarpi_lintegral :
    ∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (rrVarpi ζ) = ENNReal.ofReal (2 * Real.log 2) := by
  set G : ℝ → ℝ := fun x => 2 * Real.log (1 + Real.sqrt (1 - Real.exp (-x))) with hG
  have hcont : ContinuousWithinAt G (Ici 0) 0 := by
    apply Continuous.continuousWithinAt
    rw [hG]
    apply Continuous.mul continuous_const
    apply Continuous.log (by fun_prop)
    intro x; have := Real.sqrt_nonneg (1 - Real.exp (-x)); linarith
  have hder : ∀ x ∈ Ioi (0:ℝ), HasDerivAt G (rrVarpi x) x := fun x hx => rrG_deriv hx
  have hnn : ∀ x ∈ Ioi (0:ℝ), 0 ≤ rrVarpi x := fun x hx => rrVarpi_nonneg hx
  have htend : Tendsto G atTop (nhds (2 * Real.log 2)) := by
    have h1 : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (nhds 0) := by
      simpa using Real.tendsto_exp_neg_atTop_nhds_zero
    have h2 : Tendsto (fun x : ℝ => 1 + Real.sqrt (1 - Real.exp (-x))) atTop (nhds 2) := by
      have := (((tendsto_const_nhds (x := (1:ℝ))).sub h1).sqrt).const_add 1
      simpa [one_add_one_eq_two] using this
    have h3 := (h2.log (by norm_num)).const_mul 2
    exact h3
  have hI := integral_Ioi_of_hasDerivAt_of_nonneg hcont hder hnn htend
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hder hnn htend
  have hG0 : G 0 = 0 := by simp [hG]
  rw [hG0, sub_zero] at hI
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · rw [hI]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hnn x hx


private lemma rrExpInt {c : ℝ} (hc : 0 < c) :
    ∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (ζ * Real.exp (-(c * ζ))) = ENNReal.ofReal (1 / c ^ 2) := by
  set G : ℝ → ℝ := fun x => -(x / c + 1 / c ^ 2) * Real.exp (-(c * x)) with hG
  have hder : ∀ x ∈ Ioi (0:ℝ), HasDerivAt G (x * Real.exp (-(c * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-(c * x))) (Real.exp (-(c * x)) * (-c)) x := by
      have := ((hasDerivAt_id x).const_mul c).neg.exp
      convert this using 1 <;> simp [Pi.neg_apply]
    have h2 : HasDerivAt (fun x : ℝ => -(x / c + 1 / c ^ 2)) (-(1 / c)) x := by
      have := (((hasDerivAt_id x).div_const c).add_const (1 / c ^ 2)).neg
      convert this using 1
      · funext x; simp [Pi.neg_apply]
    have := h2.mul h1
    convert this using 1
    field_simp
    ring
  have hnn : ∀ x ∈ Ioi (0:ℝ), 0 ≤ x * Real.exp (-(c * x)) := fun x hx =>
    mul_nonneg (le_of_lt hx) (Real.exp_pos _).le
  have hcont : ContinuousWithinAt G (Ici 0) 0 := by
    apply Continuous.continuousWithinAt
    rw [hG]; fun_prop
  have htend : Tendsto G atTop (nhds 0) := by
    have hy : Tendsto (fun x : ℝ => c * x) atTop atTop := tendsto_id.const_mul_atTop hc
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hy
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp hy
    have h3 := (h1.add h2).const_mul (-(1 / c ^ 2))
    have h5 : Tendsto G atTop (nhds (-(1 / c ^ 2) * (0 + 0))) := by
      refine h3.congr (fun x => ?_)
      simp only [hG, Function.comp]; field_simp
    simpa using h5
  have hI := integral_Ioi_of_hasDerivAt_of_nonneg hcont hder hnn htend
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hder hnn htend
  have hG0 : G 0 = -(1 / c ^ 2) := by simp [hG]
  rw [hG0] at hI
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · rw [hI]; simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hnn x hx


private lemma rrVarpi_le_geom {ζ : ℝ} (hζ : 0 < ζ) :
    rrVarpi ζ ≤ Real.exp (-ζ) / (1 - Real.exp (-ζ)) := by
  have hs := rrS_pos hζ
  unfold rrVarpi
  have hr : (1 - Real.exp (-ζ)) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (1 - Real.exp (-ζ)))⁻¹ := by
    rw [Real.rpow_neg hs.le, Real.sqrt_eq_rpow]
  rw [hr]
  have hq : 0 < Real.sqrt (1 - Real.exp (-ζ)) := Real.sqrt_pos.mpr hs
  have hsq : Real.sqrt (1 - Real.exp (-ζ)) ^ 2 = 1 - Real.exp (-ζ) := Real.sq_sqrt hs.le
  have hle : Real.sqrt (1 - Real.exp (-ζ)) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact (rrS_lt_one ζ).le
  set q := Real.sqrt (1 - Real.exp (-ζ))
  have he : Real.exp (-ζ) = 1 - q ^ 2 := by linarith
  rw [he, show 1 - (1 - q ^ 2) = q ^ 2 by ring]
  rw [inv_eq_one_div, div_sub_one hq.ne', div_le_div_iff₀ hq (by positivity)]
  nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hle)]

private lemma rrGeom_tsum {ζ : ℝ} (hζ : 0 < ζ) :
    HasSum (fun n : ℕ => Real.exp (-(((n : ℝ) + 1) * ζ))) (Real.exp (-ζ) / (1 - Real.exp (-ζ))) := by
  have he0 : 0 ≤ Real.exp (-ζ) := (Real.exp_pos _).le
  have he1 : Real.exp (-ζ) < 1 := by simpa using Real.exp_lt_exp.mpr (neg_lt_zero.mpr hζ)
  have := (hasSum_geometric_of_lt_one he0 he1).mul_left (Real.exp (-ζ))
  convert this using 1
  · funext n
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  · field_simp

private lemma rrVarpi_zeta_lintegral :
    ∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (ζ * rrVarpi ζ) ≤ ENNReal.ofReal (Real.pi ^ 2 / 6) := by
  have hpt : ∀ ζ ∈ Ioi (0:ℝ), ENNReal.ofReal (ζ * rrVarpi ζ) ≤
      ∑' n : ℕ, ENNReal.ofReal (ζ * Real.exp (-(((n : ℝ) + 1) * ζ))) := by
    intro ζ hζ
    have hζ' : 0 < ζ := hζ
    have hsum := (rrGeom_tsum hζ').mul_left ζ
    have hnn : ∀ n : ℕ, 0 ≤ ζ * Real.exp (-(((n : ℝ) + 1) * ζ)) := fun n =>
      mul_nonneg hζ'.le (Real.exp_pos _).le
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable, hsum.tsum_eq]
    apply ENNReal.ofReal_le_ofReal
    calc ζ * rrVarpi ζ ≤ ζ * (Real.exp (-ζ) / (1 - Real.exp (-ζ))) :=
          mul_le_mul_of_nonneg_left (rrVarpi_le_geom hζ') hζ'.le
      _ = _ := rfl
  calc ∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (ζ * rrVarpi ζ)
      ≤ ∫⁻ ζ in Ioi (0:ℝ), ∑' n : ℕ, ENNReal.ofReal (ζ * Real.exp (-(((n : ℝ) + 1) * ζ))) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ∑' n : ℕ, ∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (ζ * Real.exp (-(((n : ℝ) + 1) * ζ))) := by
        rw [lintegral_tsum]
        intro n
        exact (by fun_prop : Measurable fun ζ : ℝ => ENNReal.ofReal (ζ * Real.exp (-(((n : ℝ) + 1) * ζ)))).aemeasurable
    _ = ∑' n : ℕ, ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2) := by
        congr 1; funext n
        exact rrExpInt (by positivity)
    _ = ENNReal.ofReal (Real.pi ^ 2 / 6) := by
        have h1 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
          have := (hasSum_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr
            (by simpa using hasSum_zeta_two)
          simpa using this
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) h1.summable, h1.tsum_eq]




private lemma rrF2_2d {G : ℝ → ENNReal} (hG : Measurable G) :
    ∫⁻ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), G (p.1 + p.2) =
      ∫⁻ τ in Ioi (0:ℝ), ENNReal.ofReal τ * G τ := by
  have hS : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  set H : ℝ × ℝ → ENNReal := fun q => (Ioi (0:ℝ)).indicator (fun _ => (1:ENNReal)) q.1 *
    (Ioi (0:ℝ)).indicator (fun _ => (1:ENNReal)) (q.2 - q.1) * G q.2 with hH
  have hHm : Measurable H := by
    refine Measurable.mul (Measurable.mul ?_ ?_) (hG.comp measurable_snd)
    · exact (measurable_const.indicator measurableSet_Ioi).comp measurable_fst
    · exact (measurable_const.indicator measurableSet_Ioi).comp (measurable_snd.sub measurable_fst)
  have hmp := MeasureTheory.measurePreserving_prod_add (volume : Measure ℝ) (volume : Measure ℝ)
  have h1 : ∫⁻ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), G (p.1 + p.2) = ∫⁻ p : ℝ × ℝ, H ((p.1, p.1 + p.2)) := by
    rw [← lintegral_indicator hS]
    refine lintegral_congr fun p => ?_
    simp only [indicator, H, mem_prod, mem_Ioi, add_sub_cancel_left]
    by_cases h1 : 0 < p.1 <;> by_cases h2 : 0 < p.2 <;> simp [h1, h2]
  have h2 : ∫⁻ p : ℝ × ℝ, H ((p.1, p.1 + p.2)) = ∫⁻ q, H q := hmp.lintegral_comp hHm
  rw [h1, h2, Measure.volume_eq_prod, lintegral_prod_symm _ hHm.aemeasurable]
  have h3 : ∀ τ : ℝ, ∫⁻ a, H (a, τ) = ENNReal.ofReal τ * G τ := by
    intro τ
    have : ∀ a : ℝ, H (a, τ) = (Ioo 0 τ).indicator (fun _ => G τ) a := by
      intro a
      simp only [H, indicator, mem_Ioi, mem_Ioo]
      have e : 0 < τ - a ↔ a < τ := sub_pos
      by_cases h1 : 0 < a <;> by_cases h2 : a < τ <;> simp [h1, h2, e]
    simp_rw [this]
    rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo, sub_zero, mul_comm]
  simp_rw [h3]
  symm
  refine setLIntegral_eq_of_support_subset ?_
  intro τ hτ
  by_contra h
  simp only [mem_Ioi, not_lt] at h
  simp [Function.mem_support, ENNReal.ofReal_of_nonpos h] at hτ


private lemma rrF2_SR_pos {τ : ℝ} (hτ : 0 < τ) : isoSinhRatio τ = τ / (2 * Real.sinh (τ / 2)) := by
  simp [isoSinhRatio, hτ.ne']

private lemma rrF2_SR_nonneg (w : ℝ) : 0 ≤ isoSinhRatio w := by
  unfold isoSinhRatio
  split_ifs with h
  · norm_num
  · rcases lt_or_gt_of_ne h with h | h
    · have : Real.sinh (w / 2) < 0 := Real.sinh_neg_iff.2 (by linarith)
      exact div_nonneg_of_nonpos h.le (by linarith)
    · have : 0 < Real.sinh (w / 2) := Real.sinh_pos_iff.2 (by linarith)
      positivity

private lemma rrF2_SR_meas : Measurable isoSinhRatio := by
  unfold isoSinhRatio
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

private lemma rrF2_Nu {Φ : ℝ → ℝ} (hΦ : Measurable Φ) :
    ∫⁻ w, ENNReal.ofReal (Φ (w.2.1 + w.2.2)) ∂isoNuStar =
      ENNReal.ofReal (2 / Real.pi ^ 2) *
        ∫⁻ τ in Ioi (0:ℝ), ENNReal.ofReal (isoSinhRatio τ * Φ τ) := by
  have hsf : SFinite isoNuBase := by unfold isoNuBase; infer_instance
  have hS : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hmeas : Measurable fun w : Bool × ℝ × ℝ => ENNReal.ofReal (Φ (w.2.1 + w.2.2)) :=
    (hΦ.comp (by fun_prop)).ennreal_ofReal
  have hρ : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))) := by
    fun_prop
  have hΦ' : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Φ (p.1 + p.2)) :=
    (hΦ.comp (by fun_prop)).ennreal_ofReal
  have step1 : ∫⁻ w, ENNReal.ofReal (Φ (w.2.1 + w.2.2)) ∂isoNuStar =
      2 * ∫⁻ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ),
        ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))) *
          ENNReal.ofReal (Φ (p.1 + p.2)) := by
    unfold isoNuStar
    rw [lintegral_prod _ hmeas.aemeasurable, lintegral_count, tsum_fintype, Fintype.sum_bool,
      ← two_mul]
    congr 1
    unfold isoNuBase
    rw [lintegral_withDensity_eq_lintegral_mul _ hρ hΦ']
    rfl
  rw [step1]
  have hG : Measurable fun τ : ℝ =>
      ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh (τ / 2)))) * ENNReal.ofReal (Φ τ) := by
    fun_prop
  have := rrF2_2d hG
  rw [this]
  have hpt : ∀ τ ∈ Ioi (0:ℝ), ENNReal.ofReal τ *
      (ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh (τ / 2)))) * ENNReal.ofReal (Φ τ)) =
      ENNReal.ofReal (1 / Real.pi ^ 2) * ENNReal.ofReal (isoSinhRatio τ * Φ τ) := by
    intro τ hτ
    have hτ : 0 < τ := hτ
    have hs : 0 < Real.sinh (τ / 2) := Real.sinh_pos_iff.2 (by linarith)
    rw [← mul_assoc, ← ENNReal.ofReal_mul hτ.le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), rrF2_SR_pos hτ]
    congr 1
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring


private lemma rrF2_Even {F : ℝ → ENNReal} (_hF : Measurable F) (he : ∀ x, F (-x) = F x) :
    ∫⁻ x, F x = 2 * ∫⁻ x in Ioi (0:ℝ), F x := by
  have h1 := lintegral_add_compl (μ := volume) F (measurableSet_Ioi (a := (0:ℝ)))
  rw [compl_Ioi] at h1
  have h2 : ∫⁻ x in Iic (0:ℝ), F x = ∫⁻ x in Iio (0:ℝ), F x := by
    rw [Measure.restrict_congr_set Iio_ae_eq_Iic]
  have h3 : ∫⁻ x in Iio (0:ℝ), F x = ∫⁻ x in Ioi (0:ℝ), F x := by
    rw [← lintegral_indicator measurableSet_Iio, ← lintegral_indicator measurableSet_Ioi,
      ← lintegral_neg_eq_self]
    refine lintegral_congr fun x => ?_
    simp only [indicator, mem_Iio, mem_Ioi, he, Left.neg_neg_iff]
  rw [← h1, h2, h3, two_mul]

private lemma rrSinh_nonneg (w : ℝ) : 0 ≤ isoSinhRatio w := rrF2_SR_nonneg w
private lemma rrSinh_measurable : Measurable isoSinhRatio := rrF2_SR_meas

private lemma rrF2_Half : ∫⁻ τ in Ioi (0:ℝ), ENNReal.ofReal (isoSinhRatio τ) =
    ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  have hmass := (lem_app_iso_averaging_i (β := 1/2) (by norm_num) (by norm_num)).1
  have h := rrF2_Nu (Φ := fun _ => 1) measurable_const
  have h1 : ∫⁻ w, ENNReal.ofReal ((fun _ : ℝ => (1:ℝ)) (w.2.1 + w.2.2)) ∂isoNuStar = 1 := by
    simp [measure_univ]
  rw [h1] at h
  simp only [mul_one] at h
  have hpi : (0:ℝ) < Real.pi ^ 2 := by positivity
  have hne : ENNReal.ofReal (2 / Real.pi ^ 2) ≠ 0 := by
    simp; positivity
  have : ∫⁻ τ in Ioi (0:ℝ), ENNReal.ofReal (isoSinhRatio τ) =
      (ENNReal.ofReal (2 / Real.pi ^ 2))⁻¹ := by
    exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h.symm)
  rw [this, ← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  field_simp


private lemma rrSinh_lintegral : ∫⁻ w : ℝ, ENNReal.ofReal (isoSinhRatio |w|) =
    ENNReal.ofReal (Real.pi ^ 2) := by
  rw [rrF2_Even (F := fun w => ENNReal.ofReal (isoSinhRatio |w|))
    (by exact (rrF2_SR_meas.comp measurable_abs).ennreal_ofReal) (by intro x; simp)]
  have : ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (isoSinhRatio |x|) =
      ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (isoSinhRatio x) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [abs_of_pos hx]
  rw [this, rrF2_Half, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring

private lemma rrF2_zeta3_pos : 0 < (riemannZeta 3).re := by
  have h : (riemannZeta ((3:ℕ) : ℂ)).re = ∑' n : ℕ, 1 / (n : ℝ) ^ 3 := by
    rw [zeta_nat_eq_tsum_of_gt_one (by omega)]
    have : (∑' n : ℕ, 1 / (n : ℂ) ^ 3) = ((∑' n : ℕ, 1 / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      refine tsum_congr fun n => ?_
      push_cast; rfl
    rw [this, Complex.ofReal_re]
  have h3 : (riemannZeta 3) = riemannZeta ((3:ℕ) : ℂ) := by norm_num
  rw [h3, h]
  refine (Real.summable_one_div_nat_pow.2 (by norm_num)).tsum_pos (fun n => by positivity) 1 ?_
  norm_num

private lemma rrF2_Ae : ∀ᵐ w ∂isoNuStar, 0 < w.2.1 ∧ 0 < w.2.2 := by
  have hsf : SFinite isoNuBase := by unfold isoNuBase; infer_instance
  have hS : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  rw [ae_iff]
  have hsub : {w : Bool × ℝ × ℝ | ¬(0 < w.2.1 ∧ 0 < w.2.2)} ⊆
      (univ : Set Bool) ×ˢ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))ᶜ := by
    intro w hw
    refine ⟨mem_univ _, ?_⟩
    intro h
    exact hw ⟨h.1, h.2⟩
  refine measure_mono_null hsub ?_
  unfold isoNuStar
  rw [Measure.prod_prod]
  have : isoNuBase (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))ᶜ = 0 := by
    unfold isoNuBase
    rw [withDensity_apply _ hS.compl, Measure.restrict_restrict hS.compl, compl_inter_self,
      Measure.restrict_empty, lintegral_zero_measure]
  rw [this, mul_zero]

private lemma rrSinh_abs_lintegral : ∫⁻ w : ℝ, ENNReal.ofReal (|w| * isoSinhRatio |w|) =
    ENNReal.ofReal (28 * (riemannZeta 3).re) := by
  have hz := rrF2_zeta3_pos
  have hM := (lem_app_iso_averaging_ii).1
  have h := rrF2_Nu (Φ := fun x => x) measurable_id
  have hnn : 0 ≤ᵐ[isoNuStar] fun w : Bool × ℝ × ℝ => w.2.1 + w.2.2 := by
    filter_upwards [rrF2_Ae] with w hw
    exact (add_pos hw.1 hw.2).le
  have hI := integral_eq_lintegral_of_nonneg_ae hnn (by fun_prop)
  rw [h] at hI
  set L := ∫⁻ τ in Ioi (0:ℝ), ENNReal.ofReal (isoSinhRatio τ * τ) with hL
  have hpi : (0:ℝ) < Real.pi ^ 2 := by positivity
  have hLtop : L ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simp; positivity)] at hI
    simp at hI
    rw [hI] at hM
    have : 0 < 28 * (riemannZeta 3).re / Real.pi ^ 2 := by positivity
    linarith
  have hLr : L = ENNReal.ofReal L.toReal := (ENNReal.ofReal_toReal hLtop).symm
  rw [hM, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hI
  have hLv : L.toReal = 14 * (riemannZeta 3).re := by
    field_simp at hI
    linarith
  rw [rrF2_Even (F := fun w => ENNReal.ofReal (|w| * isoSinhRatio |w|))
    (by exact ((measurable_abs.mul (rrF2_SR_meas.comp measurable_abs))).ennreal_ofReal)
    (by intro x; simp)]
  have : ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (|x| * isoSinhRatio |x|) = L := by
    rw [hL]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx' : 0 < x := hx
    rw [abs_of_pos hx', mul_comm]
  rw [this, hLr, hLv, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring


private lemma rrF_hasDeriv (w : ℝ) : HasDerivAt rrF (Real.exp (-w / 2) * (1 - w) / 2) w := by
  unfold rrF
  have h1 : HasDerivAt (fun w : ℝ => 1 + w) 1 w := by simpa using (hasDerivAt_id w).const_add 1
  have h2 : HasDerivAt (fun w : ℝ => Real.exp (-w / 2)) (Real.exp (-w / 2) * (-1 / 2)) w := by
    have := (((hasDerivAt_id w).neg).div_const 2).exp
    simpa using this
  have := h1.mul h2
  convert this using 1
  ring

private lemma rrF_mono : MonotoneOn rrF (Icc 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
  · exact fun w _ => (rrF_hasDeriv w).continuousAt.continuousWithinAt
  · exact fun w _ => (rrF_hasDeriv w).differentiableAt.differentiableWithinAt
  · intro w hw
    rw [interior_Icc] at hw
    rw [(rrF_hasDeriv w).deriv]
    have := Real.exp_pos (-w / 2)
    have : 0 ≤ 1 - w := by linarith [hw.2]
    positivity

private lemma rrF_anti : AntitoneOn rrF (Ici 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
  · exact fun w _ => (rrF_hasDeriv w).continuousAt.continuousWithinAt
  · exact fun w _ => (rrF_hasDeriv w).differentiableAt.differentiableWithinAt
  · intro w hw
    rw [interior_Ici] at hw
    rw [(rrF_hasDeriv w).deriv]
    have := Real.exp_pos (-w / 2)
    have : 1 - w ≤ 0 := by linarith [hw.out]
    have : Real.exp (-w / 2) * (1 - w) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) this
    linarith

private lemma rrF_nonneg {w : ℝ} (hw : 0 ≤ w) : 0 ≤ rrF w := by
  unfold rrF; positivity

private lemma rrF_le_M {w : ℝ} (hw : 0 ≤ w) : rrF w ≤ 2 * Real.exp (-1 / 2) := by
  have h1 : rrF 1 = 2 * Real.exp (-1 / 2) := by unfold rrF; norm_num
  rw [← h1]
  rcases le_total w 1 with h | h
  · exact rrF_mono ⟨hw, h⟩ ⟨zero_le_one, le_rfl⟩ h
  · exact rrF_anti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h

private lemma rrM_le : 2 * (2 * Real.exp (-1 / 2)) ≤ 243 / 100 := by
  have he : Real.exp 1 = Real.exp (1/2) * Real.exp (1/2) := by rw [← Real.exp_add]; norm_num
  have h1 := Real.exp_one_gt_d9
  have hpos := Real.exp_pos (1/2)
  have hinv : Real.exp (-1 / 2) = (Real.exp (1/2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [hinv]
  have : (4:ℝ)/243*100 ≤ Real.exp (1/2) := by
    by_contra hc
    rw [not_le] at hc
    nlinarith
  rw [show 2 * (2 * (Real.exp (1 / 2))⁻¹) = 4 / Real.exp (1/2) by field_simp; ring, div_le_iff₀ hpos]
  nlinarith
private lemma rrF_integral :
    ∫⁻ w in Ioi (0:ℝ), ENNReal.ofReal (rrF w) = ENNReal.ofReal 6 := by
  set G : ℝ → ℝ := fun w => -((6 + 2 * w) * Real.exp (-w / 2)) with hG
  have hd : ∀ w ∈ Ioi (0:ℝ), HasDerivAt G (rrF w) w := by
    intro w _
    have h1 : HasDerivAt (fun w : ℝ => 6 + 2 * w) 2 w := by
      simpa using ((hasDerivAt_id w).const_mul 2).const_add 6
    have h2 : HasDerivAt (fun w : ℝ => Real.exp (-w / 2)) (Real.exp (-w / 2) * (-1 / 2)) w := by
      have := (((hasDerivAt_id w).neg).div_const 2).exp
      simpa using this
    have := (h1.mul h2).neg
    convert this using 1
    unfold rrF; ring
  have hc : ContinuousWithinAt G (Ici 0) 0 := by
    apply Continuous.continuousWithinAt
    simp only [hG]; fun_prop
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.atTop_mul_const (show (0:ℝ) < 1/2 by norm_num))
    have h0 := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_mul_const (show (0:ℝ) < 1/2 by norm_num))
    have h2 := (h.const_mul 4).add (h0.const_mul 6)
    have h3 := h2.neg
    convert h3 using 1
    · funext w
      simp only [hG, Function.comp, id]
      have : -w / 2 = -(w * (1/2)) := by ring
      rw [this]; ring
    · simp
  have hnn : ∀ w ∈ Ioi (0:ℝ), 0 ≤ rrF w := fun w hw => rrF_nonneg (le_of_lt hw)
  have hint := integrableOn_Ioi_deriv_of_nonneg hc hd hnn hlim
  have hI := integral_Ioi_of_hasDerivAt_of_nonneg hc hd hnn hlim
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioi hnn), hI]
  simp [hG]
private lemma rrAvg {h : ℝ} (hh : 0 < h) (a c : ℝ) (F : ℝ → ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) (hsub : Ico a (a + h) ⊆ S) (hc : ∀ s ∈ Ico a (a + h), c ≤ F s) :
    ENNReal.ofReal c ≤ ENNReal.ofReal (1 / h) * ∫⁻ s in S, ENNReal.ofReal (F s) := by
  have h1 : ENNReal.ofReal c * ENNReal.ofReal h ≤ ∫⁻ s in S, ENNReal.ofReal (F s) := by
    calc ENNReal.ofReal c * ENNReal.ofReal h
        = ∫⁻ s in Ico a (a + h), ENNReal.ofReal c := by
          rw [setLIntegral_const, Real.volume_Ico]; congr 2; ring_nf
      _ ≤ ∫⁻ s in Ico a (a + h), ENNReal.ofReal (F s) :=
          setLIntegral_mono' measurableSet_Ico (fun s hs => ENNReal.ofReal_le_ofReal (hc s hs))
      _ ≤ ∫⁻ s in S, ENNReal.ofReal (F s) := lintegral_mono_set hsub
  calc ENNReal.ofReal c
      = ENNReal.ofReal (1 / h) * (ENNReal.ofReal c * ENNReal.ofReal h) := by
        rw [← mul_assoc, mul_comm (ENNReal.ofReal (1/h)), mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        rw [show 1 / h * h = 1 by field_simp]; simp
    _ ≤ _ := by gcongr
private lemma rrE_count {h : ℝ} (hh : 0 < h) (t : ℝ) (c : ENNReal) :
    ∑' k : ℕ, (if (1 - h < t + h * ((k : ℝ) + 1) ∧ t + h * ((k : ℝ) + 1) < 1 + h) then c else 0)
      ≤ 2 * c := by
  classical
  by_cases hne : ∃ k : ℕ, (1 - h < t + h * ((k : ℝ) + 1) ∧ t + h * ((k : ℝ) + 1) < 1 + h)
  · set m := Nat.find hne with hm
    have hmspec := Nat.find_spec hne
    rw [← hm] at hmspec
    have hout : ∀ k ∉ ({m, m + 1} : Finset ℕ),
        (if (1 - h < t + h * ((k : ℝ) + 1) ∧ t + h * ((k : ℝ) + 1) < 1 + h) then c else 0) = 0 := by
      intro k hk
      rw [if_neg]
      intro hP
      have h1 : m ≤ k := Nat.find_min' hne hP
      have h2 : (k : ℝ) < m + 2 := by
        by_contra hcon
        rw [not_lt] at hcon
        nlinarith [hP.2, hmspec.1]
      have h3 : k < m + 2 := by exact_mod_cast h2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      omega
    rw [tsum_eq_sum hout, Finset.sum_pair (by omega)]
    calc _ ≤ c + c := by
          gcongr <;> split_ifs <;> simp
      _ = 2 * c := by rw [two_mul]
  · push Not at hne
    have : ∀ k : ℕ, (if (1 - h < t + h * ((k : ℝ) + 1) ∧ t + h * ((k : ℝ) + 1) < 1 + h) then c else 0) = 0 := by
      intro k
      rw [if_neg]
      intro hP
      exact absurd hP.2 (not_lt.mpr (hne k hP.1))
    simp [this]
private lemma rrB_sum {h : ℝ} (hh : 0 < h) (t : ℝ) :
    ∑' j : ℕ, ((∫⁻ s in (Ico (t + h * (j : ℝ)) (t + h * ((j : ℝ) + 1)) ∩ Ioo 0 1),
        ENNReal.ofReal (rrF s)) +
      ∫⁻ s in (Ico (t + h * (j : ℝ)) (t + h * ((j : ℝ) + 1)) ∩ Ici 1), ENNReal.ofReal (rrF s))
      ≤ ENNReal.ofReal 6 := by
  set P : ℕ → Set ℝ := fun j => Ico (t + h * (j : ℝ)) (t + h * ((j : ℝ) + 1)) ∩ Ioi 0 with hP
  have hPm : ∀ j, MeasurableSet (P j) := fun j => measurableSet_Ico.inter measurableSet_Ioi
  have hPd : Pairwise (Function.onFun Disjoint P) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro s hs1 hs2
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
      have := hs1.1.2
      have := hs2.1.1
      nlinarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hlt
      have := hs1.1.1
      have := hs2.1.2
      nlinarith
  have hterm : ∀ j : ℕ, ((∫⁻ s in (Ico (t + h * (j : ℝ)) (t + h * ((j : ℝ) + 1)) ∩ Ioo 0 1),
        ENNReal.ofReal (rrF s)) +
      ∫⁻ s in (Ico (t + h * (j : ℝ)) (t + h * ((j : ℝ) + 1)) ∩ Ici 1), ENNReal.ofReal (rrF s))
      ≤ ∫⁻ s in P j, ENNReal.ofReal (rrF s) := by
    intro j
    set I := Ico (t + h * (j : ℝ)) (t + h * ((j : ℝ) + 1))
    have hdisj : Disjoint (I ∩ Ioo 0 1) (I ∩ Ici 1) := by
      rw [Set.disjoint_left]
      intro s hs1 hs2
      exact absurd hs2.2 (not_le.mpr hs1.2.2)
    rw [← lintegral_union (measurableSet_Ico.inter measurableSet_Ici) hdisj]
    apply lintegral_mono_set
    intro s hs
    rcases hs with hs | hs
    · exact ⟨hs.1, hs.2.1⟩
    · exact ⟨hs.1, show (0:ℝ) < s from lt_of_lt_of_le one_pos hs.2⟩
  calc _ ≤ ∑' j : ℕ, ∫⁻ s in P j, ENNReal.ofReal (rrF s) := ENNReal.tsum_le_tsum hterm
    _ = ∫⁻ s in ⋃ j, P j, ENNReal.ofReal (rrF s) := (lintegral_iUnion hPm hPd _).symm
    _ ≤ ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (rrF s) := by
        apply lintegral_mono_set
        intro s hs
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hs
        exact hj.2
    _ = ENNReal.ofReal 6 := rrF_integral
private lemma rrLattice {h : ℝ} (hh : 0 < h) (t : ℝ) :
    ∑' k : ℕ, ENNReal.ofReal (if 0 < t + h * ((k : ℝ) + 1) then rrF (t + h * ((k : ℝ) + 1)) else 0)
      ≤ ENNReal.ofReal (243 / 100 + 6 / h) := by
  classical
  set BL : ℕ → ENNReal := fun j => ∫⁻ s in (Ico (t + h * (j : ℝ)) (t + h * ((j : ℝ) + 1)) ∩ Ioo 0 1),
      ENNReal.ofReal (rrF s) with hBL
  set BR : ℕ → ENNReal := fun j => ∫⁻ s in (Ico (t + h * (j : ℝ)) (t + h * ((j : ℝ) + 1)) ∩ Ici 1),
      ENNReal.ofReal (rrF s) with hBR
  have key : ∀ k : ℕ, ENNReal.ofReal (if 0 < t + h * ((k : ℝ) + 1) then rrF (t + h * ((k : ℝ) + 1)) else 0)
      ≤ (if (1 - h < t + h * ((k : ℝ) + 1) ∧ t + h * ((k : ℝ) + 1) < 1 + h)
          then ENNReal.ofReal (2 * Real.exp (-1 / 2)) else 0)
        + ENNReal.ofReal (1 / h) * (BL (k + 1) + BR k) := by
    intro k
    set x := t + h * ((k : ℝ) + 1) with hx
    by_cases h0 : 0 < x
    · rw [if_pos h0]
      by_cases hL : x + h ≤ 1
      · have e1 : t + h * (((k + 1 : ℕ) : ℝ)) = x := by rw [hx]; push_cast; ring
        have e2 : t + h * (((k + 1 : ℕ) : ℝ) + 1) = x + h := by rw [hx]; push_cast; ring
        have := rrAvg hh x (rrF x) rrF (S := Ico (t + h * (((k + 1 : ℕ) : ℝ)))
            (t + h * (((k + 1 : ℕ) : ℝ) + 1)) ∩ Ioo 0 1)
          (measurableSet_Ico.inter measurableSet_Ioo)
          (by
            rw [e1, e2]
            intro s hs
            exact ⟨hs, by linarith [hs.1], by linarith [hs.2]⟩)
          (by
            intro s hs
            exact rrF_mono ⟨by linarith [hs.1], by linarith [hs.1]⟩
              ⟨by linarith [hs.1], by linarith [hs.2]⟩ hs.1)
        calc _ ≤ ENNReal.ofReal (1 / h) * BL (k + 1) := this
          _ ≤ _ := by
            refine le_trans ?_ le_add_self
            gcongr
            exact le_self_add
      · by_cases hR : 1 ≤ x - h
        · have e1 : t + h * ((k : ℝ)) = x - h := by rw [hx]; ring
          have e2 : t + h * ((k : ℝ) + 1) = x := rfl
          have := rrAvg hh (x - h) (rrF x) rrF (S := Ico (t + h * (k : ℝ))
              (t + h * ((k : ℝ) + 1)) ∩ Ici 1)
            (measurableSet_Ico.inter measurableSet_Ici)
            (by
              rw [e1]
              intro s hs
              exact ⟨⟨hs.1, by linarith [hs.2]⟩, le_trans hR hs.1⟩)
            (by
              intro s hs
              exact rrF_anti (Set.mem_Ici.mpr (le_trans hR hs.1)) (Set.mem_Ici.mpr (by linarith)) (by linarith [hs.2]))
          calc _ ≤ ENNReal.ofReal (1 / h) * BR k := this
            _ ≤ _ := by
              refine le_trans ?_ le_add_self
              gcongr
              exact le_add_self
        · have hP : 1 - h < x ∧ x < 1 + h := ⟨by linarith [not_le.mp hR], by linarith [not_le.mp hL]⟩
          rw [if_pos hP]
          refine le_trans ?_ le_self_add
          exact ENNReal.ofReal_le_ofReal (rrF_le_M h0.le)
    · rw [if_neg h0]; simp
  calc _ ≤ ∑' k : ℕ, ((if (1 - h < t + h * ((k : ℝ) + 1) ∧ t + h * ((k : ℝ) + 1) < 1 + h)
          then ENNReal.ofReal (2 * Real.exp (-1 / 2)) else 0)
        + ENNReal.ofReal (1 / h) * (BL (k + 1) + BR k)) := ENNReal.tsum_le_tsum key
    _ = (∑' k : ℕ, (if (1 - h < t + h * ((k : ℝ) + 1) ∧ t + h * ((k : ℝ) + 1) < 1 + h)
          then ENNReal.ofReal (2 * Real.exp (-1 / 2)) else 0))
        + ENNReal.ofReal (1 / h) * (∑' k : ℕ, BL (k + 1) + ∑' k : ℕ, BR k) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_add]
    _ ≤ 2 * ENNReal.ofReal (2 * Real.exp (-1 / 2)) + ENNReal.ofReal (1 / h) * ENNReal.ofReal 6 := by
        gcongr
        · exact rrE_count hh t _
        · calc ∑' k : ℕ, BL (k + 1) + ∑' k : ℕ, BR k ≤ ∑' j : ℕ, BL j + ∑' k : ℕ, BR k := by
                have hinj : ∑' k : ℕ, BL (k + 1) ≤ ∑' j : ℕ, BL j :=
                  ENNReal.tsum_comp_le_tsum_of_injective (f := fun k : ℕ => k + 1)
                    (add_left_injective 1) BL
                exact add_le_add hinj le_rfl
            _ = ∑' j : ℕ, (BL j + BR j) := (ENNReal.tsum_add).symm
            _ ≤ ENNReal.ofReal 6 := rrB_sum hh t
    _ = ENNReal.ofReal (2 * (2 * Real.exp (-1 / 2)) + 1 / h * 6) := by
        have e1 : (2 : ENNReal) * ENNReal.ofReal (2 * Real.exp (-1 / 2))
            = ENNReal.ofReal (2 * (2 * Real.exp (-1 / 2))) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
        have e2 : ENNReal.ofReal (1 / h) * ENNReal.ofReal 6 = ENNReal.ofReal (1 / h * 6) :=
          (ENNReal.ofReal_mul (by positivity)).symm
        rw [e1, e2, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (243 / 100 + 6 / h) := by
        apply ENNReal.ofReal_le_ofReal
        have := rrM_le
        have : 1 / h * 6 = 6 / h := by ring
        linarith


private lemma rr4_lint_sub (U : ℝ) (φ : ℝ → ENNReal) :
    ∫⁻ u in Iio U, φ (U - u) = ∫⁻ ζ in Ioi (0:ℝ), φ ζ := by
  have hmp := (volume : Measure ℝ).measurePreserving_sub_left U
  have hme := (Homeomorph.subLeft U).measurableEmbedding
  have := hmp.setLIntegral_comp_preimage_emb hme φ (Ioi 0)
  have hpre : (fun h : ℝ => U - h) ⁻¹' Ioi 0 = Iio U := by
    ext x; simp [sub_pos]
  rw [hpre] at this
  exact this

private lemma rr4_lint_shift (V0 v : ℝ) (φ : ℝ → ENNReal) :
    ∫⁻ u in Ioi V0, φ (u - v) = ∫⁻ w in Ioi (V0 - v), φ w := by
  have hmp := measurePreserving_sub_right (volume : Measure ℝ) v
  have hme := (Homeomorph.subRight v).measurableEmbedding
  have := hmp.setLIntegral_comp_preimage_emb hme φ (Ioi (V0 - v))
  have hpre : (fun h : ℝ => h - v) ⁻¹' Ioi (V0 - v) = Ioi V0 := by
    ext x; simp
  rw [hpre] at this
  exact this

private lemma rr4_exp_Iic (V0 : ℝ) :
    ∫⁻ u in Iic V0, ENNReal.ofReal (Real.exp (u / 2)) = ENNReal.ofReal (2 * Real.exp (V0 / 2)) := by
  have hi : IntegrableOn (fun u : ℝ => Real.exp (u / 2)) (Iic V0) := by
    have := integrableOn_exp_mul_Iic (a := (1/2 : ℝ)) (by norm_num) V0
    simpa [div_eq_inv_mul, mul_comm] using this
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  have := integral_exp_mul_Iic (a := (1/2 : ℝ)) (by norm_num) V0
  congr 1
  simp only [one_div] at this ⊢
  have h2 : ∀ u : ℝ, Real.exp (u / 2) = Real.exp (2⁻¹ * u) := fun u => by congr 1; ring
  simp_rw [h2]
  rw [this]; field_simp

private lemma rr4_f_Ioi (w1 : ℝ) (hw : 0 ≤ w1) :
    ∫⁻ w in Ioi w1, ENNReal.ofReal (rrF w) = ENNReal.ofReal ((6 + 2 * w1) * Real.exp (-w1 / 2)) := by
  have hd : ∀ x ∈ Ici w1, HasDerivAt (fun w : ℝ => -((6 + 2 * w) * Real.exp (-w / 2))) (rrF x) x := by
    intro x _
    have h1 : HasDerivAt (fun w : ℝ => Real.exp (-w / 2)) (Real.exp (-x / 2) * (-1 / 2)) x := by
      have := ((hasDerivAt_id x).neg.div_const 2).exp
      simpa using this
    have h2 : HasDerivAt (fun w : ℝ => 6 + 2 * w) 2 x := by
      simpa using ((hasDerivAt_id x).const_mul 2).const_add 6
    have := (h2.mul h1).neg
    convert this using 1
    simp only [rrF]; ring
  have ht : Filter.Tendsto (fun w : ℝ => -((6 + 2 * w) * Real.exp (-w / 2))) atTop (𝓝 0) := by
    have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
    have hh : Filter.Tendsto (fun w : ℝ => w / 2) atTop atTop :=
      Filter.tendsto_id.atTop_div_const (by norm_num)
    have a := h0.comp hh
    have b := h1.comp hh
    have c := ((b.const_mul 6).add (a.const_mul 4)).neg
    simp only [mul_zero, add_zero, neg_zero] at c
    refine c.congr (fun w => ?_)
    simp only [Function.comp]
    have : -w / 2 = -(w / 2) := by ring
    rw [this]; ring
  have hcont : ∀ x ∈ Ici w1, ContinuousWithinAt rrF (Ici w1) x := by
    intro x _; unfold rrF; fun_prop
  have hint : IntegrableOn rrF (Ioi w1) := by
    refine integrableOn_Ioi_deriv_of_nonneg (g := fun w : ℝ => -((6 + 2 * w) * Real.exp (-w / 2)))
      (l := 0) (by exact (hd w1 (Set.mem_Ici.mpr le_rfl)).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioi_subset_Ici_self hx)) (fun x hx => ?_) ht
    unfold rrF
    have : 0 ≤ x := by have := hx.out; linarith
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    unfold rrF
    have : 0 ≤ x := by have := hx.out; linarith
    positivity)]
  have := integral_Ioi_of_hasDerivAt_of_tendsto (hd w1 (Set.mem_Ici.mpr le_rfl)).continuousAt.continuousWithinAt
    (fun x hx => hd x (Ioi_subset_Ici_self hx)) hint ht
  rw [this]; congr 1; ring



private lemma rr4_f_le {w1 w : ℝ} (hw1 : 0 ≤ w1) (hw : w1 ≤ w) : rrF w ≤ 2 * rrF w1 := by
  unfold rrF
  set d := w - w1 with hd
  have hd0 : 0 ≤ d := by linarith
  have hexp : Real.exp (-w / 2) = Real.exp (-w1 / 2) * Real.exp (-d / 2) := by
    rw [← Real.exp_add]; congr 1; rw [hd]; ring
  have h1 : Real.exp (-d / 2) * (1 + d / 2) ≤ 1 := by
    have ht : d / 2 + 1 ≤ Real.exp (d / 2) := Real.add_one_le_exp _
    have hm : Real.exp (-d / 2) * Real.exp (d / 2) = 1 := by
      rw [← Real.exp_add]
      have : -d / 2 + d / 2 = 0 := by ring
      rw [this, Real.exp_zero]
    have := mul_le_mul_of_nonneg_left ht (Real.exp_pos (-d / 2)).le
    nlinarith
  have he : 0 ≤ Real.exp (-d / 2) := (Real.exp_pos _).le
  have hE1 : 0 < Real.exp (-w1 / 2) := Real.exp_pos _
  rw [hexp]
  have hw' : w = w1 + d := by rw [hd]; ring
  have key : (1 + w) * Real.exp (-d / 2) ≤ 2 * (1 + w1) := by
    have : 1 + w ≤ 2 * (1 + w1) * (1 + d / 2) := by rw [hw']; nlinarith [mul_nonneg hw1 hd0]
    calc (1 + w) * Real.exp (-d / 2) ≤ 2 * (1 + w1) * (1 + d / 2) * Real.exp (-d / 2) :=
          mul_le_mul_of_nonneg_right this he
      _ = 2 * (1 + w1) * (Real.exp (-d / 2) * (1 + d / 2)) := by ring
      _ ≤ 2 * (1 + w1) * 1 := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 2 * (1 + w1) := by ring
  calc (1 + w) * (Real.exp (-w1 / 2) * Real.exp (-d / 2))
      = ((1 + w) * Real.exp (-d / 2)) * Real.exp (-w1 / 2) := by ring
    _ ≤ (2 * (1 + w1)) * Real.exp (-w1 / 2) := mul_le_mul_of_nonneg_right key hE1.le
    _ = 2 * ((1 + w1) * Real.exp (-w1 / 2)) := by ring

private lemma rrIbound {U V0 v E S C1 : ℝ} (hv : v < V0) (hE : 0 < E) (hS : 0 ≤ S)
    (hSC : S * Real.exp V0 = C1) (Zb : ℝ → ℝ) (h0 : ∀ u, 0 ≤ Zb u)
    (hZ1 : ∀ u, Zb u ≤ E * rrF |u - v|) (hZ2 : ∀ u, Zb u ≤ S * Real.exp ((u + v) / 2)) :
    ∫⁻ u in Iio U, ENNReal.ofReal (Zb u * (1 + rrVarpi (U - u))) ≤
      ENNReal.ofReal (((32 / 10 + 2 * Real.log 2) * C1 + (96 / 10 + 4 * Real.exp (1 / 2) * Real.log 2) * E)
        * rrF (V0 - v)) := by
  set w1 := V0 - v with hw1
  have hw1pos : 0 < w1 := by rw [hw1]; linarith
  set c := S * Real.exp (v / 2) with hc
  have hc0 : 0 ≤ c := mul_nonneg hS (Real.exp_pos _).le
  set c0 := c * Real.exp (V0 / 2) with hc0def
  have hc00 : 0 ≤ c0 := mul_nonneg hc0 (Real.exp_pos _).le
  have hC1 : 0 ≤ C1 := by rw [← hSC]; exact mul_nonneg hS (Real.exp_pos _).le
  have hc0eq : c0 = C1 * Real.exp (-w1 / 2) := by
    rw [hc0def, hc, ← hSC]
    have e1 : Real.exp V0 = Real.exp (V0 / 2) * Real.exp (V0 / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-w1 / 2) * Real.exp (V0 / 2) = Real.exp (v / 2) := by
      rw [← Real.exp_add]; congr 1; rw [hw1]; ring
    rw [e1, ← e2]; ring
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- region split
  have hsplit := lintegral_inter_add_sdiff (μ := volume)
    (fun u => ENNReal.ofReal (Zb u * (1 + rrVarpi (U - u)))) (Iio U) (measurableSet_Iic (a := V0))
  rw [← hsplit]
  -- Part A
  have hA : ∫⁻ u in Iio U ∩ Iic V0, ENNReal.ofReal (Zb u * (1 + rrVarpi (U - u))) ≤
      ENNReal.ofReal (2 * c0) + ENNReal.ofReal (c0 * (2 * Real.log 2)) := by
    have h1 : ∫⁻ u in Iio U ∩ Iic V0, ENNReal.ofReal (Zb u * (1 + rrVarpi (U - u))) ≤
        ∫⁻ u in Iio U ∩ Iic V0, (ENNReal.ofReal (c * Real.exp (u / 2)) +
          ENNReal.ofReal (c0 * rrVarpi (U - u))) := by
      refine setLIntegral_mono' (measurableSet_Iio.inter measurableSet_Iic) (fun u hu => ?_)
      have huU : u < U := hu.1
      have huV : u ≤ V0 := hu.2
      have hvp : 0 ≤ rrVarpi (U - u) := rrVarpi_nonneg (by linarith)
      rw [← ENNReal.ofReal_add (mul_nonneg hc0 (Real.exp_pos _).le) (mul_nonneg hc00 hvp)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hz := hZ2 u
      have hexp : Real.exp ((u + v) / 2) = Real.exp (u / 2) * Real.exp (v / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      have hu2 : Real.exp (u / 2) ≤ Real.exp (V0 / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      have hZb : Zb u ≤ c * Real.exp (u / 2) := by
        rw [hexp] at hz; rw [hc]; nlinarith [hz]
      calc Zb u * (1 + rrVarpi (U - u)) ≤ (c * Real.exp (u / 2)) * (1 + rrVarpi (U - u)) :=
            mul_le_mul_of_nonneg_right hZb (by linarith)
        _ = c * Real.exp (u / 2) + c * Real.exp (u / 2) * rrVarpi (U - u) := by ring
        _ ≤ c * Real.exp (u / 2) + c0 * rrVarpi (U - u) := by
            have : c * Real.exp (u / 2) ≤ c0 := by
              rw [hc0def]; exact mul_le_mul_of_nonneg_left hu2 hc0
            nlinarith [mul_le_mul_of_nonneg_right this hvp]
    refine h1.trans ?_
    rw [lintegral_add_left (by fun_prop)]
    refine add_le_add ?_ ?_
    · calc ∫⁻ u in Iio U ∩ Iic V0, ENNReal.ofReal (c * Real.exp (u / 2))
          ≤ ∫⁻ u in Iic V0, ENNReal.ofReal (c * Real.exp (u / 2)) :=
            lintegral_mono_set Set.inter_subset_right
        _ = ENNReal.ofReal c * ∫⁻ u in Iic V0, ENNReal.ofReal (Real.exp (u / 2)) := by
            simp_rw [ENNReal.ofReal_mul hc0]
            rw [lintegral_const_mul _ (by fun_prop)]
        _ = ENNReal.ofReal (2 * c0) := by
            rw [rr4_exp_Iic, ← ENNReal.ofReal_mul hc0]; congr 1; rw [hc0def]; ring
    · calc ∫⁻ u in Iio U ∩ Iic V0, ENNReal.ofReal (c0 * rrVarpi (U - u))
          ≤ ∫⁻ u in Iio U, ENNReal.ofReal (c0 * rrVarpi (U - u)) :=
            lintegral_mono_set Set.inter_subset_left
        _ = ∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (c0 * rrVarpi ζ) :=
            rr4_lint_sub U (fun ζ => ENNReal.ofReal (c0 * rrVarpi ζ))
        _ = ENNReal.ofReal c0 * ∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (rrVarpi ζ) := by
            simp_rw [ENNReal.ofReal_mul hc00]
            rw [lintegral_const_mul _ rrVarpi_measurable.ennreal_ofReal]
        _ = ENNReal.ofReal (c0 * (2 * Real.log 2)) := by
            rw [rrVarpi_lintegral, ← ENNReal.ofReal_mul hc00]
  -- Part B
  have hB : ∫⁻ u in Iio U \ Iic V0, ENNReal.ofReal (Zb u * (1 + rrVarpi (U - u))) ≤
      ENNReal.ofReal (E * ((6 + 2 * w1) * Real.exp (-w1 / 2))) +
        ENNReal.ofReal (2 * E * rrF w1 * (2 * Real.log 2)) := by
    have hfw1 : 0 ≤ rrF w1 := by unfold rrF; positivity
    have h1 : ∫⁻ u in Iio U \ Iic V0, ENNReal.ofReal (Zb u * (1 + rrVarpi (U - u))) ≤
        ∫⁻ u in Iio U \ Iic V0, (ENNReal.ofReal (E * rrF (u - v)) +
          ENNReal.ofReal (2 * E * rrF w1 * rrVarpi (U - u))) := by
      refine setLIntegral_mono' (measurableSet_Iio.diff measurableSet_Iic) (fun u hu => ?_)
      have huU : u < U := hu.1
      have huV : V0 < u := not_le.mp hu.2
      have hvp : 0 ≤ rrVarpi (U - u) := rrVarpi_nonneg (by linarith)
      have hfu : 0 ≤ rrF (u - v) := by
        unfold rrF; have : 0 ≤ u - v := by linarith
        positivity
      rw [← ENNReal.ofReal_add (mul_nonneg hE.le hfu)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hE.le) hfw1) hvp)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hz := hZ1 u
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u - v)] at hz
      have hf := rr4_f_le hw1pos.le (by rw [hw1]; linarith : w1 ≤ u - v)
      calc Zb u * (1 + rrVarpi (U - u)) ≤ (E * rrF (u - v)) * (1 + rrVarpi (U - u)) :=
            mul_le_mul_of_nonneg_right hz (by linarith)
        _ = E * rrF (u - v) + E * rrF (u - v) * rrVarpi (U - u) := by ring
        _ ≤ E * rrF (u - v) + 2 * E * rrF w1 * rrVarpi (U - u) := by
            have : E * rrF (u - v) ≤ 2 * E * rrF w1 := by nlinarith [mul_le_mul_of_nonneg_left hf hE.le]
            nlinarith [mul_le_mul_of_nonneg_right this hvp]
    refine h1.trans ?_
    rw [lintegral_add_left (by unfold rrF; fun_prop)]
    refine add_le_add ?_ ?_
    · calc ∫⁻ u in Iio U \ Iic V0, ENNReal.ofReal (E * rrF (u - v))
          ≤ ∫⁻ u in Ioi V0, ENNReal.ofReal (E * rrF (u - v)) := by
            refine lintegral_mono_set (fun u hu => ?_)
            exact Set.mem_Ioi.mpr (not_le.mp (fun h => hu.2 h))
        _ = ∫⁻ w in Ioi w1, ENNReal.ofReal (E * rrF w) :=
            rr4_lint_shift V0 v (fun w => ENNReal.ofReal (E * rrF w))
        _ = ENNReal.ofReal E * ∫⁻ w in Ioi w1, ENNReal.ofReal (rrF w) := by
            have hm : Measurable (fun w : ℝ => ENNReal.ofReal (rrF w)) := by
              unfold rrF; fun_prop
            simp_rw [ENNReal.ofReal_mul hE.le]
            rw [lintegral_const_mul _ hm]
        _ = ENNReal.ofReal (E * ((6 + 2 * w1) * Real.exp (-w1 / 2))) := by
            rw [rr4_f_Ioi w1 hw1pos.le, ← ENNReal.ofReal_mul hE.le]
    · calc ∫⁻ u in Iio U \ Iic V0, ENNReal.ofReal (2 * E * rrF w1 * rrVarpi (U - u))
          ≤ ∫⁻ u in Iio U, ENNReal.ofReal (2 * E * rrF w1 * rrVarpi (U - u)) :=
            lintegral_mono_set Set.sdiff_subset
        _ = ∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (2 * E * rrF w1 * rrVarpi ζ) :=
            rr4_lint_sub U (fun ζ => ENNReal.ofReal (2 * E * rrF w1 * rrVarpi ζ))
        _ = ENNReal.ofReal (2 * E * rrF w1) * ∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (rrVarpi ζ) := by
            have hk : 0 ≤ 2 * E * rrF w1 := by positivity
            simp_rw [ENNReal.ofReal_mul hk]
            rw [lintegral_const_mul _ rrVarpi_measurable.ennreal_ofReal]
        _ = ENNReal.ofReal (2 * E * rrF w1 * (2 * Real.log 2)) := by
            have hk : 0 ≤ 2 * E * rrF w1 := by positivity
            rw [rrVarpi_lintegral, ← ENNReal.ofReal_mul hk]
  -- assembly
  refine (add_le_add hA hB).trans ?_
  have hfw1 : 0 ≤ rrF w1 := by unfold rrF; positivity
  have hexpw : Real.exp (-w1 / 2) ≤ rrF w1 := by
    unfold rrF; nlinarith [Real.exp_pos (-w1 / 2)]
  have hsq : 1 ≤ Real.exp (1 / 2) := Real.one_le_exp (by norm_num)
  have hexw : 0 < Real.exp (-w1 / 2) := Real.exp_pos _
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hc0eq]
  have hA1 : C1 * Real.exp (-w1 / 2) ≤ C1 * rrF w1 := mul_le_mul_of_nonneg_left hexpw hC1
  have hB1 : (6 + 2 * w1) * Real.exp (-w1 / 2) ≤ 6 * rrF w1 := by
    unfold rrF; nlinarith [Real.exp_pos (-w1 / 2)]
  have hB2 : E * ((6 + 2 * w1) * Real.exp (-w1 / 2)) ≤ E * (6 * rrF w1) :=
    mul_le_mul_of_nonneg_left hB1 hE.le
  have hl : 0 ≤ Real.log 2 * (E * rrF w1) := by positivity
  have h4 : Real.log 2 * (E * rrF w1) * (4 * 1) ≤ Real.log 2 * (E * rrF w1) * (4 * Real.exp (1 / 2)) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hl
  have hC2 : 0 ≤ C1 * rrF w1 * Real.log 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hA1 hlog2, mul_le_mul_of_nonneg_right hA1 (by norm_num : (0:ℝ) ≤ 2)]


section rf6
open Muon.DetEquiv (rW)

private lemma rrDivDiff_eq {β y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    isoDivDiff β y z = isoZkern β y z / (y * z) := by
  by_cases hyz : y = z
  · subst hyz
    unfold isoDivDiff isoZkern
    simp only [ite_true]
    unfold isoEslope
    rw [Real.sqrt_mul_self hy.le]
    field_simp
  · unfold isoDivDiff isoZkern
    rw [if_neg hyz, if_neg hyz]
    have hs : 0 < Real.sqrt (y * z) := Real.sqrt_pos.mpr (mul_pos hy hz)
    have hs2 : Real.sqrt (y * z) ^ 2 = y * z := Real.sq_sqrt (mul_pos hy hz).le
    have hyz' : y - z ≠ 0 := sub_ne_zero.mpr hyz
    field_simp
    rw [hs2]
    ring

private lemma rf6_weightSeq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Muon.DetEquiv.WeightSeq (Muon.emaW β) := by
  refine ⟨fun j => ?_, ?_, 0, ?_⟩
  · unfold Muon.emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  · unfold Muon.emaW
    exact (summable_geometric_of_lt_one hβ0 hβ1).mul_left _
  · unfold Muon.emaW
    rw [pow_zero, mul_one]
    exact (by linarith : (0:ℝ) < 1 - β).ne'

private lemma rf6_isoLink {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsIsoLink (rW (Muon.emaW β)) := by
  have h := lem_app_iso_weights_i hβ0.le hβ1
  refine ⟨fun q hq => (h.2.1 q (Set.mem_Ici.mp hq)).1.continuousWithinAt,
    (h.2.2.1 hβ0).1, ?_⟩
  unfold rW
  simp

private lemma rf6_root {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {s : ℝ} (hs : 0 < s) :
    0 < qIso β γ γ s ∧ rW (Muon.emaW β) (qIso β γ γ s) < γ ∧
      s * qIso β γ γ s = (γ - rW (Muon.emaW β) (qIso β γ γ s)) ^ 2 := by
  have hr := rf6_isoLink hβ0 hβ1
  obtain ⟨-, -, -, hroot, -, -⟩ := lem_app_iso_comparison_i hr hγ hγ
  obtain ⟨hD, hG⟩ := hroot s hs
  obtain ⟨hq0, hqr⟩ := hD
  rw [min_self] at hqr
  unfold isoG at hG
  have hq : qIso β γ γ s = isoRoot (rW (Muon.emaW β)) γ γ s := rfl
  rw [hq]
  refine ⟨?_, hqr, by nlinarith⟩
  rcases hq0.eq_or_lt with h | h
  · exfalso
    rw [← h] at hG
    have : rW (Muon.emaW β) 0 = 0 := hr.2.2
    rw [this] at hG
    nlinarith
  · exact h

private lemma rf6_isoRoot_resid {β γ s y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y)
    (h : y < isoRoot (rW (Muon.emaW β)) γ γ s) : rW (Muon.emaW β) y < γ := by
  unfold isoRoot at h
  split_ifs at h with hex
  · obtain ⟨hD, _⟩ := hex.choose_spec
    obtain ⟨hQ0, hQr⟩ := hD
    rw [min_self] at hQr
    have hmono := ((lem_app_iso_weights_i hβ0.le hβ1).2.2.1 hβ0).1
    have := hmono (Set.mem_Ici.mpr hy.le) (Set.mem_Ici.mpr hQ0) h
    linarith
  · linarith

private lemma rf6_mono {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    rW (Muon.emaW β) a ≤ rW (Muon.emaW β) b := by
  have hmono := ((lem_app_iso_weights_i hβ0.le hβ1).2.2.1 hβ0).1
  exact hmono.monotoneOn (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (ha.trans hab)) hab

private lemma rf6_ridge {β γ ϱ y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 < ϱ)
    (hy : 0 < y) (hyQ : y < isoQpsi β γ ϱ) :
    1 ≤ isoUlev β γ ϱ y ∧
      isoUlev β γ ϱ y ≤ 1 + rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log y) := by
  have hQ : isoQpsi β γ ϱ = qIso β γ γ ϱ := by unfold isoQpsi; rw [if_pos hϱ]
  obtain ⟨hQ0, hψ, hspec⟩ := rf6_root hβ0 hβ1 hγ hϱ
  rw [hQ] at hyQ ⊢
  set Q := qIso β γ γ ϱ with hQdef
  set ψ := rW (Muon.emaW β) Q with hψdef
  have hry : rW (Muon.emaW β) y ≤ ψ := rf6_mono hβ0 hβ1 hy.le hyQ.le
  have hA : γ - ψ ≤ isoResid β γ y := by unfold isoResid; linarith
  have hgp : 0 < γ - ψ := by linarith
  have hApos : 0 < isoResid β γ y := lt_of_lt_of_le hgp hA
  have hA2 : (γ - ψ) ^ 2 ≤ isoResid β γ y ^ 2 := by nlinarith
  have hx0 : 0 ≤ ϱ * y / isoResid β γ y ^ 2 := by positivity
  have hxle : ϱ * y / isoResid β γ y ^ 2 ≤ y / Q := by
    calc ϱ * y / isoResid β γ y ^ 2 ≤ ϱ * y / (γ - ψ) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hA2
      _ = y / Q := by rw [← hspec]; field_simp
  have hyQ1 : y / Q < 1 := (div_lt_one hQ0).mpr hyQ
  have hyQ0 : 0 < y / Q := div_pos hy hQ0
  constructor
  · unfold isoUlev
    refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) (by norm_num)
  · unfold isoUlev rrVarpi
    have hexp : Real.exp (-(Real.log Q - Real.log y)) = y / Q := by
      rw [neg_sub, Real.exp_sub, Real.exp_log hy, Real.exp_log hQ0]
    rw [hexp]
    have := Real.rpow_le_rpow_of_nonpos (x := 1 - y / Q) (y := 1 - ϱ * y / isoResid β γ y ^ 2)
      (z := -(1 / 2 : ℝ)) (by linarith) (by linarith) (by norm_num)
    linarith

private lemma rf6_resid_pos {β γ ϱ y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϱ : 0 < ϱ)
    (hy : 0 < y) (h : y < isoQpsi β γ ϱ) : 0 < isoResid β γ y := by
  unfold isoResid
  unfold isoQpsi at h
  rw [if_pos hϱ] at h
  have := rf6_isoRoot_resid (γ := γ) (s := ϱ) hβ0 hβ1 hy (by unfold qIso at h; exact h)
  linarith

private lemma rf6_gamma_pos {β γ : ℝ} (hβ1 : β < 1) (hβ0 : 0 < β) (hγ : isoGammaCirc β ≤ γ) :
    0 < γ := by
  unfold isoGammaCirc isoC' at hγ
  have : 0 < 1 - β ^ 2 := by nlinarith
  have : 0 < 1 / (1 - β ^ 2) := by positivity
  linarith

private lemma rf6_step {a m E K φ : ℝ} (hφ : 0 < φ) (ha : φ < a) (hma : a / 2 ≤ m)
    (hE : 0 ≤ E) (hK8 : 8 ≤ K) (hK : 32 * E ^ 2 ≤ K * φ ^ 2) :
    (a + 2 * E) ^ 2 ≤ K * (a * m) := by
  have ha0 : 0 < a := by linarith
  have hK0 : 0 ≤ K := by linarith
  have ham : a ^ 2 / 2 ≤ a * m := by nlinarith
  rcases le_or_gt (2 * E) a with hc | hc
  · have h1 : (a + 2 * E) ^ 2 ≤ 4 * a ^ 2 := by nlinarith
    have : 8 * (a * m) ≤ K * (a * m) := mul_le_mul_of_nonneg_right hK8 (mul_pos ha0 (by linarith : 0 < m)).le
    nlinarith
  · have h1 : (a + 2 * E) ^ 2 ≤ 16 * E ^ 2 := by nlinarith
    have h2 : φ ^ 2 / 2 ≤ a * m := by nlinarith
    have : K * (φ ^ 2 / 2) ≤ K * (a * m) := mul_le_mul_of_nonneg_left h2 hK0
    nlinarith

private lemma rf6_JJ {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hϱ : 0 < ϱ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {y z : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hyQ : y < isoQpsi β γ ϱ) (hzQ : z / β ^ (2 * ℓ) < isoQpsi β γ ϱ) :
    0 < isoDeltaHat β γ y z ∧ 0 ≤ isoWeightJ β γ y ∧ 0 ≤ isoWeightJ β γ (z / β ^ (2 * ℓ)) ∧
      isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * ℓ)) ≤
        isoK6 β * (γ ^ 2 * isoDeltaHat β γ y z) := by
  have hγ0 := rf6_gamma_pos hβ1 hβ0 hγ
  have hpow : 0 < β ^ (2 * ℓ) := pow_pos hβ0 _
  have hp1 : β ^ (2 * ℓ) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hzl0 : 0 < z / β ^ (2 * ℓ) := div_pos hz hpow
  have hzle : z ≤ z / β ^ (2 * ℓ) := (le_div_iff₀ hpow).mpr (mul_le_of_le_one_right hz.le hp1)
  have hzQ' : z < isoQpsi β γ ϱ := lt_of_le_of_lt hzle hzQ
  have hAy := rf6_resid_pos hβ0 hβ1 hϱ hy hyQ
  have hAz := rf6_resid_pos hβ0 hβ1 hϱ hz hzQ'
  have hAzl := rf6_resid_pos hβ0 hβ1 hϱ hzl0 hzQ
  -- shifts
  have hpow2 : β ^ (2 * ℓ) ≤ β ^ 2 := pow_le_pow_of_le_one hβ0.le hβ1.le (by omega)
  have hzb : z / β ^ 2 ≤ z / β ^ (2 * ℓ) :=
    div_le_div_of_nonneg_left hz.le hpow hpow2
  have hzb0 : 0 < z / β ^ 2 := div_pos hz (pow_pos hβ0 2)
  have hAzb := rf6_resid_pos hβ0 hβ1 hϱ hzb0 (lt_of_le_of_lt hzb hzQ)
  have hrzb : rW (Muon.emaW β) (z / β ^ 2) < γ := by unfold isoResid at hAzb; linarith
  have hshift := lem_app_iso_shifts_v hβ0 hβ1 γ z hz hγ hrzb
  have hphi : 0 < isoPhi 1 := ((lem_app_iso_gaussian_ii).2.2 1 one_pos).1
  obtain ⟨-, -, h3, h4, h5⟩ := lem_app_iso_kernel_bounds_v hβ0 hβ1 hγ0 hy hz hAy hAz
  have hAv : isoPhi 1 < isoAvee β γ y z := by
    refine lt_of_lt_of_le ?_ (le_max_right _ _)
    unfold isoResid at hshift ⊢; exact hshift
  have hprod : 0 < isoAvee β γ y z * max (isoAvee β γ y z - isoEbar β) (isoAvee β γ y z / 2) :=
    mul_pos (by linarith) h3
  have hg : 0 < γ ^ 2 * isoDeltaHat β γ y z := lt_of_lt_of_le hprod h4
  have hD : 0 < isoDeltaHat β γ y z := pos_of_mul_pos_right hg (by positivity)
  -- slopes
  have hslope : ∀ x : ℝ, 0 < x → 0 < isoEslope β x ∧ isoEslope β x ≤ isoEbar β := by
    intro x hx
    exact ⟨((lem_app_iso_count_ii hβ0 hβ1).1 x hx).1,
      (lem_app_iso_slope hβ0 hβ1 x hx).1.trans (lem_app_iso_slope hβ0 hβ1 x hx).2⟩
  have hE1 : 1 ≤ isoEbar β := le_max_left _ _
  have hJy0 : 0 ≤ isoWeightJ β γ y := by
    unfold isoWeightJ; linarith [(hslope y hy).1]
  have hJz0 : 0 ≤ isoWeightJ β γ (z / β ^ (2 * ℓ)) := by
    unfold isoWeightJ; linarith [(hslope _ hzl0).1]
  set a := isoAvee β γ y z with ha
  have hAy_le : isoResid β γ y ≤ a := le_max_left _ _
  have hAz_le : isoResid β γ z ≤ a := le_max_right _ _
  have hAzl_le : isoResid β γ (z / β ^ (2 * ℓ)) ≤ isoResid β γ z := by
    unfold isoResid
    have := rf6_mono hβ0 hβ1 hz.le hzle
    linarith
  have hJy : isoWeightJ β γ y ≤ a + 2 * isoEbar β := by
    unfold isoWeightJ; linarith [(hslope y hy).2]
  have hJz : isoWeightJ β γ (z / β ^ (2 * ℓ)) ≤ a + 2 * isoEbar β := by
    unfold isoWeightJ; linarith [(hslope _ hzl0).2]
  have hJJ : isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * ℓ)) ≤ (a + 2 * isoEbar β) ^ 2 := by
    rw [sq]; exact mul_le_mul hJy hJz hJz0 (by linarith)
  refine ⟨hD, hJy0, hJz0, hJJ.trans ?_⟩
  set m := max (a - isoEbar β) (a / 2) with hm
  have hma : a / 2 ≤ m := le_max_right _ _
  have ha0 : 0 < a := by linarith
  have hK8 : 8 ≤ isoK6 β := le_max_left _ _
  have hK6' : 32 * isoEbar β ^ 2 / isoPhi 1 ^ 2 ≤ isoK6 β := le_max_right _ _
  have hKnn : 0 ≤ isoK6 β := by linarith
  have hp2 : 0 < isoPhi 1 ^ 2 := by positivity
  have h3 : 32 * isoEbar β ^ 2 ≤ isoK6 β * isoPhi 1 ^ 2 := by
    rw [div_le_iff₀ hp2] at hK6'; exact hK6'
  have hstep : (a + 2 * isoEbar β) ^ 2 ≤ isoK6 β * (a * m) :=
    rf6_step hphi hAv hma (by linarith) hK8 h3
  calc (a + 2 * isoEbar β) ^ 2 ≤ isoK6 β * (a * m) := hstep
    _ ≤ isoK6 β * (γ ^ 2 * isoDeltaHat β γ y z) := mul_le_mul_of_nonneg_left h4 hKnn

private lemma rrPointwise {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hϱ : 0 < ϱ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {y z : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hyQ : y < isoQpsi β γ ϱ) (hzQ : z / β ^ (2 * ℓ) < isoQpsi β γ ϱ) :
    isoDivDiff β y z * isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * ℓ)) / isoDeltaHat β γ y z *
        (isoUlev β γ ϱ y * isoUlev β γ ϱ (z / β ^ (2 * ℓ)) - 1) ≤
      isoK6 β * γ ^ 2 * (isoEbar β * isoSinhRatio |Real.log y - Real.log z| / (y * z)) *
        (rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log y) +
          (1 + rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log y)) *
            rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log (z / β ^ (2 * ℓ)))) := by
  have hγ0 := rf6_gamma_pos hβ1 hβ0 hγ
  have hpow : 0 < β ^ (2 * ℓ) := pow_pos hβ0 _
  have hzl0 : 0 < z / β ^ (2 * ℓ) := div_pos hz hpow
  obtain ⟨hD, hJy0, hJz0, hJJ⟩ := rf6_JJ hβ0 hβ1 hγ hϱ hℓ hy hz hyQ hzQ
  obtain ⟨hu1, hu1'⟩ := rf6_ridge hβ0 hβ1 hγ0 hϱ hy hyQ
  obtain ⟨hu2, hu2'⟩ := rf6_ridge hβ0 hβ1 hγ0 hϱ hzl0 hzQ
  have hZ := lem_app_iso_kernel_bounds_ii hβ0 hβ1 hy hz
  have hlog : Real.log (y / z) = Real.log y - Real.log z := Real.log_div hy.ne' hz.ne'
  rw [hlog] at hZ
  obtain ⟨hZ0, hZ1, -⟩ := hZ
  have hZ1' := hZ1.trans (min_le_left _ _)
  have hyz : 0 < y * z := mul_pos hy hz
  rw [rrDivDiff_eq hy hz]
  set u1 := isoUlev β γ ϱ y
  set u2 := isoUlev β γ ϱ (z / β ^ (2 * ℓ))
  set v1 := rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log y)
  set v2 := rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log (z / β ^ (2 * ℓ)))
  set J1 := isoWeightJ β γ y
  set J2 := isoWeightJ β γ (z / β ^ (2 * ℓ))
  have hP : J1 * J2 / isoDeltaHat β γ y z ≤ isoK6 β * γ ^ 2 := by
    rw [div_le_iff₀ hD]; nlinarith
  have hP0 : 0 ≤ J1 * J2 / isoDeltaHat β γ y z := div_nonneg (mul_nonneg hJy0 hJz0) hD.le
  have hu12 : u1 * u2 - 1 ≤ v1 + (1 + v1) * v2 := by
    have : u1 * u2 ≤ (1 + v1) * (1 + v2) :=
      mul_le_mul hu1' hu2' (by linarith) (by linarith)
    nlinarith
  have hu0 : 0 ≤ u1 * u2 - 1 := by nlinarith
  have hDd0 : 0 ≤ isoZkern β y z / (y * z) := div_nonneg hZ0 hyz.le
  have hDd : isoZkern β y z / (y * z) ≤ isoEbar β * isoSinhRatio |Real.log y - Real.log z| / (y * z) :=
    div_le_div_of_nonneg_right hZ1' hyz.le
  have e1 : isoZkern β y z / (y * z) * J1 * J2 / isoDeltaHat β γ y z =
      isoZkern β y z / (y * z) * (J1 * J2 / isoDeltaHat β γ y z) := by ring
  rw [e1]
  have h2 : isoZkern β y z / (y * z) * (J1 * J2 / isoDeltaHat β γ y z) ≤
      isoEbar β * isoSinhRatio |Real.log y - Real.log z| / (y * z) * (isoK6 β * γ ^ 2) :=
    mul_le_mul hDd hP hP0 (hDd0.trans hDd)
  have h3 := mul_le_mul h2 hu12 hu0 ((mul_nonneg hDd0 hP0).trans h2)
  calc _ ≤ _ := h3
    _ = _ := by ring

private lemma rrPointwiseZ {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hϱ : 0 < ϱ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {y z : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hyQ : y < isoQpsi β γ ϱ) (hzQ : z / β ^ (2 * ℓ) < isoQpsi β γ ϱ) :
    isoDivDiff β y z * isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * ℓ)) / isoDeltaHat β γ y z *
        (isoUlev β γ ϱ y * isoUlev β γ ϱ (z / β ^ (2 * ℓ)) - 1) ≤
      isoK6 β * γ ^ 2 * (isoZkern β y z / (y * z)) *
        (rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log y) +
          (1 + rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log y)) *
            rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log (z / β ^ (2 * ℓ)))) := by
  have hγ0 := rf6_gamma_pos hβ1 hβ0 hγ
  have hpow : 0 < β ^ (2 * ℓ) := pow_pos hβ0 _
  have hzl0 : 0 < z / β ^ (2 * ℓ) := div_pos hz hpow
  obtain ⟨hD, hJy0, hJz0, hJJ⟩ := rf6_JJ hβ0 hβ1 hγ hϱ hℓ hy hz hyQ hzQ
  obtain ⟨hu1, hu1'⟩ := rf6_ridge hβ0 hβ1 hγ0 hϱ hy hyQ
  obtain ⟨hu2, hu2'⟩ := rf6_ridge hβ0 hβ1 hγ0 hϱ hzl0 hzQ
  have hZ := lem_app_iso_kernel_bounds_ii hβ0 hβ1 hy hz
  have hlog : Real.log (y / z) = Real.log y - Real.log z := Real.log_div hy.ne' hz.ne'
  rw [hlog] at hZ
  obtain ⟨hZ0, hZ1, -⟩ := hZ
  have hZ1' := hZ1.trans (min_le_left _ _)
  have hyz : 0 < y * z := mul_pos hy hz
  rw [rrDivDiff_eq hy hz]
  set u1 := isoUlev β γ ϱ y
  set u2 := isoUlev β γ ϱ (z / β ^ (2 * ℓ))
  set v1 := rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log y)
  set v2 := rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log (z / β ^ (2 * ℓ)))
  set J1 := isoWeightJ β γ y
  set J2 := isoWeightJ β γ (z / β ^ (2 * ℓ))
  have hP : J1 * J2 / isoDeltaHat β γ y z ≤ isoK6 β * γ ^ 2 := by
    rw [div_le_iff₀ hD]; nlinarith
  have hP0 : 0 ≤ J1 * J2 / isoDeltaHat β γ y z := div_nonneg (mul_nonneg hJy0 hJz0) hD.le
  have hu12 : u1 * u2 - 1 ≤ v1 + (1 + v1) * v2 := by
    have : u1 * u2 ≤ (1 + v1) * (1 + v2) :=
      mul_le_mul hu1' hu2' (by linarith) (by linarith)
    nlinarith
  have hu0 : 0 ≤ u1 * u2 - 1 := by nlinarith
  have hDd0 : 0 ≤ isoZkern β y z / (y * z) := div_nonneg hZ0 hyz.le
  have hDd : isoZkern β y z / (y * z) ≤ isoZkern β y z / (y * z) :=
    le_refl _
  have e1 : isoZkern β y z / (y * z) * J1 * J2 / isoDeltaHat β γ y z =
      isoZkern β y z / (y * z) * (J1 * J2 / isoDeltaHat β γ y z) := by ring
  rw [e1]
  have h2 : isoZkern β y z / (y * z) * (J1 * J2 / isoDeltaHat β γ y z) ≤
      isoZkern β y z / (y * z) * (isoK6 β * γ ^ 2) :=
    mul_le_mul hDd hP hP0 (hDd0.trans hDd)
  have h3 := mul_le_mul h2 hu12 hu0 ((mul_nonneg hDd0 hP0).trans h2)
  calc _ ≤ _ := h3
    _ = _ := by ring

end rf6




private lemma rrCoV_1d (G : ℝ → ENNReal) :
    ∫⁻ y in Ioi (0:ℝ), ENNReal.ofReal (1 / y) * G (Real.log y) = ∫⁻ w, G w := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := (univ : Set ℝ)) (f := Real.exp)
    (f' := Real.exp) MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun y => ENNReal.ofReal (1 / y) * G (Real.log y))
  rw [Set.image_univ, Real.range_exp] at h
  rw [h, Measure.restrict_univ]
  congr 1; funext x
  rw [abs_of_pos (Real.exp_pos x), Real.log_exp, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos x).le]
  rw [mul_one_div_cancel (Real.exp_pos x).ne', ENNReal.ofReal_one, one_mul]

private lemma rrCoV (H : ℝ × ℝ → ℝ) (hH : Measurable H) (hH0 : ∀ q, 0 ≤ H q) :
    ∫⁻ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), ENNReal.ofReal (H (Real.log p.1, Real.log p.2) / (p.1 * p.2))
      = ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (H q) := by
  have hm : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (H q)) := hH.ennreal_ofReal
  have hv : (volume : Measure (ℝ × ℝ)).restrict (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) =
      (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [hv, lintegral_prod]
  swap
  · refine Measurable.aemeasurable ?_
    have h1 : Measurable (fun p : ℝ × ℝ => H (Real.log p.1, Real.log p.2) / (p.1 * p.2)) :=
      (hH.comp ((Real.measurable_log.comp measurable_fst).prodMk
        (Real.measurable_log.comp measurable_snd))).div (measurable_fst.mul measurable_snd)
    exact h1.ennreal_ofReal
  have step : ∀ y ∈ Ioi (0:ℝ), ∫⁻ z in Ioi (0:ℝ),
      ENNReal.ofReal (H (Real.log y, Real.log z) / (y * z)) =
      ENNReal.ofReal (1 / y) * ∫⁻ w, ENNReal.ofReal (H (Real.log y, w)) := by
    intro y hy
    have hy' : (0:ℝ) < y := hy
    have : ∀ z ∈ Ioi (0:ℝ), ENNReal.ofReal (H (Real.log y, Real.log z) / (y * z)) =
        ENNReal.ofReal (1 / y) * (ENNReal.ofReal (1 / z) * ENNReal.ofReal (H (Real.log y, Real.log z))) := by
      intro z hz
      have hz' : (0:ℝ) < z := hz
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1; field_simp
    rw [setLIntegral_congr_fun measurableSet_Ioi this, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    exact rrCoV_1d (fun w => ENNReal.ofReal (H (Real.log y, w)))
  rw [setLIntegral_congr_fun measurableSet_Ioi step]
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  have hG : Measurable (fun a : ℝ => ∫⁻ w, ENNReal.ofReal (H (a, w))) := hm.lintegral_prod_right'
  have := rrCoV_1d (fun a => ∫⁻ w, ENNReal.ofReal (H (a, w)))
  simpa using this


private lemma rrSinh_le (δ : ℝ) : isoSinhRatio |δ| ≤ min 1 (rrF |δ|) := by
  have h := (lem_app_iso_kernel_bounds_ii (β := 1 / 2) (by norm_num) (by norm_num)
    (y := Real.exp |δ|) (z := 1) (Real.exp_pos _) one_pos).2.2
  have hl : Real.log (Real.exp |δ| / 1) = |δ| := by rw [div_one, Real.log_exp]
  rw [hl, abs_abs] at h
  simpa [rrF] using h


private lemma rr2_count (x : ℝ) :
    ∑' ℓ : ℕ, (if ((ℓ : ℝ) + 1) < x then (1 : ENNReal) else 0) ≤ ENNReal.ofReal (max x 0) := by
  have h1 : ∑' ℓ : ℕ, (if ((ℓ : ℝ) + 1) < x then (1 : ENNReal) else 0) =
      ∑ ℓ ∈ Finset.range ⌈x - 1⌉₊, (if ((ℓ : ℝ) + 1) < x then (1 : ENNReal) else 0) := by
    apply tsum_eq_sum
    intro ℓ hℓ
    simp only [Finset.mem_range, not_lt] at hℓ
    have : x - 1 ≤ (ℓ : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hℓ)
    rw [if_neg (by linarith)]
  rw [h1]
  calc ∑ ℓ ∈ Finset.range ⌈x - 1⌉₊, (if ((ℓ : ℝ) + 1) < x then (1 : ENNReal) else 0)
      ≤ ∑ ℓ ∈ Finset.range ⌈x - 1⌉₊, (1 : ENNReal) :=
        Finset.sum_le_sum (fun ℓ _ => by split_ifs <;> simp)
    _ = ENNReal.ofReal (⌈x - 1⌉₊ : ℝ) := by simp
    _ ≤ ENNReal.ofReal (max x 0) := by
        apply ENNReal.ofReal_le_ofReal
        rcases le_or_gt (x - 1) 0 with h | h
        · rw [Nat.ceil_eq_zero.mpr h]; simp
        · have := Nat.ceil_lt_add_one h.le
          have := le_max_left x 0
          linarith


private lemma rr2_lint_sub (U : ℝ) (φ : ℝ → ENNReal) :
    ∫⁻ u in Iio U, φ (U - u) = ∫⁻ ζ in Ioi (0:ℝ), φ ζ := by
  have hmp := (volume : Measure ℝ).measurePreserving_sub_left U
  have hme := (Homeomorph.subLeft U).measurableEmbedding
  have := hmp.setLIntegral_comp_preimage_emb hme φ (Ioi 0)
  have hpre : (fun h : ℝ => U - h) ⁻¹' Ioi 0 = Iio U := by
    ext x; simp [sub_pos]
  rw [hpre] at this
  exact this

private lemma rr2_zeta3_pos : 0 < (riemannZeta 3).re := by
  have h : (riemannZeta ((3:ℕ) : ℂ)).re = ∑' n : ℕ, 1 / (n : ℝ) ^ 3 := by
    rw [zeta_nat_eq_tsum_of_gt_one (by omega)]
    have : (∑' n : ℕ, 1 / (n : ℂ) ^ 3) = ((∑' n : ℕ, 1 / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      refine tsum_congr fun n => ?_
      push_cast; rfl
    rw [this, Complex.ofReal_re]
  have h3 : (riemannZeta 3) = riemannZeta ((3:ℕ) : ℂ) := by norm_num
  rw [h3, h]
  refine (Real.summable_one_div_nat_pow.2 (by norm_num)).tsum_pos (fun n => by positivity) 1 ?_
  norm_num

/-- pointwise bound after summing over `ℓ`. -/
private lemma rr2_point {U b E : ℝ} (hb : 0 < b) (hE : 0 < E) (u v : ℝ) :
    ∑' ℓ : ℕ, ENNReal.ofReal (E * isoSinhRatio |u - v| *
        ((if u < U ∧ v + 2 * b * ((ℓ : ℝ) + 1) < U then 1 else 0) * rrVarpi (U - u)))
      ≤ ENNReal.ofReal (if u < U then E / (2 * b) * isoSinhRatio |u - v| * rrVarpi (U - u) *
          ((U - u) + |u - v|) else 0) := by
  by_cases hu : u < U
  · rw [if_pos hu]
    have hS := rrSinh_nonneg |u - v|
    have hV := rrVarpi_nonneg (sub_pos.mpr hu)
    set Dc := E * isoSinhRatio |u - v| * rrVarpi (U - u) with hDc
    have hDc0 : 0 ≤ Dc := by positivity
    have hterm : ∀ ℓ : ℕ, ENNReal.ofReal (E * isoSinhRatio |u - v| *
        ((if u < U ∧ v + 2 * b * ((ℓ : ℝ) + 1) < U then 1 else 0) * rrVarpi (U - u))) =
        ENNReal.ofReal Dc * (if ((ℓ : ℝ) + 1) < (U - v) / (2 * b) then (1 : ENNReal) else 0) := by
      intro ℓ
      have hc : (v + 2 * b * ((ℓ : ℝ) + 1) < U) ↔ ((ℓ : ℝ) + 1) < (U - v) / (2 * b) := by
        rw [lt_div_iff₀ (by positivity)]; constructor <;> intro h <;> nlinarith
      by_cases h2 : v + 2 * b * ((ℓ : ℝ) + 1) < U
      · rw [if_pos ⟨hu, h2⟩, if_pos (hc.mp h2)]; simp [hDc]
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 (hc.mpr h))]; simp
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_left]
    calc ENNReal.ofReal Dc * ∑' ℓ : ℕ, (if ((ℓ : ℝ) + 1) < (U - v) / (2 * b) then (1 : ENNReal) else 0)
        ≤ ENNReal.ofReal Dc * ENNReal.ofReal (max ((U - v) / (2 * b)) 0) :=
          by gcongr; exact rr2_count _
      _ = ENNReal.ofReal (Dc * max ((U - v) / (2 * b)) 0) := (ENNReal.ofReal_mul hDc0).symm
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hm : max ((U - v) / (2 * b)) 0 ≤ ((U - u) + |u - v|) / (2 * b) := by
            apply max_le
            · apply div_le_div_of_nonneg_right _ (by positivity)
              have := le_abs_self (u - v); linarith
            · apply div_nonneg _ (by positivity); have := abs_nonneg (u - v); linarith
          calc Dc * max ((U - v) / (2 * b)) 0 ≤ Dc * (((U - u) + |u - v|) / (2 * b)) :=
                mul_le_mul_of_nonneg_left hm hDc0
            _ = _ := by rw [hDc]; field_simp
  · rw [if_neg hu]
    simp [hu]

private lemma rr2_inner {U c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    ∫⁻ v : ℝ, ENNReal.ofReal (if u < U then c * isoSinhRatio |u - v| * rrVarpi (U - u) *
          ((U - u) + |u - v|) else 0) =
      if u < U then ENNReal.ofReal (c * rrVarpi (U - u) * (U - u)) * ENNReal.ofReal (Real.pi ^ 2) +
        ENNReal.ofReal (c * rrVarpi (U - u)) * ENNReal.ofReal (28 * (riemannZeta 3).re) else 0 := by
  by_cases hu : u < U
  · simp only [if_pos hu]
    have hV := rrVarpi_nonneg (sub_pos.mpr hu)
    have hA : 0 ≤ U - u := (sub_pos.mpr hu).le
    have hpt : ∀ v : ℝ, ENNReal.ofReal (c * isoSinhRatio |u - v| * rrVarpi (U - u) *
          ((U - u) + |u - v|)) =
        ENNReal.ofReal (c * rrVarpi (U - u) * (U - u)) * ENNReal.ofReal (isoSinhRatio |u - v|) +
        ENNReal.ofReal (c * rrVarpi (U - u)) * ENNReal.ofReal (|u - v| * isoSinhRatio |u - v|) := by
      intro v
      have hS := rrSinh_nonneg |u - v|
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring
    simp_rw [hpt]
    have m1 : Measurable fun v : ℝ => ENNReal.ofReal (isoSinhRatio |u - v|) :=
      ENNReal.measurable_ofReal.comp (rrSinh_measurable.comp (by fun_prop))
    have m2 : Measurable fun v : ℝ => ENNReal.ofReal (|u - v| * isoSinhRatio |u - v|) :=
      ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun v : ℝ => |u - v|).mul
        (rrSinh_measurable.comp (by fun_prop)))
    rw [lintegral_add_left (m1.const_mul _), lintegral_const_mul _ m1, lintegral_const_mul _ m2]
    have e1 := lintegral_sub_left_eq_self (μ := (volume : Measure ℝ))
      (fun w : ℝ => ENNReal.ofReal (isoSinhRatio |w|)) u
    have e2 := lintegral_sub_left_eq_self (μ := (volume : Measure ℝ))
      (fun w : ℝ => ENNReal.ofReal (|w| * isoSinhRatio |w|)) u
    rw [e1, e2, rrSinh_lintegral, rrSinh_abs_lintegral]
  · simp [hu]

private lemma rrNpart {U b E : ℝ} (hb : 0 < b) (hE : 0 < E) :
    ∑' ℓ : ℕ, ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (E * isoSinhRatio |q.1 - q.2| *
        ((if q.1 < U ∧ q.2 + 2 * b * ((ℓ : ℝ) + 1) < U then 1 else 0) * rrVarpi (U - q.1)))
      ≤ ENNReal.ofReal (E / (2 * b) * (Real.pi ^ 4 / 6 + 56 * (riemannZeta 3).re * Real.log 2)) := by
  have hc : 0 ≤ E / (2 * b) := by positivity
  have hs := rrSinh_measurable
  have hv := rrVarpi_measurable
  have hmeas : ∀ ℓ : ℕ, Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (E * isoSinhRatio |q.1 - q.2| *
        ((if q.1 < U ∧ q.2 + 2 * b * ((ℓ : ℝ) + 1) < U then 1 else 0) * rrVarpi (U - q.1)))) := by
    intro ℓ
    have hset : MeasurableSet {q : ℝ × ℝ | q.1 < U ∧ q.2 + 2 * b * ((ℓ : ℝ) + 1) < U} :=
      (measurableSet_lt measurable_fst measurable_const).inter
        (measurableSet_lt (by fun_prop : Measurable fun q : ℝ × ℝ => q.2 + 2 * b * ((ℓ : ℝ) + 1)) measurable_const)
    refine ENNReal.measurable_ofReal.comp ?_
    exact (measurable_const.mul (hs.comp (by fun_prop))).mul
      ((Measurable.ite hset measurable_const measurable_const).mul (hv.comp (by fun_prop)))
  have hD : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (if q.1 < U then
      E / (2 * b) * isoSinhRatio |q.1 - q.2| * rrVarpi (U - q.1) * ((U - q.1) + |q.1 - q.2|)
      else 0)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_const)
      (((measurable_const.mul (hs.comp (by fun_prop))).mul (hv.comp (by fun_prop))).mul
        (by fun_prop : Measurable fun q : ℝ × ℝ => (U - q.1) + |q.1 - q.2|)) measurable_const
  have hφ : Measurable fun ζ : ℝ => ENNReal.ofReal (ζ * rrVarpi ζ) :=
    ENNReal.measurable_ofReal.comp (measurable_id.mul hv)
  calc ∑' ℓ : ℕ, ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (E * isoSinhRatio |q.1 - q.2| *
        ((if q.1 < U ∧ q.2 + 2 * b * ((ℓ : ℝ) + 1) < U then 1 else 0) * rrVarpi (U - q.1)))
      = ∫⁻ q : ℝ × ℝ, ∑' ℓ : ℕ, ENNReal.ofReal (E * isoSinhRatio |q.1 - q.2| *
        ((if q.1 < U ∧ q.2 + 2 * b * ((ℓ : ℝ) + 1) < U then 1 else 0) * rrVarpi (U - q.1))) :=
        (lintegral_tsum fun ℓ => (hmeas ℓ).aemeasurable).symm
    _ ≤ ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (if q.1 < U then
      E / (2 * b) * isoSinhRatio |q.1 - q.2| * rrVarpi (U - q.1) * ((U - q.1) + |q.1 - q.2|)
      else 0) := lintegral_mono fun q => rr2_point hb hE q.1 q.2
    _ = ∫⁻ u : ℝ, ∫⁻ v : ℝ, ENNReal.ofReal (if u < U then
      E / (2 * b) * isoSinhRatio |u - v| * rrVarpi (U - u) * ((U - u) + |u - v|)
      else 0) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hD.aemeasurable]
    _ = ∫⁻ u : ℝ, (Iio U).indicator (fun u => ENNReal.ofReal (E / (2 * b) * rrVarpi (U - u) * (U - u)) *
          ENNReal.ofReal (Real.pi ^ 2) + ENNReal.ofReal (E / (2 * b) * rrVarpi (U - u)) *
          ENNReal.ofReal (28 * (riemannZeta 3).re)) u := by
        refine lintegral_congr fun u => ?_
        rw [rr2_inner hc u]
        by_cases hu : u < U <;> simp [hu, Set.indicator]
    _ = ∫⁻ u in Iio U, (ENNReal.ofReal (E / (2 * b)) * (ENNReal.ofReal (Real.pi ^ 2) *
          ENNReal.ofReal ((U - u) * rrVarpi (U - u)) +
          ENNReal.ofReal (28 * (riemannZeta 3).re) * ENNReal.ofReal (rrVarpi (U - u)))) := by
        rw [lintegral_indicator measurableSet_Iio]
        refine setLIntegral_congr_fun measurableSet_Iio (fun u hu => ?_)
        have hu' : u < U := hu
        have hV := rrVarpi_nonneg (sub_pos.mpr hu')
        have hA : 0 ≤ U - u := (sub_pos.mpr hu').le
        rw [ENNReal.ofReal_mul (mul_nonneg hc hV), ENNReal.ofReal_mul hc, ENNReal.ofReal_mul hA]
        ring
    _ = ∫⁻ ζ in Ioi (0:ℝ), (ENNReal.ofReal (E / (2 * b)) * (ENNReal.ofReal (Real.pi ^ 2) *
          ENNReal.ofReal (ζ * rrVarpi ζ) +
          ENNReal.ofReal (28 * (riemannZeta 3).re) * ENNReal.ofReal (rrVarpi ζ))) :=
        rr2_lint_sub U (fun ζ => ENNReal.ofReal (E / (2 * b)) * (ENNReal.ofReal (Real.pi ^ 2) *
          ENNReal.ofReal (ζ * rrVarpi ζ) +
          ENNReal.ofReal (28 * (riemannZeta 3).re) * ENNReal.ofReal (rrVarpi ζ)))
    _ = ENNReal.ofReal (E / (2 * b)) * (ENNReal.ofReal (Real.pi ^ 2) *
          (∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (ζ * rrVarpi ζ)) +
          ENNReal.ofReal (28 * (riemannZeta 3).re) *
          (∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (rrVarpi ζ))) := by
        have m1 : Measurable fun ζ : ℝ => ENNReal.ofReal (Real.pi ^ 2) *
            ENNReal.ofReal (ζ * rrVarpi ζ) := hφ.const_mul _
        have m2 : Measurable fun ζ : ℝ => ENNReal.ofReal (28 * (riemannZeta 3).re) *
            ENNReal.ofReal (rrVarpi ζ) := (ENNReal.measurable_ofReal.comp hv).const_mul _
        have mv : Measurable fun ζ : ℝ => ENNReal.ofReal (rrVarpi ζ) :=
          ENNReal.measurable_ofReal.comp hv
        have m12 : Measurable fun ζ : ℝ => ENNReal.ofReal (Real.pi ^ 2) *
            ENNReal.ofReal (ζ * rrVarpi ζ) + ENNReal.ofReal (28 * (riemannZeta 3).re) *
            ENNReal.ofReal (rrVarpi ζ) := m1.add m2
        rw [lintegral_const_mul _ m12, lintegral_add_left m1, lintegral_const_mul _ hφ,
          lintegral_const_mul _ mv]
    _ ≤ ENNReal.ofReal (E / (2 * b)) * (ENNReal.ofReal (Real.pi ^ 2) *
          ENNReal.ofReal (Real.pi ^ 2 / 6) +
          ENNReal.ofReal (28 * (riemannZeta 3).re) * ENNReal.ofReal (2 * Real.log 2)) := by
        rw [rrVarpi_lintegral]
        exact mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl rrVarpi_zeta_lintegral) le_rfl)
    _ = _ := by
        have hz := rr2_zeta3_pos
        have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hc]
        congr 1; ring



private lemma rw3_lint_sub (U : ℝ) (φ : ℝ → ENNReal) :
    ∫⁻ u in Iio U, φ (U - u) = ∫⁻ ζ in Ioi (0:ℝ), φ ζ := by
  have hmp := (volume : Measure ℝ).measurePreserving_sub_left U
  have hme := (Homeomorph.subLeft U).measurableEmbedding
  have := hmp.setLIntegral_comp_preimage_emb hme φ (Ioi 0)
  have hpre : (fun h : ℝ => U - h) ⁻¹' Ioi 0 = Iio U := by
    ext x; simp [sub_pos]
  rw [hpre] at this
  exact this

private lemma rw3_count {x n0 : ℝ} (hx : x ≤ n0) (h0 : 0 ≤ n0) :
    ∑' ℓ : ℕ, (if (ℓ : ℝ) + 1 < x then (1 : ENNReal) else 0) ≤ ENNReal.ofReal n0 := by
  rw [tsum_eq_sum (s := Finset.range ⌈x - 1⌉₊)]
  · calc ∑ ℓ ∈ Finset.range ⌈x - 1⌉₊, (if (ℓ : ℝ) + 1 < x then (1 : ENNReal) else 0)
        ≤ ∑ ℓ ∈ Finset.range ⌈x - 1⌉₊, (1 : ENNReal) := by
          apply Finset.sum_le_sum; intro i _; split_ifs <;> simp
      _ = (⌈x - 1⌉₊ : ENNReal) := by simp
      _ ≤ ENNReal.ofReal n0 := by
          rw [← ENNReal.ofReal_natCast]
          apply ENNReal.ofReal_le_ofReal
          by_cases h1 : x - 1 ≤ 0
          · rw [Nat.ceil_eq_zero.mpr h1]; simpa using h0
          · have := Nat.ceil_lt_add_one (le_of_lt (not_le.mp h1))
            linarith
  · intro ℓ hℓ
    have : ¬ (ℓ : ℝ) + 1 < x := by
      intro h
      have : (ℓ : ℝ) < x - 1 := by linarith
      exact hℓ (Finset.mem_range.mpr (Nat.lt_ceil.mpr this))
    simp [this]

private lemma rw3_sinh_meas : Measurable (fun w : ℝ => isoSinhRatio |w|) :=
  rrSinh_measurable.comp measurable_abs

private lemma rw3_Ia {U E S2 : ℝ} (hE : 0 < E) (hS : 0 ≤ S2) (v : ℝ) :
    ∫⁻ u in Iio U, ENNReal.ofReal (min (E * isoSinhRatio |u - v|) (S2 * Real.exp ((u + v) / 2)) *
        (1 + rrVarpi (U - u))) ≤ ENNReal.ofReal (E * (Real.pi ^ 2 + 2 * Real.log 2)) := by
  have hmeas1 : Measurable (fun u : ℝ => ENNReal.ofReal (E * isoSinhRatio |u - v|)) :=
    ENNReal.measurable_ofReal.comp
      ((rw3_sinh_meas.comp (measurable_id.sub measurable_const)).const_mul E)
  have h1 : ∫⁻ u in Iio U, ENNReal.ofReal (min (E * isoSinhRatio |u - v|)
      (S2 * Real.exp ((u + v) / 2)) * (1 + rrVarpi (U - u))) ≤
      ∫⁻ u in Iio U, (ENNReal.ofReal (E * isoSinhRatio |u - v|) +
        ENNReal.ofReal (E * rrVarpi (U - u))) := by
    apply setLIntegral_mono' measurableSet_Iio
    intro u hu
    have hu' : 0 < U - u := sub_pos.mpr hu
    have hϖ := rrVarpi_nonneg hu'
    have hs0 := rrSinh_nonneg |u - v|
    have hs1 : isoSinhRatio |u - v| ≤ 1 := by
      have := rrSinh_le (u - v)
      exact this.trans (min_le_left _ _)
    have hm0 : 0 ≤ min (E * isoSinhRatio |u - v|) (S2 * Real.exp ((u + v) / 2)) :=
      le_min (by positivity) (by positivity)
    have hm1 := min_le_left (E * isoSinhRatio |u - v|) (S2 * Real.exp ((u + v) / 2))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : min (E * isoSinhRatio |u - v|) (S2 * Real.exp ((u + v) / 2)) * (1 + rrVarpi (U - u))
        ≤ (E * isoSinhRatio |u - v|) * (1 + rrVarpi (U - u)) :=
      mul_le_mul_of_nonneg_right hm1 (by linarith)
    nlinarith [mul_nonneg hE.le hϖ, mul_nonneg hE.le (mul_nonneg hs0 hϖ),
      mul_le_mul_of_nonneg_left hs1 (mul_nonneg hE.le hϖ)]
  refine h1.trans ?_
  rw [lintegral_add_left' hmeas1.aemeasurable]
  have e1 : ∫⁻ u in Iio U, ENNReal.ofReal (E * isoSinhRatio |u - v|) ≤
      ENNReal.ofReal (E * Real.pi ^ 2) := by
    calc _ ≤ ∫⁻ u, ENNReal.ofReal (E * isoSinhRatio |u - v|) := setLIntegral_le_lintegral _ _
      _ = ∫⁻ u, ENNReal.ofReal E * ENNReal.ofReal (isoSinhRatio |u - v|) := by
          congr 1; funext u; rw [ENNReal.ofReal_mul hE.le]
      _ = ENNReal.ofReal E * ∫⁻ u, ENNReal.ofReal (isoSinhRatio |u - v|) := by
          rw [lintegral_const_mul]
          exact ENNReal.measurable_ofReal.comp (rw3_sinh_meas.comp (measurable_id.sub measurable_const))
      _ = ENNReal.ofReal E * ∫⁻ u, ENNReal.ofReal (isoSinhRatio |u|) := by
          rw [lintegral_sub_right_eq_self (fun u : ℝ => ENNReal.ofReal (isoSinhRatio |u|)) v]
      _ = ENNReal.ofReal (E * Real.pi ^ 2) := by
          rw [rrSinh_lintegral, ← ENNReal.ofReal_mul hE.le]
  have e2 : ∫⁻ u in Iio U, ENNReal.ofReal (E * rrVarpi (U - u)) =
      ENNReal.ofReal (E * (2 * Real.log 2)) := by
    rw [rw3_lint_sub U (fun ζ => ENNReal.ofReal (E * rrVarpi ζ))]
    simp_rw [ENNReal.ofReal_mul hE.le]
    rw [lintegral_const_mul _ rrVarpi_measurable.ennreal_ofReal, rrVarpi_lintegral,
      ← ENNReal.ofReal_mul hE.le]
  calc _ ≤ ENNReal.ofReal (E * Real.pi ^ 2) + ENNReal.ofReal (E * (2 * Real.log 2)) :=
        add_le_add e1 e2.le
    _ = ENNReal.ofReal (E * (Real.pi ^ 2 + 2 * Real.log 2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity)]
        ring_nf

private lemma rw3_Ib {U V0 E S2 C1 : ℝ} (hE : 0 < E) (hS : 0 ≤ S2)
    (hSC : S2 * Real.exp V0 = C1) {v : ℝ} (hv : v < V0) :
    ∫⁻ u in Iio U, ENNReal.ofReal (min (E * isoSinhRatio |u - v|) (S2 * Real.exp ((u + v) / 2)) *
        (1 + rrVarpi (U - u))) ≤
      ENNReal.ofReal (((32 / 10 + 2 * Real.log 2) * C1 +
        (96 / 10 + 4 * Real.exp (1 / 2) * Real.log 2) * E) * rrF (V0 - v)) := by
  refine rrIbound hv hE hS hSC (fun u => min (E * isoSinhRatio |u - v|) (S2 * Real.exp ((u + v) / 2)))
    (fun u => le_min (mul_nonneg hE.le (rrSinh_nonneg _)) (by positivity)) ?_ (fun u => min_le_right _ _)
  intro u
  refine (min_le_left _ _).trans ?_
  have := (rrSinh_le (u - v)).trans (min_le_right _ _)
  exact mul_le_mul_of_nonneg_left this hE.le

private def rw3Phi (U c v : ℝ) : ENNReal :=
  if v + c < U then ENNReal.ofReal (rrVarpi (U - (v + c))) else 0

private lemma rw3_slice {U V0 c E S2 C1 : ℝ} (hE : 0 < E) (hS : 0 ≤ S2)
    (hSC : S2 * Real.exp V0 = C1) :
    ∫⁻ q : ℝ × ℝ, ENNReal.ofReal
        (min (E * isoSinhRatio |q.1 - q.2|) (S2 * Real.exp ((q.1 + q.2) / 2)) *
          ((if q.1 < U ∧ q.2 + c < U then 1 else 0) *
            ((1 + rrVarpi (U - q.1)) * rrVarpi (U - (q.2 + c))))) ≤
      ∫⁻ v : ℝ, rw3Phi U c v *
        ((if V0 ≤ v then ENNReal.ofReal (E * (Real.pi ^ 2 + 2 * Real.log 2)) else 0) +
          (if v < V0 then ENNReal.ofReal (((32 / 10 + 2 * Real.log 2) * C1 +
            (96 / 10 + 4 * Real.exp (1 / 2) * Real.log 2) * E) * rrF (V0 - v)) else 0)) := by
  have hmeas : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal
        (min (E * isoSinhRatio |q.1 - q.2|) (S2 * Real.exp ((q.1 + q.2) / 2)) *
          ((if q.1 < U ∧ q.2 + c < U then 1 else 0) *
            ((1 + rrVarpi (U - q.1)) * rrVarpi (U - (q.2 + c)))))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    have h1 : Measurable (fun q : ℝ × ℝ => isoSinhRatio |q.1 - q.2|) :=
      rw3_sinh_meas.comp (measurable_fst.sub measurable_snd)
    have h2 : Measurable (fun q : ℝ × ℝ => Real.exp ((q.1 + q.2) / 2)) := by fun_prop
    have h3 : Measurable (fun q : ℝ × ℝ => (if q.1 < U ∧ q.2 + c < U then (1:ℝ) else 0)) := by
      refine Measurable.ite ?_ measurable_const measurable_const
      exact (measurableSet_lt measurable_fst measurable_const).inter
        (measurableSet_lt (measurable_snd.add_const c) measurable_const)
    have h4 : Measurable (fun q : ℝ × ℝ => rrVarpi (U - q.1)) :=
      rrVarpi_measurable.comp (measurable_const.sub measurable_fst)
    have h5 : Measurable (fun q : ℝ × ℝ => rrVarpi (U - (q.2 + c))) :=
      rrVarpi_measurable.comp (measurable_const.sub (measurable_snd.add_const c))
    exact ((h1.const_mul E).min (h2.const_mul S2)).mul (h3.mul ((h4.const_add 1).mul h5))
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ hmeas.aemeasurable]
  apply lintegral_mono
  intro v
  by_cases hvc : v + c < U
  · have hϖ' : 0 ≤ rrVarpi (U - (v + c)) := rrVarpi_nonneg (sub_pos.mpr hvc)
    have hpt : ∀ u : ℝ, ENNReal.ofReal
        (min (E * isoSinhRatio |u - v|) (S2 * Real.exp ((u + v) / 2)) *
          ((if u < U ∧ v + c < U then 1 else 0) *
            ((1 + rrVarpi (U - u)) * rrVarpi (U - (v + c))))) =
        (Iio U).indicator (fun u => ENNReal.ofReal
          (min (E * isoSinhRatio |u - v|) (S2 * Real.exp ((u + v) / 2)) *
            (1 + rrVarpi (U - u)))) u * ENNReal.ofReal (rrVarpi (U - (v + c))) := by
      intro u
      by_cases hu : u < U
      · have hu' : 0 ≤ rrVarpi (U - u) := rrVarpi_nonneg (sub_pos.mpr hu)
        have hm0 : 0 ≤ min (E * isoSinhRatio |u - v|) (S2 * Real.exp ((u + v) / 2)) :=
          le_min (mul_nonneg hE.le (rrSinh_nonneg _)) (by positivity)
        rw [Set.indicator_of_mem (show u ∈ Iio U from hu), if_pos ⟨hu, hvc⟩,
          ← ENNReal.ofReal_mul (mul_nonneg hm0 (by linarith))]
        congr 1; ring
      · rw [Set.indicator_of_notMem (show u ∉ Iio U from hu), if_neg (fun h => hu h.1)]
        simp
    simp_rw [hpt]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Iio]
    unfold rw3Phi
    rw [if_pos hvc, mul_comm]
    gcongr
    by_cases hv : v < V0
    · have := rw3_Ib (U := U) hE hS hSC hv
      calc _ ≤ _ := this
        _ ≤ _ := by rw [if_neg (not_le.mpr hv), if_pos hv, zero_add]
    · have := rw3_Ia (U := U) hE hS v
      calc _ ≤ _ := this
        _ ≤ _ := by rw [if_pos (not_lt.mp hv), if_neg hv, add_zero]
  · have : ∀ u : ℝ, ENNReal.ofReal
        (min (E * isoSinhRatio |u - v|) (S2 * Real.exp ((u + v) / 2)) *
          ((if u < U ∧ v + c < U then 1 else 0) *
            ((1 + rrVarpi (U - u)) * rrVarpi (U - (v + c))))) = 0 := by
      intro u; rw [if_neg (fun h => hvc h.2)]; simp
    simp_rw [this]
    simp

private lemma rw3_Phi_ind (U c : ℝ) (F : ℝ → ENNReal) (v : ℝ) :
    rw3Phi U c v * F v = (Iio (U - c)).indicator (fun v => ENNReal.ofReal (rrVarpi (U - c - v)) * F v) v := by
  unfold rw3Phi
  by_cases h : v + c < U
  · have h' : v ∈ Iio (U - c) := by simp only [mem_Iio]; linarith
    rw [if_pos h, Set.indicator_of_mem h']
    congr 3; ring
  · have h' : v ∉ Iio (U - c) := by simp only [mem_Iio, not_lt]; linarith
    rw [if_neg h, Set.indicator_of_notMem h']; simp

private lemma rw3_P1 {U V0 c c0 : ℝ} (hc0 : 0 ≤ c0) :
    ∫⁻ v : ℝ, rw3Phi U c v * (if V0 ≤ v then ENNReal.ofReal c0 else 0) ≤
      if V0 < U - c then ENNReal.ofReal (c0 * (2 * Real.log 2)) else 0 := by
  split_ifs with h
  · calc _ = ∫⁻ v in Iio (U - c), ENNReal.ofReal (rrVarpi (U - c - v)) *
            (if V0 ≤ v then ENNReal.ofReal c0 else 0) := by
          rw [← lintegral_indicator measurableSet_Iio]
          congr 1; funext v; exact rw3_Phi_ind U c (fun v => if V0 ≤ v then ENNReal.ofReal c0 else 0) v
      _ ≤ ∫⁻ v in Iio (U - c), ENNReal.ofReal (rrVarpi (U - c - v)) * ENNReal.ofReal c0 := by
          apply lintegral_mono; intro v
          dsimp only; gcongr; split_ifs <;> simp
      _ = ∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (rrVarpi ζ) * ENNReal.ofReal c0 :=
          rw3_lint_sub (U - c) (fun ζ => ENNReal.ofReal (rrVarpi ζ) * ENNReal.ofReal c0)
      _ = ENNReal.ofReal (c0 * (2 * Real.log 2)) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, rrVarpi_lintegral, mul_comm,
            ← ENNReal.ofReal_mul hc0]
  · have : ∀ v : ℝ, rw3Phi U c v * (if V0 ≤ v then ENNReal.ofReal c0 else 0) = 0 := by
      intro v
      unfold rw3Phi
      by_cases hv : V0 ≤ v
      · rw [if_neg (by linarith [not_lt.mp h]  : ¬ (v + c < U))]; simp
      · simp [hv]
    simp_rw [this]; simp

private lemma rw3_P2_eq {U V0 c K : ℝ} (hK : 0 ≤ K) :
    ∫⁻ v : ℝ, rw3Phi U c v * (if v < V0 then ENNReal.ofReal (K * rrF (V0 - v)) else 0) =
      ∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (rrVarpi ζ) * (ENNReal.ofReal K *
        ENNReal.ofReal (if 0 < (ζ - (U - V0)) + c then rrF ((ζ - (U - V0)) + c) else 0)) := by
  rw [← rw3_lint_sub (U - c)
    (fun ζ => ENNReal.ofReal (rrVarpi ζ) * (ENNReal.ofReal K *
        ENNReal.ofReal (if 0 < (ζ - (U - V0)) + c then rrF ((ζ - (U - V0)) + c) else 0))),
    ← lintegral_indicator measurableSet_Iio]
  congr 1; funext v
  refine (rw3_Phi_ind U c (fun v => if v < V0 then ENNReal.ofReal (K * rrF (V0 - v)) else 0) v).trans ?_
  by_cases hv : v ∈ Iio (U - c)
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
    congr 1
    have e1 : (U - c - v) - (U - V0) + c = V0 - v := by ring
    rw [e1]
    by_cases h : v < V0
    · have : 0 < V0 - v := sub_pos.mpr h
      rw [if_pos h, if_pos this, ENNReal.ofReal_mul hK]
    · have : ¬ 0 < V0 - v := by linarith [not_lt.mp h]
      rw [if_neg h, if_neg this]; simp
  · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]

private lemma rw3_Phi_meas (U c : ℝ) : Measurable (rw3Phi U c) := by
  unfold rw3Phi
  exact Measurable.ite (measurableSet_lt (measurable_id.add_const c) measurable_const)
    (ENNReal.measurable_ofReal.comp
      (rrVarpi_measurable.comp (measurable_const.sub (measurable_id.add_const c))))
    measurable_const

private lemma rw3_rrF_meas : Measurable rrF := by
  unfold rrF; fun_prop

private lemma rrWpart {U V0 b E S2 C1 n0 : ℝ} (hb : 0 < b) (hE : 0 < E) (hS : 0 ≤ S2)
    (hSC : S2 * Real.exp V0 = C1) (hn0 : (U - V0) / (2 * b) ≤ n0) (hn0' : 0 ≤ n0) :
    ∑' ℓ : ℕ, ∫⁻ q : ℝ × ℝ, ENNReal.ofReal
        (min (E * isoSinhRatio |q.1 - q.2|) (S2 * Real.exp ((q.1 + q.2) / 2)) *
          ((if q.1 < U ∧ q.2 + 2 * b * ((ℓ : ℝ) + 1) < U then 1 else 0) *
            ((1 + rrVarpi (U - q.1)) * rrVarpi (U - (q.2 + 2 * b * ((ℓ : ℝ) + 1))))))
      ≤ ENNReal.ofReal (2 * Real.log 2 * (E * (Real.pi ^ 2 + 2 * Real.log 2)) * n0 +
          2 * Real.log 2 * (((32 / 10 + 2 * Real.log 2) * C1 +
            (96 / 10 + 4 * Real.exp (1 / 2) * Real.log 2) * E) * (243 / 100 + 6 / (2 * b)))) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c0 : ℝ := E * (Real.pi ^ 2 + 2 * Real.log 2) with hc0def
  have hc0 : 0 ≤ c0 := by positivity
  have hC1 : 0 ≤ C1 := by rw [← hSC]; positivity
  set K : ℝ := (32 / 10 + 2 * Real.log 2) * C1 +
    (96 / 10 + 4 * Real.exp (1 / 2) * Real.log 2) * E with hKdef
  have hK : 0 ≤ K := by positivity
  have step1 : ∀ ℓ : ℕ, ∫⁻ q : ℝ × ℝ, ENNReal.ofReal
        (min (E * isoSinhRatio |q.1 - q.2|) (S2 * Real.exp ((q.1 + q.2) / 2)) *
          ((if q.1 < U ∧ q.2 + 2 * b * ((ℓ : ℝ) + 1) < U then 1 else 0) *
            ((1 + rrVarpi (U - q.1)) * rrVarpi (U - (q.2 + 2 * b * ((ℓ : ℝ) + 1)))))) ≤
      (if V0 < U - 2 * b * ((ℓ : ℝ) + 1) then ENNReal.ofReal (c0 * (2 * Real.log 2)) else 0) +
      ∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (rrVarpi ζ) * (ENNReal.ofReal K *
        ENNReal.ofReal (if 0 < (ζ - (U - V0)) + 2 * b * ((ℓ : ℝ) + 1) then
          rrF ((ζ - (U - V0)) + 2 * b * ((ℓ : ℝ) + 1)) else 0)) := by
    intro ℓ
    set c : ℝ := 2 * b * ((ℓ : ℝ) + 1) with hc
    refine (rw3_slice (U := U) (V0 := V0) (c := c) (E := E) (S2 := S2) (C1 := C1) hE hS hSC).trans ?_
    have hA : Measurable (fun v : ℝ => rw3Phi U c v *
        (if V0 ≤ v then ENNReal.ofReal c0 else 0)) :=
      (rw3_Phi_meas U c).mul (Measurable.ite (measurableSet_le measurable_const measurable_id)
        measurable_const measurable_const)
    rw [lintegral_congr (fun v => mul_add (rw3Phi U c v) _ _), lintegral_add_left hA]
    exact add_le_add (rw3_P1 hc0) (rw3_P2_eq (U := U) (V0 := V0) (c := c) hK).le
  refine (ENNReal.tsum_le_tsum step1).trans ?_
  rw [ENNReal.tsum_add]
  have hP1 : ∑' ℓ : ℕ, (if V0 < U - 2 * b * ((ℓ : ℝ) + 1) then ENNReal.ofReal (c0 * (2 * Real.log 2)) else 0)
      ≤ ENNReal.ofReal (c0 * (2 * Real.log 2) * n0) := by
    have : ∀ ℓ : ℕ, (if V0 < U - 2 * b * ((ℓ : ℝ) + 1) then ENNReal.ofReal (c0 * (2 * Real.log 2)) else 0)
        = ENNReal.ofReal (c0 * (2 * Real.log 2)) *
          (if (ℓ : ℝ) + 1 < (U - V0) / (2 * b) then (1 : ENNReal) else 0) := by
      intro ℓ
      have hiff : V0 < U - 2 * b * ((ℓ : ℝ) + 1) ↔ (ℓ : ℝ) + 1 < (U - V0) / (2 * b) := by
        rw [lt_div_iff₀ (by positivity)]
        constructor <;> intro h <;> nlinarith
      by_cases h : V0 < U - 2 * b * ((ℓ : ℝ) + 1)
      · rw [if_pos h, if_pos (hiff.mp h)]; simp
      · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]; simp
    simp_rw [this]
    rw [ENNReal.tsum_mul_left]
    calc _ ≤ ENNReal.ofReal (c0 * (2 * Real.log 2)) * ENNReal.ofReal n0 :=
          mul_le_mul' le_rfl (rw3_count hn0 hn0')
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hP2 : ∑' ℓ : ℕ, ∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (rrVarpi ζ) * (ENNReal.ofReal K *
        ENNReal.ofReal (if 0 < (ζ - (U - V0)) + 2 * b * ((ℓ : ℝ) + 1) then
          rrF ((ζ - (U - V0)) + 2 * b * ((ℓ : ℝ) + 1)) else 0)) ≤
      ENNReal.ofReal (2 * Real.log 2 * (K * (243 / 100 + 6 / (2 * b)))) := by
    rw [← lintegral_tsum]
    · calc _ ≤ ∫⁻ ζ in Ioi (0:ℝ), ENNReal.ofReal (rrVarpi ζ) *
            (ENNReal.ofReal K * ENNReal.ofReal (243 / 100 + 6 / (2 * b))) := by
            apply lintegral_mono; intro ζ
            dsimp only
            rw [ENNReal.tsum_mul_left]
            gcongr
            rw [ENNReal.tsum_mul_left]
            gcongr
            exact rrLattice (h := 2 * b) (by positivity) (ζ - (U - V0))
        _ = ENNReal.ofReal (2 * Real.log 2 * (K * (243 / 100 + 6 / (2 * b)))) := by
            rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
              rrVarpi_lintegral, ← ENNReal.ofReal_mul hK,
              ← ENNReal.ofReal_mul (by positivity)]
    · intro ℓ
      refine (ENNReal.measurable_ofReal.comp rrVarpi_measurable).aemeasurable.mul ?_
      refine (measurable_const.mul (ENNReal.measurable_ofReal.comp ?_)).aemeasurable
      exact Measurable.ite (measurableSet_lt measurable_const
        ((measurable_id.sub_const _).add_const _))
        (rw3_rrF_meas.comp ((measurable_id.sub_const _).add_const _)) measurable_const
  refine (add_le_add hP1 hP2).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply le_of_eq
  congr 1
  ring


private def rrG (E S2 U b : ℝ) (ℓ : ℕ) (q : ℝ × ℝ) : ℝ :=
  min (E * isoSinhRatio |q.1 - q.2|) (S2 * Real.exp ((q.1 + q.2) / 2)) *
    ((if q.1 < U ∧ q.2 + 2 * b * ((ℓ : ℝ) + 1) < U then 1 else 0) *
      (rrVarpi (U - q.1) + (1 + rrVarpi (U - q.1)) * rrVarpi (U - (q.2 + 2 * b * ((ℓ : ℝ) + 1)))))

private lemma rrG_meas (E S2 U b : ℝ) (ℓ : ℕ) : Measurable (rrG E S2 U b ℓ) := by
  unfold rrG
  have h1 := rrSinh_measurable
  have h2 := rrVarpi_measurable
  have hs : MeasurableSet {q : ℝ × ℝ | q.1 < U ∧ q.2 + 2 * b * ((ℓ : ℝ) + 1) < U} := by
    apply MeasurableSet.inter
    · exact measurableSet_lt measurable_fst measurable_const
    · exact measurableSet_lt (measurable_snd.add_const _) measurable_const
  refine Measurable.mul ?_ (Measurable.mul ?_ ?_)
  · refine Measurable.min ?_ ?_
    · exact measurable_const.mul (h1.comp (measurable_fst.sub measurable_snd).abs)
    · exact measurable_const.mul (Real.measurable_exp.comp ((measurable_fst.add measurable_snd).div_const 2))
  · exact Measurable.ite hs measurable_const measurable_const
  · exact (h2.comp (measurable_const.sub measurable_fst)).add
      ((measurable_const.add (h2.comp (measurable_const.sub measurable_fst))).mul
        (h2.comp (measurable_const.sub (measurable_snd.add_const _))))

private lemma rrLog_shift {β z : ℝ} (hβ0 : 0 < β) (hz : 0 < z) (ℓ : ℕ) :
    Real.log (z / β ^ (2 * (ℓ + 1))) = Real.log z + 2 * Real.log (1 / β) * ((ℓ : ℝ) + 1) := by
  have hb : (0:ℝ) < β ^ (2 * (ℓ + 1)) := pow_pos hβ0 _
  rw [Real.log_div hz.ne' hb.ne', Real.log_pow, one_div, Real.log_inv]
  push_cast
  ring

private lemma rrSqrt_exp {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    Real.sqrt (y * z) = Real.exp ((Real.log y + Real.log z) / 2) := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (Real.exp_pos _).le]
  rw [← Real.exp_add]
  have : (Real.log y + Real.log z) / 2 + (Real.log y + Real.log z) / 2 = Real.log y + Real.log z := by ring
  rw [this, Real.exp_add, Real.exp_log hy, Real.exp_log hz]

private lemma rrG_nonneg {E S2 U b : ℝ} (hE : 0 ≤ E) (hS : 0 ≤ S2) (ℓ : ℕ) (q : ℝ × ℝ) :
    0 ≤ rrG E S2 U b ℓ q := by
  unfold rrG
  by_cases hc : q.1 < U ∧ q.2 + 2 * b * ((ℓ : ℝ) + 1) < U
  · rw [if_pos hc]
    have h1 := rrVarpi_nonneg (sub_pos.mpr hc.1)
    have h2 := rrVarpi_nonneg (sub_pos.mpr hc.2)
    have h3 : 0 ≤ isoSinhRatio |q.1 - q.2| := rrSinh_nonneg _
    have : 0 ≤ min (E * isoSinhRatio |q.1 - q.2|) (S2 * Real.exp ((q.1 + q.2) / 2)) :=
      le_min (mul_nonneg hE h3) (mul_nonneg hS (Real.exp_pos _).le)
    positivity
  · rw [if_neg hc]; simp

private lemma rrStepA {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hϱ : 0 < ϱ) (ℓ : ℕ) :
    isoSharpLag β γ ϱ (ℓ + 1) ≤ ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3)) *
      (ENNReal.ofReal (isoK6 β * γ ^ 2) *
        ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (rrG (isoEbar β) (Muon.sPow β 2)
          (Real.log (isoQpsi β γ ϱ)) (Real.log (1 / β)) ℓ q)) := by
  have hγ0 := rf6_gamma_pos hβ1 hβ0 hγ
  have hK60 : (0:ℝ) ≤ isoK6 β := le_trans (by norm_num) (le_max_left _ _)
  have hK6 : 0 ≤ isoK6 β * γ ^ 2 := by positivity
  have hE0 : 0 ≤ isoEbar β := le_trans zero_le_one (le_max_left _ _)
  have hS0 : 0 ≤ Muon.sPow β 2 := by
    rw [Muon.sPow_eq hβ0.le hβ1 le_rfl]
    have : 0 < 1 - β := by linarith
    have : 0 < 1 - β ^ 2 := by nlinarith
    positivity
  have hG0 := rrG_nonneg (U := Real.log (isoQpsi β γ ϱ)) (b := Real.log (1 / β)) hE0 hS0 ℓ
  unfold isoSharpLag isoRepCoeffEN
  gcongr
  rw [← rrCoV _ (rrG_meas _ _ _ _ _) hG0, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' (measurableSet_Ioi.prod measurableSet_Ioi) ?_
  rintro ⟨y, z⟩ ⟨hy, hz⟩
  simp only [mem_Ioi] at hy hz
  by_cases hc : y < isoQpsi β γ ϱ ∧ z / β ^ (2 * (ℓ + 1)) < isoQpsi β γ ϱ
  · have hQ0 : 0 < isoQpsi β γ ϱ := by
      unfold isoQpsi; rw [if_pos hϱ]; exact (rf6_root hβ0 hβ1 hγ0 hϱ).1
    have hzb : 0 < z / β ^ (2 * (ℓ + 1)) := div_pos hz (pow_pos hβ0 _)
    have hP := rrPointwiseZ hβ0 hβ1 hγ hϱ (ℓ := ℓ + 1) (by omega) hy hz hc.1 hc.2
    have hZ := (lem_app_iso_kernel_bounds_ii hβ0 hβ1 hy hz).2.1
    rw [Real.log_div hy.ne' hz.ne', rrSqrt_exp hy hz] at hZ
    have hc1 : Real.log y < Real.log (isoQpsi β γ ϱ) := Real.log_lt_log hy hc.1
    have hc2 : Real.log z + 2 * Real.log (1 / β) * ((ℓ : ℝ) + 1) < Real.log (isoQpsi β γ ϱ) := by
      rw [← rrLog_shift hβ0 hz]; exact Real.log_lt_log hzb hc.2
    rw [rrLog_shift hβ0 hz] at hP
    have hv1 := rrVarpi_nonneg (sub_pos.mpr hc1)
    have hv2 := rrVarpi_nonneg (sub_pos.mpr hc2)
    have hyz : 0 < y * z := mul_pos hy hz
    rw [← ENNReal.ofReal_mul hK6]
    apply ENNReal.ofReal_le_ofReal
    have hcond : (if y < isoQpsi β γ ϱ ∧ z / β ^ (2 * (ℓ + 1)) < isoQpsi β γ ϱ then (1:ℝ) else 0) = 1 :=
      if_pos hc
    rw [hcond]
    have hGe : rrG (isoEbar β) (Muon.sPow β 2) (Real.log (isoQpsi β γ ϱ)) (Real.log (1 / β)) ℓ
        (Real.log y, Real.log z) = min (isoEbar β * isoSinhRatio |Real.log y - Real.log z|)
          (Muon.sPow β 2 * Real.exp ((Real.log y + Real.log z) / 2)) *
        (rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log y) +
          (1 + rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log y)) *
            rrVarpi (Real.log (isoQpsi β γ ϱ) - (Real.log z + 2 * Real.log (1 / β) * ((ℓ : ℝ) + 1)))) := by
      unfold rrG
      rw [if_pos ⟨hc1, hc2⟩]; ring
    rw [hGe]
    have hT : 0 ≤ rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log y) +
          (1 + rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log y)) *
            rrVarpi (Real.log (isoQpsi β γ ϱ) - (Real.log z + 2 * Real.log (1 / β) * ((ℓ : ℝ) + 1))) := by
      positivity
    generalize hTg : rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log y) +
          (1 + rrVarpi (Real.log (isoQpsi β γ ϱ) - Real.log y)) *
            rrVarpi (Real.log (isoQpsi β γ ϱ) - (Real.log z + 2 * Real.log (1 / β) * ((ℓ : ℝ) + 1))) = T at hP hT ⊢
    have h1 : isoZkern β y z / (y * z) * T ≤
        min (isoEbar β * isoSinhRatio |Real.log y - Real.log z|)
          (Muon.sPow β 2 * Real.exp ((Real.log y + Real.log z) / 2)) / (y * z) * T :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hZ hyz.le) hT
    calc _ ≤ isoK6 β * γ ^ 2 * (isoZkern β y z / (y * z)) * T := by simpa only [one_mul] using hP
      _ = isoK6 β * γ ^ 2 * (isoZkern β y z / (y * z) * T) := by ring
      _ ≤ isoK6 β * γ ^ 2 * (min (isoEbar β * isoSinhRatio |Real.log y - Real.log z|)
          (Muon.sPow β 2 * Real.exp ((Real.log y + Real.log z) / 2)) / (y * z) * T) :=
        mul_le_mul_of_nonneg_left h1 hK6
      _ = _ := by ring
  · rw [if_neg hc]; simp


private lemma rrStepB {U V0 b E S2 C1 n0 : ℝ} (hb : 0 < b) (hE : 0 < E) (hS : 0 ≤ S2)
    (hSC : S2 * Real.exp V0 = C1) (hn0 : (U - V0) / (2 * b) ≤ n0) (hn0' : 0 ≤ n0) :
    ∑' ℓ : ℕ, ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (rrG E S2 U b ℓ q) ≤
      ENNReal.ofReal (E / (2 * b) * (Real.pi ^ 4 / 6 + 56 * (riemannZeta 3).re * Real.log 2)) +
      ENNReal.ofReal (2 * Real.log 2 * (E * (Real.pi ^ 2 + 2 * Real.log 2)) * n0 +
          2 * Real.log 2 * (((32 / 10 + 2 * Real.log 2) * C1 +
            (96 / 10 + 4 * Real.exp (1 / 2) * Real.log 2) * E) * (243 / 100 + 6 / (2 * b)))) := by
  refine le_trans ?_ (add_le_add (rrNpart (U := U) hb hE) (rrWpart (V0 := V0) (n0 := n0) (C1 := C1) (S2 := S2) hb hE hS hSC hn0 hn0'))
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun ℓ => ?_
  rw [← lintegral_add_left]
  · refine lintegral_mono fun q => ?_
    rw [← ENNReal.ofReal_add]
    · apply ENNReal.ofReal_le_ofReal
      unfold rrG
      by_cases hc : q.1 < U ∧ q.2 + 2 * b * ((ℓ : ℝ) + 1) < U
      · rw [if_pos hc]
        have h1 := rrVarpi_nonneg (sub_pos.mpr hc.1)
        have h2 := rrVarpi_nonneg (sub_pos.mpr hc.2)
        have hm : min (E * isoSinhRatio |q.1 - q.2|) (S2 * Real.exp ((q.1 + q.2) / 2)) ≤
            E * isoSinhRatio |q.1 - q.2| := min_le_left _ _
        have hm0 : 0 ≤ min (E * isoSinhRatio |q.1 - q.2|) (S2 * Real.exp ((q.1 + q.2) / 2)) :=
          le_min (mul_nonneg hE.le (rrSinh_nonneg _)) (mul_nonneg hS (Real.exp_pos _).le)
        nlinarith [mul_le_mul_of_nonneg_right hm h1]
      · rw [if_neg hc]; simp
    · by_cases hc : q.1 < U ∧ q.2 + 2 * b * ((ℓ : ℝ) + 1) < U
      · rw [if_pos hc]
        have h1 := rrVarpi_nonneg (sub_pos.mpr hc.1)
        have := rrSinh_nonneg |q.1 - q.2|
        positivity
      · rw [if_neg hc]; simp
    · by_cases hc : q.1 < U ∧ q.2 + 2 * b * ((ℓ : ℝ) + 1) < U
      · rw [if_pos hc]
        have h1 := rrVarpi_nonneg (sub_pos.mpr hc.1)
        have h2 := rrVarpi_nonneg (sub_pos.mpr hc.2)
        have hm0 : 0 ≤ min (E * isoSinhRatio |q.1 - q.2|) (S2 * Real.exp ((q.1 + q.2) / 2)) :=
          le_min (mul_nonneg hE.le (rrSinh_nonneg _)) (mul_nonneg hS (Real.exp_pos _).le)
        positivity
      · rw [if_neg hc]; simp
  · have h1 := rrSinh_measurable
    have h2 := rrVarpi_measurable
    have hs : MeasurableSet {q : ℝ × ℝ | q.1 < U ∧ q.2 + 2 * b * ((ℓ : ℝ) + 1) < U} := by
      apply MeasurableSet.inter
      · exact measurableSet_lt measurable_fst measurable_const
      · exact measurableSet_lt (measurable_snd.add_const _) measurable_const
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.mul ?_ (Measurable.mul ?_ ?_)
    · exact measurable_const.mul (h1.comp (measurable_fst.sub measurable_snd).abs)
    · exact Measurable.ite hs measurable_const measurable_const
    · exact h2.comp (measurable_const.sub measurable_fst)


private lemma rrFinalReal {β γ ψ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hψ : 0 ≤ ψ) :
    1 / (Real.pi ^ 2 * γ ^ 3) * (isoK6 β * γ ^ 2 *
      (isoEbar β / (2 * Real.log (1 / β)) * (Real.pi ^ 4 / 6 + 56 * (riemannZeta 3).re * Real.log 2) +
        (2 * Real.log 2 * (isoEbar β * (Real.pi ^ 2 + 2 * Real.log 2)) * (ψ + isoC β) +
          2 * Real.log 2 * (((32 / 10 + 2 * Real.log 2) * (1 / (1 - β ^ 2)) +
            (96 / 10 + 4 * Real.exp (1 / 2) * Real.log 2) * isoEbar β) *
              (243 / 100 + 6 / (2 * Real.log (1 / β))))))) ≤
      (isoKexFlat β + isoKexSharp β * ψ) / γ := by
  have hb : 0 < Real.log (1 / β) := by
    apply Real.log_pos; rw [lt_div_iff₀ hβ0]; linarith
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE : 0 < isoEbar β := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK60 : (0:ℝ) ≤ isoK6 β := le_trans (by norm_num) (le_max_left _ _)
  have hd : 0 < 1 - β ^ 2 := by nlinarith
  have hc : 0 ≤ isoC β := by unfold isoC; have : 0 < 1 - β := by linarith
                             positivity
  have hKJ : 0 ≤ isoKJ β := by unfold isoKJ; positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  set b := Real.log (1 / β) with hbdef
  set E := isoEbar β
  set L := Real.log 2
  set c := isoC β
  have hKJe : isoKJ β = (3.2 + 2 * L) * (1 / (1 - β ^ 2)) + (9.6 + 4 * Real.exp (1 / 2) * L) * E := by
    unfold isoKJ; rw [mul_one_div]
  set N := E / (2 * b) * (Real.pi ^ 4 / 6 + 56 * (riemannZeta 3).re * L) with hN
  have hRHS : (isoKexFlat β + isoKexSharp β * ψ) / γ =
      isoK6 β / Real.pi ^ 2 * (N + 4 * L * (E * (Real.pi ^ 2 + 2 * L) * (c + 1) +
        isoKJ β * (3.64 + 3 / b)) + 4 * L * (E * (Real.pi ^ 2 + 2 * L)) * ψ) / γ := by
    unfold isoKexFlat isoKexSharp
    ring
  rw [hRHS]
  have hLHS : 1 / (Real.pi ^ 2 * γ ^ 3) * (isoK6 β * γ ^ 2 * (N + (2 * L * (E * (Real.pi ^ 2 + 2 * L)) * (ψ + c) +
          2 * L * (((32 / 10 + 2 * L) * (1 / (1 - β ^ 2)) +
            (96 / 10 + 4 * Real.exp (1 / 2) * L) * E) *
              (243 / 100 + 6 / (2 * b)))))) =
      isoK6 β / Real.pi ^ 2 * (N + (2 * L * (E * (Real.pi ^ 2 + 2 * L)) * (ψ + c) +
          2 * L * (((32 / 10 + 2 * L) * (1 / (1 - β ^ 2)) +
            (96 / 10 + 4 * Real.exp (1 / 2) * L) * E) *
              (243 / 100 + 6 / (2 * b))))) / γ := by
    field_simp
  rw [hLHS]
  have hkj : ((32 / 10 + 2 * L) * (1 / (1 - β ^ 2)) +
            (96 / 10 + 4 * Real.exp (1 / 2) * L) * E) = isoKJ β := by
    rw [hKJe]; norm_num
  rw [hkj]
  apply div_le_div_of_nonneg_right _ hγ0.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h3 : 0 < 3 / b := by positivity
  have hq : 0 ≤ E * (Real.pi ^ 2 + 2 * L) := by positivity
  have hq2 : 0 ≤ L * (E * (Real.pi ^ 2 + 2 * L)) := by positivity
  have hq3 : 0 ≤ L * isoKJ β * (3 / b) := by positivity
  have hq4 : 0 ≤ L * isoKJ β := by positivity
  have e6 : 6 / (2 * b) = 3 / b := by field_simp; ring
  rw [e6]
  nlinarith [mul_nonneg hq2 hc, mul_nonneg hq2 hψ, mul_nonneg hq2 (zero_le_one' ℝ)]


/-! ## Ridge excess -/

/-- `lem:app-iso-ridge-excess`. Index shift: the source sum over `ℓ ≥ 1` is `ℓ + 1` over `ℕ`. 

`lem:app-iso-ridge-excess`, snapshot `cr-2026-10-23`, `section.tex` l.3159-3164.

LaTeX (verbatim):
\begin{lemma}[Ridge excess]\label{lem:app-iso-ridge-excess}
Let $\gamma\ge\gamma^\circ_\bmom$ and $\ridge>0$. Then
\[
\sum_{\ell\ge1}\overline C^{\,\sharp}_{\ell}(\ridge)\le\frac{\mathsf K^\flat_{\rm ex}+\mathsf K^\sharp_{\rm ex}\,\psi(\ridge)}\gamma .
\]
\end{lemma}
-/
theorem lem_app_iso_ridge_excess {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : isoGammaCirc β ≤ γ) (hϱ : 0 < ϱ) :
    ∑' ℓ : ℕ, isoSharpLag β γ ϱ (ℓ + 1) ≤
      ENNReal.ofReal ((isoKexFlat β + isoKexSharp β * psiIso β γ γ ϱ) / γ) := by
  have hγ0 := rf6_gamma_pos hβ1 hβ0 hγ
  have hb : 0 < Real.log (1 / β) := by
    apply Real.log_pos; rw [lt_div_iff₀ hβ0]; linarith
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE : 0 < isoEbar β := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK60 : (0:ℝ) ≤ isoK6 β := le_trans (by norm_num) (le_max_left _ _)
  have h1β : 0 < 1 - β := by linarith
  have hd : 0 < 1 - β ^ 2 := by nlinarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hz3 : 0 < (riemannZeta 3).re := rrF2_zeta3_pos
  have hQeq : isoQpsi β γ ϱ = qIso β γ γ ϱ := by unfold isoQpsi; rw [if_pos hϱ]
  obtain ⟨hQ0, hQr, -⟩ := rf6_root hβ0 hβ1 hγ0 hϱ
  have hQ0' : 0 < isoQpsi β γ ϱ := hQeq ▸ hQ0
  have hψ : psiIso β γ γ ϱ = Muon.DetEquiv.rW (Muon.emaW β) (isoQpsi β γ ϱ) := by
    rw [hQeq]; rfl
  have hψ0 : 0 ≤ psiIso β γ γ ϱ := by
    rw [hψ, ← hQeq] at *
    have hr := rf6_isoLink hβ0 hβ1
    have := hr.2.1 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hQ0'.le) hQ0'
    rw [hr.2.2] at this
    exact this.le
  have hc0 : 0 ≤ isoC β := by unfold isoC; positivity
  have hSC : Muon.sPow β 2 * Real.exp (-2 * Real.log (1 - β)) = 1 / (1 - β ^ 2) := by
    rw [Muon.sPow_eq hβ0.le hβ1 le_rfl]
    have : Real.exp (-2 * Real.log (1 - β)) = ((1 - β) ^ 2)⁻¹ := by
      have e2 : (2:ℝ) * Real.log (1 - β) = Real.log ((1 - β) ^ 2) := by
        rw [Real.log_pow]; push_cast; ring
      rw [neg_mul, Real.exp_neg, e2, Real.exp_log (pow_pos h1β 2)]
    rw [this]
    field_simp
  have hS0 : 0 ≤ Muon.sPow β 2 := by
    rw [Muon.sPow_eq hβ0.le hβ1 le_rfl]; positivity
  have hn0 : (Real.log (isoQpsi β γ ϱ) - (-2 * Real.log (1 - β))) / (2 * Real.log (1 / β)) ≤
      psiIso β γ γ ϱ + isoC β := by
    have hid : (Real.log (isoQpsi β γ ϱ) - (-2 * Real.log (1 - β))) / (2 * Real.log (1 / β)) =
        isoN β (isoQpsi β γ ϱ) := by
      unfold isoN
      congr 1
      rw [Real.log_mul (pow_pos h1β 2).ne' hQ0'.ne', Real.log_pow]
      push_cast; ring
    rw [hid]
    by_cases hx : 1 ≤ (1 - β) ^ 2 * isoQpsi β γ ϱ
    · have := ((lem_app_iso_count_i hβ0 hβ1).1 _ hx).1
      rw [hψ]; linarith
    · have : Real.log ((1 - β) ^ 2 * isoQpsi β γ ϱ) < 0 := Real.log_neg (mul_pos (pow_pos h1β 2) hQ0') (not_le.mp hx)
      have : isoN β (isoQpsi β γ ϱ) ≤ 0 := by
        unfold isoN; exact div_nonpos_of_nonpos_of_nonneg this.le (by positivity)
      linarith
  calc ∑' ℓ : ℕ, isoSharpLag β γ ϱ (ℓ + 1)
      ≤ ∑' ℓ : ℕ, ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3)) *
        (ENNReal.ofReal (isoK6 β * γ ^ 2) *
          ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (rrG (isoEbar β) (Muon.sPow β 2)
            (Real.log (isoQpsi β γ ϱ)) (Real.log (1 / β)) ℓ q)) :=
        ENNReal.tsum_le_tsum fun ℓ => rrStepA hβ0 hβ1 hγ hϱ ℓ
    _ = ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3)) * (ENNReal.ofReal (isoK6 β * γ ^ 2) *
        ∑' ℓ : ℕ, ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (rrG (isoEbar β) (Muon.sPow β 2)
            (Real.log (isoQpsi β γ ϱ)) (Real.log (1 / β)) ℓ q)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3)) * (ENNReal.ofReal (isoK6 β * γ ^ 2) *
        (ENNReal.ofReal (isoEbar β / (2 * Real.log (1 / β)) *
            (Real.pi ^ 4 / 6 + 56 * (riemannZeta 3).re * Real.log 2)) +
         ENNReal.ofReal (2 * Real.log 2 * (isoEbar β * (Real.pi ^ 2 + 2 * Real.log 2)) *
            (psiIso β γ γ ϱ + isoC β) +
          2 * Real.log 2 * (((32 / 10 + 2 * Real.log 2) * (1 / (1 - β ^ 2)) +
            (96 / 10 + 4 * Real.exp (1 / 2) * Real.log 2) * isoEbar β) *
              (243 / 100 + 6 / (2 * Real.log (1 / β))))))) := by
        gcongr
        exact rrStepB (V0 := -2 * Real.log (1 - β)) hb hE hS0 hSC hn0 (by linarith)
    _ = ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3) * (isoK6 β * γ ^ 2 *
      (isoEbar β / (2 * Real.log (1 / β)) * (Real.pi ^ 4 / 6 + 56 * (riemannZeta 3).re * Real.log 2) +
        (2 * Real.log 2 * (isoEbar β * (Real.pi ^ 2 + 2 * Real.log 2)) * (psiIso β γ γ ϱ + isoC β) +
          2 * Real.log 2 * (((32 / 10 + 2 * Real.log 2) * (1 / (1 - β ^ 2)) +
            (96 / 10 + 4 * Real.exp (1 / 2) * Real.log 2) * isoEbar β) *
              (243 / 100 + 6 / (2 * Real.log (1 / β)))))))) := by
        have hN : 0 ≤ isoEbar β / (2 * Real.log (1 / β)) *
            (Real.pi ^ 4 / 6 + 56 * (riemannZeta 3).re * Real.log 2) := by positivity
        have hW : 0 ≤ 2 * Real.log 2 * (isoEbar β * (Real.pi ^ 2 + 2 * Real.log 2)) *
            (psiIso β γ γ ϱ + isoC β) +
          2 * Real.log 2 * (((32 / 10 + 2 * Real.log 2) * (1 / (1 - β ^ 2)) +
            (96 / 10 + 4 * Real.exp (1 / 2) * Real.log 2) * isoEbar β) *
              (243 / 100 + 6 / (2 * Real.log (1 / β)))) := by positivity
        rw [← ENNReal.ofReal_add hN hW, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (rrFinalReal hβ0 hβ1 hγ0 hψ0)


/-! ## Private helpers for the ridge volatility (task P-F.11.P2) -/

/-! ## Private helpers for the ridge volatility (task P-F.11.P2) -/

private lemma rvr_link {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsIsoLink (Muon.DetEquiv.rW (Muon.emaW β)) := by
  obtain ⟨_, hd, hmono, _⟩ := lem_app_iso_weights_i hβ0.le hβ1
  refine ⟨fun q hq => (hd q hq).1.continuousWithinAt, (hmono hβ0).1, ?_⟩
  unfold Muon.DetEquiv.rW; simp

private lemma rvr_gamma_pos {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ) :
    0 < γ := by
  have h : 0 < 1 - β ^ 2 := by nlinarith [sq_nonneg β]
  have : 0 < isoC' β := by unfold isoC'; positivity
  unfold isoGammaCirc at hγ
  linarith

/-- `Q_ψ = q(-ϱ)`, its level `ψ`, and `0 < ψ < γ`. -/
private lemma rvr_Q_spec {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 < ϱ) :
    0 < isoQpsi β γ ϱ ∧ Muon.DetEquiv.rW (Muon.emaW β) (isoQpsi β γ ϱ) = psiIso β γ γ ϱ ∧
      0 < psiIso β γ γ ϱ ∧ psiIso β γ γ ϱ < γ := by
  have hlink := rvr_link hβ0 hβ1
  have hmem := ((lem_app_iso_comparison_i hlink hγ hγ).2.2.2.1 ϱ hϱ)
  obtain ⟨hD, hG⟩ := hmem
  have hQ : isoQpsi β γ ϱ = qIso β γ γ ϱ := by unfold isoQpsi; rw [if_pos hϱ]
  have hψ : psiIso β γ γ ϱ = Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ ϱ) := rfl
  have hD' : 0 ≤ qIso β γ γ ϱ ∧ Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ ϱ) < γ := by
    have := hD; unfold isoDr at this; simp only [mem_setOf_eq, min_self] at this
    exact this
  have hG' : ϱ * qIso β γ γ ϱ = (γ - Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ ϱ)) ^ 2 := by
    have := hG; unfold isoG at this; unfold qIso; nlinarith [this]
  have hQpos : 0 < qIso β γ γ ϱ := by
    rcases hD'.1.eq_or_lt with h | h
    · exfalso
      have := pow_pos (sub_pos.2 hD'.2) 2
      rw [← hG', ← h] at this; simp at this
    · exact h
  refine ⟨by rw [hQ]; exact hQpos, by rw [hQ, hψ], ?_, by rw [hψ]; exact hD'.2⟩
  rw [hψ]
  have := hlink.2.1 (mem_Ici.2 le_rfl) (mem_Ici.2 hQpos.le) hQpos
  rw [hlink.2.2] at this
  exact this

private lemma rvr_lt_iff {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q m y : ℝ} (hQ : 0 < Q)
    (hr : Muon.DetEquiv.rW (Muon.emaW β) Q = m) (hy : 0 < y) :
    y < Q ↔ Muon.DetEquiv.rW (Muon.emaW β) y < m := by
  have hs := (rvr_link hβ0 hβ1).2.1
  constructor
  · intro h
    have := hs (mem_Ici.2 hy.le) (mem_Ici.2 hQ.le) h
    rwa [hr] at this
  · intro h
    by_contra hc
    push_neg at hc
    have := hs.monotoneOn (mem_Ici.2 hQ.le) (mem_Ici.2 hy.le) hc
    rw [hr] at this
    linarith

private lemma rvr_Qlevel_spec {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < isoQlevel β m ∧ Muon.DetEquiv.rW (Muon.emaW β) (isoQlevel β m) = m := by
  have hbij := ((lem_app_iso_weights_i hβ0.le hβ1).2.2.1 hβ0).2
  obtain ⟨q, hq, e⟩ := hbij.2.2 (mem_Ici.2 hm.le)
  have hex : ∃ q : ℝ, 0 ≤ q ∧ Muon.DetEquiv.rW (Muon.emaW β) q = m := ⟨q, hq, e⟩
  have h1 : 0 ≤ isoQlevel β m ∧ Muon.DetEquiv.rW (Muon.emaW β) (isoQlevel β m) = m := by
    unfold isoQlevel
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨?_, h1.2⟩
  rcases h1.1.eq_or_lt with h | h
  · exfalso
    have hz : Muon.DetEquiv.rW (Muon.emaW β) 0 = 0 := (rvr_link hβ0 hβ1).2.2
    have h2 := h1.2
    rw [← h, hz] at h2
    linarith
  · exact h

private lemma rvr_eslope_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {y : ℝ} (hy : 0 < y) :
    0 ≤ isoEslope β y := by
  unfold isoEslope
  exact ((lem_app_iso_count_ii hβ0 hβ1).1 y hy).1.le

private lemma rvr_u_ge {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 < ϱ)
    {y : ℝ} (hy : 0 < y) (hyQ : y < isoQpsi β γ ϱ) : 1 ≤ isoUlev β γ ϱ y := by
  obtain ⟨hQ0, hrQ, hψ0, hψγ⟩ := rvr_Q_spec hβ0 hβ1 hγ hϱ
  have hQeq : isoQpsi β γ ϱ = qIso β γ γ ϱ := by unfold isoQpsi; rw [if_pos hϱ]
  have hG' : ϱ * isoQpsi β γ ϱ = (γ - psiIso β γ γ ϱ) ^ 2 := by
    have hlink := rvr_link hβ0 hβ1
    have hmem := ((lem_app_iso_comparison_i hlink hγ hγ).2.2.2.1 ϱ hϱ)
    have := hmem.2
    unfold isoG at this
    rw [hQeq]
    unfold psiIso qIso at *
    nlinarith [this]
  have hry : Muon.DetEquiv.rW (Muon.emaW β) y < psiIso β γ γ ϱ := (rvr_lt_iff hβ0 hβ1 hQ0 hrQ hy).1 hyQ
  have hA : γ - psiIso β γ γ ϱ < isoResid β γ y := by unfold isoResid; linarith
  have hA0 : 0 < γ - psiIso β γ γ ϱ := by linarith
  have hA2 : (γ - psiIso β γ γ ϱ) ^ 2 < isoResid β γ y ^ 2 :=
    pow_lt_pow_left₀ hA hA0.le (by norm_num)
  have hlt : ϱ * y < isoResid β γ y ^ 2 := by nlinarith
  have hRpos : 0 < isoResid β γ y ^ 2 := lt_of_le_of_lt (by positivity) hlt
  unfold isoUlev
  apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos
  · rw [sub_pos, div_lt_one hRpos]; exact hlt
  · have : 0 ≤ ϱ * y / isoResid β γ y ^ 2 := by positivity
    linarith
  · norm_num

private lemma rvr_lag_nonneg {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {ϱ : ℝ}
    (hϱ : 0 ≤ ϱ) (ℓ : ℕ) : 0 ≤ lagCoeff β γ ϱ ℓ := by
  have hlink := rvr_link hβ0 hβ1
  have hq : ∀ s : ℝ, 0 < s → 0 ≤ qIso β γ γ s := by
    intro s hs
    have hmem := ((lem_app_iso_comparison_i hlink hγ hγ).2.2.2.1 s hs).1
    exact hmem.1
  unfold lagCoeff
  refine mul_nonneg (by positivity) ?_
  refine setIntegral_nonneg measurableSet_Ioi (fun x hx => ?_)
  refine setIntegral_nonneg measurableSet_Ioi (fun y hy => ?_)
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  have hs : 0 < ϱ + x ^ 2 := by positivity
  have hs' : 0 < ϱ + y ^ 2 := by positivity
  obtain ⟨⟨hB0, -⟩, -, -, hD0, -⟩ := lem_app_iso_lag_i hβ0 hβ1 hγ hs hs' ℓ
  unfold lagKernel
  exact div_nonneg (mul_nonneg (mul_nonneg hB0 (hq _ hs)) (hq _ hs'))
    (mul_nonneg (by positivity) hD0.le)

private lemma rvr_n (L : ℝ) :
    ∃ n : ℕ, (∀ ℓ : ℕ, ((ℓ : ℝ) + 1 < L ↔ ℓ < n)) ∧ (n : ℝ) ≤ max L 0 ∧
      (0 < L → (n : ℝ) < L ∧ L - 1 ≤ n) := by
  refine ⟨⌈L⌉₊ - 1, ?_, ?_, ?_⟩
  · intro ℓ
    have h1 : (ℓ : ℝ) + 1 < L ↔ ℓ + 1 < ⌈L⌉₊ := by
      rw [Nat.lt_ceil]; push_cast; rfl
    rw [h1]; omega
  · rcases le_or_gt L 0 with h | h
    · have : ⌈L⌉₊ = 0 := Nat.ceil_eq_zero.2 h
      simp [this]
    · have := Nat.ceil_lt_add_one h.le
      have h2 : (((⌈L⌉₊ - 1 : ℕ)) : ℝ) ≤ (⌈L⌉₊ : ℝ) - 1 := by
        have h0 : 0 < ⌈L⌉₊ := Nat.ceil_pos.2 h
        rw [Nat.cast_sub h0]; simp
      rw [max_eq_left h.le]; linarith
  · intro h
    have h1 := Nat.ceil_lt_add_one h.le
    have h2 := Nat.le_ceil L
    have hp : 0 < ⌈L⌉₊ := Nat.ceil_pos.2 h
    rw [Nat.cast_sub hp]; push_cast
    constructor <;> linarith

private lemma rvr_sumrange (c : ℝ) (n : ℕ) :
    ∑ ℓ ∈ Finset.range n, (c - ((ℓ : ℝ) + 1)) = n * c - n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

private lemma rvr_gsum (L g e : ℝ) (hg : 0 ≤ g) (he : 0 ≤ e) :
    Summable (fun ℓ : ℕ => if (ℓ : ℝ) + 1 < L then L + g - ((ℓ : ℝ) + 1) + 2 * e else 0) ∧
    (∀ ℓ : ℕ, 0 ≤ (if (ℓ : ℝ) + 1 < L then L + g - ((ℓ : ℝ) + 1) + 2 * e else 0)) ∧
    ∑' ℓ : ℕ, (if (ℓ : ℝ) + 1 < L then L + g - ((ℓ : ℝ) + 1) + 2 * e else 0) ≤
      (max L 0) ^ 2 / 2 + (g + 2 * e) * max L 0 := by
  obtain ⟨n, hn, hnM, hnL⟩ := rvr_n L
  set f : ℕ → ℝ := fun ℓ => if (ℓ : ℝ) + 1 < L then L + g - ((ℓ : ℝ) + 1) + 2 * e else 0 with hf
  have hf0 : ∀ ℓ, 0 ≤ f ℓ := by
    intro ℓ
    simp only [hf]
    split_ifs with h
    · linarith
    · exact le_rfl
  have hz : ∀ ℓ ∉ Finset.range n, f ℓ = 0 := by
    intro ℓ hℓ
    simp only [hf]
    rw [if_neg]
    rw [hn]; simpa using hℓ
  have hs : HasSum f (∑ ℓ ∈ Finset.range n, f ℓ) := hasSum_sum_of_ne_finset_zero hz
  refine ⟨hs.summable, hf0, ?_⟩
  rw [hs.tsum_eq]
  have : ∑ ℓ ∈ Finset.range n, f ℓ =
      ∑ ℓ ∈ Finset.range n, ((L + g + 2 * e) - ((ℓ : ℝ) + 1)) := by
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    simp only [hf]
    rw [if_pos ((hn ℓ).2 (Finset.mem_range.1 hℓ))]; ring
  rw [this, rvr_sumrange]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases le_or_gt L 0 with h | h
  · have : n = 0 := by
      have := (hnM.trans_eq (max_eq_right h))
      exact_mod_cast le_antisymm this hn0
    subst this
    rw [max_eq_right h]; simp
  · obtain ⟨h1, h2⟩ := hnL h
    rw [max_eq_left h.le]
    nlinarith [sq_nonneg (L - n), mul_nonneg (add_nonneg hg (mul_nonneg zero_le_two he)) (sub_nonneg.2 h1.le)]

/-- The lag-summed shape `T(z) = ∑_{ℓ≥1} 1{z_ℓ<Q} 𝗃(z_ℓ)`, indexed by `ℓ+1`. -/
private def rvT (β γ Q z : ℝ) : ℝ :=
  ∑' ℓ : ℕ, if z / β ^ (2 * (ℓ + 1)) < Q
    then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0

private lemma rvr_term {β γ Q ψ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : 0 < Q)
    (hr : Muon.DetEquiv.rW (Muon.emaW β) Q = ψ) (hψγ : ψ < γ) {z : ℝ} (hz : 0 < z) (ℓ : ℕ) :
    0 ≤ (if z / β ^ (2 * (ℓ + 1)) < Q then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0) ∧
    (if z / β ^ (2 * (ℓ + 1)) < Q then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0) ≤
      (if (ℓ : ℝ) + 1 < (ψ - isoN β z + isoC β)
        then (ψ - isoN β z + isoC β) + (γ - ψ) - ((ℓ : ℝ) + 1) + 2 * isoEbar β else 0) := by
  have hE : 0 ≤ isoEbar β := le_trans zero_le_one (le_max_left _ _)
  have hzk : 0 < z / β ^ (2 * (ℓ + 1)) := div_pos hz (pow_pos hβ0 _)
  have hsh := lem_app_iso_shifts_ii hβ0 hβ1 z hz (ℓ + 1)
  push_cast at hsh
  split_ifs with h1 h2
  · have hr' := (rvr_lt_iff hβ0 hβ1 hQ hr hzk).1 h1
    have he0 := rvr_eslope_nonneg hβ0 hβ1 hzk
    have he1 := (lem_app_iso_slope hβ0 hβ1 _ hzk).1.trans (lem_app_iso_slope hβ0 hβ1 _ hzk).2
    unfold isoWeightJ isoResid
    constructor <;> linarith
  · exfalso
    apply h2
    have hr' := (rvr_lt_iff hβ0 hβ1 hQ hr hzk).1 h1
    linarith
  · rename_i h2
    constructor
    · exact le_rfl
    · linarith [hE]
  · exact ⟨le_rfl, le_rfl⟩

private lemma rvr_T_upper {β γ Q ψ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : 0 < Q)
    (hr : Muon.DetEquiv.rW (Muon.emaW β) Q = ψ) (hψγ : ψ < γ) {z : ℝ} (hz : 0 < z) :
    (Summable fun ℓ : ℕ => if z / β ^ (2 * (ℓ + 1)) < Q
        then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0) ∧
    (∀ ℓ : ℕ, 0 ≤ (if z / β ^ (2 * (ℓ + 1)) < Q
        then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0)) ∧
    rvT β γ Q z ≤ (max (ψ - isoN β z + isoC β) 0) ^ 2 / 2
      + ((γ - ψ) + 2 * isoEbar β) * max (ψ - isoN β z + isoC β) 0 := by
  have hE : 0 ≤ isoEbar β := le_trans zero_le_one (le_max_left _ _)
  obtain ⟨hgs, -, hgt⟩ := rvr_gsum (ψ - isoN β z + isoC β) (γ - ψ) (isoEbar β) (by linarith) hE
  have hterm := fun ℓ => rvr_term hβ0 hβ1 hQ hr hψγ hz ℓ
  have hsum : Summable fun ℓ : ℕ => if z / β ^ (2 * (ℓ + 1)) < Q
        then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0 :=
    Summable.of_nonneg_of_le (fun ℓ => (hterm ℓ).1) (fun ℓ => (hterm ℓ).2) hgs
  refine ⟨hsum, fun ℓ => (hterm ℓ).1, ?_⟩
  unfold rvT
  exact (Summable.tsum_le_tsum (fun ℓ => (hterm ℓ).2) hsum hgs).trans hgt

private lemma rvr_T_nonneg {β γ Q ψ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : 0 < Q)
    (hr : Muon.DetEquiv.rW (Muon.emaW β) Q = ψ) (hψγ : ψ < γ) {z : ℝ} (hz : 0 < z) :
    0 ≤ rvT β γ Q z := by
  unfold rvT
  exact tsum_nonneg (rvr_T_upper hβ0 hβ1 hQ hr hψγ hz).2.1

/-- Lower bound: `T(z) ≥ A X − X²/2 − 3A/2` with `X = ψ − r(z) > 0`, `A = γ − r(z)`. -/
private lemma rvr_T_lower {β γ Q ψ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : 0 < Q)
    (hr : Muon.DetEquiv.rW (Muon.emaW β) Q = ψ) (hψγ : ψ < γ) {z : ℝ} (hz : 0 < z)
    (hX : 0 < ψ - Muon.DetEquiv.rW (Muon.emaW β) z) :
    (ψ - Muon.DetEquiv.rW (Muon.emaW β) z) * isoResid β γ z
      - (ψ - Muon.DetEquiv.rW (Muon.emaW β) z) ^ 2 / 2 - 3 * isoResid β γ z / 2
      ≤ rvT β γ Q z := by
  obtain ⟨hsum, hnn, -⟩ := rvr_T_upper hβ0 hβ1 hQ hr hψγ hz
  set X := ψ - Muon.DetEquiv.rW (Muon.emaW β) z with hXdef
  set A := isoResid β γ z with hA
  have hXA : X ≤ A := by rw [hXdef, hA]; unfold isoResid; linarith
  obtain ⟨n, hn, hnM, hnL⟩ := rvr_n X
  obtain ⟨h1, h2⟩ := hnL hX
  have hle := Summable.sum_le_tsum (Finset.range n) (fun ℓ _ => hnn ℓ) hsum
  have hge : ∑ ℓ ∈ Finset.range n, (A - ((ℓ : ℝ) + 1)) ≤
      ∑ ℓ ∈ Finset.range n, (if z / β ^ (2 * (ℓ + 1)) < Q
        then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0) := by
    apply Finset.sum_le_sum
    intro ℓ hℓ
    have hℓn := Finset.mem_range.1 hℓ
    have hk : (ℓ : ℝ) + 1 < X := (hn ℓ).2 hℓn
    have hzk : 0 < z / β ^ (2 * (ℓ + 1)) := div_pos hz (pow_pos hβ0 _)
    have hsh := (lem_app_iso_shifts_i hβ0 hβ1 z hz (ℓ + 1)).2.2
    push_cast at hsh
    have hrk : Muon.DetEquiv.rW (Muon.emaW β) (z / β ^ (2 * (ℓ + 1))) < ψ := by
      rw [hXdef] at hk; linarith
    rw [if_pos ((rvr_lt_iff hβ0 hβ1 hQ hr hzk).2 hrk)]
    have he0 := rvr_eslope_nonneg hβ0 hβ1 hzk
    unfold isoWeightJ isoResid
    rw [hA]; unfold isoResid
    linarith
  have hsr := rvr_sumrange A n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmain : X * A - X ^ 2 / 2 - 3 * A / 2 ≤ n * A - n * (n + 1) / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 (h1.le.trans hXA)) (show (0:ℝ) ≤ 3 / 2 - (X - n) by linarith),
      mul_nonneg hn0 (show (0:ℝ) ≤ 1 - (X - n) by linarith), mul_nonneg (sub_nonneg.2 h1.le) (add_nonneg hX.le hn0)]
  unfold rvT
  linarith [hsr.symm ▸ hge, hle]

private lemma rvr_E1_le (e u cp τ n : ℝ) (he : 0 ≤ e) (hu : 0 ≤ u) (hcp : 0 ≤ cp) (hτ : 0 ≤ τ)
    (hn : 0 ≤ n) :
    e * τ * (1 + e * τ * u) + (1 + e * τ * u) * (e * τ + cp + n) + (e * τ + cp + n) ^ 2 * u / 2
        + 2 * e * (1 + e * τ * u) + 2 * e * (e * τ + cp + n) * u ≤
      (3 * e + 3 * e ^ 2 * u + (e + cp + 1) * (1 + 3 * e * u) + 3 * (e ^ 2 + cp ^ 2 + 1) * u / 2)
        * (1 + τ ^ 2 + n ^ 2) := by
  set R := 1 + τ ^ 2 + n ^ 2 with hR
  have hτR : τ ≤ R := by nlinarith [sq_nonneg (τ - 1), sq_nonneg n]
  have hnR : n ≤ R := by nlinarith [sq_nonneg (n - 1), sq_nonneg τ]
  have h1R : 1 ≤ R := by nlinarith [sq_nonneg τ, sq_nonneg n]
  have hτ2R : τ ^ 2 ≤ R := by nlinarith [sq_nonneg n]
  have hn2R : n ^ 2 ≤ R := by nlinarith [sq_nonneg τ]
  have hτnR : τ * n ≤ R := by nlinarith [sq_nonneg (τ - n), sq_nonneg τ, sq_nonneg n]
  have hY : e * τ + cp + n ≤ (e + cp + 1) * R := by
    nlinarith [mul_le_mul_of_nonneg_left hτR he, mul_le_mul_of_nonneg_left h1R hcp]
  have hY2 : (e * τ + cp + n) ^ 2 ≤ 3 * (e ^ 2 + cp ^ 2 + 1) * R := by
    have h3 : (e * τ + cp + n) ^ 2 ≤ 3 * ((e * τ) ^ 2 + cp ^ 2 + n ^ 2) := by
      nlinarith [sq_nonneg (e * τ - cp), sq_nonneg (cp - n), sq_nonneg (e * τ - n)]
    have h4 : (e * τ) ^ 2 ≤ e ^ 2 * R := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hτ2R (sq_nonneg e)
    have h5 : cp ^ 2 ≤ cp ^ 2 * R := le_mul_of_one_le_right (sq_nonneg cp) h1R
    nlinarith
  have hτY : τ * (e * τ + cp + n) ≤ (e + cp + 1) * R := by
    nlinarith [mul_le_mul_of_nonneg_left hτ2R he, mul_le_mul_of_nonneg_left hτR hcp]
  have heu : 0 ≤ e * u := mul_nonneg he hu
  have b1 : e * τ ≤ e * R := mul_le_mul_of_nonneg_left hτR he
  have b2 : e ^ 2 * τ ^ 2 * u ≤ e ^ 2 * u * R := by
    have := mul_le_mul_of_nonneg_left hτ2R (mul_nonneg (sq_nonneg e) hu)
    nlinarith
  have b4 : e * τ * (e * τ + cp + n) * u ≤ e * u * ((e + cp + 1) * R) := by
    have := mul_le_mul_of_nonneg_left hτY heu
    nlinarith
  have b5 : (e * τ + cp + n) ^ 2 * u ≤ 3 * (e ^ 2 + cp ^ 2 + 1) * R * u :=
    mul_le_mul_of_nonneg_right hY2 hu
  have b6 : 2 * e ≤ 2 * e * R := le_mul_of_one_le_right (by positivity) h1R
  have b7 : 2 * e ^ 2 * τ * u ≤ 2 * e ^ 2 * u * R := by
    have := mul_le_mul_of_nonneg_left hτR (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * e ^ 2) hu)
    nlinarith
  have b8 : 2 * e * (e * τ + cp + n) * u ≤ 2 * e * u * ((e + cp + 1) * R) := by
    have := mul_le_mul_of_nonneg_left hY (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * e) hu)
    nlinarith
  nlinarith

private lemma rvr_K8_cases (e u cp τ n E1 : ℝ) (he : 0 ≤ e) (hu : 0 ≤ u) (hcp : 0 ≤ cp)
    (hτ : 0 ≤ τ) (hn : 0 ≤ n) (hE1 : 0 ≤ E1)
    (hE : E1 ≤ (3 * e + 3 * e ^ 2 * u + (e + cp + 1) * (1 + 3 * e * u)
      + 3 * (e ^ 2 + cp ^ 2 + 1) * u / 2) * (1 + τ ^ 2 + n ^ 2)) :
    (6 * e * (1 + e * τ * u) + 4 * E1 ≤
      (6 * e + 6 * e ^ 2 * u + 4 * (3 * e + 3 * e ^ 2 * u + (e + cp + 1) * (1 + 3 * e * u)
        + 3 * (e ^ 2 + cp ^ 2 + 1) * u / 2)
        + 8 * e * u * (3 * e + (3 * e + 3 * e ^ 2 * u + (e + cp + 1) * (1 + 3 * e * u)
        + 3 * (e ^ 2 + cp ^ 2 + 1) * u / 2))) * (1 + τ ^ 2 + n ^ 2)) ∧
    (8 * e * u * (2 * e + e * τ + E1) ≤
      (6 * e + 6 * e ^ 2 * u + 4 * (3 * e + 3 * e ^ 2 * u + (e + cp + 1) * (1 + 3 * e * u)
        + 3 * (e ^ 2 + cp ^ 2 + 1) * u / 2)
        + 8 * e * u * (3 * e + (3 * e + 3 * e ^ 2 * u + (e + cp + 1) * (1 + 3 * e * u)
        + 3 * (e ^ 2 + cp ^ 2 + 1) * u / 2))) * (1 + τ ^ 2 + n ^ 2)) := by
  set R := 1 + τ ^ 2 + n ^ 2 with hR
  set K7 := 3 * e + 3 * e ^ 2 * u + (e + cp + 1) * (1 + 3 * e * u)
      + 3 * (e ^ 2 + cp ^ 2 + 1) * u / 2 with hK7
  have hτR : τ ≤ R := by nlinarith [sq_nonneg (τ - 1), sq_nonneg n]
  have h1R : 1 ≤ R := by nlinarith [sq_nonneg τ, sq_nonneg n]
  have hK70 : 0 ≤ K7 := by
    rw [hK7]; positivity
  have heu : 0 ≤ e * u := mul_nonneg he hu
  have hR0 : 0 ≤ R := by linarith
  have c1 : 6 * e * (1 + e * τ * u) ≤ (6 * e + 6 * e ^ 2 * u) * R := by
    have := mul_le_mul_of_nonneg_left hτR (mul_nonneg (by positivity : (0:ℝ) ≤ 6 * e ^ 2) hu)
    nlinarith [mul_le_mul_of_nonneg_left h1R (by positivity : (0:ℝ) ≤ 6 * e)]
  have c2 : 0 ≤ 8 * e * u * (3 * e + K7) * R := by positivity
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hE (by norm_num : (0:ℝ) ≤ 4)]
  · have h3 : 2 * e + e * τ ≤ 3 * e * R := by
      nlinarith [mul_le_mul_of_nonneg_left hτR he, mul_le_mul_of_nonneg_left h1R he]
    have h4 : 2 * e + e * τ + E1 ≤ (3 * e + K7) * R := by nlinarith
    have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 8 * e * u)
    have h6 : 0 ≤ (6 * e + 6 * e ^ 2 * u + 4 * K7) * R := by positivity
    nlinarith


private lemma rvr_ratio_up (a e u H E1 S ρ τ : ℝ) (ha0 : 0 < a) (he0 : 0 ≤ e) (hu0 : 0 ≤ u)
    (hH0 : 0 ≤ H) (hE10 : 0 ≤ E1) (hρ0 : 0 ≤ ρ) (hτ : 0 ≤ τ) (hHρ : H ≤ a * ρ)
    (hau : 1 ≤ a * u) (hS1 : 6 * e * ρ + 4 * E1 ≤ S)
    (hS2 : 8 * e * u * (2 * e + e * τ + E1) ≤ S) (hHa : a < 2 * e → H ≤ 2 * e + e * τ) :
    (a + 2 * e) * (H + E1) ≤ (H + S) * max (a - e) (a / 2) := by
  have hS0 : 0 ≤ S := by
    have : 0 ≤ 6 * e * ρ := by positivity
    linarith
  rcases le_or_gt (2 * e) a with hc | hc
  · have hm : a - e ≤ max (a - e) (a / 2) := le_max_left _ _
    have h1 : (H + S) * (a - e) ≤ (H + S) * max (a - e) (a / 2) :=
      mul_le_mul_of_nonneg_left hm (by linarith)
    have h2 : (6 * e * ρ + 4 * E1) * (a / 2) ≤ (6 * e * ρ + 4 * E1) * (a - e) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : (6 * e * ρ + 4 * E1) * (a - e) ≤ S * (a - e) :=
      mul_le_mul_of_nonneg_right hS1 (by linarith)
    have h4 : 3 * e * H ≤ 3 * e * (a * ρ) := mul_le_mul_of_nonneg_left hHρ (by positivity)
    have h5 : 2 * e * E1 ≤ a * E1 := mul_le_mul_of_nonneg_right hc hE10
    nlinarith
  · have hm2 : a / 2 ≤ max (a - e) (a / 2) := le_max_right _ _
    have hHa' := hHa hc
    have h1 : a + 2 * e ≤ 4 * e * (a * u) := by nlinarith
    have h2 : (a + 2 * e) * (H + E1) ≤ 4 * e * (a * u) * (H + E1) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : 8 * e * u * H ≤ 8 * e * u * (2 * e + e * τ) :=
      mul_le_mul_of_nonneg_left hHa' (by positivity)
    have h4 : (H + S) * (a / 2) ≤ (H + S) * max (a - e) (a / 2) :=
      mul_le_mul_of_nonneg_left hm2 (by linarith)
    have h6 : 8 * e * u * (H + E1) ≤ H + S := by nlinarith
    have h5 : 4 * e * (a * u) * (H + E1) ≤ (H + S) * (a / 2) := by
      have := mul_le_mul_of_nonneg_left h6 (by linarith : 0 ≤ a / 2)
      nlinarith
    linarith

private lemma rvr_alg_up (e Φ u a X g τ n cp Jy Tz d : ℝ) (he : 1 ≤ e) (hΦ : 0 < Φ)
    (hu : Φ * u = 1) (haΦ : Φ ≤ a) (hτ : 0 ≤ τ) (hn : 0 ≤ n) (hcp : 0 ≤ cp) (hX : 0 < X)
    (hg : 0 < g) (hxa : X + g ≤ a + e * τ) (hJ0 : 0 ≤ Jy) (hJ : Jy ≤ a + 2 * e) (hT0 : 0 ≤ Tz)
    (hT : Tz ≤ (X + (e * τ + cp + n)) ^ 2 / 2 + (g + 2 * e) * (X + (e * τ + cp + n)))
    (hd : a * max (a - e) (a / 2) ≤ d) :
    Jy * Tz / d ≤ (X - X ^ 2 / (2 * (X + g))) +
      (6 * e + 6 * e ^ 2 * u + 4 * (3 * e + 3 * e ^ 2 * u + (e + cp + 1) * (1 + 3 * e * u)
        + 3 * (e ^ 2 + cp ^ 2 + 1) * u / 2)
        + 8 * e * u * (3 * e + (3 * e + 3 * e ^ 2 * u + (e + cp + 1) * (1 + 3 * e * u)
        + 3 * (e ^ 2 + cp ^ 2 + 1) * u / 2))) * (1 + τ ^ 2 + n ^ 2) := by
  have he0 : 0 ≤ e := by linarith
  have hu0 : 0 ≤ u := by
    by_contra h; push_neg at h
    nlinarith
  have ha0 : 0 < a := hΦ.trans_le haΦ
  have hau : 1 ≤ a * u := by nlinarith
  set x := X + g with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  set Y := e * τ + cp + n with hY
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  set H := X - X ^ 2 / (2 * x) with hH
  have hHX : H ≤ X := by
    have : 0 ≤ X ^ 2 / (2 * x) := by positivity
    rw [hH]; linarith
  have hHx : H ≤ x := by rw [hx]; linarith
  have hH0 : 0 ≤ H := by
    rw [hH, sub_nonneg, div_le_iff₀ (by positivity)]
    nlinarith
  have hxH : x * H = x * X - X ^ 2 / 2 := by
    rw [hH]; field_simp
  set ρ := 1 + e * τ * u with hρ
  have hρ0 : 1 ≤ ρ := by rw [hρ]; have := mul_nonneg (mul_nonneg he0 hτ) hu0; linarith
  have hxρ : x ≤ a * ρ := by
    have : e * τ ≤ e * τ * (a * u) := le_mul_of_one_le_right (mul_nonneg he0 hτ) hau
    rw [hρ]; nlinarith
  set E1 := e * τ * ρ + ρ * Y + Y ^ 2 * u / 2 + 2 * e * ρ + 2 * e * Y * u with hE1
  have hE10 : 0 ≤ E1 := by rw [hE1]; positivity
  -- Step: T ≤ a (H + E1)
  have hTa : Tz ≤ a * (H + E1) := by
    have hid : (X + Y) ^ 2 / 2 + g * (X + Y) = x * H + Y * x + Y ^ 2 / 2 := by
      rw [hxH, hx]; ring
    have s1 : x * H ≤ a * H + e * τ * (a * ρ) := by
      have h1 : (x - a) * H ≤ e * τ * H := mul_le_mul_of_nonneg_right (by linarith) hH0
      have h2 : e * τ * H ≤ e * τ * (a * ρ) :=
        mul_le_mul_of_nonneg_left (hHx.trans hxρ) (mul_nonneg he0 hτ)
      nlinarith
    have s2 : Y * x ≤ Y * (a * ρ) := mul_le_mul_of_nonneg_left hxρ hY0
    have s3 : Y ^ 2 / 2 ≤ a * (Y ^ 2 * u / 2) := by
      have : Y ^ 2 ≤ Y ^ 2 * (a * u) := le_mul_of_one_le_right (sq_nonneg Y) hau
      have e1 : a * (Y ^ 2 * u / 2) = Y ^ 2 * (a * u) / 2 := by ring
      linarith
    have s4 : 2 * e * (X + Y) ≤ a * (2 * e * ρ) + a * (2 * e * Y * u) := by
      have h1 : 2 * e * X ≤ 2 * e * (a * ρ) :=
        mul_le_mul_of_nonneg_left ((by linarith : X ≤ x).trans hxρ) (by positivity)
      have h2 : 2 * e * Y ≤ 2 * e * Y * (a * u) := le_mul_of_one_le_right (by positivity) hau
      have e1 : a * (2 * e * ρ) = 2 * e * (a * ρ) := by ring
      have e2 : a * (2 * e * Y * u) = 2 * e * Y * (a * u) := by ring
      linarith
    have : (X + Y) ^ 2 / 2 + (g + 2 * e) * (X + Y) ≤ a * (H + E1) := by
      rw [hE1]
      linarith [hid, s1, s2, s3, s4]
    exact hT.trans this
  have hd0 : 0 < a * max (a - e) (a / 2) :=
    mul_pos ha0 (lt_of_lt_of_le (by linarith) (le_max_right _ _))
  have hdpos : 0 < d := lt_of_lt_of_le hd0 hd
  obtain ⟨hK1, hK2⟩ := rvr_K8_cases e u cp τ n E1 he0 hu0 hcp hτ hn hE10
    (rvr_E1_le e u cp τ n he0 hu0 hcp hτ hn)
  set K8 := (6 * e + 6 * e ^ 2 * u + 4 * (3 * e + 3 * e ^ 2 * u + (e + cp + 1) * (1 + 3 * e * u)
        + 3 * (e ^ 2 + cp ^ 2 + 1) * u / 2)
        + 8 * e * u * (3 * e + (3 * e + 3 * e ^ 2 * u + (e + cp + 1) * (1 + 3 * e * u)
        + 3 * (e ^ 2 + cp ^ 2 + 1) * u / 2))) with hK8
  set S := K8 * (1 + τ ^ 2 + n ^ 2) with hS
  have hS0 : 0 ≤ S := by
    have : 0 ≤ 4 * E1 := by positivity
    have h1 : 0 ≤ 6 * e * (1 + e * τ * u) := by positivity
    linarith
  rw [div_le_iff₀ hdpos]
  have hJT : Jy * Tz ≤ (a + 2 * e) * (a * (H + E1)) :=
    mul_le_mul hJ hTa hT0 (by linarith)
  have hmain : (a + 2 * e) * (H + E1) ≤ (H + S) * max (a - e) (a / 2) := by
    refine rvr_ratio_up a e u H E1 S ρ τ ha0 he0 hu0 hH0 hE10 (by linarith) hτ (hHx.trans hxρ) hau ?_ ?_ ?_
    · rw [hρ]; linarith [hK1]
    · exact hK2
    · intro hc
      linarith
  calc Jy * Tz ≤ (a + 2 * e) * (a * (H + E1)) := hJT
    _ = a * ((a + 2 * e) * (H + E1)) := by ring
    _ ≤ a * ((H + S) * max (a - e) (a / 2)) := mul_le_mul_of_nonneg_left hmain ha0.le
    _ = (H + S) * (a * max (a - e) (a / 2)) := by ring
    _ ≤ (H + S) * d := mul_le_mul_of_nonneg_left hd (by linarith)

private lemma rvr_f_mono (X' Xz a' Az : ℝ) (hX' : 0 < X') (hXz : X' ≤ Xz) (hXA : Xz ≤ Az)
    (ha' : 0 < a') (haA : a' ≤ Az) (hX'a : X' ≤ a') :
    X' - X' ^ 2 / (2 * a') ≤ Xz - Xz ^ 2 / (2 * Az) := by
  have hAz : 0 < Az := ha'.trans_le haA
  have h1 : X' ^ 2 / (2 * Az) ≤ X' ^ 2 / (2 * a') :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  have h2 : Xz ^ 2 / (2 * Az) - X' ^ 2 / (2 * Az) ≤ Xz - X' := by
    rw [← sub_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hXz) (sub_nonneg.2 hXA), mul_nonneg (sub_nonneg.2 hXz) hX'.le]
  linarith

private lemma rvr_f0 (X x υ : ℝ) (hυ : 0 ≤ υ) (hXυ : υ < X) (hXx : X ≤ x) :
    X - X ^ 2 / (2 * x) - 2 * υ ≤ (X - υ) - (X - υ) ^ 2 / (2 * (x - υ)) := by
  have hx : 0 < x := by linarith
  have hxυ : 0 < x - υ := by linarith
  have key : (X - υ) ^ 2 / (2 * (x - υ)) ≤ X ^ 2 / (2 * x) + υ / 2 := by
    rw [div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hυ (mul_nonneg (sub_nonneg.2 hXx) (by linarith : (0:ℝ) ≤ x + X)),
      mul_nonneg hυ (mul_nonneg hx.le (by linarith : (0:ℝ) ≤ X - υ)), mul_pos hx hxυ]
  linarith

private lemma rvr_ratio_lb (x υ : ℝ) (hυ : 0 ≤ υ) (hx : 0 < x) :
    1 - 4 * υ / x ≤ (x - υ) ^ 2 / (x + υ) ^ 2 := by
  rw [one_sub_div hx.ne', div_le_div_iff₀ hx (by positivity)]
  nlinarith [mul_nonneg hx.le (sq_nonneg υ), pow_nonneg hυ 3, mul_nonneg hυ (sq_nonneg υ)]

private lemma rvr_alg_low (υ x X Ay Az Avp Xz Jy Tz d : ℝ) (hυ : 0 ≤ υ) (hXυ : υ < X)
    (hXx : X ≤ x) (hAy : x - υ ≤ Ay) (hAz : x - υ ≤ Az) (hAvy : Ay ≤ Avp) (hAvz : Az ≤ Avp)
    (hAvp : Avp ≤ x + υ) (hXz1 : X - υ ≤ Xz) (hXz2 : Xz ≤ Az)
    (hT : Xz * Az - Xz ^ 2 / 2 - 3 * Az / 2 ≤ Tz) (hT0 : 0 ≤ Tz) (hJ : Ay ≤ Jy)
    (hd0 : 0 < d) (hd : d ≤ Avp ^ 2) :
    X - X ^ 2 / (2 * x) - 6 * υ - 3 / 2 ≤ Jy * Tz / d := by
  have hx : 0 < x := by linarith
  have ha' : 0 < x - υ := by linarith
  have hAy0 : 0 < Ay := by linarith
  have hAz0 : 0 < Az := by linarith
  have hAvp0 : 0 < Avp := by linarith
  set r0 := Ay * Az / Avp ^ 2 with hr0
  set f := Xz - Xz ^ 2 / (2 * Az) with hf
  have hr00 : 0 ≤ r0 := by positivity
  have hr01 : r0 ≤ 1 := by
    rw [hr0, div_le_one (by positivity)]
    nlinarith [mul_le_mul hAvy hAvz hAz0.le hAvp0.le]
  -- Step 1
  have hstep1 : r0 * (f - 3 / 2) ≤ Jy * Tz / d := by
    have hJT : Ay * Tz ≤ Jy * Tz := mul_le_mul_of_nonneg_right hJ hT0
    have hnn : 0 ≤ Jy * Tz / d := div_nonneg (mul_nonneg (hAy0.le.trans hJ) hT0) hd0.le
    rcases le_or_gt (3 / 2) f with hc | hc
    · have hLw : Az * (f - 3 / 2) ≤ Tz := by
        have : Az * (f - 3 / 2) = Xz * Az - Xz ^ 2 / 2 - 3 * Az / 2 := by
          rw [hf]; field_simp
        linarith
      have hLw0 : 0 ≤ Az * (f - 3 / 2) := mul_nonneg hAz0.le (by linarith)
      have h1 : Ay * (Az * (f - 3 / 2)) ≤ Ay * Tz := mul_le_mul_of_nonneg_left hLw hAy0.le
      have h2 : r0 * (f - 3 / 2) = Ay * (Az * (f - 3 / 2)) / Avp ^ 2 := by
        rw [hr0]; ring
      rw [h2]
      calc Ay * (Az * (f - 3 / 2)) / Avp ^ 2 ≤ Ay * (Az * (f - 3 / 2)) / d :=
            div_le_div_of_nonneg_left (by positivity) hd0 hd
        _ ≤ Ay * Tz / d := div_le_div_of_nonneg_right h1 hd0.le
        _ ≤ Jy * Tz / d := div_le_div_of_nonneg_right hJT hd0.le
    · have : r0 * (f - 3 / 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr00 (by linarith)
      linarith
  -- Step 2/3
  have hf0 : X - υ - (X - υ) ^ 2 / (2 * (x - υ)) ≤ f :=
    rvr_f_mono (X - υ) Xz (x - υ) Az (by linarith) hXz1 hXz2 ha' hAz (by linarith)
  have hfH := rvr_f0 X x υ hυ hXυ hXx
  have hf00 : 0 ≤ X - υ - (X - υ) ^ 2 / (2 * (x - υ)) := by
    have : (X - υ) ^ 2 / (2 * (x - υ)) ≤ X - υ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.2 hXx) (by linarith : (0:ℝ) ≤ X - υ)]
    linarith
  have hr0lb : (x - υ) ^ 2 / (x + υ) ^ 2 ≤ r0 := by
    rw [hr0]
    have h1 : (x - υ) ^ 2 ≤ Ay * Az := by
      nlinarith [mul_le_mul hAy hAz ha'.le hAy0.le]
    calc (x - υ) ^ 2 / (x + υ) ^ 2 ≤ Ay * Az / (x + υ) ^ 2 :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ Ay * Az / Avp ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_left₀ hAvp0.le hAvp 2)
  have hrat := rvr_ratio_lb x υ hυ hx
  set H := X - X ^ 2 / (2 * x) with hH
  have hHx : H ≤ x := by
    have : 0 ≤ X ^ 2 / (2 * x) := by positivity
    have : X ≤ x := hXx
    rw [hH]; linarith
  have hrf : H - 6 * υ ≤ r0 * f := by
    by_cases hc : 4 * υ ≤ x ∧ 2 * υ ≤ H
    · obtain ⟨hc1, hc2⟩ := hc
      have hq : 0 ≤ 1 - 4 * υ / x := by
        rw [sub_nonneg, div_le_one hx]; exact hc1
      have h1 : 1 - 4 * υ / x ≤ r0 := hrat.trans hr0lb
      have h2 : H - 2 * υ ≤ f := by linarith
      have h3 : (1 - 4 * υ / x) * (H - 2 * υ) ≤ r0 * f :=
        mul_le_mul h1 h2 (by linarith) hr00
      have h4 : 4 * υ / x * (H - 2 * υ) ≤ 4 * υ := by
        have : 4 * υ / x * (H - 2 * υ) ≤ 4 * υ / x * x :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        rw [div_mul_cancel₀ _ hx.ne'] at this
        exact this
      nlinarith
    · have hlt : H - 6 * υ < 0 := by
        rw [not_and_or] at hc
        rcases hc with h | h
        · push_neg at h; linarith
        · push_neg at h; linarith
      have : 0 ≤ r0 * f := mul_nonneg hr00 (hf00.trans hf0)
      linarith
  nlinarith [mul_le_mul_of_nonneg_right hr01 (by linarith : (0:ℝ) ≤ 3 / 2)]

/-- `𝖧(η) = f_x(X)` with `X = ψ − η`, `x = γ − η`. -/
private def rvH (γ ψ η : ℝ) : ℝ := (ψ - η) - (ψ - η) ^ 2 / (2 * (γ - η))

/-- `Ψ(y,z) = 1{y<Q, z_1<Q} 𝗃(y) T(z)/(γ² Δ̂(y,z))`. -/
private def rvPsi (β γ Q : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < Q ∧ p.2 / β ^ (2 * 1) < Q then
    isoWeightJ β γ p.1 * rvT β γ Q p.2 / (γ ^ 2 * isoDeltaHat β γ p.1 p.2) else 0

private lemma rvr_consts {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    1 ≤ isoEbar β ∧ 0 < isoPhi 1 ∧ 0 ≤ isoCpl β := by
  have hΦ : 0 < isoPhi 1 := (lem_app_iso_gaussian_ii.2.2 1 one_pos).1
  have h1 : 0 < 1 - β := by linarith
  have h2 : 0 < 1 - β ^ 2 := by nlinarith
  have hc : 0 ≤ isoC β := by unfold isoC; positivity
  have hc' : 0 ≤ isoC' β := by unfold isoC'; positivity
  exact ⟨le_max_left _ _, hΦ, by unfold isoCpl; linarith⟩

private lemma rvr_K8_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 ≤ isoK8 β := by
  obtain ⟨he, hΦ, hcp⟩ := rvr_consts hβ0 hβ1
  have he0 : 0 ≤ isoEbar β := by linarith
  unfold isoK8 isoK7
  positivity

private lemma rvr_K8_eq {β : ℝ} :
    isoK8 β = 6 * isoEbar β + 6 * isoEbar β ^ 2 * (1 / isoPhi 1)
      + 4 * (3 * isoEbar β + 3 * isoEbar β ^ 2 * (1 / isoPhi 1)
        + (isoEbar β + isoCpl β + 1) * (1 + 3 * isoEbar β * (1 / isoPhi 1))
        + 3 * (isoEbar β ^ 2 + isoCpl β ^ 2 + 1) * (1 / isoPhi 1) / 2)
      + 8 * isoEbar β * (1 / isoPhi 1) * (3 * isoEbar β + (3 * isoEbar β
        + 3 * isoEbar β ^ 2 * (1 / isoPhi 1)
        + (isoEbar β + isoCpl β + 1) * (1 + 3 * isoEbar β * (1 / isoPhi 1))
        + 3 * (isoEbar β ^ 2 + isoCpl β ^ 2 + 1) * (1 / isoPhi 1) / 2)) := by
  unfold isoK8 isoK7
  ring

private lemma rvr_H_nonneg {γ ψ η : ℝ} (hη : 0 < η) (hηψ : η < ψ) (hψγ : ψ < γ) :
    0 ≤ rvH γ ψ η ∧ rvH γ ψ η ≤ ψ - η := by
  unfold rvH
  have hx : 0 < γ - η := by linarith
  have h1 : 0 ≤ (ψ - η) ^ 2 / (2 * (γ - η)) := by positivity
  refine ⟨?_, by linarith⟩
  rw [sub_nonneg, div_le_iff₀ (by positivity)]
  nlinarith

private lemma rvr_region {β γ Q ψ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hQ : 0 < Q) (hr : Muon.DetEquiv.rW (Muon.emaW β) Q = ψ) (hψγ : ψ < γ)
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z) (hyQ : y < Q) (hzQ : z / β ^ (2 * 1) < Q) :
    0 < isoResid β γ y ∧ isoPhi 1 < isoResid β γ z ∧ 0 < isoDeltaHat β γ y z ∧
      Muon.DetEquiv.rW (Muon.emaW β) y < ψ := by
  have hγ0 := rvr_gamma_pos hβ0 hβ1 hγ
  have hz1 : 0 < z / β ^ (2 * 1) := by positivity
  have hry := (rvr_lt_iff hβ0 hβ1 hQ hr hy).1 hyQ
  have hrz := (rvr_lt_iff hβ0 hβ1 hQ hr hz1).1 hzQ
  have hAy : 0 < isoResid β γ y := by unfold isoResid; linarith
  have hAz : isoPhi 1 < isoResid β γ z :=
    lem_app_iso_shifts_v hβ0 hβ1 γ z hz hγ (by simpa using hrz.trans hψγ)
  have hΦ : 0 < isoPhi 1 := (lem_app_iso_gaussian_ii.2.2 1 one_pos).1
  refine ⟨hAy, hAz, ?_, hry⟩
  obtain ⟨-, -, hm, hd, -⟩ := lem_app_iso_kernel_bounds_v hβ0 hβ1 hγ0 hy hz hAy (hΦ.trans hAz)
  have hAv : 0 < isoAvee β γ y z := lt_of_lt_of_le hAy (le_max_left _ _)
  have : 0 < γ ^ 2 * isoDeltaHat β γ y z := lt_of_lt_of_le (mul_pos hAv hm) hd
  exact pos_of_mul_pos_right this (by positivity) |> fun h => by
    by_contra hc; push_neg at hc; nlinarith [sq_nonneg γ]

private lemma rvr_J_bounds {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {y : ℝ} (hy : 0 < y) :
    isoResid β γ y ≤ isoWeightJ β γ y ∧ isoWeightJ β γ y ≤ isoResid β γ y + 2 * isoEbar β := by
  have h0 := rvr_eslope_nonneg hβ0 hβ1 hy
  have h1 := ((lem_app_iso_slope hβ0 hβ1 y hy).1.trans (lem_app_iso_slope hβ0 hβ1 y hy).2)
  unfold isoWeightJ
  constructor <;> linarith

private lemma rvr_Psi_nonneg {β γ Q ψ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hQ : 0 < Q) (hr : Muon.DetEquiv.rW (Muon.emaW β) Q = ψ) (hψγ : ψ < γ)
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z) : 0 ≤ rvPsi β γ Q (y, z) := by
  have hγ0 := rvr_gamma_pos hβ0 hβ1 hγ
  unfold rvPsi
  split_ifs with h
  · obtain ⟨hA, -, hΔ, -⟩ := rvr_region hβ0 hβ1 hγ hQ hr hψγ hy hz h.1 h.2
    have hJ := (rvr_J_bounds (γ := γ) hβ0 hβ1 hy).1
    exact div_nonneg (mul_nonneg (hA.le.trans hJ) (rvr_T_nonneg hβ0 hβ1 hQ hr hψγ hz))
      (by positivity)
  · exact le_rfl

private lemma rvr_core_up {β γ Q ψ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hQ : 0 < Q) (hr : Muon.DetEquiv.rW (Muon.emaW β) Q = ψ) (hψγ : ψ < γ)
    {η y z τ : ℝ} (hη : 0 < η) (hηψ : η < ψ) (hy : 0 < y) (hz : 0 < z) (hτ : 0 ≤ τ)
    (hyA : |isoResid β γ y - (γ - η)| ≤ isoEbar β * τ)
    (hzA : |isoResid β γ z - (γ - η)| ≤ isoEbar β * τ) :
    rvPsi β γ Q (y, z) ≤ rvH γ ψ η + isoK8 β * (1 + τ ^ 2 + (max 0 (-isoN β z)) ^ 2) := by
  have hγ0 := rvr_gamma_pos hβ0 hβ1 hγ
  obtain ⟨he, hΦ, hcp⟩ := rvr_consts hβ0 hβ1
  obtain ⟨hH0, -⟩ := rvr_H_nonneg hη hηψ hψγ
  have hK8 := rvr_K8_nonneg hβ0 hβ1
  have hR0 : 0 ≤ 1 + τ ^ 2 + (max 0 (-isoN β z)) ^ 2 := by positivity
  by_cases hreg : y < Q ∧ z / β ^ (2 * 1) < Q
  · obtain ⟨hAy, hAz, hΔ, -⟩ := rvr_region hβ0 hβ1 hγ hQ hr hψγ hy hz hreg.1 hreg.2
    have hAz0 : 0 < isoResid β γ z := hΦ.trans hAz
    obtain ⟨-, -, -, hd, -⟩ := lem_app_iso_kernel_bounds_v hβ0 hβ1 hγ0 hy hz hAy hAz0
    obtain ⟨hJ1, hJ2⟩ := rvr_J_bounds (γ := γ) hβ0 hβ1 hy
    have hAv_y : isoResid β γ y ≤ isoAvee β γ y z := le_max_left _ _
    have hAv_z : isoResid β γ z ≤ isoAvee β γ y z := le_max_right _ _
    obtain ⟨-, -, hT⟩ := rvr_T_upper hβ0 hβ1 hQ hr hψγ hz
    have hT0 := rvr_T_nonneg hβ0 hβ1 hQ hr hψγ hz
    set n := max 0 (-isoN β z) with hn
    have hn0 : 0 ≤ n := le_max_left _ _
    set e := isoEbar β with he_def
    have hs3 := lem_app_iso_shifts_iii hβ0 hβ1 z hz
    have hrz : η - e * τ ≤ Muon.DetEquiv.rW (Muon.emaW β) z := by
      have := (abs_le.mp hzA).2
      unfold isoResid at this
      linarith
    have hL : ψ - isoN β z + isoC β ≤ (ψ - η) + (e * τ + isoCpl β + n) := by
      unfold isoCpl
      linarith
    have hX : 0 < ψ - η := by linarith
    have hm : max (ψ - isoN β z + isoC β) 0 ≤ (ψ - η) + (e * τ + isoCpl β + n) := by
      refine max_le hL ?_
      have : 0 ≤ e * τ := by positivity
      linarith
    have hm0 : 0 ≤ max (ψ - isoN β z + isoC β) 0 := le_max_right _ _
    have hT' : rvT β γ Q z ≤ ((ψ - η) + (e * τ + isoCpl β + n)) ^ 2 / 2
        + ((γ - ψ) + 2 * e) * ((ψ - η) + (e * τ + isoCpl β + n)) := by
      refine hT.trans ?_
      have h1 := pow_le_pow_left₀ hm0 hm 2
      have h2 := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ (γ - ψ) + 2 * e)
      linarith
    have hxa : (ψ - η) + (γ - ψ) ≤ isoAvee β γ y z + e * τ := by
      have := (abs_le.mp hyA).1
      linarith
    have hkey := rvr_alg_up e (isoPhi 1) (1 / isoPhi 1) (isoAvee β γ y z) (ψ - η) (γ - ψ) τ n
      (isoCpl β) (isoWeightJ β γ y) (rvT β γ Q z) (γ ^ 2 * isoDeltaHat β γ y z) he hΦ
      (by field_simp) (hAz.le.trans hAv_z) hτ hn0 hcp hX (by linarith) hxa
      (hAy.le.trans hJ1) (by linarith) hT0 hT' hd
    have hid : (ψ - η) + (γ - ψ) = γ - η := by ring
    rw [hid] at hkey
    unfold rvPsi
    rw [if_pos hreg, rvr_K8_eq]
    unfold rvH
    linarith [hkey]
  · unfold rvPsi
    rw [if_neg hreg]
    have : 0 ≤ isoK8 β * (1 + τ ^ 2 + (max 0 (-isoN β z)) ^ 2) := mul_nonneg hK8 hR0
    linarith

private lemma rvr_core_low {β γ Q ψ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hQ : 0 < Q) (hr : Muon.DetEquiv.rW (Muon.emaW β) Q = ψ) (hψγ : ψ < γ)
    {η y z τ : ℝ} (hη : 0 < η) (hηψ : η < ψ) (hy : 0 < y) (hz : 0 < z) (hτ : 0 ≤ τ)
    (hyA : |isoResid β γ y - (γ - η)| ≤ isoEbar β * τ)
    (hzA : |isoResid β γ z - (γ - η)| ≤ isoEbar β * τ) :
    rvH γ ψ η - 6 * (isoEbar β * (τ + 1)) - 3 / 2 ≤ rvPsi β γ Q (y, z) := by
  have hγ0 := rvr_gamma_pos hβ0 hβ1 hγ
  obtain ⟨he, hΦ, hcp⟩ := rvr_consts hβ0 hβ1
  obtain ⟨hH0, hHX⟩ := rvr_H_nonneg hη hηψ hψγ
  have hnn := rvr_Psi_nonneg hβ0 hβ1 hγ hQ hr hψγ hy hz
  set e := isoEbar β with he_def
  have he0 : 0 ≤ e := by linarith
  set υ := e * (τ + 1) with hυ
  have hυe : e * τ + e = υ := by rw [hυ]; ring
  have heτ : 0 ≤ e * τ := mul_nonneg he0 hτ
  by_cases hX : ψ - η ≤ υ
  · linarith
  · push_neg at hX
    -- the indicator holds
    have hzr : Muon.DetEquiv.rW (Muon.emaW β) z ≤ η + e * τ := by
      have := (abs_le.mp hzA).1
      unfold isoResid at this
      linarith
    have hyr : Muon.DetEquiv.rW (Muon.emaW β) y ≤ η + e * τ := by
      have := (abs_le.mp hyA).1
      unfold isoResid at this
      linarith
    have hyQ : y < Q := by
      rw [rvr_lt_iff hβ0 hβ1 hQ hr hy]; linarith
    have hz1 : 0 < z / β ^ (2 * 1) := by positivity
    have hsh := (lem_app_iso_shifts_i hβ0 hβ1 z hz 1).2.2
    push_cast at hsh
    have hzQ : z / β ^ (2 * 1) < Q := by
      rw [rvr_lt_iff hβ0 hβ1 hQ hr hz1]; linarith
    obtain ⟨hAy, hAz, hΔ, -⟩ := rvr_region hβ0 hβ1 hγ hQ hr hψγ hy hz hyQ hzQ
    have hAz0 : 0 < isoResid β γ z := hΦ.trans hAz
    obtain ⟨-, -, -, hd, hu⟩ := lem_app_iso_kernel_bounds_v hβ0 hβ1 hγ0 hy hz hAy hAz0
    obtain ⟨hJ1, -⟩ := rvr_J_bounds (γ := γ) hβ0 hβ1 hy
    have hAv_y : isoResid β γ y ≤ isoAvee β γ y z := le_max_left _ _
    have hAv_z : isoResid β γ z ≤ isoAvee β γ y z := le_max_right _ _
    have hAvle : isoAvee β γ y z ≤ (γ - η) + e * τ := by
      unfold isoAvee
      exact max_le (by linarith [(abs_le.mp hyA).2]) (by linarith [(abs_le.mp hzA).2])
    have hXz : 0 < ψ - Muon.DetEquiv.rW (Muon.emaW β) z := by linarith
    have hTl := rvr_T_lower hβ0 hβ1 hQ hr hψγ hz hXz
    have hT0 := rvr_T_nonneg hβ0 hβ1 hQ hr hψγ hz
    have hd0 : 0 < γ ^ 2 * isoDeltaHat β γ y z := by positivity
    have hAvpos : 0 < isoAvee β γ y z := lt_of_lt_of_le hAy hAv_y
    have hlow := rvr_alg_low υ (γ - η) (ψ - η) (isoResid β γ y) (isoResid β γ z)
      (isoAvee β γ y z + e) (ψ - Muon.DetEquiv.rW (Muon.emaW β) z) (isoWeightJ β γ y)
      (rvT β γ Q z) (γ ^ 2 * isoDeltaHat β γ y z) (by positivity) hX (by linarith)
      (by linarith [(abs_le.mp hyA).1]) (by linarith [(abs_le.mp hzA).1])
      (by linarith) (by linarith) (by linarith) (by linarith) (by unfold isoResid at hAz0 ⊢; linarith)
      hTl hT0 hJ1 hd0 hu
    unfold rvPsi
    rw [if_pos ⟨hyQ, hzQ⟩]
    unfold rvH
    linarith [hlow]

/-- Private helper (task P-F.11.P2): `Z` kernel for a stand-in `R`. -/
private def rvD_Z (R : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 = p.2 then p.1 * deriv R p.1 else Real.sqrt (p.1 * p.2) * (R p.1 - R p.2) / (p.1 - p.2)

/-- Private helper (task P-F.11.P2): `X` kernel for a stand-in `R`. -/
private def rvD_X (R : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 = p.2 then R p.1 - p.1 * deriv R p.1 else (p.2 * R p.1 - p.1 * R p.2) / (p.2 - p.1)

/-- Private helper (task P-F.11.P2): `Δ̂` for a stand-in `R`. -/
private def rvD_Δ (R : ℝ → ℝ) (γ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 - rvD_X R p / γ) ^ 2 - (rvD_Z R p / γ) ^ 2

/-- Private helper (task P-F.11.P2): `j` for a stand-in `R`. -/
private def rvD_J (R : ℝ → ℝ) (γ y : ℝ) : ℝ := (γ - R y) + 2 * (y * deriv R y)

/-- Private helper (task P-F.11.P2): `T` for a stand-in `R`. -/
private def rvD_T (R : ℝ → ℝ) (β γ Q z : ℝ) : ℝ :=
  ∑' ℓ : ℕ, if z / β ^ (2 * (ℓ + 1)) < Q then rvD_J R γ (z / β ^ (2 * (ℓ + 1))) else 0

/-- Private helper (task P-F.11.P2): `Ψ` for a stand-in `R`. -/
private def rvD_Psi (R : ℝ → ℝ) (β γ Q : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < Q ∧ p.2 / β ^ (2 * 1) < Q then
    rvD_J R γ p.1 * rvD_T R β γ Q p.2 / (γ ^ 2 * rvD_Δ R γ p) else 0

private lemma rvD_Z_meas {R : ℝ → ℝ} (hR : Measurable R) : Measurable (rvD_Z R) := by
  unfold rvD_Z
  have hd := measurable_deriv R
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) ?_ ?_
  · exact measurable_fst.mul (hd.comp measurable_fst)
  · fun_prop

private lemma rvD_X_meas {R : ℝ → ℝ} (hR : Measurable R) : Measurable (rvD_X R) := by
  unfold rvD_X
  have hd := measurable_deriv R
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) ?_ ?_
  · exact (hR.comp measurable_fst).sub (measurable_fst.mul (hd.comp measurable_fst))
  · fun_prop

private lemma rvD_Δ_meas {R : ℝ → ℝ} (hR : Measurable R) (γ : ℝ) :
    Measurable (rvD_Δ R γ) := by
  unfold rvD_Δ
  have := rvD_Z_meas hR
  have := rvD_X_meas hR
  fun_prop

private lemma rvD_J_meas {R : ℝ → ℝ} (hR : Measurable R) (γ : ℝ) :
    Measurable (rvD_J R γ) := by
  unfold rvD_J
  have hd := measurable_deriv R
  fun_prop

private lemma rvD_T_meas {R : ℝ → ℝ} (hR : Measurable R) (β γ Q : ℝ) :
    Measurable (rvD_T R β γ Q) := by
  unfold rvD_T
  refine Measurable.tsum (fun ℓ => ?_)
  refine Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) ?_ measurable_const
  exact (rvD_J_meas hR γ).comp (by fun_prop)

private lemma rvD_Psi_meas {R : ℝ → ℝ} (hR : Measurable R) (β γ Q : ℝ) :
    Measurable (rvD_Psi R β γ Q) := by
  unfold rvD_Psi
  have h1 := rvD_J_meas hR γ
  have h2 := rvD_T_meas hR β γ Q
  have h3 := rvD_Δ_meas hR γ
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_lt (measurable_snd.div_const _) measurable_const)
  · exact ((h1.comp measurable_fst).mul (h2.comp measurable_snd)).div
      (measurable_const.mul h3)

private lemma rvD_deriv_eq {β : ℝ} {R : ℝ → ℝ}
    (hRe : ∀ q : ℝ, 0 ≤ q → R q = Muon.DetEquiv.rW (Muon.emaW β) q) {y : ℝ} (hy : 0 < y) :
    deriv R y = deriv (Muon.DetEquiv.rW (Muon.emaW β)) y := by
  have : R =ᶠ[nhds y] Muon.DetEquiv.rW (Muon.emaW β) := by
    filter_upwards [Ioi_mem_nhds hy] with q hq using hRe q (le_of_lt hq)
  exact this.deriv_eq

private lemma rvD_J_eq {β γ : ℝ} {R : ℝ → ℝ}
    (hRe : ∀ q : ℝ, 0 ≤ q → R q = Muon.DetEquiv.rW (Muon.emaW β) q) {y : ℝ} (hy : 0 < y) :
    rvD_J R γ y = isoWeightJ β γ y := by
  unfold rvD_J isoWeightJ isoResid isoEslope
  rw [rvD_deriv_eq hRe hy, hRe y hy.le]

private lemma rvD_Δ_eq {β γ : ℝ} {R : ℝ → ℝ}
    (hRe : ∀ q : ℝ, 0 ≤ q → R q = Muon.DetEquiv.rW (Muon.emaW β) q) {y z : ℝ} (hy : 0 < y)
    (hz : 0 < z) : rvD_Δ R γ (y, z) = isoDeltaHat β γ y z := by
  unfold rvD_Δ rvD_X rvD_Z isoDeltaHat isoXkern isoZkern isoEslope
  simp only [rvD_deriv_eq hRe hy, hRe y hy.le, hRe z hz.le]

private lemma rvD_T_eq {β γ Q : ℝ} (hβ0 : 0 < β) {R : ℝ → ℝ}
    (hRe : ∀ q : ℝ, 0 ≤ q → R q = Muon.DetEquiv.rW (Muon.emaW β) q) {z : ℝ} (hz : 0 < z) :
    rvD_T R β γ Q z = rvT β γ Q z := by
  unfold rvD_T rvT
  refine tsum_congr (fun ℓ => ?_)
  have : 0 < z / β ^ (2 * (ℓ + 1)) := by positivity
  rw [rvD_J_eq hRe this]


private lemma rvr_meas {β γ Q ψ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hQ : 0 < Q) (hr : Muon.DetEquiv.rW (Muon.emaW β) Q = ψ) (hψγ : ψ < γ) :
    ∃ Φ : ℝ × ℝ → ℝ, Measurable Φ ∧ (∀ p, 0 ≤ Φ p) ∧
      ∀ y z : ℝ, 0 < y → 0 < z → Φ (y, z) = rvPsi β γ Q (y, z) := by
  have hlink := rvr_link hβ0 hβ1
  set R : ℝ → ℝ := fun q => Muon.DetEquiv.rW (Muon.emaW β) (max q 0) with hRdef
  have hRc : Continuous R :=
    ContinuousOn.comp_continuous hlink.1 (continuous_id.max continuous_const)
      (fun q => le_max_right q 0)
  have hRm : Measurable R := hRc.measurable
  have hRe : ∀ q : ℝ, 0 ≤ q → R q = Muon.DetEquiv.rW (Muon.emaW β) q := fun q hq => by
    simp only [hRdef, max_eq_left hq]
  refine ⟨fun p => max (rvD_Psi R β γ Q p) 0,
    (rvD_Psi_meas hRm β γ _).max measurable_const, fun p => le_max_right _ _, ?_⟩
  intro y z hy hz
  have heq : rvD_Psi R β γ Q (y, z) = rvPsi β γ Q (y, z) := by
    unfold rvD_Psi rvPsi
    simp only
    rw [rvD_J_eq hRe hy, rvD_T_eq hβ0 hRe hz, rvD_Δ_eq hRe hy hz]
  show max (rvD_Psi R β γ Q (y, z)) 0 = _
  rw [heq]
  exact max_eq_left (rvr_Psi_nonneg hβ0 hβ1 hγ hQ hr hψγ hy hz)

private lemma rvr_D_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {y z : ℝ} (hy : 0 < y)
    (hz : 0 < z) : 0 ≤ isoDivDiff β y z := by
  have hlink := rvr_link hβ0 hβ1
  unfold isoDivDiff
  split_ifs with h
  · subst h
    have hd := ((lem_app_iso_count_ii hβ0 hβ1).1 y hy).1
    have : 0 ≤ deriv (Muon.DetEquiv.rW (Muon.emaW β)) y := by
      by_contra hn
      push_neg at hn
      have := mul_neg_of_pos_of_neg hy hn
      linarith
    exact div_nonneg this (Real.sqrt_nonneg _)
  · have hs : 0 < Real.sqrt (y * z) := Real.sqrt_pos.mpr (mul_pos hy hz)
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have := hlink.2.1.monotoneOn (mem_Ici.2 hy.le) (mem_Ici.2 hz.le) hlt.le
      refine div_nonneg_of_nonpos (by linarith) ?_
      nlinarith
    · have := hlink.2.1.monotoneOn (mem_Ici.2 hz.le) (mem_Ici.2 hy.le) hgt.le
      exact div_nonneg (by linarith) (by nlinarith)

private lemma rvr_isoUlev_zero (β γ y : ℝ) : isoUlev β γ 0 y = 1 := by
  simp [isoUlev]

private lemma rvr_standin {β γ Q : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (L : ℕ) :
    ∃ G : ℝ × ℝ → ℝ, Measurable G ∧ ∀ y z : ℝ, 0 < y → 0 < z →
      G (y, z) = (if y < Q ∧ z / β ^ (2 * L) < Q then (1 : ℝ) else 0) *
        (isoDivDiff β y z * isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * L))
          / isoDeltaHat β γ y z) := by
  have hlink := rvr_link hβ0 hβ1
  obtain ⟨R, hRm, hRe⟩ : ∃ R : ℝ → ℝ, Measurable R ∧
      ∀ q : ℝ, 0 ≤ q → R q = Muon.DetEquiv.rW (Muon.emaW β) q := by
    refine ⟨fun q => Muon.DetEquiv.rW (Muon.emaW β) (max q 0), ?_, fun q hq => by
      simp [max_eq_left hq]⟩
    exact (ContinuousOn.comp_continuous hlink.1 (continuous_id.max continuous_const)
      (fun q => le_max_right q 0)).measurable
  have hder : ∀ y : ℝ, 0 < y → deriv R y = deriv (Muon.DetEquiv.rW (Muon.emaW β)) y := by
    intro y hy
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioi_mem_nhds hy] with q hq using hRe q (le_of_lt hq)
  have hDm : Measurable fun p : ℝ × ℝ => if p.1 = p.2 then deriv R p.1 / Real.sqrt (p.1 * p.1)
      else (R p.1 - R p.2) / ((p.1 - p.2) * Real.sqrt (p.1 * p.2)) := by
    refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) ?_ ?_
    · exact ((measurable_deriv R).comp measurable_fst).div
        ((measurable_fst.mul measurable_fst).sqrt)
    · exact ((hRm.comp measurable_fst).sub (hRm.comp measurable_snd)).div
        ((measurable_fst.sub measurable_snd).mul ((measurable_fst.mul measurable_snd).sqrt))
  have hZm : Measurable fun p : ℝ × ℝ => if p.1 = p.2 then p.1 * deriv R p.1
      else Real.sqrt (p.1 * p.2) * (R p.1 - R p.2) / (p.1 - p.2) := by
    refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) ?_ ?_
    · exact measurable_fst.mul ((measurable_deriv R).comp measurable_fst)
    · exact (((measurable_fst.mul measurable_snd).sqrt).mul
        ((hRm.comp measurable_fst).sub (hRm.comp measurable_snd))).div
        (measurable_fst.sub measurable_snd)
  have hXm : Measurable fun p : ℝ × ℝ => if p.1 = p.2 then R p.1 - p.1 * deriv R p.1
      else (p.2 * R p.1 - p.1 * R p.2) / (p.2 - p.1) := by
    refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) ?_ ?_
    · exact (hRm.comp measurable_fst).sub
        (measurable_fst.mul ((measurable_deriv R).comp measurable_fst))
    · exact ((measurable_snd.mul (hRm.comp measurable_fst)).sub
        (measurable_fst.mul (hRm.comp measurable_snd))).div (measurable_snd.sub measurable_fst)
  have hjm : Measurable fun y : ℝ => γ - R y + 2 * (y * deriv R y) :=
    (measurable_const.sub hRm).add (measurable_const.mul (measurable_id.mul (measurable_deriv R)))
  set Dt := fun p : ℝ × ℝ => if p.1 = p.2 then deriv R p.1 / Real.sqrt (p.1 * p.1)
      else (R p.1 - R p.2) / ((p.1 - p.2) * Real.sqrt (p.1 * p.2)) with hDt
  set Zt := fun p : ℝ × ℝ => if p.1 = p.2 then p.1 * deriv R p.1
      else Real.sqrt (p.1 * p.2) * (R p.1 - R p.2) / (p.1 - p.2) with hZt
  set Xt := fun p : ℝ × ℝ => if p.1 = p.2 then R p.1 - p.1 * deriv R p.1
      else (p.2 * R p.1 - p.1 * R p.2) / (p.2 - p.1) with hXt
  set jt := fun y : ℝ => γ - R y + 2 * (y * deriv R y) with hjt
  have hcond : MeasurableSet {p : ℝ × ℝ | p.1 < Q ∧
      p.2 / β ^ (2 * L) < Q} :=
    (measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_lt (measurable_snd.div_const _) measurable_const)
  refine ⟨fun p => (if p.1 < Q ∧ p.2 / β ^ (2 * L) < Q then (1 : ℝ) else 0)
      * (Dt p * jt p.1 * jt (p.2 / β ^ (2 * L)) /
        ((1 - Xt p / γ) ^ 2 - (Zt p / γ) ^ 2)), ?_, ?_⟩
  · refine (Measurable.ite hcond measurable_const measurable_const).mul ?_
    have hD : Measurable Dt := hDm
    have hZ : Measurable Zt := hZm
    have hX : Measurable Xt := hXm
    have hj : Measurable jt := hjm
    refine ((hD.mul (hj.comp measurable_fst)).mul (hj.comp (measurable_snd.div_const _))).div ?_
    exact ((measurable_const.sub (hX.div_const _)).pow_const 2).sub ((hZ.div_const _).pow_const 2)
  · intro y z hy hz
    have hz' : 0 < z / β ^ (2 * L) := div_pos hz (pow_pos hβ0 _)
    beta_reduce
    congr 1
    have hj1 : jt y = isoWeightJ β γ y := by
      simp only [hjt, isoWeightJ, isoResid, isoEslope, hRe y hy.le, hder y hy]
    have hj2 : jt (z / β ^ (2 * L)) = isoWeightJ β γ (z / β ^ (2 * L)) := by
      simp only [hjt, isoWeightJ, isoResid, isoEslope, hRe _ hz'.le, hder _ hz']
    have hD' : Dt (y, z) = isoDivDiff β y z := by
      simp only [hDt, isoDivDiff, hRe y hy.le, hRe z hz.le, hder y hy]
    have hZ' : Zt (y, z) = isoZkern β y z := by
      simp only [hZt, isoZkern, isoEslope, hRe y hy.le, hRe z hz.le, hder y hy]
    have hX' : Xt (y, z) = isoXkern β y z := by
      simp only [hXt, isoXkern, isoEslope, hRe y hy.le, hRe z hz.le, hder y hy]
    show Dt (y, z) * jt y * jt (z / β ^ (2 * L)) /
        ((1 - Xt (y, z) / γ) ^ 2 - (Zt (y, z) / γ) ^ 2) = _
    rw [hD', hZ', hX', hj1, hj2]
    rfl


private lemma rvr_ptwise {β γ Q ψ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hQ : 0 < Q) (hr : Muon.DetEquiv.rW (Muon.emaW β) Q = ψ) (hψγ : ψ < γ)
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    ∑' ℓ : ℕ, ENNReal.ofReal
        ((if y < Q ∧ z / β ^ (2 * (ℓ + 1)) < Q then (1 : ℝ) else 0) *
          (isoDivDiff β y z * isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * (ℓ + 1)))
            / isoDeltaHat β γ y z)) =
      ENNReal.ofReal (γ ^ 2 * (isoDivDiff β y z * rvPsi β γ Q (y, z))) := by
  have hγ0 := rvr_gamma_pos hβ0 hβ1 hγ
  by_cases hreg : y < Q ∧ z / β ^ (2 * 1) < Q
  · obtain ⟨hAy, hAz, hΔ, hyr⟩ := rvr_region hβ0 hβ1 hγ hQ hr hψγ hy hz hreg.1 hreg.2
    have hD := rvr_D_nonneg hβ0 hβ1 hy hz
    have hjy : 0 ≤ isoWeightJ β γ y := hAy.le.trans (rvr_J_bounds (γ := γ) hβ0 hβ1 hy).1
    obtain ⟨hsum, hnn, -⟩ := rvr_T_upper hβ0 hβ1 hQ hr hψγ hz
    set C := isoDivDiff β y z * isoWeightJ β γ y / isoDeltaHat β γ y z with hC
    have hC0 : 0 ≤ C := div_nonneg (mul_nonneg hD hjy) hΔ.le
    have hterm : ∀ ℓ : ℕ, (if y < Q ∧ z / β ^ (2 * (ℓ + 1)) < Q
        then (1 : ℝ) else 0) * (isoDivDiff β y z * isoWeightJ β γ y *
          isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) / isoDeltaHat β γ y z) =
        C * (if z / β ^ (2 * (ℓ + 1)) < Q
          then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0) := by
      intro ℓ
      by_cases h : z / β ^ (2 * (ℓ + 1)) < Q
      · rw [if_pos ⟨hreg.1, h⟩, if_pos h, hC]; ring
      · rw [if_neg (fun hh => h hh.2), if_neg h]; ring
    simp_rw [hterm]
    have hnn' : ∀ ℓ : ℕ, 0 ≤ (if z / β ^ (2 * (ℓ + 1)) < Q
          then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0) := hnn
    simp_rw [ENNReal.ofReal_mul hC0]
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg hnn' hsum, ← ENNReal.ofReal_mul hC0]
    congr 1
    have hT : rvT β γ Q z = ∑' ℓ : ℕ, (if z / β ^ (2 * (ℓ + 1)) < Q
          then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0) := rfl
    rw [← hT]
    unfold rvPsi
    rw [if_pos hreg, hC]
    field_simp
  · have hzero : ∀ ℓ : ℕ, ¬ (y < Q ∧ z / β ^ (2 * (ℓ + 1)) < Q) := by
      intro ℓ ⟨h1, h2⟩
      apply hreg
      refine ⟨h1, lt_of_le_of_lt ?_ h2⟩
      have hp : β ^ (2 * (ℓ + 1)) ≤ β ^ (2 * 1) :=
        pow_le_pow_of_le_one hβ0.le hβ1.le (by omega)
      exact div_le_div_of_nonneg_left hz.le (pow_pos hβ0 _) hp
    have : ∀ ℓ : ℕ, ENNReal.ofReal
        ((if y < Q ∧ z / β ^ (2 * (ℓ + 1)) < Q then (1 : ℝ) else 0) *
          (isoDivDiff β y z * isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * (ℓ + 1)))
            / isoDeltaHat β γ y z)) = 0 := by
      intro ℓ
      rw [if_neg (hzero ℓ)]; simp
    simp_rw [this]
    unfold rvPsi
    rw [if_neg hreg]
    simp

private lemma rvr_step1 {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hϱ : 0 < ϱ) :
    ∑' ℓ : ℕ, isoCircLag β γ ϱ (ℓ + 1) =
      ENNReal.ofReal (1 / γ) * ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal (rvPsi β γ (isoQpsi β γ ϱ) (isoPairMap (isoQlevel β η) w)) ∂isoNuStar := by
  have hγ0 := rvr_gamma_pos hβ0 hβ1 hγ
  obtain ⟨hQ, hr, hψ0, hψγ⟩ := rvr_Q_spec hβ0 hβ1 hγ0 hϱ
  set Q := isoQpsi β γ ϱ with hQdef
  have hquad : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hrep : ∀ ℓ : ℕ, isoCircLag β γ ϱ (ℓ + 1) =
      ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3)) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), ENNReal.ofReal
          ((if p.1 < Q ∧ p.2 / β ^ (2 * (ℓ + 1)) < Q then (1 : ℝ) else 0) *
            (isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 *
              isoWeightJ β γ (p.2 / β ^ (2 * (ℓ + 1))) / isoDeltaHat β γ p.1 p.2)) := by
    intro ℓ
    unfold isoCircLag isoRepCoeffEN
    simp only [mul_one]
    rfl
  have hmeas : ∀ ℓ : ℕ, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
          ((if p.1 < Q ∧ p.2 / β ^ (2 * (ℓ + 1)) < Q then (1 : ℝ) else 0) *
            (isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 *
              isoWeightJ β γ (p.2 / β ^ (2 * (ℓ + 1))) / isoDeltaHat β γ p.1 p.2)))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))) := by
    intro ℓ
    obtain ⟨G, hGm, hG⟩ := rvr_standin (β := β) (γ := γ) (Q := Q) hβ0 hβ1 (ℓ + 1)
    refine (hGm.ennreal_ofReal.aemeasurable).congr ?_
    refine (ae_restrict_iff' hquad).2 (Filter.Eventually.of_forall fun p hp => ?_)
    have := hG p.1 p.2 hp.1 hp.2
    simp only [Prod.mk.eta] at this
    simp only [this]
  have hsum : ∑' ℓ : ℕ, isoCircLag β γ ϱ (ℓ + 1) =
      ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3)) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal (γ ^ 2 * (isoDivDiff β p.1 p.2 * rvPsi β γ Q p)) := by
    simp_rw [hrep]
    rw [ENNReal.tsum_mul_left, ← lintegral_tsum hmeas]
    congr 1
    refine setLIntegral_congr_fun hquad (fun p hp => ?_)
    exact rvr_ptwise hβ0 hβ1 hγ hQ hr hψγ hp.1 hp.2
  obtain ⟨Φ, hΦm, hΦ0, hΦe⟩ := rvr_meas hβ0 hβ1 hγ hQ hr hψγ
  have havg := (lem_app_iso_averaging_i hβ0 hβ1).2 Φ hΦm hΦ0
  have hpos : ∀ (η : ℝ), 0 < η → ∀ w : Bool × ℝ × ℝ,
      0 < (isoPairMap (isoQlevel β η) w).1 ∧ 0 < (isoPairMap (isoQlevel β η) w).2 := by
    intro η hη w
    have hs := (rvr_Qlevel_spec hβ0 hβ1 hη).1
    unfold isoPairMap
    split_ifs
    · exact ⟨mul_pos hs (Real.exp_pos _), mul_pos hs (Real.exp_pos _)⟩
    · exact ⟨mul_pos hs (Real.exp_pos _), mul_pos hs (Real.exp_pos _)⟩
  have hrhs : (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal (Φ (isoPairMap (isoQlevel β η) w)) ∂isoNuStar) =
      ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal (rvPsi β γ Q (isoPairMap (isoQlevel β η) w)) ∂isoNuStar := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun η hη => ?_)
    refine lintegral_congr (fun w => ?_)
    obtain ⟨h1, h2⟩ := hpos η hη w
    have := hΦe _ _ h1 h2
    simp only [Prod.mk.eta] at this
    rw [this]
  have hlhs : (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal (isoDivDiff β p.1 p.2 * Φ p)) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal (isoDivDiff β p.1 p.2 * rvPsi β γ Q p) := by
    refine setLIntegral_congr_fun hquad (fun p hp => ?_)
    have := hΦe p.1 p.2 hp.1 hp.2
    simp only [Prod.mk.eta] at this
    rw [this]
  rw [hlhs, hrhs] at havg
  rw [hsum]
  have hsplit : (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal (γ ^ 2 * (isoDivDiff β p.1 p.2 * rvPsi β γ Q p))) =
      ENNReal.ofReal (γ ^ 2) * ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal (isoDivDiff β p.1 p.2 * rvPsi β γ Q p) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun p => ?_)
    exact ENNReal.ofReal_mul (by positivity)
  rw [hsplit, ← havg]
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

/-- Pointwise bounds at `Π(Q_η; b, a, c)`. -/
private lemma rvr_pair {β γ Q ψ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hQ : 0 < Q) (hr : Muon.DetEquiv.rW (Muon.emaW β) Q = ψ) (hψγ : ψ < γ)
    {η : ℝ} (hη : 0 < η) (b : Bool) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    0 ≤ rvPsi β γ Q (isoPairMap (isoQlevel β η) (b, a, c)) ∧
    (ψ ≤ η → rvPsi β γ Q (isoPairMap (isoQlevel β η) (b, a, c)) = 0) ∧
    (η < ψ → rvPsi β γ Q (isoPairMap (isoQlevel β η) (b, a, c)) ≤
      rvH γ ψ η + isoK8 β * (1 + (a + c) ^ 2 +
        (max 0 (-isoN β (isoPairMap (isoQlevel β η) (b, a, c)).2)) ^ 2)) ∧
    (η < ψ → rvH γ ψ η - 6 * (isoEbar β * (a + c + 1)) - 3 / 2 ≤
      rvPsi β γ Q (isoPairMap (isoQlevel β η) (b, a, c))) := by
  have hγ0 := rvr_gamma_pos hβ0 hβ1 hγ
  obtain ⟨hs, hrs⟩ := rvr_Qlevel_spec hβ0 hβ1 hη
  have h := lem_app_iso_averaging_iii (γ := γ) hβ0 hβ1 (isoQlevel β η) hs b a c ha hc
  dsimp only at h
  have hsA : isoResid β γ (isoQlevel β η) = γ - η := by unfold isoResid; rw [hrs]
  obtain ⟨y, z, hp⟩ : ∃ y z : ℝ, isoPairMap (isoQlevel β η) (b, a, c) = (y, z) :=
    ⟨_, _, Prod.mk.eta.symm⟩
  rw [hp] at h ⊢
  simp only at h ⊢
  obtain ⟨-, -, hyA, hzA, -⟩ := h
  rw [hsA] at hyA hzA
  have hyz : 0 < y ∧ 0 < z ∧ (isoQlevel β η ≤ y ∨ isoQlevel β η ≤ z) := by
    cases b <;> simp only [isoPairMap, Bool.false_eq_true, ite_false, ite_true] at hp <;>
      simp only [Prod.mk.injEq] at hp <;> obtain ⟨rfl, rfl⟩ := hp
    · refine ⟨by positivity, by positivity, Or.inr ?_⟩
      have : 1 ≤ Real.exp a := Real.one_le_exp ha
      nlinarith
    · refine ⟨by positivity, by positivity, Or.inl ?_⟩
      have : 1 ≤ Real.exp a := Real.one_le_exp ha
      nlinarith
  obtain ⟨hy, hz, hge⟩ := hyz
  have hτ : 0 ≤ a + c := by linarith
  refine ⟨rvr_Psi_nonneg hβ0 hβ1 hγ hQ hr hψγ hy hz, fun hηψ => ?_, fun hηψ => ?_, fun hηψ => ?_⟩
  · have hns : ¬ isoQlevel β η < Q := by
      rw [rvr_lt_iff hβ0 hβ1 hQ hr hs, hrs]; linarith
    have hfail : ¬ (y < Q ∧ z / β ^ (2 * 1) < Q) := by
      rintro ⟨h1, h2⟩
      have hzz : z ≤ z / β ^ (2 * 1) := by
        rw [le_div_iff₀ (by positivity)]
        have : β ^ (2 * 1) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
        nlinarith
      rcases hge with h | h
      · exact hns (lt_of_le_of_lt h h1)
      · exact hns (lt_of_le_of_lt (h.trans hzz) h2)
    unfold rvPsi
    rw [if_neg hfail]
  · exact rvr_core_up hβ0 hβ1 hγ hQ hr hψγ hη hηψ hy hz hτ hyA hzA
  · have := rvr_core_low hβ0 hβ1 hγ hQ hr hψγ hη hηψ hy hz hτ hyA hzA
    have e : isoEbar β * (a + c + 1) = isoEbar β * ((a + c) + 1) := rfl
    rw [e]; exact this

private lemma rvF_nu_ae : ∀ᵐ w ∂isoNuStar, 0 < w.2.1 ∧ 0 < w.2.2 := by
  have hS : MeasurableSet {w : Bool × ℝ × ℝ | 0 < w.2.1 ∧ 0 < w.2.2} :=
    (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
      (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd))
  haveI : SFinite isoNuBase := by unfold isoNuBase; infer_instance
  unfold isoNuStar
  have h := (Measure.ae_prod_mem_iff_ae_ae_mem (μ := (Measure.count : Measure Bool))
    (ν := isoNuBase) hS).2
  refine h (Filter.Eventually.of_forall fun b => ?_)
  have h1 : ∀ᵐ p ∂((volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))),
      p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  have h2 := (withDensity_absolutelyContinuous
    ((volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))
    (fun p : ℝ × ℝ => ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))))).ae_le h1
  filter_upwards [h2] with p hp
  exact ⟨hp.1, hp.2⟩

private lemma rvF_tau_meas : Measurable (fun w : Bool × ℝ × ℝ => w.2.1 + w.2.2) := by fun_prop

private lemma rvF_prob {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : IsProbabilityMeasure isoNuStar :=
  (lem_app_iso_averaging_i hβ0 hβ1).1

private lemma rvF_tau_int {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Integrable (fun w : Bool × ℝ × ℝ => w.2.1 + w.2.2) isoNuStar := by
  haveI := rvF_prob hβ0 hβ1
  have h2 := (lem_app_iso_averaging_ii).2.1
  have hint : Integrable (fun w : Bool × ℝ × ℝ => (w.2.1 + w.2.2) ^ 2) isoNuStar := by
    by_contra hn
    rw [integral_undef hn] at h2
    have : (0 : ℝ) < 2 * Real.pi ^ 2 := by positivity
    linarith
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hint)
    rvF_tau_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [abs_nonneg (w.2.1 + w.2.2), sq_abs (w.2.1 + w.2.2), sq_nonneg (|w.2.1 + w.2.2| - 1)]

private lemma rvF_M1_eq : ∫ w, (w.2.1 + w.2.2) ∂isoNuStar = isoM1 :=
  (lem_app_iso_averaging_ii).1

private lemma rvF_M1_nonneg' : 0 ≤ isoM1 := by
  rw [← rvF_M1_eq]
  refine integral_nonneg_of_ae ?_
  filter_upwards [rvF_nu_ae] with w hw
  exact (add_pos hw.1 hw.2).le

private lemma rvF_M3_nonneg : 0 ≤ isoM3 := by
  have : ∫ w, (w.2.1 + w.2.2) ^ 3 ∂isoNuStar = isoM3 := (lem_app_iso_averaging_ii).2.2.1
  rw [← this]
  refine integral_nonneg_of_ae ?_
  filter_upwards [rvF_nu_ae] with w hw
  exact pow_nonneg (add_pos hw.1 hw.2).le 3

private lemma rvF_lint_tau {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∫⁻ w, ENNReal.ofReal (w.2.1 + w.2.2) ∂isoNuStar = ENNReal.ofReal isoM1 := by
  rw [← rvF_M1_eq, ofReal_integral_eq_lintegral_ofReal (rvF_tau_int hβ0 hβ1)]
  filter_upwards [rvF_nu_ae] with w hw
  exact (add_pos hw.1 hw.2).le

private lemma rvF_M1_nonneg : 0 ≤ isoM1 := rvF_M1_nonneg'

private lemma rvF_L_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 ≤ isoLbar1 β ∧ 0 ≤ isoLbar2 β := by
  have hM1 := rvF_M1_nonneg'
  have hM3 := rvF_M3_nonneg
  have hM2 : 0 ≤ isoM2 := by unfold isoM2; positivity
  have hE : 0 ≤ isoEbar β := le_trans zero_le_one (le_max_left _ _)
  have hL : 0 < Real.log (1 / β) := Real.log_pos (one_lt_one_div hβ0 hβ1)
  have hb : 0 < 1 - β ^ 2 := by nlinarith
  constructor
  · unfold isoLbar1; positivity
  · unfold isoLbar2; positivity


private lemma rvF_eta_const {γ : ℝ} (hγ : 0 < γ) {K : ℝ} (hK : 0 ≤ K) :
    ∫⁻ η in Ioi (0 : ℝ), (if η < γ then ENNReal.ofReal K else 0) = ENNReal.ofReal (γ * K) := by
  have h1 : (fun η : ℝ => if η < γ then ENNReal.ofReal K else 0) =
      (Iio γ).indicator (fun _ => ENNReal.ofReal K) := by
    funext η; simp [Set.indicator]
  rw [h1, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    Set.inter_comm, Set.Ioi_inter_Iio, setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul hK,
    sub_zero, mul_comm]


private lemma rvF_lint_up_tau {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u v : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v) :
    ∫⁻ w, ENNReal.ofReal (u + v * (w.2.1 + w.2.2)) ∂isoNuStar =
      ENNReal.ofReal (u + v * isoM1) := by
  haveI := rvF_prob hβ0 hβ1
  have h1 : ∀ᵐ w ∂isoNuStar, ENNReal.ofReal (u + v * (w.2.1 + w.2.2)) =
      ENNReal.ofReal u + ENNReal.ofReal v * ENNReal.ofReal (w.2.1 + w.2.2) := by
    filter_upwards [rvF_nu_ae] with w hw
    rw [ENNReal.ofReal_add hu (mul_nonneg hv (add_pos hw.1 hw.2).le),
      ENNReal.ofReal_mul hv]
  rw [lintegral_congr_ae h1, lintegral_add_left measurable_const, lintegral_const,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, rvF_lint_tau hβ0 hβ1, measure_univ, mul_one,
    ← ENNReal.ofReal_mul hv, ← ENNReal.ofReal_add hu (mul_nonneg hv rvF_M1_nonneg')]


private lemma rvF_tau2_int {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Integrable (fun w : Bool × ℝ × ℝ => (w.2.1 + w.2.2) ^ 2) isoNuStar := by
  haveI := rvF_prob hβ0 hβ1
  have h2 := (lem_app_iso_averaging_ii).2.1
  by_contra hn
  rw [integral_undef hn] at h2
  have : (0 : ℝ) < 2 * Real.pi ^ 2 := by positivity
  linarith

private lemma rvF_lint_tau2 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∫⁻ w, ENNReal.ofReal ((w.2.1 + w.2.2) ^ 2) ∂isoNuStar = ENNReal.ofReal isoM2 := by
  have h2 : ∫ w, (w.2.1 + w.2.2) ^ 2 ∂isoNuStar = isoM2 := (lem_app_iso_averaging_ii).2.1
  rw [← h2, ofReal_integral_eq_lintegral_ofReal (rvF_tau2_int hβ0 hβ1)]
  exact Filter.Eventually.of_forall fun w => sq_nonneg _

private lemma rvF_lint_up_tau2 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u v : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v) :
    ∫⁻ w, ENNReal.ofReal (u + v * (w.2.1 + w.2.2) ^ 2) ∂isoNuStar =
      ENNReal.ofReal (u + v * isoM2) := by
  haveI := rvF_prob hβ0 hβ1
  have h1 : ∀ w : Bool × ℝ × ℝ, ENNReal.ofReal (u + v * (w.2.1 + w.2.2) ^ 2) =
      ENNReal.ofReal u + ENNReal.ofReal v * ENNReal.ofReal ((w.2.1 + w.2.2) ^ 2) := by
    intro w
    rw [ENNReal.ofReal_add hu (mul_nonneg hv (sq_nonneg _)), ENNReal.ofReal_mul hv]
  have hM2 : 0 ≤ isoM2 := by unfold isoM2; positivity
  simp_rw [h1]
  rw [lintegral_add_left measurable_const, lintegral_const,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, rvF_lint_tau2 hβ0 hβ1, measure_univ, mul_one,
    ← ENNReal.ofReal_mul hv, ← ENNReal.ofReal_add hu (mul_nonneg hv hM2)]


private lemma rvF_H_cont {γ ψ : ℝ} (hψγ : ψ < γ) : ContinuousOn (rvH γ ψ) (Icc 0 ψ) := by
  unfold rvH
  refine ContinuousOn.sub (by fun_prop) (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
  intro η hη
  have : 0 < γ - η := by linarith [hη.2]
  positivity

/-- `∫_0^ψ 𝖧 = (γ²/2) 𝒫(ψ/γ)`. -/
private lemma rvF_H_int {γ ψ : ℝ} (hψ : 0 < ψ) (hψγ : ψ < γ) :
    ∫ η in (0 : ℝ)..ψ, rvH γ ψ η = γ ^ 2 / 2 * isoCrossP (ψ / γ) := by
  have hg : 0 < γ - ψ := by linarith
  have hγ0 : 0 < γ := by linarith
  have hx : ∀ η ∈ Icc (0 : ℝ) ψ, 0 < γ - η := fun η hη => by linarith [hη.2]
  have hcont := rvF_H_cont hψγ
  set F : ℝ → ℝ := fun η => -(γ - η) ^ 2 / 4 + (γ - ψ) ^ 2 / 2 * Real.log (γ - η) with hF
  have hder : ∀ η ∈ uIcc (0 : ℝ) ψ, HasDerivAt F (rvH γ ψ η) η := by
    intro η hη
    rw [uIcc_of_le hψ.le] at hη
    have hpos := hx η hη
    have h1 : HasDerivAt (fun η : ℝ => γ - η) (-1) η := by
      simpa using (hasDerivAt_id η).const_sub γ
    have h2 := ((h1.pow 2).neg.div_const 4).add ((h1.log hpos.ne').const_mul ((γ - ψ) ^ 2 / 2))
    convert h2 using 1
    unfold rvH
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (hcont.intervalIntegrable_of_Icc hψ.le)]
  simp only [hF]
  have hlog : Real.log (γ - ψ) - Real.log γ = Real.log ((γ - ψ) / γ) := by
    rw [Real.log_div hg.ne' hγ0.ne']
  have hP : isoCrossP (ψ / γ) = 1 / 2 - (1 - ψ / γ) ^ 2 / 2 +
      (1 - ψ / γ) ^ 2 * Real.log (1 - ψ / γ) := by
    unfold isoCrossP
    rw [if_pos ((div_lt_one hγ0).2 hψγ)]
  rw [hP]
  have e1 : 1 - ψ / γ = (γ - ψ) / γ := by field_simp
  rw [e1, ← hlog]
  simp only [sub_zero]
  field_simp
  ring

private lemma rvF_H_nonneg {γ ψ : ℝ} (hψ : 0 < ψ) (hψγ : ψ < γ) :
    0 ≤ γ ^ 2 / 2 * isoCrossP (ψ / γ) := by
  rw [← rvF_H_int hψ hψγ]
  exact intervalIntegral.integral_nonneg hψ.le (fun η hη => by
    rcases hη.1.eq_or_lt with h | h
    · rw [← h]; unfold rvH
      have : 0 < γ := by linarith
      have : ψ ^ 2 / (2 * γ) ≤ ψ := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      simp only [sub_zero]
      linarith
    · rcases hη.2.eq_or_lt with h2 | h2
      · rw [h2]; unfold rvH; simp
      · exact (rvr_H_nonneg h h2 hψγ).1)

/-- `∫_0^ψ 𝖧 = (γ²/2) 𝒫(ψ/γ)` as an `ENNReal` integral. -/
private lemma rvF_H_lint {γ ψ : ℝ} (hψ : 0 < ψ) (hψγ : ψ < γ) :
    ∫⁻ η in Ioi (0 : ℝ), (if η < ψ then ENNReal.ofReal (rvH γ ψ η) else 0) =
      ENNReal.ofReal (γ ^ 2 / 2 * isoCrossP (ψ / γ)) := by
  have h1 : (fun η : ℝ => if η < ψ then ENNReal.ofReal (rvH γ ψ η) else 0) =
      (Iio ψ).indicator (fun η => ENNReal.ofReal (rvH γ ψ η)) := by
    funext η; simp [Set.indicator]
  rw [h1, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    Set.inter_comm, Set.Ioi_inter_Iio]
  have hnn : ∀ η ∈ Ioo (0 : ℝ) ψ, 0 ≤ rvH γ ψ η := fun η hη =>
    (rvr_H_nonneg hη.1 hη.2 hψγ).1
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((rvF_H_cont hψγ).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall hnn))]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hψ.le]
  exact rvF_H_int hψ hψγ

private lemma rvr_I_upper {β γ Q ψ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hQ : 0 < Q) (hr : Muon.DetEquiv.rW (Muon.emaW β) Q = ψ) (hψ0 : 0 < ψ) (hψγ : ψ < γ) :
    (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal (rvPsi β γ Q (isoPairMap (isoQlevel β η) w)) ∂isoNuStar) ≤
      ENNReal.ofReal (γ ^ 2 / 2 * isoCrossP (ψ / γ)
        + isoK8 β * (ψ * (1 + isoM2) + isoLbar2 β)) := by
  haveI := rvF_prob hβ0 hβ1
  have hK0 := rvr_K8_nonneg hβ0 hβ1
  have hM2 : 0 ≤ isoM2 := by unfold isoM2; positivity
  obtain ⟨hL1, hL2⟩ := rvF_L_nonneg hβ0 hβ1
  have hHn := rvF_H_nonneg hψ0 hψγ
  set K := isoK8 β with hK
  set n : ℝ × (Bool × ℝ × ℝ) → ℝ := fun x =>
    max 0 (-isoN β (isoPairMap (isoQlevel β x.1) x.2).2) with hn
  have hn0 : ∀ x, 0 ≤ n x := fun x => le_max_left _ _
  have hpt : ∀ η : ℝ, 0 < η → ∀ᵐ w ∂isoNuStar,
      ENNReal.ofReal (rvPsi β γ Q (isoPairMap (isoQlevel β η) w)) ≤
        (if η < ψ then ENNReal.ofReal (rvH γ ψ η) else 0) +
          ((if η < ψ then ENNReal.ofReal (K + K * (w.2.1 + w.2.2) ^ 2) else 0)
            + ENNReal.ofReal K * ENNReal.ofReal (n (η, w) ^ 2)) := by
    intro η hη
    filter_upwards [rvF_nu_ae] with w hw
    obtain ⟨h0, h1, h2, -⟩ := rvr_pair hβ0 hβ1 hγ hQ hr hψγ hη w.1 hw.1.le hw.2.le
    by_cases h : η < ψ
    · simp only [if_pos h]
      have hb := h2 h
      have hH := (rvr_H_nonneg hη h hψγ).1
      have hA : 0 ≤ K + K * (w.2.1 + w.2.2) ^ 2 := by positivity
      have hB : 0 ≤ K * n (η, w) ^ 2 := by positivity
      rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_add hA hB, ← ENNReal.ofReal_add hH (by positivity)]
      refine ENNReal.ofReal_le_ofReal (le_trans hb (le_of_eq ?_))
      simp only [hn]
      ring
    · simp only [if_neg h]
      rw [h1 (not_lt.mp h)]
      simp
  have hmA : Measurable (fun η : ℝ => if η < ψ then ENNReal.ofReal (rvH γ ψ η) else 0) :=
    Measurable.ite measurableSet_Iio (by unfold rvH; fun_prop) measurable_const
  have hmB : Measurable (fun η : ℝ => if η < ψ then ENNReal.ofReal (K + K * isoM2) else 0) :=
    Measurable.ite measurableSet_Iio measurable_const measurable_const
  have hmB' : ∀ η : ℝ, Measurable (fun w : Bool × ℝ × ℝ =>
      if η < ψ then ENNReal.ofReal (K + K * (w.2.1 + w.2.2) ^ 2) else 0) := by
    intro η
    by_cases h : η < ψ
    · simp only [if_pos h]
      exact (by fun_prop : Measurable fun w : Bool × ℝ × ℝ =>
        K + K * (w.2.1 + w.2.2) ^ 2).ennreal_ofReal
    · simp only [if_neg h]; exact measurable_const
  have hinB : ∀ η : ℝ, ∫⁻ w, (if η < ψ then ENNReal.ofReal (K + K * (w.2.1 + w.2.2) ^ 2) else 0)
      ∂isoNuStar = (if η < ψ then ENNReal.ofReal (K + K * isoM2) else 0) := by
    intro η
    by_cases h : η < ψ
    · simp only [if_pos h]
      exact rvF_lint_up_tau2 hβ0 hβ1 hK0 hK0
    · simp [h]
  have hinC : ∀ η : ℝ, ∫⁻ w, ENNReal.ofReal K * ENNReal.ofReal (n (η, w) ^ 2) ∂isoNuStar =
      ENNReal.ofReal K * ∫⁻ w, ENNReal.ofReal (n (η, w) ^ 2) ∂isoNuStar := by
    intro η
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hlow := (lem_app_iso_low_levels_ii hβ0 hβ1).2
  calc (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal (rvPsi β γ Q (isoPairMap (isoQlevel β η) w)) ∂isoNuStar)
      ≤ ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
          ((if η < ψ then ENNReal.ofReal (rvH γ ψ η) else 0) +
            ((if η < ψ then ENNReal.ofReal (K + K * (w.2.1 + w.2.2) ^ 2) else 0)
              + ENNReal.ofReal K * ENNReal.ofReal (n (η, w) ^ 2))) ∂isoNuStar :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall fun η hη => lintegral_mono_ae (hpt η hη)))
    _ = ∫⁻ η in Ioi (0 : ℝ),
          ((if η < ψ then ENNReal.ofReal (rvH γ ψ η) else 0) +
            ((if η < ψ then ENNReal.ofReal (K + K * isoM2) else 0)
              + ENNReal.ofReal K * ∫⁻ w, ENNReal.ofReal (n (η, w) ^ 2) ∂isoNuStar)) := by
        congr 1; funext η
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_add_left (hmB' η), hinB, hinC]
    _ = ENNReal.ofReal (γ ^ 2 / 2 * isoCrossP (ψ / γ)) +
          (ENNReal.ofReal (ψ * (K + K * isoM2)) +
            ENNReal.ofReal K * ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, ENNReal.ofReal (n (η, w) ^ 2) ∂isoNuStar) := by
        rw [lintegral_add_left hmA, lintegral_add_left hmB, rvF_H_lint hψ0 hψγ,
          rvF_eta_const hψ0 (by positivity), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (γ ^ 2 / 2 * isoCrossP (ψ / γ)) +
          (ENNReal.ofReal (ψ * (K + K * isoM2)) + ENNReal.ofReal K * ENNReal.ofReal (isoLbar2 β)) := by
        have h1 : ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, ENNReal.ofReal (n (η, w) ^ 2) ∂isoNuStar ≤
            ENNReal.ofReal (isoLbar2 β) := hlow
        exact add_le_add le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl h1))
    _ = _ := by
        rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add hHn (by positivity)]
        congr 1
        ring

private lemma rvr_I_lower {β γ Q ψ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hQ : 0 < Q) (hr : Muon.DetEquiv.rW (Muon.emaW β) Q = ψ) (hψ0 : 0 < ψ) (hψγ : ψ < γ) :
    ENNReal.ofReal (γ ^ 2 / 2 * isoCrossP (ψ / γ)) ≤
      (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal (rvPsi β γ Q (isoPairMap (isoQlevel β η) w)) ∂isoNuStar)
      + ENNReal.ofReal (ψ * (6 * isoEbar β * (isoM1 + 1) + 3 / 2)) := by
  haveI := rvF_prob hβ0 hβ1
  obtain ⟨he, hΦ, hcp⟩ := rvr_consts hβ0 hβ1
  have he0 : 0 ≤ isoEbar β := by linarith
  have hM1 := rvF_M1_nonneg'
  set K : ℝ := 6 * isoEbar β * (isoM1 + 1) + 3 / 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hpt : ∀ η : ℝ, 0 < η → ∀ᵐ w ∂isoNuStar,
      (if η < ψ then ENNReal.ofReal (rvH γ ψ η) else 0) ≤
        (if η < ψ then ENNReal.ofReal ((6 * isoEbar β + 3 / 2) + 6 * isoEbar β * (w.2.1 + w.2.2))
          else 0) + ENNReal.ofReal (rvPsi β γ Q (isoPairMap (isoQlevel β η) w)) := by
    intro η hη
    filter_upwards [rvF_nu_ae] with w hw
    by_cases h : η < ψ
    · simp only [if_pos h]
      obtain ⟨h0, -, -, h4⟩ := rvr_pair hβ0 hβ1 hγ hQ hr hψγ hη w.1 hw.1.le hw.2.le
      have hH := (rvr_H_nonneg hη h hψγ).1
      have hτ := add_pos hw.1 hw.2
      have hυ : 0 ≤ (6 * isoEbar β + 3 / 2) + 6 * isoEbar β * (w.2.1 + w.2.2) := by positivity
      rw [← ENNReal.ofReal_add hυ (h0)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := h4 h
      nlinarith
    · simp [h]
  have hmeasH : ∀ η : ℝ, Measurable (fun w : Bool × ℝ × ℝ =>
      if η < ψ then ENNReal.ofReal ((6 * isoEbar β + 3 / 2) + 6 * isoEbar β * (w.2.1 + w.2.2))
        else 0) := by
    intro η
    by_cases h : η < ψ
    · simp only [if_pos h]
      exact (by fun_prop : Measurable fun w : Bool × ℝ × ℝ =>
        (6 * isoEbar β + 3 / 2) + 6 * isoEbar β * (w.2.1 + w.2.2)).ennreal_ofReal
    · simp only [if_neg h]; exact measurable_const
  have hconst : ∀ η : ℝ, ∫⁻ w, (if η < ψ then ENNReal.ofReal
      ((6 * isoEbar β + 3 / 2) + 6 * isoEbar β * (w.2.1 + w.2.2)) else 0) ∂isoNuStar =
      (if η < ψ then ENNReal.ofReal K else 0) := by
    intro η
    by_cases h : η < ψ
    · simp only [if_pos h]
      have := rvF_lint_up_tau hβ0 hβ1 (u := 6 * isoEbar β + 3 / 2) (v := 6 * isoEbar β)
        (by positivity) (by positivity)
      rw [this, hK]
      congr 1; ring
    · simp [h]
  have hmeasA : Measurable (fun η : ℝ => if η < ψ then ENNReal.ofReal K else 0) :=
    Measurable.ite measurableSet_Iio measurable_const measurable_const
  calc ENNReal.ofReal (γ ^ 2 / 2 * isoCrossP (ψ / γ))
      = ∫⁻ η in Ioi (0 : ℝ), (if η < ψ then ENNReal.ofReal (rvH γ ψ η) else 0) :=
        (rvF_H_lint hψ0 hψγ).symm
    _ = ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, (if η < ψ then ENNReal.ofReal (rvH γ ψ η) else 0)
          ∂isoNuStar := by
        congr 1; funext η; rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
          ((if η < ψ then ENNReal.ofReal
              ((6 * isoEbar β + 3 / 2) + 6 * isoEbar β * (w.2.1 + w.2.2)) else 0)
            + ENNReal.ofReal (rvPsi β γ Q (isoPairMap (isoQlevel β η) w))) ∂isoNuStar :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall fun η hη => lintegral_mono_ae (hpt η hη)))
    _ = ∫⁻ η in Ioi (0 : ℝ),
          ((if η < ψ then ENNReal.ofReal K else 0)
            + ∫⁻ w, ENNReal.ofReal (rvPsi β γ Q (isoPairMap (isoQlevel β η) w)) ∂isoNuStar) := by
        congr 1; funext η; rw [lintegral_add_left (hmeasH η), hconst]
    _ = ENNReal.ofReal (ψ * K) + ∫⁻ η in Ioi (0 : ℝ),
          ∫⁻ w, ENNReal.ofReal (rvPsi β γ Q (isoPairMap (isoQlevel β η) w)) ∂isoNuStar := by
        rw [lintegral_add_left hmeasA, rvF_eta_const hψ0 hK0]
    _ = _ := add_comm _ _

private lemma rvr_split {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hϱ : 0 < ϱ) (ℓ : ℕ) :
    ENNReal.ofReal (lagCoeff β γ ϱ (ℓ + 1)) =
      isoCircLag β γ ϱ (ℓ + 1) + isoSharpLag β γ ϱ (ℓ + 1) := by
  have hγ0 := rvr_gamma_pos hβ0 hβ1 hγ
  obtain ⟨hQ, hr, hψ0, hψγ⟩ := rvr_Q_spec hβ0 hβ1 hγ0 hϱ
  have hquad : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  obtain ⟨-, hrep⟩ := prop_app_iso_vol_representation hβ0 hβ1 hγ0 hϱ.le (ℓ := ℓ + 1) (by omega)
  rw [hrep]
  unfold isoCircLag isoSharpLag isoRepCoeffEN
  rw [← mul_add]
  congr 1
  obtain ⟨G, hGm, hG⟩ := rvr_standin (β := β) (γ := γ) (Q := isoQpsi β γ ϱ) hβ0 hβ1 (ℓ + 1)
  have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
      ((if p.1 < isoQpsi β γ ϱ ∧ p.2 / β ^ (2 * (ℓ + 1)) < isoQpsi β γ ϱ then (1 : ℝ) else 0) *
        (isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 * isoWeightJ β γ (p.2 / β ^ (2 * (ℓ + 1))) /
          isoDeltaHat β γ p.1 p.2) * (fun _ : ℝ => (1 : ℝ))
          (isoUlev β γ ϱ p.1 * isoUlev β γ ϱ (p.2 / β ^ (2 * (ℓ + 1))))))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))) := by
    refine (hGm.ennreal_ofReal.aemeasurable).congr ?_
    refine (ae_restrict_iff' hquad).2 (Filter.Eventually.of_forall fun p hp => ?_)
    have := hG p.1 p.2 hp.1 hp.2
    simp only [Prod.mk.eta] at this
    simp only [this, mul_one]
  rw [← lintegral_add_left' hmeas]
  refine setLIntegral_congr_fun hquad (fun p hp => ?_)
  obtain ⟨hy, hz⟩ := hp
  have hy' : 0 < p.1 := hy
  have hz' : 0 < p.2 := hz
  by_cases hreg : p.1 < isoQpsi β γ ϱ ∧ p.2 / β ^ (2 * (ℓ + 1)) < isoQpsi β γ ϱ
  · simp only [if_pos hreg]
    obtain ⟨hAy, hAz, hΔ, hyr⟩ := rvr_region hβ0 hβ1 hγ hQ hr hψγ hy' hz' hreg.1
      (by simpa using (lt_of_le_of_lt (by
        have : β ^ (2 * (ℓ + 1)) ≤ β ^ (2 * 1) :=
          pow_le_pow_of_le_one hβ0.le hβ1.le (by omega)
        exact div_le_div_of_nonneg_left hz'.le (pow_pos hβ0 _) this) hreg.2))
    have hD := rvr_D_nonneg hβ0 hβ1 hy' hz'
    have hjy : 0 ≤ isoWeightJ β γ p.1 := hAy.le.trans (rvr_J_bounds (γ := γ) hβ0 hβ1 hy').1
    have hzk : 0 < p.2 / β ^ (2 * (ℓ + 1)) := div_pos hz' (pow_pos hβ0 _)
    have hrz := (rvr_lt_iff hβ0 hβ1 hQ hr hzk).1 hreg.2
    have hAzk : 0 < isoResid β γ (p.2 / β ^ (2 * (ℓ + 1))) := by unfold isoResid; linarith
    have hjz : 0 ≤ isoWeightJ β γ (p.2 / β ^ (2 * (ℓ + 1))) :=
      hAzk.le.trans (rvr_J_bounds (γ := γ) hβ0 hβ1 hzk).1
    have hu1 := rvr_u_ge hβ0 hβ1 hγ0 hϱ hy' hreg.1
    have hu2 := rvr_u_ge hβ0 hβ1 hγ0 hϱ hzk hreg.2
    set Kc := isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 *
      isoWeightJ β γ (p.2 / β ^ (2 * (ℓ + 1))) / isoDeltaHat β γ p.1 p.2 with hKc
    have hKc0 : 0 ≤ Kc := div_nonneg (mul_nonneg (mul_nonneg hD hjy) hjz) hΔ.le
    have huu : 1 ≤ isoUlev β γ ϱ p.1 * isoUlev β γ ϱ (p.2 / β ^ (2 * (ℓ + 1))) := by
      nlinarith
    have e1 : isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 * isoUlev β γ ϱ p.1 *
        (isoWeightJ β γ (p.2 / β ^ (2 * (ℓ + 1))) * isoUlev β γ ϱ (p.2 / β ^ (2 * (ℓ + 1)))) /
          isoDeltaHat β γ p.1 p.2 =
        Kc * (isoUlev β γ ϱ p.1 * isoUlev β γ ϱ (p.2 / β ^ (2 * (ℓ + 1)))) := by
      rw [hKc]; ring
    rw [e1]
    simp only [one_mul, mul_one]
    rw [← ENNReal.ofReal_add hKc0 (mul_nonneg hKc0 (by linarith))]
    congr 1
    ring
  · simp only [if_neg hreg]
    simp

private lemma rvr_main {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hϱ : 0 < ϱ) :
    Summable (fun ℓ : ℕ => lagCoeff β γ ϱ (ℓ + 1)) ∧
      -(psiIso β γ γ ϱ / γ) * isoKcirc β ≤
          (∑' ℓ : ℕ, lagCoeff β γ ϱ (ℓ + 1)) - γ / 2 * isoCrossP (psiIso β γ γ ϱ / γ) ∧
      (∑' ℓ : ℕ, lagCoeff β γ ϱ (ℓ + 1)) - γ / 2 * isoCrossP (psiIso β γ γ ϱ / γ) ≤
          (isoKflat β + isoKsharp β * psiIso β γ γ ϱ) / γ := by
  have hγ0 := rvr_gamma_pos hβ0 hβ1 hγ
  obtain ⟨hQ, hr, hψ0, hψγ⟩ := rvr_Q_spec hβ0 hβ1 hγ0 hϱ
  set Q := isoQpsi β γ ϱ with hQdef
  set ψ := psiIso β γ γ ϱ with hψdef
  set a : ℕ → ℝ := fun ℓ => lagCoeff β γ ϱ (ℓ + 1) with ha
  have hnn : ∀ ℓ, 0 ≤ a ℓ := fun ℓ => rvr_lag_nonneg hβ0 hβ1 hγ0 hϱ.le (ℓ + 1)
  set I : ENNReal := ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
    ENNReal.ofReal (rvPsi β γ Q (isoPairMap (isoQlevel β η) w)) ∂isoNuStar with hI
  have hUp := rvr_I_upper hβ0 hβ1 hγ hQ hr hψ0 hψγ
  have hLo := rvr_I_lower hβ0 hβ1 hγ hQ hr hψ0 hψγ
  have hstep := rvr_step1 hβ0 hβ1 hγ hϱ
  have hsharp := lem_app_iso_ridge_excess hβ0 hβ1 hγ hϱ
  have hsplit : ∑' ℓ : ℕ, ENNReal.ofReal (a ℓ) =
      ∑' ℓ : ℕ, isoCircLag β γ ϱ (ℓ + 1) + ∑' ℓ : ℕ, isoSharpLag β γ ϱ (ℓ + 1) := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr (fun ℓ => rvr_split hβ0 hβ1 hγ hϱ ℓ)
  have hHn := rvF_H_nonneg hψ0 hψγ
  obtain ⟨hL1, hL2⟩ := rvF_L_nonneg hβ0 hβ1
  have hK8 := rvr_K8_nonneg hβ0 hβ1
  have hM2 : 0 ≤ isoM2 := by unfold isoM2; positivity
  have hM1 := rvF_M1_nonneg'
  obtain ⟨he, hΦ, hcp⟩ := rvr_consts hβ0 hβ1
  have hKex : 0 ≤ isoKexFlat β + isoKexSharp β * ψ := by
    have hz := rrF2_zeta3_pos
    have hlb : 0 < Real.log (1 / β) := Real.log_pos (by rw [lt_div_iff₀ hβ0]; linarith)
    have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1β : 0 < 1 - β := by linarith
    have hd : 0 < 1 - β ^ 2 := by nlinarith
    have hc0 : 0 ≤ isoC β := by unfold isoC; positivity
    have hE0 : 0 < isoEbar β := by linarith
    have hK6 : 0 ≤ isoK6 β := le_trans (by norm_num) (le_max_left _ _)
    have hKJ : 0 ≤ isoKJ β := by unfold isoKJ; positivity
    have h1 : 0 ≤ isoKexFlat β := by unfold isoKexFlat; positivity
    have h2 : 0 ≤ isoKexSharp β := by unfold isoKexSharp; positivity
    positivity
  set U1 : ℝ := γ ^ 2 / 2 * isoCrossP (ψ / γ) + isoK8 β * (ψ * (1 + isoM2) + isoLbar2 β) with hU1
  have hU10 : 0 ≤ U1 := by rw [hU1]; positivity
  have hfin : ∑' ℓ : ℕ, ENNReal.ofReal (a ℓ) ≤
      ENNReal.ofReal (1 / γ) * ENNReal.ofReal U1 +
        ENNReal.ofReal ((isoKexFlat β + isoKexSharp β * ψ) / γ) := by
    rw [hsplit, hstep]
    exact add_le_add (mul_le_mul' le_rfl hUp) hsharp
  have hfin' : ∑' ℓ : ℕ, ENNReal.ofReal (a ℓ) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hfin
  have hsum : Summable a := by
    have := ENNReal.summable_toReal hfin'
    simpa [ENNReal.toReal_ofReal (hnn _)] using this
  have hS : ENNReal.ofReal (∑' ℓ, a ℓ) = ∑' ℓ : ℕ, ENNReal.ofReal (a ℓ) :=
    ENNReal.ofReal_tsum_of_nonneg hnn hsum
  set S := ∑' ℓ, a ℓ with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg hnn
  have hHdiv : γ ^ 2 / 2 * isoCrossP (ψ / γ) / γ = γ / 2 * isoCrossP (ψ / γ) := by
    field_simp
  refine ⟨hsum, ?_, ?_⟩
  · have hcirc_le : ∑' ℓ : ℕ, isoCircLag β γ ϱ (ℓ + 1) ≤ ENNReal.ofReal S := by
      rw [hS, hsplit]; exact le_self_add
    have h2 := mul_le_mul' (le_refl (ENNReal.ofReal (1 / γ))) hLo
    rw [mul_add, ← hstep] at h2
    have h3 : ENNReal.ofReal (1 / γ) * ENNReal.ofReal (γ ^ 2 / 2 * isoCrossP (ψ / γ)) ≤
        ENNReal.ofReal (S + 1 / γ * (ψ * isoKcirc β)) := by
      calc _ ≤ _ := h2
        _ ≤ ENNReal.ofReal S + ENNReal.ofReal (1 / γ) * ENNReal.ofReal (ψ * (6 * isoEbar β * (isoM1 + 1) + 3 / 2)) :=
            add_le_add hcirc_le le_rfl
        _ = _ := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hS0 (by positivity)]
            unfold isoKcirc; ring_nf
    rw [← ENNReal.ofReal_mul (by positivity)] at h3
    have h4 := (ENNReal.ofReal_le_ofReal_iff (add_nonneg hS0 (by unfold isoKcirc; positivity))).mp h3
    have e1 : 1 / γ * (γ ^ 2 / 2 * isoCrossP (ψ / γ)) = γ / 2 * isoCrossP (ψ / γ) := by
      field_simp
    have e2 : 1 / γ * (ψ * isoKcirc β) = ψ / γ * isoKcirc β := by ring
    rw [e1, e2] at h4
    linarith
  · have h3 : ENNReal.ofReal S ≤ ENNReal.ofReal (U1 / γ + (isoKexFlat β + isoKexSharp β * ψ) / γ) := by
      rw [hS]
      refine hfin.trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
    have e3 : U1 / γ = γ / 2 * isoCrossP (ψ / γ) + isoK8 β * (ψ * (1 + isoM2) + isoLbar2 β) / γ := by
      rw [hU1, add_div, hHdiv]
    have e4 : (isoKflat β + isoKsharp β * ψ) / γ = isoK8 β * (ψ * (1 + isoM2) + isoLbar2 β) / γ
        + (isoKexFlat β + isoKexSharp β * ψ) / γ := by
      unfold isoKflat isoKsharp
      rw [← add_div]
      congr 1
      ring
    rw [e4]
    linarith

/-! ## Integrated volatility at positive ridge -/

/--
`thm:app-iso-vol-ridge`, first display. Series index shifted as in the lemma above. The
The source's setup fact `ψ(ϱ) ∈ (0,γ)` is derived in the proof, not assumed. 

`thm:app-iso-vol-ridge`, snapshot `cr-2026-10-23`, `section.tex` l.3284-3294.

LaTeX (verbatim):
\begin{theorem}[Integrated volatility at positive ridge]\label{thm:app-iso-vol-ridge}
Let $\bmom\in(0,1)$, $\Nin=\Nout=N$, $\gamma=N/B\ge\gamma^\circ_\bmom$ and $\ridge>0$, and put
$\psi=\psi(\ridge)\in(0,\gamma)$. Then
\[
-\frac\psi\gamma\,\mathsf K^\circ_\bmom\le\sum_{\ell\ge1}\overline C_{1,\ell}(\ridge)-\frac\gamma2\,\mathcal P\Big(\frac\psi\gamma\Big)\le\frac{\mathsf K^\flat_\bmom+\mathsf K^\sharp_\bmom\psi}\gamma ,
\]
and the integrated volatility of \cref{thm:app-iso-volatility}(ii) satisfies
\[
-\frac{2\psi\,\mathsf K^\circ_\bmom}\gamma\le\frac{\mathfrak v_{\mathrm{iso}}(\ridge)}N-\frac\psi\gamma-\gamma\,\mathcal P\Big(\frac\psi\gamma\Big)\le\frac{2(\mathsf K^\flat_\bmom+\mathsf K^\sharp_\bmom\psi)}\gamma .
\]
\end{theorem}
-/
theorem thm_app_iso_vol_ridge_i {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : isoGammaCirc β ≤ γ) (hϱ : 0 < ϱ) :
    Summable (fun ℓ : ℕ => lagCoeff β γ ϱ (ℓ + 1)) ∧
      -(psiIso β γ γ ϱ / γ) * isoKcirc β ≤
          (∑' ℓ : ℕ, lagCoeff β γ ϱ (ℓ + 1)) - γ / 2 * isoCrossP (psiIso β γ γ ϱ / γ) ∧
      (∑' ℓ : ℕ, lagCoeff β γ ϱ (ℓ + 1)) - γ / 2 * isoCrossP (psiIso β γ γ ϱ / γ) ≤
          (isoKflat β + isoKsharp β * psiIso β γ γ ϱ) / γ := by
  exact rvr_main hβ0 hβ1 hγ hϱ

/--
`thm:app-iso-vol-ridge`, second display, in the explicit form `v_iso(ϱ)/N = isoVolRatio`
(see the file header). -/
theorem thm_app_iso_vol_ridge_ii {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : isoGammaCirc β ≤ γ) (hϱ : 0 < ϱ) :
    Summable (fun ℓ : ℕ => lagCoeff β γ ϱ (ℓ + 1)) ∧
      -2 * psiIso β γ γ ϱ * isoKcirc β / γ ≤
          isoVolRatio β γ ϱ - psiIso β γ γ ϱ / γ - γ * isoCrossP (psiIso β γ γ ϱ / γ) ∧
      isoVolRatio β γ ϱ - psiIso β γ γ ϱ / γ - γ * isoCrossP (psiIso β γ γ ϱ / γ) ≤
          2 * (isoKflat β + isoKsharp β * psiIso β γ γ ϱ) / γ := by
  obtain ⟨hs, hlo, hhi⟩ := rvr_main hβ0 hβ1 hγ hϱ
  refine ⟨hs, ?_, ?_⟩
  · have e : -2 * psiIso β γ γ ϱ * isoKcirc β / γ = 2 * (-(psiIso β γ γ ϱ / γ) * isoKcirc β) := by
      ring
    unfold isoVolRatio
    rw [e]; linarith
  · have e : 2 * (isoKflat β + isoKsharp β * psiIso β γ γ ϱ) / γ =
        2 * ((isoKflat β + isoKsharp β * psiIso β γ γ ϱ) / γ) := by ring
    unfold isoVolRatio
    rw [e]; linarith

private lemma rfix_log_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    -2 * x ≤ Real.log (1 - x) := by
  have hp : 0 < 1 - x := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hp
  have h1 : -2 * x ≤ 1 - (1 - x)⁻¹ := by
    have hdiv : 1 / (1 - x) ≤ 1 + 2 * x := (div_le_iff₀ hp).2 (by nlinarith)
    rw [inv_eq_one_div]
    linarith
  exact h1.trans h

private lemma rfix_root {β a b ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ) :
    0 < qIso β a b ρ ∧ 0 < psiIso β a b ρ ∧ psiIso β a b ρ < min a b ∧
      ρ * qIso β a b ρ = (a - psiIso β a b ρ) * (b - psiIso β a b ρ) := by
  have hr := rf6_isoLink hβ0 hβ1
  obtain ⟨hD, hG⟩ := (lem_app_iso_comparison_i hr ha hb).2.2.2.1 ρ hρ
  change 0 ≤ qIso β a b ρ ∧ psiIso β a b ρ < min a b at hD
  change ρ * qIso β a b ρ - (b - psiIso β a b ρ) * (a - psiIso β a b ρ) = 0 at hG
  have hq : 0 < qIso β a b ρ := by
    rcases hD.1.eq_or_lt with h | h
    · have hz : psiIso β a b ρ = 0 := by unfold psiIso; rw [← h]; exact hr.2.2
      rw [← h, hz] at hG
      nlinarith
    · exact h
  have hψ : 0 < psiIso β a b ρ := by
    have h := hr.2.1 (mem_Ici.mpr le_rfl) (mem_Ici.mpr hq.le) hq
    rw [hr.2.2] at h
    exact h
  exact ⟨hq, hψ, hD.2, by nlinarith⟩

private lemma rfix_count {β a b ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ)
    (hp0 : 0 ≤ isoPhat β a b ρ)
    (hp2 : isoPhat β a b ρ + isoC' β ≤ min a b / 2) :
    |psiIso β a b ρ - isoPhat β a b ρ| ≤
        isoEfix β (min a b) (isoPhat β a b ρ) ∧
      psiIso β a b ρ ≤ isoPhat β a b ρ + isoC' β := by
  have hL : 0 < Real.log (1 / β) := Real.log_pos ((lt_div_iff₀ hβ0).2 (by linarith))
  have hβ : 0 < 1 - β := by linarith
  have hc : 0 ≤ isoC β := by unfold isoC; positivity
  obtain ⟨hq, hH, hHg, hcl⟩ := rfix_root hβ0 hβ1 ha hb hρ
  set H := psiIso β a b ρ
  set q := qIso β a b ρ
  set p := isoPhat β a b ρ
  set g := min a b
  have hg : 0 < g := lt_min ha hb
  have hHa : 0 < a - H := by linarith [min_le_left a b]
  have hHb : 0 < b - H := by linarith [min_le_right a b]
  have hqa : q = (a - H) * (b - H) / ρ := (eq_div_iff hρ.ne').2 (by nlinarith [hcl])
  have hN : isoN β q = p +
      (Real.log (1 - H / a) + Real.log (1 - H / b)) / (2 * Real.log (1 / β)) := by
    have he : (1 - β) ^ 2 * q = ((1 - β) ^ 2 * a * b / ρ) * ((1 - H / a) * (1 - H / b)) := by
      rw [hqa]; field_simp
    have hxa : 0 < 1 - H / a := by rw [sub_pos, div_lt_one ha]; linarith
    have hxb : 0 < 1 - H / b := by rw [sub_pos, div_lt_one hb]; linarith
    unfold isoN
    rw [he, Real.log_mul (by positivity) (by positivity), Real.log_mul hxa.ne' hxb.ne', add_div]
    rfl
  have hNle : isoN β q ≤ p := by
    rw [hN]
    have h1 : Real.log (1 - H / a) ≤ 0 := Real.log_nonpos (by rw [sub_nonneg, div_le_one ha]; linarith) (by linarith [div_nonneg hH.le ha.le])
    have h2 : Real.log (1 - H / b) ≤ 0 := Real.log_nonpos (by rw [sub_nonneg, div_le_one hb]; linarith) (by linarith [div_nonneg hH.le hb.le])
    have : (Real.log (1 - H / a) + Real.log (1 - H / b)) / (2 * Real.log (1 / β)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith
  have hupper : H ≤ p + isoC' β := by
    by_cases hx : 1 ≤ (1 - β) ^ 2 * q
    · exact ((lem_app_iso_count_i hβ0 hβ1).1 q hx).2.trans (by linarith)
    · have hqq : q ≤ 1 / (1 - β) ^ 2 := (le_div_iff₀ (by positivity)).2 (by nlinarith [not_le.mp hx])
      have hr := rf6_isoLink hβ0 hβ1
      have hmono := hr.2.1.monotoneOn (mem_Ici.mpr hq.le) (mem_Ici.mpr (by positivity)) hqq
      exact hmono.trans ((lem_app_iso_count_i hβ0 hβ1).2.trans (by linarith))
  have hlowerN : isoN β q - isoC β ≤ H := by
    by_cases hx : 1 ≤ (1 - β) ^ 2 * q
    · exact ((lem_app_iso_count_i hβ0 hβ1).1 q hx).1.le
    · have hlog := Real.log_neg (mul_pos (sq_pos_of_pos hβ) hq) (not_le.mp hx)
      have hn : isoN β q ≤ 0 := div_nonpos_of_nonpos_of_nonneg hlog.le (by positivity)
      linarith
  have hHg2 : H ≤ g / 2 := hupper.trans hp2
  have hxg : H / g ≤ 1 / 2 := (div_le_iff₀ hg).2 (by linarith)
  have hga : H / a ≤ H / g := div_le_div_of_nonneg_left hH.le hg (min_le_left a b)
  have hgb : H / b ≤ H / g := div_le_div_of_nonneg_left hH.le hg (min_le_right a b)
  have hla := rfix_log_lower (div_nonneg hH.le ha.le) (hga.trans hxg)
  have hlb := rfix_log_lower (div_nonneg hH.le hb.le) (hgb.trans hxg)
  have hnlow : p - 2 * H / (Real.log (1 / β) * g) ≤ isoN β q := by
    rw [hN]
    have h : -4 * (H / g) ≤ Real.log (1 - H / a) + Real.log (1 - H / b) := by linarith
    have := div_le_div_of_nonneg_right h (by positivity : 0 ≤ 2 * Real.log (1 / β))
    have he : -4 * (H / g) / (2 * Real.log (1 / β)) = -(2 * H / (Real.log (1 / β) * g)) := by ring
    rw [he] at this
    linarith
  have hrat : 2 * H / (Real.log (1 / β) * g) ≤ 2 * (p + isoC' β) / (Real.log (1 / β) * g) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, hupper⟩
  · have he := le_max_right (isoC' β) (isoC β + 2 * (p + isoC' β) / (Real.log (1 / β) * g))
    change -max _ _ ≤ H - p
    linarith
  · exact (by linarith : H - p ≤ isoC' β).trans (le_max_left _ _)

private lemma rfix_W_bounds {a b H m : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hH : 0 ≤ H) (hHg : H ≤ min a b) (hm : 0 ≤ m) (hmH : m ≤ H) :
    Real.sqrt (a * b) * (1 - H / min a b) ≤ isoWm a b m ∧
      isoWm a b m ≤ Real.sqrt (a * b) := by
  have hg : 0 < min a b := lt_min ha hb
  have hx : 0 ≤ H / min a b := div_nonneg hH hg.le
  have hx1 : H / min a b ≤ 1 := (div_le_one hg).2 hHg
  have hcancel : min a b * (H / min a b) = H := by field_simp
  have h1 := mul_le_mul_of_nonneg_right (min_le_left a b) hx
  have h2 := mul_le_mul_of_nonneg_right (min_le_right a b) hx
  have ha' : a * (1 - H / min a b) ≤ a - m := by nlinarith
  have hb' : b * (1 - H / min a b) ≤ b - m := by nlinarith
  have ham : 0 ≤ a - m := by linarith [min_le_left a b]
  have hbm : 0 ≤ b - m := by linarith [min_le_right a b]
  have hs := Real.sq_sqrt (mul_pos ha hb).le
  constructor
  · unfold isoWm
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    have hmul := mul_le_mul ha' hb' (by positivity) ham
    calc (Real.sqrt (a * b) * (1 - H / min a b)) ^ 2
        = a * (1 - H / min a b) * (b * (1 - H / min a b)) := by
          rw [mul_pow, hs]; ring
      _ ≤ _ := hmul
  · unfold isoWm
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg hm (by linarith : 0 ≤ a + b - m)]

private lemma rfix_integral {a b H : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hH : 0 ≤ H) (hHg : H ≤ min a b) :
    H - H ^ 2 / min a b ≤ (∫ m in (0 : ℝ)..H, isoWm a b m) / Real.sqrt (a * b) ∧
      (∫ m in (0 : ℝ)..H, isoWm a b m) / Real.sqrt (a * b) ≤ H := by
  have hs : 0 < Real.sqrt (a * b) := Real.sqrt_pos.2 (mul_pos ha hb)
  have hint : IntervalIntegrable (isoWm a b) volume 0 H := by
    apply Continuous.intervalIntegrable
    unfold isoWm
    fun_prop
  have hlo := intervalIntegral.integral_mono_on hH intervalIntegrable_const hint
    (fun m hm => (rfix_W_bounds ha hb hH hHg hm.1 hm.2).1)
  have hhi := intervalIntegral.integral_mono_on hH hint intervalIntegrable_const
    (fun m hm => (rfix_W_bounds ha hb hH hHg hm.1 hm.2).2)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hlo hhi
  constructor
  · rw [le_div_iff₀ hs]
    convert hlo using 1 <;> ring
  · exact (div_le_iff₀ hs).2 (by simpa [mul_comm] using hhi)

/-! ## Fixed ridge -/

/-- `thm:app-iso-fixed-ridge`, drift and threshold (general aspect ratios). 

`thm:app-iso-fixed-ridge`, snapshot `cr-2026-10-23`, `section.tex` l.3440-3457.

LaTeX (verbatim):
\begin{theorem}[Fixed ridge, large aspect ratios]\label{thm:app-iso-fixed-ridge}
Let $\bmom\in(0,1)$, $\ridge>0$ and $\gin,\gout>0$, write $\widehat{\mathfrak p}=\widehat{\mathfrak p}_\bmom(\ridge)$,
and assume
\[
\widehat{\mathfrak p}\ge\frac{2\mathsf c'_\bmom}{\log(1/\bmom)\,\gamma_\wedge},\qquad
\widehat{\mathfrak p}+\mathsf c'_\bmom\le\frac{\gamma_\wedge}2 .
\]
Put $e_\bmom\defeq\max\big(\mathsf c'_\bmom,\ \mathsf c_\bmom+2(\widehat{\mathfrak p}+\mathsf c'_\bmom)/(\log(1/\bmom)\gamma_\wedge)\big)$. Then
\[
\big|\psi(\ridge)-\widehat{\mathfrak p}\big|\le e_\bmom,\qquad
\Big|\sqrt{\gin\gout}\;\mathfrak d_{\mathrm{iso}}(\ridge)-\frac{\widehat{\mathfrak p}}{\sqrt\pi}\Big|
\le\frac1{\sqrt\pi}\Big(e_\bmom+\frac{(\widehat{\mathfrak p}+\mathsf c'_\bmom)^2}{\gamma_\wedge}\Big)+\frac{2.32}{1-\bmom}.
\]
If moreover $\Nin=\Nout=N$ and $\gamma=N/B$, then
\[
\mathfrak v_{\mathrm{iso}}(\ridge)\ge B\,\psi(\ridge)+\mathsf k_\bmom B\Big(1-\frac{\psi(\ridge)}\gamma\Big)^2\big(\psi(\ridge)-\mathsf c''_\bmom-\mathsf c'_\bmom-1\big)_+^2 .
\]
\end{theorem}
-/
theorem thm_app_iso_fixed_ridge_i {β γin γout ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hin : 0 < γin) (hout : 0 < γout) (hϱ : 0 < ϱ)
    (hp1 : 2 * isoC' β / (Real.log (1 / β) * min γin γout) ≤ isoPhat β γin γout ϱ)
    (hp2 : isoPhat β γin γout ϱ + isoC' β ≤ min γin γout / 2) :
    |psiIso β γin γout ϱ - isoPhat β γin γout ϱ|
        ≤ isoEfix β (min γin γout) (isoPhat β γin γout ϱ) ∧
      |Real.sqrt (γin * γout) * dIso β γin γout ϱ - isoPhat β γin γout ϱ / Real.sqrt Real.pi|
        ≤ 1 / Real.sqrt Real.pi *
              (isoEfix β (min γin γout) (isoPhat β γin γout ϱ)
                + (isoPhat β γin γout ϱ + isoC' β) ^ 2 / min γin γout)
            + 2.32 / (1 - β) := by
  have hL : 0 < Real.log (1 / β) := Real.log_pos ((lt_div_iff₀ hβ0).2 (by linarith))
  have hg : 0 < min γin γout := lt_min hin hout
  have hc' : 0 ≤ isoC' β := by
    have : 0 < 1 - β ^ 2 := by nlinarith
    unfold isoC'; positivity
  have hp0 : 0 ≤ isoPhat β γin γout ϱ :=
    (div_nonneg (by positivity) (by positivity)).trans hp1
  obtain ⟨hcount, hupper⟩ := rfix_count hβ0 hβ1 hin hout hϱ hp0 hp2
  refine ⟨hcount, ?_⟩
  obtain ⟨-, hH, hHg, -⟩ := rfix_root hβ0 hβ1 hin hout hϱ
  obtain ⟨hlo, hhi⟩ := rfix_integral hin hout hH.le hHg.le
  set I := ∫ m in (0 : ℝ)..psiIso β γin γout ϱ, isoWm γin γout m
  set s := Real.sqrt (γin * γout)
  set t := Real.sqrt Real.pi
  have hs : 0 < s := Real.sqrt_pos.2 (mul_pos hin hout)
  have ht : 0 < t := Real.sqrt_pos.2 Real.pi_pos
  have hs2 : s ^ 2 = γin * γout := Real.sq_sqrt (mul_pos hin hout).le
  have hsq : psiIso β γin γout ϱ ^ 2 ≤ (isoPhat β γin γout ϱ + isoC' β) ^ 2 :=
    pow_le_pow_left₀ hH.le hupper 2
  have hdist : |I / s - isoPhat β γin γout ϱ| ≤
      isoEfix β (min γin γout) (isoPhat β γin γout ϱ) +
        (isoPhat β γin γout ϱ + isoC' β) ^ 2 / min γin γout := by
    have hd := div_le_div_of_nonneg_right hsq hg.le
    obtain ⟨hc1, hc2⟩ := abs_le.mp hcount
    apply abs_le.mpr
    constructor <;> linarith [sq_nonneg (isoPhat β γin γout ϱ + isoC' β),
      div_nonneg (sq_nonneg (isoPhat β γin γout ϱ + isoC' β)) hg.le]
  have hm := (thm_app_iso_master_i hβ0 hβ1 hin hout hϱ.le).1.trans
    (thm_app_iso_master_i hβ0 hβ1 hin hout hϱ.le).2.le
  rw [isoMLevel, if_neg hϱ.ne'] at hm
  have he : s * (1 / (Real.sqrt Real.pi * γin * γout) * I) = I / s / t := by
    apply (eq_div_iff ht.ne').2
    apply (eq_div_iff hs.ne').2
    dsimp [t]
    field_simp
    rw [hs2]
  have hm' := mul_le_mul_of_nonneg_left hm hs.le
  rw [show s = |s| from (abs_of_pos hs).symm, ← abs_mul] at hm'
  rw [abs_of_pos hs] at hm'
  have he2 : s * (2.32 / ((1 - β) * s)) = 2.32 / (1 - β) := by field_simp
  change |s * (dIso β γin γout ϱ - 1 / (Real.sqrt Real.pi * γin * γout) * I)| ≤ _ at hm'
  change |s * (dIso β γin γout ϱ - 1 / (Real.sqrt Real.pi * γin * γout) * I)| ≤ s * (2.32 / ((1 - β) * s)) at hm'
  rw [mul_sub, he, he2] at hm'
  have hd := div_le_div_of_nonneg_right hdist ht.le
  rw [← abs_of_pos ht, ← abs_div, sub_div, abs_of_pos ht] at hd
  calc |s * dIso β γin γout ϱ - isoPhat β γin γout ϱ / t|
      ≤ |s * dIso β γin γout ϱ - I / s / t| + |I / s / t - isoPhat β γin γout ϱ / t| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hm' hd
    _ = _ := by ring

private lemma rfix_q_bound {β γ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < γ) (hρ : 0 < ρ) (x : ℝ) :
    0 ≤ qIso β γ γ (ρ + x ^ 2) ∧
      qIso β γ γ (ρ + x ^ 2) ≤ qIso β γ γ ρ ∧
      qIso β γ γ (ρ + x ^ 2) ≤ (qIso β γ γ ρ + γ ^ 2) * (1 + x ^ 2)⁻¹ := by
  obtain ⟨hq, hψ, hψγ, he⟩ := rfix_root hβ0 hβ1 hγ hγ (by positivity : 0 < ρ + x ^ 2)
  rw [min_self] at hψγ
  have hanti := (lem_app_iso_comparison_i (rf6_isoLink hβ0 hβ1) hγ hγ).2.2.2.2.2
  have hqQ : qIso β γ γ (ρ + x ^ 2) ≤ qIso β γ γ ρ :=
    hanti.antitoneOn (by exact hρ) (by change 0 < ρ + x ^ 2; positivity) (by nlinarith)
  refine ⟨hq.le, hqQ, ?_⟩
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + x ^ 2)]
  nlinarith [mul_nonneg hρ.le hq.le]

private lemma rfix_lag_summable {β γ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < γ) (hρ : 0 < ρ) :
    Summable (fun ℓ : ℕ => lagCoeff β γ ρ (ℓ + 1)) := by
  let Q := qIso β γ γ ρ
  let A := Q + γ ^ 2
  let S := Muon.sPow β 2
  let T := Muon.sPow β 4
  have hQ : 0 < Q := (rfix_root hβ0 hβ1 hγ hγ hρ).1
  have hS : 0 ≤ S := by dsimp [S]; rw [Muon.sPow_two hβ0.le hβ1]; positivity
  have hT : 0 ≤ T := by dsimp [T]; unfold Muon.sPow; positivity
  have hpow : Tendsto (fun ℓ : ℕ => β ^ (ℓ + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp (tendsto_add_atTop_nat 1)
  have hX : Tendsto (fun ℓ : ℕ => Q ^ 2 * (3 * β ^ (2 * (ℓ + 1)) * T) / γ)
      atTop (𝓝 0) := by
    have hh := ((hpow.pow 2).const_mul (Q ^ 2 * 3 * T)).div_const γ
    convert hh using 1
    · funext ℓ; rw [pow_mul]; ring
    · simp
  have hZ : Tendsto (fun ℓ : ℕ => Q * (β ^ (ℓ + 1) * S) / γ) atTop (𝓝 0) := by
    convert ((hpow.const_mul (Q * S)).div_const γ) using 1
    · funext ℓ; ring
    · simp
  let f : ℝ → ℝ := fun x => A * (1 + x ^ 2)⁻¹
  let I := ∫ x in Ioi (0 : ℝ), f x
  have hf : IntegrableOn f (Ioi 0) := (integrable_inv_one_add_sq.const_mul A).integrableOn
  have hf0 : ∀ x, 0 ≤ f x := fun x => by dsimp [f, A]; positivity
  have hI : 0 ≤ I := integral_nonneg (fun x => hf0 x)
  have hs : Summable (fun ℓ : ℕ =>
      (4 / Real.pi ^ 2 * (2 * S / γ ^ 3) * I ^ 2) * β ^ (ℓ + 1)) :=
    ((summable_geometric_of_lt_one hβ0.le hβ1).comp_injective (fun a b h => by omega)).mul_left _
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [hX.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/4)),
    hZ.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/4))] with ℓ hx hz
  let C := 2 * β ^ (ℓ + 1) * S / γ ^ 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hkernel : ∀ x y : ℝ, 0 ≤ lagKernel β γ (ℓ + 1) (ρ + x ^ 2) (ρ + y ^ 2) ∧
      lagKernel β γ (ℓ + 1) (ρ + x ^ 2) (ρ + y ^ 2) ≤ C * f x * f y := by
    intro x y
    obtain ⟨hqx, hqxQ, hqxf⟩ := rfix_q_bound hβ0 hβ1 hγ hρ x
    obtain ⟨hqy, hqyQ, hqyf⟩ := rfix_q_bound hβ0 hβ1 hγ hρ y
    obtain ⟨⟨hb0, hb⟩, ⟨he0, he⟩, ⟨hx0, -⟩, hd0, -⟩ :=
      lem_app_iso_lag_i hβ0 hβ1 hγ (by positivity : 0 < ρ + x ^ 2)
        (by positivity : 0 < ρ + y ^ 2) (ℓ + 1)
    have hqq : qIso β γ γ (ρ + x ^ 2) * qIso β γ γ (ρ + y ^ 2) ≤ Q ^ 2 := by
      nlinarith [mul_le_mul hqxQ hqyQ hqy hQ.le]
    have hxx : isoLagX β γ (ℓ + 1) (ρ + x ^ 2) (ρ + y ^ 2) ≤ 1/4 := by
      unfold isoLagX
      exact (div_le_div_of_nonneg_right (mul_le_mul hqq he he0 (sq_nonneg Q)) hγ.le).trans hx.le
    have hzz0 : 0 ≤ isoLagZ β γ (ℓ + 1) (ρ + x ^ 2) (ρ + y ^ 2) := by
      unfold isoLagZ; positivity
    have hzz : isoLagZ β γ (ℓ + 1) (ρ + x ^ 2) (ρ + y ^ 2) ≤ 1/4 := by
      have hsqrt : Real.sqrt (qIso β γ γ (ρ + x ^ 2) * qIso β γ γ (ρ + y ^ 2)) ≤ Q :=
        (Real.sqrt_le_iff).2 ⟨hQ.le, hqq⟩
      unfold isoLagZ
      exact (div_le_div_of_nonneg_right (mul_le_mul hsqrt hb hb0 hQ.le) hγ.le).trans hz.le
    have hd : 1/2 ≤ isoLagDelta β γ (ℓ + 1) (ρ + x ^ 2) (ρ + y ^ 2) := by
      unfold isoLagDelta
      nlinarith
    constructor
    · unfold lagKernel; positivity
    · have hnum := mul_le_mul (mul_le_mul hb hqxf hqx (by positivity)) hqyf hqy (by positivity)
      dsimp [f, A, Q] at hnum ⊢
      unfold lagKernel
      apply (div_le_div₀ (by positivity) hnum (by positivity)
        (mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ γ ^ 3))).trans_eq
      dsimp [C, S]
      field_simp
      <;> ring
  have hinner : ∀ x : ℝ, (∫ y in Ioi (0:ℝ), lagKernel β γ (ℓ + 1) (ρ + x ^ 2) (ρ + y ^ 2))
      ≤ C * f x * I := by
    intro x
    have hh := integral_mono_of_nonneg (ae_of_all _ (fun y => (hkernel x y).1))
      (hf.const_mul (C * f x)) (ae_of_all _ (fun y => (hkernel x y).2))
    simpa only [integral_const_mul, I] using hh
  have houter := integral_mono_of_nonneg
    (ae_of_all _ (fun x => integral_nonneg (fun y => (hkernel x y).1)))
    ((hf.const_mul C).mul_const I) (ae_of_all _ hinner)
  rw [Real.norm_eq_abs, abs_of_nonneg (rvr_lag_nonneg hβ0 hβ1 hγ hρ.le (ℓ + 1))]
  unfold lagCoeff
  apply (mul_le_mul_of_nonneg_left houter (by positivity : 0 ≤ 4 / Real.pi ^ 2)).trans_eq
  simp only [integral_mul_const, integral_const_mul]
  dsimp [C, I]
  ring

private lemma rfix_triangle (X : ℝ) :
    ∃ n : ℕ, (max (X - 1) 0) ^ 2 / 2 ≤
      ∑ ℓ ∈ Finset.range n, max (X - ((ℓ : ℝ) + 1)) 0 := by
  by_cases hX : X ≤ 1
  · refine ⟨0, ?_⟩
    simp [max_eq_right (by linarith : X - 1 ≤ 0)]
  obtain ⟨n, -, -, hn⟩ := rvr_n X
  obtain ⟨hn1, hn2⟩ := hn (by linarith)
  refine ⟨n, le_trans ?_ (Finset.sum_le_sum (fun ℓ _ => le_max_left _ _))⟩
  rw [rvr_sumrange, max_eq_left (by linarith : 0 ≤ X - 1)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hn2) (sub_nonneg.mpr hn1.le)]

private lemma rfix_k_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 ≤ isoKk β := by
  have hb : 0 < 1 - β ^ 2 := by nlinarith
  have he : 0 ≤ Real.exp 2 - 1 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hb1 : 0 < 1 - β := by linarith
  have hΦ : 0 < isoPhiDeriv 1 := (lem_app_iso_gaussian_ii.2.1 1 one_pos).2.1
  have hEm : 0 ≤ isoEminus β := by unfold isoEminus; positivity
  have hEp : 0 < isoEplus β := by unfold isoEplus; positivity
  unfold isoKk
  positivity

/--
`thm:app-iso-fixed-ridge`, volatility lower bound in the square case `γin = γout = N/B`,
in the explicit form `v_iso(ϱ) = N · isoVolRatio`. -/
theorem thm_app_iso_fixed_ridge_ii {β ϱ N B : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hϱ : 0 < ϱ) (hN : 0 < N) (hB : 0 < B)
    (hp1 : 2 * isoC' β / (Real.log (1 / β) * (N / B))
      ≤ isoPhat β (N / B) (N / B) ϱ)
    (hp2 : isoPhat β (N / B) (N / B) ϱ + isoC' β ≤ (N / B) / 2) :
    Summable (fun ℓ : ℕ => lagCoeff β (N / B) ϱ (ℓ + 1)) ∧
      B * psiIso β (N / B) (N / B) ϱ
          + isoKk β * B * (1 - psiIso β (N / B) (N / B) ϱ / (N / B)) ^ 2
              * (max (psiIso β (N / B) (N / B) ϱ - isoCpp β - isoC' β - 1) 0) ^ 2
        ≤ N * isoVolRatio β (N / B) ϱ := by
  let γ := N / B
  let H := psiIso β γ γ ϱ
  let D := isoKk β / γ ^ 3 * (γ - H) ^ 2
  have hγ : 0 < γ := div_pos hN hB
  have hD : 0 ≤ D := mul_nonneg (div_nonneg (rfix_k_nonneg hβ0 hβ1) (by positivity)) (sq_nonneg _)
  have hs := rfix_lag_summable hβ0 hβ1 hγ hϱ
  refine ⟨hs, ?_⟩
  obtain ⟨n, hn⟩ := rfix_triangle (H - isoCpp β - isoC' β)
  have ht : ∀ ℓ : ℕ, D * max (H - isoCpp β - isoC' β - ((ℓ : ℝ) + 1)) 0 ≤
      lagCoeff β γ ϱ (ℓ + 1) := by
    intro ℓ
    have hh := (lem_app_iso_lag_lower_ii hβ0 hβ1 hγ hϱ (by omega : 1 ≤ ℓ + 1)).trans
      (lem_app_iso_lag_lower_i hβ0 hβ1 hγ hϱ.le (by omega : 1 ≤ ℓ + 1))
    simpa only [isoLagPsi, if_neg hϱ.ne', Nat.cast_add, Nat.cast_one,
      show H - isoCpp β - isoC' β - (↑ℓ + 1) = H - (↑ℓ + 1) - isoCpp β - isoC' β by ring,
      H, D] using hh
  have hsum := (Finset.sum_le_sum (fun ℓ (_ : ℓ ∈ Finset.range n) => ht ℓ)).trans
    (hs.sum_le_tsum (Finset.range n) (fun ℓ _ => rvr_lag_nonneg hβ0 hβ1 hγ hϱ.le (ℓ + 1)))
  rw [← Finset.mul_sum] at hsum
  have hmain := (mul_le_mul_of_nonneg_left hn hD).trans hsum
  have he : isoKk β * B * (1 - H / γ) ^ 2 = N * D := by
    dsimp [D, γ]
    field_simp
    <;> ring
  change B * H + isoKk β * B * (1 - H / γ) ^ 2 * (max (H - isoCpp β - isoC' β - 1) 0) ^ 2 ≤ _
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left hmain (by positivity : 0 ≤ 2 * N)
  have hNH : N * (H / γ) = B * H := by dsimp [γ]; field_simp; <;> ring
  change _ ≤ N * (H / γ + 2 * ∑' ℓ : ℕ, lagCoeff β γ ϱ (ℓ + 1))
  rw [mul_add, hNH]
  have hmul' : N * D * (max (H - isoCpp β - isoC' β - 1) 0) ^ 2 ≤
      N * (2 * ∑' ℓ : ℕ, lagCoeff β γ ϱ (ℓ + 1)) := by
    convert hmul using 1 <;> ring
  convert add_le_add_right hmul' (B * H) using 1 <;> congr 1 <;> ring

private lemma rfix_regime {α : Type*} {l : Filter α} {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (g p : α → ℝ)
    (hg : Tendsto g l atTop) (hp : Tendsto p l atTop)
    (hpg : Tendsto (fun x => p x / g x) l (𝓝 0)) :
    ∃ C : ℝ, ∀ᶠ x in l,
      2 * isoC' β / (Real.log (1 / β) * g x) ≤ p x ∧
      p x + isoC' β ≤ g x / 2 ∧ isoEfix β (g x) (p x) ≤ C := by
  have hL : 0 < Real.log (1 / β) := Real.log_pos ((lt_div_iff₀ hβ0).2 (by linarith))
  have hc : Tendsto (fun x => isoC' β / g x) l (𝓝 0) := tendsto_const_nhds.div_atTop hg
  have ht : Tendsto (fun x => 2 * isoC' β / (Real.log (1 / β) * g x)) l (𝓝 0) := by
    convert hc.const_mul (2 / Real.log (1 / β)) using 1 <;> first | (funext x; ring) | simp
  have hsum : Tendsto (fun x => (p x + isoC' β) / g x) l (𝓝 0) := by
    simpa only [add_div, zero_add, add_zero] using hpg.add hc
  refine ⟨max (isoC' β) (isoC β + 2 / Real.log (1 / β)), ?_⟩
  filter_upwards [hg.eventually_gt_atTop 0, hp.eventually_ge_atTop 1,
    ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hsum.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with x hx hx1 ht1 hs
  refine ⟨by linarith, (by linarith [(div_le_iff₀ hx).1 (by linarith : (p x + isoC' β) / g x ≤ 1 / 2)]), ?_⟩
  unfold isoEfix
  apply max_le (le_max_left _ _)
  apply le_trans _ (le_max_right _ _)
  have h : 2 * (p x + isoC' β) / (Real.log (1 / β) * g x) ≤ 2 / Real.log (1 / β) := by
    calc _ = 2 / Real.log (1 / β) * ((p x + isoC' β) / g x) := by ring
      _ ≤ 2 / Real.log (1 / β) * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := mul_one _
  linarith

/-- `cor:app-iso-fixed-ridge`(i). Explicit sequences `ℕ → ℝ` replace the filter on triples
(`section.tex` l.3505–3510). "∼" is `IsEquivalent` along `atTop`; "stays bounded" is an
eventual uniform bound. 

`cor:app-iso-fixed-ridge`, snapshot `cr-2026-10-23`, `section.tex` l.3502-3522.

LaTeX (verbatim):
\begin{corollary}[Fixed-ridge laws]\label{cor:app-iso-fixed-ridge}
Let $\bmom\in(0,1)$.
\begin{enumerate}[label=(\roman*)]
\item Along $\gamma_\wedge\to\infty$ and $\ridge>0$ with $\widehat{\mathfrak p}_\bmom(\ridge)\to\infty$ and
$\widehat{\mathfrak p}_\bmom(\ridge)/\gamma_\wedge\to0$,
\[
\mathfrak d_{\mathrm{iso}}(\ridge)\sim\frac{\log\big((1-\bmom)^2\gin\gout/\ridge\big)}{2\sqrt\pi\,\log(1/\bmom)\,\sqrt{\gin\gout}},
\]
and $\psi(\ridge)-\widehat{\mathfrak p}_\bmom(\ridge)$ stays bounded.
\item In the square case, for fixed $\ridge>0$, the quantity
\[
\gamma\,\mathfrak d_{\mathrm{iso}}(\ridge)-\frac1{\sqrt\pi}\Big[\mathfrak p_\bmom(\ridge)+\frac{\log((1-\bmom)\gamma)}{\log(1/\bmom)}\Big]
\]
stays bounded as $\gamma\to\infty$. In particular $\gamma\,\mathfrak d_{\mathrm{iso}}(\ridge)\to\infty$.
\item In the square case, along $\gamma\to\infty$ and $\ridge>0$ with $\psi(\ridge)\to\infty$ and
$\psi(\ridge)/\gamma\to0$, and in particular at a fixed $\ridge>0$,
\[
\mathfrak v_{\mathrm{iso}}(\ridge)=B\,\psi(\ridge)^2\Big(1+O_\bmom\Big(\frac1{\psi(\ridge)}+\frac{\psi(\ridge)}\gamma\Big)\Big).
\]
\end{enumerate}
\end{corollary}
-/
theorem cor_app_iso_fixed_ridge_i {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (gin gout ϱ : ℕ → ℝ) (hin : ∀ n, 0 < gin n) (hout : ∀ n, 0 < gout n)
    (hϱ : ∀ n, 0 < ϱ n)
    (hg : Tendsto (fun n => min (gin n) (gout n)) atTop atTop)
    (hp : Tendsto (fun n => isoPhat β (gin n) (gout n) (ϱ n)) atTop atTop)
    (hpg : Tendsto (fun n => isoPhat β (gin n) (gout n) (ϱ n) / min (gin n) (gout n))
      atTop (𝓝 0)) :
    IsEquivalent atTop (fun n => dIso β (gin n) (gout n) (ϱ n))
        (fun n => isoPhat β (gin n) (gout n) (ϱ n) /
          (Real.sqrt Real.pi * Real.sqrt (gin n * gout n))) ∧
      ∃ C : ℝ, ∀ᶠ n in atTop,
        |psiIso β (gin n) (gout n) (ϱ n) - isoPhat β (gin n) (gout n) (ϱ n)| ≤ C := by
  let p := fun n => isoPhat β (gin n) (gout n) (ϱ n)
  let g := fun n => min (gin n) (gout n)
  let t := Real.sqrt Real.pi
  let s := fun n => Real.sqrt (gin n * gout n)
  have ht : 0 < t := Real.sqrt_pos.2 Real.pi_pos
  obtain ⟨C, hreg⟩ := rfix_regime hβ0 hβ1 g p hg hp hpg
  have hbounds : ∀ᶠ n in atTop,
      |psiIso β (gin n) (gout n) (ϱ n) - p n| ≤ C ∧
      |s n * dIso β (gin n) (gout n) (ϱ n) - p n / t| ≤
        (C + (p n + isoC' β) ^ 2 / g n) / t + 2.32 / (1 - β) := by
    filter_upwards [hreg] with n hn
    obtain ⟨hc, hd⟩ := thm_app_iso_fixed_ridge_i hβ0 hβ1 (hin n) (hout n) (hϱ n) hn.1 hn.2.1
    refine ⟨hc.trans hn.2.2, hd.trans ?_⟩
    change 1 / t * (isoEfix β (g n) (p n) + (p n + isoC' β) ^ 2 / g n) + _ ≤ _
    have hh := div_le_div_of_nonneg_right (add_le_add_right hn.2.2 ((p n + isoC' β) ^ 2 / g n)) ht.le
    simpa only [div_eq_mul_inv, one_mul, mul_comm, add_comm, mul_add] using
      add_le_add_right hh (2.32 / (1 - β))
  refine ⟨?_, C, hbounds.mono (fun _ h => h.1)⟩
  have hcp : Tendsto (fun n => isoC' β / p n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hp
  have hcg : Tendsto (fun n => isoC' β / g n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hg
  have hpp : Tendsto (fun n => (p n + isoC' β) / p n) atTop (𝓝 1) := by
    have he : (fun n => (p n + isoC' β) / p n) =ᶠ[atTop] (fun n => 1 + isoC' β / p n) := by
      filter_upwards [hp.eventually_gt_atTop 0] with n hn
      change 0 < p n at hn
      simp [add_div, hn.ne']
    exact (tendsto_congr' he).2 (by simpa using tendsto_const_nhds.add hcp)
  have hsum : Tendsto (fun n => (p n + isoC' β) / g n) atTop (𝓝 0) := by
    simpa [add_div] using hpg.add hcg
  have hq : Tendsto (fun n => (p n + isoC' β) ^ 2 / g n / p n) atTop (𝓝 0) := by
    convert hsum.mul hpp using 1
    · funext n; ring
    · simp
  have hC : Tendsto (fun n => C / p n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hp
  have hk : Tendsto (fun n => (2.32 / (1 - β)) / p n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hp
  have hB : Tendsto (fun n => ((C + (p n + isoC' β) ^ 2 / g n) / t + 2.32 / (1 - β)) / p n)
      atTop (𝓝 0) := by
    convert ((hC.add hq).div_const t).add hk using 1
    · funext n; ring
    · simp
  have herr : Tendsto (fun n => (s n * dIso β (gin n) (gout n) (ϱ n) - p n / t) / p n)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hB
    filter_upwards [hbounds, hp.eventually_gt_atTop 0] with n hn hpn
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpn]
    exact div_le_div_of_nonneg_right hn.2 hpn.le
  apply isEquivalent_of_tendsto_one
  have hlim := (herr.const_mul t).add_const 1
  have he : (fun n => dIso β (gin n) (gout n) (ϱ n) / (p n / (t * s n))) =ᶠ[atTop]
      (fun n => t * ((s n * dIso β (gin n) (gout n) (ϱ n) - p n / t) / p n) + 1) := by
    filter_upwards [hp.eventually_gt_atTop 0] with n hn
    have hs : 0 < s n := Real.sqrt_pos.2 (mul_pos (hin n) (hout n))
    change 0 < p n at hn
    field_simp [hn.ne', ht.ne', hs.ne']
    <;> ring
  exact (tendsto_congr' he).2 (by simpa using hlim)

private lemma rfix_square_formula {β γ ρ : ℝ} (hβ : β < 1) (hγ : 0 < γ) (hρ : 0 < ρ) :
    isoPhat β γ γ ρ = isoPfrak β ρ + Real.log ((1 - β) * γ) / Real.log (1 / β) := by
  have hb : 0 < 1 - β := by linarith
  have he : Real.log ((1 - β) ^ 2 * γ * γ / ρ) =
      2 * Real.log (1 - β) + 2 * Real.log γ - Real.log ρ := by
    rw [Real.log_div (by positivity) hρ.ne', Real.log_mul (by positivity) hγ.ne',
      Real.log_mul (by positivity) hγ.ne', Real.log_pow]
    norm_num
    ring
  unfold isoPhat isoPfrak
  rw [he, one_div ρ, Real.log_inv, Real.log_mul hb.ne' hγ.ne']
  ring

/--
`cor:app-iso-fixed-ridge`(ii), square case at fixed `ϱ > 0`. The bound holds for all large
`γ` with an absolute constant depending on `β` and `ϱ`. -/
theorem cor_app_iso_fixed_ridge_ii {β ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϱ : 0 < ϱ) :
    Tendsto (fun γ : ℝ => γ * dIso β γ γ ϱ) atTop atTop ∧
      ∃ C : ℝ, ∀ᶠ γ in atTop,
        |γ * dIso β γ γ ϱ
            - (isoPfrak β ϱ + Real.log ((1 - β) * γ) / Real.log (1 / β)) / Real.sqrt Real.pi|
          ≤ C := by
  let L := Real.log (1 / β)
  let K := isoPfrak β ϱ + Real.log (1 - β) / L
  let p := fun γ => isoPhat β γ γ ϱ
  let t := Real.sqrt Real.pi
  have hL : 0 < L := Real.log_pos ((lt_div_iff₀ hβ0).2 (by linarith))
  have ht : 0 < t := Real.sqrt_pos.2 Real.pi_pos
  have hform : ∀ᶠ γ : ℝ in atTop, p γ = Real.log γ / L + K := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with γ hγ
    dsimp [p, K]
    rw [rfix_square_formula hβ1 hγ hϱ,
      Real.log_mul (by linarith : 0 < 1 - β).ne' hγ.ne']
    dsimp [L]
    ring
  have hp : Tendsto p atTop atTop := by
    apply (tendsto_congr' hform).2
    exact tendsto_atTop_add_const_right _ K (Real.tendsto_log_atTop.atTop_div_const hL)
  have hl1 : Tendsto (fun γ : ℝ => Real.log γ / γ) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hl2 : Tendsto (fun γ : ℝ => Real.log γ ^ 2 / γ) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hK : Tendsto (fun γ : ℝ => K / γ) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hpg : Tendsto (fun γ : ℝ => p γ / γ) atTop (𝓝 0) := by
    have he : (fun γ : ℝ => p γ / γ) =ᶠ[atTop] (fun γ => Real.log γ / γ / L + K / γ) := by
      filter_upwards [hform] with γ hγ
      rw [hγ]; ring
    apply (tendsto_congr' he).2
    simpa using (hl1.div_const L).add hK
  have hquad : Tendsto (fun γ : ℝ => (p γ + isoC' β) ^ 2 / γ) atTop (𝓝 0) := by
    have hconst : Tendsto (fun γ : ℝ => (K + isoC' β) ^ 2 / γ) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hlim := ((hl2.div_const (L ^ 2)).add
      (hl1.const_mul (2 * (K + isoC' β) / L))).add hconst
    have he : (fun γ : ℝ => (p γ + isoC' β) ^ 2 / γ) =ᶠ[atTop]
        (fun γ => Real.log γ ^ 2 / γ / L ^ 2 +
          2 * (K + isoC' β) / L * (Real.log γ / γ) + (K + isoC' β) ^ 2 / γ) := by
      filter_upwards [hform] with γ hγ
      rw [hγ]; ring
    exact (tendsto_congr' he).2 (by simpa using hlim)
  obtain ⟨C, hreg⟩ := rfix_regime hβ0 hβ1 (fun γ : ℝ => γ) p tendsto_id hp hpg
  let D := (C + 1) / t + 2.32 / (1 - β)
  have hbnd : ∀ᶠ γ : ℝ in atTop, |γ * dIso β γ γ ϱ - p γ / t| ≤ D := by
    filter_upwards [hreg, eventually_gt_atTop (0 : ℝ),
      hquad.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with γ hγ hγ0 hq
    have hh := (thm_app_iso_fixed_ridge_i hβ0 hβ1 hγ0 hγ0 hϱ
      (by simpa only [min_self] using hγ.1) (by simpa only [min_self] using hγ.2.1)).2
    rw [Real.sqrt_mul_self hγ0.le, min_self] at hh
    have hh1 : isoEfix β γ (p γ) + (p γ + isoC' β) ^ 2 / γ ≤ C + 1 := by linarith [hγ.2.2]
    have hh2 := div_le_div_of_nonneg_right hh1 ht.le
    change |γ * dIso β γ γ ϱ - p γ / t| ≤ _ at hh
    apply hh.trans
    change 1 / t * (isoEfix β γ (p γ) + (p γ + isoC' β) ^ 2 / γ) + _ ≤ _
    change 1 / t * (isoEfix β γ (p γ) + (p γ + isoC' β) ^ 2 / γ) + _ ≤ (C + 1) / t + _
    simpa only [div_eq_mul_inv, one_mul, mul_comm, add_comm] using
      add_le_add_right hh2 (2.32 / (1 - β))
  refine ⟨?_, D, ?_⟩
  · apply tendsto_atTop_mono' atTop _
      (tendsto_atTop_add_const_right _ (-D) (hp.atTop_div_const ht))
    filter_upwards [hbnd] with γ hγ
    linarith [(abs_le.mp hγ).1]
  · filter_upwards [hbnd, eventually_gt_atTop (0 : ℝ)] with γ hγ hγ0
    simpa only [p, t, rfix_square_formula hβ1 hγ0 hϱ] using hγ

private lemma rfix_cross_error {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1 / 2) :
    |isoCrossP x - x ^ 2| ≤ 2 * x ^ 3 := by
  have hxx : x < 1 := by linarith
  have hcont := rvF_H_cont (γ := 1) hxx
  have hint : IntervalIntegrable (rvH 1 x) volume 0 x :=
    hcont.intervalIntegrable_of_Icc hx.le
  have hpoint : ∀ η ∈ Icc (0:ℝ) x,
      x - η - x ^ 2 ≤ rvH 1 x η ∧ rvH 1 x η ≤ x - η := by
    intro η hη
    have hη0 := hη.1
    have hηx := hη.2
    have hd : 0 < 2 * (1 - η) := by linarith [hη.2]
    have he : rvH 1 x η = (x - η) - (x - η) ^ 2 / (2 * (1 - η)) := by
      unfold rvH
      field_simp
      <;> ring
    have hq : (x - η) ^ 2 / (2 * (1 - η)) ≤ x ^ 2 := by
      apply (div_le_iff₀ hd).2
      have hs : (x - η) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      nlinarith [mul_nonneg (sq_nonneg x) (by linarith [hη.2] : 0 ≤ 1 - 2 * η)]
    rw [he]
    constructor
    · linarith
    · exact sub_le_self _ (by positivity)
  have hlo := intervalIntegral.integral_mono_on hx.le
    (by exact (show Continuous (fun η : ℝ => x - η - x ^ 2) by fun_prop).intervalIntegrable 0 x) hint (fun η hη => (hpoint η hη).1)
  have hhi := intervalIntegral.integral_mono_on hx.le hint
    (by exact (show Continuous (fun η : ℝ => x - η) by fun_prop).intervalIntegrable 0 x) (fun η hη => (hpoint η hη).2)
  have hpoly : (∫ η in (0:ℝ)..x, x - η) = x ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => x) (g := fun η : ℝ => η)
      intervalIntegrable_const (continuous_id.intervalIntegrable 0 x)]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, integral_id]
    ring
  have hpoly2 : (∫ η in (0:ℝ)..x, x - η - x ^ 2) = x ^ 2 / 2 - x ^ 3 := by
    rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      intervalIntegrable_const, hpoly]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rw [hpoly2, rvF_H_int hx hxx] at hlo
  rw [hpoly, rvF_H_int hx hxx] at hhi
  norm_num at hlo hhi
  apply abs_le.mpr
  constructor <;> nlinarith [pow_nonneg hx.le 3]

private lemma rfix_vol_error {β γ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < γ) (hρ : 0 < ρ) (hlarge : isoGammaCirc β ≤ γ)
    (hψ : 1 ≤ psiIso β γ γ ρ) (hψγ : psiIso β γ γ ρ / γ ≤ 1/2) :
    |γ * isoVolRatio β γ ρ - psiIso β γ γ ρ ^ 2| ≤
      (2 * |isoKcirc β| + 2 * |isoKflat β| + 2 * |isoKsharp β| + 3) *
        (psiIso β γ γ ρ + psiIso β γ γ ρ ^ 3 / γ) := by
  let H := psiIso β γ γ ρ
  change |γ * isoVolRatio β γ ρ - H ^ 2| ≤
    (2 * |isoKcirc β| + 2 * |isoKflat β| + 2 * |isoKsharp β| + 3) * (H + H ^ 3 / γ)
  have hH : 0 < H := by dsimp [H]; linarith
  have hHγ : 0 < H / γ := div_pos hH hγ
  have hP := rfix_cross_error hHγ hψγ
  have hPe : |γ ^ 2 * isoCrossP (H / γ) - H ^ 2| ≤ 2 * H ^ 3 / γ := by
    have hh := mul_le_mul_of_nonneg_left hP (sq_nonneg γ)
    rw [← abs_of_nonneg (sq_nonneg γ), ← abs_mul, abs_of_nonneg (sq_nonneg γ)] at hh
    have e1 : γ ^ 2 * (isoCrossP (H / γ) - (H / γ) ^ 2) =
        γ ^ 2 * isoCrossP (H / γ) - H ^ 2 := by
      simp only [mul_sub, div_pow]
      field_simp [hγ.ne']
      <;> ring
    have e2 : γ ^ 2 * (2 * (H / γ) ^ 3) = 2 * H ^ 3 / γ := by field_simp [hγ.ne']; <;> ring
    rw [e1, e2] at hh
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  obtain ⟨-, hlo, hhi⟩ := thm_app_iso_vol_ridge_ii hβ0 hβ1 hlarge hρ
  have hlo' := (mul_le_mul_of_nonneg_left hlo hγ.le)
  have hhi' := (mul_le_mul_of_nonneg_left hhi hγ.le)
  have e1 : γ * (-2 * H * isoKcirc β / γ) = -2 * H * isoKcirc β := by field_simp
  have e2 : γ * (2 * (isoKflat β + isoKsharp β * H) / γ) =
      2 * (isoKflat β + isoKsharp β * H) := by field_simp
  change γ * (-2 * H * isoKcirc β / γ) ≤ _ at hlo'
  change _ ≤ γ * (2 * (isoKflat β + isoKsharp β * H) / γ) at hhi'
  rw [e1] at hlo'
  rw [e2] at hhi'
  have he : γ * (isoVolRatio β γ ρ - H / γ - γ * isoCrossP (H / γ)) =
      γ * isoVolRatio β γ ρ - H - γ ^ 2 * isoCrossP (H / γ) := by field_simp [hγ.ne']; <;> ring
  change _ ≤ γ * (isoVolRatio β γ ρ - H / γ - γ * isoCrossP (H / γ)) at hlo'
  change γ * (isoVolRatio β γ ρ - H / γ - γ * isoCrossP (H / γ)) ≤ _ at hhi'
  rw [he] at hlo' hhi'
  have hq : 0 ≤ H ^ 3 / γ := by positivity
  have hK0 := abs_nonneg (isoKcirc β)
  have hK1 := abs_nonneg (isoKflat β)
  have hK2 := abs_nonneg (isoKsharp β)
  have hloK := le_abs_self (isoKcirc β)
  have hhiK1 := le_abs_self (isoKflat β)
  have hhiK2 := le_abs_self (isoKsharp β)
  have herr : |γ * isoVolRatio β γ ρ - H - γ ^ 2 * isoCrossP (H / γ)| ≤
      (2 * |isoKcirc β| + 2 * |isoKflat β| + 2 * |isoKsharp β|) * H := by
    apply abs_le.mpr
    constructor
    · nlinarith [mul_nonneg hH.le (sub_nonneg.mpr hloK), mul_nonneg hK1 hH.le, mul_nonneg hK2 hH.le]
    · nlinarith [mul_nonneg hH.le (sub_nonneg.mpr hhiK2)]
  have htriangle : |γ * isoVolRatio β γ ρ - H ^ 2| ≤
      |γ * isoVolRatio β γ ρ - H - γ ^ 2 * isoCrossP (H / γ)| +
      |γ ^ 2 * isoCrossP (H / γ) - H ^ 2| + H := by
    calc _ = |(γ * isoVolRatio β γ ρ - H - γ ^ 2 * isoCrossP (H / γ)) +
        (γ ^ 2 * isoCrossP (H / γ) - H ^ 2) + H| := by congr 1; ring
      _ ≤ _ := by simpa only [abs_of_pos hH] using abs_add_three _ _ H
  apply htriangle.trans
  calc _ ≤ (2 * |isoKcirc β| + 2 * |isoKflat β| + 2 * |isoKsharp β|) * H +
        2 * H ^ 3 / γ + H := by linarith only [herr, hPe]
    _ ≤ _ := by
      have hnonneg : 0 ≤ 2 * H +
          (2 * |isoKcirc β| + 2 * |isoKflat β| + 2 * |isoKsharp β| + 1) * (H ^ 3 / γ) := by positivity
      convert (le_add_of_nonneg_right hnonneg :
        (2 * |isoKcirc β| + 2 * |isoKflat β| + 2 * |isoKsharp β|) * H + 2 * H ^ 3 / γ + H ≤
        ((2 * |isoKcirc β| + 2 * |isoKflat β| + 2 * |isoKsharp β|) * H + 2 * H ^ 3 / γ + H) +
          (2 * H + (2 * |isoKcirc β| + 2 * |isoKflat β| + 2 * |isoKsharp β| + 1) * (H ^ 3 / γ))) using 1 <;> ring


private lemma rfix_vol_eventual {α : Type*} {l : Filter α} {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (gam ρ : α → ℝ)
    (hγ : ∀ᶠ n in l, 0 < gam n) (hρ : ∀ᶠ n in l, 0 < ρ n)
    (hψ : Tendsto (fun n => psiIso β (gam n) (gam n) (ρ n)) l atTop)
    (hψγ : Tendsto (fun n => psiIso β (gam n) (gam n) (ρ n) / gam n) l (𝓝 0)) :
    ∃ C : ℝ, ∀ᶠ n in l,
      |gam n * isoVolRatio β (gam n) (ρ n) - psiIso β (gam n) (gam n) (ρ n) ^ 2| ≤
        C * (psiIso β (gam n) (gam n) (ρ n) + psiIso β (gam n) (gam n) (ρ n) ^ 3 / gam n) := by
  have hgam : Tendsto gam l atTop := by
    apply tendsto_atTop_mono' l _ hψ
    filter_upwards [hγ, hρ] with n hn hρn
    simpa only [min_self] using (rfix_root hβ0 hβ1 hn hn hρn).2.2.1.le
  refine ⟨2 * |isoKcirc β| + 2 * |isoKflat β| + 2 * |isoKsharp β| + 3, ?_⟩
  filter_upwards [hγ, hρ, hgam.eventually_ge_atTop (isoGammaCirc β),
    hψ.eventually_ge_atTop 1,
    hψγ.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/2))] with n hn hρn hlarge hH hsmall
  exact rfix_vol_error hβ0 hβ1 hn hρn hlarge hH hsmall.le

private lemma rfix_fixed_limits {β ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : 0 < ρ) :
    Tendsto (fun γ : ℝ => psiIso β γ γ ρ) atTop atTop ∧
      Tendsto (fun γ : ℝ => psiIso β γ γ ρ / γ) atTop (𝓝 0) := by
  let L := Real.log (1 / β)
  let K := isoPfrak β ρ + Real.log (1 - β) / L
  let p := fun γ => isoPhat β γ γ ρ
  have hL : 0 < L := Real.log_pos ((lt_div_iff₀ hβ0).2 (by linarith))
  have hform : ∀ᶠ γ : ℝ in atTop, p γ = Real.log γ / L + K := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with γ hγ
    dsimp [p, K]
    rw [rfix_square_formula hβ1 hγ hρ,
      Real.log_mul (by linarith : 0 < 1 - β).ne' hγ.ne']
    dsimp [L]
    ring
  have hp : Tendsto p atTop atTop := by
    apply (tendsto_congr' hform).2
    exact tendsto_atTop_add_const_right _ K (Real.tendsto_log_atTop.atTop_div_const hL)
  have hl : Tendsto (fun γ : ℝ => Real.log γ / γ) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hK : Tendsto (fun γ : ℝ => K / γ) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hpg : Tendsto (fun γ : ℝ => p γ / γ) atTop (𝓝 0) := by
    have he : (fun γ : ℝ => p γ / γ) =ᶠ[atTop] (fun γ => Real.log γ / γ / L + K / γ) := by
      filter_upwards [hform] with γ hγ
      rw [hγ]; ring
    exact (tendsto_congr' he).2 (by simpa using (hl.div_const L).add hK)
  obtain ⟨C, hreg⟩ := rfix_regime hβ0 hβ1 (fun γ : ℝ => γ) p tendsto_id hp hpg
  have hbnd : ∀ᶠ γ : ℝ in atTop, |psiIso β γ γ ρ - p γ| ≤ C := by
    filter_upwards [hreg, eventually_gt_atTop (0 : ℝ)] with γ hγ hγ0
    have hh := (thm_app_iso_fixed_ridge_i hβ0 hβ1 hγ0 hγ0 hρ
      (by simpa only [min_self] using hγ.1) (by simpa only [min_self] using hγ.2.1)).1
    exact hh.trans (by simpa only [min_self] using hγ.2.2)
  refine ⟨?_, ?_⟩
  · apply tendsto_atTop_mono' atTop _ (tendsto_atTop_add_const_right _ (-C) hp)
    filter_upwards [hbnd] with γ hγ
    linarith [(abs_le.mp hγ).1]
  · have herr : Tendsto (fun γ : ℝ => (psiIso β γ γ ρ - p γ) / γ) atTop (𝓝 0) := by
      apply squeeze_zero_norm' _ (tendsto_const_nhds.div_atTop tendsto_id :
        Tendsto (fun γ : ℝ => C / γ) atTop (𝓝 0))
      filter_upwards [hbnd, eventually_gt_atTop (0 : ℝ)] with γ hγ hγ0
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hγ0]
      exact div_le_div_of_nonneg_right hγ hγ0.le
    convert herr.add hpg using 1
    · funext γ; ring
    · simp

/-- `cor:app-iso-fixed-ridge`(iii), square case along sequences `γ_n`, `ϱ_n > 0`, `B_n > 0`
with `N_n = γ_n B_n`. The `O`-term is explicit: `|v − Bψ²| ≤ C B (ψ + ψ³/γ)`, equivalent to
`v = Bψ²(1 + O(1/ψ + ψ/γ))` for `ψ → ∞` and `ψ/γ → 0`. -/
theorem cor_app_iso_fixed_ridge_iii {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (gam B ϱ : ℕ → ℝ) (hγ : ∀ n, 0 < gam n) (hB : ∀ n, 0 < B n) (hϱ : ∀ n, 0 < ϱ n)
    (hψ : Tendsto (fun n => psiIso β (gam n) (gam n) (ϱ n)) atTop atTop)
    (hψγ : Tendsto (fun n => psiIso β (gam n) (gam n) (ϱ n) / gam n) atTop (𝓝 0)) :
    (∀ n, Summable (fun ℓ : ℕ => lagCoeff β (gam n) (ϱ n) (ℓ + 1))) ∧
      ∃ C : ℝ, ∀ᶠ n in atTop,
        |gam n * B n * isoVolRatio β (gam n) (ϱ n) - B n * psiIso β (gam n) (gam n) (ϱ n) ^ 2|
          ≤ C * B n * (psiIso β (gam n) (gam n) (ϱ n)
              + psiIso β (gam n) (gam n) (ϱ n) ^ 3 / gam n) := by
  refine ⟨fun n => rfix_lag_summable hβ0 hβ1 (hγ n) (hϱ n), ?_⟩
  obtain ⟨C, hC⟩ := rfix_vol_eventual hβ0 hβ1 gam ϱ
    (Eventually.of_forall hγ) (Eventually.of_forall hϱ) hψ hψγ
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n hn
  have hh := mul_le_mul_of_nonneg_left hn (hB n).le
  rw [← abs_of_pos (hB n), ← abs_mul, abs_of_pos (hB n)] at hh
  convert hh using 1 <;> ring

/-- `cor:app-iso-fixed-ridge`(iii), the clause "in particular at a fixed `ϱ > 0`" (`section.tex`
l.3515–3520), in the explicit form `v = N · isoVolRatio` with `N = γB` (so `v/B = γ · isoVolRatio`).
The absolute constant depends on `β` and `ϱ`. -/
theorem cor_app_iso_fixed_ridge_iii_fixed {β ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϱ : 0 < ϱ) :
    (∀ γ : ℝ, 0 < γ → Summable (fun ℓ : ℕ => lagCoeff β γ ϱ (ℓ + 1))) ∧
      ∃ C : ℝ, ∀ᶠ γ in atTop,
        |γ * isoVolRatio β γ ϱ - psiIso β γ γ ϱ ^ 2|
          ≤ C * (psiIso β γ γ ϱ + psiIso β γ γ ϱ ^ 3 / γ) := by
  refine ⟨fun γ hγ => rfix_lag_summable hβ0 hβ1 hγ hϱ, ?_⟩
  obtain ⟨hψ, hψγ⟩ := rfix_fixed_limits hβ0 hβ1 hϱ
  exact rfix_vol_eventual hβ0 hβ1 (fun γ : ℝ => γ) (fun _ => ϱ)
    (eventually_gt_atTop 0) (Eventually.of_forall (fun _ => hϱ)) hψ hψγ

/-! ## Crossover -/

private lemma rcross_log_div {a L : ℝ} (ha : 0 < a) (hL : 0 < L) :
    Tendsto (fun x : ℝ => Real.log (a * x) / (L * x)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have ha' : Tendsto (fun x : ℝ => Real.log a / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have he : (fun x : ℝ => Real.log (a * x) / (L * x)) =ᶠ[atTop]
      (fun x => (Real.log a / x + Real.log x / x) / L) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.log_mul ha.ne' hx.ne']
    ring
  exact (tendsto_congr' he).2 (by simpa using (ha'.add hlog).div_const L)

private lemma rcross_ratio {β c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c)
    (g ρ : ℕ → ℝ) (hg0 : ∀ n, 0 < g n) (hρ : ∀ n, 0 < ρ n) (hρ1 : ∀ n, ρ n < 1)
    (hg : Tendsto g atTop atTop)
    (hp : Tendsto (fun n => isoPfrak β (ρ n) / g n) atTop (𝓝 c)) :
    Tendsto (fun n => psiIso β (g n) (g n) (ρ n) / g n) atTop (𝓝 (min c 1)) := by
  let H := fun n => psiIso β (g n) (g n) (ρ n)
  let p := fun n => isoPfrak β (ρ n)
  let L := Real.log (1 / β)
  have hL : 0 < L := Real.log_pos ((lt_div_iff₀ hβ0).2 (by linarith))
  have hb : 0 < 1 - β := by linarith
  have hroot : ∀ n, 0 < qIso β (g n) (g n) (ρ n) ∧ 0 < H n ∧ H n < g n ∧
      ρ n * qIso β (g n) (g n) (ρ n) = (g n - H n) ^ 2 := by
    intro n
    simpa only [H, min_self, pow_two] using rfix_root hβ0 hβ1 (hg0 n) (hg0 n) (hρ n)
  have hcount : ∀ᶠ n in atTop,
      p n + Real.log ((1 - β) * (g n - H n)) / L - isoC β < H n ∧
      H n ≤ p n + Real.log ((1 - β) * (g n - H n)) / L + isoC' β := by
    filter_upwards [hg.eventually_gt_atTop (isoC' β + 1 / (1 - β))] with n hn
    obtain ⟨hq, hH, hHg, heq⟩ := hroot n
    have hx : 1 ≤ (1 - β) ^ 2 * qIso β (g n) (g n) (ρ n) := by
      by_contra hnx
      have hxlt : (1 - β) ^ 2 * qIso β (g n) (g n) (ρ n) < 1 := lt_of_not_ge hnx
      have hqq : qIso β (g n) (g n) (ρ n) ≤ 1 / (1 - β) ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hb)]
        nlinarith
      have hr := rf6_isoLink hβ0 hβ1
      have hHc : H n ≤ isoC' β := by
        have hm := hr.2.1.monotoneOn (mem_Ici.mpr hq.le) (mem_Ici.mpr (by positivity)) hqq
        exact hm.trans (lem_app_iso_count_i hβ0 hβ1).2
      have hres : 1 / (1 - β) < g n - H n := by linarith
      have hleft : 1 < (1 - β) ^ 2 * (g n - H n) ^ 2 := by
        have hm := mul_lt_mul_of_pos_left hres hb
        field_simp at hm
        nlinarith
      have hright : (1 - β) ^ 2 * (ρ n * qIso β (g n) (g n) (ρ n)) < 1 := by
        have hm := mul_lt_mul_of_pos_right (hρ1 n) hq
        nlinarith [mul_pos (sq_pos_of_pos hb) hq]
      rw [heq] at hright
      linarith
    have hnph : isoN β (qIso β (g n) (g n) (ρ n)) =
        isoPhat β (g n - H n) (g n - H n) (ρ n) := by
      unfold isoN isoPhat
      congr 2
      field_simp [(hρ n).ne']
      nlinarith [heq]
    have hform : isoN β (qIso β (g n) (g n) (ρ n)) =
        p n + Real.log ((1 - β) * (g n - H n)) / L := by
      rw [hnph, rfix_square_formula hβ1 (by linarith) (hρ n)]
    have hcq := (lem_app_iso_count_i hβ0 hβ1).1 _ hx
    rw [hform] at hcq
    simpa only [H, psiIso] using hcq
  have hlogUpper : Tendsto (fun n => Real.log ((1 - β) * g n) / (L * g n)) atTop (𝓝 0) :=
    (rcross_log_div hb hL).comp hg
  have hc'g : Tendsto (fun n => isoC' β / g n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hg
  let up := fun n => min 1 (p n / g n + Real.log ((1 - β) * g n) / (L * g n) + isoC' β / g n)
  have hupLim : Tendsto up atTop (𝓝 (min c 1)) := by
    have hs := (hp.add hlogUpper).add hc'g
    have hm := (tendsto_const_nhds (x := (1 : ℝ))).min hs
    simpa only [up, p, add_zero, min_comm 1 c] using hm
  have hup : ∀ᶠ n in atTop, H n / g n ≤ up n := by
    filter_upwards [hcount] with n hn
    obtain ⟨hq, hH, hHg, -⟩ := hroot n
    have hlogle : Real.log ((1 - β) * (g n - H n)) ≤ Real.log ((1 - β) * g n) :=
      Real.log_le_log (mul_pos hb (by linarith)) (by nlinarith)
    have h1 : H n / g n ≤ 1 := (div_le_one (hg0 n)).2 hHg.le
    have h2 : H n / g n ≤ p n / g n + Real.log ((1 - β) * g n) / (L * g n) + isoC' β / g n := by
      have hh := div_le_div_of_nonneg_right hn.2 (hg0 n).le
      calc H n / g n ≤ (p n + Real.log ((1 - β) * (g n - H n)) / L + isoC' β) / g n := hh
        _ = p n / g n + Real.log ((1 - β) * (g n - H n)) / (L * g n) +
            isoC' β / g n := by field_simp
        _ ≤ _ := by
          have ht := div_le_div_of_nonneg_right hlogle (mul_nonneg hL.le (hg0 n).le)
          linarith
    exact le_min h1 h2
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ := min (ε / 4) (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ < ε / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have haδ : 0 < (1 - β) * δ := mul_pos hb hδ
  have hlogLower : Tendsto
      (fun n => Real.log (((1 - β) * δ) * g n) / (L * g n)) atTop (𝓝 0) :=
    (rcross_log_div haδ hL).comp hg
  have hcg : Tendsto (fun n => isoC β / g n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hg
  let lo := fun n => min (1 - δ)
    (p n / g n + Real.log (((1 - β) * δ) * g n) / (L * g n) - isoC β / g n)
  have hloLim : Tendsto lo atTop (𝓝 (min (1 - δ) c)) := by
    have hs := (hp.add hlogLower).sub hcg
    simpa only [lo, p, add_zero, sub_zero] using tendsto_const_nhds.min hs
  have hlo : ∀ᶠ n in atTop, lo n < H n / g n := by
    filter_upwards [hcount] with n hn
    obtain ⟨-, hH, hHg, -⟩ := hroot n
    by_cases hh : 1 - δ < H n / g n
    · exact (min_le_left _ _).trans_lt hh
    · have hratio : H n / g n ≤ 1 - δ := le_of_not_gt hh
      have hres : δ * g n ≤ g n - H n := by
        have := (div_le_iff₀ (hg0 n)).1 hratio
        nlinarith
      have hlogle : Real.log (((1 - β) * δ) * g n) ≤
          Real.log ((1 - β) * (g n - H n)) :=
        Real.log_le_log (mul_pos haδ (hg0 n)) (by nlinarith)
      have hh' := div_lt_div_of_pos_right hn.1 (hg0 n)
      rw [sub_div, add_div, div_div] at hh'
      change min (1 - δ)
        (p n / g n + Real.log (((1 - β) * δ) * g n) / (L * g n) - isoC β / g n) < _
      have ht := div_le_div_of_nonneg_right hlogle (mul_nonneg hL.le (hg0 n).le)
      exact (min_le_right _ _).trans_lt (lt_of_le_of_lt
        (by linarith) hh')
  have hnearLo := Metric.tendsto_atTop.1 hloLim (ε / 2) (by positivity)
  have hnearUp := Metric.tendsto_atTop.1 hupLim ε hε
  obtain ⟨nlo, hnlo⟩ := hnearLo
  obtain ⟨nup, hnup⟩ := hnearUp
  obtain ⟨nb, hnb⟩ := eventually_atTop.1 (hlo.and hup)
  refine ⟨max nb (max nlo nup), ?_⟩
  intro n hn
  have hbnd := hnb n (le_trans (le_max_left _ _) hn)
  have hloN := hnlo n (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn))
  have hupN := hnup n (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
  rw [Real.dist_eq] at hloN hupN ⊢
  have hmin : |min (1 - δ) c - min c 1| ≤ δ := by
    rw [min_comm c 1]
    calc |min (1 - δ) c - min 1 c|
        ≤ max |(1 - δ) - 1| |c - c| := abs_min_sub_min_le_max _ _ _ _
      _ = δ := by
        rw [show (1 - δ) - 1 = -δ by ring, abs_neg, abs_of_nonneg hδ.le]
        simp [hδ.le]
  rw [abs_lt] at hloN hupN ⊢
  have hm := abs_le.mp hmin
  constructor <;> linarith

private lemma rcross_P_continuous : Continuous isoCrossP := by
  let F := fun x : ℝ => 1 / 2 - (1 - x) ^ 2 / 2 + (1 - x) ^ 2 * Real.log (1 - x)
  have hml : Continuous (fun x : ℝ => (1 - x) * Real.log (1 - x)) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  have hF : Continuous F := by
    dsimp [F]
    have hs : Continuous (fun x : ℝ => (1 - x) ^ 2 / 2) :=
      ((continuous_const.sub continuous_id).pow 2).div_const 2
    have ht : Continuous (fun x : ℝ => (1 - x) ^ 2 * Real.log (1 - x)) := by
      have hlin : Continuous (fun x : ℝ => 1 - x) := continuous_const.sub continuous_id
      rw [show (fun x : ℝ => (1 - x) ^ 2 * Real.log (1 - x)) =
        (fun x : ℝ => (1 - x) * ((1 - x) * Real.log (1 - x))) by
          funext x; ring]
      exact hlin.mul hml
    exact (continuous_const.sub hs).add ht
  have he : isoCrossP = fun x => if x ≤ 1 then F x else 1 / 2 := by
    funext x
    by_cases hx : x < 1
    · simp [isoCrossP, F, hx, hx.le]
    · have hx' : 1 ≤ x := le_of_not_gt hx
      by_cases heq : x = 1
      · subst x; simp [isoCrossP, F]
      · simp [isoCrossP, F, hx, not_le.mpr (lt_of_le_of_ne hx' (Ne.symm heq))]
  rw [he]
  exact Continuous.if_le hF continuous_const continuous_id continuous_const (by
    intro x hx
    subst x
    simp [F])

/-- `thm:app-iso-crossover`, along sequences `N_n, B_n > 0` with `γ_n = N_n/B_n → ∞`, `ϱ_n ∈ (0,1)`
and `𝔭_β(ϱ_n)/γ_n → c ∈ (0,∞)`. 

`thm:app-iso-crossover`, snapshot `cr-2026-10-23`, `section.tex` l.3560-3572.

LaTeX (verbatim):
\begin{theorem}[Crossover]\label{thm:app-iso-crossover}
Let $\bmom\in(0,1)$ be fixed, let $\Nin=\Nout=N$ and $\gamma=N/B\to\infty$, and let
$\ridge_\gamma\in(0,1)$ satisfy $\mathfrak p_\bmom(\ridge_\gamma)/\gamma\to c\in(0,\infty)$. Then
$\psi(\ridge_\gamma)/\gamma\to c\wedge1$, the same-time total satisfies
$B\psi(\ridge_\gamma)/N\to c\wedge1$,
\[
\mathfrak d_{\mathrm{iso}}(\ridge_\gamma)\longrightarrow\Xi(c)\defeq\frac{(c\wedge1)\big(1-\tfrac12(c\wedge1)\big)}{\sqrt\pi},
\]
and, with $\mathcal P$ of \cref{eqn:app-iso-crossover-P},
\[
\frac{\mathfrak v_{\mathrm{iso}}(\ridge_\gamma)}{N\gamma}\longrightarrow\mathcal P(c\wedge1).
\]
\end{theorem}
-/
theorem thm_app_iso_crossover {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (c : ℝ) (hc : 0 < c) (N B ϱ : ℕ → ℝ)
    (hN : ∀ n, 0 < N n) (hB : ∀ n, 0 < B n)
    (hγ : Tendsto (fun n => N n / B n) atTop atTop)
    (hϱ : ∀ n, 0 < ϱ n) (hϱ1 : ∀ n, ϱ n < 1)
    (hp : Tendsto (fun n => isoPfrak β (ϱ n) / (N n / B n)) atTop (𝓝 c)) :
    Tendsto (fun n => psiIso β (N n / B n) (N n / B n) (ϱ n) / (N n / B n))
        atTop (𝓝 (min c 1)) ∧
      Tendsto (fun n => B n * psiIso β (N n / B n) (N n / B n) (ϱ n) / N n)
        atTop (𝓝 (min c 1)) ∧
      Tendsto (fun n => dIso β (N n / B n) (N n / B n) (ϱ n))
        atTop (𝓝 (isoCrossXi c)) ∧
      (∀ n, Summable (fun ℓ : ℕ => lagCoeff β (N n / B n) (ϱ n) (ℓ + 1))) ∧
      Tendsto (fun n => isoVolRatio β (N n / B n) (ϱ n) / (N n / B n))
        atTop (𝓝 (isoCrossP (min c 1))) := by
  let g := fun n => N n / B n
  let H := fun n => psiIso β (g n) (g n) (ϱ n)
  have hg0 : ∀ n, 0 < g n := fun n => div_pos (hN n) (hB n)
  have hx : Tendsto (fun n => H n / g n) atTop (𝓝 (min c 1)) :=
    rcross_ratio hβ0 hβ1 hc g ϱ hg0 hϱ hϱ1 hγ hp
  have hsame : Tendsto (fun n => B n * H n / N n) atTop (𝓝 (min c 1)) := by
    convert hx using 1
    funext n
    dsimp [g]
    field_simp [(hN n).ne', (hB n).ne']
  have hxi : Tendsto (fun n => isoXi0 (H n / g n)) atTop (𝓝 (isoXi0 (min c 1))) := by
    have hcont : Continuous isoXi0 := by
      unfold isoXi0
      fun_prop
    exact hcont.continuousAt.tendsto.comp hx
  have hderr : Tendsto (fun n => dIso β (g n) (g n) (ϱ n) - isoXi0 (H n / g n))
      atTop (𝓝 0) := by
    have hb : 0 < 1 - β := by linarith
    have hbound : Tendsto (fun n => (2.32 / (1 - β)) / g n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hγ
    apply squeeze_zero_norm' _ hbound
    filter_upwards [] with n
    have hm := thm_app_iso_master_ii hβ0 hβ1 (hg0 n) (hϱ n).le
    rw [isoMLevel, if_neg (hϱ n).ne'] at hm
    rw [Real.norm_eq_abs]
    have he : 2.32 / ((1 - β) * g n) = (2.32 / (1 - β)) / g n := by
      field_simp [hb.ne', (hg0 n).ne']
    rw [he] at hm
    exact hm.le
  have hdrift : Tendsto (fun n => dIso β (g n) (g n) (ϱ n))
      atTop (𝓝 (isoCrossXi c)) := by
    have ht := hderr.add hxi
    convert ht using 1
    · funext n; ring
    · unfold isoCrossXi isoXi0
      ring
  have hP : Tendsto (fun n => isoCrossP (H n / g n)) atTop
      (𝓝 (isoCrossP (min c 1))) := rcross_P_continuous.continuousAt.tendsto.comp hx
  have hloLim : Tendsto (fun n => -2 * H n * isoKcirc β / g n / g n) atTop (𝓝 0) := by
    have hz : Tendsto (fun n => (-2 * isoKcirc β) / g n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hγ
    convert hx.mul hz using 1
    · funext n; ring
    · simp
  have hhiLim : Tendsto (fun n => 2 * (isoKflat β + isoKsharp β * H n) / g n / g n)
      atTop (𝓝 0) := by
    have hflat : Tendsto (fun n => (2 * isoKflat β / g n) / g n) atTop (𝓝 0) :=
      (tendsto_const_nhds.div_atTop hγ).div_atTop hγ
    have hz : Tendsto (fun n => (2 * isoKsharp β) / g n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hγ
    have hsharp : Tendsto (fun n => (H n / g n) * (2 * isoKsharp β / g n)) atTop (𝓝 0) := by
      simpa using hx.mul hz
    convert hflat.add hsharp using 1
    · funext n; ring
    · simp
  let A := fun n =>
    (isoVolRatio β (g n) (ϱ n) - H n / g n - g n * isoCrossP (H n / g n)) / g n
  have hAbounds : ∀ᶠ n in atTop,
      -2 * H n * isoKcirc β / g n / g n ≤ A n ∧
      A n ≤ 2 * (isoKflat β + isoKsharp β * H n) / g n / g n := by
    filter_upwards [hγ.eventually_ge_atTop (isoGammaCirc β)] with n hn
    obtain ⟨-, hlo, hhi⟩ := thm_app_iso_vol_ridge_ii hβ0 hβ1 hn (hϱ n)
    constructor
    · exact div_le_div_of_nonneg_right hlo (hg0 n).le
    · exact div_le_div_of_nonneg_right hhi (hg0 n).le
  have hA : Tendsto A atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hloLim hhiLim
      (hAbounds.mono fun n hn => hn.1) (hAbounds.mono fun n hn => hn.2)
  have hsmall : Tendsto (fun n => (H n / g n) / g n) atTop (𝓝 0) := hx.div_atTop hγ
  have hvol : Tendsto (fun n => isoVolRatio β (g n) (ϱ n) / g n)
      atTop (𝓝 (isoCrossP (min c 1))) := by
    have ht := (hA.add hsmall).add hP
    convert ht using 1
    · funext n
      dsimp [A]
      field_simp [(hg0 n).ne']
      <;> ring
    · simp
  refine ⟨?_, hsame, hdrift, ?_, ?_⟩
  · simpa only [g, H] using hx
  · intro n
    exact rfix_lag_summable hβ0 hβ1 (hg0 n) (hϱ n)
  · simpa only [g] using hvol

/-- `prop:app-iso-limit-order`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.3619–3632):
```latex
\begin{proposition}[Order of limits at positive ridge]\label{prop:app-iso-limit-order}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item For fixed $\gin,\gout>0$ and $\ridge>0$,
$\lim_{\bmom\downarrow0}\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gin,\gout)=\mathfrak d_{\mathrm{iso}}(\ridge;0,\gin,\gout)$.
\item For $\gamma\ge2$ and $\ridge\ge0$,
\[
\Big|\gamma\,\mathfrak d_{\mathrm{iso}}(\ridge;0,\gamma,\gamma)-\frac1{\sqrt\pi}\Big|\le\frac{\sqrt2\,\big(1+\sqrt{2\pi}/2+\sqrt\ridge\big)}{\pi\gamma} .
\]
\item For every $\ridge>0$,
$\lim_{\gamma\to\infty}\lim_{\bmom\downarrow0}\gamma\,\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gamma,\gamma)=\pi^{-1/2}$,
whereas for every fixed $\bmom\in(0,1)$, $\gamma\,\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gamma,\gamma)\to\infty$ as $\gamma\to\infty$.
\end{enumerate}
\end{proposition}
```

Part (i): the limit `β ↓ 0` at fixed positive ridge. 
Relocated here from `Muon.Isotropic.ZeroRidge` by the coordinator (2026-10-24): its proof needs results of this
module, which imports the original one. -/
private lemma pf5c_weightSeq {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    Muon.DetEquiv.WeightSeq (Muon.emaW b) := by
  refine ⟨fun j => ?_, ?_, 0, ?_⟩
  · unfold Muon.emaW
    exact mul_nonneg (by linarith) (pow_nonneg hb0 j)
  · unfold Muon.emaW
    exact (summable_geometric_of_lt_one hb0 hb1).mul_left _
  · simp only [Muon.emaW, pow_zero, mul_one]
    linarith

private lemma pf5c_isoLink {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    IsIsoLink (Muon.DetEquiv.rW (Muon.emaW b)) := by
  have hw := pf5c_weightSeq hb0 hb1
  exact ⟨ContinuousOn.mul continuousOn_id (Muon.DetEquiv.Fw_admissible hw).contOn,
    (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.1,
    (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.2.1⟩

private lemma pf5c_J_comp {α : Type*} {l : Filter α} {f : α → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hf : Tendsto f l (𝓝 a)) (hfn : ∀ᶠ x in l, 0 ≤ f x) :
    Tendsto (fun x => Muon.DetEquiv.J (f x)) l (𝓝 (Muon.DetEquiv.J a)) := by
  have hc : Tendsto Muon.DetEquiv.J (𝓝[Set.Ici 0] a) (𝓝 (Muon.DetEquiv.J a)) :=
    Muon.DetEquiv.lem_app_de_scalar_i.1 a (Set.mem_Ici.2 ha)
  exact hc.comp (tendsto_nhdsWithin_iff.2 ⟨hf, hfn⟩)

private lemma pf5c_Fw_tendsto (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun b : ℝ => Muon.DetEquiv.Fw (Muon.emaW b) q) (𝓝[>] (0 : ℝ))
      (𝓝 (Muon.DetEquiv.J q)) := by
  have hs : Summable (fun j : ℕ => ((1 / 2 : ℝ) ^ j) ^ 2) := by
    have h := summable_geometric_of_lt_one (show (0 : ℝ) ≤ (1 / 2) ^ 2 by norm_num)
      (show (1 / 2 : ℝ) ^ 2 < 1 by norm_num)
    convert h using 1
    funext j
    calc ((1 / 2 : ℝ) ^ j) ^ 2 = ((1 / 2 : ℝ) ^ 2) ^ j := pow_right_comm _ _ _
      _ = ((1 / 2 : ℝ) ^ 2) ^ j := rfl
  have hlim : Tendsto
      (fun b : ℝ => ∑' j : ℕ, Muon.emaW b j ^ 2 *
        Muon.DetEquiv.J (Muon.emaW b j ^ 2 * q))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑' j : ℕ, (if j = 0 then Muon.DetEquiv.J q else 0))) := by
    refine tendsto_tsum_of_dominated_convergence hs (fun j => ?_) ?_
    · by_cases hj : j = 0
      · subst j
        have hw : Tendsto (fun b : ℝ => Muon.emaW b 0) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
          have h : Tendsto (fun b : ℝ => 1 - b) (𝓝 (0 : ℝ)) (𝓝 (1 - 0)) :=
            tendsto_const_nhds.sub tendsto_id
          simpa [Muon.emaW] using h.mono_left nhdsWithin_le_nhds
        have harg := (hw.pow 2).mul_const q
        have hJ := pf5c_J_comp hq (by simpa using harg)
          (by filter_upwards [self_mem_nhdsWithin] with b hb; positivity)
        simpa [Muon.emaW] using (hw.pow 2).mul hJ
      · have hjp : 0 < j := Nat.pos_of_ne_zero hj
        have hp : Tendsto (fun b : ℝ => b ^ j) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have hi : Tendsto (fun b : ℝ => b) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
          have h := hi.pow j
          simpa only [zero_pow hjp.ne'] using h.mono_left nhdsWithin_le_nhds
        have hw : Tendsto (fun b : ℝ => Muon.emaW b j) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have hsub : Tendsto (fun b : ℝ => 1 - b) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
            have h : Tendsto (fun b : ℝ => 1 - b) (𝓝 (0 : ℝ)) (𝓝 (1 - 0)) :=
              tendsto_const_nhds.sub tendsto_id
            simpa using h.mono_left nhdsWithin_le_nhds
          simpa [Muon.emaW] using hsub.mul hp
        have harg := (hw.pow 2).mul_const q
        have hJ := pf5c_J_comp (a := 0) le_rfl (by simpa using harg)
          (by filter_upwards [self_mem_nhdsWithin] with b hb; positivity)
        simpa [hj] using (hw.pow 2).mul hJ
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with b hb j
      have hb0 : 0 ≤ b := hb.1.le
      have hb1 : b < 1 := lt_trans hb.2 (by norm_num)
      have hw0 : 0 ≤ Muon.emaW b j := by
        unfold Muon.emaW
        positivity
      have hw : Muon.emaW b j ≤ (1 / 2 : ℝ) ^ j := by
        unfold Muon.emaW
        have hp := pow_le_pow_left₀ hb0 hb.2.le j
        have hfac : 1 - b ≤ 1 := by linarith
        calc (1 - b) * b ^ j ≤ 1 * b ^ j :=
              mul_le_mul_of_nonneg_right hfac (pow_nonneg hb0 j)
          _ ≤ (1 / 2 : ℝ) ^ j := by simpa using hp
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact mul_le_of_le_one_right (sq_nonneg _)
          ((Muon.DetEquiv.lem_app_de_scalar_i.2.2.1 _
            (mul_nonneg (sq_nonneg _) hq)).2)
          |>.trans (sq_le_sq₀ hw0 (by positivity) |>.2 hw)
      · exact mul_nonneg (sq_nonneg _)
          (Muon.DetEquiv.lem_app_de_scalar_i.2.2.1 _
            (mul_nonneg (sq_nonneg _) hq)).1.le
  simpa [Muon.DetEquiv.Fw, tsum_ite_eq' 0] using hlim

private lemma pf5c_rW_tendsto (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun b : ℝ => Muon.DetEquiv.rW (Muon.emaW b) q) (𝓝[>] (0 : ℝ))
      (𝓝 (isoPhi q)) := by
  simpa [Muon.DetEquiv.rW, isoPhi] using (pf5c_Fw_tendsto q hq).const_mul q

private lemma pf5c_Lw_tendsto (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun b : ℝ => Muon.DetEquiv.Lw (Muon.emaW b) q) (𝓝[>] (0 : ℝ))
      (𝓝 (Muon.DetEquiv.J q)) := by
  have hs : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto
      (fun b : ℝ => ∑' j : ℕ, Muon.emaW b j *
        Muon.DetEquiv.J (Muon.emaW b j ^ 2 * q))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑' j : ℕ, (if j = 0 then Muon.DetEquiv.J q else 0))) := by
    refine tendsto_tsum_of_dominated_convergence hs (fun j => ?_) ?_
    · by_cases hj : j = 0
      · subst j
        have hw : Tendsto (fun b : ℝ => Muon.emaW b 0) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
          have h : Tendsto (fun b : ℝ => 1 - b) (𝓝 (0 : ℝ)) (𝓝 (1 - 0)) :=
            tendsto_const_nhds.sub tendsto_id
          simpa [Muon.emaW] using h.mono_left nhdsWithin_le_nhds
        have harg := (hw.pow 2).mul_const q
        have hJ := pf5c_J_comp hq (by simpa using harg)
          (by filter_upwards [self_mem_nhdsWithin] with b hb; positivity)
        simpa [Muon.emaW] using hw.mul hJ
      · have hjp : 0 < j := Nat.pos_of_ne_zero hj
        have hp : Tendsto (fun b : ℝ => b ^ j) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have hi : Tendsto (fun b : ℝ => b) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
          have h := hi.pow j
          simpa only [zero_pow hjp.ne'] using h.mono_left nhdsWithin_le_nhds
        have hw : Tendsto (fun b : ℝ => Muon.emaW b j) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have hsub : Tendsto (fun b : ℝ => 1 - b) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
            have h : Tendsto (fun b : ℝ => 1 - b) (𝓝 (0 : ℝ)) (𝓝 (1 - 0)) :=
              tendsto_const_nhds.sub tendsto_id
            simpa using h.mono_left nhdsWithin_le_nhds
          simpa [Muon.emaW] using hsub.mul hp
        have harg := (hw.pow 2).mul_const q
        have hJ := pf5c_J_comp (a := 0) le_rfl (by simpa using harg)
          (by filter_upwards [self_mem_nhdsWithin] with b hb; positivity)
        simpa [hj] using hw.mul hJ
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with b hb j
      have hb0 : 0 ≤ b := hb.1.le
      have hw0 : 0 ≤ Muon.emaW b j := by
        unfold Muon.emaW
        exact mul_nonneg (sub_nonneg.mpr (hb.2.trans (by norm_num)).le) (pow_nonneg hb0 j)
      have hw : Muon.emaW b j ≤ (1 / 2 : ℝ) ^ j := by
        unfold Muon.emaW
        calc (1 - b) * b ^ j ≤ 1 * b ^ j :=
              mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hb0 j)
          _ ≤ (1 / 2 : ℝ) ^ j := by simpa using pow_le_pow_left₀ hb0 hb.2.le j
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact (mul_le_of_le_one_right hw0
          (Muon.DetEquiv.lem_app_de_scalar_i.2.2.1 _
            (mul_nonneg (sq_nonneg _) hq)).2).trans hw
      · exact mul_nonneg hw0
          (Muon.DetEquiv.lem_app_de_scalar_i.2.2.1 _
            (mul_nonneg (sq_nonneg _) hq)).1.le
  simpa [Muon.DetEquiv.Lw, tsum_ite_eq' 0] using hlim

private lemma pf5c_root_pos {r : ℝ → ℝ} (hr : IsIsoLink r) {γin γout s : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s) :
    0 < isoRoot r γin γout s := by
  obtain ⟨hqD, hqG⟩ := (lem_app_iso_comparison_i hr hγin hγout).2.2.2.1 s hs
  have hq0 : 0 ≤ isoRoot r γin γout s := hqD.1
  refine lt_of_le_of_ne hq0 ?_
  intro hzero
  have hq : isoRoot r γin γout s = 0 := hzero.symm
  unfold isoG at hqG
  rw [hq, hr.2.2] at hqG
  nlinarith [mul_pos hγout hγin]

private lemma pf5c_root_tendsto {γin γout s : ℝ} (hγin : 0 < γin) (hγout : 0 < γout)
    (hs : 0 < s) :
    Tendsto (fun b : ℝ => isoRoot (Muon.DetEquiv.rW (Muon.emaW b)) γin γout s)
      (𝓝[>] (0 : ℝ))
      (𝓝 (isoRoot (Muon.DetEquiv.rW (Muon.emaW 0)) γin γout s)) := by
  let r0 := Muon.DetEquiv.rW (Muon.emaW 0)
  let q0 := isoRoot r0 γin γout s
  have hr0 : IsIsoLink r0 := pf5c_isoLink le_rfl zero_lt_one
  have hqpos : 0 < q0 := pf5c_root_pos hr0 hγin hγout hs
  obtain ⟨hqD, hqG⟩ := (lem_app_iso_comparison_i hr0 hγin hγout).2.2.2.1 s hs
  have hcont : ContinuousAt r0 q0 := hr0.1.continuousAt (Ici_mem_nhds hqpos)
  have hev : ∀ᶠ x in 𝓝 q0, r0 x < min γin γout :=
    hcont.tendsto.eventually (Iio_mem_nhds hqD.2)
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.1 hev
  rw [Metric.tendsto_nhds]
  intro ε hε
  let d := min (min (q0 / 2) (ε / 2)) (η / 2)
  let a := q0 - d
  let c := q0 + d
  have hd : 0 < d := by dsimp [d]; positivity
  have hdq : d ≤ q0 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hde : d ≤ ε / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hdη : d ≤ η / 2 := min_le_right _ _
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have hac : a < q0 := by dsimp [a]; linarith
  have hqc : q0 < c := by dsimp [c]; linarith
  have hc0 : 0 ≤ c := hqpos.le.trans hqc.le
  have haclose : dist a q0 < η := by
    rw [Real.dist_eq]
    dsimp [a]
    ring_nf
    rw [abs_neg, abs_of_pos hd]
    linarith
  have hcclose : dist c q0 < η := by
    rw [Real.dist_eq]
    dsimp [c]
    ring_nf
    rw [abs_of_pos hd]
    linarith
  have haD : a ∈ isoDr r0 γin γout := ⟨ha0, hηsub haclose⟩
  have hcD : c ∈ isoDr r0 γin γout := ⟨by dsimp [c]; positivity, hηsub hcclose⟩
  have hmono0 := (lem_app_iso_comparison_i hr0 hγin hγout).2.2.1 s hs
  have hGa : isoG r0 γin γout s a < 0 := by
    have := hmono0 haD hqD hac
    linarith
  have hGc : 0 < isoG r0 γin γout s c := by
    have := hmono0 hqD hcD hqc
    linarith
  have hra := pf5c_rW_tendsto a ha0
  have hrc := pf5c_rW_tendsto c (by dsimp [c]; positivity)
  have hzero := (lem_app_iso_weights_i (β := (0 : ℝ)) le_rfl zero_lt_one).2.2.2 rfl
  have hra0 : Tendsto (fun b : ℝ => Muon.DetEquiv.rW (Muon.emaW b) a)
      (𝓝[>] (0 : ℝ)) (𝓝 (r0 a)) := by
    simpa only [r0, hzero.1 a ha0] using hra
  have hrc0 : Tendsto (fun b : ℝ => Muon.DetEquiv.rW (Muon.emaW b) c)
      (𝓝[>] (0 : ℝ)) (𝓝 (r0 c)) := by
    simpa only [r0, hzero.1 c hc0] using hrc
  have hGaT : Tendsto
      (fun b : ℝ => isoG (Muon.DetEquiv.rW (Muon.emaW b)) γin γout s a)
      (𝓝[>] (0 : ℝ)) (𝓝 (isoG r0 γin γout s a)) := by
    unfold isoG r0
    have hs0 : Tendsto (fun _ : ℝ => s * a) (𝓝[>] (0 : ℝ)) (𝓝 (s * a)) :=
      tendsto_const_nhds
    have ho : Tendsto (fun _ : ℝ => γout) (𝓝[>] (0 : ℝ)) (𝓝 γout) :=
      tendsto_const_nhds
    have hi : Tendsto (fun _ : ℝ => γin) (𝓝[>] (0 : ℝ)) (𝓝 γin) :=
      tendsto_const_nhds
    exact hs0.sub ((ho.sub hra0).mul (hi.sub hra0))
  have hGcT : Tendsto
      (fun b : ℝ => isoG (Muon.DetEquiv.rW (Muon.emaW b)) γin γout s c)
      (𝓝[>] (0 : ℝ)) (𝓝 (isoG r0 γin γout s c)) := by
    unfold isoG r0
    have hs0 : Tendsto (fun _ : ℝ => s * c) (𝓝[>] (0 : ℝ)) (𝓝 (s * c)) :=
      tendsto_const_nhds
    have ho : Tendsto (fun _ : ℝ => γout) (𝓝[>] (0 : ℝ)) (𝓝 γout) :=
      tendsto_const_nhds
    have hi : Tendsto (fun _ : ℝ => γin) (𝓝[>] (0 : ℝ)) (𝓝 γin) :=
      tendsto_const_nhds
    exact hs0.sub ((ho.sub hrc0).mul (hi.sub hrc0))
  have hrcD : ∀ᶠ b in 𝓝[>] (0 : ℝ),
      Muon.DetEquiv.rW (Muon.emaW b) c < min γin γout :=
    hrc0.eventually (Iio_mem_nhds hcD.2)
  filter_upwards [hGaT.eventually (Iio_mem_nhds hGa),
    hGcT.eventually (Ioi_mem_nhds hGc), hrcD,
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with b hba hbc hbrc hb
  have hb1 : b < 1 := hb.2.trans (by norm_num)
  have hrb := pf5c_isoLink hb.1.le hb1
  obtain ⟨hqbD, hqbG⟩ := (lem_app_iso_comparison_i hrb hγin hγout).2.2.2.1 s hs
  have haDb : a ∈ isoDr (Muon.DetEquiv.rW (Muon.emaW b)) γin γout := by
    refine ⟨ha0, ?_⟩
    have hm := hrb.2.1.monotoneOn (Set.mem_Ici.2 ha0)
      (Set.mem_Ici.2 hc0) (hac.le.trans hqc.le)
    exact lt_of_le_of_lt hm hbrc
  have hcDb : c ∈ isoDr (Muon.DetEquiv.rW (Muon.emaW b)) γin γout :=
    ⟨hc0, hbrc⟩
  have hmonob := (lem_app_iso_comparison_i hrb hγin hγout).2.2.1 s hs
  have hlo : a < isoRoot (Muon.DetEquiv.rW (Muon.emaW b)) γin γout s := by
    by_contra hn
    have hm := hmonob.monotoneOn hqbD haDb (le_of_not_gt hn)
    linarith
  have hhi : isoRoot (Muon.DetEquiv.rW (Muon.emaW b)) γin γout s < c := by
    by_contra hn
    have hm := hmonob.monotoneOn hcDb hqbD (le_of_not_gt hn)
    linarith
  rw [Real.dist_eq]
  dsimp [a, c] at hlo hhi
  rw [abs_lt]
  constructor <;> linarith

private lemma pf5c_Lw_summable {b q : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hq : 0 ≤ q) :
    Summable (fun j : ℕ => Muon.emaW b j *
      Muon.DetEquiv.J (Muon.emaW b j ^ 2 * q)) := by
  have hw := pf5c_weightSeq hb0 hb1
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hw.2.1
  · exact mul_nonneg (hw.1 j)
      (Muon.DetEquiv.lem_app_de_scalar_i.2.2.1 _
        (mul_nonneg (sq_nonneg _) hq)).1.le
  · exact mul_le_of_le_one_right (hw.1 j)
      (Muon.DetEquiv.lem_app_de_scalar_i.2.2.1 _
        (mul_nonneg (sq_nonneg _) hq)).2

private lemma pf5c_Lw_antitone {b q₁ q₂ : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hq₁ : 0 ≤ q₁) (hqq : q₁ ≤ q₂) :
    Muon.DetEquiv.Lw (Muon.emaW b) q₂ ≤ Muon.DetEquiv.Lw (Muon.emaW b) q₁ := by
  have hw := pf5c_weightSeq hb0 hb1
  unfold Muon.DetEquiv.Lw
  refine Summable.tsum_le_tsum (fun j => ?_)
    (pf5c_Lw_summable hb0 hb1 (hq₁.trans hqq)) (pf5c_Lw_summable hb0 hb1 hq₁)
  refine mul_le_mul_of_nonneg_left ?_ (hw.1 j)
  exact Muon.DetEquiv.lem_app_de_scalar_i.2.1.antitoneOn
    (Set.mem_Ici.2 (mul_nonneg (sq_nonneg _) hq₁))
    (Set.mem_Ici.2 (mul_nonneg (sq_nonneg _) (hq₁.trans hqq)))
    (mul_le_mul_of_nonneg_left hqq (sq_nonneg _))

private lemma pf5c_Lw_zero (q : ℝ) :
    Muon.DetEquiv.Lw (Muon.emaW 0) q = Muon.DetEquiv.J q := by
  unfold Muon.DetEquiv.Lw
  rw [tsum_eq_single 0]
  · simp [Muon.emaW]
  · intro j hj
    simp [Muon.emaW, hj]

private lemma pf5c_Lw_root_tendsto {γin γout s : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s) :
    Tendsto (fun b : ℝ =>
      Muon.DetEquiv.Lw (Muon.emaW b)
        (isoRoot (Muon.DetEquiv.rW (Muon.emaW b)) γin γout s))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Muon.DetEquiv.Lw (Muon.emaW 0)
        (isoRoot (Muon.DetEquiv.rW (Muon.emaW 0)) γin γout s))) := by
  let q0 := isoRoot (Muon.DetEquiv.rW (Muon.emaW 0)) γin γout s
  have hq0 : 0 < q0 := pf5c_root_pos (pf5c_isoLink le_rfl zero_lt_one) hγin hγout hs
  have hJ : ContinuousAt Muon.DetEquiv.J q0 :=
    Muon.DetEquiv.lem_app_de_scalar_i.1.continuousAt (Ici_mem_nhds hq0)
  have hqT := pf5c_root_tendsto hγin hγout hs
  rw [pf5c_Lw_zero]
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := (Metric.continuousAt_iff.1 hJ) (ε / 4) (by positivity)
  let e := min (δ / 2) (q0 / 2)
  let a := q0 - e
  let c := q0 + e
  have he : 0 < e := by dsimp [e]; positivity
  have heδ : e < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have heq : e ≤ q0 / 2 := min_le_right _ _
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hJa : dist (Muon.DetEquiv.J a) (Muon.DetEquiv.J q0) < ε / 4 := by
    apply hδ
    rw [Real.dist_eq]
    dsimp [a]
    ring_nf
    rw [abs_neg, abs_of_pos he]
    exact heδ
  have hJc : dist (Muon.DetEquiv.J c) (Muon.DetEquiv.J q0) < ε / 4 := by
    apply hδ
    rw [Real.dist_eq]
    dsimp [c]
    ring_nf
    rw [abs_of_pos he]
    exact heδ
  have hLa := pf5c_Lw_tendsto a ha0
  have hLc := pf5c_Lw_tendsto c hc0
  have hqev := Metric.tendsto_nhds.1 hqT e he
  filter_upwards [hLa.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 4)),
    hLc.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 4)), hqev,
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with b hba hbc hbq hb
  rw [Real.dist_eq] at hba hbc hbq ⊢
  rw [Real.dist_eq] at hJa hJc
  have hb1 : b < 1 := hb.2.trans (by norm_num)
  have hqa : a < isoRoot (Muon.DetEquiv.rW (Muon.emaW b)) γin γout s := by
    dsimp [a] at hbq ⊢
    rw [abs_lt] at hbq
    linarith
  have hqc : isoRoot (Muon.DetEquiv.rW (Muon.emaW b)) γin γout s < c := by
    dsimp [c] at hbq ⊢
    rw [abs_lt] at hbq
    linarith
  have hqr0 : 0 ≤ isoRoot (Muon.DetEquiv.rW (Muon.emaW b)) γin γout s :=
    (pf5c_root_pos (pf5c_isoLink hb.1.le hb1) hγin hγout hs).le
  have hlow := pf5c_Lw_antitone (q₁ := isoRoot
    (Muon.DetEquiv.rW (Muon.emaW b)) γin γout s) (q₂ := c) hb.1.le hb1 hqr0 hqc.le
  have hupp := pf5c_Lw_antitone (q₁ := a) (q₂ := isoRoot
    (Muon.DetEquiv.rW (Muon.emaW b)) γin γout s) hb.1.le hb1 ha0 hqa.le
  rw [abs_lt] at hba hbc hJa hJc ⊢
  constructor <;> linarith

private lemma pf5c_isoGb_tendsto {γin γout s : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s) :
    Tendsto (fun b : ℝ => isoGb b γin γout s) (𝓝[>] (0 : ℝ))
      (𝓝 (isoGb 0 γin γout s)) := by
  simpa [isoGb, qIso] using
    (pf5c_root_tendsto hγin hγout hs).mul (pf5c_Lw_root_tendsto hγin hγout hs)

private lemma pf5c_isoGb_contOn {b γin γout : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hγin : 0 < γin) (hγout : 0 < γout) :
    ContinuousOn (isoGb b γin γout) (Ioi 0) := by
  have hr := pf5c_isoLink hb0 hb1
  have hq := (lem_app_iso_comparison_i hr hγin hγout).2.2.2.2.1
  have hL := (Muon.DetEquiv.lem_app_de_scalar_ii (pf5c_weightSeq hb0 hb1)).2.2.2.1
  have hmap : MapsTo (isoRoot (Muon.DetEquiv.rW (Muon.emaW b)) γin γout)
      (Ioi 0) (Ici 0) := fun s hs => Set.mem_Ici.2
        (pf5c_root_pos hr hγin hγout hs).le
  unfold isoGb qIso
  exact hq.mul (hL.comp hq hmap)

private lemma pf5c_dominator_integrable {γin γout ϱ : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) (hϱ : 0 < ϱ) :
    IntegrableOn (fun u : ℝ => γin * γout / (ϱ + u ^ 2)) (Ioi 0) := by
  let c := Real.sqrt ϱ
  have hc : 0 < c := Real.sqrt_pos.2 hϱ
  have hc2 : c ^ 2 = ϱ := Real.sq_sqrt hϱ.le
  have hi : Integrable (fun u : ℝ => (1 + (c⁻¹ * u) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hc.ne')
  refine ((hi.const_mul (γin * γout / ϱ)).integrableOn).congr_fun (fun u _ => ?_)
    measurableSet_Ioi
  dsimp [c] at hc2 ⊢
  field_simp [hϱ.ne', hc.ne']
  nlinarith

theorem prop_app_iso_limit_order_i {γin γout ϱ : ℝ} (hγin : 0 < γin) (hγout : 0 < γout)
    (hϱ : 0 < ϱ) :
    Tendsto (fun β : ℝ => dIso β γin γout ϱ) (𝓝[>] (0 : ℝ)) (𝓝 (dIso 0 γin γout ϱ)) := by
  unfold dIso
  refine Tendsto.const_mul _ ?_
  refine tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (fun u : ℝ => γin * γout / (ϱ + u ^ 2)) ?_ ?_
    (pf5c_dominator_integrable hγin hγout hϱ) ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with b hb
    have hb1 : b < 1 := hb.2.trans (by norm_num)
    have hc := pf5c_isoGb_contOn hb.1.le hb1 hγin hγout
    refine (hc.comp (continuousOn_const.add (continuousOn_id.pow 2))
      ?_).aestronglyMeasurable
      measurableSet_Ioi
    intro u hu
    exact Set.mem_Ioi.2 (add_pos_of_pos_of_nonneg hϱ (sq_nonneg u))
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with b hb
    have hb1 : b < 1 := hb.2.trans (by norm_num)
    exact ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => by
      have hs : 0 < ϱ + u ^ 2 := add_pos_of_pos_of_nonneg hϱ (sq_nonneg u)
      have hbd := (prop_app_iso_zero_i hb.1.le hb1 hγin hγout).1 _ hs
      rw [Real.norm_eq_abs, abs_of_pos hbd.1]
      exact hbd.2.trans (min_le_right _ _))
  · exact ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu =>
      pf5c_isoGb_tendsto hγin hγout
        (add_pos_of_pos_of_nonneg hϱ (sq_nonneg u)))

private lemma pf5c_g_integrable :
    IntegrableOn (fun u : ℝ => min (1 : ℝ) (1 / u ^ 2)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (g := fun _ : ℝ => 1)
      (integrableOn_const measure_Ioc_lt_top.ne)
      ((measurable_const.min (measurable_const.div (measurable_id.pow_const 2))).aestronglyMeasurable) ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (by positivity))]
      exact min_le_left _ _)
  · have hi : IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
    refine Integrable.mono' hi
      ((measurable_const.min (measurable_const.div (measurable_id.pow_const 2))).aestronglyMeasurable) ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => by
      have hu0 : 0 < u := one_pos.trans hu
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (by positivity))]
      refine (min_le_right _ _).trans (le_of_eq ?_)
      rw [Real.rpow_neg hu0.le, Real.rpow_two]
      ring)

private lemma pf5c_g_integral :
    ∫ u in Ioi (0 : ℝ), min (1 : ℝ) (1 / u ^ 2) = 2 := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1),
    setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (pf5c_g_integrable.mono_set Set.Ioc_subset_Ioi_self)
      (pf5c_g_integrable.mono_set (Set.Ioi_subset_Ioi zero_le_one))]
  have hsmall : ∫ u in Set.Ioc (0 : ℝ) 1, min (1 : ℝ) (1 / u ^ 2) = 1 := by
    calc
      ∫ u in Set.Ioc (0 : ℝ) 1, min (1 : ℝ) (1 / u ^ 2) =
          ∫ _u in Set.Ioc (0 : ℝ) 1, (1 : ℝ) :=
        setIntegral_congr_fun measurableSet_Ioc (fun u hu => by
          rw [min_eq_left]
          rw [le_div_iff₀ (sq_pos_of_pos hu.1)]
          nlinarith [sq_le_sq₀ hu.1.le zero_le_one |>.2 hu.2])
      _ = 1 := by simp
  have hlarge : ∫ u in Set.Ioi (1 : ℝ), min (1 : ℝ) (1 / u ^ 2) = 1 := by
    calc
      ∫ u in Set.Ioi (1 : ℝ), min (1 : ℝ) (1 / u ^ 2) =
          ∫ u in Set.Ioi (1 : ℝ), u ^ (-2 : ℝ) :=
        setIntegral_congr_fun measurableSet_Ioi (fun u hu => by
          rw [min_eq_right]
          · rw [Real.rpow_neg (one_pos.trans hu).le, Real.rpow_two]
            ring
          · rw [div_le_one (sq_pos_of_pos (one_pos.trans hu))]
            simpa using
              ((sq_le_sq₀ zero_le_one (one_pos.trans hu).le).2 (Set.mem_Ioi.1 hu).le))
      _ = 1 := by
        rw [integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) one_pos]
        norm_num
  rw [hsmall, hlarge]
  norm_num

private lemma pf5c_C1_bound :
    Cbeta 0 1 1 ≤ Real.sqrt 2 / Real.pi * 2 := by
  have hf := (prop_app_iso_zero_i (β := (0 : ℝ)) le_rfl zero_lt_one one_pos one_pos).2.1
  have hg := pf5c_g_integrable
  have hmono : ∫ u in Ioi (0 : ℝ), isoGb 0 1 1 (u ^ 2) ≤
      ∫ u in Ioi (0 : ℝ), min (1 : ℝ) (1 / u ^ 2) := by
    refine setIntegral_mono_on hf hg measurableSet_Ioi (fun u hu => ?_)
    have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
    have h := (prop_app_iso_zero_i (β := (0 : ℝ)) le_rfl zero_lt_one one_pos one_pos).1 _ hu2
    simpa [isoK] using h.2
  unfold Cbeta
  rw [pf5c_g_integral] at hmono
  have hk : 0 ≤ Real.sqrt 2 / Real.pi := div_nonneg (Real.sqrt_nonneg 2) Real.pi_pos.le
  have hh := mul_le_mul_of_nonneg_left hmono hk
  convert hh using 1 <;> ring

private lemma pf5c_isoGb_antitone {b γin γout s₁ s₂ : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hγin : 0 < γin) (hγout : 0 < γout)
    (hs₁ : 0 < s₁) (hss : s₁ ≤ s₂) :
    isoGb b γin γout s₂ ≤ isoGb b γin γout s₁ := by
  have hr := pf5c_isoLink hb0 hb1
  have hq := (lem_app_iso_comparison_i hr hγin hγout).2.2.2.2.2.antitoneOn
    (Set.mem_Ioi.2 hs₁) (Set.mem_Ioi.2 (hs₁.trans_le hss)) hss
  have hq₂ : 0 ≤ isoRoot (Muon.DetEquiv.rW (Muon.emaW b)) γin γout s₂ :=
    (pf5c_root_pos hr hγin hγout (hs₁.trans_le hss)).le
  unfold isoGb qIso
  exact (lem_app_iso_weights_v hb0 hb1).2.2.monotoneOn
    (Set.mem_Ici.2 hq₂) (Set.mem_Ici.2 (hq₂.trans hq)) hq

private lemma pf5c_Qlevel_r {b q : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hq : 0 ≤ q) :
    isoQlevel b (Muon.DetEquiv.rW (Muon.emaW b) q) = q := by
  have hex : ∃ z : ℝ, 0 ≤ z ∧ Muon.DetEquiv.rW (Muon.emaW b) z =
      Muon.DetEquiv.rW (Muon.emaW b) q := ⟨q, hq, rfl⟩
  unfold isoQlevel
  rw [dif_pos hex]
  have hz := hex.choose_spec
  exact (pf5c_isoLink hb0 hb1).2.1.injOn
    (Set.mem_Ici.2 hz.1) (Set.mem_Ici.2 hq) hz.2

private lemma pf5c_square_W {γ m : ℝ} (hm : m ≤ γ) :
    isoWm γ γ m = γ - m := by
  unfold isoWm
  rw [show (γ - m) * (γ - m) = (γ - m) ^ 2 by ring]
  exact Real.sqrt_sq (by linarith)

private lemma pf5c_square_W_deriv {γ m : ℝ} (hm : m < γ) :
    deriv (isoWm γ γ) m = -1 := by
  have he : ∀ᶠ x in 𝓝 m, isoWm γ γ x = γ - x := by
    filter_upwards [Iio_mem_nhds hm] with x hx
    exact pf5c_square_W hx.le
  rw [Filter.EventuallyEq.deriv_eq he]
  simp

private lemma pf5c_Lambda_nonneg (q : ℝ) (hq : 0 ≤ q) :
    0 ≤ isoLambda 0 q := by
  have hm := (lem_app_iso_weights_iv (β := (0 : ℝ)) le_rfl zero_lt_one).2.2.2.1
  have hz : isoLambda 0 0 = 0 := by simp [isoLambda]
  calc 0 = isoLambda 0 0 := hz.symm
    _ ≤ isoLambda 0 q := hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq) hq

private lemma pf5c_Ilevel_nonneg (m : ℝ) : 0 ≤ isoIlevel 0 m := by
  have hQ : 0 ≤ isoQlevel 0 m := by
    unfold isoQlevel
    split_ifs with h
    · exact h.choose_spec.1
    · exact le_rfl
  have hL : 0 < Muon.DetEquiv.Lw (Muon.emaW 0) (isoQlevel 0 m) := by
    rw [pf5c_Lw_zero]
    exact (Muon.DetEquiv.lem_app_de_scalar_i.2.2.1 _ hQ).1
  have hLam : 0 ≤ isoLambdaB 0 m := by
    unfold isoLambdaB
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact pf5c_Lambda_nonneg _ hQ
  unfold isoIlevel
  positivity

private lemma pf5c_dIso_le_Cbeta {γ ϱ : ℝ} (hγ : 0 < γ) (hϱ : 0 ≤ ϱ) :
    dIso 0 γ γ ϱ ≤ Cbeta 0 γ γ := by
  have h0 := (prop_app_iso_zero_i (β := (0 : ℝ)) le_rfl zero_lt_one hγ hγ).2.1
  have hϱint : IntegrableOn (fun u : ℝ => isoGb 0 γ γ (ϱ + u ^ 2)) (Ioi 0) := by
    rcases hϱ.eq_or_lt with h | h
    · subst h
      simpa using h0
    · refine Integrable.mono' (pf5c_dominator_integrable hγ hγ h) ?_ ?_
      · have hc := pf5c_isoGb_contOn le_rfl zero_lt_one hγ hγ
        exact (hc.comp (continuousOn_const.add (continuousOn_id.pow 2))
          (fun u hu => Set.mem_Ioi.2 (add_pos_of_pos_of_nonneg h (sq_nonneg u))))
          |>.aestronglyMeasurable measurableSet_Ioi
      · exact ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => by
          have hs : 0 < ϱ + u ^ 2 := add_pos_of_pos_of_nonneg h (sq_nonneg u)
          have hb := (prop_app_iso_zero_i (β := (0 : ℝ)) le_rfl zero_lt_one hγ hγ).1 _ hs
          rw [Real.norm_eq_abs, abs_of_pos hb.1]
          exact hb.2.trans (min_le_right _ _))
  have hmono : ∫ u in Ioi (0 : ℝ), isoGb 0 γ γ (ϱ + u ^ 2) ≤
      ∫ u in Ioi (0 : ℝ), isoGb 0 γ γ (u ^ 2) := by
    refine setIntegral_mono_on hϱint h0 measurableSet_Ioi (fun u hu => ?_)
    exact pf5c_isoGb_antitone le_rfl zero_lt_one hγ hγ
      (sq_pos_of_pos hu) (by linarith)
  unfold dIso Cbeta
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-- `prop:app-iso-limit-order`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.3619–3632):
```latex
\begin{proposition}[Order of limits at positive ridge]\label{prop:app-iso-limit-order}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item For fixed $\gin,\gout>0$ and $\ridge>0$,
$\lim_{\bmom\downarrow0}\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gin,\gout)=\mathfrak d_{\mathrm{iso}}(\ridge;0,\gin,\gout)$.
\item For $\gamma\ge2$ and $\ridge\ge0$,
\[
\Big|\gamma\,\mathfrak d_{\mathrm{iso}}(\ridge;0,\gamma,\gamma)-\frac1{\sqrt\pi}\Big|\le\frac{\sqrt2\,\big(1+\sqrt{2\pi}/2+\sqrt\ridge\big)}{\pi\gamma} .
\]
\item For every $\ridge>0$,
$\lim_{\gamma\to\infty}\lim_{\bmom\downarrow0}\gamma\,\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gamma,\gamma)=\pi^{-1/2}$,
whereas for every fixed $\bmom\in(0,1)$, $\gamma\,\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gamma,\gamma)\to\infty$ as $\gamma\to\infty$.
\end{enumerate}
\end{proposition}
```

Part (ii): the explicit bound for `γ ≥ 2` at all `ϱ ≥ 0`. 
Relocated here from `Muon.Isotropic.ZeroRidge` by the coordinator (2026-10-24): its proof needs results of this
module, which imports the original one. -/
theorem prop_app_iso_limit_order_ii {γ ϱ : ℝ} (hγ : 2 ≤ γ) (hϱ : 0 ≤ ϱ) :
    |γ * dIso 0 γ γ ϱ - 1 / Real.sqrt Real.pi|
      ≤ Real.sqrt 2 * (1 + Real.sqrt (2 * Real.pi) / 2 + Real.sqrt ϱ) / (Real.pi * γ) := by
  let z := Real.sqrt 2
  let t := Real.sqrt Real.pi
  let S := Real.sqrt (2 * Real.pi)
  let A := 1 + S / 2
  let K := z * (A + Real.sqrt ϱ) / (Real.pi * γ)
  have hγp : 0 < γ := by linarith
  have hz : 0 < z := by dsimp [z]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have ht2 : t ^ 2 = Real.pi := by dsimp [t]; exact Real.sq_sqrt Real.pi_pos.le
  have hz2 : z ^ 2 = 2 := by dsimp [z]; exact Real.sq_sqrt (by norm_num)
  have hSz : S = z * t := by
    dsimp [S, z, t]
    exact Real.sqrt_mul (by norm_num) _
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC1 : Cbeta 0 1 1 ≤ z / Real.pi * A := by
    have hc := pf5c_C1_bound
    have h2A : (2 : ℝ) ≤ A := by
      dsimp [A]
      have : 2 ≤ S := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 * Real.pi by positivity),
        Real.pi_gt_three]
      linarith
    have hk : 0 ≤ z / Real.pi := div_nonneg hz.le Real.pi_pos.le
    calc
      Cbeta 0 1 1 ≤ z / Real.pi * 2 := by simpa [z] using hc
      _ ≤ z / Real.pi * A := mul_le_mul_of_nonneg_left h2A hk
  have hC1pos : 0 ≤ Cbeta 0 1 1 :=
    (prop_app_iso_zero_i (β := (0 : ℝ)) le_rfl zero_lt_one one_pos one_pos).2.2.1.le
  have hform := prop_app_iso_exact (show (1 : ℝ) ≤ γ by linarith)
  have hzeroForm : γ * Cbeta 0 γ γ =
      1 / t - 1 / (t * γ) + Cbeta 0 1 1 / γ := by
    rw [hform]
    dsimp [t]
    field_simp [hγp.ne', ht.ne']
  have hbase : 1 / (t * γ) ≤ z * A / (Real.pi * γ) := by
    rw [div_le_div_iff₀ (mul_pos ht hγp) (mul_pos Real.pi_pos hγp)]
    have he : z * A * t = z * t + Real.pi := by
      dsimp [A]
      rw [hSz]
      nlinarith
    calc
      1 * (Real.pi * γ) = Real.pi * γ := one_mul _
      _ ≤ (z * t + Real.pi) * γ := by
        apply mul_le_mul_of_nonneg_right _ hγp.le
        nlinarith only [mul_pos hz ht]
      _ = z * A * (t * γ) := by rw [← he]; ring
  have hupper : γ * dIso 0 γ γ ϱ - 1 / t ≤ K := by
    have hd := mul_le_mul_of_nonneg_left (pf5c_dIso_le_Cbeta hγp hϱ) hγp.le
    rw [hzeroForm] at hd
    have hcdiv := div_le_div_of_nonneg_right hC1 hγp.le
    have hAt : z * A / (Real.pi * γ) ≤ K := by
      dsimp [K]
      have hsqr : 0 ≤ Real.sqrt ϱ := Real.sqrt_nonneg _
      gcongr
      linarith
    have hneg : 0 ≤ 1 / (t * γ) := by positivity
    have he : z / Real.pi * A / γ = z * A / (Real.pi * γ) := by field_simp
    rw [he] at hcdiv
    linarith
  have hlowerI : 1 / t - K ≤ γ * dIso 0 γ γ ϱ := by
    rcases hϱ.eq_or_lt with hϱ0 | hϱp
    · subst hϱ0
      have hd0 : dIso 0 γ γ 0 = Cbeta 0 γ γ := by simp [dIso, Cbeta]
      rw [hd0, hzeroForm]
      have hk0 : K = z * A / (Real.pi * γ) := by simp [K]
      rw [hk0]
      have hc0 : 0 ≤ Cbeta 0 1 1 / γ := div_nonneg hC1pos hγp.le
      linarith [hbase]
    · let q := qIso 0 γ γ ϱ
      let H := psiIso 0 γ γ ϱ
      have hr0 := pf5c_isoLink (b := (0 : ℝ)) le_rfl zero_lt_one
      have hqp : 0 < q := pf5c_root_pos hr0 hγp hγp hϱp
      obtain ⟨hqD, hqG⟩ :=
        (lem_app_iso_comparison_i hr0 hγp hγp).2.2.2.1 ϱ hϱp
      have hlink := (lem_app_iso_weights_i (β := (0 : ℝ)) le_rfl zero_lt_one).2.2.2 rfl
      have hHphi : H = isoPhi q := by
        unfold H psiIso q qIso
        exact hlink.1 _ hqp.le
      have hH0 : 0 < H := by rw [hHphi]; exact (lem_app_iso_gaussian_ii.2.2 q hqp).1
      have hH1 : H < 1 := by rw [hHphi]; exact (lem_app_iso_gaussian_ii.2.2 q hqp).2
      have hQ : isoQlevel 0 H = q := by
        rw [hHphi, ← hlink.1 q hqp.le]
        exact pf5c_Qlevel_r le_rfl zero_lt_one hqp.le
      have hM : isoMLevel 0 γ γ ϱ = H := by simp [isoMLevel, hϱp.ne', H]
      have hp := (lem_app_iso_participation_ii (β := (0 : ℝ)) (γin := γ) (γout := γ)
        (ϱ := ϱ) rfl (by simp; linarith) hγp hγp hϱ).1
      rw [hM] at hp
      have hLB : isoLambdaB 0 H = isoLambda 0 q := by
        unfold isoLambdaB
        rw [if_neg, hQ]
        rintro ⟨-, he⟩
        linarith
      have hW : isoWm γ γ H = γ - H := pf5c_square_W (by linarith)
      have hint : 0 ≤ ∫ m in (0 : ℝ)..H,
          -deriv (isoWm γ γ) m * isoIlevel 0 m := by
        apply intervalIntegral.integral_nonneg hH0.le
        intro m hm
        rw [pf5c_square_W_deriv (by linarith [hm.2])]
        simpa using pf5c_Ilevel_nonneg m
      have hpart : (1 / 2) * (γ - H) * isoLambda 0 q ≤
          ∫ u in Ioi (0 : ℝ), isoGb 0 γ γ (ϱ + u ^ 2) := by
        unfold isoIt at hp
        rw [hW, hLB] at hp
        linarith
      have htail := (lem_app_iso_weights_iv (β := (0 : ℝ)) le_rfl zero_lt_one).2.2.1 q hqp
      have hpow : q ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt q := by
        rw [Real.rpow_neg hqp.le, ← Real.sqrt_eq_rpow]
        simp [one_div]
      rw [hpow] at htail
      have hclose : ϱ * q = (γ - H) ^ 2 := by
        unfold isoG at hqG
        dsimp [q, H, qIso, psiIso] at hqG ⊢
        nlinarith
      have hsqr : Real.sqrt ϱ * Real.sqrt q = γ - H := by
        have hsquare : (Real.sqrt ϱ * Real.sqrt q) ^ 2 = (γ - H) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hϱ, Real.sq_sqrt hqp.le, hclose]
        have hn : 0 ≤ Real.sqrt ϱ * Real.sqrt q :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        have hr : 0 ≤ γ - H := by linarith
        exact (sq_eq_sq₀ hn hr).mp hsquare
      have hdiv : (γ - H) / Real.sqrt q = Real.sqrt ϱ := by
        apply (div_eq_iff (Real.sqrt_pos.2 hqp).ne').2
        exact hsqr.symm
      have hlam : S - 2 / Real.sqrt q ≤ isoLambda 0 q := by
        have he : 2 / Real.sqrt q = 2 * (1 / Real.sqrt q) := by ring
        rw [he]
        linarith [htail.2]
      have hγH : 0 ≤ γ - H := by linarith
      have hmul := mul_le_mul_of_nonneg_left hlam
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hγH)
      have hIlow : (1 / 2) * (γ - 1) * S - Real.sqrt ϱ ≤
          ∫ u in Ioi (0 : ℝ), isoGb 0 γ γ (ϱ + u ^ 2) := by
        calc
          (1 / 2) * (γ - 1) * S - Real.sqrt ϱ
              ≤ (1 / 2) * (γ - H) * S - Real.sqrt ϱ := by
                have : γ - 1 ≤ γ - H := by linarith
                gcongr
          _ = (1 / 2) * (γ - H) * (S - 2 / Real.sqrt q) := by
                rw [← hdiv]
                ring
          _ ≤ (1 / 2) * (γ - H) * isoLambda 0 q := hmul
          _ ≤ ∫ u in Ioi (0 : ℝ), isoGb 0 γ γ (ϱ + u ^ 2) := hpart
      have hscale := mul_le_mul_of_nonneg_left hIlow
        (show 0 ≤ z / (Real.pi * γ) by positivity)
      have hmain : z / (Real.pi * γ) * ((1 / 2) * (γ - 1) * S - Real.sqrt ϱ) =
          1 / t - 1 / (t * γ) - z * Real.sqrt ϱ / (Real.pi * γ) := by
        rw [hSz, ← ht2]
        field_simp [hγp.ne', ht.ne']
        linear_combination (t * (γ - 1)) * hz2
      rw [hmain] at hscale
      have hcoeff : γ * (Real.sqrt 2 / (Real.pi * γ * γ)) = z / (Real.pi * γ) := by
        dsimp [z]
        field_simp [hγp.ne', Real.pi_pos.ne']
      have hdscale : γ * dIso 0 γ γ ϱ =
          z / (Real.pi * γ) * ∫ u in Ioi (0 : ℝ), isoGb 0 γ γ (ϱ + u ^ 2) := by
        unfold dIso
        rw [← mul_assoc, hcoeff]
      have herr : 1 / (t * γ) + z * Real.sqrt ϱ / (Real.pi * γ) ≤ K := by
        dsimp [K]
        rw [show z * (A + Real.sqrt ϱ) / (Real.pi * γ) =
          z * A / (Real.pi * γ) + z * Real.sqrt ϱ / (Real.pi * γ) by ring]
        linarith [hbase]
      rw [hdscale]
      linarith
  change |γ * dIso 0 γ γ ϱ - 1 / t| ≤ K
  exact abs_le.2 ⟨by linarith, hupper⟩

/-- `prop:app-iso-limit-order`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.3619–3632):
```latex
\begin{proposition}[Order of limits at positive ridge]\label{prop:app-iso-limit-order}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item For fixed $\gin,\gout>0$ and $\ridge>0$,
$\lim_{\bmom\downarrow0}\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gin,\gout)=\mathfrak d_{\mathrm{iso}}(\ridge;0,\gin,\gout)$.
\item For $\gamma\ge2$ and $\ridge\ge0$,
\[
\Big|\gamma\,\mathfrak d_{\mathrm{iso}}(\ridge;0,\gamma,\gamma)-\frac1{\sqrt\pi}\Big|\le\frac{\sqrt2\,\big(1+\sqrt{2\pi}/2+\sqrt\ridge\big)}{\pi\gamma} .
\]
\item For every $\ridge>0$,
$\lim_{\gamma\to\infty}\lim_{\bmom\downarrow0}\gamma\,\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gamma,\gamma)=\pi^{-1/2}$,
whereas for every fixed $\bmom\in(0,1)$, $\gamma\,\mathfrak d_{\mathrm{iso}}(\ridge;\bmom,\gamma,\gamma)\to\infty$ as $\gamma\to\infty$.
\end{enumerate}
\end{proposition}
```

Part (iii): the iterated limit `lim_{γ→∞} lim_{β↓0}` at positive ridge, where the inner limit
exists for each `γ > 0` (witnessed by `L`), and the reverse-regime divergence for `β ∈ (0,1)`. 
Relocated here from `Muon.Isotropic.ZeroRidge` by the coordinator (2026-10-24): its proof needs results of this
module, which imports the original one. -/
theorem prop_app_iso_limit_order_iii {ϱ : ℝ} (hϱ : 0 < ϱ) :
    (∃ L : ℝ → ℝ,
      (∀ γ : ℝ, 0 < γ →
        Tendsto (fun β : ℝ => γ * dIso β γ γ ϱ) (𝓝[>] (0 : ℝ)) (𝓝 (L γ))) ∧
      Tendsto L atTop (𝓝 (1 / Real.sqrt Real.pi))) ∧
    (∀ β : ℝ, 0 < β → β < 1 →
      Tendsto (fun γ : ℝ => γ * dIso β γ γ ϱ) atTop atTop) := by
  refine ⟨⟨fun γ => γ * dIso 0 γ γ ϱ, ?_, ?_⟩, fun β hβ0 hβ1 =>
    (cor_app_iso_fixed_ridge_ii hβ0 hβ1 hϱ).1⟩
  · intro γ hγ
    exact (prop_app_iso_limit_order_i hγ hγ hϱ).const_mul γ
  · set c : ℝ := Real.sqrt 2 * (1 + Real.sqrt (2 * Real.pi) / 2 + Real.sqrt ϱ) / Real.pi with hc
    have hb : Tendsto (fun γ : ℝ => c / γ) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with γ hγ
    rw [Real.norm_eq_abs]
    refine (prop_app_iso_limit_order_ii hγ hϱ.le).trans (le_of_eq ?_)
    rw [hc]; field_simp

end Muon.Isotropic

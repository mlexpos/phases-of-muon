import Muon.Isotropic.ZeroRidge
import Muon.Isotropic.Closure
import Muon.Isotropic.Helpers
import Muon.Foundations.Conventions
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Appendix F: lag kernel, participation representation and layer averaging (task L-F.9)

Snapshot `cr-2026-10-23`. Source: `sections/05b-isotropic/section.tex`. Labels of this package:
`lem:app-iso-lag`(i), `lem:app-iso-kernel-bounds`, `prop:app-iso-vol-representation`,
`lem:app-iso-averaging`, `lem:app-iso-low-levels`, and the diagonal values `eqn:app-iso-diagonal`
(which fix the continuous extension in the divided-difference definitions).
Card: `sections/05b-isotropic/CARD.md` §2, §3, §5 (L-F.9), §6 (items 11, 16).

Reuse (no project object is restated): `rW`, `Lw` of `Muon.DetEquiv`; `Muon.emaW`, `Muon.sPow`
(`sw_p`) of `Muon.Foundations.Conventions`; `isoPhi`, `isoN`, `isoC'`, `isoEslope`, `isoEbar`,
`isoGammaCirc` of `Muon.Isotropic.Helpers`; `qIso`, `isoQlevel` of `Muon.Isotropic.ZeroRidge`
(`q(-s)` and `Q_m = r^{-1}(m)`); `isoRoot` of `Muon.Isotropic.Closure`.
Objects that exist only in the lag section of the paper (`b_ℓ`, `e_ℓ`, `X_ℓ`, `Z_ℓ`, `Δ_ℓ`,
`𝔨_{1,ℓ}`, `C̄_{1,ℓ}`, `D`, `𝒵`, `𝒳`, `Δ̂`, `𝖠`, `𝗃`, `u_ϱ`, `ν⋆`, `Π`, `𝖬_k`, `L_k`) are
defined here, once. Convention: the lag objects take the aspect ratio `γ = N/B` and the
square-case roots `q = qIso β γ γ s`.

Every theorem is a statement only (`sorry`) except the diagonal identities, which are unfolding
of the definitions.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open Muon.DetEquiv (rW Lw)

noncomputable section

namespace Muon.Isotropic

/-! ## Constants of the lag section -/

/-- Catalan's constant `𝖦 = ∑_{n≥0} (-1)^n/(2n+1)^2 = 0.91596…` (`lem:app-iso-averaging`(ii)).
Catalan's constant is absent from Mathlib, so it is given as its defining series. -/
def isoCatalan : ℝ := ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2

/-- `𝖬_1 = 28 ζ(3)/π²` (`lem:app-iso-averaging`(ii)): the closed form of the first moment `𝖬_1 = 𝔼⋆τ`. -/
def isoM1 : ℝ := 28 * (riemannZeta 3).re / Real.pi ^ 2

/-- `𝖬_2 = 2π²` (`lem:app-iso-averaging`(ii)): the closed form of the second moment `𝔼⋆τ²`. -/
def isoM2 : ℝ := 2 * Real.pi ^ 2

/-- `𝖬_3 = 1488 ζ(5)/π²` (`lem:app-iso-averaging`(ii)): the closed form of `𝔼⋆τ³`. -/
def isoM3 : ℝ := 1488 * (riemannZeta 5).re / Real.pi ^ 2

/-- `L̄_1` of `lem:app-iso-low-levels`(ii). -/
def isoLbar1 (β : ℝ) : ℝ :=
  1 / (2 * Real.log (1 / β)) * ((isoM1 + 1) / (1 - β ^ 2) + isoEbar β * isoM2 / 2)

/-- `L̄_2` of `lem:app-iso-low-levels`(ii). -/
def isoLbar2 (β : ℝ) : ℝ :=
  1 / (4 * Real.log (1 / β) ^ 2) *
    ((isoM2 + 2 * isoM1 + 2) / (1 - β ^ 2) + isoEbar β * isoM3 / 3)

/-! ## Residual participation, slope and the divided-difference kernels -/

/-- `𝖠(y) = γ − r_β(y)` (residual participation, `section.tex` l.2400–2402, "For $y>0$ put"
with $\mathsf e_\bmom(y)$, $\mathsf A(y)$, $\mathsf j(y)$ of `eqn:app-iso-diagonal`). -/
def isoResid (β γ y : ℝ) : ℝ := γ - rW (Muon.emaW β) y

/-- `𝗃(y) = 𝖠(y) + 2𝖾_β(y)` with `𝖾_β(y) = y r_β'(y)` = `isoEslope β y`
(`section.tex` l.2400–2402). -/
def isoWeightJ (β γ y : ℝ) : ℝ := isoResid β γ y + 2 * isoEslope β y

/-- `u_ϱ(y) = (1 − ϱ y/𝖠(y)²)^{-1/2}` (`prop:app-iso-vol-representation`, `section.tex` l.2400–2402). -/
def isoUlev (β γ ϱ y : ℝ) : ℝ :=
  (1 - ϱ * y / isoResid β γ y ^ 2) ^ (-(1 / 2 : ℝ))

/-- `D(y,z) = (r(y) − r(z))/((y − z)√(yz))`, with the diagonal value `r'(y)/√(y·y)` of the
continuous extension (`section.tex` l.2400–2427, "extended continuously to $y=z$"). -/
def isoDivDiff (β y z : ℝ) : ℝ :=
  if y = z then deriv (rW (Muon.emaW β)) y / Real.sqrt (y * y)
  else (rW (Muon.emaW β) y - rW (Muon.emaW β) z) / ((y - z) * Real.sqrt (y * z))

/-- `𝒵(y,z) = √(yz)(r(y) − r(z))/(y − z)`, with the diagonal value `𝒵(y,y) = 𝖾_β(y)`
(`eqn:app-iso-diagonal`). -/
def isoZkern (β y z : ℝ) : ℝ :=
  if y = z then isoEslope β y
  else Real.sqrt (y * z) * (rW (Muon.emaW β) y - rW (Muon.emaW β) z) / (y - z)

/-- `𝒳(y,z) = (z r(y) − y r(z))/(z − y)`, with the diagonal value `𝒳(y,y) = r(y) − 𝖾_β(y)`
(`eqn:app-iso-diagonal`). -/
def isoXkern (β y z : ℝ) : ℝ :=
  if y = z then rW (Muon.emaW β) y - isoEslope β y
  else (z * rW (Muon.emaW β) y - y * rW (Muon.emaW β) z) / (z - y)

/-- `Δ̂(y,z) = (1 − 𝒳(y,z)/γ)² − (𝒵(y,z)/γ)²` (`section.tex` l.2400–2402). -/
def isoDeltaHat (β γ y z : ℝ) : ℝ :=
  (1 - isoXkern β y z / γ) ^ 2 - (isoZkern β y z / γ) ^ 2

/-- `𝖠_∨(y,z) = max(𝖠(y), 𝖠(z))` (`section.tex` l.2400–2402). -/
def isoAvee (β γ y z : ℝ) : ℝ := max (isoResid β γ y) (isoResid β γ z)

/-- The function `δ ↦ δ/(2 sinh(δ/2))`, extended by its value `1` at `δ = 0`
(`lem:app-iso-kernel-bounds`(ii), "by continuity"). -/
def isoSinhRatio (δ : ℝ) : ℝ :=
  if δ = 0 then 1 else δ / (2 * Real.sinh (δ / 2))

/-! ## The lag kernel of the isotropic case -/

/-- `b_ℓ` of `eqn:app-pl-UV` at the roots `q = q(−s)`, `q' = q(−s')` of the square case
(`lem:app-iso-lag`): `∑_{j≥0} 𝔼 β^ℓ w_j² g²/((1+q w_j² g²)(1+β^{2ℓ} q' w_j² g²))`, `w_j = emaW β j`.
Terms with `w_j = 0` vanish, so the sum over all `j : ℕ` is the sum over `{j | 0 < w_j}`. -/
def isoLagB (β γ : ℝ) (ℓ : ℕ) (s s' : ℝ) : ℝ :=
  ∑' j : ℕ, ∫ g, β ^ ℓ * Muon.emaW β j ^ 2 * g ^ 2 /
    ((1 + qIso β γ γ s * Muon.emaW β j ^ 2 * g ^ 2) *
      (1 + β ^ (2 * ℓ) * qIso β γ γ s' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1)

/-- `e_ℓ` of `eqn:app-pl-UV` at `q = q(−s)`, `q' = q(−s')`:
`∑_{j≥0} 𝔼 β^{2ℓ} w_j⁴ g⁴/((1+q w_j² g²)(1+β^{2ℓ} q' w_j² g²))`. -/
def isoLagE (β γ : ℝ) (ℓ : ℕ) (s s' : ℝ) : ℝ :=
  ∑' j : ℕ, ∫ g, β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * g ^ 4 /
    ((1 + qIso β γ γ s * Muon.emaW β j ^ 2 * g ^ 2) *
      (1 + β ^ (2 * ℓ) * qIso β γ γ s' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1)

/-- `X_ℓ = q q' e_ℓ/γ` (`lem:app-iso-lag`). -/
def isoLagX (β γ : ℝ) (ℓ : ℕ) (s s' : ℝ) : ℝ :=
  qIso β γ γ s * qIso β γ γ s' * isoLagE β γ ℓ s s' / γ

/-- `Z_ℓ = √(q q') b_ℓ/γ` (`lem:app-iso-lag`). -/
def isoLagZ (β γ : ℝ) (ℓ : ℕ) (s s' : ℝ) : ℝ :=
  Real.sqrt (qIso β γ γ s * qIso β γ γ s') * isoLagB β γ ℓ s s' / γ

/-- `Δ_ℓ = (1 − X_ℓ)² − Z_ℓ²` (`lem:app-iso-lag`). -/
def isoLagDelta (β γ : ℝ) (ℓ : ℕ) (s s' : ℝ) : ℝ :=
  (1 - isoLagX β γ ℓ s s') ^ 2 - isoLagZ β γ ℓ s s' ^ 2

/-- The row lag kernel `𝔨_{1,ℓ}(s,s') = b_ℓ q q'/(γ³ Δ_ℓ)` at `μ_1 = … = μ_N = 1`
(`lem:app-iso-lag`(ii), explicit form; its identification with `eqn:app-pl-rowkernel` is
`lem:app-iso-lag`(ii), not stated in this package). -/
def lagKernel (β γ : ℝ) (ℓ : ℕ) (s s' : ℝ) : ℝ :=
  isoLagB β γ ℓ s s' * qIso β γ γ s * qIso β γ γ s' / (γ ^ 3 * isoLagDelta β γ ℓ s s')

/-- The row lag coefficient `C̄_{1,ℓ}(ϱ) = (4/π²) ∫_0^∞∫_0^∞ 𝔨_{1,ℓ}(ϱ+x², ϱ+y²) dx dy`
(`eqn:app-iso-lag-integral`, `lem:app-iso-lag`(ii)). -/
def lagCoeff (β γ ϱ : ℝ) (ℓ : ℕ) : ℝ :=
  4 / Real.pi ^ 2 * ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), lagKernel β γ ℓ (ϱ + x ^ 2) (ϱ + y ^ 2)

/-- `Q_{ψ(ϱ)}`: `q(−ϱ)` for `ϱ > 0` and `Q_γ = r_β^{-1}(γ)` for `ϱ = 0`
(`section.tex` l.2375–2380, "so that $Q_{\psi(\ridge)}=q(-\ridge)$ for $\ridge>0$ and $Q_{\psi(0)}=Q_\gamma$"). -/
def isoQpsi (β γ ϱ : ℝ) : ℝ :=
  if 0 < ϱ then qIso β γ γ ϱ else isoQlevel β γ

/-! ## Layer averaging: the measure `ν⋆` and the pair map `Π` -/

/-- The density `(π²·2sinh((a+c)/2))^{-1}` on `(0,∞)²` (`lem:app-iso-averaging`). -/
def isoNuBase : Measure (ℝ × ℝ) :=
  ((volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))).withDensity
    (fun p => ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))))

/-- The measure `ν⋆` on `{+,−} × (0,∞)²`, the two copies carrying the same density
(`lem:app-iso-averaging`). The first coordinate is the copy label (`true` = `+`). -/
def isoNuStar : Measure (Bool × ℝ × ℝ) :=
  (Measure.count : Measure Bool).prod isoNuBase

/-- `Π_+(s;a,c) = (s e^a, s e^{−c})` for `true`, `Π_−(s;a,c) = (s e^{−c}, s e^a)` for `false`
(`lem:app-iso-averaging`). -/
def isoPairMap (s : ℝ) (w : Bool × ℝ × ℝ) : ℝ × ℝ :=
  if w.1 then (s * Real.exp w.2.1, s * Real.exp (-w.2.2))
  else (s * Real.exp (-w.2.2), s * Real.exp w.2.1)

/-! ## Theorems -/

/-- `eqn:app-iso-diagonal`, the displayed equation of `section.tex`, snapshot `cr-2026-10-23`. Its diagonal values are the definitions of `isoZkern`, `isoXkern`, `isoDeltaHat` at `y = z`; the identity is an unfolding.
LaTeX (`sections/05b-isotropic/section.tex`):
```latex
\begin{equation}\label{eqn:app-iso-diagonal}
\begin{gathered}
\mathcal Z(y,y)=\mathsf e_\bmom(y),\qquad
\mathcal X(y,y)=r(y)-\mathsf e_\bmom(y),\\
\gamma^2\widehat\Delta(y,y)=\big(\mathsf A(y)+\mathsf e_\bmom(y)\big)^2-\mathsf e_\bmom(y)^2=\mathsf A(y)\,\mathsf j(y).
\end{gathered}
\end{equation}
```
-/
theorem eqn_app_iso_diagonal_i {β : ℝ} (y : ℝ) :
    isoZkern β y y = isoEslope β y := by
  simp [isoZkern]

/-- `eqn:app-iso-diagonal`, the displayed equation of `section.tex`, snapshot `cr-2026-10-23`. Its diagonal values are the definitions of `isoZkern`, `isoXkern`, `isoDeltaHat` at `y = z`; the identity is an unfolding.
LaTeX (`sections/05b-isotropic/section.tex`):
```latex
\begin{equation}\label{eqn:app-iso-diagonal}
\begin{gathered}
\mathcal Z(y,y)=\mathsf e_\bmom(y),\qquad
\mathcal X(y,y)=r(y)-\mathsf e_\bmom(y),\\
\gamma^2\widehat\Delta(y,y)=\big(\mathsf A(y)+\mathsf e_\bmom(y)\big)^2-\mathsf e_\bmom(y)^2=\mathsf A(y)\,\mathsf j(y).
\end{gathered}
\end{equation}
```
-/
theorem eqn_app_iso_diagonal_ii {β : ℝ} (y : ℝ) :
    isoXkern β y y = rW (Muon.emaW β) y - isoEslope β y := by
  simp [isoXkern]

/-- `eqn:app-iso-diagonal`, the displayed equation of `section.tex`, snapshot `cr-2026-10-23`. Its diagonal values are the definitions of `isoZkern`, `isoXkern`, `isoDeltaHat` at `y = z`; the identity is an unfolding.
LaTeX (`sections/05b-isotropic/section.tex`):
```latex
\begin{equation}\label{eqn:app-iso-diagonal}
\begin{gathered}
\mathcal Z(y,y)=\mathsf e_\bmom(y),\qquad
\mathcal X(y,y)=r(y)-\mathsf e_\bmom(y),\\
\gamma^2\widehat\Delta(y,y)=\big(\mathsf A(y)+\mathsf e_\bmom(y)\big)^2-\mathsf e_\bmom(y)^2=\mathsf A(y)\,\mathsf j(y).
\end{gathered}
\end{equation}
```
-/
theorem eqn_app_iso_diagonal_iii {β γ : ℝ} (hγ : γ ≠ 0) (y : ℝ) :
    γ ^ 2 * isoDeltaHat β γ y y = isoResid β γ y * isoWeightJ β γ y := by
  simp only [isoDeltaHat, eqn_app_iso_diagonal_i, eqn_app_iso_diagonal_ii, isoResid, isoWeightJ]
  field_simp
  ring

/-- Private helper (task P-F.9.P1): `q(-s) ≥ 0`. -/
private lemma qIso_nonneg_P1 (β γ s : ℝ) : 0 ≤ qIso β γ γ s := by
  unfold qIso isoRoot
  split_ifs with h
  · have hm := h.choose_spec.1
    simp only [isoDr, Set.mem_setOf_eq] at hm
    exact hm.1
  · exact le_rfl

/-- Private helper (task P-F.9.P1): summability of `w_j^p` for `p ≠ 0`. -/
private lemma summable_emaW_pow_P1 {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {p : ℕ} (hp : p ≠ 0) :
    Summable (fun j : ℕ => Muon.emaW β j ^ p) := by
  have h : (fun j : ℕ => Muon.emaW β j ^ p) = fun j : ℕ => (1 - β) ^ p * (β ^ p) ^ j := by
    funext j
    unfold Muon.emaW
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j p]
  rw [h]
  exact (summable_geometric_of_lt_one (pow_nonneg hβ0 p) (pow_lt_one₀ hβ0 hβ1 hp)).mul_left _

/-- Private helper (task P-F.9.P1): a pointwise bound on the integrand of the lag series. -/
private lemma lag_term_int_le_P1 {c a b : ℝ} (k : ℕ) (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hk : ∀ g : ℝ, 0 ≤ g ^ k) :
    0 ≤ ∫ g, c * g ^ k / ((1 + a * g ^ 2) * (1 + b * g ^ 2)) ∂(gaussianReal 0 1) ∧
    ∫ g, c * g ^ k / ((1 + a * g ^ 2) * (1 + b * g ^ 2)) ∂(gaussianReal 0 1) ≤
      ∫ g, c * g ^ k ∂(gaussianReal 0 1) := by
  have key : ∀ g : ℝ, 0 ≤ c * g ^ k / ((1 + a * g ^ 2) * (1 + b * g ^ 2)) ∧
      c * g ^ k / ((1 + a * g ^ 2) * (1 + b * g ^ 2)) ≤ c * g ^ k := by
    intro g
    have hg : 0 ≤ g ^ 2 := sq_nonneg g
    have h1 : 0 ≤ a * g ^ 2 := mul_nonneg ha hg
    have h2 : 0 ≤ b * g ^ 2 := mul_nonneg hb hg
    have hD1 : 1 ≤ (1 + a * g ^ 2) * (1 + b * g ^ 2) := by
      nlinarith [mul_nonneg h1 h2]
    have hN : 0 ≤ c * g ^ k := mul_nonneg hc (hk g)
    exact ⟨div_nonneg hN (by linarith), div_le_self hN hD1⟩
  refine ⟨integral_nonneg fun g => (key g).1, ?_⟩
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => (key g).1)
    ((Muon.Foundations.gaussian_integrable_pow k).const_mul c)
    (Filter.Eventually.of_forall fun g => (key g).2)

/-- Private helper (task P-F.9.P1): bounds for a series of nonnegative terms. -/
private lemma tsum_bounds_P1 (I K : ℕ → ℝ) (hK : Summable K) (hI0 : ∀ j, 0 ≤ I j)
    (hIK : ∀ j, I j ≤ K j) : 0 ≤ ∑' j, I j ∧ ∑' j, I j ≤ ∑' j, K j :=
  ⟨tsum_nonneg hI0, Summable.tsum_le_tsum hIK (Summable.of_nonneg_of_le hI0 hIK hK) hK⟩

/-- Private helper (task P-F.9.P1): integrability of a continuous function dominated by `C g^k`. -/
private lemma integrable_cont_le_P1 {f : ℝ → ℝ} (hf : Continuous f) (C : ℝ) (k : ℕ)
    (h : ∀ g, |f g| ≤ C * g ^ k) : Integrable f (gaussianReal 0 1) :=
  Integrable.mono' ((Muon.Foundations.gaussian_integrable_pow k).const_mul C)
    hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => by simpa [Real.norm_eq_abs] using h g)

/-- Private helper (task P-F.9.P1): integrability of the lag integrands. -/
private lemma lag_integrable_P1 {c a b : ℝ} (k : ℕ) (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hk : ∀ g : ℝ, 0 ≤ g ^ k) :
    Integrable (fun g : ℝ => c * g ^ k / ((1 + a * g ^ 2) * (1 + b * g ^ 2))) (gaussianReal 0 1) := by
  have hcont : Continuous fun g : ℝ => c * g ^ k / ((1 + a * g ^ 2) * (1 + b * g ^ 2)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro g; positivity
  refine integrable_cont_le_P1 hcont c k (fun g => ?_)
  have hg : 0 ≤ g ^ 2 := sq_nonneg g
  have h1 : 0 ≤ a * g ^ 2 := mul_nonneg ha hg
  have h2 : 0 ≤ b * g ^ 2 := mul_nonneg hb hg
  have hD1 : 1 ≤ (1 + a * g ^ 2) * (1 + b * g ^ 2) := by nlinarith [mul_nonneg h1 h2]
  have hN : 0 ≤ c * g ^ k := mul_nonneg hc (hk g)
  rw [abs_of_nonneg (div_nonneg hN (by positivity))]
  exact div_le_self hN hD1

/-- Private helper (task P-F.9.P1): integrability of `a g²/(1+a g²)`. -/
private lemma frac_integrable_P1 {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun g : ℝ => a * g ^ 2 / (1 + a * g ^ 2)) (gaussianReal 0 1) := by
  have hcont : Continuous fun g : ℝ => a * g ^ 2 / (1 + a * g ^ 2) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro g; positivity
  refine integrable_cont_le_P1 hcont a 2 (fun g => ?_)
  have h1 : 0 ≤ a * g ^ 2 := by positivity
  rw [abs_of_nonneg (div_nonneg h1 (by positivity))]
  exact div_le_self h1 (by linarith)

/-- Private helper (task P-F.9.P1): `0 ≤ E[a g²/(1+a g²)] ≤ a`. -/
private lemma frac_int_le_P1 {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ ∫ g, a * g ^ 2 / (1 + a * g ^ 2) ∂(gaussianReal 0 1) ∧
    ∫ g, a * g ^ 2 / (1 + a * g ^ 2) ∂(gaussianReal 0 1) ≤ a := by
  refine ⟨integral_nonneg fun g => div_nonneg (by positivity) (by positivity), ?_⟩
  have h := integral_mono_of_nonneg (f := fun g : ℝ => a * g ^ 2 / (1 + a * g ^ 2))
    (g := fun g : ℝ => a * g ^ 2)
    (Filter.Eventually.of_forall fun g => div_nonneg (by positivity) (by positivity))
    ((Muon.Foundations.gaussian_integrable_pow 2).const_mul a)
    (Filter.Eventually.of_forall fun g => div_le_self (by positivity) (by
      have : 0 ≤ a * g ^ 2 := by positivity
      linarith))
  rwa [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one] at h

/-- Private helper (task P-F.9.P1): `r_β(q)` as a series of Gaussian expectations. -/
private lemma rW_eq_tsum_P1 (β q : ℝ) :
    rW (Muon.emaW β) q = ∑' j : ℕ, ∫ g, q * Muon.emaW β j ^ 2 * g ^ 2 /
      (1 + q * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1) := by
  unfold rW Muon.DetEquiv.Fw Muon.DetEquiv.J
  rw [← tsum_mul_left]
  congr 1; funext j
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1; funext g; ring

/-- Private helper (task P-F.9.P1): the pointwise AM-GM step. -/
private lemma amgm_P1 {u v k p : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hk : 0 ≤ k) (hp : 0 ≤ p)
    (huv : u * v = (k * p) ^ 2) :
    (u * v + k * p) / ((1 + u) * (1 + v)) ≤ 1 / 2 * (u / (1 + u) + v / (1 + v)) := by
  have hs : 0 ≤ k * p := mul_nonneg hk hp
  have h2 : 2 * (k * p) ≤ u + v := by nlinarith [sq_nonneg (u - v), sq_nonneg (u + v - 2 * (k * p))]
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h1' : (0 : ℝ) < 1 + v := by linarith
  have hR : 1 / 2 * (u / (1 + u) + v / (1 + v)) =
      (1 / 2 * (u * (1 + v) + v * (1 + u))) / ((1 + u) * (1 + v)) := by
    field_simp
  rw [hR]
  exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)

/-- Private helper (task P-F.9.P1): the shift `w_{j+ℓ} = β^ℓ w_j`. -/
private lemma emaW_add_P1 (β : ℝ) (j ℓ : ℕ) : Muon.emaW β (j + ℓ) = β ^ ℓ * Muon.emaW β j := by
  unfold Muon.emaW; ring

/-- Private helper (task P-F.9.P1): `X_ℓ + Z_ℓ < 1` in the unnormalised form
`q q' e_ℓ + √(q q') b_ℓ < γ`, by AM-GM and `r_β(q), r_β(q') < γ`. -/
private lemma XZ_lt_P1 {β γ q q' : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℕ)
    (hq : 0 ≤ q) (hq' : 0 ≤ q') (hrq : rW (Muon.emaW β) q < γ) (hrq' : rW (Muon.emaW β) q' < γ) :
    q * q' * (∑' j : ℕ, ∫ g, β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * g ^ 4 /
      ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1)) +
    Real.sqrt (q * q') * (∑' j : ℕ, ∫ g, β ^ ℓ * Muon.emaW β j ^ 2 * g ^ 2 /
      ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1)) < γ := by
  have hβ0' : (0 : ℝ) ≤ β := hβ0.le
  have hw2 : ∀ j : ℕ, 0 ≤ Muon.emaW β j ^ 2 := fun j => sq_nonneg _
  have hs2 := summable_emaW_pow_P1 hβ0' hβ1 (by norm_num : (2 : ℕ) ≠ 0)
  have hs4 := summable_emaW_pow_P1 hβ0' hβ1 (by norm_num : (4 : ℕ) ≠ 0)
  have hcq : 0 ≤ β ^ (2 * ℓ) * q' := mul_nonneg (pow_nonneg hβ0' _) hq'
  -- summability of the E and B series
  have hEb : ∀ j : ℕ,
      0 ≤ ∫ g, β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * g ^ 4 /
          ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
            (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1) ∧
      ∫ g, β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * g ^ 4 /
          ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
            (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1) ≤
        β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * 3 := by
    intro j
    obtain ⟨h1, h2⟩ := lag_term_int_le_P1 (c := β ^ (2 * ℓ) * Muon.emaW β j ^ 4)
      (a := q * Muon.emaW β j ^ 2) (b := β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2) 4
      (mul_nonneg (pow_nonneg hβ0' _) (by positivity)) (mul_nonneg hq (hw2 j))
      (mul_nonneg hcq (hw2 j)) (fun g => by positivity)
    rw [integral_const_mul, Muon.Foundations.gaussian_moment_four] at h2
    exact ⟨h1, h2⟩
  have hBb : ∀ j : ℕ,
      0 ≤ ∫ g, β ^ ℓ * Muon.emaW β j ^ 2 * g ^ 2 /
          ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
            (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1) ∧
      ∫ g, β ^ ℓ * Muon.emaW β j ^ 2 * g ^ 2 /
          ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
            (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1) ≤
        β ^ ℓ * Muon.emaW β j ^ 2 := by
    intro j
    obtain ⟨h1, h2⟩ := lag_term_int_le_P1 (c := β ^ ℓ * Muon.emaW β j ^ 2)
      (a := q * Muon.emaW β j ^ 2) (b := β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2) 2
      (mul_nonneg (pow_nonneg hβ0' ℓ) (hw2 j)) (mul_nonneg hq (hw2 j))
      (mul_nonneg hcq (hw2 j)) (fun g => by positivity)
    rw [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one] at h2
    exact ⟨h1, h2⟩
  have hEs : Summable (fun j : ℕ => ∫ g, β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * g ^ 4 /
      ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1)) :=
    Summable.of_nonneg_of_le (fun j => (hEb j).1) (fun j => (hEb j).2)
      ((hs4.mul_left (β ^ (2 * ℓ))).mul_right 3 |>.congr fun j => by ring)
  have hBs : Summable (fun j : ℕ => ∫ g, β ^ ℓ * Muon.emaW β j ^ 2 * g ^ 2 /
      ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1)) :=
    Summable.of_nonneg_of_le (fun j => (hBb j).1) (fun j => (hBb j).2)
      (hs2.mul_left (β ^ ℓ))
  -- the `a` and `c` series
  have hA : ∀ (t : ℝ) (j : ℕ), 0 ≤ t → 0 ≤ ∫ g, t * Muon.emaW β j ^ 2 * g ^ 2 /
      (1 + t * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1) ∧
      ∫ g, t * Muon.emaW β j ^ 2 * g ^ 2 /
        (1 + t * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1) ≤ t * Muon.emaW β j ^ 2 :=
    fun t j ht => frac_int_le_P1 (mul_nonneg ht (hw2 j))
  have hAs : ∀ t : ℝ, 0 ≤ t → Summable (fun j : ℕ => ∫ g, t * Muon.emaW β j ^ 2 * g ^ 2 /
      (1 + t * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1)) := fun t ht =>
    Summable.of_nonneg_of_le (fun j => (hA t j ht).1) (fun j => (hA t j ht).2) (hs2.mul_left t)
  have hCs : Summable (fun j : ℕ => ∫ g, β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2 /
      (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1)) :=
    Summable.of_nonneg_of_le (fun j => (hA _ j hcq).1) (fun j => (hA _ j hcq).2)
      (hs2.mul_left _)
  -- the shift: `∑_j c_j ≤ r_β(q')`
  have hshift : ∑' j : ℕ, ∫ g, β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2 /
      (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1) ≤
      rW (Muon.emaW β) q' := by
    rw [rW_eq_tsum_P1]
    set A' : ℕ → ℝ := fun k => ∫ g, q' * Muon.emaW β k ^ 2 * g ^ 2 /
      (1 + q' * Muon.emaW β k ^ 2 * g ^ 2) ∂(gaussianReal 0 1) with hA'
    have hcA : ∀ j : ℕ, (∫ g, β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2 /
        (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1)) = A' (j + ℓ) := by
      intro j
      simp only [hA', emaW_add_P1]
      congr 1; funext g; ring_nf
    simp_rw [hcA]
    have hsum := (hAs q' hq')
    have := (hsum.sum_add_tsum_nat_add ℓ)
    have hnn : 0 ≤ ∑ i ∈ Finset.range ℓ, A' i :=
      Finset.sum_nonneg fun i _ => (hA q' i hq').1
    simp only [hA'] at this ⊢
    linarith
  -- the pointwise estimate, termwise in `j`
  have hterm : ∀ j : ℕ, q * q' * (∫ g, β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * g ^ 4 /
      ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1)) +
    Real.sqrt (q * q') * (∫ g, β ^ ℓ * Muon.emaW β j ^ 2 * g ^ 2 /
      ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1)) ≤
    ((∫ g, q * Muon.emaW β j ^ 2 * g ^ 2 /
      (1 + q * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1)) +
     (∫ g, β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2 /
      (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1))) / 2 := by
    intro j
    have i1 := lag_integrable_P1 (c := β ^ (2 * ℓ) * Muon.emaW β j ^ 4)
      (a := q * Muon.emaW β j ^ 2) (b := β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2) 4
      (mul_nonneg (pow_nonneg hβ0' _) (by positivity)) (mul_nonneg hq (hw2 j))
      (mul_nonneg hcq (hw2 j)) (fun g => by positivity)
    have i2 := lag_integrable_P1 (c := β ^ ℓ * Muon.emaW β j ^ 2)
      (a := q * Muon.emaW β j ^ 2) (b := β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2) 2
      (mul_nonneg (pow_nonneg hβ0' ℓ) (hw2 j)) (mul_nonneg hq (hw2 j))
      (mul_nonneg hcq (hw2 j)) (fun g => by positivity)
    have ia := frac_integrable_P1 (mul_nonneg hq (hw2 j))
    have ic := frac_integrable_P1 (mul_nonneg hcq (hw2 j))
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _) (i2.const_mul _),
      ← integral_add ia ic, ← integral_div]
    refine integral_mono ((i1.const_mul _).add (i2.const_mul _)) ((ia.add ic).div_const 2)
      (fun g => ?_)
    have hg : 0 ≤ g ^ 2 := sq_nonneg g
    have hu : 0 ≤ q * Muon.emaW β j ^ 2 * g ^ 2 := by positivity
    have hv : 0 ≤ β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2 := by positivity
    have hk : 0 ≤ Real.sqrt (q * q') := Real.sqrt_nonneg _
    have hp : 0 ≤ β ^ ℓ * Muon.emaW β j ^ 2 * g ^ 2 := by positivity
    have huv : (q * Muon.emaW β j ^ 2 * g ^ 2) * (β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2) =
        (Real.sqrt (q * q') * (β ^ ℓ * Muon.emaW β j ^ 2 * g ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hq hq')]
      ring
    have hamgm := amgm_P1 hu hv hk hp huv
    have hD : (1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2) ≠ 0 := by positivity
    have hL : q * q' * (β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * g ^ 4 /
        ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
          (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2))) +
        Real.sqrt (q * q') * (β ^ ℓ * Muon.emaW β j ^ 2 * g ^ 2 /
        ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
          (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2))) =
        ((q * Muon.emaW β j ^ 2 * g ^ 2) * (β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2) +
          Real.sqrt (q * q') * (β ^ ℓ * Muon.emaW β j ^ 2 * g ^ 2)) /
        ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
          (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2)) := by
      field_simp
    show _ ≤ _
    simp only []
    rw [hL]
    linarith
  -- sum up
  have hlhs : Summable (fun j : ℕ => q * q' * (∫ g, β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * g ^ 4 /
      ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1)) +
    Real.sqrt (q * q') * (∫ g, β ^ ℓ * Muon.emaW β j ^ 2 * g ^ 2 /
      ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1))) :=
    (hEs.mul_left _).add (hBs.mul_left _)
  have hrhs := ((hAs q hq).add hCs).div_const 2
  have hle := Summable.tsum_le_tsum hterm hlhs hrhs
  rw [(hEs.mul_left _).tsum_add (hBs.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_div_const, (hAs q hq).tsum_add hCs, ← rW_eq_tsum_P1] at hle
  linarith

/-- `lem:app-iso-lag`(i), snapshot `cr-2026-10-23`. Part (i): the bounds on `b_ℓ`, `e_ℓ`, `X_ℓ`, `Z_ℓ`, `Δ_ℓ` for `s, s' > 0`, `β ∈ (0,1)`, `γ = N/B > 0`.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Isotropic lag response]\label{lem:app-iso-lag}
Let $\bmom\in(0,1)$, $\Nin=\Nout=N$ and $\gamma=N/B$. For $s,s'>0$ put
$q\defeq q(-s)$ and $q'\defeq q(-s')$, let $b_\ell$ and $e_\ell$ be the numbers of
\cref{eqn:app-pl-UV} for these roots, and put
\[
X_\ell\defeq\frac{q\,q'\,e_\ell}\gamma,\qquad Z_\ell\defeq\frac{\sqrt{qq'}\,b_\ell}\gamma,\qquad
\Delta_\ell\defeq(1-X_\ell)^2-Z_\ell^2\qquad(\ell\ge0).
\]
\begin{enumerate}[label=(\roman*)]
\item $0\le b_\ell\le\bmom^\ell\sw2$, $0\le e_\ell\le3\bmom^{2\ell}\sw4$, $0\le X_\ell<1$ and $0<\Delta_\ell\le1$.
\item The row lag kernel \cref{eqn:app-pl-rowkernel} at $\mu_1=\dots=\mu_N=1$ is the
same for every row and equals
\[
\mathfrak k_{1,\ell}(s,s')=\frac{b_\ell\,q\,q'}{\gamma^3\,\Delta_\ell}\ \ge\ \frac{b_\ell\,q\,q'}{\gamma^3},
\]
and for every $\ridge\ge0$ the row lag coefficient is
\begin{equation}\label{eqn:app-iso-lag-integral}
\overline C_{1,\ell}(\ridge)=\frac4{\pi^2}\int_0^\infty\!\!\int_0^\infty\mathfrak k_{1,\ell}(\ridge+x^2,\ridge+y^2)\,\dif x\,\dif y ,
\end{equation}
where $\overline C_{1,\ell}(0)$ is the limit of \cref{prop:app-iso-vol-momentum}(ii).
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_lag_i {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s') (ℓ : ℕ) :
    (0 ≤ isoLagB β γ ℓ s s' ∧ isoLagB β γ ℓ s s' ≤ β ^ ℓ * Muon.sPow β 2) ∧
    (0 ≤ isoLagE β γ ℓ s s' ∧ isoLagE β γ ℓ s s' ≤ 3 * β ^ (2 * ℓ) * Muon.sPow β 4) ∧
    (0 ≤ isoLagX β γ ℓ s s' ∧ isoLagX β γ ℓ s s' < 1) ∧
    (0 < isoLagDelta β γ ℓ s s' ∧ isoLagDelta β γ ℓ s s' ≤ 1) := by
  have hβ0' : (0 : ℝ) ≤ β := hβ0.le
  have hq := qIso_nonneg_P1 β γ s
  have hq' := qIso_nonneg_P1 β γ s'
  -- `b_ℓ`: each term is at most `β^ℓ w_j² g²`, and `∫ g² = 1`.
  have hB : 0 ≤ isoLagB β γ ℓ s s' ∧ isoLagB β γ ℓ s s' ≤ β ^ ℓ * Muon.sPow β 2 := by
    have hI : ∀ j : ℕ,
        0 ≤ ∫ g, β ^ ℓ * Muon.emaW β j ^ 2 * g ^ 2 /
            ((1 + qIso β γ γ s * Muon.emaW β j ^ 2 * g ^ 2) *
              (1 + β ^ (2 * ℓ) * qIso β γ γ s' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1) ∧
        ∫ g, β ^ ℓ * Muon.emaW β j ^ 2 * g ^ 2 /
            ((1 + qIso β γ γ s * Muon.emaW β j ^ 2 * g ^ 2) *
              (1 + β ^ (2 * ℓ) * qIso β γ γ s' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1) ≤
          β ^ ℓ * Muon.emaW β j ^ 2 := by
      intro j
      obtain ⟨h1, h2⟩ := lag_term_int_le_P1 (c := β ^ ℓ * Muon.emaW β j ^ 2)
        (a := qIso β γ γ s * Muon.emaW β j ^ 2)
        (b := β ^ (2 * ℓ) * qIso β γ γ s' * Muon.emaW β j ^ 2) 2
        (mul_nonneg (pow_nonneg hβ0' ℓ) (sq_nonneg _)) (mul_nonneg hq (sq_nonneg _))
        (mul_nonneg (mul_nonneg (pow_nonneg hβ0' _) hq') (sq_nonneg _)) (fun g => by positivity)
      rw [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one] at h2
      exact ⟨h1, h2⟩
    have hK : Summable (fun j : ℕ => β ^ ℓ * Muon.emaW β j ^ 2) :=
      (summable_emaW_pow_P1 hβ0' hβ1 (by norm_num : (2 : ℕ) ≠ 0)).mul_left _
    obtain ⟨h0, h1⟩ := tsum_bounds_P1 _ _ hK (fun j => (hI j).1) (fun j => (hI j).2)
    have hsum : ∑' j : ℕ, β ^ ℓ * Muon.emaW β j ^ 2 = β ^ ℓ * Muon.sPow β 2 := by
      unfold Muon.sPow
      rw [tsum_mul_left]
    rw [hsum] at h1
    exact ⟨h0, h1⟩
  -- `e_ℓ`: each term is at most `β^{2ℓ} w_j⁴ g⁴`, and `∫ g⁴ = 3`.
  have hE : 0 ≤ isoLagE β γ ℓ s s' ∧ isoLagE β γ ℓ s s' ≤ 3 * β ^ (2 * ℓ) * Muon.sPow β 4 := by
    have hI : ∀ j : ℕ,
        0 ≤ ∫ g, β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * g ^ 4 /
            ((1 + qIso β γ γ s * Muon.emaW β j ^ 2 * g ^ 2) *
              (1 + β ^ (2 * ℓ) * qIso β γ γ s' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1) ∧
        ∫ g, β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * g ^ 4 /
            ((1 + qIso β γ γ s * Muon.emaW β j ^ 2 * g ^ 2) *
              (1 + β ^ (2 * ℓ) * qIso β γ γ s' * Muon.emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1) ≤
          β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * 3 := by
      intro j
      obtain ⟨h1, h2⟩ := lag_term_int_le_P1 (c := β ^ (2 * ℓ) * Muon.emaW β j ^ 4)
        (a := qIso β γ γ s * Muon.emaW β j ^ 2)
        (b := β ^ (2 * ℓ) * qIso β γ γ s' * Muon.emaW β j ^ 2) 4
        (mul_nonneg (pow_nonneg hβ0' _) (by positivity)) (mul_nonneg hq (sq_nonneg _))
        (mul_nonneg (mul_nonneg (pow_nonneg hβ0' _) hq') (sq_nonneg _)) (fun g => by positivity)
      rw [integral_const_mul, Muon.Foundations.gaussian_moment_four] at h2
      exact ⟨h1, h2⟩
    have hK : Summable (fun j : ℕ => β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * 3) :=
      ((summable_emaW_pow_P1 hβ0' hβ1 (by norm_num : (4 : ℕ) ≠ 0)).mul_left _).mul_right _
    obtain ⟨h0, h1⟩ := tsum_bounds_P1 _ _ hK (fun j => (hI j).1) (fun j => (hI j).2)
    have hsum : ∑' j : ℕ, β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * 3 =
        3 * β ^ (2 * ℓ) * Muon.sPow β 4 := by
      unfold Muon.sPow
      rw [tsum_mul_right, tsum_mul_left]
      ring
    rw [hsum] at h1
    exact ⟨h0, h1⟩
  -- `X_ℓ ≥ 0`.
  have hX0 : 0 ≤ isoLagX β γ ℓ s s' := by
    unfold isoLagX
    exact div_nonneg (mul_nonneg (mul_nonneg hq hq') hE.1) hγ.le
  -- `r_β(q(-t)) < γ`.
  have hlink : IsIsoLink (rW (Muon.emaW β)) := by
    obtain ⟨_, hd, hmono, _⟩ := lem_app_iso_weights_i hβ0' hβ1
    refine ⟨fun q hq => (hd q hq).1.continuousWithinAt, (hmono hβ0).1, ?_⟩
    unfold rW; simp
  have hroot : ∀ t : ℝ, 0 < t → rW (Muon.emaW β) (qIso β γ γ t) < γ := by
    intro t ht
    have hmem := ((lem_app_iso_comparison_i hlink hγ hγ).2.2.2.1 t ht).1
    have h := hmem.2
    rw [min_self] at h
    exact h
  have hXZ := XZ_lt_P1 hβ0 hβ1 ℓ hq hq' (hroot s hs) (hroot s' hs')
  have hsum1 : isoLagX β γ ℓ s s' + isoLagZ β γ ℓ s s' < 1 := by
    unfold isoLagX isoLagZ isoLagE isoLagB
    rw [← add_div, div_lt_one hγ]
    exact hXZ
  have hZ0 : 0 ≤ isoLagZ β γ ℓ s s' := by
    unfold isoLagZ
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hB.1) hγ.le
  have hX1 : isoLagX β γ ℓ s s' < 1 := by linarith
  refine ⟨hB, hE, ⟨hX0, hX1⟩, ?_, ?_⟩
  · have hfac : isoLagDelta β γ ℓ s s' =
        (1 - isoLagX β γ ℓ s s' - isoLagZ β γ ℓ s s') *
          (1 - isoLagX β γ ℓ s s' + isoLagZ β γ ℓ s s') := by
      unfold isoLagDelta; ring
    rw [hfac]
    exact mul_pos (by linarith) (by linarith)
  · unfold isoLagDelta
    nlinarith [sq_nonneg (isoLagZ β γ ℓ s s')]

/-- Private helper (task P-F.9.P2): summability of the per-`j` fraction integrals of `r_β(q)`. -/
private lemma kernel_frac_summable_P2 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    Summable (fun j : ℕ => ∫ g, q * Muon.emaW β j ^ 2 * g ^ 2 /
      (1 + q * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1)) := by
  have hS : Summable (fun j : ℕ => q * Muon.emaW β j ^ 2) :=
    (summable_emaW_pow_P1 hβ0.le hβ1 (p := 2) two_ne_zero).mul_left q
  exact Summable.of_nonneg_of_le
    (fun j => (frac_int_le_P1 (a := q * Muon.emaW β j ^ 2) (mul_nonneg hq (sq_nonneg _))).1)
    (fun j => (frac_int_le_P1 (a := q * Muon.emaW β j ^ 2) (mul_nonneg hq (sq_nonneg _))).2) hS

/-- Private helper (task P-F.9.P2): pointwise partial fraction identity for the `𝒵` kernel. -/
private lemma frac_Z_diff_P2 {w y z g : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    y * w ^ 2 * g ^ 2 / (1 + y * w ^ 2 * g ^ 2) - z * w ^ 2 * g ^ 2 / (1 + z * w ^ 2 * g ^ 2) =
      (y - z) * ((w * g) ^ 2 / ((1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2))) := by
  have hx : 0 ≤ w ^ 2 * g ^ 2 := by positivity
  have h1 : 0 < 1 + y * w ^ 2 * g ^ 2 := by
    have := mul_nonneg (mul_nonneg hy (sq_nonneg w)) (sq_nonneg g); linarith
  have h2 : 0 < 1 + z * w ^ 2 * g ^ 2 := by
    have := mul_nonneg (mul_nonneg hz (sq_nonneg w)) (sq_nonneg g); linarith
  have h1' : 0 < 1 + y * (w * g) ^ 2 := by
    have := mul_nonneg (mul_nonneg hy (sq_nonneg w)) (sq_nonneg g); rw [mul_pow]; linarith
  have h2' : 0 < 1 + z * (w * g) ^ 2 := by
    have := mul_nonneg (mul_nonneg hz (sq_nonneg w)) (sq_nonneg g); rw [mul_pow]; linarith
  rw [mul_pow]
  field_simp
  ring

/-- Private helper (task P-F.9.P2): pointwise partial fraction identity for the `𝒳` kernel. -/
private lemma frac_X_diff_P2 {w y z g : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    z * (y * w ^ 2 * g ^ 2 / (1 + y * w ^ 2 * g ^ 2)) -
        y * (z * w ^ 2 * g ^ 2 / (1 + z * w ^ 2 * g ^ 2)) =
      y * z * (z - y) * ((w * g) ^ 4 / ((1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2))) := by
  have h1 : 0 < 1 + y * w ^ 2 * g ^ 2 := by
    have := mul_nonneg (mul_nonneg hy (sq_nonneg w)) (sq_nonneg g); linarith
  have h2 : 0 < 1 + z * w ^ 2 * g ^ 2 := by
    have := mul_nonneg (mul_nonneg hz (sq_nonneg w)) (sq_nonneg g); linarith
  have h1' : 0 < 1 + y * (w * g) ^ 2 := by
    have := mul_nonneg (mul_nonneg hy (sq_nonneg w)) (sq_nonneg g); rw [mul_pow]; linarith
  have h2' : 0 < 1 + z * (w * g) ^ 2 := by
    have := mul_nonneg (mul_nonneg hz (sq_nonneg w)) (sq_nonneg g); rw [mul_pow]; linarith
  rw [mul_pow]
  field_simp
  ring

/-- Private helper (task P-F.9.P2): the divided-difference kernel `𝒵` as a series, for `y ≠ z`. -/
private lemma isoZkern_series_P2 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {y z : ℝ}
    (hy : 0 < y) (hz : 0 < z) (hyz : y ≠ z) :
    rW (Muon.emaW β) y - rW (Muon.emaW β) z = (y - z) * ∑' j : ℕ, ∫ g,
        (Muon.emaW β j * g) ^ 2 / ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1) := by
  have hsub : y - z ≠ 0 := sub_ne_zero.mpr hyz
  have hF : ∀ j : ℕ,
      (∫ g, y * Muon.emaW β j ^ 2 * g ^ 2 / (1 + y * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1)) -
        (∫ g, z * Muon.emaW β j ^ 2 * g ^ 2 / (1 + z * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1)) =
      (y - z) * ∫ g, (Muon.emaW β j * g) ^ 2 /
        ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2)) ∂(gaussianReal 0 1) := by
    intro j
    rw [← integral_sub (frac_integrable_P1 (a := y * Muon.emaW β j ^ 2) (mul_nonneg hy.le (sq_nonneg _)))
      (frac_integrable_P1 (a := z * Muon.emaW β j ^ 2) (mul_nonneg hz.le (sq_nonneg _))),
      ← integral_const_mul]
    congr 1
    funext g
    exact frac_Z_diff_P2 (w := Muon.emaW β j) hy.le hz.le
  rw [rW_eq_tsum_P1, rW_eq_tsum_P1,
    ← Summable.tsum_sub (kernel_frac_summable_P2 hβ0 hβ1 hy.le)
      (kernel_frac_summable_P2 hβ0 hβ1 hz.le),
    ← tsum_mul_left]
  exact tsum_congr hF

/-- Private helper (task P-F.9.P2): the divided-difference kernel `𝒳` as a series, for `y ≠ z`. -/
private lemma isoXkern_series_P2 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {y z : ℝ}
    (hy : 0 < y) (hz : 0 < z) (hyz : y ≠ z) :
    z * rW (Muon.emaW β) y - y * rW (Muon.emaW β) z = y * z * (z - y) * ∑' j : ℕ, ∫ g,
        (Muon.emaW β j * g) ^ 4 / ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1) := by
  have hG : ∀ j : ℕ,
      z * (∫ g, y * Muon.emaW β j ^ 2 * g ^ 2 / (1 + y * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1)) -
        y * (∫ g, z * Muon.emaW β j ^ 2 * g ^ 2 / (1 + z * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1)) =
      y * z * (z - y) * ∫ g, (Muon.emaW β j * g) ^ 4 /
        ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2)) ∂(gaussianReal 0 1) := by
    intro j
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub ((frac_integrable_P1 (a := y * Muon.emaW β j ^ 2) (mul_nonneg hy.le (sq_nonneg _))).const_mul z)
        ((frac_integrable_P1 (a := z * Muon.emaW β j ^ 2) (mul_nonneg hz.le (sq_nonneg _))).const_mul y),
      ← integral_const_mul]
    congr 1
    funext g
    exact frac_X_diff_P2 (w := Muon.emaW β j) hy.le hz.le
  have e1 : z * rW (Muon.emaW β) y - y * rW (Muon.emaW β) z =
      ∑' j : ℕ, (z * (∫ g, y * Muon.emaW β j ^ 2 * g ^ 2 / (1 + y * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1)) -
        y * (∫ g, z * Muon.emaW β j ^ 2 * g ^ 2 / (1 + z * Muon.emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1))) := by
    rw [rW_eq_tsum_P1, rW_eq_tsum_P1,
      Summable.tsum_sub ((kernel_frac_summable_P2 hβ0 hβ1 hy.le).mul_left z)
        ((kernel_frac_summable_P2 hβ0 hβ1 hz.le).mul_left y),
      tsum_mul_left, tsum_mul_left]
  rw [e1, tsum_congr hG, tsum_mul_left]

/-- `lem:app-iso-kernel-bounds`(i), snapshot `cr-2026-10-23`. Part (i): the two divided-difference kernels as series, for `y ≠ z` (both positive).
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Kernel bounds]\label{lem:app-iso-kernel-bounds}
Let $y\ne z$, put $\delta\defeq\abs{\log(y/z)}$ and $r_\wedge\defeq\min(r(y),r(z))$,
and write $d_j\defeq\emaw jg$ with $g\sim\mathcal N(0,1)$.
\begin{enumerate}[label=(\roman*)]
\item The two kernels are the series
\[
\mathcal Z(y,z)=\sqrt{yz}\sum_{j\ge0}\EE\frac{d_j^2}{(1+yd_j^2)(1+zd_j^2)},\qquad
\mathcal X(y,z)=yz\sum_{j\ge0}\EE\frac{d_j^4}{(1+yd_j^2)(1+zd_j^2)} .
\]
\item $0\le\mathcal Z(y,z)\le\min\big(\bar{\mathsf e}_\bmom\,\delta/(2\sinh(\delta/2)),\ \sw2\sqrt{yz}\big)$, and
$\delta/(2\sinh(\delta/2))\le\min\big(1,(1+\delta)e^{-\delta/2}\big)$.
\item $\max(0,r_\wedge-\bar{\mathsf e}_\bmom)\le\mathcal X(y,z)\le r_\wedge$.
\item $\mathcal X(y,z)+\mathcal Z(y,z)\le\sqrt{r(y)\,r(z)}$.
\item If $\mathsf A(y)>0$ and $\mathsf A(z)>0$, then, with $\mathsf A_\vee=\mathsf A_\vee(y,z)$,
\[
\gamma-\mathcal X\ge\mathsf A_\vee,\qquad
\gamma-\mathcal X-\mathcal Z\ge\max\Big(\mathsf A_\vee-\bar{\mathsf e}_\bmom,\ \frac{\mathsf A_\vee}2\Big)>0,
\]
\[
\mathsf A_\vee\max\Big(\mathsf A_\vee-\bar{\mathsf e}_\bmom,\ \frac{\mathsf A_\vee}2\Big)\le\gamma^2\widehat\Delta(y,z)\le\big(\mathsf A_\vee+\bar{\mathsf e}_\bmom\big)^2 .
\]
\end{enumerate}
By continuity, (ii)--(v) also hold at $y=z$.
\end{lemma}
```
-/
theorem lem_app_iso_kernel_bounds_i {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {y z : ℝ}
    (hy : 0 < y) (hz : 0 < z) (hyz : y ≠ z) :
    isoZkern β y z = Real.sqrt (y * z) * ∑' j : ℕ, ∫ g,
        (Muon.emaW β j * g) ^ 2 / ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1) ∧
    isoXkern β y z = y * z * ∑' j : ℕ, ∫ g,
        (Muon.emaW β j * g) ^ 4 / ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1) := by
  have hyz' : y - z ≠ 0 := sub_ne_zero.mpr hyz
  have hzy' : z - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyz)
  refine ⟨?_, ?_⟩
  · unfold isoZkern
    rw [if_neg hyz, isoZkern_series_P2 hβ0 hβ1 hy hz hyz, mul_left_comm (Real.sqrt (y * z)) (y - z),
      mul_div_cancel_left₀ _ hyz']
  · unfold isoXkern
    rw [if_neg hyz, isoXkern_series_P2 hβ0 hβ1 hy hz hyz, mul_right_comm (y * z) (z - y),
      mul_div_cancel_right₀ _ hzy']

/-! ### Private helpers for `lem_app_iso_kernel_bounds` (ii)-(iii) (task P-F.9.P3) -/

private lemma P3_sinh_le {δ : ℝ} (hδ : 0 ≤ δ) :
    isoSinhRatio δ ≤ min 1 ((1 + δ) * Real.exp (-δ / 2)) := by
  rcases eq_or_lt_of_le hδ with h0 | hpos
  · subst h0
    simp [isoSinhRatio]
  · have hS : 0 < Real.sinh (δ / 2) := Real.sinh_pos_iff.mpr (by linarith)
    have hsinh : δ / 2 ≤ Real.sinh (δ / 2) := Real.self_le_sinh_iff.mpr (by linarith)
    have hsh : 2 * Real.sinh (δ / 2) = Real.exp (δ / 2) - (Real.exp (δ / 2))⁻¹ := by
      rw [Real.sinh_eq, Real.exp_neg]; ring
    have hneg : Real.exp (-δ / 2) = (Real.exp (δ / 2))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    have hE2 : 1 + δ ≤ Real.exp (δ / 2) ^ 2 := by
      have h1 : Real.exp δ = Real.exp (δ / 2) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have := Real.add_one_le_exp δ
      linarith
    have hEpos : 0 < Real.exp (δ / 2) := Real.exp_pos _
    set E := Real.exp (δ / 2) with hEdef
    have hEF : E * E⁻¹ = 1 := mul_inv_cancel₀ hEpos.ne'
    have hF : (1 + δ) * (E⁻¹) ^ 2 ≤ 1 := by
      rw [inv_pow, ← div_eq_mul_inv, div_le_one (pow_pos hEpos 2)]; exact hE2
    have h2S : (0 : ℝ) < 2 * Real.sinh (δ / 2) := by linarith
    have h3 : (1 + δ) * E⁻¹ * (E - E⁻¹) = (1 + δ) - (1 + δ) * (E⁻¹) ^ 2 := by
      linear_combination (1 + δ) * hEF
    unfold isoSinhRatio
    rw [if_neg hpos.ne', hneg]
    refine le_min ?_ ?_
    · rw [div_le_one h2S]; linarith
    · rw [div_le_iff₀ h2S, hsh, h3]; linarith

private lemma P3_emaW_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (j : ℕ) :
    0 < Muon.emaW β j := by
  unfold Muon.emaW
  exact mul_pos (sub_pos.mpr hβ1) (pow_pos hβ0 j)

private lemma P3_K_eq {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    (y - z) / Real.sqrt (y * z) = 2 * Real.sinh (Real.log (y / z) / 2) := by
  rw [Real.sinh_eq, Real.exp_neg]
  have hu2 : Real.exp (Real.log (y / z) / 2) ^ 2 = y / z := by
    rw [sq, ← Real.exp_add, show Real.log (y / z) / 2 + Real.log (y / z) / 2 = Real.log (y / z) by ring,
      Real.exp_log (div_pos hy hz)]
  have hupos : 0 < Real.exp (Real.log (y / z) / 2) := Real.exp_pos _
  generalize Real.exp (Real.log (y / z) / 2) = u at hu2 hupos ⊢
  have hu0 : u ≠ 0 := hupos.ne'
  have hz0 : z ≠ 0 := hz.ne'
  have hy' : y = z * u ^ 2 := by rw [hu2]; field_simp
  have hsq : Real.sqrt (y * z) = z * u := by
    rw [hy', show z * u ^ 2 * z = (z * u) * (z * u) by ring]
    exact Real.sqrt_mul_self (mul_pos hz hupos).le
  rw [hsq, hy']
  field_simp

private lemma P3_abs_K (t : ℝ) :
    |2 * Real.sinh (t / 2)| = 2 * Real.sinh (|t| / 2) := by
  rw [abs_mul, abs_two, Real.abs_sinh, abs_div, abs_two]

private lemma P3_int_w {y z : ℝ} (hy : 0 < y) (hz : 0 < z) (w : ℝ) :
    0 ≤ ∫ g, (w * g) ^ 2 / ((1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2)) ∂(gaussianReal 0 1) ∧
    ∫ g, (w * g) ^ 2 / ((1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2)) ∂(gaussianReal 0 1) ≤ w ^ 2 := by
  have hint : Integrable (fun g : ℝ => (w * g) ^ 2) (gaussianReal 0 1) := by
    simpa only [mul_pow] using (Muon.Foundations.gaussian_integrable_pow 2).const_mul (w ^ 2)
  have hden : ∀ g : ℝ, 0 ≤ 1 + y * (w * g) ^ 2 := fun g => by
    have := mul_nonneg hy.le (sq_nonneg (w * g)); linarith
  have hden' : ∀ g : ℝ, 0 ≤ 1 + z * (w * g) ^ 2 := fun g => by
    have := mul_nonneg hz.le (sq_nonneg (w * g)); linarith
  have hmom : ∫ g, (w * g) ^ 2 ∂(gaussianReal 0 1) = w ^ 2 := by
    simp_rw [mul_pow]
    rw [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one]
  constructor
  · exact integral_nonneg fun g => div_nonneg (sq_nonneg _) (mul_nonneg (hden g) (hden' g))
  · rw [← hmom]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => ?_) hint
      (Filter.Eventually.of_forall fun g => ?_)
    · exact div_nonneg (sq_nonneg _) (mul_nonneg (hden g) (hden' g))
    · apply div_le_self (sq_nonneg _)
      have h1 := mul_nonneg hy.le (sq_nonneg (w * g))
      have h2 := mul_nonneg hz.le (sq_nonneg (w * g))
      have h3 := mul_nonneg h1 h2
      nlinarith

private lemma P3_Z_nonneg {β y z : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hz : 0 < z)
    (hyz : y ≠ z) : 0 ≤ isoZkern β y z := by
  rw [(lem_app_iso_kernel_bounds_i hβ0 hβ1 hy hz hyz).1]
  refine mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg fun j => integral_nonneg fun g => ?_)
  have h1 : 0 ≤ 1 + y * (Muon.emaW β j * g) ^ 2 := by
    have := mul_nonneg hy.le (sq_nonneg (Muon.emaW β j * g)); linarith
  have h2 : 0 ≤ 1 + z * (Muon.emaW β j * g) ^ 2 := by
    have := mul_nonneg hz.le (sq_nonneg (Muon.emaW β j * g)); linarith
  exact div_nonneg (sq_nonneg _) (mul_nonneg h1 h2)

private lemma P3_X_nonneg {β y z : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hz : 0 < z)
    (hyz : y ≠ z) : 0 ≤ isoXkern β y z := by
  rw [(lem_app_iso_kernel_bounds_i hβ0 hβ1 hy hz hyz).2]
  refine mul_nonneg (mul_nonneg hy.le hz.le) (tsum_nonneg fun j => integral_nonneg fun g => ?_)
  have h1 : 0 ≤ 1 + y * (Muon.emaW β j * g) ^ 2 := by
    have := mul_nonneg hy.le (sq_nonneg (Muon.emaW β j * g)); linarith
  have h2 : 0 ≤ 1 + z * (Muon.emaW β j * g) ^ 2 := by
    have := mul_nonneg hz.le (sq_nonneg (Muon.emaW β j * g)); linarith
  exact div_nonneg (by positivity) (mul_nonneg h1 h2)

private lemma P3_Z_abs {β y z : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hz : 0 < z)
    (hyz : y ≠ z) :
    isoZkern β y z = |rW (Muon.emaW β) y - rW (Muon.emaW β) z| /
      (2 * Real.sinh (|Real.log (y / z)| / 2)) := by
  have hZnn := P3_Z_nonneg hβ0 hβ1 hy hz hyz
  have hZeq : isoZkern β y z =
      (rW (Muon.emaW β) y - rW (Muon.emaW β) z) / ((y - z) / Real.sqrt (y * z)) := by
    unfold isoZkern
    rw [if_neg hyz, div_div_eq_mul_div]
    ring
  rw [← abs_of_nonneg hZnn, hZeq, P3_K_eq hy hz, abs_div, P3_abs_K]

private lemma P3_Z_le_sinh {β y z : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hz : 0 < z)
    (hyz : y ≠ z) : isoZkern β y z ≤ isoEbar β * isoSinhRatio |Real.log (y / z)| := by
  have hδ : 0 < |Real.log (y / z)| :=
    abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one (div_pos hy hz)
      (fun h => hyz ((div_eq_one_iff_eq hz.ne').mp h)))
  have hS : 0 < Real.sinh (|Real.log (y / z)| / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hsh : isoSinhRatio |Real.log (y / z)| =
      |Real.log (y / z)| / (2 * Real.sinh (|Real.log (y / z)| / 2)) := by
    unfold isoSinhRatio; rw [if_neg hδ.ne']
  rw [hsh, P3_Z_abs hβ0 hβ1 hy hz hyz, mul_div_assoc']
  exact div_le_div_of_nonneg_right (lem_app_iso_shifts_iv hβ0 hβ1 y z hy hz) (by linarith)

private lemma P3_Z_sw2 {β y z : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hz : 0 < z)
    (hyz : y ≠ z) : isoZkern β y z ≤ Muon.sPow β 2 * Real.sqrt (y * z) := by
  rw [(lem_app_iso_kernel_bounds_i hβ0 hβ1 hy hz hyz).1, mul_comm (Muon.sPow β 2)]
  have hK : Summable (fun j : ℕ => Muon.emaW β j ^ 2) :=
    summable_emaW_pow_P1 hβ0.le hβ1 (p := 2) two_ne_zero
  have hT := (tsum_bounds_P1
    (fun j : ℕ => ∫ g, (Muon.emaW β j * g) ^ 2 /
      ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2)) ∂(gaussianReal 0 1))
    (fun j : ℕ => Muon.emaW β j ^ 2) hK (fun j => (P3_int_w hy hz _).1)
    (fun j => (P3_int_w hy hz _).2)).2
  exact mul_le_mul_of_nonneg_left hT (Real.sqrt_nonneg _)

private lemma P3_X_bounds {β y z : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hz : 0 < z)
    (hyz : y ≠ z) :
    max 0 (min (rW (Muon.emaW β) y) (rW (Muon.emaW β) z) - isoEbar β) ≤ isoXkern β y z ∧
    isoXkern β y z ≤ min (rW (Muon.emaW β) y) (rW (Muon.emaW β) z) := by
  have hyz' : y - z ≠ 0 := sub_ne_zero.mpr hyz
  have hzy' : z - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyz)
  have hZnn := P3_Z_nonneg hβ0 hβ1 hy hz hyz
  have hXnn := P3_X_nonneg hβ0 hβ1 hy hz hyz
  have hsR : isoSinhRatio |Real.log (y / z)| ≤ 1 :=
    (P3_sinh_le (abs_nonneg (Real.log (y / z)))).trans (min_le_left _ _)
  have hEb : 0 ≤ isoEbar β := le_trans zero_le_one (le_max_left _ _)
  have hZ1 : isoZkern β y z ≤ isoEbar β := by
    calc isoZkern β y z ≤ isoEbar β * isoSinhRatio |Real.log (y / z)| :=
          P3_Z_le_sinh hβ0 hβ1 hy hz hyz
      _ ≤ isoEbar β * 1 := mul_le_mul_of_nonneg_left hsR hEb
      _ = isoEbar β := mul_one _
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (rW (Muon.emaW β) y - rW (Muon.emaW β) z) / (y - z) :=
    ⟨_, rfl⟩
  have hrs : s * (y - z) = rW (Muon.emaW β) y - rW (Muon.emaW β) z := by
    rw [hs, div_mul_cancel₀ _ hyz']
  have hZs : isoZkern β y z = Real.sqrt (y * z) * s := by
    unfold isoZkern; rw [if_neg hyz, hs]; ring
  have hXy : isoXkern β y z = rW (Muon.emaW β) y - y * s := by
    unfold isoXkern; rw [if_neg hyz, div_eq_iff hzy']
    linear_combination (-y) * hrs
  have hXz : isoXkern β y z = rW (Muon.emaW β) z - z * s := by
    unfold isoXkern; rw [if_neg hyz, div_eq_iff hzy']
    linear_combination (-z) * hrs
  have hsnn : 0 ≤ s := by
    have hp : 0 < Real.sqrt (y * z) := Real.sqrt_pos.mpr (mul_pos hy hz)
    rw [hZs] at hZnn
    by_contra h
    push_neg at h
    have := mul_neg_of_pos_of_neg hp h
    linarith
  rcases lt_or_gt_of_ne hyz with hlt | hgt
  · have hr : rW (Muon.emaW β) y ≤ rW (Muon.emaW β) z := by nlinarith
    have hyle : y ≤ Real.sqrt (y * z) := by
      calc y = Real.sqrt (y ^ 2) := (Real.sqrt_sq hy.le).symm
        _ ≤ Real.sqrt (y * z) := Real.sqrt_le_sqrt (by nlinarith)
    have hys : y * s ≤ isoZkern β y z := by
      rw [hZs]; exact mul_le_mul_of_nonneg_right hyle hsnn
    have hys0 : 0 ≤ y * s := mul_nonneg hy.le hsnn
    rw [min_eq_left hr]
    refine ⟨max_le hXnn ?_, ?_⟩
    · rw [hXy]; linarith
    · rw [hXy]; linarith
  · have hr : rW (Muon.emaW β) z ≤ rW (Muon.emaW β) y := by nlinarith
    have hzle : z ≤ Real.sqrt (y * z) := by
      calc z = Real.sqrt (z ^ 2) := (Real.sqrt_sq hz.le).symm
        _ ≤ Real.sqrt (y * z) := Real.sqrt_le_sqrt (by nlinarith)
    have hzs : z * s ≤ isoZkern β y z := by
      rw [hZs]; exact mul_le_mul_of_nonneg_right hzle hsnn
    have hzs0 : 0 ≤ z * s := mul_nonneg hz.le hsnn
    rw [min_eq_right hr]
    refine ⟨max_le hXnn ?_, ?_⟩
    · rw [hXz]; linarith
    · rw [hXz]; linarith

private lemma P3_diag_term {β y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (j : ℕ) :
    0 ≤ ∫ g, (y * Muon.emaW β j ^ 2) * g ^ 2 / (1 + y * Muon.emaW β j ^ 2 * g ^ 2) ^ 2
        ∂(gaussianReal 0 1) ∧
    ∫ g, (y * Muon.emaW β j ^ 2) * g ^ 2 / (1 + y * Muon.emaW β j ^ 2 * g ^ 2) ^ 2
        ∂(gaussianReal 0 1) ≤
      ∫ g, y * Muon.emaW β j ^ 2 * g ^ 2 / (1 + y * Muon.emaW β j ^ 2 * g ^ 2)
        ∂(gaussianReal 0 1) ∧
    ∫ g, y * Muon.emaW β j ^ 2 * g ^ 2 / (1 + y * Muon.emaW β j ^ 2 * g ^ 2)
        ∂(gaussianReal 0 1) ≤ y * Muon.emaW β j ^ 2 := by
  have ha : 0 ≤ y * Muon.emaW β j ^ 2 := mul_nonneg hy.le (sq_nonneg _)
  have hfr := frac_int_le_P1 ha
  have hint := frac_integrable_P1 ha
  refine ⟨integral_nonneg fun g => div_nonneg (mul_nonneg ha (sq_nonneg g)) (sq_nonneg _), ?_,
    hfr.2⟩
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => ?_) hint
    (Filter.Eventually.of_forall fun g => ?_)
  · exact div_nonneg (mul_nonneg ha (sq_nonneg g)) (sq_nonneg _)
  · have hx : 0 ≤ y * Muon.emaW β j ^ 2 * g ^ 2 := mul_nonneg ha (sq_nonneg g)
    apply div_le_div_of_nonneg_left hx (by linarith)
    nlinarith

private lemma P3_eslope_series {β y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) :
    isoEslope β y = ∑' j : ℕ, ∫ g, (y * Muon.emaW β j ^ 2) * g ^ 2 /
      (1 + y * Muon.emaW β j ^ 2 * g ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
  have hd : deriv (rW (Muon.emaW β)) y = isoRderiv β y :=
    (((lem_app_iso_weights_i hβ0.le hβ1).2.1 y hy.le).1.hasDerivAt (Ici_mem_nhds hy)).deriv
  unfold isoEslope
  have hconv : ∑' j : {j : ℕ | 0 < Muon.emaW β j},
      Muon.emaW β j ^ 2 * isoPhiDeriv (Muon.emaW β j ^ 2 * y) =
      ∑' j : ℕ, Muon.emaW β j ^ 2 * isoPhiDeriv (Muon.emaW β j ^ 2 * y) :=
    (Equiv.subtypeUnivEquiv (fun j : ℕ => P3_emaW_pos hβ0 hβ1 j)).tsum_eq
      (fun j : ℕ => Muon.emaW β j ^ 2 * isoPhiDeriv (Muon.emaW β j ^ 2 * y))
  rw [hd, isoRderiv, hconv, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  unfold isoPhiDeriv
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1
  funext g
  ring

private lemma P3_diag_le_rW {β y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) :
    isoEslope β y ≤ rW (Muon.emaW β) y := by
  rw [P3_eslope_series hβ0 hβ1 hy, rW_eq_tsum_P1]
  have hsumR := kernel_frac_summable_P2 hβ0 hβ1 hy.le
  have hsumT := Summable.of_nonneg_of_le (fun j => (P3_diag_term hβ0 hβ1 hy j).1)
    (fun j => (P3_diag_term hβ0 hβ1 hy j).2.1) hsumR
  exact Summable.tsum_le_tsum (fun j => (P3_diag_term hβ0 hβ1 hy j).2.1) hsumT hsumR

private lemma P3_diag_le_sw2 {β y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) :
    isoEslope β y ≤ Muon.sPow β 2 * y := by
  rw [P3_eslope_series hβ0 hβ1 hy]
  have hK : Summable (fun j : ℕ => y * Muon.emaW β j ^ 2) :=
    (summable_emaW_pow_P1 hβ0.le hβ1 (p := 2) two_ne_zero).mul_left y
  have hle : ∀ j : ℕ, ∫ g, (y * Muon.emaW β j ^ 2) * g ^ 2 / (1 + y * Muon.emaW β j ^ 2 * g ^ 2) ^ 2
      ∂(gaussianReal 0 1) ≤ y * Muon.emaW β j ^ 2 := fun j =>
    le_trans (P3_diag_term hβ0 hβ1 hy j).2.1 (P3_diag_term hβ0 hβ1 hy j).2.2
  have hsumT := Summable.of_nonneg_of_le (fun j => (P3_diag_term hβ0 hβ1 hy j).1) hle hK
  calc _ ≤ ∑' j : ℕ, y * Muon.emaW β j ^ 2 := Summable.tsum_le_tsum hle hsumT hK
    _ = Muon.sPow β 2 * y := by unfold Muon.sPow; rw [tsum_mul_left, mul_comm]

/-- `lem:app-iso-kernel-bounds`(ii), snapshot `cr-2026-10-23`. Part (ii): the bounds on `𝒵` (with `δ = |log(y/z)|`, and `δ/(2 sinh(δ/2))` read through `isoSinhRatio`, which is the continuous extension to `y = z`).
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Kernel bounds]\label{lem:app-iso-kernel-bounds}
Let $y\ne z$, put $\delta\defeq\abs{\log(y/z)}$ and $r_\wedge\defeq\min(r(y),r(z))$,
and write $d_j\defeq\emaw jg$ with $g\sim\mathcal N(0,1)$.
\begin{enumerate}[label=(\roman*)]
\item The two kernels are the series
\[
\mathcal Z(y,z)=\sqrt{yz}\sum_{j\ge0}\EE\frac{d_j^2}{(1+yd_j^2)(1+zd_j^2)},\qquad
\mathcal X(y,z)=yz\sum_{j\ge0}\EE\frac{d_j^4}{(1+yd_j^2)(1+zd_j^2)} .
\]
\item $0\le\mathcal Z(y,z)\le\min\big(\bar{\mathsf e}_\bmom\,\delta/(2\sinh(\delta/2)),\ \sw2\sqrt{yz}\big)$, and
$\delta/(2\sinh(\delta/2))\le\min\big(1,(1+\delta)e^{-\delta/2}\big)$.
\item $\max(0,r_\wedge-\bar{\mathsf e}_\bmom)\le\mathcal X(y,z)\le r_\wedge$.
\item $\mathcal X(y,z)+\mathcal Z(y,z)\le\sqrt{r(y)\,r(z)}$.
\item If $\mathsf A(y)>0$ and $\mathsf A(z)>0$, then, with $\mathsf A_\vee=\mathsf A_\vee(y,z)$,
\[
\gamma-\mathcal X\ge\mathsf A_\vee,\qquad
\gamma-\mathcal X-\mathcal Z\ge\max\Big(\mathsf A_\vee-\bar{\mathsf e}_\bmom,\ \frac{\mathsf A_\vee}2\Big)>0,
\]
\[
\mathsf A_\vee\max\Big(\mathsf A_\vee-\bar{\mathsf e}_\bmom,\ \frac{\mathsf A_\vee}2\Big)\le\gamma^2\widehat\Delta(y,z)\le\big(\mathsf A_\vee+\bar{\mathsf e}_\bmom\big)^2 .
\]
\end{enumerate}
By continuity, (ii)--(v) also hold at $y=z$.
\end{lemma}
```
-/
theorem lem_app_iso_kernel_bounds_ii {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {y z : ℝ}
    (hy : 0 < y) (hz : 0 < z) :
    0 ≤ isoZkern β y z ∧
    isoZkern β y z ≤ min (isoEbar β * isoSinhRatio |Real.log (y / z)|)
      (Muon.sPow β 2 * Real.sqrt (y * z)) ∧
    isoSinhRatio |Real.log (y / z)| ≤ min 1 ((1 + |Real.log (y / z)|) * Real.exp (-|Real.log (y / z)| / 2)) := by
  refine ⟨?_, ?_, P3_sinh_le (abs_nonneg _)⟩
  · by_cases hyz : y = z
    · subst hyz
      have hZd : isoZkern β y y = isoEslope β y := by
        unfold isoZkern; rw [if_pos rfl]
      rw [hZd]
      exact le_of_lt ((lem_app_iso_count_ii hβ0 hβ1).1 y hy).1
    · exact P3_Z_nonneg hβ0 hβ1 hy hz hyz
  · by_cases hyz : y = z
    · subst hyz
      have hZd : isoZkern β y y = isoEslope β y := by
        unfold isoZkern; rw [if_pos rfl]
      have hsr0 : isoSinhRatio 0 = 1 := by
        unfold isoSinhRatio; rw [if_pos rfl]
      rw [hZd, div_self hy.ne', Real.log_one, abs_zero, hsr0, mul_one,
        Real.sqrt_mul_self hy.le]
      refine le_min ?_ (P3_diag_le_sw2 hβ0 hβ1 hy)
      exact (lem_app_iso_slope hβ0 hβ1 y hy).1.trans (lem_app_iso_slope hβ0 hβ1 y hy).2
    · exact le_min (P3_Z_le_sinh hβ0 hβ1 hy hz hyz) (P3_Z_sw2 hβ0 hβ1 hy hz hyz)

/-- `lem:app-iso-kernel-bounds`(iii), snapshot `cr-2026-10-23`. Part (iii): the bounds on `𝒳` in terms of `r_∧ = min(r(y), r(z))`.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Kernel bounds]\label{lem:app-iso-kernel-bounds}
Let $y\ne z$, put $\delta\defeq\abs{\log(y/z)}$ and $r_\wedge\defeq\min(r(y),r(z))$,
and write $d_j\defeq\emaw jg$ with $g\sim\mathcal N(0,1)$.
\begin{enumerate}[label=(\roman*)]
\item The two kernels are the series
\[
\mathcal Z(y,z)=\sqrt{yz}\sum_{j\ge0}\EE\frac{d_j^2}{(1+yd_j^2)(1+zd_j^2)},\qquad
\mathcal X(y,z)=yz\sum_{j\ge0}\EE\frac{d_j^4}{(1+yd_j^2)(1+zd_j^2)} .
\]
\item $0\le\mathcal Z(y,z)\le\min\big(\bar{\mathsf e}_\bmom\,\delta/(2\sinh(\delta/2)),\ \sw2\sqrt{yz}\big)$, and
$\delta/(2\sinh(\delta/2))\le\min\big(1,(1+\delta)e^{-\delta/2}\big)$.
\item $\max(0,r_\wedge-\bar{\mathsf e}_\bmom)\le\mathcal X(y,z)\le r_\wedge$.
\item $\mathcal X(y,z)+\mathcal Z(y,z)\le\sqrt{r(y)\,r(z)}$.
\item If $\mathsf A(y)>0$ and $\mathsf A(z)>0$, then, with $\mathsf A_\vee=\mathsf A_\vee(y,z)$,
\[
\gamma-\mathcal X\ge\mathsf A_\vee,\qquad
\gamma-\mathcal X-\mathcal Z\ge\max\Big(\mathsf A_\vee-\bar{\mathsf e}_\bmom,\ \frac{\mathsf A_\vee}2\Big)>0,
\]
\[
\mathsf A_\vee\max\Big(\mathsf A_\vee-\bar{\mathsf e}_\bmom,\ \frac{\mathsf A_\vee}2\Big)\le\gamma^2\widehat\Delta(y,z)\le\big(\mathsf A_\vee+\bar{\mathsf e}_\bmom\big)^2 .
\]
\end{enumerate}
By continuity, (ii)--(v) also hold at $y=z$.
\end{lemma}
```
-/
theorem lem_app_iso_kernel_bounds_iii {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {y z : ℝ}
    (hy : 0 < y) (hz : 0 < z) :
    max 0 (min (rW (Muon.emaW β) y) (rW (Muon.emaW β) z) - isoEbar β) ≤ isoXkern β y z ∧
    isoXkern β y z ≤ min (rW (Muon.emaW β) y) (rW (Muon.emaW β) z) := by
  by_cases hyz : y = z
  · subst hyz
    have hX : isoXkern β y y = rW (Muon.emaW β) y - isoEslope β y := by
      unfold isoXkern; rw [if_pos rfl]
    have h1 := P3_diag_le_rW hβ0 hβ1 hy
    have h2 := (lem_app_iso_slope hβ0 hβ1 y hy).1.trans (lem_app_iso_slope hβ0 hβ1 y hy).2
    have h3 : 0 ≤ isoEslope β y := le_of_lt ((lem_app_iso_count_ii hβ0 hβ1).1 y hy).1
    rw [hX, min_self]
    exact ⟨max_le (by linarith) (by linarith), by linarith⟩
  · exact P3_X_bounds hβ0 hβ1 hy hz hyz

/-! ### Private helpers for `lem_app_iso_kernel_bounds` (iv)-(v) (task P-F.9.P4) -/

private lemma P4_mom (w : ℝ) : ∫ g, (w * g) ^ 2 ∂(gaussianReal 0 1) = w ^ 2 := by
  simp_rw [mul_pow]
  rw [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one]

private lemma P4_pow_int (w : ℝ) (k : ℕ) :
    Integrable (fun g : ℝ => (w * g) ^ k) (gaussianReal 0 1) := by
  simpa only [mul_pow] using (Muon.Foundations.gaussian_integrable_pow k).const_mul (w ^ k)

private lemma P4_int_integrable {a b : ℝ} (w : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ)
    (hk : ∀ g : ℝ, 0 ≤ (w * g) ^ k) :
    Integrable (fun g : ℝ => (w * g) ^ k / ((1 + a * (w * g) ^ 2) * (1 + b * (w * g) ^ 2)))
      (gaussianReal 0 1) := by
  have hcont : Continuous fun g : ℝ =>
      (w * g) ^ k / ((1 + a * (w * g) ^ 2) * (1 + b * (w * g) ^ 2)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro g; positivity
  refine integrable_cont_le_P1 hcont (w ^ k) k (fun g => ?_)
  have h1 : 0 ≤ a * (w * g) ^ 2 := mul_nonneg ha (sq_nonneg _)
  have h2 : 0 ≤ b * (w * g) ^ 2 := mul_nonneg hb (sq_nonneg _)
  have hD1 : 1 ≤ (1 + a * (w * g) ^ 2) * (1 + b * (w * g) ^ 2) := by
    nlinarith [mul_nonneg h1 h2]
  rw [abs_of_nonneg (div_nonneg (hk g) (by positivity))]
  calc (w * g) ^ k / ((1 + a * (w * g) ^ 2) * (1 + b * (w * g) ^ 2)) ≤ (w * g) ^ k :=
        div_le_self (hk g) hD1
    _ = w ^ k * g ^ k := mul_pow w g k

private lemma P4_frac_int {q : ℝ} (hq : 0 ≤ q) (w : ℝ) :
    Integrable (fun g : ℝ => q * (w * g) ^ 2 / (1 + q * (w * g) ^ 2)) (gaussianReal 0 1) := by
  have hcont : Continuous fun g : ℝ => q * (w * g) ^ 2 / (1 + q * (w * g) ^ 2) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro g; positivity
  refine integrable_cont_le_P1 hcont (q * w ^ 2) 2 (fun g => ?_)
  have h1 : 0 ≤ q * (w * g) ^ 2 := mul_nonneg hq (sq_nonneg _)
  rw [abs_of_nonneg (div_nonneg h1 (by positivity))]
  calc q * (w * g) ^ 2 / (1 + q * (w * g) ^ 2) ≤ q * (w * g) ^ 2 :=
        div_le_self h1 (by linarith)
    _ = q * w ^ 2 * g ^ 2 := by ring

private lemma P4_frac_le {q : ℝ} (hq : 0 ≤ q) (w : ℝ) :
    0 ≤ ∫ g, q * (w * g) ^ 2 / (1 + q * (w * g) ^ 2) ∂(gaussianReal 0 1) ∧
    ∫ g, q * (w * g) ^ 2 / (1 + q * (w * g) ^ 2) ∂(gaussianReal 0 1) ≤ q * w ^ 2 := by
  have h1 : ∀ g : ℝ, 0 ≤ q * (w * g) ^ 2 := fun g => mul_nonneg hq (sq_nonneg _)
  have h2 : ∀ g : ℝ, 0 ≤ 1 + q * (w * g) ^ 2 := fun g => by linarith [h1 g]
  refine ⟨integral_nonneg fun g => div_nonneg (h1 g) (h2 g), ?_⟩
  calc ∫ g, q * (w * g) ^ 2 / (1 + q * (w * g) ^ 2) ∂(gaussianReal 0 1)
      ≤ ∫ g, q * (w * g) ^ 2 ∂(gaussianReal 0 1) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => div_nonneg (h1 g) (h2 g))
          ((P4_pow_int w 2).const_mul q)
          (Filter.Eventually.of_forall fun g => div_le_self (h1 g) (by linarith [h1 g]))
    _ = q * w ^ 2 := by rw [integral_const_mul, P4_mom]

private lemma P4_I_bound {y z : ℝ} (hy : 0 < y) (hz : 0 < z) (w : ℝ) :
    0 ≤ ∫ g, (w * g) ^ 4 / ((1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2)) ∂(gaussianReal 0 1) ∧
    ∫ g, (w * g) ^ 4 / ((1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2)) ∂(gaussianReal 0 1) ≤
      1 / y * w ^ 2 := by
  have hy0 : y ≠ 0 := hy.ne'
  have hD : ∀ g : ℝ, 0 < (1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2) := fun g => by
    have h1 : 0 ≤ y * (w * g) ^ 2 := mul_nonneg hy.le (sq_nonneg _)
    have h2 : 0 ≤ z * (w * g) ^ 2 := mul_nonneg hz.le (sq_nonneg _)
    exact mul_pos (by linarith) (by linarith)
  have hpt : ∀ g : ℝ, (w * g) ^ 4 / ((1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2)) ≤
      1 / y * (w * g) ^ 2 := by
    intro g
    have hp : 0 ≤ (w * g) ^ 2 := sq_nonneg _
    have h4 : (w * g) ^ 4 = (w * g) ^ 2 * (w * g) ^ 2 := by ring
    rw [div_le_iff₀ (hD g), h4]
    have hyp : y * (w * g) ^ 2 ≤ (1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2) := by
      nlinarith [mul_nonneg hy.le hp, mul_nonneg hz.le hp,
        mul_nonneg (mul_nonneg hy.le hp) (mul_nonneg hz.le hp)]
    have e1 : 1 / y * (w * g) ^ 2 * (y * (w * g) ^ 2) = (w * g) ^ 2 * (w * g) ^ 2 := by
      field_simp
    calc (w * g) ^ 2 * (w * g) ^ 2 = 1 / y * (w * g) ^ 2 * (y * (w * g) ^ 2) := e1.symm
      _ ≤ 1 / y * (w * g) ^ 2 * ((1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2)) :=
          mul_le_mul_of_nonneg_left hyp (by positivity)
  refine ⟨integral_nonneg fun g => div_nonneg (by positivity) (hD g).le, ?_⟩
  calc ∫ g, (w * g) ^ 4 / ((1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2)) ∂(gaussianReal 0 1)
      ≤ ∫ g, 1 / y * (w * g) ^ 2 ∂(gaussianReal 0 1) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun g => div_nonneg (by positivity) (hD g).le)
          ((P4_pow_int w 2).const_mul (1 / y)) (Filter.Eventually.of_forall hpt)
    _ = 1 / y * w ^ 2 := by rw [integral_const_mul, P4_mom]

private lemma P4_core {a b c t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hc2 : c ^ 2 = a * b) (ht : 0 < t) :
    (a * b + c) / ((1 + a) * (1 + b)) ≤ t / 2 * (a / (1 + a)) + 1 / (2 * t) * (b / (1 + b)) := by
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  have hD : 0 < (1 + a) * (1 + b) := mul_pos h1 h2
  have hX : 0 ≤ t ^ 2 * a + b := by nlinarith [sq_nonneg t]
  have hsq : (2 * t * c) ^ 2 ≤ (t ^ 2 * a + b) ^ 2 := by
    nlinarith [sq_nonneg (t ^ 2 * a - b)]
  have hP : 2 * t * c ≤ t ^ 2 * a + b := by
    nlinarith [hsq, hX, mul_nonneg ht.le hc]
  have hkey : 2 * t * (a * b + c) ≤ t ^ 2 * a * (1 + b) + b * (1 + a) := by
    nlinarith [mul_nonneg (sq_nonneg (t - 1)) (mul_nonneg ha hb)]
  have hR : t / 2 * (a / (1 + a)) + 1 / (2 * t) * (b / (1 + b)) =
      (t ^ 2 * a * (1 + b) + b * (1 + a)) / (2 * t * ((1 + a) * (1 + b))) := by
    field_simp
  rw [hR, div_le_div_iff₀ hD (mul_pos (mul_pos two_pos ht) hD)]
  nlinarith [mul_le_mul_of_nonneg_right hkey hD.le]

private lemma P4_alg {y z s d t : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) (hs : 0 ≤ s)
    (hs2 : s ^ 2 = y * z) (ht : 0 < t) :
    y * z * (d ^ 4 / ((1 + y * d ^ 2) * (1 + z * d ^ 2))) +
        s * (d ^ 2 / ((1 + y * d ^ 2) * (1 + z * d ^ 2))) ≤
      t / 2 * (y * d ^ 2 / (1 + y * d ^ 2)) + 1 / (2 * t) * (z * d ^ 2 / (1 + z * d ^ 2)) := by
  have ha : 0 ≤ y * d ^ 2 := mul_nonneg hy (sq_nonneg _)
  have hb : 0 ≤ z * d ^ 2 := mul_nonneg hz (sq_nonneg _)
  have hc : 0 ≤ s * d ^ 2 := mul_nonneg hs (sq_nonneg _)
  have hc2 : (s * d ^ 2) ^ 2 = (y * d ^ 2) * (z * d ^ 2) := by
    rw [mul_pow, hs2]; ring
  have key := P4_core ha hb hc hc2 ht
  have e1 : y * z * (d ^ 4 / ((1 + y * d ^ 2) * (1 + z * d ^ 2))) +
        s * (d ^ 2 / ((1 + y * d ^ 2) * (1 + z * d ^ 2))) =
      (y * d ^ 2 * (z * d ^ 2) + s * d ^ 2) / ((1 + y * d ^ 2) * (1 + z * d ^ 2)) := by
    ring
  rw [e1]
  exact key

private lemma P4_pair {y z s t w : ℝ} (hy : 0 < y) (hz : 0 < z) (hs : 0 ≤ s)
    (hs2 : s ^ 2 = y * z) (ht : 0 < t) :
    y * z * (∫ g, (w * g) ^ 4 / ((1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2)) ∂(gaussianReal 0 1)) +
        s * (∫ g, (w * g) ^ 2 / ((1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2))
          ∂(gaussianReal 0 1)) ≤
      t / 2 * (∫ g, y * (w * g) ^ 2 / (1 + y * (w * g) ^ 2) ∂(gaussianReal 0 1)) +
        1 / (2 * t) * (∫ g, z * (w * g) ^ 2 / (1 + z * (w * g) ^ 2) ∂(gaussianReal 0 1)) := by
  have hF4 := P4_int_integrable (a := y) (b := z) w hy.le hz.le 4 (fun g => by positivity)
  have hF2 := P4_int_integrable (a := y) (b := z) w hy.le hz.le 2 (fun g => sq_nonneg _)
  have hfy := P4_frac_int hy.le w
  have hfz := P4_frac_int hz.le w
  have eL : y * z * (∫ g, (w * g) ^ 4 / ((1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2))
        ∂(gaussianReal 0 1)) +
      s * (∫ g, (w * g) ^ 2 / ((1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2))
        ∂(gaussianReal 0 1)) =
      ∫ g, (y * z * ((w * g) ^ 4 / ((1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2))) +
        s * ((w * g) ^ 2 / ((1 + y * (w * g) ^ 2) * (1 + z * (w * g) ^ 2)))) ∂(gaussianReal 0 1) := by
    rw [integral_add (hF4.const_mul (y * z)) (hF2.const_mul s), integral_const_mul,
      integral_const_mul]
  have eR : t / 2 * (∫ g, y * (w * g) ^ 2 / (1 + y * (w * g) ^ 2) ∂(gaussianReal 0 1)) +
      1 / (2 * t) * (∫ g, z * (w * g) ^ 2 / (1 + z * (w * g) ^ 2) ∂(gaussianReal 0 1)) =
      ∫ g, (t / 2 * (y * (w * g) ^ 2 / (1 + y * (w * g) ^ 2)) +
        1 / (2 * t) * (z * (w * g) ^ 2 / (1 + z * (w * g) ^ 2))) ∂(gaussianReal 0 1) := by
    rw [integral_add (hfy.const_mul (t / 2)) (hfz.const_mul (1 / (2 * t))), integral_const_mul,
      integral_const_mul]
  rw [eL, eR]
  refine integral_mono ((hF4.const_mul (y * z)).add (hF2.const_mul s))
    ((hfy.const_mul (t / 2)).add (hfz.const_mul (1 / (2 * t)))) fun g => ?_
  exact P4_alg (d := w * g) hy.le hz.le hs hs2 ht

private lemma P4_rW_form (β q : ℝ) :
    rW (Muon.emaW β) q = ∑' j : ℕ, ∫ g, q * (Muon.emaW β j * g) ^ 2 /
      (1 + q * (Muon.emaW β j * g) ^ 2) ∂(gaussianReal 0 1) := by
  rw [rW_eq_tsum_P1]
  exact tsum_congr fun j => by
    congr 1
    funext g
    ring

private lemma P4_rW_nonneg (β q : ℝ) (hq : 0 ≤ q) : 0 ≤ rW (Muon.emaW β) q := by
  rw [P4_rW_form]
  exact tsum_nonneg fun j => (P4_frac_le hq _).1

private lemma P4_amgm {S A B : ℝ} (hS : 0 ≤ S) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → S ≤ t / 2 * A + 1 / (2 * t) * B) : S ≤ Real.sqrt (A * B) := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · subst hA0
    rw [zero_mul, Real.sqrt_zero]
    by_contra hSneg
    push_neg at hSneg
    have hBp : 0 < B + 1 := by linarith
    have ht : (0 : ℝ) < (B + 1) / (2 * S) := div_pos hBp (by linarith)
    have hh := h _ ht
    have e : 1 / (2 * ((B + 1) / (2 * S))) = S / (B + 1) := by
      field_simp
    simp only [mul_zero, zero_add] at hh
    rw [e] at hh
    have hlt : S / (B + 1) * B < S := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hBp]
      nlinarith
    linarith
  · rcases eq_or_lt_of_le hS with hS0 | hSpos
    · rw [← hS0]
      exact Real.sqrt_nonneg _
    · have hh := h (S / A) (div_pos hSpos hApos)
      have hA' : A ≠ 0 := hApos.ne'
      have hS' : S ≠ 0 := hSpos.ne'
      have e : (S / A) / 2 * A + 1 / (2 * (S / A)) * B = S / 2 + A * B / (2 * S) := by
        field_simp
      rw [e] at hh
      have h2 : S / 2 ≤ A * B / (2 * S) := by linarith
      rw [le_div_iff₀ (by linarith)] at h2
      have hsq : S * S ≤ A * B := by nlinarith
      calc S = Real.sqrt (S ^ 2) := (Real.sqrt_sq hS).symm
        _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt (by rw [sq]; exact hsq)

private lemma P4_series {β y z s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hz : 0 < z)
    (hs : 0 ≤ s) (hs2 : s ^ 2 = y * z) :
    y * z * (∑' j : ℕ, ∫ g, (Muon.emaW β j * g) ^ 4 /
        ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1)) +
      s * (∑' j : ℕ, ∫ g, (Muon.emaW β j * g) ^ 2 /
        ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1)) ≤
      Real.sqrt (rW (Muon.emaW β) y * rW (Muon.emaW β) z) := by
  have hw2 := summable_emaW_pow_P1 hβ0.le hβ1 (p := 2) two_ne_zero
  have hsumJ : Summable (fun j : ℕ => ∫ g, (Muon.emaW β j * g) ^ 2 /
      ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
        ∂(gaussianReal 0 1)) :=
    Summable.of_nonneg_of_le (fun j => (P3_int_w hy hz (Muon.emaW β j)).1)
      (fun j => (P3_int_w hy hz (Muon.emaW β j)).2) hw2
  have hsumI : Summable (fun j : ℕ => ∫ g, (Muon.emaW β j * g) ^ 4 /
      ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
        ∂(gaussianReal 0 1)) :=
    Summable.of_nonneg_of_le (fun j => (P4_I_bound hy hz (Muon.emaW β j)).1)
      (fun j => (P4_I_bound hy hz (Muon.emaW β j)).2) (hw2.mul_left (1 / y))
  have hsumR : ∀ q : ℝ, 0 ≤ q → Summable (fun j : ℕ => ∫ g,
      q * (Muon.emaW β j * g) ^ 2 / (1 + q * (Muon.emaW β j * g) ^ 2) ∂(gaussianReal 0 1)) :=
    fun q hq => Summable.of_nonneg_of_le (fun j => (P4_frac_le hq _).1)
      (fun j => (P4_frac_le hq _).2) (hw2.mul_left q)
  have hT : y * z * (∑' j : ℕ, ∫ g, (Muon.emaW β j * g) ^ 4 /
        ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1)) +
      s * (∑' j : ℕ, ∫ g, (Muon.emaW β j * g) ^ 2 /
        ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1)) =
      ∑' j : ℕ, (y * z * (∫ g, (Muon.emaW β j * g) ^ 4 /
        ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1)) +
        s * (∫ g, (Muon.emaW β j * g) ^ 2 /
        ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1))) := by
    rw [Summable.tsum_add (hsumI.mul_left (y * z)) (hsumJ.mul_left s), tsum_mul_left,
      tsum_mul_left]
  have hbound : ∀ t : ℝ, 0 < t →
      ∑' j : ℕ, (y * z * (∫ g, (Muon.emaW β j * g) ^ 4 /
        ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1)) +
        s * (∫ g, (Muon.emaW β j * g) ^ 2 /
        ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1))) ≤
      t / 2 * rW (Muon.emaW β) y + 1 / (2 * t) * rW (Muon.emaW β) z := by
    intro t ht
    rw [P4_rW_form β y, P4_rW_form β z]
    have hRy := (hsumR y hy.le).mul_left (t / 2)
    have hRz := (hsumR z hz.le).mul_left (1 / (2 * t))
    calc _ ≤ ∑' j : ℕ, (t / 2 * (∫ g, y * (Muon.emaW β j * g) ^ 2 /
            (1 + y * (Muon.emaW β j * g) ^ 2) ∂(gaussianReal 0 1)) +
          1 / (2 * t) * (∫ g, z * (Muon.emaW β j * g) ^ 2 /
            (1 + z * (Muon.emaW β j * g) ^ 2) ∂(gaussianReal 0 1))) :=
          Summable.tsum_le_tsum (fun j => P4_pair hy hz hs hs2 ht)
            ((hsumI.mul_left (y * z)).add (hsumJ.mul_left s)) (hRy.add hRz)
      _ = t / 2 * ∑' j : ℕ, (∫ g, y * (Muon.emaW β j * g) ^ 2 /
            (1 + y * (Muon.emaW β j * g) ^ 2) ∂(gaussianReal 0 1)) +
          1 / (2 * t) * ∑' j : ℕ, (∫ g, z * (Muon.emaW β j * g) ^ 2 /
            (1 + z * (Muon.emaW β j * g) ^ 2) ∂(gaussianReal 0 1)) := by
          rw [Summable.tsum_add hRy hRz, tsum_mul_left, tsum_mul_left]
  have hS0 : 0 ≤ ∑' j : ℕ, (y * z * (∫ g, (Muon.emaW β j * g) ^ 4 /
        ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1)) +
        s * (∫ g, (Muon.emaW β j * g) ^ 2 /
        ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1))) :=
    tsum_nonneg fun j => add_nonneg
      (mul_nonneg (mul_nonneg hy.le hz.le) (P4_I_bound hy hz (Muon.emaW β j)).1)
      (mul_nonneg hs (P3_int_w hy hz (Muon.emaW β j)).1)
  rw [hT]
  exact P4_amgm hS0 (P4_rW_nonneg β y hy.le) (P4_rW_nonneg β z hz.le) hbound

/-- `lem:app-iso-kernel-bounds`(iv), snapshot `cr-2026-10-23`. Part (iv): the sum bound `𝒳 + 𝒵 ≤ √(r(y) r(z))`.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Kernel bounds]\label{lem:app-iso-kernel-bounds}
Let $y\ne z$, put $\delta\defeq\abs{\log(y/z)}$ and $r_\wedge\defeq\min(r(y),r(z))$,
and write $d_j\defeq\emaw jg$ with $g\sim\mathcal N(0,1)$.
\begin{enumerate}[label=(\roman*)]
\item The two kernels are the series
\[
\mathcal Z(y,z)=\sqrt{yz}\sum_{j\ge0}\EE\frac{d_j^2}{(1+yd_j^2)(1+zd_j^2)},\qquad
\mathcal X(y,z)=yz\sum_{j\ge0}\EE\frac{d_j^4}{(1+yd_j^2)(1+zd_j^2)} .
\]
\item $0\le\mathcal Z(y,z)\le\min\big(\bar{\mathsf e}_\bmom\,\delta/(2\sinh(\delta/2)),\ \sw2\sqrt{yz}\big)$, and
$\delta/(2\sinh(\delta/2))\le\min\big(1,(1+\delta)e^{-\delta/2}\big)$.
\item $\max(0,r_\wedge-\bar{\mathsf e}_\bmom)\le\mathcal X(y,z)\le r_\wedge$.
\item $\mathcal X(y,z)+\mathcal Z(y,z)\le\sqrt{r(y)\,r(z)}$.
\item If $\mathsf A(y)>0$ and $\mathsf A(z)>0$, then, with $\mathsf A_\vee=\mathsf A_\vee(y,z)$,
\[
\gamma-\mathcal X\ge\mathsf A_\vee,\qquad
\gamma-\mathcal X-\mathcal Z\ge\max\Big(\mathsf A_\vee-\bar{\mathsf e}_\bmom,\ \frac{\mathsf A_\vee}2\Big)>0,
\]
\[
\mathsf A_\vee\max\Big(\mathsf A_\vee-\bar{\mathsf e}_\bmom,\ \frac{\mathsf A_\vee}2\Big)\le\gamma^2\widehat\Delta(y,z)\le\big(\mathsf A_\vee+\bar{\mathsf e}_\bmom\big)^2 .
\]
\end{enumerate}
By continuity, (ii)--(v) also hold at $y=z$.
\end{lemma}
```
-/
theorem lem_app_iso_kernel_bounds_iv {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {y z : ℝ}
    (hy : 0 < y) (hz : 0 < z) :
    isoXkern β y z + isoZkern β y z ≤ Real.sqrt (rW (Muon.emaW β) y * rW (Muon.emaW β) z) := by
  by_cases hyz : y = z
  · subst hyz
    have hX : isoXkern β y y = rW (Muon.emaW β) y - isoEslope β y := by
      unfold isoXkern; rw [if_pos rfl]
    have hZ : isoZkern β y y = isoEslope β y := by
      unfold isoZkern; rw [if_pos rfl]
    rw [hX, hZ, Real.sqrt_mul_self_eq_abs]
    linarith [le_abs_self (rW (Muon.emaW β) y)]
  · rw [(lem_app_iso_kernel_bounds_i hβ0 hβ1 hy hz hyz).1,
      (lem_app_iso_kernel_bounds_i hβ0 hβ1 hy hz hyz).2]
    exact P4_series (s := Real.sqrt (y * z)) hβ0 hβ1 hy hz (Real.sqrt_nonneg _)
      (Real.sq_sqrt (mul_pos hy hz).le)

/-- `lem:app-iso-kernel-bounds`(v), snapshot `cr-2026-10-23`. Part (v): the gap `γ − 𝒳`, `γ − 𝒳 − 𝒵` and `γ² Δ̂` when `𝖠(y), 𝖠(z) > 0`.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Kernel bounds]\label{lem:app-iso-kernel-bounds}
Let $y\ne z$, put $\delta\defeq\abs{\log(y/z)}$ and $r_\wedge\defeq\min(r(y),r(z))$,
and write $d_j\defeq\emaw jg$ with $g\sim\mathcal N(0,1)$.
\begin{enumerate}[label=(\roman*)]
\item The two kernels are the series
\[
\mathcal Z(y,z)=\sqrt{yz}\sum_{j\ge0}\EE\frac{d_j^2}{(1+yd_j^2)(1+zd_j^2)},\qquad
\mathcal X(y,z)=yz\sum_{j\ge0}\EE\frac{d_j^4}{(1+yd_j^2)(1+zd_j^2)} .
\]
\item $0\le\mathcal Z(y,z)\le\min\big(\bar{\mathsf e}_\bmom\,\delta/(2\sinh(\delta/2)),\ \sw2\sqrt{yz}\big)$, and
$\delta/(2\sinh(\delta/2))\le\min\big(1,(1+\delta)e^{-\delta/2}\big)$.
\item $\max(0,r_\wedge-\bar{\mathsf e}_\bmom)\le\mathcal X(y,z)\le r_\wedge$.
\item $\mathcal X(y,z)+\mathcal Z(y,z)\le\sqrt{r(y)\,r(z)}$.
\item If $\mathsf A(y)>0$ and $\mathsf A(z)>0$, then, with $\mathsf A_\vee=\mathsf A_\vee(y,z)$,
\[
\gamma-\mathcal X\ge\mathsf A_\vee,\qquad
\gamma-\mathcal X-\mathcal Z\ge\max\Big(\mathsf A_\vee-\bar{\mathsf e}_\bmom,\ \frac{\mathsf A_\vee}2\Big)>0,
\]
\[
\mathsf A_\vee\max\Big(\mathsf A_\vee-\bar{\mathsf e}_\bmom,\ \frac{\mathsf A_\vee}2\Big)\le\gamma^2\widehat\Delta(y,z)\le\big(\mathsf A_\vee+\bar{\mathsf e}_\bmom\big)^2 .
\]
\end{enumerate}
By continuity, (ii)--(v) also hold at $y=z$.
\end{lemma}
```
-/
theorem lem_app_iso_kernel_bounds_v {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hAy : 0 < isoResid β γ y) (hAz : 0 < isoResid β γ z) :
    isoAvee β γ y z ≤ γ - isoXkern β y z ∧
    max (isoAvee β γ y z - isoEbar β) (isoAvee β γ y z / 2) ≤ γ - isoXkern β y z - isoZkern β y z ∧
    0 < max (isoAvee β γ y z - isoEbar β) (isoAvee β γ y z / 2) ∧
    isoAvee β γ y z * max (isoAvee β γ y z - isoEbar β) (isoAvee β γ y z / 2) ≤ γ ^ 2 * isoDeltaHat β γ y z ∧
    γ ^ 2 * isoDeltaHat β γ y z ≤ (isoAvee β γ y z + isoEbar β) ^ 2 := by
  have hX3 := lem_app_iso_kernel_bounds_iii hβ0 hβ1 hy hz
  have hZ2 := lem_app_iso_kernel_bounds_ii hβ0 hβ1 hy hz
  have hIV := lem_app_iso_kernel_bounds_iv hβ0 hβ1 hy hz
  have hE1 : 1 ≤ isoEbar β := le_max_left _ _
  have hS1 : isoSinhRatio |Real.log (y / z)| ≤ 1 := hZ2.2.2.trans (min_le_left _ _)
  have hZe : isoZkern β y z ≤ isoEbar β :=
    (hZ2.2.1.trans (min_le_left _ _)).trans (mul_le_of_le_one_right (by linarith) hS1)
  have hXup : isoXkern β y z ≤ min (rW (Muon.emaW β) y) (rW (Muon.emaW β) z) := hX3.2
  have hXlo : min (rW (Muon.emaW β) y) (rW (Muon.emaW β) z) - isoEbar β ≤ isoXkern β y z :=
    (le_max_right _ _).trans hX3.1
  have hrY0 : 0 ≤ rW (Muon.emaW β) y := P4_rW_nonneg β y hy.le
  have hrZ0 : 0 ≤ rW (Muon.emaW β) z := P4_rW_nonneg β z hz.le
  have hAy0 : 0 < γ - rW (Muon.emaW β) y := hAy
  have hAz0 : 0 < γ - rW (Muon.emaW β) z := hAz
  have hAv : isoAvee β γ y z = max (γ - rW (Muon.emaW β) y) (γ - rW (Muon.emaW β) z) := rfl
  have hAv1 : γ - rW (Muon.emaW β) y ≤ isoAvee β γ y z := by
    rw [hAv]; exact le_max_left _ _
  have hAv2 : γ - rW (Muon.emaW β) z ≤ isoAvee β γ y z := by
    rw [hAv]; exact le_max_right _ _
  have hAv3 : isoAvee β γ y z ≤ (γ - rW (Muon.emaW β) y) + (γ - rW (Muon.emaW β) z) := by
    rw [hAv]; exact max_le (by linarith) (by linarith)
  have hAvpos : 0 < isoAvee β γ y z := by linarith
  have hmin : γ - min (rW (Muon.emaW β) y) (rW (Muon.emaW β) z) ≤ isoAvee β γ y z := by
    rcases min_choice (rW (Muon.emaW β) y) (rW (Muon.emaW β) z) with h | h
    · rw [h]; exact hAv1
    · rw [h]; exact hAv2
  have hAM : Real.sqrt (rW (Muon.emaW β) y * rW (Muon.emaW β) z) ≤
      (rW (Muon.emaW β) y + rW (Muon.emaW β) z) / 2 := by
    have h0 : 0 ≤ (rW (Muon.emaW β) y + rW (Muon.emaW β) z) / 2 := by linarith
    calc Real.sqrt (rW (Muon.emaW β) y * rW (Muon.emaW β) z)
        ≤ Real.sqrt (((rW (Muon.emaW β) y + rW (Muon.emaW β) z) / 2) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (rW (Muon.emaW β) y - rW (Muon.emaW β) z)])
      _ = (rW (Muon.emaW β) y + rW (Muon.emaW β) z) / 2 := Real.sqrt_sq h0
  have hGX : isoAvee β γ y z ≤ γ - isoXkern β y z := by
    rw [hAv]
    exact max_le (by linarith [min_le_left (rW (Muon.emaW β) y) (rW (Muon.emaW β) z)])
      (by linarith [min_le_right (rW (Muon.emaW β) y) (rW (Muon.emaW β) z)])
  have hGX' : γ - isoXkern β y z ≤ isoAvee β γ y z + isoEbar β := by linarith
  have hM : max (isoAvee β γ y z - isoEbar β) (isoAvee β γ y z / 2) ≤
      γ - isoXkern β y z - isoZkern β y z :=
    max_le (by linarith) (by linarith)
  have hMpos : 0 < max (isoAvee β γ y z - isoEbar β) (isoAvee β γ y z / 2) :=
    lt_max_of_lt_right (by linarith)
  have hγ0 : γ ≠ 0 := hγ.ne'
  have hfac : γ ^ 2 * isoDeltaHat β γ y z =
      (γ - isoXkern β y z - isoZkern β y z) * (γ - isoXkern β y z + isoZkern β y z) := by
    unfold isoDeltaHat
    field_simp
    ring
  have hQ : isoAvee β γ y z ≤ γ - isoXkern β y z + isoZkern β y z := by linarith
  refine ⟨hGX, hM, hMpos, ?_, ?_⟩
  · rw [hfac]
    calc isoAvee β γ y z * max (isoAvee β γ y z - isoEbar β) (isoAvee β γ y z / 2)
        ≤ (γ - isoXkern β y z + isoZkern β y z) *
            (γ - isoXkern β y z - isoZkern β y z) :=
          mul_le_mul hQ hM hMpos.le (le_trans hAvpos.le hQ)
      _ = (γ - isoXkern β y z - isoZkern β y z) * (γ - isoXkern β y z + isoZkern β y z) :=
          mul_comm _ _
  · rw [hfac]
    have hsq : (γ - isoXkern β y z) ^ 2 ≤ (isoAvee β γ y z + isoEbar β) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ isoAvee β γ y z + isoEbar β - (γ - isoXkern β y z))
        (by linarith : (0 : ℝ) ≤ isoAvee β γ y z + isoEbar β + (γ - isoXkern β y z))]
    nlinarith [sq_nonneg (isoZkern β y z)]

/-- Private helper (task P-F.9.P5): the root `isoRoot` lies below any point where it is positive
(`y < q` with `y > 0` forces `r(y) < γ`). -/
private lemma P5_isoRoot_resid {β γ s y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y)
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

/-- Private helper (task P-F.9.P5): the level root `isoQlevel` lies above `y > 0` only if
`r(y) < γ`. -/
private lemma P5_isoQlevel_resid {β γ y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y)
    (h : y < isoQlevel β γ) : rW (Muon.emaW β) y < γ := by
  unfold isoQlevel at h
  split_ifs at h with hex
  · obtain ⟨hQ0, hQr⟩ := hex.choose_spec
    have hmono := ((lem_app_iso_weights_i hβ0.le hβ1).2.2.1 hβ0).1
    have := hmono (Set.mem_Ici.mpr hy.le) (Set.mem_Ici.mpr hQ0) h
    linarith
  · linarith

/-- Private helper (task P-F.9.P5): `A(y) > 0` on the region `y < Q_{ψ(ϱ)}`. -/
private lemma P5_resid_pos {β γ ϱ y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϱ : 0 ≤ ϱ)
    (hy : 0 < y) (h : y < isoQpsi β γ ϱ) : 0 < isoResid β γ y := by
  unfold isoResid
  unfold isoQpsi at h
  split_ifs at h with hpos
  · have := P5_isoRoot_resid (γ := γ) (s := ϱ) hβ0 hβ1 hy (by unfold qIso at h; exact h)
    linarith
  · have := P5_isoQlevel_resid hβ0 hβ1 hy h
    linarith

/-- Private helper (task P-F.9.P5): positivity of `Δ̂` on the region of
`prop:app-iso-vol-representation` (first conjunct). -/
private lemma P5_delta_pos {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    (hϱ : 0 ≤ ϱ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (y z : ℝ) (hy : 0 < y) (hz : 0 < z)
    (hyQ : y < isoQpsi β γ ϱ) (hzQ : z / β ^ (2 * ℓ) < isoQpsi β γ ϱ) :
    0 < isoDeltaHat β γ y z := by
  have hpow : 0 < β ^ (2 * ℓ) := pow_pos hβ0 _
  have hp1 : β ^ (2 * ℓ) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hzle : z ≤ z / β ^ (2 * ℓ) := (le_div_iff₀ hpow).mpr (mul_le_of_le_one_right hz.le hp1)
  have hzQ' : z < isoQpsi β γ ϱ := lt_of_le_of_lt hzle hzQ
  have hAy := P5_resid_pos hβ0 hβ1 hϱ hy hyQ
  have hAz := P5_resid_pos hβ0 hβ1 hϱ hz hzQ'
  obtain ⟨-, -, h3, h4, -⟩ :=
    lem_app_iso_kernel_bounds_v hβ0 hβ1 hγ hy hz hAy hAz
  have hAv : 0 < isoAvee β γ y z := lt_of_lt_of_le hAy (by unfold isoAvee; exact le_max_left _ _)
  have hprod : 0 < isoAvee β γ y z * max (isoAvee β γ y z - isoEbar β) (isoAvee β γ y z / 2) :=
    mul_pos hAv h3
  have hg : 0 < γ ^ 2 * isoDeltaHat β γ y z := lt_of_lt_of_le hprod h4
  exact pos_of_mul_pos_right hg (by positivity)

/-- Private helper (task P-F.9.P5): the EMA weights are a weight sequence. -/
private lemma P5_weightSeq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Muon.DetEquiv.WeightSeq (Muon.emaW β) := by
  refine ⟨fun j => ?_, ?_, 0, ?_⟩
  · unfold Muon.emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  · unfold Muon.emaW
    exact (summable_geometric_of_lt_one hβ0 hβ1).mul_left _
  · unfold Muon.emaW
    rw [pow_zero, mul_one]
    exact (by linarith : (0:ℝ) < 1 - β).ne'

/-- Private helper (task P-F.9.P5): `r_β` is an isotropic link. -/
private lemma P5_isoLink {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsIsoLink (rW (Muon.emaW β)) := by
  have h := lem_app_iso_weights_i hβ0.le hβ1
  refine ⟨fun q hq => (h.2.1 q (Set.mem_Ici.mp hq)).1.continuousWithinAt,
    (h.2.2.1 hβ0).1, ?_⟩
  unfold rW
  simp

/-- Private helper (task P-F.9.P5): derivative of `r_β` at positive points. -/
private lemma P5_hasDeriv {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (rW (Muon.emaW β)) (deriv (rW (Muon.emaW β)) y) y ∧
      0 < deriv (rW (Muon.emaW β)) y := by
  have hw := P5_weightSeq hβ0.le hβ1
  have h1 := (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.2.2.1 y hy
  have h2 := (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.2.2.2.1 y hy
  rw [h1.deriv]
  exact ⟨h1, h2⟩

/-- Private helper (task P-F.9.P5): the root of the closure at `s > 0`. -/
private lemma P5_root {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {s : ℝ} (hs : 0 < s) :
    0 < qIso β γ γ s ∧ rW (Muon.emaW β) (qIso β γ γ s) < γ ∧
      s * qIso β γ γ s = (γ - rW (Muon.emaW β) (qIso β γ γ s)) ^ 2 := by
  have hr := P5_isoLink hβ0 hβ1
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

/-- Private helper (task P-F.9.P5): uniqueness of the root. -/
private lemma P5_root_unique {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {s y : ℝ}
    (hs : 0 < s) (hy : 0 < y) (hry : rW (Muon.emaW β) y < γ)
    (h : s * y = (γ - rW (Muon.emaW β) y) ^ 2) : qIso β γ γ s = y := by
  have hr := P5_isoLink hβ0 hβ1
  obtain ⟨-, hex, -, hroot, -, -⟩ := lem_app_iso_comparison_i hr hγ hγ
  obtain ⟨q, -, hu⟩ := hex s hs
  have hyD : y ∈ isoDr (rW (Muon.emaW β)) γ γ ∧ isoG (rW (Muon.emaW β)) γ γ s y = 0 := by
    refine ⟨⟨hy.le, by rw [min_self]; exact hry⟩, ?_⟩
    unfold isoG; nlinarith
  have h1 := hu _ hyD
  have h2 := hu _ (hroot s hs)
  have hq : qIso β γ γ s = isoRoot (rW (Muon.emaW β)) γ γ s := rfl
  rw [hq, h2, h1]

/-- Private helper (task P-F.9.P5): the level `Q_γ`. -/
private lemma P5_Qlevel {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) :
    0 < isoQlevel β γ ∧ rW (Muon.emaW β) (isoQlevel β γ) = γ := by
  have h := lem_app_iso_weights_i hβ0.le hβ1
  have hex : ∃ q : ℝ, 0 ≤ q ∧ rW (Muon.emaW β) q = γ := by
    obtain ⟨q, hq, e⟩ := (h.2.2.1 hβ0).2.2.2 (Set.mem_Ici.mpr hγ.le)
    exact ⟨q, hq, e⟩
  have hs : 0 ≤ isoQlevel β γ ∧ rW (Muon.emaW β) (isoQlevel β γ) = γ := by
    unfold isoQlevel
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨?_, hs.2⟩
  rcases hs.1.eq_or_lt with h0 | h0
  · exfalso
    have : rW (Muon.emaW β) 0 = 0 := (P5_isoLink hβ0 hβ1).2.2
    rw [← h0, this] at hs
    linarith [hs.2]
  · exact h0

/-- Private helper (task P-F.9.P5): `Q_{ψ(ϱ)}` is positive, `r(Q) ≤ γ`, and `ϱ Q = A(Q)²`. -/
private lemma P5_Q_spec {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 ≤ ϱ) :
    0 < isoQpsi β γ ϱ ∧ rW (Muon.emaW β) (isoQpsi β γ ϱ) ≤ γ ∧
      ϱ * isoQpsi β γ ϱ = (γ - rW (Muon.emaW β) (isoQpsi β γ ϱ)) ^ 2 := by
  unfold isoQpsi
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := P5_root hβ0 hβ1 hγ h
    exact ⟨h1, h2.le, h3⟩
  · have hϱ0 : ϱ = 0 := le_antisymm (not_lt.mp h) hϱ
    obtain ⟨h1, h2⟩ := P5_Qlevel hβ0 hβ1 hγ
    refine ⟨h1, h2.le, ?_⟩
    rw [hϱ0, h2]; ring

/-- Private helper (task P-F.9.P5): points of the region map into `x > 0`, and recover the root. -/
private lemma P5_region_fwd {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 ≤ ϱ)
    {y : ℝ} (hy : 0 < y) (hyQ : y < isoQpsi β γ ϱ) :
    ϱ < (γ - rW (Muon.emaW β) y) ^ 2 / y ∧
      qIso β γ γ ((γ - rW (Muon.emaW β) y) ^ 2 / y) = y := by
  have hA := P5_resid_pos hβ0 hβ1 hϱ hy hyQ
  unfold isoResid at hA
  have hs0 : 0 < (γ - rW (Muon.emaW β) y) ^ 2 / y := by positivity
  have hq : qIso β γ γ ((γ - rW (Muon.emaW β) y) ^ 2 / y) = y :=
    P5_root_unique hβ0 hβ1 hγ hs0 hy (by linarith)
      (by field_simp)
  refine ⟨?_, hq⟩
  by_contra hcon
  push_neg at hcon
  have hr := P5_isoLink hβ0 hβ1
  obtain ⟨-, -, -, -, -, hanti⟩ := lem_app_iso_comparison_i hr hγ hγ
  have hϱpos : 0 < ϱ := lt_of_lt_of_le hs0 hcon
  have hQ : isoQpsi β γ ϱ = qIso β γ γ ϱ := by unfold isoQpsi; rw [if_pos hϱpos]
  rw [hQ] at hyQ
  rcases hcon.eq_or_lt with he | hlt
  · have : qIso β γ γ ϱ = y := by rw [← he]; exact hq
    linarith
  · have := hanti (Set.mem_Ioi.mpr hs0) (Set.mem_Ioi.mpr hϱpos) hlt
    have h2 : isoRoot (rW (Muon.emaW β)) γ γ ϱ < isoRoot (rW (Muon.emaW β)) γ γ
        ((γ - rW (Muon.emaW β) y) ^ 2 / y) := this
    have h3 : qIso β γ γ ϱ < y := by
      have : isoRoot (rW (Muon.emaW β)) γ γ ((γ - rW (Muon.emaW β) y) ^ 2 / y) = y := hq
      rw [this] at h2; exact h2
    linarith

/-- Private helper (task P-F.9.P5): every `x > 0` is hit. -/
private lemma P5_region_bwd {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 ≤ ϱ)
    {x : ℝ} (hx : 0 < x) :
    0 < qIso β γ γ (ϱ + x ^ 2) ∧ qIso β γ γ (ϱ + x ^ 2) < isoQpsi β γ ϱ ∧
      (γ - rW (Muon.emaW β) (qIso β γ γ (ϱ + x ^ 2))) ^ 2 / qIso β γ γ (ϱ + x ^ 2) =
        ϱ + x ^ 2 := by
  have hs : 0 < ϱ + x ^ 2 := by positivity
  obtain ⟨h1, h2, h3⟩ := P5_root hβ0 hβ1 hγ hs
  refine ⟨h1, ?_, by field_simp; linarith⟩
  have hr := P5_isoLink hβ0 hβ1
  rcases hϱ.eq_or_lt with h0 | hpos
  · have hQ : isoQpsi β γ ϱ = isoQlevel β γ := by
      unfold isoQpsi; rw [if_neg (by rw [← h0]; exact lt_irrefl 0)]
    rw [hQ]
    obtain ⟨hQ0, hQr⟩ := P5_Qlevel hβ0 hβ1 hγ
    by_contra hcon
    push_neg at hcon
    have := hr.2.1.monotoneOn (Set.mem_Ici.mpr hQ0.le) (Set.mem_Ici.mpr h1.le) hcon
    linarith
  · have hQ : isoQpsi β γ ϱ = qIso β γ γ ϱ := by unfold isoQpsi; rw [if_pos hpos]
    rw [hQ]
    obtain ⟨-, -, -, -, -, hanti⟩ := lem_app_iso_comparison_i hr hγ hγ
    exact hanti (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr hs) (by nlinarith)

/-- Private helper (task P-F.9.P5): the change-of-variables map `y ↦ √(A(y)²/y − ϱ)` has the
stated derivative on the region. -/
private lemma P5_T_deriv {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 ≤ ϱ)
    {y : ℝ} (hy : 0 < y) (hyQ : y < isoQpsi β γ ϱ) :
    HasDerivAt (fun t => Real.sqrt ((γ - rW (Muon.emaW β) t) ^ 2 / t - ϱ))
      (-(isoResid β γ y * isoWeightJ β γ y / y ^ 2) /
        (2 * Real.sqrt ((γ - rW (Muon.emaW β) y) ^ 2 / y - ϱ))) y := by
  obtain ⟨hd, -⟩ := P5_hasDeriv hβ0 hβ1 hy
  have hV := (P5_region_fwd hβ0 hβ1 hγ hϱ hy hyQ).1
  have hVpos : 0 < (γ - rW (Muon.emaW β) y) ^ 2 / y - ϱ := by linarith
  have h1 : HasDerivAt (fun t => γ - rW (Muon.emaW β) t) (-(deriv (rW (Muon.emaW β)) y)) y :=
    (hasDerivAt_const y γ).sub hd |>.congr_deriv (by ring)
  have h2 := (h1.pow 2).div (hasDerivAt_id y) hy.ne'
  have h3 := (h2.sub_const ϱ).sqrt hVpos.ne'
  refine h3.congr_deriv ?_
  unfold isoResid isoWeightJ isoEslope
  simp only [id, Pi.pow_apply]
  congr 1
  field_simp
  unfold isoResid
  ring

/-- Private helper (task P-F.9.P5): the Jacobian of the change of variables,
`|T'(y)| = 𝗃(y) u_ϱ(y)/(2 y √y)`. -/
private lemma P5_T_abs {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 ≤ ϱ)
    {y : ℝ} (hy : 0 < y) (hyQ : y < isoQpsi β γ ϱ) :
    |-(isoResid β γ y * isoWeightJ β γ y / y ^ 2) /
        (2 * Real.sqrt ((γ - rW (Muon.emaW β) y) ^ 2 / y - ϱ))| =
      isoWeightJ β γ y * isoUlev β γ ϱ y / (2 * (y * Real.sqrt y)) := by
  obtain ⟨-, hd⟩ := P5_hasDeriv hβ0 hβ1 hy
  have hV := (P5_region_fwd hβ0 hβ1 hγ hϱ hy hyQ).1
  have hVpos : 0 < (γ - rW (Muon.emaW β) y) ^ 2 / y - ϱ := by linarith
  have hA := P5_resid_pos hβ0 hβ1 hϱ hy hyQ
  have hj : 0 < isoWeightJ β γ y := by
    unfold isoWeightJ isoEslope
    have : 0 < y * deriv (rW (Muon.emaW β)) y := mul_pos hy hd
    linarith
  set V := (γ - rW (Muon.emaW β) y) ^ 2 / y - ϱ with hVdef
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hVpos
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hu : isoUlev β γ ϱ y = isoResid β γ y / (Real.sqrt y * Real.sqrt V) := by
    unfold isoUlev
    have hA2 : isoResid β γ y = γ - rW (Muon.emaW β) y := rfl
    have e1 : 1 - ϱ * y / isoResid β γ y ^ 2 =
        (Real.sqrt y * Real.sqrt V / isoResid β γ y) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hy.le, Real.sq_sqrt hVpos.le, hVdef, hA2]
      have : (γ - rW (Muon.emaW β) y) ≠ 0 := by rw [← hA2]; exact hA.ne'
      field_simp
    rw [e1, Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow,
      Real.sqrt_sq (by positivity)]
    field_simp
  rw [hu, abs_div, abs_neg, abs_of_pos (by positivity : 0 < isoResid β γ y * isoWeightJ β γ y / y ^ 2),
    abs_of_pos (by positivity : 0 < 2 * Real.sqrt V)]
  field_simp
  exact Real.sq_sqrt hy.le

/-- Private helper (task P-F.9.P5): the lag scalars `b_ℓ, Z_ℓ, X_ℓ` as divided differences at the
roots, off the coincidence `y = β^{2ℓ} y'`. -/
private lemma P5_lag_series {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {ℓ : ℕ}
    {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (hne : qIso β γ γ s ≠ β ^ (2 * ℓ) * qIso β γ γ s') :
    isoLagB β γ ℓ s s' =
      β ^ ℓ * ((rW (Muon.emaW β) (qIso β γ γ s) - rW (Muon.emaW β) (β ^ (2 * ℓ) * qIso β γ γ s')) /
        (qIso β γ γ s - β ^ (2 * ℓ) * qIso β γ γ s')) ∧
    isoLagZ β γ ℓ s s' = isoZkern β (qIso β γ γ s) (β ^ (2 * ℓ) * qIso β γ γ s') / γ ∧
    isoLagX β γ ℓ s s' = isoXkern β (qIso β γ γ s) (β ^ (2 * ℓ) * qIso β γ γ s') / γ := by
  obtain ⟨hy, -, -⟩ := P5_root hβ0 hβ1 hγ hs
  obtain ⟨hy', -, -⟩ := P5_root hβ0 hβ1 hγ hs'
  set y := qIso β γ γ s with hydef
  set y' := qIso β γ γ s' with hy'def
  have hc : 0 < β ^ (2 * ℓ) := pow_pos hβ0 _
  have hz : 0 < β ^ (2 * ℓ) * y' := mul_pos hc hy'
  set z := β ^ (2 * ℓ) * y' with hzdef
  obtain ⟨hZs, hXs⟩ := lem_app_iso_kernel_bounds_i hβ0 hβ1 hy hz hne
  have hyz : y - z ≠ 0 := sub_ne_zero.mpr hne
  have hsq : 0 < Real.sqrt (y * z) := Real.sqrt_pos.mpr (mul_pos hy hz)
  have hZ' : isoZkern β y z = Real.sqrt (y * z) * ((rW (Muon.emaW β) y - rW (Muon.emaW β) z) / (y - z)) := by
    unfold isoZkern
    rw [if_neg hne]
    ring
  set SZ := ∑' j : ℕ, ∫ g, (Muon.emaW β j * g) ^ 2 /
        ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1) with hSZ
  set SX := ∑' j : ℕ, ∫ g, (Muon.emaW β j * g) ^ 4 /
        ((1 + y * (Muon.emaW β j * g) ^ 2) * (1 + z * (Muon.emaW β j * g) ^ 2))
          ∂(gaussianReal 0 1) with hSX
  have hSZeq : SZ = (rW (Muon.emaW β) y - rW (Muon.emaW β) z) / (y - z) := by
    have := hZs.symm.trans hZ'
    exact mul_left_cancel₀ hsq.ne' this
  have hB : isoLagB β γ ℓ s s' = β ^ ℓ * SZ := by
    unfold isoLagB
    rw [hSZ, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [← integral_const_mul]
    congr 1
    funext g
    rw [hzdef]
    ring
  have hE : isoLagE β γ ℓ s s' = β ^ (2 * ℓ) * SX := by
    unfold isoLagE
    rw [hSX, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [← integral_const_mul]
    congr 1
    funext g
    rw [hzdef]
    ring
  refine ⟨by rw [hB, hSZeq], ?_, ?_⟩
  · unfold isoLagZ
    rw [hB, hZs]
    congr 1
    have h1 : y * y' * β ^ (2 * ℓ) = y * z := by rw [hzdef]; ring
    have h2 : Real.sqrt (y * z) = Real.sqrt (y * y') * β ^ ℓ := by
      rw [← h1, show y * y' * β ^ (2 * ℓ) = (y * y') * (β ^ ℓ) ^ 2 by ring,
        Real.sqrt_mul (mul_pos hy hy').le, Real.sqrt_sq (pow_pos hβ0 _).le]
    rw [h2]
    ring
  · unfold isoLagX
    rw [hE, hXs]
    congr 1
    rw [hzdef]
    ring

/-- Private helper (task P-F.9.P5): the lag kernel in participation coordinates, off the
coincidence. -/
private lemma P5_kernel_form {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {ℓ : ℕ}
    {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (hne : qIso β γ γ s ≠ β ^ (2 * ℓ) * qIso β γ γ s') :
    isoLagDelta β γ ℓ s s' =
      isoDeltaHat β γ (qIso β γ γ s) (β ^ (2 * ℓ) * qIso β γ γ s') ∧
    lagKernel β γ ℓ s s' =
      β ^ ℓ * ((rW (Muon.emaW β) (qIso β γ γ s) -
          rW (Muon.emaW β) (β ^ (2 * ℓ) * qIso β γ γ s')) /
        (qIso β γ γ s - β ^ (2 * ℓ) * qIso β γ γ s')) * qIso β γ γ s * qIso β γ γ s' /
        (γ ^ 3 * isoDeltaHat β γ (qIso β γ γ s) (β ^ (2 * ℓ) * qIso β γ γ s')) := by
  obtain ⟨hB, hZ, hX⟩ := P5_lag_series hβ0 hβ1 hγ hs hs' hne
  have hD : isoLagDelta β γ ℓ s s' =
      isoDeltaHat β γ (qIso β γ γ s) (β ^ (2 * ℓ) * qIso β γ γ s') := by
    unfold isoLagDelta isoDeltaHat
    rw [hX, hZ]
  refine ⟨hD, ?_⟩
  unfold lagKernel
  rw [hD, hB]

/-- Private helper (task P-F.9.P5): lower bound for `Δ̂` on the region (`ℓ ≥ 1`). -/
private lemma P5_delta_ge {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    (hϱ : 0 ≤ ϱ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {y z : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hyQ : y < isoQpsi β γ ϱ) (hzQ : z < β ^ (2 * ℓ) * isoQpsi β γ ϱ) :
    (γ - rW (Muon.emaW β) (β ^ (2 * ℓ) * isoQpsi β γ ϱ)) ^ 2 / (2 * γ ^ 2) ≤
      isoDeltaHat β γ y z ∧
    0 < (γ - rW (Muon.emaW β) (β ^ (2 * ℓ) * isoQpsi β γ ϱ)) := by
  obtain ⟨hQ0, hQr, -⟩ := P5_Q_spec hβ0 hβ1 hγ hϱ
  have hr := P5_isoLink hβ0 hβ1
  have hpow : 0 < β ^ (2 * ℓ) := pow_pos hβ0 _
  have hp1 : β ^ (2 * ℓ) < 1 := pow_lt_one₀ hβ0.le hβ1 (by omega)
  have hcQ : β ^ (2 * ℓ) * isoQpsi β γ ϱ < isoQpsi β γ ϱ := by nlinarith
  have hcQ0 : 0 < β ^ (2 * ℓ) * isoQpsi β γ ϱ := mul_pos hpow hQ0
  have ha0 : 0 < γ - rW (Muon.emaW β) (β ^ (2 * ℓ) * isoQpsi β γ ϱ) := by
    have := hr.2.1 (Set.mem_Ici.mpr hcQ0.le) (Set.mem_Ici.mpr hQ0.le) hcQ
    linarith
  refine ⟨?_, ha0⟩
  have hzQ' : z < isoQpsi β γ ϱ := by linarith
  have hAy := P5_resid_pos hβ0 hβ1 hϱ hy hyQ
  have hAz := P5_resid_pos hβ0 hβ1 hϱ hz hzQ'
  obtain ⟨-, -, -, h4, -⟩ := lem_app_iso_kernel_bounds_v hβ0 hβ1 hγ hy hz hAy hAz
  have hAz' : γ - rW (Muon.emaW β) (β ^ (2 * ℓ) * isoQpsi β γ ϱ) ≤ isoResid β γ z := by
    unfold isoResid
    have := hr.2.1.monotoneOn (Set.mem_Ici.mpr hz.le) (Set.mem_Ici.mpr hcQ0.le) hzQ.le
    linarith
  have hAv : isoResid β γ z ≤ isoAvee β γ y z := by unfold isoAvee; exact le_max_right _ _
  have hAv0 : γ - rW (Muon.emaW β) (β ^ (2 * ℓ) * isoQpsi β γ ϱ) ≤ isoAvee β γ y z :=
    hAz'.trans hAv
  have hmax : isoAvee β γ y z / 2 ≤
      max (isoAvee β γ y z - isoEbar β) (isoAvee β γ y z / 2) := le_max_right _ _
  have hAvpos : 0 < isoAvee β γ y z := lt_of_lt_of_le ha0 hAv0
  have h5 : isoAvee β γ y z * (isoAvee β γ y z / 2) ≤ γ ^ 2 * isoDeltaHat β γ y z :=
    le_trans (mul_le_mul_of_nonneg_left hmax hAvpos.le) h4
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul hAv0 hAv0 ha0.le hAvpos.le]

/-- Private helper (task P-F.9.P5): a measurable planar set with subsingleton vertical slices is
null. -/
private lemma P5_null_of_slices {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (h : ∀ a b₁ b₂, (a, b₁) ∈ S → (a, b₂) ∈ S → b₁ = b₂) :
    (volume : Measure (ℝ × ℝ)) S = 0 := by
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hS]
  refine Eventually.of_forall fun a => ?_
  show volume (Prod.mk a ⁻¹' S) = 0
  exact Set.Subsingleton.measure_zero (fun b1 h1 b2 h2 => h a b1 b2 h1 h2) _

/-- Private helper (task P-F.9.P5): `x ↦ q(−ϱ−x²)` is injective on `x > 0`. -/
private lemma P5_y_inj {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 ≤ ϱ) :
    InjOn (fun x : ℝ => qIso β γ γ (ϱ + x ^ 2)) (Ioi 0) := by
  have hr := P5_isoLink hβ0 hβ1
  obtain ⟨-, -, -, -, -, hanti⟩ := lem_app_iso_comparison_i hr hγ hγ
  have key : ∀ a b : ℝ, 0 < a → a < b →
      qIso β γ γ (ϱ + b ^ 2) < qIso β γ γ (ϱ + a ^ 2) := by
    intro a b ha hab
    have hb : 0 < b := ha.trans hab
    exact hanti (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
      (by nlinarith)
  intro a ha b hb hab
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  rcases lt_trichotomy a b with h | h | h
  · have := key a b ha' h
    simp only at hab
    linarith
  · exact h
  · have := key b a hb' h
    simp only at hab
    linarith

/-- Private helper (task P-F.9.P5): the decay bound `y(x)(1 + x²) ≤ Q + γ²`. -/
private lemma P5_y_bound {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 ≤ ϱ)
    {x : ℝ} (hx : 0 < x) :
    qIso β γ γ (ϱ + x ^ 2) * (1 + x ^ 2) ≤ isoQpsi β γ ϱ + γ ^ 2 := by
  have hs : 0 < ϱ + x ^ 2 := by positivity
  obtain ⟨h1, h2, h3⟩ := P5_root hβ0 hβ1 hγ hs
  obtain ⟨-, hQ, -⟩ := P5_region_bwd hβ0 hβ1 hγ hϱ hx
  have hr := P5_isoLink hβ0 hβ1
  have hr0 : 0 ≤ rW (Muon.emaW β) (qIso β γ γ (ϱ + x ^ 2)) := by
    have := hr.2.1.monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h1.le) h1.le
    rw [hr.2.2] at this
    exact this
  set y := qIso β γ γ (ϱ + x ^ 2)
  have hA : (γ - rW (Muon.emaW β) y) ^ 2 ≤ γ ^ 2 := by nlinarith
  nlinarith [mul_nonneg hϱ h1.le, mul_pos h1 hx]

/-- Private helper (task P-F.9.P5): a measurable version of `x ↦ q(−ϱ−x²)`. -/
private lemma P5_meas_y {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 ≤ ϱ) :
    ∃ Y : ℝ → ℝ, Measurable Y ∧ ∀ x : ℝ, 0 < x → Y x = qIso β γ γ (ϱ + x ^ 2) := by
  classical
  have hr := P5_isoLink hβ0 hβ1
  obtain ⟨-, -, -, -, hcont, -⟩ := lem_app_iso_comparison_i hr hγ hγ
  have hc : ContinuousOn (fun x : ℝ => qIso β γ γ (ϱ + x ^ 2)) (Ioi 0) := by
    refine ContinuousOn.comp (g := isoRoot (rW (Muon.emaW β)) γ γ) hcont
      (by fun_prop) ?_
    intro x hx
    have : (0 : ℝ) < x := hx
    exact Set.mem_Ioi.mpr (by positivity)
  refine ⟨Set.piecewise (Ioi 0) (fun x : ℝ => qIso β γ γ (ϱ + x ^ 2)) (fun _ => 0), ?_, ?_⟩
  · exact ContinuousOn.measurable_piecewise hc continuousOn_const measurableSet_Ioi
  · intro x hx
    rw [Set.piecewise_eq_of_mem _ _ _ (Set.mem_Ioi.mpr hx)]

/-- Private helper (task P-F.9.P5): a measurable function agreeing off the coincidence with the
participation-coordinate lag kernel. -/
private lemma P5_meas_F {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (ℓ : ℕ) :
    ∃ F : ℝ × ℝ → ℝ, Measurable F ∧ ∀ y z : ℝ, 0 < y → 0 < z → y ≠ z →
      F (y, z) = β ^ ℓ * ((rW (Muon.emaW β) y - rW (Muon.emaW β) z) / (y - z)) * y *
        (z / β ^ (2 * ℓ)) / (γ ^ 3 * isoDeltaHat β γ y z) := by
  have hr := P5_isoLink hβ0 hβ1
  set R : ℝ → ℝ := fun q => rW (Muon.emaW β) (max q 0) with hR
  have hRc : Continuous R :=
    ContinuousOn.comp_continuous hr.1 (continuous_id.max continuous_const) (fun q => le_max_right q 0)
  have hRm : Measurable R := hRc.measurable
  have hRe : ∀ q : ℝ, 0 ≤ q → R q = rW (Muon.emaW β) q := fun q hq => by
    simp only [hR, max_eq_left hq]
  set Dd : ℝ × ℝ → ℝ := fun p => (R p.1 - R p.2) / (p.1 - p.2) with hDd
  set Zk : ℝ × ℝ → ℝ := fun p => Real.sqrt (p.1 * p.2) * Dd p with hZk
  set Xk : ℝ × ℝ → ℝ := fun p => (p.2 * R p.1 - p.1 * R p.2) / (p.2 - p.1) with hXk
  have hDm : Measurable Dd := by
    simp only [hDd]; fun_prop
  have hZm : Measurable Zk := by
    simp only [hZk]; fun_prop
  have hXm : Measurable Xk := by
    simp only [hXk]; fun_prop
  refine ⟨fun p => β ^ ℓ * Dd p * p.1 * (p.2 / β ^ (2 * ℓ)) /
    (γ ^ 3 * ((1 - Xk p / γ) ^ 2 - (Zk p / γ) ^ 2)), ?_, ?_⟩
  · fun_prop
  · intro y z hy hz hyz
    simp only [hDd, hZk, hXk, hRe y hy.le, hRe z hz.le]
    unfold isoDeltaHat isoZkern isoXkern
    rw [if_neg hyz, if_neg hyz]
    ring

/-- Private helper (task P-F.9.P5): pointwise bounds on the lag kernel in `x`-coordinates. -/
private lemma P5_kernel_le {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 ≤ ϱ)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {x x' : ℝ} (hx : 0 < x) (hx' : 0 < x')
    (hne : qIso β γ γ (ϱ + x ^ 2) ≠ β ^ (2 * ℓ) * qIso β γ γ (ϱ + x' ^ 2)) :
    0 ≤ lagKernel β γ ℓ (ϱ + x ^ 2) (ϱ + x' ^ 2) ∧
    lagKernel β γ ℓ (ϱ + x ^ 2) (ϱ + x' ^ 2) ≤
      (β ^ ℓ * Muon.sPow β 2 / (γ ^ 3 * ((γ - rW (Muon.emaW β) (β ^ (2 * ℓ) * isoQpsi β γ ϱ)) ^ 2 /
        (2 * γ ^ 2)))) * (qIso β γ γ (ϱ + x ^ 2) * qIso β γ γ (ϱ + x' ^ 2)) := by
  have hs : 0 < ϱ + x ^ 2 := by positivity
  have hs' : 0 < ϱ + x' ^ 2 := by positivity
  obtain ⟨hy, -, -⟩ := P5_root hβ0 hβ1 hγ hs
  obtain ⟨hy', -, -⟩ := P5_root hβ0 hβ1 hγ hs'
  obtain ⟨-, hyQ, -⟩ := P5_region_bwd hβ0 hβ1 hγ hϱ hx
  obtain ⟨-, hy'Q, -⟩ := P5_region_bwd hβ0 hβ1 hγ hϱ hx'
  obtain ⟨⟨hB0, hB1⟩, -, -, hD0, -⟩ := lem_app_iso_lag_i hβ0 hβ1 hγ hs hs' ℓ
  have hpow : 0 < β ^ (2 * ℓ) := pow_pos hβ0 _
  have hz : 0 < β ^ (2 * ℓ) * qIso β γ γ (ϱ + x' ^ 2) := mul_pos hpow hy'
  have hzQ : β ^ (2 * ℓ) * qIso β γ γ (ϱ + x' ^ 2) < β ^ (2 * ℓ) * isoQpsi β γ ϱ :=
    mul_lt_mul_of_pos_left hy'Q hpow
  obtain ⟨hdge, ha0⟩ := P5_delta_ge hβ0 hβ1 hγ hϱ hℓ hy hz hyQ hzQ
  obtain ⟨hDeq, -⟩ := P5_kernel_form hβ0 hβ1 hγ hs hs' hne
  have hδ0 : 0 < (γ - rW (Muon.emaW β) (β ^ (2 * ℓ) * isoQpsi β γ ϱ)) ^ 2 / (2 * γ ^ 2) := by
    positivity
  have hs2 : 0 ≤ Muon.sPow β 2 := by
    rw [Muon.sPow_two hβ0.le hβ1]; exact div_nonneg (by linarith) (by linarith)
  refine ⟨?_, ?_⟩
  · unfold lagKernel
    exact div_nonneg (mul_nonneg (mul_nonneg hB0 hy.le) hy'.le)
      (mul_nonneg (by positivity) hD0.le)
  · unfold lagKernel
    rw [hDeq]
    have hΔ : 0 < isoDeltaHat β γ (qIso β γ γ (ϱ + x ^ 2))
        (β ^ (2 * ℓ) * qIso β γ γ (ϱ + x' ^ 2)) := lt_of_lt_of_le hδ0 hdge
    have h1 : isoLagB β γ ℓ (ϱ + x ^ 2) (ϱ + x' ^ 2) * qIso β γ γ (ϱ + x ^ 2) *
        qIso β γ γ (ϱ + x' ^ 2) ≤ β ^ ℓ * Muon.sPow β 2 *
        (qIso β γ γ (ϱ + x ^ 2) * qIso β γ γ (ϱ + x' ^ 2)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hB1 (mul_nonneg hy.le hy'.le)
    have h2 := div_le_div₀ (c := β ^ ℓ * Muon.sPow β 2 *
        (qIso β γ γ (ϱ + x ^ 2) * qIso β γ γ (ϱ + x' ^ 2)))
      (b := γ ^ 3 * isoDeltaHat β γ (qIso β γ γ (ϱ + x ^ 2))
        (β ^ (2 * ℓ) * qIso β γ γ (ϱ + x' ^ 2)))
      (d := γ ^ 3 * ((γ - rW (Muon.emaW β) (β ^ (2 * ℓ) * isoQpsi β γ ϱ)) ^ 2 / (2 * γ ^ 2)))
      (mul_nonneg (mul_nonneg (pow_nonneg hβ0.le _) hs2) (mul_nonneg hy.le hy'.le)) h1 (by positivity)
      (mul_le_mul_of_nonneg_left hdge (by positivity))
    refine h2.trans (le_of_eq ?_)
    ring

/-- Private helper (task P-F.9.P5): the lag coefficient as a lower integral over `x`-space. -/
private lemma P5_x_side {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 ≤ ϱ)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ENNReal.ofReal (lagCoeff β γ ϱ ℓ) =
      ENNReal.ofReal (4 / Real.pi ^ 2) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal (lagKernel β γ ℓ (ϱ + p.1 ^ 2) (ϱ + p.2 ^ 2)) := by
  obtain ⟨Y, hYm, hY⟩ := P5_meas_y hβ0 hβ1 hγ hϱ
  obtain ⟨F, hFm, hF⟩ := P5_meas_F hβ0 hβ1 hγ ℓ
  have hcpos : 0 < β ^ (2 * ℓ) := pow_pos hβ0 _
  set R : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) with hRdef
  have hRm : MeasurableSet R := measurableSet_Ioi.prod measurableSet_Ioi
  set Kc : ℝ × ℝ → ℝ := fun p => lagKernel β γ ℓ (ϱ + p.1 ^ 2) (ϱ + p.2 ^ 2) with hKc
  have hinj := P5_y_inj hβ0 hβ1 hγ hϱ
  have hN : (volume : Measure (ℝ × ℝ)) {p | p ∈ R ∧ Y p.1 = β ^ (2 * ℓ) * Y p.2} = 0 := by
    refine P5_null_of_slices ?_ ?_
    · exact hRm.inter (measurableSet_eq_fun (hYm.comp measurable_fst)
        (measurable_const.mul (hYm.comp measurable_snd)))
    · intro a b1 b2 h1 h2
      obtain ⟨⟨-, hb1⟩, e1⟩ := h1
      obtain ⟨⟨-, hb2⟩, e2⟩ := h2
      simp only at e1 e2 hb1 hb2
      have h12 : Y b1 = Y b2 := mul_left_cancel₀ hcpos.ne' (e1.symm.trans e2)
      rw [hY b1 hb1, hY b2 hb2] at h12
      exact hinj hb1 hb2 h12
  have hae : ∀ᵐ p ∂(volume.restrict R), p ∈ R ∧ Y p.1 ≠ β ^ (2 * ℓ) * Y p.2 := by
    have h1 : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
        ¬ (p ∈ R ∧ Y p.1 = β ^ (2 * ℓ) * Y p.2) := measure_eq_zero_iff_ae_notMem.1 hN
    filter_upwards [ae_restrict_mem hRm, ae_restrict_of_ae h1] with p hp hp'
    exact ⟨hp, fun h => hp' ⟨hp, h⟩⟩
  have hpos : ∀ p ∈ R, 0 < p.1 ∧ 0 < p.2 := fun p hp => ⟨hp.1, hp.2⟩
  have hKeq : Kc =ᵐ[volume.restrict R] fun p => F (Y p.1, β ^ (2 * ℓ) * Y p.2) := by
    filter_upwards [hae] with p hp
    obtain ⟨hpR, hne⟩ := hp
    obtain ⟨h1, h2⟩ := hpos p hpR
    rw [hY p.1 h1, hY p.2 h2] at hne
    have hs : 0 < ϱ + p.1 ^ 2 := by positivity
    have hs' : 0 < ϱ + p.2 ^ 2 := by positivity
    obtain ⟨-, hform⟩ := P5_kernel_form hβ0 hβ1 hγ hs hs' hne
    obtain ⟨hy, -, -⟩ := P5_root hβ0 hβ1 hγ hs
    obtain ⟨hy', -, -⟩ := P5_root hβ0 hβ1 hγ hs'
    simp only [hKc]
    rw [hform, hY p.1 h1, hY p.2 h2,
      hF _ _ hy (mul_pos hcpos hy') hne, mul_div_cancel_left₀ _ hcpos.ne']
  have hmeas : AEStronglyMeasurable Kc (volume.restrict R) :=
    ((hFm.comp ((hYm.comp measurable_fst).prodMk
      (measurable_const.mul (hYm.comp measurable_snd)))).aestronglyMeasurable).congr hKeq.symm
  set Q := isoQpsi β γ ϱ with hQ
  have hQ0 : 0 < Q := (P5_Q_spec hβ0 hβ1 hγ hϱ).1
  set C : ℝ := β ^ ℓ * Muon.sPow β 2 / (γ ^ 3 * ((γ - rW (Muon.emaW β) (β ^ (2 * ℓ) * Q)) ^ 2 /
    (2 * γ ^ 2))) with hC
  have hprod : (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))) =
      volume.restrict R := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hm : Integrable (fun x : ℝ => (Q + γ ^ 2) * (1 + x ^ 2)⁻¹)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (integrable_inv_one_add_sq.const_mul _).integrableOn
  have hg : Integrable (fun p : ℝ × ℝ => C * (((Q + γ ^ 2) * (1 + p.1 ^ 2)⁻¹) *
      ((Q + γ ^ 2) * (1 + p.2 ^ 2)⁻¹))) (volume.restrict R) := by
    rw [← hprod]
    exact (hm.mul_prod hm).const_mul C
  have hbd : ∀ᵐ p ∂(volume.restrict R), 0 ≤ Kc p ∧ Kc p ≤ C * (((Q + γ ^ 2) * (1 + p.1 ^ 2)⁻¹) *
      ((Q + γ ^ 2) * (1 + p.2 ^ 2)⁻¹)) := by
    filter_upwards [hae] with p hp
    obtain ⟨hpR, hne⟩ := hp
    obtain ⟨h1, h2⟩ := hpos p hpR
    rw [hY p.1 h1, hY p.2 h2] at hne
    obtain ⟨hk0, hk1⟩ := P5_kernel_le hβ0 hβ1 hγ hϱ hℓ h1 h2 hne
    refine ⟨hk0, hk1.trans ?_⟩
    have hs : 0 < ϱ + p.1 ^ 2 := by positivity
    have hs' : 0 < ϱ + p.2 ^ 2 := by positivity
    obtain ⟨hy, -, -⟩ := P5_root hβ0 hβ1 hγ hs
    obtain ⟨hy', -, -⟩ := P5_root hβ0 hβ1 hγ hs'
    have hb1 := P5_y_bound hβ0 hβ1 hγ hϱ h1
    have hb2 := P5_y_bound hβ0 hβ1 hγ hϱ h2
    have e1 : qIso β γ γ (ϱ + p.1 ^ 2) ≤ (Q + γ ^ 2) * (1 + p.1 ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; exact hb1
    have e2 : qIso β γ γ (ϱ + p.2 ^ 2) ≤ (Q + γ ^ 2) * (1 + p.2 ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; exact hb2
    have hCpos : 0 ≤ C := by
      have ha0 := (P5_delta_ge hβ0 hβ1 hγ hϱ hℓ hy (mul_pos hcpos hy')
        (by
          obtain ⟨-, hQ1, -⟩ := P5_region_bwd hβ0 hβ1 hγ hϱ h1
          exact hQ1) (by
          obtain ⟨-, hQ2, -⟩ := P5_region_bwd hβ0 hβ1 hγ hϱ h2
          exact mul_lt_mul_of_pos_left hQ2 hcpos)).2
      have hs2 : 0 ≤ Muon.sPow β 2 := by
        rw [Muon.sPow_two hβ0.le hβ1]; exact div_nonneg (by linarith) (by linarith)
      simp only [hC]
      positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul e1 e2 hy'.le (by positivity)) hCpos
  have hint : Integrable Kc (volume.restrict R) := by
    refine Integrable.mono' hg hmeas ?_
    filter_upwards [hbd] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
    exact hp.2
  have hI : (∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
      lagKernel β γ ℓ (ϱ + x ^ 2) (ϱ + y ^ 2)) = ∫ p, Kc p ∂(volume.restrict R) := by
    rw [← hprod]
    exact (integral_prod Kc (by rw [hprod]; exact hint)).symm
  unfold lagCoeff
  rw [hI, ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hint (by filter_upwards [hbd] with p hp using hp.1)]

/-- Private helper (task P-F.9.P5): the two-dimensional change of variables
`(y, z) ↦ (T y, T (z/c))` on `(0,Q) × (0,cQ)`. -/
private lemma P5_cov_gen {T T' : ℝ → ℝ} {Q c : ℝ} (hc : 0 < c)
    (hT : ∀ y ∈ Ioo (0 : ℝ) Q, HasDerivAt T (T' y) y) (hinj : InjOn T (Ioo 0 Q))
    (himg : T '' Ioo 0 Q = Ioi 0) (G : ℝ × ℝ → ENNReal) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), G p =
      ∫⁻ p in Ioo (0 : ℝ) Q ×ˢ Ioo (0 : ℝ) (c * Q),
        ENNReal.ofReal (|T' p.1| * (|T' (p.2 / c)| * c⁻¹)) * G (T p.1, T (p.2 / c)) := by
  have hsc : (fun z : ℝ => z / c) '' Ioo (0 : ℝ) (c * Q) = Ioo 0 Q := by
    ext w
    constructor
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      exact ⟨by positivity, by rw [div_lt_iff₀ hc]; linarith⟩
    · rintro ⟨h1, h2⟩
      refine ⟨w * c, ⟨by positivity, by nlinarith⟩, ?_⟩
      simp only
      field_simp
  have himg2 : (fun z : ℝ => T (z / c)) '' Ioo (0 : ℝ) (c * Q) = Ioi 0 := by
    rw [← himg, ← hsc, Set.image_image]
  have hinj2 : InjOn (fun z : ℝ => T (z / c)) (Ioo (0 : ℝ) (c * Q)) := by
    intro a ha b hb hab
    have ha' : a / c ∈ Ioo (0 : ℝ) Q := by
      rw [← hsc]; exact ⟨a, ha, rfl⟩
    have hb' : b / c ∈ Ioo (0 : ℝ) Q := by
      rw [← hsc]; exact ⟨b, hb, rfl⟩
    have := hinj ha' hb' hab
    field_simp at this
    exact this
  have hs : MeasurableSet (Ioo (0 : ℝ) Q ×ˢ Ioo (0 : ℝ) (c * Q)) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have himgf : (Prod.map T (fun z : ℝ => T (z / c))) '' (Ioo (0 : ℝ) Q ×ˢ Ioo (0 : ℝ) (c * Q)) =
      Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    have e := Set.prod_image_image_eq (m₁ := T) (m₂ := fun z : ℝ => T (z / c))
      (s := Ioo (0 : ℝ) Q) (t := Ioo (0 : ℝ) (c * Q))
    rw [himg, himg2] at e
    exact e.symm
  have hinjf : InjOn (Prod.map T (fun z : ℝ => T (z / c)))
      (Ioo (0 : ℝ) Q ×ˢ Ioo (0 : ℝ) (c * Q)) := hinj.prodMap hinj2
  have hderiv : ∀ p ∈ Ioo (0 : ℝ) Q ×ˢ Ioo (0 : ℝ) (c * Q),
      HasFDerivWithinAt (Prod.map T (fun z : ℝ => T (z / c)))
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (T' p.1)).prodMap
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (T' (p.2 / c) * c⁻¹)))
        (Ioo (0 : ℝ) Q ×ˢ Ioo (0 : ℝ) (c * Q)) p := by
    intro p hp
    have h1 : HasDerivAt T (T' p.1) p.1 := hT p.1 hp.1
    have h2' : p.2 / c ∈ Ioo (0 : ℝ) Q := by
      rw [← hsc]; exact ⟨p.2, hp.2, rfl⟩
    have h2 : HasDerivAt (fun z : ℝ => T (z / c)) (T' (p.2 / c) * c⁻¹) p.2 := by
      have hd := (hasDerivAt_id p.2).div_const c
      have := HasDerivAt.comp p.2 (hT _ h2') hd
      simp only [id, one_div] at this
      exact this
    exact (HasFDerivAt.prodMap p h1.hasFDerivAt h2.hasFDerivAt).hasFDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hderiv hinjf G
  rw [himgf] at key
  rw [key]
  refine lintegral_congr fun p => ?_
  congr 2
  have h1 : ∀ a : ℝ, ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a : ℝ →L[ℝ] ℝ) :
      ℝ →ₗ[ℝ] ℝ) = a • LinearMap.id := by
    intro a; ext; simp
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap, h1, h1,
    LinearMap.det_smul, LinearMap.det_smul]
  simp only [Module.finrank_self, pow_one, LinearMap.det_id, mul_one]
  rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hc)]

/-- Private helper (task P-F.9.P5): the algebra of the Jacobian and kernel factors. -/
private lemma P5_alg {b y y' N Δ J J' g P : ℝ} (hb : 0 < b) (hy : 0 < y) (hy' : 0 < y')
    (hg : 0 < g) (hP : 0 < P) (hΔ : 0 < Δ) :
    4 / P * ((J / (2 * (y * Real.sqrt y))) * ((J' / (2 * (y' * Real.sqrt y'))) * (b ^ 2)⁻¹) *
      (b * N * y * y' / (g ^ 3 * Δ))) =
    1 / (P * g ^ 3) * (N / Real.sqrt (y * (b ^ 2 * y')) * J * J' / Δ) := by
  have h1 : Real.sqrt (y * (b ^ 2 * y')) = b * Real.sqrt y * Real.sqrt y' := by
    rw [show y * (b ^ 2 * y') = b ^ 2 * (y * y') by ring, Real.sqrt_mul (sq_nonneg b),
      Real.sqrt_sq hb.le, Real.sqrt_mul hy.le]
    ring
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hsy' : 0 < Real.sqrt y' := Real.sqrt_pos.mpr hy'
  have e1 : y = Real.sqrt y * Real.sqrt y := (Real.mul_self_sqrt hy.le).symm
  have e2 : y' = Real.sqrt y' * Real.sqrt y' := (Real.mul_self_sqrt hy'.le).symm
  rw [h1]
  generalize Real.sqrt y = a at *
  generalize Real.sqrt y' = a' at *
  subst e1 e2
  field_simp
  ring

/-- Private helper (task P-F.9.P5): the change of variables inverts the root map. -/
private lemma P5_Tsq {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 ≤ ϱ)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) (isoQpsi β γ ϱ)) :
    0 < Real.sqrt ((γ - rW (Muon.emaW β) y) ^ 2 / y - ϱ) ∧
    ϱ + Real.sqrt ((γ - rW (Muon.emaW β) y) ^ 2 / y - ϱ) ^ 2 =
      (γ - rW (Muon.emaW β) y) ^ 2 / y ∧
    qIso β γ γ (ϱ + Real.sqrt ((γ - rW (Muon.emaW β) y) ^ 2 / y - ϱ) ^ 2) = y := by
  obtain ⟨hlt, hq⟩ := P5_region_fwd hβ0 hβ1 hγ hϱ hy.1 hy.2
  have hpos : 0 < (γ - rW (Muon.emaW β) y) ^ 2 / y - ϱ := by linarith
  have hsq : ϱ + Real.sqrt ((γ - rW (Muon.emaW β) y) ^ 2 / y - ϱ) ^ 2 =
      (γ - rW (Muon.emaW β) y) ^ 2 / y := by
    rw [Real.sq_sqrt hpos.le]; ring
  refine ⟨Real.sqrt_pos.mpr hpos, hsq, ?_⟩
  rw [hsq]; exact hq

/-- Private helper (task P-F.9.P5): the pointwise identity between the Jacobian-weighted kernel and
the integrand of the representation. -/
private lemma P5_pointwise {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 ≤ ϱ)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {y y' : ℝ} (hy : y ∈ Ioo (0 : ℝ) (isoQpsi β γ ϱ))
    (hy' : y' ∈ Ioo (0 : ℝ) (isoQpsi β γ ϱ)) (hne : y ≠ β ^ (2 * ℓ) * y') :
    ENNReal.ofReal (4 / Real.pi ^ 2) *
      (ENNReal.ofReal
        (|-(isoResid β γ y * isoWeightJ β γ y / y ^ 2) /
            (2 * Real.sqrt ((γ - rW (Muon.emaW β) y) ^ 2 / y - ϱ))| *
          (|-(isoResid β γ y' * isoWeightJ β γ y' / y' ^ 2) /
              (2 * Real.sqrt ((γ - rW (Muon.emaW β) y') ^ 2 / y' - ϱ))| *
            (β ^ (2 * ℓ))⁻¹)) *
       ENNReal.ofReal (lagKernel β γ ℓ
          (ϱ + Real.sqrt ((γ - rW (Muon.emaW β) y) ^ 2 / y - ϱ) ^ 2)
          (ϱ + Real.sqrt ((γ - rW (Muon.emaW β) y') ^ 2 / y' - ϱ) ^ 2))) =
    ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3)) *
      ENNReal.ofReal (isoDivDiff β y (β ^ (2 * ℓ) * y') * isoWeightJ β γ y * isoUlev β γ ϱ y *
        (isoWeightJ β γ y' * isoUlev β γ ϱ y') / isoDeltaHat β γ y (β ^ (2 * ℓ) * y')) := by
  obtain ⟨-, hs1, hq1⟩ := P5_Tsq hβ0 hβ1 hγ hϱ hy
  obtain ⟨-, hs2, hq2⟩ := P5_Tsq hβ0 hβ1 hγ hϱ hy'
  have hcpos : 0 < β ^ (2 * ℓ) := pow_pos hβ0 _
  have hpos1 : 0 < ϱ + Real.sqrt ((γ - rW (Muon.emaW β) y) ^ 2 / y - ϱ) ^ 2 := by
    rw [hs1]
    have := P5_resid_pos hβ0 hβ1 hϱ hy.1 hy.2
    unfold isoResid at this
    exact div_pos (pow_pos this 2) hy.1
  have hpos2 : 0 < ϱ + Real.sqrt ((γ - rW (Muon.emaW β) y') ^ 2 / y' - ϱ) ^ 2 := by
    rw [hs2]
    have := P5_resid_pos hβ0 hβ1 hϱ hy'.1 hy'.2
    unfold isoResid at this
    exact div_pos (pow_pos this 2) hy'.1
  obtain ⟨hDelta, hform⟩ := P5_kernel_form hβ0 hβ1 hγ hpos1 hpos2
    (by rw [hq1, hq2]; exact hne)
  rw [hform, hq1, hq2]
  have hz : 0 < β ^ (2 * ℓ) * y' := mul_pos hcpos hy'.1
  have hΔ : 0 < isoDeltaHat β γ y (β ^ (2 * ℓ) * y') :=
    P5_delta_pos hβ0 hβ1 hγ hϱ hℓ y _ hy.1 hz hy.2 (by rw [mul_div_cancel_left₀ _ hcpos.ne']; exact hy'.2)
  have hja := P5_T_abs hβ0 hβ1 hγ hϱ hy.1 hy.2
  have hja' := P5_T_abs hβ0 hβ1 hγ hϱ hy'.1 hy'.2
  have hDD : isoDivDiff β y (β ^ (2 * ℓ) * y') =
      (rW (Muon.emaW β) y - rW (Muon.emaW β) (β ^ (2 * ℓ) * y')) / (y - β ^ (2 * ℓ) * y') /
        Real.sqrt (y * (β ^ (2 * ℓ) * y')) := by
    unfold isoDivDiff
    rw [if_neg hne, div_div]
  rw [hja, hja', hDD]
  have hjpos : 0 < isoWeightJ β γ y := by
    obtain ⟨-, hd⟩ := P5_hasDeriv hβ0 hβ1 hy.1
    have hA := P5_resid_pos hβ0 hβ1 hϱ hy.1 hy.2
    unfold isoWeightJ isoEslope
    have : 0 < y * deriv (rW (Muon.emaW β)) y := mul_pos hy.1 hd
    linarith
  have hjpos' : 0 < isoWeightJ β γ y' := by
    obtain ⟨-, hd⟩ := P5_hasDeriv hβ0 hβ1 hy'.1
    have hA := P5_resid_pos hβ0 hβ1 hϱ hy'.1 hy'.2
    unfold isoWeightJ isoEslope
    have : 0 < y' * deriv (rW (Muon.emaW β)) y' := mul_pos hy'.1 hd
    linarith
  have hu : ∀ w : ℝ, w ∈ Ioo (0 : ℝ) (isoQpsi β γ ϱ) → 0 < isoUlev β γ ϱ w := by
    intro w hw
    unfold isoUlev
    have hA := P5_resid_pos hβ0 hβ1 hϱ hw.1 hw.2
    have hV := (P5_region_fwd hβ0 hβ1 hγ hϱ hw.1 hw.2).1
    have : 0 < 1 - ϱ * w / isoResid β γ w ^ 2 := by
      have h1 : ϱ * w < isoResid β γ w ^ 2 := by
        unfold isoResid at hA ⊢
        rw [lt_div_iff₀ hw.1] at hV
        linarith
      have h2 : ϱ * w / isoResid β γ w ^ 2 < 1 := by
        rw [div_lt_one (by positivity)]; exact h1
      linarith
    exact Real.rpow_pos_of_pos this _
  have hcb : β ^ (2 * ℓ) = (β ^ ℓ) ^ 2 := by ring
  have key := P5_alg (b := β ^ ℓ) (y := y) (y' := y')
    (N := (rW (Muon.emaW β) y - rW (Muon.emaW β) (β ^ (2 * ℓ) * y')) / (y - β ^ (2 * ℓ) * y'))
    (Δ := isoDeltaHat β γ y (β ^ (2 * ℓ) * y'))
    (J := isoWeightJ β γ y * isoUlev β γ ϱ y) (J' := isoWeightJ β γ y' * isoUlev β γ ϱ y')
    (g := γ) (P := Real.pi ^ 2) (pow_pos hβ0 _) hy.1 hy'.1 hγ (by positivity) hΔ
  rw [← hcb] at key
  have hJ : 0 ≤ isoWeightJ β γ y * isoUlev β γ ϱ y / (2 * (y * Real.sqrt y)) *
      (isoWeightJ β γ y' * isoUlev β γ ϱ y' / (2 * (y' * Real.sqrt y')) * (β ^ (2 * ℓ))⁻¹) := by
    have := hu y hy
    have := hu y' hy'
    have := Real.sqrt_pos.mpr hy.1
    have := Real.sqrt_pos.mpr hy'.1
    have := hy.1
    have := hy'.1
    positivity
  rw [← ENNReal.ofReal_mul hJ, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  linear_combination key

/-- Private helper (task P-F.9.P5): second conjunct of `prop_app_iso_vol_representation`. -/
private lemma P5_main {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 ≤ ϱ)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ENNReal.ofReal (lagCoeff β γ ϱ ℓ) =
      ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3)) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal
            ((if p.1 < isoQpsi β γ ϱ ∧ p.2 / β ^ (2 * ℓ) < isoQpsi β γ ϱ then (1 : ℝ) else 0) *
              (isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 * isoUlev β γ ϱ p.1 *
                (isoWeightJ β γ (p.2 / β ^ (2 * ℓ)) * isoUlev β γ ϱ (p.2 / β ^ (2 * ℓ))) /
                isoDeltaHat β γ p.1 p.2)) := by
  have hcpos : 0 < β ^ (2 * ℓ) := pow_pos hβ0 _
  obtain ⟨hQ0, -, -⟩ := P5_Q_spec hβ0 hβ1 hγ hϱ
  have hTd : ∀ y ∈ Ioo (0 : ℝ) (isoQpsi β γ ϱ), HasDerivAt
      (fun t : ℝ => Real.sqrt ((γ - rW (Muon.emaW β) t) ^ 2 / t - ϱ))
      (-(isoResid β γ y * isoWeightJ β γ y / y ^ 2) /
        (2 * Real.sqrt ((γ - rW (Muon.emaW β) y) ^ 2 / y - ϱ))) y :=
    fun y hy => P5_T_deriv hβ0 hβ1 hγ hϱ hy.1 hy.2
  have hinj : InjOn (fun t : ℝ => Real.sqrt ((γ - rW (Muon.emaW β) t) ^ 2 / t - ϱ))
      (Ioo (0 : ℝ) (isoQpsi β γ ϱ)) := by
    intro a ha b hb hab
    obtain ⟨-, -, h1⟩ := P5_Tsq hβ0 hβ1 hγ hϱ ha
    obtain ⟨-, -, h2⟩ := P5_Tsq hβ0 hβ1 hγ hϱ hb
    simp only at hab
    rw [← h1, ← h2, hab]
  have himg : (fun t : ℝ => Real.sqrt ((γ - rW (Muon.emaW β) t) ^ 2 / t - ϱ)) ''
      Ioo (0 : ℝ) (isoQpsi β γ ϱ) = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (P5_Tsq hβ0 hβ1 hγ hϱ hy).1
    · intro hx
      have hx' : (0 : ℝ) < x := hx
      obtain ⟨h1, h2, h3⟩ := P5_region_bwd hβ0 hβ1 hγ hϱ hx'
      refine ⟨qIso β γ γ (ϱ + x ^ 2), ⟨h1, h2⟩, ?_⟩
      simp only
      rw [h3, add_sub_cancel_left, Real.sqrt_sq hx'.le]
  rw [P5_x_side hβ0 hβ1 hγ hϱ hℓ, P5_cov_gen hcpos hTd hinj himg
    (fun p => ENNReal.ofReal (lagKernel β γ ℓ (ϱ + p.1 ^ 2) (ϱ + p.2 ^ 2)))]
  set Q := isoQpsi β γ ϱ with hQ
  set s : Set (ℝ × ℝ) := Ioo (0 : ℝ) Q ×ˢ Ioo (0 : ℝ) (β ^ (2 * ℓ) * Q) with hsdef
  have hs : MeasurableSet s := measurableSet_Ioo.prod measurableSet_Ioo
  have hRm : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hsub : s ⊆ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := fun p hp => ⟨hp.1.1, hp.2.1⟩
  have hRHS : (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal
        ((if p.1 < Q ∧ p.2 / β ^ (2 * ℓ) < Q then (1 : ℝ) else 0) *
          (isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 * isoUlev β γ ϱ p.1 *
            (isoWeightJ β γ (p.2 / β ^ (2 * ℓ)) * isoUlev β γ ϱ (p.2 / β ^ (2 * ℓ))) /
            isoDeltaHat β γ p.1 p.2))) =
      ∫⁻ p in s, ENNReal.ofReal
          (isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 * isoUlev β γ ϱ p.1 *
            (isoWeightJ β γ (p.2 / β ^ (2 * ℓ)) * isoUlev β γ ϱ (p.2 / β ^ (2 * ℓ))) /
            isoDeltaHat β γ p.1 p.2) := by
    have hcongr : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal
          ((if p.1 < Q ∧ p.2 / β ^ (2 * ℓ) < Q then (1 : ℝ) else 0) *
            (isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 * isoUlev β γ ϱ p.1 *
              (isoWeightJ β γ (p.2 / β ^ (2 * ℓ)) * isoUlev β γ ϱ (p.2 / β ^ (2 * ℓ))) /
              isoDeltaHat β γ p.1 p.2)) =
        s.indicator (fun p => ENNReal.ofReal
          (isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 * isoUlev β γ ϱ p.1 *
            (isoWeightJ β γ (p.2 / β ^ (2 * ℓ)) * isoUlev β γ ϱ (p.2 / β ^ (2 * ℓ))) /
            isoDeltaHat β γ p.1 p.2)) p := by
      intro p hp
      have hmem : p ∈ s ↔ p.1 < Q ∧ p.2 / β ^ (2 * ℓ) < Q := by
        constructor
        · intro h
          exact ⟨h.1.2, by rw [div_lt_iff₀ hcpos]; linarith [h.2.2]⟩
        · intro h
          exact ⟨⟨hp.1, h.1⟩, ⟨hp.2, by rw [div_lt_iff₀ hcpos] at h; linarith [h.2]⟩⟩
      by_cases h : p.1 < Q ∧ p.2 / β ^ (2 * ℓ) < Q
      · rw [if_pos h, Set.indicator_of_mem (hmem.2 h), one_mul]
      · rw [if_neg h, Set.indicator_of_notMem (fun hh => h (hmem.1 hh)), zero_mul,
          ENNReal.ofReal_zero]
    rw [setLIntegral_congr_fun hRm hcongr, lintegral_indicator hs, Measure.restrict_restrict hs,
      Set.inter_eq_left.mpr hsub]
  rw [hRHS, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hN : (volume : Measure (ℝ × ℝ)) {p | p ∈ s ∧ p.1 = p.2} = 0 := by
    refine P5_null_of_slices ?_ ?_
    · exact hs.inter (measurableSet_eq_fun measurable_fst measurable_snd)
    · intro a b1 b2 h1 h2
      have e1 : a = b1 := h1.2
      have e2 : a = b2 := h2.2
      rw [← e1, ← e2]
  have hae : ∀ᵐ p ∂(volume.restrict s), p.1 ≠ p.2 := by
    have h1 : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), ¬ (p ∈ s ∧ p.1 = p.2) :=
      measure_eq_zero_iff_ae_notMem.1 hN
    filter_upwards [ae_restrict_mem hs, ae_restrict_of_ae h1] with p hp hp'
    exact fun h => hp' ⟨hp, h⟩
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem hs, hae] with p hps hne
  have hy : p.1 ∈ Ioo (0 : ℝ) Q := hps.1
  have hy' : p.2 / β ^ (2 * ℓ) ∈ Ioo (0 : ℝ) Q := by
    refine ⟨div_pos hps.2.1 hcpos, ?_⟩
    rw [div_lt_iff₀ hcpos]; linarith [hps.2.2]
  have hz : β ^ (2 * ℓ) * (p.2 / β ^ (2 * ℓ)) = p.2 := mul_div_cancel₀ _ hcpos.ne'
  have := P5_pointwise hβ0 hβ1 hγ hϱ hℓ hy hy' (by rw [hz]; exact hne)
  rw [hz] at this
  exact this

/-- `prop:app-iso-vol-representation`, snapshot `cr-2026-10-23`. Lag coefficients in participation coordinates: positivity of `Δ̂` on the region, and the representation of `C̄_{1,ℓ}(ϱ)` as an integral over `(0,∞)²` (lower integral, nonnegative integrand).
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{proposition}[Lag coefficients in participation coordinates]\label{prop:app-iso-vol-representation}
Let $\ridge\ge0$ and let $\ell\ge1$ be an integer. Then $\widehat\Delta(y,z)>0$ whenever
$y<Q_{\psi(\ridge)}$ and $z_\ell<Q_{\psi(\ridge)}$, and
\begin{equation}\label{eqn:app-iso-vol-representation}
\overline C_{1,\ell}(\ridge)=\frac1{\pi^2\gamma^3}\int_0^\infty\!\!\int_0^\infty D(y,z)\,
\mathbf 1\{y<Q_{\psi(\ridge)},\ z_\ell<Q_{\psi(\ridge)}\}\,
\frac{\mathsf j(y)\,\mathsf u_\ridge(y)\;\mathsf j(z_\ell)\,\mathsf u_\ridge(z_\ell)}{\widehat\Delta(y,z)}\,\dif y\,\dif z .
\end{equation}
\end{proposition}
```
-/
theorem prop_app_iso_vol_representation {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    {ϱ : ℝ} (hϱ : 0 ≤ ϱ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (∀ y z : ℝ, 0 < y → 0 < z → y < isoQpsi β γ ϱ → z / β ^ (2 * ℓ) < isoQpsi β γ ϱ →
      0 < isoDeltaHat β γ y z) ∧
    ENNReal.ofReal (lagCoeff β γ ϱ ℓ) =
      ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3)) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal
            ((if p.1 < isoQpsi β γ ϱ ∧ p.2 / β ^ (2 * ℓ) < isoQpsi β γ ϱ then (1 : ℝ) else 0) *
              (isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 * isoUlev β γ ϱ p.1 *
                (isoWeightJ β γ (p.2 / β ^ (2 * ℓ)) * isoUlev β γ ϱ (p.2 / β ^ (2 * ℓ))) /
                isoDeltaHat β γ p.1 p.2)) := by
  refine ⟨fun y z hy hz hyQ hzQ => P5_delta_pos hβ0 hβ1 hγ hϱ hℓ y z hy hz hyQ hzQ, ?_⟩
  exact P5_main hβ0 hβ1 hγ hϱ hℓ

/-- Private helper (task P-F.9.P6). -/
private lemma P6_odd_sum : HasSum (fun k : ℕ => 4 / (2 * (k : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 2) := by
  have h := hasSum_zeta_two
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := h.summable
  have he : Summable (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 2) :=
    hs.comp_injective (mul_right_injective₀ (two_ne_zero))
  have ho : Summable (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) :=
    Summable.comp_injective hs (i := fun k : ℕ => 2 * k + 1) (fun a b hab => by simpa using hab)
  have hsum := tsum_even_add_odd (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) he ho
  rw [h.tsum_eq] at hsum
  have h4 : ∑' k : ℕ, 1 / ((2 * k : ℕ) : ℝ) ^ 2 = Real.pi ^ 2 / 24 := by
    have : (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 2) = fun k : ℕ => (1/4) * (1 / (k : ℝ) ^ 2) := by
      funext k
      push_cast
      rcases eq_or_ne (k : ℝ) 0 with h0 | h0
      · simp [h0]
      · field_simp; norm_num
    rw [this, tsum_mul_left, h.tsum_eq]; ring
  have hodd : ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 = Real.pi ^ 2 / 8 := by linarith
  have := ho.hasSum
  rw [hodd] at this
  have h2 := this.mul_left 4
  convert h2 using 1
  · funext k; push_cast; ring
  · ring

/-- Private helper (task P-F.9.P6). -/
private lemma P6_ker_series {τ : ℝ} (hτ : 0 < τ) :
    HasSum (fun k : ℕ => Real.exp (-(((2 * (k : ℝ) + 1) / 2) * τ)))
      (1 / (2 * Real.sinh (τ / 2))) := by
  have hq : Real.exp (-τ) < 1 := by
    simpa using Real.exp_lt_exp.2 (show -τ < 0 by linarith)
  have hg := (hasSum_geometric_of_lt_one (Real.exp_pos (-τ)).le hq).mul_left (Real.exp (-(τ / 2)))
  convert hg using 1
  · funext k
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  · rw [Real.sinh_eq]
    have h1 : Real.exp (-τ) = Real.exp (-(τ / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hpos := Real.exp_pos (-(τ / 2))
    have hlt : Real.exp (-(τ/2)) < 1 := by
      simpa using Real.exp_lt_exp.2 (show -(τ/2) < 0 by linarith)
    have hE : Real.exp (τ / 2) = (Real.exp (-(τ / 2)))⁻¹ := by
      rw [Real.exp_neg, inv_inv]
    rw [h1, hE]
    generalize Real.exp (-(τ / 2)) = e at *
    have h3 : 1 - e ^ 2 ≠ 0 := by nlinarith
    have h4 : e⁻¹ - e ≠ 0 := by
      have : e⁻¹ - e = (1 - e^2)/e := by field_simp
      rw [this]; exact div_ne_zero h3 hpos.ne'
    field_simp

/-- Private helper (task P-F.9.P6). -/
private lemma P6_exp_int {c : ℝ} (hc : 0 < c) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-c * x)) = ENNReal.ofReal (1 / c) := by
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-c * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
  have h2 : ∫ x in Ioi (0:ℝ), Real.exp (-c * x) = 1 / c := by
    rw [integral_exp_mul_Ioi (by linarith)]
    simp
  rw [h2] at this
  exact this.symm

/-- Private helper (task P-F.9.P6). -/
private lemma P6_sfinite : SFinite isoNuBase := by
  unfold isoNuBase; infer_instance

/-- Private helper (task P-F.9.P6). -/
private lemma P6_term_int (k : ℕ) :
    ∫⁻ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), ENNReal.ofReal (1 / Real.pi ^ 2) *
          (ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * p.1)) *
            ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * p.2))) =
      ENNReal.ofReal (1 / Real.pi ^ 2 * (2 / (2 * (k : ℝ) + 1)) ^ 2) := by
  have hc : (0:ℝ) < (2 * (k : ℝ) + 1) / 2 := by positivity
  rw [lintegral_const_mul _ (by fun_prop), Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun x : ℝ => ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * x)))
      (g := fun x : ℝ => ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * x)))
      (by fun_prop) (by fun_prop), P6_exp_int hc]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- Private helper (task P-F.9.P6). -/
private lemma P6_base_univ : isoNuBase univ = ENNReal.ofReal (1 / 2) := by
  unfold isoNuBase
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hS : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hfun : ∀ p ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ),
      ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))) =
        ∑' k : ℕ, ENNReal.ofReal (1 / Real.pi ^ 2) *
          (ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * p.1)) *
            ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * p.2))) := by
    intro p hp
    have hτ : 0 < p.1 + p.2 := add_pos hp.1 hp.2
    have hs := (P6_ker_series hτ).mul_left (1 / Real.pi ^ 2)
    have hpi : (0:ℝ) < Real.pi ^ 2 := by positivity
    have e1 : 1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2))) =
        ∑' k : ℕ, 1 / Real.pi ^ 2 * Real.exp (-(((2 * (k : ℝ) + 1) / 2) * (p.1 + p.2))) := by
      rw [hs.tsum_eq]; field_simp
    rw [e1, ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs.summable]
    refine tsum_congr fun k => ?_
    rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 2
    rw [← Real.exp_add]; congr 1; ring
  rw [setLIntegral_congr_fun hS hfun, lintegral_tsum (fun k => by fun_prop)]
  simp_rw [P6_term_int]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)]
  · congr 1
    have h := (P6_odd_sum.mul_left (1 / Real.pi ^ 2))
    have hpi : (0:ℝ) < Real.pi ^ 2 := by positivity
    have h' : HasSum (fun k : ℕ => 1 / Real.pi ^ 2 * (2 / (2 * (k : ℝ) + 1)) ^ 2) (1 / 2) := by
      convert h using 1
      · funext k; rw [div_pow]; ring
      · field_simp
    exact h'.tsum_eq
  · have h := (P6_odd_sum.mul_left (1 / Real.pi ^ 2)).summable
    refine h.congr fun k => ?_
    rw [div_pow]; ring

/-- Private helper (task P-F.9.P6). -/
private lemma P6_cov2 {f g f' g' : ℝ → ℝ} {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hf : ∀ x ∈ A, HasDerivAt f (f' x) x) (hg : ∀ x ∈ B, HasDerivAt g (g' x) x)
    (hinjf : InjOn f A) (hinjg : InjOn g B) (G : ℝ × ℝ → ENNReal) :
    ∫⁻ p in (f '' A) ×ˢ (g '' B), G p =
      ∫⁻ p in A ×ˢ B, ENNReal.ofReal (|f' p.1| * |g' p.2|) * G (f p.1, g p.2) := by
  have hs : MeasurableSet (A ×ˢ B) := hA.prod hB
  have himgf : (Prod.map f g) '' (A ×ˢ B) = (f '' A) ×ˢ (g '' B) :=
    (Set.prod_image_image_eq (m₁ := f) (m₂ := g) (s := A) (t := B)).symm
  have hderiv : ∀ p ∈ A ×ˢ B,
      HasFDerivWithinAt (Prod.map f g)
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f' p.1)).prodMap
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (g' p.2)))
        (A ×ˢ B) p := by
    intro p hp
    exact (HasFDerivAt.prodMap p (hf p.1 hp.1).hasFDerivAt (hg p.2 hp.2).hasFDerivAt).hasFDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hderiv (hinjf.prodMap hinjg) G
  rw [himgf] at key
  rw [key]
  refine lintegral_congr fun p => ?_
  congr 2
  have h1 : ∀ a : ℝ, ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a : ℝ →L[ℝ] ℝ) :
      ℝ →ₗ[ℝ] ℝ) = a • LinearMap.id := by
    intro a; ext; simp
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap, h1, h1,
    LinearMap.det_smul, LinearMap.det_smul]
  simp only [Module.finrank_self, pow_one, LinearMap.det_id, mul_one]
  rw [abs_mul]

/-- Private helper (task P-F.9.P6). -/
private lemma P6_alg {s a c : ℝ} (hs : 0 < s) (ha : 0 < a) (hc : 0 < c) :
    (s * Real.exp a) * (s * Real.exp (-c)) *
      (1 / (Real.pi ^ 2 * ((s * Real.exp a - s * Real.exp (-c)) *
        Real.sqrt ((s * Real.exp a) * (s * Real.exp (-c)))))) =
    1 / (Real.pi ^ 2 * (2 * Real.sinh ((a + c) / 2))) := by
  have hu1 : 1 < Real.exp (a / 2) := by
    simpa using Real.exp_lt_exp.2 (show (0:ℝ) < a / 2 by linarith)
  have hv1 : Real.exp (-(c / 2)) < 1 := by
    simpa using Real.exp_lt_exp.2 (show -(c / 2) < 0 by linarith)
  have hv0 := Real.exp_pos (-(c / 2))
  have e1 : Real.exp a = Real.exp (a / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Real.exp (-c) = Real.exp (-(c / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e3 : Real.exp ((a + c) / 2) = Real.exp (a / 2) * (Real.exp (-(c / 2)))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  have e4 : Real.exp (-((a + c) / 2)) = Real.exp (-(c / 2)) * (Real.exp (a / 2))⁻¹ := by
    rw [← Real.exp_neg (a / 2), ← Real.exp_add]; congr 1; ring
  have hsq : Real.sqrt ((s * Real.exp a) * (s * Real.exp (-c))) =
      s * Real.exp (a / 2) * Real.exp (-(c / 2)) := by
    rw [e1, e2, show (s * Real.exp (a / 2) ^ 2) * (s * Real.exp (-(c / 2)) ^ 2) =
      (s * Real.exp (a / 2) * Real.exp (-(c / 2))) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [Real.sinh_eq, hsq, e3, e4, e1, e2]
  generalize Real.exp (a / 2) = u at *
  generalize Real.exp (-(c / 2)) = v at *
  have hu0 : 0 < u := by linarith
  have h1 : u ^ 2 - v ^ 2 ≠ 0 := by nlinarith
  have h2 : u * v⁻¹ - v * u⁻¹ ≠ 0 := by
    have : u * v⁻¹ - v * u⁻¹ = (u ^ 2 - v ^ 2) / (u * v) := by field_simp
    rw [this]; exact div_ne_zero h1 (by positivity)
  have hpi : Real.pi ^ 2 ≠ 0 := by positivity
  have h3 : s * u ^ 2 - s * v ^ 2 ≠ 0 := by
    have : s * u ^ 2 - s * v ^ 2 = s * (u ^ 2 - v ^ 2) := by ring
    rw [this]; exact mul_ne_zero hs.ne' h1
  field_simp

/-- Private helper (task P-F.9.P6). -/
private lemma P6_img_f {s : ℝ} (hs : 0 < s) : (fun a : ℝ => s * Real.exp a) '' Ioi 0 = Ioi s := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    have : 1 < Real.exp a := by simpa using Real.exp_lt_exp.2 (show (0:ℝ) < a from ha)
    show s < s * Real.exp a
    nlinarith
  · intro hy
    have hy' : s < y := hy
    have hy0 : 0 < y := hs.trans hy'
    refine ⟨Real.log (y / s), ?_, ?_⟩
    · show 0 < Real.log (y / s)
      apply Real.log_pos
      rw [lt_div_iff₀ hs]; linarith
    · show s * Real.exp (Real.log (y / s)) = y
      rw [Real.exp_log (by positivity)]; field_simp

/-- Private helper (task P-F.9.P6). -/
private lemma P6_img_g {s : ℝ} (hs : 0 < s) : (fun c : ℝ => s * Real.exp (-c)) '' Ioi 0 = Ioo 0 s := by
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    have : Real.exp (-c) < 1 := by simpa using Real.exp_lt_exp.2 (show -c < 0 by
      have : (0:ℝ) < c := hc
      linarith)
    refine ⟨by positivity, ?_⟩
    show s * Real.exp (-c) < s
    nlinarith
  · rintro ⟨hy0, hy⟩
    refine ⟨-Real.log (y / s), ?_, ?_⟩
    · show 0 < -Real.log (y / s)
      have : Real.log (y / s) < 0 := Real.log_neg (by positivity) (by rw [div_lt_one hs]; exact hy)
      linarith
    · show s * Real.exp (-(-Real.log (y / s))) = y
      rw [neg_neg, Real.exp_log (by positivity)]; field_simp

/-- Private helper (task P-F.9.P6). -/
private lemma P6_A {s : ℝ} (hs : 0 < s) (Ψ : ℝ × ℝ → ℝ) :
    ∫⁻ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ),
        ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))) *
          ENNReal.ofReal (Ψ (s * Real.exp p.1, s * Real.exp (-p.2))) =
      ∫⁻ q in Ioi s ×ˢ Ioo 0 s,
        ENNReal.ofReal (1 / (Real.pi ^ 2 * ((q.1 - q.2) * Real.sqrt (q.1 * q.2)))) *
          ENNReal.ofReal (Ψ q) := by
  have h := P6_cov2 (f := fun a : ℝ => s * Real.exp a) (g := fun c : ℝ => s * Real.exp (-c))
    (f' := fun a => s * Real.exp a) (g' := fun c => -(s * Real.exp (-c)))
    (A := Ioi 0) (B := Ioi 0) measurableSet_Ioi measurableSet_Ioi
    (fun a _ => by simpa using ((Real.hasDerivAt_exp a).const_mul s))
    (fun c _ => by
      have := ((Real.hasDerivAt_exp (-c)).comp c (hasDerivAt_neg c)).const_mul s
      simpa [mul_comm] using this)
    (fun a _ b _ hab => by simpa [hs.ne'] using hab)
    (fun a _ b _ hab => by simpa [hs.ne'] using hab)
    (fun q => ENNReal.ofReal (1 / (Real.pi ^ 2 * ((q.1 - q.2) * Real.sqrt (q.1 * q.2)))) *
          ENNReal.ofReal (Ψ q))
  rw [P6_img_f hs, P6_img_g hs] at h
  rw [h]
  refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioi) fun p hp => ?_
  have ha : 0 < p.1 := hp.1
  have hc : 0 < p.2 := hp.2
  have hρ : ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))) =
      ENNReal.ofReal (|s * Real.exp p.1| * |-(s * Real.exp (-p.2))|) *
        ENNReal.ofReal (1 / (Real.pi ^ 2 * ((s * Real.exp p.1 - s * Real.exp (-p.2)) *
          Real.sqrt ((s * Real.exp p.1) * (s * Real.exp (-p.2)))))) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [abs_of_pos (by positivity), abs_neg, abs_of_pos (by positivity)]
    exact (P6_alg hs ha hc).symm
  simp only
  rw [hρ, mul_assoc]

/-- Private helper (task P-F.9.P6). -/
private lemma P6_ftc {r r' : ℝ → ℝ} (hd : ∀ y, 0 < y → HasDerivAt r (r' y) y)
    (hpos : ∀ y, 0 < y → 0 < r' y) (hmono : ∀ a b, 0 < a → 0 < b → a ≤ b → r a ≤ r b)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ s in Ioo a b, ENNReal.ofReal (r' s) = ENNReal.ofReal (r b - r a) := by
  rcases lt_or_ge a b with hab | hab
  · have hcont : ContinuousOn r (Icc a b) := fun x hx =>
      (hd x (ha.trans_le hx.1)).continuousAt.continuousWithinAt
    have hder : ∀ x ∈ Ioo a b, HasDerivAt r (r' x) x := fun x hx => hd x (ha.trans hx.1)
    have hint := intervalIntegral.integrableOn_deriv_of_nonneg hcont hder
      (fun x hx => (hpos x (ha.trans hx.1)).le)
    have hint' : IntegrableOn r' (Ioo a b) := hint.mono_set Ioo_subset_Ioc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint'
      (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using (hpos x (ha.trans hx.1)).le)]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hcont hder
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 hint)
  · rw [Ioo_eq_empty (not_lt.2 hab), Measure.restrict_empty, lintegral_zero_measure]
    symm
    rw [ENNReal.ofReal_eq_zero]
    linarith [hmono b a hb ha hab]

/-- Private helper (task P-F.9.P6). -/
private lemma P6_B {r r' : ℝ → ℝ} (hr'm : Measurable r') (hd : ∀ y, 0 < y → HasDerivAt r (r' y) y)
    (hpos : ∀ y, 0 < y → 0 < r' y) (hmono : ∀ a b, 0 < a → 0 < b → a ≤ b → r a ≤ r b)
    (H : ℝ × ℝ → ENNReal) (hH : Measurable H) :
    ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (r' s) * ∫⁻ q in Ioi s ×ˢ Ioo 0 s, H q =
      ∫⁻ q in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), ENNReal.ofReal (r q.1 - r q.2) * H q := by
  have hS : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  let f : ℝ → ℝ × ℝ → ENNReal := fun s q =>
    if (q.2 < s ∧ s < q.1) then ENNReal.ofReal (r' s) * H q else 0
  have step1 : ∀ s ∈ Ioi (0:ℝ), ENNReal.ofReal (r' s) * ∫⁻ q in Ioi s ×ˢ Ioo 0 s, H q =
      ∫⁻ q in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), f s q := by
    intro s hs
    have hs0 : 0 < s := hs
    have hK : MeasurableSet {q : ℝ × ℝ | q.2 < s ∧ s < q.1} :=
      (measurableSet_lt measurable_snd measurable_const).inter
        (measurableSet_lt measurable_const measurable_fst)
    have e1 : ∫⁻ q in Ioi s ×ˢ Ioo 0 s, H q =
        ∫⁻ q in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), {q : ℝ × ℝ | q.2 < s ∧ s < q.1}.indicator H q := by
      rw [lintegral_indicator hK, Measure.restrict_restrict hK]
      congr 2
      ext q
      simp only [mem_prod, mem_Ioi, mem_Ioo, mem_inter_iff, mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h3, h1⟩, hs0.trans h1, h2⟩
      · rintro ⟨⟨h3, h1⟩, h4, h5⟩
        exact ⟨h1, h5, h3⟩
    rw [e1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun q => ?_
    simp only [f, Set.indicator_apply, mem_setOf_eq]
    split_ifs <;> simp
  rw [setLIntegral_congr_fun measurableSet_Ioi step1]
  have hmf : Measurable (Function.uncurry f) := by
    have hc : MeasurableSet {p : ℝ × (ℝ × ℝ) | p.2.2 < p.1 ∧ p.1 < p.2.1} :=
      (measurableSet_lt (measurable_snd.comp measurable_snd) measurable_fst).inter
        (measurableSet_lt measurable_fst (measurable_fst.comp measurable_snd))
    exact Measurable.ite hc ((hr'm.ennreal_ofReal.comp measurable_fst).mul
      (hH.comp measurable_snd)) measurable_const
  rw [lintegral_lintegral_swap hmf.aemeasurable]
  refine setLIntegral_congr_fun hS fun q hq => ?_
  have hq1 : 0 < q.1 := hq.1
  have hq2 : 0 < q.2 := hq.2
  have e2 : ∀ s, f s q = (Ioo q.2 q.1).indicator (fun s => ENNReal.ofReal (r' s) * H q) s := by
    intro s
    simp only [f, Set.indicator_apply, mem_Ioo]
  simp_rw [e2]
  rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    show Ioo q.2 q.1 ∩ Ioi 0 = Ioo q.2 q.1 from inter_eq_left.2 (fun x hx => hq2.trans hx.1),
    lintegral_mul_const _ (hr'm.ennreal_ofReal), P6_ftc hd hpos hmono hq2 hq1]


/-- Private helper (task P-F.9.P6). -/
private lemma P6_mass : IsProbabilityMeasure isoNuStar := by
  have := P6_sfinite
  constructor
  unfold isoNuStar
  rw [← Set.univ_prod_univ, Measure.prod_prod, P6_base_univ]
  rw [Measure.count_univ]
  simp
  exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top


/-- Private helper (task P-F.9.P6). -/
private lemma P6_symm {β y z : ℝ} (hyz : y ≠ z) : isoDivDiff β y z = isoDivDiff β z y := by
  unfold isoDivDiff
  rw [if_neg hyz, if_neg (Ne.symm hyz), mul_comm z y]
  have : z - y = -(y - z) := by ring
  rw [this, neg_mul, div_neg, ← neg_div, neg_sub]

/-- Private helper (task P-F.9.P6). -/
private lemma P6_pt {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (Ψ : ℝ × ℝ → ℝ) {q : ℝ × ℝ}
    (hq1 : 0 < q.1) (hq2 : 0 < q.2) :
    ENNReal.ofReal (Muon.DetEquiv.rW (Muon.emaW β) q.1 - Muon.DetEquiv.rW (Muon.emaW β) q.2) *
      (ENNReal.ofReal (1 / (Real.pi ^ 2 * ((q.1 - q.2) * Real.sqrt (q.1 * q.2)))) *
        ENNReal.ofReal (Ψ q)) =
    {q : ℝ × ℝ | q.2 < q.1}.indicator
      (fun q => ENNReal.ofReal (1 / Real.pi ^ 2) * ENNReal.ofReal (isoDivDiff β q.1 q.2 * Ψ q)) q := by
  have hmono := ((lem_app_iso_weights_i hβ0.le hβ1).2.2.1 hβ0).1
  by_cases h : q.2 < q.1
  · have hlt : Muon.DetEquiv.rW (Muon.emaW β) q.2 < Muon.DetEquiv.rW (Muon.emaW β) q.1 :=
      hmono (Set.mem_Ici.2 hq2.le) (Set.mem_Ici.2 hq1.le) h
    rw [Set.indicator_of_mem (by exact h)]
    have hne : q.1 ≠ q.2 := h.ne'
    have hD : isoDivDiff β q.1 q.2 = (Muon.DetEquiv.rW (Muon.emaW β) q.1 -
        Muon.DetEquiv.rW (Muon.emaW β) q.2) / ((q.1 - q.2) * Real.sqrt (q.1 * q.2)) := by
      unfold isoDivDiff; rw [if_neg hne]
    rw [hD]
    have hs : 0 < Real.sqrt (q.1 * q.2) := Real.sqrt_pos.2 (by positivity)
    have hd : 0 < q.1 - q.2 := by linarith
    have hpi : 0 < Real.pi ^ 2 := by positivity
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  · rw [Set.indicator_of_notMem (by exact h)]
    have hle : Muon.DetEquiv.rW (Muon.emaW β) q.1 ≤ Muon.DetEquiv.rW (Muon.emaW β) q.2 :=
      hmono.monotoneOn (Set.mem_Ici.2 hq1.le) (Set.mem_Ici.2 hq2.le) (not_lt.1 h)
    rw [ENNReal.ofReal_of_nonpos (by linarith), zero_mul]


/-- Private helper (task P-F.9.P6). -/
private lemma P6_meas_pair (s : ℝ) : Measurable (isoPairMap s) := by
  unfold isoPairMap
  have hc : MeasurableSet {w : Bool × ℝ × ℝ | w.1 = true} :=
    measurable_fst (measurableSet_singleton true)
  refine Measurable.ite hc ?_ ?_
  · fun_prop
  · fun_prop

/-- Private helper (task P-F.9.P6). -/
private lemma P6_decomp (s : ℝ) (Ψ : ℝ × ℝ → ℝ) (hΨ : Measurable Ψ) :
    ∫⁻ w, ENNReal.ofReal (Ψ (isoPairMap s w)) ∂isoNuStar =
      (∫⁻ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ),
        ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))) *
          ENNReal.ofReal (Ψ (s * Real.exp p.1, s * Real.exp (-p.2)))) +
      ∫⁻ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ),
        ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))) *
          ENNReal.ofReal ((Ψ ∘ Prod.swap) (s * Real.exp p.1, s * Real.exp (-p.2))) := by
  have := P6_sfinite
  have hmeas : Measurable fun w : Bool × ℝ × ℝ => ENNReal.ofReal (Ψ (isoPairMap s w)) :=
    (hΨ.comp (P6_meas_pair s)).ennreal_ofReal
  unfold isoNuStar
  rw [lintegral_prod _ hmeas.aemeasurable, lintegral_count, tsum_fintype, Fintype.sum_bool]
  have hρ : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))) := by
    fun_prop
  have key : ∀ (Φ : ℝ × ℝ → ℝ), Measurable Φ →
      ∫⁻ p, ENNReal.ofReal (Φ p) ∂isoNuBase =
      ∫⁻ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ),
        ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))) *
          ENNReal.ofReal (Φ p) := by
    intro Φ hΦ
    unfold isoNuBase
    rw [lintegral_withDensity_eq_lintegral_mul _ hρ hΦ.ennreal_ofReal]
    rfl
  have hm : Measurable fun p : ℝ × ℝ => (s * Real.exp p.1, s * Real.exp (-p.2)) := by fun_prop
  have h1 := key (fun p => Ψ (s * Real.exp p.1, s * Real.exp (-p.2))) (hΨ.comp hm)
  have h2 := key (fun p => (Ψ ∘ Prod.swap) (s * Real.exp p.1, s * Real.exp (-p.2)))
    ((hΨ.comp measurable_swap).comp hm)
  simp only [isoPairMap, ↓reduceIte, Bool.false_eq_true]
  rw [h1, ← h2]
  rfl


/-- Private helper (task P-F.9.P6). -/
private lemma P6_part {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (Ψ : ℝ × ℝ → ℝ) (hΨ : Measurable Ψ) :
    ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (deriv (Muon.DetEquiv.rW (Muon.emaW β)) s) *
      ∫⁻ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ),
        ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))) *
          ENNReal.ofReal (Ψ (s * Real.exp p.1, s * Real.exp (-p.2))) =
    ∫⁻ q in {q : ℝ × ℝ | q.2 < q.1} ∩ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)),
      ENNReal.ofReal (1 / Real.pi ^ 2) * ENNReal.ofReal (isoDivDiff β q.1 q.2 * Ψ q) := by
  have hS : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hmono := ((lem_app_iso_weights_i hβ0.le hβ1).2.2.1 hβ0).1
  have hH : Measurable fun q : ℝ × ℝ =>
      ENNReal.ofReal (1 / (Real.pi ^ 2 * ((q.1 - q.2) * Real.sqrt (q.1 * q.2)))) *
          ENNReal.ofReal (Ψ q) := by
    have : Measurable fun q : ℝ × ℝ => 1 / (Real.pi ^ 2 * ((q.1 - q.2) * Real.sqrt (q.1 * q.2))) := by
      fun_prop
    exact this.ennreal_ofReal.mul hΨ.ennreal_ofReal
  rw [setLIntegral_congr_fun measurableSet_Ioi (fun s hs => by
    rw [P6_A hs Ψ])]
  rw [P6_B (measurable_deriv _) (fun y hy => (P5_hasDeriv hβ0 hβ1 hy).1)
    (fun y hy => (P5_hasDeriv hβ0 hβ1 hy).2)
    (fun a b ha hb hab => hmono.monotoneOn (Set.mem_Ici.2 ha.le) (Set.mem_Ici.2 hb.le) hab) _ hH]
  rw [setLIntegral_congr_fun hS (fun q hq => P6_pt hβ0 hβ1 Ψ hq.1 hq.2)]
  have hT : MeasurableSet {q : ℝ × ℝ | q.2 < q.1} := measurableSet_lt measurable_snd measurable_fst
  rw [lintegral_indicator hT, Measure.restrict_restrict hT]


/-- Private helper (task P-F.9.P6). -/
private lemma P6_sym_part {β : ℝ} (Ψ : ℝ × ℝ → ℝ) :
    ∫⁻ q in {q : ℝ × ℝ | q.1 < q.2} ∩ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)),
      ENNReal.ofReal (1 / Real.pi ^ 2) * ENNReal.ofReal (isoDivDiff β q.1 q.2 * Ψ q) =
    ∫⁻ q in {q : ℝ × ℝ | q.2 < q.1} ∩ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)),
      ENNReal.ofReal (1 / Real.pi ^ 2) *
        ENNReal.ofReal (isoDivDiff β q.1 q.2 * (Ψ ∘ Prod.swap) q) := by
  have hsw : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_swap
  have hset : (Prod.swap : ℝ × ℝ → ℝ × ℝ) ⁻¹' ({q : ℝ × ℝ | q.1 < q.2} ∩ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))) =
      {q : ℝ × ℝ | q.2 < q.1} ∩ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := by
    ext q
    simp only [mem_preimage, mem_inter_iff, mem_setOf_eq, Prod.fst_swap, Prod.snd_swap, mem_prod,
      mem_Ioi]
    tauto
  have h := hsw.setLIntegral_comp_preimage_emb MeasurableEquiv.prodComm.measurableEmbedding
    (fun y : ℝ × ℝ => ENNReal.ofReal (1 / Real.pi ^ 2) *
      ENNReal.ofReal (isoDivDiff β y.2 y.1 * Ψ y))
    ({q : ℝ × ℝ | q.1 < q.2} ∩ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)))
  rw [hset] at h
  have hmS : MeasurableSet ({q : ℝ × ℝ | q.1 < q.2} ∩ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))) :=
    (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_Ioi.prod measurableSet_Ioi)
  refine (setLIntegral_congr_fun hmS (fun b hb => ?_)).trans h.symm
  have hb1 : b.1 < b.2 := hb.1
  show ENNReal.ofReal (1 / Real.pi ^ 2) * ENNReal.ofReal (isoDivDiff β b.1 b.2 * Ψ b) =
    ENNReal.ofReal (1 / Real.pi ^ 2) * ENNReal.ofReal (isoDivDiff β b.2 b.1 * Ψ b)
  rw [P6_symm hb1.ne]


/-- Private helper (task P-F.9.P6). -/
private lemma P6_subst {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (F : ℝ → ENNReal) :
    ∫⁻ η in Ioi (0:ℝ), F (isoQlevel β η) =
      ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (deriv (Muon.DetEquiv.rW (Muon.emaW β)) s) * F s := by
  have h := lem_app_iso_weights_i hβ0.le hβ1
  have hmono := (h.2.2.1 hβ0).1
  have hbij := (h.2.2.1 hβ0).2
  have hr0 : Muon.DetEquiv.rW (Muon.emaW β) 0 = 0 := by unfold Muon.DetEquiv.rW; simp
  have himg : Muon.DetEquiv.rW (Muon.emaW β) '' Ioi 0 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (le_of_lt hx)) hx
      rw [hr0] at this
      exact this
    · intro hy
      obtain ⟨q, hq, e⟩ := hbij.2.2 (Set.mem_Ici.2 (le_of_lt hy))
      refine ⟨q, ?_, e⟩
      rcases (Set.mem_Ici.1 hq).eq_or_lt with h0 | h0
      · exfalso
        rw [← h0, hr0] at e
        exact (ne_of_lt hy) e
      · exact h0
  have key := lintegral_image_eq_lintegral_abs_deriv_mul (f := Muon.DetEquiv.rW (Muon.emaW β))
    (f' := deriv (Muon.DetEquiv.rW (Muon.emaW β))) measurableSet_Ioi
    (fun x hx => (P5_hasDeriv hβ0 hβ1 hx).1.hasDerivWithinAt)
    (hmono.injOn.mono (fun x hx => Set.mem_Ici.2 (le_of_lt hx)))
    (fun η => F (isoQlevel β η))
  rw [himg] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : 0 < x := hx
  have hrx : 0 < Muon.DetEquiv.rW (Muon.emaW β) x := by
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx0.le) hx0
    rwa [hr0] at this
  have hQ := P5_Qlevel hβ0 hβ1 hrx
  have hQx : isoQlevel β (Muon.DetEquiv.rW (Muon.emaW β) x) = x :=
    hmono.injOn (Set.mem_Ici.2 hQ.1.le) (Set.mem_Ici.2 hx0.le) hQ.2
  rw [hQx, abs_of_pos (P5_hasDeriv hβ0 hβ1 hx0).2]


/-- Private helper (task P-F.9.P6). -/
private lemma P6_avg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (Ψ : ℝ × ℝ → ℝ) (hΨ : Measurable Ψ) :
    ENNReal.ofReal (1 / Real.pi ^ 2) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), ENNReal.ofReal (isoDivDiff β p.1 p.2 * Ψ p) =
      ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, ENNReal.ofReal (Ψ (isoPairMap (isoQlevel β η) w)) ∂isoNuStar := by
  have hS : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  refine Eq.trans ?_ (P6_subst hβ0 hβ1
    (fun s => ∫⁻ w, ENNReal.ofReal (Ψ (isoPairMap s w)) ∂isoNuStar)).symm
  rw [setLIntegral_congr_fun measurableSet_Ioi (fun s _ => by rw [P6_decomp s Ψ hΨ])]
  simp_rw [mul_add]
  have hmE : ∀ Φ : ℝ × ℝ → ℝ, Measurable Φ → Measurable fun s : ℝ =>
      ENNReal.ofReal (deriv (Muon.DetEquiv.rW (Muon.emaW β)) s) *
        ∫⁻ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ),
          ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))) *
            ENNReal.ofReal (Φ (s * Real.exp p.1, s * Real.exp (-p.2))) := by
    intro Φ hΦ
    refine (measurable_deriv _).ennreal_ofReal.mul ?_
    have hm : Measurable fun z : ℝ × (ℝ × ℝ) => (z.1 * Real.exp z.2.1, z.1 * Real.exp (-z.2.2)) := by
      fun_prop
    have hf : Measurable fun z : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((z.2.1 + z.2.2) / 2)))) *
          ENNReal.ofReal (Φ (z.1 * Real.exp z.2.1, z.1 * Real.exp (-z.2.2))) := by
      refine Measurable.mul ?_ (hΦ.comp hm).ennreal_ofReal
      have : Measurable fun z : ℝ × (ℝ × ℝ) =>
          1 / (Real.pi ^ 2 * (2 * Real.sinh ((z.2.1 + z.2.2) / 2))) := by fun_prop
      exact this.ennreal_ofReal
    exact Measurable.lintegral_prod_right' (ν := volume.restrict (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))) hf
  rw [lintegral_add_left (hmE Ψ hΨ), P6_part hβ0 hβ1 Ψ hΨ,
    P6_part hβ0 hβ1 (Ψ ∘ Prod.swap) (hΨ.comp measurable_swap), ← P6_sym_part (β := β) Ψ]
  have hT : MeasurableSet {q : ℝ × ℝ | q.2 < q.1} := measurableSet_lt measurable_snd measurable_fst
  have hT' : MeasurableSet {q : ℝ × ℝ | q.1 < q.2} := measurableSet_lt measurable_fst measurable_snd
  have hdisj : Disjoint ({q : ℝ × ℝ | q.2 < q.1} ∩ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)))
      ({q : ℝ × ℝ | q.1 < q.2} ∩ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))) := by
    rw [Set.disjoint_left]
    intro q hq hq'
    have h1 : q.2 < q.1 := hq.1
    have h2 : q.1 < q.2 := hq'.1
    linarith
  rw [← lintegral_union (hT'.inter hS) hdisj]
  have hΔ : (volume : Measure (ℝ × ℝ)) {q : ℝ × ℝ | q.1 = q.2} = 0 := by
    refine P5_null_of_slices (measurableSet_eq_fun measurable_fst measurable_snd) ?_
    intro a b₁ b₂ h1 h2
    have h1' : a = b₁ := h1
    have h2' : a = b₂ := h2
    rw [← h1', ← h2']
  have hae : (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) =ᵐ[volume]
      (({q : ℝ × ℝ | q.2 < q.1} ∩ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))) ∪
        ({q : ℝ × ℝ | q.1 < q.2} ∩ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)))) := by
    have heq : (({q : ℝ × ℝ | q.2 < q.1} ∩ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))) ∪
        ({q : ℝ × ℝ | q.1 < q.2} ∩ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)))) =
        (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) \ {q : ℝ × ℝ | q.1 = q.2} := by
      ext q
      simp only [mem_union, mem_inter_iff, mem_setOf_eq, mem_diff]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h2, h1.ne'⟩
        · exact ⟨h2, h1.ne⟩
      · rintro ⟨h2, h1⟩
        rcases lt_or_gt_of_ne h1 with h | h
        · exact Or.inr ⟨h, h2⟩
        · exact Or.inl ⟨h, h2⟩
    rw [heq]
    exact (diff_null_ae_eq_self hΔ).symm
  rw [← setLIntegral_congr hae, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- `lem:app-iso-averaging`(i), snapshot `cr-2026-10-23`. Part (i): the layer-averaging identity for nonnegative `Ψ` (lower integrals; `Ψ` measurable as a formalization-side hypothesis).
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Layer averaging]\label{lem:app-iso-averaging}
Let $\nu_\star$ be the measure on $\{+,-\}\times(0,\infty)^2$ whose density in $(a,c)$
on each of the two copies is
\[
\frac1{\pi^2}\cdot\frac1{2\sinh\big((a+c)/2\big)} ,
\]
write $\EE_\star$ for the integral against it, and put $\tau\defeq a+c$,
\[
\Pi_+(s;a,c)\defeq(se^a,se^{-c}),\qquad \Pi_-(s;a,c)\defeq(se^{-c},se^a).
\]
\begin{enumerate}[label=(\roman*)]
\item $\nu_\star$ is a probability measure, and for every nonnegative function $\Psi$ on $(0,\infty)^2$,
\begin{equation}\label{eqn:app-iso-averaging}
\frac1{\pi^2}\int_0^\infty\!\!\int_0^\infty D(y,z)\,\Psi(y,z)\,\dif y\,\dif z=\int_0^\infty\EE_\star\big[\Psi\big(\Pi(Q_\eta;\cdot)\big)\big]\,\dif\eta .
\end{equation}
\item The moments $\mathsf M_k\defeq\EE_\star\tau^k$ and $\mathsf M_e\defeq\EE_\star e^{\tau/4}$ are
\[
\mathsf M_1=\frac{28\,\zeta(3)}{\pi^2}=3.41023\ldots,\quad
\mathsf M_2=2\pi^2,
\]
\[
\mathsf M_3=\frac{1488\,\zeta(5)}{\pi^2}=156.333\ldots,\quad
\mathsf M_e=2+\frac{16\,\mathrm G}{\pi^2}=3.48491\ldots,
\]
where $\mathrm G=0.91596\ldots$ is Catalan's constant.
\item If $(y,z)=\Pi(s;a,c)$, then $\abs{\log(y/s)}\le\tau$, $\abs{\log(z/s)}\le\tau$,
$\abs{\mathsf A(y)-\mathsf A(s)}\le\bar{\mathsf e}_\bmom\tau$, $\abs{\mathsf A(z)-\mathsf A(s)}\le\bar{\mathsf e}_\bmom\tau$ and $z\ge se^{-\tau}$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_averaging_i {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsProbabilityMeasure isoNuStar ∧
    ∀ Ψ : ℝ × ℝ → ℝ, Measurable Ψ → (∀ p, 0 ≤ Ψ p) →
      ENNReal.ofReal (1 / Real.pi ^ 2) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), ENNReal.ofReal (isoDivDiff β p.1 p.2 * Ψ p) =
      ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, ENNReal.ofReal (Ψ (isoPairMap (isoQlevel β η) w)) ∂isoNuStar := by
  exact ⟨P6_mass, fun Ψ hΨ _ => P6_avg hβ0 hβ1 Ψ hΨ⟩

/-- Private helper (task P-F.9.P7): residual participation moves by at most `ē_β` times the log-distance. -/
private lemma P7_resid_le {β γ s y t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs : 0 < s) (hy : 0 < y)
    (ht : |Real.log (y / s)| ≤ t) : |isoResid β γ y - isoResid β γ s| ≤ isoEbar β * t := by
  have hE : 0 ≤ isoEbar β := le_trans zero_le_one (le_max_left _ _)
  have h := lem_app_iso_shifts_iv hβ0 hβ1 y s hy hs
  have he : isoResid β γ y - isoResid β γ s =
      -(rW (Muon.emaW β) y - rW (Muon.emaW β) s) := by
    unfold isoResid; ring
  rw [he, abs_neg]
  exact h.trans (mul_le_mul_of_nonneg_left ht hE)

/-- Private helper (task P-F.9.P7): `log (s e^x / s) = x`. -/
private lemma P7_log_exp {s x : ℝ} (hs : 0 < s) : Real.log (s * Real.exp x / s) = x := by
  rw [show s * Real.exp x / s = Real.exp x from by field_simp, Real.log_exp]

/-- Private helper (task P-F.9.P7). -/
private lemma P7_mono (j : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (x ^ j * Real.exp (-(c * x))) =
      ENNReal.ofReal ((j.factorial : ℝ) / c ^ (j + 1)) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ (j : ℝ) * Real.exp (-c * x ^ (1:ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (j : ℝ)) (b := c)
      (by have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith) one_pos hc
  have hint' : IntegrableOn (fun x : ℝ => x ^ j * Real.exp (-(c * x))) (Ioi 0) := by
    refine hint.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp [Real.rpow_natCast]
  rw [← ofReal_integral_eq_lintegral_ofReal hint'
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact mul_nonneg (pow_nonneg (le_of_lt hx) _) (Real.exp_pos _).le)]
  congr 1
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (j : ℝ) + 1) (r := c)
    (by positivity) hc
  have e1 : ∫ t : ℝ in Ioi 0, t ^ (((j : ℝ) + 1) - 1) * Real.exp (-(c * t)) =
      ∫ t : ℝ in Ioi 0, t ^ j * Real.exp (-(c * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp [Real.rpow_natCast]
  rw [e1, Real.Gamma_nat_eq_factorial] at h
  have e : c ^ ((j : ℝ) + 1) = c ^ (j + 1) := by
    exact_mod_cast Real.rpow_natCast c (j + 1)
  rw [h, one_div, Real.inv_rpow hc.le, e]
  field_simp

/-- Private helper (task P-F.9.P7). -/
private lemma P7_prod_int {F G : ℝ → ENNReal} (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ q in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), F q.1 * G q.2 =
      (∫⁻ x in Ioi (0:ℝ), F x) * ∫⁻ x in Ioi (0:ℝ), G x := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact lintegral_prod_mul (f := F) (g := G) hF.aemeasurable hG.aemeasurable

/-- Private helper (task P-F.9.P7). -/
private lemma P7_T (p : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫⁻ q in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), ENNReal.ofReal ((q.1 + q.2) ^ p) *
        (ENNReal.ofReal (Real.exp (-c * q.1)) * ENNReal.ofReal (Real.exp (-c * q.2))) =
      ENNReal.ofReal (((p + 1).factorial : ℝ) / c ^ (p + 2)) := by
  have hS : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hterm : ∀ q ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), ENNReal.ofReal ((q.1 + q.2) ^ p) *
        (ENNReal.ofReal (Real.exp (-c * q.1)) * ENNReal.ofReal (Real.exp (-c * q.2))) =
      ∑ j ∈ Finset.range (p + 1),
        ENNReal.ofReal (p.choose j : ℝ) *
          (ENNReal.ofReal (q.1 ^ j * Real.exp (-(c * q.1))) *
            ENNReal.ofReal (q.2 ^ (p - j) * Real.exp (-(c * q.2)))) := by
    intro q hq
    have h1 : 0 < q.1 := hq.1
    have h2 : 0 < q.2 := hq.2
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
      add_pow, Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring_nf
  rw [setLIntegral_congr_fun hS hterm, lintegral_finsetSum _ (fun j _ => by fun_prop)]
  have hj : ∀ j ∈ Finset.range (p + 1),
      ∫⁻ q in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), ENNReal.ofReal (p.choose j : ℝ) *
          (ENNReal.ofReal (q.1 ^ j * Real.exp (-(c * q.1))) *
            ENNReal.ofReal (q.2 ^ (p - j) * Real.exp (-(c * q.2)))) =
        ENNReal.ofReal ((p.factorial : ℝ) / c ^ (p + 2)) := by
    intro j hjm
    have hjp : j ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hjm)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      P7_prod_int (F := fun x => ENNReal.ofReal (x ^ j * Real.exp (-(c * x))))
        (G := fun x => ENNReal.ofReal (x ^ (p - j) * Real.exp (-(c * x)))) (by fun_prop) (by fun_prop),
      P7_mono j hc, P7_mono (p - j) hc,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hc0 : c ≠ 0 := hc.ne'
    have hchoose : (p.choose j : ℝ) * (j.factorial : ℝ) * ((p - j).factorial : ℝ) = p.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjp
    have e : c ^ (j + 1) * c ^ (p - j + 1) = c ^ (p + 2) := by
      rw [← pow_add]; congr 1; omega
    rw [div_mul_div_comm, e, ← hchoose]
    ring
  rw [Finset.sum_congr rfl hj, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast (p + 1), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- Private helper (task P-F.9.P7). -/
private lemma P7_dens {p : ℝ × ℝ} (hp : p ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) :
    ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))) =
        ∑' k : ℕ, ENNReal.ofReal (1 / Real.pi ^ 2) *
          (ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * p.1)) *
            ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * p.2))) := by
    have hτ : 0 < p.1 + p.2 := add_pos hp.1 hp.2
    have hs := (P6_ker_series hτ).mul_left (1 / Real.pi ^ 2)
    have hpi : (0:ℝ) < Real.pi ^ 2 := by positivity
    have e1 : 1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2))) =
        ∑' k : ℕ, 1 / Real.pi ^ 2 * Real.exp (-(((2 * (k : ℝ) + 1) / 2) * (p.1 + p.2))) := by
      rw [hs.tsum_eq]; field_simp
    rw [e1, ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs.summable]
    refine tsum_congr fun k => ?_
    rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 2
    rw [← Real.exp_add]; congr 1; ring

/-- Private helper (task P-F.9.P7). -/
private lemma P7_lint (Φ : ℝ → ℝ) (hΦ : Measurable Φ) :
    ∫⁻ w, ENNReal.ofReal (Φ (w.2.1 + w.2.2)) ∂isoNuStar =
      2 * ∑' k : ℕ, ENNReal.ofReal (1 / Real.pi ^ 2) *
        ∫⁻ q in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), ENNReal.ofReal (Φ (q.1 + q.2)) *
          (ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * q.1)) *
            ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * q.2))) := by
  have := P6_sfinite
  have hS : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hmeas : Measurable fun w : Bool × ℝ × ℝ => ENNReal.ofReal (Φ (w.2.1 + w.2.2)) :=
    (hΦ.comp (by fun_prop)).ennreal_ofReal
  unfold isoNuStar
  rw [lintegral_prod _ hmeas.aemeasurable, lintegral_count, tsum_fintype, Fintype.sum_bool,
    ← two_mul]
  congr 1
  have hρ : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))) := by
    fun_prop
  have hΦ' : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Φ (p.1 + p.2)) :=
    (hΦ.comp (by fun_prop)).ennreal_ofReal
  unfold isoNuBase
  rw [lintegral_withDensity_eq_lintegral_mul _ hρ hΦ']
  have hfun : ∀ p ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ),
      ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))) *
        ENNReal.ofReal (Φ (p.1 + p.2)) =
      ∑' k : ℕ, ENNReal.ofReal (1 / Real.pi ^ 2) *
        (ENNReal.ofReal (Φ (p.1 + p.2)) *
          (ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * p.1)) *
            ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * p.2)))) := by
    intro p hp
    rw [P7_dens hp, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun k => ?_
    ring
  have hmk : ∀ k : ℕ, Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / Real.pi ^ 2) *
        (ENNReal.ofReal (Φ (p.1 + p.2)) *
          (ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * p.1)) *
            ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * p.2)))) := by
    intro k
    refine measurable_const.mul (hΦ'.mul ?_)
    exact (by fun_prop : Measurable fun p : ℝ × ℝ =>
      Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * p.1)).ennreal_ofReal.mul
      (by fun_prop : Measurable fun p : ℝ × ℝ =>
      Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * p.2)).ennreal_ofReal
  show ∫⁻ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), _ * _ = _
  rw [setLIntegral_congr_fun hS hfun, lintegral_tsum (fun k => (hmk k).aemeasurable)]
  refine tsum_congr fun k => ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]


/-- Private helper (task P-F.9.P7). -/
private lemma P7_ae : ∀ᵐ w ∂isoNuStar, 0 < w.2.1 ∧ 0 < w.2.2 := by
  have := P6_sfinite
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

/-- Private helper (task P-F.9.P7). -/
private lemma P7_odd {s : ℕ} (hs : 2 ≤ s) :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ s)
      ((1 - 1 / 2 ^ s) * ∑' n : ℕ, 1 / (n : ℝ) ^ s) := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ s) :=
    Real.summable_one_div_nat_pow.2 (by omega)
  have hinj1 : Function.Injective (fun k : ℕ => 2 * k) := fun a b hab => by simpa using hab
  have hinj2 : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b hab => by simpa using hab
  have he : Summable (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ s) := hsum.comp_injective hinj1
  have ho : Summable (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ s) := hsum.comp_injective hinj2
  have hsp := tsum_even_add_odd (f := fun n : ℕ => 1 / (n : ℝ) ^ s) he ho
  have h4 : ∑' k : ℕ, 1 / ((2 * k : ℕ) : ℝ) ^ s = (1 / 2 ^ s) * ∑' n : ℕ, 1 / (n : ℝ) ^ s := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    push_cast
    rcases eq_or_ne (k : ℝ) 0 with h0 | h0
    · rw [h0]; simp [zero_pow (by omega : s ≠ 0)]
    · rw [mul_pow]; field_simp
  have hodd : ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ s =
      (1 - 1 / 2 ^ s) * ∑' n : ℕ, 1 / (n : ℝ) ^ s := by linarith
  have := ho.hasSum
  rw [hodd] at this
  convert this using 1
  funext k; push_cast; rfl

/-- Private helper (task P-F.9.P7). -/
private lemma P7_zeta {k : ℕ} (hk : 2 ≤ k) : (riemannZeta (k : ℂ)).re = ∑' n : ℕ, 1 / (n : ℝ) ^ k := by
  rw [zeta_nat_eq_tsum_of_gt_one (by omega)]
  have : (∑' n : ℕ, 1 / (n : ℂ) ^ k) = ((∑' n : ℕ, 1 / (n : ℝ) ^ k : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    push_cast; rfl
  rw [this, Complex.ofReal_re]


/-- Private helper (task P-F.9.P7). -/
private lemma P7_mom (p : ℕ) :
    ∫ w, (w.2.1 + w.2.2) ^ p ∂isoNuStar =
      2 / Real.pi ^ 2 * ((p + 1).factorial : ℝ) * 2 ^ (p + 2) *
        ∑' k : ℕ, 1 / (2 * (k : ℝ) + 1) ^ (p + 2) := by
  have hpi : (0:ℝ) < Real.pi ^ 2 := by positivity
  have hnn : 0 ≤ᵐ[isoNuStar] fun w : Bool × ℝ × ℝ => (w.2.1 + w.2.2) ^ p := by
    filter_upwards [P7_ae] with w hw
    exact pow_nonneg (add_pos hw.1 hw.2).le _
  rw [integral_eq_lintegral_of_nonneg_ae hnn (by fun_prop)]
  have h := P7_lint (fun x : ℝ => x ^ p) (by fun_prop)
  beta_reduce at h
  rw [h]
  have hk : ∀ k : ℕ, ENNReal.ofReal (1 / Real.pi ^ 2) *
      ∫⁻ q in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), ENNReal.ofReal ((q.1 + q.2) ^ p) *
          (ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * q.1)) *
            ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * q.2))) =
      ENNReal.ofReal (1 / Real.pi ^ 2 * (((p + 1).factorial : ℝ) * 2 ^ (p + 2) *
        (1 / (2 * (k : ℝ) + 1) ^ (p + 2)))) := by
    intro k
    rw [P7_T p (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : (0:ℝ) < 2 * (k : ℝ) + 1 := by positivity
    rw [div_pow]
    field_simp
  simp_rw [hk]
  have hsum : Summable (fun k : ℕ => 1 / Real.pi ^ 2 * (((p + 1).factorial : ℝ) * 2 ^ (p + 2) *
        (1 / (2 * (k : ℝ) + 1) ^ (p + 2)))) :=
    ((P7_odd (s := p + 2) (by omega)).summable.mul_left (((p + 1).factorial : ℝ) * 2 ^ (p + 2))).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum,
    show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.toReal_ofReal (by positivity), tsum_mul_left, tsum_mul_left]
  ring


/-- Private helper (task P-F.9.P7). -/
private lemma P7_cat : ∑' k : ℕ, 1 / (4 * (k : ℝ) + 1) ^ 2 =
    Real.pi ^ 2 / 16 + isoCatalan / 2 := by
  have hf : Summable (fun m : ℕ => 1 / (2 * (m : ℝ) + 1) ^ 2) := (P7_odd (s := 2) le_rfl).summable
  have htot : ∑' m : ℕ, 1 / (2 * (m : ℝ) + 1) ^ 2 = Real.pi ^ 2 / 8 := by
    rw [(P7_odd (s := 2) le_rfl).tsum_eq, hasSum_zeta_two.tsum_eq]; ring
  have hinj1 : Function.Injective (fun k : ℕ => 2 * k) := fun a b hab => by simpa using hab
  have hinj2 : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b hab => by simpa using hab
  have he : Summable (fun k : ℕ => 1 / (2 * ((2 * k : ℕ) : ℝ) + 1) ^ 2) := hf.comp_injective hinj1
  have ho : Summable (fun k : ℕ => 1 / (2 * ((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2) :=
    hf.comp_injective hinj2
  have h1 := tsum_even_add_odd (f := fun m : ℕ => 1 / (2 * (m : ℝ) + 1) ^ 2) he ho
  have hg : Summable (fun m : ℕ => (-1 : ℝ) ^ m / (2 * (m : ℝ) + 1) ^ 2) := by
    refine Summable.of_norm (hf.congr fun m => ?_)
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have heg : Summable (fun k : ℕ => (-1 : ℝ) ^ (2 * k) / (2 * ((2 * k : ℕ) : ℝ) + 1) ^ 2) :=
    hg.comp_injective hinj1
  have hog : Summable (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / (2 * ((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2) :=
    hg.comp_injective hinj2
  have h2 := tsum_even_add_odd (f := fun m : ℕ => (-1 : ℝ) ^ m / (2 * (m : ℝ) + 1) ^ 2) heg hog
  have e1 : ∀ k : ℕ, (-1 : ℝ) ^ (2 * k) / (2 * ((2 * k : ℕ) : ℝ) + 1) ^ 2 =
      1 / (2 * ((2 * k : ℕ) : ℝ) + 1) ^ 2 := fun k => by rw [pow_mul]; simp
  have e2 : ∀ k : ℕ, (-1 : ℝ) ^ (2 * k + 1) / (2 * ((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2 =
      -(1 / (2 * ((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2) := fun k => by
    rw [pow_succ, pow_mul]; simp [neg_div]
  simp_rw [e1, e2] at h2
  rw [tsum_neg] at h2
  unfold isoCatalan
  have e3 : ∀ k : ℕ, 1 / (2 * ((2 * k : ℕ) : ℝ) + 1) ^ 2 = 1 / (4 * (k : ℝ) + 1) ^ 2 :=
    fun k => by push_cast; ring_nf
  simp_rw [e3] at h1 h2
  rw [htot] at h1
  linarith

/-- Private helper (task P-F.9.P7). -/
private lemma P7_exp :
    ∫ w, Real.exp ((w.2.1 + w.2.2) / 4) ∂isoNuStar =
      32 / Real.pi ^ 2 * ∑' k : ℕ, 1 / (4 * (k : ℝ) + 1) ^ 2 := by
  have hpi : (0:ℝ) < Real.pi ^ 2 := by positivity
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => (Real.exp_pos _).le)
    (by fun_prop)]
  have h := P7_lint (fun x : ℝ => Real.exp (x / 4)) (by fun_prop)
  beta_reduce at h
  rw [h]
  have hk : ∀ k : ℕ, ENNReal.ofReal (1 / Real.pi ^ 2) *
      ∫⁻ q in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), ENNReal.ofReal (Real.exp ((q.1 + q.2) / 4)) *
          (ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * q.1)) *
            ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * q.2))) =
      ENNReal.ofReal (1 / Real.pi ^ 2 * (16 * (1 / (4 * (k : ℝ) + 1) ^ 2))) := by
    intro k
    have hl : (0:ℝ) < (2 * (k : ℝ) + 1) / 2 - 1 / 4 := by
      have : (0:ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hT := P7_T 0 hl
    have hpt : ∀ q : ℝ × ℝ, ENNReal.ofReal (Real.exp ((q.1 + q.2) / 4)) *
          (ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * q.1)) *
            ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * q.2))) =
        ENNReal.ofReal ((q.1 + q.2) ^ 0) *
          (ENNReal.ofReal (Real.exp (-((2 * (k : ℝ) + 1) / 2 - 1 / 4) * q.1)) *
            ENNReal.ofReal (Real.exp (-((2 * (k : ℝ) + 1) / 2 - 1 / 4) * q.2))) := by
      intro q
      rw [pow_zero, ENNReal.ofReal_one, one_mul, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      simp only [← Real.exp_add]
      congr 1
      ring
    simp_rw [hpt]
    rw [hT, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : (0:ℝ) < 4 * (k : ℝ) + 1 := by positivity
    have e : (2 * (k : ℝ) + 1) / 2 - 1 / 4 = (4 * (k : ℝ) + 1) / 4 := by ring
    rw [e, div_pow]
    norm_num
    field_simp
  simp_rw [hk]
  have hs4 : Summable (fun k : ℕ => 1 / (4 * (k : ℝ) + 1) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (P7_odd (s := 2) le_rfl).summable
    apply one_div_le_one_div_of_le (by positivity)
    have : (0:ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hsum : Summable (fun k : ℕ => 1 / Real.pi ^ 2 * (16 * (1 / (4 * (k : ℝ) + 1) ^ 2))) :=
    (hs4.mul_left 16).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum,
    show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.toReal_ofReal (by positivity), tsum_mul_left, tsum_mul_left]
  ring


/-- Private helper (task P-F.9.P7). -/
private lemma P7_main :
    (∫ w, (w.2.1 + w.2.2) ∂isoNuStar = 28 * (riemannZeta 3).re / Real.pi ^ 2) ∧
    (∫ w, (w.2.1 + w.2.2) ^ 2 ∂isoNuStar = 2 * Real.pi ^ 2) ∧
    (∫ w, (w.2.1 + w.2.2) ^ 3 ∂isoNuStar = 1488 * (riemannZeta 5).re / Real.pi ^ 2) ∧
    (∫ w, Real.exp ((w.2.1 + w.2.2) / 4) ∂isoNuStar = 2 + 16 * isoCatalan / Real.pi ^ 2) := by
  have hpi : (0:ℝ) < Real.pi ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := P7_mom 1
    simp only [pow_one] at h
    rw [h, (P7_odd (s := 3) (by norm_num)).tsum_eq]
    have hz := P7_zeta (k := 3) (by norm_num)
    norm_num at hz ⊢
    rw [hz]
    field_simp
    ring
  · have h := P7_mom 2
    rw [h, (P7_odd (s := 4) (by norm_num)).tsum_eq]
    have hz : ∑' n : ℕ, 1 / (n : ℝ) ^ 4 = Real.pi ^ 4 / 90 := hasSum_zeta_four.tsum_eq
    rw [hz]
    norm_num [Nat.factorial]
    field_simp
    ring
  · have h := P7_mom 3
    rw [h, (P7_odd (s := 5) (by norm_num)).tsum_eq]
    have hz := P7_zeta (k := 5) (by norm_num)
    norm_num [Nat.factorial] at hz ⊢
    rw [hz]
    field_simp
    ring
  · rw [P7_exp, P7_cat]
    field_simp
    ring

/-- `lem:app-iso-averaging`(ii), snapshot `cr-2026-10-23`. Part (ii): the moments `𝖬_1, 𝖬_2, 𝖬_3` of `τ = a + c` and `𝖬_e` of `e^{τ/4}` under `ν⋆`, in closed form.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Layer averaging]\label{lem:app-iso-averaging}
Let $\nu_\star$ be the measure on $\{+,-\}\times(0,\infty)^2$ whose density in $(a,c)$
on each of the two copies is
\[
\frac1{\pi^2}\cdot\frac1{2\sinh\big((a+c)/2\big)} ,
\]
write $\EE_\star$ for the integral against it, and put $\tau\defeq a+c$,
\[
\Pi_+(s;a,c)\defeq(se^a,se^{-c}),\qquad \Pi_-(s;a,c)\defeq(se^{-c},se^a).
\]
\begin{enumerate}[label=(\roman*)]
\item $\nu_\star$ is a probability measure, and for every nonnegative function $\Psi$ on $(0,\infty)^2$,
\begin{equation}\label{eqn:app-iso-averaging}
\frac1{\pi^2}\int_0^\infty\!\!\int_0^\infty D(y,z)\,\Psi(y,z)\,\dif y\,\dif z=\int_0^\infty\EE_\star\big[\Psi\big(\Pi(Q_\eta;\cdot)\big)\big]\,\dif\eta .
\end{equation}
\item The moments $\mathsf M_k\defeq\EE_\star\tau^k$ and $\mathsf M_e\defeq\EE_\star e^{\tau/4}$ are
\[
\mathsf M_1=\frac{28\,\zeta(3)}{\pi^2}=3.41023\ldots,\quad
\mathsf M_2=2\pi^2,
\]
\[
\mathsf M_3=\frac{1488\,\zeta(5)}{\pi^2}=156.333\ldots,\quad
\mathsf M_e=2+\frac{16\,\mathrm G}{\pi^2}=3.48491\ldots,
\]
where $\mathrm G=0.91596\ldots$ is Catalan's constant.
\item If $(y,z)=\Pi(s;a,c)$, then $\abs{\log(y/s)}\le\tau$, $\abs{\log(z/s)}\le\tau$,
$\abs{\mathsf A(y)-\mathsf A(s)}\le\bar{\mathsf e}_\bmom\tau$, $\abs{\mathsf A(z)-\mathsf A(s)}\le\bar{\mathsf e}_\bmom\tau$ and $z\ge se^{-\tau}$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_averaging_ii :
    (∫ w, (w.2.1 + w.2.2) ∂isoNuStar = 28 * (riemannZeta 3).re / Real.pi ^ 2) ∧
    (∫ w, (w.2.1 + w.2.2) ^ 2 ∂isoNuStar = 2 * Real.pi ^ 2) ∧
    (∫ w, (w.2.1 + w.2.2) ^ 3 ∂isoNuStar = 1488 * (riemannZeta 5).re / Real.pi ^ 2) ∧
    (∫ w, Real.exp ((w.2.1 + w.2.2) / 4) ∂isoNuStar = 2 + 16 * isoCatalan / Real.pi ^ 2) := by
  exact P7_main

/-- `lem:app-iso-averaging`(iii), snapshot `cr-2026-10-23`. Part (iii): the pair `Π(s;a,c)` stays within `τ` of `s` in the logarithmic scale, and `𝖠` moves by at most `𝖾̄_β τ`.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Layer averaging]\label{lem:app-iso-averaging}
Let $\nu_\star$ be the measure on $\{+,-\}\times(0,\infty)^2$ whose density in $(a,c)$
on each of the two copies is
\[
\frac1{\pi^2}\cdot\frac1{2\sinh\big((a+c)/2\big)} ,
\]
write $\EE_\star$ for the integral against it, and put $\tau\defeq a+c$,
\[
\Pi_+(s;a,c)\defeq(se^a,se^{-c}),\qquad \Pi_-(s;a,c)\defeq(se^{-c},se^a).
\]
\begin{enumerate}[label=(\roman*)]
\item $\nu_\star$ is a probability measure, and for every nonnegative function $\Psi$ on $(0,\infty)^2$,
\begin{equation}\label{eqn:app-iso-averaging}
\frac1{\pi^2}\int_0^\infty\!\!\int_0^\infty D(y,z)\,\Psi(y,z)\,\dif y\,\dif z=\int_0^\infty\EE_\star\big[\Psi\big(\Pi(Q_\eta;\cdot)\big)\big]\,\dif\eta .
\end{equation}
\item The moments $\mathsf M_k\defeq\EE_\star\tau^k$ and $\mathsf M_e\defeq\EE_\star e^{\tau/4}$ are
\[
\mathsf M_1=\frac{28\,\zeta(3)}{\pi^2}=3.41023\ldots,\quad
\mathsf M_2=2\pi^2,
\]
\[
\mathsf M_3=\frac{1488\,\zeta(5)}{\pi^2}=156.333\ldots,\quad
\mathsf M_e=2+\frac{16\,\mathrm G}{\pi^2}=3.48491\ldots,
\]
where $\mathrm G=0.91596\ldots$ is Catalan's constant.
\item If $(y,z)=\Pi(s;a,c)$, then $\abs{\log(y/s)}\le\tau$, $\abs{\log(z/s)}\le\tau$,
$\abs{\mathsf A(y)-\mathsf A(s)}\le\bar{\mathsf e}_\bmom\tau$, $\abs{\mathsf A(z)-\mathsf A(s)}\le\bar{\mathsf e}_\bmom\tau$ and $z\ge se^{-\tau}$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_averaging_iii {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ s : ℝ, 0 < s → ∀ (b : Bool) (a c : ℝ), 0 ≤ a → 0 ≤ c →
      let p := isoPairMap s (b, a, c)
      |Real.log (p.1 / s)| ≤ a + c ∧ |Real.log (p.2 / s)| ≤ a + c ∧
      |isoResid β γ p.1 - isoResid β γ s| ≤ isoEbar β * (a + c) ∧
      |isoResid β γ p.2 - isoResid β γ s| ≤ isoEbar β * (a + c) ∧
      s * Real.exp (-(a + c)) ≤ p.2 := by
  intro s hs b a c ha hc
  dsimp only
  have hτ : 0 ≤ a + c := by linarith
  have hEx : ∀ x : ℝ, 0 < s * Real.exp x := fun x => mul_pos hs (Real.exp_pos x)
  have hlogA : |Real.log (s * Real.exp a / s)| ≤ a + c := by
    rw [P7_log_exp hs, abs_of_nonneg ha]; linarith
  have hlogC : |Real.log (s * Real.exp (-c) / s)| ≤ a + c := by
    rw [P7_log_exp hs, abs_neg, abs_of_nonneg hc]; linarith
  cases b
  · have hp : isoPairMap s (false, a, c) = (s * Real.exp (-c), s * Real.exp a) := by
      simp [isoPairMap]
    rw [hp]
    show |Real.log (s * Real.exp (-c) / s)| ≤ a + c ∧ |Real.log (s * Real.exp a / s)| ≤ a + c ∧
      |isoResid β γ (s * Real.exp (-c)) - isoResid β γ s| ≤ isoEbar β * (a + c) ∧
      |isoResid β γ (s * Real.exp a) - isoResid β γ s| ≤ isoEbar β * (a + c) ∧
      s * Real.exp (-(a + c)) ≤ s * Real.exp a
    have h5 : s * Real.exp (-(a + c)) ≤ s * Real.exp a :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hs.le
    exact ⟨hlogC, hlogA, P7_resid_le hβ0 hβ1 hs (hEx (-c)) hlogC,
      P7_resid_le hβ0 hβ1 hs (hEx a) hlogA, h5⟩
  · have hp : isoPairMap s (true, a, c) = (s * Real.exp a, s * Real.exp (-c)) := by
      simp [isoPairMap]
    rw [hp]
    show |Real.log (s * Real.exp a / s)| ≤ a + c ∧ |Real.log (s * Real.exp (-c) / s)| ≤ a + c ∧
      |isoResid β γ (s * Real.exp a) - isoResid β γ s| ≤ isoEbar β * (a + c) ∧
      |isoResid β γ (s * Real.exp (-c)) - isoResid β γ s| ≤ isoEbar β * (a + c) ∧
      s * Real.exp (-(a + c)) ≤ s * Real.exp (-c)
    have h5 : s * Real.exp (-(a + c)) ≤ s * Real.exp (-c) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hs.le
    exact ⟨hlogA, hlogC, P7_resid_le hβ0 hβ1 hs (hEx a) hlogA,
      P7_resid_le hβ0 hβ1 hs (hEx (-c)) hlogC, h5⟩

/-- `lem:app-iso-low-levels`(i), snapshot `cr-2026-10-23`. Part (i): the pointwise bound `𝗇^-_β(z) ≤ (τ − σ)_+/(2 log(1/β))` with `σ = log((1−β)² Q_η)`, for both copies and all `a, c ≥ 0`.
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Low levels]\label{lem:app-iso-low-levels}
For $\eta>0$ let $(y,z)=\Pi(Q_\eta;a,c)$ as in \cref{lem:app-iso-averaging}, and put
$\sigma\defeq\log\big((1-\bmom)^2Q_\eta\big)$. Then
\[
\mathsf n^-_\bmom(z)\le\frac{(\tau-\sigma)_+}{2\log(1/\bmom)},
\]
and $\mathsf L_k\defeq\int_0^\infty\EE_\star\big[\mathsf n^-_\bmom(z)^k\big]\,\dif\eta$ satisfies
$\mathsf L_k\le\bar{\mathsf L}_k$ for $k=1,2$, where
\[
\bar{\mathsf L}_1\defeq\frac1{2\log(1/\bmom)}\Big(\frac{\mathsf M_1+1}{1-\bmom^2}+\frac{\bar{\mathsf e}_\bmom\mathsf M_2}2\Big),\qquad
\bar{\mathsf L}_2\defeq\frac1{4\log^2(1/\bmom)}\Big(\frac{\mathsf M_2+2\mathsf M_1+2}{1-\bmom^2}+\frac{\bar{\mathsf e}_\bmom\mathsf M_3}3\Big).
\]
\end{lemma}
```
-/
theorem lem_app_iso_low_levels_i {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ η : ℝ, 0 < η → ∀ (b : Bool) (a c : ℝ), 0 ≤ a → 0 ≤ c →
      max 0 (-isoN β (isoPairMap (isoQlevel β η) (b, a, c)).2) ≤
        max 0 ((a + c) - Real.log ((1 - β) ^ 2 * isoQlevel β η)) / (2 * Real.log (1 / β)) := by
  intro η hη b a c ha hc
  have hsurj := ((lem_app_iso_weights_i hβ0.le hβ1).2.2.1 hβ0).2.2.2
  have hex : ∃ q : ℝ, 0 ≤ q ∧ rW (Muon.emaW β) q = η := by
    obtain ⟨q, hq, e⟩ := hsurj (show η ∈ Ici (0 : ℝ) from Set.mem_Ici.2 hη.le)
    exact ⟨q, hq, e⟩
  have hspec : 0 ≤ isoQlevel β η ∧ rW (Muon.emaW β) (isoQlevel β η) = η := by
    unfold isoQlevel
    rw [dif_pos hex]
    exact hex.choose_spec
  have hrW0 : rW (Muon.emaW β) 0 = 0 := by simp [rW]
  have hs : 0 < isoQlevel β η := by
    rcases hspec.1.eq_or_lt with h | h
    · exfalso
      rw [← h, hrW0] at hspec
      linarith [hspec.2]
    · exact h
  set s := isoQlevel β η with hsdef
  have H : s * Real.exp (-(a + c)) ≤ (isoPairMap s (b, a, c)).2 :=
    (lem_app_iso_averaging_iii (γ := 0) hβ0 hβ1 s hs b a c ha hc).2.2.2.2
  set z := (isoPairMap s (b, a, c)).2 with hzdef
  have hzpos : 0 < z := lt_of_lt_of_le (mul_pos hs (Real.exp_pos _)) H
  have hD : 0 < 2 * Real.log (1 / β) := by
    have : 0 < Real.log (1 / β) := Real.log_pos (one_lt_one_div hβ0 hβ1)
    linarith
  have hsq : 0 < (1 - β) ^ 2 := by
    have : 0 < 1 - β := by linarith
    positivity
  have hlogz : Real.log s + -(a + c) ≤ Real.log z := by
    have := Real.log_le_log (mul_pos hs (Real.exp_pos _)) H
    rwa [Real.log_mul hs.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  have hN : -isoN β z ≤ ((a + c) - Real.log ((1 - β) ^ 2 * s)) / (2 * Real.log (1 / β)) := by
    unfold isoN
    rw [Real.log_mul hsq.ne' hzpos.ne', Real.log_mul hsq.ne' hs.ne']
    have key : -((Real.log ((1 - β) ^ 2) + Real.log z) / (2 * Real.log (1 / β)))
        = (-(Real.log ((1 - β) ^ 2) + Real.log z)) / (2 * Real.log (1 / β)) :=
      (neg_div _ _).symm
    rw [key]
    apply div_le_div_of_nonneg_right _ hD.le
    linarith
  apply max_le
  · exact div_nonneg (le_max_left _ _) hD.le
  · calc -isoN β z ≤ ((a + c) - Real.log ((1 - β) ^ 2 * s)) / (2 * Real.log (1 / β)) := hN
      _ ≤ max 0 ((a + c) - Real.log ((1 - β) ^ 2 * s)) / (2 * Real.log (1 / β)) :=
          div_le_div_of_nonneg_right (le_max_right _ _) hD.le


/-- Private helper (task P-F.9.P8). -/
private lemma P8_ioi_tail {τ : ℝ} (hτ : 0 ≤ τ) {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal ((max 0 (τ - t)) ^ k) =
      ENNReal.ofReal (τ ^ (k + 1) / (k + 1)) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi hτ, lintegral_union measurableSet_Ioi
    (Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'))]
  have h2 : ∫⁻ t in Ioi τ, ENNReal.ofReal ((max 0 (τ - t)) ^ k) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0)]
    · simp
    · intro t ht
      have : max 0 (τ - t) = 0 := max_eq_left (by have := (mem_Ioi.1 ht); linarith)
      simp [this, zero_pow (by omega : k ≠ 0)]
  rw [h2, add_zero]
  have h1 : ∫⁻ t in Ioc 0 τ, ENNReal.ofReal ((max 0 (τ - t)) ^ k) =
      ∫⁻ t in Ioc 0 τ, ENNReal.ofReal ((τ - t) ^ k) := by
    refine setLIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    rw [max_eq_right (by linarith [ht.2])]
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← intervalIntegral.integral_of_le hτ, intervalIntegral.integral_comp_sub_left
      (fun x : ℝ => x ^ k) τ]
    simp [integral_pow]
  · exact (Continuous.integrableOn_Ioc (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pow_nonneg (by linarith [ht.2]) _

/-- Private helper (task P-F.9.P8). -/
private lemma P8_ioi_lin {τ E b : ℝ} (hτ : 0 ≤ τ) (hb : 0 < b) {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ η in Ioi E, ENNReal.ofReal ((max 0 (τ - (η - E) / b)) ^ k) =
      ENNReal.ofReal (b * (τ ^ (k + 1) / (k + 1))) := by
  have himg : (fun t : ℝ => E + b * t) '' Ioi 0 = Ioi E := by
    ext η
    constructor
    · rintro ⟨t, ht, rfl⟩
      simp only [mem_Ioi] at ht ⊢
      nlinarith
    · intro hη
      refine ⟨(η - E) / b, ?_, ?_⟩
      · simp only [mem_Ioi] at hη ⊢
        exact div_pos (by linarith) hb
      · field_simp; ring
  have hd : ∀ t ∈ Ioi (0:ℝ), HasDerivWithinAt (fun t : ℝ => E + b * t) b (Ioi 0) t := by
    intro t _
    exact (((hasDerivAt_id t).const_mul b).const_add E).hasDerivWithinAt.congr_deriv (by simp)
  have hinj : InjOn (fun t : ℝ => E + b * t) (Ioi 0) := by
    intro x _ y _ h
    simpa [hb.ne'] using h
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd hinj]
  have : ∀ t ∈ Ioi (0:ℝ), ENNReal.ofReal |b| *
      ENNReal.ofReal ((max 0 (τ - ((E + b * t) - E) / b)) ^ k) =
      ENNReal.ofReal b * ENNReal.ofReal ((max 0 (τ - t)) ^ k) := by
    intro t _
    rw [abs_of_pos hb, show (E + b * t - E) / b = t by field_simp; ring]
  rw [setLIntegral_congr_fun measurableSet_Ioi this, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    P8_ioi_tail hτ hk, ← ENNReal.ofReal_mul hb.le]

/-- Private helper (task P-F.9.P8). -/
private lemma P8_ioc_log {τ E : ℝ} (hE : 0 < E) (k : ℕ) :
    ∫⁻ η in Ioc 0 E, ENNReal.ofReal ((τ + Real.log (E / η)) ^ k) =
      ENNReal.ofReal E * ∫⁻ v in Ioi (0:ℝ), ENNReal.ofReal ((τ + v) ^ k * Real.exp (-v)) := by
  have himg : (fun v : ℝ => E * Real.exp (-v)) '' Ioi 0 = Ioo 0 E := by
    ext η
    constructor
    · rintro ⟨v, hv, rfl⟩
      simp only [mem_Ioi] at hv
      refine ⟨by positivity, ?_⟩
      have : Real.exp (-v) < 1 := by have := Real.exp_lt_exp.2 (show -v < 0 by linarith); simpa using this
      nlinarith
    · intro hη
      refine ⟨Real.log (E / η), ?_, ?_⟩
      · exact Real.log_pos ((one_lt_div hη.1).2 hη.2)
      · show E * Real.exp (-Real.log (E / η)) = η
        have := hη.1
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
  have hd : ∀ v ∈ Ioi (0:ℝ), HasDerivWithinAt (fun v : ℝ => E * Real.exp (-v))
      (-(E * Real.exp (-v))) (Ioi 0) v := by
    intro v _
    have := (((Real.hasDerivAt_exp (-v)).comp v (hasDerivAt_neg v)).const_mul E)
    exact this.hasDerivWithinAt.congr_deriv (by simp)
  have hinj : InjOn (fun v : ℝ => E * Real.exp (-v)) (Ioi 0) := by
    intro x _ y _ h
    have h' : Real.exp (-x) = Real.exp (-y) := by
      have := mul_left_cancel₀ hE.ne' h
      exact this
    have := Real.exp_injective h'
    linarith
  rw [setLIntegral_congr (Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := E)).symm, ← himg,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd hinj]
  have : ∀ v ∈ Ioi (0:ℝ), ENNReal.ofReal |-(E * Real.exp (-v))| *
      ENNReal.ofReal ((τ + Real.log (E / (E * Real.exp (-v)))) ^ k) =
      ENNReal.ofReal E * ENNReal.ofReal ((τ + v) ^ k * Real.exp (-v)) := by
    intro v _
    have hl : Real.log (E / (E * Real.exp (-v))) = v := by
      rw [div_mul_eq_div_div, div_self hE.ne', one_div, Real.log_inv, Real.log_exp, neg_neg]
    rw [hl, abs_neg, abs_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hE.le]
    congr 1; ring
  rw [setLIntegral_congr_fun measurableSet_Ioi this, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Private helper (task P-F.9.P8): the level `Q_η` is positive and solves `r(Q_η) = η`. -/
private lemma P8_Q {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {η : ℝ} (hη : 0 < η) :
    0 < isoQlevel β η ∧ rW (Muon.emaW β) (isoQlevel β η) = η := by
  have hsurj := ((lem_app_iso_weights_i hβ0.le hβ1).2.2.1 hβ0).2.2.2
  have hex : ∃ q : ℝ, 0 ≤ q ∧ rW (Muon.emaW β) q = η := by
    obtain ⟨q, hq, e⟩ := hsurj (show η ∈ Ici (0 : ℝ) from Set.mem_Ici.2 hη.le)
    exact ⟨q, hq, e⟩
  have hspec : 0 ≤ isoQlevel β η ∧ rW (Muon.emaW β) (isoQlevel β η) = η := by
    unfold isoQlevel
    rw [dif_pos hex]
    exact hex.choose_spec
  have hrW0 : rW (Muon.emaW β) 0 = 0 := by simp [rW]
  refine ⟨?_, hspec.2⟩
  rcases hspec.1.eq_or_lt with h | h
  · exfalso
    have h2 := hspec.2
    rw [← h, hrW0] at h2
    linarith
  · exact h

/-- Private helper (task P-F.9.P8): `r(s) ≤ s (1-β)/(1+β)`. -/
private lemma P8_r_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {s : ℝ} (hs : 0 ≤ s) :
    rW (Muon.emaW β) s ≤ s * ((1 - β) / (1 + β)) := by
  have h := (lem_app_iso_weights_v hβ0.le hβ1).1 s hs
  rw [Muon.sPow_two hβ0.le hβ1] at h
  unfold rW
  exact mul_le_mul_of_nonneg_left h hs

/-- Private helper (task P-F.9.P8): lower bound of `σ` in the low range. -/
private lemma P8_sigma_low {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {η : ℝ} (hη : 0 < η) :
    Real.log (η * (1 - β ^ 2)) ≤ Real.log ((1 - β) ^ 2 * isoQlevel β η) := by
  obtain ⟨hs, hr⟩ := P8_Q hβ0 hβ1 hη
  have h := P8_r_le hβ0 hβ1 hs.le
  rw [hr] at h
  have h1 : 0 < 1 - β := by linarith
  have h2 : 0 < 1 + β := by linarith
  have hpos : 0 < η * (1 - β ^ 2) := mul_pos hη (by nlinarith)
  apply Real.log_le_log hpos
  have : η * (1 - β ^ 2) ≤ isoQlevel β η * ((1 - β) / (1 + β)) * (1 - β ^ 2) :=
    mul_le_mul_of_nonneg_right h (by nlinarith)
  calc η * (1 - β ^ 2) ≤ _ := this
    _ = (1 - β) ^ 2 * isoQlevel β η := by field_simp; ring

/-- Private helper (task P-F.9.P8): lower bound of `σ` in the high range. -/
private lemma P8_sigma_high {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {η : ℝ} (hη : 1 / (1 - β ^ 2) < η) :
    (η - 1 / (1 - β ^ 2)) / isoEbar β ≤ Real.log ((1 - β) ^ 2 * isoQlevel β η) := by
  have h1 : 0 < 1 - β := by linarith
  have h2 : 0 < 1 + β := by linarith
  have hb2 : 0 < 1 - β ^ 2 := by nlinarith
  have hE0 : 0 < 1 / (1 - β ^ 2) := by positivity
  have hη0 : 0 < η := hE0.trans hη
  obtain ⟨hs, hr⟩ := P8_Q hβ0 hβ1 hη0
  set s := isoQlevel β η with hsdef
  set s0 : ℝ := 1 / (1 - β) ^ 2 with hs0
  have hs0pos : 0 < s0 := by positivity
  have hr0 : rW (Muon.emaW β) s0 ≤ 1 / (1 - β ^ 2) := by
    have := P8_r_le hβ0 hβ1 hs0pos.le
    refine this.trans (le_of_eq ?_)
    rw [hs0]; field_simp; ring
  have hmono : MonotoneOn (rW (Muon.emaW β)) (Ici 0) :=
    ((lem_app_iso_weights_i hβ0.le hβ1).2.2.1 hβ0).1.monotoneOn
  have hlt : s0 < s := by
    by_contra hcon
    push_neg at hcon
    have := hmono (Set.mem_Ici.2 hs.le) (Set.mem_Ici.2 hs0pos.le) hcon
    rw [hr] at this
    linarith
  have hshift := lem_app_iso_shifts_iv hβ0 hβ1 s s0 hs hs0pos
  have hlog : Real.log (s / s0) = Real.log ((1 - β) ^ 2 * s) := by
    congr 1; rw [hs0]; field_simp
  have hnn : 0 ≤ Real.log (s / s0) := Real.log_nonneg (by rw [le_div_iff₀ hs0pos]; linarith)
  rw [abs_of_nonneg hnn, hlog, hr] at hshift
  have hE : 0 < isoEbar β := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [div_le_iff₀ hE]
  have := (abs_le.1 hshift).2
  linarith

/-- Private helper (task P-F.9.P8): pointwise bound, low range. -/
private lemma P8_ptw_low {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {η : ℝ} (hη : 0 < η)
    (hηE : η ≤ 1 / (1 - β ^ 2)) (b : Bool) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    max 0 (-isoN β (isoPairMap (isoQlevel β η) (b, a, c)).2) ≤
      ((a + c) + Real.log ((1 / (1 - β ^ 2)) / η)) / (2 * Real.log (1 / β)) := by
  have h1 := lem_app_iso_low_levels_i hβ0 hβ1 η hη b a c ha hc
  have hD : 0 < 2 * Real.log (1 / β) := by
    have : 0 < Real.log (1 / β) := Real.log_pos (one_lt_one_div hβ0 hβ1)
    linarith
  have hb2 : 0 < 1 - β ^ 2 := by nlinarith
  have hsl := P8_sigma_low hβ0 hβ1 hη
  have hlogE : Real.log ((1 / (1 - β ^ 2)) / η) = - Real.log (η * (1 - β ^ 2)) := by
    rw [← Real.log_inv]; congr 1; field_simp
  have hge : 0 ≤ Real.log ((1 / (1 - β ^ 2)) / η) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hη]; linarith
  refine h1.trans (div_le_div_of_nonneg_right ?_ hD.le)
  apply max_le (by linarith)
  linarith

/-- Private helper (task P-F.9.P8): pointwise bound, high range. -/
private lemma P8_ptw_high {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {η : ℝ}
    (hηE : 1 / (1 - β ^ 2) < η) (b : Bool) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    max 0 (-isoN β (isoPairMap (isoQlevel β η) (b, a, c)).2) ≤
      max 0 ((a + c) - (η - 1 / (1 - β ^ 2)) / isoEbar β) / (2 * Real.log (1 / β)) := by
  have hb2 : 0 < 1 - β ^ 2 := by nlinarith
  have hη : 0 < η := (by positivity : (0:ℝ) < 1 / (1 - β ^ 2)).trans hηE
  have h1 := lem_app_iso_low_levels_i hβ0 hβ1 η hη b a c ha hc
  have hD : 0 < 2 * Real.log (1 / β) := by
    have : 0 < Real.log (1 / β) := Real.log_pos (one_lt_one_div hβ0 hβ1)
    linarith
  have hsh := P8_sigma_high hβ0 hβ1 hηE
  refine h1.trans (div_le_div_of_nonneg_right ?_ hD.le)
  apply max_le_max le_rfl
  linarith

/-- Private helper (task P-F.9.P8): the lower moments of `τ` are finite lintegrals. -/
private lemma P8_lint_pow (p : ℕ) :
    ∫⁻ w, ENNReal.ofReal ((w.2.1 + w.2.2) ^ p) ∂isoNuStar =
      ENNReal.ofReal (∫ w, (w.2.1 + w.2.2) ^ p ∂isoNuStar) := by
  rw [P7_mom p]
  have h := P7_lint (fun x : ℝ => x ^ p) (by fun_prop)
  beta_reduce at h
  rw [h]
  have hk : ∀ k : ℕ, ENNReal.ofReal (1 / Real.pi ^ 2) *
      ∫⁻ q in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), ENNReal.ofReal ((q.1 + q.2) ^ p) *
          (ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * q.1)) *
            ENNReal.ofReal (Real.exp (-(((2 * (k : ℝ) + 1) / 2)) * q.2))) =
      ENNReal.ofReal (1 / Real.pi ^ 2 * (((p + 1).factorial : ℝ) * 2 ^ (p + 2) *
        (1 / (2 * (k : ℝ) + 1) ^ (p + 2)))) := by
    intro k
    rw [P7_T p (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : (0:ℝ) < 2 * (k : ℝ) + 1 := by positivity
    rw [div_pow]
    field_simp
  simp_rw [hk]
  have hsum : Summable (fun k : ℕ => 1 / Real.pi ^ 2 * (((p + 1).factorial : ℝ) * 2 ^ (p + 2) *
        (1 / (2 * (k : ℝ) + 1) ^ (p + 2)))) :=
    ((P7_odd (s := p + 2) (by omega)).summable.mul_left
      (((p + 1).factorial : ℝ) * 2 ^ (p + 2))).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum,
    show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  rw [tsum_mul_left, tsum_mul_left]
  ring

/-- Private helper (task P-F.9.P8): lintegral of a nonnegative cubic in `τ`. -/
private lemma P8_poly {c0 c1 c2 c3 : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3) :
    ∫⁻ w, ENNReal.ofReal (c0 + c1 * (w.2.1 + w.2.2) + c2 * (w.2.1 + w.2.2) ^ 2 +
        c3 * (w.2.1 + w.2.2) ^ 3) ∂isoNuStar =
      ENNReal.ofReal (c0 + c1 * ∫ w, (w.2.1 + w.2.2) ^ 1 ∂isoNuStar +
        c2 * ∫ w, (w.2.1 + w.2.2) ^ 2 ∂isoNuStar + c3 * ∫ w, (w.2.1 + w.2.2) ^ 3 ∂isoNuStar) := by
  have := P6_mass
  have hM : ∀ p : ℕ, 0 ≤ ∫ w, (w.2.1 + w.2.2) ^ p ∂isoNuStar := fun p => by
    refine integral_nonneg_of_ae ?_
    filter_upwards [P7_ae] with w hw
    exact pow_nonneg (add_pos hw.1 hw.2).le _
  have hae : ∀ᵐ w ∂isoNuStar, ENNReal.ofReal (c0 + c1 * (w.2.1 + w.2.2) +
      c2 * (w.2.1 + w.2.2) ^ 2 + c3 * (w.2.1 + w.2.2) ^ 3) =
      ENNReal.ofReal c0 + ENNReal.ofReal c1 * ENNReal.ofReal ((w.2.1 + w.2.2) ^ 1) +
      ENNReal.ofReal c2 * ENNReal.ofReal ((w.2.1 + w.2.2) ^ 2) +
      ENNReal.ofReal c3 * ENNReal.ofReal ((w.2.1 + w.2.2) ^ 3) := by
    filter_upwards [P7_ae] with w hw
    have hτ : 0 ≤ w.2.1 + w.2.2 := (add_pos hw.1 hw.2).le
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul h1, ENNReal.ofReal_mul h2, ENNReal.ofReal_mul h3, pow_one]
  rw [lintegral_congr_ae hae]
  have m1 : Measurable fun w : Bool × ℝ × ℝ => ENNReal.ofReal c1 *
      ENNReal.ofReal ((w.2.1 + w.2.2) ^ 1) := by fun_prop
  have m2 : Measurable fun w : Bool × ℝ × ℝ => ENNReal.ofReal c2 *
      ENNReal.ofReal ((w.2.1 + w.2.2) ^ 2) := by fun_prop
  have m3 : Measurable fun w : Bool × ℝ × ℝ => ENNReal.ofReal c3 *
      ENNReal.ofReal ((w.2.1 + w.2.2) ^ 3) := by fun_prop
  rw [lintegral_add_right _ m3, lintegral_add_right _ m2, lintegral_add_right _ m1,
    lintegral_const, measure_univ, mul_one,
    lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop),
    lintegral_const_mul _ (by fun_prop), P8_lint_pow 1, P8_lint_pow 2, P8_lint_pow 3,
    ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_mul h3,
    ← ENNReal.ofReal_add h0 (mul_nonneg h1 (hM 1)),
    ← ENNReal.ofReal_add (add_nonneg h0 (mul_nonneg h1 (hM 1))) (mul_nonneg h2 (hM 2)),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg h0 (mul_nonneg h1 (hM 1)))
      (mul_nonneg h2 (hM 2))) (mul_nonneg h3 (hM 3))]

/-- Private helper (task P-F.9.P8): the `η`-integral/`ν⋆`-average bound, abstract in `k` and `I`. -/
private lemma P8_core {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {k : ℕ} (hk : 1 ≤ k) (I : ℝ → ℝ)
    (hIm : Measurable I) (hI0 : ∀ τ, 0 ≤ τ → 0 ≤ I τ)
    (hI : ∀ τ, 0 ≤ τ → ∫⁻ v in Ioi (0:ℝ), ENNReal.ofReal ((τ + v) ^ k * Real.exp (-v)) =
      ENNReal.ofReal (I τ)) :
    ∫⁻ η in Ioi (0:ℝ), ∫⁻ w,
        ENNReal.ofReal ((max 0 (-isoN β (isoPairMap (isoQlevel β η) w).2)) ^ k) ∂isoNuStar ≤
      ∫⁻ w, ENNReal.ofReal ((1 / (2 * Real.log (1 / β))) ^ k *
        ((1 / (1 - β ^ 2)) * I (w.2.1 + w.2.2) +
          isoEbar β * ((w.2.1 + w.2.2) ^ (k + 1) / ((k : ℝ) + 1)))) ∂isoNuStar := by
  have := P6_mass
  have hb2 : 0 < 1 - β ^ 2 := by nlinarith
  have hE : 0 < 1 / (1 - β ^ 2) := by positivity
  set E : ℝ := 1 / (1 - β ^ 2) with hEdef
  have hD : 0 < 2 * Real.log (1 / β) := by
    have : 0 < Real.log (1 / β) := Real.log_pos (one_lt_one_div hβ0 hβ1)
    linarith
  set c : ℝ := (1 / (2 * Real.log (1 / β))) ^ k with hcdef
  have hc : 0 ≤ c := by positivity
  have heb : 0 < isoEbar β := lt_of_lt_of_le one_pos (le_max_left _ _)
  set eb := isoEbar β with hebdef
  have hpow : ∀ T : ℝ, (T / (2 * Real.log (1 / β))) ^ k = c * T ^ k := fun T => by
    rw [hcdef, ← mul_pow]; congr 1; ring
  rw [← Set.Ioc_union_Ioi_eq_Ioi hE.le, lintegral_union measurableSet_Ioi
    (Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'))]
  -- low range
  have hlow : ∫⁻ η in Ioc 0 E, ∫⁻ w,
        ENNReal.ofReal ((max 0 (-isoN β (isoPairMap (isoQlevel β η) w).2)) ^ k) ∂isoNuStar ≤
      ∫⁻ w, ENNReal.ofReal (c * (E * I (w.2.1 + w.2.2))) ∂isoNuStar := by
    calc ∫⁻ η in Ioc 0 E, ∫⁻ w,
          ENNReal.ofReal ((max 0 (-isoN β (isoPairMap (isoQlevel β η) w).2)) ^ k) ∂isoNuStar
        ≤ ∫⁻ η in Ioc 0 E, ∫⁻ w, ENNReal.ofReal
            (c * ((w.2.1 + w.2.2) + Real.log (E / η)) ^ k) ∂isoNuStar := by
          refine setLIntegral_mono' measurableSet_Ioc (fun η hη => ?_)
          refine lintegral_mono_ae ?_
          filter_upwards [P7_ae] with w hw
          apply ENNReal.ofReal_le_ofReal
          have := P8_ptw_low hβ0 hβ1 hη.1 hη.2 w.1 hw.1.le hw.2.le
          rw [← hpow]
          exact pow_le_pow_left₀ (le_max_left _ _) this k
      _ = ∫⁻ w, (∫⁻ η in Ioc 0 E, ENNReal.ofReal
            (c * ((w.2.1 + w.2.2) + Real.log (E / η)) ^ k)) ∂isoNuStar := by
          refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
          fun_prop
      _ = ∫⁻ w, ENNReal.ofReal (c * (E * I (w.2.1 + w.2.2))) ∂isoNuStar := by
          refine lintegral_congr_ae ?_
          filter_upwards [P7_ae] with w hw
          have hτ : 0 ≤ w.2.1 + w.2.2 := (add_pos hw.1 hw.2).le
          simp_rw [ENNReal.ofReal_mul hc]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, P8_ioc_log hE _, hI _ hτ,
            ← ENNReal.ofReal_mul hE.le, ← ENNReal.ofReal_mul hc]
  -- high range
  have hhigh : ∫⁻ η in Ioi E, ∫⁻ w,
        ENNReal.ofReal ((max 0 (-isoN β (isoPairMap (isoQlevel β η) w).2)) ^ k) ∂isoNuStar ≤
      ∫⁻ w, ENNReal.ofReal (c * (eb * ((w.2.1 + w.2.2) ^ (k + 1) / ((k : ℝ) + 1))))
        ∂isoNuStar := by
    calc ∫⁻ η in Ioi E, ∫⁻ w,
          ENNReal.ofReal ((max 0 (-isoN β (isoPairMap (isoQlevel β η) w).2)) ^ k) ∂isoNuStar
        ≤ ∫⁻ η in Ioi E, ∫⁻ w, ENNReal.ofReal
            (c * (max 0 ((w.2.1 + w.2.2) - (η - E) / eb)) ^ k) ∂isoNuStar := by
          refine setLIntegral_mono' measurableSet_Ioi (fun η hη => ?_)
          refine lintegral_mono_ae ?_
          filter_upwards [P7_ae] with w hw
          apply ENNReal.ofReal_le_ofReal
          have := P8_ptw_high hβ0 hβ1 (mem_Ioi.1 hη) w.1 hw.1.le hw.2.le
          rw [← hpow]
          exact pow_le_pow_left₀ (le_max_left _ _) this k
      _ = ∫⁻ w, (∫⁻ η in Ioi E, ENNReal.ofReal
            (c * (max 0 ((w.2.1 + w.2.2) - (η - E) / eb)) ^ k)) ∂isoNuStar := by
          refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
          fun_prop
      _ = ∫⁻ w, ENNReal.ofReal (c * (eb * ((w.2.1 + w.2.2) ^ (k + 1) / ((k : ℝ) + 1))))
            ∂isoNuStar := by
          refine lintegral_congr_ae ?_
          filter_upwards [P7_ae] with w hw
          have hτ : 0 ≤ w.2.1 + w.2.2 := (add_pos hw.1 hw.2).le
          simp_rw [ENNReal.ofReal_mul hc]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, P8_ioi_lin hτ heb hk,
            ← ENNReal.ofReal_mul hc]
  refine (add_le_add hlow hhigh).trans (le_of_eq ?_)
  rw [← lintegral_add_left (by have := hIm; fun_prop)]
  refine lintegral_congr_ae ?_
  filter_upwards [P7_ae] with w hw
  have hτ : 0 ≤ w.2.1 + w.2.2 := (add_pos hw.1 hw.2).le
  rw [← ENNReal.ofReal_add (mul_nonneg hc (mul_nonneg hE.le (hI0 _ hτ)))
    (mul_nonneg hc (mul_nonneg heb.le (by positivity)))]
  congr 1; ring

/-- Private helper (task P-F.9.P8): Gamma integral `∫_0^∞ v^j e^{-v} = j!`. -/
private lemma P8_gam (j : ℕ) :
    ∫⁻ v in Ioi (0:ℝ), ENNReal.ofReal (v ^ j * Real.exp (-v)) = ENNReal.ofReal (j.factorial : ℝ) := by
  have := P7_mono j one_pos
  simp only [one_mul, pow_one, div_one, one_pow] at this
  simpa using this

/-- Private helper (task P-F.9.P8). -/
private lemma P8_I1 {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫⁻ v in Ioi (0:ℝ), ENNReal.ofReal ((τ + v) ^ 1 * Real.exp (-v)) = ENNReal.ofReal (τ + 1) := by
  have h : ∀ v ∈ Ioi (0:ℝ), ENNReal.ofReal ((τ + v) ^ 1 * Real.exp (-v)) =
      ENNReal.ofReal τ * ENNReal.ofReal (v ^ 0 * Real.exp (-v)) +
        ENNReal.ofReal (v ^ 1 * Real.exp (-v)) := by
    intro v hv
    have hv0 : (0:ℝ) < v := hv
    rw [← ENNReal.ofReal_mul hτ, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  rw [setLIntegral_congr_fun measurableSet_Ioi h,
    lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop), P8_gam 0, P8_gam 1,
    ← ENNReal.ofReal_mul hτ, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

/-- Private helper (task P-F.9.P8). -/
private lemma P8_I2 {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫⁻ v in Ioi (0:ℝ), ENNReal.ofReal ((τ + v) ^ 2 * Real.exp (-v)) =
      ENNReal.ofReal (τ ^ 2 + 2 * τ + 2) := by
  have h : ∀ v ∈ Ioi (0:ℝ), ENNReal.ofReal ((τ + v) ^ 2 * Real.exp (-v)) =
      ENNReal.ofReal (τ ^ 2) * ENNReal.ofReal (v ^ 0 * Real.exp (-v)) +
        ENNReal.ofReal (2 * τ) * ENNReal.ofReal (v ^ 1 * Real.exp (-v)) +
        ENNReal.ofReal (v ^ 2 * Real.exp (-v)) := by
    intro v hv
    have hv0 : (0:ℝ) < v := hv
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  rw [setLIntegral_congr_fun measurableSet_Ioi h,
    lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop),
    lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop),
    P8_gam 0, P8_gam 1, P8_gam 2,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num [Nat.factorial]

/-- Private helper (task P-F.9.P8): the `k = 1` bound. -/
private lemma P8_one {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
      ENNReal.ofReal (max 0 (-isoN β (isoPairMap (isoQlevel β η) w).2)) ∂isoNuStar)
      ≤ ENNReal.ofReal (isoLbar1 β) := by
  have hb2 : 0 < 1 - β ^ 2 := by nlinarith
  have hD : 0 < 2 * Real.log (1 / β) := by
    have : 0 < Real.log (1 / β) := Real.log_pos (one_lt_one_div hβ0 hβ1)
    linarith
  have heb : 0 < isoEbar β := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hcore := P8_core hβ0 hβ1 (k := 1) le_rfl (fun τ => τ + 1) (by fun_prop)
    (fun τ hτ => by positivity) (fun τ hτ => P8_I1 hτ)
  simp only [pow_one] at hcore
  refine hcore.trans (le_of_eq ?_)
  set c : ℝ := 1 / (2 * Real.log (1 / β)) with hc
  set E : ℝ := 1 / (1 - β ^ 2) with hE
  have hc0 : 0 ≤ c := by positivity
  have hE0 : 0 ≤ E := by positivity
  have hpt : ∀ w : Bool × ℝ × ℝ, c * (E * (w.2.1 + w.2.2 + 1) +
      isoEbar β * ((w.2.1 + w.2.2) ^ (1 + 1) / (((1:ℕ) : ℝ) + 1))) =
      (c * E) + (c * E) * (w.2.1 + w.2.2) + (c * (isoEbar β / 2)) * (w.2.1 + w.2.2) ^ 2 +
        0 * (w.2.1 + w.2.2) ^ 3 := by
    intro w; push_cast; ring
  simp_rw [hpt]
  rw [P8_poly (by positivity) (by positivity) (by positivity) le_rfl]
  have e1 : ∫ w, (w.2.1 + w.2.2) ^ 1 ∂isoNuStar = isoM1 := by
    simp only [pow_one]; exact P7_main.1
  have e2 : ∫ w, (w.2.1 + w.2.2) ^ 2 ∂isoNuStar = isoM2 := P7_main.2.1
  rw [e1, e2]
  congr 1
  unfold isoLbar1
  have : (isoM1 + 1) / (1 - β ^ 2) = (isoM1 + 1) * E := by rw [hE]; ring
  rw [this]
  ring

/-- Private helper (task P-F.9.P8): the `k = 2` bound. -/
private lemma P8_two {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal ((max 0 (-isoN β (isoPairMap (isoQlevel β η) w).2)) ^ 2) ∂isoNuStar)
      ≤ ENNReal.ofReal (isoLbar2 β) := by
  have hb2 : 0 < 1 - β ^ 2 := by nlinarith
  have hD : 0 < 2 * Real.log (1 / β) := by
    have : 0 < Real.log (1 / β) := Real.log_pos (one_lt_one_div hβ0 hβ1)
    linarith
  have heb : 0 < isoEbar β := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hcore := P8_core hβ0 hβ1 (k := 2) (by norm_num) (fun τ => τ ^ 2 + 2 * τ + 2) (by fun_prop)
    (fun τ hτ => by positivity) (fun τ hτ => P8_I2 hτ)
  refine hcore.trans (le_of_eq ?_)
  set c : ℝ := (1 / (2 * Real.log (1 / β))) ^ 2 with hc
  set E : ℝ := 1 / (1 - β ^ 2) with hE
  have hc0 : 0 ≤ c := by positivity
  have hE0 : 0 ≤ E := by positivity
  have hpt : ∀ w : Bool × ℝ × ℝ, c * (E * ((w.2.1 + w.2.2) ^ 2 + 2 * (w.2.1 + w.2.2) + 2) +
      isoEbar β * ((w.2.1 + w.2.2) ^ (2 + 1) / (((2:ℕ) : ℝ) + 1))) =
      (c * E * 2) + (c * E * 2) * (w.2.1 + w.2.2) + (c * E) * (w.2.1 + w.2.2) ^ 2 +
        (c * (isoEbar β / 3)) * (w.2.1 + w.2.2) ^ 3 := by
    intro w; push_cast; ring
  simp_rw [hpt]
  rw [P8_poly (by positivity) (by positivity) (by positivity) (by positivity)]
  have e1 : ∫ w, (w.2.1 + w.2.2) ^ 1 ∂isoNuStar = isoM1 := by
    simp only [pow_one]; exact P7_main.1
  have e2 : ∫ w, (w.2.1 + w.2.2) ^ 2 ∂isoNuStar = isoM2 := P7_main.2.1
  have e3 : ∫ w, (w.2.1 + w.2.2) ^ 3 ∂isoNuStar = isoM3 := P7_main.2.2.1
  rw [e1, e2, e3]
  congr 1
  unfold isoLbar2
  have : (isoM2 + 2 * isoM1 + 2) / (1 - β ^ 2) = (isoM2 + 2 * isoM1 + 2) * E := by
    rw [hE]; ring
  rw [this]
  have hc' : c = 1 / (4 * Real.log (1 / β) ^ 2) := by rw [hc]; ring
  rw [hc']
  ring
/-- `lem:app-iso-low-levels`(ii), snapshot `cr-2026-10-23`. Part (ii): the bounds `L_1 ≤ L̄_1` and `L_2 ≤ L̄_2` (lower integrals in `η` and `ν⋆`).
LaTeX (`sections/05b-isotropic/section.tex`, the whole label environment):
```latex
\begin{lemma}[Low levels]\label{lem:app-iso-low-levels}
For $\eta>0$ let $(y,z)=\Pi(Q_\eta;a,c)$ as in \cref{lem:app-iso-averaging}, and put
$\sigma\defeq\log\big((1-\bmom)^2Q_\eta\big)$. Then
\[
\mathsf n^-_\bmom(z)\le\frac{(\tau-\sigma)_+}{2\log(1/\bmom)},
\]
and $\mathsf L_k\defeq\int_0^\infty\EE_\star\big[\mathsf n^-_\bmom(z)^k\big]\,\dif\eta$ satisfies
$\mathsf L_k\le\bar{\mathsf L}_k$ for $k=1,2$, where
\[
\bar{\mathsf L}_1\defeq\frac1{2\log(1/\bmom)}\Big(\frac{\mathsf M_1+1}{1-\bmom^2}+\frac{\bar{\mathsf e}_\bmom\mathsf M_2}2\Big),\qquad
\bar{\mathsf L}_2\defeq\frac1{4\log^2(1/\bmom)}\Big(\frac{\mathsf M_2+2\mathsf M_1+2}{1-\bmom^2}+\frac{\bar{\mathsf e}_\bmom\mathsf M_3}3\Big).
\]
\end{lemma}
```
-/
theorem lem_app_iso_low_levels_ii {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, ENNReal.ofReal (max 0 (-isoN β (isoPairMap (isoQlevel β η) w).2)) ∂isoNuStar)
      ≤ ENNReal.ofReal (isoLbar1 β) ∧
    (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal ((max 0 (-isoN β (isoPairMap (isoQlevel β η) w).2)) ^ 2) ∂isoNuStar)
      ≤ ENNReal.ofReal (isoLbar2 β) := by
  refine ⟨?_, ?_⟩
  · exact P8_one hβ0 hβ1
  · exact P8_two hβ0 hβ1

end Muon.Isotropic

end

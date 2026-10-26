import Muon.Oversampled.Profile
import Muon.Oversampled.Representation
import Muon.DetEquiv.Scalar

/-!
# Appendix G2: the half-anisotropic branch and the oversampled limit law (generic form)

Snapshot `cr-2026-10-23`. Source: `sections/12-oversampled/section.tex`. Work package L-G2.6.
Scope: `lem:app-os-scalar` (i)–(iv), `lem:app-os-reduction` (a)–(d), and the generic versions
(i)–(iii) of `thm:app-os-limit` for an arbitrary `HalfAnisoBranch`. The record version of
`thm:app-os-limit` (the branch instantiated at the deterministic solution of `thm:app-de-branch`)
is L-G2.7.

Representation choices:
* The branch is the hypothesis structure `HalfAnisoBranch β γin nuOut`: five functions of `s > 0`
  (the value at `-s`), the equations of `eqn:app-os-branch` with `ν_out = nuOut`, nonnegativity,
  and continuity on `Ioi 0`. The EMA weights are `Muon.emaW β`; `J`, `Fw`, `Lw` are the
  `Muon.DetEquiv` objects of `Muon.DetEquiv.Scalar`.
* `γ_in = N_in / B` and `γ_out = N_out / B` are `gammaIn`, `gammaOut`; `r = N_out / N_in`;
  `ν̂_out = ν_out / γ_out` is `hatNu`; `s_2 = ∑_j w_j^2` is `Muon.sPow β 2` (equal to
  `(1-β)/(1+β)` by `Muon.sPow_two`); `B_eff = B / s_2`.
* `q⋆` of `lem:app-os-scalar`(iii) is an explicit argument `qs` with its defining equation. By
  (iii) that equation has exactly one solution, so the statements are equivalent to the source's
  "let $q_\star$ be as in (iii)". The scalar lemmas (iii), (iv) keep `γ_in` as a real parameter,
  as the source does.
* The standing facts of the spectral measure `ν_out` of `Σ_out` (support in `[0,∞)`, total mass
  `γ_out`) are hypotheses of the statements that use `ν̂_out` as a probability measure.
* `ε_os < 1` is a hypothesis only of the clauses that use it: clause (iii) of the theorem and
  clause (iv) of the scalar lemma. Clauses (i), (ii) of the theorem are not strengthened.
-/

open MeasureTheory Set Filter Topology

namespace Muon.Oversampled

noncomputable section

/-! ## Standing objects -/

/-- `γ_in = N_in / B` (`section.tex` l.90–93). -/
def gammaIn (Nin B : ℕ) : ℝ := (Nin : ℝ) / B

/-- `γ_out = N_out / B` (`section.tex` l.90–93). -/
def gammaOut (Nout B : ℕ) : ℝ := (Nout : ℝ) / B

/-- `ν̂_out = ν_out / γ_out`, the empirical spectral probability measure (`eqn:app-os-eps`). -/
def hatNu (nuOut : Measure ℝ) (γout : ℝ) : Measure ℝ := (ENNReal.ofReal γout)⁻¹ • nuOut

/-- `ε_os = 3(1-β²)γ_in` (`eqn:app-os-eps`). -/
def epsOs (β γin : ℝ) : ℝ := 3 * (1 - β ^ 2) * γin

/-- `Λ = 1 + 3(1-β)²q⋆` (`thm:app-os-limit`). -/
def lamOs (β qs : ℝ) : ℝ := 1 + 3 * (1 - β) ^ 2 * qs

/-- The half-anisotropic branch `(σ, σ̃, s̃₁, s₁, q)(-s)` of `eqn:app-os-branch`, as a hypothesis
structure. The field `sigma s` is `σ(-s)`, and similarly for the other four fields; `nuOut` is
`ν_out`, `γin` is `γ_in`, and the EMA weights are `Muon.emaW β`. The fields are the equations of
`eqn:app-os-branch` (for every `s > 0`), nonnegativity of the solution (`thm:app-de-branch`(i)),
and continuity in `s` on `(0,∞)` (`thm:app-de-branch`(ii)). -/
structure HalfAnisoBranch (β γin : ℝ) (nuOut : Measure ℝ) where
  /-- `σ(-s)`. -/
  sigma : ℝ → ℝ
  /-- `σ̃(-s)`. -/
  sigmaT : ℝ → ℝ
  /-- `s̃₁(-s)`. -/
  s1T : ℝ → ℝ
  /-- `s₁(-s)`. -/
  s1 : ℝ → ℝ
  /-- `q(-s)`. -/
  q : ℝ → ℝ
  eq_sigma : ∀ s : ℝ, 0 < s → sigma s = ∫ x, x / (s + s1T s * x) ∂nuOut
  eq_sigmaT : ∀ s : ℝ, 0 < s → sigmaT s = γin / (s + s1 s)
  eq_q : ∀ s : ℝ, 0 < s → q s = s * sigma s * sigmaT s
  eq_s1T : ∀ s : ℝ, 0 < s → s1T s = s * sigmaT s * Muon.DetEquiv.Fw (Muon.emaW β) (q s)
  eq_s1 : ∀ s : ℝ, 0 < s → s1 s = s * sigma s * Muon.DetEquiv.Fw (Muon.emaW β) (q s)
  nonneg : ∀ s : ℝ, 0 < s → 0 ≤ sigma s ∧ 0 ≤ sigmaT s ∧ 0 ≤ s1T s ∧ 0 ≤ s1 s ∧ 0 ≤ q s
  continuousOn_sigma : ContinuousOn sigma (Ioi 0)
  continuousOn_sigmaT : ContinuousOn sigmaT (Ioi 0)
  continuousOn_s1T : ContinuousOn s1T (Ioi 0)
  continuousOn_s1 : ContinuousOn s1 (Ioi 0)
  continuousOn_q : ContinuousOn q (Ioi 0)

/-- The integrand `k(s;μ)` of `eqn:app-os-k`, `s > 0`, `μ ≥ 0`. -/
def kOs {β γin : ℝ} {nuOut : Measure ℝ} (br : HalfAnisoBranch β γin nuOut) (s μ : ℝ) : ℝ :=
  s * Muon.DetEquiv.Lw (Muon.emaW β) (br.q s) * μ / ((s + br.s1T s * μ) * (s + br.s1 s))

/-- The coefficient `𝔡_ρ(μ) = (√2/π) ∫_0^∞ k(ρ+u²;μ) du` of `eqn:app-os-d`, for `ρ > 0`. -/
def dRidge {β γin : ℝ} {nuOut : Measure ℝ} (br : HalfAnisoBranch β γin nuOut) (ρ μ : ℝ) : ℝ :=
  Real.sqrt 2 / Real.pi * ∫ u in Ioi (0 : ℝ), kOs br (ρ + u ^ 2) μ

/-- The zero-ridge coefficient `𝔡_0(μ) = (√2/π) ∫_0^∞ k(u²;μ) du` (`thm:app-os-limit`(ii)). -/
def dZero {β γin : ℝ} {nuOut : Measure ℝ} (br : HalfAnisoBranch β γin nuOut) (μ : ℝ) : ℝ :=
  Real.sqrt 2 / Real.pi * ∫ u in Ioi (0 : ℝ), kOs br (u ^ 2) μ

/-- The rescaled ridge variable `ŝ = s/(s_2 γ_in)` (`eqn:app-os-reduction`, rescaling of the
reduction lemma). -/
def sHat (β γin s : ℝ) : ℝ := s / (Muon.sPow β 2 * γin)

/-- The rescaled branch variable `b = s̃₁(-s)/(s_2 γ_in)` (`lem:app-os-reduction`(c)). -/
def bHat {β γin : ℝ} {nuOut : Measure ℝ} (br : HalfAnisoBranch β γin nuOut) (s : ℝ) : ℝ :=
  br.s1T s / (Muon.sPow β 2 * γin)

/-! ## Scalar bounds (`lem:app-os-scalar`) -/

/-! ### Private helpers for `lem:app-os-scalar` (i), (ii) -/

private lemma os_gauss_integrand_integrable {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun g : ℝ => g ^ 2 / (1 + x * g ^ 2)) (ProbabilityTheory.gaussianReal 0 1) := by
  refine Integrable.mono' (Muon.Foundations.gaussian_integrable_pow 2)
    (by fun_prop : Measurable fun g : ℝ => g ^ 2 / (1 + x * g ^ 2)).aestronglyMeasurable
    (ae_of_all _ fun g => ?_)
  have hm := mul_nonneg hx (sq_nonneg g)
  have hd : 0 < 1 + x * g ^ 2 := by linarith
  show ‖g ^ 2 / (1 + x * g ^ 2)‖ ≤ g ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg g) hd.le)]
  exact div_le_self (sq_nonneg g) (by linarith)

private lemma os_J_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Muon.DetEquiv.J x := by
  unfold Muon.DetEquiv.J
  apply integral_nonneg
  intro g
  have hm := mul_nonneg hx (sq_nonneg g)
  have hd : 0 < 1 + x * g ^ 2 := by linarith
  exact div_nonneg (sq_nonneg g) hd.le

private lemma os_J_le_one {x : ℝ} (hx : 0 ≤ x) : Muon.DetEquiv.J x ≤ 1 := by
  unfold Muon.DetEquiv.J
  have hpt : ∀ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ≤ g ^ 2 := fun g => by
    have hm := mul_nonneg hx (sq_nonneg g)
    exact div_le_self (sq_nonneg g) (by linarith)
  calc (∫ g, g ^ 2 / (1 + x * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1))
      ≤ ∫ g, g ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) :=
        integral_mono (os_gauss_integrand_integrable hx)
          (Muon.Foundations.gaussian_integrable_pow 2) hpt
    _ = 1 := Muon.Foundations.gaussian_moment_two

private lemma os_J_lower {x : ℝ} (hx : 0 ≤ x) : 1 / (1 + 3 * x) ≤ Muon.DetEquiv.J x := by
  unfold Muon.DetEquiv.J
  have hl : 0 < 1 + 3 * x := by linarith
  have hl2 : 0 < (1 + 3 * x) ^ 2 := by positivity
  have hA : Integrable (fun g : ℝ => ((2 * (1 + 3 * x) - 1) / (1 + 3 * x) ^ 2) * g ^ 2) (ProbabilityTheory.gaussianReal 0 1) :=
    (Muon.Foundations.gaussian_integrable_pow 2).const_mul _
  have hB : Integrable (fun g : ℝ => (x / (1 + 3 * x) ^ 2) * g ^ 4) (ProbabilityTheory.gaussianReal 0 1) :=
    (Muon.Foundations.gaussian_integrable_pow 4).const_mul _
  have hpt : ∀ g : ℝ, ((2 * (1 + 3 * x) - 1) / (1 + 3 * x) ^ 2) * g ^ 2
      - (x / (1 + 3 * x) ^ 2) * g ^ 4 ≤ g ^ 2 / (1 + x * g ^ 2) := by
    intro g
    have hm := mul_nonneg hx (sq_nonneg g)
    have hd : 0 < 1 + x * g ^ 2 := by linarith
    have core : (2 * (1 + 3 * x) * g ^ 2 - g ^ 2 * (1 + x * g ^ 2)) * (1 + x * g ^ 2)
        ≤ g ^ 2 * (1 + 3 * x) ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg g)) (sq_nonneg (g ^ 2 - 3))]
    have e : ((2 * (1 + 3 * x) - 1) / (1 + 3 * x) ^ 2) * g ^ 2
        - (x / (1 + 3 * x) ^ 2) * g ^ 4
        = (2 * (1 + 3 * x) * g ^ 2 - g ^ 2 * (1 + x * g ^ 2)) / (1 + 3 * x) ^ 2 := by
      ring
    rw [e, div_le_div_iff₀ hl2 hd]
    exact core
  calc 1 / (1 + 3 * x)
      = ∫ g, ((2 * (1 + 3 * x) - 1) / (1 + 3 * x) ^ 2) * g ^ 2
          - (x / (1 + 3 * x) ^ 2) * g ^ 4 ∂(ProbabilityTheory.gaussianReal 0 1) := by
        rw [integral_sub hA hB, integral_const_mul, integral_const_mul,
          Muon.Foundations.gaussian_moment_two, Muon.Foundations.gaussian_moment_four]
        field_simp
        ring
    _ ≤ ∫ g, g ^ 2 / (1 + x * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1) :=
        integral_mono (hA.sub hB) (os_gauss_integrand_integrable hx) hpt

private lemma os_emaW_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (j : ℕ) : 0 ≤ Muon.emaW β j := by
  unfold Muon.emaW
  exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)

private lemma os_emaW_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (j : ℕ) :
    Muon.emaW β j ≤ 1 - β := by
  unfold Muon.emaW
  exact mul_le_of_le_one_right (by linarith) (pow_le_one₀ hβ0 hβ1.le)

private lemma os_emaW_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Summable (fun j : ℕ => Muon.emaW β j) := by
  have h : (fun j : ℕ => Muon.emaW β j) = fun j => (1 - β) * β ^ j := rfl
  rw [h]
  exact (summable_geometric_of_lt_one hβ0 hβ1).mul_left _

private lemma os_emaW_sq_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Summable (fun j : ℕ => Muon.emaW β j ^ 2) := by
  have h : (fun j : ℕ => Muon.emaW β j ^ 2) = fun j => (1 - β) ^ 2 * (β ^ 2) ^ j := by
    funext j
    unfold Muon.emaW
    ring
  rw [h]
  exact (summable_geometric_of_lt_one (sq_nonneg β) (by nlinarith)).mul_left _

private lemma os_F_term {β w q : ℝ} (hw0 : 0 ≤ w) (hwβ : w ≤ 1 - β) (hq : 0 ≤ q) :
    w ^ 2 / (1 + 3 * (1 - β) ^ 2 * q) ≤ w ^ 2 * Muon.DetEquiv.J (w ^ 2 * q) ∧
      w ^ 2 * Muon.DetEquiv.J (w ^ 2 * q) ≤ w ^ 2 := by
  have hwq : 0 ≤ w ^ 2 * q := mul_nonneg (sq_nonneg w) hq
  have hJ1 : Muon.DetEquiv.J (w ^ 2 * q) ≤ 1 := os_J_le_one hwq
  have hJl := os_J_lower hwq
  refine ⟨?_, mul_le_of_le_one_right (sq_nonneg w) hJ1⟩
  have hsq : w ^ 2 ≤ (1 - β) ^ 2 := pow_le_pow_left₀ hw0 hwβ 2
  have hA : 0 < 1 + 3 * (w ^ 2 * q) := by linarith
  have hB : 1 + 3 * (w ^ 2 * q) ≤ 1 + 3 * (1 - β) ^ 2 * q := by
    have h1 : w ^ 2 * q ≤ (1 - β) ^ 2 * q := mul_le_mul_of_nonneg_right hsq hq
    nlinarith
  calc w ^ 2 / (1 + 3 * (1 - β) ^ 2 * q) ≤ w ^ 2 / (1 + 3 * (w ^ 2 * q)) :=
        div_le_div_of_nonneg_left (sq_nonneg w) hA hB
    _ = w ^ 2 * (1 / (1 + 3 * (w ^ 2 * q))) := by rw [mul_one_div]
    _ ≤ w ^ 2 * Muon.DetEquiv.J (w ^ 2 * q) := mul_le_mul_of_nonneg_left hJl (sq_nonneg w)

private lemma os_L_term {β w q : ℝ} (hw0 : 0 ≤ w) (hwβ : w ≤ 1 - β) (hq : 0 ≤ q) :
    w / (1 + 3 * (1 - β) ^ 2 * q) ≤ w * Muon.DetEquiv.J (w ^ 2 * q) ∧
      w * Muon.DetEquiv.J (w ^ 2 * q) ≤ w := by
  have hwq : 0 ≤ w ^ 2 * q := mul_nonneg (sq_nonneg w) hq
  have hJ1 : Muon.DetEquiv.J (w ^ 2 * q) ≤ 1 := os_J_le_one hwq
  have hJl := os_J_lower hwq
  refine ⟨?_, mul_le_of_le_one_right hw0 hJ1⟩
  have hsq : w ^ 2 ≤ (1 - β) ^ 2 := pow_le_pow_left₀ hw0 hwβ 2
  have hA : 0 < 1 + 3 * (w ^ 2 * q) := by linarith
  have hB : 1 + 3 * (w ^ 2 * q) ≤ 1 + 3 * (1 - β) ^ 2 * q := by
    have h1 : w ^ 2 * q ≤ (1 - β) ^ 2 * q := mul_le_mul_of_nonneg_right hsq hq
    nlinarith
  calc w / (1 + 3 * (1 - β) ^ 2 * q) ≤ w / (1 + 3 * (w ^ 2 * q)) :=
        div_le_div_of_nonneg_left hw0 hA hB
    _ = w * (1 / (1 + 3 * (w ^ 2 * q))) := by rw [mul_one_div]
    _ ≤ w * Muon.DetEquiv.J (w ^ 2 * q) := mul_le_mul_of_nonneg_left hJl hw0

/-! ### Private helpers for `lem:app-os-scalar` (iii)

`K(x) = ∫ 1/(1+x g²) dγ`; the identity `x J(x) = 1 - K(x)` turns `q F_w(q)` into a series of
terms `1 - K(w_j² q)`, each nondecreasing in `q`, continuous, and tending to `1` when `w_j > 0`. -/

private lemma os_den_pos {x : ℝ} (hx : 0 ≤ x) (g : ℝ) : 0 < 1 + x * g ^ 2 := by
  have := mul_nonneg hx (sq_nonneg g)
  linarith

private lemma os_compl_zero_pos :
    (0 : ENNReal) < ProbabilityTheory.gaussianReal 0 1 ({(0 : ℝ)}ᶜ) := by
  have h0 : ProbabilityTheory.gaussianReal 0 1 {(0 : ℝ)} = 0 :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton
  have h1 : ProbabilityTheory.gaussianReal 0 1 ({(0 : ℝ)}ᶜ) = 1 := by
    rw [measure_compl (measurableSet_singleton 0) (by simp [h0]), h0]
    simp
  rw [h1]
  exact one_pos

private lemma os_K_integrable {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun g : ℝ => 1 / (1 + x * g ^ 2)) (ProbabilityTheory.gaussianReal 0 1) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_const.div (by fun_prop : Measurable fun g : ℝ => 1 + x * g ^ 2)).aestronglyMeasurable
    (ae_of_all _ fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one (os_den_pos hx g).le)]
  exact div_le_one_of_le₀ (by nlinarith [mul_nonneg hx (sq_nonneg g)]) (os_den_pos hx g).le

private lemma os_xJ_eq {x : ℝ} (hx : 0 ≤ x) :
    x * Muon.DetEquiv.J x
      = 1 - ∫ g, 1 / (1 + x * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1) := by
  unfold Muon.DetEquiv.J
  have key : ∀ g : ℝ, x * (g ^ 2 / (1 + x * g ^ 2)) = 1 - 1 / (1 + x * g ^ 2) := by
    intro g
    have hd := (os_den_pos hx g).ne'
    field_simp
    ring
  rw [← integral_const_mul]
  simp_rw [key]
  rw [integral_sub (integrable_const (1 : ℝ)) (os_K_integrable hx)]
  simp

private lemma os_T_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 1 - ∫ g, 1 / (1 + x * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1) ∧
      1 - ∫ g, 1 / (1 + x * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1) ≤ x := by
  rw [← os_xJ_eq hx]
  exact ⟨mul_nonneg hx (os_J_nonneg hx), mul_le_of_le_one_right hx (os_J_le_one hx)⟩

private lemma os_K_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ g, 1 / (1 + b * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1)
      < ∫ g, 1 / (1 + a * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1) := by
  have hb : 0 ≤ b := ha.trans hab.le
  rw [← sub_pos, ← integral_sub (os_K_integrable ha) (os_K_integrable hb)]
  have hnn : ∀ g : ℝ, 0 ≤ 1 / (1 + a * g ^ 2) - 1 / (1 + b * g ^ 2) := by
    intro g
    have h1 : 1 + a * g ^ 2 ≤ 1 + b * g ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hab.le (sq_nonneg g)]
    have := one_div_le_one_div_of_le (os_den_pos ha g) h1
    linarith
  refine (integral_pos_iff_support_of_nonneg hnn
    ((os_K_integrable ha).sub (os_K_integrable hb))).2 ?_
  refine lt_of_lt_of_le os_compl_zero_pos (measure_mono ?_)
  intro g hg
  have hg0 : g ≠ 0 := hg
  have hg2 : 0 < g ^ 2 := by positivity
  change 1 / (1 + a * g ^ 2) - 1 / (1 + b * g ^ 2) ≠ 0
  have h1 : 1 + a * g ^ 2 < 1 + b * g ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_right hab hg2]
  have := one_div_lt_one_div_of_lt (os_den_pos ha g) h1
  exact (sub_pos.2 this).ne'

private lemma os_K_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ g, 1 / (1 + b * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1)
      ≤ ∫ g, 1 / (1 + a * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1) := by
  rcases hab.lt_or_eq with h | h
  · exact (os_K_lt ha h).le
  · subst h
    exact le_refl _

private lemma os_K_continuousWithinAt {x0 : ℝ} (hx0 : 0 ≤ x0) :
    ContinuousWithinAt (fun x => ∫ g, 1 / (1 + x * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1))
      (Ici 0) x0 := by
  refine continuousWithinAt_of_dominated (F := fun x g => 1 / (1 + x * g ^ 2))
    (bound := fun _ => (1 : ℝ)) ?_ ?_ (integrable_const (1 : ℝ)) ?_
  · exact Filter.Eventually.of_forall fun x =>
      (measurable_const.div (by fun_prop : Measurable fun g : ℝ => 1 + x * g ^ 2)).aestronglyMeasurable
  · refine Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => Filter.Eventually.of_forall fun g => ?_
    have hx' : 0 ≤ x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one (os_den_pos hx' g).le)]
    exact div_le_one_of_le₀ (by nlinarith [mul_nonneg hx' (sq_nonneg g)]) (os_den_pos hx' g).le
  · refine Filter.Eventually.of_forall fun g => ?_
    apply ContinuousAt.continuousWithinAt
    exact ContinuousAt.div continuousAt_const (by fun_prop) (os_den_pos hx0 g).ne'

private lemma os_K_contOn :
    ContinuousOn (fun x => ∫ g, 1 / (1 + x * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1))
      (Ici 0) :=
  fun _ hx => os_K_continuousWithinAt hx

private lemma os_K_tendsto :
    Tendsto (fun x => ∫ g, 1 / (1 + x * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1))
      atTop (𝓝 0) := by
  have h0 : ProbabilityTheory.gaussianReal 0 1 {(0 : ℝ)} = 0 :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton
  have hae : ∀ᵐ g ∂(ProbabilityTheory.gaussianReal 0 1), g ≠ 0 := by
    rw [ae_iff]
    simpa using h0
  have hT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (F := fun (x : ℝ) (g : ℝ) => 1 / (1 + x * g ^ 2))
    (fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun x =>
      (measurable_const.div (by fun_prop : Measurable fun g : ℝ => 1 + x * g ^ 2)).aestronglyMeasurable)
    (Filter.eventually_atTop.2 ⟨0, fun x hx => ae_of_all _ fun g => by
      have hx' : 0 ≤ x := hx
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one (os_den_pos hx' g).le)]
      exact div_le_one_of_le₀ (by nlinarith [mul_nonneg hx' (sq_nonneg g)]) (os_den_pos hx' g).le⟩)
    (integrable_const (1 : ℝ))
    (by
      filter_upwards [hae] with g hg
      have hg2 : 0 < g ^ 2 := by positivity
      have hd : Tendsto (fun x : ℝ => 1 + x * g ^ 2) atTop atTop :=
        tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const hg2)
      exact tendsto_const_nhds.div_atTop hd)
  simpa using hT

private lemma os_T_summable (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    Summable (fun j : ℕ => 1 - ∫ g, 1 / (1 + Muon.emaW β j ^ 2 * q * g ^ 2)
      ∂(ProbabilityTheory.gaussianReal 0 1)) :=
  Summable.of_nonneg_of_le
    (fun j => (os_T_bounds (mul_nonneg (sq_nonneg (Muon.emaW β j)) hq)).1)
    (fun j => (os_T_bounds (mul_nonneg (sq_nonneg (Muon.emaW β j)) hq)).2)
    ((os_emaW_sq_summable hβ0 hβ1).mul_right q)

private lemma os_rW_eq (β : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    q * Muon.DetEquiv.Fw (Muon.emaW β) q
      = ∑' j : ℕ, (1 - ∫ g, 1 / (1 + Muon.emaW β j ^ 2 * q * g ^ 2)
          ∂(ProbabilityTheory.gaussianReal 0 1)) := by
  unfold Muon.DetEquiv.Fw
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  have hx : 0 ≤ Muon.emaW β j ^ 2 * q := mul_nonneg (sq_nonneg _) hq
  rw [show q * (Muon.emaW β j ^ 2 * Muon.DetEquiv.J (Muon.emaW β j ^ 2 * q))
      = (Muon.emaW β j ^ 2 * q) * Muon.DetEquiv.J (Muon.emaW β j ^ 2 * q) by ring,
    os_xJ_eq hx]

private lemma os_sum_le (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (S : Finset ℕ) {q : ℝ}
    (hq : 0 ≤ q) :
    ∑ j ∈ S, (1 - ∫ g, 1 / (1 + Muon.emaW β j ^ 2 * q * g ^ 2)
        ∂(ProbabilityTheory.gaussianReal 0 1))
      ≤ q * Muon.DetEquiv.Fw (Muon.emaW β) q := by
  rw [os_rW_eq β hq]
  exact Summable.sum_le_tsum S
    (fun j _ => (os_T_bounds (mul_nonneg (sq_nonneg (Muon.emaW β j)) hq)).1)
    (os_T_summable β hβ0 hβ1 hq)

private lemma os_exists_large (β γin : ℝ) (S : Finset ℕ) (hw : ∀ j ∈ S, 0 < Muon.emaW β j)
    (hS : γin < (S.card : ℝ)) :
    ∃ Q : ℝ, 0 ≤ Q ∧ γin < ∑ j ∈ S, (1 - ∫ g, 1 / (1 + Muon.emaW β j ^ 2 * Q * g ^ 2)
        ∂(ProbabilityTheory.gaussianReal 0 1)) := by
  have hT : Tendsto (fun Q : ℝ => ∑ j ∈ S, (1 - ∫ g, 1 / (1 + Muon.emaW β j ^ 2 * Q * g ^ 2)
      ∂(ProbabilityTheory.gaussianReal 0 1))) atTop (𝓝 (∑ j ∈ S, (1 - 0 : ℝ))) := by
    apply tendsto_finset_sum
    intro j hj
    have hc : 0 < Muon.emaW β j ^ 2 := pow_pos (hw j hj) 2
    have hlin : Tendsto (fun Q : ℝ => Muon.emaW β j ^ 2 * Q) atTop atTop :=
      Tendsto.const_mul_atTop hc tendsto_id
    exact tendsto_const_nhds.sub (os_K_tendsto.comp hlin)
  have hcard : ∑ j ∈ S, (1 - 0 : ℝ) = (S.card : ℝ) := by simp
  rw [hcard] at hT
  obtain ⟨Q, hQ1, hQ2⟩ := ((hT.eventually (lt_mem_nhds hS)).and
    (eventually_ge_atTop (0 : ℝ))).exists
  exact ⟨Q, hQ2, hQ1⟩

private lemma os_rW_contOn (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (Q : ℝ) :
    ContinuousOn (fun q => q * Muon.DetEquiv.Fw (Muon.emaW β) q) (Icc 0 Q) := by
  have hc : ContinuousOn (fun q : ℝ => ∑' j : ℕ, (1 - ∫ g, 1 / (1 + Muon.emaW β j ^ 2 * q * g ^ 2)
      ∂(ProbabilityTheory.gaussianReal 0 1))) (Icc 0 Q) := by
    refine continuousOn_tsum (u := fun j : ℕ => Muon.emaW β j ^ 2 * Q) (fun j => ?_)
      ((os_emaW_sq_summable hβ0 hβ1).mul_right Q) (fun j q hq => ?_)
    · have hlin : ContinuousOn (fun q : ℝ => Muon.emaW β j ^ 2 * q) (Icc 0 Q) :=
        (continuous_const.mul continuous_id).continuousOn
      have hmaps : Set.MapsTo (fun q : ℝ => Muon.emaW β j ^ 2 * q) (Icc 0 Q) (Ici 0) :=
        fun q hq => Set.mem_Ici.2 (mul_nonneg (sq_nonneg _) hq.1)
      exact continuousOn_const.sub (os_K_contOn.comp hlin hmaps)
    · have h0 := os_T_bounds (mul_nonneg (sq_nonneg (Muon.emaW β j)) hq.1)
      rw [Real.norm_eq_abs, abs_of_nonneg h0.1]
      exact h0.2.trans (mul_le_mul_of_nonneg_left hq.2 (sq_nonneg _))
  exact hc.congr (fun q hq => os_rW_eq β hq.1)

private lemma os_rW_strictMonoOn (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    StrictMonoOn (fun q => q * Muon.DetEquiv.Fw (Muon.emaW β) q) (Ici 0) := by
  intro a ha b hb hab
  have ha' : 0 ≤ a := ha
  have hb' : 0 ≤ b := hb
  show a * Muon.DetEquiv.Fw (Muon.emaW β) a < b * Muon.DetEquiv.Fw (Muon.emaW β) b
  rw [os_rW_eq β ha', os_rW_eq β hb']
  have hw0 : 0 < Muon.emaW β 0 := by
    unfold Muon.emaW
    rw [pow_zero, mul_one]
    linarith
  refine Summable.tsum_lt_tsum (i := 0) (fun j => ?_) ?_
    (os_T_summable β hβ0 hβ1 ha') (os_T_summable β hβ0 hβ1 hb')
  · have hxa : 0 ≤ Muon.emaW β j ^ 2 * a := mul_nonneg (sq_nonneg _) ha'
    have hxab : Muon.emaW β j ^ 2 * a ≤ Muon.emaW β j ^ 2 * b :=
      mul_le_mul_of_nonneg_left hab.le (sq_nonneg _)
    have := os_K_le hxa hxab
    linarith
  · have hxa : 0 ≤ Muon.emaW β 0 ^ 2 * a := mul_nonneg (sq_nonneg _) ha'
    have hxab : Muon.emaW β 0 ^ 2 * a < Muon.emaW β 0 ^ 2 * b :=
      mul_lt_mul_of_pos_left hab (pow_pos hw0 2)
    have := os_K_lt hxa hxab
    linarith

/-- Label `lem:app-os-scalar`, part (i). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{lemma}[Scalar bounds]\label{lem:app-os-scalar}
\begin{enumerate}[label=(\roman*)]
\item For $x\ge0$,
\[
\frac1{1+3x}\le\Jfun(x)\le1 .
\]
\item For $q\ge0$,
\[
\frac{\sw2}{1+3(1-\bmom)^2q}\le\Fw(q)\le\sw2,\qquad
\frac{1}{1+3(1-\bmom)^2q}\le\Lw(q)\le1 .
\]
\item Assume that $\bmom>0$, or that $\bmom=0$ and $\gin<1$. Then there is a
unique $q_\star>0$ with $q_\star\Fw(q_\star)=\gin$, and $q\Fw(q)<\gin$ holds
if and only if $q<q_\star$.
\item If $\epsilon_{\rm os}<1$, then the hypothesis of (iii) holds and
\[
1+3(1-\bmom)^2q_\star\le\frac1{1-\epsilon_{\rm os}} .
\]
\end{enumerate}
\end{lemma}
-/
theorem lem_app_os_scalar_i :
    ∀ x : ℝ, 0 ≤ x → 1 / (1 + 3 * x) ≤ Muon.DetEquiv.J x ∧ Muon.DetEquiv.J x ≤ 1 := by
  intro x hx
  exact ⟨os_J_lower hx, os_J_le_one hx⟩

/-- Label `lem:app-os-scalar`, part (ii). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{lemma}[Scalar bounds]\label{lem:app-os-scalar}
\begin{enumerate}[label=(\roman*)]
\item For $x\ge0$,
\[
\frac1{1+3x}\le\Jfun(x)\le1 .
\]
\item For $q\ge0$,
\[
\frac{\sw2}{1+3(1-\bmom)^2q}\le\Fw(q)\le\sw2,\qquad
\frac{1}{1+3(1-\bmom)^2q}\le\Lw(q)\le1 .
\]
\item Assume that $\bmom>0$, or that $\bmom=0$ and $\gin<1$. Then there is a
unique $q_\star>0$ with $q_\star\Fw(q_\star)=\gin$, and $q\Fw(q)<\gin$ holds
if and only if $q<q_\star$.
\item If $\epsilon_{\rm os}<1$, then the hypothesis of (iii) holds and
\[
1+3(1-\bmom)^2q_\star\le\frac1{1-\epsilon_{\rm os}} .
\]
\end{enumerate}
\end{lemma}
-/
theorem lem_app_os_scalar_ii {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∀ q : ℝ, 0 ≤ q →
      Muon.sPow β 2 / (1 + 3 * (1 - β) ^ 2 * q) ≤ Muon.DetEquiv.Fw (Muon.emaW β) q ∧
      Muon.DetEquiv.Fw (Muon.emaW β) q ≤ Muon.sPow β 2 ∧
      1 / (1 + 3 * (1 - β) ^ 2 * q) ≤ Muon.DetEquiv.Lw (Muon.emaW β) q ∧
      Muon.DetEquiv.Lw (Muon.emaW β) q ≤ 1 := by
  intro q hq
  have hs2 : Muon.sPow β 2 = ∑' j : ℕ, Muon.emaW β j ^ 2 := rfl
  have hsq := os_emaW_sq_summable hβ0 hβ1
  have hsum := os_emaW_summable hβ0 hβ1
  have hF_summ : Summable (fun j : ℕ => Muon.emaW β j ^ 2 * Muon.DetEquiv.J (Muon.emaW β j ^ 2 * q)) :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (sq_nonneg _)
        (os_J_nonneg (mul_nonneg (sq_nonneg _) hq)))
      (fun j => (os_F_term (os_emaW_nonneg hβ0 hβ1 j) (os_emaW_le hβ0 hβ1 j) hq).2) hsq
  have hL_summ : Summable (fun j : ℕ => Muon.emaW β j * Muon.DetEquiv.J (Muon.emaW β j ^ 2 * q)) :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (os_emaW_nonneg hβ0 hβ1 j)
        (os_J_nonneg (mul_nonneg (sq_nonneg _) hq)))
      (fun j => (os_L_term (os_emaW_nonneg hβ0 hβ1 j) (os_emaW_le hβ0 hβ1 j) hq).2) hsum
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e1 : Muon.sPow β 2 / (1 + 3 * (1 - β) ^ 2 * q)
        = ∑' j : ℕ, Muon.emaW β j ^ 2 / (1 + 3 * (1 - β) ^ 2 * q) := by
      rw [hs2, tsum_div_const]
    rw [e1]
    exact Summable.tsum_le_tsum (fun j => (os_F_term (os_emaW_nonneg hβ0 hβ1 j)
      (os_emaW_le hβ0 hβ1 j) hq).1) (hsq.div_const _) hF_summ
  · rw [hs2]
    exact Summable.tsum_le_tsum (fun j => (os_F_term (os_emaW_nonneg hβ0 hβ1 j)
      (os_emaW_le hβ0 hβ1 j) hq).2) hF_summ hsq
  · have e2 : ∑' j : ℕ, Muon.emaW β j / (1 + 3 * (1 - β) ^ 2 * q)
        = 1 / (1 + 3 * (1 - β) ^ 2 * q) := by
      rw [tsum_div_const, tsum_emaW hβ0 hβ1]
    rw [← e2]
    exact Summable.tsum_le_tsum (fun j => (os_L_term (os_emaW_nonneg hβ0 hβ1 j)
      (os_emaW_le hβ0 hβ1 j) hq).1) (hsum.div_const _) hL_summ
  · have h := Summable.tsum_le_tsum (fun j => (os_L_term (os_emaW_nonneg hβ0 hβ1 j)
      (os_emaW_le hβ0 hβ1 j) hq).2) hL_summ hsum
    rw [tsum_emaW hβ0 hβ1] at h
    exact h

/-- Label `lem:app-os-scalar`, part (iii). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{lemma}[Scalar bounds]\label{lem:app-os-scalar}
\begin{enumerate}[label=(\roman*)]
\item For $x\ge0$,
\[
\frac1{1+3x}\le\Jfun(x)\le1 .
\]
\item For $q\ge0$,
\[
\frac{\sw2}{1+3(1-\bmom)^2q}\le\Fw(q)\le\sw2,\qquad
\frac{1}{1+3(1-\bmom)^2q}\le\Lw(q)\le1 .
\]
\item Assume that $\bmom>0$, or that $\bmom=0$ and $\gin<1$. Then there is a
unique $q_\star>0$ with $q_\star\Fw(q_\star)=\gin$, and $q\Fw(q)<\gin$ holds
if and only if $q<q_\star$.
\item If $\epsilon_{\rm os}<1$, then the hypothesis of (iii) holds and
\[
1+3(1-\bmom)^2q_\star\le\frac1{1-\epsilon_{\rm os}} .
\]
\end{enumerate}
\end{lemma}
-/
theorem lem_app_os_scalar_iii {β γin : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ : 0 < γin)
    (hcond : 0 < β ∨ (β = 0 ∧ γin < 1)) :
    ∃ qs : ℝ, 0 < qs ∧
      (∀ q : ℝ, 0 < q → (q * Muon.DetEquiv.Fw (Muon.emaW β) q = γin ↔ q = qs)) ∧
      ∀ q : ℝ, 0 ≤ q → (q * Muon.DetEquiv.Fw (Muon.emaW β) q < γin ↔ q < qs) := by
  have hmono := os_rW_strictMonoOn β hβ0 hβ1
  obtain ⟨Q, hQ0, hQlarge⟩ : ∃ Q : ℝ, 0 ≤ Q ∧ γin < Q * Muon.DetEquiv.Fw (Muon.emaW β) Q := by
    rcases hβ0.lt_or_eq with hβpos | hβz
    · obtain ⟨Q, hQ0, hQ⟩ := os_exists_large β γin (Finset.range (⌈γin⌉₊ + 1))
        (fun j _ => mul_pos (by linarith) (pow_pos hβpos j))
        (by
          rw [Finset.card_range]
          push_cast
          linarith [Nat.le_ceil γin])
      exact ⟨Q, hQ0, lt_of_lt_of_le hQ (os_sum_le β hβ0 hβ1 _ hQ0)⟩
    · subst hβz
      have hγ1 : γin < 1 := (hcond.resolve_left (lt_irrefl 0)).2
      obtain ⟨Q, hQ0, hQ⟩ := os_exists_large 0 γin {0}
        (fun j hj => by
          rw [Finset.mem_singleton] at hj
          subst hj
          norm_num [Muon.emaW])
        (by simpa using hγ1)
      exact ⟨Q, hQ0, lt_of_lt_of_le hQ (os_sum_le 0 hβ0 hβ1 _ hQ0)⟩
  have hlo : (fun q : ℝ => q * Muon.DetEquiv.Fw (Muon.emaW β) q) 0 ≤ γin := by
    simp only [zero_mul]
    exact hγ.le
  obtain ⟨qs, ⟨hqs0, _⟩, hqsv⟩ :=
    intermediate_value_Icc hQ0 (os_rW_contOn β hβ0 hβ1 Q) (Set.mem_Icc.2 ⟨hlo, hQlarge.le⟩)
  have hqsv' : qs * Muon.DetEquiv.Fw (Muon.emaW β) qs = γin := hqsv
  have hqspos : 0 < qs := by
    refine lt_of_le_of_ne hqs0 (fun h => ?_)
    rw [← h, zero_mul] at hqsv'
    linarith
  refine ⟨qs, hqspos, ?_, ?_⟩
  · intro q hq
    constructor
    · intro h
      exact hmono.injOn (Set.mem_Ici.2 hq.le) (Set.mem_Ici.2 hqspos.le) (h.trans hqsv'.symm)
    · intro h
      rw [h]
      exact hqsv'
  · intro q hq
    constructor
    · intro h
      by_contra hge
      have hge' : qs ≤ q := not_lt.1 hge
      have h' : qs * Muon.DetEquiv.Fw (Muon.emaW β) qs ≤ q * Muon.DetEquiv.Fw (Muon.emaW β) q :=
        hmono.monotoneOn (Set.mem_Ici.2 hqspos.le) (Set.mem_Ici.2 hq) hge'
      linarith
    · intro h
      have h' : q * Muon.DetEquiv.Fw (Muon.emaW β) q < qs * Muon.DetEquiv.Fw (Muon.emaW β) qs :=
        hmono (Set.mem_Ici.2 hq) (Set.mem_Ici.2 hqspos.le) h
      linarith

/-- Label `lem:app-os-scalar`, part (iv). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{lemma}[Scalar bounds]\label{lem:app-os-scalar}
\begin{enumerate}[label=(\roman*)]
\item For $x\ge0$,
\[
\frac1{1+3x}\le\Jfun(x)\le1 .
\]
\item For $q\ge0$,
\[
\frac{\sw2}{1+3(1-\bmom)^2q}\le\Fw(q)\le\sw2,\qquad
\frac{1}{1+3(1-\bmom)^2q}\le\Lw(q)\le1 .
\]
\item Assume that $\bmom>0$, or that $\bmom=0$ and $\gin<1$. Then there is a
unique $q_\star>0$ with $q_\star\Fw(q_\star)=\gin$, and $q\Fw(q)<\gin$ holds
if and only if $q<q_\star$.
\item If $\epsilon_{\rm os}<1$, then the hypothesis of (iii) holds and
\[
1+3(1-\bmom)^2q_\star\le\frac1{1-\epsilon_{\rm os}} .
\]
\end{enumerate}
\end{lemma}
-/
theorem lem_app_os_scalar_iv {β γin : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ : 0 < γin)
    (hε : epsOs β γin < 1) :
    (0 < β ∨ (β = 0 ∧ γin < 1)) ∧
      ∀ qs : ℝ, 0 < qs → qs * Muon.DetEquiv.Fw (Muon.emaW β) qs = γin →
        lamOs β qs ≤ 1 / (1 - epsOs β γin) := by
  have hβ : 0 < β ∨ (β = 0 ∧ γin < 1) := by
    rcases hβ0.lt_or_eq with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h.symm, ?_⟩
      have h1 : epsOs β γin = 3 * γin := by
        unfold epsOs
        rw [← h]
        ring
      linarith
  have hεpos : 0 < 1 - epsOs β γin := by linarith
  refine ⟨hβ, ?_⟩
  intro qs hqs hfix
  have hlow := (lem_app_os_scalar_ii hβ0 hβ1 qs hqs.le).1
  have hS : Muon.sPow β 2 = (1 - β) / (1 + β) := Muon.sPow_two hβ0 hβ1
  have hβ1' : 0 < 1 - β := by linarith
  have hβ2 : 0 < 1 + β := by linarith
  have hy : 0 < 1 + 3 * (1 - β) ^ 2 * qs := by
    have : 0 ≤ 3 * (1 - β) ^ 2 * qs := by positivity
    linarith
  have key1 : qs * (Muon.sPow β 2 / (1 + 3 * (1 - β) ^ 2 * qs))
      ≤ γin := by
    rw [← hfix]
    exact mul_le_mul_of_nonneg_left hlow hqs.le
  rw [hS] at key1
  have h2 : qs * (1 - β) ≤ γin * ((1 + β) * (1 + 3 * (1 - β) ^ 2 * qs)) := by
    have e : qs * ((1 - β) / (1 + β) / (1 + 3 * (1 - β) ^ 2 * qs))
        * ((1 + β) * (1 + 3 * (1 - β) ^ 2 * qs)) = qs * (1 - β) := by
      field_simp
    calc qs * (1 - β)
        = qs * ((1 - β) / (1 + β) / (1 + 3 * (1 - β) ^ 2 * qs))
          * ((1 + β) * (1 + 3 * (1 - β) ^ 2 * qs)) := e.symm
      _ ≤ γin * ((1 + β) * (1 + 3 * (1 - β) ^ 2 * qs)) :=
          mul_le_mul_of_nonneg_right key1 (by positivity)
  have h3 : 3 * (1 - β) ^ 2 * qs ≤ epsOs β γin * (1 + 3 * (1 - β) ^ 2 * qs) := by
    unfold epsOs
    have h4 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 3 * (1 - β))
    nlinarith [h4]
  unfold lamOs
  rw [le_div_iff₀ hεpos]
  nlinarith [h3]

/-! ## Exact reduction of the branch (`lem:app-os-reduction`) -/

private lemma os_gammaIn_pos {Nin B : ℕ} (hNin : 1 ≤ Nin) (hB : 1 ≤ B) :
    0 < gammaIn Nin B := by
  unfold gammaIn
  exact div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))

private lemma os_F_pos' {β q : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hq : 0 ≤ q) :
    0 < Muon.DetEquiv.Fw (Muon.emaW β) q := by
  have h := (lem_app_os_scalar_ii hβ0 hβ1 q hq).1
  have hS : 0 < Muon.sPow β 2 := by
    rw [Muon.sPow_two hβ0 hβ1]
    apply div_pos <;> linarith
  have hd : 0 < 1 + 3 * (1 - β) ^ 2 * q := by
    have : 0 ≤ 3 * (1 - β) ^ 2 * q := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hq
    linarith
  exact lt_of_lt_of_le (div_pos hS hd) h

private lemma os_reduction_alg {s σ σT s1T s1 q F γ : ℝ} (hs : 0 < s) (hσ : 0 ≤ σ)
    (hF : 0 < F) (hγ : 0 < γ) (e1 : s1 = s * σ * F) (eT : σT = γ / (s + s1))
    (eq : q = s * σ * σT) (eS : s1T = s * σT * F) :
    s + s1 = s * (1 + σ * F) ∧ s1T = γ * F / (1 + σ * F) ∧ 0 < s1T ∧
      q * F = σ * s1T ∧ σ * s1T = γ * (σ * F) / (1 + σ * F) ∧ q * F < γ ∧
      s1T = F * (γ - q * F) := by
  have hD : 0 < 1 + σ * F := by
    have := mul_nonneg hσ hF.le
    linarith
  have hsum : s + s1 = s * (1 + σ * F) := by
    rw [e1]; ring
  have hsT : σT = γ / (s * (1 + σ * F)) := by
    rw [eT, hsum]
  have hS1T : s1T = γ * F / (1 + σ * F) := by
    rw [eS, hsT]
    field_simp
  have hpos : 0 < s1T := by
    rw [hS1T]; exact div_pos (mul_pos hγ hF) hD
  have hqF : q * F = σ * s1T := by
    rw [eq, eS]; ring
  have hσs : σ * s1T = γ * (σ * F) / (1 + σ * F) := by
    rw [hS1T]; ring
  have hlt : q * F < γ := by
    rw [hqF, hσs, div_lt_iff₀ hD]
    nlinarith [mul_pos hγ hF]
  have hfin : s1T = F * (γ - q * F) := by
    rw [hqF, hσs, hS1T]
    field_simp
    ring
  exact ⟨hsum, hS1T, hpos, hqF, hσs, hlt, hfin⟩

/-- Label `lem:app-os-reduction`, part (a). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{lemma}[Exact reduction of the half-anisotropic branch]\label{lem:app-os-reduction}
Fix $s>0$, write $(\sigma,\tilde\sigma,\tilde s_1,s_1,q)$ for the branch at $-s$,
and put $F=\Fw(q)$, $L=\Lw(q)$ and $\widehat F\defeq F/\sw2\in(0,1]$.
\begin{enumerate}[label=(\alph*)]
\item One has $s+s_1=s(1+\sigma F)$ and $\tilde s_1=\gin F/(1+\sigma F)>0$.
\item One has $qF=\sigma\tilde s_1=\gin\sigma F/(1+\sigma F)<\gin$, and
$\tilde s_1=F\,(\gin-qF)$.
\item With $\hat s\defeq s/(\sw2\gin)$ and $b\defeq\tilde s_1/(\sw2\gin)$,
one has $b\in(0,\widehat F]$ and
\[
\frac{b}{\widehat F}+r\,m_{\hat\nu_{\mathrm{out}}}(\hat s/b)=1 .
\]
\item For every $\mu\ge0$,
\[
\mathsf k(s;\mu)=\frac{1}{\sw2\gin}\,\frac{L}{\widehat F}\,\frac{b\mu}{\hat s+b\mu}.
\]
\end{enumerate}
\end{lemma}
-/
theorem lem_app_os_reduction_a {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Nin B : ℕ}
    (hNin : 1 ≤ Nin) (hB : 1 ≤ B) {nuOut : Measure ℝ}
    (br : HalfAnisoBranch β (gammaIn Nin B) nuOut) {s : ℝ} (hs : 0 < s) :
    s + br.s1 s = s * (1 + br.sigma s * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s)) ∧
      br.s1T s = gammaIn Nin B * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) /
        (1 + br.sigma s * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s)) ∧
      0 < br.s1T s := by
  obtain ⟨hσ, -, -, -, hq⟩ := br.nonneg s hs
  have hF := os_F_pos' hβ0 hβ1 hq
  have hγ := os_gammaIn_pos hNin hB
  have key := os_reduction_alg hs hσ hF hγ (br.eq_s1 s hs) (br.eq_sigmaT s hs)
    (br.eq_q s hs) (br.eq_s1T s hs)
  exact ⟨key.1, key.2.1, key.2.2.1⟩

/-- Label `lem:app-os-reduction`, part (b). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{lemma}[Exact reduction of the half-anisotropic branch]\label{lem:app-os-reduction}
Fix $s>0$, write $(\sigma,\tilde\sigma,\tilde s_1,s_1,q)$ for the branch at $-s$,
and put $F=\Fw(q)$, $L=\Lw(q)$ and $\widehat F\defeq F/\sw2\in(0,1]$.
\begin{enumerate}[label=(\alph*)]
\item One has $s+s_1=s(1+\sigma F)$ and $\tilde s_1=\gin F/(1+\sigma F)>0$.
\item One has $qF=\sigma\tilde s_1=\gin\sigma F/(1+\sigma F)<\gin$, and
$\tilde s_1=F\,(\gin-qF)$.
\item With $\hat s\defeq s/(\sw2\gin)$ and $b\defeq\tilde s_1/(\sw2\gin)$,
one has $b\in(0,\widehat F]$ and
\[
\frac{b}{\widehat F}+r\,m_{\hat\nu_{\mathrm{out}}}(\hat s/b)=1 .
\]
\item For every $\mu\ge0$,
\[
\mathsf k(s;\mu)=\frac{1}{\sw2\gin}\,\frac{L}{\widehat F}\,\frac{b\mu}{\hat s+b\mu}.
\]
\end{enumerate}
\end{lemma}
-/
theorem lem_app_os_reduction_b {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Nin B : ℕ}
    (hNin : 1 ≤ Nin) (hB : 1 ≤ B) {nuOut : Measure ℝ}
    (br : HalfAnisoBranch β (gammaIn Nin B) nuOut) {s : ℝ} (hs : 0 < s) :
    br.q s * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) = br.sigma s * br.s1T s ∧
      br.sigma s * br.s1T s =
        gammaIn Nin B * (br.sigma s * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s)) /
          (1 + br.sigma s * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s)) ∧
      br.q s * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) < gammaIn Nin B ∧
      br.s1T s = Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) *
        (gammaIn Nin B - br.q s * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s)) := by
  obtain ⟨hσ, -, -, -, hq⟩ := br.nonneg s hs
  have hF := os_F_pos' hβ0 hβ1 hq
  have hγ := os_gammaIn_pos hNin hB
  have key := os_reduction_alg hs hσ hF hγ (br.eq_s1 s hs) (br.eq_sigmaT s hs)
    (br.eq_q s hs) (br.eq_s1T s hs)
  exact ⟨key.2.2.2.1, key.2.2.2.2.1, key.2.2.2.2.2.1, key.2.2.2.2.2.2⟩

/-- Label `lem:app-os-reduction`, part (c). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{lemma}[Exact reduction of the half-anisotropic branch]\label{lem:app-os-reduction}
Fix $s>0$, write $(\sigma,\tilde\sigma,\tilde s_1,s_1,q)$ for the branch at $-s$,
and put $F=\Fw(q)$, $L=\Lw(q)$ and $\widehat F\defeq F/\sw2\in(0,1]$.
\begin{enumerate}[label=(\alph*)]
\item One has $s+s_1=s(1+\sigma F)$ and $\tilde s_1=\gin F/(1+\sigma F)>0$.
\item One has $qF=\sigma\tilde s_1=\gin\sigma F/(1+\sigma F)<\gin$, and
$\tilde s_1=F\,(\gin-qF)$.
\item With $\hat s\defeq s/(\sw2\gin)$ and $b\defeq\tilde s_1/(\sw2\gin)$,
one has $b\in(0,\widehat F]$ and
\[
\frac{b}{\widehat F}+r\,m_{\hat\nu_{\mathrm{out}}}(\hat s/b)=1 .
\]
\item For every $\mu\ge0$,
\[
\mathsf k(s;\mu)=\frac{1}{\sw2\gin}\,\frac{L}{\widehat F}\,\frac{b\mu}{\hat s+b\mu}.
\]
\end{enumerate}
\end{lemma}
-/
theorem lem_app_os_reduction_c {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Nout Nin B : ℕ}
    (hNout : 1 ≤ Nout) (hNin : 1 ≤ Nin) (hB : 1 ≤ B) {nuOut : Measure ℝ}
    (hν0 : nuOut (Iio 0) = 0) (hmass : nuOut univ = ENNReal.ofReal (gammaOut Nout B))
    (br : HalfAnisoBranch β (gammaIn Nin B) nuOut) {s : ℝ} (hs : 0 < s) :
    0 < bHat br s ∧
      bHat br s ≤ Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) / Muon.sPow β 2 ∧
      bHat br s / (Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) / Muon.sPow β 2) +
        ((Nout : ℝ) / Nin) *
          mNuExt (hatNu nuOut (gammaOut Nout B)) (sHat β (gammaIn Nin B) s) (bHat br s) = 1 := by
  obtain ⟨hσ, -, -, -, hq⟩ := br.nonneg s hs
  have hF := os_F_pos' hβ0 hβ1 hq
  have hγ := os_gammaIn_pos hNin hB
  have hS : 0 < Muon.sPow β 2 := by
    rw [Muon.sPow_two hβ0 hβ1]
    apply div_pos <;> linarith
  have hc : Muon.sPow β 2 * gammaIn Nin B ≠ 0 := (mul_pos hS hγ).ne'
  obtain ⟨-, hS1T, hpos, -, -, -, -⟩ :=
    os_reduction_alg hs hσ hF hγ (br.eq_s1 s hs) (br.eq_sigmaT s hs) (br.eq_q s hs)
      (br.eq_s1T s hs)
  have hD : 0 < 1 + br.sigma s * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) := by
    have := mul_nonneg hσ hF.le
    linarith
  have hγout : 0 < gammaOut Nout B := by
    unfold gammaOut
    exact div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))
  have hpt : ∀ x : ℝ, bHat br s * x / (sHat β (gammaIn Nin B) s + bHat br s * x) =
      br.s1T s * (x / (s + br.s1T s * x)) := by
    intro x
    unfold bHat sHat
    rw [show s / (Muon.sPow β 2 * gammaIn Nin B) + br.s1T s / (Muon.sPow β 2 * gammaIn Nin B) * x
        = (s + br.s1T s * x) / (Muon.sPow β 2 * gammaIn Nin B) by ring,
      div_mul_eq_mul_div, div_div_div_cancel_right₀ hc, mul_div_assoc]
  have hm : mNuExt (hatNu nuOut (gammaOut Nout B)) (sHat β (gammaIn Nin B) s) (bHat br s)
      = br.s1T s * br.sigma s / gammaOut Nout B := by
    unfold mNuExt hatNu
    rw [integral_smul_measure]
    simp_rw [hpt]
    rw [integral_const_mul, ← br.eq_sigma s hs, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hγout.le, smul_eq_mul]
    ring
  have hNin' : (Nin : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hNout' : (Nout : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hB' : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨?_, ?_, ?_⟩
  · unfold bHat
    exact div_pos hpos (mul_pos hS hγ)
  · have hTle : br.s1T s ≤ gammaIn Nin B * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) := by
      rw [hS1T]
      exact div_le_self (mul_pos hγ hF).le (by linarith [mul_nonneg hσ hF.le])
    unfold bHat
    rw [div_le_div_iff₀ (mul_pos hS hγ) hS]
    nlinarith [mul_le_mul_of_nonneg_left hTle hS.le]
  · rw [hm]
    unfold bHat
    rw [hS1T]
    unfold gammaOut gammaIn
    field_simp

/-- Label `lem:app-os-reduction`, part (d). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{lemma}[Exact reduction of the half-anisotropic branch]\label{lem:app-os-reduction}
Fix $s>0$, write $(\sigma,\tilde\sigma,\tilde s_1,s_1,q)$ for the branch at $-s$,
and put $F=\Fw(q)$, $L=\Lw(q)$ and $\widehat F\defeq F/\sw2\in(0,1]$.
\begin{enumerate}[label=(\alph*)]
\item One has $s+s_1=s(1+\sigma F)$ and $\tilde s_1=\gin F/(1+\sigma F)>0$.
\item One has $qF=\sigma\tilde s_1=\gin\sigma F/(1+\sigma F)<\gin$, and
$\tilde s_1=F\,(\gin-qF)$.
\item With $\hat s\defeq s/(\sw2\gin)$ and $b\defeq\tilde s_1/(\sw2\gin)$,
one has $b\in(0,\widehat F]$ and
\[
\frac{b}{\widehat F}+r\,m_{\hat\nu_{\mathrm{out}}}(\hat s/b)=1 .
\]
\item For every $\mu\ge0$,
\[
\mathsf k(s;\mu)=\frac{1}{\sw2\gin}\,\frac{L}{\widehat F}\,\frac{b\mu}{\hat s+b\mu}.
\]
\end{enumerate}
\end{lemma}
-/
theorem lem_app_os_reduction_d {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Nin B : ℕ}
    (hNin : 1 ≤ Nin) (hB : 1 ≤ B) {nuOut : Measure ℝ}
    (br : HalfAnisoBranch β (gammaIn Nin B) nuOut) {s : ℝ} (hs : 0 < s) :
    ∀ μ : ℝ, 0 ≤ μ →
      kOs br s μ = 1 / (Muon.sPow β 2 * gammaIn Nin B) *
        (Muon.DetEquiv.Lw (Muon.emaW β) (br.q s) /
          (Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) / Muon.sPow β 2)) *
        (bHat br s * μ / (sHat β (gammaIn Nin B) s + bHat br s * μ)) := by
  intro μ hμ
  obtain ⟨hσ, -, -, -, hq⟩ := br.nonneg s hs
  have hF := os_F_pos' hβ0 hβ1 hq
  have hγ := os_gammaIn_pos hNin hB
  have hS : 0 < Muon.sPow β 2 := by
    rw [Muon.sPow_two hβ0 hβ1]
    apply div_pos <;> linarith
  have hc : Muon.sPow β 2 * gammaIn Nin B ≠ 0 := (mul_pos hS hγ).ne'
  obtain ⟨hsum, hS1T, hpos, -, -, -, -⟩ :=
    os_reduction_alg hs hσ hF hγ (br.eq_s1 s hs) (br.eq_sigmaT s hs) (br.eq_q s hs)
      (br.eq_s1T s hs)
  have hD : 0 < 1 + br.sigma s * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) := by
    have := mul_nonneg hσ hF.le
    linarith
  have hT : br.s1T s * (1 + br.sigma s * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s))
      = gammaIn Nin B * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) := by
    rw [hS1T, div_mul_cancel₀ _ hD.ne']
  have hden : 0 < s + br.s1T s * μ := by
    have := mul_nonneg hpos.le hμ
    linarith
  have hrat : bHat br s * μ / (sHat β (gammaIn Nin B) s + bHat br s * μ)
      = br.s1T s * μ / (s + br.s1T s * μ) := by
    unfold bHat sHat
    rw [show s / (Muon.sPow β 2 * gammaIn Nin B) + br.s1T s / (Muon.sPow β 2 * gammaIn Nin B) * μ
        = (s + br.s1T s * μ) / (Muon.sPow β 2 * gammaIn Nin B) by ring,
      div_mul_eq_mul_div, div_div_div_cancel_right₀ hc]
  unfold kOs
  rw [hsum, hrat]
  have hs0 : s ≠ 0 := hs.ne'
  have hden' : s + br.s1T s * μ ≠ 0 := hden.ne'
  have hD' : 1 + br.sigma s * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) ≠ 0 := hD.ne'
  have hF' : Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) ≠ 0 := hF.ne'
  have hγ' : gammaIn Nin B ≠ 0 := hγ.ne'
  have hS' : Muon.sPow β 2 ≠ 0 := hS.ne'
  have e1 : s * Muon.DetEquiv.Lw (Muon.emaW β) (br.q s) * μ /
      ((s + br.s1T s * μ) * (s * (1 + br.sigma s * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s))))
      = Muon.DetEquiv.Lw (Muon.emaW β) (br.q s) * μ /
        ((s + br.s1T s * μ) * (1 + br.sigma s * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s))) := by
    rw [div_eq_div_iff (mul_ne_zero hden' (mul_ne_zero hs0 hD'))
      (mul_ne_zero hden' hD')]
    ring
  have e2 : 1 / (Muon.sPow β 2 * gammaIn Nin B) *
      (Muon.DetEquiv.Lw (Muon.emaW β) (br.q s) /
        (Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) / Muon.sPow β 2)) *
      (br.s1T s * μ / (s + br.s1T s * μ))
      = Muon.DetEquiv.Lw (Muon.emaW β) (br.q s) * br.s1T s * μ /
        (gammaIn Nin B * Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) * (s + br.s1T s * μ)) := by
    field_simp
  rw [e1, e2, div_eq_div_iff (mul_ne_zero hden' hD')
    (mul_ne_zero (mul_ne_zero hγ' hF') hden')]
  linear_combination (-(Muon.DetEquiv.Lw (Muon.emaW β) (br.q s) * μ * (s + br.s1T s * μ))) * hT

/-! ## Helpers for the generic limit law (`thm:app-os-limit`, parts (i), (ii)) -/

private lemma os_J_continuousWithinAt {x0 : ℝ} (hx0 : 0 ≤ x0) :
    ContinuousWithinAt (fun x => Muon.DetEquiv.J x) (Ici 0) x0 := by
  unfold Muon.DetEquiv.J
  refine continuousWithinAt_of_dominated (F := fun x g => g ^ 2 / (1 + x * g ^ 2))
    (bound := fun g => g ^ 2) ?_ ?_ (Muon.Foundations.gaussian_integrable_pow 2) ?_
  · exact Filter.Eventually.of_forall fun x =>
      (by fun_prop : Measurable fun g : ℝ => g ^ 2 / (1 + x * g ^ 2)).aestronglyMeasurable
  · refine Filter.eventually_of_mem self_mem_nhdsWithin fun x hx =>
      Filter.Eventually.of_forall fun g => ?_
    have hx' : 0 ≤ x := hx
    have hm := mul_nonneg hx' (sq_nonneg g)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg g) (by linarith))]
    exact div_le_self (sq_nonneg g) (by linarith)
  · refine Filter.Eventually.of_forall fun g => ?_
    apply ContinuousAt.continuousWithinAt
    exact ContinuousAt.div continuousAt_const (by fun_prop) (os_den_pos hx0 g).ne'

private lemma os_J_contOn : ContinuousOn (fun x => Muon.DetEquiv.J x) (Ici 0) :=
  fun _ hx => os_J_continuousWithinAt hx

private lemma os_Lw_contOn {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ContinuousOn (fun q => Muon.DetEquiv.Lw (Muon.emaW β) q) (Ici 0) := by
  unfold Muon.DetEquiv.Lw
  refine continuousOn_tsum (u := fun j : ℕ => Muon.emaW β j)
    (f := fun (j : ℕ) (q : ℝ) => Muon.emaW β j * Muon.DetEquiv.J (Muon.emaW β j ^ 2 * q))
    (fun j => ?_) (os_emaW_summable hβ0 hβ1) (fun j q hq => ?_)
  · have hlin : ContinuousOn (fun q : ℝ => Muon.emaW β j ^ 2 * q) (Ici 0) :=
      (continuous_const.mul continuous_id).continuousOn
    exact continuousOn_const.mul (os_J_contOn.comp hlin
      (fun q hq => Set.mem_Ici.2 (mul_nonneg (sq_nonneg _) (Set.mem_Ici.1 hq))))
  · have hq' : 0 ≤ q := Set.mem_Ici.1 hq
    have h0 := os_emaW_nonneg hβ0 hβ1 j
    have hJ0 := os_J_nonneg (mul_nonneg (sq_nonneg (Muon.emaW β j)) hq')
    have hJ1 := os_J_le_one (mul_nonneg (sq_nonneg (Muon.emaW β j)) hq')
    show ‖Muon.emaW β j * Muon.DetEquiv.J (Muon.emaW β j ^ 2 * q)‖ ≤ Muon.emaW β j
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 hJ0)]
    exact mul_le_of_le_one_right h0 hJ1

private lemma os_hatNu_prob {nuOut : Measure ℝ} {γout : ℝ} (hγ : 0 < γout)
    (hmass : nuOut univ = ENNReal.ofReal γout) : IsProbabilityMeasure (hatNu nuOut γout) := by
  refine ⟨?_⟩
  unfold hatNu
  rw [Measure.smul_apply, hmass, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hγ).ne' ENNReal.ofReal_ne_top

private lemma os_hatNu_Iio {nuOut : Measure ℝ} {γout : ℝ} (hν0 : nuOut (Iio 0) = 0) :
    hatNu nuOut γout (Iio 0) = 0 := by
  unfold hatNu
  rw [Measure.smul_apply, hν0, smul_zero]

private lemma os_lam_pos {β qs : ℝ} (hβ0 : 0 ≤ β) (hqs : 0 < qs) : 0 < lamOs β qs := by
  unfold lamOs
  have : 0 ≤ 3 * (1 - β) ^ 2 * qs := mul_nonneg (by positivity) hqs.le
  linarith

private lemma os_kOs_contOn {β γin : ℝ} {nuOut : Measure ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (br : HalfAnisoBranch β γin nuOut) {μ : ℝ} (hμ : 0 ≤ μ) :
    ContinuousOn (fun s => kOs br s μ) (Ioi 0) := by
  have hL : ContinuousOn (fun s => Muon.DetEquiv.Lw (Muon.emaW β) (br.q s)) (Ioi 0) :=
    (os_Lw_contOn hβ0 hβ1).comp br.continuousOn_q
      (fun s hs => Set.mem_Ici.2 (br.nonneg s hs).2.2.2.2)
  unfold kOs
  apply ContinuousOn.div
  · exact (continuousOn_id.mul hL).mul continuousOn_const
  · exact (continuousOn_id.add (br.continuousOn_s1T.mul continuousOn_const)).mul
      (continuousOn_id.add br.continuousOn_s1)
  · intro s hs
    have hs' : 0 < s := hs
    obtain ⟨-, -, h3, h4, -⟩ := br.nonneg s hs'
    have ha := mul_nonneg h3 hμ
    exact (mul_pos (by linarith) (by linarith)).ne'

private lemma os_kOs_nonneg {β γin : ℝ} {nuOut : Measure ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (br : HalfAnisoBranch β γin nuOut) {s μ : ℝ} (hs : 0 < s) (hμ : 0 ≤ μ) :
    0 ≤ kOs br s μ := by
  obtain ⟨-, -, h3, h4, hq⟩ := br.nonneg s hs
  have hq3 : 0 ≤ 3 * (1 - β) ^ 2 * br.q s := mul_nonneg (by positivity) hq
  have hL : 0 ≤ Muon.DetEquiv.Lw (Muon.emaW β) (br.q s) :=
    le_trans (div_nonneg zero_le_one (by linarith))
      (lem_app_os_scalar_ii hβ0 hβ1 (br.q s) hq).2.2.1
  unfold kOs
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg hs.le hL) hμ
  · have ha := mul_nonneg h3 hμ
    exact mul_nonneg (by linarith) (by linarith)

private lemma os_kOs_le_inv {β γin : ℝ} {nuOut : Measure ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (br : HalfAnisoBranch β γin nuOut) {s μ : ℝ} (hs : 0 < s) (hμ : 0 ≤ μ) :
    kOs br s μ ≤ μ / s := by
  obtain ⟨-, -, h3, h4, hq⟩ := br.nonneg s hs
  have hL : Muon.DetEquiv.Lw (Muon.emaW β) (br.q s) ≤ 1 :=
    (lem_app_os_scalar_ii hβ0 hβ1 (br.q s) hq).2.2.2
  have ha : 0 ≤ br.s1T s * μ := mul_nonneg h3 hμ
  have hD : s * s ≤ (s + br.s1T s * μ) * (s + br.s1 s) := by
    nlinarith [mul_nonneg hs.le ha, mul_nonneg hs.le h4, mul_nonneg ha h4]
  have hDpos : 0 < s * s := mul_pos hs hs
  have hs0 : s ≠ 0 := hs.ne'
  unfold kOs
  calc s * Muon.DetEquiv.Lw (Muon.emaW β) (br.q s) * μ / ((s + br.s1T s * μ) * (s + br.s1 s))
      ≤ s * μ / ((s + br.s1T s * μ) * (s + br.s1 s)) := by
        apply div_le_div_of_nonneg_right _ (le_trans hDpos.le hD)
        nlinarith [mul_le_mul_of_nonneg_left hL (mul_nonneg hs.le hμ)]
    _ ≤ s * μ / (s * s) := div_le_div_of_nonneg_left (mul_nonneg hs.le hμ) hDpos hD
    _ = μ / s := mul_div_mul_left μ s hs0

/-- The profile integrand at a rescaled variable `sh` (`dOsIntegrand` with `sh = rh + v²`). -/
private def osG (ν : Measure ℝ) (r μ sh : ℝ) : ℝ :=
  profileRoot ν r sh * μ / (sh + profileRoot ν r sh * μ)

/-- Algebra: the comparison of the branch integrand with the profile integrand. -/
private lemma os_alg {S F L Q G Λq Λ : ℝ} (hS : 0 < S) (hF : 0 < F) (hΛq : 0 < Λq)
    (hΛ : Λq ≤ Λ) (hFS : S / Λq ≤ F) (hF2 : F ≤ S) (hL1 : 1 / Λq ≤ L) (hL2 : L ≤ 1)
    (hG : 0 ≤ G) (hQlo : F / S * G ≤ Q) (hQhi : Q ≤ G) :
    Λ⁻¹ * G ≤ L / (F / S) * Q ∧ L / (F / S) * Q ≤ Λ * G := by
  have hFSpos : 0 < F / S := div_pos hF hS
  have hκ0 : 0 ≤ L / (F / S) := by
    apply div_nonneg _ hFSpos.le
    have : 0 ≤ 1 / Λq := by positivity
    linarith
  have hκ : L / (F / S) ≤ Λq := by
    rw [div_div_eq_mul_div, div_le_iff₀ hF]
    have h2 : S ≤ Λq * F := by
      rw [mul_comm]
      exact (div_le_iff₀ hΛq).1 hFS
    have h3 : L * S ≤ S := mul_le_of_le_one_left hS.le hL2
    linarith
  have hκF : L / (F / S) * (F / S) = L := div_mul_cancel₀ L hFSpos.ne'
  have hLΛ : Λ⁻¹ ≤ L := by
    have h1 : Λ⁻¹ ≤ Λq⁻¹ := inv_anti₀ hΛq hΛ
    rw [one_div] at hL1
    linarith
  constructor
  · calc Λ⁻¹ * G ≤ L * G := mul_le_mul_of_nonneg_right hLΛ hG
      _ = L / (F / S) * ((F / S) * G) := by rw [← mul_assoc, hκF]
      _ ≤ L / (F / S) * Q := mul_le_mul_of_nonneg_left hQlo hκ0
  · calc L / (F / S) * Q ≤ L / (F / S) * G := mul_le_mul_of_nonneg_left hQhi hκ0
      _ ≤ Λ * G := mul_le_mul_of_nonneg_right (le_trans hκ hΛ) hG

/-- Pointwise comparison of the branch integrand with the profile integrand. -/
private lemma os_pointwise {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Nout Nin B : ℕ}
    (hNout : 1 ≤ Nout) (hNin : 1 ≤ Nin) (hB : 1 ≤ B) {nuOut : Measure ℝ}
    (hν0 : nuOut (Iio 0) = 0) (hmass : nuOut univ = ENNReal.ofReal (gammaOut Nout B))
    (hcond : 0 < β ∨ (β = 0 ∧ gammaIn Nin B < 1))
    {qs : ℝ} (hqs : 0 < qs ∧ qs * Muon.DetEquiv.Fw (Muon.emaW β) qs = gammaIn Nin B)
    (br : HalfAnisoBranch β (gammaIn Nin B) nuOut) {s : ℝ} (hs : 0 < s) {μ : ℝ} (hμ : 0 ≤ μ) :
    0 ≤ osG (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ (sHat β (gammaIn Nin B) s) ∧
      osG (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ (sHat β (gammaIn Nin B) s) ≤ 1 ∧
      (lamOs β qs)⁻¹ * osG (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
          (sHat β (gammaIn Nin B) s)
        ≤ Muon.sPow β 2 * gammaIn Nin B * kOs br s μ ∧
      Muon.sPow β 2 * gammaIn Nin B * kOs br s μ
        ≤ lamOs β qs * osG (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
          (sHat β (gammaIn Nin B) s) := by
  have hγout : 0 < gammaOut Nout B := by
    unfold gammaOut
    exact div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))
  haveI : IsProbabilityMeasure (hatNu nuOut (gammaOut Nout B)) := os_hatNu_prob hγout hmass
  have hnh0 := os_hatNu_Iio (γout := gammaOut Nout B) hν0
  have hr : 0 < (Nout : ℝ) / Nin :=
    div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))
  have hS : 0 < Muon.sPow β 2 := by
    rw [Muon.sPow_two hβ0 hβ1]
    apply div_pos <;> linarith
  have hγ : 0 < gammaIn Nin B := os_gammaIn_pos hNin hB
  obtain ⟨hσ, -, -, -, hq⟩ := br.nonneg s hs
  have hF := os_F_pos' hβ0 hβ1 hq
  obtain ⟨qs', -, hsol, hiff⟩ := lem_app_os_scalar_iii hβ0 hβ1 hγ hcond
  have hqe : qs = qs' := (hsol qs hqs.1).1 hqs.2
  rw [← hqe] at hiff
  have hlt : br.q s < qs :=
    (hiff (br.q s) hq).1 (lem_app_os_reduction_b hβ0 hβ1 hNin hB br hs).2.2.1
  have hΛq0 : 0 ≤ 3 * (1 - β) ^ 2 * br.q s := mul_nonneg (by positivity) hq
  have hΛle : 1 + 3 * (1 - β) ^ 2 * br.q s ≤ lamOs β qs := by
    unfold lamOs
    nlinarith [mul_le_mul_of_nonneg_left hlt.le (by positivity : (0:ℝ) ≤ 3 * (1 - β) ^ 2)]
  have hΛq : 0 < 1 + 3 * (1 - β) ^ 2 * br.q s := by linarith
  obtain ⟨hF1, hF2, hL1, hL2⟩ := lem_app_os_scalar_ii hβ0 hβ1 (br.q s) hq
  obtain ⟨hb, -, heq⟩ := lem_app_os_reduction_c hβ0 hβ1 hNout hNin hB hν0 hmass br hs
  have hsh : 0 < sHat β (gammaIn Nin B) s := div_pos hs (mul_pos hS hγ)
  have hFh : Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) / Muon.sPow β 2 ∈ Ioc (0:ℝ) 1 :=
    ⟨div_pos hF hS, (div_le_one hS).2 hF2⟩
  have hcmp := lem_app_os_compare_ii (hatNu nuOut (gammaOut Nout B)) hnh0 hr hsh hFh hb heq μ hμ
  have hred := lem_app_os_reduction_d hβ0 hβ1 hNin hB br hs μ hμ
  have hb0 : 0 ≤ profileRoot (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin)
      (sHat β (gammaIn Nin B) s) :=
    Real.sInf_nonneg (fun x hx => hx.1.1)
  have hG0 : 0 ≤ osG (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
      (sHat β (gammaIn Nin B) s) :=
    div_nonneg (mul_nonneg hb0 hμ) (add_nonneg hsh.le (mul_nonneg hb0 hμ))
  have hG1 : osG (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
      (sHat β (gammaIn Nin B) s) ≤ 1 :=
    (div_le_one (add_pos_of_pos_of_nonneg hsh (mul_nonneg hb0 hμ))).2
      (le_add_of_nonneg_left hsh.le)
  have hK : Muon.sPow β 2 * gammaIn Nin B * kOs br s μ
      = Muon.DetEquiv.Lw (Muon.emaW β) (br.q s) / (Muon.DetEquiv.Fw (Muon.emaW β) (br.q s) / Muon.sPow β 2)
        * (bHat br s * μ / (sHat β (gammaIn Nin B) s + bHat br s * μ)) := by
    rw [hred]
    field_simp
  have key := os_alg hS hF hΛq hΛle hF1 hF2 hL1 hL2 hG0 hcmp.1 hcmp.2
  refine ⟨hG0, hG1, ?_, ?_⟩
  · rw [hK]; exact key.1
  · rw [hK]; exact key.2

/-- Two-sided sandwich of the ridge coefficient by the oversampled profile, for `ρ ≥ 0`. -/
private lemma os_sandwich {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Nout Nin B : ℕ}
    (hNout : 1 ≤ Nout) (hNin : 1 ≤ Nin) (hB : 1 ≤ B) {nuOut : Measure ℝ}
    (hν0 : nuOut (Iio 0) = 0) (hmass : nuOut univ = ENNReal.ofReal (gammaOut Nout B))
    (hcond : 0 < β ∨ (β = 0 ∧ gammaIn Nin B < 1))
    {qs : ℝ} (hqs : 0 < qs ∧ qs * Muon.DetEquiv.Fw (Muon.emaW β) qs = gammaIn Nin B)
    (br : HalfAnisoBranch β (gammaIn Nin B) nuOut) {ρ : ℝ} (hρ : 0 ≤ ρ) {μ : ℝ} (hμ : 0 ≤ μ) :
    (lamOs β qs)⁻¹ * dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
        (ρ / (Muon.sPow β 2 * gammaIn Nin B)) ≤
      Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dRidge br ρ μ ∧
    Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dRidge br ρ μ ≤
      lamOs β qs * dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
        (ρ / (Muon.sPow β 2 * gammaIn Nin B)) := by
  have hγout : 0 < gammaOut Nout B := by
    unfold gammaOut
    exact div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))
  haveI : IsProbabilityMeasure (hatNu nuOut (gammaOut Nout B)) := os_hatNu_prob hγout hmass
  have hnh0 := os_hatNu_Iio (γout := gammaOut Nout B) hν0
  have hr : 0 < (Nout : ℝ) / Nin :=
    div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))
  have hS : 0 < Muon.sPow β 2 := by
    rw [Muon.sPow_two hβ0 hβ1]
    apply div_pos <;> linarith
  have hγ : 0 < gammaIn Nin B := os_gammaIn_pos hNin hB
  have hSγ : 0 < Muon.sPow β 2 * gammaIn Nin B := mul_pos hS hγ
  have hΛpos : 0 < lamOs β qs := os_lam_pos hβ0 hqs.1
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) := ⟨_, rfl⟩
  rw [← hcdef]
  have hc : 0 < c := by rw [hcdef]; exact Real.sqrt_pos.2 hSγ
  have hc2 : c * c = Muon.sPow β 2 * gammaIn Nin B := by
    rw [hcdef]; exact Real.mul_self_sqrt hSγ.le
  have hKG : ∀ v : ℝ, 0 < v →
      0 ≤ dOsIntegrand (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
          (ρ / (Muon.sPow β 2 * gammaIn Nin B)) v ∧
      (lamOs β qs)⁻¹ * dOsIntegrand (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
          (ρ / (Muon.sPow β 2 * gammaIn Nin B)) v
        ≤ Muon.sPow β 2 * gammaIn Nin B * kOs br (ρ + (c * v) ^ 2) μ ∧
      Muon.sPow β 2 * gammaIn Nin B * kOs br (ρ + (c * v) ^ 2) μ
        ≤ lamOs β qs * dOsIntegrand (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
          (ρ / (Muon.sPow β 2 * gammaIn Nin B)) v := by
    intro v hv
    have hsv : 0 < ρ + (c * v) ^ 2 := add_pos_of_nonneg_of_pos hρ (pow_pos (mul_pos hc hv) 2)
    have hcv2 : (c * v) ^ 2 = (Muon.sPow β 2 * gammaIn Nin B) * v ^ 2 := by
      rw [← hc2]; ring
    have hsh : sHat β (gammaIn Nin B) (ρ + (c * v) ^ 2)
        = ρ / (Muon.sPow β 2 * gammaIn Nin B) + v ^ 2 := by
      unfold sHat
      rw [hcv2, add_div, mul_div_cancel_left₀ _ hSγ.ne']
    have hp := os_pointwise hβ0 hβ1 hNout hNin hB hν0 hmass hcond hqs br hsv hμ
    rw [hsh] at hp
    exact ⟨hp.1, hp.2.2.1, hp.2.2.2⟩
  have hGint : IntegrableOn (dOsIntegrand (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
      (ρ / (Muon.sPow β 2 * gammaIn Nin B))) (Ioi 0) :=
    lem_app_os_profile_i (hatNu nuOut (gammaOut Nout B)) hnh0 hr hμ _ (div_nonneg hρ hSγ.le)
  have hKcont : ContinuousOn
      (fun v : ℝ => Muon.sPow β 2 * gammaIn Nin B * kOs br (ρ + (c * v) ^ 2) μ) (Ioi 0) := by
    refine continuousOn_const.mul ((os_kOs_contOn hβ0 hβ1 br hμ).comp ?_ ?_)
    · exact (continuous_const.add ((continuous_const.mul continuous_id).pow 2)).continuousOn
    · intro v hv
      exact Set.mem_Ioi.2 (add_pos_of_nonneg_of_pos hρ (pow_pos (mul_pos hc (Set.mem_Ioi.1 hv)) 2))
  have hKint : IntegrableOn
      (fun v : ℝ => Muon.sPow β 2 * gammaIn Nin B * kOs br (ρ + (c * v) ^ 2) μ) (Ioi 0) := by
    refine Integrable.mono' (hGint.const_mul (lamOs β qs))
      (hKcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    obtain ⟨h0, h1, h2⟩ := hKG v hv
    have hK0 : 0 ≤ Muon.sPow β 2 * gammaIn Nin B * kOs br (ρ + (c * v) ^ 2) μ :=
      le_trans (mul_nonneg (inv_nonneg.2 hΛpos.le) h0) h1
    rw [Real.norm_eq_abs, abs_of_nonneg hK0]
    exact h2
  have hlow := setIntegral_mono_on (hGint.const_mul (lamOs β qs)⁻¹) hKint measurableSet_Ioi
    (fun v hv => (hKG v hv).2.1)
  have hhigh := setIntegral_mono_on hKint (hGint.const_mul (lamOs β qs)) measurableSet_Ioi
    (fun v hv => (hKG v hv).2.2)
  rw [integral_const_mul] at hlow
  have hhigh' : ∫ v in Ioi (0:ℝ), Muon.sPow β 2 * gammaIn Nin B * kOs br (ρ + (c * v) ^ 2) μ
      ≤ lamOs β qs * ∫ v in Ioi (0:ℝ), dOsIntegrand (hatNu nuOut (gammaOut Nout B))
          ((Nout : ℝ) / Nin) μ (ρ / (Muon.sPow β 2 * gammaIn Nin B)) v := by
    rw [← integral_const_mul]; exact hhigh
  have hcv : ∫ u in Ioi (0:ℝ), kOs br (ρ + u ^ 2) μ
      = c * ∫ v in Ioi (0:ℝ), kOs br (ρ + (c * v) ^ 2) μ := by
    have h := integral_comp_mul_left_Ioi (fun u : ℝ => kOs br (ρ + u ^ 2) μ) 0 hc
    simp only [mul_zero, smul_eq_mul] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  have hdR : c * dRidge br ρ μ
      = Real.sqrt 2 / Real.pi * ∫ v in Ioi (0:ℝ),
          Muon.sPow β 2 * gammaIn Nin B * kOs br (ρ + (c * v) ^ 2) μ := by
    rw [integral_const_mul]
    unfold dRidge
    rw [hcv]
    linear_combination (Real.sqrt 2 / Real.pi * ∫ v in Ioi (0:ℝ), kOs br (ρ + (c * v) ^ 2) μ) * hc2
  have hsq : 0 ≤ Real.sqrt 2 / Real.pi := by positivity
  rw [hdR]
  show _ ∧ _
  constructor
  · calc (lamOs β qs)⁻¹ * (Real.sqrt 2 / Real.pi * ∫ v in Ioi (0:ℝ),
          dOsIntegrand (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
            (ρ / (Muon.sPow β 2 * gammaIn Nin B)) v)
        = Real.sqrt 2 / Real.pi * ((lamOs β qs)⁻¹ * ∫ v in Ioi (0:ℝ),
          dOsIntegrand (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
            (ρ / (Muon.sPow β 2 * gammaIn Nin B)) v) := by ring
      _ ≤ Real.sqrt 2 / Real.pi * ∫ v in Ioi (0:ℝ),
          Muon.sPow β 2 * gammaIn Nin B * kOs br (ρ + (c * v) ^ 2) μ :=
        mul_le_mul_of_nonneg_left hlow hsq
  · calc Real.sqrt 2 / Real.pi * ∫ v in Ioi (0:ℝ),
          Muon.sPow β 2 * gammaIn Nin B * kOs br (ρ + (c * v) ^ 2) μ
        ≤ Real.sqrt 2 / Real.pi * (lamOs β qs * ∫ v in Ioi (0:ℝ),
          dOsIntegrand (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
            (ρ / (Muon.sPow β 2 * gammaIn Nin B)) v) :=
        mul_le_mul_of_nonneg_left hhigh' hsq
      _ = lamOs β qs * (Real.sqrt 2 / Real.pi * ∫ v in Ioi (0:ℝ),
          dOsIntegrand (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
            (ρ / (Muon.sPow β 2 * gammaIn Nin B)) v) := by ring

/-! ## The generic oversampled limit law (`thm:app-os-limit`) -/

/-- Label `thm:app-os-limit`, generic form, part (i) for any `HalfAnisoBranch` (the declaration of
record is L-G2.7). Snapshot `cr-2026-10-23`.
Statement verbatim:

\begin{theorem}[Oversampled limit law]\label{thm:app-os-limit}
Let $\Nout,\Nin,B\ge1$, let $\Sigmaout$ be positive semidefinite, let
$\bmom\in[0,1)$, and assume that $\bmom>0$, or that $\bmom=0$ and $\gin<1$. Let
$q_\star$ be as in \cref{lem:app-os-scalar}(iii), and put
$\Lambda\defeq1+3(1-\bmom)^2q_\star$. Write
$\mathfrak d^{\rm os}=\mathfrak d^{\rm os}_{\hat\nu_{\mathrm{out}},r}$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ridge>0$ and $\mu\ge0$,
\[
\Lambda^{-1}\,\mathfrak d^{\rm os}(\mu;\hat\ridge)\le\sqrt{\sw2\gin}\;\mathfrak d_\ridge(\mu)\le\Lambda\,\mathfrak d^{\rm os}(\mu;\hat\ridge).
\]
\item For every $\mu\ge0$ the limit
\[
\mathfrak d_0(\mu)\defeq\lim_{\ridge\downarrow0}\mathfrak d_\ridge(\mu)=\frac{\sqrt2}{\pi}\int_0^\infty\mathsf k(u^2;\mu)\,\dif u
\]
exists in $[0,\infty)$, and it satisfies the bounds of (i) with $\ridge=\hat\ridge=0$.
\item If $\epsilon_{\rm os}<1$, then $\Lambda\le(1-\epsilon_{\rm os})^{-1}$. Consequently,
for every $\ridge\ge0$ and $1\le i\le\Nout$,
\begin{equation}\label{eqn:app-os-limit}
\mathfrak d_i(\ridge)=\vartheta_i\,\sqrt{\frac{B_{\rm eff}}{\Nin}}\;\mathfrak d^{\rm os}(\mu_i;\hat\ridge)
\qquad\text{for some }\vartheta_i\in\big[1-\epsilon_{\rm os},(1-\epsilon_{\rm os})^{-1}\big],
\end{equation}
and for every $\mu\ge0$
\[
\Big|\sqrt{\sw2\gin}\;\mathfrak d_\ridge(\mu)-\mathfrak d^{\rm os}(\mu;\hat\ridge)\Big|
\le\frac{\epsilon_{\rm os}}{1-\epsilon_{\rm os}}\,\mathfrak d^{\rm os}(\mu;\hat\ridge)
\le\frac{\epsilon_{\rm os}}{1-\epsilon_{\rm os}}\sqrt{\frac\mu2}.
\]
\item For $\ridge\ge0$ let $\vartheta_\ridge(\mu)\defeq\sqrt{\sw2\gin}\,\mathfrak d_\ridge(\mu)/\mathfrak d^{\rm os}(\mu;\hat\ridge)$
for $\mu>0$ and $\vartheta_\ridge(0)\defeq1$. Then
$\operatorname{spec}\vartheta_\ridge(\Sigmaout)\subset[\Lambda^{-1},\Lambda]$ and
\[
\mathfrak d_\ridge(\Sigmaout)=\sqrt{\frac{B_{\rm eff}}{\Nin}}\;\vartheta_\ridge(\Sigmaout)\,\mathfrak d^{\rm os}(\Sigmaout;\hat\ridge).
\]
\end{enumerate}
\end{theorem}
-/
theorem limit_generic_i {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Nout Nin B : ℕ}
    (hNout : 1 ≤ Nout) (hNin : 1 ≤ Nin) (hB : 1 ≤ B) {nuOut : Measure ℝ}
    (hν0 : nuOut (Iio 0) = 0) (hmass : nuOut univ = ENNReal.ofReal (gammaOut Nout B))
    (hcond : 0 < β ∨ (β = 0 ∧ gammaIn Nin B < 1))
    {qs : ℝ} (hqs : 0 < qs ∧ qs * Muon.DetEquiv.Fw (Muon.emaW β) qs = gammaIn Nin B)
    (br : HalfAnisoBranch β (gammaIn Nin B) nuOut) :
    ∀ ρ : ℝ, 0 < ρ → ∀ μ : ℝ, 0 ≤ μ →
      (lamOs β qs)⁻¹ * dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
          (ρ / (Muon.sPow β 2 * gammaIn Nin B)) ≤
        Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dRidge br ρ μ ∧
      Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dRidge br ρ μ ≤
        lamOs β qs * dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
          (ρ / (Muon.sPow β 2 * gammaIn Nin B)) := by
  intro ρ hρ μ hμ
  exact os_sandwich hβ0 hβ1 hNout hNin hB hν0 hmass hcond hqs br hρ.le hμ

/-- Label `thm:app-os-limit`, generic form, part (ii) for any `HalfAnisoBranch` (record is L-G2.7). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{theorem}[Oversampled limit law]\label{thm:app-os-limit}
Let $\Nout,\Nin,B\ge1$, let $\Sigmaout$ be positive semidefinite, let
$\bmom\in[0,1)$, and assume that $\bmom>0$, or that $\bmom=0$ and $\gin<1$. Let
$q_\star$ be as in \cref{lem:app-os-scalar}(iii), and put
$\Lambda\defeq1+3(1-\bmom)^2q_\star$. Write
$\mathfrak d^{\rm os}=\mathfrak d^{\rm os}_{\hat\nu_{\mathrm{out}},r}$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ridge>0$ and $\mu\ge0$,
\[
\Lambda^{-1}\,\mathfrak d^{\rm os}(\mu;\hat\ridge)\le\sqrt{\sw2\gin}\;\mathfrak d_\ridge(\mu)\le\Lambda\,\mathfrak d^{\rm os}(\mu;\hat\ridge).
\]
\item For every $\mu\ge0$ the limit
\[
\mathfrak d_0(\mu)\defeq\lim_{\ridge\downarrow0}\mathfrak d_\ridge(\mu)=\frac{\sqrt2}{\pi}\int_0^\infty\mathsf k(u^2;\mu)\,\dif u
\]
exists in $[0,\infty)$, and it satisfies the bounds of (i) with $\ridge=\hat\ridge=0$.
\item If $\epsilon_{\rm os}<1$, then $\Lambda\le(1-\epsilon_{\rm os})^{-1}$. Consequently,
for every $\ridge\ge0$ and $1\le i\le\Nout$,
\begin{equation}\label{eqn:app-os-limit}
\mathfrak d_i(\ridge)=\vartheta_i\,\sqrt{\frac{B_{\rm eff}}{\Nin}}\;\mathfrak d^{\rm os}(\mu_i;\hat\ridge)
\qquad\text{for some }\vartheta_i\in\big[1-\epsilon_{\rm os},(1-\epsilon_{\rm os})^{-1}\big],
\end{equation}
and for every $\mu\ge0$
\[
\Big|\sqrt{\sw2\gin}\;\mathfrak d_\ridge(\mu)-\mathfrak d^{\rm os}(\mu;\hat\ridge)\Big|
\le\frac{\epsilon_{\rm os}}{1-\epsilon_{\rm os}}\,\mathfrak d^{\rm os}(\mu;\hat\ridge)
\le\frac{\epsilon_{\rm os}}{1-\epsilon_{\rm os}}\sqrt{\frac\mu2}.
\]
\item For $\ridge\ge0$ let $\vartheta_\ridge(\mu)\defeq\sqrt{\sw2\gin}\,\mathfrak d_\ridge(\mu)/\mathfrak d^{\rm os}(\mu;\hat\ridge)$
for $\mu>0$ and $\vartheta_\ridge(0)\defeq1$. Then
$\operatorname{spec}\vartheta_\ridge(\Sigmaout)\subset[\Lambda^{-1},\Lambda]$ and
\[
\mathfrak d_\ridge(\Sigmaout)=\sqrt{\frac{B_{\rm eff}}{\Nin}}\;\vartheta_\ridge(\Sigmaout)\,\mathfrak d^{\rm os}(\Sigmaout;\hat\ridge).
\]
\end{enumerate}
\end{theorem}
-/
theorem limit_generic_ii {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Nout Nin B : ℕ}
    (hNout : 1 ≤ Nout) (hNin : 1 ≤ Nin) (hB : 1 ≤ B) {nuOut : Measure ℝ}
    (hν0 : nuOut (Iio 0) = 0) (hmass : nuOut univ = ENNReal.ofReal (gammaOut Nout B))
    (hcond : 0 < β ∨ (β = 0 ∧ gammaIn Nin B < 1))
    {qs : ℝ} (hqs : 0 < qs ∧ qs * Muon.DetEquiv.Fw (Muon.emaW β) qs = gammaIn Nin B)
    (br : HalfAnisoBranch β (gammaIn Nin B) nuOut) :
    ∀ μ : ℝ, 0 ≤ μ →
      Tendsto (fun ρ : ℝ => dRidge br ρ μ) (𝓝[>] (0 : ℝ)) (𝓝 (dZero br μ)) ∧
      0 ≤ dZero br μ ∧
      (lamOs β qs)⁻¹ * dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ 0 ≤
        Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dZero br μ ∧
      Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dZero br μ ≤
        lamOs β qs * dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ 0 := by
  intro μ hμ
  have hS : 0 < Muon.sPow β 2 := by
    rw [Muon.sPow_two hβ0 hβ1]
    apply div_pos <;> linarith
  have hγ : 0 < gammaIn Nin B := os_gammaIn_pos hNin hB
  have hSγ : 0 < Muon.sPow β 2 * gammaIn Nin B := mul_pos hS hγ
  have hΛpos : 0 < lamOs β qs := os_lam_pos hβ0 hqs.1
  have hd0 := os_sandwich hβ0 hβ1 hNout hNin hB hν0 hmass hcond hqs br (le_refl (0:ℝ)) hμ
  rw [zero_div] at hd0
  have hdz : dRidge br 0 μ = dZero br μ := by
    unfold dRidge dZero
    simp
  rw [hdz] at hd0
  have hbound : ∀ s : ℝ, 0 < s → kOs br s μ ≤ lamOs β qs / (Muon.sPow β 2 * gammaIn Nin B) := by
    intro s hs
    have hp := os_pointwise hβ0 hβ1 hNout hNin hB hν0 hmass hcond hqs br hs hμ
    have h1 := mul_le_of_le_one_right hΛpos.le hp.2.1
    rw [le_div_iff₀ hSγ]
    calc kOs br s μ * (Muon.sPow β 2 * gammaIn Nin B)
        = Muon.sPow β 2 * gammaIn Nin B * kOs br s μ := mul_comm _ _
      _ ≤ _ := hp.2.2.2
      _ ≤ _ := h1
  have hC0 : 0 ≤ lamOs β qs / (Muon.sPow β 2 * gammaIn Nin B) := div_nonneg hΛpos.le hSγ.le
  have hmaj : ∀ ρ : ℝ, 0 < ρ → ∀ u : ℝ, 0 < u →
      kOs br (ρ + u ^ 2) μ
        ≤ (2 * (lamOs β qs / (Muon.sPow β 2 * gammaIn Nin B)) + 2 * μ) * (1 + u ^ 2)⁻¹ := by
    intro ρ hρ u hu
    have hs : 0 < ρ + u ^ 2 := add_pos hρ (pow_pos hu 2)
    have hk0 := os_kOs_nonneg hβ0 hβ1 br hs hμ
    have hC := hbound (ρ + u ^ 2) hs
    have hI := os_kOs_le_inv hβ0 hβ1 br hs hμ
    have hA : kOs br (ρ + u ^ 2) μ * (ρ + u ^ 2) ≤ μ := (le_div_iff₀ hs).1 hI
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    rcases le_total u 1 with h1 | h1
    · have hu2 : u ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hC (by positivity : (0:ℝ) ≤ 1 + u ^ 2),
        mul_nonneg hC0 (sub_nonneg.2 hu2)]
    · have hu2 : 1 ≤ u ^ 2 := by nlinarith
      have e1 : kOs br (ρ + u ^ 2) μ * u ^ 2 ≤ μ := by
        nlinarith [mul_nonneg hk0 hρ.le]
      have e2 : kOs br (ρ + u ^ 2) μ ≤ μ := by
        nlinarith [mul_nonneg hk0 (sub_nonneg.2 hu2)]
      nlinarith
  refine ⟨?_, ?_, hd0.1, hd0.2⟩
  · unfold dRidge dZero
    apply Filter.Tendsto.const_mul
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u : ℝ => (2 * (lamOs β qs / (Muon.sPow β 2 * gammaIn Nin B)) + 2 * μ)
        * (1 + u ^ 2)⁻¹) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      have hcont : ContinuousOn (fun u : ℝ => ρ + u ^ 2) (Ioi 0) :=
        (continuous_const.add (continuous_id.pow 2)).continuousOn
      exact ((os_kOs_contOn hβ0 hβ1 br hμ).comp hcont (fun u hu =>
        Set.mem_Ioi.2 (add_pos (Set.mem_Ioi.1 hρ) (pow_pos (Set.mem_Ioi.1 hu) 2)))).aestronglyMeasurable
          measurableSet_Ioi
    · have hev : ∀ᶠ ρ in 𝓝[>] (0:ℝ), ρ < 1 :=
        (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, hev] with ρ hρ hρ1
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (os_kOs_nonneg hβ0 hβ1 br
        (add_pos (Set.mem_Ioi.1 hρ) (pow_pos (Set.mem_Ioi.1 hu) 2)) hμ)]
      exact hmaj ρ (Set.mem_Ioi.1 hρ) u (Set.mem_Ioi.1 hu)
    · exact (integrable_inv_one_add_sq.const_mul _).integrableOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hc := (os_kOs_contOn hβ0 hβ1 br hμ).continuousAt
        (Ioi_mem_nhds (pow_pos (Set.mem_Ioi.1 hu) 2))
      have hT : Tendsto (fun ρ : ℝ => ρ + u ^ 2) (𝓝[>] (0:ℝ)) (𝓝 (u ^ 2)) := by
        have h0 : Tendsto (fun ρ : ℝ => ρ + u ^ 2) (𝓝 (0:ℝ)) (𝓝 (0 + u ^ 2)) :=
          (show Continuous (fun ρ : ℝ => ρ + u ^ 2) by fun_prop).tendsto 0
        rw [zero_add] at h0
        exact tendsto_nhdsWithin_of_tendsto_nhds h0
      exact hc.tendsto.comp hT
  · unfold dZero
    exact mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi
      (fun u hu => os_kOs_nonneg hβ0 hβ1 br (pow_pos (Set.mem_Ioi.1 hu) 2) hμ))

/-- Label `thm:app-os-limit`, generic form, part (iii) for any `HalfAnisoBranch` (record is L-G2.7). Snapshot `cr-2026-10-23`. Statement verbatim:

\begin{theorem}[Oversampled limit law]\label{thm:app-os-limit}
Let $\Nout,\Nin,B\ge1$, let $\Sigmaout$ be positive semidefinite, let
$\bmom\in[0,1)$, and assume that $\bmom>0$, or that $\bmom=0$ and $\gin<1$. Let
$q_\star$ be as in \cref{lem:app-os-scalar}(iii), and put
$\Lambda\defeq1+3(1-\bmom)^2q_\star$. Write
$\mathfrak d^{\rm os}=\mathfrak d^{\rm os}_{\hat\nu_{\mathrm{out}},r}$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ridge>0$ and $\mu\ge0$,
\[
\Lambda^{-1}\,\mathfrak d^{\rm os}(\mu;\hat\ridge)\le\sqrt{\sw2\gin}\;\mathfrak d_\ridge(\mu)\le\Lambda\,\mathfrak d^{\rm os}(\mu;\hat\ridge).
\]
\item For every $\mu\ge0$ the limit
\[
\mathfrak d_0(\mu)\defeq\lim_{\ridge\downarrow0}\mathfrak d_\ridge(\mu)=\frac{\sqrt2}{\pi}\int_0^\infty\mathsf k(u^2;\mu)\,\dif u
\]
exists in $[0,\infty)$, and it satisfies the bounds of (i) with $\ridge=\hat\ridge=0$.
\item If $\epsilon_{\rm os}<1$, then $\Lambda\le(1-\epsilon_{\rm os})^{-1}$. Consequently,
for every $\ridge\ge0$ and $1\le i\le\Nout$,
\begin{equation}\label{eqn:app-os-limit}
\mathfrak d_i(\ridge)=\vartheta_i\,\sqrt{\frac{B_{\rm eff}}{\Nin}}\;\mathfrak d^{\rm os}(\mu_i;\hat\ridge)
\qquad\text{for some }\vartheta_i\in\big[1-\epsilon_{\rm os},(1-\epsilon_{\rm os})^{-1}\big],
\end{equation}
and for every $\mu\ge0$
\[
\Big|\sqrt{\sw2\gin}\;\mathfrak d_\ridge(\mu)-\mathfrak d^{\rm os}(\mu;\hat\ridge)\Big|
\le\frac{\epsilon_{\rm os}}{1-\epsilon_{\rm os}}\,\mathfrak d^{\rm os}(\mu;\hat\ridge)
\le\frac{\epsilon_{\rm os}}{1-\epsilon_{\rm os}}\sqrt{\frac\mu2}.
\]
\item For $\ridge\ge0$ let $\vartheta_\ridge(\mu)\defeq\sqrt{\sw2\gin}\,\mathfrak d_\ridge(\mu)/\mathfrak d^{\rm os}(\mu;\hat\ridge)$
for $\mu>0$ and $\vartheta_\ridge(0)\defeq1$. Then
$\operatorname{spec}\vartheta_\ridge(\Sigmaout)\subset[\Lambda^{-1},\Lambda]$ and
\[
\mathfrak d_\ridge(\Sigmaout)=\sqrt{\frac{B_{\rm eff}}{\Nin}}\;\vartheta_\ridge(\Sigmaout)\,\mathfrak d^{\rm os}(\Sigmaout;\hat\ridge).
\]
\end{enumerate}
\end{theorem}
-/
theorem limit_generic_iii {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Nout Nin B : ℕ}
    (hNout : 1 ≤ Nout) (hNin : 1 ≤ Nin) (hB : 1 ≤ B) {nuOut : Measure ℝ}
    (hν0 : nuOut (Iio 0) = 0) (hmass : nuOut univ = ENNReal.ofReal (gammaOut Nout B))
    (hcond : 0 < β ∨ (β = 0 ∧ gammaIn Nin B < 1))
    {qs : ℝ} (hqs : 0 < qs ∧ qs * Muon.DetEquiv.Fw (Muon.emaW β) qs = gammaIn Nin B)
    (hε : epsOs β (gammaIn Nin B) < 1)
    (br : HalfAnisoBranch β (gammaIn Nin B) nuOut) :
    lamOs β qs ≤ (1 - epsOs β (gammaIn Nin B))⁻¹ ∧
    (∀ ρ : ℝ, 0 ≤ ρ → ∀ μ : ℝ, 0 ≤ μ → ∃ ϑ : ℝ,
      ϑ ∈ Icc (1 - epsOs β (gammaIn Nin B)) (1 - epsOs β (gammaIn Nin B))⁻¹ ∧
      dRidge br ρ μ = ϑ * Real.sqrt ((B : ℝ) / Muon.sPow β 2 / (Nin : ℝ)) *
        dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
          (ρ / (Muon.sPow β 2 * gammaIn Nin B))) ∧
    (∀ ρ : ℝ, 0 ≤ ρ → ∀ μ : ℝ, 0 ≤ μ →
      |Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dRidge br ρ μ -
          dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
            (ρ / (Muon.sPow β 2 * gammaIn Nin B))| ≤
        epsOs β (gammaIn Nin B) / (1 - epsOs β (gammaIn Nin B)) *
          dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
            (ρ / (Muon.sPow β 2 * gammaIn Nin B)) ∧
      epsOs β (gammaIn Nin B) / (1 - epsOs β (gammaIn Nin B)) *
          dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
            (ρ / (Muon.sPow β 2 * gammaIn Nin B)) ≤
        epsOs β (gammaIn Nin B) / (1 - epsOs β (gammaIn Nin B)) * Real.sqrt (μ / 2)) := by
  have hγout : 0 < gammaOut Nout B := by
    unfold gammaOut
    exact div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))
  haveI : IsProbabilityMeasure (hatNu nuOut (gammaOut Nout B)) := os_hatNu_prob hγout hmass
  have hnh0 := os_hatNu_Iio (γout := gammaOut Nout B) hν0
  have hr : 0 < (Nout : ℝ) / Nin :=
    div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))
  have hS : 0 < Muon.sPow β 2 := by
    rw [Muon.sPow_two hβ0 hβ1]
    apply div_pos <;> linarith
  have hγ : 0 < gammaIn Nin B := os_gammaIn_pos hNin hB
  have hSγ : 0 < Muon.sPow β 2 * gammaIn Nin B := mul_pos hS hγ
  have hΛpos : 0 < lamOs β qs := os_lam_pos hβ0 hqs.1
  have h1ε : 0 < 1 - epsOs β (gammaIn Nin B) := by linarith
  have hε0 : 0 ≤ epsOs β (gammaIn Nin B) := by
    unfold epsOs
    have : 0 ≤ 1 - β ^ 2 := by nlinarith
    exact mul_nonneg (mul_nonneg (by norm_num) this) hγ.le
  have hκ0 : 0 ≤ epsOs β (gammaIn Nin B) / (1 - epsOs β (gammaIn Nin B)) :=
    div_nonneg hε0 h1ε.le
  have hΛle : lamOs β qs ≤ (1 - epsOs β (gammaIn Nin B))⁻¹ := by
    have h := (lem_app_os_scalar_iv hβ0 hβ1 hγ hε).2 qs hqs.1 hqs.2
    rwa [one_div] at h
  have hΛ1 : (1 - epsOs β (gammaIn Nin B)) * lamOs β qs ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hΛle h1ε.le
    rwa [mul_inv_cancel₀ h1ε.ne'] at h
  have hΛinv : 1 - epsOs β (gammaIn Nin B) ≤ (lamOs β qs)⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hΛ1 (inv_nonneg.2 hΛpos.le)
    have e : (lamOs β qs)⁻¹ * ((1 - epsOs β (gammaIn Nin B)) * lamOs β qs)
        = 1 - epsOs β (gammaIn Nin B) := by
      rw [mul_comm (1 - epsOs β (gammaIn Nin B)), ← mul_assoc, inv_mul_cancel₀ hΛpos.ne', one_mul]
    rw [e, mul_one] at h
    exact h
  have hinvge : 1 ≤ (1 - epsOs β (gammaIn Nin B))⁻¹ := by
    have hi := mul_inv_cancel₀ h1ε.ne'
    have hip := inv_pos.2 h1ε
    nlinarith [mul_nonneg hε0 hip.le]
  have hκ1 : lamOs β qs - 1 ≤ epsOs β (gammaIn Nin B) / (1 - epsOs β (gammaIn Nin B)) := by
    rw [le_div_iff₀ h1ε]
    nlinarith [hΛ1]
  have hεκ : epsOs β (gammaIn Nin B) ≤ epsOs β (gammaIn Nin B) / (1 - epsOs β (gammaIn Nin B)) := by
    rw [le_div_iff₀ h1ε]
    nlinarith [mul_nonneg hε0 hε0]
  have hκ2 : 1 - (lamOs β qs)⁻¹ ≤ epsOs β (gammaIn Nin B) / (1 - epsOs β (gammaIn Nin B)) := by
    linarith
  have hDnn : ∀ μ : ℝ, 0 ≤ μ → ∀ rh : ℝ, 0 ≤ rh →
      0 ≤ dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ rh := by
    intro μ hμ rh hrh
    rcases hμ.lt_or_eq with h | h
    · exact ((lem_app_os_profile_iii (hatNu nuOut (gammaOut Nout B)) hnh0 hr hμ rh hrh).2 h).le
    · subst h
      unfold dOs dOsIntegrand
      simp
  refine ⟨hΛle, ?_, ?_⟩
  · intro ρ hρ μ hμ
    rcases hμ.lt_or_eq with hμpos | hμ0
    · have hsw := os_sandwich hβ0 hβ1 hNout hNin hB hν0 hmass hcond hqs br hρ hμ
      have hDpos : 0 < dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
          (ρ / (Muon.sPow β 2 * gammaIn Nin B)) :=
        (lem_app_os_profile_iii (hatNu nuOut (gammaOut Nout B)) hnh0 hr hμ _
          (div_nonneg hρ hSγ.le)).2 hμpos
      have hBne : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hNne : (Nin : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hSne : Muon.sPow β 2 ≠ 0 := hS.ne'
      have hsq : Real.sqrt ((B : ℝ) / Muon.sPow β 2 / (Nin : ℝ))
          * Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) = 1 := by
        have hnn : 0 ≤ (B : ℝ) / Muon.sPow β 2 / (Nin : ℝ) :=
          div_nonneg (div_nonneg (Nat.cast_nonneg _) hS.le) (Nat.cast_nonneg _)
        rw [← Real.sqrt_mul hnn]
        have e : (B : ℝ) / Muon.sPow β 2 / (Nin : ℝ) * (Muon.sPow β 2 * gammaIn Nin B) = 1 := by
          unfold gammaIn
          field_simp
        rw [e, Real.sqrt_one]
      set c := Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) with hcdef
      set D := dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
        (ρ / (Muon.sPow β 2 * gammaIn Nin B)) with hDdef
      set sq := Real.sqrt ((B : ℝ) / Muon.sPow β 2 / (Nin : ℝ)) with hsqdef
      have hDne : D ≠ 0 := hDpos.ne'
      refine ⟨c * dRidge br ρ μ / D, ⟨?_, ?_⟩, ?_⟩
      · rw [le_div_iff₀ hDpos]
        exact le_trans (mul_le_mul_of_nonneg_right hΛinv hDpos.le) hsw.1
      · rw [div_le_iff₀ hDpos]
        exact le_trans hsw.2 (mul_le_mul_of_nonneg_right hΛle hDpos.le)
      · have e3 : c * dRidge br ρ μ / D * sq * D = dRidge br ρ μ * (sq * c) := by
          field_simp <;> ring
        rw [e3, hsq, mul_one]
    · subst hμ0
      refine ⟨1, ⟨by linarith, hinvge⟩, ?_⟩
      simp [dRidge, kOs, dOs, dOsIntegrand]
  · intro ρ hρ μ hμ
    have hsw := os_sandwich hβ0 hβ1 hNout hNin hB hν0 hmass hcond hqs br hρ hμ
    have hDn := hDnn μ hμ _ (div_nonneg hρ hSγ.le)
    have hDb := lem_app_os_profile_iv (hatNu nuOut (gammaOut Nout B)) hnh0 hr hμ _
      (div_nonneg hρ hSγ.le)
    refine ⟨abs_le.2 ⟨?_, ?_⟩, mul_le_mul_of_nonneg_left hDb hκ0⟩
    · have hm := mul_le_mul_of_nonneg_right hκ2 hDn
      have e : (1 - (lamOs β qs)⁻¹) * dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
          (ρ / (Muon.sPow β 2 * gammaIn Nin B))
          = dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
              (ρ / (Muon.sPow β 2 * gammaIn Nin B))
            - (lamOs β qs)⁻¹ * dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
              (ρ / (Muon.sPow β 2 * gammaIn Nin B)) := by ring
      rw [e] at hm
      linarith [hsw.1]
    · have hm := mul_le_mul_of_nonneg_right hκ1 hDn
      have e : (lamOs β qs - 1) * dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
          (ρ / (Muon.sPow β 2 * gammaIn Nin B))
          = lamOs β qs * dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
              (ρ / (Muon.sPow β 2 * gammaIn Nin B))
            - dOs (hatNu nuOut (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
              (ρ / (Muon.sPow β 2 * gammaIn Nin B)) := by ring
      rw [e] at hm
      linarith [hsw.2]

end

end Muon.Oversampled

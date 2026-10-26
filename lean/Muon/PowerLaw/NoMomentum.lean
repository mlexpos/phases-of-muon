import Muon.PowerLaw.BranchLink
import Muon.PowerLaw.Continuum
import Muon.PowerLaw.DriftAsymptotics
import Muon.Volatility.LagKernel
import Muon.Volatility.Modes
import Muon.External.Certificates

/-!
# Appendix G: no-momentum endpoints (work package L-G.14)

Snapshot `cr-2026-10-23`. Source: `sections/06-power-law/section.tex`, `prop:app-pl-nomomentum-endpoints`
(l.1083–1100) and its defining display `eqn:app-pl-A-alpha` (l.1077–1081). Card: `sections/06-power-law/CARD.md`
§2, §3, §5 (L-G.14), §6 #6.

Representation choices:

* `β = 0` is explicit. It lies outside the standing range `β ∈ (0,1)` (card §6 #6), so every β-dependent
  object is instantiated at `0` (`emaW 0`, `rowVBar … 0`, `dZero0`, `Qm 0`, `Gfun0`). The β-free parts of
  `Muon.PowerLaw` are reused: `gammaOf`, `plSpec`, `c0`, `kappaOf`, `iSharp`, `rowNum`, `partF`, `sN`.
* At `β = 0` the search set of `m(s)` is `(0,1)`, not `(0,γ)`, because `r_0(q) = qJ(q) < 1` (card §6 #6;
  paper l.1102–1105). The β-generic `mOf`, `Gfun`, `dZero` of `Muon.PowerLaw` search `(0,γ)`, where `Qm 0 m`
  is junk for `m ≥ 1`; so the β = 0 instances are the local `mOf0`, `Gfun0`, `dZero0` below.
* `μ_i = i^{-α}` with `c_N = 1` is `plSpec α 1 N`; the row of `i : Fin N` is `rowNum i = i + 1`.
* `κ = Λ_N(1)` is `kappaOf α 1 N B` and `i_# = κ^{1/α}` is `iSharp α 1 N B`.
* The row volatility `𝔳_i(ϱ) = 𝔳_i(ϱ,ϱ)` is `Muon.Volatility.rowVBar` (`eqn:app-vol-rows`) at `Σ_in = Id`,
  so the eigenvalue vector `lam` is `1`. The admissible size constants `(γ⋆, C_Σ)` are explicit hypotheses:
  for this spectrum `SizeFin` reads `N ≤ γ⋆ B` and `opNorm Σ_out = μ_1 = 1 ≤ C_Σ`, and `opNorm Σ_in = 1 ≤ C_Σ`.
  The value of `rowVBar` does not depend on them (`thm:app-vol-mode-kernels`(iv) at `β = 0`).
* Zero-ridge limits are stated as `Tendsto … (𝓝[>] 0) (𝓝 value)`, which asserts existence and value together;
  no `limUnder` is used. `𝔡_i(0)` in part (ii) is the integral `dZero0` (`eqn:app-pl-drift-zero` at `β = 0`); the ϱ↓0 limit
  identification and the integrability of its integrand are stated in `prop_app_pl_nomomentum_endpoints_drift_limit`.
* The constant `A_α` of `eqn:app-pl-A-alpha` is `aAlpha`, defined here (no earlier declaration existed).
  Its integral is parenthesized, and its finiteness (the sentence after the display) is the declaration
  `eqn_app_pl_A_alpha_wf`.
* Asymptotic `∼` is `Asymptotics.IsEquivalent atTop`. Row sequences are `k : (n : ℕ) → Fin (N n)`, with
  dimensions positive (`0 < N n`, `0 < B n`), so that every row sequence exists.
-/

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set Asymptotics
open Muon.DetEquiv

noncomputable section

namespace Muon.PowerLaw

/-- `A_α` of `eqn:app-pl-A-alpha`, snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex` l.1077–1081:

\begin{equation}\label{eqn:app-pl-A-alpha}
A_\alpha\defeq c_0=\sqrt{\frac2\pi}\quad(0<\alpha\le1),\qquad
A_\alpha\defeq\frac{2\alpha}{\pi(\alpha+1)}\int_0^\infty q^{-3/2}\big(q\Jfun(q)\big)^{\frac{\alpha+1}2}\,\dif q\quad(\alpha>1),
\end{equation}
which is finite and positive, since $q\Jfun(q)\le\min(q,1)$ and $\alpha>1$.

The integral is written with `Muon.DetEquiv.J`, which is `F_0 = L_0` at `β = 0`, and `q * J q = r_0(q)`. -/
def aAlpha (α : ℝ) : ℝ :=
  if α ≤ 1 then c0 else
    2 * α / (Real.pi * (α + 1)) *
      (∫ q in Ioi (0 : ℝ), q ^ (-(3 : ℝ) / 2) * (q * J q) ^ ((α + 1) / 2))

/-- `m(s)` at `β = 0`: the solution in `(0,1)` of `s_N(m) = s` (paper l.1102–1105, "with `m(s) ∈ (0,1)`
defined by `s_N(m(s)) = s`"). At `β = 0`, `r_0(q) = qJ(q) < 1`, so `Q_m` exists only for `m < 1`, and the
search set is `(0,1)`, not `(0,γ)` as in the β-generic `Muon.PowerLaw.mOf`. This is the β = 0 instance of
`mOf` restricted to the range of `r_0`. Snapshot `cr-2026-10-23`. -/
def mOf0 (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (s : ℝ) : ℝ :=
  Function.invFunOn (sN 0 B μ) (Ioo 0 1) s

/-- `𝒢_i(s)` at `β = 0`, the β = 0 instance of `Muon.PowerLaw.Gfun` (`eqn:app-pl-finite-constants`) with
`m(s) = mOf0 B μ s` in place of `mOf`, so that `Q_{m(s)}` is the genuine `Q_m` with `m(s) ∈ (0,1)`.
Snapshot `cr-2026-10-23`. -/
def Gfun0 (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (s : ℝ) : ℝ :=
  Lw (emaW 0) (Qm 0 (mOf0 B μ s)) / Fw (emaW 0) (Qm 0 (mOf0 B μ s)) * partF B μ i (mOf0 B μ s)

/-- `𝔡_i(0)` in participation coordinates at `β = 0` (`eqn:app-pl-drift-zero`,
`dZero0 B μ i = (√2/(πγ)) ∫_0^∞ 𝒢_i(u²) du`), the β = 0 instance of `Muon.PowerLaw.dZero` built from
`Gfun0`. Snapshot `cr-2026-10-23`. -/
def dZero0 (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) : ℝ :=
  Real.sqrt 2 / (Real.pi * gammaOf N B) * ∫ u in Ioi (0 : ℝ), Gfun0 B μ i (u ^ 2)

/-- Private helper: `J x ≤ 1/x` for `x > 0` (from `g²/(1+xg²) ≤ 1/x` and `N(0,1)` a probability measure). -/
private lemma nm_J_le_inv {x : ℝ} (hx : 0 < x) : J x ≤ 1 / x := by
  have hmeas : Measurable fun g : ℝ => g ^ 2 / (1 + x * g ^ 2) := by fun_prop
  have hb : ∀ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ≤ 1 / x := by
    intro g
    have hd : 0 < 1 + x * g ^ 2 := by
      have := mul_nonneg hx.le (sq_nonneg g)
      linarith
    rw [div_le_div_iff₀ hd hx]
    nlinarith [sq_nonneg g]
  have hint : Integrable (fun g : ℝ => g ^ 2 / (1 + x * g ^ 2)) (ProbabilityTheory.gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_const (1 / x)) hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun g => ?_)
    rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg g) (by
      have := mul_nonneg hx.le (sq_nonneg g)
      linarith))]
    exact hb g
  unfold J
  calc ∫ g, g ^ 2 / (1 + x * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1) ≤ ∫ _g, 1 / x ∂(ProbabilityTheory.gaussianReal 0 1) :=
        integral_mono hint (integrable_const _) (fun g => hb g)
    _ = 1 / x := by simp

/-- Private helper: the integrand `q^{-3/2} (q J q)^{(α+1)/2}` is strictly positive on `(0,∞)`. -/
private lemma nm_integrand_pos {α q : ℝ} (hq : 0 < q) :
    0 < q ^ (-(3 : ℝ) / 2) * (q * J q) ^ ((α + 1) / 2) :=
  mul_pos (Real.rpow_pos_of_pos hq _)
    (Real.rpow_pos_of_pos (mul_pos hq (lem_app_de_scalar_i.2.2.1 q hq.le).1) _)

/-- Private helper: integrability of the `α > 1` integrand on `(0,∞)`, split at `q = 1`. Near `0`
the integrand is dominated by `q^{(α-2)/2}` (integrable since `α > 0`); on `(1,∞)` by `q^{-3/2}`,
using `q J q ≤ 1`. -/
private lemma nm_integrand_integrable {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun q : ℝ => q ^ (-(3 : ℝ) / 2) * (q * J q) ^ ((α + 1) / 2)) (Ioi 0) := by
  have hβ : (0 : ℝ) ≤ (α + 1) / 2 := by linarith
  have hJc : ContinuousOn J (Ici 0) := lem_app_de_scalar_i.1
  have hc1 : ContinuousOn (fun q : ℝ => q ^ (-(3 : ℝ) / 2)) (Ioi 0) :=
    continuousOn_id.rpow_const (fun _ hx => Or.inl (Set.mem_Ioi.mp hx).ne')
  have hc2 : ContinuousOn (fun q : ℝ => (q * J q) ^ ((α + 1) / 2)) (Ioi 0) :=
    (continuousOn_id.mul (hJc.mono Ioi_subset_Ici_self)).rpow_const (fun _ _ => Or.inr hβ)
  have hcont : ContinuousOn (fun q : ℝ => q ^ (-(3 : ℝ) / 2) * (q * J q) ^ ((α + 1) / 2)) (Ioi 0) :=
    hc1.mul hc2
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  refine IntegrableOn.union ?_ ?_
  · have hmeas : AEStronglyMeasurable (fun q : ℝ => q ^ (-(3 : ℝ) / 2) * (q * J q) ^ ((α + 1) / 2))
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      (hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    have hint : IntegrableOn (fun q : ℝ => q ^ ((α - 2) / 2)) (Ioc (0 : ℝ) 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 (by linarith)
    refine Integrable.mono' hint hmeas ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun q hq => ?_)
    have hq0 : 0 < q := hq.1
    have hq1 : q ≤ 1 := hq.2
    change ‖q ^ (-(3 : ℝ) / 2) * (q * J q) ^ ((α + 1) / 2)‖ ≤ q ^ ((α - 2) / 2)
    have hJb := lem_app_de_scalar_i.2.2.1 q hq0.le
    have hJ0 : 0 ≤ J q := hJb.1.le
    have hJ1 : J q ≤ 1 := hJb.2
    have hqJ0 : 0 ≤ q * J q := mul_nonneg hq0.le hJ0
    have hqJ : q * J q ≤ q := by
      nlinarith [mul_le_mul_of_nonneg_left hJ1 hq0.le]
    have hpow : (q * J q) ^ ((α + 1) / 2) ≤ q ^ ((α + 1) / 2) :=
      Real.rpow_le_rpow hqJ0 hqJ hβ
    have hnn : 0 ≤ q ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg hq0.le _
    have heq : q ^ (-(3 : ℝ) / 2) * q ^ ((α + 1) / 2) = q ^ ((α - 2) / 2) := by
      rw [← Real.rpow_add hq0]
      congr 1
      ring
    rw [Real.norm_of_nonneg (mul_nonneg hnn (Real.rpow_nonneg hqJ0 _))]
    calc q ^ (-(3 : ℝ) / 2) * (q * J q) ^ ((α + 1) / 2)
        ≤ q ^ (-(3 : ℝ) / 2) * q ^ ((α + 1) / 2) := mul_le_mul_of_nonneg_left hpow hnn
      _ = q ^ ((α - 2) / 2) := heq
  · have hmeas : AEStronglyMeasurable (fun q : ℝ => q ^ (-(3 : ℝ) / 2) * (q * J q) ^ ((α + 1) / 2))
        (volume.restrict (Ioi (1 : ℝ))) :=
      (hcont.mono (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))).aestronglyMeasurable measurableSet_Ioi
    have hint : IntegrableOn (fun q : ℝ => q ^ (-(3 : ℝ) / 2)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 : ℝ) / 2) < -1) one_pos
    refine Integrable.mono' hint hmeas ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun q hq => ?_)
    have hq1 : 1 < q := hq
    have hq0 : 0 < q := by linarith
    change ‖q ^ (-(3 : ℝ) / 2) * (q * J q) ^ ((α + 1) / 2)‖ ≤ q ^ (-(3 : ℝ) / 2)
    have hqJ : q * J q ≤ 1 := by
      calc q * J q ≤ q * (1 / q) := mul_le_mul_of_nonneg_left (nm_J_le_inv hq0) hq0.le
        _ = 1 := mul_one_div_cancel hq0.ne'
    have hqJ0 : 0 ≤ q * J q := (mul_pos hq0 (lem_app_de_scalar_i.2.2.1 q hq0.le).1).le
    have hpow : (q * J q) ^ ((α + 1) / 2) ≤ 1 := Real.rpow_le_one hqJ0 hqJ hβ
    have hnn : 0 ≤ q ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg hq0.le _
    rw [Real.norm_of_nonneg (mul_nonneg hnn (Real.rpow_nonneg hqJ0 _))]
    calc q ^ (-(3 : ℝ) / 2) * (q * J q) ^ ((α + 1) / 2)
        ≤ q ^ (-(3 : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left hpow hnn
      _ = q ^ (-(3 : ℝ) / 2) := mul_one _

/-- Finiteness and positivity of `A_α` (`eqn:app-pl-A-alpha`, the sentence after the display; snapshot
`cr-2026-10-23`). LaTeX, verbatim from `section.tex` l.1077–1081:

\begin{equation}\label{eqn:app-pl-A-alpha}
A_\alpha\defeq c_0=\sqrt{\frac2\pi}\quad(0<\alpha\le1),\qquad
A_\alpha\defeq\frac{2\alpha}{\pi(\alpha+1)}\int_0^\infty q^{-3/2}\big(q\Jfun(q)\big)^{\frac{\alpha+1}2}\,\dif q\quad(\alpha>1),
\end{equation}
which is finite and positive, since $q\Jfun(q)\le\min(q,1)$ and $\alpha>1$.

The integrability for `α > 1` is the claim "which is finite … since `q J(q) ≤ min(q,1)`". -/
theorem eqn_app_pl_A_alpha_wf {α : ℝ} (hα : 0 < α) :
    0 < aAlpha α ∧
      (1 < α → IntegrableOn (fun q : ℝ => q ^ (-(3 : ℝ) / 2) * (q * J q) ^ ((α + 1) / 2)) (Ioi 0)) := by
  refine ⟨?_, fun _ => nm_integrand_integrable hα⟩
  unfold aAlpha
  split_ifs with h
  · unfold c0
    exact Real.sqrt_pos.2 (div_pos two_pos Real.pi_pos)
  · apply mul_pos
    · exact div_pos (mul_pos two_pos hα) (mul_pos Real.pi_pos (by linarith))
    · have hint := nm_integrand_integrable hα
      have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
          (fun q : ℝ => q ^ (-(3 : ℝ) / 2) * (q * J q) ^ ((α + 1) / 2)) :=
        ae_restrict_of_forall_mem measurableSet_Ioi (fun q hq => (nm_integrand_pos (α := α) hq).le)
      rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
      have hpos : (0 : ENNReal) < volume (Ioi (0 : ℝ)) := by
        rw [Real.volume_Ioi]
        exact ENNReal.zero_lt_top
      exact lt_of_lt_of_le hpos (measure_mono (fun q hq =>
        ⟨Function.mem_support.2 (nm_integrand_pos (α := α) hq).ne', hq⟩))

private lemma nm_dimensions {N B : ℕ} (hγ : 1 < gammaOf N B) : 0 < N ∧ 0 < B := by
  have hB : B ≠ 0 := by
    intro h
    norm_num [gammaOf, h] at hγ
  have hN : N ≠ 0 := by
    intro h
    norm_num [gammaOf, h] at hγ
  exact ⟨Nat.pos_of_ne_zero hN, Nat.pos_of_ne_zero hB⟩

private lemma nm_endpoint_profile {α : ℝ} (hα : 0 < α) {N B : ℕ}
    (hγ : 1 < gammaOf N B) (i : Fin N) :
    kappaOf α 1 N B * plSpec α 1 N i / (1 + kappaOf α 1 N B * plSpec α 1 N i) =
      1 / (1 + (rowNum i / iSharp α 1 N B) ^ α) := by
  obtain ⟨hN, hB⟩ := nm_dimensions hγ
  have hκ : 0 < kappaOf α 1 N B :=
    (prop_app_pl_scales_i 1 hα hN hB zero_lt_one hγ).1
  have hr : 0 < rowNum i := by unfold rowNum; positivity
  have hrα : 0 < rowNum i ^ α := Real.rpow_pos_of_pos hr _
  have hs : 0 < iSharp α 1 N B := by
    unfold iSharp
    exact Real.rpow_pos_of_pos (by simpa using hκ) _
  have hsα : iSharp α 1 N B ^ α = kappaOf α 1 N B := by
    unfold iSharp
    rw [one_mul, one_div, Real.rpow_inv_rpow hκ.le hα.ne']
  have hμ : plSpec α 1 N i = (rowNum i ^ α)⁻¹ := by
    simp only [plSpec, one_mul, rowNum, Real.rpow_neg (by positivity : (0 : ℝ) ≤ (i : ℕ) + 1)]
  rw [Real.div_rpow hr.le hs.le, hsα, hμ]
  have hd : 1 + kappaOf α 1 N B * (rowNum i ^ α)⁻¹ ≠ 0 := by positivity
  have hd' : 1 + rowNum i ^ α / kappaOf α 1 N B ≠ 0 := by positivity
  field_simp
  ring

private lemma nm_endpoint_sum {α : ℝ} (hα : 0 < α) {N B : ℕ}
    (hγ : 1 < gammaOf N B) :
    ∑ i : Fin N, kappaOf α 1 N B * plSpec α 1 N i /
      (1 + kappaOf α 1 N B * plSpec α 1 N i) = (B : ℝ) := by
  obtain ⟨hN, hB⟩ := nm_dimensions hγ
  exact (prop_app_pl_scales_i 1 hα hN hB zero_lt_one hγ).2.1

/-- The row coordinate used in the endpoint statement is exactly the reciprocal
of the dimensionless row mass, after taking the `α`-th power. -/
private lemma nm_row_scale_identity {α : ℝ} (hα : 0 < α) {N B : ℕ}
    (hγ : 1 < gammaOf N B) (i : Fin N) :
    (rowNum i / iSharp α 1 N B) ^ α =
      1 / (kappaOf α 1 N B * plSpec α 1 N i) := by
  obtain ⟨hN, hB⟩ := nm_dimensions hγ
  have hκ : 0 < kappaOf α 1 N B :=
    (prop_app_pl_scales_i 1 hα hN hB zero_lt_one hγ).1
  have hr : 0 < rowNum i := by unfold rowNum; positivity
  have hs : 0 < iSharp α 1 N B := by
    unfold iSharp
    exact Real.rpow_pos_of_pos (by simpa using hκ) _
  have hsα : iSharp α 1 N B ^ α = kappaOf α 1 N B := by
    unfold iSharp
    rw [one_mul, one_div, Real.rpow_inv_rpow hκ.le hα.ne']
  have hμ : plSpec α 1 N i = (rowNum i ^ α)⁻¹ := by
    simp only [plSpec, one_mul, rowNum, Real.rpow_neg
      (by positivity : (0 : ℝ) ≤ (i : ℕ) + 1)]
  rw [Real.div_rpow hr.le hs.le, hsα, hμ]
  field_simp

private lemma nm_row_coordinate_pos {α : ℝ} (hα : 0 < α) {N B : ℕ}
    (hγ : 1 < gammaOf N B) (i : Fin N) :
    0 < rowNum i / iSharp α 1 N B := by
  obtain ⟨hN, hB⟩ := nm_dimensions hγ
  have hκ : 0 < kappaOf α 1 N B :=
    (prop_app_pl_scales_i 1 hα hN hB zero_lt_one hγ).1
  exact div_pos (by unfold rowNum; positivity) (by
    unfold iSharp
    exact Real.rpow_pos_of_pos (by simpa using hκ) _)

/-- The resolved-row hypothesis is equivalently divergence of the dimensionless row mass. -/
private lemma nm_row_mass_atTop {α : ℝ} (hα : 0 < α)
    (N B : ℕ → ℕ) (hγ : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop)
    (k : (n : ℕ) → Fin (N n))
    (hrow : Tendsto (fun n => rowNum (k n) / iSharp α 1 (N n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => kappaOf α 1 (N n) (B n) * plSpec α 1 (N n) (k n))
      atTop atTop := by
  have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) := hγ.eventually_gt_atTop 1
  have hpow : Tendsto
      (fun n => (rowNum (k n) / iSharp α 1 (N n) (B n)) ^ α) atTop (𝓝 0) := by
    have ht := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp hrow
    rw [Real.zero_rpow hα.ne'] at ht
    exact ht.congr' (Eventually.of_forall fun _ => rfl)
  have hpowWithin : Tendsto
      (fun n => (rowNum (k n) / iSharp α 1 (N n) (B n)) ^ α)
      atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hpow, by
      filter_upwards [hγ1] with n hn
      exact Real.rpow_pos_of_pos (nm_row_coordinate_pos hα hn (k n)) α⟩
  refine hpowWithin.inv_tendsto_nhdsGT_zero.congr' ?_
  filter_upwards [hγ1] with n hn
  dsimp only [Pi.inv_apply]
  rw [nm_row_scale_identity hα hn (k n)]
  simp only [one_div, inv_inv]

/-- The unresolved-row hypothesis is equivalently vanishing of the dimensionless row mass. -/
private lemma nm_row_mass_zero {α : ℝ} (hα : 0 < α)
    (N B : ℕ → ℕ) (hγ : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop)
    (k : (n : ℕ) → Fin (N n))
    (hrow : Tendsto (fun n => rowNum (k n) / iSharp α 1 (N n) (B n)) atTop atTop) :
    Tendsto (fun n => kappaOf α 1 (N n) (B n) * plSpec α 1 (N n) (k n))
      atTop (𝓝 0) := by
  have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) := hγ.eventually_gt_atTop 1
  have hpow : Tendsto
      (fun n => (rowNum (k n) / iSharp α 1 (N n) (B n)) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp hrow
  refine (tendsto_inv_atTop_zero.comp hpow).congr' ?_
  filter_upwards [hγ1] with n hn
  dsimp only [Function.comp_apply]
  rw [nm_row_scale_identity hα hn (k n)]
  simp only [one_div, inv_inv]

private lemma nm_partF_endpoint_limit {α : ℝ} {N B : ℕ}
    (hγ : 1 < gammaOf N B) (i : Fin N) :
    Tendsto (partF B (plSpec α 1 N) i) (𝓝 1)
      (𝓝 (kappaOf α 1 N B * plSpec α 1 N i /
        (1 + kappaOf α 1 N B * plSpec α 1 N i))) := by
  obtain ⟨hN, hB⟩ := nm_dimensions hγ
  have hpos : ∀ j : Fin N, 0 < plSpec α 1 N j := by
    intro j
    unfold plSpec
    positivity
  have hLam : ContinuousAt (partLam B (plSpec α 1 N)) 1 :=
    (def_app_pl_participation_bij (plSpec α 1 N) hB hN hpos).2.2.2.continuousOn.continuousAt
      (isOpen_Ioo.mem_nhds ⟨zero_lt_one, hγ⟩)
  have hκ : 0 < kappaOf α 1 N B :=
    (def_app_pl_participation_bij (plSpec α 1 N) hB hN hpos).2.1.mapsTo ⟨zero_lt_one, hγ⟩
  have hμ : 0 < plSpec α 1 N i := hpos i
  have hd : 1 + kappaOf α 1 N B * plSpec α 1 N i ≠ 0 := by positivity
  exact (hLam.tendsto.mul_const _).div (tendsto_const_nhds.add (hLam.tendsto.mul_const _)) hd

private lemma nm_wseq : WeightSeq (emaW 0) := by
  refine ⟨fun j => by simp [emaW], ?_, ⟨0, by simp [emaW]⟩⟩
  have h : emaW 0 = fun j : ℕ => if j = 0 then (1 : ℝ) else 0 := by
    funext j
    by_cases hj : j = 0 <;> simp [emaW, hj]
  rw [h]
  exact (hasSum_ite_eq 0 (1 : ℝ)).summable

private lemma nm_Fw (q : ℝ) : Fw (emaW 0) q = J q := by
  unfold Fw
  rw [tsum_eq_single 0]
  · simp [emaW]
  · intro j hj
    simp [emaW, hj]

private lemma nm_rW_limit : Tendsto (rW (emaW 0)) atTop (𝓝 (1 : ℝ)) := by
  have h := (lem_app_de_scalar_iii nm_wseq).2.2.2.2.2.2
  have he : {j : ℕ | 0 < emaW 0 j} = {0} := by
    ext j
    by_cases hj : j = 0 <;> simp [emaW, hj]
  rw [he] at h
  simp only [Set.encard_singleton, ENat.toENNReal_one] at h
  have ht := (ENNReal.continuousAt_toReal (by simp : (1 : ENNReal) ≠ ⊤)).tendsto.comp h
  simp only [ENNReal.toReal_one] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
  dsimp only [Function.comp_def]
  rw [ENNReal.toReal_ofReal]
  unfold rW
  rw [nm_Fw]
  exact mul_nonneg hq (lem_app_de_scalar_i.2.2.1 q hq).1.le

private lemma nm_Qm_spec {m : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1) :
    0 < Qm 0 m ∧ rW (emaW 0) (Qm 0 m) = m := by
  have hcont : ContinuousOn (rW (emaW 0)) (Ici 0) :=
    continuousOn_id.mul (lem_app_de_scalar_ii nm_wseq).2.2.1
  obtain ⟨b, hb, hb0⟩ := ((nm_rW_limit.eventually_const_lt hm.2).and
    (eventually_gt_atTop (0 : ℝ))).exists
  have hr0 := (lem_app_de_scalar_iii nm_wseq).2.2.1
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hb0.le
    (hcont.mono Icc_subset_Ici_self) (show m ∈ Icc (rW (emaW 0) 0) (rW (emaW 0) b) from
      ⟨by rw [hr0]; exact hm.1.le, hb.le⟩)
  have hx0 : 0 < x := by
    rcases hx.1.eq_or_lt with h | h
    · rw [← h, hr0] at hfx
      linarith [hm.1]
    · exact h
  have hex : ∃ a ∈ Ioi (0 : ℝ), rW (emaW 0) a = m := ⟨x, hx0, hfx⟩
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

private lemma nm_rW_mem {q : ℝ} (hq : 0 < q) : rW (emaW 0) q ∈ Ioo (0 : ℝ) 1 := by
  have hmono := (lem_app_de_scalar_iii nm_wseq).2.1
  have h0 := (lem_app_de_scalar_iii nm_wseq).2.2.1
  refine ⟨by simpa only [h0] using hmono (by simp) hq.le hq, ?_⟩
  have hle : rW (emaW 0) (q + 1) ≤ 1 := by
    apply ge_of_tendsto nm_rW_limit
    filter_upwards [eventually_ge_atTop (q + 1)] with x hx
    exact hmono.monotoneOn (show 0 ≤ q + 1 by linarith) (show 0 ≤ x by linarith) hx
  exact (hmono hq.le (show 0 ≤ q + 1 by linarith) (show q < q + 1 by linarith)).trans_le hle

private lemma nm_Qm_mono : StrictMonoOn (Qm 0) (Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  obtain ⟨hqa, hea⟩ := nm_Qm_spec ha
  obtain ⟨hqb, heb⟩ := nm_Qm_spec hb
  exact ((lem_app_de_scalar_iii nm_wseq).2.1.lt_iff_lt hqa.le hqb.le).1 (by simpa [hea, heb])

private lemma nm_Qm_rW {q : ℝ} (hq : 0 < q) : Qm 0 (rW (emaW 0) q) = q := by
  obtain ⟨hp, he⟩ := nm_Qm_spec (nm_rW_mem hq)
  exact (lem_app_de_scalar_iii nm_wseq).2.1.injOn hp.le hq.le he

private lemma nm_Qm_cont : ContinuousOn (Qm 0) (Ioo (0 : ℝ) 1) := by
  intro a ha
  apply ContinuousAt.continuousWithinAt
  have himg : Qm 0 '' Ioo (0 : ℝ) 1 = Ioi 0 := by
    ext q
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact (nm_Qm_spec hm).1
    · intro hq
      exact ⟨rW (emaW 0) q, nm_rW_mem hq, nm_Qm_rW hq⟩
  refine continuousAt_of_monotoneOn_of_image_mem_nhds nm_Qm_mono.monotoneOn
    (Ioo_mem_nhds ha.1 ha.2) ?_
  rw [himg]
  exact Ioi_mem_nhds (nm_Qm_spec ha).1

private lemma nm_Qm_one : Tendsto (Qm 0) (𝓝[<] (1 : ℝ)) atTop := by
  refine tendsto_atTop.2 fun a => ?_
  let q := max a 0 + 1
  have hq : 0 < q := by dsimp [q]; positivity
  have hr := nm_rW_mem hq
  filter_upwards [Ioo_mem_nhdsLT hr.2] with m hm
  have hm0 : m ∈ Ioo (0 : ℝ) 1 := ⟨hr.1.trans hm.1, hm.2⟩
  have h := nm_Qm_mono hr hm0 hm.1
  rw [nm_Qm_rW hq] at h
  exact (le_max_left a 0).trans (by dsimp [q] at h; linarith)

private lemma nm_sN_alt {N B : ℕ} (μ : Fin N → ℝ) {m : ℝ}
    (hm : m ∈ Ioo (0 : ℝ) 1) :
    sN 0 B μ m = (gammaOf N B - m) * J (Qm 0 m) / partLam B μ m := by
  have he := (nm_Qm_spec hm).2
  change Qm 0 m * Fw (emaW 0) (Qm 0 m) = m at he
  rw [nm_Fw] at he
  unfold sN
  have hediv : m / Qm 0 m = J (Qm 0 m) := by
    exact (eq_div_of_mul_eq (nm_Qm_spec hm).1.ne' (by nlinarith [he])).symm
  rw [div_mul_eq_div_div, mul_div_assoc, hediv]

private lemma nm_sN_pos {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) {m : ℝ}
    (hm : m ∈ Ioo (0 : ℝ) 1) : 0 < sN 0 B μ m := by
  unfold sN
  exact div_pos (mul_pos (sub_pos.2 (hm.2.trans hγ)) hm.1)
    (mul_pos (nm_Qm_spec hm).1
      ((def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo ⟨hm.1, hm.2.trans hγ⟩))

private lemma nm_sN_anti {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) :
    StrictAntiOn (sN 0 B μ) (Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hL := def_app_pl_participation_bij μ hB hN hpos
  have ha' : a ∈ Ioo 0 (gammaOf N B) := ⟨ha.1, ha.2.trans hγ⟩
  have hb' : b ∈ Ioo 0 (gammaOf N B) := ⟨hb.1, hb.2.trans hγ⟩
  have hLa : 0 < partLam B μ a := hL.2.1.mapsTo ha'
  have hLb : 0 < partLam B μ b := hL.2.1.mapsTo hb'
  have hJ := lem_app_de_scalar_i.2.1 (nm_Qm_spec ha).1.le (nm_Qm_spec hb).1.le
    (nm_Qm_mono ha hb hab)
  have hJb := (lem_app_de_scalar_i.2.2.1 _ (nm_Qm_spec hb).1.le).1
  rw [nm_sN_alt μ ha, nm_sN_alt μ hb]
  calc
    (gammaOf N B - b) * J (Qm 0 b) / partLam B μ b
        < (gammaOf N B - a) * J (Qm 0 a) / partLam B μ b := by
      apply div_lt_div_of_pos_right _ hLb
      exact mul_lt_mul (by linarith) hJ.le hJb (by linarith [ha.2])
    _ ≤ (gammaOf N B - a) * J (Qm 0 a) / partLam B μ a :=
      div_le_div_of_nonneg_left
        (mul_nonneg (by linarith [ha.2]) (hJb.le.trans hJ.le)) hLa (hL.2.2.1 ha' hb' hab).le

private lemma nm_sN_cont {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) :
    ContinuousOn (sN 0 B μ) (Ioo (0 : ℝ) 1) := by
  have hL := def_app_pl_participation_bij μ hB hN hpos
  unfold sN
  refine ((continuousOn_const.sub continuousOn_id).mul continuousOn_id).div
    (nm_Qm_cont.mul (hL.2.2.2.continuousOn.mono (fun m hm => ⟨hm.1, hm.2.trans hγ⟩))) ?_
  intro m hm
  exact mul_ne_zero (nm_Qm_spec hm).1.ne'
    (hL.2.1.mapsTo ⟨hm.1, hm.2.trans hγ⟩).ne'

private lemma nm_sN_large {N B : ℕ} (μ : Fin N → ℝ)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) (K : ℝ) :
    ∀ᶠ m in 𝓝[>] (0:ℝ), K < sN (0 : ℝ) B μ m := by
  have hγ : 0 < gammaOf N B := div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  have hbij := def_app_pl_participation_bij μ hB hN hpos
  have hs2 : 0 < sPow 0 2 := by norm_num [sPow_eq (β := 0) le_rfl zero_lt_one (by norm_num : 2 ≤ (2 : ℕ))]
  obtain ⟨c, hc⟩ := (lem_app_pl_weights_i_Q (β := 0) le_rfl zero_lt_one).isBigO.bound
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = |c| / sPow (0 : ℝ) 2 + 1 := ⟨_, rfl⟩
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hQC : ∀ᶠ m in 𝓝[>] (0:ℝ), Qm (0 : ℝ) m ≤ C * m := by
    filter_upwards [hc, Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with m hm hm0
    have hm0' : 0 < m := hm0.1
    have hQ := (nm_Qm_spec hm0).1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hQ,
      abs_of_pos (div_pos hm0' hs2)] at hm
    have h1 : c * (m / sPow (0 : ℝ) 2) ≤ |c| * (m / sPow (0 : ℝ) 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self c) (div_pos hm0' hs2).le
    have h2 : |c| * (m / sPow (0 : ℝ) 2) = |c| / sPow (0 : ℝ) 2 * m := by ring
    have h3 : |c| / sPow (0 : ℝ) 2 * m ≤ C * m := by
      rw [hCdef, add_mul, one_mul]
      linarith
    linarith
  obtain ⟨K', hK'def⟩ : ∃ K' : ℝ, K' = |K| + 1 := ⟨_, rfl⟩
  have hK'pos : 0 < K' := by rw [hK'def]; positivity
  have hKK' : K ≤ K' := by rw [hK'def]; linarith [le_abs_self K]
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = gammaOf N B / (2 * C * K') := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hΛsmall : ∀ᶠ m in 𝓝[>] (0 : ℝ), partLam B μ m < ε := by
    have hεmem := hbij.1.mapsTo hε
    filter_upwards [Ioo_mem_nhdsGT hεmem.1] with m hm
    have hmγ : m ∈ Ioo 0 (gammaOf N B) := ⟨hm.1, hm.2.trans hεmem.2⟩
    have hlt := hbij.2.2.1 hmγ hεmem hm.2
    have he : partLam B μ (partMN B μ ε) = ε := hbij.1.invOn_invFunOn.1 hε
    rw [he] at hlt
    exact hlt
  filter_upwards [hQC, hΛsmall, Ioo_mem_nhdsGT (half_pos hγ),
    Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with m hQle hΛε hmh hm1
  have hm0 : 0 < m := hmh.1
  have hmγ2 : m < gammaOf N B / 2 := hmh.2
  have hQ := (nm_Qm_spec hm1).1
  have hΛ := hbij.2.1.mapsTo ⟨hm0, by linarith⟩
  have hΛ' : 0 < partLam B μ m := hΛ
  unfold sN
  rw [lt_div_iff₀ (mul_pos hQ hΛ')]
  have hA : K * (Qm (0 : ℝ) m * partLam B μ m) ≤ K' * (Qm (0 : ℝ) m * partLam B μ m) :=
    mul_le_mul_of_nonneg_right hKK' (mul_pos hQ hΛ').le
  have hB' : K' * (Qm (0 : ℝ) m * partLam B μ m) ≤ K' * (C * m * partLam B μ m) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQle hΛ'.le) hK'pos.le
  have hC' : K' * (C * m * partLam B μ m) ≤ K' * (C * m * ε) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΛε.le (by positivity)) hK'pos.le
  have hD' : K' * (C * m * ε) = m * gammaOf N B / 2 := by
    rw [hεdef]
    field_simp
  have hE' : m * gammaOf N B / 2 < (gammaOf N B - m) * m := by
    have : 0 < m * (gammaOf N B / 2 - m) := mul_pos hm0 (by linarith)
    nlinarith [this]
  linarith [hA, hB', hC', hD', hE']

private lemma nm_sN_one {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) :
    Tendsto (sN 0 B μ) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hbij := def_app_pl_participation_bij μ hB hN hpos
  have hL : ContinuousAt (partLam B μ) 1 := hbij.2.2.2.continuousOn.continuousAt
    (Ioo_mem_nhds zero_lt_one hγ)
  have hLp : 0 < partLam B μ 1 := hbij.2.1.mapsTo ⟨zero_lt_one, hγ⟩
  have hid : Tendsto (fun m : ℝ => m) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun m : ℝ => (gammaOf N B - m) * m / partLam B μ m)
      (𝓝[<] (1 : ℝ)) (𝓝 ((gammaOf N B - 1) * 1 / partLam B μ 1)) :=
    ((tendsto_const_nhds.sub hid).mul hid).div
      (hL.tendsto.mono_left nhdsWithin_le_nhds) hLp.ne'
  have hi := tendsto_inv_atTop_zero.comp nm_Qm_one
  have hf := ht.mul hi
  simpa only [mul_zero] using hf.congr (fun m => by
    change (gammaOf N B - m) * m / partLam B μ m * (Qm 0 m)⁻¹ = sN 0 B μ m
    unfold sN
    ring)

private lemma nm_mOf0_spec {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) {s : ℝ} (hs : 0 < s) :
    mOf0 B μ s ∈ Ioo (0 : ℝ) 1 ∧ sN 0 B μ (mOf0 B μ s) = s := by
  obtain ⟨a, ha, hsa⟩ := ((nm_sN_large μ hB hN hpos s).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num))).exists
  obtain ⟨b, hb, hsb⟩ := ((nm_sN_one μ hB hN hpos hγ).eventually_lt_const hs |>.and
    (Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num))).exists
  have hab : a ≤ b := by linarith [hsa.2, hsb.1]
  obtain ⟨x, hx, he⟩ := intermediate_value_Icc' hab
    ((nm_sN_cont μ hB hN hpos hγ).mono (fun t ht => ⟨hsa.1.trans_le ht.1, ht.2.trans_lt hsb.2⟩))
    (show s ∈ Icc (sN 0 B μ b) (sN 0 B μ a) from ⟨hb.le, ha.le⟩)
  have hex : ∃ x ∈ Ioo (0 : ℝ) 1, sN 0 B μ x = s :=
    ⟨x, ⟨hsa.1.trans_le hx.1, hx.2.trans_lt hsb.2⟩, he⟩
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

private lemma nm_mOf0_limit {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) :
    Tendsto (mOf0 B μ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    rcases le_or_gt a 0 with h0 | h0
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact h0.trans_lt (nm_mOf0_spec μ hB hN hpos hγ hs).1.1
    · filter_upwards [Ioo_mem_nhdsGT (nm_sN_pos μ hB hN hpos hγ ⟨h0, ha⟩)] with s hs
      obtain ⟨hm, he⟩ := nm_mOf0_spec μ hB hN hpos hγ hs.1
      by_contra h
      have hle := (nm_sN_anti μ hB hN hpos hγ).antitoneOn hm ⟨h0, ha⟩ (not_lt.mp h)
      rw [he] at hle
      exact (not_le_of_gt hs.2) hle
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (nm_mOf0_spec μ hB hN hpos hγ hs).1.2.trans ha

private lemma nm_enorm_lt {x : ℝ} : ‖x‖ₑ < ⊤ := by
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_lt_top

private lemma nm_int_dirac_sum {N B : ℕ} (μ : Fin N → ℝ) (f : ℝ → ℝ) :
    ∫ t, f t ∂(ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i)) =
      (B : ℝ)⁻¹ * ∑ i, f (μ i) := by
  rw [integral_smul_measure, integral_finsetSum_measure (fun i _ => integrable_dirac nm_enorm_lt)]
  simp only [integral_dirac, ENNReal.toReal_ofReal (inv_nonneg.2 (Nat.cast_nonneg B)), smul_eq_mul]

/-- Auxiliary for the branch identity: the integral against `γ δ_1`. -/
private lemma nm_int_dirac_one (γ : ℝ) (hγ : 0 ≤ γ) (f : ℝ → ℝ) :
    ∫ t, f t ∂(ENNReal.ofReal γ • Measure.dirac (1 : ℝ)) = γ * f 1 := by
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hγ, smul_eq_mul]

private lemma nm_dirac_Icc_compl {a Cs : ℝ} (h : a ∈ Icc (0:ℝ) Cs) :
    Measure.dirac a (Icc 0 Cs)ᶜ = 0 := by
  rw [Measure.dirac_apply' _ measurableSet_Icc.compl]
  exact Set.indicator_of_notMem (show a ∉ (Icc (0:ℝ) Cs)ᶜ from fun hh => hh h) _


private lemma nm_branch {N B : ℕ} (μ : Fin N → ℝ)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i)
    {ν ν' : FiniteMeasure ℝ} {Cs : ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (hμCs : ∀ i, μ i ≤ Cs) (h1Cs : 1 ≤ Cs) (hγ1 : 1 < gammaOf N B)
    {s m : ℝ} (hs : 0 < s) (hm : m ∈ Ioo (0 : ℝ) 1) (hsm : sN (0 : ℝ) B μ m = s) :
    s * (branchSol (Fw (emaW (0 : ℝ))) ν ν' s).1 * (branchSol (Fw (emaW (0 : ℝ))) ν ν' s).2.1 = Qm (0 : ℝ) m ∧
      (branchSol (Fw (emaW (0 : ℝ))) ν ν' s).2.2.1 = s * partLam B μ m ∧
      (branchSol (Fw (emaW (0 : ℝ))) ν ν' s).2.2.2 = s * m / (gammaOf N B - m) ∧
      (branchSol (Fw (emaW (0 : ℝ))) ν ν' s).1 = m / (s * partLam B μ m) ∧
      (branchSol (Fw (emaW (0 : ℝ))) ν ν' s).2.1 = (gammaOf N B - m) / s ∧
      ∀ i : Fin N,
        (branchSol (Fw (emaW (0 : ℝ))) ν ν' s).2.2.1 * μ i /
            (s + (branchSol (Fw (emaW (0 : ℝ))) ν ν' s).2.2.1 * μ i) = partF B μ i m := by
  have hγ : 0 < gammaOf N B := by
    exact div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  have hC : 0 < Cs := lt_of_lt_of_le one_pos h1Cs
  have hw := nm_wseq
  have hmFull : m ∈ Ioo 0 (gammaOf N B) := ⟨hm.1, hm.2.trans hγ1⟩
  have hmγ : 0 < gammaOf N B - m := sub_pos.2 hmFull.2
  have hmγne : gammaOf N B - m ≠ 0 := hmγ.ne'
  have hγne : gammaOf N B ≠ 0 := hγ.ne'
  have hsne : s ≠ 0 := hs.ne'
  obtain ⟨hQ, hrQ⟩ := nm_Qm_spec hm
  have hFQ : Fw (emaW (0 : ℝ)) (Qm (0 : ℝ) m) = m / Qm (0 : ℝ) m := by
    have h' : Qm (0 : ℝ) m * Fw (emaW (0 : ℝ)) (Qm (0 : ℝ) m) = m := hrQ
    exact eq_div_of_mul_eq hQ.ne' (by rw [mul_comm]; exact h')
  obtain ⟨hbMN, hbLam, -, -⟩ := def_app_pl_participation_bij μ hB hN hpos
  have hL : 0 < partLam B μ m := hbLam.mapsTo hmFull
  have hMN : partMN B μ (partLam B μ m) = m := hbMN.invOn_invFunOn.2 hmFull
  have hkey : s * (Qm (0 : ℝ) m * partLam B μ m) = (gammaOf N B - m) * m := by
    have h := hsm
    unfold sN at h
    rw [← h]
    exact div_mul_cancel₀ _ (mul_ne_zero hQ.ne' hL.ne')
  set Q := Qm (0 : ℝ) m with hQdef
  set L := partLam B μ m with hLdef
  have hLne : L ≠ 0 := hL.ne'
  have hμ1 : ∀ i, 0 < 1 + L * μ i := fun i => by
    have := mul_pos hL (hpos i); linarith
  have hq : s * (m / (s * L)) * ((gammaOf N B - m) / s) = Q := by
    field_simp
    linear_combination -hkey
  have hclass : (ν, ν') ∈ classK Cs (gammaOf N B) := by
    have hd : ∀ i, Measure.dirac (μ i) (Icc 0 Cs) = 1 := fun i =>
      Measure.dirac_apply_of_mem ⟨(hpos i).le, hμCs i⟩
    have hdc : ∀ i, Measure.dirac (μ i) (Icc 0 Cs)ᶜ = 0 := fun i =>
      nm_dirac_Icc_compl ⟨(hpos i).le, hμCs i⟩
    have h1mem : (1 : ℝ) ∈ Icc (0:ℝ) Cs := ⟨zero_le_one, h1Cs⟩
    simp only [classK, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hν]
      simp only [Measure.smul_apply, Measure.finsetSum_apply, hd, smul_eq_mul,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg B))]
      apply le_of_eq
      congr 1
      unfold gammaOf
      ring
    · rw [hν]
      simp only [Measure.smul_apply, Measure.finsetSum_apply, hdc, smul_eq_mul,
        Finset.sum_const_zero, mul_zero]
    · rw [hν']
      simp only [Measure.smul_apply, Measure.dirac_apply_of_mem h1mem, smul_eq_mul, mul_one]
      exact le_rfl
    · rw [hν', Measure.smul_apply, nm_dirac_Icc_compl h1mem, smul_zero]
  have hsolve := branchSol_spec (Fw_admissible hw) hC hγ hclass hs
  have hcand : IsBranchSol (Fw (emaW (0 : ℝ))) ν ν' s
      (m / (s * L), (gammaOf N B - m) / s, s * L, s * m / (gammaOf N B - m)) := by
    unfold IsBranchSol
    dsimp only
    rw [hq, hFQ]
    refine ⟨div_nonneg hm.1.le (mul_nonneg hs.le hL.le), div_nonneg hmγ.le hs.le,
      mul_nonneg hs.le hL.le, div_nonneg (mul_nonneg hs.le hm.1.le) hmγ.le, ?_, ?_, ?_, ?_⟩
    · have hint := nm_int_dirac_sum (B := B) μ (fun t => t / (s * L * t + s))
      rw [hν, hint]
      have hterm : ∀ i, μ i / (s * L * μ i + s) = (s * L)⁻¹ * (L * μ i / (1 + L * μ i)) := by
        intro i
        have h3 : s * L * μ i + s ≠ 0 := by
          have := mul_pos (mul_pos hs hL) (hpos i)
          have := mul_pos hs (hμ1 i)
          nlinarith
        have h1 : 1 + L * μ i ≠ 0 := (hμ1 i).ne'
        have h2 : s * L ≠ 0 := (mul_pos hs hL).ne'
        field_simp
        ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
      have hS : (B : ℝ)⁻¹ * ∑ i, L * μ i / (1 + L * μ i) = m := hMN
      linear_combination -(s * L)⁻¹ * hS
    · have hint := nm_int_dirac_one (gammaOf N B) hγ.le (fun t => t / (s * m / (gammaOf N B - m) * t + s))
      rw [hν', hint]
      have hd : s * m / (gammaOf N B - m) * 1 + s = s * gammaOf N B / (gammaOf N B - m) := by
        field_simp
        ring
      rw [hd]
      field_simp
    · have e1 : s * ((gammaOf N B - m) / s) = gammaOf N B - m := by field_simp
      rw [e1]
      field_simp
      linear_combination hkey
    · field_simp
      linear_combination m * hkey
  have hbs := (thm_app_de_branch_i (Fw_admissible hw) hC hγ ν ν' hclass s hs).1.unique hsolve hcand
  rw [hbs]
  refine ⟨?_, rfl, rfl, rfl, rfl, ?_⟩
  · exact hq
  · intro i
    dsimp only
    unfold partF
    rw [← hLdef]
    have h1 : 1 + L * μ i ≠ 0 := (hμ1 i).ne'
    have h2 : s + s * L * μ i ≠ 0 := by
      have := mul_pos hs (hμ1 i)
      nlinarith
    rw [div_eq_div_iff h2 h1]
    ring

private lemma nm_diag_diracs {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (d : Fin N → ℝ) (hd : A = Matrix.diagonal d) :
    ∑ i, Measure.dirac (hA.eigenvalues i) = ∑ i, Measure.dirac (d i) := by
  have hr := hA.roots_charpoly_eq_eigenvalues
  have hp : A.charpoly.roots = (Matrix.diagonal d).charpoly.roots :=
    congrArg (fun M => M.charpoly.roots) hd
  rw [hp, Matrix.charpoly_diagonal, Polynomial.roots_prod] at hr
  · have he : Multiset.map hA.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val := by
      simpa using hr.symm
    have h := congrArg (fun z : Multiset ℝ => (z.map Measure.dirac).sum) he
    simpa [Finset.sum_eq_multiset_sum, Function.comp_def] using h
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

private lemma nm_nuOut {N B : ℕ} (C : Muon.Covariances N N) (μ : Fin N → ℝ)
    (hB : 0 < B) (hC : C.Sout = Matrix.diagonal μ) :
    Muon.nuOut C B = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i) := by
  unfold Muon.nuOut
  rw [nm_diag_diracs C.Sout C.psdOut.isHermitian μ hC]
  congr 1
  simp [ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < B by exact_mod_cast hB)]

private lemma nm_nuIn {N B : ℕ} (C : Muon.Covariances N N) (hB : 0 < B)
    (hC : C.Sin = 1) :
    Muon.nuIn C B = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ) := by
  unfold Muon.nuIn
  rw [nm_diag_diracs C.Sin C.psdIn.isHermitian (fun _ => 1) (by simpa using hC)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ENNReal, smul_smul]
  congr 1
  simp [gammaOf, div_eq_inv_mul, ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < B by exact_mod_cast hB)]

private lemma nm_diagonal_bound {N : ℕ} (d : Fin N → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ i, |d i| ≤ C) : Muon.opNorm (Matrix.diagonal d) ≤ C := by
  open scoped Matrix.Norms.L2Operator in
  rw [Muon.opNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hC).2 fun i => by
    simpa [Real.norm_eq_abs] using hd i

private lemma nm_setup {N B : ℕ} (hB : 0 < B) (μ : Fin N → ℝ)
    (hpos : ∀ i, 0 < μ i) {γstar CSig : ℝ}
    (hγ : (N : ℝ) ≤ γstar * B) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) :
    ∃ (Fp : Muon.Setup.FrozenParams N N B) (S : Muon.Setup.SpectralData Fp.C),
      Fp.β = 0 ∧ S.μ = μ ∧ S.lam = (fun _ => (1 : ℝ)) ∧
      Fp.C.Sout = Matrix.diagonal μ ∧ Fp.C.Sin = 1 ∧
      Muon.Volatility.SizeFin Fp.C B γstar CSig := by
  classical
  let C : Muon.Covariances N N :=
    { Sout := Matrix.diagonal μ
      Sin := Matrix.diagonal (fun _ => 1)
      psdOut := Matrix.PosSemidef.diagonal (fun j => (hpos j).le)
      psdIn := Matrix.PosSemidef.diagonal (fun _ => zero_le_one) }
  let Fp : Muon.Setup.FrozenParams N N B :=
    { C := C
      A := Pi.single i (Pi.single i 1)
      hA := by simp [Muon.fro, Pi.single_apply, ite_apply]
      β := 0
      hβ := ⟨le_rfl, zero_lt_one⟩
      hB := hB }
  let S : Muon.Setup.SpectralData Fp.C :=
    { uOut := 1
      vIn := 1
      μ := μ
      lam := fun _ => 1
      huOut := by simp
      hvIn := by simp
      eigOut := by
        intro j; ext k
        by_cases h : k = j <;> simp [Fp, C, Matrix.mulVec, dotProduct,
          Matrix.diagonal, Matrix.one_apply, h]
      eigIn := by intro j; simp [Fp, C] }
  refine ⟨Fp, S, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Fp, C]
  · simpa using hγ
  · exact nm_diagonal_bound μ CSig (by linarith) (fun j => by
      rw [abs_of_pos (hpos j)]; exact hμC j)
  · exact nm_diagonal_bound (fun _ => 1) CSig (by linarith) (fun _ => by simpa using hC1)

private lemma nm_row_eq_volraw (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : Muon.Setup.FrozenParams m n B) (S : Muon.Setup.SpectralData Fp.C)
    (hS : Muon.Volatility.SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hId : Fp.C.Sin = 1) (hβ : Fp.β = 0) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut Fp.C B)
    (hν' : (ν' : Measure ℝ) = Muon.nuIn Fp.C B) (i : Fin m) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    Muon.Volatility.rowVBar cert γstar CSig Fp.β B S.μ S.lam i ϱ ϱ =
      Muon.Volatility.volraw Fp.β ν ν' (S.μ i) ϱ := by
  have hz (ℓ : ℕ) : Muon.Volatility.lagRowBar cert γstar CSig Fp.β (ℓ + 1) B
      S.μ S.lam i ϱ ϱ = 0 :=
    Muon.Volatility.thm_app_vol_mode_kernels_iv_beta0 cert γstar CSig Fp S hS hCSig
      hId hβ i (ℓ + 1) (by omega) ϱ ϱ hϱ hϱ
  simp only [Muon.Volatility.rowVBar, hz, add_zero, tsum_zero]
  exact Muon.Volatility.thm_app_vol_mode_kernels_iv_zero_lag cert γstar CSig Fp S hS
    hCSig hId ν ν' hν hν' i ϱ hϱ

/-- `prop:app-pl-nomomentum-endpoints`(i), snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex`
l.1083–1100 (the whole environment):

\begin{proposition}[No-momentum endpoints]\label{prop:app-pl-nomomentum-endpoints}
Let $\bmom=0$, let $\alpha>0$ be fixed, and let $N,B\to\infty$ with $\gamma=N/B\to\infty$,
$\Sigmain=\Id_N$, $\Nout=\Nin=N$ and $\mu_i=i^{-\alpha}$. For $\gamma>1$ let $\resscale$ and
$i_\#=\resscale^{1/\alpha}$ be as in \cref{prop:app-pl-scales}. At each such dimension the
limits $\mathfrak d_i(0)\defeq\lim_{\ridge\downarrow0}\mathfrak d_i(\ridge)$ and
$\mathfrak v_i(0)\defeq\lim_{\ridge\downarrow0}\mathfrak v_i(\ridge)$ exist, and:
\begin{enumerate}[label=(\roman*)]
\item for every $i$,
\[
\mathfrak v_i(0)=\frac{\resscale\mu_i}{1+\resscale\mu_i}=\frac1{1+(i/i_\#)^\alpha},\qquad \sum_{i=1}^N\mathfrak v_i(0)=B ;
\]
\item for every row sequence $1\le i=i_N\le N$,
\[
\frac{i}{i_\#}\to0\ \Longrightarrow\ \mathfrak d_i(0)\sim\sqrt{\frac{\mu_i}{2\gamma}},\qquad
\frac{i}{i_\#}\to\infty\ \Longrightarrow\ \mathfrak d_i(0)\sim A_\alpha\,\mu_i\sqrt{\frac{\resscale}{2\gamma}} .
\]
\end{enumerate}
\end{proposition}

Here `β = 0`, `γ > 1` (so that `κ = Λ_N(1)` and `i_#` are defined), `Σ_in = Id_N`, `N_out = N_in = N`,
`μ_i = i^{-α}`. The limit is `𝔳_i(ϱ) → 𝔳_i(0)`, and the value is the first displayed equality. -/
theorem prop_app_pl_nomomentum_endpoints_i (cert : Muon.External.GaussianOpNorm)
    {α : ℝ} (hα : 0 < α) (N B : ℕ) (γstar CSig : ℝ)
    (hγ : 1 < gammaOf N B) (hγstar : (N : ℝ) ≤ γstar * B) (hCSig : 1 ≤ CSig) :
    (∀ i : Fin N,
      Tendsto (fun ϱ : ℝ =>
          Muon.Volatility.rowVBar cert γstar CSig (0 : ℝ) B (plSpec α 1 N) (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ)
        (𝓝[>] 0)
        (𝓝 (kappaOf α 1 N B * plSpec α 1 N i / (1 + kappaOf α 1 N B * plSpec α 1 N i)))) ∧
    (∀ i : Fin N,
      kappaOf α 1 N B * plSpec α 1 N i / (1 + kappaOf α 1 N B * plSpec α 1 N i) =
        1 / (1 + (rowNum i / iSharp α 1 N B) ^ α)) ∧
    (∑ i : Fin N, kappaOf α 1 N B * plSpec α 1 N i / (1 + kappaOf α 1 N B * plSpec α 1 N i) = (B : ℝ)) := by
  refine ⟨?_, nm_endpoint_profile hα hγ, nm_endpoint_sum hα hγ⟩
  intro i
  classical
  obtain ⟨hN, hB⟩ := nm_dimensions hγ
  have hpos : ∀ j : Fin N, 0 < plSpec α 1 N j := by
    intro j
    unfold plSpec
    positivity
  have hμC : ∀ j : Fin N, plSpec α 1 N j ≤ CSig := by
    intro j
    apply le_trans _ hCSig
    simp only [plSpec, one_mul]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by
      have hj : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
      linarith) (by linarith)
  obtain ⟨Fp, S, hβ, hμ, hlam, hout, hin, hS⟩ :=
    nm_setup hB (plSpec α 1 N) hpos hγstar hμC hCSig i
  let ν := Muon.Drift.specOutFM Fp
  let ν' := Muon.Drift.specInFM Fp
  have hν : (ν : Measure ℝ) = Muon.nuOut Fp.C B := rfl
  have hν' : (ν' : Measure ℝ) = Muon.nuIn Fp.C B := rfl
  have hνspec : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) •
      ∑ j, Measure.dirac (plSpec α 1 N j) := hν.trans (nm_nuOut Fp.C _ hB hout)
  have hν'spec : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ) :=
    hν'.trans (nm_nuIn Fp.C hB hin)
  have hlim := (nm_partF_endpoint_limit (α := α) hγ i).comp
    (nm_mOf0_limit (plSpec α 1 N) hB hN hpos hγ)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
  have hrow := nm_row_eq_volraw cert γstar CSig Fp S hS hCSig hin hβ ν ν' hν hν' i hϱ
  simp only [hβ, hμ, hlam] at hrow
  rw [hrow]
  obtain ⟨hm, he⟩ := nm_mOf0_spec (plSpec α 1 N) hB hN hpos hγ hϱ
  exact ((nm_branch (plSpec α 1 N) hB hN hpos hνspec hν'spec hμC hCSig hγ hϱ hm he).2.2.2.2.2 i).symm

private lemma nm_Lw_eq_Fw (q : ℝ) : Lw (emaW 0) q = Fw (emaW 0) q := by
  unfold Lw Fw
  congr 1
  funext j
  by_cases hj : j = 0
  · subst j
    simp [emaW]
  · simp [emaW, hj, zero_pow hj]

private lemma nm_Gfun0_eq {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ j, 0 < μ j) (hγ : 1 < gammaOf N B) (i : Fin N) {s : ℝ} (hs : 0 < s) :
    Gfun0 B μ i s = partF B μ i (mOf0 B μ s) := by
  obtain ⟨hm, -⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
  have hF : Fw (emaW 0) (Qm 0 (mOf0 B μ s)) ≠ 0 := by
    rw [nm_Fw]
    exact (lem_app_de_scalar_i.2.2.1 _ (nm_Qm_spec hm).1.le).1.ne'
  unfold Gfun0
  rw [nm_Lw_eq_Fw, div_self hF, one_mul]

private lemma nm_mOf0_anti {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ j, 0 < μ j) (hγ : 1 < gammaOf N B) {s s' : ℝ} (hs : 0 < s)
    (hss : s ≤ s') : mOf0 B μ s' ≤ mOf0 B μ s := by
  obtain ⟨hm, he⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
  obtain ⟨hm', he'⟩ := nm_mOf0_spec μ hB hN hpos hγ (hs.trans_le hss)
  by_contra h
  push_neg at h
  have ha := (nm_sN_anti μ hB hN hpos hγ) hm hm' h
  rw [he, he'] at ha
  exact (not_lt_of_ge hss) ha

private lemma nm_sat_mono {x y a : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (ha : 0 ≤ a) :
    x * a / (1 + x * a) ≤ y * a / (1 + y * a) := by
  have h1 : 0 ≤ x * a := mul_nonneg hx ha
  have h2 : x * a ≤ y * a := mul_le_mul_of_nonneg_right hxy ha
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private lemma nm_f0_facts {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ j, 0 < μ j) (hγ : 1 < gammaOf N B) (i : Fin N) {s : ℝ} (hs : 0 < s) :
    0 < partF B μ i (mOf0 B μ s) ∧ partF B μ i (mOf0 B μ s) < 1 ∧
      partF B μ i (mOf0 B μ s) ≤ partLam B μ (mOf0 B μ s) * μ i := by
  obtain ⟨hm, -⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
  have hm' : mOf0 B μ s ∈ Ioo 0 (gammaOf N B) := ⟨hm.1, hm.2.trans hγ⟩
  have hL : 0 < partLam B μ (mOf0 B μ s) :=
    (def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo hm'
  have hx : 0 < partLam B μ (mOf0 B μ s) * μ i := mul_pos hL (hpos i)
  unfold partF
  refine ⟨div_pos hx (by linarith), (div_lt_one (by linarith)).2 (by linarith), ?_⟩
  exact div_le_self hx.le (by linarith)

private lemma nm_f0_anti {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ j, 0 < μ j) (hγ : 1 < gammaOf N B) (i : Fin N) {s s' : ℝ}
    (hs : 0 < s) (hss : s ≤ s') :
    partF B μ i (mOf0 B μ s') ≤ partF B μ i (mOf0 B μ s) := by
  have hs' : 0 < s' := hs.trans_le hss
  obtain ⟨hm, -⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
  obtain ⟨hm', -⟩ := nm_mOf0_spec μ hB hN hpos hγ hs'
  have hmFull : mOf0 B μ s ∈ Ioo 0 (gammaOf N B) := ⟨hm.1, hm.2.trans hγ⟩
  have hmFull' : mOf0 B μ s' ∈ Ioo 0 (gammaOf N B) := ⟨hm'.1, hm'.2.trans hγ⟩
  have hL := (def_app_pl_participation_bij μ hB hN hpos).2.2.1.monotoneOn
    hmFull' hmFull (nm_mOf0_anti μ hB hN hpos hγ hs hss)
  unfold partF
  exact nm_sat_mono ((def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo hmFull').le
    hL (hpos i).le

private lemma nm_Gfun0_major {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ j, 0 < μ j) (hγ : 1 < gammaOf N B) (i : Fin N) :
    ∀ s : ℝ, 0 < s → |Gfun0 B μ i s| ≤
      2 * ((gammaOf N B * μ i) / (gammaOf N B * μ i + s)) := by
  intro s hs
  obtain ⟨hm, hsm⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
  obtain ⟨hf0, hf1, hfL⟩ := nm_f0_facts μ hB hN hpos hγ i hs
  have hq : 0 < Qm 0 (mOf0 B μ s) := (nm_Qm_spec hm).1
  have hJ := lem_app_de_scalar_i.2.2.1 (Qm 0 (mOf0 B μ s)) hq.le
  have hLam : 0 < partLam B μ (mOf0 B μ s) :=
    (def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo ⟨hm.1, hm.2.trans hγ⟩
  have hsL : s * partLam B μ (mOf0 B μ s) ≤ gammaOf N B := by
    have heq : s = (gammaOf N B - mOf0 B μ s) * J (Qm 0 (mOf0 B μ s)) /
        partLam B μ (mOf0 B μ s) := by
      calc
        s = sN 0 B μ (mOf0 B μ s) := hsm.symm
        _ = _ := nm_sN_alt (B := B) μ hm
    have hmul := congrArg (fun x => x * partLam B μ (mOf0 B μ s)) heq
    rw [div_mul_cancel₀ _ hLam.ne'] at hmul
    rw [hmul]
    calc
      (gammaOf N B - mOf0 B μ s) * J (Qm 0 (mOf0 B μ s)) ≤
          gammaOf N B - mOf0 B μ s :=
        mul_le_of_le_one_right (sub_nonneg.2 (hm.2.trans hγ).le) hJ.2
      _ ≤ gammaOf N B := by linarith [hm.1]
  set c := gammaOf N B * μ i with hc
  have hcpos : 0 < c := mul_pos (lt_trans one_pos hγ) (hpos i)
  have hfsc : partF B μ i (mOf0 B μ s) * s ≤ c := by
    calc
      partF B μ i (mOf0 B μ s) * s ≤
          (partLam B μ (mOf0 B μ s) * μ i) * s :=
        mul_le_mul_of_nonneg_right hfL hs.le
      _ = (s * partLam B μ (mOf0 B μ s)) * μ i := by ring
      _ ≤ gammaOf N B * μ i := mul_le_mul_of_nonneg_right hsL (hpos i).le
  rw [nm_Gfun0_eq μ hB hN hpos hγ i hs, abs_of_pos hf0]
  rcases le_total s c with hsc | hcs
  · calc
      partF B μ i (mOf0 B μ s) ≤ 1 := hf1.le
      _ ≤ 2 * (c / (c + s)) := by
        rw [← mul_div_assoc, le_div_iff₀ (by linarith)]
        linarith
  · calc
      partF B μ i (mOf0 B μ s) = partF B μ i (mOf0 B μ s) * s / s := by field_simp
      _ ≤ c / s := by gcongr
      _ ≤ 2 * (c / (c + s)) := by
        rw [← mul_div_assoc, div_le_div_iff₀ hs (by linarith)]
        nlinarith

private lemma nm_integrable_major {K c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => K * (c / (c + u ^ 2))) := by
  have h := (integrable_inv_one_add_sq.comp_div (Real.sqrt_pos.2 hc).ne').const_mul K
  refine h.congr (Filter.Eventually.of_forall (fun u => ?_))
  simp only [Function.comp]
  congr 1
  rw [div_pow, Real.sq_sqrt hc.le]
  field_simp

private lemma nm_Gfun0_int {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ j, 0 < μ j) (hγ : 1 < gammaOf N B) (i : Fin N) {τ : ℝ → ℝ}
    (hτ : MonotoneOn τ (Ioi 0)) (hτ2 : ∀ u, 0 < u → u ^ 2 ≤ τ u) :
    IntegrableOn (fun u => Gfun0 B μ i (τ u)) (Ioi 0) := by
  let c := gammaOf N B * μ i
  have hc : 0 < c := mul_pos (lt_trans one_pos hγ) (hpos i)
  have hτ0 : ∀ u, 0 < u → 0 < τ u := fun u hu => (pow_pos hu 2).trans_le (hτ2 u hu)
  have hanti : AntitoneOn (fun u => partF B μ i (mOf0 B μ (τ u))) (Ioi 0) := by
    intro a ha b hb hab
    exact nm_f0_anti μ hB hN hpos hγ i (hτ0 a ha) (hτ ha hb hab)
  have hmeas : AEStronglyMeasurable (fun u => Gfun0 B μ i (τ u))
      (volume.restrict (Ioi 0)) := by
    refine (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hanti).aestronglyMeasurable.congr ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun u hu =>
      (nm_Gfun0_eq μ hB hN hpos hγ i (hτ0 u hu)).symm
  refine Integrable.mono' ((nm_integrable_major (K := 2) hc).restrict) hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun u hu => ?_
  rw [Real.norm_eq_abs]
  refine (nm_Gfun0_major μ hB hN hpos hγ i (τ u) (hτ0 u hu)).trans ?_
  have hden1 : 0 < c + τ u := add_pos hc (hτ0 u hu)
  have hden2 : 0 < c + u ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left
    ((div_le_div_iff₀ hden1 hden2).2 (by nlinarith [hτ2 u hu])) (by norm_num)

private lemma nm_shift_bound {φ : ℝ → ℝ} {Φ ϱ : ℝ} (hϱ : 0 < ϱ)
    (hanti : AntitoneOn φ (Ioi 0)) (h0 : ∀ s, 0 < s → 0 ≤ φ s)
    (hΦ : ∀ s, 0 < s → φ s ≤ Φ) {D : ℝ → ℝ} (hD : IntegrableOn D (Ioi 0))
    (hDle : ∀ u, 0 < u → |D u| ≤ φ (u ^ 2) - φ (ϱ + u ^ 2)) :
    ∫ u in Ioi (0 : ℝ), |D u| ≤ Φ * Real.sqrt ϱ := by
  set δ := Real.sqrt ϱ with hδ
  have hδ0 : 0 < δ := Real.sqrt_pos.2 hϱ
  have hδsq : δ ^ 2 = ϱ := Real.sq_sqrt hϱ.le
  set ψ : ℝ → ℝ := fun v => φ (v ^ 2) with hψ
  have hψanti : AntitoneOn ψ (Ioi 0) := by
    intro a ha b hb hab
    exact hanti (Set.mem_Ioi.2 (pow_pos ha 2)) (Set.mem_Ioi.2 (pow_pos hb 2))
      (pow_le_pow_left₀ (le_of_lt ha) hab 2)
  have hψ0 : ∀ v, 0 < v → 0 ≤ ψ v := fun v hv => h0 _ (pow_pos hv 2)
  have hψΦ : ∀ v, 0 < v → ψ v ≤ Φ := fun v hv => hΦ _ (pow_pos hv 2)
  have hψint : ∀ a, 0 < a → IntegrableOn ψ (Ioc 0 a) := by
    intro a ha
    refine ⟨(aemeasurable_restrict_of_antitoneOn measurableSet_Ioc
        (hψanti.mono Ioc_subset_Ioi_self)).aestronglyMeasurable, ?_⟩
    refine HasFiniteIntegral.restrict_of_bounded (C := |Φ|) (by simp) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 v hv.1)]
    exact (hψΦ v hv.1).trans (le_abs_self _)
  have hpt : ∀ u, 0 < u → |D u| ≤ ψ u - ψ (u + δ) := by
    intro u hu
    refine (hDle u hu).trans ?_
    have hle : ψ (u + δ) ≤ φ (ϱ + u ^ 2) := by
      refine hanti (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity)) ?_
      nlinarith [mul_pos hu hδ0]
    show φ (u ^ 2) - φ (ϱ + u ^ 2) ≤ φ (u ^ 2) - ψ (u + δ)
    linarith
  have hT : ∀ T, δ ≤ T → ∫ u in (0 : ℝ)..T, |D u| ≤ Φ * δ := by
    intro T hTδ
    have hT0 : 0 < T := hδ0.trans_le hTδ
    have hDa : IntegrableOn (fun u => |D u|) (Ioc 0 T) :=
      IntegrableOn.mono_set (show IntegrableOn (fun u => |D u|) (Ioi 0) volume from hD.abs)
        Ioc_subset_Ioi_self
    have hi : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T + δ → IntervalIntegrable ψ volume a b := by
      intro a b ha hab hb
      have ht := (hψint (T + δ) (by positivity)).mono_set (Ioc_subset_Ioc ha hb)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 ht
    have hshift : IntervalIntegrable (fun u => ψ (u + δ)) volume 0 T := by
      have ht := (hi δ (T + δ) hδ0.le (by linarith) le_rfl).comp_add_right δ
      simpa using ht
    have hE : IntervalIntegrable (fun u => ψ u - ψ (u + δ)) volume 0 T :=
      (hi 0 T le_rfl hT0.le (by linarith)).sub hshift
    have h1 : ∫ u in (0 : ℝ)..T, |D u| ≤ ∫ u in (0 : ℝ)..T, (ψ u - ψ (u + δ)) := by
      rw [intervalIntegral.integral_of_le hT0.le, intervalIntegral.integral_of_le hT0.le]
      exact setIntegral_mono_on hDa ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT0.le).1 hE)
        measurableSet_Ioc (fun u hu => hpt u hu.1)
    have h2 : ∫ u in (0 : ℝ)..T, (ψ u - ψ (u + δ)) =
        (∫ u in (0 : ℝ)..δ, ψ u) - ∫ u in T..(T + δ), ψ u := by
      have e1 := intervalIntegral.integral_sub (hi 0 T le_rfl hT0.le (by linarith)) hshift
      have e2 := intervalIntegral.integral_comp_add_right (fun x => ψ x) (a := 0) (b := T) δ
      have eA := intervalIntegral.integral_add_adjacent_intervals
        (hi 0 δ le_rfl hδ0.le (by linarith)) (hi δ T hδ0.le hTδ (by linarith))
      have eB := intervalIntegral.integral_add_adjacent_intervals
        (hi δ T hδ0.le hTδ (by linarith)) (hi T (T + δ) hT0.le (by linarith) le_rfl)
      rw [zero_add] at e2
      linarith
    have h3 : 0 ≤ ∫ u in T..(T + δ), ψ u :=
      intervalIntegral.integral_nonneg (by linarith) (fun x hx => hψ0 x (hT0.trans_le hx.1))
    have h4 : ∫ u in (0 : ℝ)..δ, ψ u ≤ Φ * δ := by
      rw [intervalIntegral.integral_of_le hδ0.le]
      have ht := setIntegral_mono_on (hψint δ hδ0)
        (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) δ) (C := Φ) (by simp))
        measurableSet_Ioc (fun u hu => hψΦ u hu.1)
      refine ht.trans ?_
      rw [setIntegral_const]
      simp [Real.volume_real_Ioc_of_le hδ0.le, mul_comm]
    linarith
  have ht := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hD.abs
    (tendsto_id : Tendsto (fun n : ℝ => n) atTop atTop)
  exact le_of_tendsto ht ((eventually_ge_atTop δ).mono (fun T hT' => hT T hT'))

private lemma nm_kernel_pt {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ j, 0 < μ j) (hμ1 : ∀ j, μ j ≤ 1) (hγ : 1 < gammaOf N B)
    {ν ν' : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ j, Measure.dirac (μ j))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    {z : ℝ} (hz : 0 < z) (i : Fin N) :
    z * Lw (emaW 0) (Muon.Drift.branchQ (emaW 0) ν ν' z) * μ i * 1 /
      ((z + (branchSol (Fw (emaW 0)) ν ν' z).2.2.1 * μ i) *
        (z + (branchSol (Fw (emaW 0)) ν ν' z).2.2.2 * 1)) =
      (gammaOf N B)⁻¹ * Gfun0 B μ i z := by
  obtain ⟨hm, hsm⟩ := nm_mOf0_spec μ hB hN hpos hγ hz
  obtain ⟨hbMN, hbLam, -, -⟩ := def_app_pl_participation_bij μ hB hN hpos
  obtain ⟨hb1, hb2, hb3, -, -, -⟩ :=
    nm_branch μ hB hN hpos hν hν' hμ1 le_rfl hγ hz hm hsm
  unfold Gfun0 Muon.Drift.branchQ
  generalize mOf0 B μ z = m at *
  obtain ⟨hm0, hm1⟩ := hm
  have hmγ : 0 < gammaOf N B - m := sub_pos.2 (hm1.trans hγ)
  have hL : 0 < partLam B μ m := hbLam.mapsTo ⟨hm0, hm1.trans hγ⟩
  have hQ : 0 < Qm 0 m := (nm_Qm_spec ⟨hm0, hm1⟩).1
  have hrQ : rW (emaW 0) (Qm 0 m) = m := (nm_Qm_spec ⟨hm0, hm1⟩).2
  have hFQ : Fw (emaW 0) (Qm 0 m) = m / Qm 0 m := by
    exact eq_div_of_mul_eq hQ.ne' (by rw [mul_comm]; exact hrQ)
  have hkey : z * (Qm 0 m * partLam B μ m) = (gammaOf N B - m) * m := by
    rw [← hsm]
    unfold sN
    exact div_mul_cancel₀ _ (mul_ne_zero hQ.ne' hL.ne')
  have hden : 0 < 1 + partLam B μ m * μ i := by
    nlinarith [mul_pos hL (hpos i)]
  rw [hb1, hb2, hb3, hFQ]
  unfold partF
  have e1 : z + z * partLam B μ m * μ i = z * (1 + partLam B μ m * μ i) := by ring
  have e2 : z + z * m / (gammaOf N B - m) * 1 =
      z * gammaOf N B / (gammaOf N B - m) := by
    field_simp
    ring
  rw [e1, e2]
  field_simp
  congr 1
  linear_combination (-(Lw (emaW 0) (Qm 0 m) * μ i)) * hkey

private lemma nm_kernel_eq {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ j, 0 < μ j) (hμ1 : ∀ j, μ j ≤ 1) (hγ : 1 < gammaOf N B)
    (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ j, Measure.dirac (μ j))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (i : Fin N) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    Muon.Drift.kernel (emaW 0) ν ν' ϱ (μ i) 1 =
      Real.sqrt 2 / (Real.pi * gammaOf N B) *
        ∫ u in Ioi (0 : ℝ), Gfun0 B μ i (ϱ + u ^ 2) := by
  have hint : ∫ u in Ioi (0 : ℝ),
      (ϱ + u ^ 2) * Lw (emaW 0) (Muon.Drift.branchQ (emaW 0) ν ν' (ϱ + u ^ 2)) * μ i * 1 /
        ((ϱ + u ^ 2 + (branchSol (Fw (emaW 0)) ν ν' (ϱ + u ^ 2)).2.2.1 * μ i) *
          (ϱ + u ^ 2 + (branchSol (Fw (emaW 0)) ν ν' (ϱ + u ^ 2)).2.2.2 * 1)) =
      ∫ u in Ioi (0 : ℝ), (gammaOf N B)⁻¹ * Gfun0 B μ i (ϱ + u ^ 2) :=
    setIntegral_congr_fun measurableSet_Ioi (fun u _ =>
      nm_kernel_pt μ hB hN hpos hμ1 hγ hν hν'
        (add_pos_of_pos_of_nonneg hϱ (sq_nonneg u)) i)
  rw [integral_const_mul] at hint
  unfold Muon.Drift.kernel
  rw [hint]
  field_simp


/-- `prop:app-pl-nomomentum-endpoints`, existence of the zero-ridge drift limit and of its integral
(the limit clause of the proposition; the identification `𝔡_i(0) = dZero0` is the integral
`eqn:app-pl-drift-zero`). Snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex` l.1083–1100:

\begin{proposition}[No-momentum endpoints]\label{prop:app-pl-nomomentum-endpoints}
Let $\bmom=0$, let $\alpha>0$ be fixed, and let $N,B\to\infty$ with $\gamma=N/B\to\infty$,
$\Sigmain=\Id_N$, $\Nout=\Nin=N$ and $\mu_i=i^{-\alpha}$. For $\gamma>1$ let $\resscale$ and
$i_\#=\resscale^{1/\alpha}$ be as in \cref{prop:app-pl-scales}. At each such dimension the
limits $\mathfrak d_i(0)\defeq\lim_{\ridge\downarrow0}\mathfrak d_i(\ridge)$ and
$\mathfrak v_i(0)\defeq\lim_{\ridge\downarrow0}\mathfrak v_i(\ridge)$ exist, and:
\begin{enumerate}[label=(\roman*)]
\item for every $i$,
\[
\mathfrak v_i(0)=\frac{\resscale\mu_i}{1+\resscale\mu_i}=\frac1{1+(i/i_\#)^\alpha},\qquad \sum_{i=1}^N\mathfrak v_i(0)=B ;
\]
\item for every row sequence $1\le i=i_N\le N$,
\[
\frac{i}{i_\#}\to0\ \Longrightarrow\ \mathfrak d_i(0)\sim\sqrt{\frac{\mu_i}{2\gamma}},\qquad
\frac{i}{i_\#}\to\infty\ \Longrightarrow\ \mathfrak d_i(0)\sim A_\alpha\,\mu_i\sqrt{\frac{\resscale}{2\gamma}} .
\]
\end{enumerate}
\end{proposition}

Stated for one dimension with `γ > 1`, one row `i`, and the spectral measures `ν = B⁻¹∑δ_{μ_i}`, `ν' = γδ_1`
of `eqn:app-setup-spectral-measures`, with `β = 0`. -/
theorem prop_app_pl_nomomentum_endpoints_drift_limit {α : ℝ} (hα : 0 < α) (N B : ℕ)
    (ν ν' : FiniteMeasure ℝ) (hγ : 1 < gammaOf N B)
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i : Fin N, Measure.dirac (plSpec α 1 N i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ)) (i : Fin N) :
    IntegrableOn (fun u : ℝ => Gfun0 B (plSpec α 1 N) i (u ^ 2)) (Ioi 0) ∧
      Tendsto (fun ϱ : ℝ => Muon.Drift.kernel (emaW 0) ν ν' ϱ (plSpec α 1 N i) 1) (𝓝[>] 0)
        (𝓝 (dZero0 B (plSpec α 1 N) i)) := by
  obtain ⟨hN, hB⟩ := nm_dimensions hγ
  have hpos : ∀ j : Fin N, 0 < plSpec α 1 N j := by
    intro j
    unfold plSpec
    positivity
  have hμ1 : ∀ j : Fin N, plSpec α 1 N j ≤ 1 := by
    intro j
    simp only [plSpec, one_mul]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by
      have hj : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
      linarith) (by linarith)
  have hint0 : IntegrableOn
      (fun u : ℝ => Gfun0 B (plSpec α 1 N) i (u ^ 2)) (Ioi 0) :=
    nm_Gfun0_int (plSpec α 1 N) hB hN hpos hγ i
      (fun a ha b hb hab => pow_le_pow_left₀ ha.le hab 2) (fun _ _ => le_rfl)
  refine ⟨hint0, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt : Tendsto (fun ϱ : ℝ => Real.sqrt ϱ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht : Tendsto (fun x : ℝ => Real.sqrt x) (𝓝 (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt
    simpa using ht.mono_left nhdsWithin_le_nhds
  have hscale : Tendsto
      (fun ϱ : ℝ => Real.sqrt 2 / (Real.pi * gammaOf N B) * Real.sqrt ϱ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hsqrt.const_mul (Real.sqrt 2 / (Real.pi * gammaOf N B))
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hscale
  filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
  rw [nm_kernel_eq (plSpec α 1 N) hB hN hpos hμ1 hγ ν ν' hν hν' i hϱ]
  set D : ℝ → ℝ := fun u => Gfun0 B (plSpec α 1 N) i (u ^ 2) -
    Gfun0 B (plSpec α 1 N) i (ϱ + u ^ 2) with hD
  have hint1 : IntegrableOn
      (fun u : ℝ => Gfun0 B (plSpec α 1 N) i (ϱ + u ^ 2)) (Ioi 0) :=
    nm_Gfun0_int (plSpec α 1 N) hB hN hpos hγ i
      (fun a ha b hb hab => by nlinarith [pow_le_pow_left₀ ha.le hab 2])
      (fun u _ => le_add_of_nonneg_left hϱ.le)
  have hDint : IntegrableOn D (Ioi 0) := hint0.sub hint1
  have hanti : AntitoneOn (Gfun0 B (plSpec α 1 N) i) (Ioi 0) := by
    intro s hs s' hs' hss
    rw [nm_Gfun0_eq (plSpec α 1 N) hB hN hpos hγ i hs,
      nm_Gfun0_eq (plSpec α 1 N) hB hN hpos hγ i hs']
    exact nm_f0_anti (plSpec α 1 N) hB hN hpos hγ i hs hss
  have hG0 : ∀ s, 0 < s → 0 ≤ Gfun0 B (plSpec α 1 N) i s := by
    intro s hs
    rw [nm_Gfun0_eq (plSpec α 1 N) hB hN hpos hγ i hs]
    exact (nm_f0_facts (plSpec α 1 N) hB hN hpos hγ i hs).1.le
  have hG1 : ∀ s, 0 < s → Gfun0 B (plSpec α 1 N) i s ≤ 1 := by
    intro s hs
    rw [nm_Gfun0_eq (plSpec α 1 N) hB hN hpos hγ i hs]
    exact (nm_f0_facts (plSpec α 1 N) hB hN hpos hγ i hs).2.1.le
  have hDle : ∀ u, 0 < u → |D u| ≤
      Gfun0 B (plSpec α 1 N) i (u ^ 2) -
        Gfun0 B (plSpec α 1 N) i (ϱ + u ^ 2) := by
    intro u hu
    have hDu : 0 ≤ D u := by
      dsimp only [D]
      exact sub_nonneg.2 (hanti (pow_pos hu 2)
        (add_pos_of_pos_of_nonneg hϱ (sq_nonneg u)) (le_add_of_nonneg_left hϱ.le))
    rw [abs_of_nonneg hDu]
  have hshift := nm_shift_bound hϱ hanti hG0 hG1 hDint hDle
  have hdiff :
      (Real.sqrt 2 / (Real.pi * gammaOf N B) *
          ∫ u in Ioi (0 : ℝ), Gfun0 B (plSpec α 1 N) i (ϱ + u ^ 2)) -
        dZero0 B (plSpec α 1 N) i =
      Real.sqrt 2 / (Real.pi * gammaOf N B) * (-∫ u in Ioi (0 : ℝ), D u) := by
    have hI : (∫ u in Ioi (0 : ℝ), Gfun0 B (plSpec α 1 N) i (ϱ + u ^ 2)) -
        ∫ u in Ioi (0 : ℝ), Gfun0 B (plSpec α 1 N) i (u ^ 2) =
          -∫ u in Ioi (0 : ℝ), D u := by
      rw [← integral_neg]
      have he : ∀ u, -D u = Gfun0 B (plSpec α 1 N) i (ϱ + u ^ 2) -
          Gfun0 B (plSpec α 1 N) i (u ^ 2) := fun u => by simp [hD]
      simp only [he]
      exact (integral_sub hint1 hint0).symm
    rw [← hI]
    unfold dZero0
    ring
  rw [Real.norm_eq_abs, hdiff, abs_mul, abs_neg,
    abs_of_pos (by positivity : 0 < Real.sqrt 2 / (Real.pi * gammaOf N B))]
  exact mul_le_mul_of_nonneg_left
    ((abs_integral_le_integral_abs).trans (by simpa only [one_mul] using hshift)) (by positivity)

private lemma nm_contS_integrand_cont {α V : ℝ} (hα : 0 < α) (hV : 0 < V) :
    ContinuousOn (fun t : ℝ => V / (V + t ^ α)) (Icc 0 1) := by
  refine continuousOn_const.div (continuousOn_const.add ?_) ?_
  · exact (Real.continuous_rpow_const hα.le).continuousOn
  · intro t ht
    have := Real.rpow_nonneg ht.1 α
    linarith

private lemma nm_contS_strictMono {α : ℝ} (hα : 0 < α) :
    StrictMonoOn (contS α) (Ioi 0) := by
  intro V hV W hW hVW
  have hV' : (0:ℝ) < V := hV
  have hW' : (0:ℝ) < W := hW
  unfold contS
  refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one
    (nm_contS_integrand_cont hα hV') (nm_contS_integrand_cont hα hW') ?_ ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
  · intro t ht
    have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1.le α
    have h1 : 0 < V + t ^ α := by linarith
    have h2 : 0 < W + t ^ α := by linarith
    show V / (V + t ^ α) ≤ W / (W + t ^ α)
    rw [div_le_div_iff₀ h1 h2]
    nlinarith [mul_le_mul_of_nonneg_right hVW.le h0]
  · have h1 : 0 < V + (1:ℝ) ^ α := by simp; linarith
    have h2 : 0 < W + (1:ℝ) ^ α := by simp; linarith
    show V / (V + (1:ℝ) ^ α) < W / (W + (1:ℝ) ^ α)
    rw [div_lt_div_iff₀ h1 h2]
    simp
    nlinarith

private lemma nm_partMN_partLam {α : ℝ} {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    (hpos : ∀ i, 0 < plSpec α 1 N i) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 < partLam B (plSpec α 1 N) m ∧ partMN B (plSpec α 1 N) (partLam B (plSpec α 1 N) m) = m := by
  have hbij := (def_app_pl_participation_bij (plSpec α 1 N) hB hN hpos)
  refine ⟨hbij.2.1.mapsTo hm, ?_⟩
  obtain ⟨a, ha, hax⟩ := hbij.1.surjOn hm
  have hex : ∃ a ∈ Ioi (0:ℝ), partMN B (plSpec α 1 N) a = m := ⟨a, ha, hax⟩
  exact Function.invFunOn_eq hex

/-- finite-vs-continuum participation: with `V = Λ_N(m) N^{-α}`, `p' = S_α(V)` satisfies
`m/γ ≤ p' ≤ m/γ + 1/N` and `V = V_α(p')`. -/
private lemma nm_V_data {α : ℝ} (hα : 0 < α) {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    m / gammaOf N B ≤ contS α (partLam B (plSpec α 1 N) m * (N : ℝ) ^ (-α)) ∧
      contS α (partLam B (plSpec α 1 N) m * (N : ℝ) ^ (-α)) ≤ m / gammaOf N B + 1 / (N : ℝ) ∧
      contV α (contS α (partLam B (plSpec α 1 N) m * (N : ℝ) ^ (-α))) =
        partLam B (plSpec α 1 N) m * (N : ℝ) ^ (-α) := by
  have hpos : ∀ i, 0 < plSpec α 1 N i := by
    intro i; unfold plSpec; positivity
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hγ : 0 < gammaOf N B := lt_trans hm.1 hm.2
  obtain ⟨hL, hMN⟩ := nm_partMN_partLam hN hB hpos hm
  set Λ := partLam B (plSpec α 1 N) m with hΛ
  have hV : 0 < Λ * (N:ℝ) ^ (-α) := mul_pos hL (Real.rpow_pos_of_pos hNr _)
  have hS := eqn_app_pl_SN_mN (N := N) (B := B) α 1 hN hB one_pos hL
  rw [hMN, one_mul] at hS
  have hfin : finS α N (Λ * (N:ℝ) ^ (-α)) = m / gammaOf N B := by
    rw [hS]; field_simp
  have hi := lem_app_pl_finite_inverse_i_a hα hN (Λ * (N:ℝ) ^ (-α)) hV
  refine ⟨?_, ?_, ?_⟩
  · rw [← hfin]; linarith [hi.1]
  · rw [← hfin]; linarith [hi.2]
  · have hex : ∃ a ∈ Ioi (0:ℝ), contS α a = contS α (Λ * (N:ℝ) ^ (-α)) := ⟨_, hV, rfl⟩
    have h1 := Function.invFunOn_mem hex
    have h2 := Function.invFunOn_eq hex
    exact (nm_contS_strictMono hα).injOn h1 hV h2

private lemma nm_logratio (g : ℕ → ℝ) (hg : Tendsto g atTop atTop) (r1 r2 : ℕ → ℝ)
    (hr1 : Tendsto r1 atTop (𝓝 1)) (hr2 : Tendsto r2 atTop (𝓝 1)) {m : ℝ} (hm : 0 < m) :
    Tendsto (fun n => Real.log (g n / (1 * r1 n)) / Real.log (g n / (m * r2 n))) atTop (𝓝 1) := by
  have hlg : Tendsto (fun n => Real.log (g n)) atTop atTop := Real.tendsto_log_atTop.comp hg
  have hlg0 : ∀ᶠ n in atTop, 0 < Real.log (g n) := hlg.eventually_gt_atTop 0
  have hg0 : ∀ᶠ n in atTop, 0 < g n := hg.eventually_gt_atTop 0
  have hr1p : ∀ᶠ n in atTop, 0 < r1 n := Filter.Tendsto.eventually_const_lt (by norm_num : (0:ℝ) < 1) hr1
  have hr2p : ∀ᶠ n in atTop, 0 < r2 n := Filter.Tendsto.eventually_const_lt (by norm_num : (0:ℝ) < 1) hr2
  have hlr1 : Tendsto (fun n => Real.log (r1 n)) atTop (𝓝 0) := by
    have := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hr1
    simpa [Function.comp_def] using this
  have hlr2 : Tendsto (fun n => Real.log (r2 n)) atTop (𝓝 0) := by
    have := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hr2
    simpa [Function.comp_def] using this
  have hinv : Tendsto (fun n => (Real.log (g n))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hlg
  have hnum : Tendsto (fun n => 1 - Real.log (r1 n) * (Real.log (g n))⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (hlr1.mul hinv)
  have hden : Tendsto (fun n => 1 - (Real.log m + Real.log (r2 n)) * (Real.log (g n))⁻¹) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := Real.log m)).add hlr2
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (this.mul hinv)
  have := hnum.div hden one_ne_zero
  simp only [div_one] at this
  refine this.congr' ?_
  filter_upwards [hlg0, hg0, hr1p, hr2p] with n h1 h2 h3 h4
  rw [one_mul, Real.log_div h2.ne' h3.ne', Real.log_div h2.ne' (mul_pos hm h4).ne',
    Real.log_mul hm.ne' h4.ne']
  have hne : Real.log (g n) ≠ 0 := h1.ne'
  simp only [Pi.div_apply, div_eq_mul_inv]
  by_cases hd : Real.log (g n) - (Real.log m + Real.log (r2 n)) = 0
  · have : 1 - (Real.log m + Real.log (r2 n)) * (Real.log (g n))⁻¹ = 0 := by
      have : 1 - (Real.log m + Real.log (r2 n)) * (Real.log (g n))⁻¹ =
          (Real.log (g n) - (Real.log m + Real.log (r2 n))) * (Real.log (g n))⁻¹ := by
        field_simp
      rw [this, hd, zero_mul]
    rw [this, hd]; simp
  · have hd' : 1 - (Real.log m + Real.log (r2 n)) * (Real.log (g n))⁻¹ ≠ 0 := by
      intro h; apply hd
      have : 1 - (Real.log m + Real.log (r2 n)) * (Real.log (g n))⁻¹ =
          (Real.log (g n) - (Real.log m + Real.log (r2 n))) * (Real.log (g n))⁻¹ := by
        field_simp
      rw [this] at h
      rcases mul_eq_zero.1 h with h | h
      · exact h
      · exact absurd h (inv_ne_zero hne)
    field_simp

/-- The data `r_n(m') = S_α(V) γ / m' → 1` and the representation of the ratio. -/
private lemma nm_scale_data {α : ℝ} (hα : 0 < α) (N B : ℕ → ℕ) (hN0 : ∀ n, 0 < N n)
    (hB0 : ∀ n, 0 < B n) (hB : Tendsto B atTop atTop)
    (hγ : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop) {m : ℝ} (hm : m ∈ Ioc (0:ℝ) 1) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 1) ∧
      (∀ᶠ n in atTop, 0 < r n ∧
        contS α (partLam (B n) (plSpec α 1 (N n)) m * (N n : ℝ) ^ (-α)) =
          m * r n / gammaOf (N n) (B n) ∧
        contV α (m * r n / gammaOf (N n) (B n)) =
          partLam (B n) (plSpec α 1 (N n)) m * (N n : ℝ) ^ (-α)) := by
  refine ⟨fun n => contS α (partLam (B n) (plSpec α 1 (N n)) m * (N n : ℝ) ^ (-α)) *
    gammaOf (N n) (B n) / m, ?_, ?_⟩
  · have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) := hγ.eventually_gt_atTop 1
    have hBinv : Tendsto (fun n => 1 / (m * (B n : ℝ))) atTop (𝓝 0) := by
      have : Tendsto (fun n => (B n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hB
      refine (tendsto_inv_atTop_zero.comp (this.const_mul_atTop hm.1)).congr (fun n => ?_)
      simp [one_div]
    have hup : Tendsto (fun n => 1 + 1 / (m * (B n : ℝ))) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).add hBinv
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hγ1] with n hn
      have hmem : m ∈ Ioo 0 (gammaOf (N n) (B n)) := ⟨hm.1, hm.2.trans_lt hn⟩
      obtain ⟨h1, -, -⟩ := nm_V_data hα (hN0 n) (hB0 n) hmem
      have hg : 0 < gammaOf (N n) (B n) := lt_trans hm.1 hmem.2
      rw [le_div_iff₀ hm.1, one_mul, ← div_le_iff₀ hg]
      linarith
    · filter_upwards [hγ1] with n hn
      have hmem : m ∈ Ioo 0 (gammaOf (N n) (B n)) := ⟨hm.1, hm.2.trans_lt hn⟩
      obtain ⟨-, h2, -⟩ := nm_V_data hα (hN0 n) (hB0 n) hmem
      have hg : 0 < gammaOf (N n) (B n) := lt_trans hm.1 hmem.2
      have hNr : (0:ℝ) < N n := by exact_mod_cast hN0 n
      have hBr : (0:ℝ) < B n := by exact_mod_cast hB0 n
      rw [div_le_iff₀ hm.1]
      have h3 : contS α (partLam (B n) (plSpec α 1 (N n)) m * (N n : ℝ) ^ (-α)) * gammaOf (N n) (B n) ≤
          (m / gammaOf (N n) (B n) + 1 / (N n : ℝ)) * gammaOf (N n) (B n) :=
        mul_le_mul_of_nonneg_right h2 hg.le
      have h4 : (m / gammaOf (N n) (B n) + 1 / (N n : ℝ)) * gammaOf (N n) (B n) =
          m + 1 / (B n : ℝ) := by
        unfold gammaOf; field_simp
      have h5 : (1 + 1 / (m * (B n : ℝ))) * m = m + 1 / (B n : ℝ) := by
        have : (m:ℝ) ≠ 0 := hm.1.ne'
        field_simp
      linarith
  · have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) := hγ.eventually_gt_atTop 1
    filter_upwards [hγ1] with n hn
    have hmem : m ∈ Ioo 0 (gammaOf (N n) (B n)) := ⟨hm.1, hm.2.trans_lt hn⟩
    obtain ⟨h1, -, h3⟩ := nm_V_data hα (hN0 n) (hB0 n) hmem
    have hg : 0 < gammaOf (N n) (B n) := lt_trans hm.1 hmem.2
    have hP : m * (contS α (partLam (B n) (plSpec α 1 (N n)) m * (N n : ℝ) ^ (-α)) *
        gammaOf (N n) (B n) / m) / gammaOf (N n) (B n) =
        contS α (partLam (B n) (plSpec α 1 (N n)) m * (N n : ℝ) ^ (-α)) := by
      field_simp [hm.1.ne', hg.ne']
    refine ⟨?_, ?_, ?_⟩
    · apply div_pos (mul_pos _ hg) hm.1
      exact lt_of_lt_of_le (div_pos hm.1 hg) h1
    · exact hP.symm
    · rw [hP]; exact h3

private lemma nm_P_tendsto (g r : ℕ → ℝ) (hg : Tendsto g atTop atTop) (hr : Tendsto r atTop (𝓝 1))
    (hrp : ∀ᶠ n in atTop, 0 < r n) {m : ℝ} (hm : 0 < m) :
    Tendsto (fun n => m * r n / g n) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h1 : Tendsto (fun n => m * r n) atTop (𝓝 (m * 1)) := hr.const_mul m
    simpa using Tendsto.div_atTop h1 hg
  · filter_upwards [hrp, hg.eventually_gt_atTop 0] with n h1 h2
    exact div_pos (mul_pos hm h1) h2

private lemma nm_equiv_ratio {f L : ℝ → ℝ} (hf : IsEquivalent (𝓝[>] (0:ℝ)) f L)
    {Pm P1 : ℕ → ℝ} (hPm : Tendsto Pm atTop (𝓝[>] 0)) (hP1 : Tendsto P1 atTop (𝓝[>] 0)) {c : ℝ}
    (hc : Tendsto (fun n => L (Pm n) / L (P1 n)) atTop (𝓝 c)) :
    Tendsto (fun n => f (Pm n) / f (P1 n)) atTop (𝓝 c) := by
  have h := (hf.comp_tendsto hPm).div (hf.comp_tendsto hP1)
  exact h.symm.tendsto_nhds hc

private lemma nm_alg_aux (x y A Bc : ℝ) : x / y * (Bc / A) = x / A / (y / Bc) := by
  rw [div_div_div_eq, div_mul_div_comm, mul_comm y A]

private lemma nm_scale_limit {α : ℝ} (hα : 0 < α) (N B : ℕ → ℕ) (hN0 : ∀ n, 0 < N n)
    (hB0 : ∀ n, 0 < B n) (hB : Tendsto B atTop atTop)
    (hγ : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop) {m : ℝ} (hm : m ∈ Ioc (0:ℝ) 1) :
    Tendsto (fun n => partLam (B n) (plSpec α 1 (N n)) m / kappaOf α 1 (N n) (B n)) atTop
      (𝓝 (m ^ (if α ≤ 1 then (1:ℝ) else α))) := by
  have h1mem : (1:ℝ) ∈ Ioc (0:ℝ) 1 := ⟨one_pos, le_rfl⟩
  obtain ⟨rm, hrm, hrmev⟩ := nm_scale_data hα N B hN0 hB0 hB hγ hm
  obtain ⟨r1, hr1, hr1ev⟩ := nm_scale_data hα N B hN0 hB0 hB hγ h1mem
  have hrmp : ∀ᶠ n in atTop, 0 < rm n := hrmev.mono fun n h => h.1
  have hr1p : ∀ᶠ n in atTop, 0 < r1 n := hr1ev.mono fun n h => h.1
  have hPm := nm_P_tendsto _ rm hγ hrm hrmp hm.1
  have hP1 := nm_P_tendsto _ r1 hγ hr1 hr1p one_pos
  -- the ratio equals `contV(P_m)/contV(P_1)`
  have hratio : (fun n => contV α (m * rm n / gammaOf (N n) (B n)) /
        contV α (1 * r1 n / gammaOf (N n) (B n))) =ᶠ[atTop]
      fun n => partLam (B n) (plSpec α 1 (N n)) m / kappaOf α 1 (N n) (B n) := by
    filter_upwards [hrmev, hr1ev] with n h1 h2
    obtain ⟨-, -, e1⟩ := h1
    obtain ⟨-, -, e2⟩ := h2
    have hNr : (0:ℝ) < (N n : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by exact_mod_cast hN0 n) _
    rw [e1, e2]
    unfold kappaOf
    rw [mul_div_mul_right _ _ hNr.ne']
  refine Tendsto.congr' hratio ?_
  have hPmP1 : Tendsto (fun n => (m * rm n / gammaOf (N n) (B n)) /
      (1 * r1 n / gammaOf (N n) (B n))) atTop (𝓝 m) := by
    have h := (hrm.const_mul m).div hr1 one_ne_zero
    simp only [mul_one, div_one] at h
    refine h.congr' ?_
    filter_upwards [hγ.eventually_gt_atTop 0, hr1p] with n hn hn1
    simp only [Pi.div_apply]
    field_simp
  split_ifs with hα1
  · rw [Real.rpow_one]
    rcases hα1.lt_or_eq with hlt | heq
    · refine nm_equiv_ratio (lem_app_pl_continuum_iii_lt hα hlt) hPm hP1 ?_
      refine hPmP1.congr (fun n => ?_)
      have hne : (1 - α) ≠ 0 := by linarith
      field_simp
    · subst heq
      refine nm_equiv_ratio lem_app_pl_continuum_iii_one hPm hP1 ?_
      have hlog := nm_logratio _ hγ r1 rm hr1 hrm hm.1
      have := hPmP1.mul hlog
      simp only [mul_one] at this
      refine this.congr' ?_
      filter_upwards [hγ.eventually_gt_atTop 0, hrmp, hr1p] with n hn h1 h2
      rw [one_div_div, one_div_div]
      exact nm_alg_aux _ _ _ _
  · have hgt : 1 < α := not_le.1 hα1
    refine nm_equiv_ratio (lem_app_pl_continuum_iii_gt hgt) hPm hP1 ?_
    have hK : 0 < Kc α := by
      unfold Kc
      have h1 : 0 < Real.pi / α := div_pos Real.pi_pos hα
      have h2 : Real.pi / α < Real.pi := (div_lt_self Real.pi_pos hgt)
      exact div_pos Real.pi_pos (mul_pos hα (Real.sin_pos_of_pos_of_lt_pi h1 h2))
    have := (hPmP1.rpow_const (p := α) (Or.inr hα.le))
    refine this.congr' ?_
    filter_upwards [hrmp, hr1p, hγ.eventually_gt_atTop 0] with n h1 h2 h3
    have hKα : 0 < Kc α ^ α := Real.rpow_pos_of_pos hK α
    have ha : 0 ≤ m * rm n / gammaOf (N n) (B n) := (div_pos (mul_pos hm.1 h1) h3).le
    have hb : 0 ≤ 1 * r1 n / gammaOf (N n) (B n) := (div_pos (by linarith) h3).le
    have hbpos : 0 < (1 * r1 n / gammaOf (N n) (B n)) ^ α := Real.rpow_pos_of_pos (div_pos (by linarith) h3) α
    rw [Real.div_rpow ha hK.le, Real.div_rpow hb hK.le, div_div_div_cancel_right₀ hKα.ne',
      Real.div_rpow ha hb]

/-- `Λ_N(m_N(t)) = t` for `t > 0`. -/
private lemma nm_partLam_partMN {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {t : ℝ} (ht : 0 < t) :
    partMN B μ t ∈ Ioo 0 (gammaOf N B) ∧ partLam B μ (partMN B μ t) = t := by
  have hbij := def_app_pl_participation_bij μ hB hN hpos
  exact ⟨hbij.1.mapsTo ht, hbij.1.injOn.leftInvOn_invFunOn ht⟩

private lemma nm_lt_iff {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {t m : ℝ} (ht : 0 < t) (hm : m ∈ Ioo 0 (gammaOf N B)) :
    t < partLam B μ m ↔ partMN B μ t < m := by
  have hbij := def_app_pl_participation_bij μ hB hN hpos
  obtain ⟨hmem, hlam⟩ := nm_partLam_partMN μ hB hN hpos ht
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have := hbij.2.2.1.monotoneOn hm hmem hcon
    rw [hlam] at this
    linarith
  · intro h
    have := hbij.2.2.1 hmem hm h
    rwa [hlam] at this

/-- `m(s) > m'` iff `s < s_N(m')`, for `s > 0`, `m' ∈ (0,1)`. -/
private lemma nm_mOf0_gt_iff {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) {s m' : ℝ} (hs : 0 < s)
    (hm' : m' ∈ Ioo (0:ℝ) 1) : m' < mOf0 B μ s ↔ s < sN 0 B μ m' := by
  obtain ⟨hm, he⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
  constructor
  · intro h
    have := nm_sN_anti μ hB hN hpos hγ hm' hm h
    rwa [he] at this
  · intro h
    by_contra hcon
    push_neg at hcon
    have := (nm_sN_anti μ hB hN hpos hγ).antitoneOn hm hm' hcon
    rw [he] at this
    linarith

private lemma nm_Lam_mul_s {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) {s : ℝ} (hs : 0 < s) :
    partLam B μ (mOf0 B μ s) * s =
      (gammaOf N B - mOf0 B μ s) * J (Qm 0 (mOf0 B μ s)) := by
  obtain ⟨hm, he⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
  have hLam : 0 < partLam B μ (mOf0 B μ s) :=
    (def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo ⟨hm.1, hm.2.trans hγ⟩
  have h := nm_sN_alt (B := B) μ hm
  rw [he] at h
  rw [eq_div_iff hLam.ne'] at h
  linarith

private lemma nm_Lam_mul_s_le {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) {s : ℝ} (hs : 0 < s) :
    partLam B μ (mOf0 B μ s) * s ≤ gammaOf N B := by
  obtain ⟨hm, -⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
  rw [nm_Lam_mul_s μ hB hN hpos hγ hs]
  have hJ := lem_app_de_scalar_i.2.2.1 (Qm 0 (mOf0 B μ s)) (nm_Qm_spec hm).1.le
  calc
    (gammaOf N B - mOf0 B μ s) * J (Qm 0 (mOf0 B μ s)) ≤ gammaOf N B - mOf0 B μ s :=
      mul_le_of_le_one_right (sub_nonneg.2 (hm.2.trans hγ).le) hJ.2
    _ ≤ gammaOf N B := by linarith [hm.1]

private lemma nm_Lam_mOf0_lt {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) {s : ℝ} (hs : 0 < s) :
    partLam B μ (mOf0 B μ s) < partLam B μ 1 := by
  obtain ⟨hm, -⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
  exact (def_app_pl_participation_bij μ hB hN hpos).2.2.1 ⟨hm.1, hm.2.trans hγ⟩
    ⟨one_pos, hγ⟩ hm.2

private lemma nm_Lam_mOf0_anti {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') :
    partLam B μ (mOf0 B μ s') ≤ partLam B μ (mOf0 B μ s) := by
  obtain ⟨hm, -⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
  obtain ⟨hm', -⟩ := nm_mOf0_spec μ hB hN hpos hγ (hs.trans_le hss)
  exact (def_app_pl_participation_bij μ hB hN hpos).2.2.1.monotoneOn
    ⟨hm'.1, hm'.2.trans hγ⟩ ⟨hm.1, hm.2.trans hγ⟩ (nm_mOf0_anti μ hB hN hpos hγ hs hss)

private lemma nm_f_integrable {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) :
    IntegrableOn (fun u : ℝ => partLam B μ (mOf0 B μ (u ^ 2)) / partLam B μ 1) (Ioi 0) := by
  have hκ : 0 < partLam B μ 1 :=
    (def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo ⟨one_pos, hγ⟩
  set κ := partLam B μ 1 with hκdef
  have hc : 0 < gammaOf N B / κ := div_pos (lt_trans one_pos hγ) hκ
  have hanti : AntitoneOn (fun u : ℝ => partLam B μ (mOf0 B μ (u ^ 2)) / κ) (Ioi 0) := by
    intro a ha b hb hab
    exact div_le_div_of_nonneg_right
      (nm_Lam_mOf0_anti μ hB hN hpos hγ (pow_pos ha 2) (pow_le_pow_left₀ ha.le hab 2)) hκ.le
  have hmeas : AEStronglyMeasurable (fun u : ℝ => partLam B μ (mOf0 B μ (u ^ 2)) / κ)
      (volume.restrict (Ioi 0)) :=
    (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hanti).aestronglyMeasurable
  refine Integrable.mono' ((nm_integrable_major (K := 2) hc).restrict) hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun u hu => ?_
  have hs : 0 < u ^ 2 := pow_pos hu 2
  have hLpos : 0 < partLam B μ (mOf0 B μ (u ^ 2)) :=
    (def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo (by
      obtain ⟨hm, -⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
      exact ⟨hm.1, hm.2.trans hγ⟩)
  rw [Real.norm_eq_abs, abs_of_pos (div_pos hLpos hκ)]
  have h1 : partLam B μ (mOf0 B μ (u ^ 2)) / κ ≤ 1 :=
    (div_le_one hκ).2 (nm_Lam_mOf0_lt μ hB hN hpos hγ hs).le
  have h2 : partLam B μ (mOf0 B μ (u ^ 2)) / κ ≤ (gammaOf N B / κ) / u ^ 2 := by
    rw [div_div, div_le_div_iff₀ hκ (mul_pos hκ hs)]
    have := nm_Lam_mul_s_le μ hB hN hpos hγ hs
    nlinarith [this]
  set c := gammaOf N B / κ
  rcases le_total (u ^ 2) c with hsc | hcs
  · calc _ ≤ (1:ℝ) := h1
      _ ≤ 2 * (c / (c + u ^ 2)) := by
        rw [← mul_div_assoc, le_div_iff₀ (by linarith)]
        linarith
  · calc _ ≤ c / u ^ 2 := h2
      _ ≤ 2 * (c / (c + u ^ 2)) := by
        rw [← mul_div_assoc, div_le_div_iff₀ hs (by linarith)]
        nlinarith

private lemma nm_layer_set {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) {y : ℝ} (hy : 0 < y) :
    (volume.restrict (Ioi (0:ℝ))).real
        {u : ℝ | y < partLam B μ (mOf0 B μ (u ^ 2)) / partLam B μ 1} =
      (Ioo (0:ℝ) 1).indicator
        (fun y => Real.sqrt (sN 0 B μ (partMN B μ (partLam B μ 1 * y)))) y := by
  have hbij := def_app_pl_participation_bij μ hB hN hpos
  have hκ : 0 < partLam B μ 1 := hbij.2.1.mapsTo ⟨one_pos, hγ⟩
  set κ := partLam B μ 1 with hκdef
  have h1mem : (1:ℝ) ∈ Ioo 0 (gammaOf N B) := ⟨one_pos, hγ⟩
  rw [Measure.real, Measure.restrict_apply' measurableSet_Ioi]
  by_cases hy1 : y < 1
  · rw [Set.indicator_of_mem (show y ∈ Ioo (0:ℝ) 1 from ⟨hy, hy1⟩)]
    have hky : 0 < κ * y := mul_pos hκ hy
    have hMn1 : partMN B μ (κ * y) < 1 := (nm_lt_iff μ hB hN hpos hky h1mem).1 (by
      rw [← hκdef]; nlinarith)
    have hMn0 : 0 < partMN B μ (κ * y) := (hbij.1.mapsTo hky).1
    have hmem : partMN B μ (κ * y) ∈ Ioo (0:ℝ) 1 := ⟨hMn0, hMn1⟩
    have hSpos : 0 < sN 0 B μ (partMN B μ (κ * y)) := nm_sN_pos μ hB hN hpos hγ hmem
    have hset : {u : ℝ | y < partLam B μ (mOf0 B μ (u ^ 2)) / κ} ∩ Ioi 0 =
        Ioo 0 (Real.sqrt (sN 0 B μ (partMN B μ (κ * y)))) := by
      ext u
      simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨h, hu⟩
        refine ⟨hu, ?_⟩
        have hs : 0 < u ^ 2 := pow_pos hu 2
        obtain ⟨hm, -⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
        have h' : κ * y < partLam B μ (mOf0 B μ (u ^ 2)) := by
          rw [lt_div_iff₀ hκ] at h; linarith
        have h2 := (nm_lt_iff μ hB hN hpos hky ⟨hm.1, hm.2.trans hγ⟩).1 h'
        have h3 := (nm_mOf0_gt_iff μ hB hN hpos hγ hs hmem).1 h2
        exact Real.lt_sqrt_of_sq_lt h3
      · rintro ⟨hu, hlt⟩
        refine ⟨?_, hu⟩
        have hs : 0 < u ^ 2 := pow_pos hu 2
        obtain ⟨hm, -⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
        have h3 : u ^ 2 < sN 0 B μ (partMN B μ (κ * y)) := by
          exact (Real.lt_sqrt hu.le).1 hlt
        have h2 := (nm_mOf0_gt_iff μ hB hN hpos hγ hs hmem).2 h3
        have h' := (nm_lt_iff μ hB hN hpos hky ⟨hm.1, hm.2.trans hγ⟩).2 h2
        rw [lt_div_iff₀ hκ]; linarith
    rw [hset]
    simp [Real.volume_Ioo]
  · rw [Set.indicator_of_notMem (show y ∉ Ioo (0:ℝ) 1 from fun h => hy1 h.2)]
    have : {u : ℝ | y < partLam B μ (mOf0 B μ (u ^ 2)) / κ} ∩ Ioi 0 = ∅ := by
      ext u
      simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
      intro h hu
      have hs : 0 < u ^ 2 := pow_pos hu 2
      have := (div_lt_one hκ).2 (nm_Lam_mOf0_lt μ hB hN hpos hγ hs)
      linarith
    rw [this]; simp

private lemma nm_layer_n {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) :
    ∫ u in Ioi (0:ℝ), partLam B μ (mOf0 B μ (u ^ 2)) / partLam B μ 1 =
      ∫ y in Ioi (0:ℝ), (Ioo (0:ℝ) 1).indicator
        (fun y => Real.sqrt (sN 0 B μ (partMN B μ (partLam B μ 1 * y)))) y := by
  have hbij := def_app_pl_participation_bij μ hB hN hpos
  have hκ : 0 < partLam B μ 1 := hbij.2.1.mapsTo ⟨one_pos, hγ⟩
  have hint := nm_f_integrable μ hB hN hpos hγ
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun u : ℝ => partLam B μ (mOf0 B μ (u ^ 2)) / partLam B μ 1) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun u hu => ?_
    have hs : 0 < u ^ 2 := pow_pos hu 2
    obtain ⟨hm, -⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
    exact (div_pos (hbij.2.1.mapsTo ⟨hm.1, hm.2.trans hγ⟩) hκ).le
  rw [Integrable.integral_eq_integral_meas_lt hint hnn]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  exact nm_layer_set μ hB hN hpos hγ hy

private lemma nm_lt_iff' {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {t m : ℝ} (ht : 0 < t) (hm : m ∈ Ioo 0 (gammaOf N B)) :
    partLam B μ m < t ↔ m < partMN B μ t := by
  have hbij := def_app_pl_participation_bij μ hB hN hpos
  obtain ⟨hmem, hlam⟩ := nm_partLam_partMN μ hB hN hpos ht
  conv_lhs => rw [← hlam]
  exact hbij.2.2.1.lt_iff_lt hm hmem

private lemma nm_Mn_mono {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t') :
    partMN B μ t ≤ partMN B μ t' := by
  have hbij := def_app_pl_participation_bij μ hB hN hpos
  obtain ⟨hmem, hlam⟩ := nm_partLam_partMN μ hB hN hpos ht
  obtain ⟨hmem', hlam'⟩ := nm_partLam_partMN μ hB hN hpos (ht.trans_le htt)
  by_contra h
  push_neg at h
  have := hbij.2.2.1 hmem' hmem h
  rw [hlam, hlam'] at this
  linarith

private lemma nm_Mn_lt_one {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) {y : ℝ} (hy : y ∈ Ioo (0:ℝ) 1) :
    partMN B μ (partLam B μ 1 * y) ∈ Ioo (0:ℝ) 1 := by
  have hbij := def_app_pl_participation_bij μ hB hN hpos
  have hκ : 0 < partLam B μ 1 := hbij.2.1.mapsTo ⟨one_pos, hγ⟩
  have hky : 0 < partLam B μ 1 * y := mul_pos hκ hy.1
  refine ⟨(hbij.1.mapsTo hky).1, ?_⟩
  exact (nm_lt_iff μ hB hN hpos hky ⟨one_pos, hγ⟩).1 (by nlinarith [hy.2])

private lemma nm_Mn_limit {α : ℝ} (hα : 0 < α) (N B : ℕ → ℕ) (hN0 : ∀ n, 0 < N n)
    (hB0 : ∀ n, 0 < B n) (hB : Tendsto B atTop atTop)
    (hγ : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop) {y : ℝ} (hy : y ∈ Ioo (0:ℝ) 1) :
    Tendsto (fun n => partMN (B n) (plSpec α 1 (N n))
        (partLam (B n) (plSpec α 1 (N n)) 1 * y)) atTop
      (𝓝 (y ^ (1 / (if α ≤ 1 then (1:ℝ) else α)))) := by
  set ν : ℝ := if α ≤ 1 then (1:ℝ) else α with hν
  have hν0 : 0 < ν := by rw [hν]; split_ifs <;> linarith
  have hpos : ∀ n i, 0 < plSpec α 1 (N n) i := by
    intro n i; unfold plSpec; positivity
  set c : ℝ := y ^ (1 / ν) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hy.1 _
  have hc1 : c < 1 := Real.rpow_lt_one hy.1.le hy.2 (by positivity)
  have hcν : c ^ ν = y := by
    rw [hc, ← Real.rpow_mul hy.1.le, one_div, inv_mul_cancel₀ hν0.ne', Real.rpow_one]
  have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) := hγ.eventually_gt_atTop 1
  rw [tendsto_order]
  constructor
  · intro a ha
    rcases le_or_gt a 0 with ha0 | ha0
    · filter_upwards [hγ1] with n hn
      have hbij := def_app_pl_participation_bij (plSpec α 1 (N n)) (hB0 n) (hN0 n) (hpos n)
      have hκ : 0 < partLam (B n) (plSpec α 1 (N n)) 1 := hbij.2.1.mapsTo ⟨one_pos, hn⟩
      exact ha0.trans_lt (hbij.1.mapsTo (mul_pos hκ hy.1)).1
    · have haI : a ∈ Ioc (0:ℝ) 1 := ⟨ha0, (ha.trans hc1).le⟩
      have hlim := nm_scale_limit hα N B hN0 hB0 hB hγ haI
      have haν : a ^ ν < y := by
        rw [← hcν]
        exact Real.rpow_lt_rpow ha0.le ha hν0
      filter_upwards [hγ1, hlim.eventually_lt_const haν] with n hn h
      have hbij := def_app_pl_participation_bij (plSpec α 1 (N n)) (hB0 n) (hN0 n) (hpos n)
      have hκ : 0 < partLam (B n) (plSpec α 1 (N n)) 1 := hbij.2.1.mapsTo ⟨one_pos, hn⟩
      have hky : 0 < partLam (B n) (plSpec α 1 (N n)) 1 * y := mul_pos hκ hy.1
      have haγ : a ∈ Ioo 0 (gammaOf (N n) (B n)) := ⟨ha0, (haI.2).trans_lt hn⟩
      refine (nm_lt_iff' _ (hB0 n) (hN0 n) (hpos n) hky haγ).1 ?_
      unfold kappaOf at h
      rw [div_lt_iff₀ hκ] at h
      linarith
  · intro b hb
    rcases le_or_gt 1 b with hb1 | hb1
    · filter_upwards [hγ1] with n hn
      exact (nm_Mn_lt_one _ (hB0 n) (hN0 n) (hpos n) hn hy).2.trans_le hb1
    · have hbI : b ∈ Ioc (0:ℝ) 1 := ⟨hc0.trans hb, hb1.le⟩
      have hlim := nm_scale_limit hα N B hN0 hB0 hB hγ hbI
      have hbν : y < b ^ ν := by
        rw [← hcν]
        exact Real.rpow_lt_rpow hc0.le hb hν0
      filter_upwards [hγ1, hlim.eventually_const_lt hbν] with n hn h
      have hbij := def_app_pl_participation_bij (plSpec α 1 (N n)) (hB0 n) (hN0 n) (hpos n)
      have hκ : 0 < partLam (B n) (plSpec α 1 (N n)) 1 := hbij.2.1.mapsTo ⟨one_pos, hn⟩
      have hky : 0 < partLam (B n) (plSpec α 1 (N n)) 1 * y := mul_pos hκ hy.1
      have hbγ : b ∈ Ioo 0 (gammaOf (N n) (B n)) := ⟨hc0.trans hb, hb1.trans hn⟩
      have := (nm_lt_iff _ (hB0 n) (hN0 n) (hpos n) hky hbγ).1
      apply this
      unfold kappaOf at h
      rw [lt_div_iff₀ hκ] at h
      linarith

private lemma nm_E_formula {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) {y : ℝ} (hy : y ∈ Ioo (0:ℝ) 1) :
    (partLam B μ 1 / gammaOf N B) * sN 0 B μ (partMN B μ (partLam B μ 1 * y)) =
      (1 - partMN B μ (partLam B μ 1 * y) / gammaOf N B) *
        J (Qm 0 (partMN B μ (partLam B μ 1 * y))) / y := by
  have hbij := def_app_pl_participation_bij μ hB hN hpos
  have hκ : 0 < partLam B μ 1 := hbij.2.1.mapsTo ⟨one_pos, hγ⟩
  have hky : 0 < partLam B μ 1 * y := mul_pos hκ hy.1
  have hmem := nm_Mn_lt_one μ hB hN hpos hγ hy
  obtain ⟨-, hlam⟩ := nm_partLam_partMN μ hB hN hpos hky
  rw [nm_sN_alt μ hmem, hlam]
  have hg : 0 < gammaOf N B := lt_trans one_pos hγ
  field_simp

private lemma nm_E_le {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) {y : ℝ} (hy : y ∈ Ioo (0:ℝ) 1) :
    0 ≤ (partLam B μ 1 / gammaOf N B) * sN 0 B μ (partMN B μ (partLam B μ 1 * y)) ∧
    (partLam B μ 1 / gammaOf N B) * sN 0 B μ (partMN B μ (partLam B μ 1 * y)) ≤ 1 / y := by
  rw [nm_E_formula μ hB hN hpos hγ hy]
  have hmem := nm_Mn_lt_one μ hB hN hpos hγ hy
  have hg : 0 < gammaOf N B := lt_trans one_pos hγ
  have hJ := lem_app_de_scalar_i.2.2.1 (Qm 0 (partMN B μ (partLam B μ 1 * y))) (nm_Qm_spec hmem).1.le
  have h1 : 0 < 1 - partMN B μ (partLam B μ 1 * y) / gammaOf N B := by
    have : partMN B μ (partLam B μ 1 * y) / gammaOf N B < 1 := by
      rw [div_lt_one hg]; exact hmem.2.trans hγ
    linarith
  have h2 : 1 - partMN B μ (partLam B μ 1 * y) / gammaOf N B ≤ 1 := by
    have : 0 ≤ partMN B μ (partLam B μ 1 * y) / gammaOf N B := div_nonneg hmem.1.le hg.le
    linarith
  refine ⟨div_nonneg (mul_nonneg h1.le hJ.1.le) hy.1.le, ?_⟩
  apply div_le_div_of_nonneg_right _ hy.1.le
  calc _ ≤ 1 * 1 := mul_le_mul h2 hJ.2 hJ.1.le zero_le_one
    _ = 1 := one_mul 1

private lemma nm_J_Qm_cont {c : ℝ} (hc : c ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (fun m => J (Qm 0 m)) c := by
  have h1 : ContinuousAt (Qm 0) c := nm_Qm_cont.continuousAt (Ioo_mem_nhds hc.1 hc.2)
  have h2 : ContinuousAt J (Qm 0 c) :=
    (lem_app_de_scalar_i.1.continuousAt (Ici_mem_nhds (nm_Qm_spec hc).1))
  exact h2.comp h1

private lemma nm_E_limit {α : ℝ} (hα : 0 < α) (N B : ℕ → ℕ) (hN0 : ∀ n, 0 < N n)
    (hB0 : ∀ n, 0 < B n) (hB : Tendsto B atTop atTop)
    (hγ : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop) {y : ℝ} (hy : y ∈ Ioo (0:ℝ) 1) :
    Tendsto (fun n => (partLam (B n) (plSpec α 1 (N n)) 1 / gammaOf (N n) (B n)) *
        sN 0 (B n) (plSpec α 1 (N n))
          (partMN (B n) (plSpec α 1 (N n)) (partLam (B n) (plSpec α 1 (N n)) 1 * y))) atTop
      (𝓝 (J (Qm 0 (y ^ (1 / (if α ≤ 1 then (1:ℝ) else α)))) / y)) := by
  set ν : ℝ := if α ≤ 1 then (1:ℝ) else α with hν
  have hpos : ∀ n i, 0 < plSpec α 1 (N n) i := by
    intro n i; unfold plSpec; positivity
  have hν0 : 0 < ν := by rw [hν]; split_ifs <;> linarith
  have hc0 : 0 < y ^ (1 / ν) := Real.rpow_pos_of_pos hy.1 _
  have hc1 : y ^ (1 / ν) < 1 := Real.rpow_lt_one hy.1.le hy.2 (by positivity)
  have hM := nm_Mn_limit hα N B hN0 hB0 hB hγ hy
  have hJ : Tendsto (fun n => J (Qm 0 (partMN (B n) (plSpec α 1 (N n))
      (partLam (B n) (plSpec α 1 (N n)) 1 * y)))) atTop (𝓝 (J (Qm 0 (y ^ (1 / ν))))) :=
    (nm_J_Qm_cont ⟨hc0, hc1⟩).tendsto.comp hM
  have hdiv : Tendsto (fun n => partMN (B n) (plSpec α 1 (N n))
      (partLam (B n) (plSpec α 1 (N n)) 1 * y) / gammaOf (N n) (B n)) atTop (𝓝 0) :=
    hM.div_atTop hγ
  have h1 := ((tendsto_const_nhds (x := (1:ℝ))).sub hdiv).mul hJ |>.div_const y
  simp only [sub_zero, one_mul] at h1
  refine h1.congr' ?_
  filter_upwards [hγ.eventually_gt_atTop 1] with n hn
  exact (nm_E_formula _ (hB0 n) (hN0 n) (hpos n) hn hy).symm

private lemma nm_sqrt_inv_eq {y : ℝ} (hy : 0 < y) : Real.sqrt (1 / y) = y ^ (-(1:ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, one_div, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le]
  congr 1; ring

private lemma nm_dct_y {α : ℝ} (hα : 0 < α) (N B : ℕ → ℕ) (hN0 : ∀ n, 0 < N n)
    (hB0 : ∀ n, 0 < B n) (hB : Tendsto B atTop atTop)
    (hγ : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop) :
    Tendsto (fun n => ∫ y in Ioo (0:ℝ) 1, Real.sqrt
        ((partLam (B n) (plSpec α 1 (N n)) 1 / gammaOf (N n) (B n)) *
        sN 0 (B n) (plSpec α 1 (N n))
          (partMN (B n) (plSpec α 1 (N n)) (partLam (B n) (plSpec α 1 (N n)) 1 * y)))) atTop
      (𝓝 (∫ y in Ioo (0:ℝ) 1, Real.sqrt (J (Qm 0 (y ^ (1 / (if α ≤ 1 then (1:ℝ) else α)))) / y))) := by
  have hpos : ∀ n i, 0 < plSpec α 1 (N n) i := by
    intro n i; unfold plSpec; positivity
  have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) := hγ.eventually_gt_atTop 1
  refine tendsto_integral_filter_of_dominated_convergence (fun y => y ^ (-(1:ℝ) / 2)) ?_ ?_ ?_ ?_
  · filter_upwards [hγ1] with n hn
    have hbij := def_app_pl_participation_bij (plSpec α 1 (N n)) (hB0 n) (hN0 n) (hpos n)
    have hκ : 0 < partLam (B n) (plSpec α 1 (N n)) 1 := hbij.2.1.mapsTo ⟨one_pos, hn⟩
    have hg : 0 < gammaOf (N n) (B n) := lt_trans one_pos hn
    have hanti : AntitoneOn (fun y : ℝ => Real.sqrt
        ((partLam (B n) (plSpec α 1 (N n)) 1 / gammaOf (N n) (B n)) *
        sN 0 (B n) (plSpec α 1 (N n))
          (partMN (B n) (plSpec α 1 (N n)) (partLam (B n) (plSpec α 1 (N n)) 1 * y)))) (Ioo 0 1) := by
      intro a ha b hb hab
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (div_pos hκ hg).le
      have hMa := nm_Mn_lt_one _ (hB0 n) (hN0 n) (hpos n) hn ha
      have hMb := nm_Mn_lt_one _ (hB0 n) (hN0 n) (hpos n) hn hb
      exact (nm_sN_anti _ (hB0 n) (hN0 n) (hpos n) hn).antitoneOn hMa hMb
        (nm_Mn_mono _ (hB0 n) (hN0 n) (hpos n) (mul_pos hκ ha.1) (mul_le_mul_of_nonneg_left hab hκ.le))
    exact (aemeasurable_restrict_of_antitoneOn measurableSet_Ioo hanti).aestronglyMeasurable
  · filter_upwards [hγ1] with n hn
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun y hy => ?_
    obtain ⟨h0, h1⟩ := nm_E_le _ (hB0 n) (hN0 n) (hpos n) hn hy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), ← nm_sqrt_inv_eq hy.1]
    exact Real.sqrt_le_sqrt h1
  · exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ) < 1)).2 (by norm_num)
  · rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun y hy => ?_
    exact (nm_E_limit hα N B hN0 hB0 hB hγ hy).sqrt

private lemma nm_rW_eq (q : ℝ) : rW (emaW 0) q = q * J q := by
  unfold rW; rw [nm_Fw]

private lemma nm_r_gt_iff {m q : ℝ} (hm : m ∈ Ioo (0:ℝ) 1) (hq : 0 < q) :
    m < q * J q ↔ Qm 0 m < q := by
  obtain ⟨hQ, hr⟩ := nm_Qm_spec hm
  have hmono := (lem_app_de_scalar_iii nm_wseq).2.1
  rw [← nm_rW_eq]
  conv_lhs => rw [← hr]
  exact hmono.lt_iff_lt hQ.le hq.le

private lemma nm_J_Qm {m : ℝ} (hm : m ∈ Ioo (0:ℝ) 1) : J (Qm 0 m) = m / Qm 0 m := by
  obtain ⟨hQ, hr⟩ := nm_Qm_spec hm
  rw [nm_rW_eq] at hr
  rw [eq_div_iff hQ.ne']
  linarith

private lemma nm_r_mem {q : ℝ} (hq : 0 < q) : q * J q ∈ Ioo (0:ℝ) 1 := by
  rw [← nm_rW_eq]; exact nm_rW_mem hq

private lemma nm_vq_iff {v Q : ℝ} (hv : 0 < v) (hQ : 0 < Q) :
    Q < v ^ (-(2:ℝ)) ↔ v < Q ^ (-(1:ℝ) / 2) := by
  have h1 : v ^ (-(2:ℝ)) = (v ^ 2)⁻¹ := by
    rw [Real.rpow_neg hv.le]; norm_cast
  have h2 : Q ^ (-(1:ℝ) / 2) = Real.sqrt (Q⁻¹) := by
    rw [← one_div, nm_sqrt_inv_eq hQ]
  rw [h1, h2, lt_inv_comm₀ hQ (pow_pos hv 2), Real.lt_sqrt hv.le]

private lemma nm_H_cont {p : ℝ} (hp : 0 < p) :
    ContinuousOn (fun v : ℝ => (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p) (Ioi 0) := by
  have h1 : ContinuousOn (fun v : ℝ => v ^ (-(2:ℝ))) (Ioi 0) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))
  have h2 : ContinuousOn (fun v : ℝ => J (v ^ (-(2:ℝ)))) (Ioi 0) :=
    lem_app_de_scalar_i.1.comp h1 (fun x hx => Real.rpow_nonneg (le_of_lt hx) _)
  exact (h1.mul h2).rpow_const (fun x hx => Or.inr hp.le)

private lemma nm_H_bound {p : ℝ} (hp : 1 ≤ p) {v : ℝ} (hv : 0 < v) :
    0 < (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p ∧
    (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p < 1 ∧
    (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p ≤ 2 * (1 / (1 + v ^ 2)) := by
  have hq : 0 < v ^ (-(2:ℝ)) := Real.rpow_pos_of_pos hv _
  have hm := nm_r_mem hq
  refine ⟨Real.rpow_pos_of_pos hm.1 _, Real.rpow_lt_one hm.1.le hm.2 (by linarith), ?_⟩
  have hle : (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p ≤ (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) := 
    Real.rpow_le_self_of_le_one hm.1.le hm.2.le hp
  have hJ := (lem_app_de_scalar_i.2.2.1 _ hq.le).2
  have hle2 : (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ≤ v ^ (-(2:ℝ)) :=
    mul_le_of_le_one_right hq.le hJ
  have h1 : v ^ (-(2:ℝ)) = (v ^ 2)⁻¹ := by
    rw [Real.rpow_neg hv.le]; norm_cast
  rcases le_total v 1 with hv1 | hv1
  · have : (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p ≤ 1 := (Real.rpow_lt_one hm.1.le hm.2 (by linarith)).le
    have h2 : 1 ≤ 2 * (1 / (1 + v ^ 2)) := by
      rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
      nlinarith [pow_le_one₀ hv.le hv1 (n := 2)]
    linarith
  · have h3 : (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p ≤ (v ^ 2)⁻¹ := by
      rw [← h1]; linarith
    have h2 : (v ^ 2)⁻¹ ≤ 2 * (1 / (1 + v ^ 2)) := by
      rw [← mul_div_assoc, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [one_le_pow₀ hv1 (n := 2)]
    linarith

private lemma nm_H_integrable {p : ℝ} (hp : 1 ≤ p) :
    IntegrableOn (fun v : ℝ => (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable (fun v : ℝ => (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p)
      (volume.restrict (Ioi (0:ℝ))) :=
    (nm_H_cont (by linarith : 0 < p)).aestronglyMeasurable measurableSet_Ioi
  have hg : Integrable (fun v : ℝ => 2 * (1 / (1 + v ^ 2))) :=
    integrable_inv_one_add_sq.const_mul 2 |>.congr (Filter.Eventually.of_forall fun v => by simp [one_div])
  refine Integrable.mono' hg.restrict hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun v hv => ?_
  obtain ⟨h0, -, h2⟩ := nm_H_bound hp hv
  rw [Real.norm_eq_abs, abs_of_pos h0]
  exact h2

private lemma nm_layer_H_set {p : ℝ} (hp : 1 ≤ p) {t : ℝ} (ht : 0 < t) :
    (volume.restrict (Ioi (0:ℝ))).real
      {v : ℝ | t < (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p} =
    (Ioo (0:ℝ) 1).indicator (fun t => Qm 0 (t ^ (1 / p)) ^ (-(1:ℝ) / 2)) t := by
  rw [Measure.real, Measure.restrict_apply' measurableSet_Ioi]
  by_cases ht1 : t < 1
  · rw [Set.indicator_of_mem (show t ∈ Ioo (0:ℝ) 1 from ⟨ht, ht1⟩)]
    have hp0 : 0 < p := by linarith
    have hm : t ^ (1 / p) ∈ Ioo (0:ℝ) 1 :=
      ⟨Real.rpow_pos_of_pos ht _, Real.rpow_lt_one ht.le ht1 (by positivity)⟩
    have hQ := (nm_Qm_spec hm).1
    have hset : {v : ℝ | t < (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p} ∩ Ioi 0 =
        Ioo 0 (Qm 0 (t ^ (1 / p)) ^ (-(1:ℝ) / 2)) := by
      ext v
      simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨h, hv⟩
        refine ⟨hv, ?_⟩
        have hq : 0 < v ^ (-(2:ℝ)) := Real.rpow_pos_of_pos hv _
        have hr := nm_r_mem hq
        have h1 : t ^ (1 / p) < v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ))) := by
          have := Real.rpow_lt_rpow ht.le h (by positivity : 0 < 1 / p)
          rwa [← Real.rpow_mul hr.1.le, mul_one_div_cancel hp0.ne', Real.rpow_one] at this
        exact (nm_vq_iff hv hQ).1 ((nm_r_gt_iff hm hq).1 h1)
      · rintro ⟨hv, hlt⟩
        refine ⟨?_, hv⟩
        have hq : 0 < v ^ (-(2:ℝ)) := Real.rpow_pos_of_pos hv _
        have hr := nm_r_mem hq
        have h1 := (nm_r_gt_iff hm hq).2 ((nm_vq_iff hv hQ).2 hlt)
        have := Real.rpow_lt_rpow (Real.rpow_pos_of_pos ht _).le h1 hp0
        rwa [← Real.rpow_mul ht.le, one_div_mul_cancel hp0.ne', Real.rpow_one] at this
    rw [hset, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal (Real.rpow_nonneg hQ.le _)]
  · rw [Set.indicator_of_notMem (show t ∉ Ioo (0:ℝ) 1 from fun h => ht1 h.2)]
    have : {v : ℝ | t < (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p} ∩ Ioi 0 = ∅ := by
      ext v
      simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
      intro h hv
      have := (nm_H_bound hp hv).2.1
      linarith
    rw [this]; simp

private lemma nm_layer_H {p : ℝ} (hp : 1 ≤ p) :
    ∫ v in Ioi (0:ℝ), (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p =
      ∫ t in Ioo (0:ℝ) 1, Qm 0 (t ^ (1 / p)) ^ (-(1:ℝ) / 2) := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun v : ℝ => (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun v hv => (nm_H_bound hp hv).1.le
  rw [Integrable.integral_eq_integral_meas_lt (nm_H_integrable hp) hnn]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => nm_layer_H_set hp ht)]
  rw [setIntegral_indicator measurableSet_Ioo]
  have : Ioi (0:ℝ) ∩ Ioo 0 1 = Ioo 0 1 := by
    ext t; constructor
    · rintro ⟨_, h⟩; exact h
    · rintro h; exact ⟨h.1, h⟩
  rw [this]

private lemma nm_subst_H (p : ℝ) :
    ∫ v in Ioi (0:ℝ), (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p =
      (1 / 2) * ∫ x in Ioi (0:ℝ), x ^ (-(3:ℝ) / 2) * (x * J x) ^ p := by
  have h := integral_comp_rpow_Ioi (fun v : ℝ => (v ^ (-(2:ℝ)) * J (v ^ (-(2:ℝ)))) ^ p)
    (p := -(1:ℝ) / 2) (by norm_num)
  rw [← h, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : 0 < x := hx
  have h1 : (x ^ (-(1:ℝ) / 2)) ^ (-(2:ℝ)) = x := by
    rw [← Real.rpow_mul hx0.le]; norm_num
  simp only [smul_eq_mul]
  rw [h1]
  have h2 : |(-(1:ℝ) / 2)| = 1 / 2 := by norm_num [abs_div]
  rw [h2]
  have h3 : x ^ (-(1:ℝ) / 2 - 1) = x ^ (-(3:ℝ) / 2) := by norm_num
  rw [h3]
  ring

private lemma nm_pointwise_L {ν : ℝ} (hν : 0 < ν) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    (2 * ν / (ν + 1)) * x ^ (2 * ν / (ν + 1) - 1) *
      Real.sqrt (J (Qm 0 ((x ^ (2 * ν / (ν + 1))) ^ (1 / ν))) / x ^ (2 * ν / (ν + 1))) =
    (2 * ν / (ν + 1)) * Qm 0 (x ^ (1 / ((ν + 1) / 2))) ^ (-(1:ℝ) / 2) := by
  set e : ℝ := 2 * ν / (ν + 1) with he
  set p : ℝ := (ν + 1) / 2 with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  have h1 : (x ^ e) ^ (1 / ν) = x ^ (1 / p) := by
    rw [← Real.rpow_mul hx.1.le]
    congr 1
    rw [he, hp]; field_simp
  have hm : x ^ (1 / p) ∈ Ioo (0:ℝ) 1 :=
    ⟨Real.rpow_pos_of_pos hx.1 _, Real.rpow_lt_one hx.1.le hx.2 (by positivity)⟩
  have hQ := (nm_Qm_spec hm).1
  rw [h1, nm_J_Qm hm, mul_assoc]
  congr 1
  have hxe : 0 < x ^ e := Real.rpow_pos_of_pos hx.1 _
  have h2 : x ^ (1 / p) / Qm 0 (x ^ (1 / p)) / x ^ e = x ^ (1 / p - e) / Qm 0 (x ^ (1 / p)) := by
    rw [Real.rpow_sub hx.1]; field_simp
  rw [h2, Real.sqrt_div (Real.rpow_nonneg hx.1.le _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hx.1.le, ← mul_div_assoc]
  have h3 : x ^ (e - 1) * x ^ ((1 / p - e) * (1 / 2)) = 1 := by
    rw [← Real.rpow_add hx.1]
    have : e - 1 + (1 / p - e) * (1 / 2) = 0 := by
      rw [he, hp]; field_simp; ring
    rw [this, Real.rpow_zero]
  rw [h3, show (-(1:ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg hQ.le, one_div]

private lemma nm_subst_L {ν : ℝ} (hν : 0 < ν) :
    ∫ y in Ioo (0:ℝ) 1, Real.sqrt (J (Qm 0 (y ^ (1 / ν))) / y) =
      (2 * ν / (ν + 1)) *
        ∫ t in Ioo (0:ℝ) 1, Qm 0 (t ^ (1 / ((ν + 1) / 2))) ^ (-(1:ℝ) / 2) := by
  set e : ℝ := 2 * ν / (ν + 1) with he
  have he0 : 0 < e := by rw [he]; positivity
  set g : ℝ → ℝ := (Ioo (0:ℝ) 1).indicator (fun y => Real.sqrt (J (Qm 0 (y ^ (1 / ν))) / y)) with hg
  have h := integral_comp_rpow_Ioi_of_pos (g := g) he0
  have hR : ∫ y in Ioi (0:ℝ), g y = ∫ y in Ioo (0:ℝ) 1, Real.sqrt (J (Qm 0 (y ^ (1 / ν))) / y) := by
    rw [hg, setIntegral_indicator measurableSet_Ioo]
    have : Ioi (0:ℝ) ∩ Ioo 0 1 = Ioo 0 1 := by
      ext t; constructor
      · rintro ⟨_, h⟩; exact h
      · rintro h; exact ⟨h.1, h⟩
    rw [this]
  have hinter : Ioi (0:ℝ) ∩ Ioo 0 1 = Ioo 0 1 := by
    ext t; constructor
    · rintro ⟨_, h⟩; exact h
    · rintro h; exact ⟨h.1, h⟩
  have hR2 : ∫ x in Ioi (0:ℝ), (Ioo (0:ℝ) 1).indicator
        (fun t => e * Qm 0 (t ^ (1 / ((ν + 1) / 2))) ^ (-(1:ℝ) / 2)) x =
      e * ∫ t in Ioo (0:ℝ) 1, Qm 0 (t ^ (1 / ((ν + 1) / 2))) ^ (-(1:ℝ) / 2) := by
    rw [setIntegral_indicator measurableSet_Ioo, hinter, integral_const_mul]
  rw [← hR, ← h, ← hR2]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : 0 < x := hx
  by_cases hx1 : x < 1
  · have hxm : x ∈ Ioo (0:ℝ) 1 := ⟨hx0, hx1⟩
    have hxe : x ^ e ∈ Ioo (0:ℝ) 1 :=
      ⟨Real.rpow_pos_of_pos hx0 _, Real.rpow_lt_one hx0.le hx1 he0⟩
    rw [Set.indicator_of_mem hxm, hg, smul_eq_mul, Set.indicator_of_mem hxe]
    exact nm_pointwise_L hν hxm
  · have hxm : x ∉ Ioo (0:ℝ) 1 := fun h => hx1 h.2
    have hxe : x ^ e ∉ Ioo (0:ℝ) 1 := fun h => by
      have := Real.one_le_rpow (not_lt.1 hx1) he0.le
      linarith [h.2]
    rw [Set.indicator_of_notMem hxm, hg, smul_eq_mul, Set.indicator_of_notMem hxe, mul_zero]

private lemma nm_L_identity {ν : ℝ} (hν : 1 ≤ ν) :
    ∫ y in Ioo (0:ℝ) 1, Real.sqrt (J (Qm 0 (y ^ (1 / ν))) / y) =
      (ν / (ν + 1)) * ∫ q in Ioi (0:ℝ), q ^ (-(3:ℝ) / 2) * (q * J q) ^ ((ν + 1) / 2) := by
  have hν0 : 0 < ν := by linarith
  have hp : 1 ≤ (ν + 1) / 2 := by linarith
  rw [nm_subst_L hν0, ← nm_layer_H hp, nm_subst_H]
  have : 2 * ν / (ν + 1) * (1 / 2) = ν / (ν + 1) := by field_simp
  rw [← mul_assoc, this]

private lemma nm_inner_gauss (g : ℝ) :
    ∫ q in Ioi (0:ℝ), q ^ (-(1:ℝ) / 2) * (g ^ 2 / (1 + q * g ^ 2)) = Real.pi * |g| := by
  by_cases hg : g = 0
  · subst hg; simp
  have hgpos : 0 < |g| := abs_pos.2 hg
  have h := integral_comp_rpow_Ioi (fun q : ℝ => q ^ (-(1:ℝ) / 2) * (g ^ 2 / (1 + q * g ^ 2)))
    (p := (2:ℝ)) (by norm_num)
  rw [← h]
  have h1 : ∀ x ∈ Ioi (0:ℝ), (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) •
      (fun q : ℝ => q ^ (-(1:ℝ) / 2) * (g ^ 2 / (1 + q * g ^ 2))) (x ^ (2:ℝ)) =
      2 * g ^ 2 * (1 + (|g| * x) ^ 2)⁻¹ := by
    intro x hx
    have hx0 : 0 < x := hx
    simp only [smul_eq_mul]
    have e1 : (x ^ (2:ℝ)) ^ (-(1:ℝ) / 2) = x⁻¹ := by
      rw [← Real.rpow_mul hx0.le]; norm_num
      exact Real.rpow_neg_one x
    have e2 : x ^ (2:ℝ) = x ^ 2 := by norm_cast
    have e3 : x ^ ((2:ℝ) - 1) = x := by norm_num
    rw [e1, e2, e3, abs_of_pos (by norm_num : (0:ℝ) < 2), mul_pow, sq_abs]
    have : (1 + x ^ 2 * g ^ 2) ≠ 0 := by positivity
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi h1]
  rw [integral_const_mul]
  have h2 := integral_comp_mul_left_Ioi (fun y : ℝ => (1 + y ^ 2)⁻¹) (0:ℝ) hgpos
  rw [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero] at h2
  simp only [smul_eq_mul, sub_zero] at h2
  rw [h2]
  have : g ^ 2 = |g| ^ 2 := (sq_abs g).symm
  rw [this]
  field_simp

private lemma nm_J_pointwise {q : ℝ} (hq : 0 < q) :
    q ^ (-(3:ℝ) / 2) * (q * J q) ^ (((1:ℝ) + 1) / 2) = q ^ (-(1:ℝ) / 2) * J q := by
  have e1 : (((1:ℝ) + 1) / 2) = 1 := by norm_num
  rw [e1, Real.rpow_one, ← mul_assoc]
  congr 1
  have : q ^ (-(3:ℝ) / 2) * q = q ^ (-(3:ℝ) / 2 + 1) := by
    rw [Real.rpow_add hq, Real.rpow_one]
  rw [this]; norm_num

private lemma nm_F_bound {q : ℝ} (hq : 0 < q) (g : ℝ) :
    0 ≤ q ^ (-(1:ℝ) / 2) * (g ^ 2 / (1 + q * g ^ 2)) ∧
    q ^ (-(1:ℝ) / 2) * (g ^ 2 / (1 + q * g ^ 2)) ≤ q ^ (-(1:ℝ) / 2) * (1 / q) := by
  have hq1 : 0 < q ^ (-(1:ℝ) / 2) := Real.rpow_pos_of_pos hq _
  have hd : 0 < 1 + q * g ^ 2 := by positivity
  refine ⟨mul_nonneg hq1.le (div_nonneg (sq_nonneg g) hd.le), ?_⟩
  apply mul_le_mul_of_nonneg_left _ hq1.le
  rw [div_le_div_iff₀ hd hq]
  nlinarith [sq_nonneg g]

private lemma nm_M2 :
    ∫ q in Ioi (0:ℝ), q ^ (-(3:ℝ) / 2) * (q * J q) ^ (((1:ℝ) + 1) / 2) = Real.sqrt (2 * Real.pi) := by
  set F : ℝ → ℝ → ℝ := fun q g => q ^ (-(1:ℝ) / 2) * (g ^ 2 / (1 + q * g ^ 2)) with hF
  have hmeas : Measurable (Function.uncurry F) := by
    unfold Function.uncurry F
    fun_prop
  have hint1 : ∀ q ∈ Ioi (0:ℝ), Integrable (fun g => F q g) (ProbabilityTheory.gaussianReal 0 1) := by
    intro q hq
    have hq0 : 0 < q := hq
    refine Integrable.mono' (integrable_const (q ^ (-(1:ℝ) / 2) * (1 / q)))
      (by unfold F; fun_prop : Measurable fun g => F q g).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun g => ?_
    obtain ⟨h0, h1⟩ := nm_F_bound hq0 g
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  have hnorm : ∀ q ∈ Ioi (0:ℝ), ∫ g, ‖F q g‖ ∂(ProbabilityTheory.gaussianReal 0 1) = q ^ (-(1:ℝ) / 2) * J q := by
    intro q hq
    have hq0 : 0 < q := hq
    have : ∀ g, ‖F q g‖ = q ^ (-(1:ℝ) / 2) * (g ^ 2 / (1 + q * g ^ 2)) := by
      intro g
      rw [Real.norm_eq_abs, abs_of_nonneg (nm_F_bound hq0 g).1]
    simp_rw [this]
    rw [integral_const_mul]
    rfl
  have hint2 : Integrable (fun q => ∫ g, ‖F q g‖ ∂(ProbabilityTheory.gaussianReal 0 1)) (volume.restrict (Ioi 0)) := by
    have h := nm_integrand_integrable (α := 1) one_pos
    refine h.congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun q hq => ?_
    rw [hnorm q hq]
    exact nm_J_pointwise hq
  have hprod : Integrable (Function.uncurry F) ((volume.restrict (Ioi (0:ℝ))).prod (ProbabilityTheory.gaussianReal 0 1)) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨?_, hint2⟩
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall hint1
  have hswap := integral_integral_swap hprod
  have hL : ∫ q in Ioi (0:ℝ), q ^ (-(3:ℝ) / 2) * (q * J q) ^ (((1:ℝ) + 1) / 2) =
      ∫ q in Ioi (0:ℝ), ∫ g, F q g ∂(ProbabilityTheory.gaussianReal 0 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun q hq => ?_)
    rw [nm_J_pointwise hq]
    simp only [hF]
    rw [integral_const_mul]
    rfl
  rw [hL]
  rw [hswap]
  simp only [hF]
  have : ∀ g : ℝ, ∫ q in Ioi (0:ℝ), q ^ (-(1:ℝ) / 2) * (g ^ 2 / (1 + q * g ^ 2)) = Real.pi * |g| :=
    nm_inner_gauss
  simp_rw [this]
  rw [integral_const_mul, Muon.Foundations.gaussian_abs_moment]
  rw [Real.sqrt_div (by norm_num), Real.sqrt_mul (by norm_num)]
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  have h2 : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith [h2]

private lemma nm_const {α : ℝ} (hα : 0 < α) :
    (2 / Real.pi) * ∫ y in Ioo (0:ℝ) 1,
      Real.sqrt (J (Qm 0 (y ^ (1 / (if α ≤ 1 then (1:ℝ) else α)))) / y) = aAlpha α := by
  unfold aAlpha
  split_ifs with h
  · rw [nm_L_identity (le_refl (1:ℝ)), nm_M2]
    unfold c0
    have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
    have h2 : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    have hs2 : Real.sqrt 2 ≠ 0 := by positivity
    rw [Real.sqrt_div (by norm_num), Real.sqrt_mul (by norm_num)]
    field_simp
    nlinarith [h2]
  · have hgt : 1 ≤ α := by linarith [not_le.1 h]
    rw [nm_L_identity hgt]
    have : α + 1 ≠ 0 := by linarith
    field_simp

private lemma nm_Lam_integral {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) :
    ∫ u in Ioi (0:ℝ), partLam B μ (mOf0 B μ (u ^ 2)) =
      Real.sqrt (partLam B μ 1 * gammaOf N B) *
        ∫ y in Ioo (0:ℝ) 1, Real.sqrt
          ((partLam B μ 1 / gammaOf N B) * sN 0 B μ (partMN B μ (partLam B μ 1 * y))) := by
  have hbij := def_app_pl_participation_bij μ hB hN hpos
  have hκ : 0 < partLam B μ 1 := hbij.2.1.mapsTo ⟨one_pos, hγ⟩
  have hg : 0 < gammaOf N B := lt_trans one_pos hγ
  have h1 := nm_layer_n μ hB hN hpos hγ
  rw [setIntegral_indicator measurableSet_Ioo] at h1
  have hinter : Ioi (0:ℝ) ∩ Ioo 0 1 = Ioo 0 1 := by
    ext t; constructor
    · rintro ⟨_, h⟩; exact h
    · rintro h; exact ⟨h.1, h⟩
  rw [hinter] at h1
  have h2 : ∫ u in Ioi (0:ℝ), partLam B μ (mOf0 B μ (u ^ 2)) =
      partLam B μ 1 * ∫ u in Ioi (0:ℝ), partLam B μ (mOf0 B μ (u ^ 2)) / partLam B μ 1 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    field_simp
  rw [h2, h1, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo (fun y hy => ?_)
  have hS := (nm_sN_pos μ hB hN hpos hγ (nm_Mn_lt_one μ hB hN hpos hγ hy))
  rw [← Real.sqrt_mul (mul_pos hκ hg).le]
  have : partLam B μ 1 * gammaOf N B * (partLam B μ 1 / gammaOf N B *
      sN 0 B μ (partMN B μ (partLam B μ 1 * y))) =
      partLam B μ 1 ^ 2 * sN 0 B μ (partMN B μ (partLam B μ 1 * y)) := by
    field_simp
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ.le]

private lemma nm_const_alg {κ γ : ℝ} (hκ : 0 < κ) (hγ : 0 < γ) :
    Real.sqrt 2 / (Real.pi * γ) * Real.sqrt (κ * γ) = (2 / Real.pi) * Real.sqrt (κ / (2 * γ)) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hg : Real.sqrt γ ^ 2 = γ := Real.sq_sqrt hγ.le
  rw [Real.sqrt_mul hκ.le, Real.sqrt_div hκ.le, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hsg : 0 < Real.sqrt γ := by positivity
  have hpi := Real.pi_pos
  field_simp
  nlinarith [h2, hg]

private lemma nm_B_bounds {N B : ℕ} (μ : Fin N → ℝ) (hpos : ∀ j, 0 < μ j) (hB : 0 < B)
    (hN : 0 < N) (hγ : 1 < gammaOf N B) (i : Fin N) (κ T : ℝ) (hκd : κ = partLam B μ 1)
    (hTd : T = ∫ y in Ioo (0:ℝ) 1, Real.sqrt ((κ / gammaOf N B) *
      sN 0 B μ (partMN B μ (κ * y)))) :
    (2 / Real.pi) * T * (μ i * Real.sqrt (κ / (2 * gammaOf N B))) / (1 + κ * μ i) ≤ dZero0 B μ i ∧
      dZero0 B μ i ≤ (2 / Real.pi) * T * (μ i * Real.sqrt (κ / (2 * gammaOf N B))) := by
  have hbij := def_app_pl_participation_bij μ hB hN hpos
  have hκ : 0 < κ := by rw [hκd]; exact hbij.2.1.mapsTo ⟨one_pos, hγ⟩
  have hg : 0 < gammaOf N B := lt_trans one_pos hγ
  have ha := hpos i
  have hLamI : IntegrableOn (fun u : ℝ => partLam B μ (mOf0 B μ (u ^ 2))) (Ioi 0) := by
    have := (nm_f_integrable μ hB hN hpos hγ).const_mul (partLam B μ 1)
    refine Integrable.congr this ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun u _ => ?_
    have hκ' : partLam B μ 1 ≠ 0 := by rw [← hκd]; exact hκ.ne'
    field_simp
  have hGI := nm_Gfun0_int μ hB hN hpos hγ i (τ := fun u => u ^ 2)
    (fun a ha b hb hab => pow_le_pow_left₀ ha.le hab 2) (fun _ _ => le_rfl)
  have hLamEq : ∫ u in Ioi (0:ℝ), partLam B μ (mOf0 B μ (u ^ 2)) =
      Real.sqrt (κ * gammaOf N B) * T := by
    rw [hTd, hκd]; exact nm_Lam_integral μ hB hN hpos hγ
  have hcalg := nm_const_alg hκ hg
  have hup : ∫ u in Ioi (0:ℝ), Gfun0 B μ i (u ^ 2) ≤
      μ i * ∫ u in Ioi (0:ℝ), partLam B μ (mOf0 B μ (u ^ 2)) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hGI (hLamI.const_mul _) measurableSet_Ioi (fun u hu => ?_)
    have hs : 0 < u ^ 2 := pow_pos hu 2
    rw [nm_Gfun0_eq μ hB hN hpos hγ i hs]
    have := (nm_f0_facts μ hB hN hpos hγ i hs).2.2
    linarith [mul_comm (partLam B μ (mOf0 B μ (u ^ 2))) (μ i)]
  have hlo : (μ i / (1 + κ * μ i)) * ∫ u in Ioi (0:ℝ), partLam B μ (mOf0 B μ (u ^ 2)) ≤
      ∫ u in Ioi (0:ℝ), Gfun0 B μ i (u ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hLamI.const_mul _) hGI measurableSet_Ioi (fun u hu => ?_)
    have hs : 0 < u ^ 2 := pow_pos hu 2
    rw [nm_Gfun0_eq μ hB hN hpos hγ i hs]
    obtain ⟨hm, -⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
    have hL : 0 < partLam B μ (mOf0 B μ (u ^ 2)) := hbij.2.1.mapsTo ⟨hm.1, hm.2.trans hγ⟩
    have hLk : partLam B μ (mOf0 B μ (u ^ 2)) < κ := by
      rw [hκd]; exact nm_Lam_mOf0_lt μ hB hN hpos hγ hs
    unfold partF
    rw [div_mul_eq_mul_div, mul_comm (μ i) _, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hL ha, mul_pos (mul_pos hL ha) ha]
  have hI0 : dZero0 B μ i = Real.sqrt 2 / (Real.pi * gammaOf N B) *
      ∫ u in Ioi (0:ℝ), Gfun0 B μ i (u ^ 2) := rfl
  have hc0 : 0 < Real.sqrt 2 / (Real.pi * gammaOf N B) := by positivity
  rw [hLamEq] at hup hlo
  constructor
  · rw [hI0]
    calc (2 / Real.pi) * T * (μ i * Real.sqrt (κ / (2 * gammaOf N B))) / (1 + κ * μ i)
        = (Real.sqrt 2 / (Real.pi * gammaOf N B) * Real.sqrt (κ * gammaOf N B)) * T *
            (μ i / (1 + κ * μ i)) := by
          rw [hcalg]; ring
      _ = Real.sqrt 2 / (Real.pi * gammaOf N B) *
            ((μ i / (1 + κ * μ i)) * (Real.sqrt (κ * gammaOf N B) * T)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hc0.le
  · rw [hI0]
    calc _ ≤ Real.sqrt 2 / (Real.pi * gammaOf N B) * (μ i * (Real.sqrt (κ * gammaOf N B) * T)) :=
          mul_le_mul_of_nonneg_left hup hc0.le
      _ = (Real.sqrt 2 / (Real.pi * gammaOf N B) * Real.sqrt (κ * gammaOf N B)) * T * μ i := by ring
      _ = _ := by rw [hcalg]; ring

private lemma nm_caseB {α : ℝ} (hα : 0 < α) (N B : ℕ → ℕ) (hB : Tendsto B atTop atTop)
    (hγ : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop)
    (hN0 : ∀ n, 0 < N n) (hB0 : ∀ n, 0 < B n)
    (k : (n : ℕ) → Fin (N n))
    (hrow : Tendsto (fun n => kappaOf α 1 (N n) (B n) * plSpec α 1 (N n) (k n)) atTop (𝓝 0)) :
    IsEquivalent atTop (fun n => dZero0 (B n) (plSpec α 1 (N n)) (k n))
      (fun n => aAlpha α * plSpec α 1 (N n) (k n) *
        Real.sqrt (kappaOf α 1 (N n) (B n) / (2 * gammaOf (N n) (B n)))) := by
  have hpos : ∀ n j, 0 < plSpec α 1 (N n) j := by
    intro n j; unfold plSpec; positivity
  have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) := hγ.eventually_gt_atTop 1
  have hA := (eqn_app_pl_A_alpha_wf hα).1
  have hT : Tendsto (fun n => ∫ y in Ioo (0:ℝ) 1, Real.sqrt
        ((kappaOf α 1 (N n) (B n) / gammaOf (N n) (B n)) *
        sN 0 (B n) (plSpec α 1 (N n))
          (partMN (B n) (plSpec α 1 (N n)) (kappaOf α 1 (N n) (B n) * y)))) atTop
      (𝓝 (∫ y in Ioo (0:ℝ) 1, Real.sqrt (J (Qm 0 (y ^ (1 / (if α ≤ 1 then (1:ℝ) else α)))) / y))) :=
    nm_dct_y hα N B hN0 hB0 hB hγ
  have hTc : Tendsto (fun n => (2 / Real.pi) * ∫ y in Ioo (0:ℝ) 1, Real.sqrt
        ((kappaOf α 1 (N n) (B n) / gammaOf (N n) (B n)) *
        sN 0 (B n) (plSpec α 1 (N n))
          (partMN (B n) (plSpec α 1 (N n)) (kappaOf α 1 (N n) (B n) * y)))) atTop
      (𝓝 (aAlpha α)) := by
    rw [← nm_const hα]
    exact hT.const_mul _
  have hden : Tendsto (fun n => (1 + kappaOf α 1 (N n) (B n) * plSpec α 1 (N n) (k n))⁻¹) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).add hrow).inv₀ (by norm_num)
  set R : ℕ → ℝ := fun n => dZero0 (B n) (plSpec α 1 (N n)) (k n) /
    (plSpec α 1 (N n) (k n) * Real.sqrt (kappaOf α 1 (N n) (B n) / (2 * gammaOf (N n) (B n)))) with hR
  have hRlim : Tendsto R atTop (𝓝 (aAlpha α)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hTc.mul hden) hTc ?_ ?_
    · filter_upwards [hγ1] with n hn
      obtain ⟨h1, -⟩ := nm_B_bounds (plSpec α 1 (N n)) (hpos n) (hB0 n) (hN0 n) hn (k n)
        (kappaOf α 1 (N n) (B n)) _ rfl rfl
      have hg : 0 < gammaOf (N n) (B n) := lt_trans one_pos hn
      have hq : 0 < plSpec α 1 (N n) (k n) * Real.sqrt (kappaOf α 1 (N n) (B n) / (2 * gammaOf (N n) (B n))) := by
        have := hpos n (k n)
        have hκ : 0 < kappaOf α 1 (N n) (B n) :=
          (prop_app_pl_scales_i 1 hα (hN0 n) (hB0 n) one_pos hn).1
        positivity
      rw [hR]
      dsimp only
      rw [le_div_iff₀ hq]
      refine le_trans (le_of_eq ?_) h1
      rw [div_eq_mul_inv]; ring
    · filter_upwards [hγ1] with n hn
      obtain ⟨-, h2⟩ := nm_B_bounds (plSpec α 1 (N n)) (hpos n) (hB0 n) (hN0 n) hn (k n)
        (kappaOf α 1 (N n) (B n)) _ rfl rfl
      have hq : 0 < plSpec α 1 (N n) (k n) * Real.sqrt (kappaOf α 1 (N n) (B n) / (2 * gammaOf (N n) (B n))) := by
        have := hpos n (k n)
        have hκ : 0 < kappaOf α 1 (N n) (B n) :=
          (prop_app_pl_scales_i 1 hα (hN0 n) (hB0 n) one_pos hn).1
        have hg : 0 < gammaOf (N n) (B n) := lt_trans one_pos hn
        positivity
      rw [hR]
      dsimp only
      rw [div_le_iff₀ hq]
      exact h2
  refine isEquivalent_of_tendsto_one ?_
  have h1 := hRlim.div_const (aAlpha α)
  rw [div_self hA.ne'] at h1
  refine h1.congr' ?_
  filter_upwards [hγ1] with n hn
  have hg : 0 < gammaOf (N n) (B n) := lt_trans one_pos hn
  have hq : 0 < plSpec α 1 (N n) (k n) * Real.sqrt (kappaOf α 1 (N n) (B n) / (2 * gammaOf (N n) (B n))) := by
    have := hpos n (k n)
    have hκ : 0 < kappaOf α 1 (N n) (B n) :=
      (prop_app_pl_scales_i 1 hα (hN0 n) (hB0 n) one_pos hn).1
    positivity
  simp only [hR, Pi.div_apply]
  field_simp

private lemma nm_Qm_zero : Tendsto (Qm 0) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with δ hδ
    exact ha.trans_le (nm_Qm_spec hδ).1.le |>.trans_le le_rfl
  · intro b hb
    have hr := nm_r_mem hb
    filter_upwards [Ioo_mem_nhdsGT hr.1] with δ hδ
    have hδ1 : δ ∈ Ioo (0:ℝ) 1 := ⟨hδ.1, hδ.2.trans hr.2⟩
    exact (nm_r_gt_iff hδ1 hb).1 hδ.2

private lemma nm_ell : Tendsto (fun δ : ℝ => (1 - δ) * J (Qm 0 δ)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have h1 : Tendsto (fun δ : ℝ => 1 - δ) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have : Tendsto (fun δ : ℝ => 1 - δ) (𝓝 (0:ℝ)) (𝓝 (1 - 0)) :=
      (continuous_const.sub continuous_id).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun δ : ℝ => J (Qm 0 δ)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have hJ : ContinuousWithinAt J (Ici 0) 0 := lem_app_de_scalar_i.1 0 (Set.mem_Ici.2 le_rfl)
    have hQ : Tendsto (Qm 0) (𝓝[>] (0:ℝ)) (𝓝[Ici 0] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨nm_Qm_zero, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with δ hδ
      exact (nm_Qm_spec hδ).1.le
    have := hJ.tendsto.comp hQ
    rw [lem_app_de_scalar_i.2.2.2.2.2] at this
    exact this
  simpa using h1.mul h2

private lemma nm_beta_form {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) (i : Fin N) {s : ℝ} (hs : 0 < s) :
    Gfun0 B μ i s = (partLam B μ (mOf0 B μ s) * s / gammaOf N B) /
      (s / (gammaOf N B * μ i) + partLam B μ (mOf0 B μ s) * s / gammaOf N B) := by
  rw [nm_Gfun0_eq μ hB hN hpos hγ i hs]
  obtain ⟨hm, -⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
  have hL : 0 < partLam B μ (mOf0 B μ s) :=
    (def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo ⟨hm.1, hm.2.trans hγ⟩
  have hg : 0 < gammaOf N B := lt_trans one_pos hγ
  have ha := hpos i
  unfold partF
  field_simp

private lemma nm_beta_eq {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) {s : ℝ} (hs : 0 < s) :
    partLam B μ (mOf0 B μ s) * s / gammaOf N B =
      (1 - mOf0 B μ s / gammaOf N B) * J (Qm 0 (mOf0 B μ s)) := by
  rw [nm_Lam_mul_s μ hB hN hpos hγ hs]
  have hg : 0 < gammaOf N B := lt_trans one_pos hγ
  field_simp

private lemma nm_beta_bounds {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) {s : ℝ} (hs : 0 < s) :
    0 < partLam B μ (mOf0 B μ s) * s / gammaOf N B ∧
      partLam B μ (mOf0 B μ s) * s / gammaOf N B ≤ 1 := by
  obtain ⟨hm, -⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
  have hL : 0 < partLam B μ (mOf0 B μ s) :=
    (def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo ⟨hm.1, hm.2.trans hγ⟩
  have hg : 0 < gammaOf N B := lt_trans one_pos hγ
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hg]
  exact nm_Lam_mul_s_le μ hB hN hpos hγ hs

private lemma nm_beta_lower {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) {s δ : ℝ} (hs : 0 < s)
    (hδ : δ ∈ Ioo (0:ℝ) 1) (hsδ : sN 0 B μ δ ≤ s) :
    (1 - δ) * J (Qm 0 δ) ≤ partLam B μ (mOf0 B μ s) * s / gammaOf N B := by
  rw [nm_beta_eq μ hB hN hpos hγ hs]
  obtain ⟨hm, -⟩ := nm_mOf0_spec μ hB hN hpos hγ hs
  have hg : 0 < gammaOf N B := lt_trans one_pos hγ
  have hle : mOf0 B μ s ≤ δ := by
    by_contra h
    push_neg at h
    have := (nm_mOf0_gt_iff μ hB hN hpos hγ hs hδ).1 h
    linarith
  have hQ : Qm 0 (mOf0 B μ s) ≤ Qm 0 δ := nm_Qm_mono.monotoneOn hm hδ hle
  have hJ : J (Qm 0 δ) ≤ J (Qm 0 (mOf0 B μ s)) :=
    lem_app_de_scalar_i.2.1.antitoneOn (nm_Qm_spec hm).1.le (nm_Qm_spec hδ).1.le hQ
  have hJ0 := (lem_app_de_scalar_i.2.2.1 _ (nm_Qm_spec hδ).1.le).1
  have h1 : 1 - δ ≤ 1 - mOf0 B μ s / gammaOf N B := by
    have : mOf0 B μ s / gammaOf N B ≤ mOf0 B μ s := div_le_self hm.1.le hγ.le
    linarith
  have h0 : 0 ≤ 1 - δ := by linarith [hδ.2]
  exact mul_le_mul h1 hJ hJ0.le (by linarith [h1])

private lemma nm_sN_le {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) {δ : ℝ} (hδ : δ ∈ Ioo (0:ℝ) 1) :
    sN 0 B μ δ ≤ gammaOf N B / partLam B μ δ := by
  rw [nm_sN_alt μ hδ]
  have hL : 0 < partLam B μ δ :=
    (def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo ⟨hδ.1, hδ.2.trans hγ⟩
  apply div_le_div_of_nonneg_right _ hL.le
  have hJ := lem_app_de_scalar_i.2.2.1 (Qm 0 δ) (nm_Qm_spec hδ).1.le
  calc _ ≤ (gammaOf N B - δ) * 1 := mul_le_mul_of_nonneg_left hJ.2 (by linarith [hδ.2])
    _ ≤ gammaOf N B := by linarith [hδ.1]

private lemma nm_beta_limit {α : ℝ} (hα : 0 < α) (N B : ℕ → ℕ) (hN0 : ∀ n, 0 < N n)
    (hB0 : ∀ n, 0 < B n) (hB : Tendsto B atTop atTop)
    (hγ : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop)
    (k : (n : ℕ) → Fin (N n))
    (hrow : Tendsto (fun n => kappaOf α 1 (N n) (B n) * plSpec α 1 (N n) (k n)) atTop atTop)
    {w : ℝ} (hw : 0 < w) :
    Tendsto (fun n => partLam (B n) (plSpec α 1 (N n))
        (mOf0 (B n) (plSpec α 1 (N n)) (gammaOf (N n) (B n) * plSpec α 1 (N n) (k n) * w ^ 2)) *
        (gammaOf (N n) (B n) * plSpec α 1 (N n) (k n) * w ^ 2) / gammaOf (N n) (B n))
      atTop (𝓝 1) := by
  have hpos : ∀ n j, 0 < plSpec α 1 (N n) j := by
    intro n j; unfold plSpec; positivity
  have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) := hγ.eventually_gt_atTop 1
  have hspos : ∀ᶠ n in atTop, 0 < gammaOf (N n) (B n) * plSpec α 1 (N n) (k n) * w ^ 2 := by
    filter_upwards [hγ1] with n hn
    have := hpos n (k n)
    have : 0 < gammaOf (N n) (B n) := lt_trans one_pos hn
    positivity
  rw [tendsto_order]
  constructor
  · intro a' ha'
    obtain ⟨δ, hδ1, hδ2⟩ := ((nm_ell.eventually (lt_mem_nhds ha')).and
      (Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1))).exists
    have hδ : δ ∈ Ioo (0:ℝ) 1 := hδ2
    have hlim := nm_scale_limit hα N B hN0 hB0 hB hγ (m := δ) ⟨hδ.1, hδ.2.le⟩
    have hdpos : 0 < δ ^ (if α ≤ 1 then (1:ℝ) else α) := Real.rpow_pos_of_pos hδ.1 _
    have hprod := (hlim.pos_mul_atTop hdpos hrow)
    have hprod2 := (hprod.atTop_mul_const (by positivity : 0 < w ^ 2))
    filter_upwards [hγ1, hspos, hprod2.eventually_ge_atTop 1] with n hn hs h1
    have hbij := def_app_pl_participation_bij (plSpec α 1 (N n)) (hB0 n) (hN0 n) (hpos n)
    have hκ : 0 < kappaOf α 1 (N n) (B n) :=
      (prop_app_pl_scales_i 1 hα (hN0 n) (hB0 n) one_pos hn).1
    have hLδ : 0 < partLam (B n) (plSpec α 1 (N n)) δ := hbij.2.1.mapsTo ⟨hδ.1, hδ.2.trans hn⟩
    have hg : 0 < gammaOf (N n) (B n) := lt_trans one_pos hn
    have hsN := nm_sN_le (plSpec α 1 (N n)) (hB0 n) (hN0 n) (hpos n) hn hδ
    have hle : sN 0 (B n) (plSpec α 1 (N n)) δ ≤
        gammaOf (N n) (B n) * plSpec α 1 (N n) (k n) * w ^ 2 := by
      refine hsN.trans ?_
      rw [div_le_iff₀ hLδ]
      have e : partLam (B n) (plSpec α 1 (N n)) δ / kappaOf α 1 (N n) (B n) *
          (kappaOf α 1 (N n) (B n) * plSpec α 1 (N n) (k n)) * w ^ 2 =
          partLam (B n) (plSpec α 1 (N n)) δ * plSpec α 1 (N n) (k n) * w ^ 2 := by
        field_simp
      have h1' : 1 ≤ partLam (B n) (plSpec α 1 (N n)) δ * plSpec α 1 (N n) (k n) * w ^ 2 := by
        rw [← e]; exact h1
      nlinarith [h1', hg]
    have := nm_beta_lower (plSpec α 1 (N n)) (hB0 n) (hN0 n) (hpos n) hn hs hδ hle
    exact lt_of_lt_of_le hδ1 this
  · intro b hb
    filter_upwards [hγ1, hspos] with n hn hs
    exact lt_of_le_of_lt (nm_beta_bounds (plSpec α 1 (N n)) (hB0 n) (hN0 n) (hpos n) hn hs).2 hb

private lemma nm_F_anti {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) (i : Fin N) {c : ℝ} (hc : 0 < c) :
    AntitoneOn (fun w : ℝ => Gfun0 B μ i ((c * w) ^ 2)) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : 0 < (c * a) ^ 2 := by have : 0 < c * a := mul_pos hc ha; positivity
  have hb' : 0 < (c * b) ^ 2 := by have : 0 < c * b := mul_pos hc hb; positivity
  show Gfun0 B μ i ((c * b) ^ 2) ≤ Gfun0 B μ i ((c * a) ^ 2)
  rw [nm_Gfun0_eq μ hB hN hpos hγ i ha', nm_Gfun0_eq μ hB hN hpos hγ i hb']
  exact nm_f0_anti μ hB hN hpos hγ i ha' (pow_le_pow_left₀ (mul_pos hc ha).le
    (mul_le_mul_of_nonneg_left hab hc.le) 2)

private lemma nm_F_eq {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) (i : Fin N) {w : ℝ} (hw : 0 < w) :
    Gfun0 B μ i ((Real.sqrt (gammaOf N B * μ i) * w) ^ 2) =
      (partLam B μ (mOf0 B μ (gammaOf N B * μ i * w ^ 2)) * (gammaOf N B * μ i * w ^ 2) /
          gammaOf N B) /
        (w ^ 2 + partLam B μ (mOf0 B μ (gammaOf N B * μ i * w ^ 2)) *
          (gammaOf N B * μ i * w ^ 2) / gammaOf N B) := by
  have hg : 0 < gammaOf N B := lt_trans one_pos hγ
  have ha := hpos i
  have hsq : (Real.sqrt (gammaOf N B * μ i) * w) ^ 2 = gammaOf N B * μ i * w ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [hsq]
  have hs : 0 < gammaOf N B * μ i * w ^ 2 := by positivity
  rw [nm_beta_form μ hB hN hpos hγ i hs]
  congr 2
  field_simp

private lemma nm_F_le {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (hγ : 1 < gammaOf N B) (i : Fin N) {w : ℝ} (hw : 0 < w) :
    0 ≤ Gfun0 B μ i ((Real.sqrt (gammaOf N B * μ i) * w) ^ 2) ∧
    Gfun0 B μ i ((Real.sqrt (gammaOf N B * μ i) * w) ^ 2) ≤ (1 + w ^ 2)⁻¹ := by
  have hg : 0 < gammaOf N B := lt_trans one_pos hγ
  have ha := hpos i
  have hs : 0 < gammaOf N B * μ i * w ^ 2 := by positivity
  obtain ⟨hb0, hb1⟩ := nm_beta_bounds μ hB hN hpos hγ hs
  rw [nm_F_eq μ hB hN hpos hγ i hw]
  set β := partLam B μ (mOf0 B μ (gammaOf N B * μ i * w ^ 2)) *
    (gammaOf N B * μ i * w ^ 2) / gammaOf N B
  have hw2 : 0 < w ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg hb0.le hw2.le]

private lemma nm_caseA {α : ℝ} (hα : 0 < α) (N B : ℕ → ℕ) (hB : Tendsto B atTop atTop)
    (hγ : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop)
    (hN0 : ∀ n, 0 < N n) (hB0 : ∀ n, 0 < B n)
    (k : (n : ℕ) → Fin (N n))
    (hrow : Tendsto (fun n => kappaOf α 1 (N n) (B n) * plSpec α 1 (N n) (k n)) atTop atTop) :
    IsEquivalent atTop (fun n => dZero0 (B n) (plSpec α 1 (N n)) (k n))
      (fun n => Real.sqrt (plSpec α 1 (N n) (k n) / (2 * gammaOf (N n) (B n)))) := by
  have hpos : ∀ n j, 0 < plSpec α 1 (N n) j := by
    intro n j; unfold plSpec; positivity
  have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) := hγ.eventually_gt_atTop 1
  -- DCT
  have hdct : Tendsto (fun n => ∫ w in Ioi (0:ℝ), Gfun0 (B n) (plSpec α 1 (N n)) (k n)
        ((Real.sqrt (gammaOf (N n) (B n) * plSpec α 1 (N n) (k n)) * w) ^ 2)) atTop
      (𝓝 (∫ w in Ioi (0:ℝ), (1 + w ^ 2)⁻¹)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun w => (1 + w ^ 2)⁻¹) ?_ ?_ ?_ ?_
    · filter_upwards [hγ1] with n hn
      have hg : 0 < gammaOf (N n) (B n) := lt_trans one_pos hn
      have hc : 0 < Real.sqrt (gammaOf (N n) (B n) * plSpec α 1 (N n) (k n)) := by
        have := hpos n (k n); positivity
      exact (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi
        (nm_F_anti _ (hB0 n) (hN0 n) (hpos n) hn (k n) hc)).aestronglyMeasurable
    · filter_upwards [hγ1] with n hn
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun w hw => ?_
      obtain ⟨h0, h1⟩ := nm_F_le _ (hB0 n) (hN0 n) (hpos n) hn (k n) hw
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1
    · exact integrable_inv_one_add_sq.restrict
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun w hw => ?_
      have hbl := nm_beta_limit hα N B hN0 hB0 hB hγ k hrow hw
      have hw0 : 0 < w := hw
      have hw2 : 0 < w ^ 2 := by positivity
      have hcont : ContinuousAt (fun x : ℝ => x / (w ^ 2 + x)) 1 := by
        refine continuousAt_id.div (continuousAt_const.add continuousAt_id) ?_
        show w ^ 2 + 1 ≠ 0
        positivity
      have := hcont.tendsto.comp hbl
      have e : (1:ℝ) / (w ^ 2 + 1) = (1 + w ^ 2)⁻¹ := by rw [one_div, add_comm]
      simp only [Function.comp_def, e] at this
      refine this.congr' ?_
      filter_upwards [hγ1] with n hn
      exact (nm_F_eq _ (hB0 n) (hN0 n) (hpos n) hn (k n) hw).symm
  rw [integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero] at hdct
  -- ratio
  set R : ℕ → ℝ := fun n => dZero0 (B n) (plSpec α 1 (N n)) (k n) /
    Real.sqrt (plSpec α 1 (N n) (k n) / (2 * gammaOf (N n) (B n))) with hR
  have hRlim : Tendsto R atTop (𝓝 1) := by
    have h2 := hdct.const_mul (2 / Real.pi)
    have e : 2 / Real.pi * (Real.pi / 2) = 1 := by
      have := Real.pi_pos; field_simp
    rw [e] at h2
    refine h2.congr' ?_
    filter_upwards [hγ1] with n hn
    have hg : 0 < gammaOf (N n) (B n) := lt_trans one_pos hn
    have ha := hpos n (k n)
    have hc : 0 < Real.sqrt (gammaOf (N n) (B n) * plSpec α 1 (N n) (k n)) := by positivity
    have hint := integral_comp_mul_left_Ioi (fun u : ℝ => Gfun0 (B n) (plSpec α 1 (N n)) (k n) (u ^ 2))
      (0:ℝ) hc
    rw [mul_zero] at hint
    simp only [smul_eq_mul] at hint
    have hI : ∫ u in Ioi (0:ℝ), Gfun0 (B n) (plSpec α 1 (N n)) (k n) (u ^ 2) =
        Real.sqrt (gammaOf (N n) (B n) * plSpec α 1 (N n) (k n)) *
          ∫ w in Ioi (0:ℝ), Gfun0 (B n) (plSpec α 1 (N n)) (k n)
            ((Real.sqrt (gammaOf (N n) (B n) * plSpec α 1 (N n) (k n)) * w) ^ 2) := by
      rw [hint]; field_simp
    have hcalg := nm_const_alg ha hg
    simp only [hR]
    show _ = dZero0 (B n) (plSpec α 1 (N n)) (k n) /
      Real.sqrt (plSpec α 1 (N n) (k n) / (2 * gammaOf (N n) (B n)))
    have hq : 0 < Real.sqrt (plSpec α 1 (N n) (k n) / (2 * gammaOf (N n) (B n))) := by positivity
    unfold dZero0
    rw [hI, eq_div_iff hq.ne']
    rw [mul_comm (plSpec α 1 (N n) (k n)) (gammaOf (N n) (B n))] at hcalg
    calc _ = (Real.sqrt 2 / (Real.pi * gammaOf (N n) (B n)) *
          Real.sqrt (gammaOf (N n) (B n) * plSpec α 1 (N n) (k n))) *
          ∫ w in Ioi (0:ℝ), Gfun0 (B n) (plSpec α 1 (N n)) (k n)
            ((Real.sqrt (gammaOf (N n) (B n) * plSpec α 1 (N n) (k n)) * w) ^ 2) := by
          rw [hcalg]; ring
      _ = _ := by ring
  refine isEquivalent_of_tendsto_one ?_
  refine hRlim.congr' ?_
  filter_upwards [hγ1] with n hn
  rfl


/-- `prop:app-pl-nomomentum-endpoints`(ii), snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex`
l.1083–1100 (the whole environment):

\begin{proposition}[No-momentum endpoints]\label{prop:app-pl-nomomentum-endpoints}
Let $\bmom=0$, let $\alpha>0$ be fixed, and let $N,B\to\infty$ with $\gamma=N/B\to\infty$,
$\Sigmain=\Id_N$, $\Nout=\Nin=N$ and $\mu_i=i^{-\alpha}$. For $\gamma>1$ let $\resscale$ and
$i_\#=\resscale^{1/\alpha}$ be as in \cref{prop:app-pl-scales}. At each such dimension the
limits $\mathfrak d_i(0)\defeq\lim_{\ridge\downarrow0}\mathfrak d_i(\ridge)$ and
$\mathfrak v_i(0)\defeq\lim_{\ridge\downarrow0}\mathfrak v_i(\ridge)$ exist, and:
\begin{enumerate}[label=(\roman*)]
\item for every $i$,
\[
\mathfrak v_i(0)=\frac{\resscale\mu_i}{1+\resscale\mu_i}=\frac1{1+(i/i_\#)^\alpha},\qquad \sum_{i=1}^N\mathfrak v_i(0)=B ;
\]
\item for every row sequence $1\le i=i_N\le N$,
\[
\frac{i}{i_\#}\to0\ \Longrightarrow\ \mathfrak d_i(0)\sim\sqrt{\frac{\mu_i}{2\gamma}},\qquad
\frac{i}{i_\#}\to\infty\ \Longrightarrow\ \mathfrak d_i(0)\sim A_\alpha\,\mu_i\sqrt{\frac{\resscale}{2\gamma}} .
\]
\end{enumerate}
\end{proposition}

Part (ii) holds for every row sequence `k`; `i → ∞` is not required. The first conjunct is the case
`i/i_# → 0`, the second the case `i/i_# → ∞`. Here `𝔡_i(0)` is `dZero0` (its existence as the ϱ↓0 limit is
`prop_app_pl_nomomentum_endpoints_drift_limit`). The regime is `N, B → ∞` with `γ → ∞`. -/
theorem prop_app_pl_nomomentum_endpoints_ii {α : ℝ} (hα : 0 < α)
    (N B : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hB : Tendsto B atTop atTop)
    (hγ : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop)
    (hN0 : ∀ n, 0 < N n) (hB0 : ∀ n, 0 < B n)
    (k : (n : ℕ) → Fin (N n)) :
    (Tendsto (fun n => rowNum (k n) / iSharp α 1 (N n) (B n)) atTop (𝓝 0) →
      IsEquivalent atTop (fun n => dZero0 (B n) (plSpec α 1 (N n)) (k n))
        (fun n => Real.sqrt (plSpec α 1 (N n) (k n) / (2 * gammaOf (N n) (B n))))) ∧
    (Tendsto (fun n => rowNum (k n) / iSharp α 1 (N n) (B n)) atTop atTop →
      IsEquivalent atTop (fun n => dZero0 (B n) (plSpec α 1 (N n)) (k n))
        (fun n => aAlpha α * plSpec α 1 (N n) (k n) *
          Real.sqrt (kappaOf α 1 (N n) (B n) / (2 * gammaOf (N n) (B n))))) := by
  constructor
  · intro hrow
    exact nm_caseA hα N B hB hγ hN0 hB0 k (nm_row_mass_atTop hα N B hγ k hrow)
  · intro hrow
    exact nm_caseB hα N B hB hγ hN0 hB0 k (nm_row_mass_zero hα N B hγ k hrow)

end Muon.PowerLaw

end

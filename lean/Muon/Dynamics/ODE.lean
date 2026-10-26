import Muon.Dynamics.Basic

/-!
# Appendix E, work package L-E.2: the deterministic mode-energy equations

Snapshot `cr-2026-10-23`. Source: `sections/05-dynamics/section.tex`, `def:app-dyn-ode` (ll. 141-150),
`lem:app-dyn-field` (ll. 202-214), `prop:app-dyn-ode` (ll. 262-274). Card:
`sections/05-dynamics/CARD.md` §2, §3 and the L-E.2 row of §5.

Reused, not redefined: from `Muon.Dynamics.Basic` (L-E.1) `DynParams`, `DynCoeff`, `IsDynOde`,
`odeRHS`, `odeRisk`, `odeInit`, `odeMeasure`, `fieldOp`, `Adm`, `admMeasures`, `CE`, `CR`,
`mZeta`, `dMax`, `Tstar`, `specRect`, `blTest`, `blNorm`, `blDist`, `tvNorm`, `tvDist`; from
`Muon.Setup` `SpectralData`, `riskSigma`; from `Muon.Foundations.Conventions` `Covariances`, `Mat`,
`fro`, `opNorm`.

Representation choices (also in the result JSON `open_questions`):
* `def_app_dyn_ode` is `IsDynOde` (the ODE in the variables `e = B²𝒬`, from L-E.1) together with
  `0 < ℛ` on `[0,T]`: the source's field is defined only where the risk is positive, and Lean's
  junk value `√(≤0)` would otherwise admit spurious solutions.
* Measure-valued identities are stated tested against bounded measurable `φ` (the weak reading of
  the source's `∫ 𝖥_B(χ) dσ`), with interval integrability as an explicit conjunct.
* Integrability of `𝔡` against finite measures carried by `K` follows from `DynCoeff.d_lip` (𝔡 is
  continuous on `K`) and `Adm` (χ(Kᶜ) = 0); the `fieldOp` integrals are therefore genuine.
* `lem:app-dyn-field`: the constants of (ii) and (iii) are existentially quantified before the
  dimension, the covariances and the measures, with the source's dependence on the bounds
  `(M, rlo, rhi)`. Part (i) carries explicit constants, the source's `C_E`, `C_𝓡` on `𝔐` and their
  general form on `Adm M rlo rhi`.
* The fixed-dimension hypotheses of `prop:app-dyn-ode` are those of the source (ll. 263-265).
-/

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open Muon Muon.Setup

noncomputable section

namespace Muon.Dynamics

/-! ### Private helpers for `lem:app-dyn-field` (fully proved in this file) -/

open scoped Matrix.Norms.L2Operator in
/-- An eigenvalue of `A` with unit eigenvector `w` is bounded by the operator norm of `A`. -/
private lemma abs_eig_le_opNorm_aux {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (w : Fin k → ℝ)
    (μ : ℝ) (hw : ∑ a, w a * w a = 1) (he : A *ᵥ w = μ • w) :
    |μ| ≤ opNorm A := by
  set x : EuclideanSpace ℝ (Fin k) := (EuclideanSpace.equiv (Fin k) ℝ).symm w with hxdef
  have hsum : ∑ a, ‖x a‖ ^ 2 = 1 := by
    have hterm : ∀ a, ‖x a‖ ^ 2 = w a * w a := fun a => by
      rw [Real.norm_eq_abs, sq_abs, sq]
      rfl
    simp only [hterm]
    exact hw
  have hx : ‖x‖ = 1 := by
    rw [EuclideanSpace.norm_eq, hsum, Real.sqrt_one]
  have h1 := Matrix.l2_opNorm_mulVec A x
  have h2 : (EuclideanSpace.equiv (Fin k) ℝ).symm (A *ᵥ ⇑x) = μ • x := by
    ext a
    have ha := congrFun he a
    simp only [hxdef, Pi.smul_apply, smul_eq_mul] at ha ⊢
    exact ha
  rw [h2, norm_smul, hx, Real.norm_eq_abs] at h1
  simp only [mul_one] at h1
  rw [opNorm_eq_norm]
  exact h1

/-- Output eigenvalues are bounded by `‖Σ_out‖`. -/
private lemma abs_mu_le_opNorm {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (i : Fin m) :
    |S.μ i| ≤ opNorm C.Sout :=
  abs_eig_le_opNorm_aux C.Sout (fun a => S.uOut a i) (S.μ i)
    (sum_col_sq_eq_one S.uOut S.huOut i) (S.eigOut i)

/-- Input eigenvalues are bounded by `‖Σ_in‖`. -/
private lemma abs_lam_le_opNorm {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (j : Fin n) :
    |S.lam j| ≤ opNorm C.Sin :=
  abs_eig_le_opNorm_aux C.Sin (fun a => S.vIn a j) (S.lam j)
    (sum_col_sq_eq_one S.vIn S.hvIn j) (S.eigIn j)

private lemma atom_isFinite {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (q : Fin m → Fin n → ℝ) :
    IsFiniteMeasure (atomMeasure μ lam q) := by
  constructor
  unfold atomMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.sum_lt_top.2 fun j _ => ENNReal.ofReal_lt_top

/-- The atomic measure is carried by the box `[-Cs, Cs]²` when its atoms are. -/
private lemma atom_ae_box {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (q : Fin m → Fin n → ℝ)
    (Cs : ℝ) (hμ : ∀ i, |μ i| ≤ Cs) (hlam : ∀ j, |lam j| ≤ Cs) :
    ∀ᵐ x ∂(atomMeasure μ lam q), |x.1| ≤ Cs ∧ |x.2| ≤ Cs := by
  have hA : MeasurableSet {x : ℝ × ℝ | |x.1| ≤ Cs ∧ |x.2| ≤ Cs} :=
    (measurableSet_le (continuous_fst.abs.measurable) measurable_const).inter
      (measurableSet_le (continuous_snd.abs.measurable) measurable_const)
  have hc : MeasurableSet {a : ℝ × ℝ | ¬(|a.1| ≤ Cs ∧ |a.2| ≤ Cs)} := hA.compl
  rw [ae_iff]
  unfold atomMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [Measure.dirac_apply' _ hc, Set.indicator_of_notMem (by
    intro h
    simp only [Set.mem_setOf_eq] at h
    exact h ⟨hμ i, hlam j⟩)]
  simp

/-- On `K`, `|x.1 * x.2| ≤ Cs²` for the box. -/
private lemma abs_prod_le_sq {a b Cs : ℝ} (ha : |a| ≤ Cs) (hb : |b| ≤ Cs) :
    ‖a * b‖ ≤ Cs ^ 2 := by
  rw [Real.norm_eq_abs, abs_mul]
  calc |a| * |b| ≤ Cs * Cs :=
        mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)
    _ = Cs ^ 2 := by ring

private lemma box_of_specRect {Cs : ℝ} {x : ℝ × ℝ} (hx : x ∈ specRect Cs) :
    |x.1| ≤ Cs ∧ |x.2| ≤ Cs := by
  simp only [specRect, Set.mem_prod, Set.mem_Icc] at hx
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hx
  exact ⟨abs_le.2 ⟨by linarith, h2⟩, abs_le.2 ⟨by linarith, h4⟩⟩

/-- A measure with `χ(Kᶜ) = 0` is concentrated on `K`. -/
private lemma ae_specRect {Cs : ℝ} {χ : Measure (ℝ × ℝ)} (hK : χ (specRect Cs)ᶜ = 0) :
    ∀ᵐ x ∂χ, x ∈ specRect Cs := by
  rw [ae_iff]
  exact hK

/-- The drift term `∫ φ 𝔡 dχ` is bounded by `𝔡_max · χ(univ)`. -/
private lemma d_integral_bound {m n : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    {B : ℕ} (c : DynCoeff p S B) (χ : Measure (ℝ × ℝ)) [IsFiniteMeasure χ]
    (hK : χ (specRect p.CSig)ᶜ = 0) (M : ℝ) (hmass : χ.real univ ≤ M)
    (φ : ℝ × ℝ → ℝ) (hφ : ∀ x, |φ x| ≤ 1) :
    |∫ x, φ x * c.d x ∂χ| ≤ dMax p * M := by
  have hae : ∀ᵐ x ∂χ, ‖φ x * c.d x‖ ≤ dMax p := by
    filter_upwards [ae_specRect hK] with x hx
    have hd0 := c.d_nonneg x hx
    have hd1 := c.d_le x hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hd0]
    have := mul_le_mul (hφ x) hd1 hd0 zero_le_one
    linarith
  have h := norm_integral_le_of_norm_le_const hae
  rw [Real.norm_eq_abs] at h
  have hdM : 0 ≤ dMax p := by
    unfold dMax
    exact div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  exact h.trans (mul_le_mul_of_nonneg_left hmass hdM)

private lemma dMax_nonneg' (p : DynParams) : 0 ≤ dMax p := by
  unfold dMax
  exact div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)

/-- Pointwise bound on the field, `|𝖥_B(χ)(φ)| ≤ 2h 𝔡_max M/√rlo + h² m_ζ`. -/
private lemma field_pointwise {m n : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    {B : ℕ} (c : DynCoeff p S B) (M rlo rhi : ℝ) (hrlo : 0 < rlo)
    (χ : Measure (ℝ × ℝ)) (hχ : χ ∈ Adm p.CSig M rlo rhi)
    (φ : ℝ × ℝ → ℝ) (hφ : ∀ x, |φ x| ≤ 1) :
    |fieldOp p.h c.d c.ζ χ φ| ≤ 2 * p.h * dMax p * M / Real.sqrt rlo + p.h ^ 2 * mZeta p := by
  obtain ⟨hfin, hK, hmass, hr1, _⟩ := hχ
  haveI := hfin
  have hζfin : IsFiniteMeasure c.ζ := by
    rw [c.ζ_eq]
    exact atom_isFinite _ _ _
  haveI := hζfin
  have hRpos : 0 < riskOf χ := lt_of_lt_of_le hrlo hr1
  have hI := d_integral_bound p S c χ hK M hmass φ hφ
  have hJ : |∫ x, φ x ∂c.ζ| ≤ mZeta p := by
    have h := norm_integral_le_of_norm_le_const (μ := c.ζ) (f := φ) (C := 1)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hφ x)
    rw [Real.norm_eq_abs, one_mul] at h
    exact h.trans c.ζ_mass
  unfold fieldOp
  rw [if_pos hRpos]
  have hsR : 0 < Real.sqrt rlo := Real.sqrt_pos.2 hrlo
  have hs : Real.sqrt rlo ≤ Real.sqrt (riskOf χ) := Real.sqrt_le_sqrt hr1
  have hA : 2 * p.h / Real.sqrt (riskOf χ) ≤ 2 * p.h / Real.sqrt rlo :=
    div_le_div_of_nonneg_left (by linarith [p.hh]) hsR hs
  have hA0 : 0 ≤ 2 * p.h / Real.sqrt (riskOf χ) :=
    div_nonneg (by linarith [p.hh]) (Real.sqrt_nonneg _)
  have hB0 : 0 ≤ 2 * p.h / Real.sqrt rlo :=
    div_nonneg (by linarith [p.hh]) (Real.sqrt_nonneg _)
  have e1 : |-(2 * p.h / Real.sqrt (riskOf χ)) * ∫ x, φ x * c.d x ∂χ| =
      2 * p.h / Real.sqrt (riskOf χ) * |∫ x, φ x * c.d x ∂χ| := by
    rw [neg_mul, abs_neg, abs_mul, abs_of_nonneg hA0]
  have e2 : |p.h ^ 2 * ∫ x, φ x ∂c.ζ| = p.h ^ 2 * |∫ x, φ x ∂c.ζ| := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  have t := abs_add_le (-(2 * p.h / Real.sqrt (riskOf χ)) * ∫ x, φ x * c.d x ∂χ)
    (p.h ^ 2 * ∫ x, φ x ∂c.ζ)
  have k1 : 2 * p.h / Real.sqrt (riskOf χ) * |∫ x, φ x * c.d x ∂χ| ≤
      2 * p.h / Real.sqrt rlo * (dMax p * M) :=
    mul_le_mul hA hI (abs_nonneg _) hB0
  have k2 : p.h ^ 2 * |∫ x, φ x ∂c.ζ| ≤ p.h ^ 2 * mZeta p :=
    mul_le_mul_of_nonneg_left hJ (sq_nonneg _)
  have k3 : 2 * p.h / Real.sqrt rlo * (dMax p * M) =
      2 * p.h * dMax p * M / Real.sqrt rlo := by ring
  linarith

/-- The quadratic bound `½|𝖥_B(χ)(x₁x₂)| ≤ 2h 𝔡_max √rhi + h² C_Σ² m_ζ / 2`. -/
private lemma field_quad {m n : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    {B : ℕ} (c : DynCoeff p S B) (hSout : opNorm C.Sout ≤ p.CSig)
    (hSin : opNorm C.Sin ≤ p.CSig) (M rlo rhi : ℝ) (hrlo : 0 < rlo)
    (χ : Measure (ℝ × ℝ)) (hχ : χ ∈ Adm p.CSig M rlo rhi) :
    (1 / 2) * |fieldOp p.h c.d c.ζ χ (fun x => x.1 * x.2)| ≤
      2 * p.h * dMax p * Real.sqrt rhi + p.h ^ 2 * p.CSig ^ 2 * mZeta p / 2 := by
  obtain ⟨hfin, hK, hmass, hr1, hr2⟩ := hχ
  haveI := hfin
  have hζfin : IsFiniteMeasure c.ζ := by
    rw [c.ζ_eq]
    exact atom_isFinite _ _ _
  haveI := hζfin
  have hRpos : 0 < riskOf χ := lt_of_lt_of_le hrlo hr1
  have hζae : ∀ᵐ x ∂c.ζ, |x.1| ≤ p.CSig ∧ |x.2| ≤ p.CSig := by
    rw [c.ζ_eq]
    exact atom_ae_box _ _ _ _
      (fun i => (abs_mu_le_opNorm S i).trans hSout)
      (fun j => (abs_lam_le_opNorm S j).trans hSin)
  have hJ : |∫ x, x.1 * x.2 ∂c.ζ| ≤ p.CSig ^ 2 * mZeta p := by
    have hb : ∀ᵐ x ∂c.ζ, ‖x.1 * x.2‖ ≤ p.CSig ^ 2 :=
      hζae.mono fun x hx => abs_prod_le_sq hx.1 hx.2
    have h := norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left c.ζ_mass (sq_nonneg _))
  have hχae := ae_specRect hK
  have hint : Integrable (fun x : ℝ × ℝ => x.1 * x.2) χ := by
    refine Integrable.mono' (integrable_const (p.CSig ^ 2))
      (continuous_fst.mul continuous_snd).aestronglyMeasurable ?_
    exact hχae.mono fun x hx => abs_prod_le_sq (box_of_specRect hx).1 (box_of_specRect hx).2
  have hdom : ∀ᵐ x ∂χ, ‖(x.1 * x.2) * c.d x‖ ≤ dMax p * (x.1 * x.2) := by
    filter_upwards [hχae] with x hx
    have hq : 0 ≤ x.1 * x.2 := by
      have hx' := hx
      simp only [specRect, Set.mem_prod, Set.mem_Icc] at hx'
      exact mul_nonneg hx'.1.1 hx'.2.1
    have hd0 := c.d_nonneg x hx
    have hd1 := c.d_le x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hq hd0)]
    calc (x.1 * x.2) * c.d x ≤ (x.1 * x.2) * dMax p := mul_le_mul_of_nonneg_left hd1 hq
      _ = dMax p * (x.1 * x.2) := mul_comm _ _
  have hg : Integrable (fun x : ℝ × ℝ => dMax p * (x.1 * x.2)) χ := hint.const_mul (dMax p)
  have hI := norm_integral_le_of_norm_le hg hdom
  rw [integral_const_mul] at hI
  have hR2 : ∫ x, x.1 * x.2 ∂χ = 2 * riskOf χ := by
    unfold riskOf
    ring
  rw [hR2, Real.norm_eq_abs] at hI
  unfold fieldOp
  rw [if_pos hRpos]
  show (1 / 2) * |-(2 * p.h / Real.sqrt (riskOf χ)) * ∫ x, (x.1 * x.2) * c.d x ∂χ +
      p.h ^ 2 * ∫ x, x.1 * x.2 ∂c.ζ| ≤ _
  have hA0 : 0 ≤ 2 * p.h / Real.sqrt (riskOf χ) :=
    div_nonneg (by linarith [p.hh]) (Real.sqrt_nonneg _)
  have e1 : |-(2 * p.h / Real.sqrt (riskOf χ)) * ∫ x, (x.1 * x.2) * c.d x ∂χ| =
      2 * p.h / Real.sqrt (riskOf χ) * |∫ x, (x.1 * x.2) * c.d x ∂χ| := by
    rw [neg_mul, abs_neg, abs_mul, abs_of_nonneg hA0]
  have e2 : |p.h ^ 2 * ∫ x, x.1 * x.2 ∂c.ζ| = p.h ^ 2 * |∫ x, x.1 * x.2 ∂c.ζ| := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  have t := abs_add_le (-(2 * p.h / Real.sqrt (riskOf χ)) * ∫ x, (x.1 * x.2) * c.d x ∂χ)
    (p.h ^ 2 * ∫ x, x.1 * x.2 ∂c.ζ)
  have k1 : 2 * p.h / Real.sqrt (riskOf χ) * |∫ x, (x.1 * x.2) * c.d x ∂χ| ≤
      2 * p.h / Real.sqrt (riskOf χ) * (dMax p * (2 * riskOf χ)) :=
    mul_le_mul_of_nonneg_left hI hA0
  have k2 : p.h ^ 2 * |∫ x, x.1 * x.2 ∂c.ζ| ≤ p.h ^ 2 * (p.CSig ^ 2 * mZeta p) :=
    mul_le_mul_of_nonneg_left hJ (sq_nonneg _)
  have k3 : 2 * p.h / Real.sqrt (riskOf χ) * (dMax p * (2 * riskOf χ)) =
      4 * p.h * dMax p * Real.sqrt (riskOf χ) := by
    have hsq : Real.sqrt (riskOf χ) ≠ 0 := (Real.sqrt_pos.2 hRpos).ne'
    have : 2 * p.h / Real.sqrt (riskOf χ) * (dMax p * (2 * riskOf χ)) =
        2 * p.h * dMax p * (2 * riskOf χ / Real.sqrt (riskOf χ)) := by ring
    rw [this, mul_div_assoc, Real.div_sqrt]
    ring
  have hs : Real.sqrt (riskOf χ) ≤ Real.sqrt rhi := Real.sqrt_le_sqrt hr2
  have hpos : 0 ≤ 2 * p.h * dMax p := mul_nonneg (mul_nonneg (by norm_num) p.hh.le) (dMax_nonneg' p)
  have hk : 2 * p.h * dMax p * Real.sqrt (riskOf χ) ≤ 2 * p.h * dMax p * Real.sqrt rhi :=
    mul_le_mul_of_nonneg_left hs hpos
  linarith

/-- A pointwise bound over bounded test functions gives the sup-form bounds (`BddAbove`, `tvNorm`). -/
private lemma tv_of_pointwise (ℓ : (ℝ × ℝ → ℝ) → ℝ) (B : ℝ)
    (hB : ∀ φ : ℝ × ℝ → ℝ, (∀ x, |φ x| ≤ 1) → |ℓ φ| ≤ B) :
    BddAbove ((fun φ => |ℓ φ|) '' {φ : ℝ × ℝ → ℝ | Measurable φ ∧ ∀ x, |φ x| ≤ 1}) ∧
      tvNorm ℓ ≤ B := by
  refine ⟨⟨B, ?_⟩, ?_⟩
  · rintro _ ⟨φ, ⟨-, hφ⟩, rfl⟩
    exact hB φ hφ
  · unfold tvNorm
    apply csSup_le
    · exact ⟨_, ⟨fun _ => (1 : ℝ), ⟨measurable_const, fun _ => by norm_num⟩, rfl⟩⟩
    · rintro _ ⟨φ, ⟨-, hφ⟩, rfl⟩
      exact hB φ hφ

private lemma test_bdd {Cs : ℝ} (T : Set (ℝ × ℝ → ℝ))
    (hT : ∀ φ ∈ T, ∀ x ∈ specRect Cs, |φ x| ≤ 1)
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0) :
    BddAbove ((fun φ => |∫ x, φ x ∂μ - ∫ x, φ x ∂ν|) '' T) := by
  refine ⟨μ.real univ + ν.real univ, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  have hb (ρ : Measure (ℝ × ℝ)) [IsFiniteMeasure ρ]
      (hρ : ρ (specRect Cs)ᶜ = 0) : |∫ x, φ x ∂ρ| ≤ ρ.real univ := by
    have h := norm_integral_le_of_norm_le_const (μ := ρ) (f := φ) (C := 1)
      ((ae_specRect hρ).mono fun x hx => by
        rw [Real.norm_eq_abs]; exact hT φ hφ x hx)
    simpa only [Real.norm_eq_abs, one_mul] using h
  exact (abs_sub _ _).trans (add_le_add (hb μ hμ) (hb ν hν))

private lemma test_scaled {Cs A : ℝ} (T : Set (ℝ × ℝ → ℝ))
    (hT : ∀ φ ∈ T, ∀ x ∈ specRect Cs, |φ x| ≤ 1)
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0)
    (g ψ : ℝ × ℝ → ℝ) (hψ : ψ ∈ T) (hA : 0 ≤ A)
    (he : ∀ x ∈ specRect Cs, g x = A * ψ x) :
    |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤
      A * sSup ((fun φ => |∫ x, φ x ∂μ - ∫ x, φ x ∂ν|) '' T) := by
  have e (ρ : Measure (ℝ × ℝ)) (hρ : ρ (specRect Cs)ᶜ = 0) :
      ∫ x, g x ∂ρ = A * ∫ x, ψ x ∂ρ := by
    rw [← integral_const_mul]
    exact integral_congr_ae ((ae_specRect hρ).mono fun x hx => he x hx)
  rw [e μ hμ, e ν hν, ← mul_sub, abs_mul, abs_of_nonneg hA]
  exact mul_le_mul_of_nonneg_left
    (le_csSup (test_bdd T hT μ ν hμ hν) ⟨ψ, hψ, rfl⟩) hA

private lemma bl_scaled {Cs A : ℝ} (hA : 0 < A)
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0)
    (g : ℝ × ℝ → ℝ) (hb : ∀ x ∈ specRect Cs, |g x| ≤ A)
    (hl : ∀ x ∈ specRect Cs, ∀ y ∈ specRect Cs, |g x - g y| ≤ A * l1 x y) :
    |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤ A * blDist Cs μ ν := by
  refine test_scaled (blTest Cs) (fun φ hφ => hφ.1) μ ν hμ hν g
    (fun x => g x / A) ?_ hA.le ?_
  · refine ⟨?_, ?_⟩
    · intro x hx
      rw [abs_div, abs_of_pos hA]
      exact (div_le_one hA).2 (hb x hx)
    · intro x hx y hy
      rw [← sub_div, abs_div, abs_of_pos hA]
      exact (div_le_iff₀ hA).2 (by simpa only [mul_comm] using hl x hx y hy)
  · intro x _
    field_simp

private lemma local_lip_cont {Cs L : ℝ} {g : ℝ × ℝ → ℝ} (hL : 0 ≤ L)
    (hl : ∀ x ∈ specRect Cs, ∀ y ∈ specRect Cs, |g x - g y| ≤ L * l1 x y) :
    ContinuousOn g (specRect Cs) := by
  have h : LipschitzOnWith ⟨2 * L, by positivity⟩ g (specRect Cs) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Real.dist_eq]
    have hd : l1 x y ≤ 2 * dist x y := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      unfold l1
      linarith [le_max_left |x.1 - y.1| |x.2 - y.2|,
        le_max_right |x.1 - y.1| |x.2 - y.2|]
    exact (hl x hx y hy).trans (by
      change L * l1 x y ≤ (2 * L) * dist x y
      nlinarith [mul_le_mul_of_nonneg_left hd hL])
  exact h.continuousOn

private lemma tv_scaled {Cs A : ℝ} (hA : 0 < A)
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0)
    (g : ℝ × ℝ → ℝ) (hg : Measurable g)
    (hb : ∀ x ∈ specRect Cs, |g x| ≤ A) :
    |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤ A * tvDist μ ν := by
  classical
  have hK : MeasurableSet (specRect Cs) := measurableSet_Icc.prod measurableSet_Icc
  refine test_scaled {φ | Measurable φ ∧ ∀ x, |φ x| ≤ 1}
    (fun φ hφ x _ => hφ.2 x) μ ν hμ hν g
    ((specRect Cs).indicator (fun x => g x / A)) ?_ hA.le ?_
  · refine ⟨(hg.div_const A).indicator hK, ?_⟩
    intro x
    by_cases hx : x ∈ specRect Cs
    · rw [Set.indicator_of_mem hx, abs_div, abs_of_pos hA]
      exact (div_le_one hA).2 (hb x hx)
    · simp [Set.indicator_of_notMem hx]
  · intro x hx
    rw [Set.indicator_of_mem hx]
    field_simp

private lemma abs_mul_sub_bound {a b c d A B : ℝ}
    (ha : |a| ≤ A) (hd : |d| ≤ B) :
    |a * b - c * d| ≤ A * |b - d| + B * |a - c| := by
  calc
    _ = |a * (b - d) + d * (a - c)| := by congr 1; ring
    _ ≤ |a * (b - d)| + |d * (a - c)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hd (abs_nonneg _))

private lemma quad_lip (p : DynParams) :
    ∀ x ∈ specRect p.CSig, ∀ y ∈ specRect p.CSig,
      |x.1 * x.2 - y.1 * y.2| ≤ p.CSig * l1 x y := by
  intro x hx y hy
  have h := abs_mul_sub_bound (b := x.2) (c := y.1) (box_of_specRect hx).1 (box_of_specRect hy).2
  exact h.trans_eq (by unfold l1; ring)

private lemma tv_d_diff {m n : ℕ} {C : Covariances m n}
    (p : DynParams) (S : SpectralData C) {B : ℕ} (c : DynCoeff p S B)
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect p.CSig)ᶜ = 0) (hν : ν (specRect p.CSig)ᶜ = 0)
    (φ : ℝ × ℝ → ℝ) (hm : Measurable φ) (hb : ∀ x, |φ x| ≤ 1) :
    |(∫ x, φ x * c.d x ∂μ) - ∫ x, φ x * c.d x ∂ν| ≤
      (dMax p + 1) * tvDist μ ν := by
  classical
  have hL : 0 ≤ p.CSig / Real.sqrt (2 * p.ϱ) :=
    div_nonneg (by linarith [p.hC]) (Real.sqrt_nonneg _)
  have hc := local_lip_cont hL c.d_lip
  let d0 := (specRect p.CSig).piecewise c.d (fun _ => 0)
  have hd0 : Measurable d0 := hc.measurable_piecewise continuousOn_const
    (measurableSet_Icc.prod measurableSet_Icc)
  have he (ρ : Measure (ℝ × ℝ)) (hρ : ρ (specRect p.CSig)ᶜ = 0) :
      (∫ x, φ x * c.d x ∂ρ) = ∫ x, φ x * d0 x ∂ρ := by
    apply integral_congr_ae
    filter_upwards [ae_specRect hρ] with x hx
    simp only [d0, Set.piecewise_eq_of_mem (specRect p.CSig) c.d (fun _ => 0) hx]
  rw [he μ hμ, he ν hν]
  refine tv_scaled (by linarith [dMax_nonneg' p] : 0 < dMax p + 1)
    μ ν hμ hν (fun x => φ x * d0 x) (hm.mul hd0) ?_
  intro x hx
  simp only [d0, Set.piecewise_eq_of_mem (specRect p.CSig) c.d (fun _ => 0) hx]
  rw [abs_mul, abs_of_nonneg (c.d_nonneg x hx)]
  have h := mul_le_mul_of_nonneg_right (hb x) (c.d_nonneg x hx)
  linarith [c.d_le x hx]

private lemma tv_risk_diff (p : DynParams)
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect p.CSig)ᶜ = 0) (hν : ν (specRect p.CSig)ᶜ = 0) :
    |riskOf μ - riskOf ν| ≤ ((p.CSig ^ 2 + 1) / 2) * tvDist μ ν := by
  have h := tv_scaled (by positivity : 0 < p.CSig ^ 2 + 1) μ ν hμ hν
    (fun x => x.1 * x.2) (measurable_fst.mul measurable_snd) (by
      intro x hx
      have hb := abs_prod_le_sq (box_of_specRect hx).1 (box_of_specRect hx).2
      rw [Real.norm_eq_abs] at hb
      linarith)
  unfold riskOf
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

private lemma bl_d_diff {m n : ℕ} {C : Covariances m n}
    (p : DynParams) (S : SpectralData C) {B : ℕ} (c : DynCoeff p S B)
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect p.CSig)ᶜ = 0) (hν : ν (specRect p.CSig)ᶜ = 0)
    (φ : ℝ × ℝ → ℝ) (hφ : φ ∈ blTest p.CSig) :
    |(∫ x, φ x * c.d x ∂μ) - ∫ x, φ x * c.d x ∂ν| ≤
      (2 * dMax p + p.CSig / Real.sqrt (2 * p.ϱ) + 1) * blDist p.CSig μ ν := by
  have hL : 0 ≤ p.CSig / Real.sqrt (2 * p.ϱ) :=
    div_nonneg (by linarith [p.hC]) (Real.sqrt_nonneg _)
  have hd := dMax_nonneg' p
  refine bl_scaled (by linarith : 0 < 2 * dMax p + p.CSig / Real.sqrt (2 * p.ϱ) + 1)
    μ ν hμ hν (fun x => φ x * c.d x) ?_ ?_
  · intro x hx
    rw [abs_mul, abs_of_nonneg (c.d_nonneg x hx)]
    have hh := mul_le_mul_of_nonneg_right (hφ.1 x hx) (c.d_nonneg x hx)
    linarith [c.d_le x hx]
  · intro x hx y hy
    have ht : 0 ≤ l1 x y := add_nonneg (abs_nonneg _) (abs_nonneg _)
    calc
      _ ≤ 1 * |c.d x - c.d y| + dMax p * |φ x - φ y| :=
        abs_mul_sub_bound (hφ.1 x hx)
          (by rw [abs_of_nonneg (c.d_nonneg y hy)]; exact c.d_le y hy)
      _ ≤ 1 * (p.CSig / Real.sqrt (2 * p.ϱ) * l1 x y) + dMax p * l1 x y :=
        add_le_add (mul_le_mul_of_nonneg_left (c.d_lip x hx y hy) zero_le_one)
          (mul_le_mul_of_nonneg_left (hφ.2 x hx y hy) hd)
      _ ≤ _ := by nlinarith [mul_nonneg hd ht]

private lemma bl_risk_diff (p : DynParams)
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect p.CSig)ᶜ = 0) (hν : ν (specRect p.CSig)ᶜ = 0) :
    |riskOf μ - riskOf ν| ≤ ((p.CSig ^ 2 + p.CSig + 1) / 2) * blDist p.CSig μ ν := by
  have hC : 0 ≤ p.CSig := by linarith [p.hC]
  have h := bl_scaled (by positivity : 0 < p.CSig ^ 2 + p.CSig + 1) μ ν hμ hν
    (fun x => x.1 * x.2) (by
      intro x hx
      have hb := abs_prod_le_sq (box_of_specRect hx).1 (box_of_specRect hx).2
      rw [Real.norm_eq_abs] at hb
      linarith) (by
      intro x hx y hy
      have ht : 0 ≤ l1 x y := add_nonneg (abs_nonneg _) (abs_nonneg _)
      exact (quad_lip p x hx y hy).trans
        (mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg p.CSig]) ht))
  unfold riskOf
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

private lemma sup_of_pointwise (T : Set (ℝ × ℝ → ℝ)) (hne : T.Nonempty)
    (ℓ : (ℝ × ℝ → ℝ) → ℝ) (A : ℝ) (hb : ∀ φ ∈ T, |ℓ φ| ≤ A) :
    BddAbove ((fun φ => |ℓ φ|) '' T) ∧ sSup ((fun φ => |ℓ φ|) '' T) ≤ A := by
  constructor
  · exact ⟨A, by rintro _ ⟨φ, hφ, rfl⟩; exact hb φ hφ⟩
  · apply csSup_le (hne.image _)
    rintro _ ⟨φ, hφ, rfl⟩
    exact hb φ hφ

private lemma inv_sqrt_diff {r x y : ℝ} (hr : 0 < r) (hx : r ≤ x) (hy : r ≤ y) :
    |1 / Real.sqrt x - 1 / Real.sqrt y| ≤
      (1 / (Real.sqrt r) ^ 3) * |x - y| := by
  have hs := Real.sqrt_pos.2 hr
  have hxs := Real.sqrt_le_sqrt hx
  have hys := Real.sqrt_le_sqrt hy
  have hx0 : 0 < Real.sqrt x := lt_of_lt_of_le hs hxs
  have hy0 : 0 < Real.sqrt y := lt_of_lt_of_le hs hys
  have he : 1 / Real.sqrt x - 1 / Real.sqrt y =
      (y - x) / (Real.sqrt x * Real.sqrt y * (Real.sqrt x + Real.sqrt y)) := by
    apply (eq_div_iff (by positivity)).2
    field_simp
    nlinarith [Real.sq_sqrt (hr.le.trans hx), Real.sq_sqrt (hr.le.trans hy)]
  have hd : (Real.sqrt r) ^ 3 ≤
      Real.sqrt x * Real.sqrt y * (Real.sqrt x + Real.sqrt y) := by
    have h1 := mul_le_mul hxs hys hs.le (Real.sqrt_nonneg x)
    have h2 := mul_le_mul h1 (show Real.sqrt r ≤ Real.sqrt x + Real.sqrt y by linarith)
      hs.le (mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y))
    nlinarith
  rw [he, abs_div, abs_of_pos (show 0 < Real.sqrt x * Real.sqrt y *
    (Real.sqrt x + Real.sqrt y) by positivity), abs_sub_comm y x]
  calc
    _ ≤ |x - y| / (Real.sqrt r) ^ 3 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hd
    _ = _ := by ring

private lemma field_diff_bound {m n : ℕ} {C : Covariances m n}
    (p : DynParams) (S : SpectralData C) {B : ℕ} (c : DynCoeff p S B)
    (M rlo rhi D Q δ : ℝ) (hrlo : 0 < rlo)
    (χ χ' : Measure (ℝ × ℝ)) (hχ : χ ∈ Adm p.CSig M rlo rhi)
    (hχ' : χ' ∈ Adm p.CSig M rlo rhi) (φ : ℝ × ℝ → ℝ)
    (hdiff : |(∫ x, φ x * c.d x ∂χ) - ∫ x, φ x * c.d x ∂χ'| ≤ D * δ)
    (hrisk : |riskOf χ - riskOf χ'| ≤ Q * δ)
    (hφ : ∀ x ∈ specRect p.CSig, |φ x| ≤ 1) :
    |fieldOp p.h c.d c.ζ χ φ - fieldOp p.h c.d c.ζ χ' φ| ≤
      (2 * p.h / Real.sqrt rlo * D +
        2 * p.h * (1 / (Real.sqrt rlo) ^ 3) * Q * (dMax p * |M|)) * δ := by
  haveI := hχ.1
  haveI := hχ'.1
  have hhpos := p.hh
  have hi : |∫ x, φ x * c.d x ∂χ'| ≤ dMax p * |M| := by
    have hb : ∀ᵐ x ∂χ', ‖φ x * c.d x‖ ≤ dMax p := by
      filter_upwards [ae_specRect hχ'.2.1] with x hx
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (c.d_nonneg x hx)]
      exact (mul_le_mul_of_nonneg_right (hφ x hx) (c.d_nonneg x hx)).trans
        (by simpa using c.d_le x hx)
    have hh := norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hχ'.2.2.1.trans (le_abs_self M))
      (dMax_nonneg' p))
  have ha : 0 ≤ 2 * p.h / Real.sqrt (riskOf χ) := by positivity
  have ha' : 2 * p.h / Real.sqrt (riskOf χ) ≤ 2 * p.h / Real.sqrt rlo :=
    div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 hrlo)
      (Real.sqrt_le_sqrt hχ.2.2.2.1)
  have hb : |2 * p.h / Real.sqrt (riskOf χ) - 2 * p.h / Real.sqrt (riskOf χ')| ≤
      2 * p.h * (1 / (Real.sqrt rlo) ^ 3) * (Q * δ) := by
    have he : 2 * p.h / Real.sqrt (riskOf χ) - 2 * p.h / Real.sqrt (riskOf χ') =
        (2 * p.h) * (1 / Real.sqrt (riskOf χ) - 1 / Real.sqrt (riskOf χ')) := by ring
    rw [he, abs_mul, abs_of_pos (by positivity)]
    exact (mul_le_mul_of_nonneg_left
      (inv_sqrt_diff hrlo hχ.2.2.2.1 hχ'.2.2.2.1) (by positivity)).trans
        (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hrisk
          (show 0 ≤ 2 * p.h * (1 / (Real.sqrt rlo) ^ 3) by positivity)))
  unfold fieldOp
  rw [if_pos (hrlo.trans_le hχ.2.2.2.1), if_pos (hrlo.trans_le hχ'.2.2.2.1)]
  have he : -(2 * p.h / Real.sqrt (riskOf χ)) * (∫ x, φ x * c.d x ∂χ) +
      p.h ^ 2 * (∫ x, φ x ∂c.ζ) -
      (-(2 * p.h / Real.sqrt (riskOf χ')) * (∫ x, φ x * c.d x ∂χ') +
        p.h ^ 2 * (∫ x, φ x ∂c.ζ)) =
      -(2 * p.h / Real.sqrt (riskOf χ)) *
        ((∫ x, φ x * c.d x ∂χ) - ∫ x, φ x * c.d x ∂χ') -
      (2 * p.h / Real.sqrt (riskOf χ) - 2 * p.h / Real.sqrt (riskOf χ')) *
        (∫ x, φ x * c.d x ∂χ') := by ring
  rw [he]
  calc
    _ ≤ |-(2 * p.h / Real.sqrt (riskOf χ)) *
          ((∫ x, φ x * c.d x ∂χ) - ∫ x, φ x * c.d x ∂χ')| +
        |(2 * p.h / Real.sqrt (riskOf χ) - 2 * p.h / Real.sqrt (riskOf χ')) *
          (∫ x, φ x * c.d x ∂χ')| := abs_sub _ _
    _ = (2 * p.h / Real.sqrt (riskOf χ)) *
          |(∫ x, φ x * c.d x ∂χ) - ∫ x, φ x * c.d x ∂χ'| +
        |2 * p.h / Real.sqrt (riskOf χ) - 2 * p.h / Real.sqrt (riskOf χ')| *
          |∫ x, φ x * c.d x ∂χ'| := by rw [abs_mul, abs_neg, abs_of_nonneg ha, abs_mul]
    _ ≤ (2 * p.h / Real.sqrt rlo) * (D * δ) +
        (2 * p.h * (1 / (Real.sqrt rlo) ^ 3) * (Q * δ)) * (dMax p * |M|) :=
      add_le_add (mul_le_mul ha' hdiff (abs_nonneg _) (by positivity))
        (mul_le_mul hb hi (abs_nonneg _)
          (le_trans (abs_nonneg _) hb))
    _ = _ := by ring

/-- `def:app-dyn-ode`, snapshot `cr-2026-10-23`. Declaration of record `Muon.Dynamics.def_app_dyn_ode`: the deterministic mode-energy equations with the initial value `B²𝒬(0)` of `def:app-dyn-ode` and the positivity of the risk the field presupposes.

Source (`section.tex`, whole environment):
```latex
\begin{definition}[Deterministic mode-energy equations]\label{def:app-dyn-ode}
For $i\le\Nout$ and $j\le\Nin$, the deterministic mode-energy equations are
\begin{equation}\label{eqn:app-dyn-ode}
\frac{\dif}{\dif\macrotime}\big(B^2\fQ_{ij}(\macrotime)\big)=-\frac{2\macrostep\,\mathfrak d_{ij}}{\sqrt{\fRisk(\macrotime)}}\,B^2\fQ_{ij}(\macrotime)+\macrostep^2B\,\mathfrak v_{ij},\qquad
\fRisk(\macrotime)\defeq\frac12\sum_{i,j}\mu_i\lambda_j\,\fQ_{ij}(\macrotime),
\end{equation}
with the initial values $\fQ_{ij}(0)=\CMscr Q_{ij}(0)=(u_i^\T\Delta_0v_j)^2$.
Their spectral energy measure is
$\chi^{\mathrm{ode}}(\macrotime)\defeq\sum_{i,j}\fQ_{ij}(\macrotime)\,\delta_{(\mu_i,\lambda_j)}$.
\end{definition}
```
-/
def def_app_dyn_ode {m n : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    {B : ℕ} (c : DynCoeff p S B) (Δ0 : Mat m n) (T : ℝ) (e : ℝ → Fin m → Fin n → ℝ) : Prop :=
  IsDynOde p.h (B : ℝ) S.μ S.lam c.d c.v T (odeInit (B : ℝ) S Δ0) e ∧
    ∀ τ ∈ Icc 0 T, 0 < odeRisk S.μ S.lam (B : ℝ) (e τ)

/-- `lem:app-dyn-field`, snapshot `cr-2026-10-23`. Part (i) on `admMeasures p` (the source's `𝔐`), constants `C_E`, `C_𝓡` (`CE p`, `CR p`). Weak form `fieldOp`.

Source (`section.tex`, whole environment):
```latex
\begin{lemma}[The field]\label{lem:app-dyn-field}
There is $C_{\mathsf F}$, depending only on $(\macrostep,\ridge,C_\Sigma,E_\star,r_0,r_1)$
and on $m_\zeta$, such that for $\chi,\chi'\in\mathfrak M$:
\begin{enumerate}[label=(\roman*)]
\item $\abs{\mathsf F_B(\chi)(\mathbb K)}\le\norm{\mathsf F_B(\chi)}_{\mathrm{TV}}\le C_E$ and
$\frac12\big|\int\mu\lambda\,\dif\mathsf F_B(\chi)\big|\le C_{\cR}$;
\item $\norm{\mathsf F_B(\chi)-\mathsf F_B(\chi')}_{\mathrm{TV}}\le C_{\mathsf F}\norm{\chi-\chi'}_{\mathrm{TV}}$;
\item $\norm{\mathsf F_B(\chi)-\mathsf F_B(\chi')}_\BL\le C_{\mathsf F}\norm{\chi-\chi'}_\BL$.
\end{enumerate}
The same statements hold, with $C_E$, $C_{\cR}$, $C_{\mathsf F}$ depending
also on the bounds, on every set defined as $\mathfrak M$ with other
positive bounds on the mass and the risk.
\end{lemma}
```
-/
theorem lem_app_dyn_field_i {m n : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    {B : ℕ} (c : DynCoeff p S B)
    (hSout : opNorm C.Sout ≤ p.CSig) (hSin : opNorm C.Sin ≤ p.CSig)
    (χ : Measure (ℝ × ℝ)) (hχ : χ ∈ admMeasures p) :
    |fieldOp p.h c.d c.ζ χ (fun _ => 1)| ≤ CE p ∧
    BddAbove ((fun φ => |fieldOp p.h c.d c.ζ χ φ|) ''
      {φ : ℝ × ℝ → ℝ | Measurable φ ∧ ∀ x, |φ x| ≤ 1}) ∧
    tvNorm (fun φ => fieldOp p.h c.d c.ζ χ φ) ≤ CE p ∧
    (1 / 2) * |fieldOp p.h c.d c.ζ χ (fun x => x.1 * x.2)| ≤ CR p := by
  have hr0 : 0 < p.r0 / 2 := by linarith [p.hr0]
  have hχ' : χ ∈ Adm p.CSig (p.Estar + 1) (p.r0 / 2) (p.r1 + 1 / 2) := hχ
  have hB : ∀ φ : ℝ × ℝ → ℝ, (∀ x, |φ x| ≤ 1) → |fieldOp p.h c.d c.ζ χ φ| ≤ CE p := by
    intro φ hφ
    have := field_pointwise p S c (p.Estar + 1) (p.r0 / 2) (p.r1 + 1 / 2) hr0 χ hχ' φ hφ
    unfold CE
    exact this
  have hq := field_quad p S c hSout hSin (p.Estar + 1) (p.r0 / 2) (p.r1 + 1 / 2) hr0 χ hχ'
  have hsq : Real.sqrt (p.r1 + 1 / 2) ≤ Real.sqrt (p.r1 + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hpos : 0 ≤ 2 * p.h * dMax p := mul_nonneg (mul_nonneg (by norm_num) p.hh.le) (dMax_nonneg' p)
  have hk : 2 * p.h * dMax p * Real.sqrt (p.r1 + 1 / 2) ≤ 2 * p.h * dMax p * Real.sqrt (p.r1 + 1) :=
    mul_le_mul_of_nonneg_left hsq hpos
  obtain ⟨hb, ht⟩ := tv_of_pointwise (fun φ => fieldOp p.h c.d c.ζ χ φ) _ hB
  refine ⟨hB (fun _ => 1) (fun _ => by norm_num), hb, ht, ?_⟩
  unfold CR
  linarith

/-- `lem:app-dyn-field`, snapshot `cr-2026-10-23`. Part (i) for every `Adm M rlo rhi` with `rlo > 0` (the clause after (iii) of the source), explicit constants.

Source (`section.tex`, whole environment):
```latex
\begin{lemma}[The field]\label{lem:app-dyn-field}
There is $C_{\mathsf F}$, depending only on $(\macrostep,\ridge,C_\Sigma,E_\star,r_0,r_1)$
and on $m_\zeta$, such that for $\chi,\chi'\in\mathfrak M$:
\begin{enumerate}[label=(\roman*)]
\item $\abs{\mathsf F_B(\chi)(\mathbb K)}\le\norm{\mathsf F_B(\chi)}_{\mathrm{TV}}\le C_E$ and
$\frac12\big|\int\mu\lambda\,\dif\mathsf F_B(\chi)\big|\le C_{\cR}$;
\item $\norm{\mathsf F_B(\chi)-\mathsf F_B(\chi')}_{\mathrm{TV}}\le C_{\mathsf F}\norm{\chi-\chi'}_{\mathrm{TV}}$;
\item $\norm{\mathsf F_B(\chi)-\mathsf F_B(\chi')}_\BL\le C_{\mathsf F}\norm{\chi-\chi'}_\BL$.
\end{enumerate}
The same statements hold, with $C_E$, $C_{\cR}$, $C_{\mathsf F}$ depending
also on the bounds, on every set defined as $\mathfrak M$ with other
positive bounds on the mass and the risk.
\end{lemma}
```
-/
theorem lem_app_dyn_field_i_gen {m n : ℕ} {C : Covariances m n} (p : DynParams)
    (S : SpectralData C) {B : ℕ} (c : DynCoeff p S B)
    (hSout : opNorm C.Sout ≤ p.CSig) (hSin : opNorm C.Sin ≤ p.CSig) (M rlo rhi : ℝ) (hrlo : 0 < rlo)
    (χ : Measure (ℝ × ℝ)) (hχ : χ ∈ Adm p.CSig M rlo rhi) :
    |fieldOp p.h c.d c.ζ χ (fun _ => 1)| ≤ 2 * p.h * dMax p * M / Real.sqrt rlo + p.h ^ 2 * mZeta p ∧
    BddAbove ((fun φ => |fieldOp p.h c.d c.ζ χ φ|) ''
      {φ : ℝ × ℝ → ℝ | Measurable φ ∧ ∀ x, |φ x| ≤ 1}) ∧
    tvNorm (fun φ => fieldOp p.h c.d c.ζ χ φ) ≤
      2 * p.h * dMax p * M / Real.sqrt rlo + p.h ^ 2 * mZeta p ∧
    (1 / 2) * |fieldOp p.h c.d c.ζ χ (fun x => x.1 * x.2)| ≤
      2 * p.h * dMax p * Real.sqrt rhi + p.h ^ 2 * p.CSig ^ 2 * mZeta p / 2 := by
  have hB : ∀ φ : ℝ × ℝ → ℝ, (∀ x, |φ x| ≤ 1) →
      |fieldOp p.h c.d c.ζ χ φ| ≤ 2 * p.h * dMax p * M / Real.sqrt rlo + p.h ^ 2 * mZeta p :=
    fun φ hφ => field_pointwise p S c M rlo rhi hrlo χ hχ φ hφ
  have hq := field_quad p S c hSout hSin M rlo rhi hrlo χ hχ
  obtain ⟨hb, ht⟩ := tv_of_pointwise (fun φ => fieldOp p.h c.d c.ζ χ φ) _ hB
  exact ⟨hB (fun _ => 1) (fun _ => by norm_num), hb, ht, hq⟩

/-- `lem:app-dyn-field`, snapshot `cr-2026-10-23`. Part (ii), total variation Lipschitz bound; the constant depends only on `p` and the bounds `(M, rlo, rhi)`, and is chosen before the dimension and the measures. `𝔐` is the instance `M = E⋆+1`, `rlo = r₀/2`, `rhi = r₁+½`.

Source (`section.tex`, whole environment):
```latex
\begin{lemma}[The field]\label{lem:app-dyn-field}
There is $C_{\mathsf F}$, depending only on $(\macrostep,\ridge,C_\Sigma,E_\star,r_0,r_1)$
and on $m_\zeta$, such that for $\chi,\chi'\in\mathfrak M$:
\begin{enumerate}[label=(\roman*)]
\item $\abs{\mathsf F_B(\chi)(\mathbb K)}\le\norm{\mathsf F_B(\chi)}_{\mathrm{TV}}\le C_E$ and
$\frac12\big|\int\mu\lambda\,\dif\mathsf F_B(\chi)\big|\le C_{\cR}$;
\item $\norm{\mathsf F_B(\chi)-\mathsf F_B(\chi')}_{\mathrm{TV}}\le C_{\mathsf F}\norm{\chi-\chi'}_{\mathrm{TV}}$;
\item $\norm{\mathsf F_B(\chi)-\mathsf F_B(\chi')}_\BL\le C_{\mathsf F}\norm{\chi-\chi'}_\BL$.
\end{enumerate}
The same statements hold, with $C_E$, $C_{\cR}$, $C_{\mathsf F}$ depending
also on the bounds, on every set defined as $\mathfrak M$ with other
positive bounds on the mass and the risk.
\end{lemma}
```
-/
theorem lem_app_dyn_field_ii (p : DynParams) (M rlo rhi : ℝ) (hrlo : 0 < rlo) :
    ∃ CF : ℝ, ∀ {m n : ℕ} {C : Covariances m n} (S : SpectralData C) {B : ℕ}
      (c : DynCoeff p S B) (χ χ' : Measure (ℝ × ℝ)),
      χ ∈ Adm p.CSig M rlo rhi → χ' ∈ Adm p.CSig M rlo rhi →
      BddAbove ((fun φ => |fieldOp p.h c.d c.ζ χ φ - fieldOp p.h c.d c.ζ χ' φ|) ''
          {φ : ℝ × ℝ → ℝ | Measurable φ ∧ ∀ x, |φ x| ≤ 1}) ∧
        tvNorm (fun φ => fieldOp p.h c.d c.ζ χ φ - fieldOp p.h c.d c.ζ χ' φ) ≤
          CF * tvDist χ χ' := by
  refine ⟨2 * p.h / Real.sqrt rlo * (dMax p + 1) +
    2 * p.h * (1 / (Real.sqrt rlo) ^ 3) * ((p.CSig ^ 2 + 1) / 2) *
      (dMax p * |M|), ?_⟩
  intro m n C S B c χ χ' hχ hχ'
  haveI := hχ.1
  haveI := hχ'.1
  apply sup_of_pointwise {φ | Measurable φ ∧ ∀ x, |φ x| ≤ 1}
    ⟨fun _ => 0, measurable_const, by simp⟩
  intro φ hφ
  exact field_diff_bound p S c M rlo rhi (dMax p + 1) ((p.CSig ^ 2 + 1) / 2)
    (tvDist χ χ') hrlo χ χ' hχ hχ' φ
    (tv_d_diff p S c χ χ' hχ.2.1 hχ'.2.1 φ hφ.1 hφ.2)
    (tv_risk_diff p χ χ' hχ.2.1 hχ'.2.1) (fun x _ => hφ.2 x)

/-- `lem:app-dyn-field`, snapshot `cr-2026-10-23`. Part (iii), bounded-Lipschitz bound with the ℓ¹ class `blTest`, `blNorm`, `blDist` of `Dynamics.Basic`; constant as in (ii). `𝔐` is the instance `M = E⋆+1`, `rlo = r₀/2`, `rhi = r₁+½`.

Source (`section.tex`, whole environment):
```latex
\begin{lemma}[The field]\label{lem:app-dyn-field}
There is $C_{\mathsf F}$, depending only on $(\macrostep,\ridge,C_\Sigma,E_\star,r_0,r_1)$
and on $m_\zeta$, such that for $\chi,\chi'\in\mathfrak M$:
\begin{enumerate}[label=(\roman*)]
\item $\abs{\mathsf F_B(\chi)(\mathbb K)}\le\norm{\mathsf F_B(\chi)}_{\mathrm{TV}}\le C_E$ and
$\frac12\big|\int\mu\lambda\,\dif\mathsf F_B(\chi)\big|\le C_{\cR}$;
\item $\norm{\mathsf F_B(\chi)-\mathsf F_B(\chi')}_{\mathrm{TV}}\le C_{\mathsf F}\norm{\chi-\chi'}_{\mathrm{TV}}$;
\item $\norm{\mathsf F_B(\chi)-\mathsf F_B(\chi')}_\BL\le C_{\mathsf F}\norm{\chi-\chi'}_\BL$.
\end{enumerate}
The same statements hold, with $C_E$, $C_{\cR}$, $C_{\mathsf F}$ depending
also on the bounds, on every set defined as $\mathfrak M$ with other
positive bounds on the mass and the risk.
\end{lemma}
```
-/
theorem lem_app_dyn_field_iii (p : DynParams) (M rlo rhi : ℝ) (hrlo : 0 < rlo) :
    ∃ CF : ℝ, ∀ {m n : ℕ} {C : Covariances m n} (S : SpectralData C) {B : ℕ}
      (c : DynCoeff p S B) (χ χ' : Measure (ℝ × ℝ)),
      χ ∈ Adm p.CSig M rlo rhi → χ' ∈ Adm p.CSig M rlo rhi →
      BddAbove ((fun φ => |fieldOp p.h c.d c.ζ χ φ - fieldOp p.h c.d c.ζ χ' φ|) '' blTest p.CSig) ∧
        blNorm p.CSig (fun φ => fieldOp p.h c.d c.ζ χ φ - fieldOp p.h c.d c.ζ χ' φ) ≤
          CF * blDist p.CSig χ χ' := by
  refine ⟨2 * p.h / Real.sqrt rlo *
      (2 * dMax p + p.CSig / Real.sqrt (2 * p.ϱ) + 1) +
    2 * p.h * (1 / (Real.sqrt rlo) ^ 3) * ((p.CSig ^ 2 + p.CSig + 1) / 2) *
      (dMax p * |M|), ?_⟩
  intro m n C S B c χ χ' hχ hχ'
  haveI := hχ.1
  haveI := hχ'.1
  refine sup_of_pointwise (blTest p.CSig) ⟨fun _ => 0, ?_⟩ _ _ ?_
  · exact ⟨by simp, by intros; simp [l1]; positivity⟩
  · intro φ hφ
    exact field_diff_bound p S c M rlo rhi
      (2 * dMax p + p.CSig / Real.sqrt (2 * p.ϱ) + 1)
      ((p.CSig ^ 2 + p.CSig + 1) / 2) (blDist p.CSig χ χ') hrlo χ χ' hχ hχ' φ
      (bl_d_diff p S c χ χ' hχ.2.1 hχ'.2.1 φ hφ)
      (bl_risk_diff p χ χ' hχ.2.1 hχ'.2.1) hφ.1

/-! ### Private ODE helpers -/

/-- Positivity for a scalar inhomogeneous linear equation, in the within-interval form used by
the mode equations. -/
private lemma linear_ode_nonneg {T b : ℝ} (hT : 0 ≤ T) (a x : ℝ → ℝ)
    (ha : ContinuousOn a (Icc 0 T)) (hx0 : 0 ≤ x 0) (hb : 0 ≤ b)
    (hx : ∀ t ∈ Icc 0 T, HasDerivWithinAt x (-a t * x t + b) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, 0 ≤ x t := by
  intro t ht
  let A : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, a u
  have ha_int : IntervalIntegrable a volume 0 T :=
    ha.intervalIntegrable_of_Icc hT
  have hA_cont : ContinuousOn A (Icc 0 T) := by
    simpa only [A, uIcc_of_le hT] using
      (intervalIntegral.continuousOn_primitive_interval' ha_int left_mem_uIcc)
  have hx_cont : ContinuousOn x (Icc 0 T) :=
    fun s hs => (hx s hs).continuousWithinAt
  have hy_cont : ContinuousOn (fun s => Real.exp (A s) * x s) (Icc 0 T) :=
    (Real.continuous_exp.comp_continuousOn hA_cont).mul hx_cont
  have hy_deriv : ∀ s ∈ interior (Icc 0 T),
      HasDerivWithinAt (fun u => Real.exp (A u) * x u)
        (Real.exp (A s) * b) (interior (Icc 0 T)) s := by
    intro s hs
    have hs' : s ∈ Ioo 0 T := by simpa [interior_Icc] using hs
    have hAn : HasDerivAt A (a s) s := by
      have has : ContinuousAt a s :=
        (ha.continuousAt (Icc_mem_nhds hs'.1 hs'.2))
      exact intervalIntegral.integral_hasDerivAt_right
        (ha_int.mono_set (uIcc_subset_uIcc left_mem_uIcc (show s ∈ uIcc 0 T by
          simpa [uIcc_of_le hT] using (Ioo_subset_Icc_self hs'))))
        (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
          (fun z hz => ha.continuousAt (Icc_mem_nhds hz.1 hz.2)) s hs') has
    have hxn : HasDerivAt x (-a s * x s + b) s :=
      (hx s (Ioo_subset_Icc_self hs')).hasDerivAt (Icc_mem_nhds hs'.1 hs'.2)
    convert (hAn.exp.mul hxn).hasDerivWithinAt using 1 <;> ring
  have hy_mono : MonotoneOn (fun s => Real.exp (A s) * x s) (Icc 0 T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) hy_cont hy_deriv
      (fun s _ => mul_nonneg (Real.exp_pos _).le hb)
  have hmono := hy_mono (show 0 ∈ Icc 0 T by exact ⟨le_rfl, hT⟩) ht ht.1
  have hA0 : A 0 = 0 := by simp [A]
  change Real.exp (A 0) * x 0 ≤ Real.exp (A t) * x t at hmono
  rw [hA0, Real.exp_zero, one_mul] at hmono
  exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp (hx0.trans hmono)

private lemma mZeta_nonneg' (p : DynParams) : 0 ≤ mZeta p := by
  unfold mZeta kStar
  have hp : 0 ≤ p.γstar ^ 2 + 4 * p.γstar + 3 := by
    nlinarith [sq_nonneg p.γstar, p.hγ]
  have hk : 0 ≤ p.CSig * Real.sqrt
      (2 * p.γstar * (p.γstar ^ 2 + 4 * p.γstar + 3) / p.ϱ) := by
    exact mul_nonneg (by linarith [p.hC]) (Real.sqrt_nonneg _)
  have hd : 0 < 1 - p.β := by linarith [p.hβ.2]
  exact add_nonneg p.hγ (div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hk) p.hβ.1) hd.le)

private lemma CE_nonneg' (p : DynParams) : 0 ≤ CE p := by
  unfold CE
  exact add_nonneg
    (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hh.le)
      (dMax_nonneg' p)) (by linarith [p.hE])) (Real.sqrt_nonneg _))
    (mul_nonneg (sq_nonneg _) (mZeta_nonneg' p))

private lemma CR_nonneg' (p : DynParams) : 0 ≤ CR p := by
  unfold CR
  exact add_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hh.le) (dMax_nonneg' p))
      (Real.sqrt_nonneg _))
    (div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mZeta_nonneg' p)) (by norm_num))

private lemma Tstar_nonneg' (p : DynParams) : 0 ≤ Tstar p := by
  unfold Tstar
  exact div_nonneg (le_of_lt (lt_min p.hr0 zero_lt_one))
    (mul_nonneg (by norm_num) (by linarith [CE_nonneg' p, CR_nonneg' p]))

private lemma batch_pos_of_initial_risk {m n : ℕ} {C : Covariances m n}
    (p : DynParams) (S : SpectralData C) {B : ℕ} (Δ0 : Mat m n)
    (hdim : ((max m n : ℕ) : ℝ) ≤ p.γstar * (B : ℝ))
    (hR0 : p.r0 ≤ riskSigma C Δ0) : 0 < B := by
  apply Nat.pos_of_ne_zero
  intro hB
  have hmnR : ((max m n : ℕ) : ℝ) ≤ 0 := by simpa [hB] using hdim
  have hmn : max m n = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact_mod_cast hmnR
  have hm : m = 0 := by omega
  have hn : n = 0 := by omega
  subst m
  subst n
  have hrisk : riskSigma C Δ0 = 0 := by
    simp [riskSigma, pairSigma, Matrix.trace]
  linarith [p.hr0]

private lemma atom_mass_nonneg {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (q : Fin m → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j) :
    (atomMeasure μ lam q).real univ = ∑ i, ∑ j, q i j := by
  unfold atomMeasure
  rw [Measure.real_def]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.sum_ne_top.mpr fun j _ => ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.toReal_sum (fun j _ => ENNReal.ofReal_ne_top)]
  exact Finset.sum_congr rfl fun j _ => ENNReal.toReal_ofReal (hq i j)

private lemma forcing_mass_le {m n : ℕ} {C : Covariances m n}
    (p : DynParams) (S : SpectralData C) {B : ℕ} (c : DynCoeff p S B) (hB : 0 < B) :
    ∑ i, ∑ j, c.v i j / (B : ℝ) ≤ mZeta p := by
  rw [← atom_mass_nonneg S.μ S.lam (fun i j => c.v i j / (B : ℝ))
    (fun i j => div_nonneg (c.v_nonneg i j) (Nat.cast_nonneg B)), ← c.ζ_eq]
  exact c.ζ_mass

private lemma fro_sq_eq_sum_sq {m n : ℕ} (A : Mat m n) :
    fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma modeQ_sum_eq_fro_sq {m n : ℕ} {C : Covariances m n}
    (S : SpectralData C) (Δ : Mat m n) : ∑ i, ∑ j, modeQ S Δ i j = fro Δ ^ 2 := by
  have htrace : ∀ {a b : ℕ} (Y : Mat a b),
      (Y * Matrix.transpose Y).trace = fro Y ^ 2 := by
    intro a b Y
    rw [fro_sq_eq_sum_sq]
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_two]
  have he : fro (Matrix.transpose S.uOut * Δ * S.vIn) ^ 2 = fro Δ ^ 2 := by
    rw [← htrace, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S.vIn (Matrix.transpose S.vIn),
      mul_eq_one_comm.mp S.hvIn, Matrix.one_mul]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
    rw [mul_eq_one_comm.mp S.huOut, Matrix.mul_one, htrace]
  rw [← he, fro_sq_eq_sum_sq]
  simp_rw [P_apply, modeQ]

private lemma normalized_initial_risk {m n : ℕ} {C : Covariances m n}
    (S : SpectralData C) (Δ : Mat m n) :
    (1 / 2) * ∑ i, ∑ j, S.μ i * S.lam j * modeQ S Δ i j = riskSigma C Δ := by
  rw [riskSigma]
  calc
    _ = (1 / 2) * pairSigma C Δ Δ := (lem_app_setup_decomposition_ii S Δ).symm
    _ = _ := by ring

private lemma locallyLipschitz_pi_finite {α β ι : Type*} [PseudoMetricSpace α]
    [PseudoMetricSpace β] [Fintype ι]
    (f : α → ι → β) (hf : ∀ i, LocallyLipschitz (fun x => f x i)) :
    LocallyLipschitz f := by
  classical
  intro x
  let K : ι → NNReal := fun i => (hf i x).choose
  let u : ι → Set α := fun i => (hf i x).choose_spec.choose
  have hxu (i : ι) : u i ∈ 𝓝 x := (hf i x).choose_spec.choose_spec.1
  have hK (i : ι) : LipschitzOnWith (K i) (fun y => f y i) (u i) :=
    (hf i x).choose_spec.choose_spec.2
  let U : Set α := ⋂ i, u i
  let L : NNReal := ∑ i, K i
  refine ⟨L, U, ?_, LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_⟩
  · rw [Filter.iInter_mem]
    exact fun i => hxu i
  · apply (dist_pi_le_iff (mul_nonneg L.2 dist_nonneg)).2
    intro i
    have hKi : K i ≤ L := Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)
    exact ((hK i).dist_le_mul y (Set.mem_iInter.mp hy i) z (Set.mem_iInter.mp hz i)).trans
      (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 hKi) dist_nonneg)

private lemma locallyLipschitz_invSqrt_max {δ : ℝ} (hδ : 0 < δ) :
    LocallyLipschitz (fun x : ℝ => 1 / Real.sqrt (max δ x)) := by
  have hinner : LocallyLipschitz (fun x : ℝ => max δ x) :=
    LocallyLipschitz.const_max LocallyLipschitz.id δ
  intro x
  obtain ⟨Kg, t, hxt, hKg⟩ := hinner x
  have hy : 0 < max δ x := hδ.trans_le (le_max_left _ _)
  have houter : ContDiffAt ℝ 1 (fun y : ℝ => 1 / Real.sqrt y) (max δ x) :=
    contDiffAt_const.div (Real.contDiffAt_sqrt hy.ne') (Real.sqrt_pos.2 hy).ne'
  obtain ⟨Kf, u, hu, hKf⟩ := houter.exists_lipschitzOnWith
  refine ⟨Kf * Kg, t ∩ (fun y : ℝ => max δ y) ⁻¹' u,
    Filter.inter_mem hxt (hinner.continuous.continuousAt hu), ?_⟩
  exact hKf.comp (hKg.mono inter_subset_left)
    ((mapsTo_preimage (fun y : ℝ => max δ y) u).mono_left inter_subset_right)

private lemma truncated_rhs_locallyLipschitz {m n : ℕ} (h : ℝ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (d : ℝ × ℝ → ℝ)
    (b : Fin m → Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    LocallyLipschitz (fun q : Fin m → Fin n → ℝ => fun i j =>
      -(2 * h * d (μ i, lam j)) /
          Real.sqrt (max δ ((1 / 2) * ∑ a, ∑ k, μ a * lam k * q a k)) * q i j + b i j) := by
  let R : (Fin m → Fin n → ℝ) → ℝ := fun q =>
    (1 / 2) * ∑ a, ∑ k, μ a * lam k * q a k
  have hR : ContDiff ℝ 1 R := by
    dsimp only [R]
    fun_prop
  have hg : LocallyLipschitz (fun q => 1 / Real.sqrt (max δ (R q))) :=
    (locallyLipschitz_invSqrt_max hδ).comp hR.locallyLipschitz
  apply locallyLipschitz_pi_finite
  intro i
  apply locallyLipschitz_pi_finite
  intro j
  have hproj : LocallyLipschitz (fun q : Fin m → Fin n → ℝ => q i j) := by
    exact (by fun_prop : ContDiff ℝ 1 (fun q : Fin m → Fin n → ℝ => q i j)).locallyLipschitz
  have hc : LocallyLipschitz
      (fun _q : Fin m → Fin n → ℝ => -(2 * h * d (μ i, lam j))) :=
    LocallyLipschitz.const _
  have hb : LocallyLipschitz (fun _q : Fin m → Fin n → ℝ => b i j) :=
    LocallyLipschitz.const _
  have hmul : LocallyLipschitz (fun z : ℝ × ℝ => z.1 * z.2) :=
    (by fun_prop : ContDiff ℝ 1 (fun z : ℝ × ℝ => z.1 * z.2)).locallyLipschitz
  have hadd : LocallyLipschitz (fun z : ℝ × ℝ => z.1 + z.2) :=
    (by fun_prop : ContDiff ℝ 1 (fun z : ℝ × ℝ => z.1 + z.2)).locallyLipschitz
  have hcg : LocallyLipschitz (fun q : Fin m → Fin n → ℝ =>
      -(2 * h * d (μ i, lam j)) * (1 / Real.sqrt (max δ (R q)))) := by
    exact hmul.comp (hc.prodMk hg)
  have hp0 : LocallyLipschitz (fun q : Fin m → Fin n → ℝ =>
      -(2 * h * d (μ i, lam j)) * (1 / Real.sqrt (max δ (R q))) * q i j) :=
    hmul.comp (hcg.prodMk hproj)
  have hp : LocallyLipschitz (fun q : Fin m → Fin n → ℝ =>
      -(2 * h * d (μ i, lam j)) * (1 / Real.sqrt (max δ (R q))) * q i j + b i j) :=
    hadd.comp (hp0.prodMk hb)
  convert hp using 1
  funext q
  dsimp only [R]
  ring

private lemma truncated_odeRHS_locallyLipschitz {m n : ℕ} (h B : ℝ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (d : ℝ × ℝ → ℝ)
    (v : Fin m → Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    LocallyLipschitz (fun q : Fin m → Fin n → ℝ => fun i j =>
      -(2 * h * d (μ i, lam j)) /
          Real.sqrt (max δ (odeRisk μ lam B q)) * q i j + h ^ 2 * B * v i j) := by
  let R : (Fin m → Fin n → ℝ) → ℝ := odeRisk μ lam B
  have hR : ContDiff ℝ 1 R := by
    change ContDiff ℝ 1 (fun q : Fin m → Fin n → ℝ =>
      (1 / 2) * ∑ i, ∑ j, μ i * lam j * q i j / B ^ 2)
    fun_prop
  have hg : LocallyLipschitz (fun q => 1 / Real.sqrt (max δ (R q))) :=
    (locallyLipschitz_invSqrt_max hδ).comp hR.locallyLipschitz
  apply locallyLipschitz_pi_finite
  intro i
  apply locallyLipschitz_pi_finite
  intro j
  have hproj : LocallyLipschitz (fun q : Fin m → Fin n → ℝ => q i j) := by
    exact (by fun_prop : ContDiff ℝ 1 (fun q : Fin m → Fin n → ℝ => q i j)).locallyLipschitz
  have hc : LocallyLipschitz
      (fun _q : Fin m → Fin n → ℝ => -(2 * h * d (μ i, lam j))) :=
    LocallyLipschitz.const _
  have hb : LocallyLipschitz
      (fun _q : Fin m → Fin n → ℝ => h ^ 2 * B * v i j) :=
    LocallyLipschitz.const _
  have hmul : LocallyLipschitz (fun z : ℝ × ℝ => z.1 * z.2) :=
    (by fun_prop : ContDiff ℝ 1 (fun z : ℝ × ℝ => z.1 * z.2)).locallyLipschitz
  have hadd : LocallyLipschitz (fun z : ℝ × ℝ => z.1 + z.2) :=
    (by fun_prop : ContDiff ℝ 1 (fun z : ℝ × ℝ => z.1 + z.2)).locallyLipschitz
  have hcg : LocallyLipschitz (fun q : Fin m → Fin n → ℝ =>
      -(2 * h * d (μ i, lam j)) * (1 / Real.sqrt (max δ (R q)))) :=
    hmul.comp (hc.prodMk hg)
  have hp0 : LocallyLipschitz (fun q : Fin m → Fin n → ℝ =>
      -(2 * h * d (μ i, lam j)) * (1 / Real.sqrt (max δ (R q))) * q i j) :=
    hmul.comp (hcg.prodMk hproj)
  have hp := hadd.comp (hp0.prodMk hb)
  convert hp using 1
  funext q
  simp only [Function.comp_apply]
  ring

private lemma Tstar_mul_le_eighth (p : DynParams) {A : ℝ} (hA : 0 ≤ A)
    (hAsum : A ≤ 1 + CE p + CR p) :
    A * Tstar p ≤ 1 / 8 := by
  have hden : 0 < 8 * (1 + CE p + CR p) := by
    exact mul_pos (by norm_num) (by linarith [CE_nonneg' p, CR_nonneg' p])
  have hmin : min p.r0 1 ≤ 1 := min_le_right _ _
  have hnum : A * min p.r0 1 ≤ 1 + CE p + CR p := by
    calc
      A * min p.r0 1 ≤ A * 1 := mul_le_mul_of_nonneg_left hmin hA
      _ ≤ 1 + CE p + CR p := by simpa using hAsum
  unfold Tstar
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).2
  field_simp
  nlinarith

private lemma Tstar_mul_le_min_eighth (p : DynParams) {A : ℝ} (hA : 0 ≤ A)
    (hAsum : A ≤ 1 + CE p + CR p) :
    A * Tstar p ≤ min p.r0 1 / 8 := by
  have hsum : 0 < 1 + CE p + CR p := by linarith [CE_nonneg' p, CR_nonneg' p]
  have hmin : 0 ≤ min p.r0 1 := (lt_min p.hr0 zero_lt_one).le
  unfold Tstar
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos (by norm_num) hsum)).2
  have hm := mul_le_mul_of_nonneg_right hAsum hmin
  nlinarith

private lemma truncated_odeRHS_bound {m n : ℕ} {C : Covariances m n}
    (p : DynParams) (S : SpectralData C) {B : ℕ} (c : DynCoeff p S B)
    (hSout : opNorm C.Sout ≤ p.CSig) (hSin : opNorm C.Sin ≤ p.CSig)
    {δ : ℝ} (hδ : 0 < δ) (q : Fin m → Fin n → ℝ) :
    ‖(fun i j =>
      -(2 * p.h * c.d (S.μ i, S.lam j)) /
          Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) * q i j +
        p.h ^ 2 * (B : ℝ) * c.v i j)‖ ≤
      (2 * p.h * dMax p / Real.sqrt δ) * ‖q‖ +
        ‖(fun i j => p.h ^ 2 * (B : ℝ) * c.v i j)‖ := by
  have hδsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hsqrt : Real.sqrt δ ≤ Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) :=
    Real.sqrt_le_sqrt (le_max_left _ _)
  have hA : 0 ≤ 2 * p.h * dMax p / Real.sqrt δ :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hh.le) (dMax_nonneg' p)) hδsqrt.le
  have hforce : 0 ≤ ‖(fun i j => p.h ^ 2 * (B : ℝ) * c.v i j)‖ := norm_nonneg _
  rw [pi_norm_le_iff_of_nonneg (add_nonneg (mul_nonneg hA (norm_nonneg _)) hforce)]
  intro i
  rw [pi_norm_le_iff_of_nonneg (add_nonneg (mul_nonneg hA (norm_nonneg _)) hforce)]
  intro j
  rw [Real.norm_eq_abs]
  have hdij : 0 ≤ c.d (S.μ i, S.lam j) ∧ c.d (S.μ i, S.lam j) ≤ dMax p :=
    ⟨c.d_nonneg _ ⟨⟨μ_nonneg S i, (le_abs_self _).trans ((abs_mu_le_opNorm S i).trans hSout)⟩,
        ⟨lam_nonneg S j, (le_abs_self _).trans ((abs_lam_le_opNorm S j).trans hSin)⟩⟩,
      c.d_le _ ⟨⟨μ_nonneg S i, (le_abs_self _).trans ((abs_mu_le_opNorm S i).trans hSout)⟩,
        ⟨lam_nonneg S j, (le_abs_self _).trans ((abs_lam_le_opNorm S j).trans hSin)⟩⟩⟩
  have hspos : 0 < Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) :=
    Real.sqrt_pos.2 (hδ.trans_le (le_max_left _ _))
  have hcoef :
      |-(2 * p.h * c.d (S.μ i, S.lam j)) /
          Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q))| ≤
        2 * p.h * dMax p / Real.sqrt δ := by
    rw [abs_div, abs_neg,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hh.le) hdij.1),
      abs_of_pos hspos]
    exact div_le_div₀
      (mul_nonneg (mul_nonneg (by norm_num) p.hh.le) (dMax_nonneg' p))
      (mul_le_mul_of_nonneg_left hdij.2 (mul_nonneg (by norm_num) p.hh.le)) hδsqrt hsqrt
  calc
    |-(2 * p.h * c.d (S.μ i, S.lam j)) /
          Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) * q i j +
        p.h ^ 2 * (B : ℝ) * c.v i j| ≤
        |-(2 * p.h * c.d (S.μ i, S.lam j)) /
          Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q))| * |q i j| +
        |p.h ^ 2 * (B : ℝ) * c.v i j| := by
          convert abs_add_le
            (-(2 * p.h * c.d (S.μ i, S.lam j)) /
              Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) * q i j)
            (p.h ^ 2 * (B : ℝ) * c.v i j) using 1 <;> simp only [abs_mul] <;> ring
    _ ≤ (2 * p.h * dMax p / Real.sqrt δ) * ‖q‖ +
        ‖(fun i j => p.h ^ 2 * (B : ℝ) * c.v i j)‖ := by
      apply add_le_add
      · exact mul_le_mul hcoef
          ((norm_le_pi_norm (q i) j).trans (norm_le_pi_norm q i))
          (abs_nonneg _) hA
      · exact (norm_le_pi_norm ((fun i j => p.h ^ 2 * (B : ℝ) * c.v i j) i) j).trans
          (norm_le_pi_norm (fun i j => p.h ^ 2 * (B : ℝ) * c.v i j) i)

private lemma exists_ode_on_Icc_of_locallyLipschitz_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (F : E → E) (x0 : E) (T : ℝ) (hT : 0 ≤ T) (a L : NNReal)
    (hF : LocallyLipschitz F)
    (hbound : ∀ x ∈ Metric.closedBall x0 (a : ℝ), ‖F x‖ ≤ (L : ℝ))
    (hLT : (L : ℝ) * T ≤ (a : ℝ)) :
    ∃ x : ℝ → E, x 0 = x0 ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt x (F (x t)) (Icc 0 T) t := by
  obtain ⟨K, hK⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (isCompact_closedBall x0 (a : ℝ))
      hF.locallyLipschitzOn
  let t0 : Icc (0 : ℝ) T := ⟨0, left_mem_Icc.2 hT⟩
  have hpl : IsPicardLindelof (fun _ => F) t0 x0 a 0 L K :=
    IsPicardLindelof.of_time_independent hbound hK (by simpa [t0, max_eq_left hT] using hLT)
  simpa only [t0] using hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

private lemma truncated_ode_nonneg {m n : ℕ} {C : Covariances m n} (p : DynParams)
    (S : SpectralData C) {B : ℕ} (c : DynCoeff p S B) (e0 : Fin m → Fin n → ℝ)
    (T : ℝ) (hT : 0 ≤ T) {δ : ℝ} (hδ : 0 < δ) (e : ℝ → Fin m → Fin n → ℝ)
    (he0 : ∀ i j, 0 ≤ e0 i j) (heinit : e 0 = e0)
    (he : ∀ t ∈ Icc 0 T, HasDerivWithinAt e
      (fun i j => -(2 * p.h * c.d (S.μ i, S.lam j)) /
          Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) (e t))) * e t i j +
        p.h ^ 2 * (B : ℝ) * c.v i j) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, ∀ i j, 0 ≤ e t i j := by
  have he_cont : ContinuousOn e (Icc 0 T) := fun t ht => (he t ht).continuousWithinAt
  have hR_cont : ContinuousOn
      (fun t => odeRisk S.μ S.lam (B : ℝ) (e t)) (Icc 0 T) := by
    unfold odeRisk
    fun_prop
  intro t ht i j
  let a : ℝ → ℝ := fun s =>
    2 * p.h * c.d (S.μ i, S.lam j) /
      Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) (e s)))
  have ha : ContinuousOn a (Icc 0 T) := by
    apply ContinuousOn.div continuousOn_const
      (continuous_max.comp_continuousOn (continuousOn_const.prodMk hR_cont)).sqrt
    intro s hs
    exact (Real.sqrt_pos.2 (hδ.trans_le (le_max_left _ _))).ne'
  refine linear_ode_nonneg (b := p.h ^ 2 * (B : ℝ) * c.v i j)
    hT a (fun s => e s i j) ha ?_ ?_ ?_ t ht
  · rw [heinit]
    exact he0 i j
  · exact mul_nonneg (mul_nonneg (sq_nonneg p.h) (Nat.cast_nonneg B)) (c.v_nonneg i j)
  · intro s hs
    have hv := (he s hs).hasFDerivWithinAt
    have hi := hasFDerivWithinAt_pi'.mp hv i
    have hij := hasFDerivWithinAt_pi'.mp hi j
    have hij' := hij.hasDerivWithinAt
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hij'
    convert hij' using 1
    dsimp only [a]
    ring

private lemma odeRisk_hasDerivWithinAt {m n : ℕ} (B : ℝ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (e : ℝ → Fin m → Fin n → ℝ) (F : Fin m → Fin n → ℝ)
    (s : Set ℝ) (t : ℝ) (he : HasDerivWithinAt e F s t) :
    HasDerivWithinAt (fun u => odeRisk μ lam B (e u)) (odeRisk μ lam B F) s t := by
  have hcoord (i : Fin m) (j : Fin n) :
      HasDerivWithinAt (fun u => e u i j) (F i j) s t := by
    have hv := he.hasFDerivWithinAt
    have hi := hasFDerivWithinAt_pi'.mp hv i
    have hij := hasFDerivWithinAt_pi'.mp hi j
    simpa only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
      using hij.hasDerivWithinAt
  unfold odeRisk
  have hj (i : Fin m) : HasDerivWithinAt
      (∑ j, fun u => (μ i * lam j / B ^ 2) * e u i j)
      (∑ j, (μ i * lam j / B ^ 2) * F i j) s t := by
    exact HasDerivWithinAt.sum (u := Finset.univ) fun j _ =>
      (hcoord i j).const_mul (μ i * lam j / B ^ 2)
  have hi : HasDerivWithinAt
      (∑ i, ∑ j, fun u => (μ i * lam j / B ^ 2) * e u i j)
      (∑ i, ∑ j, (μ i * lam j / B ^ 2) * F i j) s t := by
    exact HasDerivWithinAt.sum (u := Finset.univ) fun i _ => hj i
  convert hi.const_mul (1 / 2) using 1
  · funext u
    simp only [Finset.sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

private lemma spectral_pair_bounds {m n : ℕ} {C : Covariances m n}
    (p : DynParams) (S : SpectralData C) (hSout : opNorm C.Sout ≤ p.CSig)
    (hSin : opNorm C.Sin ≤ p.CSig) (i : Fin m) (j : Fin n) :
    0 ≤ S.μ i * S.lam j ∧ S.μ i * S.lam j ≤ p.CSig ^ 2 := by
  have hμ : 0 ≤ S.μ i ∧ S.μ i ≤ p.CSig :=
    ⟨μ_nonneg S i, (le_abs_self _).trans ((abs_mu_le_opNorm S i).trans hSout)⟩
  have hl : 0 ≤ S.lam j ∧ S.lam j ≤ p.CSig :=
    ⟨lam_nonneg S j, (le_abs_self _).trans ((abs_lam_le_opNorm S j).trans hSin)⟩
  exact ⟨mul_nonneg hμ.1 hl.1, by nlinarith [mul_le_mul hμ.2 hl.2 hl.1 (by linarith [p.hC])]⟩

private lemma forcing_risk_bounds {m n : ℕ} {C : Covariances m n}
    (p : DynParams) (S : SpectralData C) {B : ℕ} (c : DynCoeff p S B)
    (hSout : opNorm C.Sout ≤ p.CSig) (hSin : opNorm C.Sin ≤ p.CSig) (hB : 0 < B) :
    0 ≤ odeRisk S.μ S.lam (B : ℝ)
        (fun i j => p.h ^ 2 * (B : ℝ) * c.v i j) ∧
    odeRisk S.μ S.lam (B : ℝ)
        (fun i j => p.h ^ 2 * (B : ℝ) * c.v i j) ≤
      p.h ^ 2 * p.CSig ^ 2 * mZeta p / 2 := by
  have hBc : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hsum0 : 0 ≤ ∑ i, ∑ j, S.μ i * S.lam j * (c.v i j / (B : ℝ)) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (spectral_pair_bounds p S hSout hSin i j).1
        (div_nonneg (c.v_nonneg i j) hBc.le)
  have hsum : ∑ i, ∑ j, S.μ i * S.lam j * (c.v i j / (B : ℝ)) ≤
      p.CSig ^ 2 * mZeta p := by
    calc
      _ ≤ ∑ i, ∑ j, p.CSig ^ 2 * (c.v i j / (B : ℝ)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (spectral_pair_bounds p S hSout hSin i j).2
            (div_nonneg (c.v_nonneg i j) hBc.le)
      _ = p.CSig ^ 2 * ∑ i, ∑ j, c.v i j / (B : ℝ) := by
        simp_rw [Finset.mul_sum]
      _ ≤ p.CSig ^ 2 * mZeta p :=
        mul_le_mul_of_nonneg_left (forcing_mass_le p S c hB) (sq_nonneg _)
  unfold odeRisk
  have heq : ∀ i j, S.μ i * S.lam j * (p.h ^ 2 * (B : ℝ) * c.v i j) / (B : ℝ) ^ 2 =
      p.h ^ 2 * (S.μ i * S.lam j * (c.v i j / (B : ℝ))) := by
    intro i j
    field_simp
  simp_rw [heq, ← Finset.mul_sum]
  constructor <;> nlinarith [sq_nonneg p.h]

private lemma drift_risk_bounds {m n : ℕ} {C : Covariances m n}
    (p : DynParams) (S : SpectralData C) {B : ℕ} (c : DynCoeff p S B)
    (hSout : opNorm C.Sout ≤ p.CSig) (hSin : opNorm C.Sin ≤ p.CSig)
    (hB : 0 < B) {δ : ℝ} (hδ : 0 < δ) (q : Fin m → Fin n → ℝ)
    (hq : ∀ i j, 0 ≤ q i j) (hRhi : odeRisk S.μ S.lam (B : ℝ) q ≤ p.r1 + 1) :
    -(2 * p.h * dMax p * Real.sqrt (p.r1 + 1)) ≤
      odeRisk S.μ S.lam (B : ℝ)
        (fun i j => -(2 * p.h * c.d (S.μ i, S.lam j)) /
          Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) * q i j) ∧
    odeRisk S.μ S.lam (B : ℝ)
        (fun i j => -(2 * p.h * c.d (S.μ i, S.lam j)) /
          Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) * q i j) ≤ 0 := by
  have hBc : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  let R := odeRisk S.μ S.lam (B : ℝ) q
  have hR0 : 0 ≤ R := by
    dsimp only [R, odeRisk]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      div_nonneg (mul_nonneg (spectral_pair_bounds p S hSout hSin i j).1 (hq i j))
        (sq_nonneg _))
  have hspos : 0 < Real.sqrt (max δ R) := Real.sqrt_pos.2 (hδ.trans_le (le_max_left _ _))
  have hdsum0 : 0 ≤ (1 / 2) * ∑ i, ∑ j,
      S.μ i * S.lam j * (c.d (S.μ i, S.lam j) * q i j) / (B : ℝ) ^ 2 := by
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      div_nonneg (mul_nonneg (spectral_pair_bounds p S hSout hSin i j).1
        (mul_nonneg (c.d_nonneg _
          ⟨⟨μ_nonneg S i, (le_abs_self _).trans ((abs_mu_le_opNorm S i).trans hSout)⟩,
           ⟨lam_nonneg S j, (le_abs_self _).trans ((abs_lam_le_opNorm S j).trans hSin)⟩⟩)
          (hq i j))) (sq_nonneg _))
  have hdsum : (1 / 2) * ∑ i, ∑ j,
      S.μ i * S.lam j * (c.d (S.μ i, S.lam j) * q i j) / (B : ℝ) ^ 2 ≤
      dMax p * R := by
    have hraw : (∑ i, ∑ j,
        S.μ i * S.lam j * (c.d (S.μ i, S.lam j) * q i j) / (B : ℝ) ^ 2) ≤
        dMax p * (∑ i, ∑ j, S.μ i * S.lam j * q i j / (B : ℝ) ^ 2) := by
      calc
        _ ≤ ∑ i, ∑ j, dMax p * (S.μ i * S.lam j * q i j / (B : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          have hd := c.d_le (S.μ i, S.lam j)
            ⟨⟨μ_nonneg S i, (le_abs_self _).trans ((abs_mu_le_opNorm S i).trans hSout)⟩,
             ⟨lam_nonneg S j, (le_abs_self _).trans ((abs_lam_le_opNorm S j).trans hSin)⟩⟩
          have hw := (spectral_pair_bounds p S hSout hSin i j).1
          have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd (hq i j)) hw
          exact (div_le_div_of_nonneg_right hh (sq_nonneg _)).trans_eq (by ring)
        _ = _ := by simp_rw [Finset.mul_sum]
    dsimp only [R, odeRisk]
    nlinarith [dMax_nonneg' p]
  have hsqrtR : R / Real.sqrt (max δ R) ≤ Real.sqrt (p.r1 + 1) := by
    have hr1 : 0 ≤ p.r1 + 1 := by linarith [p.hr0, p.hr]
    by_cases hz : R = 0
    · simp [hz, hr1]
    · have hRp : 0 < R := lt_of_le_of_ne hR0 (Ne.symm hz)
      have h1 : R / Real.sqrt (max δ R) ≤ R / Real.sqrt R :=
        div_le_div_of_nonneg_left hR0 (Real.sqrt_pos.2 hRp)
          (Real.sqrt_le_sqrt (le_max_right _ _))
      calc
        R / Real.sqrt (max δ R) ≤ R / Real.sqrt R := h1
        _ = Real.sqrt R := by rw [Real.div_sqrt]
        _ ≤ Real.sqrt (p.r1 + 1) := Real.sqrt_le_sqrt hRhi
  dsimp only [R] at hR0 hRhi hdsum hsqrtR
  have heq : (1 / 2) * ∑ i, ∑ j,
      S.μ i * S.lam j *
        (-(2 * p.h * c.d (S.μ i, S.lam j)) /
          Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) * q i j) / (B : ℝ) ^ 2 =
      -(2 * p.h / Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q))) *
        ((1 / 2) * ∑ i, ∑ j,
          S.μ i * S.lam j * (c.d (S.μ i, S.lam j) * q i j) / (B : ℝ) ^ 2) := by
    have hterm : ∀ i j, S.μ i * S.lam j *
        (-(2 * p.h * c.d (S.μ i, S.lam j)) /
          Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) * q i j) / (B : ℝ) ^ 2 =
        -(2 * p.h / Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q))) *
          (S.μ i * S.lam j * (c.d (S.μ i, S.lam j) * q i j) / (B : ℝ) ^ 2) := by
      intro i j
      ring
    simp_rw [hterm, ← Finset.mul_sum]
    ring
  change -(2 * p.h * dMax p * Real.sqrt (p.r1 + 1)) ≤
      (1 / 2) * ∑ i, ∑ j,
        S.μ i * S.lam j * (-(2 * p.h * c.d (S.μ i, S.lam j)) /
          Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) * q i j) / (B : ℝ) ^ 2 ∧
    (1 / 2) * ∑ i, ∑ j,
        S.μ i * S.lam j * (-(2 * p.h * c.d (S.μ i, S.lam j)) /
          Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) * q i j) / (B : ℝ) ^ 2 ≤ 0
  rw [heq]
  constructor
  · have hpref : 0 ≤ 2 * p.h / Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) :=
      div_nonneg (mul_nonneg (by norm_num) p.hh.le) hspos.le
    have hm := mul_le_mul_of_nonneg_left hdsum hpref
    have hs : (2 * p.h * dMax p) *
        (odeRisk S.μ S.lam (B : ℝ) q /
          Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q))) ≤
        (2 * p.h * dMax p) * Real.sqrt (p.r1 + 1) :=
      mul_le_mul_of_nonneg_left hsqrtR
        (mul_nonneg (mul_nonneg (by norm_num) p.hh.le) (dMax_nonneg' p))
    have hall : 2 * p.h / Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) *
        ((1 / 2) * ∑ i, ∑ j,
          S.μ i * S.lam j * (c.d (S.μ i, S.lam j) * q i j) / (B : ℝ) ^ 2) ≤
        2 * p.h * dMax p * Real.sqrt (p.r1 + 1) := by
      have hs' : 2 * p.h / Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) *
          (dMax p * odeRisk S.μ S.lam (B : ℝ) q) ≤
          2 * p.h * dMax p * Real.sqrt (p.r1 + 1) := by
        convert hs using 1 <;> ring
      exact hm.trans hs'
    simpa only [neg_mul] using neg_le_neg hall
  · exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg (mul_nonneg (by norm_num) p.hh.le) hspos.le)) hdsum0

private lemma drift_risk_nonpos {m n : ℕ} {C : Covariances m n}
    (p : DynParams) (S : SpectralData C) {B : ℕ} (c : DynCoeff p S B)
    (hSout : opNorm C.Sout ≤ p.CSig) (hSin : opNorm C.Sin ≤ p.CSig)
    {δ : ℝ} (hδ : 0 < δ) (q : Fin m → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j) :
    odeRisk S.μ S.lam (B : ℝ)
        (fun i j => -(2 * p.h * c.d (S.μ i, S.lam j)) /
          Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) * q i j) ≤ 0 := by
  unfold odeRisk
  apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
  apply Finset.sum_nonpos
  intro i _
  apply Finset.sum_nonpos
  intro j _
  have hd0 := c.d_nonneg (S.μ i, S.lam j)
    ⟨⟨μ_nonneg S i, (le_abs_self _).trans ((abs_mu_le_opNorm S i).trans hSout)⟩,
     ⟨lam_nonneg S j, (le_abs_self _).trans ((abs_lam_le_opNorm S j).trans hSin)⟩⟩
  have hspos : 0 < Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) :=
    Real.sqrt_pos.2 (hδ.trans_le (le_max_left _ _))
  have hcoef0 : 0 ≤ 2 * p.h * c.d (S.μ i, S.lam j) :=
    mul_nonneg (mul_nonneg (by norm_num) p.hh.le) hd0
  have hneg : -(2 * p.h * c.d (S.μ i, S.lam j)) /
      Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcoef0) hspos.le
  have hnum : S.μ i * S.lam j *
      (-(2 * p.h * c.d (S.μ i, S.lam j)) /
        Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) * q i j) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (spectral_pair_bounds p S hSout hSin i j).1
      (mul_nonpos_of_nonpos_of_nonneg
        hneg (hq i j))
  exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg (B : ℝ))

private lemma function_bounds_of_deriv {T lo hi : ℝ} (hT : 0 ≤ T) (f f' : ℝ → ℝ)
    (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (f' t) (Icc 0 T) t)
    (hlo : ∀ t ∈ Icc 0 T, lo ≤ f' t) (hhi : ∀ t ∈ Icc 0 T, f' t ≤ hi) :
    ∀ t ∈ Icc 0 T, f 0 + lo * t ≤ f t ∧ f t ≤ f 0 + hi * t := by
  have hc_lo : ContinuousOn (fun s => f s - lo * s) (Icc 0 T) :=
    hc.sub (continuousOn_const.mul continuousOn_id)
  have hc_hi : ContinuousOn (fun s => hi * s - f s) (Icc 0 T) :=
    (continuousOn_const.mul continuousOn_id).sub hc
  have hm_lo : MonotoneOn (fun s => f s - lo * s) (Icc 0 T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) hc_lo (by
      intro s hs
      have hs' : s ∈ Icc 0 T := interior_subset hs
      change HasDerivWithinAt (fun u => f u - lo * u) (f' s - lo) (interior (Icc 0 T)) s
      have hh := ((hd s hs').mono interior_subset).sub
        ((hasDerivWithinAt_id s (interior (Icc 0 T))).const_mul lo)
      convert hh using 1
      · ext u
        rfl
      · simp)
      (fun s hs => by
        have hs' : s ∈ Icc 0 T := interior_subset hs
        linarith [hlo s hs'])
  have hm_hi : MonotoneOn (fun s => hi * s - f s) (Icc 0 T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) hc_hi (by
      intro s hs
      have hs' : s ∈ Icc 0 T := interior_subset hs
      change HasDerivWithinAt (fun u => hi * u - f u) (hi - f' s) (interior (Icc 0 T)) s
      have hh := ((hasDerivWithinAt_id s (interior (Icc 0 T))).const_mul hi).sub
        ((hd s hs').mono interior_subset)
      convert hh using 1
      · ext u
        rfl
      · simp)
      (fun s hs => by
        have hs' : s ∈ Icc 0 T := interior_subset hs
        linarith [hhi s hs'])
  intro t ht
  have h0 : 0 ∈ Icc 0 T := ⟨le_rfl, hT⟩
  constructor
  · have := hm_lo h0 ht ht.1
    linarith
  · have := hm_hi h0 ht ht.1
    linarith

private lemma function_upper_of_deriv {T hi : ℝ} (hT : 0 ≤ T) (f f' : ℝ → ℝ)
    (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (f' t) (Icc 0 T) t)
    (hhi : ∀ t ∈ Icc 0 T, f' t ≤ hi) :
    ∀ t ∈ Icc 0 T, f t ≤ f 0 + hi * t := by
  have hc_hi : ContinuousOn (fun s => hi * s - f s) (Icc 0 T) :=
    (continuousOn_const.mul continuousOn_id).sub hc
  have hm : MonotoneOn (fun s => hi * s - f s) (Icc 0 T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) hc_hi (by
      intro s hs
      have hs' : s ∈ Icc 0 T := interior_subset hs
      have hh := ((hasDerivWithinAt_id s (interior (Icc 0 T))).const_mul hi).sub
        ((hd s hs').mono interior_subset)
      convert hh using 1
      · ext u; rfl
      )
      (fun s hs => by linarith [hhi s (interior_subset hs)])
  intro t ht
  have := hm (show 0 ∈ Icc 0 T by exact ⟨le_rfl, hT⟩) ht ht.1
  linarith

private lemma function_lower_of_deriv {T lo : ℝ} (hT : 0 ≤ T) (f f' : ℝ → ℝ)
    (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (f' t) (Icc 0 T) t)
    (hlo : ∀ t ∈ Icc 0 T, lo ≤ f' t) :
    ∀ t ∈ Icc 0 T, f 0 + lo * t ≤ f t := by
  have hc_lo : ContinuousOn (fun s => f s - lo * s) (Icc 0 T) :=
    hc.sub (continuousOn_const.mul continuousOn_id)
  have hm : MonotoneOn (fun s => f s - lo * s) (Icc 0 T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) hc_lo (by
      intro s hs
      have hs' : s ∈ Icc 0 T := interior_subset hs
      have hh := ((hd s hs').mono interior_subset).sub
        ((hasDerivWithinAt_id s (interior (Icc 0 T))).const_mul lo)
      convert hh using 1
      · ext u; rfl
      )
      (fun s hs => by linarith [hlo s (interior_subset hs)])
  intro t ht
  have := hm (show 0 ∈ Icc 0 T by exact ⟨le_rfl, hT⟩) ht ht.1
  linarith

/-- Every solution of the mode ODE with positive risk has nonnegative coordinates. -/
private lemma dyn_ode_nonneg {m n : ℕ} {C : Covariances m n} (p : DynParams)
    (S : SpectralData C) {B : ℕ} (c : DynCoeff p S B) (e0 : Fin m → Fin n → ℝ)
    (T : ℝ) (hT : 0 ≤ T) (e : ℝ → Fin m → Fin n → ℝ)
    (he0 : ∀ i j, 0 ≤ e0 i j)
    (he : IsDynOde p.h (B : ℝ) S.μ S.lam c.d c.v T e0 e)
    (hR : ∀ t ∈ Icc 0 T, 0 < odeRisk S.μ S.lam (B : ℝ) (e t)) :
    ∀ t ∈ Icc 0 T, ∀ i j, 0 ≤ e t i j := by
  have he_cont : ContinuousOn e (Icc 0 T) :=
    fun t ht => (he.2 t ht).continuousWithinAt
  have hR_cont : ContinuousOn
      (fun t => odeRisk S.μ S.lam (B : ℝ) (e t)) (Icc 0 T) := by
    unfold odeRisk
    fun_prop
  intro t ht i j
  let a : ℝ → ℝ := fun s =>
    2 * p.h * c.d (S.μ i, S.lam j) /
      Real.sqrt (odeRisk S.μ S.lam (B : ℝ) (e s))
  have ha : ContinuousOn a (Icc 0 T) := by
    apply ContinuousOn.div continuousOn_const hR_cont.sqrt
    intro s hs
    exact (Real.sqrt_pos.2 (hR s hs)).ne'
  refine linear_ode_nonneg (b := p.h ^ 2 * (B : ℝ) * c.v i j)
    hT a (fun s => e s i j) ha ?_ ?_ ?_ t ht
  · rw [he.1]
    exact he0 i j
  · exact mul_nonneg (mul_nonneg (sq_nonneg p.h) (Nat.cast_nonneg B)) (c.v_nonneg i j)
  · intro s hs
    have hv := (he.2 s hs).hasFDerivWithinAt
    have hi := hasFDerivWithinAt_pi'.mp hv i
    have hij := hasFDerivWithinAt_pi'.mp hi j
    have hij' := hij.hasDerivWithinAt
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hij'
    convert hij' using 1
    unfold odeRHS a
    ring

private lemma prop_app_dyn_ode_i_nonneg {m n : ℕ} {C : Covariances m n}
    (p : DynParams) (S : SpectralData C) {B : ℕ} (c : DynCoeff p S B) (Δ0 : Mat m n) :
    ∀ e : ℝ → Fin m → Fin n → ℝ, def_app_dyn_ode p S c Δ0 (Tstar p) e →
      ∀ τ ∈ Icc 0 (Tstar p), ∀ i j, 0 ≤ e τ i j / (B : ℝ) ^ 2 := by
  intro e he τ hτ i j
  by_cases hB : B = 0
  · simp [hB]
  · have hcoord : 0 ≤ e τ i j := dyn_ode_nonneg p S c
      (odeInit (B : ℝ) S Δ0) (Tstar p) (Tstar_nonneg' p) e
      (fun i j => mul_nonneg (sq_nonneg _) (sq_nonneg _)) he.1 he.2 τ hτ i j
    exact div_nonneg hcoord (sq_nonneg _)

/-- The mode vector field is continuously differentiable wherever its risk is positive. -/
private lemma odeRHS_contDiffOn_pos {m n : ℕ} (h B : ℝ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (d : ℝ × ℝ → ℝ) (v : Fin m → Fin n → ℝ) :
    ContDiffOn ℝ 1 (odeRHS h B μ lam d v) {e | 0 < odeRisk μ lam B e} := by
  let R : (Fin m → Fin n → ℝ) → ℝ := odeRisk μ lam B
  have hR : ContDiff ℝ 1 R := by
    change ContDiff ℝ 1
      (fun e : Fin m → Fin n → ℝ =>
        (1 / 2) * ∑ i, ∑ j, μ i * lam j * e i j / B ^ 2)
    fun_prop
  have hsqrt : ContDiffOn ℝ 1 (fun e => Real.sqrt (R e)) {e | 0 < R e} :=
    hR.contDiffOn.sqrt (fun e he => ne_of_gt he)
  have hsqrt_ne : ∀ e ∈ {e | 0 < R e}, Real.sqrt (R e) ≠ 0 :=
    fun e he => (Real.sqrt_pos.2 he).ne'
  unfold odeRHS
  apply contDiffOn_pi'
  intro i
  apply contDiffOn_pi'
  intro j
  change ContDiffOn ℝ 1
    (fun e => -(2 * h * d (μ i, lam j)) / Real.sqrt (R e) * e i j + h ^ 2 * B * v i j)
    {e | 0 < R e}
  exact ((contDiffOn_const.div hsqrt hsqrt_ne).mul (by fun_prop)).add contDiffOn_const

/-- Positive-risk solutions of the mode equation with the same initial value are unique. -/
private lemma dyn_ode_unique {m n : ℕ} (h B : ℝ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (d : ℝ × ℝ → ℝ) (v : Fin m → Fin n → ℝ)
    (T : ℝ) (hT : 0 ≤ T) (e0 : Fin m → Fin n → ℝ)
    (e e' : ℝ → Fin m → Fin n → ℝ)
    (he : IsDynOde h B μ lam d v T e0 e) (he' : IsDynOde h B μ lam d v T e0 e')
    (hRe : ∀ t ∈ Icc 0 T, 0 < odeRisk μ lam B (e t))
    (hRe' : ∀ t ∈ Icc 0 T, 0 < odeRisk μ lam B (e' t)) :
    EqOn e e' (Icc 0 T) := by
  let R : (Fin m → Fin n → ℝ) → ℝ := odeRisk μ lam B
  have hR : Continuous R := by
    change Continuous
      (fun x : Fin m → Fin n → ℝ =>
        (1 / 2) * ∑ i, ∑ j, μ i * lam j * x i j / B ^ 2)
    fun_prop
  have hRlin : IsLinearMap ℝ R := by
    constructor
    · intro x y
      change (1 / 2) * ∑ i, ∑ j, μ i * lam j * (x i j + y i j) / B ^ 2 =
        (1 / 2) * ∑ i, ∑ j, μ i * lam j * x i j / B ^ 2 +
          (1 / 2) * ∑ i, ∑ j, μ i * lam j * y i j / B ^ 2
      simp_rw [mul_add, add_div, Finset.sum_add_distrib]
      ring
    · intro a x
      change (1 / 2) * ∑ i, ∑ j, μ i * lam j * (a * x i j) / B ^ 2 =
        a * ((1 / 2) * ∑ i, ∑ j, μ i * lam j * x i j / B ^ 2)
      simp_rw [show ∀ i j, μ i * lam j * (a * x i j) / B ^ 2 =
        a * (μ i * lam j * x i j / B ^ 2) by intros; ring,
        ← Finset.mul_sum]
      ring
  have he_cont : ContinuousOn e (Icc 0 T) :=
    fun t ht => (he.2 t ht).continuousWithinAt
  have he'_cont : ContinuousOn e' (Icc 0 T) :=
    fun t ht => (he'.2 t ht).continuousWithinAt
  have hRe_cont : ContinuousOn (fun t => R (e t)) (Icc 0 T) :=
    hR.comp_continuousOn he_cont
  have hRe'_cont : ContinuousOn (fun t => R (e' t)) (Icc 0 T) :=
    hR.comp_continuousOn he'_cont
  obtain ⟨te, hte, hmRe⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT) hRe_cont
  obtain ⟨te', hte', hmRe'⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT) hRe'_cont
  obtain ⟨ue, hue, hmue⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 hT) (continuous_norm.comp_continuousOn he_cont)
  obtain ⟨ue', hue', hmue'⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 hT) (continuous_norm.comp_continuousOn he'_cont)
  let δ := min (R (e te)) (R (e' te'))
  let M := max ‖e ue‖ ‖e' ue'‖
  let s : Set (Fin m → Fin n → ℝ) := Metric.closedBall 0 M ∩ {x | δ ≤ R x}
  have hδ : 0 < δ := lt_min (hRe te hte) (hRe' te' hte')
  have hsconv : Convex ℝ s := by
    dsimp only [s]
    exact convex_closedBall 0 M |>.inter (convex_halfSpace_ge hRlin δ)
  have hscompact : IsCompact s := by
    dsimp only [s]
    exact (isCompact_closedBall 0 M).inter_right (isClosed_le continuous_const hR)
  have hspos : s ⊆ {x | 0 < odeRisk μ lam B x} := by
    intro x hx
    exact hδ.trans_le hx.2
  obtain ⟨K, hLip⟩ :=
    ((odeRHS_contDiffOn_pos h B μ lam d v).mono hspos).exists_lipschitzOnWith
      one_ne_zero hsconv hscompact
  apply ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => odeRHS h B μ lam d v) (s := fun _ => s) (K := K)
  · intro t ht
    exact hLip
  · exact he_cont
  · intro t ht
    exact (he.2 t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff]
      exact (hmue (mem_Icc_of_Ico ht)).trans (le_max_left _ _)
    · exact (min_le_left _ _).trans
        (show R (e te) ≤ R (e t) from hmRe (mem_Icc_of_Ico ht))
  · exact he'_cont
  · intro t ht
    exact (he'.2 t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff]
      exact (hmue' (mem_Icc_of_Ico ht)).trans (le_max_right _ _)
    · exact (min_le_right _ _).trans
        (show R (e' te') ≤ R (e' t) from hmRe' (mem_Icc_of_Ico ht))
  · rw [he.1, he'.1]

/-- `prop:app-dyn-ode`, snapshot `cr-2026-10-23`. Part (i): existence and uniqueness of the solution on `[0,T⋆]` (uniqueness on the interval, since the equations do not constrain `e` off it), and `𝒬_ij ≥ 0`. Fixed dimension, hypotheses as in ll. 263-265.

Source (`section.tex`, whole environment):
```latex
\begin{proposition}[Well-posedness]\label{prop:app-dyn-ode}
At a fixed dimension, let $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$ and
$\max(\Nin,\Nout)\le\gamma_\star B$, and let $\Delta_0$ satisfy
$\norm{\Delta_0}_\F^2\le E_\star$ and $r_0\le\cR(\Delta_0)\le r_1$. Then:
\begin{enumerate}[label=(\roman*)]
\item the system \cref{eqn:app-dyn-ode} has a unique solution on
$[0,T_\star]$, and $\fQ_{ij}(\macrotime)\ge0$ for all $i,j$ and $\macrotime\le T_\star$;
\item for $\macrotime\le T_\star$, $\abs{\chi^{\mathrm{ode}}(\macrotime)(\mathbb K)-\norm{\Delta_0}_\F^2}\le C_E\macrotime$
and $\abs{\fRisk(\macrotime)-\cR(\Delta_0)}\le C_{\cR}\macrotime$; in particular
$\chi^{\mathrm{ode}}(\macrotime)\in\mathfrak M$;
\item $\chi^{\mathrm{ode}}$ satisfies \cref{eqn:app-dyn-ode-measure} on $[0,T_\star]$.
\end{enumerate}
\end{proposition}
```
-/
theorem prop_app_dyn_ode_i {m n : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    {B : ℕ} (c : DynCoeff p S B) (Δ0 : Mat m n)
    (hSout : opNorm C.Sout ≤ p.CSig) (hSin : opNorm C.Sin ≤ p.CSig)
    (hdim : ((max m n : ℕ) : ℝ) ≤ p.γstar * (B : ℝ))
    (hE : fro Δ0 ^ 2 ≤ p.Estar) (hR0 : p.r0 ≤ riskSigma C Δ0) (hR1 : riskSigma C Δ0 ≤ p.r1) :
    (∃ e : ℝ → Fin m → Fin n → ℝ, def_app_dyn_ode p S c Δ0 (Tstar p) e) ∧
    (∀ e e' : ℝ → Fin m → Fin n → ℝ, def_app_dyn_ode p S c Δ0 (Tstar p) e →
      def_app_dyn_ode p S c Δ0 (Tstar p) e' → EqOn e e' (Icc 0 (Tstar p))) ∧
    (∀ e : ℝ → Fin m → Fin n → ℝ, def_app_dyn_ode p S c Δ0 (Tstar p) e →
      ∀ τ ∈ Icc 0 (Tstar p), ∀ i j, 0 ≤ e τ i j / (B : ℝ) ^ 2) := by
  refine ⟨?_, ?_, prop_app_dyn_ode_i_nonneg p S c Δ0⟩
  · have hB : 0 < B := batch_pos_of_initial_risk p S Δ0 hdim hR0
    have hBc : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
    let δ : ℝ := p.r0 / 2
    have hδ : 0 < δ := by dsimp only [δ]; linarith [p.hr0]
    let F : (Fin m → Fin n → ℝ) → (Fin m → Fin n → ℝ) := fun q i j =>
      -(2 * p.h * c.d (S.μ i, S.lam j)) /
          Real.sqrt (max δ (odeRisk S.μ S.lam (B : ℝ) q)) * q i j +
        p.h ^ 2 * (B : ℝ) * c.v i j
    let A : ℝ := 2 * p.h * dMax p / Real.sqrt δ
    let D : ℝ := ‖(fun i j => p.h ^ 2 * (B : ℝ) * c.v i j)‖
    let e0 := odeInit (B : ℝ) S Δ0
    have hA : 0 ≤ A := by
      dsimp only [A]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hh.le) (dMax_nonneg' p))
        (Real.sqrt_nonneg _)
    have hD : 0 ≤ D := norm_nonneg _
    have hACE : A ≤ CE p := by
      have hx : A * 1 ≤ A * (p.Estar + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [p.hE]) hA
      calc
        A = A * 1 := by ring
        _ ≤ A * (p.Estar + 1) := hx
        _ ≤ A * (p.Estar + 1) + p.h ^ 2 * mZeta p :=
          le_add_of_nonneg_right (mul_nonneg (sq_nonneg p.h) (mZeta_nonneg' p))
        _ = CE p := by dsimp only [A, δ, CE]; ring
    have hAT : A * Tstar p ≤ 1 / 8 := Tstar_mul_le_eighth p hA
      (hACE.trans (by linarith [CR_nonneg' p]))
    let base : ℝ := A * ‖e0‖ + D
    have hbase : 0 ≤ base := add_nonneg (mul_nonneg hA (norm_nonneg _)) hD
    let ar : ℝ := 2 * Tstar p * base
    have har : 0 ≤ ar := mul_nonneg (mul_nonneg (by norm_num) (Tstar_nonneg' p)) hbase
    let lr : ℝ := A * (‖e0‖ + ar) + D
    have hlr : 0 ≤ lr := add_nonneg (mul_nonneg hA (add_nonneg (norm_nonneg _) har)) hD
    have hFloc : LocallyLipschitz F := by
      dsimp only [F]
      exact truncated_odeRHS_locallyLipschitz p.h (B : ℝ) S.μ S.lam c.d c.v hδ
    have hFbound : ∀ q ∈ Metric.closedBall e0 ar, ‖F q‖ ≤ lr := by
      intro q hq
      have hdist : dist q e0 ≤ ar := by simpa only [Metric.mem_closedBall] using hq
      have hqnorm : ‖q‖ ≤ ‖e0‖ + ar := by
        calc
          ‖q‖ ≤ ‖e0‖ + ‖q - e0‖ := by linarith [norm_sub_norm_le q e0]
          _ ≤ ‖e0‖ + ar := by
            gcongr
            simpa [dist_eq_norm] using hdist
      calc
        ‖F q‖ ≤ A * ‖q‖ + D := truncated_odeRHS_bound p S c hSout hSin hδ q
        _ ≤ A * (‖e0‖ + ar) + D := by gcongr
        _ = lr := rfl
    have hLT : lr * Tstar p ≤ ar := by
      dsimp only [lr, ar, base]
      have hT0 := Tstar_nonneg' p
      have hAT' : A * Tstar p ≤ 1 / 2 := hAT.trans (by norm_num)
      nlinarith [mul_nonneg hbase hT0, mul_nonneg hA hT0]
    obtain ⟨e, he0, he⟩ := exists_ode_on_Icc_of_locallyLipschitz_bounded F e0
      (Tstar p) (Tstar_nonneg' p) ⟨ar, har⟩ ⟨lr, hlr⟩ hFloc hFbound hLT
    have henonneg : ∀ t ∈ Icc 0 (Tstar p), ∀ i j, 0 ≤ e t i j :=
      truncated_ode_nonneg p S c e0 (Tstar p) (Tstar_nonneg' p) hδ e
        (fun i j => mul_nonneg (sq_nonneg _) (sq_nonneg _)) he0 (by
          intro t ht
          simpa only [F] using he t ht)
    let R : ℝ → ℝ := fun t => odeRisk S.μ S.lam (B : ℝ) (e t)
    let RF : ℝ → ℝ := fun t => odeRisk S.μ S.lam (B : ℝ) (F (e t))
    have hRcont : ContinuousOn R (Icc 0 (Tstar p)) := by
      dsimp only [R, odeRisk]
      have hecont : ContinuousOn e (Icc 0 (Tstar p)) := fun t ht => (he t ht).continuousWithinAt
      fun_prop
    have hRder : ∀ t ∈ Icc 0 (Tstar p),
        HasDerivWithinAt R (RF t) (Icc 0 (Tstar p)) t := by
      intro t ht
      exact odeRisk_hasDerivWithinAt (B : ℝ) S.μ S.lam e (F (e t)) _ _ (he t ht)
    have hRinit : R 0 = riskSigma C Δ0 := by
      dsimp only [R, e0] at he0 ⊢
      rw [he0]
      unfold odeRisk odeInit
      have hterm : ∀ i j, S.μ i * S.lam j * ((B : ℝ) ^ 2 * modeQ S Δ0 i j) /
          (B : ℝ) ^ 2 = S.μ i * S.lam j * modeQ S Δ0 i j := by
        intro i j
        field_simp
      simp_rw [hterm]
      exact normalized_initial_risk S Δ0
    let KF : ℝ := odeRisk S.μ S.lam (B : ℝ)
      (fun i j => p.h ^ 2 * (B : ℝ) * c.v i j)
    have hKF := forcing_risk_bounds p S c hSout hSin hB
    have hsplit (t : ℝ) : RF t =
        odeRisk S.μ S.lam (B : ℝ)
          (fun i j => -(2 * p.h * c.d (S.μ i, S.lam j)) /
            Real.sqrt (max δ (R t)) * e t i j) + KF := by
      dsimp only [RF, F, R, KF, odeRisk]
      simp_rw [mul_add, add_div, Finset.sum_add_distrib]
      ring
    have hRFupper : ∀ t ∈ Icc 0 (Tstar p), RF t ≤ KF := by
      intro t ht
      rw [hsplit]
      linarith [drift_risk_nonpos p S c hSout hSin hδ (e t) (henonneg t ht)]
    have hRupper0 := function_upper_of_deriv (Tstar_nonneg' p) R RF hRcont hRder hRFupper
    have hKFCR : KF ≤ CR p := by
      have hdrift0 : 0 ≤ 2 * p.h * dMax p * Real.sqrt (p.r1 + 1) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hh.le) (dMax_nonneg' p))
          (Real.sqrt_nonneg (p.r1 + 1))
      unfold CR
      exact hKF.2.trans (by linarith)
    have hKFT : KF * Tstar p ≤ 1 / 8 :=
      (mul_le_mul_of_nonneg_right hKFCR (Tstar_nonneg' p)).trans
        (Tstar_mul_le_eighth p (CR_nonneg' p) (by linarith [CE_nonneg' p]))
    have hRupper : ∀ t ∈ Icc 0 (Tstar p), R t ≤ p.r1 + 1 := by
      intro t ht
      have hk : KF * t ≤ 1 / 8 :=
        (mul_le_mul_of_nonneg_left ht.2 hKF.1).trans hKFT
      rw [hRinit] at hRupper0
      linarith [hRupper0 t ht, hR1]
    have hRFlower : ∀ t ∈ Icc 0 (Tstar p), -CR p ≤ RF t := by
      intro t ht
      rw [hsplit]
      have hd := (drift_risk_bounds p S c hSout hSin hB hδ (e t)
        (henonneg t ht) (hRupper t ht)).1
      unfold CR
      linarith [hKF.1]
    have hRlower0 := function_lower_of_deriv (Tstar_nonneg' p) R RF hRcont hRder hRFlower
    have hCRT : CR p * Tstar p ≤ min p.r0 1 / 8 :=
      Tstar_mul_le_min_eighth p (CR_nonneg' p) (by linarith [CE_nonneg' p])
    have hRlower : ∀ t ∈ Icc 0 (Tstar p), δ < R t := by
      intro t ht
      have hct : CR p * t ≤ min p.r0 1 / 8 :=
        (mul_le_mul_of_nonneg_left ht.2 (CR_nonneg' p)).trans hCRT
      have hm : min p.r0 1 / 8 ≤ p.r0 / 8 :=
        div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      rw [hRinit] at hRlower0
      dsimp only [δ]
      linarith [hRlower0 t ht, hR0, p.hr0]
    refine ⟨e, ?_, fun t ht => (hδ.trans (hRlower t ht)).trans_le le_rfl⟩
    refine ⟨he0, ?_⟩
    intro t ht
    have hmax : max δ (R t) = R t := max_eq_right (hRlower t ht).le
    convert he t ht using 1
    funext i j
    simp only [F, R, hmax, odeRHS]
  · intro e e' he he'
    exact dyn_ode_unique p.h (B : ℝ) S.μ S.lam c.d c.v (Tstar p) (Tstar_nonneg' p)
      (odeInit (B : ℝ) S Δ0) e e' he.1 he'.1 he.2 he'.2

private lemma atom_integral {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (q : Fin m → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j) (f : ℝ × ℝ → ℝ) :
    ∫ x, f x ∂(atomMeasure μ lam q) = ∑ i, ∑ j, q i j * f (μ i, lam j) := by
  have hint : ∀ i j, Integrable f (ENNReal.ofReal (q i j) • Measure.dirac (μ i, lam j)) :=
    fun i j => (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  unfold atomMeasure
  rw [integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.2 (fun j _ => hint i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum_measure (fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hq i j), smul_eq_mul]

private lemma riskOf_odeMeasure {m n : ℕ} (B : ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (e : Fin m → Fin n → ℝ) (he : ∀ i j, 0 ≤ e i j / B ^ 2) :
    riskOf (odeMeasure B μ lam e) = odeRisk μ lam B e := by
  unfold riskOf odeMeasure odeRisk
  rw [atom_integral μ lam _ he]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma odeMass_hasDerivWithinAt {m n : ℕ} (B : ℝ)
    (e : ℝ → Fin m → Fin n → ℝ) (F : Fin m → Fin n → ℝ)
    (s : Set ℝ) (t : ℝ) (he : HasDerivWithinAt e F s t) :
    HasDerivWithinAt (fun u => ∑ i, ∑ j, e u i j / B ^ 2)
      (∑ i, ∑ j, F i j / B ^ 2) s t := by
  have hcoord (i : Fin m) (j : Fin n) :
      HasDerivWithinAt (fun u => e u i j) (F i j) s t := by
    have hv := he.hasFDerivWithinAt
    have hi := hasFDerivWithinAt_pi'.mp hv i
    have hij := hasFDerivWithinAt_pi'.mp hi j
    simpa only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
      using hij.hasDerivWithinAt
  have hj (i : Fin m) : HasDerivWithinAt
      (∑ j, fun u => e u i j / B ^ 2) (∑ j, F i j / B ^ 2) s t :=
    HasDerivWithinAt.sum (u := Finset.univ) fun j _ => (hcoord i j).div_const _
  have hi : HasDerivWithinAt
      (∑ i, ∑ j, fun u => e u i j / B ^ 2) (∑ i, ∑ j, F i j / B ^ 2) s t :=
    HasDerivWithinAt.sum (u := Finset.univ) fun i _ => hj i
  convert hi using 1
  funext u
  simp only [Finset.sum_apply]

private lemma atom_mem_specRect {m n : ℕ} {C : Covariances m n} (p : DynParams)
    (S : SpectralData C) (hSout : opNorm C.Sout ≤ p.CSig) (hSin : opNorm C.Sin ≤ p.CSig)
    (i : Fin m) (j : Fin n) : (S.μ i, S.lam j) ∈ specRect p.CSig :=
  ⟨⟨μ_nonneg S i, (le_abs_self _).trans ((abs_mu_le_opNorm S i).trans hSout)⟩,
   ⟨lam_nonneg S j, (le_abs_self _).trans ((abs_lam_le_opNorm S j).trans hSin)⟩⟩

private lemma ode_core {m n : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    {B : ℕ} (c : DynCoeff p S B) (Δ0 : Mat m n)
    (hSout : opNorm C.Sout ≤ p.CSig) (hSin : opNorm C.Sin ≤ p.CSig)
    (hdim : ((max m n : ℕ) : ℝ) ≤ p.γstar * (B : ℝ))
    (hE : fro Δ0 ^ 2 ≤ p.Estar) (hR0 : p.r0 ≤ riskSigma C Δ0) (hR1 : riskSigma C Δ0 ≤ p.r1)
    (e : ℝ → Fin m → Fin n → ℝ) (he : def_app_dyn_ode p S c Δ0 (Tstar p) e) :
    ∀ t ∈ Icc 0 (Tstar p),
      |∑ i, ∑ j, e t i j / (B : ℝ) ^ 2 - fro Δ0 ^ 2| ≤ CE p * t ∧
      |odeRisk S.μ S.lam (B : ℝ) (e t) - riskSigma C Δ0| ≤ CR p * t ∧
      p.r0 / 2 ≤ odeRisk S.μ S.lam (B : ℝ) (e t) ∧
      odeRisk S.μ S.lam (B : ℝ) (e t) ≤ p.r1 + 1 / 2 ∧
      ∑ i, ∑ j, e t i j / (B : ℝ) ^ 2 ≤ p.Estar + 1 := by
  have hB : 0 < B := batch_pos_of_initial_risk p S Δ0 hdim hR0
  have hBc : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hT := Tstar_nonneg' p
  have hpos := he.2
  have hnn : ∀ t ∈ Icc 0 (Tstar p), ∀ i j, 0 ≤ e t i j :=
    dyn_ode_nonneg p S c (odeInit (B : ℝ) S Δ0) (Tstar p) hT e
      (fun i j => mul_nonneg (sq_nonneg _) (sq_nonneg _)) he.1 hpos
  have hecont : ContinuousOn e (Icc 0 (Tstar p)) := fun t ht => (he.1.2 t ht).continuousWithinAt
  -- risk
  let R : ℝ → ℝ := fun t => odeRisk S.μ S.lam (B : ℝ) (e t)
  let F : ℝ → Fin m → Fin n → ℝ := fun t => odeRHS p.h (B : ℝ) S.μ S.lam c.d c.v (e t)
  let RF : ℝ → ℝ := fun t => odeRisk S.μ S.lam (B : ℝ) (F t)
  have hRcont : ContinuousOn R (Icc 0 (Tstar p)) := by
    dsimp only [R, odeRisk]
    fun_prop
  have hRder : ∀ t ∈ Icc 0 (Tstar p), HasDerivWithinAt R (RF t) (Icc 0 (Tstar p)) t :=
    fun t ht => odeRisk_hasDerivWithinAt (B : ℝ) S.μ S.lam e (F t) _ _ (he.1.2 t ht)
  have hRinit : R 0 = riskSigma C Δ0 := by
    dsimp only [R]
    rw [he.1.1]
    unfold odeRisk odeInit
    have hterm : ∀ i j, S.μ i * S.lam j * ((B : ℝ) ^ 2 * modeQ S Δ0 i j) /
        (B : ℝ) ^ 2 = S.μ i * S.lam j * modeQ S Δ0 i j := by
      intro i j
      field_simp
    simp_rw [hterm]
    exact normalized_initial_risk S Δ0
  let KF : ℝ := odeRisk S.μ S.lam (B : ℝ) (fun i j => p.h ^ 2 * (B : ℝ) * c.v i j)
  have hKF := forcing_risk_bounds p S c hSout hSin hB
  have hsplit : ∀ t, RF t =
      odeRisk S.μ S.lam (B : ℝ)
        (fun i j => -(2 * p.h * c.d (S.μ i, S.lam j)) /
          Real.sqrt (max (R t) (R t)) * e t i j) + KF := by
    intro t
    simp only [max_self]
    dsimp only [RF, F, KF, odeRisk, odeRHS, R]
    simp_rw [mul_add, add_div, Finset.sum_add_distrib]
    ring
  have hRFupper : ∀ t ∈ Icc 0 (Tstar p), RF t ≤ KF := by
    intro t ht
    rw [hsplit]
    linarith [drift_risk_nonpos p S c hSout hSin (hpos t ht) (e t) (hnn t ht)]
  have hRupper0 := function_upper_of_deriv hT R RF hRcont hRder hRFupper
  have hKFCR : KF ≤ CR p := by
    have hdrift0 : 0 ≤ 2 * p.h * dMax p * Real.sqrt (p.r1 + 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hh.le) (dMax_nonneg' p))
        (Real.sqrt_nonneg (p.r1 + 1))
    unfold CR
    exact hKF.2.trans (by linarith)
  have hKFT : KF * Tstar p ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right hKFCR hT).trans
      (Tstar_mul_le_eighth p (CR_nonneg' p) (by linarith [CE_nonneg' p]))
  have hRupper : ∀ t ∈ Icc 0 (Tstar p), R t ≤ p.r1 + 1 / 8 := by
    intro t ht
    have hk : KF * t ≤ 1 / 8 := (mul_le_mul_of_nonneg_left ht.2 hKF.1).trans hKFT
    rw [hRinit] at hRupper0
    linarith [hRupper0 t ht, hR1]
  have hRFlower : ∀ t ∈ Icc 0 (Tstar p), -CR p ≤ RF t := by
    intro t ht
    rw [hsplit]
    have hd := (drift_risk_bounds p S c hSout hSin hB (hpos t ht) (e t)
      (hnn t ht) (by linarith [hRupper t ht])).1
    simp only [max_self] at hd ⊢
    unfold CR
    linarith [hKF.1]
  have hRlower0 := function_lower_of_deriv hT R RF hRcont hRder hRFlower
  have hCRT : CR p * Tstar p ≤ min p.r0 1 / 8 :=
    Tstar_mul_le_min_eighth p (CR_nonneg' p) (by linarith [CE_nonneg' p])
  have hct : ∀ t ∈ Icc 0 (Tstar p), CR p * t ≤ min p.r0 1 / 8 := fun t ht =>
    (mul_le_mul_of_nonneg_left ht.2 (CR_nonneg' p)).trans hCRT
  have hm : min p.r0 1 / 8 ≤ p.r0 / 8 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hRlower : ∀ t ∈ Icc 0 (Tstar p), p.r0 / 2 ≤ R t := by
    intro t ht
    rw [hRinit] at hRlower0
    linarith [hRlower0 t ht, hR0, p.hr0, hct t ht]
  -- mass
  let M : ℝ → ℝ := fun t => ∑ i, ∑ j, e t i j / (B : ℝ) ^ 2
  let MF : ℝ → ℝ := fun t => ∑ i, ∑ j, F t i j / (B : ℝ) ^ 2
  have hMcont : ContinuousOn M (Icc 0 (Tstar p)) := by
    dsimp only [M]
    fun_prop
  have hMder : ∀ t ∈ Icc 0 (Tstar p), HasDerivWithinAt M (MF t) (Icc 0 (Tstar p)) t :=
    fun t ht => odeMass_hasDerivWithinAt (B : ℝ) e (F t) _ _ (he.1.2 t ht)
  have hMinit : M 0 = fro Δ0 ^ 2 := by
    dsimp only [M]
    rw [he.1.1]
    unfold odeInit
    have hterm : ∀ i j, (B : ℝ) ^ 2 * modeQ S Δ0 i j / (B : ℝ) ^ 2 = modeQ S Δ0 i j := by
      intro i j
      field_simp
    simp_rw [hterm]
    exact modeQ_sum_eq_fro_sq S Δ0
  let Fm : ℝ := ∑ i, ∑ j, p.h ^ 2 * (B : ℝ) * c.v i j / (B : ℝ) ^ 2
  have hFm : 0 ≤ Fm ∧ Fm ≤ p.h ^ 2 * mZeta p := by
    have heq : Fm = p.h ^ 2 * ∑ i, ∑ j, c.v i j / (B : ℝ) := by
      dsimp only [Fm]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    rw [heq]
    refine ⟨mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg
      fun j _ => div_nonneg (c.v_nonneg i j) hBc.le), ?_⟩
    exact mul_le_mul_of_nonneg_left (forcing_mass_le p S c hB) (sq_nonneg _)
  let Dm : ℝ → ℝ := fun t => ∑ i, ∑ j,
    -(2 * p.h * c.d (S.μ i, S.lam j)) / Real.sqrt (R t) * e t i j / (B : ℝ) ^ 2
  have hMsplit : ∀ t, MF t = Dm t + Fm := by
    intro t
    dsimp only [MF, F, Dm, Fm, odeRHS, R]
    simp_rw [add_div, Finset.sum_add_distrib]
  have hDm0 : ∀ t ∈ Icc 0 (Tstar p), Dm t ≤ 0 := by
    intro t ht
    apply Finset.sum_nonpos; intro i _
    apply Finset.sum_nonpos; intro j _
    have hd0 := c.d_nonneg _ (atom_mem_specRect p S hSout hSin i j)
    have hs : 0 < Real.sqrt (R t) := Real.sqrt_pos.2 (hpos t ht)
    have : 0 ≤ 2 * p.h * c.d (S.μ i, S.lam j) / Real.sqrt (R t) * e t i j / (B : ℝ) ^ 2 :=
      div_nonneg (mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hh.le) hd0)
        hs.le) (hnn t ht i j)) (sq_nonneg _)
    have h2 : -(2 * p.h * c.d (S.μ i, S.lam j)) / Real.sqrt (R t) * e t i j / (B : ℝ) ^ 2 =
        -(2 * p.h * c.d (S.μ i, S.lam j) / Real.sqrt (R t) * e t i j / (B : ℝ) ^ 2) := by ring
    rw [h2]; linarith
  have hMFupper : ∀ t ∈ Icc 0 (Tstar p), MF t ≤ CE p := by
    intro t ht
    rw [hMsplit]
    have := hDm0 t ht
    unfold CE
    have : 0 ≤ 2 * p.h * dMax p * (p.Estar + 1) / Real.sqrt (p.r0 / 2) :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hh.le) (dMax_nonneg' p))
        (by linarith [p.hE])) (Real.sqrt_nonneg _)
    linarith [hFm.2]
  have hMupper0 := function_upper_of_deriv hT M MF hMcont hMder hMFupper
  have hCET : CE p * Tstar p ≤ 1 / 8 :=
    Tstar_mul_le_eighth p (CE_nonneg' p) (by linarith [CR_nonneg' p])
  have hMupper : ∀ t ∈ Icc 0 (Tstar p), M t ≤ p.Estar + 1 := by
    intro t ht
    have hk : CE p * t ≤ 1 / 8 := (mul_le_mul_of_nonneg_left ht.2 (CE_nonneg' p)).trans hCET
    rw [hMinit] at hMupper0
    linarith [hMupper0 t ht]
  have hMFlower : ∀ t ∈ Icc 0 (Tstar p), -CE p ≤ MF t := by
    intro t ht
    rw [hMsplit]
    have hs : 0 < Real.sqrt (R t) := Real.sqrt_pos.2 (hpos t ht)
    have hs2 : Real.sqrt (p.r0 / 2) ≤ Real.sqrt (R t) := Real.sqrt_le_sqrt (hRlower t ht)
    have hs3 : 0 < Real.sqrt (p.r0 / 2) := Real.sqrt_pos.2 (by linarith [p.hr0])
    set A1 : ℝ := 2 * p.h * dMax p / Real.sqrt (p.r0 / 2) with hA1
    have hA10 : 0 ≤ A1 := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hh.le)
      (dMax_nonneg' p)) hs3.le
    have hterm : ∀ i j, -(A1 * (e t i j / (B : ℝ) ^ 2)) ≤
        -(2 * p.h * c.d (S.μ i, S.lam j)) / Real.sqrt (R t) * e t i j / (B : ℝ) ^ 2 := by
      intro i j
      have hd0 := c.d_nonneg _ (atom_mem_specRect p S hSout hSin i j)
      have hd1 := c.d_le _ (atom_mem_specRect p S hSout hSin i j)
      have hcoef : 2 * p.h * c.d (S.μ i, S.lam j) / Real.sqrt (R t) ≤ A1 := by
        rw [hA1]
        calc 2 * p.h * c.d (S.μ i, S.lam j) / Real.sqrt (R t)
            ≤ 2 * p.h * c.d (S.μ i, S.lam j) / Real.sqrt (p.r0 / 2) :=
              div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (by norm_num) p.hh.le) hd0)
                hs3 hs2
          _ ≤ 2 * p.h * dMax p / Real.sqrt (p.r0 / 2) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd1
                (mul_nonneg (by norm_num) p.hh.le)) hs3.le
      have he0 : 0 ≤ e t i j / (B : ℝ) ^ 2 := div_nonneg (hnn t ht i j) (sq_nonneg _)
      have h3 := mul_le_mul_of_nonneg_right hcoef he0
      have h4 : -(2 * p.h * c.d (S.μ i, S.lam j)) / Real.sqrt (R t) * e t i j / (B : ℝ) ^ 2 =
          -(2 * p.h * c.d (S.μ i, S.lam j) / Real.sqrt (R t) * (e t i j / (B : ℝ) ^ 2)) := by
        ring
      rw [h4]; linarith
    have hsum : -(A1 * M t) ≤ Dm t := by
      dsimp only [M, Dm]
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun j _ => hterm i j
    have hMt := hMupper t ht
    have hMt0 : 0 ≤ M t := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      div_nonneg (hnn t ht i j) (sq_nonneg _)
    have h5 : A1 * M t ≤ A1 * (p.Estar + 1) := mul_le_mul_of_nonneg_left hMt hA10
    have h6 : A1 * (p.Estar + 1) = 2 * p.h * dMax p * (p.Estar + 1) / Real.sqrt (p.r0 / 2) := by
      rw [hA1]; ring
    unfold CE
    linarith [hFm.1, hFm.2, mZeta_nonneg' p, sq_nonneg p.h, mul_nonneg (sq_nonneg p.h) (mZeta_nonneg' p)]
  have hMlower0 := function_lower_of_deriv hT M MF hMcont hMder hMFlower
  intro t ht
  have hCEt : CE p * t ≤ 1 / 8 := (mul_le_mul_of_nonneg_left ht.2 (CE_nonneg' p)).trans hCET
  have hKt : KF * t ≤ CR p * t := mul_le_mul_of_nonneg_right hKFCR ht.1
  rw [hMinit] at hMupper0 hMlower0
  rw [hRinit] at hRupper0 hRlower0
  have hct' := hct t ht
  refine ⟨?_, ?_, hRlower t ht, ?_, hMupper t ht⟩
  · change |M t - fro Δ0 ^ 2| ≤ CE p * t
    rw [abs_le]
    have h1 := hMupper0 t ht
    have h2 := hMlower0 t ht
    constructor <;> linarith
  · change |R t - riskSigma C Δ0| ≤ CR p * t
    rw [abs_le]
    have h1 := hRupper0 t ht
    have h2 := hRlower0 t ht
    constructor <;> linarith
  · linarith [hRupper t ht, hR1]
private lemma atom_compl_specRect {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (q : Fin m → Fin n → ℝ) (Cs : ℝ) (hmem : ∀ i j, (μ i, lam j) ∈ specRect Cs) :
    atomMeasure μ lam q (specRect Cs)ᶜ = 0 := by
  have hc : MeasurableSet (specRect Cs)ᶜ :=
    (measurableSet_Icc.prod measurableSet_Icc).compl
  unfold atomMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [Measure.dirac_apply' _ hc, Set.indicator_of_notMem (by
    intro h
    exact h (hmem i j))]
  simp

private lemma odeMeasure_real_specRect {m n : ℕ} (B : ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (e : Fin m → Fin n → ℝ) (Cs : ℝ) (hmem : ∀ i j, (μ i, lam j) ∈ specRect Cs) :
    (odeMeasure B μ lam e).real (specRect Cs) = (odeMeasure B μ lam e).real univ := by
  have hs : MeasurableSet (specRect Cs) := measurableSet_Icc.prod measurableSet_Icc
  have h0 := atom_compl_specRect μ lam (fun i j => e i j / B ^ 2) Cs hmem
  have h1 := measure_add_measure_compl (μ := odeMeasure B μ lam e) hs
  unfold odeMeasure at h0 h1 ⊢
  rw [h0, add_zero] at h1
  rw [Measure.real_def, Measure.real_def, h1]

private lemma odeWeighted_hasDerivWithinAt {m n : ℕ} (B : ℝ) (w : Fin m → Fin n → ℝ)
    (e : ℝ → Fin m → Fin n → ℝ) (F : Fin m → Fin n → ℝ)
    (s : Set ℝ) (t : ℝ) (he : HasDerivWithinAt e F s t) :
    HasDerivWithinAt (fun u => ∑ i, ∑ j, e u i j / B ^ 2 * w i j)
      (∑ i, ∑ j, F i j / B ^ 2 * w i j) s t := by
  have hcoord (i : Fin m) (j : Fin n) :
      HasDerivWithinAt (fun u => e u i j) (F i j) s t := by
    have hv := he.hasFDerivWithinAt
    have hi := hasFDerivWithinAt_pi'.mp hv i
    have hij := hasFDerivWithinAt_pi'.mp hi j
    simpa only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
      using hij.hasDerivWithinAt
  have hj (i : Fin m) : HasDerivWithinAt
      (∑ j, fun u => e u i j / B ^ 2 * w i j) (∑ j, F i j / B ^ 2 * w i j) s t :=
    HasDerivWithinAt.sum (u := Finset.univ) fun j _ =>
      ((hcoord i j).div_const _).mul_const _
  have hi : HasDerivWithinAt
      (∑ i, ∑ j, fun u => e u i j / B ^ 2 * w i j) (∑ i, ∑ j, F i j / B ^ 2 * w i j) s t :=
    HasDerivWithinAt.sum (u := Finset.univ) fun i _ => hj i
  convert hi using 1
  funext u
  simp only [Finset.sum_apply]


/-- `prop:app-dyn-ode`, snapshot `cr-2026-10-23`. Part (ii): `|χ^ode(τ)(K) − ‖Δ₀‖²_F| ≤ C_E τ`, `|𝓡(τ) − 𝓡(Δ₀)| ≤ C_𝓡 τ`, and `χ^ode(τ) ∈ 𝔐`. Fixed dimension.

Source (`section.tex`, whole environment):
```latex
\begin{proposition}[Well-posedness]\label{prop:app-dyn-ode}
At a fixed dimension, let $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$ and
$\max(\Nin,\Nout)\le\gamma_\star B$, and let $\Delta_0$ satisfy
$\norm{\Delta_0}_\F^2\le E_\star$ and $r_0\le\cR(\Delta_0)\le r_1$. Then:
\begin{enumerate}[label=(\roman*)]
\item the system \cref{eqn:app-dyn-ode} has a unique solution on
$[0,T_\star]$, and $\fQ_{ij}(\macrotime)\ge0$ for all $i,j$ and $\macrotime\le T_\star$;
\item for $\macrotime\le T_\star$, $\abs{\chi^{\mathrm{ode}}(\macrotime)(\mathbb K)-\norm{\Delta_0}_\F^2}\le C_E\macrotime$
and $\abs{\fRisk(\macrotime)-\cR(\Delta_0)}\le C_{\cR}\macrotime$; in particular
$\chi^{\mathrm{ode}}(\macrotime)\in\mathfrak M$;
\item $\chi^{\mathrm{ode}}$ satisfies \cref{eqn:app-dyn-ode-measure} on $[0,T_\star]$.
\end{enumerate}
\end{proposition}
```
-/
theorem prop_app_dyn_ode_ii {m n : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    {B : ℕ} (c : DynCoeff p S B) (Δ0 : Mat m n)
    (hSout : opNorm C.Sout ≤ p.CSig) (hSin : opNorm C.Sin ≤ p.CSig)
    (hdim : ((max m n : ℕ) : ℝ) ≤ p.γstar * (B : ℝ))
    (hE : fro Δ0 ^ 2 ≤ p.Estar) (hR0 : p.r0 ≤ riskSigma C Δ0) (hR1 : riskSigma C Δ0 ≤ p.r1) :
    ∀ e : ℝ → Fin m → Fin n → ℝ, def_app_dyn_ode p S c Δ0 (Tstar p) e →
      ∀ τ ∈ Icc 0 (Tstar p),
        |(odeMeasure (B : ℝ) S.μ S.lam (e τ)).real (specRect p.CSig) - fro Δ0 ^ 2| ≤ CE p * τ ∧
        |odeRisk S.μ S.lam (B : ℝ) (e τ) - riskSigma C Δ0| ≤ CR p * τ ∧
        odeMeasure (B : ℝ) S.μ S.lam (e τ) ∈ admMeasures p := by
  intro e he τ hτ
  obtain ⟨h1, h2, h3, h4, h5⟩ := ode_core p S c Δ0 hSout hSin hdim hE hR0 hR1 e he τ hτ
  have hnn : ∀ i j, 0 ≤ e τ i j / (B : ℝ) ^ 2 := prop_app_dyn_ode_i_nonneg p S c Δ0 e he τ hτ
  have hmem : ∀ i j, (S.μ i, S.lam j) ∈ specRect p.CSig := atom_mem_specRect p S hSout hSin
  have hmass : (odeMeasure (B : ℝ) S.μ S.lam (e τ)).real univ =
      ∑ i, ∑ j, e τ i j / (B : ℝ) ^ 2 :=
    atom_mass_nonneg S.μ S.lam _ hnn
  have hrisk := riskOf_odeMeasure (B : ℝ) S.μ S.lam (e τ) hnn
  refine ⟨?_, h2, ?_⟩
  · rw [odeMeasure_real_specRect (B : ℝ) S.μ S.lam (e τ) p.CSig hmem, hmass]
    exact h1
  · refine ⟨atom_isFinite _ _ _, atom_compl_specRect _ _ _ _ hmem, ?_, ?_, ?_⟩
    · rw [hmass]; exact h5
    · rw [hrisk]; exact h3
    · rw [hrisk]; exact h4

/-- `prop:app-dyn-ode`, snapshot `cr-2026-10-23`. Part (iii): the measure form `eqn:app-dyn-ode-measure`, tested against bounded measurable `φ` (weak reading) with interval integrability of the integrand. Fixed dimension.

Source (`section.tex`, whole environment):
```latex
\begin{proposition}[Well-posedness]\label{prop:app-dyn-ode}
At a fixed dimension, let $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$ and
$\max(\Nin,\Nout)\le\gamma_\star B$, and let $\Delta_0$ satisfy
$\norm{\Delta_0}_\F^2\le E_\star$ and $r_0\le\cR(\Delta_0)\le r_1$. Then:
\begin{enumerate}[label=(\roman*)]
\item the system \cref{eqn:app-dyn-ode} has a unique solution on
$[0,T_\star]$, and $\fQ_{ij}(\macrotime)\ge0$ for all $i,j$ and $\macrotime\le T_\star$;
\item for $\macrotime\le T_\star$, $\abs{\chi^{\mathrm{ode}}(\macrotime)(\mathbb K)-\norm{\Delta_0}_\F^2}\le C_E\macrotime$
and $\abs{\fRisk(\macrotime)-\cR(\Delta_0)}\le C_{\cR}\macrotime$; in particular
$\chi^{\mathrm{ode}}(\macrotime)\in\mathfrak M$;
\item $\chi^{\mathrm{ode}}$ satisfies \cref{eqn:app-dyn-ode-measure} on $[0,T_\star]$.
\end{enumerate}
\end{proposition}
```
-/
theorem prop_app_dyn_ode_iii {m n : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    {B : ℕ} (c : DynCoeff p S B) (Δ0 : Mat m n)
    (hSout : opNorm C.Sout ≤ p.CSig) (hSin : opNorm C.Sin ≤ p.CSig)
    (hdim : ((max m n : ℕ) : ℝ) ≤ p.γstar * (B : ℝ))
    (hE : fro Δ0 ^ 2 ≤ p.Estar) (hR0 : p.r0 ≤ riskSigma C Δ0) (hR1 : riskSigma C Δ0 ≤ p.r1) :
    ∀ e : ℝ → Fin m → Fin n → ℝ, def_app_dyn_ode p S c Δ0 (Tstar p) e →
      ∀ φ : ℝ × ℝ → ℝ, Measurable φ → (∃ M0 : ℝ, ∀ x, |φ x| ≤ M0) →
      ∀ τ ∈ Icc 0 (Tstar p),
        IntervalIntegrable
            (fun σ => fieldOp p.h c.d c.ζ (odeMeasure (B : ℝ) S.μ S.lam (e σ)) φ)
            MeasureTheory.volume 0 τ ∧
        (∫ x, φ x ∂(odeMeasure (B : ℝ) S.μ S.lam (e τ))) =
          (∫ x, φ x ∂(odeMeasure (B : ℝ) S.μ S.lam (e 0))) +
            (∫ σ in (0 : ℝ)..τ, fieldOp p.h c.d c.ζ (odeMeasure (B : ℝ) S.μ S.lam (e σ)) φ) := by
  intro e he φ hφm _ τ hτ
  have hB : 0 < B := batch_pos_of_initial_risk p S Δ0 hdim hR0
  have hBc : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hT := Tstar_nonneg' p
  have hpos := he.2
  have hnnT : ∀ s ∈ Icc 0 (Tstar p), ∀ i j, 0 ≤ e s i j / (B : ℝ) ^ 2 :=
    prop_app_dyn_ode_i_nonneg p S c Δ0 e he
  have hecont : ContinuousOn e (Icc 0 (Tstar p)) := fun t ht => (he.1.2 t ht).continuousWithinAt
  let w : Fin m → Fin n → ℝ := fun i j => φ (S.μ i, S.lam j)
  let Gf : ℝ → ℝ := fun s => ∑ i, ∑ j, e s i j / (B : ℝ) ^ 2 * w i j
  let G' : ℝ → ℝ := fun s => ∑ i, ∑ j,
    odeRHS p.h (B : ℝ) S.μ S.lam c.d c.v (e s) i j / (B : ℝ) ^ 2 * w i j
  have hA : ∀ s ∈ Icc 0 (Tstar p),
      ∫ x, φ x ∂(odeMeasure (B : ℝ) S.μ S.lam (e s)) = Gf s := by
    intro s hs
    unfold odeMeasure
    rw [atom_integral _ _ _ (hnnT s hs)]
  have hBfield : ∀ s ∈ Icc 0 (Tstar p),
      fieldOp p.h c.d c.ζ (odeMeasure (B : ℝ) S.μ S.lam (e s)) φ = G' s := by
    intro s hs
    have hrisk := riskOf_odeMeasure (B : ℝ) S.μ S.lam (e s) (hnnT s hs)
    have hRp : 0 < riskOf (odeMeasure (B : ℝ) S.μ S.lam (e s)) := by
      rw [hrisk]; exact hpos s hs
    have hI1 : ∫ x, φ x * c.d x ∂(odeMeasure (B : ℝ) S.μ S.lam (e s)) =
        ∑ i, ∑ j, e s i j / (B : ℝ) ^ 2 * (w i j * c.d (S.μ i, S.lam j)) := by
      unfold odeMeasure
      rw [atom_integral _ _ _ (hnnT s hs)]
    have hI2 : ∫ x, φ x ∂c.ζ = ∑ i, ∑ j, c.v i j / (B : ℝ) * w i j := by
      rw [c.ζ_eq, atom_integral _ _ _ (fun i j => div_nonneg (c.v_nonneg i j) hBc.le)]
    unfold fieldOp
    rw [if_pos hRp, hI1, hI2, hrisk]
    dsimp only [G']
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold odeRHS
    field_simp
  have hC : ∀ s ∈ Icc 0 (Tstar p), HasDerivWithinAt Gf (G' s) (Icc 0 (Tstar p)) s :=
    fun s hs => odeWeighted_hasDerivWithinAt (B : ℝ) w e _ _ _ (he.1.2 s hs)
  have hGcont : ContinuousOn Gf (Icc 0 (Tstar p)) := by
    dsimp only [Gf]
    fun_prop
  have hRcont : ContinuousOn (fun s => odeRisk S.μ S.lam (B : ℝ) (e s)) (Icc 0 (Tstar p)) := by
    unfold odeRisk
    fun_prop
  have hinv : ContinuousOn (fun s => (Real.sqrt (odeRisk S.μ S.lam (B : ℝ) (e s)))⁻¹)
      (Icc 0 (Tstar p)) :=
    (hRcont.sqrt).inv₀ fun s hs => (Real.sqrt_pos.2 (hpos s hs)).ne'
  have hG'cont : ContinuousOn G' (Icc 0 (Tstar p)) := by
    refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
    have hec : ContinuousOn (fun s => e s i j) (Icc 0 (Tstar p)) := by fun_prop
    unfold odeRHS
    simp only [div_eq_mul_inv]
    fun_prop
  have hsub : Icc 0 τ ⊆ Icc 0 (Tstar p) := Icc_subset_Icc_right hτ.2
  have hcontF : ContinuousOn
      (fun σ => fieldOp p.h c.d c.ζ (odeMeasure (B : ℝ) S.μ S.lam (e σ)) φ) (uIcc 0 τ) := by
    rw [uIcc_of_le hτ.1]
    exact (hG'cont.mono hsub).congr fun s hs => hBfield s (hsub hs)
  refine ⟨hcontF.intervalIntegrable, ?_⟩
  have hint : (∫ σ in (0 : ℝ)..τ, fieldOp p.h c.d c.ζ (odeMeasure (B : ℝ) S.μ S.lam (e σ)) φ) =
      ∫ σ in (0 : ℝ)..τ, G' σ := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hτ.1] at hs
    exact hBfield s (hsub hs)
  rw [hint, hA τ hτ, hA 0 ⟨le_rfl, hT⟩]
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.1 (hGcont.mono hsub)
    (f' := G') (fun x hx => ((hC x (hsub ⟨hx.1.le, hx.2.le⟩)).mono hsub).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)) ((hG'cont.mono hsub).intervalIntegrable_of_Icc hτ.1)
  rw [this]
  ring

end Muon.Dynamics

end

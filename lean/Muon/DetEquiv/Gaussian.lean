import Muon.Setup.Residual
import Muon.Setup.Frozen
import Muon.Foundations.Gaussian
import Muon.Foundations.GaussianCombinatorics

/-!
# Appendix B: Gaussian moment, Bessel and response lemmas (task L-B.6)

Snapshot `cr-2026-10-23`. Source: `sections/02-deterministic-equivalents/section.tex`:
`lem:app-de-moments` (l.879–896), `lem:app-de-bessel` (l.945–956), `lem:app-de-stein`
(l.986–1002). Every declaration's docstring carries its verbatim LaTeX environment.

Reuse (nothing redefined):
* `Muon.Setup.gaussPair`, `Muon.Setup.resid`, `Muon.Setup.lem_app_setup_residual_i`
  (A's admitted residual law), `Muon.Setup.rOut`, `Muon.Setup.rIn`, `Muon.Setup.eucNorm`,
  `Muon.Covariances`, `Muon.opNorm`, `Muon.fro`, `Muon.outer`, `Muon.mean`,
  `Muon.Foundations.stdGaussianPi`.
* Stein's one-dimensional lemma is `Muon.Foundations.gaussian_stein` (proved, not certified);
  it is used in the proofs, not restated here.

Representation choices:
* `lem:app-de-moments` is stated at finite `B`: the hypotheses are `N_out, N_in ≤ γ⋆ B`,
  `‖Σ_out‖, ‖Σ_in‖ ≤ C_Σ` and `‖Â‖_F = 1`, not the asymptotic `assum:app-setup-regime`.
  Parts are one theorem each; `L^p` norms are `eLpNorm` (no integrability is assumed).
* `lem:app-de-bessel` is stated for a sub-σ-algebra `G` of the ambient space: `(z,w)` has
  law `gaussPair`, is independent of `G`, and `e` is measurable with respect to
  `σ(z,w) ∨ G` and square integrable. The `G`-conditional norms are `condExp G P`. One
  declaration covers real and complex `e` (`RCLike 𝕜`).
* `lem:app-de-stein`: hypotheses on `f` are `C³` with `f, f', f'', f'''` polynomially bounded
  (orders 0–3; order 0 is needed for integrability). The `‖f'''‖_∞` bound is stated as
  "for every `M` bounding `|f'''|`", which is equivalent to the supremum form. The transposed
  versions are separate declarations on `gaussPair n m` with `A` replaced by `Aᵀ`; `(Aᵀ)ᵀ`
  is written as `A`.
-/

set_option linter.style.longLine false

open scoped Matrix MatrixOrder ENNReal ContDiff
open MeasureTheory ProbabilityTheory Filter Topology
open Muon Muon.Setup

noncomputable section

namespace Muon.DetEquiv

/-! ## Gaussian moment bounds (`lem:app-de-moments`) -/

/-- Scaled output vector `u = Σ_out^{1/2} z / √B` of `lem:app-de-moments` (`section.tex`
l.881), as a function of the pair `x = (z, w)`. -/
def momU {m n : ℕ} (C : Covariances m n) (B : ℕ) (x : Vec m × Vec n) : Vec m :=
  (Real.sqrt (B : ℝ))⁻¹ • Matrix.mulVec (rOut C) x.1

/-- Scaled input vector `v = Σ_in^{1/2} w / √B` of `lem:app-de-moments` (`section.tex` l.881). -/
def momV {m n : ℕ} (C : Covariances m n) (B : ℕ) (x : Vec m × Vec n) : Vec n :=
  (Real.sqrt (B : ℝ))⁻¹ • Matrix.mulVec (rIn C) x.2

/-- `𝖭 = ‖u‖² + ‖v‖²` of `lem:app-de-moments` (`section.tex` l.881). -/
def momN {m n : ℕ} (C : Covariances m n) (B : ℕ) (x : Vec m × Vec n) : ℝ :=
  eucNorm (momU C B x) ^ 2 + eucNorm (momV C B x) ^ 2

/-- Private helper for part (ii): `E (∑ z_i²)^q` is integrable under the standard Gaussian. -/
private lemma de_sq_sum_pow_integrable (n q : ℕ) :
    Integrable (fun z : Vec n => (∑ i, z i ^ 2) ^ q) (Muon.Foundations.stdGaussianPi n) := by
  cases q with
  | zero => simpa using integrable_const (1 : ℝ)
  | succ k =>
    have hcoord : ∀ i : Fin n, Integrable (fun z : Vec n => (z i ^ 2) ^ (k + 1))
        (Muon.Foundations.stdGaussianPi n) := by
      intro i
      have hm : MeasurePreserving (fun z : Vec n => z i) (Muon.Foundations.stdGaussianPi n)
          (gaussianReal 0 1) := by
        unfold Muon.Foundations.stdGaussianPi
        exact measurePreserving_eval _ i
      have h2 := (hm.integrable_comp (g := fun x : ℝ => x ^ (2 * (k + 1)))
        (by fun_prop)).2 (Muon.Foundations.gaussian_integrable_pow (2 * (k + 1)))
      convert h2 using 1
      funext z
      simp [← pow_mul, mul_comm]
    have hsum : Integrable (fun z : Vec n => ∑ i, (z i ^ 2) ^ (k + 1))
        (Muon.Foundations.stdGaussianPi n) :=
      integrable_finsetSum _ (fun i _ => hcoord i)
    refine Integrable.mono' (hsum.const_mul ((n : ℝ) ^ k)) ?_ ?_
    · exact (by fun_prop : Continuous fun z : Vec n => (∑ i, z i ^ 2) ^ (k + 1)).aestronglyMeasurable
    · refine Eventually.of_forall (fun z => ?_)
      have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ z i ^ 2 := fun i _ => sq_nonneg _
      have h := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => z i ^ 2) hnn k
      rw [Real.norm_of_nonneg (pow_nonneg (Finset.sum_nonneg hnn) _)]
      simpa [Finset.card_univ, Fintype.card_fin] using h

/-- Private helper for part (ii): the pointwise bound `d² ≤ (∑ z_i²)(∑ w_j²)` when `‖Δ‖_F = 1`. -/
private lemma de_resid_sq_le {m n : ℕ} (Ah : Mat m n) (hA : fro Ah = 1) (x : Vec m × Vec n) :
    resid Ah x ^ 2 ≤ (∑ i, x.1 i ^ 2) * (∑ j, x.2 j ^ 2) := by
  have hfro : ∑ i, ∑ j, Ah i j ^ 2 = 1 := by
    have h := hA
    unfold fro at h
    rw [Real.sqrt_eq_one] at h
    simp [Real.norm_eq_abs, sq_abs] at h
    exact h
  have hv : ∀ i, (Matrix.mulVec Ah x.2 i) ^ 2 ≤ (∑ j, Ah i j ^ 2) * (∑ j, x.2 j ^ 2) := by
    intro i
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) (fun j => Ah i j)
      (fun j => x.2 j)
    simpa [Matrix.mulVec, dotProduct] using this
  have hsum : ∑ i, (Matrix.mulVec Ah x.2 i) ^ 2 ≤ ∑ j, x.2 j ^ 2 := by
    calc ∑ i, (Matrix.mulVec Ah x.2 i) ^ 2
        ≤ ∑ i, (∑ j, Ah i j ^ 2) * (∑ j, x.2 j ^ 2) := Finset.sum_le_sum (fun i _ => hv i)
      _ = (∑ i, ∑ j, Ah i j ^ 2) * (∑ j, x.2 j ^ 2) := by rw [Finset.sum_mul]
      _ = ∑ j, x.2 j ^ 2 := by rw [hfro, one_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
    (fun i => x.1 i) (fun i => Matrix.mulVec Ah x.2 i)
  have hres : resid Ah x = ∑ i, x.1 i * Matrix.mulVec Ah x.2 i := by
    simp [resid, dotProduct]
  rw [hres]
  calc (∑ i, x.1 i * Matrix.mulVec Ah x.2 i) ^ 2
      ≤ (∑ i, x.1 i ^ 2) * ∑ i, (Matrix.mulVec Ah x.2 i) ^ 2 := hcs
    _ ≤ (∑ i, x.1 i ^ 2) * ∑ j, x.2 j ^ 2 :=
        mul_le_mul_of_nonneg_left hsum (Finset.sum_nonneg (fun i _ => sq_nonneg _))

private lemma de_sqrt_quad_le {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosSemidef)
    (C : ℝ) (hC : opNorm S ≤ C) (z : Vec m) :
    ∑ i, (Matrix.mulVec (CFC.sqrt S) z i) ^ 2 ≤ C * ∑ i, z i ^ 2 := by
  have h0 : 0 ≤ S := Matrix.nonneg_iff_posSemidef.mpr hS
  have hR : (CFC.sqrt S).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).isHermitian
  have hRR : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S h0
  have hsym : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
    simpa using hR.eq
  have h1 : ∑ i, (Matrix.mulVec (CFC.sqrt S) z i) ^ 2 = dotProduct z (Matrix.mulVec S z) := by
    calc ∑ i, (Matrix.mulVec (CFC.sqrt S) z i) ^ 2
        = dotProduct (Matrix.mulVec (CFC.sqrt S) z) (Matrix.mulVec (CFC.sqrt S) z) := by
          simp [dotProduct, sq]
      _ = dotProduct z (Matrix.mulVec S z) := by
          rw [Matrix.dotProduct_mulVec, ← hsym, Matrix.vecMul_transpose, hsym,
            Matrix.mulVec_mulVec, hRR, dotProduct_comm]
  have h2 : ‖Matrix.toEuclideanLin S (WithLp.toLp 2 z)‖ ≤ opNorm S * ‖WithLp.toLp 2 z‖ := by
    have := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin S)).le_opNorm (WithLp.toLp 2 z)
    simpa [opNorm] using this
  have hn : ∀ v : Vec m, ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, v i ^ 2 := by
    intro v
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have h3 : dotProduct z (Matrix.mulVec S z)
      = inner ℝ (WithLp.toLp 2 z) (Matrix.toEuclideanLin S (WithLp.toLp 2 z)) := by
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_toLp, dotProduct, PiLp.inner_apply, mul_comm]
  have h4 : ‖Matrix.toEuclideanLin S (WithLp.toLp 2 z)‖ ≤ C * ‖WithLp.toLp 2 z‖ :=
    h2.trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
  rw [h1, h3, ← hn]
  calc inner ℝ (WithLp.toLp 2 z) (Matrix.toEuclideanLin S (WithLp.toLp 2 z))
      ≤ ‖WithLp.toLp 2 z‖ * ‖Matrix.toEuclideanLin S (WithLp.toLp 2 z)‖ := real_inner_le_norm _ _
    _ ≤ ‖WithLp.toLp 2 z‖ * (C * ‖WithLp.toLp 2 z‖) :=
        mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ = C * ‖WithLp.toLp 2 z‖ ^ 2 := by ring

private lemma de_dfact_succ (q : ℕ) :
    ((Nat.doubleFactorial (2 * (q + 1) - 1) : ℕ) : ℝ)
      = (2 * (q : ℝ) + 1) * ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) := by
  rcases q with _ | r
  · simp
  · have h : 2 * (r + 1 + 1) - 1 = (2 * (r + 1) - 1) + 2 := by omega
    rw [h, Nat.doubleFactorial_add_two]
    have h2 : 2 * (r + 1) - 1 + 2 = 2 * (r + 1) + 1 := by omega
    rw [h2]
    push_cast
    ring

private lemma de_prod_le (m q : ℕ) :
    ∏ j ∈ Finset.range q, ((m : ℝ) + 2 * (j : ℝ))
      ≤ (m : ℝ) ^ q * ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · cases q with
    | zero => simp
    | succ q =>
      rw [Finset.prod_eq_zero (i := 0) (Finset.mem_range.2 (by omega)) (by simp)]
      positivity
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Finset.prod_range_succ, de_dfact_succ, pow_succ]
      have hD : (0 : ℝ) ≤ ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
      have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
      calc (∏ j ∈ Finset.range q, ((m : ℝ) + 2 * (j : ℝ))) * ((m : ℝ) + 2 * (q : ℝ))
          ≤ ((m : ℝ) ^ q * ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ)) * ((m : ℝ) + 2 * (q : ℝ)) :=
            mul_le_mul_of_nonneg_right ih (by positivity)
        _ ≤ ((m : ℝ) ^ q * ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ)) * ((m : ℝ) * (2 * q + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith
        _ = (m : ℝ) ^ q * (m : ℝ) * ((2 * (q : ℝ) + 1) * ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ)) := by
            ring

private lemma de_gen_lintegral {k : ℕ} (f : Vec k → ℝ) (hf : Continuous f) (c K0 : ℝ) (hc : 0 ≤ c)
    (hck : c * (k : ℝ) ≤ K0) (hb : ∀ z, 0 ≤ f z ∧ f z ≤ c * ∑ i, z i ^ 2) (q : ℕ) (hq : 1 ≤ q) :
    ∫⁻ z, ENNReal.ofReal (f z ^ q) ∂(Muon.Foundations.stdGaussianPi k)
      ≤ ENNReal.ofReal (K0 ^ q * ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ)) := by
  have hint : Integrable (fun z : Vec k => (c * ∑ i, z i ^ 2) ^ q)
      (Muon.Foundations.stdGaussianPi k) := by
    simp_rw [mul_pow]
    exact (de_sq_sum_pow_integrable k q).const_mul (c ^ q)
  have hint2 : Integrable (fun z : Vec k => f z ^ q) (Muon.Foundations.stdGaussianPi k) := by
    refine Integrable.mono' hint (by fun_prop : Continuous fun z : Vec k => f z ^ q).aestronglyMeasurable
      (Eventually.of_forall (fun z => ?_))
    rw [Real.norm_of_nonneg (pow_nonneg (hb z).1 _)]
    exact pow_le_pow_left₀ (hb z).1 (hb z).2 q
  rw [← ofReal_integral_eq_lintegral_ofReal hint2
    (Eventually.of_forall (fun z => pow_nonneg (hb z).1 _))]
  apply ENNReal.ofReal_le_ofReal
  calc ∫ z, f z ^ q ∂(Muon.Foundations.stdGaussianPi k)
      ≤ ∫ z, (c * ∑ i, z i ^ 2) ^ q ∂(Muon.Foundations.stdGaussianPi k) :=
        integral_mono hint2 hint (fun z => pow_le_pow_left₀ (hb z).1 (hb z).2 q)
    _ = c ^ q * ∫ z, (∑ i, z i ^ 2) ^ q ∂(Muon.Foundations.stdGaussianPi k) := by
        simp_rw [mul_pow]; exact integral_const_mul _ _
    _ = c ^ q * ∏ j ∈ Finset.range q, ((k : ℝ) + 2 * (j : ℝ)) := by
        rw [Muon.Foundations.stdGaussianPi_sq_norm_moment k q hq]
    _ ≤ c ^ q * ((k : ℝ) ^ q * ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (de_prod_le k q) (pow_nonneg hc _)
    _ = (c * (k : ℝ)) ^ q * ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) := by ring
    _ ≤ K0 ^ q * ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hck q) (Nat.cast_nonneg _)

private lemma de_eLpNorm_of_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : α → ℝ) (hg : AEStronglyMeasurable g μ) (hnn : ∀ x, 0 ≤ g x) (p : ℕ) (hp : 1 ≤ p)
    (K : ℝ) (hK : 0 ≤ K) (h : ∫⁻ x, ENNReal.ofReal (g x ^ p) ∂μ ≤ ENNReal.ofReal K) :
    eLpNorm g (p : ℝ≥0∞) μ ≤ ENNReal.ofReal (K ^ ((1 : ℝ) / p)) := by
  have hpt : ∀ x : α, ‖g x‖ₑ ^ (((p : ℕ) : ℝ≥0∞).toReal) = ENNReal.ofReal (g x ^ p) := by
    intro x
    rw [ENNReal.toReal_natCast, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hnn x),
      ENNReal.ofReal_rpow_of_nonneg (hnn x) (by positivity), Real.rpow_natCast]
  have hp0 : ((p : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 (ENNReal.natCast_ne_top _) hg]
  simp_rw [hpt]
  rw [ENNReal.toReal_natCast]
  calc (∫⁻ x, ENNReal.ofReal (g x ^ p) ∂μ) ^ (1 / (p : ℝ))
      ≤ (ENNReal.ofReal K) ^ (1 / (p : ℝ)) := ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal (K ^ ((1 : ℝ) / p)) := ENNReal.ofReal_rpow_of_nonneg hK (by positivity)

private lemma de_rpow_aux (a D : ℝ) (ha : 0 ≤ a) (hD : 0 ≤ D) (p : ℕ) (hp : 1 ≤ p) :
    (a ^ p * D) ^ ((1 : ℝ) / p) = a * D ^ ((1 : ℝ) / p) := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [Real.mul_rpow (pow_nonneg ha _) hD, ← Real.rpow_natCast, ← Real.rpow_mul ha]
  rw [mul_one_div_cancel hp', Real.rpow_one]

private lemma de_part_std {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.PosSemidef) (B : ℕ)
    (hB : 0 < B) (γ CSig : ℝ) (hk : (k : ℝ) ≤ γ * (B : ℝ)) (hC : opNorm S ≤ CSig) (q : ℕ)
    (hq : 1 ≤ q) :
    ∫⁻ z, ENNReal.ofReal (((B : ℝ)⁻¹ * ∑ i, (Matrix.mulVec (CFC.sqrt S) z i) ^ 2) ^ q)
        ∂(Muon.Foundations.stdGaussianPi k)
      ≤ ENNReal.ofReal ((CSig * γ) ^ q * ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ)) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hC0 : 0 ≤ CSig := le_trans (norm_nonneg _) hC
  refine de_gen_lintegral (fun z => (B : ℝ)⁻¹ * ∑ i, (Matrix.mulVec (CFC.sqrt S) z i) ^ 2)
    (by fun_prop) (CSig * (B : ℝ)⁻¹) (CSig * γ) (by positivity) ?_ ?_ q hq
  · have : (B : ℝ)⁻¹ * (k : ℝ) ≤ γ := by
      calc (B : ℝ)⁻¹ * (k : ℝ) ≤ (B : ℝ)⁻¹ * (γ * B) :=
            mul_le_mul_of_nonneg_left hk (by positivity)
        _ = γ := by field_simp
    calc CSig * (B : ℝ)⁻¹ * (k : ℝ) = CSig * ((B : ℝ)⁻¹ * (k : ℝ)) := by ring
      _ ≤ CSig * γ := mul_le_mul_of_nonneg_left this hC0
  · intro z
    refine ⟨by positivity, ?_⟩
    have := de_sqrt_quad_le S hS CSig hC z
    calc (B : ℝ)⁻¹ * ∑ i, (Matrix.mulVec (CFC.sqrt S) z i) ^ 2
        ≤ (B : ℝ)⁻¹ * (CSig * ∑ i, z i ^ 2) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = CSig * (B : ℝ)⁻¹ * ∑ i, z i ^ 2 := by ring

private lemma de_uSq_eq {m n : ℕ} (C : Covariances m n) (B : ℕ) (x : Vec m × Vec n) :
    eucNorm (momU C B x) ^ 2 = (B : ℝ)⁻¹ * ∑ i, (Matrix.mulVec (rOut C) x.1 i) ^ 2 := by
  unfold eucNorm momU
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

private lemma de_vSq_eq {m n : ℕ} (C : Covariances m n) (B : ℕ) (x : Vec m × Vec n) :
    eucNorm (momV C B x) ^ 2 = (B : ℝ)⁻¹ * ∑ i, (Matrix.mulVec (rIn C) x.2 i) ^ 2 := by
  unfold eucNorm momV
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

private lemma de_lintU {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig : ℝ)
    (hm : (m : ℝ) ≤ γ * (B : ℝ)) (hC : opNorm C.Sout ≤ CSig) (q : ℕ) (hq : 1 ≤ q) :
    ∫⁻ x, ENNReal.ofReal ((eucNorm (momU C B x) ^ 2) ^ q) ∂(gaussPair m n)
      ≤ ENNReal.ofReal ((CSig * γ) ^ q * ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ)) := by
  have h := de_part_std C.Sout C.psdOut B hB γ CSig hm hC q hq
  have hmp : MeasurePreserving (Prod.fst : Vec m × Vec n → Vec m) (gaussPair m n)
      (Muon.Foundations.stdGaussianPi m) := measurePreserving_fst
  have hmeas : Measurable (fun z : Vec m => ENNReal.ofReal
      (((B : ℝ)⁻¹ * ∑ i, (Matrix.mulVec (CFC.sqrt C.Sout) z i) ^ 2) ^ q)) := by
    apply ENNReal.measurable_ofReal.comp
    exact (by fun_prop : Continuous fun z : Vec m =>
      ((B : ℝ)⁻¹ * ∑ i, (Matrix.mulVec (CFC.sqrt C.Sout) z i) ^ 2) ^ q).measurable
  have := hmp.lintegral_comp hmeas
  simp only [de_uSq_eq]
  rw [show (∫⁻ x, ENNReal.ofReal (((B : ℝ)⁻¹ * ∑ i, (Matrix.mulVec (rOut C) x.1 i) ^ 2) ^ q)
      ∂(gaussPair m n)) = ∫⁻ x, ENNReal.ofReal (((B : ℝ)⁻¹ * ∑ i, (Matrix.mulVec (CFC.sqrt C.Sout) x.1 i) ^ 2) ^ q)
      ∂(gaussPair m n) from rfl, this]
  exact h

private lemma de_lintV {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig : ℝ)
    (hn : (n : ℝ) ≤ γ * (B : ℝ)) (hC : opNorm C.Sin ≤ CSig) (q : ℕ) (hq : 1 ≤ q) :
    ∫⁻ x, ENNReal.ofReal ((eucNorm (momV C B x) ^ 2) ^ q) ∂(gaussPair m n)
      ≤ ENNReal.ofReal ((CSig * γ) ^ q * ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ)) := by
  have h := de_part_std C.Sin C.psdIn B hB γ CSig hn hC q hq
  have hmp : MeasurePreserving (Prod.snd : Vec m × Vec n → Vec n) (gaussPair m n)
      (Muon.Foundations.stdGaussianPi n) := measurePreserving_snd
  have hmeas : Measurable (fun z : Vec n => ENNReal.ofReal
      (((B : ℝ)⁻¹ * ∑ i, (Matrix.mulVec (CFC.sqrt C.Sin) z i) ^ 2) ^ q)) := by
    apply ENNReal.measurable_ofReal.comp
    exact (by fun_prop : Continuous fun z : Vec n =>
      ((B : ℝ)⁻¹ * ∑ i, (Matrix.mulVec (CFC.sqrt C.Sin) z i) ^ 2) ^ q).measurable
  have := hmp.lintegral_comp hmeas
  simp only [de_vSq_eq]
  rw [show (∫⁻ x, ENNReal.ofReal (((B : ℝ)⁻¹ * ∑ i, (Matrix.mulVec (rIn C) x.2 i) ^ 2) ^ q)
      ∂(gaussPair m n)) = ∫⁻ x, ENNReal.ofReal (((B : ℝ)⁻¹ * ∑ i, (Matrix.mulVec (CFC.sqrt C.Sin) x.2 i) ^ 2) ^ q)
      ∂(gaussPair m n) from rfl, this]
  exact h

private lemma de_contU {m n : ℕ} (C : Covariances m n) (B : ℕ) :
    Continuous (fun x : Vec m × Vec n => eucNorm (momU C B x) ^ 2) := by
  have : (fun x : Vec m × Vec n => eucNorm (momU C B x) ^ 2)
      = fun x => (B : ℝ)⁻¹ * ∑ i, (Matrix.mulVec (rOut C) x.1 i) ^ 2 := funext (de_uSq_eq C B)
  rw [this]; fun_prop

private lemma de_contV {m n : ℕ} (C : Covariances m n) (B : ℕ) :
    Continuous (fun x : Vec m × Vec n => eucNorm (momV C B x) ^ 2) := by
  have : (fun x : Vec m × Vec n => eucNorm (momV C B x) ^ 2)
      = fun x => (B : ℝ)⁻¹ * ∑ i, (Matrix.mulVec (rIn C) x.2 i) ^ 2 := funext (de_vSq_eq C B)
  rw [this]; fun_prop

private lemma de_eLpU {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig : ℝ)
    (hγ : 0 ≤ γ) (hm : (m : ℝ) ≤ γ * (B : ℝ)) (hC : opNorm C.Sout ≤ CSig) (p : ℕ) (hp : 1 ≤ p) :
    eLpNorm (fun x => eucNorm (momU C B x) ^ 2) (p : ℝ≥0∞) (gaussPair m n)
      ≤ ENNReal.ofReal (CSig * γ * ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / p)) := by
  have hC0 : 0 ≤ CSig := le_trans (norm_nonneg _) hC
  have h := de_eLpNorm_of_lintegral (μ := gaussPair m n) (fun x => eucNorm (momU C B x) ^ 2)
    (de_contU C B).aestronglyMeasurable (fun x => sq_nonneg _) p hp
    ((CSig * γ) ^ p * ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ)) (by positivity)
    (de_lintU C B hB γ CSig hm hC p hp)
  rwa [de_rpow_aux _ _ (by positivity) (Nat.cast_nonneg _) p hp] at h

private lemma de_eLpV {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig : ℝ)
    (hγ : 0 ≤ γ) (hn : (n : ℝ) ≤ γ * (B : ℝ)) (hC : opNorm C.Sin ≤ CSig) (p : ℕ) (hp : 1 ≤ p) :
    eLpNorm (fun x => eucNorm (momV C B x) ^ 2) (p : ℝ≥0∞) (gaussPair m n)
      ≤ ENNReal.ofReal (CSig * γ * ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / p)) := by
  have hC0 : 0 ≤ CSig := le_trans (norm_nonneg _) hC
  have h := de_eLpNorm_of_lintegral (μ := gaussPair m n) (fun x => eucNorm (momV C B x) ^ 2)
    (de_contV C B).aestronglyMeasurable (fun x => sq_nonneg _) p hp
    ((CSig * γ) ^ p * ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ)) (by positivity)
    (de_lintV C B hB γ CSig hn hC p hp)
  rwa [de_rpow_aux _ _ (by positivity) (Nat.cast_nonneg _) p hp] at h

/-- B = 0 forces `m = n = 0`, hence all the scaled norms vanish. -/
private lemma de_B_zero {m n : ℕ} (B : ℕ) (γ : ℝ) (hB : B = 0)
    (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) : m = 0 ∧ n = 0 := by
  subst hB
  simp only [Nat.cast_zero, mul_zero] at hdim
  exact ⟨by exact_mod_cast le_antisymm hdim.1 (Nat.cast_nonneg _),
    by exact_mod_cast le_antisymm hdim.2 (Nat.cast_nonneg _)⟩

/-- `lem:app-de-moments`, part (i), snapshot `cr-2026-10-23`. Verbatim from the frozen source
(`section.tex` l.879–896):

\begin{lemma}[Gaussian moment bounds]\label{lem:app-de-moments}
Let $z\sim\mathcal N(0,\Id_{\Nout})$, $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent, let $\Sigmaout,\Sigmain$ satisfy \cref{assum:app-setup-regime}, and
put $\mathsf u=\Sigmaout^{1/2}z/\sqrt B$, $\mathsf v=\Sigmain^{1/2}w/\sqrt B$,
$\mathsf N=\norm{\mathsf u}^2+\norm{\mathsf v}^2$ and $d=z^\T\Ahat w$. Then
for every integer $p\ge1$
\[
\begin{gathered}
\norm{\mathsf N}_p\le2C_\Sigma\gamma_\star\big((2p-1)!!\big)^{1/p},\qquad
\norm{d}_{2p}\le\big((2p-1)!!\big)^{1/p},\\
\big\|\abs d\,\norm{\mathsf u}\norm{\mathsf v}\big\|_2\le 15^{2/3}\,C_\Sigma\gamma_\star\le 7\,C_\Sigma\gamma_\star .
\end{gathered}
\]
Also, for any symmetric $A\in\R^{\Nout\times\Nout}$,
\[
\EE[z^\T Az]=\Tr A,\qquad \Var(z^\T Az)=2\norm{A}_\F^2 .
\]
\end{lemma}
-/
theorem lem_app_de_moments_i {m n : ℕ} (C : Covariances m n) (B : ℕ) (γ CSig : ℝ)
    (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ))
    (hC : opNorm C.Sout ≤ CSig ∧ opNorm C.Sin ≤ CSig) :
    ∀ p : ℕ, 1 ≤ p →
      eLpNorm (momN C B) (p : ℝ≥0∞) (gaussPair m n) ≤
        ENNReal.ofReal (2 * CSig * γ * ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / p)) := by
  intro p hp
  by_cases hB : B = 0
  · obtain ⟨rfl, rfl⟩ := de_B_zero B γ hB hdim
    have : momN C B = fun _ => 0 := by
      funext x; simp [momN, eucNorm]
    rw [this]; simp
  · have hBpos : 0 < B := Nat.pos_of_ne_zero hB
    have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
    have hγ : 0 ≤ γ := by
      by_contra h
      push Not at h
      have := hdim.1
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hC0 : 0 ≤ CSig := le_trans (norm_nonneg _) hC.1
    have hsum : momN C B = (fun x => eucNorm (momU C B x) ^ 2) + (fun x => eucNorm (momV C B x) ^ 2) := rfl
    have hp1 : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast hp
    rw [hsum]
    calc eLpNorm ((fun x => eucNorm (momU C B x) ^ 2) + (fun x => eucNorm (momV C B x) ^ 2))
          (p : ℝ≥0∞) (gaussPair m n)
        ≤ eLpNorm (fun x => eucNorm (momU C B x) ^ 2) (p : ℝ≥0∞) (gaussPair m n)
          + eLpNorm (fun x => eucNorm (momV C B x) ^ 2) (p : ℝ≥0∞) (gaussPair m n) :=
          eLpNorm_add_le hp1
      _ ≤ ENNReal.ofReal (CSig * γ * ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / p))
          + ENNReal.ofReal (CSig * γ * ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / p)) :=
          add_le_add (de_eLpU C B hBpos γ CSig hγ hdim.1 hC.1 p hp)
            (de_eLpV C B hBpos γ CSig hγ hdim.2 hC.2 p hp)
      _ = ENNReal.ofReal (2 * CSig * γ * ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / p)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring

/-- `lem:app-de-moments`, part (ii), snapshot `cr-2026-10-23`. Verbatim from the frozen source
(`section.tex` l.879–896):

\begin{lemma}[Gaussian moment bounds]\label{lem:app-de-moments}
Let $z\sim\mathcal N(0,\Id_{\Nout})$, $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent, let $\Sigmaout,\Sigmain$ satisfy \cref{assum:app-setup-regime}, and
put $\mathsf u=\Sigmaout^{1/2}z/\sqrt B$, $\mathsf v=\Sigmain^{1/2}w/\sqrt B$,
$\mathsf N=\norm{\mathsf u}^2+\norm{\mathsf v}^2$ and $d=z^\T\Ahat w$. Then
for every integer $p\ge1$
\[
\begin{gathered}
\norm{\mathsf N}_p\le2C_\Sigma\gamma_\star\big((2p-1)!!\big)^{1/p},\qquad
\norm{d}_{2p}\le\big((2p-1)!!\big)^{1/p},\\
\big\|\abs d\,\norm{\mathsf u}\norm{\mathsf v}\big\|_2\le 15^{2/3}\,C_\Sigma\gamma_\star\le 7\,C_\Sigma\gamma_\star .
\end{gathered}
\]
Also, for any symmetric $A\in\R^{\Nout\times\Nout}$,
\[
\EE[z^\T Az]=\Tr A,\qquad \Var(z^\T Az)=2\norm{A}_\F^2 .
\]
\end{lemma}
-/
theorem lem_app_de_moments_ii {m n : ℕ} (Ah : Mat m n) (hA : fro Ah = 1) :
    ∀ p : ℕ, 1 ≤ p →
      eLpNorm (fun x => resid Ah x) ((2 * p : ℕ) : ℝ≥0∞) (gaussPair m n) ≤
        ENNReal.ofReal (((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / p)) := by
  intro p hp
  set D : ℝ := ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) with hDdef
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  have hfin : ∫ x, |resid Ah x| ^ (2 * p) ∂(gaussPair m n) ≤ D ^ 2 :=
    (lem_app_setup_residual_i Ah hA).2.2.2.2 p hp
  have hmeasR : AEStronglyMeasurable (fun x => resid Ah x) (gaussPair m n) :=
    (by unfold resid; fun_prop : Continuous fun x : Vec m × Vec n => resid Ah x).aestronglyMeasurable
  have hbound : ∀ x : Vec m × Vec n,
      |resid Ah x| ^ (2 * p) ≤ (∑ i, x.1 i ^ 2) ^ p * (∑ j, x.2 j ^ 2) ^ p := by
    intro x
    rw [pow_mul, sq_abs, ← mul_pow]
    exact pow_le_pow_left₀ (sq_nonneg _) (de_resid_sq_le Ah hA x) p
  have hgint : Integrable (fun x : Vec m × Vec n => (∑ i, x.1 i ^ 2) ^ p * (∑ j, x.2 j ^ 2) ^ p)
      (gaussPair m n) := by
    unfold gaussPair
    exact Integrable.mul_prod (de_sq_sum_pow_integrable m p) (de_sq_sum_pow_integrable n p)
  have hint : Integrable (fun x : Vec m × Vec n => |resid Ah x| ^ (2 * p)) (gaussPair m n) := by
    refine Integrable.mono' hgint ?_ ?_
    · exact (by unfold resid; fun_prop : Continuous fun x : Vec m × Vec n =>
        |resid Ah x| ^ (2 * p)).aestronglyMeasurable
    · refine Eventually.of_forall (fun x => ?_)
      rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact hbound x
  have hnn : 0 ≤ᵐ[gaussPair m n] (fun x : Vec m × Vec n => |resid Ah x| ^ (2 * p)) :=
    Eventually.of_forall (fun x => pow_nonneg (abs_nonneg _) _)
  have hpt : ∀ x : Vec m × Vec n,
      ‖resid Ah x‖ₑ ^ (((2 * p : ℕ) : ℝ≥0∞).toReal) = ENNReal.ofReal (|resid Ah x| ^ (2 * p)) := by
    intro x
    rw [ENNReal.toReal_natCast, ← ofReal_norm, Real.norm_eq_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by positivity), Real.rpow_natCast]
  have hp0 : ((2 * p : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by omega : 2 * p ≠ 0)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 (ENNReal.natCast_ne_top _) hmeasR]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  rw [ENNReal.toReal_natCast]
  calc (ENNReal.ofReal (∫ x, |resid Ah x| ^ (2 * p) ∂(gaussPair m n))) ^ (1 / ((2 * p : ℕ) : ℝ))
      ≤ (ENNReal.ofReal (D ^ 2)) ^ (1 / ((2 * p : ℕ) : ℝ)) :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hfin) (by positivity)
    _ = ENNReal.ofReal ((D ^ 2) ^ (1 / ((2 * p : ℕ) : ℝ))) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
    _ = ENNReal.ofReal (D ^ ((1 : ℝ) / p)) := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hD0]
        congr 1
        have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
        push_cast
        field_simp

private lemma de_root (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (hn : 1 ≤ n) :
    (x ^ n) ^ ((1 : ℝ) / (n : ℝ)) = x := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_one_div_cancel this, Real.rpow_one]

private lemma de_root_ennreal (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (hn : 1 ≤ n) :
    (ENNReal.ofReal (x ^ n)) ^ ((1 : ℝ) / (n : ℝ)) = ENNReal.ofReal x := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), de_root x hx n hn]

private lemma de_resid_lint {m n : ℕ} (Ah : Mat m n) (hA : fro Ah = 1) (p : ℕ) (hp : 1 ≤ p) :
    ∫⁻ x, ENNReal.ofReal ((resid Ah x ^ 2) ^ p) ∂(gaussPair m n)
      ≤ ENNReal.ofReal (((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) ^ 2) := by
  have hfin : ∫ x, |resid Ah x| ^ (2 * p) ∂(gaussPair m n)
      ≤ ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) ^ 2 :=
    (lem_app_setup_residual_i Ah hA).2.2.2.2 p hp
  have hbound : ∀ x : Vec m × Vec n,
      |resid Ah x| ^ (2 * p) ≤ (∑ i, x.1 i ^ 2) ^ p * (∑ j, x.2 j ^ 2) ^ p := by
    intro x
    rw [pow_mul, sq_abs, ← mul_pow]
    exact pow_le_pow_left₀ (sq_nonneg _) (de_resid_sq_le Ah hA x) p
  have hgint : Integrable (fun x : Vec m × Vec n => (∑ i, x.1 i ^ 2) ^ p * (∑ j, x.2 j ^ 2) ^ p)
      (gaussPair m n) := by
    unfold gaussPair
    exact Integrable.mul_prod (de_sq_sum_pow_integrable m p) (de_sq_sum_pow_integrable n p)
  have hint : Integrable (fun x : Vec m × Vec n => |resid Ah x| ^ (2 * p)) (gaussPair m n) := by
    refine Integrable.mono' hgint ?_ ?_
    · exact (by unfold resid; fun_prop : Continuous fun x : Vec m × Vec n =>
        |resid Ah x| ^ (2 * p)).aestronglyMeasurable
    · refine Eventually.of_forall (fun x => ?_)
      rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact hbound x
  have hnn : 0 ≤ᵐ[gaussPair m n] (fun x : Vec m × Vec n => |resid Ah x| ^ (2 * p)) :=
    Eventually.of_forall (fun x => pow_nonneg (abs_nonneg _) _)
  have hrw : ∀ x : Vec m × Vec n, (resid Ah x ^ 2) ^ p = |resid Ah x| ^ (2 * p) := by
    intro x; rw [pow_mul, sq_abs]
  simp_rw [hrw]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  exact ENNReal.ofReal_le_ofReal hfin

private lemma de_iii_fst {m n : ℕ} (C : Covariances m n) (B : ℕ) (γ CSig : ℝ)
    (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ))
    (hC : opNorm C.Sout ≤ CSig ∧ opNorm C.Sin ≤ CSig) (Ah : Mat m n) (hA : fro Ah = 1) :
    eLpNorm (fun x => |resid Ah x| * eucNorm (momU C B x) * eucNorm (momV C B x)) 2
        (gaussPair m n) ≤ ENNReal.ofReal ((15 : ℝ) ^ ((2 : ℝ) / 3) * CSig * γ) := by
  by_cases hB : B = 0
  · obtain ⟨rfl, rfl⟩ := de_B_zero B γ hB hdim
    have : (fun x : Vec 0 × Vec 0 => |resid Ah x| * eucNorm (momU C B x) * eucNorm (momV C B x))
        = fun _ => 0 := by
      funext x; simp [eucNorm]
    rw [this]; simp
  · have hBpos : 0 < B := Nat.pos_of_ne_zero hB
    have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
    have hγ : 0 ≤ γ := by
      by_contra h
      push Not at h
      have := hdim.1
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hC0 : 0 ≤ CSig := le_trans (norm_nonneg _) hC.1
    set t : ℝ := CSig * γ with ht
    have ht0 : 0 ≤ t := by positivity
    set r : ℝ := (15 : ℝ) ^ ((1 : ℝ) / 3) with hr
    have hr0 : 0 < r := by positivity
    have hr3 : r ^ 3 = 15 := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have hr2 : r ^ 2 = (15 : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have hD3 : ((Nat.doubleFactorial (2 * 3 - 1) : ℕ) : ℝ) = 15 := by
      norm_num [Nat.doubleFactorial]
    -- the three lintegral bounds
    have h0 : ∫⁻ x, ENNReal.ofReal ((resid Ah x ^ 2) ^ 3) ∂(gaussPair m n)
        ≤ ENNReal.ofReal (((r ^ 2)) ^ 3) := by
      refine (de_resid_lint Ah hA 3 (by norm_num)).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hD3, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hr3]
    have h1 : ∫⁻ x, ENNReal.ofReal ((eucNorm (momU C B x) ^ 2) ^ 3) ∂(gaussPair m n)
        ≤ ENNReal.ofReal ((t * r) ^ 3) := by
      refine (de_lintU C B hBpos γ CSig hdim.1 hC.1 3 (by norm_num)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      rw [hD3, show (t * r) ^ 3 = t ^ 3 * 15 by rw [mul_pow, hr3]]
    have h2 : ∫⁻ x, ENNReal.ofReal ((eucNorm (momV C B x) ^ 2) ^ 3) ∂(gaussPair m n)
        ≤ ENNReal.ofReal ((t * r) ^ 3) := by
      refine (de_lintV C B hBpos γ CSig hdim.2 hC.2 3 (by norm_num)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      rw [hD3, show (t * r) ^ 3 = t ^ 3 * 15 by rw [mul_pow, hr3]]
    -- Hölder with three exponents 3
    set d2 : Vec m × Vec n → ℝ := fun x => resid Ah x ^ 2 with hd2
    set a : Vec m × Vec n → ℝ := fun x => eucNorm (momU C B x) ^ 2 with ha
    set b : Vec m × Vec n → ℝ := fun x => eucNorm (momV C B x) ^ 2 with hb
    have hcd : Continuous d2 := by rw [hd2]; unfold resid; fun_prop
    have hca : Continuous a := de_contU C B
    have hcb : Continuous b := de_contV C B
    have hmeas : ∀ f : Vec m × Vec n → ℝ, Continuous f →
        Measurable (fun x => ENNReal.ofReal (f x ^ 3)) := fun f hf =>
      ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun x => f x ^ 3).measurable
    let Fs : Fin 3 → Vec m × Vec n → ℝ≥0∞ := ![fun x => ENNReal.ofReal (d2 x ^ 3),
      fun x => ENNReal.ofReal (a x ^ 3), fun x => ENNReal.ofReal (b x ^ 3)]
    have hH := ENNReal.lintegral_prod_norm_pow_le (μ := gaussPair m n) (Finset.univ : Finset (Fin 3))
      (f := Fs) (p := fun _ => (1 : ℝ) / ((3 : ℕ) : ℝ))
      (by
        intro i _
        fin_cases i
        · exact (hmeas d2 hcd).aemeasurable
        · exact (hmeas a hca).aemeasurable
        · exact (hmeas b hcb).aemeasurable)
      (by simp) (by intro i _; positivity)
    simp only [Fin.prod_univ_three, Fs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp, Fin.succ_zero_eq_one] at hH
    have hnn3 : ∀ x, 0 ≤ d2 x ∧ 0 ≤ a x ∧ 0 ≤ b x := fun x => ⟨sq_nonneg _, sq_nonneg _, sq_nonneg _⟩
    have hpt : ∀ x, ENNReal.ofReal (d2 x ^ 3) ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))
        * ENNReal.ofReal (a x ^ 3) ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))
        * ENNReal.ofReal (b x ^ 3) ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))
        = ENNReal.ofReal (d2 x * a x * b x) := by
      intro x
      rw [de_root_ennreal _ (hnn3 x).1 3 (by norm_num), de_root_ennreal _ (hnn3 x).2.1 3 (by norm_num),
        de_root_ennreal _ (hnn3 x).2.2 3 (by norm_num),
        ← ENNReal.ofReal_mul (hnn3 x).1, ← ENNReal.ofReal_mul (mul_nonneg (hnn3 x).1 (hnn3 x).2.1)]
    simp_rw [hpt] at hH
    have hX : ∫⁻ x, ENNReal.ofReal (d2 x * a x * b x) ∂(gaussPair m n)
        ≤ ENNReal.ofReal ((r ^ 2 * t) ^ 2) := by
      refine hH.trans ?_
      calc (∫⁻ x, ENNReal.ofReal (d2 x ^ 3) ∂(gaussPair m n)) ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))
            * (∫⁻ x, ENNReal.ofReal (a x ^ 3) ∂(gaussPair m n)) ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))
            * (∫⁻ x, ENNReal.ofReal (b x ^ 3) ∂(gaussPair m n)) ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))
          ≤ (ENNReal.ofReal ((r ^ 2) ^ 3)) ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))
            * (ENNReal.ofReal ((t * r) ^ 3)) ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))
            * (ENNReal.ofReal ((t * r) ^ 3)) ^ ((1 : ℝ) / ((3 : ℕ) : ℝ)) := by
            gcongr
        _ = ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (t * r) * ENNReal.ofReal (t * r) := by
            rw [de_root_ennreal _ (by positivity) 3 (by norm_num),
              de_root_ennreal _ (by positivity) 3 (by norm_num)]
        _ = ENNReal.ofReal ((r ^ 2 * t) ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
    have hmeasG : AEStronglyMeasurable
        (fun x => |resid Ah x| * eucNorm (momU C B x) * eucNorm (momV C B x)) (gaussPair m n) := by
      have : Continuous fun x : Vec m × Vec n =>
          |resid Ah x| * eucNorm (momU C B x) * eucNorm (momV C B x) := by
        unfold resid eucNorm momU momV; fun_prop
      exact this.aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) hmeasG]
    have hge : ∀ x : Vec m × Vec n,
        ‖|resid Ah x| * eucNorm (momU C B x) * eucNorm (momV C B x)‖ₑ ^ ((2 : ℝ≥0∞).toReal)
          = ENNReal.ofReal (d2 x * a x * b x) := by
      intro x
      have hg0 : 0 ≤ |resid Ah x| * eucNorm (momU C B x) * eucNorm (momV C B x) :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
      rw [ENNReal.toReal_ofNat, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hg0,
        ENNReal.ofReal_rpow_of_nonneg hg0 (by norm_num), Real.rpow_two]
      congr 1
      simp only [hd2, ha, hb]
      rw [mul_pow, mul_pow, sq_abs]
    simp_rw [hge]
    calc (∫⁻ x, ENNReal.ofReal (d2 x * a x * b x) ∂(gaussPair m n)) ^ (1 / ((2 : ℝ≥0∞).toReal))
        ≤ (ENNReal.ofReal ((r ^ 2 * t) ^ 2)) ^ (1 / ((2 : ℝ≥0∞).toReal)) :=
          ENNReal.rpow_le_rpow hX (by simp)
      _ = ENNReal.ofReal ((15 : ℝ) ^ ((2 : ℝ) / 3) * CSig * γ) := by
          have h2 : (1 : ℝ) / ((2 : ℝ≥0∞).toReal) = (1 : ℝ) / ((2 : ℕ) : ℝ) := by norm_num
          rw [h2, de_root_ennreal _ (by positivity) 2 (by norm_num), hr2, ht]
          congr 1; ring

/-- `lem:app-de-moments`, part (iii), snapshot `cr-2026-10-23`. Verbatim from the frozen source
(`section.tex` l.879–896):

\begin{lemma}[Gaussian moment bounds]\label{lem:app-de-moments}
Let $z\sim\mathcal N(0,\Id_{\Nout})$, $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent, let $\Sigmaout,\Sigmain$ satisfy \cref{assum:app-setup-regime}, and
put $\mathsf u=\Sigmaout^{1/2}z/\sqrt B$, $\mathsf v=\Sigmain^{1/2}w/\sqrt B$,
$\mathsf N=\norm{\mathsf u}^2+\norm{\mathsf v}^2$ and $d=z^\T\Ahat w$. Then
for every integer $p\ge1$
\[
\begin{gathered}
\norm{\mathsf N}_p\le2C_\Sigma\gamma_\star\big((2p-1)!!\big)^{1/p},\qquad
\norm{d}_{2p}\le\big((2p-1)!!\big)^{1/p},\\
\big\|\abs d\,\norm{\mathsf u}\norm{\mathsf v}\big\|_2\le 15^{2/3}\,C_\Sigma\gamma_\star\le 7\,C_\Sigma\gamma_\star .
\end{gathered}
\]
Also, for any symmetric $A\in\R^{\Nout\times\Nout}$,
\[
\EE[z^\T Az]=\Tr A,\qquad \Var(z^\T Az)=2\norm{A}_\F^2 .
\]
\end{lemma}
-/
theorem lem_app_de_moments_iii {m n : ℕ} (C : Covariances m n) (B : ℕ) (γ CSig : ℝ)
    (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) (hγ : 0 ≤ γ)
    (hC : opNorm C.Sout ≤ CSig ∧ opNorm C.Sin ≤ CSig) (Ah : Mat m n) (hA : fro Ah = 1) :
    eLpNorm (fun x => |resid Ah x| * eucNorm (momU C B x) * eucNorm (momV C B x)) 2
        (gaussPair m n) ≤ ENNReal.ofReal ((15 : ℝ) ^ ((2 : ℝ) / 3) * CSig * γ) ∧
      (15 : ℝ) ^ ((2 : ℝ) / 3) * CSig * γ ≤ 7 * CSig * γ := by
  refine ⟨de_iii_fst C B γ CSig hdim hC Ah hA, ?_⟩
  have hC0 : 0 ≤ CSig := le_trans (norm_nonneg _) hC.1
  have h15 : (15 : ℝ) ^ ((2 : ℝ) / 3) ≤ 7 := by
    have h1 : (15 : ℝ) ^ ((2 : ℝ) / 3) = ((15 : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_mul (by norm_num)]; norm_num
    have h2 : (7 : ℝ) = ((7 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_mul (by norm_num)]; norm_num
    rw [h1, h2]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    norm_num
  nlinarith [mul_nonneg hC0 hγ]

/-- `lem:app-de-moments`, part (iv), snapshot `cr-2026-10-23`. Verbatim from the frozen source
(`section.tex` l.879–896):

\begin{lemma}[Gaussian moment bounds]\label{lem:app-de-moments}
Let $z\sim\mathcal N(0,\Id_{\Nout})$, $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent, let $\Sigmaout,\Sigmain$ satisfy \cref{assum:app-setup-regime}, and
put $\mathsf u=\Sigmaout^{1/2}z/\sqrt B$, $\mathsf v=\Sigmain^{1/2}w/\sqrt B$,
$\mathsf N=\norm{\mathsf u}^2+\norm{\mathsf v}^2$ and $d=z^\T\Ahat w$. Then
for every integer $p\ge1$
\[
\begin{gathered}
\norm{\mathsf N}_p\le2C_\Sigma\gamma_\star\big((2p-1)!!\big)^{1/p},\qquad
\norm{d}_{2p}\le\big((2p-1)!!\big)^{1/p},\\
\big\|\abs d\,\norm{\mathsf u}\norm{\mathsf v}\big\|_2\le 15^{2/3}\,C_\Sigma\gamma_\star\le 7\,C_\Sigma\gamma_\star .
\end{gathered}
\]
Also, for any symmetric $A\in\R^{\Nout\times\Nout}$,
\[
\EE[z^\T Az]=\Tr A,\qquad \Var(z^\T Az)=2\norm{A}_\F^2 .
\]
\end{lemma}
-/
theorem lem_app_de_moments_iv {m : ℕ} (A : Mat m m) (hA : A.IsSymm) :
    ∫ z, dotProduct z (Matrix.mulVec A z) ∂(Muon.Foundations.stdGaussianPi m) =
      Matrix.trace A := by
  have e : ∀ z : Vec m, dotProduct z (Matrix.mulVec A z) = ∑ i, ∑ j, z i * A i j * z j := by
    intro z
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  exact Muon.Foundations.stdGaussianPi_quadratic_mean m A

/-- `lem:app-de-moments`, part (v), snapshot `cr-2026-10-23`. Verbatim from the frozen source
(`section.tex` l.879–896):

\begin{lemma}[Gaussian moment bounds]\label{lem:app-de-moments}
Let $z\sim\mathcal N(0,\Id_{\Nout})$, $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent, let $\Sigmaout,\Sigmain$ satisfy \cref{assum:app-setup-regime}, and
put $\mathsf u=\Sigmaout^{1/2}z/\sqrt B$, $\mathsf v=\Sigmain^{1/2}w/\sqrt B$,
$\mathsf N=\norm{\mathsf u}^2+\norm{\mathsf v}^2$ and $d=z^\T\Ahat w$. Then
for every integer $p\ge1$
\[
\begin{gathered}
\norm{\mathsf N}_p\le2C_\Sigma\gamma_\star\big((2p-1)!!\big)^{1/p},\qquad
\norm{d}_{2p}\le\big((2p-1)!!\big)^{1/p},\\
\big\|\abs d\,\norm{\mathsf u}\norm{\mathsf v}\big\|_2\le 15^{2/3}\,C_\Sigma\gamma_\star\le 7\,C_\Sigma\gamma_\star .
\end{gathered}
\]
Also, for any symmetric $A\in\R^{\Nout\times\Nout}$,
\[
\EE[z^\T Az]=\Tr A,\qquad \Var(z^\T Az)=2\norm{A}_\F^2 .
\]
\end{lemma}
-/
theorem lem_app_de_moments_v {m : ℕ} (A : Mat m m) (hA : A.IsSymm) :
    variance (fun z : Vec m => dotProduct z (Matrix.mulVec A z))
        (Muon.Foundations.stdGaussianPi m) =
      2 * fro A ^ 2 := by
  have e : ∀ z : Vec m, dotProduct z (Matrix.mulVec A z) = ∑ i, ∑ j, z i * A i j * z j := by
    intro z
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hm : Measurable (fun z : Vec m => ∑ i, ∑ j, z i * A i j * z j) := by fun_prop
  have hmean := Muon.Foundations.stdGaussianPi_quadratic_mean m A
  have hvar := Muon.Foundations.stdGaussianPi_quadratic_variance m A hA
  have hsym : ∀ i j, A j i = A i j := fun i j => by
    have h := congrFun (congrFun hA i) j
    rw [Matrix.transpose_apply] at h
    exact h
  have hfro : fro A ^ 2 = (A * A).trace := by
    unfold fro
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym i j]
    ring
  simp_rw [e]
  rw [variance_eq_integral hm.aemeasurable]
  simp only [hmean]
  rw [hvar, hfro]

/-! ## Bessel bounds (`lem:app-de-bessel`) -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

section DeBesselHelpers
open Muon.Foundations

private lemma de_gmono {n k : ℕ} (c : Fin k → Fin n) :
    Integrable (fun z : Fin n → ℝ => ∏ r : Fin k, z (c r)) (stdGaussianPi n) := by
  have hprod : (fun z : Fin n → ℝ => ∏ r : Fin k, z (c r))
      = fun z : Fin n → ℝ => ∏ i : Fin n, (fun (x : ℝ) => x ^ Fintype.card {r // c r = i}) (z i) := by
    funext z
    rw [← Fintype.prod_fiberwise c (fun r => z (c r))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_congr rfl (fun (r : {r // c r = i}) _ => by rw [r.2]), Finset.prod_const,
      Finset.card_univ]
  rw [hprod]
  unfold stdGaussianPi
  exact Integrable.fintype_prod (fun i => gaussian_integrable_pow _)

private lemma de_gtwo {n : ℕ} (p q : Fin n) :
    Integrable (fun z : Fin n → ℝ => z p * z q) (stdGaussianPi n) := by
  have h := de_gmono (n := n) ![p, q]
  simpa [Fin.prod_univ_two] using h

private lemma de_gfour {n : ℕ} (p q r s : Fin n) :
    Integrable (fun z : Fin n → ℝ => z p * z q * z r * z s) (stdGaussianPi n) := by
  have h := de_gmono (n := n) ![p, q, r, s]
  simpa [Fin.prod_univ_four] using h

private lemma de_m2 {n : ℕ} (p q : Fin n) :
    ∫ z, z p * z q ∂(stdGaussianPi n) = if p = q then 1 else 0 := by
  have := gaussian_weighted_linear_moment n (Pi.single p 1) q
  simp only [single_dotProduct, one_mul] at this
  rw [this]
  simp [Pi.single_apply, eq_comm]

private lemma de_m4 {n : ℕ} (i j k l : Fin n) :
    ∫ z, z i * z j * z k * z l ∂(stdGaussianPi n)
      = (if i = j then 1 else 0) * (if k = l then 1 else 0)
        + (if i = k then 1 else 0) * (if j = l then 1 else 0)
        + (if i = l then 1 else 0) * (if j = k then 1 else 0) := by
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a b =>
    ((if a = k ∧ b = l then 1 else 0) + (if a = l ∧ b = k then 1 else 0)) / 2 with hM
  have hMs : Mᵀ = M := by
    ext a b; simp only [hM, Matrix.transpose_apply, Matrix.of_apply]
    rw [add_comm]; congr 1 <;> simp only [and_comm]
  have := gaussian_quartic_covariance n 1 M 1 (by simp) hMs (stdGaussianPi n) id
    (by simp) aemeasurable_id i j
  have hs : ∀ (f : Fin n → Fin n → ℝ) (p q : Fin n),
      ∑ a, ∑ b, f a b * (if a = p ∧ b = q then (1:ℝ) else 0) = f p q := by
    intro f p q; simp [ite_and, mul_ite]
  have hq : ∀ z : Fin n → ℝ, z ⬝ᵥ (M *ᵥ z) = z k * z l := by
    intro z
    have h1 : z ⬝ᵥ (M *ᵥ z) = (∑ a, ∑ b, (z a * z b) * (if a = k ∧ b = l then (1:ℝ) else 0)) / 2
        + (∑ a, ∑ b, (z a * z b) * (if a = l ∧ b = k then (1:ℝ) else 0)) / 2 := by
      simp only [hM, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum, Finset.sum_div,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [h1, hs, hs]; ring
  have hint : ∀ z : Fin n → ℝ, id z i * id z j * (id z ⬝ᵥ (M *ᵥ z)) = z i * z j * z k * z l := by
    intro z; simp only [id, hq]; ring
  have e : ∫ z, z i * z j * z k * z l ∂(stdGaussianPi n)
      = ∫ w, id w i * id w j * (id w ⬝ᵥ (M *ᵥ id w)) ∂(stdGaussianPi n) :=
    integral_congr_ae (Eventually.of_forall fun z => (hint z).symm)
  rw [e, this]
  simp [hM, Matrix.trace, Matrix.mul_apply, Matrix.one_apply]
  have ht : ∑ a : Fin n, (((if a = k ∧ a = l then (1:ℝ) else 0) + if a = l ∧ a = k then 1 else 0) / 2)
      = if k = l then 1 else 0 := by
    by_cases h : k = l
    · subst h; simp
    · have : ∀ a : Fin n, ¬(a = k ∧ a = l) := fun a ha => h (ha.1.symm.trans ha.2)
      have h2 : ∀ a : Fin n, ¬(a = l ∧ a = k) := fun a ha => h (ha.2.symm.trans ha.1)
      simp [this, h2, h]
  rw [ht]
  simp only [ite_and]
  split_ifs <;> norm_num

private lemma de_gfam1_memLp (m n : ℕ) (a : Fin m × Fin n) :
    MemLp (fun x : Vec m × Vec n => x.1 a.1 * x.2 a.2) 2 (gaussPair m n) := by
  have hm : Measurable (fun x : Vec m × Vec n => x.1 a.1 * x.2 a.2) := by fun_prop
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have h := Integrable.mul_prod (de_gtwo a.1 a.1) (de_gtwo a.2 a.2)
  unfold gaussPair
  convert h using 2 with x
  ring

private lemma de_gfam1_gram (m n : ℕ) (a b : Fin m × Fin n) :
    ∫ x : Vec m × Vec n, (x.1 a.1 * x.2 a.2) * (x.1 b.1 * x.2 b.2) ∂(gaussPair m n)
      = if a = b then 1 else 0 := by
  have h := integral_prod_mul (μ := stdGaussianPi m) (ν := stdGaussianPi n)
    (fun z : Vec m => z a.1 * z b.1) (fun w : Vec n => w a.2 * w b.2)
  unfold gaussPair
  have e : ∀ x : Vec m × Vec n, (x.1 a.1 * x.2 a.2) * (x.1 b.1 * x.2 b.2)
      = (x.1 a.1 * x.1 b.1) * (x.2 a.2 * x.2 b.2) := fun x => by ring
  simp only [e]
  rw [h, de_m2, de_m2]
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  by_cases h1 : a1 = b1 <;> by_cases h2 : a2 = b2 <;> simp [h1, h2]

private lemma de_gsq_memLp (d : ℕ) (a : Fin d × Fin d) :
    MemLp (fun z : Vec d => z a.1 * z a.2 - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2
      (stdGaussianPi d) := by
  have hm : Measurable (fun z : Vec d => z a.1 * z a.2 - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) := by
    fun_prop
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  set c : ℝ := (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2
  have e : (fun z : Vec d => (z a.1 * z a.2 - c) ^ 2)
      = fun z => z a.1 * z a.2 * z a.1 * z a.2 - (2 * c) * (z a.1 * z a.2) + c ^ 2 := by
    funext z; ring
  rw [e]
  exact ((de_gfour _ _ _ _).sub ((de_gtwo _ _).const_mul _)).add (integrable_const _)

private lemma de_gsq_gram (d : ℕ) (a b : Fin d × Fin d) :
    ∫ z : Vec d, (z a.1 * z a.2 - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2)
        * (z b.1 * z b.2 - (1 : Matrix (Fin d) (Fin d) ℝ) b.1 b.2) ∂(stdGaussianPi d)
      = (if a.1 = b.1 then 1 else 0) * (if a.2 = b.2 then 1 else 0)
        + (if a.1 = b.2 then 1 else 0) * (if a.2 = b.1 then 1 else 0) := by
  obtain ⟨i, k⟩ := a
  obtain ⟨j, l⟩ := b
  simp only [Matrix.one_apply]
  have e : (fun z : Vec d => (z i * z k - (if i = k then (1:ℝ) else 0))
        * (z j * z l - (if j = l then (1:ℝ) else 0)))
      = fun z => z i * z k * z j * z l - (if j = l then (1:ℝ) else 0) * (z i * z k)
          - (if i = k then (1:ℝ) else 0) * (z j * z l) + (if i = k then (1:ℝ) else 0) * (if j = l then (1:ℝ) else 0) := by
    funext z; ring
  rw [e]
  rw [integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul, de_m4, de_m2, de_m2]
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  all_goals first
    | exact de_gfour i k j l
    | exact (de_gtwo i k).const_mul _
    | exact (de_gtwo j l).const_mul _
    | exact (de_gfour i k j l).sub ((de_gtwo i k).const_mul _)
    | exact ((de_gfour i k j l).sub ((de_gtwo i k).const_mul _)).sub ((de_gtwo j l).const_mul _)
    | exact integrable_const _

private lemma de_core_trunc {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (φ : ι → Ω → ℝ) (hφ : ∀ a, MemLp (φ a) 2 P) (Γ : ι → ι → ℝ)
    (hΓ : ∀ a b, condExp G P (fun w => φ a w * φ b w) =ᵐ[P] fun _ => Γ a b)
    (e : Ω → ℝ) (he : MemLp e 2 P) (t : ℝ) (N : ℕ) :
    ∀ᵐ ζ ∂P, (∑ a, condExp G P (fun w => φ a w * e w) ζ ^ 2 ≤ N) →
      0 ≤ condExp G P (fun w => e w ^ 2) ζ
        - 2 * t * ∑ a, condExp G P (fun w => φ a w * e w) ζ ^ 2
        + t ^ 2 * ∑ a, ∑ b, Γ a b * condExp G P (fun w => φ a w * e w) ζ
            * condExp G P (fun w => φ b w * e w) ζ := by
  classical
  set c : ι → Ω → ℝ := fun a => condExp G P (fun w => φ a w * e w) with hc
  have hφe : ∀ a, Integrable (fun w => φ a w * e w) P := fun a => by
    have := (hφ a).integrable_mul he
    exact this
  have hφφ : ∀ a b, Integrable (fun w => φ a w * φ b w) P := fun a b => (hφ a).integrable_mul (hφ b)
  have he2 : Integrable (fun w => e w ^ 2) P := by
    have := he.integrable_mul he
    convert this using 1
    funext w; simp [sq]
  have hcm : ∀ a, StronglyMeasurable[G] (c a) := fun a => stronglyMeasurable_condExp
  set S : Set Ω := {ζ | ∑ a, c a ζ ^ 2 ≤ N} with hS
  have hSm : MeasurableSet[G] S := by
    have : Measurable[G] (fun ζ => ∑ a, c a ζ ^ 2) :=
      Finset.measurable_sum _ (fun a _ => ((hcm a).measurable).pow_const 2)
    exact this measurableSet_Iic
  set b : ι → Ω → ℝ := fun a => S.indicator (c a) with hb
  have hbm : ∀ a, StronglyMeasurable[G] (b a) := fun a => (hcm a).indicator hSm
  have hbb : ∀ a w, ‖b a w‖ ≤ N + 1 := by
    intro a w
    by_cases h : w ∈ S
    · simp only [hb, Set.indicator_of_mem h]
      have h1 : c a w ^ 2 ≤ N := le_trans (Finset.single_le_sum (f := fun a => c a w ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ a)) h
      rw [Real.norm_eq_abs]
      nlinarith [sq_abs (c a w), abs_nonneg (c a w)]
    · simp [hb, Set.indicator_of_notMem h]; positivity
  have hbmΩ : ∀ a, StronglyMeasurable[mΩ] (b a) := fun a => (hbm a).mono hG
  -- pieces
  have hF1 : ∀ a, Integrable (fun w => b a w * (φ a w * e w)) P := fun a =>
    (hφe a).bdd_mul (hbmΩ a).aestronglyMeasurable (Eventually.of_forall (hbb a))
  have hF2 : ∀ a b', Integrable (fun w => (b a w * b b' w) * (φ a w * φ b' w)) P := fun a b' =>
    (hφφ a b').bdd_mul ((hbmΩ a).mul (hbmΩ b')).aestronglyMeasurable
      (Eventually.of_forall (fun w => by
        rw [norm_mul]
        have h1 := hbb a w
        have h2 := hbb b' w
        exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)))
  have hexp : ∀ w, (e w - t * ∑ a, b a w * φ a w) ^ 2
      = e w ^ 2 - (2 * t) * ∑ a, b a w * (φ a w * e w)
        + t ^ 2 * ∑ a, ∑ b', (b a w * b b' w) * (φ a w * φ b' w) := by
    intro w
    have : (∑ a, b a w * φ a w) ^ 2 = ∑ a, ∑ b', (b a w * b b' w) * (φ a w * φ b' w) := by
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b' _ => by ring
    have h2 : e w * ∑ a, b a w * φ a w = ∑ a, b a w * (φ a w * e w) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
    calc (e w - t * ∑ a, b a w * φ a w) ^ 2
        = e w ^ 2 - 2 * t * (e w * ∑ a, b a w * φ a w) + t ^ 2 * (∑ a, b a w * φ a w) ^ 2 := by ring
      _ = _ := by rw [this, h2]
  have hnn : 0 ≤ᵐ[P] condExp G P (fun w => (e w - t * ∑ a, b a w * φ a w) ^ 2) :=
    condExp_nonneg (Eventually.of_forall fun w => sq_nonneg _)
  -- linearity
  have hI1 : Integrable (∑ a, fun w => b a w * (φ a w * e w)) P :=
    integrable_finsetSum' _ (fun a _ => hF1 a)
  have hI2 : Integrable (∑ a, ∑ b', fun w => (b a w * b b' w) * (φ a w * φ b' w)) P :=
    integrable_finsetSum' _ (fun a _ => integrable_finsetSum' _ (fun b' _ => hF2 a b'))
  have hfun : (fun w => (e w - t * ∑ a, b a w * φ a w) ^ 2)
      = (fun w => e w ^ 2) - (2 * t) • (∑ a, fun w => b a w * (φ a w * e w))
        + (t ^ 2) • (∑ a, ∑ b', fun w => (b a w * b b' w) * (φ a w * φ b' w)) := by
    funext w
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    exact hexp w
  have hlin : condExp G P (fun w => (e w - t * ∑ a, b a w * φ a w) ^ 2) =ᵐ[P]
      condExp G P (fun w => e w ^ 2)
        - (2 * t) • (∑ a, condExp G P (fun w => b a w * (φ a w * e w)))
        + (t ^ 2) • (∑ a, ∑ b', condExp G P (fun w => (b a w * b b' w) * (φ a w * φ b' w))) := by
    rw [hfun]
    have h0 := condExp_add ((he2.sub (hI1.smul (2 * t)))) (hI2.smul (t ^ 2)) G
    have h1 := condExp_sub he2 (hI1.smul (2 * t)) G
    have h2 := condExp_smul (𝕜 := ℝ) (μ := P) (2 * t) (∑ a, fun w => b a w * (φ a w * e w)) G
    have h3 := condExp_smul (𝕜 := ℝ) (μ := P) (t ^ 2)
      (∑ a, ∑ b', fun w => (b a w * b b' w) * (φ a w * φ b' w)) G
    have h4 := condExp_finsetSum (μ := P) (s := Finset.univ) (fun a _ => hF1 a) G
    have h5 : condExp G P (∑ a, ∑ b', fun w => (b a w * b b' w) * (φ a w * φ b' w)) =ᵐ[P]
        ∑ a, ∑ b', condExp G P (fun w => (b a w * b b' w) * (φ a w * φ b' w)) := by
      have := condExp_finsetSum (μ := P) (s := Finset.univ)
        (f := fun a => ∑ b', fun w => (b a w * b b' w) * (φ a w * φ b' w))
        (fun a _ => integrable_finsetSum' _ (fun b' _ => hF2 a b')) G
      refine this.trans ?_
      have hall : ∀ᵐ w ∂P, ∀ a, condExp G P (∑ b', fun w => (b a w * b b' w) * (φ a w * φ b' w)) w
          = ∑ b', condExp G P (fun w => (b a w * b b' w) * (φ a w * φ b' w)) w := by
        rw [ae_all_iff]; intro a
        exact (condExp_finsetSum (μ := P) (s := Finset.univ)
          (f := fun b' => fun w => (b a w * b b' w) * (φ a w * φ b' w))
          (fun b' _ => hF2 a b') G).mono fun w hw => by simpa [Finset.sum_apply] using hw
      filter_upwards [hall] with w hw
      simp only [Finset.sum_apply]
      exact Finset.sum_congr rfl fun a _ => hw a
    filter_upwards [h0, h1, h2, h3, h4, h5] with w w0 w1 w2 w3 w4 w5
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at w0 w1 w2 w3 w5 ⊢
    rw [w0, w1, w2, w3, w5, w4]
  have hpull1 : ∀ᵐ ζ ∂P, ∀ a, condExp G P (fun w => b a w * (φ a w * e w)) ζ = b a ζ * c a ζ := by
    rw [ae_all_iff]; intro a
    exact (condExp_mul_of_stronglyMeasurable_left (μ := P) (hbm a)
      (hF1 a) (hφe a))
  have hpull2 : ∀ᵐ ζ ∂P, ∀ a b', condExp G P (fun w => (b a w * b b' w) * (φ a w * φ b' w)) ζ
      = (b a ζ * b b' ζ) * Γ a b' := by
    rw [ae_all_iff]; intro a
    rw [ae_all_iff]; intro b'
    have h1 := condExp_mul_of_stronglyMeasurable_left (μ := P)
      (f := fun w => b a w * b b' w) (g := fun w => φ a w * φ b' w) ((hbm a).mul (hbm b'))
      (hF2 a b') (hφφ a b')
    filter_upwards [h1, hΓ a b'] with ζ w1 w2
    have w1' : condExp G P (fun w => (b a w * b b' w) * (φ a w * φ b' w)) ζ
        = (b a ζ * b b' ζ) * condExp G P (fun w => φ a w * φ b' w) ζ := w1
    rw [w1', w2]
  filter_upwards [hlin, hnn, hpull1, hpull2] with ζ w1 w2 w3 w4 hζ
  have hbc : ∀ a, b a ζ = c a ζ := fun a => by simp [hb, Set.indicator_of_mem (show ζ ∈ S from hζ)]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at w1
  rw [w1] at w2
  simp only [w3, w4, hbc] at w2
  have e1 : ∑ a, c a ζ * c a ζ = ∑ a, c a ζ ^ 2 := Finset.sum_congr rfl fun a _ => by ring
  have e2 : ∑ a, ∑ b', c a ζ * c b' ζ * Γ a b' = ∑ a, ∑ b', Γ a b' * c a ζ * c b' ζ :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b' _ => by ring
  rw [e1, e2] at w2
  exact w2

private lemma de_ae_nat {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {p : Ω → ℕ → Prop} (h : ∀ N, ∀ᵐ ζ ∂P, p ζ N) :
    ∀ᵐ ζ ∂P, ∀ N, p ζ N := ae_all_iff.2 h

private lemma de_core {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (φ : ι → Ω → ℝ) (hφ : ∀ a, MemLp (φ a) 2 P) (Γ : ι → ι → ℝ)
    (hΓ : ∀ a b, condExp G P (fun w => φ a w * φ b w) =ᵐ[P] fun _ => Γ a b)
    (e : Ω → ℝ) (he : MemLp e 2 P) (t : ℝ) :
    ∀ᵐ ζ ∂P, 2 * t * ∑ a, condExp G P (fun w => φ a w * e w) ζ ^ 2
        - t ^ 2 * ∑ a, ∑ b, Γ a b * condExp G P (fun w => φ a w * e w) ζ
            * condExp G P (fun w => φ b w * e w) ζ
      ≤ condExp G P (fun w => e w ^ 2) ζ := by
  have h : ∀ᵐ ζ ∂P, ∀ N : ℕ, (∑ a, condExp G P (fun w => φ a w * e w) ζ ^ 2 ≤ N) →
      0 ≤ condExp G P (fun w => e w ^ 2) ζ
        - 2 * t * ∑ a, condExp G P (fun w => φ a w * e w) ζ ^ 2
        + t ^ 2 * ∑ a, ∑ b, Γ a b * condExp G P (fun w => φ a w * e w) ζ
            * condExp G P (fun w => φ b w * e w) ζ := by
    exact de_ae_nat (fun N => de_core_trunc P G hG φ hφ Γ hΓ e he t N)
  filter_upwards [h] with ζ hζ
  have := hζ ⌈∑ a, condExp G P (fun w => φ a w * e w) ζ ^ 2⌉₊ (Nat.le_ceil _)
  linarith

private lemma de_indep_mk {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n : ℕ} {X : Ω → Vec m × Vec n} {P : Measure Ω} (hXae : AEMeasurable X P)
    {G : MeasurableSpace Ω}
    (hind : Indep (MeasurableSpace.comap X inferInstance) G P) :
    Indep (MeasurableSpace.comap (hXae.mk X) inferInstance) G P := by
  rw [Indep_iff] at hind ⊢
  intro t1 t2 h1 h2
  obtain ⟨S, hS, rfl⟩ := h1
  have hae : (hXae.mk X) ⁻¹' S =ᵐ[P] X ⁻¹' S := by
    filter_upwards [hXae.ae_eq_mk] with w hw
    simp [Set.preimage, hw]
  have := hind (X ⁻¹' S) t2 ⟨S, hS, rfl⟩ h2
  rw [measure_congr (hae.inter (EventuallyEq.refl _ t2)), measure_congr hae]
  exact this

private lemma de_cond_const {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hXae : AEMeasurable X P)
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X inferInstance) G P)
    (g : Vec m × Vec n → ℝ) (hg : Measurable g) :
    condExp G P (fun w => g (X w)) =ᵐ[P] fun _ => ∫ w, g (X w) ∂P := by
  have hXm : @Measurable Ω _ mΩ _ (hXae.mk X) := hXae.measurable_mk
  have hind' := de_indep_mk hXae hind
  have hae : (fun w => g (X w)) =ᵐ[P] fun w => g (hXae.mk X w) := by
    filter_upwards [hXae.ae_eq_mk] with w hw
    simp [hw]
  have h1 := condExp_indep_eq (μ := P) hXm.comap_le hG
    (f := fun w => g (hXae.mk X w))
    ((hg.comp (comap_measurable (hXae.mk X))).stronglyMeasurable) hind'
  refine (condExp_congr_ae hae).trans (h1.trans ?_)
  refine Eventually.of_forall fun w => ?_
  exact integral_congr_ae (hae.symm)

private lemma de_aem {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) : AEMeasurable X P := by
  by_contra hne
  have h0 := Measure.map_of_not_aemeasurable_of_ne_zero hne (IsProbabilityMeasure.ne_zero P)
  have hd := hX.symm.trans h0
  obtain ⟨x0, hd⟩ : ∃ x0 : Vec m × Vec n, gaussPair m n = Measure.dirac x0 := ⟨_, hd⟩
  have key : ∀ c : Vec m × Vec n → ℝ, Measurable c →
      (gaussPair m n).map c = gaussianReal 0 1 → False := by
    intro c hc hmap
    have h1 : (gaussPair m n).map c {c x0} = 1 := by
      rw [Measure.map_apply hc (measurableSet_singleton _), hd, Measure.dirac_apply' _
        (hc (measurableSet_singleton _))]
      simp
    rw [hmap] at h1
    have := noAtoms_gaussianReal (μ := 0) (v := 1) one_ne_zero
    rw [measure_singleton] at h1
    exact zero_ne_one h1
  have hfst : (gaussPair m n).map Prod.fst = Muon.Foundations.stdGaussianPi m := by
    unfold gaussPair
    rw [Measure.map_fst_prod]; simp
  have hsnd : (gaussPair m n).map Prod.snd = Muon.Foundations.stdGaussianPi n := by
    unfold gaussPair
    rw [Measure.map_snd_prod]; simp
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hm; subst hn
      exact hne (measurable_of_subsingleton_codomain X).aemeasurable
    · refine key (fun x => x.2 ⟨0, hn⟩) ((measurable_pi_apply _).comp measurable_snd) ?_
      have := Muon.Foundations.stdGaussianPi_map_coord n ⟨0, hn⟩
      rw [← this, ← hsnd, Measure.map_map (measurable_pi_apply _) measurable_snd]
      rfl
  · refine key (fun x => x.1 ⟨0, hm⟩) ((measurable_pi_apply _).comp measurable_fst) ?_
    have := Muon.Foundations.stdGaussianPi_map_coord m ⟨0, hm⟩
    rw [← this, ← hfst, Measure.map_map (measurable_pi_apply _) measurable_fst]
    rfl

private lemma de_family {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n)
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X inferInstance) G P)
    {ι : Type*} (f : ι → Vec m × Vec n → ℝ) (hfm : ∀ a, Measurable (f a))
    (hf2 : ∀ a, MemLp (f a) 2 (gaussPair m n)) :
    (∀ a, MemLp (fun w => f a (X w)) 2 P) ∧
    ∀ a b, condExp G P (fun w => f a (X w) * f b (X w)) =ᵐ[P]
      fun _ => ∫ x, f a x * f b x ∂(gaussPair m n) := by
  have hXae : AEMeasurable X P := de_aem P X hX
  refine ⟨fun a => ?_, fun a b => ?_⟩
  · have hg : MemLp (f a) 2 (@Measure.map Ω (Vec m × Vec n) mΩ _ X P) := by rw [hX]; exact hf2 a
    exact hg.comp_of_map hXae
  · have h := de_cond_const P X hXae G hG hind (fun x => f a x * f b x) ((hfm a).mul (hfm b))
    refine h.trans (Eventually.of_forall fun w => ?_)
    change ∫ w, f a (X w) * f b (X w) ∂P = ∫ x, f a x * f b x ∂(gaussPair m n)
    rw [← hX]
    exact (integral_map (φ := X) hXae (f := fun x => f a x * f b x) ((hfm a).mul (hfm b)).aestronglyMeasurable).symm

private lemma de_real_i {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n)
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X inferInstance) G P)
    (e : Ω → ℝ) (he : MemLp e 2 P) :
    ∀ᵐ ζ ∂P, ∑ i : Fin m, ∑ l : Fin n,
        (condExp G P (fun w => (X w).1 i * (X w).2 l * e w) ζ) ^ 2
      ≤ condExp G P (fun w => e w ^ 2) ζ := by
  obtain ⟨hφ, hΓ⟩ := de_family P X hX G hG hind
    (fun (a : Fin m × Fin n) (x : Vec m × Vec n) => x.1 a.1 * x.2 a.2) (fun a => by fun_prop)
    (de_gfam1_memLp m n)
  have hΓ' : ∀ a b : Fin m × Fin n, condExp G P
      (fun w => ((X w).1 a.1 * (X w).2 a.2) * ((X w).1 b.1 * (X w).2 b.2)) =ᵐ[P]
        fun _ => if a = b then (1:ℝ) else 0 := fun a b => by
    have := hΓ a b
    rw [de_gfam1_gram] at this
    exact this
  have h := de_core P G hG (fun (a : Fin m × Fin n) w => (X w).1 a.1 * (X w).2 a.2) hφ
    (fun a b => if a = b then 1 else 0) hΓ' e he 1
  filter_upwards [h] with ζ hζ
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Fintype.sum_prod_type, one_pow, one_mul] at hζ ⊢
  simp only [← sq] at hζ
  linarith

private lemma de_symsum (d : ℕ) (c : Fin d × Fin d → ℝ) (hs : ∀ i k, c (i, k) = c (k, i)) :
    ∑ a : Fin d × Fin d, ∑ b : Fin d × Fin d,
      (((if a.1 = b.1 then (1:ℝ) else 0) * (if a.2 = b.2 then 1 else 0)
        + (if a.1 = b.2 then 1 else 0) * (if a.2 = b.1 then 1 else 0)) * c a * c b)
      = 2 * ∑ a : Fin d × Fin d, c a ^ 2 := by
  simp only [Fintype.sum_prod_type, add_mul, Finset.sum_add_distrib]
  have h1 : ∑ i : Fin d, ∑ k : Fin d, ∑ j : Fin d, ∑ l : Fin d,
      (if i = j then (1:ℝ) else 0) * (if k = l then 1 else 0) * c (i, k) * c (j, l)
      = ∑ i : Fin d, ∑ k : Fin d, c (i, k) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp [mul_assoc, sq]
  have h2 : ∑ i : Fin d, ∑ k : Fin d, ∑ j : Fin d, ∑ l : Fin d,
      (if i = l then (1:ℝ) else 0) * (if k = j then 1 else 0) * c (i, k) * c (j, l)
      = ∑ i : Fin d, ∑ k : Fin d, c (i, k) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp [mul_assoc, sq, hs i k]
  rw [h1, h2]; ring

private lemma de_real_sq {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n)
    (π : Vec m × Vec n → Vec d) (hπ : Measurable π)
    (hmap : (gaussPair m n).map π = stdGaussianPi d)
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X inferInstance) G P)
    (e : Ω → ℝ) (he : MemLp e 2 P) :
    ∀ᵐ ζ ∂P, ∑ i : Fin d, ∑ k : Fin d,
        (condExp G P (fun w => ((π (X w)) i * (π (X w)) k
            - (1 : Matrix (Fin d) (Fin d) ℝ) i k) * e w) ζ) ^ 2
      ≤ 2 * condExp G P (fun w => e w ^ 2) ζ := by
  set f : Fin d × Fin d → Vec m × Vec n → ℝ := fun a x =>
    (π x) a.1 * (π x) a.2 - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2 with hf
  have hfm : ∀ a, Measurable (f a) := fun a => by
    have : Measurable (fun x : Vec m × Vec n => (π x) a.1 * (π x) a.2
      - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) := by
      have := (measurable_pi_apply a.1).comp hπ
      have h2 := (measurable_pi_apply a.2).comp hπ
      exact (this.mul h2).sub measurable_const
    exact this
  have hf2 : ∀ a, MemLp (f a) 2 (gaussPair m n) := fun a => by
    have h1 : MemLp (fun z : Vec d => z a.1 * z a.2 - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2
        (Measure.map π (gaussPair m n)) := by rw [hmap]; exact de_gsq_memLp d a
    exact h1.comp_of_map hπ.aemeasurable
  obtain ⟨hφ, hΓ⟩ := de_family P X hX G hG hind f hfm hf2
  have hgram : ∀ a b, ∫ x, f a x * f b x ∂(gaussPair m n)
      = (if a.1 = b.1 then (1:ℝ) else 0) * (if a.2 = b.2 then 1 else 0)
        + (if a.1 = b.2 then 1 else 0) * (if a.2 = b.1 then 1 else 0) := fun a b => by
    rw [← de_gsq_gram d a b, ← hmap]
    exact (integral_map hπ.aemeasurable (f := fun z : Vec d =>
      (z a.1 * z a.2 - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2)
        * (z b.1 * z b.2 - (1 : Matrix (Fin d) (Fin d) ℝ) b.1 b.2))
      (((((measurable_pi_apply a.1).mul (measurable_pi_apply a.2)).sub measurable_const).mul
        (((measurable_pi_apply b.1).mul (measurable_pi_apply b.2)).sub
          measurable_const)).aestronglyMeasurable)).symm
  have hΓ' : ∀ a b, condExp G P (fun w => f a (X w) * f b (X w)) =ᵐ[P]
      fun _ => (if a.1 = b.1 then (1:ℝ) else 0) * (if a.2 = b.2 then 1 else 0)
        + (if a.1 = b.2 then 1 else 0) * (if a.2 = b.1 then 1 else 0) := fun a b => by
    have := hΓ a b
    rw [hgram] at this
    exact this
  have h := de_core P G hG (fun a w => f a (X w)) hφ
    (fun a b => (if a.1 = b.1 then (1:ℝ) else 0) * (if a.2 = b.2 then 1 else 0)
        + (if a.1 = b.2 then 1 else 0) * (if a.2 = b.1 then 1 else 0)) hΓ' e he (1/2)
  filter_upwards [h] with ζ hζ
  set c : Fin d × Fin d → ℝ := fun a => condExp G P (fun w => f a (X w) * e w) ζ with hc
  have hs : ∀ i k, c (i, k) = c (k, i) := fun i k => by
    have hfun : (fun w => f (i, k) (X w) * e w) = fun w => f (k, i) (X w) * e w := by
      funext w
      by_cases h : i = k
      · subst h; rfl
      · have h' : ¬ k = i := fun h2 => h h2.symm
        simp only [hf, Matrix.one_apply, h, h', if_false]
        rw [mul_comm (π (X w) i)]
    show condExp G P (fun w => f (i, k) (X w) * e w) ζ = condExp G P (fun w => f (k, i) (X w) * e w) ζ
    rw [hfun]
  have hsum := de_symsum d c hs
  have hζ' : 2 * (1/2) * ∑ a, c a ^ 2 - (1/2) ^ 2 * ∑ a, ∑ b,
      ((if a.1 = b.1 then (1:ℝ) else 0) * (if a.2 = b.2 then 1 else 0)
        + (if a.1 = b.2 then 1 else 0) * (if a.2 = b.1 then 1 else 0)) * c a * c b
      ≤ condExp G P (fun w => e w ^ 2) ζ := hζ
  rw [hsum] at hζ'
  rw [Fintype.sum_prod_type] at hζ'
  show ∑ i : Fin d, ∑ k : Fin d, (c (i, k)) ^ 2 ≤ _
  linarith

private lemma de_lift {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝕜 : Type*} [RCLike 𝕜]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    {ι : Type*} [Fintype ι] (φ : ι → Ω → ℝ) (hφ : ∀ a, MemLp (φ a) 2 P)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hreal : ∀ e : Ω → ℝ, MemLp e 2 P → ∀ᵐ ζ ∂P,
      ∑ a, (condExp G P (fun w => φ a w * e w) ζ) ^ 2 ≤ κ * condExp G P (fun w => e w ^ 2) ζ)
    (e : Ω → 𝕜) (he : MemLp e 2 P) :
    ∀ᵐ ζ ∂P, Real.sqrt (∑ a, ‖condExp G P (fun w => ((φ a w : ℝ) : 𝕜) * e w) ζ‖ ^ 2)
      ≤ Real.sqrt κ * Real.sqrt (condExp G P (fun w => ‖e w‖ ^ 2) ζ) := by
  have hre : MemLp (fun w => RCLike.re (e w)) 2 P := he.re
  have him : MemLp (fun w => RCLike.im (e w)) 2 P := he.im
  have hfa : ∀ a, Integrable (fun w => ((φ a w : ℝ) : 𝕜) * e w) P := fun a => by
    have h : MemLp (fun w => (φ a w) • e w) 1 P := ((hφ a).smul he (r := 1))
    have h2 := memLp_one_iff_integrable.1 h
    convert h2 using 2 with w
    simp [RCLike.real_smul_eq_coe_mul]
  have hc : ∀ a, (fun ζ => RCLike.re (condExp G P (fun w => ((φ a w : ℝ) : 𝕜) * e w) ζ))
        =ᵐ[P] condExp G P (fun w => φ a w * RCLike.re (e w)) ∧
      (fun ζ => RCLike.im (condExp G P (fun w => ((φ a w : ℝ) : 𝕜) * e w) ζ))
        =ᵐ[P] condExp G P (fun w => φ a w * RCLike.im (e w)) := fun a => by
    constructor
    · have := (RCLike.reCLM (K := 𝕜)).comp_condExp_comm (m := G) (hfa a)
      refine this.trans (condExp_congr_ae (Eventually.of_forall fun w => ?_))
      simp [RCLike.re_ofReal_mul]
    · have := (RCLike.imCLM (K := 𝕜)).comp_condExp_comm (m := G) (hfa a)
      refine this.trans (condExp_congr_ae (Eventually.of_forall fun w => ?_))
      simp [RCLike.im_ofReal_mul]
  have hall : ∀ᵐ ζ ∂P, ∀ a,
      RCLike.re (condExp G P (fun w => ((φ a w : ℝ) : 𝕜) * e w) ζ)
        = condExp G P (fun w => φ a w * RCLike.re (e w)) ζ ∧
      RCLike.im (condExp G P (fun w => ((φ a w : ℝ) : 𝕜) * e w) ζ)
        = condExp G P (fun w => φ a w * RCLike.im (e w)) ζ := by
    rw [Filter.eventually_all]
    intro a
    filter_upwards [(hc a).1, (hc a).2] with ζ h1 h2
    exact ⟨h1, h2⟩
  have hsq : condExp G P (fun w => ‖e w‖ ^ 2) =ᵐ[P]
      fun ζ => condExp G P (fun w => RCLike.re (e w) ^ 2) ζ
        + condExp G P (fun w => RCLike.im (e w) ^ 2) ζ := by
    have hi1 : Integrable (fun w => RCLike.re (e w) ^ 2) P := by
      have := hre.integrable_mul hre
      convert this using 1; funext w; simp [sq]
    have hi2 : Integrable (fun w => RCLike.im (e w) ^ 2) P := by
      have := him.integrable_mul him
      convert this using 1; funext w; simp [sq]
    have := condExp_add hi1 hi2 G (μ := P)
    refine (condExp_congr_ae (Eventually.of_forall fun w => ?_)).trans this
    simp only [Pi.add_apply]
    rw [RCLike.norm_sq_eq_def]; ring
  filter_upwards [hall, hsq, hreal _ hre, hreal _ him] with ζ h1 h2 h3 h4
  have hS : ∑ a, ‖condExp G P (fun w => ((φ a w : ℝ) : 𝕜) * e w) ζ‖ ^ 2
      ≤ κ * condExp G P (fun w => ‖e w‖ ^ 2) ζ := by
    have : ∑ a, ‖condExp G P (fun w => ((φ a w : ℝ) : 𝕜) * e w) ζ‖ ^ 2
        = ∑ a, (condExp G P (fun w => φ a w * RCLike.re (e w)) ζ) ^ 2
          + ∑ a, (condExp G P (fun w => φ a w * RCLike.im (e w)) ζ) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [RCLike.norm_sq_eq_def, (h1 a).1, (h1 a).2]; ring
    rw [this, h2]
    nlinarith
  calc Real.sqrt (∑ a, ‖condExp G P (fun w => ((φ a w : ℝ) : 𝕜) * e w) ζ‖ ^ 2)
      ≤ Real.sqrt (κ * condExp G P (fun w => ‖e w‖ ^ 2) ζ) := Real.sqrt_le_sqrt hS
    _ = _ := Real.sqrt_mul hκ _

private lemma de_sq_memLp {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n)
    (π : Vec m × Vec n → Vec d) (hπ : Measurable π)
    (hmap : (gaussPair m n).map π = stdGaussianPi d) (a : Fin d × Fin d) :
    MemLp (fun w => (π (X w)) a.1 * (π (X w)) a.2
      - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2 P := by
  have h1 : MemLp (fun z : Vec d => z a.1 * z a.2 - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2
      (Measure.map π (gaussPair m n)) := by rw [hmap]; exact de_gsq_memLp d a
  have h2 := h1.comp_of_map hπ.aemeasurable
  have hg : MemLp (fun x : Vec m × Vec n => (π x) a.1 * (π x) a.2
      - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2 (@Measure.map Ω (Vec m × Vec n) mΩ _ X P) := by
    rw [hX]; exact h2
  exact hg.comp_of_map (de_aem P X hX)

end DeBesselHelpers

/-- `lem:app-de-bessel`, part (i), snapshot `cr-2026-10-23`. Verbatim from the frozen source
(`section.tex` l.945–956; `real or complex e` is `RCLike 𝕜`, and the conditional expectation
`𝔼_𝒢` is `condExp G P`):

\begin{lemma}[Bessel bounds]\label{lem:app-de-bessel}
Let $z\sim\mathcal N(0,\Id_{\Nout})$ and $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent of each other and of a $\sigma$-field $\mathcal G$, and let $e$ be
a real or complex random variable depending on $z$, $w$ and $\mathcal G$. Then
\begin{equation}\label{eqn:app-de-bessel}
\begin{gathered}
\norm{\EE_{\mathcal G}[(z\tensor w)\,e]}_\F\le\norm{e}_{2,\mathcal G},\qquad
\norm{\EE_{\mathcal G}[(z\tensor z-\Id)\,e]}_\F\le\sqrt2\,\norm{e}_{2,\mathcal G},\\
\norm{\EE_{\mathcal G}[(w\tensor w-\Id)\,e]}_\F\le\sqrt2\,\norm{e}_{2,\mathcal G}.
\end{gathered}
\end{equation}
\end{lemma}
-/
theorem lem_app_de_bessel_i {m n : ℕ} {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace 𝕜]
    [BorelSpace 𝕜] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Vec m × Vec n)
    (hX : P.map X = gaussPair m n) (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X inferInstance) G P)
    (e : Ω → 𝕜) (he : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e)
    (he2 : MemLp e 2 P) :
    ∀ᵐ ζ ∂P,
      Real.sqrt (∑ i, ∑ l, ‖condExp G P
          (fun ω' => (((X ω').1 i * (X ω').2 l : ℝ) : 𝕜) * e ω') ζ‖ ^ 2) ≤
        Real.sqrt (condExp G P (fun ω' => ‖e ω'‖ ^ 2) ζ) := by
  have hφ : ∀ a : Fin m × Fin n, MemLp (fun w => (X w).1 a.1 * (X w).2 a.2) 2 P :=
    (de_family P X hX G hG hind
      (fun (a : Fin m × Fin n) (x : Vec m × Vec n) => x.1 a.1 * x.2 a.2) (fun a => by fun_prop)
      (de_gfam1_memLp m n)).1
  have h := de_lift (𝕜 := 𝕜) P G hG (fun (a : Fin m × Fin n) w => (X w).1 a.1 * (X w).2 a.2) hφ 1
    zero_le_one (fun e he => by
      filter_upwards [de_real_i P X hX G hG hind e he] with ζ hζ
      rw [Fintype.sum_prod_type, one_mul]; exact hζ) e he2
  filter_upwards [h] with ζ hζ
  rw [Real.sqrt_one, one_mul, Fintype.sum_prod_type] at hζ
  exact hζ

/-- `lem:app-de-bessel`, part (ii), snapshot `cr-2026-10-23`. Verbatim from the frozen source
(`section.tex` l.945–956; `real or complex e` is `RCLike 𝕜`, and the conditional expectation
`𝔼_𝒢` is `condExp G P`):

\begin{lemma}[Bessel bounds]\label{lem:app-de-bessel}
Let $z\sim\mathcal N(0,\Id_{\Nout})$ and $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent of each other and of a $\sigma$-field $\mathcal G$, and let $e$ be
a real or complex random variable depending on $z$, $w$ and $\mathcal G$. Then
\begin{equation}\label{eqn:app-de-bessel}
\begin{gathered}
\norm{\EE_{\mathcal G}[(z\tensor w)\,e]}_\F\le\norm{e}_{2,\mathcal G},\qquad
\norm{\EE_{\mathcal G}[(z\tensor z-\Id)\,e]}_\F\le\sqrt2\,\norm{e}_{2,\mathcal G},\\
\norm{\EE_{\mathcal G}[(w\tensor w-\Id)\,e]}_\F\le\sqrt2\,\norm{e}_{2,\mathcal G}.
\end{gathered}
\end{equation}
\end{lemma}
-/
theorem lem_app_de_bessel_ii {m : ℕ} {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace 𝕜]
    [BorelSpace 𝕜] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X inferInstance) G P)
    (e : Ω → 𝕜) (he : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e)
    (he2 : MemLp e 2 P) :
    ∀ᵐ ζ ∂P,
      Real.sqrt (∑ i, ∑ k, ‖condExp G P
          (fun ω' => ((((X ω').1 i * (X ω').1 k - (1 : Mat m m) i k : ℝ)) : 𝕜) * e ω') ζ‖ ^ 2) ≤
        Real.sqrt 2 * Real.sqrt (condExp G P (fun ω' => ‖e ω'‖ ^ 2) ζ) := by
  have hmap : (gaussPair m n).map Prod.fst = Muon.Foundations.stdGaussianPi m := by
    unfold gaussPair
    rw [Measure.map_fst_prod]; simp
  have hφ := de_sq_memLp P X hX Prod.fst measurable_fst hmap
  have h := de_lift (𝕜 := 𝕜) P G hG (fun (a : Fin m × Fin m) w =>
      (X w).1 a.1 * (X w).1 a.2 - (1 : Matrix (Fin m) (Fin m) ℝ) a.1 a.2) hφ 2
    (by norm_num) (fun e he => by
      filter_upwards [de_real_sq P X hX Prod.fst measurable_fst hmap G hG hind e he] with ζ hζ
      rw [Fintype.sum_prod_type]; exact hζ) e he2
  filter_upwards [h] with ζ hζ
  rw [Fintype.sum_prod_type] at hζ
  exact hζ

/-- `lem:app-de-bessel`, part (iii), snapshot `cr-2026-10-23`. Verbatim from the frozen source
(`section.tex` l.945–956; `real or complex e` is `RCLike 𝕜`, and the conditional expectation
`𝔼_𝒢` is `condExp G P`):

\begin{lemma}[Bessel bounds]\label{lem:app-de-bessel}
Let $z\sim\mathcal N(0,\Id_{\Nout})$ and $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent of each other and of a $\sigma$-field $\mathcal G$, and let $e$ be
a real or complex random variable depending on $z$, $w$ and $\mathcal G$. Then
\begin{equation}\label{eqn:app-de-bessel}
\begin{gathered}
\norm{\EE_{\mathcal G}[(z\tensor w)\,e]}_\F\le\norm{e}_{2,\mathcal G},\qquad
\norm{\EE_{\mathcal G}[(z\tensor z-\Id)\,e]}_\F\le\sqrt2\,\norm{e}_{2,\mathcal G},\\
\norm{\EE_{\mathcal G}[(w\tensor w-\Id)\,e]}_\F\le\sqrt2\,\norm{e}_{2,\mathcal G}.
\end{gathered}
\end{equation}
\end{lemma}
-/
theorem lem_app_de_bessel_iii {m n : ℕ} {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace 𝕜]
    [BorelSpace 𝕜] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Vec m × Vec n)
    (hX : P.map X = gaussPair m n) (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X inferInstance) G P)
    (e : Ω → 𝕜) (he : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e)
    (he2 : MemLp e 2 P) :
    ∀ᵐ ζ ∂P,
      Real.sqrt (∑ i, ∑ k, ‖condExp G P
          (fun ω' => ((((X ω').2 i * (X ω').2 k - (1 : Mat n n) i k : ℝ)) : 𝕜) * e ω') ζ‖ ^ 2) ≤
        Real.sqrt 2 * Real.sqrt (condExp G P (fun ω' => ‖e ω'‖ ^ 2) ζ) := by
  have hmap : (gaussPair m n).map Prod.snd = Muon.Foundations.stdGaussianPi n := by
    unfold gaussPair
    rw [Measure.map_snd_prod]; simp
  have hφ := de_sq_memLp P X hX Prod.snd measurable_snd hmap
  have h := de_lift (𝕜 := 𝕜) P G hG (fun (a : Fin n × Fin n) w =>
      (X w).2 a.1 * (X w).2 a.2 - (1 : Matrix (Fin n) (Fin n) ℝ) a.1 a.2) hφ 2
    (by norm_num) (fun e he => by
      filter_upwards [de_real_sq P X hX Prod.snd measurable_snd hmap G hG hind e he] with ζ hζ
      rw [Fintype.sum_prod_type]; exact hζ) e he2
  filter_upwards [h] with ζ hζ
  rw [Fintype.sum_prod_type] at hζ
  exact hζ

/-! ## Gaussian response (`lem:app-de-stein`) -/

/-! ## Helpers for `lem:app-de-stein` -/

private lemma st_int_pow (n q : ℕ) :
    Integrable (fun z : Vec n => (1 + ∑ i, z i ^ 2) ^ q) (Muon.Foundations.stdGaussianPi n) := by
  have h : ∀ z : Vec n, (1 + ∑ i, z i ^ 2) ^ q = ∑ j ∈ Finset.range (q + 1), ((∑ i, z i ^ 2) ^ j * 1 ^ (q - j) * (q.choose j : ℝ)) := by
    intro z; rw [add_comm, add_pow]
  simp_rw [h]
  refine integrable_finsetSum _ fun j _ => ?_
  simp only [one_pow, mul_one]
  exact (de_sq_sum_pow_integrable n j).mul_const _

private lemma st_int_single {N : ℕ} (F : Vec N → ℝ) (hF : AEStronglyMeasurable F (Muon.Foundations.stdGaussianPi N))
    (K : ℝ) (p : ℕ) (h : ∀ z, |F z| ≤ K * (1 + ∑ i, z i ^ 2) ^ p) :
    Integrable F (Muon.Foundations.stdGaussianPi N) := by
  refine ((st_int_pow N p).const_mul K).mono' hF (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]; exact h z

private lemma st_int_pair {m n : ℕ} (F : Vec m × Vec n → ℝ) (hF : AEStronglyMeasurable F (gaussPair m n))
    (K : ℝ) (p : ℕ) (h : ∀ x : Vec m × Vec n, |F x| ≤ K * (1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)) ^ p) :
    Integrable F (gaussPair m n) := by
  have hK : 0 ≤ K := by
    have := h 0; simp at this
    exact le_trans (abs_nonneg _) this
  have hI : Integrable (fun x : Vec m × Vec n => K * ((1 + ∑ i, x.1 i ^ 2) ^ p * (1 + ∑ j, x.2 j ^ 2) ^ p)) (gaussPair m n) := by
    unfold gaussPair
    exact ((st_int_pow m p).mul_prod (st_int_pow n p)).const_mul K
  refine hI.mono' hF (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  refine (h x).trans (mul_le_mul_of_nonneg_left ?_ hK)
  rw [← mul_pow]
  have h1 : 0 ≤ ∑ i, x.1 i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : 0 ≤ ∑ j, x.2 j ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  exact pow_le_pow_left₀ (by positivity) (by nlinarith) p

private lemma st_one_add_pow_le (u : ℝ) (hu : 0 ≤ u) (p : ℕ) : (1 + u) ^ p ≤ 2 ^ p * (1 + u ^ p) := by
  have hup : 0 ≤ u ^ p := by positivity
  rcases le_total u 1 with h | h
  · calc (1 + u) ^ p ≤ 2 ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
      _ ≤ 2 ^ p * (1 + u ^ p) := le_mul_of_one_le_right (by positivity) (by linarith)
  · calc (1 + u) ^ p ≤ (2 * u) ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
      _ = 2 ^ p * u ^ p := mul_pow _ _ _
      _ ≤ 2 ^ p * (1 + u ^ p) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private lemma st_slice_sum {N : ℕ} (k : Fin (N + 1)) (t : ℝ) (y : Vec N) :
    ∑ i, (Fin.insertNth k t y : Vec (N + 1)) i ^ 2 = t ^ 2 + ∑ j, y j ^ 2 := by
  rw [Fin.sum_univ_succAbove _ k]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

private lemma st_slice_growth {N : ℕ} (k : Fin (N + 1)) (F : Vec (N + 1) → ℝ) (K : ℝ) (p : ℕ)
    (h : ∀ z, |F z| ≤ K * (1 + ∑ i, z i ^ 2) ^ p) (y : Vec N) :
    ∃ (C : ℝ) (q : ℕ), ∀ t : ℝ, |F (Fin.insertNth k t y)| ≤ C * (1 + |t| ^ q) := by
  have hK : 0 ≤ K := by
    have := h 0; simp at this
    exact le_trans (abs_nonneg _) this
  refine ⟨K * (1 + ∑ j, y j ^ 2) ^ p * 2 ^ p, 2 * p, fun t => ?_⟩
  have h1 := h (Fin.insertNth k t y)
  rw [st_slice_sum] at h1
  have hy : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : (1 + (t ^ 2 + ∑ j, y j ^ 2)) ^ p ≤ (1 + ∑ j, y j ^ 2) ^ p * (1 + t ^ 2) ^ p := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg t]) p
  have h3 := st_one_add_pow_le (t ^ 2) (sq_nonneg t) p
  have h4 : (t ^ 2) ^ p = |t| ^ (2 * p) := by rw [pow_mul, sq_abs]
  rw [h4] at h3
  calc |F (Fin.insertNth k t y)| ≤ K * (1 + (t ^ 2 + ∑ j, y j ^ 2)) ^ p := h1
    _ ≤ K * ((1 + ∑ j, y j ^ 2) ^ p * (1 + t ^ 2) ^ p) := mul_le_mul_of_nonneg_left h2 hK
    _ ≤ K * ((1 + ∑ j, y j ^ 2) ^ p * (2 ^ p * (1 + |t| ^ (2 * p)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) hK
    _ = _ := by ring

private lemma st_stein_pi {N : ℕ} (k : Fin N) (F F' : Vec N → ℝ) (hF : Continuous F)
    (hF' : Continuous F')
    (hd : ∀ z : Vec N, HasDerivAt (fun t => F (Function.update z k t)) (F' z) (z k))
    (K : ℝ) (p : ℕ) (hg : ∀ z, |F z| ≤ K * (1 + ∑ i, z i ^ 2) ^ p)
    (K' : ℝ) (p' : ℕ) (hg' : ∀ z, |F' z| ≤ K' * (1 + ∑ i, z i ^ 2) ^ p') :
    ∫ z, z k * F z ∂(Muon.Foundations.stdGaussianPi N) =
      ∫ z, F' z ∂(Muon.Foundations.stdGaussianPi N) := by
  cases N with
  | zero => exact k.elim0
  | succ N =>
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => gaussianReal 0 1) k
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) k with he
  set ν := (gaussianReal 0 1).prod (Measure.pi fun j : Fin N => gaussianReal 0 1) with hν
  have hstd : Muon.Foundations.stdGaussianPi (N + 1) = Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1 := rfl
  have hI : ∀ G : Vec (N + 1) → ℝ, ∫ z, G z ∂(Muon.Foundations.stdGaussianPi (N + 1)) =
      ∫ q, G (e.symm q) ∂ν := by
    intro G
    have := hmp.integral_comp' (g := fun q => G (e.symm q))
    rw [hstd]
    simpa using this
  have hIn : ∀ G : Vec (N + 1) → ℝ, Integrable G (Muon.Foundations.stdGaussianPi (N + 1)) →
      Integrable (fun q => G (e.symm q)) ν := by
    intro G hG
    have := (hmp.symm).integrable_comp_emb (MeasurableEquiv.measurableEmbedding e.symm) (g := G)
    exact this.2 (by rw [hstd] at hG; exact hG)
  have hsym : ∀ q : ℝ × Vec N, (e.symm q) = Fin.insertNth k q.1 q.2 := by
    intro q; simp [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hint1 : Integrable (fun z : Vec (N + 1) => z k * F z) (Muon.Foundations.stdGaussianPi (N + 1)) := by
    refine st_int_single _ ((continuous_apply k).mul hF).aestronglyMeasurable (K * 2) (p + 1) fun z => ?_
    have hK : 0 ≤ K := by
      have := hg 0; simp at this
      exact le_trans (abs_nonneg _) this
    have hz : |z k| ≤ 1 + ∑ i, z i ^ 2 := by
      have : z k ^ 2 ≤ ∑ i, z i ^ 2 := Finset.single_le_sum (f := fun i => z i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ k)
      nlinarith [sq_abs (z k), abs_nonneg (z k)]
    have hS : 1 ≤ 1 + ∑ i, z i ^ 2 := by
      have : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      linarith
    rw [abs_mul]
    calc |z k| * |F z| ≤ (1 + ∑ i, z i ^ 2) * (K * (1 + ∑ i, z i ^ 2) ^ p) :=
          mul_le_mul hz (hg z) (abs_nonneg _) (by positivity)
      _ = K * (1 + ∑ i, z i ^ 2) ^ (p + 1) := by ring
      _ ≤ K * 2 * (1 + ∑ i, z i ^ 2) ^ (p + 1) := by
          have : 0 ≤ K * (1 + ∑ i, z i ^ 2) ^ (p + 1) := by positivity
          nlinarith
  have hint2 : Integrable F' (Muon.Foundations.stdGaussianPi (N + 1)) :=
    st_int_single _ hF'.aestronglyMeasurable K' p' hg'
  rw [hI, hI, integral_prod_symm _ (hIn _ hint1), integral_prod_symm _ (hIn _ hint2)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [hsym]
  simp only [Fin.insertNth_apply_same]
  have hdy : ∀ t : ℝ, HasDerivAt (fun s => F (Fin.insertNth k s y)) (F' (Fin.insertNth k t y)) t := by
    intro t
    have := hd (Fin.insertNth k t y)
    simp only [Fin.insertNth_apply_same, Fin.update_insertNth] at this
    exact this
  have hcont : Continuous (fun s : ℝ => Fin.insertNth k s y : ℝ → Vec (N + 1)) :=
    Continuous.finInsertNth (A := fun _ => ℝ) k continuous_id continuous_const
  have hcd : ContDiff ℝ 1 (fun s => F (Fin.insertNth k s y)) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hdy t).differentiableAt, ?_⟩
    have : deriv (fun s => F (Fin.insertNth k s y)) = fun t => F' (Fin.insertNth k t y) :=
      funext fun t => (hdy t).deriv
    rw [this]
    exact hF'.comp hcont
  have hder : deriv (fun s => F (Fin.insertNth k s y)) = fun t => F' (Fin.insertNth k t y) :=
    funext fun t => (hdy t).deriv
  have := Muon.Foundations.gaussian_stein (fun s => F (Fin.insertNth k s y)) hcd
    (st_slice_growth k F K p hg y)
    (by rw [hder]; exact st_slice_growth k F' K' p' hg' y)
  rw [hder] at this
  exact this

private lemma st_split (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℕ) :
    (1 + (a + b)) ^ p ≤ (1 + a) ^ p * (1 + b) ^ p := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by nlinarith) p

private lemma st_mul_bound (a F K S : ℝ) (p : ℕ) (ha : |a| ≤ 1 + S) (hS : 0 ≤ S)
    (hF : |F| ≤ K * (1 + S) ^ p) : |a * F| ≤ K * 2 * (1 + S) ^ (p + 1) := by
  have hK : 0 ≤ K := by
    have h0 : 0 ≤ K * (1 + S) ^ p := le_trans (abs_nonneg _) hF
    exact nonneg_of_mul_nonneg_left h0 (by positivity)
  rw [abs_mul]
  have hS1 : 1 ≤ 1 + S := by linarith
  calc |a| * |F| ≤ (1 + S) * (K * (1 + S) ^ p) :=
        mul_le_mul ha hF (abs_nonneg _) (by positivity)
    _ = K * (1 + S) ^ (p + 1) := by ring
    _ ≤ K * 2 * (1 + S) ^ (p + 1) := by
        have : 0 ≤ K * (1 + S) ^ (p + 1) := by positivity
        nlinarith

private lemma st_coord_le {N : ℕ} (z : Vec N) (k : Fin N) : |z k| ≤ 1 + ∑ i, z i ^ 2 := by
  have : z k ^ 2 ≤ ∑ i, z i ^ 2 :=
    Finset.single_le_sum (f := fun i => z i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ k)
  nlinarith [sq_abs (z k), abs_nonneg (z k)]

private lemma st_sum_nonneg {N : ℕ} (z : Vec N) : 0 ≤ ∑ i, z i ^ 2 :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

private lemma st_stein_fst {m n : ℕ} (k : Fin m) (F F' : Vec m × Vec n → ℝ) (hF : Continuous F)
    (hF' : Continuous F')
    (hd : ∀ x : Vec m × Vec n,
      HasDerivAt (fun t => F (Function.update x.1 k t, x.2)) (F' x) (x.1 k))
    (K : ℝ) (p : ℕ)
    (hg : ∀ x : Vec m × Vec n, |F x| ≤ K * (1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)) ^ p)
    (K' : ℝ) (p' : ℕ)
    (hg' : ∀ x : Vec m × Vec n, |F' x| ≤ K' * (1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)) ^ p') :
    ∫ x, x.1 k * F x ∂(gaussPair m n) = ∫ x, F' x ∂(gaussPair m n) := by
  have hint1 : Integrable (fun x : Vec m × Vec n => x.1 k * F x) (gaussPair m n) :=
    st_int_pair _ ((continuous_apply k |>.comp continuous_fst).mul hF).aestronglyMeasurable
      (K * 2) (p + 1) fun x => st_mul_bound _ _ _ _ _
        ((st_coord_le x.1 k).trans (by linarith [st_sum_nonneg x.2])) (by
          linarith [st_sum_nonneg x.1, st_sum_nonneg x.2]) (hg x)
  have hint2 : Integrable F' (gaussPair m n) :=
    st_int_pair _ hF'.aestronglyMeasurable K' p' hg'
  unfold gaussPair at hint1 hint2 ⊢
  rw [integral_prod_symm _ hint1, integral_prod_symm _ hint2]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  have hK : 0 ≤ K := by
    have := hg 0; simp at this
    exact le_trans (abs_nonneg _) this
  have hK' : 0 ≤ K' := by
    have := hg' 0; simp at this
    exact le_trans (abs_nonneg _) this
  have hw := st_sum_nonneg w
  refine st_stein_pi k (fun z => F (z, w)) (fun z => F' (z, w)) (hF.comp (by fun_prop))
    (hF'.comp (by fun_prop)) (fun z => hd (z, w)) (K * (1 + ∑ j, w j ^ 2) ^ p) p
    (fun z => ?_) (K' * (1 + ∑ j, w j ^ 2) ^ p') p' (fun z => ?_)
  · calc |F (z, w)| ≤ K * (1 + (∑ i, z i ^ 2 + ∑ j, w j ^ 2)) ^ p := hg (z, w)
      _ ≤ K * ((1 + ∑ i, z i ^ 2) ^ p * (1 + ∑ j, w j ^ 2) ^ p) :=
        mul_le_mul_of_nonneg_left (st_split _ _ (st_sum_nonneg z) hw p) hK
      _ = _ := by ring
  · calc |F' (z, w)| ≤ K' * (1 + (∑ i, z i ^ 2 + ∑ j, w j ^ 2)) ^ p' := hg' (z, w)
      _ ≤ K' * ((1 + ∑ i, z i ^ 2) ^ p' * (1 + ∑ j, w j ^ 2) ^ p') :=
        mul_le_mul_of_nonneg_left (st_split _ _ (st_sum_nonneg z) hw p') hK'
      _ = _ := by ring

private lemma st_stein_snd {m n : ℕ} (l : Fin n) (F F' : Vec m × Vec n → ℝ) (hF : Continuous F)
    (hF' : Continuous F')
    (hd : ∀ x : Vec m × Vec n,
      HasDerivAt (fun t => F (x.1, Function.update x.2 l t)) (F' x) (x.2 l))
    (K : ℝ) (p : ℕ)
    (hg : ∀ x : Vec m × Vec n, |F x| ≤ K * (1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)) ^ p)
    (K' : ℝ) (p' : ℕ)
    (hg' : ∀ x : Vec m × Vec n, |F' x| ≤ K' * (1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)) ^ p') :
    ∫ x, x.2 l * F x ∂(gaussPair m n) = ∫ x, F' x ∂(gaussPair m n) := by
  have hint1 : Integrable (fun x : Vec m × Vec n => x.2 l * F x) (gaussPair m n) :=
    st_int_pair _ ((continuous_apply l |>.comp continuous_snd).mul hF).aestronglyMeasurable
      (K * 2) (p + 1) fun x => st_mul_bound _ _ _ _ _
        ((st_coord_le x.2 l).trans (by linarith [st_sum_nonneg x.1])) (by
          linarith [st_sum_nonneg x.1, st_sum_nonneg x.2]) (hg x)
  have hint2 : Integrable F' (gaussPair m n) :=
    st_int_pair _ hF'.aestronglyMeasurable K' p' hg'
  unfold gaussPair at hint1 hint2 ⊢
  rw [integral_prod _ hint1, integral_prod _ hint2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  have hK : 0 ≤ K := by
    have := hg 0; simp at this
    exact le_trans (abs_nonneg _) this
  have hK' : 0 ≤ K' := by
    have := hg' 0; simp at this
    exact le_trans (abs_nonneg _) this
  have hz := st_sum_nonneg z
  refine st_stein_pi l (fun w => F (z, w)) (fun w => F' (z, w)) (hF.comp (by fun_prop))
    (hF'.comp (by fun_prop)) (fun w => hd (z, w)) (K * (1 + ∑ i, z i ^ 2) ^ p) p
    (fun w => ?_) (K' * (1 + ∑ i, z i ^ 2) ^ p') p' (fun w => ?_)
  · calc |F (z, w)| ≤ K * (1 + (∑ i, z i ^ 2 + ∑ j, w j ^ 2)) ^ p := hg (z, w)
      _ ≤ K * ((1 + ∑ i, z i ^ 2) ^ p * (1 + ∑ j, w j ^ 2) ^ p) :=
        mul_le_mul_of_nonneg_left (st_split _ _ hz (st_sum_nonneg w) p) hK
      _ = _ := by ring
  · calc |F' (z, w)| ≤ K' * (1 + (∑ i, z i ^ 2 + ∑ j, w j ^ 2)) ^ p' := hg' (z, w)
      _ ≤ K' * ((1 + ∑ i, z i ^ 2) ^ p' * (1 + ∑ j, w j ^ 2) ^ p') :=
        mul_le_mul_of_nonneg_left (st_split _ _ hz (st_sum_nonneg w) p') hK'
      _ = _ := by ring

private lemma st_pg_mul {E : Type*} (S : E → ℝ) {F G : E → ℝ}
    (hF : ∃ (K : ℝ) (p : ℕ), ∀ x, |F x| ≤ K * (1 + S x) ^ p)
    (hG : ∃ (K : ℝ) (p : ℕ), ∀ x, |G x| ≤ K * (1 + S x) ^ p) :
    ∃ (K : ℝ) (p : ℕ), ∀ x, |F x * G x| ≤ K * (1 + S x) ^ p := by
  obtain ⟨K1, p1, h1⟩ := hF
  obtain ⟨K2, p2, h2⟩ := hG
  refine ⟨K1 * K2, p1 + p2, fun x => ?_⟩
  rw [abs_mul, pow_add]
  calc |F x| * |G x| ≤ (K1 * (1 + S x) ^ p1) * (K2 * (1 + S x) ^ p2) :=
        mul_le_mul (h1 x) (h2 x) (abs_nonneg _) (le_trans (abs_nonneg _) (h1 x))
    _ = _ := by ring

private lemma st_pg_add {E : Type*} (S : E → ℝ) (hS : ∀ x, 0 ≤ S x) {F G : E → ℝ}
    (hF : ∃ (K : ℝ) (p : ℕ), ∀ x, |F x| ≤ K * (1 + S x) ^ p)
    (hG : ∃ (K : ℝ) (p : ℕ), ∀ x, |G x| ≤ K * (1 + S x) ^ p) :
    ∃ (K : ℝ) (p : ℕ), ∀ x, |F x + G x| ≤ K * (1 + S x) ^ p := by
  obtain ⟨K1, p1, h1⟩ := hF
  obtain ⟨K2, p2, h2⟩ := hG
  refine ⟨|K1| + |K2|, p1 + p2, fun x => ?_⟩
  have hb : 1 ≤ 1 + S x := by linarith [hS x]
  have e1 : (1 + S x) ^ p1 ≤ (1 + S x) ^ (p1 + p2) := pow_le_pow_right₀ hb (by omega)
  have e2 : (1 + S x) ^ p2 ≤ (1 + S x) ^ (p1 + p2) := pow_le_pow_right₀ hb (by omega)
  have p0 : 0 < (1 + S x) ^ p1 := by positivity
  have p0' : 0 < (1 + S x) ^ p2 := by positivity
  calc |F x + G x| ≤ |F x| + |G x| := abs_add_le _ _
    _ ≤ K1 * (1 + S x) ^ p1 + K2 * (1 + S x) ^ p2 := add_le_add (h1 x) (h2 x)
    _ ≤ |K1| * (1 + S x) ^ (p1 + p2) + |K2| * (1 + S x) ^ (p1 + p2) :=
        add_le_add (mul_le_mul (le_abs_self _) e1 p0.le (abs_nonneg _))
          (mul_le_mul (le_abs_self _) e2 p0'.le (abs_nonneg _))
    _ = _ := by ring

private lemma st_pg_const {E : Type*} (S : E → ℝ) (c : ℝ) :
    ∃ (K : ℝ) (p : ℕ), ∀ _x : E, |c| ≤ K * (1 + S _x) ^ p :=
  ⟨|c|, 0, fun _ => by simp⟩

private lemma st_pg_fst {m n : ℕ} (a : Fin m) :
    ∃ (K : ℝ) (p : ℕ), ∀ x : Vec m × Vec n, |x.1 a| ≤
      K * (1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)) ^ p :=
  ⟨1, 1, fun x => by
    have := (st_coord_le x.1 a).trans (by linarith [st_sum_nonneg x.2] :
      1 + ∑ i, x.1 i ^ 2 ≤ 1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2))
    simpa using this⟩

private lemma st_pg_snd {m n : ℕ} (a : Fin n) :
    ∃ (K : ℝ) (p : ℕ), ∀ x : Vec m × Vec n, |x.2 a| ≤
      K * (1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)) ^ p :=
  ⟨1, 1, fun x => by
    have := (st_coord_le x.2 a).trans (by linarith [st_sum_nonneg x.1] :
      1 + ∑ j, x.2 j ^ 2 ≤ 1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2))
    simpa using this⟩

private lemma st_resid_bound {m n : ℕ} (A : Mat m n) (x : Vec m × Vec n) :
    |resid A x| ≤ (∑ i, ∑ j, |A i j|) * (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2) := by
  have h1 : resid A x = ∑ i, ∑ j, x.1 i * (A i j * x.2 j) := by
    simp only [resid, dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hb : ∀ i j, |x.1 i * (A i j * x.2 j)| ≤ |A i j| * (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2) := by
    intro i j
    have e1 : x.1 i ^ 2 ≤ ∑ i, x.1 i ^ 2 :=
      Finset.single_le_sum (f := fun i => x.1 i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
    have e2 : x.2 j ^ 2 ≤ ∑ j, x.2 j ^ 2 :=
      Finset.single_le_sum (f := fun j => x.2 j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)
    have e3 : |x.1 i| * |x.2 j| ≤ ∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2 := by
      nlinarith [sq_abs (x.1 i), sq_abs (x.2 j), sq_nonneg (|x.1 i| - |x.2 j|), abs_nonneg (x.1 i),
        abs_nonneg (x.2 j)]
    calc |x.1 i * (A i j * x.2 j)| = |A i j| * (|x.1 i| * |x.2 j|) := by
          rw [abs_mul, abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left e3 (abs_nonneg _)
  rw [h1]
  calc |∑ i, ∑ j, x.1 i * (A i j * x.2 j)| ≤ ∑ i, |∑ j, x.1 i * (A i j * x.2 j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x.1 i * (A i j * x.2 j)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j| * (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ = _ := by simp only [← Finset.sum_mul]

private lemma st_pg_resid {m n : ℕ} (A : Mat m n) (g : ℝ → ℝ)
    (hg : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g u| ≤ K * (1 + |u| ^ k)) :
    ∃ (K : ℝ) (p : ℕ), ∀ x : Vec m × Vec n, |g (resid A x)| ≤
      K * (1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)) ^ p := by
  obtain ⟨K, k, h⟩ := hg
  have hK : 0 ≤ K := by
    have h0 := h 0
    have : 0 ≤ K * (1 + |(0 : ℝ)| ^ k) := le_trans (abs_nonneg _) h0
    exact nonneg_of_mul_nonneg_left this (by positivity)
  set C := ∑ i, ∑ j, |A i j| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨K * (1 + C ^ k), k, fun x => ?_⟩
  set S := ∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2 with hS
  have hS0 : 0 ≤ S := by linarith [st_sum_nonneg x.1, st_sum_nonneg x.2]
  have hd : |resid A x| ^ k ≤ C ^ k * (1 + S) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      ((st_resid_bound A x).trans (by nlinarith)) k
  have h1 : (1 : ℝ) ≤ (1 + S) ^ k := one_le_pow₀ (by linarith)
  calc |g (resid A x)| ≤ K * (1 + |resid A x| ^ k) := h _
    _ ≤ K * ((1 + S) ^ k + C ^ k * (1 + S) ^ k) := mul_le_mul_of_nonneg_left (by linarith) hK
    _ = _ := by ring

private lemma st_resid_upd1 {m n : ℕ} (A : Mat m n) (z : Vec m) (w : Vec n) (k : Fin m) (t : ℝ) :
    resid A (Function.update z k t, w) = resid A (z, w) + (t - z k) * (A *ᵥ w) k := by
  have h : Function.update z k t = z + Pi.single k (t - z k) := by
    ext i
    by_cases hi : i = k
    · subst hi; simp
    · simp [hi, Function.update_of_ne hi]
  simp only [resid]
  rw [h, add_dotProduct, single_dotProduct]

private lemma st_resid_upd2 {m n : ℕ} (A : Mat m n) (z : Vec m) (w : Vec n) (l : Fin n) (t : ℝ) :
    resid A (z, Function.update w l t) = resid A (z, w) + (t - w l) * (z ᵥ* A) l := by
  have h : Function.update w l t = w + Pi.single l (t - w l) := by
    ext i
    by_cases hi : i = l
    · subst hi; simp
    · simp [hi, Function.update_of_ne hi]
  simp only [resid]
  rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, h, dotProduct_add, dotProduct_single, mul_comm]

private lemma st_hd_z {m n : ℕ} (A : Mat m n) (g g1 : ℝ → ℝ) (hg : ∀ u, HasDerivAt g (g1 u) u)
    (z : Vec m) (w : Vec n) (k : Fin m) :
    HasDerivAt (fun t => g (resid A (Function.update z k t, w)))
      (g1 (resid A (z, w)) * (A *ᵥ w) k) (z k) := by
  have h1 : HasDerivAt (fun t : ℝ => resid A (z, w) + (t - z k) * (A *ᵥ w) k) ((A *ᵥ w) k) (z k) := by
    simpa using (((hasDerivAt_id (z k)).sub_const (z k)).mul_const ((A *ᵥ w) k)).const_add (resid A (z, w))
  have h2 : HasDerivAt g (g1 (resid A (z, w))) (resid A (z, w) + (z k - z k) * (A *ᵥ w) k) := by
    simpa using hg (resid A (z, w))
  have := h2.comp (z k) h1
  simpa [Function.comp_def, st_resid_upd1] using this

private lemma st_hd_w {m n : ℕ} (A : Mat m n) (g g1 : ℝ → ℝ) (hg : ∀ u, HasDerivAt g (g1 u) u)
    (z : Vec m) (w : Vec n) (l : Fin n) :
    HasDerivAt (fun t => g (resid A (z, Function.update w l t)))
      (g1 (resid A (z, w)) * (z ᵥ* A) l) (w l) := by
  have h1 : HasDerivAt (fun t : ℝ => resid A (z, w) + (t - w l) * (z ᵥ* A) l) ((z ᵥ* A) l) (w l) := by
    simpa using (((hasDerivAt_id (w l)).sub_const (w l)).mul_const ((z ᵥ* A) l)).const_add (resid A (z, w))
  have h2 : HasDerivAt g (g1 (resid A (z, w))) (resid A (z, w) + (w l - w l) * (z ᵥ* A) l) := by
    simpa using hg (resid A (z, w))
  have := h2.comp (w l) h1
  simpa [Function.comp_def, st_resid_upd2] using this

private lemma st_cont_resid {m n : ℕ} (A : Mat m n) : Continuous (resid A) := by
  have : resid A = fun x => ∑ i, x.1 i * ∑ j, A i j * x.2 j := by
    funext x; simp [resid, dotProduct, Matrix.mulVec]
  rw [this]
  fun_prop

private lemma st_cont_mulvec {m n : ℕ} (A : Mat m n) (k : Fin m) :
    Continuous (fun x : Vec m × Vec n => (A *ᵥ x.2) k) := by
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

private lemma st_cont_vecmul {m n : ℕ} (A : Mat m n) (l : Fin n) :
    Continuous (fun x : Vec m × Vec n => (x.1 ᵥ* A) l) := by
  simp only [Matrix.vecMul, dotProduct]
  fun_prop

private lemma st_pg_mulvec {m n : ℕ} (A : Mat m n) (k : Fin m) :
    ∃ (K : ℝ) (p : ℕ), ∀ x : Vec m × Vec n, |(A *ᵥ x.2) k| ≤
      K * (1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)) ^ p := by
  refine ⟨∑ j, |A k j|, 1, fun x => ?_⟩
  have hx : ∀ j, |x.2 j| ≤ 1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2) := fun j =>
    (st_coord_le x.2 j).trans (by linarith [st_sum_nonneg x.1])
  simp only [Matrix.mulVec, dotProduct, pow_one]
  calc |∑ j, A k j * x.2 j| ≤ ∑ j, |A k j * x.2 j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |A k j| * (1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)) :=
        Finset.sum_le_sum fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

private lemma st_pg_vecmul {m n : ℕ} (A : Mat m n) (l : Fin n) :
    ∃ (K : ℝ) (p : ℕ), ∀ x : Vec m × Vec n, |(x.1 ᵥ* A) l| ≤
      K * (1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)) ^ p := by
  refine ⟨∑ i, |A i l|, 1, fun x => ?_⟩
  have hx : ∀ i, |x.1 i| ≤ 1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2) := fun i =>
    (st_coord_le x.1 i).trans (by linarith [st_sum_nonneg x.2])
  simp only [Matrix.vecMul, dotProduct, pow_one]
  calc |∑ i, x.1 i * A i l| ≤ ∑ i, |x.1 i * A i l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |A i l| * (1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)) :=
        Finset.sum_le_sum fun i _ => by
          rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_left (hx i) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

private lemma st_D0 {N : ℕ} (z : Vec N) (k a : Fin N) :
    HasDerivAt (fun t : ℝ => Function.update z k t a) (if a = k then 1 else 0) (z k) := by
  by_cases h : a = k
  · subst h; simpa using hasDerivAt_id' (z a)
  · simpa [h, Function.update_of_ne h] using hasDerivAt_const (z k) (z a)

private lemma st_LZ1 {m n : ℕ} (A : Mat m n) (g0 g1 : ℝ → ℝ) (hd : ∀ u, HasDerivAt g0 (g1 u) u)
    (hc0 : Continuous g0) (hc1 : Continuous g1)
    (hp0 : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g0 u| ≤ K * (1 + |u| ^ k))
    (hp1 : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g1 u| ≤ K * (1 + |u| ^ k)) (k a : Fin m) :
    ∫ x, x.1 k * (x.1 a * g0 (resid A x)) ∂(gaussPair m n) =
      ∫ x, ((if a = k then (1 : ℝ) else 0) * g0 (resid A x) +
        x.1 a * (g1 (resid A x) * (A *ᵥ x.2) k)) ∂(gaussPair m n) := by
  have S := fun x : Vec m × Vec n => ∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2
  have pF := st_pg_mul (fun x : Vec m × Vec n => ∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)
    (st_pg_fst a) (st_pg_resid A g0 hp0)
  have pF' := st_pg_add (fun x : Vec m × Vec n => ∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)
    (fun x => by linarith [st_sum_nonneg x.1, st_sum_nonneg x.2])
    (st_pg_mul (fun x : Vec m × Vec n => ∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)
      (st_pg_const _ (if a = k then (1 : ℝ) else 0)) (st_pg_resid A g0 hp0))
    (st_pg_mul (fun x : Vec m × Vec n => ∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2) (st_pg_fst a)
      (st_pg_mul _ (st_pg_resid A g1 hp1) (st_pg_mulvec A k)))
  obtain ⟨K, p, hK⟩ := pF
  obtain ⟨K', p', hK'⟩ := pF'
  have cr := st_cont_resid A
  refine st_stein_fst k (fun x => x.1 a * g0 (resid A x))
    (fun x => (if a = k then (1 : ℝ) else 0) * g0 (resid A x) +
        x.1 a * (g1 (resid A x) * (A *ᵥ x.2) k)) (by fun_prop) ?_ ?_ K p hK K' p' hK'
  · have := st_cont_mulvec A k
    fun_prop
  · intro x
    have h := (st_D0 x.1 k a).mul (st_hd_z A g0 g1 hd x.1 x.2 k)
    refine HasDerivAt.congr_deriv h ?_
    simp

private lemma st_LZ2 {m n : ℕ} (A : Mat m n) (g0 g1 : ℝ → ℝ) (hd : ∀ u, HasDerivAt g0 (g1 u) u)
    (hc0 : Continuous g0) (hc1 : Continuous g1)
    (hp0 : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g0 u| ≤ K * (1 + |u| ^ k))
    (hp1 : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g1 u| ≤ K * (1 + |u| ^ k)) (k : Fin m) (j : Fin n) :
    ∫ x, x.1 k * (x.2 j * g0 (resid A x)) ∂(gaussPair m n) =
      ∫ x, x.2 j * (g1 (resid A x) * (A *ᵥ x.2) k) ∂(gaussPair m n) := by
  have pF := st_pg_mul (fun x : Vec m × Vec n => ∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)
    (st_pg_snd j) (st_pg_resid A g0 hp0)
  have pF' := st_pg_mul (fun x : Vec m × Vec n => ∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2) (st_pg_snd j)
      (st_pg_mul _ (st_pg_resid A g1 hp1) (st_pg_mulvec A k))
  obtain ⟨K, p, hK⟩ := pF
  obtain ⟨K', p', hK'⟩ := pF'
  have cr := st_cont_resid A
  refine st_stein_fst k (fun x => x.2 j * g0 (resid A x))
    (fun x => x.2 j * (g1 (resid A x) * (A *ᵥ x.2) k)) (by fun_prop) ?_ ?_ K p hK K' p' hK'
  · have := st_cont_mulvec A k
    fun_prop
  · intro x
    exact (st_hd_z A g0 g1 hd x.1 x.2 k).const_mul (x.2 j)

private lemma st_LW1 {m n : ℕ} (A : Mat m n) (g0 g1 : ℝ → ℝ) (hd : ∀ u, HasDerivAt g0 (g1 u) u)
    (hc0 : Continuous g0) (hc1 : Continuous g1)
    (hp0 : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g0 u| ≤ K * (1 + |u| ^ k))
    (hp1 : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g1 u| ≤ K * (1 + |u| ^ k)) (k : Fin m) (l : Fin n) :
    ∫ x, x.2 l * (x.1 k * g0 (resid A x)) ∂(gaussPair m n) =
      ∫ x, x.1 k * (g1 (resid A x) * (x.1 ᵥ* A) l) ∂(gaussPair m n) := by
  have pF := st_pg_mul (fun x : Vec m × Vec n => ∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)
    (st_pg_fst k) (st_pg_resid A g0 hp0)
  have pF' := st_pg_mul (fun x : Vec m × Vec n => ∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2) (st_pg_fst k)
      (st_pg_mul _ (st_pg_resid A g1 hp1) (st_pg_vecmul A l))
  obtain ⟨K, p, hK⟩ := pF
  obtain ⟨K', p', hK'⟩ := pF'
  have cr := st_cont_resid A
  refine st_stein_snd l (fun x => x.1 k * g0 (resid A x))
    (fun x => x.1 k * (g1 (resid A x) * (x.1 ᵥ* A) l)) (by fun_prop) ?_ ?_ K p hK K' p' hK'
  · have := st_cont_vecmul A l
    fun_prop
  · intro x
    exact (st_hd_w A g0 g1 hd x.1 x.2 l).const_mul (x.1 k)

private lemma st_int_gen {m n : ℕ} (A : Mat m n) (c : Vec m × Vec n → ℝ) (hc : Continuous c)
    (hpc : ∃ (K : ℝ) (p : ℕ), ∀ x : Vec m × Vec n,
      |c x| ≤ K * (1 + (∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2)) ^ p)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hpg : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g u| ≤ K * (1 + |u| ^ k)) :
    Integrable (fun x => c x * g (resid A x)) (gaussPair m n) := by
  obtain ⟨K, p, h⟩ := st_pg_mul (fun x : Vec m × Vec n => ∑ i, x.1 i ^ 2 + ∑ j, x.2 j ^ 2) hpc
    (st_pg_resid A g hpg)
  exact st_int_pair _ (hc.mul (hg.comp (st_cont_resid A))).aestronglyMeasurable K p h

private lemma st_I_a {m n : ℕ} (A : Mat m n) (g : ℝ → ℝ) (hg : Continuous g)
    (hpg : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g u| ≤ K * (1 + |u| ^ k)) (k a : Fin m) :
    Integrable (fun x : Vec m × Vec n => x.1 k * (x.1 a * g (resid A x))) (gaussPair m n) :=
  (st_int_gen A (fun x => x.1 k * x.1 a) (by fun_prop)
    (st_pg_mul _ (st_pg_fst k) (st_pg_fst a)) g hg hpg).congr
    (ae_of_all _ fun x => mul_assoc _ _ _)

private lemma st_I_b {m n : ℕ} (A : Mat m n) (g : ℝ → ℝ) (hg : Continuous g)
    (hpg : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g u| ≤ K * (1 + |u| ^ k)) (c : ℝ) :
    Integrable (fun x : Vec m × Vec n => c * g (resid A x)) (gaussPair m n) :=
  st_int_gen A (fun _ => c) continuous_const (st_pg_const _ c) g hg hpg

private lemma st_I_d {m n : ℕ} (A : Mat m n) (g : ℝ → ℝ) (hg : Continuous g)
    (hpg : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g u| ≤ K * (1 + |u| ^ k)) (a : Fin m) (j : Fin n) :
    Integrable (fun x : Vec m × Vec n => x.1 a * (x.2 j * g (resid A x))) (gaussPair m n) :=
  (st_int_gen A (fun x => x.1 a * x.2 j) (by fun_prop)
    (st_pg_mul _ (st_pg_fst a) (st_pg_snd j)) g hg hpg).congr
    (ae_of_all _ fun x => mul_assoc _ _ _)

private lemma st_I_f {m n : ℕ} (A : Mat m n) (g : ℝ → ℝ) (hg : Continuous g)
    (hpg : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g u| ≤ K * (1 + |u| ^ k)) (j i : Fin n) :
    Integrable (fun x : Vec m × Vec n => g (resid A x) * (x.2 j * x.2 i)) (gaussPair m n) :=
  (st_int_gen A (fun x => x.2 j * x.2 i) (by fun_prop)
    (st_pg_mul _ (st_pg_snd j) (st_pg_snd i)) g hg hpg).congr
    (ae_of_all _ fun x => mul_comm _ _)

private lemma st_T2 {m n : ℕ} (A : Mat m n) (gp gq : ℝ → ℝ) (hd : ∀ u, HasDerivAt gp (gq u) u)
    (hcp : Continuous gp) (hcq : Continuous gq)
    (hpp : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |gp u| ≤ K * (1 + |u| ^ k))
    (hpq : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |gq u| ≤ K * (1 + |u| ^ k)) (k a : Fin m) :
    ∫ x, x.1 k * (x.1 a * gp (resid A x)) ∂(gaussPair m n) =
      (if a = k then (1 : ℝ) else 0) * ∫ x, gp (resid A x) ∂(gaussPair m n) +
        ∑ j, A k j * ∫ x, x.1 a * (x.2 j * gq (resid A x)) ∂(gaussPair m n) := by
  rw [st_LZ1 A gp gq hd hcp hcq hpp hpq k a]
  have e : ∀ x : Vec m × Vec n, (if a = k then (1 : ℝ) else 0) * gp (resid A x) +
      x.1 a * (gq (resid A x) * (A *ᵥ x.2) k) =
      (if a = k then (1 : ℝ) else 0) * gp (resid A x) +
        ∑ j, A k j * (x.1 a * (x.2 j * gq (resid A x))) := by
    intro x
    congr 1
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_add (st_I_b A gp hcp hpp _)
      (integrable_finsetSum _ fun j _ => (st_I_d A gq hcq hpq a j).const_mul _),
    integral_finsetSum _ fun j _ => (st_I_d A gq hcq hpq a j).const_mul _, integral_const_mul]
  simp only [integral_const_mul]

private lemma st_T3 {m n : ℕ} (A : Mat m n) (gp gq : ℝ → ℝ) (hd : ∀ u, HasDerivAt gp (gq u) u)
    (hcp : Continuous gp) (hcq : Continuous gq)
    (hpp : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |gp u| ≤ K * (1 + |u| ^ k))
    (hpq : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |gq u| ≤ K * (1 + |u| ^ k)) (a : Fin m) (j : Fin n) :
    ∫ x, x.1 a * (x.2 j * gp (resid A x)) ∂(gaussPair m n) =
      ∑ i, A a i * ∫ x, gq (resid A x) * (x.2 j * x.2 i) ∂(gaussPair m n) := by
  rw [st_LZ2 A gp gq hd hcp hcq hpp hpq a j]
  have e : ∀ x : Vec m × Vec n, x.2 j * (gq (resid A x) * (A *ᵥ x.2) a) =
      ∑ i, A a i * (gq (resid A x) * (x.2 j * x.2 i)) := by
    intro x
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => (st_I_f A gq hcq hpq j i).const_mul _]
  simp only [integral_const_mul]

private lemma st_core_iii {m n : ℕ} (A : Mat m n) (g0 g1 g2 : ℝ → ℝ)
    (hd0 : ∀ u, HasDerivAt g0 (g1 u) u) (hd1 : ∀ u, HasDerivAt g1 (g2 u) u)
    (c0 : Continuous g0) (c1 : Continuous g1) (c2 : Continuous g2)
    (p0 : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g0 u| ≤ K * (1 + |u| ^ k))
    (p1 : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g1 u| ≤ K * (1 + |u| ^ k))
    (p2 : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g2 u| ≤ K * (1 + |u| ^ k)) :
    Muon.mean (gaussPair m n) (fun x => g0 (resid A x) • (Muon.outer x.1 x.1 - 1)) =
      A * Muon.mean (gaussPair m n) (fun x => g2 (resid A x) • Muon.outer x.2 x.2) * Aᵀ := by
  ext k l
  have h1 : ∫ x, g0 (resid A x) * (x.1 k * x.1 l - (1 : Mat m m) k l) ∂(gaussPair m n) =
      ∑ j, A k j * ∑ i, A l i * ∫ x, g2 (resid A x) * (x.2 j * x.2 i) ∂(gaussPair m n) := by
    have e : ∀ x : Vec m × Vec n, g0 (resid A x) * (x.1 k * x.1 l - (1 : Mat m m) k l) =
        x.1 k * (x.1 l * g0 (resid A x)) - (1 : Mat m m) k l * g0 (resid A x) := fun x => by ring
    simp_rw [e]
    rw [integral_sub (st_I_a A g0 c0 p0 k l) (st_I_b A g0 c0 p0 _),
      st_T2 A g0 g1 hd0 c0 c1 p0 p1 k l, integral_const_mul]
    have e2 : (if l = k then (1 : ℝ) else 0) = (1 : Mat m m) k l := by
      rw [Matrix.one_apply]; simp only [eq_comm]
    rw [e2, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [st_T3 A g1 g2 hd1 c1 c2 p1 p2 l j]
  simp only [Muon.mean, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [h1]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma st_core_i {m n : ℕ} (A : Mat m n) (g0 g1 g2 g3 : ℝ → ℝ)
    (hd0 : ∀ u, HasDerivAt g0 (g1 u) u) (hd1 : ∀ u, HasDerivAt g1 (g2 u) u)
    (hd2 : ∀ u, HasDerivAt g2 (g3 u) u)
    (c0 : Continuous g0) (c1 : Continuous g1) (c2 : Continuous g2) (c3 : Continuous g3)
    (p0 : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g0 u| ≤ K * (1 + |u| ^ k))
    (p1 : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g1 u| ≤ K * (1 + |u| ^ k))
    (p2 : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g2 u| ≤ K * (1 + |u| ^ k))
    (p3 : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g3 u| ≤ K * (1 + |u| ^ k)) :
    Muon.mean (gaussPair m n) (fun x => g0 (resid A x) • Muon.outer x.1 x.2) =
      (∫ x, g1 (resid A x) ∂(gaussPair m n)) • A +
        A * Muon.mean (gaussPair m n) (fun x => g3 (resid A x) • Muon.outer x.2 x.2) * Aᵀ * A := by
  ext k l
  have h1 : ∫ x, g0 (resid A x) * (x.1 k * x.2 l) ∂(gaussPair m n) =
      ∑ a, A a l * ((if a = k then (1 : ℝ) else 0) * ∫ x, g1 (resid A x) ∂(gaussPair m n) +
        ∑ j, A k j * ∑ i, A a i *
          ∫ x, g3 (resid A x) * (x.2 j * x.2 i) ∂(gaussPair m n)) := by
    have e : ∀ x : Vec m × Vec n, g0 (resid A x) * (x.1 k * x.2 l) =
        x.2 l * (x.1 k * g0 (resid A x)) := fun x => by ring
    simp_rw [e]
    rw [st_LW1 A g0 g1 hd0 c0 c1 p0 p1 k l]
    have e2 : ∀ x : Vec m × Vec n, x.1 k * (g1 (resid A x) * (x.1 ᵥ* A) l) =
        ∑ a, A a l * (x.1 k * (x.1 a * g1 (resid A x))) := by
      intro x
      simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    simp_rw [e2]
    rw [integral_finsetSum _ fun a _ => (st_I_a A g1 c1 p1 k a).const_mul _]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_const_mul, st_T2 A g1 g2 hd1 c1 c2 p1 p2 k a]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [st_T3 A g2 g3 hd2 c2 c3 p2 p3 a j]
  simp only [Muon.mean, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [h1]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · simp [mul_comm]
  · simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

private lemma st_hd {f : ℝ → ℝ} {N : ℕ} (hf : ContDiff ℝ (N : WithTop ℕ∞) f) (j : ℕ) (hj : j < N)
    (u : ℝ) : HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f u) u := by
  have hdiff := hf.differentiable_iteratedDeriv j (by exact_mod_cast hj)
  have := (hdiff u).hasDerivAt
  rwa [← congrFun iteratedDeriv_succ u] at this

private lemma st_cont {f : ℝ → ℝ} {N : ℕ} (hf : ContDiff ℝ (N : WithTop ℕ∞) f) (j : ℕ)
    (hj : j ≤ N) : Continuous (iteratedDeriv j f) :=
  hf.continuous_iteratedDeriv j (by exact_mod_cast hj)


private lemma st_fro_nn {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma st_fro_transpose {k l : ℕ} (A : Mat k l) : fro Aᵀ = fro A := by
  unfold fro
  congr 1
  exact Finset.sum_comm

private lemma st_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma st_opNorm_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ opNorm A := by
  unfold opNorm
  exact norm_nonneg _

open scoped Matrix.Norms.L2Operator in
private lemma st_opNorm_mul_le {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B

private lemma st_fro_sq {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma st_fro_mul_le_left {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ opNorm M * fro N := by
  have hcol : ∀ j : Fin r, ∑ i, (M * N) i j ^ 2 ≤ opNorm M ^ 2 * ∑ k, N k j ^ 2 := by
    intro j
    obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin q), ∀ k, v.ofLp k = N k j :=
      ⟨(EuclideanSpace.equiv (Fin q) ℝ).symm (fun k => N k j), fun k => rfl⟩
    have h1 : ‖(EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)‖ ≤ opNorm M * ‖v‖ := by
      rw [opNorm_eq_norm]
      exact Matrix.l2_opNorm_mulVec M v
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at h2
    have e1 : ∀ i, ((EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)).ofLp i = (M * N) i j := by
      intro i
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, hv]
    have e2 : ∑ k, v.ofLp k ^ 2 = ∑ k, N k j ^ 2 :=
      Finset.sum_congr rfl fun k _ => by rw [hv]
    simp only [e1, e2] at h2
    exact h2
  have hfro : fro (M * N) ^ 2 ≤ (opNorm M * fro N) ^ 2 := by
    rw [st_fro_sq, mul_pow, st_fro_sq, Finset.sum_comm]
    calc ∑ j, ∑ i, (M * N) i j ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, N k j ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, N k j ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (st_fro_nn _) (mul_nonneg (st_opNorm_nonneg M) (st_fro_nn N))
    two_ne_zero).mp hfro

private lemma st_fro_mul_le_right {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ fro M * opNorm N := by
  have h := st_fro_mul_le_left Nᵀ Mᵀ
  rw [st_opNorm_transpose, st_fro_transpose, ← Matrix.transpose_mul, st_fro_transpose] at h
  linarith [mul_comm (opNorm N) (fro M)]

private lemma st_opNorm_le_of_sq {m n : ℕ} (U : Mat m n) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ x : Fin n → ℝ, ∑ k, (U *ᵥ x) k ^ 2 ≤ M ^ 2 * ∑ i, x i ^ 2) : opNorm U ≤ M := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x => ?_
  show ‖Matrix.toEuclideanLin U x‖ ≤ M * ‖x‖
  have hx := h (WithLp.ofLp x)
  have hsq : ‖Matrix.toEuclideanLin U x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Real.norm_eq_abs, sq_abs] using hx
  nlinarith [norm_nonneg (Matrix.toEuclideanLin U x), mul_nonneg hM (norm_nonneg x)]

private lemma st_int_snd {m n : ℕ} (F : Vec n → ℝ) (hF : Continuous F) :
    ∫ x, F x.2 ∂(gaussPair m n) = ∫ w, F w ∂(Muon.Foundations.stdGaussianPi n) := by
  have hmap : (gaussPair m n).map Prod.snd = Muon.Foundations.stdGaussianPi n := by
    unfold gaussPair
    rw [Measure.map_snd_prod]; simp
  conv_rhs => rw [← hmap]
  rw [integral_map measurable_snd.aemeasurable hF.aestronglyMeasurable]

private lemma st_lin_sq_int {n : ℕ} (v : Vec n) :
    Integrable (fun w : Vec n => (∑ i, v i * w i) ^ 2) (Muon.Foundations.stdGaussianPi n) := by
  have e : ∀ w : Vec n, (∑ i, v i * w i) ^ 2 = ∑ i, ∑ j, v i * v j * (w i * w j) := by
    intro w
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (de_gtwo i j).const_mul _

private lemma st_lin_sq {n : ℕ} (v : Vec n) :
    ∫ w, (∑ i, v i * w i) ^ 2 ∂(Muon.Foundations.stdGaussianPi n) = ∑ i, v i ^ 2 := by
  have e : ∀ w : Vec n, (∑ i, v i * w i) ^ 2 = ∑ i, ∑ j, v i * v j * (w i * w j) := by
    intro w
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (de_gtwo i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (de_gtwo i j).const_mul _]
  simp only [integral_const_mul, de_m2]
  simp [sq]

private lemma st_opNorm_mean {m n : ℕ} (A : Mat m n) (g : ℝ → ℝ) (hc : Continuous g)
    (hp : ∃ (K : ℝ) (k : ℕ), ∀ u : ℝ, |g u| ≤ K * (1 + |u| ^ k)) (M : ℝ)
    (hM : ∀ u : ℝ, |g u| ≤ M) :
    opNorm (Muon.mean (gaussPair m n)
      (fun x => g (resid A x) • Muon.outer x.2 x.2)) ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine st_opNorm_le_of_sq _ M hM0 fun v => ?_
  set X := Muon.mean (gaussPair m n) (fun x => g (resid A x) • Muon.outer x.2 x.2) with hX
  have hXe : ∀ j i, X j i = ∫ x, g (resid A x) * (x.2 j * x.2 i) ∂(gaussPair m n) := by
    intro j i
    simp [hX, Muon.mean, Matrix.vecMulVec_apply]
  set u : Vec n := X *ᵥ v with hu
  set a : Vec m × Vec n → ℝ := fun x => ∑ k, u k * x.2 k with ha
  set b : Vec m × Vec n → ℝ := fun x => ∑ i, v i * x.2 i with hb
  have e : ∀ x : Vec m × Vec n, g (resid A x) * (a x * b x) =
      ∑ k, ∑ i, u k * v i * (g (resid A x) * (x.2 k * x.2 i)) := by
    intro x
    simp only [ha, hb]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hS : ∑ k, u k ^ 2 = ∫ x, g (resid A x) * (a x * b x) ∂(gaussPair m n) := by
    simp_rw [e]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ =>
      (st_I_f A g hc hp k i).const_mul _]
    have : ∀ k, ∫ x, ∑ i, u k * v i * (g (resid A x) * (x.2 k * x.2 i)) ∂(gaussPair m n) =
        u k * ∑ i, X k i * v i := by
      intro k
      rw [integral_finsetSum _ fun i _ => (st_I_f A g hc hp k i).const_mul _, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, hXe]; ring
    simp_rw [this]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hu, Matrix.mulVec, dotProduct, sq]
  have ia : Integrable (fun x : Vec m × Vec n => (a x) ^ 2) (gaussPair m n) := by
    unfold gaussPair
    exact (st_lin_sq_int u).comp_snd _
  have ib : Integrable (fun x : Vec m × Vec n => (b x) ^ 2) (gaussPair m n) := by
    unfold gaussPair
    exact (st_lin_sq_int v).comp_snd _
  have ig : Integrable (fun x : Vec m × Vec n => g (resid A x) * (a x * b x)) (gaussPair m n) := by
    simp_rw [e]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ =>
      (st_I_f A g hc hp k i).const_mul _
  have ha2 : ∫ x, (a x) ^ 2 ∂(gaussPair m n) = ∑ k, u k ^ 2 := by
    have := st_int_snd (m := m) (n := n) (fun w => (∑ i, u i * w i) ^ 2)
      (by fun_prop)
    simpa [ha, st_lin_sq] using this
  have hb2 : ∫ x, (b x) ^ 2 ∂(gaussPair m n) = ∑ i, v i ^ 2 := by
    have := st_int_snd (m := m) (n := n) (fun w => (∑ i, v i * w i) ^ 2)
      (by fun_prop)
    simpa [hb, st_lin_sq] using this
  have hmono : ∫ x, g (resid A x) * (a x * b x) ∂(gaussPair m n) ≤
      ∫ x, ((a x) ^ 2 + M ^ 2 * (b x) ^ 2) / 2 ∂(gaussPair m n) := by
    refine integral_mono ig ((ia.add (ib.const_mul _)).div_const 2) fun x => ?_
    have h1 : |g (resid A x) * (a x * b x)| ≤ M * (|a x| * |b x|) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (hM _) le_rfl (by positivity) hM0
    have h2 : g (resid A x) * (a x * b x) ≤ M * (|a x| * |b x|) := (le_abs_self _).trans h1
    nlinarith [sq_nonneg (|a x| - M * |b x|), sq_abs (a x), sq_abs (b x)]
  have hrhs : ∫ x, ((a x) ^ 2 + M ^ 2 * (b x) ^ 2) / 2 ∂(gaussPair m n) =
      (∑ k, u k ^ 2 + M ^ 2 * ∑ i, v i ^ 2) / 2 := by
    rw [integral_div, integral_add ia (ib.const_mul _), integral_const_mul, ha2, hb2]
  rw [hS] at *
  linarith


/-- `lem:app-de-stein`, part (i), snapshot `cr-2026-10-23`. Verbatim from the frozen source
(`section.tex` l.986–1002):

\begin{lemma}[Gaussian response]\label{lem:app-de-stein}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic, $z\sim\mathcal N(0,\Id_{\Nout})$,
$w\sim\mathcal N(0,\Id_{\Nin})$ independent, and $d=z^\T Aw$. Let
$f\in C^3(\R)$ and $\psi\in C^2(\R)$ have polynomially bounded derivatives up
to the stated orders. Then
\begin{align}
\EE[(z\tensor w)\,f(d)]&=A\,\EE f'(d)+A\,\EE[(w\tensor w)\,f'''(d)]\,A^\T A,
\label{eqn:app-de-stein1}\\
\norm{\EE[(z\tensor w)\,f(d)]-A\,\EE f'(d)}_\F&\le\norm{f'''}_\infty\norm A^2\norm A_\F,
\notag\\
\EE[(z\tensor z-\Id)\,\psi(d)]&=A\,\EE[(w\tensor w)\,\psi''(d)]\,A^\T,
\label{eqn:app-de-stein2}\\
\norm{\EE[(z\tensor z-\Id)\,\psi(d)]}_\F&\le\norm{\psi''}_\infty\norm A\norm A_\F,
\notag
\end{align}
and both \cref{eqn:app-de-stein1,eqn:app-de-stein2} hold with $(z,w,A)$ replaced by $(w,z,A^\T)$.
\end{lemma}
-/
theorem lem_app_de_stein_i {m n : ℕ} (A : Mat m n) (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f)
    (hfp : ∀ j : ℕ, j ≤ 3 → ∃ (K : ℝ) (k : ℕ), ∀ x : ℝ, |iteratedDeriv j f x| ≤ K * (1 + |x| ^ k)) :
    Muon.mean (gaussPair m n) (fun x => f (resid A x) • Muon.outer x.1 x.2) =
      (∫ x, deriv f (resid A x) ∂(gaussPair m n)) • A +
        A * Muon.mean (gaussPair m n) (fun x => iteratedDeriv 3 f (resid A x) • Muon.outer x.2 x.2)
          * Aᵀ * A := by
  have hf' : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) f := by exact_mod_cast hf
  have := st_core_i A (iteratedDeriv 0 f) (iteratedDeriv 1 f) (iteratedDeriv 2 f) (iteratedDeriv 3 f)
    (st_hd hf' 0 (by norm_num)) (st_hd hf' 1 (by norm_num)) (st_hd hf' 2 (by norm_num))
    (st_cont hf' 0 (by norm_num)) (st_cont hf' 1 (by norm_num)) (st_cont hf' 2 (by norm_num))
    (st_cont hf' 3 (by norm_num)) (hfp 0 (by norm_num)) (hfp 1 (by norm_num))
    (hfp 2 (by norm_num)) (hfp 3 (by norm_num))
  simpa only [iteratedDeriv_zero, iteratedDeriv_one] using this

/-- `lem:app-de-stein`, part (ii), snapshot `cr-2026-10-23`. Verbatim from the frozen source
(`section.tex` l.986–1002):

\begin{lemma}[Gaussian response]\label{lem:app-de-stein}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic, $z\sim\mathcal N(0,\Id_{\Nout})$,
$w\sim\mathcal N(0,\Id_{\Nin})$ independent, and $d=z^\T Aw$. Let
$f\in C^3(\R)$ and $\psi\in C^2(\R)$ have polynomially bounded derivatives up
to the stated orders. Then
\begin{align}
\EE[(z\tensor w)\,f(d)]&=A\,\EE f'(d)+A\,\EE[(w\tensor w)\,f'''(d)]\,A^\T A,
\label{eqn:app-de-stein1}\\
\norm{\EE[(z\tensor w)\,f(d)]-A\,\EE f'(d)}_\F&\le\norm{f'''}_\infty\norm A^2\norm A_\F,
\notag\\
\EE[(z\tensor z-\Id)\,\psi(d)]&=A\,\EE[(w\tensor w)\,\psi''(d)]\,A^\T,
\label{eqn:app-de-stein2}\\
\norm{\EE[(z\tensor z-\Id)\,\psi(d)]}_\F&\le\norm{\psi''}_\infty\norm A\norm A_\F,
\notag
\end{align}
and both \cref{eqn:app-de-stein1,eqn:app-de-stein2} hold with $(z,w,A)$ replaced by $(w,z,A^\T)$.
\end{lemma}
-/
theorem lem_app_de_stein_ii {m n : ℕ} (A : Mat m n) (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f)
    (hfp : ∀ j : ℕ, j ≤ 3 → ∃ (K : ℝ) (k : ℕ), ∀ x : ℝ, |iteratedDeriv j f x| ≤ K * (1 + |x| ^ k)) :
    ∀ M : ℝ, (∀ x : ℝ, |iteratedDeriv 3 f x| ≤ M) →
      fro (Muon.mean (gaussPair m n) (fun x => f (resid A x) • Muon.outer x.1 x.2) -
          (∫ x, deriv f (resid A x) ∂(gaussPair m n)) • A) ≤
        M * opNorm A ^ 2 * fro A := by
  intro M hM
  have hf' : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) f := by exact_mod_cast hf
  have h := lem_app_de_stein_i A f hf hfp
  have hX := st_opNorm_mean A (iteratedDeriv 3 f) (st_cont hf' 3 (by norm_num)) (hfp 3 (by norm_num)) M hM
  set X3 := Muon.mean (gaussPair m n)
    (fun x => iteratedDeriv 3 f (resid A x) • Muon.outer x.2 x.2) with hX3
  have e : Muon.mean (gaussPair m n) (fun x => f (resid A x) • Muon.outer x.1 x.2) -
      (∫ x, deriv f (resid A x) ∂(gaussPair m n)) • A = A * X3 * Aᵀ * A := by
    rw [h]; abel
  rw [e]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  calc fro (A * X3 * Aᵀ * A) ≤ opNorm (A * X3 * Aᵀ) * fro A := st_fro_mul_le_left _ _
    _ ≤ (opNorm (A * X3) * opNorm Aᵀ) * fro A :=
        mul_le_mul_of_nonneg_right (st_opNorm_mul_le _ _) (st_fro_nn _)
    _ ≤ ((opNorm A * opNorm X3) * opNorm Aᵀ) * fro A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (st_opNorm_mul_le _ _)
          (st_opNorm_nonneg _)) (st_fro_nn _)
    _ ≤ ((opNorm A * M) * opNorm A) * fro A := by
        rw [st_opNorm_transpose]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hX (st_opNorm_nonneg _)) (st_opNorm_nonneg _)) (st_fro_nn _)
    _ = M * opNorm A ^ 2 * fro A := by ring

/-- `lem:app-de-stein`, part (iii), snapshot `cr-2026-10-23`. Verbatim from the frozen source
(`section.tex` l.986–1002):

\begin{lemma}[Gaussian response]\label{lem:app-de-stein}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic, $z\sim\mathcal N(0,\Id_{\Nout})$,
$w\sim\mathcal N(0,\Id_{\Nin})$ independent, and $d=z^\T Aw$. Let
$f\in C^3(\R)$ and $\psi\in C^2(\R)$ have polynomially bounded derivatives up
to the stated orders. Then
\begin{align}
\EE[(z\tensor w)\,f(d)]&=A\,\EE f'(d)+A\,\EE[(w\tensor w)\,f'''(d)]\,A^\T A,
\label{eqn:app-de-stein1}\\
\norm{\EE[(z\tensor w)\,f(d)]-A\,\EE f'(d)}_\F&\le\norm{f'''}_\infty\norm A^2\norm A_\F,
\notag\\
\EE[(z\tensor z-\Id)\,\psi(d)]&=A\,\EE[(w\tensor w)\,\psi''(d)]\,A^\T,
\label{eqn:app-de-stein2}\\
\norm{\EE[(z\tensor z-\Id)\,\psi(d)]}_\F&\le\norm{\psi''}_\infty\norm A\norm A_\F,
\notag
\end{align}
and both \cref{eqn:app-de-stein1,eqn:app-de-stein2} hold with $(z,w,A)$ replaced by $(w,z,A^\T)$.
\end{lemma}
-/
theorem lem_app_de_stein_iii {m n : ℕ} (A : Mat m n) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hψp : ∀ j : ℕ, j ≤ 2 → ∃ (K : ℝ) (k : ℕ), ∀ x : ℝ, |iteratedDeriv j ψ x| ≤ K * (1 + |x| ^ k)) :
    Muon.mean (gaussPair m n) (fun x => ψ (resid A x) • (Muon.outer x.1 x.1 - 1)) =
      A * Muon.mean (gaussPair m n) (fun x => iteratedDeriv 2 ψ (resid A x) • Muon.outer x.2 x.2) * Aᵀ := by
  have hf' : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) ψ := by exact_mod_cast hψ
  have := st_core_iii A (iteratedDeriv 0 ψ) (iteratedDeriv 1 ψ) (iteratedDeriv 2 ψ)
    (st_hd hf' 0 (by norm_num)) (st_hd hf' 1 (by norm_num))
    (st_cont hf' 0 (by norm_num)) (st_cont hf' 1 (by norm_num)) (st_cont hf' 2 (by norm_num))
    (hψp 0 (by norm_num)) (hψp 1 (by norm_num)) (hψp 2 (by norm_num))
  simpa only [iteratedDeriv_zero] using this

/-- `lem:app-de-stein`, part (iv), snapshot `cr-2026-10-23`. Verbatim from the frozen source
(`section.tex` l.986–1002):

\begin{lemma}[Gaussian response]\label{lem:app-de-stein}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic, $z\sim\mathcal N(0,\Id_{\Nout})$,
$w\sim\mathcal N(0,\Id_{\Nin})$ independent, and $d=z^\T Aw$. Let
$f\in C^3(\R)$ and $\psi\in C^2(\R)$ have polynomially bounded derivatives up
to the stated orders. Then
\begin{align}
\EE[(z\tensor w)\,f(d)]&=A\,\EE f'(d)+A\,\EE[(w\tensor w)\,f'''(d)]\,A^\T A,
\label{eqn:app-de-stein1}\\
\norm{\EE[(z\tensor w)\,f(d)]-A\,\EE f'(d)}_\F&\le\norm{f'''}_\infty\norm A^2\norm A_\F,
\notag\\
\EE[(z\tensor z-\Id)\,\psi(d)]&=A\,\EE[(w\tensor w)\,\psi''(d)]\,A^\T,
\label{eqn:app-de-stein2}\\
\norm{\EE[(z\tensor z-\Id)\,\psi(d)]}_\F&\le\norm{\psi''}_\infty\norm A\norm A_\F,
\notag
\end{align}
and both \cref{eqn:app-de-stein1,eqn:app-de-stein2} hold with $(z,w,A)$ replaced by $(w,z,A^\T)$.
\end{lemma}
-/
theorem lem_app_de_stein_iv {m n : ℕ} (A : Mat m n) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hψp : ∀ j : ℕ, j ≤ 2 → ∃ (K : ℝ) (k : ℕ), ∀ x : ℝ, |iteratedDeriv j ψ x| ≤ K * (1 + |x| ^ k)) :
    ∀ M : ℝ, (∀ x : ℝ, |iteratedDeriv 2 ψ x| ≤ M) →
      fro (Muon.mean (gaussPair m n) (fun x => ψ (resid A x) • (Muon.outer x.1 x.1 - 1))) ≤
        M * opNorm A * fro A := by
  intro M hM
  have hf' : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) ψ := by exact_mod_cast hψ
  have h := lem_app_de_stein_iii A ψ hψ hψp
  have hX := st_opNorm_mean A (iteratedDeriv 2 ψ) (st_cont hf' 2 (by norm_num)) (hψp 2 (by norm_num)) M hM
  set X2 := Muon.mean (gaussPair m n)
    (fun x => iteratedDeriv 2 ψ (resid A x) • Muon.outer x.2 x.2) with hX2
  rw [h]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  calc fro (A * X2 * Aᵀ) ≤ fro (A * X2) * opNorm Aᵀ := st_fro_mul_le_right _ _
    _ ≤ (fro A * opNorm X2) * opNorm Aᵀ :=
        mul_le_mul_of_nonneg_right (st_fro_mul_le_right _ _) (st_opNorm_nonneg _)
    _ ≤ (fro A * M) * opNorm A := by
        rw [st_opNorm_transpose]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX (st_fro_nn _))
          (st_opNorm_nonneg _)
    _ = M * opNorm A * fro A := by ring

/-- `lem:app-de-stein`, part (v) (the transposed form of part (i) with `(z, w, A)` replaced by
`(w, z, Aᵀ)`), snapshot `cr-2026-10-23`. Verbatim from the frozen source (`section.tex`
l.986–1002):

\begin{lemma}[Gaussian response]\label{lem:app-de-stein}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic, $z\sim\mathcal N(0,\Id_{\Nout})$,
$w\sim\mathcal N(0,\Id_{\Nin})$ independent, and $d=z^\T Aw$. Let
$f\in C^3(\R)$ and $\psi\in C^2(\R)$ have polynomially bounded derivatives up
to the stated orders. Then
\begin{align}
\EE[(z\tensor w)\,f(d)]&=A\,\EE f'(d)+A\,\EE[(w\tensor w)\,f'''(d)]\,A^\T A,
\label{eqn:app-de-stein1}\\
\norm{\EE[(z\tensor w)\,f(d)]-A\,\EE f'(d)}_\F&\le\norm{f'''}_\infty\norm A^2\norm A_\F,
\notag\\
\EE[(z\tensor z-\Id)\,\psi(d)]&=A\,\EE[(w\tensor w)\,\psi''(d)]\,A^\T,
\label{eqn:app-de-stein2}\\
\norm{\EE[(z\tensor z-\Id)\,\psi(d)]}_\F&\le\norm{\psi''}_\infty\norm A\norm A_\F,
\notag
\end{align}
and both \cref{eqn:app-de-stein1,eqn:app-de-stein2} hold with $(z,w,A)$ replaced by $(w,z,A^\T)$.
\end{lemma}
-/
theorem lem_app_de_stein_v {m n : ℕ} (A : Mat m n) (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f)
    (hfp : ∀ j : ℕ, j ≤ 3 → ∃ (K : ℝ) (k : ℕ), ∀ x : ℝ, |iteratedDeriv j f x| ≤ K * (1 + |x| ^ k)) :
    Muon.mean (gaussPair n m) (fun x => f (resid Aᵀ x) • Muon.outer x.1 x.2) =
      (∫ x, deriv f (resid Aᵀ x) ∂(gaussPair n m)) • Aᵀ +
        Aᵀ * Muon.mean (gaussPair n m) (fun x => iteratedDeriv 3 f (resid Aᵀ x) • Muon.outer x.2 x.2)
          * A * Aᵀ := by
  have := lem_app_de_stein_i Aᵀ f hf hfp
  rwa [Matrix.transpose_transpose] at this

/-- `lem:app-de-stein`, part (vi) (the transposed form of part (ii)), snapshot `cr-2026-10-23`.
Verbatim from the frozen source (`section.tex` l.986–1002):

\begin{lemma}[Gaussian response]\label{lem:app-de-stein}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic, $z\sim\mathcal N(0,\Id_{\Nout})$,
$w\sim\mathcal N(0,\Id_{\Nin})$ independent, and $d=z^\T Aw$. Let
$f\in C^3(\R)$ and $\psi\in C^2(\R)$ have polynomially bounded derivatives up
to the stated orders. Then
\begin{align}
\EE[(z\tensor w)\,f(d)]&=A\,\EE f'(d)+A\,\EE[(w\tensor w)\,f'''(d)]\,A^\T A,
\label{eqn:app-de-stein1}\\
\norm{\EE[(z\tensor w)\,f(d)]-A\,\EE f'(d)}_\F&\le\norm{f'''}_\infty\norm A^2\norm A_\F,
\notag\\
\EE[(z\tensor z-\Id)\,\psi(d)]&=A\,\EE[(w\tensor w)\,\psi''(d)]\,A^\T,
\label{eqn:app-de-stein2}\\
\norm{\EE[(z\tensor z-\Id)\,\psi(d)]}_\F&\le\norm{\psi''}_\infty\norm A\norm A_\F,
\notag
\end{align}
and both \cref{eqn:app-de-stein1,eqn:app-de-stein2} hold with $(z,w,A)$ replaced by $(w,z,A^\T)$.
\end{lemma}
-/
theorem lem_app_de_stein_vi {m n : ℕ} (A : Mat m n) (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f)
    (hfp : ∀ j : ℕ, j ≤ 3 → ∃ (K : ℝ) (k : ℕ), ∀ x : ℝ, |iteratedDeriv j f x| ≤ K * (1 + |x| ^ k)) :
    ∀ M : ℝ, (∀ x : ℝ, |iteratedDeriv 3 f x| ≤ M) →
      fro (Muon.mean (gaussPair n m) (fun x => f (resid Aᵀ x) • Muon.outer x.1 x.2) -
          (∫ x, deriv f (resid Aᵀ x) ∂(gaussPair n m)) • Aᵀ) ≤
        M * opNorm Aᵀ ^ 2 * fro Aᵀ :=
  lem_app_de_stein_ii Aᵀ f hf hfp

/-- `lem:app-de-stein`, part (vii) (the transposed form of part (iii)), snapshot `cr-2026-10-23`.
Verbatim from the frozen source (`section.tex` l.986–1002):

\begin{lemma}[Gaussian response]\label{lem:app-de-stein}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic, $z\sim\mathcal N(0,\Id_{\Nout})$,
$w\sim\mathcal N(0,\Id_{\Nin})$ independent, and $d=z^\T Aw$. Let
$f\in C^3(\R)$ and $\psi\in C^2(\R)$ have polynomially bounded derivatives up
to the stated orders. Then
\begin{align}
\EE[(z\tensor w)\,f(d)]&=A\,\EE f'(d)+A\,\EE[(w\tensor w)\,f'''(d)]\,A^\T A,
\label{eqn:app-de-stein1}\\
\norm{\EE[(z\tensor w)\,f(d)]-A\,\EE f'(d)}_\F&\le\norm{f'''}_\infty\norm A^2\norm A_\F,
\notag\\
\EE[(z\tensor z-\Id)\,\psi(d)]&=A\,\EE[(w\tensor w)\,\psi''(d)]\,A^\T,
\label{eqn:app-de-stein2}\\
\norm{\EE[(z\tensor z-\Id)\,\psi(d)]}_\F&\le\norm{\psi''}_\infty\norm A\norm A_\F,
\notag
\end{align}
and both \cref{eqn:app-de-stein1,eqn:app-de-stein2} hold with $(z,w,A)$ replaced by $(w,z,A^\T)$.
\end{lemma}
-/
theorem lem_app_de_stein_vii {m n : ℕ} (A : Mat m n) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hψp : ∀ j : ℕ, j ≤ 2 → ∃ (K : ℝ) (k : ℕ), ∀ x : ℝ, |iteratedDeriv j ψ x| ≤ K * (1 + |x| ^ k)) :
    Muon.mean (gaussPair n m) (fun x => ψ (resid Aᵀ x) • (Muon.outer x.1 x.1 - 1)) =
      Aᵀ * Muon.mean (gaussPair n m) (fun x => iteratedDeriv 2 ψ (resid Aᵀ x) • Muon.outer x.2 x.2) * A := by
  have := lem_app_de_stein_iii Aᵀ ψ hψ hψp
  rwa [Matrix.transpose_transpose] at this

/-- `lem:app-de-stein`, part (viii) (the transposed form of part (iv)), snapshot `cr-2026-10-23`.
Verbatim from the frozen source (`section.tex` l.986–1002):

\begin{lemma}[Gaussian response]\label{lem:app-de-stein}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic, $z\sim\mathcal N(0,\Id_{\Nout})$,
$w\sim\mathcal N(0,\Id_{\Nin})$ independent, and $d=z^\T Aw$. Let
$f\in C^3(\R)$ and $\psi\in C^2(\R)$ have polynomially bounded derivatives up
to the stated orders. Then
\begin{align}
\EE[(z\tensor w)\,f(d)]&=A\,\EE f'(d)+A\,\EE[(w\tensor w)\,f'''(d)]\,A^\T A,
\label{eqn:app-de-stein1}\\
\norm{\EE[(z\tensor w)\,f(d)]-A\,\EE f'(d)}_\F&\le\norm{f'''}_\infty\norm A^2\norm A_\F,
\notag\\
\EE[(z\tensor z-\Id)\,\psi(d)]&=A\,\EE[(w\tensor w)\,\psi''(d)]\,A^\T,
\label{eqn:app-de-stein2}\\
\norm{\EE[(z\tensor z-\Id)\,\psi(d)]}_\F&\le\norm{\psi''}_\infty\norm A\norm A_\F,
\notag
\end{align}
and both \cref{eqn:app-de-stein1,eqn:app-de-stein2} hold with $(z,w,A)$ replaced by $(w,z,A^\T)$.
\end{lemma}
-/
theorem lem_app_de_stein_viii {m n : ℕ} (A : Mat m n) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hψp : ∀ j : ℕ, j ≤ 2 → ∃ (K : ℝ) (k : ℕ), ∀ x : ℝ, |iteratedDeriv j ψ x| ≤ K * (1 + |x| ^ k)) :
    ∀ M : ℝ, (∀ x : ℝ, |iteratedDeriv 2 ψ x| ≤ M) →
      fro (Muon.mean (gaussPair n m) (fun x => ψ (resid Aᵀ x) • (Muon.outer x.1 x.1 - 1))) ≤
        M * opNorm Aᵀ * fro Aᵀ :=
  lem_app_de_stein_iv Aᵀ ψ hψ hψp

end Muon.DetEquiv

end

import Muon.Foundations.Gaussian
import Muon.Foundations.GaussianCombinatorics
import Muon.SignSGD.Defs

/-!
# Appendix I (SignSGD): exact coordinate moments and characteristic-function decay

Interface for the labels `lem:app-sgd-moments` (parts (i)–(vii)) and `lem:app-sgd-decay`, with the
objects they use (the single-sample coordinate `X`, the standardized `Y`, `ψ`, `C_ch`) and the
helper statements of card §3b for L-I.5. Source of record: snapshot `cr-2026-10-23`,
`sections/08-signsgd/section.tex` l. 256–284 (standing hypotheses and `lem:app-sgd-moments`) and
l. 335–347 (`eqn:app-sgd-psi`, `lem:app-sgd-decay`). Docstrings carry the LaTeX verbatim.

Standing hypotheses (l. 256–266), made explicit. `Σin = Id` and `Σout = Id` are carried by the law
`gaussBatch`: one sample `(z, w)` with `z`, `w` independent standard Gaussian vectors. The state
`Δ ≠ 0` is deterministic and is an explicit hypothesis of every statement. The entry `(i, j)` is
fixed. The block notation of l. 256–266 is encoded with zero padding instead of deleted indices:
`sgdDeletedBlock` is `Δ` with row `i` and column `j` set to zero, `sgdRow` is `r` (zero at `j`) and
`sgdCol` is `q` (zero at `i`). Every norm and bilinear form in the statements is the one of the
deleted-index object, because the padded entries contribute zero. The coordinates `ξ = z_i` and
`ζ = w_j` are `z i` and `w j`, so `X = (zᵀΔw) ξ ζ` is `sgdCoord`.

Expectations are integrals against `gaussBatch`. `Var` is `ProbabilityTheory.variance`, and `s` is
`sgdSd`. The standardized coordinate `Y = (X - Δ_ij)/s` is `sgdStdCoord`.

Quantifier order. The moment parts hold for all `Nout Nin : ℕ`, all `Δ ≠ 0`, all `i`, `j`; part (vi)
for all integers `p ≥ 1`. In `lem:app-sgd-decay` the bound holds for every `t ≠ 0` under the
hypothesis `‖Δ̄‖_F ≥ ‖Δ‖_F / 2`; `ψ` and `C_ch` depend on no dimension.

Declarations of record: `lem_app_sgd_moments_i` … `_vii`, `lem_app_sgd_decay`. Helper statements are
proved by the workers (see the result JSON for the proof cards). `sgdPsi` and `sgdCch` are defined
here, not in `Muon.SignSGD.Defs`; L-I.6 imports them from this module.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Muon.SignSGD

/-! ## Sample space and the single-sample coordinate -/

/-- The law of one sample `(z, w)` with `z ∼ N(0, Id_{Nout})` and `w ∼ N(0, Id_{Nin})`
independent: the standing hypotheses `Σout = Σin = Id` of l. 256–266. -/
noncomputable def gaussBatch (Nout Nin : ℕ) :
    Measure ((Fin Nout → ℝ) × (Fin Nin → ℝ)) :=
  (Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin)

/-- The single-sample coordinate `X = (zᵀΔw) ξ ζ` with `ξ = z_i`, `ζ = w_j`
(`eqn:app-sgd-coordinate`, l. 273–275). `B G°_{ij}` is the sum of `B` i.i.d. copies of `X`. -/
def sgdCoord {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout) (j : Fin Nin)
    (p : (Fin Nout → ℝ) × (Fin Nin → ℝ)) : ℝ :=
  dotProduct p.1 (Matrix.mulVec Δ p.2) * p.1 i * p.2 j

/-- `Δ̄`: the matrix `Δ` with row `i` and column `j` deleted (l. 258), written with zero entries in
the deleted row and column. -/
def sgdDeletedBlock {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) : Matrix (Fin Nout) (Fin Nin) ℝ :=
  fun k l => if k = i ∨ l = j then 0 else Δ k l

/-- `r = (Δ_{il})_{l ≠ j}`, the rest of row `i` (l. 258), zero at `l = j`. -/
def sgdRow {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout) (j : Fin Nin) :
    Fin Nin → ℝ :=
  fun l => if l = j then 0 else Δ i l

/-- `q = (Δ_{kj})_{k ≠ i}`, the rest of column `j` (l. 258), zero at `k = i`. -/
def sgdCol {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout) (j : Fin Nin) :
    Fin Nout → ℝ :=
  fun k => if k = i then 0 else Δ k j

/-- `s = (Var X)^{1/2}`, the standard deviation of the single-sample coordinate (l. 276). -/
noncomputable def sgdSd {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) : ℝ :=
  Real.sqrt (variance (sgdCoord Δ i j) (gaussBatch Nout Nin))

/-- The standardized coordinate `Y = (X - Δ_ij)/s` (l. 282). -/
noncomputable def sgdStdCoord {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) (p : (Fin Nout → ℝ) × (Fin Nin → ℝ)) : ℝ :=
  (sgdCoord Δ i j p - Δ i j) / sgdSd Δ i j

/-- `ψ(x) ≔ E(1 + x²ξ²ζ²)^{-1/2}` for `x ≥ 0`, with `ξ, ζ` independent standard Gaussians, and
`C_ch ≔ √8 (E|g|^{-1/2})²`. The LaTeX definition (`eqn:app-sgd-psi`, verbatim):

\begin{equation}\label{eqn:app-sgd-psi}
\psi(x)\defeq\EE\big(1+x^2\xi^2\zeta^2\big)^{-1/2}\quad(x\ge0),\qquad
C_{\rm ch}\defeq\sqrt8\,\big(\EE\abs g^{-1/2}\big)^2 .
\end{equation}
The function $\psi$ is nonincreasing, $\psi(x)<1$ for $x>0$, and
$\EE\abs g^{-1/2}=2^{-1/4}\Gamma(1/4)/\sqrt\pi$ is finite. -/
noncomputable def sgdPsi (x : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, (1 + x ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^ (-(1 / 2 : ℝ))
    ∂((gaussianReal 0 1).prod (gaussianReal 0 1))

/-- The constant `C_ch = √8 (E|g|^{-1/2})²` of `eqn:app-sgd-psi`; see `sgdPsi`. -/
noncomputable def sgdCch : ℝ :=
  Real.sqrt 8 * (∫ g, |g| ^ (-(1 / 2 : ℝ)) ∂(gaussianReal 0 1)) ^ 2

/-- The characteristic function `φ_Y(t) = E e^{i t Y}` of the standardized coordinate
(`lem:app-sgd-decay`). -/
noncomputable def sgdCharFunY {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) (t : ℝ) : ℂ :=
  ∫ p, Complex.exp ((t : ℂ) * Complex.I * ((sgdStdCoord Δ i j p : ℝ) : ℂ))
    ∂(gaussBatch Nout Nin)

private lemma sgd_psi_int_bdd {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun p : ℝ × ℝ => (1 + x ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^ (-(1 / 2 : ℝ)))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  refine Integrable.of_bound (Measurable.aestronglyMeasurable (by fun_prop)) 1 ?_
  refine Filter.Eventually.of_forall fun p => ?_
  have hb : (0:ℝ) ≤ 1 + x ^ 2 * p.1 ^ 2 * p.2 ^ 2 := by positivity
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hb _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (by positivity))
    (by norm_num)

private lemma sgd_psi_zero_null :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) {p : ℝ × ℝ | p.1 * p.2 = 0} = 0 := by
  have h1 : gaussianReal (0:ℝ) 1 ({0} : Set ℝ) = 0 :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero (Real.volume_singleton)
  have hs : {p : ℝ × ℝ | p.1 * p.2 = 0} ⊆ ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) ∪
      (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ) := by
    intro p hp
    have hp' : p.1 * p.2 = 0 := hp
    rcases mul_eq_zero.mp hp' with h | h
    · exact Or.inl (Set.mk_mem_prod (Set.mem_singleton_iff.mpr h) (Set.mem_univ _))
    · exact Or.inr (Set.mk_mem_prod (Set.mem_univ _) (Set.mem_singleton_iff.mpr h))
  refine measure_mono_null hs (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, h1, zero_mul]
  · rw [Measure.prod_prod, h1, mul_zero]

/-- Helper: `ψ` is nonincreasing on `[0, ∞)` (l. 338–340; asserted and unproved in the source). -/
theorem sgd_psi_antitoneOn : AntitoneOn sgdPsi (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx' : (0:ℝ) ≤ x := hx
  have hy' : (0:ℝ) ≤ y := hy
  unfold sgdPsi
  refine integral_mono (sgd_psi_int_bdd hy') (sgd_psi_int_bdd hx') (fun p => ?_)
  have h2 : x ^ 2 ≤ y ^ 2 := by nlinarith
  have h3 : x ^ 2 * p.1 ^ 2 * p.2 ^ 2 ≤ y ^ 2 * p.1 ^ 2 * p.2 ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (sq_nonneg _)) (sq_nonneg _)
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)

/-- Helper: `ψ(x) < 1` for `x > 0` (l. 338–340). -/
theorem sgd_psi_lt_one {x : ℝ} (hx : 0 < x) : sgdPsi x < 1 := by
  unfold sgdPsi
  have hint := sgd_psi_int_bdd hx.le
  have hg : Integrable (fun p : ℝ × ℝ => 1 - (1 + x ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^ (-(1 / 2 : ℝ)))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := (integrable_const (1:ℝ)).sub hint
  have hnn : 0 ≤ᵐ[(gaussianReal 0 1).prod (gaussianReal 0 1)]
      (fun p : ℝ × ℝ => 1 - (1 + x ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^ (-(1 / 2 : ℝ))) := by
    refine Filter.Eventually.of_forall fun p => ?_
    show (0:ℝ) ≤ 1 - (1 + x ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^ (-(1 / 2 : ℝ))
    have := Real.rpow_le_one_of_one_le_of_nonpos
      (le_add_of_nonneg_right (by positivity : (0:ℝ) ≤ x ^ 2 * p.1 ^ 2 * p.2 ^ 2))
      (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
    linarith
  have hsub : {p : ℝ × ℝ | p.1 * p.2 = 0}ᶜ ⊆
      Function.support (fun p : ℝ × ℝ => 1 - (1 + x ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^ (-(1 / 2 : ℝ))) := by
    intro p hp
    have hp' : p.1 * p.2 ≠ 0 := hp
    have hp1 : p.1 ≠ 0 := left_ne_zero_of_mul hp'
    have hp2 : p.2 ≠ 0 := right_ne_zero_of_mul hp'
    have hpos' : 0 < x ^ 2 * p.1 ^ 2 * p.2 ^ 2 := by positivity
    have hlt : (1 + x ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^ (-(1 / 2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
    show 1 - (1 + x ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^ (-(1 / 2 : ℝ)) ≠ 0
    intro h
    linarith
  have hms : MeasurableSet {p : ℝ × ℝ | p.1 * p.2 = 0} :=
    (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).measurableSet
  have hpos : 0 < (((gaussianReal 0 1).prod (gaussianReal 0 1)))
      (Function.support (fun p : ℝ × ℝ => 1 - (1 + x ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^ (-(1 / 2 : ℝ)))) := by
    calc (0:ENNReal) < ((gaussianReal 0 1).prod (gaussianReal 0 1)) {p : ℝ × ℝ | p.1 * p.2 = 0}ᶜ := by
          rw [prob_compl_eq_one_sub hms, sgd_psi_zero_null, tsub_zero]
          exact one_pos
      _ ≤ _ := measure_mono hsub
  have hpos_int := (integral_pos_iff_support_of_nonneg_ae hnn hg).mpr hpos
  have h1 : ∫ _ : ℝ × ℝ, (1:ℝ) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = 1 := by simp
  rw [integral_sub (integrable_const (1:ℝ)) hint, h1] at hpos_int
  linarith

/-- Auxiliary: `x ↦ |x|^{-1/2} e^{-x²/2}` is integrable on the positive half-line. -/
private lemma sgd_nh_half_line :
    IntegrableOn (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * x ^ 2))
      (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
    (s := -(1 / 2 : ℝ)) (by norm_num)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx' : (0 : ℝ) < x := hx
  simp only [abs_of_pos hx']

/-- Auxiliary: `x ↦ |x|^{-1/2} e^{-x²/2}` is integrable on `ℝ` (even extension of the half-line
piece, via `F = F₀ + F₀ ∘ neg` with `F₀` the restriction to `(0, ∞)`). -/
private lemma sgd_nh_integrable :
    Integrable (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
  have hF0 : Integrable (Set.indicator (Ioi (0 : ℝ))
      (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr sgd_nh_half_line
  have hsplit : (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * x ^ 2))
      = fun x : ℝ => Set.indicator (Ioi (0 : ℝ))
          (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) x
        + Set.indicator (Ioi (0 : ℝ))
          (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) (-x) := by
    funext x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · have hnx : (0 : ℝ) < -x := by linarith
      have h1 : x ∉ Ioi (0 : ℝ) := by simp only [mem_Ioi, not_lt]; exact hx.le
      simp only [Set.indicator_of_notMem h1, Set.indicator_of_mem (mem_Ioi.mpr hnx), zero_add,
        abs_neg, neg_sq]
    · subst hx
      have h0 : (0 : ℝ) ∉ Ioi (0 : ℝ) := fun h => lt_irrefl (0 : ℝ) h
      have h0' : (0 : ℝ) ^ (-(1 / 2 : ℝ)) = 0 := Real.zero_rpow (by norm_num)
      simp only [neg_zero, Set.indicator_of_notMem h0, abs_zero, h0', zero_mul, add_zero]
    · have h2 : -x ∉ Ioi (0 : ℝ) := by simp only [mem_Ioi, not_lt]; linarith
      simp only [Set.indicator_of_notMem h2, Set.indicator_of_mem (mem_Ioi.mpr hx), add_zero]
  rw [hsplit]
  exact hF0.add hF0.comp_neg

/-- Auxiliary: `f ↦ φ·f` integrability transfers between `gaussianReal 0 1` and the Lebesgue
measure weighted by the density. -/
private lemma sgd_pdf_integrable_smul_iff (f : ℝ → ℝ) :
    Integrable (fun x => gaussianPDFReal 0 1 x • f x) ↔ Integrable f (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  simp only [toReal_gaussianPDF]

/-- Helper: `E|g|^{-1/2}` is finite (l. 340); its value is `gaussian_neg_half_abs_moment`. -/
theorem sgd_neg_half_abs_integrable :
    Integrable (fun g : ℝ => |g| ^ (-(1 / 2 : ℝ))) (gaussianReal 0 1) := by
  rw [← sgd_pdf_integrable_smul_iff]
  have hpt : (fun x : ℝ => gaussianPDFReal 0 1 x • |x| ^ (-(1 / 2 : ℝ)))
      = fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹
          * (|x| ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    funext x
    rw [gaussianPDFReal_def, smul_eq_mul]
    dsimp only
    have hexp : -(x - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ)) = -(1 / 2 : ℝ) * x ^ 2 := by
      simp only [NNReal.coe_one, mul_one, sub_zero]; ring
    rw [hexp]
    simp only [NNReal.coe_one, mul_one]
    ring
  rw [hpt]
  exact sgd_nh_integrable.const_mul _

/-- Auxiliary: `(1 + y²)^{-1/2} ≤ y^{-1/2}` for `y > 0`. -/
private lemma sgd_pt_rpow_le {y : ℝ} (hy : 0 < y) :
    (1 + y ^ 2) ^ (-(1 / 2 : ℝ)) ≤ y ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_le_rpow_of_nonpos hy (by nlinarith [sq_nonneg (y - 1 / 2)]) (by norm_num)

/-- Helper: `ψ(x) ≤ x^{-1/2} (E|g|^{-1/2})²` for `x > 0`, from `(1 + y²)^{-1/2} ≤ y^{-1/2}` applied
pointwise with `y = x|ξζ|` (proof of `lem:app-sgd-decay`). -/
theorem sgd_psi_le_rpow {x : ℝ} (hx : 0 < x) :
    sgdPsi x ≤ x ^ (-(1 / 2 : ℝ)) * (∫ g, |g| ^ (-(1 / 2 : ℝ)) ∂(gaussianReal 0 1)) ^ 2 := by
  have hint1 := sgd_neg_half_abs_integrable
  have hprod : Integrable (fun p : ℝ × ℝ => |p.1| ^ (-(1 / 2 : ℝ)) * |p.2| ^ (-(1 / 2 : ℝ)))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := hint1.mul_prod hint1
  have hae : ∀ᵐ p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)), p.1 * p.2 ≠ 0 := by
    exact ae_iff.mpr (measure_mono_null (fun p hp => not_not.mp hp) sgd_psi_zero_null)
  have hx0 : (0 : ℝ) ≤ x := hx.le
  have hle : sgdPsi x ≤ ∫ p : ℝ × ℝ,
      x ^ (-(1 / 2 : ℝ)) * (|p.1| ^ (-(1 / 2 : ℝ)) * |p.2| ^ (-(1 / 2 : ℝ)))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    unfold sgdPsi
    refine integral_mono_ae (sgd_psi_int_bdd hx0) (hprod.const_mul _) ?_
    filter_upwards [hae] with p hp
    have hp1 : p.1 ≠ 0 := left_ne_zero_of_mul hp
    have hp2 : p.2 ≠ 0 := right_ne_zero_of_mul hp
    have hpos : 0 < x * |p.1| * |p.2| := by
      have ha : 0 < |p.1| := abs_pos.mpr hp1
      have hb : 0 < |p.2| := abs_pos.mpr hp2
      positivity
    have hsq : x ^ 2 * p.1 ^ 2 * p.2 ^ 2 = (x * |p.1| * |p.2|) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs, sq_abs]
    rw [hsq]
    have h1 := sgd_pt_rpow_le hpos
    have hsplit : x ^ (-(1 / 2 : ℝ)) * (|p.1| ^ (-(1 / 2 : ℝ)) * |p.2| ^ (-(1 / 2 : ℝ)))
        = (x * |p.1| * |p.2|) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.mul_rpow (mul_nonneg hx0 (abs_nonneg _)) (abs_nonneg _),
        Real.mul_rpow hx0 (abs_nonneg _)]
      ring
    rw [hsplit]
    exact h1
  have hprodint : ∫ p : ℝ × ℝ, |p.1| ^ (-(1 / 2 : ℝ)) * |p.2| ^ (-(1 / 2 : ℝ))
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))
      = (∫ g, |g| ^ (-(1 / 2 : ℝ)) ∂(gaussianReal 0 1))
        * (∫ g, |g| ^ (-(1 / 2 : ℝ)) ∂(gaussianReal 0 1)) :=
    integral_prod_mul (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
      (fun g : ℝ => |g| ^ (-(1 / 2 : ℝ))) (fun g : ℝ => |g| ^ (-(1 / 2 : ℝ)))
  calc sgdPsi x
      ≤ _ := hle
    _ = x ^ (-(1 / 2 : ℝ)) * (∫ g, |g| ^ (-(1 / 2 : ℝ)) ∂(gaussianReal 0 1)) ^ 2 := by
      rw [integral_const_mul, hprodint, sq]

private lemma pg_peel {n : ℕ} (c v : Fin n → ℝ) (α lam : ℝ) (hlam : 0 ≤ lam)
    (hα : ∑ k, v k * c k = α * ∑ k, c k ^ 2) :
    ∫ x, Real.exp (-lam * (∑ k, (x * c k + v k) ^ 2) / 2) ∂(gaussianReal 0 1)
      ≤ (1 + lam * ∑ k, c k ^ 2) ^ (-(1 / 2 : ℝ))
        * Real.exp (-lam * (∑ k, (v k - α * c k) ^ 2) / 2) := by
  set S := ∑ k, c k ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
  by_cases hS' : S = 0
  · have hc : ∀ k, c k = 0 := by
      intro k
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (c k))).1 hS' k
        (Finset.mem_univ k)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    simp only [hc, mul_zero, zero_add, sub_zero, hS', add_zero, mul_zero]
    simp
  · have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS')
    set σ := Real.sqrt S with hσ
    have hσ2 : σ ^ 2 = S := Real.sq_sqrt hS0
    have hexp : ∀ x : ℝ, -lam * (∑ k, (x * c k + v k) ^ 2) / 2
        = -lam * (σ * x + σ * α) ^ 2 / 2 + (-lam * (∑ k, (v k - α * c k) ^ 2) / 2) := by
      intro x
      have : ∑ k, (x * c k + v k) ^ 2 = (σ * x + σ * α) ^ 2 + ∑ k, (v k - α * c k) ^ 2 := by
        have e1 : (σ * x + σ * α) ^ 2 = S * (x + α) ^ 2 := by
          rw [← mul_add, mul_pow, hσ2]
        rw [e1]
        have e2 : ∑ k, (x * c k + v k) ^ 2 = x ^ 2 * S + 2 * x * (∑ k, v k * c k)
            + ∑ k, v k ^ 2 := by
          simp only [hS, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => by ring
        have e3 : ∑ k, (v k - α * c k) ^ 2 = ∑ k, v k ^ 2 - 2 * α * (∑ k, v k * c k)
            + α ^ 2 * S := by
          simp only [hS, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => by ring
        rw [e2, e3, hα]; ring
      rw [this]; ring
    simp_rw [hexp, Real.exp_add]
    rw [integral_mul_const, Muon.Foundations.gaussian_completed_square lam σ (σ * α) hlam, hσ2]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have hA : 0 < 1 + lam * S := by positivity
    have : Real.exp (-lam * (σ * α) ^ 2 / (2 * (1 + lam * S))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ lam * (σ * α) ^ 2 / (2 * (1 + lam * S)) := by positivity
      have e : -lam * (σ * α) ^ 2 / (2 * (1 + lam * S)) = -(lam * (σ * α) ^ 2 / (2 * (1 + lam * S))) := by ring
      linarith
    calc _ ≤ (1 + lam * S) ^ (-(1 / 2 : ℝ)) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _

private lemma pg_slice (n : ℕ) (i : Fin n) (f : (Fin n → ℝ) → ℝ)
    (hf : Integrable f (Muon.Foundations.stdGaussianPi n)) :
    ∫ z, f z ∂(Muon.Foundations.stdGaussianPi n)
      = ∫ z, ∫ x, f (Function.update z i x) ∂(gaussianReal 0 1)
          ∂(Muon.Foundations.stdGaussianPi n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal (0 : ℝ) 1) i
  have hg : ∀ F : (Fin (m + 1) → ℝ) → ℝ, ∫ z, F z ∂(Muon.Foundations.stdGaussianPi (m + 1))
      = ∫ p, F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm p)
          ∂((gaussianReal 0 1).prod (Muon.Foundations.stdGaussianPi m)) := by
    intro F
    have := hmp.integral_comp' (g := fun p => F ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (m + 1) => ℝ) i).symm p))
    simp only [MeasurableEquiv.symm_apply_apply] at this
    exact this
  have hint' : Integrable (fun p => f ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (m + 1) => ℝ) i).symm p))
      ((gaussianReal 0 1).prod (Muon.Foundations.stdGaussianPi m)) :=
    (MeasurePreserving.symm _ hmp).integrable_comp_of_integrable hf
  have hL : ∫ z, f z ∂(Muon.Foundations.stdGaussianPi (m + 1))
      = ∫ y, ∫ x, f (i.insertNth x y) ∂(gaussianReal 0 1) ∂(Muon.Foundations.stdGaussianPi m) := by
    rw [hg, integral_prod_symm _ hint']
    rfl
  rw [hL, hg (fun z => ∫ x, f (Function.update z i x) ∂(gaussianReal 0 1))]
  have e : ∀ p : ℝ × (Fin m → ℝ),
      ∫ x, f (Function.update ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm p)
        i x) ∂(gaussianReal 0 1) = ∫ x, f (i.insertNth x p.2) ∂(gaussianReal 0 1) := by
    intro p
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.update_insertNth]
  simp only [e]
  refine Eq.trans ?_ (integral_fun_snd (μ := gaussianReal 0 1)
    (ν := Muon.Foundations.stdGaussianPi m)
    (fun y => ∫ x, f (i.insertNth x y) ∂(gaussianReal 0 1))).symm
  simp

private lemma pg_orth {n m : ℕ} (N : Matrix (Fin n) (Fin m) ℝ)
    (hN : ∀ i j, i ≠ j → ∑ k, N k i * N k j = 0) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∀ (s : Finset (Fin m)) (h : Fin n → ℝ),
    ∫ w, Real.exp (-lam * (∑ k, (∑ j ∈ s, w j * N k j + h k) ^ 2) / 2)
        ∂(Muon.Foundations.stdGaussianPi m)
      ≤ ∏ j ∈ s, (1 + lam * ∑ k, N k j ^ 2) ^ (-(1 / 2 : ℝ)) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro h
    simp only [Finset.sum_empty, zero_add, Finset.prod_empty]
    have : ∀ w : Fin m → ℝ, Real.exp (-lam * (∑ k, h k ^ 2) / 2) ≤ 1 := by
      intro w
      rw [Real.exp_le_one_iff]
      have : 0 ≤ lam * ∑ k, h k ^ 2 := mul_nonneg hlam (Finset.sum_nonneg fun k _ => sq_nonneg _)
      linarith
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact this 0
  | insert a s ha ih =>
    intro h
    set S := ∑ k, N k a ^ 2 with hS
    set α := (∑ k, h k * N k a) / S with hαdef
    have hαS : ∑ k, h k * N k a = α * S := by
      by_cases hS0 : S = 0
      · have hc : ∀ k, N k a = 0 := by
          intro k
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (N k a))).1 hS0 k
            (Finset.mem_univ k)
          exact pow_eq_zero_iff (two_ne_zero) |>.1 this
        simp [hc, hS0]
      · rw [hαdef]; field_simp
    have hint : Integrable (fun w : Fin m → ℝ =>
        Real.exp (-lam * (∑ k, (∑ j ∈ insert a s, w j * N k j + h k) ^ 2) / 2))
        (Muon.Foundations.stdGaussianPi m) := by
      refine Integrable.mono' (integrable_const (1 : ℝ))
        (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun w => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have : 0 ≤ lam * ∑ k, (∑ j ∈ insert a s, w j * N k j + h k) ^ 2 :=
        mul_nonneg hlam (Finset.sum_nonneg fun k _ => sq_nonneg _)
      linarith
    rw [pg_slice m a _ hint, Finset.prod_insert ha]
    have step : ∀ z : Fin m → ℝ,
        ∫ x, Real.exp (-lam * (∑ k, (∑ j ∈ insert a s, (Function.update z a x) j * N k j + h k) ^ 2) / 2)
          ∂(gaussianReal 0 1)
        ≤ (1 + lam * S) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-lam * (∑ k, (∑ j ∈ s, z j * N k j + (h k - α * N k a)) ^ 2) / 2) := by
      intro z
      have heq : ∀ x : ℝ, ∀ k, ∑ j ∈ insert a s, (Function.update z a x) j * N k j
          = x * N k a + ∑ j ∈ s, z j * N k j := by
        intro x k
        rw [Finset.sum_insert ha, Function.update_self]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hj ha)]
      have hv : ∑ k, (∑ j ∈ s, z j * N k j + h k) * N k a = α * ∑ k, N k a ^ 2 := by
        have : ∑ k, (∑ j ∈ s, z j * N k j + h k) * N k a
            = ∑ j ∈ s, z j * (∑ k, N k j * N k a) + ∑ k, h k * N k a := by
          simp only [add_mul, Finset.sum_mul, Finset.sum_add_distrib, Finset.mul_sum]
          rw [Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
        rw [this, hαS]
        have h0 : ∑ j ∈ s, z j * (∑ k, N k j * N k a) = 0 :=
          Finset.sum_eq_zero fun j hj => by
            rw [hN j a (ne_of_mem_of_not_mem hj ha), mul_zero]
        rw [h0, zero_add]
      have key := pg_peel (fun k => N k a) (fun k => ∑ j ∈ s, z j * N k j + h k) α lam hlam hv
      refine le_trans (le_of_eq ?_) (le_trans key (le_of_eq ?_))
      · refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [heq, add_assoc]
      · simp only [add_sub_assoc]; rfl
    have hG : Integrable (fun z : Fin m → ℝ => (1 + lam * S) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-lam * (∑ k, (∑ j ∈ s, z j * N k j + (h k - α * N k a)) ^ 2) / 2))
        (Muon.Foundations.stdGaussianPi m) := by
      refine Integrable.const_mul ?_ _
      refine Integrable.mono' (integrable_const (1 : ℝ))
        (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun w => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have : 0 ≤ lam * ∑ k, (∑ j ∈ s, w j * N k j + (h k - α * N k a)) ^ 2 :=
        mul_nonneg hlam (Finset.sum_nonneg fun k _ => sq_nonneg _)
      linarith
    calc _ ≤ ∫ z : Fin m → ℝ, (1 + lam * S) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-lam * (∑ k, (∑ j ∈ s, z j * N k j + (h k - α * N k a)) ^ 2) / 2)
          ∂(Muon.Foundations.stdGaussianPi m) :=
          integral_mono_of_nonneg (ae_of_all _ fun z => integral_nonneg fun x => (Real.exp_pos _).le)
            hG (ae_of_all _ step)
      _ = (1 + lam * S) ^ (-(1 / 2 : ℝ)) * ∫ z : Fin m → ℝ,
          Real.exp (-lam * (∑ k, (∑ j ∈ s, z j * N k j + (h k - α * N k a)) ^ 2) / 2)
          ∂(Muon.Foundations.stdGaussianPi m) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (ih _) (by positivity)

section
open Matrix
private theorem pg_map_toLp (n : ℕ) :
    (Muon.Foundations.stdGaussianPi n).map (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      = stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  unfold Muon.Foundations.stdGaussianPi
  exact map_pi_eq_stdGaussian

/-- Private helper: the rotation `x ↦ O x` of `EuclideanSpace ℝ (Fin n)` as a linear isometry
equivalence, for `O ∈ O(n)`. -/
private noncomputable def pg_rotE (n : ℕ) (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearEquiv.isometryOfInner
    { toFun := fun x => WithLp.toLp 2 ((O : Matrix (Fin n) (Fin n) ℝ) *ᵥ WithLp.ofLp x)
      invFun := fun x => WithLp.toLp 2 ((O : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ WithLp.ofLp x)
      map_add' := by
        intro x y
        ext i
        simp [Matrix.mulVec_add]
      map_smul' := by
        intro c x
        ext i
        simp [Matrix.mulVec_smul]
      left_inv := by
        intro x
        have h : (O : Matrix (Fin n) (Fin n) ℝ)ᵀ * (O : Matrix (Fin n) (Fin n) ℝ) = 1 :=
          (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 O.2
        ext i
        change ((O : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ
          ((O : Matrix (Fin n) (Fin n) ℝ) *ᵥ WithLp.ofLp x)) i
          = WithLp.ofLp x i
        rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
      right_inv := by
        intro x
        have h : (O : Matrix (Fin n) (Fin n) ℝ) * (O : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 :=
          (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).1 O.2
        ext i
        change ((O : Matrix (Fin n) (Fin n) ℝ) *ᵥ
          ((O : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ WithLp.ofLp x)) i
          = WithLp.ofLp x i
        rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec] }
    (by
      intro x y
      have h : (O : Matrix (Fin n) (Fin n) ℝ)ᵀ * (O : Matrix (Fin n) (Fin n) ℝ) = 1 :=
        (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 O.2
      simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.star_mulVec,
        Matrix.conjTranspose_eq_transpose_of_trivial]
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h, Matrix.vecMul_one,
        dotProduct_comm])

/-- Rotation invariance: for `O ∈ O(n)`, `O g` has the same law as `g`. -/
private theorem pg_map_orthogonal (n : ℕ) (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    (Muon.Foundations.stdGaussianPi n).map (fun z : Fin n → ℝ => (O : Matrix (Fin n) (Fin n) ℝ) *ᵥ z)
      = Muon.Foundations.stdGaussianPi n := by
  have hrot : Measurable (pg_rotE n O) := (pg_rotE n O).continuous.measurable
  have hf : Measurable (fun z : Fin n → ℝ => (O : Matrix (Fin n) (Fin n) ℝ) *ᵥ z) := by
    fun_prop
  have he : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
  have hG := stdGaussian_map (pg_rotE n O)
  have hcomp : (WithLp.toLp 2 ∘ fun z : Fin n → ℝ => (O : Matrix (Fin n) (Fin n) ℝ) *ᵥ z)
      = (pg_rotE n O) ∘ (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by
    funext z
    ext i
    simp [pg_rotE]
  have key : ((Muon.Foundations.stdGaussianPi n).map
      (fun z : Fin n → ℝ => (O : Matrix (Fin n) (Fin n) ℝ) *ᵥ z)).map (WithLp.toLp 2)
      = (Muon.Foundations.stdGaussianPi n).map (WithLp.toLp 2) := by
    rw [Measure.map_map he hf, hcomp, ← Measure.map_map hrot he, pg_map_toLp, hG]
  exact hemb.map_injective key
end

private lemma pg_diag {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) :
    ∃ U : Matrix.orthogonalGroup (Fin m) ℝ, ∃ d : Fin m → ℝ,
      (U : Matrix (Fin m) (Fin m) ℝ).transpose * A * (U : Matrix (Fin m) (Fin m) ℝ)
        = Matrix.diagonal d := by
  refine ⟨hA.eigenvectorUnitary, RCLike.ofReal ∘ hA.eigenvalues, ?_⟩
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  have h1 : (star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)) *
      (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) = 1 :=
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have h2 : (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) *
      (star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)) = 1 :=
    Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h1 h2 h
  generalize (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) = U at h h1 h2 ⊢
  generalize (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix (Fin m) (Fin m) ℝ) = D at h ⊢
  rw [h]
  calc U.transpose * (U * D * U.transpose) * U
        = (U.transpose * U) * D * (U.transpose * U) := by simp only [Matrix.mul_assoc]
    _ = D := by rw [h1]; simp

private lemma pg_prod_ge {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hs : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j _ => ha j
    nlinarith [ha i]

/-- Helper: Gaussian MGF with a linear shift, `E_w exp(-λ‖Mw + h‖²/2) ≤ (1 + λ‖M‖_F²)^{-1/2}`
for `λ ≥ 0` and every `M`, `h` (proof of `lem:app-sgd-decay`: completed square, SVD of `M`, product bound). -/
theorem sgd_gauss_mgf_frob {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (h : Fin n → ℝ)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ∫ w, Real.exp (-lam * (∑ k, (Matrix.mulVec M w k + h k) ^ 2) / 2)
        ∂(Muon.Foundations.stdGaussianPi m)
      ≤ (1 + lam * frobNorm M ^ 2) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨U, d, hUd⟩ := pg_diag (M.transpose * M) (by have := Matrix.isHermitian_conjTranspose_mul_self M; rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this)
  set Um : Matrix (Fin m) (Fin m) ℝ := (U : Matrix (Fin m) (Fin m) ℝ) with hUm
  set N : Matrix (Fin n) (Fin m) ℝ := M * Um with hN
  have hNN : N.transpose * N = Matrix.diagonal d := by
    rw [← hUd, hN, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have hentry : ∀ i j, ∑ k, N k i * N k j = (Matrix.diagonal d) i j := by
    intro i j
    rw [← hNN, Matrix.mul_apply]
    simp
  have horth : ∀ i j, i ≠ j → ∑ k, N k i * N k j = 0 := by
    intro i j hij
    rw [hentry, Matrix.diagonal_apply_ne _ hij]
  have hdj : ∀ j, ∑ k, N k j ^ 2 = d j := by
    intro j
    have := hentry j j
    rw [Matrix.diagonal_apply_eq] at this
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => sq _
  -- rotate
  have hmeas : Measurable (fun w : Fin m → ℝ => Matrix.mulVec Um w) := by fun_prop
  have hrot : ∀ g : (Fin m → ℝ) → ℝ, Continuous g →
      ∫ w, g w ∂(Muon.Foundations.stdGaussianPi m)
        = ∫ w, g (Matrix.mulVec Um w) ∂(Muon.Foundations.stdGaussianPi m) := by
    intro g hg
    have := integral_map (μ := Muon.Foundations.stdGaussianPi m) hmeas.aemeasurable
      (φ := fun w : Fin m → ℝ => Matrix.mulVec Um w) (f := g) hg.aestronglyMeasurable
    rw [pg_map_orthogonal m U] at this
    exact this
  have hfc : Continuous (fun w : Fin m → ℝ =>
      Real.exp (-lam * (∑ k, (Matrix.mulVec M w k + h k) ^ 2) / 2)) := by
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  rw [hrot _ hfc]
  have e1 : ∀ w : Fin m → ℝ, ∀ k, Matrix.mulVec M (Matrix.mulVec Um w) k
      = ∑ j ∈ Finset.univ, w j * N k j := by
    intro w k
    rw [Matrix.mulVec_mulVec, ← hN]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp_rw [e1]
  refine le_trans (pg_orth N horth lam hlam Finset.univ h) ?_
  simp_rw [hdj]
  have hd0 : ∀ j, 0 ≤ d j := fun j => by rw [← hdj j]; exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hsum : ∑ j, d j = frobNorm M ^ 2 := by
    have hU1 : Um * Um.transpose = 1 := (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).1 U.2
    have htr : Matrix.trace (Matrix.diagonal d) = Matrix.trace (M.transpose * M) := by
      rw [← hUd, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hU1, Matrix.mul_one]
    rw [Matrix.trace_diagonal] at htr
    have hf : frobNorm M ^ 2 = ∑ i, ∑ j, M i j ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
    rw [hf, Finset.sum_comm]
    have : Matrix.trace (M.transpose * M) = ∑ j, ∑ i, M i j ^ 2 := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]
    rw [this] at htr
    rw [← htr]
  rw [Real.finsetProd_rpow Finset.univ (fun j => 1 + lam * d j)
    (fun j _ => by have := hd0 j; positivity)]
  have hp := pg_prod_ge Finset.univ (fun j => lam * d j) (fun j => mul_nonneg hlam (hd0 j))
  rw [← Finset.mul_sum, hsum] at hp
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hp (by norm_num)

/-- Helper: modulus of the characteristic function of an affine functional of a standard Gaussian
vector, `|E exp(i t (c + ⟨z, u⟩))| = exp(-t²‖u‖²/2)` (proof of `lem:app-sgd-decay`, integral over `z'`). -/
theorem sgd_gauss_charfun_linear {n : ℕ} (u : Fin n → ℝ) (c t : ℝ) :
    ‖∫ z, Complex.exp ((t : ℂ) * Complex.I * ((c + ∑ k, z k * u k : ℝ) : ℂ))
        ∂(Muon.Foundations.stdGaussianPi n)‖
      = Real.exp (-(t ^ 2 * ∑ k, u k ^ 2) / 2) := by
  have hS0 : 0 ≤ ∑ k, u k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hmeas : Measurable (fun z : Fin n → ℝ => ∑ k, z k * u k) := by fun_prop
  have hg : Measurable (fun x : ℝ => Complex.exp ((t : ℂ) * Complex.I * ((c + x : ℝ) : ℂ))) := by
    fun_prop
  have e1 : ∫ z, Complex.exp ((t : ℂ) * Complex.I * ((c + ∑ k, z k * u k : ℝ) : ℂ))
        ∂(Muon.Foundations.stdGaussianPi n)
      = ∫ x, Complex.exp ((t : ℂ) * Complex.I * ((c + x : ℝ) : ℂ))
        ∂((Muon.Foundations.stdGaussianPi n).map (fun z : Fin n → ℝ => ∑ k, z k * u k)) :=
    (integral_map hmeas.aemeasurable hg.aestronglyMeasurable).symm
  have hsplit : ∀ x : ℝ, Complex.exp ((t : ℂ) * Complex.I * ((c + x : ℝ) : ℂ))
      = Complex.exp (((t * c : ℝ) : ℂ) * Complex.I) * Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) := by
    intro x
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hc1 : ‖Complex.exp (((t * c : ℝ) : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hchar : ∫ x, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
      ∂(gaussianReal 0 (Real.toNNReal (∑ k, u k ^ 2)))
      = charFun (gaussianReal 0 (Real.toNNReal (∑ k, u k ^ 2))) t := by
    rw [charFun_apply_real]
    simp only [Complex.ofReal_mul]
  rw [e1, Muon.Foundations.stdGaussianPi_linear_map]
  simp_rw [hsplit]
  rw [integral_const_mul, norm_mul, hc1, one_mul, hchar, charFun_gaussianReal, Complex.norm_exp]
  congr 1
  have hz : ((t : ℂ) * ((0 : ℝ) : ℂ) * Complex.I
      - (((Real.toNNReal (∑ k, u k ^ 2) : ℝ)) : ℂ) * (t : ℂ) ^ 2 / 2)
      = (((-(t ^ 2 * ∑ k, u k ^ 2) / 2 : ℝ)) : ℂ) := by
    rw [Real.coe_toNNReal _ hS0]
    push_cast
    ring
  rw [hz, Complex.ofReal_re]

/-- Helper: even moments of a linear functional of a standard Gaussian vector,
`E⟨z, u⟩^{2p} = (2p-1)!! ‖u‖^{2p}` (proof of `lem:app-sgd-moments`(vi), conditionally on `w`). -/
theorem sgd_gauss_linear_even_moment {n : ℕ} (p : ℕ) (u : Fin n → ℝ) :
    ∫ z, (∑ k, z k * u k) ^ (2 * p) ∂(Muon.Foundations.stdGaussianPi n)
      = (((2 * p - 1).doubleFactorial : ℕ) : ℝ) * (∑ k, u k ^ 2) ^ p := by
  have hS0 : 0 ≤ ∑ k, u k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.sqrt (∑ k, u k ^ 2) := ⟨_, rfl⟩
  have hc2 : c ^ 2 = ∑ k, u k ^ 2 := by rw [hc]; exact Real.sq_sqrt hS0
  have hg : gaussianReal 0 (Real.toNNReal (∑ k, u k ^ 2))
      = (gaussianReal 0 1).map (fun x : ℝ => c * x) := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    apply NNReal.eq
    simp [Real.coe_toNNReal _ hS0, hc2]
  have hmeas : Measurable (fun z : Fin n → ℝ => ∑ k, z k * u k) := by fun_prop
  have h1 : ∫ z, (∑ k, z k * u k) ^ (2 * p) ∂(Muon.Foundations.stdGaussianPi n)
      = ∫ x, x ^ (2 * p) ∂(gaussianReal 0 (Real.toNNReal (∑ k, u k ^ 2))) := by
    rw [← Muon.Foundations.stdGaussianPi_linear_map n u]
    exact (integral_map hmeas.aemeasurable
      (by fun_prop : Measurable fun x : ℝ => x ^ (2 * p)).aestronglyMeasurable).symm
  rw [h1, hg, integral_map (by fun_prop : Measurable fun x : ℝ => c * x).aemeasurable
    (by fun_prop : Measurable fun x : ℝ => x ^ (2 * p)).aestronglyMeasurable]
  simp_rw [mul_pow]
  rw [integral_const_mul, Muon.Foundations.gaussian_moment_even p, pow_mul, hc2]
  ring

/-- Private helper: quadratic form in a basis diagonalising the Gram matrix. -/
private lemma pg_quad_diag {n m : ℕ} (N : Matrix (Fin n) (Fin m) ℝ) (d : Fin m → ℝ)
    (hN : ∀ a b, a ≠ b → ∑ k, N k a * N k b = 0) (hd : ∀ a, ∑ k, N k a * N k a = d a)
    (v : Fin m → ℝ) : ∑ k, (Matrix.mulVec N v) k ^ 2 = ∑ a, d a * v a ^ 2 := by
  have e1 : ∀ k, (Matrix.mulVec N v) k ^ 2 = ∑ a, ∑ b, N k a * N k b * (v a * v b) := by
    intro k
    simp only [Matrix.mulVec, dotProduct, sq]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl (fun k _ => e1 k), Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  have e2 : ∀ b, ∑ k, N k a * N k b * (v a * v b) = (∑ k, N k a * N k b) * (v a * v b) :=
    fun b => by rw [Finset.sum_mul]
  simp only [e2]
  rw [Finset.sum_eq_single a]
  · rw [hd a]; ring
  · intro b _ hb; rw [hN a b (Ne.symm hb), zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- Helper: `E‖Mw‖^{2p} ≤ (2p-1)!! ‖M‖_F^{2p}` for integers `p ≥ 1` (SVD of `M`, Jensen on
`∑ π_l g_l²`; proof of `lem:app-sgd-moments`(vi)). -/
theorem sgd_quadform_moment_le {n m : ℕ} (p : ℕ) (hp : 1 ≤ p) (M : Matrix (Fin n) (Fin m) ℝ) :
    ∫ w, (∑ k, Matrix.mulVec M w k ^ 2) ^ p ∂(Muon.Foundations.stdGaussianPi m)
      ≤ (((2 * p - 1).doubleFactorial : ℕ) : ℝ) * frobNorm M ^ (2 * p) := by
  have hA : (Matrix.transpose M * M).IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_self M
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  obtain ⟨U, d, hUd⟩ := pg_diag (Matrix.transpose M * M) hA
  have hUU : (U : Matrix (Fin m) (Fin m) ℝ) * Matrix.transpose (U : Matrix (Fin m) (Fin m) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).1 U.2
  have hGramEq : Matrix.transpose (M * (U : Matrix (Fin m) (Fin m) ℝ)) * (M * (U : Matrix (Fin m) (Fin m) ℝ))
      = Matrix.transpose (U : Matrix (Fin m) (Fin m) ℝ) * (Matrix.transpose M * M) * (U : Matrix (Fin m) (Fin m) ℝ) := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have hGram : ∀ a b : Fin m, ∑ k, (M * (U : Matrix (Fin m) (Fin m) ℝ)) k a
      * (M * (U : Matrix (Fin m) (Fin m) ℝ)) k b = Matrix.diagonal d a b := by
    intro a b
    rw [← hUd, ← hGramEq]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hd_eq : ∀ a, ∑ k, (M * (U : Matrix (Fin m) (Fin m) ℝ)) k a
      * (M * (U : Matrix (Fin m) (Fin m) ℝ)) k a = d a := fun a => by
    rw [hGram a a, Matrix.diagonal_apply_eq]
  have hd_nonneg : ∀ a, 0 ≤ d a := fun a => by
    rw [← hd_eq a]
    exact Finset.sum_nonneg fun k _ => mul_self_nonneg _
  have hQ : ∀ v : Fin m → ℝ, ∑ k, (Matrix.mulVec M (Matrix.mulVec (U : Matrix (Fin m) (Fin m) ℝ) v)) k ^ 2
      = ∑ a, d a * v a ^ 2 := by
    intro v
    rw [Matrix.mulVec_mulVec]
    exact pg_quad_diag (M * (U : Matrix (Fin m) (Fin m) ℝ)) d
      (fun a b hab => by rw [hGram a b, Matrix.diagonal_apply_ne _ hab]) hd_eq v
  have hS : ∑ a, d a = frobNorm M ^ 2 := by
    have htr : Matrix.trace (Matrix.diagonal d) = ∑ a, d a := Matrix.trace_diagonal d
    rw [← htr, ← hUd]
    have hcyc : Matrix.trace (Matrix.transpose (U : Matrix (Fin m) (Fin m) ℝ) * (Matrix.transpose M * M) * (U : Matrix (Fin m) (Fin m) ℝ))
        = Matrix.trace (Matrix.transpose M * M) := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    rw [hcyc]
    have hF : 0 ≤ ∑ i, ∑ j, M i j ^ 2 := by positivity
    unfold frobNorm
    rw [Real.sq_sqrt hF]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]
    exact Finset.sum_comm
  have hpush : ∫ w, (∑ k, Matrix.mulVec M w k ^ 2) ^ p ∂(Muon.Foundations.stdGaussianPi m)
      = ∫ v, (∑ a, d a * v a ^ 2) ^ p ∂(Muon.Foundations.stdGaussianPi m) := by
    have h := integral_map (μ := Muon.Foundations.stdGaussianPi m)
      (φ := fun v : Fin m → ℝ => Matrix.mulVec (U : Matrix (Fin m) (Fin m) ℝ) v)
      (f := fun w : Fin m → ℝ => (∑ k, Matrix.mulVec M w k ^ 2) ^ p)
      (by fun_prop : Measurable fun v : Fin m → ℝ => Matrix.mulVec (U : Matrix (Fin m) (Fin m) ℝ) v).aemeasurable
      (by fun_prop : Measurable fun w : Fin m → ℝ => (∑ k, Matrix.mulVec M w k ^ 2) ^ p).aestronglyMeasurable
    rw [pg_map_orthogonal m U] at h
    rw [h]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [hQ]
  have hint : ∀ a : Fin m, Integrable (fun v : Fin m → ℝ => v a ^ (2 * p))
      (Muon.Foundations.stdGaussianPi m) := by
    intro a
    have hm : Measurable (fun z : Fin m → ℝ => z a) := by fun_prop
    exact (integrable_map_measure (g := fun x : ℝ => x ^ (2 * p))
      (f := fun z : Fin m → ℝ => z a)
      (by fun_prop : Measurable fun x : ℝ => x ^ (2 * p)).aestronglyMeasurable
      hm.aemeasurable).1 (by
        rw [Muon.Foundations.stdGaussianPi_map_coord]
        exact Muon.Foundations.gaussian_integrable_pow _)
  have hcoord : ∀ a : Fin m, ∫ v, v a ^ (2 * p) ∂(Muon.Foundations.stdGaussianPi m)
      = (((2 * p - 1).doubleFactorial : ℕ) : ℝ) := by
    intro a
    rw [← Muon.Foundations.gaussian_moment_even p, ← Muon.Foundations.stdGaussianPi_map_coord m a]
    exact (integral_map (by fun_prop : Measurable fun z : Fin m → ℝ => z a).aemeasurable
      (by fun_prop : Measurable fun x : ℝ => x ^ (2 * p)).aestronglyMeasurable).symm
  rw [hpush, pow_mul, ← hS]
  by_cases hS0 : ∑ a, d a = 0
  · have hd0 : ∀ a, d a = 0 := fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hd_nonneg a)).1 hS0 a (Finset.mem_univ a)
    rw [hS0]
    simp [hd0, show p ≠ 0 by omega]
  · obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ a, d a := ⟨_, rfl⟩
    rw [← hSdef]
    have hSpos : 0 < S := by
      rw [hSdef]
      exact lt_of_le_of_ne (Finset.sum_nonneg fun a _ => hd_nonneg a) (Ne.symm hS0)
    have hpt : ∀ v : Fin m → ℝ, (∑ a, d a * v a ^ 2) ^ p
        ≤ S ^ p * ∑ a, (d a / S) * v a ^ (2 * p) := by
      intro v
      have hw : ∑ a, d a / S = 1 := by
        rw [← Finset.sum_div, ← hSdef, div_self hSpos.ne']
      have hmean := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun a => d a / S)
        (fun a => v a ^ 2) (fun a _ => div_nonneg (hd_nonneg a) hSpos.le) hw
        (fun a _ => sq_nonneg _) p
      have hlin : ∑ a, d a * v a ^ 2 = S * ∑ a, d a / S * v a ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        field_simp
      have h2 : ∀ a, (v a ^ 2) ^ p = v a ^ (2 * p) := fun a => (pow_mul (v a) 2 p).symm
      simp only [h2] at hmean
      rw [hlin, mul_pow]
      exact mul_le_mul_of_nonneg_left hmean (pow_nonneg hSpos.le p)
    have hint_sum : Integrable (fun v : Fin m → ℝ => S ^ p * ∑ a, (d a / S) * v a ^ (2 * p))
        (Muon.Foundations.stdGaussianPi m) :=
      (integrable_finset_sum _ fun a _ => (hint a).const_mul (d a / S)).const_mul _
    have hnonneg : ∀ v : Fin m → ℝ, 0 ≤ (∑ a, d a * v a ^ 2) ^ p := fun v =>
      pow_nonneg (Finset.sum_nonneg fun a _ => mul_nonneg (hd_nonneg a) (sq_nonneg _)) p
    calc ∫ v, (∑ a, d a * v a ^ 2) ^ p ∂(Muon.Foundations.stdGaussianPi m)
        ≤ ∫ v, S ^ p * ∑ a, (d a / S) * v a ^ (2 * p) ∂(Muon.Foundations.stdGaussianPi m) :=
          integral_mono_of_nonneg (ae_of_all _ hnonneg) hint_sum (ae_of_all _ hpt)
      _ = S ^ p * ∑ a, (d a / S) * ∫ v, v a ^ (2 * p) ∂(Muon.Foundations.stdGaussianPi m) := by
          rw [integral_const_mul, integral_finset_sum _ fun a _ => (hint a).const_mul _]
          congr 1
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [integral_const_mul]
      _ = S ^ p * ∑ a, (d a / S) * (((2 * p - 1).doubleFactorial : ℕ) : ℝ) := by
          simp only [hcoord]
      _ = (((2 * p - 1).doubleFactorial : ℕ) : ℝ) * S ^ p := by
          rw [← Finset.sum_mul, ← Finset.sum_div, ← hSdef, div_self hSpos.ne']
          ring

/-! ## Private helpers for parts (i)-(iii) -/

private lemma cm_mono_integrable {n k : ℕ} (c : Fin k → Fin n) :
    Integrable (fun z : Fin n → ℝ => ∏ r : Fin k, z (c r))
      (Muon.Foundations.stdGaussianPi n) := by
  have hprod : (fun z : Fin n → ℝ => ∏ r : Fin k, z (c r))
      = fun z : Fin n → ℝ => ∏ i : Fin n,
          (fun (x : ℝ) => x ^ Fintype.card {r // c r = i}) (z i) := by
    funext z
    rw [← Fintype.prod_fiberwise c (fun r => z (c r))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_congr rfl (fun (r : {r // c r = i}) _ => by rw [r.2]), Finset.prod_const,
      Finset.card_univ]
  rw [hprod]
  unfold Muon.Foundations.stdGaussianPi
  exact Integrable.fintype_prod (fun i => Muon.Foundations.gaussian_integrable_pow _)

private lemma cm_pair_int {n : ℕ} (p q : Fin n) :
    Integrable (fun z : Fin n → ℝ => z p * z q) (Muon.Foundations.stdGaussianPi n) := by
  have h := cm_mono_integrable (n := n) ![p, q]
  simpa [Fin.prod_univ_two] using h

private lemma cm_pair_moment {n : ℕ} (p q : Fin n) :
    ∫ z, z p * z q ∂(Muon.Foundations.stdGaussianPi n) = (Pi.single p (1 : ℝ) : Fin n → ℝ) q := by
  have h := Muon.Foundations.gaussian_weighted_linear_moment n (Pi.single p 1) q
  simp only [single_dotProduct, one_mul] at h
  exact h

private lemma cm_quad_int {n : ℕ} (a b c d : Fin n) :
    Integrable (fun z : Fin n → ℝ => z a * z b * z c * z d) (Muon.Foundations.stdGaussianPi n) := by
  have h := cm_mono_integrable (n := n) ![a, b, c, d]
  simpa [Fin.prod_univ_four] using h

private lemma cm_lin_sq_int {n : ℕ} (u : Fin n → ℝ) (j : Fin n) :
    Integrable (fun w : Fin n → ℝ => dotProduct u w ^ 2 * w j ^ 2)
      (Muon.Foundations.stdGaussianPi n) := by
  have e : (fun w : Fin n → ℝ => dotProduct u w ^ 2 * w j ^ 2)
      = fun w => ∑ a, ∑ b, (u a * u b) * (w a * w b * w j * w j) := by
    funext w
    simp only [dotProduct, sq, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [e]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (cm_quad_int a b j j).const_mul _

private lemma cm_sum_sq {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ x, f x) ^ 2 = ∑ x, ∑ y, f x * f y := by
  rw [sq, Fintype.sum_mul_sum]

private lemma cm_frob_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobNorm A ^ 2 = ∑ a, ∑ b, A a b ^ 2 := by
  unfold frobNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)

/-! ## Lemma `lem:app-sgd-moments` -/

/-- **lem:app-sgd-moments**, part (i), `Muon.SignSGD.lem_app_sgd_moments_i` (mean).

cr-2026-10-23. The lemma has seven conjuncts (i)-(vii); the LaTeX statement of the whole lemma, verbatim:

\begin{lemma}[Moments of one coordinate]\label{lem:app-sgd-moments}
The coordinate \cref{eqn:app-sgd-coordinate} has mean $\EE X=\Delta_{ij}$, variance
\[
s^2\defeq\Var X=F^2+2\norm{\Delta_{i\cdot}}^2+2\norm{\Delta_{\cdot j}}^2+3\Delta_{ij}^2,\qquad F^2\le s^2\le8F^2,
\]
and third centered moment
\[
m_3\defeq\EE(X-\Delta_{ij})^3=24\Delta_{ij}\norm{\bar\Delta}_\F^2+126\Delta_{ij}\big(\norm r^2+\norm q^2\big)+200\Delta_{ij}^3+54\,q^\T\bar\Delta r,
\]
so that $\abs{m_3}\le200\abs{\Delta_{ij}}F^2+54F\norm r\norm q$. For every
integer $p\ge1$, $\EE\abs X^p\le((2p-1)!!)^2F^p$, and the standardized
coordinate $Y\defeq(X-\Delta_{ij})/s$ satisfies $\EE Y^4\le88208$.
\end{lemma} -/
theorem lem_app_sgd_moments_i {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0)
    (i : Fin Nout) (j : Fin Nin) :
    ∫ p, sgdCoord Δ i j p ∂(gaussBatch Nout Nin) = Δ i j := by
  have hexp : ∀ p : (Fin Nout → ℝ) × (Fin Nin → ℝ), sgdCoord Δ i j p
      = ∑ k, ∑ l, Δ k l * ((p.1 k * p.1 i) * (p.2 l * p.2 j)) := by
    intro p
    simp only [sgdCoord, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hint : ∀ k l, Integrable (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      (p.1 k * p.1 i) * (p.2 l * p.2 j)) (gaussBatch Nout Nin) := fun k l =>
    (cm_pair_int k i).mul_prod (cm_pair_int l j)
  have hk : ∀ k, Integrable (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      ∑ l, Δ k l * ((p.1 k * p.1 i) * (p.2 l * p.2 j))) (gaussBatch Nout Nin) := fun k =>
    integrable_finsetSum _ fun l _ => (hint k l).const_mul _
  have hprod : ∀ k l, ∫ p, (p.1 k * p.1 i) * (p.2 l * p.2 j) ∂(gaussBatch Nout Nin)
      = (Pi.single k (1 : ℝ) : Fin Nout → ℝ) i * (Pi.single l (1 : ℝ) : Fin Nin → ℝ) j := by
    intro k l
    unfold gaussBatch
    refine (integral_prod_mul (fun z : Fin Nout → ℝ => z k * z i)
      (fun w : Fin Nin → ℝ => w l * w j)).trans ?_
    simp only [cm_pair_moment]
  have key : ∫ p, ∑ k, ∑ l, Δ k l * ((p.1 k * p.1 i) * (p.2 l * p.2 j)) ∂(gaussBatch Nout Nin)
      = ∑ k, ∑ l, Δ k l * ((Pi.single k (1 : ℝ) : Fin Nout → ℝ) i
        * (Pi.single l (1 : ℝ) : Fin Nin → ℝ) j) := by
    rw [integral_finsetSum _ (fun k _ => hk k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ (fun l _ => (hint k l).const_mul _)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, hprod k l]
  simp only [hexp]
  rw [key]
  simp [Pi.single_apply, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- **lem:app-sgd-moments**, part (ii), `Muon.SignSGD.lem_app_sgd_moments_ii` (variance: the formula for s^2).

cr-2026-10-23. The lemma has seven conjuncts (i)-(vii); the LaTeX statement of the whole lemma, verbatim:

\begin{lemma}[Moments of one coordinate]\label{lem:app-sgd-moments}
The coordinate \cref{eqn:app-sgd-coordinate} has mean $\EE X=\Delta_{ij}$, variance
\[
s^2\defeq\Var X=F^2+2\norm{\Delta_{i\cdot}}^2+2\norm{\Delta_{\cdot j}}^2+3\Delta_{ij}^2,\qquad F^2\le s^2\le8F^2,
\]
and third centered moment
\[
m_3\defeq\EE(X-\Delta_{ij})^3=24\Delta_{ij}\norm{\bar\Delta}_\F^2+126\Delta_{ij}\big(\norm r^2+\norm q^2\big)+200\Delta_{ij}^3+54\,q^\T\bar\Delta r,
\]
so that $\abs{m_3}\le200\abs{\Delta_{ij}}F^2+54F\norm r\norm q$. For every
integer $p\ge1$, $\EE\abs X^p\le((2p-1)!!)^2F^p$, and the standardized
coordinate $Y\defeq(X-\Delta_{ij})/s$ satisfies $\EE Y^4\le88208$.
\end{lemma} -/
theorem lem_app_sgd_moments_ii {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0)
    (i : Fin Nout) (j : Fin Nin) :
    variance (sgdCoord Δ i j) (gaussBatch Nout Nin)
      = frobNorm Δ ^ 2 + 2 * (∑ l, Δ i l ^ 2) + 2 * (∑ k, Δ k j ^ 2) + 3 * Δ i j ^ 2 := by
  have hS : ∀ p : (Fin Nout → ℝ) × (Fin Nin → ℝ), sgdCoord Δ i j p
      = (∑ x : Fin Nout × Fin Nin, Δ x.1 x.2 * (p.1 x.1 * p.2 x.2)) * (p.1 i * p.2 j) := by
    intro p
    rw [Fintype.sum_prod_type]
    simp only [sgdCoord, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hG : ∀ p : (Fin Nout → ℝ) × (Fin Nin → ℝ), sgdCoord Δ i j p ^ 2
      = ∑ x : Fin Nout × Fin Nin, ∑ y : Fin Nout × Fin Nin,
          (Δ x.1 x.2 * Δ y.1 y.2) * ((p.1 x.1 * p.1 y.1 * p.1 i * p.1 i)
            * (p.2 x.2 * p.2 y.2 * p.2 j * p.2 j)) := by
    intro p
    rw [hS p, mul_pow, cm_sum_sq]
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have hIsq : Integrable (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) => sgdCoord Δ i j p ^ 2)
      ((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin)) := by
    simp only [hG]
    exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
      ((cm_quad_int x.1 y.1 i i).mul_prod (cm_quad_int x.2 y.2 j j)).const_mul _
  have hmeas : AEStronglyMeasurable (sgdCoord Δ i j) (gaussBatch Nout Nin) := by
    have hc : Continuous (sgdCoord Δ i j) := by
      have e : sgdCoord Δ i j = fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
          (∑ x : Fin Nout × Fin Nin, Δ x.1 x.2 * (p.1 x.1 * p.2 x.2)) * (p.1 i * p.2 j) :=
        funext hS
      rw [e]
      fun_prop
    exact hc.aestronglyMeasurable
  haveI : IsProbabilityMeasure (gaussBatch Nout Nin) := by
    unfold gaussBatch
    infer_instance
  have hmemLp : MemLp (sgdCoord Δ i j) 2 (gaussBatch Nout Nin) :=
    (memLp_two_iff_integrable_sq hmeas).2 hIsq
  have hmain : ∫ p, sgdCoord Δ i j p ^ 2 ∂(gaussBatch Nout Nin)
      = frobNorm Δ ^ 2 + 2 * (∑ l, Δ i l ^ 2) + 2 * (∑ k, Δ k j ^ 2) + 4 * Δ i j ^ 2 := by
    unfold gaussBatch
    rw [integral_prod_symm _ hIsq]
    have step : ∀ w : Fin Nin → ℝ,
        ∫ z, sgdCoord Δ i j (z, w) ^ 2 ∂(Muon.Foundations.stdGaussianPi Nout)
          = w j ^ 2 * ((∑ a, Matrix.mulVec Δ w a ^ 2) + 2 * Matrix.mulVec Δ w i ^ 2) := by
      intro w
      have e : ∀ z : Fin Nout → ℝ, sgdCoord Δ i j (z, w) ^ 2
          = w j ^ 2 * (dotProduct (Matrix.mulVec Δ w) z ^ 2 * z i ^ 2) := by
        intro z
        simp only [sgdCoord]
        rw [dotProduct_comm z]
        ring
      simp only [e]
      rw [integral_const_mul, Muon.Foundations.gaussian_weighted_square_moment]
    simp only [step]
    have hrw : ∀ w : Fin Nin → ℝ,
        w j ^ 2 * ((∑ a, Matrix.mulVec Δ w a ^ 2) + 2 * Matrix.mulVec Δ w i ^ 2)
          = (∑ a, dotProduct (Δ a) w ^ 2 * w j ^ 2) + 2 * (dotProduct (Δ i) w ^ 2 * w j ^ 2) := by
      intro w
      simp only [Matrix.mulVec]
      rw [mul_add, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun a _ => by ring
      · ring
    simp only [hrw]
    have hf : Integrable (fun w : Fin Nin → ℝ => ∑ a, dotProduct (Δ a) w ^ 2 * w j ^ 2)
        (Muon.Foundations.stdGaussianPi Nin) :=
      integrable_finsetSum _ fun a _ => cm_lin_sq_int (Δ a) j
    have hg : Integrable (fun w : Fin Nin → ℝ => 2 * (dotProduct (Δ i) w ^ 2 * w j ^ 2))
        (Muon.Foundations.stdGaussianPi Nin) :=
      (cm_lin_sq_int (Δ i) j).const_mul 2
    rw [integral_add hf hg, integral_finsetSum _ (fun a _ => cm_lin_sq_int (Δ a) j),
      integral_const_mul]
    simp only [Muon.Foundations.gaussian_weighted_square_moment]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [cm_frob_sq Δ]
    ring
  rw [variance_eq_sub hmemLp, lem_app_sgd_moments_i Δ hΔ i j]
  simp only [Pi.pow_apply]
  rw [hmain]
  ring

/-- **lem:app-sgd-moments**, part (iii), `Muon.SignSGD.lem_app_sgd_moments_iii` (F^2 <= s^2 <= 8 F^2).

cr-2026-10-23. The lemma has seven conjuncts (i)-(vii); the LaTeX statement of the whole lemma, verbatim:

\begin{lemma}[Moments of one coordinate]\label{lem:app-sgd-moments}
The coordinate \cref{eqn:app-sgd-coordinate} has mean $\EE X=\Delta_{ij}$, variance
\[
s^2\defeq\Var X=F^2+2\norm{\Delta_{i\cdot}}^2+2\norm{\Delta_{\cdot j}}^2+3\Delta_{ij}^2,\qquad F^2\le s^2\le8F^2,
\]
and third centered moment
\[
m_3\defeq\EE(X-\Delta_{ij})^3=24\Delta_{ij}\norm{\bar\Delta}_\F^2+126\Delta_{ij}\big(\norm r^2+\norm q^2\big)+200\Delta_{ij}^3+54\,q^\T\bar\Delta r,
\]
so that $\abs{m_3}\le200\abs{\Delta_{ij}}F^2+54F\norm r\norm q$. For every
integer $p\ge1$, $\EE\abs X^p\le((2p-1)!!)^2F^p$, and the standardized
coordinate $Y\defeq(X-\Delta_{ij})/s$ satisfies $\EE Y^4\le88208$.
\end{lemma} -/
theorem lem_app_sgd_moments_iii {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0)
    (i : Fin Nout) (j : Fin Nin) :
    frobNorm Δ ^ 2 ≤ variance (sgdCoord Δ i j) (gaussBatch Nout Nin) ∧
      variance (sgdCoord Δ i j) (gaussBatch Nout Nin) ≤ 8 * frobNorm Δ ^ 2 := by
  have h2 := lem_app_sgd_moments_ii Δ hΔ i j
  have hA : 0 ≤ ∑ l, Δ i l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hB : 0 ≤ ∑ k, Δ k j ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hrow : Δ i j ^ 2 ≤ ∑ b, Δ i b ^ 2 :=
    Finset.single_le_sum (f := fun b => Δ i b ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ j)
  have hrow' : ∑ b, Δ i b ^ 2 ≤ ∑ a, ∑ b, Δ a b ^ 2 :=
    Finset.single_le_sum (f := fun a => ∑ b, Δ a b ^ 2)
      (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.mem_univ i)
  have hcol : ∑ k, Δ k j ^ 2 ≤ ∑ a, ∑ b, Δ a b ^ 2 :=
    Finset.sum_le_sum fun k _ =>
      Finset.single_le_sum (f := fun b => Δ k b ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ j)
  rw [h2, cm_frob_sq Δ]
  constructor <;> linarith [sq_nonneg (Δ i j)]

/-- Helper (sign-SGD, part (v)): the deleted block, the row `r` and the column `q` together with
`Δ_ij` exhaust the squared entries of `Δ`: `F² = ‖Δ̄‖_F² + ‖r‖² + ‖q‖² + Δ_ij²`. -/
private lemma cm_split_frob {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) :
    frobNorm Δ ^ 2 = frobNorm (sgdDeletedBlock Δ i j) ^ 2 + (∑ l, sgdRow Δ i j l ^ 2)
      + (∑ k, sgdCol Δ i j k ^ 2) + Δ i j ^ 2 := by
  rw [cm_frob_sq, cm_frob_sq]
  have hpt : ∀ a b, Δ a b ^ 2 = sgdDeletedBlock Δ i j a b ^ 2
      + (if a = i then sgdRow Δ i j b ^ 2 else 0)
      + (if a = i then (if b = j then Δ i j ^ 2 else 0) else 0)
      + (if b = j then sgdCol Δ i j a ^ 2 else 0) := by
    intro a b
    by_cases ha : a = i <;> by_cases hb : b = j <;>
      simp [sgdDeletedBlock, sgdRow, sgdCol, ha, hb]
  have e : ∑ a, ∑ b, Δ a b ^ 2 = ∑ a, ∑ b, (sgdDeletedBlock Δ i j a b ^ 2
      + (if a = i then sgdRow Δ i j b ^ 2 else 0)
      + (if a = i then (if b = j then Δ i j ^ 2 else 0) else 0)
      + (if b = j then sgdCol Δ i j a ^ 2 else 0)) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hpt a b
  rw [e]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq]
  ring

/-- Helper (sign-SGD, part (v)): Cauchy–Schwarz for the bilinear form `qᵀ Δ̄ r`:
`(qᵀ Δ̄ r)² ≤ ‖Δ̄‖_F² ‖q‖² ‖r‖²`. -/
private lemma cm_bilin_cs {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) :
    dotProduct (sgdCol Δ i j) (Matrix.mulVec (sgdDeletedBlock Δ i j) (sgdRow Δ i j)) ^ 2
      ≤ frobNorm (sgdDeletedBlock Δ i j) ^ 2
        * ((∑ k, sgdCol Δ i j k ^ 2) * (∑ l, sgdRow Δ i j l ^ 2)) := by
  have hdot : dotProduct (sgdCol Δ i j) (Matrix.mulVec (sgdDeletedBlock Δ i j) (sgdRow Δ i j))
      = ∑ x : Fin Nout × Fin Nin, sgdDeletedBlock Δ i j x.1 x.2
          * (sgdCol Δ i j x.1 * sgdRow Δ i j x.2) := by
    rw [Fintype.sum_prod_type]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hqr : ∑ x : Fin Nout × Fin Nin, (sgdCol Δ i j x.1 * sgdRow Δ i j x.2) ^ 2
      = (∑ k, sgdCol Δ i j k ^ 2) * (∑ l, sgdRow Δ i j l ^ 2) := by
    rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hD : ∑ x : Fin Nout × Fin Nin, sgdDeletedBlock Δ i j x.1 x.2 ^ 2
      = frobNorm (sgdDeletedBlock Δ i j) ^ 2 := by
    rw [Fintype.sum_prod_type, cm_frob_sq]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin Nout × Fin Nin))
    (fun x => sgdDeletedBlock Δ i j x.1 x.2) (fun x => sgdCol Δ i j x.1 * sgdRow Δ i j x.2)
  rw [hdot, ← hD, ← hqr]
  exact h

/-! ## Private helpers for part (iv) -/

private def Mom {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) : Prop :=
  Measurable f ∧ ∀ p : ℕ, Integrable (fun x => f x ^ (2 * p)) μ

private lemma mom_const {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (c : ℝ) :
    Mom μ (fun _ : α => c) :=
  ⟨measurable_const, fun _ => integrable_const _⟩

private lemma mom_mul {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ}
    (hf : Mom μ f)
    (hg : Mom μ g) :
    Mom μ (fun x => f x * g x) := by
  refine ⟨hf.1.mul hg.1, fun p => ?_⟩
  have h1 := hf.2 (2 * p)
  have h2 := hg.2 (2 * p)
  refine Integrable.mono' (h1.add h2) ((hf.1.mul hg.1).pow_const _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have e1 : (f x * g x) ^ (2 * p) = f x ^ (2 * p) * g x ^ (2 * p) := mul_pow _ _ _
  have e2 : f x ^ (2 * (2 * p)) = (f x ^ (2 * p)) ^ 2 := by rw [← pow_mul]; ring_nf
  have e3 : g x ^ (2 * (2 * p)) = (g x ^ (2 * p)) ^ 2 := by rw [← pow_mul]; ring_nf
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [e1, e2, e3]
  have a0 : 0 ≤ f x ^ (2 * p) := by rw [pow_mul]; positivity
  have b0 : 0 ≤ g x ^ (2 * p) := by rw [pow_mul]; positivity
  rw [abs_of_nonneg (mul_nonneg a0 b0)]
  nlinarith [sq_nonneg (f x ^ (2 * p) - g x ^ (2 * p)), mul_nonneg a0 b0]

private lemma mom_add {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ}
    (hf : Mom μ f)
    (hg : Mom μ g) :
    Mom μ (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, fun p => ?_⟩
  have h := ((hf.2 p).add (hg.2 p)).const_mul ((2:ℝ) ^ (2 * p))
  refine Integrable.mono' h ((hf.1.add hg.1).pow_const _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hsq : (f x + g x) ^ 2 ≤ 2 * (f x ^ 2 + g x ^ 2) := by
    nlinarith [sq_nonneg (f x - g x)]
  have a0 : 0 ≤ f x ^ 2 := sq_nonneg _
  have b0 : 0 ≤ g x ^ 2 := sq_nonneg _
  have s1 : (f x + g x) ^ (2 * p) ≤ (2 * (f x ^ 2 + g x ^ 2)) ^ p := by
    rw [pow_mul]; exact pow_le_pow_left₀ (sq_nonneg _) hsq p
  have s2 := add_pow_le a0 b0 p
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg (by rw [pow_mul]; positivity)]
  calc (f x + g x) ^ (2 * p) ≤ (2 * (f x ^ 2 + g x ^ 2)) ^ p := s1
    _ = 2 ^ p * (f x ^ 2 + g x ^ 2) ^ p := mul_pow _ _ _
    _ ≤ 2 ^ p * (2 ^ (p - 1) * ((f x ^ 2) ^ p + (g x ^ 2) ^ p)) := by gcongr
    _ ≤ (2:ℝ) ^ (2 * p) * ((f x) ^ (2 * p) + g x ^ (2 * p)) := by
        rw [← pow_mul, ← pow_mul]
        have : (2:ℝ) ^ p * 2 ^ (p - 1) ≤ 2 ^ (2 * p) := by
          rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
        have h3 : 0 ≤ f x ^ (2 * p) + g x ^ (2 * p) := by
          have := a0; have := b0
          rw [pow_mul, pow_mul]; positivity
        calc (2:ℝ) ^ p * (2 ^ (p - 1) * (f x ^ (2 * p) + g x ^ (2 * p)))
            = (2 ^ p * 2 ^ (p - 1)) * (f x ^ (2 * p) + g x ^ (2 * p)) := by ring
          _ ≤ _ := by gcongr
    _ = _ := by simp [Pi.add_apply]


private lemma mom_sub {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f g : α → ℝ} (hf : Mom μ f) (hg : Mom μ g) : Mom μ (fun x => f x - g x) := by
  have := mom_add μ hf (mom_mul μ (mom_const μ (-1)) hg)
  simpa [sub_eq_add_neg] using this

private lemma mom_pow {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Mom μ f) (k : ℕ) : Mom μ (fun x => f x ^ k) := by
  induction k with
  | zero => simpa using mom_const μ 1
  | succ k ih => simpa [pow_succ] using mom_mul μ ih hf

private lemma mom_integrable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Mom μ f) : Integrable f μ := by
  have h := (hf.2 1).add (integrable_const (1 : ℝ))
  refine Integrable.mono' h hf.1.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply, mul_one, pow_one]
  nlinarith [sq_abs (f x), abs_nonneg (f x), sq_nonneg (|f x| - 1)]

private lemma mom_sum {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {ι : Type*} (s : Finset ι) {f : ι → α → ℝ} (hf : ∀ k, Mom μ (f k)) :
    Mom μ (fun x => ∑ k ∈ s, f k x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mom_const μ 0
  | insert a s ha ih => simpa [Finset.sum_insert ha] using mom_add μ (hf a) ih

private lemma slice_pi (n : ℕ) (i : Fin n) (f : (Fin n → ℝ) → ℝ)
    (hf : Integrable f (Muon.Foundations.stdGaussianPi n)) :
    ∫ z, f z ∂(Muon.Foundations.stdGaussianPi n)
      = ∫ z, ∫ x, f (Function.update z i x) ∂(gaussianReal 0 1)
          ∂(Muon.Foundations.stdGaussianPi n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal (0 : ℝ) 1) i
  have hg : ∀ F : (Fin (m + 1) → ℝ) → ℝ, ∫ z, F z ∂(Muon.Foundations.stdGaussianPi (m + 1))
      = ∫ p, F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm p)
          ∂((gaussianReal 0 1).prod (Muon.Foundations.stdGaussianPi m)) := by
    intro F
    have := hmp.integral_comp' (g := fun p => F ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (m + 1) => ℝ) i).symm p))
    simp only [MeasurableEquiv.symm_apply_apply] at this
    exact this
  have hint' : Integrable (fun p => f ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (m + 1) => ℝ) i).symm p))
      ((gaussianReal 0 1).prod (Muon.Foundations.stdGaussianPi m)) :=
    (MeasurePreserving.symm _ hmp).integrable_comp_of_integrable hf
  have hL : ∫ z, f z ∂(Muon.Foundations.stdGaussianPi (m + 1))
      = ∫ y, ∫ x, f (i.insertNth x y) ∂(gaussianReal 0 1) ∂(Muon.Foundations.stdGaussianPi m) := by
    rw [hg, integral_prod_symm _ hint']
    rfl
  rw [hL, hg (fun z => ∫ x, f (Function.update z i x) ∂(gaussianReal 0 1))]
  have e : ∀ p : ℝ × (Fin m → ℝ),
      ∫ x, f (Function.update ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm p)
        i x) ∂(gaussianReal 0 1) = ∫ x, f (i.insertNth x p.2) ∂(gaussianReal 0 1) := by
    intro p
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.update_insertNth]
  simp only [e]
  refine Eq.trans ?_ (integral_fun_snd (μ := gaussianReal 0 1)
    (ν := Muon.Foundations.stdGaussianPi m)
    (fun y => ∫ x, f (i.insertNth x y) ∂(gaussianReal 0 1))).symm
  simp

private lemma gint6 (c0 c1 c2 c3 c4 c5 c6 : ℝ) :
    ∫ x : ℝ, (c0 * x ^ 0 + c1 * x ^ 1 + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4 + c5 * x ^ 5
      + c6 * x ^ 6) ∂(gaussianReal 0 1) = c0 + c2 + 3 * c4 + 15 * c6 := by
  have I : ∀ (k : ℕ) (c : ℝ), Integrable (fun x : ℝ => c * x ^ k) (gaussianReal 0 1) :=
    fun k c => (Muon.Foundations.gaussian_integrable_pow k).const_mul c
  have M : ∀ (k : ℕ) (c : ℝ), ∫ x : ℝ, c * x ^ k ∂(gaussianReal 0 1)
      = c * ∫ x : ℝ, x ^ k ∂(gaussianReal 0 1) := fun k c => integral_const_mul c _
  have h1 : Integrable (fun x : ℝ => c0 * x ^ 0 + c1 * x ^ 1) (gaussianReal 0 1) :=
    (I 0 c0).add (I 1 c1)
  have h2 : Integrable (fun x : ℝ => c0 * x ^ 0 + c1 * x ^ 1 + c2 * x ^ 2) (gaussianReal 0 1) :=
    h1.add (I 2 c2)
  have h3 : Integrable (fun x : ℝ => c0 * x ^ 0 + c1 * x ^ 1 + c2 * x ^ 2 + c3 * x ^ 3)
      (gaussianReal 0 1) := h2.add (I 3 c3)
  have h4 : Integrable (fun x : ℝ => c0 * x ^ 0 + c1 * x ^ 1 + c2 * x ^ 2 + c3 * x ^ 3
      + c4 * x ^ 4) (gaussianReal 0 1) := h3.add (I 4 c4)
  have h5 : Integrable (fun x : ℝ => c0 * x ^ 0 + c1 * x ^ 1 + c2 * x ^ 2 + c3 * x ^ 3
      + c4 * x ^ 4 + c5 * x ^ 5) (gaussianReal 0 1) := h4.add (I 5 c5)
  rw [integral_add h5 (I 6 c6), integral_add h4 (I 5 c5), integral_add h3 (I 4 c4),
    integral_add h2 (I 3 c3), integral_add h1 (I 2 c2), integral_add (I 0 c0) (I 1 c1),
    M, M, M, M, M, M, M]
  have o1 := Muon.Foundations.gaussian_moment_odd 0
  have o3 := Muon.Foundations.gaussian_moment_odd 1
  have o5 := Muon.Foundations.gaussian_moment_odd 2
  simp only [Nat.mul_zero, zero_add, Nat.reduceMul, Nat.reduceAdd, pow_one] at o1 o3 o5
  simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, one_mul, pow_one]
  rw [o1, o3, o5, Muon.Foundations.gaussian_moment_two, Muon.Foundations.gaussian_moment_four,
    Muon.Foundations.gaussian_moment_six]
  ring


private lemma int_P (D : ℝ) (E1 : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hE : ∀ y a b c : ℝ, E1 y a b c = 15*D^3*y^6 - 9*D^3*y^4 + 3*D^3*y^2 - D^3 + 45*D^2*a*y^5 - 18*D^2*a*y^3 + 3*D^2*a*y + 45*D*a^2*y^4 - 9*D*a^2*y^2 + 9*D*b^2*y^6 - 3*D*b^2*y^4 + 18*D*b*c*y^5 - 6*D*b*c*y^3 + 9*D*c^2*y^4 - 3*D*c^2*y^2 + 15*a^3*y^3 + 9*a*b^2*y^5 + 18*a*b*c*y^4 + 9*a*c^2*y^3) (y a b c : ℝ) :
    ∫ x : ℝ, (x * y * (D * x * y + x * a + y * b + c) - D) ^ 3 ∂(gaussianReal 0 1)
      = E1 y a b c := by
  rw [hE]
  have h := gint6 (-D^3) (3*D^2*b*y^2 + 3*D^2*c*y) (3*D^3*y^2 + 3*D^2*a*y - 3*D*b^2*y^4 - 6*D*b*c*y^3 - 3*D*c^2*y^2) (-6*D^2*b*y^4 - 6*D^2*c*y^3 - 6*D*a*b*y^3 - 6*D*a*c*y^2 + b^3*y^6 + 3*b^2*c*y^5 + 3*b*c^2*y^4 + c^3*y^3) (-3*D^3*y^4 - 6*D^2*a*y^3 - 3*D*a^2*y^2 + 3*D*b^2*y^6 + 6*D*b*c*y^5 + 3*D*c^2*y^4 + 3*a*b^2*y^5 + 6*a*b*c*y^4 + 3*a*c^2*y^3) (3*D^2*b*y^6 + 3*D^2*c*y^5 + 6*D*a*b*y^5 + 6*D*a*c*y^4 + 3*a^2*b*y^4 + 3*a^2*c*y^3) (D^3*y^6 + 3*D^2*a*y^5 + 3*D*a^2*y^4 + a^3*y^3)
  refine Eq.trans ?_ (h.trans (by ring))
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

private lemma int_E1 (D : ℝ) (E1 : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hE : ∀ y a b c : ℝ, E1 y a b c = 15*D^3*y^6 - 9*D^3*y^4 + 3*D^3*y^2 - D^3 + 45*D^2*a*y^5 - 18*D^2*a*y^3 + 3*D^2*a*y + 45*D*a^2*y^4 - 9*D*a^2*y^2 + 9*D*b^2*y^6 - 3*D*b^2*y^4 + 18*D*b*c*y^5 - 6*D*b*c*y^3 + 9*D*c^2*y^4 - 3*D*c^2*y^2 + 15*a^3*y^3 + 9*a*b^2*y^5 + 18*a*b*c*y^4 + 9*a*c^2*y^3) (a b c : ℝ) :
    ∫ y : ℝ, E1 y a b c ∂(gaussianReal 0 1)
      = 126 * D * a ^ 2 + 54 * a * b * c + 126 * D * b ^ 2 + 24 * D * c ^ 2 + 200 * D ^ 3 := by
  have h := gint6 (-D^3) (3*D^2*a) (3*D^3 - 9*D*a^2 - 3*D*c^2) (-18*D^2*a - 6*D*b*c + 15*a^3 + 9*a*c^2) (-9*D^3 + 45*D*a^2 - 3*D*b^2 + 9*D*c^2 + 18*a*b*c) (45*D^2*a + 18*D*b*c + 9*a*b^2) (15*D^3 + 9*D*b^2)
  have e : ∀ y : ℝ, E1 y a b c = (-D^3) * y ^ 0 + (3*D^2*a) * y ^ 1 + (3*D^3 - 9*D*a^2 - 3*D*c^2) * y ^ 2 + (-18*D^2*a - 6*D*b*c + 15*a^3 + 9*a*c^2) * y ^ 3 + (-9*D^3 + 45*D*a^2 - 3*D*b^2 + 9*D*c^2 + 18*a*b*c) * y ^ 4 + (45*D^2*a + 18*D*b*c + 9*a*b^2) * y ^ 5 + (15*D^3 + 9*D*b^2) * y ^ 6 := fun y => by rw [hE]; ring
  simp only [e]
  rw [h]
  ring

private lemma mom_E1 {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (D : ℝ) (E1 : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hE : ∀ y a b c : ℝ, E1 y a b c = 15*D^3*y^6 - 9*D^3*y^4 + 3*D^3*y^2 - D^3 + 45*D^2*a*y^5 - 18*D^2*a*y^3 + 3*D^2*a*y + 45*D*a^2*y^4 - 9*D*a^2*y^2 + 9*D*b^2*y^6 - 3*D*b^2*y^4 + 18*D*b*c*y^5 - 6*D*b*c*y^3 + 9*D*c^2*y^4 - 3*D*c^2*y^2 + 15*a^3*y^3 + 9*a*b^2*y^5 + 18*a*b*c*y^4 + 9*a*c^2*y^3)
    {y a b c : α → ℝ} (hy : Mom μ y) (ha : Mom μ a) (hb : Mom μ b) (hc : Mom μ c) :
    Mom μ (fun x => E1 (y x) (a x) (b x) (c x)) := by
  simp only [hE]
  repeat' first
    | exact mom_const μ _
    | assumption
    | apply mom_sub
    | apply mom_add
    | apply mom_mul
    | apply mom_pow


private lemma exists_E1 (D : ℝ) :
    ∃ E1 : ℝ → ℝ → ℝ → ℝ → ℝ, ∀ y a b c : ℝ, E1 y a b c = 15*D^3*y^6 - 9*D^3*y^4 + 3*D^3*y^2 - D^3 + 45*D^2*a*y^5 - 18*D^2*a*y^3 + 3*D^2*a*y + 45*D*a^2*y^4 - 9*D*a^2*y^2 + 9*D*b^2*y^6 - 3*D*b^2*y^4 + 18*D*b*c*y^5 - 6*D*b*c*y^3 + 9*D*c^2*y^4 - 3*D*c^2*y^2 + 15*a^3*y^3 + 9*a*b^2*y^5 + 18*a*b*c*y^4 + 9*a*c^2*y^3 :=
  ⟨fun y a b c => 15*D^3*y^6 - 9*D^3*y^4 + 3*D^3*y^2 - D^3 + 45*D^2*a*y^5 - 18*D^2*a*y^3 + 3*D^2*a*y + 45*D*a^2*y^4 - 9*D*a^2*y^2 + 9*D*b^2*y^6 - 3*D*b^2*y^4 + 18*D*b*c*y^5 - 6*D*b*c*y^3 + 9*D*c^2*y^4 - 3*D*c^2*y^2 + 15*a^3*y^3 + 9*a*b^2*y^5 + 18*a*b*c*y^4 + 9*a*c^2*y^3, fun _ _ _ _ => rfl⟩

private lemma mom_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [SigmaFinite μ] [IsFiniteMeasure ν] {f : α → ℝ} (hf : Mom μ f) :
    Mom (μ.prod ν) (fun p => f p.1) := by
  refine ⟨hf.1.comp measurable_fst, fun p => ?_⟩
  have := (hf.2 p).mul_prod (integrable_const (1 : ℝ)) (ν := ν)
  simpa using this

private lemma mom_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [IsFiniteMeasure μ] [SigmaFinite ν] {g : β → ℝ} (hg : Mom ν g) :
    Mom (μ.prod ν) (fun p => g p.2) := by
  refine ⟨hg.1.comp measurable_snd, fun p => ?_⟩
  have := (integrable_const (1 : ℝ)).mul_prod (hg.2 p) (μ := μ)
  simpa using this

private lemma mom_coord (n : ℕ) (i : Fin n) :
    Mom (Muon.Foundations.stdGaussianPi n) (fun z : Fin n → ℝ => z i) := by
  refine ⟨measurable_pi_apply i, fun p => ?_⟩
  have h := cm_mono_integrable (n := n) (fun _ : Fin (2 * p) => i)
  simpa [Finset.prod_const] using h

private lemma mom_dot (n : ℕ) (u : Fin n → ℝ) :
    Mom (Muon.Foundations.stdGaussianPi n) (fun z : Fin n → ℝ => dotProduct u z) := by
  have h := mom_sum (Muon.Foundations.stdGaussianPi n) (Finset.univ : Finset (Fin n))
    (f := fun k z => u k * z k)
    (fun k => mom_mul _ (mom_const _ (u k)) (mom_coord n k))
  exact h

private lemma mom_P {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {ξ ζ a b c : α → ℝ} (D : ℝ) (hξ : Mom μ ξ) (hζ : Mom μ ζ) (ha : Mom μ a) (hb : Mom μ b)
    (hc : Mom μ c) :
    Mom μ (fun x => (ξ x * ζ x * (D * ξ x * ζ x + ξ x * a x + ζ x * b x + c x) - D) ^ 3) := by
  repeat' first
    | exact mom_const μ _
    | assumption
    | apply mom_sub
    | apply mom_add
    | apply mom_mul
    | apply mom_pow

private lemma mom_Q2 {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {a b c : α → ℝ} (D : ℝ) (ha : Mom μ a) (hb : Mom μ b) (hc : Mom μ c) :
    Mom μ (fun x => 126 * D * a x ^ 2 + 54 * a x * b x * c x + 126 * D * b x ^ 2
      + 24 * D * c x ^ 2 + 200 * D ^ 3) := by
  repeat' first
    | exact mom_const μ _
    | assumption
    | apply mom_sub
    | apply mom_add
    | apply mom_mul
    | apply mom_pow

private lemma main_gen {Nout Nin : ℕ} (D : ℝ) (i : Fin Nout) (j : Fin Nin)
    (A : (Fin Nin → ℝ) → ℝ) (B : (Fin Nout → ℝ) → ℝ)
    (C : (Fin Nout → ℝ) → (Fin Nin → ℝ) → ℝ)
    (hA : Mom (Muon.Foundations.stdGaussianPi Nin) A)
    (hB : Mom (Muon.Foundations.stdGaussianPi Nout) B)
    (hCz : ∀ w, Mom (Muon.Foundations.stdGaussianPi Nout) (fun z => C z w))
    (hCw : ∀ z, Mom (Muon.Foundations.stdGaussianPi Nin) (fun w => C z w))
    (hCb : Mom ((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin))
      (fun p => C p.1 p.2))
    (hAj : ∀ w y, A (Function.update w j y) = A w)
    (hBi : ∀ z x, B (Function.update z i x) = B z)
    (hCi : ∀ z w x, C (Function.update z i x) w = C z w)
    (hCj : ∀ z w y, C z (Function.update w j y) = C z w) :
    ∫ p : (Fin Nout → ℝ) × (Fin Nin → ℝ),
        (p.1 i * p.2 j * (D * p.1 i * p.2 j + p.1 i * A p.2 + p.2 j * B p.1 + C p.1 p.2) - D) ^ 3
      ∂((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin))
    = ∫ p : (Fin Nout → ℝ) × (Fin Nin → ℝ),
        (126 * D * A p.2 ^ 2 + 54 * A p.2 * B p.1 * C p.1 p.2 + 126 * D * B p.1 ^ 2
          + 24 * D * C p.1 p.2 ^ 2 + 200 * D ^ 3)
      ∂((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin)) := by
  set μ := Muon.Foundations.stdGaussianPi Nout with hμ
  set ν := Muon.Foundations.stdGaussianPi Nin with hν
  have hξ : Mom (μ.prod ν) (fun p => p.1 i) := mom_fst μ ν (mom_coord Nout i)
  have hζ : Mom (μ.prod ν) (fun p => p.2 j) := mom_snd μ ν (mom_coord Nin j)
  have hA' : Mom (μ.prod ν) (fun p => A p.2) := mom_snd μ ν hA
  have hB' : Mom (μ.prod ν) (fun p => B p.1) := mom_fst μ ν hB
  have hF := mom_integrable _ (mom_P (μ.prod ν) D hξ hζ hA' hB' hCb)
  obtain ⟨E1, hE⟩ := exists_E1 D
  have hG := mom_integrable _ (mom_E1 (μ.prod ν) D E1 hE hζ hA' hB' hCb)
  have hQ := mom_integrable _ (mom_Q2 (μ.prod ν) D hA' hB' hCb)
  -- step 1: integrate out `ξ`
  have step1 : ∀ w : Fin Nin → ℝ,
      ∫ z, (z i * w j * (D * z i * w j + z i * A w + w j * B z + C z w) - D) ^ 3 ∂μ
        = ∫ z, E1 (w j) (A w) (B z) (C z w) ∂μ := by
    intro w
    have hint : Integrable (fun z => (z i * w j * (D * z i * w j + z i * A w + w j * B z
        + C z w) - D) ^ 3) μ :=
      mom_integrable _ (mom_P μ D (mom_coord Nout i) (mom_const μ (w j)) (mom_const μ (A w)) hB
        (hCz w))
    rw [slice_pi Nout i _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.update_self, hBi, hCi]
    exact int_P D E1 hE (w j) (A w) (B z) (C z w)
  -- step 2: integrate out `ζ`
  have step2 : ∀ z : Fin Nout → ℝ,
      ∫ w, E1 (w j) (A w) (B z) (C z w) ∂ν
        = ∫ w, (126 * D * A w ^ 2 + 54 * A w * B z * C z w + 126 * D * B z ^ 2
          + 24 * D * C z w ^ 2 + 200 * D ^ 3) ∂ν := by
    intro z
    have hint : Integrable (fun w => E1 (w j) (A w) (B z) (C z w)) ν :=
      mom_integrable _ (mom_E1 ν D E1 hE (mom_coord Nin j) hA (mom_const ν (B z)) (hCw z))
    rw [slice_pi Nin j _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Function.update_self, hAj, hCj]
    exact int_E1 D E1 hE (A w) (B z) (C z w)
  rw [integral_prod_symm _ hF]
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun w => step1 w)) ?_
  rw [← integral_prod_symm (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
    E1 (p.2 j) (A p.2) (B p.1) (C p.1 p.2)) hG, integral_prod _ hG]
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => step2 z)) ?_
  rw [← integral_prod _ hQ]

private lemma lin_bil (n : ℕ) (a b : Fin n → ℝ) :
    ∫ z, dotProduct a z * dotProduct b z ∂(Muon.Foundations.stdGaussianPi n) = dotProduct a b := by
  have e : ∀ z : Fin n → ℝ, dotProduct a z * dotProduct b z
      = ∑ p, ∑ q, (a p * b q) * (z p * z q) := by
    intro z
    simp only [dotProduct]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  simp only [e]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ fun q _ =>
    (cm_pair_int p q).const_mul _)]
  simp only [fun p => integral_finsetSum Finset.univ
    (fun q _ => (cm_pair_int p q).const_mul (a p * b q)), integral_const_mul, cm_pair_moment]
  simp [Pi.single_apply, dotProduct]

private lemma dot_update {n : ℕ} (u : Fin n → ℝ) (i : Fin n) (hu : u i = 0) (z : Fin n → ℝ)
    (x : ℝ) : dotProduct u (Function.update z i x) = dotProduct u z := by
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = i
  · subst hk; simp [hu]
  · simp [Function.update_of_ne hk]

private lemma sgd_decomp {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) (z : Fin Nout → ℝ) (w : Fin Nin → ℝ) :
    dotProduct z (Matrix.mulVec Δ w)
      = Δ i j * z i * w j + z i * dotProduct (sgdRow Δ i j) w + w j * dotProduct (sgdCol Δ i j) z
        + dotProduct z (Matrix.mulVec (sgdDeletedBlock Δ i j) w) := by
  have hΔ : ∀ k l, Δ k l = sgdDeletedBlock Δ i j k l + (if k = i then sgdRow Δ i j l else 0)
      + (if l = j then sgdCol Δ i j k else 0)
      + (if k = i then (if l = j then Δ i j else 0) else 0) := by
    intro k l
    by_cases hk : k = i <;> by_cases hl : l = j <;>
      simp [sgdDeletedBlock, sgdRow, sgdCol, hk, hl]
  have e : dotProduct z (Matrix.mulVec Δ w) = ∑ k, ∑ l, z k * w l * Δ k l := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [e]
  have e2 : ∑ k, ∑ l, z k * w l * Δ k l = ∑ k, ∑ l, (z k * w l * sgdDeletedBlock Δ i j k l
      + z k * w l * (if k = i then sgdRow Δ i j l else 0)
      + z k * w l * (if l = j then sgdCol Δ i j k else 0)
      + z k * w l * (if k = i then (if l = j then Δ i j else 0) else 0)) := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_add, ← mul_add, ← mul_add, ← hΔ]
  rw [e2]
  simp only [Finset.sum_add_distrib]
  have f1 : ∑ k, ∑ l, z k * w l * sgdDeletedBlock Δ i j k l
      = dotProduct z (Matrix.mulVec (sgdDeletedBlock Δ i j) w) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have f2 : ∑ k, ∑ l, z k * w l * (if k = i then sgdRow Δ i j l else 0)
      = z i * dotProduct (sgdRow Δ i j) w := by
    simp [mul_ite, Finset.sum_ite_eq', dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have f3 : ∑ k, ∑ l, z k * w l * (if l = j then sgdCol Δ i j k else 0)
      = w j * dotProduct (sgdCol Δ i j) z := by
    simp [mul_ite, Finset.sum_ite_eq', dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have f4 : ∑ k, ∑ l, z k * w l * (if k = i then (if l = j then Δ i j else 0) else 0)
      = Δ i j * z i * w j := by
    simp [mul_ite]
    ring
  rw [f1, f2, f3, f4]
  ring

private lemma mom_Cb {Nout Nin : ℕ} (M : Matrix (Fin Nout) (Fin Nin) ℝ) :
    Mom ((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin))
      (fun p => dotProduct p.1 (Matrix.mulVec M p.2)) := by
  have e : (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) => dotProduct p.1 (Matrix.mulVec M p.2))
      = fun p => ∑ k, ∑ l, M k l * (p.1 k * p.2 l) := by
    funext p
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [e]
  exact mom_sum _ _ fun k => mom_sum _ _ fun l => mom_mul _ (mom_const _ _)
    (mom_mul _ (mom_fst _ _ (mom_coord Nout k)) (mom_snd _ _ (mom_coord Nin l)))

private lemma q2_batch {Nout Nin : ℕ} (M : Matrix (Fin Nout) (Fin Nin) ℝ) (r : Fin Nin → ℝ)
    (q : Fin Nout → ℝ) (D : ℝ) :
    ∫ p : (Fin Nout → ℝ) × (Fin Nin → ℝ),
        (126 * D * dotProduct r p.2 ^ 2
          + 54 * dotProduct r p.2 * dotProduct q p.1 * dotProduct p.1 (Matrix.mulVec M p.2)
          + 126 * D * dotProduct q p.1 ^ 2
          + 24 * D * dotProduct p.1 (Matrix.mulVec M p.2) ^ 2 + 200 * D ^ 3)
      ∂((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin))
    = 126 * D * dotProduct r r + 54 * dotProduct q (Matrix.mulVec M r)
      + 126 * D * dotProduct q q + 24 * D * (∑ k, ∑ l, M k l ^ 2) + 200 * D ^ 3 := by
  set μ := Muon.Foundations.stdGaussianPi Nout with hμ
  set ν := Muon.Foundations.stdGaussianPi Nin with hν
  have hA' : Mom (μ.prod ν) (fun p => dotProduct r p.2) := mom_snd μ ν (mom_dot Nin r)
  have hB' : Mom (μ.prod ν) (fun p => dotProduct q p.1) := mom_fst μ ν (mom_dot Nout q)
  have hCb : Mom (μ.prod ν) (fun p => dotProduct p.1 (Matrix.mulVec M p.2)) := mom_Cb M
  have i1 : Integrable (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      126 * D * dotProduct r p.2 ^ 2) (μ.prod ν) := by
    refine mom_integrable _ ?_
    repeat' first
      | exact mom_const _ _
      | assumption
      | apply mom_mul
      | apply mom_pow
  have i2 : Integrable (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      54 * dotProduct r p.2 * dotProduct q p.1 * dotProduct p.1 (Matrix.mulVec M p.2))
      (μ.prod ν) := by
    refine mom_integrable _ ?_
    repeat' first
      | exact mom_const _ _
      | assumption
      | apply mom_mul
      | apply mom_pow
  have i3 : Integrable (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      126 * D * dotProduct q p.1 ^ 2) (μ.prod ν) := by
    refine mom_integrable _ ?_
    repeat' first
      | exact mom_const _ _
      | assumption
      | apply mom_mul
      | apply mom_pow
  have i4 : Integrable (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      24 * D * dotProduct p.1 (Matrix.mulVec M p.2) ^ 2) (μ.prod ν) := by
    refine mom_integrable _ ?_
    repeat' first
      | exact mom_const _ _
      | assumption
      | apply mom_mul
      | apply mom_pow
  have i5 : Integrable (fun _ : (Fin Nout → ℝ) × (Fin Nin → ℝ) => 200 * D ^ 3) (μ.prod ν) :=
    integrable_const _
  -- the four moments
  have m1 : ∫ p : (Fin Nout → ℝ) × (Fin Nin → ℝ), dotProduct r p.2 ^ 2 ∂(μ.prod ν)
      = dotProduct r r := by
    rw [integral_fun_snd (μ := μ) (ν := ν) (fun w => dotProduct r w ^ 2), probReal_univ, one_smul]
    simp only [sq]
    exact lin_bil Nin r r
  have m2 : ∫ p : (Fin Nout → ℝ) × (Fin Nin → ℝ), dotProduct q p.1 ^ 2 ∂(μ.prod ν)
      = dotProduct q q := by
    rw [integral_fun_fst (μ := μ) (ν := ν) (fun z => dotProduct q z ^ 2), probReal_univ, one_smul]
    simp only [sq]
    exact lin_bil Nout q q
  have m3 : ∫ p : (Fin Nout → ℝ) × (Fin Nin → ℝ),
      dotProduct p.1 (Matrix.mulVec M p.2) ^ 2 ∂(μ.prod ν) = ∑ k, ∑ l, M k l ^ 2 := by
    have hint : Integrable (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
        dotProduct p.1 (Matrix.mulVec M p.2) ^ 2) (μ.prod ν) :=
      mom_integrable _ (mom_pow _ hCb 2)
    rw [integral_prod_symm _ hint]
    have inner : ∀ w : Fin Nin → ℝ, ∫ z, dotProduct z (Matrix.mulVec M w) ^ 2 ∂μ
        = ∑ k, dotProduct (M k) w * dotProduct (M k) w := by
      intro w
      have e : ∀ z : Fin Nout → ℝ, dotProduct z (Matrix.mulVec M w) ^ 2
          = dotProduct (Matrix.mulVec M w) z * dotProduct (Matrix.mulVec M w) z := fun z => by
        rw [dotProduct_comm z, sq]
      simp only [e]
      have := lin_bil Nout (Matrix.mulVec M w) (Matrix.mulVec M w)
      refine this.trans ?_
      simp only [dotProduct, Matrix.mulVec]
    simp only [inner]
    rw [integral_finsetSum _ (fun k _ =>
      mom_integrable _ (mom_mul _ (mom_dot Nin (M k)) (mom_dot Nin (M k))))]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine (lin_bil Nin (M k) (M k)).trans ?_
    simp [dotProduct, sq]
  have m4 : ∫ p : (Fin Nout → ℝ) × (Fin Nin → ℝ),
      dotProduct r p.2 * dotProduct q p.1 * dotProduct p.1 (Matrix.mulVec M p.2) ∂(μ.prod ν)
      = dotProduct q (Matrix.mulVec M r) := by
    have hint : Integrable (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
        dotProduct r p.2 * dotProduct q p.1 * dotProduct p.1 (Matrix.mulVec M p.2)) (μ.prod ν) :=
      mom_integrable _ (mom_mul _ (mom_mul _ hA' hB') hCb)
    rw [integral_prod_symm _ hint]
    have inner : ∀ w : Fin Nin → ℝ,
        ∫ z, dotProduct r w * dotProduct q z * dotProduct z (Matrix.mulVec M w) ∂μ
          = dotProduct (Matrix.vecMul q M) w * dotProduct r w := by
      intro w
      have e : ∀ z : Fin Nout → ℝ, dotProduct r w * dotProduct q z
          * dotProduct z (Matrix.mulVec M w)
          = dotProduct r w * (dotProduct q z * dotProduct (Matrix.mulVec M w) z) := fun z => by
        rw [dotProduct_comm z, mul_assoc]
      simp only [e]
      rw [integral_const_mul]
      have := lin_bil Nout q (Matrix.mulVec M w)
      rw [this, Matrix.dotProduct_mulVec, mul_comm]
    simp only [inner]
    have e2 : ∀ w : Fin Nin → ℝ, dotProduct (Matrix.vecMul q M) w * dotProduct r w
        = dotProduct r w * dotProduct (Matrix.vecMul q M) w := fun w => mul_comm _ _
    simp only [e2]
    refine (lin_bil Nin r (Matrix.vecMul q M)).trans ?_
    rw [dotProduct_comm, Matrix.dotProduct_mulVec]
  have e4 : ∀ p : (Fin Nout → ℝ) × (Fin Nin → ℝ),
      54 * dotProduct r p.2 * dotProduct q p.1 * dotProduct p.1 (Matrix.mulVec M p.2)
        = 54 * (dotProduct r p.2 * dotProduct q p.1 * dotProduct p.1 (Matrix.mulVec M p.2)) :=
    fun p => by ring
  have j2 : Integrable (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      126 * D * dotProduct r p.2 ^ 2
        + 54 * dotProduct r p.2 * dotProduct q p.1 * dotProduct p.1 (Matrix.mulVec M p.2))
      (μ.prod ν) := i1.add i2
  have j3 : Integrable (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      126 * D * dotProduct r p.2 ^ 2
        + 54 * dotProduct r p.2 * dotProduct q p.1 * dotProduct p.1 (Matrix.mulVec M p.2)
        + 126 * D * dotProduct q p.1 ^ 2) (μ.prod ν) := j2.add i3
  have j4 : Integrable (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      126 * D * dotProduct r p.2 ^ 2
        + 54 * dotProduct r p.2 * dotProduct q p.1 * dotProduct p.1 (Matrix.mulVec M p.2)
        + 126 * D * dotProduct q p.1 ^ 2
        + 24 * D * dotProduct p.1 (Matrix.mulVec M p.2) ^ 2) (μ.prod ν) := j3.add i4
  rw [integral_add j4 i5, integral_add j3 i4, integral_add j2 i3, integral_add i1 i2]
  simp only [e4, integral_const_mul, integral_const, m1, m2, m3, m4, probReal_univ, smul_eq_mul,
    one_mul]

/-- **lem:app-sgd-moments**, part (iv), `Muon.SignSGD.lem_app_sgd_moments_iv` (third centered moment m_3).

cr-2026-10-23. The lemma has seven conjuncts (i)-(vii); the LaTeX statement of the whole lemma, verbatim:

\begin{lemma}[Moments of one coordinate]\label{lem:app-sgd-moments}
The coordinate \cref{eqn:app-sgd-coordinate} has mean $\EE X=\Delta_{ij}$, variance
\[
s^2\defeq\Var X=F^2+2\norm{\Delta_{i\cdot}}^2+2\norm{\Delta_{\cdot j}}^2+3\Delta_{ij}^2,\qquad F^2\le s^2\le8F^2,
\]
and third centered moment
\[
m_3\defeq\EE(X-\Delta_{ij})^3=24\Delta_{ij}\norm{\bar\Delta}_\F^2+126\Delta_{ij}\big(\norm r^2+\norm q^2\big)+200\Delta_{ij}^3+54\,q^\T\bar\Delta r,
\]
so that $\abs{m_3}\le200\abs{\Delta_{ij}}F^2+54F\norm r\norm q$. For every
integer $p\ge1$, $\EE\abs X^p\le((2p-1)!!)^2F^p$, and the standardized
coordinate $Y\defeq(X-\Delta_{ij})/s$ satisfies $\EE Y^4\le88208$.
\end{lemma} -/
theorem lem_app_sgd_moments_iv {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0)
    (i : Fin Nout) (j : Fin Nin) :
    ∫ p, (sgdCoord Δ i j p - Δ i j) ^ 3 ∂(gaussBatch Nout Nin)
      = 24 * Δ i j * frobNorm (sgdDeletedBlock Δ i j) ^ 2
        + 126 * Δ i j * (∑ l, sgdRow Δ i j l ^ 2 + ∑ k, sgdCol Δ i j k ^ 2)
        + 200 * Δ i j ^ 3
        + 54 * dotProduct (sgdCol Δ i j) (Matrix.mulVec (sgdDeletedBlock Δ i j) (sgdRow Δ i j)) := by
  have hrj : sgdRow Δ i j j = 0 := by simp [sgdRow]
  have hqi : sgdCol Δ i j i = 0 := by simp [sgdCol]
  have hrow : ∀ w : Fin Nin → ℝ, Matrix.mulVec (sgdDeletedBlock Δ i j) w i = 0 := by
    intro w
    simp [Matrix.mulVec, dotProduct, sgdDeletedBlock]
  have hcol : ∀ (w : Fin Nin → ℝ) (y : ℝ),
      Matrix.mulVec (sgdDeletedBlock Δ i j) (Function.update w j y)
        = Matrix.mulVec (sgdDeletedBlock Δ i j) w := by
    intro w y
    funext k
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = j
    · subst hl; simp [sgdDeletedBlock]
    · rw [Function.update_of_ne hl]
  have hmain := main_gen (Δ i j) i j (fun w => dotProduct (sgdRow Δ i j) w)
    (fun z => dotProduct (sgdCol Δ i j) z)
    (fun z w => dotProduct z (Matrix.mulVec (sgdDeletedBlock Δ i j) w))
    (mom_dot Nin _) (mom_dot Nout _)
    (fun w => by
      have e : (fun z : Fin Nout → ℝ => dotProduct z (Matrix.mulVec (sgdDeletedBlock Δ i j) w))
          = fun z => dotProduct (Matrix.mulVec (sgdDeletedBlock Δ i j) w) z :=
        funext fun z => dotProduct_comm _ _
      rw [e]
      exact mom_dot _ _)
    (fun z => by
      have e : (fun w : Fin Nin → ℝ => dotProduct z (Matrix.mulVec (sgdDeletedBlock Δ i j) w))
          = fun w => dotProduct (Matrix.vecMul z (sgdDeletedBlock Δ i j)) w :=
        funext fun w => Matrix.dotProduct_mulVec _ _ _
      rw [e]
      exact mom_dot _ _)
    (mom_Cb _)
    (fun w y => dot_update _ j hrj w y)
    (fun z x => dot_update _ i hqi z x)
    (fun z w x => by
      rw [dotProduct_comm _ (Matrix.mulVec (sgdDeletedBlock Δ i j) w),
        dotProduct_comm z, dot_update _ i (hrow w) z x])
    (fun z w y => by simp only [hcol])
  unfold gaussBatch
  have hpt : ∀ p : (Fin Nout → ℝ) × (Fin Nin → ℝ),
      (sgdCoord Δ i j p - Δ i j) ^ 3
        = (p.1 i * p.2 j * (Δ i j * p.1 i * p.2 j + p.1 i * dotProduct (sgdRow Δ i j) p.2
          + p.2 j * dotProduct (sgdCol Δ i j) p.1
          + dotProduct p.1 (Matrix.mulVec (sgdDeletedBlock Δ i j) p.2)) - Δ i j) ^ 3 := by
    intro p
    have h := sgd_decomp Δ i j p.1 p.2
    simp only [sgdCoord]
    rw [h]
    ring
  simp only [hpt]
  rw [hmain, q2_batch (sgdDeletedBlock Δ i j) (sgdRow Δ i j) (sgdCol Δ i j) (Δ i j)]
  have e1 : dotProduct (sgdRow Δ i j) (sgdRow Δ i j) = ∑ l, sgdRow Δ i j l ^ 2 := by
    simp [dotProduct, sq]
  have e2 : dotProduct (sgdCol Δ i j) (sgdCol Δ i j) = ∑ k, sgdCol Δ i j k ^ 2 := by
    simp [dotProduct, sq]
  rw [e1, e2, ← cm_frob_sq]
  ring

/-- **lem:app-sgd-moments**, part (v), `Muon.SignSGD.lem_app_sgd_moments_v` (bound on |m_3|).

cr-2026-10-23. The lemma has seven conjuncts (i)-(vii); the LaTeX statement of the whole lemma, verbatim:

\begin{lemma}[Moments of one coordinate]\label{lem:app-sgd-moments}
The coordinate \cref{eqn:app-sgd-coordinate} has mean $\EE X=\Delta_{ij}$, variance
\[
s^2\defeq\Var X=F^2+2\norm{\Delta_{i\cdot}}^2+2\norm{\Delta_{\cdot j}}^2+3\Delta_{ij}^2,\qquad F^2\le s^2\le8F^2,
\]
and third centered moment
\[
m_3\defeq\EE(X-\Delta_{ij})^3=24\Delta_{ij}\norm{\bar\Delta}_\F^2+126\Delta_{ij}\big(\norm r^2+\norm q^2\big)+200\Delta_{ij}^3+54\,q^\T\bar\Delta r,
\]
so that $\abs{m_3}\le200\abs{\Delta_{ij}}F^2+54F\norm r\norm q$. For every
integer $p\ge1$, $\EE\abs X^p\le((2p-1)!!)^2F^p$, and the standardized
coordinate $Y\defeq(X-\Delta_{ij})/s$ satisfies $\EE Y^4\le88208$.
\end{lemma} -/
theorem lem_app_sgd_moments_v {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0)
    (i : Fin Nout) (j : Fin Nin) :
    |∫ p, (sgdCoord Δ i j p - Δ i j) ^ 3 ∂(gaussBatch Nout Nin)|
      ≤ 200 * |Δ i j| * frobNorm Δ ^ 2
        + 54 * frobNorm Δ * Real.sqrt (∑ l, sgdRow Δ i j l ^ 2)
          * Real.sqrt (∑ k, sgdCol Δ i j k ^ 2) := by
  rw [lem_app_sgd_moments_iv Δ hΔ i j]
  have hsplit := cm_split_frob Δ i j
  have hcs := cm_bilin_cs Δ i j
  have hG0 : 0 ≤ frobNorm (sgdDeletedBlock Δ i j) := by
    unfold frobNorm; exact Real.sqrt_nonneg _
  have hF0 : 0 ≤ frobNorm Δ := by
    unfold frobNorm; exact Real.sqrt_nonneg _
  have hR0 : 0 ≤ ∑ l, sgdRow Δ i j l ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQ0 : 0 ≤ ∑ k, sgdCol Δ i j k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsR : Real.sqrt (∑ l, sgdRow Δ i j l ^ 2) ^ 2 = ∑ l, sgdRow Δ i j l ^ 2 :=
    Real.sq_sqrt hR0
  have hsQ : Real.sqrt (∑ k, sgdCol Δ i j k ^ 2) ^ 2 = ∑ k, sgdCol Δ i j k ^ 2 :=
    Real.sq_sqrt hQ0
  have hsRn : 0 ≤ Real.sqrt (∑ l, sgdRow Δ i j l ^ 2) := Real.sqrt_nonneg _
  have hsQn : 0 ≤ Real.sqrt (∑ k, sgdCol Δ i j k ^ 2) := Real.sqrt_nonneg _
  -- |qᵀ Δ̄ r| ≤ ‖Δ̄‖_F ‖q‖ ‖r‖
  have hcabs : |dotProduct (sgdCol Δ i j) (Matrix.mulVec (sgdDeletedBlock Δ i j) (sgdRow Δ i j))|
      ≤ frobNorm (sgdDeletedBlock Δ i j) * (Real.sqrt (∑ k, sgdCol Δ i j k ^ 2)
        * Real.sqrt (∑ l, sgdRow Δ i j l ^ 2)) := by
    have h2 : dotProduct (sgdCol Δ i j) (Matrix.mulVec (sgdDeletedBlock Δ i j) (sgdRow Δ i j)) ^ 2
        ≤ (frobNorm (sgdDeletedBlock Δ i j) * (Real.sqrt (∑ k, sgdCol Δ i j k ^ 2)
          * Real.sqrt (∑ l, sgdRow Δ i j l ^ 2))) ^ 2 := by
      rw [mul_pow, mul_pow, hsR, hsQ]
      exact hcs
    have hnn : 0 ≤ frobNorm (sgdDeletedBlock Δ i j) * (Real.sqrt (∑ k, sgdCol Δ i j k ^ 2)
        * Real.sqrt (∑ l, sgdRow Δ i j l ^ 2)) := by positivity
    nlinarith [sq_abs (dotProduct (sgdCol Δ i j) (Matrix.mulVec (sgdDeletedBlock Δ i j)
      (sgdRow Δ i j))), abs_nonneg (dotProduct (sgdCol Δ i j) (Matrix.mulVec
      (sgdDeletedBlock Δ i j) (sgdRow Δ i j)))]
  have hFle : frobNorm (sgdDeletedBlock Δ i j) ≤ frobNorm Δ := by
    nlinarith [sq_nonneg (Δ i j), sq_nonneg (frobNorm (sgdDeletedBlock Δ i j) - frobNorm Δ),
      hsplit, hR0, hQ0, hG0, hF0]
  have hP : 24 * frobNorm (sgdDeletedBlock Δ i j) ^ 2
      + 126 * ((∑ l, sgdRow Δ i j l ^ 2) + (∑ k, sgdCol Δ i j k ^ 2))
      + 200 * Δ i j ^ 2 ≤ 200 * frobNorm Δ ^ 2 := by
    nlinarith [sq_nonneg (frobNorm (sgdDeletedBlock Δ i j)), hsplit, hR0, hQ0]
  have hP0 : 0 ≤ 24 * frobNorm (sgdDeletedBlock Δ i j) ^ 2
      + 126 * ((∑ l, sgdRow Δ i j l ^ 2) + (∑ k, sgdCol Δ i j k ^ 2))
      + 200 * Δ i j ^ 2 := by
    nlinarith [sq_nonneg (frobNorm (sgdDeletedBlock Δ i j)), sq_nonneg (Δ i j)]
  have hmain : |24 * Δ i j * frobNorm (sgdDeletedBlock Δ i j) ^ 2
      + 126 * Δ i j * ((∑ l, sgdRow Δ i j l ^ 2) + (∑ k, sgdCol Δ i j k ^ 2))
      + 200 * Δ i j ^ 3| ≤ 200 * |Δ i j| * frobNorm Δ ^ 2 := by
    have e : 24 * Δ i j * frobNorm (sgdDeletedBlock Δ i j) ^ 2
        + 126 * Δ i j * ((∑ l, sgdRow Δ i j l ^ 2) + (∑ k, sgdCol Δ i j k ^ 2))
        + 200 * Δ i j ^ 3
        = Δ i j * (24 * frobNorm (sgdDeletedBlock Δ i j) ^ 2
          + 126 * ((∑ l, sgdRow Δ i j l ^ 2) + (∑ k, sgdCol Δ i j k ^ 2))
          + 200 * Δ i j ^ 2) := by ring
    rw [e, abs_mul, abs_of_nonneg hP0]
    have := mul_le_mul_of_nonneg_left hP (abs_nonneg (Δ i j))
    linarith
  have htri := abs_add_le (24 * Δ i j * frobNorm (sgdDeletedBlock Δ i j) ^ 2
      + 126 * Δ i j * ((∑ l, sgdRow Δ i j l ^ 2) + (∑ k, sgdCol Δ i j k ^ 2))
      + 200 * Δ i j ^ 3)
    (54 * dotProduct (sgdCol Δ i j) (Matrix.mulVec (sgdDeletedBlock Δ i j) (sgdRow Δ i j)))
  have hc54 : |54 * dotProduct (sgdCol Δ i j) (Matrix.mulVec (sgdDeletedBlock Δ i j)
      (sgdRow Δ i j))| ≤ 54 * frobNorm Δ * Real.sqrt (∑ l, sgdRow Δ i j l ^ 2)
          * Real.sqrt (∑ k, sgdCol Δ i j k ^ 2) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 54)]
    have h4 : frobNorm (sgdDeletedBlock Δ i j) * (Real.sqrt (∑ k, sgdCol Δ i j k ^ 2)
        * Real.sqrt (∑ l, sgdRow Δ i j l ^ 2)) ≤ frobNorm Δ * (Real.sqrt (∑ k, sgdCol Δ i j k ^ 2)
        * Real.sqrt (∑ l, sgdRow Δ i j l ^ 2)) :=
      mul_le_mul_of_nonneg_right hFle (by positivity)
    nlinarith [hcabs, h4]
  linarith [htri, hmain, hc54]

/-! ## Helpers for part (vi) (private, proved in this file) -/

private lemma vi_coord_int (n : ℕ) (i : Fin n) (k : ℕ) :
    Integrable (fun z : Fin n → ℝ => z i ^ k) (Muon.Foundations.stdGaussianPi n) := by
  have hm : MeasurePreserving (fun z : Fin n → ℝ => z i) (Muon.Foundations.stdGaussianPi n)
      (gaussianReal 0 1) := measurePreserving_eval _ i
  exact (hm.integrable_comp (g := fun x : ℝ => x ^ k) (by fun_prop)).2
    (Muon.Foundations.gaussian_integrable_pow k)

private lemma vi_coord_moment (n : ℕ) (i : Fin n) (p : ℕ) :
    ∫ z, z i ^ (2 * p) ∂(Muon.Foundations.stdGaussianPi n)
      = (((2 * p - 1).doubleFactorial : ℕ) : ℝ) := by
  have hm : Measurable (fun z : Fin n → ℝ => z i) := by fun_prop
  have e := integral_map (μ := Muon.Foundations.stdGaussianPi n) (φ := fun z : Fin n → ℝ => z i)
    hm.aemeasurable (f := fun x : ℝ => x ^ (2 * p))
    (by fun_prop : Measurable fun x : ℝ => x ^ (2 * p)).aestronglyMeasurable
  rw [Muon.Foundations.stdGaussianPi_map_coord, Muon.Foundations.gaussian_moment_even] at e
  exact e.symm

private lemma vi_lin_int {n : ℕ} (p : ℕ) (hp : 1 ≤ p) (u : Fin n → ℝ) :
    Integrable (fun z : Fin n → ℝ => dotProduct z u ^ (2 * p))
      (Muon.Foundations.stdGaussianPi n) := by
  by_contra h
  have h0 : ∫ z, dotProduct z u ^ (2 * p) ∂(Muon.Foundations.stdGaussianPi n)
      = (((2 * p - 1).doubleFactorial : ℕ) : ℝ) * (∑ k, u k ^ 2) ^ p :=
    sgd_gauss_linear_even_moment p u
  rw [integral_undef h] at h0
  have hd : (((2 * p - 1).doubleFactorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  have hS : ∑ k, u k ^ 2 = 0 := by
    rcases mul_eq_zero.1 h0.symm with h1 | h1
    · exact absurd h1 hd
    · exact (pow_eq_zero_iff (by omega : p ≠ 0)).1 h1
  have hu : ∀ k, u k = 0 := by
    intro k
    have h2 : u k ^ 2 ≤ ∑ k, u k ^ 2 :=
      Finset.single_le_sum (f := fun k => u k ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    have h3 : u k ^ 2 = 0 := by linarith [sq_nonneg (u k)]
    exact (pow_eq_zero_iff two_ne_zero).1 h3
  apply h
  have e : (fun z : Fin n → ℝ => dotProduct z u ^ (2 * p)) = fun _ => 0 := by
    funext z
    simp [dotProduct, hu, zero_pow (by omega : 2 * p ≠ 0)]
  rw [e]
  exact integrable_zero _ _ _

private lemma vi_inner (n m : ℕ) (p : ℕ) (Δ : Matrix (Fin n) (Fin m) ℝ) (w : Fin m → ℝ) :
    ∫ z, dotProduct z (Matrix.mulVec Δ w) ^ (2 * p) ∂(Muon.Foundations.stdGaussianPi n)
      = (((2 * p - 1).doubleFactorial : ℕ) : ℝ) * (∑ k, Matrix.mulVec Δ w k ^ 2) ^ p :=
  sgd_gauss_linear_even_moment p (Matrix.mulVec Δ w)

private lemma vi_sq_pow_int (m p : ℕ) (hp : 1 ≤ p) :
    Integrable (fun w : Fin m → ℝ => (∑ k, w k ^ 2) ^ p) (Muon.Foundations.stdGaussianPi m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [zero_pow (by omega : p ≠ 0)]
  · by_contra h
    have h0 := Muon.Foundations.stdGaussianPi_sq_norm_moment m p hp
    rw [integral_undef h] at h0
    have hpos : ∏ j ∈ Finset.range p, ((m : ℝ) + 2 * (j : ℝ)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j _
      have h1 : (0 : ℝ) < m := by exact_mod_cast hm
      have h2 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have h3 : (0 : ℝ) < (m : ℝ) + 2 * (j : ℝ) := by linarith
      exact h3.ne'
    exact hpos h0.symm

private lemma vi_frob_pos {n m : ℕ} {Δ : Matrix (Fin n) (Fin m) ℝ} (hΔ : Δ ≠ 0) :
    0 < frobNorm Δ := by
  obtain ⟨a, b, hab⟩ : ∃ a b, Δ a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΔ (Matrix.ext fun a b => by simpa using h a b)
  have hpos : 0 < ∑ a', ∑ b', Δ a' b' ^ 2 := by
    have h1 : 0 < Δ a b ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hab))
    calc (0 : ℝ) < Δ a b ^ 2 := h1
      _ ≤ ∑ b', Δ a b' ^ 2 :=
          Finset.single_le_sum (f := fun b' => Δ a b' ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ b)
      _ ≤ ∑ a', ∑ b', Δ a' b' ^ 2 :=
          Finset.single_le_sum (f := fun a' => ∑ b', Δ a' b' ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ a)
  unfold frobNorm
  exact Real.sqrt_pos.2 hpos

private lemma vi_quad_int {n m : ℕ} (p : ℕ) (hp : 1 ≤ p) (Δ : Matrix (Fin n) (Fin m) ℝ) :
    Integrable (fun w : Fin m → ℝ => (∑ k, Matrix.mulVec Δ w k ^ 2) ^ p)
      (Muon.Foundations.stdGaussianPi m) := by
  have hS := (vi_sq_pow_int m p hp).const_mul ((frobNorm Δ ^ 2) ^ p)
  have hcont : Continuous fun w : Fin m → ℝ => (∑ k, Matrix.mulVec Δ w k ^ 2) ^ p := by
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  refine Integrable.mono' hS hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  have hnn : 0 ≤ ∑ k, Matrix.mulVec Δ w k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.norm_of_nonneg (pow_nonneg hnn p)]
  have hCS : ∑ k, Matrix.mulVec Δ w k ^ 2 ≤ frobNorm Δ ^ 2 * ∑ l, w l ^ 2 := by
    rw [cm_frob_sq, Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    have e : Matrix.mulVec Δ w k = ∑ b, Δ k b * w b := rfl
    rw [e]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc (∑ k, Matrix.mulVec Δ w k ^ 2) ^ p ≤ (frobNorm Δ ^ 2 * ∑ l, w l ^ 2) ^ p :=
        pow_le_pow_left₀ hnn hCS p
    _ = (frobNorm Δ ^ 2) ^ p * (∑ l, w l ^ 2) ^ p := mul_pow _ _ _

private lemma vi_hf_int {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (p : ℕ)
    (hp : 1 ≤ p) :
    Integrable (fun q : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      dotProduct q.1 (Matrix.mulVec Δ q.2) ^ (2 * p))
      ((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin)) := by
  have hcont : Continuous fun q : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      dotProduct q.1 (Matrix.mulVec Δ q.2) ^ (2 * p) := by
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  rw [integrable_prod_iff' hcont.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun w => vi_lin_int p hp (Matrix.mulVec Δ w), ?_⟩
  have hn : ∀ x : ℝ, ‖x ^ (2 * p)‖ = x ^ (2 * p) := fun x => by
    rw [pow_mul]
    exact Real.norm_of_nonneg (by positivity)
  have e : (fun w : Fin Nin → ℝ => ∫ z, ‖dotProduct z (Matrix.mulVec Δ w) ^ (2 * p)‖
      ∂(Muon.Foundations.stdGaussianPi Nout))
      = fun w => (((2 * p - 1).doubleFactorial : ℕ) : ℝ) *
          (∑ k, Matrix.mulVec Δ w k ^ 2) ^ p := by
    funext w
    simp only [hn]
    exact vi_inner _ _ p Δ w
  rw [e]
  exact (vi_quad_int p hp Δ).const_mul _

private lemma vi_hd_val {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (p : ℕ)
    (hp : 1 ≤ p) :
    ∫ q : (Fin Nout → ℝ) × (Fin Nin → ℝ), dotProduct q.1 (Matrix.mulVec Δ q.2) ^ (2 * p)
      ∂((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin))
      ≤ (((2 * p - 1).doubleFactorial : ℕ) : ℝ) *
          ((((2 * p - 1).doubleFactorial : ℕ) : ℝ) * frobNorm Δ ^ (2 * p)) := by
  rw [integral_prod_symm _ (vi_hf_int Δ p hp)]
  simp only [vi_inner]
  rw [integral_const_mul]
  have hq := sgd_quadform_moment_le p hp Δ
  exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)

/-- **lem:app-sgd-moments**, part (vi), `Muon.SignSGD.lem_app_sgd_moments_vi` (absolute moments E|X|^p, all integers p >= 1).

cr-2026-10-23. The lemma has seven conjuncts (i)-(vii); the LaTeX statement of the whole lemma, verbatim:

\begin{lemma}[Moments of one coordinate]\label{lem:app-sgd-moments}
The coordinate \cref{eqn:app-sgd-coordinate} has mean $\EE X=\Delta_{ij}$, variance
\[
s^2\defeq\Var X=F^2+2\norm{\Delta_{i\cdot}}^2+2\norm{\Delta_{\cdot j}}^2+3\Delta_{ij}^2,\qquad F^2\le s^2\le8F^2,
\]
and third centered moment
\[
m_3\defeq\EE(X-\Delta_{ij})^3=24\Delta_{ij}\norm{\bar\Delta}_\F^2+126\Delta_{ij}\big(\norm r^2+\norm q^2\big)+200\Delta_{ij}^3+54\,q^\T\bar\Delta r,
\]
so that $\abs{m_3}\le200\abs{\Delta_{ij}}F^2+54F\norm r\norm q$. For every
integer $p\ge1$, $\EE\abs X^p\le((2p-1)!!)^2F^p$, and the standardized
coordinate $Y\defeq(X-\Delta_{ij})/s$ satisfies $\EE Y^4\le88208$.
\end{lemma} -/
theorem lem_app_sgd_moments_vi {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0)
    (i : Fin Nout) (j : Fin Nin) :
    ∀ p : ℕ, 1 ≤ p →
      ∫ x, |sgdCoord Δ i j x| ^ p ∂(gaussBatch Nout Nin)
        ≤ (((2 * p - 1).doubleFactorial : ℕ) : ℝ) ^ 2 * frobNorm Δ ^ p := by
  intro p hp
  have hF : 0 < frobNorm Δ := vi_frob_pos hΔ
  have hμ : (0 : ℝ) < frobNorm Δ ^ p := pow_pos hF p
  have hμne : frobNorm Δ ^ p ≠ 0 := hμ.ne'
  rw [show gaussBatch Nout Nin = (Muon.Foundations.stdGaussianPi Nout).prod
      (Muon.Foundations.stdGaussianPi Nin) from rfl]
  have hcont : Continuous fun q : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      dotProduct q.1 (Matrix.mulVec Δ q.2) ^ (2 * p) := by
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hf_int := vi_hf_int Δ p hp
  have hc_int : Integrable (fun q : (Fin Nout → ℝ) × (Fin Nin → ℝ) => (q.1 i * q.2 j) ^ (2 * p))
      ((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin)) := by
    have h := Integrable.mul_prod (vi_coord_int Nout i (2 * p)) (vi_coord_int Nin j (2 * p))
    simpa only [mul_pow] using h
  have hc_val : ∫ q : (Fin Nout → ℝ) × (Fin Nin → ℝ), (q.1 i * q.2 j) ^ (2 * p)
      ∂((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin))
      = (((2 * p - 1).doubleFactorial : ℕ) : ℝ) * (((2 * p - 1).doubleFactorial : ℕ) : ℝ) := by
    have h := integral_prod_mul (μ := Muon.Foundations.stdGaussianPi Nout)
      (ν := Muon.Foundations.stdGaussianPi Nin) (fun x : Fin Nout → ℝ => x i ^ (2 * p))
      (fun y : Fin Nin → ℝ => y j ^ (2 * p))
    simp only [mul_pow, vi_coord_moment] at h ⊢
    exact h
  have hpt : ∀ q : (Fin Nout → ℝ) × (Fin Nin → ℝ),
      |sgdCoord Δ i j q| ^ p ≤ ((frobNorm Δ ^ p)⁻¹ * dotProduct q.1 (Matrix.mulVec Δ q.2) ^ (2 * p)
        + frobNorm Δ ^ p * (q.1 i * q.2 j) ^ (2 * p)) / 2 := by
    intro q
    have hX : sgdCoord Δ i j q = dotProduct q.1 (Matrix.mulVec Δ q.2) * (q.1 i * q.2 j) := by
      unfold sgdCoord
      ring
    have e : |sgdCoord Δ i j q| ^ p
        = |dotProduct q.1 (Matrix.mulVec Δ q.2)| ^ p * |q.1 i * q.2 j| ^ p := by
      rw [hX, abs_mul, mul_pow]
    have sq_pow : ∀ x : ℝ, (|x| ^ p) ^ 2 = x ^ (2 * p) := fun x => by
      rw [← pow_mul, mul_comm p 2, pow_mul, sq_abs, ← pow_mul]
    have amgm : ∀ a b μ : ℝ, 0 < μ → a * b ≤ (μ⁻¹ * a ^ 2 + μ * b ^ 2) / 2 := by
      intro a b μ hμ0
      have hμ1 : μ ≠ 0 := hμ0.ne'
      have h1 : 0 ≤ μ⁻¹ * (a - μ * b) ^ 2 := mul_nonneg (inv_nonneg.2 hμ0.le) (sq_nonneg _)
      have h2 : μ⁻¹ * (a - μ * b) ^ 2 = μ⁻¹ * a ^ 2 + μ * b ^ 2 - 2 * (a * b) := by
        field_simp
        ring
      linarith
    rw [e]
    have := amgm (|dotProduct q.1 (Matrix.mulVec Δ q.2)| ^ p) (|q.1 i * q.2 j| ^ p)
      (frobNorm Δ ^ p) hμ
    rw [sq_pow, sq_pow] at this
    exact this
  have hg_int : Integrable (fun q : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      ((frobNorm Δ ^ p)⁻¹ * dotProduct q.1 (Matrix.mulVec Δ q.2) ^ (2 * p)
        + frobNorm Δ ^ p * (q.1 i * q.2 j) ^ (2 * p)) / 2)
      ((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin)) :=
    ((hf_int.const_mul _).add (hc_int.const_mul _)).div_const 2
  have hd_val := vi_hd_val Δ p hp
  have hfin := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun q => by positivity) hg_int (Filter.Eventually.of_forall hpt)
  have hsplit : ∫ q : (Fin Nout → ℝ) × (Fin Nin → ℝ),
      ((frobNorm Δ ^ p)⁻¹ * dotProduct q.1 (Matrix.mulVec Δ q.2) ^ (2 * p)
        + frobNorm Δ ^ p * (q.1 i * q.2 j) ^ (2 * p)) / 2
      ∂((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin))
      = ((frobNorm Δ ^ p)⁻¹ * ∫ q : (Fin Nout → ℝ) × (Fin Nin → ℝ),
            dotProduct q.1 (Matrix.mulVec Δ q.2) ^ (2 * p)
            ∂((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin))
          + frobNorm Δ ^ p * ∫ q : (Fin Nout → ℝ) × (Fin Nin → ℝ), (q.1 i * q.2 j) ^ (2 * p)
            ∂((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin)))
          / 2 := by
    rw [integral_div, integral_add (hf_int.const_mul _) (hc_int.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [hsplit, hc_val] at hfin
  have hinv := mul_le_mul_of_nonneg_left hd_val (inv_nonneg.2 hμ.le)
  have key : ((frobNorm Δ ^ p)⁻¹ * ((((2 * p - 1).doubleFactorial : ℕ) : ℝ) *
      ((((2 * p - 1).doubleFactorial : ℕ) : ℝ) * frobNorm Δ ^ (2 * p)))
      + frobNorm Δ ^ p * ((((2 * p - 1).doubleFactorial : ℕ) : ℝ) *
      (((2 * p - 1).doubleFactorial : ℕ) : ℝ))) / 2
      = (((2 * p - 1).doubleFactorial : ℕ) : ℝ) ^ 2 * frobNorm Δ ^ p := by
    rw [pow_mul' (frobNorm Δ) 2 p]
    field_simp
    ring
  linarith

private lemma vii_pow4_add (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  have h1 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have h2 : ((a + b) ^ 2) ^ 2 ≤ (2 * (a ^ 2 + b ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), h2]

private lemma vii_pow4_sub (a b : ℝ) : (a - b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  have h1 : (a - b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a + b)]
  have h2 : ((a - b) ^ 2) ^ 2 ≤ (2 * (a ^ 2 + b ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), h2]

private lemma vii_entry_le {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) : Δ i j ^ 2 ≤ frobNorm Δ ^ 2 := by
  rw [cm_frob_sq]
  have h1 : Δ i j ^ 2 ≤ ∑ b, Δ i b ^ 2 :=
    Finset.single_le_sum (f := fun b => Δ i b ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ b, Δ i b ^ 2 ≤ ∑ a, ∑ b, Δ a b ^ 2 :=
    Finset.single_le_sum (f := fun a => ∑ b, Δ a b ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

/-- **lem:app-sgd-moments**, part (vii), `Muon.SignSGD.lem_app_sgd_moments_vii` (fourth moment of the standardized coordinate Y).

cr-2026-10-23. The lemma has seven conjuncts (i)-(vii); the LaTeX statement of the whole lemma, verbatim:

\begin{lemma}[Moments of one coordinate]\label{lem:app-sgd-moments}
The coordinate \cref{eqn:app-sgd-coordinate} has mean $\EE X=\Delta_{ij}$, variance
\[
s^2\defeq\Var X=F^2+2\norm{\Delta_{i\cdot}}^2+2\norm{\Delta_{\cdot j}}^2+3\Delta_{ij}^2,\qquad F^2\le s^2\le8F^2,
\]
and third centered moment
\[
m_3\defeq\EE(X-\Delta_{ij})^3=24\Delta_{ij}\norm{\bar\Delta}_\F^2+126\Delta_{ij}\big(\norm r^2+\norm q^2\big)+200\Delta_{ij}^3+54\,q^\T\bar\Delta r,
\]
so that $\abs{m_3}\le200\abs{\Delta_{ij}}F^2+54F\norm r\norm q$. For every
integer $p\ge1$, $\EE\abs X^p\le((2p-1)!!)^2F^p$, and the standardized
coordinate $Y\defeq(X-\Delta_{ij})/s$ satisfies $\EE Y^4\le88208$.
\end{lemma} -/
theorem lem_app_sgd_moments_vii {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0)
    (i : Fin Nout) (j : Fin Nin) :
    ∫ x, sgdStdCoord Δ i j x ^ 4 ∂(gaussBatch Nout Nin) ≤ 88208 := by
  haveI : IsProbabilityMeasure (gaussBatch Nout Nin) := by
    unfold gaussBatch
    infer_instance
  have hF : 0 < frobNorm Δ := vi_frob_pos hΔ
  have hvar := lem_app_sgd_moments_iii Δ hΔ i j
  have hs : frobNorm Δ ≤ sgdSd Δ i j := by
    unfold sgdSd
    calc frobNorm Δ = Real.sqrt (frobNorm Δ ^ 2) := (Real.sqrt_sq hF.le).symm
      _ ≤ Real.sqrt (variance (sgdCoord Δ i j) (gaussBatch Nout Nin)) :=
          Real.sqrt_le_sqrt hvar.1
  have hs0 : 0 < sgdSd Δ i j := lt_of_lt_of_le hF hs
  have hΔ4 : Δ i j ^ 4 ≤ frobNorm Δ ^ 4 := by
    have h0 : 0 ≤ Δ i j ^ 2 := sq_nonneg _
    calc Δ i j ^ 4 = (Δ i j ^ 2) ^ 2 := by ring
      _ ≤ (frobNorm Δ ^ 2) ^ 2 := pow_le_pow_left₀ h0 (vii_entry_le Δ i j) 2
      _ = frobNorm Δ ^ 4 := by ring
  -- fourth moment of X
  have hdf : (((2 * 4 - 1).doubleFactorial : ℕ) : ℝ) = 105 := by
    norm_num [Nat.doubleFactorial]
  have hX4 : ∫ x, sgdCoord Δ i j x ^ 4 ∂(gaussBatch Nout Nin) ≤ 11025 * frobNorm Δ ^ 4 := by
    have h := lem_app_sgd_moments_vi Δ hΔ i j 4 (by norm_num)
    have he : ∀ x, |sgdCoord Δ i j x| ^ 4 = sgdCoord Δ i j x ^ 4 :=
      fun x => Even.pow_abs ⟨2, rfl⟩ _
    simp only [he, hdf] at h
    linarith
  -- pointwise identities
  have hX : ∀ x, sgdCoord Δ i j x = sgdSd Δ i j * sgdStdCoord Δ i j x + Δ i j := by
    intro x
    unfold sgdStdCoord
    field_simp
    ring
  have hY4 : ∀ x, sgdStdCoord Δ i j x ^ 4
      = (sgdCoord Δ i j x - Δ i j) ^ 4 / sgdSd Δ i j ^ 4 := by
    intro x
    unfold sgdStdCoord
    rw [div_pow]
  by_cases hY : Integrable (fun x => sgdStdCoord Δ i j x ^ 4) (gaussBatch Nout Nin)
  swap
  · rw [integral_undef hY]
    norm_num
  have hcont : Continuous fun q : (Fin Nout → ℝ) × (Fin Nin → ℝ) => sgdCoord Δ i j q := by
    simp only [sgdCoord, Matrix.mulVec, dotProduct]
    fun_prop
  have hXi : Integrable (fun x => sgdCoord Δ i j x ^ 4) (gaussBatch Nout Nin) := by
    refine Integrable.mono' ((hY.const_mul (8 * sgdSd Δ i j ^ 4)).add
      (integrable_const (8 * Δ i j ^ 4))) (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity), hX x]
    calc (sgdSd Δ i j * sgdStdCoord Δ i j x + Δ i j) ^ 4
        ≤ 8 * ((sgdSd Δ i j * sgdStdCoord Δ i j x) ^ 4 + Δ i j ^ 4) := vii_pow4_add _ _
      _ = 8 * sgdSd Δ i j ^ 4 * sgdStdCoord Δ i j x ^ 4 + 8 * Δ i j ^ 4 := by ring
  have hYbd : ∀ x, sgdStdCoord Δ i j x ^ 4
      ≤ 8 / sgdSd Δ i j ^ 4 * (sgdCoord Δ i j x ^ 4 + Δ i j ^ 4) := by
    intro x
    calc sgdStdCoord Δ i j x ^ 4 = (sgdCoord Δ i j x - Δ i j) ^ 4 / sgdSd Δ i j ^ 4 := hY4 x
      _ ≤ 8 * (sgdCoord Δ i j x ^ 4 + Δ i j ^ 4) / sgdSd Δ i j ^ 4 := by
          gcongr
          exact vii_pow4_sub _ _
      _ = 8 / sgdSd Δ i j ^ 4 * (sgdCoord Δ i j x ^ 4 + Δ i j ^ 4) := by ring
  have hRint : Integrable (fun x => 8 / sgdSd Δ i j ^ 4 * (sgdCoord Δ i j x ^ 4 + Δ i j ^ 4))
      (gaussBatch Nout Nin) := (hXi.add (integrable_const _)).const_mul _
  have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
    hRint (Filter.Eventually.of_forall hYbd)
  rw [integral_const_mul, integral_add hXi (integrable_const _), integral_const] at hmono
  have hq : frobNorm Δ ^ 4 / sgdSd Δ i j ^ 4 ≤ 1 :=
    (div_le_one (by positivity)).2 (pow_le_pow_left₀ hF.le hs 4)
  have hc : (0 : ℝ) ≤ 8 / sgdSd Δ i j ^ 4 := by positivity
  have hbound : 8 / sgdSd Δ i j ^ 4 *
      (∫ x, sgdCoord Δ i j x ^ 4 ∂(gaussBatch Nout Nin) + Δ i j ^ 4)
      ≤ 8 / sgdSd Δ i j ^ 4 * (11026 * frobNorm Δ ^ 4) :=
    mul_le_mul_of_nonneg_left (by linarith) hc
  have key : 8 / sgdSd Δ i j ^ 4 * (11026 * frobNorm Δ ^ 4)
      = 88208 * (frobNorm Δ ^ 4 / sgdSd Δ i j ^ 4) := by
    ring
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
  linarith

/-! ## Lemma `lem:app-sgd-decay` -/

/-- Private helper (second conjunct of `lem:app-sgd-decay`): `ψ(|t|/8) ≤ min{1, C_ch|t|^{-1/2}}`
from `ψ < 1` and the `x^{-1/2}` bound of `sgd_psi_le_rpow`. -/
private lemma cm_decay_tail {t : ℝ} (ht : t ≠ 0) :
    sgdPsi (|t| / 8) ≤ min 1 (sgdCch * |t| ^ (-(1 / 2 : ℝ))) := by
  have hpos : 0 < |t| / 8 := by
    have := abs_pos.mpr ht
    positivity
  have h1 : sgdPsi (|t| / 8) ≤ 1 := (sgd_psi_lt_one hpos).le
  have h2 := sgd_psi_le_rpow hpos
  have h8 : (8 : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt 8)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (by norm_num)]
  have key : (|t| / 8) ^ (-(1 / 2 : ℝ)) = Real.sqrt 8 * |t| ^ (-(1 / 2 : ℝ)) := by
    rw [Real.div_rpow (abs_nonneg t) (by norm_num), h8, div_inv_eq_mul]
    ring
  have hC : sgdCch * |t| ^ (-(1 / 2 : ℝ))
      = (Real.sqrt 8 * |t| ^ (-(1 / 2 : ℝ)))
        * (∫ g, |g| ^ (-(1 / 2 : ℝ)) ∂(gaussianReal 0 1)) ^ 2 := by
    unfold sgdCch
    ring
  rw [key] at h2
  refine le_min h1 ?_
  rw [hC]
  exact h2

/-- Private helper (reduction of `lem:app-sgd-decay`): from the characteristic-function bound
`hcore` for the unstandardized coordinate `X` at frequency `u`, and the Frobenius comparison
`s ≤ 4 ‖Δ‖_F ≤ 8 ‖Δ̄‖_F`, the standardized characteristic function is bounded by `ψ(|t|/8)`. -/
private lemma cm_decay_reduce {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0)
    (i : Fin Nout) (j : Fin Nin)
    (hbar : frobNorm Δ / 2 ≤ frobNorm (sgdDeletedBlock Δ i j))
    (hcore : ∀ u : ℝ, ‖∫ p, Complex.exp ((u : ℂ) * Complex.I * ((sgdCoord Δ i j p : ℝ) : ℂ))
        ∂(gaussBatch Nout Nin)‖ ≤ sgdPsi (|u| * frobNorm (sgdDeletedBlock Δ i j)))
    (t : ℝ) :
    ‖sgdCharFunY Δ i j t‖ ≤ sgdPsi (|t| / 8) := by
  have hF : 0 < frobNorm Δ := vi_frob_pos hΔ
  have hv := lem_app_sgd_moments_iii Δ hΔ i j
  have hFb : 0 ≤ frobNorm (sgdDeletedBlock Δ i j) := by linarith
  have hvar_pos : 0 < variance (sgdCoord Δ i j) (gaussBatch Nout Nin) := by
    have := pow_pos hF 2
    linarith [hv.1]
  have hs : 0 < sgdSd Δ i j := Real.sqrt_pos.mpr hvar_pos
  have hs4 : sgdSd Δ i j ≤ 4 * frobNorm Δ := by
    unfold sgdSd
    calc Real.sqrt (variance (sgdCoord Δ i j) (gaussBatch Nout Nin))
        ≤ Real.sqrt ((4 * frobNorm Δ) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [hv.2, sq_nonneg (frobNorm Δ)])
      _ = 4 * frobNorm Δ := Real.sqrt_sq (by linarith)
  have hbar8 : sgdSd Δ i j ≤ 8 * frobNorm (sgdDeletedBlock Δ i j) := by linarith
  have hfac : sgdCharFunY Δ i j t
      = Complex.exp (((-(t / sgdSd Δ i j * Δ i j) : ℝ) : ℂ) * Complex.I)
        * ∫ p, Complex.exp (((t / sgdSd Δ i j : ℝ) : ℂ) * Complex.I
            * ((sgdCoord Δ i j p : ℝ) : ℂ)) ∂(gaussBatch Nout Nin) := by
    unfold sgdCharFunY
    rw [← integral_const_mul]
    congr 1
    funext p
    rw [← Complex.exp_add]
    congr 1
    unfold sgdStdCoord
    have hsC : (sgdSd Δ i j : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
    ring
  have hc := hcore (t / sgdSd Δ i j)
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine hc.trans ?_
  have harg : |t| / 8 ≤ |t / sgdSd Δ i j| * frobNorm (sgdDeletedBlock Δ i j) := by
    rw [abs_div, abs_of_pos hs, div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) hs]
    nlinarith [mul_le_mul_of_nonneg_left hbar8 (abs_nonneg t)]
  have ha : |t| / 8 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by positivity)
  have hb : |t / sgdSd Δ i j| * frobNorm (sgdDeletedBlock Δ i j) ∈ Set.Ici (0 : ℝ) :=
    Set.mem_Ici.mpr (mul_nonneg (abs_nonneg _) hFb)
  exact sgd_psi_antitoneOn ha hb harg

/-! ## Private helpers for `lem:app-sgd-decay` (core characteristic-function bound) -/

private lemma slice_pi_c (n : ℕ) (i : Fin n) (f : (Fin n → ℝ) → ℂ)
    (hf : Integrable f (Muon.Foundations.stdGaussianPi n)) :
    ∫ z, f z ∂(Muon.Foundations.stdGaussianPi n)
      = ∫ z, ∫ x, f (Function.update z i x) ∂(gaussianReal 0 1)
          ∂(Muon.Foundations.stdGaussianPi n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal (0 : ℝ) 1) i
  have hg : ∀ F : (Fin (m + 1) → ℝ) → ℂ, ∫ z, F z ∂(Muon.Foundations.stdGaussianPi (m + 1))
      = ∫ p, F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm p)
          ∂((gaussianReal 0 1).prod (Muon.Foundations.stdGaussianPi m)) := by
    intro F
    have := hmp.integral_comp' (g := fun p => F ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (m + 1) => ℝ) i).symm p))
    simp only [MeasurableEquiv.symm_apply_apply] at this
    exact this
  have hint' : Integrable (fun p => f ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (m + 1) => ℝ) i).symm p))
      ((gaussianReal 0 1).prod (Muon.Foundations.stdGaussianPi m)) :=
    (MeasurePreserving.symm _ hmp).integrable_comp_of_integrable hf
  have hL : ∫ z, f z ∂(Muon.Foundations.stdGaussianPi (m + 1))
      = ∫ y, ∫ x, f (i.insertNth x y) ∂(gaussianReal 0 1) ∂(Muon.Foundations.stdGaussianPi m) := by
    rw [hg, integral_prod_symm _ hint']
    rfl
  rw [hL, hg (fun z => ∫ x, f (Function.update z i x) ∂(gaussianReal 0 1))]
  have e : ∀ p : ℝ × (Fin m → ℝ),
      ∫ x, f (Function.update ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm p)
        i x) ∂(gaussianReal 0 1) = ∫ x, f (i.insertNth x p.2) ∂(gaussianReal 0 1) := by
    intro p
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.update_insertNth]
  simp only [e]
  refine Eq.trans ?_ (integral_fun_snd (μ := gaussianReal 0 1)
    (ν := Muon.Foundations.stdGaussianPi m)
    (fun y => ∫ x, f (i.insertNth x y) ∂(gaussianReal 0 1))).symm
  simp

private lemma sgd_row_j {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) : sgdRow Δ i j j = 0 := by simp [sgdRow]

private lemma sgd_col_i {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) : sgdCol Δ i j i = 0 := by simp [sgdCol]

private lemma sgd_Db_row {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) (w : Fin Nin → ℝ) : Matrix.mulVec (sgdDeletedBlock Δ i j) w i = 0 := by
  simp [Matrix.mulVec, dotProduct, sgdDeletedBlock]

private lemma sgd_Db_col {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) (w : Fin Nin → ℝ) (y : ℝ) :
    Matrix.mulVec (sgdDeletedBlock Δ i j) (Function.update w j y)
      = Matrix.mulVec (sgdDeletedBlock Δ i j) w := by
  funext k
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l = j
  · subst hl; simp [sgdDeletedBlock]
  · rw [Function.update_of_ne hl]

private lemma sgd_coord_update {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) (z : Fin Nout → ℝ) (w : Fin Nin → ℝ) (ξ ζ : ℝ) :
    sgdCoord Δ i j (Function.update z i ξ, Function.update w j ζ)
      = ξ * ζ * (Δ i j * ξ * ζ + ξ * dotProduct (sgdRow Δ i j) w
        + ζ * dotProduct (sgdCol Δ i j) z
        + dotProduct z (Matrix.mulVec (sgdDeletedBlock Δ i j) w)) := by
  have h := sgd_decomp Δ i j (Function.update z i ξ) (Function.update w j ζ)
  have e1 : dotProduct (Function.update z i ξ) (Matrix.mulVec (sgdDeletedBlock Δ i j) w)
      = dotProduct z (Matrix.mulVec (sgdDeletedBlock Δ i j) w) := by
    rw [dotProduct_comm _ (Matrix.mulVec (sgdDeletedBlock Δ i j) w), dotProduct_comm z,
      dot_update _ i (sgd_Db_row Δ i j w) z ξ]
  simp only [sgdCoord]
  rw [h, sgd_Db_col, e1, dot_update _ j (sgd_row_j Δ i j) w ζ,
    dot_update _ i (sgd_col_i Δ i j) z ξ]
  simp only [Function.update_self]
  ring

private lemma decay_lvl1 {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) (u ξ ζ : ℝ) (w : Fin Nin → ℝ) :
    ‖∫ z, Complex.exp ((u : ℂ) * Complex.I
        * ((sgdCoord Δ i j (Function.update z i ξ, Function.update w j ζ) : ℝ) : ℂ))
        ∂(Muon.Foundations.stdGaussianPi Nout)‖
      = Real.exp (-((u * ξ * ζ) ^ 2 * ∑ k, (Matrix.mulVec (sgdDeletedBlock Δ i j) w k
          + ζ * sgdCol Δ i j k) ^ 2) / 2) := by
  have h := sgd_gauss_charfun_linear (n := Nout)
    (fun k => Matrix.mulVec (sgdDeletedBlock Δ i j) w k + ζ * sgdCol Δ i j k)
    (Δ i j * ξ * ζ + ξ * dotProduct (sgdRow Δ i j) w) (u * ξ * ζ)
  have e : ∀ z : Fin Nout → ℝ,
      Complex.exp ((u : ℂ) * Complex.I
        * ((sgdCoord Δ i j (Function.update z i ξ, Function.update w j ζ) : ℝ) : ℂ))
      = Complex.exp (((u * ξ * ζ : ℝ) : ℂ) * Complex.I
        * (((Δ i j * ξ * ζ + ξ * dotProduct (sgdRow Δ i j) w)
          + ∑ k, z k * (Matrix.mulVec (sgdDeletedBlock Δ i j) w k
            + ζ * sgdCol Δ i j k) : ℝ) : ℂ)) := by
    intro z
    congr 1
    have hq : dotProduct (sgdCol Δ i j) z = ∑ k, z k * sgdCol Δ i j k := by
      simp only [dotProduct]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hC : dotProduct z (Matrix.mulVec (sgdDeletedBlock Δ i j) w)
        = ∑ k, z k * Matrix.mulVec (sgdDeletedBlock Δ i j) w k := rfl
    have hs : ∑ k, z k * (Matrix.mulVec (sgdDeletedBlock Δ i j) w k + ζ * sgdCol Δ i j k)
        = dotProduct z (Matrix.mulVec (sgdDeletedBlock Δ i j) w)
          + ζ * dotProduct (sgdCol Δ i j) z := by
      rw [hq, hC, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [sgd_coord_update, hs]
    push_cast
    ring
  simp only [e]
  refine h.trans ?_
  congr 1

private lemma sgd_coord_cont {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) : Continuous (sgdCoord Δ i j) := by
  unfold sgdCoord
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

private lemma decay_bdd {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℂ} (hc : Continuous f)
    (hb : ∀ x, ‖f x‖ ≤ 1) : Integrable f μ :=
  Integrable.of_bound hc.aestronglyMeasurable 1 (Filter.Eventually.of_forall hb)

private lemma decay_bdd_real {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hc : Continuous f)
    (hb : ∀ x, ‖f x‖ ≤ 1) : Integrable f μ :=
  Integrable.of_bound hc.aestronglyMeasurable 1 (Filter.Eventually.of_forall hb)

private lemma decay_norm_exp (u x : ℝ) :
    ‖Complex.exp ((u : ℂ) * Complex.I * ((x : ℝ) : ℂ))‖ = 1 := by
  have : (u : ℂ) * Complex.I * ((x : ℝ) : ℂ) = ((u * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

private lemma decay_core {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout)
    (j : Fin Nin) (u : ℝ) :
    ‖∫ p, Complex.exp ((u : ℂ) * Complex.I * ((sgdCoord Δ i j p : ℝ) : ℂ))
        ∂(gaussBatch Nout Nin)‖ ≤ sgdPsi (|u| * frobNorm (sgdDeletedBlock Δ i j)) := by
  set μ := Muon.Foundations.stdGaussianPi Nout with hμ
  set ν := Muon.Foundations.stdGaussianPi Nin with hν
  set γ : Measure ℝ := gaussianReal 0 1 with hγ
  set Db := sgdDeletedBlock Δ i j with hDb
  set q := sgdCol Δ i j with hq
  -- the integrand and its bounded continuity
  set Fc : (Fin Nout → ℝ) × (Fin Nin → ℝ) → ℂ := fun p =>
    Complex.exp ((u : ℂ) * Complex.I * ((sgdCoord Δ i j p : ℝ) : ℂ)) with hFc
  have hFcc : Continuous Fc := by
    have := sgd_coord_cont Δ i j
    rw [hFc]
    fun_prop
  have hFcb : ∀ p, ‖Fc p‖ ≤ 1 := fun p => (decay_norm_exp u _).le
  have hFi : Integrable Fc (μ.prod ν) := decay_bdd _ hFcc hFcb
  -- exponent function
  set S : (Fin Nin → ℝ) → ℝ → ℝ := fun w ζ =>
    ∑ k, (Matrix.mulVec Db w k + ζ * q k) ^ 2 with hS
  set E : ℝ → ℝ → (Fin Nin → ℝ) → ℝ := fun ξ ζ w =>
    Real.exp (-((u * ξ * ζ) ^ 2 * S w ζ) / 2) with hE
  have hEc : Continuous (fun x : ℝ × ℝ × (Fin Nin → ℝ) => E x.1 x.2.1 x.2.2) := by
    simp only [hE, hS]
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hEb : ∀ ξ ζ w, ‖E ξ ζ w‖ ≤ 1 := by
    intro ξ ζ w
    simp only [hE, Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ (u * ξ * ζ) ^ 2 * S w ζ :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun k _ => sq_nonneg _)
    linarith
  -- level 2: integrate out `ξ` (after slicing `z`)
  have lvl2 : ∀ (w : Fin Nin → ℝ) (ζ : ℝ),
      ‖∫ z, Fc (z, Function.update w j ζ) ∂μ‖ ≤ ∫ ξ, E ξ ζ w ∂γ := by
    intro w ζ
    have hint : Integrable (fun z => Fc (z, Function.update w j ζ)) μ :=
      decay_bdd μ (hFcc.comp (by fun_prop)) (fun z => hFcb _)
    rw [slice_pi_c Nout i _ hint]
    have hupd : Continuous (fun x : (Fin Nout → ℝ) × ℝ => Function.update x.1 i x.2) := by
      fun_prop
    have hjoint : Integrable (Function.uncurry fun (z : Fin Nout → ℝ) (ξ : ℝ) =>
        Fc (Function.update z i ξ, Function.update w j ζ)) (μ.prod γ) :=
      decay_bdd _ (hFcc.comp (hupd.prodMk continuous_const)) (fun x => hFcb _)
    rw [integral_integral_swap hjoint]
    refine norm_integral_le_of_norm_le (g := fun ξ => E ξ ζ w) ?_
      (Filter.Eventually.of_forall fun ξ => ?_)
    · refine decay_bdd_real γ ?_ (fun ξ => hEb ξ ζ w)
      have := hEc.comp (show Continuous (fun ξ : ℝ => (ξ, ζ, w)) by fun_prop)
      exact this
    · exact (decay_lvl1 Δ i j u ξ ζ w).le
  show ‖∫ p, Fc p ∂(μ.prod ν)‖ ≤ _
  rw [integral_prod_symm Fc hFi]
  set G : (Fin Nin → ℝ) → ℂ := fun w => ∫ z, Fc (z, w) ∂μ with hGdef
  have hG : Integrable G ν := hFi.integral_prod_right
  rw [slice_pi_c Nin j G hG]
  have hEi : Integrable (fun x : (Fin Nin → ℝ) × (ℝ × ℝ) => E x.2.1 x.2.2 x.1)
      (ν.prod (γ.prod γ)) := by
    refine decay_bdd_real _ ?_ (fun x => hEb _ _ _)
    have := hEc.comp (show Continuous (fun x : (Fin Nin → ℝ) × (ℝ × ℝ) => (x.2.1, x.2.2, x.1))
      by fun_prop)
    exact this
  have hΨ : Integrable (fun w => ∫ p, E p.1 p.2 w ∂(γ.prod γ)) ν := hEi.integral_prod_left
  refine (norm_integral_le_of_norm_le hΨ (Filter.Eventually.of_forall fun w => ?_)).trans ?_
  · have hE2 : Integrable (fun p : ℝ × ℝ => E p.1 p.2 w) (γ.prod γ) := by
      refine decay_bdd_real _ ?_ (fun x => hEb _ _ _)
      have := hEc.comp (show Continuous (fun p : ℝ × ℝ => (p.1, p.2, w)) by fun_prop)
      exact this
    rw [integral_prod_symm _ hE2]
    exact norm_integral_le_of_norm_le hE2.integral_prod_right
      (Filter.Eventually.of_forall fun ζ => lvl2 w ζ)
  · rw [integral_integral_swap (f := fun (w : Fin Nin → ℝ) (p : ℝ × ℝ) => E p.1 p.2 w) hEi]
    unfold sgdPsi
    refine integral_mono hEi.integral_prod_right ?_ (fun p => ?_)
    · refine decay_bdd_real _ ?_ (fun p => ?_)
      · exact Continuous.rpow_const (by fun_prop) (fun p => Or.inl (by positivity))
      · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
        refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by norm_num)
        have : 0 ≤ (|u| * frobNorm Db) ^ 2 * p.1 ^ 2 * p.2 ^ 2 := by positivity
        linarith
    · have h := sgd_gauss_mgf_frob Db (fun k => p.2 * q k) ((u * p.1 * p.2) ^ 2) (sq_nonneg _)
      have e : ∀ w : Fin Nin → ℝ, E p.1 p.2 w
          = Real.exp (-(u * p.1 * p.2) ^ 2 * (∑ k, (Matrix.mulVec Db w k + p.2 * q k) ^ 2) / 2) := by
        intro w
        simp only [hE, hS]
        congr 1
        ring
      simp only [e]
      refine h.trans (le_of_eq ?_)
      congr 1
      simp only [mul_pow, sq_abs]
      ring

/-- **lem:app-sgd-decay**, `Muon.SignSGD.lem_app_sgd_decay`.

cr-2026-10-23. LaTeX statement (verbatim):

\begin{lemma}[Decay of the characteristic function]\label{lem:app-sgd-decay}
If $\norm{\bar\Delta}_\F\ge F/2$, then $\phi_Y(t)\defeq\EE e^{\mathrm i tY}$ satisfies
\begin{equation}\label{eqn:app-sgd-decay}
\abs{\phi_Y(t)}\le\psi\big(\abs t/8\big)\le\min\big\{1,\ C_{\rm ch}\abs t^{-1/2}\big\}\qquad(t\ne0).
\end{equation}
\end{lemma} -/
theorem lem_app_sgd_decay {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0)
    (i : Fin Nout) (j : Fin Nin)
    (hbar : frobNorm Δ / 2 ≤ frobNorm (sgdDeletedBlock Δ i j)) :
    ∀ t : ℝ, t ≠ 0 →
      ‖sgdCharFunY Δ i j t‖ ≤ sgdPsi (|t| / 8) ∧
        sgdPsi (|t| / 8) ≤ min 1 (sgdCch * |t| ^ (-(1 / 2 : ℝ))) := by
  intro t ht
  exact ⟨cm_decay_reduce Δ hΔ i j hbar (fun u => decay_core Δ i j u) t, cm_decay_tail ht⟩

end Muon.SignSGD

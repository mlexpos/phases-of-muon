import Muon.Drift.Tail

/-!
# Appendix E, `lem:app-dyn-mean`(iv): the state-uniform operator-norm response (interface draft)

Snapshot `cr-2026-10-23`. Source: `sections/05-dynamics/section.tex`, proof of `lem:app-dyn-mean`
(iii)–(iv), ll. 908–982. Everything here is on the real axis and non-asymptotic: every constant and
every error sequence is chosen before the dimension, the weights, the state and the samples, and
the error sequences are indexed by the batch size `B` only. This is the drafter's open question F2
("state-uniform `lem:app-de-replace`"): the Lean statement `Muon.DetEquiv.lem_app_de_replace`
(`Concentration.lean`:3487) already has this shape (its `e` is chosen before `m n B w F S t`, and
`F` carries an arbitrary normalized state), so no new uniform deterministic-equivalent statement is
needed. What is missing is the response bound with the state dependence displayed
(`eqn:app-dyn-H-op`); the existing response statements
(`Muon.Drift.prop_app_drift_response_weights`, `Response.lean`:3562) are along `SetupRegime`
sequences, which carry `‖Â‖ → 0` (field `diffuse`) and fixed EMA weights, and their error
contains `r'_B`, `δ_B(I)` that are only small for diffuse states. They cannot give (iv) by a
compactness/contradiction argument: along a subsequence with
`‖Â_k‖ → a > 0` none of them applies.

Declarations.
* `expected_update_contour`: `𝔼 Q_ϱ(M_t) = (2/π) ∫₀^∞ 𝓗(ϱ + u²) du` (the display of (iii),
  ll. 909–912, first identity), public form of the private Fubini helpers of `FiniteMean.lean`
  and `Drift/Mean.lean`.
* `eqn_app_dyn_eps_large` (ll. 934–937).
* `eqn_app_dyn_H_op` (ll. 964–967), with `e^{(1)}_B(s)`, `e^{(2)}_B(s)` passed as upper bounds
  `ε₁`, `ε₂` (the sup over `j` of the replacement errors is attained-or-bounded by any such pair).
* `expected_update_opNorm_uniform`: the integrated bound
  `‖𝔼 Q_ϱ(M_t)‖ ≤ K‖Â‖ + r_B`, `r_B → 0`, with `K, r` depending only on `(ϱ, C_Σ, γ⋆)`
  (ll. 973–982). `lem:app-dyn-mean`(iv) is its corollary along a dimension sequence with
  `B_k → ∞`.
-/

-- Docstrings quote the frozen LaTeX verbatim, which has lines over 100 characters.
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Matrix ENNReal
open Matrix
open Muon Muon.Setup Muon.DetEquiv Muon.Drift

noncomputable section

namespace Muon.Dynamics

variable {m n B : ℕ}

private lemma pe15p4_hQ {m n B : ℕ} (F : FrozenParams m n B) :
    Measurable (fun x : Vec m × Vec n =>
      (dotProduct x.1 (Matrix.mulVec F.A x.2)) •
        (rOut F.C * Muon.outer x.1 x.2 * rIn F.C)) := by
  have hdot : Measurable (fun x : Vec m × Vec n =>
      dotProduct x.1 (Matrix.mulVec F.A x.2)) := by
    show Measurable (fun x : Vec m × Vec n => ∑ i, x.1 i * ∑ j, F.A i j * x.2 j)
    exact Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp measurable_fst).mul
      (Finset.measurable_sum _ (fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp measurable_snd))))
  have hout : Continuous (fun x : Vec m × Vec n => Muon.outer x.1 x.2) :=
    continuous_pi fun i => continuous_pi fun j =>
      ((continuous_apply i).comp continuous_fst).mul
        ((continuous_apply j).comp continuous_snd)
  have hM : Measurable (fun x : Vec m × Vec n =>
      rOut F.C * Muon.outer x.1 x.2 * rIn F.C) :=
    Continuous.measurable ((continuous_const.matrix_mul hout).matrix_mul continuous_const)
  exact hdot.smul hM

private lemma pe15p4_meas_WB {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) : Measurable (WeightedBuf w F S t) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hQ := pe15p4_hQ F
  unfold WeightedBuf
  refine Measurable.tsum fun j => ?_
  refine Measurable.const_smul ?_ (w j)
  show Measurable (fun ω => ((B : ℝ))⁻¹ • ∑ a : Fin B,
    (dotProduct (S.zw (t + 1 - (j : ℤ)) a ω).1
      (Matrix.mulVec F.A (S.zw (t + 1 - (j : ℤ)) a ω).2)) •
      (rOut F.C * outer (S.zw (t + 1 - (j : ℤ)) a ω).1
        (S.zw (t + 1 - (j : ℤ)) a ω).2 * rIn F.C))
  exact (Finset.measurable_sum _ fun a _ => hQ.comp (S.meas _ _)).const_smul ((B : ℝ)⁻¹)

private lemma pe15p4_posDef {m n : ℕ} (M : Mat m n) {c : ℝ} (hc : 0 < c) :
    (M * Mᵀ + c • (1 : Mat m m)).PosDef := by
  have h0 : (M * Mᵀ).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose M
  have hd : (c • (1 : Mat m m)).PosDef := by
    have : c • (1 : Mat m m) = Matrix.diagonal (fun _ : Fin m => c) := by
      ext i j
      by_cases h : i = j <;> simp [h]
    rw [this]
    exact Matrix.posDef_diagonal_iff.mpr (fun _ => hc)
  rw [add_comm]
  exact hd.add_posSemidef h0

open scoped Matrix.Norms.L2Operator in
private lemma pe15p4_abs_entry_le_opNorm {p q : ℕ} (K : Mat p q)
    (i : Fin p) (j : Fin q) : |K i j| ≤ opNorm K := by
  have h1 := Matrix.l2_opNorm_mulVec K (EuclideanSpace.single j (1 : ℝ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin p) ℝ).symm
    (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i
  have h3 : ((EuclideanSpace.equiv (Fin p) ℝ).symm
      (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i = K i j := by
    simp [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at h1
  rw [h3, Real.norm_eq_abs] at h2
  rw [opNorm_eq_norm]
  linarith

private lemma pe15p4_Phi_cont {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ)
    (i : Fin m) (j : Fin n) :
    Continuous (fun p : Mat m n × ℝ =>
      ((p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹ * p.1) i j) := by
  have hA : Continuous (fun p : Mat m n × ℝ =>
      p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m)) := by
    refine Continuous.add (continuous_fst.matrix_mul continuous_fst.matrix_transpose) ?_
    exact (continuous_const.add (continuous_snd.pow 2)).smul continuous_const
  have hI : Continuous (fun p : Mat m n × ℝ =>
      (p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hdet : (p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m)).det ≠ 0 :=
      (pe15p4_posDef p.1 (by positivity : 0 < ϱ + p.2 ^ 2)).det_pos.ne'
    have h1 := continuousAt_matrix_inv
      (p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))
      (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)
    exact h1.comp_of_eq hA.continuousAt rfl
  exact (continuous_apply j).comp ((continuous_apply i).comp (hI.matrix_mul continuous_fst))

private lemma pe15p4_meas_gen {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    {ϱ : ℝ} (hϱ : 0 < ϱ) (i : Fin m) (j : Fin n)
    (WB : Ω → Mat m n) (hWBm : Measurable WB) :
    Measurable (fun p : Ω × ℝ =>
      ((WB p.1 * (WB p.1)ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹ * WB p.1) i j) := by
  have hmp : Measurable (fun p : Ω × ℝ => (WB p.1, p.2)) :=
    (hWBm.comp measurable_fst).prodMk measurable_snd
  have hΦ : Measurable (fun p : Mat m n × ℝ =>
      ((p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹ * p.1) i j) :=
    (pe15p4_Phi_cont hϱ i j).measurable
  exact Measurable.comp (g := fun p : Mat m n × ℝ =>
      ((p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹ * p.1) i j)
    (f := fun p : Ω × ℝ => (WB p.1, p.2)) hΦ hmp

private lemma pe15p4_swap {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) {ϱ : ℝ} (hϱ : 0 < ϱ)
    (i : Fin m) (j : Fin n) :
    Integrable (fun u : ℝ => Hmix w F S t (ϱ + u ^ 2) i j)
      (volume.restrict (Ioi 0)) ∧
      EQ w F S t ϱ i j =
        (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), Hmix w F S t (ϱ + u ^ 2) i j := by
  set WB := WeightedBuf w F S t with hWB
  have hWBm : Measurable WB := pe15p4_meas_WB w F S t
  set g : Ω × ℝ → ℝ := fun p =>
    ((WB p.1 * (WB p.1)ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹ * WB p.1) i j with hg
  have hgm : Measurable g := pe15p4_meas_gen hϱ i j WB hWBm
  have hcont := fun ω => lem_app_setup_contour ϱ hϱ (WB ω)
  have hnorm : ∀ ω, ∀ u : ℝ, ‖g (ω, u)‖ ≤
      nuc ((WB ω * (WB ω)ᵀ + (ϱ + u ^ 2) • (1 : Mat m m))⁻¹ * WB ω) := by
    intro ω u
    rw [Real.norm_eq_abs]
    exact (pe15p4_abs_entry_le_opNorm
      ((WB ω * (WB ω)ᵀ + (ϱ + u ^ 2) • (1 : Mat m m))⁻¹ * WB ω) i j).trans
      (opNorm_le_nuc _)
  have hint : Integrable g (P.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hgm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun ω => (hcont ω).2.1 i j, ?_⟩
    refine Integrable.of_bound (C := Real.pi / 2 * (min m n : ℝ)) ?_ ?_
    · exact hgm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      have h0 : 0 ≤ ∫ u in Ioi (0 : ℝ), ‖g (ω, u)‖ := integral_nonneg fun u => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      refine le_trans
        (integral_mono ((hcont ω).2.1 i j).norm (hcont ω).2.2.1 fun u => hnorm ω u)
        (hcont ω).2.2.2
  have hint' : Integrable (Function.uncurry fun ω u => g (ω, u))
      (P.prod (volume.restrict (Ioi (0 : ℝ)))) := hint
  have hswap := integral_integral_swap hint'
  have hH : ∀ u : ℝ, Hmix w F S t (ϱ + u ^ 2) i j = ∫ ω, g (ω, u) ∂P :=
    fun u => by
      simp only [Hmix, Muon.mean, Matrix.of_apply, Xs, Rs, hg]
      rfl
  refine ⟨?_, ?_⟩
  · simp_rw [hH]
    exact hint.integral_prod_right
  · have hE : EQ w F S t ϱ i j =
        ∫ ω, ((2 / Real.pi) * ∫ u in Ioi (0 : ℝ), g (ω, u)) ∂P := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      exact (hcont ω).1 i j
    rw [hE, integral_const_mul]
    simp_rw [hH]
    rw [← hswap]

private lemma pe15p4_l2_of_cond {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (f : Ω → ℝ) (y : ℝ) (hy : 0 ≤ y) (hf : MemLp f 2 P)
    (hc : ∀ᵐ ζ ∂P, Real.sqrt (condExp G P (fun ω => f ω ^ 2) ζ) ≤ y) :
    eLpNorm f 2 P ≤ ENNReal.ofReal y := by
  have hn : 0 ≤ᵐ[P] condExp G P (fun ω => f ω ^ 2) :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg (f ω))
  have hc2 : ∀ᵐ ζ ∂P, condExp G P (fun ω => f ω ^ 2) ζ ≤ y ^ 2 := by
    filter_upwards [hc, hn] with ζ hz hnz
    simp only [Pi.zero_apply] at hnz
    rw [← Real.sq_sqrt hnz]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hz 2
  have hi : ∫ ω, f ω ^ 2 ∂P ≤ y ^ 2 := by
    rw [← integral_condExp hG]
    have h := integral_mono_ae integrable_condExp (integrable_const _) hc2
    simpa using h
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_iff.mpr ⟨hy, hi⟩

private lemma pe15p4_den_pos {x d : ℝ} (hx : 0 ≤ x) : 0 < 1 + x * d ^ 2 := by
  nlinarith [mul_nonneg hx (sq_nonneg d)]

private lemma pe15p4_f_abs {x d : ℝ} (hx : 0 ≤ x) : |fX x d| ≤ |d| := by
  unfold fX
  rw [abs_div, abs_of_pos (pe15p4_den_pos (d := d) hx)]
  exact div_le_self (abs_nonneg _) (by nlinarith [mul_nonneg hx (sq_nonneg d)])

private lemma pe15p4_psi_abs {x d : ℝ} (hx : 0 ≤ x) : |psiX x d| ≤ d ^ 2 := by
  unfold psiX
  rw [abs_div, abs_of_nonneg (sq_nonneg d), abs_of_pos (pe15p4_den_pos (d := d) hx)]
  exact div_le_self (sq_nonneg _) (by nlinarith [mul_nonneg hx (sq_nonneg d)])

private lemma pe15p4_f_cont {x : ℝ} (hx : 0 ≤ x) : Continuous (fX x) := by
  unfold fX
  exact Continuous.div (by fun_prop) (by fun_prop)
    (fun d => (pe15p4_den_pos (d := d) hx).ne')

private lemma pe15p4_psi_cont {x : ℝ} (hx : 0 ≤ x) : Continuous (psiX x) := by
  unfold psiX
  exact Continuous.div (by fun_prop) (by fun_prop)
    (fun d => (pe15p4_den_pos (d := d) hx).ne')

private lemma pe15p4_ageD_norms {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    eLpNorm (ageD F S t j) 2 P ≤ 1 ∧
      eLpNorm (fun ω => ageD F S t j ω ^ 2) 2 P ≤ 3 := by
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hX
  have hXm : Measurable X := S.meas _ _
  have hmp : MeasurePreserving X P (gaussPair m n) := ⟨hXm, S.law _ _⟩
  have hrm : AEStronglyMeasurable (fun x : Vec m × Vec n => resid F.A x)
      (gaussPair m n) := (by unfold resid; fun_prop : Continuous fun x : Vec m × Vec n =>
        resid F.A x).aestronglyMeasurable
  have hcomp (p : ℝ≥0∞) : eLpNorm (ageD F S t j) p P =
      eLpNorm (fun x => resid F.A x) p (gaussPair m n) := by
    have heq : ageD F S t j = (fun x => resid F.A x) ∘ X := rfl
    rw [heq]
    exact eLpNorm_comp_measurePreserving hrm hmp
  constructor
  · rw [hcomp 2]
    have h := lem_app_de_moments_ii F.A F.hA 1 le_rfl
    norm_num [Nat.doubleFactorial] at h ⊢
    exact h
  · have hdm : AEStronglyMeasurable (ageD F S t j) P :=
      hrm.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
    have hsquare : eLpNorm (fun ω => ageD F S t j ω ^ 2) 2 P =
        eLpNorm (ageD F S t j) 4 P ^ (2 : ℕ) := by
      have heq : (fun ω => ageD F S t j ω ^ 2) =
          fun ω => ‖ageD F S t j ω‖ ^ (2 : ℝ) := by
        funext ω
        norm_num [Real.norm_eq_abs, sq_abs]
      rw [heq, eLpNorm_norm_rpow _ hdm (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hsquare, hcomp 4]
    have h := lem_app_de_moments_ii F.A F.hA 2 (by norm_num)
    have hp := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
    norm_num [Nat.doubleFactorial] at hp ⊢
    calc
      eLpNorm (fun x => resid F.A x) 4 (gaussPair m n) ^ (2 : ℕ)
          ≤ ENNReal.ofReal (3 ^ (1 / 2 : ℝ)) ^ (2 : ℕ) := hp
      _ = 3 := by
        rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _) 2]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num

/-- Contour representation of the expected update, snapshot `cr-2026-10-23`
(`sections/05-dynamics/section.tex` ll. 908–912, first identity):
```latex
\emph{(iii).} By \cref{lem:app-setup-contour} and differentiation of its
integrand in the ridge,
\[
\EE\,\Qridge{\ridge'}(\Mt)=\frac2\pi\int_0^\infty\mathcal H(\ridge'+u^2)\,\dif u,\qquad
```
for a general weight sequence in the class, entrywise, with the integrability of `Q_ϱ(M_t)` and of
`u ↦ 𝓗(ϱ + u²)` on `(0, ∞)`. Ingredients: `Muon.Setup.lem_app_setup_contour`
(`RegularizedMap.lean`:659) and Fubini; the same computation is private in `FiniteMean.lean`
(l. 337) and `Drift/Mean.lean` (l. 283). -/
theorem expected_update_contour {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {w : ℕ → ℝ} (hw : WeightClass w) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Q ϱ (WeightedBuf w F S t ω) i j) P) ∧
    (∀ (i : Fin m) (j : Fin n),
      IntegrableOn (fun u : ℝ => Hmix w F S t (ϱ + u ^ 2) i j) (Ioi (0 : ℝ))) ∧
    ∀ (i : Fin m) (j : Fin n),
      EQ w F S t ϱ i j = (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), Hmix w F S t (ϱ + u ^ 2) i j := by
  refine ⟨fun i j => ?_, ⟨fun i j => (pe15p4_swap w F S t hϱ i j).1,
    fun i j => (pe15p4_swap w F S t hϱ i j).2⟩⟩
  have hmeas := pe15p4_meas_WB w F S t
  have hc : Continuous (fun M : Mat m n => Q ϱ M) := by
    have := (continuousOn_Q_pos (m := m) (n := n)).comp
      ((continuous_const.prodMk continuous_id).continuousOn :
        ContinuousOn (fun M : Mat m n => (ϱ, M)) univ)
      (fun M _ => ⟨hϱ, trivial⟩)
    exact continuousOn_univ.1 this
  have hqm : Measurable (fun ω => Q ϱ (WeightedBuf w F S t ω)) := hc.measurable.comp hmeas
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp hqm)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    exact (pe15p4_abs_entry_le_opNorm _ i j).trans
      ((lem_app_setup_filter_i ϱ hϱ.le (WeightedBuf w F S t ω)).1.trans (by norm_num))

/-- `eqn:app-dyn-eps-large`, snapshot `cr-2026-10-23` (`sections/05-dynamics/section.tex`
ll. 925–937):
```latex
For a sample of age $j$, with
$\check x_j=\emaw j^2q_B$ and the targets $\check\alpha_{1,j},\check\alpha_{2,j}$
of \cref{eqn:app-de-targets}, put
\[
\mathsf e^{(1)}_B(s)\defeq\sup_j\frac{\norm{\alpha_{1,j}-\check\alpha_{1,j}}_2}{\emaw j},\qquad
\mathsf e^{(2)}_B(s)\defeq\sup_j\frac{\norm{\alpha_{2,j}-\check\alpha_{2,j}}_2}{\emaw j^2}.
\]
Then $\sup_{s\in I}(\mathsf e^{(1)}_B+\mathsf e^{(2)}_B)\le2e_B(I)$ on every
compact $I$, and for $s\ge1$, by \cref{lem:app-drift-coeffmoments},
$\abs{f_x(d)}\le\abs d$, $0\le\psi_x(d)\le d^2$ and $\sigma_B\le C_\Sigma\gamma_\star/s$,
\begin{equation}\label{eqn:app-dyn-eps-large}
\mathsf e^{(1)}_B(s)\le C,\qquad\mathsf e^{(2)}_B(s)\le\frac Cs .
\end{equation}
```
Encoding: the suprema over `j` are unfolded (`‖α_{1,j} − α̌_{1,j}‖₂ ≤ w_j C` for every `j`); `C`
depends only on `(C_Σ, γ⋆)` and is chosen before all data; the weights are a general sequence in
the class. The compact-`I` clause is `Muon.DetEquiv.lem_app_de_replace`. -/
theorem eqn_app_dyn_eps_large (CS γ : ℝ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (w : ℕ → ℝ) (F : FrozenParams m n B)
      (S : FrozenSamples P m n B) (t : ℤ),
      WeightClass w → opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ (j : ℕ) (s : ℝ), 1 ≤ s →
        eLpNorm (fun ω => delAlpha1 w F S t j s ω - checkAlpha1 w F S t j s ω) 2 P
            ≤ ENNReal.ofReal (w j * C) ∧
        eLpNorm (fun ω => delAlpha2 w F S t j s ω - checkAlpha2 w F S t j s ω) 2 P
            ≤ ENNReal.ofReal (w j ^ 2 * C / s) := by
  let CSp := max CS 0
  let γp := max γ 0
  obtain ⟨Cc, hCc0, hCc⟩ := tl_facts CSp γp (le_max_right _ _)
  refine ⟨Cc + 1 + 3 * (CSp * γp), ?_⟩
  intro Ω inst m n B P _ w F S t hw hCo hCi hm hn j s hs
  have hwp0 : 0 ≤ w j := hw.1.1 j
  have hwp1 : w j ≤ 1 := hw.2.1 j
  have hCop : opNorm F.C.Sout ≤ CSp := hCo.trans (le_max_left _ _)
  have hCip : opNorm F.C.Sin ≤ CSp := hCi.trans (le_max_left _ _)
  have hmp : (m : ℝ) ≤ γp * B := hm.trans (mul_le_mul_of_nonneg_right
    (le_max_left _ _) (Nat.cast_nonneg B))
  have hnp : (n : ℝ) ≤ γp * B := hn.trans (mul_le_mul_of_nonneg_right
    (le_max_left _ _) (Nat.cast_nonneg B))
  obtain ⟨-, -, -, L1, L2, c1, c2, -, -⟩ :=
    hCc Ω m n B P F S t j w hwp0 hwp1 hCop hCip hmp hnp s hs
  have hG : sigmaOthers F S t j ≤ inst := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have ha1 : eLpNorm (delAlpha1 w F S t j s) 2 P ≤ ENNReal.ofReal (Cc * w j) :=
    pe15p4_l2_of_cond P _ hG _ _ (mul_nonneg hCc0 hwp0) L1 c1
  have hspos : 0 < s := lt_of_lt_of_le one_pos hs
  have ha2 : eLpNorm (delAlpha2 w F S t j s) 2 P ≤
      ENNReal.ofReal (Cc * w j ^ 2 / s) :=
    pe15p4_l2_of_cond P _ hG _ _ (by positivity) L2 c2
  obtain ⟨hd1, hd2⟩ := pe15p4_ageD_norms F S t j
  obtain ⟨hσ0, hσ, -, -, hq0, -⟩ := eqn_app_de_qI w hw F S t CSp γp s {s}
    hspos (by intro x hx; rcases hx with rfl; exact le_rfl)
      ⟨hCop, hCip⟩ ⟨hmp, hnp⟩ s (Set.mem_singleton s)
  have hx0 : 0 ≤ w j ^ 2 * qB w F S t s := mul_nonneg (sq_nonneg _) hq0
  have hdm : Measurable (ageD F S t j) := by
    have hX := S.meas (t + 1 - (j : ℤ)) (slotOne F.hB)
    show Measurable (fun ω => ∑ i,
      (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).1 i *
        ∑ k, F.A i k * (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).2 k)
    exact Finset.measurable_sum _ (fun i _ =>
      ((measurable_pi_apply i).comp hX.fst).mul
        (Finset.measurable_sum _ (fun k _ =>
          measurable_const.mul ((measurable_pi_apply k).comp hX.snd))))
  have hc1m : AEStronglyMeasurable (checkAlpha1 w F S t j s) P := by
    unfold checkAlpha1
    exact ((pe15p4_f_cont hx0).measurable.comp hdm).const_mul (w j) |>.aestronglyMeasurable
  have hc1 : eLpNorm (checkAlpha1 w F S t j s) 2 P ≤ ENNReal.ofReal (w j) := by
    have hm := eLpNorm_mono_ae (p := 2) (g := fun ω => w j * ageD F S t j ω) hc1m
      (Filter.Eventually.of_forall fun ω => by
      simp only [checkAlpha1, Real.norm_eq_abs, abs_mul, abs_of_nonneg hwp0]
      exact mul_le_mul_of_nonneg_left (pe15p4_f_abs hx0) hwp0)
    refine hm.trans ?_
    have heq : (fun ω => w j * ageD F S t j ω) = (w j) • ageD F S t j := rfl
    rw [heq, eLpNorm_const_smul]
    simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hwp0]
    calc ENNReal.ofReal (w j) * eLpNorm (ageD F S t j) 2 P
        ≤ ENNReal.ofReal (w j) * 1 :=
          mul_le_mul le_rfl hd1 (by positivity) (by positivity)
      _ = ENNReal.ofReal (w j) := mul_one _
  have hc2m : AEStronglyMeasurable (checkAlpha2 w F S t j s) P := by
    unfold checkAlpha2
    exact ((pe15p4_psi_cont hx0).measurable.comp hdm).const_mul
      (w j ^ 2 * sigmaB w F S t s) |>.aestronglyMeasurable
  have hc2 : eLpNorm (checkAlpha2 w F S t j s) 2 P ≤
      ENNReal.ofReal (3 * (w j ^ 2 * (CSp * γp / s))) := by
    have hm := eLpNorm_mono_ae (p := 2)
      (g := fun ω => (w j ^ 2 * sigmaB w F S t s) * ageD F S t j ω ^ 2) hc2m
      (Filter.Eventually.of_forall fun ω => by
      simp only [checkAlpha2, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ0)]
      exact mul_le_mul_of_nonneg_left
        (by simpa [abs_of_nonneg (sq_nonneg (ageD F S t j ω))] using
          (pe15p4_psi_abs (d := ageD F S t j ω) hx0))
        (mul_nonneg (sq_nonneg _) hσ0))
    refine hm.trans ?_
    have heq : (fun ω => (w j ^ 2 * sigmaB w F S t s) * ageD F S t j ω ^ 2) =
        (w j ^ 2 * sigmaB w F S t s) • (fun ω => ageD F S t j ω ^ 2) := rfl
    rw [heq, eLpNorm_const_smul]
    simp only [Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ0)]
    calc ENNReal.ofReal (w j ^ 2 * sigmaB w F S t s) *
          eLpNorm (fun ω => ageD F S t j ω ^ 2) 2 P
        ≤ ENNReal.ofReal (w j ^ 2 * sigmaB w F S t s) * 3 :=
          mul_le_mul le_rfl hd2 (by positivity) (by positivity)
      _ ≤ ENNReal.ofReal (3 * (w j ^ 2 * (CSp * γp / s))) := by
        rw [show (3 : ENNReal) = ENNReal.ofReal 3 by norm_num,
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ w j ^ 2 * sigmaB w F S t s)]
        exact ENNReal.ofReal_le_ofReal
          (by nlinarith [mul_le_mul_of_nonneg_left hσ (sq_nonneg (w j))])
  constructor
  · refine (eLpNorm_sub_le (by norm_num)).trans ((add_le_add ha1 hc1).trans ?_)
    rw [← ENNReal.ofReal_add (mul_nonneg hCc0 hwp0) hwp0]
    exact ENNReal.ofReal_le_ofReal (by
      have : 0 ≤ 3 * (CSp * γp) := by positivity
      nlinarith)
  · refine (eLpNorm_sub_le (by norm_num)).trans ((add_le_add ha2 hc2).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ Cc * w j ^ 2 / s)
      (by positivity : 0 ≤ 3 * (w j ^ 2 * (CSp * γp / s)))]
    refine ENNReal.ofReal_le_ofReal ?_
    calc
      Cc * w j ^ 2 / s + 3 * (w j ^ 2 * (CSp * γp / s)) =
          w j ^ 2 * (Cc + 3 * (CSp * γp)) / s := by ring
      _ ≤ w j ^ 2 * (Cc + 1 + 3 * (CSp * γp)) / s := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)) hspos.le

/-! ### Private copies of the response-argument helpers of `Drift/Response.lean` (task P-E.15.P4)

Copied verbatim from the private helpers of `Muon/Drift/Response.lean` (`pe_src_err` and `pe_gram_err` with
the explicit `s`-dependence kept in place of the `s ≥ s₀` constants). -/

section TlHelpers
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
open scoped MatrixOrder

private lemma tlb_opNorm_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ opNorm A := by
  unfold opNorm; exact norm_nonneg _

private lemma tlb_fro_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma tlb_fro_sq {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

open scoped Matrix.Norms.L2Operator in
private lemma tlb_fro_mul_le_left {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
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
    rw [tlb_fro_sq, mul_pow, tlb_fro_sq, Finset.sum_comm]
    calc ∑ j, ∑ i, (M * N) i j ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, N k j ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, N k j ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (tlb_fro_nonneg _) (mul_nonneg (tlb_opNorm_nonneg M)
    (tlb_fro_nonneg N)) two_ne_zero).mp hfro

open scoped Matrix.Norms.L2Operator in
private lemma tlb_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma tlb_fro_transpose {k l : ℕ} (A : Mat k l) : fro Aᵀ = fro A := by
  unfold fro
  congr 1
  simp only [Matrix.transpose_apply]
  exact Finset.sum_comm

private lemma tlb_fro_mul_le_right {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ fro M * opNorm N := by
  have h := tlb_fro_mul_le_left Nᵀ Mᵀ
  rw [← Matrix.transpose_mul, tlb_fro_transpose, tlb_opNorm_transpose, tlb_fro_transpose] at h
  linarith [mul_comm (opNorm N) (fro M)]

open scoped Matrix.Norms.L2Operator in
private lemma tlb_opNorm_mul_le {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B

open scoped Matrix.Norms.L2Operator in
/-- `‖r_out‖² = ‖Σ_out‖` for the regularized square root `r_out`. -/
private lemma tlb_opNorm_rOut_mul_self {m n : ℕ} (C : Covariances m n) :
    opNorm (rOut C) * opNorm (rOut C) = opNorm C.Sout := by
  have hh : (rOut C)ᴴ = rOut C :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sout)).isHermitian
  have hsq : rOut C * rOut C = C.Sout :=
    CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)
  have := Matrix.l2_opNorm_conjTranspose_mul_self (rOut C)
  rw [hh, hsq] at this
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact this.symm

open scoped Matrix.Norms.L2Operator in
/-- The `r_in` analogue of `tlb_opNorm_rOut_mul_self`. -/
private lemma tlb_opNorm_rIn_mul_self {m n : ℕ} (C : Covariances m n) :
    opNorm (rIn C) * opNorm (rIn C) = opNorm C.Sin := by
  have hh : (rIn C)ᴴ = rIn C :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  have hsq : rIn C * rIn C = C.Sin :=
    CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)
  have := Matrix.l2_opNorm_conjTranspose_mul_self (rIn C)
  rw [hh, hsq] at this
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact this.symm

private lemma tlb_fro_one {m : ℕ} : fro (1 : Mat m m) = Real.sqrt m := by
  unfold fro
  simp [Matrix.one_apply]

/-- `‖S‖_F ≤ √m ‖S‖` for `S` square of size `m` (the factor `√m` of the Id term). -/
private lemma tlb_fro_le_sqrt_mul_opNorm {m : ℕ} (S : Mat m m) :
    fro S ≤ Real.sqrt m * opNorm S := by
  have h := tlb_fro_mul_le_left S (1 : Mat m m)
  rw [Matrix.mul_one, tlb_fro_one] at h
  linarith [mul_comm (opNorm S) (Real.sqrt m)]

/-- Conditional Jensen for the square: `(E_𝒢 e)² ≤ E_𝒢 e²` a.e. -/
private lemma tlb_jensen_sq (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ) (e : Ω → ℝ) (he2 : MemLp e 2 P) :
    ∀ᵐ ζ ∂P, condExp G P e ζ ^ 2 ≤ condExp G P (fun ω => e ω ^ 2) ζ := by
  have hcvx : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := (Even.convexOn_pow (by decide))
  have hcont : LowerSemicontinuousOn (fun x : ℝ => x ^ 2) Set.univ :=
    (by fun_prop : Continuous fun x : ℝ => x ^ 2).continuousOn.lowerSemicontinuousOn
  have h := ConvexOn.map_condExp_le (μ := P) (m := G) (mα := mΩ) hG hcvx hcont
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) isClosed_univ
    (he2.integrable one_le_two) (he2.integrable_sq)
  filter_upwards [h] with ζ hζ
  simpa [Function.comp_def] using hζ

/-! ## Private integrability helpers (copies of private lemmas of `Muon.DetEquiv.Gaussian`) -/

section BfCopies
open Muon.Foundations

private lemma tlb_gmono {n k : ℕ} (c : Fin k → Fin n) :
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

private lemma tlb_gtwo {n : ℕ} (p q : Fin n) :
    Integrable (fun z : Fin n → ℝ => z p * z q) (stdGaussianPi n) := by
  have h := tlb_gmono (n := n) ![p, q]
  simpa [Fin.prod_univ_two] using h

private lemma tlb_gfour {n : ℕ} (p q r s : Fin n) :
    Integrable (fun z : Fin n → ℝ => z p * z q * z r * z s) (stdGaussianPi n) := by
  have h := tlb_gmono (n := n) ![p, q, r, s]
  simpa [Fin.prod_univ_four] using h

private lemma tlb_gfam1_memLp (m n : ℕ) (a : Fin m × Fin n) :
    MemLp (fun x : Vec m × Vec n => x.1 a.1 * x.2 a.2) 2 (gaussPair m n) := by
  have hm : Measurable (fun x : Vec m × Vec n => x.1 a.1 * x.2 a.2) := by fun_prop
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have h := Integrable.mul_prod (tlb_gtwo a.1 a.1) (tlb_gtwo a.2 a.2)
  unfold gaussPair
  convert h using 2 with x
  ring

private lemma tlb_gsq_memLp (d : ℕ) (a : Fin d × Fin d) :
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
  exact ((tlb_gfour _ _ _ _).sub ((tlb_gtwo _ _).const_mul _)).add (integrable_const _)

private lemma tlb_aem {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n : ℕ}
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

private lemma tlb_sq_memLp {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n)
    (π : Vec m × Vec n → Vec d) (hπ : Measurable π)
    (hmap : (gaussPair m n).map π = stdGaussianPi d) (a : Fin d × Fin d) :
    MemLp (fun w => (π (X w)) a.1 * (π (X w)) a.2
      - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2 P := by
  have h1 : MemLp (fun z : Vec d => z a.1 * z a.2 - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2
      (Measure.map π (gaussPair m n)) := by rw [hmap]; exact tlb_gsq_memLp d a
  have h2 := h1.comp_of_map hπ.aemeasurable
  have hg : MemLp (fun x : Vec m × Vec n => (π x) a.1 * (π x) a.2
      - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2 (@Measure.map Ω (Vec m × Vec n) mΩ _ X P) := by
    rw [hX]; exact h2
  exact hg.comp_of_map (tlb_aem P X hX)

end BfCopies

/-- Conditional expectation of a finite weighted sum of integrable functions. -/
private lemma tlb_condExp_sum {ι : Type*} [Fintype ι] (P : Measure Ω) (G : MeasurableSpace Ω)
    (g : ι → Ω → ℝ) (hg : ∀ i, Integrable (g i) P) (c : ι → ℝ) :
    condExp G P (fun ω => ∑ i, c i * g i ω) =ᵐ[P] fun ζ => ∑ i, c i * condExp G P (g i) ζ := by
  have h1 : (fun ω => ∑ i, c i * g i ω) = ∑ i, c i • g i := by
    funext ω; simp [Finset.sum_apply]
  rw [h1]
  refine (condExp_finsetSum (fun i _ => (hg i).smul (c i)) G).trans ?_
  have hall : ∀ᵐ ζ ∂P, ∀ i, condExp G P (c i • g i) ζ = (c i • condExp G P (g i)) ζ :=
    ae_all_iff.2 fun i => condExp_smul (c i) (g i) G
  filter_upwards [hall] with ζ hζ
  simp [Finset.sum_apply, hζ]

private lemma tlb_memLp_sq_fst {m n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (a b : Fin m) :
    MemLp (fun ω => (X ω).1 a * (X ω).1 b - (1 : Mat m m) a b) 2 P := by
  have hmap : (gaussPair m n).map Prod.fst = Muon.Foundations.stdGaussianPi m := by
    unfold gaussPair
    rw [Measure.map_fst_prod]; simp
  exact tlb_sq_memLp P X hX Prod.fst measurable_fst hmap (a, b)

private lemma tlb_memLp_sq_snd {m n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (a b : Fin n) :
    MemLp (fun ω => (X ω).2 a * (X ω).2 b - (1 : Mat n n) a b) 2 P := by
  have hmap : (gaussPair m n).map Prod.snd = Muon.Foundations.stdGaussianPi n := by
    unfold gaussPair
    rw [Measure.map_snd_prod]; simp
  exact tlb_sq_memLp P X hX Prod.snd measurable_snd hmap (a, b)

private lemma tlb_memLp_cross {m n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (a : Fin m) (b : Fin n) :
    MemLp (fun ω => (X ω).1 a * (X ω).2 b) 2 P := by
  have hg : MemLp (fun x : Vec m × Vec n => x.1 a * x.2 b) 2
      (@Measure.map Ω (Vec m × Vec n) mΩ _ X P) := by
    rw [hX]; exact tlb_gfam1_memLp m n (a, b)
  exact hg.comp_of_map (tlb_aem P X hX)

private lemma tlb_integrable_mul {f g : Ω → ℝ} {P : Measure Ω} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg

open scoped Matrix.Norms.Frobenius in
private lemma tlb_fro_add {k l : ℕ} (A B' : Mat k l) : fro (A + B') ≤ fro A + fro B' := by
  rw [fro_eq_norm, fro_eq_norm, fro_eq_norm]; exact norm_add_le _ _

open scoped Matrix.Norms.Frobenius in
private lemma tlb_fro_smul {k l : ℕ} (c : ℝ) (A : Mat k l) : fro (c • A) = |c| * fro A := by
  rw [fro_eq_norm, fro_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma tlc_Rs_continuous {m n : ℕ} (s : ℝ) (hs : 0 < s) :
    Continuous (fun M : Mat m n => Rs M s) := by
  rw [continuous_iff_continuousAt]
  intro M
  have hA : ∀ M : Mat m n, IsUnit (M * Mᵀ + s • (1 : Mat m m)).det := by
    intro M
    have h6 := (lem_app_de_resolvent M s hs).2.2.2.2.2.1
    have : Rs M s * (M * Mᵀ + s • (1 : Mat m m)) = 1 := by
      rw [Matrix.mul_add, h6, Matrix.mul_smul, Matrix.mul_one]
      abel
    exact Matrix.isUnit_det_of_left_inverse this
  have hcont : ContinuousAt (fun M : Mat m n => M * Mᵀ + s • (1 : Mat m m)) M := by
    fun_prop
  have hdet : (M * Mᵀ + s • (1 : Mat m m)).det ≠ 0 := (hA M).ne_zero
  have hinv : ContinuousAt (Inv.inv : Mat m m → Mat m m) (M * Mᵀ + s • (1 : Mat m m)) := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  show ContinuousAt (fun M : Mat m n => (M * Mᵀ + s • (1 : Mat m m))⁻¹) M
  exact ContinuousAt.comp (g := fun A : Mat m m => A⁻¹)
    (f := fun M : Mat m n => M * Mᵀ + s • (1 : Mat m m)) hinv hcont

private lemma tlc_Rts_continuous {m n : ℕ} (s : ℝ) (hs : 0 < s) :
    Continuous (fun M : Mat m n => Rts M s) := by
  have e : (fun M : Mat m n => Rts M s) = fun M => Rs Mᵀ s := by
    funext M; simp [Rts, Rs]
  rw [e]
  exact (tlc_Rs_continuous s hs).comp continuous_id.matrix_transpose

private lemma tlc_alpha_cont {m n : ℕ} (s : ℝ) (hs : 0 < s) :
    Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.alpha1 q.1 q.2.1 q.2.2.1 q.2.2.2 s) ∧
    Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.alpha2 q.1 q.2.1 q.2.2.1 q.2.2.2 s) ∧
    Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.alpha3 q.1 q.2.1 q.2.2.1 q.2.2.2 s) := by
  have hR := tlc_Rs_continuous (m := m) (n := n) s hs
  have hRt := tlc_Rts_continuous (m := m) (n := n) s hs
  have hX : Continuous (fun M : Mat m n => Muon.DetEquiv.Xs M s) := by
    unfold Muon.DetEquiv.Xs; exact hR.matrix_mul continuous_id
  have hU : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.delU q.1 q.2.2.1 s) := by
    simp only [Muon.DetEquiv.delU, dotProduct]
    fun_prop
  have hV : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.delV q.1 q.2.2.2 s) := by
    simp only [Muon.DetEquiv.delV, dotProduct]
    fun_prop
  have hC : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.delC q.1 q.2.2.1 q.2.2.2 s) := by
    simp only [Muon.DetEquiv.delC, dotProduct]
    fun_prop
  have hL : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.delLambda q.1 q.2.1 q.2.2.1 q.2.2.2 s) := by
    simp only [Muon.DetEquiv.delLambda]
    fun_prop
  have hne : ∀ q : Mat m n × ℝ × Vec m × Vec n,
      Muon.DetEquiv.delLambda q.1 q.2.1 q.2.2.1 q.2.2.2 s ≠ 0 :=
    fun q => (Muon.DetEquiv.lem_app_de_deletion q.1 q.2.1 q.2.2.1 q.2.2.2
      (q.1 + q.2.1 • Muon.outer q.2.2.1 q.2.2.2) s rfl hs).1.ne'
  refine ⟨?_, ?_, ?_⟩
  · simp only [Muon.DetEquiv.alpha1]
    exact (continuous_fst.comp continuous_snd |>.mul
      (continuous_const.add ((continuous_fst.comp continuous_snd).mul hC))).div hL hne
  · simp only [Muon.DetEquiv.alpha2]
    exact (((continuous_fst.comp continuous_snd).pow 2).mul hU).div hL hne
  · simp only [Muon.DetEquiv.alpha3]
    exact ((continuous_const.mul ((continuous_fst.comp continuous_snd).pow 2)).mul hV).neg.div hL hne
/-- Matrix product entry as a sum over the index pairs of the middle factor. -/
private lemma tlc_mul3_apply {p q r t : ℕ} (A : Mat p q) (B : Mat q r) (C : Mat r t) (i : Fin p)
    (j : Fin t) :
    (A * B * C) i j = ∑ x : Fin q × Fin r, (A i x.1 * C x.2 j) * B x.1 x.2 := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- Entrywise pull-out of bounded `𝒢`-measurable matrix factors from `condExpMat`. -/
private lemma tlc_condExpMat_pull {p q r t : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ) (L : Ω → Mat p q) (R : Ω → Mat r t)
    (cL cR : ℝ) (hcL : 0 ≤ cL) (hcR : 0 ≤ cR)
    (hL : ∀ i j, Measurable[G] (fun ω => L ω i j))
    (hR : ∀ i j, Measurable[G] (fun ω => R ω i j))
    (hLb : ∀ ω i j, |L ω i j| ≤ cL) (hRb : ∀ ω i j, |R ω i j| ≤ cR)
    (F : Ω → Mat q r) (hF : ∀ k l, Integrable (fun ω => F ω k l) P) :
    ∀ᵐ ζ ∂P, Muon.Foundations.condExpMat G P (fun ω => L ω * F ω * R ω) ζ = L ζ * Muon.Foundations.condExpMat G P F ζ * R ζ := by
  have hint : ∀ i j (x : Fin q × Fin r),
      Integrable (fun ω => (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) P := by
    intro i j x
    refine Integrable.bdd_mul (c := cL * cR) (hF x.1 x.2)
      (((hL i x.1).mul (hR x.2 j)).mono hG le_rfl).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hLb ω i x.1) (hRb ω x.2 j) (abs_nonneg _) hcL
  have hterm : ∀ i j (x : Fin q × Fin r), ∀ᵐ ζ ∂P,
      condExp G P (fun ω => (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) ζ =
        (L ζ i x.1 * R ζ x.2 j) * condExp G P (fun ω => F ω x.1 x.2) ζ := by
    intro i j x
    have hfm : Measurable[G] (fun ω => L ω i x.1 * R ω x.2 j) := (hL i x.1).mul (hR x.2 j)
    have := condExp_mul_of_stronglyMeasurable_left (m := G) (μ := P)
      (f := fun ω => L ω i x.1 * R ω x.2 j) (g := fun ω => F ω x.1 x.2)
      hfm.stronglyMeasurable (hint i j x) (hF x.1 x.2)
    filter_upwards [this] with ζ hζ
    exact hζ
  have hentry : ∀ i j, ∀ᵐ ζ ∂P,
      Muon.Foundations.condExpMat G P (fun ω => L ω * F ω * R ω) ζ i j = (L ζ * Muon.Foundations.condExpMat G P F ζ * R ζ) i j := by
    intro i j
    have h1 : condExp G P (fun ω => ∑ x : Fin q × Fin r, (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2)
        =ᵐ[P] ∑ x : Fin q × Fin r,
          condExp G P (fun ω => (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) := by
      have e : (fun ω => ∑ x : Fin q × Fin r, (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) =
          ∑ x : Fin q × Fin r, (fun ω => (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) := by
        funext ω; simp [Finset.sum_apply]
      rw [e]
      exact condExp_finsetSum (fun x _ => hint i j x) G
    have h2 : ∀ᵐ ζ ∂P, ∀ x : Fin q × Fin r,
        condExp G P (fun ω => (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) ζ =
          (L ζ i x.1 * R ζ x.2 j) * condExp G P (fun ω => F ω x.1 x.2) ζ :=
      ae_all_iff.2 fun x => hterm i j x
    filter_upwards [h1, h2] with ζ h1ζ h2ζ
    have e2 : (fun ω => (L ω * F ω * R ω) i j) =
        fun ω => ∑ x : Fin q × Fin r, (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2 :=
      funext fun ω => tlc_mul3_apply _ _ _ _ _
    rw [Muon.Foundations.condExpMat_apply, e2, h1ζ, Finset.sum_apply, tlc_mul3_apply]
    exact Finset.sum_congr rfl fun x _ => h2ζ x
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hentry i j] with ζ hζ
  ext i j
  exact hζ i j

/-- Operator-norm bound on matrix entries (copy of the trace-file helper). -/
private lemma tlc_abs_entry_le {p q : ℕ} (K : Mat p q) (i : Fin p) (j : Fin q) :
    |K i j| ≤ opNorm K := by
  have h1 := Matrix.l2_opNorm_mulVec K (EuclideanSpace.single j (1 : ℝ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin p) ℝ).symm
    (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i
  have h3 : ((EuclideanSpace.equiv (Fin p) ℝ).symm
      (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i = K i j := by
    simp [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at h1
  rw [h3, Real.norm_eq_abs] at h2
  rw [opNorm_eq_norm]
  linarith

/-- Vector-form integrability: `e (u_a v_b)` is integrable when `u = c R x`, `v = c' S y`. -/
private lemma tlc_int_outer {d d' : ℕ} (P : Measure Ω) (x : Ω → Vec d) (y : Ω → Vec d')
    (R : Mat d d) (S : Mat d' d') (c c' : ℝ) (u : Ω → Vec d) (v : Ω → Vec d') (e : Ω → ℝ)
    (hu : ∀ ω, u ω = c • (R *ᵥ x ω)) (hv : ∀ ω, v ω = c' • (S *ᵥ y ω))
    (hxy : ∀ p q, Integrable (fun ω => x ω p * y ω q * e ω) P) (a : Fin d) (b : Fin d') :
    Integrable (fun ω => e ω * (u ω a * v ω b)) P := by
  have h : (fun ω => e ω * (u ω a * v ω b)) = fun ω =>
      ∑ p : Fin d, ∑ q : Fin d', (c * c' * (R a p * S b q)) * (x ω p * y ω q * e ω) := by
    funext ω
    rw [hu, hv]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [h]
  exact integrable_finset_sum _ fun p _ =>
    integrable_finset_sum _ fun q _ => (hxy p q).const_mul _

/-- Entries of `L * F * R` are integrable under bounded `𝒢`-measurable factors. -/
private lemma tlc_int_LFR {p q r t : ℕ} (P : Measure Ω) (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (L : Ω → Mat p q) (R : Ω → Mat r t) (cL cR : ℝ) (hcL : 0 ≤ cL)
    (hL : ∀ i j, Measurable[G] (fun ω => L ω i j))
    (hR : ∀ i j, Measurable[G] (fun ω => R ω i j))
    (hLb : ∀ ω i j, |L ω i j| ≤ cL) (hRb : ∀ ω i j, |R ω i j| ≤ cR)
    (F : Ω → Mat q r) (hF : ∀ k l, Integrable (fun ω => F ω k l) P) (i : Fin p) (j : Fin t) :
    Integrable (fun ω => (L ω * F ω * R ω) i j) P := by
  have e : (fun ω => (L ω * F ω * R ω) i j) =
      fun ω => ∑ x : Fin q × Fin r, (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2 :=
    funext fun ω => tlc_mul3_apply _ _ _ _ _
  rw [e]
  refine integrable_finset_sum _ fun x _ => ?_
  refine Integrable.bdd_mul (c := cL * cR) (hF x.1 x.2)
    (((hL i x.1).mul (hR x.2 j)).mono hG le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hLb ω i x.1) (hRb ω x.2 j) (abs_nonneg _) hcL

/-- Entrywise additivity of `condExpMat`. -/
private lemma tlc_condExpMat_add {p q : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (A B : Ω → Mat p q)
    (hA : ∀ i j, Integrable (fun ω => A ω i j) P) (hB : ∀ i j, Integrable (fun ω => B ω i j) P) :
    ∀ᵐ ζ ∂P, Muon.Foundations.condExpMat G P (fun ω => A ω + B ω) ζ =
      Muon.Foundations.condExpMat G P A ζ + Muon.Foundations.condExpMat G P B ζ := by
  have hent : ∀ i j, ∀ᵐ ζ ∂P, Muon.Foundations.condExpMat G P (fun ω => A ω + B ω) ζ i j =
      (Muon.Foundations.condExpMat G P A ζ + Muon.Foundations.condExpMat G P B ζ) i j := by
    intro i j
    have h := condExp_add (hA i j) (hB i j) G
    filter_upwards [h] with ζ hζ
    rw [Matrix.add_apply, Muon.Foundations.condExpMat_apply, Muon.Foundations.condExpMat_apply,
      Muon.Foundations.condExpMat_apply]
    exact hζ
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hent i j] with ζ hζ
  ext i j
  exact hζ i j

/-- Operator-norm sandwich for the Frobenius norm. -/
private lemma tlc_fro_sandwich {p q r t : ℕ} (L : Mat p q) (K : Mat q r) (R : Mat r t) :
    fro (L * K * R) ≤ opNorm L * fro K * opNorm R :=
  (tlb_fro_mul_le_right _ _).trans
    (mul_le_mul_of_nonneg_right (tlb_fro_mul_le_left _ _) (tlb_opNorm_nonneg _))

/-- Frobenius bound for a pulled-out sandwich `L (condExp F) R` under a Bessel bound on `F`. -/
private lemma tlc_term {p q r t : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ) (L : Ω → Mat p q) (R : Ω → Mat r t)
    (cL cR : ℝ) (hcL : 0 ≤ cL) (hcR : 0 ≤ cR)
    (hL : ∀ i j, Measurable[G] (fun ω => L ω i j))
    (hR : ∀ i j, Measurable[G] (fun ω => R ω i j))
    (hLb : ∀ ω i j, |L ω i j| ≤ cL) (hRb : ∀ ω i j, |R ω i j| ≤ cR)
    (F : Ω → Mat q r) (hF : ∀ k l, Integrable (fun ω => F ω k l) P)
    (aL aR K : ℝ) (haL0 : 0 ≤ aL) (haR0 : 0 ≤ aR) (hK0 : 0 ≤ K)
    (haL : ∀ ζ, opNorm (L ζ) ≤ aL) (haR : ∀ ζ, opNorm (R ζ) ≤ aR)
    (hK : ∀ᵐ ζ ∂P, fro (Muon.Foundations.condExpMat G P F ζ) ≤ K) :
    ∀ᵐ ζ ∂P, fro (Muon.Foundations.condExpMat G P (fun ω => L ω * F ω * R ω) ζ) ≤ aL * K * aR := by
  filter_upwards [tlc_condExpMat_pull (mΩ := mΩ) P G hG L R cL cR hcL hcR hL hR hLb hRb F hF, hK]
    with ζ h1 h2
  rw [h1]
  refine (tlc_fro_sandwich _ _ _).trans ?_
  exact mul_le_mul (mul_le_mul (haL ζ) h2 (tlb_fro_nonneg _) haL0) (haR ζ) (tlb_opNorm_nonneg _)
    (mul_nonneg haL0 hK0)

/-- Conditional second moment of `e` from a pointwise bound `|e| ≤ D |a|`. -/
private lemma tlc_cond_sq (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω)
    (e a : Ω → ℝ) (D K : ℝ) (hD : 0 ≤ D) (hK0 : 0 ≤ K) (he : Measurable[mΩ] e)
    (hea : ∀ ω, |e ω| ≤ D * |a ω|) (ha2 : Integrable (fun ω => |a ω| ^ 2) P)
    (hK : ∀ᵐ ω ∂P, condExp G P (fun ω' => |a ω'| ^ 2) ω ≤ K ^ 2) :
    ∀ᵐ ζ ∂P, Real.sqrt (condExp G P (fun ω => e ω ^ 2) ζ) ≤ D * K := by
  have hle : ∀ ω, e ω ^ 2 ≤ D ^ 2 * |a ω| ^ 2 := fun ω => by
    rw [← sq_abs (e ω)]
    have := pow_le_pow_left₀ (abs_nonneg _) (hea ω) 2
    linarith [this, show (D * |a ω|) ^ 2 = D ^ 2 * |a ω| ^ 2 by ring]
  have hg : Integrable (fun ω => D ^ 2 * |a ω| ^ 2) P := ha2.const_mul (D ^ 2)
  have hI : Integrable (fun ω => e ω ^ 2) P := by
    refine Integrable.mono' hg (he.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hle ω
  have hc := condExp_mono (m := G) hI hg (Filter.Eventually.of_forall hle)
  have hsc : condExp G P (fun ω => D ^ 2 * |a ω| ^ 2) =ᵐ[P]
      fun ζ => D ^ 2 * condExp G P (fun ω => |a ω| ^ 2) ζ := by
    have := condExp_smul (μ := P) (D ^ 2) (fun ω => |a ω| ^ 2) G
    simpa [Pi.smul_def, smul_eq_mul] using this
  filter_upwards [hc, hsc, hK] with ζ h1 h2 h3
  have h4 : condExp G P (fun ω => e ω ^ 2) ζ ≤ D ^ 2 * K ^ 2 := by
    have h2' : condExp G P (fun ω => D ^ 2 * |a ω| ^ 2) ζ =
        D ^ 2 * condExp G P (fun ω => |a ω| ^ 2) ζ := h2
    rw [h2'] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))
  calc Real.sqrt (condExp G P (fun ω => e ω ^ 2) ζ) ≤ Real.sqrt (D ^ 2 * K ^ 2) :=
        Real.sqrt_le_sqrt h4
    _ = D * K := by
        rw [show D ^ 2 * K ^ 2 = (D * K) ^ 2 by ring, Real.sqrt_sq (mul_nonneg hD hK0)]



/-- `L²` membership from a pointwise domination by an `L²` function. -/
private lemma tlc_memLp2 (P : Measure Ω) (e a : Ω → ℝ) (D : ℝ) (he : Measurable[mΩ] e)
    (hea : ∀ ω, |e ω| ≤ D * |a ω|) (ha2 : Integrable (fun ω => |a ω| ^ 2) P) : MemLp e 2 P := by
  have hle : ∀ ω, e ω ^ 2 ≤ D ^ 2 * |a ω| ^ 2 := fun ω => by
    rw [← sq_abs (e ω)]
    have := pow_le_pow_left₀ (abs_nonneg _) (hea ω) 2
    linarith [this, show (D * |a ω|) ^ 2 = D ^ 2 * |a ω| ^ 2 by ring]
  refine (memLp_two_iff_integrable_sq he.aestronglyMeasurable).2 ?_
  refine Integrable.mono' (ha2.const_mul (D ^ 2)) (he.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hle ω

end TlHelpers

section TlMean
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma tl_mean_tower (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω)
    (hG : G ≤ mΩ) {m n : ℕ} (F : Ω → Mat m n) :
    @Muon.mean Ω mΩ _ _ P F = @Muon.mean Ω mΩ _ _ P (Muon.Foundations.condExpMat G P F) := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply, Muon.Foundations.condExpMat_apply]
  exact (integral_condExp hG).symm

private lemma tl_mean_congr (P : Measure Ω) {m n : ℕ} (F F' : Ω → Mat m n)
    (h : ∀ᵐ ω ∂P, F ω = F' ω) : Muon.mean P F = Muon.mean P F' := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply]
  exact integral_congr_ae (h.mono fun ω hω => by simp only [hω])

private lemma tl_mean_smul (P : Measure Ω) {m n : ℕ} (c : ℝ) (F : Ω → Mat m n) :
    Muon.mean P (fun ω => c • F ω) = c • Muon.mean P F := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact integral_const_mul _ _

private lemma tl_mean_add (P : Measure Ω) {m n : ℕ} (F F' : Ω → Mat m n)
    (hF : ∀ i k, Integrable (fun ω => F ω i k) P) (hF' : ∀ i k, Integrable (fun ω => F' ω i k) P) :
    Muon.mean P (fun ω => F ω + F' ω) = Muon.mean P F + Muon.mean P F' := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply, Matrix.add_apply]
  exact integral_add (hF i k) (hF' i k)

private lemma tl_mean_sub (P : Measure Ω) {m n : ℕ} (F F' : Ω → Mat m n)
    (hF : ∀ i k, Integrable (fun ω => F ω i k) P) (hF' : ∀ i k, Integrable (fun ω => F' ω i k) P) :
    Muon.mean P (fun ω => F ω - F' ω) = Muon.mean P F - Muon.mean P F' := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply, Matrix.sub_apply]
  exact integral_sub (hF i k) (hF' i k)

private lemma tl_mean_mul_right (P : Measure Ω) {m n r : ℕ} (F : Ω → Mat m n) (A : Mat n r)
    (hF : ∀ i k, Integrable (fun ω => F ω i k) P) :
    Muon.mean P (fun ω => F ω * A) = Muon.mean P F * A := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply, Matrix.mul_apply]
  rw [integral_finsetSum _ (fun l _ => (hF i l).mul_const _)]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact integral_mul_const _ _

end TlMean

section TlFacts
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma tl_indep {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    sigmaOthers F S t j ≤ mΩ ∧
    Indep (MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance)
      (sigmaOthers F S t j) P := by
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hX : Measurable X := S.meas _ _
  have hG : sigmaOthers F S t j ≤ mΩ := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  refine ⟨hG, ?_⟩
  have hind : Indep (sigmaOthers F S t j) (MeasurableSpace.comap X inferInstance) P := by
    have hind0 := (iIndepFun_iff_iIndep
      (fun _ : ℤ × Fin B => (inferInstance : MeasurableSpace (Vec m × Vec n)))
      (fun q : ℤ × Fin B => fun ω => S.zw q.1 q.2 ω) P).mp S.indep
    have hdisj : Disjoint {q : ℤ × Fin B | q ≠ (t + 1 - (j : ℤ), slotOne F.hB)}
        ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B)) := by
      rw [Set.disjoint_singleton_right]; exact fun h => h rfl
    have key := indep_iSup_of_disjoint (fun q : ℤ × Fin B => (S.meas q.1 q.2).comap_le) hind0 hdisj
    have hB' : MeasurableSpace.comap X inferInstance ≤
        ⨆ i ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B)),
          MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance :=
      le_iSup₂ (f := fun i (_ : i ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B))) =>
        MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance)
        (t + 1 - (j : ℤ), slotOne F.hB) (Set.mem_singleton _)
    exact indep_of_indep_of_le_right key hB'
  exact hind.symm

end TlFacts

section TlFacts2
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma tl_sqrt_le (P : Measure Ω) (G : MeasurableSpace Ω) (e : Ω → ℝ) (y : ℝ)
    (hc : ∀ᵐ ζ ∂P, condExp G P (fun ω => |e ω| ^ 2) ζ ≤ y ^ 2) :
    ∀ᵐ ζ ∂P, Real.sqrt (condExp G P (fun ω => e ω ^ 2) ζ) ≤ |y| := by
  filter_upwards [hc] with ζ h
  have e1 : (fun ω => |e ω| ^ 2) = fun ω => e ω ^ 2 := by funext ω; exact sq_abs _
  rw [e1] at h
  calc _ ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h
    _ = _ := Real.sqrt_sq_eq_abs _

end TlFacts2

section TlS
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma tl_entm {m n a b : ℕ} (G : MeasurableSpace Ω) (M0 : Ω → Mat m n)
    (hM0 : Measurable[G] M0) (Φ : Mat m n → Mat a b) (hΦ : Continuous Φ) (i : Fin a) (k : Fin b) :
    Measurable[G] (fun ω => Φ (M0 ω) i k) :=
  (((measurable_pi_apply k).comp (measurable_pi_apply i) :
    Measurable (fun f : Mat a b => f i k))).comp (hΦ.measurable.comp hM0)

private lemma tl_opNorm_one_le {n : ℕ} : opNorm (1 : Mat n n) ≤ 1 := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  simp [Matrix.toEuclideanLin]


private lemma tl_ent_eq {d d' : ℕ} (e : Ω → ℝ) (u : Ω → Vec d) (v : Ω → Vec d') (k : Fin d)
    (l : Fin d') :
    (fun ω => (e ω • Muon.outer (u ω) (v ω)) k l) = fun ω => e ω * (u ω k * v ω l) := by
  funext ω; simp [Muon.outer, Matrix.vecMulVec_apply]

private lemma tl_int_uv {m n B : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (C : Covariances m n)
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (e : Ω → ℝ) (he : MemLp e 2 P)
    (k : Fin m) (l : Fin n) :
    Integrable (fun ω => (e ω • Muon.outer (momU C B (X ω)) (momV C B (X ω))) k l) P := by
  rw [tl_ent_eq]
  exact tlc_int_outer (mΩ := mΩ) P (fun ω => (X ω).1) (fun ω => (X ω).2) (rOut C) (rIn C) _ _
    (fun ω => momU C B (X ω)) (fun ω => momV C B (X ω)) e (fun ω => rfl) (fun ω => rfl)
    (fun p q => tlb_integrable_mul (mΩ := mΩ) (tlb_memLp_cross (mΩ := mΩ) P X hX p q) he) k l

private lemma tl_int_ww {m n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (e : Ω → ℝ) (he : MemLp e 2 P)
    (k l : Fin n) :
    Integrable (fun ω => (e ω • Muon.outer (X ω).2 (X ω).2) k l) P := by
  rw [tl_ent_eq]
  have h := (tlb_integrable_mul (mΩ := mΩ) (tlb_memLp_sq_snd (mΩ := mΩ) P X hX k l) he).add
    ((he.integrable one_le_two).const_mul ((1 : Mat n n) k l))
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply]
  ring

private lemma tl_int_uu {m n B : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (C : Covariances m n)
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (e : Ω → ℝ) (he : MemLp e 2 P)
    (k l : Fin n) :
    Integrable (fun ω => (e ω • Muon.outer (momV C B (X ω)) (momV C B (X ω))) k l) P := by
  rw [tl_ent_eq]
  refine tlc_int_outer (mΩ := mΩ) P (fun ω => (X ω).2) (fun ω => (X ω).2) (rIn C) (rIn C) _ _
    (fun ω => momV C B (X ω)) (fun ω => momV C B (X ω)) e (fun ω => rfl) (fun ω => rfl)
    (fun p q => ?_) k l
  have h := (tlb_integrable_mul (mΩ := mΩ) (tlb_memLp_sq_snd (mΩ := mΩ) P X hX p q) he).add
    ((he.integrable one_le_two).const_mul ((1 : Mat n n) p q))
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply]
  ring

end TlS

section TlQ0
open ProbabilityTheory
open scoped MatrixOrder

private lemma tl_rIn_symm {m n : ℕ} (C : Covariances m n) : (rIn C)ᵀ = rIn C := by
  have h : (CFC.sqrt C.Sin)ᴴ = CFC.sqrt C.Sin :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma tl_rIn_sq {m n : ℕ} (C : Covariances m n) : rIn C * rIn C = C.Sin :=
  CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)

private lemma tl_B_outer_vv {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B)
    (x : Vec m × Vec n) :
    (B : ℝ) • Muon.outer (momV C B x) (momV C B x) = rIn C * Muon.outer x.2 x.2 * rIn C := by
  have hv : Matrix.vecMul x.2 (rIn C) = Matrix.mulVec (rIn C) x.2 := by
    rw [← Matrix.vecMul_transpose, tl_rIn_symm]
  have h1 : rIn C * Muon.outer x.2 x.2 * rIn C =
      Muon.outer (Matrix.mulVec (rIn C) x.2) (Matrix.mulVec (rIn C) x.2) := by
    rw [Muon.outer, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]
  rw [h1]
  unfold momV
  ext i k
  simp only [Matrix.smul_apply, smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have haa : (B : ℝ) * ((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hBr.le]; exact mul_inv_cancel₀ hBr.ne'
  calc (B : ℝ) * ((Real.sqrt (B : ℝ))⁻¹ * (rIn C *ᵥ x.2) i * ((Real.sqrt (B : ℝ))⁻¹ * (rIn C *ᵥ x.2) k))
      = ((B : ℝ) * ((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹)) *
        ((rIn C *ᵥ x.2) i * (rIn C *ᵥ x.2) k) := by ring
    _ = _ := by rw [haa, one_mul]

end TlQ0

section PeFacts
open ProbabilityTheory

private theorem pe_facts (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), 0 ≤ w j → w j ≤ 1 →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, s0 ≤ s →
        (∀ ω, 0 ≤ delAlpha2 w F S t j s ω) ∧
        Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance ⊔
          sigmaOthers F S t j] (delAlpha1 w F S t j s) ∧
        Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance ⊔
          sigmaOthers F S t j] (delAlpha2 w F S t j s) ∧
        MemLp (delAlpha1 w F S t j s) 2 P ∧ MemLp (delAlpha2 w F S t j s) 2 P ∧
        (∀ᵐ ζ ∂P, Real.sqrt (condExp (sigmaOthers F S t j) P
          (fun ω => delAlpha1 w F S t j s ω ^ 2) ζ) ≤ Cc * w j) ∧
        (∀ᵐ ζ ∂P, Real.sqrt (condExp (sigmaOthers F S t j) P
          (fun ω => delAlpha2 w F S t j s ω ^ 2) ζ) ≤ Cc * w j ^ 2 / s) ∧
        Integrable (delAlpha2 w F S t j s) P ∧
        (∀ᵐ ζ ∂P, condExp (sigmaOthers F S t j) P (delAlpha2 w F S t j s) ζ ≤ Cc * w j ^ 2 / s) := by
  obtain ⟨C1, hC1⟩ := lem_app_drift_coeffmoments 1 le_rfl s0 hs0 CS γ hγ
  obtain ⟨C2, hC2⟩ := lem_app_drift_coeffmoments 2 (by norm_num) s0 hs0 CS γ hγ
  refine ⟨|C1| + |C2|, by positivity, ?_⟩
  intro Ω inst m n B P _ F S t j w hw0 hw1 hCo hCi hm hn s hs
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hM0 := tl_meas_del w F S t j
  obtain ⟨-, -, -, ⟨i2a, c2a⟩⟩ :=
    hC1 Ω m n B P F S t j (delBufAge w F S t j) (w j) hCo hCi hm hn hw0 hw1 hM0 s hs
  obtain ⟨hnn, ⟨i1, c1⟩, -, ⟨i2, c2⟩⟩ :=
    hC2 Ω m n B P F S t j (delBufAge w F S t j) (w j) hCo hCi hm hn hw0 hw1 hM0 s hs
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hX : Measurable X := S.meas _ _
  obtain ⟨hG, -⟩ := tl_indep F S t j
  have hGc : MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j ≤ inst :=
    sup_le hX.comap_le hG
  have hXc : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j] X :=
    (comap_measurable X).mono le_sup_left le_rfl
  have hM0c : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (delBufAge w F S t j) := hM0.mono le_sup_right le_rfl
  have hdm : Measurable (fun x : Vec m × Vec n => resid F.A x) := by unfold resid; fun_prop
  have hUm : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => momU F.C B (X ω)) := by
    have : Measurable (momU F.C B : Vec m × Vec n → Vec m) := by unfold momU; fun_prop
    exact this.comp hXc
  have hVm : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => momV F.C B (X ω)) := by
    have : Measurable (momV F.C B : Vec m × Vec n → Vec n) := by unfold momV; fun_prop
    exact this.comp hXc
  have hDm : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => w j * resid F.A (X ω)) := (hdm.comp hXc).const_mul (w j)
  have hq : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => (delBufAge w F S t j ω, w j * resid F.A (X ω), momU F.C B (X ω),
        momV F.C B (X ω))) :=
    hM0c.prodMk (hDm.prodMk (hUm.prodMk hVm))
  obtain ⟨c1', c2', -⟩ := tlc_alpha_cont (m := m) (n := n) s hspos
  have hA1 : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (delAlpha1 w F S t j s) := c1'.measurable.comp hq
  have hA2 : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (delAlpha2 w F S t j s) := c2'.measurable.comp hq
  have hn2 : ∀ ω, 0 ≤ delAlpha2 w F S t j s ω := hnn
  have L1 : MemLp (delAlpha1 w F S t j s) 2 P :=
    tlc_memLp2 P _ (delAlpha1 w F S t j s) 1 (hA1.mono hGc le_rfl) (fun ω => by rw [one_mul]) i1
  have L2 : MemLp (delAlpha2 w F S t j s) 2 P :=
    tlc_memLp2 P _ (delAlpha2 w F S t j s) 1 (hA2.mono hGc le_rfl) (fun ω => by rw [one_mul]) i2
  have hCc0 : 0 ≤ |C1| + |C2| := by positivity
  refine ⟨hn2, hA1, hA2, L1, L2, ?_, ?_, ?_, ?_⟩
  · filter_upwards [tl_sqrt_le P (sigmaOthers F S t j) (delAlpha1 w F S t j s) (C2 * w j) c1]
      with ζ h
    refine h.trans ?_
    rw [abs_mul, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C1]) hw0
  · filter_upwards [tl_sqrt_le P (sigmaOthers F S t j) (delAlpha2 w F S t j s) (C2 * w j ^ 2 / s) c2]
      with ζ h
    refine h.trans ?_
    have hw2 : 0 ≤ w j ^ 2 := sq_nonneg _
    rw [abs_div, abs_mul, abs_of_nonneg hw2, abs_of_pos hspos, mul_div_assoc]
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C1]) (by positivity)
  · exact L2.integrable one_le_two
  · have e2 : (fun ω => |delAlpha2 w F S t j s ω| ^ 1) = delAlpha2 w F S t j s := by
      funext ω; rw [pow_one, abs_of_nonneg (hn2 ω)]
    have c2b : ∀ᵐ ζ ∂P, condExp (sigmaOthers F S t j) P
        (fun ω => |delAlpha2 w F S t j s ω| ^ 1) ζ ≤ (C1 * w j ^ 2 / s) ^ 1 := c2a
    rw [e2] at c2b
    filter_upwards [c2b] with ζ h
    refine h.trans ?_
    rw [pow_one, mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self C1, abs_nonneg C2]) (by positivity)

end PeFacts

section PeCalc
open scoped Matrix.Norms.L2Operator

/-! ### Calculus of the replacement functions `ψ_x`, `f_x` -/

private lemma gc_den_pos {x : ℝ} (hx : 0 ≤ x) (d : ℝ) : 0 < 1 + x * d ^ 2 := by
  have := mul_nonneg hx (sq_nonneg d); linarith

private lemma gc_ratio {x : ℝ} (hx : 0 ≤ x) {N N' : ℝ → ℝ} (k : ℕ)
    (hN : ∀ d, HasDerivAt N (N' d) d) (d : ℝ) :
    HasDerivAt (fun d => N d / (1 + x * d ^ 2) ^ k)
      ((N' d * (1 + x * d ^ 2) - N d * (k * (2 * x * d))) / (1 + x * d ^ 2) ^ (k + 1)) d := by
  have hg := gc_den_pos hx d
  have h1 : HasDerivAt (fun d : ℝ => d ^ 2) (2 * d) d := by simpa using hasDerivAt_pow 2 d
  have h2 : HasDerivAt (fun d : ℝ => 1 + x * d ^ 2) (x * (2 * d)) d :=
    (h1.const_mul x).const_add 1
  have h3 := h2.pow k
  have h4 := (hN d).div h3 (pow_pos hg k).ne'
  refine h4.congr_deriv ?_
  simp only [Pi.pow_apply]
  generalize hG : 1 + x * d ^ 2 = G at *
  have hG0 : G ≠ 0 := hg.ne'
  rcases k with _ | k
  · simp
    field_simp
  · rw [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

/-- ψ_x derivatives. -/
private lemma gc_psi_eq {x : ℝ} : psiX x = fun d => d ^ 2 / (1 + x * d ^ 2) ^ 1 := by
  funext d; simp [psiX]

private lemma gc_psi1 {x : ℝ} (hx : 0 ≤ x) : deriv (psiX x) = fun d => 2 * d / (1 + x * d ^ 2) ^ 2 := by
  funext d
  rw [gc_psi_eq]
  have := gc_ratio hx (N := fun d => d ^ 2) (N' := fun d => 2 * d) 1
    (fun d => by simpa using hasDerivAt_pow 2 d) d
  rw [this.deriv]
  have hg := gc_den_pos hx d
  field_simp
  ring

private lemma gc_psi2 {x : ℝ} (hx : 0 ≤ x) :
    deriv (deriv (psiX x)) = fun d => (2 - 6 * x * d ^ 2) / (1 + x * d ^ 2) ^ 3 := by
  rw [gc_psi1 hx]
  funext d
  have := gc_ratio hx (N := fun d => 2 * d) (N' := fun d => 2) 2
    (fun d => by simpa using (hasDerivAt_id d).const_mul 2) d
  rw [this.deriv]
  have hg := gc_den_pos hx d
  field_simp
  ring


private lemma gc_f_eq {x : ℝ} : fX x = fun d => d / (1 + x * d ^ 2) ^ 1 := by
  funext d; simp [fX]

private lemma gc_f1 {x : ℝ} (hx : 0 ≤ x) :
    deriv (fX x) = fun d => (1 - x * d ^ 2) / (1 + x * d ^ 2) ^ 2 := by
  funext d
  rw [gc_f_eq]
  have := gc_ratio hx (N := fun d => d) (N' := fun d => 1) 1 (fun d => hasDerivAt_id d) d
  rw [this.deriv]
  have hg := gc_den_pos hx d
  field_simp
  ring

private lemma gc_f2 {x : ℝ} (hx : 0 ≤ x) :
    deriv (deriv (fX x)) = fun d => (-6 * x * d + 2 * x ^ 2 * d ^ 3) / (1 + x * d ^ 2) ^ 3 := by
  rw [gc_f1 hx]
  funext d
  have := gc_ratio hx (N := fun d => 1 - x * d ^ 2) (N' := fun d => -(2 * x * d)) 2
    (fun d => by
      have h1 : HasDerivAt (fun d : ℝ => d ^ 2) (2 * d) d := by simpa using hasDerivAt_pow 2 d
      have := ((h1.const_mul x).const_sub 1)
      convert this using 1; ring) d
  rw [this.deriv]
  have hg := gc_den_pos hx d
  field_simp
  ring

private lemma gc_f3 {x : ℝ} (hx : 0 ≤ x) :
    deriv (deriv (deriv (fX x))) =
      fun d => (-6 * x + 36 * x ^ 2 * d ^ 2 - 6 * x ^ 3 * d ^ 4) / (1 + x * d ^ 2) ^ 4 := by
  rw [gc_f2 hx]
  funext d
  have := gc_ratio hx (N := fun d => -6 * x * d + 2 * x ^ 2 * d ^ 3)
    (N' := fun d => -6 * x + 6 * x ^ 2 * d ^ 2) 3
    (fun d => by
      have h1 : HasDerivAt (fun d : ℝ => d ^ 3) (3 * d ^ 2) d := by simpa using hasDerivAt_pow 3 d
      have := ((hasDerivAt_id d).const_mul (-6 * x)).add (h1.const_mul (2 * x ^ 2))
      convert this using 1
      · funext y; simp
      · ring) d
  rw [this.deriv]
  have hg := gc_den_pos hx d
  field_simp
  ring

private lemma gc_psi_hyp {x : ℝ} (hx : 0 ≤ x) :
    ContDiff ℝ 2 (psiX x) ∧
      (∀ j : ℕ, j ≤ 2 → ∃ (K : ℝ) (k : ℕ), ∀ d : ℝ, |iteratedDeriv j (psiX x) d| ≤ K * (1 + |d| ^ k)) ∧
      ∀ d : ℝ, |iteratedDeriv 2 (psiX x) d| ≤ 6 := by
  have hcd : ContDiff ℝ 2 (psiX x) := by
    have : psiX x = fun d => d ^ 2 / (1 + x * d ^ 2) := by funext d; rfl
    rw [this]
    exact ContDiff.div (contDiff_id.pow 2) (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2)))
      (fun d => (gc_den_pos hx d).ne')
  have hi2 : iteratedDeriv 2 (psiX x) = deriv (deriv (psiX x)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hb2 : ∀ d : ℝ, |iteratedDeriv 2 (psiX x) d| ≤ 6 := by
    intro d
    rw [hi2, gc_psi2 hx]
    have hg := gc_den_pos hx d
    set y := x * d ^ 2 with hy
    have hy0 : 0 ≤ y := mul_nonneg hx (sq_nonneg d)
    have e : 6 * x * d ^ 2 = 6 * y := by rw [hy]; ring
    show |(2 - 6 * x * d ^ 2) / (1 + y) ^ 3| ≤ 6
    rw [e, abs_div, abs_of_pos (pow_pos hg 3), div_le_iff₀ (pow_pos hg 3)]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg y, mul_nonneg hy0 (sq_nonneg y), pow_nonneg hy0 3]
  refine ⟨hcd, fun j hj => ?_, hb2⟩
  interval_cases j
  · refine ⟨1, 2, fun d => ?_⟩
    rw [iteratedDeriv_zero]
    have hg := gc_den_pos hx d
    show |d ^ 2 / (1 + x * d ^ 2)| ≤ _
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hg]
    nlinarith [mul_nonneg hx (sq_nonneg d), sq_nonneg d, abs_nonneg d, sq_abs d,
      mul_nonneg (mul_nonneg hx (sq_nonneg d)) (sq_nonneg d)]
  · refine ⟨2, 1, fun d => ?_⟩
    rw [iteratedDeriv_one, gc_psi1 hx]
    have hg := gc_den_pos hx d
    show |2 * d / (1 + x * d ^ 2) ^ 2| ≤ _
    rw [abs_div, abs_of_pos (pow_pos hg 2), div_le_iff₀ (pow_pos hg 2), abs_mul]
    have h1 : 1 ≤ (1 + x * d ^ 2) ^ 2 := by nlinarith [mul_nonneg hx (sq_nonneg d)]
    simp only [abs_two, pow_one]
    nlinarith [abs_nonneg d]
  · exact ⟨6, 0, fun d => by simpa using (hb2 d).trans (by norm_num)⟩


private lemma gc_f_hyp {x : ℝ} (hx : 0 ≤ x) :
    ContDiff ℝ 3 (fX x) ∧
      (∀ j : ℕ, j ≤ 3 → ∃ (K : ℝ) (k : ℕ), ∀ d : ℝ, |iteratedDeriv j (fX x) d| ≤ K * (1 + |d| ^ k)) ∧
      (∀ d : ℝ, |deriv (fX x) d| ≤ 1) ∧ ∀ d : ℝ, |iteratedDeriv 3 (fX x) d| ≤ 36 * x := by
  have hcd : ContDiff ℝ 3 (fX x) := by
    have : fX x = fun d => d / (1 + x * d ^ 2) := by funext d; rfl
    rw [this]
    exact ContDiff.div contDiff_id (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2)))
      (fun d => (gc_den_pos hx d).ne')
  have hi2 : iteratedDeriv 2 (fX x) = deriv (deriv (fX x)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hi3 : iteratedDeriv 3 (fX x) = deriv (deriv (deriv (fX x))) := by
    rw [iteratedDeriv_succ, hi2]
  have hb1 : ∀ d : ℝ, |deriv (fX x) d| ≤ 1 := by
    intro d
    rw [gc_f1 hx]
    have hg := gc_den_pos hx d
    set y := x * d ^ 2 with hy
    have hy0 : 0 ≤ y := mul_nonneg hx (sq_nonneg d)
    show |(1 - y) / (1 + y) ^ 2| ≤ 1
    rw [abs_div, abs_of_pos (pow_pos hg 2), div_le_iff₀ (pow_pos hg 2), one_mul, abs_le]
    constructor <;> nlinarith [sq_nonneg y]
  have hb3 : ∀ d : ℝ, |iteratedDeriv 3 (fX x) d| ≤ 36 * x := by
    intro d
    rw [hi3, gc_f3 hx]
    have hg := gc_den_pos hx d
    set y := x * d ^ 2 with hy
    have hy0 : 0 ≤ y := mul_nonneg hx (sq_nonneg d)
    have e : (-6 * x + 36 * x ^ 2 * d ^ 2 - 6 * x ^ 3 * d ^ 4) = x * (-6 + 36 * y - 6 * y ^ 2) := by
      rw [hy]; ring
    show |(-6 * x + 36 * x ^ 2 * d ^ 2 - 6 * x ^ 3 * d ^ 4) / (1 + y) ^ 4| ≤ 36 * x
    rw [e, abs_div, abs_of_pos (pow_pos hg 4), div_le_iff₀ (pow_pos hg 4), abs_mul,
      abs_of_nonneg hx]
    have h5 : |-6 + 36 * y - 6 * y ^ 2| ≤ 36 * (1 + y) ^ 4 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg y, mul_nonneg hy0 (sq_nonneg y), pow_nonneg hy0 3,
        pow_nonneg hy0 4]
    nlinarith [mul_le_mul_of_nonneg_left h5 hx]
  refine ⟨hcd, fun j hj => ?_, hb1, hb3⟩
  interval_cases j
  · refine ⟨1, 1, fun d => ?_⟩
    rw [iteratedDeriv_zero]
    have hg := gc_den_pos hx d
    show |d / (1 + x * d ^ 2)| ≤ _
    rw [abs_div, abs_of_pos hg, div_le_iff₀ hg]
    nlinarith [abs_nonneg d, mul_nonneg hx (sq_nonneg d), mul_nonneg (abs_nonneg d) (mul_nonneg hx (sq_nonneg d))]
  · exact ⟨1, 0, fun d => by rw [iteratedDeriv_one]; have := hb1 d; simp; linarith⟩
  · refine ⟨6 * x + 2 * x ^ 2, 3, fun d => ?_⟩
    rw [hi2, gc_f2 hx]
    have hg := gc_den_pos hx d
    show |(-6 * x * d + 2 * x ^ 2 * d ^ 3) / (1 + x * d ^ 2) ^ 3| ≤ _
    have hg3 : 1 ≤ (1 + x * d ^ 2) ^ 3 := one_le_pow₀ (by nlinarith [mul_nonneg hx (sq_nonneg d)])
    rw [abs_div, abs_of_pos (pow_pos hg 3), div_le_iff₀ (pow_pos hg 3)]
    have a1 : |-6 * x * d| = 6 * x * |d| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hx]; norm_num
    have a2 : |2 * x ^ 2 * d ^ 3| = 2 * x ^ 2 * |d| ^ 3 := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hx]; norm_num
    have h6 : |-6 * x * d + 2 * x ^ 2 * d ^ 3| ≤ 6 * x * |d| + 2 * x ^ 2 * |d| ^ 3 := by
      refine (abs_add_le _ _).trans ?_
      rw [a1, a2]
    have hd : |d| ≤ 1 + |d| ^ 3 := by
      have := abs_nonneg d
      nlinarith [sq_nonneg (|d| - 1), sq_nonneg |d|]
    have hK : 0 ≤ 6 * x + 2 * x ^ 2 := by positivity
    have hd3 : 0 ≤ |d| ^ 3 := by positivity
    calc |-6 * x * d + 2 * x ^ 2 * d ^ 3| ≤ 6 * x * |d| + 2 * x ^ 2 * |d| ^ 3 := h6
      _ ≤ (6 * x + 2 * x ^ 2) * (1 + |d| ^ 3) := by
          nlinarith [mul_nonneg hx hd3, mul_nonneg (sq_nonneg x) hd3, mul_le_mul_of_nonneg_left hd hx]
      _ ≤ (6 * x + 2 * x ^ 2) * (1 + |d| ^ 3) * (1 + x * d ^ 2) ^ 3 :=
          le_mul_of_one_le_right (by positivity) hg3
  · refine ⟨36 * x, 0, fun d => ?_⟩
    rw [pow_zero]
    nlinarith [hb3 d, hx]



end PeCalc

section PeAux
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma pe_fro_eq {m n : ℕ} (a : Mat m n) :
    fro a = Real.sqrt (∑ x : Fin m × Fin n, a x.1 x.2 ^ 2) := by
  unfold fro
  simp [Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]

private lemma pe_inner_le {m n : ℕ} (a b : Mat m n) :
    ∑ i, ∑ k, a i k * b i k ≤ fro a * fro b := by
  rw [pe_fro_eq, pe_fro_eq]
  have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m × Fin n))
    (fun x => a x.1 x.2) (fun x => b x.1 x.2)
  simpa [Fintype.sum_prod_type] using this

private lemma pe_mean_fro_le_int (P : Measure Ω) [IsProbabilityMeasure P] {m n : ℕ}
    (F : Ω → Mat m n) (hF : ∀ i k, Integrable (fun ω => F ω i k) P) (ψ : Ω → ℝ)
    (hψ : Integrable ψ P) (hc : ∀ᵐ ω ∂P, fro (F ω) ≤ ψ ω) :
    fro (Muon.mean P F) ≤ ∫ ω, ψ ω ∂P := by
  set E := Muon.mean P F with hE
  have hint : ∀ i k, Integrable (fun ω => E i k * F ω i k) P := fun i k => (hF i k).const_mul _
  have h1 : fro E ^ 2 = ∫ ω, ∑ i, ∑ k, E i k * F ω i k ∂P := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hint i k))]
    rw [tlb_fro_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun k _ => hint i k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    simp only [hE, Muon.mean, Matrix.of_apply]
    ring
  have h2 : ∫ ω, ∑ i, ∑ k, E i k * F ω i k ∂P ≤ ∫ ω, fro E * ψ ω ∂P := by
    refine integral_mono_ae (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
      hint i k) (hψ.const_mul _) ?_
    filter_upwards [hc] with ω hω
    exact (pe_inner_le E (F ω)).trans (mul_le_mul_of_nonneg_left hω (tlb_fro_nonneg _))
  rw [integral_const_mul] at h2
  have h3 : fro E ^ 2 ≤ fro E * ∫ ω, ψ ω ∂P := h1 ▸ h2
  have hI0 : 0 ≤ ∫ ω, ψ ω ∂P := integral_nonneg_of_ae (by
    filter_upwards [hc] with ω hω
    exact (tlb_fro_nonneg _).trans hω)
  by_contra h
  push Not at h
  nlinarith [tlb_fro_nonneg E]

private lemma pe_int_sqrt_condExp (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω)
    (hG : G ≤ mΩ) (e : Ω → ℝ) (he2 : MemLp e 2 P) :
    Integrable (fun ζ => Real.sqrt (condExp G P (fun ω => e ω ^ 2) ζ)) P ∧
    ∫ ζ, Real.sqrt (condExp G P (fun ω => e ω ^ 2) ζ) ∂P ≤ Real.sqrt (∫ ω, e ω ^ 2 ∂P) := by
  set Y : Ω → ℝ := condExp G P (fun ω => e ω ^ 2) with hY
  have hY0 : 0 ≤ᵐ[P] Y := condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg (e ω))
  have hYint : Integrable Y P := integrable_condExp
  have hYm : AEStronglyMeasurable[mΩ] Y P :=
    ((stronglyMeasurable_condExp (m := G) (f := fun ω => e ω ^ 2) (μ := P)).mono hG).aestronglyMeasurable
  have hφm : AEStronglyMeasurable[mΩ] (fun ζ => Real.sqrt (Y ζ)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hYm
  have hsq : (fun ζ => Real.sqrt (Y ζ) ^ 2) =ᵐ[P] Y := by
    filter_upwards [hY0] with ζ h
    exact Real.sq_sqrt h
  have hφ2 : MemLp (fun ζ => Real.sqrt (Y ζ)) 2 P := by
    rw [memLp_two_iff_integrable_sq hφm]
    exact hYint.congr hsq.symm
  have hφi : Integrable (fun ζ => Real.sqrt (Y ζ)) P := hφ2.integrable one_le_two
  refine ⟨hφi, ?_⟩
  have hvar := variance_nonneg (fun ζ => Real.sqrt (Y ζ)) P
  rw [variance_eq_sub hφ2] at hvar
  have hint2 : ∫ ζ, (fun ζ => Real.sqrt (Y ζ)) ζ ^ 2 ∂P = ∫ ω, e ω ^ 2 ∂P := by
    simp only [Pi.pow_apply]
    rw [integral_congr_ae hsq]
    exact integral_condExp hG
  have h1 : (∫ ζ, Real.sqrt (Y ζ) ∂P) ^ 2 ≤ ∫ ω, e ω ^ 2 ∂P := by
    have := hvar
    simp only [Pi.pow_apply] at this
    rw [show (∫ ζ, (fun ζ => Real.sqrt (Y ζ)) ζ ^ 2 ∂P) = ∫ ω, e ω ^ 2 ∂P from hint2] at this
    linarith
  exact (le_abs_self _).trans (Real.abs_le_sqrt h1)

private lemma pe_sqrt_int_le {f : Ω → ℝ} (P : Measure Ω) (hf : MemLp f 2 P) {K : ℝ} (hK : 0 ≤ K)
    (h : eLpNorm f 2 P ≤ ENNReal.ofReal K) : Real.sqrt (∫ ω, f ω ^ 2 ∂P) ≤ K := by
  have h1 := hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have h2 : ∫ ω, ‖f ω‖ ^ (ENNReal.toReal 2) ∂P = ∫ ω, f ω ^ 2 ∂P := by
    simp [Real.norm_eq_abs, sq_abs]
  rw [h1, h2] at h
  have h3 : (∫ ω, f ω ^ 2 ∂P) ^ (ENNReal.toReal 2)⁻¹ ≤ K := by
    have := (ENNReal.ofReal_le_ofReal_iff hK).1 h
    simpa using this
  simpa [Real.sqrt_eq_rpow] using h3

end PeAux

section PeSrc
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private theorem pe_src_bessel {m n B : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (w : ℕ → ℝ) (CS : ℝ)
    (hCo : opNorm F.C.Sout ≤ CS) (hCi : opNorm F.C.Sin ≤ CS) {s : ℝ} (hs : 0 < s)
    (e : Ω → ℝ)
    (he : Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance ⊔
      sigmaOthers F S t j] e)
    (he2 : MemLp e 2 P) :
    (∀ i k, Integrable (fun ω => (e ω • (Rs (delBufAge w F S t j ω) s *
        outer (ageU F S t j ω) (ageV F S t j ω))) i k) P) ∧
    fro ((B : ℝ) • Muon.mean P (fun ω => e ω • (Rs (delBufAge w F S t j ω) s *
        outer (ageU F S t j ω) (ageV F S t j ω)))) ≤ CS / s * Real.sqrt (∫ ω, e ω ^ 2 ∂P) := by
  have hB : 0 < B := F.hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCS0 : 0 ≤ CS := (tlb_opNorm_nonneg _).trans hCo
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hlaw : P.map X = gaussPair m n := S.law _ _
  obtain ⟨hG, hindc⟩ := tl_indep F S t j
  have hM0 := tl_meas_del w F S t j
  have hR0m : ∀ i k, Measurable[sigmaOthers F S t j]
      (fun ω => Rs (delBufAge w F S t j ω) s i k) :=
    fun i k => tl_entm (sigmaOthers F S t j) _ hM0 (fun M => Rs M s) (tlc_Rs_continuous s hs) i k
  have hRb : ∀ ω, opNorm (Rs (delBufAge w F S t j ω) s) ≤ 1 / s :=
    fun ω => (lem_app_de_resolvent _ s hs).1
  have hF' := tl_int_uv (B := B) P F.C X hlaw e he2
  have hmeas1 : ∀ i k, Measurable[sigmaOthers F S t j] (fun ω => (1 : Mat n n) i k) :=
    fun i k => measurable_const
  have hb1 : ∀ (ω : Ω) i k, |(1 : Mat n n) i k| ≤ 1 := fun ω i k =>
    (tlc_abs_entry_le _ i k).trans tl_opNorm_one_le
  have hLb : ∀ ω i k, |Rs (delBufAge w F S t j ω) s i k| ≤ 1 / s :=
    fun ω i k => (tlc_abs_entry_le _ i k).trans (hRb ω)
  have hrew' : ∀ ω, e ω •
      (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω)) =
      Rs (delBufAge w F S t j ω) s * (e ω •
        Muon.outer (momU F.C B (X ω)) (momV F.C B (X ω))) * (1 : Mat n n) := by
    intro ω
    rw [Matrix.mul_one, Matrix.mul_smul]
    rfl
  have hrew := funext hrew'
  have hint := tlc_int_LFR (mΩ := mΩ) P (sigmaOthers F S t j) hG
    (fun ω => Rs (delBufAge w F S t j ω) s) (fun _ => (1 : Mat n n)) (1 / s) 1 (by positivity)
    hR0m hmeas1 hLb hb1 _ hF'
  refine ⟨fun i k => ?_, ?_⟩
  · exact (hint i k).congr (Filter.Eventually.of_forall fun ω => by dsimp only; rw [hrew' ω])
  · rw [hrew]
    have hK := bessel_frob_uv (mΩ := mΩ) P F.C CS hB hCo hCi X hlaw (sigmaOthers F S t j) hG
      hindc _ he he2
    have hpull := tlc_condExpMat_pull (mΩ := mΩ) P (sigmaOthers F S t j) hG
      (fun ω => Rs (delBufAge w F S t j ω) s) (fun _ => (1 : Mat n n)) (1 / s) 1 (by positivity)
      zero_le_one hR0m hmeas1 hLb hb1 _ hF'
    obtain ⟨hsi, hsle⟩ := pe_int_sqrt_condExp P (sigmaOthers F S t j) hG e he2
    have hae : ∀ᵐ ζ ∂P, fro (Muon.Foundations.condExpMat (sigmaOthers F S t j) P (fun ω =>
        Rs (delBufAge w F S t j ω) s * (e ω • Muon.outer (momU F.C B (X ω)) (momV F.C B (X ω))) *
          (1 : Mat n n)) ζ) ≤
        1 / s * (CS / B * Real.sqrt (condExp (sigmaOthers F S t j) P (fun ω => e ω ^ 2) ζ)) * 1 := by
      filter_upwards [hpull, hK.mono fun ζ h => h.1] with ζ h1 h2
      rw [h1]
      refine (tlc_fro_sandwich _ _ _).trans ?_
      exact mul_le_mul (mul_le_mul (hRb ζ) h2 (tlb_fro_nonneg _) (by positivity))
        tl_opNorm_one_le (tlb_opNorm_nonneg _) (by positivity)
    rw [tl_mean_tower P (sigmaOthers F S t j) hG, tlb_fro_smul, abs_of_pos hBr]
    have hc := pe_mean_fro_le_int P _ (fun i k => by
      simpa only [Muon.Foundations.condExpMat_apply] using integrable_condExp) _
      (((hsi.const_mul (CS / B)).const_mul (1 / s)).mul_const 1) hae
    calc (B : ℝ) * _ ≤ (B : ℝ) * ∫ ζ, 1 / s * (CS / B * Real.sqrt (condExp (sigmaOthers F S t j) P
          (fun ω => e ω ^ 2) ζ)) * 1 ∂P := mul_le_mul_of_nonneg_left hc hBr.le
      _ = CS / s * ∫ ζ, Real.sqrt (condExp (sigmaOthers F S t j) P (fun ω => e ω ^ 2) ζ) ∂P := by
          simp only [mul_one]
          rw [integral_const_mul, integral_const_mul]
          field_simp
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left hsle ?_
          positivity

end PeSrc

section PeSrc2
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma pe_rOut_outer_rIn {m n : ℕ} (C : Covariances m n) (z : Vec m) (w : Vec n) :
    rOut C * outer z w * rIn C =
      outer (Matrix.mulVec (rOut C) z) (Matrix.mulVec (rIn C) w) := by
  have hv : Matrix.vecMul w (rIn C) = Matrix.mulVec (rIn C) w := by
    rw [← Matrix.vecMul_transpose, tl_rIn_symm]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]

private lemma pe_B_outer_uv {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B)
    (x : Vec m × Vec n) :
    (B : ℝ) • Muon.outer (momU C B x) (momV C B x) = rOut C * Muon.outer x.1 x.2 * rIn C := by
  rw [pe_rOut_outer_rIn]
  unfold momU momV
  ext i k
  simp only [Matrix.smul_apply, smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have haa : (B : ℝ) * ((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hBr.le]; exact mul_inv_cancel₀ hBr.ne'
  calc (B : ℝ) * ((Real.sqrt (B : ℝ))⁻¹ * (rOut C *ᵥ x.1) i * ((Real.sqrt (B : ℝ))⁻¹ * (rIn C *ᵥ x.2) k))
      = ((B : ℝ) * ((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹)) *
        ((rOut C *ᵥ x.1) i * (rIn C *ᵥ x.2) k) := by ring
    _ = _ := by rw [haa, one_mul]

/-- The mean of `L Y R` factorizes when `L` is `𝒢_{j1}`-measurable bounded and `Y` is a function of
the age-`j` sample. -/
private lemma pe_mean_indep_prod {m n B p q r t' : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (L : Ω → Mat p q) (Rm : Mat r t') (cL cR : ℝ) (hcL : 0 ≤ cL) (hcR : 0 ≤ cR)
    (hL : ∀ i k, Measurable[sigmaOthers F S t j] (fun ω => L ω i k)) (hLb : ∀ ω i k, |L ω i k| ≤ cL)
    (hRb : ∀ i k, |Rm i k| ≤ cR)
    (Y : Ω → Mat q r)
    (hY : ∀ i k, Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance]
      (fun ω => Y ω i k))
    (hYi : ∀ i k, Integrable (fun ω => Y ω i k) P) :
    Muon.mean P (fun ω => L ω * Y ω * Rm) = Muon.mean P L * Muon.mean P Y * Rm := by
  obtain ⟨hG, hindc⟩ := tl_indep F S t j
  have hG' : MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance ≤ mΩ :=
    (S.meas _ _).comap_le
  have hRm : ∀ i k, Measurable[sigmaOthers F S t j] (fun _ : Ω => Rm i k) := fun i k => measurable_const
  have hRb' : ∀ (ω : Ω) i k, |Rm i k| ≤ cR := fun ω i k => hRb i k
  have hpull := tlc_condExpMat_pull (mΩ := mΩ) P (sigmaOthers F S t j) hG L (fun _ => Rm) cL cR hcL
    hcR hL hRm hLb hRb' Y hYi
  have hci := Muon.Foundations.condExpMat_indep_eq (μ := P) (sigmaOthers F S t j) _ hG hG' hY hindc
  have hLi : ∀ i k, Integrable (fun ω => L ω i k) P := fun i k =>
    Integrable.of_bound (((hL i k).mono hG le_rfl).aestronglyMeasurable) cL
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hLb ω i k)
  have hLY : ∀ i k, Integrable (fun ω => (L ω * Muon.mean P Y) i k) P := by
    intro i k
    simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ fun l _ => (hLi i l).mul_const _
  rw [tl_mean_tower P (sigmaOthers F S t j) hG, tl_mean_congr P _ (fun ζ => L ζ * Muon.mean P Y * Rm)
    (by filter_upwards [hpull, hci] with ζ h1 h2; rw [h1, h2]),
    tl_mean_mul_right P _ Rm hLY]
  congr 1
  exact tl_mean_mul_right P L (Muon.mean P Y) hLi

private lemma pe_mean_map {m n : ℕ} (P : Measure Ω) (X : Ω → Vec m × Vec n) (hX : Measurable X)
    {a b : ℕ} (h : Vec m × Vec n → Mat a b) (hh : Continuous h) :
    Muon.mean P (fun ω => h (X ω)) = Muon.mean (P.map X) h := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply]
  rw [integral_map hX.aemeasurable]
  exact (((measurable_pi_apply k).comp (measurable_pi_apply i)).comp
    hh.measurable).aestronglyMeasurable

end PeSrc2

section PeSrc3
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma pe_resid_cont {m n : ℕ} (A : Mat m n) : Continuous (resid A) := by
  unfold resid dotProduct Matrix.mulVec dotProduct; fun_prop

private lemma pe_memLp_resid {m n : ℕ} {P : Measure Ω} (A : Mat m n) (hA : fro A = 1)
    (X : Ω → Vec m × Vec n) (hX : Measurable X) (hlaw : P.map X = gaussPair m n) :
    MemLp (fun ω => resid A (X ω)) 2 P := by
  have h2 := (lem_app_setup_residual_i A hA).2.1
  have hint2 : Integrable (fun p : Vec m × Vec n => resid A p ^ 2) (gaussPair m n) := by
    by_contra h
    rw [integral_undef h] at h2
    norm_num at h2
  have hm : MemLp (resid A) 2 (gaussPair m n) :=
    (memLp_two_iff_integrable_sq (pe_resid_cont A).aestronglyMeasurable).2 hint2
  rw [← hlaw] at hm
  exact (memLp_map_measure_iff (pe_resid_cont A).aestronglyMeasurable hX.aemeasurable).1 hm

end PeSrc3

section PeSrc4
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private theorem pe_src_main {m n B : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (w : ℕ → ℝ) (CS : ℝ)
    (hCo : opNorm F.C.Sout ≤ CS) (hCi : opNorm F.C.Sin ≤ CS) {s : ℝ} (hs : 0 < s)
    {c : ℝ} (hc : 0 ≤ c) {x : ℝ} (hx : 0 ≤ x) :
    fro ((B : ℝ) • Muon.mean P (fun ω => (c * fX x (ageD F S t j ω)) •
        (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))) -
      (c * ∫ p, deriv (fX x) (resid F.A p) ∂(gaussPair m n)) •
        (expDelRes w F S t j (slotOne F.hB) s * EG F)) ≤
      1 / s * CS * (c * (36 * x * opNorm F.A ^ 2)) := by
  have hB : 0 < B := F.hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCS0 : 0 ≤ CS := (tlb_opNorm_nonneg _).trans hCo
  set A := F.A with hAdef
  have hA : fro A = 1 := F.hA
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hXm : Measurable X := S.meas _ _
  have hlaw : P.map X = gaussPair m n := S.law _ _
  obtain ⟨hG, hindc⟩ := tl_indep F S t j
  have hM0 := tl_meas_del w F S t j
  obtain ⟨hcd, hpoly, hb1, hb3⟩ := gc_f_hyp hx
  have hfc : Continuous (fX x) := hcd.continuous
  set g : Vec m × Vec n → ℝ := fun p => c * fX x (resid A p) with hgdef
  have hgc : Continuous g := continuous_const.mul (hfc.comp (pe_resid_cont A))
  set Yf : Vec m × Vec n → Mat m n := fun p => g p • Muon.outer p.1 p.2 with hYfdef
  have hYc : Continuous Yf := by
    refine continuous_matrix fun i k => ?_
    simp only [hYfdef, Matrix.smul_apply, smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply]
    fun_prop
  -- the resolvent factor
  set R0 : Ω → Mat m m := fun ω => Rs (delBufAge w F S t j ω) s with hR0def
  have hR0m : ∀ i k, Measurable[sigmaOthers F S t j] (fun ω => R0 ω i k) :=
    fun i k => tl_entm (sigmaOthers F S t j) _ hM0 (fun M => Rs M s) (tlc_Rs_continuous s hs) i k
  have hRb : ∀ ω, opNorm (R0 ω) ≤ 1 / s := fun ω => (lem_app_de_resolvent _ s hs).1
  have hR0i : ∀ i k, Integrable (fun ω => R0 ω i k) P := fun i k =>
    Integrable.of_bound (((hR0m i k).mono hG le_rfl).aestronglyMeasurable) (1 / s)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact (tlc_abs_entry_le _ i k).trans (hRb ω))
  -- operator norms of the square roots
  set ro := rOut F.C with hro
  set ri := rIn F.C with hri
  have hro0 : 0 ≤ opNorm ro := tlb_opNorm_nonneg _
  have hri0 : 0 ≤ opNorm ri := tlb_opNorm_nonneg _
  have hrr : opNorm ro * opNorm ri ≤ CS := by
    have h1 : (opNorm ro * opNorm ri) ^ 2 ≤ CS ^ 2 := by
      have e1 : (opNorm ro * opNorm ro) = opNorm F.C.Sout := tlb_opNorm_rOut_mul_self F.C
      have e2 : (opNorm ri * opNorm ri) = opNorm F.C.Sin := tlb_opNorm_rIn_mul_self F.C
      calc (opNorm ro * opNorm ri) ^ 2 = (opNorm ro * opNorm ro) * (opNorm ri * opNorm ri) := by ring
        _ ≤ CS * CS := by rw [e1, e2]; exact mul_le_mul hCo hCi (tlb_opNorm_nonneg _) hCS0
        _ = CS ^ 2 := by ring
    exact le_of_sq_le_sq (by simpa using h1) hCS0 |>.trans_eq rfl
  -- the L factor
  set L : Ω → Mat m m := fun ω => R0 ω * ro with hLdef
  have hLm : ∀ i k, Measurable[sigmaOthers F S t j] (fun ω => L ω i k) := by
    intro i k
    have hc1 : Continuous (fun M : Mat m n => Rs M s * ro) :=
      (tlc_Rs_continuous s hs).matrix_mul continuous_const
    exact tl_entm (sigmaOthers F S t j) _ hM0 (fun M => Rs M s * ro) hc1 i k
  have hLb : ∀ ω i k, |L ω i k| ≤ 1 / s * opNorm ro := fun ω i k =>
    (tlc_abs_entry_le _ i k).trans ((tlb_opNorm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hRb ω) hro0))
  -- the Y factor
  have hgmem : MemLp (fun ω => g (X ω)) 2 P := by
    have hr := pe_memLp_resid (P := P) A hA X hXm hlaw
    refine (hr.norm.const_mul c).mono' ?_ ?_
    · exact (hgc.comp_aestronglyMeasurable hXm.aestronglyMeasurable)
    · refine Filter.Eventually.of_forall fun ω => ?_
      simp only [hgdef, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc]
      refine mul_le_mul_of_nonneg_left ?_ hc
      have hg := gc_den_pos hx (resid A (X ω))
      show |fX x (resid A (X ω))| ≤ ‖resid A (X ω)‖
      rw [Real.norm_eq_abs]
      unfold fX
      rw [abs_div, abs_of_pos hg, div_le_iff₀ hg]
      nlinarith [abs_nonneg (resid A (X ω)), mul_nonneg hx (sq_nonneg (resid A (X ω))),
        mul_nonneg (abs_nonneg (resid A (X ω))) (mul_nonneg hx (sq_nonneg (resid A (X ω))))]
  have hYm : ∀ i k, Measurable[MeasurableSpace.comap X inferInstance]
      (fun ω => Yf (X ω) i k) := by
    intro i k
    have hik : Measurable (fun M : Mat m n => M i k) :=
      (measurable_pi_apply k).comp (measurable_pi_apply i)
    have : Measurable (fun p : Vec m × Vec n => Yf p i k) := hik.comp hYc.measurable
    exact this.comp (comap_measurable X)
  have hYi : ∀ i k, Integrable (fun ω => Yf (X ω) i k) P := by
    intro i k
    have := tlb_integrable_mul (mΩ := mΩ) (tlb_memLp_cross (mΩ := mΩ) P X hlaw i k) hgmem
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [hYfdef, Muon.outer, Matrix.vecMulVec_apply]
    ring
  -- pointwise rewriting
  have hpt : ∀ ω, (B : ℝ) • ((c * fX x (ageD F S t j ω)) •
      (R0 ω * outer (ageU F S t j ω) (ageV F S t j ω))) = L ω * Yf (X ω) * ri := by
    intro ω
    have h1 := pe_B_outer_uv F.C B hB (X ω)
    have h2 : (B : ℝ) • ((c * fX x (ageD F S t j ω)) •
        (R0 ω * outer (ageU F S t j ω) (ageV F S t j ω))) =
        R0 ω * ((c * fX x (ageD F S t j ω)) • ((B : ℝ) • Muon.outer (momU F.C B (X ω))
          (momV F.C B (X ω)))) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, smul_comm]; rfl
    rw [h2, h1]
    simp only [hLdef, hYfdef, hgdef, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hro, hri]
    rfl
  have hmean1 : (B : ℝ) • Muon.mean P (fun ω => (c * fX x (ageD F S t j ω)) •
      (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))) =
      Muon.mean P (fun ω => L ω * Yf (X ω) * ri) := by
    rw [← tl_mean_smul]
    exact congrArg _ (funext hpt)
  have hprod := pe_mean_indep_prod P F S t j L ri (1 / s * opNorm ro) (opNorm ri)
    (by positivity) hri0 hLm hLb (fun i k => tlc_abs_entry_le _ i k) (fun ω => Yf (X ω)) hYm hYi
  have hLmean : Muon.mean P L = Muon.mean P R0 * ro := by
    exact tl_mean_mul_right P R0 ro hR0i
  have hYmean : Muon.mean P (fun ω => Yf (X ω)) = c • Muon.mean (gaussPair m n)
      (fun p => fX x (resid A p) • Muon.outer p.1 p.2) := by
    rw [pe_mean_map P X hXm Yf hYc, hlaw]
    ext i k
    simp only [Muon.mean, hYfdef, hgdef, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hmean1, hprod, hLmean, hYmean]
  set M1 := Muon.mean (gaussPair m n) (fun p => fX x (resid A p) • Muon.outer p.1 p.2) with hM1
  set jx := ∫ p, deriv (fX x) (resid A p) ∂(gaussPair m n) with hjx
  have hst := lem_app_de_stein_ii A (fX x) hcd hpoly (36 * x) hb3
  rw [hA, mul_one] at hst
  have hPj : expDelRes w F S t j (slotOne F.hB) s = Muon.mean P R0 := rfl
  set Pj := Muon.mean P R0 with hPjdef
  have halg : Pj * ro * (c • M1) * ri - (c * jx) • (Pj * EG F) =
      c • (Pj * (ro * (M1 - jx • A) * ri)) := by
    have hEG : EG F = ro * A * ri := rfl
    rw [hEG]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub,
      mul_smul, Matrix.mul_assoc]
  rw [hPj, halg, tlb_fro_smul, abs_of_nonneg hc]
  set Z := ro * (M1 - jx • A) * ri with hZ
  have hPZ : Pj * Z = Muon.mean P (fun ω => R0 ω * Z) := by
    exact (tl_mean_mul_right P R0 Z hR0i).symm
  have hfZ : fro Z ≤ CS * (36 * x * opNorm A ^ 2) := by
    refine (tlc_fro_sandwich _ _ _).trans ?_
    calc opNorm ro * fro (M1 - jx • A) * opNorm ri ≤ opNorm ro * (36 * x * opNorm A ^ 2) * opNorm ri := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hst hro0) hri0
      _ = (opNorm ro * opNorm ri) * (36 * x * opNorm A ^ 2) := by ring
      _ ≤ CS * (36 * x * opNorm A ^ 2) :=
          mul_le_mul_of_nonneg_right hrr (by positivity)
  have hPZb : fro (Pj * Z) ≤ 1 / s * (CS * (36 * x * opNorm A ^ 2)) := by
    rw [hPZ]
    refine tl_mean_fro_le P _ (fun i k => ?_) _ (Filter.Eventually.of_forall fun ω => ?_)
    · simp only [Matrix.mul_apply]
      exact integrable_finsetSum _ fun l _ => (hR0i i l).mul_const _
    · exact (tlb_fro_mul_le_left _ _).trans (mul_le_mul (hRb ω) hfZ (tlb_fro_nonneg _)
        (by positivity))
  calc c * fro (Pj * Z) ≤ c * (1 / s * (CS * (36 * x * opNorm A ^ 2))) :=
        mul_le_mul_of_nonneg_left hPZb hc
    _ = _ := by ring

end PeSrc4

section PeSrc5
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma pe_memLp_fX {m n : ℕ} {P : Measure Ω} (A : Mat m n) (hA : fro A = 1)
    (X : Ω → Vec m × Vec n) (hX : Measurable X) (hlaw : P.map X = gaussPair m n) (c : ℝ)
    {x : ℝ} (hx : 0 ≤ x) :
    MemLp (fun ω => c * fX x (resid A (X ω))) 2 P := by
  obtain ⟨hcd, -, -, -⟩ := gc_f_hyp hx
  have hfc : Continuous (fX x) := hcd.continuous
  have hr := pe_memLp_resid (P := P) A hA X hX hlaw
  refine (hr.norm.const_mul |c|).mono' ?_ ?_
  · exact (continuous_const.mul (hfc.comp (pe_resid_cont A))).comp_aestronglyMeasurable
      hX.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    simp only [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
    have hg := gc_den_pos hx (resid A (X ω))
    unfold fX
    rw [abs_div, abs_of_pos hg, div_le_iff₀ hg]
    nlinarith [abs_nonneg (resid A (X ω)), mul_nonneg hx (sq_nonneg (resid A (X ω))),
      mul_nonneg (abs_nonneg (resid A (X ω))) (mul_nonneg hx (sq_nonneg (resid A (X ω))))]

private theorem pe_src_err (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), 0 ≤ w j → w j ≤ 1 →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, s0 ≤ s → ∀ x e : ℝ, 0 ≤ x → 0 ≤ e →
        eLpNorm (fun ω => delAlpha1 w F S t j s ω - w j * fX x (ageD F S t j ω)) 2 P ≤
          ENNReal.ofReal (w j * e) →
        fro ((B : ℝ) • Muon.mean P (fun ω => delAlpha1 w F S t j s ω •
            (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))) -
          (w j * ∫ p, deriv (fX x) (resid F.A p) ∂(gaussPair m n)) •
            (expDelRes w F S t j (slotOne F.hB) s * EG F)) ≤
          CS / s * (w j * e) + 1 / s * CS * (w j * (36 * x * opNorm F.A ^ 2)) := by
  obtain ⟨Cc, hCc0, hCc⟩ := pe_facts s0 hs0 CS γ hγ
  intro Ω inst m n B P _ F S t j w hw0 hw1 hCo hCi hm hn s hs x e hx he he1
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  obtain ⟨-, hA1, -, L1, -, -, -, -, -⟩ := hCc Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hXm : Measurable X := S.meas _ _
  have hlaw : P.map X = gaussPair m n := S.law _ _
  obtain ⟨hG, hindc⟩ := tl_indep F S t j
  have hGc : MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j ≤ inst :=
    sup_le hXm.comap_le hG
  have hXc : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j] X :=
    (comap_measurable X).mono le_sup_left le_rfl
  obtain ⟨hcd, -, -, -⟩ := gc_f_hyp hx
  have hfc : Continuous (fX x) := hcd.continuous
  have hdm : Measurable (fun p : Vec m × Vec n => resid F.A p) := (pe_resid_cont F.A).measurable
  have hgm : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => w j * fX x (resid F.A (X ω))) :=
    (hfc.measurable.comp (hdm.comp hXc)).const_mul (w j)
  set e1 : Ω → ℝ := fun ω => delAlpha1 w F S t j s ω - w j * fX x (ageD F S t j ω) with he1def
  have hgmem := pe_memLp_fX (P := P) F.A F.hA X hXm hlaw (w j) hx
  have he1m : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j] e1 :=
    hA1.sub hgm
  have he12 : MemLp e1 2 P := L1.sub hgmem
  obtain ⟨hint1, hb1⟩ := pe_src_bessel P F S t j w CS hCo hCi hspos e1 he1m he12
  obtain ⟨hintA, -⟩ := pe_src_bessel P F S t j w CS hCo hCi hspos (delAlpha1 w F S t j s) hA1 L1
  set M : Ω → Mat m n := fun ω => Rs (delBufAge w F S t j ω) s *
    outer (ageU F S t j ω) (ageV F S t j ω) with hMdef
  have hsplit : (fun ω => delAlpha1 w F S t j s ω • M ω) =
      fun ω => e1 ω • M ω + (w j * fX x (ageD F S t j ω)) • M ω := by
    funext ω
    rw [← add_smul]
    congr 1
    simp only [he1def]; ring
  have hint2 : ∀ i k, Integrable (fun ω => ((w j * fX x (ageD F S t j ω)) • M ω) i k) P := by
    intro i k
    refine ((hintA i k).sub (hint1 i k)).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply, he1def, Matrix.smul_apply, smul_eq_mul, hMdef]
    ring
  rw [hsplit, tl_mean_add P _ _ hint1 hint2, smul_add]
  have hmain := pe_src_main P F S t j w CS hCo hCi hspos (c := w j) hw0 hx
  have hb1' : fro ((B : ℝ) • Muon.mean P (fun ω => e1 ω • M ω)) ≤ CS / s * (w j * e) := by
    refine hb1.trans (mul_le_mul_of_nonneg_left ?_ ?_)
    · exact pe_sqrt_int_le P he12 (mul_nonneg hw0 he) he1
    · have : 0 ≤ CS := (tlb_opNorm_nonneg _).trans hCo
      positivity
  have hsum : (B : ℝ) • Muon.mean P (fun ω => e1 ω • M ω) +
      (B : ℝ) • Muon.mean P (fun ω => (w j * fX x (ageD F S t j ω)) • M ω) -
      (w j * ∫ p, deriv (fX x) (resid F.A p) ∂(gaussPair m n)) •
        (expDelRes w F S t j (slotOne F.hB) s * EG F) =
      (B : ℝ) • Muon.mean P (fun ω => e1 ω • M ω) +
      ((B : ℝ) • Muon.mean P (fun ω => (w j * fX x (ageD F S t j ω)) • M ω) -
      (w j * ∫ p, deriv (fX x) (resid F.A p) ∂(gaussPair m n)) •
        (expDelRes w F S t j (slotOne F.hB) s * EG F)) := by abel
  rw [hsum]
  refine (tlb_fro_add _ _).trans ?_
  have hCS0 : 0 ≤ CS := (tlb_opNorm_nonneg _).trans hCo
  have hA0 : 0 ≤ opNorm F.A ^ 2 := by positivity
  exact add_le_add hb1' hmain

end PeSrc5

section PeGram
open ProbabilityTheory

private theorem pe_gram_decomp (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), 0 ≤ w j → w j ≤ 1 →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, s0 ≤ s →
        (∀ i k, Integrable (fun ω => (delAlpha2 w F S t j s ω •
            (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))) i k) P) ∧
        (B : ℝ) • Muon.mean P (fun ω => delAlpha2 w F S t j s ω •
            (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))) =
          (bj w F S t j s • Hj w F S t j s + Cj w F S t j s) * F.C.Sin +
          Muon.mean P (fun ζ => (Xs (delBufAge w F S t j ζ) s * rIn F.C) *
            Muon.Foundations.condExpMat (sigmaOthers F S t j) P
              (fun ω => delAlpha2 w F S t j s ω • (Muon.outer
                (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).2
                (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).2 - 1)) ζ * rIn F.C) := by
  obtain ⟨Cc, hCc0, hCc⟩ := pe_facts s0 hs0 CS γ hγ
  intro Ω inst m n B P _ F S t j w hw0 hw1 hCo hCi hm hn s hs
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hB : 0 < B := F.hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCS : 0 ≤ CS := (tlb_opNorm_nonneg _).trans hCo
  obtain ⟨he2nn, -, e2m, -, L2, -, k2, -, -⟩ :=
    hCc Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hlaw : P.map X = gaussPair m n := S.law _ _
  obtain ⟨hG, hindc⟩ := tl_indep F S t j
  have hM0 := tl_meas_del w F S t j
  set e2 := delAlpha2 w F S t j s with he2def
  set r := opNorm (rIn F.C) with hrdef
  have hr0 : 0 ≤ r := tlb_opNorm_nonneg _
  have hrr : r * r ≤ CS := (tlb_opNorm_rIn_mul_self F.C).le.trans hCi
  have hs2 : 0 < 1 / (2 * Real.sqrt s) := by positivity
  -- the factors
  have hXs : Continuous (fun M : Mat m n => Xs M s) := by
    unfold Xs; exact (tlc_Rs_continuous s hspos).matrix_mul continuous_id
  have hLc : Continuous (fun M : Mat m n => Xs M s * rIn F.C) := hXs.matrix_mul continuous_const
  have hLm : ∀ i k, Measurable[(sigmaOthers F S t j)] (fun ω => (Xs (delBufAge w F S t j ω) s * rIn F.C) i k) :=
    fun i k => tl_entm (sigmaOthers F S t j) _ hM0 (fun M => Xs M s * rIn F.C) hLc i k
  have hXm : ∀ i k, Measurable[(sigmaOthers F S t j)] (fun ω => Xs (delBufAge w F S t j ω) s i k) :=
    fun i k => tl_entm (sigmaOthers F S t j) _ hM0 (fun M => Xs M s) hXs i k
  have hRm : ∀ i k, Measurable[(sigmaOthers F S t j)] (fun ω : Ω => rIn F.C i k) := fun i k => measurable_const
  have hXb : ∀ ω, opNorm (Xs (delBufAge w F S t j ω) s) ≤ 1 / (2 * Real.sqrt s) :=
    fun ω => (lem_app_de_resolvent _ s hspos).2.2.1
  have hLb' : ∀ ω, opNorm (Xs (delBufAge w F S t j ω) s * rIn F.C) ≤ 1 / (2 * Real.sqrt s) * r :=
    fun ω => (tlb_opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hXb ω) hr0)
  have hLb : ∀ ω i k, |(Xs (delBufAge w F S t j ω) s * rIn F.C) i k| ≤ 1 / (2 * Real.sqrt s) * r :=
    fun ω i k => (tlc_abs_entry_le _ i k).trans (hLb' ω)
  have hRb : ∀ (ω : Ω) i k, |rIn F.C i k| ≤ r := fun ω i k => tlc_abs_entry_le _ i k
  have hXbd : ∀ ω i k, |Xs (delBufAge w F S t j ω) s i k| ≤ 1 / (2 * Real.sqrt s) :=
    fun ω i k => (tlc_abs_entry_le _ i k).trans (hXb ω)
  have hW := tl_int_ww (n := n) (m := m) P X hlaw e2 L2
  have hint := tlc_int_LFR (mΩ := inst) P (sigmaOthers F S t j) hG
    (fun ω => Xs (delBufAge w F S t j ω) s * rIn F.C) (fun _ => rIn F.C)
    (1 / (2 * Real.sqrt s) * r) r (by positivity) hLm hRm hLb hRb _ hW
  have hpt : ∀ ω, (B : ℝ) • (e2 ω • (Xs (delBufAge w F S t j ω) s *
      outer (ageV F S t j ω) (ageV F S t j ω))) =
      (Xs (delBufAge w F S t j ω) s * rIn F.C) * (e2 ω • Muon.outer (X ω).2 (X ω).2) * rIn F.C := by
    intro ω
    have h := tl_B_outer_vv F.C B hB (X ω)
    have h2 : (B : ℝ) • (e2 ω • (Xs (delBufAge w F S t j ω) s *
        outer (ageV F S t j ω) (ageV F S t j ω))) =
        Xs (delBufAge w F S t j ω) s * (e2 ω • ((B : ℝ) • Muon.outer (momV F.C B (X ω))
          (momV F.C B (X ω)))) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, smul_comm]; rfl
    rw [h2, h]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hsum_int : ∀ i k, Integrable (fun ω => (e2 ω • (Xs (delBufAge w F S t j ω) s *
      outer (ageV F S t j ω) (ageV F S t j ω))) i k) P := by
    intro i k
    refine ((hint i k).const_mul ((B : ℝ)⁻¹)).congr (Filter.Eventually.of_forall fun ω => ?_)
    have := congrFun (congrFun (hpt ω) i) k
    simp only [Matrix.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]
    field_simp
  refine ⟨hsum_int, ?_⟩
  have hmean : (B : ℝ) • Muon.mean P (fun ω => e2 ω • (Xs (delBufAge w F S t j ω) s *
      outer (ageV F S t j ω) (ageV F S t j ω))) =
      Muon.mean P (fun ω => (Xs (delBufAge w F S t j ω) s * rIn F.C) *
        (e2 ω • Muon.outer (X ω).2 (X ω).2) * rIn F.C) := by
    rw [← tl_mean_smul]
    exact congrArg _ (funext hpt)
  rw [hmean, tl_mean_tower P (sigmaOthers F S t j) hG]
  obtain ⟨hK, -⟩ := tl_gram_cond P X hlaw (sigmaOthers F S t j) hG hindc e2 e2m L2
  set Γ : Ω → Mat n n := Muon.Foundations.condExpMat (sigmaOthers F S t j) P
    (fun ω => e2 ω • (Muon.outer (X ω).2 (X ω).2 - 1)) with hΓdef
  have hΓint : ∀ i k, Integrable (fun ζ => Γ ζ i k) P := fun i k => by
    simpa only [hΓdef, Muon.Foundations.condExpMat_apply] using integrable_condExp
  have hφ : Integrable (condExp (sigmaOthers F S t j) P e2) P := integrable_condExp
  have hpull := tlc_condExpMat_pull (mΩ := inst) P (sigmaOthers F S t j) hG
    (fun ω => Xs (delBufAge w F S t j ω) s * rIn F.C) (fun _ => rIn F.C)
    (1 / (2 * Real.sqrt s) * r) r (by positivity) hr0 hLm hRm hLb hRb
    (fun ω => e2 ω • Muon.outer (X ω).2 (X ω).2) hW
  have halg : ∀ (X0 : Mat m n) (φ : ℝ) (Γ' : Mat n n),
      (X0 * rIn F.C) * (φ • (1 : Mat n n) + Γ') * rIn F.C =
        (φ • X0) * F.C.Sin + (X0 * rIn F.C) * Γ' * rIn F.C := by
    intro X0 φ Γ'
    rw [← tl_rIn_sq F.C]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  have hae : ∀ᵐ ζ ∂P, Muon.Foundations.condExpMat (sigmaOthers F S t j) P
      (fun ω => (Xs (delBufAge w F S t j ω) s * rIn F.C) * (e2 ω • Muon.outer (X ω).2 (X ω).2) *
        rIn F.C) ζ =
      (condExp (sigmaOthers F S t j) P e2 ζ • Xs (delBufAge w F S t j ζ) s) * F.C.Sin +
        (Xs (delBufAge w F S t j ζ) s * rIn F.C) * Γ ζ * rIn F.C := by
    filter_upwards [hpull, hK] with ζ h1 h2
    rw [h1, h2]
    exact halg _ _ _
  rw [tl_mean_congr P _ _ hae]
  -- integrability
  have hX0int : ∀ i k, Integrable (fun ζ => Xs (delBufAge w F S t j ζ) s i k) P := fun i k =>
    Integrable.of_bound (((hXm i k).mono hG le_rfl).aestronglyMeasurable) (1 / (2 * Real.sqrt s))
      (Filter.Eventually.of_forall fun ζ => by
        rw [Real.norm_eq_abs]; exact hXbd ζ i k)
  have hφX : ∀ i k, Integrable (fun ζ => (condExp (sigmaOthers F S t j) P e2 ζ •
      Xs (delBufAge w F S t j ζ) s) i k) P := by
    intro i k
    have := Integrable.bdd_mul (c := 1 / (2 * Real.sqrt s)) hφ
      (((hXm i k).mono hG le_rfl).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ζ => by rw [Real.norm_eq_abs]; exact hXbd ζ i k)
    refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  have hφXS : ∀ i k, Integrable (fun ζ => ((condExp (sigmaOthers F S t j) P e2 ζ •
      Xs (delBufAge w F S t j ζ) s) * F.C.Sin) i k) P := by
    intro i k
    simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ fun l _ => (hφX i l).mul_const _
  have hLΓR := tlc_int_LFR (mΩ := inst) P (sigmaOthers F S t j) hG
    (fun ω => Xs (delBufAge w F S t j ω) s * rIn F.C) (fun _ => rIn F.C)
    (1 / (2 * Real.sqrt s) * r) r (by positivity) hLm hRm hLb hRb Γ hΓint
  rw [tl_mean_add P _ _ hφXS hLΓR, tl_mean_mul_right P _ F.C.Sin hφX]
  have hC : Cj w F S t j s = Muon.mean P (fun ω =>
      (condExp (sigmaOthers F S t j) P e2 ω - bj w F S t j s) • Xs (delBufAge w F S t j ω) s) := rfl
  have hH : Hj w F S t j s = Muon.mean P (fun ω => Xs (delBufAge w F S t j ω) s) := rfl
  have hsub : Muon.mean P (fun ω =>
      (condExp (sigmaOthers F S t j) P e2 ω - bj w F S t j s) • Xs (delBufAge w F S t j ω) s) =
      Muon.mean P (fun ω => condExp (sigmaOthers F S t j) P e2 ω • Xs (delBufAge w F S t j ω) s) -
        bj w F S t j s • Muon.mean P (fun ω => Xs (delBufAge w F S t j ω) s) := by
    rw [← tl_mean_smul]
    rw [← tl_mean_sub P _ _ hφX (fun i k => by
      simp only [Matrix.smul_apply, smul_eq_mul]; exact (hX0int i k).const_mul _)]
    exact congrArg _ (funext fun ω => sub_smul _ _ _)
  rw [hC, hH, hsub, show ∀ a b : Mat m n, a + (b - a) = b from fun a b => by abel]


end PeGram

section PeGram2
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma pe_resid_pow4_int {m n : ℕ} (Δ : Mat m n) (hΔ : fro Δ = 1) :
    Integrable (fun p : Vec m × Vec n => resid Δ p ^ 4) (gaussPair m n) := by
  by_contra h
  have h0 := integral_undef h
  obtain ⟨_, _, h4, _, _⟩ := lem_app_setup_residual_i Δ hΔ
  have hS : 0 ≤ ∑ k ∈ Finset.range (min m n), svals Δ k ^ 4 :=
    Finset.sum_nonneg (fun k _ => by positivity)
  linarith

private lemma pe_psi_abs {x d : ℝ} (hx : 0 ≤ x) : |psiX x d| ≤ d ^ 2 := by
  unfold psiX
  have h1 := mul_nonneg hx (sq_nonneg d)
  rw [abs_of_nonneg (div_nonneg (sq_nonneg d) (by linarith))]
  exact div_le_self (sq_nonneg d) (by linarith)

private lemma pe_psi_cont {x : ℝ} (hx : 0 ≤ x) : Continuous (psiX x) := by
  unfold psiX
  refine Continuous.div (by fun_prop) (by fun_prop) (fun d => ?_)
  have := mul_nonneg hx (sq_nonneg d)
  exact (by linarith : (0:ℝ) < 1 + x * d ^ 2).ne'

private lemma pe_memLp_psi {m n : ℕ} {P : Measure Ω} (A : Mat m n) (hA : fro A = 1)
    (X : Ω → Vec m × Vec n) (hX : Measurable X) (hlaw : P.map X = gaussPair m n) (c : ℝ)
    {x : ℝ} (hx : 0 ≤ x) :
    MemLp (fun ω => c * psiX x (resid A (X ω))) 2 P := by
  have hc : Continuous (fun p : Vec m × Vec n => c * psiX x (resid A p)) :=
    continuous_const.mul ((pe_psi_cont hx).comp (pe_resid_cont A))
  have hint4 : Integrable (fun ω => resid A (X ω) ^ 4) P := by
    have h := pe_resid_pow4_int A hA
    rw [← hlaw] at h
    exact (integrable_map_measure (((pe_resid_cont A).pow 4).aestronglyMeasurable)
      hX.aemeasurable).1 h
  rw [memLp_two_iff_integrable_sq (hc.comp_aestronglyMeasurable hX.aestronglyMeasurable)]
  refine (hint4.const_mul (c ^ 2)).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((hc.comp_aestronglyMeasurable hX.aestronglyMeasurable).pow 2)
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
    have h1 := pe_psi_abs (x := x) (d := resid A (X ω)) hx
    have h2 : psiX x (resid A (X ω)) ^ 2 ≤ resid A (X ω) ^ 4 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs] at this
      calc _ ≤ (resid A (X ω) ^ 2) ^ 2 := this
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg c)

private lemma pe_int_gram {m n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (e : Ω → ℝ) (he2 : MemLp e 2 P) :
    ∀ i k, Integrable (fun ω => (e ω • (Muon.outer (X ω).2 (X ω).2 - 1)) i k) P := by
  intro i k
  have := tlb_integrable_mul (mΩ := mΩ) (tlb_memLp_sq_snd (mΩ := mΩ) P X hX i k) he2
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [Muon.outer, Matrix.vecMulVec_apply]
  ring

private lemma pe_gram_const {m n : ℕ} (A : Mat m n) (hA : fro A = 1) {x : ℝ} (hx : 0 ≤ x) :
    fro (Muon.mean (gaussPair m n) (fun p => psiX x (resid A p) • (Muon.outer p.2 p.2 - 1))) ≤
      6 * opNorm A := by
  obtain ⟨hcd, hpoly, hb2⟩ := gc_psi_hyp hx
  have h := lem_app_de_stein_viii A (psiX x) hcd hpoly 6 hb2
  rw [tlb_opNorm_transpose, tlb_fro_transpose, hA, mul_one] at h
  have hswap : (gaussPair n m).map Prod.swap = gaussPair m n := by
    unfold gaussPair
    rw [Measure.prod_swap]
  have hmean : Muon.mean (gaussPair m n) (fun p => psiX x (resid A p) • (Muon.outer p.2 p.2 - 1)) =
      Muon.mean (gaussPair n m) (fun q => psiX x (resid Aᵀ q) • (Muon.outer q.1 q.1 - 1)) := by
    ext i k
    simp only [Muon.mean, Matrix.of_apply]
    rw [← hswap]
    have hm : Measurable (fun p : Vec m × Vec n => (psiX x (resid A p) •
        (Muon.outer p.2 p.2 - 1)) i k) := by
      have hc : Continuous (fun p : Vec m × Vec n => (psiX x (resid A p) •
          (Muon.outer p.2 p.2 - 1)) i k) := by
        simp only [Matrix.smul_apply, Matrix.sub_apply, Muon.outer, Matrix.vecMulVec_apply,
          smul_eq_mul]
        exact ((pe_psi_cont hx).comp (pe_resid_cont A)).mul (by fun_prop)
      exact hc.measurable
    rw [integral_map measurable_swap.aemeasurable hm.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    have hr : resid A (Prod.swap q) = resid Aᵀ q := by
      unfold resid
      simp only [Prod.fst_swap, Prod.snd_swap]
      calc dotProduct q.2 (A *ᵥ q.1) = dotProduct (A *ᵥ q.1) q.2 := dotProduct_comm _ _
        _ = dotProduct (q.1 ᵥ* Aᵀ) q.2 := by rw [Matrix.vecMul_transpose]
        _ = dotProduct q.1 (Aᵀ *ᵥ q.2) := (Matrix.dotProduct_mulVec _ _ _).symm
    simp only [hr, Prod.snd_swap]
  rw [hmean]
  exact h

end PeGram2

section PeGram3
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
private theorem pe_gram_err (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), 0 ≤ w j → w j ≤ 1 →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, s0 ≤ s → ∀ x σ e : ℝ, 0 ≤ x → 0 ≤ σ → 0 ≤ e →
        eLpNorm (fun ω => delAlpha2 w F S t j s ω - w j ^ 2 * σ * psiX x (ageD F S t j ω)) 2 P ≤
          ENNReal.ofReal (w j ^ 2 * e) →
        fro ((B : ℝ) • Muon.mean P (fun ω => delAlpha2 w F S t j s ω •
            (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))) -
          (bj w F S t j s • Hj w F S t j s + Cj w F S t j s) * F.C.Sin) ≤
          CS / (2 * Real.sqrt s) * (2 * (w j ^ 2 * e) + w j ^ 2 * σ * (6 * opNorm F.A)) := by
  obtain ⟨Cc, hCc0, hCc⟩ := pe_facts s0 hs0 CS γ hγ
  intro Ω inst m n B P _ F S t j w hw0 hw1 hCo hCi hm hn s hs x σ e hx hσ he he2
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hCS : 0 ≤ CS := (tlb_opNorm_nonneg _).trans hCo
  have hB : 0 < B := F.hB
  obtain ⟨-, -, hA2, -, L2, -, -, -, -⟩ := hCc Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs
  obtain ⟨-, hdec⟩ := pe_gram_decomp s0 hs0 CS γ hγ Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs
  rw [hdec, add_sub_cancel_left]
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hXm : Measurable X := S.meas _ _
  have hlaw : P.map X = gaussPair m n := S.law _ _
  obtain ⟨hG, hindc⟩ := tl_indep F S t j
  have hM0 := tl_meas_del w F S t j
  have hGc : MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j ≤ inst :=
    sup_le hXm.comap_le hG
  have hXc : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j] X :=
    (comap_measurable X).mono le_sup_left le_rfl
  have hdm : Measurable (fun p : Vec m × Vec n => resid F.A p) := (pe_resid_cont F.A).measurable
  set A := F.A with hAdef
  have hA : fro A = 1 := F.hA
  set c2 : ℝ := w j ^ 2 * σ with hc2def
  have hc20 : 0 ≤ c2 := by positivity
  -- the split of α₂
  set a2s : Ω → ℝ := fun ω => c2 * psiX x (resid A (X ω)) with ha2sdef
  set d2 : Ω → ℝ := fun ω => delAlpha2 w F S t j s ω - w j ^ 2 * σ * psiX x (ageD F S t j ω)
    with hd2def
  have ha2sm : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j] a2s :=
    (((pe_psi_cont hx).measurable.comp (hdm.comp hXc))).const_mul c2
  have ha2sm' : Measurable[MeasurableSpace.comap X inferInstance] a2s :=
    ((pe_psi_cont hx).measurable.comp (hdm.comp (comap_measurable X))).const_mul c2
  have ha2sL : MemLp a2s 2 P := pe_memLp_psi (P := P) A hA X hXm hlaw c2 hx
  have hd2m : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j] d2 :=
    hA2.sub ha2sm
  have hd2L : MemLp d2 2 P := L2.sub ha2sL
  have hsplit : (fun ω => delAlpha2 w F S t j s ω • (Muon.outer (X ω).2 (X ω).2 - 1)) =
      fun ω => d2 ω • (Muon.outer (X ω).2 (X ω).2 - 1) + a2s ω • (Muon.outer (X ω).2 (X ω).2 - 1) := by
    funext ω
    rw [← add_smul]
    congr 1
    have hD : ageD F S t j ω = resid A (X ω) := rfl
    simp only [hd2def, ha2sdef, hc2def, hD]
    ring
  -- the pieces of the conditional expectation
  have hi1 := pe_int_gram P X hlaw d2 hd2L
  have hi2 := pe_int_gram P X hlaw a2s ha2sL
  have hadd := tlc_condExpMat_add (mΩ := inst) P (sigmaOthers F S t j)
    (fun ω => d2 ω • (Muon.outer (X ω).2 (X ω).2 - 1))
    (fun ω => a2s ω • (Muon.outer (X ω).2 (X ω).2 - 1)) hi1 hi2
  obtain ⟨-, hΓ1b⟩ := tl_gram_cond P X hlaw (sigmaOthers F S t j) hG hindc d2 hd2m hd2L
  have hY2 : ∀ i k, Measurable[MeasurableSpace.comap X inferInstance]
      (fun ω => (a2s ω • (Muon.outer (X ω).2 (X ω).2 - 1)) i k) := by
    intro i k
    have h2i : Measurable[MeasurableSpace.comap X inferInstance] (fun ω => (X ω).2 i) :=
      (measurable_pi_apply i).comp (measurable_snd.comp (comap_measurable X))
    have h2k : Measurable[MeasurableSpace.comap X inferInstance] (fun ω => (X ω).2 k) :=
      (measurable_pi_apply k).comp (measurable_snd.comp (comap_measurable X))
    have e : (fun ω => (a2s ω • (Muon.outer (X ω).2 (X ω).2 - 1)) i k) =
        fun ω => a2s ω * ((X ω).2 i * (X ω).2 k - (1 : Mat n n) i k) := by
      funext ω; simp [Muon.outer, Matrix.vecMulVec_apply]
    rw [e]
    exact ha2sm'.mul ((h2i.mul h2k).sub_const _)
  have hci2 := Muon.Foundations.condExpMat_indep_eq (μ := P) (sigmaOthers F S t j) _ hG
    hXm.comap_le hY2 hindc
  have hM2 : fro (Muon.mean P (fun ω => a2s ω • (Muon.outer (X ω).2 (X ω).2 - 1))) ≤
      c2 * (6 * opNorm A) := by
    have hh : Continuous (fun p : Vec m × Vec n =>
        (c2 * psiX x (resid A p)) • (Muon.outer p.2 p.2 - 1)) := by
      refine continuous_matrix fun i k => ?_
      simp only [Matrix.smul_apply, Matrix.sub_apply, Muon.outer, Matrix.vecMulVec_apply,
        smul_eq_mul]
      exact (continuous_const.mul ((pe_psi_cont hx).comp (pe_resid_cont A))).mul (by fun_prop)
    have hm := pe_mean_map P X hXm _ hh
    rw [show (fun ω => a2s ω • (Muon.outer (X ω).2 (X ω).2 - 1)) =
      fun ω => (fun p : Vec m × Vec n => (c2 * psiX x (resid A p)) • (Muon.outer p.2 p.2 - 1)) (X ω)
      from rfl, hm, hlaw]
    have hsm : Muon.mean (gaussPair m n) (fun p => (c2 * psiX x (resid A p)) •
        (Muon.outer p.2 p.2 - 1)) = c2 • Muon.mean (gaussPair m n)
          (fun p => psiX x (resid A p) • (Muon.outer p.2 p.2 - 1)) := by
      ext i k
      simp only [Muon.mean, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hsm, tlb_fro_smul, abs_of_nonneg hc20]
    exact mul_le_mul_of_nonneg_left (pe_gram_const A hA hx) hc20
  -- the sandwich
  set r := opNorm (rIn F.C) with hrdef
  have hr0 : 0 ≤ r := tlb_opNorm_nonneg _
  have hrr : r * r ≤ CS := (tlb_opNorm_rIn_mul_self F.C).le.trans hCi
  have hXs : Continuous (fun M : Mat m n => Xs M s * rIn F.C) :=
    (by unfold Xs; exact (tlc_Rs_continuous s hspos).matrix_mul continuous_id : Continuous
      (fun M : Mat m n => Xs M s)).matrix_mul continuous_const
  have hLm : ∀ i k, Measurable[sigmaOthers F S t j]
      (fun ω => (Xs (delBufAge w F S t j ω) s * rIn F.C) i k) :=
    fun i k => tl_entm (sigmaOthers F S t j) _ hM0 (fun M => Xs M s * rIn F.C) hXs i k
  have hXb : ∀ ω, opNorm (Xs (delBufAge w F S t j ω) s) ≤ 1 / (2 * Real.sqrt s) :=
    fun ω => (lem_app_de_resolvent _ s hspos).2.2.1
  have hLb' : ∀ ω, opNorm (Xs (delBufAge w F S t j ω) s * rIn F.C) ≤ 1 / (2 * Real.sqrt s) * r :=
    fun ω => (tlb_opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hXb ω) hr0)
  have hLb : ∀ ω i k, |(Xs (delBufAge w F S t j ω) s * rIn F.C) i k| ≤ 1 / (2 * Real.sqrt s) * r :=
    fun ω i k => (tlc_abs_entry_le _ i k).trans (hLb' ω)
  have hRm : ∀ i k, Measurable[sigmaOthers F S t j] (fun ω : Ω => rIn F.C i k) := fun i k => measurable_const
  have hRb : ∀ (ω : Ω) i k, |rIn F.C i k| ≤ r := fun ω i k => tlc_abs_entry_le _ i k
  set Γ : Ω → Mat n n := Muon.Foundations.condExpMat (sigmaOthers F S t j) P
    (fun ω => delAlpha2 w F S t j s ω • (Muon.outer (X ω).2 (X ω).2 - 1)) with hΓdef
  have hΓint : ∀ i k, Integrable (fun ζ => Γ ζ i k) P := fun i k => by
    simpa only [hΓdef, Muon.Foundations.condExpMat_apply] using integrable_condExp
  have hLΓR := tlc_int_LFR (mΩ := inst) P (sigmaOthers F S t j) hG
    (fun ω => Xs (delBufAge w F S t j ω) s * rIn F.C) (fun _ => rIn F.C)
    (1 / (2 * Real.sqrt s) * r) r (by positivity) hLm hRm hLb hRb Γ hΓint
  have hΓae : ∀ᵐ ζ ∂P, Γ ζ = Muon.Foundations.condExpMat (sigmaOthers F S t j) P
      (fun ω => d2 ω • (Muon.outer (X ω).2 (X ω).2 - 1)) ζ +
      Muon.Foundations.condExpMat (sigmaOthers F S t j) P
      (fun ω => a2s ω • (Muon.outer (X ω).2 (X ω).2 - 1)) ζ := by
    filter_upwards [hadd] with ζ h
    simp only [hΓdef]
    rw [hsplit]
    exact h
  obtain ⟨hsi, hsle⟩ := pe_int_sqrt_condExp P (sigmaOthers F S t j) hG d2 hd2L
  have hsq2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  set ψ : Ω → ℝ := fun ζ => CS / (2 * Real.sqrt s) * (Real.sqrt 2 *
    Real.sqrt (condExp (sigmaOthers F S t j) P (fun ω => d2 ω ^ 2) ζ) + c2 * (6 * opNorm A)) with hψdef
  have hψi : Integrable ψ P :=
    ((hsi.const_mul (Real.sqrt 2)).add (integrable_const (c2 * (6 * opNorm A)))).const_mul _
  have hae : ∀ᵐ ζ ∂P, fro ((Xs (delBufAge w F S t j ζ) s * rIn F.C) * Γ ζ * rIn F.C) ≤ ψ ζ := by
    filter_upwards [hΓae, hΓ1b, hci2] with ζ h1 h2 h3
    refine (tlc_fro_sandwich _ _ _).trans ?_
    have hG1 : fro (Γ ζ) ≤ Real.sqrt 2 * Real.sqrt (condExp (sigmaOthers F S t j) P
        (fun ω => d2 ω ^ 2) ζ) + c2 * (6 * opNorm A) := by
      rw [h1]
      refine (tlb_fro_add _ _).trans (add_le_add h2 ?_)
      rw [h3]
      exact hM2
    have hGn : 0 ≤ Real.sqrt 2 * Real.sqrt (condExp (sigmaOthers F S t j) P
        (fun ω => d2 ω ^ 2) ζ) + c2 * (6 * opNorm A) :=
      add_nonneg (by positivity) (mul_nonneg hc20 (mul_nonneg (by norm_num) (tlb_opNorm_nonneg _)))
    calc opNorm (Xs (delBufAge w F S t j ζ) s * rIn F.C) * fro (Γ ζ) * r
        ≤ (1 / (2 * Real.sqrt s) * r) * (Real.sqrt 2 * Real.sqrt (condExp (sigmaOthers F S t j) P
          (fun ω => d2 ω ^ 2) ζ) + c2 * (6 * opNorm A)) * r :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hLb' ζ) hG1 (tlb_fro_nonneg _) (by positivity)) hr0
      _ = (r * r) * (1 / (2 * Real.sqrt s)) * (Real.sqrt 2 * Real.sqrt (condExp (sigmaOthers F S t j) P
          (fun ω => d2 ω ^ 2) ζ) + c2 * (6 * opNorm A)) := by ring
      _ ≤ CS * (1 / (2 * Real.sqrt s)) * (Real.sqrt 2 * Real.sqrt (condExp (sigmaOthers F S t j) P
          (fun ω => d2 ω ^ 2) ζ) + c2 * (6 * opNorm A)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrr (by positivity)) hGn
      _ = ψ ζ := by simp only [hψdef]; ring
  have hmean := pe_mean_fro_le_int P _ (fun i k => hLΓR i k) ψ hψi hae
  refine hmean.trans ?_
  have hint : ∫ ζ, ψ ζ ∂P = CS / (2 * Real.sqrt s) * (Real.sqrt 2 * ∫ ζ, Real.sqrt (condExp
      (sigmaOthers F S t j) P (fun ω => d2 ω ^ 2) ζ) ∂P + c2 * (6 * opNorm A)) := by
    simp only [hψdef]
    rw [integral_const_mul, integral_add (hsi.const_mul _) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul]
  rw [hint]
  have hd2n : ∫ ζ, Real.sqrt (condExp (sigmaOthers F S t j) P (fun ω => d2 ω ^ 2) ζ) ∂P ≤
      w j ^ 2 * e :=
    hsle.trans (pe_sqrt_int_le P hd2L (mul_nonneg (sq_nonneg _) he) he2)
  have hcoef0 : 0 ≤ CS / (2 * Real.sqrt s) := by positivity
  have hA0 : 0 ≤ opNorm A := tlb_opNorm_nonneg _
  have h1 : Real.sqrt 2 * ∫ ζ, Real.sqrt (condExp (sigmaOthers F S t j) P
      (fun ω => d2 ω ^ 2) ζ) ∂P ≤ 2 * (w j ^ 2 * e) :=
    mul_le_mul hsq2 hd2n (integral_nonneg fun ζ => Real.sqrt_nonneg _) (by norm_num)
  have h2 : c2 * (6 * opNorm A) = w j ^ 2 * σ * (6 * opNorm A) := rfl
  exact mul_le_mul_of_nonneg_left (by rw [h2] at *; linarith) hcoef0

end PeGram3

section PeNorms
open scoped Matrix.Norms.L2Operator
variable {Ω' : Type*}
private lemma pj_opNorm_nonneg {p q : ℕ} (K : Mat p q) : 0 ≤ opNorm K := by
  unfold opNorm; exact norm_nonneg _

private lemma pj_sq_mulVec {a b : ℕ} (K : Mat a b) (x : Vec b) :
    ∑ i, (K *ᵥ x) i ^ 2 ≤ opNorm K ^ 2 * ∑ i, x i ^ 2 := by
  have h2 : ‖Matrix.toEuclideanLin K (WithLp.toLp 2 x)‖ ≤ opNorm K * ‖WithLp.toLp 2 x‖ := by
    have := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)).le_opNorm (WithLp.toLp 2 x)
    simpa [opNorm] using this
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)] at h3
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Real.norm_eq_abs, sq_abs] using h3

private lemma pj_opNorm_le_of_sq {m n : ℕ} (U : Mat m n) (M : ℝ) (hM : 0 ≤ M)
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

private lemma pj_opNorm_of_bilin {a b : ℕ} (K : Mat a b) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ (x : Vec a) (y : Vec b),
      |dotProduct x (K *ᵥ y)| ≤ c * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2)) :
    opNorm K ≤ c := by
  refine pj_opNorm_le_of_sq K c hc fun y => ?_
  have h1 := h (K *ᵥ y) y
  have hS : dotProduct (K *ᵥ y) (K *ᵥ y) = ∑ k, (K *ᵥ y) k ^ 2 := by
    simp [dotProduct, sq]
  rw [hS] at h1
  set S := ∑ k, (K *ᵥ y) k ^ 2 with hSdef
  set Y := ∑ i, y i ^ 2 with hYdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [abs_of_nonneg hS0] at h1
  have hr := Real.sq_sqrt hS0
  have hq := Real.sq_sqrt hY0
  have hr0 := Real.sqrt_nonneg S
  have hq0 := Real.sqrt_nonneg Y
  have key : Real.sqrt S ≤ c * Real.sqrt Y := by
    by_contra hcon
    push Not at hcon
    have hpos : 0 < Real.sqrt S := lt_of_le_of_lt (by positivity) hcon
    nlinarith [mul_pos hpos (sub_pos.2 hcon)]
  calc S = Real.sqrt S ^ 2 := hr.symm
    _ ≤ (c * Real.sqrt Y) ^ 2 := pow_le_pow_left₀ hr0 key 2
    _ = c ^ 2 * Y := by rw [mul_pow, hq]

private lemma gh_bilin_le {a b : ℕ} (K : Mat a b) (x : Vec a) (y : Vec b) :
    |dotProduct x (K *ᵥ y)| ≤
      opNorm K * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2) := by
  have hS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (fun i => (K *ᵥ y) i)
  have h2 := pj_sq_mulVec K y
  have hn := pj_opNorm_nonneg K
  have hx0 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hy0 : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hd : (dotProduct x (K *ᵥ y)) ^ 2 ≤ (∑ i, x i ^ 2) * (opNorm K ^ 2 * ∑ i, y i ^ 2) := by
    refine le_trans (by simpa [dotProduct] using hS) ?_
    exact mul_le_mul_of_nonneg_left h2 hx0
  calc |dotProduct x (K *ᵥ y)| = Real.sqrt ((dotProduct x (K *ᵥ y)) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i, x i ^ 2) * (opNorm K ^ 2 * ∑ i, y i ^ 2)) := Real.sqrt_le_sqrt hd
    _ = _ := by
        rw [Real.sqrt_mul hx0, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hn]; ring

private lemma gh_bilin_int {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {a b : ℕ} (D : Ω' → Mat a b)
    (hint : ∀ i k, Integrable (fun ω => D ω i k) P) (xv : Vec a) (yv : Vec b) :
    dotProduct xv ((Matrix.of fun i k => ∫ ω, D ω i k ∂P) *ᵥ yv)
      = ∫ ω, dotProduct xv (D ω *ᵥ yv) ∂P := by
  have hin : ∀ i, Integrable (fun ω => xv i * ∑ k, D ω i k * yv k) P := fun i =>
    ((integrable_finsetSum _ fun k _ => (hint i k).mul_const (yv k))).const_mul (xv i)
  have h1 : ∫ ω, dotProduct xv (D ω *ᵥ yv) ∂P = ∑ i, ∫ ω, xv i * ∑ k, D ω i k * yv k ∂P := by
    unfold dotProduct Matrix.mulVec
    simp only [dotProduct]
    exact integral_finsetSum _ fun i _ => hin i
  rw [h1]
  unfold dotProduct Matrix.mulVec
  simp only [Matrix.of_apply, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun k _ => (hint i k).mul_const (yv k)]
  congr 1
  exact Finset.sum_congr rfl fun k _ => (integral_mul_const (yv k) _).symm

private lemma gh_opNorm_mean {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {a b : ℕ} (D : Ω' → Mat a b)
    (hint : ∀ i k, Integrable (fun ω => D ω i k) P) (c : ℝ) (hc : 0 ≤ c)
    (hD : ∀ ω, opNorm (D ω) ≤ c) : opNorm (Muon.mean P D) ≤ c := by
  refine pj_opNorm_of_bilin _ c hc fun x y => ?_
  have e : Muon.mean P D = Matrix.of fun i k => ∫ ω, D ω i k ∂P := rfl
  rw [e, gh_bilin_int P D hint x y]
  have hnorm := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun ω => dotProduct x (D ω *ᵥ y))
    (C := c * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2))
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      refine (gh_bilin_le (D ω) x y).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hD ω) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  simp only [probReal_univ, mul_one] at hnorm
  rwa [Real.norm_eq_abs] at hnorm

private lemma kern_opNorm_le_of_sq {a b : ℕ} (K : Mat a b) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Vec b, ∑ k, (K *ᵥ x) k ^ 2 ≤ c ^ 2 * ∑ i, x i ^ 2) : opNorm K ≤ c := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  show ‖Matrix.toEuclideanLin K x‖ ≤ c * ‖x‖
  have hx := h (WithLp.ofLp x)
  have hsq : ‖Matrix.toEuclideanLin K x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Real.norm_eq_abs, sq_abs] using hx
  nlinarith [norm_nonneg (Matrix.toEuclideanLin K x), mul_nonneg hc (norm_nonneg x)]

private lemma kern_inv_opNorm_le {k : ℕ} (S : Mat k k) (hS : S.PosSemidef) {a s : ℝ}
    (ha : 0 ≤ a) (hs : 0 < s) :
    opNorm (s • (1 : Mat k k) + a • S)⁻¹ ≤ 1 / s := by
  set M : Mat k k := s • (1 : Mat k k) + a • S with hM
  have hMy : ∀ (y : Vec k) (i : Fin k), (M *ᵥ y) i = s * y i + a * (S *ᵥ y) i := by
    intro y i
    simp [hM, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have key : ∀ y : Vec k, s ^ 2 * ∑ i, y i ^ 2 ≤ ∑ i, (M *ᵥ y) i ^ 2 := by
    intro y
    have hYnn : 0 ≤ ∑ i, y i * (S *ᵥ y) i := by
      have := hS.dotProduct_mulVec_nonneg y
      simpa [dotProduct, star_trivial] using this
    have hz : 0 ≤ ∑ i, (S *ᵥ y) i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have e : ∑ i, (M *ᵥ y) i ^ 2 = ∑ i, (s ^ 2 * y i ^ 2 + 2 * s * a * (y i * (S *ᵥ y) i)
        + a ^ 2 * (S *ᵥ y) i ^ 2) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hMy]; ring
    rw [e]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hs.le) ha) hYnn,
      mul_nonneg (sq_nonneg a) hz]
  have hinj : Function.Injective (M *ᵥ ·) := by
    intro y y' h
    have h' : M *ᵥ y = M *ᵥ y' := h
    have h0 : M *ᵥ (y - y') = 0 := by rw [Matrix.mulVec_sub, h', sub_self]
    have h1 := key (y - y')
    have h2 : ∑ i, (M *ᵥ (y - y')) i ^ 2 = 0 := by rw [h0]; simp
    have hnn : 0 ≤ ∑ i, (y - y') i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsum : ∑ i, (y - y') i ^ 2 = 0 := by
      have hs2 : 0 < s ^ 2 := pow_pos hs 2
      refine le_antisymm ?_ hnn
      nlinarith
    have hz : ∀ i, (y - y') i = 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ((y - y') i))).mp hsum i
        (Finset.mem_univ _)
      exact (pow_eq_zero_iff two_ne_zero).mp this
    exact sub_eq_zero.mp (funext hz)
  have hu : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hMinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hu)
  refine kern_opNorm_le_of_sq _ (one_div_nonneg.mpr hs.le) fun v => ?_
  have hv : M *ᵥ (M⁻¹ *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
  have h := key (M⁻¹ *ᵥ v)
  rw [hv] at h
  have hs2 : 0 < s ^ 2 := pow_pos hs 2
  rw [div_pow, one_pow, one_div]
  calc ∑ i, (M⁻¹ *ᵥ v) i ^ 2 = (s ^ 2)⁻¹ * (s ^ 2 * ∑ i, (M⁻¹ *ᵥ v) i ^ 2) := by
        rw [← mul_assoc, inv_mul_cancel₀ hs2.ne', one_mul]
    _ ≤ (s ^ 2)⁻¹ * ∑ i, v i ^ 2 := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hs2.le)

end PeNorms

section PeB
open ProbabilityTheory

private theorem pe_b (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ K : ℝ, ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), 0 ≤ w j → w j ≤ 1 →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, s0 ≤ s → 0 ≤ bj w F S t j s ∧ bj w F S t j s ≤ K * w j ^ 2 / s := by
  obtain ⟨Cc, hCc0, hCc⟩ := pe_facts s0 hs0 CS γ hγ
  refine ⟨Cc, ?_⟩
  intro Ω inst m n B P _ F S t j w hw0 hw1 hCo hCi hm hn s hs
  obtain ⟨hn2, -, -, -, -, -, -, hi, hle⟩ := hCc Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs
  obtain ⟨hG, -⟩ := tl_indep F S t j
  have hb : bj w F S t j s = ∫ ω, delAlpha2 w F S t j s ω ∂P := by
    unfold bj phiJ
    exact integral_condExp hG
  refine ⟨?_, ?_⟩
  · rw [hb]; exact integral_nonneg hn2
  · unfold bj phiJ
    calc ∫ ω, condExp (sigmaOthers F S t j) P (delAlpha2 w F S t j s) ω ∂P
        ≤ ∫ _ω, Cc * w j ^ 2 / s ∂P :=
          integral_mono_ae integrable_condExp (integrable_const _) hle
      _ = _ := by rw [integral_const, probReal_univ, one_smul]

end PeB

section PeNm
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

private lemma pe_hQ {m n B : ℕ} (F : FrozenParams m n B) :
    Measurable (fun x : Vec m × Vec n =>
      (dotProduct x.1 (Matrix.mulVec F.A x.2)) • (rOut F.C * Muon.outer x.1 x.2 * rIn F.C)) := by
  have hdot : Measurable (fun x : Vec m × Vec n => dotProduct x.1 (Matrix.mulVec F.A x.2)) := by
    show Measurable (fun x : Vec m × Vec n => ∑ i, x.1 i * ∑ j, F.A i j * x.2 j)
    exact Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp measurable_fst).mul
      (Finset.measurable_sum _ (fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp measurable_snd))))
  have hout : Continuous (fun x : Vec m × Vec n => Muon.outer x.1 x.2) :=
    continuous_pi fun i => continuous_pi fun j =>
      ((continuous_apply i).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)
  have hM : Measurable (fun x : Vec m × Vec n => rOut F.C * Muon.outer x.1 x.2 * rIn F.C) :=
    Continuous.measurable ((continuous_const.matrix_mul hout).matrix_mul continuous_const)
  exact hdot.smul hM

private lemma pe_meas_WB {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) : Measurable (WeightedBuf w F S t) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hQ := pe_hQ F
  unfold WeightedBuf
  refine Measurable.tsum fun j => ?_
  refine Measurable.const_smul ?_ (w j)
  show Measurable (fun ω => ((B : ℝ))⁻¹ • ∑ a : Fin B,
    (dotProduct (S.zw (t + 1 - (j : ℤ)) a ω).1 (Matrix.mulVec F.A (S.zw (t + 1 - (j : ℤ)) a ω).2)) •
      (rOut F.C * outer (S.zw (t + 1 - (j : ℤ)) a ω).1 (S.zw (t + 1 - (j : ℤ)) a ω).2 * rIn F.C))
  exact (Finset.measurable_sum _ fun a _ => hQ.comp (S.meas _ _)).const_smul ((B : ℝ)⁻¹)


private lemma pe_le_biSup {f : ℝ → ℝ} {S : Set ℝ} {c : ℝ} (hb : ∀ x ∈ S, f x ≤ c) (hc : 0 ≤ c)
    {x : ℝ} (hx : x ∈ S) : f x ≤ ⨆ y ∈ S, f y := by
  have hbdd : BddAbove (Set.range fun y => ⨆ (_ : y ∈ S), f y) := by
    refine ⟨c, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact Real.iSup_le (fun hy => hb y hy) hc
  refine le_trans (le_of_eq ?_) (le_ciSup hbdd x)
  rw [ciSup_pos hx]

private lemma pe_EG_fro {m n B : ℕ} (F : FrozenParams m n B) {CS : ℝ}
    (hCo : opNorm F.C.Sout ≤ CS) (hCi : opNorm F.C.Sin ≤ CS) : fro (EG F) ≤ CS := by
  have hCS0 : 0 ≤ CS := (tlb_opNorm_nonneg _).trans hCo
  have hro0 : 0 ≤ opNorm (rOut F.C) := tlb_opNorm_nonneg _
  have hri0 : 0 ≤ opNorm (rIn F.C) := tlb_opNorm_nonneg _
  have hrr : opNorm (rOut F.C) * opNorm (rIn F.C) ≤ CS := by
    have h1 : (opNorm (rOut F.C) * opNorm (rIn F.C)) ^ 2 ≤ CS ^ 2 := by
      have e1 := tlb_opNorm_rOut_mul_self F.C
      have e2 := tlb_opNorm_rIn_mul_self F.C
      calc (opNorm (rOut F.C) * opNorm (rIn F.C)) ^ 2
          = (opNorm (rOut F.C) * opNorm (rOut F.C)) * (opNorm (rIn F.C) * opNorm (rIn F.C)) := by ring
        _ ≤ CS * CS := by rw [e1, e2]; exact mul_le_mul hCo hCi (tlb_opNorm_nonneg _) hCS0
        _ = CS ^ 2 := by ring
    exact abs_le_of_sq_le_sq' h1 hCS0 |>.2
  unfold EG
  refine (tlc_fro_sandwich _ _ _).trans ?_
  rw [F.hA, mul_one]
  exact hrr

end PeNm

section PeNm2
open ProbabilityTheory
variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

private lemma pe_expRes_op [IsProbabilityMeasure P] {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) {s : ℝ} (hs : 0 < s) :
    opNorm (expRes w F S t s) ≤ 1 / s := by
  have hWB := pe_meas_WB w F S t
  have hRm : Measurable (fun M : Mat m n => Rs M s) := by
    exact (tlc_Rs_continuous s hs).measurable
  have hint : ∀ i k, Integrable (fun ω => Rs (WeightedBuf w F S t ω) s i k) P := by
    intro i k
    have hik : Measurable (fun M : Mat m m => M i k) :=
      (measurable_pi_apply k).comp (measurable_pi_apply i)
    refine Integrable.of_bound ((hik.comp (hRm.comp hWB)).aestronglyMeasurable) (1 / s)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact (tlc_abs_entry_le _ i k).trans (lem_app_de_resolvent _ s hs).1
  exact gh_opNorm_mean P _ hint (1 / s) (by positivity) fun ω => (lem_app_de_resolvent _ s hs).1

private lemma pe_expResT_op [IsProbabilityMeasure P] {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) {s : ℝ} (hs : 0 < s) :
    opNorm (expResT w F S t s) ≤ 1 / s := by
  have hWB := pe_meas_WB w F S t
  have hRm : Measurable (fun M : Mat m n => Rts M s) := by
    exact (tlc_Rts_continuous s hs).measurable
  have hint : ∀ i k, Integrable (fun ω => Rts (WeightedBuf w F S t ω) s i k) P := by
    intro i k
    have hik : Measurable (fun M : Mat n n => M i k) :=
      (measurable_pi_apply k).comp (measurable_pi_apply i)
    refine Integrable.of_bound ((hik.comp (hRm.comp hWB)).aestronglyMeasurable) (1 / s)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact (tlc_abs_entry_le _ i k).trans (lem_app_de_resolvent _ s hs).2.1
  exact gh_opNorm_mean P _ hint (1 / s) (by positivity) fun ω => (lem_app_de_resolvent _ s hs).2.1

end PeNm2
section Pe15Term
open ProbabilityTheory

private lemma pe15p4_fro_sub {a b : ℕ} (A B' : Mat a b) : fro (A - B') ≤ fro A + fro B' := by
  have : A - B' = A + (-1 : ℝ) • B' := by simp [sub_eq_add_neg]
  rw [this]
  refine (tlb_fro_add _ _).trans ?_
  rw [tlb_fro_smul]
  simp

private lemma pe15p4_identity {m n : ℕ} (SRC GRM H Hj Cj EG : Matrix (Fin m) (Fin n) ℝ)
    (Sin : Matrix (Fin n) (Fin n) ℝ) (Pj : Matrix (Fin m) (Fin m) ℝ) (b c : ℝ) :
    SRC - GRM + b • (H * Sin) - c • (Pj * EG) =
      (SRC - c • (Pj * EG)) - (GRM - (b • Hj + Cj) * Sin) + b • ((H - Hj) * Sin) - Cj * Sin := by
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, smul_sub, sub_smul, mul_sub,
    mul_smul]
  abel

set_option maxHeartbeats 2000000 in
private theorem pe15p4_term (ϱ : ℝ) (hϱ : 0 < ϱ) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), WeightClass w → opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B → ∀ s : ℝ, ϱ ≤ s → ∀ e₁ e₂ : ℝ, 0 ≤ e₁ → 0 ≤ e₂ →
      eLpNorm (fun ω => delAlpha1 w F S t j s ω - checkAlpha1 w F S t j s ω) 2 P
        ≤ ENNReal.ofReal (w j * e₁) →
      eLpNorm (fun ω => delAlpha2 w F S t j s ω - checkAlpha2 w F S t j s ω) 2 P
        ≤ ENNReal.ofReal (w j ^ 2 * e₂) →
      fro ((B : ℝ) • Muon.mean P (fun ω => delAlpha1 w F S t j s ω •
              (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))
            - delAlpha2 w F S t j s ω •
              (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))) +
          bj w F S t j s • (Hmix w F S t s * F.C.Sin) -
          (w j * ∫ p, deriv (fX (w j ^ 2 * qB w F S t s)) (resid F.A p) ∂(gaussPair m n)) •
            (expDelRes w F S t j (slotOne F.hB) s * EG F)) ≤
        w j * (CS / s * (e₁ + 36 * qB w F S t s * opNorm F.A ^ 2) +
          CS / Real.sqrt s * (e₂ + 3 * sigmaB w F S t s * opNorm F.A) +
          K / (s * Real.sqrt (B : ℝ))) := by
  obtain ⟨Cc, hCc0, hCc⟩ := pe_facts ϱ hϱ CS γ hγ
  obtain ⟨Kb, hKb⟩ := pe_b ϱ hϱ CS γ hγ
  obtain ⟨Ch, hCh⟩ := lem_app_drift_multiplier_ii_weights ϱ hϱ CS γ hγ
  obtain ⟨Cv, hCv⟩ := lem_app_drift_covariance_weights ϱ hϱ CS γ hγ
  have hsq0 : 0 < Real.sqrt ϱ := Real.sqrt_pos.2 hϱ
  refine ⟨|Kb| * |Ch| * |CS| / ϱ + |Cv| * |CS| / Real.sqrt ϱ, by positivity, ?_⟩
  intro Ω inst m n B P _ F S t j w hw hCo hCi hm hn s hs e₁ e₂ he₁ he₂ hr1 hr2
  have hsp : 0 < s := lt_of_lt_of_le hϱ hs
  have hCS : 0 ≤ CS := (tlb_opNorm_nonneg _).trans hCo
  have hw0 : 0 ≤ w j := hw.1.1 j
  have hw1 : w j ≤ 1 := hw.2.1 j
  have hB : 0 < B := F.hB
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hsB : 1 ≤ Real.sqrt (B : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hBr
  have hsB0 : 0 < Real.sqrt (B : ℝ) := lt_of_lt_of_le one_pos hsB
  have hw2 : w j ^ 2 ≤ w j := by rw [sq]; exact mul_le_of_le_one_right hw0 hw1
  have hw3 : w j ^ 3 ≤ w j := by
    calc w j ^ 3 = w j * w j ^ 2 := by ring
      _ ≤ 1 * w j := mul_le_mul hw1 hw2 (sq_nonneg _) zero_le_one
      _ = w j := one_mul _
  obtain ⟨hσ0, hσle, -, -, hq0, -⟩ := eqn_app_de_qI w hw F S t CS γ s {s}
    hsp (by intro x hx; rcases hx with rfl; exact le_rfl) ⟨hCo, hCi⟩ ⟨hm, hn⟩ s
    (Set.mem_singleton s)
  set σ := sigmaB w F S t s with hσdef
  set q := qB w F S t s with hqdef
  set x := w j ^ 2 * q with hxdef
  have hx0 : 0 ≤ x := mul_nonneg (sq_nonneg _) hq0
  obtain ⟨-, hA1, hA2, L1, L2, -, -, -, -⟩ := hCc Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs
  obtain ⟨hint2, -⟩ := pe_gram_decomp ϱ hϱ CS γ hγ Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs
  obtain ⟨hint1, -⟩ := pe_src_bessel P F S t j w CS hCo hCi hsp (delAlpha1 w F S t j s) hA1 L1
  have hT : (B : ℝ) • Muon.mean P (fun ω => delAlpha1 w F S t j s ω •
        (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))
      - delAlpha2 w F S t j s ω •
        (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))) =
      (B : ℝ) • Muon.mean P (fun ω => delAlpha1 w F S t j s ω •
        (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))) -
      (B : ℝ) • Muon.mean P (fun ω => delAlpha2 w F S t j s ω •
        (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))) := by
    rw [tl_mean_sub P _ _ hint1 hint2, smul_sub]
  rw [hT]
  set jx : ℝ := ∫ p, deriv (fX x) (resid F.A p) ∂(gaussPair m n) with hjxdef
  set b := bj w F S t j s with hbdef
  set a := opNorm F.A with hadef
  have ha0 : 0 ≤ a := tlb_opNorm_nonneg _
  have hD1 := pe_src_err ϱ hϱ CS γ hγ Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs x e₁
    hx0 he₁ hr1
  have hD2 := pe_gram_err ϱ hϱ CS γ hγ Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs x σ e₂
    hx0 hσ0 he₂ hr2
  rw [pe15p4_identity _ _ (Hmix w F S t s) (Hj w F S t j s) (Cj w F S t j s) (EG F) F.C.Sin
    (expDelRes w F S t j (slotOne F.hB) s) b (w j * jx)]
  obtain ⟨hb0, hb1⟩ := hKb Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs
  have hHm := hCh Ω m n B P F S t j w hw hCo hCi hm hn s hs
  obtain ⟨-, hCjb, -, -⟩ := hCv Ω m n B P F S t w ⟨hw.1.1, hw.1.2.1, hw.2.1, hw.2.2⟩ hCo hCi hm hn
    s hs
  have hι : 0 ≤ 1 / (s * Real.sqrt (B : ℝ)) := by positivity
  have hbn : b ≤ |Kb| * w j ^ 2 / s := by
    refine hb1.trans ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self Kb) (sq_nonneg _)) hsp.le
  have hHn : fro (Hmix w F S t s - Hj w F S t j s) ≤ |Ch| * w j * (1 / (s * Real.sqrt (B : ℝ))) := by
    refine hHm.trans ?_
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self Ch) hw0) (by positivity)
  have hs_ϱ : 1 / s ≤ 1 / ϱ := one_div_le_one_div_of_le hϱ hs
  have b6 : fro (b • ((Hmix w F S t s - Hj w F S t j s) * F.C.Sin)) ≤
      w j * (|Kb| * |Ch| * |CS| / ϱ * (1 / (s * Real.sqrt (B : ℝ)))) := by
    rw [tlb_fro_smul, abs_of_nonneg hb0]
    have h6 : fro ((Hmix w F S t s - Hj w F S t j s) * F.C.Sin) ≤
        |Ch| * w j * (1 / (s * Real.sqrt (B : ℝ))) * |CS| :=
      (tlb_fro_mul_le_right _ _).trans (mul_le_mul hHn (hCi.trans (le_abs_self CS))
        (tlb_opNorm_nonneg _) (by positivity))
    calc b * fro ((Hmix w F S t s - Hj w F S t j s) * F.C.Sin)
        ≤ (|Kb| * w j ^ 2 / s) * (|Ch| * w j * (1 / (s * Real.sqrt (B : ℝ))) * |CS|) :=
          mul_le_mul hbn h6 (tlb_fro_nonneg _) (by positivity)
      _ = (|Kb| * |Ch| * |CS|) * (w j ^ 3) * (1 / s) * (1 / (s * Real.sqrt (B : ℝ))) := by
          field_simp
      _ ≤ (|Kb| * |Ch| * |CS|) * (w j) * (1 / ϱ) * (1 / (s * Real.sqrt (B : ℝ))) := by
          have h0 : 0 ≤ |Kb| * |Ch| * |CS| := by positivity
          gcongr
      _ = _ := by ring
  have b7 : fro (Cj w F S t j s * F.C.Sin) ≤
      w j * (|Cv| * |CS| / Real.sqrt ϱ * (1 / (s * Real.sqrt (B : ℝ)))) := by
    refine (tlb_fro_mul_le_right _ _).trans ?_
    have hss : Real.sqrt ϱ ≤ Real.sqrt s := Real.sqrt_le_sqrt hs
    have hsqs : 0 < Real.sqrt s := lt_of_lt_of_le hsq0 hss
    have hc : fro (Cj w F S t j s) ≤
        |Cv| * w j * (1 / Real.sqrt ϱ) * (1 / (s * Real.sqrt (B : ℝ))) := by
      refine (hCjb j).trans ?_
      calc Cv * w j ^ 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ))
          ≤ |Cv| * w j ^ 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ)) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Cv) (sq_nonneg _))
              (by positivity)
        _ = |Cv| * w j ^ 2 * (1 / Real.sqrt s) * (1 / (s * Real.sqrt (B : ℝ))) := by
            field_simp
        _ ≤ |Cv| * w j * (1 / Real.sqrt ϱ) * (1 / (s * Real.sqrt (B : ℝ))) := by
            have h1 : 1 / Real.sqrt s ≤ 1 / Real.sqrt ϱ := one_div_le_one_div_of_le hsq0 hss
            gcongr
    calc fro (Cj w F S t j s) * opNorm F.C.Sin
        ≤ (|Cv| * w j * (1 / Real.sqrt ϱ) * (1 / (s * Real.sqrt (B : ℝ)))) * |CS| :=
          mul_le_mul hc (hCi.trans (le_abs_self CS)) (tlb_opNorm_nonneg _) (by positivity)
      _ = _ := by field_simp
  -- the two Gaussian-term bounds
  have c1 : fro ((B : ℝ) • Muon.mean P (fun ω => delAlpha1 w F S t j s ω •
            (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))) -
          (w j * jx) • (expDelRes w F S t j (slotOne F.hB) s * EG F)) ≤
      w j * (CS / s * (e₁ + 36 * q * a ^ 2)) := by
    refine hD1.trans ?_
    have hxq : x ≤ q := mul_le_of_le_one_left hq0 (by nlinarith)
    have ha2 : 0 ≤ a ^ 2 := sq_nonneg _
    have : 1 / s * CS * (w j * (36 * x * a ^ 2)) ≤ 1 / s * CS * (w j * (36 * q * a ^ 2)) := by
      gcongr
    calc _ ≤ CS / s * (w j * e₁) + 1 / s * CS * (w j * (36 * q * a ^ 2)) :=
          add_le_add le_rfl this
      _ = _ := by field_simp
  have c2 : fro ((B : ℝ) • Muon.mean P (fun ω => delAlpha2 w F S t j s ω •
            (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))) -
          (b • Hj w F S t j s + Cj w F S t j s) * F.C.Sin) ≤
      w j * (CS / Real.sqrt s * (e₂ + 3 * σ * a)) := by
    refine hD2.trans ?_
    have hsqs : 0 < Real.sqrt s := Real.sqrt_pos.2 hsp
    calc CS / (2 * Real.sqrt s) * (2 * (w j ^ 2 * e₂) + w j ^ 2 * σ * (6 * a))
        = w j ^ 2 * (CS / Real.sqrt s * (e₂ + 3 * σ * a)) := by field_simp; ring
      _ ≤ w j * (CS / Real.sqrt s * (e₂ + 3 * σ * a)) :=
          mul_le_mul_of_nonneg_right hw2 (by positivity)
  refine (pe15p4_fro_sub _ _).trans ((add_le_add ((tlb_fro_add _ _).trans
    (add_le_add (pe15p4_fro_sub _ _) b6)) b7).trans ?_)
  have hKs : (|Kb| * |Ch| * |CS| / ϱ + |Cv| * |CS| / Real.sqrt ϱ) / (s * Real.sqrt (B : ℝ)) =
      |Kb| * |Ch| * |CS| / ϱ * (1 / (s * Real.sqrt (B : ℝ))) +
        |Cv| * |CS| / Real.sqrt ϱ * (1 / (s * Real.sqrt (B : ℝ))) := by ring
  rw [hKs]
  linarith [c1, c2]

end Pe15Term

section Pe15Supp
open ProbabilityTheory

private lemma pe15p4_inner_le {p q : ℕ} (K : Mat p q) (x : Fin q → ℝ) (y : Fin p → ℝ) :
    ∑ k, y k * (K *ᵥ x) k ≤
      opNorm K * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2) := by
  have hT : ‖Matrix.toEuclideanLin K (WithLp.toLp 2 x)‖ ≤ opNorm K * ‖WithLp.toLp 2 x‖ := by
    exact (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)).le_opNorm _
  have hin := real_inner_le_norm (WithLp.toLp 2 y) (Matrix.toEuclideanLin K (WithLp.toLp 2 x))
  have hx : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin q))‖ = Real.sqrt (∑ i, x i ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [Real.norm_eq_abs, sq_abs]
  have hy : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin p))‖ = Real.sqrt (∑ i, y i ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [Real.norm_eq_abs, sq_abs]
  have hi : inner ℝ (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin p))
      (Matrix.toEuclideanLin K (WithLp.toLp 2 x)) = ∑ k, y k * (K *ᵥ x) k := by
    simp [PiLp.inner_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply, mul_comm]
  rw [← hi]
  rw [hx] at hT; rw [hy] at hin
  calc _ ≤ _ := hin
    _ ≤ Real.sqrt (∑ i, y i ^ 2) * (opNorm K * Real.sqrt (∑ i, x i ^ 2)) :=
        mul_le_mul_of_nonneg_left hT (Real.sqrt_nonneg _)
    _ = _ := by ring

private lemma pe15p4_opNorm_le_bil {p q : ℕ} (K : Mat p q) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ (x : Fin q → ℝ) (y : Fin p → ℝ),
      ∑ k, y k * (K *ᵥ x) k ≤ M * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2)) :
    opNorm K ≤ M := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x => ?_
  show ‖Matrix.toEuclideanLin K x‖ ≤ M * ‖x‖
  have hx : ‖x‖ = Real.sqrt (∑ i, (WithLp.ofLp x) i ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [Real.norm_eq_abs, sq_abs]
  set v : Fin p → ℝ := K *ᵥ (WithLp.ofLp x) with hv
  have hn : ‖Matrix.toEuclideanLin K x‖ = Real.sqrt (∑ i, v i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp [Real.norm_eq_abs, sq_abs, hv, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  have := h (WithLp.ofLp x) v
  have hs : ∑ k, v k * (K *ᵥ WithLp.ofLp x) k = (Real.sqrt (∑ i, v i ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]; simp [hv, sq]
  rw [hs, ← hx] at this
  rw [hn]
  set a := Real.sqrt (∑ i, v i ^ 2)
  by_cases ha : a = 0
  · rw [ha]; positivity
  · have ha' : 0 < a := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm ha)
    nlinarith


private lemma pe15p4_summable_mat {p q : ℕ} (f : ℕ → Mat p q) (c : ℕ → ℝ)
    (hf : ∀ j i k, |f j i k| ≤ c j) (hc : Summable c) : Summable f :=
  Pi.summable.2 fun i => Pi.summable.2 fun k =>
    Summable.of_norm_bounded hc (fun j => by simpa using hf j i k)

private lemma pe15p4_hasSum_entry {p q : ℕ} {f : ℕ → Mat p q} {S : Mat p q} (h : HasSum f S)
    (i : Fin p) (k : Fin q) : HasSum (fun j => f j i k) (S i k) :=
  Pi.hasSum.1 (Pi.hasSum.1 h i) k

private lemma pe15p4_opNorm_hasSum {p q : ℕ} (f : ℕ → Mat p q) (S : Mat p q) (c : ℕ → ℝ)
    (hf : HasSum f S) (hc : Summable c) (hfc : ∀ j, opNorm (f j) ≤ c j) :
    opNorm S ≤ ∑' j, c j := by
  have hc0 : ∀ j, 0 ≤ c j := fun j => (tlb_opNorm_nonneg _).trans (hfc j)
  have hM : 0 ≤ ∑' j, c j := tsum_nonneg hc0
  refine pe15p4_opNorm_le_bil S _ hM fun x y => ?_
  have hent : ∀ k i, HasSum (fun j => y k * x i * f j k i) (y k * x i * S k i) :=
    fun k i => (pe15p4_hasSum_entry hf k i).mul_left _
  have hsum : HasSum (fun j => ∑ k, ∑ i, y k * x i * f j k i) (∑ k, ∑ i, y k * x i * S k i) :=
    hasSum_sum (fun k _ => hasSum_sum (fun i _ => hent k i))
  have hconv : ∀ T : Mat p q, ∑ k, y k * (T *ᵥ x) k = ∑ k, ∑ i, y k * x i * T k i := by
    intro T
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hb : HasSum (fun j => c j * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2))
      ((∑' j, c j) * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2)) :=
    (hc.hasSum.mul_right _).mul_right _
  rw [hconv]
  refine hasSum_le (fun j => ?_) hsum hb
  rw [← hconv]
  calc _ ≤ opNorm (f j) * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2) :=
        pe15p4_inner_le _ x y
    _ ≤ c j * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2) := by
        gcongr; exact hfc j
    _ = _ := by ring

private lemma pe15p4_opNorm_le_Y {p n : ℕ} (D : Mat p n) (S : Mat n n) (hS : S.PosSemidef)
    {b : ℝ} (hb : 0 ≤ b) : opNorm D ≤ opNorm (D * ((1 : Mat n n) + b • S)) := by
  set Y : Mat n n := (1 : Mat n n) + b • S with hY
  have hdet : IsUnit Y.det := by
    have h2 : ((1 : ℝ) • (1 : Mat n n)).PosDef := Matrix.PosDef.one.smul one_pos
    have h1 : (b • S).PosSemidef := hS.smul hb
    have h3 := Matrix.PosDef.add_posSemidef h2 h1
    rw [one_smul] at h3
    exact isUnit_iff_ne_zero.mpr h3.det_pos.ne'
  have hinv : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv Y hdet
  have hD : D = (D * Y) * Y⁻¹ := by rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  have hYinv : opNorm Y⁻¹ ≤ 1 := by
    have := kern_inv_opNorm_le S hS hb one_pos
    simpa [hY] using this
  calc opNorm D = opNorm ((D * Y) * Y⁻¹) := by rw [← hD]
    _ ≤ opNorm (D * Y) * opNorm Y⁻¹ := tlb_opNorm_mul_le _ _
    _ ≤ opNorm (D * Y) * 1 := mul_le_mul_of_nonneg_left hYinv (tlb_opNorm_nonneg _)
    _ = _ := mul_one _

private lemma pe15p4_opNorm_le_fro {m n : ℕ} (K : Mat m n) : opNorm K ≤ fro K := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, fro,
    ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have hK : ∀ i, ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)) x).ofLp i =
      ∑ j, K i j * x.ofLp j := fun i => by
    simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
  have hi : ∀ i, ‖∑ j, K i j * x.ofLp j‖ ^ 2 ≤
      (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) := by
    intro i
    calc
      ‖∑ j, K i j * x.ofLp j‖ ^ 2 ≤ (∑ j, ‖K i j‖ * ‖x.ofLp j‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
        exact norm_mul _ _
      _ ≤ (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc
    ∑ i, ‖((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)) x).ofLp i‖ ^ 2 =
        ∑ i, ‖∑ j, K i j * x.ofLp j‖ ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [hK i]
    _ ≤ ∑ i, (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => hi i
    _ = (∑ i, ∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) :=
      (Finset.sum_mul _ _ _).symm

private lemma pe15p4_EG_op {m n B : ℕ} (F : FrozenParams m n B) {CS : ℝ}
    (hCo : opNorm F.C.Sout ≤ CS) (hCi : opNorm F.C.Sin ≤ CS) : opNorm (EG F) ≤ CS * opNorm F.A := by
  have hCS0 : 0 ≤ CS := (tlb_opNorm_nonneg _).trans hCo
  have hro0 : 0 ≤ opNorm (rOut F.C) := tlb_opNorm_nonneg _
  have hri0 : 0 ≤ opNorm (rIn F.C) := tlb_opNorm_nonneg _
  have hrr : opNorm (rOut F.C) * opNorm (rIn F.C) ≤ CS := by
    have h1 : (opNorm (rOut F.C) * opNorm (rIn F.C)) ^ 2 ≤ CS ^ 2 := by
      have e1 := tlb_opNorm_rOut_mul_self F.C
      have e2 := tlb_opNorm_rIn_mul_self F.C
      calc (opNorm (rOut F.C) * opNorm (rIn F.C)) ^ 2
          = (opNorm (rOut F.C) * opNorm (rOut F.C)) * (opNorm (rIn F.C) * opNorm (rIn F.C)) := by ring
        _ ≤ CS * CS := by rw [e1, e2]; exact mul_le_mul hCo hCi (tlb_opNorm_nonneg _) hCS0
        _ = CS ^ 2 := by ring
    exact abs_le_of_sq_le_sq' h1 hCS0 |>.2
  unfold EG
  calc opNorm (rOut F.C * F.A * rIn F.C)
      ≤ opNorm (rOut F.C * F.A) * opNorm (rIn F.C) := tlb_opNorm_mul_le _ _
    _ ≤ (opNorm (rOut F.C) * opNorm F.A) * opNorm (rIn F.C) :=
        mul_le_mul_of_nonneg_right (tlb_opNorm_mul_le _ _) hri0
    _ = (opNorm (rOut F.C) * opNorm (rIn F.C)) * opNorm F.A := by ring
    _ ≤ CS * opNorm F.A := mul_le_mul_of_nonneg_right hrr (tlb_opNorm_nonneg _)

private lemma pe15p4_expDel_op {Ω : Type} [inst : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) {s : ℝ} (hs : 0 < s) :
    opNorm (expDelRes w F S t j (slotOne F.hB) s) ≤ 1 / s := by
  obtain ⟨hG, -⟩ := tl_indep F S t j
  have hM0 : Measurable (delBufAge w F S t j) := (tl_meas_del w F S t j).mono hG le_rfl
  have hRm : Measurable (fun M : Mat m n => Rs M s) := (tlc_Rs_continuous s hs).measurable
  have hint : ∀ i k, Integrable (fun ω => Rs (delBufAge w F S t j ω) s i k) P := by
    intro i k
    have hik : Measurable (fun M : Mat m m => M i k) :=
      (measurable_pi_apply k).comp (measurable_pi_apply i)
    refine Integrable.of_bound ((hik.comp (hRm.comp hM0)).aestronglyMeasurable) (1 / s)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact (tlc_abs_entry_le _ i k).trans (lem_app_de_resolvent _ s hs).1
  exact gh_opNorm_mean P _ hint (1 / s) (by positivity) fun ω => (lem_app_de_resolvent _ s hs).1

private lemma pe15p4_jx_le {m n : ℕ} (A : Mat m n) {x : ℝ} (hx : 0 ≤ x) :
    |∫ p, deriv (fX x) (resid A p) ∂(gaussPair m n)| ≤ 1 := by
  obtain ⟨hcd, -, hb1, -⟩ := gc_f_hyp hx
  have := norm_integral_le_of_norm_le_const (μ := gaussPair m n)
    (f := fun p => deriv (fX x) (resid A p)) (C := 1)
    (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hb1 _)
  simpa using this


open scoped Matrix.Norms.L2Operator in
private lemma pe15p4_opNorm_add_le {a b : ℕ} (A B' : Mat a b) :
    opNorm (A + B') ≤ opNorm A + opNorm B' := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact norm_add_le _ _

open scoped Matrix.Norms.L2Operator in
private lemma pe15p4_opNorm_smul {a b : ℕ} (c : ℝ) (A : Mat a b) :
    opNorm (c • A) = |c| * opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, norm_smul, Real.norm_eq_abs]

end Pe15Supp

/-- `eqn:app-dyn-H-op`, snapshot `cr-2026-10-23` (`sections/05-dynamics/section.tex` ll. 939–972):
the operator-norm response bound with the state dependence displayed.
```latex
The proof of \cref{prop:app-drift-response}, run with these targets and
with the expected deleted resolvent $\mathcal P_j(s)$ kept in place of
$\Rbar(-s)$, gives an equation for $\mathcal H(s)$ in which every error is
displayed with its dependence on $\norm{\Ahat}$.
[...]
\[
\mathcal H(s)\,\mathsf Y_B(s)=\sum_j\emaw j\,\jmath_j\,\mathcal P_j(s)\,\EE\Gt+E_1(s),
\]
\[
\norm{E_1(s)}_\F\le C\Big[\frac{\mathsf e^{(1)}_B(s)}{s}+\frac{q_B(s)\norm{\Ahat}^2}{s}+\frac{\mathsf e^{(2)}_B(s)+\sigma_B(s)\norm{\Ahat}}{\sqrt s}+\frac{1}{s\sqrt B}\Big]\qquad(s\ge\ridge),
\]
with $C$ depending on $\ridge$. [...] Since $b_B(s)\ge0$,
$\norm{\mathsf Y_B(s)^{-1}}\le1$, and with $q_B,\sigma_B\le C/s$,
\begin{equation}\label{eqn:app-dyn-H-op}
\norm{\mathcal H(s)}\le C\Big(\frac1s+\frac1{s^{3/2}}+\frac1{s^2}\Big)\norm{\Ahat}+\mathsf e_B(s),\qquad
\mathsf e_B(s)\defeq C\Big[\frac{\mathsf e^{(1)}_B(s)}{s}+\frac{\mathsf e^{(2)}_B(s)}{\sqrt s}+\frac{1}{s\sqrt B}\Big],
\end{equation}
for $s\ge\ridge$.
```
Encoding: for a fixed `ϱ > 0` one `C` (depending only on `(ϱ, C_Σ, γ⋆)`, chosen before all data)
serves every finite model with `max(N_in,N_out) ≤ γ⋆B`, `‖Σ‖ ≤ C_Σ`, every weight sequence in the
class, every normalized state (the field `F.A`, `‖Â‖_F = 1`, with no condition on `‖Â‖`) and every
`s ≥ ϱ`. `e^{(1)}_B(s)`, `e^{(2)}_B(s)` enter as any upper bounds `ε₁`, `ε₂` of the replacement
errors over all ages (equivalent to the source's suprema, which may be `+∞` a priori). Norms: `‖·‖`
is `opNorm`. -/
theorem eqn_app_dyn_H_op (ϱ CS γ : ℝ) (hϱ : 0 < ϱ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (w : ℕ → ℝ) (F : FrozenParams m n B)
      (S : FrozenSamples P m n B) (t : ℤ),
      WeightClass w → opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, ϱ ≤ s → ∀ ε₁ ε₂ : ℝ, 0 ≤ ε₁ → 0 ≤ ε₂ →
      (∀ j : ℕ, eLpNorm (fun ω => delAlpha1 w F S t j s ω - checkAlpha1 w F S t j s ω) 2 P
          ≤ ENNReal.ofReal (w j * ε₁)) →
      (∀ j : ℕ, eLpNorm (fun ω => delAlpha2 w F S t j s ω - checkAlpha2 w F S t j s ω) 2 P
          ≤ ENNReal.ofReal (w j ^ 2 * ε₂)) →
        opNorm (Hmix w F S t s) ≤
          C * (1 / s + 1 / (s * Real.sqrt s) + 1 / s ^ 2) * opNorm F.A +
            C * (ε₁ / s + ε₂ / Real.sqrt s + 1 / (s * Real.sqrt (B : ℝ))) := by
  obtain ⟨K, hK0, hK⟩ := pe15p4_term ϱ hϱ CS (max γ 0) (le_max_right _ _)
  obtain ⟨Kb, hKb⟩ := pe_b ϱ hϱ CS (max γ 0) (le_max_right _ _)
  refine ⟨|CS| + 36 * |CS| * (|CS| * max γ 0) ^ 2 + 3 * |CS| * (|CS| * max γ 0) + K, ?_⟩
  intro Ω inst m n B P _ w F S t hw hCo hCi hm hn s hs ε₁ ε₂ hε₁ hε₂ hr1 hr2
  have hsp : 0 < s := lt_of_lt_of_le hϱ hs
  have hCS : 0 ≤ CS := (tlb_opNorm_nonneg _).trans hCo
  have hγp0 : 0 ≤ max γ 0 := le_max_right _ _
  have hmp : (m : ℝ) ≤ max γ 0 * B :=
    hm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg B))
  have hnp : (n : ℝ) ≤ max γ 0 * B :=
    hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg B))
  have hB : 0 < B := F.hB
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hsB0 : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsqs : 0 < Real.sqrt s := Real.sqrt_pos.2 hsp
  obtain ⟨hσ0, hσle, -, -, hq0, hqle⟩ := eqn_app_de_qI w hw F S t CS (max γ 0) s {s}
    hsp (by intro x hx; rcases hx with rfl; exact le_rfl) ⟨hCo, hCi⟩ ⟨hmp, hnp⟩ s
    (Set.mem_singleton s)
  set σ := sigmaB w F S t s with hσdef
  set q := qB w F S t s with hqdef
  set a := opNorm F.A with hadef
  have ha0 : 0 ≤ a := tlb_opNorm_nonneg _
  have ha1 : a ≤ 1 := (pe15p4_opNorm_le_fro F.A).trans (le_of_eq F.hA)
  set Θ : ℝ := CS / s * (ε₁ + 36 * q * a ^ 2) + CS / Real.sqrt s * (ε₂ + 3 * σ * a) +
    K / (s * Real.sqrt (B : ℝ)) with hΘdef
  have hΘ0 : 0 ≤ Θ := by positivity
  have hsw : Summable w := hw.1.2.1
  have hexact := lem_app_drift_exact_weights hw F S t s hsp
  have hbj := fun j => hKb Ω m n B P F S t j w (hw.1.1 j) (hw.2.1 j) hCo hCi hmp hnp s hs
  have hbs : Summable (fun j => bj w F S t j s) := by
    refine Summable.of_nonneg_of_le (fun j => (hbj j).1) (fun j => ?_)
      ((hsw.mul_left |Kb|).div_const s)
    refine (hbj j).2.trans ?_
    have hw2 : w j ^ 2 ≤ w j := by
      rw [sq]; exact mul_le_of_le_one_right (hw.1.1 j) (hw.2.1 j)
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_right (le_abs_self Kb) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hw2 (abs_nonneg _))) hsp.le
  obtain ⟨u, hu⟩ : ∃ u : ℕ → Mat m n, ∀ j, u j =
      (w j * ∫ p, deriv (fX (w j ^ 2 * qB w F S t s)) (resid F.A p) ∂(gaussPair m n)) •
        (expDelRes w F S t j (slotOne F.hB) s * EG F) := ⟨_, fun _ => rfl⟩
  have hu_op : ∀ j, opNorm (u j) ≤ w j * (CS * a / s) := by
    intro j
    rw [hu, pe15p4_opNorm_smul, abs_mul, abs_of_nonneg (hw.1.1 j)]
    have hx0 : 0 ≤ w j ^ 2 * q := mul_nonneg (sq_nonneg _) hq0
    have hjx := pe15p4_jx_le F.A hx0
    have hPE : opNorm (expDelRes w F S t j (slotOne F.hB) s * EG F) ≤ CS * a / s := by
      refine (tlb_opNorm_mul_le _ _).trans ?_
      have h1 := pe15p4_expDel_op w F S t j hsp
      have h2 := pe15p4_EG_op F hCo hCi
      calc _ ≤ 1 / s * (CS * a) := mul_le_mul h1 h2 (tlb_opNorm_nonneg _) (by positivity)
        _ = _ := by ring
    calc w j * |∫ p, deriv (fX (w j ^ 2 * qB w F S t s)) (resid F.A p) ∂(gaussPair m n)| *
          opNorm (expDelRes w F S t j (slotOne F.hB) s * EG F)
        ≤ w j * 1 * (CS * a / s) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hjx (hw.1.1 j)) hPE
            (tlb_opNorm_nonneg _) (by have := hw.1.1 j; positivity)
      _ = _ := by ring
  have hcs : 0 ≤ CS * a / s := by positivity
  have hu_sum : Summable u := pe15p4_summable_mat u (fun j => w j * (CS * a / s))
    (fun j i k => (pe15p4_abs_entry_le_opNorm _ i k).trans (hu_op j)) (hsw.mul_right _)
  have hg := (hexact.add (hbs.hasSum.smul_const (Hmix w F S t s * F.C.Sin))).sub hu_sum.hasSum
  have hterm : ∀ j, fro ((B : ℝ) • Muon.mean P (fun ω => delAlpha1 w F S t j s ω •
              (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))
            - delAlpha2 w F S t j s ω •
              (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))) +
          bj w F S t j s • (Hmix w F S t s * F.C.Sin) - u j) ≤ w j * Θ := by
    intro j
    rw [hu]
    exact hK Ω m n B P F S t j w hw hCo hCi hmp hnp s hs ε₁ ε₂ hε₁ hε₂ (hr1 j) (hr2 j)
  have hEr : fro ((Hmix w F S t s + (∑' j, bj w F S t j s) • (Hmix w F S t s * F.C.Sin)) -
      ∑' j, u j) ≤ Θ := by
    refine (tl_fro_hasSum _ _ (fun j => w j * Θ) hg (hsw.mul_right _) hterm
      (fun j => mul_nonneg (hw.1.1 j) hΘ0)).trans ?_
    rw [tsum_mul_right]
    exact mul_le_of_le_one_left hΘ0 hw.2.2
  have hSu : opNorm (∑' j, u j) ≤ CS * a / s := by
    refine (pe15p4_opNorm_hasSum u _ (fun j => w j * (CS * a / s)) hu_sum.hasSum
      (hsw.mul_right _) hu_op).trans ?_
    rw [tsum_mul_right]
    exact mul_le_of_le_one_left hcs hw.2.2
  have hYeq : Hmix w F S t s * YB w F S t s =
      ((Hmix w F S t s + (∑' j, bj w F S t j s) • (Hmix w F S t s * F.C.Sin)) -
        ∑' j, u j) + ∑' j, u j := by
    rw [sub_add_cancel]
    unfold YB bB
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hb0 : 0 ≤ bB w F S t s := tsum_nonneg (fun j => (hbj j).1)
  have hH : opNorm (Hmix w F S t s) ≤ opNorm (Hmix w F S t s * YB w F S t s) :=
    pe15p4_opNorm_le_Y (Hmix w F S t s) F.C.Sin F.C.psdIn hb0
  have hfin : opNorm (Hmix w F S t s) ≤ CS * a / s + Θ := by
    refine hH.trans ?_
    rw [hYeq]
    refine (pe15p4_opNorm_add_le _ _).trans ?_
    have := (pe15p4_opNorm_le_fro ((Hmix w F S t s + (∑' j, bj w F S t j s) •
      (Hmix w F S t s * F.C.Sin)) - ∑' j, u j)).trans hEr
    linarith
  have hCS' : |CS| = CS := abs_of_nonneg hCS
  rw [hCS']
  have ha2 : a ^ 2 ≤ a := pow_le_of_le_one ha0 ha1 (by norm_num)
  have hT2 : CS / s * (36 * q * a ^ 2) ≤ 36 * CS * (CS * max γ 0) ^ 2 * (1 / s ^ 2) * a := by
    have h1 : q * a ^ 2 ≤ (CS * max γ 0) ^ 2 / s * a :=
      mul_le_mul hqle ha2 (sq_nonneg _) (by positivity)
    calc CS / s * (36 * q * a ^ 2) = CS / s * 36 * (q * a ^ 2) := by ring
      _ ≤ CS / s * 36 * ((CS * max γ 0) ^ 2 / s * a) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by field_simp
  have hT3 : CS / Real.sqrt s * (3 * σ * a) ≤
      3 * CS * (CS * max γ 0) * (1 / (s * Real.sqrt s)) * a := by
    have h1 : σ * a ≤ CS * max γ 0 / s * a := mul_le_mul_of_nonneg_right hσle ha0
    calc CS / Real.sqrt s * (3 * σ * a) = CS / Real.sqrt s * 3 * (σ * a) := by ring
      _ ≤ CS / Real.sqrt s * 3 * (CS * max γ 0 / s * a) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by field_simp
  have hΘ' : Θ = CS * (ε₁ / s) + CS * (ε₂ / Real.sqrt s) + K * (1 / (s * Real.sqrt (B : ℝ))) +
      CS / s * (36 * q * a ^ 2) + CS / Real.sqrt s * (3 * σ * a) := by
    simp only [hΘdef]; field_simp; ring
  have hX1 : CS * a / s = CS * (1 / s) * a := by field_simp
  have hL : 0 ≤ (36 * CS * (CS * max γ 0) ^ 2 + 3 * CS * (CS * max γ 0) + K) * (1 / s) * a +
      (CS + 36 * CS * (CS * max γ 0) ^ 2 + K) * (1 / (s * Real.sqrt s)) * a +
      (CS + 3 * CS * (CS * max γ 0) + K) * (1 / s ^ 2) * a +
      (36 * CS * (CS * max γ 0) ^ 2 + 3 * CS * (CS * max γ 0) + K) * (ε₁ / s) +
      (36 * CS * (CS * max γ 0) ^ 2 + 3 * CS * (CS * max γ 0) + K) * (ε₂ / Real.sqrt s) +
      (CS + 36 * CS * (CS * max γ 0) ^ 2 + 3 * CS * (CS * max γ 0)) *
        (1 / (s * Real.sqrt (B : ℝ))) := by positivity
  have hRHS : (CS + 36 * CS * (CS * max γ 0) ^ 2 + 3 * CS * (CS * max γ 0) + K) *
        (1 / s + 1 / (s * Real.sqrt s) + 1 / s ^ 2) * a +
      (CS + 36 * CS * (CS * max γ 0) ^ 2 + 3 * CS * (CS * max γ 0) + K) *
        (ε₁ / s + ε₂ / Real.sqrt s + 1 / (s * Real.sqrt (B : ℝ))) =
      (CS * (1 / s) * a + 3 * CS * (CS * max γ 0) * (1 / (s * Real.sqrt s)) * a +
        36 * CS * (CS * max γ 0) ^ 2 * (1 / s ^ 2) * a + CS * (ε₁ / s) + CS * (ε₂ / Real.sqrt s) +
        K * (1 / (s * Real.sqrt (B : ℝ)))) +
      ((36 * CS * (CS * max γ 0) ^ 2 + 3 * CS * (CS * max γ 0) + K) * (1 / s) * a +
      (CS + 36 * CS * (CS * max γ 0) ^ 2 + K) * (1 / (s * Real.sqrt s)) * a +
      (CS + 3 * CS * (CS * max γ 0) + K) * (1 / s ^ 2) * a +
      (36 * CS * (CS * max γ 0) ^ 2 + 3 * CS * (CS * max γ 0) + K) * (ε₁ / s) +
      (36 * CS * (CS * max γ 0) ^ 2 + 3 * CS * (CS * max γ 0) + K) * (ε₂ / Real.sqrt s) +
      (CS + 36 * CS * (CS * max γ 0) ^ 2 + 3 * CS * (CS * max γ 0)) *
        (1 / (s * Real.sqrt (B : ℝ)))) := by ring
  rw [hRHS]
  linarith [hfin, hΘ', hX1, hT2, hT3, hL]

private lemma pe15p4_opNorm_integral {p q : ℕ} (K : Mat p q) (φ : ℝ → Mat p q) (g : ℝ → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hK : ∀ i j, K i j = c * ∫ u in Ioi (0 : ℝ), φ u i j)
    (hint : ∀ i j, IntegrableOn (fun u => φ u i j) (Ioi (0 : ℝ)))
    (hg : IntegrableOn g (Ioi (0 : ℝ)))
    (hφ : ∀ u ∈ Ioi (0 : ℝ), opNorm (φ u) ≤ g u) :
    opNorm K ≤ c * ∫ u in Ioi (0 : ℝ), g u := by
  have hg0 : 0 ≤ ∫ u in Ioi (0 : ℝ), g u :=
    setIntegral_nonneg measurableSet_Ioi fun u hu =>
      (norm_nonneg _ : (0:ℝ) ≤ opNorm (φ u)).trans (hφ u hu)
  refine pe15p4_opNorm_le_bil K _ (mul_nonneg hc hg0) fun x y => ?_
  have hsum : ∀ u, ∑ k, y k * (φ u *ᵥ x) k = ∑ k, ∑ j, y k * x j * φ u k j := by
    intro u
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hL : ∑ k, y k * (K *ᵥ x) k =
      c * ∫ u in Ioi (0 : ℝ), ∑ k, y k * (φ u *ᵥ x) k := by
    have : ∀ u, ∑ k, y k * (φ u *ᵥ x) k = ∑ k, ∑ j, y k * x j * φ u k j := hsum
    simp_rw [this]
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun j _ =>
      (hint k j).const_mul _)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hint k j).const_mul _), Finset.mul_sum]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, hK k j]; ring
  have hI : IntegrableOn (fun u => ∑ k, y k * (φ u *ᵥ x) k) (Ioi (0 : ℝ)) := by
    have : ∀ u, ∑ k, y k * (φ u *ᵥ x) k = ∑ k, ∑ j, y k * x j * φ u k j := hsum
    simp_rw [this]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
      (hint k j).const_mul _
  rw [hL]
  have hle : ∫ u in Ioi (0 : ℝ), ∑ k, y k * (φ u *ᵥ x) k ≤
      ∫ u in Ioi (0 : ℝ), g u * (Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2)) := by
    refine setIntegral_mono_on hI (hg.mul_const _) measurableSet_Ioi fun u hu => ?_
    calc _ ≤ opNorm (φ u) * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2) :=
          pe15p4_inner_le _ x y
      _ ≤ g u * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2) := by
          gcongr
          exact hφ u hu
      _ = _ := by ring
  rw [integral_mul_const] at hle
  calc _ ≤ c * ((∫ u in Ioi (0 : ℝ), g u) * (Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2))) :=
        mul_le_mul_of_nonneg_left hle hc
    _ = _ := by ring


private lemma pe15p4_g_int (M0 ce T R : ℝ) (hR : 0 < R) (g : ℝ → ℝ)
    (hg : ∀ u, g u = M0 * (1 + u ^ 2)⁻¹ + (Ioc (0 : ℝ) R).indicator (fun _ => ce) u +
      (Ioi R).indicator (fun v : ℝ => T * v ^ (-2 : ℝ)) u) :
    IntegrableOn g (Ioi (0 : ℝ)) ∧
    ∫ u in Ioi (0 : ℝ), g u = M0 * (Real.pi / 2) + ce * R + T / R := by
  have hgf : g = fun u => M0 * (1 + u ^ 2)⁻¹ + (Ioc (0 : ℝ) R).indicator (fun _ => ce) u +
      (Ioi R).indicator (fun v : ℝ => T * v ^ (-2 : ℝ)) u := funext hg
  have h1 : IntegrableOn (fun u : ℝ => M0 * (1 + u ^ 2)⁻¹) (Ioi (0 : ℝ)) :=
    (integrable_inv_one_add_sq.const_mul M0).integrableOn
  have h2 : IntegrableOn ((Ioc (0 : ℝ) R).indicator (fun _ => ce)) (Ioi (0 : ℝ)) := by
    have : Integrable ((Ioc (0 : ℝ) R).indicator (fun _ => ce)) volume :=
      (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
    exact this.integrableOn
  have h3 : IntegrableOn ((Ioi R).indicator (fun v : ℝ => T * v ^ (-2 : ℝ))) (Ioi (0 : ℝ)) := by
    have : Integrable ((Ioi R).indicator (fun v : ℝ => T * v ^ (-2 : ℝ))) volume :=
      (integrable_indicator_iff measurableSet_Ioi).2
        ((integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hR).const_mul T)
    exact this.integrableOn
  have e1 : ∫ u in Ioi (0 : ℝ), M0 * (1 + u ^ 2)⁻¹ = M0 * (Real.pi / 2) := by
    rw [integral_const_mul, integral_Ioi_inv_one_add_sq]; simp
  have e2 : ∫ u in Ioi (0 : ℝ), (Ioc (0 : ℝ) R).indicator (fun _ => ce) u = ce * R := by
    rw [setIntegral_indicator measurableSet_Ioc]
    have : Ioi (0 : ℝ) ∩ Ioc 0 R = Ioc 0 R := by
      ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; tauto
    rw [this, setIntegral_const]
    simp [hR.le, mul_comm]
  have e3 : ∫ u in Ioi (0 : ℝ), (Ioi R).indicator (fun v : ℝ => T * v ^ (-2 : ℝ)) u = T / R := by
    rw [setIntegral_indicator measurableSet_Ioi]
    have : Ioi (0 : ℝ) ∩ Ioi R = Ioi R := by
      ext x; simp only [mem_inter_iff, mem_Ioi]; constructor
      · exact fun h => h.2
      · exact fun h => ⟨hR.trans h, h⟩
    rw [this, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hR]
    have : R ^ (-2 + 1 : ℝ) = R⁻¹ := by
      rw [show (-2 + 1 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    rw [this]; field_simp; norm_num
  subst hgf
  refine ⟨(h1.add h2).add h3, ?_⟩
  rw [integral_add (f := fun u => M0 * (1 + u ^ 2)⁻¹ + (Ioc (0 : ℝ) R).indicator (fun _ => ce) u)
    (g := fun u => (Ioi R).indicator (fun v : ℝ => T * v ^ (-2 : ℝ)) u) (h1.add h2) h3,
    integral_add h1 h2, e1, e2, e3]


private lemma pe15p4_F1 {ϱ : ℝ} (hϱ : 0 < ϱ) (u : ℝ) :
    1 / (ϱ + u ^ 2) + 1 / ((ϱ + u ^ 2) * Real.sqrt (ϱ + u ^ 2)) + 1 / (ϱ + u ^ 2) ^ 2 ≤
      (1 + 1 / Real.sqrt ϱ + 1 / ϱ) / min ϱ 1 * (1 + u ^ 2)⁻¹ := by
  have hμ : 0 < min ϱ 1 := lt_min hϱ one_pos
  have hs : ϱ ≤ ϱ + u ^ 2 := by nlinarith [sq_nonneg u]
  have hs0 : 0 < ϱ + u ^ 2 := by nlinarith [sq_nonneg u]
  have hsq : 0 < Real.sqrt ϱ := Real.sqrt_pos.2 hϱ
  have hsqs : Real.sqrt ϱ ≤ Real.sqrt (ϱ + u ^ 2) := Real.sqrt_le_sqrt hs
  have hmu : min ϱ 1 * (1 + u ^ 2) ≤ ϱ + u ^ 2 := by
    have h1 := min_le_left ϱ 1
    have h2 := min_le_right ϱ 1
    nlinarith [sq_nonneg u]
  have hinv : 1 / (ϱ + u ^ 2) ≤ 1 / min ϱ 1 * (1 + u ^ 2)⁻¹ := by
    calc 1 / (ϱ + u ^ 2) ≤ 1 / (min ϱ 1 * (1 + u ^ 2)) :=
          one_div_le_one_div_of_le (by positivity) hmu
      _ = _ := by field_simp
  have hsum : 1 / (ϱ + u ^ 2) + 1 / ((ϱ + u ^ 2) * Real.sqrt (ϱ + u ^ 2)) +
      1 / (ϱ + u ^ 2) ^ 2 ≤ (1 + 1 / Real.sqrt ϱ + 1 / ϱ) * (1 / (ϱ + u ^ 2)) := by
    have a2 : 1 / ((ϱ + u ^ 2) * Real.sqrt (ϱ + u ^ 2)) ≤ 1 / Real.sqrt ϱ * (1 / (ϱ + u ^ 2)) := by
      rw [one_div_mul_one_div]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have a3 : 1 / (ϱ + u ^ 2) ^ 2 ≤ 1 / ϱ * (1 / (ϱ + u ^ 2)) := by
      rw [one_div_mul_one_div]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    nlinarith
  calc _ ≤ _ := hsum
    _ ≤ (1 + 1 / Real.sqrt ϱ + 1 / ϱ) * (1 / min ϱ 1 * (1 + u ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by ring

private lemma pe15p4_F2 {ϱ : ℝ} (hϱ : 0 < ϱ) (E : ℝ) (hE : 0 ≤ E) (B : ℕ) {u : ℝ} (hu : 0 < u) :
    E / (ϱ + u ^ 2) + (E / (ϱ + u ^ 2)) / Real.sqrt (ϱ + u ^ 2) +
        1 / ((ϱ + u ^ 2) * Real.sqrt (B : ℝ)) ≤
      (E + E / Real.sqrt ϱ + 1) * u ^ (-2 : ℝ) := by
  have hu2 : 0 < u ^ 2 := by positivity
  have hs0 : 0 < ϱ + u ^ 2 := by positivity
  have hs : u ^ 2 ≤ ϱ + u ^ 2 := by linarith
  have hsq : 0 < Real.sqrt ϱ := Real.sqrt_pos.2 hϱ
  have hsqs : Real.sqrt ϱ ≤ Real.sqrt (ϱ + u ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hr : u ^ (-2 : ℝ) = 1 / u ^ 2 := by
    rw [Real.rpow_neg hu.le, Real.rpow_two, one_div]
  have h1 : 1 / (ϱ + u ^ 2) ≤ 1 / u ^ 2 := one_div_le_one_div_of_le hu2 hs
  have hB : 1 / Real.sqrt (B : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp
    · have : (1 : ℝ) ≤ Real.sqrt B := by
        rw [Real.one_le_sqrt]; exact_mod_cast h
      exact (div_le_one (by linarith)).2 this
  have hB0 : 0 ≤ 1 / Real.sqrt (B : ℝ) := by positivity
  have t1 : E / (ϱ + u ^ 2) ≤ E * (1 / u ^ 2) := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left h1 hE
  have t2 : (E / (ϱ + u ^ 2)) / Real.sqrt (ϱ + u ^ 2) ≤ E / Real.sqrt ϱ * (1 / u ^ 2) := by
    have : (E / (ϱ + u ^ 2)) / Real.sqrt (ϱ + u ^ 2) = E * (1 / (ϱ + u ^ 2)) * (1 / Real.sqrt (ϱ + u ^ 2)) := by
      field_simp
    rw [this]
    have h3 : 1 / Real.sqrt (ϱ + u ^ 2) ≤ 1 / Real.sqrt ϱ := one_div_le_one_div_of_le hsq hsqs
    calc _ ≤ E * (1 / u ^ 2) * (1 / Real.sqrt ϱ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hE) h3 (by positivity) (by positivity)
      _ = _ := by field_simp
  have t3 : 1 / ((ϱ + u ^ 2) * Real.sqrt (B : ℝ)) ≤ 1 * (1 / u ^ 2) := by
    have : 1 / ((ϱ + u ^ 2) * Real.sqrt (B : ℝ)) = (1 / (ϱ + u ^ 2)) * (1 / Real.sqrt (B : ℝ)) := by
      rw [one_div_mul_one_div]
    rw [this]
    calc _ ≤ (1 / u ^ 2) * 1 := mul_le_mul h1 hB hB0 (by positivity)
      _ = _ := by ring
  rw [hr]; nlinarith


/-- The integrated state-uniform bound, snapshot `cr-2026-10-23` (`sections/05-dynamics/section.tex`
ll. 973–982):
```latex
The operator norm of the expected update is the integral of
\cref{eqn:app-dyn-H-op}. Splitting at a cutoff $\mathsf R\ge1$,
\[
\norm{\EE\,\Qridge\ridge(\Mt)}\le\frac2\pi\int_0^\infty\norm{\mathcal H(\ridge+u^2)}\,\dif u
\le C\norm{\Ahat}+\frac2\pi\Big[\mathsf R\sup_{s\in[\ridge,\ridge+\mathsf R^2]}\mathsf e_B(s)+\frac{C}{\mathsf R}\Big].
\]
Let $r_B$ be the infimum over $\mathsf R\ge1$ of the bracket. It does not depend
on the state, and it tends to zero: for fixed $\mathsf R$ the first term
vanishes as the dimension grows, and the second is small for large
$\mathsf R$. This proves (iv).
```
Encoding: `K` and the sequence `r` (indexed by the batch size `B`) depend only on `(ϱ, C_Σ, γ⋆)`
and are chosen before the dimension, the weights, the state, the samples and the time. This is
stronger than `lem:app-dyn-mean`(iv) as stated (whose `r_B` may also depend on the dimension
sequence and the weights) and gives it with `r_k := r (B k)` along any sequence with `B_k → ∞`.
The strengthening is what the source's proof gives: the only `B`-dependent inputs are
`lem_app_de_replace` (sequence `e_B(I)` depending only on `(I, C_Σ, γ⋆)`) and `1/√B`. -/
theorem expected_update_opNorm_uniform (ϱ CS γ : ℝ) (hϱ : 0 < ϱ) :
    ∃ K : ℝ, ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
        [IsProbabilityMeasure P] (w : ℕ → ℝ) (F : FrozenParams m n B)
        (S : FrozenSamples P m n B) (t : ℤ),
        WeightClass w → opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
        (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
          opNorm (EQ w F S t ϱ) ≤ K * opNorm F.A + r B := by
  obtain ⟨CH0, hCH0⟩ := eqn_app_dyn_H_op ϱ CS γ hϱ
  obtain ⟨CE0, hCE0⟩ := eqn_app_dyn_eps_large CS γ
  have hrep := fun k : ℕ => lem_app_de_replace (Icc ϱ (ϱ + ((k : ℝ) + 1) ^ 2)) isCompact_Icc
    (fun s hs => lt_of_lt_of_le hϱ hs.1) CS γ
  choose e he hrep using hrep
  have hCH : 0 ≤ max CH0 0 := le_max_right _ _
  have hE0 : 0 ≤ max CE0 0 := le_max_right _ _
  obtain ⟨CH, hCHdef⟩ : ∃ CH : ℝ, CH = max CH0 0 := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = max CE0 0 := ⟨_, rfl⟩
  rw [← hCHdef] at hCH
  rw [← hEdef] at hE0
  have hCHle : CH0 ≤ CH := hCHdef ▸ le_max_left _ _
  have hEle : CE0 ≤ E := hEdef ▸ le_max_left _ _
  obtain ⟨A0, hA0⟩ : ∃ A0 : ℝ, A0 = CH * ((1 + 1 / Real.sqrt ϱ + 1 / ϱ) / min ϱ 1) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = CH * (E + E / Real.sqrt ϱ + 1) := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  obtain ⟨ce, hce⟩ : ∃ ce : ℕ → ℕ → ℝ, ∀ k B, ce k B = CH * (max (e k B) 0 / ϱ +
      max (e k B) 0 / Real.sqrt ϱ + 1 / (ϱ * Real.sqrt (B : ℝ))) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Tk, hTk⟩ : ∃ Tk : ℕ → ℕ → ℝ, ∀ k B, Tk k B =
      (2 / Real.pi) * (ce k B * ((k : ℝ) + 1) + T / ((k : ℝ) + 1)) := ⟨_, fun _ _ => rfl⟩
  have hce0 : ∀ k B, 0 ≤ ce k B := fun k B => by rw [hce]; positivity
  have hTk0 : ∀ k B, 0 ≤ Tk k B := fun k B => by rw [hTk]; have := hce0 k B; positivity
  refine ⟨A0, fun B => ⨅ k : ℕ, Tk k B, ?_, ?_⟩
  · rw [tendsto_order]
    constructor
    · intro a ha
      exact Eventually.of_forall fun B => lt_of_lt_of_le ha (le_ciInf fun k => hTk0 k B)
    · intro a ha
      obtain ⟨k, hk⟩ := exists_nat_gt ((2 / Real.pi * T) * 2 / a)
      have hk' : (2 / Real.pi) * (T / ((k : ℝ) + 1)) < a / 2 := by
        have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        rw [← mul_div_assoc, div_lt_iff₀ hk1]
        rw [div_lt_iff₀ ha] at hk
        nlinarith
      have h1 : Tendsto (fun B => max (e k B) 0) atTop (𝓝 0) := by
        simpa using (he k).max (tendsto_const_nhds (x := (0 : ℝ)))
      have h2 : Tendsto (fun B : ℕ => 1 / (ϱ * Real.sqrt (B : ℝ))) atTop (𝓝 0) := by
        have h := (tendsto_inv_atTop_zero.comp
          (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
        have h' := h.const_mul ϱ⁻¹
        rw [mul_zero] at h'
        refine h'.congr fun B => ?_
        simp [one_div, mul_comm]
      have h3 : Tendsto (fun B => Tk k B) atTop (𝓝 ((2 / Real.pi) * (T / ((k : ℝ) + 1)))) := by
        have := ((((((h1.div_const ϱ).add (h1.div_const (Real.sqrt ϱ))).add h2).const_mul
          CH).mul_const ((k : ℝ) + 1)).add_const (T / ((k : ℝ) + 1))).const_mul (2 / Real.pi)
        simp only [hTk, hce]
        simpa using this
      filter_upwards [h3.eventually (gt_mem_nhds (by linarith : (2 / Real.pi) *
        (T / ((k : ℝ) + 1)) < a))] with B hB
      have hbdd : BddBelow (Set.range fun k : ℕ => Tk k B) :=
        ⟨0, by rintro _ ⟨k', rfl⟩; exact hTk0 k' B⟩
      exact lt_of_le_of_lt (ciInf_le hbdd k) hB
  · intro Ω _ m n B P _ w F S t hw hCo hCi hm hn
    have key : ∀ k : ℕ, opNorm (EQ w F S t ϱ) ≤ A0 * opNorm F.A + Tk k B := by
      intro k
      obtain ⟨-, hint2, hEQ⟩ := expected_update_contour hw F S t ϱ hϱ
      have hR : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ, ∀ u, g u = A0 * opNorm F.A * (1 + u ^ 2)⁻¹ +
          (Ioc (0 : ℝ) ((k : ℝ) + 1)).indicator (fun _ => ce k B) u +
          (Ioi ((k : ℝ) + 1)).indicator (fun v : ℝ => T * v ^ (-2 : ℝ)) u :=
        ⟨_, fun _ => rfl⟩
      have hpt : ∀ u ∈ Ioi (0 : ℝ), opNorm (Hmix w F S t (ϱ + u ^ 2)) ≤ g u := by
        intro u hu
        have hu0 : 0 < u := hu
        have hs : ϱ ≤ ϱ + u ^ 2 := by nlinarith [sq_nonneg u]
        have hs0 : 0 < ϱ + u ^ 2 := by linarith
        have hA : 0 ≤ opNorm F.A := norm_nonneg _
        have hF1 := pe15p4_F1 hϱ u
        have hmono : ∀ x : ℝ, 0 ≤ x → CH0 * x ≤ CH * x := fun x hx =>
          mul_le_mul_of_nonneg_right hCHle hx
        have hfirst : CH0 * (1 / (ϱ + u ^ 2) + 1 / ((ϱ + u ^ 2) * Real.sqrt (ϱ + u ^ 2)) +
            1 / (ϱ + u ^ 2) ^ 2) * opNorm F.A ≤ A0 * opNorm F.A * (1 + u ^ 2)⁻¹ := by
          have h0 : 0 ≤ 1 / (ϱ + u ^ 2) + 1 / ((ϱ + u ^ 2) * Real.sqrt (ϱ + u ^ 2)) +
              1 / (ϱ + u ^ 2) ^ 2 := by positivity
          calc _ ≤ CH * (1 / (ϱ + u ^ 2) + 1 / ((ϱ + u ^ 2) * Real.sqrt (ϱ + u ^ 2)) +
                1 / (ϱ + u ^ 2) ^ 2) * opNorm F.A :=
                mul_le_mul_of_nonneg_right (hmono _ h0) hA
            _ ≤ CH * ((1 + 1 / Real.sqrt ϱ + 1 / ϱ) / min ϱ 1 * (1 + u ^ 2)⁻¹) * opNorm F.A :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF1 hCH) hA
            _ = _ := by rw [hA0]; ring
        rw [hgdef]
        by_cases hle : u ≤ (k : ℝ) + 1
        · have hind : (Ioc (0 : ℝ) ((k : ℝ) + 1)).indicator (fun _ => ce k B) u = ce k B :=
            indicator_of_mem (show u ∈ Ioc (0 : ℝ) ((k : ℝ) + 1) from ⟨hu0, hle⟩) _
          have hind2 : (Ioi ((k : ℝ) + 1)).indicator (fun v : ℝ => T * v ^ (-2 : ℝ)) u = 0 :=
            indicator_of_notMem (by simpa using hle) _
          rw [hind, hind2, add_zero]
          have hu2 : ϱ + u ^ 2 ≤ ϱ + ((k : ℝ) + 1) ^ 2 := by
            have : u ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
            linarith
          have h1 := hrep k m n B w hw Ω P F S t hCo hCi hm hn
          have hH := hCH0 Ω m n B P w F S t hw hCo hCi hm hn (ϱ + u ^ 2) hs
            (max (e k B) 0) (max (e k B) 0) (le_max_right _ _) (le_max_right _ _)
            (fun j => by
              refine (h1 j (ϱ + u ^ 2) ⟨hs, hu2⟩ |>.1).trans (ENNReal.ofReal_le_ofReal ?_)
              exact mul_le_mul_of_nonneg_left (le_max_left _ _) (hw.1.1 j))
            (fun j => by
              refine (h1 j (ϱ + u ^ 2) ⟨hs, hu2⟩ |>.2.1).trans (ENNReal.ofReal_le_ofReal ?_)
              exact mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg _))
          have hsecond : CH0 * (max (e k B) 0 / (ϱ + u ^ 2) +
              max (e k B) 0 / Real.sqrt (ϱ + u ^ 2) + 1 / ((ϱ + u ^ 2) * Real.sqrt (B : ℝ))) ≤
              ce k B := by
            have hsqs : Real.sqrt ϱ ≤ Real.sqrt (ϱ + u ^ 2) := Real.sqrt_le_sqrt hs
            have hsq : 0 < Real.sqrt ϱ := Real.sqrt_pos.2 hϱ
            have hx := le_max_right (e k B) 0
            have c1 : max (e k B) 0 / (ϱ + u ^ 2) ≤ max (e k B) 0 / ϱ :=
              div_le_div_of_nonneg_left hx hϱ hs
            have c2 : max (e k B) 0 / Real.sqrt (ϱ + u ^ 2) ≤ max (e k B) 0 / Real.sqrt ϱ :=
              div_le_div_of_nonneg_left hx hsq hsqs
            have c3 : 1 / ((ϱ + u ^ 2) * Real.sqrt (B : ℝ)) ≤ 1 / (ϱ * Real.sqrt (B : ℝ)) := by
              rcases (Real.sqrt_nonneg (B : ℝ)).eq_or_lt with h | h
              · rw [← h]; simp
              · exact one_div_le_one_div_of_le (by positivity)
                  (mul_le_mul_of_nonneg_right hs h.le)
            rw [hce]
            calc _ ≤ CH * (max (e k B) 0 / (ϱ + u ^ 2) +
                max (e k B) 0 / Real.sqrt (ϱ + u ^ 2) + 1 / ((ϱ + u ^ 2) * Real.sqrt (B : ℝ))) :=
                  hmono _ (by positivity)
              _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hCH
          have : 1 / (ϱ + u ^ 2) = 1 / (ϱ + u ^ 2) := rfl
          have hrw : (1 / (ϱ + u ^ 2) + 1 / ((ϱ + u ^ 2) * Real.sqrt (ϱ + u ^ 2)) +
              1 / (ϱ + u ^ 2) ^ 2) = (1 / (ϱ + u ^ 2) + 1 / ((ϱ + u ^ 2) * Real.sqrt (ϱ + u ^ 2)) +
              1 / (ϱ + u ^ 2) ^ 2) := rfl
          have hH' : opNorm (Hmix w F S t (ϱ + u ^ 2)) ≤
              CH0 * (1 / (ϱ + u ^ 2) + 1 / ((ϱ + u ^ 2) * Real.sqrt (ϱ + u ^ 2)) +
                1 / (ϱ + u ^ 2) ^ 2) * opNorm F.A + CH0 * (max (e k B) 0 / (ϱ + u ^ 2) +
              max (e k B) 0 / Real.sqrt (ϱ + u ^ 2) + 1 / ((ϱ + u ^ 2) * Real.sqrt (B : ℝ))) := hH
          linarith
        · have hgt : (k : ℝ) + 1 < u := not_le.1 hle
          have hind : (Ioc (0 : ℝ) ((k : ℝ) + 1)).indicator (fun _ => ce k B) u = 0 :=
            indicator_of_notMem (by simp [hle]) _
          have hind2 : (Ioi ((k : ℝ) + 1)).indicator (fun v : ℝ => T * v ^ (-2 : ℝ)) u =
              T * u ^ (-2 : ℝ) := indicator_of_mem hgt _
          rw [hind, hind2, add_zero]
          have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
            have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
            linarith
          have hs1 : 1 ≤ ϱ + u ^ 2 := by nlinarith
          have hEE := hCE0 Ω m n B P w F S t hw hCo hCi hm hn
          have hH := hCH0 Ω m n B P w F S t hw hCo hCi hm hn (ϱ + u ^ 2) hs E (E / (ϱ + u ^ 2))
            hE0 (div_nonneg hE0 hs0.le)
            (fun j => by
              refine (hEE j (ϱ + u ^ 2) hs1 |>.1).trans (ENNReal.ofReal_le_ofReal ?_)
              exact mul_le_mul_of_nonneg_left hEle (hw.1.1 j))
            (fun j => by
              refine (hEE j (ϱ + u ^ 2) hs1 |>.2).trans (ENNReal.ofReal_le_ofReal ?_)
              rw [mul_div_assoc]
              exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hEle hs0.le) (sq_nonneg _))
          have hsecond : CH0 * (E / (ϱ + u ^ 2) + (E / (ϱ + u ^ 2)) / Real.sqrt (ϱ + u ^ 2) +
              1 / ((ϱ + u ^ 2) * Real.sqrt (B : ℝ))) ≤ T * u ^ (-2 : ℝ) := by
            have hF2 := pe15p4_F2 hϱ E hE0 B hu0
            rw [hT, mul_assoc]
            calc _ ≤ CH * (E / (ϱ + u ^ 2) + (E / (ϱ + u ^ 2)) / Real.sqrt (ϱ + u ^ 2) +
                1 / ((ϱ + u ^ 2) * Real.sqrt (B : ℝ))) := hmono _ (by positivity)
              _ ≤ _ := mul_le_mul_of_nonneg_left hF2 hCH
          have hH' : opNorm (Hmix w F S t (ϱ + u ^ 2)) ≤
              CH0 * (1 / (ϱ + u ^ 2) + 1 / ((ϱ + u ^ 2) * Real.sqrt (ϱ + u ^ 2)) +
                1 / (ϱ + u ^ 2) ^ 2) * opNorm F.A + CH0 * (E / (ϱ + u ^ 2) +
              (E / (ϱ + u ^ 2)) / Real.sqrt (ϱ + u ^ 2) +
                1 / ((ϱ + u ^ 2) * Real.sqrt (B : ℝ))) := hH
          linarith
      obtain ⟨hgi, hgv⟩ := pe15p4_g_int (A0 * opNorm F.A) (ce k B) T ((k : ℝ) + 1) hR g hgdef
      have hb := pe15p4_opNorm_integral (EQ w F S t ϱ) (fun u => Hmix w F S t (ϱ + u ^ 2))
        g (2 / Real.pi)
        (by positivity) hEQ hint2 hgi hpt
      rw [hgv, hTk] at *
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      calc _ ≤ _ := hb
        _ = _ := by field_simp; ring
    have hbdd : BddBelow (Set.range fun k : ℕ => Tk k B) := ⟨0, by rintro _ ⟨k', rfl⟩; exact hTk0 k' B⟩
    have : opNorm (EQ w F S t ϱ) - A0 * opNorm F.A ≤ ⨅ k : ℕ, Tk k B :=
      le_ciInf fun k => by linarith [key k]
    linarith

end Muon.Dynamics

end

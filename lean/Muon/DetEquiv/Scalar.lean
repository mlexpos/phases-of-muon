import Muon.Foundations.Conventions
import Muon.Foundations.Gaussian

/-!
# Appendix B: scalar functions of the weight class (task L-B.1)

Snapshot `cr-2026-10-22`. Source: `sections/02-deterministic-equivalents/section.tex`,
"Scalar functions" (l.45–66), `lem:app-de-scalar` (l.49–74), `prop:app-de-nomomentum`
(l.441–447), and the weight class `eqn:app-de-weightclass` (l.1138–1148).

Representation choices (CARD §2, §6.2 and ruling L2):

* The weight class is general: nonnegative, summable (so that `tsum` means the sum),
  not all zero (`∃ j, w j ≠ 0`), bounded by one, with total mass at most one. The
  EMA weights `Muon.emaW β` (β ∈ [0,1)) are an instance. Summability is a field, not
  left implicit, because `tsum` of a non-summable family is junk.
* `J`, `Fw`, `Lw`, `rW` are the paper's `J`, `F_w`, `L_w`, `r_w` for an arbitrary weight
  sequence `w : ℕ → ℝ`. Their series are `tsum`s over `j : ℕ`.
* `AdmissibleWeightFn F` records the four properties of the abstract weight function that
  Appendix B's branch proof uses (card §2, §6.17).
* Power sums for a general sequence are `sumPow w p`; `Muon.sPow β p` is the EMA case
  (`sPow_eq_sumPow_emaW`, proved by `rfl`). The paper's `\sw{1}` is written `∑' j, w j`.
* `J`, `F_w`, `L_w` are defined for `x ≥ 0`; the integrand is singular for `x < 0`, so
  every statement is restricted to `Set.Ici 0`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

namespace Muon.DetEquiv

/-! ## Weight sequences and the weight class -/

/-- Nonnegative, summable, not all zero: the hypothesis of `lem:app-de-scalar`(ii),(iii)
("Let $w$ be nonnegative, summable and not all zero"). -/
def WeightSeq (w : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ w j) ∧ Summable w ∧ ∃ j, w j ≠ 0

/-- The weight class of `eqn:app-de-weightclass`, with "not all zero" made explicit
(coordinator ruling L2). Source (l.1138–1148): "the results of this subsection are stated for a
fixed weight sequence $w=(\emaw j)_{j\ge0}$ satisfying
\begin{equation}\label{eqn:app-de-weightclass}
0\le\emaw j\le1\quad(j\ge0),\qquad \sum_{j\ge0}\emaw j\le1 ,
\end{equation}". The EMA weights are the instance `Muon.emaW β` for `β ∈ [0,1)`. -/
def WeightClass (w : ℕ → ℝ) : Prop :=
  WeightSeq w ∧ (∀ j, w j ≤ 1) ∧ ∑' j, w j ≤ 1

/-- `S_p = ∑_{j ≥ 0} w_j^p` for a general weight sequence (`sPow` of `Muon.Conventions` is
the EMA case). -/
def sumPow (w : ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑' j, w j ^ p

/-- The EMA power sums are the general ones at the EMA weights `Muon.emaW β`. -/
theorem sPow_eq_sumPow_emaW (β : ℝ) (p : ℕ) :
    Muon.sPow β p = sumPow (Muon.emaW β) p :=
  rfl

/-! ## The scalar functions -/

/-- `J(x) = E[g²/(1+xg²)]` for `g ~ N(0,1)` (`eqn:app-de-JFL`, l.43–47: "For
$g\sim\mathcal N(0,1)$ and $x,q\ge0$ put $\Jfun(x)\defeq\EE\frac{g^2}{1+xg^2}$"). -/
def J (x : ℝ) : ℝ :=
  ∫ g, g ^ 2 / (1 + x * g ^ 2) ∂(gaussianReal 0 1)

/-- `F_w(q) = ∑_{j ≥ 0} w_j² J(w_j² q)` (`eqn:app-de-JFL`, l.43–47). -/
def Fw (w : ℕ → ℝ) (q : ℝ) : ℝ :=
  ∑' j, w j ^ 2 * J (w j ^ 2 * q)

/-- `L_w(q) = ∑_{j ≥ 0} w_j J(w_j² q)` (`eqn:app-de-JFL`, l.43–47). -/
def Lw (w : ℕ → ℝ) (q : ℝ) : ℝ :=
  ∑' j, w j * J (w j ^ 2 * q)

/-- `r_w(q) = q F_w(q)` (`eqn:app-de-JFL` and the definition of `r_w` in the scalar lemma,
l.66: "$r_w(q)\defeq qF_w(q)$"). -/
def rW (w : ℕ → ℝ) (q : ℝ) : ℝ :=
  q * Fw w q

/-- Abstract admissible weight function: the four properties that the proof of the branch
theorem uses (card §2; D's `lem:app-vol-profile` instantiates it). Source of the
properties: `F_w` as in `lem:app-de-scalar`(ii),(iii). -/
structure AdmissibleWeightFn (F : ℝ → ℝ) : Prop where
  /-- `F` is continuous on `[0,∞)`. -/
  contOn : ContinuousOn F (Ici 0)
  /-- `F` is positive on `[0,∞)`. -/
  pos : ∀ q, 0 ≤ q → 0 < F q
  /-- `F(q) ≤ F(0)` on `[0,∞)`. -/
  le_zero : ∀ q, 0 ≤ q → F q ≤ F 0
  /-- `q ↦ q F(q)` is strictly increasing on `[0,∞)`. -/
  r_strictMonoOn : StrictMonoOn (fun q => q * F q) (Ici 0)
  /-- `q F(q)` vanishes at `q = 0`. -/
  r_zero : (fun q => q * F q) 0 = 0

/-! ### Private helpers for `lem_app_de_scalar_i` (fully proved) -/

private lemma J_den_pos {x : ℝ} (hx : 0 ≤ x) (g : ℝ) : 0 < 1 + x * g ^ 2 := by
  have := mul_nonneg hx (sq_nonneg g)
  linarith

/-- The complement of `{0}` has full Gaussian measure. -/
private lemma gauss_compl_zero_pos : (0 : ENNReal) < gaussianReal 0 1 ({(0 : ℝ)}ᶜ) := by
  have h0 : gaussianReal 0 1 {(0 : ℝ)} = 0 :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton
  have h1 : gaussianReal 0 1 ({(0 : ℝ)}ᶜ) = 1 := by
    rw [measure_compl (measurableSet_singleton 0) (by simp [h0]), h0]
    simp
  rw [h1]
  exact one_pos

/-- Generic dominated integrability for `p g / (1 + x g²)` with `0 ≤ p ≤` integrable. -/
private lemma den_integrable {p : ℝ → ℝ} (hp : Integrable p (gaussianReal 0 1))
    (hp0 : ∀ g, 0 ≤ p g) (hpm : Measurable p) {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun g => p g / (1 + x * g ^ 2)) (gaussianReal 0 1) := by
  refine Integrable.mono' hp
    (hpm.div (by fun_prop : Measurable fun g : ℝ => 1 + x * g ^ 2)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun g => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hp0 g) (J_den_pos hx g).le)]
  exact div_le_self (hp0 g) (by nlinarith [mul_nonneg hx (sq_nonneg g)])

/-- Generic dominated continuity (within `[0,∞)`) of `x ↦ ∫ p g / (1 + x g²)`. -/
private lemma den_continuousWithinAt {p : ℝ → ℝ} (hp : Integrable p (gaussianReal 0 1))
    (hp0 : ∀ g, 0 ≤ p g) (hpm : Measurable p) (x0 : ℝ) (hx0 : 0 ≤ x0) :
    ContinuousWithinAt (fun x => ∫ g, p g / (1 + x * g ^ 2) ∂(gaussianReal 0 1)) (Ici 0) x0 := by
  refine continuousWithinAt_of_dominated (F := fun x g => p g / (1 + x * g ^ 2))
    (bound := p) ?_ ?_ hp ?_
  · exact Filter.Eventually.of_forall fun x =>
      (hpm.div (by fun_prop : Measurable fun g : ℝ => 1 + x * g ^ 2)).aestronglyMeasurable
  · refine Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => Filter.Eventually.of_forall fun g => ?_
    have hx' : 0 ≤ x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hp0 g) (J_den_pos hx' g).le)]
    exact div_le_self (hp0 g) (by nlinarith [mul_nonneg hx' (sq_nonneg g)])
  · refine Filter.Eventually.of_forall fun g => ?_
    apply ContinuousAt.continuousWithinAt
    exact ContinuousAt.div continuousAt_const (by fun_prop) (J_den_pos hx0 g).ne'

private lemma J_integrable {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun g : ℝ => g ^ 2 / (1 + x * g ^ 2)) (gaussianReal 0 1) :=
  den_integrable (Muon.Foundations.gaussian_integrable_pow 2) (fun g => sq_nonneg g) (measurable_id.pow_const 2) hx

private lemma J_strictAntiOn : StrictAntiOn J (Ici 0) := by
  intro a ha b hb hab
  have ha' : 0 ≤ a := ha
  have hb' : 0 ≤ b := hb
  unfold J
  rw [← sub_pos, ← integral_sub (J_integrable ha') (J_integrable hb')]
  have hnn : ∀ g : ℝ, 0 ≤ g ^ 2 / (1 + a * g ^ 2) - g ^ 2 / (1 + b * g ^ 2) := by
    intro g
    have hlt : g ^ 2 / (1 + b * g ^ 2) ≤ g ^ 2 / (1 + a * g ^ 2) := by
      rw [div_le_div_iff₀ (J_den_pos hb' g) (J_den_pos ha' g)]
      nlinarith [mul_nonneg (sq_nonneg g) (mul_nonneg (sq_nonneg g) (sub_nonneg.2 hab.le))]
    linarith
  refine (integral_pos_iff_support_of_nonneg hnn ((J_integrable ha').sub (J_integrable hb'))).2 ?_
  refine lt_of_lt_of_le gauss_compl_zero_pos (measure_mono ?_)
  intro g hg
  have hg0 : g ≠ 0 := hg
  have hg2 : 0 < g ^ 2 := by positivity
  change g ^ 2 / (1 + a * g ^ 2) - g ^ 2 / (1 + b * g ^ 2) ≠ 0
  have hlt : g ^ 2 / (1 + b * g ^ 2) < g ^ 2 / (1 + a * g ^ 2) := by
    rw [div_lt_div_iff₀ (J_den_pos hb' g) (J_den_pos ha' g)]
    nlinarith [mul_pos (mul_pos hg2 hg2) (sub_pos.2 hab)]
  exact (sub_pos.2 hlt).ne'

private lemma J_pos {x : ℝ} (hx : 0 ≤ x) : 0 < J x := by
  unfold J
  rw [integral_pos_iff_support_of_nonneg (fun g => (div_nonneg (sq_nonneg g) (J_den_pos hx g).le))
    (J_integrable hx)]
  refine lt_of_lt_of_le gauss_compl_zero_pos (measure_mono ?_)
  intro g hg
  have hg0 : g ≠ 0 := hg
  have hg2 : 0 < g ^ 2 := by positivity
  change g ^ 2 / (1 + x * g ^ 2) ≠ 0
  exact (div_pos hg2 (J_den_pos hx g)).ne'

private lemma J_le_one {x : ℝ} (hx : 0 ≤ x) : J x ≤ 1 := by
  unfold J
  refine (integral_mono (J_integrable hx) (Muon.Foundations.gaussian_integrable_pow 2)
    (fun g => div_le_self (sq_nonneg g) (by nlinarith [mul_nonneg hx (sq_nonneg g)]))).trans_eq ?_
  exact Muon.Foundations.gaussian_moment_two

private lemma J_zero : J 0 = 1 := by
  unfold J
  simp only [zero_mul, add_zero, div_one]
  exact Muon.Foundations.gaussian_moment_two

private lemma H4_integrable {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun g : ℝ => g ^ 4 / (1 + x * g ^ 2)) (gaussianReal 0 1) :=
  den_integrable (Muon.Foundations.gaussian_integrable_pow 4) (fun g => by positivity) (measurable_id.pow_const 4) hx

/-- `J(x) = 1 - x · E[g⁴/(1+xg²)]` on `[0,∞)`. -/
private lemma J_eq_one_sub {x : ℝ} (hx : 0 ≤ x) :
    J x = 1 - x * ∫ g, g ^ 4 / (1 + x * g ^ 2) ∂(gaussianReal 0 1) := by
  have key : ∀ g : ℝ, g ^ 2 / (1 + x * g ^ 2) = g ^ 2 - x * (g ^ 4 / (1 + x * g ^ 2)) := by
    intro g
    have := (J_den_pos hx g).ne'
    field_simp
    ring
  unfold J
  calc ∫ g, g ^ 2 / (1 + x * g ^ 2) ∂(gaussianReal 0 1)
      = ∫ g, (g ^ 2 - x * (g ^ 4 / (1 + x * g ^ 2))) ∂(gaussianReal 0 1) := by
        congr 1
        ext g
        exact key g
    _ = (∫ g, g ^ 2 ∂(gaussianReal 0 1)) - x * ∫ g, g ^ 4 / (1 + x * g ^ 2) ∂(gaussianReal 0 1) := by
        rw [integral_sub (Muon.Foundations.gaussian_integrable_pow 2) ((H4_integrable hx).const_mul x),
          integral_const_mul]
    _ = 1 - x * ∫ g, g ^ 4 / (1 + x * g ^ 2) ∂(gaussianReal 0 1) := by
        rw [Muon.Foundations.gaussian_moment_two]

private lemma J_continuousWithinAt {x0 : ℝ} (hx0 : 0 ≤ x0) :
    ContinuousWithinAt J (Ici 0) x0 :=
  den_continuousWithinAt (Muon.Foundations.gaussian_integrable_pow 2) (fun g => sq_nonneg g)
    (measurable_id.pow_const 2) x0 hx0

private lemma J_hasDerivWithinAt_zero :
    HasDerivWithinAt J (-3) (Ici 0) 0 := by
  have hHc := den_continuousWithinAt (p := fun g : ℝ => g ^ 4) (Muon.Foundations.gaussian_integrable_pow 4)
    (fun g => by positivity) (measurable_id.pow_const 4) 0 le_rfl
  have hH0 : (∫ g, g ^ 4 / (1 + (0 : ℝ) * g ^ 2) ∂(gaussianReal 0 1)) = 3 := by
    simp only [zero_mul, add_zero, div_one]
    exact Muon.Foundations.gaussian_moment_four
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hT : Tendsto (fun x => -(∫ g, g ^ 4 / (1 + x * g ^ 2) ∂(gaussianReal 0 1)))
      (𝓝[Ici 0 \ {0}] 0) (𝓝 (-3)) := by
    have h1 := hHc.tendsto.mono_left
      (nhdsWithin_mono (0 : ℝ) (diff_subset (s := Ici (0 : ℝ)) (t := {(0 : ℝ)})))
    rw [hH0] at h1
    simpa using h1.neg
  refine hT.congr' ?_
  refine eventually_nhdsWithin_of_forall fun x hx => ?_
  have hx0 : 0 ≤ x := hx.1
  have hxne : x ≠ 0 := hx.2
  beta_reduce
  rw [slope_def_field, J_eq_one_sub hx0, J_zero, sub_zero]
  generalize (∫ g, g ^ 4 / (1 + x * g ^ 2) ∂(gaussianReal 0 1)) = I
  field_simp
  ring

/-- The five non-smoothness conjuncts of `lem_app_de_scalar_i`, assembled from the helpers. -/
private lemma J_scalar_i_no_smooth :
    ContinuousOn J (Ici 0) ∧
    StrictAntiOn J (Ici 0) ∧
    (∀ x, 0 ≤ x → 0 < J x ∧ J x ≤ 1) ∧
    HasDerivWithinAt J (-3) (Ici 0) 0 ∧
    J 0 = 1 :=
  ⟨fun _ hx => J_continuousWithinAt hx, J_strictAntiOn, fun _ hx => ⟨J_pos hx, J_le_one hx⟩,
    J_hasDerivWithinAt_zero, J_zero⟩

/-! ### Smoothness helpers: the family `F_k(x) = E[g^(2k+2)/(1+xg²)^(k+1)]` -/

private lemma Pk_bounds {k : ℕ} {x : ℝ} (hx : 0 ≤ x) (g : ℝ) :
    0 ≤ g ^ (2 * k + 2) / (1 + x * g ^ 2) ^ (k + 1) ∧
    g ^ (2 * k + 2) / (1 + x * g ^ 2) ^ (k + 1) ≤ g ^ (2 * k + 2) := by
  have hd : 0 < (1 + x * g ^ 2) ^ (k + 1) := pow_pos (J_den_pos hx g) _
  have hg : 0 ≤ g ^ (2 * k + 2) := by
    rw [pow_add, pow_mul]; positivity
  refine ⟨div_nonneg hg hd.le, div_le_self hg ?_⟩
  exact one_le_pow₀ (by nlinarith [mul_nonneg hx (sq_nonneg g)])

private lemma Pk_meas (k : ℕ) (x : ℝ) :
    Measurable fun g : ℝ => g ^ (2 * k + 2) / (1 + x * g ^ 2) ^ (k + 1) :=
  (measurable_id.pow_const _).div (by fun_prop)

private lemma Pk_integrable {k : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun g : ℝ => g ^ (2 * k + 2) / (1 + x * g ^ 2) ^ (k + 1)) (gaussianReal 0 1) := by
  refine Integrable.mono' (Muon.Foundations.gaussian_integrable_pow (2 * k + 2))
    (Pk_meas k x).aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Pk_bounds hx g).1]
  exact (Pk_bounds hx g).2

private lemma Fk_continuousWithinAt (k : ℕ) {x0 : ℝ} (hx0 : 0 ≤ x0) :
    ContinuousWithinAt
      (fun x => ∫ g, g ^ (2 * k + 2) / (1 + x * g ^ 2) ^ (k + 1) ∂(gaussianReal 0 1)) (Ici 0) x0 := by
  refine continuousWithinAt_of_dominated
    (F := fun x g => g ^ (2 * k + 2) / (1 + x * g ^ 2) ^ (k + 1))
    (bound := fun g => g ^ (2 * k + 2)) ?_ ?_
    (Muon.Foundations.gaussian_integrable_pow (2 * k + 2)) ?_
  · exact Filter.Eventually.of_forall fun x => (Pk_meas k x).aestronglyMeasurable
  · refine Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => Filter.Eventually.of_forall fun g => ?_
    have hx' : 0 ≤ x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Pk_bounds hx' g).1]
    exact (Pk_bounds hx' g).2
  · refine Filter.Eventually.of_forall fun g => ?_
    apply ContinuousAt.continuousWithinAt
    exact ContinuousAt.div continuousAt_const (by fun_prop)
      (pow_pos (J_den_pos hx0 g) _).ne'

private lemma Pk_hasDerivAt (k : ℕ) {y : ℝ} (hy : 0 ≤ y) (g : ℝ) :
    HasDerivAt (fun y : ℝ => g ^ (2 * k + 2) / (1 + y * g ^ 2) ^ (k + 1))
      (-((k + 1 : ℝ) * (g ^ (2 * (k + 1) + 2) / (1 + y * g ^ 2) ^ (k + 1 + 1)))) y := by
  have hd := J_den_pos hy g
  have h1 : HasDerivAt (fun y : ℝ => 1 + y * g ^ 2) (g ^ 2) y := by
    simpa using ((hasDerivAt_id y).mul_const (g ^ 2)).const_add 1
  have h2 := h1.pow (k + 1)
  have h3 := (hasDerivAt_const y (g ^ (2 * k + 2))).div h2 (pow_pos hd _).ne'
  refine h3.congr_deriv ?_
  beta_reduce
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.pow_apply]
  have : (1 + y * g ^ 2) ≠ 0 := hd.ne'
  field_simp
  ring

private lemma Fk_hasDerivAt (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun x => ∫ g, g ^ (2 * k + 2) / (1 + x * g ^ 2) ^ (k + 1) ∂(gaussianReal 0 1))
      (∫ g, -((k + 1 : ℝ) * (g ^ (2 * (k + 1) + 2) / (1 + x * g ^ 2) ^ (k + 1 + 1)))
        ∂(gaussianReal 0 1)) x := by
  have hb : Integrable (fun g : ℝ => ((k : ℝ) + 1) * g ^ (2 * (k + 1) + 2)) (gaussianReal 0 1) :=
    (Muon.Foundations.gaussian_integrable_pow _).const_mul _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x g => g ^ (2 * k + 2) / (1 + x * g ^ 2) ^ (k + 1))
    (F' := fun x g => -((k + 1 : ℝ) * (g ^ (2 * (k + 1) + 2) / (1 + x * g ^ 2) ^ (k + 1 + 1))))
    (bound := fun g => ((k : ℝ) + 1) * g ^ (2 * (k + 1) + 2))
    (s := Ioo (x / 2) (x + x / 2)) (Ioo_mem_nhds (by linarith) (by linarith)) ?_ (Pk_integrable hx.le)
    ?_ ?_ hb ?_).2
  · exact Filter.Eventually.of_forall fun y => (Pk_meas k y).aestronglyMeasurable
  · exact (((Pk_meas (k + 1) x).const_mul _).neg).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun g y hy => ?_
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have := Pk_bounds (k := k + 1) hy0 g
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (by have := this.1; positivity)]
    exact mul_le_mul_of_nonneg_left this.2 (by positivity)
  · exact Filter.Eventually.of_forall fun g y hy => Pk_hasDerivAt k (by linarith [hy.1]) g

private lemma Fk_hasDerivWithinAt (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt
      (fun x => ∫ g, g ^ (2 * k + 2) / (1 + x * g ^ 2) ^ (k + 1) ∂(gaussianReal 0 1))
      (-((k + 1 : ℝ) * ∫ g, g ^ (2 * (k + 1) + 2) / (1 + x * g ^ 2) ^ (k + 1 + 1)
        ∂(gaussianReal 0 1))) (Ici 0) x := by
  have hint : ∀ y : ℝ, 0 ≤ y → (∫ g, -((k + 1 : ℝ) * (g ^ (2 * (k + 1) + 2) /
      (1 + y * g ^ 2) ^ (k + 1 + 1))) ∂(gaussianReal 0 1)) =
      -((k + 1 : ℝ) * ∫ g, g ^ (2 * (k + 1) + 2) / (1 + y * g ^ 2) ^ (k + 1 + 1)
        ∂(gaussianReal 0 1)) := by
    intro y _
    rw [integral_neg, integral_const_mul]
  rcases hx.lt_or_eq with hx | hx
  · have := (Fk_hasDerivAt k hx).hasDerivWithinAt (s := Ici 0)
    rwa [hint x hx.le] at this
  · subst hx
    refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0) ?_ ?_ self_mem_nhdsWithin ?_
    · intro y hy
      exact (Fk_hasDerivAt k hy).differentiableAt.differentiableWithinAt
    · exact (Fk_continuousWithinAt k le_rfl).mono Ioi_subset_Ici_self
    · rw [← neg_mul]
      have hc := (Fk_continuousWithinAt (k + 1) (le_refl 0)).tendsto.mono_left
        (nhdsWithin_mono (0 : ℝ) (Ioi_subset_Ici_self (a := (0 : ℝ))))
      have hc' := hc.const_mul (-((k + 1 : ℝ)))
      refine hc'.congr' ?_
      refine eventually_nhdsWithin_of_forall fun y hy => ?_
      have hy' : (0 : ℝ) < y := hy
      beta_reduce
      rw [(Fk_hasDerivAt k hy').deriv, hint y hy'.le, neg_mul]

private lemma Fk_contDiffOn : ∀ (n k : ℕ),
    ContDiffOn ℝ n
      (fun x => ∫ g, g ^ (2 * k + 2) / (1 + x * g ^ 2) ^ (k + 1) ∂(gaussianReal 0 1)) (Ici 0) := by
  intro n
  induction n with
  | zero =>
    intro k
    exact contDiffOn_zero.2 (fun x hx => Fk_continuousWithinAt k hx)
  | succ n ih =>
    intro k
    have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast,
      contDiffOn_succ_iff_derivWithin hu]
    refine ⟨fun x hx => (Fk_hasDerivWithinAt k hx).differentiableWithinAt, by simp, ?_⟩
    refine ((ih (k + 1)).const_smul (-((k + 1 : ℝ)))).congr ?_
    intro x hx
    rw [(Fk_hasDerivWithinAt k hx).derivWithin (hu x hx)]
    simp [neg_mul_eq_neg_mul]

private lemma J_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) J (Ici 0) := by
  have h := contDiffOn_infty.2 (fun n => Fk_contDiffOn n 0)
  refine h.congr ?_
  intro x _
  simp [J]

/-! ### Series helpers for `lem_app_de_scalar_ii` -/

private lemma summable_pow_of_weight {w : ℕ → ℝ} (hw : WeightSeq w) {k : ℕ} (hk : k ≠ 0) :
    Summable (fun j => w j ^ k) := by
  refine Summable.of_norm_bounded_eventually_nat hw.2.1 ?_
  filter_upwards [hw.2.1.tendsto_atTop_zero.eventually (gt_mem_nhds one_pos)] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hw.1 j) k)]
  exact pow_le_of_le_one (hw.1 j) hj.le hk

private lemma Fk_bounds (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (∫ g, g ^ (2 * k + 2) / (1 + x * g ^ 2) ^ (k + 1) ∂(gaussianReal 0 1)) ∧
    (∫ g, g ^ (2 * k + 2) / (1 + x * g ^ 2) ^ (k + 1) ∂(gaussianReal 0 1)) ≤
      ∫ g, g ^ (2 * k + 2) ∂(gaussianReal 0 1) :=
  ⟨integral_nonneg fun g => (Pk_bounds hx g).1,
    integral_mono (Pk_integrable hx) (Muon.Foundations.gaussian_integrable_pow (2 * k + 2))
      fun g => (Pk_bounds hx g).2⟩

private lemma Fk_hasDerivAt' (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => ∫ g, g ^ (2 * k + 2) / (1 + x * g ^ 2) ^ (k + 1) ∂(gaussianReal 0 1))
      (-((k + 1 : ℝ) * ∫ g, g ^ (2 * (k + 1) + 2) / (1 + x * g ^ 2) ^ (k + 1 + 1)
        ∂(gaussianReal 0 1))) x := by
  have h := Fk_hasDerivAt k hx
  rwa [integral_neg, integral_const_mul] at h

private lemma Fk_comp_hasDerivAt (k : ℕ) {b y : ℝ} (hb : 0 < b) (hy : 0 < y) :
    HasDerivAt (fun q : ℝ => ∫ g, g ^ (2 * k + 2) / (1 + b * q * g ^ 2) ^ (k + 1)
        ∂(gaussianReal 0 1))
      (-((k + 1 : ℝ) * ∫ g, g ^ (2 * (k + 1) + 2) / (1 + b * y * g ^ 2) ^ (k + 1 + 1)
        ∂(gaussianReal 0 1)) * b) y := by
  have h1 : HasDerivAt (fun q : ℝ => b * q) b y := by
    simpa using (hasDerivAt_id y).const_mul b
  exact (Fk_hasDerivAt' k (mul_pos hb hy)).comp y h1

private lemma T_term_norm_le {w : ℕ → ℝ} (hw : WeightSeq w) (c k j : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ‖w j ^ (c + 2 * k) * ∫ g, g ^ (2 * k + 2) / (1 + w j ^ 2 * x * g ^ 2) ^ (k + 1)
        ∂(gaussianReal 0 1)‖ ≤ w j ^ (c + 2 * k) * ∫ g, g ^ (2 * k + 2) ∂(gaussianReal 0 1) := by
  have hx' : 0 ≤ w j ^ 2 * x := mul_nonneg (sq_nonneg _) hx
  have hA : 0 ≤ w j ^ (c + 2 * k) := pow_nonneg (hw.1 j) _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA (Fk_bounds k hx').1)]
  exact mul_le_mul_of_nonneg_left (Fk_bounds k hx').2 hA

private lemma T_summable {w : ℕ → ℝ} (hw : WeightSeq w) {c : ℕ} (hc : c ≠ 0) (k : ℕ) {x : ℝ}
    (hx : 0 ≤ x) :
    Summable (fun j => w j ^ (c + 2 * k) * ∫ g, g ^ (2 * k + 2) / (1 + w j ^ 2 * x * g ^ 2) ^ (k + 1)
        ∂(gaussianReal 0 1)) :=
  Summable.of_norm_bounded ((summable_pow_of_weight hw (by omega)).mul_right _)
    (fun j => T_term_norm_le hw c k j hx)

private lemma T_continuousOn {w : ℕ → ℝ} (hw : WeightSeq w) {c : ℕ} (hc : c ≠ 0) (k : ℕ) :
    ContinuousOn (fun q : ℝ => ∑' j, w j ^ (c + 2 * k) *
      ∫ g, g ^ (2 * k + 2) / (1 + w j ^ 2 * q * g ^ 2) ^ (k + 1) ∂(gaussianReal 0 1)) (Ici 0) := by
  have hF : ContinuousOn (fun x : ℝ => ∫ g, g ^ (2 * k + 2) / (1 + x * g ^ 2) ^ (k + 1)
      ∂(gaussianReal 0 1)) (Ici 0) := fun x hx => Fk_continuousWithinAt k hx
  refine continuousOn_tsum (fun j => ?_)
    ((summable_pow_of_weight hw (by omega : c + 2 * k ≠ 0)).mul_right
      (∫ g, g ^ (2 * k + 2) ∂(gaussianReal 0 1))) (fun j q hq => T_term_norm_le hw c k j hq)
  exact continuousOn_const.mul (hF.comp (by fun_prop : ContinuousOn (fun q : ℝ => w j ^ 2 * q) (Ici 0))
    (fun q hq => Set.mem_Ici.2 (mul_nonneg (sq_nonneg _) (Set.mem_Ici.1 hq))))

private lemma T_hasDerivAt_term {w : ℕ → ℝ} (hw : WeightSeq w) {c : ℕ} (hc : c ≠ 0) (k j : ℕ)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun q : ℝ => w j ^ (c + 2 * k) * ∫ g, g ^ (2 * k + 2) / (1 + w j ^ 2 * q * g ^ 2)
        ^ (k + 1) ∂(gaussianReal 0 1))
      (w j ^ (c + 2 * k) * (-((k + 1 : ℝ) * ∫ g, g ^ (2 * (k + 1) + 2) / (1 + w j ^ 2 * y * g ^ 2)
        ^ (k + 1 + 1) ∂(gaussianReal 0 1)) * w j ^ 2)) y := by
  rcases (hw.1 j).lt_or_eq with hpos | hzero
  · exact (Fk_comp_hasDerivAt k (pow_pos hpos 2) hy).const_mul _
  · rw [← hzero, zero_pow (by omega : c + 2 * k ≠ 0)]
    simpa using (hasDerivAt_const y (0 : ℝ))

private lemma T_hasDerivAt {w : ℕ → ℝ} (hw : WeightSeq w) {c : ℕ} (hc : c ≠ 0) (k : ℕ) {y : ℝ}
    (hy : 0 < y) :
    HasDerivAt (fun q : ℝ => ∑' j, w j ^ (c + 2 * k) * ∫ g, g ^ (2 * k + 2) /
        (1 + w j ^ 2 * q * g ^ 2) ^ (k + 1) ∂(gaussianReal 0 1))
      (-((k + 1 : ℝ)) * ∑' j, w j ^ (c + 2 * (k + 1)) * ∫ g, g ^ (2 * (k + 1) + 2) /
        (1 + w j ^ 2 * y * g ^ 2) ^ (k + 1 + 1) ∂(gaussianReal 0 1)) y := by
  have hbound : ∀ j, ∀ z ∈ Ioi (0 : ℝ), ‖w j ^ (c + 2 * k) * (-((k + 1 : ℝ) *
      ∫ g, g ^ (2 * (k + 1) + 2) / (1 + w j ^ 2 * z * g ^ 2) ^ (k + 1 + 1)
        ∂(gaussianReal 0 1)) * w j ^ 2)‖ ≤
      ((k + 1 : ℝ) * ∫ g, g ^ (2 * (k + 1) + 2) ∂(gaussianReal 0 1)) * w j ^ (c + 2 * (k + 1)) := by
    intro j z hz
    have hz0 : 0 ≤ w j ^ 2 * z := mul_nonneg (sq_nonneg _) (le_of_lt hz)
    obtain ⟨h1, h2⟩ := Fk_bounds (k + 1) hz0
    have hA : 0 ≤ w j ^ (c + 2 * k) := pow_nonneg (hw.1 j) _
    have hB : 0 ≤ w j ^ 2 := sq_nonneg _
    have hm : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    have hexp : w j ^ (c + 2 * (k + 1)) = w j ^ (c + 2 * k) * w j ^ 2 := by ring
    rw [hexp, Real.norm_eq_abs, abs_le]
    constructor
    · nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hA hB) hm) (sub_nonneg.2 h2),
        mul_nonneg (mul_nonneg (mul_nonneg hA hB) hm) h1]
    · nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hA hB) hm) (sub_nonneg.2 h2),
        mul_nonneg (mul_nonneg (mul_nonneg hA hB) hm) h1]
  have hsum := hasDerivAt_tsum_of_isPreconnected
    (u := fun j => ((k + 1 : ℝ) * ∫ g, g ^ (2 * (k + 1) + 2) ∂(gaussianReal 0 1)) *
      w j ^ (c + 2 * (k + 1)))
    ((summable_pow_of_weight hw (by omega : c + 2 * (k + 1) ≠ 0)).mul_left _)
    isOpen_Ioi isPreconnected_Ioi
    (fun j z hz => T_hasDerivAt_term hw hc k j hz) hbound
    (Set.mem_Ioi.2 hy) (T_summable hw hc k (le_of_lt hy)) (Set.mem_Ioi.2 hy)
  convert hsum using 1
  rw [← tsum_mul_left]
  congr 1
  ext j
  ring

private lemma T_hasDerivWithinAt {w : ℕ → ℝ} (hw : WeightSeq w) {c : ℕ} (hc : c ≠ 0) (k : ℕ)
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (fun q : ℝ => ∑' j, w j ^ (c + 2 * k) * ∫ g, g ^ (2 * k + 2) /
        (1 + w j ^ 2 * q * g ^ 2) ^ (k + 1) ∂(gaussianReal 0 1))
      (-((k + 1 : ℝ)) * ∑' j, w j ^ (c + 2 * (k + 1)) * ∫ g, g ^ (2 * (k + 1) + 2) /
        (1 + w j ^ 2 * x * g ^ 2) ^ (k + 1 + 1) ∂(gaussianReal 0 1)) (Ici 0) x := by
  rcases hx.lt_or_eq with hx | hx
  · exact (T_hasDerivAt hw hc k hx).hasDerivWithinAt
  · subst hx
    refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0) ?_ ?_ self_mem_nhdsWithin ?_
    · intro y hy
      exact (T_hasDerivAt hw hc k hy).differentiableAt.differentiableWithinAt
    · exact (T_continuousOn hw hc k 0 (Set.mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self
    · have hc' := ((T_continuousOn hw hc (k + 1)) 0 (Set.mem_Ici.2 le_rfl)).tendsto.mono_left
        (nhdsWithin_mono (0 : ℝ) (Ioi_subset_Ici_self (a := (0 : ℝ)))) |>.const_mul
          (-((k + 1 : ℝ)))
      refine hc'.congr' ?_
      refine eventually_nhdsWithin_of_forall fun y hy => ?_
      have hy' : (0 : ℝ) < y := hy
      exact (T_hasDerivAt hw hc k hy').deriv.symm

private lemma T_contDiffOn {w : ℕ → ℝ} (hw : WeightSeq w) {c : ℕ} (hc : c ≠ 0) :
    ∀ (n k : ℕ), ContDiffOn ℝ n (fun q : ℝ => ∑' j, w j ^ (c + 2 * k) * ∫ g,
      g ^ (2 * k + 2) / (1 + w j ^ 2 * q * g ^ 2) ^ (k + 1) ∂(gaussianReal 0 1)) (Ici 0) := by
  intro n
  induction n with
  | zero =>
    intro k
    exact contDiffOn_zero.2 (T_continuousOn hw hc k)
  | succ n ih =>
    intro k
    have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast,
      contDiffOn_succ_iff_derivWithin hu]
    refine ⟨fun x hx => (T_hasDerivWithinAt hw hc k hx).differentiableWithinAt, by simp, ?_⟩
    refine ((ih (k + 1)).const_smul (-((k + 1 : ℝ)))).congr ?_
    intro x hx
    rw [(T_hasDerivWithinAt hw hc k hx).derivWithin (hu x hx)]
    simp [smul_eq_mul]

/-! ### Helpers for `lem_app_de_scalar_iii` (fully proved) -/

private lemma K_integrable {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun g : ℝ => g ^ 2 / (1 + x * g ^ 2) ^ 2) (gaussianReal 0 1) := by
  refine Integrable.mono' (Muon.Foundations.gaussian_integrable_pow 2)
    ((measurable_id.pow_const 2).div (by fun_prop)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun g => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_self (sq_nonneg g) (one_le_pow₀ (by nlinarith [mul_nonneg hx (sq_nonneg g)]))

private lemma K_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ∫ g, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ∧
    ∫ g, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ≤ ∫ g, g ^ 2 ∂(gaussianReal 0 1) :=
  ⟨integral_nonneg fun g => by positivity,
    integral_mono (K_integrable hx) (Muon.Foundations.gaussian_integrable_pow 2)
      fun g => div_le_self (sq_nonneg g) (one_le_pow₀ (by nlinarith [mul_nonneg hx (sq_nonneg g)]))⟩

private lemma K_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < ∫ g, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
  have hnn : ∀ g : ℝ, 0 ≤ g ^ 2 / (1 + x * g ^ 2) ^ 2 := fun g => by positivity
  rw [integral_pos_iff_support_of_nonneg hnn (K_integrable hx)]
  refine lt_of_lt_of_le gauss_compl_zero_pos (measure_mono ?_)
  intro g hg
  have hg0 : g ≠ 0 := hg
  have hg2 : 0 < g ^ 2 := by positivity
  change g ^ 2 / (1 + x * g ^ 2) ^ 2 ≠ 0
  exact (div_pos hg2 (pow_pos (J_den_pos hx g) 2)).ne'

private lemma Q_integrable {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun g : ℝ => g ^ 4 / (1 + x * g ^ 2) ^ 2) (gaussianReal 0 1) := by
  have h := Pk_integrable (k := 1) hx
  exact h

private lemma D_summable {w : ℕ → ℝ} (hw : WeightSeq w) {q : ℝ} (hq : 0 ≤ q) :
    Summable (fun j => w j ^ 2 * ∫ g, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) := by
  refine Summable.of_norm_bounded ((summable_pow_of_weight hw (by norm_num : (2 : ℕ) ≠ 0)).mul_right
    (∫ g, g ^ 2 ∂(gaussianReal 0 1))) (fun j => ?_)
  have hx : 0 ≤ w j ^ 2 * q := mul_nonneg (sq_nonneg _) hq
  obtain ⟨h1, h2⟩ := K_bounds hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) h1)]
  exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

private lemma Jw_summable {w : ℕ → ℝ} (hw : WeightSeq w) {q : ℝ} (hq : 0 ≤ q) :
    Summable (fun j => w j ^ 2 * ∫ g, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ∂(gaussianReal 0 1)) := by
  refine Summable.of_norm_bounded (summable_pow_of_weight hw (by norm_num : (2 : ℕ) ≠ 0))
    (fun j => ?_)
  have hx : 0 ≤ w j ^ 2 * q := mul_nonneg (sq_nonneg _) hq
  have h : 0 ≤ w j ^ 2 * ∫ g, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ∂(gaussianReal 0 1) :=
    mul_nonneg (sq_nonneg _) (J_pos hx).le
  rw [Real.norm_eq_abs, abs_of_nonneg h]
  exact mul_le_of_le_one_right (sq_nonneg _) (J_le_one hx)

private lemma Qw_summable {w : ℕ → ℝ} (hw : WeightSeq w) {q : ℝ} (hq : 0 ≤ q) :
    Summable (fun j => w j ^ 4 * ∫ g, g ^ 4 / (1 + w j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) := by
  refine Summable.of_norm_bounded ((summable_pow_of_weight hw (by norm_num : (4 : ℕ) ≠ 0)).mul_right
    (∫ g, g ^ 4 ∂(gaussianReal 0 1))) (fun j => ?_)
  have hx : 0 ≤ w j ^ 2 * q := mul_nonneg (sq_nonneg _) hq
  have h0 : 0 ≤ w j ^ 4 := by positivity
  have h1 : 0 ≤ ∫ g, g ^ 4 / (1 + w j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1) :=
    integral_nonneg fun g => by positivity
  have h2 : ∫ g, g ^ 4 / (1 + w j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)
      ≤ ∫ g, g ^ 4 ∂(gaussianReal 0 1) :=
    integral_mono (Q_integrable hx) (Muon.Foundations.gaussian_integrable_pow 4)
      fun g => div_le_self (by positivity)
        (one_le_pow₀ (by nlinarith [mul_nonneg hx (sq_nonneg g)]))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 h1)]
  exact mul_le_mul_of_nonneg_left h2 h0

private lemma Fw_eq_sum (w : ℕ → ℝ) (q : ℝ) :
    Fw w q = ∑' j, w j ^ 2 * ∫ g, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ∂(gaussianReal 0 1) :=
  rfl

private lemma Fw_hasDerivAt {w : ℕ → ℝ} (hw : WeightSeq w) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (Fw w)
      (-(∑' j, w j ^ 4 * ∫ g, g ^ 4 / (1 + w j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1))) q := by
  have hF : Fw w = fun q : ℝ => ∑' j, w j ^ (2 + 2 * 0) *
      ∫ g, g ^ (2 * 0 + 2) / (1 + w j ^ 2 * q * g ^ 2) ^ (0 + 1) ∂(gaussianReal 0 1) := by
    funext q
    simp [Fw, J]
  rw [hF]
  have h := T_hasDerivAt hw (by norm_num : (2 : ℕ) ≠ 0) 0 hq
  convert h using 1
  norm_num

private lemma rW_hasDerivAt {w : ℕ → ℝ} (hw : WeightSeq w) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (rW w)
      (∑' j, w j ^ 2 * ∫ g, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) q := by
  show HasDerivAt (fun y : ℝ => y * Fw w y) _ q
  have h := (hasDerivAt_id' q).mul (Fw_hasDerivAt hw hq)
  convert h using 1
  have ha := Jw_summable hw hq.le
  have hc := Qw_summable hw hq.le
  have hid : ∀ j : ℕ, w j ^ 2 * ∫ g, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)
      = w j ^ 2 * ∫ g, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ∂(gaussianReal 0 1)
        + -(q * (w j ^ 4 * ∫ g, g ^ 4 / (1 + w j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1))) := by
    intro j
    have hx : 0 ≤ w j ^ 2 * q := mul_nonneg (sq_nonneg _) hq.le
    have key : ∫ g, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)
        = (∫ g, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ∂(gaussianReal 0 1))
          - w j ^ 2 * q * ∫ g, g ^ 4 / (1 + w j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
      rw [← integral_const_mul, ← integral_sub (J_integrable hx) ((Q_integrable hx).const_mul _)]
      congr 1
      ext g
      have := (J_den_pos hx g).ne'
      field_simp
      ring
    rw [key]
    ring
  rw [Fw_eq_sum, one_mul, mul_neg, ← tsum_mul_left, ← tsum_neg,
    ← Summable.tsum_add ha (hc.mul_left q).neg]
  exact tsum_congr hid

private lemma rW_deriv_pos {w : ℕ → ℝ} (hw : WeightSeq w) {q : ℝ} (hq : 0 < q) :
    0 < ∑' j, w j ^ 2 * ∫ g, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
  obtain ⟨j, hj⟩ := hw.2.2
  have hnn : ∀ i, 0 ≤ w i ^ 2 * ∫ g, g ^ 2 / (1 + w i ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1) :=
    fun i => mul_nonneg (sq_nonneg _) (K_bounds (mul_nonneg (sq_nonneg _) hq.le)).1
  refine lt_of_lt_of_le ?_ ((D_summable hw hq.le).le_tsum j (fun i _ => hnn i))
  have hj2 : 0 < w j ^ 2 := by positivity
  exact mul_pos hj2 (K_pos (mul_nonneg (sq_nonneg _) hq.le))

private lemma rW_eq_sum_int {w : ℕ → ℝ} (hw : WeightSeq w) (q : ℝ) :
    rW w q = ∑' j, ∫ g, w j ^ 2 * q * g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ∂(gaussianReal 0 1) := by
  unfold rW
  rw [Fw_eq_sum, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1
  ext g
  ring


/-! ### Tail helpers for `lem_app_de_scalar_iii` (per-term integrals, monotone in q) -/

private lemma frac_nonneg {c : ℝ} (hc : 0 ≤ c) (g : ℝ) : 0 ≤ c * g ^ 2 / (1 + c * g ^ 2) :=
  div_nonneg (mul_nonneg hc (sq_nonneg g)) (by linarith [mul_nonneg hc (sq_nonneg g)])

private lemma frac_le_self {c : ℝ} (hc : 0 ≤ c) (g : ℝ) :
    c * g ^ 2 / (1 + c * g ^ 2) ≤ c * g ^ 2 :=
  div_le_self (mul_nonneg hc (sq_nonneg g)) (le_add_of_nonneg_right (mul_nonneg hc (sq_nonneg g)))

private lemma frac_integrable {c : ℝ} (hc : 0 ≤ c) :
    Integrable (fun g : ℝ => c * g ^ 2 / (1 + c * g ^ 2)) (gaussianReal 0 1) :=
  Integrable.mono' ((Muon.Foundations.gaussian_integrable_pow 2).const_mul c)
    (by fun_prop : Measurable fun g : ℝ => c * g ^ 2 / (1 + c * g ^ 2)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (frac_nonneg hc g)]
      exact frac_le_self hc g)

private lemma frac_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (g : ℝ) :
    a * g ^ 2 / (1 + a * g ^ 2) ≤ b * g ^ 2 / (1 + b * g ^ 2) := by
  have h1 : 0 < 1 + a * g ^ 2 := by linarith [mul_nonneg ha (sq_nonneg g)]
  have h2 : 0 < 1 + b * g ^ 2 := by linarith [mul_nonneg (ha.trans hab) (sq_nonneg g)]
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_nonneg (sq_nonneg g) (sub_nonneg.2 hab)]

private lemma Tm_nonneg (w : ℕ → ℝ) (j : ℕ) (q : ℝ) : 0 ≤ (∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1)) :=
  integral_nonneg fun g => frac_nonneg (mul_nonneg (sq_nonneg _) (le_max_right _ _)) g

private lemma Tm_le (w : ℕ → ℝ) (j : ℕ) (q : ℝ) : (∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1)) ≤ w j ^ 2 * max q 0 := by
  have hc : 0 ≤ w j ^ 2 * max q 0 := mul_nonneg (sq_nonneg _) (le_max_right _ _)
  calc ∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1)
      ≤ ∫ g, w j ^ 2 * max q 0 * g ^ 2 ∂(gaussianReal 0 1) :=
        integral_mono (frac_integrable hc) ((Muon.Foundations.gaussian_integrable_pow 2).const_mul _)
          (frac_le_self hc)
    _ = w j ^ 2 * max q 0 := by
        rw [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one]

private lemma Tm_mono (w : ℕ → ℝ) (j : ℕ) : Monotone (fun q => (∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1))) := by
  intro a b h
  have ha : 0 ≤ w j ^ 2 * max a 0 := mul_nonneg (sq_nonneg _) (le_max_right _ _)
  have hle : w j ^ 2 * max a 0 ≤ w j ^ 2 * max b 0 :=
    mul_le_mul_of_nonneg_left (max_le_max h le_rfl) (sq_nonneg _)
  exact integral_mono (frac_integrable ha) (frac_integrable (ha.trans hle))
    (fun g => frac_mono ha hle g)

private lemma Tm_summable {w : ℕ → ℝ} (hw : WeightSeq w) (q : ℝ) :
    Summable (fun j => (∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1))) :=
  Summable.of_nonneg_of_le (fun j => Tm_nonneg w j q) (fun j => Tm_le w j q)
    ((summable_pow_of_weight hw (by norm_num : (2 : ℕ) ≠ 0)).mul_right (max q 0))

private lemma Tm_eq_rW {w : ℕ → ℝ} (hw : WeightSeq w) {q : ℝ} (hq : 0 ≤ q) :
    rW w q = ∑' j, (∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1)) := by
  rw [rW_eq_sum_int hw q]
  exact tsum_congr fun j => by rw [max_eq_left hq]

private lemma frac_tendsto {a : ℝ} (ha : 0 < a) {g : ℝ} (hg : g ≠ 0) :
    Tendsto (fun q : ℝ => a * max q 0 * g ^ 2 / (1 + a * max q 0 * g ^ 2)) atTop (𝓝 1) := by
  have hm : Tendsto (fun q : ℝ => max q 0) atTop atTop :=
    tendsto_atTop_mono (fun q => le_max_left q 0) tendsto_id
  have hgpos : 0 < g ^ 2 := by positivity
  have hs : Tendsto (fun q : ℝ => a * max q 0 * g ^ 2) atTop atTop :=
    (hm.const_mul_atTop ha).atTop_mul_const hgpos
  have h1 : Tendsto (fun s : ℝ => (1 + s)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub (h1.comp hs)
  rw [sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [hs.eventually_ge_atTop 0] with q hq
  have hpos : 0 < 1 + a * max q 0 * g ^ 2 := by linarith
  show 1 - (1 + a * max q 0 * g ^ 2)⁻¹ = a * max q 0 * g ^ 2 / (1 + a * max q 0 * g ^ 2)
  rw [eq_div_iff hpos.ne', sub_mul, inv_mul_cancel₀ hpos.ne']
  ring

private lemma Tm_tendsto {w : ℕ → ℝ} {j : ℕ} (hj : 0 < w j) :
    Tendsto (fun q => (∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1))) atTop (𝓝 1) := by
  have hlim : Tendsto (fun q : ℝ => ∫ g, w j ^ 2 * max q 0 * g ^ 2 /
      (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ _g, (1 : ℝ) ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const 1) ?_
    · exact Filter.Eventually.of_forall fun q => (by fun_prop : Measurable fun g : ℝ =>
        w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun q => Filter.Eventually.of_forall fun g => ?_
      have hc : 0 ≤ w j ^ 2 * max q 0 := mul_nonneg (sq_nonneg _) (le_max_right _ _)
      have hn := mul_nonneg hc (sq_nonneg g)
      rw [Real.norm_eq_abs, abs_of_nonneg (frac_nonneg hc g)]
      exact (div_le_one (by linarith)).2 (by linarith)
    · have hae : ∀ᵐ g ∂(gaussianReal 0 1), g ≠ 0 := by
        rw [ae_iff]
        simpa using gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton
      filter_upwards [hae] with g hg
      exact frac_tendsto (pow_pos hj 2) hg
  have h1 : ∫ _g, (1 : ℝ) ∂(gaussianReal 0 1) = 1 := by simp
  rw [h1] at hlim
  exact hlim

private lemma Tm_iSup {w : ℕ → ℝ} (hw : WeightSeq w) (j : ℕ) :
    ⨆ q : ℝ, ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1))) = {j | 0 < w j}.indicator (fun _ => (1 : ℝ≥0∞)) j := by
  rcases (hw.1 j).lt_or_eq with hpos | hzero
  · have hmono : Monotone (fun q : ℝ => ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1)))) :=
      fun a b h => ENNReal.ofReal_le_ofReal (Tm_mono w j h)
    have hlim : Tendsto (fun q : ℝ => ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1)))) atTop (𝓝 1) := by
      have := ENNReal.tendsto_ofReal (Tm_tendsto hpos)
      rwa [ENNReal.ofReal_one] at this
    rw [Set.indicator_of_mem (show j ∈ {j | 0 < w j} from hpos)]
    exact tendsto_nhds_unique (tendsto_atTop_iSup hmono) hlim
  · have hz : ∀ q : ℝ, (∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1)) = 0 := fun q => by
      rw [← hzero]
      simp
    have hnot : j ∉ {j | 0 < w j} := fun h => by
      have h' : (0 : ℝ) < w j := h
      linarith
    rw [Set.indicator_of_notMem hnot]
    simp [hz]

private lemma rW_tail {w : ℕ → ℝ} (hw : WeightSeq w) :
    Tendsto (fun q : ℝ => ENNReal.ofReal (rW w q)) atTop
      (𝓝 (Set.encard {j | 0 < w j}).toENNReal) := by
  have hGmono : ∀ j, Monotone (fun q : ℝ => ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1)))) :=
    fun j a b h => ENNReal.ofReal_le_ofReal (Tm_mono w j h)
  have hsum_mono : Monotone (fun q : ℝ => ∑' j, ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1)))) :=
    fun a b h => ENNReal.tsum_le_tsum fun j => hGmono j h
  have hinterchange : ⨆ q : ℝ, ∑' j, ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1)))
      = ∑' j, ⨆ q : ℝ, ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1))) := by
    calc ⨆ q : ℝ, ∑' j, ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1)))
        = ⨆ q : ℝ, ⨆ s : Finset ℕ, ∑ j ∈ s, ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1))) :=
          iSup_congr fun q => ENNReal.tsum_eq_iSup_sum
      _ = ⨆ s : Finset ℕ, ⨆ q : ℝ, ∑ j ∈ s, ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1))) := iSup_comm
      _ = ⨆ s : Finset ℕ, ∑ j ∈ s, ⨆ q : ℝ, ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1))) :=
          iSup_congr fun s => (ENNReal.finsetSum_iSup_of_monotone hGmono).symm
      _ = ∑' j, ⨆ q : ℝ, ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1))) := ENNReal.tsum_eq_iSup_sum.symm
  have hlimit : ∑' j, ⨆ q : ℝ, ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1)))
      = (Set.encard {j | 0 < w j}).toENNReal := by
    rw [tsum_congr (Tm_iSup hw)]
    exact ((tsum_subtype _ (fun _ => (1 : ℝ≥0∞))).symm).trans (ENNReal.tsum_set_one _)
  have h2 : Tendsto (fun q : ℝ => ∑' j, ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1)))) atTop
      (𝓝 (⨆ q : ℝ, ∑' j, ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1))))) := tendsto_atTop_iSup hsum_mono
  rw [hinterchange, hlimit] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
  show ∑' j, ENNReal.ofReal ((∫ g, w j ^ 2 * max q 0 * g ^ 2 / (1 + w j ^ 2 * max q 0 * g ^ 2) ∂(gaussianReal 0 1))) = ENNReal.ofReal (rW w q)
  rw [Tm_eq_rW hw hq, ENNReal.ofReal_tsum_of_nonneg (fun j => Tm_nonneg w j q) (Tm_summable hw q)]

/-! ## Statements -/

/-- `lem:app-de-scalar`(i), snapshot `cr-2026-10-22`. LaTeX (part (i) of the lemma,
`sections/02-deterministic-equivalents/section.tex` l.49–74; the lemma header reads
"Let $w$ be nonnegative, summable and not all zero."; this part does not use $w$, see CARD §3):
```
\begin{lemma}[Properties of the scalar functions]\label{lem:app-de-scalar}
Let $w$ be nonnegative, summable and not all zero.
\begin{enumerate}[label=(\roman*)]
\item $\Jfun$ is continuous and strictly decreasing on $[0,\infty)$ with
values in $(0,1]$, it is $C^\infty$ on $(0,\infty)$ with one-sided
derivatives at $0$, and
\[
\Jfun(0)=1,\qquad \Jfun'(0)=-3 .
\]
\item The series defining $F_w$ and $L_w$ converge uniformly on $[0,\infty)$;
$F_w$ and $L_w$ are continuous, $C^\infty$ on $(0,\infty)$ with one-sided
derivatives at $0$, and
\[
F_w(0)=\sw2,\qquad F_w'(0)=-3\sw4,\qquad L_w(0)=\sum_jw_j,\qquad L_w'(0)=-3\sw3 .
\]
\item The function
\[
r_w(q)\defeq qF_w(q)=\sum_j\EE\frac{w_j^2qg^2}{1+w_j^2qg^2}
\]
is strictly increasing on $[0,\infty)$, with $r_w(0)=0$ and
\[
r_w'(q)=\sum_jw_j^2\,\EE\frac{g^2}{(1+w_j^2qg^2)^2}>0 ,
\]
and $r_w(q)\uparrow\#\{j:w_j>0\}\in\{1,2,\dots\}\cup\{\infty\}$ as $q\to\infty$.
\end{enumerate}
\end{lemma}
```
Encoding: `J` is `Muon.DetEquiv.J`; `C^∞ on (0,∞) with one-sided derivatives at 0` is
`ContDiffOn ℝ ∞` on `Ici 0` (one-sided derivatives of every order at 0; review L-B.1 D1) plus
the first derivative's value via `HasDerivWithinAt` on `Ici 0`. -/
theorem lem_app_de_scalar_i :
    ContinuousOn J (Ici 0) ∧
    StrictAntiOn J (Ici 0) ∧
    (∀ x, 0 ≤ x → 0 < J x ∧ J x ≤ 1) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) J (Ici 0) ∧
    HasDerivWithinAt J (-3) (Ici 0) 0 ∧
    J 0 = 1 := by
  obtain ⟨h1, h2, h3, h5, h6⟩ := J_scalar_i_no_smooth
  exact ⟨h1, h2, h3, J_contDiffOn, h5, h6⟩

/-- `lem:app-de-scalar`(ii), snapshot `cr-2026-10-22`. LaTeX (part (ii), with the lemma header
"Let $w$ be nonnegative, summable and not all zero." of l.49–50):
```
\begin{enumerate}[label=(\roman*)]
\item The series defining $F_w$ and $L_w$ converge uniformly on $[0,\infty)$;
$F_w$ and $L_w$ are continuous, $C^\infty$ on $(0,\infty)$ with one-sided
derivatives at $0$, and
\[
F_w(0)=\sw2,\qquad F_w'(0)=-3\sw4,\qquad L_w(0)=\sum_jw_j,\qquad L_w'(0)=-3\sw3 .
\]
\end{enumerate}
```
Here $\sw p=\sum_jw_j^p$ is `sumPow w p`, and $\sum_j w_j$ is `∑' j, w j`. "Converge
uniformly on $[0,\infty)$" is the uniform convergence of the partial sums to `Fw w`
(resp. `Lw w`). -/
theorem lem_app_de_scalar_ii {w : ℕ → ℝ} (hw : WeightSeq w) :
    TendstoUniformlyOn
      (fun (n : ℕ) (q : ℝ) => ∑ j ∈ Finset.range n, w j ^ 2 * J (w j ^ 2 * q))
      (Fw w) atTop (Ici 0) ∧
    TendstoUniformlyOn
      (fun (n : ℕ) (q : ℝ) => ∑ j ∈ Finset.range n, w j * J (w j ^ 2 * q))
      (Lw w) atTop (Ici 0) ∧
    ContinuousOn (Fw w) (Ici 0) ∧
    ContinuousOn (Lw w) (Ici 0) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (Fw w) (Ici 0) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (Lw w) (Ici 0) ∧
    Fw w 0 = sumPow w 2 ∧
    HasDerivWithinAt (Fw w) (-3 * sumPow w 4) (Ici 0) 0 ∧
    Lw w 0 = ∑' j, w j ∧
    HasDerivWithinAt (Lw w) (-3 * sumPow w 3) (Ici 0) 0 := by
  have hJc : ContinuousOn J (Ici 0) := fun x hx => J_continuousWithinAt hx
  have hq2 : ∀ j : ℕ, ∀ q ∈ Ici (0 : ℝ), 0 ≤ w j ^ 2 * q := fun j q hq =>
    mul_nonneg (sq_nonneg _) (Set.mem_Ici.1 hq)
  have hbF : ∀ j : ℕ, ∀ q ∈ Ici (0 : ℝ), ‖w j ^ 2 * J (w j ^ 2 * q)‖ ≤ w j ^ 2 := by
    intro j q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (J_pos (hq2 j q hq)).le)]
    exact mul_le_of_le_one_right (sq_nonneg _) (J_le_one (hq2 j q hq))
  have hbL : ∀ j : ℕ, ∀ q ∈ Ici (0 : ℝ), ‖w j * J (w j ^ 2 * q)‖ ≤ w j := by
    intro j q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw.1 j) (J_pos (hq2 j q hq)).le)]
    exact mul_le_of_le_one_right (hw.1 j) (J_le_one (hq2 j q hq))
  have hsF : Summable (fun j : ℕ => w j ^ 2) := summable_pow_of_weight hw (by norm_num)
  have hFu : TendstoUniformlyOn
      (fun (n : ℕ) (q : ℝ) => ∑ j ∈ Finset.range n, w j ^ 2 * J (w j ^ 2 * q))
      (Fw w) atTop (Ici 0) :=
    tendstoUniformlyOn_tsum_nat (f := fun j q => w j ^ 2 * J (w j ^ 2 * q)) hsF hbF
  have hLu : TendstoUniformlyOn
      (fun (n : ℕ) (q : ℝ) => ∑ j ∈ Finset.range n, w j * J (w j ^ 2 * q))
      (Lw w) atTop (Ici 0) :=
    tendstoUniformlyOn_tsum_nat (f := fun j q => w j * J (w j ^ 2 * q)) hw.2.1 hbL
  have hcF : ContinuousOn (Fw w) (Ici 0) :=
    continuousOn_tsum (f := fun j q => w j ^ 2 * J (w j ^ 2 * q))
      (fun j => continuousOn_const.mul (hJc.comp
        (by fun_prop : ContinuousOn (fun q : ℝ => w j ^ 2 * q) (Ici 0))
        (fun q hq => Set.mem_Ici.2 (hq2 j q hq)))) hsF hbF
  have hcL : ContinuousOn (Lw w) (Ici 0) :=
    continuousOn_tsum (f := fun j q => w j * J (w j ^ 2 * q))
      (fun j => continuousOn_const.mul (hJc.comp
        (by fun_prop : ContinuousOn (fun q : ℝ => w j ^ 2 * q) (Ici 0))
        (fun q hq => Set.mem_Ici.2 (hq2 j q hq)))) hw.2.1 hbL
  have hF : Fw w = fun q : ℝ => ∑' j, w j ^ (2 + 2 * 0) *
      ∫ g, g ^ (2 * 0 + 2) / (1 + w j ^ 2 * q * g ^ 2) ^ (0 + 1) ∂(gaussianReal 0 1) := by
    funext q
    simp [Fw, J]
  have hL : Lw w = fun q : ℝ => ∑' j, w j ^ (1 + 2 * 0) *
      ∫ g, g ^ (2 * 0 + 2) / (1 + w j ^ 2 * q * g ^ 2) ^ (0 + 1) ∂(gaussianReal 0 1) := by
    funext q
    simp [Lw, J]
  have hcdF : ContDiffOn ℝ (⊤ : ℕ∞) (Fw w) (Ici 0) := by
    rw [hF]
    exact contDiffOn_infty.2 (fun n => T_contDiffOn hw (by norm_num) n 0)
  have hcdL : ContDiffOn ℝ (⊤ : ℕ∞) (Lw w) (Ici 0) := by
    rw [hL]
    exact contDiffOn_infty.2 (fun n => T_contDiffOn hw (by norm_num) n 0)
  have hv0F : Fw w 0 = sumPow w 2 := by
    simp [Fw, sumPow, J_zero]
  have hv0L : Lw w 0 = ∑' j, w j := by
    simp [Lw, J_zero]
  have hd0F : HasDerivWithinAt (Fw w) (-3 * sumPow w 4) (Ici 0) 0 := by
    rw [hF]
    have h := T_hasDerivWithinAt hw (by norm_num : (2 : ℕ) ≠ 0) 0 (le_refl (0 : ℝ))
    convert h using 1
    have hval : ∀ j : ℕ, (∫ g, g ^ (2 * (0 + 1) + 2) / (1 + w j ^ 2 * 0 * g ^ 2) ^ (0 + 1 + 1)
        ∂(gaussianReal 0 1)) = 3 := by
      intro j
      norm_num
      exact Muon.Foundations.gaussian_moment_four
    simp only [hval, tsum_mul_right]
    norm_num [sumPow]
    ring
  have hd0L : HasDerivWithinAt (Lw w) (-3 * sumPow w 3) (Ici 0) 0 := by
    rw [hL]
    have h := T_hasDerivWithinAt hw (by norm_num : (1 : ℕ) ≠ 0) 0 (le_refl (0 : ℝ))
    convert h using 1
    have hval : ∀ j : ℕ, (∫ g, g ^ (2 * (0 + 1) + 2) / (1 + w j ^ 2 * 0 * g ^ 2) ^ (0 + 1 + 1)
        ∂(gaussianReal 0 1)) = 3 := by
      intro j
      norm_num
      exact Muon.Foundations.gaussian_moment_four
    simp only [hval, tsum_mul_right]
    norm_num [sumPow]
    ring
  exact ⟨hFu, hLu, hcF, hcL, hcdF, hcdL, hv0F, hd0F, hv0L, hd0L⟩

private lemma rW_strictMonoOn {w : ℕ → ℝ} (hw : WeightSeq w) : StrictMonoOn (rW w) (Ici 0) := by
  have hc : ContinuousOn (rW w) (Ici 0) := by
    have hF := (lem_app_de_scalar_ii hw).2.2.1
    exact continuousOn_id.mul hF
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) hc
  intro q hq
  rw [interior_Ici] at hq
  rw [(rW_hasDerivAt hw hq).deriv]
  exact rW_deriv_pos hw hq

/-- `lem:app-de-scalar`(iii), snapshot `cr-2026-10-22`. LaTeX (part (iii), with the lemma header
"Let $w$ be nonnegative, summable and not all zero." of l.49–50):
```
\begin{enumerate}[label=(\roman*)]
\item The function
\[
r_w(q)\defeq qF_w(q)=\sum_j\EE\frac{w_j^2qg^2}{1+w_j^2qg^2}
\]
is strictly increasing on $[0,\infty)$, with $r_w(0)=0$ and
\[
r_w'(q)=\sum_jw_j^2\,\EE\frac{g^2}{(1+w_j^2qg^2)^2}>0 ,
\]
and $r_w(q)\uparrow\#\{j:w_j>0\}\in\{1,2,\dots\}\cup\{\infty\}$ as $q\to\infty$.
\end{enumerate}
```
Encoding: the count `#{j : w_j > 0}` is `Set.encard {j | 0 < w j} : ℕ∞`, and the
increasing limit is taken in `ℝ≥0∞` via `ENNReal.ofReal (rW w q)` (so `∞` is `⊤`). The
derivative is stated for `q > 0` (`r_w'(q)` is displayed for each `q`; the positivity
clause is for `q > 0`). -/
theorem lem_app_de_scalar_iii {w : ℕ → ℝ} (hw : WeightSeq w) :
    (∀ q, 0 ≤ q → rW w q =
      ∑' j, ∫ g, w j ^ 2 * q * g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ∂(gaussianReal 0 1)) ∧
    StrictMonoOn (rW w) (Ici 0) ∧
    rW w 0 = 0 ∧
    (∀ q ∈ Ioi 0, HasDerivAt (rW w)
      (∑' j, w j ^ 2 * ∫ g, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) q) ∧
    (∀ q ∈ Ioi 0,
      0 < ∑' j, w j ^ 2 * ∫ g, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) ∧
    1 ≤ Set.encard {j | 0 < w j} ∧
    Tendsto (fun q : ℝ => ENNReal.ofReal (rW w q)) atTop
      (𝓝 (Set.encard {j | 0 < w j}).toENNReal) := by
  refine ⟨fun q _ => rW_eq_sum_int hw q, rW_strictMonoOn hw, by simp [rW],
    fun q hq => rW_hasDerivAt hw hq, fun q hq => rW_deriv_pos hw hq, ?_, rW_tail hw⟩
  obtain ⟨j, hj⟩ := hw.2.2
  exact Set.one_le_encard_iff_nonempty.2 ⟨j, lt_of_le_of_ne (hw.1 j) (Ne.symm hj)⟩

/-- `prop:app-de-nomomentum`, snapshot `cr-2026-10-22`. LaTeX
(`sections/02-deterministic-equivalents/section.tex` l.441–447):
```
\begin{proposition}[No-momentum closure]\label{prop:app-de-nomomentum}
For $q>0$ put $\xi\defeq(2q)^{-1/2}$. Then
\begin{equation}\label{eqn:app-de-erfc}
q\Jfun(q)=\EE\frac{qg^2}{1+qg^2}=\EE\frac{g^2}{g^2+2\xi^2}
=1-\sqrt\pi\,\xi\,e^{\xi^2}\operatorname{erfc}(\xi).
\end{equation}
\end{proposition}
```
The three displayed equalities are the three conjuncts. `erfc` is
`Muon.Foundations.erfc` (Mathlib has none). The two substantive identities are the
Foundations lemmas `app_de_nomomentum_ratio` and `app_de_nomomentum_erfc`. -/
theorem prop_app_de_nomomentum (q ξ : ℝ) (hq : 0 < q) (hξ : ξ = (2 * q) ^ (-(1 / 2 : ℝ))) :
    q * J q = ∫ g, q * g ^ 2 / (1 + q * g ^ 2) ∂(gaussianReal 0 1) ∧
    ∫ g, q * g ^ 2 / (1 + q * g ^ 2) ∂(gaussianReal 0 1) =
      ∫ g, g ^ 2 / (g ^ 2 + 2 * ξ ^ 2) ∂(gaussianReal 0 1) ∧
    ∫ g, g ^ 2 / (g ^ 2 + 2 * ξ ^ 2) ∂(gaussianReal 0 1) =
      1 - Real.sqrt Real.pi * ξ * Real.exp (ξ ^ 2) * Muon.Foundations.erfc ξ := by
  refine ⟨?_, Muon.Foundations.app_de_nomomentum_ratio q ξ hq hξ,
    Muon.Foundations.app_de_nomomentum_erfc q ξ hq hξ⟩
  unfold J
  rw [← integral_const_mul]
  congr 1
  ext g
  ring

/-- Card L-B.1 (not a label): `AdmissibleWeightFn (Fw w)` for every weight sequence (review L-B.1 D2: the branch theorem
and `prop:app-de-normalization`(i) use weights outside the class) (`lem:app-de-scalar` (i)–(iii) give the four properties; the positivity of `F_w`
on `[0,∞)` uses `∃ j, w j ≠ 0`). Consumed by L-B.2 and by D's `lem:app-vol-profile`. -/
theorem Fw_admissible {w : ℕ → ℝ} (hw : WeightSeq w) : AdmissibleWeightFn (Fw w) := by
  have hq2 : ∀ j : ℕ, ∀ q : ℝ, 0 ≤ q → 0 ≤ w j ^ 2 * q :=
    fun j q hq => mul_nonneg (sq_nonneg _) hq
  have hsF : Summable (fun j : ℕ => w j ^ 2) := summable_pow_of_weight hw (by norm_num)
  have hterm : ∀ q : ℝ, 0 ≤ q → ∀ j : ℕ, 0 ≤ w j ^ 2 * J (w j ^ 2 * q) :=
    fun q hq j => mul_nonneg (sq_nonneg _) (J_pos (hq2 j q hq)).le
  have hsum : ∀ q : ℝ, 0 ≤ q → Summable (fun j : ℕ => w j ^ 2 * J (w j ^ 2 * q)) := by
    intro q hq
    refine Summable.of_nonneg_of_le (hterm q hq) (fun j => ?_) hsF
    exact mul_le_of_le_one_right (sq_nonneg _) (J_le_one (hq2 j q hq))
  refine ⟨(lem_app_de_scalar_ii hw).2.2.1, ?_, ?_, rW_strictMonoOn hw, by simp [rW]⟩
  · intro q hq
    have hq' : (0 : ℝ) ≤ q := hq
    obtain ⟨j, hj⟩ := hw.2.2
    show 0 < ∑' j, w j ^ 2 * J (w j ^ 2 * q)
    refine Summable.tsum_pos (hsum q hq') (hterm q hq') j ?_
    exact mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj)))
      (J_pos (hq2 j q hq'))
  · intro q hq
    have hq' : (0 : ℝ) ≤ q := hq
    show ∑' j, w j ^ 2 * J (w j ^ 2 * q) ≤ ∑' j, w j ^ 2 * J (w j ^ 2 * 0)
    refine Summable.tsum_le_tsum (fun j => ?_) (hsum q hq') (hsum 0 le_rfl)
    have h0 : w j ^ 2 * 0 ≤ w j ^ 2 * q := mul_le_mul_of_nonneg_left hq' (sq_nonneg _)
    have hJ : J (w j ^ 2 * q) ≤ J (w j ^ 2 * 0) :=
      J_strictAntiOn.antitoneOn (Set.mem_Ici.2 (by simp)) (Set.mem_Ici.2 (hq2 j q hq')) h0
    exact mul_le_mul_of_nonneg_left hJ (sq_nonneg _)

end Muon.DetEquiv

end

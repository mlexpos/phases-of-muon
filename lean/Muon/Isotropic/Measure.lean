import Muon.Isotropic.Aspect
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

/-!
# Appendix F: the isotropic measure pair, negative-axis transforms, and the small and large aspect laws

Task L-F.6 (interface). Snapshot `cr-2026-10-23`. Source: `sections/05b-isotropic/section.tex`.
Labels owned (queue `L-F.6`, card §3/§5 item 6): `def:app-iso-measure` (l.787–796),
`lem:app-iso-transforms` (l.810–821), `lem:app-iso-moments` (l.863–884), `prop:app-iso-measure`
(l.948–951), `prop:app-iso-spectral` (l.999–1017), `prop:app-iso-reciprocity` part (i) (l.1589–1608),
`thm:app-iso-small` (l.1508–1531), `thm:app-iso-large` (l.1640–1665). Also the square-pair helpers
`isoPair_square_iff` and `isoPair_square_eq` (l.798–806, card §5 item 6) and the preamble facts of
`eqn:app-iso-chi` (`isoChi_facts`, used by `thm:app-iso-large`).

Reuse (never redefined here): `Muon.Isotropic.isoNegStieltjes` (`S_ν(−t)`, Aspect), `isoMP`, `isoMPa`,
`isoMPb`, `isoJr` (`𝖬_r`, `a_r`, `b_r`, `J_r`; Aspect), `Cbeta` (`C_β`; ZeroRidge), `psiIso`
(`ψ`; ZeroRidge), `isoPhi` (`Φ`; Helpers). The pair-free helpers `C0_small_asymp` and `C0_large_bound`
of Aspect are not restated; the square small-aspect limit in `thm_app_iso_small_iii` is written out
in full, since it is a conjunct of the source statement.

Interface choices (faithfulness notes):
* `IsIsoMeasurePair γin γout mo mi` is the structure of `def:app-iso-measure`, with `mo` for
  `𝔪_out` and `mi` for `𝔪_in` (`mi` avoids shadowing `min`). Its positivity fields carry the standing
  hypothesis `γin,γout>0` of the definition; masses are `ENNReal.ofReal γ`, which makes the measures finite.
* Weak convergence of probability measures on `ℝ` is tested against bounded continuous functions
  `BoundedContinuousFunction ℝ ℝ` (the Portmanteau form of the source's "converges weakly").
* Integrals of nonnegative functions against the measures in the lemmas carry an explicit
  `Integrable` clause wherever the source asserts a finite value, since Bochner integrals of
  non-integrable functions are `0` in Lean.
* The restriction `(mo j).restrict (Ioi 0)` is the probability measure `η_j` of `lem:app-iso-moments`(iv):
  by that part, `η_j` is determined by `mo j` as its restriction to `(0,∞)`. The proofs use part (iv) to
  identify it; the statements do not take it as a hypothesis.
* `thm:app-iso-small` and `thm:app-iso-large` take the pair as a hypothesis for each index `j`, as the
  source does (`prop:app-iso-measure` gives its existence); they are stated for sequences
  `ℕ → ℝ` with the limits written as `Tendsto` filters.
* Every theorem is a statement only (`sorry`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

noncomputable section

namespace Muon.Isotropic

/-! ## Definitions -/

/-- `m̂_b`: the image of a measure under `λ ↦ λ/b` (`prop:app-iso-spectral`, l.1010–1017; the
pushforward of `𝔪_out`, and of `𝔪_out/γout` in `prop:app-iso-reciprocity`(i)). -/
def isoScaledImage (b : ℝ) (m : Measure ℝ) : Measure ℝ :=
  Measure.map (fun l : ℝ => l / b) m

/-- `P`: the image of `m/γ` under `λ ↦ λ/γ`, the normalized measure of `thm:app-iso-small`
and `prop:app-iso-reciprocity`(i); for `m = 𝔪_out` it is a probability measure. -/
def isoNormMeasure (γ : ℝ) (m : Measure ℝ) : Measure ℝ :=
  Measure.map (fun l : ℝ => l / γ) (ENNReal.ofReal γ⁻¹ • m)

/-- The law of `g²` for `g ∼ 𝒩(0,1)` (`𝖷` of `eqn:app-iso-chi`, `thm:app-iso-large`). -/
def isoChi : Measure ℝ :=
  Measure.map (fun g : ℝ => g ^ 2) (gaussianReal 0 1)

/-- Isotropic measure pair (`def:app-iso-measure`, `section.tex` l.787–796): finite nonnegative
measures `𝔪_out`, `𝔪_in` on `[0,∞)` of masses `γout`, `γin`, whose transforms
`σ(−t) = S_{𝔪_out}(−t)` and `σ̃(−t) = S_{𝔪_in}(−t)` satisfy, for every `t>0`,
`γout − tσ(−t) = γin − tσ̃(−t) = Φ(tσ(−t)σ̃(−t))`. -/
structure IsIsoMeasurePair (γin γout : ℝ) (mo mi : Measure ℝ) : Prop where
  pos_in : 0 < γin
  pos_out : 0 < γout
  mass_out : mo univ = ENNReal.ofReal γout
  mass_in : mi univ = ENNReal.ofReal γin
  supp_out : mo (Iio 0) = 0
  supp_in : mi (Iio 0) = 0
  identity : ∀ t : ℝ, 0 < t →
    γout - t * isoNegStieltjes mo t = γin - t * isoNegStieltjes mi t ∧
      γout - t * isoNegStieltjes mo t =
        isoPhi (t * isoNegStieltjes mo t * isoNegStieltjes mi t)

/-! ## Negative-axis transforms -/

private theorem ae_nonneg_of_Iio (μ : Measure ℝ) (h0 : μ (Iio 0) = 0) : ∀ᵐ x ∂μ, 0 ≤ x := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext; simp
  rw [this]; exact h0

private theorem inv_pow_le (t x s : ℝ) (ht : 0 < t) (hx : 0 ≤ x) (hs : t / 2 < s) (n : ℕ) :
    ((x + s) ^ n)⁻¹ ≤ (2 / t) ^ n := by
  have h1 : (x + s)⁻¹ ≤ 2 / t := by
    have h2 : t / 2 ≤ x + s := by linarith
    calc (x + s)⁻¹ ≤ (t / 2)⁻¹ := inv_anti₀ (by positivity) h2
      _ = 2 / t := by rw [inv_div]
  rw [← inv_pow]
  exact pow_le_pow_left₀ (by have : 0 < x + s := by linarith
                             positivity) h1 n

private theorem resPow_hasDeriv (μ : Measure ℝ) [IsFiniteMeasure μ] (h0 : μ (Iio 0) = 0)
    (k : ℕ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ x, (((x + s) ^ (k + 1))⁻¹) ∂μ)
      (-((k : ℝ) + 1) * ∫ x, (((x + t) ^ (k + 2))⁻¹) ∂μ) t := by
  have hnn := ae_nonneg_of_Iio μ h0
  have hs : Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have hmeas : ∀ s : ℝ, Measurable (fun x : ℝ => ((x + s) ^ (k + 1))⁻¹) := fun s => by fun_prop
  have hmeas' : ∀ s : ℝ, Measurable (fun x : ℝ => -((k : ℝ) + 1) * ((x + s) ^ (k + 2))⁻¹) :=
    fun s => by fun_prop
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := t)
    (F := fun s x => ((x + s) ^ (k + 1))⁻¹)
    (F' := fun s x => -((k : ℝ) + 1) * ((x + s) ^ (k + 2))⁻¹)
    (bound := fun _ => ((k : ℝ) + 1) * (2 / t) ^ (k + 2)) hs
    (Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable)
    (by
      refine Integrable.mono' (integrable_const ((2 / t) ^ (k + 1)))
        (hmeas t).aestronglyMeasurable ?_
      filter_upwards [hnn] with x hx
      have hxt : 0 < x + t := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_pow_le t x t ht hx (by linarith) _)
    (hmeas' t).aestronglyMeasurable
    (by
      filter_upwards [hnn] with x hx s hs'
      have hs'' : t / 2 < s := hs'
      have hxs : 0 < x + s := by linarith
      have := inv_pow_le t x s ht hx hs'' (k + 2)
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) + 1),
        abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left this (by positivity))
    (integrable_const _)
    (by
      filter_upwards [hnn] with x hx s hs'
      have hs'' : t / 2 < s := hs'
      have hxs : 0 < x + s := by linarith
      have h1 : HasDerivAt (fun s : ℝ => x + s) 1 s := by simpa using (hasDerivAt_id s).const_add x
      have h2 := (h1.pow (k + 1)).inv (by simpa using (pow_pos hxs (k + 1)).ne')
      convert h2 using 1
      simp only [Pi.pow_apply]
      push_cast
      field_simp
      ring)
  have := key.2
  rwa [integral_const_mul] at this

private theorem resPow_eq (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0)
    (htr : ∀ t : ℝ, 0 < t → ∫ x, (x + t)⁻¹ ∂μ = ∫ x, (x + t)⁻¹ ∂ν) :
    ∀ k : ℕ, ∀ t : ℝ, 0 < t →
      ∫ x, (((x + t) ^ (k + 1))⁻¹) ∂μ = ∫ x, (((x + t) ^ (k + 1))⁻¹) ∂ν := by
  intro k
  induction k with
  | zero => intro t ht; simpa using htr t ht
  | succ k ih =>
    intro t ht
    have h1 := resPow_hasDeriv μ hμ0 k t ht
    have h2 := resPow_hasDeriv ν hν0 k t ht
    have h3 : HasDerivAt (fun s : ℝ => ∫ x, (((x + s) ^ (k + 1))⁻¹) ∂ν)
        (-((k : ℝ) + 1) * ∫ x, (((x + t) ^ (k + 2))⁻¹) ∂μ) t := by
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds ht] with s hs using (ih s hs).symm
    have := h3.unique h2
    have hk : (-((k : ℝ) + 1)) ≠ 0 := by have : (0:ℝ) ≤ k := Nat.cast_nonneg k
                                         linarith
    exact mul_left_cancel₀ hk this

private theorem moment_eq (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0)
    (hmass : μ univ = ν univ)
    (htr : ∀ t : ℝ, 0 < t → ∫ x, (x + t)⁻¹ ∂μ = ∫ x, (x + t)⁻¹ ∂ν) (n : ℕ) :
    ∫ x, ((1 + x)⁻¹) ^ n ∂μ = ∫ x, ((1 + x)⁻¹) ^ n ∂ν := by
  cases n with
  | zero =>
    simp only [pow_zero, integral_const, smul_eq_mul, mul_one]
    simp [Measure.real, hmass]
  | succ k =>
    have := resPow_eq μ ν hμ0 hν0 htr k 1 one_pos
    simpa [inv_pow, add_comm] using this

private theorem poly_integral_eq (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0)
    (hmom : ∀ n : ℕ, ∫ x, ((1 + x)⁻¹) ^ n ∂μ = ∫ x, ((1 + x)⁻¹) ^ n ∂ν) (P : Polynomial ℝ) :
    ∫ x, P.eval ((1 + x)⁻¹) ∂μ = ∫ x, P.eval ((1 + x)⁻¹) ∂ν := by
  have hint : ∀ (m : Measure ℝ) [IsFiniteMeasure m], m (Iio 0) = 0 → ∀ i : ℕ,
      Integrable (fun x : ℝ => ((1 + x)⁻¹) ^ i) m := by
    intro m _ hm0 i
    refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop : Measurable _).aestronglyMeasurable ?_
    filter_upwards [ae_nonneg_of_Iio m hm0] with x hx
    have h1 : (1 + x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have h2 : 0 ≤ (1 + x)⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h2 _)]
    exact pow_le_one₀ h2 h1
  have key : ∀ (m : Measure ℝ) [IsFiniteMeasure m], m (Iio 0) = 0 →
      ∫ x, P.eval ((1 + x)⁻¹) ∂m =
        ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * ∫ x, ((1 + x)⁻¹) ^ i ∂m := by
    intro m _ hm0
    simp_rw [Polynomial.eval_eq_sum_range]
    rw [integral_finsetSum _ (fun i _ => (hint m hm0 i).const_mul _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  rw [key μ hμ0, key ν hν0]
  exact Finset.sum_congr rfl fun i _ => by rw [hmom i]

private theorem ext_of_moments (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0)
    (hmom : ∀ n : ℕ, ∫ x, ((1 + x)⁻¹) ^ n ∂μ = ∫ x, ((1 + x)⁻¹) ^ n ∂ν) : μ = ν := by
  have : PolishSpace (Ici (0:ℝ)) := isClosed_Ici.polishSpace
  obtain ⟨r, hr⟩ : ∃ r : BoundedContinuousFunction (Ici (0:ℝ)) ℝ, ∀ y, r y = (1 + y.1)⁻¹ := by
    refine ⟨BoundedContinuousFunction.mkOfBound
      ⟨fun y => (1 + y.1)⁻¹, ?_⟩ 1 ?_, fun _ => rfl⟩
    · have : ∀ y : Ici (0:ℝ), (1 + y.1) ≠ 0 := fun y => by have := y.2; simp only [mem_Ici] at this; linarith
      exact Continuous.inv₀ (by fun_prop) this
    · intro x y
      have hx := x.2; have hy := y.2
      simp only [mem_Ici] at hx hy
      have a1 : (1 + x.1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have a2 : (1 + y.1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have b1 : 0 ≤ (1 + x.1)⁻¹ := inv_nonneg.mpr (by linarith)
      have b2 : 0 ≤ (1 + y.1)⁻¹ := inv_nonneg.mpr (by linarith)
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_le]; constructor <;> linarith
  let A : StarSubalgebra ℝ (BoundedContinuousFunction (Ici (0:ℝ)) ℝ) := StarAlgebra.adjoin ℝ {r}
  have hA : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    refine ⟨fun z => r z, ⟨(BoundedContinuousFunction.toContinuousMapStarₐ ℝ) r, ?_, rfl⟩, ?_⟩
    · exact ⟨r, StarAlgebra.self_mem_adjoin_singleton ℝ r, rfl⟩
    · simp only [hr]
      intro h
      apply hxy
      apply Subtype.ext
      have h1 : 0 < 1 + x.1 := by have := x.2; simp only [mem_Ici] at this; linarith
      have h2 : 0 < 1 + y.1 := by have := y.2; simp only [mem_Ici] at this; linarith
      have := inv_injective h
      linarith
  have hmem : ∀ g ∈ A, ∃ P : Polynomial ℝ, ∀ y, g y = P.eval (r y) := by
    intro g hg
    have hg' : g ∈ Algebra.adjoin ℝ ({r} ∪ star {r} : Set (BoundedContinuousFunction (Ici (0:ℝ)) ℝ)) := hg
    have hstar : star ({r} : Set (BoundedContinuousFunction (Ici (0:ℝ)) ℝ)) = {r} := by
      ext f; simp only [Set.mem_star, mem_singleton_iff]
      constructor <;> intro h <;> subst h <;> (ext; simp)
    rw [hstar, Set.union_self, Algebra.adjoin_singleton_eq_range_aeval] at hg'
    obtain ⟨P, rfl⟩ := hg'
    refine ⟨P, fun y => ?_⟩
    clear hg
    show ((Polynomial.aeval r) P) y = _
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simp [hp, hq]
    | monomial n a => simp
  have hp : Measurable (Set.projIci (0:ℝ)) := (measurable_const.max measurable_id).subtype_mk
  have e : ∀ (g : BoundedContinuousFunction (Ici (0:ℝ)) ℝ) (P : Polynomial ℝ),
      (∀ y, g y = P.eval (r y)) → ∀ m : Measure ℝ, m (Iio 0) = 0 →
      ∫ x, g (Set.projIci (0:ℝ) x) ∂m = ∫ x, P.eval ((1 + x)⁻¹) ∂m := by
    intro g P hP m hm
    refine integral_congr_ae ?_
    filter_upwards [ae_nonneg_of_Iio m hm] with x hx
    rw [hP, hr]
    simp [Set.coe_projIci, max_eq_right hx]
  have hEq : μ.map (Set.projIci (0:ℝ)) = ν.map (Set.projIci (0:ℝ)) := by
    refine ext_of_forall_mem_subalgebra_integral_eq_of_polish (𝕜 := ℝ) (A := A) hA ?_
    intro g hg
    obtain ⟨P, hP⟩ := hmem g hg
    rw [integral_map hp.aemeasurable g.continuous.aestronglyMeasurable,
      integral_map hp.aemeasurable g.continuous.aestronglyMeasurable,
      e g P hP μ hμ0, e g P hP ν hν0]
    exact poly_integral_eq μ ν hμ0 hν0 hmom P
  have back : ∀ m : Measure ℝ, m (Iio 0) = 0 →
      (m.map (Set.projIci (0:ℝ))).map Subtype.val = m := by
    intro m hm
    rw [Measure.map_map measurable_subtype_coe hp]
    have : (Subtype.val ∘ Set.projIci (0:ℝ)) =ᵐ[m] id := by
      filter_upwards [ae_nonneg_of_Iio m hm] with x hx
      simp [Set.coe_projIci, max_eq_right hx]
    rw [Measure.map_congr this, Measure.map_id]
  rw [← back μ hμ0, ← back ν hν0, hEq]

private theorem resolvent_integrable (m : Measure ℝ) [IsFiniteMeasure m] (h0 : m (Iio 0) = 0)
    (T : ℝ) (hT : 0 < T) : Integrable (fun x : ℝ => (x + T)⁻¹) m := by
  refine Integrable.mono' (integrable_const T⁻¹) (by fun_prop : Measurable _).aestronglyMeasurable ?_
  filter_upwards [ae_nonneg_of_Iio m h0] with x hx
  have h1 : 0 < x + T := by linarith
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h1)]
  exact inv_anti₀ hT (by linarith)

private theorem tail_bound (m : Measure ℝ) [IsProbabilityMeasure m] (h0 : m (Iio 0) = 0)
    (T : ℝ) (hT : 0 < T) :
    (m (Ioi T)).toReal ≤ 2 * (1 - T * ∫ x, (x + T)⁻¹ ∂m) := by
  have hint := resolvent_integrable m h0 T hT
  have e1 : (m (Ioi T)).toReal = ∫ x, (Ioi T).indicator (fun _ => (1:ℝ)) x ∂m := by
    rw [integral_indicator_const (1:ℝ) measurableSet_Ioi]; simp [Measure.real]
  have e2 : ∫ x, 2 * (1 - T * (x + T)⁻¹) ∂m = 2 * (1 - T * ∫ x, (x + T)⁻¹ ∂m) := by
    rw [integral_const_mul, integral_sub (integrable_const _) (hint.const_mul T),
      integral_const_mul]
    simp
  rw [e1, ← e2]
  refine integral_mono_ae ((integrable_const (1:ℝ)).indicator measurableSet_Ioi)
    ((integrable_const _).sub (hint.const_mul T) |>.const_mul 2) ?_
  filter_upwards [ae_nonneg_of_Iio m h0] with x hx
  have h1 : 0 < x + T := by linarith
  have h2 : T * (x + T)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one h1]; linarith
  by_cases hxT : T < x
  · rw [Set.indicator_of_mem (by exact hxT)]
    have : T * (x + T)⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ h1]; linarith
    linarith
  · rw [Set.indicator_of_notMem (by exact hxT)]
    linarith

private theorem tail_small (m : Measure ℝ) [IsProbabilityMeasure m] (h0 : m (Iio 0) = 0) :
    Tendsto (fun T : ℝ => 1 - T * ∫ x, (x + T)⁻¹ ∂m) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => ∫ x, x / (x + T) ∂m) atTop (𝓝 (∫ _x : ℝ, (0:ℝ) ∂m)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ)) ?_ ?_
      (integrable_const _) ?_
    · exact Eventually.of_forall fun T => (by fun_prop : Measurable _).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with T hT
      filter_upwards [ae_nonneg_of_Iio m h0] with x hx
      have h1 : 0 < x + T := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hx h1.le), div_le_one h1]
      linarith
    · filter_upwards with x
      exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_id)
  simp only [integral_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hint := resolvent_integrable m h0 T hT
  have : ∫ x, x / (x + T) ∂m = ∫ x, (1 - T * (x + T)⁻¹) ∂m := by
    refine integral_congr_ae ?_
    filter_upwards [ae_nonneg_of_Iio m h0] with x hx
    have h1 : 0 < x + T := by linarith
    field_simp
    ring
  rw [this, integral_sub (integrable_const _) (hint.const_mul T), integral_const_mul]
  simp

private theorem seq_tight (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (ν j)) (hsupp : ∀ j, ν j (Iio 0) = 0)
    (hprob₀ : IsProbabilityMeasure ν₀) (hsupp₀ : ν₀ (Iio 0) = 0)
    (hconv : ∀ t : ℝ, 0 < t →
      Tendsto (fun j => ∫ x, (x + t)⁻¹ ∂(ν j)) atTop (𝓝 (∫ x, (x + t)⁻¹ ∂ν₀))) :
    ∀ ε : ENNReal, 0 < ε → ∃ K : Set ℝ, IsCompact K ∧ ∀ j, ν j Kᶜ ≤ ε := by
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun j => by simp [hεt]⟩
  have hδ : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  set δ := ε.toReal with hδdef
  obtain ⟨T, hT1, hT0⟩ := ((tail_small ν₀ hsupp₀).eventually
      (eventually_lt_nhds (show (0:ℝ) < δ / 4 by positivity))).and
      (eventually_gt_atTop (0:ℝ)) |>.exists
  obtain ⟨J, hJ⟩ := eventually_atTop.1
    ((tendsto_const_nhds.sub ((hconv T hT0).const_mul T)).eventually
      (eventually_lt_nhds (show 1 - T * ∫ x, (x + T)⁻¹ ∂ν₀ < δ / 2 by linarith)))
  have hK : ∀ j, ∃ K : Set ℝ, IsCompact K ∧ ν j Kᶜ ≤ ε := by
    intro j
    have := hprob j
    obtain ⟨K, hK, h⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
      (isTightMeasureSet_singleton (μ := ν j)) ε hε
    exact ⟨K, hK, h _ rfl⟩
  choose Kj hKj using hK
  refine ⟨Icc 0 T ∪ ⋃ j ∈ Finset.range J, Kj j, isCompact_Icc.union
    (Finset.isCompact_biUnion _ fun j _ => (hKj j).1), fun j => ?_⟩
  by_cases hj : j < J
  · refine le_trans (measure_mono ?_) (hKj j).2
    intro x hx hx'
    exact hx (Or.inr (mem_biUnion (Finset.mem_range.2 hj) hx'))
  · have := hprob j
    have hb := tail_bound (ν j) (hsupp j) T hT0
    have hj' := hJ j (not_lt.1 hj)
    have h3 : (ν j (Ioi T)).toReal ≤ δ := by
      linarith
    refine le_trans (measure_mono ?_) (le_trans (measure_union_le (Iio 0) (Ioi T)) ?_)
    · intro x hx
      by_contra hxn
      simp only [mem_union, mem_Iio, mem_Ioi, not_or, not_lt] at hxn
      exact hx (Or.inl ⟨hxn.1, hxn.2⟩)
    · rw [hsupp j, zero_add, ← ENNReal.ofReal_toReal (measure_ne_top (ν j) (Ioi T)),
        ← ENNReal.ofReal_toReal hεt]
      exact ENNReal.ofReal_le_ofReal h3

private theorem weak_conv (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (ν j)) (hsupp : ∀ j, ν j (Iio 0) = 0)
    (hprob₀ : IsProbabilityMeasure ν₀) (hsupp₀ : ν₀ (Iio 0) = 0)
    (hconv : ∀ t : ℝ, 0 < t →
      Tendsto (fun j => ∫ x, (x + t)⁻¹ ∂(ν j)) atTop (𝓝 (∫ x, (x + t)⁻¹ ∂ν₀))) :
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop (𝓝 (∫ x, f x ∂ν₀)) := by
  let P : ℕ → ProbabilityMeasure ℝ := fun j => ⟨ν j, hprob j⟩
  let P₀ : ProbabilityMeasure ℝ := ⟨ν₀, hprob₀⟩
  have hP : Tendsto P atTop (𝓝 P₀) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    have htight : IsTightMeasureSet
        {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range P} := by
      rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
      intro ε hε
      obtain ⟨K, hK, h⟩ := seq_tight ν ν₀ hprob hsupp hprob₀ hsupp₀ hconv ε hε
      refine ⟨K, hK, ?_⟩
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      exact h j
    have hcomp : IsCompact (closure (Set.range P)) := isCompact_closure_of_isTightMeasureSet htight
    obtain ⟨a, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (x := P ∘ ns)
      (fun n => subset_closure ⟨ns n, rfl⟩)
    refine ⟨φ, ?_⟩
    suffices ha : a = P₀ by rw [← ha]; exact hlim
    have ha0 : (a : Measure ℝ) (Iio 0) = 0 := by
      have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (G := Iio (0:ℝ)) isOpen_Iio
      have : (fun n => (((P ∘ ns) ∘ φ) n : Measure ℝ) (Iio 0)) = fun _ => 0 :=
        funext fun n => hsupp _
      rw [this, liminf_const] at h
      exact le_antisymm h (zero_le)
    have htr : ∀ t : ℝ, 0 < t → ∫ x, (x + t)⁻¹ ∂(a : Measure ℝ) = ∫ x, (x + t)⁻¹ ∂ν₀ := by
      intro t ht
      obtain ⟨h, hh⟩ : ∃ h : BoundedContinuousFunction ℝ ℝ, ∀ x, h x = (max x 0 + t)⁻¹ := by
        refine ⟨BoundedContinuousFunction.mkOfBound ⟨fun x => (max x 0 + t)⁻¹, ?_⟩ t⁻¹ ?_,
          fun _ => rfl⟩
        · exact Continuous.inv₀ (by fun_prop) (fun x => by
            have := le_max_right x 0; linarith)
        · intro x y
          have hx : (max x 0 + t)⁻¹ ≤ t⁻¹ := inv_anti₀ ht (by have := le_max_right x 0; linarith)
          have hy : (max y 0 + t)⁻¹ ≤ t⁻¹ := inv_anti₀ ht (by have := le_max_right y 0; linarith)
          have hx0 : 0 ≤ (max x 0 + t)⁻¹ := inv_nonneg.mpr (by have := le_max_right x 0; linarith)
          have hy0 : 0 ≤ (max y 0 + t)⁻¹ := inv_nonneg.mpr (by have := le_max_right y 0; linarith)
          simp only [ContinuousMap.coe_mk, Real.dist_eq]
          rw [abs_le]; constructor <;> linarith
      have hae : ∀ m : Measure ℝ, m (Iio 0) = 0 →
          ∫ x, h x ∂m = ∫ x, (x + t)⁻¹ ∂m := by
        intro m hm
        refine integral_congr_ae ?_
        filter_upwards [ae_nonneg_of_Iio m hm] with x hx
        rw [hh, max_eq_left hx]
      have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) h
      have h2 : Tendsto (fun n => ∫ x, h x ∂(((P ∘ ns) ∘ φ) n : Measure ℝ)) atTop
          (𝓝 (∫ x, (x + t)⁻¹ ∂ν₀)) := by
        have := (hconv t ht).comp (hns.comp hφ.tendsto_atTop)
        refine this.congr fun n => ?_
        exact (hae _ (hsupp _)).symm
      rw [← hae _ ha0, ← hae _ hsupp₀]
      have h2' : Tendsto (fun n => ∫ x, h x ∂(((P ∘ ns) ∘ φ) n : Measure ℝ)) atTop
          (𝓝 (∫ x, h x ∂ν₀)) := by rw [hae _ hsupp₀]; exact h2
      exact tendsto_nhds_unique h1 h2'
    have := a.prop
    exact Subtype.ext (ext_of_moments (a : Measure ℝ) ν₀ ha0 hsupp₀
      (moment_eq (a : Measure ℝ) ν₀ ha0 hsupp₀ (by simp) htr))
  intro f
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hP f

private theorem sqrt_tail (m : Measure ℝ) [IsProbabilityMeasure m] (h0 : m (Iio 0) = 0)
    (hint : Integrable (fun x : ℝ => x) m) (K : ℝ) (hK : 0 < K) :
    Integrable (fun x : ℝ => Real.sqrt x) m ∧
    |∫ x, Real.sqrt x ∂m - ∫ x, min (Real.sqrt x) K ∂m| ≤ (∫ x, x ∂m) / K := by
  have hsq : Integrable (fun x : ℝ => Real.sqrt x) m := by
    refine Integrable.mono' (hint.add (integrable_const (1:ℝ)))
      Real.continuous_sqrt.measurable.aestronglyMeasurable ?_
    filter_upwards [ae_nonneg_of_Iio m h0] with x hx
    have h1 := Real.sq_sqrt hx
    have h2 := Real.sqrt_nonneg x
    rw [Real.norm_eq_abs, abs_of_nonneg h2]
    show Real.sqrt x ≤ x + 1
    nlinarith [sq_nonneg (Real.sqrt x - 1)]
  have hmin : Integrable (fun x : ℝ => min (Real.sqrt x) K) m := by
    refine Integrable.mono' (integrable_const K)
      (Real.continuous_sqrt.measurable.min measurable_const).aestronglyMeasurable ?_
    filter_upwards with x
    have h2 := Real.sqrt_nonneg x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min h2 hK.le)]
    exact min_le_right _ _
  refine ⟨hsq, ?_⟩
  rw [← integral_sub hsq hmin]
  have hnn : 0 ≤ᵐ[m] fun x => Real.sqrt x - min (Real.sqrt x) K := by
    filter_upwards with x using sub_nonneg.2 (min_le_left _ _)
  rw [abs_of_nonneg (integral_nonneg_of_ae hnn), ← integral_div]
  refine integral_mono_ae (hsq.sub hmin) (hint.div_const K) ?_
  filter_upwards [ae_nonneg_of_Iio m h0] with x hx
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sqrt_nonneg x
  rw [le_div_iff₀ hK]
  by_cases hs : Real.sqrt x ≤ K
  · rw [min_eq_left hs]; simp; positivity
  · rw [not_le] at hs
    rw [min_eq_right hs.le]
    nlinarith

private theorem sqrt_part (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (ν j)) (hsupp : ∀ j, ν j (Iio 0) = 0)
    (hprob₀ : IsProbabilityMeasure ν₀) (hsupp₀ : ν₀ (Iio 0) = 0)
    (hweak : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop (𝓝 (∫ x, f x ∂ν₀)))
    (hint : ∀ j, Integrable (fun x : ℝ => x) (ν j)) (hint₀ : Integrable (fun x : ℝ => x) ν₀)
    (hbdd : BddAbove (Set.range fun j => ∫ x, x ∂(ν j))) :
    Tendsto (fun j => ∫ x, Real.sqrt x ∂(ν j)) atTop (𝓝 (∫ x, Real.sqrt x ∂ν₀)) := by
  obtain ⟨C, hC⟩ := hbdd
  set B := max C (∫ x, x ∂ν₀) with hB
  have hBj : ∀ j, ∫ x, x ∂(ν j) ≤ B := fun j => (hC ⟨j, rfl⟩).trans (le_max_left _ _)
  have hB0 : ∫ x, x ∂ν₀ ≤ B := le_max_right _ _
  have hBpos : 0 ≤ B := by
    refine le_trans ?_ hB0
    exact integral_nonneg_of_ae (by
      filter_upwards [ae_nonneg_of_Iio ν₀ hsupp₀] with x hx using hx)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K := 3 * (B + 1) / ε with hKdef
  have hK : 0 < K := by positivity
  have hBK : B / K < ε / 3 := by
    rw [div_lt_iff₀ hK, hKdef]
    field_simp
    nlinarith
  obtain ⟨f, hf⟩ : ∃ f : BoundedContinuousFunction ℝ ℝ, ∀ x, f x = min (Real.sqrt x) K := by
    refine ⟨BoundedContinuousFunction.mkOfBound
      ⟨fun x => min (Real.sqrt x) K, Real.continuous_sqrt.min continuous_const⟩ K ?_,
      fun _ => rfl⟩
    intro x y
    have hx := Real.sqrt_nonneg x
    have hy := Real.sqrt_nonneg y
    have a1 : min (Real.sqrt x) K ≤ K := min_le_right _ _
    have a2 : min (Real.sqrt y) K ≤ K := min_le_right _ _
    have b1 : 0 ≤ min (Real.sqrt x) K := le_min hx hK.le
    have b2 : 0 ≤ min (Real.sqrt y) K := le_min hy hK.le
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    rw [abs_le]; constructor <;> linarith
  have hfun : (fun x => f x) = fun x => min (Real.sqrt x) K := funext hf
  have hw := hweak f
  simp_rw [hf] at hw
  rw [Metric.tendsto_atTop] at hw
  obtain ⟨N, hN⟩ := hw (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have := hprob n
  have h1 := (sqrt_tail (ν n) (hsupp n) (hint n) K hK).2
  have h2 := (sqrt_tail ν₀ hsupp₀ hint₀ K hK).2
  have h3 := hN n hn
  rw [Real.dist_eq] at h3 ⊢
  have e1 : (∫ x, x ∂(ν n)) / K ≤ B / K := div_le_div_of_nonneg_right (hBj n) hK.le
  have e2 : (∫ x, x ∂ν₀) / K ≤ B / K := div_le_div_of_nonneg_right hB0 hK.le
  rw [abs_le] at h1 h2
  rw [abs_lt] at h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]


/-- lem:app-iso-transforms, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.810–821):
```latex
\begin{lemma}[Negative-axis transforms]\label{lem:app-iso-transforms}
\begin{enumerate}[label=(\roman*)]
\item Let $\nu_j$ $(j\ge1)$ and $\nu$ be probability measures on $[0,\infty)$
with $S_{\nu_j}(-t)\to S_\nu(-t)$ for every $t>0$. Then $\nu_j\to\nu$
weakly. If moreover $\sup_j\int x\,\nu_j(\dif x)<\infty$ and $\int x\,\nu(\dif x)<\infty$, then
\[
\int\sqrt x\,\nu_j(\dif x)\longrightarrow\int\sqrt x\,\nu(\dif x).
\]
\item Two finite nonnegative measures on $[0,\infty)$ with equal masses and
equal transforms at every $-t$, $t>0$, are equal.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_transforms_i (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (ν j)) (hsupp : ∀ j, ν j (Iio 0) = 0)
    (hprob₀ : IsProbabilityMeasure ν₀) (hsupp₀ : ν₀ (Iio 0) = 0)
    (hconv : ∀ t : ℝ, 0 < t →
      Tendsto (fun j => isoNegStieltjes (ν j) t) atTop (𝓝 (isoNegStieltjes ν₀ t))) :
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop (𝓝 (∫ x, f x ∂ν₀))) ∧
    ((∀ j, Integrable (fun x : ℝ => x) (ν j)) → Integrable (fun x : ℝ => x) ν₀ →
      BddAbove (Set.range fun j => ∫ x, x ∂(ν j)) →
      Tendsto (fun j => ∫ x, Real.sqrt x ∂(ν j)) atTop (𝓝 (∫ x, Real.sqrt x ∂ν₀))) := by
  have hweak := weak_conv ν ν₀ hprob hsupp hprob₀ hsupp₀ (fun t ht => hconv t ht)
  exact ⟨hweak, fun h1 h2 h3 => sqrt_part ν ν₀ hprob hsupp hprob₀ hsupp₀ hweak h1 h2 h3⟩

/-- lem:app-iso-transforms, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.810–821):
```latex
\begin{lemma}[Negative-axis transforms]\label{lem:app-iso-transforms}
\begin{enumerate}[label=(\roman*)]
\item Let $\nu_j$ $(j\ge1)$ and $\nu$ be probability measures on $[0,\infty)$
with $S_{\nu_j}(-t)\to S_\nu(-t)$ for every $t>0$. Then $\nu_j\to\nu$
weakly. If moreover $\sup_j\int x\,\nu_j(\dif x)<\infty$ and $\int x\,\nu(\dif x)<\infty$, then
\[
\int\sqrt x\,\nu_j(\dif x)\longrightarrow\int\sqrt x\,\nu(\dif x).
\]
\item Two finite nonnegative measures on $[0,\infty)$ with equal masses and
equal transforms at every $-t$, $t>0$, are equal.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_transforms_ii {μ ν : Measure ℝ} (hμ : IsFiniteMeasure μ)
    (hν : IsFiniteMeasure ν) (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0)
    (hmass : μ univ = ν univ)
    (htr : ∀ t : ℝ, 0 < t → isoNegStieltjes μ t = isoNegStieltjes ν t) :
    μ = ν := by
  exact ext_of_moments μ ν hμ0 hν0
    (moment_eq μ ν hμ0 hν0 hmass (fun t ht => by simpa [isoNegStieltjes] using htr t ht))

/-! ## Moments and atoms -/

private theorem m_link0 : IsIsoLink (Muon.DetEquiv.rW (Muon.emaW 0)) := by
  obtain ⟨-, hd, -, h4⟩ := lem_app_iso_weights_i (β := 0) le_rfl zero_lt_one
  obtain ⟨hphi, hmono, -⟩ := h4 rfl
  refine ⟨fun q hq => (hd q hq).1.continuousWithinAt, fun a ha b hb hab => hmono ha hb hab, ?_⟩
  rw [hphi 0 le_rfl]
  simp [isoPhi]

private theorem m_rW0 {q : ℝ} (hq : 0 ≤ q) : Muon.DetEquiv.rW (Muon.emaW 0) q = isoPhi q :=
  ((lem_app_iso_weights_i (β := 0) le_rfl zero_lt_one).2.2.2 rfl).1 q hq

private theorem m_neg_pos (m : Measure ℝ) [IsFiniteMeasure m] (h0 : m (Iio 0) = 0)
    (hpos : (0:ENNReal) < m univ) (t : ℝ) (ht : 0 < t) :
    0 < ∫ x, (x + t)⁻¹ ∂m := by
  have hint := resolvent_integrable m h0 t ht
  rw [integral_pos_iff_support_of_nonneg_ae _ hint]
  · have h2 : m univ ≤ m (Ici 0) := by
      have := measure_union_le (μ := m) (Iio 0) (Ici 0)
      rw [Set.Iio_union_Ici, h0, zero_add] at this
      exact this
    refine lt_of_lt_of_le hpos (h2.trans (measure_mono ?_))
    intro x hx
    have hx' : (0:ℝ) ≤ x := hx
    simp only [Function.mem_support]
    exact inv_ne_zero (by linarith)
  · filter_upwards [ae_nonneg_of_Iio m h0] with x hx
    exact inv_nonneg.mpr (by linarith)


/-- lem:app-iso-moments, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.863–884):
```latex
\begin{lemma}[Moments and atoms]\label{lem:app-iso-moments}
Let $(\mathfrak m_{\mathrm{out}},\mathfrak m_{\mathrm{in}})$ be an isotropic measure pair at $(\gin,\gout)$.
\begin{enumerate}[label=(\roman*)]
\item The transforms are the branch: $\sigma(-t)$ and $\tilde\sigma(-t)$ in
\cref{eqn:app-iso-hypothesis} are those of \cref{prop:app-iso-closure} at
$\bmom=0$, and $\psi(t)=\int\frac{\lambda}{\lambda+t}\,\mathfrak m_{\mathrm{out}}(\dif\lambda)$.
\item The first moments are
\[
\int\lambda\,\mathfrak m_{\mathrm{out}}(\dif\lambda)=\int\lambda\,\mathfrak m_{\mathrm{in}}(\dif\lambda)=\gin\gout,
\qquad\text{and}\qquad \int\sqrt\lambda\,\mathfrak m_{\mathrm{out}}(\dif\lambda)\le\gout\sqrt{\gin}.
\]
\item $\mathfrak m_{\mathrm{in}}-\mathfrak m_{\mathrm{out}}=(\gin-\gout)\,\delta_0$.
\item If $\gin>1$ and $\gout>1$, then
$\mathfrak m_{\mathrm{out}}=(\gout-1)\delta_0+\eta$ and
$\mathfrak m_{\mathrm{in}}=(\gin-1)\delta_0+\eta$ for a probability measure $\eta$
on $(0,\infty)$.
\item For every finite nonnegative measure $\nu$ on $[0,\infty)$,
\begin{equation}\label{eqn:app-iso-half-moment}
\int\sqrt x\,\nu(\dif x)=\frac1\pi\int_0^\infty t^{-1/2}\int\frac{x}{x+t}\,\nu(\dif x)\,\dif t .
\end{equation}
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_moments_i {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) :
    ∀ t : ℝ, 0 < t →
      isoNegStieltjes mo t = (γout - psiIso 0 γin γout t) / t ∧
      isoNegStieltjes mi t = (γin - psiIso 0 γin γout t) / t ∧
      psiIso 0 γin γout t = ∫ l, l / (l + t) ∂mo := by
  intro t ht
  haveI : IsFiniteMeasure mo := ⟨by rw [hp.mass_out]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure mi := ⟨by rw [hp.mass_in]; exact ENNReal.ofReal_lt_top⟩
  have hid1 := (hp.identity t ht).1
  have hid2 := (hp.identity t ht).2
  have hSo : 0 < isoNegStieltjes mo t := m_neg_pos mo hp.supp_out
    (by rw [hp.mass_out]; exact ENNReal.ofReal_pos.mpr hp.pos_out) t ht
  have hSi : 0 < isoNegStieltjes mi t := m_neg_pos mi hp.supp_in
    (by rw [hp.mass_in]; exact ENNReal.ofReal_pos.mpr hp.pos_in) t ht
  have hto : 0 < t * isoNegStieltjes mo t := mul_pos ht hSo
  have hti : 0 < t * isoNegStieltjes mi t := mul_pos ht hSi
  have hqs0 : 0 ≤ t * isoNegStieltjes mo t * isoNegStieltjes mi t :=
    (mul_pos hto hSi).le
  have hrq : Muon.DetEquiv.rW (Muon.emaW 0) (t * isoNegStieltjes mo t * isoNegStieltjes mi t)
      = γout - t * isoNegStieltjes mo t := by
    rw [m_rW0 hqs0]
    exact hid2.symm
  have hlt : Muon.DetEquiv.rW (Muon.emaW 0) (t * isoNegStieltjes mo t * isoNegStieltjes mi t)
      < min γin γout := by
    rw [hrq]
    apply lt_min
    · linarith
    · linarith
  have hmem : t * isoNegStieltjes mo t * isoNegStieltjes mi t ∈
      isoDr (Muon.DetEquiv.rW (Muon.emaW 0)) γin γout := ⟨hqs0, hlt⟩
  have hG : isoG (Muon.DetEquiv.rW (Muon.emaW 0)) γin γout t
      (t * isoNegStieltjes mo t * isoNegStieltjes mi t) = 0 := by
    unfold isoG
    rw [hrq]
    have e : γin - (γout - t * isoNegStieltjes mo t) = t * isoNegStieltjes mi t := by
      linarith
    rw [e]
    ring
  obtain ⟨q0, -, hu⟩ := (lem_app_iso_comparison_i m_link0 hp.pos_in hp.pos_out).2.1 t ht
  have hex : ∃ q, q ∈ isoDr (Muon.DetEquiv.rW (Muon.emaW 0)) γin γout ∧
      isoG (Muon.DetEquiv.rW (Muon.emaW 0)) γin γout t q = 0 :=
    ⟨_, hmem, hG⟩
  have hroot : isoRoot (Muon.DetEquiv.rW (Muon.emaW 0)) γin γout t
      = t * isoNegStieltjes mo t * isoNegStieltjes mi t := by
    unfold isoRoot
    rw [dif_pos hex]
    exact (hu _ hex.choose_spec).trans (hu _ ⟨hmem, hG⟩).symm
  have hpsi : psiIso 0 γin γout t = γout - t * isoNegStieltjes mo t := by
    unfold psiIso qIso
    rw [hroot, hrq]
  refine ⟨?_, ?_, ?_⟩
  · rw [hpsi, eq_div_iff ht.ne']
    ring
  · rw [hpsi, eq_div_iff ht.ne']
    linear_combination hid1
  · rw [hpsi]
    have hint := resolvent_integrable mo hp.supp_out t ht
    have e : ∫ l, l / (l + t) ∂mo = ∫ l, (1 - t * (l + t)⁻¹) ∂mo := by
      refine integral_congr_ae ?_
      filter_upwards [ae_nonneg_of_Iio mo hp.supp_out] with l hl
      have h1 : l + t ≠ 0 := by intro h; linarith
      field_simp
      ring
    rw [e, integral_sub (integrable_const _) (hint.const_mul t), integral_const_mul]
    unfold isoNegStieltjes
    simp [Measure.real, hp.mass_out, ENNReal.toReal_ofReal hp.pos_out.le]

/-! ### Helpers for `lem:app-iso-moments` parts (ii) and (iv) (P-F.6.P3) -/

private theorem m_psi_identities {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) (t : ℝ) (ht : 0 < t) :
    ∫ l, l / (l + t) ∂mo = γout - t * isoNegStieltjes mo t ∧
    ∫ l, l / (l + t) ∂mo = isoPhi (t * isoNegStieltjes mo t * isoNegStieltjes mi t) ∧
    γin - t * isoNegStieltjes mi t = ∫ l, l / (l + t) ∂mo := by
  obtain ⟨h1, -, h3⟩ := lem_app_iso_moments_i hp t ht
  have hid := hp.identity t ht
  have e1 : ∫ l, l / (l + t) ∂mo = γout - t * isoNegStieltjes mo t := by
    rw [← h3, h1]
    field_simp
    ring
  exact ⟨e1, e1.trans hid.2, hid.1.symm.trans e1.symm⟩

private theorem m_q_facts {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) (t : ℝ) (ht : 0 < t) :
    ∫ l, l / (l + t) ∂mo = isoPhi (t * isoNegStieltjes mo t * isoNegStieltjes mi t) ∧
    0 < ∫ l, l / (l + t) ∂mo ∧ ∫ l, l / (l + t) ∂mo < 1 ∧
    ∫ l, l / (l + t) ∂mo ≤ (t * isoNegStieltjes mo t * isoNegStieltjes mi t) ∧
    (t * isoNegStieltjes mo t * isoNegStieltjes mi t) - ∫ l, l / (l + t) ∂mo ≤ 3 * ((t * isoNegStieltjes mo t * isoNegStieltjes mi t)) ^ 2 ∧
    t * ((t * isoNegStieltjes mo t * isoNegStieltjes mi t)) = (γout - ∫ l, l / (l + t) ∂mo) * (γin - ∫ l, l / (l + t) ∂mo) ∧
    0 < γout - ∫ l, l / (l + t) ∂mo ∧ 0 < γin - ∫ l, l / (l + t) ∂mo := by
  haveI : IsFiniteMeasure mo := ⟨by rw [hp.mass_out]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure mi := ⟨by rw [hp.mass_in]; exact ENNReal.ofReal_lt_top⟩
  have hSo : 0 < isoNegStieltjes mo t :=
    m_neg_pos mo hp.supp_out (by rw [hp.mass_out]; exact ENNReal.ofReal_pos.mpr hp.pos_out) t ht
  have hSi : 0 < isoNegStieltjes mi t :=
    m_neg_pos mi hp.supp_in (by rw [hp.mass_in]; exact ENNReal.ofReal_pos.mpr hp.pos_in) t ht
  obtain ⟨e1, e2, e3⟩ := m_psi_identities hp t ht
  have hq : 0 < (t * isoNegStieltjes mo t * isoNegStieltjes mi t) := mul_pos (mul_pos ht hSo) hSi
  obtain ⟨hphi0, hphi1⟩ := lem_app_iso_gaussian_ii.2.2 _ hq
  obtain ⟨h3a, h3b⟩ := lem_app_iso_gaussian_iii _ hq
  have hAp : 0 < t * isoNegStieltjes mo t := mul_pos ht hSo
  have hBp : 0 < t * isoNegStieltjes mi t := mul_pos ht hSi
  have hA : t * isoNegStieltjes mo t = γout - ∫ l, l / (l + t) ∂mo := by linarith
  have hB : t * isoNegStieltjes mi t = γin - ∫ l, l / (l + t) ∂mo := by linarith
  refine ⟨e2, by rw [e2]; exact hphi0, by rw [e2]; exact hphi1, by rw [e2]; linarith,
    by rw [e2]; linarith, ?_, by linarith, by linarith⟩
  rw [← hA, ← hB]
  ring

private theorem m_t_psi_tendsto_top {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) :
    Tendsto (fun t : ℝ => t * ∫ l, l / (l + t) ∂mo) atTop (𝓝 (γin * γout)) := by
  have hC : 0 < γin * γout := mul_pos hp.pos_in hp.pos_out
  have hle : ∀ t : ℝ, 0 < t → (∫ l, l / (l + t) ∂mo) * t ≤ γin * γout ∧ (t * isoNegStieltjes mo t * isoNegStieltjes mi t) * t ≤ γin * γout := by
    intro t ht
    obtain ⟨-, hpos, -, hψq, -, hD, -, hB⟩ := m_q_facts hp t ht
    have hprod : (γout - (∫ l, l / (l + t) ∂mo)) * (γin - (∫ l, l / (l + t) ∂mo)) ≤ γout * γin :=
      mul_le_mul (by linarith) (by linarith) hB.le hp.pos_out.le
    constructor
    · linarith [mul_le_mul_of_nonneg_right hψq ht.le]
    · linarith
  have hψ_inv : ∀ t : ℝ, 0 < t → (∫ l, l / (l + t) ∂mo) ≤ γin * γout * t⁻¹ := by
    intro t ht
    rw [← div_eq_mul_inv, le_div_iff₀ ht]
    exact (hle t ht).1
  have hq_inv : ∀ t : ℝ, 0 < t → (t * isoNegStieltjes mo t * isoNegStieltjes mi t) ≤ γin * γout * t⁻¹ := by
    intro t ht
    rw [← div_eq_mul_inv, le_div_iff₀ ht]
    exact (hle t ht).2
  have hinv0 : Tendsto (fun t : ℝ => γin * γout * t⁻¹) atTop (𝓝 0) := by
    have hT := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (γin * γout)
    rw [mul_zero] at hT
    exact hT
  have hψ0 : Tendsto (fun t : ℝ => (∫ l, l / (l + t) ∂mo)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hinv0
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      exact (m_q_facts hp t ht).2.1.le
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      exact hψ_inv t ht
  have hgT := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (3 * (γin * γout) * (γin * γout))
  rw [mul_zero] at hgT
  have hgap : Tendsto (fun t : ℝ => t * ((t * isoNegStieltjes mo t * isoNegStieltjes mi t) - (∫ l, l / (l + t) ∂mo))) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hgT
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      obtain ⟨-, hpos, -, hψq, -, -, -, -⟩ := m_q_facts hp t ht
      exact mul_nonneg ht.le (by linarith)
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      obtain ⟨-, hpos, -, hψq, hqψ, -, -, -⟩ := m_q_facts hp t ht
      have hq0 : 0 ≤ (t * isoNegStieltjes mo t * isoNegStieltjes mi t) := by linarith
      have hqt := (hle t ht).2
      have hqi := hq_inv t ht
      have hC3 : 0 ≤ 3 * (γin * γout) := (mul_pos (by norm_num) hC).le
      calc t * ((t * isoNegStieltjes mo t * isoNegStieltjes mi t) - (∫ l, l / (l + t) ∂mo)) ≤ t * (3 * ((t * isoNegStieltjes mo t * isoNegStieltjes mi t)) ^ 2) := mul_le_mul_of_nonneg_left hqψ ht.le
        _ = 3 * ((t * isoNegStieltjes mo t * isoNegStieltjes mi t) * t) * (t * isoNegStieltjes mo t * isoNegStieltjes mi t) := by ring
        _ ≤ 3 * (γin * γout) * (t * isoNegStieltjes mo t * isoNegStieltjes mi t) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqt (by norm_num)) hq0
        _ ≤ 3 * (γin * γout) * (γin * γout * t⁻¹) := mul_le_mul_of_nonneg_left hqi hC3
        _ = 3 * (γin * γout) * (γin * γout) * t⁻¹ := by ring
  have hprod : Tendsto (fun t : ℝ => (γout - (∫ l, l / (l + t) ∂mo)) * (γin - (∫ l, l / (l + t) ∂mo))) atTop
      (𝓝 ((γout - 0) * (γin - 0))) :=
    (tendsto_const_nhds.sub hψ0).mul (tendsto_const_nhds.sub hψ0)
  have htq : Tendsto (fun t : ℝ => t * (t * isoNegStieltjes mo t * isoNegStieltjes mi t)) atTop (𝓝 ((γout - 0) * (γin - 0))) :=
    hprod.congr' (by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      exact ((m_q_facts hp t ht).2.2.2.2.2.1).symm)
  have hfin := htq.sub hgap
  have hval : (γout - 0) * (γin - 0) - 0 = γin * γout := by ring
  rw [hval] at hfin
  exact hfin.congr (fun t => by ring)

private theorem m_lintegral_ofReal {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) :
    ∫⁻ x, ENNReal.ofReal x ∂mo = ENNReal.ofReal (γin * γout) := by
  haveI : IsFiniteMeasure mo := ⟨by rw [hp.mass_out]; exact ENNReal.ofReal_lt_top⟩
  have hnn := ae_nonneg_of_Iio mo hp.supp_out
  have hN : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hseq : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * ∫ l, l / (l + ((n : ℝ) + 1)) ∂mo) atTop
      (𝓝 (γin * γout)) := (m_t_psi_tendsto_top hp).comp hN
  have hnn_n : ∀ n : ℕ, 0 ≤ᵐ[mo] fun l : ℝ => ((n : ℝ) + 1) * (l / (l + ((n : ℝ) + 1))) := by
    intro n
    have ha : (0:ℝ) < (n : ℝ) + 1 := by positivity
    filter_upwards [hnn] with l hl
    exact mul_nonneg ha.le (div_nonneg hl (by linarith))
  have hint : ∀ n : ℕ,
      Integrable (fun l : ℝ => ((n : ℝ) + 1) * (l / (l + ((n : ℝ) + 1)))) mo := by
    intro n
    have ha : (0:ℝ) < (n : ℝ) + 1 := by positivity
    have hres := resolvent_integrable mo hp.supp_out ((n : ℝ) + 1) ha
    have hI : Integrable (fun l : ℝ => ((n : ℝ) + 1) - ((n : ℝ) + 1) * ((n : ℝ) + 1) *
        (l + ((n : ℝ) + 1))⁻¹) mo :=
      (integrable_const ((n : ℝ) + 1)).sub (hres.const_mul (((n : ℝ) + 1) * ((n : ℝ) + 1)))
    refine hI.congr ?_
    filter_upwards [hnn] with l hl
    have hla : l + ((n : ℝ) + 1) ≠ 0 := (by linarith : (0:ℝ) < l + ((n : ℝ) + 1)).ne'
    field_simp
    ring
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun l : ℝ => ENNReal.ofReal (((n : ℝ) + 1) * (l / (l + ((n : ℝ) + 1))))) mo :=
    fun n => (Measurable.ennreal_ofReal (by fun_prop)).aemeasurable
  have hmono : ∀ᵐ l ∂mo, Monotone fun n : ℕ =>
      ENNReal.ofReal (((n : ℝ) + 1) * (l / (l + ((n : ℝ) + 1)))) := by
    filter_upwards [hnn] with l hl
    intro n m hnm
    apply ENNReal.ofReal_le_ofReal
    have hab : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).2 hnm
      linarith
    have ha : (0:ℝ) < (n : ℝ) + 1 := by positivity
    have hb : (0:ℝ) < (m : ℝ) + 1 := by positivity
    rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.2 hab) (mul_nonneg hl hl)]
  have hlim : ∀ᵐ l ∂mo, Tendsto
      (fun n : ℕ => ENNReal.ofReal (((n : ℝ) + 1) * (l / (l + ((n : ℝ) + 1))))) atTop
      (𝓝 (ENNReal.ofReal l)) := by
    filter_upwards [hnn] with l hl
    apply ENNReal.tendsto_ofReal
    have hinv : Tendsto (fun n : ℕ => (l + ((n : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _ hN)
    have h2 : Tendsto (fun n : ℕ => l - l * l * (l + ((n : ℝ) + 1))⁻¹) atTop
        (𝓝 (l - l * l * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
    rw [mul_zero, sub_zero] at h2
    refine Tendsto.congr (fun n => ?_) h2
    have ha : (0:ℝ) < (n : ℝ) + 1 := by positivity
    have hla : l + ((n : ℝ) + 1) ≠ 0 := (by linarith : (0:ℝ) < l + ((n : ℝ) + 1)).ne'
    field_simp
    ring
  have hL := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hlim
  have hval : ∀ n : ℕ, ∫⁻ l, ENNReal.ofReal (((n : ℝ) + 1) * (l / (l + ((n : ℝ) + 1)))) ∂mo =
      ENNReal.ofReal (((n : ℝ) + 1) * ∫ l, l / (l + ((n : ℝ) + 1)) ∂mo) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (hnn_n n), integral_const_mul]
  simp only [hval] at hL
  exact tendsto_nhds_unique hL (ENNReal.tendsto_ofReal hseq)

private theorem m_moment_of (m : Measure ℝ) [IsFiniteMeasure m] (h0 : m (Iio 0) = 0) (c : ℝ)
    (hc : 0 ≤ c) (hL : ∫⁻ x, ENNReal.ofReal x ∂m = ENNReal.ofReal c) :
    Integrable (fun x : ℝ => x) m ∧ ∫ x, x ∂m = c := by
  have hnn := ae_nonneg_of_Iio m h0
  have hI : Integrable (fun x : ℝ => (ENNReal.ofReal x).toReal) m :=
    integrable_toReal_of_lintegral_ne_top measurable_id.ennreal_ofReal.aemeasurable
      (by rw [hL]; exact ENNReal.ofReal_ne_top)
  refine ⟨hI.congr (by filter_upwards [hnn] with x hx; exact ENNReal.toReal_ofReal hx), ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn measurable_id.aestronglyMeasurable, hL,
    ENNReal.toReal_ofReal hc]

private theorem m_decomp (m : Measure ℝ) (h0 : m (Iio 0) = 0) :
    m = m {0} • Measure.dirac (0:ℝ) + m.restrict (Ioi 0) := by
  have hsplit : m = m.restrict {0} + m.restrict ({0}ᶜ) :=
    (Measure.restrict_add_restrict_compl (μ := m) (measurableSet_singleton 0)).symm
  have hc : ({0}ᶜ : Set ℝ) = Iio 0 ∪ Ioi 0 := by
    ext x
    simp only [mem_compl_iff, mem_singleton_iff, mem_union, mem_Iio, mem_Ioi]
    constructor
    · intro hx
      rcases lt_trichotomy x 0 with h | h | h
      · exact Or.inl h
      · exact absurd h hx
      · exact Or.inr h
    · rintro (h | h) hx <;> rw [hx] at h <;> linarith
  have hsplit2 : m.restrict ({0}ᶜ) = m.restrict (Ioi 0) := by
    have hdisj : Disjoint (Iio (0:ℝ)) (Ioi (0:ℝ)) :=
      Set.disjoint_left.2 fun x (hx : x ∈ Iio (0:ℝ)) (hx' : x ∈ Ioi (0:ℝ)) =>
        lt_asymm (show x < 0 from hx) (show 0 < x from hx')
    rw [hc, Measure.restrict_union hdisj measurableSet_Ioi, Measure.restrict_eq_zero.2 h0,
      zero_add]
  rw [hsplit2, Measure.restrict_singleton] at hsplit
  exact hsplit

private theorem m_atom (m : Measure ℝ) [IsFiniteMeasure m] (h0 : m (Iio 0) = 0) (c : ℝ)
    (hc : m univ = ENNReal.ofReal c) (hpos : m (Ioi 0) = 1) (hc1 : 1 ≤ c) :
    m {0} = ENNReal.ofReal (c - 1) := by
  have h := congrArg (fun μ : Measure ℝ => μ univ) (m_decomp m h0)
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    measure_univ, Measure.dirac_apply_of_mem (mem_univ (0:ℝ)), mul_one] at h
  rw [hc, hpos] at h
  rw [ENNReal.eq_sub_of_add_eq ENNReal.one_ne_top h.symm, ENNReal.ofReal_sub c zero_le_one,
    ENNReal.ofReal_one]


private theorem m_moments_iii_copy {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) :
    mi + ENNReal.ofReal γout • Measure.dirac 0 = mo + ENNReal.ofReal γin • Measure.dirac 0 := by
  have hmi : IsFiniteMeasure mi := ⟨by rw [hp.mass_in]; exact ENNReal.ofReal_lt_top⟩
  have hmo : IsFiniteMeasure mo := ⟨by rw [hp.mass_out]; exact ENNReal.ofReal_lt_top⟩
  have hd0 : Measure.dirac (0:ℝ) (Iio 0) = 0 := by simp
  have hfin : ∀ (c : ℝ) (m : Measure ℝ) [IsFiniteMeasure m], IsFiniteMeasure (ENNReal.ofReal c • m) := by
    intro c m _
    exact ⟨by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  haveI : IsFiniteMeasure (ENNReal.ofReal γout • Measure.dirac (0:ℝ)) := hfin _ _
  haveI : IsFiniteMeasure (ENNReal.ofReal γin • Measure.dirac (0:ℝ)) := hfin _ _
  have hsupp1 : (mi + ENNReal.ofReal γout • Measure.dirac (0:ℝ) : Measure ℝ) (Iio 0) = 0 := by
    rw [Measure.add_apply, Measure.smul_apply, hp.supp_in, hd0]; simp
  have hsupp2 : (mo + ENNReal.ofReal γin • Measure.dirac (0:ℝ) : Measure ℝ) (Iio 0) = 0 := by
    rw [Measure.add_apply, Measure.smul_apply, hp.supp_out, hd0]; simp
  have hmass : (mi + ENNReal.ofReal γout • Measure.dirac (0:ℝ) : Measure ℝ) univ =
      (mo + ENNReal.ofReal γin • Measure.dirac (0:ℝ) : Measure ℝ) univ := by
    rw [Measure.add_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      hp.mass_in, hp.mass_out]
    simp [Measure.dirac_apply_of_mem, add_comm]
  refine lem_app_iso_transforms_ii inferInstance inferInstance hsupp1 hsupp2 hmass ?_
  intro t ht
  have ht0 : t ≠ 0 := ht.ne'
  have hi1 : Integrable (fun x : ℝ => (x + t)⁻¹) mi := resolvent_integrable mi hp.supp_in t ht
  have hi2 : Integrable (fun x : ℝ => (x + t)⁻¹) (ENNReal.ofReal γout • Measure.dirac (0:ℝ)) :=
    (resolvent_integrable (Measure.dirac 0) hd0 t ht).smul_measure ENNReal.ofReal_ne_top
  have hj1 : Integrable (fun x : ℝ => (x + t)⁻¹) mo := resolvent_integrable mo hp.supp_out t ht
  have hj2 : Integrable (fun x : ℝ => (x + t)⁻¹) (ENNReal.ofReal γin • Measure.dirac (0:ℝ)) :=
    (resolvent_integrable (Measure.dirac 0) hd0 t ht).smul_measure ENNReal.ofReal_ne_top
  have h := (hp.identity t ht).1
  simp only [isoNegStieltjes] at h ⊢
  rw [integral_add_measure hi1 hi2, integral_add_measure hj1 hj2, integral_smul_measure,
    integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal hp.pos_out.le, ENNReal.toReal_ofReal hp.pos_in.le]
  have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
  simp only [smul_eq_mul, zero_add]
  linear_combination t⁻¹ * h + (∫ x, (x + t)⁻¹ ∂mo - ∫ x, (x + t)⁻¹ ∂mi) * hinv


/-- lem:app-iso-moments, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.863–884):
```latex
\begin{lemma}[Moments and atoms]\label{lem:app-iso-moments}
Let $(\mathfrak m_{\mathrm{out}},\mathfrak m_{\mathrm{in}})$ be an isotropic measure pair at $(\gin,\gout)$.
\begin{enumerate}[label=(\roman*)]
\item The transforms are the branch: $\sigma(-t)$ and $\tilde\sigma(-t)$ in
\cref{eqn:app-iso-hypothesis} are those of \cref{prop:app-iso-closure} at
$\bmom=0$, and $\psi(t)=\int\frac{\lambda}{\lambda+t}\,\mathfrak m_{\mathrm{out}}(\dif\lambda)$.
\item The first moments are
\[
\int\lambda\,\mathfrak m_{\mathrm{out}}(\dif\lambda)=\int\lambda\,\mathfrak m_{\mathrm{in}}(\dif\lambda)=\gin\gout,
\qquad\text{and}\qquad \int\sqrt\lambda\,\mathfrak m_{\mathrm{out}}(\dif\lambda)\le\gout\sqrt{\gin}.
\]
\item $\mathfrak m_{\mathrm{in}}-\mathfrak m_{\mathrm{out}}=(\gin-\gout)\,\delta_0$.
\item If $\gin>1$ and $\gout>1$, then
$\mathfrak m_{\mathrm{out}}=(\gout-1)\delta_0+\eta$ and
$\mathfrak m_{\mathrm{in}}=(\gin-1)\delta_0+\eta$ for a probability measure $\eta$
on $(0,\infty)$.
\item For every finite nonnegative measure $\nu$ on $[0,\infty)$,
\begin{equation}\label{eqn:app-iso-half-moment}
\int\sqrt x\,\nu(\dif x)=\frac1\pi\int_0^\infty t^{-1/2}\int\frac{x}{x+t}\,\nu(\dif x)\,\dif t .
\end{equation}
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_moments_ii {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) :
    Integrable (fun x : ℝ => x) mo ∧ ∫ x, x ∂mo = γin * γout ∧
    Integrable (fun x : ℝ => x) mi ∧ ∫ x, x ∂mi = γin * γout ∧
    Integrable (fun x : ℝ => Real.sqrt x) mo ∧
      ∫ x, Real.sqrt x ∂mo ≤ γout * Real.sqrt γin := by
  haveI : IsFiniteMeasure mo := ⟨by rw [hp.mass_out]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure mi := ⟨by rw [hp.mass_in]; exact ENNReal.ofReal_lt_top⟩
  have hC : 0 ≤ γin * γout := (mul_pos hp.pos_in hp.pos_out).le
  have hLo := m_lintegral_ofReal hp
  have hR := congrArg (fun m : Measure ℝ => ∫⁻ x, ENNReal.ofReal x ∂m)
    (m_moments_iii_copy hp)
  simp only [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, ENNReal.ofReal_zero,
    smul_zero, add_zero] at hR
  have hLi : ∫⁻ x, ENNReal.ofReal x ∂mi = ENNReal.ofReal (γin * γout) := hR.trans hLo
  obtain ⟨hIo, hEo⟩ := m_moment_of mo hp.supp_out (γin * γout) hC hLo
  obtain ⟨hIi, hEi⟩ := m_moment_of mi hp.supp_in (γin * γout) hC hLi
  have hnnO := ae_nonneg_of_Iio mo hp.supp_out
  have hs : 0 < Real.sqrt γin := Real.sqrt_pos.2 hp.pos_in
  have hs2 : Real.sqrt γin * Real.sqrt γin = γin := Real.mul_self_sqrt hp.pos_in.le
  have hbd : ∀ x : ℝ, 0 ≤ x → Real.sqrt x ≤ (x + γin) / (2 * Real.sqrt γin) := by
    intro x hx
    rw [le_div_iff₀ (by linarith)]
    nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - Real.sqrt γin)]
  have hIbd : Integrable (fun x : ℝ => (x + γin) / (2 * Real.sqrt γin)) mo :=
    (hIo.add (integrable_const γin)).div_const (2 * Real.sqrt γin)
  have hsqI : Integrable (fun x : ℝ => Real.sqrt x) mo :=
    Integrable.mono' hIbd Real.continuous_sqrt.aestronglyMeasurable (by
      filter_upwards [hnnO] with x hx
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg x)]
      exact hbd x hx)
  have hcomp : ∫ x, (x + γin) / (2 * Real.sqrt γin) ∂mo = γout * Real.sqrt γin := by
    rw [integral_div, integral_add hIo (integrable_const _), integral_const, hEo]
    simp only [Measure.real, hp.mass_out, ENNReal.toReal_ofReal hp.pos_out.le, smul_eq_mul]
    rw [div_eq_iff (by linarith)]
    linear_combination (-2 * γout) * hs2
  have hle := integral_mono_ae hsqI hIbd
    (by filter_upwards [hnnO] with x hx; exact hbd x hx)
  exact ⟨hIo, hEo, hIi, hEi, hsqI, hle.trans hcomp.le⟩

/-- lem:app-iso-moments, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.863–884):
```latex
\begin{lemma}[Moments and atoms]\label{lem:app-iso-moments}
Let $(\mathfrak m_{\mathrm{out}},\mathfrak m_{\mathrm{in}})$ be an isotropic measure pair at $(\gin,\gout)$.
\begin{enumerate}[label=(\roman*)]
\item The transforms are the branch: $\sigma(-t)$ and $\tilde\sigma(-t)$ in
\cref{eqn:app-iso-hypothesis} are those of \cref{prop:app-iso-closure} at
$\bmom=0$, and $\psi(t)=\int\frac{\lambda}{\lambda+t}\,\mathfrak m_{\mathrm{out}}(\dif\lambda)$.
\item The first moments are
\[
\int\lambda\,\mathfrak m_{\mathrm{out}}(\dif\lambda)=\int\lambda\,\mathfrak m_{\mathrm{in}}(\dif\lambda)=\gin\gout,
\qquad\text{and}\qquad \int\sqrt\lambda\,\mathfrak m_{\mathrm{out}}(\dif\lambda)\le\gout\sqrt{\gin}.
\]
\item $\mathfrak m_{\mathrm{in}}-\mathfrak m_{\mathrm{out}}=(\gin-\gout)\,\delta_0$.
\item If $\gin>1$ and $\gout>1$, then
$\mathfrak m_{\mathrm{out}}=(\gout-1)\delta_0+\eta$ and
$\mathfrak m_{\mathrm{in}}=(\gin-1)\delta_0+\eta$ for a probability measure $\eta$
on $(0,\infty)$.
\item For every finite nonnegative measure $\nu$ on $[0,\infty)$,
\begin{equation}\label{eqn:app-iso-half-moment}
\int\sqrt x\,\nu(\dif x)=\frac1\pi\int_0^\infty t^{-1/2}\int\frac{x}{x+t}\,\nu(\dif x)\,\dif t .
\end{equation}
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_moments_iii {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) :
    mi + ENNReal.ofReal γout • Measure.dirac 0 = mo + ENNReal.ofReal γin • Measure.dirac 0 := by
  have hmi : IsFiniteMeasure mi := ⟨by rw [hp.mass_in]; exact ENNReal.ofReal_lt_top⟩
  have hmo : IsFiniteMeasure mo := ⟨by rw [hp.mass_out]; exact ENNReal.ofReal_lt_top⟩
  have hd0 : Measure.dirac (0:ℝ) (Iio 0) = 0 := by simp
  have hfin : ∀ (c : ℝ) (m : Measure ℝ) [IsFiniteMeasure m], IsFiniteMeasure (ENNReal.ofReal c • m) := by
    intro c m _
    exact ⟨by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  haveI : IsFiniteMeasure (ENNReal.ofReal γout • Measure.dirac (0:ℝ)) := hfin _ _
  haveI : IsFiniteMeasure (ENNReal.ofReal γin • Measure.dirac (0:ℝ)) := hfin _ _
  have hsupp1 : (mi + ENNReal.ofReal γout • Measure.dirac (0:ℝ) : Measure ℝ) (Iio 0) = 0 := by
    rw [Measure.add_apply, Measure.smul_apply, hp.supp_in, hd0]; simp
  have hsupp2 : (mo + ENNReal.ofReal γin • Measure.dirac (0:ℝ) : Measure ℝ) (Iio 0) = 0 := by
    rw [Measure.add_apply, Measure.smul_apply, hp.supp_out, hd0]; simp
  have hmass : (mi + ENNReal.ofReal γout • Measure.dirac (0:ℝ) : Measure ℝ) univ =
      (mo + ENNReal.ofReal γin • Measure.dirac (0:ℝ) : Measure ℝ) univ := by
    rw [Measure.add_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      hp.mass_in, hp.mass_out]
    simp [Measure.dirac_apply_of_mem, add_comm]
  refine lem_app_iso_transforms_ii inferInstance inferInstance hsupp1 hsupp2 hmass ?_
  intro t ht
  have ht0 : t ≠ 0 := ht.ne'
  have hi1 : Integrable (fun x : ℝ => (x + t)⁻¹) mi := resolvent_integrable mi hp.supp_in t ht
  have hi2 : Integrable (fun x : ℝ => (x + t)⁻¹) (ENNReal.ofReal γout • Measure.dirac (0:ℝ)) :=
    (resolvent_integrable (Measure.dirac 0) hd0 t ht).smul_measure ENNReal.ofReal_ne_top
  have hj1 : Integrable (fun x : ℝ => (x + t)⁻¹) mo := resolvent_integrable mo hp.supp_out t ht
  have hj2 : Integrable (fun x : ℝ => (x + t)⁻¹) (ENNReal.ofReal γin • Measure.dirac (0:ℝ)) :=
    (resolvent_integrable (Measure.dirac 0) hd0 t ht).smul_measure ENNReal.ofReal_ne_top
  have h := (hp.identity t ht).1
  simp only [isoNegStieltjes] at h ⊢
  rw [integral_add_measure hi1 hi2, integral_add_measure hj1 hj2, integral_smul_measure,
    integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal hp.pos_out.le, ENNReal.toReal_ofReal hp.pos_in.le]
  have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
  simp only [smul_eq_mul, zero_add]
  linear_combination t⁻¹ * h + (∫ x, (x + t)⁻¹ ∂mo - ∫ x, (x + t)⁻¹ ∂mi) * hinv

/-- lem:app-iso-moments, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.863–884):
```latex
\begin{lemma}[Moments and atoms]\label{lem:app-iso-moments}
Let $(\mathfrak m_{\mathrm{out}},\mathfrak m_{\mathrm{in}})$ be an isotropic measure pair at $(\gin,\gout)$.
\begin{enumerate}[label=(\roman*)]
\item The transforms are the branch: $\sigma(-t)$ and $\tilde\sigma(-t)$ in
\cref{eqn:app-iso-hypothesis} are those of \cref{prop:app-iso-closure} at
$\bmom=0$, and $\psi(t)=\int\frac{\lambda}{\lambda+t}\,\mathfrak m_{\mathrm{out}}(\dif\lambda)$.
\item The first moments are
\[
\int\lambda\,\mathfrak m_{\mathrm{out}}(\dif\lambda)=\int\lambda\,\mathfrak m_{\mathrm{in}}(\dif\lambda)=\gin\gout,
\qquad\text{and}\qquad \int\sqrt\lambda\,\mathfrak m_{\mathrm{out}}(\dif\lambda)\le\gout\sqrt{\gin}.
\]
\item $\mathfrak m_{\mathrm{in}}-\mathfrak m_{\mathrm{out}}=(\gin-\gout)\,\delta_0$.
\item If $\gin>1$ and $\gout>1$, then
$\mathfrak m_{\mathrm{out}}=(\gout-1)\delta_0+\eta$ and
$\mathfrak m_{\mathrm{in}}=(\gin-1)\delta_0+\eta$ for a probability measure $\eta$
on $(0,\infty)$.
\item For every finite nonnegative measure $\nu$ on $[0,\infty)$,
\begin{equation}\label{eqn:app-iso-half-moment}
\int\sqrt x\,\nu(\dif x)=\frac1\pi\int_0^\infty t^{-1/2}\int\frac{x}{x+t}\,\nu(\dif x)\,\dif t .
\end{equation}
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_moments_iv {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) (h1 : 1 < γin) (h2 : 1 < γout) :
    ∃ η : Measure ℝ, IsProbabilityMeasure η ∧ η (Iic 0) = 0 ∧
      mo = ENNReal.ofReal (γout - 1) • Measure.dirac 0 + η ∧
      mi = ENNReal.ofReal (γin - 1) • Measure.dirac 0 + η := by
  haveI : IsFiniteMeasure mo := ⟨by rw [hp.mass_out]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure mi := ⟨by rw [hp.mass_in]; exact ENNReal.ofReal_lt_top⟩
  have hnnO := ae_nonneg_of_Iio mo hp.supp_out
  have hcpos : 0 < (γout - 1) * (γin - 1) := mul_pos (by linarith) (by linarith)
  have hq_big : Tendsto (fun t : ℝ => t * isoNegStieltjes mo t * isoNegStieltjes mi t)
      (𝓝[>] 0) atTop := by
    refine tendsto_atTop_mono' _ ?_ (tendsto_inv_nhdsGT_zero.const_mul_atTop hcpos)
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    obtain ⟨-, -, hlt1, -, -, hD, hA, hB⟩ := m_q_facts hp t ht'
    have hmul : (γout - 1) * (γin - 1) ≤
        (γout - ∫ l, l / (l + t) ∂mo) * (γin - ∫ l, l / (l + t) ∂mo) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    rw [mul_inv_le_iff₀ ht']
    linarith
  have hψ1 : Tendsto (fun t : ℝ => ∫ l, l / (l + t) ∂mo) (𝓝[>] 0) (𝓝 1) := by
    have hphi := lem_app_iso_gaussian_iv.2.comp hq_big
    refine Tendsto.congr' ?_ hphi
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((m_q_facts hp t ht).1).symm
  have hlim2 : Tendsto (fun t : ℝ => ∫ l, l / (l + t) ∂mo) (𝓝[>] 0)
      (𝓝 (∫ l, (Ioi (0:ℝ)).indicator (1 : ℝ → ℝ) l ∂mo)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ)) ?_ ?_
      (integrable_const 1) ?_
    · exact Filter.Eventually.of_forall fun t => (by fun_prop : Measurable _).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with t ht
      filter_upwards [hnnO] with l hl
      have ht' : 0 < t := ht
      have hpos : 0 < l + t := by linarith
      show ‖l / (l + t)‖ ≤ 1
      rw [Real.norm_of_nonneg (div_nonneg hl hpos.le), div_le_one hpos]
      linarith
    · filter_upwards [hnnO] with l hl
      rcases hl.lt_or_eq with hl0 | hl0
      · rw [Set.indicator_of_mem (show l ∈ Ioi (0:ℝ) from hl0)]
        have hc : ContinuousAt (fun t : ℝ => l / (l + t)) 0 :=
          continuousAt_const.div (continuousAt_const.add continuousAt_id)
            (by simpa using hl0.ne')
        have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
        simpa [hl0.ne'] using h
      · rw [← hl0, Set.indicator_of_notMem (show (0:ℝ) ∉ Ioi (0:ℝ) by simp)]
        simp only [zero_div]
        exact tendsto_const_nhds
  have hmo1 : mo.real (Ioi 0) = 1 :=
    (integral_indicator_one (μ := mo) measurableSet_Ioi).symm.trans
      (tendsto_nhds_unique hlim2 hψ1)
  have hmo1' : mo (Ioi 0) = 1 := by
    rw [Measure.real] at hmo1
    exact (ENNReal.toReal_eq_one_iff _).1 hmo1
  have hR := congrArg (fun m : Measure ℝ => m.restrict (Ioi (0:ℝ))) (lem_app_iso_moments_iii hp)
  have hd : (Measure.dirac (0:ℝ)).restrict (Ioi (0:ℝ)) = 0 :=
    Measure.restrict_eq_zero.2 (by simp)
  simp only [Measure.restrict_add, Measure.restrict_smul, hd, smul_zero, add_zero] at hR
  have hmiR : mi.restrict (Ioi 0) = mo.restrict (Ioi 0) := hR
  have hmi1' : mi (Ioi 0) = 1 := by
    have h1 := congrArg (fun m : Measure ℝ => m univ) hmiR
    simp only [Measure.restrict_apply_univ] at h1
    rw [h1, hmo1']
  have hmo0 : mo {0} = ENNReal.ofReal (γout - 1) :=
    m_atom mo hp.supp_out γout hp.mass_out hmo1' (by linarith)
  have hmi0 : mi {0} = ENNReal.ofReal (γin - 1) :=
    m_atom mi hp.supp_in γin hp.mass_in hmi1' (by linarith)
  have hIic : mo.restrict (Ioi 0) (Iic 0) = 0 := by
    rw [Measure.restrict_apply measurableSet_Iic, Set.Iic_inter_Ioi, Set.Ioc_self, measure_empty]
  refine ⟨mo.restrict (Ioi 0), ⟨by rw [Measure.restrict_apply_univ]; exact hmo1'⟩, hIic,
    (m_decomp mo hp.supp_out).trans (by rw [hmo0]),
    (m_decomp mi hp.supp_in).trans (by rw [hmi0, hmiR])⟩

private lemma m_mom_pow (t : ℝ) (ht : 0 ≤ t) : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
  rw [Real.rpow_neg ht, Real.sqrt_eq_rpow]

private lemma m_mom_alg (s v : ℝ) (hs : 0 < s) (hv : 0 < v) :
    s ^ 2 * (2 * v) * ((s * v)⁻¹ * (s ^ 2 / (s ^ 2 + s ^ 2 * v ^ 2))) = 2 * s * (1 + v ^ 2)⁻¹ := by
  field_simp

private lemma m_mom_inner (x : ℝ) (hx : 0 ≤ x) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-(1 / 2 : ℝ)) * (x / (x + t))) =
      ENNReal.ofReal (Real.pi * Real.sqrt x) := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp
  · have himg : (fun v : ℝ => x * v ^ 2) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
      ext t
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact mul_pos hx' (pow_pos (show (0 : ℝ) < v from hv) 2)
      · intro ht
        refine ⟨Real.sqrt (t / x), Real.sqrt_pos.mpr (div_pos (show (0 : ℝ) < t from ht) hx'), ?_⟩
        show x * Real.sqrt (t / x) ^ 2 = t
        rw [Real.sq_sqrt (div_nonneg (le_of_lt (show (0 : ℝ) < t from ht)) hx'.le)]
        field_simp
    have hderiv : ∀ v ∈ Ioi (0 : ℝ),
        HasDerivWithinAt (fun v : ℝ => x * v ^ 2) (x * (2 * v)) (Ioi (0 : ℝ)) v := by
      intro v _
      exact ((hasDerivAt_pow 2 v).const_mul x).hasDerivWithinAt.congr_deriv (by norm_num)
    have hinj : InjOn (fun v : ℝ => x * v ^ 2) (Ioi (0 : ℝ)) := by
      intro a ha b hb h
      have h2 : a ^ 2 = b ^ 2 := mul_left_cancel₀ hx'.ne' h
      exact (pow_left_inj₀ (le_of_lt (show (0 : ℝ) < a from ha))
        (le_of_lt (show (0 : ℝ) < b from hb)) two_ne_zero).mp h2
    have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj
      (fun t : ℝ => ENNReal.ofReal (t ^ (-(1 / 2 : ℝ)) * (x / (x + t))))
    rw [himg] at key
    rw [key]
    have hpt : ∀ v ∈ Ioi (0 : ℝ),
        ENNReal.ofReal |x * (2 * v)| *
            ENNReal.ofReal ((x * v ^ 2) ^ (-(1 / 2 : ℝ)) * (x / (x + x * v ^ 2))) =
          ENNReal.ofReal (2 * Real.sqrt x) * ENNReal.ofReal ((1 + v ^ 2)⁻¹) := by
      intro v hv
      have hv' : (0 : ℝ) < v := hv
      have hxv : (0 : ℝ) ≤ x * (2 * v) := (mul_pos hx' (by linarith)).le
      rw [abs_of_nonneg hxv, m_mom_pow _ (mul_nonneg hx (sq_nonneg v)),
        Real.sqrt_mul hx, Real.sqrt_sq hv'.le,
        ← ENNReal.ofReal_mul hxv, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * Real.sqrt x by positivity)]
      congr 1
      have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx'
      have := m_mom_alg (Real.sqrt x) v hs hv'
      rw [Real.sq_sqrt hx] at this
      exact this
    refine (setLIntegral_congr_fun measurableSet_Ioi hpt).trans ?_
    have hfi : IntegrableOn (fun v : ℝ => (1 + v ^ 2)⁻¹) (Ioi (0 : ℝ)) :=
      integrable_inv_one_add_sq.integrableOn
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun v : ℝ => (1 + v ^ 2)⁻¹ :=
      Filter.Eventually.of_forall (fun v => inv_nonneg.mpr (by positivity))
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← ofReal_integral_eq_lintegral_ofReal hfi hnn,
      integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero,
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * Real.sqrt x by positivity)]
    congr 1
    ring

/-- lem:app-iso-moments, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.863–884):
```latex
\begin{lemma}[Moments and atoms]\label{lem:app-iso-moments}
Let $(\mathfrak m_{\mathrm{out}},\mathfrak m_{\mathrm{in}})$ be an isotropic measure pair at $(\gin,\gout)$.
\begin{enumerate}[label=(\roman*)]
\item The transforms are the branch: $\sigma(-t)$ and $\tilde\sigma(-t)$ in
\cref{eqn:app-iso-hypothesis} are those of \cref{prop:app-iso-closure} at
$\bmom=0$, and $\psi(t)=\int\frac{\lambda}{\lambda+t}\,\mathfrak m_{\mathrm{out}}(\dif\lambda)$.
\item The first moments are
\[
\int\lambda\,\mathfrak m_{\mathrm{out}}(\dif\lambda)=\int\lambda\,\mathfrak m_{\mathrm{in}}(\dif\lambda)=\gin\gout,
\qquad\text{and}\qquad \int\sqrt\lambda\,\mathfrak m_{\mathrm{out}}(\dif\lambda)\le\gout\sqrt{\gin}.
\]
\item $\mathfrak m_{\mathrm{in}}-\mathfrak m_{\mathrm{out}}=(\gin-\gout)\,\delta_0$.
\item If $\gin>1$ and $\gout>1$, then
$\mathfrak m_{\mathrm{out}}=(\gout-1)\delta_0+\eta$ and
$\mathfrak m_{\mathrm{in}}=(\gin-1)\delta_0+\eta$ for a probability measure $\eta$
on $(0,\infty)$.
\item For every finite nonnegative measure $\nu$ on $[0,\infty)$,
\begin{equation}\label{eqn:app-iso-half-moment}
\int\sqrt x\,\nu(\dif x)=\frac1\pi\int_0^\infty t^{-1/2}\int\frac{x}{x+t}\,\nu(\dif x)\,\dif t .
\end{equation}
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_iso_moments_v :
    ∀ ν : Measure ℝ, IsFiniteMeasure ν → ν (Iio 0) = 0 →
      (Integrable (fun x : ℝ => Real.sqrt x) ν ↔
        IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂ν) (Ioi (0 : ℝ))) ∧
      ∫ x, Real.sqrt x ∂ν =
        1 / Real.pi * ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂ν := by
  intro ν hν hν0
  have hae : ∀ᵐ x ∂ν, 0 ≤ x := ae_nonneg_of_Iio ν hν0
  have hsqnn : 0 ≤ᵐ[ν] fun x : ℝ => Real.sqrt x :=
    Filter.Eventually.of_forall (fun x => Real.sqrt_nonneg x)
  have hsqm : Measurable fun x : ℝ => Real.sqrt x := by fun_prop
  set L : ENNReal := ∫⁻ x, ENNReal.ofReal (Real.sqrt x) ∂ν with hL
  set J : ℝ → ENNReal := fun t => ∫⁻ x, ENNReal.ofReal (x / (x + t)) ∂ν with hJ
  have hJm : Measurable J := by
    have h := Measurable.lintegral_prod_right' (ν := ν)
      (f := fun p : ℝ × ℝ => ENNReal.ofReal (p.2 / (p.2 + p.1))) (by fun_prop)
    exact h
  have hJfin : ∀ t : ℝ, 0 < t → J t ≠ ⊤ := by
    intro t ht
    have hle : J t ≤ ν Set.univ := by
      calc J t ≤ ∫⁻ x, 1 ∂ν := by
            refine lintegral_mono_ae ?_
            filter_upwards [hae] with x hx
            exact ENNReal.ofReal_le_one.mpr ((div_le_one (by linarith)).mpr (by linarith))
        _ = ν Set.univ := by simp
    exact ne_top_of_le_ne_top (measure_ne_top ν Set.univ) hle
  have hbochner : ∀ t : ℝ, 0 < t → ∫ x, x / (x + t) ∂ν = (J t).toReal := by
    intro t ht
    have hnn : 0 ≤ᵐ[ν] fun x : ℝ => x / (x + t) :=
      hae.mono fun x hx => div_nonneg hx (by linarith)
    rw [integral_eq_lintegral_of_nonneg_ae hnn (by fun_prop : Measurable fun x : ℝ => x / (x + t)).aestronglyMeasurable]
  have hFM : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂ν) =
        ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) * J t := by
    intro t ht
    rw [hbochner t ht, ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
      ENNReal.ofReal_toReal (hJfin t ht)]
  have hA : ∫⁻ x, ENNReal.ofReal (Real.pi * Real.sqrt x) ∂ν = ENNReal.ofReal Real.pi * L := by
    simp_rw [ENNReal.ofReal_mul Real.pi_pos.le]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hswap_inner : ∀ t : ℝ, 0 < t →
      ∫⁻ x, ENNReal.ofReal (t ^ (-(1 / 2 : ℝ)) * (x / (x + t))) ∂ν =
        ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) * J t := by
    intro t ht
    have h0 : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
    simp_rw [ENNReal.ofReal_mul h0]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hT : ∫⁻ x, ENNReal.ofReal (Real.pi * Real.sqrt x) ∂ν =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) * J t := by
    have h1 : ∫⁻ x, ENNReal.ofReal (Real.pi * Real.sqrt x) ∂ν =
        ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-(1 / 2 : ℝ)) * (x / (x + t)))) ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with x hx
      exact (m_mom_inner x hx).symm
    have hmeas2 : Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (p.2 ^ (-(1 / 2 : ℝ)) * (p.1 / (p.1 + p.2)))) := by
      fun_prop
    rw [h1]
    refine (lintegral_lintegral_swap hmeas2.aemeasurable).trans ?_
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    exact hswap_inner t ht'
  have hE : ENNReal.ofReal Real.pi * L =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂ν) := by
    have hM : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂ν) =
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) * J t :=
      setLIntegral_congr_fun measurableSet_Ioi (fun t ht => hFM t ht)
    rw [hM, ← hA, hT]
  have hFnn : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂ν := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t (ht : (0 : ℝ) < t) => ?_)
    exact mul_nonneg (Real.rpow_nonneg ht.le _)
      (integral_nonneg_of_ae (hae.mono fun x hx => div_nonneg hx (by linarith)))
  have hFmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂ν)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hG : Measurable (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * (J t).toReal) :=
      (measurable_id.pow_const _).mul (ENNReal.measurable_toReal.comp hJm)
    refine hG.aestronglyMeasurable.congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall (fun t (ht : (0 : ℝ) < t) => ?_))
    show t ^ (-(1 / 2 : ℝ)) * (J t).toReal = t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂ν
    rw [hbochner t ht]
  have hBoch : ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂ν =
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂ν)).toReal :=
    integral_eq_lintegral_of_nonneg_ae hFnn hFmeas
  have hsqint : ∫ x, Real.sqrt x ∂ν = L.toReal :=
    integral_eq_lintegral_of_nonneg_ae hsqnn hsqm.aestronglyMeasurable
  have hLint : Integrable (fun x : ℝ => Real.sqrt x) ν ↔ L < ⊤ := by
    constructor
    · intro h
      exact (hasFiniteIntegral_iff_ofReal hsqnn).mp h.2
    · intro h
      exact ⟨hsqm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hsqnn).mpr h⟩
  have hFint : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂ν)
      (Ioi (0 : ℝ)) ↔
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂ν)) < ⊤ := by
    constructor
    · intro h
      exact (hasFiniteIntegral_iff_ofReal hFnn).mp h.2
    · intro h
      exact ⟨hFmeas, (hasFiniteIntegral_iff_ofReal hFnn).mpr h⟩
  have hpi0 : ENNReal.ofReal Real.pi ≠ 0 := (ENNReal.ofReal_pos.mpr Real.pi_pos).ne'
  have hLM : L < ⊤ ↔ ENNReal.ofReal Real.pi * L < ⊤ := by
    constructor
    · intro h
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h
    · intro h
      rcases ENNReal.mul_lt_top_iff.mp h with h' | h' | h'
      · exact h'.2
      · exact absurd h' hpi0
      · rw [h']
        exact ENNReal.zero_lt_top
  have hiff : Integrable (fun x : ℝ => Real.sqrt x) ν ↔
      IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂ν) (Ioi (0 : ℝ)) := by
    rw [hLint, hFint, ← hE]
    exact hLM
  refine ⟨hiff, ?_⟩
  rw [hsqint, hBoch, ← hE, ENNReal.toReal_mul, ENNReal.toReal_ofReal Real.pi_pos.le]
  field_simp

/-! ## The isotropic measure pair -/

/-- Square-pair characterization (`section.tex` l.798–806, card §6.14): at `γin = γout = γ`, a
finite measure `μ` of mass `γ` on `[0,∞)` satisfies the scalar measure hypothesis of
`def:app-phase-scalar` (`γ − tσ_μ(t) = Φ(tσ_μ(t)²)`, `t>0`) if and only if `(μ, μ)` is an
isotropic measure pair at `(γ, γ)`. Finiteness is implied by the mass clause. -/
theorem isoPair_square_iff {γ : ℝ} (hγ : 0 < γ) (μ : Measure ℝ) :
    (μ univ = ENNReal.ofReal γ ∧ μ (Iio 0) = 0 ∧
      ∀ t : ℝ, 0 < t → γ - t * isoNegStieltjes μ t = isoPhi (t * isoNegStieltjes μ t ^ 2)) ↔
      IsIsoMeasurePair γ γ μ μ := by
  constructor
  · rintro ⟨hm, hs, hid⟩
    refine ⟨hγ, hγ, hm, hm, hs, hs, fun t ht => ⟨rfl, ?_⟩⟩
    rw [hid t ht]
    congr 1
    ring
  · rintro ⟨_, _, hmo, _, hso, _, hid⟩
    refine ⟨hmo, hso, fun t ht => ?_⟩
    rw [(hid t ht).2]
    congr 1
    ring

/-- Square pairs have equal measures: at `γin = γout`, lem:app-iso-moments(iii) gives `𝔪_in = 𝔪_out`
(`section.tex` l.802–803). -/
theorem isoPair_square_eq {γ : ℝ} {mo mi : Measure ℝ} (hp : IsIsoMeasurePair γ γ mo mi) :
    mo = mi := by
  have h := lem_app_iso_moments_iii hp
  ext s hs
  have hs' := congrArg (fun m : Measure ℝ => m s) h
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' (0:ℝ) hs] at hs'
  have hne : ENNReal.ofReal γ * s.indicator 1 (0:ℝ) ≠ ⊤ := by
    by_cases h0 : (0:ℝ) ∈ s <;> simp [h0, ENNReal.ofReal_ne_top]
  rw [add_comm (mi s), add_comm (mo s)] at hs'
  exact ((ENNReal.add_right_inj hne).1 hs').symm

/-- prop:app-iso-measure, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.948–951):
```latex
\begin{proposition}[Existence of the isotropic measure pair]\label{prop:app-iso-measure}
For every $\gin>0$ and $\gout>0$ there is exactly one isotropic measure pair
$(\mathfrak m_{\mathrm{out}},\mathfrak m_{\mathrm{in}})$ at $(\gin,\gout)$.
\end{proposition}
```
Uniqueness part of `prop:app-iso-measure` (L-F.6 scope). Two isotropic measure pairs at the same
`(γin, γout)` have equal measures. Existence (and the ExistsUnique record declaration) is L-F.7
(`MeasureExistence.lean`), since it depends on B's T4 chain.
-/
theorem prop_app_iso_measure_unique {γin γout : ℝ} {mo mo' mi mi' : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) (hp' : IsIsoMeasurePair γin γout mo' mi') :
    mo = mo' ∧ mi = mi' := by
  haveI : IsFiniteMeasure mo := ⟨by rw [hp.mass_out]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure mi := ⟨by rw [hp.mass_in]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure mo' := ⟨by rw [hp'.mass_out]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure mi' := ⟨by rw [hp'.mass_in]; exact ENNReal.ofReal_lt_top⟩
  have htr := lem_app_iso_moments_i hp
  have htr' := lem_app_iso_moments_i hp'
  constructor
  · refine lem_app_iso_transforms_ii inferInstance inferInstance hp.supp_out hp'.supp_out ?_ ?_
    · rw [hp.mass_out, hp'.mass_out]
    · intro t ht
      rw [(htr t ht).1, (htr' t ht).1]
  · refine lem_app_iso_transforms_ii inferInstance inferInstance hp.supp_in hp'.supp_in ?_ ?_
    · rw [hp.mass_in, hp'.mass_in]
    · intro t ht
      rw [(htr t ht).2.1, (htr' t ht).2.1]

/-! ## Spectral form of the constant -/

/-! ### Helpers for `prop:app-iso-spectral` (P-F.6.P7) -/

private theorem m_hemaW0 (j : ℕ) : Muon.emaW 0 j = if j = 0 then 1 else 0 := by
  by_cases h : j = 0
  · subst h; simp [Muon.emaW]
  · simp [Muon.emaW, h, zero_pow h]

private theorem m_Lw0_eq_Fw0 (q : ℝ) :
    Muon.DetEquiv.Lw (Muon.emaW 0) q = Muon.DetEquiv.Fw (Muon.emaW 0) q := by
  simp only [Muon.DetEquiv.Lw, Muon.DetEquiv.Fw, m_hemaW0]
  congr 1
  funext j
  by_cases h : j = 0 <;> simp [h]

private theorem m_isoGb0 (γin γout t : ℝ) : isoGb 0 γin γout t = psiIso 0 γin γout t := by
  unfold isoGb psiIso Muon.DetEquiv.rW
  rw [m_Lw0_eq_Fw0]

private theorem m_psi_mi {γin γout : ℝ} {mo mi : Measure ℝ} (hp : IsIsoMeasurePair γin γout mo mi)
    (t : ℝ) (ht : 0 < t) :
    ∫ x, x / (x + t) ∂mi = psiIso 0 γin γout t := by
  haveI : IsFiniteMeasure mi := ⟨by rw [hp.mass_in]; exact ENNReal.ofReal_lt_top⟩
  obtain ⟨-, h2, -⟩ := lem_app_iso_moments_i hp t ht
  have hS : ∫ x, (x + t)⁻¹ ∂mi = (γin - psiIso 0 γin γout t) / t := h2
  have hae := ae_nonneg_of_Iio mi hp.supp_in
  have hint : Integrable (fun x : ℝ => (x + t)⁻¹) mi := resolvent_integrable mi hp.supp_in t ht
  have e1 : ∫ x, x / (x + t) ∂mi = ∫ x, (1 - t * (x + t)⁻¹) ∂mi := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    have hxt : x + t ≠ 0 := by linarith
    field_simp
    ring
  have hm : mi.real univ = γin := by
    rw [Measure.real, hp.mass_in, ENNReal.toReal_ofReal hp.pos_in.le]
  rw [e1, integral_sub (integrable_const _) (hint.const_mul t), integral_const,
    integral_const_mul, hS]
  simp only [smul_eq_mul, mul_one, hm]
  field_simp
  ring

private theorem m_spectral_key {γin γout : ℝ} (hγin : 0 < γin) (hγout : 0 < γout)
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hν0 : ν (Iio 0) = 0)
    (hψ : ∀ t : ℝ, 0 < t → ∫ x, x / (x + t) ∂ν = psiIso 0 γin γout t) :
    Cbeta 0 γin γout = 1 / (Real.sqrt 2 * γin * γout) * ∫ x, Real.sqrt x ∂ν := by
  have hC := (prop_app_iso_zero_i (β := 0) (γin := γin) (γout := γout) le_rfl zero_lt_one
    hγin hγout).2.2.2.2
  have hmo := (lem_app_iso_moments_v ν inferInstance hν0).2
  have hint : ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * isoGb 0 γin γout t
      = ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂ν := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [hψ t ht', m_isoGb0]
  have hmo' : ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * ∫ x, x / (x + t) ∂ν
      = Real.pi * ∫ x, Real.sqrt x ∂ν := by
    rw [hmo]
    field_simp
  rw [hC, hint, hmo']
  have h1 : Real.sqrt 2 ≠ 0 := by positivity
  have h2 : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- prop:app-iso-spectral, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.999–1017):
```latex
\begin{proposition}[Spectral form of the constant]\label{prop:app-iso-spectral}
Let $(\mathfrak m_{\mathrm{out}},\mathfrak m_{\mathrm{in}})$ be the isotropic measure
pair at $(\gin,\gout)$ of \cref{prop:app-iso-measure}. Then
\begin{equation}\label{eqn:app-iso-C-moment}
C(\gin,\gout)=\frac{1}{\sqrt2\,\gin\gout}\int\sqrt\lambda\,\mathfrak m_{\mathrm{out}}(\dif\lambda)
=\frac{1}{\sqrt2\,\gin\gout}\int\sqrt\lambda\,\mathfrak m_{\mathrm{in}}(\dif\lambda).
\end{equation}
For $b>0$ let $\widehat{\mathfrak m}_b$ be the image of $\mathfrak m_{\mathrm{out}}$ under
$\lambda\mapsto\lambda/b$, a measure of mass $\gout$ with transform
$S_{\widehat{\mathfrak m}_b}(-t)=b\,\sigma(-bt)$, and with density $b\rho(bx)$ when
$\mathfrak m_{\mathrm{out}}$ has density $\rho$. Then
\begin{equation}\label{eqn:app-iso-C-scale}
C(\gin,\gout)=\frac{\sqrt b}{\sqrt2\,\gin\gout}\int\sqrt x\,\widehat{\mathfrak m}_b(\dif x).
\end{equation}
In particular, at $b=\gin\gout$,
\[
C(\gin,\gout)=\frac{1}{\sqrt{2\gin\gout}}\int\sqrt x\,\widehat{\mathfrak m}_{\gin\gout}(\dif x).
\]
\end{proposition}
```
-/
theorem prop_app_iso_spectral_i {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) :
    Cbeta 0 γin γout = 1 / (Real.sqrt 2 * γin * γout) * ∫ l, Real.sqrt l ∂mo ∧
      Cbeta 0 γin γout = 1 / (Real.sqrt 2 * γin * γout) * ∫ l, Real.sqrt l ∂mi := by
  haveI : IsFiniteMeasure mo := ⟨by rw [hp.mass_out]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure mi := ⟨by rw [hp.mass_in]; exact ENNReal.ofReal_lt_top⟩
  exact ⟨m_spectral_key hp.pos_in hp.pos_out mo hp.supp_out
      (fun t ht => (lem_app_iso_moments_i hp t ht).2.2.symm),
    m_spectral_key hp.pos_in hp.pos_out mi hp.supp_in (fun t ht => m_psi_mi hp t ht)⟩

/-! ### Scaling and change-of-variables helpers (P-F.6.P7) -/

private theorem m_core_div {c : ℝ} (hc : 0 < c) (h : ℝ → ENNReal) (s : Set ℝ)
    (hs : MeasurableSet s) :
    ∫⁻ l in (fun l : ℝ => l / c) ⁻¹' s, h l = ENNReal.ofReal c * ∫⁻ x in s, h (c * x) := by
  have hP : MeasurableSet ((fun l : ℝ => l / c) ⁻¹' s) := hs.preimage (by fun_prop)
  have hL := lintegral_map_equiv (μ := volume)
    (((fun l : ℝ => l / c) ⁻¹' s).indicator h) (MeasurableEquiv.mulLeft₀ c hc.ne')
  have hmap : Measure.map (fun x : ℝ => c * x) volume = ENNReal.ofReal c⁻¹ • volume := by
    rw [Real.map_volume_mul_left hc.ne', abs_of_pos (inv_pos.2 hc)]
  have hL' : ∫⁻ y, ((fun l : ℝ => l / c) ⁻¹' s).indicator h y ∂(ENNReal.ofReal c⁻¹ • volume)
      = ∫⁻ x, ((fun l : ℝ => l / c) ⁻¹' s).indicator h (c * x) := by
    rw [← hmap]
    exact hL
  rw [lintegral_smul_measure, smul_eq_mul] at hL'
  have hGc : ∀ x : ℝ, ((fun l : ℝ => l / c) ⁻¹' s).indicator h (c * x)
      = s.indicator (fun x => h (c * x)) x := by
    intro x
    by_cases hx : x ∈ s
    · have hx' : c * x ∈ (fun l : ℝ => l / c) ⁻¹' s := by
        show c * x / c ∈ s
        rw [mul_div_cancel_left₀ x hc.ne']
        exact hx
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]
    · have hx' : c * x ∉ (fun l : ℝ => l / c) ⁻¹' s := by
        show ¬ (c * x / c ∈ s)
        rw [mul_div_cancel_left₀ x hc.ne']
        exact hx
      rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx]
  have hJ : ∫⁻ x, ((fun l : ℝ => l / c) ⁻¹' s).indicator h (c * x) = ∫⁻ x in s, h (c * x) := by
    simp only [hGc]
    exact lintegral_indicator hs _
  have hI : ∫⁻ l in (fun l : ℝ => l / c) ⁻¹' s, h l
      = ∫⁻ y, ((fun l : ℝ => l / c) ⁻¹' s).indicator h y := by
    rw [← lintegral_indicator hP]
  have hinv : ENNReal.ofReal c * ENNReal.ofReal c⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one]
  rw [hI, ← hJ, ← hL', ← mul_assoc, hinv, one_mul]

private theorem m_map_div_wd {c : ℝ} (hc : 0 < c) (h : ℝ → ENNReal) :
    Measure.map (fun l : ℝ => l / c) (volume.withDensity h) =
      volume.withDensity (fun x => ENNReal.ofReal c * h (c * x)) := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, withDensity_apply _ (hs.preimage (by fun_prop)),
    withDensity_apply _ hs, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact m_core_div hc h s hs

private theorem m_scaled_density {b : ℝ} (hb : 0 < b) (ρ : ℝ → ℝ) :
    isoScaledImage b (volume.withDensity (fun l => ENNReal.ofReal (ρ l))) =
      volume.withDensity (fun x => ENNReal.ofReal (b * ρ (b * x))) := by
  unfold isoScaledImage
  rw [m_map_div_wd hb]
  congr 1
  funext x
  simp only [ENNReal.ofReal_mul hb.le]

private theorem m_S_div {c : ℝ} (hc : 0 < c) (ν : Measure ℝ) (t : ℝ) :
    ∫ x, (x / c + t)⁻¹ ∂ν = c * ∫ x, (x + c * t)⁻¹ ∂ν := by
  have hc0 : c ≠ 0 := hc.ne'
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (x / c + t)⁻¹ = c * (x + c * t)⁻¹
  rw [show x / c + t = (x + c * t) / c by field_simp, inv_div, div_eq_mul_inv]

private theorem m_scaled_stieltjes (mo : Measure ℝ) {b : ℝ} (hb : 0 < b) (t : ℝ) :
    isoNegStieltjes (isoScaledImage b mo) t = b * isoNegStieltjes mo (b * t) := by
  unfold isoNegStieltjes isoScaledImage
  rw [integral_map (by fun_prop : Measurable fun l : ℝ => l / b).aemeasurable
    (by fun_prop : Measurable fun x : ℝ => (x + t)⁻¹).aestronglyMeasurable]
  exact m_S_div hb mo t

private theorem m_norm_eq_map {γin γout : ℝ} (hγin : 0 < γin) (hγout : 0 < γout)
    (mo : Measure ℝ) :
    isoNormMeasure γout mo =
      Measure.map (fun x : ℝ => γin * x) (ENNReal.ofReal γout⁻¹ • isoScaledImage (γin * γout) mo) := by
  have hγin0 : γin ≠ 0 := hγin.ne'
  have hγout0 : γout ≠ 0 := hγout.ne'
  unfold isoNormMeasure isoScaledImage
  rw [Measure.map_smul _ (by fun_prop : Measurable fun l : ℝ => l / γout).aemeasurable,
    Measure.map_smul _ (by fun_prop : Measurable fun x : ℝ => γin * x).aemeasurable,
    Measure.map_map (g := fun x : ℝ => γin * x) (f := fun l : ℝ => l / (γin * γout))
      (by fun_prop) (by fun_prop)]
  congr 1
  have hf : ((fun x : ℝ => γin * x) ∘ fun l : ℝ => l / (γin * γout)) = fun l : ℝ => l / γout := by
    funext l
    simp only [Function.comp]
    field_simp
  rw [hf]

/-- prop:app-iso-spectral, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.999–1017):
```latex
\begin{proposition}[Spectral form of the constant]\label{prop:app-iso-spectral}
Let $(\mathfrak m_{\mathrm{out}},\mathfrak m_{\mathrm{in}})$ be the isotropic measure
pair at $(\gin,\gout)$ of \cref{prop:app-iso-measure}. Then
\begin{equation}\label{eqn:app-iso-C-moment}
C(\gin,\gout)=\frac{1}{\sqrt2\,\gin\gout}\int\sqrt\lambda\,\mathfrak m_{\mathrm{out}}(\dif\lambda)
=\frac{1}{\sqrt2\,\gin\gout}\int\sqrt\lambda\,\mathfrak m_{\mathrm{in}}(\dif\lambda).
\end{equation}
For $b>0$ let $\widehat{\mathfrak m}_b$ be the image of $\mathfrak m_{\mathrm{out}}$ under
$\lambda\mapsto\lambda/b$, a measure of mass $\gout$ with transform
$S_{\widehat{\mathfrak m}_b}(-t)=b\,\sigma(-bt)$, and with density $b\rho(bx)$ when
$\mathfrak m_{\mathrm{out}}$ has density $\rho$. Then
\begin{equation}\label{eqn:app-iso-C-scale}
C(\gin,\gout)=\frac{\sqrt b}{\sqrt2\,\gin\gout}\int\sqrt x\,\widehat{\mathfrak m}_b(\dif x).
\end{equation}
In particular, at $b=\gin\gout$,
\[
C(\gin,\gout)=\frac{1}{\sqrt{2\gin\gout}}\int\sqrt x\,\widehat{\mathfrak m}_{\gin\gout}(\dif x).
\]
\end{proposition}
```
-/
theorem prop_app_iso_spectral_ii {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) :
    (∀ b : ℝ, 0 < b →
      isoScaledImage b mo univ = ENNReal.ofReal γout ∧
      (∀ t : ℝ, 0 < t →
        isoNegStieltjes (isoScaledImage b mo) t = b * isoNegStieltjes mo (b * t)) ∧
      (∀ ρ : ℝ → ℝ, mo = volume.withDensity (fun l => ENNReal.ofReal (ρ l)) →
        isoScaledImage b mo = volume.withDensity (fun x => ENNReal.ofReal (b * ρ (b * x)))) ∧
      Cbeta 0 γin γout =
        Real.sqrt b / (Real.sqrt 2 * γin * γout) * ∫ x, Real.sqrt x ∂(isoScaledImage b mo)) ∧
    Cbeta 0 γin γout =
      1 / Real.sqrt (2 * γin * γout) * ∫ x, Real.sqrt x ∂(isoScaledImage (γin * γout) mo) := by
  have hC1 := (prop_app_iso_spectral_i hp).1
  have hγ : 0 < γin * γout := mul_pos hp.pos_in hp.pos_out
  have hγin0 : γin ≠ 0 := hp.pos_in.ne'
  have hγout0 : γout ≠ 0 := hp.pos_out.ne'
  have hD : ∀ b : ℝ, 0 < b → Cbeta 0 γin γout =
      Real.sqrt b / (Real.sqrt 2 * γin * γout) * ∫ x, Real.sqrt x ∂(isoScaledImage b mo) := by
    intro b hb
    unfold isoScaledImage
    rw [integral_map (by fun_prop : Measurable fun l : ℝ => l / b).aemeasurable
      Real.continuous_sqrt.measurable.aestronglyMeasurable]
    have hsq : ∀ l : ℝ, Real.sqrt (l / b) = Real.sqrt l / Real.sqrt b :=
      fun l => Real.sqrt_div' l hb.le
    simp only [hsq, integral_div]
    rw [hC1]
    have hsb : Real.sqrt b ≠ 0 := (Real.sqrt_pos.2 hb).ne'
    have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 two_pos).ne'
    field_simp
  refine ⟨fun b hb => ⟨?_, fun t _ => m_scaled_stieltjes mo hb t, ?_, hD b hb⟩, ?_⟩
  · unfold isoScaledImage
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ, hp.mass_out]
  · intro ρ hρ
    rw [hρ]
    exact m_scaled_density hb ρ
  · rw [hD (γin * γout) hγ]
    congr 1
    rw [show 2 * γin * γout = 2 * (γin * γout) by ring, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    have hs2 : 0 < Real.sqrt (γin * γout) := Real.sqrt_pos.2 hγ
    have hsq := Real.mul_self_sqrt hγ.le
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
    rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero h2.ne' hγin0) hγout0)
      (mul_ne_zero h2.ne' hs2.ne')]
    linear_combination (Real.sqrt 2) * hsq

/-! ## Reciprocity, part (i) -/

/-- prop:app-iso-reciprocity, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1589–1608):
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
-/
theorem prop_app_iso_reciprocity_i {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) :
    isoNormMeasure γout mo =
        Measure.map (fun x : ℝ => γin * x)
          (ENNReal.ofReal γout⁻¹ • isoScaledImage (γin * γout) mo) ∧
    (∀ ρ : ℝ → ℝ, isoScaledImage (γin * γout) mo = volume.withDensity (fun x => ENNReal.ofReal (ρ x)) →
      isoNormMeasure γout mo =
        volume.withDensity (fun y => ENNReal.ofReal (ρ (y / γin) / (γin * γout)))) ∧
    (∀ t : ℝ, 0 < t →
      isoNegStieltjes (isoNormMeasure γout mo) t = isoNegStieltjes mo (γout * t) ∧
      isoNegStieltjes (isoNormMeasure γout mo) t =
        1 / (γin * γout) * isoNegStieltjes (isoScaledImage (γin * γout) mo) (t / γin)) ∧
    Cbeta 0 γin γout =
      Real.sqrt γout / (Real.sqrt 2 * γin) * ∫ x, Real.sqrt x ∂(isoNormMeasure γout mo) := by
  have hC1 := (prop_app_iso_spectral_i hp).1
  have hγ : 0 < γin * γout := mul_pos hp.pos_in hp.pos_out
  have hγin0 : γin ≠ 0 := hp.pos_in.ne'
  have hγout0 : γout ≠ 0 := hp.pos_out.ne'
  have hn := m_norm_eq_map hp.pos_in hp.pos_out mo
  refine ⟨hn, ?_, ?_, ?_⟩
  · intro ρ hρ
    rw [hn, hρ, Measure.map_smul _ (by fun_prop : Measurable fun x : ℝ => γin * x).aemeasurable]
    ext s hs
    rw [Measure.smul_apply, Measure.map_apply (by fun_prop) hs,
      withDensity_apply _ (hs.preimage (by fun_prop)), withDensity_apply _ hs, smul_eq_mul]
    have hset : ((fun x : ℝ => γin * x) ⁻¹' s) = ((fun l : ℝ => l / γin⁻¹) ⁻¹' s) := by
      congr 1
      funext x
      show γin * x = x / γin⁻¹
      rw [div_inv_eq_mul, mul_comm]
    rw [hset]
    have hcore := m_core_div (c := γin⁻¹) (inv_pos.2 hp.pos_in)
      (fun x => ENNReal.ofReal (ρ x)) s hs
    beta_reduce at hcore
    rw [hcore]
    simp only [inv_mul_eq_div]
    have hpt : ∀ y : ℝ, ENNReal.ofReal (ρ (y / γin) / (γin * γout)) =
        ENNReal.ofReal γout⁻¹ * (ENNReal.ofReal γin⁻¹ * ENNReal.ofReal (ρ (y / γin))) := by
      intro y
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hp.pos_in.le),
        ← ENNReal.ofReal_mul (inv_nonneg.2 hp.pos_out.le)]
      congr 1
      ring
    have hint : ∫⁻ y in s, ENNReal.ofReal (ρ (y / γin) / (γin * γout)) =
        ∫⁻ y in s, ENNReal.ofReal γout⁻¹ * (ENNReal.ofReal γin⁻¹ * ENNReal.ofReal (ρ (y / γin))) :=
      lintegral_congr (fun y => hpt y)
    rw [hint, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  · intro t ht
    have ha : isoNegStieltjes (isoNormMeasure γout mo) t = isoNegStieltjes mo (γout * t) := by
      unfold isoNegStieltjes isoNormMeasure
      rw [integral_map (by fun_prop : Measurable fun l : ℝ => l / γout).aemeasurable
        (by fun_prop : Measurable fun x : ℝ => (x + t)⁻¹).aestronglyMeasurable,
        integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hp.pos_out.le), smul_eq_mul]
      rw [m_S_div hp.pos_out mo t, ← mul_assoc, inv_mul_cancel₀ hγout0, one_mul]
    refine ⟨ha, ?_⟩
    rw [ha, m_scaled_stieltjes mo hγ (t / γin)]
    have e : γin * γout * (t / γin) = γout * t := by field_simp
    rw [e, ← mul_assoc, one_div_mul_cancel hγ.ne', one_mul]
  · have hsq : ∀ l : ℝ, Real.sqrt (l / γout) = Real.sqrt l / Real.sqrt γout :=
      fun l => Real.sqrt_div' l hp.pos_out.le
    unfold isoNormMeasure
    rw [integral_map (by fun_prop : Measurable fun l : ℝ => l / γout).aemeasurable
      Real.continuous_sqrt.measurable.aestronglyMeasurable, integral_smul_measure,
      ENNReal.toReal_ofReal (inv_nonneg.2 hp.pos_out.le), smul_eq_mul]
    simp only [hsq, integral_div]
    rw [hC1]
    have hsg : Real.sqrt γout ≠ 0 := (Real.sqrt_pos.2 hp.pos_out).ne'
    have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 two_pos).ne'
    field_simp

/-! ## Small aspect ratios -/

private theorem m_norm_neg {γ : ℝ} (hγ : 0 < γ) (mo : Measure ℝ) (t : ℝ) :
    isoNegStieltjes (isoNormMeasure γ mo) t = isoNegStieltjes mo (γ * t) := by
  unfold isoNegStieltjes isoNormMeasure
  rw [integral_map (by fun_prop : Measurable fun l : ℝ => l / γ).aemeasurable
    (by fun_prop : Measurable fun x : ℝ => (x + t)⁻¹).aestronglyMeasurable,
    integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hγ.le), smul_eq_mul]
  rw [inv_mul_eq_iff_eq_mul₀ hγ.ne']
  exact m_S_div hγ mo t

private theorem m_negS_bounds {ν : Measure ℝ} [IsFiniteMeasure ν] (h0 : ν (Iio 0) = 0)
    {s : ℝ} (hs : 0 < s) :
    0 ≤ isoNegStieltjes ν s ∧ isoNegStieltjes ν s ≤ (ν univ).toReal / s := by
  constructor
  · unfold isoNegStieltjes
    apply integral_nonneg_of_ae
    filter_upwards [ae_nonneg_of_Iio ν h0] with x hx
    exact inv_nonneg.2 (by linarith)
  · unfold isoNegStieltjes
    have hae : (fun x : ℝ => (x + s)⁻¹) ≤ᵐ[ν] (fun _ : ℝ => s⁻¹) := by
      filter_upwards [ae_nonneg_of_Iio ν h0] with x hx
      exact inv_anti₀ hs (by linarith)
    have h := integral_mono_ae (resolvent_integrable ν h0 s hs) (integrable_const s⁻¹) hae
    have hc : ∫ _x : ℝ, s⁻¹ ∂ν = (ν univ).toReal * s⁻¹ := by
      rw [integral_const, smul_eq_mul]; rfl
    rw [hc] at h
    rw [div_eq_mul_inv]
    exact h

private theorem m_small_phi {v : ℝ} (hv : 0 ≤ v) : 0 ≤ v - isoPhi v ∧ v - isoPhi v ≤ 3 * v ^ 2 := by
  rcases hv.eq_or_lt with h | h
  · subst h; simp [isoPhi]
  · exact lem_app_iso_gaussian_iii v h

private theorem m_norm_prob {γ : ℝ} (hγ : 0 < γ) {mo : Measure ℝ}
    (hmass : mo univ = ENNReal.ofReal γ) : IsProbabilityMeasure (isoNormMeasure γ mo) := by
  refine ⟨?_⟩
  unfold isoNormMeasure
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ, Measure.smul_apply,
    smul_eq_mul, hmass, ← ENNReal.ofReal_mul (inv_nonneg.2 hγ.le), inv_mul_cancel₀ hγ.ne',
    ENNReal.ofReal_one]

private theorem m_norm_supp {γ : ℝ} (hγ : 0 < γ) {mo : Measure ℝ} (h0 : mo (Iio 0) = 0) :
    isoNormMeasure γ mo (Iio 0) = 0 := by
  have hpre : (fun l : ℝ => l / γ) ⁻¹' Iio 0 = Iio 0 := by
    ext l
    simp [div_lt_iff₀ hγ]
  unfold isoNormMeasure
  rw [Measure.map_apply (by fun_prop) measurableSet_Iio, hpre, Measure.smul_apply, h0, smul_zero]

private theorem m_isoMP_supp {r : ℝ} (hr : 0 < r) : isoMP r (Iio 0) = 0 := by
  have ha : 0 ≤ isoMPa r := by
    unfold isoMPa
    exact div_nonneg (sq_nonneg _) hr.le
  have h1 : Measure.dirac (0 : ℝ) (Iio 0) = 0 := by simp
  have h2 : (volume.restrict (Ioo (isoMPa r) (isoMPb r))).withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * x)))
      (Iio 0) = 0 := by
    rw [withDensity_apply _ measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
    have he : Iio (0 : ℝ) ∩ Ioo (isoMPa r) (isoMPb r) = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iio, mem_Ioo, mem_empty_iff_false, iff_false]
      rintro ⟨h1', h2'⟩
      linarith [h2'.1]
    rw [he, Measure.restrict_empty, lintegral_zero_measure]
  unfold isoMP
  rw [Measure.add_apply, Measure.smul_apply, h1, h2, smul_zero, add_zero]

private theorem m_norm_mean {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) :
    Integrable (fun x : ℝ => x) (isoNormMeasure γout mo) ∧
      ∫ x, x ∂(isoNormMeasure γout mo) = γin / γout := by
  obtain ⟨hI, hM, -⟩ := lem_app_iso_moments_ii hp
  have hγ : 0 < γout := hp.pos_out
  constructor
  · unfold isoNormMeasure
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    exact (hI.div_const γout).smul_measure ENNReal.ofReal_ne_top
  · unfold isoNormMeasure
    rw [integral_map (by fun_prop : Measurable fun l : ℝ => l / γout).aemeasurable
      (by fun_prop : Measurable fun x : ℝ => x).aestronglyMeasurable,
      integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hγ.le), smul_eq_mul,
      integral_div, hM]
    field_simp

/-- thm:app-iso-small, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1508–1531):
```latex
\begin{theorem}[Small aspect ratios]\label{thm:app-iso-small}
Let $\gin^{(j)},\gout^{(j)}\to0$ with $r_j\defeq\gout^{(j)}/\gin^{(j)}\to r\in(0,\infty)$,
and let $(\mathfrak m_{\mathrm{out}}^{(j)},\mathfrak m_{\mathrm{in}}^{(j)})$ be the isotropic
measure pair at $(\gin^{(j)},\gout^{(j)})$ of \cref{prop:app-iso-measure}.
Let $\mathsf P_j$ be the image of the probability measure
$\mathfrak m_{\mathrm{out}}^{(j)}/\gout^{(j)}$ under $\lambda\mapsto\lambda/\gout^{(j)}$,
and write $\mathsf m_j(t)\defeq S_{\mathsf P_j}(-t)$.
\begin{enumerate}[label=(\roman*)]
\item For every $t>0$,
\begin{equation}\label{eqn:app-iso-small-residual}
\Big|t\,\mathsf m_j(t)^2+\Big(t+\frac1{r_j}-1\Big)\mathsf m_j(t)-1\Big|\le\frac{3\gout^{(j)}}{r_j^2t^2}.
\end{equation}
\item $\mathsf P_j\to\mathsf M_r$ weakly, and $\int\sqrt x\,\mathsf P_j(\dif x)\to J_r\defeq\int\sqrt x\,\mathsf M_r(\dif x)>0$.
\item The constant satisfies
\begin{equation}\label{eqn:app-iso-small}
\begin{gathered}
C\big(\gin^{(j)},\gout^{(j)}\big)=\frac{r_j}{\sqrt{2\gout^{(j)}}}\int\sqrt x\,\mathsf P_j(\dif x)
\sim\frac{r}{\sqrt{2\gout^{(j)}}}\,J_r,\\
J_r=\int_{a_r}^{b_r}\frac{\sqrt{(b_r-x)(x-a_r)}}{2\pi\sqrt x}\,\dif x .
\end{gathered}
\end{equation}
In particular $J_1=8/(3\pi)$, and $C(\gamma)\sim8/(3\pi\sqrt{2\gamma})$ as $\gamma\downarrow0$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_iso_small_i (gin gout : ℕ → ℝ) (mo mi : ℕ → Measure ℝ) (r : ℝ)
    (hp : ∀ j, IsIsoMeasurePair (gin j) (gout j) (mo j) (mi j))
    (hr : 0 < r)
    (hin : Tendsto gin atTop (𝓝 0)) (hout : Tendsto gout atTop (𝓝 0))
    (hratio : Tendsto (fun j => gout j / gin j) atTop (𝓝 r)) :
    ∀ j : ℕ, ∀ t : ℝ, 0 < t →
      |t * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t ^ 2 +
          (t + gin j / gout j - 1) * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t - 1| ≤
        3 * gout j / ((gout j / gin j) ^ 2 * t ^ 2) := by
  intro j t ht
  have hp' := hp j
  have hγ : 0 < gout j := hp'.pos_out
  have hγi : 0 < gin j := hp'.pos_in
  haveI : IsFiniteMeasure (mo j) := ⟨by rw [hp'.mass_out]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure (mi j) := ⟨by rw [hp'.mass_in]; exact ENNReal.ofReal_lt_top⟩
  have hs : 0 < gout j * t := mul_pos hγ ht
  rw [m_norm_neg hγ (mo j) t]
  obtain ⟨hS0, hSle⟩ := m_negS_bounds hp'.supp_out hs
  obtain ⟨hT0, hTle⟩ := m_negS_bounds hp'.supp_in hs
  rw [hp'.mass_out, ENNReal.toReal_ofReal hγ.le] at hSle
  rw [hp'.mass_in, ENNReal.toReal_ofReal hγi.le] at hTle
  obtain ⟨hid1, hid2⟩ := hp'.identity (gout j * t) hs
  set S := isoNegStieltjes (mo j) (gout j * t) with hSdef
  set T := isoNegStieltjes (mi j) (gout j * t) with hTdef
  have hv0 : 0 ≤ gout j * t * S * T := mul_nonneg (mul_nonneg hs.le hS0) hT0
  have hS1 : S ≤ 1 / t := by
    have e : gout j / (gout j * t) = 1 / t := by field_simp
    calc S ≤ gout j / (gout j * t) := hSle
    _ = 1 / t := e
  have hvle : gout j * t * S * T ≤ gin j / t := by
    have hST : S * T ≤ (1 / t) * (gin j / (gout j * t)) :=
      mul_le_mul hS1 hTle hT0 (one_div_pos.2 ht).le
    calc gout j * t * S * T = (gout j * t) * (S * T) := by ring
    _ ≤ (gout j * t) * ((1 / t) * (gin j / (gout j * t))) :=
        mul_le_mul_of_nonneg_left hST hs.le
    _ = gin j / t := by field_simp
  have hE := m_small_phi hv0
  have hq : gout j * (gin j / gout j) = gin j := mul_div_cancel₀ _ hγ.ne'
  have hR : gout j * (t * S ^ 2 + (t + gin j / gout j - 1) * S - 1) =
      gout j * t * S * T - isoPhi (gout j * t * S * T) := by
    linear_combination (-1 : ℝ) * hid2 + (-S) * hid1 + S * hq
  have hRnn : 0 ≤ t * S ^ 2 + (t + gin j / gout j - 1) * S - 1 := by
    have h0 : 0 ≤ gout j * (t * S ^ 2 + (t + gin j / gout j - 1) * S - 1) := by
      rw [hR]; linarith [hE.1]
    exact (mul_nonneg_iff_of_pos_left hγ).1 h0
  rw [abs_of_nonneg hRnn]
  have hv2 : (gout j * t * S * T) ^ 2 ≤ (gin j / t) ^ 2 := pow_le_pow_left₀ hv0 hvle 2
  have hB : 3 * gout j / ((gout j / gin j) ^ 2 * t ^ 2) = 3 * (gin j / t) ^ 2 / gout j := by
    field_simp
  rw [hB, le_div_iff₀ hγ]
  nlinarith [hR, hE.2, hv2]

private theorem m_isoJr_pos {r : ℝ} (hr : 0 < r) : 0 < isoJr r := by
  obtain ⟨hP, hInt, -, -⟩ := lem_app_iso_mp hr
  have hsupp := m_isoMP_supp hr
  have ha : 0 ≤ isoMPa r := by
    unfold isoMPa
    exact div_nonneg (sq_nonneg _) hr.le
  have hab : isoMPa r < isoMPb r := by
    unfold isoMPa isoMPb
    have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
    apply div_lt_div_of_pos_right _ hr
    nlinarith
  have hFpos : ∀ x ∈ Ioo (isoMPa r) (isoMPb r),
      ENNReal.ofReal (Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * x)) ≠ 0 := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    refine (ENNReal.ofReal_pos.2 (div_pos (Real.sqrt_pos.2 (mul_pos ?_ ?_)) ?_)).ne'
    · linarith [hx.2]
    · linarith [hx.1]
    · exact mul_pos (mul_pos two_pos Real.pi_pos) hx0
  have hF : Measurable (fun x : ℝ =>
      ENNReal.ofReal (Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * x))) := by
    fun_prop
  have hρ : 0 < (volume.restrict (Ioo (isoMPa r) (isoMPb r))).withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) /
        (2 * Real.pi * x))) (Ioo (isoMPa r) (isoMPb r)) := by
    rw [withDensity_apply _ measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_self, setLIntegral_pos_iff hF]
    have hsub2 : Ioo (isoMPa r) (isoMPb r) ⊆
        Function.support (fun x : ℝ =>
          ENNReal.ofReal (Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * x))) ∩
          Ioo (isoMPa r) (isoMPb r) :=
      fun x hx => ⟨Function.mem_support.2 (hFpos x hx), hx⟩
    refine lt_of_lt_of_le ?_ (measure_mono hsub2)
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.2 (sub_pos.2 hab)
  have hsubset : Ioo (isoMPa r) (isoMPb r) ⊆ Function.support (fun x : ℝ => Real.sqrt x) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    exact Function.mem_support.2 (Real.sqrt_pos.2 hx0).ne'
  have hM : 0 < isoMP r (Function.support (fun x : ℝ => Real.sqrt x)) := by
    unfold isoMP
    rw [Measure.add_apply]
    exact lt_of_lt_of_le hρ (le_add_left (measure_mono hsubset))
  have hint : Integrable (fun x : ℝ => Real.sqrt x) (isoMP r) := by
    refine Integrable.mono' (g := fun x : ℝ => 1 + x) ((integrable_const (1 : ℝ)).add hInt)
      (Real.continuous_sqrt.measurable).aestronglyMeasurable ?_
    filter_upwards [ae_nonneg_of_Iio (isoMP r) hsupp] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x)]
    nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - 1 / 2)]
  unfold isoJr
  exact (integral_pos_iff_support_of_nonneg (fun x => Real.sqrt_nonneg x) hint).2 hM

private theorem m_transform_conv {r : ℝ} (hr : 0 < r) {gin gout : ℕ → ℝ}
    {mo mi : ℕ → Measure ℝ} (hp : ∀ j, IsIsoMeasurePair (gin j) (gout j) (mo j) (mi j))
    (hin : Tendsto gin atTop (𝓝 0)) (hout : Tendsto gout atTop (𝓝 0))
    (hratio : Tendsto (fun j => gout j / gin j) atTop (𝓝 r)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun j => isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t) atTop
      (𝓝 (isoNegStieltjes (isoMP r) t)) := by
  obtain ⟨-, -, -, hall⟩ := lem_app_iso_mp hr
  obtain ⟨⟨hmpos, hmquad⟩, -, -⟩ := hall t ht
  set mstar := isoNegStieltjes (isoMP r) t with hmdef
  set b := t + 1 / r - 1 with hbdef
  have hbm : b * mstar = 1 - t * mstar ^ 2 := by linarith [hmquad]
  have key : ∀ x : ℝ, 0 ≤ x → |x - mstar| ≤ mstar * |t * x ^ 2 + b * x - 1| := by
    intro x hx
    have e : mstar * (t * x ^ 2 + b * x - 1) = (x - mstar) * (t * mstar * x + 1) := by
      linear_combination x * hbm
    have h2 : 1 ≤ |t * mstar * x + 1| := by
      have hnn : 0 ≤ t * mstar * x + 1 := by
        have := mul_nonneg (mul_nonneg ht.le hmpos.le) hx
        linarith
      rw [abs_of_nonneg hnn]
      have := mul_nonneg (mul_nonneg ht.le hmpos.le) hx
      linarith
    have h3 : mstar * |t * x ^ 2 + b * x - 1| = |(x - mstar) * (t * mstar * x + 1)| := by
      rw [← e, abs_mul, abs_of_pos hmpos]
    rw [h3, abs_mul]
    exact le_mul_of_one_le_right (abs_nonneg _) h2
  have hcb : ∀ j, 0 ≤ isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t ∧
      isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t ≤ 1 / t := by
    intro j
    haveI := m_norm_prob (hp j).pos_out (hp j).mass_out
    have h := m_negS_bounds (m_norm_supp (hp j).pos_out (hp j).supp_out) ht
    rwa [measure_univ, ENNReal.toReal_one] at h
  have hB : Tendsto (fun j => 3 * gout j / ((gout j / gin j) ^ 2 * t ^ 2)) atTop (𝓝 0) := by
    have h : Tendsto (fun j => 3 * gout j / ((gout j / gin j) ^ 2 * t ^ 2)) atTop
        (𝓝 (3 * 0 / (r ^ 2 * t ^ 2))) :=
      (hout.const_mul 3).div ((hratio.pow 2).mul_const (t ^ 2))
        (mul_pos (pow_pos hr 2) (pow_pos ht 2)).ne'
    rwa [mul_zero, zero_div] at h
  have hdiff : Tendsto (fun j => gin j / gout j - 1 / r) atTop (𝓝 0) := by
    have hinv : Tendsto (fun j => gin j / gout j) atTop (𝓝 r⁻¹) := by
      simpa [inv_div] using hratio.inv₀ hr.ne'
    have h := hinv.sub_const (1 / r)
    have e : r⁻¹ - 1 / r = 0 := by rw [one_div, sub_self]
    rwa [e] at h
  have hD : Tendsto (fun j => 3 * gout j / ((gout j / gin j) ^ 2 * t ^ 2) +
      |gin j / gout j - 1 / r| * (1 / t)) atTop (𝓝 0) := by
    have h := hB.add ((hdiff.abs).mul_const (1 / t))
    simpa using h
  have hsq : Tendsto (fun j => isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t - mstar)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => ?_) (by have h := hD.const_mul mstar; rwa [mul_zero] at h)
    rw [Real.norm_eq_abs]
    have hc := hcb j
    have hbound := thm_app_iso_small_i gin gout mo mi r hp hr hin hout hratio j t ht
    have hQe : t * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t ^ 2 +
        b * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t - 1 =
        (t * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t ^ 2 +
          (t + gin j / gout j - 1) * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t - 1) -
        (gin j / gout j - 1 / r) * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t := by
      rw [hbdef]; ring
    have habsQ : |t * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t ^ 2 +
        b * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t - 1| ≤
        3 * gout j / ((gout j / gin j) ^ 2 * t ^ 2) +
          |gin j / gout j - 1 / r| * (1 / t) := by
      rw [hQe]
      have hdc : |(gin j / gout j - 1 / r) * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t|
          ≤ |gin j / gout j - 1 / r| * (1 / t) := by
        rw [abs_mul, abs_of_nonneg hc.1]
        exact mul_le_mul_of_nonneg_left hc.2 (abs_nonneg _)
      calc _ = |(t * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t ^ 2 +
            (t + gin j / gout j - 1) * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t - 1) +
            -((gin j / gout j - 1 / r) * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t)| := by
            rw [sub_eq_add_neg]
        _ ≤ |(t * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t ^ 2 +
            (t + gin j / gout j - 1) * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t - 1)| +
            |-((gin j / gout j - 1 / r) * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t)| :=
            abs_add_le _ _
        _ = |(t * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t ^ 2 +
            (t + gin j / gout j - 1) * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t - 1)| +
            |(gin j / gout j - 1 / r) * isoNegStieltjes (isoNormMeasure (gout j) (mo j)) t| := by
            rw [abs_neg]
        _ ≤ 3 * gout j / ((gout j / gin j) ^ 2 * t ^ 2) +
            |gin j / gout j - 1 / r| * (1 / t) := add_le_add hbound hdc
    have := mul_le_mul_of_nonneg_left habsQ hmpos.le
    exact le_trans (key _ hc.1) this
  exact tendsto_sub_nhds_zero_iff.1 hsq

/-- thm:app-iso-small, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1508–1531):
```latex
\begin{theorem}[Small aspect ratios]\label{thm:app-iso-small}
Let $\gin^{(j)},\gout^{(j)}\to0$ with $r_j\defeq\gout^{(j)}/\gin^{(j)}\to r\in(0,\infty)$,
and let $(\mathfrak m_{\mathrm{out}}^{(j)},\mathfrak m_{\mathrm{in}}^{(j)})$ be the isotropic
measure pair at $(\gin^{(j)},\gout^{(j)})$ of \cref{prop:app-iso-measure}.
Let $\mathsf P_j$ be the image of the probability measure
$\mathfrak m_{\mathrm{out}}^{(j)}/\gout^{(j)}$ under $\lambda\mapsto\lambda/\gout^{(j)}$,
and write $\mathsf m_j(t)\defeq S_{\mathsf P_j}(-t)$.
\begin{enumerate}[label=(\roman*)]
\item For every $t>0$,
\begin{equation}\label{eqn:app-iso-small-residual}
\Big|t\,\mathsf m_j(t)^2+\Big(t+\frac1{r_j}-1\Big)\mathsf m_j(t)-1\Big|\le\frac{3\gout^{(j)}}{r_j^2t^2}.
\end{equation}
\item $\mathsf P_j\to\mathsf M_r$ weakly, and $\int\sqrt x\,\mathsf P_j(\dif x)\to J_r\defeq\int\sqrt x\,\mathsf M_r(\dif x)>0$.
\item The constant satisfies
\begin{equation}\label{eqn:app-iso-small}
\begin{gathered}
C\big(\gin^{(j)},\gout^{(j)}\big)=\frac{r_j}{\sqrt{2\gout^{(j)}}}\int\sqrt x\,\mathsf P_j(\dif x)
\sim\frac{r}{\sqrt{2\gout^{(j)}}}\,J_r,\\
J_r=\int_{a_r}^{b_r}\frac{\sqrt{(b_r-x)(x-a_r)}}{2\pi\sqrt x}\,\dif x .
\end{gathered}
\end{equation}
In particular $J_1=8/(3\pi)$, and $C(\gamma)\sim8/(3\pi\sqrt{2\gamma})$ as $\gamma\downarrow0$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_iso_small_ii (gin gout : ℕ → ℝ) (mo mi : ℕ → Measure ℝ) (r : ℝ)
    (hp : ∀ j, IsIsoMeasurePair (gin j) (gout j) (mo j) (mi j))
    (hr : 0 < r)
    (hin : Tendsto gin atTop (𝓝 0)) (hout : Tendsto gout atTop (𝓝 0))
    (hratio : Tendsto (fun j => gout j / gin j) atTop (𝓝 r)) :
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, f x ∂(isoNormMeasure (gout j) (mo j))) atTop
        (𝓝 (∫ x, f x ∂(isoMP r)))) ∧
    Tendsto (fun j => ∫ x, Real.sqrt x ∂(isoNormMeasure (gout j) (mo j))) atTop
        (𝓝 (isoJr r)) ∧
    0 < isoJr r := by
  obtain ⟨hP, hInt, -, -⟩ := lem_app_iso_mp hr
  have hprob : ∀ j, IsProbabilityMeasure (isoNormMeasure (gout j) (mo j)) :=
    fun j => m_norm_prob (hp j).pos_out (hp j).mass_out
  have hsupp : ∀ j, isoNormMeasure (gout j) (mo j) (Iio 0) = 0 :=
    fun j => m_norm_supp (hp j).pos_out (hp j).supp_out
  have hweak := lem_app_iso_transforms_i (fun j => isoNormMeasure (gout j) (mo j)) (isoMP r)
    hprob hsupp hP (m_isoMP_supp hr)
    (fun t ht => m_transform_conv hr hp hin hout hratio ht)
  have hmean : ∀ j, ∫ x, x ∂(isoNormMeasure (gout j) (mo j)) = gin j / gout j :=
    fun j => (m_norm_mean (hp j)).2
  have hbdd : BddAbove (Set.range fun j => ∫ x, x ∂(isoNormMeasure (gout j) (mo j))) := by
    have hT : Tendsto (fun j => gin j / gout j) atTop (𝓝 r⁻¹) := by
      simpa [inv_div] using hratio.inv₀ hr.ne'
    have hfun : (fun j => ∫ x, x ∂(isoNormMeasure (gout j) (mo j))) =
        fun j => gin j / gout j := funext hmean
    rw [hfun]
    exact hT.bddAbove_range
  have hsq := hweak.2 (fun j => (m_norm_mean (hp j)).1) hInt hbdd
  exact ⟨hweak.1, hsq, m_isoJr_pos hr⟩

private theorem m_sqrt_norm {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) :
    ∫ x, Real.sqrt x ∂(isoNormMeasure γout mo) =
      1 / (γout * Real.sqrt γout) * ∫ l, Real.sqrt l ∂mo := by
  have hsq : ∀ l : ℝ, Real.sqrt (l / γout) = Real.sqrt l / Real.sqrt γout :=
    fun l => Real.sqrt_div' l hp.pos_out.le
  unfold isoNormMeasure
  rw [integral_map (by fun_prop : Measurable fun l : ℝ => l / γout).aemeasurable
    Real.continuous_sqrt.measurable.aestronglyMeasurable, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.2 hp.pos_out.le), smul_eq_mul]
  simp only [hsq, integral_div]
  have hsg : Real.sqrt γout ≠ 0 := (Real.sqrt_pos.2 hp.pos_out).ne'
  have hg : γout ≠ 0 := hp.pos_out.ne'
  field_simp

private theorem m_small_C {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) :
    Cbeta 0 γin γout = γout / γin / Real.sqrt (2 * γout) *
      ∫ x, Real.sqrt x ∂(isoNormMeasure γout mo) := by
  rw [m_sqrt_norm hp, (prop_app_iso_spectral_i hp).1,
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) γout]
  have hs : Real.sqrt γout ≠ 0 := (Real.sqrt_pos.2 hp.pos_out).ne'
  have ht : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)).ne'
  have hg : γout ≠ 0 := hp.pos_out.ne'
  have hgi : γin ≠ 0 := hp.pos_in.ne'
  have hss : Real.sqrt γout * Real.sqrt γout = γout := Real.mul_self_sqrt hp.pos_out.le
  have key : γout / γin / (Real.sqrt 2 * Real.sqrt γout) * (1 / (γout * Real.sqrt γout)) =
      1 / (Real.sqrt 2 * γin * γout) := by
    rw [div_div, div_mul_div_comm, div_eq_div_iff
      (mul_ne_zero (mul_ne_zero hgi (mul_ne_zero ht hs)) (mul_ne_zero hg hs))
      (mul_ne_zero (mul_ne_zero ht hgi) hg)]
    linear_combination (-(Real.sqrt 2 * γin * γout)) * hss
  rw [← mul_assoc, key]

private theorem m_isoJr_eq {r : ℝ} (hr : 0 < r) :
    isoJr r = ∫ x in isoMPa r..isoMPb r,
      Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * Real.sqrt x) := by
  have ha : 0 ≤ isoMPa r := div_nonneg (sq_nonneg _) hr.le
  have hab : isoMPa r ≤ isoMPb r := by
    unfold isoMPa isoMPb
    apply div_le_div_of_nonneg_right _ hr.le
    nlinarith [Real.sqrt_nonneg r]
  have hid := (lem_app_iso_mp hr).2.1
  haveI : IsFiniteMeasure (isoMP r) := ⟨by simp [(lem_app_iso_mp hr).1.measure_univ]⟩
  have hI : Integrable (fun x : ℝ => Real.sqrt x) (isoMP r) := by
    have hg : Integrable (fun x : ℝ => 1 + |x|) (isoMP r) := (integrable_const (1:ℝ)).add hid.abs
    refine Integrable.mono' hg (by fun_prop : Measurable fun x : ℝ => Real.sqrt x).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x)]
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - 1)]
    · rw [Real.sqrt_eq_zero'.2 hx, abs_of_nonpos hx]
      linarith
  unfold isoJr
  unfold isoMP at hI ⊢
  obtain ⟨h1, h2⟩ := integrable_add_measure.1 hI
  rw [integral_add_measure h1 h2, integral_smul_measure, integral_dirac, Real.sqrt_zero,
    smul_zero, zero_add, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
  have hx0 : 0 < x := lt_of_le_of_lt ha hx.1
  have hD : 0 ≤ Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * x) :=
    div_nonneg (Real.sqrt_nonneg _) (mul_pos (mul_pos two_pos Real.pi_pos) hx0).le
  rw [ENNReal.toReal_ofReal hD, smul_eq_mul]
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  rw [div_mul_eq_mul_div, div_eq_div_iff (mul_pos (mul_pos two_pos Real.pi_pos) hx0).ne'
    (mul_pos (mul_pos two_pos Real.pi_pos) hs).ne']
  linear_combination (2 * Real.pi * Real.sqrt ((isoMPb r - x) * (x - isoMPa r))) * hxx

private theorem m_isoJr_one : isoJr 1 = 8 / (3 * Real.pi) := by
  have h1 : isoMPa 1 = 0 := by simp [isoMPa]
  have h4 : isoMPb 1 = 4 := by norm_num [isoMPb]
  rw [m_isoJr_eq one_pos, h1, h4]
  have hc : ∫ x in (0:ℝ)..4, Real.sqrt ((4 - x) * (x - 0)) / (2 * Real.pi * Real.sqrt x) =
      ∫ x in (0:ℝ)..4, Real.sqrt (4 - x) / (2 * Real.pi) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num)] at hx
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx.1
    rw [sub_zero, Real.sqrt_mul (by linarith [hx.2] : (0:ℝ) ≤ 4 - x)]
    field_simp
  have hsub : ∫ x in (0:ℝ)..4, Real.sqrt (4 - x) = ∫ x in (0:ℝ)..4, Real.sqrt x := by
    have := intervalIntegral.integral_comp_sub_left (fun y : ℝ => Real.sqrt y) (4:ℝ)
      (a := (0:ℝ)) (b := (4:ℝ))
    simpa only [sub_self, sub_zero] using this
  have hroot : ∫ x in (0:ℝ)..4, Real.sqrt x = 16 / 3 := by
    have e : ∫ x in (0:ℝ)..4, Real.sqrt x = ∫ x in (0:ℝ)..4, x ^ (1 / (2:ℝ)) :=
      intervalIntegral.integral_congr (fun x _ => Real.sqrt_eq_rpow x)
    rw [e, integral_rpow (Or.inl (by norm_num))]
    have h4 : (4:ℝ) ^ (1 / (2:ℝ) + 1) = 8 := by
      rw [Real.rpow_add (by norm_num : (0:ℝ) < 4), Real.rpow_one, ← Real.sqrt_eq_rpow,
        show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      norm_num
    rw [h4, Real.zero_rpow (by norm_num)]
    norm_num
  rw [hc, intervalIntegral.integral_div, hsub, hroot]
  field_simp
  ring

/-- thm:app-iso-small, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1508–1531):
```latex
\begin{theorem}[Small aspect ratios]\label{thm:app-iso-small}
Let $\gin^{(j)},\gout^{(j)}\to0$ with $r_j\defeq\gout^{(j)}/\gin^{(j)}\to r\in(0,\infty)$,
and let $(\mathfrak m_{\mathrm{out}}^{(j)},\mathfrak m_{\mathrm{in}}^{(j)})$ be the isotropic
measure pair at $(\gin^{(j)},\gout^{(j)})$ of \cref{prop:app-iso-measure}.
Let $\mathsf P_j$ be the image of the probability measure
$\mathfrak m_{\mathrm{out}}^{(j)}/\gout^{(j)}$ under $\lambda\mapsto\lambda/\gout^{(j)}$,
and write $\mathsf m_j(t)\defeq S_{\mathsf P_j}(-t)$.
\begin{enumerate}[label=(\roman*)]
\item For every $t>0$,
\begin{equation}\label{eqn:app-iso-small-residual}
\Big|t\,\mathsf m_j(t)^2+\Big(t+\frac1{r_j}-1\Big)\mathsf m_j(t)-1\Big|\le\frac{3\gout^{(j)}}{r_j^2t^2}.
\end{equation}
\item $\mathsf P_j\to\mathsf M_r$ weakly, and $\int\sqrt x\,\mathsf P_j(\dif x)\to J_r\defeq\int\sqrt x\,\mathsf M_r(\dif x)>0$.
\item The constant satisfies
\begin{equation}\label{eqn:app-iso-small}
\begin{gathered}
C\big(\gin^{(j)},\gout^{(j)}\big)=\frac{r_j}{\sqrt{2\gout^{(j)}}}\int\sqrt x\,\mathsf P_j(\dif x)
\sim\frac{r}{\sqrt{2\gout^{(j)}}}\,J_r,\\
J_r=\int_{a_r}^{b_r}\frac{\sqrt{(b_r-x)(x-a_r)}}{2\pi\sqrt x}\,\dif x .
\end{gathered}
\end{equation}
In particular $J_1=8/(3\pi)$, and $C(\gamma)\sim8/(3\pi\sqrt{2\gamma})$ as $\gamma\downarrow0$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_iso_small_iii (gin gout : ℕ → ℝ) (mo mi : ℕ → Measure ℝ) (r : ℝ)
    (hp : ∀ j, IsIsoMeasurePair (gin j) (gout j) (mo j) (mi j))
    (hr : 0 < r)
    (hin : Tendsto gin atTop (𝓝 0)) (hout : Tendsto gout atTop (𝓝 0))
    (hratio : Tendsto (fun j => gout j / gin j) atTop (𝓝 r)) :
    (∀ j : ℕ, Cbeta 0 (gin j) (gout j) =
        gout j / gin j / Real.sqrt (2 * gout j) *
          ∫ x, Real.sqrt x ∂(isoNormMeasure (gout j) (mo j))) ∧
    Asymptotics.IsEquivalent atTop (fun j => Cbeta 0 (gin j) (gout j))
        (fun j => r / Real.sqrt (2 * gout j) * isoJr r) ∧
    isoJr r = ∫ x in isoMPa r..isoMPb r,
        Real.sqrt ((isoMPb r - x) * (x - isoMPa r)) / (2 * Real.pi * Real.sqrt x) ∧
    isoJr 1 = 8 / (3 * Real.pi) ∧
    Tendsto (fun γ : ℝ => Cbeta 0 γ γ / (8 / (3 * Real.pi * Real.sqrt (2 * γ))))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hweak := thm_app_iso_small_ii gin gout mo mi r hp hr hin hout hratio
  have hsq := hweak.2.1
  have hJ : 0 < isoJr r := hweak.2.2
  refine ⟨fun j => m_small_C (hp j), ?_, m_isoJr_eq hr, m_isoJr_one, C0_small_asymp⟩
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  have h1 : Tendsto (fun j => gout j / gin j / r) atTop (𝓝 1) := by
    have := hratio.div_const r
    rwa [div_self hr.ne'] at this
  have h2 : Tendsto (fun j => (∫ x, Real.sqrt x ∂(isoNormMeasure (gout j) (mo j))) / isoJr r)
      atTop (𝓝 1) := by
    have := hsq.div_const (isoJr r)
    rwa [div_self hJ.ne'] at this
  have h3 := h1.mul h2
  rw [one_mul] at h3
  refine Tendsto.congr (fun j => ?_) h3
  have hgi : gin j ≠ 0 := (hp j).pos_in.ne'
  have hgo : 0 < Real.sqrt (2 * gout j) := Real.sqrt_pos.2 (by linarith [(hp j).pos_out])
  have hgo' : Real.sqrt (gout j * 2) ≠ 0 := by
    rw [mul_comm]; exact hgo.ne'
  simp only [Pi.div_apply]
  rw [m_small_C (hp j)]
  field_simp

/-! ## Large aspect ratios -/

private lemma m_chi_half_pos {H : ℝ → ENNReal} (K : ℝ) :
    ∫⁻ g in Ioi (0 : ℝ), H (g ^ 2) * ENNReal.ofReal (K * Real.exp (-(g ^ 2 / 2))) =
      ∫⁻ x in Ioi (0 : ℝ), H x * ENNReal.ofReal (K * Real.exp (-(x / 2)) / (2 * Real.sqrt x)) := by
  have himg : (fun g : ℝ => g ^ 2) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact pow_pos (show (0:ℝ) < g from hg) 2
    · intro hx
      exact ⟨Real.sqrt x, Real.sqrt_pos.mpr hx, Real.sq_sqrt hx.le⟩
  have hderiv : ∀ g ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun g : ℝ => g ^ 2) (2 * g) (Ioi (0 : ℝ)) g := by
    intro g _
    exact (hasDerivAt_pow 2 g).hasDerivWithinAt.congr_deriv (by norm_num)
  have hinj : InjOn (fun g : ℝ => g ^ 2) (Ioi (0 : ℝ)) := by
    intro a ha b hb h
    exact (pow_left_inj₀ (le_of_lt ha) (le_of_lt hb) two_ne_zero).mp h
  calc ∫⁻ g in Ioi (0 : ℝ), H (g ^ 2) * ENNReal.ofReal (K * Real.exp (-(g ^ 2 / 2)))
      = ∫⁻ g in Ioi (0 : ℝ), ENNReal.ofReal |2 * g| *
          (fun x : ℝ => H x * ENNReal.ofReal (K * Real.exp (-(x / 2)) / (2 * Real.sqrt x)))
            (g ^ 2) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun g hg => ?_)
        have hg' : 0 < g := hg
        dsimp only
        rw [Real.sqrt_sq hg'.le, abs_of_pos (by linarith : (0:ℝ) < 2 * g)]
        have h1 : ENNReal.ofReal (2 * g) *
            ENNReal.ofReal (K * Real.exp (-(g ^ 2 / 2)) / (2 * g))
            = ENNReal.ofReal (K * Real.exp (-(g ^ 2 / 2))) := by
          rw [← ENNReal.ofReal_mul (by linarith)]
          congr 1
          field_simp
        calc H (g ^ 2) * ENNReal.ofReal (K * Real.exp (-(g ^ 2 / 2)))
            = H (g ^ 2) * (ENNReal.ofReal (2 * g) *
                ENNReal.ofReal (K * Real.exp (-(g ^ 2 / 2)) / (2 * g))) := by rw [h1]
          _ = _ := by ring
    _ = ∫⁻ x in (fun g : ℝ => g ^ 2) '' Ioi (0 : ℝ),
          H x * ENNReal.ofReal (K * Real.exp (-(x / 2)) / (2 * Real.sqrt x)) :=
        (lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj
          (fun x : ℝ => H x * ENNReal.ofReal (K * Real.exp (-(x / 2)) / (2 * Real.sqrt x)))).symm
    _ = _ := by rw [himg]

private lemma m_chi_neg_half (F : ℝ → ENNReal) :
    ∫⁻ a in Iio (0 : ℝ), F a = ∫⁻ g in Ioi (0 : ℝ), F (-g) := by
  have himg : (fun g : ℝ => -g) '' Ioi (0 : ℝ) = Iio (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact neg_lt_zero.mpr (show (0:ℝ) < g from hg)
    · intro hx
      exact ⟨-x, show (0:ℝ) < -x from neg_pos.mpr hx, neg_neg x⟩
  have hd : ∀ g ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun g : ℝ => -g) (-1) (Ioi (0 : ℝ)) g :=
    fun g _ => (hasDerivAt_neg g).hasDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd
    neg_injective.injOn F
  rw [himg] at key
  rw [key]
  simp

private lemma m_chi_density_aux {H : ℝ → ENNReal} (hH : Measurable H) {K : ℝ} (hK : 0 ≤ K) :
    ∫⁻ a, H (a ^ 2) * ENNReal.ofReal (K * Real.exp (-(a ^ 2 / 2))) =
      ∫⁻ x in Ioi (0 : ℝ), H x * ENNReal.ofReal (K * Real.exp (-(x / 2)) / Real.sqrt x) := by
  set F : ℝ → ENNReal := fun a => H (a ^ 2) * ENNReal.ofReal (K * Real.exp (-(a ^ 2 / 2)))
    with hF
  have hsplit : ∫⁻ a, F a = (∫⁻ a in Ioi (0 : ℝ), F a) + ∫⁻ a in Iio (0 : ℝ), F a := by
    have := lintegral_add_compl (μ := volume) F (A := Ioi (0 : ℝ)) measurableSet_Ioi
    rw [compl_Ioi, ← setLIntegral_congr Iio_ae_eq_Iic] at this
    exact this.symm
  have h1 : ∫⁻ a in Ioi (0 : ℝ), F a =
      ∫⁻ x in Ioi (0 : ℝ), H x * ENNReal.ofReal (K * Real.exp (-(x / 2)) / (2 * Real.sqrt x)) :=
    m_chi_half_pos K
  have hneg : ∫⁻ a in Iio (0 : ℝ), F a = ∫⁻ a in Ioi (0 : ℝ), F a := by
    rw [m_chi_neg_half F]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun g _ => ?_)
    simp only [hF, neg_sq]
  have hG : Measurable (fun x : ℝ =>
      H x * ENNReal.ofReal (K * Real.exp (-(x / 2)) / (2 * Real.sqrt x))) :=
    hH.mul (by fun_prop)
  calc ∫⁻ a, F a = (∫⁻ a in Ioi (0 : ℝ), F a) + ∫⁻ a in Iio (0 : ℝ), F a := hsplit
    _ = (∫⁻ a in Ioi (0 : ℝ), F a) + ∫⁻ a in Ioi (0 : ℝ), F a := by rw [hneg]
    _ = (∫⁻ x in Ioi (0 : ℝ), H x * ENNReal.ofReal (K * Real.exp (-(x / 2)) / (2 * Real.sqrt x))) +
          ∫⁻ x in Ioi (0 : ℝ), H x * ENNReal.ofReal (K * Real.exp (-(x / 2)) / (2 * Real.sqrt x)) := by
        congr 1 <;> exact h1
    _ = ∫⁻ x in Ioi (0 : ℝ), (H x * ENNReal.ofReal (K * Real.exp (-(x / 2)) / (2 * Real.sqrt x)) +
          H x * ENNReal.ofReal (K * Real.exp (-(x / 2)) / (2 * Real.sqrt x))) :=
        (lintegral_add_left hG _).symm
    _ = ∫⁻ x in Ioi (0 : ℝ), H x * ENNReal.ofReal (K * Real.exp (-(x / 2)) / Real.sqrt x) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
        have hc : 0 ≤ K * Real.exp (-(x / 2)) / (2 * Real.sqrt x) := by
          apply div_nonneg (mul_nonneg hK (Real.exp_pos _).le)
          positivity
        rw [← mul_add, ← ENNReal.ofReal_add hc hc]
        congr 2
        ring

/-- Preamble of `thm:app-iso-large` (`eqn:app-iso-chi`, `section.tex` l.1640–1665): the law `𝖷` of
`g²` has density `e^{−x/2}/√(2πx)` on `x>0`, first moment `1` and half-moment `√(2/π)`. -/
theorem isoChi_facts :
    isoChi = volume.withDensity (fun x : ℝ =>
        ENNReal.ofReal ((Ioi (0 : ℝ)).indicator
          (fun x : ℝ => Real.exp (-(x / 2)) / Real.sqrt (2 * Real.pi * x)) x)) ∧
    ∫ x, x ∂isoChi = 1 ∧
    ∫ x, Real.sqrt x ∂isoChi = Real.sqrt (2 / Real.pi) := by
  have hmap : ∀ f : ℝ → ℝ, Measurable f →
      ∫ x, f x ∂isoChi = ∫ g, f (g ^ 2) ∂(gaussianReal 0 1) := by
    intro f hf
    unfold isoChi
    exact integral_map (by fun_prop : Measurable fun g : ℝ => g ^ 2).aemeasurable
      hf.aestronglyMeasurable
  have hm1 : ∫ x, x ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal
  have hm2 : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have h := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_of_integral_eq_zero aemeasurable_id (by simpa using hm1)] at h
    simpa using h
  refine ⟨?_, ?_, ?_⟩
  · have hφ : ∀ a : ℝ, gaussianPDF 0 1 a =
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(a ^ 2 / 2))) := by
      intro a
      show ENNReal.ofReal ((Real.sqrt (2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹ *
        Real.exp (-(a - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ)))) = _
      congr 1
      simp only [NNReal.coe_one, mul_one, sub_zero]
      ring_nf
    have hcE : ∀ x : ℝ, 0 < x →
        ENNReal.ofReal (Real.exp (-(x / 2)) / Real.sqrt (2 * Real.pi * x)) =
          ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x / 2)) / Real.sqrt x) := by
      intro x hx
      congr 1
      rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * Real.pi) x]
      have h1 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
      have h2 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
      field_simp
    have hdens : isoChi = volume.withDensity (fun x : ℝ =>
        ENNReal.ofReal ((Ioi (0 : ℝ)).indicator
          (fun x : ℝ => Real.exp (-(x / 2)) / Real.sqrt (2 * Real.pi * x)) x)) := by
      refine Measure.ext fun s hs => ?_
      have hsq : Measurable fun g : ℝ => g ^ 2 := by fun_prop
      have hsm : MeasurableSet ((fun g : ℝ => g ^ 2) ⁻¹' s) := hsq hs
      unfold isoChi
      rw [Measure.map_apply hsq hs, gaussianReal_of_var_ne_zero 0 one_ne_zero,
        withDensity_apply _ hsm, withDensity_apply _ hs,
        ← lintegral_indicator hsm, ← lintegral_indicator hs]
      have hL : ∀ a : ℝ, ((fun g : ℝ => g ^ 2) ⁻¹' s).indicator (gaussianPDF 0 1) a =
          s.indicator (1 : ℝ → ENNReal) (a ^ 2) *
            ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(a ^ 2 / 2))) := by
        intro a
        by_cases ha : a ^ 2 ∈ s
        · have ha' : a ∈ (fun g : ℝ => g ^ 2) ⁻¹' s := ha
          rw [Set.indicator_of_mem ha', Set.indicator_of_mem ha, Pi.one_apply, one_mul, hφ]
        · have ha' : a ∉ (fun g : ℝ => g ^ 2) ⁻¹' s := ha
          rw [Set.indicator_of_notMem ha', Set.indicator_of_notMem ha, zero_mul]
      have hR : ∀ x : ℝ, s.indicator (fun x : ℝ => ENNReal.ofReal ((Ioi (0 : ℝ)).indicator
          (fun x : ℝ => Real.exp (-(x / 2)) / Real.sqrt (2 * Real.pi * x)) x)) x =
          (Ioi (0 : ℝ)).indicator (fun x : ℝ => s.indicator (1 : ℝ → ENNReal) x *
            ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x / 2)) / Real.sqrt x)) x := by
        intro x
        by_cases hx : (0 : ℝ) < x <;> by_cases hxs : x ∈ s <;>
          simp [Set.indicator, hx, hxs, hcE x]
      rw [lintegral_congr hL, m_chi_density_aux (measurable_one.indicator hs)
        (inv_nonneg.mpr (Real.sqrt_nonneg _)), lintegral_congr hR, lintegral_indicator measurableSet_Ioi]
    exact hdens
  · refine (hmap (fun x => x) measurable_id).trans ?_
    simpa using hm2
  · refine (hmap (fun x => Real.sqrt x) (by fun_prop)).trans ?_
    simp only [Real.sqrt_sq_eq_abs]
    exact Muon.Foundations.gaussian_abs_moment

private theorem m_restrict_eq {η mo : Measure ℝ} {c : ℝ} (hmo : mo = ENNReal.ofReal c • Measure.dirac 0 + η)
    (h0 : η (Iic 0) = 0) : mo.restrict (Ioi 0) = η := by
  have hset : {x : ℝ | ¬ (x ∈ Ioi (0:ℝ))} = Iic 0 := by
    ext x
    simp
  have hae : ∀ᵐ x ∂η, x ∈ Ioi (0:ℝ) := by
    refine ae_iff.2 ?_
    rw [hset]
    exact h0
  have hd : (Measure.dirac (0:ℝ)).restrict (Ioi 0) = 0 := by
    rw [Measure.restrict_eq_zero]
    simp
  rw [hmo, Measure.restrict_add, Measure.restrict_smul, hd, Measure.restrict_eq_self_of_ae_mem hae]
  simp

private theorem m_delta_stieltjes {η : Measure ℝ} [IsFiniteMeasure η] (h0 : η (Iio 0) = 0)
    {c : ℝ} (hc : 0 ≤ c) {τ : ℝ} (hτ : 0 < τ) :
    isoNegStieltjes (ENNReal.ofReal c • Measure.dirac 0 + η) τ = c / τ + isoNegStieltjes η τ := by
  have hI := resolvent_integrable η h0 τ hτ
  have hD : Integrable (fun x : ℝ => (x + τ)⁻¹) (Measure.dirac (0:ℝ)) := by
    refine Integrable.mono' (integrable_const τ⁻¹)
      (by fun_prop : Measurable fun x : ℝ => (x + τ)⁻¹).aestronglyMeasurable ?_
    refine (ae_dirac_iff (measurableSet_le (by fun_prop) (by fun_prop))).2 ?_
    simp [abs_of_pos hτ]
  have hD' : Integrable (fun x : ℝ => (x + τ)⁻¹) (ENNReal.ofReal c • Measure.dirac (0:ℝ)) :=
    hD.smul_measure ENNReal.ofReal_ne_top
  unfold isoNegStieltjes
  rw [integral_add_measure hD' hI, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal hc, smul_eq_mul, zero_add, div_eq_mul_inv]

private theorem m_gauss_identity {t : ℝ} (ht : 0 < t) :
    1 - t * isoNegStieltjes isoChi t = isoPhi (1 / t) := by
  rw [lem_app_iso_gaussian_i (1 / t) (by positivity)]
  have hsq : ((2 * (1 / t)) ^ (-(1 / 2 : ℝ))) ^ 2 = t / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have e : (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 := by norm_num
    rw [e, Real.rpow_neg_one]
    field_simp
  have hF : isoF ((2 * (1 / t)) ^ (-(1 / 2 : ℝ))) = ∫ g, g ^ 2 / (g ^ 2 + t) ∂(gaussianReal 0 1) := by
    unfold isoF
    congr 1
    funext g
    rw [show 2 * ((2 * (1 / t)) ^ (-(1 / 2 : ℝ))) ^ 2 = t by rw [hsq]; ring]
  have hS : isoNegStieltjes isoChi t = ∫ g, (g ^ 2 + t)⁻¹ ∂(gaussianReal 0 1) := by
    unfold isoNegStieltjes isoChi
    exact integral_map (by fun_prop : Measurable fun g : ℝ => g ^ 2).aemeasurable
      (by fun_prop : Measurable fun x : ℝ => (x + t)⁻¹).aestronglyMeasurable
  have hI : Integrable (fun g : ℝ => (g ^ 2 + t)⁻¹) (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_const t⁻¹)
      (by fun_prop : Measurable fun g : ℝ => (g ^ 2 + t)⁻¹).aestronglyMeasurable
      (Eventually.of_forall fun g => ?_)
    have hp : 0 < g ^ 2 + t := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp)]
    exact inv_anti₀ ht (by linarith [sq_nonneg g])
  have hpt : (fun g : ℝ => g ^ 2 / (g ^ 2 + t)) = fun g => 1 - t * (g ^ 2 + t)⁻¹ := by
    funext g
    have hp : 0 < g ^ 2 + t := by positivity
    field_simp
    ring
  rw [hF, hS, hpt, integral_sub (integrable_const 1) (hI.const_mul t), integral_const_mul,
    integral_const]
  simp

private theorem m_phi_lip {v w : ℝ} (hv : 0 < v) (hw : 0 < w) :
    |isoPhi v - isoPhi w| ≤ |v - w| := by
  have hd : ∀ x ∈ Ioi (0:ℝ), DifferentiableAt ℝ isoPhi x := fun x hx =>
    (lem_app_iso_gaussian_ii.2.1 x hx).1.differentiableAt
  have hb : ∀ x ∈ Ioi (0:ℝ), ‖deriv isoPhi x‖ ≤ 1 := by
    intro x hx
    have h := lem_app_iso_gaussian_ii.2.1 x hx
    rw [h.1.deriv, Real.norm_eq_abs, abs_of_pos h.2.1]
    exact h.2.2
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Ioi (0:ℝ))
    (Set.mem_Ioi.2 hv) (Set.mem_Ioi.2 hw)
  simp only [Real.norm_eq_abs, one_mul] at h
  rw [abs_sub_comm v w, abs_sub_comm (isoPhi v)]
  exact h

private theorem m_phi_arg_bound {γin γout H t : ℝ} (hi1 : 1 ≤ γin) (ho1 : 1 ≤ γout) (ht : 0 < t)
    (h0 : 0 ≤ H) (h1 : H ≤ 1) :
    |(γout - H) * (γin - H) / (γin * γout * t) - 1 / t| ≤ (1 / γout + 1 / γin) / t := by
  have hi : 0 < γin := by linarith
  have ho : 0 < γout := by linarith
  have hden : 0 < γin * γout * t := mul_pos (mul_pos hi ho) ht
  have key : (γout - H) * (γin - H) / (γin * γout * t) - 1 / t =
      -(H * (γin + γout - H)) / (γin * γout * t) := by
    field_simp
    ring
  have hnum0 : 0 ≤ H * (γin + γout - H) := mul_nonneg h0 (by linarith)
  have hnum1 : H * (γin + γout - H) ≤ γin + γout := by nlinarith
  have hq : |-(H * (γin + γout - H)) / (γin * γout * t)| =
      H * (γin + γout - H) / (γin * γout * t) := by
    rw [abs_div, abs_neg, abs_of_nonneg hnum0, abs_of_pos hden]
  rw [key, hq]
  have e : (1 / γout + 1 / γin) / t = (γin + γout) / (γin * γout * t) := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right hnum1 hden.le

private theorem m_E_prop {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) (h1 : 1 < γin) (h2 : 1 < γout) :
    IsProbabilityMeasure (isoScaledImage (γin * γout) (mo.restrict (Ioi 0))) ∧
      isoScaledImage (γin * γout) (mo.restrict (Ioi 0)) (Iio 0) = 0 := by
  obtain ⟨η, hηp, hη0, hmo, -⟩ := lem_app_iso_moments_iv hp h1 h2
  haveI := hηp
  have hR : mo.restrict (Ioi 0) = η := m_restrict_eq hmo hη0
  have hη0' : η (Iio 0) = 0 := measure_mono_null Set.Iio_subset_Iic_self hη0
  have hb : 0 < γin * γout := mul_pos (by linarith) (by linarith)
  rw [hR]
  refine ⟨?_, ?_⟩
  · unfold isoScaledImage
    exact (Measure.isProbabilityMeasure_map_iff
      (by fun_prop : Measurable fun l : ℝ => l / (γin * γout)).aemeasurable).2 inferInstance
  · unfold isoScaledImage
    rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
    have hpre : (fun l : ℝ => l / (γin * γout)) ⁻¹' Iio 0 = Iio 0 := by
      ext l
      simp [div_lt_iff₀ hb]
    rw [hpre]
    exact hη0'

private theorem m_closure {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) (h1 : 1 < γin) (h2 : 1 < γout) {t : ℝ} (ht : 0 < t)
    {H : ℝ} (hH : H = 1 - t * isoNegStieltjes (isoScaledImage (γin * γout) (mo.restrict (Ioi 0))) t) :
    isoPhi ((γout - H) * (γin - H) / (γin * γout * t)) = H := by
  obtain ⟨η, hηp, hη0, hmo, hmi⟩ := lem_app_iso_moments_iv hp h1 h2
  haveI := hηp
  have hR : mo.restrict (Ioi 0) = η := m_restrict_eq hmo hη0
  have hη0' : η (Iio 0) = 0 := measure_mono_null Set.Iio_subset_Iic_self hη0
  have hb : 0 < γin * γout := mul_pos (by linarith) (by linarith)
  have hτ : 0 < γin * γout * t := mul_pos hb ht
  have hS : isoNegStieltjes (isoScaledImage (γin * γout) (mo.restrict (Ioi 0))) t =
      γin * γout * isoNegStieltjes η (γin * γout * t) := by
    rw [hR]
    exact m_scaled_stieltjes η hb t
  have hSmo : isoNegStieltjes mo (γin * γout * t) =
      (γout - 1) / (γin * γout * t) + isoNegStieltjes η (γin * γout * t) := by
    rw [hmo]
    exact m_delta_stieltjes hη0' (by linarith) hτ
  have hSmi : isoNegStieltjes mi (γin * γout * t) =
      (γin - 1) / (γin * γout * t) + isoNegStieltjes η (γin * γout * t) := by
    rw [hmi]
    exact m_delta_stieltjes hη0' (by linarith) hτ
  have hH' : H = 1 - (γin * γout * t) * isoNegStieltjes η (γin * γout * t) := by
    rw [hH, hS]
    ring
  have hSmo' : isoNegStieltjes mo (γin * γout * t) = (γout - H) / (γin * γout * t) := by
    rw [hSmo, hH']
    field_simp
    ring
  have hSmi' : isoNegStieltjes mi (γin * γout * t) = (γin - H) / (γin * γout * t) := by
    rw [hSmi, hH']
    field_simp
    ring
  have hid := (hp.identity (γin * γout * t) hτ).2
  rw [hSmo', hSmi'] at hid
  have e1 : γout - γin * γout * t * ((γout - H) / (γin * γout * t)) = H := by
    field_simp
    ring
  have e2 : γin * γout * t * ((γout - H) / (γin * γout * t)) * ((γin - H) / (γin * γout * t)) =
      (γout - H) * (γin - H) / (γin * γout * t) := by
    field_simp
  rw [e1, e2] at hid
  exact hid.symm

private theorem m_H_bounds {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) (h1 : 1 < γin) (h2 : 1 < γout) {t : ℝ} (ht : 0 < t)
    {H : ℝ} (hH : H = 1 - t * isoNegStieltjes (isoScaledImage (γin * γout) (mo.restrict (Ioi 0))) t) :
    0 ≤ H ∧ H ≤ 1 := by
  obtain ⟨hprob, h0⟩ := m_E_prop hp h1 h2
  have hb := m_negS_bounds h0 ht
  have hu : ((isoScaledImage (γin * γout) (mo.restrict (Ioi 0))) univ).toReal = 1 := by
    simp
  rw [hu] at hb
  have hSt : isoNegStieltjes (isoScaledImage (γin * γout) (mo.restrict (Ioi 0))) t * t ≤ 1 :=
    (le_div_iff₀ ht).1 hb.2
  constructor
  · rw [hH]; nlinarith [hb.1, ht]
  · rw [hH]; nlinarith [hb.1, ht]

private theorem m_limit_H {gin gout : ℕ → ℝ} {mo mi : ℕ → Measure ℝ}
    (hp : ∀ j, IsIsoMeasurePair (gin j) (gout j) (mo j) (mi j))
    (hin : Tendsto gin atTop atTop) (hout : Tendsto gout atTop atTop) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun j => 1 - t * isoNegStieltjes
      (isoScaledImage (gin j * gout j) ((mo j).restrict (Ioi 0))) t) atTop (𝓝 (isoPhi (1 / t))) := by
  have hδ : Tendsto (fun j => (1 / gout j + 1 / gin j) / t) atTop (𝓝 0) := by
    have h1' : Tendsto (fun j => 1 / gout j) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hout
    have h2' : Tendsto (fun j => 1 / gin j) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hin
    have := (h1'.add h2').div_const t
    simpa using this
  have hlow := (tendsto_const_nhds (x := isoPhi (1 / t))).sub hδ
  have hup := (tendsto_const_nhds (x := isoPhi (1 / t))).add hδ
  rw [sub_zero] at hlow
  rw [add_zero] at hup
  have hev : ∀ᶠ j in atTop, |1 - t * isoNegStieltjes
      (isoScaledImage (gin j * gout j) ((mo j).restrict (Ioi 0))) t - isoPhi (1 / t)| ≤
      (1 / gout j + 1 / gin j) / t := by
    filter_upwards [hin.eventually_gt_atTop 2, hout.eventually_gt_atTop 2] with j hj1 hj2
    have hpj := hp j
    have h1 : 1 < gin j := by linarith
    have h2 : 1 < gout j := by linarith
    set H := 1 - t * isoNegStieltjes
      (isoScaledImage (gin j * gout j) ((mo j).restrict (Ioi 0))) t with hHdef
    have hHb := m_H_bounds hpj h1 h2 ht hHdef
    have hcl := m_closure hpj h1 h2 ht hHdef
    have harg := m_phi_arg_bound h1.le h2.le ht hHb.1 hHb.2
    have hsmall : (1 / gout j + 1 / gin j) / t < 1 / t := by
      have hA : 1 / gout j < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hj2
      have hB : 1 / gin j < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hj1
      have : 1 / gout j + 1 / gin j < 1 := by linarith
      exact div_lt_div_of_pos_right this ht
    have hvpos : 0 < (gout j - H) * (gin j - H) / (gin j * gout j * t) := by
      have hl := (abs_le.1 harg).1
      have h1t : 0 < 1 / t := one_div_pos.2 ht
      linarith
    have hlip := m_phi_lip hvpos (one_div_pos.2 ht)
    rw [hcl] at hlip
    exact hlip.trans harg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [hev] with j hj
    have hj' := abs_le.1 hj
    linarith [hj'.1]
  · filter_upwards [hev] with j hj
    have hj' := abs_le.1 hj
    linarith [hj'.2]

/-- thm:app-iso-large, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1640–1665):
```latex
\begin{theorem}[Large aspect ratios]\label{thm:app-iso-large}
Let $\gin^{(j)},\gout^{(j)}\to\infty$, without a condition on their ratio,
and let $(\mathfrak m_{\mathrm{out}}^{(j)},\mathfrak m_{\mathrm{in}}^{(j)})$ be the isotropic
measure pair at $(\gin^{(j)},\gout^{(j)})$ of \cref{prop:app-iso-measure}.
For $j$ with $\gin^{(j)},\gout^{(j)}>1$ write
$\mathfrak m_{\mathrm{out}}^{(j)}=(\gout^{(j)}-1)\delta_0+\eta_j$ as in
\cref{lem:app-iso-moments}(iv), let $\mathsf E_j$ be the image of the
probability measure $\eta_j$ under $\lambda\mapsto\lambda/(\gin^{(j)}\gout^{(j)})$,
and put $\epsilon_j\defeq1/\gin^{(j)}+1/\gout^{(j)}$. Let $\mathsf X$ be the law
of $g^2$ for $g\sim\mathcal N(0,1)$, which has density, first moment and
half-moment
\begin{equation}\label{eqn:app-iso-chi}
\frac{e^{-x/2}}{\sqrt{2\pi x}}\,\mathbf 1_{x>0},\qquad
\int x\,\mathsf X(\dif x)=1,\qquad
\int\sqrt x\,\mathsf X(\dif x)=\sqrt{\frac2\pi}.
\end{equation}
Then $\mathsf E_j\to\mathsf X$ weakly,
\begin{equation}\label{eqn:app-iso-large-error}
0\le\sqrt{\frac2\pi}-\int\sqrt x\,\mathsf E_j(\dif x)\le\frac4\pi\sqrt{\epsilon_j},
\end{equation}
and
\begin{equation}\label{eqn:app-iso-large}
C\big(\gin^{(j)},\gout^{(j)}\big)=\frac{1}{\sqrt{2\gin^{(j)}\gout^{(j)}}}\int\sqrt x\,\mathsf E_j(\dif x)\sim\frac{1}{\sqrt{\pi\gin^{(j)}\gout^{(j)}}} .
\end{equation}
In particular $C(\gamma)\sim1/(\sqrt\pi\,\gamma)$ as $\gamma\to\infty$.
\end{theorem}
```
-/
theorem thm_app_iso_large_i (gin gout : ℕ → ℝ) (mo mi : ℕ → Measure ℝ)
    (hp : ∀ j, IsIsoMeasurePair (gin j) (gout j) (mo j) (mi j))
    (hin : Tendsto gin atTop atTop) (hout : Tendsto gout atTop atTop) :
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, f x ∂(isoScaledImage (gin j * gout j) ((mo j).restrict (Ioi 0))))
        atTop (𝓝 (∫ x, f x ∂isoChi)) := by
  intro f
  haveI : IsProbabilityMeasure isoChi := by
    unfold isoChi
    exact (Measure.isProbabilityMeasure_map_iff
      (by fun_prop : Measurable fun g : ℝ => g ^ 2).aemeasurable).2 inferInstance
  have hχ0 : isoChi (Iio 0) = 0 := by
    unfold isoChi
    rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
    have hpre : (fun g : ℝ => g ^ 2) ⁻¹' Iio 0 = ∅ := by
      ext g
      simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
      exact sq_nonneg g
    rw [hpre, measure_empty]
  obtain ⟨ν, hν⟩ : ∃ ν : ℕ → Measure ℝ, ∀ j, ν j = if h : 1 < gin j ∧ 1 < gout j then
      isoScaledImage (gin j * gout j) ((mo j).restrict (Ioi 0)) else isoChi :=
    ⟨_, fun j => rfl⟩
  have hν_eq : ∀ᶠ j in atTop, 1 < gin j ∧ 1 < gout j :=
    (hin.eventually_gt_atTop 1).and (hout.eventually_gt_atTop 1)
  have hprob : ∀ j, IsProbabilityMeasure (ν j) := by
    intro j
    rw [hν j]
    by_cases h : 1 < gin j ∧ 1 < gout j
    · rw [dif_pos h]
      exact (m_E_prop (hp j) h.1 h.2).1
    · rw [dif_neg h]
      infer_instance
  have hsupp : ∀ j, ν j (Iio 0) = 0 := by
    intro j
    rw [hν j]
    by_cases h : 1 < gin j ∧ 1 < gout j
    · rw [dif_pos h]
      exact (m_E_prop (hp j) h.1 h.2).2
    · rw [dif_neg h]
      exact hχ0
  have hconv : ∀ t : ℝ, 0 < t →
      Tendsto (fun j => isoNegStieltjes (ν j) t) atTop (𝓝 (isoNegStieltjes isoChi t)) := by
    intro t ht
    have hX : isoNegStieltjes isoChi t = (1 - isoPhi (1 / t)) / t := by
      rw [← m_gauss_identity ht, sub_sub_cancel, mul_div_cancel_left₀ _ ht.ne']
    rw [hX]
    have hlim := ((tendsto_const_nhds (x := (1:ℝ))).sub
      (m_limit_H hp hin hout ht)).div_const t
    have hE : Tendsto (fun j => isoNegStieltjes
        (isoScaledImage (gin j * gout j) ((mo j).restrict (Ioi 0))) t) atTop
        (𝓝 ((1 - isoPhi (1 / t)) / t)) := by
      refine Tendsto.congr (fun j => ?_) hlim
      show (1 - (1 - t * isoNegStieltjes
        (isoScaledImage (gin j * gout j) ((mo j).restrict (Ioi 0))) t)) / t =
        isoNegStieltjes (isoScaledImage (gin j * gout j) ((mo j).restrict (Ioi 0))) t
      rw [sub_sub_cancel, mul_div_cancel_left₀ _ ht.ne']
    refine Tendsto.congr' ?_ hE
    filter_upwards [hν_eq] with j hj
    rw [hν j, dif_pos hj]
  have key := (lem_app_iso_transforms_i ν isoChi hprob hsupp inferInstance hχ0 hconv).1 f
  refine Tendsto.congr' ?_ key
  filter_upwards [hν_eq] with j hj
  rw [hν j, dif_pos hj]

private theorem m_arctan_int {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun s : ℝ => x / (x + s ^ 2)) (Ioi 0) ∧
      ∫ s in Ioi (0:ℝ), x / (x + s ^ 2) = Real.pi * Real.sqrt x / 2 := by
  have hc : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hcc : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hfun : (fun s : ℝ => x / (x + s ^ 2)) = fun s => (1 + ((Real.sqrt x)⁻¹ * s) ^ 2)⁻¹ := by
    funext s
    have : 0 < x + s ^ 2 := by positivity
    field_simp
    rw [hcc]
    ring
  rw [hfun]
  have hI : Integrable (fun s : ℝ => (1 + ((Real.sqrt x)⁻¹ * s) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hc.ne')
  refine ⟨hI.integrableOn, ?_⟩
  rw [integral_comp_mul_left_Ioi (fun u : ℝ => (1 + u ^ 2)⁻¹) 0 (inv_pos.2 hc)]
  rw [integral_Ioi_inv_one_add_sq]
  simp [mul_zero]
  ring

private theorem m_half_lint (ν : Measure ℝ) [IsFiniteMeasure ν] (h0 : ν (Iio 0) = 0) :
    ∫⁻ x, ENNReal.ofReal (Real.sqrt x) ∂ν =
      ENNReal.ofReal (2 / Real.pi) *
        ∫⁻ s in Ioi (0:ℝ), ∫⁻ x, ENNReal.ofReal (x / (x + s ^ 2)) ∂ν := by
  have hmeas : Measurable (Function.uncurry fun (s x : ℝ) => ENNReal.ofReal (x / (x + s ^ 2))) := by
    fun_prop
  rw [lintegral_lintegral_swap (μ := volume.restrict (Ioi (0:ℝ))) (ν := ν) hmeas.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hae : ∀ᵐ x ∂ν, 0 ≤ x := by
    refine ae_iff.2 ?_
    have : {x : ℝ | ¬ 0 ≤ x} = Iio 0 := by ext x; simp
    rw [this]; exact h0
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · obtain ⟨hI, hv⟩ := m_arctan_int h
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] fun s : ℝ => x / (x + s ^ 2) :=
      Eventually.of_forall fun s => by positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hI hnn, hv, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : 0 < Real.pi := Real.pi_pos
    field_simp

private theorem m_g_meas (ν : Measure ℝ) [IsFiniteMeasure ν] :
    StronglyMeasurable fun s : ℝ => ∫ x, x / (x + s ^ 2) ∂ν := by
  have h : StronglyMeasurable (fun p : ℝ × ℝ => p.2 / (p.2 + p.1 ^ 2)) := by
    apply Measurable.stronglyMeasurable
    fun_prop
  exact h.integral_prod_right'

private theorem m_g_nonneg (ν : Measure ℝ) [IsFiniteMeasure ν] (h0 : ν (Iio 0) = 0) (s : ℝ) :
    0 ≤ ∫ x, x / (x + s ^ 2) ∂ν := by
  apply integral_nonneg_of_ae
  have hae : ∀ᵐ x ∂ν, 0 ≤ x := by
    refine ae_iff.2 ?_
    have : {x : ℝ | ¬ 0 ≤ x} = Iio 0 := by ext x; simp
    rw [this]; exact h0
  filter_upwards [hae] with x hx
  exact div_nonneg hx (by positivity)

private theorem m_half_moment (ν : Measure ℝ) [IsFiniteMeasure ν] (h0 : ν (Iio 0) = 0)
    (G : ℝ → ℝ) (hG : IntegrableOn G (Ioi 0))
    (hle : ∀ s : ℝ, 0 < s → ∫ x, x / (x + s ^ 2) ∂ν ≤ G s) :
    Integrable (fun x : ℝ => Real.sqrt x) ν ∧
      ∫ x, Real.sqrt x ∂ν = 2 / Real.pi * ∫ s in Ioi (0:ℝ), ∫ x, x / (x + s ^ 2) ∂ν := by
  set g : ℝ → ℝ := fun s => ∫ x, x / (x + s ^ 2) ∂ν with hgdef
  have hgm : AEStronglyMeasurable g (volume.restrict (Ioi (0:ℝ))) :=
    (m_g_meas ν).aestronglyMeasurable
  have hgI : IntegrableOn g (Ioi 0) := by
    refine Integrable.mono' hG hgm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (m_g_nonneg ν h0 s)]
    exact hle s hs
  have hinner : ∀ s : ℝ, 0 < s → ∫⁻ x, ENNReal.ofReal (x / (x + s ^ 2)) ∂ν = ENNReal.ofReal (g s) := by
    intro s hs
    have hae : ∀ᵐ x ∂ν, 0 ≤ x := by
      refine ae_iff.2 ?_
      have : {x : ℝ | ¬ 0 ≤ x} = Iio 0 := by ext x; simp
      rw [this]; exact h0
    have hint : Integrable (fun x : ℝ => x / (x + s ^ 2)) ν := by
      refine Integrable.mono' (integrable_const (1:ℝ)) (by fun_prop : Measurable _).aestronglyMeasurable ?_
      filter_upwards [hae] with x hx
      have : 0 < x + s ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hx this.le), div_le_one this]
      nlinarith [sq_nonneg s]
    rw [ofReal_integral_eq_lintegral_ofReal hint]
    filter_upwards [hae] with x hx
    exact div_nonneg hx (by positivity)
  have hL := m_half_lint ν h0
  have hrhs : ∫⁻ s in Ioi (0:ℝ), ∫⁻ x, ENNReal.ofReal (x / (x + s ^ 2)) ∂ν =
      ENNReal.ofReal (∫ s in Ioi (0:ℝ), g s) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgI]
    · refine setLIntegral_congr_fun measurableSet_Ioi ?_
      intro s hs
      exact hinner s hs
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact m_g_nonneg ν h0 s
  rw [hrhs, ← ENNReal.ofReal_mul (by positivity)] at hL
  have hint : Integrable (fun x : ℝ => Real.sqrt x) ν := by
    refine ⟨(by fun_prop : Measurable Real.sqrt).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => Real.sqrt_nonneg x)]
    rw [hL]
    exact ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => Real.sqrt_nonneg x)
    (by fun_prop : Measurable Real.sqrt).aestronglyMeasurable, hL,
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) (integral_nonneg_of_ae ?_))]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact m_g_nonneg ν h0 s

private theorem m_min_int {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun s : ℝ => min 1 (ε / s ^ 2)) (Ioi 0) ∧
      ∫ s in Ioi (0:ℝ), min 1 (ε / s ^ 2) = 2 * Real.sqrt ε := by
  have hc : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hcc : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  set c := Real.sqrt ε with hcdef
  have hsplit : Ioi (0:ℝ) = Ioc 0 c ∪ Ioi c := (Ioc_union_Ioi_eq_Ioi hc.le).symm
  have hmeas : Measurable fun s : ℝ => min 1 (ε / s ^ 2) := by fun_prop
  have hrp : ∀ s : ℝ, 0 < s → ε / s ^ 2 = ε * s ^ (-2 : ℝ) := by
    intro s hs
    rw [Real.rpow_neg hs.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    ring
  have h1 : IntegrableOn (fun s : ℝ => min 1 (ε / s ^ 2)) (Ioc 0 c) := by
    refine Integrable.mono' (integrable_const (1:ℝ)) hmeas.aestronglyMeasurable ?_
    refine Eventually.of_forall fun s => ?_
    have hn : 0 ≤ min 1 (ε / s ^ 2) := le_min zero_le_one (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    simp
  have hI2 : IntegrableOn (fun s : ℝ => ε * s ^ (-2 : ℝ)) (Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hc).const_mul ε
  have h2 : IntegrableOn (fun s : ℝ => min 1 (ε / s ^ 2)) (Ioi c) := by
    refine Integrable.mono' hI2 hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hc.trans hs
    have hn : 0 ≤ min 1 (ε / s ^ 2) := le_min zero_le_one (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hn, ← hrp s hs0]
    exact min_le_right _ _
  refine ⟨?_, ?_⟩
  · rw [hsplit]; exact h1.union h2
  · rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h1 h2]
    have e1 : ∫ s in Ioc 0 c, min 1 (ε / s ^ 2) = c := by
      rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (1:ℝ))]
      · simp [c]
      · intro s hs
        have hs0 : 0 < s := hs.1
        have : 1 ≤ ε / s ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith [hs.2, hs.1]
        exact min_eq_left this
    have e2 : ∫ s in Ioi c, min 1 (ε / s ^ 2) = c := by
      rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s => ε * s ^ (-2 : ℝ))]
      · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hc]
        have : c ^ (-2 + 1 : ℝ) = c⁻¹ := by
          rw [show (-2 + 1 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
        rw [this]
        field_simp
        nlinarith [hcc]
      · intro s hs
        have hs0 : 0 < s := hc.trans hs
        have : ε / s ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]
          have hs' : c < s := hs
          nlinarith [hs', hc, hcc]
        show min 1 (ε / s ^ 2) = ε * s ^ (-2 : ℝ)
        rw [min_eq_right this, hrp s hs0]
    rw [e1, e2]; ring

private theorem m_g_int (ν : Measure ℝ) [IsFiniteMeasure ν] (h0 : ν (Iio 0) = 0)
    (G : ℝ → ℝ) (hG : IntegrableOn G (Ioi 0))
    (hle : ∀ s : ℝ, 0 < s → ∫ x, x / (x + s ^ 2) ∂ν ≤ G s) :
    IntegrableOn (fun s : ℝ => ∫ x, x / (x + s ^ 2) ∂ν) (Ioi 0) := by
  refine Integrable.mono' hG (m_g_meas ν).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (m_g_nonneg ν h0 s)]
  exact hle s hs

private theorem m_half_diff (ν χ : Measure ℝ) [IsFiniteMeasure ν] [IsFiniteMeasure χ]
    (h0ν : ν (Iio 0) = 0) (h0χ : χ (Iio 0) = 0)
    (G : ℝ → ℝ) (hG : IntegrableOn G (Ioi 0))
    (hχG : ∀ s : ℝ, 0 < s → ∫ x, x / (x + s ^ 2) ∂χ ≤ G s)
    {ε : ℝ} (hε : 0 < ε)
    (hd : ∀ s : ℝ, 0 < s → 0 ≤ (∫ x, x / (x + s ^ 2) ∂χ) - ∫ x, x / (x + s ^ 2) ∂ν ∧
      (∫ x, x / (x + s ^ 2) ∂χ) - ∫ x, x / (x + s ^ 2) ∂ν ≤ min 1 (ε / s ^ 2)) :
    0 ≤ ∫ x, Real.sqrt x ∂χ - ∫ x, Real.sqrt x ∂ν ∧
      ∫ x, Real.sqrt x ∂χ - ∫ x, Real.sqrt x ∂ν ≤ 4 / Real.pi * Real.sqrt ε := by
  have hGν : ∀ s : ℝ, 0 < s → ∫ x, x / (x + s ^ 2) ∂ν ≤ G s := fun s hs => by
    linarith [(hd s hs).1, hχG s hs]
  obtain ⟨-, hχ⟩ := m_half_moment χ h0χ G hG hχG
  obtain ⟨-, hν⟩ := m_half_moment ν h0ν G hG hGν
  have hIχ := m_g_int χ h0χ G hG hχG
  have hIν := m_g_int ν h0ν G hG hGν
  obtain ⟨hIm, hm⟩ := m_min_int hε
  rw [hχ, hν, ← mul_sub, ← integral_sub hIχ hIν]
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor
  · apply mul_nonneg (by positivity)
    apply setIntegral_nonneg measurableSet_Ioi
    intro s hs
    exact (hd s hs).1
  · have : ∫ s in Ioi (0:ℝ), ((∫ x, x / (x + s ^ 2) ∂χ) - ∫ x, x / (x + s ^ 2) ∂ν) ≤
        ∫ s in Ioi (0:ℝ), min 1 (ε / s ^ 2) :=
      setIntegral_mono_on (hIχ.sub hIν) hIm measurableSet_Ioi (fun s hs => (hd s hs).2)
    rw [hm] at this
    calc 2 / Real.pi * _ ≤ 2 / Real.pi * (2 * Real.sqrt ε) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 4 / Real.pi * Real.sqrt ε := by ring

private theorem m_H_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] (h0 : ν (Iio 0) = 0) {t : ℝ}
    (ht : 0 < t) : ∫ x, x / (x + t) ∂ν = 1 - t * isoNegStieltjes ν t := by
  have hae : ∀ᵐ x ∂ν, 0 ≤ x := ae_nonneg_of_Iio ν h0
  have hpt : (fun x : ℝ => x / (x + t)) =ᵐ[ν] fun x => 1 - t * (x + t)⁻¹ := by
    filter_upwards [hae] with x hx
    have : 0 < x + t := by linarith
    field_simp
    ring
  rw [integral_congr_ae hpt, integral_sub (integrable_const 1)
    ((resolvent_integrable ν h0 t ht).const_mul t), integral_const_mul]
  simp [isoNegStieltjes]

/-- thm:app-iso-large, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1640–1665):
```latex
\begin{theorem}[Large aspect ratios]\label{thm:app-iso-large}
Let $\gin^{(j)},\gout^{(j)}\to\infty$, without a condition on their ratio,
and let $(\mathfrak m_{\mathrm{out}}^{(j)},\mathfrak m_{\mathrm{in}}^{(j)})$ be the isotropic
measure pair at $(\gin^{(j)},\gout^{(j)})$ of \cref{prop:app-iso-measure}.
For $j$ with $\gin^{(j)},\gout^{(j)}>1$ write
$\mathfrak m_{\mathrm{out}}^{(j)}=(\gout^{(j)}-1)\delta_0+\eta_j$ as in
\cref{lem:app-iso-moments}(iv), let $\mathsf E_j$ be the image of the
probability measure $\eta_j$ under $\lambda\mapsto\lambda/(\gin^{(j)}\gout^{(j)})$,
and put $\epsilon_j\defeq1/\gin^{(j)}+1/\gout^{(j)}$. Let $\mathsf X$ be the law
of $g^2$ for $g\sim\mathcal N(0,1)$, which has density, first moment and
half-moment
\begin{equation}\label{eqn:app-iso-chi}
\frac{e^{-x/2}}{\sqrt{2\pi x}}\,\mathbf 1_{x>0},\qquad
\int x\,\mathsf X(\dif x)=1,\qquad
\int\sqrt x\,\mathsf X(\dif x)=\sqrt{\frac2\pi}.
\end{equation}
Then $\mathsf E_j\to\mathsf X$ weakly,
\begin{equation}\label{eqn:app-iso-large-error}
0\le\sqrt{\frac2\pi}-\int\sqrt x\,\mathsf E_j(\dif x)\le\frac4\pi\sqrt{\epsilon_j},
\end{equation}
and
\begin{equation}\label{eqn:app-iso-large}
C\big(\gin^{(j)},\gout^{(j)}\big)=\frac{1}{\sqrt{2\gin^{(j)}\gout^{(j)}}}\int\sqrt x\,\mathsf E_j(\dif x)\sim\frac{1}{\sqrt{\pi\gin^{(j)}\gout^{(j)}}} .
\end{equation}
In particular $C(\gamma)\sim1/(\sqrt\pi\,\gamma)$ as $\gamma\to\infty$.
\end{theorem}
```
-/
theorem thm_app_iso_large_ii (gin gout : ℕ → ℝ) (mo mi : ℕ → Measure ℝ)
    (hp : ∀ j, IsIsoMeasurePair (gin j) (gout j) (mo j) (mi j))
    (hin : Tendsto gin atTop atTop) (hout : Tendsto gout atTop atTop) :
    ∀ j : ℕ, 1 < gin j → 1 < gout j →
      0 ≤ Real.sqrt (2 / Real.pi) -
          ∫ x, Real.sqrt x ∂(isoScaledImage (gin j * gout j) ((mo j).restrict (Ioi 0))) ∧
      Real.sqrt (2 / Real.pi) -
          ∫ x, Real.sqrt x ∂(isoScaledImage (gin j * gout j) ((mo j).restrict (Ioi 0))) ≤
        4 / Real.pi * Real.sqrt (1 / gin j + 1 / gout j) := by
  intro j h1 h2
  obtain ⟨hprob, h0E⟩ := m_E_prop (hp j) h1 h2
  haveI := hprob
  haveI : IsProbabilityMeasure isoChi := by
    unfold isoChi
    exact (Measure.isProbabilityMeasure_map_iff
      (by fun_prop : Measurable fun g : ℝ => g ^ 2).aemeasurable).2 inferInstance
  have hχ0 : isoChi (Iio 0) = 0 := by
    unfold isoChi
    rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
    have hpre : (fun g : ℝ => g ^ 2) ⁻¹' Iio 0 = ∅ := by
      ext g
      simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
      exact sq_nonneg g
    rw [hpre, measure_empty]
  have hεpos : 0 < 1 / gin j + 1 / gout j := by
    have := (hp j).pos_in
    have := (hp j).pos_out
    positivity
  have hΦ := lem_app_iso_gaussian_ii
  have hχeq : ∀ s : ℝ, 0 < s → ∫ x, x / (x + s ^ 2) ∂isoChi = isoPhi (1 / s ^ 2) := by
    intro s hs
    have ht : 0 < s ^ 2 := by positivity
    rw [m_H_eq isoChi hχ0 ht, m_gauss_identity ht]
  obtain ⟨hGI, -⟩ := m_min_int (zero_lt_one' ℝ)
  have hχG : ∀ s : ℝ, 0 < s → ∫ x, x / (x + s ^ 2) ∂isoChi ≤ min 1 (1 / s ^ 2) := by
    intro s hs
    rw [hχeq s hs]
    have hv : 0 < 1 / s ^ 2 := by positivity
    exact le_min (hΦ.2.2 _ hv).2.le (by linarith [(lem_app_iso_gaussian_iii _ hv).1])
  have key := m_half_diff (isoScaledImage (gin j * gout j) ((mo j).restrict (Ioi 0))) isoChi
    h0E hχ0 (fun s => min 1 (1 / s ^ 2)) hGI hχG hεpos ?_
  · rw [(isoChi_facts).2.2] at key
    exact key
  · intro s hs
    have ht : 0 < s ^ 2 := by positivity
    set H := 1 - s ^ 2 * isoNegStieltjes
      (isoScaledImage (gin j * gout j) ((mo j).restrict (Ioi 0))) (s ^ 2) with hHdef
    rw [hχeq s hs, m_H_eq _ h0E ht, ← hHdef]
    have hHb := m_H_bounds (hp j) h1 h2 ht hHdef
    have hcl := m_closure (hp j) h1 h2 ht hHdef
    have harg := m_phi_arg_bound h1.le h2.le ht hHb.1 hHb.2
    have hgi : 0 < gin j := by linarith
    have hgo : 0 < gout j := by linarith
    have hv : 0 < (gout j - H) * (gin j - H) / (gin j * gout j * s ^ 2) := by
      have : 0 < gout j - H := by linarith [hHb.2]
      have : 0 < gin j - H := by linarith [hHb.2]
      positivity
    have hle : (gout j - H) * (gin j - H) / (gin j * gout j * s ^ 2) ≤ 1 / s ^ 2 := by
      have := (abs_le.1 harg).2
      have e : (1 / gout j + 1 / gin j) / s ^ 2 ≥ 0 := by positivity
      -- use the exact form
      have key : (gout j - H) * (gin j - H) / (gin j * gout j * s ^ 2) - 1 / s ^ 2 =
          -(H * (gin j + gout j - H)) / (gin j * gout j * s ^ 2) := by
        field_simp
        ring
      have hn : 0 ≤ H * (gin j + gout j - H) := mul_nonneg hHb.1 (by linarith [hHb.2])
      have : -(H * (gin j + gout j - H)) / (gin j * gout j * s ^ 2) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      linarith
    have hinv : 0 < 1 / s ^ 2 := by positivity
    have hmono := hΦ.1.monotoneOn (mem_Ioi.2 hv) (mem_Ioi.2 hinv) hle
    have hlip := m_phi_lip hv hinv
    rw [hcl] at hlip hmono
    have hlt := (hΦ.2.2 _ hinv).2
    have hbd : |(gout j - H) * (gin j - H) / (gin j * gout j * s ^ 2) - 1 / s ^ 2| ≤
        (1 / gout j + 1 / gin j) / s ^ 2 := harg
    rw [abs_sub_comm] at hlip hbd
    have h3 : isoPhi (1 / s ^ 2) - H ≤ (1 / gout j + 1 / gin j) / s ^ 2 := by
      have := (abs_le.1 hlip).2
      have := le_abs_self (1 / s ^ 2 - (gout j - H) * (gin j - H) / (gin j * gout j * s ^ 2))
      linarith
    refine ⟨by linarith, le_min (by linarith [hHb.1]) ?_⟩
    have e : (1 / gout j + 1 / gin j) / s ^ 2 = (1 / gin j + 1 / gout j) / s ^ 2 := by ring
    rw [← e]
    exact h3

private theorem m_sqrt_restrict (b : ℝ) (hb : 0 < b) (m : Measure ℝ) :
    ∫ x, Real.sqrt x ∂(isoScaledImage b m) =
      ∫ x, Real.sqrt x ∂(isoScaledImage b (m.restrict (Ioi 0))) := by
  unfold isoScaledImage
  rw [integral_map (by fun_prop : Measurable fun l : ℝ => l / b).aemeasurable
      (by fun_prop : Measurable Real.sqrt).aestronglyMeasurable,
    integral_map (by fun_prop : Measurable fun l : ℝ => l / b).aemeasurable
      (by fun_prop : Measurable Real.sqrt).aestronglyMeasurable]
  have h : ∀ x : ℝ, x ∉ Ioi (0 : ℝ) → Real.sqrt (x / b) = 0 := by
    intro x hx
    apply Real.sqrt_eq_zero'.2
    apply div_nonpos_iff.2
    right
    exact ⟨not_lt.1 hx, hb.le⟩
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero h).symm

private theorem m_iii_pt {γin γout : ℝ} {mo mi : Measure ℝ}
    (hp : IsIsoMeasurePair γin γout mo mi) :
    Cbeta 0 γin γout = 1 / Real.sqrt (2 * (γin * γout)) *
      ∫ x, Real.sqrt x ∂(isoScaledImage (γin * γout) (mo.restrict (Ioi 0))) := by
  rw [(prop_app_iso_spectral_ii hp).2,
    m_sqrt_restrict _ (mul_pos hp.pos_in hp.pos_out) mo, mul_assoc]

private theorem m_sqrt_prod : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
  have hp0 := Real.pi_pos.ne'
  rw [← Real.sqrt_mul (by positivity)]
  rw [show Real.pi / 2 * (2 / Real.pi) = 1 by field_simp]
  simp

private theorem m_iii_lim {gin gout : ℕ → ℝ} {mo mi : ℕ → Measure ℝ}
    (hp : ∀ j, IsIsoMeasurePair (gin j) (gout j) (mo j) (mi j))
    (hin : Tendsto gin atTop atTop) (hout : Tendsto gout atTop atTop) :
    Tendsto (fun j => ∫ x, Real.sqrt x ∂(isoScaledImage (gin j * gout j) ((mo j).restrict (Ioi 0))))
      atTop (𝓝 (Real.sqrt (2 / Real.pi))) := by
  have h1 : Tendsto (fun j => 1 / gin j) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hin
  have h2 : Tendsto (fun j => 1 / gout j) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hout
  have h3 : Tendsto (fun j => Real.sqrt (1 / gin j + 1 / gout j)) atTop (𝓝 0) := by
    have h12 := h1.add h2
    rw [add_zero] at h12
    have := (Real.continuous_sqrt.tendsto 0).comp h12
    simpa [Function.comp_def] using this
  have hbd : Tendsto (fun j => 4 / Real.pi * Real.sqrt (1 / gin j + 1 / gout j)) atTop (𝓝 0) := by
    simpa using h3.const_mul (4 / Real.pi)
  have hlow := (tendsto_const_nhds (x := Real.sqrt (2 / Real.pi))).sub hbd
  rw [sub_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hin.eventually_gt_atTop 1, hout.eventually_gt_atTop 1] with j hj1 hj2
    have := (thm_app_iso_large_ii gin gout mo mi hp hin hout j hj1 hj2).2
    linarith
  · filter_upwards [hin.eventually_gt_atTop 1, hout.eventually_gt_atTop 1] with j hj1 hj2
    have := (thm_app_iso_large_ii gin gout mo mi hp hin hout j hj1 hj2).1
    linarith

theorem m_iii_parts12 (gin gout : ℕ → ℝ) (mo mi : ℕ → Measure ℝ)
    (hp : ∀ j, IsIsoMeasurePair (gin j) (gout j) (mo j) (mi j))
    (hin : Tendsto gin atTop atTop) (hout : Tendsto gout atTop atTop) :
    (∀ j : ℕ, 1 < gin j → 1 < gout j →
      Cbeta 0 (gin j) (gout j) =
        1 / Real.sqrt (2 * (gin j * gout j)) *
          ∫ x, Real.sqrt x ∂(isoScaledImage (gin j * gout j) ((mo j).restrict (Ioi 0)))) ∧
    Asymptotics.IsEquivalent atTop (fun j => Cbeta 0 (gin j) (gout j))
        (fun j => 1 / Real.sqrt (Real.pi * gin j * gout j)) := by
  refine ⟨fun j _ _ => m_iii_pt (hp j), ?_⟩
  · apply Asymptotics.isEquivalent_of_tendsto_one
    have key := (m_iii_lim hp hin hout).const_mul (Real.sqrt (Real.pi / 2))
    rw [m_sqrt_prod] at key
    refine key.congr' (Filter.Eventually.of_forall fun j => ?_)
    simp only [Pi.div_apply]
    rw [m_iii_pt (hp j)]
    have hb : 0 < gin j * gout j := mul_pos (hp j).pos_in (hp j).pos_out
    have hs : 0 < Real.sqrt (gin j * gout j) := Real.sqrt_pos.2 hb
    have e1 : Real.sqrt (Real.pi * gin j * gout j) =
        Real.sqrt Real.pi * Real.sqrt (gin j * gout j) := by
      rw [mul_assoc, Real.sqrt_mul Real.pi_pos.le]
    have e2 : Real.sqrt (2 * (gin j * gout j)) = Real.sqrt 2 * Real.sqrt (gin j * gout j) :=
      Real.sqrt_mul (by norm_num) _
    have e3 : Real.sqrt (Real.pi / 2) = Real.sqrt Real.pi / Real.sqrt 2 :=
      Real.sqrt_div Real.pi_pos.le 2
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hp' : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
    rw [e1, e2, e3]
    field_simp

/-- Pair-free helper (card §6.8): for `γin, γout > 1`, with `b = γin γout` and
`ε = 1/γin + 1/γout`, the scalar error bound `|√(2/π) − √(2b) C_0(γin,γout)| ≤ (4/π)√ε`
(the bound `eqn:app-iso-large-error` of `thm:app-iso-large` after `C = (2b)^{-1/2} ∫√x E_j`). 
Relocated here from `Muon.Isotropic.Aspect` by the coordinator (2026-10-24): its proof needs results of this
module, which imports the original one. -/
theorem C0_large_bound {γin γout : ℝ} (h1 : 1 < γin) (h2 : 1 < γout) :
    |Real.sqrt (2 / Real.pi) - Real.sqrt (2 * (γin * γout)) * Cbeta 0 γin γout| ≤
      4 / Real.pi * Real.sqrt (1 / γin + 1 / γout) := by
  have hi : 0 < γin := by linarith
  have ho : 0 < γout := by linarith
  have hb : 0 < γin * γout := mul_pos hi ho
  have he : 0 < 1 / γin + 1 / γout := by positivity
  have hbe : 0 < γin * γout * (1 / γin + 1 / γout) := mul_pos hb he
  have hpoint : ∀ u : ℝ, 0 < u →
      0 ≤ isoPhi (γin * γout / u ^ 2) - isoGb 0 γin γout (u ^ 2) ∧
      isoPhi (γin * γout / u ^ 2) - isoGb 0 γin γout (u ^ 2) ≤
        min 1 (γin * γout * (1 / γin + 1 / γout) / u ^ 2) := by
    intro u hu
    have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
    set q := qIso 0 γin γout (u ^ 2) with hqdef
    set H := isoGb 0 γin γout (u ^ 2) with hHdef
    have hr := (lem_app_iso_comparison_i m_link0 hi ho).2.2.2.1 (u ^ 2) hu2
    have hr' : q ∈ isoDr (Muon.DetEquiv.rW (Muon.emaW 0)) γin γout ∧
        isoG (Muon.DetEquiv.rW (Muon.emaW 0)) γin γout (u ^ 2) q = 0 := by
      simpa [q, qIso] using hr
    have hq0 : 0 ≤ q := hr'.1.1
    have hrq : Muon.DetEquiv.rW (Muon.emaW 0) q = H := by
      rw [hHdef, m_isoGb0]
      simp only [psiIso, qIso, hqdef]
    have hHphi : H = isoPhi q := by rw [← hrq, m_rW0 hq0]
    have hroot : u ^ 2 * q = (γout - H) * (γin - H) := by
      unfold isoG at hr'
      rw [hrq] at hr'
      linarith [hr'.2]
    have hHlt : H < min γin γout := by rw [← hrq]; exact hr'.1.2
    have hqpos : 0 < q := by
      have hgo : 0 < γout - H := by linarith [min_le_right γin γout]
      have hgi : 0 < γin - H := by linarith [min_le_left γin γout]
      nlinarith [mul_pos hgo hgi]
    have hHb := (lem_app_iso_gaussian_ii.2.2 q hqpos)
    have hH0 : 0 ≤ H := by rw [hHphi]; exact hHb.1.le
    have hH1 : H ≤ 1 := by rw [hHphi]; exact hHb.2.le
    have hqeq : q = (γout - H) * (γin - H) / u ^ 2 := by
      rw [eq_div_iff hu2.ne']
      simpa [mul_comm] using hroot
    have hqle : q ≤ γin * γout / u ^ 2 := by
      rw [hqeq]
      apply div_le_div_of_nonneg_right _ hu2.le
      nlinarith [mul_nonneg hH0 (by linarith : 0 ≤ γin + γout - H)]
    have href : 0 < γin * γout / u ^ 2 := div_pos hb hu2
    have hmono := lem_app_iso_gaussian_ii.1.monotoneOn
      (Set.mem_Ioi.2 hqpos) (Set.mem_Ioi.2 href) hqle
    have harg0 := m_phi_arg_bound h1.le h2.le (div_pos hu2 hb) hH0 hH1
    have harg : |q - γin * γout / u ^ 2| ≤
        γin * γout * (1 / γin + 1 / γout) / u ^ 2 := by
      rw [hqeq]
      convert harg0 using 1 <;> field_simp <;> ring
    have hlip := m_phi_lip href hqpos
    rw [abs_sub_comm (γin * γout / u ^ 2) q] at hlip
    have hdiff0 : 0 ≤ isoPhi (γin * γout / u ^ 2) - H := by
      rw [hHphi]
      exact sub_nonneg.mpr hmono
    have hdiffarg : isoPhi (γin * γout / u ^ 2) - H ≤
        γin * γout * (1 / γin + 1 / γout) / u ^ 2 := by
      rw [hHphi]
      have hdiff0' : 0 ≤ isoPhi (γin * γout / u ^ 2) - isoPhi q := by
        rw [← hHphi]
        exact hdiff0
      have habs : |isoPhi (γin * γout / u ^ 2) - isoPhi q| =
          isoPhi (γin * γout / u ^ 2) - isoPhi q := abs_of_nonneg hdiff0'
      rw [habs] at hlip
      exact hlip.trans harg
    rw [hHdef] at hdiff0 ⊢
    refine ⟨hdiff0, le_min ?_ hdiffarg⟩
    have hrefle := (lem_app_iso_gaussian_ii.2.2 _ href).2.le
    linarith
  have hminB := m_min_int hb
  have hPhiI : IntegrableOn (fun u : ℝ => isoPhi (γin * γout / u ^ 2)) (Ioi 0) := by
    have hc : ContinuousOn (fun u : ℝ => isoPhi (γin * γout / u ^ 2)) (Ioi 0) := by
      have hphi : ContinuousOn isoPhi (Ioi 0) := fun v hv =>
        (lem_app_iso_gaussian_ii.2.1 v hv).1.continuousAt.continuousWithinAt
      have hin : ContinuousOn (fun u : ℝ => γin * γout / u ^ 2) (Ioi 0) := by
        intro u hu
        exact (continuousAt_const.div₀ (continuousAt_id.pow 2)
          (pow_ne_zero 2 (ne_of_gt hu))).continuousWithinAt
      exact hphi.comp hin (fun u hu => Set.mem_Ioi.2 (div_pos hb (sq_pos_of_pos hu)))
    refine Integrable.mono' hminB.1 (hc.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hv : 0 < γin * γout / u ^ 2 := div_pos hb (sq_pos_of_pos hu)
    have hp := lem_app_iso_gaussian_ii.2.2 _ hv
    rw [Real.norm_eq_abs, abs_of_pos hp.1]
    exact le_min hp.2.le (by linarith [(lem_app_iso_gaussian_iii _ hv).1])
  have hPsiI : IntegrableOn (fun u : ℝ => isoGb 0 γin γout (u ^ 2)) (Ioi 0) :=
    (prop_app_iso_zero_i (β := 0) le_rfl zero_lt_one hi ho).2.1
  have hminE := m_min_int hbe
  have hdiffI : IntegrableOn
      (fun u : ℝ => isoPhi (γin * γout / u ^ 2) - isoGb 0 γin γout (u ^ 2)) (Ioi 0) :=
    hPhiI.sub hPsiI
  have hdiff_nonneg : 0 ≤ ∫ u in Ioi (0 : ℝ),
      (isoPhi (γin * γout / u ^ 2) - isoGb 0 γin γout (u ^ 2)) := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro u hu
    exact (hpoint u hu).1
  have hdiff_le : (∫ u in Ioi (0 : ℝ),
      (isoPhi (γin * γout / u ^ 2) - isoGb 0 γin γout (u ^ 2))) ≤
      2 * Real.sqrt (γin * γout * (1 / γin + 1 / γout)) := by
    rw [← hminE.2]
    exact setIntegral_mono_on hdiffI hminE.1 measurableSet_Ioi
      (fun u hu => (hpoint u hu).2)
  haveI : IsProbabilityMeasure isoChi := by
    unfold isoChi
    exact (Measure.isProbabilityMeasure_map_iff
      (by fun_prop : Measurable fun g : ℝ => g ^ 2).aemeasurable).2 inferInstance
  have hchi0 : isoChi (Iio 0) = 0 := by
    unfold isoChi
    rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
    have hpre : (fun g : ℝ => g ^ 2) ⁻¹' Iio 0 = ∅ := by
      ext g
      simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
      exact sq_nonneg g
    rw [hpre, measure_empty]
  have hchi : ∀ u : ℝ, 0 < u →
      ∫ x, x / (x + u ^ 2) ∂isoChi = isoPhi (1 / u ^ 2) := by
    intro u hu
    have hu2 : 0 < u ^ 2 := by positivity
    rw [m_H_eq isoChi hchi0 hu2, m_gauss_identity hu2]
  obtain ⟨hmin1, -⟩ := m_min_int (zero_lt_one' ℝ)
  have hchiG : ∀ u : ℝ, 0 < u →
      ∫ x, x / (x + u ^ 2) ∂isoChi ≤ min 1 (1 / u ^ 2) := by
    intro u hu
    rw [hchi u hu]
    have hv : 0 < 1 / u ^ 2 := by positivity
    exact le_min (lem_app_iso_gaussian_ii.2.2 _ hv).2.le
      (by linarith [(lem_app_iso_gaussian_iii _ hv).1])
  have hbase := (m_half_moment isoChi hchi0 (fun u => min 1 (1 / u ^ 2)) hmin1 hchiG).2
  rw [(isoChi_facts).2.2] at hbase
  have hsqrtb : 0 < Real.sqrt (γin * γout) := Real.sqrt_pos.2 hb
  have hscale := integral_comp_mul_left_Ioi
    (fun u : ℝ => isoPhi (1 / u ^ 2)) 0 (inv_pos.2 hsqrtb)
  have hscale' : ∫ u in Ioi (0 : ℝ), isoPhi (γin * γout / u ^ 2) =
      Real.sqrt (γin * γout) * ∫ u in Ioi (0 : ℝ), isoPhi (1 / u ^ 2) := by
    rw [mul_zero, smul_eq_mul] at hscale
    have hsqb : Real.sqrt (γin * γout) ^ 2 = γin * γout := Real.sq_sqrt hb.le
    convert hscale using 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      congr 1
      field_simp
      rw [hsqb]
    · rw [inv_inv]
  have hC : Real.sqrt (2 * (γin * γout)) * Cbeta 0 γin γout =
      2 / (Real.pi * Real.sqrt (γin * γout)) *
        ∫ u in Ioi (0 : ℝ), isoGb 0 γin γout (u ^ 2) := by
    unfold Cbeta
    have hs2 : Real.sqrt (2 * (γin * γout)) = Real.sqrt 2 * Real.sqrt (γin * γout) :=
      Real.sqrt_mul (by norm_num) _
    rw [hs2]
    have hs2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hsqb : Real.sqrt (γin * γout) ^ 2 = γin * γout := Real.sq_sqrt hb.le
    calc
      Real.sqrt 2 * Real.sqrt (γin * γout) *
            (Real.sqrt 2 / (Real.pi * γin * γout) *
              ∫ u in Ioi (0 : ℝ), isoGb 0 γin γout (u ^ 2)) =
          (2 * Real.sqrt (γin * γout)) / (Real.pi * (γin * γout)) *
            ∫ u in Ioi (0 : ℝ), isoGb 0 γin γout (u ^ 2) := by
        ring_nf
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      _ = 2 / (Real.pi * Real.sqrt (γin * γout)) *
            ∫ u in Ioi (0 : ℝ), isoGb 0 γin γout (u ^ 2) := by
        congr 1
        field_simp
        nlinarith [hsqb]
  have hbase' : Real.sqrt (2 / Real.pi) =
      2 / Real.pi * ∫ u in Ioi (0 : ℝ), isoPhi (1 / u ^ 2) := by
    calc
      Real.sqrt (2 / Real.pi) =
          2 / Real.pi * ∫ u in Ioi (0 : ℝ), ∫ x, x / (x + u ^ 2) ∂isoChi := hbase
      _ = 2 / Real.pi * ∫ u in Ioi (0 : ℝ), isoPhi (1 / u ^ 2) := by
        congr 1
        exact setIntegral_congr_fun measurableSet_Ioi (fun u hu => hchi u hu)
  have hPhi : Real.sqrt (2 / Real.pi) =
      2 / (Real.pi * Real.sqrt (γin * γout)) *
        ∫ u in Ioi (0 : ℝ), isoPhi (γin * γout / u ^ 2) := by
    rw [hscale', hbase']
    field_simp
  rw [hPhi, hC, ← mul_sub, ← integral_sub hPhiI hPsiI, abs_of_nonneg
    (mul_nonneg (by positivity) hdiff_nonneg)]
  calc
    2 / (Real.pi * Real.sqrt (γin * γout)) *
          ∫ u in Ioi (0 : ℝ),
            (isoPhi (γin * γout / u ^ 2) - isoGb 0 γin γout (u ^ 2))
        ≤ 2 / (Real.pi * Real.sqrt (γin * γout)) *
            (2 * Real.sqrt (γin * γout * (1 / γin + 1 / γout))) :=
      mul_le_mul_of_nonneg_left hdiff_le (by positivity)
    _ = 4 / Real.pi * Real.sqrt (1 / γin + 1 / γout) := by
      rw [Real.sqrt_mul hb.le]
      field_simp
      ring

end Muon.Isotropic

end

import MatrixConcentration
import Muon.Dynamics.Freezing
import Muon.Dynamics.Transport
import Muon.External.Certificates

set_option linter.style.longLine false

/-!
# Appendix E, work package L-E.11: persistence of diffuseness

Snapshot `cr-2026-10-23`. Source: `sections/05-dynamics/section.tex`, subsection "Persistence of diffuseness":
`lem:app-dyn-matrix-martingale` (ll. 2025–2033) and `lem:app-dyn-diffuse` (ll. 2057–2063). Card:
`sections/05-dynamics/CARD.md` §2, §3, §4, §5 (L-E.11). Interface draft: every proof is `sorry`.

Representation choices:
* Matrix martingale. The source's `Z_b` are random selfadjoint `d × d` real matrices with filtration `ℱ b`
  (the past at block `b`). "Determined by the past at block `b+1`" is `Measurable[ℱ (b+1)]` of every entry;
  "conditional mean zero given the past at block `b`" is `condExp` of every entry (entrywise, since the
  matrix conditional expectation is entrywise). `‖·‖` is `opNorm`. The bound `‖Z_b‖ ≤ c` holds everywhere.
  Integrability of the entries is a conclusion conjunct.
* Diffuseness. The actual process is the one of `Muon.Dynamics.DynSetup` (Transport, bridge
  `DynHyp.exists_dynSetup`), not a new sample model. Dimensions are a sequence `k`; each dimension carries its
  own sample space `Ω k` and probability `P k`, so that "in probability" is read as the convergence
  of `P k` of the event, which is the form the bridge produces.
* Standing hypotheses: (H1) is `regime : ProportionalRegime` (converging aspect ratios, bounded covariances)
  together with the per-dimension `DynSetup` fields (size, whitened i.i.d. Gaussian samples, independence);
  (H2) and (H4) are `DynSetup` fields; (H3) is `W0_hat` (`‖Â₀‖ → 0`), the only diffuseness assumed (as the source
  says). `T > 0` is fixed and `ε > 0` is arbitrary.
* The exit index `t_{b_c}` is `L · b_c` with `b_c` the first block start outside `𝒜` (`admA`), in `ℕ∞`
  (`⊤` if there is none). The max over `t ≤ t_{b_c} ∧ TB` is written as the existence of such `t` with
  `δ(Δ_t) > ε`; this is the same event because the index set is finite.
* The event is taken with the outer measure `P k` (no measurability conjunct); see open questions.
* Constants: none in this statement (the source's convergence has none).
-/

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open Muon Muon.Setup

universe u

noncomputable section

namespace Muon.Dynamics

/-! ## Matrix martingale inequality -/

private lemma mm_abs_entry_le_opNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d) : |A i j| ≤ opNorm A := by
  have h₁ := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℝ))
  have h₂ := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin d) ℝ).symm
    (A *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i
  have h₃ : ((EuclideanSpace.equiv (Fin d) ℝ).symm
      (A *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i = A i j := by
    simp
  simp only [PiLp.norm_single, norm_one, mul_one] at h₁
  rw [h₃, Real.norm_eq_abs] at h₂
  rw [opNorm_eq_norm]
  linarith

private lemma mm_entries_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ)
    (ℱ : ℕ → MeasurableSpace Ω) (hle : ∀ b, ℱ b ≤ mΩ)
    (Z : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hmeas : ∀ b i j, Measurable[ℱ (b + 1)] (fun ω => Z b ω i j))
    (c : ℝ) (hbd : ∀ b ω, opNorm (Z b ω) ≤ c) :
    ∀ b i j, Integrable (fun ω => Z b ω i j) P := by
  intro b i j
  refine Integrable.mono' (integrable_const c)
    ((hmeas b i j).mono (hle (b + 1)) le_rfl).aestronglyMeasurable ?_
  exact ae_of_all P fun ω => by
    rw [Real.norm_eq_abs]
    exact (mm_abs_entry_le_opNorm (Z b ω) i j).trans (hbd b ω)

private lemma mm_partial_sum_measurable {Ω : Type*}
    (d : ℕ) (ℱ : ℕ → MeasurableSpace Ω) (hmono : Monotone ℱ)
    (Z : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hmeas : ∀ b i j, Measurable[ℱ (b + 1)] (fun ω => Z b ω i j))
    (j : ℕ) : Measurable[ℱ j] (fun ω => ∑ b ∈ Finset.range j, Z b ω) := by
  let : MeasurableSpace Ω := ℱ j
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro k
  simpa only [Matrix.sum_apply] using Finset.measurable_sum (Finset.range j) (fun b hb =>
    (hmeas b i k).mono (hmono (Nat.succ_le_of_lt (Finset.mem_range.mp hb))) le_rfl)

private lemma mm_entries_integral_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ)
    (ℱ : ℕ → MeasurableSpace Ω) (hle : ∀ b, ℱ b ≤ mΩ)
    (Z : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hmean : ∀ b i j, MeasureTheory.condExp (ℱ b) P (fun ω => Z b ω i j) =ᵐ[P] 0) :
    ∀ b i j, (∫ ω, Z b ω i j ∂P) = 0 := by
  intro b i j
  rw [← integral_condExp (hle b)]
  exact (integral_congr_ae (hmean b i j)).trans (by simp)

private lemma mm_partial_sum_isHermitian {Ω : Type*} (d : ℕ)
    (Z : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsa : ∀ b ω, (Z b ω).IsHermitian) (j : ℕ) (ω : Ω) :
    (∑ b ∈ Finset.range j, Z b ω).IsHermitian := by
  exact (isSelfAdjoint_sum _ fun b _ => (hsa b ω).isSelfAdjoint).isHermitian

open scoped Matrix.Norms.L2Operator in
private lemma mm_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (Z : Ω → Matrix (Fin d) (Fin d) ℝ) (hmeas : Measurable Z)
    (hsa : ∀ ω, (Z ω).IsHermitian) (c : ℝ) (hbd : ∀ ω, opNorm (Z ω) ≤ c)
    (u : ℝ) : Integrable (fun ω => NormedSpace.exp (u • Z ω)) P := by
  by_cases hd : d = 0
  · subst d
    have heq : (fun ω => NormedSpace.exp (u • Z ω)) = 0 := by
      funext ω
      ext i
      exact Fin.elim0 i
    rw [heq]
    exact integrable_zero _ _ _
  have : NeZero d := ⟨hd⟩
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℝ) :=
    .restrictScalars ℚ ℝ (Matrix (Fin d) (Fin d) ℝ)
  refine Integrable.mono' (integrable_const (Real.exp (|u| * c)))
    (NormedSpace.exp_continuous.measurable.comp
      (hmeas.const_smul u)).aestronglyMeasurable ?_
  refine ae_of_all P fun ω => ?_
  rw [← CFC.real_exp_eq_normedSpace_exp ((hsa ω).smul (IsSelfAdjoint.all u)).isSelfAdjoint,
    ← cfc_comp_const_mul u Real.exp (Z ω) (ha := (hsa ω).isSelfAdjoint)]
  apply norm_cfc_le (Real.exp_nonneg _)
  intro y hy
  have hybd : |y| ≤ opNorm (Z ω) := by
    simpa only [Real.norm_eq_abs, ← opNorm_eq_norm] using spectrum.norm_le_norm_of_mem hy
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    u * y ≤ |u * y| := le_abs_self _
    _ = |u| * |y| := abs_mul _ _
    _ ≤ |u| * c := mul_le_mul_of_nonneg_left (hybd.trans (hbd ω)) (abs_nonneg _)

open scoped Matrix.Norms.L2Operator in
private lemma mm_partial_sum_norm_le {Ω : Type*} {d : ℕ}
    (Z : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (hbd : ∀ b ω, opNorm (Z b ω) ≤ c) (j : ℕ) (ω : Ω) :
    opNorm (∑ b ∈ Finset.range j, Z b ω) ≤ (j : ℝ) * c := by
  rw [opNorm_eq_norm]
  calc
    ‖∑ b ∈ Finset.range j, Z b ω‖ ≤ ∑ b ∈ Finset.range j, ‖Z b ω‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ Finset.range j, c := Finset.sum_le_sum fun b _ =>
      (opNorm_eq_norm (Z b ω)) ▸ hbd b ω
    _ = (j : ℝ) * c := by simp

open scoped Matrix.Norms.L2Operator in
private lemma mm_trace_mgf {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ) (ℱ : ℕ → MeasurableSpace Ω) (hmono : Monotone ℱ) (hle : ∀ b, ℱ b ≤ mΩ)
    (Z : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (hsa : ∀ b ω, (Z b ω).IsHermitian)
    (hmeas : ∀ b i j, Measurable[ℱ (b + 1)] (fun ω => Z b ω i j))
    (hmean : ∀ b i j, MeasureTheory.condExp (ℱ b) P (fun ω => Z b ω i j) =ᵐ[P] 0)
    {c : ℝ} (hc : 0 < c) (hbd : ∀ b ω, opNorm (Z b ω) ≤ c) (j : ℕ) (u : ℝ) :
    (∫ ω, Matrix.trace (NormedSpace.exp (u • ∑ b ∈ Finset.range j, Z b ω)) ∂P) ≤
      (d : ℝ) * Real.exp ((j : ℝ) * u ^ 2 * c ^ 2 / 2) := by
  exact MatrixConcentration.matrixMartingale_trace_mgf P d ℱ hmono hle Z hsa hmeas hmean
    hc hbd j u

open scoped Matrix.Norms.L2Operator in
private lemma mm_trace_exp_eq_sum {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (u : ℝ) :
    Matrix.trace (NormedSpace.exp (u • A)) = ∑ i, Real.exp (u * hA.eigenvalues i) := by
  rw [← CFC.real_exp_eq_normedSpace_exp (hA.smul (IsSelfAdjoint.all u)).isSelfAdjoint,
    ← cfc_comp_const_mul u Real.exp A (ha := hA.isSelfAdjoint), hA.cfc_eq,
    Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp

open scoped Matrix.Norms.L2Operator in
private lemma mm_exp_spectral_le_trace {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (u t : ℝ) (ht : t ∈ spectrum ℝ A) :
    Real.exp (u * t) ≤ Matrix.trace (NormedSpace.exp (u • A)) := by
  rw [hA.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  rw [mm_trace_exp_eq_sum A hA u]
  exact Finset.single_le_sum (fun k _ => Real.exp_nonneg (u * hA.eigenvalues k)) (Finset.mem_univ i)

open scoped Matrix.Norms.L2Operator in
private lemma mm_norm_event_trace {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) {x u : ℝ} (hx : 0 < x) (hu : 0 < u)
    (hAx : x ≤ opNorm A) :
    Real.exp (u * x) ≤ Matrix.trace (NormedSpace.exp (u • A)) +
      Matrix.trace (NormedSpace.exp ((-u) • A)) := by
  by_cases hd : d = 0
  · subst d
    have hz : A = 0 := by ext i; exact Fin.elim0 i
    rw [hz, opNorm_eq_norm, norm_zero] at hAx
    exact False.elim ((not_le_of_gt hx) hAx)
  have : NeZero d := ⟨hd⟩
  have hp (v : ℝ) : 0 ≤ Matrix.trace (NormedSpace.exp (v • A)) :=
    ((hA.smul (IsSelfAdjoint.all v)).isSelfAdjoint.exp_nonneg).posSemidef.trace_nonneg
  have he : Real.exp (u * x) ≤ Real.exp (u * opNorm A) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hAx hu.le)
  have hspec : opNorm A ∈ spectrum ℝ A ∨ -opNorm A ∈ spectrum ℝ A := by
    obtain ⟨⟨t, ht, heq⟩, _⟩ :=
      IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) A hA.isSelfAdjoint
    change ‖t‖ = ‖A‖ at heq
    rw [Real.norm_eq_abs, ← opNorm_eq_norm] at heq
    rcases le_total 0 t with htpos | htneg
    · left
      rw [← heq, abs_of_nonneg htpos]
      exact ht
    · right
      rw [← heq, abs_of_nonpos htneg, neg_neg]
      exact ht
  rcases hspec with h | h
  · exact he.trans ((mm_exp_spectral_le_trace A hA u _
      (by simpa only [opNorm_eq_norm] using h)).trans (le_add_of_nonneg_right (hp (-u))))
  · have hn := mm_exp_spectral_le_trace A hA (-u) (-opNorm A)
      (by simpa only [opNorm_eq_norm] using h)
    have hh : Real.exp (u * opNorm A) ≤ Matrix.trace (NormedSpace.exp ((-u) • A)) := by
      simpa only [neg_mul_neg] using hn
    exact he.trans (hh.trans (le_add_of_nonneg_left (hp u)))

open scoped Matrix.Norms.L2Operator in
private lemma mm_fixed_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ) (ℱ : ℕ → MeasurableSpace Ω) (hmono : Monotone ℱ) (hle : ∀ b, ℱ b ≤ mΩ)
    (Z : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (hsa : ∀ b ω, (Z b ω).IsHermitian)
    (hmeas : ∀ b i j, Measurable[ℱ (b + 1)] (fun ω => Z b ω i j))
    (hmean : ∀ b i j, MeasureTheory.condExp (ℱ b) P (fun ω => Z b ω i j) =ᵐ[P] 0)
    {c : ℝ} (hc : 0 < c) (hbd : ∀ b ω, opNorm (Z b ω) ≤ c)
    (j : ℕ) (x u : ℝ) (hx : 0 < x) (hu : 0 < u) :
    P {ω | x ≤ opNorm (∑ b ∈ Finset.range j, Z b ω)} ≤
      ENNReal.ofReal (2 * (d : ℝ) * Real.exp (-u * x + (j : ℝ) * u ^ 2 * c ^ 2 / 2)) := by
  let S := fun ω => ∑ b ∈ Finset.range j, Z b ω
  let T := (Matrix.traceLinearMap (Fin d) ℝ ℝ).toContinuousLinearMap
  have hm : Measurable S :=
    (mm_partial_sum_measurable d ℱ hmono Z hmeas j).mono (hle j) le_rfl
  have hi (v : ℝ) := T.integrable_comp (mm_exp_integrable P S hm
    (mm_partial_sum_isHermitian d Z hsa j) ((j : ℝ) * c)
    (mm_partial_sum_norm_le Z c hbd j) v)
  have hp (v : ℝ) (ω : Ω) : 0 ≤ Matrix.trace (NormedSpace.exp (v • S ω)) :=
    (((mm_partial_sum_isHermitian d Z hsa j ω).smul
      (IsSelfAdjoint.all v)).isSelfAdjoint.exp_nonneg).posSemidef.trace_nonneg
  have hMarkov := ((hi u).add (hi (-u))).const_mul (Real.exp (-u * x))
  have hb := hMarkov.measure_le_integral
    (ae_of_all P fun ω => mul_nonneg (Real.exp_nonneg _) (add_nonneg (hp u ω) (hp (-u) ω)))
    (s := {ω | x ≤ opNorm (S ω)}) (fun ω hω => by
      have h := mm_norm_event_trace (S ω) (mm_partial_sum_isHermitian d Z hsa j ω) hx hu hω
      have he : Real.exp (-u * x) * Real.exp (u * x) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      rw [← he]
      exact mul_le_mul_of_nonneg_left h (Real.exp_nonneg _))
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [Pi.add_apply] at *
  rw [integral_const_mul, integral_add (hi u) (hi (-u))]
  have h₁ := mm_trace_mgf P d ℱ hmono hle Z hsa hmeas hmean hc hbd j u
  have h₂ := mm_trace_mgf P d ℱ hmono hle Z hsa hmeas hmean hc hbd j (-u)
  simp only [neg_sq] at h₂
  calc
    _ ≤ Real.exp (-u * x) * ((d : ℝ) * Real.exp ((j : ℝ) * u ^ 2 * c ^ 2 / 2) +
        (d : ℝ) * Real.exp ((j : ℝ) * u ^ 2 * c ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (Real.exp_nonneg _)
    _ = _ := by rw [Real.exp_add]; ring

/-- `lem:app-dyn-matrix-martingale`, snapshot `cr-2026-10-23`. Generic Hermitian matrix martingale
inequality for `d × d` selfadjoint blocks with a filtration `ℱ`. Source, `section.tex` ll. 2025–2033,
verbatim:
```latex
\begin{lemma}[Matrix martingale]\label{lem:app-dyn-matrix-martingale}
Let $Z_0,Z_1,\dots$ be random selfadjoint $d\times d$ matrices such that
$Z_b$ is determined by the past at block $b+1$, has conditional mean zero
given the past at block $b$, and satisfies $\norm{Z_b}\le c$. Then for $x>0$
and every integer $N\ge1$,
\[
\Pr\Big(\max_{j\le N}\Big\|\sum_{b<j}Z_b\Big\|\ge x\Big)\le2dN\exp\Big(-\frac{x^2}{2Nc^2}\Big).
\]
\end{lemma}
```
Encoding: `ℱ b` is the past at block `b`; `Z b` is `ℱ (b+1)`-measurable, its entries have conditional
mean zero given `ℱ b`, and `‖Z b ω‖ ≤ c` for every `ω`. The conclusion carries the integrability of the
entries (a conjunct) and the tail bound for the event `max_{j ≤ N} ‖∑_{b<j} Z_b‖ ≥ x`.
No constraint on `c` is stated in the source, and at `c = 0` Lean's `x²/0 = 0` makes the bound `2dN ≥ 1`, which is trivially true. -/
theorem lem_app_dyn_matrix_martingale {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    -- the dimension `d` and the filtration `ℱ` (the past at block `b`)
    (d : ℕ) (ℱ : ℕ → MeasurableSpace Ω) (hmono : Monotone ℱ) (hle : ∀ b, ℱ b ≤ mΩ)
    -- the increments `Z_b`
    (Z : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (hsa : ∀ b ω, (Z b ω).IsHermitian)
    -- `Z_b` is determined by the past at block `b+1`
    (hmeas : ∀ b i j, Measurable[ℱ (b + 1)] (fun ω => Z b ω i j))
    -- conditional mean zero given the past at block `b` (entrywise)
    (hmean : ∀ b i j, MeasureTheory.condExp (ℱ b) P (fun ω => Z b ω i j) =ᵐ[P] 0)
    -- the bound `‖Z_b‖ ≤ c`
    (c : ℝ) (hbd : ∀ b ω, opNorm (Z b ω) ≤ c)
    -- `x > 0` and `N ≥ 1`
    (x : ℝ) (hx : 0 < x) (N : ℕ) (hN : 1 ≤ N) :
    (∀ b i j, Integrable (fun ω => Z b ω i j) P) ∧
    P {ω | ∃ j ≤ N, x ≤ opNorm (∑ b ∈ Finset.range j, Z b ω)} ≤
      ENNReal.ofReal (2 * (d : ℝ) * (N : ℝ) * Real.exp (-(x ^ 2) / (2 * (N : ℝ) * c ^ 2))) := by
  refine ⟨mm_entries_integrable P d ℱ hle Z hmeas c hbd, ?_⟩
  by_cases hc : c ≤ 0
  · have hempty : {ω | ∃ j ≤ N, x ≤ opNorm (∑ b ∈ Finset.range j, Z b ω)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨j, _, hj⟩
      have hzero : opNorm (∑ b ∈ Finset.range j, Z b ω) ≤ 0 :=
        (mm_partial_sum_norm_le Z c hbd j ω).trans
          (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg j) hc)
      exact (not_le_of_gt hx) (hj.trans hzero)
    rw [hempty, measure_empty]
    exact bot_le
  have hcpos : 0 < c := lt_of_not_ge hc
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  let u : ℝ := x / ((N : ℝ) * c ^ 2)
  have hu : 0 < u := div_pos hx (mul_pos hNpos (sq_pos_of_pos hcpos))
  have hopt : ∀ j ≤ N,
      -u * x + (j : ℝ) * u ^ 2 * c ^ 2 / 2 ≤
        -u * x + (N : ℝ) * u ^ 2 * c ^ 2 / 2 := by
    intro j hj
    gcongr
  have hcalc : -u * x + (N : ℝ) * u ^ 2 * c ^ 2 / 2 =
      -(x ^ 2) / (2 * (N : ℝ) * c ^ 2) := by
    dsimp [u]
    field_simp
    ring
  have htail : ∀ j ≤ N,
      P {ω | x ≤ opNorm (∑ b ∈ Finset.range j, Z b ω)} ≤
        ENNReal.ofReal (2 * (d : ℝ) *
          Real.exp (-(x ^ 2) / (2 * (N : ℝ) * c ^ 2))) := by
    intro j hj
    refine (mm_fixed_tail P d ℱ hmono hle Z hsa hmeas hmean hcpos hbd j x u hx hu).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    rw [← hcalc]
    exact hopt j hj
  have hsub : {ω | ∃ j ≤ N, x ≤ opNorm (∑ b ∈ Finset.range j, Z b ω)} ⊆
      ⋃ j ∈ Finset.range N, {ω | x ≤ opNorm (∑ b ∈ Finset.range (j + 1), Z b ω)} := by
    rintro ω ⟨j, hjN, hj⟩
    cases j with
    | zero =>
      have hzero : opNorm (∑ b ∈ Finset.range 0, Z b ω) ≤ 0 := by
        simpa only [Nat.cast_zero, zero_mul] using mm_partial_sum_norm_le Z c hbd 0 ω
      exact False.elim ((not_le_of_gt hx) (hj.trans hzero))
    | succ j =>
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), hj⟩⟩
  calc
    _ ≤ P (⋃ j ∈ Finset.range N,
        {ω | x ≤ opNorm (∑ b ∈ Finset.range (j + 1), Z b ω)}) := measure_mono hsub
    _ ≤ ∑ j ∈ Finset.range N,
        P {ω | x ≤ opNorm (∑ b ∈ Finset.range (j + 1), Z b ω)} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range N, ENNReal.ofReal (2 * (d : ℝ) *
        Real.exp (-(x ^ 2) / (2 * (N : ℝ) * c ^ 2))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact htail (j + 1) (by have := Finset.mem_range.mp hj; omega)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
      congr 1
      ring

/-! ## Persistence of diffuseness -/

/-- The block index `b_c = inf {b ≥ 0 : Δ_{t_b} ∉ 𝒜}` of `lem:app-dyn-diffuse`, with `t_b = bL`, valued in
`ℕ∞` (`⊤` when the process never leaves `𝒜` at block starts). `𝒜 = admA p C` (section.tex ll. 1487–1490, unlabelled). -/
def dynBlockIndexExit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}
    (S : DynSetup p P m n B) : Ω → ℕ∞ :=
  fun ω => ⨅ (b : ℕ) (_ : dynDelta S (b * blockLen B) ω ∉ admA p S.C), (b : ℕ∞)

/-- The exit time `t_{b_c} = L · b_c` of `lem:app-dyn-diffuse`, with `L = blockLen B` (`eqn:app-dyn-L`). -/
def dynBlockExitTime {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}
    (S : DynSetup p P m n B) : Ω → ℕ∞ :=
  fun ω => (blockLen B : ℕ∞) * dynBlockIndexExit S ω

private lemma diffuse_past_le {p : DynParams} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) : dynPast S t ≤ mΩ := by
  refine sup_le (iSup_le fun s => iSup_le fun _ => iSup_le fun a => ?_) S.M0_meas.comap_le
  exact (S.cs.meas_act s a).comap_le

private lemma diffuse_past_mono {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) {s t : ℕ} (h : s ≤ t) :
    dynPast S s ≤ dynPast S t := by
  refine sup_le_sup_right (iSup_le fun u => iSup_le fun hu => iSup_le fun a => ?_) _
  exact le_iSup₂_of_le u ⟨hu.1, hu.2.trans (by exact_mod_cast h)⟩ (le_iSup_of_le a le_rfl)

private lemma diffuse_mat_meas {Ω : Type*} {σ : MeasurableSpace Ω} {m n : ℕ}
    {F : Ω → Mat m n} (h : ∀ i j, Measurable[σ] fun ω => F ω i j) : Measurable[σ] F :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => h i j

private lemma diffuse_entry_meas {Ω : Type*} {σ : MeasurableSpace Ω} {m n : ℕ}
    {F : Ω → Mat m n} (hF : Measurable[σ] F) (i : Fin m) (j : Fin n) :
    Measurable[σ] fun ω => F ω i j :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hF)

private lemma diffuse_grad_meas {Ω : Type*} {σ : MeasurableSpace Ω} {B m n : ℕ}
    {D : Ω → Mat m n} {b : Ω → Batch m n B} (hD : Measurable[σ] D)
    (hb : Measurable[σ] b) : Measurable[σ] (fun ω => grad (D ω) (b ω)) := by
  have hc : Continuous (fun q : Mat m n × Batch m n B => grad q.1 q.2) := by
    unfold grad resid outer
    fun_prop
  exact Measurable.comp (g := fun q : Mat m n × Batch m n B => grad q.1 q.2)
    (f := fun ω => (D ω, b ω)) hc.measurable (hD.prodMk hb)

private lemma diffuse_step_meas {Ω : Type*} {σ : MeasurableSpace Ω} {B m n : ℕ}
    (C : Covariances m n) (q : AlgParams m n) (k : ℕ) (s : Ω → AlgState m n)
    (b : Ω → Batch m n B) (hW : Measurable[σ] (fun ω => (s ω).W))
    (hM : Measurable[σ] (fun ω => (s ω).Mprev)) (hb : Measurable[σ] b) :
    Measurable[σ] (fun ω => (step C q k (s ω) (b ω)).W) ∧
      Measurable[σ] (fun ω => (step C q k (s ω) (b ω)).Mprev) := by
  have hD : Measurable[σ] (fun ω => errorOf q (s ω)) :=
    (continuous_id.sub continuous_const).measurable.comp hW
  have hG := diffuse_grad_meas hD hb
  have hbuf : Measurable[σ] (fun ω => stepBuffer q (s ω) (b ω)) := by
    apply diffuse_mat_meas
    intro i j
    simp only [stepBuffer, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact ((diffuse_entry_meas hM i j).const_mul _).add
      ((diffuse_entry_meas hG i j).const_mul _)
  have hR : Measurable[σ] (fun ω => riskSigma C (errorOf q (s ω))) := by
    apply (show Continuous (fun D : Mat m n => riskSigma C D) by
      unfold riskSigma pairSigma
      fun_prop).measurable.comp hD
  have hset : MeasurableSet[σ] {ω | riskSigma C (errorOf q (s ω)) = 0} :=
    hR (measurableSet_singleton 0)
  have hU : Measurable[σ] (fun ω => stepUpdate C q (s ω) (b ω)) := by
    refine Measurable.ite hset measurable_const ?_
    have hnn : ∀ ω, 0 ≤ 2 * riskSigma C (errorOf q (s ω)) * q.ϱ := fun ω => by
      exact mul_nonneg (mul_nonneg (by norm_num)
        (by rw [eqn_app_setup_whitened_risk]; positivity)) q.hϱ.le
    have hφ : Measurable[σ]
        (fun ω => (⟨2 * riskSigma C (errorOf q (s ω)) * q.ϱ, hnn ω⟩ : Set.Ici (0 : ℝ))) :=
      ((hR.const_mul 2).mul_const q.ϱ).subtype_mk
    exact measurable_Q.comp (hφ.prodMk hbuf)
  refine ⟨?_, hbuf⟩
  apply diffuse_mat_meas
  intro i j
  simp only [step, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact (diffuse_entry_meas hW i j).sub ((diffuse_entry_meas hU i j).const_mul _)

private lemma diffuse_pi_meas {Ω : Type*} {σ : MeasurableSpace Ω} {ι : Type*}
    {π : ι → Type*} [∀ i, MeasurableSpace (π i)] {g : Ω → ∀ i, π i}
    (h : ∀ i, Measurable[σ] fun ω => g ω i) : Measurable[σ] g :=
  measurable_pi_iff.mpr h

private lemma diffuse_batch_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (u : ℕ) :
    Measurable[dynPast S (u + 1)] (dynBatch S u) := by
  refine diffuse_pi_meas (fun a => ?_)
  have hz : Measurable[dynPast S (u + 1)] (S.cs.act ((u : ℤ) + 1) a) := by
    apply Measurable.of_comap_le
    refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le ((u : ℤ) + 1) ⟨by omega, by push_cast; omega⟩
      (le_iSup_of_le a le_rfl)
  exact (show Continuous (fun z : Vec m × Vec n => phys S.C z) by
    unfold phys
    fun_prop).measurable.comp hz

private lemma diffuse_state_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S t] (fun ω => (dynState S t ω).W) ∧
      Measurable[dynPast S t] (dynBuf S t) := by
  induction t with
  | zero =>
      refine ⟨measurable_const, ?_⟩
      exact (comap_measurable S.M0).mono le_sup_right le_rfl
  | succ k ih =>
      have hW := ih.1.mono (diffuse_past_mono S (Nat.le_succ k)) le_rfl
      have hM := ih.2.mono (diffuse_past_mono S (Nat.le_succ k)) le_rfl
      exact diffuse_step_meas (σ := dynPast S (k + 1)) S.C S.alg k (dynState S k)
        (dynBatch S k) hW hM (diffuse_batch_meas S k)

private lemma diffuse_delta_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S t] (dynDelta S t) :=
  (continuous_id.sub continuous_const).measurable.comp (diffuse_state_meas S t).1

private lemma diffuse_adm_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) :
    MeasurableSet[dynPast S t] {ω | dynDelta S t ω ∈ admA p S.C} := by
  have hD := diffuse_delta_meas S t
  have hr : Measurable[dynPast S t] (fun ω => riskSigma S.C (dynDelta S t ω)) := by
    exact (show Continuous (fun D : Mat m n => riskSigma S.C D) by
      unfold riskSigma pairSigma
      fun_prop).measurable.comp hD
  have hf : Measurable[dynPast S t] (fun ω => fro (dynDelta S t ω) ^ 2) := by
    apply (show Continuous (fun D : Mat m n => fro D ^ 2) by
      unfold fro
      fun_prop).measurable.comp hD
  change MeasurableSet[dynPast S t]
    ({ω | p.r0 / 2 ≤ riskSigma S.C (dynDelta S t ω)} ∩
      ({ω | riskSigma S.C (dynDelta S t ω) ≤ p.r1 + 1 / 2} ∩
        {ω | fro (dynDelta S t ω) ^ 2 ≤ p.Estar + 1}))
  exact (measurableSet_le measurable_const hr).inter
    ((measurableSet_le hr measurable_const).inter (measurableSet_le hf measurable_const))

private lemma diffuse_initial_state {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {p : DynParams} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) :
    diffuseness S.C (dynDelta S 0 ω) = opNorm (Ahat S.C (S.W0 - S.alg.Wstar)) := by
  rfl

private lemma diffuse_initial_adm (p : DynParams) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) :
    dynDelta S 0 ω ∈ admA p S.C := by
  change p.r0 / 2 ≤ riskSigma S.C (S.W0 - S.alg.Wstar) ∧
    riskSigma S.C (S.W0 - S.alg.Wstar) ≤ p.r1 + 1 / 2 ∧
      fro (S.W0 - S.alg.Wstar) ^ 2 ≤ p.Estar + 1
  exact ⟨by linarith [S.W0_risk.1, p.hr0], by linarith [S.W0_risk.2],
    by linarith [S.W0_norm]⟩

private lemma diffuse_before_exit_adm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {p : DynParams} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) (b : ℕ)
    (hb : (b : ℕ∞) < dynBlockIndexExit S ω) :
    dynDelta S (b * blockLen B) ω ∈ admA p S.C := by
  by_contra hout
  have hle : dynBlockIndexExit S ω ≤ (b : ℕ∞) := by
    unfold dynBlockIndexExit
    exact iInf_le_of_le b (iInf_le_of_le hout le_rfl)
  exact (not_le_of_gt hb) hle

private lemma diffuse_before_exit_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {p : DynParams} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) (b : ℕ) :
    (b : ℕ∞) < dynBlockIndexExit S ω ↔
      ∀ a ≤ b, dynDelta S (a * blockLen B) ω ∈ admA p S.C := by
  constructor
  · intro hb a hab
    exact diffuse_before_exit_adm S ω a
      (lt_of_le_of_lt (by exact_mod_cast hab) hb)
  · intro h
    have hle : ((b + 1 : ℕ) : ℕ∞) ≤ dynBlockIndexExit S ω := by
      unfold dynBlockIndexExit
      refine le_iInf fun c => le_iInf fun hc => ?_
      exact_mod_cast Nat.succ_le_iff.mpr (lt_of_not_ge (fun hcb => hc (h c hcb)))
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self b) hle

private lemma diffuse_before_exit_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {p : DynParams} {m n B : ℕ} (S : DynSetup p P m n B) (b : ℕ) :
    MeasurableSet[dynPast S (b * blockLen B)]
      {ω | (b : ℕ∞) < dynBlockIndexExit S ω} := by
  have hm : ∀ a ∈ Finset.range (b + 1),
      MeasurableSet[dynPast S (b * blockLen B)]
        {ω | dynDelta S (a * blockLen B) ω ∈ admA p S.C} := by
    intro a ha
    exact diffuse_past_mono S (Nat.mul_le_mul_right _ (by
      have := Finset.mem_range.mp ha
      omega)) _ (diffuse_adm_meas S (a * blockLen B))
  have heq : {ω | (b : ℕ∞) < dynBlockIndexExit S ω} =
      ⋂ a ∈ Finset.range (b + 1),
        {ω | dynDelta S (a * blockLen B) ω ∈ admA p S.C} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range, Nat.lt_add_one_iff]
    exact diffuse_before_exit_iff S ω b
  rw [heq]
  exact (Finset.range (b + 1)).measurableSet_biInter hm

private lemma diffuse_block_filtration {p : DynParams} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) :
    ∃ ℱ : ℕ → MeasurableSpace Ω, Monotone ℱ ∧ (∀ b, ℱ b ≤ mΩ) ∧
      ∀ b, ℱ b = dynPast S (b * blockLen B) := by
  refine ⟨fun b => dynPast S (b * blockLen B), ?_, ?_, fun _ => rfl⟩
  · intro a b hab
    exact diffuse_past_mono S (Nat.mul_le_mul_right _ hab)
  · exact fun b => diffuse_past_le S (b * blockLen B)

private lemma diffuse_blockLen_pos {B : ℕ} (hB : 0 < B) : 0 < blockLen B := by
  unfold blockLen
  apply Nat.floor_pos.mpr
  exact Real.one_le_rpow (by exact_mod_cast hB) (by norm_num)

private lemma diffuse_exit_ge_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {p : DynParams} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) :
    (1 : ℕ∞) ≤ dynBlockIndexExit S ω := by
  unfold dynBlockIndexExit
  refine le_iInf fun b => le_iInf fun hb => ?_
  have hbpos : 1 ≤ b := by
    by_contra h
    have hb0 : b = 0 := by omega
    subst b
    exact hb (by simpa using diffuse_initial_adm p S ω)
  exact_mod_cast hbpos

private lemma diffuse_risk_before_exit (p : DynParams) :
    ∃ B0 : ℕ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (m n B : ℕ)
      (S : DynSetup p P m n B), B0 ≤ B → ∀ (ω : Ω) (t : ℕ),
        (t : ℕ∞) ≤ dynBlockExitTime S ω →
          p.r0 / 4 ≤ riskSigma S.C (dynDelta S t ω) := by
  obtain ⟨Bmove, hmove⟩ := lem_app_dyn_movement_ii p (p.r0 / 2) (p.r1 + 1 / 2)
    (p.Estar + 1) (by linarith [p.hr0]) (by nlinarith [p.hr, p.hr0])
  refine ⟨max Bmove 1, ?_⟩
  intro Ω _ P m n B S hB ω t ht
  have hBpos : 0 < B := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right Bmove 1).trans hB)
  have hLpos : 0 < blockLen B := diffuse_blockLen_pos hBpos
  let b := t / blockLen B
  have hble : b * blockLen B ≤ t := by
    dsimp [b]
    simpa only [mul_comm] using Nat.div_mul_le_self t (blockLen B)
  have htlt : t < (b + 1) * blockLen B := by
    exact (Nat.div_lt_iff_lt_mul hLpos).mp (by dsimp [b]; omega)
  have hwindow (a : ℕ) (ha : (a : ℕ∞) < dynBlockIndexExit S ω)
      (hat : |(t : ℤ) - (a * blockLen B : ℕ)| ≤ 4 * (blockLen B : ℤ)) :
      p.r0 / 4 ≤ riskSigma S.C (dynDelta S t ω) := by
    have hA := diffuse_before_exit_adm S ω a ha
    have hw := (hmove Ω P m n B S ((le_max_left Bmove 1).trans hB) ω
      (a * blockLen B) hA).2 t hat
    convert hw.1 using 1 <;> simp [enl] <;> ring
  by_cases hbexit : (b : ℕ∞) < dynBlockIndexExit S ω
  · apply hwindow b hbexit
    rw [Nat.add_mul, one_mul] at htlt
    have hdiff : t - b * blockLen B ≤ 4 * blockLen B := by omega
    have hbleI : ((b * blockLen B : ℕ) : ℤ) ≤ (t : ℤ) := by exact_mod_cast hble
    rw [abs_of_nonneg (sub_nonneg.mpr hbleI)]
    rw [← Int.ofNat_sub hble]
    exact_mod_cast hdiff
  · have hexitle : dynBlockIndexExit S ω ≤ (b : ℕ∞) := le_of_not_gt hbexit
    have hexitne : dynBlockIndexExit S ω ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.coe_ne_top b) hexitle
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hexitne
    have hcb : c ≤ b := by
      rw [← hc] at hexitle
      exact ENat.coe_le_coe.mp hexitle
    have htcb : t ≤ blockLen B * c := by
      rw [dynBlockExitTime, ← hc] at ht
      rw [← ENat.coe_mul] at ht
      exact ENat.coe_le_coe.mp ht
    have hbc : b ≤ c := by
      dsimp [b]
      exact Nat.div_le_of_le_mul htcb
    have hbc_eq : b = c := Nat.le_antisymm hbc hcb
    have hbpos : 0 < b := by
      have hc1 : 1 ≤ c := by
        have he := diffuse_exit_ge_one S ω
        rw [← hc] at he
        exact ENat.coe_le_coe.mp he
      omega
    apply hwindow (b - 1)
    · rw [← hc, ← hbc_eq]
      exact ENat.coe_lt_coe.mpr (by omega)
    · have hbase : (b - 1) * blockLen B ≤ t :=
        (Nat.mul_le_mul_right (blockLen B) (Nat.sub_le b 1)).trans hble
      have hbdecomp : b = (b - 1) + 1 := by omega
      have hspan : (b + 1) * blockLen B =
          (b - 1) * blockLen B + 2 * blockLen B := by
        nth_rewrite 1 [hbdecomp]
        ring
      rw [hspan] at htlt
      have hdiff : t - (b - 1) * blockLen B ≤ 4 * blockLen B := by omega
      have hbaseI : ((((b - 1) * blockLen B : ℕ)) : ℤ) ≤ (t : ℤ) := by
        exact_mod_cast hbase
      rw [abs_of_nonneg (sub_nonneg.mpr hbaseI)]
      rw [← Int.ofNat_sub hbase]
      exact_mod_cast hdiff

private lemma diffuse_fro_nonneg {m n : ℕ} (A : Mat m n) : 0 ≤ fro A :=
  Real.sqrt_nonneg _

private lemma diffuse_opNorm_nonneg {m n : ℕ} (A : Mat m n) : 0 ≤ opNorm A := by
  unfold opNorm
  exact norm_nonneg _

private lemma diffuse_opNorm_mul {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  open scoped Matrix.Norms.L2Operator in
  simpa only [opNorm_eq_norm] using Matrix.l2_opNorm_mul A B

open scoped Matrix.Norms.L2Operator in
private lemma diffuse_opNorm_transpose {m n : ℕ} (A : Mat m n) :
    opNorm Aᵀ = opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma diffuse_mulVec_sq_le {m n : ℕ} (A : Mat m n) (v : Fin n → ℝ) :
    ∑ i, (∑ j, A i j * v j) ^ 2 ≤ opNorm A ^ 2 * ∑ j, v j ^ 2 := by
  open scoped Matrix.Norms.L2Operator in
    rw [opNorm_eq_norm]
    have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 v)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hsq
    simpa [Matrix.mulVec, dotProduct] using hsq

private lemma diffuse_spectrum_hermDilation {m n : ℕ} (A : Mat m n) (c : ℝ)
    (hA : opNorm A ≤ c) :
    spectrum ℝ (Muon.Foundations.hermDilation A) ⊆ Set.Icc (-c) c := by
  intro l hl
  have hH := Muon.Foundations.hermDilation_isHermitian A
  rw [hH.spectrum_real_eq_range_eigenvalues] at hl
  obtain ⟨i, rfl⟩ := hl
  set lam := hH.eigenvalues i with hlam
  set v := hH.eigenvectorBasis i with hvdef
  have hv : Muon.Foundations.hermDilation A *ᵥ ⇑v = lam • ⇑v :=
    hH.mulVec_eigenvectorBasis i
  have hnorm : ∑ k, (v k) ^ 2 = 1 := by
    have h1 : ‖v‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
    rw [← EuclideanSpace.real_norm_sq_eq, h1]
    norm_num
  set e := (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)) with he
  set x : Fin m → ℝ := fun i => v (e (Sum.inl i)) with hx
  set y : Fin n → ℝ := fun j => v (e (Sum.inr j)) with hy
  have hsum : ∑ i, x i ^ 2 + ∑ j, y j ^ 2 = 1 := by
    rw [← hnorm, ← Equiv.sum_comp e, Fintype.sum_sum_type]
  have hu : (v ∘ e) = Sum.elim x y := by
    funext s
    rcases s with s | s <;> rfl
  have hmv : Muon.Foundations.hermDilation A *ᵥ ⇑v =
      (((Matrix.fromBlocks 0 A Aᵀ 0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) *ᵥ
        (v ∘ e)) ∘ e.symm) := by
    unfold Muon.Foundations.hermDilation
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    rfl
  have h1 : ∀ i, (A *ᵥ y) i = lam * x i := by
    intro i
    have hi := congrFun hv (e (Sum.inl i))
    rw [hmv] at hi
    simp only [Function.comp, Equiv.symm_apply_apply, hu, Matrix.fromBlocks_mulVec] at hi
    simpa using hi
  have h2 : ∀ j, (Aᵀ *ᵥ x) j = lam * y j := by
    intro j
    have hj := congrFun hv (e (Sum.inr j))
    rw [hmv] at hj
    simp only [Function.comp, Equiv.symm_apply_apply, hu, Matrix.fromBlocks_mulVec] at hj
    simpa using hj
  have e1 : lam ^ 2 * ∑ i, x i ^ 2 ≤ c ^ 2 * ∑ j, y j ^ 2 := by
    have h := diffuse_mulVec_sq_le A y
    have heq : ∑ i, (∑ j, A i j * y j) ^ 2 = lam ^ 2 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi := h1 i
      simp only [Matrix.mulVec, dotProduct] at hi
      rw [hi]
      ring
    rw [heq] at h
    have hop : 0 ≤ opNorm A := diffuse_opNorm_nonneg A
    have hs : opNorm A ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hop hA 2
    nlinarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (y j))]
  have e2 : lam ^ 2 * ∑ j, y j ^ 2 ≤ c ^ 2 * ∑ i, x i ^ 2 := by
    have h := diffuse_mulVec_sq_le Aᵀ x
    have heq : ∑ j, (∑ i, Aᵀ j i * x i) ^ 2 = lam ^ 2 * ∑ j, y j ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj := h2 j
      simp only [Matrix.mulVec, dotProduct] at hj
      rw [hj]
      ring
    rw [heq, diffuse_opNorm_transpose] at h
    have hop : 0 ≤ opNorm A := diffuse_opNorm_nonneg A
    have hs : opNorm A ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hop hA 2
    nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (x i))]
  have h3 : lam ^ 2 ≤ c ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' h3 ((diffuse_opNorm_nonneg A).trans hA)

private lemma diffuse_opNorm_upperRight {m n : ℕ} (X : Mat (m + n) (m + n)) :
    opNorm (Muon.Foundations.upperRight X) ≤ opNorm X := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) (fun x => ?_)
  set y : EuclideanSpace ℝ (Fin (m + n)) :=
    WithLp.toLp 2 (Fin.append (0 : Fin m → ℝ) x.ofLp) with hy
  have hyn : ‖y‖ = ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [hy, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have hle := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)).le_opNorm y
  rw [← hyn]
  refine le_trans ?_ hle
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_add]
  have h2 : 0 ≤ ∑ i : Fin n,
      ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X) y) (Fin.natAdd m i)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  refine le_trans (le_of_eq ?_) (le_add_of_nonneg_right h2)
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [hy, Matrix.mulVec, dotProduct, Muon.Foundations.upperRight, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right]

open scoped Matrix.Norms.L2Operator in
private lemma diffuse_opNorm_hermDilation {m n : ℕ} (A : Mat m n) :
    opNorm (Muon.Foundations.hermDilation A) = opNorm A := by
  apply le_antisymm
  · have hH := Muon.Foundations.hermDilation_isHermitian A
    by_cases hd : m + n = 0
    · have hzero : Muon.Foundations.hermDilation A = 0 := by
        ext i
        exact Fin.elim0 (hd ▸ i)
      rw [hzero]
      simp [opNorm]
    have : NeZero (m + n) := ⟨hd⟩
    obtain ⟨⟨t, ht, heq⟩, _⟩ :=
      IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ)
        (Muon.Foundations.hermDilation A) hH.isSelfAdjoint
    change ‖t‖ = ‖Muon.Foundations.hermDilation A‖ at heq
    rw [Real.norm_eq_abs, ← opNorm_eq_norm] at heq
    rw [← heq]
    exact abs_le.mpr (diffuse_spectrum_hermDilation A (opNorm A) le_rfl ht)
  · have hur : Muon.Foundations.upperRight (Muon.Foundations.hermDilation A) = A := by
      ext i j
      simp [Muon.Foundations.upperRight, Muon.Foundations.hermDilation,
        Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
    calc
      opNorm A = opNorm (Muon.Foundations.upperRight
          (Muon.Foundations.hermDilation A)) := congrArg opNorm hur.symm
      _ ≤ opNorm (Muon.Foundations.hermDilation A) := diffuse_opNorm_upperRight _

private lemma diffuse_hermDilation_sub {m n : ℕ} (A B : Mat m n) :
    Muon.Foundations.hermDilation (A - B) =
      Muon.Foundations.hermDilation A - Muon.Foundations.hermDilation B := by
  ext i j
  simp only [Muon.Foundations.hermDilation, Matrix.sub_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  generalize finSumFinEquiv.symm i = a
  generalize finSumFinEquiv.symm j = b
  cases a <;> cases b <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.transpose_sub]

private lemma diffuse_hermDilation_smul {m n : ℕ} (a : ℝ) (A : Mat m n) :
    Muon.Foundations.hermDilation (a • A) =
      a • Muon.Foundations.hermDilation A := by
  ext i j
  simp only [Muon.Foundations.hermDilation, Matrix.smul_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  cases u <;> cases v <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply]

private lemma diffuse_hermDilation_sum {m n : ℕ} {ι : Type*} (s : Finset ι)
    (A : ι → Mat m n) :
    Muon.Foundations.hermDilation (∑ i ∈ s, A i) =
      ∑ i ∈ s, Muon.Foundations.hermDilation (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext i j
      simp [Muon.Foundations.hermDilation]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [show Muon.Foundations.hermDilation (A a + ∑ x ∈ s, A x) =
          Muon.Foundations.hermDilation (A a) +
            Muon.Foundations.hermDilation (∑ x ∈ s, A x) by
        rw [show A a + ∑ x ∈ s, A x = A a - (-(∑ x ∈ s, A x)) by abel,
          diffuse_hermDilation_sub, show Muon.Foundations.hermDilation (-(∑ x ∈ s, A x)) =
            -Muon.Foundations.hermDilation (∑ x ∈ s, A x) by
              simpa only [neg_smul, one_smul] using diffuse_hermDilation_smul (-1) (∑ x ∈ s, A x)]
        abel]
      rw [ih]

open scoped Matrix.Norms.L2Operator in
private lemma diffuse_sqrt_opNorm_sq {k : ℕ} (A : Mat k k) (hA : A.PosSemidef) :
    opNorm (CFC.sqrt A) ^ 2 = opNorm A := by
  have hh : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hs : CFC.sqrt A * CFC.sqrt A = A :=
    CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.mpr hA)
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (CFC.sqrt A)
  rw [hh, hs] at h
  simpa only [opNorm_eq_norm, pow_two] using h.symm

private lemma diffuse_Arot_opNorm_le (p : DynParams) {m n B : ℕ}
    (C : Covariances m n) (hsize : Muon.Volatility.SizeFin C B p.γstar p.CSig) (D : Mat m n) :
    opNorm (Arot C D) ≤ p.CSig * opNorm D := by
  have ho := diffuse_sqrt_opNorm_sq C.Sout C.psdOut
  have hi := diffuse_sqrt_opNorm_sq C.Sin C.psdIn
  have hC : 0 ≤ p.CSig := le_trans (by norm_num) p.hC
  have hn : opNorm (rOut C) * opNorm (rIn C) ≤ p.CSig := by
    have h1 : 0 ≤ opNorm (rOut C) := diffuse_opNorm_nonneg _
    have h2 : 0 ≤ opNorm (rIn C) := diffuse_opNorm_nonneg _
    have h3 : opNorm (rOut C) ^ 2 ≤ p.CSig := ho.le.trans hsize.2.1
    have h4 : opNorm (rIn C) ^ 2 ≤ p.CSig := hi.le.trans hsize.2.2
    have hm := mul_le_mul h3 h4 (sq_nonneg (opNorm (rIn C))) hC
    nlinarith [mul_nonneg h1 h2]
  calc
    opNorm (Arot C D) ≤ opNorm (rOut C) * opNorm D * opNorm (rIn C) :=
      (diffuse_opNorm_mul (rOut C * D) (rIn C)).trans
        (mul_le_mul_of_nonneg_right (diffuse_opNorm_mul (rOut C) D)
          (diffuse_opNorm_nonneg _))
    _ = (opNorm (rOut C) * opNorm (rIn C)) * opNorm D := by ring
    _ ≤ p.CSig * opNorm D :=
      mul_le_mul_of_nonneg_right hn (diffuse_opNorm_nonneg _)

private lemma diffuse_delta_succ (p : DynParams) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) (t : ℕ) :
    dynDelta S (t + 1) ω = dynDelta S t ω - (p.h / B) • dynUpd S t ω := by
  change (run S.C S.alg _ _ (t + 1)).W - S.alg.Wstar = _
  simp only [run, step, dynDelta, devRand, dynUpd, gtRand, errorOf, runRand, S.alg_η]
  module

private lemma diffuse_delta_add (p : DynParams) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) (t L : ℕ) :
    dynDelta S (t + L) ω = dynDelta S t ω -
      (p.h / B) • ∑ r ∈ Finset.range L, dynUpd S (t + r) ω := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Nat.add_succ, diffuse_delta_succ, ih, Finset.sum_range_succ, smul_add]
      abel

private lemma diffuse_opNorm_accumulate {m n : ℕ} (D : ℕ → Mat m n) (a : ℝ)
    (hstep : ∀ u, opNorm (D (u + 1) - D u) ≤ a) (t t' : ℕ) (htt' : t ≤ t') :
    opNorm (D t' - D t) ≤ a * ((t' : ℝ) - t) := by
  induction t', htt' using Nat.le_induction with
  | base => simp [opNorm]
  | succ u hu ih =>
    have he : D (u + 1) - D t = (D (u + 1) - D u) + (D u - D t) := by abel
    rw [he]
    have hadd : opNorm ((D (u + 1) - D u) + (D u - D t)) ≤
        opNorm (D (u + 1) - D u) + opNorm (D u - D t) := by
      open scoped Matrix.Norms.L2Operator in
      simpa only [opNorm_eq_norm] using norm_add_le (D (u + 1) - D u) (D u - D t)
    have h := hadd.trans (add_le_add (hstep u) ih)
    push_cast
    linarith

private lemma diffuse_Arot_movement (p : DynParams) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω)
    (t t' : ℕ) (htt' : t ≤ t') :
    opNorm (Arot S.C (dynDelta S t' ω - dynDelta S t ω)) ≤
      p.CSig * p.h * ((t' : ℝ) - t) / B := by
  have hη : 0 ≤ p.h / (B : ℝ) := div_nonneg p.hh.le (Nat.cast_nonneg _)
  have hmove := diffuse_opNorm_accumulate (fun u => dynDelta S u ω) (p.h / B)
    (fun u => by
      have hupd : opNorm (dynUpd S u ω) ≤ 1 := by
        have hr : 0 ≤ riskSigma S.C (dynDelta S u ω) := by
          rw [eqn_app_setup_whitened_risk]
          positivity
        unfold dynUpd gtRand stepUpdate
        split_ifs with hz
        · simp [opNorm]
        · have hh : 0 ≤ 2 * riskSigma S.C (dynDelta S u ω) * S.alg.ϱ :=
            mul_nonneg (mul_nonneg (by norm_num) hr) S.alg.hϱ.le
          exact (lem_app_setup_filter_i _ hh
            (stepBuffer S.alg (runRand S.C S.alg (dynStart S) (dynBatch S) u ω)
              (dynBatch S u ω))).1
      rw [diffuse_delta_succ, sub_sub_cancel_left]
      open scoped Matrix.Norms.L2Operator in
      simp only [opNorm_eq_norm, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
      exact (mul_le_mul_of_nonneg_left hupd hη).trans_eq (mul_one _)) t t' htt'
  calc
    opNorm (Arot S.C (dynDelta S t' ω - dynDelta S t ω))
        ≤ p.CSig * opNorm (dynDelta S t' ω - dynDelta S t ω) :=
      diffuse_Arot_opNorm_le p S.C S.size _
    _ ≤ p.CSig * ((p.h / B) * ((t' : ℝ) - t)) :=
      mul_le_mul_of_nonneg_left hmove (le_trans (by norm_num) p.hC)
    _ = p.CSig * p.h * ((t' : ℝ) - t) / B := by ring

private lemma diffuse_Arot_block_movement (p : DynParams) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) (t : ℕ) :
    opNorm (Arot S.C (dynDelta S (t + blockLen B) ω - dynDelta S t ω)) ≤
      p.CSig * p.h * (blockLen B : ℝ) / B := by
  simpa only [Nat.cast_add, add_sub_cancel_left] using
    diffuse_Arot_movement p S ω t (t + blockLen B) (Nat.le_add_right _ _)

private lemma diffuse_dimension_bound (p : DynParams) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) :
    ((m + n : ℕ) : ℝ) ≤ 2 * p.γstar * B := by
  have hm : (m : ℝ) ≤ p.γstar * B := by
    have hmmax : (m : ℝ) ≤ ((max m n : ℕ) : ℝ) := by
      exact_mod_cast (le_max_left m n)
    exact hmmax.trans S.size.1
  have hn : (n : ℝ) ≤ p.γstar * B := by
    have hnmax : (n : ℝ) ≤ ((max m n : ℕ) : ℝ) := by
      exact_mod_cast (le_max_right m n)
    exact hnmax.trans S.size.1
  push_cast
  linarith

open scoped Matrix.Norms.L2Operator in
private lemma diffuse_eq_rot_div_sqrt_risk {m n : ℕ} (C : Covariances m n) (D : Mat m n) :
    diffuseness C D = opNorm (Arot C D) / Real.sqrt (2 * riskSigma C D) := by
  unfold diffuseness normState Ahat
  rw [opNorm_eq_norm, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), ← opNorm_eq_norm]
  ring

open scoped Matrix.Norms.L2Operator in
private lemma diffuse_le_rot_div_sqrt {m n : ℕ} (C : Covariances m n) (D : Mat m n)
    {r : ℝ} (hr : 0 < r) (hD : r ≤ riskSigma C D) :
    diffuseness C D ≤ opNorm (Arot C D) / Real.sqrt (2 * r) := by
  rw [diffuse_eq_rot_div_sqrt_risk]
  have hop : 0 ≤ opNorm (Arot C D) := by rw [opNorm_eq_norm]; positivity
  have hsqrt : Real.sqrt (2 * r) ≤ Real.sqrt (2 * riskSigma C D) := by
    exact Real.sqrt_le_sqrt (by linarith)
  exact div_le_div_of_nonneg_left hop (by positivity) hsqrt

private lemma diffuse_update_bounds (p : DynParams) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) (t : ℕ) :
    opNorm (dynUpd S t ω) ≤ 1 ∧ fro (dynUpd S t ω) ≤ Real.sqrt (p.γstar * B) := by
  have hr : 0 ≤ riskSigma S.C (dynDelta S t ω) := by
    rw [eqn_app_setup_whitened_risk]
    positivity
  unfold dynUpd gtRand stepUpdate
  split_ifs with hz
  · simp [opNorm, fro]
    positivity
  · have hh : 0 ≤ 2 * riskSigma S.C (dynDelta S t ω) * S.alg.ϱ := by
      exact mul_nonneg (mul_nonneg (by norm_num) hr) S.alg.hϱ.le
    obtain ⟨ho, hf, hk, _⟩ := lem_app_setup_filter_i _ hh
      (stepBuffer S.alg (runRand S.C S.alg (dynStart S) (dynBatch S) t ω) (dynBatch S t ω))
    refine ⟨ho, ?_⟩
    have hmin : ((min m n : ℕ) : ℝ) ≤ p.γstar * B := by
      have hm : ((min m n : ℕ) : ℝ) ≤ ((max m n : ℕ) : ℝ) := by
        exact_mod_cast (min_le_max : min m n ≤ max m n)
      exact hm.trans S.size.1
    have hk' : ((stepBuffer S.alg (runRand S.C S.alg (dynStart S) (dynBatch S) t ω)
        (dynBatch S t ω)).rank : ℝ) ≤ ((min m n : ℕ) : ℝ) := by
      exact_mod_cast hk
    exact (Real.le_sqrt (diffuse_fro_nonneg _) (mul_nonneg p.hγ (Nat.cast_nonneg B))).mpr
      (hf.trans (hk'.trans hmin))

private lemma diffuse_discrete_gronwall {u : ℕ → ℝ} {A a : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hu : ∀ j, u j ≤ A + a * ∑ b ∈ Finset.range j, u b) :
    ∀ j, u j ≤ A * (1 + a) ^ j := by
  let v : ℕ → ℝ := fun j => A + a * ∑ b ∈ Finset.range j, u b
  have hv : ∀ j, v j ≤ A * (1 + a) ^ j := by
    intro j
    induction j with
    | zero => simp [v]
    | succ j ih =>
        have huj : u j ≤ v j := by simpa [v] using hu j
        have hstep : v (j + 1) = v j + a * u j := by
          simp only [v, Finset.sum_range_succ]
          ring
        rw [hstep, pow_succ]
        calc
          v j + a * u j ≤ v j + a * v j :=
            add_le_add_right (mul_le_mul_of_nonneg_left huj ha) _
          _ = v j * (1 + a) := by ring
          _ ≤ (A * (1 + a) ^ j) * (1 + a) :=
            mul_le_mul_of_nonneg_right ih (by linarith)
          _ = A * ((1 + a) ^ j * (1 + a)) := by ring
  intro j
  exact (hu j).trans (hv j)

private lemma diffuse_hermDilation_entry {m n : ℕ} (p q : Fin (m + n)) :
    (∀ V : Mat m n, Muon.Foundations.hermDilation V p q = 0) ∨
      ∃ (i : Fin m) (j : Fin n), ∀ V : Mat m n, Muon.Foundations.hermDilation V p q = V i j := by
  unfold Muon.Foundations.hermDilation
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize finSumFinEquiv.symm p = a
  generalize finSumFinEquiv.symm q = b
  rcases a with i | i <;> rcases b with j | j
  · left
    intro V
    simp [Matrix.fromBlocks_apply₁₁]
  · right
    exact ⟨i, j, fun V => by simp [Matrix.fromBlocks_apply₁₂]⟩
  · right
    exact ⟨j, i, fun V => by simp [Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply]⟩
  · left
    intro V
    simp [Matrix.fromBlocks_apply₂₂]

private lemma diffuse_abs_entry_le {m n : ℕ} (A : Mat m n) (i : Fin m) (j : Fin n) :
    |A i j| ≤ opNorm A := by
  have h := mm_abs_entry_le_opNorm (Muon.Foundations.hermDilation A) (Fin.castAdd n i)
    (Fin.natAdd m j)
  rw [diffuse_opNorm_hermDilation] at h
  have : Muon.Foundations.hermDilation A (Fin.castAdd n i) (Fin.natAdd m j) = A i j := by
    simp [Muon.Foundations.hermDilation, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.fromBlocks_apply₁₂, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd]
  rwa [this] at h

open scoped Matrix.Norms.L2Operator in
private lemma diffuse_opNorm_meas {Ω : Type*} {σ : MeasurableSpace Ω} {m n : ℕ}
    {F : Ω → Mat m n} (hF : Measurable[σ] F) : Measurable[σ] (fun ω => opNorm (F ω)) := by
  have hc : Continuous (fun A : Mat m n => opNorm A) := by
    simp only [opNorm_eq_norm]
    exact continuous_norm
  exact hc.measurable.comp hF

open scoped Matrix.Norms.L2Operator in
private lemma diffuse_mart_tail {Ω : Type*}
    [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m n : ℕ}
    (ℱ : ℕ → MeasurableSpace Ω) (hmono : Monotone ℱ) (hle : ∀ b, ℱ b ≤ mΩ)
    (X : ℕ → Ω → Mat m n) (hmeas : ∀ b i j, Measurable[ℱ (b + 1)] (fun ω => X b ω i j))
    (c : ℝ) (hc : 0 ≤ c) (hbd : ∀ b ω, opNorm (X b ω) ≤ c)
    (x : ℝ) (hx : 0 < x) (N : ℕ) (hN : 1 ≤ N) :
    P {ω | ∃ j ≤ N, x ≤ opNorm (∑ b ∈ Finset.range j,
        (X b ω - Muon.Foundations.condExpMat (ℱ b) P (X b) ω))} ≤
      ENNReal.ofReal (2 * ((m + n : ℕ) : ℝ) * (N : ℝ) *
        Real.exp (-(x ^ 2) / (2 * (N : ℝ) * (2 * c) ^ 2))) := by
  classical
  set V : ℕ → Ω → Mat m n :=
    fun b ω => X b ω - Muon.Foundations.condExpMat (ℱ b) P (X b) ω with hV
  have hXint : ∀ b i j, Integrable (fun ω => X b ω i j) P := by
    intro b i j
    refine Integrable.mono' (integrable_const c)
      ((hmeas b i j).mono (hle (b + 1)) le_rfl).aestronglyMeasurable ?_
    exact ae_of_all P fun ω => by
      rw [Real.norm_eq_abs]
      exact (diffuse_abs_entry_le _ i j).trans (hbd b ω)
  have hVent_meas : ∀ b i j, Measurable[ℱ (b + 1)] (fun ω => V b ω i j) := by
    intro b i j
    have h1 := hmeas b i j
    have h2 : Measurable[ℱ b] (fun ω => condExp (ℱ b) P (fun ω' => X b ω' i j) ω) :=
      (stronglyMeasurable_condExp (m := ℱ b) (μ := P)
        (f := fun ω => X b ω i j)).measurable
    exact h1.sub (h2.mono (hmono (Nat.le_succ b)) le_rfl)
  have hVmean : ∀ b i j, condExp (ℱ b) P (fun ω => V b ω i j) =ᵐ[P] 0 := by
    intro b i j
    have hi := hXint b i j
    have hcI : Integrable (condExp (ℱ b) P (fun ω => X b ω i j)) P := integrable_condExp
    have hsub := condExp_sub hi hcI (ℱ b)
    have h2 : condExp (ℱ b) P (condExp (ℱ b) P (fun ω => X b ω i j)) =ᵐ[P]
        condExp (ℱ b) P (fun ω => X b ω i j) :=
      condExp_condExp_of_le le_rfl (hle b)
    filter_upwards [hsub, h2] with ω h h'
    have e : (fun ω => V b ω i j) = (fun ω => X b ω i j) -
        condExp (ℱ b) P (fun ω => X b ω i j) := rfl
    rw [e, h]
    simp only [Pi.sub_apply, h', sub_self, Pi.zero_apply]
  have hcond_bd : ∀ b, ∀ᵐ ω ∂P,
      opNorm (Muon.Foundations.condExpMat (ℱ b) P (X b) ω) ≤ c := by
    intro b
    have hXm : Measurable (X b) := diffuse_mat_meas fun i j =>
      (hmeas b i j).mono (hle (b + 1)) le_rfl
    have hop_meas : Measurable (fun ω => opNorm (X b ω)) := diffuse_opNorm_meas hXm
    have hop_int : Integrable (fun ω => opNorm (X b ω)) P :=
      Integrable.mono' (integrable_const c) hop_meas.aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (diffuse_opNorm_nonneg _)]
          exact hbd b ω)
    have h1 := opNorm_condExpMat_le (ℱ b) (hle b) (X b) (hXint b) hop_int
    have h2 : condExp (ℱ b) P (fun ω => opNorm (X b ω)) ≤ᵐ[P] fun _ => c := by
      have := condExp_mono (m := ℱ b) hop_int (integrable_const c)
        (ae_of_all P fun ω => hbd b ω)
      filter_upwards [this] with ω hω
      rwa [condExp_const (hle b)] at hω
    filter_upwards [h1, h2] with ω h1 h2 using h1.trans h2
  set D : ℕ → Ω → Mat (m + n) (m + n) := fun b ω => Muon.Foundations.hermDilation (V b ω) with hD
  have hDop : ∀ᵐ ω ∂P, ∀ b, opNorm (D b ω) ≤ 2 * c := by
    rw [ae_all_iff]
    intro b
    filter_upwards [hcond_bd b] with ω hω
    simp only [hD]
    rw [diffuse_opNorm_hermDilation]
    have : opNorm (V b ω) ≤ opNorm (X b ω) +
        opNorm (Muon.Foundations.condExpMat (ℱ b) P (X b) ω) := by
      simp only [hV, opNorm_eq_norm]
      exact norm_sub_le _ _
    linarith [hbd b ω]
  have hDent : ∀ b p q, Measurable[ℱ (b + 1)] (fun ω => D b ω p q) := by
    intro b p q
    rcases diffuse_hermDilation_entry (m := m) (n := n) p q with h | ⟨i, j, h⟩
    · simp only [hD, h]
      exact measurable_const
    · simp only [hD, h]
      exact hVent_meas b i j
  set Z : ℕ → Ω → Mat (m + n) (m + n) :=
    fun b ω => if opNorm (D b ω) ≤ 2 * c then D b ω else 0 with hZ
  have hZsa : ∀ b ω, (Z b ω).IsHermitian := by
    intro b ω
    simp only [hZ]
    split_ifs
    · exact Muon.Foundations.hermDilation_isHermitian _
    · exact Matrix.isHermitian_zero
  have hZbd : ∀ b ω, opNorm (Z b ω) ≤ 2 * c := by
    intro b ω
    simp only [hZ]
    split_ifs with h
    · exact h
    · have h0 : opNorm (0 : Mat (m + n) (m + n)) = 0 := by simp [opNorm]
      rw [h0]
      linarith
  have hZmeas : ∀ b p q, Measurable[ℱ (b + 1)] (fun ω => Z b ω p q) := by
    intro b p q
    have hset : MeasurableSet[ℱ (b + 1)] {ω | opNorm (D b ω) ≤ 2 * c} :=
      measurableSet_le (diffuse_opNorm_meas (diffuse_mat_meas (hDent b))) measurable_const
    have : (fun ω => Z b ω p q) = fun ω => if opNorm (D b ω) ≤ 2 * c then D b ω p q else 0 := by
      funext ω
      simp only [hZ]
      split_ifs <;> rfl
    rw [this]
    exact Measurable.ite hset (hDent b p q) measurable_const
  have hZmean : ∀ b p q, condExp (ℱ b) P (fun ω => Z b ω p q) =ᵐ[P] 0 := by
    intro b p q
    have hae : (fun ω => Z b ω p q) =ᵐ[P] fun ω => D b ω p q := by
      filter_upwards [hDop] with ω hω
      simp only [hZ, if_pos (hω b)]
    refine (condExp_congr_ae hae).trans ?_
    rcases diffuse_hermDilation_entry (m := m) (n := n) p q with h | ⟨i, j, h⟩
    · have : (fun ω => D b ω p q) = 0 := by
        funext ω
        simp only [hD, h, Pi.zero_apply]
      rw [this, condExp_zero]
    · have : (fun ω => D b ω p q) = fun ω => V b ω i j := by
        funext ω
        simp only [hD, h]
      rw [this]
      exact hVmean b i j
  have hZ2 := lem_app_dyn_matrix_martingale P (m + n) ℱ hmono hle Z hZsa hZmeas hZmean
    (2 * c) hZbd x hx N hN
  have hsub : {ω | ∃ j ≤ N, x ≤ opNorm (∑ b ∈ Finset.range j,
        (X b ω - Muon.Foundations.condExpMat (ℱ b) P (X b) ω))} ≤ᵐ[P]
      {ω | ∃ j ≤ N, x ≤ opNorm (∑ b ∈ Finset.range j, Z b ω)} := by
    filter_upwards [hDop] with ω hω hmem
    obtain ⟨j, hj, hxj⟩ := hmem
    refine ⟨j, hj, ?_⟩
    have : ∑ b ∈ Finset.range j, Z b ω =
        Muon.Foundations.hermDilation (∑ b ∈ Finset.range j, V b ω) := by
      rw [diffuse_hermDilation_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hZD : Z b ω = D b ω := by
        simp only [hZ]
        rw [if_pos (hω b)]
      rw [hZD]
    rw [this, diffuse_opNorm_hermDilation]
    exact hxj
  exact (measure_mono_ae hsub).trans hZ2.2

private lemma diffuse_condExp_sum {Ω : Type*} (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) P) :
    condExp 𝒢 P (fun ω => ∑ i ∈ s, f i ω) =ᵐ[P] fun ω => ∑ i ∈ s, condExp 𝒢 P (f i) ω := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have : (fun _ : Ω => (0 : ℝ)) = 0 := rfl
      rw [this, condExp_zero]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have hsum : Integrable (fun ω => ∑ i ∈ s, f i ω) P :=
        integrable_finset_sum _ fun i _ => hf i
      have h1 := condExp_add (hf a) hsum 𝒢
      filter_upwards [h1, ih] with ω h1ω ihω
      have e : (fun ω => f a ω + ∑ i ∈ s, f i ω) =
          f a + fun ω => ∑ i ∈ s, f i ω := rfl
      rw [e, h1ω]
      simp only [Pi.add_apply, ihω]

private lemma diffuse_rot_entry {m n : ℕ} (R : Mat m m) (Q : Mat n n) (a : ℝ) (U : Mat m n)
    (i : Fin m) (j : Fin n) :
    (a • (R * U * Q)) i j = ∑ p : Fin m × Fin n, (a * R i p.1 * Q p.2 j) * U p.1 p.2 := by
  rw [Fintype.sum_prod_type]
  simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

private lemma diffuse_condExpMat_rot {Ω : Type*} (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m n : ℕ} (R : Mat m m) (Q : Mat n n)
    (a : ℝ) (U : Ω → Mat m n) (hU : ∀ i j, Integrable (fun ω => U ω i j) P) :
    Muon.Foundations.condExpMat 𝒢 P (fun ω => a • (R * U ω * Q)) =ᵐ[P]
      fun ω => a • (R * Muon.Foundations.condExpMat 𝒢 P U ω * Q) := by
  classical
  have hent : ∀ i j, ∀ᵐ ω ∂P, Muon.Foundations.condExpMat 𝒢 P (fun ω => a • (R * U ω * Q)) ω i j =
      (a • (R * Muon.Foundations.condExpMat 𝒢 P U ω * Q)) i j := by
    intro i j
    have e1 : (fun ω' => (a • (R * U ω' * Q)) i j) =
        fun ω' => ∑ p : Fin m × Fin n, (a * R i p.1 * Q p.2 j) * U ω' p.1 p.2 := by
      funext ω'
      exact diffuse_rot_entry R Q a (U ω') i j
    have hf : ∀ p : Fin m × Fin n, Integrable
        (fun ω' => (a * R i p.1 * Q p.2 j) * U ω' p.1 p.2) P := fun p =>
      (hU p.1 p.2).const_mul _
    have hs := diffuse_condExp_sum 𝒢 P Finset.univ _ hf
    have hp : ∀ p : Fin m × Fin n, condExp 𝒢 P
        (fun ω' => (a * R i p.1 * Q p.2 j) * U ω' p.1 p.2) =ᵐ[P]
        fun ω => (a * R i p.1 * Q p.2 j) * condExp 𝒢 P (fun ω' => U ω' p.1 p.2) ω := by
      intro p
      have := condExp_smul (μ := P) (a * R i p.1 * Q p.2 j) (fun ω' => U ω' p.1 p.2) 𝒢
      exact this
    have hall : ∀ᵐ ω ∂P, ∀ p : Fin m × Fin n, condExp 𝒢 P
        (fun ω' => (a * R i p.1 * Q p.2 j) * U ω' p.1 p.2) ω =
        (a * R i p.1 * Q p.2 j) * condExp 𝒢 P (fun ω' => U ω' p.1 p.2) ω :=
      ae_all_iff.mpr hp
    filter_upwards [hs, hall] with ω hsω hallω
    change condExp 𝒢 P (fun ω' => (a • (R * U ω' * Q)) i j) ω = _
    rw [e1, hsω]
    simp only [hallω]
    rw [diffuse_rot_entry R Q a (Muon.Foundations.condExpMat 𝒢 P U ω) i j]
    rfl
  have hall : ∀ᵐ ω ∂P, ∀ i j, Muon.Foundations.condExpMat 𝒢 P (fun ω => a • (R * U ω * Q)) ω i j =
      (a • (R * Muon.Foundations.condExpMat 𝒢 P U ω * Q)) i j :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hent i j
  filter_upwards [hall] with ω hω
  ext i j
  exact hω i j

/-! ## Assembly of `lem:app-dyn-diffuse` -/

/-- The unstopped rotated block increment `Y_{b+1} − Y_b` with `Y_b = Σ_out^{1/2} Δ_{bL} Σ_in^{1/2}`. -/
private def dfX {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (S : DynSetup p P m n B) (b : ℕ) (ω : Ω) : Mat m n :=
  Arot S.C (dynDelta S ((b + 1) * blockLen B) ω - dynDelta S (b * blockLen B) ω)

private lemma diffuse_dfX_eq {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (b : ℕ) (ω : Ω) :
    dfX S b ω = (-(p.h / B)) • (rOut S.C * (∑ u ∈ Finset.range (blockLen B),
      dynUpd S (b * blockLen B + u) ω) * rIn S.C) := by
  unfold dfX
  have e : (b + 1) * blockLen B = b * blockLen B + blockLen B := by ring
  rw [e, diffuse_delta_add]
  unfold Arot
  rw [sub_sub_cancel_left]
  simp [Matrix.mul_smul, Matrix.smul_mul, neg_smul]

open scoped Matrix.Norms.L2Operator in
private lemma diffuse_cond_dfX {p : DynParams} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B) (b : ℕ)
    (hint : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω =>
      (∑ u ∈ Finset.range (blockLen B), dynUpd S (b * blockLen B + u) ω) i j) P) :
    ∀ᵐ ω ∂P, opNorm (Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P (dfX S b) ω) =
      p.h / B * opNorm (rOut S.C * Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P
        (fun ω' => ∑ u ∈ Finset.range (blockLen B), dynUpd S (b * blockLen B + u) ω') ω *
          rIn S.C) := by
  have hfun : dfX S b = fun ω => (-(p.h / B)) • (rOut S.C * (∑ u ∈ Finset.range (blockLen B),
      dynUpd S (b * blockLen B + u) ω) * rIn S.C) := funext (diffuse_dfX_eq S b)
  have h := diffuse_condExpMat_rot (dynPast S (b * blockLen B)) P (rOut S.C) (rIn S.C)
    (-(p.h / B)) (fun ω => ∑ u ∈ Finset.range (blockLen B), dynUpd S (b * blockLen B + u) ω) hint
  rw [hfun]
  filter_upwards [h] with ω hω
  rw [hω]
  have hnn : 0 ≤ p.h / (B : ℝ) := div_nonneg p.hh.le (Nat.cast_nonneg _)
  simp only [opNorm_eq_norm, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hnn]

open scoped Matrix.Norms.L2Operator in
private lemma diffuse_opNorm_add_le {m n : ℕ} (A B : Mat m n) :
    opNorm (A + B) ≤ opNorm A + opNorm B := by
  simpa only [opNorm_eq_norm] using norm_add_le A B

open scoped Matrix.Norms.L2Operator in
private lemma diffuse_opNorm_sum_le {m n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Mat m n) :
    opNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, opNorm (f i) := by
  simpa only [opNorm_eq_norm] using norm_sum_le s f

private lemma diffuse_dfX_tele {p : DynParams} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (S : DynSetup p P m n B) (ω : Ω) (j : ℕ) :
    Arot S.C (dynDelta S (j * blockLen B) ω) =
      Arot S.C (dynDelta S 0 ω) + ∑ b ∈ Finset.range j, dfX S b ω := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih]
      unfold dfX Arot
      rw [Matrix.mul_sub, Matrix.sub_mul]
      abel

private lemma diffuse_drift_abs (K r Y L buf lg Q : ℝ) (hY : 0 ≤ Y) (hL : 0 ≤ L)
    (hb : 0 ≤ buf) (hlg : 0 ≤ lg) (hQ : 0 ≤ Q) :
    K * L * (Y + r) + K * (buf + lg + Q) ≤ |K| * L * (Y + |r|) + |K| * (buf + lg + Q) := by
  have h1 : K * Y ≤ |K| * Y := mul_le_mul_of_nonneg_right (le_abs_self K) hY
  have h2 : K * r ≤ |K| * |r| := (le_abs_self _).trans (abs_mul K r).le
  have h3 : K * (buf + lg + Q) ≤ |K| * (buf + lg + Q) :=
    mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
  have h4 : K * L * (Y + r) = L * (K * Y + K * r) := by ring
  have h5 : |K| * L * (Y + |r|) = L * (|K| * Y + |K| * |r|) := by ring
  rw [h4, h5]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 h2) hL]

/-- (D1) The deterministic Gronwall consequence. -/
private lemma diffuse_gronwall_abstract (N : ℕ∞) (J : ℕ) (y w v q : ℕ → ℝ) (a ρ x : ℝ)
    (ha : 0 ≤ a) (hρ : 0 ≤ ρ) (hy : ∀ j, 0 ≤ y j) (hw : ∀ j, 0 ≤ w j) (hv : ∀ j, 0 ≤ v j)
    (hq : ∀ b, 0 ≤ q b)
    (h1 : ∀ j ≤ J, (j : ℕ∞) ≤ N → y j ≤ y 0 + ∑ b ∈ Finset.range j, w b + v j)
    (h2 : ∀ b < J, (b : ℕ∞) < N → w b ≤ a * y b + ρ + q b)
    (hvx : ∀ j ≤ J, v j < x)
    (hqx : ∑ b ∈ Finset.range J, (if (b : ℕ∞) < N then q b else 0) < x) :
    ∀ j ≤ J, (j : ℕ∞) ≤ N → y j ≤ (y 0 + J * ρ + 2 * x) * Real.exp (a * J) := by
  intro j hjJ hjN
  have hx0 : 0 ≤ x := (hv 0).trans (hvx 0 (Nat.zero_le _)).le
  have hA : 0 ≤ y 0 + J * ρ + 2 * x := by
    have := hy 0
    positivity
  let u : ℕ → ℝ := fun i => if i ≤ J ∧ (i : ℕ∞) ≤ N then y i else 0
  have hu0 : ∀ i, 0 ≤ u i := fun i => by
    simp only [u]
    split_ifs
    · exact hy i
    · exact le_rfl
  have hu : ∀ i, u i ≤ (y 0 + J * ρ + 2 * x) + a * ∑ b ∈ Finset.range i, u b := by
    intro i
    by_cases hc : i ≤ J ∧ (i : ℕ∞) ≤ N
    · have hui : u i = y i := by simp only [u, if_pos hc]
      rw [hui]
      have hbJ : ∀ b ∈ Finset.range i, b < J := fun b hb =>
        lt_of_lt_of_le (Finset.mem_range.mp hb) hc.1
      have hbN : ∀ b ∈ Finset.range i, (b : ℕ∞) < N := fun b hb =>
        lt_of_lt_of_le (by exact_mod_cast Finset.mem_range.mp hb) hc.2
      have hw' : ∑ b ∈ Finset.range i, w b ≤ ∑ b ∈ Finset.range i, (a * y b + ρ + q b) :=
        Finset.sum_le_sum fun b hb => h2 b (hbJ b hb) (hbN b hb)
      have hyu : ∑ b ∈ Finset.range i, y b = ∑ b ∈ Finset.range i, u b := by
        refine Finset.sum_congr rfl fun b hb => ?_
        have hbc : b ≤ J ∧ (b : ℕ∞) ≤ N := ⟨(hbJ b hb).le, (hbN b hb).le⟩
        simp only [u, if_pos hbc]
      have hqsum : ∑ b ∈ Finset.range i, q b ≤
          ∑ b ∈ Finset.range J, (if (b : ℕ∞) < N then q b else 0) := by
        calc
          ∑ b ∈ Finset.range i, q b =
              ∑ b ∈ Finset.range i, (if (b : ℕ∞) < N then q b else 0) :=
            Finset.sum_congr rfl fun b hb => by rw [if_pos (hbN b hb)]
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono hc.1) (fun b _ _ => by split_ifs <;> simp [hq b])
      have hsplit : ∑ b ∈ Finset.range i, (a * y b + ρ + q b) =
          a * ∑ b ∈ Finset.range i, y b + (i : ℝ) * ρ + ∑ b ∈ Finset.range i, q b := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
      have hiρ : (i : ℝ) * ρ ≤ J * ρ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hc.1) hρ
      have h1i := h1 i hc.1 hc.2
      have hvi := hvx i hc.1
      rw [hyu] at hsplit
      linarith
    · have hui : u i = 0 := by simp only [u, if_neg hc]
      rw [hui]
      have : 0 ≤ a * ∑ b ∈ Finset.range i, u b :=
        mul_nonneg ha (Finset.sum_nonneg fun b _ => hu0 b)
      linarith
  have hg := diffuse_discrete_gronwall hA ha hu j
  have huj : u j = y j := by simp only [u, if_pos (show j ≤ J ∧ (j : ℕ∞) ≤ N from ⟨hjJ, hjN⟩)]
  rw [huj] at hg
  refine hg.trans (mul_le_mul_of_nonneg_left ?_ hA)
  calc
    (1 + a) ^ j ≤ (Real.exp a) ^ j :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp a]) j
    _ = Real.exp (a * j) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (a * J) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hjJ) ha)

/-- (C) The martingale tail bound for the centred rotated block increments. -/
private lemma diffuse_mart_event {p : DynParams} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ}
    (S : DynSetup p P m n B) (x : ℝ) (hx : 0 < x) (J : ℕ) (hJ : 1 ≤ J) :
    P {ω | ∃ j ≤ J, x ≤ opNorm (∑ b ∈ Finset.range j,
        (dfX S b ω - Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P (dfX S b) ω))} ≤
      ENNReal.ofReal (2 * ((m + n : ℕ) : ℝ) * (J : ℝ) * Real.exp (-(x ^ 2) /
        (2 * (J : ℝ) * (2 * (p.CSig * p.h * (blockLen B : ℝ) / B)) ^ 2))) := by
  have hmono : Monotone (fun b : ℕ => dynPast S (b * blockLen B)) :=
    fun a b hab => diffuse_past_mono S (Nat.mul_le_mul_right _ hab)
  have hle : ∀ b : ℕ, dynPast S (b * blockLen B) ≤ ‹MeasurableSpace Ω› :=
    fun b => diffuse_past_le S _
  have hmeas : ∀ (b : ℕ) (i : Fin m) (j : Fin n),
      Measurable[dynPast S ((b + 1) * blockLen B)] (fun ω => dfX S b ω i j) := by
    intro b i j
    have h1 := diffuse_delta_meas S ((b + 1) * blockLen B)
    have h2 := (diffuse_delta_meas S (b * blockLen B)).mono
      (diffuse_past_mono S (Nat.mul_le_mul_right _ (Nat.le_succ b))) le_rfl
    have hc : Continuous (fun q : Mat m n × Mat m n => Arot S.C (q.1 - q.2)) := by
      unfold Arot
      fun_prop
    have := hc.measurable.comp (h1.prodMk h2)
    exact diffuse_entry_meas this i j
  have hc0 : 0 ≤ p.CSig * p.h * (blockLen B : ℝ) / B := by
    have := p.hC
    have := p.hh
    positivity
  have hbd : ∀ (b : ℕ) (ω : Ω), opNorm (dfX S b ω) ≤ p.CSig * p.h * (blockLen B : ℝ) / B := by
    intro b ω
    have h := diffuse_Arot_block_movement p S ω (b * blockLen B)
    have e : (b + 1) * blockLen B = b * blockLen B + blockLen B := by ring
    unfold dfX
    rw [e]
    exact h
  exact diffuse_mart_tail P (fun b => dynPast S (b * blockLen B)) hmono hle (dfX S) hmeas
    _ hc0 hbd x hx J hJ

private lemma diffuse_exit_lt_iff {α : Type*} (A : Set α) (Δ : ℕ → α) (t : ℕ) :
    (t : ℕ∞) < (⨅ (s : ℕ) (_ : Δ s ∉ A), (s : ℕ∞)) ↔ ∀ s ≤ t, Δ s ∈ A := by
  constructor
  · intro ht s hs
    by_contra hout
    have hle : (⨅ (s : ℕ) (_ : Δ s ∉ A), (s : ℕ∞)) ≤ (s : ℕ∞) :=
      iInf_le_of_le s (iInf_le_of_le hout le_rfl)
    exact (not_le_of_gt ht) (hle.trans (by exact_mod_cast hs))
  · intro h
    have hle : ((t + 1 : ℕ) : ℕ∞) ≤ (⨅ (s : ℕ) (_ : Δ s ∉ A), (s : ℕ∞)) := by
      refine le_iInf fun s => le_iInf fun hs => ?_
      exact_mod_cast Nat.succ_le_iff.mpr (lt_of_not_ge (fun hst => hs (h s hst)))
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self t) hle

private lemma diffuse_admSet_meas {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (t : ℕ) (K : ℝ × ℝ × ℝ) :
    MeasurableSet[dynPast S t] {ω | dynDelta S t ω ∈ admSetOf S.C K} := by
  have hD := diffuse_delta_meas S t
  have hr : Measurable[dynPast S t] (fun ω => riskSigma S.C (dynDelta S t ω)) := by
    exact (show Continuous (fun D : Mat m n => riskSigma S.C D) by
      unfold riskSigma pairSigma
      fun_prop).measurable.comp hD
  have hf : Measurable[dynPast S t] (fun ω => fro (dynDelta S t ω) ^ 2) := by
    apply (show Continuous (fun D : Mat m n => fro D ^ 2) by
      unfold fro
      fun_prop).measurable.comp hD
  change MeasurableSet[dynPast S t]
    ({ω | K.1 ≤ riskSigma S.C (dynDelta S t ω)} ∩
      ({ω | riskSigma S.C (dynDelta S t ω) ≤ K.2.1} ∩
        {ω | fro (dynDelta S t ω) ^ 2 ≤ K.2.2}))
  exact (measurableSet_le measurable_const hr).inter
    ((measurableSet_le hr measurable_const).inter (measurableSet_le hf measurable_const))

private lemma diffuse_geom_le {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (J : ℕ) :
    ∑ b ∈ Finset.range J, β ^ b ≤ 1 / (1 - β) := by
  have h := mul_neg_geom_sum β J
  have hpos : 0 < 1 - β := by linarith
  rw [le_div_iff₀ hpos, mul_comm]
  rw [h]
  have : 0 ≤ β ^ J := pow_nonneg h0 J
  linarith

private lemma diffuse_int_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (g : Ω → ℝ) (hg0 : ∀ ω, 0 ≤ g ω) (hint : Integrable g P)
    (hint2 : Integrable (fun ω => g ω ^ 2) P) (Q : ℝ) (hQ : 0 < Q)
    (h : ∫ ω, g ω ^ 2 ∂P ≤ Q) : ∫ ω, g ω ∂P ≤ Real.sqrt Q := by
  set s := Real.sqrt Q with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hQ
  have hss : s ^ 2 = Q := Real.sq_sqrt hQ.le
  have hpt : ∀ ω, g ω ≤ g ω ^ 2 / (2 * s) + s / 2 := by
    intro ω
    rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (g ω - s)]
  have h1 : ∫ ω, g ω ∂P ≤ ∫ ω, (g ω ^ 2 / (2 * s) + s / 2) ∂P :=
    integral_mono hint ((hint2.div_const _).add (integrable_const _)) hpt
  rw [integral_add (hint2.div_const _) (integrable_const _), integral_div,
    integral_const] at h1
  simp only [probReal_univ, smul_eq_mul, one_mul] at h1
  have h2 : (∫ ω, g ω ^ 2 ∂P) / (2 * s) ≤ Q / (2 * s) :=
    div_le_div_of_nonneg_right h (by positivity)
  have h3 : Q / (2 * s) = s / 2 := by
    rw [← hss]
    field_simp
  linarith

/-- (B) The `L¹` bound for the accumulated buffer terms, with Markov's inequality. -/
private lemma diffuse_buffer_markov (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∃ B0 : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (m n B : ℕ) (S : DynSetup p P m n B), B0 ≤ B →
      ∀ (J : ℕ) (a x : ℝ), 0 ≤ a → 0 < x →
        P {ω | x ≤ ∑ b ∈ Finset.range J, if (b : ℕ∞) < dynBlockIndexExit S ω then
            a * opNorm (dynBuf S (b * blockLen B) ω) else 0} ≤
          ENNReal.ofReal (a * (Real.sqrt (2 * p.cM * B) / (1 - p.β) +
            J * K * Real.log (2 * (B : ℝ))) / x) := by
  have hr0 : 0 < p.r0 / 2 := by linarith [p.hr0]
  have hle0 : p.r0 / 2 ≤ p.r1 + 1 / 2 := by linarith [p.hr, p.hr0]
  obtain ⟨Bm, hmove⟩ :=
    lem_app_dyn_movement_ii p (p.r0 / 2) (p.r1 + 1 / 2) (p.Estar + 1) hr0 hle0
  have hr1 : 0 < (enl (admBase p)).1 := by
    simp only [enl, admBase]
    linarith [p.hr0]
  have hle1 : (enl (admBase p)).1 ≤ (enl (admBase p)).2.1 := by
    simp only [enl, admBase]
    linarith [p.hr, p.hr0]
  obtain ⟨K2, hbuf⟩ := lem_app_dyn_buffer_ii certOp p (enl (admBase p)).1
    (enl (admBase p)).2.1 (enl (admBase p)).2.2 hr1 hle1
  refine ⟨max Bm 1, Real.sqrt (max K2 1), Real.sqrt_nonneg _, ?_⟩
  intro Ω _ P _ m n B S hB J a x ha hx
  have hBm : Bm ≤ B := (le_max_left _ _).trans hB
  have hB1 : 1 ≤ B := (le_max_right _ _).trans hB
  have hB1R : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hBpos : (0 : ℝ) < B := by linarith
  have hLpos : 0 < blockLen B := diffuse_blockLen_pos hB1
  have hlgpos : 0 < Real.log (2 * (B : ℝ)) := Real.log_pos (by linarith)
  -- the exit time τ from 𝒜⁺
  set τ : Ω → ℕ∞ := fun ω =>
    ⨅ (s : ℕ) (_ : dynDelta S s ω ∉ admSetOf S.C (enl (admBase p))), (s : ℕ∞) with hτdef
  have hτ1 : ∀ t : ℕ, MeasurableSet[dynPast S t] {ω | (t : ℕ∞) < τ ω} := by
    intro t
    have : {ω | (t : ℕ∞) < τ ω} = ⋂ s ∈ Finset.range (t + 1),
        {ω | dynDelta S s ω ∈ admSetOf S.C (enl (admBase p))} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range, Nat.lt_add_one_iff]
      exact diffuse_exit_lt_iff _ (fun s => dynDelta S s ω) t
    rw [this]
    refine (Finset.range (t + 1)).measurableSet_biInter fun s hs => ?_
    exact diffuse_past_mono S (by have := Finset.mem_range.mp hs; omega) _
      (diffuse_admSet_meas S s _)
  have hτ2 : ∀ (t : ℕ) (ω : Ω), (t : ℕ∞) < τ ω →
      dynDelta S t ω ∈ admSetOf S.C (enl (admBase p)) :=
    fun t ω h => (diffuse_exit_lt_iff _ (fun s => dynDelta S s ω) t).mp h t le_rfl
  have hbuf' := hbuf Ω P m n B S τ hτ1 hτ2
  -- before the block exit, the process stays in 𝒜⁺ up to the block start
  have hind : ∀ (b : ℕ) (ω : Ω), (b : ℕ∞) < dynBlockIndexExit S ω →
      ((b * blockLen B : ℕ) : ℕ∞) ≤ τ ω := by
    intro b ω hb
    refine le_of_lt ((diffuse_exit_lt_iff _ (fun s => dynDelta S s ω) _).mpr fun s hs => ?_)
    have hab : s / blockLen B ≤ b := Nat.div_le_of_le_mul (by rw [mul_comm]; exact hs)
    have hbc : ((s / blockLen B : ℕ) : ℕ∞) < dynBlockIndexExit S ω :=
      lt_of_le_of_lt (by exact_mod_cast hab) hb
    have hA := diffuse_before_exit_adm S ω (s / blockLen B) hbc
    refine (hmove Ω P m n B S hBm ω (s / blockLen B * blockLen B) hA).2 s ?_
    have h1 : s / blockLen B * blockLen B ≤ s := Nat.div_mul_le_self s (blockLen B)
    have h2 : s < s / blockLen B * blockLen B + blockLen B := by
      have := Nat.mod_lt s hLpos
      have h3 := Nat.div_add_mod s (blockLen B)
      rw [mul_comm] at h3
      omega
    have h1' : ((s / blockLen B * blockLen B : ℕ) : ℤ) ≤ (s : ℤ) := by exact_mod_cast h1
    rw [abs_of_nonneg (by linarith)]
    have : (s : ℤ) < ((s / blockLen B * blockLen B : ℕ) : ℤ) + (blockLen B : ℤ) := by
      exact_mod_cast h2
    have : (0 : ℤ) ≤ blockLen B := Int.natCast_nonneg _
    linarith
  -- the truncated norms
  set g : ℕ → Ω → ℝ := fun b ω => Real.sqrt ({ω | ((b * blockLen B : ℕ) : ℕ∞) ≤ τ ω}.indicator
      (fun ω => opNorm (dynBuf S (b * blockLen B) ω) ^ 2) ω) with hgdef
  have hg0 : ∀ b ω, 0 ≤ g b ω := fun b ω => Real.sqrt_nonneg _
  have hg2 : ∀ b ω, g b ω ^ 2 = {ω | ((b * blockLen B : ℕ) : ℕ∞) ≤ τ ω}.indicator
      (fun ω => opNorm (dynBuf S (b * blockLen B) ω) ^ 2) ω := by
    intro b ω
    simp only [hgdef]
    rw [Real.sq_sqrt]
    exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
  have hgint2 : ∀ b, Integrable (fun ω => g b ω ^ 2) P := by
    intro b
    have := (hbuf' (b * blockLen B)).1
    refine this.congr (ae_of_all _ fun ω => ?_)
    exact (hg2 b ω).symm
  have hgint : ∀ b, Integrable (g b) P := by
    intro b
    refine Integrable.mono' ((hgint2 b).add (integrable_const 1))
      (Real.continuous_sqrt.comp_aestronglyMeasurable (hbuf' (b * blockLen B)).1.aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 b ω), Pi.add_apply]
    nlinarith [sq_nonneg (g b ω - 1), hg0 b ω]
  have hcM := p.hcM
  have hβ0 := p.hβ.1
  have hβ1 := p.hβ.2
  have hgint_le : ∀ b, ∫ ω, g b ω ∂P ≤ p.β ^ b * Real.sqrt (2 * p.cM * B) +
      Real.sqrt (max K2 1) * Real.log (2 * (B : ℝ)) := by
    intro b
    obtain ⟨_, hI⟩ := hbuf' (b * blockLen B)
    set t := b * blockLen B with ht
    have hmax : (0 : ℝ) < max K2 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hQpos : 0 < 2 * p.β ^ (2 * t) * (p.cM * B) + max K2 1 * Real.log (2 * (B : ℝ)) ^ 2 :=
      add_pos_of_nonneg_of_pos (by positivity) (mul_pos hmax (pow_pos hlgpos 2))
    have hle : ∫ ω, g b ω ^ 2 ∂P ≤
        2 * p.β ^ (2 * t) * (p.cM * B) + max K2 1 * Real.log (2 * (B : ℝ)) ^ 2 := by
      have e : (fun ω => g b ω ^ 2) = {ω | (t : ℕ∞) ≤ τ ω}.indicator
          (fun ω => opNorm (dynBuf S t ω) ^ 2) := funext (hg2 b)
      rw [e]
      refine hI.trans ?_
      have : K2 * Real.log (2 * (B : ℝ)) ^ 2 ≤ max K2 1 * Real.log (2 * (B : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      linarith
    have h1 := diffuse_int_le_sqrt (g b) (hg0 b) (hgint b) (hgint2 b) _ hQpos hle
    have hA0 : 0 ≤ p.β ^ t * Real.sqrt (2 * p.cM * B) := by positivity
    have hC0 : 0 ≤ Real.sqrt (max K2 1) * Real.log (2 * (B : ℝ)) := by positivity
    have h2 : Real.sqrt (2 * p.β ^ (2 * t) * (p.cM * B) + max K2 1 * Real.log (2 * (B : ℝ)) ^ 2) ≤
        p.β ^ t * Real.sqrt (2 * p.cM * B) + Real.sqrt (max K2 1) * Real.log (2 * (B : ℝ)) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have e1 : (p.β ^ t * Real.sqrt (2 * p.cM * B)) ^ 2 = 2 * p.β ^ (2 * t) * (p.cM * B) := by
        rw [mul_pow, Real.sq_sqrt (by positivity), mul_comm 2 t, pow_mul]
        ring
      have e2 : (Real.sqrt (max K2 1) * Real.log (2 * (B : ℝ))) ^ 2 =
          max K2 1 * Real.log (2 * (B : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hmax.le]
      nlinarith [mul_nonneg hA0 hC0]
    have h3 : p.β ^ t ≤ p.β ^ b :=
      pow_le_pow_of_le_one hβ0 hβ1.le (Nat.le_mul_of_pos_right b hLpos)
    have h4 : p.β ^ t * Real.sqrt (2 * p.cM * B) ≤ p.β ^ b * Real.sqrt (2 * p.cM * B) :=
      mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
    linarith
  have hFle : ∀ ω, (∑ b ∈ Finset.range J, if (b : ℕ∞) < dynBlockIndexExit S ω then
      a * opNorm (dynBuf S (b * blockLen B) ω) else 0) ≤ ∑ b ∈ Finset.range J, a * g b ω := by
    intro ω
    refine Finset.sum_le_sum fun b _ => ?_
    split_ifs with h
    · have hm : ω ∈ {ω | ((b * blockLen B : ℕ) : ℕ∞) ≤ τ ω} := hind b ω h
      have : g b ω = opNorm (dynBuf S (b * blockLen B) ω) := by
        simp only [hgdef, Set.indicator_of_mem hm]
        exact Real.sqrt_sq (diffuse_opNorm_nonneg _)
      rw [this]
    · exact mul_nonneg ha (hg0 b ω)
  set F' : Ω → ℝ := fun ω => ∑ b ∈ Finset.range J, a * g b ω with hF'
  have hF'int : Integrable F' P := integrable_finset_sum _ fun b _ => (hgint b).const_mul a
  have hF'nn : 0 ≤ᵐ[P] F' :=
    ae_of_all _ fun ω => Finset.sum_nonneg fun b _ => mul_nonneg ha (hg0 b ω)
  have hM := mul_meas_ge_le_integral_of_nonneg hF'nn hF'int x
  have hint_le : ∫ ω, F' ω ∂P ≤ a * (Real.sqrt (2 * p.cM * B) / (1 - p.β) +
      J * Real.sqrt (max K2 1) * Real.log (2 * (B : ℝ))) := by
    have hgeom := diffuse_geom_le hβ0 p.hβ.2 J
    have hA : 0 ≤ Real.sqrt (2 * p.cM * B) := Real.sqrt_nonneg _
    calc ∫ ω, F' ω ∂P = ∑ b ∈ Finset.range J, a * ∫ ω, g b ω ∂P := by
          rw [hF', integral_finset_sum _ (fun b _ => (hgint b).const_mul a)]
          simp only [integral_const_mul]
      _ ≤ ∑ b ∈ Finset.range J, a * (p.β ^ b * Real.sqrt (2 * p.cM * B) +
            Real.sqrt (max K2 1) * Real.log (2 * (B : ℝ))) :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hgint_le b) ha
      _ = a * (Real.sqrt (2 * p.cM * B) * ∑ b ∈ Finset.range J, p.β ^ b +
            J * Real.sqrt (max K2 1) * Real.log (2 * (B : ℝ))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul]
          ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ ha
          have := mul_le_mul_of_nonneg_left hgeom hA
          rw [mul_one_div] at this
          linarith
  calc P {ω | x ≤ ∑ b ∈ Finset.range J, if (b : ℕ∞) < dynBlockIndexExit S ω then
          a * opNorm (dynBuf S (b * blockLen B) ω) else 0}
      ≤ P {ω | x ≤ F' ω} := measure_mono fun ω h => h.trans (hFle ω)
    _ = ENNReal.ofReal (P.real {ω | x ≤ F' ω}) := by
        rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        rw [le_div_iff₀ hx]
        nlinarith [hM, hint_le])

/-- (A + D2) Drift, martingale decomposition and Gronwall on a fixed model. -/
private lemma diffuse_good_bound {p : DynParams} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (S : DynSetup p P m n B)
    (K r : ℝ) (hB : 1 ≤ B)
    (hint : ∀ t : ℕ, ∀ (i : Fin m) (j : Fin n),
      Integrable (fun ω => (∑ u ∈ Finset.range (blockLen B), dynUpd S (t + u) ω) i j) P)
    (hdrift : ∀ t : ℕ, ∀ᵐ ω ∂P, ω ∈ dynInK S t (admBase p) →
      opNorm (rOut S.C * Muon.Foundations.condExpMat (dynPast S t) P
          (fun ω' => ∑ u ∈ Finset.range (blockLen B), dynUpd S (t + u) ω') ω * rIn S.C) ≤
        K * (blockLen B : ℝ) * (opNorm (rOut S.C * dynDelta S t ω * rIn S.C) + r) +
          K * (opNorm (dynBuf S t ω) + Real.log (2 * (B : ℝ)) +
            (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ)))
    (J : ℕ) (x : ℝ) :
    ∀ᵐ ω ∂P, (¬ ∃ j ≤ J, x ≤ opNorm (∑ b ∈ Finset.range j,
        (dfX S b ω - Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P (dfX S b) ω))) →
      (∑ b ∈ Finset.range J, if (b : ℕ∞) < dynBlockIndexExit S ω then
          p.h / B * |K| * opNorm (dynBuf S (b * blockLen B) ω) else 0) < x →
      ∀ j ≤ J, (j : ℕ∞) ≤ dynBlockIndexExit S ω →
        opNorm (Arot S.C (dynDelta S (j * blockLen B) ω)) ≤
          (opNorm (Arot S.C (dynDelta S 0 ω)) +
            J * (p.h * |K| * blockLen B / B * |r| + p.h * |K| / B *
              (Real.log (2 * (B : ℝ)) + (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) /
                Real.sqrt (B : ℝ))) + 2 * x) * Real.exp (p.h * |K| * blockLen B / B * J) := by
  classical
  have hB1R : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBpos : (0 : ℝ) < B := by linarith
  have hlg : 0 ≤ Real.log (2 * (B : ℝ)) := Real.log_nonneg (by linarith)
  have hQ : 0 ≤ (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ) := by
    positivity
  have hhB : 0 ≤ p.h / (B : ℝ) := div_nonneg p.hh.le hBpos.le
  have hae : ∀ᵐ ω ∂P, ∀ b : ℕ,
      (opNorm (Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P (dfX S b) ω) =
        p.h / B * opNorm (rOut S.C * Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P
          (fun ω' => ∑ u ∈ Finset.range (blockLen B), dynUpd S (b * blockLen B + u) ω') ω *
            rIn S.C)) ∧
      (ω ∈ dynInK S (b * blockLen B) (admBase p) →
        opNorm (rOut S.C * Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P
          (fun ω' => ∑ u ∈ Finset.range (blockLen B), dynUpd S (b * blockLen B + u) ω') ω *
            rIn S.C) ≤
        K * (blockLen B : ℝ) * (opNorm (rOut S.C * dynDelta S (b * blockLen B) ω * rIn S.C) + r) +
          K * (opNorm (dynBuf S (b * blockLen B) ω) + Real.log (2 * (B : ℝ)) +
            (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ))) := by
    rw [ae_all_iff]
    intro b
    filter_upwards [diffuse_cond_dfX S b (hint (b * blockLen B)), hdrift (b * blockLen B)]
      with ω h1 h2 using ⟨h1, h2⟩
  filter_upwards [hae] with ω hω hn1 hn2
  set N : ℕ∞ := dynBlockIndexExit S ω with hN
  have hcond : ∀ b : ℕ, (b : ℕ∞) < N → opNorm (Muon.Foundations.condExpMat
      (dynPast S (b * blockLen B)) P (dfX S b) ω) ≤
      p.h * |K| * blockLen B / B * opNorm (Arot S.C (dynDelta S (b * blockLen B) ω)) +
        (p.h * |K| * blockLen B / B * |r| + p.h * |K| / B *
          (Real.log (2 * (B : ℝ)) + (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) /
            Real.sqrt (B : ℝ))) + p.h / B * |K| * opNorm (dynBuf S (b * blockLen B) ω) := by
    intro b hb
    obtain ⟨e1, e2⟩ := hω b
    have hadm : ω ∈ dynInK S (b * blockLen B) (admBase p) :=
      diffuse_before_exit_adm S ω b hb
    have h3 := e2 hadm
    have h4 := diffuse_drift_abs K r (opNorm (rOut S.C * dynDelta S (b * blockLen B) ω * rIn S.C))
      (blockLen B : ℝ) (opNorm (dynBuf S (b * blockLen B) ω)) (Real.log (2 * (B : ℝ)))
      ((blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ))
      (diffuse_opNorm_nonneg _) (Nat.cast_nonneg _) (diffuse_opNorm_nonneg _) hlg hQ
    rw [e1]
    have h5 := mul_le_mul_of_nonneg_left (h3.trans h4) hhB
    refine h5.trans (le_of_eq ?_)
    unfold Arot
    ring
  have hA0 : 0 ≤ p.h * |K| * blockLen B / B := by
    have := p.hh
    positivity
  have hρ0 : 0 ≤ p.h * |K| * blockLen B / B * |r| + p.h * |K| / B *
      (Real.log (2 * (B : ℝ)) + (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) /
        Real.sqrt (B : ℝ)) := by
    have := p.hh
    positivity
  have hD := diffuse_gronwall_abstract N J
    (fun j => opNorm (Arot S.C (dynDelta S (j * blockLen B) ω)))
    (fun b => opNorm (Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P (dfX S b) ω))
    (fun j => opNorm (∑ b ∈ Finset.range j,
        (dfX S b ω - Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P (dfX S b) ω)))
    (fun b => p.h / B * |K| * opNorm (dynBuf S (b * blockLen B) ω))
    (p.h * |K| * blockLen B / B)
    (p.h * |K| * blockLen B / B * |r| + p.h * |K| / B *
      (Real.log (2 * (B : ℝ)) + (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) /
        Real.sqrt (B : ℝ))) x hA0 hρ0
    (fun _ => diffuse_opNorm_nonneg _) (fun _ => diffuse_opNorm_nonneg _)
    (fun _ => diffuse_opNorm_nonneg _)
    (fun b => by
      have := p.hh
      have := diffuse_opNorm_nonneg (dynBuf S (b * blockLen B) ω)
      positivity)
    (fun j _ _ => by
      show opNorm (Arot S.C (dynDelta S (j * blockLen B) ω)) ≤
        opNorm (Arot S.C (dynDelta S (0 * blockLen B) ω)) +
          ∑ b ∈ Finset.range j, opNorm (Muon.Foundations.condExpMat
            (dynPast S (b * blockLen B)) P (dfX S b) ω) +
          opNorm (∑ b ∈ Finset.range j,
            (dfX S b ω - Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P (dfX S b) ω))
      have e0 : (0 : ℕ) * blockLen B = 0 := Nat.zero_mul _
      rw [e0]
      have hsplit : ∑ b ∈ Finset.range j, dfX S b ω =
          ∑ b ∈ Finset.range j, Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P
            (dfX S b) ω +
          ∑ b ∈ Finset.range j,
            (dfX S b ω - Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P
              (dfX S b) ω) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => by abel
      rw [diffuse_dfX_tele S ω j, hsplit, ← add_assoc]
      refine (diffuse_opNorm_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (diffuse_opNorm_add_le _ _).trans (add_le_add le_rfl ?_)
      exact diffuse_opNorm_sum_le _ _)
    (fun b _ hb => hcond b hb)
    (fun j hj => lt_of_not_ge fun h => hn1 ⟨j, hj, h⟩)
    hn2
  intro j hj hjN
  have := hD j hj hjN
  have e0 : (0 : ℕ) * blockLen B = 0 := Nat.zero_mul _
  simp only [e0] at this
  exact this

/-- `L ≤ B`. -/
private lemma diffuse_blockLen_le {B : ℕ} (hB : 1 ≤ B) : (blockLen B : ℝ) ≤ B := by
  have h1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  unfold blockLen
  calc
    ((⌊(B : ℝ) ^ ((1 : ℝ) / 8)⌋₊ : ℕ) : ℝ) ≤ (B : ℝ) ^ ((1 : ℝ) / 8) :=
      Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    _ ≤ (B : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    _ = B := Real.rpow_one _

/-- The geometry of the last step: a bad time produces a bad block start. -/
private lemma diffuse_bad_to_block {p : DynParams} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ} (S : DynSetup p P m n B) (hB : 1 ≤ B)
    (hrisk : ∀ (ω : Ω) (t : ℕ), (t : ℕ∞) ≤ dynBlockExitTime S ω →
      p.r0 / 4 ≤ riskSigma S.C (dynDelta S t ω))
    (T ε : ℝ) (hT : 0 < T) (ω : Ω) (t : ℕ)
    (ht1 : (t : ℕ∞) ≤ dynBlockExitTime S ω) (ht2 : (t : ℝ) ≤ T * B)
    (hε : ε < diffuseness S.C (dynDelta S t ω)) :
    ∃ j : ℕ, j ≤ ⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ ∧ (j : ℕ∞) ≤ dynBlockIndexExit S ω ∧
      ε * Real.sqrt (p.r0 / 2) <
        opNorm (Arot S.C (dynDelta S (j * blockLen B) ω)) +
          p.CSig * p.h * (blockLen B : ℝ) / B := by
  have hBpos : 0 < B := hB
  have hLpos : 0 < blockLen B := diffuse_blockLen_pos hBpos
  have hLposR : (0 : ℝ) < (blockLen B : ℝ) := by exact_mod_cast hLpos
  have hBposR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hBpos
  refine ⟨t / blockLen B, ?_, ?_, ?_⟩
  · have h1 : (((t / blockLen B : ℕ)) : ℝ) ≤ (t : ℝ) / (blockLen B : ℝ) := Nat.cast_div_le
    have h2 : (t : ℝ) / (blockLen B : ℝ) ≤ T * (B : ℝ) / (blockLen B : ℝ) :=
      div_le_div_of_nonneg_right ht2 hLposR.le
    have h3 := Nat.le_ceil (T * (B : ℝ) / (blockLen B : ℝ))
    exact_mod_cast h1.trans (h2.trans h3)
  · by_cases htop : dynBlockIndexExit S ω = ⊤
    · rw [htop]
      exact le_top
    · obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp htop
      have htcb : t ≤ blockLen B * c := by
        rw [dynBlockExitTime, ← hc, ← ENat.coe_mul] at ht1
        exact ENat.coe_le_coe.mp ht1
      rw [← hc]
      exact ENat.coe_le_coe.mpr (Nat.div_le_of_le_mul htcb)
  · have hjt : t / blockLen B * blockLen B ≤ t := Nat.div_mul_le_self t (blockLen B)
    have hrem : t - t / blockLen B * blockLen B < blockLen B := by
      have := Nat.mod_lt t hLpos
      have h2 := Nat.div_add_mod t (blockLen B)
      rw [mul_comm] at h2
      omega
    have hmove := diffuse_Arot_movement p S ω (t / blockLen B * blockLen B) t hjt
    have hcast : (t : ℝ) - ((t / blockLen B * blockLen B : ℕ) : ℝ) ≤ (blockLen B : ℝ) := by
      have : ((t - t / blockLen B * blockLen B : ℕ) : ℝ) ≤ (blockLen B : ℝ) := by
        exact_mod_cast hrem.le
      rwa [Nat.cast_sub hjt] at this
    have hmove' : opNorm (Arot S.C (dynDelta S t ω -
        dynDelta S (t / blockLen B * blockLen B) ω)) ≤ p.CSig * p.h * (blockLen B : ℝ) / B := by
      refine hmove.trans ?_
      apply div_le_div_of_nonneg_right _ hBposR.le
      exact mul_le_mul_of_nonneg_left hcast (mul_nonneg (le_trans (by norm_num) p.hC) p.hh.le)
    have hlin : Arot S.C (dynDelta S t ω) =
        Arot S.C (dynDelta S (t / blockLen B * blockLen B) ω) +
          Arot S.C (dynDelta S t ω - dynDelta S (t / blockLen B * blockLen B) ω) := by
      unfold Arot
      rw [Matrix.mul_sub, Matrix.sub_mul]
      abel
    have htri : opNorm (Arot S.C (dynDelta S t ω)) ≤
        opNorm (Arot S.C (dynDelta S (t / blockLen B * blockLen B) ω)) +
          opNorm (Arot S.C (dynDelta S t ω - dynDelta S (t / blockLen B * blockLen B) ω)) := by
      rw [hlin]
      open scoped Matrix.Norms.L2Operator in
      simpa only [opNorm_eq_norm] using norm_add_le _ _
    have hr4 : 0 < p.r0 / 4 := by linarith [p.hr0]
    have hdel := diffuse_le_rot_div_sqrt S.C (dynDelta S t ω) hr4 (hrisk ω t ht1)
    have hsq : Real.sqrt (2 * (p.r0 / 4)) = Real.sqrt (p.r0 / 2) := by
      congr 1
      ring
    rw [hsq] at hdel
    have hs0 : 0 < Real.sqrt (p.r0 / 2) := Real.sqrt_pos.mpr (by linarith [p.hr0])
    have hlt : ε < opNorm (Arot S.C (dynDelta S t ω)) / Real.sqrt (p.r0 / 2) :=
      lt_of_lt_of_le hε hdel
    rw [lt_div_iff₀ hs0] at hlt
    linarith

/-- `a J ≤ h K (T+1)`. -/
private lemma diffuse_aJ_le (T h K : ℝ) (hT : 0 < T) (hh : 0 < h) (hK : 0 ≤ K) {B : ℕ}
    (hB : 1 ≤ B) :
    h * K * (blockLen B : ℝ) / (B : ℝ) * ((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ) ≤
      h * K * (T + 1) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hLpos : (0 : ℝ) < (blockLen B : ℝ) := by exact_mod_cast diffuse_blockLen_pos hB
  have hLB := diffuse_blockLen_le hB
  have hJ : ((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ) ≤ T * B / blockLen B + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hhK : 0 ≤ h * K := mul_nonneg hh.le hK
  calc
    h * K * (blockLen B : ℝ) / (B : ℝ) * ((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ)
        ≤ h * K * (blockLen B : ℝ) / (B : ℝ) * (T * B / blockLen B + 1) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = h * K * (T + (blockLen B : ℝ) / B) := by
      field_simp
    _ ≤ h * K * (T + 1) := by
      apply mul_le_mul_of_nonneg_left _ hhK
      have : (blockLen B : ℝ) / B ≤ 1 := (div_le_one hBpos).mpr hLB
      linarith

/-- Bounds on the block length. -/
private lemma diffuse_L_bounds {B : ℕ} (hB : 256 ≤ B) :
    (B : ℝ) ^ ((1 : ℝ) / 8) / 2 ≤ (blockLen B : ℝ) ∧
      (blockLen B : ℝ) ≤ (B : ℝ) ^ ((1 : ℝ) / 8) := by
  have hB1 : (256 : ℝ) ≤ B := by exact_mod_cast hB
  have hy : (2 : ℝ) ≤ (B : ℝ) ^ ((1 : ℝ) / 8) := by
    have : (256 : ℝ) ^ ((1 : ℝ) / 8) ≤ (B : ℝ) ^ ((1 : ℝ) / 8) :=
      Real.rpow_le_rpow (by norm_num) hB1 (by norm_num)
    have h2 : (256 : ℝ) ^ ((1 : ℝ) / 8) = 2 := by
      rw [show (256 : ℝ) = 2 ^ (8 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  unfold blockLen
  constructor
  · have := Nat.lt_floor_add_one ((B : ℝ) ^ ((1 : ℝ) / 8))
    linarith
  · exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)


private lemma diffuse_log_rpow_tendsto :
    Tendsto (fun B : ℕ => Real.log (2 * (B : ℝ)) * (B : ℝ) ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 8 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => x ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have h3 : Tendsto (fun x : ℝ => Real.log 2 * x ^ (-(1 / 8 : ℝ)) + Real.log x / x ^ (1 / 8 : ℝ))
      atTop (𝓝 0) := by simpa using (h2.const_mul (Real.log 2)).add h1
  have h4 : Tendsto (fun x : ℝ => Real.log (2 * x) * x ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) := by
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.log_mul (by norm_num) hx.ne', Real.rpow_neg hx.le]
    ring
  exact h4.comp tendsto_natCast_atTop_atTop

/-- `L/B ≤ B^{-1/8}`. -/
private lemma diffuse_L_div_le {B : ℕ} (hB : 256 ≤ B) :
    (blockLen B : ℝ) / B ≤ (B : ℝ) ^ (-(1 / 8 : ℝ)) := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (le_trans (by norm_num) hB)
  have hBpos : (0 : ℝ) < B := by linarith
  have hL := (diffuse_L_bounds hB).2
  have h1 : (B : ℝ) ^ ((1 : ℝ) / 8) / B ≤ (B : ℝ) ^ (-(1 / 8 : ℝ)) := by
    have h2 : (B : ℝ) ^ ((1 : ℝ) / 8) / B = (B : ℝ) ^ (-(7 / 8 : ℝ)) := by
      rw [show (-(7 / 8 : ℝ)) = (1 : ℝ) / 8 - 1 by norm_num, Real.rpow_sub_one hBpos.ne']
    rw [h2]
    exact Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
  exact (div_le_div_of_nonneg_right hL hBpos.le).trans h1

/-- `J/B ≤ (2T+1) B^{-1/8}`. -/
private lemma diffuse_J_div_le (T : ℝ) (hT : 0 < T) {B : ℕ} (hB : 256 ≤ B) :
    ((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ) / B ≤ (2 * T + 1) * (B : ℝ) ^ (-(1 / 8 : ℝ)) := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (le_trans (by norm_num) hB)
  have hBpos : (0 : ℝ) < B := by linarith
  obtain ⟨hL1, hL2⟩ := diffuse_L_bounds hB
  set y : ℝ := (B : ℝ) ^ ((1 : ℝ) / 8) with hy
  have hy2 : (2 : ℝ) ≤ y := by
    have : (256 : ℝ) ^ ((1 : ℝ) / 8) ≤ (B : ℝ) ^ ((1 : ℝ) / 8) :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hB) (by norm_num)
    have h2 : (256 : ℝ) ^ ((1 : ℝ) / 8) = 2 := by
      rw [show (256 : ℝ) = 2 ^ (8 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have hypos : 0 < y := by linarith
  have hyB : y ≤ B := by
    calc y ≤ (B : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
      _ = B := Real.rpow_one _
  have hLpos : (0 : ℝ) < (blockLen B : ℝ) := by linarith
  have hJ : ((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ) ≤ T * B / blockLen B + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hneg : (B : ℝ) ^ (-(1 / 8 : ℝ)) = y⁻¹ := by
    rw [hy, ← Real.rpow_neg hBpos.le]
  rw [hneg]
  have h1 : T * B / blockLen B ≤ 2 * T * B / y := by
    rw [div_le_div_iff₀ hLpos hypos]
    nlinarith [mul_pos hT hBpos]
  have h2 : (1 : ℝ) ≤ B / y := by rw [le_div_iff₀ hypos]; linarith
  calc
    ((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ) / B ≤ (2 * T * B / y + 1) / B :=
      div_le_div_of_nonneg_right (hJ.trans (by linarith)) hBpos.le
    _ = 2 * T * y⁻¹ + 1 / B := by field_simp
    _ ≤ (2 * T + 1) * y⁻¹ := by
      have : 1 / (B : ℝ) ≤ y⁻¹ := by
        rw [one_div]
        exact inv_anti₀ hypos hyB
      nlinarith


private lemma diffuse_L4_le {B : ℕ} (hB : 256 ≤ B) : (blockLen B : ℝ) ^ 4 ≤ B := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (le_trans (by norm_num) hB)
  have hBpos : (0 : ℝ) < B := by linarith
  obtain ⟨_, hL2⟩ := diffuse_L_bounds hB
  set y : ℝ := (B : ℝ) ^ ((1 : ℝ) / 8) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hB1 (by norm_num)
  have hy8 : y ^ 8 = B := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hBpos.le]
    norm_num
  calc
    (blockLen B : ℝ) ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hL2 4
    _ ≤ y ^ 8 := pow_le_pow_right₀ hy1 (by norm_num)
    _ = B := hy8

private lemma diffuse_L2_le_sqrt {B : ℕ} (hB : 256 ≤ B) :
    (blockLen B : ℝ) ^ 2 ≤ Real.sqrt B := by
  apply Real.le_sqrt_of_sq_le
  have h4 := diffuse_L4_le hB
  calc ((blockLen B : ℝ) ^ 2) ^ 2 = (blockLen B : ℝ) ^ 4 := by ring
    _ ≤ (B : ℝ) := h4

private lemma diffuse_det_bound (T h K : ℝ) (hT : 0 < T) (hh : 0 < h) (hK : 0 ≤ K) {B : ℕ}
    (hB : 256 ≤ B) (rho : ℝ) :
    |((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ) *
      (h * K * (blockLen B : ℝ) / (B : ℝ) * rho + h * K / (B : ℝ) *
        (Real.log (2 * (B : ℝ)) + (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) /
          Real.sqrt (B : ℝ)))| ≤
      h * K * (T + 1) * |rho| +
        2 * (h * K * (2 * T + 1)) * (Real.log (2 * (B : ℝ)) * (B : ℝ) ^ (-(1 / 8 : ℝ))) := by
  have hB1' : 1 ≤ B := le_trans (by norm_num) hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB1'
  have hBpos : (0 : ℝ) < B := by linarith
  have hlg : 0 ≤ Real.log (2 * (B : ℝ)) := Real.log_nonneg (by linarith)
  have hJ0 : (0 : ℝ) ≤ ((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  set J : ℝ := ((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ) with hJ
  have hhK : 0 ≤ h * K := mul_nonneg hh.le hK
  have haJ := diffuse_aJ_le T h K hT hh hK hB1'
  have hJB := diffuse_J_div_le T hT hB
  have hL2 := diffuse_L2_le_sqrt hB
  have hsq : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBpos
  have hratio : (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ) ≤
      Real.log (2 * (B : ℝ)) := by
    rw [div_le_iff₀ hsq]
    nlinarith
  have hratio0 : 0 ≤ (blockLen B : ℝ) ^ 2 * Real.log (2 * (B : ℝ)) / Real.sqrt (B : ℝ) := by
    positivity
  set lg : ℝ := Real.log (2 * (B : ℝ)) with hlgdef
  set u : ℝ := (B : ℝ) ^ (-(1 / 8 : ℝ)) with hu
  have hJb : J * (h * K / B) ≤ h * K * (2 * T + 1) * u := by
    have : J * (h * K / B) = h * K * (J / B) := by ring
    rw [this]
    calc h * K * (J / B) ≤ h * K * ((2 * T + 1) * u) := mul_le_mul_of_nonneg_left hJB hhK
      _ = _ := by ring
  have habs : |J * (h * K * (blockLen B : ℝ) / (B : ℝ) * rho + h * K / (B : ℝ) *
        (lg + (blockLen B : ℝ) ^ 2 * lg / Real.sqrt (B : ℝ)))| ≤
      J * (h * K * (blockLen B : ℝ) / (B : ℝ)) * |rho| +
        J * (h * K / B) * (lg + (blockLen B : ℝ) ^ 2 * lg / Real.sqrt (B : ℝ)) := by
    have hnn : 0 ≤ J * (h * K / B) * (lg + (blockLen B : ℝ) ^ 2 * lg / Real.sqrt (B : ℝ)) := by
      positivity
    have hnn2 : 0 ≤ J * (h * K * (blockLen B : ℝ) / (B : ℝ)) := by positivity
    rw [abs_le]
    constructor
    · nlinarith [neg_abs_le rho, abs_nonneg rho, mul_nonneg hnn2 (abs_nonneg rho)]
    · nlinarith [le_abs_self rho, abs_nonneg rho, mul_nonneg hnn2 (abs_nonneg rho)]
  refine habs.trans ?_
  have h1 : J * (h * K * (blockLen B : ℝ) / (B : ℝ)) * |rho| ≤ h * K * (T + 1) * |rho| := by
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg rho)
    calc J * (h * K * (blockLen B : ℝ) / (B : ℝ)) =
        h * K * (blockLen B : ℝ) / (B : ℝ) * J := by ring
      _ ≤ _ := haJ
  have h2 : J * (h * K / B) * (lg + (blockLen B : ℝ) ^ 2 * lg / Real.sqrt (B : ℝ)) ≤
      2 * (h * K * (2 * T + 1)) * (lg * u) := by
    calc J * (h * K / B) * (lg + (blockLen B : ℝ) ^ 2 * lg / Real.sqrt (B : ℝ))
        ≤ (h * K * (2 * T + 1) * u) * (lg + lg) := by
          apply mul_le_mul hJb (by linarith) (by positivity) (by positivity)
      _ = 2 * (h * K * (2 * T + 1)) * (lg * u) := by ring
  linarith


/-- Asymptotics: the deterministic part. -/
private lemma diffuse_asym_det (Bs : ℕ → ℕ) (hB : Tendsto Bs atTop atTop) (T h K : ℝ)
    (hT : 0 < T) (hh : 0 < h) (hK : 0 ≤ K) (rho : ℕ → ℝ) (hrho : Tendsto rho atTop (𝓝 0)) :
    Tendsto (fun k => ((⌈T * (Bs k : ℝ) / (blockLen (Bs k) : ℝ)⌉₊ : ℕ) : ℝ) *
      (h * K * (blockLen (Bs k) : ℝ) / (Bs k : ℝ) * rho k + h * K / (Bs k : ℝ) *
        (Real.log (2 * (Bs k : ℝ)) + (blockLen (Bs k) : ℝ) ^ 2 * Real.log (2 * (Bs k : ℝ)) /
          Real.sqrt (Bs k : ℝ)))) atTop (𝓝 0) := by
  have hu := diffuse_log_rpow_tendsto.comp hB
  have hbd : Tendsto (fun k => h * K * (T + 1) * |rho k| + 2 * (h * K * (2 * T + 1)) *
      (Real.log (2 * (Bs k : ℝ)) * (Bs k : ℝ) ^ (-(1 / 8 : ℝ)))) atTop (𝓝 0) := by
    simpa using (hrho.abs.const_mul (h * K * (T + 1))).add (hu.const_mul (2 * (h * K * (2 * T + 1))))
  refine squeeze_zero_norm' ?_ hbd
  filter_upwards [hB.eventually_ge_atTop 256] with k hk
  rw [Real.norm_eq_abs]
  exact diffuse_det_bound T h K hT hh hK hk (rho k)

/-- Asymptotics: the block increment bound. -/
private lemma diffuse_asym_incr (Bs : ℕ → ℕ) (hB : Tendsto Bs atTop atTop) (c : ℝ) :
    Tendsto (fun k => c * (blockLen (Bs k) : ℝ) / (Bs k : ℝ)) atTop (𝓝 0) := by
  have hu : Tendsto (fun k => (Bs k : ℝ) ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp (tendsto_natCast_atTop_atTop.comp hB)
  have hbd : Tendsto (fun k => |c| * (Bs k : ℝ) ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) := by
    simpa using hu.const_mul |c|
  refine squeeze_zero_norm' ?_ hbd
  filter_upwards [hB.eventually_ge_atTop 256] with k hk
  rw [Real.norm_eq_abs, mul_div_assoc, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ (blockLen (Bs k) : ℝ) / (Bs k : ℝ) from
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (diffuse_L_div_le hk) (abs_nonneg c)

/-- `√B / B ≤ B^{-1/8}`. -/
private lemma diffuse_sqrt_div_le {B : ℕ} (hB : 256 ≤ B) :
    Real.sqrt (B : ℝ) / B ≤ (B : ℝ) ^ (-(1 / 8 : ℝ)) := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (le_trans (by norm_num) hB)
  have hBpos : (0 : ℝ) < B := by linarith
  rw [Real.sqrt_eq_rpow, show (1 / 2 : ℝ) = 1 / 2 from rfl]
  rw [← Real.rpow_sub_one hBpos.ne']
  exact Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)

/-- Asymptotics: the Markov bound. -/
private lemma diffuse_asym_markov (Bs : ℕ → ℕ) (hB : Tendsto Bs atTop atTop) (T h K Kb cM β x : ℝ)
    (hT : 0 < T) (hx : 0 < x) :
    Tendsto (fun k => h / (Bs k : ℝ) * K * (Real.sqrt (2 * cM * (Bs k : ℝ)) / (1 - β) +
      ((⌈T * (Bs k : ℝ) / (blockLen (Bs k) : ℝ)⌉₊ : ℕ) : ℝ) * Kb * Real.log (2 * (Bs k : ℝ))) / x)
      atTop (𝓝 0) := by
  have hu : Tendsto (fun k => (Bs k : ℝ) ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp (tendsto_natCast_atTop_atTop.comp hB)
  have hv := diffuse_log_rpow_tendsto.comp hB
  have hbd : Tendsto (fun k => |h * K| / x * ((Real.sqrt |2 * cM| / |1 - β|) *
      (Bs k : ℝ) ^ (-(1 / 8 : ℝ)) + |Kb| * ((2 * T + 1) *
      (Real.log (2 * (Bs k : ℝ)) * (Bs k : ℝ) ^ (-(1 / 8 : ℝ)))))) atTop (𝓝 0) := by
    simpa using (((hu.const_mul (Real.sqrt |2 * cM| / |1 - β|)).add
      ((hv.const_mul (2 * T + 1)).const_mul |Kb|)).const_mul (|h * K| / x))
  refine squeeze_zero_norm' ?_ hbd
  filter_upwards [hB.eventually_ge_atTop 256] with k hk
  set B := Bs k with hBdef
  have hB1' : 1 ≤ B := le_trans (by norm_num) hk
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB1'
  have hBpos : (0 : ℝ) < B := by linarith
  have hlg : 0 ≤ Real.log (2 * (B : ℝ)) := Real.log_nonneg (by linarith)
  have hJB := diffuse_J_div_le T hT hk
  have hsqB := diffuse_sqrt_div_le hk
  have hJ0 : (0 : ℝ) ≤ ((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  set J : ℝ := ((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ) with hJ
  set lg := Real.log (2 * (B : ℝ)) with hlgdef
  set u : ℝ := (B : ℝ) ^ (-(1 / 8 : ℝ)) with hu'
  have hu0 : 0 ≤ u := Real.rpow_nonneg hBpos.le _
  have hform : h / B * K * (Real.sqrt (2 * cM * B) / (1 - β) + J * Kb * lg) / x =
      h * K / x * ((Real.sqrt (2 * cM * B) / B) / (1 - β) + (J / B) * Kb * lg) := by
    field_simp
  rw [hform, Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hx]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsqrt : Real.sqrt (2 * cM * B) ≤ Real.sqrt |2 * cM| * Real.sqrt B := by
    rw [← Real.sqrt_mul (abs_nonneg _)]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (le_abs_self _) hBpos.le)
  have hsqrt0 : 0 ≤ Real.sqrt (2 * cM * B) := Real.sqrt_nonneg _
  calc
    |(Real.sqrt (2 * cM * B) / B) / (1 - β) + (J / B) * Kb * lg|
        ≤ |(Real.sqrt (2 * cM * B) / B) / (1 - β)| + |(J / B) * Kb * lg| := abs_add_le _ _
    _ ≤ (Real.sqrt |2 * cM| / |1 - β|) * u + |Kb| * ((2 * T + 1) * (lg * u)) := by
      apply add_le_add
      · rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (2 * cM * B) / B)]
        have h1 : Real.sqrt (2 * cM * B) / B ≤ Real.sqrt |2 * cM| * u := by
          calc Real.sqrt (2 * cM * B) / B ≤ (Real.sqrt |2 * cM| * Real.sqrt B) / B :=
                div_le_div_of_nonneg_right hsqrt hBpos.le
            _ = Real.sqrt |2 * cM| * (Real.sqrt B / B) := by ring
            _ ≤ Real.sqrt |2 * cM| * u := mul_le_mul_of_nonneg_left hsqB (Real.sqrt_nonneg _)
        calc Real.sqrt (2 * cM * B) / B / |1 - β| ≤ (Real.sqrt |2 * cM| * u) / |1 - β| :=
              div_le_div_of_nonneg_right h1 (abs_nonneg _)
          _ = Real.sqrt |2 * cM| / |1 - β| * u := by ring
      · rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ J / B), abs_of_nonneg hlg]
        have : J / B * |Kb| * lg ≤ ((2 * T + 1) * u) * |Kb| * lg := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hJB (abs_nonneg _)) hlg
        nlinarith [this]


private lemma diffuse_y8 {B : ℕ} (hB : 1 ≤ B) : ((B : ℝ) ^ ((1 : ℝ) / 8)) ^ 8 = B := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  rw [← Real.rpow_natCast, ← Real.rpow_mul hBpos.le]
  norm_num

private lemma diffuse_mart_bound (T γ CS h x : ℝ)
    (hT : 0 < T) (hγ : 0 ≤ γ) (hCS : 1 ≤ CS) (hh : 0 < h) (hx : 0 < x) {B m : ℕ}
    (hB : 256 ≤ B) (hm : (m : ℝ) ≤ 2 * γ * (B : ℝ)) :
    2 * (m : ℝ) * ((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ) *
      Real.exp (-(x ^ 2) / (2 * ((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ) *
        (2 * (CS * h * (blockLen B : ℝ) / (B : ℝ))) ^ 2)) ≤
    4 * γ * (T + 1) * (((B : ℝ) ^ ((1 : ℝ) / 8)) ^ 16 *
      Real.exp (-(x ^ 2 / (8 * CS ^ 2 * h ^ 2 * (T + 1))) * (B : ℝ) ^ ((1 : ℝ) / 8))) := by
  have hB1' : 1 ≤ B := le_trans (by norm_num) hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB1'
  have hBpos : (0 : ℝ) < B := by linarith
  have hLpos' : 0 < blockLen B := diffuse_blockLen_pos hB1'
  have hL1 : (1 : ℝ) ≤ blockLen B := by exact_mod_cast hLpos'
  have hLpos : (0 : ℝ) < blockLen B := by linarith
  have hLB := diffuse_blockLen_le hB1'
  have hJ : ((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ) ≤ T * B / blockLen B + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hJ1 : (1 : ℝ) ≤ ((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ) := by
    have : 0 < ⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ := Nat.ceil_pos.mpr (by positivity)
    exact_mod_cast this
  set J : ℝ := ((⌈T * (B : ℝ) / (blockLen B : ℝ)⌉₊ : ℕ) : ℝ) with hJdef
  set y : ℝ := (B : ℝ) ^ ((1 : ℝ) / 8) with hy
  have hy8 : y ^ 8 = B := diffuse_y8 hB1'
  have hypos : 0 < y := Real.rpow_pos_of_pos hBpos _
  have hCS0 : 0 < CS := by linarith
  -- J ≤ (T+1) B / L
  have hJ2 : J ≤ (T + 1) * B / blockLen B := by
    have : (1 : ℝ) ≤ B / blockLen B := by rw [le_div_iff₀ hLpos]; linarith
    calc J ≤ T * B / blockLen B + 1 := hJ
      _ ≤ T * B / blockLen B + B / blockLen B := by linarith
      _ = (T + 1) * B / blockLen B := by ring
  have hJB : J ≤ (T + 1) * B := by
    refine hJ2.trans ?_
    rw [div_le_iff₀ hLpos]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < T + 1) hBpos]
  set c : ℝ := CS * h * (blockLen B : ℝ) / (B : ℝ) with hc
  have hcpos : 0 < c := by positivity
  have hDpos : 0 < 2 * J * (2 * c) ^ 2 := by positivity
  have hDle : 2 * J * (2 * c) ^ 2 ≤ 8 * CS ^ 2 * h ^ 2 * (T + 1) * y⁻¹ := by
    have h1 : 2 * J * (2 * c) ^ 2 = 8 * CS ^ 2 * h ^ 2 * (J * (blockLen B : ℝ) ^ 2 / (B : ℝ) ^ 2) := by
      rw [hc]; field_simp; ring
    have h2 : J * (blockLen B : ℝ) ^ 2 / (B : ℝ) ^ 2 ≤ (T + 1) * ((blockLen B : ℝ) / B) := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hJ2 (by positivity : 0 ≤ (blockLen B : ℝ) ^ 2)
      calc J * (blockLen B : ℝ) ^ 2 ≤ (T + 1) * B / blockLen B * (blockLen B : ℝ) ^ 2 := this
        _ = (T + 1) * ((blockLen B : ℝ) / B) * (B : ℝ) ^ 2 := by field_simp
    have h3 : (blockLen B : ℝ) / B ≤ y⁻¹ := by
      have := diffuse_L_div_le hB
      have hneg : (B : ℝ) ^ (-(1 / 8 : ℝ)) = y⁻¹ := by
        rw [hy, ← Real.rpow_neg hBpos.le]
      rwa [hneg] at this
    rw [h1]
    have hcs : 0 ≤ 8 * CS ^ 2 * h ^ 2 := by positivity
    calc 8 * CS ^ 2 * h ^ 2 * (J * (blockLen B : ℝ) ^ 2 / (B : ℝ) ^ 2)
        ≤ 8 * CS ^ 2 * h ^ 2 * ((T + 1) * y⁻¹) :=
          mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by linarith))) hcs
      _ = _ := by ring
  have hexp : Real.exp (-(x ^ 2) / (2 * J * (2 * c) ^ 2)) ≤
      Real.exp (-(x ^ 2 / (8 * CS ^ 2 * h ^ 2 * (T + 1))) * y) := by
    apply Real.exp_le_exp.mpr
    have hK : 0 < 8 * CS ^ 2 * h ^ 2 * (T + 1) := by positivity
    have : x ^ 2 / (8 * CS ^ 2 * h ^ 2 * (T + 1)) * y ≤ x ^ 2 / (2 * J * (2 * c) ^ 2) := by
      rw [show x ^ 2 / (8 * CS ^ 2 * h ^ 2 * (T + 1)) * y =
        x ^ 2 / (8 * CS ^ 2 * h ^ 2 * (T + 1) * y⁻¹) by field_simp]
      exact div_le_div_of_nonneg_left (by positivity) hDpos hDle
    rw [neg_div, neg_mul]
    linarith
  have hprod : 2 * (m : ℝ) * J ≤ 4 * γ * (T + 1) * y ^ 16 := by
    have h16 : y ^ 16 = (B : ℝ) ^ 2 := by
      rw [show y ^ 16 = (y ^ 8) ^ 2 by ring, hy8]
    rw [h16]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have := mul_le_mul hm hJB (by linarith) (by positivity : (0 : ℝ) ≤ 2 * γ * B)
    nlinarith [this]
  calc 2 * (m : ℝ) * J * Real.exp (-(x ^ 2) / (2 * J * (2 * c) ^ 2))
      ≤ (4 * γ * (T + 1) * y ^ 16) *
        Real.exp (-(x ^ 2 / (8 * CS ^ 2 * h ^ 2 * (T + 1))) * y) :=
        mul_le_mul hprod hexp (Real.exp_nonneg _) (by positivity)
    _ = _ := by ring

/-- Asymptotics: the martingale bound. -/
private lemma diffuse_asym_mart (Bs ms : ℕ → ℕ) (hB : Tendsto Bs atTop atTop) (T γ CS h x : ℝ)
    (hT : 0 < T) (hγ : 0 ≤ γ) (hCS : 1 ≤ CS) (hh : 0 < h) (hx : 0 < x)
    (hms : ∀ k, (ms k : ℝ) ≤ 2 * γ * (Bs k : ℝ)) :
    Tendsto (fun k => 2 * (ms k : ℝ) * ((⌈T * (Bs k : ℝ) / (blockLen (Bs k) : ℝ)⌉₊ : ℕ) : ℝ) *
      Real.exp (-(x ^ 2) / (2 * ((⌈T * (Bs k : ℝ) / (blockLen (Bs k) : ℝ)⌉₊ : ℕ) : ℝ) *
        (2 * (CS * h * (blockLen (Bs k) : ℝ) / (Bs k : ℝ))) ^ 2))) atTop (𝓝 0) := by
  have hCS0 : 0 < CS := by linarith
  have hκ : 0 < x ^ 2 / (8 * CS ^ 2 * h ^ 2 * (T + 1)) := by positivity
  have hy : Tendsto (fun k => (Bs k : ℝ) ^ ((1 : ℝ) / 8)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (tendsto_natCast_atTop_atTop.comp hB)
  have hg : Tendsto (fun y : ℝ => y ^ (16 : ℝ) *
      Real.exp (-(x ^ 2 / (8 * CS ^ 2 * h ^ 2 * (T + 1))) * y)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 16 _ hκ
  have hG : Tendsto (fun k => 4 * γ * (T + 1) * (((Bs k : ℝ) ^ ((1 : ℝ) / 8)) ^ 16 *
      Real.exp (-(x ^ 2 / (8 * CS ^ 2 * h ^ 2 * (T + 1))) * (Bs k : ℝ) ^ ((1 : ℝ) / 8))))
      atTop (𝓝 0) := by
    have := (hg.comp hy).const_mul (4 * γ * (T + 1))
    simpa [Real.rpow_natCast] using this
  refine squeeze_zero' ?_ ?_ hG
  · filter_upwards with k
    positivity
  · filter_upwards [hB.eventually_ge_atTop 256] with k hk
    exact diffuse_mart_bound T γ CS h x hT hγ hCS hh hx hk (hms k)


/-- `lem:app-dyn-diffuse`, snapshot `cr-2026-10-23`. Persistence of diffuseness along the algorithm.
Source, `section.tex` ll. 2057–2063, verbatim:
```latex
\begin{lemma}[Persistence of diffuseness]\label{lem:app-dyn-diffuse}
Let $b_c\defeq\inf\{b\ge0:\Delta_{t_b}\notin\mathcal A\}$. For every fixed $T>0$,
\[
\max\big\{\delta(\Dt):\ t\le t_{b_c}\wedge TB\big\}\longrightarrow0\quad\text{in probability}.
\]
No diffuseness beyond the initial condition \ref{hyp:app-dyn-initial} is used.
\end{lemma}
```
Encoding: for every fixed `T > 0` and `ε > 0`, `P k` of the event "some `t ≤ t_{b_c} ∧ TB` has
`δ(Δ_t) > ε`" tends to `0` as the dimension `k → ∞`, which is the max-in-probability statement. The
standing hypotheses are (H1) (`regime`, and the size, sample and independence fields of `S k`), (H2) and (H4)
(fields of `S k`), and (H3) through `W0_hat`, the only diffuseness assumed. -/
theorem lem_app_dyn_diffuse (certOp : Muon.External.GaussianOpNormL6)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (p : DynParams) (P : ∀ k : ℕ, Measure (Ω k)) [∀ k : ℕ, IsProbabilityMeasure (P k)]
    (m n B : ℕ → ℕ) (S : ∀ k : ℕ, DynSetup p (P k) (m k) (n k) (B k))
    -- (H1) `hyp:app-dyn-data`: converging aspect ratios and bounded covariances
    (regime : ProportionalRegime m n B (fun k => (S k).C))
    -- (H3) `hyp:app-dyn-initial`: `‖Â₀‖ → 0`
    (W0_hat : Tendsto (fun k => opNorm (Ahat (S k).C ((S k).W0 - (S k).alg.Wstar))) atTop (𝓝 0))
    -- `T > 0` fixed and `ε > 0`
    (T : ℝ) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun k : ℕ => P k {ω | ∃ t : ℕ, (t : ℕ∞) ≤ dynBlockExitTime (S k) ω ∧
        (t : ℝ) ≤ T * (B k : ℝ) ∧ ε < diffuseness (S k).C (dynDelta (S k) t ω)})
      atTop (𝓝 0) := by
  classical
  have hr0 : 0 < p.r0 / 2 := by linarith [p.hr0]
  have hle0 : p.r0 / 2 ≤ p.r1 + 1 / 2 := by linarith [p.hr, p.hr0]
  obtain ⟨B1, hB1⟩ := diffuse_risk_before_exit p
  obtain ⟨B2, Kc, hcd⟩ :=
    cond_block_drift certOp p (p.r0 / 2) (p.r1 + 1 / 2) (p.Estar + 1) hr0 hle0
  obtain ⟨B3, Kb, hKb, hbm⟩ := diffuse_buffer_markov certOp p
  obtain ⟨r, hr, hrk⟩ := hcd Ω P m n B S regime
  have hBtop : Tendsto B atTop atTop := regime.B_top
  have hs0pos : 0 < Real.sqrt (p.r0 / 2) := Real.sqrt_pos.mpr hr0
  have hΛpos : 0 < Real.exp (p.h * |Kc| * (T + 1)) := Real.exp_pos _
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ,
      x = ε * Real.sqrt (p.r0 / 2) / (8 * Real.exp (p.h * |Kc| * (T + 1))) := ⟨_, rfl⟩
  have hxpos : 0 < x := by rw [hxdef]; positivity
  -- the initial state
  have hz : Tendsto (fun k => Real.sqrt (2 * p.r1) *
      opNorm (Ahat (S k).C ((S k).W0 - (S k).alg.Wstar))) atTop (𝓝 0) := by
    simpa using W0_hat.const_mul (Real.sqrt (2 * p.r1))
  have hdet := diffuse_asym_det B hBtop T p.h |Kc| hT p.hh (abs_nonneg _) (fun k => |r k|)
    (by simpa using hr.abs)
  have hsum : Tendsto (fun k => Real.sqrt (2 * p.r1) *
      opNorm (Ahat (S k).C ((S k).W0 - (S k).alg.Wstar)) +
      ((⌈T * (B k : ℝ) / (blockLen (B k) : ℝ)⌉₊ : ℕ) : ℝ) *
      (p.h * |Kc| * (blockLen (B k) : ℝ) / (B k : ℝ) * |r k| + p.h * |Kc| / (B k : ℝ) *
        (Real.log (2 * (B k : ℝ)) + (blockLen (B k) : ℝ) ^ 2 * Real.log (2 * (B k : ℝ)) /
          Real.sqrt (B k : ℝ)))) atTop (𝓝 0) := by
    simpa using hz.add hdet
  have hinc := diffuse_asym_incr B hBtop (p.CSig * p.h)
  have hmk := diffuse_asym_markov B hBtop T p.h |Kc| Kb p.cM p.β x hT hxpos
  have hmt := diffuse_asym_mart B (fun k => m k + n k) hBtop T p.γstar p.CSig p.h x hT p.hγ p.hC
    p.hh hxpos (fun k => by
      have := diffuse_dimension_bound p (S k)
      push_cast at this ⊢
      linarith)
  have hev1 : ∀ᶠ k in atTop, max (max B1 B2) (max B3 1) ≤ B k := hBtop.eventually_ge_atTop _
  have hev2 : ∀ᶠ k in atTop, Real.sqrt (2 * p.r1) *
      opNorm (Ahat (S k).C ((S k).W0 - (S k).alg.Wstar)) +
      ((⌈T * (B k : ℝ) / (blockLen (B k) : ℝ)⌉₊ : ℕ) : ℝ) *
      (p.h * |Kc| * (blockLen (B k) : ℝ) / (B k : ℝ) * |r k| + p.h * |Kc| / (B k : ℝ) *
        (Real.log (2 * (B k : ℝ)) + (blockLen (B k) : ℝ) ^ 2 * Real.log (2 * (B k : ℝ)) /
          Real.sqrt (B k : ℝ))) < x := (tendsto_order.1 hsum).2 x hxpos
  have hev3 : ∀ᶠ k in atTop, p.CSig * p.h * (blockLen (B k) : ℝ) / (B k : ℝ) <
      ε * Real.sqrt (p.r0 / 2) / 2 := (tendsto_order.1 hinc).2 _ (by positivity)
  have hbound : ∀ᶠ k in atTop,
      P k {ω | ∃ t : ℕ, (t : ℕ∞) ≤ dynBlockExitTime (S k) ω ∧
        (t : ℝ) ≤ T * (B k : ℝ) ∧ ε < diffuseness (S k).C (dynDelta (S k) t ω)} ≤
      ENNReal.ofReal (2 * ((m k + n k : ℕ) : ℝ) *
        ((⌈T * (B k : ℝ) / (blockLen (B k) : ℝ)⌉₊ : ℕ) : ℝ) *
        Real.exp (-(x ^ 2) / (2 * ((⌈T * (B k : ℝ) / (blockLen (B k) : ℝ)⌉₊ : ℕ) : ℝ) *
          (2 * (p.CSig * p.h * (blockLen (B k) : ℝ) / (B k : ℝ))) ^ 2))) +
      ENNReal.ofReal (p.h / (B k : ℝ) * |Kc| * (Real.sqrt (2 * p.cM * (B k : ℝ)) / (1 - p.β) +
        ((⌈T * (B k : ℝ) / (blockLen (B k) : ℝ)⌉₊ : ℕ) : ℝ) * Kb * Real.log (2 * (B k : ℝ))) / x) := by
    filter_upwards [hev1, hev2, hev3] with k hk1 hk2 hk3
    have hkB1 : B1 ≤ B k := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hk1
    have hkB2 : B2 ≤ B k := le_trans ((le_max_right _ _).trans (le_max_left _ _)) hk1
    have hkB3 : B3 ≤ B k := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hk1
    have hkB4 : 1 ≤ B k := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hk1
    set J : ℕ := ⌈T * (B k : ℝ) / (blockLen (B k) : ℝ)⌉₊ with hJdef
    have hLpos : 0 < blockLen (B k) := diffuse_blockLen_pos (by omega)
    have hJ1 : 1 ≤ J := by
      rw [hJdef]
      apply Nat.one_le_iff_ne_zero.mpr
      apply (Nat.ceil_pos.mpr _).ne'
      have : (0 : ℝ) < (B k : ℝ) := by exact_mod_cast hkB4
      have : (0 : ℝ) < (blockLen (B k) : ℝ) := by exact_mod_cast hLpos
      positivity
    have hgood := diffuse_good_bound (S k) Kc (r k) hkB4 (fun t i j => (hrk k hkB2 t).1 i j)
      (fun t => (hrk k hkB2 t).2) J x
    have hm1 := diffuse_mart_event (S k) x hxpos J hJ1
    have ha : 0 ≤ p.h / (B k : ℝ) * |Kc| := by
      have := p.hh
      positivity
    have hm2 := hbm (Ω k) (P k) (m k) (n k) (B k) (S k) hkB3 J (p.h / (B k : ℝ) * |Kc|) x ha hxpos
    have hrisk : ∀ (ω : Ω k) (t : ℕ), (t : ℕ∞) ≤ dynBlockExitTime (S k) ω →
        p.r0 / 4 ≤ riskSigma (S k).C (dynDelta (S k) t ω) :=
      fun ω t ht => hB1 (Ω k) (P k) (m k) (n k) (B k) (S k) hkB1 ω t ht
    have haJ := diffuse_aJ_le T p.h |Kc| hT p.hh (abs_nonneg _) hkB4
    have hsub : {ω | ∃ t : ℕ, (t : ℕ∞) ≤ dynBlockExitTime (S k) ω ∧
        (t : ℝ) ≤ T * (B k : ℝ) ∧ ε < diffuseness (S k).C (dynDelta (S k) t ω)} ≤ᵐ[P k]
        ({ω | ∃ j ≤ J, x ≤ opNorm (∑ b ∈ Finset.range j,
          (dfX (S k) b ω - Muon.Foundations.condExpMat (dynPast (S k) (b * blockLen (B k)))
            (P k) (dfX (S k) b) ω))} ∪
        {ω | x ≤ ∑ b ∈ Finset.range J, if (b : ℕ∞) < dynBlockIndexExit (S k) ω then
            p.h / (B k : ℝ) * |Kc| * opNorm (dynBuf (S k) (b * blockLen (B k)) ω) else 0}) := by
      filter_upwards [hgood] with ω hω hbad
      obtain ⟨t, ht1, ht2, hεt⟩ := hbad
      by_contra hnot
      rw [Set.mem_union, not_or] at hnot
      obtain ⟨hn1, hn2⟩ := hnot
      have hY := hω hn1 (not_le.mp hn2)
      obtain ⟨j, hjJ, hjb, hlt⟩ := diffuse_bad_to_block (S k) hkB4 hrisk T ε hT ω t ht1 ht2 hεt
      have hYj := hY j hjJ hjb
      have hΔ0 : opNorm (Arot (S k).C (dynDelta (S k) 0 ω)) ≤ Real.sqrt (2 * p.r1) *
          opNorm (Ahat (S k).C ((S k).W0 - (S k).alg.Wstar)) := by
        have hD0 : dynDelta (S k) 0 ω = (S k).W0 - (S k).alg.Wstar := rfl
        rw [hD0]
        have hR := (S k).W0_risk
        have hdi := diffuse_eq_rot_div_sqrt_risk (S k).C ((S k).W0 - (S k).alg.Wstar)
        have hdi' : diffuseness (S k).C ((S k).W0 - (S k).alg.Wstar) =
            opNorm (Ahat (S k).C ((S k).W0 - (S k).alg.Wstar)) := rfl
        have hpos : 0 < Real.sqrt (2 * riskSigma (S k).C ((S k).W0 - (S k).alg.Wstar)) :=
          Real.sqrt_pos.mpr (by linarith [p.hr0, hR.1])
        have heq : opNorm (Arot (S k).C ((S k).W0 - (S k).alg.Wstar)) =
            opNorm (Ahat (S k).C ((S k).W0 - (S k).alg.Wstar)) *
              Real.sqrt (2 * riskSigma (S k).C ((S k).W0 - (S k).alg.Wstar)) := by
          rw [← hdi', hdi]
          field_simp
        rw [heq, mul_comm]
        exact mul_le_mul_of_nonneg_right
          (Real.sqrt_le_sqrt (by linarith [hR.2])) (diffuse_opNorm_nonneg _)
      have hE : Real.exp (p.h * |Kc| * (blockLen (B k) : ℝ) / (B k : ℝ) * (J : ℝ)) ≤
          Real.exp (p.h * |Kc| * (T + 1)) := Real.exp_le_exp.mpr haJ
      have hEpos : 0 < Real.exp (p.h * |Kc| * (blockLen (B k) : ℝ) / (B k : ℝ) * (J : ℝ)) :=
        Real.exp_pos _
      have hA : 0 ≤ opNorm (Arot (S k).C (dynDelta (S k) 0 ω)) + (J : ℝ) *
          (p.h * |Kc| * (blockLen (B k) : ℝ) / (B k : ℝ) * |r k| + p.h * |Kc| / (B k : ℝ) *
            (Real.log (2 * (B k : ℝ)) + (blockLen (B k) : ℝ) ^ 2 * Real.log (2 * (B k : ℝ)) /
              Real.sqrt (B k : ℝ))) + 2 * x := by
        by_contra hneg
        have := mul_neg_of_neg_of_pos (not_le.mp hneg) hEpos
        linarith [diffuse_opNorm_nonneg (Arot (S k).C (dynDelta (S k) (j * blockLen (B k)) ω))]
      have hA3 : opNorm (Arot (S k).C (dynDelta (S k) 0 ω)) + (J : ℝ) *
          (p.h * |Kc| * (blockLen (B k) : ℝ) / (B k : ℝ) * |r k| + p.h * |Kc| / (B k : ℝ) *
            (Real.log (2 * (B k : ℝ)) + (blockLen (B k) : ℝ) ^ 2 * Real.log (2 * (B k : ℝ)) /
              Real.sqrt (B k : ℝ))) + 2 * x ≤ 3 * x := by linarith
      have hprod := mul_le_mul hA3 hE hEpos.le (by linarith)
      have hx8 : x * Real.exp (p.h * |Kc| * (T + 1)) * 8 = ε * Real.sqrt (p.r0 / 2) := by
        rw [hxdef]
        field_simp
      nlinarith
    calc
      _ ≤ P k _ := measure_mono_ae hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := add_le_add hm1 hm2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
    (Eventually.of_forall fun _ => bot_le) hbound
  have := (ENNReal.tendsto_ofReal hmt).add (ENNReal.tendsto_ofReal hmk)
  simpa using this

end Muon.Dynamics

end

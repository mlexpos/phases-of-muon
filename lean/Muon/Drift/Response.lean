import Muon.Drift.Defs
import Muon.Drift.Coefficients
import Muon.Setup.Regime
import Muon.DetEquiv.Gram
import Muon.Drift.Targets
import Muon.Drift.Tail

/-!
# Muon.Drift: response equation and the mixed resolvent closure, part (i) (work package L-C.9)

Interface draft (statements only; every proof is `sorry`) for `prop:app-drift-response` and
`thm:app-drift-mixed`(i) of `sections/03-drift/CARD.md` §3, snapshot `cr-2026-10-23`.
Part (ii) of `thm:app-drift-mixed` is `Muon.Drift.thm_app_drift_mixed_ii` (L-C.7, `Tail.lean`) and
is not restated here.

Reused, not restated: `Hmix`, `Tcand`, `EB`, `YB`, `bB`, `EG`, `branchQ`, `branchSigma`,
`deltaB`, `rPrimeB`, `freshExp`, `specOutFM`/`specInFM`, `delAlpha1/2`, `alphaStar1/2`
(`Muon.Drift.Defs`, `Muon.DetEquiv.Concentration`), `WeightClass`, `sumPow`, `Fw`, `Lw`
(`Muon.DetEquiv.Scalar`), `psiX`, `J` (`Muon.DetEquiv`), `emaW`, `emaW_weightClass`
(`Muon.Foundations.Conventions`, `Muon.Drift.Coefficients`), and `Muon.Setup.SetupRegime`
(`assum:app-setup-regime`).

Representation choices (see the docstrings and the result JSON):
* Each record is stated for a general weight sequence `w` with `WeightClass w` (card rule (a)),
  as a `_weights` helper; the EMA record is the instance at `Muon.emaW R.β`. `WeightClass`
  already contains "not all zero" (`WeightSeq`, coordinator ruling L2).
* Sequences of models carry `Ω : ℕ → Type` (as in `Muon.Drift.Targets`); the single-model
  statements of `Tail.lean` use `Ω : Type`.
* `prop:app-drift-response`: the constant `C_I` depends only on `(I, C_Σ, γ⋆)`, so it is
  quantified before the regime sequence (card §6.3, lesson (b)); `(C_Σ, γ⋆)` are the fields
  `CSig`, `γstar` of the regime; `q_I = (C_Σ γ⋆)²/s₋` with `s₋ = sInf I` is given by
  `qIbound` (`eqn:app-de-qI`, `section.tex` l.567). The sequence `e_B^⋆` of
  `lem:app-drift-targets` is existential and is quantified inside the statement together with
  the defining bounds of that lemma.
* Junk values: every `⨆` is paired with a `BddAbove` conjunct (card rule (c)); the limits are
  `Tendsto` statements along the model index `k`.
-/

open MeasureTheory Filter Topology Set
open scoped Matrix ENNReal
open Matrix
open Muon Muon.Setup Muon.DetEquiv

set_option linter.style.longLine false

namespace Muon.Drift

variable {m n : ℕ}

/-- The output bound `q_I = (C_Σ γ⋆)²/s₋` with `s₋ = min I` (`eqn:app-de-qI`, `section.tex` l.567),
written with `sInf I`. Helper for `prop:app-drift-response`. -/
noncomputable def qIbound (CS γ : ℝ) (I : Set ℝ) : ℝ :=
  (CS * γ) ^ 2 / sInf I

/-- The fresh-Gaussian residual functional `r_B = sup_{0≤x≤Q} |𝔼 ψ_x(d) − J(x)|` of
`lem:app-de-gaussian`, with `d = zᵀ Â w` as in `freshExp`. Helper for `prop:app-drift-response`
(the statement of `lem:app-de-gaussian` is inline there, not a named definition). -/
noncomputable def rBfresh (A : Mat m n) (Q : ℝ) : ℝ :=
  ⨆ x ∈ Icc (0 : ℝ) Q, |freshExp A (fun d => psiX x d) - Muon.DetEquiv.J x|

private lemma pcr_delU_nonneg {m n : ℕ} (M : Mat m n) (u : Vec m) (s : ℝ) (hs : 0 < s) :
    0 ≤ delU M u s := by
  have hG : IsUnit (M * Mᵀ + s • (1 : Mat m m)).det := by
    have h1 : (M * Mᵀ).PosSemidef := by
      have h := Matrix.posSemidef_self_mul_conjTranspose M
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    have h2 : (s • (1 : Mat m m)).PosDef := Matrix.PosDef.one.smul hs
    have h3 := Matrix.PosDef.add_posSemidef h2 h1
    rw [add_comm]
    exact isUnit_iff_ne_zero.mpr h3.det_pos.ne'
  set y := Rs M s *ᵥ u with hy
  have hu : (M * Mᵀ + s • (1 : Mat m m)) *ᵥ y = u := by
    rw [hy, Matrix.mulVec_mulVec]
    unfold Rs
    rw [Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]
  have h0 : delU M u s = y ⬝ᵥ ((M * Mᵀ + s • (1 : Mat m m)) *ᵥ y) := by
    rw [hu, delU, dotProduct_comm]
  have h1 : y ⬝ᵥ ((M * Mᵀ + s • (1 : Mat m m)) *ᵥ y)
      = (Mᵀ *ᵥ y) ⬝ᵥ (Mᵀ *ᵥ y) + s * (y ⬝ᵥ y) := by
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    have hv : y ᵥ* M = Mᵀ *ᵥ y := by
      have h := Matrix.vecMul_transpose Mᵀ y
      rwa [Matrix.transpose_transpose] at h
    rw [hv, smul_eq_mul]
  rw [h0, h1]
  have := dotProduct_self_star_nonneg (Mᵀ *ᵥ y)
  have h2 : 0 ≤ y ⬝ᵥ y := by simpa using dotProduct_self_star_nonneg y
  have h3 : 0 ≤ (Mᵀ *ᵥ y) ⬝ᵥ (Mᵀ *ᵥ y) := by simpa using this
  positivity

private lemma pcr_alpha2_nonneg {m n : ℕ} (M₀ : Mat m n) (h : ℝ) (u : Vec m) (v : Vec n) (s : ℝ)
    (hs : 0 < s) : 0 ≤ alpha2 M₀ h u v s := by
  have hL := (lem_app_de_deletion M₀ h u v (M₀ + h • outer u v) s rfl hs).1
  unfold alpha2
  exact div_nonneg (mul_nonneg (sq_nonneg _) (pcr_delU_nonneg M₀ u s hs)) hL.le

private lemma pcr_bB_nonneg {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (s : ℝ) (hs : 0 < s) : 0 ≤ bB w F S t s := by
  unfold bB
  refine tsum_nonneg fun j => ?_
  unfold bj phiJ
  refine integral_nonneg_of_ae ?_
  have : 0 ≤ᵐ[P] delAlpha2 w F S t j s := Filter.Eventually.of_forall fun ω =>
    pcr_alpha2_nonneg _ _ _ _ _ hs
  exact condExp_nonneg this

private lemma pcr_identity {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (ν ν' : FiniteMeasure ℝ) (s : ℝ) :
    Hmix w F S t s * YB w F S t s =
      (Lw w (branchQ w ν ν' s)) • (Rbar (Fw w) ν ν' F.C s * EG F) + EB w F S t ν ν' s := by
  unfold EB; abel


-- PCR-HELPERS-BEGIN
section PcrA
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma pcr_indep {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B)
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

private lemma pcr_resid_memLp (m n : ℕ) (A : Mat m n) (hA : fro A = 1) :
    MemLp (fun p : Vec m × Vec n => resid A p) 2 (gaussPair m n) := by
  have h := lem_app_de_moments_ii A hA 1 le_rfl
  norm_num [Nat.doubleFactorial] at h
  exact lt_of_le_of_lt h ENNReal.one_lt_top

end PcrA

section PcrB
open ProbabilityTheory

private lemma pcr_psi_int {Ω : Type*} [mΩ : MeasurableSpace Ω] {m n B : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    Integrable (fun ω => psiX x (ageD F S t j ω)) P ∧
    ∫ ω, psiX x (ageD F S t j ω) ∂P = freshExp F.A (fun d => psiX x d) := by
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hX : Measurable X := S.meas _ _
  have hlaw : P.map X = gaussPair m n := S.law _ _
  have hd : ∀ ω, ageD F S t j ω = resid F.A (X ω) := fun ω => rfl
  have hcont : Continuous (fun p : Vec m × Vec n => psiX x (resid F.A p)) := by
    unfold psiX resid
    refine Continuous.div (by fun_prop) (by fun_prop) fun p => ?_
    have := mul_nonneg hx (sq_nonneg (dotProduct p.1 (F.A.mulVec p.2))); linarith
  have hmeas : AEStronglyMeasurable (fun p : Vec m × Vec n => psiX x (resid F.A p)) (P.map X) :=
    hcont.aestronglyMeasurable
  have hg : Integrable (fun p : Vec m × Vec n => psiX x (resid F.A p)) (gaussPair m n) := by
    have hm2 := (pcr_resid_memLp m n F.A F.hA).integrable_sq
    refine hm2.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    unfold psiX
    have hD : 1 ≤ 1 + x * resid F.A p ^ 2 := by
      have := mul_nonneg hx (sq_nonneg (resid F.A p)); linarith
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by linarith))]
    exact div_le_self (sq_nonneg _) hD
  have hg' : Integrable (fun p : Vec m × Vec n => psiX x (resid F.A p)) (P.map X) := by
    rw [hlaw]; exact hg
  refine ⟨?_, ?_⟩
  · exact (integrable_map_measure hmeas hX.aemeasurable).1 hg'
  · have := integral_map (μ := P) hX.aemeasurable hmeas
    rw [hlaw] at this
    exact this.symm

private lemma pcr_abs_int_le_L2 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (f : Ω → ℝ) (hf : MemLp f 2 P) (c : ℝ) (hc : 0 ≤ c)
    (h : eLpNorm f 2 P ≤ ENNReal.ofReal c) : |∫ ω, f ω ∂P| ≤ c := by
  have h1 : eLpNorm f 1 P ≤ eLpNorm f 2 P := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hi : Integrable f P := hf.integrable one_le_two
  have h2 : ENNReal.ofReal (∫ ω, ‖f ω‖ ∂P) ≤ ENNReal.ofReal c := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hi, ← eLpNorm_one_eq_lintegral_enorm]
    · exact h1.trans h
    · exact hf.aestronglyMeasurable
  have h3 := (ENNReal.ofReal_le_ofReal_iff hc).1 h2
  exact (abs_integral_le_integral_abs).trans (by simpa [Real.norm_eq_abs] using h3)

end PcrB

section PcrC
open ProbabilityTheory

private lemma pcr_bj_close {Ω : Type} [mΩ : MeasurableSpace Ω] {m n B : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (s : ℝ) (hs : 0 < s) (CS γ : ℝ) (hγ : 0 ≤ γ)
    (hw0 : 0 ≤ w j) (hw1 : w j ≤ 1) (hCo : opNorm F.C.Sout ≤ CS) (hCi : opNorm F.C.Sin ≤ CS)
    (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (σ q e r : ℝ) (hσ : 0 ≤ σ) (hq : 0 ≤ q) (he0 : 0 ≤ e)
    (he : eLpNorm (fun ω => delAlpha2 w F S t j s ω
        - w j ^ 2 * σ * psiX (w j ^ 2 * q) (ageD F S t j ω)) 2 P ≤ ENNReal.ofReal (w j ^ 2 * e))
    (hr : |freshExp F.A (fun d => psiX (w j ^ 2 * q) d) - Muon.DetEquiv.J (w j ^ 2 * q)| ≤ r) :
    |bj w F S t j s - w j ^ 2 * σ * Muon.DetEquiv.J (w j ^ 2 * q)| ≤ w j ^ 2 * (e + σ * r) := by
  obtain ⟨C, hC⟩ := lem_app_drift_coeffmoments 1 le_rfl s hs CS γ hγ
  have hM0 := tl_meas_del w F S t j
  obtain ⟨hnn, -, -, ⟨i2, -⟩⟩ := hC Ω m n B P F S t j (delBufAge w F S t j) (w j) hCo hCi hm hn
    hw0 hw1 hM0 s le_rfl
  have hnn' : ∀ ω, 0 ≤ delAlpha2 w F S t j s ω := hnn
  have i2' : Integrable (fun ω => |delAlpha2 w F S t j s ω| ^ 1) P := i2
  have hi2 : Integrable (delAlpha2 w F S t j s) P := by
    have e2 : (fun ω => |delAlpha2 w F S t j s ω| ^ 1) = delAlpha2 w F S t j s := by
      funext ω; rw [pow_one, abs_of_nonneg (hnn' ω)]
    rw [← e2]; exact i2'
  obtain ⟨hG, -⟩ := pcr_indep F S t j
  have hb : bj w F S t j s = ∫ ω, delAlpha2 w F S t j s ω ∂P := by
    unfold bj phiJ
    exact integral_condExp hG
  obtain ⟨hpi, hpe⟩ := pcr_psi_int F S t j (w j ^ 2 * q) (by positivity)
  have hstar : Integrable (fun ω => w j ^ 2 * σ * psiX (w j ^ 2 * q) (ageD F S t j ω)) P :=
    hpi.const_mul _
  have hdiff : MemLp (fun ω => delAlpha2 w F S t j s ω
        - w j ^ 2 * σ * psiX (w j ^ 2 * q) (ageD F S t j ω)) 2 P := by
    have h1 : AEStronglyMeasurable (fun ω => delAlpha2 w F S t j s ω
        - w j ^ 2 * σ * psiX (w j ^ 2 * q) (ageD F S t j ω)) P :=
      hi2.aestronglyMeasurable.sub hstar.aestronglyMeasurable
    have h2 : eLpNorm (fun ω => delAlpha2 w F S t j s ω
        - w j ^ 2 * σ * psiX (w j ^ 2 * q) (ageD F S t j ω)) 2 P < ⊤ :=
      lt_of_le_of_lt he ENNReal.ofReal_lt_top
    exact h2
  have h1 := pcr_abs_int_le_L2 _ hdiff (w j ^ 2 * e) (by positivity) he
  rw [integral_sub hi2 hstar, integral_const_mul, hpe] at h1
  rw [hb]
  have e3 : ∫ ω, delAlpha2 w F S t j s ω ∂P - w j ^ 2 * σ * Muon.DetEquiv.J (w j ^ 2 * q)
      = (∫ ω, delAlpha2 w F S t j s ω ∂P - w j ^ 2 * σ * freshExp F.A (fun d => psiX (w j ^ 2 * q) d))
        + w j ^ 2 * σ * (freshExp F.A (fun d => psiX (w j ^ 2 * q) d) - Muon.DetEquiv.J (w j ^ 2 * q)) := by
    ring
  rw [e3]
  have h2 : |w j ^ 2 * σ * (freshExp F.A (fun d => psiX (w j ^ 2 * q) d) - Muon.DetEquiv.J (w j ^ 2 * q))|
      ≤ w j ^ 2 * σ * r := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ w j ^ 2 * σ)]
    exact mul_le_mul_of_nonneg_left hr (by positivity)
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ w j ^ 2 * e + w j ^ 2 * σ * r := add_le_add h1 h2
    _ = _ := by ring

end PcrC

private lemma pcr_sum_close (w : ℕ → ℝ) (hw : WeightClass w) (b : ℕ → ℝ) (σ q c : ℝ)
    (hσ : 0 ≤ σ) (hq : 0 ≤ q) (hc : 0 ≤ c)
    (h : ∀ j, |b j - w j ^ 2 * σ * Muon.DetEquiv.J (w j ^ 2 * q)| ≤ w j ^ 2 * c) :
    Summable b ∧ |∑' j, b j - σ * Fw w q| ≤ sumPow w 2 * c := by
  have hw0 := hw.1.1
  have hw1 := hw.2.1
  have hs1 : Summable w := hw.1.2.1
  have hw2 : ∀ j, w j ^ 2 ≤ w j := fun j => by
    rw [sq]; exact mul_le_of_le_one_right (hw0 j) (hw1 j)
  have hsq : Summable (fun j => w j ^ 2) :=
    Summable.of_nonneg_of_le (fun j => sq_nonneg _) hw2 hs1
  have hJ : ∀ j, 0 ≤ Muon.DetEquiv.J (w j ^ 2 * q) ∧ Muon.DetEquiv.J (w j ^ 2 * q) ≤ 1 := fun j => by
    obtain ⟨-, -, h3, -⟩ := lem_app_de_scalar_i
    have := h3 (w j ^ 2 * q) (by have := hw0 j; positivity)
    exact ⟨this.1.le, this.2⟩
  have ha : Summable (fun j => w j ^ 2 * Muon.DetEquiv.J (w j ^ 2 * q)) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (sq_nonneg _) (hJ j).1)
      (fun j => by simpa using mul_le_mul_of_nonneg_left (hJ j).2 (sq_nonneg (w j))) hsq
  have hd : Summable (fun j => b j - w j ^ 2 * σ * Muon.DetEquiv.J (w j ^ 2 * q)) :=
    Summable.of_norm_bounded (hsq.mul_right c) (fun j => by
      rw [Real.norm_eq_abs]; exact h j)
  have hat : Summable (fun j => w j ^ 2 * σ * Muon.DetEquiv.J (w j ^ 2 * q)) := by
    have := ha.mul_left σ
    refine this.congr (fun j => ?_); ring
  have hb : Summable b := by
    have := hd.add hat
    simpa using this
  refine ⟨hb, ?_⟩
  have hF : Fw w q = ∑' j, w j ^ 2 * Muon.DetEquiv.J (w j ^ 2 * q) := rfl
  have e1 : ∑' j, b j - σ * Fw w q =
      ∑' j, (b j - w j ^ 2 * σ * Muon.DetEquiv.J (w j ^ 2 * q)) := by
    rw [hF, Summable.tsum_sub hb hat, ← tsum_mul_left]
    congr 1
    refine tsum_congr fun j => ?_
    ring
  rw [e1]
  have hg : HasSum (fun j => w j ^ 2 * c) (sumPow w 2 * c) := by
    have := (hsq.hasSum).mul_right c
    exact this
  have := tsum_of_norm_bounded hg (f := fun j => b j - w j ^ 2 * σ * Muon.DetEquiv.J (w j ^ 2 * q))
    (fun j => by rw [Real.norm_eq_abs]; exact h j)
  simpa [Real.norm_eq_abs] using this

private lemma pcr_gamma_pos (R : Muon.Setup.SetupRegime) : 0 < R.γstar := by
  have h : ∀ k, (R.n k : ℝ) / (R.B k : ℝ) ≤ R.γstar := fun k => by
    have hB : (0 : ℝ) < (R.B k : ℝ) := by exact_mod_cast (R.F k).hB
    rw [div_le_iff₀ hB]
    exact (Nat.cast_le.2 (le_max_right _ _)).trans (R.dims k)
  have := le_of_tendsto' R.prop.ratio_in h
  exact lt_of_lt_of_le R.prop.γin_pos this

private lemma pcr_drift (R : Muon.Setup.SetupRegime) (k : ℕ) :
    DriftBound (R.F k) R.CSig R.γstar := ⟨R.normOut k, R.normIn k, R.dims k⟩

private lemma pcr_branch (R : Muon.Setup.SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w) (k : ℕ)
    {s : ℝ} (hs : 0 < s) :
    0 ≤ branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s ∧
    branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s ≤ R.CSig * R.γstar / s ∧
    0 ≤ branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s ∧
    branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s ≤ (R.CSig * R.γstar) ^ 2 / s ∧
    0 ≤ (branchSol (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) s).2.2.1 := by
  have hC : 0 < R.CSig := lt_of_lt_of_le one_pos R.hC
  have hγ := pcr_gamma_pos R
  have hp := spectral_mem_classK (R.F k) (pcr_drift R k)
  have hspec := branchSol_spec (Fw_admissible hw.1) hC hγ hp hs
  have hbox := (thm_app_de_branch_i_weight hw.1 hC hγ _ _ hp s hs).2 _ hspec
  have hnn : ∀ {F : ℝ → ℝ} {ν ν' : FiniteMeasure ℝ} {s : ℝ} {x : ℝ × ℝ × ℝ × ℝ},
      IsBranchSol F ν ν' s x → 0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2.1 ∧ 0 ≤ x.2.2.2 := by
    intro F ν ν' s x h
    obtain ⟨σ, σ', a, c⟩ := x
    obtain ⟨a1, a2, a3, a4, -⟩ := h
    exact ⟨a1, a2, a3, a4⟩
  obtain ⟨h1, h2, h3, -⟩ := hnn hspec
  obtain ⟨b1, -, -, -, b5⟩ := hbox
  refine ⟨h1, ?_, ?_, ?_, h3⟩
  · unfold branchSigma; rw [mul_comm]; exact b1
  · unfold branchQ; exact mul_nonneg (mul_nonneg hs.le h1) h2
  · unfold branchQ; rw [mul_comm R.CSig R.γstar]; exact b5

private lemma pcr_le_biSup {f : ℝ → ℝ} {S : Set ℝ} {c : ℝ} (hb : ∀ x ∈ S, f x ≤ c) (hc : 0 ≤ c)
    {x : ℝ} (hx : x ∈ S) : f x ≤ ⨆ y ∈ S, f y := by
  have hbdd : BddAbove (Set.range fun y => ⨆ (_ : y ∈ S), f y) := by
    refine ⟨c, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact Real.iSup_le (fun hy => hb y hy) hc
  refine le_trans (le_of_eq ?_) (le_ciSup hbdd x)
  rw [ciSup_pos hx]

private lemma pcr_biSup_le {f : ℝ → ℝ} {S : Set ℝ} {c : ℝ} (hb : ∀ x ∈ S, f x ≤ c) (hc : 0 ≤ c) :
    ⨆ y ∈ S, f y ≤ c :=
  Real.iSup_le (fun y => Real.iSup_le (fun hy => hb y hy) hc) hc

private lemma pcr_biSup_nonneg {f : ℝ → ℝ} {S : Set ℝ} (hb : ∀ x, 0 ≤ f x) :
    0 ≤ ⨆ y ∈ S, f y :=
  Real.iSup_nonneg fun y => Real.iSup_nonneg fun _ => hb y

private lemma pcr_bddAbove {f : ℝ → ℝ} {S : Set ℝ} {c : ℝ} (hb : ∀ x ∈ S, f x ≤ c) :
    BddAbove (f '' S) := ⟨c, by rintro _ ⟨y, hy, rfl⟩; exact hb y hy⟩

private lemma pcr_uniform_bundle (I : Set ℝ) (f : ℕ → ℝ → ℝ) (g : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf0 : ∀ k s, 0 ≤ f k s) (hg0 : ∀ k, 0 ≤ g k)
    (hf : ∀ k s, s ∈ I → f k s ≤ C * g k) (hg : Tendsto g atTop (nhds 0)) :
    (∀ k, BddAbove ((f k) '' I)) ∧
      Tendsto (fun k => ⨆ s ∈ I, f k s) atTop (nhds 0) ∧
      ∀ k, ⨆ s ∈ I, f k s ≤ C * g k := by
  have hCg0 : ∀ k, 0 ≤ C * g k := fun k => mul_nonneg hC (hg0 k)
  have hsup : ∀ k, ⨆ s ∈ I, f k s ≤ C * g k := fun k =>
    pcr_biSup_le (hf k) (hCg0 k)
  refine ⟨fun k => pcr_bddAbove (hf k), ?_, hsup⟩
  have hCg : Tendsto (fun k => C * g k) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hg
  exact squeeze_zero
    (fun k => pcr_biSup_nonneg (fun s => hf0 k s))
    hsup hCg

private lemma pcr_rBfresh_tendsto {m n : ℕ → ℕ} (A : ∀ k, Mat (m k) (n k))
    (hA : ∀ k, fro (A k) = 1) (hAn : Tendsto (fun k => opNorm (A k)) atTop (nhds 0)) (Q : ℝ) :
    Tendsto (fun k => rBfresh (A k) Q) atTop (nhds 0) := by
  let P : ∀ k, Measure (Vec (m k) × Vec (n k)) := fun k => gaussPair (m k) (n k)
  have hlaw : ∀ k, (P k).map (fun x => (x.1, x.2)) = gaussPair (m k) (n k) := by
    intro k
    have heq : (fun x : Vec (m k) × Vec (n k) => (x.1, x.2)) = id := by funext x; exact x.eta.symm
    rw [heq, Measure.map_id]
  have h := lem_app_de_gaussian P A (fun _ x => x.1) (fun _ x => x.2) hlaw hA hAn Q
  simpa only [rBfresh, freshExp, freshMeas, gaussPair, P, resid] using h

private lemma pcr_fresh_psi_bound {m n : ℕ} (A : Mat m n) (hA : fro A = 1) {x : ℝ}
    (hx : 0 ≤ x) : |freshExp A (fun d => psiX x d) - Muon.DetEquiv.J x| ≤ 1 := by
  have h2 := (lem_app_setup_residual_i A hA).2.1
  have hint2 : Integrable (fun p : Vec m × Vec n => resid A p ^ 2) (gaussPair m n) := by
    by_contra h
    rw [integral_undef h] at h2
    norm_num at h2
  have hcont : Continuous (fun p : Vec m × Vec n => psiX x (resid A p)) := by
    unfold psiX resid
    refine Continuous.div (by fun_prop) (by fun_prop) fun p => ?_
    have := mul_nonneg hx (sq_nonneg (dotProduct p.1 (A.mulVec p.2)))
    linarith
  have hint : Integrable (fun p : Vec m × Vec n => psiX x (resid A p)) (gaussPair m n) := by
    refine hint2.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    show ‖psiX x (resid A p)‖ ≤ resid A p ^ 2
    rw [Real.norm_eq_abs]
    unfold psiX
    have hden : (1 : ℝ) ≤ 1 + x * resid A p ^ 2 := by
      nlinarith [mul_nonneg hx (sq_nonneg (resid A p))]
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (zero_le_one.trans hden))]
    exact div_le_self (sq_nonneg _) hden
  have hle : ∫ p, psiX x (resid A p) ∂(gaussPair m n) ≤ 1 := by
    rw [← h2]
    refine integral_mono hint hint2 fun p => ?_
    unfold psiX
    have hden : (1 : ℝ) ≤ 1 + x * resid A p ^ 2 := by
      nlinarith [mul_nonneg hx (sq_nonneg (resid A p))]
    exact (div_le_self (sq_nonneg _) hden)
  have hge : 0 ≤ ∫ p, psiX x (resid A p) ∂(gaussPair m n) := by
    refine integral_nonneg fun p => ?_
    unfold psiX
    exact div_nonneg (sq_nonneg _) (by positivity)
  have hJ := lem_app_de_scalar_i.2.2.1 x hx
  change |∫ p, psiX x (resid A p) ∂(gaussPair m n) - Muon.DetEquiv.J x| ≤ 1
  rw [abs_le]
  constructor <;> linarith [hJ.1, hJ.2]

private lemma pcr_le_rBfresh {m n : ℕ} (A : Mat m n) (hA : fro A = 1) {Q x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) Q) :
    |freshExp A (fun d => psiX x d) - Muon.DetEquiv.J x| ≤ rBfresh A Q := by
  unfold rBfresh
  exact pcr_le_biSup (fun y hy => pcr_fresh_psi_bound A hA hy.1) zero_le_one hx

private lemma pcr_branch_data {m n B : ℕ} (F : FrozenParams m n B) (w : ℕ → ℝ)
    (hw : WeightClass w) (CS γ s : ℝ) (hCS : 0 < CS) (hγ : 0 < γ)
    (hCo : opNorm F.C.Sout ≤ CS) (hCi : opNorm F.C.Sin ≤ CS)
    (hdim : ((max m n : ℕ) : ℝ) ≤ γ * B) (hs : 0 < s) :
    0 ≤ branchSigma w (specOutFM F) (specInFM F) s ∧
    branchSigma w (specOutFM F) (specInFM F) s ≤ CS * γ / s ∧
    0 ≤ branchQ w (specOutFM F) (specInFM F) s ∧
    branchQ w (specOutFM F) (specInFM F) s ≤ (CS * γ) ^ 2 / s ∧
    0 ≤ (branchSol (Fw w) (specOutFM F) (specInFM F) s).2.2.1 := by
  have hp := spectral_mem_classK F (⟨hCo, hCi, hdim⟩ : DriftBound F CS γ)
  have hspec := branchSol_spec (Fw_admissible hw.1) hCS hγ hp hs
  have hbox := (thm_app_de_branch_i_weight hw.1 hCS hγ _ _ hp s hs).2 _ hspec
  have hnn : ∀ {G : ℝ → ℝ} {ν ν' : FiniteMeasure ℝ} {r : ℝ} {x : ℝ × ℝ × ℝ × ℝ},
      IsBranchSol G ν ν' r x → 0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2.1 ∧ 0 ≤ x.2.2.2 := by
    intro G ν ν' r x h
    obtain ⟨σ, σ', a, c⟩ := x
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  obtain ⟨h1, h2, h3, -⟩ := hnn hspec
  obtain ⟨b1, -, -, -, b5⟩ := hbox
  refine ⟨h1, ?_, ?_, ?_, h3⟩
  · unfold branchSigma; rw [mul_comm]; exact b1
  · unfold branchQ; exact mul_nonneg (mul_nonneg hs.le h1) h2
  · unfold branchQ; rw [mul_comm CS γ]; exact b5

private lemma pcr_bB_close {m n B : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (w : ℕ → ℝ) (hw : WeightClass w) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (s sm CS γ e : ℝ) (hsm : 0 < sm) (hs : sm ≤ s)
    (hCS : 0 < CS) (hγ : 0 < γ) (he0 : 0 ≤ e)
    (hCo : opNorm F.C.Sout ≤ CS) (hCi : opNorm F.C.Sin ≤ CS)
    (hdim : ((max m n : ℕ) : ℝ) ≤ γ * B)
    (htarget : ∀ j,
      eLpNorm (fun ω => delAlpha2 w F S t j s ω -
          alphaStar2 w F S t (specOutFM F) (specInFM F) j s ω) 2 P ≤
        ENNReal.ofReal (w j ^ 2 * e)) :
    Summable (fun j => bj w F S t j s) ∧
    |bB w F S t s - branchSigma w (specOutFM F) (specInFM F) s *
        Fw w (branchQ w (specOutFM F) (specInFM F) s)| ≤
      sumPow w 2 * (e + (CS * γ / sm) * rBfresh F.A ((CS * γ) ^ 2 / sm)) := by
  have hspos : 0 < s := hsm.trans_le hs
  obtain ⟨hσ0, hσ, hq0, hq, -⟩ := pcr_branch_data F w hw CS γ s hCS hγ hCo hCi hdim hspos
  have hm : (m : ℝ) ≤ γ * B := (Nat.cast_le.2 (le_max_left m n)).trans hdim
  have hn : (n : ℝ) ≤ γ * B := (Nat.cast_le.2 (le_max_right m n)).trans hdim
  set σ := branchSigma w (specOutFM F) (specInFM F) s with hσdef
  set q := branchQ w (specOutFM F) (specInFM F) s with hqdef
  set Q := (CS * γ) ^ 2 / sm with hQdef
  set r := rBfresh F.A Q with hrdef
  have hC0 : 0 ≤ CS * γ / sm := by positivity
  have hr0 : 0 ≤ r := by
    rw [hrdef]
    exact pcr_biSup_nonneg fun _ => abs_nonneg _
  have hqQ : q ≤ Q := by
    rw [hqdef, hQdef]
    refine hq.trans ?_
    exact div_le_div_of_nonneg_left (sq_nonneg _) hsm (hs)
  have hj : ∀ j, |bj w F S t j s - w j ^ 2 * σ * Muon.DetEquiv.J (w j ^ 2 * q)| ≤
      w j ^ 2 * (e + (CS * γ / sm) * r) := by
    intro j
    have hw0 := hw.1.1 j
    have hw1 := hw.2.1 j
    have hx : w j ^ 2 * q ∈ Icc (0 : ℝ) Q := by
      refine ⟨mul_nonneg (sq_nonneg _) hq0, ?_⟩
      calc w j ^ 2 * q ≤ 1 * q := mul_le_mul_of_nonneg_right (by nlinarith [hw0, hw1]) hq0
        _ ≤ 1 * Q := mul_le_mul_of_nonneg_left hqQ zero_le_one
        _ = Q := one_mul Q
    have hrj := pcr_le_rBfresh F.A F.hA hx
    have hj0 := pcr_bj_close w F S t j s hspos CS γ hγ.le hw0 hw1 hCo hCi hm hn
      σ q e r hσ0 hq0 he0 (by simpa [alphaStar2, xJ, hσdef, hqdef] using htarget j) hrj
    refine hj0.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    have hσC : σ ≤ CS * γ / sm := hσ.trans (div_le_div_of_nonneg_left (by positivity) hsm hs)
    linarith [mul_le_mul_of_nonneg_right hσC hr0]
  have hc0 : 0 ≤ e + (CS * γ / sm) * r := by positivity
  simpa [bB, hσdef, hqdef, hQdef, hrdef] using
    (pcr_sum_close w hw (fun j => bj w F S t j s) σ q
      (e + (CS * γ / sm) * r) hσ0 hq0 hc0 hj)

private lemma pcr_bB_bundle (CS γ : ℝ) (I : Set ℝ) (hI : IsCompact I)
    (hIpos : I ⊆ Set.Ioi 0) (R : Muon.Setup.SetupRegime) (hCS : R.CSig = CS)
    (hγ : R.γstar = γ) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (w : ℕ → ℝ) (hw : WeightClass w) (eStar : ℕ → ℝ)
    (he0 : ∀ k, 0 ≤ eStar k) (het : Tendsto eStar atTop (nhds 0))
    (htarget : ∀ k j s, s ∈ I →
      eLpNorm (fun ω => delAlpha2 w (R.F k) (S k) t j s ω -
          alphaStar2 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
        2 (P k) ≤ ENNReal.ofReal (w j ^ 2 * eStar k)) :
    (∀ k : ℕ, ∀ s ∈ I, 0 ≤ bB w (R.F k) (S k) t s) ∧
    (∀ k : ℕ, BddAbove ((fun s => |bB w (R.F k) (S k) t s
        - branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s *
          Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)|) '' I)) ∧
    (∀ k : ℕ, ⨆ s ∈ I, |bB w (R.F k) (S k) t s
        - branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s *
          Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)| ≤
      sumPow w 2 * (eStar k + (CS * γ / sInf I) *
        rBfresh (R.F k).A (qIbound CS γ I))) ∧
    Tendsto (fun k => ⨆ s ∈ I, |bB w (R.F k) (S k) t s
        - branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s *
          Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)|) atTop (nhds 0) := by
  rcases I.eq_empty_or_nonempty with hIe | hIne
  · subst I
    simp
    exact fun k => mul_nonneg (tsum_nonneg fun _ => sq_nonneg _) (he0 k)
  have hsmem : sInf I ∈ I := hI.sInf_mem hIne
  have hsm : 0 < sInf I := hIpos hsmem
  have hs : ∀ s ∈ I, sInf I ≤ s := fun s hsI => csInf_le hI.bddBelow hsI
  have hCp : 0 < R.CSig := lt_of_lt_of_le one_pos R.hC
  have hγp := pcr_gamma_pos R
  have hclose : ∀ k s, s ∈ I →
      |bB w (R.F k) (S k) t s - branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s *
          Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)| ≤
        sumPow w 2 * (eStar k + (CS * γ / sInf I) *
          rBfresh (R.F k).A (qIbound CS γ I)) := by
    intro k s hsI
    have h0 := pcr_bB_close w hw (R.F k) (S k) t s (sInf I) R.CSig R.γstar (eStar k)
      hsm (hs s hsI) hCp hγp (he0 k) (R.normOut k) (R.normIn k) (R.dims k)
      (fun j => htarget k j s hsI)
    simpa [hCS, hγ, qIbound] using h0.2
  have hbound0 : ∀ k, 0 ≤ sumPow w 2 * (eStar k + (CS * γ / sInf I) *
      rBfresh (R.F k).A (qIbound CS γ I)) := by
    intro k
    have hr0 : 0 ≤ rBfresh (R.F k).A (qIbound CS γ I) :=
      pcr_biSup_nonneg fun _ => abs_nonneg _
    have hC0 : 0 ≤ CS * γ / sInf I := by rw [← hCS, ← hγ]; positivity
    have hsum0 : 0 ≤ sumPow w 2 := tsum_nonneg fun _ => sq_nonneg _
    exact mul_nonneg hsum0 (add_nonneg (he0 k) (mul_nonneg hC0 hr0))
  refine ⟨fun k s hsI => pcr_bB_nonneg w (R.F k) (S k) t s (hIpos hsI), ?_, ?_, ?_⟩
  · exact fun k => pcr_bddAbove (hclose k)
  · exact fun k => pcr_biSup_le (hclose k) (hbound0 k)
  · have hr := pcr_rBfresh_tendsto (fun k => (R.F k).A) (fun k => (R.F k).hA)
        R.diffuse (qIbound CS γ I)
    have hRHS : Tendsto (fun k => sumPow w 2 * (eStar k + (CS * γ / sInf I) *
        rBfresh (R.F k).A (qIbound CS γ I))) atTop (nhds 0) := by
      convert tendsto_const_nhds.mul (het.add (tendsto_const_nhds.mul hr)) using 1 <;> ring
    exact squeeze_zero
      (fun k => pcr_biSup_nonneg (fun _ => abs_nonneg _))
      (fun k => pcr_biSup_le (hclose k) (hbound0 k)) hRHS

private lemma pcr_abs_target {m n B : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (w : ℕ → ℝ) (hw : WeightClass w) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (ν ν' : FiniteMeasure ℝ) (e : ℝ)
    (h : ∀ j s,
      eLpNorm (fun ω => delAlpha1 w F S t j s ω - alphaStar1 w F S t ν ν' j s ω) 2 P ≤
          ENNReal.ofReal (w j * e) ∧
      eLpNorm (fun ω => delAlpha2 w F S t j s ω - alphaStar2 w F S t ν ν' j s ω) 2 P ≤
          ENNReal.ofReal (w j ^ 2 * e)) :
    ∀ j s,
      eLpNorm (fun ω => delAlpha1 w F S t j s ω - alphaStar1 w F S t ν ν' j s ω) 2 P ≤
          ENNReal.ofReal (w j * |e|) ∧
      eLpNorm (fun ω => delAlpha2 w F S t j s ω - alphaStar2 w F S t ν ν' j s ω) 2 P ≤
          ENNReal.ofReal (w j ^ 2 * |e|) := by
  intro j s
  refine ⟨(h j s).1.trans ?_, (h j s).2.trans ?_⟩
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_abs_self e) (hw.1.1 j))
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_abs_self e) (sq_nonneg _))

private lemma pcr_inv_sqrt_B (R : Muon.Setup.SetupRegime) :
    Tendsto (fun k => 1 / Real.sqrt ((R.B k : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hcast : Tendsto (fun k => ((R.B k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp R.prop.B_top
  have hsqrt : Tendsto (fun k => Real.sqrt ((R.B k : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  simp only [one_div]
  exact tendsto_inv_atTop_zero.comp hsqrt

private lemma pcr_error_scale_tendsto (CS γ : ℝ) (I : Set ℝ)
    (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (t : ℤ) (w : ℕ → ℝ) {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0))
    (hdelta : Tendsto (fun k => deltaB w (R.F k) (S k) t
      (specOutFM (R.F k)) (specInFM (R.F k)) I) atTop (𝓝 0)) :
    Tendsto (fun k => e k + rPrimeB (R.F k).A (qIbound CS γ I) + opNorm (R.F k).A
      + opNorm (R.F k).A ^ 2 + deltaB w (R.F k) (S k) t
        (specOutFM (R.F k)) (specInFM (R.F k)) I
      + 1 / Real.sqrt ((R.B k : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hr := lem_app_drift_gaussian (fun k => (R.F k).A) (fun k => (R.F k).hA)
    R.diffuse (qIbound CS γ I)
  have hA2 : Tendsto (fun k => opNorm (R.F k).A ^ 2) atTop (𝓝 0) := by
    simpa using R.diffuse.pow 2
  simpa using (((he.add hr).add R.diffuse).add hA2).add hdelta |>.add (pcr_inv_sqrt_B R)

private lemma pcr_assemble (CS γ : ℝ) (I : Set ℝ) (hI : IsCompact I)
    (hIpos : I ⊆ Set.Ioi 0) (CI : ℝ) (R : Muon.Setup.SetupRegime)
    (hCS : R.CSig = CS) (hγ : R.γstar = γ)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (w : ℕ → ℝ) (hw : WeightClass w) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (htarget : ∀ k j s, s ∈ I →
      eLpNorm (fun ω => delAlpha1 w (R.F k) (S k) t j s ω -
          alphaStar1 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
        2 (P k) ≤ ENNReal.ofReal (w j * e k) ∧
      eLpNorm (fun ω => delAlpha2 w (R.F k) (S k) t j s ω -
          alphaStar2 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
        2 (P k) ≤ ENNReal.ofReal (w j ^ 2 * e k))
    (hEBbdd : ∀ k, BddAbove ((fun s => fro (EB w (R.F k) (S k) t (specOutFM (R.F k))
        (specInFM (R.F k)) s)) '' I))
    (hEBlim : Tendsto (fun k => ⨆ s ∈ I, fro (EB w (R.F k) (S k) t
        (specOutFM (R.F k)) (specInFM (R.F k)) s)) atTop (𝓝 0))
    (hEB : ∀ k, ⨆ s ∈ I, fro (EB w (R.F k) (S k) t (specOutFM (R.F k))
        (specInFM (R.F k)) s) ≤
      CI * (|e k| + rPrimeB (R.F k).A (qIbound CS γ I) + opNorm (R.F k).A
        + opNorm (R.F k).A ^ 2 + deltaB w (R.F k) (S k) t (specOutFM (R.F k))
          (specInFM (R.F k)) I + 1 / Real.sqrt ((R.B k : ℕ) : ℝ))) :
    ∃ eStar : ℕ → ℝ, Tendsto eStar atTop (𝓝 0) ∧
      (∀ k : ℕ, ∀ j : ℕ, ∀ s ∈ I,
        eLpNorm (fun ω => delAlpha1 w (R.F k) (S k) t j s ω
            - alphaStar1 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
          2 (P k) ≤ ENNReal.ofReal (w j * eStar k) ∧
        eLpNorm (fun ω => delAlpha2 w (R.F k) (S k) t j s ω
            - alphaStar2 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
          2 (P k) ≤ ENNReal.ofReal (w j ^ 2 * eStar k)) ∧
      (∀ k : ℕ, ∀ s ∈ I,
        Hmix w (R.F k) (S k) t s * YB w (R.F k) (S k) t s =
          (Lw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)) •
            (Rbar (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s * EG (R.F k))
          + EB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) s) ∧
      (∀ k : ℕ, BddAbove ((fun s => fro (EB w (R.F k) (S k) t (specOutFM (R.F k))
          (specInFM (R.F k)) s)) '' I)) ∧
      Tendsto (fun k => ⨆ s ∈ I, fro (EB w (R.F k) (S k) t (specOutFM (R.F k))
          (specInFM (R.F k)) s)) atTop (𝓝 0) ∧
      (∀ k : ℕ, ⨆ s ∈ I, fro (EB w (R.F k) (S k) t (specOutFM (R.F k))
          (specInFM (R.F k)) s) ≤
        CI * (eStar k + rPrimeB (R.F k).A (qIbound CS γ I) + opNorm (R.F k).A
          + opNorm (R.F k).A ^ 2 + deltaB w (R.F k) (S k) t (specOutFM (R.F k))
            (specInFM (R.F k)) I + 1 / Real.sqrt ((R.B k : ℕ) : ℝ))) ∧
      (∀ k : ℕ, ∀ s ∈ I, 0 ≤ bB w (R.F k) (S k) t s) ∧
      (∀ k : ℕ, BddAbove ((fun s => |bB w (R.F k) (S k) t s
          - branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s *
            Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)|) '' I)) ∧
      (∀ k : ℕ, ⨆ s ∈ I, |bB w (R.F k) (S k) t s
          - branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s *
            Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)| ≤
        sumPow w 2 * (eStar k + (CS * γ / sInf I) *
          rBfresh (R.F k).A (qIbound CS γ I))) ∧
      Tendsto (fun k => ⨆ s ∈ I, |bB w (R.F k) (S k) t s
          - branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s *
            Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)|) atTop (𝓝 0) := by
  let eStar : ℕ → ℝ := fun k => |e k|
  have heStar : Tendsto eStar atTop (𝓝 0) := by
    simpa [eStar] using he.abs
  have he0 : ∀ k, 0 ≤ eStar k := fun k => abs_nonneg _
  have ht : ∀ k j s, s ∈ I →
      eLpNorm (fun ω => delAlpha1 w (R.F k) (S k) t j s ω -
          alphaStar1 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
        2 (P k) ≤ ENNReal.ofReal (w j * eStar k) ∧
      eLpNorm (fun ω => delAlpha2 w (R.F k) (S k) t j s ω -
          alphaStar2 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
        2 (P k) ≤ ENNReal.ofReal (w j ^ 2 * eStar k) := by
    intro k j s hs
    refine ⟨(htarget k j s hs).1.trans ?_, (htarget k j s hs).2.trans ?_⟩
    · exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (le_abs_self (e k)) (hw.1.1 j))
    · exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (le_abs_self (e k)) (sq_nonneg _))
  obtain ⟨hb0, hbBdd, hb, hblim⟩ := pcr_bB_bundle CS γ I hI hIpos R hCS hγ P S t w hw
    eStar he0 heStar (fun k j s hs => (ht k j s hs).2)
  refine ⟨eStar, heStar, ht, ?_, hEBbdd, hEBlim, ?_, hb0, hbBdd, hb, hblim⟩
  · intro k s _
    exact pcr_identity w (R.F k) (S k) t _ _ s
  · simpa [eStar] using hEB


-- PE-HELPERS-BEGIN

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

private theorem pe_src_err (s0 : ℝ) (hs0 : 0 < s0) (CS γ Q : ℝ) (hγ : 0 ≤ γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), 0 ≤ w j → w j ≤ 1 →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, s0 ≤ s → ∀ x e : ℝ, 0 ≤ x → x ≤ Q → 0 ≤ e →
        eLpNorm (fun ω => delAlpha1 w F S t j s ω - w j * fX x (ageD F S t j ω)) 2 P ≤
          ENNReal.ofReal (w j * e) →
        fro ((B : ℝ) • Muon.mean P (fun ω => delAlpha1 w F S t j s ω •
            (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))) -
          (w j * ∫ p, deriv (fX x) (resid F.A p) ∂(gaussPair m n)) •
            (expDelRes w F S t j (slotOne F.hB) s * EG F)) ≤
          K * w j * (e + opNorm F.A ^ 2) := by
  obtain ⟨Cc, hCc0, hCc⟩ := pe_facts s0 hs0 CS γ hγ
  refine ⟨|CS| / s0 * (1 + 36 * |Q|), by positivity, ?_⟩
  intro Ω inst m n B P _ F S t j w hw0 hw1 hCo hCi hm hn s hs x e hx hxQ he he1
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
  have hs1 : 1 / s ≤ 1 / s0 := one_div_le_one_div_of_le hs0 hs
  have hCs1 : CS / s ≤ |CS| / s0 :=
    div_le_div₀ (abs_nonneg _) (le_abs_self _) hs0 hs
  calc _ ≤ CS / s * (w j * e) + 1 / s * CS * (w j * (36 * x * opNorm F.A ^ 2)) := add_le_add hb1' hmain
    _ ≤ |CS| / s0 * (w j * e) + |CS| / s0 * (w j * (36 * |Q| * opNorm F.A ^ 2)) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_right hCs1 (mul_nonneg hw0 he)
        · have h1 : 1 / s * CS = CS / s := by ring
          rw [h1]
          refine mul_le_mul hCs1 ?_ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hxQ.trans (le_abs_self Q)) (by norm_num)) hA0) hw0
    _ ≤ _ := by
        rw [← sub_nonneg]
        have hh : |CS| / s0 * (1 + 36 * |Q|) * w j * (e + opNorm F.A ^ 2) -
            (|CS| / s0 * (w j * e) + |CS| / s0 * (w j * (36 * |Q| * opNorm F.A ^ 2))) =
            |CS| / s0 * w j * opNorm F.A ^ 2 + 36 * (|CS| / s0) * |Q| * w j * e := by ring
        rw [hh]
        positivity

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
private theorem pe_gram_err (s0 : ℝ) (hs0 : 0 < s0) (CS γ Sb : ℝ) (hγ : 0 ≤ γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), 0 ≤ w j → w j ≤ 1 →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, s0 ≤ s → ∀ x σ e : ℝ, 0 ≤ x → 0 ≤ σ → σ ≤ Sb → 0 ≤ e →
        eLpNorm (fun ω => delAlpha2 w F S t j s ω - w j ^ 2 * σ * psiX x (ageD F S t j ω)) 2 P ≤
          ENNReal.ofReal (w j ^ 2 * e) →
        fro ((B : ℝ) • Muon.mean P (fun ω => delAlpha2 w F S t j s ω •
            (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))) -
          (bj w F S t j s • Hj w F S t j s + Cj w F S t j s) * F.C.Sin) ≤
          |CS| / (2 * Real.sqrt s0) * (2 + 6 * |Sb|) * w j ^ 2 * (e + opNorm F.A) := by
  obtain ⟨Cc, hCc0, hCc⟩ := pe_facts s0 hs0 CS γ hγ
  refine ⟨|CS| / (2 * Real.sqrt s0) * (2 + 6 * |Sb|), by positivity, ?_⟩
  intro Ω inst m n B P _ F S t j w hw0 hw1 hCo hCi hm hn s hs x σ e hx hσ hσS he he2
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
  have hs0s : Real.sqrt s0 ≤ Real.sqrt s := Real.sqrt_le_sqrt hs
  have hsq0 : 0 < Real.sqrt s0 := Real.sqrt_pos.2 hs0
  have hcoef : CS / (2 * Real.sqrt s) ≤ |CS| / (2 * Real.sqrt s0) :=
    div_le_div₀ (abs_nonneg _) (le_abs_self _) (by positivity)
      (mul_le_mul_of_nonneg_left hs0s (by norm_num))
  have hcoef0 : 0 ≤ CS / (2 * Real.sqrt s) := by positivity
  have hA0 : 0 ≤ opNorm A := tlb_opNorm_nonneg _
  have hinner : Real.sqrt 2 * ∫ ζ, Real.sqrt (condExp (sigmaOthers F S t j) P
      (fun ω => d2 ω ^ 2) ζ) ∂P + c2 * (6 * opNorm A) ≤
      (2 + 6 * |Sb|) * w j ^ 2 * (e + opNorm A) := by
    have hI0 : 0 ≤ ∫ ζ, Real.sqrt (condExp (sigmaOthers F S t j) P (fun ω => d2 ω ^ 2) ζ) ∂P :=
      integral_nonneg fun ζ => Real.sqrt_nonneg _
    have h1 : Real.sqrt 2 * ∫ ζ, Real.sqrt (condExp (sigmaOthers F S t j) P
        (fun ω => d2 ω ^ 2) ζ) ∂P ≤ 2 * (w j ^ 2 * e) :=
      mul_le_mul hsq2 hd2n hI0 (by norm_num)
    have h2 : c2 * (6 * opNorm A) ≤ 6 * |Sb| * w j ^ 2 * opNorm A := by
      have : c2 ≤ |Sb| * w j ^ 2 := by
        simp only [hc2def]
        nlinarith [sq_nonneg (w j), le_abs_self Sb, mul_le_mul_of_nonneg_left hσS (sq_nonneg (w j))]
      nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hA0)]
    have h3 : 0 ≤ 2 * w j ^ 2 * opNorm A + 6 * |Sb| * w j ^ 2 * e := by positivity
    have hh : (2 + 6 * |Sb|) * w j ^ 2 * (e + opNorm A) = 2 * (w j ^ 2 * e) +
        6 * |Sb| * w j ^ 2 * opNorm A + (2 * w j ^ 2 * opNorm A + 6 * |Sb| * w j ^ 2 * e) := by ring
    generalize (∫ ζ, Real.sqrt (condExp (sigmaOthers F S t j) P (fun ω => d2 ω ^ 2) ζ) ∂P) = II
      at h1 ⊢
    rw [hh]
    linarith
  calc CS / (2 * Real.sqrt s) * (Real.sqrt 2 * ∫ ζ, Real.sqrt (condExp (sigmaOthers F S t j) P
        (fun ω => d2 ω ^ 2) ζ) ∂P + c2 * (6 * opNorm A))
      ≤ |CS| / (2 * Real.sqrt s0) * ((2 + 6 * |Sb|) * w j ^ 2 * (e + opNorm A)) := by
        refine mul_le_mul hcoef hinner ?_ (by positivity)
        exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg fun ζ => Real.sqrt_nonneg _))
          (mul_nonneg hc20 (mul_nonneg (by norm_num) hA0))
    _ = _ := by ring

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

section PePj0
open ProbabilityTheory

private lemma pe_branch_data {m n B : ℕ} (F : FrozenParams m n B) (w : ℕ → ℝ)
    (hw : WeightClass w) (CS γ s : ℝ) (hCS : 0 < CS) (hγ : 0 < γ)
    (hCo : opNorm F.C.Sout ≤ CS) (hCi : opNorm F.C.Sin ≤ CS)
    (hdim : ((max m n : ℕ) : ℝ) ≤ γ * B) (hs : 0 < s) :
    0 ≤ branchSigma w (specOutFM F) (specInFM F) s ∧
    branchSigma w (specOutFM F) (specInFM F) s ≤ CS * γ / s ∧
    0 ≤ branchQ w (specOutFM F) (specInFM F) s ∧
    branchQ w (specOutFM F) (specInFM F) s ≤ (CS * γ) ^ 2 / s ∧
    0 ≤ (branchSol (Fw w) (specOutFM F) (specInFM F) s).2.2.1 := by
  have hp := spectral_mem_classK F (⟨hCo, hCi, hdim⟩ : DriftBound F CS γ)
  have hspec := branchSol_spec (Fw_admissible hw.1) hCS hγ hp hs
  have hbox := (thm_app_de_branch_i_weight hw.1 hCS hγ _ _ hp s hs).2 _ hspec
  have hnn : ∀ {G : ℝ → ℝ} {ν ν' : FiniteMeasure ℝ} {r : ℝ} {x : ℝ × ℝ × ℝ × ℝ},
      IsBranchSol G ν ν' r x → 0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2.1 ∧ 0 ≤ x.2.2.2 := by
    intro G ν ν' r x h
    obtain ⟨σ, σ', a, c⟩ := x
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  obtain ⟨h1, h2, h3, -⟩ := hnn hspec
  obtain ⟨b1, -, -, -, b5⟩ := hbox
  refine ⟨h1, ?_, ?_, ?_, h3⟩
  · unfold branchSigma; rw [mul_comm]; exact b1
  · unfold branchQ; exact mul_nonneg (mul_nonneg hs.le h1) h2
  · unfold branchQ; rw [mul_comm CS γ]; exact b5


private lemma pe_rprime_bound {m n : ℕ} (A : Mat m n) (hA : fro A = 1) {Q x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) Q) :
    |(∫ p, deriv (fX x) (resid A p) ∂(gaussPair m n)) - Muon.DetEquiv.J x| ≤ rPrimeB A Q := by
  unfold rPrimeB
  refine le_trans (le_of_eq rfl) (pe_le_biSup
    (f := fun x => |freshExp A (fun d => deriv (fX x) d) - Muon.DetEquiv.J x|) (c := 2)
    (fun y hy => ?_) (by norm_num) hx)
  obtain ⟨-, -, hb1, -⟩ := gc_f_hyp hy.1
  have hint : |∫ p, deriv (fX y) (resid A p) ∂(gaussPair m n)| ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := gaussPair m n)
      (f := fun p => deriv (fX y) (resid A p)) (C := 1)
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hb1 _)
    simpa using this
  have hJ := lem_app_de_scalar_i.2.2.1 y hy.1
  show |(∫ p, deriv (fX y) (resid A p) ∂(gaussPair m n)) - Muon.DetEquiv.J y| ≤ 2
  rw [abs_le] at hint ⊢
  constructor <;> linarith [hJ.1, hJ.2]

private lemma pe_Rbar_op {m n : ℕ} (C : Covariances m n) (G : ℝ → ℝ) (ν ν' : FiniteMeasure ℝ)
    {s : ℝ} (hs : 0 < s) (ha : 0 ≤ (branchSol G ν ν' s).2.2.1) :
    opNorm (Rbar G ν ν' C s) ≤ 1 / s :=
  kern_inv_opNorm_le C.Sout C.psdOut ha hs

private lemma pe_Rtbar_op {m n : ℕ} (C : Covariances m n) (G : ℝ → ℝ) (ν ν' : FiniteMeasure ℝ)
    {s : ℝ} (hs : 0 < s) (ha : 0 ≤ (branchSol G ν ν' s).2.2.2) :
    opNorm (Rtbar G ν ν' C s) ≤ 1 / s :=
  kern_inv_opNorm_le C.Sin C.psdIn ha hs

end PePj0

section PePerj
open ProbabilityTheory


open scoped Matrix.Norms.L2Operator in
private lemma pe_opNorm_sub_le {a b : ℕ} (A B' : Mat a b) :
    opNorm (A - B') ≤ opNorm A + opNorm B' := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact norm_sub_le _ _

private lemma pe_fro_sub {a b : ℕ} (A B' : Mat a b) : fro (A - B') ≤ fro A + fro B' := by
  have : A - B' = A + (-1 : ℝ) • B' := by simp [sub_eq_add_neg]
  rw [this]
  refine (tlb_fro_add _ _).trans ?_
  rw [tlb_fro_smul]
  simp

private lemma pe_perj_identity {m n : ℕ} (SRC GRM H Hj Cj EG : Matrix (Fin m) (Fin n) ℝ)
    (Sin : Matrix (Fin n) (Fin n) ℝ) (P Pj Rb : Matrix (Fin m) (Fin m) ℝ) (b wj jx Jx : ℝ) :
    SRC - GRM + b • (H * Sin) - (wj * Jx) • (Rb * EG) =
      (SRC - (wj * jx) • (Pj * EG)) - (GRM - (b • Hj + Cj) * Sin) - (wj * jx) • ((P - Pj) * EG)
        + (wj * jx) • ((P - Rb) * EG) + (wj * (jx - Jx)) • (Rb * EG) + b • ((H - Hj) * Sin)
        - Cj * Sin := by
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, smul_sub, sub_smul, mul_sub, mul_smul]
  abel

set_option maxHeartbeats 2000000 in
private theorem pe_perj (CS γ : ℝ) (hCS : 0 < CS) (hγ : 0 < γ) (I : Set ℝ) (hI : IsCompact I)
    (hIpos : I ⊆ Set.Ioi 0) (sm : ℝ) (hsm : 0 < sm) (hsmI : ∀ s ∈ I, sm ≤ s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), WeightClass w → opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      ((max m n : ℕ) : ℝ) ≤ γ * B → ∀ s ∈ I, ∀ e : ℝ, 0 ≤ e →
        eLpNorm (fun ω => delAlpha1 w F S t j s ω -
          alphaStar1 w F S t (specOutFM F) (specInFM F) j s ω) 2 P ≤ ENNReal.ofReal (w j * e) →
        eLpNorm (fun ω => delAlpha2 w F S t j s ω -
          alphaStar2 w F S t (specOutFM F) (specInFM F) j s ω) 2 P ≤
          ENNReal.ofReal (w j ^ 2 * e) →
        fro ((B : ℝ) • Muon.mean P (fun ω => delAlpha1 w F S t j s ω •
              (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))
            - delAlpha2 w F S t j s ω •
              (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))) +
          bj w F S t j s • (Hmix w F S t s * F.C.Sin) -
          (w j * J (xJ w (specOutFM F) (specInFM F) j s)) •
            (Rbar (Fw w) (specOutFM F) (specInFM F) F.C s * EG F)) ≤
          K * w j * (e + rPrimeB F.A (qIbound CS γ I) + opNorm F.A + opNorm F.A ^ 2 +
            deltaB w F S t (specOutFM F) (specInFM F) I + 1 / Real.sqrt (B : ℝ)) := by
  set Q := qIbound CS γ I with hQdef
  set Sb := CS * γ / sm with hSbdef
  set Kg := |CS| / (2 * Real.sqrt sm) * (2 + 6 * |Sb|) with hKgdef
  obtain ⟨K1, hK1, h1⟩ := pe_src_err sm hsm CS γ Q hγ.le
  obtain ⟨-, -, h2⟩ := pe_gram_err sm hsm CS γ Sb hγ.le
  obtain ⟨Cpj, hCpj, hpj⟩ := eqn_app_de_Pj_P I hI hIpos CS γ
  obtain ⟨Kb, hKb⟩ := pe_b sm hsm CS γ hγ.le
  obtain ⟨Ch, hCh⟩ := lem_app_drift_multiplier_ii_weights sm hsm CS γ hγ.le
  obtain ⟨Cv, hCv⟩ := lem_app_drift_covariance_weights sm hsm CS γ hγ.le
  have hsq0 : 0 < Real.sqrt sm := Real.sqrt_pos.2 hsm
  have hKg0 : 0 ≤ Kg := by positivity
  refine ⟨K1 + Kg + Cpj * CS + CS + CS / sm + |Kb| * |Ch| * CS / sm ^ 2 +
    |Cv| * CS / (sm * Real.sqrt sm), by positivity, ?_⟩
  intro Ω inst m n B P _ F S t j w hw hCo hCi hdim s hs e he he1 he2
  have hsp : 0 < s := hIpos hs
  have hsms : sm ≤ s := hsmI s hs
  have hm : (m : ℝ) ≤ γ * B := (Nat.cast_le.2 (le_max_left m n)).trans hdim
  have hn : (n : ℝ) ≤ γ * B := (Nat.cast_le.2 (le_max_right m n)).trans hdim
  have hw0 : 0 ≤ w j := hw.1.1 j
  have hw1 : w j ≤ 1 := hw.2.1 j
  have hB : 0 < B := F.hB
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hsB : 1 ≤ Real.sqrt (B : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hBr
  have hsB0 : 0 < Real.sqrt (B : ℝ) := lt_of_lt_of_le one_pos hsB
  have hw2 : w j ^ 2 ≤ w j := by rw [sq]; exact mul_le_of_le_one_right hw0 hw1
  obtain ⟨hσ0, hσle, hq0, hqle, hs1⟩ := pe_branch_data F w hw CS γ s hCS hγ hCo hCi hdim hsp
  have hsI : sInf I ∈ I := hI.sInf_mem ⟨s, hs⟩
  have hsIp : 0 < sInf I := hIpos hsI
  have hsIs : sInf I ≤ s := csInf_le hI.bddBelow hs
  set σ := branchSigma w (specOutFM F) (specInFM F) s with hσdef
  set x := xJ w (specOutFM F) (specInFM F) j s with hxdef
  have hx0 : 0 ≤ x := mul_nonneg (sq_nonneg _) hq0
  have hxQ : x ≤ Q := by
    have : x ≤ branchQ w (specOutFM F) (specInFM F) s := by
      show w j ^ 2 * branchQ w (specOutFM F) (specInFM F) s ≤ _
      exact mul_le_of_le_one_left hq0 (by nlinarith)
    refine this.trans (hqle.trans ?_)
    exact div_le_div_of_nonneg_left (sq_nonneg _) hsIp hsIs
  have hσS : σ ≤ Sb := hσle.trans (div_le_div_of_nonneg_left (mul_nonneg hCS.le hγ.le) hsm hsms)
  -- the three ingredients from the previous steps
  obtain ⟨Cc, hCc0, hCc⟩ := pe_facts sm hsm CS γ hγ.le
  obtain ⟨-, hA1, hA2, L1, L2, -, -, -, -⟩ := hCc Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hsms
  obtain ⟨hint2, -⟩ := pe_gram_decomp sm hsm CS γ hγ.le Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hsms
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
  -- abbreviations
  set jx : ℝ := ∫ p, deriv (fX x) (resid F.A p) ∂(gaussPair m n) with hjxdef
  set b := bj w F S t j s with hbdef
  set a := opNorm F.A with hadef
  set rp := rPrimeB F.A Q with hrpdef
  set dl := deltaB w F S t (specOutFM F) (specInFM F) I with hdldef
  set ι := 1 / Real.sqrt (B : ℝ) with hιdef
  have ha0 : 0 ≤ a := tlb_opNorm_nonneg _
  have hrp0 : 0 ≤ rp := Real.iSup_nonneg fun y => Real.iSup_nonneg fun _ => abs_nonneg _
  have hdl0 : 0 ≤ dl := Real.iSup_nonneg fun y => Real.iSup_nonneg fun _ => tlb_opNorm_nonneg _
  have hι0 : 0 ≤ ι := by positivity
  set Θ := e + rp + a + a ^ 2 + dl + ι with hΘdef
  have hΘ0 : 0 ≤ Θ := by positivity
  have hxIcc : x ∈ Icc (0 : ℝ) Q := ⟨hx0, hxQ⟩
  have hjxJ : |jx - J x| ≤ rp := pe_rprime_bound F.A F.hA hxIcc
  obtain ⟨hcd, -, hb1, -⟩ := gc_f_hyp hx0
  have hjx1 : |jx| ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := gaussPair m n)
      (f := fun p => deriv (fX x) (resid F.A p)) (C := 1)
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hb1 _)
    simpa using this
  -- the pieces
  have hD1 := h1 Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hsms x e hx0 hxQ he he1
  have hD2 := h2 Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hsms x σ e hx0 hσ0 hσS he he2
  set Pj := expDelRes w F S t j (slotOne F.hB) s with hPjdef
  set Pm := expRes w F S t s with hPmdef
  set Rb := Rbar (Fw w) (specOutFM F) (specInFM F) F.C s with hRbdef
  have hEG := pe_EG_fro F hCo hCi
  have hPjP : opNorm (Pm - Pj) ≤ Cpj * w j / B :=
    hpj m n B w hw Ω P F S t hCo hCi hm hn j (slotOne F.hB) s hs
  have hRbop : opNorm Rb ≤ 1 / s := pe_Rbar_op F.C (Fw w) _ _ hsp hs1
  have hdelta : opNorm (Pm - Rb) ≤ dl := by
    refine pe_le_biSup (f := fun s' => opNorm (expRes w F S t s' -
      Rbar (Fw w) (specOutFM F) (specInFM F) F.C s')) (c := 2 / sm) (fun s' hs' => ?_)
      (by positivity) hs
    have hsp' : 0 < s' := hIpos hs'
    have hsm' : sm ≤ s' := hsmI s' hs'
    obtain ⟨-, -, -, -, hs1'⟩ := pe_branch_data F w hw CS γ s' hCS hγ hCo hCi hdim hsp'
    have h1' := pe_expRes_op w F S t hsp'
    have h2' := pe_Rbar_op F.C (Fw w) (specOutFM F) (specInFM F) hsp' hs1'
    have hh : 1 / s' ≤ 1 / sm := one_div_le_one_div_of_le hsm hsm'
    calc opNorm (expRes w F S t s' - Rbar (Fw w) (specOutFM F) (specInFM F) F.C s')
        ≤ opNorm (expRes w F S t s') + opNorm (Rbar (Fw w) (specOutFM F) (specInFM F) F.C s') := by
          exact pe_opNorm_sub_le _ _
      _ ≤ 2 / sm := by
          have : 2 / sm = 1 / sm + 1 / sm := by ring
          rw [this]; exact add_le_add (h1'.trans hh) (h2'.trans hh)
  rw [pe_perj_identity _ _ (Hmix w F S t s) (Hj w F S t j s) (Cj w F S t j s) (EG F) F.C.Sin Pm Pj Rb
    b (w j) jx (J x)]
  -- bounds on the seven pieces
  have hBB : 1 / (B : ℝ) ≤ ι := by
    rw [hιdef]
    refine one_div_le_one_div_of_le hsB0 ?_
    nlinarith [Real.mul_self_sqrt (Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  have hwjx : |w j * jx| ≤ w j := by
    rw [abs_mul, abs_of_nonneg hw0]
    exact mul_le_of_le_one_right hw0 hjx1
  have hCSpos : 0 ≤ CS := hCS.le
  have b3 : fro ((w j * jx) • ((Pm - Pj) * EG F)) ≤ Cpj * CS * w j * ι := by
    rw [tlb_fro_smul]
    have h3 : fro ((Pm - Pj) * EG F) ≤ Cpj * w j / B * CS :=
      (tlb_fro_mul_le_left _ _).trans (mul_le_mul hPjP hEG (tlb_fro_nonneg _) (by positivity))
    calc |w j * jx| * fro ((Pm - Pj) * EG F) ≤ w j * (Cpj * w j / B * CS) :=
          mul_le_mul hwjx h3 (tlb_fro_nonneg _) hw0
      _ = (Cpj * CS * w j) * (w j * (1 / B)) := by ring
      _ ≤ (Cpj * CS * w j) * (1 * ι) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hw1 hBB (by positivity) zero_le_one
      _ = _ := by ring
  have b4 : fro ((w j * jx) • ((Pm - Rb) * EG F)) ≤ CS * w j * dl := by
    rw [tlb_fro_smul]
    have h4 : fro ((Pm - Rb) * EG F) ≤ dl * CS :=
      (tlb_fro_mul_le_left _ _).trans (mul_le_mul hdelta hEG (tlb_fro_nonneg _) hdl0)
    calc |w j * jx| * fro ((Pm - Rb) * EG F) ≤ w j * (dl * CS) :=
          mul_le_mul hwjx h4 (tlb_fro_nonneg _) hw0
      _ = _ := by ring
  have b5 : fro ((w j * (jx - J x)) • (Rb * EG F)) ≤ CS / sm * w j * rp := by
    rw [tlb_fro_smul, abs_mul, abs_of_nonneg hw0]
    have h5 : fro (Rb * EG F) ≤ 1 / s * CS :=
      (tlb_fro_mul_le_left _ _).trans (mul_le_mul hRbop hEG (tlb_fro_nonneg _) (by positivity))
    have h5' : 1 / s * CS ≤ CS / sm := by
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_left hCSpos hsm hsms
    calc w j * |jx - J x| * fro (Rb * EG F) ≤ w j * rp * (CS / sm) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hjxJ hw0) (h5.trans h5') (tlb_fro_nonneg _)
            (by positivity)
      _ = _ := by ring
  obtain ⟨hb0, hb1⟩ := hKb Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hsms
  have hHm := hCh Ω m n B P F S t j w hw hCo hCi hm hn s hsms
  obtain ⟨-, hCjb, -, -⟩ := hCv Ω m n B P F S t w ⟨hw.1.1, hw.1.2.1, hw.2.1, hw.2.2⟩ hCo hCi hm hn s hsms
  have hbn : b ≤ |Kb| * w j ^ 2 / sm := by
    refine hb1.trans ?_
    calc Kb * w j ^ 2 / s ≤ |Kb| * w j ^ 2 / s :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Kb) (sq_nonneg _))
            hsp.le
      _ ≤ |Kb| * w j ^ 2 / sm := div_le_div_of_nonneg_left (by positivity) hsm hsms
  have hHn : fro (Hmix w F S t s - Hj w F S t j s) ≤ |Ch| * w j * ι / sm := by
    refine hHm.trans ?_
    calc Ch * w j / (s * Real.sqrt (B : ℝ)) ≤ |Ch| * w j / (s * Real.sqrt (B : ℝ)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Ch) hw0)
            (by positivity)
      _ ≤ |Ch| * w j / (sm * Real.sqrt (B : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_right hsms hsB0.le)
      _ = _ := by rw [hιdef]; field_simp
  have b6 : fro (b • ((Hmix w F S t s - Hj w F S t j s) * F.C.Sin)) ≤
      |Kb| * |Ch| * CS / sm ^ 2 * w j * ι := by
    rw [tlb_fro_smul, abs_of_nonneg hb0]
    have h6 : fro ((Hmix w F S t s - Hj w F S t j s) * F.C.Sin) ≤ |Ch| * w j * ι / sm * CS :=
      (tlb_fro_mul_le_right _ _).trans (mul_le_mul hHn hCi (tlb_opNorm_nonneg _) (by positivity))
    calc b * fro ((Hmix w F S t s - Hj w F S t j s) * F.C.Sin)
        ≤ (|Kb| * w j ^ 2 / sm) * (|Ch| * w j * ι / sm * CS) :=
          mul_le_mul hbn h6 (tlb_fro_nonneg _) (by positivity)
      _ = (|Kb| * |Ch| * CS / sm ^ 2) * (w j ^ 3) * ι := by ring
      _ ≤ (|Kb| * |Ch| * CS / sm ^ 2) * w j * ι := by
          have : w j ^ 3 ≤ w j := by
            calc w j ^ 3 = w j * w j ^ 2 := by ring
              _ ≤ 1 * w j := mul_le_mul hw1 hw2 (sq_nonneg _) zero_le_one
              _ = w j := one_mul _
          have h0 : 0 ≤ |Kb| * |Ch| * CS / sm ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left this h0, hι0]
  have b7 : fro (Cj w F S t j s * F.C.Sin) ≤ |Cv| * CS / (sm * Real.sqrt sm) * w j * ι := by
    refine (tlb_fro_mul_le_right _ _).trans ?_
    have hss : Real.sqrt sm ≤ Real.sqrt s := Real.sqrt_le_sqrt hsms
    have hc : fro (Cj w F S t j s) ≤ |Cv| * w j * ι / (sm * Real.sqrt sm) := by
      refine (hCjb j).trans ?_
      calc Cv * w j ^ 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ))
          ≤ |Cv| * w j ^ 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ)) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Cv) (sq_nonneg _))
              (by positivity)
        _ ≤ |Cv| * w j ^ 2 / (sm * Real.sqrt sm * Real.sqrt (B : ℝ)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul_of_nonneg_right (mul_le_mul hsms hss hsq0.le hsp.le) hsB0.le)
        _ ≤ |Cv| * w j / (sm * Real.sqrt sm * Real.sqrt (B : ℝ)) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw2 (abs_nonneg _)) (by positivity)
        _ = _ := by rw [hιdef]; field_simp
    calc fro (Cj w F S t j s) * opNorm F.C.Sin ≤ (|Cv| * w j * ι / (sm * Real.sqrt sm)) * CS :=
          mul_le_mul hc hCi (tlb_opNorm_nonneg _) (by positivity)
      _ = _ := by ring
  -- assemble
  have key : ∀ X1 X2 X3 X4 X5 X6 X7 : Mat m n,
      fro (X1 - X2 - X3 + X4 + X5 + X6 - X7) ≤
        fro X1 + fro X2 + fro X3 + fro X4 + fro X5 + fro X6 + fro X7 := by
    intro X1 X2 X3 X4 X5 X6 X7
    have c1 := pe_fro_sub (X1 - X2 - X3 + X4 + X5 + X6) X7
    have c2 := tlb_fro_add (X1 - X2 - X3 + X4 + X5) X6
    have c3 := tlb_fro_add (X1 - X2 - X3 + X4) X5
    have c4 := tlb_fro_add (X1 - X2 - X3) X4
    have c5 := pe_fro_sub (X1 - X2) X3
    have c6 := pe_fro_sub X1 X2
    linarith
  refine (key _ _ _ _ _ _ _).trans ?_
  have hΘe : e + a ^ 2 ≤ Θ := by simp only [hΘdef]; linarith [hrp0, ha0, hdl0, hι0]
  have hΘa : e + a ≤ Θ := by simp only [hΘdef]; nlinarith [hrp0, ha0, hdl0, hι0, sq_nonneg a]
  have f1 : K1 * w j * (e + a ^ 2) ≤ K1 * w j * Θ :=
    mul_le_mul_of_nonneg_left hΘe (mul_nonneg hK1 hw0)
  have f2 : Kg * w j ^ 2 * (e + a) ≤ Kg * w j * Θ := by
    calc Kg * w j ^ 2 * (e + a) ≤ Kg * w j * (e + a) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw2 hKg0) (by positivity)
      _ ≤ Kg * w j * Θ := mul_le_mul_of_nonneg_left hΘa (mul_nonneg hKg0 hw0)
  have f3 : Cpj * CS * w j * ι ≤ Cpj * CS * w j * Θ :=
    mul_le_mul_of_nonneg_left (by simp only [hΘdef]; linarith [hrp0, ha0, hdl0, he, sq_nonneg a])
      (by positivity)
  have f4 : CS * w j * dl ≤ CS * w j * Θ :=
    mul_le_mul_of_nonneg_left (by simp only [hΘdef]; linarith [hrp0, ha0, hι0, he, sq_nonneg a])
      (by positivity)
  have f5 : CS / sm * w j * rp ≤ CS / sm * w j * Θ :=
    mul_le_mul_of_nonneg_left (by simp only [hΘdef]; linarith [hdl0, ha0, hι0, he, sq_nonneg a])
      (by positivity)
  have f6 : |Kb| * |Ch| * CS / sm ^ 2 * w j * ι ≤ |Kb| * |Ch| * CS / sm ^ 2 * w j * Θ :=
    mul_le_mul_of_nonneg_left (by simp only [hΘdef]; linarith [hrp0, ha0, hdl0, he, sq_nonneg a])
      (by positivity)
  have f7 : |Cv| * CS / (sm * Real.sqrt sm) * w j * ι ≤ |Cv| * CS / (sm * Real.sqrt sm) * w j * Θ :=
    mul_le_mul_of_nonneg_left (by simp only [hΘdef]; linarith [hrp0, ha0, hdl0, he, sq_nonneg a])
      (by positivity)
  have hKeq : (K1 + Kg + Cpj * CS + CS + CS / sm + |Kb| * |Ch| * CS / sm ^ 2 +
      |Cv| * CS / (sm * Real.sqrt sm)) * w j * Θ =
      K1 * w j * Θ + Kg * w j * Θ + Cpj * CS * w j * Θ + CS * w j * Θ + CS / sm * w j * Θ +
      |Kb| * |Ch| * CS / sm ^ 2 * w j * Θ + |Cv| * CS / (sm * Real.sqrt sm) * w j * Θ := by ring
  rw [hKeq]
  linarith [hD1, hD2, b3, b4, b5, b6, b7]

end PePerj

section PeEB2
open ProbabilityTheory

set_option maxHeartbeats 1000000 in
private theorem pe_EB_bound (CS γ : ℝ) (hCS : 0 < CS) (hγ : 0 < γ) (I : Set ℝ) (hI : IsCompact I)
    (hIpos : I ⊆ Set.Ioi 0) (sm : ℝ) (hsm : 0 < sm) (hsmI : ∀ s ∈ I, sm ≤ s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (w : ℕ → ℝ), WeightClass w → opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      ((max m n : ℕ) : ℝ) ≤ γ * B → ∀ e : ℝ, 0 ≤ e →
      (∀ j : ℕ, ∀ s ∈ I,
        eLpNorm (fun ω => delAlpha1 w F S t j s ω -
          alphaStar1 w F S t (specOutFM F) (specInFM F) j s ω) 2 P ≤ ENNReal.ofReal (w j * e) ∧
        eLpNorm (fun ω => delAlpha2 w F S t j s ω -
          alphaStar2 w F S t (specOutFM F) (specInFM F) j s ω) 2 P ≤
          ENNReal.ofReal (w j ^ 2 * e)) →
      ∀ s ∈ I, fro (EB w F S t (specOutFM F) (specInFM F) s) ≤
        K * (e + rPrimeB F.A (qIbound CS γ I) + opNorm F.A + opNorm F.A ^ 2 +
          deltaB w F S t (specOutFM F) (specInFM F) I + 1 / Real.sqrt (B : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := pe_perj CS γ hCS hγ I hI hIpos sm hsm hsmI
  obtain ⟨Kb, hKb⟩ := pe_b sm hsm CS γ hγ.le
  refine ⟨K, hK0, ?_⟩
  intro Ω inst m n B P _ F S t w hw hCo hCi hdim e he htar s hs
  have hsp : 0 < s := hIpos hs
  have hsms : sm ≤ s := hsmI s hs
  have hm : (m : ℝ) ≤ γ * B := (Nat.cast_le.2 (le_max_left m n)).trans hdim
  have hn : (n : ℝ) ≤ γ * B := (Nat.cast_le.2 (le_max_right m n)).trans hdim
  have hsw : Summable w := hw.1.2.1
  have hexact := lem_app_drift_exact_weights hw F S t s hsp
  -- summability of the coefficients
  have hbs : Summable (fun j => bj w F S t j s) := by
    refine Summable.of_nonneg_of_le (fun j => (hKb Ω m n B P F S t j w (hw.1.1 j) (hw.2.1 j) hCo hCi
      hm hn s hsms).1) (fun j => ?_) ((hsw.mul_left |Kb|).div_const s)
    refine (hKb Ω m n B P F S t j w (hw.1.1 j) (hw.2.1 j) hCo hCi hm hn s hsms).2.trans ?_
    have hw2 : w j ^ 2 ≤ w j := by
      rw [sq]; exact mul_le_of_le_one_right (hw.1.1 j) (hw.2.1 j)
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_right (le_abs_self Kb) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hw2 (abs_nonneg _))) hsp.le
  obtain ⟨σ0, σle, q0, qle, hs1⟩ := pe_branch_data F w hw CS γ s hCS hγ hCo hCi hdim hsp
  have hLs : Summable (fun j => w j * Muon.DetEquiv.J (w j ^ 2 * branchQ w (specOutFM F) (specInFM F) s)) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hsw
    · exact mul_nonneg (hw.1.1 j) (lem_app_de_scalar_i.2.2.1 _ (mul_nonneg (sq_nonneg _) q0)).1.le
    · exact mul_le_of_le_one_right (hw.1.1 j)
        (lem_app_de_scalar_i.2.2.1 _ (mul_nonneg (sq_nonneg _) q0)).2
  have hZ := (hexact.add (hbs.hasSum.smul_const (Hmix w F S t s * F.C.Sin))).sub
    (hLs.hasSum.smul_const (Rbar (Fw w) (specOutFM F) (specInFM F) F.C s * EG F))
  have hEBeq : EB w F S t (specOutFM F) (specInFM F) s =
      Hmix w F S t s + bB w F S t s • (Hmix w F S t s * F.C.Sin) -
        Lw w (branchQ w (specOutFM F) (specInFM F) s) •
          (Rbar (Fw w) (specOutFM F) (specInFM F) F.C s * EG F) := by
    unfold EB YB
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hbB : bB w F S t s = ∑' j, bj w F S t j s := rfl
  have hLw : Lw w (branchQ w (specOutFM F) (specInFM F) s) =
      ∑' j, w j * Muon.DetEquiv.J (w j ^ 2 * branchQ w (specOutFM F) (specInFM F) s) := rfl
  have hEB' : EB w F S t (specOutFM F) (specInFM F) s =
      Hmix w F S t s + (∑' j, bj w F S t j s) • (Hmix w F S t s * F.C.Sin) -
        (∑' j, w j * Muon.DetEquiv.J (w j ^ 2 * branchQ w (specOutFM F) (specInFM F) s)) •
          (Rbar (Fw w) (specOutFM F) (specInFM F) F.C s * EG F) := by
    rw [hEBeq, hbB, hLw]
  have hrp0 : 0 ≤ rPrimeB F.A (qIbound CS γ I) :=
    Real.iSup_nonneg fun y => Real.iSup_nonneg fun _ => abs_nonneg _
  have hdl0 : 0 ≤ deltaB w F S t (specOutFM F) (specInFM F) I :=
    Real.iSup_nonneg fun y => Real.iSup_nonneg fun _ => tlb_opNorm_nonneg _
  have hΘ0 : 0 ≤ e + rPrimeB F.A (qIbound CS γ I) + opNorm F.A + opNorm F.A ^ 2 +
      deltaB w F S t (specOutFM F) (specInFM F) I + 1 / Real.sqrt (B : ℝ) := by
    have := tlb_opNorm_nonneg F.A
    positivity
  set Θ := e + rPrimeB F.A (qIbound CS γ I) + opNorm F.A + opNorm F.A ^ 2 +
      deltaB w F S t (specOutFM F) (specInFM F) I + 1 / Real.sqrt (B : ℝ) with hΘ
  have hsc : Summable (fun j => K * w j * Θ) := (hsw.mul_left K).mul_right Θ
  have hfro := tl_fro_hasSum _ _ (fun j => K * w j * Θ) hZ hsc (fun j => by
    exact hK Ω m n B P F S t j w hw hCo hCi hdim s hs e he (htar j s hs).1 (htar j s hs).2)
    (fun j => mul_nonneg (mul_nonneg hK0 (hw.1.1 j)) hΘ0)
  rw [hEB']
  refine hfro.trans ?_
  rw [tsum_mul_right, tsum_mul_left]
  have : K * ∑' j, w j ≤ K * 1 := mul_le_mul_of_nonneg_left hw.2.2 hK0
  rw [mul_one] at this
  exact mul_le_mul_of_nonneg_right this hΘ0

end PeEB2

section PeEB
open ProbabilityTheory

private lemma pe_branch_t {m n B : ℕ} (F : FrozenParams m n B) (w : ℕ → ℝ)
    (hw : WeightClass w) (CS γ s : ℝ) (hCS : 0 < CS) (hγ : 0 < γ)
    (hCo : opNorm F.C.Sout ≤ CS) (hCi : opNorm F.C.Sin ≤ CS)
    (hdim : ((max m n : ℕ) : ℝ) ≤ γ * B) (hs : 0 < s) :
    0 ≤ (branchSol (Fw w) (specOutFM F) (specInFM F) s).2.2.2 := by
  have hp := spectral_mem_classK F (⟨hCo, hCi, hdim⟩ : DriftBound F CS γ)
  have hspec := branchSol_spec (Fw_admissible hw.1) hCS hγ hp hs
  generalize branchSol (Fw w) (specOutFM F) (specInFM F) s = x at hspec ⊢
  obtain ⟨σ, σ', a, c⟩ := x
  exact hspec.2.2.2.1

end PeEB

section PeFinal
open ProbabilityTheory

private lemma pe_delta_tendsto (R : Muon.Setup.SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ) (I : Set ℝ)
    (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) :
    Tendsto (fun k => deltaB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) I)
      atTop (𝓝 0) := by
  obtain ⟨sm, hsm, hsmI⟩ : ∃ sm : ℝ, 0 < sm ∧ ∀ s ∈ I, sm ≤ s := by
    rcases I.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨sInf I, hIpos (hI.sInf_mem h), fun s hs => csInf_le hI.bddBelow hs⟩
  have hC : 0 < R.CSig := lt_of_lt_of_le one_pos R.hC
  have hγ := pcr_gamma_pos R
  have hgram := thm_app_de_gram R w hw P S (fun k => specOutFM (R.F k))
    (fun k => specInFM (R.F k)) (fun k => rfl) (fun k => rfl) t I hI hIpos
  refine squeeze_zero (fun k => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
    tlb_opNorm_nonneg _) (fun k => ?_) hgram
  have hsupnn : 0 ≤ ⨆ s ∈ I, (opNorm (expRes w (R.F k) (S k) t s -
        Rbar (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s) +
      opNorm (expResT w (R.F k) (S k) t s -
        Rtbar (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s)) :=
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
      add_nonneg (tlb_opNorm_nonneg _) (tlb_opNorm_nonneg _)
  refine pcr_biSup_le (fun s hs => ?_) hsupnn
  have hsp : 0 < s := hIpos hs
  have hsms : sm ≤ s := hsmI s hs
  have hdim : ((max (R.m k) (R.n k) : ℕ) : ℝ) ≤ R.γstar * (R.B k) := R.dims k
  obtain ⟨-, -, -, -, hs1⟩ := pe_branch_data (R.F k) w hw R.CSig R.γstar s hC hγ (R.normOut k)
    (R.normIn k) hdim hsp
  have hs2 := pe_branch_t (R.F k) w hw R.CSig R.γstar s hC hγ (R.normOut k) (R.normIn k) hdim hsp
  have hbound : ∀ s' ∈ I, (opNorm (expRes w (R.F k) (S k) t s' -
        Rbar (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s') +
      opNorm (expResT w (R.F k) (S k) t s' -
        Rtbar (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s')) ≤ 4 / sm := by
    intro s' hs'
    have hsp' : 0 < s' := hIpos hs'
    have hsm' : sm ≤ s' := hsmI s' hs'
    obtain ⟨-, -, -, -, hs1'⟩ := pe_branch_data (R.F k) w hw R.CSig R.γstar s' hC hγ
      (R.normOut k) (R.normIn k) hdim hsp'
    have hs2' := pe_branch_t (R.F k) w hw R.CSig R.γstar s' hC hγ (R.normOut k) (R.normIn k)
      hdim hsp'
    have hh : 1 / s' ≤ 1 / sm := one_div_le_one_div_of_le hsm hsm'
    have a1 := (pe_expRes_op w (R.F k) (S k) t hsp').trans hh
    have a2 := (pe_Rbar_op (R.F k).C (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) hsp' hs1').trans hh
    have a3 := (pe_expResT_op w (R.F k) (S k) t hsp').trans hh
    have a4 := (pe_Rtbar_op (R.F k).C (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) hsp' hs2').trans hh
    have e1 := pe_opNorm_sub_le (expRes w (R.F k) (S k) t s')
      (Rbar (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s')
    have e2 := pe_opNorm_sub_le (expResT w (R.F k) (S k) t s')
      (Rtbar (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s')
    have : 4 / sm = 1 / sm + 1 / sm + 1 / sm + 1 / sm := by ring
    rw [this]
    linarith
  refine le_trans (le_add_of_nonneg_right (tlb_opNorm_nonneg (expResT w (R.F k) (S k) t s -
    Rtbar (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s))) ?_
  exact pcr_le_biSup (f := fun s' => opNorm (expRes w (R.F k) (S k) t s' -
        Rbar (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s') +
      opNorm (expResT w (R.F k) (S k) t s' -
        Rtbar (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s')) hbound
    (by positivity) hs

end PeFinal

-- PE-HELPERS-END

-- PCR-HELPERS-END

/-- General-weight form of `prop:app-drift-response`, snapshot `cr-2026-10-23` (card rule (a),
§6.1). For a fixed compact `I ⊆ (0,∞)` and constants `C_Σ`, `γ⋆` there is `C_I` depending only on
`(I, C_Σ, γ⋆)` (quantified before the regime sequence, lesson (b)) such that for every
`SetupRegime` `R` with `R.CSig = C_Σ`, `R.γstar = γ⋆`, every weight sequence `w` in `WeightClass`
and every sample space sequence, there is a sequence `e_B^⋆ → 0` (the sequence of
`lem:app-drift-targets`, with its defining bounds for `α_{1,j}`, `α_{2,j}`) such that, with
`E_B(s) = 𝓗(s)𝖸_B(s) − L_w(q(−s)) R̄(−s) 𝔼G̃`:
the identity `𝓗𝖸_B = L_w R̄ 𝔼G̃ + E_B` holds on `I`; `sup_{s∈I}‖E_B(s)‖_F` is bounded by
`C_I(e_B^⋆ + r'_B + ‖Â‖ + ‖Â‖² + δ_B(I) + 1/√B)` and tends to `0`; and `b_B` satisfies the
explicit bound with `s_{w,2} = ∑ w_j²`. -/
theorem prop_app_drift_response_weights (CS γ : ℝ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) :
    ∃ CI : ℝ, ∀ R : Muon.Setup.SetupRegime, R.CSig = CS → R.γstar = γ →
      ∀ (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
        [∀ k, IsProbabilityMeasure (P k)]
        (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ) (w : ℕ → ℝ),
        WeightClass w →
        ∃ eStar : ℕ → ℝ, Tendsto eStar atTop (𝓝 0) ∧
          (∀ k : ℕ, ∀ j : ℕ, ∀ s ∈ I,
            eLpNorm (fun ω => delAlpha1 w (R.F k) (S k) t j s ω
                - alphaStar1 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
              2 (P k) ≤ ENNReal.ofReal (w j * eStar k) ∧
            eLpNorm (fun ω => delAlpha2 w (R.F k) (S k) t j s ω
                - alphaStar2 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
              2 (P k) ≤ ENNReal.ofReal (w j ^ 2 * eStar k)) ∧
          (∀ k : ℕ, ∀ s ∈ I,
            Hmix w (R.F k) (S k) t s * YB w (R.F k) (S k) t s =
              (Lw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)) •
                (Rbar (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s * EG (R.F k))
              + EB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) s) ∧
          (∀ k : ℕ, BddAbove ((fun s => fro (EB w (R.F k) (S k) t (specOutFM (R.F k))
              (specInFM (R.F k)) s)) '' I)) ∧
          Tendsto (fun k => ⨆ s ∈ I, fro (EB w (R.F k) (S k) t (specOutFM (R.F k))
              (specInFM (R.F k)) s)) atTop (𝓝 0) ∧
          (∀ k : ℕ, ⨆ s ∈ I, fro (EB w (R.F k) (S k) t (specOutFM (R.F k))
              (specInFM (R.F k)) s) ≤
            CI * (eStar k + rPrimeB (R.F k).A (qIbound CS γ I) + opNorm (R.F k).A
              + opNorm (R.F k).A ^ 2 + deltaB w (R.F k) (S k) t (specOutFM (R.F k))
                (specInFM (R.F k)) I + 1 / Real.sqrt ((R.B k : ℕ) : ℝ))) ∧
          (∀ k : ℕ, ∀ s ∈ I, 0 ≤ bB w (R.F k) (S k) t s) ∧
          (∀ k : ℕ, BddAbove ((fun s => |bB w (R.F k) (S k) t s
              - branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s
                * Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)|) '' I)) ∧
          (∀ k : ℕ, ⨆ s ∈ I, |bB w (R.F k) (S k) t s
              - branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s
                * Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)| ≤
            sumPow w 2 * (eStar k + (CS * γ / sInf I) * rBfresh (R.F k).A (qIbound CS γ I))) ∧
          Tendsto (fun k => ⨆ s ∈ I, |bB w (R.F k) (S k) t s
              - branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s
                * Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)|) atTop (𝓝 0) := by
  by_cases hpos : 0 < CS ∧ 0 < γ
  swap
  · refine ⟨0, fun R hCS hγ => ?_⟩
    exfalso
    exact hpos ⟨hCS ▸ lt_of_lt_of_le one_pos R.hC, hγ ▸ pcr_gamma_pos R⟩
  obtain ⟨hCSpos, hγpos⟩ := hpos
  obtain ⟨sm, hsm, hsmI⟩ : ∃ sm : ℝ, 0 < sm ∧ ∀ s ∈ I, sm ≤ s := by
    rcases I.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨sInf I, hIpos (hI.sInf_mem h), fun s hs => csInf_le hI.bddBelow hs⟩
  obtain ⟨K, hK0, hK⟩ := pe_EB_bound CS γ hCSpos hγpos I hI hIpos sm hsm hsmI
  refine ⟨K, fun R hCS hγ Ω _ P _ S t w hw => ?_⟩
  obtain ⟨e, he, htarget⟩ := lem_app_drift_targets_ii_weights R P S t I hI hIpos w hw
  have hdim : ∀ k, ((max (R.m k) (R.n k) : ℕ) : ℝ) ≤ γ * (R.B k : ℝ) := fun k => hγ ▸ R.dims k
  have hCo : ∀ k, opNorm (R.F k).C.Sout ≤ CS := fun k => hCS ▸ R.normOut k
  have hCi : ∀ k, opNorm (R.F k).C.Sin ≤ CS := fun k => hCS ▸ R.normIn k
  have ht : ∀ k j s, s ∈ I →
      eLpNorm (fun ω => delAlpha1 w (R.F k) (S k) t j s ω -
          alphaStar1 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
        2 (P k) ≤ ENNReal.ofReal (w j * |e k|) ∧
      eLpNorm (fun ω => delAlpha2 w (R.F k) (S k) t j s ω -
          alphaStar2 w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
        2 (P k) ≤ ENNReal.ofReal (w j ^ 2 * |e k|) := by
    intro k j s hs
    refine ⟨(htarget k j s hs).1.trans ?_, (htarget k j s hs).2.trans ?_⟩
    · exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (le_abs_self (e k)) (hw.1.1 j))
    · exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (le_abs_self (e k)) (sq_nonneg _))
  have hpt : ∀ k, ∀ s ∈ I,
      fro (EB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) s) ≤
        K * (|e k| + rPrimeB (R.F k).A (qIbound CS γ I) + opNorm (R.F k).A
          + opNorm (R.F k).A ^ 2 + deltaB w (R.F k) (S k) t (specOutFM (R.F k))
            (specInFM (R.F k)) I + 1 / Real.sqrt ((R.B k : ℕ) : ℝ)) := by
    intro k s hs
    exact hK (Ω k) (R.m k) (R.n k) (R.B k) (P k) (R.F k) (S k) t w hw (hCo k) (hCi k) (hdim k)
      |e k| (abs_nonneg _) (fun j s' hs' => ht k j s' hs') s hs
  have hg0 : ∀ k, 0 ≤ |e k| + rPrimeB (R.F k).A (qIbound CS γ I) + opNorm (R.F k).A
          + opNorm (R.F k).A ^ 2 + deltaB w (R.F k) (S k) t (specOutFM (R.F k))
            (specInFM (R.F k)) I + 1 / Real.sqrt ((R.B k : ℕ) : ℝ) := by
    intro k
    have h1 : 0 ≤ rPrimeB (R.F k).A (qIbound CS γ I) :=
      Real.iSup_nonneg fun y => Real.iSup_nonneg fun _ => abs_nonneg _
    have h2 : 0 ≤ deltaB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) I :=
      Real.iSup_nonneg fun y => Real.iSup_nonneg fun _ => tlb_opNorm_nonneg _
    have h3 := tlb_opNorm_nonneg (R.F k).A
    positivity
  obtain ⟨hbdd, hlim, hsup⟩ := pcr_uniform_bundle I
    (fun k s => fro (EB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) s))
    (fun k => |e k| + rPrimeB (R.F k).A (qIbound CS γ I) + opNorm (R.F k).A
          + opNorm (R.F k).A ^ 2 + deltaB w (R.F k) (S k) t (specOutFM (R.F k))
            (specInFM (R.F k)) I + 1 / Real.sqrt ((R.B k : ℕ) : ℝ)) K hK0
    (fun k s => tlb_fro_nonneg _) hg0 hpt
    (pcr_error_scale_tendsto CS γ I R P S t w (by simpa using he.abs)
      (pe_delta_tendsto R w hw P S t I hI hIpos))
  exact pcr_assemble CS γ I hI hIpos K R hCS hγ P S t w hw e he htarget hbdd hlim hsup

/-- `prop:app-drift-response`, snapshot `cr-2026-10-23`: the EMA record. Same conclusion as
`prop_app_drift_response_weights` with `w = emaW R.β` (`β` fixed by `R.hβ`). Source, verbatim
(`section.tex` l.706–723):
```latex
\begin{proposition}[Response equation]\label{prop:app-drift-response}
Under \cref{assum:app-setup-regime}, for $s\in I$ let
$b_B(s)\defeq\sum_{j\ge0}b_j\ge0$ with $b_j$ as in \cref{eqn:app-drift-Cj},
and let $\mathsf Y_B(s)\defeq\Id_{\Nin}+b_B(s)\Sigmain$. Then
\begin{equation}\label{eqn:app-drift-response}
\mathcal H(s)\,\mathsf Y_B(s)=\Lw\big(q(-s)\big)\,\Rbar(-s)\,\EE\Gt+E_B(s),
\end{equation}
where, with $r_B$ from \cref{lem:app-de-gaussian}, $r_B'$ from
\cref{lem:app-drift-gaussian}, $e_B^\star$ from \cref{lem:app-drift-targets}
and $\delta_B(I)\defeq\sup_{s\in I}\norm{\mathcal P(s)-\Rbar(-s)}$,
\begin{equation}\label{eqn:app-drift-response-error}
\sup_{s\in I}\norm{E_B(s)}_\F\le C_I\Big[e_B^\star+r_B'+\norm{\Ahat}+\norm{\Ahat}^2+\delta_B(I)+\frac{1}{\sqrt B}\Big]\longrightarrow0 ,
\end{equation}
and the coefficient $b_B$ satisfies
\begin{equation}\label{eqn:app-drift-bB}
\sup_{s\in I}\abs{b_B(s)-\sigma(-s)\Fw(q(-s))}\le\sw2\Big(e_B^\star+\frac{C_\Sigma\gamma_\star}{s_-}r_B\Big)\longrightarrow0 .
\end{equation}
\end{proposition}
```
-/
theorem prop_app_drift_response (CS γ : ℝ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) :
    ∃ CI : ℝ, ∀ R : Muon.Setup.SetupRegime, R.CSig = CS → R.γstar = γ →
      ∀ (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
        [∀ k, IsProbabilityMeasure (P k)]
        (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ),
        ∃ eStar : ℕ → ℝ, Tendsto eStar atTop (𝓝 0) ∧
          (∀ k : ℕ, ∀ j : ℕ, ∀ s ∈ I,
            eLpNorm (fun ω => delAlpha1 (emaW R.β) (R.F k) (S k) t j s ω
                - alphaStar1 (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
              2 (P k) ≤ ENNReal.ofReal (emaW R.β j * eStar k) ∧
            eLpNorm (fun ω => delAlpha2 (emaW R.β) (R.F k) (S k) t j s ω
                - alphaStar2 (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) j s ω)
              2 (P k) ≤ ENNReal.ofReal (emaW R.β j ^ 2 * eStar k)) ∧
          (∀ k : ℕ, ∀ s ∈ I,
            Hmix (emaW R.β) (R.F k) (S k) t s * YB (emaW R.β) (R.F k) (S k) t s =
              (Lw (emaW R.β) (branchQ (emaW R.β) (specOutFM (R.F k)) (specInFM (R.F k)) s)) •
                (Rbar (Fw (emaW R.β)) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s * EG (R.F k))
              + EB (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) s) ∧
          (∀ k : ℕ, BddAbove ((fun s => fro (EB (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k))
              (specInFM (R.F k)) s)) '' I)) ∧
          Tendsto (fun k => ⨆ s ∈ I, fro (EB (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k))
              (specInFM (R.F k)) s)) atTop (𝓝 0) ∧
          (∀ k : ℕ, ⨆ s ∈ I, fro (EB (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k))
              (specInFM (R.F k)) s) ≤
            CI * (eStar k + rPrimeB (R.F k).A (qIbound CS γ I) + opNorm (R.F k).A
              + opNorm (R.F k).A ^ 2 + deltaB (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k))
                (specInFM (R.F k)) I + 1 / Real.sqrt ((R.B k : ℕ) : ℝ))) ∧
          (∀ k : ℕ, ∀ s ∈ I, 0 ≤ bB (emaW R.β) (R.F k) (S k) t s) ∧
          (∀ k : ℕ, BddAbove ((fun s => |bB (emaW R.β) (R.F k) (S k) t s
              - branchSigma (emaW R.β) (specOutFM (R.F k)) (specInFM (R.F k)) s
                * Fw (emaW R.β) (branchQ (emaW R.β) (specOutFM (R.F k)) (specInFM (R.F k)) s)|) '' I)) ∧
          (∀ k : ℕ, ⨆ s ∈ I, |bB (emaW R.β) (R.F k) (S k) t s
              - branchSigma (emaW R.β) (specOutFM (R.F k)) (specInFM (R.F k)) s
                * Fw (emaW R.β) (branchQ (emaW R.β) (specOutFM (R.F k)) (specInFM (R.F k)) s)| ≤
            sumPow (emaW R.β) 2 * (eStar k + (CS * γ / sInf I) * rBfresh (R.F k).A (qIbound CS γ I))) ∧
          Tendsto (fun k => ⨆ s ∈ I, |bB (emaW R.β) (R.F k) (S k) t s
              - branchSigma (emaW R.β) (specOutFM (R.F k)) (specInFM (R.F k)) s
                * Fw (emaW R.β) (branchQ (emaW R.β) (specOutFM (R.F k)) (specInFM (R.F k)) s)|)
            atTop (𝓝 0) := by
  obtain ⟨CI, hCI⟩ := prop_app_drift_response_weights CS γ I hI hIpos
  refine ⟨CI, ?_⟩
  intro R hCS hγ Ω _ P _ S t
  have hβ := (R.F 0).hβ
  rw [R.hβ 0] at hβ
  exact hCI R hCS hγ Ω P S t (emaW R.β) (emaW_weightClass R.β hβ)

-- PCD-HELPERS-BEGIN
section PcdHelpers

private lemma pcd_fro_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma pcd_opNorm_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ opNorm A := by
  unfold opNorm; exact norm_nonneg _

private lemma pcd_fro_sq {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

open scoped Matrix.Norms.L2Operator in
private lemma pcd_fro_mul_le_left {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
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
    rw [pcd_fro_sq, mul_pow, pcd_fro_sq, Finset.sum_comm]
    calc ∑ j, ∑ i, (M * N) i j ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, N k j ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, N k j ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (pcd_fro_nonneg _) (mul_nonneg (pcd_opNorm_nonneg M)
    (pcd_fro_nonneg N)) two_ne_zero).mp hfro

open scoped Matrix.Norms.L2Operator in
private lemma pcd_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma pcd_fro_transpose {k l : ℕ} (A : Mat k l) : fro Aᵀ = fro A := by
  unfold fro
  congr 1
  simp only [Matrix.transpose_apply]
  exact Finset.sum_comm

private lemma pcd_fro_mul_le_right {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ fro M * opNorm N := by
  have h := pcd_fro_mul_le_left Nᵀ Mᵀ
  rw [← Matrix.transpose_mul, pcd_fro_transpose, pcd_opNorm_transpose, pcd_fro_transpose] at h
  linarith [mul_comm (opNorm N) (fro M)]

open scoped Matrix.Norms.Frobenius in
private lemma pcd_fro_add {k l : ℕ} (A B' : Mat k l) : fro (A + B') ≤ fro A + fro B' := by
  rw [fro_eq_norm, fro_eq_norm, fro_eq_norm]; exact norm_add_le _ _

open scoped Matrix.Norms.Frobenius in
private lemma pcd_fro_smul {k l : ℕ} (c : ℝ) (A : Mat k l) : fro (c • A) = |c| * fro A := by
  rw [fro_eq_norm, fro_eq_norm, norm_smul, Real.norm_eq_abs]

/-- `‖D‖_F ≤ ‖D (1 + b S)‖_F` for PSD `S`, `b ≥ 0` (replaces `‖Y_B⁻¹‖ ≤ 1`). -/
private lemma pcd_fro_le_mul_Y {p n : ℕ} (D : Mat p n) (S : Mat n n) (hS : S.PosSemidef)
    {b : ℝ} (hb : 0 ≤ b) : fro D ≤ fro (D * ((1 : Mat n n) + b • S)) := by
  have hsym : ∀ j k, S j k = S k j := fun j k => by
    have h := hS.isHermitian.eq
    have := congrFun (congrFun h k) j
    simpa using this
  refine le_of_pow_le_pow_left₀ two_ne_zero (pcd_fro_nonneg _) ?_
  rw [pcd_fro_sq, pcd_fro_sq]
  refine Finset.sum_le_sum fun i _ => ?_
  set v : Vec n := fun j => D i j with hv
  have e : ∀ j, (D * ((1 : Mat n n) + b • S)) i j = v j + b * (S *ᵥ v) j := by
    intro j
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul]
    congr 2
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hv]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsym j k]; ring
  simp only [e]
  have hYnn : 0 ≤ ∑ j, v j * (S *ᵥ v) j := by
    have := hS.dotProduct_mulVec_nonneg v
    simpa [dotProduct, star_trivial] using this
  have hz : 0 ≤ ∑ j, (S *ᵥ v) j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have e2 : ∑ j, (v j + b * (S *ᵥ v) j) ^ 2 = ∑ j, v j ^ 2 + 2 * b * ∑ j, v j * (S *ᵥ v) j
      + b ^ 2 * ∑ j, (S *ᵥ v) j ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e2]
  nlinarith [mul_nonneg hb hYnn, mul_nonneg (sq_nonneg b) hz]

/-- `(s 1 + s a S)⁻¹ (1 + a S) = s⁻¹ 1` for PSD `S`, `a ≥ 0`, `s > 0`. -/
private lemma pcd_inv_mul {k : ℕ} (S : Mat k k) (hS : S.PosSemidef) {a s : ℝ} (ha : 0 ≤ a)
    (hs : 0 < s) :
    (s • (1 : Mat k k) + (s * a) • S)⁻¹ * ((1 : Mat k k) + a • S) = s⁻¹ • (1 : Mat k k) := by
  have hM : s • (1 : Mat k k) + (s * a) • S = s • ((1 : Mat k k) + a • S) := by
    rw [smul_add, smul_smul]
  have hG : IsUnit (s • (1 : Mat k k) + (s * a) • S).det := by
    have h2 : (s • (1 : Mat k k)).PosDef := Matrix.PosDef.one.smul hs
    have h1 : ((s * a) • S).PosSemidef := hS.smul (mul_nonneg hs.le ha)
    have h3 := Matrix.PosDef.add_posSemidef h2 h1
    exact isUnit_iff_ne_zero.mpr h3.det_pos.ne'
  have h := Matrix.nonsing_inv_mul _ hG
  rw [hM] at h ⊢
  rw [Matrix.mul_smul] at h
  have h' : s⁻¹ • (s • ((s • ((1 : Mat k k) + a • S))⁻¹ * ((1 : Mat k k) + a • S))) = s⁻¹ • 1 := by
    rw [h]
  rwa [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] at h'

end PcdHelpers

-- PCD-HELPERS-END

section PcdMain

private lemma pcd_branch_c (w : ℕ → ℝ) (ν ν' : FiniteMeasure ℝ) (s : ℝ)
    (h : IsBranchSol (Fw w) ν ν' s (branchSol (Fw w) ν ν' s)) :
    (branchSol (Fw w) ν ν' s).2.2.2 =
      s * (branchSol (Fw w) ν ν' s).1 * Fw w (branchQ w ν ν' s) := by
  unfold branchQ
  generalize branchSol (Fw w) ν ν' s = x at h ⊢
  obtain ⟨σ, σ', a, c⟩ := x
  exact h.2.2.2.2.2.2.2

/-- `T(s) · (1 + σ(-s) F_w(q(-s)) Σ_in) = L_w(q(-s)) R̄(-s) 𝔼G̃`. -/
private lemma pcd_TY (R : Muon.Setup.SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w) (k : ℕ)
    {s : ℝ} (hs : 0 < s) :
    Tcand w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) s *
      ((1 : Mat (R.n k) (R.n k)) + (branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s *
        Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)) • (R.F k).C.Sin) =
    (Lw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)) •
      (Rbar (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s * EG (R.F k)) := by
  have hC : 0 < R.CSig := lt_of_lt_of_le one_pos R.hC
  have hγ := pcr_gamma_pos R
  have hp := spectral_mem_classK (R.F k) (pcr_drift R k)
  have hspec := branchSol_spec (Fw_admissible hw.1) hC hγ hp hs
  have hc := pcd_branch_c w _ _ s hspec
  obtain ⟨hσ0, -, hq0, -, -⟩ := pcr_branch R w hw k hs
  have hF0 : 0 ≤ Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s) := by
    exact ((Fw_admissible hw.1).pos _ hq0).le
  have hRt : Rtbar (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s *
      ((1 : Mat (R.n k) (R.n k)) + (branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s *
        Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)) • (R.F k).C.Sin)
      = s⁻¹ • (1 : Mat (R.n k) (R.n k)) := by
    unfold Rtbar
    rw [hc, mul_assoc]
    exact pcd_inv_mul _ (R.F k).C.psdIn (mul_nonneg hσ0 hF0) hs
  unfold Tcand
  rw [Matrix.smul_mul, Matrix.mul_assoc, hRt, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  have : s * Lw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s) * s⁻¹ =
      Lw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s) := by
    field_simp
  rw [this]

end PcdMain


section PcdMain2

private lemma pcd_point (R : Muon.Setup.SetupRegime) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (k : ℕ)
    (S : FrozenSamples P (R.m k) (R.n k) (R.B k)) (t : ℤ) (w : ℕ → ℝ) (hw : WeightClass w)
    {s sm : ℝ} (hs : 0 < s) (hsm : 0 < sm) (hle : sm ≤ s)
    (hid : Hmix w (R.F k) S t s * YB w (R.F k) S t s =
      (Lw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)) •
        (Rbar (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s * EG (R.F k))
      + EB w (R.F k) S t (specOutFM (R.F k)) (specInFM (R.F k)) s)
    (hb0 : 0 ≤ bB w (R.F k) S t s) :
    fro (Hmix w (R.F k) S t s - Tcand w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) s) ≤
      fro (EB w (R.F k) S t (specOutFM (R.F k)) (specInFM (R.F k)) s) +
      (R.CSig ^ 2 / sm) * |bB w (R.F k) S t s
        - branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s *
          Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)| := by
  have hC : 0 < R.CSig := lt_of_lt_of_le one_pos R.hC
  have hγ := pcr_gamma_pos R
  set H := Hmix w (R.F k) S t s with hH
  set T := Tcand w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) s with hT
  set E := EB w (R.F k) S t (specOutFM (R.F k)) (specInFM (R.F k)) s with hE
  set b := bB w (R.F k) S t s with hb
  set a := branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s *
    Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s) with ha
  set Sg := (R.F k).C.Sin with hSg
  have hTY := pcd_TY R w hw k hs
  rw [← hT, ← ha] at hTY
  have hD : (H - T) * ((1 : Mat (R.n k) (R.n k)) + b • Sg) = E + (a - b) • (T * Sg) := by
    have h1 : H * ((1 : Mat (R.n k) (R.n k)) + b • Sg) =
        (Lw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)) •
        (Rbar (Fw w) (specOutFM (R.F k)) (specInFM (R.F k)) (R.F k).C s * EG (R.F k)) + E := hid
    rw [Matrix.sub_mul, h1, ← hTY]
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, sub_smul]
    abel
  have hpsd : Sg.PosSemidef := (R.F k).C.psdIn
  have h1 := pcd_fro_le_mul_Y (H - T) Sg hpsd hb0
  rw [hD] at h1
  have hTf : fro T ≤ R.CSig / s :=
    thm_app_drift_mixed_ii_T hC hγ hw (R.F k) (pcr_drift R k) hs
  have hTS : fro (T * Sg) ≤ R.CSig / s * R.CSig :=
    (pcd_fro_mul_le_right T Sg).trans
      (mul_le_mul hTf (R.normIn k) (pcd_opNorm_nonneg _) (div_nonneg hC.le hs.le))
  have h2 : fro (E + (a - b) • (T * Sg)) ≤ fro E + |a - b| * (R.CSig / s * R.CSig) := by
    refine (pcd_fro_add _ _).trans ?_
    rw [pcd_fro_smul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hTS (abs_nonneg _))
  have h3 : R.CSig / s * R.CSig ≤ R.CSig ^ 2 / sm := by
    rw [div_mul_eq_mul_div, ← sq]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hsm hle
  rw [abs_sub_comm] at h2
  calc fro (H - T) ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left h3 (abs_nonneg _))
    _ = _ := by rw [mul_comm]

end PcdMain2
-- MOVED-TARGET-BEGIN
/-- General-weight form of `thm:app-drift-mixed`(i), snapshot `cr-2026-10-23` (card rule (a)).
For `WeightClass w` under `assum:app-setup-regime`, with the spectral measures `specOutFM`,
`specInFM`: the family `s ↦ ‖𝓗(s) − T(s)‖_F` is bounded on `I` (`BddAbove`) and its supremum over
`I` tends to `0`. The EMA record is the instance at `emaW R.β`. -/
theorem thm_app_drift_mixed_i_weights (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) (w : ℕ → ℝ) (hw : WeightClass w) :
    (∀ k, BddAbove ((fun s => fro (Hmix w (R.F k) (S k) t s
        - Tcand w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) s)) '' I)) ∧
    Tendsto (fun k => ⨆ s ∈ I, fro (Hmix w (R.F k) (S k) t s
        - Tcand w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) s)) atTop (𝓝 0) := by
  obtain ⟨CI, hCI⟩ := prop_app_drift_response_weights R.CSig R.γstar I hI hIpos
  obtain ⟨eStar, -, -, hid, hEb, hElim, -, hb0, hbBdd, -, hblim⟩ := hCI R rfl rfl Ω P S t w hw
  set f : ℕ → ℝ → ℝ := fun k s => fro (Hmix w (R.F k) (S k) t s
        - Tcand w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) s) with hf
  set Ef : ℕ → ℝ → ℝ := fun k s => fro (EB w (R.F k) (S k) t (specOutFM (R.F k))
        (specInFM (R.F k)) s) with hEf
  set Bf : ℕ → ℝ → ℝ := fun k s => |bB w (R.F k) (S k) t s
              - branchSigma w (specOutFM (R.F k)) (specInFM (R.F k)) s
                * Fw w (branchQ w (specOutFM (R.F k)) (specInFM (R.F k)) s)| with hBf
  set K : ℝ := R.CSig ^ 2 / sInf I with hK
  have hK0 : 0 ≤ K := by
    by_cases hne : I.Nonempty
    · have hpos : 0 < sInf I := hIpos (hI.sInf_mem hne)
      exact div_nonneg (sq_nonneg _) hpos.le
    · have h0 := Set.not_nonempty_iff_eq_empty.mp hne
      simp [hK, h0]
  have hle : ∀ (g : ℝ → ℝ) (hg : BddAbove (g '' I)) x, x ∈ I → g x ≤ ⨆ y ∈ I, g y := by
    intro g hg x hx
    obtain ⟨c, hc⟩ := hg
    exact pcr_le_biSup (c := max c 0) (fun y hy => (hc ⟨y, hy, rfl⟩).trans (le_max_left _ _))
      (le_max_right _ _) hx
  have hpt : ∀ k, ∀ s ∈ I, f k s ≤ Ef k s + K * Bf k s := by
    intro k s hs
    have hsp : 0 < s := hIpos hs
    have hne : I.Nonempty := ⟨s, hs⟩
    have hmem := hI.sInf_mem hne
    exact pcd_point R k (S k) t w hw hsp (hIpos hmem) (csInf_le hI.bddBelow hs) (hid k s hs)
      (hb0 k s hs)
  have hEnn : ∀ k, 0 ≤ ⨆ s ∈ I, Ef k s := fun k => pcr_biSup_nonneg (fun _ => pcd_fro_nonneg _)
  have hBnn : ∀ k, 0 ≤ ⨆ s ∈ I, Bf k s := fun k => pcr_biSup_nonneg (fun _ => abs_nonneg _)
  have hbound : ∀ k, ∀ s ∈ I, f k s ≤ (⨆ s ∈ I, Ef k s) + K * ⨆ s ∈ I, Bf k s := by
    intro k s hs
    refine (hpt k s hs).trans (add_le_add (hle (Ef k) (hEb k) s hs)
      (mul_le_mul_of_nonneg_left (hle (Bf k) (hbBdd k) s hs) hK0))
  have hc0 : ∀ k, 0 ≤ (⨆ s ∈ I, Ef k s) + K * ⨆ s ∈ I, Bf k s := fun k =>
    add_nonneg (hEnn k) (mul_nonneg hK0 (hBnn k))
  refine ⟨fun k => pcr_bddAbove (hbound k), ?_⟩
  refine squeeze_zero (fun k => pcr_biSup_nonneg (fun _ => pcd_fro_nonneg _))
    (fun k => pcr_biSup_le (hbound k) (hc0 k)) ?_
  simpa using hElim.add (hblim.const_mul K)

/-- Part (i) of `thm:app-drift-mixed`, snapshot `cr-2026-10-23`: `sup_{s∈I} ‖𝓗(s) − T(s)‖_F → 0`
under `assum:app-setup-regime` with the EMA weights `emaW β` (`β` fixed by `R.hβ`), together with
the boundedness of the family over `I`. Instance of `thm_app_drift_mixed_i_weights`.
Source, verbatim (`section.tex` l.99–115):
```latex
\begin{theorem}[Mixed resolvent closure and tail bound]\label{thm:app-drift-mixed}
\begin{enumerate}[label=(\roman*)]
\item Under \cref{assum:app-setup-regime}, for every compact $I\subset(0,\infty)$,
\begin{equation}\label{eqn:app-drift-mixed}
\sup_{s\in I}\norm{\mathcal H(s)-T(s)}_\F\longrightarrow0 .
\end{equation}
\item In the frozen-state model under \cref{assum:data-target}, with
$\max(\Nout,\Nin)\le\gamma_\star B$, $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$,
$\norm{\Ahat}_\F=1$ and weights satisfying \cref{eqn:app-drift-weights}, but
without any condition on $\norm{\Ahat}$ and for every finite dimension,
there is $C$ depending only on $(C_\Sigma,\gamma_\star)$ such that
\begin{equation}\label{eqn:app-drift-tail}
\norm{\mathcal H(s)}_\F\le\frac{C}{s}\quad(s\ge1),\qquad
\norm{T(s)}_\F\le\frac{C_\Sigma}{s}\quad(s>0).
\end{equation}
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_drift_mixed_i (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) :
    (∀ k, BddAbove ((fun s => fro (Hmix (emaW R.β) (R.F k) (S k) t s
        - Tcand (emaW R.β) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) s)) '' I)) ∧
    Tendsto (fun k => ⨆ s ∈ I, fro (Hmix (emaW R.β) (R.F k) (S k) t s
        - Tcand (emaW R.β) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) s)) atTop (𝓝 0) :=
  thm_app_drift_mixed_i_weights R P S t I hI hIpos (emaW R.β)
    (by have h0 := (R.F 0).hβ; rw [R.hβ 0] at h0; exact emaW_weightClass R.β h0)

end Muon.Drift

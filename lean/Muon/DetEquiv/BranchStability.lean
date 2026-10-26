import Muon.DetEquiv.Branch

/-!
# Appendix B: compactness of the spectral class and stability of the branch (task L-B.3)

Snapshot `cr-2026-10-23`. Source: `sections/02-deterministic-equivalents/section.tex`,
`lem:app-de-compact` (l.205–210) and `thm:app-de-branch` parts (ii) and (iii) (l.174–195).
Part (i) of the theorem and the box are `Muon.DetEquiv.thm_app_de_branch_i` (`Branch.lean`);
part (iv) is in `BranchSmooth.lean` (task L-B.4).

Representation choices (CARD §2, §3, §6.3 and the CORRECTIONS entry for `thm:app-de-branch`(ii)):

* `𝒦` is `classK Cs γ` of `Branch.lean`. Its factor `𝒦₁` (one measure of mass at most `γ⋆` on
  `[0,C_Σ]`) is `classK1`, with `classK_eq_prod` the factorization.
* Sequences are replaced by topology. `FiniteMeasure ℝ` carries the weak topology; on `𝒦₁` it agrees
  with the topology of weak convergence against `C([0,C_Σ])` (Tietze extension, equal total masses),
  but it is not metrizable in Mathlib. Compactness is `IsCompact`; the sequential claims of
  `lem:app-de-compact` become continuity on the product; convergence arguments downstream use
  filters and cluster points.
* `thm:app-de-branch`(ii) is stated as joint continuity on `(0,∞)×𝒦` plus a modulus in `s`,
  uniform over `𝒦` (no uniform structure on `𝒦` exists; CARD §6.3).
* `thm:app-de-branch`(iii) uses an arbitrary box `[0,𝔟]⁴` in place of the paper's box
  `[0,γ⋆C_Σ/s₋]²×[0,γ⋆C_Σ·∑w²]²`, and an abstract `F` with `AdmissibleWeightFn F` (ruling L2).
  Here `δ` depends on `(ε, I, C_Σ, γ⋆, 𝔟, F)` and not on `(ν,ν̃)`, `s` or the tuple.
  The approximate-root tuple is `(u, v, a, c) = (σ', σ̃', a', c')`, with `q' = s u v`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace Muon.DetEquiv

/-! ## The factor `𝒦₁` and the compactness of `𝒦` -/

/-- The factor `𝒦₁` of `eqn:app-de-class`: a finite positive Borel measure `μ` on `[0,C_Σ]` with
`μ([0,C_Σ]) ≤ γ⋆`, encoded as in `classK` (`Branch.lean`): support condition `μ([0,C_Σ]ᶜ) = 0`,
mass condition `μ([0,C_Σ]) ≤ γ⋆` in `ℝ≥0∞`. -/
def classK1 (Cs γ : ℝ) : Set (FiniteMeasure ℝ) :=
  {μ | (μ : Measure ℝ) (Icc 0 Cs) ≤ ENNReal.ofReal γ ∧ (μ : Measure ℝ) (Icc 0 Cs)ᶜ = 0}

/-- `𝒦 = 𝒦₁ × 𝒦₁` (factorization of `eqn:app-de-class`, which is a product of the two
independent conditions on `ν` and `ν̃`). -/
theorem classK_eq_prod (Cs γ : ℝ) : classK Cs γ = classK1 Cs γ ×ˢ classK1 Cs γ := by
  ext ⟨μ, ν⟩
  simp only [classK, classK1, Set.mem_prod, Set.mem_ofPred_eq]
  tauto

/-- `lem:app-de-compact`, the compactness claim (snapshot `cr-2026-10-23`). LaTeX
(`sections/02-deterministic-equivalents/section.tex` l.205–210):
```
\begin{lemma}[Compactness of the spectral class]\label{lem:app-de-compact}
Every sequence in $\mathcal K$ has a subsequence that converges, weakly against
$C([0,C_\Sigma])$ in each coordinate, to an element of $\mathcal K$. If
$\nu_n\to\nu$ weakly in this sense, $s_n\to s>0$ and $a_n\to a\ge0$, then
$\int\frac{x}{s_n+a_nx}\,\nu_n(dx)\to\int\frac{x}{s+ax}\,\nu(dx)$.
\end{lemma}
```
Encoding: the sequential statement "every sequence in `𝒦` has a subsequence converging to an
element of `𝒦`" is replaced by `IsCompact (classK Cs γ)` (Mathlib's compactness of
`{μ | μ.mass ≤ C ∧ μ Kᶜ = 0}` on a compact `K` gives it, with `K = [0,C_Σ]`). -/
theorem lem_app_de_compact_i {Cs γ : ℝ} (hC : 0 < Cs) (hγ : 0 < γ) :
    IsCompact (classK Cs γ) := by
  have key : ∀ μ : FiniteMeasure ℝ, (μ : Measure ℝ) (Icc 0 Cs)ᶜ = 0 →
      ((μ.mass : ℝ≥0) : ℝ≥0∞) = (μ : Measure ℝ) (Icc 0 Cs) := by
    intro μ h2
    have hu : (μ : Measure ℝ) univ = (μ : Measure ℝ) (Icc 0 Cs) := by
      rw [← measure_add_measure_compl (μ := (μ : Measure ℝ)) measurableSet_Icc, h2, add_zero]
    rw [FiniteMeasure.ennreal_mass, hu]
  have hset : classK1 Cs γ =
      {μ : FiniteMeasure ℝ | μ.mass ≤ Real.toNNReal γ ∧ (μ : Measure ℝ) (Icc 0 Cs)ᶜ = 0} := by
    ext μ
    simp only [classK1, mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      exact ENNReal.coe_le_coe.mp ((key μ h2).le.trans h1)
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [← key μ h2]
      exact ENNReal.coe_le_coe.mpr h1
  rw [classK_eq_prod, hset]
  have hc0 := isCompact_setOfPred_finiteMeasure_le_of_isCompact (E := ℝ) (Real.toNNReal γ)
    (isCompact_Icc (a := 0) (b := Cs))
  have hc : IsCompact {μ : FiniteMeasure ℝ |
      μ.mass ≤ Real.toNNReal γ ∧ (μ : Measure ℝ) (Icc 0 Cs)ᶜ = 0} := by
    convert hc0 using 3 with μ
    simp only [← ENNReal.coe_eq_zero, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact hc.prod hc

/-! ### Helpers for the joint continuity (`lem_app_de_compact_ii`) -/

/-- Clamp of `x` to `[0, Cs]`. -/
private def clampC (Cs x : ℝ) : ℝ := max 0 (min x Cs)

private lemma continuous_clampC (Cs : ℝ) : Continuous (clampC Cs) := by
  unfold clampC; fun_prop

private lemma clampC_mem {Cs : ℝ} (hC : 0 ≤ Cs) (x : ℝ) : clampC Cs x ∈ Icc 0 Cs :=
  ⟨le_max_left _ _, max_le hC (min_le_right _ _)⟩

private lemma clampC_of_mem {Cs x : ℝ} (hx : x ∈ Icc 0 Cs) : clampC Cs x = x := by
  unfold clampC
  rw [min_eq_left hx.2, max_eq_right hx.1]

/-- Test integrand: `x/(s+ax)` on `[0,Cs]`, extended as a continuous bounded function of `x`. -/
private def gK (Cs s a x : ℝ) : ℝ := clampC Cs x / (s + a * clampC Cs x)

private lemma gK_eq_of_mem {Cs x : ℝ} (s a : ℝ) (hx : x ∈ Icc 0 Cs) :
    gK Cs s a x = x / (s + a * x) := by
  unfold gK
  rw [clampC_of_mem hx]

private lemma gK_continuous {Cs s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hC : 0 ≤ Cs) :
    Continuous (gK Cs s a) := by
  unfold gK
  refine Continuous.div (continuous_clampC Cs) (continuous_const.add
    (continuous_const.mul (continuous_clampC Cs))) ?_
  intro x
  have h1 := mul_nonneg ha (clampC_mem hC x).1
  exact (by linarith : (0:ℝ) < s + a * clampC Cs x).ne'

private lemma gK_abs_le {Cs s a x : ℝ} (hC : 0 ≤ Cs) (hs : 0 < s) (ha : 0 ≤ a) :
    ‖gK Cs s a x‖ ≤ Cs / s := by
  rw [Real.norm_eq_abs]
  unfold gK
  obtain ⟨h0, hCs⟩ := clampC_mem hC x
  have h1 := mul_nonneg ha h0
  rw [abs_of_nonneg (div_nonneg h0 (by linarith))]
  rw [div_le_div_iff₀ (by linarith) hs]
  nlinarith

/-- Modulus of the difference of two test integrands. -/
private def modC (Cs σ s a s0 a0 : ℝ) : ℝ := Cs * (|s - s0| + Cs * |a - a0|) / (σ * σ)

private lemma gK_sub_le {Cs σ s a s' a' x : ℝ} (hC : 0 ≤ Cs) (hσ : 0 < σ)
    (hs : σ ≤ s) (hs' : σ ≤ s') (ha : 0 ≤ a) (ha' : 0 ≤ a') :
    ‖gK Cs s a x - gK Cs s' a' x‖ ≤ modC Cs σ s a s' a' := by
  rw [Real.norm_eq_abs]
  unfold gK modC
  obtain ⟨h0, hCs⟩ := clampC_mem hC x
  set c := clampC Cs x with hcdef
  have hD1 : σ ≤ s + a * c := by nlinarith [mul_nonneg ha h0]
  have hD2 : σ ≤ s' + a' * c := by nlinarith [mul_nonneg ha' h0]
  have hp1 : 0 < s + a * c := by linarith
  have hp2 : 0 < s' + a' * c := by linarith
  rw [div_sub_div _ _ hp1.ne' hp2.ne', abs_div, abs_of_pos (mul_pos hp1 hp2)]
  have hnum : |c * (s' + a' * c) - (s + a * c) * c| ≤ Cs * (|s - s'| + Cs * |a - a'|) := by
    have e : c * (s' + a' * c) - (s + a * c) * c = c * ((s' - s) + (a' - a) * c) := by ring
    rw [e, abs_mul, abs_of_nonneg h0]
    have h1 : |(s' - s) + (a' - a) * c| ≤ |s - s'| + Cs * |a - a'| := by
      calc |(s' - s) + (a' - a) * c| ≤ |s' - s| + |(a' - a) * c| := abs_add_le _ _
        _ = |s - s'| + |a - a'| * c := by
          rw [abs_mul, abs_of_nonneg h0, abs_sub_comm s' s, abs_sub_comm a' a]
        _ ≤ |s - s'| + Cs * |a - a'| := by nlinarith [abs_nonneg (a - a')]
    exact mul_le_mul hCs h1 (abs_nonneg _) hC
  have hB : 0 ≤ Cs * (|s - s'| + Cs * |a - a'|) :=
    mul_nonneg hC (add_nonneg (abs_nonneg _) (mul_nonneg hC (abs_nonneg _)))
  have hpp : σ * σ ≤ (s + a * c) * (s' + a' * c) := by nlinarith
  calc |c * (s' + a' * c) - (s + a * c) * c| / ((s + a * c) * (s' + a' * c))
      ≤ Cs * (|s - s'| + Cs * |a - a'|) / ((s + a * c) * (s' + a' * c)) :=
        div_le_div_of_nonneg_right hnum (mul_pos hp1 hp2).le
    _ ≤ Cs * (|s - s'| + Cs * |a - a'|) / (σ * σ) :=
        div_le_div_of_nonneg_left hB (mul_pos hσ hσ) hpp

/-- The modulus tends to zero as `(s,a) → (s0,a0)`. -/
private lemma modC_continuous (Cs σ s0 a0 : ℝ) :
    Continuous (fun p : ℝ × ℝ × FiniteMeasure ℝ => modC Cs σ p.1 p.2.1 s0 a0) := by
  unfold modC
  fun_prop

/-- Integral of the test integrand against a finite measure of mass `≤ γ` supported on `[0,Cs]`. -/
private def Gfun (Cs : ℝ) (p : ℝ × ℝ × FiniteMeasure ℝ) : ℝ :=
  ∫ x, gK Cs p.1 p.2.1 x ∂(p.2.2 : Measure ℝ)

private lemma univ_real_le {Cs γ : ℝ} (hγ : 0 < γ) {μ : FiniteMeasure ℝ}
    (hμ : μ ∈ classK1 Cs γ) : (μ : Measure ℝ).real univ ≤ γ := by
  rcases hμ with ⟨h1, h2⟩
  have hu : (μ : Measure ℝ) univ = (μ : Measure ℝ) (Icc 0 Cs) := by
    rw [← measure_add_measure_compl (μ := (μ : Measure ℝ)) measurableSet_Icc, h2, add_zero]
  rw [measureReal_def, hu]
  exact ENNReal.toReal_le_of_le_ofReal hγ.le h1

private lemma ae_mem_of_classK1 {Cs γ : ℝ} {μ : FiniteMeasure ℝ}
    (hμ : μ ∈ classK1 Cs γ) : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc 0 Cs := by
  rcases hμ with ⟨_, h2⟩
  exact ae_iff.2 h2

/-- `lem:app-de-compact`, the continuity claim (snapshot `cr-2026-10-23`). LaTeX
(`sections/02-deterministic-equivalents/section.tex` l.205–210):
```
\begin{lemma}[Compactness of the spectral class]\label{lem:app-de-compact}
Every sequence in $\mathcal K$ has a subsequence that converges, weakly against
$C([0,C_\Sigma])$ in each coordinate, to an element of $\mathcal K$. If
$\nu_n\to\nu$ weakly in this sense, $s_n\to s>0$ and $a_n\to a\ge0$, then
$\int\frac{x}{s_n+a_nx}\,\nu_n(dx)\to\int\frac{x}{s+ax}\,\nu(dx)$.
\end{lemma}
```
Encoding: the sequential claim "if `ν_n → ν` weakly, `s_n → s > 0` and `a_n → a ≥ 0` then the
integrals converge" is the joint continuity of `(s, a, ν) ↦ ∫ x/(s + a x) dν` on
`(0,∞) × [0,∞) × 𝒦₁` (the product topology; `FiniteMeasure ℝ` is not metrizable here). -/
theorem lem_app_de_compact_ii {Cs γ : ℝ} (hC : 0 < Cs) (hγ : 0 < γ) :
    ContinuousOn
      (fun p : ℝ × ℝ × FiniteMeasure ℝ => ∫ x, x / (p.1 + p.2.1 * x) ∂(p.2.2 : Measure ℝ))
      (Ioi 0 ×ˢ Ici 0 ×ˢ classK1 Cs γ) := by
  set S : Set (ℝ × ℝ × FiniteMeasure ℝ) := Ioi (0:ℝ) ×ˢ Ici (0:ℝ) ×ˢ classK1 Cs γ with hSdef
  have hC0 : 0 ≤ Cs := hC.le
  have hS_eq : ∀ p ∈ S, (∫ x, x / (p.1 + p.2.1 * x) ∂(p.2.2 : Measure ℝ)) = Gfun Cs p := by
    rintro p ⟨-, -, hμ⟩
    unfold Gfun
    apply integral_congr_ae
    filter_upwards [ae_mem_of_classK1 hμ] with x hx
    exact (gK_eq_of_mem _ _ hx).symm
  intro p0 hp0
  have hs0 : 0 < p0.1 := Set.mem_Ioi.mp hp0.1
  have ha0 : 0 ≤ p0.2.1 := Set.mem_Ici.mp hp0.2.1
  have hG : ContinuousWithinAt (Gfun Cs) S p0 := by
    set g0 : BoundedContinuousFunction ℝ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (gK Cs p0.1 p0.2.1)
      (gK_continuous hs0 ha0 hC0) (Cs / p0.1) (fun x => gK_abs_le hC0 hs0 ha0) with hg0
    have hG0 : Gfun Cs p0 = ∫ x, g0 x ∂(p0.2.2 : Measure ℝ) := rfl
    have hμT : Tendsto (fun p : ℝ × ℝ × FiniteMeasure ℝ => p.2.2) (𝓝[S] p0) (𝓝 p0.2.2) :=
      ((continuous_snd.comp continuous_snd).tendsto p0).mono_left nhdsWithin_le_nhds
    have hint : Tendsto (fun p : ℝ × ℝ × FiniteMeasure ℝ => ∫ x, g0 x ∂(p.2.2 : Measure ℝ))
        (𝓝[S] p0) (𝓝 (∫ x, g0 x ∂(p0.2.2 : Measure ℝ))) :=
      FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμT g0
    have hsev : ∀ᶠ p in 𝓝[S] p0, p0.1 / 2 < p.1 :=
      eventually_nhdsWithin_of_eventually_nhds
        ((continuous_fst.tendsto p0).eventually (lt_mem_nhds (by linarith : p0.1 / 2 < p0.1)))
    have hev : ∀ᶠ p in 𝓝[S] p0, p ∈ S ∧ p0.1 / 2 < p.1 := by
      filter_upwards [self_mem_nhdsWithin, hsev] with p hp hp2 using ⟨hp, hp2⟩
    have hCT : Tendsto (fun p : ℝ × ℝ × FiniteMeasure ℝ => modC Cs (p0.1 / 2) p.1 p.2.1 p0.1 p0.2.1)
        (𝓝[S] p0) (𝓝 0) := by
      have h := ((modC_continuous Cs (p0.1 / 2) p0.1 p0.2.1).tendsto p0).mono_left
        (nhdsWithin_le_nhds (s := S))
      simpa [modC] using h
    have hsq : Tendsto (fun p : ℝ × ℝ × FiniteMeasure ℝ =>
        modC Cs (p0.1 / 2) p.1 p.2.1 p0.1 p0.2.1 * γ +
          ‖(∫ x, g0 x ∂(p.2.2 : Measure ℝ)) - ∫ x, g0 x ∂(p0.2.2 : Measure ℝ)‖)
        (𝓝[S] p0) (𝓝 0) := by
      have h3 : Tendsto (fun p : ℝ × ℝ × FiniteMeasure ℝ =>
          ‖(∫ x, g0 x ∂(p.2.2 : Measure ℝ)) - ∫ x, g0 x ∂(p0.2.2 : Measure ℝ)‖)
          (𝓝[S] p0) (𝓝 0) := by
        have := (hint.sub_const (∫ x, g0 x ∂(p0.2.2 : Measure ℝ))).norm
        rw [sub_self, norm_zero] at this
        exact this
      have h4 := (hCT.mul_const γ).add h3
      rw [zero_mul, add_zero] at h4
      exact h4
    have hmain : Tendsto (fun p : ℝ × ℝ × FiniteMeasure ℝ => ‖Gfun Cs p - Gfun Cs p0‖)
        (𝓝[S] p0) (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ hsq
      · exact Filter.Eventually.of_forall (fun p => norm_nonneg _)
      · filter_upwards [hev] with p hp
        obtain ⟨hpS, hpsev⟩ := hp
        have hμp : p.2.2 ∈ classK1 Cs γ := hpS.2.2
        have ha : 0 ≤ p.2.1 := Set.mem_Ici.mp hpS.2.1
        have hs : 0 < p.1 := by linarith
        have hint1 : Integrable (fun x => gK Cs p.1 p.2.1 x) (p.2.2 : Measure ℝ) :=
          Integrable.of_bound (gK_continuous hs ha hC0).aestronglyMeasurable (Cs / p.1)
            (ae_of_all _ fun x => gK_abs_le hC0 hs ha)
        have hint2 : Integrable (fun x => g0 x) (p.2.2 : Measure ℝ) := g0.integrable _
        have hdiff : Gfun Cs p - ∫ x, g0 x ∂(p.2.2 : Measure ℝ) =
            ∫ x, (gK Cs p.1 p.2.1 x - g0 x) ∂(p.2.2 : Measure ℝ) :=
          (integral_sub hint1 hint2).symm
        have hmC : 0 ≤ modC Cs (p0.1 / 2) p.1 p.2.1 p0.1 p0.2.1 := by
          unfold modC
          exact div_nonneg (mul_nonneg hC0 (add_nonneg (abs_nonneg _)
            (mul_nonneg hC0 (abs_nonneg _)))) (mul_self_nonneg _)
        have hbd : ‖∫ x, (gK Cs p.1 p.2.1 x - g0 x) ∂(p.2.2 : Measure ℝ)‖ ≤
            modC Cs (p0.1 / 2) p.1 p.2.1 p0.1 p0.2.1 * γ := by
          have h := norm_integral_le_of_norm_le_const (μ := (p.2.2 : Measure ℝ))
            (f := fun x => gK Cs p.1 p.2.1 x - g0 x)
            (C := modC Cs (p0.1 / 2) p.1 p.2.1 p0.1 p0.2.1)
            (ae_of_all _ fun x => gK_sub_le (σ := p0.1 / 2) (s' := p0.1) (a' := p0.2.1)
              (x := x) hC0 (by linarith) hpsev.le (by linarith) ha ha0)
          exact h.trans (mul_le_mul_of_nonneg_left (univ_real_le hγ hμp) hmC)
        have hA : ‖Gfun Cs p - ∫ x, g0 x ∂(p.2.2 : Measure ℝ)‖ ≤
            modC Cs (p0.1 / 2) p.1 p.2.1 p0.1 p0.2.1 * γ := by
          rw [hdiff]; exact hbd
        have hsplit : Gfun Cs p - Gfun Cs p0 =
            (Gfun Cs p - ∫ x, g0 x ∂(p.2.2 : Measure ℝ)) +
              ((∫ x, g0 x ∂(p.2.2 : Measure ℝ)) - ∫ x, g0 x ∂(p0.2.2 : Measure ℝ)) := by
          rw [hG0]; ring
        rw [hsplit]
        have htri := norm_add_le (Gfun Cs p - ∫ x, g0 x ∂(p.2.2 : Measure ℝ))
          ((∫ x, g0 x ∂(p.2.2 : Measure ℝ)) - ∫ x, g0 x ∂(p0.2.2 : Measure ℝ))
        linarith
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hmain
  have hGc : ContinuousWithinAt (Gfun Cs) S p0 := hG
  exact hGc.congr (fun p hp => hS_eq p hp) (hS_eq p0 hp0)


/-! ## Stability and continuity of the branch -/

/-- The components `(σ, σ̃, a, c)` satisfying the defining equations form a solution. -/
private lemma isBranchSol_mk {F : ℝ → ℝ} {μ ν : FiniteMeasure ℝ} {s σ σ' a c : ℝ}
    (h0 : 0 ≤ σ) (h1 : 0 ≤ σ') (h2 : 0 ≤ a) (h3 : 0 ≤ c)
    (e1 : σ = ∫ t, t / (a * t + s) ∂(μ : Measure ℝ))
    (e2 : σ' = ∫ t, t / (c * t + s) ∂(ν : Measure ℝ))
    (e3 : a = s * σ' * F (s * σ * σ')) (e4 : c = s * σ * F (s * σ * σ')) :
    IsBranchSol F μ ν s (σ, σ', a, c) := by
  simp only [IsBranchSol]
  exact ⟨h0, h1, h2, h3, e1, e2, e3, e4⟩

private lemma integral_comm_add (μ : Measure ℝ) (s a : ℝ) :
    ∫ t, t / (s + a * t) ∂μ = ∫ t, t / (a * t + s) ∂μ := by
  congr 1
  funext t
  rw [add_comm]

/-- Solution equations of `branchSol`, in the form of `lem_app_de_compact_ii`. -/
private lemma bs_eqs {F : ℝ → ℝ} (hF : AdmissibleWeightFn F) {Cs γ : ℝ} (hC : 0 < Cs) (hγ : 0 < γ)
    {μ ν : FiniteMeasure ℝ} (hp : (μ, ν) ∈ classK Cs γ) {s : ℝ} (hs : 0 < s) :
    0 ≤ (branchSol F μ ν s).1 ∧ 0 ≤ (branchSol F μ ν s).2.1 ∧
    0 ≤ (branchSol F μ ν s).2.2.1 ∧ 0 ≤ (branchSol F μ ν s).2.2.2 ∧
    (branchSol F μ ν s).1 = ∫ t, t / (s + (branchSol F μ ν s).2.2.1 * t) ∂(μ : Measure ℝ) ∧
    (branchSol F μ ν s).2.1 = ∫ t, t / (s + (branchSol F μ ν s).2.2.2 * t) ∂(ν : Measure ℝ) ∧
    (branchSol F μ ν s).2.2.1 = s * (branchSol F μ ν s).2.1 *
      F (s * (branchSol F μ ν s).1 * (branchSol F μ ν s).2.1) ∧
    (branchSol F μ ν s).2.2.2 = s * (branchSol F μ ν s).1 *
      F (s * (branchSol F μ ν s).1 * (branchSol F μ ν s).2.1) := by
  have h := branchSol_spec hF hC hγ hp hs
  generalize branchSol F μ ν s = x at h ⊢
  obtain ⟨σ, σ', a, c⟩ := x
  obtain ⟨h0, h0', h0a, h0c, h1, h2, h3, h4⟩ := h
  have e1 : ∀ t : ℝ, t / (s + a * t) = t / (a * t + s) := fun t => by rw [add_comm]
  have e2 : ∀ t : ℝ, t / (s + c * t) = t / (c * t + s) := fun t => by rw [add_comm]
  refine ⟨h0, h0', h0a, h0c, ?_, ?_, h3, h4⟩
  · change σ = ∫ t, t / (s + a * t) ∂(μ : Measure ℝ)
    simp only [e1]
    exact h1
  · change σ' = ∫ t, t / (s + c * t) ∂(ν : Measure ℝ)
    simp only [e2]
    exact h2

/-- `thm:app-de-branch`(ii), snapshot `cr-2026-10-23`. LaTeX
(`sections/02-deterministic-equivalents/section.tex` l.164–166 and l.174–178):
```
\begin{theorem}[The weighted branch]\label{thm:app-de-branch}
Let $w$ be nonnegative, summable and not all zero, and let $C_\Sigma,\gamma_\star>0$.
\begin{enumerate}[label=(\roman*)]
...
\item (Continuity.) Equip $\mathcal K$ with the topology of weak convergence
against $C([0,C_\Sigma])$ in each coordinate. The solution map
$(s,\nu,\tilde\nu)\mapsto(\sigma,\tilde\sigma,\tilde s_1,s_1)$ is continuous on
$(0,\infty)\times\mathcal K$, and for every compact $I\subset(0,\infty)$ it is
uniformly continuous on $I\times\mathcal K$.
```
Encoding: "uniformly continuous on `I × 𝒦`" is replaced by (a) joint continuity of the solution map
`(s, (ν, ν̃)) ↦ branchSol` on `(0,∞) × 𝒦`, and (b) for every compact `I ⊆ (0,∞)` and every `ε > 0`
a `δ > 0`, uniform over `𝒦` and over `s, s' ∈ I`, with `|s - s'| < δ ⇒ dist < ε` (CARD §6.3,
CORRECTIONS #5). The distance is the sup-norm on `ℝ × ℝ × ℝ × ℝ`. -/
theorem thm_app_de_branch_ii {F : ℝ → ℝ} (hF : AdmissibleWeightFn F) {Cs γ : ℝ}
    (hC : 0 < Cs) (hγ : 0 < γ) :
    ContinuousOn (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) => branchSol F p.2.1 p.2.2 p.1)
      (Ioi 0 ×ˢ classK Cs γ) ∧
    ∀ I : Set ℝ, IsCompact I → I ⊆ Ioi 0 → ∀ ε > 0, ∃ δ > 0,
      ∀ p ∈ classK Cs γ, ∀ s ∈ I, ∀ s' ∈ I, |s - s'| < δ →
        dist (branchSol F p.1 p.2 s) (branchSol F p.1 p.2 s') < ε := by
  have hK : IsCompact (classK Cs γ) := lem_app_de_compact_i hC hγ
  have hG := lem_app_de_compact_ii hC hγ
  have hK1 : ∀ μ ν : FiniteMeasure ℝ, (μ, ν) ∈ classK Cs γ → μ ∈ classK1 Cs γ :=
    fun μ ν h => ⟨h.1, h.2.1⟩
  have hK2 : ∀ μ ν : FiniteMeasure ℝ, (μ, ν) ∈ classK Cs γ → ν ∈ classK1 Cs γ :=
    fun μ ν h => ⟨h.2.2.1, h.2.2.2⟩
  have part1 : ContinuousOn
      (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) => branchSol F p.2.1 p.2.2 p.1)
      (Ioi 0 ×ˢ classK Cs γ) := by
    rintro ⟨s0, μ0, ν0⟩ ⟨hs0, hp0⟩
    have hs0' : (0:ℝ) < s0 := hs0
    have hIoo : Ioo (s0/2) (2*s0) ∈ 𝓝 s0 := Ioo_mem_nhds (by linarith) (by linarith)
    have hNmem : (Ioo (s0/2) (2*s0) ×ˢ (univ : Set (FiniteMeasure ℝ × FiniteMeasure ℝ))) ∩
        (Ioi (0:ℝ) ×ˢ classK Cs γ) ∈ 𝓝[Ioi (0:ℝ) ×ˢ classK Cs γ] (s0, μ0, ν0) :=
      Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (prod_mem_nhds hIoo univ_mem))
        self_mem_nhdsWithin
    set N := (Ioo (s0/2) (2*s0) ×ˢ (univ : Set (FiniteMeasure ℝ × FiniteMeasure ℝ))) ∩
        (Ioi (0:ℝ) ×ˢ classK Cs γ) with hNdef
    set Bx : Set (ℝ × ℝ × ℝ × ℝ) := Icc 0 (γ * Cs / (s0/2)) ×ˢ Icc 0 (γ * Cs / (s0/2)) ×ˢ
      Icc 0 (γ * Cs * F 0) ×ˢ Icc 0 (γ * Cs * F 0) with hBxdef
    have hBxc : IsCompact Bx :=
      isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
    have hpN : ∀ p ∈ N, 0 < p.1 ∧ p.2 ∈ classK Cs γ := fun p hp => ⟨hp.2.1, hp.2.2⟩
    have hbox : ∀ p ∈ N, branchSol F p.2.1 p.2.2 p.1 ∈ Bx := by
      intro p hp
      obtain ⟨hs, hp'⟩ := hpN p hp
      have hI : p.1 ∈ Ioo (s0/2) (2*s0) := hp.1.1
      have hsI : s0/2 < p.1 := hI.1
      have hpc : (p.2.1, p.2.2) ∈ classK Cs γ := hp'
      have hb := (thm_app_de_branch_i hF hC hγ p.2.1 p.2.2 hpc p.1 hs).2 _
        (branchSol_spec hF hC hγ hpc hs)
      obtain ⟨b1, b2, b3, b4, -⟩ := hb
      obtain ⟨n1, n2, n3, n4, -⟩ := bs_eqs hF hC hγ hpc hs
      have hdiv : γ * Cs / p.1 ≤ γ * Cs / (s0/2) :=
        div_le_div_of_nonneg_left (mul_nonneg hγ.le hC.le) (by linarith) hsI.le
      exact ⟨⟨n1, b1.trans hdiv⟩, ⟨n2, b2.trans hdiv⟩, ⟨n3, b3⟩, ⟨n4, b4⟩⟩
    unfold ContinuousWithinAt
    rw [tendsto_iff_ultrafilter]
    intro U hU
    have hUN : N ∈ (U : Filter _) := hU hNmem
    set V : Ultrafilter (ℝ × ℝ × ℝ × ℝ) :=
      U.map (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) => branchSol F p.2.1 p.2.2 p.1)
      with hVdef
    have hVle : (V : Filter (ℝ × ℝ × ℝ × ℝ)) ≤ 𝓟 Bx := by
      rw [hVdef, Ultrafilter.coe_map, Filter.le_principal_iff]
      exact Filter.mem_map.2 (Filter.mem_of_superset hUN (fun (p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ)) hp => hbox p hp))
    obtain ⟨y, hyBx, hy⟩ := hBxc.ultrafilter_le_nhds V hVle
    have hyT : Tendsto (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        branchSol F p.2.1 p.2.2 p.1) U (𝓝 y) := hy
    have hU0 : Tendsto id (U : Filter _) (𝓝 (s0, μ0, ν0)) := hU.trans nhdsWithin_le_nhds
    have hsT : Tendsto (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) => p.1) U (𝓝 s0) :=
      (continuous_fst.tendsto _).comp hU0
    have hμT : Tendsto (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) => p.2.1) U (𝓝 μ0) :=
      ((continuous_fst.comp continuous_snd).tendsto _).comp hU0
    have hνT : Tendsto (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) => p.2.2) U (𝓝 ν0) :=
      ((continuous_snd.comp continuous_snd).tendsto _).comp hU0
    have hy1T : Tendsto (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        (branchSol F p.2.1 p.2.2 p.1).1) U (𝓝 y.1) :=
      (continuous_fst.tendsto y).comp hyT
    have hy2T : Tendsto (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        (branchSol F p.2.1 p.2.2 p.1).2.1) U (𝓝 y.2.1) :=
      ((continuous_fst.comp continuous_snd).tendsto y).comp hyT
    have hy3T : Tendsto (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        (branchSol F p.2.1 p.2.2 p.1).2.2.1) U (𝓝 y.2.2.1) :=
      ((continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto y).comp hyT
    have hy4T : Tendsto (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        (branchSol F p.2.1 p.2.2 p.1).2.2.2) U (𝓝 y.2.2.2) :=
      ((continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto y).comp hyT
    have hy0 : 0 ≤ y.1 := hyBx.1.1
    have hy1 : 0 ≤ y.2.1 := hyBx.2.1.1
    have hy3 : 0 ≤ y.2.2.1 := hyBx.2.2.1.1
    have hy4 : 0 ≤ y.2.2.2 := hyBx.2.2.2.1
    -- sigma-equation
    have hσ : y.1 = ∫ t, t / (s0 + y.2.2.1 * t) ∂(μ0 : Measure ℝ) := by
      have hwS : (s0, y.2.2.1, μ0) ∈ Ioi (0:ℝ) ×ˢ Ici (0:ℝ) ×ˢ classK1 Cs γ :=
        ⟨hs0', hy3, hK1 μ0 ν0 hp0⟩
      have hGc := hG (s0, y.2.2.1, μ0) hwS
      have hGlim : Tendsto (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
          (p.1, (branchSol F p.2.1 p.2.2 p.1).2.2.1, p.2.1)) U (𝓝 (s0, y.2.2.1, μ0)) :=
        hsT.prodMk_nhds (hy3T.prodMk_nhds hμT)
      have hev : ∀ᶠ p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) in (U : Filter _), (p.1, (branchSol F p.2.1 p.2.2 p.1).2.2.1, p.2.1) ∈
          Ioi (0:ℝ) ×ˢ Ici (0:ℝ) ×ˢ classK1 Cs γ :=
        Filter.eventually_of_mem hUN (fun (p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ)) hp => ⟨(hpN p hp).1,
          (bs_eqs hF hC hγ (hpN p hp).2 (hpN p hp).1).2.2.1, hK1 _ _ (hpN p hp).2⟩)
      have hlim := hGc.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hGlim, hev⟩)
      have hfg : (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
          (branchSol F p.2.1 p.2.2 p.1).1) =ᶠ[(U : Filter _)]
          (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
            ∫ t, t / (p.1 + (branchSol F p.2.1 p.2.2 p.1).2.2.1 * t) ∂(p.2.1 : Measure ℝ)) :=
        Filter.eventually_of_mem hUN (fun (p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ)) hp =>
          (bs_eqs hF hC hγ (hpN p hp).2 (hpN p hp).1).2.2.2.2.1)
      exact tendsto_nhds_unique_of_eventuallyEq hy1T hlim hfg
    -- sigma'-equation
    have hσ' : y.2.1 = ∫ t, t / (s0 + y.2.2.2 * t) ∂(ν0 : Measure ℝ) := by
      have hwS : (s0, y.2.2.2, ν0) ∈ Ioi (0:ℝ) ×ˢ Ici (0:ℝ) ×ˢ classK1 Cs γ :=
        ⟨hs0', hy4, hK2 μ0 ν0 hp0⟩
      have hGc := hG (s0, y.2.2.2, ν0) hwS
      have hGlim : Tendsto (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
          (p.1, (branchSol F p.2.1 p.2.2 p.1).2.2.2, p.2.2)) U (𝓝 (s0, y.2.2.2, ν0)) :=
        hsT.prodMk_nhds (hy4T.prodMk_nhds hνT)
      have hev : ∀ᶠ p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) in (U : Filter _), (p.1, (branchSol F p.2.1 p.2.2 p.1).2.2.2, p.2.2) ∈
          Ioi (0:ℝ) ×ˢ Ici (0:ℝ) ×ˢ classK1 Cs γ :=
        Filter.eventually_of_mem hUN (fun (p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ)) hp => ⟨(hpN p hp).1,
          (bs_eqs hF hC hγ (hpN p hp).2 (hpN p hp).1).2.2.2.1, hK2 _ _ (hpN p hp).2⟩)
      have hlim := hGc.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hGlim, hev⟩)
      have hfg : (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
          (branchSol F p.2.1 p.2.2 p.1).2.1) =ᶠ[(U : Filter _)]
          (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
            ∫ t, t / (p.1 + (branchSol F p.2.1 p.2.2 p.1).2.2.2 * t) ∂(p.2.2 : Measure ℝ)) :=
        Filter.eventually_of_mem hUN (fun (p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ)) hp =>
          (bs_eqs hF hC hγ (hpN p hp).2 (hpN p hp).1).2.2.2.2.2.1)
      exact tendsto_nhds_unique_of_eventuallyEq hy2T hlim hfg
    -- the two algebraic equations
    have hq0 : 0 ≤ s0 * y.1 * y.2.1 := mul_nonneg (mul_nonneg hs0'.le hy0) hy1
    have hqT : Tendsto (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        p.1 * (branchSol F p.2.1 p.2.2 p.1).1 * (branchSol F p.2.1 p.2.2 p.1).2.1) U
        (𝓝 (s0 * y.1 * y.2.1)) :=
      (hsT.mul hy1T).mul hy2T
    have hqmem : ∀ᶠ p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) in (U : Filter _), p.1 * (branchSol F p.2.1 p.2.2 p.1).1 *
        (branchSol F p.2.1 p.2.2 p.1).2.1 ∈ Ici (0:ℝ) :=
      Filter.eventually_of_mem hUN (fun (p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ)) hp => mul_nonneg (mul_nonneg (hpN p hp).1.le
        (bs_eqs hF hC hγ (hpN p hp).2 (hpN p hp).1).1)
        (bs_eqs hF hC hγ (hpN p hp).2 (hpN p hp).1).2.1)
    have hFc : ContinuousWithinAt F (Ici 0) (s0 * y.1 * y.2.1) := hF.contOn _ hq0
    have hFlim := hFc.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hqT, hqmem⟩)
    have hHa : Tendsto (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        p.1 * (branchSol F p.2.1 p.2.2 p.1).2.1 *
          F (p.1 * (branchSol F p.2.1 p.2.2 p.1).1 * (branchSol F p.2.1 p.2.2 p.1).2.1)) U
        (𝓝 (s0 * y.2.1 * F (s0 * y.1 * y.2.1))) :=
      (hsT.mul hy2T).mul hFlim
    have hfa : (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        p.1 * (branchSol F p.2.1 p.2.2 p.1).2.1 *
          F (p.1 * (branchSol F p.2.1 p.2.2 p.1).1 * (branchSol F p.2.1 p.2.2 p.1).2.1))
        =ᶠ[(U : Filter _)]
        (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) => (branchSol F p.2.1 p.2.2 p.1).2.2.1) :=
      Filter.eventually_of_mem hUN (fun (p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ)) hp =>
        (bs_eqs hF hC hγ (hpN p hp).2 (hpN p hp).1).2.2.2.2.2.2.1.symm)
    have ha : s0 * y.2.1 * F (s0 * y.1 * y.2.1) = y.2.2.1 :=
      tendsto_nhds_unique_of_eventuallyEq hHa hy3T hfa
    have hHc : Tendsto (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        p.1 * (branchSol F p.2.1 p.2.2 p.1).1 *
          F (p.1 * (branchSol F p.2.1 p.2.2 p.1).1 * (branchSol F p.2.1 p.2.2 p.1).2.1)) U
        (𝓝 (s0 * y.1 * F (s0 * y.1 * y.2.1))) :=
      (hsT.mul hy1T).mul hFlim
    have hfc : (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        p.1 * (branchSol F p.2.1 p.2.2 p.1).1 *
          F (p.1 * (branchSol F p.2.1 p.2.2 p.1).1 * (branchSol F p.2.1 p.2.2 p.1).2.1))
        =ᶠ[(U : Filter _)]
        (fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) => (branchSol F p.2.1 p.2.2 p.1).2.2.2) :=
      Filter.eventually_of_mem hUN (fun (p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ)) hp =>
        (bs_eqs hF hC hγ (hpN p hp).2 (hpN p hp).1).2.2.2.2.2.2.2.symm)
    have hc : s0 * y.1 * F (s0 * y.1 * y.2.1) = y.2.2.2 :=
      tendsto_nhds_unique_of_eventuallyEq hHc hy4T hfc
    -- identify the limit with branchSol by uniqueness
    have e1 : y.1 = ∫ t, t / (y.2.2.1 * t + s0) ∂(μ0 : Measure ℝ) := by
      rw [hσ, integral_comm_add]
    have e2 : y.2.1 = ∫ t, t / (y.2.2.2 * t + s0) ∂(ν0 : Measure ℝ) := by
      rw [hσ', integral_comm_add]
    have hyIS : IsBranchSol F μ0 ν0 s0 (y.1, y.2.1, y.2.2.1, y.2.2.2) :=
      isBranchSol_mk hy0 hy1 hy3 hy4 e1 e2 ha.symm hc.symm
    obtain ⟨z, -, hz⟩ := (thm_app_de_branch_i hF hC hγ μ0 ν0 hp0 s0 hs0').1
    have hyB : (y.1, y.2.1, y.2.2.1, y.2.2.2) = z := hz _ hyIS
    have hbB : branchSol F μ0 ν0 s0 = z := hz _ (branchSol_spec hF hC hγ hp0 hs0')
    have hyeq : y = branchSol F μ0 ν0 s0 := by
      rw [hbB, ← hyB]
    rw [hyeq] at hyT
    exact hyT
  refine ⟨part1, ?_⟩
  intro I hI hI0 ε hε
  set K : Set (ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ)) := I ×ˢ I ×ˢ classK Cs γ with hKdef
  have hKc : IsCompact K := hI.prod (hI.prod hK)
  have hsub1 : ContinuousOn (fun q : ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
      branchSol F q.2.2.1 q.2.2.2 q.1) K :=
    part1.comp (f := fun q : ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) => (q.1, q.2.2))
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn
      (fun q hq => ⟨hI0 hq.1, hq.2.2⟩)
  have hsub2 : ContinuousOn (fun q : ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
      branchSol F q.2.2.1 q.2.2.2 q.2.1) K :=
    part1.comp (f := fun q : ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) => (q.2.1, q.2.2))
      ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd)).continuousOn
      (fun q hq => ⟨hI0 hq.2.1, hq.2.2⟩)
  set g : ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) → ℝ := fun q =>
    dist (branchSol F q.2.2.1 q.2.2.2 q.1) (branchSol F q.2.2.1 q.2.2.2 q.2.1) with hgdef
  have hgc : ContinuousOn g K := fun q hq => Filter.Tendsto.dist (hsub1 q hq) (hsub2 q hq)
  set Ω := K ∩ g ⁻¹' Ici ε with hΩdef
  have hΩcl : IsClosed Ω := hgc.preimage_isClosed_of_isClosed hKc.isClosed isClosed_Ici
  have hΩc : IsCompact Ω := hKc.of_isClosed_subset hΩcl Set.inter_subset_left
  set D : Set (ℝ × ℝ) := (fun q : ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
    (q.1, q.2.1)) '' Ω with hDdef
  have hDc : IsCompact D := hΩc.image (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hne0 : ∀ x ∈ D, x.1 ≠ x.2 := by
    rintro x ⟨q, hq, rfl⟩ heq
    dsimp only at heq
    have hq' : ε ≤ g q := hq.2
    simp only [hgdef] at hq'
    rw [show q.2.1 = q.1 from heq.symm, dist_self] at hq'
    linarith
  obtain ⟨δ, hδ, hδD⟩ : ∃ δ > 0, ∀ x ∈ D, δ ≤ |x.1 - x.2| := by
    rcases D.eq_empty_or_nonempty with hE | hne
    · exact ⟨1, one_pos, fun x hx => by simp [hE] at hx⟩
    · obtain ⟨x0, hx0, hmin⟩ := hDc.exists_isMinOn hne
        (f := fun x : ℝ × ℝ => |x.1 - x.2|)
        (by fun_prop : Continuous fun x : ℝ × ℝ => |x.1 - x.2|).continuousOn
      refine ⟨|x0.1 - x0.2|, abs_pos.2 (sub_ne_zero.2 (hne0 x0 hx0)), fun x hx => ?_⟩
      exact isMinOn_iff.1 hmin x hx
  refine ⟨δ, hδ, fun p hp s hs s' hs' hss => ?_⟩
  by_contra hge
  push_neg at hge
  have hmem : (s, s', p) ∈ Ω := ⟨⟨hs, hs', hp⟩, hge⟩
  have h2 := hδD (s, s') ⟨(s, s', p), hmem, rfl⟩
  dsimp only at h2
  linarith

/-- `thm:app-de-branch`(iii), snapshot `cr-2026-10-23`. LaTeX
(`sections/02-deterministic-equivalents/section.tex` l.164–166 and l.179–195):
```
\begin{theorem}[The weighted branch]\label{thm:app-de-branch}
Let $w$ be nonnegative, summable and not all zero, and let $C_\Sigma,\gamma_\star>0$.
\begin{enumerate}[label=(\roman*)]
...
\item (Stability under approximate roots.) Let $I\subset(0,\infty)$ be compact
with $s_-\defeq\min I$. For every $\epsilon>0$ there is $\delta>0$, depending
only on $(\epsilon,I,C_\Sigma,\gamma_\star,w)$, with the following property.
If $(\nu,\tilde\nu)\in\mathcal K$, $s\in I$, and
$(\sigma',\tilde\sigma',a',c')\in[0,\gamma_\star C_\Sigma/s_-]^2\times[0,\gamma_\star C_\Sigma\sw2]^2$
satisfy, with $q'=s\sigma'\tilde\sigma'$,
\[
\begin{gathered}
\Big|\sigma'-\int\frac{x}{s+a'x}\,\nu(dx)\Big|\le\delta,\qquad
\Big|\tilde\sigma'-\int\frac{x}{s+c'x}\,\tilde\nu(dx)\Big|\le\delta,\\
\abs{a'-s\tilde\sigma'F_w(q')}\le\delta,\qquad
\abs{c'-s\sigma'F_w(q')}\le\delta,
\end{gathered}
\]
then $\abs{\sigma'-\sigma}+\abs{\tilde\sigma'-\tilde\sigma}+\abs{a'-\tilde s_1}+\abs{c'-s_1}\le\epsilon$,
where $(\sigma,\tilde\sigma,\tilde s_1,s_1)$ is the solution of
\cref{eqn:app-de-system} at $z=-s$ for $(\nu,\tilde\nu)$.
```
Encoding: the box `[0,γ⋆C_Σ/s₋]²×[0,γ⋆C_Σ·∑w²]²` is generalized to `[0,𝔟]⁴`
(CARD §3 row 3); `s₋ = min I` is not needed. The tuple is `(u, v, a, c) = (σ', σ̃', a', c')` with `q' = s u v`; the four
approximate relations are those of the source with `δ`; the conclusion is the sum of the four
absolute errors against `(σ, σ̃, s̃₁, s₁)(-s) = branchSol F ν ν' s`. -/
theorem thm_app_de_branch_iii {F : ℝ → ℝ} (hF : AdmissibleWeightFn F) {Cs γ 𝔟 : ℝ}
    (hC : 0 < Cs) (hγ : 0 < γ) {I : Set ℝ} (hI : IsCompact I) (hI0 : I ⊆ Ioi 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ ν ν' : FiniteMeasure ℝ, (ν, ν') ∈ classK Cs γ →
      ∀ s ∈ I, ∀ u v a c : ℝ, u ∈ Icc 0 𝔟 → v ∈ Icc 0 𝔟 → a ∈ Icc 0 𝔟 → c ∈ Icc 0 𝔟 →
        |u - ∫ t, t / (s + a * t) ∂(ν : Measure ℝ)| ≤ δ →
        |v - ∫ t, t / (s + c * t) ∂(ν' : Measure ℝ)| ≤ δ →
        |a - s * v * F (s * u * v)| ≤ δ →
        |c - s * u * F (s * u * v)| ≤ δ →
        |u - (branchSol F ν ν' s).1| + |v - (branchSol F ν ν' s).2.1| +
          |a - (branchSol F ν ν' s).2.2.1| + |c - (branchSol F ν ν' s).2.2.2| ≤ ε := by
  intro ε hε
  obtain ⟨Q, hQdef⟩ : ∃ Q : Set (ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ)),
      Q = Icc 0 𝔟 ×ˢ Icc 0 𝔟 ×ˢ Icc 0 𝔟 ×ˢ Icc 0 𝔟 ×ˢ I ×ˢ classK Cs γ := ⟨_, rfl⟩
  have hQc : IsCompact Q := by
    rw [hQdef]
    exact isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod
      (isCompact_Icc.prod (hI.prod (lem_app_de_compact_i hC hγ)))))
  have hmemQ : ∀ q : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ), q ∈ Q ↔
      (q.1 ∈ Icc 0 𝔟 ∧ q.2.1 ∈ Icc 0 𝔟 ∧ q.2.2.1 ∈ Icc 0 𝔟 ∧ q.2.2.2.1 ∈ Icc 0 𝔟 ∧
        q.2.2.2.2.1 ∈ I ∧ q.2.2.2.2.2 ∈ classK Cs γ) := by
    intro q
    rw [hQdef]
    exact Iff.rfl
  obtain ⟨f1, hf1⟩ : ∃ f : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) → ℝ,
      f = fun p => ∫ t, t / (p.2.2.2.2.1 + p.2.2.1 * t) ∂(p.2.2.2.2.2.1 : Measure ℝ) := ⟨_, rfl⟩
  obtain ⟨f2, hf2⟩ : ∃ f : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) → ℝ,
      f = fun p => ∫ t, t / (p.2.2.2.2.1 + p.2.2.2.1 * t) ∂(p.2.2.2.2.2.2 : Measure ℝ) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ f : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) → ℝ,
      f = fun p => F (p.2.2.2.2.1 * p.1 * p.2.1) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ f : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) → ℝ,
      f = fun p => |p.1 - f1 p| + |p.2.1 - f2 p| + |p.2.2.1 - p.2.2.2.2.1 * p.2.1 * g p| +
        |p.2.2.2.1 - p.2.2.2.2.1 * p.1 * g p| := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ f : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) → ℝ,
      f = fun p => |p.1 - (branchSol F p.2.2.2.2.2.1 p.2.2.2.2.2.2 p.2.2.2.2.1).1| +
        |p.2.1 - (branchSol F p.2.2.2.2.2.1 p.2.2.2.2.2.2 p.2.2.2.2.1).2.1| +
        |p.2.2.1 - (branchSol F p.2.2.2.2.2.1 p.2.2.2.2.2.2 p.2.2.2.2.1).2.2.1| +
        |p.2.2.2.1 - (branchSol F p.2.2.2.2.2.1 p.2.2.2.2.2.2 p.2.2.2.2.1).2.2.2| := ⟨_, rfl⟩
  -- continuity of the ingredients on the compact set `Q`
  have hfc1 : ContinuousOn f1 Q := by
    rw [hf1]
    have hφ1 : Continuous (fun p : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        (p.2.2.2.2.1, p.2.2.1, p.2.2.2.2.2.1)) := by fun_prop
    refine (lem_app_de_compact_ii hC hγ).comp hφ1.continuousOn ?_
    intro q hq
    obtain ⟨hu, hv, ha, hc, hs, hp⟩ := (hmemQ q).1 hq
    exact ⟨hI0 hs, ha.1, hp.1, hp.2.1⟩
  have hfc2 : ContinuousOn f2 Q := by
    rw [hf2]
    have hφ2 : Continuous (fun p : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        (p.2.2.2.2.1, p.2.2.2.1, p.2.2.2.2.2.2)) := by fun_prop
    refine (lem_app_de_compact_ii hC hγ).comp hφ2.continuousOn ?_
    intro q hq
    obtain ⟨hu, hv, ha, hc, hs, hp⟩ := (hmemQ q).1 hq
    exact ⟨hI0 hs, hc.1, hp.2.2.1, hp.2.2.2⟩
  have hgc : ContinuousOn g Q := by
    rw [hg]
    have hφg : Continuous (fun p : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        p.2.2.2.2.1 * p.1 * p.2.1) := by fun_prop
    refine hF.contOn.comp hφg.continuousOn ?_
    intro q hq
    obtain ⟨hu, hv, ha, hc, hs, hp⟩ := (hmemQ q).1 hq
    have hs0 : 0 < q.2.2.2.2.1 := hI0 hs
    exact mul_nonneg (mul_nonneg hs0.le hu.1) hv.1
  have hBs : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
      branchSol F p.2.2.2.2.2.1 p.2.2.2.2.2.2 p.2.2.2.2.1) Q := by
    have hφB : Continuous (fun p : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        (p.2.2.2.2.1, p.2.2.2.2.2)) := by fun_prop
    refine (thm_app_de_branch_ii hF hC hγ).1.comp hφB.continuousOn ?_
    intro q hq
    obtain ⟨hu, hv, ha, hc, hs, hp⟩ := (hmemQ q).1 hq
    exact ⟨hI0 hs, hp⟩
  have hEc : ContinuousOn E Q := by
    rw [hE]
    have c1 : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        (branchSol F p.2.2.2.2.2.1 p.2.2.2.2.2.2 p.2.2.2.2.1).1) Q :=
      (by fun_prop : Continuous (fun x : ℝ × ℝ × ℝ × ℝ => x.1)).comp_continuousOn hBs
    have c2 : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        (branchSol F p.2.2.2.2.2.1 p.2.2.2.2.2.2 p.2.2.2.2.1).2.1) Q :=
      (by fun_prop : Continuous (fun x : ℝ × ℝ × ℝ × ℝ => x.2.1)).comp_continuousOn hBs
    have c3 : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        (branchSol F p.2.2.2.2.2.1 p.2.2.2.2.2.2 p.2.2.2.2.1).2.2.1) Q :=
      (by fun_prop : Continuous (fun x : ℝ × ℝ × ℝ × ℝ => x.2.2.1)).comp_continuousOn hBs
    have c4 : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
        (branchSol F p.2.2.2.2.2.1 p.2.2.2.2.2.2 p.2.2.2.2.1).2.2.2) Q :=
      (by fun_prop : Continuous (fun x : ℝ × ℝ × ℝ × ℝ => x.2.2.2)).comp_continuousOn hBs
    fun_prop
  have hRc : ContinuousOn R Q := by
    rw [hR]
    fun_prop
  -- the set where the error is at least `ε`, compact
  have hFc : IsCompact (Q ∩ E ⁻¹' Ici ε) :=
    hQc.of_isClosed_subset (hEc.preimage_isClosed_of_isClosed hQc.isClosed isClosed_Ici)
      Set.inter_subset_left
  -- on that set the residual is bounded below by a positive constant
  have hpos : ∀ q ∈ Q ∩ E ⁻¹' Ici ε, 0 < R q := by
    rintro q ⟨hq, hEq⟩
    obtain ⟨hu, hv, ha, hc, hs, hp⟩ := (hmemQ q).1 hq
    have hEq' : ε ≤ E q := hEq
    by_contra hneg
    push_neg at hneg
    rw [hR] at hneg
    dsimp only at hneg
    have a1 := abs_nonneg (q.1 - f1 q)
    have a2 := abs_nonneg (q.2.1 - f2 q)
    have a3 := abs_nonneg (q.2.2.1 - q.2.2.2.2.1 * q.2.1 * g q)
    have a4 := abs_nonneg (q.2.2.2.1 - q.2.2.2.2.1 * q.1 * g q)
    have z1 : q.1 - f1 q = 0 := abs_eq_zero.1 (by linarith)
    have z2 : q.2.1 - f2 q = 0 := abs_eq_zero.1 (by linarith)
    have z3 : q.2.2.1 - q.2.2.2.2.1 * q.2.1 * g q = 0 := abs_eq_zero.1 (by linarith)
    have z4 : q.2.2.2.1 - q.2.2.2.2.1 * q.1 * g q = 0 := abs_eq_zero.1 (by linarith)
    have hsp : 0 < q.2.2.2.2.1 := hI0 hs
    have hgq : g q = F (q.2.2.2.2.1 * q.1 * q.2.1) := by rw [hg]
    rw [hgq] at z3 z4
    have k1 : f1 q = ∫ t, t / (q.2.2.2.2.1 + q.2.2.1 * t) ∂(q.2.2.2.2.2.1 : Measure ℝ) := by
      rw [hf1]
    have k2 : f2 q = ∫ t, t / (q.2.2.2.2.1 + q.2.2.2.1 * t) ∂(q.2.2.2.2.2.2 : Measure ℝ) := by
      rw [hf2]
    have e1 := integral_comm_add (q.2.2.2.2.2.1 : Measure ℝ) q.2.2.2.2.1 q.2.2.1
    have e2 := integral_comm_add (q.2.2.2.2.2.2 : Measure ℝ) q.2.2.2.2.1 q.2.2.2.1
    have hsol : IsBranchSol F q.2.2.2.2.2.1 q.2.2.2.2.2.2 q.2.2.2.2.1
        (q.1, q.2.1, q.2.2.1, q.2.2.2.1) :=
      isBranchSol_mk hu.1 hv.1 ha.1 hc.1 (by linarith) (by linarith) (by linarith) (by linarith)
    have huniq := (thm_app_de_branch_i hF hC hγ q.2.2.2.2.2.1 q.2.2.2.2.2.2 hp
      q.2.2.2.2.1 hsp).1.unique hsol (branchSol_spec hF hC hγ hp hsp)
    have f1' : q.1 = (branchSol F q.2.2.2.2.2.1 q.2.2.2.2.2.2 q.2.2.2.2.1).1 :=
      congrArg Prod.fst huniq
    have f2' : q.2.1 = (branchSol F q.2.2.2.2.2.1 q.2.2.2.2.2.2 q.2.2.2.2.1).2.1 :=
      congrArg (fun x => x.2.1) huniq
    have f3' : q.2.2.1 = (branchSol F q.2.2.2.2.2.1 q.2.2.2.2.2.2 q.2.2.2.2.1).2.2.1 :=
      congrArg (fun x => x.2.2.1) huniq
    have f4' : q.2.2.2.1 = (branchSol F q.2.2.2.2.2.1 q.2.2.2.2.2.2 q.2.2.2.2.1).2.2.2 :=
      congrArg (fun x => x.2.2.2) huniq
    rw [hE] at hEq'
    dsimp only at hEq'
    rw [← f1', ← f2', ← f3', ← f4'] at hEq'
    simp only [sub_self, abs_zero, add_zero] at hEq'
    linarith
  -- a uniform margin `δ` on that compact set
  obtain ⟨δ, hδ, hδF⟩ : ∃ δ > 0, ∀ q ∈ Q ∩ E ⁻¹' Ici ε, δ ≤ R q := by
    rcases (Q ∩ E ⁻¹' Ici ε).eq_empty_or_nonempty with hE0 | hne
    · exact ⟨1, one_pos, fun q hq => by simp [hE0] at hq⟩
    · obtain ⟨q0, hq0, hmin⟩ := hFc.exists_isMinOn hne (hRc.mono Set.inter_subset_left)
      exact ⟨R q0, hpos q0 hq0, fun q hq => isMinOn_iff.1 hmin q hq⟩
  refine ⟨δ / 8, div_pos hδ (by norm_num), ?_⟩
  intro ν ν' hp s hs u v a c hu hv ha hc h1 h2 h3 h4
  by_contra hlt
  push_neg at hlt
  have hmem : ((u, v, a, c, s, (ν, ν')) : ℝ × ℝ × ℝ × ℝ × ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ))
      ∈ Q := (hmemQ _).2 ⟨hu, hv, ha, hc, hs, hp⟩
  have hEq : ε ≤ E (u, v, a, c, s, (ν, ν')) := by
    rw [hE]
    exact hlt.le
  have hk := hδF (u, v, a, c, s, (ν, ν')) ⟨hmem, hEq⟩
  have k1 : f1 (u, v, a, c, s, (ν, ν')) = ∫ t, t / (s + a * t) ∂(ν : Measure ℝ) := by
    rw [hf1]
  have k2 : f2 (u, v, a, c, s, (ν, ν')) = ∫ t, t / (s + c * t) ∂(ν' : Measure ℝ) := by
    rw [hf2]
  have k3 : g (u, v, a, c, s, (ν, ν')) = F (s * u * v) := by
    rw [hg]
  have hRle : R (u, v, a, c, s, (ν, ν')) ≤ δ / 2 := by
    rw [hR]
    dsimp only
    rw [k1, k2, k3]
    linarith
  linarith

end Muon.DetEquiv

end

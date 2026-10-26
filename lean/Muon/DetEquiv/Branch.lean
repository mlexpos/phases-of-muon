import Muon.DetEquiv.Scalar
import Muon.Foundations.Conventions

/-!
# Appendix B: the branch of the scalar fixed-point system (task L-B.2)

Snapshot `cr-2026-10-23`. Source: `sections/02-deterministic-equivalents/section.tex`,
"The weighted fixed-point system" (l.116–208: `def:app-de-branch`, `eqn:app-de-class`,
`thm:app-de-branch`), `rem:app-de-nomomentum` (l.475–508, promoted by ruling L8) and
`prop:app-de-normalization` (l.510–534).

Representation choices (CARD §2, §3, §6 and ruling L2):

* The unknowns are `(σ, σ̃, s̃₁, s₁) : ℝ × ℝ × ℝ × ℝ`, in the paper's order. In `IsBranchSol`
  the pair `(a, c)` is `(s̃₁, s₁)`; `q := s σ σ̃` is a `let`. The system is written at `z = -s`
  with `s > 0`, so `x/(s̃₁ x - z)` is `x/(a x + s)`.
* The branch theorem is stated for an abstract weight function `F` with `AdmissibleWeightFn F`
  (ruling L2; CARD §2, §6.17). Its box is written with `F 0` in place of `∑ w_j²`.
  `thm_app_de_branch_i_weight` is the source statement for a weight sequence `w` (box with
  `sumPow w 2`), obtained from `Fw_admissible` and `Fw w 0 = sumPow w 2`.
* `classK Cs γ` is the class `𝒦` of `eqn:app-de-class` on `FiniteMeasure ℝ`; the mass
  condition is `ν([0,Cs]) ≤ γ` and the support condition is `ν([0,Cs]ᶜ) = 0`.
* `branchSol` is the total solution map (the solution given by (i) when it exists, `0`
  otherwise), so that `Rbar` and `Rtbar` are total (CARD §2, §3 row 2).
* `Rbar`, `Rtbar` take the covariance `C : Covariances m n` and the weight function `F` and the
  measures as arguments. The spectral measures of A are `Muon.nuOut C B` and `Muon.nuIn C B`
  (`Measure ℝ`); where a statement needs them, the hypothesis `(ν : Measure ℝ) = nuOut C B`
  connects them to the `FiniteMeasure` arguments.
* `leadW ϖ` is the weight `(ϖ, 0, 0, …)`; `leadW 1` is the unit weight, which is the no-momentum
  case `w = (1,0,…)` of the remark. `equalW K` is `w_j = 1/K` for `j < K`, and `0` otherwise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Matrix MatrixOrder

noncomputable section

namespace Muon.DetEquiv

/-! ## The class `𝒦` -/

/-- The class `𝒦` of `eqn:app-de-class`, snapshot `cr-2026-10-23`. LaTeX
(`sections/02-deterministic-equivalents/section.tex` l.159–162):
```
\begin{equation}\label{eqn:app-de-class}
\mathcal K\defeq\big\{(\nu,\tilde\nu):\ \nu,\tilde\nu\text{ finite positive Borel measures on }[0,C_\Sigma],\
\nu([0,C_\Sigma])\le\gamma_\star,\ \tilde\nu([0,C_\Sigma])\le\gamma_\star\big\}.
\end{equation}
```
Encoding: "finite positive Borel measures on `[0,Cs]`" is the support condition
`μ ([0,Cs]ᶜ) = 0` on `FiniteMeasure ℝ`; the mass bound is `μ ([0,Cs]) ≤ γ⋆` in `ℝ≥0∞`. -/
def classK (Cs γ : ℝ) : Set (FiniteMeasure ℝ × FiniteMeasure ℝ) :=
  {p | (p.1 : Measure ℝ) (Icc 0 Cs) ≤ ENNReal.ofReal γ ∧ (p.1 : Measure ℝ) (Icc 0 Cs)ᶜ = 0 ∧
    (p.2 : Measure ℝ) (Icc 0 Cs) ≤ ENNReal.ofReal γ ∧ (p.2 : Measure ℝ) (Icc 0 Cs)ᶜ = 0}

/-- The equal-weight sequence `w_j = 1/K` for `0 ≤ j < K`, `w_j = 0` otherwise
(`prop:app-de-normalization`(ii), `section.tex` l.512–513). -/
def equalW (K : ℕ) : ℕ → ℝ :=
  fun j => if j < K then (K : ℝ)⁻¹ else 0

/-- The single-weight sequence `(ϖ, 0, 0, …)` (`prop:app-de-normalization`(i), `section.tex`
l.511–512). `leadW 1` is the unit weight `(1, 0, 0, …)` of `rem:app-de-nomomentum`. -/
def leadW (ϖ : ℝ) : ℕ → ℝ :=
  fun j => if j = 0 then ϖ else 0

/-! ## The fixed-point system and its solution map -/

/-- The weighted fixed-point system at `z = -s` (`def:app-de-branch`, `eqn:app-de-system`),
snapshot `cr-2026-10-23`. LaTeX (`sections/02-deterministic-equivalents/section.tex` l.116–128):
```
\begin{definition}[Weighted fixed-point system]\label{def:app-de-branch}
Let $(\nu,\tilde\nu)$ be finite positive Borel measures on $[0,\infty)$ with
compact support, let $w$ be as above, and let $z=-s$ with $s>0$. The weighted
fixed-point system at $z$ is the system of equations in the four unknowns
$(\sigma,\tilde\sigma,\tilde s_1,s_1)\in[0,\infty)^4$
\begin{equation}\label{eqn:app-de-system}
\begin{aligned}
\sigma&=\int\frac{x}{\tilde s_1x-z}\,\nu(dx),\qquad&
\tilde\sigma&=\int\frac{x}{s_1x-z}\,\tilde\nu(dx),\\
q&=-z\,\sigma\tilde\sigma,\qquad&
\tilde s_1&=-z\,\tilde\sigma\,F_w(q),\qquad s_1=-z\,\sigma\,F_w(q).
\end{aligned}
\end{equation}
```
Encoding: the tuple is `(σ, σ̃, s̃₁, s₁) = (x.1, x.2.1, x.2.2.1, x.2.2.2)`; `F` is the weight
function (`F_w` for a weight sequence `w`); `q = s σ σ̃` is a `let`. The first two equations are
`σ = ∫ x/(s̃₁ x + s) dν`, `σ̃ = ∫ x/(s₁ x + s) dν̃`. The measures are on `[0,∞)` with compact
support in the source; the integrand is bounded on the support, so the integrals are the paper's. -/
def IsBranchSol (F : ℝ → ℝ) (ν ν' : FiniteMeasure ℝ) (s : ℝ) :
    ℝ × ℝ × ℝ × ℝ → Prop
  | (σ, σ', a, c) =>
    let q := s * σ * σ'
    0 ≤ σ ∧ 0 ≤ σ' ∧ 0 ≤ a ∧ 0 ≤ c ∧
      σ = ∫ t, t / (a * t + s) ∂(ν : Measure ℝ) ∧
      σ' = ∫ t, t / (c * t + s) ∂(ν' : Measure ℝ) ∧
      a = s * σ' * F q ∧ c = s * σ * F q

open scoped Classical in
/-- Total solution map `(σ, σ̃, s̃₁, s₁)(-s)` of `def:app-de-branch` (`section.tex` l.140–141,
"where $(\sigma,\tilde\sigma,\tilde s_1,s_1)(z)$ is the solution given by
\cref{thm:app-de-branch}"). It is `h.choose` when a solution exists and `0` otherwise, so that
it is a total function; `branchSol_spec` is the statement that it is the solution. -/
def branchSol (F : ℝ → ℝ) (ν ν' : FiniteMeasure ℝ) (s : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  if h : ∃ x, IsBranchSol F ν ν' s x then h.choose else 0

/-- `\overline R(z)` of `eqn:app-de-Rbar`, snapshot `cr-2026-10-23`. LaTeX
(`sections/02-deterministic-equivalents/section.tex` l.136–139):
```
\Rbar(z)\defeq\big(\tilde s_1(z)\,\Sigmaout-z\,\Id_{\Nout}\big)^{-1},
```
with `z = -s`, so `-z = s` and the matrix is `s • 1 + s̃₁ • Σ_out`. The solution `s̃₁` is the
third component of `branchSol`. -/
def Rbar {m n : ℕ} (F : ℝ → ℝ) (ν ν' : FiniteMeasure ℝ) (C : Covariances m n) (s : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  (s • (1 : Matrix (Fin m) (Fin m) ℝ) + (branchSol F ν ν' s).2.2.1 • C.Sout)⁻¹

/-- `\overline{\widetilde R}(z)` of `eqn:app-de-Rbar`, snapshot `cr-2026-10-23`. LaTeX
(`sections/02-deterministic-equivalents/section.tex` l.136–139):
```
\Rtbar(z)\defeq\big(s_1(z)\,\Sigmain-z\,\Id_{\Nin}\big)^{-1},
```
with `z = -s`; the matrix is `s • 1 + s₁ • Σ_in`, and `s₁` is the fourth component of `branchSol`. -/
def Rtbar {m n : ℕ} (F : ℝ → ℝ) (ν ν' : FiniteMeasure ℝ) (C : Covariances m n) (s : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (s • (1 : Matrix (Fin n) (Fin n) ℝ) + (branchSol F ν ν' s).2.2.2 • C.Sin)⁻¹

/-! ## The branch theorem -/

/-- Private helper (a priori bound): for a measure with mass `≤ γ` on `[0,Cs]` and no mass outside,
`∫ t/(a t + s) dν ≤ γ Cs / s` for `a ≥ 0`, `s > 0`. -/
private lemma branch_integral_le {Cs γ s a : ℝ} (hγ : 0 ≤ γ) (hCs : 0 ≤ Cs) (hs : 0 < s)
    (ha : 0 ≤ a) {ν : FiniteMeasure ℝ} (hmass : (ν : Measure ℝ) (Icc 0 Cs) ≤ ENNReal.ofReal γ)
    (hsupp : (ν : Measure ℝ) (Icc 0 Cs)ᶜ = 0) :
    ∫ t, t / (a * t + s) ∂(ν : Measure ℝ) ≤ γ * Cs / s := by
  set μ : Measure ℝ := (ν : Measure ℝ) with hμ
  have hmeas : MeasurableSet (Icc (0 : ℝ) Cs) := measurableSet_Icc
  have hae : ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) Cs := by
    rw [MeasureTheory.ae_iff]
    exact hsupp
  have hbound : ∀ᵐ t ∂μ, t / (a * t + s) ≤ Cs / s := by
    filter_upwards [hae] with t ht
    obtain ⟨h0, h1⟩ := ht
    have hpos : 0 < a * t + s := by nlinarith [mul_nonneg ha h0]
    rw [div_le_div_iff₀ hpos hs]
    nlinarith [mul_nonneg ha h0, mul_le_mul_of_nonneg_right h1 hs.le]
  have hnn : 0 ≤ᵐ[μ] fun t : ℝ => t / (a * t + s) := by
    filter_upwards [hae] with t ht
    obtain ⟨h0, _⟩ := ht
    exact div_nonneg h0 (by nlinarith [mul_nonneg ha h0])
  have huniv : μ univ ≤ ENNReal.ofReal γ := by
    have h := measure_add_measure_compl (μ := μ) hmeas
    rw [hsupp, add_zero] at h
    rw [← h]
    exact hmass
  have hreal : μ.real univ ≤ γ := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hγ huniv
  calc ∫ t, t / (a * t + s) ∂μ ≤ ∫ _t, Cs / s ∂μ :=
        integral_mono_of_nonneg hnn (integrable_const _) hbound
    _ = μ.real univ * (Cs / s) := by rw [integral_const, smul_eq_mul]
    _ ≤ γ * (Cs / s) := mul_le_mul_of_nonneg_right hreal (div_nonneg hCs hs.le)
    _ = γ * Cs / s := by ring

/-! ### Private helpers for the existence and uniqueness conjunct of `thm_app_de_branch_i` -/

private lemma bp_pt {Cs s x t : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (ht : t ∈ Icc 0 Cs) :
    0 ≤ t / (x * t + s) ∧ t / (x * t + s) ≤ Cs / s ∧ 0 < x * t + s := by
  obtain ⟨h0, h1⟩ := ht
  have hpos : 0 < x * t + s := by nlinarith [mul_nonneg hx h0]
  refine ⟨div_nonneg h0 hpos.le, ?_, hpos⟩
  rw [div_le_div_iff₀ hpos hs]
  nlinarith [mul_nonneg hx h0, mul_le_mul_of_nonneg_right h1 hs.le]

private lemma bp_ae {μ : Measure ℝ} {Cs : ℝ} (hsupp : μ (Icc 0 Cs)ᶜ = 0) :
    ∀ᵐ t ∂μ, t ∈ Icc (0:ℝ) Cs := by
  rw [MeasureTheory.ae_iff]; exact hsupp

private lemma bp_pos {μ : Measure ℝ} {f : ℝ → ℝ} (hf : Integrable f μ)
    (hnn : ∀ᵐ t ∂μ, 0 ≤ f t) (hpos : ∀ t, 0 < t → 0 < f t) (hμ : μ (Ioi 0) ≠ 0) :
    0 < ∫ t, f t ∂μ := by
  rw [integral_pos_iff_support_of_nonneg_ae hnn hf]
  exact lt_of_lt_of_le (pos_iff_ne_zero.2 hμ) (measure_mono (fun t ht => ne_of_gt (hpos t ht)))

private lemma bp_g_cont {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs s : ℝ} (hs : 0 < s)
    (hsupp : μ (Icc 0 Cs)ᶜ = 0) :
    ContinuousOn (fun x => ∫ t, t / (x * t + s) ∂μ) (Ici 0) := by
  refine continuousOn_of_dominated (bound := fun _ => Cs / s) ?_ ?_ (integrable_const _) ?_
  · intro x _
    exact (by fun_prop : Measurable fun t : ℝ => t / (x * t + s)).aestronglyMeasurable
  · intro x hx
    filter_upwards [bp_ae hsupp] with t ht
    obtain ⟨h0, h1, _⟩ := bp_pt (Cs := Cs) hs hx ht
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  · filter_upwards [bp_ae hsupp] with t ht
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx
    exact (bp_pt (Cs := Cs) hs hx ht).2.2.ne'


private lemma bp_int {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x)
    (hsupp : μ (Icc 0 Cs)ᶜ = 0) : Integrable (fun t => t / (x * t + s)) μ := by
  refine Integrable.mono' (integrable_const (Cs / s))
    (by fun_prop : Measurable fun t : ℝ => t / (x * t + s)).aestronglyMeasurable ?_
  filter_upwards [bp_ae hsupp] with t ht
  obtain ⟨h0, h1, _⟩ := bp_pt (Cs := Cs) hs hx ht
  rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1

private lemma bp_int' {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x)
    (hsupp : μ (Icc 0 Cs)ᶜ = 0) : Integrable (fun t => x * t / (x * t + s)) μ := by
  have := (bp_int (Cs := Cs) hs hx hsupp).const_mul x
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [mul_div_assoc]

private lemma bp_H_eq {μ : Measure ℝ} {s x : ℝ} :
    x * ∫ t, t / (x * t + s) ∂μ = ∫ t, x * t / (x * t + s) ∂μ := by
  rw [← integral_const_mul]
  simp only [mul_div_assoc]

private lemma bp_g_pos {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x)
    (hsupp : μ (Icc 0 Cs)ᶜ = 0) (hμ : μ (Ioi 0) ≠ 0) : 0 < ∫ t, t / (x * t + s) ∂μ := by
  refine bp_pos (bp_int hs hx hsupp) ?_ ?_ hμ
  · filter_upwards [bp_ae hsupp] with t ht
    exact (bp_pt (Cs := Cs) hs hx ht).1
  · intro t ht
    have : 0 < x * t + s := by nlinarith [mul_nonneg hx ht.le]
    exact div_pos ht this

private lemma bp_g_anti {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs s : ℝ} (hs : 0 < s)
    (hsupp : μ (Icc 0 Cs)ᶜ = 0) (hμ : μ (Ioi 0) ≠ 0) :
    StrictAntiOn (fun x => ∫ t, t / (x * t + s) ∂μ) (Ici 0) := by
  intro x hx y hy hxy
  simp only [mem_Ici] at hx hy
  show ∫ t, t / (y * t + s) ∂μ < ∫ t, t / (x * t + s) ∂μ
  rw [← sub_pos, ← integral_sub (bp_int hs hx hsupp) (bp_int hs hy hsupp)]
  refine bp_pos ((bp_int hs hx hsupp).sub (bp_int hs hy hsupp)) ?_ ?_ hμ
  · filter_upwards [bp_ae hsupp] with t ht
    have h0 := ht.1
    have h1 := bp_pt (Cs := Cs) hs hx ht
    have h2 := bp_pt (Cs := Cs) hs hy ht
    show 0 ≤ t / (x * t + s) - t / (y * t + s)
    rw [sub_nonneg]
    exact div_le_div_of_nonneg_left h0 h1.2.2 (by nlinarith [mul_nonneg h0 (sub_nonneg.2 hxy.le)])
  · intro t ht
    have h1 : 0 < x * t + s := by nlinarith [mul_nonneg hx ht.le]
    show 0 < t / (x * t + s) - t / (y * t + s)
    rw [sub_pos]
    exact div_lt_div_of_pos_left ht h1 (by nlinarith [mul_pos ht (sub_pos.2 hxy)])

private lemma bp_H_mono {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs s : ℝ} (hs : 0 < s)
    (hsupp : μ (Icc 0 Cs)ᶜ = 0) (hμ : μ (Ioi 0) ≠ 0) :
    StrictMonoOn (fun x => x * ∫ t, t / (x * t + s) ∂μ) (Ici 0) := by
  intro x hx y hy hxy
  simp only [mem_Ici] at hx hy
  show x * ∫ t, t / (x * t + s) ∂μ < y * ∫ t, t / (y * t + s) ∂μ
  rw [bp_H_eq, bp_H_eq, ← sub_pos, ← integral_sub (bp_int' (Cs := Cs) hs hy hsupp) (bp_int' (Cs := Cs) hs hx hsupp)]
  refine bp_pos ((bp_int' (Cs := Cs) hs hy hsupp).sub (bp_int' (Cs := Cs) hs hx hsupp)) ?_ ?_ hμ
  · filter_upwards [bp_ae hsupp] with t ht
    have h0 := ht.1
    have h1 := bp_pt (Cs := Cs) hs hx ht
    have h2 := bp_pt (Cs := Cs) hs hy ht
    show 0 ≤ y * t / (y * t + s) - x * t / (x * t + s)
    rw [sub_nonneg, div_le_div_iff₀ h1.2.2 h2.2.2]
    nlinarith [mul_nonneg h0 (sub_nonneg.2 hxy.le), mul_nonneg (mul_nonneg h0 (sub_nonneg.2 hxy.le)) hs.le]
  · intro t ht
    have h1 : 0 < x * t + s := by nlinarith [mul_nonneg hx ht.le]
    have h2 : 0 < y * t + s := by nlinarith [mul_nonneg hy ht.le]
    show 0 < y * t / (y * t + s) - x * t / (x * t + s)
    rw [sub_pos, div_lt_div_iff₀ h1 h2]
    nlinarith [mul_pos (mul_pos ht hs) (sub_pos.2 hxy)]

private lemma bp_H_le {μ : Measure ℝ} [IsFiniteMeasure μ] {Cs s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x)
    (hsupp : μ (Icc 0 Cs)ᶜ = 0) : x * ∫ t, t / (x * t + s) ∂μ ≤ μ.real univ := by
  rw [bp_H_eq]
  calc ∫ t, x * t / (x * t + s) ∂μ ≤ ∫ _t, (1:ℝ) ∂μ := by
        refine integral_mono_ae (bp_int' (Cs := Cs) hs hx hsupp) (integrable_const _) ?_
        filter_upwards [bp_ae hsupp] with t ht
        have h1 := bp_pt (Cs := Cs) hs hx ht
        show x * t / (x * t + s) ≤ 1
        rw [div_le_one h1.2.2]; linarith
    _ = μ.real univ := by simp


private lemma bp_inv {g : ℝ → ℝ} {B : ℝ} (hcont : ContinuousOn g (Ici 0))
    (hmono : StrictMonoOn (fun x => x * g x) (Ici 0))
    (hB : ∀ x, 0 ≤ x → x * g x ≤ B) :
    ∃ (P : ℝ) (X : ℝ → ℝ), 0 < P ∧ (∀ x, 0 ≤ x → x * g x < P) ∧
      (∀ ρ, ρ < P → ∃ x, 0 ≤ x ∧ ρ < x * g x) ∧
      (∀ ρ, 0 ≤ ρ → ρ < P → 0 ≤ X ρ ∧ X ρ * g (X ρ) = ρ) ∧
      (∀ x, 0 ≤ x → X (x * g x) = x) ∧ ContinuousOn X (Ioo 0 P) := by
  set S : Set ℝ := (fun x => x * g x) '' Ici 0 with hS
  have hbdd : BddAbove S := by
    refine ⟨B, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hB x hx
  have hne : S.Nonempty := ⟨0 * g 0, 0, mem_Ici.2 le_rfl, rfl⟩
  set P := sSup S with hP
  have hH0 : (0:ℝ) * g 0 = 0 := by ring
  have hlt : ∀ x, 0 ≤ x → x * g x < P := by
    intro x hx
    have h1 : x * g x < (x + 1) * g (x + 1) :=
      hmono (show x ∈ Ici (0:ℝ) from hx) (show x + 1 ∈ Ici (0:ℝ) by
        simp only [mem_Ici]; linarith) (by linarith)
    exact lt_of_lt_of_le h1 (le_csSup hbdd ⟨x + 1, by simp only [mem_Ici]; linarith, rfl⟩)
  have hPpos : 0 < P := by
    have := hlt 0 le_rfl
    rwa [hH0] at this
  have hsup : ∀ ρ, ρ < P → ∃ x, 0 ≤ x ∧ ρ < x * g x := by
    intro ρ hρ
    obtain ⟨_, ⟨x, hx, rfl⟩, h⟩ := exists_lt_of_lt_csSup hne hρ
    exact ⟨x, hx, h⟩
  have hHc : ContinuousOn (fun x => x * g x) (Ici 0) := continuousOn_id.mul hcont
  have hex : ∀ ρ, 0 ≤ ρ → ρ < P → ∃ x, 0 ≤ x ∧ x * g x = ρ := by
    intro ρ h0 hρ
    obtain ⟨x1, hx1, hlt1⟩ := hsup ρ hρ
    have := intermediate_value_Icc hx1 (hHc.mono (Icc_subset_Ici_self))
    rw [hH0] at this
    obtain ⟨x, hx, hxρ⟩ := this ⟨h0, hlt1.le⟩
    exact ⟨x, hx.1, hxρ⟩
  classical
  let X : ℝ → ℝ := fun ρ => if h : ∃ x, 0 ≤ x ∧ x * g x = ρ then h.choose else 0
  have hXspec : ∀ ρ, 0 ≤ ρ → ρ < P → 0 ≤ X ρ ∧ X ρ * g (X ρ) = ρ := by
    intro ρ h0 hρ
    have h := hex ρ h0 hρ
    simp only [X, dif_pos h]
    exact h.choose_spec
  have hXH : ∀ x, 0 ≤ x → X (x * g x) = x := by
    intro x hx
    have h : ∃ y, 0 ≤ y ∧ y * g y = x * g x := ⟨x, hx, rfl⟩
    have hs := h.choose_spec
    have : X (x * g x) = h.choose := by simp only [X, dif_pos h]
    rw [this]
    exact hmono.injOn (show h.choose ∈ Ici (0:ℝ) from hs.1) (show x ∈ Ici (0:ℝ) from hx) hs.2
  refine ⟨P, X, hPpos, hlt, hsup, hXspec, hXH, ?_⟩
  have hXmono : MonotoneOn X (Ioo 0 P) := by
    intro a ha b hb hab
    by_contra hcon
    push_neg at hcon
    have h1 := hXspec a ha.1.le ha.2
    have h2 := hXspec b hb.1.le hb.2
    have := hmono (show X b ∈ Ici (0:ℝ) from h2.1) (show X a ∈ Ici (0:ℝ) from h1.1) hcon
    simp only at this
    rw [h1.2, h2.2] at this
    linarith
  intro ρ0 hρ0
  refine ContinuousAt.continuousWithinAt ?_
  refine continuousAt_of_monotoneOn_of_image_mem_nhds hXmono (Ioo_mem_nhds hρ0.1 hρ0.2) ?_
  have hpos : 0 < X ρ0 := by
    have h := hXspec ρ0 hρ0.1.le hρ0.2
    rcases h.1.eq_or_lt with h0 | h0
    · exfalso
      have := h.2
      rw [← h0, hH0] at this
      linarith [hρ0.1]
    · exact h0
  refine mem_of_superset (Ioi_mem_nhds hpos) ?_
  intro x hx
  have hx' : (0:ℝ) < x := hx
  refine ⟨x * g x, ⟨?_, hlt x hx'.le⟩, hXH x hx'.le⟩
  have := hmono (mem_Ici.2 (le_refl (0:ℝ))) (show x ∈ Ici (0:ℝ) from hx'.le) hx'
  simp only at this
  rwa [hH0] at this


private lemma bp_Xmono {g X : ℝ → ℝ} {P : ℝ} (hgm : StrictMonoOn (fun x => x * g x) (Ici 0))
    (hXs : ∀ ρ, 0 ≤ ρ → ρ < P → 0 ≤ X ρ ∧ X ρ * g (X ρ) = ρ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < P) : X a < X b := by
  by_contra hcon
  have hcon' : X b ≤ X a := not_lt.1 hcon
  have h1 := hXs a ha (hab.trans hb)
  have h2 := hXs b (ha.trans hab.le) hb
  have := hgm.monotoneOn (show X b ∈ Ici (0:ℝ) from h2.1) (show X a ∈ Ici (0:ℝ) from h1.1) hcon'
  rw [h1.2, h2.2] at this
  linarith

private lemma bp_Xpos {g X : ℝ → ℝ} {P : ℝ}
    (hXs : ∀ ρ, 0 ≤ ρ → ρ < P → 0 ≤ X ρ ∧ X ρ * g (X ρ) = ρ) {ρ : ℝ} (h0 : 0 < ρ)
    (hP : ρ < P) : 0 < X ρ := by
  have h := hXs ρ h0.le hP
  rcases h.1.eq_or_lt with h' | h'
  · exfalso
    have := h.2
    rw [← h'] at this
    linarith
  · exact h'

private lemma bp_small {F : ℝ → ℝ} (hF : AdmissibleWeightFn F) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ q, 0 ≤ q → q ≤ δ → q * F q < ε := by
  have hc : ContinuousWithinAt (fun q => q * F q) (Ici 0) 0 :=
    (continuousOn_id.mul hF.contOn) 0 (mem_Ici.2 le_rfl)
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, h⟩ := hc ε hε
  refine ⟨δ / 2, by positivity, fun q hq hqd => ?_⟩
  have := h (show q ∈ Ici (0:ℝ) from hq) (by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hq]; linarith)
  have h0 : (0:ℝ) * F 0 = 0 := hF.r_zero
  change dist (q * F q) (0 * F 0) < ε at this
  rw [h0, Real.dist_eq, sub_zero] at this
  exact lt_of_le_of_lt (le_abs_self _) this


private lemma bp_hi {F : ℝ → ℝ} (hF : AdmissibleWeightFn F) {s : ℝ} (hs : 0 < s)
    {g g' X X' : ℝ → ℝ} {P P' : ℝ} (hPP : P ≤ P')
    (hgm : StrictMonoOn (fun x => x * g x) (Ici 0)) (hP : 0 < P)
    (hPlt : ∀ x, 0 ≤ x → x * g x < P) (hPsup : ∀ ρ, ρ < P → ∃ x, 0 ≤ x ∧ ρ < x * g x)
    (hXs : ∀ ρ, 0 ≤ ρ → ρ < P → 0 ≤ X ρ ∧ X ρ * g (X ρ) = ρ)
    (hXH : ∀ x, 0 ≤ x → X (x * g x) = x)
    (hgm' : StrictMonoOn (fun x => x * g' x) (Ici 0))
    (hXs' : ∀ ρ, 0 ≤ ρ → ρ < P' → 0 ≤ X' ρ ∧ X' ρ * g' (X' ρ) = ρ) :
    ∃ ρ, 0 < ρ ∧ ρ < P ∧
      (s * g (X ρ) * g' (X' ρ)) * F (s * g (X ρ) * g' (X' ρ)) < ρ := by
  have hP2 : 0 < P / 2 := by positivity
  have hP2lt : P / 2 < P := half_lt_self hP
  obtain ⟨δ, hδ, hsm⟩ := bp_small hF hP2
  have hx1 : 0 < X' (P / 2) := bp_Xpos hXs' hP2 (hP2lt.trans_le hPP)
  obtain ⟨xm, hxm0, hxm⟩ := hPsup (P / 2) hP2lt
  set Y : ℝ := s * P ^ 2 / (δ * X' (P / 2)) with hYdef
  have hY : 0 < Y := by positivity
  set xs : ℝ := max Y xm with hxsdef
  have hxs0 : 0 < xs := lt_max_of_lt_left hY
  set ρ : ℝ := xs * g xs with hρdef
  have hρlt : ρ < P := hPlt xs hxs0.le
  have hρgt : P / 2 < ρ := hxm.trans_le
    (hgm.monotoneOn (show xm ∈ Ici (0:ℝ) from hxm0) (show xs ∈ Ici (0:ℝ) from hxs0.le)
      (le_max_right _ _))
  have hXρ : X ρ = xs := hXH xs hxs0.le
  have hgx : g (X ρ) = ρ / xs := by
    rw [hXρ, hρdef]; field_simp
  have hc : X' (P / 2) < X' ρ := bp_Xmono hgm' hXs' hP2.le hρgt (hρlt.trans_le hPP)
  have hc0 : 0 < X' ρ := hx1.trans hc
  have hρ0 : 0 < ρ := hP2.trans hρgt
  have hgc : g' (X' ρ) = ρ / X' ρ := by
    have := (hXs' ρ hρ0.le (hρlt.trans_le hPP)).2
    field_simp
    linarith
  refine ⟨ρ, hρ0, hρlt, ?_⟩
  rw [hgx, hgc]
  have hq0 : 0 ≤ s * (ρ / xs) * (ρ / X' ρ) := by positivity
  have hqd : s * (ρ / xs) * (ρ / X' ρ) ≤ δ := by
    have e : s * (ρ / xs) * (ρ / X' ρ) = s * ρ ^ 2 / (xs * X' ρ) := by field_simp
    rw [e, div_le_iff₀ (mul_pos hxs0 hc0)]
    have h1 : Y ≤ xs := le_max_left _ _
    have h2 : xs * X' ρ ≥ Y * X' (P / 2) :=
      mul_le_mul h1 hc.le hx1.le hxs0.le
    have h3 : δ * (Y * X' (P / 2)) = s * P ^ 2 := by
      rw [hYdef]; field_simp
    have h4 : s * ρ ^ 2 ≤ s * P ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0.le hρlt.le 2) hs.le
    nlinarith [mul_le_mul_of_nonneg_left h2 hδ.le]
  exact (hsm _ hq0 hqd).trans hρgt


private lemma bp_cross {F : ℝ → ℝ} (hF : AdmissibleWeightFn F) {s : ℝ} (hs : 0 < s)
    {g g' X X' : ℝ → ℝ} {P P' : ℝ}
    (hgc : ContinuousOn g (Ici 0)) (hgp : ∀ x, 0 ≤ x → 0 < g x)
    (hga : StrictAntiOn g (Ici 0)) (hgm : StrictMonoOn (fun x => x * g x) (Ici 0))
    (hP : 0 < P) (hPlt : ∀ x, 0 ≤ x → x * g x < P)
    (hPsup : ∀ ρ, ρ < P → ∃ x, 0 ≤ x ∧ ρ < x * g x)
    (hXs : ∀ ρ, 0 ≤ ρ → ρ < P → 0 ≤ X ρ ∧ X ρ * g (X ρ) = ρ)
    (hXH : ∀ x, 0 ≤ x → X (x * g x) = x) (hXc : ContinuousOn X (Ioo 0 P))
    (hgc' : ContinuousOn g' (Ici 0)) (hgp' : ∀ x, 0 ≤ x → 0 < g' x)
    (hga' : StrictAntiOn g' (Ici 0)) (hgm' : StrictMonoOn (fun x => x * g' x) (Ici 0))
    (hP' : 0 < P') (hPlt' : ∀ x, 0 ≤ x → x * g' x < P')
    (hPsup' : ∀ ρ, ρ < P' → ∃ x, 0 ≤ x ∧ ρ < x * g' x)
    (hXs' : ∀ ρ, 0 ≤ ρ → ρ < P' → 0 ≤ X' ρ ∧ X' ρ * g' (X' ρ) = ρ)
    (hXH' : ∀ x, 0 ≤ x → X' (x * g' x) = x) (hXc' : ContinuousOn X' (Ioo 0 P')) :
    ∃! ρ, (0 < ρ ∧ ρ < min P P') ∧
      (s * g (X ρ) * g' (X' ρ)) * F (s * g (X ρ) * g' (X' ρ)) = ρ := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ → ℝ, ∀ ρ, q ρ = s * g (X ρ) * g' (X' ρ) := ⟨_, fun _ => rfl⟩
  simp only [← hq]
  set m := min P P' with hm
  have hm0 : 0 < m := lt_min hP hP'
  have hmP : m ≤ P := min_le_left _ _
  have hmP' : m ≤ P' := min_le_right _ _
  have hXnn : ∀ ρ ∈ Ioo 0 m, 0 ≤ X ρ := fun ρ hρ => (hXs ρ hρ.1.le (hρ.2.trans_le hmP)).1
  have hXnn' : ∀ ρ ∈ Ioo 0 m, 0 ≤ X' ρ := fun ρ hρ => (hXs' ρ hρ.1.le (hρ.2.trans_le hmP')).1
  have hqpos : ∀ ρ ∈ Ioo 0 m, 0 < q ρ := by
    intro ρ hρ
    rw [hq]
    exact mul_pos (mul_pos hs (hgp _ (hXnn ρ hρ))) (hgp' _ (hXnn' ρ hρ))
  have hqc : ContinuousOn q (Ioo 0 m) := by
    have e : q = fun ρ => s * g (X ρ) * g' (X' ρ) := funext hq
    rw [e]
    have h1 : ContinuousOn (fun ρ => g (X ρ)) (Ioo 0 m) :=
      hgc.comp (hXc.mono (Ioo_subset_Ioo le_rfl hmP)) (fun ρ hρ => hXnn ρ hρ)
    have h2 : ContinuousOn (fun ρ => g' (X' ρ)) (Ioo 0 m) :=
      hgc'.comp (hXc'.mono (Ioo_subset_Ioo le_rfl hmP')) (fun ρ hρ => hXnn' ρ hρ)
    exact (continuousOn_const.mul h1).mul h2
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℝ → ℝ, ∀ ρ, Γ ρ = q ρ * F (q ρ) - ρ := ⟨_, fun _ => rfl⟩
  have hΓc : ContinuousOn Γ (Ioo 0 m) := by
    have e : Γ = fun ρ => q ρ * F (q ρ) - ρ := funext hΓ
    rw [e]
    exact (hqc.mul (hF.contOn.comp hqc (fun ρ hρ => (hqpos ρ hρ).le))).sub continuousOn_id
  -- strict anti
  have hΓa : StrictAntiOn Γ (Ioo 0 m) := by
    intro a ha b hb hab
    have hXab : X a < X b := bp_Xmono hgm hXs ha.1.le hab (hb.2.trans_le hmP)
    have hXab' : X' a < X' b := bp_Xmono hgm' hXs' ha.1.le hab (hb.2.trans_le hmP')
    have hg1 : g (X b) < g (X a) := hga (mem_Ici.2 (hXnn a ha)) (mem_Ici.2 (hXnn b hb)) hXab
    have hg2 : g' (X' b) < g' (X' a) := hga' (mem_Ici.2 (hXnn' a ha)) (mem_Ici.2 (hXnn' b hb)) hXab'
    have hqab : q b < q a := by
      rw [hq, hq]
      have := hgp (X b) (hXnn b hb)
      have := hgp' (X' b) (hXnn' b hb)
      have h3 : g (X b) * g' (X' b) < g (X a) * g' (X' a) :=
        mul_lt_mul'' hg1 hg2 (hgp _ (hXnn b hb)).le (hgp' _ (hXnn' b hb)).le
      calc s * g (X b) * g' (X' b) = s * (g (X b) * g' (X' b)) := by ring
        _ < s * (g (X a) * g' (X' a)) := mul_lt_mul_of_pos_left h3 hs
        _ = s * g (X a) * g' (X' a) := by ring
    have hr := hF.r_strictMonoOn (show q b ∈ Ici (0:ℝ) from (hqpos b hb).le)
      (show q a ∈ Ici (0:ℝ) from (hqpos a ha).le) hqab
    simp only at hr
    rw [hΓ, hΓ]
    linarith
  -- low end
  have hlo : ∃ ρ ∈ Ioo 0 m, 0 < Γ ρ := by
    have hg1 := hgp 1 zero_le_one
    have hg1' := hgp' 1 zero_le_one
    set q0 := s * g 1 * g' 1 with hq0
    have hq0p : 0 < q0 := by positivity
    set r0 := q0 * F q0 with hr0
    have hr0p : 0 < r0 := mul_pos hq0p (hF.pos _ hq0p.le)
    set ρ := min (min (r0 / 2) (g 1 / 2)) (min (g' 1 / 2) (m / 2)) with hρ
    have hρ0 : 0 < ρ := by positivity
    have hρ1 : ρ ≤ r0 / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have hρ2 : ρ ≤ g 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hρ3 : ρ ≤ g' 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hρ4 : ρ ≤ m / 2 := (min_le_right _ _).trans (min_le_right _ _)
    have hρm : ρ ∈ Ioo 0 m := ⟨hρ0, by linarith⟩
    have hX1 : X ρ ≤ 1 := by
      have h1 : ρ < 1 * g 1 := by linarith
      have h2 : X ρ < X (1 * g 1) :=
        bp_Xmono hgm hXs hρ0.le h1 (hPlt 1 zero_le_one)
      rw [hXH 1 zero_le_one] at h2
      exact h2.le
    have hX1' : X' ρ ≤ 1 := by
      have h1 : ρ < 1 * g' 1 := by linarith
      have h2 : X' ρ < X' (1 * g' 1) :=
        bp_Xmono hgm' hXs' hρ0.le h1 (hPlt' 1 zero_le_one)
      rw [hXH' 1 zero_le_one] at h2
      exact h2.le
    have hga1 : g 1 ≤ g (X ρ) :=
      hga.antitoneOn (mem_Ici.2 (hXnn ρ hρm)) (mem_Ici.2 zero_le_one) hX1
    have hga1' : g' 1 ≤ g' (X' ρ) :=
      hga'.antitoneOn (mem_Ici.2 (hXnn' ρ hρm)) (mem_Ici.2 zero_le_one) hX1'
    have hqge : q0 ≤ q ρ := by
      rw [hq, hq0]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hga1 hs.le) hga1' hg1'.le
        (mul_nonneg hs.le (hgp _ (hXnn ρ hρm)).le)
    have hrge : r0 ≤ q ρ * F (q ρ) :=
      (hF.r_strictMonoOn.monotoneOn (show q0 ∈ Ici (0:ℝ) from hq0p.le)
        (show q ρ ∈ Ici (0:ℝ) from (hqpos ρ hρm).le) hqge)
    refine ⟨ρ, hρm, ?_⟩
    rw [hΓ]
    linarith
  -- high end
  have hhi : ∃ ρ ∈ Ioo 0 m, Γ ρ < 0 := by
    rcases le_total P P' with hPP | hPP
    · obtain ⟨ρ, h0, h1, h2⟩ := bp_hi hF hs hPP hgm hP hPlt hPsup hXs hXH hgm' hXs'
      refine ⟨ρ, ⟨h0, ?_⟩, ?_⟩
      · rw [hm, min_eq_left hPP]; exact h1
      · rw [hΓ, hq]; linarith
    · obtain ⟨ρ, h0, h1, h2⟩ := bp_hi hF hs hPP hgm' hP' hPlt' hPsup' hXs' hXH' hgm hXs
      refine ⟨ρ, ⟨h0, ?_⟩, ?_⟩
      · rw [hm, min_eq_right hPP]; exact h1
      · rw [hΓ, hq]
        have e : s * g (X ρ) * g' (X' ρ) = s * g' (X' ρ) * g (X ρ) := by ring
        rw [e]; linarith
  obtain ⟨a, ha, hΓa0⟩ := hlo
  obtain ⟨b, hb, hΓb0⟩ := hhi
  have hsub : uIcc a b ⊆ Ioo 0 m := (Set.ordConnected_Ioo).uIcc_subset ha hb
  have hivt := intermediate_value_uIcc (hΓc.mono hsub)
  have h0mem : (0:ℝ) ∈ uIcc (Γ a) (Γ b) := mem_uIcc.2 (Or.inr ⟨hΓb0.le, hΓa0.le⟩)
  obtain ⟨ρ, hρ, hρ0⟩ := hivt h0mem
  have hρm : ρ ∈ Ioo 0 m := hsub hρ
  refine ⟨ρ, ⟨hρm, ?_⟩, ?_⟩
  · rw [hΓ] at hρ0
    linarith
  · rintro y ⟨hy, hye⟩
    have hyz : Γ y = 0 := by rw [hΓ]; linarith
    rcases lt_trichotomy y ρ with h | h | h
    · have := hΓa hy hρm h
      rw [hyz, hρ0] at this; exact absurd this (lt_irrefl _)
    · exact h
    · have := hΓa hρm hy h
      rw [hyz, hρ0] at this; exact absurd this (lt_irrefl _)


private lemma bp_main {F : ℝ → ℝ} (hF : AdmissibleWeightFn F) {Cs s : ℝ} (hs : 0 < s)
    {ν ν' : FiniteMeasure ℝ} (hsupp : (ν : Measure ℝ) (Icc 0 Cs)ᶜ = 0)
    (hsupp' : (ν' : Measure ℝ) (Icc 0 Cs)ᶜ = 0)
    (hμ : (ν : Measure ℝ) (Ioi 0) ≠ 0) (hμ' : (ν' : Measure ℝ) (Ioi 0) ≠ 0) :
    ∃! x, IsBranchSol F ν ν' s x := by
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun x => ∫ t, t / (x * t + s) ∂(ν : Measure ℝ) := ⟨_, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g' : ℝ → ℝ, g' = fun x => ∫ t, t / (x * t + s) ∂(ν' : Measure ℝ) :=
    ⟨_, rfl⟩
  have hgc : ContinuousOn g (Ici 0) := by rw [hg]; exact bp_g_cont hs hsupp
  have hgc' : ContinuousOn g' (Ici 0) := by rw [hg']; exact bp_g_cont hs hsupp'
  have hgp : ∀ x, 0 ≤ x → 0 < g x := by
    intro x hx; rw [hg]; exact bp_g_pos hs hx hsupp hμ
  have hgp' : ∀ x, 0 ≤ x → 0 < g' x := by
    intro x hx; rw [hg']; exact bp_g_pos hs hx hsupp' hμ'
  have hga : StrictAntiOn g (Ici 0) := by rw [hg]; exact bp_g_anti hs hsupp hμ
  have hga' : StrictAntiOn g' (Ici 0) := by rw [hg']; exact bp_g_anti hs hsupp' hμ'
  have hgm : StrictMonoOn (fun x => x * g x) (Ici 0) := by rw [hg]; exact bp_H_mono hs hsupp hμ
  have hgm' : StrictMonoOn (fun x => x * g' x) (Ici 0) := by
    rw [hg']; exact bp_H_mono hs hsupp' hμ'
  have hB : ∀ x, 0 ≤ x → x * g x ≤ (ν : Measure ℝ).real univ := by
    intro x hx; rw [hg]; exact bp_H_le hs hx hsupp
  have hB' : ∀ x, 0 ≤ x → x * g' x ≤ (ν' : Measure ℝ).real univ := by
    intro x hx; rw [hg']; exact bp_H_le hs hx hsupp'
  obtain ⟨P, X, hP, hPlt, hPsup, hXs, hXH, hXc⟩ := bp_inv hgc hgm hB
  obtain ⟨P', X', hP', hPlt', hPsup', hXs', hXH', hXc'⟩ := bp_inv hgc' hgm' hB'
  obtain ⟨ρ, ⟨hρm, hρe⟩, huniq⟩ := bp_cross hF hs hgc hgp hga hgm hP hPlt hPsup hXs hXH hXc
    hgc' hgp' hga' hgm' hP' hPlt' hPsup' hXs' hXH' hXc'
  have hρP : ρ < P := hρm.2.trans_le (min_le_left _ _)
  have hρP' : ρ < P' := hρm.2.trans_le (min_le_right _ _)
  obtain ⟨hX0, hXe⟩ := hXs ρ hρm.1.le hρP
  obtain ⟨hX0', hXe'⟩ := hXs' ρ hρm.1.le hρP'
  have hgX := hgp _ hX0
  have hgX' := hgp' _ hX0'
  refine ⟨(g (X ρ), g' (X' ρ), X ρ, X' ρ), ?_, ?_⟩
  · refine ⟨hgX.le, hgX'.le, hX0, hX0', ?_, ?_, ?_, ?_⟩
    · rw [hg]
    · rw [hg']
    · apply mul_left_cancel₀ hgX.ne'
      calc g (X ρ) * X ρ = ρ := by rw [mul_comm]; exact hXe
        _ = _ := by linear_combination hρe.symm
    · apply mul_left_cancel₀ hgX'.ne'
      calc g' (X' ρ) * X' ρ = ρ := by rw [mul_comm]; exact hXe'
        _ = _ := by linear_combination hρe.symm
  · rintro ⟨σ, σ', a, c⟩ hy
    obtain ⟨hσ0, hσ'0, ha0, hc0, hσ, hσ', ha, hc⟩ := hy
    have hσg : σ = g a := by rw [hg]; exact hσ
    have hσg' : σ' = g' c := by rw [hg']; exact hσ'
    have hσp : 0 < σ := by rw [hσg]; exact hgp a ha0
    have hσp' : 0 < σ' := by rw [hσg']; exact hgp' c hc0
    have hq0 : 0 < s * σ * σ' := by positivity
    have hFq := hF.pos _ hq0.le
    have hρy1 : a * σ = (s * σ * σ') * F (s * σ * σ') := by rw [ha]; ring
    have hρy2 : c * σ' = (s * σ * σ') * F (s * σ * σ') := by rw [hc]; ring
    have hapos : 0 < a := by rw [ha]; positivity
    have hcpos : 0 < c := by rw [hc]; positivity
    have hHa : a * g a = a * σ := by rw [hσg]
    have hHc : c * g' c = c * σ' := by rw [hσg']
    have hXa : X (a * g a) = a := hXH a ha0
    have hXc2 : X' (c * g' c) = c := hXH' c hc0
    have hρeq : a * g a = c * g' c := by rw [hHa, hHc, hρy1, hρy2]
    have hρy0 : 0 < a * g a := mul_pos hapos (hgp a ha0)
    have h1 := huniq (a * g a) ⟨⟨hρy0, lt_min (hPlt a ha0) (by rw [hρeq]; exact hPlt' c hc0)⟩, ?_⟩
    · have hXa' : X (a * g a) = a := hXa
      have hXc' : X' (a * g a) = c := by rw [hρeq]; exact hXc2
      rw [h1] at hXa' hXc'
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext hXa'.symm hXc'.symm))
      · show σ = g (X ρ)
        rw [hXa', hσg]
      · show σ' = g' (X' ρ)
        rw [hXc', hσg']
    · have hXa' : X (a * g a) = a := hXa
      have hXc' : X' (a * g a) = c := by rw [hρeq]; exact hXc2
      rw [hXa', hXc', ← hσg, ← hσg']
      exact hρy1.symm

private lemma bp_zero {μ : Measure ℝ} {Cs s : ℝ} (hsupp : μ (Icc 0 Cs)ᶜ = 0)
    (h0 : μ (Ioi 0) = 0) (a : ℝ) : ∫ t, t / (a * t + s) ∂μ = 0 := by
  have h1 : ∀ᵐ t ∂μ, t ∉ Ioi (0:ℝ) := by
    rw [ae_iff]
    rwa [show {a | ¬ a ∉ Ioi (0:ℝ)} = Ioi 0 by ext; simp]
  apply integral_eq_zero_of_ae
  filter_upwards [bp_ae hsupp, h1] with t ht ht'
  have : t = 0 := le_antisymm (not_lt.1 ht') ht.1
  simp [this]

private lemma bp_deg {F : ℝ → ℝ} (hF : AdmissibleWeightFn F) {Cs s : ℝ} (hs : 0 < s)
    {ν ν' : FiniteMeasure ℝ} (hsupp : (ν : Measure ℝ) (Icc 0 Cs)ᶜ = 0)
    (hsupp' : (ν' : Measure ℝ) (Icc 0 Cs)ᶜ = 0) (h0 : (ν : Measure ℝ) (Ioi 0) = 0) :
    ∃! x, IsBranchSol F ν ν' s x := by
  have hF0 : 0 < F 0 := hF.pos 0 le_rfl
  have hz := bp_zero (s := s) hsupp h0
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∫ t, t / (0 * t + s) ∂(ν' : Measure ℝ) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hS]
    refine integral_nonneg_of_ae ?_
    filter_upwards [bp_ae hsupp'] with t ht
    exact (bp_pt (Cs := Cs) hs le_rfl ht).1
  refine ⟨(0, S, s * S * F 0, 0), ?_, ?_⟩
  · refine ⟨le_rfl, hS0, by positivity, le_rfl, ?_, ?_, ?_, ?_⟩
    · exact (hz _).symm
    · exact hS
    · simp
    · simp
  · rintro ⟨σ, σ', a, c⟩ hy
    obtain ⟨hσ0, hσ'0, ha0, hc0, hσ, hσ', ha, hc⟩ := hy
    have hσz : σ = 0 := by rw [hσ]; exact hz a
    have hcz : c = 0 := by rw [hc, hσz]; ring
    have hσS : σ' = S := by rw [hσ', hcz, hS]
    have haS : a = s * S * F 0 := by
      rw [ha, hσS, hσz]; simp
    rw [hσz, hσS, haS, hcz]

private lemma bp_swap {F : ℝ → ℝ} {s : ℝ} {ν ν' : FiniteMeasure ℝ} {σ σ' a c : ℝ} :
    IsBranchSol F ν ν' s (σ, σ', a, c) ↔ IsBranchSol F ν' ν s (σ', σ, c, a) := by
  simp only [IsBranchSol]
  have e : s * σ' * σ = s * σ * σ' := by ring
  rw [e]
  tauto

private lemma bp_exu {F : ℝ → ℝ} (hF : AdmissibleWeightFn F) {Cs s : ℝ} (hs : 0 < s)
    {ν ν' : FiniteMeasure ℝ} (hsupp : (ν : Measure ℝ) (Icc 0 Cs)ᶜ = 0)
    (hsupp' : (ν' : Measure ℝ) (Icc 0 Cs)ᶜ = 0) : ∃! x, IsBranchSol F ν ν' s x := by
  by_cases h : (ν : Measure ℝ) (Ioi 0) = 0
  · exact bp_deg hF hs hsupp hsupp' h
  by_cases h' : (ν' : Measure ℝ) (Ioi 0) = 0
  · obtain ⟨⟨σ, σ', a, c⟩, hy, hu⟩ := bp_deg hF hs hsupp' hsupp h'
    refine ⟨(σ', σ, c, a), bp_swap.1 hy, ?_⟩
    · rintro ⟨x1, x2, x3, x4⟩ hx
      have := hu (x2, x1, x4, x3) (bp_swap.1 hx)
      simp only [Prod.mk.injEq] at this ⊢
      tauto
  · exact bp_main hF hs hsupp hsupp' h h'

/-- `thm:app-de-branch`(i) with an abstract weight function `F` (ruling L2; CARD §2, §6.17),
snapshot `cr-2026-10-23`. LaTeX (`sections/02-deterministic-equivalents/section.tex`
l.164–176, part (i) and the display `eqn:app-de-box`):
```
\begin{theorem}[The weighted branch]\label{thm:app-de-branch}
Let $w$ be nonnegative, summable and not all zero, and let $C_\Sigma,\gamma_\star>0$.
\begin{enumerate}[label=(\roman*)]
\item (Existence and uniqueness.) For every $(\nu,\tilde\nu)\in\mathcal K$ and
every $s>0$ the system \cref{eqn:app-de-system} at $z=-s$ has exactly one
solution in $[0,\infty)^4$. It satisfies
\begin{equation}\label{eqn:app-de-box}
\sigma,\tilde\sigma\le\frac{\gamma_\star C_\Sigma}{s},\qquad
\tilde s_1,s_1\le\gamma_\star C_\Sigma\,\sw2,\qquad q\le\frac{(\gamma_\star C_\Sigma)^2}{s}.
\end{equation}
```
Encoding: `F` is abstract with `AdmissibleWeightFn F`; `w` enters only through `F`. The box
constant `∑_j w_j²` is `F 0` here; for `F = Fw w` it is `sumPow w 2` (`thm_app_de_branch_i_weight`).
The unknown in the box is the unique solution, stated as "every solution in `[0,∞)⁴` satisfies
the box" together with existence and uniqueness. -/
theorem thm_app_de_branch_i {F : ℝ → ℝ} (hF : AdmissibleWeightFn F) {Cs γ : ℝ}
    (hC : 0 < Cs) (hγ : 0 < γ) :
    ∀ ν ν' : FiniteMeasure ℝ, (ν, ν') ∈ classK Cs γ → ∀ s : ℝ, 0 < s →
      (∃! x, IsBranchSol F ν ν' s x) ∧
      ∀ x, IsBranchSol F ν ν' s x →
        x.1 ≤ γ * Cs / s ∧ x.2.1 ≤ γ * Cs / s ∧
        x.2.2.1 ≤ γ * Cs * F 0 ∧ x.2.2.2 ≤ γ * Cs * F 0 ∧
        s * x.1 * x.2.1 ≤ (γ * Cs) ^ 2 / s := by
  intro ν ν' hp s hs
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨?_, ?_⟩
  · exact bp_exu hF hs h2 h4
  · rintro ⟨σ, σ', a, c⟩ hx
    obtain ⟨hσ0, hσ'0, ha0, hc0, hσ, hσ', ha, hc⟩ := hx
    dsimp only at hσ0 hσ'0 ha0 hc0 hσ hσ' ha hc ⊢
    have hK1 : σ ≤ γ * Cs / s := by
      rw [hσ]; exact branch_integral_le hγ.le hC.le hs ha0 h1 h2
    have hK2 : σ' ≤ γ * Cs / s := by
      rw [hσ']; exact branch_integral_le hγ.le hC.le hs hc0 h3 h4
    have hq0 : 0 ≤ s * σ * σ' := by positivity
    have hF0 : 0 ≤ F 0 := (hF.pos 0 le_rfl).le
    have hFq : F (s * σ * σ') ≤ F 0 := hF.le_zero _ hq0
    have hK0 : 0 ≤ γ * Cs / s := by positivity
    refine ⟨hK1, hK2, ?_, ?_, ?_⟩
    · rw [ha]
      calc s * σ' * F (s * σ * σ') ≤ s * σ' * F 0 :=
            mul_le_mul_of_nonneg_left hFq (by positivity)
        _ ≤ s * (γ * Cs / s) * F 0 := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hK2 hs.le) hF0
        _ = γ * Cs * F 0 := by field_simp
    · rw [hc]
      calc s * σ * F (s * σ * σ') ≤ s * σ * F 0 :=
            mul_le_mul_of_nonneg_left hFq (by positivity)
        _ ≤ s * (γ * Cs / s) * F 0 := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hK1 hs.le) hF0
        _ = γ * Cs * F 0 := by field_simp
    · have hmm : σ * σ' ≤ γ * Cs / s * (γ * Cs / s) := mul_le_mul hK1 hK2 hσ'0 hK0
      calc s * σ * σ' = s * (σ * σ') := by ring
        _ ≤ s * (γ * Cs / s * (γ * Cs / s)) := mul_le_mul_of_nonneg_left hmm hs.le
        _ = (γ * Cs) ^ 2 / s := by field_simp

/-- `thm:app-de-branch`(i) for a weight sequence `w` (the source statement with
`w` nonnegative, summable and not all zero, and the box with `sw2 = ∑_j w_j²`), snapshot
`cr-2026-10-23`. LaTeX (`sections/02-deterministic-equivalents/section.tex` l.164–176, as in
`thm_app_de_branch_i`; the box constant is `\sw2`, so the bound on `\tilde s_1, s_1` reads
`\gamma_\star C_\Sigma\,\sw2`). Obtained from `thm_app_de_branch_i` with `F = Fw w`, using
`Fw_admissible` and `Fw w 0 = sumPow w 2`. -/
theorem thm_app_de_branch_i_weight {w : ℕ → ℝ} (hw : WeightSeq w) {Cs γ : ℝ}
    (hC : 0 < Cs) (hγ : 0 < γ) :
    ∀ ν ν' : FiniteMeasure ℝ, (ν, ν') ∈ classK Cs γ → ∀ s : ℝ, 0 < s →
      (∃! x, IsBranchSol (Fw w) ν ν' s x) ∧
      ∀ x, IsBranchSol (Fw w) ν ν' s x →
        x.1 ≤ γ * Cs / s ∧ x.2.1 ≤ γ * Cs / s ∧
        x.2.2.1 ≤ γ * Cs * sumPow w 2 ∧ x.2.2.2 ≤ γ * Cs * sumPow w 2 ∧
        s * x.1 * x.2.1 ≤ (γ * Cs) ^ 2 / s := by
  intro ν ν' hp s hs
  obtain ⟨h1, h2⟩ := thm_app_de_branch_i (Fw_admissible hw) hC hγ ν ν' hp s hs
  have h0 : Fw w 0 = sumPow w 2 := (lem_app_de_scalar_ii hw).2.2.2.2.2.2.1
  refine ⟨h1, fun x hx => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := h2 x hx
  refine ⟨a1, a2, ?_, ?_, a5⟩
  · rw [← h0]; exact a3
  · rw [← h0]; exact a4

/-- Helper: `branchSol` is the unique solution of the system whenever one exists, that is, under
the hypotheses of `thm_app_de_branch_i`. Source: the definition's sentence "where
`(σ,σ̃,s̃₁,s₁)(z)` is the solution given by thm (i)". -/
theorem branchSol_spec {F : ℝ → ℝ} (hF : AdmissibleWeightFn F) {Cs γ : ℝ}
    (hC : 0 < Cs) (hγ : 0 < γ) {ν ν' : FiniteMeasure ℝ} (hp : (ν, ν') ∈ classK Cs γ)
    {s : ℝ} (hs : 0 < s) :
    IsBranchSol F ν ν' s (branchSol F ν ν' s) := by
  have h := (thm_app_de_branch_i hF hC hγ ν ν' hp s hs).1.exists
  unfold branchSol
  rw [dif_pos h]
  exact h.choose_spec

/-! ## The promoted no-momentum dictionary -/

/-- `rem:app-de-nomomentum`(a), promoted by ruling L8, snapshot `cr-2026-10-23`. LaTeX
(`sections/02-deterministic-equivalents/section.tex` l.475–478 and l.480–482):
```
\begin{remark}[Dictionary to the no-momentum system]\label{rem:app-de-nomomentum}
At $\bmom=0$, with $z=-s$, the system \cref{eqn:app-de-system} for the
spectral measures \cref{eqn:app-setup-spectral-measures} is
```
Claim (a): at `w = (1, 0, …)` one has `F_w = L_w = J` (the no-momentum weight; the remark's
"$\bmom=0$" is `w = (1,0,…)`, `section.tex` l.475–478 and `eqn:app-de-JFL`). -/
theorem rem_app_de_nomomentum_a :
    ∀ q ∈ Ici (0 : ℝ), Fw (leadW 1) q = J q ∧ Lw (leadW 1) q = J q := by
  intro q _
  constructor
  · unfold Fw
    rw [tsum_eq_single 0]
    · simp [leadW]
    · intro j hj
      simp [leadW, hj]
  · unfold Lw
    rw [tsum_eq_single 0]
    · simp [leadW]
    · intro j hj
      simp [leadW, hj]

/-- Private helper: at `w = (1, 0, …)` the weighted function is `J` (claim (a), pointwise). -/
private lemma bp_fw_lead1 (q : ℝ) : Fw (leadW 1) q = J q := by
  unfold Fw
  rw [tsum_eq_single 0]
  · simp [leadW]
  · intro j hj
    simp [leadW, hj]

/-- Private helper: `(1, 0, …)` is a weight sequence, so `Fw (leadW 1)` is admissible. -/
private lemma bp_adm1 : AdmissibleWeightFn (Fw (leadW 1)) := by
  have hw : WeightSeq (leadW 1) := by
    unfold WeightSeq
    refine ⟨fun j => ?_, ?_, ⟨0, by simp [leadW]⟩⟩
    · unfold leadW
      split_ifs <;> norm_num
    · exact (hasSum_ite_eq 0 (1 : ℝ)).summable
  exact Fw_admissible hw

/-- Private helper: integral against `nuOut` as a finite sum over the eigenvalues of `Σ_out`. -/
private lemma bp_int_nuOut {m n B : ℕ} (C : Covariances m n) (g : ℝ → ℝ) :
    ∫ x, g x ∂(nuOut C B) =
      (B : ℝ)⁻¹ * ∑ i, g (C.psdOut.isHermitian.eigenvalues i) := by
  unfold nuOut
  rw [integral_smul_measure, integral_finsetSum_measure (fun i _ => integrable_dirac (by simp)),
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp only [integral_dirac, smul_eq_mul]

/-- Private helper: the algebra of the solution `(σ, σ̃, s̃₁, s₁)` at `w = (1,0,…)`: `s̃₁ σ = q J(q)`
and `s₁ σ̃ = q J(q)` with `q = s σ σ̃`. -/
private lemma bp_b_of_sol {F : ℝ → ℝ} (hF : ∀ q, F q = J q) {ν ν' : FiniteMeasure ℝ} {s : ℝ}
    (x : ℝ × ℝ × ℝ × ℝ) (hx : IsBranchSol F ν ν' s x) :
    x.2.2.1 * x.1 = (s * x.1 * x.2.1) * J (s * x.1 * x.2.1) ∧
      x.2.2.2 * x.2.1 = (s * x.1 * x.2.1) * J (s * x.1 * x.2.1) := by
  obtain ⟨σ, σ', a, c⟩ := x
  obtain ⟨-, -, -, -, -, -, ha, hc⟩ := hx
  dsimp only at ha hc ⊢
  rw [hF] at ha hc
  constructor
  · rw [ha]; ring
  · rw [hc]; ring

/-- Private helper: trace identity for the solution at `w = (1,0,…)`, with `ν = ν_out`. -/
private lemma bp_c_of_sol {m n B : ℕ} (C : Covariances m n) (hB : 0 < B)
    {F : ℝ → ℝ} {ν ν' : FiniteMeasure ℝ} (hν : (ν : Measure ℝ) = nuOut C B) {s : ℝ} (hs : 0 < s)
    (x : ℝ × ℝ × ℝ × ℝ) (hx : IsBranchSol F ν ν' s x) :
    x.2.2.1 * x.1 - (m : ℝ) / (B : ℝ) =
      -s * ((B : ℝ)⁻¹ * (s • (1 : Matrix (Fin m) (Fin m) ℝ) + x.2.2.1 • C.Sout)⁻¹.trace) := by
  classical
  obtain ⟨σ, σ', a, c⟩ := x
  obtain ⟨-, -, ha0, -, hσ, -, -, -⟩ := hx
  dsimp only at ha0 hσ ⊢
  rw [hν] at hσ
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hH : IsSelfAdjoint C.Sout := C.psdOut.isHermitian
  have hspec : spectrum ℝ C.Sout ⊆ {t : ℝ | 0 ≤ t} :=
    (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.1 C.psdOut).2
  have key : ∀ i, a * (C.psdOut.isHermitian.eigenvalues i / (a * C.psdOut.isHermitian.eigenvalues i + s))
      = 1 - s * (a * C.psdOut.isHermitian.eigenvalues i + s)⁻¹ := by
    intro i
    have hl : 0 ≤ C.psdOut.isHermitian.eigenvalues i := C.psdOut.eigenvalues_nonneg i
    have h0 : 0 < a * C.psdOut.isHermitian.eigenvalues i + s := by
      have := mul_nonneg ha0 hl
      linarith
    field_simp
    ring
  have h1 : σ = (B : ℝ)⁻¹ * ∑ i, C.psdOut.isHermitian.eigenvalues i /
      (a * C.psdOut.isHermitian.eigenvalues i + s) := by
    rw [hσ, bp_int_nuOut C]
  have hcfc : cfc (fun t => (a * t + s)⁻¹) C.Sout =
      (s • (1 : Matrix (Fin m) (Fin m) ℝ) + a • C.Sout)⁻¹ := by
    have hadd : cfc (fun t => a * t + s) C.Sout = s • (1 : Matrix (Fin m) (Fin m) ℝ) + a • C.Sout := by
      rw [cfc_add (a := C.Sout) (fun t => a * t) (fun _ => s), cfc_const_mul_id a C.Sout hH, cfc_const s C.Sout hH,
        Algebra.algebraMap_eq_smul_one, add_comm]
    have hne : ∀ t ∈ spectrum ℝ C.Sout, (fun t => a * t + s) t ≠ 0 := by
      intro t ht
      have h1' : (0 : ℝ) ≤ t := hspec ht
      have h2' : 0 ≤ a * t := mul_nonneg ha0 h1'
      show a * t + s ≠ 0
      exact (by linarith : (0 : ℝ) < a * t + s).ne'
    rw [← hadd, Matrix.nonsing_inv_eq_ringInverse]
    exact cfc_inv (a := C.Sout) (f := fun t => a * t + s) hne
  have h2 : (B : ℝ)⁻¹ * (s • (1 : Matrix (Fin m) (Fin m) ℝ) + a • C.Sout)⁻¹.trace =
      (B : ℝ)⁻¹ * ∑ i, (a * C.psdOut.isHermitian.eigenvalues i + s)⁻¹ := by
    have := trace_cfc_eq_integral_nuOut C hB (fun t => (a * t + s)⁻¹)
    rw [bp_int_nuOut C, hcfc] at this
    exact this
  have hs2 : a * ∑ i, C.psdOut.isHermitian.eigenvalues i /
      (a * C.psdOut.isHermitian.eigenvalues i + s) =
      (m : ℝ) - s * ∑ i, (a * C.psdOut.isHermitian.eigenvalues i + s)⁻¹ := by
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_sub_distrib,
      Finset.mul_sum]
    simp
  linear_combination a * h1 + (B : ℝ)⁻¹ * hs2 + s * h2

/-- `rem:app-de-nomomentum`(b), promoted by ruling L8, snapshot `cr-2026-10-23`. LaTeX
(`sections/02-deterministic-equivalents/section.tex` l.483–488 and the coupling
`eqn:app-de-coupling`, l.149–155):
```
\tilde s_1\,\sigma=s_1\,\tilde\sigma=q\Jfun(q),\qquad q=-z\sigma\tilde\sigma .
```
Claim (b): for `(ν, ν̃) ∈ 𝒦` and `s > 0`, the solution at `w = (1,0,…)` satisfies
`s̃₁ σ = s₁ σ̃ = q J(q)` with `q = s σ σ̃`. -/
theorem rem_app_de_nomomentum_b {Cs γ : ℝ} (hC : 0 < Cs) (hγ : 0 < γ)
    {ν ν' : FiniteMeasure ℝ} (hp : (ν, ν') ∈ classK Cs γ) {s : ℝ} (hs : 0 < s) :
    let x := branchSol (Fw (leadW 1)) ν ν' s
    x.2.2.1 * x.1 = (s * x.1 * x.2.1) * J (s * x.1 * x.2.1) ∧
      x.2.2.2 * x.2.1 = (s * x.1 * x.2.1) * J (s * x.1 * x.2.1) := by
  intro x
  exact bp_b_of_sol (fun q => bp_fw_lead1 q) (branchSol (Fw (leadW 1)) ν ν' s)
    (branchSol_spec bp_adm1 hC hγ hp hs)

/-- `rem:app-de-nomomentum`(c), promoted by ruling L8, snapshot `cr-2026-10-23`. LaTeX
(`sections/02-deterministic-equivalents/section.tex` l.493–500, the trace identity):
```
\tilde s_1\sigma-\frac{\Nout}B=z\,\frac1B\Tr\Rbar(z).
```
Claim (c): with `ν = ν_out` (the spectral measure `nuOut C B`, `B > 0`) and the solution at
`w = (1,0,…)`, `s̃₁ σ - N_out/B = z (1/B) Tr R̄(z)` at `z = -s`. The identity uses only the first
trace equation, so only the hypothesis `ν = ν_out` is needed on the measures. -/
theorem rem_app_de_nomomentum_c {Cs γ : ℝ} (hC : 0 < Cs) (hγ : 0 < γ)
    {m n B : ℕ} (C : Covariances m n) (hB : 0 < B)
    {ν ν' : FiniteMeasure ℝ} (hν : (ν : Measure ℝ) = nuOut C B)
    (hp : (ν, ν') ∈ classK Cs γ) {s : ℝ} (hs : 0 < s) :
    (branchSol (Fw (leadW 1)) ν ν' s).2.2.1 * (branchSol (Fw (leadW 1)) ν ν' s).1 -
        (m : ℝ) / (B : ℝ) =
      -s * ((B : ℝ)⁻¹ * (Rbar (Fw (leadW 1)) ν ν' C s).trace) := by
  unfold Rbar
  exact bp_c_of_sol C hB hν hs (branchSol (Fw (leadW 1)) ν ν' s)
    (branchSol_spec bp_adm1 hC hγ hp hs)

/-- Private helper: functional calculus of `t ↦ t / (a t + s)` at a positive semidefinite matrix,
`cfc (t ↦ t/(a t + s)) S = S (a S + s 1)⁻¹` for `a ≥ 0`, `s > 0`. -/
private lemma bp_cfc_ratio {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosSemidef)
    {a s : ℝ} (ha0 : 0 ≤ a) (hs : 0 < s) :
    cfc (fun t => t / (a * t + s)) S = S * (a • S + s • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ := by
  have hH : IsSelfAdjoint S := hS.isHermitian
  have hspec : spectrum ℝ S ⊆ {t : ℝ | 0 ≤ t} :=
    (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.1 hS).2
  have hadd : cfc (fun t => a * t + s) S = a • S + s • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    rw [cfc_add (a := S) (fun t => a * t) (fun _ => s), cfc_const_mul_id a S hH, cfc_const s S hH,
      Algebra.algebraMap_eq_smul_one]
  have hne : ∀ t ∈ spectrum ℝ S, (fun t => a * t + s) t ≠ 0 := by
    intro t ht
    have h1' : (0 : ℝ) ≤ t := hspec ht
    have h2' : 0 ≤ a * t := mul_nonneg ha0 h1'
    show a * t + s ≠ 0
    exact (by linarith : (0 : ℝ) < a * t + s).ne'
  have hinv : cfc (fun t => (a * t + s)⁻¹) S = (a • S + s • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ := by
    rw [← hadd, Matrix.nonsing_inv_eq_ringInverse]
    exact cfc_inv (a := S) (f := fun t => a * t + s) hne
  have hg : ContinuousOn (fun t => (a * t + s)⁻¹) (spectrum ℝ S) :=
    ContinuousOn.inv₀ (by fun_prop) hne
  have hmul := cfc_mul (fun t => t) (fun t => (a * t + s)⁻¹) S
    (by fun_prop) hg
  rw [cfc_id' ℝ S, hinv] at hmul
  simp only [div_eq_mul_inv]
  exact hmul

/-- `def:app-de-branch`, trace form of the first two equations, snapshot `cr-2026-10-23`
(`section.tex` l.129–134): "For the spectral measures of `eqn:app-setup-spectral-measures` the
first two equations read σ = (1/B) Tr(Σ_out(s̃₁Σ_out − z)⁻¹), σ̃ = (1/B) Tr(Σ_in(s₁Σ_in − z)⁻¹)."
Stated at `z = −s` for every coefficient `a ≥ 0` in place of `s̃₁` (resp. `s₁`). Added after
review L-B.2 (defect D1); cited by `cor:app-de-trace` (l.1796–1798). -/
theorem def_app_de_branch_trace {m n B : ℕ} (C : Covariances m n) (hB : 0 < B)
    {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) :
    ∫ x, x / (a * x + s) ∂(nuOut C B) =
        (B : ℝ)⁻¹ * (C.Sout * (a • C.Sout + s • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹).trace ∧
      ∫ x, x / (a * x + s) ∂(nuIn C B) =
        (B : ℝ)⁻¹ * (C.Sin * (a • C.Sin + s • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).trace := by
  constructor
  · have h := trace_cfc_eq_integral_nuOut C hB (fun t => t / (a * t + s))
    rw [bp_cfc_ratio C.Sout C.psdOut ha hs] at h
    exact h.symm
  · have h := trace_cfc_eq_integral_nuIn C hB (fun t => t / (a * t + s))
    rw [bp_cfc_ratio C.Sin C.psdIn ha hs] at h
    exact h.symm

/-! ## Normalization checks -/

/-- Private helper: `Fw` of the single weight `leadW ϖ`. -/
private lemma bp_fw_lead (ϖ q : ℝ) : Fw (leadW ϖ) q = ϖ ^ 2 * J (ϖ ^ 2 * q) := by
  unfold Fw
  rw [tsum_eq_single 0]
  · simp [leadW]
  · intro j hj
    simp [leadW, hj]

/-- Private helper: `leadW ϖ` is a weight sequence for `ϖ > 0`. -/
private lemma bp_lead_seq {ϖ : ℝ} (hϖ : 0 < ϖ) : WeightSeq (leadW ϖ) := by
  refine ⟨fun j => ?_, ?_, ⟨0, by simp [leadW, hϖ.ne']⟩⟩
  · unfold leadW
    split_ifs <;> linarith
  · exact (hasSum_ite_eq 0 ϖ).summable

/-- Private helper: `equalW K` is a weight sequence for `K ≥ 1`. -/
private lemma bp_equal_seq {K : ℕ} (hK : 1 ≤ K) : WeightSeq (equalW K) := by
  refine ⟨fun j => ?_, ?_, ⟨0, ?_⟩⟩
  · unfold equalW
    split_ifs <;> positivity
  · apply summable_of_ne_finset_zero (s := Finset.range K)
    intro j hj
    have : ¬ j < K := fun h => hj (Finset.mem_range.2 h)
    simp [equalW, this]
  · have hK0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    simp [equalW, hK0, show (0 : ℕ) < K by omega]

/-- Private helper: `Fw` of the equal-weight sequence `equalW K` (`K ≥ 1`). -/
private lemma bp_fw_equal {K : ℕ} (hK : 1 ≤ K) (q : ℝ) :
    Fw (equalW K) q = (K : ℝ)⁻¹ * J (q / (K : ℝ) ^ 2) := by
  have hK0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  unfold Fw
  rw [tsum_eq_sum (s := Finset.range K)]
  · rw [Finset.sum_congr rfl (g := fun _ => (K : ℝ)⁻¹ ^ 2 * J ((K : ℝ)⁻¹ ^ 2 * q))]
    · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        show ((K : ℝ)⁻¹ ^ 2 * q) = q / (K : ℝ) ^ 2 by ring]
      field_simp
    · intro j hj
      simp [equalW, Finset.mem_range.1 hj]
  · intro j hj
    have : ¬ j < K := fun h => hj (Finset.mem_range.2 h)
    simp [equalW, this]

/-- Private helper: the integral against the rescaled measure `K⁻¹ • μ` is `K⁻¹` times the
integral against `μ`. -/
private lemma bp_int_smul {μ : FiniteMeasure ℝ} {K : ℕ} (f : ℝ → ℝ) :
    ∫ t, f t ∂(((K : ℝ≥0)⁻¹ • μ : FiniteMeasure ℝ) : Measure ℝ) =
      (K : ℝ)⁻¹ * ∫ t, f t ∂(μ : Measure ℝ) := by
  rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure, NNReal.smul_def]
  simp

/-- Private helper: the rescaled measures `K⁻¹ • ν`, `K⁻¹ • ν'` stay in `𝒦` for `K ≥ 1`. -/
private lemma bp_classK_smul {Cs γ : ℝ} {ν ν' : FiniteMeasure ℝ} {K : ℕ} (hK : 1 ≤ K)
    (hp : (ν, ν') ∈ classK Cs γ) : ((K : ℝ≥0)⁻¹ • ν, (K : ℝ≥0)⁻¹ • ν') ∈ classK Cs γ := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hc : (K : ℝ≥0)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hK)
  have hc' : (((K : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) ≤ 1 := ENNReal.coe_le_one_iff.2 hc
  simp only [classK, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply, ENNReal.smul_def]
    exact (mul_le_of_le_one_left zero_le hc').trans h1
  · rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply, h2, smul_zero]
  · rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply, ENNReal.smul_def]
    exact (mul_le_of_le_one_left zero_le hc').trans h3
  · rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply, h4, smul_zero]

/-- Private helper: rescaling of the integral `∫ t/(ϖ² a t + s)`. -/
private lemma bp_int_scale {μ : FiniteMeasure ℝ} {ϖ s a : ℝ} (hϖ : 0 < ϖ) :
    ∫ t, t / (ϖ ^ 2 * a * t + s) ∂(μ : Measure ℝ) =
      (ϖ ^ 2)⁻¹ * ∫ t, t / (a * t + s / ϖ ^ 2) ∂(μ : Measure ℝ) := by
  have hϖ0 : ϖ ^ 2 ≠ 0 := by positivity
  have he : ∀ t : ℝ, t / (ϖ ^ 2 * a * t + s) = (ϖ ^ 2)⁻¹ * (t / (a * t + s / ϖ ^ 2)) := by
    intro t
    have h1 : ϖ ^ 2 * a * t + s = ϖ ^ 2 * (a * t + s / ϖ ^ 2) := by
      rw [mul_add, mul_div_assoc', mul_div_cancel_left₀ s hϖ0]
      ring
    rw [h1]
    generalize a * t + s / ϖ ^ 2 = D
    ring
  rw [← integral_const_mul]
  simp_rw [he]

/-- Private helper: inverse of a nonzero real multiple of a matrix. -/
private lemma bp_inv_smul_mat {n : ℕ} {k : ℝ} (hk : k ≠ 0) (M : Matrix (Fin n) (Fin n) ℝ) :
    (k • M)⁻¹ = k⁻¹ • M⁻¹ := by
  by_cases h : IsUnit M.det
  · haveI : Invertible k := invertibleOfNonzero hk
    rw [Matrix.inv_smul k (A := M) h, invOf_eq_inv]
  · have h' : ¬ IsUnit (k • M).det := by
      rw [Matrix.det_smul]
      exact fun hu => h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h', Matrix.nonsing_inv_apply_not_isUnit _ h,
      smul_zero]

/-- Private helper: the rescaled tuple `(ϖ⁻² σ₁, ϖ⁻² σ̃₁, ϖ² s̃₁, ϖ² s₁)` solves the system at
`w = (ϖ, 0, …)` and spectral parameter `s`, when `(σ₁, …)` solves it for `w = (1, 0, …)` at
`s/ϖ²`. -/
private lemma bp_scale_i {ν ν' : FiniteMeasure ℝ} {ϖ s : ℝ} (hϖ : 0 < ϖ)
    (z : ℝ × ℝ × ℝ × ℝ) (hz : IsBranchSol (Fw (leadW 1)) ν ν' (s / ϖ ^ 2) z) :
    IsBranchSol (Fw (leadW ϖ)) ν ν' s
      ((ϖ ^ 2)⁻¹ * z.1, (ϖ ^ 2)⁻¹ * z.2.1, ϖ ^ 2 * z.2.2.1, ϖ ^ 2 * z.2.2.2) := by
  obtain ⟨σ, σ', a, c⟩ := z
  obtain ⟨h0, h0', ha0, hc0, hσ, hσ', ha, hc⟩ := hz
  rw [bp_fw_lead1] at ha hc
  have hϖ0 : ϖ ^ 2 ≠ 0 := by positivity
  have harg1 : ϖ ^ 2 * (s * ((ϖ ^ 2)⁻¹ * σ) * ((ϖ ^ 2)⁻¹ * σ')) = s / ϖ ^ 2 * σ * σ' := by
    field_simp
  unfold IsBranchSol
  simp only [bp_fw_lead, harg1]
  refine ⟨mul_nonneg (by positivity) h0, mul_nonneg (by positivity) h0',
    mul_nonneg (by positivity) ha0, mul_nonneg (by positivity) hc0, ?_, ?_, ?_, ?_⟩
  · rw [bp_int_scale hϖ, ← hσ]
  · rw [bp_int_scale hϖ, ← hσ']
  · rw [ha]
    field_simp
  · rw [hc]
    field_simp

/-- Private helper: the rescaled tuple `(K σ₁, K σ̃₁, s̃₁, s₁)` solves the system for `w = (1/K, …)`
at `(ν, ν̃)`, when `(σ₁, …)` solves the unit-weight system at `(ν/K, ν̃/K)`. -/
private lemma bp_scale_ii {ν ν' : FiniteMeasure ℝ} {K : ℕ} (hK : 1 ≤ K) {s : ℝ}
    (z : ℝ × ℝ × ℝ × ℝ)
    (hz : IsBranchSol (Fw (leadW 1)) ((K : ℝ≥0)⁻¹ • ν) ((K : ℝ≥0)⁻¹ • ν') s z) :
    IsBranchSol (Fw (equalW K)) ν ν' s
      ((K : ℝ) * z.1, (K : ℝ) * z.2.1, z.2.2.1, z.2.2.2) := by
  have hK0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨σ, σ', a, c⟩ := z
  obtain ⟨h0, h0', ha0, hc0, hσ, hσ', ha, hc⟩ := hz
  rw [bp_fw_lead1] at ha hc
  rw [bp_int_smul] at hσ hσ'
  have harg : (s * ((K : ℝ) * σ) * ((K : ℝ) * σ')) / (K : ℝ) ^ 2 = s * σ * σ' := by
    field_simp
  unfold IsBranchSol
  simp only [bp_fw_equal hK, harg]
  refine ⟨mul_nonneg (by positivity) h0, mul_nonneg (by positivity) h0',
    ha0, hc0, ?_, ?_, ?_, ?_⟩
  · rw [hσ, ← mul_assoc, mul_inv_cancel₀ hK0, one_mul]
  · rw [hσ', ← mul_assoc, mul_inv_cancel₀ hK0, one_mul]
  · rw [ha]
    field_simp
  · rw [hc]
    field_simp

/-- `prop:app-de-normalization`(i), snapshot `cr-2026-10-23`. LaTeX
(`sections/02-deterministic-equivalents/section.tex` l.510–534, part (i)):
```
\begin{proposition}[Normalization checks]\label{prop:app-de-normalization}
Let $(\nu,\tilde\nu)\in\mathcal K$ and $s>0$.
\begin{enumerate}[label=(\roman*)]
\item (One weight.) Let $w=(\varpi,0,0,\dots)$ with $\varpi>0$, and let
$(\sigma_1,\tilde\sigma_1,\tilde s_{1,1},s_{1,1})(-s')$ denote the solution for
the unit weight $(1,0,0,\dots)$ at the spectral parameter $s'=s/\varpi^2$.
Then the solution for $w$ at $s$ is
\[
\begin{gathered}
\sigma=\varpi^{-2}\sigma_1(-s'),\qquad\tilde\sigma=\varpi^{-2}\tilde\sigma_1(-s'),\qquad
q=\varpi^{-2}q_1(-s'),\\
\tilde s_1=\varpi^2\tilde s_{1,1}(-s'),\qquad s_1=\varpi^2s_{1,1}(-s'),
\end{gathered}
\]
and $\Rbar_w(-s)=\varpi^{-2}\Rbar_1(-s')$.
```
Encoding: the solution for `w` at `s` is `x = branchSol (Fw (leadW ϖ)) ν ν' s`; the unit-weight
solution at `s' = s/ϖ²` is `y = branchSol (Fw (leadW 1)) ν ν' (s/ϖ²)`. The clause "`q = ϖ⁻² q₁(-s')`"
is `s σ σ̃ = ϖ⁻² (s' σ₁ σ̃₁)`. The statement holds for arbitrary `(ν, ν̃) ∈ 𝒦` (see the
open question on §6.12 in the coordinator report): `Rbar` is parametrized by the measures. -/
theorem prop_app_de_normalization_i {Cs γ ϖ : ℝ} (hC : 0 < Cs) (hγ : 0 < γ) (hϖ : 0 < ϖ)
    {m n : ℕ} (C : Covariances m n) {ν ν' : FiniteMeasure ℝ}
    (hp : (ν, ν') ∈ classK Cs γ) {s : ℝ} (hs : 0 < s) :
    let x := branchSol (Fw (leadW ϖ)) ν ν' s
    let y := branchSol (Fw (leadW 1)) ν ν' (s / ϖ ^ 2)
    x.1 = (ϖ ^ 2)⁻¹ * y.1 ∧ x.2.1 = (ϖ ^ 2)⁻¹ * y.2.1 ∧
      s * x.1 * x.2.1 = (ϖ ^ 2)⁻¹ * ((s / ϖ ^ 2) * y.1 * y.2.1) ∧
      x.2.2.1 = ϖ ^ 2 * y.2.2.1 ∧ x.2.2.2 = ϖ ^ 2 * y.2.2.2 ∧
      Rbar (Fw (leadW ϖ)) ν ν' C s = (ϖ ^ 2)⁻¹ • Rbar (Fw (leadW 1)) ν ν' C (s / ϖ ^ 2) := by
  intro x y
  have hx : IsBranchSol (Fw (leadW ϖ)) ν ν' s x :=
    branchSol_spec (Fw_admissible (bp_lead_seq hϖ)) hC hγ hp hs
  have hy : IsBranchSol (Fw (leadW 1)) ν ν' (s / ϖ ^ 2) y :=
    branchSol_spec bp_adm1 hC hγ hp (div_pos hs (by positivity))
  have hxy : x = ((ϖ ^ 2)⁻¹ * y.1, (ϖ ^ 2)⁻¹ * y.2.1, ϖ ^ 2 * y.2.2.1, ϖ ^ 2 * y.2.2.2) :=
    (thm_app_de_branch_i (Fw_admissible (bp_lead_seq hϖ)) hC hγ ν ν' hp s hs).1.unique hx
      (bp_scale_i hϖ y hy)
  have hϖ0 : ϖ ^ 2 ≠ 0 := by positivity
  have hM : s • (1 : Matrix (Fin m) (Fin m) ℝ) + (ϖ ^ 2 * y.2.2.1) • C.Sout =
      ϖ ^ 2 • ((s / ϖ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ) + y.2.2.1 • C.Sout) := by
    have hk : ϖ ^ 2 * (s / ϖ ^ 2) = s := by field_simp
    rw [smul_add, smul_smul, smul_smul, hk]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxy]
  · rw [hxy]
  · simp only [hxy]
    ring
  · rw [hxy]
  · rw [hxy]
  · show (s • (1 : Matrix (Fin m) (Fin m) ℝ) + x.2.2.1 • C.Sout)⁻¹ =
      (ϖ ^ 2)⁻¹ • ((s / ϖ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ) + y.2.2.1 • C.Sout)⁻¹
    simp only [hxy]
    rw [hM, bp_inv_smul_mat hϖ0]

/-- `prop:app-de-normalization`(ii), snapshot `cr-2026-10-23`. LaTeX
(`sections/02-deterministic-equivalents/section.tex` l.510–534, part (ii)):
```
\item ($K$ equal weights.) Let $w_j=1/K$ for $0\le j<K$ and $w_j=0$ otherwise.
Then $F_w(q)=K^{-1}\Jfun(q/K^2)$, and the solution for $w$ at $(\nu,\tilde\nu)$
is related to the solution $(\sigma',\tilde\sigma',\tilde s_1',s_1')$ for the unit weight at the
measures $(\nu/K,\tilde\nu/K)$ by
\[
\sigma=K\sigma',\qquad \tilde\sigma=K\tilde\sigma',\qquad q=K^2q',\qquad
\tilde s_1=\tilde s_1',\qquad s_1=s_1'.
\]
```
Encoding: `ν/K` is the finite measure `(K : ℝ≥0)⁻¹ • ν`. The relation `q = K² q'` is at the same
`s`, with `q' = s σ' σ̃'`. The statement holds for `(ν, ν̃) ∈ 𝒦`, `s > 0`, `K ≥ 1`. -/
theorem prop_app_de_normalization_ii {Cs γ : ℝ} (hC : 0 < Cs) (hγ : 0 < γ) {K : ℕ}
    (hK : 1 ≤ K) {ν ν' : FiniteMeasure ℝ} (hp : (ν, ν') ∈ classK Cs γ) {s : ℝ} (hs : 0 < s) :
    let x := branchSol (Fw (equalW K)) ν ν' s
    let y := branchSol (Fw (leadW 1)) ((K : ℝ≥0)⁻¹ • ν) ((K : ℝ≥0)⁻¹ • ν') s
    (∀ q : ℝ, Fw (equalW K) q = (K : ℝ)⁻¹ * J (q / (K : ℝ) ^ 2)) ∧
      x.1 = (K : ℝ) * y.1 ∧ x.2.1 = (K : ℝ) * y.2.1 ∧
      x.2.2.1 = y.2.2.1 ∧ x.2.2.2 = y.2.2.2 ∧
      s * x.1 * x.2.1 = (K : ℝ) ^ 2 * (s * y.1 * y.2.1) := by
  intro x y
  have hx : IsBranchSol (Fw (equalW K)) ν ν' s x :=
    branchSol_spec (Fw_admissible (bp_equal_seq hK)) hC hγ hp hs
  have hp' := bp_classK_smul hK hp
  have hy : IsBranchSol (Fw (leadW 1)) ((K : ℝ≥0)⁻¹ • ν) ((K : ℝ≥0)⁻¹ • ν') s y :=
    branchSol_spec bp_adm1 hC hγ hp' hs
  have hxy : x = ((K : ℝ) * y.1, (K : ℝ) * y.2.1, y.2.2.1, y.2.2.2) :=
    (thm_app_de_branch_i (Fw_admissible (bp_equal_seq hK)) hC hγ ν ν' hp s hs).1.unique hx
      (bp_scale_ii hK y hy)
  refine ⟨bp_fw_equal hK, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hxy]
  · simp only [hxy]
  · simp only [hxy]
  · simp only [hxy]
  · simp only [hxy]
    ring

end Muon.DetEquiv

end

import Muon.DetEquiv.BranchStability
import Muon.Oversampled.LimitLaw
import Muon.Oversampled.SqrtLaw
import Muon.DetEquiv.Branch

/-!
# Appendix G2: the oversampled model layer (declarations of record)

Snapshot `cr-2026-10-23`. Source: `sections/12-oversampled/section.tex`. Work package L-G2.7.
Scope: `def:app-os-objects`(iv), `thm:app-os-limit`(i)–(iv) of record, `thm:app-os-sqrt`(iii),
`def:app-os-packed`, `cor:app-os-packed`(i),(ii), `cor:app-os-identity`(ii), and the promoted
display of `rem:app-os-normalization`.

Representation choices:
* The generic statements of `Muon.Oversampled.LimitLaw` are instantiated at a half-anisotropic
  branch `br : HalfAnisoBranch β (gammaIn Nin B) (Muon.nuOut C B)` that is the solution of the
  weighted system `Muon.DetEquiv.IsBranchSol` for the EMA weights, `ν_out = Muon.nuOut C B` and
  `ν_in = γ_in δ_1` (`IsModelBranch`). Existence is `exists_modelBranch`; the branch is unique
  on `(0,∞)`, so quantifying over `br` with `IsModelBranch` is the source's "the solution".
* `Muon.nuOut C B` and `ν_in` are carried to `FiniteMeasure ℝ` by `nuOutFM` and `nuInFM` (the
  type of `Muon.DetEquiv.branchSol`).
* The standing hypothesis `Σ_in = Id` of the section is `hSin : C.Sin = 1`. The square case
  `N_out = N_in = N` is written with `Muon.Covariances N N`.
* `ν̂_out` is `nuHatOut C`, the empirical probability measure of `def:app-os-objects`(iv); the
  identity with `ν_out/γ_out` is `def_app_os_objects_iv_nu`.
* `B_eff = B / s_2` is `bEff`; `ρ̂ = ρ/(s_2 γ_in)` is `sHat` and `ε_os` is `epsOs`, both from
  `LimitLaw`.
* The record clauses quantify `ϑ` after `ρ` and `i` (`∀ ρ ∀ i ∃ ϑ`), as card §6.1 requires.
* The loewner-order and functional-calculus clauses use `cfc` on the matrix `Σ_out`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal MatrixOrder

namespace Muon.Oversampled

noncomputable section

/-! ## Model-level objects -/

/-- `B_eff = B / s_2` (`section.tex` l.90–93). -/
def bEff (β : ℝ) (B : ℕ) : ℝ := (B : ℝ) / Muon.sPow β 2

/-- The output eigenvalues `μ_k` of `Σ_out`, indexed as `C.psdOut.isHermitian.eigenvalues`. -/
def eigOut {m n : ℕ} (C : Muon.Covariances m n) : Fin m → ℝ :=
  C.psdOut.isHermitian.eigenvalues

/-- Label `def:app-os-objects`, part (iv) (`ν̂_out` as the empirical measure, `eqn:app-os-eps`). Snapshot `cr-2026-10-23`. Statement verbatim (`sections/12-oversampled/section.tex` l.200–228):

\begin{definition}[Oversampled objects]\label{def:app-os-objects}
Let $\nu$ be a probability measure and $r>0$.
\begin{enumerate}[label=(\roman*)]
\item The profile root $b_0=b_0^{\nu,r}$ is the function of
\cref{lem:app-os-root}.
\item For $\mu\ge0$ and $\hat\ridge\ge0$, the oversampled drift profile is
\begin{equation}\label{eqn:app-os-profile}
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\defeq\frac{\sqrt2}{\pi}\int_0^\infty
\frac{b_0(\hat s)\,\mu}{\hat s+b_0(\hat s)\,\mu}\,\dif v,\qquad \hat s=\hat\ridge+v^2 .
\end{equation}
In the square case we write $\mathfrak d^{\rm os}_\nu\defeq\mathfrak d^{\rm os}_{\nu,1}$
and $\mathfrak d^{\rm os}_\nu(\mu)\defeq\mathfrak d^{\rm os}_{\nu,1}(\mu;0)$.
\item The density $\varpi$ on $(0,\infty)$ and the square-root efficiency
$\chi_\nu$ are
\begin{equation}\label{eqn:app-os-chi}
\varpi(y)\defeq\frac2\pi\,\frac{\sqrt y}{(1+y)^2},\qquad
\chi_\nu(\mu)\defeq\int_0^\infty\varpi(y)\sqrt{1-m_\nu(\mu y)}\,\dif y\qquad(\mu>0).
\end{equation}
\item At a finite dimension, the empirical spectral probability measure of
$\Sigmaout$, the rescaled ridge and the small parameter are
\begin{equation}\label{eqn:app-os-eps}
\begin{gathered}
\hat\nu_{\mathrm{out}}\defeq\frac1{\Nout}\sum_{k=1}^{\Nout}\delta_{\mu_k}=\frac{\nu_{\mathrm{out}}}{\gout},\qquad
\hat\ridge\defeq\frac{\ridge}{\sw2\gin}\quad(\ridge\ge0),\\
\epsilon_{\rm os}\defeq3(1-\bmom^2)\gin=3(1+\bmom)^2\frac{\Nin}{B_{\rm eff}} .
\end{gathered}
\end{equation}
\end{enumerate}
\end{definition}
-/
def nuHatOut {m n : ℕ} (C : Muon.Covariances m n) : Measure ℝ :=
  (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (eigOut C i)

/-- `ν_out` is a finite measure when `B ≥ 1`. -/
theorem nuOut_isFiniteMeasure {m n : ℕ} (C : Muon.Covariances m n) {B : ℕ} (hB : 1 ≤ B) :
    IsFiniteMeasure (Muon.nuOut C B) := by
  unfold Muon.nuOut
  apply Measure.smul_finite _
  exact ENNReal.inv_ne_top.2 (by exact_mod_cast (show B ≠ 0 by omega))

/-- The output spectral measure `ν_out` as an element of `FiniteMeasure ℝ`, the type of the
measures in `Muon.DetEquiv.branchSol`. -/
def nuOutFM {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ) (hB : 1 ≤ B) : FiniteMeasure ℝ :=
  ⟨Muon.nuOut C B, nuOut_isFiniteMeasure C hB⟩

/-- The input spectral measure `ν_in = γ_in δ_1` (`Σ_in = Id`), as an element of
`FiniteMeasure ℝ`. -/
def nuInFM (γ : ℝ) : FiniteMeasure ℝ :=
  ⟨ENNReal.ofReal γ • Measure.dirac (1 : ℝ), Measure.smul_finite _ ENNReal.ofReal_ne_top⟩

/-- The half-anisotropic branch `(σ, σ̃, s̃₁, s₁)(-s)` of `sec:app-os-setup` is the solution of
the weighted system `Muon.DetEquiv.IsBranchSol` for the EMA weights, `ν_out` and `γ_in δ_1`.
`IsModelBranch C B hB β br` says that `br` solves that system at every `s > 0`. -/
def IsModelBranch {Nout Nin : ℕ} (C : Muon.Covariances Nout Nin) (B : ℕ) (hB : 1 ≤ B) (β : ℝ)
    (br : HalfAnisoBranch β (gammaIn Nin B) (Muon.nuOut C B)) : Prop :=
  ∀ s : ℝ, 0 < s →
    Muon.DetEquiv.IsBranchSol (Muon.DetEquiv.Fw (Muon.emaW β)) (nuOutFM C B hB)
      (nuInFM (gammaIn Nin B)) s (br.sigma s, br.sigmaT s, br.s1T s, br.s1 s)

/-- Private: the EMA weights are a weight sequence (nonnegative, summable, not all zero). -/
private lemma os_emaW_weightSeq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Muon.DetEquiv.WeightSeq (Muon.emaW β) := by
  refine ⟨fun j => ?_, ?_, 0, ?_⟩
  · unfold Muon.emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  · unfold Muon.emaW
    exact (summable_geometric_of_lt_one hβ0 hβ1).mul_left _
  · unfold Muon.emaW
    rw [pow_zero, mul_one]
    exact (by linarith : (0:ℝ) < 1 - β).ne'

/-- Private: `γ_in = N_in / B > 0`. -/
private lemma os_model_gammaIn_pos {Nin B : ℕ} (hNin : 1 ≤ Nin) (hB : 1 ≤ B) :
    0 < gammaIn Nin B := by
  unfold gammaIn
  exact div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))

/-- Private: unpacking `IsBranchSol` into its components. -/
private lemma os_isBranchSol_unpack {F : ℝ → ℝ} {ν ν' : FiniteMeasure ℝ} {s : ℝ}
    {x : ℝ × ℝ × ℝ × ℝ} (h : Muon.DetEquiv.IsBranchSol F ν ν' s x) :
    0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2.1 ∧ 0 ≤ x.2.2.2 ∧
      x.1 = ∫ t, t / (x.2.2.1 * t + s) ∂(ν : Measure ℝ) ∧
      x.2.1 = ∫ t, t / (x.2.2.2 * t + s) ∂(ν' : Measure ℝ) ∧
      x.2.2.1 = s * x.2.1 * F (s * x.1 * x.2.1) ∧
      x.2.2.2 = s * x.1 * F (s * x.1 * x.2.1) := by
  obtain ⟨σ, σ', a, c⟩ := x
  exact h

/-- Private: the model pair `(ν_out, γ_in δ_1)` lies in the class `𝒦` with
`C_Σ = max 1 (∑ eigenvalues of Σ_out)` and `γ_⋆ = max γ_in γ_out`. -/
private lemma os_model_mem {Nout Nin B : ℕ} (hNin : 1 ≤ Nin) (hB : 1 ≤ B)
    (C : Muon.Covariances Nout Nin) :
    (nuOutFM C B hB, nuInFM (gammaIn Nin B)) ∈
      Muon.DetEquiv.classK (max 1 (∑ i, C.psdOut.isHermitian.eigenvalues i))
        (max (gammaIn Nin B) (gammaOut Nout B)) := by
  set Cs : ℝ := max 1 (∑ i, C.psdOut.isHermitian.eigenvalues i) with hCs
  set γ : ℝ := max (gammaIn Nin B) (gammaOut Nout B) with hγ
  have hCs1 : 1 ≤ Cs := le_max_left _ _
  have hγin' : gammaIn Nin B ≤ γ := le_max_left _ _
  have hγout : gammaOut Nout B ≤ γ := le_max_right _ _
  have heig : ∀ i, C.psdOut.isHermitian.eigenvalues i ∈ Icc (0:ℝ) Cs := by
    intro i
    refine ⟨C.psdOut.eigenvalues_nonneg i, ?_⟩
    have h1 : C.psdOut.isHermitian.eigenvalues i ≤ ∑ j, C.psdOut.isHermitian.eigenvalues j :=
      Finset.single_le_sum (fun j _ => C.psdOut.eigenvalues_nonneg j) (Finset.mem_univ i)
    exact le_trans h1 (le_max_right _ _)
  have hmassOut : Muon.nuOut C B univ = ENNReal.ofReal (gammaOut Nout B) := by
    unfold Muon.nuOut gammaOut
    rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
    simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ENNReal.ofReal_inv_of_pos (by exact_mod_cast (show 0 < B by omega)),
      ENNReal.ofReal_natCast, mul_comm]
  have hcompOut : Muon.nuOut C B (Icc 0 Cs)ᶜ = 0 := by
    unfold Muon.nuOut
    rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
    have hz : ∀ i ∈ (Finset.univ : Finset (Fin Nout)),
        (Measure.dirac (C.psdOut.isHermitian.eigenvalues i)) (Icc 0 Cs)ᶜ = 0 :=
      fun i _ => (MeasureTheory.dirac_eq_zero_iff_not_mem measurableSet_Icc.compl).2
        (fun h => h (heig i))
    rw [Finset.sum_eq_zero hz, mul_zero]
  have hcompIn : (ENNReal.ofReal (gammaIn Nin B) • Measure.dirac (1:ℝ)) (Icc 0 Cs)ᶜ = 0 := by
    have hz : Measure.dirac (1:ℝ) (Icc 0 Cs)ᶜ = 0 :=
      (MeasureTheory.dirac_eq_zero_iff_not_mem measurableSet_Icc.compl).2
        (fun h => h ⟨zero_le_one, hCs1⟩)
    rw [Measure.smul_apply, hz, smul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Muon.nuOut C B (Icc 0 Cs) ≤ ENNReal.ofReal γ
    calc Muon.nuOut C B (Icc 0 Cs) ≤ Muon.nuOut C B univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal (gammaOut Nout B) := hmassOut
      _ ≤ ENNReal.ofReal γ := ENNReal.ofReal_le_ofReal hγout
  · exact hcompOut
  · change (ENNReal.ofReal (gammaIn Nin B) • Measure.dirac (1:ℝ)) (Icc 0 Cs) ≤ ENNReal.ofReal γ
    have h1mem : (1:ℝ) ∈ Icc (0:ℝ) Cs := ⟨zero_le_one, hCs1⟩
    rw [Measure.smul_apply, Measure.dirac_apply_of_mem h1mem, smul_eq_mul, mul_one]
    exact ENNReal.ofReal_le_ofReal hγin'
  · exact hcompIn

/-- The branch of `thm:app-de-branch`(i) exists for the model measures, with `C_Σ` and `γ_⋆`
as in `sec:app-os-setup`. -/
theorem exists_modelBranch {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Nout Nin B : ℕ}
    (hNout : 1 ≤ Nout) (hNin : 1 ≤ Nin) (hB : 1 ≤ B) (C : Muon.Covariances Nout Nin) :
    ∃ br : HalfAnisoBranch β (gammaIn Nin B) (Muon.nuOut C B), IsModelBranch C B hB β br := by
  have hγin : 0 < gammaIn Nin B := os_model_gammaIn_pos hNin hB
  have hmem := os_model_mem (Nout := Nout) hNin hB C
  set Cs : ℝ := max 1 (∑ i, C.psdOut.isHermitian.eigenvalues i) with hCs
  set γ : ℝ := max (gammaIn Nin B) (gammaOut Nout B) with hγ
  have hC : 0 < Cs := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hγpos : 0 < γ := lt_of_lt_of_le hγin (le_max_left _ _)
  have hF := Muon.DetEquiv.Fw_admissible (os_emaW_weightSeq hβ0 hβ1)
  set ν := nuOutFM C B hB with hν
  set ν' := nuInFM (gammaIn Nin B) with hν'
  set S : ℝ → ℝ × ℝ × ℝ × ℝ :=
    fun s => Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν' s with hS
  have hspec : ∀ s : ℝ, 0 < s →
      Muon.DetEquiv.IsBranchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν' s (S s) :=
    fun s hs => Muon.DetEquiv.branchSol_spec hF hC hγpos hmem hs
  have hcontP := (Muon.DetEquiv.thm_app_de_branch_ii hF hC hγpos).1
  have hcont : ContinuousOn S (Ioi 0) :=
    hcontP.comp (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs, hmem⟩)
  have hc1 : ContinuousOn (fun s => (S s).1) (Ioi 0) := continuous_fst.comp_continuousOn hcont
  have hc2 : ContinuousOn (fun s => (S s).2.1) (Ioi 0) :=
    continuous_fst.comp_continuousOn (continuous_snd.comp_continuousOn hcont)
  have hc3 : ContinuousOn (fun s => (S s).2.2.1) (Ioi 0) :=
    continuous_fst.comp_continuousOn (continuous_snd.comp_continuousOn
      (continuous_snd.comp_continuousOn hcont))
  have hc4 : ContinuousOn (fun s => (S s).2.2.2) (Ioi 0) :=
    continuous_snd.comp_continuousOn (continuous_snd.comp_continuousOn
      (continuous_snd.comp_continuousOn hcont))
  have hE1 : ∀ s : ℝ, 0 < s →
      (S s).1 = ∫ x, x / (s + (S s).2.2.1 * x) ∂(Muon.nuOut C B) := by
    intro s hs
    refine (os_isBranchSol_unpack (hspec s hs)).2.2.2.2.1.trans ?_
    congr 1
    funext t
    rw [add_comm]
  have hE2 : ∀ s : ℝ, 0 < s →
      (S s).2.1 = gammaIn Nin B / (s + (S s).2.2.2) := by
    intro s hs
    refine (os_isBranchSol_unpack (hspec s hs)).2.2.2.2.2.1.trans ?_
    have hν'eq : (ν' : Measure ℝ) = ENNReal.ofReal (gammaIn Nin B) • Measure.dirac (1:ℝ) := rfl
    rw [hν'eq, integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hγin.le, smul_eq_mul]
    rw [mul_one, add_comm, mul_one_div]
  have hE3 : ∀ s : ℝ, 0 < s →
      (S s).2.2.1 = s * (S s).2.1 * Muon.DetEquiv.Fw (Muon.emaW β) (s * (S s).1 * (S s).2.1) :=
    fun s hs => (os_isBranchSol_unpack (hspec s hs)).2.2.2.2.2.2.1
  have hE4 : ∀ s : ℝ, 0 < s →
      (S s).2.2.2 = s * (S s).1 * Muon.DetEquiv.Fw (Muon.emaW β) (s * (S s).1 * (S s).2.1) :=
    fun s hs => (os_isBranchSol_unpack (hspec s hs)).2.2.2.2.2.2.2
  refine ⟨{ sigma := fun s => (S s).1
          , sigmaT := fun s => (S s).2.1
          , s1T := fun s => (S s).2.2.1
          , s1 := fun s => (S s).2.2.2
          , q := fun s => s * (S s).1 * (S s).2.1
          , eq_sigma := hE1
          , eq_sigmaT := hE2
          , eq_q := fun s _ => rfl
          , eq_s1T := hE3
          , eq_s1 := hE4
          , nonneg := fun s hs =>
              ⟨(os_isBranchSol_unpack (hspec s hs)).1,
               (os_isBranchSol_unpack (hspec s hs)).2.1,
               (os_isBranchSol_unpack (hspec s hs)).2.2.1,
               (os_isBranchSol_unpack (hspec s hs)).2.2.2.1,
               mul_nonneg (mul_nonneg hs.le (os_isBranchSol_unpack (hspec s hs)).1)
                 (os_isBranchSol_unpack (hspec s hs)).2.1⟩
          , continuousOn_sigma := hc1
          , continuousOn_sigmaT := hc2
          , continuousOn_s1T := hc3
          , continuousOn_s1 := hc4
          , continuousOn_q := (continuousOn_id.mul hc1).mul hc2 }, fun s hs => hspec s hs⟩

/-- The ratio `ϑ_ρ(μ)` of `thm:app-os-limit`(iv): `√(s_2 γ_in) 𝔡_ρ(μ) / 𝔡^os(μ; ρ̂)` for
`μ > 0`, and `ϑ_ρ(0) = 1`. -/
def thetaRidge {β γin : ℝ} {nuOut : Measure ℝ} (br : HalfAnisoBranch β γin nuOut)
    (nu : Measure ℝ) (r ρ μ : ℝ) : ℝ :=
  if μ = 0 then 1 else
    Real.sqrt (Muon.sPow β 2 * γin) * dRidge br ρ μ / dOs nu r μ (sHat β γin ρ)

/-- The lower profile `𝔡̲_ν(μ)` of `thm:app-os-sqrt`(iii): `C_* √(1 - m_ν(μ)) √(μ/2)` for
`μ > 0`, and `0` at `μ = 0`. -/
def dUnder (ν : Measure ℝ) (μ : ℝ) : ℝ :=
  if μ = 0 then 0 else cStar * Real.sqrt (1 - mNu ν μ) * Real.sqrt (μ / 2)

/-- Label `def:app-os-packed`. Snapshot `cr-2026-10-23`. Statement verbatim (`sections/12-oversampled/section.tex` l.966–972):

\begin{definition}[Packed mode]\label{def:app-os-packed}
Let $K\ge1$ and $\delta\in(0,1]$. In the square case $\Nout=\Nin=N$, an
eigenvalue $\mu_i>0$ of $\Sigmaout$ is \emph{$(K,\delta)$-packed} if
\[
\#\{k\le N:\ \mu_k\le K\mu_i\}\ge\delta N .
\]
\end{definition}
-/
def def_app_os_packed {N : ℕ} (K δ : ℝ) (μ : Fin N → ℝ) (i : Fin N) : Prop :=
  0 < μ i ∧ δ * (N : ℝ) ≤ ((Finset.univ.filter fun k => μ k ≤ K * μ i).card : ℝ)

/-- Private: `ν_out` puts no mass on `(-∞, 0)` (the eigenvalues of `Σ_out` are nonnegative). -/
private lemma os_nuOut_Iio {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ) :
    Muon.nuOut C B (Iio 0) = 0 := by
  unfold Muon.nuOut
  rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      (Measure.dirac (C.psdOut.isHermitian.eigenvalues i)) (Iio 0) = 0 :=
    fun i _ => (MeasureTheory.dirac_eq_zero_iff_not_mem measurableSet_Iio).2
      (not_lt.2 (C.psdOut.eigenvalues_nonneg i))
  rw [Finset.sum_eq_zero hz, mul_zero]

/-- Private: the total mass of `ν_out` is `γ_out = N_out / B` (for `B ≥ 1`). -/
private lemma os_nuOut_mass {m n : ℕ} (C : Muon.Covariances m n) {B : ℕ} (hB : 1 ≤ B) :
    Muon.nuOut C B univ = ENNReal.ofReal (gammaOut m B) := by
  unfold Muon.nuOut gammaOut
  rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast (show 0 < B by omega)),
    ENNReal.ofReal_natCast, mul_comm]

/-! ## Declarations of record -/

/-- Label `def:app-os-objects`, part (iv), identity `ν̂_out = ν_out/γ_out` (`eqn:app-os-eps`). Snapshot `cr-2026-10-23`. Statement verbatim (`sections/12-oversampled/section.tex` l.200–228):

\begin{definition}[Oversampled objects]\label{def:app-os-objects}
Let $\nu$ be a probability measure and $r>0$.
\begin{enumerate}[label=(\roman*)]
\item The profile root $b_0=b_0^{\nu,r}$ is the function of
\cref{lem:app-os-root}.
\item For $\mu\ge0$ and $\hat\ridge\ge0$, the oversampled drift profile is
\begin{equation}\label{eqn:app-os-profile}
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\defeq\frac{\sqrt2}{\pi}\int_0^\infty
\frac{b_0(\hat s)\,\mu}{\hat s+b_0(\hat s)\,\mu}\,\dif v,\qquad \hat s=\hat\ridge+v^2 .
\end{equation}
In the square case we write $\mathfrak d^{\rm os}_\nu\defeq\mathfrak d^{\rm os}_{\nu,1}$
and $\mathfrak d^{\rm os}_\nu(\mu)\defeq\mathfrak d^{\rm os}_{\nu,1}(\mu;0)$.
\item The density $\varpi$ on $(0,\infty)$ and the square-root efficiency
$\chi_\nu$ are
\begin{equation}\label{eqn:app-os-chi}
\varpi(y)\defeq\frac2\pi\,\frac{\sqrt y}{(1+y)^2},\qquad
\chi_\nu(\mu)\defeq\int_0^\infty\varpi(y)\sqrt{1-m_\nu(\mu y)}\,\dif y\qquad(\mu>0).
\end{equation}
\item At a finite dimension, the empirical spectral probability measure of
$\Sigmaout$, the rescaled ridge and the small parameter are
\begin{equation}\label{eqn:app-os-eps}
\begin{gathered}
\hat\nu_{\mathrm{out}}\defeq\frac1{\Nout}\sum_{k=1}^{\Nout}\delta_{\mu_k}=\frac{\nu_{\mathrm{out}}}{\gout},\qquad
\hat\ridge\defeq\frac{\ridge}{\sw2\gin}\quad(\ridge\ge0),\\
\epsilon_{\rm os}\defeq3(1-\bmom^2)\gin=3(1+\bmom)^2\frac{\Nin}{B_{\rm eff}} .
\end{gathered}
\end{equation}
\end{enumerate}
\end{definition}
-/
theorem def_app_os_objects_iv_nu {m n : ℕ} (C : Muon.Covariances m n) {B : ℕ} (hB : 1 ≤ B) :
    nuHatOut C = hatNu (Muon.nuOut C B) (gammaOut m B) := by
  by_cases hm : m = 0
  · subst hm
    simp [nuHatOut, hatNu, Muon.nuOut, gammaOut]
  have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hBne0 : (B : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  have hBneTop : (B : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top B
  unfold nuHatOut hatNu Muon.nuOut gammaOut
  rw [ENNReal.ofReal_div_of_pos hB0, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, smul_smul]
  congr 1
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hBneTop))
    (Or.inl (ENNReal.inv_ne_top.2 hBne0)), inv_inv, mul_right_comm,
    ENNReal.mul_inv_cancel hBne0 hBneTop, one_mul]

/-- Label `def:app-os-objects`, part (iv), identity `ε_os = 3(1+β)² N_in/B_eff` (`eqn:app-os-eps`). Snapshot `cr-2026-10-23`. Statement verbatim (`sections/12-oversampled/section.tex` l.200–228):

\begin{definition}[Oversampled objects]\label{def:app-os-objects}
Let $\nu$ be a probability measure and $r>0$.
\begin{enumerate}[label=(\roman*)]
\item The profile root $b_0=b_0^{\nu,r}$ is the function of
\cref{lem:app-os-root}.
\item For $\mu\ge0$ and $\hat\ridge\ge0$, the oversampled drift profile is
\begin{equation}\label{eqn:app-os-profile}
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\defeq\frac{\sqrt2}{\pi}\int_0^\infty
\frac{b_0(\hat s)\,\mu}{\hat s+b_0(\hat s)\,\mu}\,\dif v,\qquad \hat s=\hat\ridge+v^2 .
\end{equation}
In the square case we write $\mathfrak d^{\rm os}_\nu\defeq\mathfrak d^{\rm os}_{\nu,1}$
and $\mathfrak d^{\rm os}_\nu(\mu)\defeq\mathfrak d^{\rm os}_{\nu,1}(\mu;0)$.
\item The density $\varpi$ on $(0,\infty)$ and the square-root efficiency
$\chi_\nu$ are
\begin{equation}\label{eqn:app-os-chi}
\varpi(y)\defeq\frac2\pi\,\frac{\sqrt y}{(1+y)^2},\qquad
\chi_\nu(\mu)\defeq\int_0^\infty\varpi(y)\sqrt{1-m_\nu(\mu y)}\,\dif y\qquad(\mu>0).
\end{equation}
\item At a finite dimension, the empirical spectral probability measure of
$\Sigmaout$, the rescaled ridge and the small parameter are
\begin{equation}\label{eqn:app-os-eps}
\begin{gathered}
\hat\nu_{\mathrm{out}}\defeq\frac1{\Nout}\sum_{k=1}^{\Nout}\delta_{\mu_k}=\frac{\nu_{\mathrm{out}}}{\gout},\qquad
\hat\ridge\defeq\frac{\ridge}{\sw2\gin}\quad(\ridge\ge0),\\
\epsilon_{\rm os}\defeq3(1-\bmom^2)\gin=3(1+\bmom)^2\frac{\Nin}{B_{\rm eff}} .
\end{gathered}
\end{equation}
\end{enumerate}
\end{definition}
-/
theorem def_app_os_objects_iv_eps (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (Nin B : ℕ) :
    epsOs β (gammaIn Nin B) = 3 * (1 + β) ^ 2 * (Nin : ℝ) / bEff β B := by
  have h1 : (1 - β) ≠ 0 := by intro h; linarith
  have h2 : (1 + β) ≠ 0 := by intro h; linarith
  unfold epsOs gammaIn bEff
  rw [Muon.sPow_two hβ0 hβ1]
  by_cases hB : (B : ℝ) = 0
  · simp [hB]
  · field_simp
    ring

/-- Label `thm:app-os-limit`, part (i) (declaration of record). Snapshot `cr-2026-10-23`. Statement verbatim (`sections/12-oversampled/section.tex` l.430–465):

\begin{theorem}[Oversampled limit law]\label{thm:app-os-limit}
Let $\Nout,\Nin,B\ge1$, let $\Sigmaout$ be positive semidefinite, let
$\bmom\in[0,1)$, and assume that $\bmom>0$, or that $\bmom=0$ and $\gin<1$. Let
$q_\star$ be as in \cref{lem:app-os-scalar}(iii), and put
$\Lambda\defeq1+3(1-\bmom)^2q_\star$. Write
$\mathfrak d^{\rm os}=\mathfrak d^{\rm os}_{\hat\nu_{\mathrm{out}},r}$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ridge>0$ and $\mu\ge0$,
\[
\Lambda^{-1}\,\mathfrak d^{\rm os}(\mu;\hat\ridge)\le\sqrt{\sw2\gin}\;\mathfrak d_\ridge(\mu)\le\Lambda\,\mathfrak d^{\rm os}(\mu;\hat\ridge).
\]
\item For every $\mu\ge0$ the limit
\[
\mathfrak d_0(\mu)\defeq\lim_{\ridge\downarrow0}\mathfrak d_\ridge(\mu)=\frac{\sqrt2}{\pi}\int_0^\infty\mathsf k(u^2;\mu)\,\dif u
\]
exists in $[0,\infty)$, and it satisfies the bounds of (i) with $\ridge=\hat\ridge=0$.
\item If $\epsilon_{\rm os}<1$, then $\Lambda\le(1-\epsilon_{\rm os})^{-1}$. Consequently,
for every $\ridge\ge0$ and $1\le i\le\Nout$,
\begin{equation}\label{eqn:app-os-limit}
\mathfrak d_i(\ridge)=\vartheta_i\,\sqrt{\frac{B_{\rm eff}}{\Nin}}\;\mathfrak d^{\rm os}(\mu_i;\hat\ridge)
\qquad\text{for some }\vartheta_i\in\big[1-\epsilon_{\rm os},(1-\epsilon_{\rm os})^{-1}\big],
\end{equation}
and for every $\mu\ge0$
\[
\Big|\sqrt{\sw2\gin}\;\mathfrak d_\ridge(\mu)-\mathfrak d^{\rm os}(\mu;\hat\ridge)\Big|
\le\frac{\epsilon_{\rm os}}{1-\epsilon_{\rm os}}\,\mathfrak d^{\rm os}(\mu;\hat\ridge)
\le\frac{\epsilon_{\rm os}}{1-\epsilon_{\rm os}}\sqrt{\frac\mu2}.
\]
\item For $\ridge\ge0$ let $\vartheta_\ridge(\mu)\defeq\sqrt{\sw2\gin}\,\mathfrak d_\ridge(\mu)/\mathfrak d^{\rm os}(\mu;\hat\ridge)$
for $\mu>0$ and $\vartheta_\ridge(0)\defeq1$. Then
$\operatorname{spec}\vartheta_\ridge(\Sigmaout)\subset[\Lambda^{-1},\Lambda]$ and
\[
\mathfrak d_\ridge(\Sigmaout)=\sqrt{\frac{B_{\rm eff}}{\Nin}}\;\vartheta_\ridge(\Sigmaout)\,\mathfrak d^{\rm os}(\Sigmaout;\hat\ridge).
\]
\end{enumerate}
\end{theorem}
-/
theorem thm_app_os_limit_i {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Nout Nin B : ℕ}
    (hNout : 1 ≤ Nout) (hNin : 1 ≤ Nin) (hB : 1 ≤ B) (C : Muon.Covariances Nout Nin)
    (hSin : C.Sin = 1) (hcond : 0 < β ∨ (β = 0 ∧ gammaIn Nin B < 1))
    {qs : ℝ} (hqs : 0 < qs ∧ qs * Muon.DetEquiv.Fw (Muon.emaW β) qs = gammaIn Nin B)
    (br : HalfAnisoBranch β (gammaIn Nin B) (Muon.nuOut C B)) (hbr : IsModelBranch C B hB β br) :
    ∀ ρ : ℝ, 0 < ρ → ∀ μ : ℝ, 0 ≤ μ →
      (lamOs β qs)⁻¹ * dOs (nuHatOut C) ((Nout : ℝ) / Nin) μ (sHat β (gammaIn Nin B) ρ) ≤
        Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dRidge br ρ μ ∧
      Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dRidge br ρ μ ≤
        lamOs β qs * dOs (nuHatOut C) ((Nout : ℝ) / Nin) μ (sHat β (gammaIn Nin B) ρ) := by
  rw [def_app_os_objects_iv_nu C hB]
  exact limit_generic_i hβ0 hβ1 hNout hNin hB (os_nuOut_Iio C B) (os_nuOut_mass C hB) hcond hqs br

/-- Label `thm:app-os-limit`, part (ii) (declaration of record). Snapshot `cr-2026-10-23`. Statement verbatim (`sections/12-oversampled/section.tex` l.430–465):

\begin{theorem}[Oversampled limit law]\label{thm:app-os-limit}
Let $\Nout,\Nin,B\ge1$, let $\Sigmaout$ be positive semidefinite, let
$\bmom\in[0,1)$, and assume that $\bmom>0$, or that $\bmom=0$ and $\gin<1$. Let
$q_\star$ be as in \cref{lem:app-os-scalar}(iii), and put
$\Lambda\defeq1+3(1-\bmom)^2q_\star$. Write
$\mathfrak d^{\rm os}=\mathfrak d^{\rm os}_{\hat\nu_{\mathrm{out}},r}$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ridge>0$ and $\mu\ge0$,
\[
\Lambda^{-1}\,\mathfrak d^{\rm os}(\mu;\hat\ridge)\le\sqrt{\sw2\gin}\;\mathfrak d_\ridge(\mu)\le\Lambda\,\mathfrak d^{\rm os}(\mu;\hat\ridge).
\]
\item For every $\mu\ge0$ the limit
\[
\mathfrak d_0(\mu)\defeq\lim_{\ridge\downarrow0}\mathfrak d_\ridge(\mu)=\frac{\sqrt2}{\pi}\int_0^\infty\mathsf k(u^2;\mu)\,\dif u
\]
exists in $[0,\infty)$, and it satisfies the bounds of (i) with $\ridge=\hat\ridge=0$.
\item If $\epsilon_{\rm os}<1$, then $\Lambda\le(1-\epsilon_{\rm os})^{-1}$. Consequently,
for every $\ridge\ge0$ and $1\le i\le\Nout$,
\begin{equation}\label{eqn:app-os-limit}
\mathfrak d_i(\ridge)=\vartheta_i\,\sqrt{\frac{B_{\rm eff}}{\Nin}}\;\mathfrak d^{\rm os}(\mu_i;\hat\ridge)
\qquad\text{for some }\vartheta_i\in\big[1-\epsilon_{\rm os},(1-\epsilon_{\rm os})^{-1}\big],
\end{equation}
and for every $\mu\ge0$
\[
\Big|\sqrt{\sw2\gin}\;\mathfrak d_\ridge(\mu)-\mathfrak d^{\rm os}(\mu;\hat\ridge)\Big|
\le\frac{\epsilon_{\rm os}}{1-\epsilon_{\rm os}}\,\mathfrak d^{\rm os}(\mu;\hat\ridge)
\le\frac{\epsilon_{\rm os}}{1-\epsilon_{\rm os}}\sqrt{\frac\mu2}.
\]
\item For $\ridge\ge0$ let $\vartheta_\ridge(\mu)\defeq\sqrt{\sw2\gin}\,\mathfrak d_\ridge(\mu)/\mathfrak d^{\rm os}(\mu;\hat\ridge)$
for $\mu>0$ and $\vartheta_\ridge(0)\defeq1$. Then
$\operatorname{spec}\vartheta_\ridge(\Sigmaout)\subset[\Lambda^{-1},\Lambda]$ and
\[
\mathfrak d_\ridge(\Sigmaout)=\sqrt{\frac{B_{\rm eff}}{\Nin}}\;\vartheta_\ridge(\Sigmaout)\,\mathfrak d^{\rm os}(\Sigmaout;\hat\ridge).
\]
\end{enumerate}
\end{theorem}
-/
theorem thm_app_os_limit_ii {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Nout Nin B : ℕ}
    (hNout : 1 ≤ Nout) (hNin : 1 ≤ Nin) (hB : 1 ≤ B) (C : Muon.Covariances Nout Nin)
    (hSin : C.Sin = 1) (hcond : 0 < β ∨ (β = 0 ∧ gammaIn Nin B < 1))
    {qs : ℝ} (hqs : 0 < qs ∧ qs * Muon.DetEquiv.Fw (Muon.emaW β) qs = gammaIn Nin B)
    (br : HalfAnisoBranch β (gammaIn Nin B) (Muon.nuOut C B)) (hbr : IsModelBranch C B hB β br) :
    ∀ μ : ℝ, 0 ≤ μ →
      Tendsto (fun ρ : ℝ => dRidge br ρ μ) (𝓝[>] (0 : ℝ)) (𝓝 (dZero br μ)) ∧
      0 ≤ dZero br μ ∧
      (lamOs β qs)⁻¹ * dOs (nuHatOut C) ((Nout : ℝ) / Nin) μ 0 ≤
        Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dZero br μ ∧
      Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dZero br μ ≤
        lamOs β qs * dOs (nuHatOut C) ((Nout : ℝ) / Nin) μ 0 := by
  rw [def_app_os_objects_iv_nu C hB]
  exact limit_generic_ii hβ0 hβ1 hNout hNin hB (os_nuOut_Iio C B) (os_nuOut_mass C hB) hcond hqs br

/-- Label `thm:app-os-limit`, part (iii) (declaration of record). Snapshot `cr-2026-10-23`. Statement verbatim (`sections/12-oversampled/section.tex` l.430–465):

\begin{theorem}[Oversampled limit law]\label{thm:app-os-limit}
Let $\Nout,\Nin,B\ge1$, let $\Sigmaout$ be positive semidefinite, let
$\bmom\in[0,1)$, and assume that $\bmom>0$, or that $\bmom=0$ and $\gin<1$. Let
$q_\star$ be as in \cref{lem:app-os-scalar}(iii), and put
$\Lambda\defeq1+3(1-\bmom)^2q_\star$. Write
$\mathfrak d^{\rm os}=\mathfrak d^{\rm os}_{\hat\nu_{\mathrm{out}},r}$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ridge>0$ and $\mu\ge0$,
\[
\Lambda^{-1}\,\mathfrak d^{\rm os}(\mu;\hat\ridge)\le\sqrt{\sw2\gin}\;\mathfrak d_\ridge(\mu)\le\Lambda\,\mathfrak d^{\rm os}(\mu;\hat\ridge).
\]
\item For every $\mu\ge0$ the limit
\[
\mathfrak d_0(\mu)\defeq\lim_{\ridge\downarrow0}\mathfrak d_\ridge(\mu)=\frac{\sqrt2}{\pi}\int_0^\infty\mathsf k(u^2;\mu)\,\dif u
\]
exists in $[0,\infty)$, and it satisfies the bounds of (i) with $\ridge=\hat\ridge=0$.
\item If $\epsilon_{\rm os}<1$, then $\Lambda\le(1-\epsilon_{\rm os})^{-1}$. Consequently,
for every $\ridge\ge0$ and $1\le i\le\Nout$,
\begin{equation}\label{eqn:app-os-limit}
\mathfrak d_i(\ridge)=\vartheta_i\,\sqrt{\frac{B_{\rm eff}}{\Nin}}\;\mathfrak d^{\rm os}(\mu_i;\hat\ridge)
\qquad\text{for some }\vartheta_i\in\big[1-\epsilon_{\rm os},(1-\epsilon_{\rm os})^{-1}\big],
\end{equation}
and for every $\mu\ge0$
\[
\Big|\sqrt{\sw2\gin}\;\mathfrak d_\ridge(\mu)-\mathfrak d^{\rm os}(\mu;\hat\ridge)\Big|
\le\frac{\epsilon_{\rm os}}{1-\epsilon_{\rm os}}\,\mathfrak d^{\rm os}(\mu;\hat\ridge)
\le\frac{\epsilon_{\rm os}}{1-\epsilon_{\rm os}}\sqrt{\frac\mu2}.
\]
\item For $\ridge\ge0$ let $\vartheta_\ridge(\mu)\defeq\sqrt{\sw2\gin}\,\mathfrak d_\ridge(\mu)/\mathfrak d^{\rm os}(\mu;\hat\ridge)$
for $\mu>0$ and $\vartheta_\ridge(0)\defeq1$. Then
$\operatorname{spec}\vartheta_\ridge(\Sigmaout)\subset[\Lambda^{-1},\Lambda]$ and
\[
\mathfrak d_\ridge(\Sigmaout)=\sqrt{\frac{B_{\rm eff}}{\Nin}}\;\vartheta_\ridge(\Sigmaout)\,\mathfrak d^{\rm os}(\Sigmaout;\hat\ridge).
\]
\end{enumerate}
\end{theorem}
-/
theorem thm_app_os_limit_iii {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Nout Nin B : ℕ}
    (hNout : 1 ≤ Nout) (hNin : 1 ≤ Nin) (hB : 1 ≤ B) (C : Muon.Covariances Nout Nin)
    (hSin : C.Sin = 1) (hcond : 0 < β ∨ (β = 0 ∧ gammaIn Nin B < 1))
    {qs : ℝ} (hqs : 0 < qs ∧ qs * Muon.DetEquiv.Fw (Muon.emaW β) qs = gammaIn Nin B)
    (hε : epsOs β (gammaIn Nin B) < 1)
    (br : HalfAnisoBranch β (gammaIn Nin B) (Muon.nuOut C B)) (hbr : IsModelBranch C B hB β br) :
    lamOs β qs ≤ (1 - epsOs β (gammaIn Nin B))⁻¹ ∧
    (∀ ρ : ℝ, 0 ≤ ρ → ∀ i : Fin Nout, ∃ ϑ : ℝ,
      ϑ ∈ Icc (1 - epsOs β (gammaIn Nin B)) (1 - epsOs β (gammaIn Nin B))⁻¹ ∧
      dRidge br ρ (eigOut C i) =
        ϑ * Real.sqrt (bEff β B / (Nin : ℝ)) *
          dOs (nuHatOut C) ((Nout : ℝ) / Nin) (eigOut C i) (sHat β (gammaIn Nin B) ρ)) ∧
    (∀ ρ : ℝ, 0 ≤ ρ → ∀ μ : ℝ, 0 ≤ μ →
      |Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dRidge br ρ μ -
          dOs (nuHatOut C) ((Nout : ℝ) / Nin) μ (sHat β (gammaIn Nin B) ρ)| ≤
        epsOs β (gammaIn Nin B) / (1 - epsOs β (gammaIn Nin B)) *
          dOs (nuHatOut C) ((Nout : ℝ) / Nin) μ (sHat β (gammaIn Nin B) ρ) ∧
      epsOs β (gammaIn Nin B) / (1 - epsOs β (gammaIn Nin B)) *
          dOs (nuHatOut C) ((Nout : ℝ) / Nin) μ (sHat β (gammaIn Nin B) ρ) ≤
        epsOs β (gammaIn Nin B) / (1 - epsOs β (gammaIn Nin B)) * Real.sqrt (μ / 2)) := by
  have h3 := limit_generic_iii hβ0 hβ1 hNout hNin hB (os_nuOut_Iio C B) (os_nuOut_mass C hB)
    hcond hqs hε br
  rw [def_app_os_objects_iv_nu C hB]
  refine ⟨h3.1, fun ρ hρ i => ?_, h3.2.2⟩
  obtain ⟨ϑ, hϑ, h⟩ := h3.2.1 ρ hρ (eigOut C i) (C.psdOut.eigenvalues_nonneg i)
  exact ⟨ϑ, hϑ, h⟩

/-- Label `thm:app-os-limit`, part (iv) (declaration of record). Snapshot `cr-2026-10-23`. Statement verbatim (`sections/12-oversampled/section.tex` l.430–465):

\begin{theorem}[Oversampled limit law]\label{thm:app-os-limit}
Let $\Nout,\Nin,B\ge1$, let $\Sigmaout$ be positive semidefinite, let
$\bmom\in[0,1)$, and assume that $\bmom>0$, or that $\bmom=0$ and $\gin<1$. Let
$q_\star$ be as in \cref{lem:app-os-scalar}(iii), and put
$\Lambda\defeq1+3(1-\bmom)^2q_\star$. Write
$\mathfrak d^{\rm os}=\mathfrak d^{\rm os}_{\hat\nu_{\mathrm{out}},r}$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ridge>0$ and $\mu\ge0$,
\[
\Lambda^{-1}\,\mathfrak d^{\rm os}(\mu;\hat\ridge)\le\sqrt{\sw2\gin}\;\mathfrak d_\ridge(\mu)\le\Lambda\,\mathfrak d^{\rm os}(\mu;\hat\ridge).
\]
\item For every $\mu\ge0$ the limit
\[
\mathfrak d_0(\mu)\defeq\lim_{\ridge\downarrow0}\mathfrak d_\ridge(\mu)=\frac{\sqrt2}{\pi}\int_0^\infty\mathsf k(u^2;\mu)\,\dif u
\]
exists in $[0,\infty)$, and it satisfies the bounds of (i) with $\ridge=\hat\ridge=0$.
\item If $\epsilon_{\rm os}<1$, then $\Lambda\le(1-\epsilon_{\rm os})^{-1}$. Consequently,
for every $\ridge\ge0$ and $1\le i\le\Nout$,
\begin{equation}\label{eqn:app-os-limit}
\mathfrak d_i(\ridge)=\vartheta_i\,\sqrt{\frac{B_{\rm eff}}{\Nin}}\;\mathfrak d^{\rm os}(\mu_i;\hat\ridge)
\qquad\text{for some }\vartheta_i\in\big[1-\epsilon_{\rm os},(1-\epsilon_{\rm os})^{-1}\big],
\end{equation}
and for every $\mu\ge0$
\[
\Big|\sqrt{\sw2\gin}\;\mathfrak d_\ridge(\mu)-\mathfrak d^{\rm os}(\mu;\hat\ridge)\Big|
\le\frac{\epsilon_{\rm os}}{1-\epsilon_{\rm os}}\,\mathfrak d^{\rm os}(\mu;\hat\ridge)
\le\frac{\epsilon_{\rm os}}{1-\epsilon_{\rm os}}\sqrt{\frac\mu2}.
\]
\item For $\ridge\ge0$ let $\vartheta_\ridge(\mu)\defeq\sqrt{\sw2\gin}\,\mathfrak d_\ridge(\mu)/\mathfrak d^{\rm os}(\mu;\hat\ridge)$
for $\mu>0$ and $\vartheta_\ridge(0)\defeq1$. Then
$\operatorname{spec}\vartheta_\ridge(\Sigmaout)\subset[\Lambda^{-1},\Lambda]$ and
\[
\mathfrak d_\ridge(\Sigmaout)=\sqrt{\frac{B_{\rm eff}}{\Nin}}\;\vartheta_\ridge(\Sigmaout)\,\mathfrak d^{\rm os}(\Sigmaout;\hat\ridge).
\]
\end{enumerate}
\end{theorem}
-/
theorem thm_app_os_limit_iv {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Nout Nin B : ℕ}
    (hNout : 1 ≤ Nout) (hNin : 1 ≤ Nin) (hB : 1 ≤ B) (C : Muon.Covariances Nout Nin)
    (hSin : C.Sin = 1) (hcond : 0 < β ∨ (β = 0 ∧ gammaIn Nin B < 1))
    {qs : ℝ} (hqs : 0 < qs ∧ qs * Muon.DetEquiv.Fw (Muon.emaW β) qs = gammaIn Nin B)
    (br : HalfAnisoBranch β (gammaIn Nin B) (Muon.nuOut C B)) (hbr : IsModelBranch C B hB β br) :
    ∀ ρ : ℝ, 0 ≤ ρ →
      spectrum ℝ (cfc (fun μ : ℝ => thetaRidge br (nuHatOut C) ((Nout : ℝ) / Nin) ρ μ)
          C.Sout) ⊆ Icc (lamOs β qs)⁻¹ (lamOs β qs) ∧
      cfc (fun μ : ℝ => dRidge br ρ μ) C.Sout =
        Real.sqrt (bEff β B / (Nin : ℝ)) •
          (cfc (fun μ : ℝ => thetaRidge br (nuHatOut C) ((Nout : ℝ) / Nin) ρ μ) C.Sout *
            cfc (fun μ : ℝ => dOs (nuHatOut C) ((Nout : ℝ) / Nin) μ (sHat β (gammaIn Nin B) ρ))
              C.Sout) := by
  have hnn : ∀ μ ∈ spectrum ℝ C.Sout, 0 ≤ μ := by
    intro μ hμ
    rw [C.psdOut.isHermitian.spectrum_real_eq_range_eigenvalues] at hμ
    obtain ⟨i, rfl⟩ := hμ
    exact C.psdOut.eigenvalues_nonneg i
  have hfin : (spectrum ℝ C.Sout).Finite := by
    rw [C.psdOut.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  have hγout : 0 < gammaOut Nout B := by
    unfold gammaOut
    exact div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))
  have hγ : 0 < gammaIn Nin B := by
    unfold gammaIn
    exact div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))
  have hS : 0 < Muon.sPow β 2 := by
    rw [Muon.sPow_two hβ0 hβ1]
    apply div_pos <;> linarith
  have hSγ : 0 < Muon.sPow β 2 * gammaIn Nin B := mul_pos hS hγ
  have hr : (0 : ℝ) < (Nout : ℝ) / Nin :=
    div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))
  have hΛ1 : 1 ≤ lamOs β qs := by
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (sq_nonneg (1 - β))) hqs.1.le
    unfold lamOs
    linarith
  have hΛpos : 0 < lamOs β qs := by linarith
  have hν0' : hatNu (Muon.nuOut C B) (gammaOut Nout B) (Iio 0) = 0 := by
    unfold hatNu
    rw [Measure.smul_apply, os_nuOut_Iio C B, smul_zero]
  haveI : IsProbabilityMeasure (hatNu (Muon.nuOut C B) (gammaOut Nout B)) := by
    refine ⟨?_⟩
    unfold hatNu
    rw [Measure.smul_apply, os_nuOut_mass C hB, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hγout).ne' ENNReal.ofReal_ne_top
  have hpos : ∀ ρ : ℝ, 0 ≤ ρ → ∀ μ : ℝ, 0 < μ →
      0 < dOs (hatNu (Muon.nuOut C B) (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
        (sHat β (gammaIn Nin B) ρ) := by
    intro ρ hρ μ hμ
    have hsh : 0 ≤ sHat β (gammaIn Nin B) ρ := div_nonneg hρ hSγ.le
    exact (lem_app_os_profile_iii _ hν0' hr hμ.le _ hsh).2 hμ
  have hθ : ∀ ρ : ℝ, 0 ≤ ρ → ∀ μ : ℝ, 0 ≤ μ →
      (lamOs β qs)⁻¹ ≤ thetaRidge br (hatNu (Muon.nuOut C B) (gammaOut Nout B))
          ((Nout : ℝ) / Nin) ρ μ ∧
      thetaRidge br (hatNu (Muon.nuOut C B) (gammaOut Nout B)) ((Nout : ℝ) / Nin) ρ μ ≤
          lamOs β qs := by
    intro ρ hρ μ hμ
    rcases hμ.eq_or_lt with h0 | hμpos
    · subst h0
      have h1 : thetaRidge br (hatNu (Muon.nuOut C B) (gammaOut Nout B)) ((Nout : ℝ) / Nin) ρ 0
          = 1 := by
        simp [thetaRidge]
      rw [h1]
      exact ⟨(inv_le_one₀ hΛpos).2 hΛ1, hΛ1⟩
    · have hD := hpos ρ hρ μ hμpos
      have hθdef : thetaRidge br (hatNu (Muon.nuOut C B) (gammaOut Nout B)) ((Nout : ℝ) / Nin) ρ μ
          = Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dRidge br ρ μ /
            dOs (hatNu (Muon.nuOut C B) (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
              (sHat β (gammaIn Nin B) ρ) := by
        unfold thetaRidge
        rw [if_neg hμpos.ne']
      have hbd : (lamOs β qs)⁻¹ * dOs (hatNu (Muon.nuOut C B) (gammaOut Nout B))
            ((Nout : ℝ) / Nin) μ (sHat β (gammaIn Nin B) ρ) ≤
          Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dRidge br ρ μ ∧
          Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dRidge br ρ μ ≤
          lamOs β qs * dOs (hatNu (Muon.nuOut C B) (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
            (sHat β (gammaIn Nin B) ρ) := by
        rcases hρ.eq_or_lt with h0 | hρpos
        · subst h0
          have hdz : dRidge br 0 μ = dZero br μ := by simp [dRidge, dZero]
          have hs0 : sHat β (gammaIn Nin B) 0 = 0 := by simp [sHat]
          obtain ⟨_, _, h3, h4⟩ := limit_generic_ii hβ0 hβ1 hNout hNin hB (os_nuOut_Iio C B)
            (os_nuOut_mass C hB) hcond hqs br μ hμ
          rw [hs0, hdz]
          exact ⟨h3, h4⟩
        · obtain ⟨h1, h2⟩ := limit_generic_i hβ0 hβ1 hNout hNin hB (os_nuOut_Iio C B)
            (os_nuOut_mass C hB) hcond hqs br ρ hρpos μ hμ
          exact ⟨h1, h2⟩
      rw [hθdef]
      exact ⟨(le_div_iff₀ hD).2 hbd.1, (div_le_iff₀ hD).2 hbd.2⟩
  have hB' : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hN' : (Nin : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hS' : Muon.sPow β 2 ≠ 0 := hS.ne'
  have hbE : 0 ≤ bEff β B / (Nin : ℝ) := by
    unfold bEff
    exact div_nonneg (div_nonneg (Nat.cast_nonneg _) hS.le) (Nat.cast_nonneg _)
  have hkey : Real.sqrt (bEff β B / (Nin : ℝ)) * Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) = 1 := by
    rw [← Real.sqrt_mul hbE]
    have : bEff β B / (Nin : ℝ) * (Muon.sPow β 2 * gammaIn Nin B) = 1 := by
      unfold bEff gammaIn
      field_simp
    rw [this, Real.sqrt_one]
  rw [def_app_os_objects_iv_nu C hB]
  intro ρ hρ
  refine ⟨?_, ?_⟩
  · rw [cfc_map_spectrum (fun μ : ℝ => thetaRidge br (hatNu (Muon.nuOut C B) (gammaOut Nout B))
      ((Nout : ℝ) / Nin) ρ μ) C.Sout (show IsSelfAdjoint C.Sout from C.psdOut.isHermitian)
      (hfin.continuousOn (fun μ : ℝ => thetaRidge br (hatNu (Muon.nuOut C B) (gammaOut Nout B))
        ((Nout : ℝ) / Nin) ρ μ))]
    rintro _ ⟨μ, hμ, rfl⟩
    exact ⟨(hθ ρ hρ μ (hnn μ hμ)).1, (hθ ρ hρ μ (hnn μ hμ)).2⟩
  · have hcongr : cfc (fun μ : ℝ => dRidge br ρ μ) C.Sout =
        cfc (fun μ : ℝ => Real.sqrt (bEff β B / (Nin : ℝ)) *
          (thetaRidge br (hatNu (Muon.nuOut C B) (gammaOut Nout B)) ((Nout : ℝ) / Nin) ρ μ *
            dOs (hatNu (Muon.nuOut C B) (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
              (sHat β (gammaIn Nin B) ρ))) C.Sout := by
      apply cfc_congr
      intro μ hμ
      dsimp only
      rcases (hnn μ hμ).eq_or_lt with h0 | hμpos
      · subst h0
        have h1 : dRidge br ρ 0 = 0 := by simp [dRidge, kOs]
        have h2 : dOs (hatNu (Muon.nuOut C B) (gammaOut Nout B)) ((Nout : ℝ) / Nin) 0
            (sHat β (gammaIn Nin B) ρ) = 0 := by
          simp [dOs, dOsIntegrand]
        simp [h1, h2]
      · have hD := hpos ρ hρ μ hμpos
        have hθdef : thetaRidge br (hatNu (Muon.nuOut C B) (gammaOut Nout B)) ((Nout : ℝ) / Nin)
            ρ μ = Real.sqrt (Muon.sPow β 2 * gammaIn Nin B) * dRidge br ρ μ /
              dOs (hatNu (Muon.nuOut C B) (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
                (sHat β (gammaIn Nin B) ρ) := by
          unfold thetaRidge
          rw [if_neg hμpos.ne']
        rw [hθdef, div_mul_cancel₀ _ hD.ne', ← mul_assoc, hkey, one_mul]
    rw [hcongr,
      cfc_const_mul (Real.sqrt (bEff β B / (Nin : ℝ)))
        (fun μ : ℝ => thetaRidge br (hatNu (Muon.nuOut C B) (gammaOut Nout B)) ((Nout : ℝ) / Nin) ρ μ *
          dOs (hatNu (Muon.nuOut C B) (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
            (sHat β (gammaIn Nin B) ρ)) C.Sout
        (hfin.continuousOn (fun μ : ℝ => thetaRidge br (hatNu (Muon.nuOut C B) (gammaOut Nout B))
            ((Nout : ℝ) / Nin) ρ μ * dOs (hatNu (Muon.nuOut C B) (gammaOut Nout B)) ((Nout : ℝ) / Nin)
            μ (sHat β (gammaIn Nin B) ρ))),
      cfc_mul (fun μ : ℝ => thetaRidge br (hatNu (Muon.nuOut C B) (gammaOut Nout B))
          ((Nout : ℝ) / Nin) ρ μ)
        (fun μ : ℝ => dOs (hatNu (Muon.nuOut C B) (gammaOut Nout B)) ((Nout : ℝ) / Nin) μ
          (sHat β (gammaIn Nin B) ρ)) C.Sout
        (hfin.continuousOn (fun μ : ℝ => thetaRidge br (hatNu (Muon.nuOut C B) (gammaOut Nout B))
          ((Nout : ℝ) / Nin) ρ μ))
        (hfin.continuousOn (fun μ : ℝ => dOs (hatNu (Muon.nuOut C B) (gammaOut Nout B))
          ((Nout : ℝ) / Nin) μ (sHat β (gammaIn Nin B) ρ)))]

/-- Private helper (P-G2.7.P5): the square-case empirical measure is a probability measure
when there is at least one eigenvalue index. -/
private lemma os3_prob {N : ℕ} (C : Muon.Covariances N N) (i : Fin N) :
    IsProbabilityMeasure (nuHatOut C) := by
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hN0 : (N : ENNReal) ≠ 0 := by exact_mod_cast hNpos.ne'
  refine ⟨?_⟩
  unfold nuHatOut
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, Measure.dirac_apply_of_mem,
    Set.mem_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel hN0 (ENNReal.natCast_ne_top N)

/-- Private helper (P-G2.7.P5): `ν̂_out` gives no mass to the negatives. -/
private lemma os3_ae {N : ℕ} (C : Muon.Covariances N N) : nuHatOut C (Set.Iio 0) = 0 := by
  have hnn : ∀ j, 0 ≤ eigOut C j := fun j => C.psdOut.eigenvalues_nonneg j
  unfold nuHatOut
  simp [Measure.coe_finset_sum, Finset.sum_apply, Measure.dirac_apply' _ measurableSet_Iio,
    Set.indicator_apply, fun j => not_lt.2 (hnn j)]

/-- Private helper (P-G2.7.P5): integral against `ν̂_out` as a finite sum over eigenvalues. -/
private lemma os3_integral {N : ℕ} (C : Muon.Covariances N N) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ x, f x ∂(nuHatOut C) = (N : ℝ)⁻¹ * ∑ i, f (eigOut C i) := by
  unfold nuHatOut
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv, smul_eq_mul]
  · intro i _
    exact integrable_dirac' hf.stronglyMeasurable (by simp)

/-- Private helper (P-G2.7.P5): Loewner comparison of two functional calculi of `Σ_out`,
reduced to the eigenvalues. -/
private lemma os3_cfc_le {N : ℕ} (C : Muon.Covariances N N) (f g : ℝ → ℝ)
    (hfg : ∀ i : Fin N, f (eigOut C i) ≤ g (eigOut C i)) :
    cfc f C.Sout ≤ cfc g C.Sout := by
  have hH : C.Sout.IsHermitian := C.psdOut.isHermitian
  have hsp : spectrum ℝ C.Sout = Set.range (eigOut C) := hH.spectrum_real_eq_range_eigenvalues
  have hfin : (spectrum ℝ C.Sout).Finite := by rw [hsp]; exact Set.finite_range _
  refine cfc_mono ?_ (hfin.continuousOn f) (hfin.continuousOn g)
  intro x hx
  rw [hsp] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hfg i

/-- Label `thm:app-os-sqrt`, part (iii) (square case; the square case is encoded by `Covariances N N`). Snapshot `cr-2026-10-23`. Statement verbatim (`sections/12-oversampled/section.tex` l.856–878):

\begin{theorem}[Square-root law]\label{thm:app-os-sqrt}
Let $C_*\defeq\frac12+\frac{2\log2}{\pi}\approx0.9413$.
\begin{enumerate}[label=(\roman*)]
\item For every probability measure $\nu$ and every $\mu>0$,
\[
\max\Big\{C_*\sqrt{1-m_\nu(\mu)},\ 1-m_\nu(\mu)\Big\}\sqrt{\frac\mu2}\ \le\ \mathfrak d^{\rm os}_\nu(\mu)\ \le\ \sqrt{\frac\mu2}.
\]
\item For every probability measure $\nu$, every $\mu>0$ and every $K>0$,
\[
1-m_\nu(\mu)\ge\frac{\nu([0,K\mu])}{1+K};\qquad\text{in particular}\qquad 1-m_\nu(\mu)\ge\tfrac12\,\nu([0,\mu]).
\]
\item In the square case $\Nout=\Nin$, let
$\underline{\mathfrak d}(\mu)\defeq C_*\sqrt{1-m_{\hat\nu_{\mathrm{out}}}(\mu)}\sqrt{\mu/2}$ for
$\mu>0$ and $\underline{\mathfrak d}(0)\defeq0$. Then
\[
\underline{\mathfrak d}(\Sigmaout)\preceq\mathfrak d^{\rm os}_{\hat\nu_{\mathrm{out}}}(\Sigmaout)\preceq\Big(\frac{\Sigmaout}2\Big)^{1/2},
\]
where, for $\mu_k>0$,
\[
1-m_{\hat\nu_{\mathrm{out}}}(\mu_k)=\frac1{\Nout}\sum_{l=1}^{\Nout}\frac{\mu_k}{\mu_k+\mu_l}.
\]
\end{enumerate}
\end{theorem}
-/
theorem thm_app_os_sqrt_iii {N : ℕ} (C : Muon.Covariances N N) :
    cfc (fun μ : ℝ => dUnder (nuHatOut C) μ) C.Sout ≤
        cfc (fun μ : ℝ => dOsSq (nuHatOut C) μ) C.Sout ∧
      cfc (fun μ : ℝ => dOsSq (nuHatOut C) μ) C.Sout ≤
        cfc (fun x : ℝ => Real.sqrt (x / 2)) C.Sout ∧
      ∀ k : Fin N, 0 < eigOut C k →
        1 - mNu (nuHatOut C) (eigOut C k) =
          (N : ℝ)⁻¹ * ∑ l : Fin N, eigOut C k / (eigOut C k + eigOut C l) := by
  have hnn : ∀ j, 0 ≤ eigOut C j := fun j => C.psdOut.eigenvalues_nonneg j
  have hP : ∀ i : Fin N, dUnder (nuHatOut C) (eigOut C i) ≤ dOsSq (nuHatOut C) (eigOut C i) ∧
      dOsSq (nuHatOut C) (eigOut C i) ≤ Real.sqrt (eigOut C i / 2) := by
    intro i
    haveI := os3_prob C i
    rcases (hnn i).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp [dUnder, dOsSq, dOs, dOsIntegrand]
    · have h := thm_app_os_sqrt_i (nuHatOut C) (os3_ae C) hpos
      refine ⟨?_, h.2⟩
      unfold dUnder
      rw [if_neg hpos.ne']
      exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) h.1
  refine ⟨os3_cfc_le C _ _ (fun i => (hP i).1), os3_cfc_le C _ _ (fun i => (hP i).2), ?_⟩
  intro k hk
  have hmeas : Measurable (fun x : ℝ => x / (eigOut C k + x)) := by fun_prop
  have hI := os3_integral C (fun x : ℝ => x / (eigOut C k + x)) hmeas
  unfold mNu
  rw [hI]
  have hN0 : (N : ℝ) ≠ 0 := (Nat.cast_pos.2 k.pos).ne'
  have hden : ∀ l, eigOut C k + eigOut C l ≠ 0 := fun l => (add_pos_of_pos_of_nonneg hk (hnn l)).ne'
  have hone : (N : ℝ)⁻¹ * ∑ _l : Fin N, (1 : ℝ) = 1 := by
    simp [hN0]
  have hterm : ∀ l, (1 : ℝ) - eigOut C l / (eigOut C k + eigOut C l) =
      eigOut C k / (eigOut C k + eigOut C l) := by
    intro l
    rw [one_sub_div (hden l), add_sub_cancel_right]
  calc 1 - (N : ℝ)⁻¹ * ∑ i, eigOut C i / (eigOut C k + eigOut C i)
      = (N : ℝ)⁻¹ * ∑ _l : Fin N, (1 : ℝ) - (N : ℝ)⁻¹ * ∑ i, eigOut C i / (eigOut C k + eigOut C i) := by
        rw [hone]
    _ = (N : ℝ)⁻¹ * ∑ i : Fin N, (1 - eigOut C i / (eigOut C k + eigOut C i)) := by
        rw [← mul_sub, Finset.sum_sub_distrib]
    _ = (N : ℝ)⁻¹ * ∑ l : Fin N, eigOut C k / (eigOut C k + eigOut C l) := by
        simp only [hterm]

/-- Private helper (P-G2.7.P6): mass of a closed interval `[0,a]` under `ν̂_out`, as a count. -/
private lemma os4_mass {N : ℕ} (C : Muon.Covariances N N) (a : ℝ) :
    (nuHatOut C (Icc 0 a)).toReal =
      (N : ℝ)⁻¹ * ((Finset.univ.filter fun k => 0 ≤ eigOut C k ∧ eigOut C k ≤ a).card : ℝ) := by
  unfold nuHatOut
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply' _ measurableSet_Icc, Set.indicator_apply, Pi.one_apply, smul_eq_mul,
    Finset.sum_boole, Set.mem_Icc]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-- Private helper (P-G2.7.P6): `√(B_eff/(2N)) √μ = √(B_eff/N) √(μ/2)`. -/
private lemma os4_sqrt (β : ℝ) (B N : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) :
    Real.sqrt (bEff β B / (2 * (N : ℝ))) * Real.sqrt μ =
      Real.sqrt (bEff β B / (N : ℝ)) * Real.sqrt (μ / 2) := by
  rw [← Real.sqrt_mul' _ hμ, ← Real.sqrt_mul' _ (div_nonneg hμ (by norm_num))]
  congr 1
  ring

/-- Label `cor:app-os-packed`, part (i) (upper bound). Snapshot `cr-2026-10-23`. Statement verbatim (`sections/12-oversampled/section.tex` l.974–986):

\begin{corollary}[Packed modes]\label{cor:app-os-packed}
Assume $\Nout=\Nin=N$ and $\epsilon_{\rm os}<1$, and let $\mathfrak d_i(0)$ be the
zero-ridge coefficient of \cref{thm:app-os-limit}(ii). For every mode with
$\mu_i>0$,
\[
\mathfrak d_i(0)\le\frac1{1-\epsilon_{\rm os}}\sqrt{\frac{B_{\rm eff}}{2N}}\,\sqrt{\mu_i},
\]
and if $\mu_i$ is $(K,\delta)$-packed, then
\[
\mathfrak d_i(0)\ge(1-\epsilon_{\rm os})\,C_*\sqrt{\frac{\delta}{1+K}}\,\sqrt{\frac{B_{\rm eff}}{2N}}\,\sqrt{\mu_i},
\qquad C_*=\frac12+\frac{2\log2}\pi .
\]
\end{corollary}
-/
theorem cor_app_os_packed_i {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 1 ≤ N) (hB : 1 ≤ B) (C : Muon.Covariances N N)
    (hSin : C.Sin = 1) (hcond : 0 < β ∨ (β = 0 ∧ gammaIn N B < 1))
    {qs : ℝ} (hqs : 0 < qs ∧ qs * Muon.DetEquiv.Fw (Muon.emaW β) qs = gammaIn N B)
    (hε : epsOs β (gammaIn N B) < 1)
    (br : HalfAnisoBranch β (gammaIn N B) (Muon.nuOut C B)) (hbr : IsModelBranch C B hB β br)
    (i : Fin N) (hμ : 0 < eigOut C i) :
    dZero br (eigOut C i) ≤
      (1 - epsOs β (gammaIn N B))⁻¹ * Real.sqrt (bEff β B / (2 * (N : ℝ))) *
        Real.sqrt (eigOut C i) := by
  haveI := os3_prob C i
  have hμ : 0 < eigOut C i := hμ
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hsq1 := (thm_app_os_sqrt_i (nuHatOut C) (os3_ae C) hμ).2
  have hε1 : 0 ≤ 1 - epsOs β (gammaIn N B) := by linarith [hε]
  obtain ⟨ϑ, hϑ, hϑeq⟩ :=
    (thm_app_os_limit_iii hβ0 hβ1 hN hN hB C hSin hcond hqs hε br hbr).2.1 0 le_rfl i
  have h11 : (N : ℝ) / (N : ℝ) = 1 := div_self hNpos.ne'
  have hs0 : sHat β (gammaIn N B) 0 = 0 := by simp [sHat]
  have hz : dZero br (eigOut C i) = dRidge br 0 (eigOut C i) := by simp [dZero, dRidge]
  have key : dZero br (eigOut C i) =
      ϑ * Real.sqrt (bEff β B / (N : ℝ)) * dOsSq (nuHatOut C) (eigOut C i) := by
    rw [hz, hϑeq, h11, hs0]
    rfl
  have hs : 0 ≤ Real.sqrt (bEff β B / (N : ℝ)) := Real.sqrt_nonneg _
  have hϑ0 : 0 ≤ ϑ := le_trans hε1 hϑ.1
  calc dZero br (eigOut C i)
      = ϑ * Real.sqrt (bEff β B / (N : ℝ)) * dOsSq (nuHatOut C) (eigOut C i) := key
    _ ≤ ϑ * Real.sqrt (bEff β B / (N : ℝ)) * Real.sqrt (eigOut C i / 2) :=
        mul_le_mul_of_nonneg_left hsq1 (mul_nonneg hϑ0 hs)
    _ ≤ (1 - epsOs β (gammaIn N B))⁻¹ * Real.sqrt (bEff β B / (N : ℝ)) *
          Real.sqrt (eigOut C i / 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hϑ.2 hs) (Real.sqrt_nonneg _)
    _ = (1 - epsOs β (gammaIn N B))⁻¹ * Real.sqrt (bEff β B / (2 * (N : ℝ))) *
          Real.sqrt (eigOut C i) := by
        linear_combination (-(1 - epsOs β (gammaIn N B))⁻¹) * os4_sqrt β B N hμ.le

/-- Label `cor:app-os-packed`, part (ii) (lower bound). Snapshot `cr-2026-10-23`. Statement verbatim (`sections/12-oversampled/section.tex` l.974–986):

\begin{corollary}[Packed modes]\label{cor:app-os-packed}
Assume $\Nout=\Nin=N$ and $\epsilon_{\rm os}<1$, and let $\mathfrak d_i(0)$ be the
zero-ridge coefficient of \cref{thm:app-os-limit}(ii). For every mode with
$\mu_i>0$,
\[
\mathfrak d_i(0)\le\frac1{1-\epsilon_{\rm os}}\sqrt{\frac{B_{\rm eff}}{2N}}\,\sqrt{\mu_i},
\]
and if $\mu_i$ is $(K,\delta)$-packed, then
\[
\mathfrak d_i(0)\ge(1-\epsilon_{\rm os})\,C_*\sqrt{\frac{\delta}{1+K}}\,\sqrt{\frac{B_{\rm eff}}{2N}}\,\sqrt{\mu_i},
\qquad C_*=\frac12+\frac{2\log2}\pi .
\]
\end{corollary}
-/
theorem cor_app_os_packed_ii {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 1 ≤ N) (hB : 1 ≤ B) (C : Muon.Covariances N N)
    (hSin : C.Sin = 1) (hcond : 0 < β ∨ (β = 0 ∧ gammaIn N B < 1))
    {qs : ℝ} (hqs : 0 < qs ∧ qs * Muon.DetEquiv.Fw (Muon.emaW β) qs = gammaIn N B)
    (hε : epsOs β (gammaIn N B) < 1)
    (br : HalfAnisoBranch β (gammaIn N B) (Muon.nuOut C B)) (hbr : IsModelBranch C B hB β br)
    {K δ : ℝ} (hK : 1 ≤ K) (hδ : 0 < δ ∧ δ ≤ 1) (i : Fin N)
    (hp : def_app_os_packed K δ (eigOut C) i) :
    (1 - epsOs β (gammaIn N B)) * cStar * Real.sqrt (δ / (1 + K)) *
        Real.sqrt (bEff β B / (2 * (N : ℝ))) * Real.sqrt (eigOut C i) ≤
      dZero br (eigOut C i) := by
  unfold def_app_os_packed at hp
  obtain ⟨hμ, hcard⟩ := hp
  haveI := os3_prob C i
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hK0 : 0 < K := by linarith
  have h1K : 0 < 1 + K := by linarith
  have hsq1 := thm_app_os_sqrt_i (nuHatOut C) (os3_ae C) hμ
  have hsq2 := thm_app_os_sqrt_ii (nuHatOut C) (os3_ae C) hμ hK0
  have hε1 : 0 ≤ 1 - epsOs β (gammaIn N B) := by linarith [hε]
  -- counting: the packed count is at most the count of the interval [0, K μ_i]
  have hcardle : ((Finset.univ.filter fun k => eigOut C k ≤ K * eigOut C i).card : ℝ) ≤
      ((Finset.univ.filter fun k => 0 ≤ eigOut C k ∧ eigOut C k ≤ K * eigOut C i).card : ℝ) := by
    apply Nat.cast_le.2
    apply Finset.card_le_card
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, C.psdOut.eigenvalues_nonneg k, hk.2⟩
  have hmass : δ ≤ (nuHatOut C (Icc 0 (K * eigOut C i))).toReal := by
    rw [os4_mass]
    have h1 : δ * (N : ℝ) ≤
        ((Finset.univ.filter fun k => 0 ≤ eigOut C k ∧ eigOut C k ≤ K * eigOut C i).card : ℝ) :=
      le_trans hcard hcardle
    calc δ = (N : ℝ)⁻¹ * (δ * (N : ℝ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hNpos.le)
  have hm0 : δ / (1 + K) ≤ (nuHatOut C (Icc 0 (K * eigOut C i))).toReal / (1 + K) :=
    div_le_div_of_nonneg_right hmass h1K.le
  have hm : δ / (1 + K) ≤ 1 - mNu (nuHatOut C) (eigOut C i) := le_trans hm0 hsq2.1
  have hsqrtm : Real.sqrt (δ / (1 + K)) ≤ Real.sqrt (1 - mNu (nuHatOut C) (eigOut C i)) :=
    Real.sqrt_le_sqrt hm
  have hc : 0 < cStar := by
    unfold cStar
    have h1 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have h2 : 0 < 2 * Real.log 2 / Real.pi := div_pos (by linarith) Real.pi_pos
    linarith
  have hD : cStar * Real.sqrt (δ / (1 + K)) * Real.sqrt (eigOut C i / 2) ≤
      dOsSq (nuHatOut C) (eigOut C i) :=
    calc cStar * Real.sqrt (δ / (1 + K)) * Real.sqrt (eigOut C i / 2)
        ≤ cStar * Real.sqrt (1 - mNu (nuHatOut C) (eigOut C i)) * Real.sqrt (eigOut C i / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrtm hc.le)
            (Real.sqrt_nonneg _)
      _ ≤ max (cStar * Real.sqrt (1 - mNu (nuHatOut C) (eigOut C i)))
            (1 - mNu (nuHatOut C) (eigOut C i)) * Real.sqrt (eigOut C i / 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      _ ≤ dOsSq (nuHatOut C) (eigOut C i) := hsq1.1
  have hD0 : 0 ≤ dOsSq (nuHatOut C) (eigOut C i) :=
    le_trans (mul_nonneg (mul_nonneg hc.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) hD
  obtain ⟨ϑ, hϑ, hϑeq⟩ :=
    (thm_app_os_limit_iii hβ0 hβ1 hN hN hB C hSin hcond hqs hε br hbr).2.1 0 le_rfl i
  have h11 : (N : ℝ) / (N : ℝ) = 1 := div_self hNpos.ne'
  have hs0 : sHat β (gammaIn N B) 0 = 0 := by simp [sHat]
  have hz : dZero br (eigOut C i) = dRidge br 0 (eigOut C i) := by simp [dZero, dRidge]
  have key : dZero br (eigOut C i) =
      ϑ * Real.sqrt (bEff β B / (N : ℝ)) * dOsSq (nuHatOut C) (eigOut C i) := by
    rw [hz, hϑeq, h11, hs0]
    rfl
  have hs : 0 ≤ Real.sqrt (bEff β B / (N : ℝ)) := Real.sqrt_nonneg _
  have hϑ1 : 1 - epsOs β (gammaIn N B) ≤ ϑ := hϑ.1
  calc (1 - epsOs β (gammaIn N B)) * cStar * Real.sqrt (δ / (1 + K)) *
        Real.sqrt (bEff β B / (2 * (N : ℝ))) * Real.sqrt (eigOut C i)
      = (1 - epsOs β (gammaIn N B)) * Real.sqrt (bEff β B / (N : ℝ)) *
          (cStar * Real.sqrt (δ / (1 + K)) * Real.sqrt (eigOut C i / 2)) := by
        linear_combination ((1 - epsOs β (gammaIn N B)) * cStar * Real.sqrt (δ / (1 + K))) *
          os4_sqrt β B N hμ.le
    _ ≤ (1 - epsOs β (gammaIn N B)) * Real.sqrt (bEff β B / (N : ℝ)) *
          dOsSq (nuHatOut C) (eigOut C i) :=
        mul_le_mul_of_nonneg_left hD (mul_nonneg hε1 hs)
    _ ≤ ϑ * Real.sqrt (bEff β B / (N : ℝ)) * dOsSq (nuHatOut C) (eigOut C i) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hϑ1 hs) hD0
    _ = dZero br (eigOut C i) := key.symm

/-- Private helper (P-G2.7.P7): with `Σ_out = 1` every output eigenvalue equals `1`. -/
private lemma os5_eig_one {N : ℕ} (C : Muon.Covariances N N) (hId : C.Sout = 1) (i : Fin N) :
    eigOut C i = 1 := by
  have hsp : spectrum ℝ C.Sout = Set.range (eigOut C) :=
    C.psdOut.isHermitian.spectrum_real_eq_range_eigenvalues
  have hne : Nonempty (Fin N) := ⟨i⟩
  have hmem : eigOut C i ∈ Set.range (eigOut C) := ⟨i, rfl⟩
  rw [← hsp, hId, spectrum.one_eq] at hmem
  exact Set.mem_singleton_iff.mp hmem

/-- Private helper (P-G2.7.P7): with `Σ_out = 1` the square-case empirical measure is `δ_1`. -/
private lemma os5_nuHat_dirac {N : ℕ} (C : Muon.Covariances N N) (hN : 1 ≤ N)
    (hId : C.Sout = 1) : nuHatOut C = Measure.dirac 1 := by
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hsum : ∑ i : Fin N, Measure.dirac (eigOut C i) = N • Measure.dirac (1 : ℝ) := by
    simp [os5_eig_one C hId]
  unfold nuHatOut
  rw [hsum, ← Nat.cast_smul_eq_nsmul ℝ≥0∞ N, smul_smul,
    ENNReal.inv_mul_cancel hN0 (ENNReal.natCast_ne_top N), one_smul]

/-- Label `cor:app-os-identity`, part (ii). Snapshot `cr-2026-10-23`. Statement verbatim (`sections/12-oversampled/section.tex` l.1486–1494):

\begin{corollary}[Identity covariance]\label{cor:app-os-identity}
\begin{enumerate}[label=(\roman*)]
\item One has $\mathfrak d^{\rm os}_{\delta_1}(1)=\dfrac{4\sqrt2}{3\pi}=\dfrac{8}{3\pi\sqrt2}$.
\item If $\Sigmaout=\Id_N$, $\Nout=\Nin=N$, $\gamma=N/B$ and $\epsilon_{\rm os}<1$, then
\[
\mathfrak d_0(1)=\frac{8\,\vartheta}{3\pi\sqrt{2\sw2\gamma}}\qquad\text{for some }\vartheta\in\big[1-\epsilon_{\rm os},(1-\epsilon_{\rm os})^{-1}\big].
\]
\end{enumerate}
\end{corollary}
-/
theorem cor_app_os_identity_ii {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 1 ≤ N) (hB : 1 ≤ B) (C : Muon.Covariances N N)
    (hSin : C.Sin = 1) (hId : C.Sout = 1) (hcond : 0 < β ∨ (β = 0 ∧ gammaIn N B < 1))
    {qs : ℝ} (hqs : 0 < qs ∧ qs * Muon.DetEquiv.Fw (Muon.emaW β) qs = gammaIn N B)
    (hε : epsOs β (gammaIn N B) < 1)
    (br : HalfAnisoBranch β (gammaIn N B) (Muon.nuOut C B)) (hbr : IsModelBranch C B hB β br) :
    ∃ ϑ : ℝ, ϑ ∈ Icc (1 - epsOs β (gammaIn N B)) (1 - epsOs β (gammaIn N B))⁻¹ ∧
      dZero br 1 = 8 * ϑ / (3 * Real.pi * Real.sqrt (2 * Muon.sPow β 2 * gammaIn N B)) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  obtain ⟨ϑ, hϑ, h⟩ :=
    (thm_app_os_limit_iii hβ0 hβ1 hN hN hB C hSin hcond hqs hε br hbr).2.1 0 le_rfl ⟨0, hN⟩
  refine ⟨ϑ, hϑ, ?_⟩
  have h11 : (N : ℝ) / (N : ℝ) = 1 := div_self hN0
  have hs0 : sHat β (gammaIn N B) 0 = 0 := by simp [sHat]
  have hz : dZero br 1 = dRidge br 0 1 := by simp [dZero, dRidge]
  have he : eigOut C ⟨0, hN⟩ = 1 := os5_eig_one C hId _
  rw [he, h11, hs0, os5_nuHat_dirac C hN hId] at h
  have hd : dOs (Measure.dirac (1 : ℝ)) 1 1 0 = 4 * Real.sqrt 2 / (3 * Real.pi) :=
    cor_app_os_identity_i.1
  rw [hz, h, hd]
  have hS : 0 < Muon.sPow β 2 := by
    rw [Muon.sPow_two hβ0 hβ1]
    apply div_pos <;> linarith
  have hγ : 0 < gammaIn N B := by
    unfold gammaIn
    exact div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))
  have hS' : Muon.sPow β 2 ≠ 0 := hS.ne'
  have hSγ : 0 < Muon.sPow β 2 * gammaIn N B := mul_pos hS hγ
  have ht : 0 < Real.sqrt (Muon.sPow β 2 * gammaIn N B) := Real.sqrt_pos.2 hSγ
  have ht' : Real.sqrt (Muon.sPow β 2 * gammaIn N B) ≠ 0 := ht.ne'
  have ht2 : Real.sqrt (Muon.sPow β 2 * gammaIn N B) ^ 2 = Muon.sPow β 2 * gammaIn N B :=
    Real.sq_sqrt hSγ.le
  have hb : Real.sqrt (bEff β B / (N : ℝ)) = 1 / Real.sqrt (Muon.sPow β 2 * gammaIn N B) := by
    have key : bEff β B / (N : ℝ) = (1 / Real.sqrt (Muon.sPow β 2 * gammaIn N B)) ^ 2 := by
      rw [div_pow, one_pow, ht2]
      unfold bEff gammaIn
      field_simp
    rw [key, Real.sqrt_sq (by positivity)]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2p : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hsq : Real.sqrt (2 * Muon.sPow β 2 * gammaIn N B) =
      Real.sqrt 2 * Real.sqrt (Muon.sPow β 2 * gammaIn N B) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_assoc]
  rw [hb, hsq, show (8 : ℝ) = 4 * Real.sqrt 2 * Real.sqrt 2 by rw [mul_assoc, h2]; norm_num]
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  try ring

/-- Label `rem:app-os-normalization`, promoted display only (l.1536–1539; the remark's "≈" displays stay out of scope). Snapshot `cr-2026-10-23`. Statement verbatim:

\[
\mathfrak d_i(0)=\sqrt{\frac{B_{\rm eff}}{N}}\;\vartheta_i\,\chi_{\hat\nu_{\mathrm{out}}}(\mu_i)\,\sqrt{\frac{\mu_i}2},
\qquad\vartheta_i\in\big[1-\epsilon_{\rm os},(1-\epsilon_{\rm os})^{-1}\big].
\]
-/
theorem rem_app_os_normalization {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 1 ≤ N) (hB : 1 ≤ B) (C : Muon.Covariances N N)
    (hSin : C.Sin = 1) (hcond : 0 < β ∨ (β = 0 ∧ gammaIn N B < 1))
    {qs : ℝ} (hqs : 0 < qs ∧ qs * Muon.DetEquiv.Fw (Muon.emaW β) qs = gammaIn N B)
    (hε : epsOs β (gammaIn N B) < 1)
    (br : HalfAnisoBranch β (gammaIn N B) (Muon.nuOut C B)) (hbr : IsModelBranch C B hB β br) :
    ∀ i : Fin N, ∃ ϑ : ℝ, ϑ ∈ Icc (1 - epsOs β (gammaIn N B)) (1 - epsOs β (gammaIn N B))⁻¹ ∧
      dZero br (eigOut C i) =
        Real.sqrt (bEff β B / (N : ℝ)) * ϑ * sqrtEff (nuHatOut C) (eigOut C i) *
          Real.sqrt (eigOut C i / 2) := by
  intro i
  obtain ⟨ϑ, hϑ, h⟩ :=
    (thm_app_os_limit_iii hβ0 hβ1 hN hN hB C hSin hcond hqs hε br hbr).2.1 0 le_rfl i
  refine ⟨ϑ, hϑ, ?_⟩
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have h11 : (N : ℝ) / (N : ℝ) = 1 := div_self hN0
  have hs0 : sHat β (gammaIn N B) 0 = 0 := by simp [sHat]
  have hz : dZero br (eigOut C i) = dRidge br 0 (eigOut C i) := by simp [dZero, dRidge]
  rw [hz, h, h11, hs0]
  haveI : IsProbabilityMeasure (nuHatOut C) := os3_prob C i
  have hd : dOs (nuHatOut C) 1 (eigOut C i) 0 = dOsSq (nuHatOut C) (eigOut C i) := rfl
  have hnn : 0 ≤ eigOut C i := C.psdOut.eigenvalues_nonneg i
  rcases hnn.lt_or_eq with hpos | hzero
  · rw [hd, lem_app_os_repr_ii (nuHatOut C) (os3_ae C) hpos]
    ring
  · rw [← hzero]
    simp [dOs, dOsIntegrand]

end

end Muon.Oversampled

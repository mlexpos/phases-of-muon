import Muon.Volatility.Modes
import Muon.Volatility.Closed.Path
import Muon.Volatility.LagKernel

/-!
# Appendix D, work package L-D.18: the closed-form lag kernel, its bounds, reductions and lag sums

Work package L-D.18 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/04-volatility/section.tex`: the two-point quantities and the determinant (l.1466–1493),
`thm:app-vol-closed-kernel` (l.1509–1523), `cor:app-vol-closed-bounds` (l.1525–1551),
`prop:app-vol-closed-reductions` (l.1553–1576), `thm:app-vol-closed-filtered` (l.1578–1594),
`cor:app-vol-closed-modes` (l.1604–1638), `prop:app-vol-closed-lagsum` (l.1640–1674), and the
forward definitions `eqn:app-vol-traces`, `eqn:app-vol-Upsilon`, `eqn:app-vol-kernel`,
`eqn:app-vol-Zk` (l.3120–3145), which L-D.19 shares.
Card: `sections/04-volatility/CARD.md` §2, §3 (rows of these six labels), §5 (row L-D.18), §6.

Reused, not redefined: `closedModeH`, `closedModeCl` (`Muon.Volatility.Modes`, L-D.14, admitted);
`profileF`, `pairedB`, `pairedE`, `branchPt`, `toutT`, `tinT`, `profileDelta`, `thetaSigma`,
`kappaSigma`, `qhatBeta`, `epsBeta`, `emaXi₁`, `emaXi₂`, `cutoffXi`, `IsStdGaussianFamily`
(`Muon.Volatility.Closed.Profile`); `profileKernel`, `lagRespCut`-level path facts
(`Muon.Volatility.Closed.Path`); `lagResp`, `lagRespCut`, `lagGammaBar`, `classDiag`, `modeVij`
(`Muon.Volatility.LagKernel`); `iotaF`, `omegaF`, `IsOddBddLip` (`OddSpectral`); `SizeFin`
(`Defs`); `Rbar`, `Rtbar`, `branchSol`, `Fw`, `classK` (`Muon.DetEquiv`); `emaW`, `sPow`,
`opNorm`, `Covariances`, `nuOut`, `nuIn` (`Muon.Foundations.Conventions`).

Encoding decisions:
* Every closed-form statement is at the level of the paired profile (`profileKernel`, `profileDelta`
  at the EMA profile `emaXi₁`, `emaXi₂` of lag `ℓ`, with branch points `emaBr1`, `emaBr2`). The
  lag kernel itself is `lagResp` at the diagonal tests `Fd`, `Gd` (`thm_app_vol_closed_kernel_ii`
  identifies the two). Test matrices `Fm`, `Gm` enter only through `hFd`, `hGd`.
* The two-resolvent kernel `eqn:app-vol-kernel` is written over the full spectral branch
  (`Muon.DetEquiv.branchSol` at `Fw (emaW β)`, the spectral measures `ν, ν'` as `FiniteMeasure ℝ`
  with `hν`, `hν'`), as in `volraw`. The bridge from the profile branch to the full branch is
  `lem_app_vol_closed_branch_ema_two` (the `ξ₂` analogue of `lem_app_vol_closed_branch_ema`) and
  `nu_pair_mem_classK` (the spectral measures lie in `𝒦`).
* Derivatives of `F_w` and `r_w` are the explicit series of `lem:app-vol-closed-profile`(a) and
  `lem:app-de-scalar`(iii) (`fwNegDeriv`, `rwDeriv`), not `deriv`, so no junk value at `q = 0`.
* Standing assumptions: `SizeFin` as a top-level hypothesis on every statement that uses the
  closed form (the source fixes the dimension and `γ⋆, C_Σ` throughout the subsection), `1 ≤ C_Σ`
  where `lagResp` existence is used, `IsStdGaussianFamily` for every Gaussian family. Lag-indexed
  Gaussian families are `g : ∀ ℓ, ℕ ⊕ Fin ℓ → Ω → ℝ`, as the EMA profile at each lag has its own
  fresh labels.
* Positivity of the matrices enters as `Matrix.PosSemidef` (`Fm.PosSemidef`), not as signs of
  eigenvalues. Eigenvalues `μ`, `λ` are taken from `Set.range S.μ`, `Set.range S.lam`.
* Sums and integrals carry their conjuncts: `Summable` for each lag series, `IntegrableOn` for each
  double integral, `Tendsto` for each `lagResp` limit (the value is junk without it).
* Quantifier order: the constants `clagConst β γ`, `thetaSigma`, `kappaSigma` depend only on the
  data named in their arguments, and every bound is stated for all `s, u, ϱ` after the
  constants.
-/

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped Matrix MatrixOrder
open Matrix
open Muon Muon.Setup Muon.DetEquiv

noncomputable section

namespace Muon.Volatility

/-! ## Scalar objects of the closed form -/

/-- `φ_q(x) = x / (1 + q x²)`, the summand of `b_ℓ` in `prop:app-vol-closed-lagsum`. Snapshot `cr-2026-10-23`. -/
def phiQ (q x : ℝ) : ℝ := x / (1 + q * x ^ 2)

/-- `ψ_q(x) = x² / (1 + q x²)`, the summand of `e_ℓ` in `prop:app-vol-closed-lagsum`. Snapshot `cr-2026-10-23`. -/
def psiQ (q x : ℝ) : ℝ := x ^ 2 / (1 + q * x ^ 2)

/-- The lag weights `c_0 = 1` and `c_ℓ = 2` for `ℓ ≥ 1` (`prop:app-vol-closed-lagsum`). Snapshot `cr-2026-10-23`. -/
def lagCoef (ℓ : ℕ) : ℝ := if ℓ = 0 then 1 else 2

/-- `-F'_w(q) = ∑_j w_j⁴ 𝔼[g⁴ (1 + w_j² q g²)⁻²]` with `w_j = emaW β j` and `g ∼ N(0,1)`, the
second term of `eqn:app-vol-Upsilon` (`lem:app-vol-closed-profile`(a)). Snapshot `cr-2026-10-23`.
-/
def fwNegDeriv (β q : ℝ) : ℝ :=
  ∑' j : ℕ, Muon.emaW β j ^ 4 * ∫ g, g ^ 4 / (1 + q * Muon.emaW β j ^ 2 * g ^ 2) ^ 2 ∂(gaussianReal 0 1)

/-- `r'_w(q) = ∑_j w_j² 𝔼[g² (1 + w_j² q g²)⁻²]` (`lem:app-de-scalar`(iii), the derivative of
`r_w(q) = q F_w(q)`), as in `eqn:app-vol-Upsilon`. Snapshot `cr-2026-10-23`.
-/
def rwDeriv (β q : ℝ) : ℝ :=
  ∑' j : ℕ, Muon.emaW β j ^ 2 * ∫ g, g ^ 2 / (1 + q * Muon.emaW β j ^ 2 * g ^ 2) ^ 2 ∂(gaussianReal 0 1)

/-- `clagConst β γ` of `cor:app-vol-closed-bounds`(iv): `C^lag_β = γ⋆/4` for `β = 0` and
`max(γ⋆/4, 4 sw₂ q̂_β ε_β⁻²)` for `0 < β < 1`, where `sw₂ = ∑_j emaw_j²`. It depends only on
`(β, γ⋆)`. Snapshot `cr-2026-10-23`.
-/
def clagConst (β γ : ℝ) : ℝ :=
  if β = 0 then γ / 4 else max (γ / 4) (4 * Muon.sPow β 2 * qhatBeta β γ / epsBeta β γ ^ 2)

/-! ## Two-point quantities over the full spectral branch (`eqn:app-vol-traces`, `eqn:app-vol-kernel`) -/

/-- `𝒯^out_p(s,u) = (1/B) Tr(Σ_out^p R̄(-s) R̄(-u))`, `p ∈ {1, 2}` (`eqn:app-vol-traces`). Snapshot `cr-2026-10-23`. -/
def trOutP (β : ℝ) {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ) (ν ν' : FiniteMeasure ℝ)
    (p : ℕ) (s u : ℝ) : ℝ :=
  (B : ℝ)⁻¹ * ((C.Sout ^ p) * Rbar (Fw (Muon.emaW β)) ν ν' C s * Rbar (Fw (Muon.emaW β)) ν ν' C u).trace

/-- `𝒯^in_p(s,u) = (1/B) Tr(Σ_in^p R̃̄(-s) R̃̄(-u))`, `p ∈ {1, 2}` (`eqn:app-vol-traces`). Snapshot `cr-2026-10-23`. -/
def trInP (β : ℝ) {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ) (ν ν' : FiniteMeasure ℝ)
    (p : ℕ) (s u : ℝ) : ℝ :=
  (B : ℝ)⁻¹ * ((C.Sin ^ p) * Rtbar (Fw (Muon.emaW β)) ν ν' C s * Rtbar (Fw (Muon.emaW β)) ν ν' C u).trace

/-- `Υ(s)` of `eqn:app-vol-Upsilon`, with `q = s σ(-s) σ̃(-s)` from the full branch at `s`
(`σ` the first and `σ̃` the second coordinate of `branchSol`), `Fw'(q) = -fwNegDeriv` and
`r'_β(q) = rwDeriv`. Snapshot `cr-2026-10-23`.
-/
def upsilonK (β : ℝ) {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ) (ν ν' : FiniteMeasure ℝ)
    (s : ℝ) : ℝ :=
  let x := branchSol (Fw (Muon.emaW β)) ν ν' s
  let q := s * x.1 * x.2.1
  (1 + s ^ 2 * x.2.1 ^ 2 * (-fwNegDeriv β q) * trOutP β C B ν ν' 2 s s) *
      (1 + s ^ 2 * x.1 ^ 2 * (-fwNegDeriv β q) * trInP β C B ν ν' 2 s s) -
    s ^ 2 * rwDeriv β q ^ 2 * trOutP β C B ν ν' 2 s s * trInP β C B ν ν' 2 s s

/-- The two-resolvent kernel `𝔨(s,u)` of `eqn:app-vol-kernel`: the off-diagonal formula for
`s ≠ u` and the diagonal formula (with `Υ`) for `s = u`. The fourth branch coordinate is `s₁`, the
third `s̃₁`, both over the full branch. Snapshot `cr-2026-10-23`.
-/
def kernelK (β : ℝ) {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ) (ν ν' : FiniteMeasure ℝ)
    (s u : ℝ) : ℝ :=
  let x := branchSol (Fw (Muon.emaW β)) ν ν' s
  let y := branchSol (Fw (Muon.emaW β)) ν ν' u
  if s = u then
    s ^ 2 * rwDeriv β (s * x.1 * x.2.1) * trOutP β C B ν ν' 2 s s * trInP β C B ν ν' 2 s s /
      upsilonK β C B ν ν' s
  else
    trOutP β C B ν ν' 2 s u * trInP β C B ν ν' 2 s u *
      (u * x.2.2.2 - s * y.2.2.2) / ((u - s) * trOutP β C B ν ν' 1 s u)

/-- The total `𝔷_𝔨(ϱ) = (4/π²) ∫_0^∞∫_0^∞ 𝔨(ϱ+x², ϱ+y²) dx dy` of `eqn:app-vol-Zk` (the integrability
is a theorem of L-D.19). Snapshot `cr-2026-10-23`.
-/
def zkK (β : ℝ) {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ) (ν ν' : FiniteMeasure ℝ) (ϱ : ℝ) :
    ℝ :=
  (4 / Real.pi ^ 2) * ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), kernelK β C B ν ν' (ϱ + x ^ 2) (ϱ + y ^ 2)

/-! ## The EMA paired profile at lag `ℓ`: branch points and two-point functions -/

/-- The branch point of the first EMA profile at lag `ℓ` at `s` (`def:app-vol-closed-profile`, EMA
paragraph): the branch of `F_{ξ₁} = F_w` at `s`. Snapshot `cr-2026-10-23`.
-/
def emaBr1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {m n : ℕ} (C : Muon.Covariances m n)
    (B : ℕ) (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (s : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  branchPt (profileF P (emaXi₁ β ℓ g)) C B s

/-- The branch point of the second EMA profile at lag `ℓ` at `s` (the `ξ₂` analogue of `emaBr1`). Snapshot `cr-2026-10-23`. -/
def emaBr2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {m n : ℕ} (C : Muon.Covariances m n)
    (B : ℕ) (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (s : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  branchPt (profileF P (emaXi₂ β ℓ g)) C B s

/-- `b_ℓ(q,q') = ∑_j 𝔼[φ_q(emaw_j g_j) φ_{q'}(emaw_{j+ℓ} g_j)]` of `prop:app-vol-closed-lagsum`. Snapshot `cr-2026-10-23`. -/
def emaLagB {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ : ℕ)
    (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (q q' : ℝ) : ℝ :=
  ∑' j : ℕ, ∫ ω, phiQ q (Muon.emaW β j * g (Sum.inl j) ω) *
    phiQ q' (Muon.emaW β (j + ℓ) * g (Sum.inl j) ω) ∂P

/-- `e_ℓ(q,q') = ∑_j 𝔼[ψ_q(emaw_j g_j) ψ_{q'}(emaw_{j+ℓ} g_j)]` of `prop:app-vol-closed-lagsum`. Snapshot `cr-2026-10-23`. -/
def emaLagE {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ : ℕ)
    (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (q q' : ℝ) : ℝ :=
  ∑' j : ℕ, ∫ ω, psiQ q (Muon.emaW β j * g (Sum.inl j) ω) *
    psiQ q' (Muon.emaW β (j + ℓ) * g (Sum.inl j) ω) ∂P

/-! ## Bridges between the profile branch and the full branch -/

/-- Reindexing equivalence `ℕ ⊕ Fin ℓ ≃ ℕ`: shared label `j ↦ j + ℓ`, fresh label `i ↦ ℓ - (i+1)`. -/
private lemma emaTwoEquiv_exists (ℓ : ℕ) : ∃ e : ℕ ⊕ Fin ℓ ≃ ℕ,
    (∀ j, e (Sum.inl j) = j + ℓ) ∧ ∀ i : Fin ℓ, e (Sum.inr i) = ℓ - (i.val + 1) := by
  refine ⟨{
    toFun := fun a => match a with
      | Sum.inl j => j + ℓ
      | Sum.inr i => ℓ - (i.val + 1)
    invFun := fun k => if h : k < ℓ then Sum.inr ⟨ℓ - (k + 1), by omega⟩ else Sum.inl (k - ℓ)
    left_inv := ?_
    right_inv := ?_ }, fun j => rfl, fun i => rfl⟩
  · intro a
    rcases a with j | i
    · simp
    · have := i.isLt
      have h : ℓ - (i.val + 1) < ℓ := by omega
      simp only [h, dite_true, Sum.inr.injEq]
      ext; simp only; omega
  · intro k
    by_cases h : k < ℓ
    · simp only [h, dite_true]; omega
    · simp only [h, dite_false]; omega

private lemma ema_two_term {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ℓ : ℕ}
    {a : ℕ ⊕ Fin ℓ} {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g) (c q : ℝ) :
    ∫ ω, (c * g a ω) ^ 2 / (1 + q * (c * g a ω) ^ 2) ∂P =
      ∫ x, (c * x) ^ 2 / (1 + q * (c * x) ^ 2) ∂(gaussianReal 0 1) := by
  have h := (hg.2.2 a).integral_comp
    (f := fun x : ℝ => (c * x) ^ 2 / (1 + q * (c * x) ^ 2))
    (Measurable.aestronglyMeasurable (by fun_prop))
  exact h

private lemma ema_two_profileF {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {β : ℝ} {ℓ : ℕ}
    {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g) :
    profileF P (emaXi₂ β ℓ g) = profileF P (emaXi₁ β ℓ g) := by
  funext q
  set T : ℕ → ℝ := fun k => ∫ x, (Muon.emaW β k * x) ^ 2 / (1 + q * (Muon.emaW β k * x) ^ 2)
    ∂(gaussianReal 0 1) with hT
  obtain ⟨e, he1, he2⟩ := emaTwoEquiv_exists ℓ
  have h2 : profileF P (emaXi₂ β ℓ g) q = ∑' k, T k := by
    unfold profileF
    rw [← e.tsum_eq T]
    refine tsum_congr ?_
    intro a
    rcases a with j | i
    · have hw : β ^ ℓ * Muon.emaW β j = Muon.emaW β (j + ℓ) := by
        unfold Muon.emaW; ring
      have := ema_two_term (a := Sum.inl j) hg (β ^ ℓ * Muon.emaW β j) q
      simp only [emaXi₂, hT, he1, he2]
      rw [show (fun ω => (β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω) ^ 2 /
        (1 + q * (β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω) ^ 2)) = fun ω => (β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω) ^ 2 /
        (1 + q * (β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω) ^ 2) from rfl, this, hw]
    · have := ema_two_term (a := Sum.inr i) hg (Muon.emaW β (ℓ - (i.val + 1))) q
      simp only [emaXi₂, hT, he1, he2]
      exact this
  have h1 : profileF P (emaXi₁ β ℓ g) q = ∑' k, T k := by
    unfold profileF
    rw [← (Sum.inl_injective (α := ℕ) (β := Fin ℓ)).tsum_eq (f := fun a : ℕ ⊕ Fin ℓ =>
      ∫ ω, emaXi₁ β ℓ g a ω ^ 2 / (1 + q * emaXi₁ β ℓ g a ω ^ 2) ∂P)]
    · refine tsum_congr ?_
      intro j
      exact ema_two_term (a := Sum.inl j) hg (Muon.emaW β j) q
    · intro a ha
      rcases a with j | i
      · exact ⟨j, rfl⟩
      · exfalso; apply ha; simp [emaXi₁]
  rw [h2, h1]

/-- `lem:app-vol-closed-branch`, the `ξ₂` branch bridge (the second buffer of the EMA paired profile
at lag `ℓ`). Both marginals of the EMA paired profile have scalar function `F_w`
(`prop:app-vol-closed-lagsum` setting; `eqn:app-de-system`), so the branch point of `ξ₂` at `s` is
the solution of `thm:app-de-branch` for `(ν, ν̃)`. Sorried; the proof reindexes the labels
`j + ℓ` (shared) and `ℓ - (i+1)` (fresh) onto `ℕ`. Snapshot `cr-2026-10-23`.
-/
theorem lem_app_vol_closed_branch_ema_two {m n B : ℕ} (hB : 0 < B) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {ℓ : ℕ} {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (C : Muon.Covariances m n) (Cs γ : ℝ) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut C B) (hν' : (ν' : Measure ℝ) = Muon.nuIn C B)
    (hK : (ν, ν') ∈ Muon.DetEquiv.classK Cs γ) {s : ℝ} (hs : 0 < s) :
    profileF P (emaXi₂ β ℓ g) = Fw (Muon.emaW β) ∧
      branchPt (profileF P (emaXi₂ β ℓ g)) C B s = branchSol (Fw (Muon.emaW β)) ν ν' s := by
  have hF := ema_two_profileF (P := P) (β := β) hg
  have h1 := lem_app_vol_closed_branch_ema hB hβ0 hβ1 hg C Cs γ ν ν' hν hν' hK hs
  rw [hF]
  exact h1

private lemma eig_le_opNorm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) (i : Fin m) :
    hA.eigenvalues i ≤ opNorm A := by
  have hv : Matrix.toEuclideanLin A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    ext k
    have := congr_fun (hA.mulVec_eigenvectorBasis i) k
    simpa [Matrix.toLpLin_apply] using this
  have hn : ‖hA.eigenvectorBasis i‖ = 1 := (hA.eigenvectorBasis).orthonormal.1 i
  have h := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).le_opNorm (hA.eigenvectorBasis i)
  have h2 : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) (hA.eigenvectorBasis i)‖ = |hA.eigenvalues i| := by
    show ‖Matrix.toEuclideanLin A (hA.eigenvectorBasis i)‖ = _
    rw [hv, norm_smul, hn, mul_one, Real.norm_eq_abs]
  rw [h2, hn, mul_one] at h
  exact (le_abs_self _).trans h

private lemma spec_meas_class {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hP : A.PosSemidef) (B : ℕ)
    (hB : 0 < B) (γ CS : ℝ) (hm : (m : ℝ) ≤ γ * B) (hC : opNorm A ≤ CS) :
    ((B : ENNReal)⁻¹ • ∑ i, Measure.dirac (hP.isHermitian.eigenvalues i) : Measure ℝ) (Set.Icc 0 CS) ≤
        ENNReal.ofReal γ ∧
      ((B : ENNReal)⁻¹ • ∑ i, Measure.dirac (hP.isHermitian.eigenvalues i) : Measure ℝ) (Set.Icc 0 CS)ᶜ = 0 := by
  have hmem : ∀ i, hP.isHermitian.eigenvalues i ∈ Set.Icc (0 : ℝ) CS := fun i =>
    ⟨hP.eigenvalues_nonneg i, (eig_le_opNorm A hP.isHermitian i).trans hC⟩
  constructor
  · calc _ ≤ ((B : ENNReal)⁻¹ • ∑ i, Measure.dirac (hP.isHermitian.eigenvalues i) : Measure ℝ) Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = (B : ENNReal)⁻¹ * (m : ENNReal) := by simp
      _ = ENNReal.ofReal ((m : ℝ) / B) := by
          have hB' : (0 : ℝ) < B := by exact_mod_cast hB
          rw [ENNReal.ofReal_div_of_pos hB', ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
            div_eq_mul_inv, mul_comm]
      _ ≤ ENNReal.ofReal γ := by
          apply ENNReal.ofReal_le_ofReal
          have hB' : (0 : ℝ) < B := by exact_mod_cast hB
          rw [div_le_iff₀ hB']; exact hm
  · simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
    rw [Finset.sum_eq_zero, mul_zero]
    intro i _
    rw [Measure.dirac_apply' _ measurableSet_Icc.compl]
    simp [hmem i]

/-- The spectral measures of covariances satisfying `SizeFin` lie in the class `𝒦` of
`eqn:app-de-class` at `C_Σ`, `γ⋆`: their mass is `N/B ≤ γ⋆` and their support is the spectrum,
which lies in `[0, C_Σ]` (`Muon.opNorm` bound). Helper for the bridge to `Muon.DetEquiv`.
Sorried. Snapshot `cr-2026-10-23`.
-/
theorem nu_pair_mem_classK {m n B : ℕ} (C : Muon.Covariances m n) (γstar CSig : ℝ)
    (hS : SizeFin C B γstar CSig) (hB : 0 < B) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut C B) (hν' : (ν' : Measure ℝ) = Muon.nuIn C B) :
    (ν, ν') ∈ Muon.DetEquiv.classK CSig γstar := by
  obtain ⟨hsz, hout, hin⟩ := hS
  have hm : (m : ℝ) ≤ γstar * B := le_trans (by exact_mod_cast le_max_left m n) hsz
  have hn : (n : ℝ) ≤ γstar * B := le_trans (by exact_mod_cast le_max_right m n) hsz
  have h1 := spec_meas_class C.Sout C.psdOut B hB γstar CSig hm hout
  have h2 := spec_meas_class C.Sin C.psdIn B hB γstar CSig hn hin
  unfold Muon.nuOut at hν
  unfold Muon.nuIn at hν'
  simp only [Muon.DetEquiv.classK, Set.mem_setOf_eq]
  rw [hν, hν']
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

/-! ## Statements -/


/-- `thm:app-vol-closed-kernel`, part (i), snapshot `cr-2026-10-23`. Declaration of record for
part (i) of the EMA paired profile at lag `ℓ`: `Δ_ℓ(s,u) > 0`; `Δ_ℓ(s,u) ≥ θ_Σ(min(s,u))²` when
`Σ_out ≠ 0` and `Σ_in ≠ 0`; `Δ_ℓ(s,u) = 1` otherwise. The standing size conditions are
`SizeFin`. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Closed-form lag kernel]\label{thm:app-vol-closed-kernel}
Let $\ell\ge0$, let $F,G$ be diagonal tests and $s,u>0$.
\begin{enumerate}[label=(\roman*)]
\item $\Delta_\ell(s,u)>0$. If $\Sigmaout\ne0$ and $\Sigmain\ne0$, then
$\Delta_\ell(s,u)\ge\theta_\Sigma(\min(s,u))^2$; otherwise $\Delta_\ell(s,u)=1$.
\item The lag kernel of \cref{eqn:app-vol-lag-kernel} is
\begin{equation}\label{eqn:app-vol-closed-kernel}
\mathfrak k_\ell[F,G](s,u)=\frac{su\,b_\ell\;\mathcal T^{\mathrm{out}}[F](s,u)\;\mathcal T^{\mathrm{in}}[G](s,u)}{\Delta_\ell(s,u)} .
\end{equation}
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_closed_kernel_i (γstar CSig : ℝ) {m n B : ℕ} (C : Muon.Covariances m n)
    (hB : 0 < B) (hS : SizeFin C B γstar CSig) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ℓ : ℕ)
    {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g) (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    0 < profileDelta P C B (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) s u ∧
      ((C.Sout ≠ 0 ∧ C.Sin ≠ 0) →
        thetaSigma C B (min s u) ^ 2 ≤ profileDelta P C B (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) s u) ∧
      ((C.Sout = 0 ∨ C.Sin = 0) → profileDelta P C B (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) s u = 1) := by
  have hp := lem_app_vol_closed_profile_iv hβ0 hβ1 hg
  have hw : WeightSeq (Muon.emaW β) := (Muon.Drift.emaW_weightClass β ⟨hβ0, hβ1⟩).1
  have hF : Fw (Muon.emaW β) 0 ≤ 1 := by
    rw [(lem_app_de_scalar_ii hw).2.2.2.2.2.2.1,
      ← sPow_eq_sumPow_emaW, Muon.sPow_two hβ0 hβ1]
    exact (div_le_one (by linarith : 0 < 1 + β)).2 (by linarith)
  have hF₁ : profileF P (emaXi₁ β ℓ g) 0 ≤ 1 := by rw [hp.1]; exact hF
  have hF₂ : profileF P (emaXi₂ β ℓ g) 0 ≤ 1 := by rw [hp.2.1]; exact hF
  have hpair := hp.2.2.2.2.2
  by_cases hC : C.Sout = 0 ∨ C.Sin = 0
  · have hd := (lem_app_vol_closed_determinant_i hB hpair hF₁ hF₂ C hC hs hu).1
    refine ⟨by rw [hd]; norm_num, ?_, fun _ => hd⟩
    rintro ⟨hout, hin⟩
    exact (hC.elim hout hin).elim
  · have hout : C.Sout ≠ 0 := fun h => hC (Or.inl h)
    have hin : C.Sin ≠ 0 := fun h => hC (Or.inr h)
    have hd := lem_app_vol_closed_determinant_ii hB hpair hF₁ hF₂ C hout hin hs hu
    exact ⟨lt_of_lt_of_le hd.2 hd.1, fun _ => hd.1, fun h => (hC h).elim⟩

/-- `thm:app-vol-closed-kernel`, part (ii), snapshot `cr-2026-10-23`. Declaration of record for part
(ii): the deterministic lag kernel `𝔨_ℓ[F,G](s,u) = 𝔑_ℓ[F,G](ι_s, ι_u)` (`lagResp`, the limit of
`eqn:app-vol-Phi`, with the existence conjunct) equals the closed form
`s u b_ℓ T^out[F] T^in[G] / Δ_ℓ` of `profileKernel` at the EMA profile of lag `ℓ`, for diagonal
tests `F = Fm`, `G = Gm` (`hFd`, `hGd`) and every positive `s, u`, with no ellipticity. The standing
assumptions are `SizeFin` and `1 ≤ C_Σ`. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Closed-form lag kernel]\label{thm:app-vol-closed-kernel}
Let $\ell\ge0$, let $F,G$ be diagonal tests and $s,u>0$.
\begin{enumerate}[label=(\roman*)]
\item $\Delta_\ell(s,u)>0$. If $\Sigmaout\ne0$ and $\Sigmain\ne0$, then
$\Delta_\ell(s,u)\ge\theta_\Sigma(\min(s,u))^2$; otherwise $\Delta_\ell(s,u)=1$.
\item The lag kernel of \cref{eqn:app-vol-lag-kernel} is
\begin{equation}\label{eqn:app-vol-closed-kernel}
\mathfrak k_\ell[F,G](s,u)=\frac{su\,b_\ell\;\mathcal T^{\mathrm{out}}[F](s,u)\;\mathcal T^{\mathrm{in}}[G](s,u)}{\Delta_\ell(s,u)} .
\end{equation}
\end{enumerate}
\end{theorem}
```
-/
/- Relocated below the private spectral-decomposition helpers. -/
/-
theorem thm_app_vol_closed_kernel_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (ℓ : ℕ)
    {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ) (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    Tendsto (fun p : ℕ × ℝ =>
        lagRespCut cert γstar CSig Fp.β ℓ p.1 p.2 B S.μ S.lam Fd Gd (iotaF s) (iotaF u))
      (atTop ×ˢ atTop : Filter (ℕ × ℝ))
      (𝓝 (lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u))) ∧
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u) =
      profileKernel P Fp.C B (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g) Fm Gm s u := by
  sorry
-/

private lemma closed_cutoff_eq_tail (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (ℓ J : ℕ) (R : ℝ)
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (s u : ℝ) (hs : sRad cert γstar CSig R ≤ s) (hu : sRad cert γstar CSig R ≤ u) :
    lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd (iotaF s) (iotaF u) =
      profileKernel P Fp.C B (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) Fm Gm s u := by
  have h₁ := (lem_app_vol_closed_path_i cert γstar CSig Fp S hS hout hin
    ℓ J R hg Fd Gd s u hs hu).2
  have h₂ := (lem_app_vol_closed_path_ii cert γstar CSig Fp S hS hout hin
    ℓ J R hg Fd Gd Fm Gm hFd hGd s u hs hu).1
  exact_mod_cast h₁.symm.trans h₂

private lemma closed_eqvgen_isLeft {k : ℕ} (p : TreeMatch k × TreeMatch k) (x y : TreeVtx k)
    (h : Relation.EqvGen (treeRel p) x y) : x.isLeft = y.isLeft := by
  induction h with
  | rel x y hr =>
    obtain ⟨s, h | h | h | h⟩ := hr <;> obtain ⟨hx, hy⟩ := h <;> subst hx <;> subst hy <;> rfl
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

private lemma closed_truncMoment_zero (d : ℕ) (hd : d ≠ 0) (R : ℝ) (hR : R ≤ 0) :
    treeTruncMoment d R = 0 := by
  unfold treeTruncMoment
  rw [if_neg hd]
  have : (fun x : ℝ => if |x| ≤ R then x ^ d else 0) = fun _ => 0 := by
    funext x
    split_ifs with h
    · have : x = 0 := by
        have := abs_nonneg x
        exact abs_eq_zero.mp (le_antisymm (h.trans hR) this)
      subst this; simp [hd]
    · rfl
  rw [this]; simp

open Classical in
private lemma closed_treeMono_zero {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (hR : R ≤ 0) (B : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (a b : ℕ) :
    treeMono β ℓ J R B μ lam Fd Gd a b = 0 := by
  unfold treeMono
  apply Finset.sum_eq_zero
  intro p _
  split_ifs with hp
  · have hk : 0 < treeK a b := by unfold treeK; omega
    set r0 : Fin (treeK a b) := ⟨0, hk⟩ with hr0
    apply Finset.prod_eq_zero (Finset.mem_univ (treeMk p (Sum.inr r0)))
    unfold treeClassFactor
    have hno : ¬ ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = treeMk p (Sum.inr r0) := by
      rintro ⟨e, he⟩
      have h1 := closed_eqvgen_isLeft p _ _ (Quotient.exact he)
      simp at h1
    rw [if_neg hno]
    have hcard : (Finset.univ.filter fun r => treeMk p (Sum.inr r) = treeMk p (Sum.inr r0)).card ≠ 0 := by
      apply Finset.card_ne_zero_of_mem (a := r0)
      simp
    simp only [closed_truncMoment_zero _ hcard R hR, zero_mul]
  · rfl

private lemma closed_tree_zero_of_nonpos {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (hR : R ≤ 0) (B : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f₁ f₂ : Polynomial ℝ) :
    def_app_vol_tree β ℓ J R B μ lam Fd Gd f₁ f₂ = 0 := by
  unfold def_app_vol_tree
  apply Finset.sum_eq_zero; intro a _
  apply Finset.sum_eq_zero; intro b _
  rw [closed_treeMono_zero β ℓ J R hR B μ lam Fd Gd a b, mul_zero]


private lemma closed_cutoffXi_nonpos {Ω : Type} [MeasurableSpace Ω] (β : ℝ)
    (ℓ J l : ℕ) {R : ℝ} (hR : R ≤ 0) (g : ℤ → Ω → ℝ) :
    cutoffXi β ℓ J R l g = 0 := by
  funext α ω
  dsimp [cutoffXi]
  split_ifs with h
  · have hz : g α ω = 0 := abs_nonpos_iff.mp (h.trans hR)
    simp [hz]
  · simp

private lemma closed_cutoff_delta_pos {m n B : ℕ} (C : Muon.Covariances m n)
    (hB : 0 < B) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ℓ J : ℕ) (R : ℝ)
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    0 < profileDelta P C B (cutoffXi β ℓ J R 1 g) (cutoffXi β ℓ J R 2 g) s u := by
  by_cases hR : 0 < R
  · have hp := lem_app_vol_closed_cutoff_paired (ℓ := ℓ) (J := J) hβ0 hβ1 hR hg
    have hF₁ := (lem_app_vol_closed_cutoff_masses (ℓ := ℓ) (J := J) hβ0 hβ1 hR hg (Or.inl rfl)).2.2.2
    have hF₂ := (lem_app_vol_closed_cutoff_masses (ℓ := ℓ) (J := J) hβ0 hβ1 hR hg (Or.inr rfl)).2.2.2
    by_cases hC : C.Sout = 0 ∨ C.Sin = 0
    · rw [(lem_app_vol_closed_determinant_i hB hp hF₁ hF₂ C hC hs hu).1]
      norm_num
    · have hout : C.Sout ≠ 0 := fun h => hC (Or.inl h)
      have hin : C.Sin ≠ 0 := fun h => hC (Or.inr h)
      have hd := lem_app_vol_closed_determinant_ii hB hp hF₁ hF₂ C hout hin hs hu
      exact lt_of_lt_of_le hd.2 hd.1
  · rw [closed_cutoffXi_nonpos β ℓ J 1 (le_of_not_gt hR) g,
      closed_cutoffXi_nonpos β ℓ J 2 (le_of_not_gt hR) g]
    norm_num [profileDelta, pairedB, pairedE, closedDelta]

private lemma closed_eq_pos_of_separately_analytic {f g : ℝ → ℝ → ℝ} (a : ℝ)
    (hf₁ : ∀ u, 0 < u → AnalyticOnNhd ℝ (fun s => f s u) (Ioi 0))
    (hg₁ : ∀ u, 0 < u → AnalyticOnNhd ℝ (fun s => g s u) (Ioi 0))
    (hf₂ : ∀ s, 0 < s → AnalyticOnNhd ℝ (f s) (Ioi 0))
    (hg₂ : ∀ s, 0 < s → AnalyticOnNhd ℝ (g s) (Ioi 0))
    (htail : ∀ s u, a ≤ s → a ≤ u → f s u = g s u) :
    ∀ s u, 0 < s → 0 < u → f s u = g s u := by
  let b := max a 0 + 1
  have hb : 0 < b := by dsimp [b]; have := le_max_right a 0; linarith
  have hab : a < b := by dsimp [b]; have := le_max_left a 0; linarith
  have heq : ∀ u, 0 < u → a ≤ u → ∀ s, 0 < s → f s u = g s u := by
    intro u hu hau s hs
    apply (hf₁ u hu).eqOn_of_preconnected_of_eventuallyEq (hg₁ u hu) isPreconnected_Ioi hb _ hs
    filter_upwards [eventually_gt_nhds hab] with x hx
    exact htail x u hx.le hau
  intro s u hs hu
  apply (hf₂ s hs).eqOn_of_preconnected_of_eventuallyEq (hg₂ s hs) isPreconnected_Ioi hb _ hu
  filter_upwards [eventually_gt_nhds hab, eventually_gt_nhds hb] with y hy hy0
  exact heq y hy0 hy.le s hs

private lemma closed_analytic_det {d : ℕ} {A : ℝ → Matrix (Fin d) (Fin d) ℝ}
    {t : ℝ} (hA : ∀ i j, AnalyticAt ℝ (fun v => A v i j) t) :
    AnalyticAt ℝ (fun v => (A v).det) t := by
  classical
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun i _ => hA (σ i) i))

private lemma closed_analytic_inv_entry {d : ℕ} {A : ℝ → Matrix (Fin d) (Fin d) ℝ}
    {t : ℝ} (hA : ∀ i j, AnalyticAt ℝ (fun v => A v i j) t)
    (hdet : (A t).det ≠ 0) (i j : Fin d) :
    AnalyticAt ℝ (fun v => (A v)⁻¹ i j) t := by
  classical
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply ((closed_analytic_det hA).inv hdet).mul
  apply closed_analytic_det
  intro k l
  by_cases hk : k = j
  · subst k
    simp only [Matrix.updateRow_self]
    exact analyticAt_const
  · simpa only [Matrix.updateRow_ne hk] using hA k l

private lemma closed_branch_spec {m n B : ℕ} (hB : 0 < B) {Ω ι : Type}
    [MeasurableSpace Ω] [Countable ι] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ)
    (C : Muon.Covariances m n) (hout : C.Sout ≠ 0) (hin : C.Sin ≠ 0)
    (γ : ℝ) (hγ : (max m n : ℝ) ≤ γ * B) {s : ℝ} (hs : 0 < s) :
    IsBranchPoint (profileF P ξ) C B s (branchPt (profileF P ξ) C B s) ∧
      (0 < (branchPt (profileF P ξ) C B s).1 ∧
       0 < (branchPt (profileF P ξ) C B s).2.1 ∧
       0 < (branchPt (profileF P ξ) C B s).2.2.1 ∧
       0 < (branchPt (profileF P ξ) C B s).2.2.2) := by
  have h := lem_app_vol_closed_branch_ii hB hξ hs C hout hin γ hγ
  have he := h.1.exists
  have hx : IsBranchPoint (profileF P ξ) C B s (branchPt (profileF P ξ) C B s) := by
    unfold branchPt
    rw [dif_pos he]
    exact he.choose_spec
  exact ⟨hx, (h.2 _ hx).1⟩

private lemma closed_analytic_resolvent_entry {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosSemidef) {s a : ℝ → ℝ} {t : ℝ}
    (hs : AnalyticAt ℝ s t) (ha : AnalyticAt ℝ a t) (hs0 : 0 < s t) (ha0 : 0 ≤ a t)
    (i j : Fin d) :
    AnalyticAt ℝ (fun v => (s v • (1 : Matrix (Fin d) (Fin d) ℝ) + a v • A)⁻¹ i j) t := by
  apply closed_analytic_inv_entry
  · intro k l
    exact (hs.mul analyticAt_const).add (ha.mul analyticAt_const)
  · exact ne_of_gt (((Matrix.PosDef.one.smul hs0).add_posSemidef (hA.smul ha0)).det_pos)

private lemma closed_analytic_trace_resolvents {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosSemidef) (F : Matrix (Fin d) (Fin d) ℝ) (B : ℕ)
    {s u a c : ℝ → ℝ} {t : ℝ}
    (hs : AnalyticAt ℝ s t) (hu : AnalyticAt ℝ u t)
    (ha : AnalyticAt ℝ a t) (hc : AnalyticAt ℝ c t)
    (hs0 : 0 < s t) (hu0 : 0 < u t) (ha0 : 0 ≤ a t) (hc0 : 0 ≤ c t) :
    AnalyticAt ℝ (fun v => (B : ℝ)⁻¹ *
      (F * A * (s v • (1 : Matrix (Fin d) (Fin d) ℝ) + a v • A)⁻¹ *
        (u v • (1 : Matrix (Fin d) (Fin d) ℝ) + c v • A)⁻¹).trace) t := by
  classical
  apply analyticAt_const.mul
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.analyticAt_fun_sum
  intro i _
  apply Finset.analyticAt_fun_sum
  intro j _
  apply AnalyticAt.mul
  · apply Finset.analyticAt_fun_sum
    intro k _
    exact analyticAt_const.mul (closed_analytic_resolvent_entry hA hs ha hs0 ha0 k j)
  · exact closed_analytic_resolvent_entry hA hu hc hu0 hc0 j i

private lemma closed_analytic_kernel_formula {m n B : ℕ} (C : Muon.Covariances m n)
    (Fm : Mat m m) (Gm : Mat n n) {x y : ℝ → ℝ × ℝ × ℝ × ℝ}
    {s u b e : ℝ → ℝ} {t : ℝ}
    (hx : AnalyticAt ℝ x t) (hy : AnalyticAt ℝ y t)
    (hs : AnalyticAt ℝ s t) (hu : AnalyticAt ℝ u t)
    (hb : AnalyticAt ℝ b t) (he : AnalyticAt ℝ e t)
    (hs0 : 0 < s t) (hu0 : 0 < u t)
    (hxa : 0 ≤ (x t).2.2.1) (hxc : 0 ≤ (x t).2.2.2)
    (hya : 0 ≤ (y t).2.2.1) (hyc : 0 ≤ (y t).2.2.2)
    (hdelta : closedDelta C B (x t) (y t) (s t) (u t) (b t) (e t) ≠ 0) :
    AnalyticAt ℝ (fun v => s v * u v * b v * toutT C B (x v) (y v) (s v) (u v) Fm *
      tinT C B (x v) (y v) (s v) (u v) Gm /
        closedDelta C B (x v) (y v) (s v) (u v) (b v) (e v)) t := by
  have hTo : ∀ F, AnalyticAt ℝ (fun v => toutT C B (x v) (y v) (s v) (u v) F) t := fun F =>
    closed_analytic_trace_resolvents C.psdOut F B hs hu (analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp hx))) (analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp hy)))
      hs0 hu0 hxa hya
  have hTi : ∀ G, AnalyticAt ℝ (fun v => tinT C B (x v) (y v) (s v) (u v) G) t := fun G =>
    closed_analytic_trace_resolvents C.psdIn G B hs hu (analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp hx))) (analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp hy)))
      hs0 hu0 hxc hyc
  apply (((hs.mul hu).mul hb).mul (hTo Fm) |>.mul (hTi Gm)).div _ hdelta
  exact ((analyticAt_const.sub
    ((((((hs.mul hu).mul (hTo C.Sout)).mul (analyticAt_fst.comp (analyticAt_snd.comp hx))).mul (analyticAt_fst.comp (analyticAt_snd.comp hy))).mul he))).mul
    (analyticAt_const.sub
      ((((((hs.mul hu).mul (hTi C.Sin)).mul (analyticAt_fst.comp hx)).mul (analyticAt_fst.comp hy)).mul he)))).sub
    (((((hs.mul hu).mul (hTo C.Sout)).mul (hTi C.Sin)).mul (hb.pow 2)))

private lemma closed_profileKernel_analytic_left {m n B : ℕ} (C : Muon.Covariances m n)
    (hB : 0 < B) (hout : C.Sout ≠ 0) (hin : C.Sin ≠ 0)
    (γ : ℝ) (hγ : (max m n : ℝ) ≤ γ * B) {Ω ι : Type}
    [MeasurableSpace Ω] [Countable ι] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ₁ ξ₂ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂)
    (Fm : Mat m m) (Gm : Mat n n) {u : ℝ} (hu : 0 < u)
    (hdelta : ∀ s, 0 < s → profileDelta P C B ξ₁ ξ₂ s u ≠ 0) :
    AnalyticOnNhd ℝ (fun s => profileKernel P C B ξ₁ ξ₂ Fm Gm s u) (Ioi 0) := by
  intro s hs
  have hx := (lem_app_vol_closed_branch_iii hB hξ.profile₁ C hout hin).1 s hs
  have hy := closed_branch_spec hB hξ.profile₂ C hout hin γ hγ hu
  have hxs := closed_branch_spec hB hξ.profile₁ C hout hin γ hγ hs
  have hq : AnalyticAt ℝ (fun v => v * (branchPt (profileF P ξ₁) C B v).1 *
      (branchPt (profileF P ξ₁) C B v).2.1) s :=
    (analyticAt_id.mul (analyticAt_fst.comp hx)).mul
      (analyticAt_fst.comp (analyticAt_snd.comp hx))
  have hq0 : 0 < s * (branchPt (profileF P ξ₁) C B s).1 *
      (branchPt (profileF P ξ₁) C B s).2.1 := mul_pos (mul_pos hs hxs.2.1) hxs.2.2.1
  have hq'0 : 0 ≤ u * (branchPt (profileF P ξ₂) C B u).1 *
      (branchPt (profileF P ξ₂) C B u).2.1 :=
    (mul_pos (mul_pos hu hy.2.1) hy.2.2.1).le
  have hp := lem_app_vol_closed_profile_iii hξ
  exact closed_analytic_kernel_formula C Fm Gm hx analyticAt_const analyticAt_id analyticAt_const
    ((hp.2.2.1 _ hq'0 _ hq0).comp (f := fun v => v * (branchPt (profileF P ξ₁) C B v).1 *
      (branchPt (profileF P ξ₁) C B v).2.1) hq)
    ((hp.2.2.2.1 _ hq'0 _ hq0).comp (f := fun v => v * (branchPt (profileF P ξ₁) C B v).1 *
      (branchPt (profileF P ξ₁) C B v).2.1) hq)
    hs hu hxs.2.2.2.1.le hxs.2.2.2.2.le hy.2.2.2.1.le hy.2.2.2.2.le (hdelta s hs)

private lemma closed_profileKernel_analytic_right {m n B : ℕ} (C : Muon.Covariances m n)
    (hB : 0 < B) (hout : C.Sout ≠ 0) (hin : C.Sin ≠ 0)
    (γ : ℝ) (hγ : (max m n : ℝ) ≤ γ * B) {Ω ι : Type}
    [MeasurableSpace Ω] [Countable ι] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ₁ ξ₂ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂)
    (Fm : Mat m m) (Gm : Mat n n) {s : ℝ} (hs : 0 < s)
    (hdelta : ∀ u, 0 < u → profileDelta P C B ξ₁ ξ₂ s u ≠ 0) :
    AnalyticOnNhd ℝ (fun u => profileKernel P C B ξ₁ ξ₂ Fm Gm s u) (Ioi 0) := by
  intro u hu
  have hy := (lem_app_vol_closed_branch_iii hB hξ.profile₂ C hout hin).1 u hu
  have hx := closed_branch_spec hB hξ.profile₁ C hout hin γ hγ hs
  have hys := closed_branch_spec hB hξ.profile₂ C hout hin γ hγ hu
  have hq : AnalyticAt ℝ (fun v => v * (branchPt (profileF P ξ₂) C B v).1 *
      (branchPt (profileF P ξ₂) C B v).2.1) u :=
    (analyticAt_id.mul (analyticAt_fst.comp hy)).mul
      (analyticAt_fst.comp (analyticAt_snd.comp hy))
  have hq0 : 0 < u * (branchPt (profileF P ξ₂) C B u).1 *
      (branchPt (profileF P ξ₂) C B u).2.1 := mul_pos (mul_pos hu hys.2.1) hys.2.2.1
  have hq'0 : 0 ≤ s * (branchPt (profileF P ξ₁) C B s).1 *
      (branchPt (profileF P ξ₁) C B s).2.1 :=
    (mul_pos (mul_pos hs hx.2.1) hx.2.2.1).le
  have hp := lem_app_vol_closed_profile_iii hξ
  exact closed_analytic_kernel_formula C Fm Gm analyticAt_const hy analyticAt_const analyticAt_id
    ((hp.2.2.2.2.1 _ hq'0 _ hq0).comp (f := fun v => v * (branchPt (profileF P ξ₂) C B v).1 *
      (branchPt (profileF P ξ₂) C B v).2.1) hq)
    ((hp.2.2.2.2.2.1 _ hq'0 _ hq0).comp (f := fun v => v * (branchPt (profileF P ξ₂) C B v).1 *
      (branchPt (profileF P ξ₂) C B v).2.1) hq)
    hs hu hx.2.2.2.1.le hx.2.2.2.2.le hys.2.2.2.1.le hys.2.2.2.2.le (hdelta u hu)

private lemma closed_continuous_resolvent_curve {X : Type} [TopologicalSpace X] [CompactSpace X]
    (A : C(X, ℝ)) : ∃ k : ℝ → C(X, ℝ),
      (∀ s, 0 < s → ∀ x, k s x = iotaF s (A x)) ∧ AnalyticOnNhd ℝ k (Ioi 0) := by
  let D : ℝ → C(X, ℝ) := fun s => A ^ 2 + s • 1
  have hunit : ∀ s, 0 < s → IsUnit (D s) := by
    intro s hs
    apply (ContinuousMap.isUnit_iff_forall_ne_zero _).2
    intro x
    change A x ^ 2 + s * 1 ≠ 0
    nlinarith [sq_nonneg (A x)]
  refine ⟨fun s => A * Ring.inverse (D s), ?_, ?_⟩
  · intro s hs x
    have hm := congrArg (fun f : C(X, ℝ) => f x) (Ring.mul_inverse_cancel (D s) (hunit s hs))
    change (A x ^ 2 + s * 1) * (Ring.inverse (D s)) x = 1 at hm
    change A x * (Ring.inverse (D s)) x = A x / (A x ^ 2 + s)
    have hd : A x ^ 2 + s ≠ 0 := by nlinarith [sq_nonneg (A x)]
    apply (eq_div_iff hd).2
    calc A x * (Ring.inverse (D s)) x * (A x ^ 2 + s) =
        A x * ((A x ^ 2 + s * 1) * (Ring.inverse (D s)) x) := by ring
      _ = A x := by rw [hm, mul_one]
  · intro s hs
    have hd : AnalyticAt ℝ D s := analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    have hi := analyticAt_inverse (𝕜 := ℝ) (hunit s hs).unit
    rw [IsUnit.unit_spec] at hi
    exact analyticAt_const.mul (hi.comp (f := D) hd)

private lemma closed_filter_resolvent_analytic (D K : ℝ) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (T : (ℝ → ℝ) → ℝ)
    (hlin : ∀ f g : ℝ → ℝ, ContinuousOn f (Icc (-D) D) →
      (∀ x ∈ Icc (-D) D, f (-x) = -f x) → ContinuousOn g (Icc (-D) D) →
      (∀ x ∈ Icc (-D) D, g (-x) = -g x) → ∀ c : ℝ,
      T (fun x => f x + c * g x) = T f + c * T g)
    (hbound : ∀ f : ℝ → ℝ, ContinuousOn f (Icc (-D) D) →
      (∀ x ∈ Icc (-D) D, f (-x) = -f x) → |T f| ≤ K * supOn D f) :
    AnalyticOnNhd ℝ (fun s => T (iotaF s)) (Ioi 0) := by
  let π : ℝ → Icc (-D) D := Set.projIcc (-D) D (by linarith)
  let E : C(Icc (-D) D, ℝ) → ℝ → ℝ := fun f x => (f (π x) - f (π (-x))) / 2
  have hEc : ∀ f, ContinuousOn (E f) (Icc (-D) D) := by
    intro f
    exact ((f.continuous.comp continuous_projIcc).sub
      (f.continuous.comp (continuous_projIcc.comp continuous_neg))).div_const 2 |>.continuousOn
  have hEo : ∀ f x, E f (-x) = -E f x := by
    intro f x
    dsimp [E]
    simp only [neg_neg]
    ring
  have hEs : ∀ f, supOn D (E f) ≤ ‖f‖ := by
    intro f
    apply Real.iSup_le _ (norm_nonneg _)
    intro x
    have h₁ := f.norm_coe_le_norm (π x)
    have h₂ := f.norm_coe_le_norm (π (-x))
    change |(f (π x) - f (π (-x))) / 2| ≤ ‖f‖
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [Real.norm_eq_abs] at h₁ h₂
    have := abs_sub (f (π x)) (f (π (-x)))
    linarith
  have hz : T (fun _ => 0) = 0 := by
    have h := hbound (fun _ => 0) continuousOn_const (by intros; simp)
    have hs : supOn D (fun _ => 0) = 0 := by
      apply le_antisymm
      · exact Real.iSup_le (fun _ => by simp) le_rfl
      · exact Real.iSup_nonneg (fun _ => abs_nonneg _)
    rw [hs, mul_zero] at h
    exact abs_nonpos_iff.mp h
  let L₀ : C(Icc (-D) D, ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun f => T (E f)
    map_add' := by
      intro f g
      have he : E (f + g) = fun x => E f x + 1 * E g x := by
        funext x
        simp only [E, ContinuousMap.add_apply]
        ring
      change T (E (f + g)) = T (E f) + T (E g)
      rw [he, hlin _ _ (hEc f) (fun x _ => hEo f x) (hEc g) (fun x _ => hEo g x) 1, one_mul]
    map_smul' := by
      intro c f
      have he : E (c • f) = fun x => (0 : ℝ) + c * E f x := by
        funext x
        simp only [E, ContinuousMap.smul_apply, smul_eq_mul]
        ring
      change T (E (c • f)) = c * T (E f)
      rw [he, hlin _ _ continuousOn_const (by intros; simp) (hEc f) (fun x _ => hEo f x) c,
        hz, zero_add] }
  let L : C(Icc (-D) D, ℝ) →L[ℝ] ℝ := L₀.mkContinuous K (fun f => by
    change |T (E f)| ≤ K * ‖f‖
    exact (hbound _ (hEc f) (fun x _ => hEo f x)).trans (mul_le_mul_of_nonneg_left (hEs f) hK))
  have hcongr : ∀ f g : ℝ → ℝ, ContinuousOn f (Icc (-D) D) →
      (∀ x ∈ Icc (-D) D, f (-x) = -f x) → ContinuousOn g (Icc (-D) D) →
      (∀ x ∈ Icc (-D) D, g (-x) = -g x) → EqOn f g (Icc (-D) D) → T f = T g := by
    intro f g hfc hfo hgc hgo hfg
    have hc : ContinuousOn (fun x => f x + (-1) * g x) (Icc (-D) D) :=
      hfc.add (continuousOn_const.mul hgc)
    have ho : ∀ x ∈ Icc (-D) D, f (-x) + (-1) * g (-x) = -(f x + (-1) * g x) := by
      intro x hx
      rw [hfo x hx, hgo x hx]
      ring
    have hs : supOn D (fun x => f x + (-1) * g x) = 0 := by
      apply le_antisymm
      · exact Real.iSup_le (fun x => by simp [hfg x.2]) le_rfl
      · exact Real.iSup_nonneg (fun _ => abs_nonneg _)
    have hb := hbound _ hc ho
    rw [hs, mul_zero, hlin f g hfc hfo hgc hgo (-1)] at hb
    have := abs_nonpos_iff.mp hb
    linarith
  let A : C(Icc (-D) D, ℝ) := ⟨fun x => x.1, continuous_subtype_val⟩
  obtain ⟨k, hk, hka⟩ := closed_continuous_resolvent_curve A
  intro s hs
  have ha := (L.analyticAt (k s)).comp (hka s hs)
  apply ha.congr
  filter_upwards [eventually_gt_nhds hs] with v hv
  change T (E (k v)) = T (iotaF v)
  apply hcongr _ _ (hEc _) (fun x _ => hEo _ x)
  · exact (continuous_id.div (continuous_id.pow 2 |>.add continuous_const)
      (fun x => by change x ^ 2 + v ≠ 0; positivity)).continuousOn
  · intro x _
    simp only [iotaF, neg_sq, neg_div]
  · intro x hx
    have hnx : -x ∈ Icc (-D) D := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    dsimp [E]
    rw [hk v hv, hk v hv]
    simp only [π, Set.projIcc_of_mem _ hx, Set.projIcc_of_mem _ hnx, A,
      ContinuousMap.coe_mk, iotaF, neg_sq]
    ring

private lemma closed_iota_continuous {s : ℝ} (hs : 0 < s) : Continuous (iotaF s) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const)
    (fun x => by change x ^ 2 + s ≠ 0; positivity)

private lemma closed_iota_odd (s x : ℝ) : iotaF s (-x) = -iotaF s x := by
  simp only [iotaF, neg_sq, neg_div]

private lemma closed_cutoff_analytic_unit (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ J : ℕ) {R : ℝ} (hR : 0 < R)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hF : opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1)
    (hG : opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1) :
    (∀ u, 0 < u → AnalyticOnNhd ℝ (fun s =>
      lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd (iotaF s) (iotaF u)) (Ioi 0)) ∧
    (∀ s, 0 < s → AnalyticOnNhd ℝ (fun u =>
      lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd (iotaF s) (iotaF u)) (Ioi 0)) := by
  let D := volDR cert R CSig γstar
  have hD : 0 ≤ D := by dsimp [D, volDR]; positivity
  have hsup : ∀ f, 0 ≤ supOn D f := fun f => Real.iSup_nonneg (fun _ => abs_nonneg _)
  constructor
  · intro u hu
    apply closed_filter_resolvent_analytic D (|γstar| * supOn D (iotaF u)) hD
      (mul_nonneg (abs_nonneg _) (hsup _))
      (fun f => lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f (iotaF u))
    · intro f f' hfc hfo hf'c hf'o c
      exact (lem_app_vol_tree_extension_ii cert γstar CSig Fp S hS ℓ J R D le_rfl f (iotaF u)
        hfc hfo (closed_iota_continuous hu).continuousOn (fun x _ => closed_iota_odd u x)).2.2.2.2.2.1
          c f' hf'c hf'o Fd Gd
    · intro f hfc hfo
      have hb := (lem_app_vol_tree_extension_ii cert γstar CSig Fp S hS ℓ J R D le_rfl f (iotaF u)
        hfc hfo (closed_iota_continuous hu).continuousOn (fun x _ => closed_iota_odd u x)).2.1
          Fd Gd _ _ rfl rfl hF hG
      change |treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f (iotaF u)| ≤ _
      calc _ ≤ γstar * supOn D f * supOn D (iotaF u) := hb
        _ ≤ |γstar| * supOn D f * supOn D (iotaF u) := by
          gcongr; exacts [hsup _, hsup _, le_abs_self _]
        _ = _ := by ring
  · intro s hs
    apply closed_filter_resolvent_analytic D (|γstar| * supOn D (iotaF s)) hD
      (mul_nonneg (abs_nonneg _) (hsup _))
      (fun g => lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd (iotaF s) g)
    · intro g g' hgc hgo hg'c hg'o c
      exact (lem_app_vol_tree_extension_ii cert γstar CSig Fp S hS ℓ J R D le_rfl (iotaF s) g
        (closed_iota_continuous hs).continuousOn (fun x _ => closed_iota_odd s x) hgc hgo).2.2.2.2.2.2.1
          c g' hg'c hg'o Fd Gd
    · intro g hgc hgo
      have hb := (lem_app_vol_tree_extension_ii cert γstar CSig Fp S hS ℓ J R D le_rfl (iotaF s) g
        (closed_iota_continuous hs).continuousOn (fun x _ => closed_iota_odd s x) hgc hgo).2.1
          Fd Gd _ _ rfl rfl hF hG
      change |treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D (iotaF s) g| ≤ _
      calc _ ≤ γstar * supOn D (iotaF s) * supOn D g := hb
        _ ≤ |γstar| * supOn D (iotaF s) * supOn D g := by
          gcongr; exacts [hsup _, hsup _, le_abs_self _]
        _ = _ := by ring

private lemma closed_cutoff_scale_tests (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (ℓ J : ℕ) (R c d : ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfo : ∀ x, f (-x) = -f x) (hgo : ∀ x, g (-x) = -g x) :
    lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam (c • Fd) (d • Gd) f g =
      c * d * lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f g := by
  have h := lem_app_vol_tree_extension_ii cert γstar CSig Fp S hS ℓ J R _ le_rfl f g
    hf.continuousOn (fun x _ => hfo x) hg.continuousOn (fun x _ => hgo x)
  have hzF : ∀ G, treeRespExt Fp.β ℓ J R B S.μ S.lam 0 G (volDR cert R CSig γstar) f g = 0 := by
    intro G
    have he := h.2.2.2.1 1 0 0 G
    simp only [Pi.zero_apply, mul_zero, add_zero, one_mul] at he
    change treeRespExt Fp.β ℓ J R B S.μ S.lam 0 G (volDR cert R CSig γstar) f g =
      treeRespExt Fp.β ℓ J R B S.μ S.lam 0 G (volDR cert R CSig γstar) f g +
      treeRespExt Fp.β ℓ J R B S.μ S.lam 0 G (volDR cert R CSig γstar) f g at he
    linarith
  have hzG : ∀ F, treeRespExt Fp.β ℓ J R B S.μ S.lam F 0 (volDR cert R CSig γstar) f g = 0 := by
    intro F
    have he := h.2.2.2.2.1 1 F 0 0
    simp only [Pi.zero_apply, mul_zero, add_zero, one_mul] at he
    change treeRespExt Fp.β ℓ J R B S.μ S.lam F 0 (volDR cert R CSig γstar) f g =
      treeRespExt Fp.β ℓ J R B S.μ S.lam F 0 (volDR cert R CSig γstar) f g +
      treeRespExt Fp.β ℓ J R B S.μ S.lam F 0 (volDR cert R CSig γstar) f g at he
    linarith
  have hF := h.2.2.2.1 c Fd 0 (d • Gd)
  have hG := h.2.2.2.2.1 d Fd Gd 0
  simp only [Pi.zero_apply, add_zero, hzF, hzG] at hF hG
  change treeRespExt Fp.β ℓ J R B S.μ S.lam (c • Fd) (d • Gd)
    (volDR cert R CSig γstar) f g = c * d *
      treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd (volDR cert R CSig γstar) f g
  change treeRespExt Fp.β ℓ J R B S.μ S.lam (c • Fd) (d • Gd)
    (volDR cert R CSig γstar) f g = c *
      treeRespExt Fp.β ℓ J R B S.μ S.lam Fd (d • Gd) (volDR cert R CSig γstar) f g at hF
  change treeRespExt Fp.β ℓ J R B S.μ S.lam Fd (d • Gd)
    (volDR cert R CSig γstar) f g = d *
      treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd (volDR cert R CSig γstar) f g at hG
  rw [hF, hG]
  ring

open scoped Matrix.Norms.L2Operator in
private lemma closed_normalize_test {k : ℕ} (U : Mat k k) (Fd : Fin k → ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ Fd' : Fin k → ℝ, Fd = c • Fd' ∧
      opNorm (U * Matrix.diagonal Fd' * Uᵀ) ≤ 1 := by
  let a := opNorm (U * Matrix.diagonal Fd * Uᵀ)
  have ha : 0 ≤ a := by dsimp [a, opNorm]; exact norm_nonneg _
  refine ⟨a + 1, by positivity, (a + 1)⁻¹ • Fd, ?_, ?_⟩
  · rw [smul_smul, mul_inv_cancel₀ (by positivity : a + 1 ≠ 0), one_smul]
  · rw [Matrix.diagonal_smul, Matrix.mul_smul, smul_mul_assoc, opNorm_eq_norm,
      norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity : 0 < a + 1),
      ← opNorm_eq_norm]
    change (a + 1)⁻¹ * a ≤ 1
    rw [inv_mul_le_iff₀ (by positivity : 0 < a + 1)]
    linarith

private lemma closed_cutoff_analytic (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ J : ℕ) {R : ℝ} (hR : 0 < R)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) :
    (∀ u, 0 < u → AnalyticOnNhd ℝ (fun s =>
      lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd (iotaF s) (iotaF u)) (Ioi 0)) ∧
    (∀ s, 0 < s → AnalyticOnNhd ℝ (fun u =>
      lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd (iotaF s) (iotaF u)) (Ioi 0)) := by
  obtain ⟨c, hc, Fd', hFd, hF⟩ := closed_normalize_test S.uOut Fd
  obtain ⟨d, hd, Gd', hGd, hG⟩ := closed_normalize_test S.vIn Gd
  have h := closed_cutoff_analytic_unit cert γstar CSig Fp S hS hCSig ℓ J hR Fd' Gd' hF hG
  have he : ∀ s u, 0 < s → 0 < u →
      lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd (iotaF s) (iotaF u) =
        c * d * lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd' Gd' (iotaF s) (iotaF u) := by
    intro s u hs hu
    rw [hFd, hGd]
    exact closed_cutoff_scale_tests cert γstar CSig Fp S hS ℓ J R c d Fd' Gd' _ _
      (closed_iota_continuous hs) (closed_iota_continuous hu) (closed_iota_odd s) (closed_iota_odd u)
  constructor
  · intro u hu s hs
    apply ((analyticAt_const (v := c * d)).mul (h.1 u hu s hs)).congr
    filter_upwards [eventually_gt_nhds hs] with v hv
    exact (he v u hv hu).symm
  · intro s hs u hu
    apply ((analyticAt_const (v := c * d)).mul (h.2 s hs u hu)).congr
    filter_upwards [eventually_gt_nhds hu] with v hv
    exact (he s v hs hv).symm

private lemma closed_cutoff_eq_pos (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (ℓ J : ℕ)
    {R : ℝ} (hR : 0 < R) {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd (iotaF s) (iotaF u) =
      profileKernel P Fp.C B (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) Fm Gm s u := by
  have ha := closed_cutoff_analytic cert γstar CSig Fp S hS hCSig ℓ J hR Fd Gd
  have hp := lem_app_vol_closed_cutoff_paired (ℓ := ℓ) (J := J) Fp.hβ.1 Fp.hβ.2 hR hg
  exact closed_eq_pos_of_separately_analytic (sRad cert γstar CSig R) ha.1
    (fun v hv => closed_profileKernel_analytic_left Fp.C Fp.hB hout hin γstar (by simpa only [Nat.cast_max] using hS.1) hp Fm Gm hv
      (fun t ht => ne_of_gt (closed_cutoff_delta_pos Fp.C Fp.hB Fp.hβ.1 Fp.hβ.2 ℓ J R hg ht hv)))
    ha.2
    (fun t ht => closed_profileKernel_analytic_right Fp.C Fp.hB hout hin γstar (by simpa only [Nat.cast_max] using hS.1) hp Fm Gm ht
      (fun v hv => ne_of_gt (closed_cutoff_delta_pos Fp.C Fp.hB Fp.hβ.1 Fp.hβ.2 ℓ J R hg ht hv)))
    (fun t v ht hv => closed_cutoff_eq_tail cert γstar CSig Fp S hS hout hin ℓ J R hg
      Fm Gm Fd Gd hFd hGd t v ht hv) s u hs hu

private lemma closed_tree_prev_val {k : ℕ} (s : Fin k) :
    (treePrev s).val = if s.val = 0 then k - 1 else s.val - 1 := by
  obtain ⟨v, hv⟩ := s
  unfold treePrev
  dsimp only
  rcases Nat.eq_zero_or_pos v with rfl | hpos
  · simp [Nat.mod_eq_of_lt (show k - 1 < k by omega)]
  · rw [if_neg (show ¬ (v = 0) by omega)]
    have e : v + (k - 1) = (v - 1) + k := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (show v - 1 < k by omega)]

private lemma closed_tree_outV_odd {k : ℕ} (hk : k % 2 = 0) (s : Fin k) :
    (treeOutV s).val % 2 = 1 := by
  have hs := s.isLt
  unfold treeOutV
  split_ifs with h
  · have h' : s.val % 2 = 0 := h
    rw [closed_tree_prev_val]
    split_ifs with h0 <;> omega
  · have h' : ¬ s.val % 2 = 0 := h
    omega

private lemma closed_tree_inV_even {k : ℕ} (s : Fin k) : (treeInV s).val % 2 = 0 := by
  have hs := s.isLt
  unfold treeInV
  split_ifs with h
  · have h' : s.val % 2 = 0 := h
    exact h'
  · have h' : ¬ s.val % 2 = 0 := h
    rw [closed_tree_prev_val]
    split_ifs with h0 <;> omega

/-- Private helper: the identifications preserve the parity of external indices. -/
private lemma closed_tree_setoid_par {k : ℕ} (hk : k % 2 = 0) (p : TreeMatch k × TreeMatch k) {x y : TreeVtx k}
    (h : treeSetoid p x y) : (Sum.elim (fun e => e.val % 2) (fun _ => 2)) x = (Sum.elim (fun e => e.val % 2) (fun _ => 2)) y := by
  change Relation.EqvGen (treeRel p) x y at h
  induction h with
  | rel x y hxy =>
    unfold treeRel at hxy
    obtain ⟨s, h1 | h1 | h1 | h1⟩ := hxy
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a; subst h1b; rfl
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a; subst h1b; rfl
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a; subst h1b
      simp only [Sum.elim_inl]
      rw [closed_tree_outV_odd hk s, closed_tree_outV_odd hk (p.1.1 s)]
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a; subst h1b
      simp only [Sum.elim_inl]
      rw [closed_tree_inV_even s, closed_tree_inV_even (p.2.1 s)]
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Private helper: the class of the `G`-mark contains no odd (output) external vertex. -/
private lemma closed_tree_gmark_pure (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) :
    ¬ ∃ e : Fin (treeK a b),
      treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeGMark a b)) ∧ e.val % 2 = 1 := by
  rintro ⟨e, heq, hodd⟩
  unfold treeMk at heq
  have h2 := closed_tree_setoid_par (by unfold treeK; omega) p (Quotient.exact heq)
  simp only [Sum.elim_inl, treeGMark, Fin.val_mk] at h2
  omega

private lemma closed_eigenvalues_zero {k : ℕ} (A U : Mat k k) (e : Fin k → ℝ)
    (hU : Uᵀ * U = 1) (he : ∀ i, A *ᵥ (fun j => U j i) = e i • (fun j => U j i))
    (hA : A = 0) : ∀ i, e i = 0 := by
  intro i
  have hc : (fun j => U j i) ⬝ᵥ (fun j => U j i) = 1 :=
    sum_col_sq_eq_one U hU i
  have hi := congrArg (fun v => (fun j => U j i) ⬝ᵥ v) (he i)
  simpa [hA, dotProduct_smul, hc] using hi.symm

open Classical in
private lemma closed_treeMono_degenerate {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hzero : (∀ i, μ i = 0) ∨ (∀ j, lam j = 0)) (a b : ℕ) :
    treeMono β ℓ J R B μ lam Fd Gd a b = 0 := by
  unfold treeMono
  apply Finset.sum_eq_zero
  intro p _
  split_ifs with hp
  · rcases hzero with hμ | hl
    · apply Finset.prod_eq_zero (Finset.mem_univ (treeMk p (Sum.inl (treeFMark a b))))
      unfold treeClassFactor
      rw [if_pos ⟨treeFMark a b, rfl⟩,
        if_pos ⟨treeFMark a b, rfl, by dsimp [treeFMark]; omega⟩]
      have hc : (Finset.univ.filter fun e : Fin (treeK a b) =>
          treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeFMark a b))).card ≠ 0 := by
        apply Finset.card_ne_zero_of_mem (a := treeFMark a b)
        simp
      simp [hμ, hc]
    · apply Finset.prod_eq_zero (Finset.mem_univ (treeMk p (Sum.inl (treeGMark a b))))
      unfold treeClassFactor
      rw [if_pos ⟨treeGMark a b, rfl⟩, if_neg (closed_tree_gmark_pure a b p)]
      have hc : (Finset.univ.filter fun e : Fin (treeK a b) =>
          treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeGMark a b))).card ≠ 0 := by
        apply Finset.card_ne_zero_of_mem (a := treeGMark a b)
        simp
      simp [hl, hc]
  · rfl

private lemma closed_tree_degenerate {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hzero : (∀ i, μ i = 0) ∨ (∀ j, lam j = 0)) (f g : Polynomial ℝ) :
    def_app_vol_tree β ℓ J R B μ lam Fd Gd f g = 0 := by
  unfold def_app_vol_tree
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  rw [closed_treeMono_degenerate β ℓ J R B μ lam Fd Gd hzero a b, mul_zero]

private lemma closed_cutoff_degenerate (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hC : Fp.C.Sout = 0 ∨ Fp.C.Sin = 0) (ℓ J : ℕ) (R : ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f g : ℝ → ℝ) :
    lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f g = 0 := by
  have hzero : (∀ i, S.μ i = 0) ∨ (∀ j, S.lam j = 0) := by
    rcases hC with hC | hC
    · exact Or.inl (closed_eigenvalues_zero _ _ _ S.huOut S.eigOut hC)
    · exact Or.inr (closed_eigenvalues_zero _ _ _ S.hvIn S.eigIn hC)
  unfold lagRespCut treeRespExt
  have hz : (fun k : ℕ => def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd
      (treeApprox (volDR cert R CSig γstar) f k) (treeApprox (volDR cert R CSig γstar) g k)) =
      fun _ => 0 := funext fun k => closed_tree_degenerate Fp.β ℓ J R B S.μ S.lam Fd Gd hzero _ _
  rw [hz]
  exact (tendsto_const_nhds (x := (0 : ℝ))).limUnder_eq

private lemma closed_cutoff_eq_nonpos (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (ℓ J : ℕ) (R : ℝ) (hR : R ≤ 0)
    (g : ℤ → Ω → ℝ) (Fm : Mat m m) (Gm : Mat n n)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (s u : ℝ) :
    lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd (iotaF s) (iotaF u) =
      profileKernel P Fp.C B (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) Fm Gm s u := by
  have hleft : lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd
      (iotaF s) (iotaF u) = 0 := by
    unfold lagRespCut treeRespExt
    have hz : (fun k : ℕ => def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd
        (treeApprox (volDR cert R CSig γstar) (iotaF s) k)
        (treeApprox (volDR cert R CSig γstar) (iotaF u) k)) = fun _ => 0 :=
      funext fun k => closed_tree_zero_of_nonpos _ _ _ _ hR _ _ _ _ _ _ _
    rw [hz]
    exact (tendsto_const_nhds (x := (0 : ℝ))).limUnder_eq
  rw [hleft, closed_cutoffXi_nonpos Fp.β ℓ J 1 hR g,
    closed_cutoffXi_nonpos Fp.β ℓ J 2 hR g]
  simp [profileKernel, pairedB]

private lemma closed_profileKernel_degenerate {m n B : ℕ} (C : Muon.Covariances m n)
    {Ω ι : Type} [MeasurableSpace Ω] [Countable ι] (P : Measure Ω)
    (ξ₁ ξ₂ : ι → Ω → ℝ) (hC : C.Sout = 0 ∨ C.Sin = 0)
    (Fm : Mat m m) (Gm : Mat n n) (s u : ℝ) :
    profileKernel P C B ξ₁ ξ₂ Fm Gm s u = 0 := by
  rcases hC with hC | hC
  · simp [profileKernel, toutT, hC]
  · simp [profileKernel, tinT, hC]

/-- `thm:app-vol-closed-kernel`, cutoff version, snapshot `cr-2026-10-23`. Declaration of record for
the cutoff identity of `lem:app-vol-closed-path` extended from `[s_R, ∞)²` to `(0,∞)²`
(`𝔨^{J,R}_ℓ[F,G] = 𝔎^{J,R}[F,G]` in the proof of part (ii), Steps 1–2 of the proof): for every
`J`, `R`, the cutoff lag response `lagRespCut` equals the closed form of the cutoff paired profile
`cutoffXi · 1`, `cutoffXi · 2`, for all `s, u > 0`, and `Δ^{J,R}(s,u) ≠ 0`. The sorried proof uses
`lem_app_vol_closed_path_ii` and the identity theorem. Source: the proof of `thm:app-vol-closed-kernel`
(l.2503–2562), with the same standing assumptions as part (ii). -/
theorem thm_app_vol_closed_kernel_cutoff (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (ℓ J : ℕ) (R : ℝ)
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ) :
    ∀ s u : ℝ, 0 < s → 0 < u →
      lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd (iotaF s) (iotaF u) =
          profileKernel P Fp.C B (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) Fm Gm s u ∧
        profileDelta P Fp.C B (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) s u ≠ 0 := by
  intro s u hs hu
  refine ⟨?_, ne_of_gt (closed_cutoff_delta_pos Fp.C Fp.hB Fp.hβ.1 Fp.hβ.2
    ℓ J R hg hs hu)⟩
  by_cases hR : R ≤ 0
  · exact closed_cutoff_eq_nonpos cert γstar CSig Fp S P ℓ J R hR g Fm Gm Fd Gd s u
  · have hRpos : 0 < R := lt_of_not_ge hR
    by_cases hC : Fp.C.Sout = 0 ∨ Fp.C.Sin = 0
    · rw [closed_cutoff_degenerate cert γstar CSig Fp S hC ℓ J R Fd Gd,
        closed_profileKernel_degenerate Fp.C P _ _ hC Fm Gm s u]
    · exact closed_cutoff_eq_pos cert γstar CSig Fp S hS hCSig
        (fun h => hC (Or.inl h)) (fun h => hC (Or.inr h)) ℓ J hRpos hg
        Fm Gm Fd Gd hFd hGd s u hs hu

private lemma closed_bounds_gauss_exists (A : Type) [Countable A] :
    ∃ P : Measure (A → ℝ), IsProbabilityMeasure P ∧
      IsStdGaussianFamily P (fun (a : A) (ω : A → ℝ) => ω a) := by
  refine ⟨Measure.infinitePi (fun _ : A => gaussianReal 0 1), inferInstance, ?_, ?_, ?_⟩
  · intro a
    exact measurable_pi_apply a
  · exact iIndepFun_infinitePi (P := fun _ : A => gaussianReal 0 1)
      (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  · intro a
    exact ⟨(measurable_pi_apply a).aemeasurable, by
      simpa using Measure.infinitePi_map_eval (fun _ : A => gaussianReal 0 1) a⟩

open scoped Matrix.Norms.L2Operator in
private lemma closed_bounds_opNorm_mul_le {a b c : ℕ} (A : Mat a b) (D : Mat b c) :
    opNorm (A * D) ≤ opNorm A * opNorm D := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A D

open scoped Matrix.Norms.L2Operator in
private lemma closed_bounds_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

open scoped Matrix.Norms.L2Operator in
private lemma closed_bounds_abs_entry_le_opNorm {p q : ℕ} (K : Mat p q) (i : Fin p) (j : Fin q) :
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

open scoped Matrix.Norms.L2Operator in
private lemma closed_bounds_opNorm_orth_le {p : ℕ} (U : Mat p p) (hU : Uᵀ * U = 1) :
    opNorm U ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hU] at h
  have h1 : ‖(1 : Mat p p)‖ ≤ 1 := by
    have : (1 : Mat p p) = Matrix.diagonal (fun _ => (1 : ℝ)) := by simp
    rw [this, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => by simp)
  rw [opNorm_eq_norm]
  nlinarith [norm_nonneg U]

open scoped Matrix.Norms.L2Operator in
private lemma closed_bounds_diag_abs_le {p : ℕ} (U : Mat p p) (hU : Uᵀ * U = 1)
    (M : Mat p p) (d : Fin p → ℝ) (hM : M = U * Matrix.diagonal d * Uᵀ) (i : Fin p) :
    |d i| ≤ opNorm M := by
  have hD : Matrix.diagonal d = Uᵀ * M * U := by
    rw [hM]
    calc Matrix.diagonal d = (Uᵀ * U) * Matrix.diagonal d * (Uᵀ * U) := by rw [hU]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hentry : (Uᵀ * M * U) i i = d i := by rw [← hD]; simp
  have h1 : |d i| ≤ opNorm (Uᵀ * M * U) := by
    simpa only [hentry] using closed_bounds_abs_entry_le_opNorm (Uᵀ * M * U) i i
  have hn : opNorm U ≤ 1 := closed_bounds_opNorm_orth_le U hU
  have hn' : opNorm Uᵀ ≤ 1 := by rw [closed_bounds_opNorm_transpose]; exact hn
  have h0 : 0 ≤ opNorm M := by rw [opNorm_eq_norm]; exact norm_nonneg _
  have h00 : 0 ≤ opNorm Uᵀ := by rw [opNorm_eq_norm]; exact norm_nonneg _
  have h000 : 0 ≤ opNorm U := by rw [opNorm_eq_norm]; exact norm_nonneg _
  have h2 : opNorm (Uᵀ * M * U) ≤ 1 * opNorm M * 1 := by
    calc opNorm (Uᵀ * M * U) ≤ opNorm (Uᵀ * M) * opNorm U :=
          closed_bounds_opNorm_mul_le _ _
      _ ≤ (opNorm Uᵀ * opNorm M) * opNorm U :=
          mul_le_mul_of_nonneg_right (closed_bounds_opNorm_mul_le _ _) h000
      _ ≤ (1 * opNorm M) * 1 :=
          mul_le_mul (mul_le_mul hn' le_rfl h0 zero_le_one) hn h000 (by positivity)
  linarith

private lemma closed_bounds_trace_spectral {d : ℕ} (A U : Mat d d) (v : Fin d → ℝ)
    (hU : Uᵀ * U = 1) (hA : A = U * Matrix.diagonal v * Uᵀ) :
    A.trace = ∑ i, v i := by
  rw [hA, Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]

private lemma closed_bounds_trace_two_resolvents {d : ℕ}
    (A U : Matrix (Fin d) (Fin d) ℝ) (v w : Fin d → ℝ)
    (hU : Uᵀ * U = 1) (hA : A = U * Matrix.diagonal v * Uᵀ)
    (F : Matrix (Fin d) (Fin d) ℝ) (hF : F = U * Matrix.diagonal w * Uᵀ)
    (s a u c : ℝ) (hs : ∀ i, s + a * v i ≠ 0) (hu : ∀ i, u + c * v i ≠ 0) :
    (F * A * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • A)⁻¹ *
      (u • (1 : Matrix (Fin d) (Fin d) ℝ) + c • A)⁻¹).trace =
        ∑ i, w i * v i / ((s + a * v i) * (u + c * v i)) := by
  classical
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hinv : ∀ (t b : ℝ), (∀ i, t + b * v i ≠ 0) →
      (t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • A)⁻¹ =
        U * Matrix.diagonal (fun i => (t + b * v i)⁻¹) * Uᵀ := by
    intro t b hden
    have he : Matrix.diagonal (fun i => t + b * v i) =
        t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • Matrix.diagonal v := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
    have hfac : t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • A =
        U * Matrix.diagonal (fun i => t + b * v i) * Uᵀ := by
      rw [he, Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU, ← hA]
    have hdiag : Matrix.diagonal (fun i => t + b * v i) *
        Matrix.diagonal (fun i => (t + b * v i)⁻¹) = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij, hden]
    apply Matrix.inv_eq_right_inv
    rw [hfac]
    calc U * Matrix.diagonal (fun i => t + b * v i) * Uᵀ *
          (U * Matrix.diagonal (fun i => (t + b * v i)⁻¹) * Uᵀ) =
        U * (Matrix.diagonal (fun i => t + b * v i) *
          Matrix.diagonal (fun i => (t + b * v i)⁻¹)) * Uᵀ := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
      _ = 1 := by rw [hdiag, Matrix.mul_one, hUU]
  rw [hinv s a hs, hinv u c hu, hA, hF]
  calc
    (U * Matrix.diagonal w * Uᵀ * (U * Matrix.diagonal v * Uᵀ) *
        (U * Matrix.diagonal (fun i => (s + a * v i)⁻¹) * Uᵀ) *
        (U * Matrix.diagonal (fun i => (u + c * v i)⁻¹) * Uᵀ)).trace =
      (U * (Matrix.diagonal w * Matrix.diagonal v *
        Matrix.diagonal (fun i => (s + a * v i)⁻¹) *
        Matrix.diagonal (fun i => (u + c * v i)⁻¹)) * Uᵀ).trace := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul,
            ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul,
            ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
    _ = (Matrix.diagonal w * Matrix.diagonal v *
        Matrix.diagonal (fun i => (s + a * v i)⁻¹) *
        Matrix.diagonal (fun i => (u + c * v i)⁻¹)).trace := by
          rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    _ = _ := by
      simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, div_eq_mul_inv]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_inv]
      ring

open scoped Matrix.Norms.L2Operator in
private lemma closed_bounds_trace_abs {d B : ℕ} (hB : 0 < B)
    (A U : Mat d d) (v w : Fin d → ℝ) (hU : Uᵀ * U = 1)
    (hA : A = U * Matrix.diagonal v * Uᵀ) (F : Mat d d)
    (hF : F = U * Matrix.diagonal w * Uᵀ) (hv : ∀ i, 0 ≤ v i)
    (s a u c : ℝ) (hs : 0 < s) (ha : 0 ≤ a) (hu : 0 < u) (hc : 0 ≤ c) :
    |(B : ℝ)⁻¹ * (F * A * (s • (1 : Mat d d) + a • A)⁻¹ *
      (u • (1 : Mat d d) + c • A)⁻¹).trace| ≤
        opNorm F * A.trace / ((B : ℝ) * (s * u)) := by
  have hsr : ∀ i, 0 < s + a * v i := fun i => add_pos_of_pos_of_nonneg hs (mul_nonneg ha (hv i))
  have hur : ∀ i, 0 < u + c * v i := fun i => add_pos_of_pos_of_nonneg hu (mul_nonneg hc (hv i))
  rw [closed_bounds_trace_two_resolvents A U v w hU hA F hF s a u c
    (fun i => (hsr i).ne') (fun i => (hur i).ne')]
  have hterm : ∀ i, |w i * v i / ((s + a * v i) * (u + c * v i))| ≤
      opNorm F * v i / (s * u) := by
    intro i
    rw [abs_div, abs_mul, abs_of_nonneg (hv i), abs_of_pos (mul_pos (hsr i) (hur i))]
    have hd : s * u ≤ (s + a * v i) * (u + c * v i) := by
      nlinarith [mul_nonneg ha (hv i), mul_nonneg hc (hv i)]
    exact div_le_div₀
      (mul_nonneg ((abs_nonneg (w i)).trans (closed_bounds_diag_abs_le U hU F w hF i)) (hv i))
      (mul_le_mul_of_nonneg_right (closed_bounds_diag_abs_le U hU F w hF i) (hv i))
      (mul_pos hs hu) hd
  have hsum : |∑ i, w i * v i / ((s + a * v i) * (u + c * v i))| ≤
      opNorm F * A.trace / (s * u) := by
    calc
      |∑ i, w i * v i / ((s + a * v i) * (u + c * v i))| ≤
          ∑ i, |w i * v i / ((s + a * v i) * (u + c * v i))| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, opNorm F * v i / (s * u) := Finset.sum_le_sum fun i _ => hterm i
      _ = opNorm F * A.trace / (s * u) := by
        rw [closed_bounds_trace_spectral A U v hU hA]
        simp only [Finset.mul_sum, Finset.sum_div]
  rw [abs_mul, abs_of_pos (inv_pos.mpr (by exact_mod_cast hB : (0 : ℝ) < B))]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  calc
    (B : ℝ)⁻¹ * |∑ i, w i * v i / ((s + a * v i) * (u + c * v i))| ≤
        (B : ℝ)⁻¹ * (opNorm F * A.trace / (s * u)) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hBr.le)
    _ = opNorm F * A.trace / ((B : ℝ) * (s * u)) := by field_simp

private lemma closed_bounds_trace_nonneg {d B : ℕ} (hB : 0 < B)
    (A U : Mat d d) (v w : Fin d → ℝ) (hU : Uᵀ * U = 1)
    (hA : A = U * Matrix.diagonal v * Uᵀ) (F : Mat d d)
    (hF : F = U * Matrix.diagonal w * Uᵀ) (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i)
    (s a u c : ℝ) (hs : 0 < s) (ha : 0 ≤ a) (hu : 0 < u) (hc : 0 ≤ c) :
    0 ≤ (B : ℝ)⁻¹ * (F * A * (s • (1 : Mat d d) + a • A)⁻¹ *
      (u • (1 : Mat d d) + c • A)⁻¹).trace := by
  rw [closed_bounds_trace_two_resolvents A U v w hU hA F hF s a u c
    (fun i => (add_pos_of_pos_of_nonneg hs (mul_nonneg ha (hv i))).ne')
    (fun i => (add_pos_of_pos_of_nonneg hu (mul_nonneg hc (hv i))).ne')]
  exact mul_nonneg (inv_nonneg.mpr (by exact_mod_cast hB.le : (0 : ℝ) ≤ B))
    (Finset.sum_nonneg fun i _ => div_nonneg (mul_nonneg (hw i) (hv i))
      (mul_nonneg (add_nonneg hs.le (mul_nonneg ha (hv i)))
        (add_nonneg hu.le (mul_nonneg hc (hv i)))))

private lemma closed_bounds_emaW_sq_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Summable (fun j : ℕ => Muon.emaW β j ^ 2) := by
  have hr : β ^ 2 < 1 := pow_lt_one₀ hβ0 hβ1 (by omega)
  have key : (fun j : ℕ => Muon.emaW β j ^ 2) =
      fun j => (1 - β) ^ 2 * (β ^ 2) ^ j := by
    funext j
    unfold Muon.emaW
    rw [mul_pow, pow_right_comm β j 2]
  rw [key]
  exact (summable_geometric_of_lt_one (pow_nonneg hβ0 2) hr).mul_left _

private lemma closed_bounds_cutoff_varpi_sum {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (ℓ J : ℕ) :
    ∑ α ∈ cutoffLabels J ℓ,
        cutoffVarpi β ℓ J 1 α * cutoffVarpi β ℓ J 2 α ≤ Muon.sPow β 2 * β ^ ℓ := by
  have hmem : ∀ α ∈ cutoffLabels J ℓ,
      cutoffVarpi β ℓ J 1 α * cutoffVarpi β ℓ J 2 α =
        treeVarpi β ℓ 1 α * treeVarpi β ℓ 2 α := by
    intro α hα
    simp [cutoffVarpi, hα]
  rw [Finset.sum_congr rfl hmem]
  have hsub : Finset.Icc (-(J : ℤ)) 0 ⊆ cutoffLabels J ℓ := Finset.subset_union_left
  have hzero : ∀ x ∈ cutoffLabels J ℓ, x ∉ Finset.Icc (-(J : ℤ)) 0 →
      treeVarpi β ℓ 1 x * treeVarpi β ℓ 2 x = 0 := by
    intro x hx hx'
    simp only [cutoffLabels, Finset.mem_union, Finset.mem_Icc] at hx hx'
    have hpos : 0 < x := by rcases hx with hx | hx <;> omega
    have h1 : treeVarpi β ℓ 1 x = 0 := by
      unfold treeVarpi
      rw [if_neg (show ¬ x ≤ 0 by omega)]
      simp
    rw [h1, zero_mul]
  rw [← Finset.sum_subset hsub hzero]
  have heq : ∑ α ∈ Finset.Icc (-(J : ℤ)) 0,
      treeVarpi β ℓ 1 α * treeVarpi β ℓ 2 α =
        β ^ ℓ * ∑ j ∈ Finset.range (J + 1), Muon.emaW β j ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_nbij' (fun α : ℤ => α.natAbs) (fun n : ℕ => -(n : ℤ))
    · intro α hα
      simp only [Finset.mem_Icc, Finset.mem_range] at hα ⊢
      have he := Int.ofNat_natAbs_of_nonpos hα.2
      omega
    · intro n hn
      simp only [Finset.mem_range, Finset.mem_Icc] at hn ⊢
      omega
    · intro α hα
      simp only [Finset.mem_Icc] at hα
      simpa [Int.ofNat_natAbs_of_nonpos hα.2]
    · intro n hn
      simp only [Finset.mem_range] at hn
      simp
    · intro α hα
      simp only [Finset.mem_Icc] at hα
      unfold treeVarpi
      rw [if_pos hα.2, if_pos rfl, if_pos hα.2, if_neg (by norm_num : (2 : ℕ) ≠ 1)]
      ring
  rw [heq]
  have hpartial := (closed_bounds_emaW_sq_summable hβ0 hβ1).sum_le_tsum
    (Finset.range (J + 1)) (fun j _ => sq_nonneg (Muon.emaW β j))
  simpa [Muon.sPow, mul_comm] using
    (mul_le_mul_of_nonneg_left hpartial (pow_nonneg hβ0 ℓ))

private lemma closed_bounds_gauss_sq_integral :
    ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hL : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) :=
    memLp_id_gaussianReal' (2 : ENNReal) (by simp)
  have h := variance_eq_sub hL
  rw [variance_id_gaussianReal] at h
  simp only [Pi.pow_apply, id] at h
  have hm : ∫ x, x ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal
  rw [hm] at h
  norm_num at h ⊢
  linarith

private lemma closed_bounds_cutoff_cross_term {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → ℝ}
    (hg : HasLaw g (gaussianReal 0 1) P) (R c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ∫ ω, (c * (if |g ω| ≤ R then g ω else 0)) *
      (d * (if |g ω| ≤ R then g ω else 0)) ∂P ≤ c * d := by
  have hint : Integrable (fun ω => g ω ^ 2) P := by
    have hL : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) :=
      memLp_id_gaussianReal' (2 : ENNReal) (by simp)
    exact hg.integrable_comp hL.integrable_sq
  have hI : ∫ ω, g ω ^ 2 ∂P = 1 := by
    have h := hg.integral_comp (f := fun x : ℝ => x ^ 2)
      (continuous_pow 2).aestronglyMeasurable
    rw [closed_bounds_gauss_sq_integral] at h
    exact h
  have hle : ∀ ω, (c * (if |g ω| ≤ R then g ω else 0)) *
      (d * (if |g ω| ≤ R then g ω else 0)) ≤ c * d * g ω ^ 2 := by
    intro ω
    split_ifs
    · nlinarith
    · nlinarith [mul_nonneg hc hd, sq_nonneg (g ω)]
  calc
    ∫ ω, (c * (if |g ω| ≤ R then g ω else 0)) *
        (d * (if |g ω| ≤ R then g ω else 0)) ∂P ≤
        ∫ ω, c * d * g ω ^ 2 ∂P :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun ω => by
          dsimp only
          rw [show (c * (if |g ω| ≤ R then g ω else 0)) *
              (d * (if |g ω| ≤ R then g ω else 0)) =
              (c * d) * (if |g ω| ≤ R then g ω else 0) ^ 2 by ring]
          exact mul_nonneg (mul_nonneg hc hd) (sq_nonneg _))
        (hint.const_mul _) (Eventually.of_forall hle)
    _ = c * d := by rw [integral_const_mul, hI, mul_one]

private lemma closed_bounds_cutoffVarpi_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (ℓ J l : ℕ) (α : ℤ) : 0 ≤ cutoffVarpi β ℓ J l α := by
  unfold cutoffVarpi
  split_ifs
  · unfold treeVarpi
    split_ifs <;> try { exact le_rfl } <;> unfold Muon.emaW <;> positivity
  · exact le_rfl

private lemma closed_bounds_cutoff_b {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ℓ J : ℕ} {R : ℝ} (hR : 0 < R) {g : ℤ → Ω → ℝ}
    (hg : IsStdGaussianFamily P g) {q q' : ℝ} (hq : 0 ≤ q) (hq' : 0 ≤ q') :
    0 ≤ pairedB P (cutoffXi β ℓ J R 1 g) (cutoffXi β ℓ J R 2 g) q q' ∧
      pairedB P (cutoffXi β ℓ J R 1 g) (cutoffXi β ℓ J R 2 g) q q' ≤
        Muon.sPow β 2 * β ^ ℓ := by
  have hp := lem_app_vol_closed_cutoff_paired (ℓ := ℓ) (J := J) hβ0 hβ1 hR hg
  have hb := (lem_app_vol_closed_profile_iii hp).2.2.2.2.2.2.1 q (mem_Ici.2 hq) q'
    (mem_Ici.2 hq')
  refine ⟨hb.1, hb.2.trans ((min_le_right _ _).trans ?_)⟩
  have hzero : ∀ α ∉ cutoffLabels J ℓ,
      ∫ ω, cutoffXi β ℓ J R 1 g α ω * cutoffXi β ℓ J R 2 g α ω ∂P = 0 := by
    intro α hα
    have hv : cutoffVarpi β ℓ J 1 α = 0 := by
      unfold cutoffVarpi
      rw [if_neg hα]
    simp [cutoffXi, hv]
  rw [tsum_eq_sum hzero]
  exact (Finset.sum_le_sum fun α hα => by
    simp only [cutoffXi]
    exact closed_bounds_cutoff_cross_term (hg.2.2 α) R _ _
      (closed_bounds_cutoffVarpi_nonneg hβ0 hβ1 ℓ J 1 α)
      (closed_bounds_cutoffVarpi_nonneg hβ0 hβ1 ℓ J 2 α)).trans
        (closed_bounds_cutoff_varpi_sum hβ0 hβ1 ℓ J)

open scoped Matrix.Norms.L2Operator in
private lemma closed_bounds_profileKernel_cutoff {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (ℓ J : ℕ) {R : ℝ} (hR : 0 < R)
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    |profileKernel P Fp.C B (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g)
        Fm Gm s u| ≤
      Muon.sPow Fp.β 2 * (Fp.C.Sout.trace * Fp.C.Sin.trace) * Muon.opNorm Fm *
        Muon.opNorm Gm * Fp.β ^ ℓ /
          ((B : ℝ) ^ 2 * (s * u) * thetaSigma Fp.C B (min s u) ^ 2) := by
  by_cases hC : Fp.C.Sout = 0 ∨ Fp.C.Sin = 0
  · have hz := closed_profileKernel_degenerate (B := B) Fp.C P
      (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) hC Fm Gm s u
    rw [hz, abs_zero]
    rcases hC with hC | hC
    · simp [hC]
    · simp [hC]
  · have hout : Fp.C.Sout ≠ 0 := fun h => hC (Or.inl h)
    have hin : Fp.C.Sin ≠ 0 := fun h => hC (Or.inr h)
    let ξ₁ := cutoffXi Fp.β ℓ J R 1 g
    let ξ₂ := cutoffXi Fp.β ℓ J R 2 g
    let x := branchPt (profileF P ξ₁) Fp.C B s
    let y := branchPt (profileF P ξ₂) Fp.C B u
    have hp := lem_app_vol_closed_cutoff_paired (ℓ := ℓ) (J := J) Fp.hβ.1 Fp.hβ.2 hR hg
    have hm1 := (lem_app_vol_closed_cutoff_masses (ℓ := ℓ) (J := J) Fp.hβ.1 Fp.hβ.2 hR hg
      (l := 1) (Or.inl rfl)).2.2.2
    have hm2 := (lem_app_vol_closed_cutoff_masses (ℓ := ℓ) (J := J) Fp.hβ.1 Fp.hβ.2 hR hg
      (l := 2) (Or.inr rfl)).2.2.2
    have hx := closed_branch_spec Fp.hB hp.profile₁ Fp.C hout hin γstar
      (by simpa only [Nat.cast_max] using hS.1) hs
    have hy := closed_branch_spec Fp.hB hp.profile₂ Fp.C hout hin γstar
      (by simpa only [Nat.cast_max] using hS.1) hu
    have hq : 0 ≤ s * x.1 * x.2.1 :=
      mul_nonneg (mul_nonneg hs.le (by dsimp [x, ξ₁]; exact hx.2.1.le))
        (by dsimp [x, ξ₁]; exact hx.2.2.1.le)
    have hq' : 0 ≤ u * y.1 * y.2.1 :=
      mul_nonneg (mul_nonneg hu.le (by dsimp [y, ξ₂]; exact hy.2.1.le))
        (by dsimp [y, ξ₂]; exact hy.2.2.1.le)
    have hb := closed_bounds_cutoff_b (ℓ := ℓ) (J := J) Fp.hβ.1 Fp.hβ.2 hR hg hq hq'
    have hto : |toutT Fp.C B x y s u Fm| ≤
        opNorm Fm * Fp.C.Sout.trace / ((B : ℝ) * (s * u)) := by
      exact closed_bounds_trace_abs Fp.hB Fp.C.Sout S.uOut S.μ Fd S.huOut
        (Sout_eq_spectral S) Fm hFd (μ_nonneg S) s x.2.2.1 u y.2.2.1 hs
        hx.2.2.2.1.le hu hy.2.2.2.1.le
    have hti : |tinT Fp.C B x y s u Gm| ≤
        opNorm Gm * Fp.C.Sin.trace / ((B : ℝ) * (s * u)) := by
      exact closed_bounds_trace_abs Fp.hB Fp.C.Sin S.vIn S.lam Gd S.hvIn
        (Sin_eq_spectral S) Gm hGd (lam_nonneg S) s x.2.2.2 u y.2.2.2 hs
        hx.2.2.2.2.le hu hy.2.2.2.2.le
    have hdelta := (lem_app_vol_closed_determinant_ii Fp.hB hp hm1 hm2 Fp.C hout hin hs hu).1
    have hdpos := (closed_cutoff_delta_pos Fp.C Fp.hB Fp.hβ.1 Fp.hβ.2 ℓ J R hg hs hu)
    change |s * u * pairedB P ξ₁ ξ₂ (s * x.1 * x.2.1) (u * y.1 * y.2.1) *
        toutT Fp.C B x y s u Fm * tinT Fp.C B x y s u Gm /
          profileDelta P Fp.C B ξ₁ ξ₂ s u| ≤ _
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hs, abs_of_pos hu,
      abs_of_nonneg hb.1, abs_of_pos hdpos]
    have hBreal : (0 : ℝ) < B := by exact_mod_cast Fp.hB
    have htrout : 0 ≤ Fp.C.Sout.trace := Fp.C.psdOut.trace_nonneg
    have htrin : 0 ≤ Fp.C.Sin.trace := Fp.C.psdIn.trace_nonneg
    have hnF : 0 ≤ opNorm Fm := by rw [opNorm_eq_norm]; exact norm_nonneg _
    have hnG : 0 ≤ opNorm Gm := by rw [opNorm_eq_norm]; exact norm_nonneg _
    have hsp : 0 ≤ Muon.sPow Fp.β 2 := tsum_nonneg fun j => sq_nonneg (Muon.emaW Fp.β j)
    have hpow : 0 ≤ Fp.β ^ ℓ := pow_nonneg Fp.hβ.1 ℓ
    have hbe : pairedB P ξ₁ ξ₂ (s * x.1 * x.2.1) (u * y.1 * y.2.1) ≤
        Muon.sPow Fp.β 2 * Fp.β ^ ℓ := by simpa [ξ₁, ξ₂] using hb.2
    have hθ : 0 < thetaSigma Fp.C B (min s u) ^ 2 :=
      (lem_app_vol_closed_determinant_ii Fp.hB hp hm1 hm2 Fp.C hout hin hs hu).2
    calc
      s * u * pairedB P ξ₁ ξ₂ (s * x.1 * x.2.1) (u * y.1 * y.2.1) *
          |toutT Fp.C B x y s u Fm| * |tinT Fp.C B x y s u Gm| /
            profileDelta P Fp.C B ξ₁ ξ₂ s u ≤
        s * u * (Muon.sPow Fp.β 2 * Fp.β ^ ℓ) *
          (opNorm Fm * Fp.C.Sout.trace / ((B : ℝ) * (s * u))) *
          (opNorm Gm * Fp.C.Sin.trace / ((B : ℝ) * (s * u))) /
            thetaSigma Fp.C B (min s u) ^ 2 := by
              apply div_le_div₀ (by positivity) _ hθ hdelta
              gcongr
      _ = _ := by field_simp

private lemma closed_bounds_diag_nonneg {k : ℕ} (U : Mat k k) (hU : Uᵀ * U = 1)
    (d : Fin k → ℝ) (h : (U * Matrix.diagonal d * Uᵀ).PosSemidef) (i : Fin k) :
    0 ≤ d i := by
  have h2 := h.conjTranspose_mul_mul_same U
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  have he : Uᵀ * (U * Matrix.diagonal d * Uᵀ) * U = Matrix.diagonal d := by
    calc
      Uᵀ * (U * Matrix.diagonal d * Uᵀ) * U =
          (Uᵀ * U) * Matrix.diagonal d * (Uᵀ * U) := by simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal d := by rw [hU]; simp
  rw [he] at h2
  simpa using h2.diag_nonneg (i := i)

private lemma closed_bounds_profileKernel_cutoff_nonneg {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (ℓ J : ℕ) {R : ℝ} (hR : 0 < R)
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (hFm : Fm.PosSemidef) (hGm : Gm.PosSemidef)
    (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    0 ≤ profileKernel P Fp.C B (cutoffXi Fp.β ℓ J R 1 g)
      (cutoffXi Fp.β ℓ J R 2 g) Fm Gm s u := by
  by_cases hC : Fp.C.Sout = 0 ∨ Fp.C.Sin = 0
  · rw [closed_profileKernel_degenerate (B := B) Fp.C P
      (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) hC Fm Gm s u]
  · have hout : Fp.C.Sout ≠ 0 := fun h => hC (Or.inl h)
    have hin : Fp.C.Sin ≠ 0 := fun h => hC (Or.inr h)
    let ξ₁ := cutoffXi Fp.β ℓ J R 1 g
    let ξ₂ := cutoffXi Fp.β ℓ J R 2 g
    let x := branchPt (profileF P ξ₁) Fp.C B s
    let y := branchPt (profileF P ξ₂) Fp.C B u
    have hp := lem_app_vol_closed_cutoff_paired (ℓ := ℓ) (J := J) Fp.hβ.1 Fp.hβ.2 hR hg
    have hx := closed_branch_spec Fp.hB hp.profile₁ Fp.C hout hin γstar
      (by simpa only [Nat.cast_max] using hS.1) hs
    have hy := closed_branch_spec Fp.hB hp.profile₂ Fp.C hout hin γstar
      (by simpa only [Nat.cast_max] using hS.1) hu
    have hq : 0 ≤ s * x.1 * x.2.1 :=
      mul_nonneg (mul_nonneg hs.le (by dsimp [x, ξ₁]; exact hx.2.1.le))
        (by dsimp [x, ξ₁]; exact hx.2.2.1.le)
    have hq' : 0 ≤ u * y.1 * y.2.1 :=
      mul_nonneg (mul_nonneg hu.le (by dsimp [y, ξ₂]; exact hy.2.1.le))
        (by dsimp [y, ξ₂]; exact hy.2.2.1.le)
    have hb := (closed_bounds_cutoff_b (ℓ := ℓ) (J := J) Fp.hβ.1 Fp.hβ.2
      hR hg hq hq').1
    have hFd0 : ∀ i, 0 ≤ Fd i := by
      intro i
      apply closed_bounds_diag_nonneg S.uOut S.huOut Fd
      rwa [← hFd]
    have hGd0 : ∀ i, 0 ≤ Gd i := by
      intro i
      apply closed_bounds_diag_nonneg S.vIn S.hvIn Gd
      rwa [← hGd]
    have hto : 0 ≤ toutT Fp.C B x y s u Fm := by
      exact closed_bounds_trace_nonneg Fp.hB Fp.C.Sout S.uOut S.μ Fd S.huOut
        (Sout_eq_spectral S) Fm hFd (μ_nonneg S) hFd0 s x.2.2.1 u y.2.2.1 hs
        (by dsimp [x, ξ₁]; exact hx.2.2.2.1.le) hu
        (by dsimp [y, ξ₂]; exact hy.2.2.2.1.le)
    have hti : 0 ≤ tinT Fp.C B x y s u Gm := by
      exact closed_bounds_trace_nonneg Fp.hB Fp.C.Sin S.vIn S.lam Gd S.hvIn
        (Sin_eq_spectral S) Gm hGd (lam_nonneg S) hGd0 s x.2.2.2 u y.2.2.2 hs
        (by dsimp [x, ξ₁]; exact hx.2.2.2.2.le) hu
        (by dsimp [y, ξ₂]; exact hy.2.2.2.2.le)
    have hd := closed_cutoff_delta_pos Fp.C Fp.hB Fp.hβ.1 Fp.hβ.2 ℓ J R hg hs hu
    change 0 ≤ s * u * pairedB P ξ₁ ξ₂ (s * x.1 * x.2.1) (u * y.1 * y.2.1) *
      toutT Fp.C B x y s u Fm * tinT Fp.C B x y s u Gm /
        profileDelta P Fp.C B ξ₁ ξ₂ s u
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hs.le hu.le) hb) hto) hti)
      hd.le

private lemma closed_bounds_add_filter (f g : ℝ → ℝ) (hf : IsOddBddLip f)
    (hg : IsOddBddLip g) (c : ℝ) : IsOddBddLip (fun x => f x + c * g x) := by
  obtain ⟨M, hM⟩ := hf.2.1
  obtain ⟨N, hN⟩ := hg.2.1
  obtain ⟨L, hL⟩ := hf.2.2
  obtain ⟨K, hK⟩ := hg.2.2
  refine ⟨fun x => by
    change f (-x) + c * g (-x) = -(f x + c * g x)
    rw [hf.1, hg.1]
    ring, ⟨M + |c| * N, fun x => ?_⟩, ⟨L + |c| * K, fun x y => ?_⟩⟩
  · calc
      |f x + c * g x| ≤ |f x| + |c * g x| := abs_add_le _ _
      _ ≤ M + |c| * N := by rw [abs_mul]; gcongr; exacts [hM x, hN x]
  · calc
      |f x + c * g x - (f y + c * g y)| =
          |(f x - f y) + c * (g x - g y)| := by congr 1; ring
      _ ≤ |f x - f y| + |c * (g x - g y)| := abs_add_le _ _
      _ ≤ L * |x - y| + |c| * (K * |x - y|) := by
        rw [abs_mul]
        gcongr
        exacts [hL x y, hK x y]
      _ = (L + |c| * K) * |x - y| := by ring

private lemma closed_bounds_lag_filter_lip (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (f g f' g' : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g)
    (hf' : IsOddBddLip f') (hg' : IsOddBddLip g') :
    |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f g -
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f' g'| ≤
      γstar * opNorm Fm * opNorm Gm *
        (supNorm (fun x => f x - f' x) * supNorm g +
          supNorm f' * supNorm (fun x => g x - g' x)) := by
  have hd1 := closed_bounds_add_filter f f' hf hf' (-1)
  have hd2 := closed_bounds_add_filter g g' hg hg' (-1)
  have he1 : (fun x => f x + -1 * f' x) = fun x => f x - f' x := by
    funext x
    ring
  have he2 : (fun x => g x + -1 * g' x) = fun x => g x - g' x := by
    funext x
    ring
  have lin1 := (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS
    hCSig ℓ f g hf hg).2.2.2.1 (-1) f' hf' Fd Gd
  have lin2 := (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS
    hCSig ℓ f' g hf' hg).2.2.2.2.1 (-1) g' hg' Fd Gd
  have b1 := (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS
    hCSig ℓ _ g hd1 hg).1 Fm Gm Fd Gd hFd hGd
  have b2 := (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS
    hCSig ℓ f' _ hf' hd2).1 Fm Gm Fd Gd hFd hGd
  rw [he1] at b1 lin1
  rw [he2] at b2 lin2
  have hkey : lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f g -
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f' g' =
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (fun x => f x - f' x) g +
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f' (fun x => g x - g' x) := by
    rw [lin1, lin2]
    ring
  rw [hkey]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add b1 b2
    _ = _ := by ring

private lemma closed_bounds_supNorm_nonneg (f : ℝ → ℝ) : 0 ≤ supNorm f :=
  Real.iSup_nonneg fun _ => abs_nonneg _

private lemma closed_bounds_cont_param (Φ : (ℝ → ℝ) → (ℝ → ℝ) → ℝ) (γ : ℝ)
    (hγ : 0 ≤ γ)
    (hΦ : ∀ f g f' g' : ℝ → ℝ, IsOddBddLip f → IsOddBddLip g →
      IsOddBddLip f' → IsOddBddLip g' →
      |Φ f g - Φ f' g'| ≤ γ * (supNorm (fun x => f x - f' x) * supNorm g +
        supNorm f' * supNorm (fun x => g x - g' x)))
    (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    Continuous (fun p : ℝ × ℝ => Φ (iotaF (s + p.1 ^ 2)) (iotaF (u + p.2 ^ 2))) := by
  have hsq : ∀ x : ℝ, 0 ≤ x ^ 2 := fun x => sq_nonneg x
  have hp1 : 0 < s ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hs _
  have hp2 : 0 < u ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hu _
  have hr1 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hr2 : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  set C1 : ℝ := γ / (s ^ ((3 : ℝ) / 2) * (2 * Real.sqrt u))
  set C2 : ℝ := γ / ((2 * Real.sqrt s) * u ^ ((3 : ℝ) / 2))
  have hbound : ∀ x x' y y' : ℝ,
      |Φ (iotaF (s + x ^ 2)) (iotaF (u + y ^ 2)) -
        Φ (iotaF (s + x' ^ 2)) (iotaF (u + y' ^ 2))| ≤
        C1 * |x ^ 2 - x' ^ 2| + C2 * |y ^ 2 - y' ^ 2| := by
    intro x x' y y'
    have hsx : 0 < s + x ^ 2 := by linarith [hsq x]
    have hsx' : 0 < s + x' ^ 2 := by linarith [hsq x']
    have huy : 0 < u + y ^ 2 := by linarith [hsq y]
    have huy' : 0 < u + y' ^ 2 := by linarith [hsq y']
    have hl := hΦ _ _ _ _ (lem_app_vol_sharp_ii hsx one_pos).1
      (lem_app_vol_sharp_ii huy one_pos).1 (lem_app_vol_sharp_ii hsx' one_pos).1
      (lem_app_vol_sharp_ii huy' one_pos).1
    have d1 := (lem_app_vol_sharp_iii hs one_pos (s := s + x ^ 2) (s' := s + x' ^ 2)
      (ϱ := 1) (ϱ' := 1) (ϱ₀ := 1) (by linarith [hsq x])
      (by linarith [hsq x']) le_rfl le_rfl).1
    have d2 := (lem_app_vol_sharp_iii hu one_pos (s := u + y ^ 2) (s' := u + y' ^ 2)
      (ϱ := 1) (ϱ' := 1) (ϱ₀ := 1) (by linarith [hsq y])
      (by linarith [hsq y']) le_rfl le_rfl).1
    have n1 : supNorm (iotaF (u + y ^ 2)) ≤ 1 / (2 * Real.sqrt u) := by
      rw [(lem_app_vol_sharp_ii huy one_pos).2.2.1]
      exact one_div_le_one_div_of_le (by positivity)
        (by have ht := Real.sqrt_le_sqrt (show u ≤ u + y ^ 2 by linarith [hsq y]); linarith)
    have n2 : supNorm (iotaF (s + x' ^ 2)) ≤ 1 / (2 * Real.sqrt s) := by
      rw [(lem_app_vol_sharp_ii hsx' one_pos).2.2.1]
      exact one_div_le_one_div_of_le (by positivity)
        (by have ht := Real.sqrt_le_sqrt (show s ≤ s + x' ^ 2 by linarith [hsq x']); linarith)
    have e1 : |(s + x ^ 2) - (s + x' ^ 2)| = |x ^ 2 - x' ^ 2| := by congr 1; ring
    have e2 : |(u + y ^ 2) - (u + y' ^ 2)| = |y ^ 2 - y' ^ 2| := by congr 1; ring
    rw [e1] at d1
    rw [e2] at d2
    have hn1 := closed_bounds_supNorm_nonneg
      (fun z => iotaF (s + x ^ 2) z - iotaF (s + x' ^ 2) z)
    have hn2 := closed_bounds_supNorm_nonneg
      (fun z => iotaF (u + y ^ 2) z - iotaF (u + y' ^ 2) z)
    have hn3 := closed_bounds_supNorm_nonneg (iotaF (u + y ^ 2))
    have hn4 := closed_bounds_supNorm_nonneg (iotaF (s + x' ^ 2))
    have hd1 : supNorm (fun z => iotaF (s + x ^ 2) z - iotaF (s + x' ^ 2) z) ≤
        |x ^ 2 - x' ^ 2| / s ^ ((3 : ℝ) / 2) := by simpa using d1
    have hd2 : supNorm (fun z => iotaF (u + y ^ 2) z - iotaF (u + y' ^ 2) z) ≤
        |y ^ 2 - y' ^ 2| / u ^ ((3 : ℝ) / 2) := by simpa using d2
    refine hl.trans ?_
    have m1 := mul_le_mul hd1 n1 hn3 (by positivity)
    have m2 := mul_le_mul n2 hd2 hn2 (by positivity)
    have ht := mul_le_mul_of_nonneg_left (add_le_add m1 m2) hγ
    refine ht.trans (le_of_eq ?_)
    dsimp [C1, C2]
    field_simp
  refine continuous_iff_continuousAt.mpr fun b => ?_
  have hb : Tendsto (fun a : ℝ × ℝ => C1 * |a.1 ^ 2 - b.1 ^ 2| +
      C2 * |a.2 ^ 2 - b.2 ^ 2|) (𝓝 b) (𝓝 0) := by
    have hc : Continuous (fun a : ℝ × ℝ => C1 * |a.1 ^ 2 - b.1 ^ 2| +
        C2 * |a.2 ^ 2 - b.2 ^ 2|) := by fun_prop
    simpa using hc.tendsto b
  refine tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero (fun _ => dist_nonneg) (fun a => ?_) hb)
  rw [Real.dist_eq]
  exact hbound _ _ _ _

private lemma closed_bounds_cont_on_of_squares (Φ : (ℝ → ℝ) → (ℝ → ℝ) → ℝ)
    (hΦ : ∀ s u : ℝ, 0 < s → 0 < u → Continuous (fun p : ℝ × ℝ =>
      Φ (iotaF (s + p.1 ^ 2)) (iotaF (u + p.2 ^ 2)))) :
    ContinuousOn (fun p : ℝ × ℝ => Φ (iotaF p.1) (iotaF p.2))
      (Ioi 0 ×ˢ Ioi 0) := by
  intro p hp
  have hp1 : 0 < p.1 := hp.1
  have hp2 : 0 < p.2 := hp.2
  let a : ℝ := p.1 / 2
  let b : ℝ := p.2 / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  let Q : ℝ × ℝ → ℝ × ℝ := fun q =>
    (Real.sqrt (q.1 - a), Real.sqrt (q.2 - b))
  have hQ : Continuous Q := by
    dsimp [Q]
    fun_prop
  have hcomp : Continuous (fun q : ℝ × ℝ =>
      Φ (iotaF (a + (Q q).1 ^ 2)) (iotaF (b + (Q q).2 ^ 2))) := by
    exact (hΦ a b ha hb).comp hQ
  have he1 := (continuousAt_fst : Tendsto (fun q : ℝ × ℝ => q.1) (𝓝 p) (𝓝 p.1)).eventually_const_lt
    (show a < p.1 by dsimp [a]; linarith)
  have he2 := (continuousAt_snd : Tendsto (fun q : ℝ × ℝ => q.2) (𝓝 p) (𝓝 p.2)).eventually_const_lt
    (show b < p.2 by dsimp [b]; linarith)
  have heq : (fun q : ℝ × ℝ =>
      Φ (iotaF (a + (Q q).1 ^ 2)) (iotaF (b + (Q q).2 ^ 2))) =ᶠ[𝓝 p]
      (fun q => Φ (iotaF q.1) (iotaF q.2)) := by
    filter_upwards [he1, he2] with q hq1 hq2
    dsimp [Q]
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    congr 2 <;> ring
  exact (hcomp.continuousAt.congr_of_eventuallyEq heq.symm).continuousWithinAt

/-- `cor:app-vol-closed-bounds`, part (i), snapshot `cr-2026-10-23`. Declaration of record: the
lag kernel `𝔨_ℓ[F,G]` is continuous on `(0,∞)²`; it is nonnegative for positive semidefinite `F`
and `G`; and it vanishes identically when `β = 0` and `ℓ ≥ 1`. LaTeX, verbatim from `section.tex`
(the whole environment):

```latex
\begin{corollary}[Regularity and bounds]\label{cor:app-vol-closed-bounds}
Let $\ell\ge0$ and let $F,G$ be diagonal tests.
\begin{enumerate}[label=(\roman*)]
\item $\mathfrak k_\ell[F,G]$ is continuous on $(0,\infty)^2$. It is nonnegative if
$F$ and $G$ are positive semidefinite. It vanishes identically if $\bmom=0$ and
$\ell\ge1$.
\item For all $s,u>0$,
\[
\abs{\mathfrak k_\ell[F,G](s,u)}\le\frac{\gamma_\star\norm F\norm G}{4\sqrt{su}},\qquad
\abs{\mathfrak k_\ell[F,G](s,u)}\le\frac{\sw2\,\Tr\Sigmaout\,\Tr\Sigmain\,\norm F\norm G\,\bmom^\ell}{B^2\,su\,\theta_\Sigma(\min(s,u))^2}.
\]
\item If $0<\bmom<1$ and $\ell\ge1$, then for all $s,u>0$,
\[
\abs{\mathfrak k_\ell[F,G](s,u)}\le\frac{4\sw2\,\hat q_\bmom\,\norm F\norm G\,\bmom^\ell}{\epsilon_\bmom^2\sqrt{su}} .
\]
\item Consequently
$\abs{\mathfrak k_\ell[F,G](s,u)}\le C_\bmom^{\mathrm{lag}}\norm F\norm G\,\bmom^\ell/\sqrt{su}$ for all
$\ell\ge0$ and $s,u>0$, with $C_\bmom^{\mathrm{lag}}\defeq\max(\gamma_\star/4,\,4\sw2\hat q_\bmom\epsilon_\bmom^{-2})$
for $0<\bmom<1$ and $C_0^{\mathrm{lag}}\defeq\gamma_\star/4$. The constant depends only
on $(\bmom,\gamma_\star)$.
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_vol_closed_bounds_i (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ) :
    ContinuousOn
        (fun p : ℝ × ℝ =>
          lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF p.1) (iotaF p.2))
        (Ioi 0 ×ˢ Ioi 0) ∧
      (Fm.PosSemidef → Gm.PosSemidef → ∀ s u : ℝ, 0 < s → 0 < u →
        0 ≤ lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u)) ∧
      (Fp.β = 0 → 1 ≤ ℓ → ∀ s u : ℝ, 0 < s → 0 < u →
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u) = 0) := by
  constructor
  · let Φ : (ℝ → ℝ) → (ℝ → ℝ) → ℝ := fun f g =>
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f g
    let c : ℝ := γstar * opNorm Fm * opNorm Gm
    have hΦ : ∀ f g f' g' : ℝ → ℝ, IsOddBddLip f → IsOddBddLip g →
        IsOddBddLip f' → IsOddBddLip g' →
        |Φ f g - Φ f' g'| ≤ max c 0 *
          (supNorm (fun x => f x - f' x) * supNorm g +
            supNorm f' * supNorm (fun x => g x - g' x)) := by
      intro f g f' g' hf hg hf' hg'
      have hl := closed_bounds_lag_filter_lip cert γstar CSig Fp S hS hCSig ℓ
        Fm Gm Fd Gd hFd hGd f g f' g' hf hg hf' hg'
      have ht : 0 ≤ supNorm (fun x => f x - f' x) * supNorm g +
          supNorm f' * supNorm (fun x => g x - g' x) :=
        add_nonneg
          (mul_nonneg (closed_bounds_supNorm_nonneg _) (closed_bounds_supNorm_nonneg _))
          (mul_nonneg (closed_bounds_supNorm_nonneg _) (closed_bounds_supNorm_nonneg _))
      exact hl.trans (mul_le_mul_of_nonneg_right (le_max_left c 0) ht)
    apply closed_bounds_cont_on_of_squares Φ
    intro s u hs hu
    exact closed_bounds_cont_param Φ (max c 0) (le_max_right _ _) hΦ s u hs hu
  constructor
  · intro hFm hGm s u hs hu
    obtain ⟨P, hP, hg⟩ := closed_bounds_gauss_exists ℤ
    letI := hP
    have hlim := thm_app_vol_lag_kernel_exists cert γstar CSig Fp S hS hCSig ℓ
      Fm Gm Fd Gd hFd hGd (iotaF s) (iotaF u)
        (lem_app_vol_sharp_ii hs hs).1 (lem_app_vol_sharp_ii hu hu).1
    have hn : -lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd
        (iotaF s) (iotaF u) ≤ 0 := by
      apply le_of_tendsto hlim.neg
      filter_upwards [(tendsto_snd : Tendsto (Prod.snd : ℕ × ℝ → ℝ)
        (atTop ×ˢ atTop) atTop).eventually_gt_atTop 0] with q hq
      rw [(thm_app_vol_closed_kernel_cutoff cert γstar CSig Fp S hS hCSig
        (P := P) ℓ q.1 q.2 hg Fm Gm Fd Gd hFd hGd s u hs hu).1]
      exact neg_nonpos.mpr (closed_bounds_profileKernel_cutoff_nonneg γstar CSig Fp S hS
        ℓ q.1 hq hg Fm Gm Fd Gd hFd hGd hFm hGm s u hs hu)
    linarith
  · intro hβ hℓ s u hs hu
    obtain ⟨P, hP, hg⟩ := closed_bounds_gauss_exists ℤ
    letI := hP
    have hlim := thm_app_vol_lag_kernel_exists cert γstar CSig Fp S hS hCSig ℓ
      Fm Gm Fd Gd hFd hGd (iotaF s) (iotaF u)
        (lem_app_vol_sharp_ii hs hs).1 (lem_app_vol_sharp_ii hu hu).1
    apply tendsto_nhds_unique hlim
    have hev : (fun q : ℕ × ℝ => lagRespCut cert γstar CSig Fp.β ℓ q.1 q.2 B
        S.μ S.lam Fd Gd (iotaF s) (iotaF u)) =ᶠ[atTop ×ˢ atTop]
        (fun _ => 0) := by
      filter_upwards [(tendsto_snd : Tendsto (Prod.snd : ℕ × ℝ → ℝ)
        (atTop ×ˢ atTop) atTop).eventually_gt_atTop 0] with q hq
      rw [(thm_app_vol_closed_kernel_cutoff cert γstar CSig Fp S hS hCSig
        (P := P) ℓ q.1 q.2 hg Fm Gm Fd Gd hFd hGd s u hs hu).1]
      rw [hβ]
      apply abs_nonpos_iff.mp
      have hz := closed_bounds_profileKernel_cutoff γstar CSig Fp S hS ℓ q.1 hq hg
        Fm Gm Fd Gd hFd hGd s u hs hu
      have hℓ0 : ℓ ≠ 0 := by omega
      rw [hβ, zero_pow hℓ0] at hz
      simpa using hz
    rw [tendsto_congr' hev]
    exact tendsto_const_nhds

/-- `cor:app-vol-closed-bounds`, part (ii), snapshot `cr-2026-10-23`. Declaration of record: the two
bounds `|𝔨_ℓ[F,G](s,u)| ≤ γ⋆ ‖F‖ ‖G‖ / (4√(su))` and
`|𝔨_ℓ[F,G](s,u)| ≤ sw₂ Tr Σ_out Tr Σ_in ‖F‖ ‖G‖ β^ℓ / (B² s u θ_Σ(min(s,u))²)`, for every lag and
all `s, u > 0`. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{corollary}[Regularity and bounds]\label{cor:app-vol-closed-bounds}
Let $\ell\ge0$ and let $F,G$ be diagonal tests.
\begin{enumerate}[label=(\roman*)]
\item $\mathfrak k_\ell[F,G]$ is continuous on $(0,\infty)^2$. It is nonnegative if
$F$ and $G$ are positive semidefinite. It vanishes identically if $\bmom=0$ and
$\ell\ge1$.
\item For all $s,u>0$,
\[
\abs{\mathfrak k_\ell[F,G](s,u)}\le\frac{\gamma_\star\norm F\norm G}{4\sqrt{su}},\qquad
\abs{\mathfrak k_\ell[F,G](s,u)}\le\frac{\sw2\,\Tr\Sigmaout\,\Tr\Sigmain\,\norm F\norm G\,\bmom^\ell}{B^2\,su\,\theta_\Sigma(\min(s,u))^2}.
\]
\item If $0<\bmom<1$ and $\ell\ge1$, then for all $s,u>0$,
\[
\abs{\mathfrak k_\ell[F,G](s,u)}\le\frac{4\sw2\,\hat q_\bmom\,\norm F\norm G\,\bmom^\ell}{\epsilon_\bmom^2\sqrt{su}} .
\]
\item Consequently
$\abs{\mathfrak k_\ell[F,G](s,u)}\le C_\bmom^{\mathrm{lag}}\norm F\norm G\,\bmom^\ell/\sqrt{su}$ for all
$\ell\ge0$ and $s,u>0$, with $C_\bmom^{\mathrm{lag}}\defeq\max(\gamma_\star/4,\,4\sw2\hat q_\bmom\epsilon_\bmom^{-2})$
for $0<\bmom<1$ and $C_0^{\mathrm{lag}}\defeq\gamma_\star/4$. The constant depends only
on $(\bmom,\gamma_\star)$.
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_vol_closed_bounds_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ) :
    ∀ s u : ℝ, 0 < s → 0 < u →
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u)| ≤
          γstar * Muon.opNorm Fm * Muon.opNorm Gm / (4 * Real.sqrt (s * u)) ∧
        |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u)| ≤
          Muon.sPow Fp.β 2 * (Fp.C.Sout.trace * Fp.C.Sin.trace) * Muon.opNorm Fm *
            Muon.opNorm Gm * Fp.β ^ ℓ / ((B : ℝ) ^ 2 * (s * u) * thetaSigma Fp.C B (min s u) ^ 2) := by
  intro s u hs hu
  constructor
  · have hb := (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS
      hCSig ℓ (iotaF s) (iotaF u) (lem_app_vol_sharp_ii hs hs).1
        (lem_app_vol_sharp_ii hu hu).1).1 Fm Gm Fd Gd hFd hGd
    rw [(lem_app_vol_sharp_ii hs hs).2.2.1, (lem_app_vol_sharp_ii hu hu).2.2.1] at hb
    calc
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u)| ≤
          γstar * opNorm Fm * opNorm Gm * (1 / (2 * Real.sqrt s)) *
            (1 / (2 * Real.sqrt u)) := hb
      _ = γstar * opNorm Fm * opNorm Gm / (4 * Real.sqrt (s * u)) := by
        rw [Real.sqrt_mul hs.le]
        field_simp
        ring
  · obtain ⟨P, hP, hg⟩ := closed_bounds_gauss_exists ℤ
    letI := hP
    have hlim := thm_app_vol_lag_kernel_exists cert γstar CSig Fp S hS hCSig ℓ
      Fm Gm Fd Gd hFd hGd (iotaF s) (iotaF u)
        (lem_app_vol_sharp_ii hs hs).1 (lem_app_vol_sharp_ii hu hu).1
    apply le_of_tendsto hlim.abs
    filter_upwards [(tendsto_snd : Tendsto (Prod.snd : ℕ × ℝ → ℝ)
      (atTop ×ˢ atTop) atTop).eventually_gt_atTop 0] with p hp
    rw [(thm_app_vol_closed_kernel_cutoff cert γstar CSig Fp S hS hCSig
      (P := P) ℓ p.1 p.2 hg Fm Gm Fd Gd hFd hGd s u hs hu).1]
    exact closed_bounds_profileKernel_cutoff γstar CSig Fp S hS ℓ p.1 hp hg
      Fm Gm Fd Gd hFd hGd s u hs hu

/-
/-- `cor:app-vol-closed-bounds`, part (iii), snapshot `cr-2026-10-23`. Declaration of record: for
`0 < β < 1` and `ℓ ≥ 1`, `|𝔨_ℓ[F,G](s,u)| ≤ 4 sw₂ q̂_β ‖F‖ ‖G‖ β^ℓ / (ε_β² √(su))`. The constants
`q̂_β` and `ε_β` depend only on `(β, γ⋆)` (`qhatBeta`, `epsBeta`). LaTeX, verbatim from `section.tex`
(the whole environment):

```latex
\begin{corollary}[Regularity and bounds]\label{cor:app-vol-closed-bounds}
Let $\ell\ge0$ and let $F,G$ be diagonal tests.
\begin{enumerate}[label=(\roman*)]
\item $\mathfrak k_\ell[F,G]$ is continuous on $(0,\infty)^2$. It is nonnegative if
$F$ and $G$ are positive semidefinite. It vanishes identically if $\bmom=0$ and
$\ell\ge1$.
\item For all $s,u>0$,
\[
\abs{\mathfrak k_\ell[F,G](s,u)}\le\frac{\gamma_\star\norm F\norm G}{4\sqrt{su}},\qquad
\abs{\mathfrak k_\ell[F,G](s,u)}\le\frac{\sw2\,\Tr\Sigmaout\,\Tr\Sigmain\,\norm F\norm G\,\bmom^\ell}{B^2\,su\,\theta_\Sigma(\min(s,u))^2}.
\]
\item If $0<\bmom<1$ and $\ell\ge1$, then for all $s,u>0$,
\[
\abs{\mathfrak k_\ell[F,G](s,u)}\le\frac{4\sw2\,\hat q_\bmom\,\norm F\norm G\,\bmom^\ell}{\epsilon_\bmom^2\sqrt{su}} .
\]
\item Consequently
$\abs{\mathfrak k_\ell[F,G](s,u)}\le C_\bmom^{\mathrm{lag}}\norm F\norm G\,\bmom^\ell/\sqrt{su}$ for all
$\ell\ge0$ and $s,u>0$, with $C_\bmom^{\mathrm{lag}}\defeq\max(\gamma_\star/4,\,4\sw2\hat q_\bmom\epsilon_\bmom^{-2})$
for $0<\bmom<1$ and $C_0^{\mathrm{lag}}\defeq\gamma_\star/4$. The constant depends only
on $(\bmom,\gamma_\star)$.
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_vol_closed_bounds_iii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (hβpos : 0 < Fp.β) (ℓ : ℕ)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ) :
    ∀ s u : ℝ, 0 < s → 0 < u → 1 ≤ ℓ →
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u)| ≤
        4 * Muon.sPow Fp.β 2 * qhatBeta Fp.β γstar * Muon.opNorm Fm * Muon.opNorm Gm *
          Fp.β ^ ℓ / (epsBeta Fp.β γstar ^ 2 * Real.sqrt (s * u)) := by
  sorry

/-- `cor:app-vol-closed-bounds`, part (iv), snapshot `cr-2026-10-23`. Declaration of record: for
every lag, `|𝔨_ℓ[F,G](s,u)| ≤ C^lag_β ‖F‖ ‖G‖ β^ℓ / √(su)` with `C^lag_β = clagConst β γ⋆`, which
depends only on `(β, γ⋆)`, uniformly in the dimension and in the lag. LaTeX, verbatim from
`section.tex` (the whole environment):

```latex
\begin{corollary}[Regularity and bounds]\label{cor:app-vol-closed-bounds}
Let $\ell\ge0$ and let $F,G$ be diagonal tests.
\begin{enumerate}[label=(\roman*)]
\item $\mathfrak k_\ell[F,G]$ is continuous on $(0,\infty)^2$. It is nonnegative if
$F$ and $G$ are positive semidefinite. It vanishes identically if $\bmom=0$ and
$\ell\ge1$.
\item For all $s,u>0$,
\[
\abs{\mathfrak k_\ell[F,G](s,u)}\le\frac{\gamma_\star\norm F\norm G}{4\sqrt{su}},\qquad
\abs{\mathfrak k_\ell[F,G](s,u)}\le\frac{\sw2\,\Tr\Sigmaout\,\Tr\Sigmain\,\norm F\norm G\,\bmom^\ell}{B^2\,su\,\theta_\Sigma(\min(s,u))^2}.
\]
\item If $0<\bmom<1$ and $\ell\ge1$, then for all $s,u>0$,
\[
\abs{\mathfrak k_\ell[F,G](s,u)}\le\frac{4\sw2\,\hat q_\bmom\,\norm F\norm G\,\bmom^\ell}{\epsilon_\bmom^2\sqrt{su}} .
\]
\item Consequently
$\abs{\mathfrak k_\ell[F,G](s,u)}\le C_\bmom^{\mathrm{lag}}\norm F\norm G\,\bmom^\ell/\sqrt{su}$ for all
$\ell\ge0$ and $s,u>0$, with $C_\bmom^{\mathrm{lag}}\defeq\max(\gamma_\star/4,\,4\sw2\hat q_\bmom\epsilon_\bmom^{-2})$
for $0<\bmom<1$ and $C_0^{\mathrm{lag}}\defeq\gamma_\star/4$. The constant depends only
on $(\bmom,\gamma_\star)$.
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_vol_closed_bounds_iv (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ) :
    ∀ s u : ℝ, 0 < s → 0 < u →
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u)| ≤
        clagConst Fp.β γstar * Muon.opNorm Fm * Muon.opNorm Gm * Fp.β ^ ℓ / Real.sqrt (s * u) := by
  intro s u hs hu
  by_cases hβ : Fp.β = 0
  · by_cases hℓ : ℓ = 0
    · subst hℓ
      have hb := (cor_app_vol_closed_bounds_ii cert γstar CSig Fp S hS hCSig 0
        Fm Gm Fd Gd hFd hGd s u hs hu).1
      rw [hβ] at hb
      rw [clagConst, if_pos hβ, hβ]
      norm_num
      convert hb using 1 <;> ring
    · have hz := (cor_app_vol_closed_bounds_i cert γstar CSig Fp S hS hCSig ℓ
        Fm Gm Fd Gd hFd hGd).2.2 hβ (by omega) s u hs hu
      rw [hz, abs_zero, hβ, zero_pow hℓ]
      norm_num
  · have hβpos : 0 < Fp.β := lt_of_le_of_ne Fp.hβ.1 (Ne.symm hβ)
    by_cases hℓ : ℓ = 0
    · subst hℓ
      have hb := (cor_app_vol_closed_bounds_ii cert γstar CSig Fp S hS hCSig 0
        Fm Gm Fd Gd hFd hGd s u hs hu).1
      have hsqrt : 0 < Real.sqrt (s * u) := Real.sqrt_pos.2 (mul_pos hs hu)
      have hnF : 0 ≤ opNorm Fm := by unfold opNorm; exact norm_nonneg _
      have hnG : 0 ≤ opNorm Gm := by unfold opNorm; exact norm_nonneg _
      refine hb.trans ?_
      simp only [clagConst, hβ, if_false, pow_zero, mul_one]
      calc
        γstar * opNorm Fm * opNorm Gm / (4 * Real.sqrt (s * u)) =
            (γstar / 4) * opNorm Fm * opNorm Gm / Real.sqrt (s * u) := by ring
        _ ≤ max (γstar / 4)
              (4 * Muon.sPow Fp.β 2 * qhatBeta Fp.β γstar / epsBeta Fp.β γstar ^ 2) *
              opNorm Fm * opNorm Gm / Real.sqrt (s * u) := by
          apply div_le_div_of_nonneg_right _ hsqrt.le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hnF) hnG
    · have hb := cor_app_vol_closed_bounds_iii cert γstar CSig Fp S hS hCSig hβpos ℓ
        Fm Gm Fd Gd hFd hGd s u hs hu (by omega)
      have hsqrt : 0 < Real.sqrt (s * u) := Real.sqrt_pos.2 (mul_pos hs hu)
      have hnF : 0 ≤ opNorm Fm := by unfold opNorm; exact norm_nonneg _
      have hnG : 0 ≤ opNorm Gm := by unfold opNorm; exact norm_nonneg _
      have hpow : 0 ≤ Fp.β ^ ℓ := pow_nonneg Fp.hβ.1 ℓ
      refine hb.trans ?_
      simp only [clagConst, hβ, if_false]
      calc
        4 * Muon.sPow Fp.β 2 * qhatBeta Fp.β γstar * opNorm Fm * opNorm Gm *
              Fp.β ^ ℓ / (epsBeta Fp.β γstar ^ 2 * Real.sqrt (s * u)) =
            (4 * Muon.sPow Fp.β 2 * qhatBeta Fp.β γstar /
                epsBeta Fp.β γstar ^ 2) * opNorm Fm * opNorm Gm * Fp.β ^ ℓ /
              Real.sqrt (s * u) := by ring
        _ ≤ max (γstar / 4)
              (4 * Muon.sPow Fp.β 2 * qhatBeta Fp.β γstar / epsBeta Fp.β γstar ^ 2) *
              opNorm Fm * opNorm Gm * Fp.β ^ ℓ / Real.sqrt (s * u) := by
          apply div_le_div_of_nonneg_right _ hsqrt.le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_right _ _) hnF) hnG) hpow
-/

/-- Scaled Cauchy kernel helper for `thm:app-vol-closed-filtered` (P-D.18.P7). -/
private lemma closed_filt_key {a : ℝ} (ha : 0 < a) (y : ℝ) :
    (a + y ^ 2)⁻¹ = a⁻¹ * (1 + ((Real.sqrt a)⁻¹ * y) ^ 2)⁻¹ := by
  have h2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have ha' : a ≠ 0 := ha.ne'
  rw [mul_pow, inv_pow, h2]
  field_simp

private lemma closed_filt_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : ℝ => (a + y ^ 2)⁻¹) := by
  have hb : (Real.sqrt a)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 ha).ne'
  refine ((integrable_inv_one_add_mul_sq hb).const_mul a⁻¹).congr
    (Filter.Eventually.of_forall fun y => ?_)
  exact (closed_filt_key ha y).symm

private lemma closed_filt_integral {a : ℝ} (ha : 0 < a) :
    ∫ y in Ioi (0 : ℝ), (a + y ^ 2)⁻¹ = Real.pi / (2 * Real.sqrt a) := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hinv : a⁻¹ = (Real.sqrt a)⁻¹ * (Real.sqrt a)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt ha.le]
  have h := integral_comp_mul_left_Ioi (fun u : ℝ => (1 + u ^ 2)⁻¹) 0 (inv_pos.2 hs)
  simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero, inv_inv,
    smul_eq_mul] at h
  simp_rw [closed_filt_key ha]
  rw [integral_const_mul, h, hinv]
  field_simp

private lemma closed_filt_pointwise (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (ϱ ϱ' : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') (x y : ℝ) :
    |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF (ϱ + x ^ 2))
        (iotaF (ϱ' + y ^ 2))| ≤
      (Muon.sPow Fp.β 2 * (Fp.C.Sout.trace * Fp.C.Sin.trace) * Muon.opNorm Fm *
        Muon.opNorm Gm * (1 + kappaSigma Fp.C B / min ϱ ϱ') ^ 2 * Fp.β ^ ℓ /
          (B : ℝ) ^ 2) * (ϱ + x ^ 2)⁻¹ * (ϱ' + y ^ 2)⁻¹ := by
  have hnF : 0 ≤ Muon.opNorm Fm := by unfold Muon.opNorm; exact norm_nonneg _
  have hnG : 0 ≤ Muon.opNorm Gm := by unfold Muon.opNorm; exact norm_nonneg _
  have htrout : 0 ≤ Fp.C.Sout.trace := Fp.C.psdOut.trace_nonneg
  have htrin : 0 ≤ Fp.C.Sin.trace := Fp.C.psdIn.trace_nonneg
  have hsP : 0 ≤ Muon.sPow Fp.β 2 := by
    unfold Muon.sPow; exact tsum_nonneg fun j => sq_nonneg _
  have hβℓ : 0 ≤ Fp.β ^ ℓ := pow_nonneg Fp.hβ.1 ℓ
  have hκ : 0 ≤ kappaSigma Fp.C B := by
    unfold kappaSigma
    exact le_max_of_le_left (mul_nonneg (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) htrin)
      (by unfold Muon.opNorm; exact norm_nonneg _))
  have hmpos : 0 < min ϱ ϱ' := lt_min hϱ hϱ'
  have hX : 0 ≤ Muon.sPow Fp.β 2 * (Fp.C.Sout.trace * Fp.C.Sin.trace) * Muon.opNorm Fm *
      Muon.opNorm Gm * Fp.β ^ ℓ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hsP (mul_nonneg htrout htrin)) hnF) hnG) hβℓ
  have hs : 0 < ϱ + x ^ 2 := add_pos_of_pos_of_nonneg hϱ (sq_nonneg x)
  have hu : 0 < ϱ' + y ^ 2 := add_pos_of_pos_of_nonneg hϱ' (sq_nonneg y)
  have hb := (cor_app_vol_closed_bounds_ii cert γstar CSig Fp S hS hCSig ℓ Fm Gm Fd Gd hFd hGd
    (ϱ + x ^ 2) (ϱ' + y ^ 2) hs hu).2
  have hmt : min ϱ ϱ' ≤ min (ϱ + x ^ 2) (ϱ' + y ^ 2) :=
    le_min ((min_le_left _ _).trans (le_add_of_nonneg_right (sq_nonneg x)))
      ((min_le_right _ _).trans (le_add_of_nonneg_right (sq_nonneg y)))
  have htpos : 0 < min (ϱ + x ^ 2) (ϱ' + y ^ 2) := lt_min hs hu
  have hθ : 1 / thetaSigma Fp.C B (min (ϱ + x ^ 2) (ϱ' + y ^ 2)) ^ 2 ≤
      (1 + kappaSigma Fp.C B / min ϱ ϱ') ^ 2 := by
    have htk : 0 < min (ϱ + x ^ 2) (ϱ' + y ^ 2) + kappaSigma Fp.C B := by linarith
    have ht0 : min (ϱ + x ^ 2) (ϱ' + y ^ 2) ≠ 0 := htpos.ne'
    have htk0 : min (ϱ + x ^ 2) (ϱ' + y ^ 2) + kappaSigma Fp.C B ≠ 0 := htk.ne'
    have e : 1 / thetaSigma Fp.C B (min (ϱ + x ^ 2) (ϱ' + y ^ 2)) ^ 2 =
        (1 + kappaSigma Fp.C B / min (ϱ + x ^ 2) (ϱ' + y ^ 2)) ^ 2 := by
      unfold thetaSigma
      field_simp
    rw [e]
    have h1 : kappaSigma Fp.C B / min (ϱ + x ^ 2) (ϱ' + y ^ 2) ≤
        kappaSigma Fp.C B / min ϱ ϱ' := div_le_div_of_nonneg_left hκ hmpos hmt
    have h2 : 0 ≤ 1 + kappaSigma Fp.C B / min (ϱ + x ^ 2) (ϱ' + y ^ 2) := by
      have := div_nonneg hκ htpos.le
      linarith
    nlinarith [mul_nonneg (sub_nonneg.2 h1) h2, sq_nonneg
      (kappaSigma Fp.C B / min ϱ ϱ' -
        kappaSigma Fp.C B / min (ϱ + x ^ 2) (ϱ' + y ^ 2))]
  refine hb.trans ?_
  calc _ = (Muon.sPow Fp.β 2 * (Fp.C.Sout.trace * Fp.C.Sin.trace) * Muon.opNorm Fm *
          Muon.opNorm Gm * Fp.β ^ ℓ) *
        (1 / thetaSigma Fp.C B (min (ϱ + x ^ 2) (ϱ' + y ^ 2)) ^ 2) /
        ((B : ℝ) ^ 2 * ((ϱ + x ^ 2) * (ϱ' + y ^ 2))) := by
          simp only [div_eq_mul_inv, mul_inv, one_div]; ring
    _ ≤ (Muon.sPow Fp.β 2 * (Fp.C.Sout.trace * Fp.C.Sin.trace) * Muon.opNorm Fm *
          Muon.opNorm Gm * Fp.β ^ ℓ) * (1 + kappaSigma Fp.C B / min ϱ ϱ') ^ 2 /
        ((B : ℝ) ^ 2 * ((ϱ + x ^ 2) * (ϱ' + y ^ 2))) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hθ hX)
        (mul_nonneg (sq_nonneg _) (mul_nonneg hs.le hu.le))
    _ = _ := by simp only [div_eq_mul_inv, mul_inv]; ring

/- `prop_app_vol_closed_reductions_i` is relocated below `thm_app_vol_closed_kernel_ii`. -/
/-- `thm:app-vol-closed-filtered`, part (i), snapshot `cr-2026-10-23`. Declaration of record: for
`ℓ ≥ 0`, diagonal `F, G` and `ϱ, ϱ' > 0`, the double integral of `𝔨_ℓ[F,G](ϱ+x², ϱ'+y²)` over
`(0,∞)²` converges absolutely, and `C̄_ℓ[F,G](ϱ,ϱ') = (4/π²) ∫_0^∞∫_0^∞ 𝔨_ℓ[F,G](ϱ+x², ϱ'+y²) dx dy`.
LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Filtered lag coefficients]\label{thm:app-vol-closed-filtered}
Let $\ell\ge0$, let $F,G$ be diagonal tests, let $\ridge,\ridge'>0$ and
$\ridge_m\defeq\min(\ridge,\ridge')$. The double integral below converges absolutely,
and
\begin{equation}\label{eqn:app-vol-closed-filtered}
\overline C_\ell[F,G](\ridge,\ridge')=\frac4{\pi^2}\int_0^\infty\!\!\int_0^\infty\mathfrak k_\ell[F,G](\ridge+x^2,\ridge'+y^2)\,dx\,dy,
\end{equation}
\[
\abs{\overline C_\ell[F,G](\ridge,\ridge')}\le\frac{\sw2\,\Tr\Sigmaout\,\Tr\Sigmain\,\norm F\norm G\,(1+\kappa_\Sigma/\ridge_m)^2\,\bmom^\ell}{B^2\sqrt{\ridge\ridge'}} .
\]
\end{theorem}
```
-/
theorem thm_app_vol_closed_filtered_i (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (ϱ ϱ' : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') :
    IntegrableOn
        (fun p : ℝ × ℝ =>
          lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF (ϱ + p.1 ^ 2))
            (iotaF (ϱ' + p.2 ^ 2)))
        (Ioi 0 ×ˢ Ioi 0) ∧
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (omegaF ϱ) (omegaF ϱ') =
        (4 / Real.pi ^ 2) * ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
          lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF (ϱ + x ^ 2))
            (iotaF (ϱ' + y ^ 2)) := by
  let Fm : Mat m m := S.uOut * Matrix.diagonal Fd * S.uOutᵀ
  let Gm : Mat n n := S.vIn * Matrix.diagonal Gd * S.vInᵀ
  let f : ℝ × ℝ → ℝ := fun p =>
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF (ϱ + p.1 ^ 2))
      (iotaF (ϱ' + p.2 ^ 2))
  let A : ℝ := Muon.sPow Fp.β 2 * (Fp.C.Sout.trace * Fp.C.Sin.trace) *
    Muon.opNorm Fm * Muon.opNorm Gm * (1 + kappaSigma Fp.C B / min ϱ ϱ') ^ 2 *
      Fp.β ^ ℓ / (B : ℝ) ^ 2
  have hQmeas : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hcont0 := (cor_app_vol_closed_bounds_i cert γstar CSig Fp S hS hCSig ℓ
    Fm Gm Fd Gd rfl rfl).1
  have hmap : Continuous (fun p : ℝ × ℝ => (ϱ + p.1 ^ 2, ϱ' + p.2 ^ 2)) :=
    (continuous_const.add (continuous_fst.pow 2)).prodMk
      (continuous_const.add (continuous_snd.pow 2))
  have hcont : ContinuousOn f (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    apply hcont0.comp hmap.continuousOn
    intro p hp
    exact ⟨add_pos_of_pos_of_nonneg hϱ (sq_nonneg p.1),
      add_pos_of_pos_of_nonneg hϱ' (sq_nonneg p.2)⟩
  have hmajor : IntegrableOn
      (fun p : ℝ × ℝ => A * (ϱ + p.1 ^ 2)⁻¹ * (ϱ' + p.2 ^ 2)⁻¹)
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    simpa only [mul_assoc] using
      ((closed_filt_integrable hϱ).integrableOn.mul_prod
        (closed_filt_integrable hϱ').integrableOn).const_mul A
  have hint : IntegrableOn f (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    refine hmajor.mono' (hcont.aestronglyMeasurable hQmeas) ?_
    refine ae_restrict_of_forall_mem hQmeas fun p _ => ?_
    rw [Real.norm_eq_abs]
    exact closed_filt_pointwise cert γstar CSig Fp S hS hCSig ℓ Fm Gm Fd Gd rfl rfl
      ϱ ϱ' hϱ hϱ' p.1 p.2
  refine ⟨hint, ?_⟩
  let Q : ℕ → Set (ℝ × ℝ) := fun k =>
    Ioc (0 : ℝ) ((k : ℝ) + 1) ×ˢ Ioc (0 : ℝ) ((k : ℝ) + 1)
  have hQmeas' : ∀ k, MeasurableSet (Q k) := fun _ => measurableSet_Ioc.prod measurableSet_Ioc
  have hQmono : Monotone Q := by
    intro a b hab p hp
    have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
      rw [add_le_add_iff_right]
      exact_mod_cast hab
    exact ⟨⟨hp.1.1, hp.1.2.trans hab'⟩, ⟨hp.2.1, hp.2.2.trans hab'⟩⟩
  have hQunion : (⋃ k, Q k) = Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    ext p
    simp only [mem_iUnion, mem_prod, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨k, ⟨hp1, _⟩, hp2, _⟩
      exact ⟨hp1, hp2⟩
    · rintro ⟨hp1, hp2⟩
      obtain ⟨k, hk⟩ := exists_nat_gt (max p.1 p.2)
      refine ⟨k, ⟨hp1, ?_⟩, hp2, ?_⟩
      · exact (le_max_left _ _).trans (hk.le.trans (le_add_of_nonneg_right zero_le_one))
      · exact (le_max_right _ _).trans (hk.le.trans (le_add_of_nonneg_right zero_le_one))
  have hlimProd : Tendsto (fun k => ∫ p in Q k, f p) atTop
      (𝓝 (∫ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), f p)) := by
    have h := tendsto_setIntegral_of_monotone hQmeas' hQmono (by
      rw [hQunion]
      exact hint)
    rwa [hQunion] at h
  have hQsub : ∀ k, Q k ⊆ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    intro k p hp
    exact ⟨hp.1.1, hp.2.1⟩
  have hiter : ∀ k : ℕ,
      (∫ x in (0 : ℝ)..((k : ℝ) + 1), ∫ y in (0 : ℝ)..((k : ℝ) + 1), f (x, y)) =
        ∫ p in Q k, f p := by
    intro k
    calc
      (∫ x in (0 : ℝ)..((k : ℝ) + 1), ∫ y in (0 : ℝ)..((k : ℝ) + 1), f (x, y)) =
          ∫ x in Ioc (0 : ℝ) ((k : ℝ) + 1),
            ∫ y in Ioc (0 : ℝ) ((k : ℝ) + 1), f (x, y) := by
              rw [intervalIntegral.integral_of_le (by positivity)]
              congr with x
              rw [intervalIntegral.integral_of_le (by positivity)]
      _ = ∫ p in Q k, f p :=
        (setIntegral_prod f (hint.mono_set (hQsub k))).symm
  have hlimIter : Tendsto
      (fun k : ℕ => ∫ x in (0 : ℝ)..((k : ℝ) + 1),
        ∫ y in (0 : ℝ)..((k : ℝ) + 1), f (x, y)) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), f (x, y))) := by
    have hp := hlimProd.congr' (Eventually.of_forall fun k => (hiter k).symm)
    rw [Measure.volume_eq_prod] at hp
    rw [setIntegral_prod f hint] at hp
    exact hp
  let c : ℝ := lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd
    (omegaF ϱ) (omegaF ϱ')
  let q : ℕ → ℝ := fun k => (4 / Real.pi ^ 2) *
    ∫ x in (0 : ℝ)..((k : ℝ) + 1), ∫ y in (0 : ℝ)..((k : ℝ) + 1), f (x, y)
  let E : ℝ := 4 * CSig * (γstar * Real.sqrt γstar) * opNorm Fm * opNorm Gm
  have happrox : ∀ k : ℕ, |c - q k| ≤ E / (Real.pi * ((k : ℝ) + 1)) := by
    intro k
    simpa only [c, q, E, f] using
      (thm_app_vol_integrated_i cert γstar CSig Fp S hS hCSig ℓ ((k : ℝ) + 1)
        (by norm_num) Fm Gm Fd Gd rfl rfl ϱ ϱ' hϱ hϱ').2
  have hden : Tendsto (fun k : ℕ => Real.pi * ((k : ℝ) + 1)) atTop atTop :=
    Tendsto.const_mul_atTop Real.pi_pos
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have herr : Tendsto (fun k : ℕ => E / (Real.pi * ((k : ℝ) + 1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hqc : Tendsto q atTop (𝓝 c) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun k => dist_nonneg) (fun k => ?_) herr)
    rw [Real.dist_eq, abs_sub_comm]
    exact happrox k
  have hqfull := hlimIter.const_mul (4 / Real.pi ^ 2)
  change c = (4 / Real.pi ^ 2) * ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), f (x, y)
  exact tendsto_nhds_unique hqc hqfull

/-- `thm:app-vol-closed-filtered`, part (ii), snapshot `cr-2026-10-23`. Declaration of record: the
filtered bound `|C̄_ℓ[F,G](ϱ,ϱ')| ≤ sw₂ Tr Σ_out Tr Σ_in ‖F‖ ‖G‖ (1 + κ_Σ/min(ϱ,ϱ'))² β^ℓ /
(B² √(ϱϱ'))`, for diagonal `F, G` (`Fm`, `Gm`) and `ϱ, ϱ' > 0`. The constant `κ_Σ` is
`kappaSigma`. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Filtered lag coefficients]\label{thm:app-vol-closed-filtered}
Let $\ell\ge0$, let $F,G$ be diagonal tests, let $\ridge,\ridge'>0$ and
$\ridge_m\defeq\min(\ridge,\ridge')$. The double integral below converges absolutely,
and
\begin{equation}\label{eqn:app-vol-closed-filtered}
\overline C_\ell[F,G](\ridge,\ridge')=\frac4{\pi^2}\int_0^\infty\!\!\int_0^\infty\mathfrak k_\ell[F,G](\ridge+x^2,\ridge'+y^2)\,dx\,dy,
\end{equation}
\[
\abs{\overline C_\ell[F,G](\ridge,\ridge')}\le\frac{\sw2\,\Tr\Sigmaout\,\Tr\Sigmain\,\norm F\norm G\,(1+\kappa_\Sigma/\ridge_m)^2\,\bmom^\ell}{B^2\sqrt{\ridge\ridge'}} .
\]
\end{theorem}
```
-/
theorem thm_app_vol_closed_filtered_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ) (ϱ ϱ' : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') :
    |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (omegaF ϱ) (omegaF ϱ')| ≤
      Muon.sPow Fp.β 2 * (Fp.C.Sout.trace * Fp.C.Sin.trace) * Muon.opNorm Fm * Muon.opNorm Gm *
        (1 + kappaSigma Fp.C B / min ϱ ϱ') ^ 2 * Fp.β ^ ℓ /
        ((B : ℝ) ^ 2 * Real.sqrt (ϱ * ϱ')) := by
  have hid := (thm_app_vol_closed_filtered_i cert γstar CSig Fp S hS hCSig ℓ Fd Gd ϱ ϱ' hϱ hϱ').2
  have hB : (B : ℝ) ≠ 0 := by exact_mod_cast Fp.hB.ne'
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Muon.sPow Fp.β 2 * (Fp.C.Sout.trace * Fp.C.Sin.trace) *
      Muon.opNorm Fm * Muon.opNorm Gm * (1 + kappaSigma Fp.C B / min ϱ ϱ') ^ 2 * Fp.β ^ ℓ /
        (B : ℝ) ^ 2 := ⟨_, rfl⟩
  -- pointwise majorant on the quadrant
  have hpt : ∀ x ∈ Ioi (0 : ℝ), ∀ y ∈ Ioi (0 : ℝ),
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2))| ≤
        A * (ϱ + x ^ 2)⁻¹ * (ϱ' + y ^ 2)⁻¹ := by
    intro x _ y _
    simpa only [hA] using closed_filt_pointwise cert γstar CSig Fp S hS hCSig ℓ
      Fm Gm Fd Gd hFd hGd ϱ ϱ' hϱ hϱ' x y
  -- integrate the majorant over the quadrant
  have hJ : ‖∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2))‖ ≤
        (A * (Real.pi / (2 * Real.sqrt ϱ'))) * (Real.pi / (2 * Real.sqrt ϱ)) := by
    have hin : ∀ x ∈ Ioi (0 : ℝ), ‖∫ y in Ioi (0 : ℝ),
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2))‖ ≤
          (A * (Real.pi / (2 * Real.sqrt ϱ'))) * (ϱ + x ^ 2)⁻¹ := by
      intro x hx
      have hg : Integrable (fun y : ℝ => A * (ϱ + x ^ 2)⁻¹ * (ϱ' + y ^ 2)⁻¹)
          (volume.restrict (Ioi (0 : ℝ))) :=
        ((closed_filt_integrable hϱ').const_mul (A * (ϱ + x ^ 2)⁻¹)).integrableOn
      refine (norm_integral_le_of_norm_le hg ?_).trans_eq ?_
      · refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
        rw [Real.norm_eq_abs]
        exact hpt x hx y hy
      · rw [integral_const_mul, closed_filt_integral hϱ']
        ring
    have hg2 : Integrable (fun x : ℝ => (A * (Real.pi / (2 * Real.sqrt ϱ'))) * (ϱ + x ^ 2)⁻¹)
        (volume.restrict (Ioi (0 : ℝ))) :=
      ((closed_filt_integrable hϱ).const_mul _).integrableOn
    refine (norm_integral_le_of_norm_le hg2 (ae_restrict_of_forall_mem measurableSet_Ioi hin)).trans_eq ?_
    rw [integral_const_mul, closed_filt_integral hϱ]
  rw [Real.norm_eq_abs] at hJ
  have hs1 : 0 < Real.sqrt ϱ := Real.sqrt_pos.2 hϱ
  have hs2 : 0 < Real.sqrt ϱ' := Real.sqrt_pos.2 hϱ'
  have hsq : Real.sqrt (ϱ * ϱ') = Real.sqrt ϱ * Real.sqrt ϱ' := Real.sqrt_mul hϱ.le ϱ'
  rw [hid, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / Real.pi ^ 2)]
  refine (mul_le_mul_of_nonneg_left hJ (by positivity)).trans (le_of_eq ?_)
  rw [hsq, hA]
  have hs1' : Real.sqrt ϱ ≠ 0 := hs1.ne'
  have hs2' : Real.sqrt ϱ' ≠ 0 := hs2.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  try ring

private lemma closed_modeH_pointwise (γstar CSig : ℝ) {m n B : ℕ}
    (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℓ : ℕ)
    {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (i : Fin m) (j : Fin n) (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    0 ≤ closedModeH P Fp.C B Fp.β ℓ g (S.μ i) (S.lam j) s u ∧
      closedModeH P Fp.C B Fp.β ℓ g (S.μ i) (S.lam j) s u ≤
        S.μ i * S.lam j * Muon.sPow Fp.β 2 * Fp.β ^ ℓ /
          (s * u * thetaSigma Fp.C B (min s u) ^ 2) := by
  by_cases hC : Fp.C.Sout = 0 ∨ Fp.C.Sin = 0
  · rcases hC with hout | hin
    · have hi : S.μ i = 0 := closed_eigenvalues_zero Fp.C.Sout S.uOut S.μ S.huOut
        (fun k => eig_u S k) hout i
      simp [closedModeH, hi]
    · have hj : S.lam j = 0 := closed_eigenvalues_zero Fp.C.Sin S.vIn S.lam S.hvIn
        (fun k => eig_v S k) hin j
      simp [closedModeH, hj]
  · have hout : Fp.C.Sout ≠ 0 := fun h => hC (Or.inl h)
    have hin : Fp.C.Sin ≠ 0 := fun h => hC (Or.inr h)
    let x := branchPt (profileF P (emaXi₁ Fp.β ℓ g)) Fp.C B s
    let y := branchPt (profileF P (emaXi₂ Fp.β ℓ g)) Fp.C B u
    have hp := lem_app_vol_closed_profile_iv Fp.hβ.1 Fp.hβ.2 hg
    have hx := closed_branch_spec Fp.hB hp.2.2.2.2.2.profile₁ Fp.C hout hin γstar
      (by simpa only [Nat.cast_max] using hS.1) hs
    have hy := closed_branch_spec Fp.hB hp.2.2.2.2.2.profile₂ Fp.C hout hin γstar
      (by simpa only [Nat.cast_max] using hS.1) hu
    have hq : 0 ≤ s * x.1 * x.2.1 :=
      mul_nonneg (mul_nonneg hs.le (by dsimp [x]; exact hx.2.1.le))
        (by dsimp [x]; exact hx.2.2.1.le)
    have hq' : 0 ≤ u * y.1 * y.2.1 :=
      mul_nonneg (mul_nonneg hu.le (by dsimp [y]; exact hy.2.1.le))
        (by dsimp [y]; exact hy.2.2.1.le)
    have hb := hp.2.2.2.2.1 (s * x.1 * x.2.1) (u * y.1 * y.2.1) hq hq'
    have hd := thm_app_vol_closed_kernel_i γstar CSig Fp.C Fp.hB hS
      Fp.hβ.1 Fp.hβ.2 ℓ hg s u hs hu
    have hμ0 := μ_nonneg S i
    have hl0 := lam_nonneg S j
    have hd1 : 0 < s + x.2.2.1 * S.μ i :=
      add_pos_of_pos_of_nonneg hs (mul_nonneg (by dsimp [x]; exact hx.2.2.2.1.le) hμ0)
    have hd2 : 0 < u + y.2.2.1 * S.μ i :=
      add_pos_of_pos_of_nonneg hu (mul_nonneg (by dsimp [y]; exact hy.2.2.2.1.le) hμ0)
    have hd3 : 0 < s + x.2.2.2 * S.lam j :=
      add_pos_of_pos_of_nonneg hs (mul_nonneg (by dsimp [x]; exact hx.2.2.2.2.le) hl0)
    have hd4 : 0 < u + y.2.2.2 * S.lam j :=
      add_pos_of_pos_of_nonneg hu (mul_nonneg (by dsimp [y]; exact hy.2.2.2.2.le) hl0)
    have htheta : 0 < thetaSigma Fp.C B (min s u) ^ 2 := by
      unfold thetaSigma
      have hk : 0 ≤ kappaSigma Fp.C B := by
        unfold kappaSigma
        exact le_max_of_le_left (mul_nonneg
          (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) Fp.C.psdIn.trace_nonneg)
          (by unfold Muon.opNorm; exact norm_nonneg _))
      have hm : 0 < min s u := lt_min hs hu
      positivity
    have hden : (s * u) ^ 2 * thetaSigma Fp.C B (min s u) ^ 2 ≤
        (s + x.2.2.1 * S.μ i) * (u + y.2.2.1 * S.μ i) *
          (s + x.2.2.2 * S.lam j) * (u + y.2.2.2 * S.lam j) *
            profileDelta P Fp.C B (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g) s u := by
      have h1 : s ≤ s + x.2.2.1 * S.μ i := le_add_of_nonneg_right
        (mul_nonneg (by dsimp [x]; exact hx.2.2.2.1.le) hμ0)
      have h2 : u ≤ u + y.2.2.1 * S.μ i := le_add_of_nonneg_right
        (mul_nonneg (by dsimp [y]; exact hy.2.2.2.1.le) hμ0)
      have h3 : s ≤ s + x.2.2.2 * S.lam j := le_add_of_nonneg_right
        (mul_nonneg (by dsimp [x]; exact hx.2.2.2.2.le) hl0)
      have h4 : u ≤ u + y.2.2.2 * S.lam j := le_add_of_nonneg_right
        (mul_nonneg (by dsimp [y]; exact hy.2.2.2.2.le) hl0)
      calc
        (s * u) ^ 2 * thetaSigma Fp.C B (min s u) ^ 2 =
            s * u * s * u * thetaSigma Fp.C B (min s u) ^ 2 := by ring
        _ ≤ (s + x.2.2.1 * S.μ i) * (u + y.2.2.1 * S.μ i) *
            (s + x.2.2.2 * S.lam j) * (u + y.2.2.2 * S.lam j) *
              profileDelta P Fp.C B (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g) s u := by
          gcongr
          exact hd.2.1 ⟨hout, hin⟩
    change 0 ≤ s * u * S.μ i * S.lam j *
        pairedB P (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g)
          (s * x.1 * x.2.1) (u * y.1 * y.2.1) /
        ((s + x.2.2.1 * S.μ i) * (u + y.2.2.1 * S.μ i) *
          (s + x.2.2.2 * S.lam j) * (u + y.2.2.2 * S.lam j) *
            profileDelta P Fp.C B (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g) s u) ∧ _
    constructor
    · exact div_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hs.le hu.le) hμ0) hl0) hb.1)
        (mul_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg hd1.le hd2.le) hd3.le) hd4.le) hd.1.le)
    · have hnum : s * u * S.μ i * S.lam j *
          pairedB P (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g)
            (s * x.1 * x.2.1) (u * y.1 * y.2.1) ≤
          s * u * S.μ i * S.lam j * (Muon.sPow Fp.β 2 * Fp.β ^ ℓ) := by
        gcongr
        exact hb.2
      have hsp : 0 ≤ Muon.sPow Fp.β 2 := by
        unfold Muon.sPow
        exact tsum_nonneg fun k => sq_nonneg _
      have hpow : 0 ≤ Fp.β ^ ℓ := pow_nonneg Fp.hβ.1 ℓ
      calc
        _ ≤ (s * u * S.μ i * S.lam j * (Muon.sPow Fp.β 2 * Fp.β ^ ℓ)) /
            ((s * u) ^ 2 * thetaSigma Fp.C B (min s u) ^ 2) :=
          div_le_div₀
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hs.le hu.le) hμ0) hl0)
              (mul_nonneg hsp hpow))
            hnum (mul_pos (sq_pos_of_pos (mul_pos hs hu)) htheta) hden
        _ = _ := by
          field_simp [hs.ne', hu.ne', ne_of_gt htheta]

private lemma closed_modes_scalar_difference {x y q : ℝ}
    (hy : 0 ≤ y) (hyx : y ≤ x) (hq : 0 ≤ q) :
    0 ≤ x / (1 + q * x) - y / (1 + q * y) ∧
      x / (1 + q * x) - y / (1 + q * y) ≤ x - y := by
  have hx : 0 ≤ x := hy.trans hyx
  have hd1 : 0 < 1 + q * x := by positivity
  have hd2 : 0 < 1 + q * y := by positivity
  have he : x / (1 + q * x) - y / (1 + q * y) =
      (x - y) / ((1 + q * x) * (1 + q * y)) := by
    field_simp
    <;> ring
  rw [he]
  refine ⟨div_nonneg (sub_nonneg.mpr hyx) (mul_pos hd1 hd2).le,
    div_le_self (sub_nonneg.mpr hyx) ?_⟩
  have h1 : 1 ≤ 1 + q * x := le_add_of_nonneg_right (mul_nonneg hq hx)
  have h2 : 1 ≤ 1 + q * y := le_add_of_nonneg_right (mul_nonneg hq hy)
  nlinarith

private lemma closed_modes_profile_terms {Ω ι : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {ξ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ)
    {q : ℝ} (hq : 0 ≤ q) :
    (∀ a, Integrable (fun ω => ξ a ω ^ 2 / (1 + q * ξ a ω ^ 2)) P) ∧
      Summable (fun a => ∫ ω, ξ a ω ^ 2 / (1 + q * ξ a ω ^ 2) ∂P) := by
  have hb : ∀ a ω, ‖ξ a ω ^ 2 / (1 + q * ξ a ω ^ 2)‖ ≤ ξ a ω ^ 2 := by
    intro a ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_self (sq_nonneg _) (le_add_of_nonneg_right (mul_nonneg hq (sq_nonneg _)))
  constructor
  · intro a
    exact (hξ.integrable_sq a).mono'
      (((hξ.measurable a).pow_const 2).div
        (measurable_const.add (measurable_const.mul ((hξ.measurable a).pow_const 2)))).aestronglyMeasurable
      (ae_of_all _ (hb a))
  · exact hξ.summable_sq.of_norm_bounded fun a =>
      norm_integral_le_of_norm_le (hξ.integrable_sq a) (ae_of_all _ (hb a))

private lemma closed_modes_profile_error {Ω ι : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {ξ η : ι → Ω → ℝ}
    (hξ : def_app_vol_closed_profile P ξ) (hη : def_app_vol_closed_profile P η)
    (hle : ∀ a ω, η a ω ^ 2 ≤ ξ a ω ^ 2) {q : ℝ} (hq : 0 ≤ q) :
    |profileF P η q - profileF P ξ q| ≤
      (∑' a, ∫ ω, ξ a ω ^ 2 ∂P) - ∑' a, ∫ ω, η a ω ^ 2 ∂P := by
  have htξ := closed_modes_profile_terms hξ hq
  have htη := closed_modes_profile_terms hη hq
  have hterm : ∀ a,
      0 ≤ (∫ ω, ξ a ω ^ 2 / (1 + q * ξ a ω ^ 2) ∂P) -
        ∫ ω, η a ω ^ 2 / (1 + q * η a ω ^ 2) ∂P := by
    intro a
    rw [← integral_sub (htξ.1 a) (htη.1 a)]
    exact integral_nonneg fun ω => (closed_modes_scalar_difference (sq_nonneg _) (hle a ω) hq).1
  have hnonneg : 0 ≤ profileF P ξ q - profileF P η q := by
    unfold profileF
    rw [← htξ.2.tsum_sub htη.2]
    exact tsum_nonneg hterm
  rw [abs_sub_comm, abs_of_nonneg hnonneg]
  unfold profileF
  rw [← htξ.2.tsum_sub htη.2, ← hξ.summable_sq.tsum_sub hη.summable_sq]
  apply (htξ.2.sub htη.2).tsum_le_tsum _ (hξ.summable_sq.sub hη.summable_sq)
  intro a
  rw [← integral_sub (htξ.1 a) (htη.1 a),
    ← integral_sub (hξ.integrable_sq a) (hη.integrable_sq a)]
  exact integral_mono ((htξ.1 a).sub (htη.1 a))
    ((hξ.integrable_sq a).sub (hη.integrable_sq a))
    (fun ω => (closed_modes_scalar_difference (sq_nonneg _) (hle a ω) hq).2)

private lemma closed_modes_profile_uniform {Ω ι : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {ξ : ι → Ω → ℝ} {ξn : ℕ → ι → Ω → ℝ}
    (hξ : def_app_vol_closed_profile P ξ) (hξn : ∀ k, def_app_vol_closed_profile P (ξn k))
    (hle : ∀ k a ω, ξn k a ω ^ 2 ≤ ξ a ω ^ 2)
    (hlim : ∀ a, ∀ᵐ ω ∂P, Tendsto (fun k => ξn k a ω) atTop (𝓝 (ξ a ω))) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ q ∈ Ici (0 : ℝ),
      |profileF P (ξn k) q - profileF P ξ q| ≤ ε := by
  have hterm : ∀ a, Tendsto (fun k => ∫ ω, ξn k a ω ^ 2 ∂P) atTop
      (𝓝 (∫ ω, ξ a ω ^ 2 ∂P)) := by
    intro a
    apply tendsto_integral_of_dominated_convergence (fun ω => ξ a ω ^ 2)
      (fun k => ((hξn k).measurable a).pow_const 2 |>.aestronglyMeasurable)
      (hξ.integrable_sq a)
    · intro k
      exact ae_of_all _ fun ω => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (ξn k a ω))] using hle k a ω
    · filter_upwards [hlim a] with ω hω
      exact hω.pow 2
  have hsum : Tendsto (fun k => ∑' a, ∫ ω, ξn k a ω ^ 2 ∂P) atTop
      (𝓝 (∑' a, ∫ ω, ξ a ω ^ 2 ∂P)) := by
    apply tendsto_tsum_of_dominated_convergence hξ.summable_sq hterm
    exact Filter.Eventually.of_forall fun k a =>
      norm_integral_le_of_norm_le (hξ.integrable_sq a) (ae_of_all _ fun ω => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (ξn k a ω))] using hle k a ω)
  have hdiff : Tendsto (fun k => (∑' a, ∫ ω, ξ a ω ^ 2 ∂P) -
      ∑' a, ∫ ω, ξn k a ω ^ 2 ∂P) atTop (𝓝 0) := by
    have H : Tendsto (fun k => (∑' a, ∫ ω, ξ a ω ^ 2 ∂P) -
        ∑' a, ∫ ω, ξn k a ω ^ 2 ∂P) atTop
        (𝓝 ((∑' a, ∫ ω, ξ a ω ^ 2 ∂P) - (∑' a, ∫ ω, ξ a ω ^ 2 ∂P))) :=
      tendsto_const_nhds.sub hsum
    simpa only [sub_self] using H
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hdiff.eventually_lt_const hε)
  exact ⟨N, fun k hk q hq =>
    (closed_modes_profile_error hξ (hξn k) (hle k) hq).trans (hN k hk).le⟩

private lemma closed_modes_tsum_integral_limit {Ω ι : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {f : ℕ → ι → Ω → ℝ} {f₀ bound : ι → Ω → ℝ}
    (hf : ∀ k a, AEStronglyMeasurable (f k a) P)
    (hb : ∀ a, Integrable (bound a) P)
    (hsum : Summable (fun a => ∫ ω, bound a ω ∂P))
    (hle : ∀ k a, ∀ᵐ ω ∂P, ‖f k a ω‖ ≤ bound a ω)
    (hlim : ∀ a, ∀ᵐ ω ∂P, Tendsto (fun k => f k a ω) atTop (𝓝 (f₀ a ω))) :
    Tendsto (fun k => ∑' a, ∫ ω, f k a ω ∂P) atTop (𝓝 (∑' a, ∫ ω, f₀ a ω ∂P)) := by
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro a
    exact tendsto_integral_of_dominated_convergence (bound a)
      (fun k => hf k a) (hb a) (fun k => hle k a) (hlim a)
  · exact Filter.Eventually.of_forall fun k a => norm_integral_le_of_norm_le (hb a) (hle k a)

private lemma closed_modes_paired_limit {Ω ι : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {ξ₁ ξ₂ : ι → Ω → ℝ} {ξn₁ ξn₂ : ℕ → ι → Ω → ℝ}
    (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂)
    (hξn : ∀ k, def_app_vol_closed_profile_ii P (ξn₁ k) (ξn₂ k))
    (hle₁ : ∀ k a ω, ξn₁ k a ω ^ 2 ≤ ξ₁ a ω ^ 2)
    (hle₂ : ∀ k a ω, ξn₂ k a ω ^ 2 ≤ ξ₂ a ω ^ 2)
    (hlim₁ : ∀ a, ∀ᵐ ω ∂P, Tendsto (fun k => ξn₁ k a ω) atTop (𝓝 (ξ₁ a ω)))
    (hlim₂ : ∀ a, ∀ᵐ ω ∂P, Tendsto (fun k => ξn₂ k a ω) atTop (𝓝 (ξ₂ a ω)))
    {q₁ q₂ : ℕ → ℝ} {q₁₀ q₂₀ : ℝ} (hq₁ : ∀ k, 0 ≤ q₁ k) (hq₂ : ∀ k, 0 ≤ q₂ k)
    (hq₁₀ : 0 ≤ q₁₀) (hq₂₀ : 0 ≤ q₂₀)
    (hq₁lim : Tendsto q₁ atTop (𝓝 q₁₀)) (hq₂lim : Tendsto q₂ atTop (𝓝 q₂₀)) :
    Tendsto (fun k => pairedB P (ξn₁ k) (ξn₂ k) (q₁ k) (q₂ k)) atTop
        (𝓝 (pairedB P ξ₁ ξ₂ q₁₀ q₂₀)) ∧
      Tendsto (fun k => pairedE P (ξn₁ k) (ξn₂ k) (q₁ k) (q₂ k)) atTop
        (𝓝 (pairedE P ξ₁ ξ₂ q₁₀ q₂₀)) := by
  have hden : ∀ k a ω, 1 ≤
      (1 + q₁ k * ξn₁ k a ω ^ 2) * (1 + q₂ k * ξn₂ k a ω ^ 2) := by
    intro k a ω
    have h1 := mul_nonneg (hq₁ k) (sq_nonneg (ξn₁ k a ω))
    have h2 := mul_nonneg (hq₂ k) (sq_nonneg (ξn₂ k a ω))
    nlinarith [mul_nonneg h1 h2]
  have hmeas : ∀ (d k : ℕ) a, AEStronglyMeasurable (fun ω =>
      ξn₁ k a ω ^ d * ξn₂ k a ω ^ d /
        ((1 + q₁ k * ξn₁ k a ω ^ 2) * (1 + q₂ k * ξn₂ k a ω ^ 2))) P := by
    intro d k a
    have h1 := (hξn k).profile₁.measurable a
    have h2 := (hξn k).profile₂.measurable a
    exact (((h1.pow_const d).mul (h2.pow_const d)).div
      ((measurable_const.add (measurable_const.mul (h1.pow_const 2))).mul
        (measurable_const.add (measurable_const.mul (h2.pow_const 2))))).aestronglyMeasurable
  have hterm : ∀ (d : ℕ) a, ∀ᵐ ω ∂P, Tendsto (fun k =>
      ξn₁ k a ω ^ d * ξn₂ k a ω ^ d /
        ((1 + q₁ k * ξn₁ k a ω ^ 2) * (1 + q₂ k * ξn₂ k a ω ^ 2))) atTop
      (𝓝 (ξ₁ a ω ^ d * ξ₂ a ω ^ d /
        ((1 + q₁₀ * ξ₁ a ω ^ 2) * (1 + q₂₀ * ξ₂ a ω ^ 2)))) := by
    intro d a
    filter_upwards [hlim₁ a, hlim₂ a] with ω h1 h2
    exact ((h1.pow d).mul (h2.pow d)).div
      ((tendsto_const_nhds.add (hq₁lim.mul (h1.pow 2))).mul
        (tendsto_const_nhds.add (hq₂lim.mul (h2.pow 2)))) (by positivity)
  constructor
  · have hb : ∀ a, Integrable (fun ω => (ξ₁ a ω ^ 2 + ξ₂ a ω ^ 2) / 2) P :=
      fun a => ((hξ.profile₁.integrable_sq a).add (hξ.profile₂.integrable_sq a)).div_const 2
    have hsum : Summable (fun a => ∫ ω, (ξ₁ a ω ^ 2 + ξ₂ a ω ^ 2) / 2 ∂P) := by
      simp_rw [integral_div, integral_add (hξ.profile₁.integrable_sq _) (hξ.profile₂.integrable_sq _)]
      exact (hξ.profile₁.summable_sq.add hξ.profile₂.summable_sq).div_const 2
    have hbd : ∀ k a, ∀ᵐ ω ∂P, ‖ξn₁ k a ω ^ 1 * ξn₂ k a ω ^ 1 /
        ((1 + q₁ k * ξn₁ k a ω ^ 2) * (1 + q₂ k * ξn₂ k a ω ^ 2))‖ ≤
        (ξ₁ a ω ^ 2 + ξ₂ a ω ^ 2) / 2 := by
      intro k a
      apply ae_of_all
      intro ω
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one (hden k a ω))]
      refine (div_le_self (abs_nonneg _) (hden k a ω)).trans ?_
      rw [pow_one, pow_one, abs_of_nonneg ((hξn k).nonneg_prod a ω)]
      nlinarith [sq_nonneg (ξn₁ k a ω - ξn₂ k a ω), hle₁ k a ω, hle₂ k a ω]
    simpa only [pairedB, pow_one] using
      closed_modes_tsum_integral_limit (hmeas 1) hb hsum hbd (hterm 1)
  · have hbd : ∀ k a, ∀ᵐ ω ∂P, ‖ξn₁ k a ω ^ 2 * ξn₂ k a ω ^ 2 /
        ((1 + q₁ k * ξn₁ k a ω ^ 2) * (1 + q₂ k * ξn₂ k a ω ^ 2))‖ ≤
        ξ₁ a ω ^ 2 * ξ₂ a ω ^ 2 := by
      intro k a
      apply ae_of_all
      intro ω
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one (hden k a ω)),
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact (div_le_self (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hden k a ω)).trans
        (mul_le_mul (hle₁ k a ω) (hle₂ k a ω) (sq_nonneg _) (sq_nonneg _))
    exact closed_modes_tsum_integral_limit (hmeas 2) hξ.integrable_sq_prod
      hξ.summable_sq_prod hbd (hterm 2)

private lemma closed_modes_resolvent_limit {d : ℕ} {A : Mat d d} (hA : A.PosSemidef)
    {s a₀ : ℝ} (hs : 0 < s) (ha₀ : 0 ≤ a₀) {a : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (fun k => (s • (1 : Mat d d) + a k • A)⁻¹) atTop
      (𝓝 ((s • (1 : Mat d d) + a₀ • A)⁻¹)) := by
  have hd : (s • (1 : Mat d d) + a₀ • A).det ≠ 0 :=
    ne_of_gt (((Matrix.PosDef.one.smul hs).add_posSemidef (hA.smul ha₀)).det_pos)
  apply (continuousAt_matrix_inv _ (by
    rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv]
    exact continuousAt_inv₀ hd)).tendsto.comp
  exact tendsto_const_nhds.add (ha.smul tendsto_const_nhds)

private lemma closed_modes_trace_limit {d : ℕ} {A : Mat d d} (hA : A.PosSemidef)
    (F : Mat d d) (B : ℕ) {s u a₀ c₀ : ℝ}
    (hs : 0 < s) (hu : 0 < u) (ha₀ : 0 ≤ a₀) (hc₀ : 0 ≤ c₀)
    {a c : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 a₀)) (hc : Tendsto c atTop (𝓝 c₀)) :
    Tendsto (fun k => (B : ℝ)⁻¹ *
      (F * A * (s • (1 : Mat d d) + a k • A)⁻¹ * (u • (1 : Mat d d) + c k • A)⁻¹).trace)
      atTop (𝓝 ((B : ℝ)⁻¹ *
        (F * A * (s • (1 : Mat d d) + a₀ • A)⁻¹ * (u • (1 : Mat d d) + c₀ • A)⁻¹).trace)) := by
  apply Tendsto.const_mul
  apply (continuous_id.matrix_trace.tendsto _).comp
  exact (tendsto_const_nhds.mul (closed_modes_resolvent_limit hA hs ha₀ ha)).mul
    (closed_modes_resolvent_limit hA hu hc₀ hc)

private lemma closed_modes_profileKernel_limit {Ω ι : Type} [MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (C : Muon.Covariances m n)
    (hB : 0 < B) (hout : C.Sout ≠ 0) (hin : C.Sin ≠ 0)
    (γ : ℝ) (hγ : (max m n : ℝ) ≤ γ * B)
    {ξ₁ ξ₂ : ι → Ω → ℝ} {ξn₁ ξn₂ : ℕ → ι → Ω → ℝ}
    (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂)
    (hξn : ∀ k, def_app_vol_closed_profile_ii P (ξn₁ k) (ξn₂ k))
    (hle₁ : ∀ k a ω, ξn₁ k a ω ^ 2 ≤ ξ₁ a ω ^ 2)
    (hle₂ : ∀ k a ω, ξn₂ k a ω ^ 2 ≤ ξ₂ a ω ^ 2)
    (hlim₁ : ∀ a, ∀ᵐ ω ∂P, Tendsto (fun k => ξn₁ k a ω) atTop (𝓝 (ξ₁ a ω)))
    (hlim₂ : ∀ a, ∀ᵐ ω ∂P, Tendsto (fun k => ξn₂ k a ω) atTop (𝓝 (ξ₂ a ω)))
    (Fm : Mat m m) (Gm : Mat n n) (s u : ℝ) (hs : 0 < s) (hu : 0 < u)
    (hd : profileDelta P C B ξ₁ ξ₂ s u ≠ 0) :
    Tendsto (fun k => profileKernel P C B (ξn₁ k) (ξn₂ k) Fm Gm s u) atTop
      (𝓝 (profileKernel P C B ξ₁ ξ₂ Fm Gm s u)) := by
  have hbdd {ξ : ι → Ω → ℝ} {ξn : ℕ → ι → Ω → ℝ}
      (h : def_app_vol_closed_profile P ξ) (hn : ∀ k, def_app_vol_closed_profile P (ξn k))
      (hle : ∀ k a ω, ξn k a ω ^ 2 ≤ ξ a ω ^ 2) :
      BddAbove (Set.range fun k => profileF P (ξn k) 0) := by
    refine ⟨profileF P ξ 0, ?_⟩
    rintro _ ⟨k, rfl⟩
    simp only [profileF, zero_mul, add_zero, div_one]
    exact (hn k).summable_sq.tsum_le_tsum
      (fun a => integral_mono ((hn k).integrable_sq a) (h.integrable_sq a) (hle k a)) h.summable_sq
  have hx := lem_app_vol_closed_branch_iv hB hξ.profile₁ C (fun k => (hξn k).profile₁)
    (closed_modes_profile_uniform hξ.profile₁ (fun k => (hξn k).profile₁) hle₁ hlim₁)
    (hbdd hξ.profile₁ (fun k => (hξn k).profile₁) hle₁) s hs
  have hy := lem_app_vol_closed_branch_iv hB hξ.profile₂ C (fun k => (hξn k).profile₂)
    (closed_modes_profile_uniform hξ.profile₂ (fun k => (hξn k).profile₂) hle₂ hlim₂)
    (hbdd hξ.profile₂ (fun k => (hξn k).profile₂) hle₂) u hu
  have hxs := closed_branch_spec hB hξ.profile₁ C hout hin γ hγ hs
  have hys := closed_branch_spec hB hξ.profile₂ C hout hin γ hγ hu
  have hxns := fun k => closed_branch_spec hB (hξn k).profile₁ C hout hin γ hγ hs
  have hyns := fun k => closed_branch_spec hB (hξn k).profile₂ C hout hin γ hγ hu
  have hp := closed_modes_paired_limit hξ hξn hle₁ hle₂ hlim₁ hlim₂
    (fun k => (mul_pos (mul_pos hs (hxns k).2.1) (hxns k).2.2.1).le)
    (fun k => (mul_pos (mul_pos hu (hyns k).2.1) (hyns k).2.2.1).le)
    (mul_pos (mul_pos hs hxs.2.1) hxs.2.2.1).le
    (mul_pos (mul_pos hu hys.2.1) hys.2.2.1).le
    ((hx.fst_nhds.const_mul s).mul hx.snd_nhds.fst_nhds) ((hy.fst_nhds.const_mul u).mul hy.snd_nhds.fst_nhds)
  have hTo := fun F => closed_modes_trace_limit C.psdOut F B hs hu
    hxs.2.2.2.1.le hys.2.2.2.1.le hx.snd_nhds.snd_nhds.fst_nhds hy.snd_nhds.snd_nhds.fst_nhds
  have hTi := fun G => closed_modes_trace_limit C.psdIn G B hs hu
    hxs.2.2.2.2.le hys.2.2.2.2.le hx.snd_nhds.snd_nhds.snd_nhds hy.snd_nhds.snd_nhds.snd_nhds
  have hD : Tendsto (fun k => profileDelta P C B (ξn₁ k) (ξn₂ k) s u) atTop
      (𝓝 (profileDelta P C B ξ₁ ξ₂ s u)) := by
    exact ((tendsto_const_nhds.sub
      (((((hTo C.Sout).const_mul (s * u)).mul hx.snd_nhds.fst_nhds).mul hy.snd_nhds.fst_nhds).mul hp.2)).mul
      (tendsto_const_nhds.sub
        (((((hTi C.Sin).const_mul (s * u)).mul hx.fst_nhds).mul hy.fst_nhds).mul hp.2))).sub
      ((((hTo C.Sout).const_mul (s * u)).mul (hTi C.Sin)).mul (hp.1.pow 2))
  exact ((((hp.1.const_mul (s * u)).mul (hTo Fm)).mul (hTi Gm)).div hD hd)

private lemma closed_modes_profile_reindex {Ω ι κ : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {ξ : κ → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ)
    {e : ι → κ} (he : Function.Injective e)
    (hz : ∀ a, a ∉ Set.range e → ξ a = 0) :
    def_app_vol_closed_profile P (fun a => ξ (e a)) ∧
      profileF P (fun a => ξ (e a)) = profileF P ξ := by
  constructor
  · refine ⟨fun a => hξ.measurable (e a), fun a => hξ.integrable_sq (e a),
      hξ.summable_sq.comp_injective he, ?_⟩
    obtain ⟨a, ha⟩ := hξ.exists_ne_zero
    by_cases hmem : a ∈ Set.range e
    · obtain ⟨b, rfl⟩ := hmem
      exact ⟨b, ha⟩
    · rw [hz a hmem] at ha
      simp at ha
  · funext q
    unfold profileF
    apply he.tsum_eq (f := fun a => ∫ ω, ξ a ω ^ 2 / (1 + q * ξ a ω ^ 2) ∂P)
    intro a ha
    by_contra hmem
    apply ha
    simp [hz a hmem]

private lemma closed_modes_pair_reindex {Ω ι κ : Type} [MeasurableSpace Ω]
    [Countable ι] [Countable κ] {P : Measure Ω}
    {ξ₁ ξ₂ : κ → Ω → ℝ} (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂)
    {e : ι → κ} (he : Function.Injective e)
    (hz₁ : ∀ a, a ∉ Set.range e → ξ₁ a = 0)
    (hz₂ : ∀ a, a ∉ Set.range e → ξ₂ a = 0) :
    def_app_vol_closed_profile_ii P (fun a => ξ₁ (e a)) (fun a => ξ₂ (e a)) ∧
      ∀ {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ) (Fm : Mat m m) (Gm : Mat n n) (s u : ℝ),
        profileKernel P C B (fun a => ξ₁ (e a)) (fun a => ξ₂ (e a)) Fm Gm s u =
          profileKernel P C B ξ₁ ξ₂ Fm Gm s u := by
  have h1 := closed_modes_profile_reindex hξ.profile₁ he hz₁
  have h2 := closed_modes_profile_reindex hξ.profile₂ he hz₂
  refine ⟨⟨h1.1, h2.1, fun a => hξ.nonneg_prod (e a),
    fun a => hξ.integrable_sq_prod (e a), hξ.summable_sq_prod.comp_injective he⟩, ?_⟩
  have hb : pairedB P (fun a => ξ₁ (e a)) (fun a => ξ₂ (e a)) = pairedB P ξ₁ ξ₂ := by
    funext q q'
    unfold pairedB
    apply he.tsum_eq (f := fun a => ∫ ω, ξ₁ a ω * ξ₂ a ω /
      ((1 + q * ξ₁ a ω ^ 2) * (1 + q' * ξ₂ a ω ^ 2)) ∂P)
    intro a ha
    by_contra hmem
    apply ha
    simp [hz₁ a hmem]
  have hE : pairedE P (fun a => ξ₁ (e a)) (fun a => ξ₂ (e a)) = pairedE P ξ₁ ξ₂ := by
    funext q q'
    unfold pairedE
    apply he.tsum_eq (f := fun a => ∫ ω, ξ₁ a ω ^ 2 * ξ₂ a ω ^ 2 /
      ((1 + q * ξ₁ a ω ^ 2) * (1 + q' * ξ₂ a ω ^ 2)) ∂P)
    intro a ha
    by_contra hmem
    apply ha
    simp [hz₁ a hmem]
  intro m n C B Fm Gm s u
  simp only [profileKernel, profileDelta, h1.2, h2.2, hb, hE]

private lemma closed_modes_cutoff_embedding (ℓ : ℕ) :
    ∃ e : ℕ ⊕ Fin ℓ → ℤ, Function.Injective e ∧
      (∀ j, e (Sum.inl j) = -(j : ℤ)) ∧
      (∀ i : Fin ℓ, e (Sum.inr i) = ((i.val + 1 : ℕ) : ℤ)) ∧
      (∀ a, e a ≤ ℓ) ∧ ∀ z : ℤ, z ≤ ℓ → z ∈ Set.range e := by
  let e : ℕ ⊕ Fin ℓ → ℤ := fun a => match a with
    | Sum.inl j => -(j : ℤ)
    | Sum.inr i => ((i.val + 1 : ℕ) : ℤ)
  refine ⟨e, ?_, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro a b hab
    cases a with
    | inl j =>
      cases b with
      | inl k =>
        have : j = k := by simpa only [e, neg_inj, Int.natCast_inj] using hab
        simp [this]
      | inr i => simp only [e] at hab; omega
    | inr i =>
      cases b with
      | inl j => simp only [e] at hab; omega
      | inr j =>
        have : i.val = j.val := by simp only [e] at hab; omega
        exact congrArg Sum.inr (Fin.ext this)
  · intro a
    cases a with
    | inl j => dsimp [e]; omega
    | inr i => dsimp [e]; have := i.isLt; omega
  · intro z hz
    by_cases hz0 : z ≤ 0
    · refine ⟨Sum.inl (-z).toNat, ?_⟩
      dsimp [e]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    · refine ⟨Sum.inr ⟨z.toNat - 1, by omega⟩, ?_⟩
      dsimp [e]
      omega

private lemma closed_modes_cutoff_to_ema (γstar CSig : ℝ) {m n B : ℕ}
    (Fp : FrozenParams m n B) (hS : SizeFin Fp.C B γstar CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ℓ : ℕ) {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (e : ℕ ⊕ Fin ℓ → ℤ) (he : Function.Injective e)
    (he1 : ∀ j, e (Sum.inl j) = -(j : ℤ))
    (he2 : ∀ i : Fin ℓ, e (Sum.inr i) = ((i.val + 1 : ℕ) : ℤ))
    (hele : ∀ a, e a ≤ ℓ) (herange : ∀ z : ℤ, z ≤ ℓ → z ∈ Set.range e)
    (Fm : Mat m m) (Gm : Mat n n) (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    IsStdGaussianFamily P (fun a => g (e a)) ∧
      Tendsto (fun k : ℕ => profileKernel P Fp.C B
        (cutoffXi Fp.β ℓ k ((k : ℝ) + 1) 1 g) (cutoffXi Fp.β ℓ k ((k : ℝ) + 1) 2 g)
        Fm Gm s u) atTop
        (𝓝 (profileKernel P Fp.C B (emaXi₁ Fp.β ℓ (fun a => g (e a)))
          (emaXi₂ Fp.β ℓ (fun a => g (e a))) Fm Gm s u)) := by
  have hg' : IsStdGaussianFamily P (fun a => g (e a)) :=
    ⟨fun a => hg.1 (e a), hg.2.1.precomp he, fun a => hg.2.2 (e a)⟩
  refine ⟨hg', ?_⟩
  have hz : ∀ (k r : ℕ) a, a ∉ Set.range e →
      cutoffXi Fp.β ℓ k ((k : ℝ) + 1) r g a = 0 := by
    intro k r a ha
    have hmem : a ∉ cutoffLabels k ℓ := by
      intro hm
      apply ha
      apply herange
      simp only [cutoffLabels, Finset.mem_union, Finset.mem_Icc] at hm
      omega
    funext ω
    simp [cutoffXi, cutoffVarpi, hmem]
  have hcut := fun (k : ℕ) => closed_modes_pair_reindex
    (lem_app_vol_closed_cutoff_paired Fp.hβ.1 Fp.hβ.2 (ℓ := ℓ) (J := k)
      (by positivity : 0 < (k : ℝ) + 1) hg)
    he (hz k 1) (hz k 2)
  have hw1 : ∀ a ω, treeVarpi Fp.β ℓ 1 (e a) * g (e a) ω =
      emaXi₁ Fp.β ℓ (fun a => g (e a)) a ω := by
    intro a ω
    cases a with
    | inl j => simp [he1, treeVarpi, emaXi₁]
    | inr i => simp [he2, treeVarpi, emaXi₁]
  have hw2 : ∀ a ω, treeVarpi Fp.β ℓ 2 (e a) * g (e a) ω =
      emaXi₂ Fp.β ℓ (fun a => g (e a)) a ω := by
    intro a ω
    cases a with
    | inl j => simp [he1, treeVarpi, emaXi₂]
    | inr i => simp [he2, treeVarpi, emaXi₂]
  have hle : ∀ (k r : ℕ) a ω,
      cutoffXi Fp.β ℓ k ((k : ℝ) + 1) r g (e a) ω ^ 2 ≤
        (treeVarpi Fp.β ℓ r (e a) * g (e a) ω) ^ 2 := by
    intro k r a ω
    by_cases hm : e a ∈ cutoffLabels k ℓ
    · by_cases hR : |g (e a) ω| ≤ (k : ℝ) + 1
      · simp [cutoffXi, cutoffVarpi, hm, hR]
      · simp [cutoffXi, cutoffVarpi, hm, hR, sq_nonneg]
    · simp [cutoffXi, cutoffVarpi, hm, sq_nonneg]
  have hlim : ∀ r a ω, Tendsto (fun k : ℕ =>
      cutoffXi Fp.β ℓ k ((k : ℝ) + 1) r g (e a) ω) atTop
      (𝓝 (treeVarpi Fp.β ℓ r (e a) * g (e a) ω)) := by
    intro r a ω
    apply tendsto_const_nhds.congr'
    filter_upwards
      [(tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℤ)) atTop atTop).eventually_ge_atTop (-e a),
       (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop).eventually_ge_atTop |g (e a) ω|]
      with k hk hR
    have hm : e a ∈ cutoffLabels k ℓ := by
      have := hele a
      simp only [cutoffLabels, Finset.mem_union, Finset.mem_Icc]
      omega
    have hR' : |g (e a) ω| ≤ (k : ℝ) + 1 := by linarith
    simp [cutoffXi, cutoffVarpi, hm, hR']
  have hp := lem_app_vol_closed_profile_iv Fp.hβ.1 Fp.hβ.2 hg'
  have H := closed_modes_profileKernel_limit Fp.C Fp.hB hout hin γstar
    (by simpa only [Nat.cast_max] using hS.1) hp.2.2.2.2.2 (fun k => (hcut k).1)
    (fun k a ω => by rw [← hw1 a ω]; exact hle k 1 a ω)
    (fun k a ω => by rw [← hw2 a ω]; exact hle k 2 a ω)
    (fun a => ae_of_all _ fun ω => by rw [← hw1 a ω]; exact hlim 1 a ω)
    (fun a => ae_of_all _ fun ω => by rw [← hw2 a ω]; exact hlim 2 a ω)
    Fm Gm s u hs hu
    (ne_of_gt (thm_app_vol_closed_kernel_i γstar CSig Fp.C Fp.hB hS
      Fp.hβ.1 Fp.hβ.2 ℓ hg' s u hs hu).1)
  exact H.congr' (Filter.Eventually.of_forall fun k => (hcut k).2 Fp.C B Fm Gm s u)

private lemma closed_modes_modeH_law (γstar CSig : ℝ) {m n B : ℕ}
    (Fp : FrozenParams m n B) (hS : SizeFin Fp.C B γstar CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ℓ : ℕ) {g : ℕ ⊕ Fin ℓ → Ω → ℝ} {g' : ℕ ⊕ Fin ℓ → Ω' → ℝ}
    (hg : IsStdGaussianFamily P g) (hg' : IsStdGaussianFamily Q g')
    (μ l s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    closedModeH Q Fp.C B Fp.β ℓ g' μ l s u = closedModeH P Fp.C B Fp.β ℓ g μ l s u := by
  have hp := lem_app_vol_closed_profile_iv Fp.hβ.1 Fp.hβ.2 hg
  have hp' := lem_app_vol_closed_profile_iv Fp.hβ.1 Fp.hβ.2 hg'
  let x := branchPt (Fw (Muon.emaW Fp.β)) Fp.C B s
  let y := branchPt (Fw (Muon.emaW Fp.β)) Fp.C B u
  let q := s * x.1 * x.2.1
  let q' := u * y.1 * y.2.1
  have hx := closed_branch_spec Fp.hB hp.2.2.2.2.2.profile₁ Fp.C hout hin γstar
    (by simpa only [Nat.cast_max] using hS.1) hs
  have hy := closed_branch_spec Fp.hB hp.2.2.2.2.2.profile₂ Fp.C hout hin γstar
    (by simpa only [Nat.cast_max] using hS.1) hu
  rw [hp.1] at hx
  rw [hp.2.1] at hy
  have hq : 0 ≤ q := (mul_pos (mul_pos hs hx.2.1) hx.2.2.1).le
  have hq' : 0 ≤ q' := (mul_pos (mul_pos hu hy.2.1) hy.2.2.1).le
  have hpair :
      pairedB Q (emaXi₁ Fp.β ℓ g') (emaXi₂ Fp.β ℓ g') q q' =
        pairedB P (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g) q q' ∧
      pairedE Q (emaXi₁ Fp.β ℓ g') (emaXi₂ Fp.β ℓ g') q q' =
        pairedE P (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g) q q' := by
    by_cases hqq : q = Fp.β ^ (2 * ℓ) * q'
    · have H := hp.2.2.2.1 q q' hq hq' hqq
      have H' := hp'.2.2.2.1 q q' hq hq' hqq
      exact ⟨H'.1.trans H.1.symm, H'.2.trans H.2.symm⟩
    · have H := hp.2.2.1 q q' hq hq' hqq
      have H' := hp'.2.2.1 q q' hq hq' hqq
      exact ⟨H'.1.trans H.1.symm, H'.2.trans H.2.symm⟩
  unfold closedModeH profileDelta
  simp only [hp.1, hp.2.1, hp'.1, hp'.2.1]
  rw [hpair.1, hpair.2]

private lemma closed_modes_class_sum {d : ℕ} (v : Fin d → ℝ) (μ : ℝ) (f : ℝ → ℝ) :
    ∑ i, classDiag v μ i * f (v i) =
      ((Finset.univ.filter fun i => v i = μ).card : ℝ) * f μ := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => v i = μ), f (v i) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : v i = μ <;> simp [classDiag, hi]
    _ = ∑ _i ∈ Finset.univ.filter (fun i => v i = μ), f μ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := by simp

private lemma closed_modes_trace_projection {d : ℕ}
    (A U : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ)
    (hU : Uᵀ * U = 1) (hA : A = U * Matrix.diagonal v * Uᵀ)
    (μ s a u c : ℝ) (hs : ∀ i, s + a * v i ≠ 0) (hu : ∀ i, u + c * v i ≠ 0) :
    ((U * Matrix.diagonal (classDiag v μ) * Uᵀ) * A *
      (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • A)⁻¹ *
      (u • (1 : Matrix (Fin d) (Fin d) ℝ) + c • A)⁻¹).trace =
        ((Finset.univ.filter fun i => v i = μ).card : ℝ) *
          (μ / ((s + a * μ) * (u + c * μ))) := by
  classical
  rw [closed_bounds_trace_two_resolvents A U v (classDiag v μ) hU hA _ rfl s a u c hs hu]
  simp only [mul_div_assoc]
  exact closed_modes_class_sum v μ (fun z => z / ((s + a * z) * (u + c * z)))

private lemma closed_modes_profile_projection (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ℓ : ℕ) {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (μ l : ℝ) (hμ : μ ∈ Set.range S.μ) (hl : l ∈ Set.range S.lam)
    (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    profileKernel P Fp.C B (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g)
      (S.uOut * Matrix.diagonal (classDiag S.μ μ) * S.uOutᵀ)
      (S.vIn * Matrix.diagonal (classDiag S.lam l) * S.vInᵀ) s u =
        ((((Finset.univ.filter fun k => S.μ k = μ).card : ℝ) *
          ((Finset.univ.filter fun k => S.lam k = l).card : ℝ)) / (B : ℝ) ^ 2) *
          closedModeH P Fp.C B Fp.β ℓ g μ l s u := by
  classical
  rcases hμ with ⟨i, rfl⟩
  rcases hl with ⟨j, rfl⟩
  by_cases hC : Fp.C.Sout = 0 ∨ Fp.C.Sin = 0
  · rw [closed_profileKernel_degenerate Fp.C P _ _ hC]
    rcases hC with hout | hin
    · have hi : S.μ i = 0 := closed_eigenvalues_zero Fp.C.Sout S.uOut S.μ S.huOut
        (fun k => eig_u S k) hout i
      simp [closedModeH, hi]
    · have hj : S.lam j = 0 := closed_eigenvalues_zero Fp.C.Sin S.vIn S.lam S.hvIn
        (fun k => eig_v S k) hin j
      simp [closedModeH, hj]
  · let x := branchPt (profileF P (emaXi₁ Fp.β ℓ g)) Fp.C B s
    let y := branchPt (profileF P (emaXi₂ Fp.β ℓ g)) Fp.C B u
    have hp := lem_app_vol_closed_profile_iv Fp.hβ.1 Fp.hβ.2 hg
    have hx := closed_branch_spec Fp.hB hp.2.2.2.2.2.profile₁ Fp.C
      (fun h => hC (Or.inl h)) (fun h => hC (Or.inr h)) γstar
      (by simpa only [Nat.cast_max] using hS.1) hs
    have hy := closed_branch_spec Fp.hB hp.2.2.2.2.2.profile₂ Fp.C
      (fun h => hC (Or.inl h)) (fun h => hC (Or.inr h)) γstar
      (by simpa only [Nat.cast_max] using hS.1) hu
    have hso : ∀ k, s + x.2.2.1 * S.μ k ≠ 0 := fun k => ne_of_gt
      (add_pos_of_pos_of_nonneg hs (mul_nonneg hx.2.2.2.1.le (μ_nonneg S k)))
    have huo : ∀ k, u + y.2.2.1 * S.μ k ≠ 0 := fun k => ne_of_gt
      (add_pos_of_pos_of_nonneg hu (mul_nonneg hy.2.2.2.1.le (μ_nonneg S k)))
    have hsi : ∀ k, s + x.2.2.2 * S.lam k ≠ 0 := fun k => ne_of_gt
      (add_pos_of_pos_of_nonneg hs (mul_nonneg hx.2.2.2.2.le (lam_nonneg S k)))
    have hui : ∀ k, u + y.2.2.2 * S.lam k ≠ 0 := fun k => ne_of_gt
      (add_pos_of_pos_of_nonneg hu (mul_nonneg hy.2.2.2.2.le (lam_nonneg S k)))
    have hto := closed_modes_trace_projection Fp.C.Sout S.uOut S.μ S.huOut
      (Sout_eq_spectral S) (S.μ i) s x.2.2.1 u y.2.2.1 hso huo
    have hti := closed_modes_trace_projection Fp.C.Sin S.vIn S.lam S.hvIn
      (Sin_eq_spectral S) (S.lam j) s x.2.2.2 u y.2.2.2 hsi hui
    change s * u * pairedB P (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g)
        (s * x.1 * x.2.1) (u * y.1 * y.2.1) *
        toutT Fp.C B x y s u (S.uOut * Matrix.diagonal (classDiag S.μ (S.μ i)) * S.uOutᵀ) *
        tinT Fp.C B x y s u (S.vIn * Matrix.diagonal (classDiag S.lam (S.lam j)) * S.vInᵀ) /
          profileDelta P Fp.C B (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g) s u = _
    unfold toutT tinT
    rw [hto, hti]
    dsimp [closedModeH, x, y]
    simp only [div_eq_mul_inv, mul_inv, pow_two]
    ring

private lemma closed_modes_filtered_of_pointwise (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (μ l : ℝ)
    (hμ : μ ∈ Set.range S.μ) (hl : l ∈ Set.range S.lam)
    (hpoint : ∀ s u : ℝ, 0 < s → 0 < u →
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (classDiag S.μ μ) (classDiag S.lam l)
        (iotaF s) (iotaF u) =
        ((((Finset.univ.filter fun k => S.μ k = μ).card : ℝ) *
          ((Finset.univ.filter fun k => S.lam k = l).card : ℝ)) / (B : ℝ) ^ 2) *
          closedModeH P Fp.C B Fp.β ℓ g μ l s u)
    (ϱ : ℝ) (hϱ : 0 < ϱ) :
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (classDiag S.μ μ) (classDiag S.lam l)
        (omegaF ϱ) (omegaF ϱ) =
      ((((Finset.univ.filter fun k => S.μ k = μ).card : ℝ) *
          ((Finset.univ.filter fun k => S.lam k = l).card : ℝ)) / (B : ℝ) ^ 2) *
        closedModeCl P Fp.C B Fp.β ℓ g μ l ϱ ∧
    IntegrableOn
      (fun p : ℝ × ℝ => closedModeH P Fp.C B Fp.β ℓ g μ l (ϱ + p.1 ^ 2) (ϱ + p.2 ^ 2))
      (Ioi 0 ×ˢ Ioi 0) := by
  classical
  let c : ℝ := (((Finset.univ.filter fun k => S.μ k = μ).card : ℝ) *
    ((Finset.univ.filter fun k => S.lam k = l).card : ℝ)) / (B : ℝ) ^ 2
  have hc : c ≠ 0 := by
    apply ne_of_gt
    apply div_pos
    · apply mul_pos
      · exact_mod_cast Finset.card_pos.mpr (by rcases hμ with ⟨i, hi⟩; exact ⟨i, by simp [hi]⟩)
      · exact_mod_cast Finset.card_pos.mpr (by rcases hl with ⟨j, hj⟩; exact ⟨j, by simp [hj]⟩)
    · exact sq_pos_of_pos (by exact_mod_cast Fp.hB)
  have hf := thm_app_vol_closed_filtered_i cert γstar CSig Fp S hS hCSig ℓ
    (classDiag S.μ μ) (classDiag S.lam l) ϱ ϱ hϱ hϱ
  have heq : (fun p : ℝ × ℝ =>
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (classDiag S.μ μ) (classDiag S.lam l)
        (iotaF (ϱ + p.1 ^ 2)) (iotaF (ϱ + p.2 ^ 2))) =
      (fun p => c * closedModeH P Fp.C B Fp.β ℓ g μ l (ϱ + p.1 ^ 2) (ϱ + p.2 ^ 2)) := by
    funext p
    exact hpoint _ _ (add_pos_of_pos_of_nonneg hϱ (sq_nonneg p.1))
      (add_pos_of_pos_of_nonneg hϱ (sq_nonneg p.2))
  constructor
  · rw [hf.2]
    have hi : ∀ x y : ℝ,
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (classDiag S.μ μ) (classDiag S.lam l)
          (iotaF (ϱ + x ^ 2)) (iotaF (ϱ + y ^ 2)) =
          c * closedModeH P Fp.C B Fp.β ℓ g μ l (ϱ + x ^ 2) (ϱ + y ^ 2) :=
      fun x y => congrFun heq (x, y)
    simp_rw [hi, integral_const_mul]
    unfold closedModeCl
    change _ = c * _
    ring
  · have hint := hf.1
    rw [heq] at hint
    have h := hint.const_mul c⁻¹
    simpa only [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ hc, one_mul] using h

private lemma closed_modes_lag_degenerate (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hC : Fp.C.Sout = 0 ∨ Fp.C.Sin = 0) (ℓ : ℕ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u) = 0 := by
  have hlim := thm_app_vol_lag_kernel_exists cert γstar CSig Fp S hS hCSig ℓ
    (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) (S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    Fd Gd rfl rfl (iotaF s) (iotaF u)
    (lem_app_vol_sharp_ii hs hs).1 (lem_app_vol_sharp_ii hu hu).1
  have hz : (fun p : ℕ × ℝ =>
      lagRespCut cert γstar CSig Fp.β ℓ p.1 p.2 B S.μ S.lam Fd Gd (iotaF s) (iotaF u)) =
      fun _ => 0 := by
    funext p
    exact closed_cutoff_degenerate cert γstar CSig Fp S hC ℓ p.1 p.2 Fd Gd
      (iotaF s) (iotaF u)
  rw [hz] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

open Classical in
/-- `cor:app-vol-closed-modes`, part (i), snapshot `cr-2026-10-23`. Declaration of record: for
eigenvalues `μ` of `Σ_out` and `λ` of `Σ_in` and `ℓ ≥ 0`, the closed mode kernel is nonnegative and
`𝔨_ℓ[P_μ,P'_λ](s,u) = (r_μ t_λ / B²) 𝔥_ℓ(μ,λ;s,u)`, and `C̄_ℓ[P_μ,P'_λ](ϱ,ϱ) = (r_μ t_λ/B²) 𝔠_ℓ(μ,λ;ϱ)`,
where `r_μ`, `t_λ` are the multiplicities. The tests are the spectral projections `projOut`,
`projIn` written with `classDiag`. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{corollary}[Mode volatility]\label{cor:app-vol-closed-modes}
Let $\ridge>0$, and let $\mu,\lambda$ be eigenvalues of $\Sigmaout,\Sigmain$.
\begin{enumerate}[label=(\roman*)]
\item For all $\ell\ge0$ and $s,u>0$, $\mathfrak h_\ell(\mu,\lambda;s,u)\ge0$ and
\[
\mathfrak k_\ell[P_\mu,P'_\lambda](s,u)=\frac{r_\mu t_\lambda}{B^2}\,\mathfrak h_\ell(\mu,\lambda;s,u),\qquad
\overline C_\ell[P_\mu,P'_\lambda](\ridge,\ridge)=\frac{r_\mu t_\lambda}{B^2}\,\mathfrak c_\ell(\mu,\lambda;\ridge).
\]
\item For all $\ell\ge0$,
\[
0\le\mathfrak c_\ell(\mu,\lambda;\ridge)\le\frac{\mu\lambda\,\sw2\,(1+\kappa_\Sigma/\ridge)^2}{\ridge}\,\bmom^\ell .
\]
\item The mode coefficient \cref{eqn:app-vol-vij} is, for every $i,j$,
\begin{equation}\label{eqn:app-vol-closed-vij}
\begin{gathered}
\mathfrak v_{ij}(\ridge)=\frac1B\Big(\mathfrak c_0(\mu_i,\lambda_j;\ridge)+2\sum_{\ell\ge1}\mathfrak c_\ell(\mu_i,\lambda_j;\ridge)\Big),\\
0\le\mathfrak v_{ij}(\ridge)\le\frac{\mu_i\lambda_j\,\sw2\,(1+\kappa_\Sigma/\ridge)^2}{B\,\ridge}\cdot\frac{1+\bmom}{1-\bmom},
\end{gathered}
\end{equation}
the series converging absolutely with nonnegative terms.
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_vol_closed_modes_i (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (ℓ : ℕ)
    {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g) (μ l : ℝ)
    (hμ : μ ∈ Set.range S.μ) (hl : l ∈ Set.range S.lam) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    (∀ s u : ℝ, 0 < s → 0 < u → 0 ≤ closedModeH P Fp.C B Fp.β ℓ g μ l s u) ∧
    (∀ s u : ℝ, 0 < s → 0 < u →
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (classDiag S.μ μ) (classDiag S.lam l)
          (iotaF s) (iotaF u) =
        ((((Finset.univ.filter fun k => S.μ k = μ).card : ℝ) *
          ((Finset.univ.filter fun k => S.lam k = l).card : ℝ)) / (B : ℝ) ^ 2) *
          closedModeH P Fp.C B Fp.β ℓ g μ l s u) ∧
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (classDiag S.μ μ) (classDiag S.lam l)
        (omegaF ϱ) (omegaF ϱ) =
      ((((Finset.univ.filter fun k => S.μ k = μ).card : ℝ) *
          ((Finset.univ.filter fun k => S.lam k = l).card : ℝ)) / (B : ℝ) ^ 2) *
        closedModeCl P Fp.C B Fp.β ℓ g μ l ϱ ∧
    IntegrableOn
      (fun p : ℝ × ℝ => closedModeH P Fp.C B Fp.β ℓ g μ l (ϱ + p.1 ^ 2) (ϱ + p.2 ^ 2))
      (Ioi 0 ×ˢ Ioi 0) := by
  have hpoint : ∀ s u : ℝ, 0 < s → 0 < u →
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (classDiag S.μ μ) (classDiag S.lam l)
          (iotaF s) (iotaF u) =
        ((((Finset.univ.filter fun k => S.μ k = μ).card : ℝ) *
          ((Finset.univ.filter fun k => S.lam k = l).card : ℝ)) / (B : ℝ) ^ 2) *
          closedModeH P Fp.C B Fp.β ℓ g μ l s u := by
    intro s u hs hu
    rw [← closed_modes_profile_projection γstar CSig Fp S hS ℓ hg μ l hμ hl s u hs hu]
    by_cases hC : Fp.C.Sout = 0 ∨ Fp.C.Sin = 0
    · rw [closed_modes_lag_degenerate cert γstar CSig Fp S hS hCSig hC ℓ
        (classDiag S.μ μ) (classDiag S.lam l) s u hs hu,
        closed_profileKernel_degenerate Fp.C P _ _ hC]
    · have hout : Fp.C.Sout ≠ 0 := fun h => hC (Or.inl h)
      have hin : Fp.C.Sin ≠ 0 := fun h => hC (Or.inr h)
      obtain ⟨Q, hQ, hgQ⟩ := closed_bounds_gauss_exists ℤ
      letI := hQ
      obtain ⟨e, he, he1, he2, hele, herange⟩ := closed_modes_cutoff_embedding ℓ
      let Fm := S.uOut * Matrix.diagonal (classDiag S.μ μ) * S.uOutᵀ
      let Gm := S.vIn * Matrix.diagonal (classDiag S.lam l) * S.vInᵀ
      have hconv := closed_modes_cutoff_to_ema γstar CSig Fp hS hout hin ℓ hgQ
        e he he1 he2 hele herange Fm Gm s u hs hu
      have hlim := thm_app_vol_lag_kernel_exists cert γstar CSig Fp S hS hCSig ℓ
        Fm Gm (classDiag S.μ μ) (classDiag S.lam l) rfl rfl (iotaF s) (iotaF u)
        (lem_app_vol_sharp_ii hs hs).1 (lem_app_vol_sharp_ii hu hu).1
      have hseq : Tendsto (fun k : ℕ => (k, (k : ℝ) + 1)) atTop
          (atTop ×ˢ atTop : Filter (ℕ × ℝ)) :=
        tendsto_id.prodMk (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      have hlim' := (hlim.comp hseq).congr' (Filter.Eventually.of_forall fun k =>
        (thm_app_vol_closed_kernel_cutoff cert γstar CSig Fp S hS hCSig
          ℓ k ((k : ℝ) + 1) hgQ Fm Gm (classDiag S.μ μ) (classDiag S.lam l)
          rfl rfl s u hs hu).1)
      have heq := tendsto_nhds_unique hlim' hconv.2
      rw [heq, closed_modes_profile_projection γstar CSig Fp S hS ℓ hconv.1 μ l hμ hl s u hs hu,
        closed_modes_profile_projection γstar CSig Fp S hS ℓ hg μ l hμ hl s u hs hu,
        closed_modes_modeH_law γstar CSig Fp hS hout hin ℓ hg hconv.1 μ l s u hs hu]
  refine ⟨?_, hpoint,
    closed_modes_filtered_of_pointwise cert γstar CSig Fp S hS hCSig ℓ g μ l hμ hl
      hpoint ϱ hϱ⟩
  rcases hμ with ⟨i, rfl⟩
  rcases hl with ⟨j, rfl⟩
  intro s u hs hu
  exact (closed_modeH_pointwise γstar CSig Fp S hS ℓ hg i j s u hs hu).1

/-- `cor:app-vol-closed-modes`, part (ii), snapshot `cr-2026-10-23`. Declaration of record: for
eigenvalues `μ ∈ spec Σ_out`, `λ ∈ spec Σ_in`, `ϱ > 0` and `ℓ ≥ 0`,
`0 ≤ 𝔠_ℓ(μ,λ;ϱ) ≤ μ λ sw₂ (1 + κ_Σ/ϱ)² β^ℓ / ϱ`. LaTeX, verbatim from `section.tex` (the whole
environment):

```latex
\begin{corollary}[Mode volatility]\label{cor:app-vol-closed-modes}
Let $\ridge>0$, and let $\mu,\lambda$ be eigenvalues of $\Sigmaout,\Sigmain$.
\begin{enumerate}[label=(\roman*)]
\item For all $\ell\ge0$ and $s,u>0$, $\mathfrak h_\ell(\mu,\lambda;s,u)\ge0$ and
\[
\mathfrak k_\ell[P_\mu,P'_\lambda](s,u)=\frac{r_\mu t_\lambda}{B^2}\,\mathfrak h_\ell(\mu,\lambda;s,u),\qquad
\overline C_\ell[P_\mu,P'_\lambda](\ridge,\ridge)=\frac{r_\mu t_\lambda}{B^2}\,\mathfrak c_\ell(\mu,\lambda;\ridge).
\]
\item For all $\ell\ge0$,
\[
0\le\mathfrak c_\ell(\mu,\lambda;\ridge)\le\frac{\mu\lambda\,\sw2\,(1+\kappa_\Sigma/\ridge)^2}{\ridge}\,\bmom^\ell .
\]
\item The mode coefficient \cref{eqn:app-vol-vij} is, for every $i,j$,
\begin{equation}\label{eqn:app-vol-closed-vij}
\begin{gathered}
\mathfrak v_{ij}(\ridge)=\frac1B\Big(\mathfrak c_0(\mu_i,\lambda_j;\ridge)+2\sum_{\ell\ge1}\mathfrak c_\ell(\mu_i,\lambda_j;\ridge)\Big),\\
0\le\mathfrak v_{ij}(\ridge)\le\frac{\mu_i\lambda_j\,\sw2\,(1+\kappa_\Sigma/\ridge)^2}{B\,\ridge}\cdot\frac{1+\bmom}{1-\bmom},
\end{gathered}
\end{equation}
the series converging absolutely with nonnegative terms.
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_vol_closed_modes_ii (γstar CSig : ℝ) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m n B : ℕ} (Fp : FrozenParams m n B)
    (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig) (ℓ : ℕ)
    {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g) (μ l : ℝ)
    (hμ : μ ∈ Set.range S.μ) (hl : l ∈ Set.range S.lam) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    0 ≤ closedModeCl P Fp.C B Fp.β ℓ g μ l ϱ ∧
      closedModeCl P Fp.C B Fp.β ℓ g μ l ϱ ≤
        μ * l * Muon.sPow Fp.β 2 * (1 + kappaSigma Fp.C B / ϱ) ^ 2 / ϱ * Fp.β ^ ℓ := by
  rcases hμ with ⟨i, rfl⟩
  rcases hl with ⟨j, rfl⟩
  let A : ℝ := S.μ i * S.lam j * Muon.sPow Fp.β 2 *
    (1 + kappaSigma Fp.C B / ϱ) ^ 2 * Fp.β ^ ℓ
  have hκ : 0 ≤ kappaSigma Fp.C B := by
    unfold kappaSigma
    exact le_max_of_le_left (mul_nonneg
      (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) Fp.C.psdIn.trace_nonneg)
      (by unfold Muon.opNorm; exact norm_nonneg _))
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (μ_nonneg S i) (lam_nonneg S j))
          (by unfold Muon.sPow; exact tsum_nonneg fun k => sq_nonneg _))
        (sq_nonneg _))
      (pow_nonneg Fp.hβ.1 ℓ)
  have hpt : ∀ x y : ℝ,
      0 ≤ closedModeH P Fp.C B Fp.β ℓ g (S.μ i) (S.lam j)
        (ϱ + x ^ 2) (ϱ + y ^ 2) ∧
      closedModeH P Fp.C B Fp.β ℓ g (S.μ i) (S.lam j)
          (ϱ + x ^ 2) (ϱ + y ^ 2) ≤
        A * (ϱ + x ^ 2)⁻¹ * (ϱ + y ^ 2)⁻¹ := by
    intro x y
    have hs : 0 < ϱ + x ^ 2 := add_pos_of_pos_of_nonneg hϱ (sq_nonneg x)
    have hu : 0 < ϱ + y ^ 2 := add_pos_of_pos_of_nonneg hϱ (sq_nonneg y)
    have hb := closed_modeH_pointwise γstar CSig Fp S hS ℓ hg i j
      (ϱ + x ^ 2) (ϱ + y ^ 2) hs hu
    refine ⟨hb.1, hb.2.trans ?_⟩
    have hm : ϱ ≤ min (ϱ + x ^ 2) (ϱ + y ^ 2) :=
      le_min (le_add_of_nonneg_right (sq_nonneg x)) (le_add_of_nonneg_right (sq_nonneg y))
    have ht : 0 < min (ϱ + x ^ 2) (ϱ + y ^ 2) := lt_min hs hu
    have htheta : 1 / thetaSigma Fp.C B (min (ϱ + x ^ 2) (ϱ + y ^ 2)) ^ 2 ≤
        (1 + kappaSigma Fp.C B / ϱ) ^ 2 := by
      have h1 : kappaSigma Fp.C B / min (ϱ + x ^ 2) (ϱ + y ^ 2) ≤
          kappaSigma Fp.C B / ϱ := div_le_div_of_nonneg_left hκ hϱ hm
      have hleft : 0 ≤ 1 + kappaSigma Fp.C B /
          min (ϱ + x ^ 2) (ϱ + y ^ 2) := by positivity
      have he : 1 / thetaSigma Fp.C B (min (ϱ + x ^ 2) (ϱ + y ^ 2)) ^ 2 =
          (1 + kappaSigma Fp.C B / min (ϱ + x ^ 2) (ϱ + y ^ 2)) ^ 2 := by
        unfold thetaSigma
        field_simp [hϱ.ne', ht.ne', (add_pos_of_pos_of_nonneg ht hκ).ne']
      rw [he]
      nlinarith [mul_nonneg (sub_nonneg.2 h1) hleft,
        sq_nonneg (kappaSigma Fp.C B / ϱ -
          kappaSigma Fp.C B / min (ϱ + x ^ 2) (ϱ + y ^ 2))]
    calc
      S.μ i * S.lam j * Muon.sPow Fp.β 2 * Fp.β ^ ℓ /
          ((ϱ + x ^ 2) * (ϱ + y ^ 2) *
            thetaSigma Fp.C B (min (ϱ + x ^ 2) (ϱ + y ^ 2)) ^ 2) =
        (S.μ i * S.lam j * Muon.sPow Fp.β 2 * Fp.β ^ ℓ) *
          (1 / thetaSigma Fp.C B (min (ϱ + x ^ 2) (ϱ + y ^ 2)) ^ 2) *
            (ϱ + x ^ 2)⁻¹ * (ϱ + y ^ 2)⁻¹ := by
              field_simp
      _ ≤ (S.μ i * S.lam j * Muon.sPow Fp.β 2 * Fp.β ^ ℓ) *
          (1 + kappaSigma Fp.C B / ϱ) ^ 2 *
            (ϱ + x ^ 2)⁻¹ * (ϱ + y ^ 2)⁻¹ := by
        have hcoef : 0 ≤ S.μ i * S.lam j * Muon.sPow Fp.β 2 * Fp.β ^ ℓ :=
          mul_nonneg
            (mul_nonneg (mul_nonneg (μ_nonneg S i) (lam_nonneg S j))
              (by unfold Muon.sPow; exact tsum_nonneg fun k => sq_nonneg _))
            (pow_nonneg Fp.hβ.1 ℓ)
        gcongr
      _ = _ := by simp only [A]; ring
  have hinner : ∀ x : ℝ,
      ∫ y in Ioi (0 : ℝ), closedModeH P Fp.C B Fp.β ℓ g (S.μ i) (S.lam j)
          (ϱ + x ^ 2) (ϱ + y ^ 2) ≤
        (A * (ϱ + x ^ 2)⁻¹) * (Real.pi / (2 * Real.sqrt ϱ)) := by
    intro x
    have hgint : Integrable (fun y : ℝ =>
        (A * (ϱ + x ^ 2)⁻¹) * (ϱ + y ^ 2)⁻¹) (volume.restrict (Ioi (0 : ℝ))) :=
      ((closed_filt_integrable hϱ).const_mul (A * (ϱ + x ^ 2)⁻¹)).integrableOn
    refine (integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ioi fun y _ => (hpt x y).1)
      hgint (ae_restrict_of_forall_mem measurableSet_Ioi fun y _ => ?_)).trans_eq ?_
    · simpa only [mul_assoc] using (hpt x y).2
    · rw [integral_const_mul, closed_filt_integral hϱ]
  have houter :
      ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
          closedModeH P Fp.C B Fp.β ℓ g (S.μ i) (S.lam j)
            (ϱ + x ^ 2) (ϱ + y ^ 2) ≤
        (A * (Real.pi / (2 * Real.sqrt ϱ))) * (Real.pi / (2 * Real.sqrt ϱ)) := by
    have hgint : Integrable (fun x : ℝ =>
        (A * (Real.pi / (2 * Real.sqrt ϱ))) * (ϱ + x ^ 2)⁻¹)
        (volume.restrict (Ioi (0 : ℝ))) :=
      ((closed_filt_integrable hϱ).const_mul
        (A * (Real.pi / (2 * Real.sqrt ϱ)))).integrableOn
    refine (integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x _ =>
        integral_nonneg fun y => (hpt x y).1)
      hgint (ae_restrict_of_forall_mem measurableSet_Ioi fun x _ => ?_)).trans_eq ?_
    · calc
        ∫ y in Ioi (0 : ℝ), closedModeH P Fp.C B Fp.β ℓ g (S.μ i) (S.lam j)
            (ϱ + x ^ 2) (ϱ + y ^ 2) ≤
            (A * (ϱ + x ^ 2)⁻¹) * (Real.pi / (2 * Real.sqrt ϱ)) := hinner x
        _ = (A * (Real.pi / (2 * Real.sqrt ϱ))) * (ϱ + x ^ 2)⁻¹ := by ring
    · rw [integral_const_mul, closed_filt_integral hϱ]
  unfold closedModeCl
  constructor
  · exact mul_nonneg (by positivity) (integral_nonneg fun x => integral_nonneg fun y => (hpt x y).1)
  · refine (mul_le_mul_of_nonneg_left houter (by positivity)).trans_eq ?_
    dsimp [A]
    have hsqrt : 0 < Real.sqrt ϱ := Real.sqrt_pos.2 hϱ
    field_simp [Real.pi_ne_zero, hsqrt.ne', hϱ.ne']
    rw [Real.sq_sqrt hϱ.le]
    ring

private lemma closed_modes_pairMeasure_apply (xs ys : Finset ℝ) (v : ℝ → ℝ → ℝ) (x y : ℝ) :
    pairMeasure xs ys v (x, y) = if x ∈ xs ∧ y ∈ ys then v x y else 0 := by
  classical
  have hs : ∀ a b : ℝ, (Finsupp.single (a, b) (v a b) : (ℝ × ℝ) →₀ ℝ) (x, y) =
      if a = x ∧ b = y then v a b else 0 := by
    intro a b
    by_cases h : (a, b) = (x, y)
    · cases h
      simp
    · have hn : ¬ (a = x ∧ b = y) := fun hab => h (Prod.ext hab.1 hab.2)
      simp [Finsupp.single_apply, h, hn]
  simp [pairMeasure]
  simp_rw [hs]
  have hi : ∀ a ∈ xs,
      (∑ b ∈ ys, if a = x ∧ b = y then v a b else 0) =
        if a = x then (if y ∈ ys then v a y else 0) else 0 := by
    intro a ha
    by_cases hax : a = x
    · subst a
      simp
    · simp [hax]
  rw [Finset.sum_congr rfl hi]
  by_cases hx : x ∈ xs <;> by_cases hy : y ∈ ys <;> simp [hx, hy]

open Classical in
/-- `cor:app-vol-closed-modes`, part (iii), snapshot `cr-2026-10-23`. Declaration of record: the mode
coefficient `𝔳_ij(ϱ) = (1/B)(𝔠_0(μ_i,λ_j;ϱ) + 2 ∑_{ℓ≥1} 𝔠_ℓ(μ_i,λ_j;ϱ))` with absolutely
convergent nonnegative terms, and `0 ≤ 𝔳_ij(ϱ) ≤ μ_i λ_j sw₂ (1+κ_Σ/ϱ)² (1+β)/((1-β) B ϱ)`. The lag
Gaussian families are `g ℓ` for each lag. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{corollary}[Mode volatility]\label{cor:app-vol-closed-modes}
Let $\ridge>0$, and let $\mu,\lambda$ be eigenvalues of $\Sigmaout,\Sigmain$.
\begin{enumerate}[label=(\roman*)]
\item For all $\ell\ge0$ and $s,u>0$, $\mathfrak h_\ell(\mu,\lambda;s,u)\ge0$ and
\[
\mathfrak k_\ell[P_\mu,P'_\lambda](s,u)=\frac{r_\mu t_\lambda}{B^2}\,\mathfrak h_\ell(\mu,\lambda;s,u),\qquad
\overline C_\ell[P_\mu,P'_\lambda](\ridge,\ridge)=\frac{r_\mu t_\lambda}{B^2}\,\mathfrak c_\ell(\mu,\lambda;\ridge).
\]
\item For all $\ell\ge0$,
\[
0\le\mathfrak c_\ell(\mu,\lambda;\ridge)\le\frac{\mu\lambda\,\sw2\,(1+\kappa_\Sigma/\ridge)^2}{\ridge}\,\bmom^\ell .
\]
\item The mode coefficient \cref{eqn:app-vol-vij} is, for every $i,j$,
\begin{equation}\label{eqn:app-vol-closed-vij}
\begin{gathered}
\mathfrak v_{ij}(\ridge)=\frac1B\Big(\mathfrak c_0(\mu_i,\lambda_j;\ridge)+2\sum_{\ell\ge1}\mathfrak c_\ell(\mu_i,\lambda_j;\ridge)\Big),\\
0\le\mathfrak v_{ij}(\ridge)\le\frac{\mu_i\lambda_j\,\sw2\,(1+\kappa_\Sigma/\ridge)^2}{B\,\ridge}\cdot\frac{1+\bmom}{1-\bmom},
\end{gathered}
\end{equation}
the series converging absolutely with nonnegative terms.
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_vol_closed_modes_iii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (g : ∀ ℓ : ℕ, ℕ ⊕ Fin ℓ → Ω → ℝ) (hg : ∀ ℓ : ℕ, IsStdGaussianFamily P (g ℓ))
    (i : Fin m) (j : Fin n) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    Summable (fun ℓ : ℕ => closedModeCl P Fp.C B Fp.β (ℓ + 1) (g (ℓ + 1)) (S.μ i) (S.lam j) ϱ) ∧
    modeVij cert γstar CSig Fp S ϱ i j =
        (B : ℝ)⁻¹ * (closedModeCl P Fp.C B Fp.β 0 (g 0) (S.μ i) (S.lam j) ϱ +
          2 * ∑' ℓ : ℕ, closedModeCl P Fp.C B Fp.β (ℓ + 1) (g (ℓ + 1)) (S.μ i) (S.lam j) ϱ) ∧
    0 ≤ modeVij cert γstar CSig Fp S ϱ i j ∧
      modeVij cert γstar CSig Fp S ϱ i j ≤
        S.μ i * S.lam j * Muon.sPow Fp.β 2 * (1 + kappaSigma Fp.C B / ϱ) ^ 2 / ((B : ℝ) * ϱ) *
          ((1 + Fp.β) / (1 - Fp.β)) := by
  let c : ℕ → ℝ := fun ℓ =>
    closedModeCl P Fp.C B Fp.β ℓ (g ℓ) (S.μ i) (S.lam j) ϱ
  let K : ℝ := S.μ i * S.lam j * Muon.sPow Fp.β 2 *
    (1 + kappaSigma Fp.C B / ϱ) ^ 2 / ϱ
  let r : ℝ := ((Finset.univ.filter fun k => S.μ k = S.μ i).card : ℝ)
  let t : ℝ := ((Finset.univ.filter fun k => S.lam k = S.lam j).card : ℝ)
  have hc : ∀ ℓ : ℕ, 0 ≤ c ℓ ∧ c ℓ ≤ K * Fp.β ^ ℓ := by
    intro ℓ
    simpa only [c, K] using
      (cor_app_vol_closed_modes_ii γstar CSig Fp S hS ℓ (hg ℓ)
        (S.μ i) (S.lam j) ⟨i, rfl⟩ ⟨j, rfl⟩ ϱ hϱ)
  have hgeo : Summable (fun ℓ : ℕ => Fp.β ^ ℓ) :=
    summable_geometric_of_lt_one Fp.hβ.1 Fp.hβ.2
  have hmajor : Summable (fun ℓ : ℕ => K * Fp.β ^ (ℓ + 1)) := by
    convert hgeo.mul_left (K * Fp.β) using 1
    funext ℓ
    rw [pow_succ]
    ring
  have hsum : Summable (fun ℓ : ℕ => c (ℓ + 1)) :=
    Summable.of_nonneg_of_le (fun ℓ => (hc (ℓ + 1)).1)
      (fun ℓ => (hc (ℓ + 1)).2) hmajor
  have hsum_target : Summable (fun ℓ : ℕ =>
      closedModeCl P Fp.C B Fp.β (ℓ + 1) (g (ℓ + 1)) (S.μ i) (S.lam j) ϱ) := by
    simpa only [c] using hsum
  have hr : 0 < r := by
    have hrN : 0 < (Finset.univ.filter fun k => S.μ k = S.μ i).card :=
      Finset.card_pos.mpr ⟨i, by simp⟩
    dsimp only [r]
    exact_mod_cast hrN
  have ht : 0 < t := by
    have htN : 0 < (Finset.univ.filter fun k => S.lam k = S.lam j).card :=
      Finset.card_pos.mpr ⟨j, by simp⟩
    dsimp only [t]
    exact_mod_cast htN
  have hB : (B : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt Fp.hB)
  have hL : ∀ ℓ : ℕ,
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam
          (classDiag S.μ (S.μ i)) (classDiag S.lam (S.lam j))
          (omegaF ϱ) (omegaF ϱ) =
        (r * t / (B : ℝ) ^ 2) * c ℓ := by
    intro ℓ
    simpa only [r, t, c] using
      (cor_app_vol_closed_modes_i cert γstar CSig Fp S hS hCSig ℓ (hg ℓ)
        (S.μ i) (S.lam j) ⟨i, rfl⟩ ⟨j, rfl⟩ ϱ hϱ).2.2.1
  have hzeta : measureZeta cert γstar CSig Fp S ϱ (S.μ i, S.lam j) =
      lagGammaBar cert γstar CSig Fp.β B S.μ S.lam
        (classDiag S.μ (S.μ i)) (classDiag S.lam (S.lam j)) ϱ ϱ := by
    rw [measureZeta, closed_modes_pairMeasure_apply]
    simp [muVals, lamVals]
  have hgamma : lagGammaBar cert γstar CSig Fp.β B S.μ S.lam
        (classDiag S.μ (S.μ i)) (classDiag S.lam (S.lam j)) ϱ ϱ =
      (r * t / (B : ℝ) ^ 2) * (c 0 + 2 * ∑' ℓ : ℕ, c (ℓ + 1)) := by
    unfold lagGammaBar
    rw [hL 0]
    calc
      (r * t / (B : ℝ) ^ 2) * c 0 +
          ∑' ℓ : ℕ,
            (lagResp cert γstar CSig Fp.β (ℓ + 1) B S.μ S.lam
                (classDiag S.μ (S.μ i)) (classDiag S.lam (S.lam j))
                (omegaF ϱ) (omegaF ϱ) +
              lagResp cert γstar CSig Fp.β (ℓ + 1) B S.μ S.lam
                (classDiag S.μ (S.μ i)) (classDiag S.lam (S.lam j))
                (omegaF ϱ) (omegaF ϱ)) =
          (r * t / (B : ℝ) ^ 2) * c 0 +
            ∑' ℓ : ℕ, (r * t / (B : ℝ) ^ 2) * (2 * c (ℓ + 1)) := by
              congr 1
              apply tsum_congr
              intro ℓ
              rw [hL (ℓ + 1)]
              ring
      _ = (r * t / (B : ℝ) ^ 2) * c 0 +
          (r * t / (B : ℝ) ^ 2) * (∑' ℓ : ℕ, 2 * c (ℓ + 1)) := by
            rw [tsum_mul_left]
      _ = (r * t / (B : ℝ) ^ 2) * (c 0 + 2 * ∑' ℓ : ℕ, c (ℓ + 1)) := by
            rw [tsum_mul_left]
            ring
  have hmode : modeVij cert γstar CSig Fp S ϱ i j =
      (B : ℝ)⁻¹ * (c 0 + 2 * ∑' ℓ : ℕ, c (ℓ + 1)) := by
    unfold modeVij
    rw [hzeta, hgamma]
    dsimp only [r, t]
    field_simp [hB, hr.ne', ht.ne']
  have hmode_target : modeVij cert γstar CSig Fp S ϱ i j =
      (B : ℝ)⁻¹ * (closedModeCl P Fp.C B Fp.β 0 (g 0) (S.μ i) (S.lam j) ϱ +
        2 * ∑' ℓ : ℕ,
          closedModeCl P Fp.C B Fp.β (ℓ + 1) (g (ℓ + 1)) (S.μ i) (S.lam j) ϱ) := by
    simpa only [c] using hmode
  have htail0 : 0 ≤ ∑' ℓ : ℕ, c (ℓ + 1) := tsum_nonneg fun ℓ => (hc (ℓ + 1)).1
  have hX0 : 0 ≤ c 0 + 2 * ∑' ℓ : ℕ, c (ℓ + 1) :=
    add_nonneg (hc 0).1 (mul_nonneg (by norm_num) htail0)
  have hmode0 : 0 ≤ modeVij cert γstar CSig Fp S ϱ i j := by
    rw [hmode]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg B)) hX0
  have htail : (∑' ℓ : ℕ, c (ℓ + 1)) ≤ K * Fp.β / (1 - Fp.β) := by
    calc
      (∑' ℓ : ℕ, c (ℓ + 1)) ≤ ∑' ℓ : ℕ, K * Fp.β ^ (ℓ + 1) :=
        Summable.tsum_le_tsum (fun ℓ => (hc (ℓ + 1)).2) hsum hmajor
      _ = ∑' ℓ : ℕ, (K * Fp.β) * Fp.β ^ ℓ := by
        apply tsum_congr
        intro ℓ
        rw [pow_succ]
        ring
      _ = K * Fp.β / (1 - Fp.β) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one Fp.hβ.1 Fp.hβ.2]
        simp only [div_eq_mul_inv]
  have hX : c 0 + 2 * ∑' ℓ : ℕ, c (ℓ + 1) ≤
      K * ((1 + Fp.β) / (1 - Fp.β)) := by
    calc
      c 0 + 2 * ∑' ℓ : ℕ, c (ℓ + 1) ≤
          K + 2 * (K * Fp.β / (1 - Fp.β)) :=
        add_le_add (by simpa using (hc 0).2) (mul_le_mul_of_nonneg_left htail (by norm_num))
      _ = K * ((1 + Fp.β) / (1 - Fp.β)) := by
        field_simp [ne_of_gt (sub_pos.mpr Fp.hβ.2)]
        ring
  have hmode_le : modeVij cert γstar CSig Fp S ϱ i j ≤
      S.μ i * S.lam j * Muon.sPow Fp.β 2 * (1 + kappaSigma Fp.C B / ϱ) ^ 2 /
          ((B : ℝ) * ϱ) * ((1 + Fp.β) / (1 - Fp.β)) := by
    rw [hmode]
    calc
      (B : ℝ)⁻¹ * (c 0 + 2 * ∑' ℓ : ℕ, c (ℓ + 1)) ≤
          (B : ℝ)⁻¹ * (K * ((1 + Fp.β) / (1 - Fp.β))) :=
        mul_le_mul_of_nonneg_left hX (inv_nonneg.mpr (Nat.cast_nonneg B))
      _ = S.μ i * S.lam j * Muon.sPow Fp.β 2 *
          (1 + kappaSigma Fp.C B / ϱ) ^ 2 / ((B : ℝ) * ϱ) *
            ((1 + Fp.β) / (1 - Fp.β)) := by
        dsimp only [K]
        field_simp [hB, hϱ.ne']
  exact ⟨hsum_target, hmode_target, hmode0, hmode_le⟩

private lemma lag_emaW_shift (β : ℝ) (ℓ j : ℕ) :
    β ^ ℓ * Muon.emaW β j = Muon.emaW β (j + ℓ) := by
  simp only [Muon.emaW, pow_add]; ring

private lemma lag_pairedB_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (β : ℝ) (ℓ : ℕ)
    (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (q q' : ℝ) :
    pairedB P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' = emaLagB P β ℓ g q q' := by
  unfold pairedB emaLagB
  rw [← Function.Injective.tsum_eq (g := (Sum.inl : ℕ → ℕ ⊕ Fin ℓ)) Sum.inl_injective]
  · refine tsum_congr (fun j => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [emaXi₁, emaXi₂, phiQ]
    rw [← lag_emaW_shift β ℓ j, div_mul_div_comm]
  · intro a ha
    rcases a with j | i
    · exact ⟨j, rfl⟩
    · exfalso; apply ha
      simp [emaXi₁]

private lemma lag_pairedE_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (β : ℝ) (ℓ : ℕ)
    (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (q q' : ℝ) :
    pairedE P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' = emaLagE P β ℓ g q q' := by
  unfold pairedE emaLagE
  rw [← Function.Injective.tsum_eq (g := (Sum.inl : ℕ → ℕ ⊕ Fin ℓ)) Sum.inl_injective]
  · refine tsum_congr (fun j => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [emaXi₁, emaXi₂, psiQ]
    rw [← lag_emaW_shift β ℓ j, div_mul_div_comm]
  · intro a ha
    rcases a with j | i
    · exact ⟨j, rfl⟩
    · exfalso; apply ha
      simp [emaXi₁]


/-- `prop:app-vol-closed-lagsum`, part (i), snapshot `cr-2026-10-23`. Declaration of record: the lag
form. With the lag-independent quantities `A_o = s u 𝖴 σ̃ σ̃'`, `A_in = s u 𝖵 σ σ'`, `A_× = s u 𝖴 𝖵`
(`𝖴 = 𝒯^out[Σ_out]`, `𝖵 = 𝒯^in[Σ_in]` at the branch points of the two buffers), and
`b_ℓ = ∑_j 𝔼[φ_q(emaw_j g_j) φ_{q'}(emaw_{j+ℓ} g_j)]`, `e_ℓ = ∑_j 𝔼[ψ_q(emaw_j g_j) ψ_{q'}(emaw_{j+ℓ} g_j)]`,
the kernel at the EMA profile of lag `ℓ` equals
`s u 𝒯^out[Fm] 𝒯^in[Gm] b_ℓ / (1 - (A_o + A_in) e_ℓ + A_o A_in e_ℓ² - A_× b_ℓ²)`, for `s, u > 0`.
Here `q = s σ σ̃` and `q' = u σ' σ̃'` (`emaBr1`, `emaBr2`). LaTeX, verbatim from `section.tex` (the
whole environment):

```latex
\begin{proposition}[Lag dependence]\label{prop:app-vol-closed-lagsum}
Let $F,G$ be diagonal tests and $s,u,\ridge>0$. With the lag-independent
quantities
\[
A_{\mathrm o}\defeq su\,\mathsf U\tilde\sigma\tilde\sigma',\qquad A_{\mathrm{in}}\defeq su\,\mathsf V\sigma\sigma',\qquad A_\times\defeq su\,\mathsf U\mathsf V,
\]
for every $\ell\ge0$,
\[
\mathfrak k_\ell[F,G](s,u)=su\,\mathcal T^{\mathrm{out}}[F]\,\mathcal T^{\mathrm{in}}[G]\,\frac{b_\ell}{1-(A_{\mathrm o}+A_{\mathrm{in}})e_\ell+A_{\mathrm o}A_{\mathrm{in}}e_\ell^2-A_\times b_\ell^2},
\]
\[
b_\ell=\sum_{j\ge0}\EE\big[\phi_q(\emaw jg)\,\phi_{q'}(\emaw{j+\ell}g)\big],\qquad
e_\ell=\sum_{j\ge0}\EE\big[\psi_q(\emaw jg)\,\psi_{q'}(\emaw{j+\ell}g)\big].
\]
Moreover $\sum_\ell c_\ell\,\mathfrak k_\ell[F,G](\ridge+x^2,\ridge+y^2)$ converges absolutely
for all $x,y\ge0$, and
\[
\overline\Gamma[F,G](\ridge,\ridge)=\frac4{\pi^2}\int_0^\infty\!\!\int_0^\infty\sum_{\ell\ge0}c_\ell\,\mathfrak k_\ell[F,G](\ridge+x^2,\ridge+y^2)\,dx\,dy,
\]
with $\overline\Gamma$ of \cref{eqn:app-vol-Gammabar}, the double integral converging
absolutely.
\end{proposition}
```
-/
theorem prop_app_vol_closed_lagsum_i (γstar CSig : ℝ) {m n B : ℕ} (C : Muon.Covariances m n)
    (hB : 0 < B) (hS : SizeFin C B γstar CSig) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ℓ : ℕ)
    {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g) (Fm : Mat m m) (Gm : Mat n n)
    (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    profileKernel P C B (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) Fm Gm s u =
      s * u * toutT C B (emaBr1 P C B β ℓ g s) (emaBr2 P C B β ℓ g u) s u Fm *
          tinT C B (emaBr1 P C B β ℓ g s) (emaBr2 P C B β ℓ g u) s u Gm *
          emaLagB P β ℓ g (s * (emaBr1 P C B β ℓ g s).1 * (emaBr1 P C B β ℓ g s).2.1)
            (u * (emaBr2 P C B β ℓ g u).1 * (emaBr2 P C B β ℓ g u).2.1) /
        (1 -
          (s * u * toutT C B (emaBr1 P C B β ℓ g s) (emaBr2 P C B β ℓ g u) s u C.Sout *
              (emaBr1 P C B β ℓ g s).2.1 * (emaBr2 P C B β ℓ g u).2.1 +
            s * u * tinT C B (emaBr1 P C B β ℓ g s) (emaBr2 P C B β ℓ g u) s u C.Sin *
              (emaBr1 P C B β ℓ g s).1 * (emaBr2 P C B β ℓ g u).1) *
            emaLagE P β ℓ g (s * (emaBr1 P C B β ℓ g s).1 * (emaBr1 P C B β ℓ g s).2.1)
              (u * (emaBr2 P C B β ℓ g u).1 * (emaBr2 P C B β ℓ g u).2.1) +
          (s * u * toutT C B (emaBr1 P C B β ℓ g s) (emaBr2 P C B β ℓ g u) s u C.Sout *
              (emaBr1 P C B β ℓ g s).2.1 * (emaBr2 P C B β ℓ g u).2.1) *
            (s * u * tinT C B (emaBr1 P C B β ℓ g s) (emaBr2 P C B β ℓ g u) s u C.Sin *
              (emaBr1 P C B β ℓ g s).1 * (emaBr2 P C B β ℓ g u).1) *
            emaLagE P β ℓ g (s * (emaBr1 P C B β ℓ g s).1 * (emaBr1 P C B β ℓ g s).2.1)
              (u * (emaBr2 P C B β ℓ g u).1 * (emaBr2 P C B β ℓ g u).2.1) ^ 2 -
          (s * u * toutT C B (emaBr1 P C B β ℓ g s) (emaBr2 P C B β ℓ g u) s u C.Sout *
              tinT C B (emaBr1 P C B β ℓ g s) (emaBr2 P C B β ℓ g u) s u C.Sin) *
            emaLagB P β ℓ g (s * (emaBr1 P C B β ℓ g s).1 * (emaBr1 P C B β ℓ g s).2.1)
              (u * (emaBr2 P C B β ℓ g u).1 * (emaBr2 P C B β ℓ g u).2.1) ^ 2) := by
  simp only [profileKernel, profileDelta, closedDelta, emaBr1, emaBr2, lag_pairedB_eq,
    lag_pairedE_eq]
  ring

private lemma closed_quad_iter {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))) :
    ∫ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), f p =
      ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), f (x, y) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
  exact integral_prod _ hf

/-- `prop:app-vol-closed-lagsum`, part (ii), snapshot `cr-2026-10-23`. Declaration of record: the lag
sum. For `ϱ > 0`, every `x, y ≥ 0` the series `∑_ℓ c_ℓ 𝔨_ℓ[F,G](ϱ+x², ϱ+y²)` converges absolutely;
the function `(x,y) ↦ ∑_ℓ c_ℓ 𝔨_ℓ` is integrable on `(0,∞)²`; and
`Γ̄[F,G](ϱ,ϱ) = (4/π²) ∫∫ ∑_ℓ c_ℓ 𝔨_ℓ[F,G](ϱ+x², ϱ+y²) dx dy` with `Γ̄` of `eqn:app-vol-Gammabar`.
No closed form of the lag sum is claimed. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{proposition}[Lag dependence]\label{prop:app-vol-closed-lagsum}
Let $F,G$ be diagonal tests and $s,u,\ridge>0$. With the lag-independent
quantities
\[
A_{\mathrm o}\defeq su\,\mathsf U\tilde\sigma\tilde\sigma',\qquad A_{\mathrm{in}}\defeq su\,\mathsf V\sigma\sigma',\qquad A_\times\defeq su\,\mathsf U\mathsf V,
\]
for every $\ell\ge0$,
\[
\mathfrak k_\ell[F,G](s,u)=su\,\mathcal T^{\mathrm{out}}[F]\,\mathcal T^{\mathrm{in}}[G]\,\frac{b_\ell}{1-(A_{\mathrm o}+A_{\mathrm{in}})e_\ell+A_{\mathrm o}A_{\mathrm{in}}e_\ell^2-A_\times b_\ell^2},
\]
\[
b_\ell=\sum_{j\ge0}\EE\big[\phi_q(\emaw jg)\,\phi_{q'}(\emaw{j+\ell}g)\big],\qquad
e_\ell=\sum_{j\ge0}\EE\big[\psi_q(\emaw jg)\,\psi_{q'}(\emaw{j+\ell}g)\big].
\]
Moreover $\sum_\ell c_\ell\,\mathfrak k_\ell[F,G](\ridge+x^2,\ridge+y^2)$ converges absolutely
for all $x,y\ge0$, and
\[
\overline\Gamma[F,G](\ridge,\ridge)=\frac4{\pi^2}\int_0^\infty\!\!\int_0^\infty\sum_{\ell\ge0}c_\ell\,\mathfrak k_\ell[F,G](\ridge+x^2,\ridge+y^2)\,dx\,dy,
\]
with $\overline\Gamma$ of \cref{eqn:app-vol-Gammabar}, the double integral converging
absolutely.
\end{proposition}
```
-/
theorem prop_app_vol_closed_lagsum_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    (∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        Summable (fun ℓ : ℕ =>
          lagCoef ℓ * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd
            (iotaF (ϱ + x ^ 2)) (iotaF (ϱ + y ^ 2)))) ∧
      IntegrableOn
        (fun p : ℝ × ℝ => ∑' ℓ : ℕ, lagCoef ℓ * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd
          (iotaF (ϱ + p.1 ^ 2)) (iotaF (ϱ + p.2 ^ 2)))
        (Ioi 0 ×ˢ Ioi 0) ∧
      lagGammaBar cert γstar CSig Fp.β B S.μ S.lam Fd Gd ϱ ϱ =
        (4 / Real.pi ^ 2) * ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
          ∑' ℓ : ℕ, lagCoef ℓ * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd
            (iotaF (ϱ + x ^ 2)) (iotaF (ϱ + y ^ 2)) := by
  let Fm : Mat m m := S.uOut * Matrix.diagonal Fd * S.uOutᵀ
  let Gm : Mat n n := S.vIn * Matrix.diagonal Gd * S.vInᵀ
  let Fl : ℕ → ℝ × ℝ → ℝ := fun ℓ p =>
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF (ϱ + p.1 ^ 2)) (iotaF (ϱ + p.2 ^ 2))
  let Q : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
  let W : ℝ × ℝ → ℝ := fun p => (ϱ + p.1 ^ 2)⁻¹ * (ϱ + p.2 ^ 2)⁻¹
  let C0 : ℝ := Muon.sPow Fp.β 2 * (Fp.C.Sout.trace * Fp.C.Sin.trace) *
    Muon.opNorm Fm * Muon.opNorm Gm * (1 + kappaSigma Fp.C B / min ϱ ϱ) ^ 2 / (B : ℝ) ^ 2
  have hQmeas : MeasurableSet Q := measurableSet_Ioi.prod measurableSet_Ioi
  have hbd : ∀ (ℓ : ℕ) (p : ℝ × ℝ), |Fl ℓ p| ≤ C0 * Fp.β ^ ℓ * W p := by
    intro ℓ p
    have h := closed_filt_pointwise cert γstar CSig Fp S hS hCSig ℓ Fm Gm Fd Gd rfl rfl
      ϱ ϱ hϱ hϱ p.1 p.2
    refine h.trans (le_of_eq ?_)
    simp only [C0, W]
    ring
  have hbd2 : ∀ (ℓ : ℕ) (p : ℝ × ℝ), |lagCoef ℓ * Fl ℓ p| ≤ (2 * C0 * W p) * Fp.β ^ ℓ := by
    intro ℓ p
    have hc : |lagCoef ℓ| ≤ 2 := by
      unfold lagCoef; split_ifs <;> norm_num
    have hW0 : 0 ≤ W p := by
      have h1 : 0 < ϱ + p.1 ^ 2 := add_pos_of_pos_of_nonneg hϱ (sq_nonneg _)
      have h2 : 0 < ϱ + p.2 ^ 2 := add_pos_of_pos_of_nonneg hϱ (sq_nonneg _)
      exact (mul_pos (inv_pos.2 h1) (inv_pos.2 h2)).le
    have hb := hbd ℓ p
    have hC0 : 0 ≤ C0 * Fp.β ^ ℓ * W p := (abs_nonneg _).trans hb
    rw [abs_mul]
    calc |lagCoef ℓ| * |Fl ℓ p| ≤ 2 * (C0 * Fp.β ^ ℓ * W p) :=
          mul_le_mul hc hb (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hsum_geo : ∀ c : ℝ, Summable (fun ℓ : ℕ => c * Fp.β ^ ℓ) := fun c =>
    (summable_geometric_of_lt_one Fp.hβ.1 Fp.hβ.2).mul_left c
  have hpart1 : ∀ x y : ℝ,
      Summable (fun ℓ : ℕ => lagCoef ℓ * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd
        (iotaF (ϱ + x ^ 2)) (iotaF (ϱ + y ^ 2))) := by
    intro x y
    refine Summable.of_norm_bounded (hsum_geo (2 * C0 * W (x, y))) fun ℓ => ?_
    rw [Real.norm_eq_abs]
    exact hbd2 ℓ (x, y)
  have hW : IntegrableOn W Q := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact ((closed_filt_integrable hϱ).integrableOn.mul_prod
        (closed_filt_integrable hϱ).integrableOn)
  have hFint : ∀ ℓ, IntegrableOn (Fl ℓ) Q := fun ℓ =>
    (thm_app_vol_closed_filtered_i cert γstar CSig Fp S hS hCSig ℓ Fd Gd ϱ ϱ hϱ hϱ).1
  have hGint : ∀ ℓ, IntegrableOn (fun p => lagCoef ℓ * Fl ℓ p) Q := fun ℓ => (hFint ℓ).const_mul _
  have hGint' : ∀ ℓ, Integrable (fun p => lagCoef ℓ * Fl ℓ p) (volume.restrict Q) := hGint
  have hnormsum : Summable (fun ℓ : ℕ => ∫ p, ‖lagCoef ℓ * Fl ℓ p‖ ∂(volume.restrict Q)) := by
    refine Summable.of_nonneg_of_le (fun ℓ => integral_nonneg fun p => norm_nonneg _)
      (fun ℓ => ?_) (hsum_geo (2 * C0 * ∫ p, W p ∂(volume.restrict Q)))
    have hWi : Integrable W (volume.restrict Q) := hW
    calc ∫ p, ‖lagCoef ℓ * Fl ℓ p‖ ∂(volume.restrict Q)
        ≤ ∫ p, (2 * C0 * W p) * Fp.β ^ ℓ ∂(volume.restrict Q) := by
          refine integral_mono (hGint' ℓ).norm ((hWi.const_mul (2 * C0)).mul_const _) fun p => ?_
          simpa only [Real.norm_eq_abs] using hbd2 ℓ p
      _ = _ := by rw [integral_mul_const, integral_const_mul]
  have hHas := hasSum_integral_of_summable_integral_norm hGint' hnormsum
  have hpart2 : IntegrableOn (fun p : ℝ × ℝ => ∑' ℓ : ℕ, lagCoef ℓ * Fl ℓ p) Q := by
    have hWi : Integrable W (volume.restrict Q) := hW
    have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => ∑' ℓ : ℕ, lagCoef ℓ * Fl ℓ p)
        (volume.restrict Q) := by
      refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (f := fun N p => ∑ ℓ ∈ Finset.range N, lagCoef ℓ * Fl ℓ p) ?_ ?_
      · intro N
        have := Finset.aestronglyMeasurable_sum (Finset.range N)
          fun ℓ _ => (hGint' ℓ).aestronglyMeasurable
        convert this using 1
        ext p
        simp
      · refine Filter.Eventually.of_forall fun p => ?_
        exact (hpart1 p.1 p.2).hasSum.tendsto_sum_nat
    refine Integrable.mono' ((hWi.const_mul (2 * C0)).mul_const (1 - Fp.β)⁻¹) hmeas
      (Filter.Eventually.of_forall fun p => ?_)
    have hg := (hasSum_geometric_of_lt_one Fp.hβ.1 Fp.hβ.2).mul_left (2 * C0 * W p)
    refine tsum_of_norm_bounded hg fun ℓ => ?_
    rw [Real.norm_eq_abs]
    exact hbd2 ℓ p
  have hC : ∀ ℓ, lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (omegaF ϱ) (omegaF ϱ) =
      (4 / Real.pi ^ 2) * ∫ p in Q, Fl ℓ p := fun ℓ =>
    (thm_app_vol_closed_filtered_i cert γstar CSig Fp S hS hCSig ℓ Fd Gd ϱ ϱ hϱ hϱ).2.trans
      (congrArg _ (closed_quad_iter (hFint ℓ)).symm)
  have hH2 : HasSum (fun ℓ : ℕ => lagCoef ℓ *
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (omegaF ϱ) (omegaF ϱ))
      ((4 / Real.pi ^ 2) * ∫ p in Q, ∑' ℓ : ℕ, lagCoef ℓ * Fl ℓ p) := by
    convert hHas.mul_left (4 / Real.pi ^ 2) using 1
    funext ℓ
    rw [hC ℓ, integral_const_mul]
    ring
  have hit : ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
      ∑' ℓ : ℕ, lagCoef ℓ * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd
        (iotaF (ϱ + x ^ 2)) (iotaF (ϱ + y ^ 2)) =
      ∫ p in Q, ∑' ℓ : ℕ, lagCoef ℓ * Fl ℓ p := (closed_quad_iter hpart2).symm
  refine ⟨fun x y _ _ => hpart1 x y, hpart2, ?_⟩
  rw [hit]
  have hts := hH2.tsum_eq
  rw [hH2.summable.tsum_eq_zero_add] at hts
  rw [← hts]
  unfold lagGammaBar
  simp only [lagCoef, if_true, one_mul, Nat.add_one_ne_zero, if_false]
  congr 1
  exact tsum_congr fun ℓ => by ring

private lemma closed_lagResp_sum_left (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (Fd : Fin m → ℝ)
    (Gd : Fin n → ℝ) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    lagResp cert γstar CSig Fp.β 0 B S.μ S.lam Fd Gd (omegaF ϱ) (omegaF ϱ) =
      ∑ i, Fd i * lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (Pi.single i 1) Gd
        (omegaF ϱ) (omegaF ϱ) := by
  obtain ⟨-, hlin, -⟩ := thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS
    hCSig 0 (omegaF ϱ) (omegaF ϱ) (lem_app_vol_sharp_ii hϱ hϱ).2.1
      (lem_app_vol_sharp_ii hϱ hϱ).2.1
  have h0 : lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (fun _ => (0 : ℝ)) Gd
      (omegaF ϱ) (omegaF ϱ) = 0 := by
    have h := hlin 1 (fun _ => 0) (fun _ => 0) Gd
    simp only [mul_zero, zero_add, one_mul] at h
    linarith
  have step : ∀ s : Finset (Fin m),
      lagResp cert γstar CSig Fp.β 0 B S.μ S.lam
          (fun j => ∑ i ∈ s, Fd i * (Pi.single i 1 : Fin m → ℝ) j) Gd
          (omegaF ϱ) (omegaF ϱ) =
        ∑ i ∈ s, Fd i * lagResp cert γstar CSig Fp.β 0 B S.μ S.lam
          (Pi.single i 1) Gd (omegaF ϱ) (omegaF ϱ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert k s hk ih =>
      have h := hlin (Fd k) (Pi.single k 1)
        (fun j => ∑ i ∈ s, Fd i * (Pi.single i 1 : Fin m → ℝ) j) Gd
      simp only [Finset.sum_insert hk]
      rw [← ih, ← h]
  have h := step Finset.univ
  have hfun :
      (fun j => ∑ i ∈ (Finset.univ : Finset (Fin m)),
        Fd i * (Pi.single i 1 : Fin m → ℝ) j) = Fd := by
    funext j
    simp [Pi.single_apply]
  rwa [hfun] at h

private lemma closed_lagResp_sum_right (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (Fd : Fin m → ℝ)
    (Gd : Fin n → ℝ) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    lagResp cert γstar CSig Fp.β 0 B S.μ S.lam Fd Gd (omegaF ϱ) (omegaF ϱ) =
      ∑ j, Gd j * lagResp cert γstar CSig Fp.β 0 B S.μ S.lam Fd (Pi.single j 1)
        (omegaF ϱ) (omegaF ϱ) := by
  obtain ⟨-, -, hlin, -⟩ := thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS
    hCSig 0 (omegaF ϱ) (omegaF ϱ) (lem_app_vol_sharp_ii hϱ hϱ).2.1
      (lem_app_vol_sharp_ii hϱ hϱ).2.1
  have h0 : lagResp cert γstar CSig Fp.β 0 B S.μ S.lam Fd (fun _ => (0 : ℝ))
      (omegaF ϱ) (omegaF ϱ) = 0 := by
    have h := hlin 1 Fd (fun _ => 0) (fun _ => 0)
    simp only [mul_zero, zero_add, one_mul] at h
    linarith
  have step : ∀ s : Finset (Fin n),
      lagResp cert γstar CSig Fp.β 0 B S.μ S.lam Fd
          (fun k => ∑ j ∈ s, Gd j * (Pi.single j 1 : Fin n → ℝ) k)
          (omegaF ϱ) (omegaF ϱ) =
        ∑ j ∈ s, Gd j * lagResp cert γstar CSig Fp.β 0 B S.μ S.lam
          Fd (Pi.single j 1) (omegaF ϱ) (omegaF ϱ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert k s hk ih =>
      have h := hlin (Gd k) Fd (Pi.single k 1)
        (fun j => ∑ i ∈ s, Gd i * (Pi.single i 1 : Fin n → ℝ) j)
      simp only [Finset.sum_insert hk]
      rw [← ih, ← h]
  have h := step Finset.univ
  have hfun :
      (fun k => ∑ j ∈ (Finset.univ : Finset (Fin n)),
        Gd j * (Pi.single j 1 : Fin n → ℝ) k) = Gd := by
    funext k
    simp [Pi.single_apply]
  rwa [hfun] at h

private lemma closed_lagResp_single_left_eq (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (i i' : Fin m)
    (hi : S.μ i = S.μ i') (Gd : Fin n → ℝ) (ϱ : ℝ) :
    lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (Pi.single i 1) Gd
        (omegaF ϱ) (omegaF ϱ) =
      lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (Pi.single i' 1) Gd
        (omegaF ϱ) (omegaF ϱ) := by
  unfold lagResp lagRespCut treeRespExt def_app_vol_tree treeMono treeClassFactor
  have key : ∀ q r : ℕ, ∑ k : Fin m, S.μ k ^ q * (Pi.single i (1 : ℝ) : Fin m → ℝ) k ^ r =
      ∑ k : Fin m, S.μ k ^ q * (Pi.single i' (1 : ℝ) : Fin m → ℝ) k ^ r := by
    intro q r
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      simp
    · have hs : ∀ j : Fin m,
          ∑ k : Fin m, S.μ k ^ q * (Pi.single j (1 : ℝ) : Fin m → ℝ) k ^ r = S.μ j ^ q := by
        intro j
        rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk
          simp [Pi.single_apply, hk, hr.ne']
        · intro hj
          exact absurd (Finset.mem_univ j) hj
      rw [hs i, hs i', hi]
  simp only [key]

private lemma closed_lagResp_single_right_eq (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (Fd : Fin m → ℝ)
    (j j' : Fin n) (hj : S.lam j = S.lam j') (ϱ : ℝ) :
    lagResp cert γstar CSig Fp.β 0 B S.μ S.lam Fd (Pi.single j 1)
        (omegaF ϱ) (omegaF ϱ) =
      lagResp cert γstar CSig Fp.β 0 B S.μ S.lam Fd (Pi.single j' 1)
        (omegaF ϱ) (omegaF ϱ) := by
  unfold lagResp lagRespCut treeRespExt def_app_vol_tree treeMono treeClassFactor
  have key : ∀ q r : ℕ, ∑ k : Fin n, S.lam k ^ q * (Pi.single j (1 : ℝ) : Fin n → ℝ) k ^ r =
      ∑ k : Fin n, S.lam k ^ q * (Pi.single j' (1 : ℝ) : Fin n → ℝ) k ^ r := by
    intro q r
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      simp
    · have hs : ∀ l : Fin n,
          ∑ k : Fin n, S.lam k ^ q * (Pi.single l (1 : ℝ) : Fin n → ℝ) k ^ r = S.lam l ^ q := by
        intro l
        rw [Finset.sum_eq_single l]
        · simp
        · intro k _ hk
          simp [Pi.single_apply, hk, hr.ne']
        · intro hl
          exact absurd (Finset.mem_univ l) hl
      rw [hs j, hs j', hj]
  simp only [key]

open Classical in
private theorem closed_marginals_spectral_of_cert (cert : Muon.External.GaussianOpNorm)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : ℕ ⊕ Fin 0 → Ω → ℝ) (hg : IsStdGaussianFamily P g) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut Fp.C B)
    (hν' : (ν' : Measure ℝ) = Muon.nuIn Fp.C B) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    (∀ μ ∈ Set.range S.μ,
        (B : ℝ)⁻¹ * (∑ j : Fin n, closedModeCl P Fp.C B Fp.β 0 g μ (S.lam j) ϱ) =
          volraw Fp.β ν ν' μ ϱ) ∧
      (∀ l ∈ Set.range S.lam,
        (B : ℝ)⁻¹ * (∑ i : Fin m, closedModeCl P Fp.C B Fp.β 0 g (S.μ i) l ϱ) =
          volTildeZero Fp.β ν ν' l ϱ) := by
  have hmarg := cor_app_vol_marginals_tests cert γstar CSig Fp S hS hCSig ν ν' hν hν' ϱ hϱ
  have hB : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  constructor
  · intro μ hμ
    obtain ⟨i, rfl⟩ := hμ
    let r : ℝ := ((Finset.univ.filter fun k => S.μ k = S.μ i).card : ℝ)
    have hr : 0 < r := by
      dsimp [r]
      have hi : i ∈ Finset.univ.filter (fun k => S.μ k = S.μ i) := by simp
      exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩
    have hclass_single : ∀ j : Fin n,
        lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (classDiag S.μ (S.μ i)) (Pi.single j 1)
            (omegaF ϱ) (omegaF ϱ) =
          r / (B : ℝ) ^ 2 * closedModeCl P Fp.C B Fp.β 0 g (S.μ i) (S.lam j) ϱ := by
      intro j
      let t : ℝ := ((Finset.univ.filter fun k => S.lam k = S.lam j).card : ℝ)
      have ht : 0 < t := by
        dsimp [t]
        have hj : j ∈ Finset.univ.filter (fun k => S.lam k = S.lam j) := by simp
        exact_mod_cast Finset.card_pos.mpr ⟨j, hj⟩
      have hlin := closed_lagResp_sum_right cert γstar CSig Fp S hS hCSig
        (classDiag S.μ (S.μ i)) (classDiag S.lam (S.lam j)) ϱ hϱ
      have hsum :
          (∑ k : Fin n, classDiag S.lam (S.lam j) k *
              lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (classDiag S.μ (S.μ i))
                (Pi.single k 1) (omegaF ϱ) (omegaF ϱ)) =
            t * lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (classDiag S.μ (S.μ i))
              (Pi.single j 1) (omegaF ϱ) (omegaF ϱ) := by
        calc
          _ = ∑ k ∈ Finset.univ.filter (fun k => S.lam k = S.lam j),
                lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (classDiag S.μ (S.μ i))
                  (Pi.single k 1) (omegaF ϱ) (omegaF ϱ) := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro k _
              by_cases hk : S.lam k = S.lam j <;> simp [classDiag, hk]
          _ = ∑ k' ∈ Finset.univ.filter (fun k => S.lam k = S.lam j),
                lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (classDiag S.μ (S.μ i))
                  (Pi.single j 1) (omegaF ϱ) (omegaF ϱ) := by
              apply Finset.sum_congr rfl
              intro k hk
              exact closed_lagResp_single_right_eq cert γstar CSig Fp S
                (classDiag S.μ (S.μ i)) k j (Finset.mem_filter.mp hk).2 ϱ
          _ = _ := by simp [t]
      rw [hsum] at hlin
      have hmode := (cor_app_vol_closed_modes_i cert γstar CSig Fp S hS hCSig 0
        (Ω := Ω) (P := P) (g := g) hg
        (S.μ i) (S.lam j) ⟨i, rfl⟩ ⟨j, rfl⟩ ϱ hϱ).2.2.1
      rw [hmode] at hlin
      dsimp [r, t] at hlin ⊢
      field_simp [ne_of_gt ht] at hlin ⊢
      nlinarith
    have hright := closed_lagResp_sum_right cert γstar CSig Fp S hS hCSig
      (classDiag S.μ (S.μ i)) (fun _ : Fin n => (1 : ℝ)) ϱ hϱ
    simp only [one_mul] at hright
    have hresp :
        lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (classDiag S.μ (S.μ i))
            (fun _ : Fin n => 1) (omegaF ϱ) (omegaF ϱ) =
          r / (B : ℝ) ^ 2 *
            ∑ j : Fin n, closedModeCl P Fp.C B Fp.β 0 g (S.μ i) (S.lam j) ϱ := by
      rw [hright, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact hclass_single j
    have hleft := closed_lagResp_sum_left cert γstar CSig Fp S hS hCSig
      (classDiag S.μ (S.μ i)) (fun _ : Fin n => (1 : ℝ)) ϱ hϱ
    have hsum :
        (∑ k : Fin m, classDiag S.μ (S.μ i) k *
            lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (Pi.single k 1) (fun _ : Fin n => 1)
              (omegaF ϱ) (omegaF ϱ)) =
          r * lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (Pi.single i 1) (fun _ : Fin n => 1)
            (omegaF ϱ) (omegaF ϱ) := by
      calc
        _ = ∑ k ∈ Finset.univ.filter (fun k => S.μ k = S.μ i),
              lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (Pi.single k 1) (fun _ : Fin n => 1)
                (omegaF ϱ) (omegaF ϱ) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro k _
            by_cases hk : S.μ k = S.μ i <;> simp [classDiag, hk]
        _ = ∑ k' ∈ Finset.univ.filter (fun k => S.μ k = S.μ i),
              lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (Pi.single i 1) (fun _ : Fin n => 1)
                (omegaF ϱ) (omegaF ϱ) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact closed_lagResp_single_left_eq cert γstar CSig Fp S k i
              (Finset.mem_filter.mp hk).2 (fun _ : Fin n => 1) ϱ
        _ = _ := by simp [r]
    rw [hsum] at hleft
    have hrow := hmarg.1 i
    unfold lagRowBar at hrow
    have heq := hleft.symm.trans hresp
    field_simp [ne_of_gt hr, ne_of_gt hB] at heq hrow ⊢
    nlinarith
  · intro l hl
    obtain ⟨j, rfl⟩ := hl
    let t : ℝ := ((Finset.univ.filter fun k => S.lam k = S.lam j).card : ℝ)
    have ht : 0 < t := by
      dsimp [t]
      have hj : j ∈ Finset.univ.filter (fun k => S.lam k = S.lam j) := by simp
      exact_mod_cast Finset.card_pos.mpr ⟨j, hj⟩
    have hsingle_class : ∀ i : Fin m,
        lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (Pi.single i 1) (classDiag S.lam (S.lam j))
            (omegaF ϱ) (omegaF ϱ) =
          t / (B : ℝ) ^ 2 * closedModeCl P Fp.C B Fp.β 0 g (S.μ i) (S.lam j) ϱ := by
      intro i
      let r : ℝ := ((Finset.univ.filter fun k => S.μ k = S.μ i).card : ℝ)
      have hr : 0 < r := by
        dsimp [r]
        have hi : i ∈ Finset.univ.filter (fun k => S.μ k = S.μ i) := by simp
        exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩
      have hlin := closed_lagResp_sum_left cert γstar CSig Fp S hS hCSig
        (classDiag S.μ (S.μ i)) (classDiag S.lam (S.lam j)) ϱ hϱ
      have hsum :
          (∑ k : Fin m, classDiag S.μ (S.μ i) k *
              lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (Pi.single k 1)
                (classDiag S.lam (S.lam j)) (omegaF ϱ) (omegaF ϱ)) =
            r * lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (Pi.single i 1)
              (classDiag S.lam (S.lam j)) (omegaF ϱ) (omegaF ϱ) := by
        calc
          _ = ∑ k ∈ Finset.univ.filter (fun k => S.μ k = S.μ i),
                lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (Pi.single k 1)
                  (classDiag S.lam (S.lam j)) (omegaF ϱ) (omegaF ϱ) := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro k _
              by_cases hk : S.μ k = S.μ i <;> simp [classDiag, hk]
          _ = ∑ k' ∈ Finset.univ.filter (fun k => S.μ k = S.μ i),
                lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (Pi.single i 1)
                  (classDiag S.lam (S.lam j)) (omegaF ϱ) (omegaF ϱ) := by
              apply Finset.sum_congr rfl
              intro k hk
              exact closed_lagResp_single_left_eq cert γstar CSig Fp S k i
                (Finset.mem_filter.mp hk).2 (classDiag S.lam (S.lam j)) ϱ
          _ = _ := by simp [r]
      rw [hsum] at hlin
      have hmode := (cor_app_vol_closed_modes_i cert γstar CSig Fp S hS hCSig 0
        (Ω := Ω) (P := P) (g := g) hg
        (S.μ i) (S.lam j) ⟨i, rfl⟩ ⟨j, rfl⟩ ϱ hϱ).2.2.1
      rw [hmode] at hlin
      dsimp [r, t] at hlin ⊢
      field_simp [ne_of_gt hr] at hlin ⊢
      nlinarith
    have hleft := closed_lagResp_sum_left cert γstar CSig Fp S hS hCSig
      (fun _ : Fin m => (1 : ℝ)) (classDiag S.lam (S.lam j)) ϱ hϱ
    simp only [one_mul] at hleft
    have hresp :
        lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (fun _ : Fin m => 1)
            (classDiag S.lam (S.lam j)) (omegaF ϱ) (omegaF ϱ) =
          t / (B : ℝ) ^ 2 *
            ∑ i : Fin m, closedModeCl P Fp.C B Fp.β 0 g (S.μ i) (S.lam j) ϱ := by
      rw [hleft, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact hsingle_class i
    have hright := closed_lagResp_sum_right cert γstar CSig Fp S hS hCSig
      (fun _ : Fin m => (1 : ℝ)) (classDiag S.lam (S.lam j)) ϱ hϱ
    have hsum :
        (∑ k : Fin n, classDiag S.lam (S.lam j) k *
            lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (fun _ : Fin m => 1) (Pi.single k 1)
              (omegaF ϱ) (omegaF ϱ)) =
          t * lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (fun _ : Fin m => 1) (Pi.single j 1)
            (omegaF ϱ) (omegaF ϱ) := by
      calc
        _ = ∑ k ∈ Finset.univ.filter (fun k => S.lam k = S.lam j),
              lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (fun _ : Fin m => 1) (Pi.single k 1)
                (omegaF ϱ) (omegaF ϱ) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro k _
            by_cases hk : S.lam k = S.lam j <;> simp [classDiag, hk]
        _ = ∑ k' ∈ Finset.univ.filter (fun k => S.lam k = S.lam j),
              lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (fun _ : Fin m => 1) (Pi.single j 1)
                (omegaF ϱ) (omegaF ϱ) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact closed_lagResp_single_right_eq cert γstar CSig Fp S (fun _ : Fin m => 1) k j
              (Finset.mem_filter.mp hk).2 ϱ
        _ = _ := by simp [t]
    rw [hsum] at hright
    have hcol := hmarg.2 j
    have heq := hright.symm.trans hresp
    field_simp [ne_of_gt ht, ne_of_gt hB] at heq hcol ⊢
    nlinarith

/-- `cor:app-vol-marginals`, spectral form (`eqn:app-vol-marginals`), snapshot `cr-2026-10-23`.
Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

\begin{corollary}[Same-step marginals]\label{cor:app-vol-marginals}
Fix a finite dimension and $\ridge>0$. For every row $i$ and every column $j$,
\begin{equation}\label{eqn:app-vol-marginals-tests}
B\,\overline C_0[u_i\tensor u_i,\Id](\ridge,\ridge)=\volraw_i(\ridge),\qquad
B\,\overline C_0[\Id,v_j\tensor v_j](\ridge,\ridge)=\widetilde{\mathfrak v}^{(0)}_j(\ridge),
\end{equation}
and, for every eigenvalue $\mu$ of $\Sigmaout$ and every eigenvalue $\lambda$ of $\Sigmain$,
\begin{equation}\label{eqn:app-vol-marginals}
\frac1B\sum_{j=1}^{\Nin}\mathfrak c_0(\mu,\lambda_j;\ridge)=\frac{\tilde s_1(-\ridge)\,\mu}{\ridge+\tilde s_1(-\ridge)\,\mu},\qquad
\frac1B\sum_{i=1}^{\Nout}\mathfrak c_0(\mu_i,\lambda;\ridge)=\frac{s_1(-\ridge)\,\lambda}{\ridge+s_1(-\ridge)\,\lambda} .
\end{equation}
\end{corollary} 
Relocated here from `Muon.Volatility.Modes` by the coordinator (2026-10-24): its proof needs results of this
module, which imports the original one. -/
theorem cor_app_vol_marginals_spectral (cert : Muon.External.GaussianOpNorm)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (g : ℕ ⊕ Fin 0 → Ω → ℝ) (hg : IsStdGaussianFamily P g)
    (γstar CSig : ℝ) {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut Fp.C B) (hν' : (ν' : Measure ℝ) = Muon.nuIn Fp.C B)
    (ϱ : ℝ) (hϱ : 0 < ϱ) :
    (∀ μ ∈ Set.range S.μ,
        (B : ℝ)⁻¹ * (∑ j : Fin n, closedModeCl P Fp.C B Fp.β 0 g μ (S.lam j) ϱ) =
          volraw Fp.β ν ν' μ ϱ) ∧
      (∀ l ∈ Set.range S.lam,
        (B : ℝ)⁻¹ * (∑ i : Fin m, closedModeCl P Fp.C B Fp.β 0 g (S.μ i) l ϱ) =
          volTildeZero Fp.β ν ν' l ϱ) :=
  closed_marginals_spectral_of_cert cert P g hg γstar CSig Fp S hS hCSig ν ν' hν hν' ϱ hϱ

private lemma closed_lagResp_sum_left_general (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f g : ℝ → ℝ)
    (hf : IsOddBddLip f) (hg : IsOddBddLip g) :
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f g =
      ∑ i, Fd i * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1) Gd f g := by
  obtain ⟨-, hlin, -⟩ := thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS
    hCSig ℓ f g hf hg
  have h0 : lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (fun _ => (0 : ℝ)) Gd f g = 0 := by
    have h := hlin 1 (fun _ => 0) (fun _ => 0) Gd
    simp only [mul_zero, zero_add, one_mul] at h
    linarith
  have step : ∀ t : Finset (Fin m),
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam
          (fun j => ∑ i ∈ t, Fd i * (Pi.single i 1 : Fin m → ℝ) j) Gd f g =
        ∑ i ∈ t, Fd i * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam
          (Pi.single i 1) Gd f g := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using h0
    | insert k t hk ih =>
      have h := hlin (Fd k) (Pi.single k 1)
        (fun j => ∑ i ∈ t, Fd i * (Pi.single i 1 : Fin m → ℝ) j) Gd
      simp only [Finset.sum_insert hk]
      rw [h, ih]
  have h := step Finset.univ
  have hfun :
      (fun j => ∑ i ∈ (Finset.univ : Finset (Fin m)),
        Fd i * (Pi.single i 1 : Fin m → ℝ) j) = Fd := by
    funext j
    simp [Pi.single_apply]
  rwa [hfun] at h

private lemma closed_lagResp_sum_right_general (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f g : ℝ → ℝ)
    (hf : IsOddBddLip f) (hg : IsOddBddLip g) :
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f g =
      ∑ j, Gd j * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd (Pi.single j 1) f g := by
  obtain ⟨-, -, hlin, -⟩ := thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS
    hCSig ℓ f g hf hg
  have h0 : lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd (fun _ => (0 : ℝ)) f g = 0 := by
    have h := hlin 1 Fd (fun _ => 0) (fun _ => 0)
    simp only [mul_zero, zero_add, one_mul] at h
    linarith
  have step : ∀ t : Finset (Fin n),
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd
          (fun k => ∑ j ∈ t, Gd j * (Pi.single j 1 : Fin n → ℝ) k) f g =
        ∑ j ∈ t, Gd j * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam
          Fd (Pi.single j 1) f g := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using h0
    | insert k t hk ih =>
      have h := hlin (Gd k) Fd (Pi.single k 1)
        (fun j => ∑ i ∈ t, Gd i * (Pi.single i 1 : Fin n → ℝ) j)
      simp only [Finset.sum_insert hk]
      rw [h, ih]
  have h := step Finset.univ
  have hfun :
      (fun k => ∑ j ∈ (Finset.univ : Finset (Fin n)),
        Gd j * (Pi.single j 1 : Fin n → ℝ) k) = Gd := by
    funext k
    simp [Pi.single_apply]
  rwa [hfun] at h

private lemma closed_lagResp_single_left_eq_general (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (ℓ : ℕ) (i i' : Fin m) (hi : S.μ i = S.μ i') (Gd : Fin n → ℝ)
    (f g : ℝ → ℝ) :
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1) Gd f g =
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i' 1) Gd f g := by
  unfold lagResp lagRespCut treeRespExt def_app_vol_tree treeMono treeClassFactor
  have key : ∀ q r : ℕ, ∑ k : Fin m, S.μ k ^ q * (Pi.single i (1 : ℝ) : Fin m → ℝ) k ^ r =
      ∑ k : Fin m, S.μ k ^ q * (Pi.single i' (1 : ℝ) : Fin m → ℝ) k ^ r := by
    intro q r
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      simp
    · have hs : ∀ j : Fin m,
          ∑ k : Fin m, S.μ k ^ q * (Pi.single j (1 : ℝ) : Fin m → ℝ) k ^ r = S.μ j ^ q := by
        intro j
        rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk
          simp [Pi.single_apply, hk, hr.ne']
        · intro hj
          exact absurd (Finset.mem_univ j) hj
      rw [hs i, hs i', hi]
  simp only [key]

private lemma closed_lagResp_single_right_eq_general (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (ℓ : ℕ) (Fd : Fin m → ℝ) (j j' : Fin n) (hj : S.lam j = S.lam j')
    (f g : ℝ → ℝ) :
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd (Pi.single j 1) f g =
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd (Pi.single j' 1) f g := by
  unfold lagResp lagRespCut treeRespExt def_app_vol_tree treeMono treeClassFactor
  have key : ∀ q r : ℕ, ∑ k : Fin n, S.lam k ^ q * (Pi.single j (1 : ℝ) : Fin n → ℝ) k ^ r =
      ∑ k : Fin n, S.lam k ^ q * (Pi.single j' (1 : ℝ) : Fin n → ℝ) k ^ r := by
    intro q r
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      simp
    · have hs : ∀ l : Fin n,
          ∑ k : Fin n, S.lam k ^ q * (Pi.single l (1 : ℝ) : Fin n → ℝ) k ^ r = S.lam l ^ q := by
        intro l
        rw [Finset.sum_eq_single l]
        · simp
        · intro k _ hk
          simp [Pi.single_apply, hk, hr.ne']
        · intro hl
          exact absurd (Finset.mem_univ l) hl
      rw [hs j, hs j', hj]
  simp only [key]

private lemma closed_lagResp_single_mode (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ℓ : ℕ) {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (i : Fin m) (j : Fin n) (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1) (Pi.single j 1)
        (iotaF s) (iotaF u) =
      (B : ℝ) ^ (-2 : ℤ) * closedModeH P Fp.C B Fp.β ℓ g (S.μ i) (S.lam j) s u := by
  let r : ℝ := ((Finset.univ.filter fun k => S.μ k = S.μ i).card : ℝ)
  let t : ℝ := ((Finset.univ.filter fun k => S.lam k = S.lam j).card : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast Finset.card_pos.mpr ⟨i, by simp⟩
  have ht : 0 < t := by
    dsimp [t]
    exact_mod_cast Finset.card_pos.mpr ⟨j, by simp⟩
  have hf := (lem_app_vol_sharp_ii hs hs).1
  have hfu := (lem_app_vol_sharp_ii hu hu).1
  have hleft := closed_lagResp_sum_left_general cert γstar CSig Fp S hS hCSig ℓ
    (classDiag S.μ (S.μ i)) (classDiag S.lam (S.lam j)) (iotaF s) (iotaF u) hf hfu
  have hsumleft :
      (∑ k : Fin m, classDiag S.μ (S.μ i) k *
          lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single k 1)
            (classDiag S.lam (S.lam j)) (iotaF s) (iotaF u)) =
        r * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1)
          (classDiag S.lam (S.lam j)) (iotaF s) (iotaF u) := by
    calc
      _ = ∑ k ∈ Finset.univ.filter (fun k => S.μ k = S.μ i),
            lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single k 1)
              (classDiag S.lam (S.lam j)) (iotaF s) (iotaF u) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro k _
          by_cases hk : S.μ k = S.μ i <;> simp [classDiag, hk]
      _ = ∑ k' ∈ Finset.univ.filter (fun k => S.μ k = S.μ i),
            lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1)
              (classDiag S.lam (S.lam j)) (iotaF s) (iotaF u) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact closed_lagResp_single_left_eq_general cert γstar CSig Fp S ℓ k i
            (Finset.mem_filter.mp hk).2 (classDiag S.lam (S.lam j)) (iotaF s) (iotaF u)
      _ = _ := by simp [r]
  rw [hsumleft] at hleft
  have hright := closed_lagResp_sum_right_general cert γstar CSig Fp S hS hCSig ℓ
    (Pi.single i 1) (classDiag S.lam (S.lam j)) (iotaF s) (iotaF u) hf hfu
  have hsumright :
      (∑ k : Fin n, classDiag S.lam (S.lam j) k *
          lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1)
            (Pi.single k 1) (iotaF s) (iotaF u)) =
        t * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1)
          (Pi.single j 1) (iotaF s) (iotaF u) := by
    calc
      _ = ∑ k ∈ Finset.univ.filter (fun k => S.lam k = S.lam j),
            lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1)
              (Pi.single k 1) (iotaF s) (iotaF u) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro k _
          by_cases hk : S.lam k = S.lam j <;> simp [classDiag, hk]
      _ = ∑ k' ∈ Finset.univ.filter (fun k => S.lam k = S.lam j),
            lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1)
              (Pi.single j 1) (iotaF s) (iotaF u) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact closed_lagResp_single_right_eq_general cert γstar CSig Fp S ℓ
            (Pi.single i 1) k j (Finset.mem_filter.mp hk).2 (iotaF s) (iotaF u)
      _ = _ := by simp [t]
  rw [hsumright] at hright
  have hmode := (cor_app_vol_closed_modes_i cert γstar CSig Fp S hS hCSig ℓ hg
    (S.μ i) (S.lam j) ⟨i, rfl⟩ ⟨j, rfl⟩ 1 one_pos).2.1 s u hs hu
  rw [hleft, hright] at hmode
  have hB : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  dsimp [r, t] at hmode ⊢
  field_simp [ne_of_gt hr, ne_of_gt ht, ne_of_gt hB] at hmode ⊢
  nlinarith

private lemma closed_trace_two_resolvents {d : ℕ}
    (A U : Matrix (Fin d) (Fin d) ℝ) (v w : Fin d → ℝ)
    (hU : Uᵀ * U = 1) (hA : A = U * Matrix.diagonal v * Uᵀ)
    (F : Matrix (Fin d) (Fin d) ℝ) (hF : F = U * Matrix.diagonal w * Uᵀ)
    (s a u c : ℝ) (hs : ∀ i, s + a * v i ≠ 0) (hu : ∀ i, u + c * v i ≠ 0) :
    (F * A * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • A)⁻¹ *
      (u • (1 : Matrix (Fin d) (Fin d) ℝ) + c • A)⁻¹).trace =
        ∑ i, w i * v i / ((s + a * v i) * (u + c * v i)) := by
  classical
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hinv : ∀ (t b : ℝ), (∀ i, t + b * v i ≠ 0) →
      (t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • A)⁻¹ =
        U * Matrix.diagonal (fun i => (t + b * v i)⁻¹) * Uᵀ := by
    intro t b hden
    have he : Matrix.diagonal (fun i => t + b * v i) =
        t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • Matrix.diagonal v := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
    have hfac : t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • A =
        U * Matrix.diagonal (fun i => t + b * v i) * Uᵀ := by
      rw [he, Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU, ← hA]
    have hdiag : Matrix.diagonal (fun i => t + b * v i) *
        Matrix.diagonal (fun i => (t + b * v i)⁻¹) = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij, hden]
    apply Matrix.inv_eq_right_inv
    rw [hfac]
    calc U * Matrix.diagonal (fun i => t + b * v i) * Uᵀ *
          (U * Matrix.diagonal (fun i => (t + b * v i)⁻¹) * Uᵀ) =
        U * (Matrix.diagonal (fun i => t + b * v i) *
          Matrix.diagonal (fun i => (t + b * v i)⁻¹)) * Uᵀ := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
      _ = 1 := by rw [hdiag, Matrix.mul_one, hUU]
  rw [hinv s a hs, hinv u c hu, hA, hF]
  calc
    (U * Matrix.diagonal w * Uᵀ * (U * Matrix.diagonal v * Uᵀ) *
        (U * Matrix.diagonal (fun i => (s + a * v i)⁻¹) * Uᵀ) *
        (U * Matrix.diagonal (fun i => (u + c * v i)⁻¹) * Uᵀ)).trace =
      (U * (Matrix.diagonal w * Matrix.diagonal v *
        Matrix.diagonal (fun i => (s + a * v i)⁻¹) *
        Matrix.diagonal (fun i => (u + c * v i)⁻¹)) * Uᵀ).trace := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul,
            ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul,
            ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
    _ = (Matrix.diagonal w * Matrix.diagonal v *
        Matrix.diagonal (fun i => (s + a * v i)⁻¹) *
        Matrix.diagonal (fun i => (u + c * v i)⁻¹)).trace := by
          rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    _ = _ := by
      simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, div_eq_mul_inv]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_inv]
      ring

private lemma closed_profileKernel_mode_sum (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ℓ : ℕ) {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    profileKernel P Fp.C B (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g) Fm Gm s u =
      ∑ i, ∑ j, Fd i * Gd j * (B : ℝ) ^ (-2 : ℤ) *
        closedModeH P Fp.C B Fp.β ℓ g (S.μ i) (S.lam j) s u := by
  let x := branchPt (profileF P (emaXi₁ Fp.β ℓ g)) Fp.C B s
  let y := branchPt (profileF P (emaXi₂ Fp.β ℓ g)) Fp.C B u
  have hp := lem_app_vol_closed_profile_iv Fp.hβ.1 Fp.hβ.2 hg
  have hx := closed_branch_spec Fp.hB hp.2.2.2.2.2.profile₁ Fp.C hout hin γstar
    (by simpa only [Nat.cast_max] using hS.1) hs
  have hy := closed_branch_spec Fp.hB hp.2.2.2.2.2.profile₂ Fp.C hout hin γstar
    (by simpa only [Nat.cast_max] using hS.1) hu
  have hso : ∀ i, s + x.2.2.1 * S.μ i ≠ 0 := fun i => ne_of_gt
    (add_pos_of_pos_of_nonneg hs (mul_nonneg hx.2.2.2.1.le (μ_nonneg S i)))
  have huo : ∀ i, u + y.2.2.1 * S.μ i ≠ 0 := fun i => ne_of_gt
    (add_pos_of_pos_of_nonneg hu (mul_nonneg hy.2.2.2.1.le (μ_nonneg S i)))
  have hsi : ∀ j, s + x.2.2.2 * S.lam j ≠ 0 := fun j => ne_of_gt
    (add_pos_of_pos_of_nonneg hs (mul_nonneg hx.2.2.2.2.le (lam_nonneg S j)))
  have hui : ∀ j, u + y.2.2.2 * S.lam j ≠ 0 := fun j => ne_of_gt
    (add_pos_of_pos_of_nonneg hu (mul_nonneg hy.2.2.2.2.le (lam_nonneg S j)))
  have hB : (B : ℝ) ≠ 0 := by exact_mod_cast Fp.hB.ne'
  have hBpow : (B : ℝ) ^ (-2 : ℤ) = (B : ℝ)⁻¹ ^ 2 := by
    norm_num [_root_.zpow_neg]
  have hdelta : profileDelta P Fp.C B (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g) s u ≠ 0 :=
    ne_of_gt (thm_app_vol_closed_kernel_i γstar CSig Fp.C Fp.hB hS
      Fp.hβ.1 Fp.hβ.2 ℓ hg s u hs hu).1
  have hto : toutT Fp.C B x y s u Fm =
      (B : ℝ)⁻¹ * ∑ i, Fd i * S.μ i /
        ((s + x.2.2.1 * S.μ i) * (u + y.2.2.1 * S.μ i)) := by
    unfold toutT
    rw [closed_trace_two_resolvents Fp.C.Sout S.uOut S.μ Fd S.huOut
      (Sout_eq_spectral S) Fm hFd s x.2.2.1 u y.2.2.1 hso huo]
  have hti : tinT Fp.C B x y s u Gm =
      (B : ℝ)⁻¹ * ∑ j, Gd j * S.lam j /
        ((s + x.2.2.2 * S.lam j) * (u + y.2.2.2 * S.lam j)) := by
    unfold tinT
    rw [closed_trace_two_resolvents Fp.C.Sin S.vIn S.lam Gd S.hvIn
      (Sin_eq_spectral S) Gm hGd s x.2.2.2 u y.2.2.2 hsi hui]
  change s * u * pairedB P (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g)
      (s * x.1 * x.2.1) (u * y.1 * y.2.1) * toutT Fp.C B x y s u Fm *
        tinT Fp.C B x y s u Gm /
          profileDelta P Fp.C B (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g) s u = _
  rw [hto, hti]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [closedModeH, x, y]
  rw [hBpow]
  simp only [div_eq_mul_inv, mul_inv]
  ring

private lemma closed_lagResp_mode_sum (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ℓ : ℕ) {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u) =
      ∑ i, ∑ j, Fd i * Gd j * (B : ℝ) ^ (-2 : ℤ) *
        closedModeH P Fp.C B Fp.β ℓ g (S.μ i) (S.lam j) s u := by
  have hf := (lem_app_vol_sharp_ii hs hs).1
  have hfu := (lem_app_vol_sharp_ii hu hu).1
  rw [closed_lagResp_sum_left_general cert γstar CSig Fp S hS hCSig ℓ
    Fd Gd (iotaF s) (iotaF u) hf hfu]
  apply Finset.sum_congr rfl
  intro i _
  rw [closed_lagResp_sum_right_general cert γstar CSig Fp S hS hCSig ℓ
    (Pi.single i 1) Gd (iotaF s) (iotaF u) hf hfu, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [closed_lagResp_single_mode cert γstar CSig Fp S hS hCSig ℓ hg i j s u hs hu]
  ring

theorem thm_app_vol_closed_kernel_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (ℓ : ℕ)
    {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ) (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    Tendsto (fun p : ℕ × ℝ =>
        lagRespCut cert γstar CSig Fp.β ℓ p.1 p.2 B S.μ S.lam Fd Gd (iotaF s) (iotaF u))
      (atTop ×ˢ atTop : Filter (ℕ × ℝ))
      (𝓝 (lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u))) ∧
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u) =
      profileKernel P Fp.C B (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g) Fm Gm s u := by
  have hlim := thm_app_vol_lag_kernel_exists cert γstar CSig Fp S hS hCSig ℓ
    Fm Gm Fd Gd hFd hGd (iotaF s) (iotaF u)
      (lem_app_vol_sharp_ii hs hs).1 (lem_app_vol_sharp_ii hu hu).1
  refine ⟨hlim, ?_⟩
  by_cases hC : Fp.C.Sout = 0 ∨ Fp.C.Sin = 0
  · have hz : (fun p : ℕ × ℝ =>
        lagRespCut cert γstar CSig Fp.β ℓ p.1 p.2 B S.μ S.lam Fd Gd (iotaF s) (iotaF u)) =
        fun _ => 0 := by
      funext p
      exact closed_cutoff_degenerate cert γstar CSig Fp S hC ℓ p.1 p.2 Fd Gd (iotaF s) (iotaF u)
    rw [hz] at hlim
    have hzero : lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u) = 0 :=
      tendsto_nhds_unique hlim tendsto_const_nhds
    rw [hzero, closed_profileKernel_degenerate Fp.C P _ _ hC Fm Gm s u]
  · rw [closed_lagResp_mode_sum cert γstar CSig Fp S hS hCSig ℓ hg Fd Gd s u hs hu,
      closed_profileKernel_mode_sum γstar CSig Fp S hS
        (fun h => hC (Or.inl h)) (fun h => hC (Or.inr h)) ℓ hg Fm Gm Fd Gd hFd hGd s u hs hu]

private lemma closed_bounds_qhat_bdd {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (γ : ℝ) :
    BddAbove {q : ℝ | 0 ≤ q ∧ Muon.DetEquiv.rW (Muon.emaW β) q ≤ γ} := by
  have hw : WeightSeq (Muon.emaW β) :=
    (Muon.Drift.emaW_weightClass β ⟨hβ0.le, hβ1⟩).1
  have h := (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.2.2.2.2.2
  have hset : {j : ℕ | 0 < Muon.emaW β j} = Set.univ := by
    ext j
    simp only [mem_setOf_eq, mem_univ, iff_true]
    unfold Muon.emaW
    exact mul_pos (by linarith) (pow_pos hβ0 j)
  rw [hset, Set.encard_univ] at h
  have htop : (ENat.card ℕ).toENNReal = ⊤ := by simp
  rw [htop] at h
  have hev := h.eventually_const_lt (ENNReal.ofReal_lt_top (r := γ))
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 hev
  refine ⟨Q, fun q hq => ?_⟩
  by_contra hlt
  push_neg at hlt
  have h1 := hQ q hlt.le
  have h2 := (ENNReal.ofReal_lt_ofReal_iff'.1 h1).1
  linarith [hq.2]

private lemma closed_bounds_trace_one {d : ℕ} (A U : Mat d d) (v : Fin d → ℝ)
    (hU : Uᵀ * U = 1) (hA : A = U * Matrix.diagonal v * Uᵀ)
    (s a : ℝ) (hs : ∀ i, s + a * v i ≠ 0) :
    (A * (s • (1 : Mat d d) + a • A)⁻¹).trace = ∑ i, v i / (s + a * v i) := by
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have h := closed_bounds_trace_two_resolvents A U v (fun _ => 1) hU hA 1
    (by rw [Matrix.diagonal_one, Matrix.mul_one, hUU]) s a 1 0 hs (by intro i; simp)
  simpa using h

private lemma closed_bounds_sum_cs {d B : ℕ} (hB : 0 < B) (v : Fin d → ℝ)
    (hv : ∀ i, 0 ≤ v i) {s u a c : ℝ} (hs : 0 < s) (hu : 0 < u)
    (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (B : ℝ)⁻¹ * ∑ i, v i / ((s + a * v i) * (u + c * v i)) ≤
      Real.sqrt (((B : ℝ)⁻¹ * ∑ i, v i / ((s + a * v i) ^ 2)) *
        ((B : ℝ)⁻¹ * ∑ i, v i / ((u + c * v i) ^ 2))) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hB0 : 0 ≤ (B : ℝ)⁻¹ := inv_nonneg.2 hBr.le
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => Real.sqrt (v i) / (s + a * v i))
    (fun i => Real.sqrt (v i) / (u + c * v i))
  have e1 : ∀ i, v i / ((s + a * v i) * (u + c * v i)) =
      (Real.sqrt (v i) / (s + a * v i)) * (Real.sqrt (v i) / (u + c * v i)) := by
    intro i
    rw [div_mul_div_comm, Real.mul_self_sqrt (hv i)]
  have e2 : ∀ i, (Real.sqrt (v i) / (s + a * v i)) ^ 2 =
      v i / (s + a * v i) ^ 2 := by
    intro i
    rw [div_pow, Real.sq_sqrt (hv i)]
  have e3 : ∀ i, (Real.sqrt (v i) / (u + c * v i)) ^ 2 =
      v i / (u + c * v i) ^ 2 := by
    intro i
    rw [div_pow, Real.sq_sqrt (hv i)]
  simp_rw [← e1, e2, e3] at h
  have hf : 0 ≤ ∑ i, v i / (s + a * v i) ^ 2 :=
    Finset.sum_nonneg fun i _ => div_nonneg (hv i) (sq_nonneg _)
  have hg : 0 ≤ ∑ i, v i / (u + c * v i) ^ 2 :=
    Finset.sum_nonneg fun i _ => div_nonneg (hv i) (sq_nonneg _)
  have hprod : ((B : ℝ)⁻¹ * ∑ i, v i / (s + a * v i) ^ 2) *
      ((B : ℝ)⁻¹ * ∑ i, v i / (u + c * v i) ^ 2) =
      ((B : ℝ)⁻¹) ^ 2 *
        ((∑ i, v i / (s + a * v i) ^ 2) * ∑ i, v i / (u + c * v i) ^ 2) := by ring
  rw [hprod, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB0, Real.sqrt_mul hf]
  exact mul_le_mul_of_nonneg_left h hB0

private lemma closed_bounds_sum_diag {d B : ℕ} (hB : 0 < B) (v : Fin d → ℝ)
    (hv : ∀ i, 0 ≤ v i) {s a σ : ℝ} (hs : 0 < s) (ha : 0 ≤ a)
    (hσ : σ = (B : ℝ)⁻¹ * ∑ i, v i / (s + a * v i)) :
    (B : ℝ)⁻¹ * ∑ i, v i / (s + a * v i) ^ 2 ≤ σ / s := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  rw [hσ]
  have hsum : ∑ i, v i / (s + a * v i) ^ 2 ≤
      (1 / s) * ∑ i, v i / (s + a * v i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hd : 0 < s + a * v i := add_pos_of_pos_of_nonneg hs (mul_nonneg ha (hv i))
    rw [div_le_iff₀ (sq_pos_of_pos hd)]
    field_simp [ne_of_gt hs, ne_of_gt hd]
    nlinarith [mul_nonneg ha (sq_nonneg (v i))]
  calc
    (B : ℝ)⁻¹ * ∑ i, v i / (s + a * v i) ^ 2 ≤
        (B : ℝ)⁻¹ * ((1 / s) * ∑ i, v i / (s + a * v i)) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hBr.le)
    _ = ((B : ℝ)⁻¹ * ∑ i, v i / (s + a * v i)) / s := by ring

private lemma closed_bounds_trace_sqrt {d B : ℕ} (hB : 0 < B)
    (A U : Mat d d) (v w : Fin d → ℝ) (hU : Uᵀ * U = 1)
    (hA : A = U * Matrix.diagonal v * Uᵀ) (F : Mat d d)
    (hF : F = U * Matrix.diagonal w * Uᵀ) (hv : ∀ i, 0 ≤ v i)
    (x y : ℝ × ℝ × ℝ × ℝ) (s a u c σ τ : ℝ)
    (hs : 0 < s) (ha : 0 ≤ a) (hu : 0 < u) (hc : 0 ≤ c)
    (hσ : σ = (B : ℝ)⁻¹ * (A * (s • (1 : Mat d d) + a • A)⁻¹).trace)
    (hτ : τ = (B : ℝ)⁻¹ * (A * (u • (1 : Mat d d) + c • A)⁻¹).trace) :
    |(B : ℝ)⁻¹ * (F * A * (s • (1 : Mat d d) + a • A)⁻¹ *
      (u • (1 : Mat d d) + c • A)⁻¹).trace| ≤
      opNorm F * Real.sqrt ((σ / s) * (τ / u)) := by
  have hsr : ∀ i, 0 < s + a * v i := fun i =>
    add_pos_of_pos_of_nonneg hs (mul_nonneg ha (hv i))
  have hur : ∀ i, 0 < u + c * v i := fun i =>
    add_pos_of_pos_of_nonneg hu (mul_nonneg hc (hv i))
  rw [closed_bounds_trace_two_resolvents A U v w hU hA F hF s a u c
    (fun i => (hsr i).ne') (fun i => (hur i).ne')]
  have hcross0 : 0 ≤ (B : ℝ)⁻¹ * ∑ i, v i / ((s + a * v i) * (u + c * v i)) :=
    mul_nonneg (inv_nonneg.mpr (by exact_mod_cast hB.le : (0 : ℝ) ≤ B))
      (Finset.sum_nonneg fun i _ => div_nonneg (hv i) (mul_nonneg (hsr i).le (hur i).le))
  have habs : |(B : ℝ)⁻¹ * ∑ i, w i * v i /
      ((s + a * v i) * (u + c * v i))| ≤
      opNorm F * ((B : ℝ)⁻¹ * ∑ i, v i / ((s + a * v i) * (u + c * v i))) := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr (by exact_mod_cast hB : (0 : ℝ) < B))]
    have hsum : |∑ i, w i * v i / ((s + a * v i) * (u + c * v i))| ≤
        opNorm F * ∑ i, v i / ((s + a * v i) * (u + c * v i)) := by
      rw [Finset.mul_sum]
      calc
        |∑ i, w i * v i / ((s + a * v i) * (u + c * v i))| ≤
            ∑ i, |w i * v i / ((s + a * v i) * (u + c * v i))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, opNorm F * (v i / ((s + a * v i) * (u + c * v i))) := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_div, abs_mul, abs_of_nonneg (hv i), abs_of_pos (mul_pos (hsr i) (hur i))]
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_right (closed_bounds_diag_abs_le U hU F w hF i)
            (div_nonneg (hv i) (mul_pos (hsr i) (hur i)).le)
    calc
      (B : ℝ)⁻¹ * |∑ i, w i * v i / ((s + a * v i) * (u + c * v i))| ≤
          (B : ℝ)⁻¹ * (opNorm F * ∑ i, v i / ((s + a * v i) * (u + c * v i))) :=
        mul_le_mul_of_nonneg_left hsum
          (inv_nonneg.mpr (by exact_mod_cast hB.le : (0 : ℝ) ≤ B))
      _ = opNorm F * ((B : ℝ)⁻¹ * ∑ i, v i / ((s + a * v i) * (u + c * v i))) := by ring
  have hcs := closed_bounds_sum_cs hB v hv hs hu ha hc
  have hσ' : σ = (B : ℝ)⁻¹ * ∑ i, v i / (s + a * v i) := by
    rw [hσ, closed_bounds_trace_one A U v hU hA s a (fun i => (hsr i).ne')]
  have hτ' : τ = (B : ℝ)⁻¹ * ∑ i, v i / (u + c * v i) := by
    rw [hτ, closed_bounds_trace_one A U v hU hA u c (fun i => (hur i).ne')]
  have hd1 := closed_bounds_sum_diag hB v hv hs ha hσ'
  have hd2 := closed_bounds_sum_diag hB v hv hu hc hτ'
  have hs1 : 0 ≤ (B : ℝ)⁻¹ * ∑ i, v i / (s + a * v i) ^ 2 :=
    mul_nonneg (inv_nonneg.mpr (by exact_mod_cast hB.le : (0 : ℝ) ≤ B))
      (Finset.sum_nonneg fun i _ => div_nonneg (hv i) (sq_nonneg _))
  have hs2 : 0 ≤ (B : ℝ)⁻¹ * ∑ i, v i / (u + c * v i) ^ 2 :=
    mul_nonneg (inv_nonneg.mpr (by exact_mod_cast hB.le : (0 : ℝ) ≤ B))
      (Finset.sum_nonneg fun i _ => div_nonneg (hv i) (sq_nonneg _))
  have ht1 : 0 ≤ σ / s := hs1.trans hd1
  have ht2 : 0 ≤ τ / u := hs2.trans hd2
  calc
    |(B : ℝ)⁻¹ * ∑ i, w i * v i / ((s + a * v i) * (u + c * v i))| ≤
        opNorm F * ((B : ℝ)⁻¹ * ∑ i, v i / ((s + a * v i) * (u + c * v i))) := habs
    _ ≤ opNorm F * Real.sqrt (((B : ℝ)⁻¹ * ∑ i, v i / (s + a * v i) ^ 2) *
          ((B : ℝ)⁻¹ * ∑ i, v i / (u + c * v i) ^ 2)) :=
      mul_le_mul_of_nonneg_left hcs (by unfold opNorm; exact norm_nonneg _)
    _ ≤ opNorm F * Real.sqrt ((σ / s) * (τ / u)) := by
      apply mul_le_mul_of_nonneg_left _ (by unfold opNorm; exact norm_nonneg _)
      exact Real.sqrt_le_sqrt (mul_le_mul hd1 hd2 hs2 ht1)

theorem cor_app_vol_closed_bounds_iii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (hβpos : 0 < Fp.β) (ℓ : ℕ)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ) :
    ∀ s u : ℝ, 0 < s → 0 < u → 1 ≤ ℓ →
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u)| ≤
        4 * Muon.sPow Fp.β 2 * qhatBeta Fp.β γstar * Muon.opNorm Fm * Muon.opNorm Gm *
          Fp.β ^ ℓ / (epsBeta Fp.β γstar ^ 2 * Real.sqrt (s * u)) := by
  intro s u hs hu hℓ
  obtain ⟨P, hP, hg⟩ := closed_bounds_gauss_exists (ℕ ⊕ Fin ℓ)
  letI := hP
  rw [(thm_app_vol_closed_kernel_ii cert γstar CSig Fp S hS hCSig ℓ hg
    Fm Gm Fd Gd hFd hGd s u hs hu).2]
  have hBr : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  have hγ0 : 0 ≤ γstar := by
    have hz : (0 : ℝ) ≤ (max m n : ℕ) := by positivity
    have hsz := hS.1
    nlinarith
  have hbdd := closed_bounds_qhat_bdd hβpos Fp.hβ.2 γstar
  have hqh0 : 0 ≤ qhatBeta Fp.β γstar := by
    unfold qhatBeta
    apply le_csSup hbdd
    refine ⟨le_rfl, ?_⟩
    simp [Muon.DetEquiv.rW, hγ0]
  by_cases hC : Fp.C.Sout = 0 ∨ Fp.C.Sin = 0
  · rw [closed_profileKernel_degenerate Fp.C P _ _ hC Fm Gm s u, abs_zero]
    have hnF : 0 ≤ opNorm Fm := by unfold opNorm; exact norm_nonneg _
    have hnG : 0 ≤ opNorm Gm := by unfold opNorm; exact norm_nonneg _
    have hsp : 0 ≤ Muon.sPow Fp.β 2 := tsum_nonneg fun j => sq_nonneg (Muon.emaW Fp.β j)
    exact div_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
  · have hout : Fp.C.Sout ≠ 0 := fun h => hC (Or.inl h)
    have hin : Fp.C.Sin ≠ 0 := fun h => hC (Or.inr h)
    have hm : 0 < m := by
      by_contra hm
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      subst m
      exact hout (Subsingleton.elim _ _)
    have hγ : 0 < γstar := by
      have hm' : (0 : ℝ) < (max m n : ℕ) := by exact_mod_cast hm.trans_le (le_max_left m n)
      nlinarith [hS.1]
    let x := branchPt (profileF P (emaXi₁ Fp.β ℓ (fun a ω => ω a))) Fp.C B s
    let y := branchPt (profileF P (emaXi₂ Fp.β ℓ (fun a ω => ω a))) Fp.C B u
    have hp := lem_app_vol_closed_profile_iv Fp.hβ.1 Fp.hβ.2 hg
    have hpair := hp.2.2.2.2.2
    have hx := closed_branch_spec Fp.hB hpair.profile₁ Fp.C hout hin γstar
      (by simpa only [Nat.cast_max] using hS.1) hs
    have hy := closed_branch_spec Fp.hB hpair.profile₂ Fp.C hout hin γstar
      (by simpa only [Nat.cast_max] using hS.1) hu
    have hxspec := hx.1
    have hyspec := hy.1
    obtain ⟨hxσ0, hxτ0, hxa0, hxc0, hxσ, hxτ, -, -⟩ := hxspec
    obtain ⟨hyσ0, hyτ0, hya0, hyc0, hyσ, hyτ, -, -⟩ := hyspec
    let q := s * (branchPt (profileF P (emaXi₁ Fp.β ℓ (fun a ω => ω a))) Fp.C B s).1 *
      (branchPt (profileF P (emaXi₁ Fp.β ℓ (fun a ω => ω a))) Fp.C B s).2.1
    let q' := u * (branchPt (profileF P (emaXi₂ Fp.β ℓ (fun a ω => ω a))) Fp.C B u).1 *
      (branchPt (profileF P (emaXi₂ Fp.β ℓ (fun a ω => ω a))) Fp.C B u).2.1
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hq'0 : 0 ≤ q' := by dsimp [q']; positivity
    have hbx := (lem_app_vol_closed_branch_ii Fp.hB hpair.profile₁ hs Fp.C hout hin γstar
      (by simpa only [Nat.cast_max] using hS.1)).2 _ hx.1
    have hby := (lem_app_vol_closed_branch_ii Fp.hB hpair.profile₂ hu Fp.C hout hin γstar
      (by simpa only [Nat.cast_max] using hS.1)).2 _ hy.1
    obtain ⟨-, -, -, -, -, hrx, -, hltx, hlex⟩ := hbx
    obtain ⟨-, -, -, -, -, hry, -, hlty, hley⟩ := hby
    have hr1 : profileR P (emaXi₁ Fp.β ℓ (fun a ω => ω a)) =
        Muon.DetEquiv.rW (Muon.emaW Fp.β) := by
      funext z
      simp only [profileR, Muon.DetEquiv.rW, hp.1]
    have hr2 : profileR P (emaXi₂ Fp.β ℓ (fun a ω => ω a)) =
        Muon.DetEquiv.rW (Muon.emaW Fp.β) := by
      funext z
      simp only [profileR, Muon.DetEquiv.rW, hp.2.1]
    have hqγ : Muon.DetEquiv.rW (Muon.emaW Fp.β) q ≤ γstar := by
      rw [← hr1]
      exact hrx.trans_le (hltx.le.trans hlex)
    have hq'γ : Muon.DetEquiv.rW (Muon.emaW Fp.β) q' ≤ γstar := by
      rw [← hr2]
      exact hry.trans_le (hlty.le.trans hley)
    have hqle : q ≤ qhatBeta Fp.β γstar := by
      unfold qhatBeta
      exact le_csSup hbdd ⟨hq0, hqγ⟩
    have hq'le : q' ≤ qhatBeta Fp.β γstar := by
      unfold qhatBeta
      exact le_csSup hbdd ⟨hq'0, hq'γ⟩
    have hF : Fw (Muon.emaW Fp.β) 0 ≤ 1 := by
      rw [(lem_app_de_scalar_ii ((Muon.Drift.emaW_weightClass Fp.β Fp.hβ).1)).2.2.2.2.2.2.1,
        ← sPow_eq_sumPow_emaW, Muon.sPow_two Fp.hβ.1 Fp.hβ.2]
      exact (div_le_one (by linarith : 0 < 1 + Fp.β)).2 (by linarith)
    have hd0 := lem_app_vol_closed_determinant_iii Fp.hB hβpos Fp.hβ.2 hℓ hg
      Fp.C hout hin γstar hγ (by simpa only [Nat.cast_max] using hS.1)
      (by rw [hp.1]; exact hF) (by rw [hp.2.1]; exact hF)
    have hd : epsBeta Fp.β γstar ^ 2 / 4 ≤
        profileDelta P Fp.C B (emaXi₁ Fp.β ℓ (fun a ω => ω a))
          (emaXi₂ Fp.β ℓ (fun a ω => ω a)) s u :=
      (hd0.2.2 s u hs hu).2.trans (hd0.2.2 s u hs hu).1
    have hdpos := (thm_app_vol_closed_kernel_i γstar CSig Fp.C Fp.hB hS
      Fp.hβ.1 Fp.hβ.2 ℓ hg s u hs hu).1
    have hb := (hp.2.2.2.2.1 q q' hq0 hq'0)
    have hto : |toutT Fp.C B x y s u Fm| ≤ opNorm Fm *
        Real.sqrt ((x.1 / s) * (y.1 / u)) := by
      exact closed_bounds_trace_sqrt Fp.hB Fp.C.Sout S.uOut S.μ Fd S.huOut
        (Sout_eq_spectral S) Fm hFd (μ_nonneg S) x y s x.2.2.1 u y.2.2.1 x.1 y.1
        hs hxa0 hu hya0 hxσ hyσ
    have hti : |tinT Fp.C B x y s u Gm| ≤ opNorm Gm *
        Real.sqrt ((x.2.1 / s) * (y.2.1 / u)) := by
      exact closed_bounds_trace_sqrt Fp.hB Fp.C.Sin S.vIn S.lam Gd S.hvIn
        (Sin_eq_spectral S) Gm hGd (lam_nonneg S) x y s x.2.2.2 u y.2.2.2 x.2.1 y.2.1
        hs hxc0 hu hyc0 hxτ hyτ
    have htr : s * u * |toutT Fp.C B x y s u Fm| * |tinT Fp.C B x y s u Gm| ≤
        opNorm Fm * opNorm Gm * qhatBeta Fp.β γstar / Real.sqrt (s * u) := by
      have hnF : 0 ≤ opNorm Fm := by unfold opNorm; exact norm_nonneg _
      have hnG : 0 ≤ opNorm Gm := by unfold opNorm; exact norm_nonneg _
      have hA0 : 0 ≤ (x.1 / s) * (y.1 / u) := by positivity
      have hC0 : 0 ≤ (x.2.1 / s) * (y.2.1 / u) := by positivity
      have hsu0 : 0 ≤ s * u := (mul_pos hs hu).le
      have hqq0 : 0 ≤ q * q' := mul_nonneg hq0 hq'0
      have hp := mul_le_mul hto hti (abs_nonneg _)
        (mul_nonneg hnF (Real.sqrt_nonneg _))
      have hp' := mul_le_mul_of_nonneg_left hp (mul_nonneg hs.le hu.le)
      have hsqrtq : Real.sqrt (q * q') ≤ qhatBeta Fp.β γstar := by
        have hmul := mul_le_mul hqle hq'le hq'0 hqh0
        calc
          Real.sqrt (q * q') ≤ Real.sqrt (qhatBeta Fp.β γstar * qhatBeta Fp.β γstar) :=
            Real.sqrt_le_sqrt hmul
          _ = qhatBeta Fp.β γstar := by
            rw [← sq, Real.sqrt_sq hqh0]
      have hsqrtid : s * u * Real.sqrt ((x.1 / s) * (y.1 / u)) *
          Real.sqrt ((x.2.1 / s) * (y.2.1 / u)) =
          Real.sqrt (q * q') / Real.sqrt (s * u) := by
        have hL0 : 0 ≤ s * u * Real.sqrt ((x.1 / s) * (y.1 / u)) *
            Real.sqrt ((x.2.1 / s) * (y.2.1 / u)) := by positivity
        have hR0 : 0 ≤ Real.sqrt (q * q') / Real.sqrt (s * u) := by positivity
        apply (sq_eq_sq₀ hL0 hR0).mp
        rw [div_pow, Real.sq_sqrt hqq0, Real.sq_sqrt hsu0]
        rw [show (s * u * Real.sqrt ((x.1 / s) * (y.1 / u)) *
            Real.sqrt ((x.2.1 / s) * (y.2.1 / u))) ^ 2 =
            (s * u) ^ 2 * Real.sqrt ((x.1 / s) * (y.1 / u)) ^ 2 *
              Real.sqrt ((x.2.1 / s) * (y.2.1 / u)) ^ 2 by ring,
          Real.sq_sqrt hA0, Real.sq_sqrt hC0]
        have hqeq : q = s * x.1 * x.2.1 := rfl
        have hq'eq : q' = u * y.1 * y.2.1 := rfl
        rw [hqeq, hq'eq]
        field_simp [ne_of_gt hs, ne_of_gt hu]
      calc
        s * u * |toutT Fp.C B x y s u Fm| * |tinT Fp.C B x y s u Gm| ≤
            s * u * ((opNorm Fm * Real.sqrt ((x.1 / s) * (y.1 / u))) *
              (opNorm Gm * Real.sqrt ((x.2.1 / s) * (y.2.1 / u)))) := by
          simpa only [mul_assoc] using hp'
        _ = opNorm Fm * opNorm Gm *
              (Real.sqrt (q * q') / Real.sqrt (s * u)) := by rw [← hsqrtid]; ring
        _ ≤ opNorm Fm * opNorm Gm *
              (qhatBeta Fp.β γstar / Real.sqrt (s * u)) := by
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hsqrtq (Real.sqrt_nonneg _)) (mul_nonneg hnF hnG)
        _ = opNorm Fm * opNorm Gm * qhatBeta Fp.β γstar / Real.sqrt (s * u) := by ring
    change |s * u * pairedB P (emaXi₁ Fp.β ℓ (fun a ω => ω a))
        (emaXi₂ Fp.β ℓ (fun a ω => ω a)) q q' * toutT Fp.C B x y s u Fm *
          tinT Fp.C B x y s u Gm /
            profileDelta P Fp.C B (emaXi₁ Fp.β ℓ (fun a ω => ω a))
              (emaXi₂ Fp.β ℓ (fun a ω => ω a)) s u| ≤ _
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hs, abs_of_pos hu,
      abs_of_nonneg hb.1, abs_of_pos hdpos]
    have hnum : s * u * pairedB P (emaXi₁ Fp.β ℓ (fun a ω => ω a))
        (emaXi₂ Fp.β ℓ (fun a ω => ω a)) q q' * |toutT Fp.C B x y s u Fm| *
          |tinT Fp.C B x y s u Gm| ≤
        Muon.sPow Fp.β 2 * Fp.β ^ ℓ *
          (opNorm Fm * opNorm Gm * qhatBeta Fp.β γstar / Real.sqrt (s * u)) := by
      have hsp : 0 ≤ Muon.sPow Fp.β 2 := tsum_nonneg fun j => sq_nonneg (Muon.emaW Fp.β j)
      have hA0 : 0 ≤ s * u * |toutT Fp.C B x y s u Fm| * |tinT Fp.C B x y s u Gm| := by
        positivity
      have hM0 : 0 ≤ Muon.sPow Fp.β 2 * Fp.β ^ ℓ :=
        mul_nonneg hsp (pow_nonneg Fp.hβ.1 ℓ)
      have ht := mul_le_mul hb.2 htr hA0 hM0
      convert ht using 1 <;> ring
    have hnum0 : 0 ≤ s * u * pairedB P (emaXi₁ Fp.β ℓ (fun a ω => ω a))
        (emaXi₂ Fp.β ℓ (fun a ω => ω a)) q q' * |toutT Fp.C B x y s u Fm| *
          |tinT Fp.C B x y s u Gm| :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hs.le hu.le) hb.1)
        (abs_nonneg _)) (abs_nonneg _)
    have hupper0 : 0 ≤ Muon.sPow Fp.β 2 * Fp.β ^ ℓ *
        (opNorm Fm * opNorm Gm * qhatBeta Fp.β γstar / Real.sqrt (s * u)) := by
      have hsp : 0 ≤ Muon.sPow Fp.β 2 := tsum_nonneg fun j => sq_nonneg (Muon.emaW Fp.β j)
      have hnF : 0 ≤ opNorm Fm := by unfold opNorm; exact norm_nonneg _
      have hnG : 0 ≤ opNorm Gm := by unfold opNorm; exact norm_nonneg _
      positivity
    calc
      _ ≤ (Muon.sPow Fp.β 2 * Fp.β ^ ℓ *
          (opNorm Fm * opNorm Gm * qhatBeta Fp.β γstar / Real.sqrt (s * u))) /
            (epsBeta Fp.β γstar ^ 2 / 4) :=
        div_le_div₀ hupper0 hnum (div_pos (sq_pos_of_pos hd0.1) (by norm_num)) hd
      _ = _ := by
        field_simp [ne_of_gt hd0.1, ne_of_gt (Real.sqrt_pos.2 (mul_pos hs hu))]

theorem cor_app_vol_closed_bounds_iv (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ) :
    ∀ s u : ℝ, 0 < s → 0 < u →
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF s) (iotaF u)| ≤
        clagConst Fp.β γstar * Muon.opNorm Fm * Muon.opNorm Gm * Fp.β ^ ℓ / Real.sqrt (s * u) := by
  intro s u hs hu
  by_cases hβ : Fp.β = 0
  · by_cases hℓ : ℓ = 0
    · subst hℓ
      have hb := (cor_app_vol_closed_bounds_ii cert γstar CSig Fp S hS hCSig 0
        Fm Gm Fd Gd hFd hGd s u hs hu).1
      rw [hβ] at hb
      rw [clagConst, if_pos hβ, hβ]
      norm_num
      convert hb using 1 <;> ring
    · have hz := (cor_app_vol_closed_bounds_i cert γstar CSig Fp S hS hCSig ℓ
        Fm Gm Fd Gd hFd hGd).2.2 hβ (by omega) s u hs hu
      rw [hz, abs_zero, hβ, zero_pow hℓ]
      norm_num
  · have hβpos : 0 < Fp.β := lt_of_le_of_ne Fp.hβ.1 (Ne.symm hβ)
    by_cases hℓ : ℓ = 0
    · subst hℓ
      have hb := (cor_app_vol_closed_bounds_ii cert γstar CSig Fp S hS hCSig 0
        Fm Gm Fd Gd hFd hGd s u hs hu).1
      have hsqrt : 0 < Real.sqrt (s * u) := Real.sqrt_pos.2 (mul_pos hs hu)
      have hnF : 0 ≤ opNorm Fm := by unfold opNorm; exact norm_nonneg _
      have hnG : 0 ≤ opNorm Gm := by unfold opNorm; exact norm_nonneg _
      refine hb.trans ?_
      simp only [clagConst, hβ, if_false, pow_zero, mul_one]
      calc
        γstar * opNorm Fm * opNorm Gm / (4 * Real.sqrt (s * u)) =
            (γstar / 4) * opNorm Fm * opNorm Gm / Real.sqrt (s * u) := by ring
        _ ≤ max (γstar / 4)
              (4 * Muon.sPow Fp.β 2 * qhatBeta Fp.β γstar / epsBeta Fp.β γstar ^ 2) *
              opNorm Fm * opNorm Gm / Real.sqrt (s * u) := by
          apply div_le_div_of_nonneg_right _ hsqrt.le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hnF) hnG
    · have hb := cor_app_vol_closed_bounds_iii cert γstar CSig Fp S hS hCSig hβpos ℓ
        Fm Gm Fd Gd hFd hGd s u hs hu (by omega)
      have hsqrt : 0 < Real.sqrt (s * u) := Real.sqrt_pos.2 (mul_pos hs hu)
      have hnF : 0 ≤ opNorm Fm := by unfold opNorm; exact norm_nonneg _
      have hnG : 0 ≤ opNorm Gm := by unfold opNorm; exact norm_nonneg _
      have hpow : 0 ≤ Fp.β ^ ℓ := pow_nonneg Fp.hβ.1 ℓ
      refine hb.trans ?_
      simp only [clagConst, hβ, if_false]
      calc
        4 * Muon.sPow Fp.β 2 * qhatBeta Fp.β γstar * opNorm Fm * opNorm Gm *
              Fp.β ^ ℓ / (epsBeta Fp.β γstar ^ 2 * Real.sqrt (s * u)) =
            (4 * Muon.sPow Fp.β 2 * qhatBeta Fp.β γstar /
                epsBeta Fp.β γstar ^ 2) * opNorm Fm * opNorm Gm * Fp.β ^ ℓ /
              Real.sqrt (s * u) := by ring
        _ ≤ max (γstar / 4)
              (4 * Muon.sPow Fp.β 2 * qhatBeta Fp.β γstar / epsBeta Fp.β γstar ^ 2) *
              opNorm Fm * opNorm Gm * Fp.β ^ ℓ / Real.sqrt (s * u) := by
          apply div_le_div_of_nonneg_right _ hsqrt.le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_right _ _) hnF) hnG) hpow

private lemma red_gauss_exists (A : Type) [Countable A] :
    ∃ P : Measure (A → ℝ), IsProbabilityMeasure P ∧
      IsStdGaussianFamily P (fun (a : A) (ω : A → ℝ) => ω a) := by
  refine ⟨Measure.infinitePi (fun _ : A => gaussianReal 0 1), inferInstance, ?_, ?_, ?_⟩
  · intro a; exact measurable_pi_apply a
  · exact iIndepFun_infinitePi (P := fun _ : A => gaussianReal 0 1)
      (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  · intro a
    exact ⟨(measurable_pi_apply a).aemeasurable, by
      simpa using Measure.infinitePi_map_eval (fun _ : A => gaussianReal 0 1) a⟩

private lemma red_sum_ids {d : ℕ} (v : Fin d → ℝ) (s u a a' : ℝ)
    (hs : ∀ i, s + a * v i ≠ 0) (hu : ∀ i, u + a' * v i ≠ 0) :
    (∑ i, v i / (s + a * v i)) - ∑ i, v i / (u + a' * v i) =
      (u - s) * ∑ i, v i / ((s + a * v i) * (u + a' * v i)) +
        (a' - a) * ∑ i, v i * v i / ((s + a * v i) * (u + a' * v i)) ∧
    u * ∑ i, v i / (u + a' * v i) - s * ∑ i, v i / (s + a * v i) =
      (u * a - s * a') * ∑ i, v i * v i / ((s + a * v i) * (u + a' * v i)) := by
  constructor
  · rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h1 := hs i
    have h2 := hu i
    rw [div_sub_div _ _ h1 h2, ← mul_div_assoc, ← mul_div_assoc, ← add_div]
    congr 1
    ring
  · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h1 := hs i
    have h2 := hu i
    rw [← mul_div_assoc, ← mul_div_assoc, ← mul_div_assoc, div_sub_div _ _ h2 h1,
      mul_comm (u + a' * v i)]
    congr 1 <;> ring

private lemma red_trace_one {d : ℕ} (A U : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ)
    (hU : Uᵀ * U = 1) (hA : A = U * Matrix.diagonal v * Uᵀ) (s a : ℝ)
    (hs : ∀ i, s + a * v i ≠ 0) :
    (A * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • A)⁻¹).trace = ∑ i, v i / (s + a * v i) := by
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have h := closed_trace_two_resolvents A U v (fun _ => 1) hU hA 1
    (by rw [Matrix.diagonal_one, Matrix.mul_one, hUU]) s a 1 0 hs (by intro i; simp)
  simpa using h

private lemma red_trace_p1 {d : ℕ} (A U : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ)
    (hU : Uᵀ * U = 1) (hA : A = U * Matrix.diagonal v * Uᵀ) (s a u c : ℝ)
    (hs : ∀ i, s + a * v i ≠ 0) (hu : ∀ i, u + c * v i ≠ 0) :
    (A ^ 1 * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • A)⁻¹ *
      (u • (1 : Matrix (Fin d) (Fin d) ℝ) + c • A)⁻¹).trace =
        ∑ i, v i / ((s + a * v i) * (u + c * v i)) := by
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have h := closed_trace_two_resolvents A U v (fun _ => 1) hU hA 1
    (by rw [Matrix.diagonal_one, Matrix.mul_one, hUU]) s a u c hs hu
  simpa using h

private lemma red_trace_p2 {d : ℕ} (A U : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ)
    (hU : Uᵀ * U = 1) (hA : A = U * Matrix.diagonal v * Uᵀ) (s a u c : ℝ)
    (hs : ∀ i, s + a * v i ≠ 0) (hu : ∀ i, u + c * v i ≠ 0) :
    (A * A * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • A)⁻¹ *
      (u • (1 : Matrix (Fin d) (Fin d) ℝ) + c • A)⁻¹).trace =
        ∑ i, v i * v i / ((s + a * v i) * (u + c * v i)) :=
  closed_trace_two_resolvents A U v v hU hA A hA s a u c hs hu

private lemma red_alg (s u σ τ σ' τ' F1 F2 U V Jo b0 e0 : ℝ)
    (hs : 0 < s) (hu : 0 < u) (hsu : s ≠ u)
    (R1 : σ - σ' = (u - s) * Jo + (u * τ' * F2 - s * τ * F1) * U)
    (R2 : u * σ' - s * σ = (u * (s * τ * F1) - s * (u * τ' * F2)) * U)
    (R3 : u * τ' - s * τ = (u * (s * σ * F1) - s * (u * σ' * F2)) * V)
    (hb : b0 * (s * σ * τ - u * σ' * τ') = s * σ * τ * F1 - u * σ' * τ' * F2)
    (he : e0 * (u * σ' * τ' - s * σ * τ) = F1 - F2)
    (hq : s * σ * τ - u * σ' * τ' ≠ 0)
    (hρ : s * σ * τ * F1 - u * σ' * τ' * F2 ≠ 0) :
    ((1 - s * u * U * τ * τ' * e0) * (1 - s * u * V * σ * σ' * e0) - s * u * U * V * b0 ^ 2 ≠ 0) ∧
    Jo ≠ 0 ∧
    s * u * b0 * U * V / ((1 - s * u * U * τ * τ' * e0) * (1 - s * u * V * σ * σ' * e0) - s * u * U * V * b0 ^ 2)
      = U * V * (u * (s * σ * F1) - s * (u * σ' * F2)) / ((u - s) * Jo) := by
  have hus : u - s ≠ 0 := sub_ne_zero.2 (Ne.symm hsu)
  set q := s * σ * τ with hqdef
  set q' := u * σ' * τ' with hq'def
  set A := τ * F1 - τ' * F2 with hA
  set C := σ * F1 - σ' * F2 with hC
  set ρ := q * F1 - q' * F2 with hρdef
  set Δ := (1 - s * u * U * τ * τ' * e0) * (1 - s * u * V * σ * σ' * e0) - s * u * U * V * b0 ^ 2 with hΔ
  have L1 : s * u * A * ((u - s) * Jo) = (u - s) * ρ := by
    simp only [hA, hρdef, hqdef, hq'def]
    linear_combination (-(u * (s * τ * F1) - s * (u * τ' * F2))) * R1 + (u * τ' * F2 - s * τ * F1) * R2
  have L2 : A * (q' - q) * (1 - s * u * U * τ * τ' * e0) = (τ' - τ) * ρ := by
    simp only [hA, hρdef, hqdef, hq'def]
    linear_combination (-(τ * F1 - τ' * F2) * (s * u * U * τ * τ')) * he + (τ * τ' * (F1 - F2)) * R2
  have L3 : C * (q' - q) * (1 - s * u * V * σ * σ' * e0) = (σ' - σ) * ρ := by
    simp only [hC, hρdef, hqdef, hq'def]
    linear_combination (-(σ * F1 - σ' * F2) * (s * u * V * σ * σ')) * he + (σ * σ' * (F1 - F2)) * R3
  have L4 : s * u * A * C * (q - q') ^ 2 * Δ = ρ ^ 2 * ((u - s) * (q - q')) := by
    have P : (A * (q' - q) * (1 - s * u * U * τ * τ' * e0)) * (C * (q' - q) * (1 - s * u * V * σ * σ' * e0)) = ((τ' - τ) * ρ) * ((σ' - σ) * ρ) := by
      rw [L2, L3]
    have hAU : s * u * A * U = u * σ' - s * σ := by rw [R2]; simp only [hA, hqdef, hq'def]; ring
    have hCV : s * u * C * V = u * τ' - s * τ := by rw [R3]; simp only [hC, hqdef, hq'def]; ring
    rw [hΔ]
    have hb' := hb
    linear_combination (s * u) * P - (s * u * A * C * (s * u * U * V) * (b0 * (q - q') + ρ)) * hb - ρ ^ 2 * (s * u * C * V) * hAU - ρ ^ 2 * (u * σ' - s * σ) * hCV
  have L4' : s * u * A * C * (q - q') * Δ = ρ ^ 2 * (u - s) := by
    refine mul_right_cancel₀ hq ?_
    linear_combination L4
  have hρ2 : ρ ^ 2 * (u - s) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hρ) hus
  have hΔne : Δ ≠ 0 := by
    intro h; apply hρ2; rw [← L4', h]; ring
  have hAne : A ≠ 0 := by
    intro h; apply hρ2; rw [← L4', h]; ring
  have hCne : C ≠ 0 := by
    intro h; apply hρ2; rw [← L4', h]; ring
  have hJne : Jo ≠ 0 := by
    intro h; apply mul_ne_zero hus hρ; rw [← L1, h]; ring
  have hN : s * u * A * C * (q - q') ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hs.ne' hu.ne') hAne) hCne) hq
  have G : s * u * b0 * ((u - s) * Jo) = s * u * C * Δ := by
    refine mul_left_cancel₀ hN ?_
    linear_combination (s * u * C * (s * u * A * ((u - s) * Jo))) * hb + (s * u * C * ρ) * L1 - (s * u * C) * L4'
  refine ⟨hΔne, hJne, ?_⟩
  rw [div_eq_div_iff hΔne (mul_ne_zero hus hJne)]
  linear_combination (U * V) * G

private lemma red_tsum_zero (f : ℕ ⊕ Fin 0 → ℝ) :
    ∑' a : ℕ ⊕ Fin 0, f a = ∑' j : ℕ, f (Sum.inl j) := by
  rw [← (Equiv.sumEmpty ℕ (Fin 0)).symm.tsum_eq f]
  rfl

private lemma red_diag_B {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (β : ℝ)
    {g : ℕ ⊕ Fin 0 → Ω → ℝ} (hg : IsStdGaussianFamily P g) (q : ℝ) :
    pairedB P (emaXi₁ β 0 g) (emaXi₂ β 0 g) q q = rwDeriv β q := by
  unfold pairedB rwDeriv
  rw [red_tsum_zero]
  refine tsum_congr (fun j => ?_)
  have h : (∫ ω, (Muon.emaW β j * g (Sum.inl j) ω) * (Muon.emaW β j * g (Sum.inl j) ω) /
      ((1 + q * (Muon.emaW β j * g (Sum.inl j) ω) ^ 2) *
        (1 + q * (Muon.emaW β j * g (Sum.inl j) ω) ^ 2)) ∂P) =
      ∫ x, (Muon.emaW β j * x) * (Muon.emaW β j * x) /
        ((1 + q * (Muon.emaW β j * x) ^ 2) * (1 + q * (Muon.emaW β j * x) ^ 2))
          ∂(gaussianReal 0 1) :=
    (hg.2.2 (Sum.inl j)).integral_comp
      (f := fun x : ℝ => (Muon.emaW β j * x) * (Muon.emaW β j * x) /
        ((1 + q * (Muon.emaW β j * x) ^ 2) * (1 + q * (Muon.emaW β j * x) ^ 2)))
      (Measurable.aestronglyMeasurable (by fun_prop))
  simp only [emaXi₁, emaXi₂, pow_zero, one_mul]
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only
  ring

private lemma red_diag_E {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (β : ℝ)
    {g : ℕ ⊕ Fin 0 → Ω → ℝ} (hg : IsStdGaussianFamily P g) (q : ℝ) :
    pairedE P (emaXi₁ β 0 g) (emaXi₂ β 0 g) q q = fwNegDeriv β q := by
  unfold pairedE fwNegDeriv
  rw [red_tsum_zero]
  refine tsum_congr (fun j => ?_)
  have h : (∫ ω, (Muon.emaW β j * g (Sum.inl j) ω) ^ 2 * (Muon.emaW β j * g (Sum.inl j) ω) ^ 2 /
      ((1 + q * (Muon.emaW β j * g (Sum.inl j) ω) ^ 2) *
        (1 + q * (Muon.emaW β j * g (Sum.inl j) ω) ^ 2)) ∂P) =
      ∫ x, (Muon.emaW β j * x) ^ 2 * (Muon.emaW β j * x) ^ 2 /
        ((1 + q * (Muon.emaW β j * x) ^ 2) * (1 + q * (Muon.emaW β j * x) ^ 2))
          ∂(gaussianReal 0 1) :=
    (hg.2.2 (Sum.inl j)).integral_comp
      (f := fun x : ℝ => (Muon.emaW β j * x) ^ 2 * (Muon.emaW β j * x) ^ 2 /
        ((1 + q * (Muon.emaW β j * x) ^ 2) * (1 + q * (Muon.emaW β j * x) ^ 2)))
      (Measurable.aestronglyMeasurable (by fun_prop))
  simp only [emaXi₁, emaXi₂, pow_zero, one_mul]
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only
  ring

private lemma red_profile_eq {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (γstar CSig : ℝ) (hS : SizeFin Fp.C B γstar CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut Fp.C B) (hν' : (ν' : Measure ℝ) = Muon.nuIn Fp.C B)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g : ℕ ⊕ Fin 0 → Ω → ℝ} (hg : IsStdGaussianFamily P g) (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    profileKernel P Fp.C B (emaXi₁ Fp.β 0 g) (emaXi₂ Fp.β 0 g) Fp.C.Sout Fp.C.Sin s u =
      kernelK Fp.β Fp.C B ν ν' s u := by
  have hβ0 := Fp.hβ.1
  have hβ1 := Fp.hβ.2
  have hp := lem_app_vol_closed_profile_iv hβ0 hβ1 hg
  have hK := nu_pair_mem_classK Fp.C γstar CSig hS Fp.hB ν ν' hν hν'
  have hb1 : ∀ t, 0 < t → branchPt (profileF P (emaXi₁ Fp.β 0 g)) Fp.C B t =
      branchSol (Fw (Muon.emaW Fp.β)) ν ν' t := fun t ht =>
    (lem_app_vol_closed_branch_ema Fp.hB hβ0 hβ1 hg Fp.C CSig γstar ν ν' hν hν' hK ht).2
  have hb2 : ∀ t, 0 < t → branchPt (profileF P (emaXi₂ Fp.β 0 g)) Fp.C B t =
      branchSol (Fw (Muon.emaW Fp.β)) ν ν' t := fun t ht =>
    (lem_app_vol_closed_branch_ema_two Fp.hB hβ0 hβ1 hg Fp.C CSig γstar ν ν' hν hν' hK ht).2
  have hsp : ∀ t, 0 < t → IsBranchPoint (Fw (Muon.emaW Fp.β)) Fp.C B t
      (branchSol (Fw (Muon.emaW Fp.β)) ν ν' t) ∧
      (0 < (branchSol (Fw (Muon.emaW Fp.β)) ν ν' t).1 ∧
       0 < (branchSol (Fw (Muon.emaW Fp.β)) ν ν' t).2.1 ∧
       0 < (branchSol (Fw (Muon.emaW Fp.β)) ν ν' t).2.2.1 ∧
       0 < (branchSol (Fw (Muon.emaW Fp.β)) ν ν' t).2.2.2) := by
    intro t ht
    have h := closed_branch_spec Fp.hB hp.2.2.2.2.2.profile₁ Fp.C hout hin γstar
      (by simpa only [Nat.cast_max] using hS.1) ht
    rw [hb1 t ht, hp.1] at h
    exact h
  simp only [profileKernel, profileDelta, closedDelta, toutT, tinT, hb1 s hs, hb2 u hu,
    kernelK, trOutP, trInP, Rbar, Rtbar, upsilonK]
  by_cases hsu : s = u
  · subst hsu
    rw [if_pos rfl, red_diag_B Fp.β hg, red_diag_E Fp.β hg, pow_two Fp.C.Sout, pow_two Fp.C.Sin]
    ring
  · rw [if_neg hsu]
    obtain ⟨hxs, hxpos⟩ := hsp s hs
    obtain ⟨hys, hypos⟩ := hsp u hu
    have hq0 : 0 < s * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).1 *
        (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).2.1 := mul_pos (mul_pos hs hxpos.1) hxpos.2.1
    have hq0' : 0 < u * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).1 *
        (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).2.1 := mul_pos (mul_pos hu hypos.1) hypos.2.1
    have hqne : s * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).1 *
        (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).2.1 ≠
        u * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).1 *
        (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).2.1 := by
      intro heq
      apply hsu
      refine (lem_app_vol_closed_branch_iii Fp.hB hp.2.2.2.2.2.profile₁ Fp.C hout hin).2.injOn
        (Set.mem_Ioi.2 hs) (Set.mem_Ioi.2 hu) ?_
      simp only [hb1 s hs, hb1 u hu]
      exact heq
    have hmono := (lem_app_vol_closed_profile_ii hp.2.2.2.2.2.profile₁).1
    have hρ : (s * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).1 *
        (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).2.1) *
          Fw (Muon.emaW Fp.β) (s * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).1 *
            (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).2.1) -
        (u * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).1 *
        (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).2.1) *
          Fw (Muon.emaW Fp.β) (u * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).1 *
            (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).2.1) ≠ 0 := by
      intro h
      apply hqne
      refine hmono.injOn (Set.mem_Ici.2 hq0.le) (Set.mem_Ici.2 hq0'.le) ?_
      simp only [profileR, hp.1]
      linarith
    obtain ⟨hBd, hEd⟩ := hp.2.2.1 _ _ hq0.le hq0'.le (by simpa using hqne)
    simp only [mul_zero, pow_zero, one_mul] at hBd hEd
    have hb : pairedB P (emaXi₁ Fp.β 0 g) (emaXi₂ Fp.β 0 g)
        (s * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).1 * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).2.1)
        (u * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).1 * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).2.1) *
        ((s * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).1 * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).2.1) -
        (u * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).1 * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).2.1)) =
        (s * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).1 * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).2.1) *
          Fw (Muon.emaW Fp.β) (s * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).1 *
            (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).2.1) -
        (u * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).1 *
        (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).2.1) *
          Fw (Muon.emaW Fp.β) (u * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).1 *
            (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).2.1) := by
      rw [hBd, div_mul_cancel₀ _ (sub_ne_zero.2 hqne)]
      simp [rW]
    have he : pairedE P (emaXi₁ Fp.β 0 g) (emaXi₂ Fp.β 0 g)
        (s * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).1 * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).2.1)
        (u * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).1 * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).2.1) *
        ((u * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).1 * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).2.1) -
        (s * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).1 * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).2.1)) =
        Fw (Muon.emaW Fp.β) (s * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).1 *
            (branchSol (Fw (Muon.emaW Fp.β)) ν ν' s).2.1) -
        Fw (Muon.emaW Fp.β) (u * (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).1 *
            (branchSol (Fw (Muon.emaW Fp.β)) ν ν' u).2.1) := by
      rw [hEd, div_mul_cancel₀ _ (sub_ne_zero.2 hqne.symm)]
    clear hBd hEd hmono hq0 hq0'
    generalize branchSol (Fw (Muon.emaW Fp.β)) ν ν' s = x at *
    generalize branchSol (Fw (Muon.emaW Fp.β)) ν ν' u = y at *
    obtain ⟨σ, τ, a, c⟩ := x
    obtain ⟨σ', τ', a', c'⟩ := y
    obtain ⟨hσ0, hτ0, ha0, hc0, hσ, hτ, ha, hc⟩ := hxs
    obtain ⟨hσ0', hτ0', ha0', hc0', hσ', hτ', ha', hc'⟩ := hys
    dsimp only at *
    have hso : ∀ i, s + a * S.μ i ≠ 0 := fun i => ne_of_gt
      (add_pos_of_pos_of_nonneg hs (mul_nonneg ha0 (μ_nonneg S i)))
    have huo : ∀ i, u + a' * S.μ i ≠ 0 := fun i => ne_of_gt
      (add_pos_of_pos_of_nonneg hu (mul_nonneg ha0' (μ_nonneg S i)))
    have hsi : ∀ j, s + c * S.lam j ≠ 0 := fun j => ne_of_gt
      (add_pos_of_pos_of_nonneg hs (mul_nonneg hc0 (lam_nonneg S j)))
    have hui : ∀ j, u + c' * S.lam j ≠ 0 := fun j => ne_of_gt
      (add_pos_of_pos_of_nonneg hu (mul_nonneg hc0' (lam_nonneg S j)))
    rw [red_trace_one Fp.C.Sout S.uOut S.μ S.huOut (Sout_eq_spectral S) s a hso] at hσ
    rw [red_trace_one Fp.C.Sout S.uOut S.μ S.huOut (Sout_eq_spectral S) u a' huo] at hσ'
    rw [red_trace_one Fp.C.Sin S.vIn S.lam S.hvIn (Sin_eq_spectral S) s c hsi] at hτ
    rw [red_trace_one Fp.C.Sin S.vIn S.lam S.hvIn (Sin_eq_spectral S) u c' hui] at hτ'
    have h1 := red_sum_ids S.μ s u a a' hso huo
    have h2 := red_sum_ids S.lam s u c c' hsi hui
    rw [pow_two Fp.C.Sout, pow_two Fp.C.Sin]
    generalize hJ : (↑B : ℝ)⁻¹ * (Fp.C.Sout ^ 1 * (s • (1 : Matrix (Fin m) (Fin m) ℝ) +
      a • Fp.C.Sout)⁻¹ * (u • (1 : Matrix (Fin m) (Fin m) ℝ) + a' • Fp.C.Sout)⁻¹).trace = Jo
    generalize hU : (↑B : ℝ)⁻¹ * (Fp.C.Sout * Fp.C.Sout * (s • (1 : Matrix (Fin m) (Fin m) ℝ) +
      a • Fp.C.Sout)⁻¹ * (u • (1 : Matrix (Fin m) (Fin m) ℝ) + a' • Fp.C.Sout)⁻¹).trace = U
    generalize hV : (↑B : ℝ)⁻¹ * (Fp.C.Sin * Fp.C.Sin * (s • (1 : Matrix (Fin n) (Fin n) ℝ) +
      c • Fp.C.Sin)⁻¹ * (u • (1 : Matrix (Fin n) (Fin n) ℝ) + c' • Fp.C.Sin)⁻¹).trace = V
    rw [red_trace_p1 Fp.C.Sout S.uOut S.μ S.huOut (Sout_eq_spectral S) s a u a' hso huo] at hJ
    rw [red_trace_p2 Fp.C.Sout S.uOut S.μ S.huOut (Sout_eq_spectral S) s a u a' hso huo] at hU
    rw [red_trace_p2 Fp.C.Sin S.vIn S.lam S.hvIn (Sin_eq_spectral S) s c u c' hsi hui] at hV
    have R1 : σ - σ' = (u - s) * Jo + (a' - a) * U := by
      rw [hσ, hσ', ← hJ, ← hU]
      linear_combination (↑B : ℝ)⁻¹ * h1.1
    have R2 : u * σ' - s * σ = (u * a - s * a') * U := by
      rw [hσ, hσ', ← hU]
      linear_combination (↑B : ℝ)⁻¹ * h1.2
    have R3 : u * τ' - s * τ = (u * c - s * c') * V := by
      rw [hτ, hτ', ← hV]
      linear_combination (↑B : ℝ)⁻¹ * h2.2
    clear hJ hU hV h1 h2 hσ hσ' hτ hτ' hso huo hsi hui
    subst ha hc ha' hc'
    exact (red_alg s u σ τ σ' τ' _ _ U V Jo _ _ hs hu hsu R1 R2 R3 hb he
      (sub_ne_zero.2 hqne) hρ).2.2


/-- `prop:app-vol-closed-reductions`, part (a), snapshot `cr-2026-10-23`. Declaration of record: if
`Σ_out ≠ 0` and `Σ_in ≠ 0`, then for all `s, u > 0` the lag-zero kernel at the covariances
(`lagResp` at `ℓ = 0` with the eigenvalue tests `μ`, `λ`) equals the two-resolvent kernel
`𝔨(s,u)` of `eqn:app-vol-kernel`. Hence `𝔨_0[Σ_out,Σ_in] = 𝔨`. The spectral measures are `ν, ν'`
with `hν`, `hν'`. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{proposition}[Two reductions]\label{prop:app-vol-closed-reductions}
\leavevmode
\begin{enumerate}[label=(\alph*)]
\item If $\Sigmaout\ne0$ and $\Sigmain\ne0$, then for all $s,u>0$ the right side
of \cref{eqn:app-vol-closed-kernel} at $\ell=0$, $F=\Sigmaout$, $G=\Sigmain$ equals
the two-resolvent kernel $\mathfrak k(s,u)$ of \cref{eqn:app-vol-kernel}. Hence
$\mathfrak k_0[\Sigmaout,\Sigmain]=\mathfrak k$, without ellipticity.
\item If $\Sigmain=\Id_{\Nin}$, then for every $i$, every $\ell\ge0$ and all
$s,u>0$,
\begin{equation}\label{eqn:app-vol-closed-half}
\begin{gathered}
B\,\mathfrak k_\ell[u_i\tensor u_i,\Id_{\Nin}](s,u)=\frac{(\Nin/B)\,su\,\mu_i\,b_\ell}{(s+\tilde s_1\mu_i)(u+\tilde s_1'\mu_i)(s+s_1)(u+s_1')\,\Delta_\ell(s,u)},\\
\mathsf V=\frac{\Nin/B}{(s+s_1)(u+s_1')} .
\end{gathered}
\end{equation}
For $\Nin=\Nout=N$ this is \cref{eqn:app-pl-response} with $\gamma=N/B$; the
identity holds for every pair $(\Nout,\Nin)$.
\end{enumerate}
\end{proposition}
```
-/
theorem prop_app_vol_closed_reductions_i (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut Fp.C B) (hν' : (ν' : Measure ℝ) = Muon.nuIn Fp.C B)
    (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    lagResp cert γstar CSig Fp.β 0 B S.μ S.lam S.μ S.lam (iotaF s) (iotaF u) =
      kernelK Fp.β Fp.C B ν ν' s u := by
  obtain ⟨P, hPprob, hg⟩ := red_gauss_exists (ℕ ⊕ Fin 0)
  haveI := hPprob
  rw [(thm_app_vol_closed_kernel_ii cert γstar CSig Fp S hS hCSig 0 hg Fp.C.Sout Fp.C.Sin S.μ
    S.lam (Sout_eq_spectral S) (Sin_eq_spectral S) s u hs hu).2]
  exact red_profile_eq Fp S γstar CSig hS hout hin ν ν' hν hν' hg s u hs hu

private lemma lag_lam_one {m n : ℕ} {C : Muon.Covariances m n} (S : SpectralData C)
    (hId : C.Sin = 1) (j : Fin n) : S.lam j = 1 := by
  have h := Sin_eq_spectral S
  rw [hId] at h
  have hD : Matrix.diagonal S.lam = 1 := by
    calc Matrix.diagonal S.lam = (S.vInᵀ * S.vIn) * Matrix.diagonal S.lam *
          (S.vInᵀ * S.vIn) := by rw [S.hvIn, Matrix.one_mul, Matrix.mul_one]
      _ = S.vInᵀ * (S.vIn * Matrix.diagonal S.lam * S.vInᵀ) * S.vIn := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← h, Matrix.mul_one, S.hvIn]
  have := congrFun (congrFun hD j) j
  simpa using this

private lemma lag_branchPt_nonneg {m n : ℕ} (F : ℝ → ℝ) (C : Muon.Covariances m n) (B : ℕ)
    (s : ℝ) : 0 ≤ (branchPt F C B s).2.2.1 ∧ 0 ≤ (branchPt F C B s).2.2.2 := by
  unfold branchPt
  split_ifs with h
  · have := h.choose_spec
    generalize h.choose = x at this
    obtain ⟨x1, x2, x3, x4⟩ := x
    simp only [IsBranchPoint] at this
    exact ⟨this.2.2.1, this.2.2.2.1⟩
  · simp


/-- `prop:app-vol-closed-reductions`, part (b), snapshot `cr-2026-10-23`. Declaration of record: if
`Σ_in = Id_{N_in}`, then for every output index `i`, every lag `ℓ` and all `s, u > 0`,
`B 𝔨_ℓ[u_i ⊗ u_i, Id](s,u) = (N_in/B) s u μ_i b_ℓ / ((s + s̃₁ μ_i)(u + s̃₁' μ_i)(s + s₁)(u + s₁') Δ_ℓ)`
and `𝖵 = 𝒯^in[Σ_in](s,u) = (N_in/B) / ((s + s₁)(u + s₁'))`, with the branch and `b_ℓ`, `Δ_ℓ` of the
EMA paired profile at lag `ℓ`. The test `u_i ⊗ u_i` is the diagonal `Pi.single i 1` in the basis
`S.uOut`. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{proposition}[Two reductions]\label{prop:app-vol-closed-reductions}
\leavevmode
\begin{enumerate}[label=(\alph*)]
\item If $\Sigmaout\ne0$ and $\Sigmain\ne0$, then for all $s,u>0$ the right side
of \cref{eqn:app-vol-closed-kernel} at $\ell=0$, $F=\Sigmaout$, $G=\Sigmain$ equals
the two-resolvent kernel $\mathfrak k(s,u)$ of \cref{eqn:app-vol-kernel}. Hence
$\mathfrak k_0[\Sigmaout,\Sigmain]=\mathfrak k$, without ellipticity.
\item If $\Sigmain=\Id_{\Nin}$, then for every $i$, every $\ell\ge0$ and all
$s,u>0$,
\begin{equation}\label{eqn:app-vol-closed-half}
\begin{gathered}
B\,\mathfrak k_\ell[u_i\tensor u_i,\Id_{\Nin}](s,u)=\frac{(\Nin/B)\,su\,\mu_i\,b_\ell}{(s+\tilde s_1\mu_i)(u+\tilde s_1'\mu_i)(s+s_1)(u+s_1')\,\Delta_\ell(s,u)},\\
\mathsf V=\frac{\Nin/B}{(s+s_1)(u+s_1')} .
\end{gathered}
\end{equation}
For $\Nin=\Nout=N$ this is \cref{eqn:app-pl-response} with $\gamma=N/B$; the
identity holds for every pair $(\Nout,\Nin)$.
\end{enumerate}
\end{proposition}
```
-/
theorem prop_app_vol_closed_reductions_ii {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (hId : Fp.C.Sin = 1)
    (ℓ : ℕ) {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g) (i : Fin m) (s u : ℝ)
    (hs : 0 < s) (hu : 0 < u) :
    (B : ℝ) * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1) (fun _ : Fin n => (1 : ℝ))
        (iotaF s) (iotaF u) =
      ((n : ℝ) / B) * s * u * S.μ i * emaLagB P Fp.β ℓ g
          (s * (emaBr1 P Fp.C B Fp.β ℓ g s).1 * (emaBr1 P Fp.C B Fp.β ℓ g s).2.1)
          (u * (emaBr2 P Fp.C B Fp.β ℓ g u).1 * (emaBr2 P Fp.C B Fp.β ℓ g u).2.1) /
        ((s + (emaBr1 P Fp.C B Fp.β ℓ g s).2.2.1 * S.μ i) *
          (u + (emaBr2 P Fp.C B Fp.β ℓ g u).2.2.1 * S.μ i) *
          (s + (emaBr1 P Fp.C B Fp.β ℓ g s).2.2.2) *
          (u + (emaBr2 P Fp.C B Fp.β ℓ g u).2.2.2) *
          profileDelta P Fp.C B (emaXi₁ Fp.β ℓ g) (emaXi₂ Fp.β ℓ g) s u) ∧
    tinT Fp.C B (emaBr1 P Fp.C B Fp.β ℓ g s) (emaBr2 P Fp.C B Fp.β ℓ g u) s u Fp.C.Sin =
      ((n : ℝ) / B) /
        ((s + (emaBr1 P Fp.C B Fp.β ℓ g s).2.2.2) * (u + (emaBr2 P Fp.C B Fp.β ℓ g u).2.2.2)) := by
  have hlam := lag_lam_one S hId
  have hB : (B : ℝ) ≠ 0 := by exact_mod_cast Fp.hB.ne'
  constructor
  · rw [closed_lagResp_mode_sum cert γstar CSig Fp S hS hCSig ℓ hg (Pi.single i 1)
      (fun _ => 1) s u hs hu]
    have h1 : ∀ i' : Fin m, (∑ j : Fin n, (Pi.single i 1 : Fin m → ℝ) i' * (1 : ℝ) *
        (B : ℝ) ^ (-2 : ℤ) * closedModeH P Fp.C B Fp.β ℓ g (S.μ i') (S.lam j) s u) =
        if i' = i then ∑ j : Fin n, (B : ℝ) ^ (-2 : ℤ) *
          closedModeH P Fp.C B Fp.β ℓ g (S.μ i) (S.lam j) s u else 0 := by
      intro i'
      by_cases h : i' = i
      · subst h; simp
      · simp [h, Pi.single_apply]
    rw [Finset.sum_congr rfl (fun i' _ => h1 i'), Finset.sum_ite_eq' Finset.univ i]
    simp only [Finset.mem_univ, if_true, hlam, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    unfold closedModeH
    simp only [lag_pairedB_eq]
    simp only [emaBr1, emaBr2, mul_one]
    have hBp : (B : ℝ) ^ (-2 : ℤ) = (B : ℝ)⁻¹ ^ 2 := by norm_num [_root_.zpow_neg]
    rw [hBp]
    field_simp
  · have hc := lag_branchPt_nonneg (profileF P (emaXi₁ Fp.β ℓ g)) Fp.C B s
    have hc' := lag_branchPt_nonneg (profileF P (emaXi₂ Fp.β ℓ g)) Fp.C B u
    have hsi : ∀ j, s + (emaBr1 P Fp.C B Fp.β ℓ g s).2.2.2 * S.lam j ≠ 0 := fun j => ne_of_gt
      (add_pos_of_pos_of_nonneg hs (mul_nonneg hc.2 (lam_nonneg S j)))
    have hui : ∀ j, u + (emaBr2 P Fp.C B Fp.β ℓ g u).2.2.2 * S.lam j ≠ 0 := fun j => ne_of_gt
      (add_pos_of_pos_of_nonneg hu (mul_nonneg hc'.2 (lam_nonneg S j)))
    unfold tinT
    rw [red_trace_p2 Fp.C.Sin S.vIn S.lam S.hvIn (Sin_eq_spectral S) s _ u _ hsi hui]
    simp only [hlam, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    simp only [div_eq_mul_inv, mul_inv]
    ring

end Muon.Volatility

end

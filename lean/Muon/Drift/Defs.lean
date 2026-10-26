import Muon.DetEquiv.Concentration
import Muon.DetEquiv.Branch
import Muon.DetEquiv.Scalar
import Muon.DetEquiv.SampleModel
import Muon.DetEquiv.Resolvent
import Muon.Setup.Truncation
import Muon.Setup.Basic
import Muon.Setup.Regime
import Muon.Oversampled.Model
import Muon.Foundations.Gaussian

/-!
# Muon.Drift: definitions (work package L-C.1)

Definitions of `sections/03-drift/CARD.md` §2, snapshot `cr-2026-10-23`. Every object is
defined once, from the project's shared definitions (`Muon.Setup`, `Muon.DetEquiv`,
`Muon.Foundations.Conventions`); nothing is restated. The weight sequence `w` is a general
`ℕ → ℝ` (the card's design rule (a)); the EMA case is `w := Muon.emaW F.β`.

Constants `C_I` in `e_B^⋆` are passed as explicit parameters (the paper's `C_I` is
existential; no value is fixed). The sequence `e_B` of `lem_app_de_replace` is likewise an
explicit parameter, since that statement is existential and cannot be unpacked in a definition.

No theorem is stated here; the identities of L-C.1 are none (card §5 row L-C.1).
-/

open MeasureTheory Filter Topology Set
open scoped Matrix ENNReal
open Matrix
open Muon Muon.Setup Muon.DetEquiv

namespace Muon.Drift

variable {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## Spectral measures as finite measures (`eqn:app-setup-spectral-measures`)

`nuOut` and `nuIn` are carried to `FiniteMeasure ℝ`, the argument type of
`branchSol`. The output case is A's `nuOutFM` (`Muon.Oversampled`), reused. -/

/-- `ν_in` is a finite measure when `B ≥ 1`. -/
theorem nuIn_isFiniteMeasure (C : Covariances m n) {B : ℕ} (hB : 1 ≤ B) :
    IsFiniteMeasure (Muon.nuIn C B) := by
  unfold Muon.nuIn
  exact Measure.smul_finite _ (ENNReal.inv_ne_top.2 (by exact_mod_cast (show B ≠ 0 by omega)))

/-- The output spectral measure `ν_out = nuOut C B` as a `FiniteMeasure ℝ` (reuses
`Muon.Oversampled.nuOutFM`). -/
noncomputable def specOutFM (F : FrozenParams m n B) : FiniteMeasure ℝ :=
  Muon.Oversampled.nuOutFM F.C B F.hB

/-- The input spectral measure `ν_in = nuIn C B` as a `FiniteMeasure ℝ`. -/
noncomputable def specInFM (F : FrozenParams m n B) : FiniteMeasure ℝ :=
  ⟨Muon.nuIn F.C B, nuIn_isFiniteMeasure F.C F.hB⟩

/-! ## Fresh Gaussian sample and expectations over it -/

/-- Law of a fresh pair `(z, w) ~ N(0,I_m) ⊗ N(0,I_n)`, as in `FrozenSamples.law`. -/
noncomputable def freshMeas (m n : ℕ) : Measure (Vec m × Vec n) :=
  (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)

/-- `𝔼 g(d)` for the fresh sample scalar `d = zᵀ Â w` (`lem:app-drift-gaussian`,
`lem:app-de-gaussian`). -/
noncomputable def freshExp (A : Mat m n) (g : ℝ → ℝ) : ℝ :=
  ∫ x, g (dotProduct x.1 (Matrix.mulVec A x.2)) ∂(freshMeas m n)

/-! ## The weight-parametrized branch objects -/

/-- `q(-s) = s σ(-s) σ̃(-s)` of the branch with weights `w` and measures `ν, ν'`
(`def:app-de-branch`, `eqn:app-de-system`). -/
noncomputable def branchQ (w : ℕ → ℝ) (ν ν' : FiniteMeasure ℝ) (s : ℝ) : ℝ :=
  s * (branchSol (Fw w) ν ν' s).1 * (branchSol (Fw w) ν ν' s).2.1

/-- `σ(-s)` of the branch (`def:app-de-branch`). -/
noncomputable def branchSigma (w : ℕ → ℝ) (ν ν' : FiniteMeasure ℝ) (s : ℝ) : ℝ :=
  (branchSol (Fw w) ν ν' s).1

/-- Normalized state product `Σ_out^{1/2} Â Σ_in^{1/2} = 𝔼 G̃` (`eqn:app-drift-H`,
`eqn:app-setup-normalized-moments`). `Â` is the frozen normalized state `F.A`. -/
noncomputable def EG (F : FrozenParams m n B) : Mat m n :=
  rOut F.C * F.A * rIn F.C

/-! ## The candidates (`eqn:app-drift-H`, `eqn:app-drift-Gbar`) -/

/-- Expected mixed resolvent `𝓗(s) = 𝔼[R(-s) M_t] = 𝔼 𝖷_s(M_t)` of the buffer with
weights `w` (`eqn:app-drift-H`). -/
noncomputable def Hmix (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ) :
    Mat m n :=
  Muon.mean P (fun ω => Xs (WeightedBuf w F S t ω) s)

/-- Candidate `T(s) = s Lw(q(-s)) R̄(-s) EG R̃̄(-s)` (`eqn:app-drift-H`). -/
noncomputable def Tcand (w : ℕ → ℝ) (F : FrozenParams m n B) (ν ν' : FiniteMeasure ℝ) (s : ℝ) : Mat m n :=
  (s * Lw w (branchQ w ν ν' s)) •
    (Rbar (Fw w) ν ν' F.C s * EG F * Rtbar (Fw w) ν ν' F.C s)

/-- Regularized candidate `Ḡ_ϱ = (2/π) ∫_0^∞ T(ϱ+u²) du` (`eqn:app-drift-Gbar`). The integral
is taken entrywise (the Bochner integral on `Matrix`, which has no global norm, is the
entrywise one in finite dimension). -/
noncomputable def Gbar (w : ℕ → ℝ) (F : FrozenParams m n B) (ν ν' : FiniteMeasure ℝ) (ϱ : ℝ) : Mat m n :=
  Matrix.of fun i j =>
    (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), Tcand w F ν ν' (ϱ + u ^ 2) i j

/-- Kernel `𝔡(μ,λ) = (√2/π) ∫_0^∞ z Lw(q(-z)) μλ / ((z + s̃₁(-z)μ)(z + s₁(-z)λ)) du`,
`z = ϱ + u²` (`eqn:app-drift-kernel`). The branch is that of the full measures `ν, ν'`. -/
noncomputable def kernel (w : ℕ → ℝ) (ν ν' : FiniteMeasure ℝ) (ϱ μ lam : ℝ) : ℝ :=
  (Real.sqrt 2 / Real.pi) * ∫ u in Ioi (0 : ℝ),
    (ϱ + u ^ 2) * Lw w (branchQ w ν ν' (ϱ + u ^ 2)) * μ * lam /
      ((ϱ + u ^ 2 + (branchSol (Fw w) ν ν' (ϱ + u ^ 2)).2.2.1 * μ) *
        (ϱ + u ^ 2 + (branchSol (Fw w) ν ν' (ϱ + u ^ 2)).2.2.2 * lam))

/-- Expected update `𝔼 Q_ϱ(M_t)` of the frozen-state model (`def:app-setup-frozen`). -/
noncomputable def EQ (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (ϱ : ℝ) :
    Mat m n :=
  Muon.mean P (fun ω => Q ϱ (WeightedBuf w F S t ω))

/-- `ε_B = sup_{ϱ ∈ [ϱ₋, ϱ₊]} ‖𝔼 Q_ϱ(M_t) − Ḡ_ϱ‖_F` (`eqn:app-drift-mean`). -/
noncomputable def epsB (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (ν ν' : FiniteMeasure ℝ) (ϱlo ϱhi : ℝ) : ℝ :=
  ⨆ ϱ ∈ Icc ϱlo ϱhi, fro (EQ w F S t ϱ - Gbar w F ν ν' ϱ)

/-- `E_ϱ` with `(E_ϱ)_{ij} = u_iᵀ(𝔼 G̃ − Ḡ_ϱ) v_j` (`cor:app-drift-kernel`). -/
noncomputable def Erho (w : ℕ → ℝ) (F : FrozenParams m n B) (SD : SpectralData F.C) (S : FrozenSamples P m n B)
    (t : ℤ) (ν ν' : FiniteMeasure ℝ) (ϱ : ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j =>
    dotProduct (SD.u i) ((EQ w F S t ϱ - Gbar w F ν ν' ϱ) *ᵥ SD.v j)

/-- `𝔡_i = 𝔡(μ_i, 1)` in the half-anisotropic case (`cor:app-drift-halfaniso`). -/
noncomputable def dIdx (w : ℕ → ℝ) (F : FrozenParams m n B) (ν ν' : FiniteMeasure ℝ) (SD : SpectralData F.C) (ϱ : ℝ) (i : Fin m) :
    ℝ :=
  kernel w ν ν' ϱ (SD.μ i) 1

/-! ## Scalar targets and the centred quantities (`eqn:app-drift-theta`, `-targets`) -/

/-- Target `ϑ_B(I) = sup_{s∈I} (|σ_B(s) − σ(−s)| + |σ̃_B(s) − σ̃(−s)|)`
(`eqn:app-drift-theta`). -/
noncomputable def thetaB (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (ν ν' : FiniteMeasure ℝ) (I : Set ℝ) : ℝ :=
  ⨆ s ∈ I, (|sigmaB w F S t s - (branchSol (Fw w) ν ν' s).1| +
    |sigmaTildeB w F S t s - (branchSol (Fw w) ν ν' s).2.1|)

/-- `x_j = w_j² q(-s)` (`eqn:app-drift-targets`). -/
noncomputable def xJ (w : ℕ → ℝ) (ν ν' : FiniteMeasure ℝ) (j : ℕ) (s : ℝ) : ℝ :=
  w j ^ 2 * branchQ w ν ν' s

/-- `α⋆_{1,j} = w_j f_{x_j}(d_j)` (`eqn:app-drift-targets`). -/
noncomputable def alphaStar1 (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (ν ν' : FiniteMeasure ℝ) (j : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  w j * fX (xJ w ν ν' j s) (ageD F S t j ω)

/-- `α⋆_{2,j} = w_j² σ(−s) ψ_{x_j}(d_j)` (`eqn:app-drift-targets`). -/
noncomputable def alphaStar2 (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (ν ν' : FiniteMeasure ℝ) (j : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  w j ^ 2 * branchSigma w ν ν' s * psiX (xJ w ν ν' j s) (ageD F S t j ω)

/-- `r'_B = sup_{0≤x≤Q} |𝔼 f'_x(d) − J(x)|` (`lem:app-drift-gaussian`), with `Q = q_I` an
explicit parameter (the ambient interval's bound). `f'_x` is the derivative in `d`. -/
noncomputable def rPrimeB (A : Mat m n) (Q : ℝ) : ℝ :=
  ⨆ x ∈ Icc (0 : ℝ) Q, |freshExp A (fun d => deriv (fX x) d) - J x|

/-- `δ_B(I) = sup_{s∈I} ‖𝒫(s) − R̄(−s)‖` in operator norm (`prop:app-drift-response`). -/
noncomputable def deltaB (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (ν ν' : FiniteMeasure ℝ) (I : Set ℝ) : ℝ :=
  ⨆ s ∈ I, opNorm (expRes w F S t s - Rbar (Fw w) ν ν' F.C s)

/-! ## The deleted-sample expectations (`eqn:app-drift-Cj`, `eqn:app-drift-phi`) -/

/-- `𝔼 α_{2,ja}` of a fresh sample: `φ_ϖ(K) = 𝔼 α_2` with `(M_0,𝗁,𝗎,𝗏) = (K, ϖ d, u, v)`
(`eqn:app-drift-phi`). -/
noncomputable def phiFresh (F : FrozenParams m n B) (K : Mat m n) (ϖ s : ℝ) : ℝ :=
  ∫ x, alpha2 K (ϖ * dotProduct x.1 (Matrix.mulVec F.A x.2)) (momU F.C B x) (momV F.C B x) s
    ∂(freshMeas m n)

/-- The σ-field `𝒢_{j1}` generated by all samples other than the age-`j` sample in slot `1`
(`def:app-setup-frozen`, `eqn:app-drift-Cj`). -/
abbrev sigmaOthers (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    MeasurableSpace Ω :=
  ⨆ (p : ℤ × Fin B) (_ : p ≠ (t + 1 - (j : ℤ), slotOne F.hB)),
    MeasurableSpace.comap (S.zw p.1 p.2) inferInstance

/-- `φ_j = 𝔼_{𝒢_{j1}} α_{2,j1}` (`eqn:app-drift-Cj`), as a conditional expectation on `Ω`. -/
noncomputable def phiJ (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (s : ℝ) : Ω → ℝ :=
  condExp (sigmaOthers F S t j) P (delAlpha2 w F S t j s)

/-- `b_j = 𝔼 φ_j` (`eqn:app-drift-Cj`). -/
noncomputable def bj (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (s : ℝ) : ℝ :=
  ∫ ω, phiJ w F S t j s ω ∂P

/-- `𝒞_j = 𝔼[(φ_j − b_j) 𝖷_0^{(j1)}]` (`eqn:app-drift-Cj`). -/
noncomputable def Cj (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (s : ℝ) : Mat m n :=
  Muon.mean P (fun ω =>
    (phiJ w F S t j s ω - bj w F S t j s) • Xs (delBufAge w F S t j ω) s)

/-- `ℋ_j(s) = 𝔼 𝖷_0^{(j1)}` (`eqn:app-drift-deletion-mean`). -/
noncomputable def Hj (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (s : ℝ) : Mat m n :=
  Muon.mean P (fun ω => Xs (delBufAge w F S t j ω) s)

/-- `b_B(s) = ∑_{j≥0} b_j` (`prop:app-drift-response`). -/
noncomputable def bB (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ) : ℝ :=
  ∑' j, bj w F S t j s

/-- `𝖸_B(s) = Id_{N_in} + b_B(s) Σ_in` (`prop:app-drift-response`). -/
noncomputable def YB (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 : Matrix (Fin n) (Fin n) ℝ) + bB w F S t s • F.C.Sin

/-- Response residual `E_B(s) = 𝓗(s) 𝖸_B(s) − Lw(q(−s)) R̄(−s) 𝔼G̃` (`prop:app-drift-response`). -/
noncomputable def EB (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (ν ν' : FiniteMeasure ℝ) (s : ℝ) : Mat m n :=
  Hmix w F S t s * YB w F S t s -
    (Lw w (branchQ w ν ν' s)) • (Rbar (Fw w) ν ν' F.C s * EG F)

/-- The shifted constant `e_B^⋆ = e_B + C_I ϑ_B(I)` (`lem:app-drift-targets`). The constant
`C_I` and the sequence `e_B` are explicit parameters (see the module doc). -/
noncomputable def eBstar (e : ℕ → ℝ) (CI : ℝ) (B : ℕ) (ϑ : ℝ) : ℝ :=
  e B + CI * ϑ

/-! ## Truncated objects (`prop:app-drift-truncation`, `lem:app-setup-truncation`) -/

/-- Truncated weights `w^{(J)}_j = w_j 𝟙_{j≤J}` (`prop:app-drift-truncation`). -/
noncomputable def truncW (w : ℕ → ℝ) (J : ℕ) : ℕ → ℝ :=
  fun j => if j ≤ J then w j else 0

/-- Truncated buffer `M^{(J)}_t = ∑_{j≤J} w_j G_{t+1−j}` (`prop:app-drift-truncation`). -/
noncomputable def bufTrunc (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (J : ℕ)
    (ω : Ω) : Mat m n :=
  WeightedBufTrunc w F S t J ω

end Muon.Drift

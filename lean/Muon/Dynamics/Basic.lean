import Muon.Setup.Algorithm
import Muon.Foundations.AnalysisExtra

/-!
# Appendix E, work package L-E.1: objects of the deterministic dynamics

Snapshot `cr-2026-10-23`. Source: `sections/05-dynamics/section.tex`: the standing setup
(ll. 40–123), the deterministic equations and the admissible set (ll. 135–213), the hypotheses of
`thm:app-dyn-main` (ll. 340–352), and the block constants (`eqn:app-dyn-L`, l. 1481).
Card: `sections/05-dynamics/CARD.md` §2 and the L-E.1 row of §5.

This module holds definitions only (work package L-E.1 has no labelled targets). It is the shared
vocabulary of L-E.2 to L-E.13. Reused, not redefined: `Muon.Setup.AlgParams`, `Muon.Setup.run`,
`Muon.Setup.runRand`, `Muon.Setup.devRand`, `Muon.Setup.Ahat`, `Muon.Setup.riskSigma`,
`Muon.Setup.modeQ`, `Muon.Setup.SpectralData`, `Muon.Setup.grad` (the minibatch gradient of
`eqn:app-setup-gradient`, which is `G°_{t+1}[E]` of `eqn:app-dyn-batch`), `Muon.Setup.dataTarget`,
`Muon.Setup.IIDBatch`, `Muon.ProportionalRegime`, `Muon.Covariances`, `Muon.opNorm`, `Muon.fro`.

Representation choices (also in the result JSON `open_questions`):
* Spectral measures are `Measure (ℝ × ℝ)`: finite sums of Dirac masses at `(μ_i, λ_j)`, built by
  `atomMeasure`. The source's `FiniteMeasure K` is not used; every statement only uses them on `K`.
* The bounded-Lipschitz class `blTest` is the source's class on `K` with the ℓ¹ Lipschitz bound
  `|x − y|₁`. `Muon.Foundations.blDist` (sup metric on `ℝ × ℝ`) is not this norm and is not used.
* `𝖪⋆` (`eqn:app-vol-K`) is the explicit function `kStar CSig γstar ϱ`, so `T⋆` is dimension-free and
  D can import the same constant.
* Definitions with a source "defined only where … > 0" return the Lean convention value (`0`)
  outside that domain; every use in the source is at positive risk.
-/

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open Muon Muon.Setup

noncomputable section

namespace Muon.Dynamics

/-! ## Constants and parameters -/

/-- Fixed constants of `thm:app-dyn-main`: macrostep `h` (`\macrostep`), normalized ridge `ϱ`,
momentum `β`, `γ⋆`, `C_Σ`, `E⋆`, `c_M`, `0 < r₀ ≤ r₁`. The constant `𝖪⋆` is `kStar`, not a parameter. Snapshot `cr-2026-10-23`. @@LINES 336 339
-/
structure DynParams where
  h : ℝ
  ϱ : ℝ
  β : ℝ
  γstar : ℝ
  CSig : ℝ
  Estar : ℝ
  cM : ℝ
  r0 : ℝ
  r1 : ℝ
  hh : 0 < h
  hϱ : 0 < ϱ
  hβ : 0 ≤ β ∧ β < 1
  hγ : 0 ≤ γstar
  hC : 1 ≤ CSig
  hE : 0 ≤ Estar
  hcM : 0 ≤ cM
  hr0 : 0 < r0
  hr : r0 ≤ r1

/-- The spectral rectangle `K = [0, C_Σ]²` (`eqn:app-dyn-chi`, l. 79). -/
def specRect (Cs : ℝ) : Set (ℝ × ℝ) := Icc 0 Cs ×ˢ Icc 0 Cs

/-- The ℓ¹ distance `|x − y|₁` on `ℝ × ℝ` (the metric of the bounded-Lipschitz class, l. 99). -/
def l1 (x y : ℝ × ℝ) : ℝ := |x.1 - y.1| + |x.2 - y.2|

/-- The constant `𝖪⋆ = C_Σ √(2γ⋆(γ⋆² + 4γ⋆ + 3)/ϱ)` of `eqn:app-vol-K` at `ϱ₋ = ϱ`. Defined here
so that the volatility section can import it. Snapshot `cr-2026-10-23`. Source (D, `eqn:app-vol-K`):
`eqn:app-vol-K` (`section.tex` ll. 862–864 of D (`sections/04-volatility/section.tex`)):
```latex
\begin{equation}\label{eqn:app-vol-K}
\mathsf K_\star\defeq C_\Sigma\sqrt{\frac{2\gamma_\star(\gamma_\star^2+4\gamma_\star+3)}{\ridge_-}} .
\end{equation}
```
-/
noncomputable def kStar (CSig γstar ϱ : ℝ) : ℝ :=
  CSig * Real.sqrt (2 * γstar * (γstar ^ 2 + 4 * γstar + 3) / ϱ)

/-- `𝔡_max = C_Σ² / √(2ϱ)` (`eqn:app-dyn-coefficient-bounds`). -/
def dMax (p : DynParams) : ℝ := p.CSig ^ 2 / Real.sqrt (2 * p.ϱ)

/-- `m_ζ = γ⋆ + 2𝖪⋆β/(1 − β)`, with `𝖪⋆ = kStar` (`eqn:app-dyn-coefficient-bounds`). -/
def mZeta (p : DynParams) : ℝ := p.γstar + 2 * kStar p.CSig p.γstar p.ϱ * p.β / (1 - p.β)

/-- `C_E` of `eqn:app-dyn-Tstar`. -/
def CE (p : DynParams) : ℝ :=
  2 * p.h * dMax p * (p.Estar + 1) / Real.sqrt (p.r0 / 2) + p.h ^ 2 * mZeta p

/-- `C_𝓡` of `eqn:app-dyn-Tstar`. -/
def CR (p : DynParams) : ℝ :=
  2 * p.h * dMax p * Real.sqrt (p.r1 + 1) + p.h ^ 2 * p.CSig ^ 2 * mZeta p / 2

/-- The horizon `T⋆ = min(r₀,1) / (8(1 + C_E + C_𝓡))`. Dimension-free. Snapshot `cr-2026-10-23`.
Source (`eqn:app-dyn-Tstar`):
`eqn:app-dyn-Tstar` (`section.tex` ll. 189–195):
```latex
\begin{equation}\label{eqn:app-dyn-Tstar}
\begin{gathered}
C_E\defeq\frac{2\macrostep\,\mathfrak d_{\max}(E_\star+1)}{\sqrt{r_0/2}}+\macrostep^2m_\zeta,\qquad
C_{\cR}\defeq2\macrostep\,\mathfrak d_{\max}\sqrt{r_1+1}+\frac{\macrostep^2C_\Sigma^2m_\zeta}{2},\\
T_\star\defeq\frac{\min(r_0,1)}{8\,(1+C_E+C_{\cR})} ,
\end{gathered}
\end{equation}
```
-/
def Tstar (p : DynParams) : ℝ := min p.r0 1 / (8 * (1 + CE p + CR p))

/-- Block length `L = ⌊B^{1/8}⌋` (`eqn:app-dyn-L`). Snapshot `cr-2026-10-23`. Source:
`eqn:app-dyn-L` (`section.tex` ll. 1481–1484):
```latex
\begin{equation}\label{eqn:app-dyn-L}
L\defeq\lfloor B^{1/8}\rfloor,\qquad
\mathsf q\defeq\lceil C_0\log(2B)\rceil,\qquad C_0\defeq\max\Big(1,\frac{2}{\log(1/\bmom)}\Big)
\end{equation}
```
-/
def blockLen (B : ℕ) : ℕ := ⌊(B : ℝ) ^ ((1 : ℝ) / 8)⌋₊

/-- `C₀ = max(1, 2/log(1/β))`, with `C₀ = 1` at `β = 0` (`eqn:app-dyn-L`). The case split is
explicit: Lean's `log 0 = 0` would give the same value by accident. -/
def C0 (β : ℝ) : ℝ := if β = 0 then 1 else max 1 (2 / Real.log (1 / β))

/-- Prefix length `𝗊 = ⌈C₀ log(2B)⌉` (`eqn:app-dyn-L`). -/
def prefixLen (β : ℝ) (B : ℕ) : ℕ := ⌈C0 β * Real.log (2 * (B : ℝ))⌉₊

/-! ## Spectral measures and the field -/

/-- Atomic measure `∑_{ij} q_ij δ_{(μ_i, λ_j)}` on `ℝ × ℝ`. -/
def atomMeasure {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (q : Fin m → Fin n → ℝ) :
    Measure (ℝ × ℝ) :=
  ∑ i, ∑ j, ENNReal.ofReal (q i j) • Measure.dirac (μ i, lam j)

/-- Spectral energy measure `χ(Δ) = ∑_{ij} 𝒬_ij(Δ) δ_{(μ_i,λ_j)}` on `K` (`eqn:app-dyn-chi`,
ll. 78–81). Snapshot `cr-2026-10-23`. Source:
`eqn:app-dyn-chi` (`section.tex` ll. 80–82):
```latex
\begin{equation}\label{eqn:app-dyn-chi}
\chi(\Delta)\defeq\sum_{i,j}\CMscr Q_{ij}(\Delta)\,\delta_{(\mu_i,\lambda_j)}\quad\text{on }\mathbb K .
\end{equation}
```
-/
def specMeasure {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (Δ : Mat m n) :
    Measure (ℝ × ℝ) :=
  atomMeasure S.μ S.lam (Muon.Setup.modeQ S Δ)

/-- Risk of a spectral measure, `𝓡(χ) = ½ ∫ μλ dχ` (`eqn:app-dyn-field` ll. 172–173 and
`def:app-dyn-ode`). -/
def riskOf (χ : Measure (ℝ × ℝ)) : ℝ := (1 / 2) * ∫ x, x.1 * x.2 ∂χ

/-- Admissible spectral measures `𝒜(mass, r₋, r₊)`: finite, carried by `K`, `χ(K) ≤ mass`,
`r₋ ≤ 𝓡(χ) ≤ r₊`. Snapshot `cr-2026-10-23`. `𝔐 = Adm C_Σ (E⋆+1) (r₀/2) (r₁+½)` (`eqn:app-dyn-admissible-measures`). -/
def Adm (Cs mass rlo rhi : ℝ) : Set (Measure (ℝ × ℝ)) :=
  {χ | IsFiniteMeasure χ ∧ χ (specRect Cs)ᶜ = 0 ∧ χ.real univ ≤ mass ∧
    rlo ≤ riskOf χ ∧ riskOf χ ≤ rhi}

/-- The admissible measures `𝔐` of `eqn:app-dyn-admissible-measures`. Snapshot `cr-2026-10-23`. Source:
`eqn:app-dyn-admissible-measures` (`section.tex` ll. 198–200):
```latex
\begin{equation}\label{eqn:app-dyn-admissible-measures}
\mathfrak M\defeq\Big\{\chi\ \text{positive on }\mathbb K:\ \chi(\mathbb K)\le E_\star+1,\ \frac{r_0}{2}\le\fRisk(\chi)\le r_1+\frac12\Big\}.
\end{equation}
```
-/
def admMeasures (p : DynParams) : Set (Measure (ℝ × ℝ)) :=
  Adm p.CSig (p.Estar + 1) (p.r0 / 2) (p.r1 + 1 / 2)

/-- The field `𝖥_B(χ)` in weak form. Snapshot `cr-2026-10-23`. Source:
`eqn:app-dyn-field` (`section.tex` ll. 173–175):
```latex
\begin{equation}\label{eqn:app-dyn-field}
\mathsf F_B(\chi)\defeq-\frac{2\macrostep}{\sqrt{\fRisk(\chi)}}\,\mathfrak d\,\chi+\macrostep^2\zeta .
\end{equation}
```
Weak form:
`φ ↦ −(2h/√𝓡(χ)) ∫ φ 𝔡 dχ + h² ∫ φ dζ`. Its value is `0` when `𝓡(χ) ≤ 0`, outside the domain
of the source definition. -/
def fieldOp (h : ℝ) (d : ℝ × ℝ → ℝ) (ζ χ : Measure (ℝ × ℝ)) (φ : ℝ × ℝ → ℝ) : ℝ :=
  if 0 < riskOf χ then
    -(2 * h / Real.sqrt (riskOf χ)) * ∫ x, φ x * d x ∂χ + h ^ 2 * ∫ x, φ x ∂ζ
  else 0

/-- Bounded-Lipschitz test class on `K`: `|φ| ≤ 1` and `|φ(x) − φ(y)| ≤ |x − y|₁` on `K`. The
norm is the one of the source's setup (snapshot `cr-2026-10-23`). Source:
(`section.tex` ll. 96–101):
```latex
$\mathbb K$ we use the total variation $\norm m_{\mathrm{TV}}$ and the
bounded-Lipschitz norm $\norm m_\BL$ of the volatility section (the
definition following \cref{eqn:app-vol-measures}), in which the test
functions $\phi$ satisfy $\norm\phi_\infty\le1$ and
$\abs{\phi(x)-\phi(y)}\le\abs{x-y}_1$. For a bounded function $\phi$ on
$\mathbb K$, $\phi\,m$ denotes the measure with density $\phi$ with respect
```
-/
def blTest (Cs : ℝ) : Set (ℝ × ℝ → ℝ) :=
  {φ | (∀ x ∈ specRect Cs, |φ x| ≤ 1) ∧
    ∀ x ∈ specRect Cs, ∀ y ∈ specRect Cs, |φ x - φ y| ≤ l1 x y}

/-- Bounded-Lipschitz norm of a linear functional `ℓ` on test functions: `sup_{φ ∈ BL} |ℓ φ|`. -/
def blNorm (Cs : ℝ) (ℓ : (ℝ × ℝ → ℝ) → ℝ) : ℝ :=
  sSup ((fun φ => |ℓ φ|) '' blTest Cs)

/-- Bounded-Lipschitz distance of two measures on `K`, `‖μ − ν‖_BL`. -/
def blDist (Cs : ℝ) (μ ν : Measure (ℝ × ℝ)) : ℝ :=
  blNorm Cs (fun φ => ∫ x, φ x ∂μ - ∫ x, φ x ∂ν)

/-- Total variation norm of a linear functional on measurable test functions:
`sup_{|φ| ≤ 1} |ℓ φ|`. It is the source's `‖·‖_TV` of a signed measure (ll. 96–101) and is used
for the field `𝖥_B(χ)` in `lem:app-dyn-field`. -/
def tvNorm (ℓ : (ℝ × ℝ → ℝ) → ℝ) : ℝ :=
  sSup ((fun φ => |ℓ φ|) '' {φ | Measurable φ ∧ ∀ x, |φ x| ≤ 1})

/-- Total variation distance `‖μ − ν‖_TV = tvNorm (∫ · dμ − ∫ · dν)`. -/
def tvDist (μ ν : Measure (ℝ × ℝ)) : ℝ :=
  tvNorm (fun φ => ∫ x, φ x ∂μ - ∫ x, φ x ∂ν)

/-- Bridge to the sup-metric bounded-Lipschitz norm `Muon.Foundations.blDist` (`AnalysisExtra`, on
`K` with the metric of `ℝ × ℝ`). The source's norm `blDist` (ℓ¹ on `K`) satisfies, for finite
measures carried by `K`, `BL_sup ≤ blDist ≤ 2 · BL_sup`: the sup-Lipschitz test class is contained
in the ℓ¹ class since `|x − y|_∞ ≤ |x − y|_1`, and `φ` in the ℓ¹ class gives `φ/2` in the sup class
since `|x − y|_1 ≤ 2|x − y|_∞`. Proof card in the results JSON. -/
theorem blDist_bridge (Cs : ℝ) (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0) :
    Muon.Foundations.blDist (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) μ)
        (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) ν) ≤ blDist Cs μ ν ∧
      blDist Cs μ ν ≤ 2 * Muon.Foundations.blDist
        (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) μ)
        (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) ν) := by
  classical
  have hK : MeasurableSet (specRect Cs) := measurableSet_Icc.prod measurableSet_Icc
  have hae : ∀ ρ : Measure (ℝ × ℝ), ρ (specRect Cs)ᶜ = 0 → ∀ᵐ x ∂ρ, x ∈ specRect Cs := by
    intro ρ hρ
    rw [ae_iff, show {a | ¬ a ∈ specRect Cs} = (specRect Cs)ᶜ by ext; simp]
    exact hρ
  have hpush : ∀ ρ : Measure (ℝ × ℝ), ρ (specRect Cs)ᶜ = 0 → ∀ φ : ℝ × ℝ → ℝ,
      ∫ x : specRect Cs, φ x.1 ∂(Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) ρ)
        = ∫ x, φ x ∂ρ := by
    intro ρ hρ φ
    rw [← (MeasurableEmbedding.subtype_coe hK).integral_map φ,
      (MeasurableEmbedding.subtype_coe hK).map_comap ρ, Subtype.range_coe, Measure.restrict_eq_self_of_ae_mem (hae ρ hρ)]
  have hfin : ∀ ρ : Measure (ℝ × ℝ), IsFiniteMeasure ρ →
      IsFiniteMeasure (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) ρ) := by
    intro ρ hρ
    refine ⟨?_⟩
    rw [Measure.comap_apply _ (MeasurableEmbedding.subtype_coe hK).injective
      (MeasurableEmbedding.subtype_coe hK).measurableSet_image' _ MeasurableSet.univ]
    exact measure_lt_top _ _
  -- mass bound on blTest
  have hbd : ∀ (ρ : Measure (ℝ × ℝ)) [IsFiniteMeasure ρ], ρ (specRect Cs)ᶜ = 0 →
      ∀ φ ∈ blTest Cs, |∫ x, φ x ∂ρ| ≤ ρ.real univ := by
    intro ρ _ hρ φ hφ
    have h := norm_integral_le_of_norm_le_const (μ := ρ) (f := φ) (C := 1)
      (by
        filter_upwards [hae ρ hρ] with x hx
        rw [Real.norm_eq_abs]
        exact hφ.1 x hx)
    rw [Real.norm_eq_abs, one_mul] at h
    exact h
  -- bounded-Lipschitz image of blTest is bounded
  have hbddL : BddAbove ((fun φ : ℝ × ℝ → ℝ => |∫ x, φ x ∂μ - ∫ x, φ x ∂ν|) '' blTest Cs) := by
    refine ⟨μ.real univ + ν.real univ, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    have h1 := abs_le.mp (hbd μ hμ φ hφ)
    have h2 := abs_le.mp (hbd ν hν φ hφ)
    exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  have hnnL : 0 ≤ blDist Cs μ ν := by
    unfold blDist blNorm
    exact Real.sSup_nonneg (by rintro _ ⟨φ, _, rfl⟩; exact abs_nonneg _)
  have hnnK : 0 ≤ Muon.Foundations.blDist (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) μ)
      (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) ν) := by
    unfold Muon.Foundations.blDist
    exact Real.sSup_nonneg (by rintro _ ⟨f, _, rfl⟩; exact abs_nonneg _)
  rcases le_or_gt 0 Cs with h0 | hneg
  · haveI : IsFiniteMeasure (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) μ) :=
      hfin μ inferInstance
    haveI : IsFiniteMeasure (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) ν) :=
      hfin ν inferInstance
    set μK := Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) μ with hμK
    set νK := Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) ν with hνK
    have hbdK : ∀ (ρ : Measure (specRect Cs)) [IsFiniteMeasure ρ] (f : specRect Cs → ℝ),
        (∀ x, |f x| ≤ 1) → |∫ x, f x ∂ρ| ≤ ρ.real univ := by
      intro ρ _ f hf1
      have h := norm_integral_le_of_norm_le_const (μ := ρ) (f := f) (C := 1)
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hf1 x)
      rw [Real.norm_eq_abs, one_mul] at h
      exact h
    -- projection of ℝ × ℝ onto the rectangle
    obtain ⟨proj, hproj_def⟩ : ∃ proj : ℝ × ℝ → specRect Cs, ∀ x : ℝ × ℝ,
        (proj x).1 = ((projIcc 0 Cs h0 x.1 : ℝ), (projIcc 0 Cs h0 x.2 : ℝ)) :=
      ⟨fun x => ⟨((projIcc 0 Cs h0 x.1 : ℝ), (projIcc 0 Cs h0 x.2 : ℝ)),
        ⟨(projIcc 0 Cs h0 x.1).2, (projIcc 0 Cs h0 x.2).2⟩⟩, fun x => rfl⟩
    have hdproj : ∀ p q : ℝ × ℝ, dist (proj p) (proj q) ≤ l1 p q := by
      intro p q
      simp only [Subtype.dist_eq, hproj_def, Prod.dist_eq, Real.dist_eq]
      unfold l1
      have e1 := Set.abs_projIcc_sub_projIcc (c := p.1) (d := q.1) h0
      have e2 := Set.abs_projIcc_sub_projIcc (c := p.2) (d := q.2) h0
      refine max_le ?_ ?_
      · linarith [abs_nonneg (p.2 - q.2)]
      · linarith [abs_nonneg (p.1 - q.1)]
    have hproj : ∀ x : specRect Cs, proj x.1 = x := by
      intro x
      apply Subtype.ext
      rw [hproj_def, projIcc_of_mem h0 x.2.1, projIcc_of_mem h0 x.2.2]
    -- LEFT inequality
    have hA : Muon.Foundations.blDist μK νK ≤ blDist Cs μ ν := by
      unfold Muon.Foundations.blDist
      refine Real.sSup_le ?_ hnnL
      rintro _ ⟨f, hf, rfl⟩
      have hf' : (∀ x, |f x| ≤ 1) ∧ ∀ x y, |f x - f y| ≤ dist x y := hf
      obtain ⟨φ, hφdef⟩ : ∃ φ : ℝ × ℝ → ℝ, φ = fun x => f (proj x) := ⟨_, rfl⟩
      have hfφ : ∀ x : specRect Cs, f x = φ x.1 := by
        intro x
        rw [hφdef]
        show f x = f (proj x.1)
        rw [hproj x]
      have hφmem : φ ∈ blTest Cs := by
        rw [hφdef]
        refine ⟨fun x _ => hf'.1 _, fun x _ y _ => ?_⟩
        show |f (proj x) - f (proj y)| ≤ l1 x y
        exact (hf'.2 _ _).trans (hdproj x y)
      have e1 : ∫ x : specRect Cs, f x ∂μK = ∫ x : specRect Cs, φ x.1 ∂μK :=
        integral_congr_ae (ae_of_all _ hfφ)
      have e2 : ∫ x : specRect Cs, f x ∂νK = ∫ x : specRect Cs, φ x.1 ∂νK :=
        integral_congr_ae (ae_of_all _ hfφ)
      show |∫ x : specRect Cs, f x ∂μK - ∫ x : specRect Cs, f x ∂νK| ≤ blDist Cs μ ν
      rw [e1, e2, hμK, hνK, hpush μ hμ φ, hpush ν hν φ]
      unfold blDist blNorm
      exact le_csSup hbddL ⟨φ, hφmem, rfl⟩
    -- RIGHT inequality
    have hB : blDist Cs μ ν ≤ 2 * Muon.Foundations.blDist μK νK := by
      have hbddK : BddAbove ((fun f : specRect Cs → ℝ => |∫ x, f x ∂μK - ∫ x, f x ∂νK|) ''
          Muon.Foundations.blBall (specRect Cs)) := by
        refine ⟨μK.real univ + νK.real univ, ?_⟩
        rintro _ ⟨f, hf, rfl⟩
        have hf' : (∀ x, |f x| ≤ 1) ∧ ∀ x y, |f x - f y| ≤ dist x y := hf
        have h1 := abs_le.mp (hbdK μK f hf'.1)
        have h2 := abs_le.mp (hbdK νK f hf'.1)
        exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
      unfold blDist blNorm
      refine Real.sSup_le ?_ (mul_nonneg (by norm_num) hnnK)
      rintro _ ⟨φ, ⟨hφ1, hφ2⟩, rfl⟩
      show |∫ x, φ x ∂μ - ∫ x, φ x ∂ν| ≤ 2 * Muon.Foundations.blDist μK νK
      obtain ⟨f, hfdef⟩ : ∃ f : specRect Cs → ℝ, f = fun x => (1 / 2) * φ x.1 := ⟨_, rfl⟩
      have hf : f ∈ Muon.Foundations.blBall (specRect Cs) := by
        rw [hfdef]
        refine ⟨fun x => ?_, fun x y => ?_⟩
        · show |(1 / 2) * φ x.1| ≤ 1
          have := abs_le.mp (hφ1 x.1 x.2)
          exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩
        · show |(1 / 2) * φ x.1 - (1 / 2) * φ y.1| ≤ dist x y
          have h1 := hφ2 x.1 x.2 y.1 y.2
          have hd : dist x y = max |x.1.1 - y.1.1| |x.1.2 - y.1.2| := by
            rw [Subtype.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
          rw [hd, show (1 / 2 : ℝ) * φ x.1 - (1 / 2) * φ y.1 = (1 / 2) * (φ x.1 - φ y.1) by ring,
            abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          unfold l1 at h1
          have ha := le_max_left |x.1.1 - y.1.1| |x.1.2 - y.1.2|
          have hb := le_max_right |x.1.1 - y.1.1| |x.1.2 - y.1.2|
          linarith
      have hK_le : |∫ x, f x ∂μK - ∫ x, f x ∂νK| ≤ Muon.Foundations.blDist μK νK :=
        le_csSup hbddK ⟨f, hf, rfl⟩
      have hf_eq : ∀ (ρ : Measure (ℝ × ℝ)), ρ (specRect Cs)ᶜ = 0 →
          ∫ x, f x ∂(Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) ρ)
            = (1 / 2) * ∫ x, φ x ∂ρ := by
        intro ρ hρ
        rw [← hpush ρ hρ φ, ← integral_const_mul, hfdef]
      have e : ∫ x, f x ∂μK - ∫ x, f x ∂νK = (1 / 2) * (∫ x, φ x ∂μ - ∫ x, φ x ∂ν) := by
        rw [hμK, hνK, hf_eq μ hμ, hf_eq ν hν]
        ring
      rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hK_le
      linarith
    exact ⟨hA, hB⟩
  · -- empty rectangle: both measures vanish
    have hempty : specRect Cs = ∅ := by
      simp [specRect, Set.Icc_eq_empty (not_le.mpr hneg)]
    have hμ0 : μ = 0 := by
      rw [hempty, Set.compl_empty] at hμ
      exact Measure.measure_univ_eq_zero.mp hμ
    have hν0 : ν = 0 := by
      rw [hempty, Set.compl_empty] at hν
      exact Measure.measure_univ_eq_zero.mp hν
    subst hμ0 hν0
    have hz : ∀ s : Set ℝ, (∀ x ∈ s, x = 0) → sSup s = 0 := fun s hs =>
      le_antisymm (Real.sSup_le (fun x hx => (hs x hx).le) le_rfl)
        (Real.sSup_nonneg (fun x hx => (hs x hx).ge))
    have e1 : Muon.Foundations.blDist (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) 0)
        (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) 0) = 0 := by
      unfold Muon.Foundations.blDist
      apply hz
      rintro _ ⟨f, _, rfl⟩
      simp
    have e2 : blDist Cs 0 0 = 0 := by
      unfold blDist blNorm
      apply hz
      rintro _ ⟨φ, _, rfl⟩
      simp
    rw [e1, e2]
    norm_num

/-! ## The deterministic mode-energy equations -/

/-- Risk of a mode-energy array `e = B²𝒬`: `𝓡 = ½ ∑ μ_i λ_j 𝒬_ij = (1/2B²) ∑ μ_i λ_j e_ij`
(`def:app-dyn-ode`). -/
def odeRisk {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (B : ℝ) (e : Fin m → Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, μ i * lam j * e i j / B ^ 2

/-- Right-hand side of `eqn:app-dyn-ode`, in the variables `e_ij = B²𝒬_ij`:
`ė_ij = −2h 𝔡_ij e_ij/√𝓡 + h² B 𝔳_ij`, with `𝔡_ij = 𝔡(μ_i, λ_j)`. -/
def odeRHS {m n : ℕ} (h B : ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (d : ℝ × ℝ → ℝ)
    (v : Fin m → Fin n → ℝ) (e : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => -(2 * h * d (μ i, lam j)) / Real.sqrt (odeRisk μ lam B e) * e i j
    + h ^ 2 * B * v i j

/-- `def:app-dyn-ode`: `e` solves the deterministic mode-energy equations on `[0, T]` with
initial value `e0`. Snapshot `cr-2026-10-23`. Source:
`def:app-dyn-ode` (`section.tex` ll. 141–150):
```latex
\begin{definition}[Deterministic mode-energy equations]\label{def:app-dyn-ode}
For $i\le\Nout$ and $j\le\Nin$, the deterministic mode-energy equations are
\begin{equation}\label{eqn:app-dyn-ode}
\frac{\dif}{\dif\macrotime}\big(B^2\fQ_{ij}(\macrotime)\big)=-\frac{2\macrostep\,\mathfrak d_{ij}}{\sqrt{\fRisk(\macrotime)}}\,B^2\fQ_{ij}(\macrotime)+\macrostep^2B\,\mathfrak v_{ij},\qquad
\fRisk(\macrotime)\defeq\frac12\sum_{i,j}\mu_i\lambda_j\,\fQ_{ij}(\macrotime),
\end{equation}
with the initial values $\fQ_{ij}(0)=\CMscr Q_{ij}(0)=(u_i^\T\Delta_0v_j)^2$.
Their spectral energy measure is
$\chi^{\mathrm{ode}}(\macrotime)\defeq\sum_{i,j}\fQ_{ij}(\macrotime)\,\delta_{(\mu_i,\lambda_j)}$.
\end{definition}
```
-/
def IsDynOde {m n : ℕ} (h B : ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (d : ℝ × ℝ → ℝ)
    (v : Fin m → Fin n → ℝ) (T : ℝ) (e0 : Fin m → Fin n → ℝ) (e : ℝ → Fin m → Fin n → ℝ) : Prop :=
  e 0 = e0 ∧ ∀ τ ∈ Icc 0 T, HasDerivWithinAt e (odeRHS h B μ lam d v (e τ)) (Icc 0 T) τ

/-- Initial value of the mode-energy array, `e_ij(0) = B²(u_iᵀΔ_0 v_j)²` (`def:app-dyn-ode`). -/
def odeInit {m n : ℕ} {C : Covariances m n} (B : ℝ) (S : SpectralData C) (Δ0 : Mat m n) :
    Fin m → Fin n → ℝ :=
  fun i j => B ^ 2 * Muon.Setup.modeQ S Δ0 i j

/-- The measure `χ^ode(τ) = ∑ 𝒬_ij(τ) δ_{(μ_i,λ_j)}` read from `e(τ) = B²𝒬(τ)`. -/
def odeMeasure {m n : ℕ} (B : ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (e : Fin m → Fin n → ℝ) :
    Measure (ℝ × ℝ) :=
  atomMeasure μ lam (fun i j => e i j / B ^ 2)

/-- The actual spectral energy measure `χ^act(τ) = χ(Δ_{⌊Bτ⌋})` (l. 333). Here `Δ` is one path
`t ↦ Δ_t`; the random version composes with `Muon.Setup.devRand`. -/
def actMeasure {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (B : ℕ)
    (Δ : ℕ → Mat m n) (τ : ℝ) : Measure (ℝ × ℝ) :=
  specMeasure S (Δ ⌊(B : ℝ) * τ⌋₊)

/-! ## Coefficients and the drift and forcing data -/

/-- The coefficients of the deterministic equations at one dimension: the drift kernel `𝔡`, the
mode coefficients `𝔳_ij ≥ 0` and the forcing measure `ζ = B^{-1} ∑ 𝔳_ij δ_{(μ_i,λ_j)}`, with the
bounds of `eqn:app-dyn-coefficient-bounds` as fields (`𝔡` on `K`, `ζ(K) ≤ m_ζ`). Instantiated
later from `cor:app-drift-kernel` (C) and `prop:app-vol-disintegration` (D). Snapshot `cr-2026-10-23`.
Source (`eqn:app-dyn-coefficient-bounds`, ll. 117–122; `ζ` l. 109):
`eqn:app-dyn-coefficient-bounds` (`section.tex` ll. 117–123):
```latex
\begin{equation}\label{eqn:app-dyn-coefficient-bounds}
\begin{gathered}
0\le\mathfrak d\le\mathfrak d_{\max}\defeq\frac{C_\Sigma^2}{\sqrt{2\ridge}}\ \text{on }\mathbb K,\qquad
\abs{\mathfrak d(x)-\mathfrak d(y)}\le\frac{C_\Sigma}{\sqrt{2\ridge}}\abs{x-y}_1,\\
0\le\zeta(\mathbb K)\le m_\zeta\defeq\gamma_\star+\frac{2\mathsf K_\star\bmom}{1-\bmom}.
\end{gathered}
\end{equation}
```
-/
structure DynCoeff {m n : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    (B : ℕ) where
  /-- The drift kernel `𝔡 : K → ℝ`. -/
  d : ℝ × ℝ → ℝ
  d_nonneg : ∀ x ∈ specRect p.CSig, 0 ≤ d x
  d_le : ∀ x ∈ specRect p.CSig, d x ≤ dMax p
  d_lip : ∀ x ∈ specRect p.CSig, ∀ y ∈ specRect p.CSig,
    |d x - d y| ≤ p.CSig / Real.sqrt (2 * p.ϱ) * l1 x y
  /-- The mode coefficients `𝔳_ij`. -/
  v : Fin m → Fin n → ℝ
  v_nonneg : ∀ i j, 0 ≤ v i j
  /-- The forcing measure `ζ`. -/
  ζ : Measure (ℝ × ℝ)
  ζ_eq : ζ = atomMeasure S.μ S.lam (fun i j => v i j / (B : ℝ))
  ζ_mass : ζ.real univ ≤ mZeta p

/-! ## Hypotheses of the main theorem -/

/-- Hypotheses (H1)–(H4) of `thm:app-dyn-main`, along a sequence of dimensions indexed by `k`
(`m k = N_out`, `n k = N_in`, `B k`). The source text, ll. 340–352:
(`section.tex` ll. 340–352):
```latex
\begin{enumerate}[label=(H\arabic*)]
\item \label{hyp:app-dyn-data} \cref{assum:data-target,assum:proportional-regime}
hold with deterministic covariances, $\max(\Nin,\Nout)\le\gamma_\star B$
and $\norm{\Sigmain},\norm{\Sigmaout}\le C_\Sigma$;
\item \label{hyp:app-dyn-algorithm} the algorithm of
\cref{def:app-setup-algorithm} is run with momentum $\bmom$, normalized
ridge $\ridge$ and step $\lr_t=\macrostep/B$;
\item \label{hyp:app-dyn-initial} $W_0$ is deterministic,
$\norm{\Delta_0}_\F^2\le E_\star$, $r_0\le\cR(0)\le r_1$, and
$\norm{\widehat A_0}\to0$;
\item \label{hyp:app-dyn-buffer} the initial buffer $M^\circ_{-1}$ is
independent of all batches and $\EE\norm{M^\circ_{-1}}_\F^2\le c_MB$.
\end{enumerate}
```
Field groups: (H1) `hyp:app-dyn-data`, (H2) `hyp:app-dyn-algorithm`, (H3) `hyp:app-dyn-initial`,
(H4) `hyp:app-dyn-buffer`. The batch process `x k t` (the batch of step `t`) is part of (H1). -/
structure DynHyp (p : DynParams) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (m n B : ℕ → ℕ) (C : ∀ k : ℕ, Covariances (m k) (n k)) where
  -- (H1) `hyp:app-dyn-data`
  regime : ProportionalRegime m n B C
  dims : ∀ k : ℕ, ((max (m k) (n k) : ℕ) : ℝ) ≤ p.γstar * (B k : ℝ)
  normBd : ∀ k : ℕ, opNorm (C k).Sin ≤ p.CSig ∧ opNorm (C k).Sout ≤ p.CSig
  x : ∀ k : ℕ, ℕ → Ω → Batch (m k) (n k) (B k)
  iid : ∀ k t, IIDBatch P (dataTarget (C k)) (fun a ω => x k t ω a)
  steps_indep : ∀ k : ℕ, iIndepFun (fun t => x k t) P
  -- (H2) `hyp:app-dyn-algorithm`: momentum β, ridge ϱ, step h/B
  alg : ∀ k : ℕ, AlgParams (m k) (n k)
  alg_β : ∀ k, (alg k).β = p.β
  alg_ϱ : ∀ k, (alg k).ϱ = p.ϱ
  alg_η : ∀ k t, (alg k).η t = p.h / (B k : ℝ)
  -- (H3) `hyp:app-dyn-initial`: deterministic W₀, ‖Δ₀‖_F² ≤ E⋆, r₀ ≤ 𝓡(0) ≤ r₁, ‖Â₀‖ → 0
  W0 : ∀ k : ℕ, Mat (m k) (n k)
  W0_norm : ∀ k, fro (W0 k - (alg k).Wstar) ^ 2 ≤ p.Estar
  W0_risk : ∀ k, p.r0 ≤ riskSigma (C k) (W0 k - (alg k).Wstar) ∧
    riskSigma (C k) (W0 k - (alg k).Wstar) ≤ p.r1
  W0_hat : Tendsto (fun k => opNorm (Ahat (C k) (W0 k - (alg k).Wstar))) atTop (𝓝 0)
  -- (H4) `hyp:app-dyn-buffer`: initial buffer M°₋₁ independent of all batches, E‖M°₋₁‖_F² ≤ c_M B
  Mm1 : ∀ k : ℕ, Ω → Mat (m k) (n k)
  Mm1_meas : ∀ k : ℕ, AEMeasurable (Mm1 k) P
  Mm1_indep : ∀ k : ℕ, IndepFun (Mm1 k) (fun ω t => x k t ω) P
  Mm1_bound : ∀ k : ℕ, ∫⁻ ω, ENNReal.ofReal (fro (Mm1 k ω) ^ 2) ∂P ≤ ENNReal.ofReal (p.cM * B k)

/-! ## Minibatch gradient, normalized state and diffuseness -/

/-- The batch gradient `G°_{t+1}[E] = (1/B) ∑_a (z_aᵀ Σ_out^{1/2} E Σ_in^{1/2} w_a)
Σ_out^{1/2}(z_a ⊗ w_a) Σ_in^{1/2}` of `eqn:app-dyn-batch` (l. 44–46). The batch is physical
(`X = Σ^{1/2} z`), so this is the minibatch gradient `Muon.Setup.grad` of `eqn:app-setup-gradient`;
it is reused, not redefined. Linear in `E`. -/
abbrev batchGrad {m n B : ℕ} (E : Mat m n) (b : Batch m n B) : Mat m n := Muon.Setup.grad E b

/-- The normalized state `Â(Δ) = Σ_out^{1/2} Δ Σ_in^{1/2} / √(2𝓡(Δ))` (`eqn:app-dyn-diffuse`,
l. 67–69), which is `Muon.Setup.Ahat`. At zero risk Lean gives `0`. -/
abbrev normState {m n : ℕ} (C : Covariances m n) (Δ : Mat m n) : Mat m n := Ahat C Δ

/-- Diffuseness `δ(Δ) = ‖Â(Δ)‖` (`eqn:app-dyn-diffuse`). Snapshot `cr-2026-10-23`. Source:
`eqn:app-dyn-diffuse` (`section.tex` ll. 67–70):
```latex
\begin{equation}\label{eqn:app-dyn-diffuse}
\widehat A(\Delta)\defeq\frac{\Sigmaout^{1/2}\Delta\Sigmain^{1/2}}{\sqrt{2\cR(\Delta)}},\qquad
\delta(\Delta)\defeq\norm{\widehat A(\Delta)} ,
\end{equation}
```
-/
def diffuseness {m n : ℕ} (C : Covariances m n) (Δ : Mat m n) : ℝ := opNorm (normState C Δ)

/-- Physical ridge `ϱ°(Δ) = 2𝓡(Δ)ϱ` (`eqn:app-dyn-algorithm`, l. 52). -/
def physRidge {m n : ℕ} (p : DynParams) (C : Covariances m n) (Δ : Mat m n) : ℝ :=
  2 * riskSigma C Δ * p.ϱ

/-- The selfadjoint map `𝒲_{f,g} X = f(Σ_out) X g(Σ_in)` (`eqn:app-dyn-test`, l. 84), by the
continuous functional calculus of the covariances. Snapshot `cr-2026-10-23`. Source:
(`section.tex` ll. 83–85):
```latex
For bounded functions $f,g$ on $[0,C_\Sigma]$ we write
$\mathcal W_{f,g}X\defeq f(\Sigmaout)\,X\,g(\Sigmain)$, a linear map on
$\R^{\Nout\times\Nin}$ which is selfadjoint for the Frobenius pairing
```
-/
def wfg {m n : ℕ} (f g : ℝ → ℝ) (C : Covariances m n) (X : Mat m n) : Mat m n :=
  cfc f C.Sout * X * cfc g C.Sin

/-- The normalized states `𝒮_B = {Â(Δ) : 𝓡(Δ) > 0}` of the frozen-state model. -/
def NormStates {m n : ℕ} (C : Covariances m n) : Set (Mat m n) :=
  {A | ∃ Δ : Mat m n, 0 < riskSigma C Δ ∧ A = normState C Δ}

/-- The sets `𝒦(r₋, r₊, E) = {Δ : r₋ ≤ 𝓡(Δ) ≤ r₊, ‖Δ‖_F² ≤ E}`, indexed by the triple
`(r₋, r₊, E)`. Snapshot `cr-2026-10-23`. Source:
(`section.tex` ll. 1475–1476):
```latex
\paragraph{Blocks and admissible states.}
For $0<r_-\le r_+$ and $E<\infty$ let
```
-/
def admSetOf {m n : ℕ} (C : Covariances m n) (t : ℝ × ℝ × ℝ) : Set (Mat m n) :=
  {Δ | t.1 ≤ riskSigma C Δ ∧ riskSigma C Δ ≤ t.2.1 ∧ fro Δ ^ 2 ≤ t.2.2}

/-- The enlargement `𝒦' = 𝒦(r₋/2, 2r₊, 2E + 2)` (l. 1477) on triples. -/
def enl (t : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (t.1 / 2, 2 * t.2.1, 2 * t.2.2 + 2)

/-- The base triple `(r₀/2, r₁ + ½, E⋆ + 1)` of `𝒜` (l. 1479). -/
def admBase (p : DynParams) : ℝ × ℝ × ℝ := (p.r0 / 2, p.r1 + 1 / 2, p.Estar + 1)

/-- `𝒜 = 𝒦(r₀/2, r₁+½, E⋆+1)`, `𝒜⁺ = 𝒜'`, `𝒜⁺⁺ = (𝒜⁺)'` (l. 1479). -/
def admA {m n : ℕ} (p : DynParams) (C : Covariances m n) : Set (Mat m n) :=
  admSetOf C (admBase p)
def admAplus {m n : ℕ} (p : DynParams) (C : Covariances m n) : Set (Mat m n) :=
  admSetOf C (enl (admBase p))
def admAplusplus {m n : ℕ} (p : DynParams) (C : Covariances m n) : Set (Mat m n) :=
  admSetOf C (enl (enl (admBase p)))

end Muon.Dynamics

end

import Muon.Foundations.Conventions
import ProbabilityFoundations.Freezing

/-!
# Foundations: freezing lemma and entrywise matrix conditional expectation

Work package L-A.F3 (interface draft). Snapshot `cr-2026-10-23`. Helper package with no paper
label: the freezing lemma (`X` 𝒢-measurable, `Y` independent of 𝒢 ⇒ `E[f(X,Y) | 𝒢] = g(X)` with
`g(x) = E f(x,Y)`) and the entrywise matrix conditional expectation `condExpMat`, which is the
convention of `sections/01-setup/section.tex` l.39 ("expectations of matrices are entrywise").

Consumers: A `prop:app-setup-moments`(iii), `prop:app-setup-normalization`(ii),
`cor:app-setup-augmented` (last sentence), via `Muon.Setup.Model` and `Muon.Setup.Algorithm`.

Mathlib reuse: `MeasureTheory.condExp`, `MeasureTheory.condExp_indep_eq` (scalar, `m₁`
independent of `m₂`, `f` `m₁`-measurable), `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`,
`ProbabilityTheory.indep_of_indep_of_le_left`,
`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`.
Mathlib has no freezing lemma in this form (only the `condDistrib` representation
`condExp_prod_ae_eq_integral_condDistrib`, which conditions on `X` rather than on 𝒢).

All proofs are `sorry` (statements only); proof routes are in
`phases-of-muon/appendix-nodes/results/L-A.F3-interface.json`.
-/

open scoped Matrix MatrixOrder
open MeasureTheory ProbabilityTheory

noncomputable section

namespace Muon.Foundations

variable {Ω α β : Type*}

/-! ## Entrywise matrix conditional expectation -/

/-- Entrywise conditional expectation `E[X | 𝒢]` of a random matrix `X : Ω → Mat m n`: the
`(i, j)` entry is the scalar conditional expectation of `X_{ij}`. The result is a random matrix
(defined almost everywhere, as `condExp` is). -/
def condExpMat {m n : ℕ} (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (X : Ω → Mat m n) : Ω → Mat m n :=
  fun ω => Matrix.of fun i j => condExp 𝒢 μ (fun ω' => X ω' i j) ω

theorem condExpMat_eq_foundations {m n : ℕ} (𝒢 : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} (μ : Measure Ω) (X : Ω → Mat m n) :
    condExpMat 𝒢 μ X = ProbabilityFoundations.condExpMat 𝒢 μ X := rfl

/-- Entrywise reading of `condExpMat`. -/
theorem condExpMat_apply {m n : ℕ} (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (X : Ω → Mat m n) (ω : Ω) (i : Fin m) (j : Fin n) :
    condExpMat 𝒢 μ X ω i j = condExp 𝒢 μ (fun ω' => X ω' i j) ω :=
  ProbabilityFoundations.condExpMat_apply 𝒢 μ X ω i j

/-- `condExpMat` respects almost-everywhere equality of matrix-valued random variables. -/
theorem condExpMat_congr_ae {m n : ℕ} (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {X X' : Ω → Mat m n} (h : X =ᵐ[μ] X') :
    condExpMat 𝒢 μ X =ᵐ[μ] condExpMat 𝒢 μ X' :=
  ProbabilityFoundations.condExpMat_congr_ae 𝒢 h

/-- Independence: if the entries of `X` are measurable for a σ-algebra `𝒢'` independent of
𝒢, then `E[X | 𝒢]` is almost everywhere the entrywise mean `Muon.mean μ X`. -/
theorem condExpMat_indep_eq {m n : ℕ} (𝒢 𝒢' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h𝒢 : 𝒢 ≤ mΩ) (h𝒢' : 𝒢' ≤ mΩ)
    {X : Ω → Mat m n} (hX : ∀ i j, Measurable[𝒢'] fun ω => X ω i j)
    (hind : Indep 𝒢' 𝒢 μ) :
    condExpMat 𝒢 μ X =ᵐ[μ] fun _ => Muon.mean μ X :=
  ProbabilityFoundations.condExpMat_indep_eq 𝒢 𝒢' h𝒢 h𝒢' hX hind

/-! ## Freezing lemma -/

/-- Freezing lemma, scalar form. Let `X` be 𝒢-measurable and `Y` independent of 𝒢, and let
`f(x, y)` be jointly measurable with `f(X, Y)` integrable. Then `E[f(X,Y) | 𝒢]` equals, almost
everywhere, `ω ↦ ∫ f(X ω, y) dP_Y(y)`, where `P_Y = μ.map Y` is the law of `Y`. -/
theorem freezing_condExp (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [mα : MeasurableSpace α] [mβ : MeasurableSpace β] (h𝒢 : 𝒢 ≤ mΩ)
    {X : Ω → α} {Y : Ω → β} (hX : Measurable[𝒢] X) (hY : Measurable Y)
    (hind : Indep 𝒢 (MeasurableSpace.comap Y mβ) μ)
    {f : α → β → ℝ} (hf : Measurable (Function.uncurry f))
    (hfint : Integrable (fun ω => f (X ω) (Y ω)) μ) :
    condExp 𝒢 μ (fun ω => f (X ω) (Y ω)) =ᵐ[μ] fun ω => ∫ y, f (X ω) y ∂(μ.map Y) :=
  ProbabilityFoundations.freezing_condExp 𝒢 h𝒢 hX hY hind hf hfint

/-- Freezing lemma, matrix form. The entrywise version of `freezing_condExp`: for a family
`F x y : Mat m n` with jointly measurable entries and integrable `F(X,Y)` entries, the entrywise
conditional expectation `condExpMat 𝒢 μ (F(X,Y))` is almost everywhere the entrywise mean
`Muon.mean (μ.map Y) (F (X ω))` of `y ↦ F (X ω) y` under the law of `Y`. -/
theorem freezing_condExpMat {m n : ℕ} (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    (h𝒢 : 𝒢 ≤ mΩ)
    {X : Ω → α} {Y : Ω → β} (hX : Measurable[𝒢] X) (hY : Measurable Y)
    (hind : Indep 𝒢 (MeasurableSpace.comap Y mβ) μ)
    {F : α → β → Mat m n} (hF : ∀ i j, Measurable (Function.uncurry fun x y => F x y i j))
    (hfint : ∀ i j, Integrable (fun ω => F (X ω) (Y ω) i j) μ) :
    condExpMat 𝒢 μ (fun ω => F (X ω) (Y ω)) =ᵐ[μ]
      fun ω => Muon.mean (μ.map Y) (fun y => F (X ω) y) :=
  ProbabilityFoundations.freezing_condExpMat 𝒢 h𝒢 hX hY hind hF hfint

end Muon.Foundations

end

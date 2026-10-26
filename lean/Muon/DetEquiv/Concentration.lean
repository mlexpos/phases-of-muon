import Muon.DetEquiv.SampleModel
import Muon.DetEquiv.Gaussian
import Muon.DetEquiv.Resolvent
import Muon.DetEquiv.Scalar
import Muon.Foundations.Probability

/-!
# Appendix B: concentration of the deleted-sample quantities (task L-B.8)

Snapshot `cr-2026-10-23`. Source: `sections/02-deterministic-equivalents/section.tex`, the labels
`lem:app-de-variance` (l.1207–1213; part (iv) is the input side of the deleted buffer),
`lem:app-de-scalars` (l.1267–1272) and
`lem:app-de-replace` (l.1326–1341), with the targets `eqn:app-de-targets` (l.1327–1333) and the
expected resolvents `eqn:app-de-expected` (l.1193–1201). CARD §5 WP L-B.8.

Reuse, nothing redefined: `WeightClass`, `sumPow` (`DetEquiv.Scalar`); `WeightedBuf`,
`WeightedBufDel`, `sigmaB`, `sigmaTildeB`, `qB`, `FrozenSamples` (`DetEquiv.SampleModel`,
`Setup.Frozen`); `momU`, `momV` (`DetEquiv.Gaussian`: `u = Σout^{1/2} z/√B`, `v = Σin^{1/2} w/√B`);
`Rs`, `delU`, `delV`, `delC`, `alpha1`, `alpha2`, `alpha3` (`DetEquiv.Resolvent`); `opNorm`
(`Foundations.Conventions`).

Representation choices:
* Complex test matrices `T`: the real resolvent is embedded by `Matrix.map`; the complex variance
  `E|Y − EY|²` is `cVar`, since `ProbabilityTheory.variance` is real-valued.
* Every L² norm is `eLpNorm _ 2 P` (no junk value from non-integrable integrands).
* The constants `C_I` are existential, chosen from `(I, C_Σ, γ⋆)` before the model, so they are
  uniform over all `(m, n, B, w, Ω, P, S, t)` satisfying the stated hypotheses.
* `e_B` of `lem:app-de-replace` is existential in the statement. The source defines it inside the
  proof as the maximum of three suprema (l.1458–1460), so it is not a statement object.
* Paper's slot `a = 1` is `slotOne F.hB : Fin B`, i.e. index `0`.
* The §B.3 ambient hypotheses (CARD §6.5) are explicit: `I` compact in `(0,∞)`, `WeightClass w`,
  `opNorm F.C.Sout, opNorm F.C.Sin ≤ C_Σ`, `m, n ≤ γ⋆ B`, `IsProbabilityMeasure P`, and the sample
  law carried by `FrozenSamples`.
-/

set_option linter.style.longLine false

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set
open Matrix
open Muon Muon.Setup

noncomputable section

namespace Muon.DetEquiv

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Helpers (no contract beyond their docstrings) -/

/-- Complex variance `E|Y − EY|²` of a complex random variable `Y` (the source's `Var Y`
for complex `Y`, `lem:app-de-variance`). Valued in `[0, ∞]`. -/
def cVar (P : Measure Ω) (Y : Ω → ℂ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (‖Y ω - ∫ ω', Y ω' ∂P‖ ^ 2) ∂P

/-- Normalized trace `(1/B) Tr(T R)` of a complex test matrix `T` against a real resolvent `R`
(`lem:app-de-variance`: `Y(s) = (1/B) Tr(T R(-s))`). -/
def normTrace {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) (B : ℕ) (R : Mat k k) : ℂ :=
  (B : ℂ)⁻¹ * Matrix.trace (T * R.map (fun x : ℝ => (x : ℂ)))

/-- `f_x(d) = d/(1+xd²)` (`eqn:app-de-targets`, `lem:app-de-replace`). -/
def fX (x d : ℝ) : ℝ := d / (1 + x * d ^ 2)

/-- `ψ_x(d) = d²/(1+xd²)` (`eqn:app-de-targets`, `lem:app-de-replace`). -/
def psiX (x d : ℝ) : ℝ := d ^ 2 / (1 + x * d ^ 2)

/-- The paper's slot `a = 1`, as the index `0 : Fin B`. -/
def slotOne {B : ℕ} (hB : 0 < B) : Fin B := ⟨0, hB⟩

/-- Sample scalar `d_{sa} = z_{sa}ᵀ Â w_{sa}` (`eqn:app-setup-frozen-objects`). -/
def sampleD {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (s : ℤ) (a : Fin B) (ω : Ω) : ℝ :=
  dotProduct (S.zw s a ω).1 (Matrix.mulVec F.A (S.zw s a ω).2)

/-- Age-`j` sample scalar `d_j = d_{t+1-j, 1}` at time `t`. -/
def ageD {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (ω : Ω) : ℝ :=
  sampleD F S (t + 1 - (j : ℤ)) (slotOne F.hB) ω

/-- Age-`j` output vector `u_j = Σout^{1/2} z_j/√B` in slot `1` (`momU`). -/
def ageU {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (ω : Ω) : Vec m :=
  momU F.C B (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω)

/-- Age-`j` input vector `v_j = Σin^{1/2} w_j/√B` in slot `1` (`momV`). -/
def ageV {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (ω : Ω) : Vec n :=
  momV F.C B (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω)

/-- The buffer `M_0^{(j1)}` with the age-`j` sample in slot `1` deleted, at time `t`
(`eqn:app-de-expected`, `lem:app-de-scalars`, `lem:app-de-replace`). -/
def delBufAge {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (ω : Ω) : Mat m n :=
  WeightedBufDel w F S t (t + 1 - (j : ℤ)) (slotOne F.hB) ω

/-- Deleted-sample coefficient `α_{1,j} = alpha1 (M_0^{(j1)}) (w_j d_j) u_j v_j` at `s`
(`eqn:app-de-coefficients` with `𝗁 = w_j d_j`, `eqn:app-de-replace`). -/
def delAlpha1 {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  alpha1 (delBufAge w F S t j ω) (w j * ageD F S t j ω) (ageU F S t j ω) (ageV F S t j ω) s

/-- Deleted-sample coefficient `α_{2,j}` (`eqn:app-de-coefficients`). -/
def delAlpha2 {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  alpha2 (delBufAge w F S t j ω) (w j * ageD F S t j ω) (ageU F S t j ω) (ageV F S t j ω) s

/-- Deleted-sample coefficient `α_{3,j}` (`eqn:app-de-coefficients`). -/
def delAlpha3 {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  alpha3 (delBufAge w F S t j ω) (w j * ageD F S t j ω) (ageU F S t j ω) (ageV F S t j ω) s

/-- `eqn:app-de-targets`, snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.1327–1333):
For $x\ge0$ put $f_x(d)\defeq\frac{d}{1+xd^2}$ and $\psi_x(d)\defeq\frac{d^2}{1+xd^2}$,
and for a sample of age $j$ and $s\in I$ define the target coefficients
\begin{equation}\label{eqn:app-de-targets}
\check\alpha_{1,j}\defeq\emaw j\,f_{\emaw j^2q_B}(d_j),\qquad
\check\alpha_{2,j}\defeq\emaw j^2\,\sigma_B\,\psi_{\emaw j^2q_B}(d_j),\qquad
\check\alpha_{3,j}\defeq-s\,\emaw j^2\,\tilde\sigma_B\,\psi_{\emaw j^2q_B}(d_j).
\end{equation}
-/
def checkAlpha1 {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  w j * fX (w j ^ 2 * qB w F S t s) (ageD F S t j ω)

/-- Target `α̌_{2,j} = w_j² σ_B(s) ψ_{w_j² q_B(s)}(d_j)` (`eqn:app-de-targets`). -/
def checkAlpha2 {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  w j ^ 2 * sigmaB w F S t s * psiX (w j ^ 2 * qB w F S t s) (ageD F S t j ω)

/-- Target `α̌_{3,j} = −s w_j² σ̃_B(s) ψ_{w_j² q_B(s)}(d_j)` (`eqn:app-de-targets`). -/
def checkAlpha3 {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  -(s * (w j ^ 2 * sigmaTildeB w F S t s * psiX (w j ^ 2 * qB w F S t s) (ageD F S t j ω)))



/-! ## Private machinery for `lem:app-de-variance` -/

section ESslot

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [MeasurableSpace X]

private lemma pb8_update_meas (i : ι) :
    Measurable (fun p : (ι → X) × (ι → X) => Function.update p.1 i (p.2 i)) := by
  refine measurable_pi_iff.2 fun k => ?_
  by_cases h : k = i
  · subst h
    simp only [Function.update_self]
    exact (measurable_pi_apply _).comp measurable_snd
  · simp only [Function.update_of_ne h]
    exact (measurable_pi_apply _).comp measurable_fst

private lemma pb8_es_slot (μ0 : Measure X) [IsProbabilityMeasure μ0]
    (f : (ι → X) → ℝ) (hfm : Measurable f) (Bd : ℝ) (hfb : ∀ x, |f x| ≤ Bd)
    (c : ι → ℝ) (h : X → ℝ) (hhm : Measurable h) (hh2 : Integrable (fun x => h x ^ 2) μ0)
    (hdiff : ∀ (i : ι) (p q : ι → X),
      |f p - f (Function.update p i (q i))| ≤ |c i| * (|h (p i)| + |h (q i)|)) :
    variance f (Measure.pi fun _ : ι => μ0) ≤ 2 * (∫ x, h x ^ 2 ∂μ0) * ∑ i, c i ^ 2 := by
  have hf2 : MemLp f 2 (Measure.pi fun _ : ι => μ0) :=
    MemLp.of_bound hfm.aestronglyMeasurable Bd
      (Filter.Eventually.of_forall fun x => by simpa using hfb x)
  refine (Muon.Foundations.efron_stein (fun _ => μ0) f hf2).trans ?_
  set ν := (Measure.pi fun _ : ι => μ0).prod (Measure.pi fun _ : ι => μ0) with hν
  haveI : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  have hslot : ∀ i : ι, ∫ p, (f p.1 - f (Function.update p.1 i (p.2 i))) ^ 2 ∂ν ≤
      4 * c i ^ 2 * ∫ x, h x ^ 2 ∂μ0 := by
    intro i
    have hm1 : MeasurePreserving (fun p : (ι → X) × (ι → X) => p.1 i) ν μ0 :=
      (measurePreserving_eval (fun _ : ι => μ0) i).comp measurePreserving_fst
    have hm2 : MeasurePreserving (fun p : (ι → X) × (ι → X) => p.2 i) ν μ0 :=
      (measurePreserving_eval (fun _ : ι => μ0) i).comp measurePreserving_snd
    have hhsq : Measurable (fun x => h x ^ 2) := hhm.pow_const 2
    have i1 : Integrable (fun p : (ι → X) × (ι → X) => h (p.1 i) ^ 2) ν :=
      (hm1.integrable_comp hhsq.aestronglyMeasurable).2 hh2
    have i2 : Integrable (fun p : (ι → X) × (ι → X) => h (p.2 i) ^ 2) ν :=
      (hm2.integrable_comp hhsq.aestronglyMeasurable).2 hh2
    have e1 : ∫ p, h (p.1 i) ^ 2 ∂ν = ∫ x, h x ^ 2 ∂μ0 := by
      have := integral_map (μ := ν) hm1.aemeasurable (f := fun x => h x ^ 2)
        hhsq.aestronglyMeasurable
      rw [hm1.map_eq] at this
      exact this.symm
    have e2 : ∫ p, h (p.2 i) ^ 2 ∂ν = ∫ x, h x ^ 2 ∂μ0 := by
      have := integral_map (μ := ν) hm2.aemeasurable (f := fun x => h x ^ 2)
        hhsq.aestronglyMeasurable
      rw [hm2.map_eq] at this
      exact this.symm
    have hfu : Measurable (fun p : (ι → X) × (ι → X) =>
        (f p.1 - f (Function.update p.1 i (p.2 i))) ^ 2) :=
      ((hfm.comp measurable_fst).sub (hfm.comp (pb8_update_meas i))).pow_const 2
    have hint : Integrable (fun p : (ι → X) × (ι → X) =>
        (f p.1 - f (Function.update p.1 i (p.2 i))) ^ 2) ν := by
      refine Integrable.of_bound hfu.aestronglyMeasurable ((2 * Bd) ^ 2)
        (Filter.Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := hfb p.1
      have h2 := hfb (Function.update p.1 i (p.2 i))
      have hb : |f p.1 - f (Function.update p.1 i (p.2 i))| ≤ 2 * Bd := by
        calc _ ≤ |f p.1| + |f (Function.update p.1 i (p.2 i))| := abs_sub _ _
          _ ≤ 2 * Bd := by linarith
      calc (f p.1 - f (Function.update p.1 i (p.2 i))) ^ 2
          = |f p.1 - f (Function.update p.1 i (p.2 i))| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * Bd) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    calc ∫ p, (f p.1 - f (Function.update p.1 i (p.2 i))) ^ 2 ∂ν
        ≤ ∫ p, 2 * c i ^ 2 * (h (p.1 i) ^ 2 + h (p.2 i) ^ 2) ∂ν := by
          refine integral_mono hint ((i1.add i2).const_mul _) fun p => ?_
          have hd := hdiff i p.1 p.2
          have hsq : (f p.1 - f (Function.update p.1 i (p.2 i))) ^ 2 ≤
              (|c i| * (|h (p.1 i)| + |h (p.2 i)|)) ^ 2 :=
            (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) hd 2)
          refine hsq.trans ?_
          have : (|c i| * (|h (p.1 i)| + |h (p.2 i)|)) ^ 2 =
              c i ^ 2 * (|h (p.1 i)| + |h (p.2 i)|) ^ 2 := by
            rw [mul_pow, sq_abs]
          rw [this]
          have h3 : (|h (p.1 i)| + |h (p.2 i)|) ^ 2 ≤ 2 * (h (p.1 i) ^ 2 + h (p.2 i) ^ 2) := by
            nlinarith [sq_nonneg (|h (p.1 i)| - |h (p.2 i)|), sq_abs (h (p.1 i)), sq_abs (h (p.2 i))]
          nlinarith [sq_nonneg (c i)]
      _ = 2 * c i ^ 2 * (∫ x, h x ^ 2 ∂μ0 + ∫ x, h x ^ 2 ∂μ0) := by
          rw [integral_const_mul, integral_add i1 i2, e1, e2]
      _ = 4 * c i ^ 2 * ∫ x, h x ^ 2 ∂μ0 := by ring
  calc (1 / 2 : ℝ) * ∑ i, ∫ p, (f p.1 - f (Function.update p.1 i (p.2 i))) ^ 2 ∂ν
      ≤ (1 / 2 : ℝ) * ∑ i, 4 * c i ^ 2 * ∫ x, h x ^ 2 ∂μ0 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hslot i) (by norm_num)
    _ = 2 * (∫ x, h x ^ 2 ∂μ0) * ∑ i, c i ^ 2 := by
        rw [← Finset.sum_mul]
        have : ∑ i, 4 * c i ^ 2 = 4 * ∑ i, c i ^ 2 := by rw [Finset.mul_sum]
        rw [this]; ring

end ESslot

section CVarLemmas

variable {Ω' : Type*} [MeasurableSpace Ω']

private lemma pb8_cVar_eq (P : Measure Ω') [IsProbabilityMeasure P] (Y : Ω' → ℂ)
    (hm : Measurable Y) (Bd : ℝ) (hb : ∀ ω, ‖Y ω‖ ≤ Bd) :
    cVar P Y = ENNReal.ofReal
      (variance (fun ω => (Y ω).re) P + variance (fun ω => (Y ω).im) P) := by
  have hint : Integrable Y P :=
    Integrable.of_bound hm.aestronglyMeasurable Bd (Filter.Eventually.of_forall hb)
  have hre : Measurable (fun ω => (Y ω).re) := Complex.measurable_re.comp hm
  have him : Measurable (fun ω => (Y ω).im) := Complex.measurable_im.comp hm
  have hre1 : (∫ ω, Y ω ∂P).re = ∫ ω, (Y ω).re ∂P := by
    have := integral_re (μ := P) hint
    simpa using this.symm
  have him1 : (∫ ω, Y ω ∂P).im = ∫ ω, (Y ω).im ∂P := by
    have := integral_im (μ := P) hint
    simpa using this.symm
  have hv1 := variance_eq_integral (μ := P) hre.aemeasurable
  have hv2 := variance_eq_integral (μ := P) him.aemeasurable
  have hbre : ∀ ω, |(Y ω).re| ≤ Bd := fun ω => (Complex.abs_re_le_norm _).trans (hb ω)
  have hbim : ∀ ω, |(Y ω).im| ≤ Bd := fun ω => (Complex.abs_im_le_norm _).trans (hb ω)
  have hint_re : Integrable (fun ω => (Y ω).re) P :=
    Integrable.of_bound hre.aestronglyMeasurable Bd
      (Filter.Eventually.of_forall fun ω => by simpa using hbre ω)
  have hint_im : Integrable (fun ω => (Y ω).im) P :=
    Integrable.of_bound him.aestronglyMeasurable Bd
      (Filter.Eventually.of_forall fun ω => by simpa using hbim ω)
  have hsq : ∀ (f : Ω' → ℝ), Measurable f → Integrable f P → (∀ ω, |f ω| ≤ Bd) →
      Integrable (fun ω => (f ω - ∫ ω', f ω' ∂P) ^ 2) P := by
    intro f hf hfi hfb
    refine Integrable.of_bound ((hf.sub_const _).pow_const 2).aestronglyMeasurable
      ((Bd + Bd) ^ 2) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hc : |∫ ω', f ω' ∂P| ≤ Bd := by
      have := norm_integral_le_of_norm_le_const (μ := P) (f := f) (C := Bd)
        (Filter.Eventually.of_forall fun ω => by simpa using hfb ω)
      simpa using this
    have : |f ω - ∫ ω', f ω' ∂P| ≤ Bd + Bd :=
      (abs_sub _ _).trans (add_le_add (hfb ω) hc)
    calc (f ω - ∫ ω', f ω' ∂P) ^ 2 = |f ω - ∫ ω', f ω' ∂P| ^ 2 := (sq_abs _).symm
      _ ≤ (Bd + Bd) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have h1 := hsq _ hre hint_re hbre
  have h2 := hsq _ him hint_im hbim
  unfold cVar
  have hpt : ∀ ω, ENNReal.ofReal (‖Y ω - ∫ ω', Y ω' ∂P‖ ^ 2) =
      ENNReal.ofReal ((((Y ω).re - ∫ ω', (Y ω').re ∂P) ^ 2)) +
        ENNReal.ofReal ((((Y ω).im - ∫ ω', (Y ω').im ∂P) ^ 2)) := by
    intro ω
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), Complex.sq_norm, Complex.normSq_apply]
    congr 1
    simp only [Complex.sub_re, Complex.sub_im, hre1, him1]
    ring
  simp_rw [hpt]
  rw [lintegral_add_left ((hre.sub_const _).pow_const 2).ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal h1 (Filter.Eventually.of_forall fun ω => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal h2 (Filter.Eventually.of_forall fun ω => sq_nonneg _),
    ← ENNReal.ofReal_add (integral_nonneg fun ω => sq_nonneg _)
      (integral_nonneg fun ω => sq_nonneg _), hv1, hv2]

end CVarLemmas

section CVarLimit

variable {Ω' : Type*} [MeasurableSpace Ω']

private lemma pb8_cVar_limit (P : Measure Ω') [IsProbabilityMeasure P] (Y : ℕ → Ω' → ℂ)
    (Yinf : Ω' → ℂ) (hm : ∀ J, Measurable (Y J)) (Bd : ℝ) (hb : ∀ J ω, ‖Y J ω‖ ≤ Bd)
    (hlim : ∀ᵐ ω ∂P, Filter.Tendsto (fun J => Y J ω) Filter.atTop (nhds (Yinf ω)))
    (K : ℝ) (hK : ∀ J, cVar P (Y J) ≤ ENNReal.ofReal K) :
    cVar P Yinf ≤ ENNReal.ofReal K := by
  have hc : Filter.Tendsto (fun J => ∫ ω, Y J ω ∂P) Filter.atTop (nhds (∫ ω, Yinf ω ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ => Bd)
      (fun J => (hm J).aestronglyMeasurable) (integrable_const Bd)
      (fun J => Filter.Eventually.of_forall fun ω => hb J ω) hlim
  have hpt : ∀ᵐ ω ∂P, Filter.Tendsto
      (fun J => ENNReal.ofReal (‖Y J ω - ∫ ω', Y J ω' ∂P‖ ^ 2)) Filter.atTop
      (nhds (ENNReal.ofReal (‖Yinf ω - ∫ ω', Yinf ω' ∂P‖ ^ 2))) := by
    filter_upwards [hlim] with ω hω
    refine ENNReal.tendsto_ofReal ?_
    have h1 : Filter.Tendsto (fun J => Y J ω - ∫ ω', Y J ω' ∂P) Filter.atTop
        (nhds (Yinf ω - ∫ ω', Yinf ω' ∂P)) := hω.sub hc
    exact (h1.norm).pow 2
  unfold cVar
  calc ∫⁻ ω, ENNReal.ofReal (‖Yinf ω - ∫ ω', Yinf ω' ∂P‖ ^ 2) ∂P
      = ∫⁻ ω, Filter.liminf (fun J => ENNReal.ofReal (‖Y J ω - ∫ ω', Y J ω' ∂P‖ ^ 2))
          Filter.atTop ∂P :=
        lintegral_congr_ae (hpt.mono fun ω h => h.liminf_eq.symm)
    _ ≤ Filter.liminf (fun J => ∫⁻ ω, ENNReal.ofReal (‖Y J ω - ∫ ω', Y J ω' ∂P‖ ^ 2) ∂P)
          Filter.atTop :=
        lintegral_liminf_le (fun J => (((hm J).sub_const _).norm.pow_const 2).ennreal_ofReal)
    _ ≤ ENNReal.ofReal K :=
        Filter.liminf_le_of_frequently_le' (Filter.Eventually.frequently
          (Filter.Eventually.of_forall fun J => hK J))

end CVarLimit

section Determ

/-- complex version of the quadratic-form bound for the operator norm. -/
private lemma pb8_sum_sq_mulVec_le_c {a b : ℕ} (T : Matrix (Fin a) (Fin b) ℂ) (y : Fin b → ℂ) :
    ∑ k, ‖(T *ᵥ y) k‖ ^ 2 ≤ opNorm T ^ 2 * ∑ i, ‖y i‖ ^ 2 := by
  have hb : ‖Matrix.toEuclideanLin T (WithLp.toLp 2 y)‖ ≤ opNorm T * ‖WithLp.toLp 2 y‖ :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin T)).le_opNorm (WithLp.toLp 2 y)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)] at hsq
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct] using hsq

private lemma pb8_opNorm_le_of_sq {m n : ℕ} (U : Mat m n) (M : ℝ) (hM : 0 ≤ M)
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

private lemma pb8_opNorm_nonneg {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ} (K : Matrix (Fin m) (Fin n) 𝕜) :
    0 ≤ opNorm K := by
  unfold opNorm; exact norm_nonneg _

/-- `‖Re T‖ ≤ ‖T‖` and `‖Im T‖ ≤ ‖T‖` for operator norms. -/
private lemma pb8_opNorm_map_le {a b : ℕ} (T : Matrix (Fin a) (Fin b) ℂ) (f : ℂ → ℝ)
    (hf : ∀ z, |f z| ≤ ‖z‖) (hl : ∀ (x : Fin b → ℝ), ∀ k, ((T.map f) *ᵥ x) k =
      f ((T *ᵥ (fun i => (x i : ℂ))) k)) :
    opNorm (T.map f) ≤ opNorm T := by
  refine pb8_opNorm_le_of_sq _ _ (pb8_opNorm_nonneg T) fun x => ?_
  have h1 := pb8_sum_sq_mulVec_le_c T (fun i => (x i : ℂ))
  calc ∑ k, ((T.map f) *ᵥ x) k ^ 2 ≤ ∑ k, ‖(T *ᵥ (fun i => (x i : ℂ))) k‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [hl x k]
        calc f _ ^ 2 = |f _| ^ 2 := (sq_abs _).symm
          _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (hf _) 2
    _ ≤ opNorm T ^ 2 * ∑ i, ‖((x i : ℂ))‖ ^ 2 := h1
    _ = opNorm T ^ 2 * ∑ i, x i ^ 2 := by
        simp [Complex.norm_real, sq_abs]

private lemma pb8_opNorm_re_le {a b : ℕ} (T : Matrix (Fin a) (Fin b) ℂ) :
    opNorm (T.map Complex.re) ≤ opNorm T :=
  pb8_opNorm_map_le T Complex.re Complex.abs_re_le_norm (fun x k => by
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.re_sum])

private lemma pb8_opNorm_im_le {a b : ℕ} (T : Matrix (Fin a) (Fin b) ℂ) :
    opNorm (T.map Complex.im) ≤ opNorm T :=
  pb8_opNorm_map_le T Complex.im Complex.abs_im_le_norm (fun x k => by
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.im_sum])

/-- Trace duality for a complex test matrix against a real matrix (constant `2`). -/
private lemma pb8_trace_duality {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) (E : Mat k k) :
    ‖Matrix.trace (T * E.map (fun x : ℝ => (x : ℂ)))‖ ≤ 2 * opNorm T * nuc E := by
  have hre : (Matrix.trace (T * E.map (fun x : ℝ => (x : ℂ)))).re =
      Matrix.trace ((T.map Complex.re) * E) := by
    simp [Matrix.trace, Matrix.mul_apply, Complex.re_sum, Matrix.map_apply]
  have him : (Matrix.trace (T * E.map (fun x : ℝ => (x : ℂ)))).im =
      Matrix.trace ((T.map Complex.im) * E) := by
    simp [Matrix.trace, Matrix.mul_apply, Complex.im_sum, Matrix.map_apply]
  have h1 := trace_mul_le_opNorm_mul_nuc (T.map Complex.re) E
  have h2 := trace_mul_le_opNorm_mul_nuc (T.map Complex.im) E
  have hn := nuc_nonneg E
  have hr := pb8_opNorm_re_le T
  have hi := pb8_opNorm_im_le T
  calc ‖Matrix.trace (T * E.map (fun x : ℝ => (x : ℂ)))‖
      ≤ |(Matrix.trace (T * E.map (fun x : ℝ => (x : ℂ)))).re| +
        |(Matrix.trace (T * E.map (fun x : ℝ => (x : ℂ)))).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ opNorm T * nuc E + opNorm T * nuc E := by
        rw [hre, him]
        exact add_le_add (h1.trans (mul_le_mul_of_nonneg_right hr hn))
          (h2.trans (mul_le_mul_of_nonneg_right hi hn))
    _ = 2 * opNorm T * nuc E := by ring

end Determ

section Gfun

private lemma pb8_normTrace_sub {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) (B : ℕ) (R R' : Mat k k) :
    normTrace T B R - normTrace T B R' = (B : ℂ)⁻¹ * Matrix.trace (T * (R - R').map (fun x : ℝ => (x : ℂ))) := by
  unfold normTrace
  rw [← mul_sub, Matrix.map_sub _ (fun a b => Complex.ofReal_sub a b), Matrix.mul_sub, Matrix.trace_sub]

private lemma pb8_normTrace_lip {k l : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) (CT : ℝ)
    (hT : opNorm T ≤ CT) (B : ℕ) (s : ℝ) (hs : 0 < s) (K K' : Mat k l) :
    ‖normTrace T B (Rs K s) - normTrace T B (Rs K' s)‖ ≤
      ((B : ℝ)⁻¹ * (2 * CT * (2 / (s * Real.sqrt s)))) * nuc (K - K') := by
  rw [pb8_normTrace_sub, norm_mul]
  have h1 := pb8_trace_duality T (Rs K s - Rs K' s)
  have h2 := lem_app_de_lipschitz K K' s hs
  have hB : ‖(B : ℂ)⁻¹‖ = (B : ℝ)⁻¹ := by simp
  rw [hB]
  have hB0 : (0 : ℝ) ≤ (B : ℝ)⁻¹ := by positivity
  have hn := pb8_opNorm_nonneg T
  calc (B : ℝ)⁻¹ * ‖Matrix.trace (T * (Rs K s - Rs K' s).map (fun x : ℝ => (x : ℂ)))‖
      ≤ (B : ℝ)⁻¹ * (2 * opNorm T * nuc (Rs K s - Rs K' s)) :=
        mul_le_mul_of_nonneg_left h1 hB0
    _ ≤ (B : ℝ)⁻¹ * (2 * CT * (2 / (s * Real.sqrt s) * nuc (K - K'))) := by
        refine mul_le_mul_of_nonneg_left ?_ hB0
        have : 2 * opNorm T ≤ 2 * CT := by linarith
        calc 2 * opNorm T * nuc (Rs K s - Rs K' s)
            ≤ 2 * opNorm T * (2 / (s * Real.sqrt s) * nuc (K - K')) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ ≤ 2 * CT * (2 / (s * Real.sqrt s) * nuc (K - K')) :=
              mul_le_mul_of_nonneg_right this (by have := nuc_nonneg (K - K'); positivity)
    _ = ((B : ℝ)⁻¹ * (2 * CT * (2 / (s * Real.sqrt s)))) * nuc (K - K') := by ring

private lemma pb8_normTrace_bdd {k l : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) (CT : ℝ)
    (hT : opNorm T ≤ CT) (B : ℕ) (s : ℝ) (hs : 0 < s) (K : Mat k l) :
    ‖normTrace T B (Rs K s)‖ ≤ (B : ℝ)⁻¹ * (2 * CT * ((k : ℝ) * (1 / s))) := by
  unfold normTrace
  rw [norm_mul]
  have hB : ‖(B : ℂ)⁻¹‖ = (B : ℝ)⁻¹ := by simp
  rw [hB]
  have hB0 : (0 : ℝ) ≤ (B : ℝ)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hB0
  have h1 := pb8_trace_duality T (Rs K s)
  have h2 := nuc_le_rank_mul_opNorm (Rs K s)
  have h3 := (lem_app_de_resolvent K s hs).1
  have h4 : (Matrix.rank (Rs K s) : ℝ) ≤ k := by exact_mod_cast Matrix.rank_le_height _
  have hn := pb8_opNorm_nonneg T
  have hR := pb8_opNorm_nonneg (Rs K s)
  have hnuc : nuc (Rs K s) ≤ (k : ℝ) * (1 / s) :=
    h2.trans (mul_le_mul h4 h3 hR (Nat.cast_nonneg _))
  calc _ ≤ 2 * opNorm T * nuc (Rs K s) := h1
    _ ≤ 2 * CT * ((k : ℝ) * (1 / s)) := by
        refine mul_le_mul (by linarith) hnuc (nuc_nonneg _) (by linarith)

private lemma pb8_Rs_continuous {m n : ℕ} (s : ℝ) (hs : 0 < s) :
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

end Gfun

section Sample

private lemma pb8_rOut_outer_rIn {m n B : ℕ} (F : FrozenParams m n B) (z : Vec m) (w : Vec n) :
    rOut F.C * outer z w * rIn F.C =
      outer (Matrix.mulVec (rOut F.C) z) (Matrix.mulVec (rIn F.C) w) := by
  have hsym : (rIn F.C)ᵀ = rIn F.C := by
    have h : (CFC.sqrt F.C.Sin)ᴴ = CFC.sqrt F.C.Sin :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg F.C.Sin)).isHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hv : Matrix.vecMul w (rIn F.C) = Matrix.mulVec (rIn F.C) w := by
    rw [← Matrix.vecMul_transpose, hsym]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]

private lemma pb8_eucNorm_smul {k : ℕ} (c : ℝ) (v : Vec k) :
    eucNorm (c • v) = |c| * eucNorm v := by
  unfold eucNorm
  have : ∑ i, (c • v) i ^ 2 = c ^ 2 * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_pow]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- The slot term `sampleTerm` as a function of the sample `x = (z, w)`. -/
private def pb8Q {m n B : ℕ} (F : FrozenParams m n B) (x : Vec m × Vec n) : Mat m n :=
  (dotProduct x.1 (Matrix.mulVec F.A x.2)) • (rOut F.C * Muon.outer x.1 x.2 * rIn F.C)

/-- `h(x) = |d| ‖u‖ ‖v‖`, the integrand of `lem:app-de-moments`(iii). -/
private def pb8h {m n B : ℕ} (F : FrozenParams m n B) (x : Vec m × Vec n) : ℝ :=
  |resid F.A x| * eucNorm (momU F.C B x) * eucNorm (momV F.C B x)

private lemma pb8_nuc_Q {m n B : ℕ} (F : FrozenParams m n B) (x : Vec m × Vec n) :
    (B : ℝ)⁻¹ * nuc (pb8Q F x) = pb8h F x := by
  have hB : (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ = (B : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg B)]
  unfold pb8Q pb8h
  rw [pb8_rOut_outer_rIn, nuc_smul, nuc_outer]
  unfold momU momV resid
  rw [pb8_eucNorm_smul, pb8_eucNorm_smul]
  have h1 : Real.sqrt (∑ i, (Matrix.mulVec (rOut F.C) x.1) i ^ 2) =
      eucNorm (Matrix.mulVec (rOut F.C) x.1) := rfl
  have h2 : Real.sqrt (∑ i, (Matrix.mulVec (rIn F.C) x.2) i ^ 2) =
      eucNorm (Matrix.mulVec (rIn F.C) x.2) := rfl
  rw [h1, h2]
  have hs : |(Real.sqrt (B : ℝ))⁻¹| = (Real.sqrt (B : ℝ))⁻¹ := abs_of_nonneg (by positivity)
  rw [hs]
  calc (B : ℝ)⁻¹ * (|dotProduct x.1 (Matrix.mulVec F.A x.2)| *
        (eucNorm (Matrix.mulVec (rOut F.C) x.1) * eucNorm (Matrix.mulVec (rIn F.C) x.2)))
      = ((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹) * (|dotProduct x.1 (Matrix.mulVec F.A x.2)| *
        (eucNorm (Matrix.mulVec (rOut F.C) x.1) * eucNorm (Matrix.mulVec (rIn F.C) x.2))) := by
        rw [hB]
    _ = _ := by ring

private lemma pb8Q_continuous {m n B : ℕ} (F : FrozenParams m n B) : Continuous (pb8Q F) := by
  unfold pb8Q
  fun_prop

private lemma pb8Q_measurable {m n B : ℕ} (F : FrozenParams m n B) : Measurable (pb8Q F) :=
  (pb8Q_continuous F).measurable

private lemma pb8h_measurable {m n B : ℕ} (F : FrozenParams m n B) : Measurable (pb8h F) := by
  unfold pb8h resid eucNorm momU momV
  fun_prop

end Sample

section Family

variable {m n B : ℕ}

private lemma pb8_law {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (S : FrozenSamples P m n B) (t : ℤ) (J : ℕ) :
    P.map (fun ω (i : Fin (J + 1) × Fin B) => S.zw (t + 1 - ((i.1 : ℕ) : ℤ)) i.2 ω) =
      Measure.pi (fun _ : Fin (J + 1) × Fin B => gaussPair m n) := by
  have hinj : Function.Injective
      (fun i : Fin (J + 1) × Fin B => ((t + 1 - ((i.1 : ℕ) : ℤ), i.2) : ℤ × Fin B)) := by
    intro i k h
    simp only [Prod.mk.injEq] at h
    refine Prod.ext (Fin.ext ?_) h.2
    have := h.1
    omega
  have hind := S.indep.precomp hinj
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i : Fin (J + 1) × Fin B => (S.meas (t + 1 - ((i.1 : ℕ) : ℤ)) i.2).aemeasurable)).mp hind
  rw [h]
  congr 1
  funext i
  exact S.law _ _

end Family

section BufF

variable {m n B : ℕ}

/-- Truncated, one-slot-deleted buffer as a function of the family of samples of ages `≤ J`. -/
private def pb8bufF (w : ℕ → ℝ) (F : FrozenParams m n B) (t s' : ℤ) (a : Fin B) (J : ℕ)
    (x : Fin (J + 1) × Fin B → Vec m × Vec n) : Mat m n :=
  ∑ i : Fin (J + 1) × Fin B,
    if t + 1 - ((i.1 : ℕ) : ℤ) = s' ∧ i.2 = a then 0 else w i.1 • ((B : ℝ)⁻¹ • pb8Q F (x i))

/-- Truncated deleted buffer, `∑_{j ≤ J}` of the deleted batches. -/
private def pb8Mtr {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t s' : ℤ) (a : Fin B) (J : ℕ) (ω : Ω') : Mat m n :=
  ∑ j ∈ Finset.range (J + 1), w j • ((B : ℝ)⁻¹ • ∑ b : Fin B,
    if t + 1 - (j : ℤ) = s' ∧ b = a then 0 else sampleTerm F S (t + 1 - (j : ℤ)) b ω)

private lemma pb8_bufF_eq {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t s' : ℤ) (a : Fin B) (J : ℕ) (ω : Ω') :
    pb8bufF w F t s' a J (fun i => S.zw (t + 1 - ((i.1 : ℕ) : ℤ)) i.2 ω) =
      pb8Mtr w F S t s' a J ω := by
  unfold pb8bufF pb8Mtr
  rw [Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range (fun j => w j • ((B : ℝ)⁻¹ • ∑ b : Fin B,
    if t + 1 - (j : ℤ) = s' ∧ b = a then 0 else sampleTerm F S (t + 1 - (j : ℤ)) b ω)) (J + 1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : t + 1 - ((j : ℕ) : ℤ) = s' ∧ b = a
  · simp [h]
  · simp only [if_neg h]
    rfl

private lemma pb8h_nonneg {m n B : ℕ} (F : FrozenParams m n B) (x : Vec m × Vec n) : 0 ≤ pb8h F x := by
  unfold pb8h eucNorm
  positivity

private lemma pb8_nuc_zero {m n : ℕ} : nuc (0 : Mat m n) = 0 := by
  have := nuc_smul (0 : ℝ) (0 : Mat m n)
  simpa using this

private lemma pb8_nuc_sub_le {m n : ℕ} (K L : Mat m n) : nuc (K - L) ≤ nuc K + nuc L := by
  have h := nuc_add_le K (-L)
  have h2 : nuc (-L) = nuc L := by
    have := nuc_smul (-1 : ℝ) L
    simpa using this
  rw [sub_eq_add_neg]
  linarith

private lemma pb8_bufF_diff (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (F : FrozenParams m n B)
    (t s' : ℤ) (a : Fin B) (J : ℕ) (x : Fin (J + 1) × Fin B → Vec m × Vec n)
    (i : Fin (J + 1) × Fin B) (y : Vec m × Vec n) :
    nuc (pb8bufF w F t s' a J x - pb8bufF w F t s' a J (Function.update x i y)) ≤
      w i.1 * (pb8h F (x i) + pb8h F y) := by
  classical
  set τ : Fin (J + 1) × Fin B → Vec m × Vec n → Mat m n := fun k z =>
    if t + 1 - ((k.1 : ℕ) : ℤ) = s' ∧ k.2 = a then 0 else w k.1 • ((B : ℝ)⁻¹ • pb8Q F z) with hτ
  have hsub : pb8bufF w F t s' a J x - pb8bufF w F t s' a J (Function.update x i y) =
      τ i (x i) - τ i y := by
    unfold pb8bufF
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · simp [hτ]
    · intro k _ hk
      simp [Function.update_of_ne hk]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hsub]
  by_cases hm : t + 1 - ((i.1 : ℕ) : ℤ) = s' ∧ i.2 = a
  · simp only [hτ, if_pos hm, sub_self, pb8_nuc_zero]
    exact mul_nonneg (hw _) (add_nonneg
      (pb8h_nonneg F _) (pb8h_nonneg F _))
  · simp only [hτ, if_neg hm]
    have hB : (0 : ℝ) ≤ (B : ℝ)⁻¹ := by positivity
    have e : w i.1 • ((B : ℝ)⁻¹ • pb8Q F (x i)) - w i.1 • ((B : ℝ)⁻¹ • pb8Q F y) =
        (w i.1 * (B : ℝ)⁻¹) • (pb8Q F (x i) - pb8Q F y) := by
      rw [mul_smul, smul_sub, smul_sub]
    rw [e, nuc_smul, abs_of_nonneg (mul_nonneg (hw _) hB)]
    have h1 := pb8_nuc_sub_le (pb8Q F (x i)) (pb8Q F y)
    have h2 := pb8_nuc_Q F (x i)
    have h3 := pb8_nuc_Q F y
    calc w i.1 * (B : ℝ)⁻¹ * nuc (pb8Q F (x i) - pb8Q F y)
        ≤ w i.1 * (B : ℝ)⁻¹ * (nuc (pb8Q F (x i)) + nuc (pb8Q F y)) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (hw _) hB)
      _ = w i.1 * ((B : ℝ)⁻¹ * nuc (pb8Q F (x i)) + (B : ℝ)⁻¹ * nuc (pb8Q F y)) := by ring
      _ = w i.1 * (pb8h F (x i) + pb8h F y) := by rw [h2, h3]

private lemma pb8bufF_continuous (w : ℕ → ℝ) (F : FrozenParams m n B) (t s' : ℤ) (a : Fin B)
    (J : ℕ) : Continuous (pb8bufF w F t s' a J) := by
  unfold pb8bufF
  refine continuous_finset_sum _ fun i _ => ?_
  by_cases h : t + 1 - ((i.1 : ℕ) : ℤ) = s' ∧ i.2 = a
  · simp only [if_pos h]; exact continuous_const
  · simp only [if_neg h]
    have hc : Continuous (fun x : (Fin (J + 1) × Fin B → Vec m × Vec n) => pb8Q F (x i)) :=
      (pb8Q_continuous F).comp (continuous_apply i)
    exact (continuous_const (y := w i.1)).smul ((continuous_const (y := (B : ℝ)⁻¹)).smul hc)

end BufF

section Finite

variable {m n B : ℕ}

private lemma pb8_finite {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t s' : ℤ) (a : Fin B) (J : ℕ)
    (g : Mat m n → ℂ) (hgc : Continuous g) (Bd : ℝ) (hgb : ∀ M, ‖g M‖ ≤ Bd)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ M M', ‖g M - g M'‖ ≤ L * nuc (M - M'))
    (hh2 : Integrable (fun x => pb8h F x ^ 2) (gaussPair m n)) :
    cVar P (fun ω => g (pb8Mtr w F S t s' a J ω)) ≤
      ENNReal.ofReal (4 * (∫ x, pb8h F x ^ 2 ∂(gaussPair m n)) *
        ((B : ℝ) * L ^ 2 * ∑ j ∈ Finset.range (J + 1), w j ^ 2)) := by
  set φ : Ω' → (Fin (J + 1) × Fin B → Vec m × Vec n) :=
    fun ω i => S.zw (t + 1 - ((i.1 : ℕ) : ℤ)) i.2 ω with hφ
  have hφm : Measurable φ := measurable_pi_iff.2 fun i => S.meas _ _
  have hlaw := pb8_law P S t J
  have hY : (fun ω => g (pb8Mtr w F S t s' a J ω)) =
      fun ω => g (pb8bufF w F t s' a J (φ ω)) := by
    funext ω
    rw [← pb8_bufF_eq]
  have hGc : Continuous (fun x => g (pb8bufF w F t s' a J x)) :=
    hgc.comp (pb8bufF_continuous w F t s' a J)
  have hsum : ∑ i : Fin (J + 1) × Fin B, (L * w i.1) ^ 2 =
      (B : ℝ) * L ^ 2 * ∑ j ∈ Finset.range (J + 1), w j ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow]
    rw [← Fin.sum_univ_eq_sum_range (fun j => w j ^ 2) (J + 1), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hES : ∀ (r : ℂ → ℝ), (∀ z z', |r z - r z'| ≤ ‖z - z'‖) → (∀ z, |r z| ≤ ‖z‖) →
      Continuous r →
      variance (fun x => r (g (pb8bufF w F t s' a J x))) (Measure.pi fun _ : Fin (J + 1) × Fin B => gaussPair m n)
        ≤ 2 * (∫ x, pb8h F x ^ 2 ∂(gaussPair m n)) *
          ((B : ℝ) * L ^ 2 * ∑ j ∈ Finset.range (J + 1), w j ^ 2) := by
    intro r hr1 hr2 hrc
    rw [← hsum]
    refine pb8_es_slot (gaussPair m n) (fun x => r (g (pb8bufF w F t s' a J x)))
      (hrc.comp hGc).measurable Bd (fun x => (hr2 _).trans (hgb _))
      (fun i => L * w i.1) (pb8h F) (pb8h_measurable F) hh2 ?_
    intro i p q
    calc |r (g (pb8bufF w F t s' a J p)) - r (g (pb8bufF w F t s' a J (Function.update p i (q i))))|
        ≤ ‖g (pb8bufF w F t s' a J p) - g (pb8bufF w F t s' a J (Function.update p i (q i)))‖ :=
          hr1 _ _
      _ ≤ L * nuc (pb8bufF w F t s' a J p - pb8bufF w F t s' a J (Function.update p i (q i))) :=
          hlip _ _
      _ ≤ L * (w i.1 * (pb8h F (p i) + pb8h F (q i))) :=
          mul_le_mul_of_nonneg_left (pb8_bufF_diff w hw F t s' a J p i (q i)) hL
      _ = |L * w i.1| * (|pb8h F (p i)| + |pb8h F (q i)|) := by
          rw [abs_of_nonneg (mul_nonneg hL (hw _)), abs_of_nonneg (pb8h_nonneg F _),
            abs_of_nonneg (pb8h_nonneg F _)]
          ring
  have hbd : ∀ ω, ‖g (pb8bufF w F t s' a J (φ ω))‖ ≤ Bd := fun ω => hgb _
  have hmY : Measurable (fun ω => g (pb8bufF w F t s' a J (φ ω))) := hGc.measurable.comp hφm
  rw [hY, pb8_cVar_eq P _ hmY Bd hbd]
  refine ENNReal.ofReal_le_ofReal ?_
  have hv : ∀ (r : ℂ → ℝ), Continuous r →
      variance (fun ω => r (g (pb8bufF w F t s' a J (φ ω)))) P =
        variance (fun x => r (g (pb8bufF w F t s' a J x)))
          (Measure.pi fun _ : Fin (J + 1) × Fin B => gaussPair m n) := by
    intro r hrc
    have := variance_map (μ := P) (Y := φ)
      (X := fun x => r (g (pb8bufF w F t s' a J x))) (by rw [hφ, hlaw]; exact (hrc.comp hGc).measurable.aemeasurable)
      hφm.aemeasurable
    rw [← hlaw]
    exact this.symm
  have e1 := hv Complex.re Complex.continuous_re
  have e2 := hv Complex.im Complex.continuous_im
  have b1 := hES Complex.re (fun z z' => by
    rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _) (fun z => Complex.abs_re_le_norm _)
    Complex.continuous_re
  have b2 := hES Complex.im (fun z z' => by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _) (fun z => Complex.abs_im_le_norm _)
    Complex.continuous_im
  rw [e1, e2]
  linarith

end Finite

section Limit

variable {m n B : ℕ}

private lemma pb8_sum_ite_erase (a : Fin B) (T : Fin B → Mat m n) :
    ∑ b : Fin B, (if b = a then (0 : Mat m n) else T b) = ∑ b : Fin B, T b - T a := by
  have h : ∀ b : Fin B, (if b = a then (0 : Mat m n) else T b) =
      T b - (if b = a then T b else 0) := by
    intro b
    by_cases hb : b = a
    · simp [hb]
    · simp [hb]
  rw [Finset.sum_congr rfl (fun b _ => h b), Finset.sum_sub_distrib]
  simp

private lemma pb8_Mtr_tendsto {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} (w : ℕ → ℝ)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t s' : ℤ) (a : Fin B) (ω : Ω')
    (hsum : Summable fun j : ℕ => w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) :
    Filter.Tendsto (fun J => pb8Mtr w F S t s' a J ω) Filter.atTop
      (nhds (WeightedBufDel w F S t s' a ω)) := by
  set δ : ℕ → Mat m n := fun j =>
    if t + 1 - (j : ℤ) = s' then w j • ((B : ℝ)⁻¹ • sampleTerm F S (t + 1 - (j : ℤ)) a ω) else 0
    with hδ
  have hterm : ∀ j : ℕ, w j • ((B : ℝ)⁻¹ • ∑ b : Fin B,
      if t + 1 - (j : ℤ) = s' ∧ b = a then 0 else sampleTerm F S (t + 1 - (j : ℤ)) b ω) =
      w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω - δ j := by
    intro j
    rw [frozenBatchG_eq_sum]
    by_cases hj : t + 1 - (j : ℤ) = s'
    · simp only [hδ, hj, true_and, if_true]
      rw [pb8_sum_ite_erase a (fun b => sampleTerm F S s' b ω)]
      simp only [smul_sub]
    · simp only [hδ, hj, false_and, if_false, sub_zero]
  have hδs : Summable δ := by
    refine summable_of_ne_finset_zero (s := {(t + 1 - s').toNat}) fun j hj => ?_
    simp only [Finset.mem_singleton] at hj
    simp only [hδ]
    rw [if_neg]
    intro h
    apply hj
    omega
  have hms : Summable fun j : ℕ => w j • ((B : ℝ)⁻¹ • ∑ b : Fin B,
      if t + 1 - (j : ℤ) = s' ∧ b = a then 0 else sampleTerm F S (t + 1 - (j : ℤ)) b ω) :=
    (hsum.sub hδs).congr (fun j => (hterm j).symm)
  have := (hms.hasSum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
  unfold WeightedBufDel
  exact this

private lemma pb8_Mtr_measurable {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'} (w : ℕ → ℝ)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t s' : ℤ) (a : Fin B) (J : ℕ) :
    Measurable (fun ω => pb8Mtr w F S t s' a J ω) := by
  have : (fun ω => pb8Mtr w F S t s' a J ω) = fun ω => pb8bufF w F t s' a J
      (fun i => S.zw (t + 1 - ((i.1 : ℕ) : ℤ)) i.2 ω) := by
    funext ω; rw [pb8_bufF_eq]
  rw [this]
  exact (pb8bufF_continuous w F t s' a J).measurable.comp
    (measurable_pi_iff.2 fun i => S.meas _ _)

end Limit

section Core

variable {m n B : ℕ}

private lemma pb8_int_sq {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (h : X → ℝ) (hm : Measurable h) (c : ℝ) (hc : 0 ≤ c)
    (hH : eLpNorm h 2 μ ≤ ENNReal.ofReal c) :
    Integrable (fun x => h x ^ 2) μ ∧ ∫ x, h x ^ 2 ∂μ ≤ c ^ 2 := by
  have hmem : MemLp h 2 μ := memLp_iff.mpr (lt_of_le_of_lt hH ENNReal.ofReal_lt_top)
  refine ⟨hmem.integrable_sq, ?_⟩
  have h1 := hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  rw [h1] at hH
  have h2 : (∫ x, ‖h x‖ ^ ((2 : ℝ≥0∞).toReal) ∂μ) ^ ((2 : ℝ≥0∞).toReal)⁻¹ ≤ c := by
    have := (ENNReal.ofReal_le_ofReal_iff hc).1 hH
    exact this
  have h3 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h3] at h2
  have h4 : 0 ≤ ∫ x, ‖h x‖ ^ (2 : ℝ) ∂μ := integral_nonneg fun x => by positivity
  have h5 : ∫ x, ‖h x‖ ^ (2 : ℝ) ∂μ ≤ c ^ 2 := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg h4 _) h2 (by norm_num : (0 : ℝ) ≤ 2)
    rw [← Real.rpow_mul h4] at this
    simpa using this
  have h6 : ∫ x, h x ^ 2 ∂μ = ∫ x, ‖h x‖ ^ (2 : ℝ) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [Real.rpow_two, sq_abs]
  rw [h6]; exact h5

private lemma pb8_core {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (hw : WeightClass w) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t s' : ℤ) (a : Fin B)
    (g : Mat m n → ℂ) (hgc : Continuous g) (Bd : ℝ) (hgb : ∀ M, ‖g M‖ ≤ Bd)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ M M', ‖g M - g M'‖ ≤ L * nuc (M - M'))
    (Hc : ℝ) (hHc : 0 ≤ Hc) (hH : eLpNorm (pb8h F) 2 (gaussPair m n) ≤ ENNReal.ofReal Hc) :
    cVar P (fun ω => g (WeightedBufDel w F S t s' a ω)) ≤
      ENNReal.ofReal (4 * Hc ^ 2 * ((B : ℝ) * L ^ 2 * sumPow w 2)) := by
  obtain ⟨hh2, hint⟩ := pb8_int_sq (gaussPair m n) (pb8h F) (pb8h_measurable F) Hc hHc hH
  have hw0 : ∀ j, 0 ≤ w j := hw.1.1
  have hs2 : Summable (fun j => w j ^ 2) := by
    refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) hw.1.2.1
    have := hw.2.1 j
    nlinarith [hw0 j]
  have hpart : ∀ J, ∑ j ∈ Finset.range (J + 1), w j ^ 2 ≤ sumPow w 2 := fun J =>
    hs2.sum_le_tsum _ (fun j _ => sq_nonneg _)
  refine pb8_cVar_limit P (fun J ω => g (pb8Mtr w F S t s' a J ω))
    (fun ω => g (WeightedBufDel w F S t s' a ω))
    (fun J => hgc.measurable.comp (pb8_Mtr_measurable w F S t s' a J)) Bd
    (fun J ω => hgb _) ?_ _ ?_
  · filter_upwards [weightedBuf_summable_ae w hw.1 F S] with ω hω
    exact (hgc.tendsto _).comp (pb8_Mtr_tendsto w F S t s' a ω (hω t))
  · intro J
    refine (pb8_finite P w hw0 F S t s' a J g hgc Bd hgb L hL hlip hh2).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    have h0 : 0 ≤ ∫ x, pb8h F x ^ 2 ∂(gaussPair m n) := integral_nonneg fun x => sq_nonneg _
    have hsc : 0 ≤ (B : ℝ) * L ^ 2 := by positivity
    calc 4 * (∫ x, pb8h F x ^ 2 ∂(gaussPair m n)) *
          ((B : ℝ) * L ^ 2 * ∑ j ∈ Finset.range (J + 1), w j ^ 2)
        ≤ 4 * Hc ^ 2 * ((B : ℝ) * L ^ 2 * ∑ j ∈ Finset.range (J + 1), w j ^ 2) := by
          refine mul_le_mul_of_nonneg_right (by linarith) (by
            have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (J + 1)) => sq_nonneg (w j))
            positivity)
      _ ≤ 4 * Hc ^ 2 * ((B : ℝ) * L ^ 2 * sumPow w 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (hpart J) hsc

end Core

section Master

private lemma pb8_const (Hc CT S Bn s sm : ℝ) (hB : 0 < Bn) (hsm : 0 < sm) (hs : sm ≤ s)
    (hS : 0 ≤ S) :
    4 * Hc ^ 2 * (Bn * (Bn⁻¹ * (2 * CT * (2 / (s * Real.sqrt s)))) ^ 2 * S) ≤
      (64 * Hc ^ 2 / sm ^ 3) * CT ^ 2 * S / Bn := by
  have hs0 : 0 < s := lt_of_lt_of_le hsm hs
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have e : 4 * Hc ^ 2 * (Bn * (Bn⁻¹ * (2 * CT * (2 / (s * Real.sqrt s)))) ^ 2 * S) =
      (64 * Hc ^ 2 * CT ^ 2 * S / Bn) / s ^ 3 := by
    have : s ^ 3 = (s * Real.sqrt s) ^ 2 := by rw [mul_pow, hsq]; ring
    rw [this]
    field_simp
    ring
  rw [e]
  have h1 : (64 * Hc ^ 2 / sm ^ 3) * CT ^ 2 * S / Bn = (64 * Hc ^ 2 * CT ^ 2 * S / Bn) / sm ^ 3 := by
    field_simp
  rw [h1]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  exact pow_le_pow_left₀ hsm.le hs 3

private lemma pb8_buf_eq_del {m n B : ℕ} {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'}
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (ω : Ω') :
    WeightedBuf w F S t ω = WeightedBufDel w F S t (t + 2) (slotOne F.hB) ω := by
  unfold WeightedBuf WeightedBufDel
  refine tsum_congr fun j => ?_
  have h : ¬ (t + 1 - (j : ℤ) = t + 2) := by omega
  simp only [h, false_and, if_false]
  rw [frozenBatchG_eq_sum]

private lemma pb8_master (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) (CSig γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m n B : ℕ) (w : ℕ → ℝ), WeightClass w →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
        (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ),
        opNorm F.C.Sout ≤ CSig → opNorm F.C.Sin ≤ CSig →
        (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
        ∀ s ∈ I, ∀ (s' : ℤ) (a : Fin B) (k l : ℕ) (Φ : Mat m n → Mat k l), Continuous Φ →
          (∀ M M', nuc (Φ M - Φ M') ≤ nuc (M - M')) →
          ∀ (T : Matrix (Fin k) (Fin k) ℂ) (CT : ℝ), opNorm T ≤ CT →
          cVar P (fun ω => normTrace T B (Rs (Φ (WeightedBufDel w F S t s' a ω)) s)) ≤
            ENNReal.ofReal (C * CT ^ 2 * sumPow w 2 / B) := by
  refine ⟨64 * (7 * CSig * γ) ^ 2 / (sInf I) ^ 3, div_nonneg (by positivity) (pow_nonneg (Real.sInf_nonneg fun x hx => (hIpos hx).le) 3), ?_⟩
  intro m n B w hw Ω' _ P _ F S t hCo hCi hm hn s hsI s' a k l Φ hΦc hΦn T CT hT
  have hsm : 0 < sInf I := hIpos (hI.sInf_mem ⟨s, hsI⟩)
  have hsle : sInf I ≤ s := csInf_le hI.bddBelow hsI
  have hs0 : 0 < s := lt_of_lt_of_le hsm hsle
  have hBpos : 0 < B := F.hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hγ : 0 ≤ γ := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg hBr
    have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hC0 : 0 ≤ CSig := le_trans (pb8_opNorm_nonneg _) hCo
  have hCT0 : 0 ≤ CT := le_trans (pb8_opNorm_nonneg _) hT
  have hmom := lem_app_de_moments_iii F.C B γ CSig ⟨hm, hn⟩ hγ ⟨hCo, hCi⟩ F.A F.hA
  have hH : eLpNorm (pb8h F) 2 (gaussPair m n) ≤ ENNReal.ofReal (7 * CSig * γ) :=
    hmom.1.trans (ENNReal.ofReal_le_ofReal hmom.2)
  have hHc : 0 ≤ 7 * CSig * γ := by positivity
  set g : Mat m n → ℂ := fun M => normTrace T B (Rs (Φ M) s) with hg
  have hgc : Continuous g := by
    have h1 : Continuous fun M : Mat m n => (Rs (Φ M) s).map (fun x : ℝ => (x : ℂ)) :=
      ((pb8_Rs_continuous s hs0).comp hΦc).matrix_map Complex.continuous_ofReal
    show Continuous fun M : Mat m n => normTrace T B (Rs (Φ M) s)
    unfold normTrace
    exact continuous_const.mul ((continuous_const.matrix_mul h1).matrix_trace)
  set L : ℝ := (B : ℝ)⁻¹ * (2 * CT * (2 / (s * Real.sqrt s))) with hL
  have hL0 : 0 ≤ L := by positivity
  have hlip : ∀ M M', ‖g M - g M'‖ ≤ L * nuc (M - M') := by
    intro M M'
    refine (pb8_normTrace_lip T CT hT B s hs0 (Φ M) (Φ M')).trans ?_
    exact mul_le_mul_of_nonneg_left (hΦn M M') hL0
  have hcore := pb8_core P w hw F S t s' a g hgc ((B : ℝ)⁻¹ * (2 * CT * ((k : ℝ) * (1 / s))))
    (fun M => pb8_normTrace_bdd T CT hT B s hs0 (Φ M)) L hL0 hlip (7 * CSig * γ) hHc hH
  refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
  have hS : 0 ≤ sumPow w 2 := tsum_nonneg fun j => sq_nonneg _
  exact pb8_const (7 * CSig * γ) CT (sumPow w 2) (B : ℝ) s (sInf I) hBr hsm hsle hS

end Master

/-! ## Variance of normalized traces (`lem:app-de-variance`) -/

/-- `lem:app-de-variance`, part (i), snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.1207–1213):
\begin{lemma}[Variance of normalized traces]\label{lem:app-de-variance}
Let $T\in\mathbb{C}^{\Nout\times\Nout}$ be deterministic with $\norm T\le C_T$ and put
$Y(s)\defeq\frac1B\Tr\big(TR(-s)\big)$. Then $\Var Y(s)\le C_IC_T^2\,\sw2/B$ for
$s\in I$. The same bound holds for $\frac1B\Tr(\widetilde TR_s(\Mt^\T))$ with
$\norm{\widetilde T}\le C_T$, and for the traces of the resolvents of any
buffer with one sample deleted.
\end{lemma}
-/
theorem lem_app_de_variance_i (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    (CSig γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m n B : ℕ) (w : ℕ → ℝ), WeightClass w →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
        (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ),
        opNorm F.C.Sout ≤ CSig → opNorm F.C.Sin ≤ CSig →
        (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
        ∀ s ∈ I, ∀ (T : Matrix (Fin m) (Fin m) ℂ) (CT : ℝ), opNorm T ≤ CT →
          cVar P (fun ω => normTrace T B (Rs (WeightedBuf w F S t ω) s)) ≤
            ENNReal.ofReal (C * CT ^ 2 * sumPow w 2 / B) := by
  obtain ⟨C, hC0, H⟩ := pb8_master I hI hIpos CSig γ
  refine ⟨C, hC0, fun m n B w hw Ω' _ P _ F S t hCo hCi hm hn s hs T CT hT => ?_⟩
  have e : (fun ω => normTrace T B (Rs (WeightedBuf w F S t ω) s)) =
      fun ω => normTrace T B (Rs (id (WeightedBufDel w F S t (t + 2) (slotOne F.hB) ω)) s) := by
    funext ω
    rw [pb8_buf_eq_del]
    rfl
  rw [e]
  have h := H m n B w hw Ω' P F S t hCo hCi hm hn s hs (t + 2) (slotOne F.hB) m n id continuous_id
    (fun _ _ => le_rfl) T CT hT
  simpa only [id_eq] using h

/-- `lem:app-de-variance`, part (ii), snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.1207–1213):
\begin{lemma}[Variance of normalized traces]\label{lem:app-de-variance}
Let $T\in\mathbb{C}^{\Nout\times\Nout}$ be deterministic with $\norm T\le C_T$ and put
$Y(s)\defeq\frac1B\Tr\big(TR(-s)\big)$. Then $\Var Y(s)\le C_IC_T^2\,\sw2/B$ for
$s\in I$. The same bound holds for $\frac1B\Tr(\widetilde TR_s(\Mt^\T))$ with
$\norm{\widetilde T}\le C_T$, and for the traces of the resolvents of any
buffer with one sample deleted.
\end{lemma}
-/
theorem lem_app_de_variance_ii (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    (CSig γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m n B : ℕ) (w : ℕ → ℝ), WeightClass w →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
        (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ),
        opNorm F.C.Sout ≤ CSig → opNorm F.C.Sin ≤ CSig →
        (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
        ∀ s ∈ I, ∀ (T : Matrix (Fin n) (Fin n) ℂ) (CT : ℝ), opNorm T ≤ CT →
          cVar P (fun ω => normTrace T B (Rs ((WeightedBuf w F S t ω)ᵀ) s)) ≤
            ENNReal.ofReal (C * CT ^ 2 * sumPow w 2 / B) := by
  obtain ⟨C, hC0, H⟩ := pb8_master I hI hIpos CSig γ
  refine ⟨C, hC0, fun m n B w hw Ω' _ P _ F S t hCo hCi hm hn s hs T CT hT => ?_⟩
  have e : (fun ω => normTrace T B (Rs ((WeightedBuf w F S t ω)ᵀ) s)) =
      fun ω => normTrace T B (Rs (Matrix.transpose
        (WeightedBufDel w F S t (t + 2) (slotOne F.hB) ω)) s) := by
    funext ω
    rw [pb8_buf_eq_del]
  rw [e]
  exact H m n B w hw Ω' P F S t hCo hCi hm hn s hs (t + 2) (slotOne F.hB) n m Matrix.transpose
    continuous_id.matrix_transpose
    (fun M M' => by rw [← Matrix.transpose_sub, nuc_transpose]) T CT hT

/-- `lem:app-de-variance`, part (iii), snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.1207–1213):
\begin{lemma}[Variance of normalized traces]\label{lem:app-de-variance}
Let $T\in\mathbb{C}^{\Nout\times\Nout}$ be deterministic with $\norm T\le C_T$ and put
$Y(s)\defeq\frac1B\Tr\big(TR(-s)\big)$. Then $\Var Y(s)\le C_IC_T^2\,\sw2/B$ for
$s\in I$. The same bound holds for $\frac1B\Tr(\widetilde TR_s(\Mt^\T))$ with
$\norm{\widetilde T}\le C_T$, and for the traces of the resolvents of any
buffer with one sample deleted.
\end{lemma}
-/
theorem lem_app_de_variance_iii (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    (CSig γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m n B : ℕ) (w : ℕ → ℝ), WeightClass w →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
        (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ),
        opNorm F.C.Sout ≤ CSig → opNorm F.C.Sin ≤ CSig →
        (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
        ∀ s ∈ I, ∀ (s' : ℤ) (a : Fin B) (T : Matrix (Fin m) (Fin m) ℂ) (CT : ℝ), opNorm T ≤ CT →
          cVar P (fun ω => normTrace T B (Rs (WeightedBufDel w F S t s' a ω) s)) ≤
            ENNReal.ofReal (C * CT ^ 2 * sumPow w 2 / B) := by
  obtain ⟨C, hC0, H⟩ := pb8_master I hI hIpos CSig γ
  refine ⟨C, hC0, fun m n B w hw Ω' _ P _ F S t hCo hCi hm hn s hs s' a T CT hT => ?_⟩
  have h := H m n B w hw Ω' P F S t hCo hCi hm hn s hs s' a m n id continuous_id
    (fun _ _ => le_rfl) T CT hT
  simpa only [id_eq] using h

/-- `lem:app-de-variance`, part (iv), snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.1207–1213):
\begin{lemma}[Variance of normalized traces]\label{lem:app-de-variance}
Let $T\in\mathbb{C}^{\Nout\times\Nout}$ be deterministic with $\norm T\le C_T$ and put
$Y(s)\defeq\frac1B\Tr\big(TR(-s)\big)$. Then $\Var Y(s)\le C_IC_T^2\,\sw2/B$ for
$s\in I$. The same bound holds for $\frac1B\Tr(\widetilde TR_s(\Mt^\T))$ with
$\norm{\widetilde T}\le C_T$, and for the traces of the resolvents of any
buffer with one sample deleted.
\end{lemma}
-/
theorem lem_app_de_variance_iv (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    (CSig γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m n B : ℕ) (w : ℕ → ℝ), WeightClass w →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
        (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ),
        opNorm F.C.Sout ≤ CSig → opNorm F.C.Sin ≤ CSig →
        (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
        ∀ s ∈ I, ∀ (s' : ℤ) (a : Fin B) (T : Matrix (Fin n) (Fin n) ℂ) (CT : ℝ), opNorm T ≤ CT →
          cVar P (fun ω => normTrace T B (Rs ((WeightedBufDel w F S t s' a ω)ᵀ) s)) ≤
            ENNReal.ofReal (C * CT ^ 2 * sumPow w 2 / B) := by
  obtain ⟨C, hC0, H⟩ := pb8_master I hI hIpos CSig γ
  refine ⟨C, hC0, fun m n B w hw Ω' _ P _ F S t hCo hCi hm hn s hs s' a T CT hT => ?_⟩
  exact H m n B w hw Ω' P F S t hCo hCi hm hn s hs s' a n m Matrix.transpose
    continuous_id.matrix_transpose
    (fun M M' => by rw [← Matrix.transpose_sub, nuc_transpose]) T CT hT

/-! ## Private machinery for `lem:app-de-scalars` -/

section Scalars

private lemma pb82_eLpNorm_le {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') (f : Ω' → ℝ)
    (hf : Measurable f) (c : ℝ) (hc : 0 ≤ c)
    (h : ∫⁻ ω, ENNReal.ofReal ((f ω) ^ 2) ∂P ≤ ENNReal.ofReal (c ^ 2)) :
    eLpNorm f 2 P ≤ ENNReal.ofReal c := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have hpt : ∀ ω, ‖f ω‖ₑ ^ (2 : ℝ) = ENNReal.ofReal ((f ω) ^ 2) := by
    intro ω
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    congr 1
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  simp_rw [hpt]
  calc (∫⁻ ω, ENNReal.ofReal ((f ω) ^ 2) ∂P) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal (c ^ 2)) ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal c := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      congr 1
      rw [← Real.sqrt_eq_rpow]
      exact Real.sqrt_sq hc

private lemma pb82_tonelli {Ω' : Type*} [MeasurableSpace Ω'] {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (P : Measure Ω') [IsProbabilityMeasure P] (X : Ω' → α) (Y : Ω' → β)
    (hX : Measurable X) (hY : Measurable Y) (hind : IndepFun Y X P) (μ : Measure α)
    (hμ : P.map X = μ) (f : β → α → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) :
    ∫⁻ ω, f (Y ω) (X ω) ∂P = ∫⁻ y, ∫⁻ x, f y x ∂μ ∂(P.map Y) := by
  have h := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hX.aemeasurable).1 hind
  haveI : IsProbabilityMeasure μ := by rw [← hμ]; infer_instance
  have e : ∫⁻ ω, f (Y ω) (X ω) ∂P = ∫⁻ p, Function.uncurry f p ∂(P.map fun ω => (Y ω, X ω)) := by
    rw [lintegral_map hf (hY.prodMk hX)]; rfl
  rw [e, h, hμ, lintegral_prod _ hf.aemeasurable]
  rfl

private lemma pb82_quad_lintegral (k : ℕ) (A : Mat k k) (hA : A.transpose = A) :
    ∫⁻ z, ENNReal.ofReal ((dotProduct z (Matrix.mulVec A z) - Matrix.trace A) ^ 2)
      ∂(Muon.Foundations.stdGaussianPi k) ≤ ENNReal.ofReal (2 * (A * A).trace) := by
  have e : ∀ z : Vec k, dotProduct z (Matrix.mulVec A z) = ∑ i, ∑ j, z i * A i j * z j := by
    intro z
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hvar := Muon.Foundations.stdGaussianPi_quadratic_variance k A hA
  simp_rw [e]
  have hsym : ∀ i j, A j i = A i j := fun i j => by
    have h := congrArg (fun M => M i j) hA
    simpa [Matrix.transpose_apply] using h
  have htr : (A * A).trace = ∑ i, ∑ j, A i j ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym j i]; ring
  by_cases h0 : (A * A).trace = 0
  · have hz : ∀ i j, A i j = 0 := by
      intro i j
      rw [htr] at h0
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
        (fun j _ => sq_nonneg (A i j)))).1 h0 i (Finset.mem_univ i)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (A i j))).1 h1 j
        (Finset.mem_univ j)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h2
    have hA0 : A = 0 := by ext i j; exact hz i j
    subst hA0
    simp
  · have hpos : 0 < (A * A).trace := by
      rw [htr] at h0 ⊢
      exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
        (Ne.symm h0)
    have hint : Integrable (fun z : Fin k → ℝ => (∑ i, ∑ j, z i * A i j * z j - A.trace) ^ 2)
        (Muon.Foundations.stdGaussianPi k) := by
      by_contra hni
      rw [integral_undef hni] at hvar
      linarith
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z => sq_nonneg _),
      hvar]

private lemma pb82_sum_sq_mulVec_le {a b : ℕ} (T : Mat a b) (y : Fin b → ℝ) :
    ∑ k, (T *ᵥ y) k ^ 2 ≤ opNorm T ^ 2 * ∑ i, y i ^ 2 := by
  have hb : ‖Matrix.toEuclideanLin T (WithLp.toLp 2 y)‖ ≤ opNorm T * ‖WithLp.toLp 2 y‖ :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin T)).le_opNorm (WithLp.toLp 2 y)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)] at hsq
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Real.norm_eq_abs, sq_abs] using hsq

private lemma pb82_fro_sq_le {a b : ℕ} (A : Mat a b) :
    ∑ i, ∑ j, A i j ^ 2 ≤ (b : ℝ) * opNorm A ^ 2 := by
  classical
  have h1 : ∀ j : Fin b, ∑ i, A i j ^ 2 ≤ opNorm A ^ 2 := by
    intro j
    have := pb82_sum_sq_mulVec_le A (Pi.single j 1)
    have e1 : ∀ i, (A *ᵥ (Pi.single j (1 : ℝ))) i = A i j := fun i => by
      simp [Matrix.mulVec_single_one]
    have e2 : ∑ i, (Pi.single j (1 : ℝ) : Fin b → ℝ) i ^ 2 = 1 := by
      simp [Pi.single_apply]
    simpa [e1, e2] using this
  rw [Finset.sum_comm]
  calc ∑ j, ∑ i, A i j ^ 2 ≤ ∑ _j : Fin b, opNorm A ^ 2 := Finset.sum_le_sum fun j _ => h1 j
    _ = (b : ℝ) * opNorm A ^ 2 := by simp

open scoped Matrix.Norms.L2Operator in
private lemma pb82_opNorm_mul_le {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B

open scoped Matrix.Norms.L2Operator in
private lemma pb82_opNorm_sqrt_mul_self {a : ℕ} (S : Mat a a) (hS : S.PosSemidef) :
    opNorm (CFC.sqrt S) * opNorm (CFC.sqrt S) = opNorm S := by
  have hh : (CFC.sqrt S)ᴴ = CFC.sqrt S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).isHermitian
  have hsq : CFC.sqrt S * CFC.sqrt S = S :=
    CFC.sqrt_mul_sqrt_self S (Matrix.nonneg_iff_posSemidef.mpr hS)
  have := Matrix.l2_opNorm_conjTranspose_mul_self (CFC.sqrt S)
  rw [hh, hsq] at this
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact this.symm

private lemma pb82_sqrt_symm {a : ℕ} (S : Mat a a) :
    (CFC.sqrt S).transpose = CFC.sqrt S := by
  have h : (CFC.sqrt S)ᴴ = CFC.sqrt S := by
    by_cases hS : S.PosSemidef
    · exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).isHermitian
    · exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma pb82_lintegral_le_of_eLpNorm {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    (f : Ω' → ℝ) (hf : Measurable f) (c : ℝ) (hc : 0 ≤ c)
    (h : eLpNorm f 2 P ≤ ENNReal.ofReal c) :
    ∫⁻ ω, ENNReal.ofReal ((f ω) ^ 2) ∂P ≤ ENNReal.ofReal (c ^ 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable] at h
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2] at h
  have hpt : ∀ ω, ‖f ω‖ₑ ^ (2 : ℝ) = ENNReal.ofReal ((f ω) ^ 2) := by
    intro ω
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    congr 1
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  simp_rw [hpt] at h
  have h3 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul] at h3
  norm_num at h3
  rw [ENNReal.ofReal_pow hc]
  simpa using h3

private lemma pb82_bilin {m n : ℕ} (A : Mat m n) :
    ∫⁻ x, ENNReal.ofReal ((dotProduct x.1 (A *ᵥ x.2)) ^ 2) ∂(gaussPair m n) ≤
      ENNReal.ofReal (∑ i, ∑ j, A i j ^ 2) := by
  set c : ℝ := fro A with hc
  have hc2 : c ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
    rw [hc]; unfold fro
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
    simp
  rw [← hc2]
  by_cases h0 : c = 0
  · have hz : ∀ i j, A i j = 0 := by
      intro i j
      have h1 : ∑ i, ∑ j, A i j ^ 2 = 0 := by rw [← hc2, h0]; ring
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
        (fun j _ => sq_nonneg (A i j)))).1 h1 i (Finset.mem_univ i)
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (A i j))).1 h2 j
        (Finset.mem_univ j)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h3
    have hA0 : A = 0 := by ext i j; exact hz i j
    subst hA0
    simp
  · have hcpos : 0 < c := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
    set Ah : Mat m n := c⁻¹ • A with hAh
    have hfro : fro Ah = 1 := by
      unfold fro
      have : ∑ i, ∑ j, ‖Ah i j‖ ^ 2 = c⁻¹ ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [hAh, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      have : Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) = c := rfl
      rw [this]
      field_simp
    have hmom := lem_app_de_moments_ii Ah hfro 1 le_rfl
    have hres : ∀ x : Vec m × Vec n, resid Ah x = c⁻¹ * dotProduct x.1 (A *ᵥ x.2) := by
      intro x
      simp [resid, hAh, Matrix.smul_mulVec, dotProduct_smul]
    have hmeas : Measurable (fun x : Vec m × Vec n => resid Ah x) := by
      unfold resid; fun_prop
    have hint : ∫⁻ x, ENNReal.ofReal ((resid Ah x) ^ 2) ∂(gaussPair m n) ≤ 1 := by
      have h1 : eLpNorm (fun x => resid Ah x) 2 (gaussPair m n) ≤ ENNReal.ofReal 1 := by
        have h1 := hmom
        simp only [Nat.mul_one, Nat.cast_ofNat, Nat.doubleFactorial, Nat.cast_one, div_one,
          Real.rpow_one] at h1
        simpa using h1
      have := pb82_lintegral_le_of_eLpNorm (gaussPair m n) _ hmeas 1 zero_le_one h1
      simpa using this
    have hpt : ∀ x : Vec m × Vec n, ENNReal.ofReal ((dotProduct x.1 (A *ᵥ x.2)) ^ 2) =
        ENNReal.ofReal (c ^ 2) * ENNReal.ofReal ((resid Ah x) ^ 2) := by
      intro x
      rw [← ENNReal.ofReal_mul (sq_nonneg _), hres x]
      congr 1
      field_simp
    simp_rw [hpt]
    rw [lintegral_const_mul _ (hmeas.pow_const 2).ennreal_ofReal]
    calc ENNReal.ofReal (c ^ 2) * ∫⁻ x, ENNReal.ofReal ((resid Ah x) ^ 2) ∂(gaussPair m n)
        ≤ ENNReal.ofReal (c ^ 2) * 1 := by gcongr
      _ = ENNReal.ofReal (c ^ 2) := mul_one _

private lemma pb82_Rs_symm {k l : ℕ} (M : Mat k l) (s : ℝ) : (Rs M s).transpose = Rs M s := by
  unfold Rs
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  simp [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_smul]

private lemma pb82_trace_sq {k : ℕ} (A : Mat k k) (hA : A.transpose = A) :
    (A * A).trace = ∑ i, ∑ j, A i j ^ 2 := by
  have hsym : ∀ i j, A j i = A i j := fun i j => by
    have h := congrArg (fun M => M i j) hA
    simpa [Matrix.transpose_apply] using h
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsym j i]; ring

open scoped Matrix.Norms.L2Operator in
private lemma pb82_opNorm_smul {a b : ℕ} (c : ℝ) (A : Mat a b) :
    opNorm (c • A) = |c| * opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, norm_smul, Real.norm_eq_abs]

/-- The algebra of `uᵀ R u` for `u = (√B)⁻¹ r ζ`. -/
private lemma pb82_quad_alg {k : ℕ} (r R : Mat k k) (hr : r.transpose = r) (c : ℝ) (ζ : Vec k) :
    dotProduct (c • (r *ᵥ ζ)) (R *ᵥ (c • (r *ᵥ ζ))) =
      dotProduct ζ ((c ^ 2 • (r * R * r)) *ᵥ ζ) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, Matrix.smul_mulVec]
  rw [dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have h1 : dotProduct (r *ᵥ ζ) (R *ᵥ (r *ᵥ ζ)) = dotProduct ζ ((r * R * r) *ᵥ ζ) := by
    have key : ∀ x y : Vec k, dotProduct (r *ᵥ x) y = dotProduct x (r *ᵥ y) := by
      intro x y
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hr,
        dotProduct_comm]
    rw [key, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [h1]; ring

/-- Matrix of the conditional Gaussian quadratic form. -/
private def pb82A {k l : ℕ} (Sg : Mat k k) (B : ℕ) (s : ℝ) (M : Mat k l) : Mat k k :=
  ((Real.sqrt (B : ℝ))⁻¹ ^ 2) • (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg)

private lemma pb82A_symm {k l : ℕ} (Sg : Mat k k) (B : ℕ) (s : ℝ) (M : Mat k l) :
    (pb82A Sg B s M).transpose = pb82A Sg B s M := by
  unfold pb82A
  rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul, pb82_sqrt_symm,
    pb82_Rs_symm]
  rw [Matrix.mul_assoc]

private lemma pb82A_trace {k l : ℕ} (Sg : Mat k k) (hS : Sg.PosSemidef) (B : ℕ) (hB : 0 < B)
    (s : ℝ) (M : Mat k l) :
    (pb82A Sg B s M).trace = (B : ℝ)⁻¹ * (Sg * Rs M s).trace := by
  unfold pb82A
  have hsq : CFC.sqrt Sg * CFC.sqrt Sg = Sg :=
    CFC.sqrt_mul_sqrt_self Sg (Matrix.nonneg_iff_posSemidef.mpr hS)
  rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm (CFC.sqrt Sg * Rs M s) (CFC.sqrt Sg),
    ← Matrix.mul_assoc, hsq]
  congr 1
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg B)]

private lemma pb82A_fro {k l : ℕ} (Sg : Mat k k) (hS : Sg.PosSemidef) (CSig : ℝ)
    (hC : opNorm Sg ≤ CSig) (B : ℕ) (hB : 0 < B) (s : ℝ) (hs : 0 < s) (M : Mat k l) :
    ∑ i, ∑ j, pb82A Sg B s M i j ^ 2 ≤ (k : ℝ) * (CSig / (s * B)) ^ 2 := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hr := pb82_opNorm_sqrt_mul_self Sg hS
  have hC0 : 0 ≤ CSig := (pb8_opNorm_nonneg Sg).trans hC
  have hR := (lem_app_de_resolvent M s hs).1
  have h1 : opNorm (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg) ≤ CSig * (1 / s) := by
    calc opNorm (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg)
        ≤ opNorm (CFC.sqrt Sg * Rs M s) * opNorm (CFC.sqrt Sg) := pb82_opNorm_mul_le _ _
      _ ≤ (opNorm (CFC.sqrt Sg) * opNorm (Rs M s)) * opNorm (CFC.sqrt Sg) :=
          mul_le_mul_of_nonneg_right (pb82_opNorm_mul_le _ _) (pb8_opNorm_nonneg _)
      _ = (opNorm (CFC.sqrt Sg) * opNorm (CFC.sqrt Sg)) * opNorm (Rs M s) := by ring
      _ ≤ CSig * (1 / s) := by
          rw [hr]
          exact mul_le_mul hC hR (pb8_opNorm_nonneg _) hC0
  have h2 : opNorm (pb82A Sg B s M) ≤ CSig / (s * B) := by
    unfold pb82A
    rw [pb82_opNorm_smul, abs_of_nonneg (by positivity)]
    calc (Real.sqrt (B : ℝ))⁻¹ ^ 2 * opNorm (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg)
        ≤ (Real.sqrt (B : ℝ))⁻¹ ^ 2 * (CSig * (1 / s)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = CSig / (s * B) := by
          rw [inv_pow, Real.sq_sqrt hBr.le]
          field_simp
  calc ∑ i, ∑ j, pb82A Sg B s M i j ^ 2 ≤ (k : ℝ) * opNorm (pb82A Sg B s M) ^ 2 :=
        pb82_fro_sq_le _
    _ ≤ (k : ℝ) * (CSig / (s * B)) ^ 2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pb8_opNorm_nonneg _) h2 2)
          (Nat.cast_nonneg k)

private lemma pb82_T1 {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {k l : ℕ} (Sg : Mat k k) (hS : Sg.PosSemidef) (CSig : ℝ) (hC : opNorm Sg ≤ CSig)
    (B : ℕ) (hB : 0 < B) (s : ℝ) (hs : 0 < s)
    (ζ : Ω' → Vec k) (N : Ω' → Mat k l) (hζ : Measurable ζ) (hN : Measurable N)
    (hind : IndepFun N ζ P) (hlaw : P.map ζ = Muon.Foundations.stdGaussianPi k) :
    ∫⁻ ω, ENNReal.ofReal ((dotProduct ((Real.sqrt (B : ℝ))⁻¹ • (CFC.sqrt Sg *ᵥ ζ ω))
        (Rs (N ω) s *ᵥ ((Real.sqrt (B : ℝ))⁻¹ • (CFC.sqrt Sg *ᵥ ζ ω)))
        - (B : ℝ)⁻¹ * (Sg * Rs (N ω) s).trace) ^ 2) ∂P
      ≤ ENNReal.ofReal ((k : ℝ) * (2 * (CSig / (s * B)) ^ 2)) := by
  have hRc : Continuous (fun M : Mat k l => Rs M s) := pb8_Rs_continuous s hs
  set f : Mat k l → Vec k → ℝ≥0∞ := fun M z =>
    ENNReal.ofReal ((dotProduct z (Matrix.mulVec (pb82A Sg B s M) z)
      - Matrix.trace (pb82A Sg B s M)) ^ 2) with hf
  have hpt : ∀ ω, ENNReal.ofReal ((dotProduct ((Real.sqrt (B : ℝ))⁻¹ • (CFC.sqrt Sg *ᵥ ζ ω))
        (Rs (N ω) s *ᵥ ((Real.sqrt (B : ℝ))⁻¹ • (CFC.sqrt Sg *ᵥ ζ ω)))
        - (B : ℝ)⁻¹ * (Sg * Rs (N ω) s).trace) ^ 2) = f (N ω) (ζ ω) := by
    intro ω
    simp only [hf]
    rw [pb82_quad_alg _ _ (pb82_sqrt_symm Sg), pb82A_trace Sg hS B hB]
    rfl
  have hfm : Measurable (Function.uncurry f) := by
    have hc : Continuous (fun p : Mat k l × Vec k =>
        (dotProduct p.2 (Matrix.mulVec (pb82A Sg B s p.1) p.2)
      - Matrix.trace (pb82A Sg B s p.1)) ^ 2) := by
      unfold pb82A
      fun_prop
    exact hc.measurable.ennreal_ofReal
  simp_rw [hpt]
  rw [pb82_tonelli P ζ N hζ hN hind _ hlaw f hfm]
  calc ∫⁻ y, ∫⁻ x, f y x ∂(Muon.Foundations.stdGaussianPi k) ∂(P.map N)
      ≤ ∫⁻ _y, ENNReal.ofReal ((k : ℝ) * (2 * (CSig / (s * B)) ^ 2)) ∂(P.map N) := by
        refine lintegral_mono fun M => ?_
        refine (pb82_quad_lintegral k (pb82A Sg B s M) (pb82A_symm Sg B s M)).trans ?_
        refine ENNReal.ofReal_le_ofReal ?_
        rw [pb82_trace_sq _ (pb82A_symm Sg B s M)]
        have := pb82A_fro Sg hS CSig hC B hB s hs M
        linarith
    _ = ENNReal.ofReal ((k : ℝ) * (2 * (CSig / (s * B)) ^ 2)) := by
        rw [lintegral_const, measure_univ, mul_one]

private lemma pb82_bil_alg {m n : ℕ} (r1 : Mat m m) (r2 : Mat n n) (X : Mat m n)
    (h1 : r1.transpose = r1) (c : ℝ) (z : Vec m) (w : Vec n) :
    dotProduct (c • (r1 *ᵥ z)) (X *ᵥ (c • (r2 *ᵥ w))) =
      dotProduct z (((c * c) • (r1 * X * r2)) *ᵥ w) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]
  have key : ∀ (x : Vec m) (y : Vec m), dotProduct (r1 *ᵥ x) y = dotProduct x (r1 *ᵥ y) := by
    intro x y
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h1,
      dotProduct_comm]
  rw [key, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  ring

private def pb82AC {m n : ℕ} (S1 : Mat m m) (S2 : Mat n n) (B : ℕ) (s : ℝ) (M : Mat m n) :
    Mat m n :=
  ((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹) • (CFC.sqrt S1 * Xs M s * CFC.sqrt S2)

private lemma pb82AC_fro {m n : ℕ} (S1 : Mat m m) (S2 : Mat n n) (h1 : S1.PosSemidef)
    (h2 : S2.PosSemidef) (CSig : ℝ) (hC1 : opNorm S1 ≤ CSig) (hC2 : opNorm S2 ≤ CSig)
    (B : ℕ) (hB : 0 < B) (s : ℝ) (hs : 0 < s) (M : Mat m n) :
    ∑ i, ∑ j, pb82AC S1 S2 B s M i j ^ 2 ≤ (n : ℝ) * (CSig / (2 * Real.sqrt s * B)) ^ 2 := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hC0 : 0 ≤ CSig := (pb8_opNorm_nonneg S1).trans hC1
  have e1 := pb82_opNorm_sqrt_mul_self S1 h1
  have e2 := pb82_opNorm_sqrt_mul_self S2 h2
  have hX := (lem_app_de_resolvent M s hs).2.2.1
  have hab : opNorm (CFC.sqrt S1) * opNorm (CFC.sqrt S2) ≤ CSig := by
    have ha := pb8_opNorm_nonneg (CFC.sqrt S1)
    have hb := pb8_opNorm_nonneg (CFC.sqrt S2)
    have hsq : (opNorm (CFC.sqrt S1) * opNorm (CFC.sqrt S2)) ^ 2 ≤ CSig ^ 2 := by
      calc (opNorm (CFC.sqrt S1) * opNorm (CFC.sqrt S2)) ^ 2
          = (opNorm (CFC.sqrt S1) * opNorm (CFC.sqrt S1)) *
            (opNorm (CFC.sqrt S2) * opNorm (CFC.sqrt S2)) := by ring
        _ ≤ CSig * CSig := by
          rw [e1, e2]
          exact mul_le_mul hC1 hC2 (pb8_opNorm_nonneg _) hC0
        _ = CSig ^ 2 := by ring
    exact le_of_sq_le_sq hsq hC0 |> fun h => by nlinarith [mul_nonneg ha hb]
  have h3 : opNorm (CFC.sqrt S1 * Xs M s * CFC.sqrt S2) ≤ CSig * (1 / (2 * Real.sqrt s)) := by
    calc opNorm (CFC.sqrt S1 * Xs M s * CFC.sqrt S2)
        ≤ opNorm (CFC.sqrt S1 * Xs M s) * opNorm (CFC.sqrt S2) := pb82_opNorm_mul_le _ _
      _ ≤ (opNorm (CFC.sqrt S1) * opNorm (Xs M s)) * opNorm (CFC.sqrt S2) :=
          mul_le_mul_of_nonneg_right (pb82_opNorm_mul_le _ _) (pb8_opNorm_nonneg _)
      _ ≤ (opNorm (CFC.sqrt S1) * (1 / (2 * Real.sqrt s))) * opNorm (CFC.sqrt S2) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hX (pb8_opNorm_nonneg _)) (pb8_opNorm_nonneg _)
      _ = (opNorm (CFC.sqrt S1) * opNorm (CFC.sqrt S2)) * (1 / (2 * Real.sqrt s)) := by ring
      _ ≤ CSig * (1 / (2 * Real.sqrt s)) := by
          exact mul_le_mul_of_nonneg_right hab (by positivity)
  have h4 : opNorm (pb82AC S1 S2 B s M) ≤ CSig / (2 * Real.sqrt s * B) := by
    unfold pb82AC
    rw [pb82_opNorm_smul, abs_of_nonneg (by positivity)]
    calc (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ *
          opNorm (CFC.sqrt S1 * Xs M s * CFC.sqrt S2)
        ≤ (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ * (CSig * (1 / (2 * Real.sqrt s))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = CSig / (2 * Real.sqrt s * B) := by
          have : (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ = (B : ℝ)⁻¹ := by
            rw [← mul_inv, Real.mul_self_sqrt hBr.le]
          rw [this]
          field_simp
  calc ∑ i, ∑ j, pb82AC S1 S2 B s M i j ^ 2 ≤ (n : ℝ) * opNorm (pb82AC S1 S2 B s M) ^ 2 :=
        pb82_fro_sq_le _
    _ ≤ (n : ℝ) * (CSig / (2 * Real.sqrt s * B)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pb8_opNorm_nonneg _) h4 2)
          (Nat.cast_nonneg n)

private lemma pb82_TC {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n : ℕ} (S1 : Mat m m) (S2 : Mat n n) (h1 : S1.PosSemidef) (h2 : S2.PosSemidef)
    (CSig : ℝ) (hC1 : opNorm S1 ≤ CSig) (hC2 : opNorm S2 ≤ CSig)
    (B : ℕ) (hB : 0 < B) (s : ℝ) (hs : 0 < s)
    (x : Ω' → Vec m × Vec n) (N : Ω' → Mat m n) (hx : Measurable x) (hN : Measurable N)
    (hind : IndepFun N x P) (hlaw : P.map x = gaussPair m n) :
    ∫⁻ ω, ENNReal.ofReal ((dotProduct ((Real.sqrt (B : ℝ))⁻¹ • (CFC.sqrt S1 *ᵥ (x ω).1))
        (Xs (N ω) s *ᵥ ((Real.sqrt (B : ℝ))⁻¹ • (CFC.sqrt S2 *ᵥ (x ω).2)))) ^ 2) ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * (CSig / (2 * Real.sqrt s * B)) ^ 2) := by
  have hRc : Continuous (fun M : Mat m n => Rs M s) := pb8_Rs_continuous s hs
  set f : Mat m n → (Vec m × Vec n) → ℝ≥0∞ := fun M p =>
    ENNReal.ofReal ((dotProduct p.1 (Matrix.mulVec (pb82AC S1 S2 B s M) p.2)) ^ 2) with hf
  have hpt : ∀ ω, ENNReal.ofReal ((dotProduct ((Real.sqrt (B : ℝ))⁻¹ • (CFC.sqrt S1 *ᵥ (x ω).1))
        (Xs (N ω) s *ᵥ ((Real.sqrt (B : ℝ))⁻¹ • (CFC.sqrt S2 *ᵥ (x ω).2)))) ^ 2) =
      f (N ω) (x ω) := by
    intro ω
    simp only [hf]
    rw [pb82_bil_alg _ _ _ (pb82_sqrt_symm S1)]
    rfl
  have hfm : Measurable (Function.uncurry f) := by
    have hc : Continuous (fun p : Mat m n × (Vec m × Vec n) =>
        (dotProduct p.2.1 (Matrix.mulVec (pb82AC S1 S2 B s p.1) p.2.2)) ^ 2) := by
      unfold pb82AC Xs
      fun_prop
    exact hc.measurable.ennreal_ofReal
  simp_rw [hpt]
  rw [pb82_tonelli P x N hx hN hind _ hlaw f hfm]
  calc ∫⁻ y, ∫⁻ p, f y p ∂(gaussPair m n) ∂(P.map N)
      ≤ ∫⁻ _y, ENNReal.ofReal ((n : ℝ) * (CSig / (2 * Real.sqrt s * B)) ^ 2) ∂(P.map N) := by
        refine lintegral_mono fun M => ?_
        refine (pb82_bilin (pb82AC S1 S2 B s M)).trans ?_
        exact ENNReal.ofReal_le_ofReal (pb82AC_fro S1 S2 h1 h2 CSig hC1 hC2 B hB s hs M)
    _ = ENNReal.ofReal ((n : ℝ) * (CSig / (2 * Real.sqrt s * B)) ^ 2) := by
        rw [lintegral_const, measure_univ, mul_one]

private lemma pb82_opNorm_le_of_sq_c {a b : ℕ} (U : Matrix (Fin a) (Fin b) ℂ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ y : Fin b → ℂ, ∑ k, ‖(U *ᵥ y) k‖ ^ 2 ≤ M ^ 2 * ∑ i, ‖y i‖ ^ 2) : opNorm U ≤ M := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x => ?_
  have hx := h (WithLp.ofLp x)
  have hsq : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin U)) x‖ ^ 2 ≤
      (M * ‖x‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct] using hx
  nlinarith [norm_nonneg ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin U)) x),
    mul_nonneg hM (norm_nonneg x)]

private lemma pb82_opNorm_complexify {a b : ℕ} (S : Mat a b) :
    opNorm (S.map (fun x : ℝ => (x : ℂ))) ≤ opNorm S := by
  refine pb82_opNorm_le_of_sq_c _ _ (pb8_opNorm_nonneg S) fun y => ?_
  have h1 := pb82_sum_sq_mulVec_le S (fun i => (y i).re)
  have h2 := pb82_sum_sq_mulVec_le S (fun i => (y i).im)
  have hre : ∀ k, ((S.map (fun x : ℝ => (x : ℂ))) *ᵥ y) k =
      (((S *ᵥ (fun i => (y i).re)) k : ℝ) : ℂ) + Complex.I * (((S *ᵥ (fun i => (y i).im)) k : ℝ) : ℂ) := by
    intro k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.ofReal_sum, Complex.ofReal_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    apply Complex.ext <;> simp
  have hn : ∀ k, ‖((S.map (fun x : ℝ => (x : ℂ))) *ᵥ y) k‖ ^ 2 =
      (S *ᵥ (fun i => (y i).re)) k ^ 2 + (S *ᵥ (fun i => (y i).im)) k ^ 2 := by
    intro k
    rw [hre k, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hy : ∀ i, ‖y i‖ ^ 2 = (y i).re ^ 2 + (y i).im ^ 2 := by
    intro i
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp_rw [hn, hy, Finset.sum_add_distrib]
  rw [mul_add]
  exact add_le_add h1 h2

private lemma pb82_abs_entry_le {a : ℕ} (K : Mat a a) (i j : Fin a) : |K i j| ≤ opNorm K := by
  classical
  have h := pb82_sum_sq_mulVec_le K (Pi.single j 1)
  have e1 : ∀ i, (K *ᵥ (Pi.single j (1 : ℝ))) i = K i j := fun i => by
    simp [Matrix.mulVec_single_one]
  have e2 : ∑ i, (Pi.single j (1 : ℝ) : Fin a → ℝ) i ^ 2 = 1 := by
    simp [Pi.single_apply]
  simp only [e1, e2, mul_one] at h
  have h3 : K i j ^ 2 ≤ ∑ k, K k j ^ 2 :=
    Finset.single_le_sum (f := fun k => K k j ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  exact abs_le_of_sq_le_sq (h3.trans h) (pb8_opNorm_nonneg K)

private lemma pb82_trace_mean_eq {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {p : ℕ} (X : Ω' → Mat p p)
    (hX : Measurable X) (c : ℝ) (hb : ∀ ω, opNorm (X ω) ≤ c) (S : Mat p p) :
    (S * Muon.mean P X).trace = ∫ ω, (S * X ω).trace ∂P := by
  have hmeas : ∀ i k, Measurable (fun ω => X ω k i) := fun i k =>
    (by fun_prop : Measurable fun M : Mat p p => M k i).comp hX
  have hint : ∀ i k, Integrable (fun ω => X ω k i) P := fun i k =>
    Integrable.mono' (integrable_const c) (hmeas i k).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact (pb82_abs_entry_le (X ω) k i).trans (hb ω))
  have hL : (S * Muon.mean P X).trace = ∑ i, ∑ k, S i k * ∫ ω, X ω k i ∂P := by
    simp [Matrix.trace, Matrix.mul_apply, Muon.mean]
  have hR : ∀ ω, (S * X ω).trace = ∑ i, ∑ k, S i k * X ω k i := fun ω => by
    simp [Matrix.trace, Matrix.mul_apply]
  simp only [hR]
  rw [hL, integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun k _ =>
    (hint i k).const_mul (S i k)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun k _ => (hint i k).const_mul (S i k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]

private lemma pb82_meas_tr {Ω' : Type*} [MeasurableSpace Ω'] {k : ℕ} (Sg : Mat k k)
    (R : Ω' → Mat k k) (hR : Measurable R) : Measurable (fun ω => (Sg * R ω).trace) := by
  have hent : ∀ i j, Measurable (fun ω => R ω i j) := fun i j =>
    (by fun_prop : Measurable fun M : Mat k k => M i j).comp hR
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (hent j i).const_mul _

private lemma pb82_meas_quad {Ω' : Type*} [MeasurableSpace Ω'] {k : ℕ} (Sg : Mat k k)
    (R : Ω' → Mat k k) (ζ : Ω' → Vec k) (c : ℝ) (hR : Measurable R) (hζ : Measurable ζ) :
    Measurable (fun ω => dotProduct (c • (Sg *ᵥ ζ ω)) (R ω *ᵥ (c • (Sg *ᵥ ζ ω)))) := by
  have hent : ∀ i j, Measurable (fun ω => R ω i j) := fun i j =>
    (by fun_prop : Measurable fun M : Mat k k => M i j).comp hR
  have hz : ∀ i, Measurable (fun ω => ζ ω i) := fun i => (measurable_pi_apply i).comp hζ
  simp only [dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.mul ?_ ?_
  · refine Measurable.mul measurable_const ?_
    exact Finset.measurable_sum _ fun j _ => (hz j).const_mul _
  · refine Finset.measurable_sum _ fun j _ => ?_
    refine Measurable.mul (hent i j) ?_
    refine Measurable.mul measurable_const ?_
    exact Finset.measurable_sum _ fun l _ => (hz l).const_mul _

private lemma pb82_side {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {k l : ℕ} (Sg : Mat k k) (hS : Sg.PosSemidef) (CSig : ℝ) (hC : opNorm Sg ≤ CSig)
    (B : ℕ) (hB : 0 < B) (s : ℝ) (hs : 0 < s)
    (ζ : Ω' → Vec k) (N0 Nf : Ω' → Mat k l) (hζ : Measurable ζ) (hN0 : Measurable N0)
    (hNf : Measurable Nf) (hind : IndepFun N0 ζ P)
    (hlaw : P.map ζ = Muon.Foundations.stdGaussianPi k)
    (hrank : ∀ᵐ ω ∂P, nuc (Rs (Nf ω) s - Rs (N0 ω) s) ≤ 4 / s)
    (Vr : ℝ) (hV0 : 0 ≤ Vr)
    (hvar : cVar P (fun ω => normTrace (Sg.map (fun x : ℝ => (x : ℂ))) B (Rs (Nf ω) s)) ≤
      ENNReal.ofReal Vr) :
    eLpNorm (fun ω => dotProduct ((Real.sqrt (B : ℝ))⁻¹ • (CFC.sqrt Sg *ᵥ ζ ω))
        (Rs (N0 ω) s *ᵥ ((Real.sqrt (B : ℝ))⁻¹ • (CFC.sqrt Sg *ᵥ ζ ω)))
        - (B : ℝ)⁻¹ * (Sg * Muon.mean P (fun ω => Rs (Nf ω) s)).trace) 2 P ≤
      ENNReal.ofReal (Real.sqrt ((k : ℝ) * (2 * (CSig / (s * B)) ^ 2)))
        + ENNReal.ofReal (CSig * (4 / s) / B) + ENNReal.ofReal (Real.sqrt Vr) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hRc : Continuous (fun M : Mat k l => Rs M s) := pb8_Rs_continuous s hs
  have hRm0 : Measurable (fun ω => Rs (N0 ω) s) := hRc.measurable.comp hN0
  have hRmf : Measurable (fun ω => Rs (Nf ω) s) := hRc.measurable.comp hNf
  set σ : ℝ := (B : ℝ)⁻¹ * (Sg * Muon.mean P (fun ω => Rs (Nf ω) s)).trace with hσ
  set u : Ω' → Vec k := fun ω => (Real.sqrt (B : ℝ))⁻¹ • (CFC.sqrt Sg *ᵥ ζ ω) with hu
  set f1 : Ω' → ℝ := fun ω => dotProduct (u ω) (Rs (N0 ω) s *ᵥ u ω)
      - (B : ℝ)⁻¹ * (Sg * Rs (N0 ω) s).trace with hf1
  set f2 : Ω' → ℝ := fun ω => (B : ℝ)⁻¹ * ((Sg * Rs (N0 ω) s).trace - (Sg * Rs (Nf ω) s).trace)
    with hf2
  set f3 : Ω' → ℝ := fun ω => (B : ℝ)⁻¹ * (Sg * Rs (Nf ω) s).trace - σ with hf3
  have hm1 : Measurable f1 :=
    (pb82_meas_quad (CFC.sqrt Sg) _ ζ _ hRm0 hζ).sub ((pb82_meas_tr Sg _ hRm0).const_mul _)
  have hm2 : Measurable f2 :=
    ((pb82_meas_tr Sg _ hRm0).sub (pb82_meas_tr Sg _ hRmf)).const_mul _
  have hm3 : Measurable f3 := ((pb82_meas_tr Sg _ hRmf).const_mul _).sub_const _
  have hsplit : (fun ω => dotProduct (u ω) (Rs (N0 ω) s *ᵥ u ω) - σ) = (f1 + f2) + f3 := by
    funext ω
    simp only [Pi.add_apply, hf1, hf2, hf3]
    ring
  show eLpNorm (fun ω => dotProduct (u ω) (Rs (N0 ω) s *ᵥ u ω) - σ) 2 P ≤ _
  rw [hsplit]
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  refine add_le_add ((eLpNorm_add_le (by norm_num)).trans (add_le_add ?_ ?_)) ?_
  · -- T1
    refine pb82_eLpNorm_le P f1 hm1 _ (Real.sqrt_nonneg _) ?_
    rw [Real.sq_sqrt (by positivity)]
    exact pb82_T1 P Sg hS CSig hC B hB s hs ζ N0 hζ hN0 hind hlaw
  · -- T2
    have hbd : ∀ᵐ ω ∂P, ‖f2 ω‖ ≤ CSig * (4 / s) / B := by
      filter_upwards [hrank] with ω hω
      have h1 := trace_mul_le_opNorm_mul_nuc Sg (Rs (N0 ω) s - Rs (Nf ω) s)
      have e : Rs (N0 ω) s - Rs (Nf ω) s = (-1 : ℝ) • (Rs (Nf ω) s - Rs (N0 ω) s) := by
        rw [neg_smul, one_smul, neg_sub]
      have hn : nuc (Rs (N0 ω) s - Rs (Nf ω) s) ≤ 4 / s := by
        rw [e, nuc_smul]; simpa using hω
      have h2 : |(Sg * (Rs (N0 ω) s - Rs (Nf ω) s)).trace| ≤ CSig * (4 / s) :=
        h1.trans (mul_le_mul hC hn (nuc_nonneg _) ((pb8_opNorm_nonneg _).trans hC))
      rw [Matrix.mul_sub, Matrix.trace_sub] at h2
      show ‖(B : ℝ)⁻¹ * ((Sg * Rs (N0 ω) s).trace - (Sg * Rs (Nf ω) s).trace)‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hBr)]
      calc (B : ℝ)⁻¹ * |(Sg * Rs (N0 ω) s).trace - (Sg * Rs (Nf ω) s).trace|
          ≤ (B : ℝ)⁻¹ * (CSig * (4 / s)) := mul_le_mul_of_nonneg_left h2 (inv_pos.mpr hBr).le
        _ = CSig * (4 / s) / B := by ring
    have := eLpNorm_le_of_ae_bound (p := 2) hm2.aestronglyMeasurable hbd
    simpa using this
  · -- T3
    have hY : ∀ ω, normTrace (Sg.map (fun x : ℝ => (x : ℂ))) B (Rs (Nf ω) s) =
        (((B : ℝ)⁻¹ * (Sg * Rs (Nf ω) s).trace : ℝ) : ℂ) := by
      intro ω
      unfold normTrace
      simp [Matrix.trace, Matrix.mul_apply, Matrix.map_apply]
    have hb : ∀ ω, opNorm (Rs (Nf ω) s) ≤ 1 / s := fun ω => (lem_app_de_resolvent _ s hs).1
    have hmean : ∫ ω, (B : ℝ)⁻¹ * (Sg * Rs (Nf ω) s).trace ∂P = σ := by
      rw [integral_const_mul, ← pb82_trace_mean_eq P (fun ω => Rs (Nf ω) s) hRmf (1 / s) hb Sg]
    have hcv : cVar P (fun ω => normTrace (Sg.map (fun x : ℝ => (x : ℂ))) B (Rs (Nf ω) s)) =
        ∫⁻ ω, ENNReal.ofReal ((f3 ω) ^ 2) ∂P := by
      unfold cVar
      simp_rw [hY]
      rw [integral_complex_ofReal, hmean]
      refine lintegral_congr fun ω => ?_
      congr 1
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    refine pb82_eLpNorm_le P f3 hm3 _ (Real.sqrt_nonneg _) ?_
    rw [Real.sq_sqrt hV0, ← hcv]
    exact hvar

private lemma pb82_A1 (m B γ CSig s sm : ℝ) (hB : 0 < B) (hm : m ≤ γ * B) (hm0 : 0 ≤ m)
    (hsm : 0 < sm) (hs : sm ≤ s) (hC0 : 0 ≤ CSig) :
    Real.sqrt (m * (2 * (CSig / (s * B)) ^ 2)) ≤ Real.sqrt (2 * γ) * CSig / sm / Real.sqrt B := by
  have hγ : 0 ≤ γ := by
    by_contra h
    push Not at h
    nlinarith
  have hs0 : 0 < s := lt_of_lt_of_le hsm hs
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp only [div_pow, mul_pow, Real.sq_sqrt hB.le, Real.sq_sqrt (show 0 ≤ 2 * γ by positivity)]
  have h1 : m * (2 * (CSig ^ 2 / (s ^ 2 * B ^ 2))) ≤ γ * B * (2 * (CSig ^ 2 / (s ^ 2 * B ^ 2))) :=
    mul_le_mul_of_nonneg_right hm (by positivity)
  refine h1.trans ?_
  have e1 : γ * B * (2 * (CSig ^ 2 / (s ^ 2 * B ^ 2))) = 2 * γ * CSig ^ 2 / (s ^ 2 * B) := by
    field_simp
  rw [e1, div_div]
  have : sm ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hsm.le hs 2
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_right this hB.le)

private lemma pb82_A2 (B CSig s sm : ℝ) (hB : 1 ≤ B) (hsm : 0 < sm) (hs : sm ≤ s)
    (hC0 : 0 ≤ CSig) : CSig * (4 / s) / B ≤ 4 * CSig / sm / Real.sqrt B := by
  have hB0 : 0 < B := by linarith
  have hs0 : 0 < s := lt_of_lt_of_le hsm hs
  have hsB : 1 ≤ Real.sqrt B := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hB
  have hsB0 : 0 < Real.sqrt B := by linarith
  have hBs : Real.sqrt B ≤ B := by
    have := Real.sqrt_le_sqrt (show B ≤ B * B by nlinarith)
    rwa [Real.sqrt_mul_self hB0.le] at this
  calc CSig * (4 / s) / B ≤ CSig * (4 / sm) / B := by
        gcongr
    _ ≤ CSig * (4 / sm) / Real.sqrt B := by
        gcongr
    _ = 4 * CSig / sm / Real.sqrt B := by ring

private lemma pb82_A3 (B CSig C3 S : ℝ) (hB : 0 < B) (hC3 : 0 ≤ C3) (hS0 : 0 ≤ S) (hS1 : S ≤ 1)
    (hC0 : 0 ≤ CSig) :
    Real.sqrt (C3 * CSig ^ 2 * S / B) ≤ Real.sqrt C3 * CSig / Real.sqrt B := by
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp only [div_pow, mul_pow, Real.sq_sqrt hC3, Real.sq_sqrt hB.le]
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (by positivity) hS1) hB.le

private lemma pb82_A4 (n B γ CSig s sm : ℝ) (hB : 0 < B) (hn : n ≤ γ * B) (hn0 : 0 ≤ n)
    (hsm : 0 < sm) (hs : sm ≤ s) (hC0 : 0 ≤ CSig) :
    Real.sqrt (n * (CSig / (2 * Real.sqrt s * B)) ^ 2) ≤
      CSig * Real.sqrt γ / (2 * Real.sqrt sm) / Real.sqrt B := by
  have hγ : 0 ≤ γ := by
    by_contra h
    push Not at h
    nlinarith
  have hs0 : 0 < s := lt_of_lt_of_le hsm hs
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  have hsm' : 0 < Real.sqrt sm := Real.sqrt_pos.mpr hsm
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp only [div_pow, mul_pow, Real.sq_sqrt hB.le, Real.sq_sqrt hγ,
    Real.sq_sqrt hsm.le, Real.sq_sqrt hs0.le]
  have h1 : n * (CSig ^ 2 / (2 ^ 2 * s * B ^ 2)) ≤ γ * B * (CSig ^ 2 / (2 ^ 2 * s * B ^ 2)) :=
    mul_le_mul_of_nonneg_right hn (by positivity)
  refine h1.trans ?_
  have e1 : γ * B * (CSig ^ 2 / (2 ^ 2 * s * B ^ 2)) = γ * CSig ^ 2 / (4 * s * B) := by
    field_simp
    ring
  have e2 : CSig ^ 2 * γ / (2 ^ 2 * sm) / B = γ * CSig ^ 2 / (4 * sm * B) := by
    field_simp
    ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hB.le)

section Glue

variable {m n B : ℕ} {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'}

private lemma pb82_meas_batch (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    Measurable (frozenBatchG F S s) := by
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have : frozenBatchG F S s = fun ω => (B : ℝ)⁻¹ • ∑ a : Fin B, pb8Q F (S.zw s a ω) := rfl
  rw [this]
  exact (Finset.measurable_sum _ fun a _ => (pb8Q_measurable F).comp (S.meas s a)).const_smul ((B : ℝ)⁻¹)

private lemma pb82_meas_buf (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) : Measurable (WeightedBuf w F S t) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  unfold WeightedBuf
  exact Measurable.tsum fun j => (pb82_meas_batch F S (t + 1 - (j : ℤ))).const_smul (w j)

private lemma pb82_meas_del (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t s : ℤ) (a : Fin B) : Measurable (WeightedBufDel w F S t s a) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  unfold WeightedBufDel
  refine Measurable.tsum fun j => ?_
  refine Measurable.const_smul (Measurable.const_smul ?_ ((B : ℝ)⁻¹)) (w j)
  refine Finset.measurable_sum _ fun b _ => ?_
  by_cases h : t + 1 - (j : ℤ) = s ∧ b = a
  · simp only [if_pos h]; exact measurable_const
  · simp only [if_neg h]; exact (pb8Q_measurable F).comp (S.meas _ _)

private lemma pb82_decomp [IsProbabilityMeasure P] (w : ℕ → ℝ) (hw : WeightClass w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    ∀ᵐ ω ∂P, WeightedBuf w F S t ω = delBufAge w F S t j ω +
      (w j * ageD F S t j ω) • outer (ageU F S t j ω) (ageV F S t j ω) := by
  filter_upwards [weightedBuf_summable_ae w hw.1 F S] with ω hω
  have h := weightedBuf_eq_del_add w F S t (t + 1 - (j : ℤ)) (slotOne F.hB) j rfl ω (hω t)
  rw [h]
  unfold delBufAge
  congr 1
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hcc : (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ = (B : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hB]
  have e1 : sampleTerm F S (t + 1 - (j : ℤ)) (slotOne F.hB) ω =
      ageD F S t j ω • outer (Matrix.mulVec (rOut F.C) (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).1)
        (Matrix.mulVec (rIn F.C) (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).2) := by
    unfold sampleTerm
    rw [pb8_rOut_outer_rIn]
    rfl
  rw [e1]
  unfold ageU ageV momU momV
  ext i k
  simp only [Matrix.smul_apply, smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply]
  rw [← hcc]
  ring

private lemma pb82_law_fst (x : Ω' → Vec m × Vec n) (hx : Measurable x)
    (hlaw : P.map x = gaussPair m n) [IsProbabilityMeasure P] :
    P.map (fun ω => (x ω).1) = Muon.Foundations.stdGaussianPi m := by
  have h := Measure.map_map (μ := P) measurable_fst hx
  have e : (fun ω => (x ω).1) = Prod.fst ∘ x := rfl
  rw [e, ← h, hlaw]
  unfold gaussPair
  rw [Measure.map_fst_prod]
  simp

private lemma pb82_law_snd (x : Ω' → Vec m × Vec n) (hx : Measurable x)
    (hlaw : P.map x = gaussPair m n) [IsProbabilityMeasure P] :
    P.map (fun ω => (x ω).2) = Muon.Foundations.stdGaussianPi n := by
  have h := Measure.map_map (μ := P) measurable_snd hx
  have e : (fun ω => (x ω).2) = Prod.snd ∘ x := rfl
  rw [e, ← h, hlaw]
  unfold gaussPair
  rw [Measure.map_snd_prod]
  simp

private lemma pb82_Rts_eq {a b : ℕ} (M : Mat a b) (s : ℝ) : Rts M s = Rs Mᵀ s := by
  unfold Rts Rs
  rw [Matrix.transpose_transpose]

private lemma pb82_delV_eq {a b : ℕ} (M : Mat a b) (v : Vec b) (s : ℝ) :
    delV M v s = delU Mᵀ v s := by
  unfold delV delU
  rw [pb82_Rts_eq]

private lemma pb82_meas_bil {Ω'' : Type*} [MeasurableSpace Ω''] {a b : ℕ} (r1 : Mat a a)
    (r2 : Mat b b) (X : Ω'' → Mat a b) (z : Ω'' → Vec a) (w : Ω'' → Vec b) (c : ℝ)
    (hX : Measurable X) (hz : Measurable z) (hw : Measurable w) :
    Measurable (fun ω => dotProduct (c • (r1 *ᵥ z ω)) (X ω *ᵥ (c • (r2 *ᵥ w ω)))) := by
  have hent : ∀ i j, Measurable (fun ω => X ω i j) := fun i j =>
    (by fun_prop : Measurable fun M : Mat a b => M i j).comp hX
  have hz' : ∀ i, Measurable (fun ω => z ω i) := fun i => (measurable_pi_apply i).comp hz
  have hw' : ∀ i, Measurable (fun ω => w ω i) := fun i => (measurable_pi_apply i).comp hw
  simp only [dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.mul ?_ ?_
  · refine Measurable.mul measurable_const ?_
    exact Finset.measurable_sum _ fun j _ => (hz' j).const_mul _
  · refine Finset.measurable_sum _ fun j _ => ?_
    refine Measurable.mul (hent i j) ?_
    refine Measurable.mul measurable_const ?_
    exact Finset.measurable_sum _ fun l _ => (hw' l).const_mul _

end Glue

private lemma pb82_sumPow_le (w : ℕ → ℝ) (hw : WeightClass w) : 0 ≤ sumPow w 2 ∧ sumPow w 2 ≤ 1 := by
  have hw0 : ∀ j, 0 ≤ w j := hw.1.1
  have hs1 : Summable w := hw.1.2.1
  have hs2 : Summable (fun j => w j ^ 2) := by
    refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) hs1
    have := hw.2.1 j
    nlinarith [hw0 j]
  refine ⟨tsum_nonneg fun j => sq_nonneg _, ?_⟩
  unfold sumPow
  calc ∑' j, w j ^ 2 ≤ ∑' j, w j := by
        refine Summable.tsum_le_tsum (fun j => ?_) hs2 hs1
        have := hw.2.1 j
        nlinarith [hw0 j]
    _ ≤ 1 := hw.2.2

private lemma pb82_sum_bound (m B γ CSig s sm C3 S : ℝ) (hB : 1 ≤ B) (hm : m ≤ γ * B)
    (hm0 : 0 ≤ m) (hsm : 0 < sm) (hs : sm ≤ s) (hC0 : 0 ≤ CSig) (hC3 : 0 ≤ C3) (hS0 : 0 ≤ S)
    (hS1 : S ≤ 1) :
    ENNReal.ofReal (Real.sqrt (m * (2 * (CSig / (s * B)) ^ 2))) +
      ENNReal.ofReal (CSig * (4 / s) / B) + ENNReal.ofReal (Real.sqrt (C3 * CSig ^ 2 * S / B)) ≤
    ENNReal.ofReal ((Real.sqrt (2 * γ) * CSig / sm + 4 * CSig / sm + Real.sqrt C3 * CSig) /
      Real.sqrt B) := by
  have hB0 : 0 < B := by linarith
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB0
  have h1 := pb82_A1 m B γ CSig s sm hB0 hm hm0 hsm hs hC0
  have h2 := pb82_A2 B CSig s sm hB hsm hs hC0
  have h3 := pb82_A3 B CSig C3 S hB0 hC3 hS0 hS1 hC0
  calc _ ≤ ENNReal.ofReal (Real.sqrt (2 * γ) * CSig / sm / Real.sqrt B) +
        ENNReal.ofReal (4 * CSig / sm / Real.sqrt B) +
        ENNReal.ofReal (Real.sqrt C3 * CSig / Real.sqrt B) :=
        add_le_add (add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2))
          (ENNReal.ofReal_le_ofReal h3)
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

section Final

private lemma pb82_hTr {a b : ℕ} : Measurable (fun M : Mat a b => Mᵀ) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k =>
    (by fun_prop : Measurable fun M : Mat a b => M k i)

private lemma pb82_U {I : Set ℝ} (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w) {Ω' : Type} [MeasurableSpace Ω']
    (P : Measure Ω') [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (CS γ sm : ℝ) (hCS0 : 0 ≤ CS)
    (hCo' : opNorm F.C.Sout ≤ CS) (hm : (m : ℝ) ≤ γ * B) (hsmpos : 0 < sm)
    (j : ℕ) (s : ℝ) (hs : s ∈ I) (hsle : sm ≤ s) (C3 : ℝ) (hC3 : 0 ≤ C3)
    (hvar : cVar P (fun ω => normTrace (F.C.Sout.map (fun x : ℝ => (x : ℂ))) B
      (Rs (WeightedBuf w F S t ω) s)) ≤
      ENNReal.ofReal (C3 * CS ^ 2 * sumPow w 2 / B)) :
    eLpNorm (fun ω => delU (delBufAge w F S t j ω) (ageU F S t j ω) s
      - sigmaB w F S t s) 2 P ≤ ENNReal.ofReal ((Real.sqrt (2 * γ) * CS / sm + 4 * CS / sm
        + Real.sqrt C3 * CS) / Real.sqrt B) := by
  have hs0 : 0 < s := lt_of_lt_of_le hsmpos hsle
  have hBpos : 0 < B := F.hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hBpos
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hx : Measurable (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) := S.meas _ _
  have hlaw : P.map (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) = gaussPair m n := by
    unfold gaussPair
    exact S.law (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hind : IndepFun (delBufAge w F S t j) (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) P :=
    weightedBufDel_indep w F S t (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hN0 : Measurable (delBufAge w F S t j) :=
    pb82_meas_del w F S t (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hWB : Measurable (WeightedBuf w F S t) := pb82_meas_buf w F S t
  have hdec := pb82_decomp w hw F S t j
  obtain ⟨hS0, hS1⟩ := pb82_sumPow_le w hw
  have hrank : ∀ᵐ ω ∂P, nuc (Rs (WeightedBuf w F S t ω) s - Rs (delBufAge w F S t j ω) s)
      ≤ 4 / s := by
    filter_upwards [hdec] with ω hω
    exact (lem_app_de_coeff hI hIpos (delBufAge w F S t j ω) (ageU F S t j ω)
      (ageV F S t j ω) (WeightedBuf w F S t ω) (ageD F S t j ω) (w j) hω (hw.1.1 j)
      (hw.2.1 j) s hs).2.2.2.2.2
  have hlawU : P.map (fun ω => (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).1) =
      Muon.Foundations.stdGaussianPi m :=
    pb82_law_fst (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) hx hlaw
  have hindU : IndepFun (delBufAge w F S t j)
      (fun ω => (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).1) P :=
    hind.comp measurable_id measurable_fst
  have hside := pb82_side P F.C.Sout F.C.psdOut CS hCo' B hBpos s hs0
    (fun ω => (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).1) (delBufAge w F S t j)
    (WeightedBuf w F S t) hx.fst hN0 hWB hindU hlawU hrank
    (C3 * CS ^ 2 * sumPow w 2 / B)
    (div_nonneg (mul_nonneg (mul_nonneg hC3 (sq_nonneg _)) hS0) (Nat.cast_nonneg B)) hvar
  have e : (fun ω => delU (delBufAge w F S t j ω) (ageU F S t j ω) s - sigmaB w F S t s) =
      fun ω => dotProduct ((Real.sqrt (B : ℝ))⁻¹ •
          (CFC.sqrt F.C.Sout *ᵥ (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).1))
        (Rs (delBufAge w F S t j ω) s *ᵥ ((Real.sqrt (B : ℝ))⁻¹ •
          (CFC.sqrt F.C.Sout *ᵥ (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).1)))
        - (B : ℝ)⁻¹ * (F.C.Sout * Muon.mean P (fun ω => Rs (WeightedBuf w F S t ω) s)).trace := by
    funext ω
    unfold delU ageU momU rOut sigmaB expRes
    rfl
  rw [e]
  exact hside.trans (pb82_sum_bound (m : ℝ) B γ CS s sm C3
    (sumPow w 2) hB1 hm hm0 hsmpos hsle hCS0 hC3 hS0 hS1)

private lemma pb82_V {I : Set ℝ} (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w) {Ω' : Type} [MeasurableSpace Ω']
    (P : Measure Ω') [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (CS γ sm : ℝ) (hCS0 : 0 ≤ CS)
    (hCi' : opNorm F.C.Sin ≤ CS) (hn : (n : ℝ) ≤ γ * B) (hsmpos : 0 < sm)
    (j : ℕ) (s : ℝ) (hs : s ∈ I) (hsle : sm ≤ s) (C3 : ℝ) (hC3 : 0 ≤ C3)
    (hvar : cVar P (fun ω => normTrace (F.C.Sin.map (fun x : ℝ => (x : ℂ))) B
      (Rs ((WeightedBuf w F S t ω)ᵀ) s)) ≤
      ENNReal.ofReal (C3 * CS ^ 2 * sumPow w 2 / B)) :
    eLpNorm (fun ω => delV (delBufAge w F S t j ω) (ageV F S t j ω) s
      - sigmaTildeB w F S t s) 2 P ≤ ENNReal.ofReal ((Real.sqrt (2 * γ) * CS / sm + 4 * CS / sm
        + Real.sqrt C3 * CS) / Real.sqrt B) := by
  have hs0 : 0 < s := lt_of_lt_of_le hsmpos hsle
  have hBpos : 0 < B := F.hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hBpos
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hx : Measurable (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) := S.meas _ _
  have hlaw : P.map (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) = gaussPair m n := by
    unfold gaussPair
    exact S.law (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hind : IndepFun (delBufAge w F S t j) (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) P :=
    weightedBufDel_indep w F S t (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hN0 : Measurable (delBufAge w F S t j) :=
    pb82_meas_del w F S t (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hWB : Measurable (WeightedBuf w F S t) := pb82_meas_buf w F S t
  have hdec := pb82_decomp w hw F S t j
  obtain ⟨hS0, hS1⟩ := pb82_sumPow_le w hw
  have hrank : ∀ᵐ ω ∂P, nuc (Rs ((WeightedBuf w F S t ω)ᵀ) s
      - Rs ((delBufAge w F S t j ω)ᵀ) s) ≤ 4 / s := by
    filter_upwards [hdec] with ω hω
    have hω' : (WeightedBuf w F S t ω)ᵀ = (delBufAge w F S t j ω)ᵀ +
        (w j * ageD F S t j ω) • outer (ageV F S t j ω) (ageU F S t j ω) := by
      rw [hω]
      simp [Matrix.transpose_add, Matrix.transpose_smul, Muon.outer,
        Matrix.transpose_vecMulVec]
    exact (lem_app_de_coeff hI hIpos (delBufAge w F S t j ω)ᵀ (ageV F S t j ω)
      (ageU F S t j ω) (WeightedBuf w F S t ω)ᵀ (ageD F S t j ω) (w j) hω' (hw.1.1 j)
      (hw.2.1 j) s hs).2.2.2.2.2
  have hlawV : P.map (fun ω => (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).2) =
      Muon.Foundations.stdGaussianPi n :=
    pb82_law_snd (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) hx hlaw
  have hindV : IndepFun (fun ω => (delBufAge w F S t j ω)ᵀ)
      (fun ω => (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).2) P :=
    hind.comp pb82_hTr measurable_snd
  have hside := pb82_side P F.C.Sin F.C.psdIn CS hCi' B hBpos s hs0
    (fun ω => (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).2)
    (fun ω => (delBufAge w F S t j ω)ᵀ) (fun ω => (WeightedBuf w F S t ω)ᵀ) hx.snd
    (pb82_hTr.comp hN0) (pb82_hTr.comp hWB) hindV hlawV hrank
    (C3 * CS ^ 2 * sumPow w 2 / B)
    (div_nonneg (mul_nonneg (mul_nonneg hC3 (sq_nonneg _)) hS0) (Nat.cast_nonneg B)) hvar
  have e : (fun ω => delV (delBufAge w F S t j ω) (ageV F S t j ω) s
      - sigmaTildeB w F S t s) = fun ω => dotProduct
        ((Real.sqrt (B : ℝ))⁻¹ • (CFC.sqrt F.C.Sin *ᵥ (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).2))
        (Rs ((delBufAge w F S t j ω)ᵀ) s *ᵥ ((Real.sqrt (B : ℝ))⁻¹ •
          (CFC.sqrt F.C.Sin *ᵥ (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).2)))
        - (B : ℝ)⁻¹ * (F.C.Sin * Muon.mean P (fun ω => Rs ((WeightedBuf w F S t ω)ᵀ) s)).trace := by
    funext ω
    rw [pb82_delV_eq]
    unfold delU ageV momV rIn sigmaTildeB expResT
    simp only [pb82_Rts_eq]
  rw [e]
  exact hside.trans (pb82_sum_bound (n : ℝ) B γ CS s sm C3 (sumPow w 2) hB1 hn hn0 hsmpos
    hsle hCS0 hC3 hS0 hS1)

private lemma pb82_C {I : Set ℝ} (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    {m n B : ℕ} (w : ℕ → ℝ) {Ω' : Type} [MeasurableSpace Ω']
    (P : Measure Ω') [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (CS γ sm : ℝ) (hCS0 : 0 ≤ CS)
    (hCo' : opNorm F.C.Sout ≤ CS) (hCi' : opNorm F.C.Sin ≤ CS) (hn : (n : ℝ) ≤ γ * B)
    (hsmpos : 0 < sm) (j : ℕ) (s : ℝ) (hs : s ∈ I) (hsle : sm ≤ s) :
    eLpNorm (fun ω => delC (delBufAge w F S t j ω) (ageU F S t j ω) (ageV F S t j ω) s) 2 P ≤
      ENNReal.ofReal (CS * Real.sqrt γ / (2 * Real.sqrt sm) / Real.sqrt B) := by
  have hs0 : 0 < s := lt_of_lt_of_le hsmpos hsle
  have hBpos : 0 < B := F.hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hx : Measurable (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) := S.meas _ _
  have hlaw : P.map (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) = gaussPair m n := by
    unfold gaussPair
    exact S.law (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hind : IndepFun (delBufAge w F S t j) (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) P :=
    weightedBufDel_indep w F S t (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hN0 : Measurable (delBufAge w F S t j) :=
    pb82_meas_del w F S t (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hXc : Continuous (fun M : Mat m n => Xs M s) := by
    unfold Xs
    exact (pb8_Rs_continuous s hs0).matrix_mul continuous_id
  have hmeasC : Measurable (fun ω => delC (delBufAge w F S t j ω) (ageU F S t j ω)
      (ageV F S t j ω) s) :=
    pb82_meas_bil (CFC.sqrt F.C.Sout) (CFC.sqrt F.C.Sin)
      (fun ω => Xs (delBufAge w F S t j ω) s)
      (fun ω => (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).1)
      (fun ω => (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).2) _ (hXc.measurable.comp hN0)
      hx.fst hx.snd
  refine (pb82_eLpNorm_le P _ hmeasC (Real.sqrt ((n : ℝ) * (CS / (2 * Real.sqrt s * B)) ^ 2))
    (Real.sqrt_nonneg _) ?_).trans
    (ENNReal.ofReal_le_ofReal (pb82_A4 (n : ℝ) B γ CS s sm hBr hn hn0 hsmpos hsle hCS0))
  rw [Real.sq_sqrt (by positivity)]
  exact pb82_TC P F.C.Sout F.C.Sin F.C.psdOut F.C.psdIn CS hCo' hCi' B hBpos s hs0
    (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) (delBufAge w F S t j) hx hN0 hind hlaw

end Final

end Scalars
/-! ## Concentration of the deleted-sample scalars (`lem:app-de-scalars`) -/

/-- `lem:app-de-scalars`, snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.1267–1272):
\begin{lemma}[Concentration of the deleted-sample scalars]\label{lem:app-de-scalars}
For every age $j$ and $s\in I$,
\begin{equation}\label{eqn:app-de-scalars}
\norm{\mathsf U_{j}-\sigma_B(s)}_2+\norm{\mathsf V_{j}-\tilde\sigma_B(s)}_2+\norm{\mathsf C_{j}}_2\le\frac{C_I}{\sqrt B}.
\end{equation}
\end{lemma}
-/
theorem lem_app_de_scalars (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    (CSig γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m n B : ℕ) (w : ℕ → ℝ), WeightClass w →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
        (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ),
        opNorm F.C.Sout ≤ CSig → opNorm F.C.Sin ≤ CSig →
        (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
        ∀ (j : ℕ), ∀ s ∈ I,
          eLpNorm (fun ω => delU (delBufAge w F S t j ω) (ageU F S t j ω) s
              - sigmaB w F S t s) 2 P
            + eLpNorm (fun ω => delV (delBufAge w F S t j ω) (ageV F S t j ω) s
              - sigmaTildeB w F S t s) 2 P
            + eLpNorm (fun ω => delC (delBufAge w F S t j ω) (ageU F S t j ω) (ageV F S t j ω) s)
              2 P
          ≤ ENNReal.ofReal (C / Real.sqrt (B : ℝ)) := by
  obtain ⟨Ci, hCi0, Hi⟩ := lem_app_de_variance_i I hI hIpos CSig γ
  obtain ⟨Cii, hCii0, Hii⟩ := lem_app_de_variance_ii I hI hIpos CSig γ
  have hsm0 : 0 ≤ sInf I := Real.sInf_nonneg fun x hx => (hIpos hx).le
  have hCS0 : 0 ≤ max CSig 0 := le_max_right _ _
  have hCSle : CSig ≤ max CSig 0 := le_max_left _ _
  refine ⟨(Real.sqrt (2 * γ) * max CSig 0 / sInf I + 4 * max CSig 0 / sInf I
      + Real.sqrt Ci * max CSig 0) +
    (Real.sqrt (2 * γ) * max CSig 0 / sInf I + 4 * max CSig 0 / sInf I
      + Real.sqrt Cii * max CSig 0) +
    max CSig 0 * Real.sqrt γ / (2 * Real.sqrt (sInf I)), by positivity, ?_⟩
  intro m n B w hw Ω' _ P _ F S t hCo hCi hm hn j s hs
  have hsmpos : 0 < sInf I := hIpos (hI.sInf_mem ⟨s, hs⟩)
  have hsle : sInf I ≤ s := csInf_le hI.bddBelow hs
  have hCo' : opNorm F.C.Sout ≤ max CSig 0 := hCo.trans hCSle
  have hCi' : opNorm F.C.Sin ≤ max CSig 0 := hCi.trans hCSle
  have hU := pb82_U hI hIpos w hw P F S t (max CSig 0) γ (sInf I) hCS0 hCo' hm hsmpos j s hs hsle
    Ci hCi0 (by
      have := Hi m n B w hw Ω' P F S t hCo hCi hm hn s hs
        (F.C.Sout.map (fun x : ℝ => (x : ℂ))) (max CSig 0)
        ((pb82_opNorm_complexify _).trans hCo')
      exact this)
  have hV := pb82_V hI hIpos w hw P F S t (max CSig 0) γ (sInf I) hCS0 hCi' hn hsmpos j s hs hsle
    Cii hCii0 (by
      have := Hii m n B w hw Ω' P F S t hCo hCi hm hn s hs
        (F.C.Sin.map (fun x : ℝ => (x : ℂ))) (max CSig 0)
        ((pb82_opNorm_complexify _).trans hCi')
      exact this)
  have hC := pb82_C hI hIpos w P F S t (max CSig 0) γ (sInf I) hCS0 hCo' hCi' hn hsmpos j s hs hsle
  calc _ ≤ _ := add_le_add (add_le_add hU hV) hC
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-! ## Private machinery for `lem:app-de-replace` -/

section Replace

private lemma pb83_algB (h s σ σt U V C m q Ξ : ℝ) (hm : 0 ≤ m) (hh : |h| ≤ m)
    (hq : q = s * σ * σt) (hq0 : 0 ≤ q) (hs : 0 ≤ s) (hσ : 0 ≤ σ)
    (hΞ : Ξ = s * σ * |σt - V| + s * |V| * |σ - U| + (1 + q) * |C| + C ^ 2) :
    |((1 + h * C) ^ 2 + s * h ^ 2 * U * V) - (1 + q * h ^ 2)| ≤ (1 + m) ^ 3 * Ξ := by
  set T1 : ℝ := s * σ * |σt - V| + s * |V| * |σ - U| with hT1
  have hT1nn : 0 ≤ T1 := by positivity
  have hT : |s * U * V - q| ≤ T1 := by
    have e : s * U * V - q = -(s * σ * (σt - V)) - s * V * (σ - U) := by rw [hq]; ring
    rw [e]
    calc |-(s * σ * (σt - V)) - s * V * (σ - U)|
        ≤ |-(s * σ * (σt - V))| + |s * V * (σ - U)| := abs_sub _ _
      _ = T1 := by
        rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg hσ, hT1]
  have e : ((1 + h * C) ^ 2 + s * h ^ 2 * U * V) - (1 + q * h ^ 2)
      = 2 * h * C + h ^ 2 * C ^ 2 + h ^ 2 * (s * U * V - q) := by ring
  rw [e]
  have h2 : h ^ 2 ≤ m ^ 2 := by
    have := sq_le_sq' (by linarith [abs_le.1 hh]) (abs_le.1 hh).2
    exact this
  have hC0 : 0 ≤ |C| := abs_nonneg C
  have t1 : |2 * h * C| ≤ 2 * m * |C| := by
    rw [abs_mul, abs_mul, abs_two]
    have : 0 ≤ |C| := hC0
    nlinarith
  have t2 : |h ^ 2 * C ^ 2| ≤ m ^ 2 * C ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg h), abs_of_nonneg (sq_nonneg C)]
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have t3 : |h ^ 2 * (s * U * V - q)| ≤ m ^ 2 * T1 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg h)]
    exact mul_le_mul h2 hT (abs_nonneg _) (sq_nonneg _)
  have hsum : |2 * h * C + h ^ 2 * C ^ 2 + h ^ 2 * (s * U * V - q)|
      ≤ 2 * m * |C| + m ^ 2 * C ^ 2 + m ^ 2 * T1 :=
    (abs_add_three _ _ _).trans (by linarith)
  refine hsum.trans ?_
  rw [hΞ]
  have c1 : m ^ 2 ≤ (1 + m) ^ 3 := by nlinarith [sq_nonneg m, mul_nonneg hm (sq_nonneg m)]
  have c2 : 2 * m ≤ (1 + m) ^ 3 * (1 + q) := by
    have : 2 * m ≤ (1 + m) ^ 3 := by nlinarith [sq_nonneg m, mul_nonneg hm (sq_nonneg m)]
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (1 + m) ^ 3) hq0]
  have a1 := mul_le_mul_of_nonneg_right c1 hT1nn
  have a2 := mul_le_mul_of_nonneg_right c2 hC0
  have a3 := mul_le_mul_of_nonneg_right c1 (sq_nonneg C)
  nlinarith

/-- generic `a/Λ - b/D` bound -/
private lemma pb83_G2 (a b Lam D : ℝ) (hL : 1 / 2 ≤ Lam) (hD : 1 ≤ D) :
    |a / Lam - b / D| ≤ 2 * |a - b| + 2 * |b| * |D - Lam| := by
  have hL0 : 0 < Lam := by linarith
  have hD0 : 0 < D := by linarith
  have e : a / Lam - b / D = (a - b) / Lam + b * (D - Lam) / (Lam * D) := by
    field_simp; ring
  rw [e]
  have i1 : |(a - b) / Lam| ≤ 2 * |a - b| := by
    rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
    nlinarith [abs_nonneg (a - b)]
  have i2 : |b * (D - Lam) / (Lam * D)| ≤ 2 * |b| * |D - Lam| := by
    rw [abs_div, abs_of_pos (mul_pos hL0 hD0), div_le_iff₀ (mul_pos hL0 hD0), ← mul_assoc]
    have h3 : 1 ≤ 2 * (Lam * D) := by nlinarith
    have h4 : 0 ≤ |b| * |D - Lam| := by positivity
    rw [abs_mul]
    nlinarith
  exact (abs_add_le _ _).trans (add_le_add i1 i2)

private lemma pb83_pt (Z D Ψ m a τ lam : ℝ) (hm : 0 < m) (hτ : 0 < τ) (hlam : 0 < lam)
    (hΨ : 0 ≤ Ψ) (hgood : |D| ≤ m → Ψ ≤ τ → |Z| ≤ a) :
    Z ^ 2 ≤ a ^ 2 + lam / 2 * Z ^ 4 + 1 / (2 * lam * m ^ 2) * D ^ 2 + 1 / (2 * lam * τ) * Ψ := by
  have p1 : 0 ≤ lam / 2 * Z ^ 4 := by positivity
  have p2 : 0 ≤ 1 / (2 * lam * m ^ 2) * D ^ 2 := by positivity
  have p3 : 0 ≤ 1 / (2 * lam * τ) * Ψ := by positivity
  by_cases hg : |D| ≤ m ∧ Ψ ≤ τ
  · have := hgood hg.1 hg.2
    have : Z ^ 2 ≤ a ^ 2 := by
      rw [← sq_abs Z]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    linarith
  · have hbad : 1 ≤ D ^ 2 / m ^ 2 + Ψ / τ := by
      rw [not_and_or] at hg
      rcases hg with h | h
      · push Not at h
        have : 1 ≤ D ^ 2 / m ^ 2 := by
          rw [le_div_iff₀ (by positivity), one_mul]
          rw [← sq_abs D]
          exact pow_le_pow_left₀ hm.le h.le 2
        have : 0 ≤ Ψ / τ := by positivity
        linarith
      · push Not at h
        have : 1 ≤ Ψ / τ := by rw [le_div_iff₀ hτ, one_mul]; exact h.le
        have : 0 ≤ D ^ 2 / m ^ 2 := by positivity
        linarith
    have hyoung : Z ^ 2 ≤ lam / 2 * Z ^ 4 + 1 / (2 * lam) := by
      have : 0 ≤ (lam * Z ^ 2 - 1) ^ 2 := sq_nonneg _
      have e : lam / 2 * Z ^ 4 + 1 / (2 * lam) - Z ^ 2 = (lam * Z ^ 2 - 1) ^ 2 / (2 * lam) := by
        field_simp; ring
      have : 0 ≤ (lam * Z ^ 2 - 1) ^ 2 / (2 * lam) := by positivity
      linarith
    have e2 : 1 / (2 * lam) * (D ^ 2 / m ^ 2 + Ψ / τ)
        = 1 / (2 * lam * m ^ 2) * D ^ 2 + 1 / (2 * lam * τ) * Ψ := by
      field_simp
    have : 1 / (2 * lam) ≤ 1 / (2 * lam) * (D ^ 2 / m ^ 2 + Ψ / τ) :=
      le_mul_of_one_le_right (by positivity) hbad
    nlinarith [sq_nonneg a]

private lemma pb83_L2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z D Ψ : Ω → ℝ) (hZ : Measurable Z) (hD : Measurable D) (hΨm : Measurable Ψ)
    (hΨ0 : ∀ ω, 0 ≤ Ψ ω)
    (m a τ lam K eD eΨ : ℝ) (hm : 0 < m) (ha : 0 ≤ a) (hτ : 0 < τ) (hlam : 0 < lam)
    (hgood : ∀ ω, |D ω| ≤ m → Ψ ω ≤ τ → |Z ω| ≤ a)
    (hD2 : ∫⁻ ω, ENNReal.ofReal (D ω ^ 2) ∂P ≤ ENNReal.ofReal eD)
    (hΨ1 : ∫⁻ ω, ENNReal.ofReal (Ψ ω) ∂P ≤ ENNReal.ofReal eΨ)
    (hZ4 : ∫⁻ ω, ENNReal.ofReal (Z ω ^ 4) ∂P ≤ ENNReal.ofReal K) (hK : 0 ≤ K) (heD : 0 ≤ eD)
    (heΨ : 0 ≤ eΨ) :
    ∫⁻ ω, ENNReal.ofReal (Z ω ^ 2) ∂P ≤
      ENNReal.ofReal (a ^ 2 + (lam * K + (eD / m ^ 2 + eΨ / τ) / lam) / 2) := by
  have pt : ∀ ω, ENNReal.ofReal (Z ω ^ 2) ≤ ENNReal.ofReal (a ^ 2) +
      ENNReal.ofReal (lam / 2) * ENNReal.ofReal (Z ω ^ 4) +
      ENNReal.ofReal (1 / (2 * lam * m ^ 2)) * ENNReal.ofReal (D ω ^ 2) +
      ENNReal.ofReal (1 / (2 * lam * τ)) * ENNReal.ofReal (Ψ ω) := by
    intro ω
    have := hΨ0 ω
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (pb83_pt (Z ω) (D ω) (Ψ ω) m a τ lam hm hτ hlam (hΨ0 ω)
      (hgood ω))
  have m4 : Measurable (fun ω => ENNReal.ofReal (Z ω ^ 4)) :=
    ENNReal.measurable_ofReal.comp (hZ.pow_const 4)
  have m2 : Measurable (fun ω => ENNReal.ofReal (D ω ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hD.pow_const 2)
  have m1 : Measurable (fun ω => ENNReal.ofReal (Ψ ω)) := ENNReal.measurable_ofReal.comp hΨm
  calc ∫⁻ ω, ENNReal.ofReal (Z ω ^ 2) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (a ^ 2) +
      ENNReal.ofReal (lam / 2) * ENNReal.ofReal (Z ω ^ 4) +
      ENNReal.ofReal (1 / (2 * lam * m ^ 2)) * ENNReal.ofReal (D ω ^ 2) +
      ENNReal.ofReal (1 / (2 * lam * τ)) * ENNReal.ofReal (Ψ ω)) ∂P := lintegral_mono pt
    _ = ENNReal.ofReal (a ^ 2) +
      ENNReal.ofReal (lam / 2) * ∫⁻ ω, ENNReal.ofReal (Z ω ^ 4) ∂P +
      ENNReal.ofReal (1 / (2 * lam * m ^ 2)) * ∫⁻ ω, ENNReal.ofReal (D ω ^ 2) ∂P +
      ENNReal.ofReal (1 / (2 * lam * τ)) * ∫⁻ ω, ENNReal.ofReal (Ψ ω) ∂P := by
        rw [lintegral_add_right _ (m1.const_mul _), lintegral_add_right _ (m2.const_mul _),
          lintegral_add_right _ (m4.const_mul _), lintegral_const, lintegral_const_mul _ m4,
          lintegral_const_mul _ m2, lintegral_const_mul _ m1]
        simp
    _ ≤ ENNReal.ofReal (a ^ 2) +
      ENNReal.ofReal (lam / 2) * ENNReal.ofReal K +
      ENNReal.ofReal (1 / (2 * lam * m ^ 2)) * ENNReal.ofReal eD +
      ENNReal.ofReal (1 / (2 * lam * τ)) * ENNReal.ofReal eΨ := by gcongr
    _ = ENNReal.ofReal (a ^ 2 + (lam * K + (eD / m ^ 2 + eΨ / τ) / lam) / 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
        ring


set_option maxHeartbeats 800000 in
private lemma pb83_good (ϖ d s σ σt U V C m κ ρ Ψ Lam D q : ℝ) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1)
    (hm1 : 1 ≤ m) (hd : |d| ≤ m) (hs : 0 < s) (hσ : 0 ≤ σ) (hσt : 0 ≤ σt)
    (hq : q = s * σ * σt) (hκ1 : 1 ≤ κ) (hσκ : σ ≤ κ) (hsσκ : s * σt ≤ κ) (hsκ : s ≤ κ)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hLam : Lam = (1 + ϖ * d * C) ^ 2 + s * (ϖ * d) ^ 2 * U * V)
    (hD : D = 1 + q * (ϖ * d) ^ 2)
    (hΨ : Ψ = (s * σ * |σt - V| + (s * σt + s * |V - σt|) * |σ - U| + (1 + q) * |C|
        + C ^ 2) + |U - σ| + |V - σt|)
    (hΨτ : Ψ ≤ ρ / (4 * κ * (1 + m) ^ 5)) :
    1 / 2 ≤ Lam ∧
    |d * (1 + ϖ * d * C) / Lam - d / D| ≤ ρ ∧
    |d ^ 2 * U / Lam - σ * d ^ 2 / D| ≤ ρ ∧
    |-(s * d ^ 2 * V) / Lam - (-(s * σt * d ^ 2)) / D| ≤ ρ := by
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hm0 : 0 ≤ m := by linarith
  have hh : |ϖ * d| ≤ m := by
    rw [abs_mul, abs_of_nonneg hϖ0]
    calc ϖ * |d| ≤ 1 * |d| := mul_le_mul_of_nonneg_right hϖ1 (abs_nonneg _)
      _ ≤ m := by linarith
  set Ξ : ℝ := s * σ * |σt - V| + s * |V| * |σ - U| + (1 + q) * |C| + C ^ 2 with hΞ
  have hVb : |V| ≤ σt + |V - σt| := by
    have := abs_sub_abs_le_abs_sub V σt
    rw [abs_of_nonneg hσt] at this
    linarith
  have hΞΨ : Ξ ≤ Ψ := by
    rw [hΨ, hΞ]
    have : s * |V| * |σ - U| ≤ (s * σt + s * |V - σt|) * |σ - U| := by
      have : s * |V| ≤ s * σt + s * |V - σt| := by nlinarith
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have := abs_nonneg (U - σ)
    have := abs_nonneg (V - σt)
    linarith
  have hdU : |U - σ| + Ξ ≤ Ψ := by
    rw [hΨ, hΞ]
    have : s * |V| * |σ - U| ≤ (s * σt + s * |V - σt|) * |σ - U| := by
      have : s * |V| ≤ s * σt + s * |V - σt| := by nlinarith
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have := abs_nonneg (V - σt)
    linarith
  have hdV : |V - σt| + Ξ ≤ Ψ := by
    rw [hΨ, hΞ]
    have : s * |V| * |σ - U| ≤ (s * σt + s * |V - σt|) * |σ - U| := by
      have : s * |V| ≤ s * σt + s * |V - σt| := by nlinarith
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have := abs_nonneg (U - σ)
    linarith
  have hΞ0 : 0 ≤ Ξ := by positivity
  have hCΞ : |C| ≤ Ξ := by
    have h1 : 0 ≤ s * σ * |σt - V| := by positivity
    have h2 : 0 ≤ s * |V| * |σ - U| := by positivity
    have h3 : 0 ≤ q * |C| := by positivity
    have h4 := sq_nonneg C
    rw [hΞ]; nlinarith
  have hΛD : |Lam - D| ≤ (1 + m) ^ 3 * Ξ := by
    rw [hLam, hD]
    refine pb83_algB (ϖ * d) s σ σt U V C m q Ξ hm0 hh hq hq0 hs.le hσ hΞ
  have h1m : (0:ℝ) < 1 + m := by linarith
  have hpow : (1 + m) ^ 3 * (ρ / (4 * κ * (1 + m) ^ 5)) ≤ 1 / 4 := by
    have e : (1 + m) ^ 3 * (ρ / (4 * κ * (1 + m) ^ 5)) = ρ / (4 * κ * (1 + m) ^ 2) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have h2 : 1 ≤ (1 + m) ^ 2 := one_le_pow₀ (by linarith)
    have h3 : 1 ≤ κ * (1 + m) ^ 2 := one_le_mul_of_one_le_of_one_le hκ1 h2
    linarith
  have hΞτ : (1 + m) ^ 3 * Ξ ≤ 1 / 4 :=
    ((mul_le_mul_of_nonneg_left (hΞΨ.trans hΨτ) (by positivity))).trans hpow
  have hD1 : 1 ≤ D := by
    rw [hD]; nlinarith [mul_nonneg hq0 (sq_nonneg (ϖ * d))]
  have hLam2 : 1 / 2 ≤ Lam := by
    have := (abs_le.1 hΛD).1
    linarith
  -- common size bounds
  have hLτ : 4 * κ * (1 + m) ^ 5 * Ψ ≤ ρ := by
    have hpos : 0 < 4 * κ * (1 + m) ^ 5 := by positivity
    have := mul_le_mul_of_nonneg_left hΨτ hpos.le
    rw [mul_div_cancel₀ _ hpos.ne'] at this
    exact this
  have hΨ0 : 0 ≤ Ψ := hΞ0.trans hΞΨ
  have hm2 : m ^ 2 ≤ (1 + m) ^ 2 := pow_le_pow_left₀ hm0 (by linarith) 2
  have hm2' : m ^ 2 ≤ (1 + m) ^ 5 := by
    have : (1 + m) ^ 2 ≤ (1 + m) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  have hd2 : d ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs d]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hm3 : m * (1 + m) ^ 3 ≤ (1 + m) ^ 5 := by
    have : m ≤ (1 + m) ^ 2 := le_trans (by linarith : m ≤ 1 + m) (le_self_pow₀ (by linarith) (by norm_num))
    calc m * (1 + m) ^ 3 ≤ (1 + m) ^ 2 * (1 + m) ^ 3 :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = (1 + m) ^ 5 := by ring
  have hK5 : 0 ≤ (1 + m) ^ 5 := by positivity
  have hΞκΨ : (1 + m) ^ 5 * Ξ ≤ κ * (1 + m) ^ 5 * Ψ := by
    have : Ξ ≤ κ * Ψ := le_trans hΞΨ (le_mul_of_one_le_left hΨ0 hκ1)
    calc (1 + m) ^ 5 * Ξ ≤ (1 + m) ^ 5 * (κ * Ψ) := mul_le_mul_of_nonneg_left this hK5
      _ = κ * (1 + m) ^ 5 * Ψ := by ring
  have hκE : (1 + m) ^ 5 ≤ κ * (1 + m) ^ 5 := le_mul_of_one_le_left hK5 hκ1
  have hm2E : m ^ 2 * (1 + m) ^ 3 ≤ (1 + m) ^ 5 := by
    calc m ^ 2 * (1 + m) ^ 3 ≤ (1 + m) ^ 2 * (1 + m) ^ 3 :=
          mul_le_mul_of_nonneg_right hm2 (by positivity)
      _ = (1 + m) ^ 5 := by ring
  have hmm : m * m ≤ (1 + m) ^ 5 := by rw [← sq]; exact hm2'
  have hD2 : |d ^ 2| ≤ m ^ 2 := by rw [abs_of_nonneg (sq_nonneg d)]; exact hd2
  have hP : ∀ x : ℝ, 0 ≤ x → x ≤ Ψ → 4 * κ * (1 + m) ^ 5 * x ≤ ρ := fun x hx hxΨ =>
    le_trans (mul_le_mul_of_nonneg_left hxΨ (by positivity)) hLτ
  refine ⟨hLam2, ?_, ?_, ?_⟩
  · have := pb83_G2 (d * (1 + ϖ * d * C)) d Lam D hLam2 hD1
    refine this.trans ?_
    have e1 : |d * (1 + ϖ * d * C) - d| = |d| * |ϖ * d| * |C| := by
      have : d * (1 + ϖ * d * C) - d = d * (ϖ * d) * C := by ring
      rw [this, abs_mul, abs_mul]
    rw [e1]
    have t1 : |d| * |ϖ * d| * |C| ≤ (1 + m) ^ 5 * Ξ := by
      have : |d| * |ϖ * d| ≤ m * m := mul_le_mul hd hh (abs_nonneg _) hm0
      calc |d| * |ϖ * d| * |C| ≤ (m * m) * |C| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ ≤ (m * m) * Ξ := mul_le_mul_of_nonneg_left hCΞ (by positivity)
        _ ≤ (1 + m) ^ 5 * Ξ := mul_le_mul_of_nonneg_right hmm hΞ0
    have t2 : |d| * |D - Lam| ≤ (1 + m) ^ 5 * Ξ := by
      rw [abs_sub_comm]
      calc |d| * |Lam - D| ≤ m * ((1 + m) ^ 3 * Ξ) := mul_le_mul hd hΛD (abs_nonneg _) hm0
        _ = (m * (1 + m) ^ 3) * Ξ := by ring
        _ ≤ (1 + m) ^ 5 * Ξ := mul_le_mul_of_nonneg_right hm3 hΞ0
    have hfin := hP Ψ hΨ0 le_rfl
    linarith only [this, t1, t2, hfin, hρ0, hΞκΨ]
  · have := pb83_G2 (d ^ 2 * U) (σ * d ^ 2) Lam D hLam2 hD1
    refine this.trans ?_
    have e1 : |d ^ 2 * U - σ * d ^ 2| = d ^ 2 * |U - σ| := by
      have : d ^ 2 * U - σ * d ^ 2 = d ^ 2 * (U - σ) := by ring
      rw [this, abs_mul, abs_of_nonneg (sq_nonneg d)]
    have e2 : |σ * d ^ 2| = σ * d ^ 2 := abs_of_nonneg (by positivity)
    rw [e1, e2]
    have t1 : d ^ 2 * |U - σ| ≤ κ * (1 + m) ^ 5 * |U - σ| :=
      mul_le_mul_of_nonneg_right (hd2.trans (hm2'.trans hκE)) (abs_nonneg _)
    have t2 : σ * d ^ 2 * |D - Lam| ≤ κ * (1 + m) ^ 5 * Ξ := by
      rw [abs_sub_comm]
      calc σ * d ^ 2 * |Lam - D| ≤ κ * m ^ 2 * ((1 + m) ^ 3 * Ξ) :=
            mul_le_mul (mul_le_mul hσκ hd2 (sq_nonneg _) (by linarith)) hΛD (abs_nonneg _)
              (by positivity)
        _ = κ * (m ^ 2 * (1 + m) ^ 3) * Ξ := by ring
        _ ≤ κ * (1 + m) ^ 5 * Ξ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hm2E (by linarith)) hΞ0
    have hfin := hP (|U - σ| + Ξ) (by positivity) hdU
    linarith only [this, t1, t2, hfin, hρ0]
  · have := pb83_G2 (-(s * d ^ 2 * V)) (-(s * σt * d ^ 2)) Lam D hLam2 hD1
    refine this.trans ?_
    have e1 : |-(s * d ^ 2 * V) - -(s * σt * d ^ 2)| = s * d ^ 2 * |V - σt| := by
      have : -(s * d ^ 2 * V) - -(s * σt * d ^ 2) = -(s * d ^ 2 * (V - σt)) := by ring
      rw [this, abs_neg, abs_mul, abs_mul, abs_of_nonneg hs.le, abs_of_nonneg (sq_nonneg d)]
    have e2 : |-(s * σt * d ^ 2)| = s * σt * d ^ 2 := by
      rw [abs_neg]; exact abs_of_nonneg (by positivity)
    rw [e1, e2]
    have t1 : s * d ^ 2 * |V - σt| ≤ κ * (1 + m) ^ 5 * |V - σt| := by
      have : s * d ^ 2 ≤ κ * (1 + m) ^ 5 :=
        (mul_le_mul hsκ hd2 (sq_nonneg _) (by linarith)).trans
          (mul_le_mul_of_nonneg_left hm2' (by linarith))
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have t2 : s * σt * d ^ 2 * |D - Lam| ≤ κ * (1 + m) ^ 5 * Ξ := by
      rw [abs_sub_comm]
      calc s * σt * d ^ 2 * |Lam - D| ≤ κ * m ^ 2 * ((1 + m) ^ 3 * Ξ) :=
            mul_le_mul (mul_le_mul hsσκ hd2 (sq_nonneg _) (by linarith)) hΛD (abs_nonneg _)
              (by positivity)
        _ = κ * (m ^ 2 * (1 + m) ^ 3) * Ξ := by ring
        _ ≤ κ * (1 + m) ^ 5 * Ξ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hm2E (by linarith)) hΞ0
    have hfin := hP (|V - σt| + Ξ) (by positivity) hdV
    linarith only [this, t1, t2, hfin, hρ0]

private lemma pb83_S_le (K ρ : ℝ) (hK : 0 ≤ K) (hρ0 : 0 < ρ) :
    ρ ^ 2 + (ρ ^ 2 / (K + 1) * K + (1 / ((ρ ^ 2)⁻¹) ^ 2) / (ρ ^ 2 / (K + 1))) / 2
      ≤ (3 / 2 + (K + 1) / 2) * ρ ^ 2 := by
  have hK1 : 0 < K + 1 := by linarith
  have e1 : 1 / ((ρ ^ 2)⁻¹) ^ 2 / (ρ ^ 2 / (K + 1)) = ρ ^ 2 * (K + 1) := by
    field_simp
  have e2 : ρ ^ 2 / (K + 1) * K ≤ ρ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK1]
    nlinarith [sq_nonneg ρ]
  rw [e1]
  nlinarith [sq_nonneg ρ]

private lemma pb83_lim (K C1 κ ρ : ℝ) :
    Tendsto (fun B : ℕ => ρ ^ 2 + (ρ ^ 2 / (K + 1) * K +
        (1 / ((ρ ^ 2)⁻¹) ^ 2 + (C1 / Real.sqrt (B : ℝ)) / (ρ / (4 * κ * (1 + (ρ ^ 2)⁻¹) ^ 5)))
          / (ρ ^ 2 / (K + 1))) / 2) atTop
      (𝓝 (ρ ^ 2 + (ρ ^ 2 / (K + 1) * K + (1 / ((ρ ^ 2)⁻¹) ^ 2) / (ρ ^ 2 / (K + 1))) / 2)) := by
  have hz : Tendsto (fun B : ℕ => C1 / Real.sqrt (B : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun B : ℕ => Real.sqrt (B : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact h1.const_div_atTop C1 |>.congr (fun _ => rfl)
  have hc : Continuous (fun x : ℝ => ρ ^ 2 + (ρ ^ 2 / (K + 1) * K +
        (1 / ((ρ ^ 2)⁻¹) ^ 2 + x / (ρ / (4 * κ * (1 + (ρ ^ 2)⁻¹) ^ 5)))
          / (ρ ^ 2 / (K + 1))) / 2) := by fun_prop
  have h0 := (hc.tendsto 0).comp hz
  simp only [Function.comp_def, zero_div, add_zero] at h0
  exact h0

private lemma pb83_exists_e (K C1 κ : ℝ) (hK : 0 ≤ K) (hC1 : 0 ≤ C1) (hκ : 1 ≤ κ) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ (B : ℕ) (x : ℝ),
      (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → x ≤ Real.sqrt (ρ ^ 2 + (ρ ^ 2 / (K + 1) * K +
        (1 / ((ρ ^ 2)⁻¹) ^ 2 + (C1 / Real.sqrt (B : ℝ)) / (ρ / (4 * κ * (1 + (ρ ^ 2)⁻¹) ^ 5)))
          / (ρ ^ 2 / (K + 1))) / 2)) → x ≤ e B := by
  have hK1 : 0 < K + 1 := by linarith
  refine ⟨fun B => ⨅ k : ℕ, Real.sqrt ((1 / ((k : ℝ) + 1)) ^ 2 + ((1 / ((k : ℝ) + 1)) ^ 2 / (K + 1) * K +
        (1 / (((1 / ((k : ℝ) + 1)) ^ 2)⁻¹) ^ 2 + (C1 / Real.sqrt (B : ℝ)) / ((1 / ((k : ℝ) + 1)) /
          (4 * κ * (1 + ((1 / ((k : ℝ) + 1)) ^ 2)⁻¹) ^ 5)))
          / ((1 / ((k : ℝ) + 1)) ^ 2 / (K + 1))) / 2), ?_, ?_⟩
  · rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · refine Eventually.of_forall fun B => lt_of_lt_of_le ha (le_ciInf fun k => Real.sqrt_nonneg _)
    · have ha2 : 0 < a ^ 2 / 2 := by positivity
      obtain ⟨k, hk⟩ := exists_nat_gt (2 * (3 / 2 + (K + 1) / 2) / a ^ 2)
      set ρ : ℝ := 1 / ((k : ℝ) + 1) with hρ
      have hk0 : (0 : ℝ) < ρ := by positivity
      have hk1 : ρ ≤ 1 := by
        rw [hρ, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      have hc0 : 0 < (3 / 2 + (K + 1) / 2 : ℝ) := by linarith
      have hSa : ρ ^ 2 + (ρ ^ 2 / (K + 1) * K + (1 / ((ρ ^ 2)⁻¹) ^ 2) / (ρ ^ 2 / (K + 1))) / 2
          < a ^ 2 / 2 := by
        refine lt_of_le_of_lt (pb83_S_le K ρ hK hk0) ?_
        have h1 : (3 / 2 + (K + 1) / 2) * ρ ^ 2 ≤ (3 / 2 + (K + 1) / 2) * ρ :=
          mul_le_mul_of_nonneg_left (by nlinarith) hc0.le
        have h2 : (3 / 2 + (K + 1) / 2) * ρ < a ^ 2 / 2 := by
          rw [hρ, mul_one_div, div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ (by positivity)] at hk
          nlinarith
        linarith
      have hev := (pb83_lim K C1 κ ρ).eventually (gt_mem_nhds
        (show ρ ^ 2 + (ρ ^ 2 / (K + 1) * K + (1 / ((ρ ^ 2)⁻¹) ^ 2) / (ρ ^ 2 / (K + 1))) / 2 <
          a ^ 2 / 2 + a ^ 2 / 2 by linarith))
      filter_upwards [hev] with B hB
      refine lt_of_le_of_lt (ciInf_le ⟨0, ?_⟩ k) ?_
      · rintro _ ⟨k', rfl⟩; exact Real.sqrt_nonneg _
      · rw [Real.sqrt_lt' ha]
        simp only [hρ] at hB
        linarith
  · intro B x hx
    refine le_ciInf fun k => ?_
    have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hk1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    exact hx _ hk0 hk1


private lemma pb83_cs {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (A Bv : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ Bv)
    (hA : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ ≤ ENNReal.ofReal A)
    (hB : ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ ≤ ENNReal.ofReal Bv) :
    ∫⁻ x, ENNReal.ofReal (f x * g x) ∂μ ≤ ENNReal.ofReal (Real.sqrt A * Real.sqrt Bv) := by
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (Real.HolderConjugate.two_two)
    (f := fun x => ENNReal.ofReal (f x)) (g := fun x => ENNReal.ofReal (g x))
    (ENNReal.measurable_ofReal.comp hf).aemeasurable (ENNReal.measurable_ofReal.comp hg).aemeasurable
  have e1 : ∀ h : α → ℝ, (∀ x, 0 ≤ h x) → ∫⁻ x, ENNReal.ofReal (h x) ^ (2 : ℝ) ∂μ
      = ∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂μ := by
    intro h h0
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (h0 x) (by norm_num)]
    congr 1
    exact Real.rpow_two _
  have e2 : ∫⁻ x, ENNReal.ofReal (f x * g x) ∂μ = ∫⁻ x, (ENNReal.ofReal (f x) * ENNReal.ofReal (g x)) ∂μ :=
    lintegral_congr fun x => ENNReal.ofReal_mul (hf0 x)
  rw [e2]
  refine hcs.trans ?_
  rw [e1 f hf0, e1 g hg0]
  have hh : (1 : ℝ) / 2 = 2⁻¹ := by norm_num
  calc (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal A) ^ (1 / (2 : ℝ)) * (ENNReal.ofReal Bv) ^ (1 / (2 : ℝ)) :=
        mul_le_mul' (ENNReal.rpow_le_rpow hA (by norm_num)) (ENNReal.rpow_le_rpow hB (by norm_num))
    _ = ENNReal.ofReal (Real.sqrt A * Real.sqrt Bv) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA0 (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hB0 (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]


private lemma pb83_lint_pow {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : Measurable f) (p : ℕ) (hp : 1 ≤ p) (K : ℝ) (hK : 0 ≤ K)
    (h : eLpNorm f (p : ENNReal) μ ≤ ENNReal.ofReal K) :
    ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ ≤ ENNReal.ofReal (K ^ p) := by
  have hp0 : ((p : ℕ) : ENNReal) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 (ENNReal.natCast_ne_top _)
    hf.aestronglyMeasurable, ENNReal.toReal_natCast] at h
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 := ENNReal.rpow_le_rpow h hpr.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpr.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hK hpr.le, Real.rpow_natCast] at h2
  refine le_trans (le_of_eq ?_) h2
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hpr.le,
    Real.rpow_natCast]

private lemma pb83_one_add_pow (a : ℝ) (ha : 0 ≤ a) (p : ℕ) : (1 + a) ^ p ≤ 2 ^ p * (1 + a ^ p) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ p ≤ 2 ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
      _ ≤ 2 ^ p * (1 + a ^ p) := le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg ha p])
  · calc (1 + a) ^ p ≤ (2 * a) ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
      _ = 2 ^ p * a ^ p := mul_pow _ _ _
      _ ≤ 2 ^ p * (1 + a ^ p) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)



private lemma pb83_young28 (u v : ℝ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    u ^ 16 * v ^ 12 ≤ u ^ 28 + v ^ 28 := by
  rcases le_total u v with h | h
  · have h1 : u ^ 16 ≤ v ^ 16 := pow_le_pow_left₀ (by linarith) h 16
    have h2 : u ^ 16 * v ^ 12 ≤ v ^ 16 * v ^ 12 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have : v ^ 16 * v ^ 12 = v ^ 28 := by ring
    nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ u) 28]
  · have h1 : v ^ 12 ≤ u ^ 12 := pow_le_pow_left₀ (by linarith) h 12
    have h2 : u ^ 16 * v ^ 12 ≤ u ^ 16 * u ^ 12 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have : u ^ 16 * u ^ 12 = u ^ 28 := by ring
    nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ v) 28]

private lemma pb83_G4 {m n : ℕ} (C : Covariances m n) (B : ℕ) (γ CSig : ℝ)
    (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) (hγ : 0 ≤ γ)
    (hC : opNorm C.Sout ≤ CSig ∧ opNorm C.Sin ≤ CSig) (Ah : Mat m n) (hA : fro Ah = 1) :
    ∫⁻ x, ENNReal.ofReal (((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ 4) ∂(gaussPair m n)
      ≤ ENNReal.ofReal (2 ^ 28 * (2 + ((Nat.doubleFactorial 27 : ℕ) : ℝ) ^ 2
          + (2 * CSig * γ) ^ 28 * ((Nat.doubleFactorial 55 : ℕ) : ℝ))) := by
  have hC0 : 0 ≤ CSig := le_trans (pb8_opNorm_nonneg _) hC.1
  have hNm : Measurable (momN C B : Vec m × Vec n → ℝ) := by
    unfold momN eucNorm momU momV
    fun_prop
  have hNnn : ∀ x, 0 ≤ momN C B x := fun x => by unfold momN; positivity
  have hdm : Measurable (fun x : Vec m × Vec n => resid Ah x) := by unfold resid; fun_prop
  have hd := pb83_lint_pow (gaussPair m n) (fun x => resid Ah x) hdm 28 (by norm_num)
    (((Nat.doubleFactorial 27 : ℕ) : ℝ) ^ ((1 : ℝ) / 14)) (by positivity)
    (by simpa using lem_app_de_moments_ii Ah hA 14 (by norm_num))
  have hdD : (((Nat.doubleFactorial 27 : ℕ) : ℝ) ^ ((1 : ℝ) / 14)) ^ 28
      = ((Nat.doubleFactorial 27 : ℕ) : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  rw [hdD] at hd
  have hN := pb83_lint_pow (gaussPair m n) (momN C B) hNm 28 (by norm_num)
    (2 * CSig * γ * ((Nat.doubleFactorial 55 : ℕ) : ℝ) ^ ((1 : ℝ) / 28)) (by positivity)
    (by simpa using lem_app_de_moments_i C B γ CSig hdim hC 28 (by norm_num))
  have hNN : (2 * CSig * γ * ((Nat.doubleFactorial 55 : ℕ) : ℝ) ^ ((1 : ℝ) / 28)) ^ 28
      = (2 * CSig * γ) ^ 28 * ((Nat.doubleFactorial 55 : ℕ) : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast (((Nat.doubleFactorial 55 : ℕ) : ℝ) ^ ((1 : ℝ) / 28)),
      ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  rw [hNN] at hN
  have habsN : ∀ x : Vec m × Vec n, |momN C B x| = momN C B x := fun x => abs_of_nonneg (hNnn x)
  simp_rw [habsN] at hN
  have hpt : ∀ x : Vec m × Vec n, ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ 4
      ≤ 2 ^ 28 * 2 + 2 ^ 28 * |resid Ah x| ^ 28 + 2 ^ 28 * momN C B x ^ 28 := by
    intro x
    have h1 : ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ 4
        = (1 + |resid Ah x|) ^ 16 * (1 + momN C B x) ^ 12 := by ring
    rw [h1]
    refine (pb83_young28 _ _ (by linarith [abs_nonneg (resid Ah x)]) (by linarith [hNnn x])).trans ?_
    have a1 := pb83_one_add_pow _ (abs_nonneg (resid Ah x)) 28
    have a2 := pb83_one_add_pow _ (hNnn x) 28
    nlinarith [a1, a2]
  calc ∫⁻ x, ENNReal.ofReal (((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ 4) ∂(gaussPair m n)
      ≤ ∫⁻ x, (ENNReal.ofReal (2 ^ 28 * 2) + ENNReal.ofReal (2 ^ 28) * ENNReal.ofReal (|resid Ah x| ^ 28)
          + ENNReal.ofReal (2 ^ 28) * ENNReal.ofReal (momN C B x ^ 28)) ∂(gaussPair m n) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal (2 ^ 28 * 2) + ENNReal.ofReal (2 ^ 28) * ∫⁻ x, ENNReal.ofReal (|resid Ah x| ^ 28) ∂(gaussPair m n)
          + ENNReal.ofReal (2 ^ 28) * ∫⁻ x, ENNReal.ofReal (momN C B x ^ 28) ∂(gaussPair m n) := by
        have m1 : Measurable (fun x : Vec m × Vec n => ENNReal.ofReal (|resid Ah x| ^ 28)) :=
          ENNReal.measurable_ofReal.comp (by fun_prop)
        have m2 : Measurable (fun x : Vec m × Vec n => ENNReal.ofReal (momN C B x ^ 28)) :=
          ENNReal.measurable_ofReal.comp (by fun_prop)
        rw [lintegral_add_left ((m1.const_mul _).const_add _), lintegral_add_left measurable_const,
          lintegral_const_mul _ m1, lintegral_const_mul _ m2, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (2 ^ 28 * 2) + ENNReal.ofReal (2 ^ 28) * ENNReal.ofReal (((Nat.doubleFactorial 27 : ℕ) : ℝ) ^ 2)
          + ENNReal.ofReal (2 ^ 28) * ENNReal.ofReal ((2 * CSig * γ) ^ 28 * ((Nat.doubleFactorial 55 : ℕ) : ℝ)) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring


private lemma pb83_Rs_psd {k l : ℕ} (M : Mat k l) (s : ℝ) (hs : 0 < s) : (Rs M s).PosSemidef := by
  unfold Rs
  refine Matrix.PosSemidef.inv ?_
  have h1 : (M * Mᵀ).PosSemidef := by
    have := Matrix.posSemidef_self_mul_conjTranspose M
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have h2 : (s • (1 : Mat k k)).PosSemidef := Matrix.PosSemidef.one.smul hs.le
  exact h1.add h2

private lemma pb83_trA_nonneg {k l : ℕ} (Sg : Mat k k) (B : ℕ) (s : ℝ) (hs : 0 < s)
    (M : Mat k l) : 0 ≤ (pb82A Sg B s M).trace := by
  unfold pb82A
  rw [Matrix.trace_smul, smul_eq_mul]
  refine mul_nonneg (by positivity) ?_
  have hH : (CFC.sqrt Sg)ᴴ = CFC.sqrt Sg := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact pb82_sqrt_symm Sg
  have := (pb83_Rs_psd M s hs).mul_mul_conjTranspose_same (CFC.sqrt Sg)
  rw [hH] at this
  exact this.trace_nonneg

private lemma pb83_opA {k l : ℕ} (Sg : Mat k k) (hS : Sg.PosSemidef) (CSig : ℝ)
    (hC : opNorm Sg ≤ CSig) (B : ℕ) (hB : 0 < B) (s : ℝ) (hs : 0 < s) (M : Mat k l) :
    opNorm (pb82A Sg B s M) ≤ CSig / (s * B) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hr := pb82_opNorm_sqrt_mul_self Sg hS
  have hC0 : 0 ≤ CSig := (pb8_opNorm_nonneg Sg).trans hC
  have hR := (lem_app_de_resolvent M s hs).1
  have h1 : opNorm (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg) ≤ CSig * (1 / s) := by
    calc opNorm (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg)
        ≤ opNorm (CFC.sqrt Sg * Rs M s) * opNorm (CFC.sqrt Sg) := pb82_opNorm_mul_le _ _
      _ ≤ (opNorm (CFC.sqrt Sg) * opNorm (Rs M s)) * opNorm (CFC.sqrt Sg) :=
          mul_le_mul_of_nonneg_right (pb82_opNorm_mul_le _ _) (pb8_opNorm_nonneg _)
      _ = (opNorm (CFC.sqrt Sg) * opNorm (CFC.sqrt Sg)) * opNorm (Rs M s) := by ring
      _ ≤ CSig * (1 / s) := by
          rw [hr]
          exact mul_le_mul hC hR (pb8_opNorm_nonneg _) hC0
  unfold pb82A
  rw [pb82_opNorm_smul, abs_of_nonneg (by positivity)]
  calc (Real.sqrt (B : ℝ))⁻¹ ^ 2 * opNorm (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg)
      ≤ (Real.sqrt (B : ℝ))⁻¹ ^ 2 * (CSig * (1 / s)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = CSig / (s * B) := by
        rw [inv_pow, Real.sq_sqrt hBr.le]
        field_simp

private lemma pb83_sig {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {k l : ℕ} (Sg : Mat k k) (hS : Sg.PosSemidef) (CS : ℝ)
    (hC : opNorm Sg ≤ CS) (B : ℕ) (hB : 0 < B) (s : ℝ) (hs : 0 < s) (X : Ω' → Mat k l)
    (hX : Measurable X) (g : ℝ) (hk : (k : ℝ) ≤ g * B) :
    0 ≤ (B : ℝ)⁻¹ * (Sg * Muon.mean P (fun ω => Rs (X ω) s)).trace ∧
    (B : ℝ)⁻¹ * (Sg * Muon.mean P (fun ω => Rs (X ω) s)).trace ≤ g * CS / s := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hC0 : 0 ≤ CS := (pb8_opNorm_nonneg Sg).trans hC
  have hmeas : Measurable (fun ω => Rs (X ω) s) := (pb8_Rs_continuous s hs).measurable.comp hX
  have hb : ∀ ω, opNorm (Rs (X ω) s) ≤ 1 / s := fun ω => (lem_app_de_resolvent (X ω) s hs).1
  have h1 := pb82_trace_mean_eq P (fun ω => Rs (X ω) s) hmeas (1 / s) hb Sg
  have e : (B : ℝ)⁻¹ * (Sg * Muon.mean P (fun ω => Rs (X ω) s)).trace
      = ∫ ω, (pb82A Sg B s (X ω)).trace ∂P := by
    rw [h1, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    exact (pb82A_trace Sg hS B hB s (X ω)).symm
  rw [e]
  refine ⟨integral_nonneg fun ω => pb83_trA_nonneg Sg B s hs (X ω), ?_⟩
  have hpt : ∀ ω, ‖(pb82A Sg B s (X ω)).trace‖ ≤ g * CS / s := by
    intro ω
    rw [Real.norm_eq_abs]
    have hop := pb83_opA Sg hS CS hC B hB s hs (X ω)
    calc |(pb82A Sg B s (X ω)).trace| ≤ ∑ i, |(pb82A Sg B s (X ω)) i i| := by
          simpa [Matrix.trace, Matrix.diag] using
            Finset.abs_sum_le_sum_abs (fun i => (pb82A Sg B s (X ω)) i i) Finset.univ
      _ ≤ ∑ _i : Fin k, CS / (s * B) :=
          Finset.sum_le_sum fun i _ => (pb82_abs_entry_le _ i i).trans hop
      _ = (k : ℝ) * (CS / (s * B)) := by simp
      _ ≤ (g * B) * (CS / (s * B)) := mul_le_mul_of_nonneg_right hk (by positivity)
      _ = g * CS / s := by field_simp
  have := norm_integral_le_of_norm_le_const (μ := P) (ae_of_all _ hpt)
  exact (le_abs_self _).trans (by simpa using this)


private lemma pb83_L1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P ≤ ENNReal.ofReal (ε ^ 2)) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal ε := by
  have := pb83_cs P f (fun _ => 1) hf measurable_const hf0 (fun _ => zero_le_one) (ε ^ 2) 1
    (by positivity) zero_le_one h (by simp)
  simp only [mul_one, Real.sqrt_one] at this
  rwa [Real.sqrt_sq hε] at this

private lemma pb83_Psi_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f1 f2 f3 : Ω → ℝ) (hm1 : Measurable f1) (hm2 : Measurable f2)
    (hm3 : Measurable f3) (h1 : ∀ ω, 0 ≤ f1 ω) (h2 : ∀ ω, 0 ≤ f2 ω) (h3 : ∀ ω, 0 ≤ f3 ω)
    (ε : ℝ) (hε : 0 ≤ ε) (A1 A2 A3 s : ℝ) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3)
    (hs : 0 ≤ s)
    (e1 : ∫⁻ ω, ENNReal.ofReal (f1 ω ^ 2) ∂P ≤ ENNReal.ofReal (ε ^ 2))
    (e2 : ∫⁻ ω, ENNReal.ofReal (f2 ω ^ 2) ∂P ≤ ENNReal.ofReal (ε ^ 2))
    (e3 : ∫⁻ ω, ENNReal.ofReal (f3 ω ^ 2) ∂P ≤ ENNReal.ofReal (ε ^ 2)) :
    ∫⁻ ω, ENNReal.ofReal (A1 * f2 ω + A2 * f1 ω + s * (f2 ω * f1 ω) + A3 * f3 ω + f3 ω ^ 2) ∂P
      ≤ ENNReal.ofReal ((A1 + A2 + A3) * ε + (s + 1) * ε ^ 2) := by
  have l1 := pb83_L1 P f1 hm1 h1 ε hε e1
  have l2 := pb83_L1 P f2 hm2 h2 ε hε e2
  have l3 := pb83_L1 P f3 hm3 h3 ε hε e3
  have lp := pb83_cs P f2 f1 hm2 hm1 h2 h1 (ε ^ 2) (ε ^ 2) (by positivity) (by positivity) e2 e1
  rw [Real.sqrt_sq hε] at lp
  have pt : ∀ ω, ENNReal.ofReal (A1 * f2 ω + A2 * f1 ω + s * (f2 ω * f1 ω) + A3 * f3 ω + f3 ω ^ 2)
      = ENNReal.ofReal A1 * ENNReal.ofReal (f2 ω) + ENNReal.ofReal A2 * ENNReal.ofReal (f1 ω)
        + ENNReal.ofReal s * ENNReal.ofReal (f2 ω * f1 ω)
        + ENNReal.ofReal A3 * ENNReal.ofReal (f3 ω) + ENNReal.ofReal (f3 ω ^ 2) := by
    intro ω
    have := h1 ω; have := h2 ω; have := h3 ω
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul hA1, ENNReal.ofReal_mul hA2, ENNReal.ofReal_mul hs,
      ENNReal.ofReal_mul hA3]
  simp_rw [pt]
  have mm1 : Measurable (fun ω => ENNReal.ofReal (f1 ω)) := ENNReal.measurable_ofReal.comp hm1
  have mm2 : Measurable (fun ω => ENNReal.ofReal (f2 ω)) := ENNReal.measurable_ofReal.comp hm2
  have mm3 : Measurable (fun ω => ENNReal.ofReal (f3 ω)) := ENNReal.measurable_ofReal.comp hm3
  have mp : Measurable (fun ω => ENNReal.ofReal (f2 ω * f1 ω)) :=
    ENNReal.measurable_ofReal.comp (hm2.mul hm1)
  have mq : Measurable (fun ω => ENNReal.ofReal (f3 ω ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hm3.pow_const 2)
  have M2 : Measurable (fun ω => ENNReal.ofReal A1 * ENNReal.ofReal (f2 ω)
      + ENNReal.ofReal A2 * ENNReal.ofReal (f1 ω)) :=
    (mm2.const_mul _).add (mm1.const_mul _)
  have M3 : Measurable (fun ω => ENNReal.ofReal A1 * ENNReal.ofReal (f2 ω)
      + ENNReal.ofReal A2 * ENNReal.ofReal (f1 ω)
      + ENNReal.ofReal s * ENNReal.ofReal (f2 ω * f1 ω)) := M2.add (mp.const_mul _)
  have M4 : Measurable (fun ω => ENNReal.ofReal A1 * ENNReal.ofReal (f2 ω)
      + ENNReal.ofReal A2 * ENNReal.ofReal (f1 ω)
      + ENNReal.ofReal s * ENNReal.ofReal (f2 ω * f1 ω)
      + ENNReal.ofReal A3 * ENNReal.ofReal (f3 ω)) := M3.add (mm3.const_mul _)
  rw [lintegral_add_right _ mq, lintegral_add_left M3,
    lintegral_add_left M2, lintegral_add_left (mm2.const_mul _), lintegral_const_mul _ mm2,
    lintegral_const_mul _ mm1, lintegral_const_mul _ mp, lintegral_const_mul _ mm3]
  calc _ ≤ ENNReal.ofReal A1 * ENNReal.ofReal ε + ENNReal.ofReal A2 * ENNReal.ofReal ε
        + ENNReal.ofReal s * ENNReal.ofReal (ε * ε)
        + ENNReal.ofReal A3 * ENNReal.ofReal ε + ENNReal.ofReal (ε ^ 2) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul hA1, ← ENNReal.ofReal_mul hA2, ← ENNReal.ofReal_mul hs,
          ← ENNReal.ofReal_mul hA3,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring


private lemma pb83_forms {m n : ℕ} (M₀ : Mat m n) (u : Vec m) (v : Vec n) (d ϖ s q σ σt : ℝ)
    (hϖ : ϖ ≠ 0) (hL : 0 < delLambda M₀ (ϖ * d) u v s) (hq : 0 ≤ q) :
    (alpha1 M₀ (ϖ * d) u v s - ϖ * (d / (1 + (ϖ ^ 2 * q) * d ^ 2))) / ϖ
      = d * (1 + ϖ * d * delC M₀ u v s) / delLambda M₀ (ϖ * d) u v s
        - d / (1 + q * (ϖ * d) ^ 2) ∧
    (alpha2 M₀ (ϖ * d) u v s - ϖ ^ 2 * σ * (d ^ 2 / (1 + (ϖ ^ 2 * q) * d ^ 2))) / ϖ ^ 2
      = d ^ 2 * delU M₀ u s / delLambda M₀ (ϖ * d) u v s
        - σ * d ^ 2 / (1 + q * (ϖ * d) ^ 2) ∧
    (alpha3 M₀ (ϖ * d) u v s - -(s * (ϖ ^ 2 * σt * (d ^ 2 / (1 + (ϖ ^ 2 * q) * d ^ 2))))) / ϖ ^ 2
      = -(s * d ^ 2 * delV M₀ v s) / delLambda M₀ (ϖ * d) u v s
        - (-(s * σt * d ^ 2)) / (1 + q * (ϖ * d) ^ 2) := by
  have hD : 1 + q * (ϖ * d) ^ 2 ≠ 0 := by positivity
  have hD' : 1 + (ϖ ^ 2 * q) * d ^ 2 = 1 + q * (ϖ * d) ^ 2 := by ring
  have hLn := hL.ne'
  rw [hD']
  refine ⟨?_, ?_, ?_⟩
  · unfold alpha1
    field_simp
  · unfold alpha2
    field_simp
  · unfold alpha3
    field_simp

private lemma pb83_sqNorm_nonneg {a : ℕ} (x : Vec a) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

private lemma pb83_size {I : Set ℝ} (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    {m n : ℕ} (M₀ : Mat m n) (u : Vec m) (v : Vec n) (d ϖ s q σ σt κ : ℝ)
    (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hs : s ∈ I) (hq : 0 ≤ q) (hσ0 : 0 ≤ σ) (hσt0 : 0 ≤ σt)
    (hκ1 : 1 ≤ κ) (hσκ : σ ≤ κ) (hsσκ : s * σt ≤ κ) :
    |d * (1 + ϖ * d * delC M₀ u v s) / delLambda M₀ (ϖ * d) u v s
        - d / (1 + q * (ϖ * d) ^ 2)| ≤
      (coeffConst I + κ) * ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) ∧
    |d ^ 2 * delU M₀ u s / delLambda M₀ (ϖ * d) u v s
        - σ * d ^ 2 / (1 + q * (ϖ * d) ^ 2)| ≤
      (coeffConst I + κ) * ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) ∧
    |-(s * d ^ 2 * delV M₀ v s) / delLambda M₀ (ϖ * d) u v s
        - (-(s * σt * d ^ 2)) / (1 + q * (ϖ * d) ^ 2)| ≤
      (coeffConst I + κ) * ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) := by
  have hs0 : 0 < s := hIpos hs
  have hL := (lem_app_de_deletion M₀ (ϖ * d) u v (M₀ + (ϖ * d) • outer u v) s rfl hs0).1
  have hLn := hL.ne'
  obtain ⟨-, -, c3, c4, -⟩ := lem_app_de_coeff hI hIpos M₀ u v (M₀ + (ϖ * d) • outer u v) d ϖ rfl
    hϖ0.le hϖ1 s hs
  have c3' := c3 hϖ0
  have c4' := c4 hϖ0
  have hN0 : 0 ≤ sqNorm u + sqNorm v := add_nonneg (pb83_sqNorm_nonneg u) (pb83_sqNorm_nonneg v)
  set N := sqNorm u + sqNorm v with hN
  set Gb : ℝ := (1 + |d|) ^ 4 * (1 + N) ^ 3 with hGb
  have hN3 : 1 ≤ (1 + N) ^ 3 := one_le_pow₀ (by linarith)
  have hd4 : d ^ 2 ≤ (1 + |d|) ^ 4 := by
    have h1 : d ^ 2 = |d| ^ 2 := (sq_abs d).symm
    rw [h1]
    have : |d| ^ 2 ≤ (1 + |d|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
    have h2 : (1 + |d|) ^ 2 ≤ (1 + |d|) ^ 4 :=
      pow_le_pow_right₀ (by linarith [abs_nonneg d]) (by norm_num)
    linarith
  have hd1 : |d| ≤ (1 + |d|) ^ 4 := by
    have : 1 + |d| ≤ (1 + |d|) ^ 4 := le_self_pow₀ (by linarith [abs_nonneg d]) (by norm_num)
    linarith
  have hGb1 : (1 + |d|) ^ 4 ≤ Gb := by
    rw [hGb]; exact le_mul_of_one_le_right (by positivity) hN3
  have hd2G : d ^ 2 ≤ Gb := hd4.trans hGb1
  have hd1G : |d| ≤ Gb := hd1.trans hGb1
  have hD1 : 1 ≤ 1 + q * (ϖ * d) ^ 2 := by nlinarith [mul_nonneg hq (sq_nonneg (ϖ * d))]
  have hDpos : 0 < 1 + q * (ϖ * d) ^ 2 := by linarith
  have e1 : alpha1 M₀ (ϖ * d) u v s / ϖ
      = d * (1 + ϖ * d * delC M₀ u v s) / delLambda M₀ (ϖ * d) u v s := by
    unfold alpha1; field_simp
  have e2 : alpha2 M₀ (ϖ * d) u v s / ϖ ^ 2
      = d ^ 2 * delU M₀ u s / delLambda M₀ (ϖ * d) u v s := by
    unfold alpha2; field_simp
  have e3 : alpha3 M₀ (ϖ * d) u v s / ϖ ^ 2
      = -(s * d ^ 2 * delV M₀ v s) / delLambda M₀ (ϖ * d) u v s := by
    unfold alpha3; field_simp
  rw [e1] at c3'
  have hα2 : |alpha2 M₀ (ϖ * d) u v s / ϖ ^ 2| + |alpha3 M₀ (ϖ * d) u v s / ϖ ^ 2|
      ≤ coeffConst I * Gb := by
    have : (|alpha2 M₀ (ϖ * d) u v s| + |alpha3 M₀ (ϖ * d) u v s|) / ϖ ^ 2
        = |alpha2 M₀ (ϖ * d) u v s / ϖ ^ 2| + |alpha3 M₀ (ϖ * d) u v s / ϖ ^ 2| := by
      rw [abs_div, abs_div, abs_of_pos (by positivity : 0 < ϖ ^ 2), add_div]
    rw [← this]
    calc _ ≤ coeffConst I * (1 + |d|) ^ 4 * (1 + N) ^ 3 := c4'
      _ = coeffConst I * Gb := by rw [hGb]; ring
  rw [e2] at hα2
  rw [e3] at hα2
  have hdiv : ∀ x : ℝ, |x / (1 + q * (ϖ * d) ^ 2)| ≤ |x| := by
    intro x
    rw [abs_div, abs_of_pos hDpos]
    exact div_le_self (abs_nonneg _) hD1
  refine ⟨?_, ?_, ?_⟩
  · calc _ ≤ |d * (1 + ϖ * d * delC M₀ u v s) / delLambda M₀ (ϖ * d) u v s|
          + |d / (1 + q * (ϖ * d) ^ 2)| := abs_sub _ _
      _ ≤ coeffConst I * Gb + κ * Gb := by
          have h1 : |d * (1 + ϖ * d * delC M₀ u v s) / delLambda M₀ (ϖ * d) u v s|
              ≤ coeffConst I * Gb := by
            refine c3'.trans (le_of_eq ?_)
            rw [hGb]; ring
          have h2 : |d / (1 + q * (ϖ * d) ^ 2)| ≤ κ * Gb :=
            (hdiv d).trans (hd1G.trans (le_mul_of_one_le_left (by positivity) hκ1))
          linarith
      _ = _ := by ring
  · have h2 : |σ * d ^ 2 / (1 + q * (ϖ * d) ^ 2)| ≤ κ * Gb := by
      refine (hdiv _).trans ?_
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul hσκ hd2G (sq_nonneg _) (by linarith)
    calc _ ≤ |d ^ 2 * delU M₀ u s / delLambda M₀ (ϖ * d) u v s|
          + |σ * d ^ 2 / (1 + q * (ϖ * d) ^ 2)| := abs_sub _ _
      _ ≤ coeffConst I * Gb + κ * Gb := by
          have := hα2; have := abs_nonneg (-(s * d ^ 2 * delV M₀ v s) / delLambda M₀ (ϖ * d) u v s)
          linarith
      _ = _ := by ring
  · have h2 : |(-(s * σt * d ^ 2)) / (1 + q * (ϖ * d) ^ 2)| ≤ κ * Gb := by
      refine (hdiv _).trans ?_
      rw [abs_neg, abs_of_nonneg (by positivity)]
      exact mul_le_mul hsσκ hd2G (sq_nonneg _) (by linarith)
    calc _ ≤ |-(s * d ^ 2 * delV M₀ v s) / delLambda M₀ (ϖ * d) u v s|
          + |(-(s * σt * d ^ 2)) / (1 + q * (ϖ * d) ^ 2)| := abs_sub _ _
      _ ≤ coeffConst I * Gb + κ * Gb := by
          have := hα2; have := abs_nonneg (d ^ 2 * delU M₀ u s / delLambda M₀ (ϖ * d) u v s)
          linarith
      _ = _ := by ring


private lemma pb83_sigfacts {m n B : ℕ} (w : ℕ → ℝ) {Ω' : Type} [MeasurableSpace Ω']
    (P : Measure Ω') [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (CS g : ℝ)
    (hCo : opNorm F.C.Sout ≤ CS) (hCi : opNorm F.C.Sin ≤ CS)
    (hm : (m : ℝ) ≤ g * B) (hn : (n : ℝ) ≤ g * B) (s : ℝ) (hs0 : 0 < s) :
    0 ≤ sigmaB w F S t s ∧ sigmaB w F S t s ≤ g * CS / s ∧
    0 ≤ sigmaTildeB w F S t s ∧ sigmaTildeB w F S t s ≤ g * CS / s := by
  have hWB : Measurable (WeightedBuf w F S t) := pb82_meas_buf w F S t
  obtain ⟨a1, a2⟩ := pb83_sig P F.C.Sout F.C.psdOut CS hCo B F.hB s hs0 (WeightedBuf w F S t)
    hWB g hm
  obtain ⟨b1, b2⟩ := pb83_sig P F.C.Sin F.C.psdIn CS hCi B F.hB s hs0
    (fun ω => (WeightedBuf w F S t ω)ᵀ) (pb82_hTr.comp hWB) g hn
  have e : expResT w F S t s = Muon.mean P (fun ω => Rs ((WeightedBuf w F S t ω)ᵀ) s) := by
    unfold expResT
    simp only [pb82_Rts_eq]
  refine ⟨a1, a2, ?_, ?_⟩
  · unfold sigmaTildeB; rw [e]; exact b1
  · unfold sigmaTildeB; rw [e]; exact b2


private lemma pb83_meas3 {m n B : ℕ} (w : ℕ → ℝ) {Ω' : Type} [MeasurableSpace Ω']
    (P : Measure Ω') (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (s : ℝ) (hs0 : 0 < s) :
    Measurable (fun ω => delU (delBufAge w F S t j ω) (ageU F S t j ω) s) ∧
    Measurable (fun ω => delV (delBufAge w F S t j ω) (ageV F S t j ω) s) ∧
    Measurable (fun ω => delC (delBufAge w F S t j ω) (ageU F S t j ω)
      (ageV F S t j ω) s) := by
  have hx : Measurable (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) := S.meas _ _
  have hN0 : Measurable (delBufAge w F S t j) :=
    pb82_meas_del w F S t (t + 1 - (j : ℤ)) (slotOne F.hB)
  refine ⟨?_, ?_, ?_⟩
  · have e : (fun ω => delU (delBufAge w F S t j ω) (ageU F S t j ω) s) =
        fun ω => dotProduct ((Real.sqrt (B : ℝ))⁻¹ •
            (CFC.sqrt F.C.Sout *ᵥ (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).1))
          (Rs (delBufAge w F S t j ω) s *ᵥ ((Real.sqrt (B : ℝ))⁻¹ •
            (CFC.sqrt F.C.Sout *ᵥ (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).1))) := by
      funext ω
      unfold delU ageU momU rOut
      rfl
    rw [e]
    exact pb82_meas_quad (CFC.sqrt F.C.Sout) (fun ω => Rs (delBufAge w F S t j ω) s)
      (fun ω => (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).1) _
      ((pb8_Rs_continuous s hs0).measurable.comp hN0) hx.fst
  · have e : (fun ω => delV (delBufAge w F S t j ω) (ageV F S t j ω) s) =
        fun ω => dotProduct ((Real.sqrt (B : ℝ))⁻¹ •
            (CFC.sqrt F.C.Sin *ᵥ (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).2))
          (Rs ((delBufAge w F S t j ω)ᵀ) s *ᵥ ((Real.sqrt (B : ℝ))⁻¹ •
            (CFC.sqrt F.C.Sin *ᵥ (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).2))) := by
      funext ω
      rw [pb82_delV_eq]
      unfold delU ageV momV rIn
      rfl
    rw [e]
    exact pb82_meas_quad (CFC.sqrt F.C.Sin) (fun ω => Rs ((delBufAge w F S t j ω)ᵀ) s)
      (fun ω => (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).2) _
      ((pb8_Rs_continuous s hs0).measurable.comp (pb82_hTr.comp hN0)) hx.snd
  · have hXc : Continuous (fun M : Mat m n => Xs M s) := by
      unfold Xs
      exact (pb8_Rs_continuous s hs0).matrix_mul continuous_id
    exact pb82_meas_bil (CFC.sqrt F.C.Sout) (CFC.sqrt F.C.Sin)
      (fun ω => Xs (delBufAge w F S t j ω) s)
      (fun ω => (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).1)
      (fun ω => (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω).2) _ (hXc.measurable.comp hN0)
      hx.fst hx.snd


private lemma pb83_eucNorm_sq {k : ℕ} (z : Vec k) : eucNorm z ^ 2 = sqNorm z := by
  unfold eucNorm sqNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

private lemma pb83_PMom {m n B : ℕ} {Ω' : Type} [MeasurableSpace Ω']
    (P : Measure Ω') [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (CS g : ℝ) (hg0 : 0 ≤ g)
    (hCo : opNorm F.C.Sout ≤ CS) (hCi : opNorm F.C.Sin ≤ CS)
    (hm : (m : ℝ) ≤ g * B) (hn : (n : ℝ) ≤ g * B) :
    Measurable (ageD F S t j) ∧
    Measurable (fun ω => sqNorm (ageU F S t j ω) + sqNorm (ageV F S t j ω)) ∧
    ∫⁻ ω, ENNReal.ofReal (ageD F S t j ω ^ 2) ∂P ≤ ENNReal.ofReal 1 ∧
    ∫⁻ ω, ENNReal.ofReal (((1 + |ageD F S t j ω|) ^ 4 *
        (1 + (sqNorm (ageU F S t j ω) + sqNorm (ageV F S t j ω))) ^ 3) ^ 4) ∂P ≤
      ENNReal.ofReal (2 ^ 28 * (2 + ((Nat.doubleFactorial 27 : ℕ) : ℝ) ^ 2
          + (2 * CS * g) ^ 28 * ((Nat.doubleFactorial 55 : ℕ) : ℝ))) := by
  have hx : Measurable (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) := S.meas _ _
  have hlaw : P.map (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) = gaussPair m n := by
    unfold gaussPair
    exact S.law (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hNm : Measurable (momN F.C B : Vec m × Vec n → ℝ) := by
    unfold momN eucNorm momU momV
    fun_prop
  have hdm : Measurable (fun x : Vec m × Vec n => resid F.A x) := by unfold resid; fun_prop
  have hNe : ∀ ω, sqNorm (ageU F S t j ω) + sqNorm (ageV F S t j ω)
      = momN F.C B (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω) := by
    intro ω
    unfold momN ageU ageV
    rw [pb83_eucNorm_sq, pb83_eucNorm_sq]
  have hDe : ∀ ω, ageD F S t j ω = resid F.A (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω) :=
    fun ω => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ageD F S t j = fun ω => resid F.A (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω) :=
      funext hDe
    rw [this]; exact hdm.comp hx
  · have : (fun ω => sqNorm (ageU F S t j ω) + sqNorm (ageV F S t j ω)) =
        fun ω => momN F.C B (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω) := funext hNe
    rw [this]; exact hNm.comp hx
  · have hmom := lem_app_de_moments_ii F.A F.hA 1 le_rfl
    have h1 : eLpNorm (fun x => resid F.A x) 2 (gaussPair m n) ≤ ENNReal.ofReal 1 := by
      have h1 := hmom
      simp only [Nat.mul_one, Nat.cast_ofNat, Nat.doubleFactorial, Nat.cast_one, div_one,
        Real.rpow_one] at h1
      simpa using h1
    have := pb82_lintegral_le_of_eLpNorm (gaussPair m n) _ hdm 1 zero_le_one h1
    rw [one_pow] at this
    calc ∫⁻ ω, ENNReal.ofReal (ageD F S t j ω ^ 2) ∂P
        = ∫⁻ ω, ENNReal.ofReal (resid F.A (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω) ^ 2) ∂P :=
          rfl
      _ = ∫⁻ y, ENNReal.ofReal (resid F.A y ^ 2) ∂(P.map (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB))) :=
          (lintegral_map (ENNReal.measurable_ofReal.comp (hdm.pow_const 2)) hx).symm
      _ ≤ ENNReal.ofReal 1 := by rw [hlaw]; exact this
  · have hG := pb83_G4 F.C B g CS ⟨hm, hn⟩ hg0 ⟨hCo, hCi⟩ F.A F.hA
    have hf : Measurable (fun y : Vec m × Vec n => ENNReal.ofReal
        (((1 + |resid F.A y|) ^ 4 * (1 + momN F.C B y) ^ 3) ^ 4)) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    calc ∫⁻ ω, ENNReal.ofReal (((1 + |ageD F S t j ω|) ^ 4 *
        (1 + (sqNorm (ageU F S t j ω) + sqNorm (ageV F S t j ω))) ^ 3) ^ 4) ∂P
        = ∫⁻ ω, ENNReal.ofReal (((1 + |resid F.A (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω)|) ^ 4 *
          (1 + momN F.C B (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω)) ^ 3) ^ 4) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [hNe ω, hDe ω]
      _ = ∫⁻ y, ENNReal.ofReal (((1 + |resid F.A y|) ^ 4 * (1 + momN F.C B y) ^ 3) ^ 4)
            ∂(P.map (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB))) :=
          (lintegral_map hf hx).symm
      _ ≤ _ := by rw [hlaw]; exact hG


private lemma pb83_measZ {Ω' : Type*} [MeasurableSpace Ω'] (d U V C : Ω' → ℝ)
    (hd : Measurable d) (hU : Measurable U) (hV : Measurable V) (hC : Measurable C)
    (ϖ s σ σt q : ℝ) :
    Measurable (fun ω => d ω * (1 + ϖ * d ω * C ω) /
        ((1 + ϖ * d ω * C ω) ^ 2 + s * (ϖ * d ω) ^ 2 * U ω * V ω)
        - d ω / (1 + q * (ϖ * d ω) ^ 2)) ∧
    Measurable (fun ω => d ω ^ 2 * U ω /
        ((1 + ϖ * d ω * C ω) ^ 2 + s * (ϖ * d ω) ^ 2 * U ω * V ω)
        - σ * d ω ^ 2 / (1 + q * (ϖ * d ω) ^ 2)) ∧
    Measurable (fun ω => -(s * d ω ^ 2 * V ω) /
        ((1 + ϖ * d ω * C ω) ^ 2 + s * (ϖ * d ω) ^ 2 * U ω * V ω)
        - (-(s * σt * d ω ^ 2)) / (1 + q * (ϖ * d ω) ^ 2)) := by
  refine ⟨?_, ?_, ?_⟩ <;> fun_prop

private lemma pb83_measPsi {Ω' : Type*} [MeasurableSpace Ω'] (U V C : Ω' → ℝ)
    (hU : Measurable U) (hV : Measurable V) (hC : Measurable C) (s σ σt q : ℝ) :
    Measurable (fun ω => (s * σ * |σt - V ω| + (s * σt + s * |V ω - σt|) * |σ - U ω|
        + (1 + q) * |C ω| + C ω ^ 2) + |U ω - σ| + |V ω - σt|) := by
  fun_prop

private lemma pb83_fourth {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') (Zf Gx : Ω' → ℝ)
    (c Kc K : ℝ) (hGm : Measurable Gx) (hc : 0 ≤ c) (hG0 : ∀ ω, 0 ≤ Gx ω)
    (hpt : ∀ ω, Zf ω ^ 4 ≤ c * Gx ω)
    (hG : ∫⁻ ω, ENNReal.ofReal (Gx ω) ∂P ≤ ENNReal.ofReal Kc) (hK : c * Kc ≤ K) :
    ∫⁻ ω, ENNReal.ofReal (Zf ω ^ 4) ∂P ≤ ENNReal.ofReal K := by
  calc ∫⁻ ω, ENNReal.ofReal (Zf ω ^ 4) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal c * ENNReal.ofReal (Gx ω) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul hc]
        exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal (Gx ω) ∂P :=
        lintegral_const_mul _ (ENNReal.measurable_ofReal.comp hGm)
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal Kc := by gcongr
    _ = ENNReal.ofReal (c * Kc) := (ENNReal.ofReal_mul hc).symm
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal hK


set_option maxHeartbeats 800000 in
private lemma pb83_main {I : Set ℝ} (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w) {Ω' : Type} [MeasurableSpace Ω']
    (P : Measure Ω') [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (CS g C0 κ K C1 : ℝ) (hCS0 : 0 ≤ CS) (hg0 : 0 ≤ g)
    (hCo : opNorm F.C.Sout ≤ CS) (hCi : opNorm F.C.Sin ≤ CS)
    (hm : (m : ℝ) ≤ g * B) (hn : (n : ℝ) ≤ g * B) (hC0 : 0 ≤ C0)
    (hκ1 : 1 ≤ κ) (hκM : ∀ s ∈ I, s ≤ κ) (hκσ : g * CS / sInf I ≤ κ) (hκ2 : g * CS ≤ κ)
    (hC1 : C0 * (3 + 2 * (g * CS) + (g * CS) ^ 2 / sInf I + (κ + 1) * C0) ≤ C1)
    (hK : (coeffConst I + κ) ^ 4 * (2 ^ 28 * (2 + ((Nat.doubleFactorial 27 : ℕ) : ℝ) ^ 2
          + (2 * CS * g) ^ 28 * ((Nat.doubleFactorial 55 : ℕ) : ℝ))) ≤ K)
    (j : ℕ) (hwj : 0 < w j) (s : ℝ) (hs : s ∈ I)
    (H0 : eLpNorm (fun ω => delU (delBufAge w F S t j ω) (ageU F S t j ω) s
            - sigmaB w F S t s) 2 P
          + eLpNorm (fun ω => delV (delBufAge w F S t j ω) (ageV F S t j ω) s
            - sigmaTildeB w F S t s) 2 P
          + eLpNorm (fun ω => delC (delBufAge w F S t j ω) (ageU F S t j ω)
            (ageV F S t j ω) s) 2 P ≤ ENNReal.ofReal (C0 / Real.sqrt (B : ℝ)))
    (ρ R : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hR : R = ρ ^ 2 + (ρ ^ 2 / (K + 1) * K +
        (1 / ((ρ ^ 2)⁻¹) ^ 2 + (C1 / Real.sqrt (B : ℝ)) / (ρ / (4 * κ * (1 + (ρ ^ 2)⁻¹) ^ 5)))
          / (ρ ^ 2 / (K + 1))) / 2) :
    Measurable (fun ω => (delAlpha1 w F S t j s ω - checkAlpha1 w F S t j s ω) / w j) ∧
    Measurable (fun ω => (delAlpha2 w F S t j s ω - checkAlpha2 w F S t j s ω) / w j ^ 2) ∧
    Measurable (fun ω => (delAlpha3 w F S t j s ω - checkAlpha3 w F S t j s ω) / w j ^ 2) ∧
    (∫⁻ ω, ENNReal.ofReal (((delAlpha1 w F S t j s ω - checkAlpha1 w F S t j s ω) / w j) ^ 2) ∂P
        ≤ ENNReal.ofReal R ∧
    ∫⁻ ω, ENNReal.ofReal (((delAlpha2 w F S t j s ω - checkAlpha2 w F S t j s ω) / w j ^ 2) ^ 2) ∂P
        ≤ ENNReal.ofReal R ∧
    ∫⁻ ω, ENNReal.ofReal (((delAlpha3 w F S t j s ω - checkAlpha3 w F S t j s ω) / w j ^ 2) ^ 2) ∂P
        ≤ ENNReal.ofReal R) := by
  have hBpos : 0 < B := F.hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hBpos
  have hsB1 : 1 ≤ Real.sqrt (B : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hB1
  have hsB0 : 0 < Real.sqrt (B : ℝ) := by linarith
  have hs0 : 0 < s := hIpos hs
  have hsm : 0 < sInf I := hIpos (hI.sInf_mem ⟨s, hs⟩)
  have hsle : sInf I ≤ s := csInf_le hI.bddBelow hs
  have hϖ1 : w j ≤ 1 := hw.2.1 j
  have hx : Measurable (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) := S.meas _ _
  have hlaw : P.map (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) = gaussPair m n := by
    unfold gaussPair
    exact S.law (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hN0 : Measurable (delBufAge w F S t j) :=
    pb82_meas_del w F S t (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hWB : Measurable (WeightedBuf w F S t) := pb82_meas_buf w F S t
  obtain ⟨hσ0, hσ1, hσt0, hσt1⟩ := pb83_sigfacts w P F S t CS g hCo hCi hm hn s hs0
  obtain ⟨hUm, hVm, hCm⟩ := pb83_meas3 w P F S t j s hs0
  obtain ⟨hdm, hNm, hD2, hG⟩ := pb83_PMom P F S t j CS g hg0 hCo hCi hm hn
  have hqdef : qB w F S t s = s * sigmaB w F S t s * sigmaTildeB w F S t s := rfl
  have hq0 : 0 ≤ qB w F S t s := by rw [hqdef]; positivity
  have hgCS : 0 ≤ g * CS := mul_nonneg hg0 hCS0
  have hsσ : s * sigmaB w F S t s ≤ g * CS :=
    calc s * sigmaB w F S t s ≤ s * (g * CS / s) := mul_le_mul_of_nonneg_left hσ1 hs0.le
      _ = g * CS := by field_simp
  have hsσt : s * sigmaTildeB w F S t s ≤ g * CS :=
    calc s * sigmaTildeB w F S t s ≤ s * (g * CS / s) := mul_le_mul_of_nonneg_left hσt1 hs0.le
      _ = g * CS := by field_simp
  have hσκ : sigmaB w F S t s ≤ κ :=
    hσ1.trans ((div_le_div_of_nonneg_left hgCS hsm hsle).trans hκσ)
  have hsσtκ : s * sigmaTildeB w F S t s ≤ κ := hsσt.trans hκ2
  have hqle : qB w F S t s ≤ (g * CS) ^ 2 / sInf I := by
    have h1 : qB w F S t s = (s * sigmaB w F S t s) * (s * sigmaTildeB w F S t s) / s := by
      rw [hqdef]; field_simp
    rw [h1]
    have h2 : (s * sigmaB w F S t s) * (s * sigmaTildeB w F S t s) ≤ (g * CS) ^ 2 := by
      rw [sq]
      exact mul_le_mul hsσ hsσt (by positivity) hgCS
    calc _ ≤ (g * CS) ^ 2 / s := div_le_div_of_nonneg_right h2 hs0.le
      _ ≤ (g * CS) ^ 2 / sInf I := div_le_div_of_nonneg_left (by positivity) hsm hsle
  obtain ⟨Uf, hUf⟩ : ∃ Uf : Ω' → ℝ,
      Uf = fun ω => delU (delBufAge w F S t j ω) (ageU F S t j ω) s := ⟨_, rfl⟩
  obtain ⟨Vf, hVf⟩ : ∃ Vf : Ω' → ℝ,
      Vf = fun ω => delV (delBufAge w F S t j ω) (ageV F S t j ω) s := ⟨_, rfl⟩
  obtain ⟨Cf, hCf⟩ : ∃ Cf : Ω' → ℝ, Cf = fun ω => delC (delBufAge w F S t j ω)
      (ageU F S t j ω) (ageV F S t j ω) s := ⟨_, rfl⟩
  have hUm' : Measurable Uf := by rw [hUf]; exact hUm
  have hVm' : Measurable Vf := by rw [hVf]; exact hVm
  have hCm' : Measurable Cf := by rw [hCf]; exact hCm
  have H0' : eLpNorm (fun ω => Uf ω - sigmaB w F S t s) 2 P
      + eLpNorm (fun ω => Vf ω - sigmaTildeB w F S t s) 2 P + eLpNorm Cf 2 P
        ≤ ENNReal.ofReal (C0 / Real.sqrt (B : ℝ)) := by
    subst hUf hVf hCf; exact H0
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = C0 / Real.sqrt (B : ℝ) := ⟨_, rfl⟩
  rw [← hεdef] at H0'
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have hεC : ε ≤ C0 := by rw [hεdef]; exact div_le_self hC0 hsB1
  have eU : eLpNorm (fun ω => Uf ω - sigmaB w F S t s) 2 P ≤ ENNReal.ofReal ε :=
    (le_self_add.trans le_self_add).trans H0'
  have eV : eLpNorm (fun ω => Vf ω - sigmaTildeB w F S t s) 2 P ≤ ENNReal.ofReal ε :=
    (le_add_self.trans le_self_add).trans H0'
  have eC : eLpNorm Cf 2 P ≤ ENNReal.ofReal ε := le_add_self.trans H0'
  have lU : ∫⁻ ω, ENNReal.ofReal (|Uf ω - sigmaB w F S t s| ^ 2) ∂P ≤ ENNReal.ofReal (ε ^ 2) := by
    have := pb82_lintegral_le_of_eLpNorm P (fun ω => Uf ω - sigmaB w F S t s)
      (hUm'.sub measurable_const) ε hε0 eU
    simpa only [sq_abs] using this
  have lV : ∫⁻ ω, ENNReal.ofReal (|Vf ω - sigmaTildeB w F S t s| ^ 2) ∂P
      ≤ ENNReal.ofReal (ε ^ 2) := by
    have := pb82_lintegral_le_of_eLpNorm P (fun ω => Vf ω - sigmaTildeB w F S t s)
      (hVm'.sub measurable_const) ε hε0 eV
    simpa only [sq_abs] using this
  have lC : ∫⁻ ω, ENNReal.ofReal (|Cf ω| ^ 2) ∂P ≤ ENNReal.ofReal (ε ^ 2) := by
    have := pb82_lintegral_le_of_eLpNorm P Cf hCm' ε hε0 eC
    simpa only [sq_abs] using this
  have hPsi := pb83_Psi_int P (fun ω => |Uf ω - sigmaB w F S t s|)
    (fun ω => |Vf ω - sigmaTildeB w F S t s|) (fun ω => |Cf ω|)
    (hUm'.sub measurable_const).abs (hVm'.sub measurable_const).abs hCm'.abs
    (fun ω => abs_nonneg _) (fun ω => abs_nonneg _) (fun ω => abs_nonneg _) ε hε0
    (s * sigmaB w F S t s + 1) (s * sigmaTildeB w F S t s + 1) (1 + qB w F S t s) s
    (by positivity) (by positivity) (by linarith) hs0.le lU lV lC
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : Ω' → ℝ, Ψ = fun ω =>
      (s * sigmaB w F S t s * |sigmaTildeB w F S t s - Vf ω|
        + (s * sigmaTildeB w F S t s + s * |Vf ω - sigmaTildeB w F S t s|)
          * |sigmaB w F S t s - Uf ω|
        + (1 + qB w F S t s) * |Cf ω| + Cf ω ^ 2) + |Uf ω - sigmaB w F S t s|
        + |Vf ω - sigmaTildeB w F S t s| := ⟨_, rfl⟩
  have hΨm : Measurable Ψ := by
    rw [hΨdef]; exact pb83_measPsi Uf Vf Cf hUm' hVm' hCm' _ _ _ _
  have hΨ0 : ∀ ω, 0 ≤ Ψ ω := by
    intro ω; rw [hΨdef]; have := hq0
    have h1 : 0 ≤ sigmaB w F S t s := hσ0
    have h2 : 0 ≤ sigmaTildeB w F S t s := hσt0
    positivity
  have hΨ1 : ∫⁻ ω, ENNReal.ofReal (Ψ ω) ∂P ≤ ENNReal.ofReal (C1 / Real.sqrt (B : ℝ)) := by
    have e : ∀ ω, Ψ ω = (s * sigmaB w F S t s + 1) * |Vf ω - sigmaTildeB w F S t s|
        + (s * sigmaTildeB w F S t s + 1) * |Uf ω - sigmaB w F S t s|
        + s * (|Vf ω - sigmaTildeB w F S t s| * |Uf ω - sigmaB w F S t s|)
        + (1 + qB w F S t s) * |Cf ω| + |Cf ω| ^ 2 := by
      intro ω
      simp only [hΨdef]
      rw [abs_sub_comm (sigmaTildeB w F S t s) (Vf ω),
        abs_sub_comm (sigmaB w F S t s) (Uf ω), sq_abs]
      ring
    simp_rw [e]
    refine hPsi.trans (ENNReal.ofReal_le_ofReal ?_)
    have hA : (s * sigmaB w F S t s + 1) + (s * sigmaTildeB w F S t s + 1) + (1 + qB w F S t s)
        ≤ 3 + 2 * (g * CS) + (g * CS) ^ 2 / sInf I := by linarith
    have hsκ : s + 1 ≤ κ + 1 := by linarith [hκM s hs]
    have h1 : ((s * sigmaB w F S t s + 1) + (s * sigmaTildeB w F S t s + 1)
        + (1 + qB w F S t s)) * ε ≤ (3 + 2 * (g * CS) + (g * CS) ^ 2 / sInf I) * ε :=
      mul_le_mul_of_nonneg_right hA hε0
    have h2 : (s + 1) * ε ^ 2 ≤ ((κ + 1) * C0) * ε := by
      rw [sq]
      calc (s + 1) * (ε * ε) = (s + 1) * ε * ε := by ring
        _ ≤ (κ + 1) * C0 * ε := by
          refine mul_le_mul (mul_le_mul hsκ hεC hε0 (by linarith [hκM s hs])) le_rfl hε0
            (by positivity)
    have h3 : C0 * (3 + 2 * (g * CS) + (g * CS) ^ 2 / sInf I + (κ + 1) * C0) / Real.sqrt B
        ≤ C1 / Real.sqrt B := div_le_div_of_nonneg_right hC1 hsB0.le
    calc _ ≤ (3 + 2 * (g * CS) + (g * CS) ^ 2 / sInf I) * ε + ((κ + 1) * C0) * ε := by linarith
      _ = C0 * (3 + 2 * (g * CS) + (g * CS) ^ 2 / sInf I + (κ + 1) * C0) / Real.sqrt B := by
          rw [hεdef]; ring
      _ ≤ _ := h3
  have hϖne : w j ≠ 0 := hwj.ne'
  have hLpos : ∀ ω, 0 < delLambda (delBufAge w F S t j ω) (w j * ageD F S t j ω)
      (ageU F S t j ω) (ageV F S t j ω) s := fun ω =>
    (lem_app_de_deletion (delBufAge w F S t j ω) (w j * ageD F S t j ω) (ageU F S t j ω)
      (ageV F S t j ω) _ s rfl hs0).1
  have hforms := fun ω => pb83_forms (delBufAge w F S t j ω) (ageU F S t j ω) (ageV F S t j ω)
    (ageD F S t j ω) (w j) s (qB w F S t s) (sigmaB w F S t s) (sigmaTildeB w F S t s) hϖne
    (hLpos ω) hq0
  have hsize := fun ω => pb83_size hI hIpos (delBufAge w F S t j ω) (ageU F S t j ω)
    (ageV F S t j ω) (ageD F S t j ω) (w j) s (qB w F S t s) (sigmaB w F S t s)
    (sigmaTildeB w F S t s) κ hwj hϖ1 hs hq0 hσ0 hσt0 hκ1 hσκ hsσtκ
  have hK0 : 0 ≤ K := le_trans (by positivity) hK
  have hC10 : 0 ≤ C1 := le_trans (by positivity) hC1
  have hm1 : 1 ≤ (ρ ^ 2)⁻¹ := by
    rw [one_le_inv₀ (by positivity)]
    nlinarith
  have hGm : Measurable (fun ω => ((1 + |ageD F S t j ω|) ^ 4 *
      (1 + (sqNorm (ageU F S t j ω) + sqNorm (ageV F S t j ω))) ^ 3) ^ 4) := by
    have := hdm; have := hNm
    fun_prop
  have hGnn : ∀ ω, 0 ≤ ((1 + |ageD F S t j ω|) ^ 4 *
      (1 + (sqNorm (ageU F S t j ω) + sqNorm (ageV F S t j ω))) ^ 3) ^ 4 := fun ω => by positivity
  -- the three normalised differences and their closed forms
  have hZ1 : ∀ ω, (delAlpha1 w F S t j s ω - checkAlpha1 w F S t j s ω) / w j =
      ageD F S t j ω * (1 + w j * ageD F S t j ω * Cf ω) /
        ((1 + w j * ageD F S t j ω * Cf ω) ^ 2 + s * (w j * ageD F S t j ω) ^ 2 * Uf ω * Vf ω)
      - ageD F S t j ω / (1 + qB w F S t s * (w j * ageD F S t j ω) ^ 2) := by
    intro ω
    have := (hforms ω).1
    simp only [hUf, hVf, hCf]
    exact this
  have hZ2 : ∀ ω, (delAlpha2 w F S t j s ω - checkAlpha2 w F S t j s ω) / w j ^ 2 =
      ageD F S t j ω ^ 2 * Uf ω /
        ((1 + w j * ageD F S t j ω * Cf ω) ^ 2 + s * (w j * ageD F S t j ω) ^ 2 * Uf ω * Vf ω)
      - sigmaB w F S t s * ageD F S t j ω ^ 2
        / (1 + qB w F S t s * (w j * ageD F S t j ω) ^ 2) := by
    intro ω
    have := (hforms ω).2.1
    simp only [hUf, hVf, hCf]
    exact this
  have hZ3 : ∀ ω, (delAlpha3 w F S t j s ω - checkAlpha3 w F S t j s ω) / w j ^ 2 =
      -(s * ageD F S t j ω ^ 2 * Vf ω) /
        ((1 + w j * ageD F S t j ω * Cf ω) ^ 2 + s * (w j * ageD F S t j ω) ^ 2 * Uf ω * Vf ω)
      - (-(s * sigmaTildeB w F S t s * ageD F S t j ω ^ 2))
        / (1 + qB w F S t s * (w j * ageD F S t j ω) ^ 2) := by
    intro ω
    have := (hforms ω).2.2
    simp only [hUf, hVf, hCf]
    exact this
  obtain ⟨mZ1, mZ2, mZ3⟩ := pb83_measZ (ageD F S t j) Uf Vf Cf hdm hUm' hVm' hCm' (w j) s
    (sigmaB w F S t s) (sigmaTildeB w F S t s) (qB w F S t s)
  have mZ1' : Measurable (fun ω => (delAlpha1 w F S t j s ω - checkAlpha1 w F S t j s ω) / w j) := by
    have : (fun ω => (delAlpha1 w F S t j s ω - checkAlpha1 w F S t j s ω) / w j) = _ := funext hZ1
    rw [this]; exact mZ1
  have mZ2' : Measurable (fun ω => (delAlpha2 w F S t j s ω - checkAlpha2 w F S t j s ω) / w j ^ 2) := by
    have : (fun ω => (delAlpha2 w F S t j s ω - checkAlpha2 w F S t j s ω) / w j ^ 2) = _ := funext hZ2
    rw [this]; exact mZ2
  have mZ3' : Measurable (fun ω => (delAlpha3 w F S t j s ω - checkAlpha3 w F S t j s ω) / w j ^ 2) := by
    have : (fun ω => (delAlpha3 w F S t j s ω - checkAlpha3 w F S t j s ω) / w j ^ 2) = _ := funext hZ3
    rw [this]; exact mZ3
  have hgood : ∀ ω, |ageD F S t j ω| ≤ (ρ ^ 2)⁻¹ →
      Ψ ω ≤ ρ / (4 * κ * (1 + (ρ ^ 2)⁻¹) ^ 5) →
      |(delAlpha1 w F S t j s ω - checkAlpha1 w F S t j s ω) / w j| ≤ ρ ∧
      |(delAlpha2 w F S t j s ω - checkAlpha2 w F S t j s ω) / w j ^ 2| ≤ ρ ∧
      |(delAlpha3 w F S t j s ω - checkAlpha3 w F S t j s ω) / w j ^ 2| ≤ ρ := by
    intro ω hd hΨτ
    have hg := pb83_good (w j) (ageD F S t j ω) s (sigmaB w F S t s) (sigmaTildeB w F S t s)
      (delU (delBufAge w F S t j ω) (ageU F S t j ω) s)
      (delV (delBufAge w F S t j ω) (ageV F S t j ω) s)
      (delC (delBufAge w F S t j ω) (ageU F S t j ω) (ageV F S t j ω) s)
      ((ρ ^ 2)⁻¹) κ ρ (Ψ ω)
      (delLambda (delBufAge w F S t j ω) (w j * ageD F S t j ω) (ageU F S t j ω)
        (ageV F S t j ω) s)
      (1 + qB w F S t s * (w j * ageD F S t j ω) ^ 2) (qB w F S t s) hwj.le hϖ1 hm1 hd hs0 hσ0
      hσt0 rfl hκ1 hσκ hsσtκ (by linarith [hκM s hs]) hρ0 hρ1 rfl rfl
      (by simp only [hΨdef, hUf, hVf, hCf]) hΨτ
    obtain ⟨-, b1, b2, b3⟩ := hg
    have e1 := hZ1 ω
    have e2 := hZ2 ω
    have e3 := hZ3 ω
    simp only [hUf, hVf, hCf] at e1 e2 e3
    rw [e1, e2, e3]
    exact ⟨b1, b2, b3⟩
  have hbd : ∀ ω,
      |(delAlpha1 w F S t j s ω - checkAlpha1 w F S t j s ω) / w j| ≤ (coeffConst I + κ) *
        ((1 + |ageD F S t j ω|) ^ 4 *
          (1 + (sqNorm (ageU F S t j ω) + sqNorm (ageV F S t j ω))) ^ 3) ∧
      |(delAlpha2 w F S t j s ω - checkAlpha2 w F S t j s ω) / w j ^ 2| ≤ (coeffConst I + κ) *
        ((1 + |ageD F S t j ω|) ^ 4 *
          (1 + (sqNorm (ageU F S t j ω) + sqNorm (ageV F S t j ω))) ^ 3) ∧
      |(delAlpha3 w F S t j s ω - checkAlpha3 w F S t j s ω) / w j ^ 2| ≤ (coeffConst I + κ) *
        ((1 + |ageD F S t j ω|) ^ 4 *
          (1 + (sqNorm (ageU F S t j ω) + sqNorm (ageV F S t j ω))) ^ 3) := by
    intro ω
    have e1 := hZ1 ω
    have e2 := hZ2 ω
    have e3 := hZ3 ω
    simp only [hUf, hVf, hCf] at e1 e2 e3
    rw [e1, e2, e3]
    exact hsize ω
  have hCG : 0 ≤ coeffConst I + κ := by
    have : 0 ≤ coeffConst I := by unfold coeffConst; positivity
    linarith
  have hfourth : ∀ (Zf : Ω' → ℝ),
      (∀ ω, |Zf ω| ≤ (coeffConst I + κ) * ((1 + |ageD F S t j ω|) ^ 4 *
          (1 + (sqNorm (ageU F S t j ω) + sqNorm (ageV F S t j ω))) ^ 3)) →
      ∫⁻ ω, ENNReal.ofReal (Zf ω ^ 4) ∂P ≤ ENNReal.ofReal K := by
    intro Zf hZ
    refine pb83_fourth P Zf _ ((coeffConst I + κ) ^ 4) _ K hGm (by positivity) hGnn
      (fun ω => ?_) hG hK
    calc Zf ω ^ 4 = |Zf ω| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      _ ≤ ((coeffConst I + κ) * ((1 + |ageD F S t j ω|) ^ 4 *
          (1 + (sqNorm (ageU F S t j ω) + sqNorm (ageV F S t j ω))) ^ 3)) ^ 4 :=
          pow_le_pow_left₀ (abs_nonneg _) (hZ ω) 4
      _ = (coeffConst I + κ) ^ 4 * (((1 + |ageD F S t j ω|) ^ 4 *
          (1 + (sqNorm (ageU F S t j ω) + sqNorm (ageV F S t j ω))) ^ 3) ^ 4) :=
          mul_pow _ _ _
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hmpos : 0 < (ρ ^ 2)⁻¹ := by positivity
  have hτpos : 0 < ρ / (4 * κ * (1 + (ρ ^ 2)⁻¹) ^ 5) := by
    have : 0 < κ := by linarith
    positivity
  have hlam : 0 < ρ ^ 2 / (K + 1) := by positivity
  have hfin : ∀ (Zf : Ω' → ℝ), Measurable Zf →
      (∀ ω, |ageD F S t j ω| ≤ (ρ ^ 2)⁻¹ → Ψ ω ≤ ρ / (4 * κ * (1 + (ρ ^ 2)⁻¹) ^ 5) →
        |Zf ω| ≤ ρ) →
      ∫⁻ ω, ENNReal.ofReal (Zf ω ^ 4) ∂P ≤ ENNReal.ofReal K →
      ∫⁻ ω, ENNReal.ofReal (Zf ω ^ 2) ∂P ≤ ENNReal.ofReal R := by
    intro Zf hZm hgd h4
    have := pb83_L2 P Zf (ageD F S t j) Ψ hZm hdm hΨm hΨ0 ((ρ ^ 2)⁻¹) ρ
      (ρ / (4 * κ * (1 + (ρ ^ 2)⁻¹) ^ 5)) (ρ ^ 2 / (K + 1)) K 1 (C1 / Real.sqrt (B : ℝ)) hmpos
      hρ0.le hτpos hlam hgd hD2 hΨ1 h4 hK0 zero_le_one (by positivity)
    rw [hR]
    exact this
  refine ⟨mZ1', mZ2', mZ3', hfin _ mZ1' (fun ω h1 h2 => (hgood ω h1 h2).1)
    (hfourth _ (fun ω => (hbd ω).1)), hfin _ mZ2' (fun ω h1 h2 => (hgood ω h1 h2).2.1)
    (hfourth _ (fun ω => (hbd ω).2.1)), hfin _ mZ3' (fun ω h1 h2 => (hgood ω h1 h2).2.2)
    (hfourth _ (fun ω => (hbd ω).2.2))⟩


private lemma pb83_conc {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] (Zf : Ω' → ℝ) (hZm : Measurable Zf) (K C1 κ : ℝ) (B : ℕ)
    (e : ℕ → ℝ) (hK0 : 0 ≤ K) (hC10 : 0 ≤ C1) (hκ1 : 1 ≤ κ)
    (hpick : ∀ x : ℝ,
      (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → x ≤ Real.sqrt (ρ ^ 2 + (ρ ^ 2 / (K + 1) * K +
        (1 / ((ρ ^ 2)⁻¹) ^ 2 + (C1 / Real.sqrt (B : ℝ)) / (ρ / (4 * κ * (1 + (ρ ^ 2)⁻¹) ^ 5)))
          / (ρ ^ 2 / (K + 1))) / 2)) → x ≤ e B)
    (hint : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∫⁻ ω, ENNReal.ofReal (Zf ω ^ 2) ∂P ≤
      ENNReal.ofReal (ρ ^ 2 + (ρ ^ 2 / (K + 1) * K +
        (1 / ((ρ ^ 2)⁻¹) ^ 2 + (C1 / Real.sqrt (B : ℝ)) / (ρ / (4 * κ * (1 + (ρ ^ 2)⁻¹) ^ 5)))
          / (ρ ^ 2 / (K + 1))) / 2)) :
    eLpNorm Zf 2 P ≤ ENNReal.ofReal (e B) := by
  have hκ0 : 0 < κ := by linarith
  have hR0 : ∀ ρ : ℝ, 0 < ρ → 0 ≤ ρ ^ 2 + (ρ ^ 2 / (K + 1) * K +
        (1 / ((ρ ^ 2)⁻¹) ^ 2 + (C1 / Real.sqrt (B : ℝ)) / (ρ / (4 * κ * (1 + (ρ ^ 2)⁻¹) ^ 5)))
          / (ρ ^ 2 / (K + 1))) / 2 := fun ρ hρ => by positivity
  have hb : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → eLpNorm Zf 2 P ≤ ENNReal.ofReal (Real.sqrt (ρ ^ 2 +
      (ρ ^ 2 / (K + 1) * K +
        (1 / ((ρ ^ 2)⁻¹) ^ 2 + (C1 / Real.sqrt (B : ℝ)) / (ρ / (4 * κ * (1 + (ρ ^ 2)⁻¹) ^ 5)))
          / (ρ ^ 2 / (K + 1))) / 2)) := by
    intro ρ hρ0 hρ1
    refine pb82_eLpNorm_le P Zf hZm _ (Real.sqrt_nonneg _) ?_
    rw [Real.sq_sqrt (hR0 ρ hρ0)]
    exact hint ρ hρ0 hρ1
  have hfin : eLpNorm Zf 2 P ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb 1 one_pos le_rfl)
  have hx : (eLpNorm Zf 2 P).toReal ≤ e B := by
    refine hpick _ fun ρ hρ0 hρ1 => ?_
    exact ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) (hb ρ hρ0 hρ1)
  calc eLpNorm Zf 2 P = ENNReal.ofReal (eLpNorm Zf 2 P).toReal := (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal (e B) := ENNReal.ofReal_le_ofReal hx

end Replace

/-! ## Replacement of the deletion coefficients (`lem:app-de-replace`) -/

/-- `lem:app-de-replace`, snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.1326–1341):
\begin{lemma}[Replacement of the deletion coefficients]\label{lem:app-de-replace}
For $x\ge0$ put $f_x(d)\defeq\frac{d}{1+xd^2}$ and $\psi_x(d)\defeq\frac{d^2}{1+xd^2}$,
and for a sample of age $j$ and $s\in I$ define the target coefficients
\begin{equation}\label{eqn:app-de-targets}
\check\alpha_{1,j}\defeq\emaw j\,f_{\emaw j^2q_B}(d_j),\qquad
\check\alpha_{2,j}\defeq\emaw j^2\,\sigma_B\,\psi_{\emaw j^2q_B}(d_j),\qquad
\check\alpha_{3,j}\defeq-s\,\emaw j^2\,\tilde\sigma_B\,\psi_{\emaw j^2q_B}(d_j).
\end{equation}
There is a sequence $e_B\to0$, depending only on $(I,C_\Sigma,\gamma_\star)$,
the weights and the dimension, such that for every age $j$ and every $s\in I$
\begin{equation}\label{eqn:app-de-replace}
\norm{\alpha_{1,j}-\check\alpha_{1,j}}_2\le\emaw j\,e_B,\qquad
\norm{\alpha_{2,j}-\check\alpha_{2,j}}_2\le\emaw j^2\,e_B,\qquad
\norm{\alpha_{3,j}-\check\alpha_{3,j}}_2\le\emaw j^2\,e_B .
\end{equation}
\end{lemma}
-/
theorem lem_app_de_replace (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    (CSig γ : ℝ) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ (m n B : ℕ) (w : ℕ → ℝ), WeightClass w →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
        (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ),
        opNorm F.C.Sout ≤ CSig → opNorm F.C.Sin ≤ CSig →
        (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
        ∀ (j : ℕ), ∀ s ∈ I,
          eLpNorm (fun ω => delAlpha1 w F S t j s ω - checkAlpha1 w F S t j s ω) 2 P
              ≤ ENNReal.ofReal (w j * e B) ∧
          eLpNorm (fun ω => delAlpha2 w F S t j s ω - checkAlpha2 w F S t j s ω) 2 P
              ≤ ENNReal.ofReal (w j ^ 2 * e B) ∧
          eLpNorm (fun ω => delAlpha3 w F S t j s ω - checkAlpha3 w F S t j s ω) 2 P
              ≤ ENNReal.ofReal (w j ^ 2 * e B) := by
  obtain ⟨C0, hC00, H0⟩ := lem_app_de_scalars I hI hIpos CSig γ
  have hsm0 : 0 ≤ sInf I := Real.sInf_nonneg fun x hx => (hIpos hx).le
  obtain ⟨CS, hCSdef⟩ : ∃ CS : ℝ, CS = max CSig 0 := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = max γ 0 := ⟨_, rfl⟩
  have hCS0 : 0 ≤ CS := by rw [hCSdef]; exact le_max_right _ _
  have hg0 : 0 ≤ g := by rw [hgdef]; exact le_max_right _ _
  have hgCS : 0 ≤ g * CS := mul_nonneg hg0 hCS0
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = max 1 (max (sSup I) (max (g * CS / sInf I) (g * CS))) :=
    ⟨_, rfl⟩
  have hκ1 : 1 ≤ κ := by rw [hκdef]; exact le_max_left _ _
  have hκM : ∀ s ∈ I, s ≤ κ := fun s hs => by
    rw [hκdef]
    exact (le_csSup hI.bddAbove hs).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hκσ : g * CS / sInf I ≤ κ := by
    rw [hκdef]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hκ2 : g * CS ≤ κ := by
    rw [hκdef]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨C1, hC1def⟩ : ∃ C1 : ℝ,
      C1 = C0 * (3 + 2 * (g * CS) + (g * CS) ^ 2 / sInf I + (κ + 1) * C0) := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (coeffConst I + κ) ^ 4 * (2 ^ 28 * (2 +
      ((Nat.doubleFactorial 27 : ℕ) : ℝ) ^ 2
      + (2 * CS * g) ^ 28 * ((Nat.doubleFactorial 55 : ℕ) : ℝ))) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hκ0 : 0 < κ := by linarith
  have hC10 : 0 ≤ C1 := by rw [hC1def]; positivity
  obtain ⟨e, he, hpick⟩ := pb83_exists_e K C1 κ hK0 hC10 hκ1
  refine ⟨e, he, ?_⟩
  intro m n B w hw Ω' _ P _ F S t hCo hCi hm hn j s hs
  have hBn : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hm' : (m : ℝ) ≤ g * B :=
    hm.trans (mul_le_mul_of_nonneg_right (by rw [hgdef]; exact le_max_left _ _) hBn)
  have hn' : (n : ℝ) ≤ g * B :=
    hn.trans (mul_le_mul_of_nonneg_right (by rw [hgdef]; exact le_max_left _ _) hBn)
  have hCo' : opNorm F.C.Sout ≤ CS := hCo.trans (by rw [hCSdef]; exact le_max_left _ _)
  have hCi' : opNorm F.C.Sin ≤ CS := hCi.trans (by rw [hCSdef]; exact le_max_left _ _)
  have hH0 := H0 m n B w hw Ω' P F S t hCo hCi hm hn j s hs
  have hs0 : 0 < s := hIpos hs
  have hw0 : 0 ≤ w j := hw.1.1 j
  by_cases hwj : w j = 0
  · have z1 : (fun ω => delAlpha1 w F S t j s ω - checkAlpha1 w F S t j s ω) = 0 := by
      funext ω
      simp [delAlpha1, checkAlpha1, alpha1, hwj]
    have z2 : (fun ω => delAlpha2 w F S t j s ω - checkAlpha2 w F S t j s ω) = 0 := by
      funext ω
      simp [delAlpha2, checkAlpha2, alpha2, hwj]
    have z3 : (fun ω => delAlpha3 w F S t j s ω - checkAlpha3 w F S t j s ω) = 0 := by
      funext ω
      simp [delAlpha3, checkAlpha3, alpha3, hwj]
    rw [z1, z2, z3, eLpNorm_zero]
    exact ⟨zero_le, zero_le, zero_le⟩
  · have hwpos : 0 < w j := lt_of_le_of_ne hw0 (Ne.symm hwj)
    have hmain := fun ρ R hρ0 hρ1 hR => pb83_main hI hIpos w hw P F S t CS g C0 κ K C1 hCS0 hg0
      hCo' hCi' hm' hn' hC00 hκ1 hκM hκσ hκ2 (le_of_eq hC1def.symm)
      (le_of_eq hKdef.symm) j hwpos s hs hH0 ρ R hρ0 hρ1 hR
    have hconc : ∀ (Zf : Ω' → ℝ), Measurable Zf →
        (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∫⁻ ω, ENNReal.ofReal (Zf ω ^ 2) ∂P ≤
          ENNReal.ofReal (ρ ^ 2 + (ρ ^ 2 / (K + 1) * K +
            (1 / ((ρ ^ 2)⁻¹) ^ 2 + (C1 / Real.sqrt (B : ℝ)) /
              (ρ / (4 * κ * (1 + (ρ ^ 2)⁻¹) ^ 5))) / (ρ ^ 2 / (K + 1))) / 2)) →
        eLpNorm Zf 2 P ≤ ENNReal.ofReal (e B) := fun Zf hZm hint =>
      pb83_conc P Zf hZm K C1 κ B e hK0 hC10 hκ1 (hpick B) hint
    obtain ⟨mZ1, mZ2, mZ3, -⟩ := hmain 1 _ one_pos le_rfl rfl
    have hscale : ∀ (k : ℕ) (Df Zf : Ω' → ℝ), (∀ ω, Df ω = w j ^ k * Zf ω) →
        eLpNorm Zf 2 P ≤ ENNReal.ofReal (e B) →
        eLpNorm Df 2 P ≤ ENNReal.ofReal (w j ^ k * e B) := by
      intro k Df Zf hD hZ
      have : Df = (w j ^ k) • Zf := funext fun ω => by rw [hD ω]; rfl
      rw [this, eLpNorm_const_smul, ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul' ?_ hZ
      rw [Real.enorm_eq_ofReal (by positivity)]
    refine ⟨?_, ?_, ?_⟩
    · have := hscale 1 (fun ω => delAlpha1 w F S t j s ω - checkAlpha1 w F S t j s ω)
        (fun ω => (delAlpha1 w F S t j s ω - checkAlpha1 w F S t j s ω) / w j)
        (fun ω => by field_simp) (hconc _ mZ1 fun ρ hρ0 hρ1 =>
          (hmain ρ _ hρ0 hρ1 rfl).2.2.2.1)
      simpa using this
    · exact hscale 2 (fun ω => delAlpha2 w F S t j s ω - checkAlpha2 w F S t j s ω)
        (fun ω => (delAlpha2 w F S t j s ω - checkAlpha2 w F S t j s ω) / w j ^ 2)
        (fun ω => by field_simp) (hconc _ mZ2 fun ρ hρ0 hρ1 =>
          (hmain ρ _ hρ0 hρ1 rfl).2.2.2.2.1)
    · exact hscale 2 (fun ω => delAlpha3 w F S t j s ω - checkAlpha3 w F S t j s ω)
        (fun ω => (delAlpha3 w F S t j s ω - checkAlpha3 w F S t j s ω) / w j ^ 2)
        (fun ω => by field_simp) (hconc _ mZ3 fun ρ hρ0 hρ1 =>
          (hmain ρ _ hρ0 hρ1 rfl).2.2.2.2.2)

end Muon.DetEquiv

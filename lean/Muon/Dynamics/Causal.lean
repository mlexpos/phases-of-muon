import Muon.Dynamics.FiniteMean
import Muon.Dynamics.Chains
import Muon.Dynamics.Filter
import Muon.DetEquiv.Resolvent
import Muon.DetEquiv.Concentration
import Muon.External.Certificates

/-!
# Appendix E, work package L-E.8: causal expansion of the frozen chain

Snapshot `cr-2026-10-23`. Source: `sections/05-dynamics/section.tex`, subsection "Causal response
of the frozen chain" (ll. 993–1466): `lem:app-dyn-tangent` (ll. 1027–1036), `lem:app-dyn-derivative`
(ll. 1078–1099), `lem:app-dyn-coefficients` (ll. 1136–1151), `lem:app-dyn-raw` (ll. 1202–1210),
`prop:app-dyn-reduction` (ll. 1237–1256), `lem:app-dyn-minor` (ll. 1317–1326),
`prop:app-dyn-scalar` (ll. 1353–1362), `lem:app-dyn-ridge` (ll. 1394–1400),
`prop:app-dyn-stationary-tangent` (ll. 1415–1425). Card: `sections/05-dynamics/CARD.md`
§2, §3, §5 (L-E.8).
Interface draft: statements are `sorry`ed; proofs are later work.

Representation choices:
* Norms are the project's named norms: `Muon.opNorm` (operator), `Muon.fro` (Frobenius), `Muon.nuc`
  (nuclear). Frobenius pairings are `frobIP X Y = Tr(X Yᵀ)`; the Σ-pairing of `Muon.Setup.pairSigma`
  is reused for `⟨Σ_out D Σ_in, ·⟩`.
* Sampling model. Batches are read from `Muon.Dynamics.ChainSamples` (whitened pairs
  `act s a` of the batch whose gradient is `G°_s`; auxiliary batches `aux t j a`).
  Stationary chains are `Muon.Dynamics.def_app_dyn_chains` (index `r` of `N_r` is array
  index `r + 1`), so `N_r` is `stat (r + 1)`, and `V_r` is `statV (r + 1)`.
* Pathwise causal chain (`causalState`): for fixed batches `G : ℤ → Batch`, the chain of the
  source with state `Δ^ε_r` and buffer `M^ε_{r-1}`; `causalState … ε r = (Δ^ε_r, M^ε_{r-1})`.
  The source's "defined for small ε" is replaced by totality: the Lean maps are total, and the
  derivatives are two-sided at `ε = 0` under `0 < R(D)`.
* Derivatives are entrywise `HasDerivAt` statements (`Matrix` carries no normed-space instance);
  `causalDot` is the entrywise derivative used in the stationary tangent.
* Coefficient derivatives `∂_d α_i` are `deriv` of `α_i(M₀, ϖ·y, u, v, s)` in `y` at `d`; part (i)
  of `lem:app-dyn-derivative` proves they are the displayed rational functions.
* Expectations of random quantities carry `Integrable` conjuncts (no junk `∫`).
* `Muon.Dynamics.Test`-type data are plain hypotheses through `IsTest`.
* Constants: `∃ C` comes after the fixed parameters (`p`, `s₀`, `c_Π`, …) and before the model
  (`m n B`, covariances, samples, states), as the source states the dependence.
-/

-- Docstrings quote the frozen LaTeX verbatim, which has lines over 100 characters.
set_option linter.style.longLine false

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open Muon Muon.Setup Muon.DetEquiv

noncomputable section

namespace Muon.Dynamics

/-! ## Helpers: Frobenius pairing, tests, sample vectors -/

/-- Frobenius pairing `⟨X, Y⟩_F = Tr(X Yᵀ)` on real matrices (the paper's `⟨·,·⟩` in
`eqn:app-dyn-F`, `lem:app-dyn-raw`). -/
def frobIP {m n : ℕ} (X Y : Mat m n) : ℝ := (X * Yᵀ).trace

/-- A test `Π`: a deterministic matrix with `‖Π‖_F ≤ c_Π` and `‖Π‖ ≤ π_Π ≤ c_Π`
(`section.tex`, the paragraph before `eqn:app-dyn-epsPi`, ll. 1063–1066). -/
def IsTest {m n : ℕ} (cP piT : ℝ) (Pt : Mat m n) : Prop :=
  fro Pt ≤ cP ∧ opNorm Pt ≤ piT ∧ piT ≤ cP

/-- Sample vector `u = Σ_out^{1/2} z / √B` of `lem:app-dyn-coefficients` (ll. 1136–1151). -/
def sampU {m n : ℕ} (C : Covariances m n) (B : ℕ) (x : Vec m × Vec n) : Vec m :=
  (Real.sqrt (B : ℝ))⁻¹ • (rOut C *ᵥ x.1)

/-- Sample vector `v = Σ_in^{1/2} w / √B` of `lem:app-dyn-coefficients` (ll. 1136–1151). -/
def sampV {m n : ℕ} (C : Covariances m n) (B : ℕ) (x : Vec m × Vec n) : Vec n :=
  (Real.sqrt (B : ℝ))⁻¹ • (rIn C *ᵥ x.2)

/-- Minor trace `σ = (1/B) Tr(Σ_out R_s(M₀))` (`eqn:app-dyn-minor-traces`, ll. 1127–1134). -/
def sigmaS {m n : ℕ} (C : Covariances m n) (B : ℕ) (M : Mat m n) (s : ℝ) : ℝ :=
  (B : ℝ)⁻¹ * (C.Sout * Rs M s).trace

/-- Minor trace `σ̃ = (1/B) Tr(Σ_in R̃_s(M₀))` (`eqn:app-dyn-minor-traces`, ll. 1127–1134). -/
def sigmaT {m n : ℕ} (C : Covariances m n) (B : ℕ) (M : Mat m n) (s : ℝ) : ℝ :=
  (B : ℝ)⁻¹ * (C.Sin * Rts M s).trace

/-- `x = ϖ² s σ σ̃` (`eqn:app-dyn-minor-traces`, ll. 1127–1134). -/
def xMinor {m n : ℕ} (C : Covariances m n) (B : ℕ) (M : Mat m n) (ϖ s : ℝ) : ℝ :=
  ϖ ^ 2 * s * sigmaS C B M s * sigmaT C B M s

/-- `∂_d α₁` with `𝗁 = ϖ d` and `M₀, u, v` fixed (`lem:app-dyn-derivative`). -/
def dAlpha1 {m n : ℕ} (M0 : Mat m n) (ϖ s : ℝ) (u : Vec m) (v : Vec n) (d : ℝ) : ℝ :=
  deriv (fun y : ℝ => alpha1 M0 (ϖ * y) u v s) d

/-- `∂_d α₂` with `𝗁 = ϖ d` and `M₀, u, v` fixed (`lem:app-dyn-derivative`). -/
def dAlpha2 {m n : ℕ} (M0 : Mat m n) (ϖ s : ℝ) (u : Vec m) (v : Vec n) (d : ℝ) : ℝ :=
  deriv (fun y : ℝ => alpha2 M0 (ϖ * y) u v s) d

/-- `∂_d α₃` with `𝗁 = ϖ d` and `M₀, u, v` fixed (`lem:app-dyn-derivative`). -/
def dAlpha3 {m n : ℕ} (M0 : Mat m n) (ϖ s : ℝ) (u : Vec m) (v : Vec n) (d : ℝ) : ℝ :=
  deriv (fun y : ℝ => alpha3 M0 (ϖ * y) u v s) d

/-- Entrywise directional derivative `𝖣𝖷_s(N)[R]` of `M ↦ 𝖷_s(M)` (`eqn:app-dyn-DX`). -/
def dirX {m n : ℕ} (N R : Mat m n) (s : ℝ) : Mat m n :=
  Matrix.of fun i j => deriv (fun t : ℝ => Xs (N + t • R) s i j) 0

/-- Sample `a` of the derivative identity: `M₀^{(a)} = N − ϖ d_a u_a ⊗ v_a` (`eqn:app-dyn-DX`). -/
def sampleMinor {m n B : ℕ} (N : Mat m n) (ϖ : ℝ) (d : Fin B → ℝ) (u : Fin B → Vec m)
    (v : Fin B → Vec n) (a : Fin B) : Mat m n :=
  N - (ϖ * d a) • outer (u a) (v a)

/-- Right-hand side of `eqn:app-dyn-DX`: `∑_a e_a [ ∂α₃ R₀(u⊗u)𝖷₀ + s∂α₁ R₀(u⊗v)R̃₀
- ∂α₁ 𝖷₀(v⊗u)𝖷₀ − s∂α₂ 𝖷₀(v⊗v)R̃₀ ]` with all quantities at `M₀^{(a)}`. -/
def dXExpr {m n B : ℕ} (N : Mat m n) (ϖ s : ℝ) (d e : Fin B → ℝ) (u : Fin B → Vec m)
    (v : Fin B → Vec n) : Mat m n :=
  ∑ a : Fin B,
    e a • (dAlpha3 (sampleMinor N ϖ d u v a) ϖ s (u a) (v a) (d a) •
        (Rs (sampleMinor N ϖ d u v a) s * outer (u a) (u a) * Xs (sampleMinor N ϖ d u v a) s)
      + (s * dAlpha1 (sampleMinor N ϖ d u v a) ϖ s (u a) (v a) (d a)) •
        (Rs (sampleMinor N ϖ d u v a) s * outer (u a) (v a) * Rts (sampleMinor N ϖ d u v a) s)
      - dAlpha1 (sampleMinor N ϖ d u v a) ϖ s (u a) (v a) (d a) •
        (Xs (sampleMinor N ϖ d u v a) s * outer (v a) (u a) * Xs (sampleMinor N ϖ d u v a) s)
      - (s * dAlpha2 (sampleMinor N ϖ d u v a) ϖ s (u a) (v a) (d a)) •
        (Xs (sampleMinor N ϖ d u v a) s * outer (v a) (v a) * Rts (sampleMinor N ϖ d u v a) s))

/-- Gaussian kernel of `lem:app-dyn-raw`: `b(x) = 𝔼 ψ''_x(d)`, `d = zᵀ Â w`. -/
def bFun {m n : ℕ} (Ah : Mat m n) (x : ℝ) : ℝ :=
  ∫ z, iteratedDeriv 2 (psiX x) (resid Ah z) ∂(gaussPair m n)

/-- `N_x = 𝔼[(w ⊗ w) ψ''''_x(d)]` of `lem:app-dyn-raw` (entrywise mean). -/
def NFun {m n : ℕ} (Ah : Mat m n) (x : ℝ) : Mat n n :=
  Muon.mean (gaussPair m n) (fun z => iteratedDeriv 4 (psiX x) (resid Ah z) • outer z.2 z.2)

/-- The scalar `F_s(T)` of `eqn:app-dyn-F` for an arbitrary real matrix `T` with its own traces:
`F_s(T) = s b(x) { σ̃ ⟨Π, R_s(T) Σ_out 𝖷_s(T)⟩ + σ ⟨Π, 𝖷_s(T) Σ_in R̃_s(T)⟩ }`,
`x = ϖ² s σ σ̃`. -/
def Fs {m n : ℕ} (C : Covariances m n) (B : ℕ) (Ah Pt : Mat m n) (ϖ s : ℝ) (T : Mat m n) : ℝ :=
  s * bFun Ah (xMinor C B T ϖ s) *
    (sigmaT C B T s * frobIP Pt (Rs T s * C.Sout * Xs T s)
      + sigmaS C B T s * frobIP Pt (Xs T s * C.Sin * Rts T s))

/-! ## Pathwise causal chain and its derivatives (`def:app-dyn-chains` and `lem:app-dyn-tangent`) -/

/-- The chain of `lem:app-dyn-tangent` for fixed batches `G`, as a function of the step `ε`:
`causalState … ε r = (Δ^ε_r, M^ε_{r-1})` with `Δ^ε_0 = D`, `M^ε_{-1} = m₀`,
`M^ε_r = β M^ε_{r-1} + (1-β) G°_{t+r+1}[Δ^ε_r]`, and `Δ^ε_{r+1} = Δ^ε_r − ε 𝖲^ε_r`, where
`𝖲^ε_r = Q_{ϱ°(Δ^ε_r)}(M^ε_r)`. -/
def causalState {m n B : ℕ} (p : DynParams) (C : Covariances m n) (G : ℤ → Batch m n B) (t : ℕ)
    (D m0 : Mat m n) (ε : ℝ) : ℕ → Mat m n × Mat m n
  | 0 => (D, m0)
  | r + 1 =>
    let st := causalState p C G t D m0 ε r
    let M : Mat m n := p.β • st.2 + (1 - p.β) • batchGrad st.1 (G ((t : ℤ) + r + 1))
    (st.1 - ε • Q (physRidge p C st.1) M, M)

/-- The update `𝖲^ε_r = Q_{ϱ°(Δ^ε_r)}(M^ε_r)` of the pathwise chain (`lem:app-dyn-tangent`). -/
def causalS {m n B : ℕ} (p : DynParams) (C : Covariances m n) (G : ℤ → Batch m n B) (t : ℕ)
    (D m0 : Mat m n) (ε : ℝ) (r : ℕ) : Mat m n :=
  Q (physRidge p C (causalState p C G t D m0 ε r).1) (causalState p C G t D m0 ε (r + 1)).2

/-- Frozen update `V^{m₀}_k = Q_{ϱ°(D)}(N^{m₀}_k)` at `ε = 0` (`lem:app-dyn-tangent`, `def:app-dyn-chains`),
with `N^{m₀}_k = emaChain … (k + 1)`. -/
def frozenV {m n B : ℕ} (p : DynParams) (C : Covariances m n) (G : ℤ → Batch m n B) (t : ℕ)
    (D m0 : Mat m n) (k : ℕ) : Mat m n :=
  Q (physRidge p C D) (emaChain p.β D G t m0 (k + 1))

/-- The derivative `Ṁ_r` of `M^ε_r` at `ε = 0` (`eqn:app-dyn-tangent`, with the sign of
`Δ̇_r = −∑_{k<r} V_k`). -/
def tangentM {m n B : ℕ} (p : DynParams) (C : Covariances m n) (G : ℤ → Batch m n B) (t : ℕ)
    (D m0 : Mat m n) (r : ℕ) : Mat m n :=
  -∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
    emaW p.β (r - j) • batchGrad (frozenV p C G t D m0 k) (G ((t : ℤ) + j + 1))

/-- The entrywise derivative `Ṡ_r` at `ε = 0` of the pathwise update (`lem:app-dyn-tangent`). -/
def causalDot {m n B : ℕ} (p : DynParams) (C : Covariances m n) (G : ℤ → Batch m n B) (t : ℕ)
    (D m0 : Mat m n) (r : ℕ) : Mat m n :=
  Matrix.of fun i j => deriv (fun ε : ℝ => causalS p C G t D m0 ε r i j) 0

/-! ## Stationary chain of the sampled model (`def:app-dyn-chains`) -/

/-- `N_r` of the stationary chain at `(t, D)`, read from `def_app_dyn_chains` (`stat (r + 1)`). -/
def stationaryN {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (p : DynParams)
    (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n) (r : ℕ) (ω : Ω) :
    Mat m n :=
  (def_app_dyn_chains p C cs t D 0 ω).stat (r + 1)

/-- `V_r = Q_{ϱ°(D)}(N_r)` of the stationary chain at `(t, D)` (`stat`-side `statV (r + 1)`). -/
def stationaryV {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (p : DynParams)
    (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n) (r : ℕ) (ω : Ω) :
    Mat m n :=
  (def_app_dyn_chains p C cs t D 0 ω).statV (r + 1)

/-- The stationary chain with the target sample `a` of the batch of step `t + j + 1` removed:
`T_a = N_r − ϖ d_{j,a} u_{j,a} ⊗ v_{j,a}`, `ϖ = emaW(r − j)`, `d = zᵀ Â w`, `Â = Ahat(D)`
(`prop:app-dyn-reduction`, ll. 1237–1256). -/
def sampleRemainder {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (p : DynParams)
    (C : Covariances m n) (cs : ChainSamples P m n B) (t j r : ℕ) (D : Mat m n) (a : Fin B)
    (ω : Ω) : Mat m n :=
  let x := cs.act ((t : ℤ) + j + 1) a ω
  stationaryN p C cs t D r ω - (emaW p.β (r - j) * resid (Ahat C D) x) •
    outer (sampU C B x) (sampV C B x)

/-- The σ-algebra of the batch of step `t + j` (gradient `G°_{t+j+1}`, `cs.act (t+j+1)`)
(`prop:app-dyn-reduction`). -/
abbrev batchSigma {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (cs : ChainSamples P m n B) (t j : ℕ) : MeasurableSpace Ω :=
  ⨆ a : Fin B, MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) a) inferInstance

/-- The σ-algebra of all other samples (`prop:app-dyn-reduction`, CORRECTIONS row 19): the batches of the
steps other than `t + j` and all auxiliary batches. -/
abbrev otherSigma {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (cs : ChainSamples P m n B) (t j : ℕ) : MeasurableSpace Ω :=
  (⨆ (s : ℤ) (_ : s ≠ (t : ℤ) + j + 1) (a : Fin B), MeasurableSpace.comap (cs.act s a) inferInstance) ⊔
    (⨆ (t' : ℤ) (i : ℕ) (a : Fin B), MeasurableSpace.comap (cs.aux t' i a) inferInstance)

/-! ## Theorems -/

private lemma causal_zero {m n B : ℕ} (p : DynParams) (C : Covariances m n)
    (G : ℤ → Batch m n B) (t : ℕ) (D m0 : Mat m n) (r : ℕ) :
    causalState p C G t D m0 0 r = (D, emaChain p.β D G t m0 r) := by
  induction r with
  | zero => rfl
  | succ r ih => simp [causalState, ih, emaChain]

private lemma causal_Q_chain {m n : ℕ} (K : ℝ → Mat m n) (l : ℝ → ℝ)
    (R : Mat m n) (a : ℝ) (hl : 0 < l 0)
    (hK : ∀ i j, HasDerivAt (fun x => K x i j) (R i j) 0)
    (hl' : HasDerivAt l a 0) (i : Fin m) (j : Fin n) :
    HasDerivAt (fun x => Q (l x) (K x) i j)
      ((dirDeriv (l 0) (K 0) R + a • ridgeDeriv (l 0) (K 0)) i j) 0 := by
  let F := fun z : (Fin m → Fin n → ℝ) × ℝ => Q z.2 (Matrix.of z.1) i j
  have hd : DifferentiableAt ℝ F (K 0, l 0) := by
    have ho : {z : (Fin m → Fin n → ℝ) × ℝ | 0 < z.2} ∈ 𝓝 (K 0, l 0) :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds hl
    exact (contDiffAt_pi.mp (contDiffAt_pi.mp
      ((Q_contDiffOn_pos m n).contDiffAt ho) i) j).differentiableAt (by norm_num)
  let L := fderiv ℝ F (K 0, l 0)
  have hL : HasFDerivAt F L (K 0, l 0) := hd.hasFDerivAt
  have hk : HasDerivAt (fun x => (fun u v => K x u v)) (fun u v => R u v) 0 :=
    hasDerivAt_pi.mpr fun u => hasDerivAt_pi.mpr fun v => hK u v
  have hmain := hL.comp_hasDerivAt 0 (hk.prodMk hl')
  have hline : HasDerivAt
      (fun x : ℝ => ((fun u v => K 0 u v + x * R u v), l 0)) (R, 0) 0 := by
    convert ((hasDerivAt_const (0 : ℝ) (fun u v => K 0 u v)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (fun u v => R u v))).prodMk
      (hasDerivAt_const (0 : ℝ) (l 0)) using 1 <;> first | rfl | simp
  have he1 : L (R, 0) = dirDeriv (l 0) (K 0) R i j := by
    have hh := hL.comp_hasDerivAt_of_eq 0 hline (by simp)
    exact hh.deriv.symm
  have hridge : HasDerivAt (fun x : ℝ => ((fun u v => K 0 u v), x)) (0, 1) (l 0) :=
    (hasDerivAt_const (l 0) (fun u v => K 0 u v)).prodMk (hasDerivAt_id (l 0))
  have he2 : L (0, 1) = ridgeDeriv (l 0) (K 0) i j := by
    exact (hL.comp_hasDerivAt (l 0) hridge).deriv.symm
  have he : L (R, a) = L (R, 0) + a * L (0, 1) := by
    have hp : ((fun u v => R u v), a) = ((fun u v => R u v), (0 : ℝ)) + a • ((0 : Fin m → Fin n → ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hp, map_add, map_smul]; rfl
  rw [he, he1, he2] at hmain
  convert hmain using 1
  · funext x
    change Q (l x) (K x) i j = Q (l x) (Matrix.of fun u v => K x u v) i j
    congr 2
  · rfl

private lemma causal_pair_symm {m n : ℕ} (C : Covariances m n) (A E : Mat m n) :
    pairSigma C A E = pairSigma C E A := by
  have ho : C.Soutᵀ = C.Sout := C.psdOut.isHermitian.eq
  have hi : C.Sinᵀ = C.Sin := C.psdIn.isHermitian.eq
  unfold pairSigma
  rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose, ho, hi]
  simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_comm (E * C.Sin * Aᵀ) C.Sout)

private lemma causal_pair_deriv {m n : ℕ} (C : Covariances m n)
    (A E : ℝ → Mat m n) (A' E' : Mat m n)
    (hA : ∀ i j, HasDerivAt (fun x => A x i j) (A' i j) 0)
    (hE : ∀ i j, HasDerivAt (fun x => E x i j) (E' i j) 0) :
    HasDerivAt (fun x => pairSigma C (A x) (E x))
      (pairSigma C A' (E 0) + pairSigma C (A 0) E') 0 := by
  simp only [pairSigma, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  convert HasDerivAt.fun_sum (fun i _ =>
    HasDerivAt.fun_sum (fun j _ =>
      (HasDerivAt.fun_sum (fun k _ =>
        (HasDerivAt.fun_sum (fun u _ => (hA u k).const_mul (C.Sout i u))).mul_const
          (C.Sin k j))).mul (hE i j))) using 1
  simp [Finset.sum_add_distrib, Finset.sum_mul]

private lemma causal_ridge_deriv {m n : ℕ} (p : DynParams) (C : Covariances m n)
    (A : ℝ → Mat m n) (E : Mat m n)
    (hA : ∀ i j, HasDerivAt (fun x => A x i j) (E i j) 0) :
    HasDerivAt (fun x => physRidge p C (A x)) (2 * p.ϱ * pairSigma C (A 0) E) 0 := by
  have h := ((causal_pair_deriv C A A E E hA hA).div_const 2).const_mul 2 |>.mul_const p.ϱ
  convert h using 1
  · rfl
  · rw [causal_pair_symm C E (A 0)]
    ring

private lemma causal_grad_deriv {m n B : ℕ} (A : ℝ → Mat m n) (E : Mat m n)
    (b : Batch m n B) (hA : ∀ i j, HasDerivAt (fun x => A x i j) (E i j) 0)
    (i : Fin m) (j : Fin n) :
    HasDerivAt (fun x => batchGrad (A x) b i j) (batchGrad E b i j) 0 := by
  have hr : ∀ a, HasDerivAt (fun x => resid (A x) (b a)) (resid E (b a)) 0 := by
    intro a
    unfold resid Matrix.mulVec dotProduct
    exact HasDerivAt.fun_sum fun u _ =>
      (HasDerivAt.fun_sum fun v _ => (hA u v).mul_const ((b a).2 v)).const_mul ((b a).1 u)
  simpa only [batchGrad, grad, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    using (HasDerivAt.fun_sum fun a _ => (hr a).mul_const (outer (b a).1 (b a).2 i j)).const_mul
      ((B : ℝ)⁻¹)

private lemma causal_grad_neg_sum {m n B : ℕ} (V : ℕ → Mat m n)
    (b : Batch m n B) (r : ℕ) :
    batchGrad (-∑ k ∈ Finset.range r, V k) b = -∑ k ∈ Finset.range r, batchGrad (V k) b := by
  let L : Mat m n →ₗ[ℝ] Mat m n :=
    { toFun := fun E => batchGrad E b
      map_add' := by
        intro E F
        simp [batchGrad, grad, resid, Matrix.add_mulVec, dotProduct_add,
          add_smul, Finset.sum_add_distrib, smul_add]
      map_smul' := by
        intro c E
        simp [batchGrad, grad, resid, Matrix.smul_mulVec, dotProduct_smul,
          smul_smul, Finset.smul_sum, mul_comm, mul_assoc] }
  exact (L.map_neg _).trans (congrArg Neg.neg (map_sum L _ _))

private lemma causal_tangentM_succ {m n B : ℕ} (p : DynParams) (C : Covariances m n)
    (G : ℤ → Batch m n B) (t : ℕ) (D m0 : Mat m n) (r : ℕ) :
    tangentM p C G t D m0 (r + 1) = p.β • tangentM p C G t D m0 r +
      (1 - p.β) • batchGrad (-∑ k ∈ Finset.range (r + 1), frozenV p C G t D m0 k)
        (G ((t : ℤ) + (r + 1) + 1)) := by
  rw [causal_grad_neg_sum]
  unfold tangentM
  rw [Finset.sum_range_succ]
  have hw : ∀ j ∈ Finset.range (r + 1), emaW p.β (r + 1 - j) = p.β * emaW p.β (r - j) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [show r + 1 - j = (r - j) + 1 by omega]
    unfold emaW
    rw [pow_succ]
    ring
  have he : (∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
      emaW p.β (r + 1 - j) • batchGrad (frozenV p C G t D m0 k) (G ((t : ℤ) + j + 1))) =
      p.β • ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
      emaW p.β (r - j) • batchGrad (frozenV p C G t D m0 k) (G ((t : ℤ) + j + 1)) := by
    simp only [Finset.smul_sum, smul_smul]
    exact Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k _ => by rw [hw j hj]
  rw [he]
  simp [emaW, Finset.smul_sum, neg_add_rev, smul_neg, add_comm]

private lemma causal_S_deriv {m n B : ℕ} (p : DynParams) (C : Covariances m n)
    (G : ℤ → Batch m n B) (t : ℕ) (D m0 : Mat m n) (hD : 0 < riskSigma C D) (r : ℕ)
    (hA : ∀ i j, HasDerivAt (fun ε : ℝ => (causalState p C G t D m0 ε r).1 i j)
      ((-∑ k ∈ Finset.range r, frozenV p C G t D m0 k) i j) 0)
    (hM : ∀ i j, HasDerivAt (fun ε : ℝ => (causalState p C G t D m0 ε (r + 1)).2 i j)
      (tangentM p C G t D m0 r i j) 0) (i : Fin m) (j : Fin n) :
    HasDerivAt (fun ε : ℝ => causalS p C G t D m0 ε r i j)
      ((dirDeriv (physRidge p C D) (emaChain p.β D G t m0 (r + 1)) (tangentM p C G t D m0 r)
        + (-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r, frozenV p C G t D m0 k))) •
          ridgeDeriv (physRidge p C D) (emaChain p.β D G t m0 (r + 1))) i j) 0 := by
  have hl := causal_ridge_deriv p C (fun ε => (causalState p C G t D m0 ε r).1) _ hA
  have hp : 0 < physRidge p C (causalState p C G t D m0 0 r).1 := by
    rw [causal_zero]
    exact mul_pos (mul_pos (by norm_num) hD) p.hϱ
  have h := causal_Q_chain (fun ε => (causalState p C G t D m0 ε (r + 1)).2)
    (fun ε => physRidge p C (causalState p C G t D m0 ε r).1)
    (tangentM p C G t D m0 r) _ hp hM hl i j
  simpa only [causalS, causal_zero, Prod.fst, Prod.snd, pairSigma, Matrix.transpose_neg,
    Matrix.mul_neg, Matrix.trace_neg, mul_neg] using h

/-- `lem:app-dyn-tangent`, snapshot `cr-2026-10-23`. Statement verbatim from `section.tex` (ll. 1027–1036):
```latex
\begin{lemma}[Causal tangent]\label{lem:app-dyn-tangent}
The derivatives at $\varepsilon=0$ exist, and with $\ell=\ridgephys(D)$,
\begin{equation}\label{eqn:app-dyn-tangent}
\begin{gathered}
\dot\Delta_r=-\sum_{k<r}V^{m_0}_k,\qquad
\dot M_r=-\sum_{0\le k<j\le r}\emaw{r-j}\,G^\circ_{t+j+1}\big[V^{m_0}_k\big],\\
\dot {\mathsf S}_r=D\Qridge\ell(N^{m_0}_r)\big[\dot M_r\big]-2\ridge\Big\langle\Sigmaout D\Sigmain,\sum_{k<r}V^{m_0}_k\Big\rangle\,\partial_\ell\Qridge\ell(N^{m_0}_r).
\end{gathered}
\end{equation}
\end{lemma}
```
-/
theorem lem_app_dyn_tangent {m n B : ℕ} (p : DynParams) (C : Covariances m n)
    (G : ℤ → Batch m n B) (t : ℕ) (D m0 : Mat m n) (hD : 0 < riskSigma C D) :
    (∀ r : ℕ, ∀ i j, HasDerivAt (fun ε : ℝ => (causalState p C G t D m0 ε r).1 i j)
        ((-∑ k ∈ Finset.range r, frozenV p C G t D m0 k) i j) 0) ∧
    (∀ r : ℕ, ∀ i j, HasDerivAt (fun ε : ℝ => (causalState p C G t D m0 ε (r + 1)).2 i j)
        (tangentM p C G t D m0 r i j) 0) ∧
    (∀ r : ℕ, ∀ i j, HasDerivAt (fun ε : ℝ => causalS p C G t D m0 ε r i j)
        ((dirDeriv (physRidge p C D) (emaChain p.β D G t m0 (r + 1)) (tangentM p C G t D m0 r)
          + (-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r, frozenV p C G t D m0 k))) •
            ridgeDeriv (physRidge p C D) (emaChain p.β D G t m0 (r + 1))) i j) 0) := by
  have hall : ∀ r : ℕ,
      (∀ i j, HasDerivAt (fun ε : ℝ => (causalState p C G t D m0 ε r).1 i j)
        ((-∑ k ∈ Finset.range r, frozenV p C G t D m0 k) i j) 0) ∧
      (∀ i j, HasDerivAt (fun ε : ℝ => (causalState p C G t D m0 ε (r + 1)).2 i j)
        (tangentM p C G t D m0 r i j) 0) := by
    intro r
    induction r with
    | zero =>
      constructor
      · intro i j
        simpa [causalState] using hasDerivAt_const (0 : ℝ) (D i j)
      · intro i j
        simpa [causalState, tangentM] using hasDerivAt_const (0 : ℝ)
          ((p.β • m0 + (1 - p.β) • batchGrad D (G ((t : ℤ) + 0 + 1))) i j)
    | succ r ih =>
      have hS := causal_S_deriv p C G t D m0 hD r ih.1 ih.2
      have hA : ∀ i j, HasDerivAt (fun ε : ℝ => (causalState p C G t D m0 ε (r + 1)).1 i j)
          ((-∑ k ∈ Finset.range (r + 1), frozenV p C G t D m0 k) i j) 0 := by
        intro i j
        have hh := (ih.1 i j).sub ((hasDerivAt_id (0 : ℝ)).mul (hS i j))
        convert hh using 1
        · rfl
        · simp [causalS, causal_zero, frozenV, Finset.sum_range_succ,
            Matrix.neg_apply, Matrix.add_apply, add_comm, sub_eq_add_neg]
      refine ⟨hA, ?_⟩
      intro i j
      have hh := ((ih.2 i j).const_mul p.β).add
        ((causal_grad_deriv (fun ε => (causalState p C G t D m0 ε (r + 1)).1)
          _ (G ((t : ℤ) + (r + 1) + 1)) hA i j).const_mul (1 - p.β))
      convert hh using 1
      · rfl
      · rw [causal_tangentM_succ]
        rfl
  exact ⟨fun r => (hall r).1, fun r => (hall r).2,
    fun r => causal_S_deriv p C G t D m0 hD r (hall r).1 (hall r).2⟩

/-- `lem:app-dyn-derivative`, snapshot `cr-2026-10-23`. Statement verbatim from `section.tex` (ll. 1078–1099):
```latex
\begin{lemma}[Residual derivatives]\label{lem:app-dyn-derivative}
In the setting of \cref{lem:app-de-deletion}, let $\mathsf h=\varpi d$ with
$\varpi\in[0,1]$, and regard the coefficients \cref{eqn:app-de-coefficients}
as functions of $d$ with $M_0,\mathsf u,\mathsf v$ fixed. Then
\begin{equation}\label{eqn:app-dyn-derivative}
\partial_d\alpha_1=\frac{\varpi\big[(1+\mathsf h\mathsf C)^2-s\mathsf h^2\mathsf U\mathsf V\big]}{\Lambda^2},\qquad
\partial_d\alpha_2=\frac{2\varpi\mathsf h\mathsf U(1+\mathsf h\mathsf C)}{\Lambda^2},\qquad
\partial_d\alpha_3=-\frac{2s\varpi\mathsf h\mathsf V(1+\mathsf h\mathsf C)}{\Lambda^2}.
\end{equation}
Let $N=N'+\varpi\sum_{a\le B}d_a\,\mathsf u_a\tensor\mathsf v_a$, where $N'$ and the
vectors $\mathsf u_a,\mathsf v_a$ do not depend on the scalars $d_a$, and for each
$a$ let the quantities of \cref{lem:app-de-deletion} be computed with
$(M_0,\mathsf h,\mathsf u,\mathsf v)=(N-\varpi d_a\mathsf u_a\tensor\mathsf v_a,\varpi d_a,\mathsf u_a,\mathsf v_a)$,
with a superscript $(a)$. Then for real $(e_a)_{a\le B}$,
\begin{equation}\label{eqn:app-dyn-DX}
\begin{aligned}
&\frac{\dif}{\dif\vartheta}\mathsf X_s\Big(N+\vartheta\varpi\sum_ae_a\mathsf u_a\tensor\mathsf v_a\Big)\Big|_{\vartheta=0}\\
&\qquad=\sum_ae_a\Big[\partial_d\alpha_3^{(a)}R_0^{(a)}(\mathsf u_a\tensor\mathsf u_a)\mathsf X_0^{(a)}+s\,\partial_d\alpha_1^{(a)}R_0^{(a)}(\mathsf u_a\tensor\mathsf v_a)\widetilde R_0^{(a)}\\
&\qquad\qquad-\partial_d\alpha_1^{(a)}\mathsf X_0^{(a)}(\mathsf v_a\tensor\mathsf u_a)\mathsf X_0^{(a)}-s\,\partial_d\alpha_2^{(a)}\mathsf X_0^{(a)}(\mathsf v_a\tensor\mathsf v_a)\widetilde R_0^{(a)}\Big].
\end{aligned}
\end{equation}
\end{lemma}
```
-/
theorem lem_app_dyn_derivative_i {m n : ℕ} (M0 : Mat m n) (ϖ s : ℝ) (u : Vec m) (v : Vec n)
    (hs : 0 < s) (hϖ : ϖ ∈ Icc (0 : ℝ) 1) (d : ℝ) :
    HasDerivAt (fun y : ℝ => alpha1 M0 (ϖ * y) u v s)
        (ϖ * ((1 + (ϖ * d) * delC M0 u v s) ^ 2 - s * (ϖ * d) ^ 2 * delU M0 u s * delV M0 v s)
          / (delLambda M0 (ϖ * d) u v s) ^ 2) d ∧
    HasDerivAt (fun y : ℝ => alpha2 M0 (ϖ * y) u v s)
        (2 * ϖ * (ϖ * d) * delU M0 u s * (1 + (ϖ * d) * delC M0 u v s)
          / (delLambda M0 (ϖ * d) u v s) ^ 2) d ∧
    HasDerivAt (fun y : ℝ => alpha3 M0 (ϖ * y) u v s)
        (-(2 * s * ϖ * (ϖ * d) * delV M0 v s * (1 + (ϖ * d) * delC M0 u v s))
          / (delLambda M0 (ϖ * d) u v s) ^ 2) d := by
  have hΛ : delLambda M0 (ϖ * d) u v s ≠ 0 := by
    have hM : M0 + (ϖ * d) • outer u v = M0 + (ϖ * d) • outer u v := rfl
    exact (lem_app_de_deletion M0 (ϖ * d) u v
      (M0 + (ϖ * d) • outer u v) s hM hs).1.ne'
  have hx : HasDerivAt (fun y : ℝ => ϖ * y) ϖ d := by
    simpa using (hasDerivAt_id d).const_mul ϖ
  have hden : HasDerivAt (fun y : ℝ => delLambda M0 (ϖ * y) u v s)
      (2 * ϖ * delC M0 u v s * (1 + (ϖ * d) * delC M0 u v s)
        + 2 * s * ϖ * (ϖ * d) * delU M0 u s * delV M0 v s) d := by
    unfold delLambda
    convert (((hasDerivAt_const d 1).add (hx.mul_const (delC M0 u v s))).pow 2).add
      ((((hx.pow 2).const_mul s).mul_const (delU M0 u s)).mul_const (delV M0 v s)) using 1 <;>
      simp only [Pi.add_apply] <;> ring
  have h₁ : HasDerivAt (fun y : ℝ => (ϖ * y) * (1 + (ϖ * y) * delC M0 u v s))
      (ϖ * (1 + 2 * (ϖ * d) * delC M0 u v s)) d := by
    convert hx.mul ((hasDerivAt_const d 1).add (hx.mul_const (delC M0 u v s))) using 1 <;>
      simp only [Pi.add_apply] <;> ring
  have h₂ : HasDerivAt (fun y : ℝ => (ϖ * y) ^ 2 * delU M0 u s)
      (2 * ϖ * (ϖ * d) * delU M0 u s) d := by
    convert (hx.pow 2).mul_const (delU M0 u s) using 1 <;> ring
  have h₃ : HasDerivAt (fun y : ℝ => -(s * (ϖ * y) ^ 2 * delV M0 v s))
      (-(2 * s * ϖ * (ϖ * d) * delV M0 v s)) d := by
    convert (((hx.pow 2).const_mul s).mul_const (delV M0 v s)).neg using 1 <;> ring
  constructor
  · unfold alpha1
    convert h₁.fun_div hden hΛ using 1 <;> simp only [delLambda] <;> field_simp <;> ring
  constructor
  · unfold alpha2
    convert h₂.fun_div hden hΛ using 1 <;> simp only [delLambda] <;> field_simp <;> ring
  · unfold alpha3
    convert h₃.fun_div hden hΛ using 1 <;> simp only [delLambda] <;> field_simp <;> ring

private lemma pe8_vmv {m n : ℕ} (a : Fin m → ℝ) (b c : Fin n → ℝ) :
    vecMulVec a b *ᵥ c = (b ⬝ᵥ c) • a := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma pe8_Rs_symm {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (s : ℝ) :
    (Rs M s)ᵀ = Rs M s := by
  unfold Rs
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  simp [Matrix.transpose_add, Matrix.transpose_mul]

private lemma pe8_Rs_sandwich {m n : ℕ} (M₀ : Matrix (Fin m) (Fin n) ℝ) (s : ℝ)
    (hR₀ : IsUnit (M₀ * M₀ᵀ + s • (1 : Matrix (Fin m) (Fin m) ℝ)).det)
    (hRt₀ : IsUnit (M₀ᵀ * M₀ + s • (1 : Matrix (Fin n) (Fin n) ℝ)).det) :
    M₀ᵀ * Rs M₀ s * M₀ = 1 - s • Rts M₀ s := by
  unfold Rs Rts
  have key : M₀ᵀ * (M₀ * M₀ᵀ + s • (1 : Matrix (Fin m) (Fin m) ℝ))
      = (M₀ᵀ * M₀ + s • (1 : Matrix (Fin n) (Fin n) ℝ)) * M₀ᵀ := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_smul,
      Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  set A := M₀ * M₀ᵀ + s • (1 : Matrix (Fin m) (Fin m) ℝ) with hAdef
  set B := M₀ᵀ * M₀ + s • (1 : Matrix (Fin n) (Fin n) ℝ) with hBdef
  have hcomm : M₀ᵀ * A⁻¹ = B⁻¹ * M₀ᵀ := by
    calc M₀ᵀ * A⁻¹ = (B⁻¹ * B) * (M₀ᵀ * A⁻¹) := by
          rw [Matrix.nonsing_inv_mul _ hRt₀, Matrix.one_mul]
      _ = B⁻¹ * ((B * M₀ᵀ) * A⁻¹) := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * ((M₀ᵀ * A) * A⁻¹) := by rw [key]
      _ = B⁻¹ * (M₀ᵀ * (A * A⁻¹)) := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * M₀ᵀ := by rw [Matrix.mul_nonsing_inv _ hR₀, Matrix.mul_one]
  have hMB : M₀ᵀ * M₀ = B - s • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hBdef, add_sub_cancel_right]
  calc M₀ᵀ * A⁻¹ * M₀ = B⁻¹ * (M₀ᵀ * M₀) := by rw [hcomm, Matrix.mul_assoc]
    _ = B⁻¹ * (B - s • (1 : Matrix (Fin n) (Fin n) ℝ)) := by rw [hMB]
    _ = 1 - s • B⁻¹ := by
          rw [mul_sub, Matrix.nonsing_inv_mul _ hRt₀, Matrix.mul_smul, Matrix.mul_one]

private theorem pe8_col_i {m n : ℕ}
    (M M₀ : Matrix (Fin m) (Fin n) ℝ) (h s : ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hΛ : delLambda M₀ h u v s ≠ 0)
    (hdel : Rs M s - Rs M₀ s =
      alpha3 M₀ h u v s • vecMulVec (Rs M₀ s *ᵥ u) (Rs M₀ s *ᵥ u)
        - alpha1 M₀ h u v s • vecMulVec (Rs M₀ s *ᵥ u) (Xs M₀ s *ᵥ v)
        - alpha1 M₀ h u v s • vecMulVec (Xs M₀ s *ᵥ v) (Rs M₀ s *ᵥ u)
        + alpha2 M₀ h u v s • vecMulVec (Xs M₀ s *ᵥ v) (Xs M₀ s *ᵥ v)) :
    h • (Rs M s *ᵥ u) =
      alpha1 M₀ h u v s • (Rs M₀ s *ᵥ u) - alpha2 M₀ h u v s • (Xs M₀ s *ᵥ v) := by
  have hU : dotProduct (Rs M₀ s *ᵥ u) u = delU M₀ u s := by
    unfold delU; exact dotProduct_comm _ _
  have hC : dotProduct (Xs M₀ s *ᵥ v) u = delC M₀ u v s := by
    unfold delC; exact dotProduct_comm _ _
  have hd := congrArg (fun A : Matrix (Fin m) (Fin m) ℝ => A *ᵥ u) hdel
  simp only [sub_mulVec, add_mulVec, smul_mulVec, pe8_vmv, hU, hC] at hd
  have hR : Rs M s *ᵥ u = Rs M₀ s *ᵥ u
      + (alpha3 M₀ h u v s * delU M₀ u s - alpha1 M₀ h u v s * delC M₀ u v s)
          • (Rs M₀ s *ᵥ u)
      + (alpha2 M₀ h u v s * delC M₀ u v s - alpha1 M₀ h u v s * delU M₀ u s)
          • (Xs M₀ s *ᵥ v) := by
    linear_combination (norm := module) hd
  have S1 : h * (1 + alpha3 M₀ h u v s * delU M₀ u s - alpha1 M₀ h u v s * delC M₀ u v s)
      = alpha1 M₀ h u v s := by
    unfold alpha1 alpha3
    unfold delLambda at hΛ ⊢
    generalize hLg : (1 + h * delC M₀ u v s) ^ 2 + s * h ^ 2 * delU M₀ u s * delV M₀ v s = L
      at hΛ ⊢
    field_simp
    rw [← hLg]
    ring
  have S2 : h * (alpha2 M₀ h u v s * delC M₀ u v s - alpha1 M₀ h u v s * delU M₀ u s)
      = -alpha2 M₀ h u v s := by
    unfold alpha1 alpha2
    unfold delLambda at hΛ ⊢
    field_simp
    ring
  rw [hR]
  linear_combination (norm := module) S1 • (Rs M₀ s *ᵥ u) + S2 • (Xs M₀ s *ᵥ v)

private theorem pe8_col_ii {m n : ℕ}
    (M M₀ : Matrix (Fin m) (Fin n) ℝ) (h s : ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hM : M = M₀ + h • vecMulVec u v)
    (hR₀ : IsUnit (M₀ * M₀ᵀ + s • (1 : Matrix (Fin m) (Fin m) ℝ)).det)
    (hRt₀ : IsUnit (M₀ᵀ * M₀ + s • (1 : Matrix (Fin n) (Fin n) ℝ)).det)
    (hΛ : delLambda M₀ h u v s ≠ 0)
    (hdel : Rs M s - Rs M₀ s =
      alpha3 M₀ h u v s • vecMulVec (Rs M₀ s *ᵥ u) (Rs M₀ s *ᵥ u)
        - alpha1 M₀ h u v s • vecMulVec (Rs M₀ s *ᵥ u) (Xs M₀ s *ᵥ v)
        - alpha1 M₀ h u v s • vecMulVec (Xs M₀ s *ᵥ v) (Rs M₀ s *ᵥ u)
        + alpha2 M₀ h u v s • vecMulVec (Xs M₀ s *ᵥ v) (Xs M₀ s *ᵥ v)) :
    Xs M s - Xs M₀ s =
      alpha3 M₀ h u v s • (Rs M₀ s * vecMulVec u u * Xs M₀ s)
        + (s * alpha1 M₀ h u v s) • (Rs M₀ s * vecMulVec u v * Rts M₀ s)
        - alpha1 M₀ h u v s • (Xs M₀ s * vecMulVec v u * Xs M₀ s)
        - (s * alpha2 M₀ h u v s) • (Xs M₀ s * vecMulVec v v * Rts M₀ s) := by
  have hsymm : (Rs M₀ s)ᵀ = Rs M₀ s := pe8_Rs_symm M₀ s
  have hid : M₀ᵀ * Rs M₀ s * M₀ = 1 - s • Rts M₀ s := pe8_Rs_sandwich M₀ s hR₀ hRt₀
  have hXT : (Xs M₀ s)ᵀ * M₀ = 1 - s • Rts M₀ s := by
    unfold Xs
    rw [Matrix.transpose_mul, hsymm]
    exact hid
  have hvR : ∀ w : Fin m → ℝ, w ᵥ* Rs M₀ s = Rs M₀ s *ᵥ w := by
    intro w
    rw [← Matrix.mulVec_transpose, hsymm]
  have V1 : (Rs M₀ s *ᵥ u) ᵥ* M₀ = u ᵥ* Xs M₀ s := by
    unfold Xs
    rw [← hvR, Matrix.vecMul_vecMul]
  have V2 : (Xs M₀ s *ᵥ v) ᵥ* M₀ = v - s • (v ᵥ* Rts M₀ s) := by
    have hvX : Xs M₀ s *ᵥ v = v ᵥ* (Xs M₀ s)ᵀ := by
      rw [← Matrix.mulVec_transpose, Matrix.transpose_transpose]
    rw [hvX, Matrix.vecMul_vecMul, hXT, Matrix.vecMul_sub, Matrix.vecMul_smul,
      Matrix.vecMul_one]
  have hRu := pe8_col_i M M₀ h s u v hΛ hdel
  have hR' := sub_eq_iff_eq_add'.mp hdel
  have hMR : ∀ R : Matrix (Fin m) (Fin m) ℝ,
      R * M = R * M₀ + vecMulVec (h • (R *ᵥ u)) v := by
    intro R
    rw [hM, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_vecMulVec]
    congr 1
    ext i j
    simp [vecMulVec, mul_assoc]
  have hX' : Xs M s = Rs M s * M₀ + vecMulVec (h • (Rs M s *ᵥ u)) v := hMR _
  have hd0 : Rs M₀ s * M₀ = Xs M₀ s := rfl
  have hsplit : ∀ a b c : Matrix (Fin m) (Fin n) ℝ, a + b + c - a = b + c :=
    fun a b c => by abel
  rw [hX', hRu, hR', Matrix.add_mul (Rs M₀ s), hd0, hsplit]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.vecMulVec_mul,
    Matrix.mul_vecMulVec,
    V1, V2]
  ext i j
  simp only [vecMulVec, Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem pe8_col {m n : ℕ}
    (M M₀ : Mat m n) (h s : ℝ) (u : Vec m) (v : Vec n)
    (hM : M = M₀ + h • outer u v) (hs : 0 < s) :
    h • (Rs M s *ᵥ u) =
        alpha1 M₀ h u v s • (Rs M₀ s *ᵥ u)
          - alpha2 M₀ h u v s • (Xs M₀ s *ᵥ v) ∧
    Xs M s - Xs M₀ s =
        alpha3 M₀ h u v s •
            (Rs M₀ s * outer u u * Xs M₀ s)
          + (s * alpha1 M₀ h u v s) •
            (Rs M₀ s * outer u v * Rts M₀ s)
          - alpha1 M₀ h u v s •
            (Xs M₀ s * outer v u * Xs M₀ s)
          - (s * alpha2 M₀ h u v s) •
            (Xs M₀ s * outer v v * Rts M₀ s) := by
  have hUnit : ∀ {a b : ℕ} (A : Mat a b),
      IsUnit (A * Aᵀ + s • (1 : Mat a a)).det := by
    intro a b A
    have h1 : (A * Aᵀ).PosSemidef := by
      have h := Matrix.posSemidef_self_mul_conjTranspose A
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    have h2 : (s • (1 : Mat a a)).PosDef := Matrix.PosDef.one.smul hs
    have h3 := Matrix.PosDef.add_posSemidef h2 h1
    rw [add_comm]
    exact isUnit_iff_ne_zero.mpr h3.det_pos.ne'
  have hUnitT : IsUnit (M₀ᵀ * M₀ + s • (1 : Mat n n)).det := by
    have h := hUnit M₀ᵀ
    rwa [Matrix.transpose_transpose] at h
  have hdel := (lem_app_de_deletion M₀ h u v M s hM hs).2.1
  have hΛ := (lem_app_de_deletion M₀ h u v M s hM hs).1.ne'
  exact ⟨pe8_col_i M M₀ h s u v hΛ hdel,
    pe8_col_ii M M₀ h s u v hM (hUnit M₀) hUnitT hΛ hdel⟩


private lemma pe8_det_diff {k : ℕ} (G : ℝ → Matrix (Fin k) (Fin k) ℝ) (t : ℝ)
    (hG : ∀ i j, DifferentiableAt ℝ (fun θ => G θ i j) t) :
    DifferentiableAt ℝ (fun θ => (G θ).det) t := by
  simp_rw [Matrix.det_apply]
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  refine DifferentiableAt.const_smul ?_ _
  refine DifferentiableAt.fun_finsetProd fun i _ => hG _ _

private lemma pe8_inv_diff {k : ℕ} (G : ℝ → Matrix (Fin k) (Fin k) ℝ) (t : ℝ)
    (hG : ∀ i j, DifferentiableAt ℝ (fun θ => G θ i j) t) (hdet : (G t).det ≠ 0) (i j : Fin k) :
    DifferentiableAt ℝ (fun θ => (G θ)⁻¹ i j) t := by
  have h1 : ∀ θ, (G θ)⁻¹ i j = ((G θ).det)⁻¹ * (G θ).adjugate i j := by
    intro θ
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  simp_rw [h1]
  refine DifferentiableAt.mul (DifferentiableAt.inv (pe8_det_diff G t hG) hdet) ?_
  simp_rw [Matrix.adjugate_apply]
  refine pe8_det_diff (fun θ => (G θ).updateRow j (Pi.single i 1)) t ?_
  intro a b
  by_cases ha : a = j
  · subst ha
    simp only [Matrix.updateRow_self]
    exact differentiableAt_const _
  · simp only [Matrix.updateRow_ne ha]
    exact hG a b

private lemma pe8_unit {m n : ℕ} (A : Mat m n) (s : ℝ) (hs : 0 < s) :
    (A * Aᵀ + s • (1 : Mat m m)).det ≠ 0 := by
  have h1 : (A * Aᵀ).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have h2 : (s • (1 : Mat m m)).PosDef := Matrix.PosDef.one.smul hs
  have h3 := Matrix.PosDef.add_posSemidef h2 h1
  rw [add_comm]
  exact h3.det_pos.ne'

private lemma pe8_dX {m n : ℕ} (N T : Mat m n) (s : ℝ) (hs : 0 < s) :
    ∀ i j, HasDerivAt (fun θ : ℝ => Xs (N + θ • T) s i j)
      ((Rs N s * T - Rs N s * (T * Nᵀ + N * Tᵀ) * Rs N s * N) i j) 0 := by
  set G : ℝ → Mat m m := fun θ => (N + θ • T) * (N + θ • T)ᵀ + s • (1 : Mat m m) with hGdef
  set G' : Mat m m := T * Nᵀ + N * Tᵀ with hG'def
  have hA : ∀ i k, HasDerivAt (fun θ : ℝ => (N + θ • T) i k) (T i k) 0 := by
    intro i k
    convert ((hasDerivAt_id (0 : ℝ)).mul_const (T i k)).const_add (N i k) using 1 <;>
      simp [Matrix.add_apply, Matrix.smul_apply]
  have hGd : ∀ i j, HasDerivAt (fun θ : ℝ => G θ i j) (G' i j) 0 := by
    intro i j
    have hs' : ∀ θ : ℝ, G θ i j = ∑ k, (N + θ • T) i k * (N + θ • T) j k + s * (1 : Mat m m) i j := by
      intro θ
      simp [hGdef, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply]
    simp_rw [hs']
    have := (HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hA i k).mul (hA j k))).add_const
      (s * (1 : Mat m m) i j)
    convert this using 1
    simp [hG'def, Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply]
    exact (Finset.sum_add_distrib).symm
  have hdet : ∀ θ, (G θ).det ≠ 0 := fun θ => pe8_unit _ s hs
  have hRd : ∀ i j, DifferentiableAt ℝ (fun θ => (G θ)⁻¹ i j) 0 :=
    fun i j => pe8_inv_diff G 0 (fun i j => (hGd i j).differentiableAt) (hdet 0) i j
  have hG0 : G 0 = N * Nᵀ + s • (1 : Mat m m) := by simp [hGdef]
  have hR0 : (G 0)⁻¹ = Rs N s := by rw [hG0]; rfl
  set R' : Mat m m := Matrix.of fun i j => deriv (fun θ => (G θ)⁻¹ i j) 0 with hR'def
  have hRhas : ∀ i j, HasDerivAt (fun θ => (G θ)⁻¹ i j) (R' i j) 0 := fun i j =>
    (hRd i j).hasDerivAt
  -- differentiate G * G⁻¹ = 1
  have hid : ∀ θ i j, ∑ k, G θ i k * (G θ)⁻¹ k j = (1 : Mat m m) i j := by
    intro θ i j
    have := Matrix.mul_nonsing_inv (G θ) (isUnit_iff_ne_zero.mpr (hdet θ))
    have h := congrFun (congrFun this i) j
    rw [Matrix.mul_apply] at h
    exact h
  have hsum : G' * (G 0)⁻¹ + G 0 * R' = 0 := by
    ext i j
    have h1 := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hGd i k).mul (hRhas k j))
    have h2 : HasDerivAt (fun θ : ℝ => ∑ k, G θ i k * (G θ)⁻¹ k j) 0 0 := by
      simp_rw [hid]; exact hasDerivAt_const _ _
    have := h1.unique h2
    simpa [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib, add_comm] using this
  have hRinv : R' = -((G 0)⁻¹ * G' * (G 0)⁻¹) := by
    have hL : (G 0)⁻¹ * G 0 = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet 0))
    have h2 := congrArg (fun X => (G 0)⁻¹ * X) hsum
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hL, Matrix.one_mul, Matrix.mul_zero] at h2
    exact eq_neg_of_add_eq_zero_right h2
  intro i j
  have hX : ∀ θ : ℝ, Xs (N + θ • T) s i j = ∑ k, (G θ)⁻¹ i k * (N + θ • T) k j := by
    intro θ; simp [Xs, Rs, hGdef, Matrix.mul_apply]
  simp_rw [hX]
  have := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hRhas i k).mul (hA k j))
  convert this using 1
  rw [Finset.sum_add_distrib]
  simp only [zero_smul, add_zero]
  rw [← Matrix.mul_apply, ← Matrix.mul_apply, hRinv, hR0, ← Matrix.add_apply]
  refine congrFun (congrFun ?_ i) j
  simp only [Matrix.neg_mul, Matrix.mul_assoc, sub_eq_add_neg, add_comm]
  rfl

private lemma pe8_one {m n : ℕ} (N M0 : Mat m n) (ϖ s : ℝ) (u : Vec m) (v : Vec n) (d : ℝ)
    (hs : 0 < s) (hϖ : ϖ ∈ Icc (0 : ℝ) 1) (hM0 : M0 = N - (ϖ * d) • outer u v) :
    Rs N s * (ϖ • outer u v) - Rs N s * ((ϖ • outer u v) * Nᵀ + N * (ϖ • outer u v)ᵀ) * Rs N s * N =
      dAlpha3 M0 ϖ s u v d • (Rs M0 s * outer u u * Xs M0 s)
      + (s * dAlpha1 M0 ϖ s u v d) • (Rs M0 s * outer u v * Rts M0 s)
      - dAlpha1 M0 ϖ s u v d • (Xs M0 s * outer v u * Xs M0 s)
      - (s * dAlpha2 M0 ϖ s u v d) • (Xs M0 s * outer v v * Rts M0 s) := by
  obtain ⟨hd1, hd2, hd3⟩ := lem_app_dyn_derivative_i M0 ϖ s u v hs hϖ d
  have ha1 : HasDerivAt (fun y : ℝ => alpha1 M0 (ϖ * y) u v s) (dAlpha1 M0 ϖ s u v d) d :=
    hd1.differentiableAt.hasDerivAt
  have ha2 : HasDerivAt (fun y : ℝ => alpha2 M0 (ϖ * y) u v s) (dAlpha2 M0 ϖ s u v d) d :=
    hd2.differentiableAt.hasDerivAt
  have ha3 : HasDerivAt (fun y : ℝ => alpha3 M0 (ϖ * y) u v s) (dAlpha3 M0 ϖ s u v d) d :=
    hd3.differentiableAt.hasDerivAt
  ext i j
  have hT := pe8_dX N (ϖ • outer u v) s hs i j
  have hsub : HasDerivAt (fun y : ℝ => y - d) 1 d := (hasDerivAt_id d).sub_const d
  have hcomp := HasDerivAt.scomp (g₁ := fun θ : ℝ => Xs (N + θ • (ϖ • outer u v)) s i j) (x := d)
    (h := fun y : ℝ => y - d) (by simpa using hT) hsub
  have hf1 : HasDerivAt (fun y : ℝ => Xs (M0 + (ϖ * y) • outer u v) s i j)
      ((Rs N s * (ϖ • outer u v) - Rs N s * ((ϖ • outer u v) * Nᵀ + N * (ϖ • outer u v)ᵀ) *
        Rs N s * N) i j) d := by
    convert hcomp using 1
    · funext y
      have hh : M0 + (ϖ * y) • outer u v = N + (y - d) • ϖ • outer u v := by
        rw [hM0]; module
      simp only [Function.comp, hh]
    · simp
  have hf : ∀ y : ℝ, Xs (M0 + (ϖ * y) • outer u v) s i j = Xs M0 s i j
      + alpha3 M0 (ϖ * y) u v s * (Rs M0 s * outer u u * Xs M0 s) i j
      + (s * alpha1 M0 (ϖ * y) u v s) * (Rs M0 s * outer u v * Rts M0 s) i j
      - alpha1 M0 (ϖ * y) u v s * (Xs M0 s * outer v u * Xs M0 s) i j
      - (s * alpha2 M0 (ϖ * y) u v s) * (Xs M0 s * outer v v * Rts M0 s) i j := by
    intro y
    have h := (pe8_col (M0 + (ϖ * y) • outer u v) M0 (ϖ * y) s u v rfl hs).2
    have h' := congrFun (congrFun h i) j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h'
    linarith
  have hf2 : HasDerivAt (fun y : ℝ => Xs (M0 + (ϖ * y) • outer u v) s i j)
      (dAlpha3 M0 ϖ s u v d * (Rs M0 s * outer u u * Xs M0 s) i j
      + (s * dAlpha1 M0 ϖ s u v d) * (Rs M0 s * outer u v * Rts M0 s) i j
      - dAlpha1 M0 ϖ s u v d * (Xs M0 s * outer v u * Xs M0 s) i j
      - (s * dAlpha2 M0 ϖ s u v d) * (Xs M0 s * outer v v * Rts M0 s) i j) d := by
    simp_rw [hf]
    have := ((((hasDerivAt_const d (Xs M0 s i j)).add
      (ha3.mul_const ((Rs M0 s * outer u u * Xs M0 s) i j))).add
      ((ha1.const_mul s).mul_const ((Rs M0 s * outer u v * Rts M0 s) i j))).sub
      (ha1.mul_const ((Xs M0 s * outer v u * Xs M0 s) i j))).sub
      ((ha2.const_mul s).mul_const ((Xs M0 s * outer v v * Rts M0 s) i j))
    convert this using 1
    simp
  rw [hf1.unique hf2]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-- `lem:app-dyn-derivative`, snapshot `cr-2026-10-23`. Statement verbatim from `section.tex` (ll. 1078–1099):
```latex
\begin{lemma}[Residual derivatives]\label{lem:app-dyn-derivative}
In the setting of \cref{lem:app-de-deletion}, let $\mathsf h=\varpi d$ with
$\varpi\in[0,1]$, and regard the coefficients \cref{eqn:app-de-coefficients}
as functions of $d$ with $M_0,\mathsf u,\mathsf v$ fixed. Then
\begin{equation}\label{eqn:app-dyn-derivative}
\partial_d\alpha_1=\frac{\varpi\big[(1+\mathsf h\mathsf C)^2-s\mathsf h^2\mathsf U\mathsf V\big]}{\Lambda^2},\qquad
\partial_d\alpha_2=\frac{2\varpi\mathsf h\mathsf U(1+\mathsf h\mathsf C)}{\Lambda^2},\qquad
\partial_d\alpha_3=-\frac{2s\varpi\mathsf h\mathsf V(1+\mathsf h\mathsf C)}{\Lambda^2}.
\end{equation}
Let $N=N'+\varpi\sum_{a\le B}d_a\,\mathsf u_a\tensor\mathsf v_a$, where $N'$ and the
vectors $\mathsf u_a,\mathsf v_a$ do not depend on the scalars $d_a$, and for each
$a$ let the quantities of \cref{lem:app-de-deletion} be computed with
$(M_0,\mathsf h,\mathsf u,\mathsf v)=(N-\varpi d_a\mathsf u_a\tensor\mathsf v_a,\varpi d_a,\mathsf u_a,\mathsf v_a)$,
with a superscript $(a)$. Then for real $(e_a)_{a\le B}$,
\begin{equation}\label{eqn:app-dyn-DX}
\begin{aligned}
&\frac{\dif}{\dif\vartheta}\mathsf X_s\Big(N+\vartheta\varpi\sum_ae_a\mathsf u_a\tensor\mathsf v_a\Big)\Big|_{\vartheta=0}\\
&\qquad=\sum_ae_a\Big[\partial_d\alpha_3^{(a)}R_0^{(a)}(\mathsf u_a\tensor\mathsf u_a)\mathsf X_0^{(a)}+s\,\partial_d\alpha_1^{(a)}R_0^{(a)}(\mathsf u_a\tensor\mathsf v_a)\widetilde R_0^{(a)}\\
&\qquad\qquad-\partial_d\alpha_1^{(a)}\mathsf X_0^{(a)}(\mathsf v_a\tensor\mathsf u_a)\mathsf X_0^{(a)}-s\,\partial_d\alpha_2^{(a)}\mathsf X_0^{(a)}(\mathsf v_a\tensor\mathsf v_a)\widetilde R_0^{(a)}\Big].
\end{aligned}
\end{equation}
\end{lemma}
```
-/
theorem lem_app_dyn_derivative_ii {m n B : ℕ} (Np N : Mat m n) (ϖ s : ℝ) (u : Fin B → Vec m)
    (v : Fin B → Vec n) (d e : Fin B → ℝ) (hs : 0 < s) (hϖ : ϖ ∈ Icc (0 : ℝ) 1)
    (hN : N = Np + ϖ • ∑ a, d a • outer (u a) (v a)) :
    ∀ i j, HasDerivAt (fun θ : ℝ => Xs (N + (θ * ϖ) • ∑ a, e a • outer (u a) (v a)) s i j)
        (dXExpr N ϖ s d e u v i j) 0 := by
  intro i j
  set S : Mat m n := ∑ a, e a • outer (u a) (v a) with hS
  set T : Mat m n := ϖ • S with hT
  have hfun : (fun θ : ℝ => Xs (N + (θ * ϖ) • S) s i j) = fun θ : ℝ => Xs (N + θ • T) s i j := by
    funext θ; rw [hT, smul_smul]
  rw [hfun]
  refine (pe8_dX N T s hs i j).congr_deriv ?_
  let Φ : Mat m n →ₗ[ℝ] Mat m n :=
    { toFun := fun P => Rs N s * P - Rs N s * (P * Nᵀ + N * Pᵀ) * Rs N s * N
      map_add' := by
        intro P Q
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add]
        abel
      map_smul' := by
        intro c P
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul, smul_add, smul_sub,
          RingHom.id_apply]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub,
          smul_add] }
  have hlin : Rs N s * T - Rs N s * (T * Nᵀ + N * Tᵀ) * Rs N s * N =
      ∑ a, e a • (Rs N s * (ϖ • outer (u a) (v a))
        - Rs N s * ((ϖ • outer (u a) (v a)) * Nᵀ + N * (ϖ • outer (u a) (v a))ᵀ) * Rs N s * N) := by
    change Φ T = ∑ a, e a • Φ (ϖ • outer (u a) (v a))
    simp only [hT, hS, map_smul, map_sum, Finset.smul_sum, smul_comm ϖ]
  rw [hlin]
  unfold dXExpr
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pe8_one N (sampleMinor N ϖ d u v a) ϖ s (u a) (v a) (d a) hs hϖ rfl]

private lemma pe8_fX_deriv (x d : ℝ) (hx : 0 ≤ x) :
    deriv (fX x) d = (1 - x * d ^ 2) / (1 + x * d ^ 2) ^ 2 := by
  have hden : 1 + x * d ^ 2 ≠ 0 := by
    positivity
  have hn : HasDerivAt (fun y : ℝ => y) 1 d := hasDerivAt_id d
  have hd : HasDerivAt (fun y : ℝ => 1 + x * y ^ 2) (2 * x * d) d := by
    convert (hasDerivAt_const d 1).add ((hasDerivAt_pow 2 d).const_mul x) using 1 <;> ring
  have hq := hn.div hd hden
  rw [show fX x = fun y : ℝ => y / (1 + x * y ^ 2) by rfl]
  rw [show deriv (fun y : ℝ => y / (1 + x * y ^ 2)) d =
      (1 * (1 + x * d ^ 2) - d * (2 * x * d)) / (1 + x * d ^ 2) ^ 2 by
        exact hq.deriv]
  field_simp
  ring

private lemma pe8_psiX_deriv (x d : ℝ) (hx : 0 ≤ x) :
    deriv (psiX x) d = 2 * d / (1 + x * d ^ 2) ^ 2 := by
  have hden : 1 + x * d ^ 2 ≠ 0 := by
    positivity
  have hn : HasDerivAt (fun y : ℝ => y ^ 2) (2 * d) d := by
    simpa using hasDerivAt_pow 2 d
  have hd : HasDerivAt (fun y : ℝ => 1 + x * y ^ 2) (2 * x * d) d := by
    convert (hasDerivAt_const d 1).add ((hasDerivAt_pow 2 d).const_mul x) using 1 <;> ring
  have hq := hn.div hd hden
  rw [show psiX x = fun y : ℝ => y ^ 2 / (1 + x * y ^ 2) by rfl]
  rw [show deriv (fun y : ℝ => y ^ 2 / (1 + x * y ^ 2)) d =
      (2 * d * (1 + x * d ^ 2) - d ^ 2 * (2 * x * d)) / (1 + x * d ^ 2) ^ 2 by
        exact hq.deriv]
  field_simp
  ring

private lemma pe8_coeff_endpoint {m n : ℕ} (M0 : Mat m n) (ϖ s : ℝ)
    (u : Vec m) (v : Vec n) (d σ σt : ℝ) (hs : 0 < s) (hϖ : ϖ ∈ Icc (0 : ℝ) 1)
    (hσ : 0 ≤ σ) (hσt : 0 ≤ σt) (hU : delU M0 u s = σ)
    (hV : delV M0 v s = σt) (hC : delC M0 u v s = 0) :
    dAlpha1 M0 ϖ s u v d = ϖ * deriv (fX (ϖ ^ 2 * s * σ * σt)) d ∧
    dAlpha2 M0 ϖ s u v d = ϖ ^ 2 * σ * deriv (psiX (ϖ ^ 2 * s * σ * σt)) d ∧
    dAlpha3 M0 ϖ s u v d = -s * ϖ ^ 2 * σt * deriv (psiX (ϖ ^ 2 * s * σ * σt)) d := by
  have hx : 0 ≤ ϖ ^ 2 * s * σ * σt := by positivity
  obtain ⟨hd1, hd2, hd3⟩ := lem_app_dyn_derivative_i M0 ϖ s u v hs hϖ d
  have e1 := hd1.deriv
  have e2 := hd2.deriv
  have e3 := hd3.deriv
  unfold dAlpha1 dAlpha2 dAlpha3
  rw [e1, e2, e3, pe8_fX_deriv _ _ hx, pe8_psiX_deriv _ _ hx, hU, hV, hC]
  unfold delLambda
  rw [hU, hV, hC]
  simp only [mul_zero, add_zero, one_pow]
  have heq : 1 + s * (ϖ * d) ^ 2 * σ * σt = 1 + (ϖ ^ 2 * s * σ * σt) * d ^ 2 := by ring
  rw [heq]
  have hD : ((1 + (ϖ ^ 2 * s * σ * σt) * d ^ 2) ^ 2) ≠ 0 := by positivity
  constructor
  · field_simp [hD]
  constructor
  · field_simp [hD]
  · field_simp [hD]

private lemma pe8_std_fst {m n : ℕ} :
    Muon.External.IsStdGaussianVector (gaussPair m n) (Prod.fst : Vec m × Vec n → Vec m) := by
  unfold Muon.External.IsStdGaussianVector gaussPair Muon.Foundations.stdGaussianPi
  simp

private lemma pe8_std_snd {m n : ℕ} :
    Muon.External.IsStdGaussianVector (gaussPair m n) (Prod.snd : Vec m × Vec n → Vec n) := by
  unfold Muon.External.IsStdGaussianVector gaussPair Muon.Foundations.stdGaussianPi
  simp

private lemma pe8_sqrt_symm {k : ℕ} (S : Mat k k) :
    (CFC.sqrt S).transpose = CFC.sqrt S := by
  have h : (CFC.sqrt S)ᴴ = CFC.sqrt S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).isHermitian
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

private lemma pe8_quad_alg {k : ℕ} (r R : Mat k k) (hr : r.transpose = r)
    (c : ℝ) (ζ : Vec k) :
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
  rw [h1]
  ring

private lemma pe8_quad_trace {k l : ℕ} (Sg : Mat k k) (hS : Sg.PosSemidef)
    (B : ℕ) (hB : 0 < B) (s : ℝ) (M : Mat k l) :
    (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
        (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg)).trace =
      (B : ℝ)⁻¹ * (Sg * Rs M s).trace := by
  have hsq : CFC.sqrt Sg * CFC.sqrt Sg = Sg :=
    CFC.sqrt_mul_sqrt_self Sg (Matrix.nonneg_iff_posSemidef.mpr hS)
  rw [Matrix.trace_smul, smul_eq_mul,
    Matrix.trace_mul_comm (CFC.sqrt Sg * Rs M s) (CFC.sqrt Sg),
    ← Matrix.mul_assoc, hsq]
  congr 1
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg B)]

private lemma pe8_U_certificate (cert : Muon.External.GaussianQuadFormLp)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ Cp : ℝ, ∀ {m n : ℕ} (Cv : Covariances m n) (B : ℕ)
    (hB : 0 < B) (M0 : Mat m n) (s : ℝ),
      eLpNorm (fun z : Vec m × Vec n =>
          delU M0 (sampU Cv B z) s - sigmaS Cv B M0 s)
          (ENNReal.ofReal p) (gaussPair m n) ≤
        ENNReal.ofReal (Cp * Muon.External.frobNorm
          (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
            (CFC.sqrt Cv.Sout * Rs M0 s * CFC.sqrt Cv.Sout))) := by
  obtain ⟨Cp, hCp⟩ := cert.holds p hp
  refine ⟨Cp, fun {m n} Cv B hB M0 s => ?_⟩
  have h := hCp m (Vec m × Vec n) (gaussPair m n)
    (Prod.fst : Vec m × Vec n → Vec m) pe8_std_fst
    (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
      (CFC.sqrt Cv.Sout * Rs M0 s * CFC.sqrt Cv.Sout))
  have hfun : (fun z : Vec m × Vec n =>
      delU M0 (sampU Cv B z) s - sigmaS Cv B M0 s) =
      (fun z : Vec m × Vec n => dotProduct z.1
        ((((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
          (CFC.sqrt Cv.Sout * Rs M0 s * CFC.sqrt Cv.Sout)) *ᵥ z.1) -
        (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
          (CFC.sqrt Cv.Sout * Rs M0 s * CFC.sqrt Cv.Sout)).trace) := by
    funext z
    unfold delU sampU sigmaS rOut
    rw [pe8_quad_alg _ _ (pe8_sqrt_symm Cv.Sout)]
    rw [pe8_quad_trace Cv.Sout Cv.psdOut B hB s M0]
  rwa [hfun]

private lemma pe8_V_certificate (cert : Muon.External.GaussianQuadFormLp)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ Cp : ℝ, ∀ {m n : ℕ} (Cv : Covariances m n) (B : ℕ)
    (hB : 0 < B) (M0 : Mat m n) (s : ℝ),
      eLpNorm (fun z : Vec m × Vec n =>
          delV M0 (sampV Cv B z) s - sigmaT Cv B M0 s)
          (ENNReal.ofReal p) (gaussPair m n) ≤
        ENNReal.ofReal (Cp * Muon.External.frobNorm
          (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
            (CFC.sqrt Cv.Sin * Rts M0 s * CFC.sqrt Cv.Sin))) := by
  obtain ⟨Cp, hCp⟩ := cert.holds p hp
  refine ⟨Cp, fun {m n} Cv B hB M0 s => ?_⟩
  have h := hCp n (Vec m × Vec n) (gaussPair m n)
    (Prod.snd : Vec m × Vec n → Vec n) pe8_std_snd
    (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
      (CFC.sqrt Cv.Sin * Rts M0 s * CFC.sqrt Cv.Sin))
  have hfun : (fun z : Vec m × Vec n =>
      delV M0 (sampV Cv B z) s - sigmaT Cv B M0 s) =
      (fun z : Vec m × Vec n => dotProduct z.2
        ((((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
          (CFC.sqrt Cv.Sin * Rts M0 s * CFC.sqrt Cv.Sin)) *ᵥ z.2) -
        (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
          (CFC.sqrt Cv.Sin * Rts M0 s * CFC.sqrt Cv.Sin)).trace) := by
    funext z
    unfold delV sampV sigmaT rIn
    rw [pe8_quad_alg _ _ (pe8_sqrt_symm Cv.Sin)]
    have hrt : Rts M0 s = Rs M0ᵀ s := by
      unfold Rts Rs
      rw [Matrix.transpose_transpose]
    rw [hrt, pe8_quad_trace Cv.Sin Cv.psdIn B hB s M0ᵀ]
  rwa [hfun]

private lemma pe8_opNorm_nonneg {a b : ℕ} (A : Mat a b) : 0 ≤ opNorm A := by
  unfold opNorm
  positivity

private lemma pe8_sum_sq_mulVec_le {a b : ℕ} (T : Mat a b) (y : Fin b → ℝ) :
    ∑ k, (T *ᵥ y) k ^ 2 ≤ opNorm T ^ 2 * ∑ i, y i ^ 2 := by
  have hb : ‖Matrix.toEuclideanLin T (WithLp.toLp 2 y)‖ ≤
      opNorm T * ‖WithLp.toLp 2 y‖ :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin T)).le_opNorm (WithLp.toLp 2 y)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)] at hsq
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Real.norm_eq_abs, sq_abs] using hsq

private lemma pe8_fro_sq_le {a b : ℕ} (A : Mat a b) :
    ∑ i, ∑ j, A i j ^ 2 ≤ (b : ℝ) * opNorm A ^ 2 := by
  classical
  have hcol : ∀ j : Fin b, ∑ i, A i j ^ 2 ≤ opNorm A ^ 2 := by
    intro j
    have h := pe8_sum_sq_mulVec_le A (Pi.single j 1)
    have e1 : ∀ i, (A *ᵥ (Pi.single j (1 : ℝ))) i = A i j := fun i => by
      simp [Matrix.mulVec_single_one]
    have e2 : ∑ i, (Pi.single j (1 : ℝ) : Fin b → ℝ) i ^ 2 = 1 := by
      simp [Pi.single_apply]
    simpa [e1, e2] using h
  rw [Finset.sum_comm]
  calc
    ∑ j, ∑ i, A i j ^ 2 ≤ ∑ _j : Fin b, opNorm A ^ 2 :=
      Finset.sum_le_sum fun j _ => hcol j
    _ = (b : ℝ) * opNorm A ^ 2 := by simp

open scoped Matrix.Norms.L2Operator in
private lemma pe8_opNorm_mul_le {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B

open scoped Matrix.Norms.L2Operator in
private lemma pe8_opNorm_sqrt_mul_self {a : ℕ} (S : Mat a a) (hS : S.PosSemidef) :
    opNorm (CFC.sqrt S) * opNorm (CFC.sqrt S) = opNorm S := by
  have hh : (CFC.sqrt S)ᴴ = CFC.sqrt S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).isHermitian
  have hsq : CFC.sqrt S * CFC.sqrt S = S :=
    CFC.sqrt_mul_sqrt_self S (Matrix.nonneg_iff_posSemidef.mpr hS)
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (CFC.sqrt S)
  rw [hh, hsq] at h
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact h.symm

open scoped Matrix.Norms.L2Operator in
private lemma pe8_opNorm_smul {a b : ℕ} (c : ℝ) (A : Mat a b) :
    opNorm (c • A) = |c| * opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma pe8_certificate_matrix_sq {k l : ℕ} (Sg : Mat k k) (hS : Sg.PosSemidef)
    (CS : ℝ) (hC : opNorm Sg ≤ CS) (B : ℕ) (hB : 0 < B) (s : ℝ) (hs : 0 < s)
    (M : Mat k l) :
    ∑ i, ∑ j, ((((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
        (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg)) i j) ^ 2 ≤
      (k : ℝ) * (CS / (s * B)) ^ 2 := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hr := pe8_opNorm_sqrt_mul_self Sg hS
  have hC0 : 0 ≤ CS := (pe8_opNorm_nonneg Sg).trans hC
  have hR := (lem_app_de_resolvent M s hs).1
  have h1 : opNorm (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg) ≤ CS * (1 / s) := by
    calc
      opNorm (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg)
          ≤ opNorm (CFC.sqrt Sg * Rs M s) * opNorm (CFC.sqrt Sg) := pe8_opNorm_mul_le _ _
      _ ≤ (opNorm (CFC.sqrt Sg) * opNorm (Rs M s)) * opNorm (CFC.sqrt Sg) :=
        mul_le_mul_of_nonneg_right (pe8_opNorm_mul_le _ _) (pe8_opNorm_nonneg _)
      _ = (opNorm (CFC.sqrt Sg) * opNorm (CFC.sqrt Sg)) * opNorm (Rs M s) := by ring
      _ ≤ CS * (1 / s) := by
        rw [hr]
        exact mul_le_mul hC hR (pe8_opNorm_nonneg _) hC0
  have h2 : opNorm (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
      (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg)) ≤ CS / (s * B) := by
    rw [pe8_opNorm_smul, abs_of_nonneg (by positivity)]
    calc
      (Real.sqrt (B : ℝ))⁻¹ ^ 2 * opNorm (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg)
          ≤ (Real.sqrt (B : ℝ))⁻¹ ^ 2 * (CS * (1 / s)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = CS / (s * B) := by
        rw [inv_pow, Real.sq_sqrt hBr.le]
        field_simp
  calc
    ∑ i, ∑ j, ((((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
        (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg)) i j) ^ 2
        ≤ (k : ℝ) * opNorm (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
          (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg)) ^ 2 := pe8_fro_sq_le _
    _ ≤ (k : ℝ) * (CS / (s * B)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pe8_opNorm_nonneg _) h2 2)
        (Nat.cast_nonneg k)

private lemma pe8_sqrt_fro_scale (k B γ CS s s0 : ℝ) (hB : 0 < B) (hk : k ≤ γ * B)
    (hk0 : 0 ≤ k) (hCS : 0 ≤ CS) (hs0 : 0 < s0) (hs : s0 ≤ s) :
    Real.sqrt (k * (CS / (s * B)) ^ 2) ≤ Real.sqrt γ * CS / s0 / Real.sqrt B := by
  have hγ : 0 ≤ γ := by
    by_contra h
    push Not at h
    nlinarith
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp only [div_pow, mul_pow, Real.sq_sqrt hB.le, Real.sq_sqrt hγ]
  have h1 : k * (CS ^ 2 / (s ^ 2 * B ^ 2)) ≤
      γ * B * (CS ^ 2 / (s ^ 2 * B ^ 2)) :=
    mul_le_mul_of_nonneg_right hk (by positivity)
  refine h1.trans ?_
  have e1 : γ * B * (CS ^ 2 / (s ^ 2 * B ^ 2)) = γ * CS ^ 2 / (s ^ 2 * B) := by
    field_simp
  rw [e1, div_div]
  have hsq : s0 ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hs0.le hs 2
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_right hsq hB.le)

private lemma pe8_certificate_matrix_frob {k l : ℕ} (Sg : Mat k k) (hS : Sg.PosSemidef)
    (CS γ : ℝ) (hC : opNorm Sg ≤ CS) (B : ℕ) (hB : 0 < B) (hk : (k : ℝ) ≤ γ * B)
    (s s0 : ℝ) (hs0 : 0 < s0) (hs : s0 ≤ s) (M : Mat k l) :
    Muon.External.frobNorm (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
        (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg)) ≤
      Real.sqrt γ * CS / s0 / Real.sqrt B := by
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCS : 0 ≤ CS := (pe8_opNorm_nonneg Sg).trans hC
  unfold Muon.External.frobNorm
  calc
    Real.sqrt (∑ i, ∑ j, ((((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
        (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg)) i j) ^ 2)
        ≤ Real.sqrt ((k : ℝ) * (CS / (s * B)) ^ 2) :=
      Real.sqrt_le_sqrt (pe8_certificate_matrix_sq Sg hS CS hC B hB s hspos M)
    _ ≤ Real.sqrt γ * CS / s0 / Real.sqrt B :=
      pe8_sqrt_fro_scale k B γ CS s s0 hBr hk (Nat.cast_nonneg k) hCS hs0 hs

private lemma pe8_U_concentration (cert : Muon.External.GaussianQuadFormLp) (pe : ℕ)
    (hpe : 1 ≤ pe) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s0 : ℝ) (hs0 : 0 < s0) (γ CS : ℝ) {m n : ℕ}
    (Cv : Covariances m n) (B : ℕ) (hB : 0 < B) (M0 : Mat m n) (s : ℝ)
    (hCo : opNorm Cv.Sout ≤ CS) (hm : (m : ℝ) ≤ γ * B) (hs : s0 ≤ s),
      eLpNorm (fun z : Vec m × Vec n =>
          delU M0 (sampU Cv B z) s - sigmaS Cv B M0 s)
          (pe : ℝ≥0∞) (gaussPair m n) ≤
        ENNReal.ofReal (K * Real.sqrt γ * CS / s0 / Real.sqrt B) := by
  have hp : (1 : ℝ) ≤ pe := by exact_mod_cast hpe
  obtain ⟨Cp, hcert'⟩ := pe8_U_certificate cert pe hp
  let K : ℝ := max 0 Cp
  refine ⟨K, le_max_left _ _, ?_⟩
  intro s0 hs0 γ CS m n Cv B hB M0 s hCo hm hs
  have hcert := hcert' Cv B hB M0 s
  have hf := pe8_certificate_matrix_frob Cv.Sout Cv.psdOut CS γ hCo B hB hm s s0 hs0 hs M0
  have hfnn : 0 ≤ Muon.External.frobNorm (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
      (CFC.sqrt Cv.Sout * Rs M0 s * CFC.sqrt Cv.Sout)) := by
    unfold Muon.External.frobNorm
    positivity
  have hK : Cp ≤ K := le_max_right _ _
  calc
    eLpNorm (fun z : Vec m × Vec n =>
        delU M0 (sampU Cv B z) s - sigmaS Cv B M0 s)
        (pe : ℝ≥0∞) (gaussPair m n)
        ≤ ENNReal.ofReal (Cp * Muon.External.frobNorm (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
          (CFC.sqrt Cv.Sout * Rs M0 s * CFC.sqrt Cv.Sout))) := by simpa using hcert
    _ ≤ ENNReal.ofReal (K * Real.sqrt γ * CS / s0 / Real.sqrt B) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        Cp * Muon.External.frobNorm (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
            (CFC.sqrt Cv.Sout * Rs M0 s * CFC.sqrt Cv.Sout))
            ≤ K * Muon.External.frobNorm (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
              (CFC.sqrt Cv.Sout * Rs M0 s * CFC.sqrt Cv.Sout)) :=
          mul_le_mul_of_nonneg_right hK hfnn
        _ ≤ K * (Real.sqrt γ * CS / s0 / Real.sqrt B) :=
          mul_le_mul_of_nonneg_left hf (le_max_left _ _)
        _ = K * Real.sqrt γ * CS / s0 / Real.sqrt B := by ring

private lemma pe8_V_concentration (cert : Muon.External.GaussianQuadFormLp) (pe : ℕ)
    (hpe : 1 ≤ pe) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s0 : ℝ) (hs0 : 0 < s0) (γ CS : ℝ) {m n : ℕ}
    (Cv : Covariances m n) (B : ℕ) (hB : 0 < B) (M0 : Mat m n) (s : ℝ)
    (hCi : opNorm Cv.Sin ≤ CS) (hn : (n : ℝ) ≤ γ * B) (hs : s0 ≤ s),
      eLpNorm (fun z : Vec m × Vec n =>
          delV M0 (sampV Cv B z) s - sigmaT Cv B M0 s)
          (pe : ℝ≥0∞) (gaussPair m n) ≤
        ENNReal.ofReal (K * Real.sqrt γ * CS / s0 / Real.sqrt B) := by
  have hp : (1 : ℝ) ≤ pe := by exact_mod_cast hpe
  obtain ⟨Cp, hcert'⟩ := pe8_V_certificate cert pe hp
  let K : ℝ := max 0 Cp
  refine ⟨K, le_max_left _ _, ?_⟩
  intro s0 hs0 γ CS m n Cv B hB M0 s hCi hn hs
  have hcert := hcert' Cv B hB M0 s
  have hrt : Rts M0 s = Rs M0ᵀ s := by
    unfold Rts Rs
    rw [Matrix.transpose_transpose]
  have hf := pe8_certificate_matrix_frob Cv.Sin Cv.psdIn CS γ hCi B hB hn s s0 hs0 hs M0ᵀ
  rw [← hrt] at hf
  have hfnn : 0 ≤ Muon.External.frobNorm (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
      (CFC.sqrt Cv.Sin * Rts M0 s * CFC.sqrt Cv.Sin)) := by
    unfold Muon.External.frobNorm
    positivity
  have hK : Cp ≤ K := le_max_right _ _
  calc
    eLpNorm (fun z : Vec m × Vec n =>
        delV M0 (sampV Cv B z) s - sigmaT Cv B M0 s)
        (pe : ℝ≥0∞) (gaussPair m n)
        ≤ ENNReal.ofReal (Cp * Muon.External.frobNorm (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
          (CFC.sqrt Cv.Sin * Rts M0 s * CFC.sqrt Cv.Sin))) := by simpa using hcert
    _ ≤ ENNReal.ofReal (K * Real.sqrt γ * CS / s0 / Real.sqrt B) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        Cp * Muon.External.frobNorm (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
            (CFC.sqrt Cv.Sin * Rts M0 s * CFC.sqrt Cv.Sin))
            ≤ K * Muon.External.frobNorm (((Real.sqrt (B : ℝ))⁻¹ ^ 2) •
              (CFC.sqrt Cv.Sin * Rts M0 s * CFC.sqrt Cv.Sin)) :=
          mul_le_mul_of_nonneg_right hK hfnn
        _ ≤ K * (Real.sqrt γ * CS / s0 / Real.sqrt B) :=
          mul_le_mul_of_nonneg_left hf (le_max_left _ _)
        _ = K * Real.sqrt γ * CS / s0 / Real.sqrt B := by ring

private lemma pe8_dilation_quad {m n : ℕ} (A : Mat m n) (z : Vec m × Vec n)
    (glue : (Vec m × Vec n) → Vec (m + n))
    (hleft : ∀ z i, glue z (Fin.castAdd n i) = z.1 i)
    (hright : ∀ z j, glue z (Fin.natAdd m j) = z.2 j) :
    dotProduct (glue z)
        (((1 / 2 : ℝ) • Muon.Foundations.hermDilation A) *ᵥ glue z) =
      dotProduct z.1 (A *ᵥ z.2) := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_add, Finset.mul_sum,
    Matrix.smul_apply, smul_eq_mul, Muon.Foundations.hermDilation, Matrix.reindex_apply,
    Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply, Matrix.zero_apply,
    hleft, hright, zero_mul, mul_zero, Finset.sum_const_zero, zero_add,
    add_zero]
  rw [Finset.sum_comm (f := fun j i => z.2 j * (1 / 2 * A i j * z.1 i))]
  have hleft : (∑ i, ∑ j, z.1 i * (1 / 2 * A i j * z.2 j)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, z.1 i * (A i j * z.2 j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hright : (∑ i, ∑ j, z.2 j * (1 / 2 * A i j * z.1 i)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, z.1 i * (A i j * z.2 j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hleft, hright]
  ring

private lemma pe8_dilation_trace {m n : ℕ} (A : Mat m n) :
    (((1 / 2 : ℝ) • Muon.Foundations.hermDilation A)).trace = 0 := by
  simp [Matrix.trace, Muon.Foundations.hermDilation, Fin.sum_univ_add]

private lemma pe8_bil_alg {m n : ℕ} (r1 : Mat m m) (r2 : Mat n n) (X : Mat m n)
    (h1 : r1.transpose = r1) (c : ℝ) (z : Vec m) (w : Vec n) :
    dotProduct (c • (r1 *ᵥ z)) (X *ᵥ (c • (r2 *ᵥ w))) =
      dotProduct z (((c * c) • (r1 * X * r2)) *ᵥ w) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, Matrix.smul_mulVec,
    dotProduct_smul]
  simp only [smul_eq_mul]
  have key : ∀ (x y : Vec m), dotProduct (r1 *ᵥ x) y = dotProduct x (r1 *ᵥ y) := by
    intro x y
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h1,
      dotProduct_comm]
  rw [key, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  ring

private lemma pe8_C_certificate (cert : Muon.External.GaussianQuadFormLp)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ Cp : ℝ, ∀ {m n : ℕ} (Cv : Covariances m n) (B : ℕ)
    (M0 : Mat m n) (s : ℝ),
      eLpNorm (fun z : Vec m × Vec n => delC M0 (sampU Cv B z) (sampV Cv B z) s)
          (ENNReal.ofReal p) (gaussPair m n) ≤
        ENNReal.ofReal (Cp * Muon.External.frobNorm
          ((1 / 2 : ℝ) • Muon.Foundations.hermDilation
            (((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹) •
              (CFC.sqrt Cv.Sout * Xs M0 s * CFC.sqrt Cv.Sin)))) := by
  obtain ⟨Cp, hCp⟩ := cert.holds p hp
  refine ⟨Cp, fun {m n} Cv B M0 s => ?_⟩
  let A : Mat m n := (((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹) •
    (CFC.sqrt Cv.Sout * Xs M0 s * CFC.sqrt Cv.Sin))
  let glue : (Vec m × Vec n) ≃ᵐ Vec (m + n) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (m + n) => ℝ) finSumFinEquiv)
  have hleft : ∀ (z : Vec m × Vec n) (i : Fin m),
      glue z (Fin.castAdd n i) = z.1 i := by
    intro z i
    rw [← finSumFinEquiv_apply_left]
    change (Equiv.piCongrLeft (fun _ : Fin (m + n) => ℝ) finSumFinEquiv)
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)).symm z)
      (finSumFinEquiv (Sum.inl i)) = z.1 i
    rw [Equiv.piCongrLeft_apply_apply]
    rfl
  have hright : ∀ (z : Vec m × Vec n) (j : Fin n),
      glue z (Fin.natAdd m j) = z.2 j := by
    intro z j
    rw [← finSumFinEquiv_apply_right]
    change (Equiv.piCongrLeft (fun _ : Fin (m + n) => ℝ) finSumFinEquiv)
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)).symm z)
      (finSumFinEquiv (Sum.inr j)) = z.2 j
    rw [Equiv.piCongrLeft_apply_apply]
    rfl
  have hstd : Muon.External.IsStdGaussianVector (gaussPair m n) glue := by
    unfold Muon.External.IsStdGaussianVector
    exact ((measurePreserving_sumPiEquivProdPi_symm
        (fun _ : Fin m ⊕ Fin n => gaussianReal 0 1)).trans
      (measurePreserving_piCongrLeft (α := fun _ : Fin (m + n) => ℝ)
        (fun _ => gaussianReal 0 1) finSumFinEquiv)).map_eq
  have h := hCp (m + n) (Vec m × Vec n) (gaussPair m n) glue hstd
    ((1 / 2 : ℝ) • Muon.Foundations.hermDilation A)
  have hfun : (fun z : Vec m × Vec n =>
      delC M0 (sampU Cv B z) (sampV Cv B z) s) =
      (fun z : Vec m × Vec n => dotProduct (glue z)
        (((1 / 2 : ℝ) • Muon.Foundations.hermDilation A) *ᵥ glue z) -
        (((1 / 2 : ℝ) • Muon.Foundations.hermDilation A)).trace) := by
    funext z
    rw [pe8_dilation_quad A z glue hleft hright, pe8_dilation_trace, sub_zero]
    unfold delC sampU sampV rOut rIn A
    exact pe8_bil_alg _ _ _ (pe8_sqrt_symm Cv.Sout) _ _ _
  rwa [hfun]

private lemma pe8_frobNorm_eq_fro {k : ℕ} (A : Mat k k) :
    Muon.External.frobNorm A = fro A := by
  unfold Muon.External.frobNorm fro
  congr 2
  simp only [Real.norm_eq_abs, sq_abs]

open scoped Matrix.Norms.Frobenius in
private lemma pe8_fro_smul {m n : ℕ} (c : ℝ) (A : Mat m n) :
    fro (c • A) = |c| * fro A := by
  rw [fro_eq_norm, fro_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma pe8_dilation_frob_le {m n : ℕ} (A : Mat m n) :
    Muon.External.frobNorm ((1 / 2 : ℝ) • Muon.Foundations.hermDilation A) ≤ fro A := by
  rw [pe8_frobNorm_eq_fro, pe8_fro_smul, abs_of_nonneg (by norm_num)]
  have hsq := Muon.Foundations.fro_hermDilation A
  have hA : 0 ≤ fro A := by unfold fro; positivity
  have hD : 0 ≤ fro (Muon.Foundations.hermDilation A) := by unfold fro; positivity
  nlinarith [sq_nonneg (fro (Muon.Foundations.hermDilation A) - 2 * fro A)]

private lemma pe8_sqrt_cross_scale (n B γ CS s s0 : ℝ) (hB : 0 < B)
    (hn : n ≤ γ * B) (hn0 : 0 ≤ n) (hCS : 0 ≤ CS) (hs0 : 0 < s0)
    (hs : s0 ≤ s) :
    Real.sqrt (n * (CS / (2 * Real.sqrt s * B)) ^ 2) ≤
      CS * Real.sqrt γ / (2 * Real.sqrt s0) / Real.sqrt B := by
  have hγ : 0 ≤ γ := by
    by_contra h
    push Not at h
    nlinarith
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  have hs0' : 0 < Real.sqrt s0 := Real.sqrt_pos.mpr hs0
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp only [div_pow, mul_pow, Real.sq_sqrt hB.le, Real.sq_sqrt hγ,
    Real.sq_sqrt hs0.le, Real.sq_sqrt hspos.le]
  have h1 : n * (CS ^ 2 / (2 ^ 2 * s * B ^ 2)) ≤
      γ * B * (CS ^ 2 / (2 ^ 2 * s * B ^ 2)) :=
    mul_le_mul_of_nonneg_right hn (by positivity)
  refine h1.trans ?_
  have e1 : γ * B * (CS ^ 2 / (2 ^ 2 * s * B ^ 2)) =
      γ * CS ^ 2 / (4 * s * B) := by field_simp; ring
  have e2 : CS ^ 2 * γ / (2 ^ 2 * s0) / B =
      γ * CS ^ 2 / (4 * s0 * B) := by field_simp; ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hB.le)

private lemma pe8_cross_matrix_frob {m n : ℕ} (Cv : Covariances m n) (CS γ : ℝ)
    (hCo : opNorm Cv.Sout ≤ CS) (hCi : opNorm Cv.Sin ≤ CS)
    (B : ℕ) (hB : 0 < B) (hn : (n : ℝ) ≤ γ * B) (M0 : Mat m n)
    (s s0 : ℝ) (hs0 : 0 < s0) (hs : s0 ≤ s) :
    fro ((((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹) •
        (CFC.sqrt Cv.Sout * Xs M0 s * CFC.sqrt Cv.Sin))) ≤
      CS * Real.sqrt γ / (2 * Real.sqrt s0) / Real.sqrt B := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hCS : 0 ≤ CS := (pe8_opNorm_nonneg Cv.Sout).trans hCo
  have e1 := pe8_opNorm_sqrt_mul_self Cv.Sout Cv.psdOut
  have e2 := pe8_opNorm_sqrt_mul_self Cv.Sin Cv.psdIn
  have hX := (lem_app_de_resolvent M0 s hspos).2.2.1
  have hab : opNorm (CFC.sqrt Cv.Sout) * opNorm (CFC.sqrt Cv.Sin) ≤ CS := by
    have ha := pe8_opNorm_nonneg (CFC.sqrt Cv.Sout)
    have hb := pe8_opNorm_nonneg (CFC.sqrt Cv.Sin)
    have hsq : (opNorm (CFC.sqrt Cv.Sout) * opNorm (CFC.sqrt Cv.Sin)) ^ 2 ≤ CS ^ 2 := by
      calc
        (opNorm (CFC.sqrt Cv.Sout) * opNorm (CFC.sqrt Cv.Sin)) ^ 2 =
            (opNorm (CFC.sqrt Cv.Sout) * opNorm (CFC.sqrt Cv.Sout)) *
              (opNorm (CFC.sqrt Cv.Sin) * opNorm (CFC.sqrt Cv.Sin)) := by ring
        _ ≤ CS * CS := by
          rw [e1, e2]
          exact mul_le_mul hCo hCi (pe8_opNorm_nonneg _) hCS
        _ = CS ^ 2 := by ring
    exact le_of_sq_le_sq hsq hCS |> fun h => by nlinarith [mul_nonneg ha hb]
  let A : Mat m n := (((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹) •
    (CFC.sqrt Cv.Sout * Xs M0 s * CFC.sqrt Cv.Sin))
  have hop0 : opNorm (CFC.sqrt Cv.Sout * Xs M0 s * CFC.sqrt Cv.Sin) ≤
      CS * (1 / (2 * Real.sqrt s)) := by
    calc
      opNorm (CFC.sqrt Cv.Sout * Xs M0 s * CFC.sqrt Cv.Sin)
          ≤ opNorm (CFC.sqrt Cv.Sout * Xs M0 s) * opNorm (CFC.sqrt Cv.Sin) :=
        pe8_opNorm_mul_le _ _
      _ ≤ (opNorm (CFC.sqrt Cv.Sout) * opNorm (Xs M0 s)) *
          opNorm (CFC.sqrt Cv.Sin) :=
        mul_le_mul_of_nonneg_right (pe8_opNorm_mul_le _ _) (pe8_opNorm_nonneg _)
      _ ≤ (opNorm (CFC.sqrt Cv.Sout) * (1 / (2 * Real.sqrt s))) *
          opNorm (CFC.sqrt Cv.Sin) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hX (pe8_opNorm_nonneg _)) (pe8_opNorm_nonneg _)
      _ = (opNorm (CFC.sqrt Cv.Sout) * opNorm (CFC.sqrt Cv.Sin)) *
          (1 / (2 * Real.sqrt s)) := by ring
      _ ≤ CS * (1 / (2 * Real.sqrt s)) :=
        mul_le_mul_of_nonneg_right hab (by positivity)
  have hop : opNorm A ≤ CS / (2 * Real.sqrt s * B) := by
    unfold A
    rw [pe8_opNorm_smul, abs_of_nonneg (by positivity)]
    calc
      (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ *
          opNorm (CFC.sqrt Cv.Sout * Xs M0 s * CFC.sqrt Cv.Sin)
          ≤ (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ *
            (CS * (1 / (2 * Real.sqrt s))) :=
        mul_le_mul_of_nonneg_left hop0 (by positivity)
      _ = CS / (2 * Real.sqrt s * B) := by
        have hsq : (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ = (B : ℝ)⁻¹ := by
          rw [← mul_inv, Real.mul_self_sqrt hBr.le]
        rw [hsq]
        field_simp
  unfold fro
  calc
    Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) = Real.sqrt (∑ i, ∑ j, A i j ^ 2) := by
      congr 2
      simp only [Real.norm_eq_abs, sq_abs]
    _ ≤ Real.sqrt ((n : ℝ) * (CS / (2 * Real.sqrt s * B)) ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact (pe8_fro_sq_le A).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pe8_opNorm_nonneg A) hop 2)
          (Nat.cast_nonneg n))
    _ ≤ CS * Real.sqrt γ / (2 * Real.sqrt s0) / Real.sqrt B :=
      pe8_sqrt_cross_scale n B γ CS s s0 hBr hn (Nat.cast_nonneg n) hCS hs0 hs

private lemma pe8_C_concentration (cert : Muon.External.GaussianQuadFormLp) (pe : ℕ)
    (hpe : 1 ≤ pe) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s0 : ℝ) (hs0 : 0 < s0) (γ CS : ℝ) {m n : ℕ}
    (Cv : Covariances m n) (B : ℕ) (hB : 0 < B) (M0 : Mat m n) (s : ℝ)
    (hCo : opNorm Cv.Sout ≤ CS) (hCi : opNorm Cv.Sin ≤ CS)
    (hn : (n : ℝ) ≤ γ * B) (hs : s0 ≤ s),
      eLpNorm (fun z : Vec m × Vec n => delC M0 (sampU Cv B z) (sampV Cv B z) s)
          (pe : ℝ≥0∞) (gaussPair m n) ≤
        ENNReal.ofReal
          (K * (CS * Real.sqrt γ / (2 * Real.sqrt s0)) / Real.sqrt B) := by
  have hp : (1 : ℝ) ≤ pe := by exact_mod_cast hpe
  obtain ⟨Cp, hcert'⟩ := pe8_C_certificate cert pe hp
  let K : ℝ := max 0 Cp
  refine ⟨K, le_max_left _ _, ?_⟩
  intro s0 hs0 γ CS m n Cv B hB M0 s hCo hCi hn hs
  have hcert := hcert' Cv B M0 s
  let A : Mat m n := (((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹) •
    (CFC.sqrt Cv.Sout * Xs M0 s * CFC.sqrt Cv.Sin))
  have hfA := pe8_cross_matrix_frob Cv CS γ hCo hCi B hB hn M0 s s0 hs0 hs
  change fro A ≤ _ at hfA
  have hf : Muon.External.frobNorm
      ((1 / 2 : ℝ) • Muon.Foundations.hermDilation A) ≤
      CS * Real.sqrt γ / (2 * Real.sqrt s0) / Real.sqrt B :=
    (pe8_dilation_frob_le A).trans hfA
  have hfnn : 0 ≤ Muon.External.frobNorm
      ((1 / 2 : ℝ) • Muon.Foundations.hermDilation A) := by
    unfold Muon.External.frobNorm
    positivity
  have hK : Cp ≤ K := le_max_right _ _
  calc
    eLpNorm (fun z : Vec m × Vec n => delC M0 (sampU Cv B z) (sampV Cv B z) s)
        (pe : ℝ≥0∞) (gaussPair m n) ≤
        ENNReal.ofReal (Cp * Muon.External.frobNorm
          ((1 / 2 : ℝ) • Muon.Foundations.hermDilation A)) := by simpa [A] using hcert
    _ ≤ ENNReal.ofReal
        (K * (CS * Real.sqrt γ / (2 * Real.sqrt s0)) / Real.sqrt B) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        Cp * Muon.External.frobNorm
            ((1 / 2 : ℝ) • Muon.Foundations.hermDilation A) ≤
            K * Muon.External.frobNorm
              ((1 / 2 : ℝ) • Muon.Foundations.hermDilation A) :=
          mul_le_mul_of_nonneg_right hK hfnn
        _ ≤ K * (CS * Real.sqrt γ / (2 * Real.sqrt s0) / Real.sqrt B) :=
          mul_le_mul_of_nonneg_left hf (le_max_left _ _)
        _ = K * (CS * Real.sqrt γ / (2 * Real.sqrt s0)) / Real.sqrt B := by ring

private lemma pe8_delU_nonneg {m n : ℕ} (M : Mat m n) (u : Vec m) (s : ℝ)
    (hs : 0 < s) : 0 ≤ delU M u s := by
  have hpsd : (Rs M s).PosSemidef := by
    unfold Rs
    refine Matrix.PosSemidef.inv ?_
    have hMM : (M * Mᵀ).PosSemidef := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_self_mul_conjTranspose M
    exact hMM.add (Matrix.PosSemidef.one.smul hs.le)
  simpa [delU] using hpsd.dotProduct_mulVec_nonneg u

private lemma pe8_delV_nonneg {m n : ℕ} (M : Mat m n) (v : Vec n) (s : ℝ)
    (hs : 0 < s) : 0 ≤ delV M v s := by
  have hrt : Rts M s = Rs Mᵀ s := by
    unfold Rts Rs
    rw [Matrix.transpose_transpose]
  rw [delV, hrt]
  exact pe8_delU_nonneg Mᵀ v s hs

private lemma pe8_dAlpha_formula {m n : ℕ} (M0 : Mat m n) (ϖ s : ℝ)
    (u : Vec m) (v : Vec n) (d : ℝ) (hs : 0 < s) (hϖ : ϖ ∈ Icc (0 : ℝ) 1) :
    dAlpha1 M0 ϖ s u v d =
        ϖ * ((1 + (ϖ * d) * delC M0 u v s) ^ 2 -
          s * (ϖ * d) ^ 2 * delU M0 u s * delV M0 v s) /
          (delLambda M0 (ϖ * d) u v s) ^ 2 ∧
    dAlpha2 M0 ϖ s u v d =
        2 * ϖ * (ϖ * d) * delU M0 u s * (1 + (ϖ * d) * delC M0 u v s) /
          (delLambda M0 (ϖ * d) u v s) ^ 2 ∧
    dAlpha3 M0 ϖ s u v d =
        (-(2 * s * ϖ * (ϖ * d) * delV M0 v s *
          (1 + (ϖ * d) * delC M0 u v s))) /
          (delLambda M0 (ϖ * d) u v s) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := lem_app_dyn_derivative_i M0 ϖ s u v hs hϖ d
  exact ⟨h1.deriv, h2.deriv, h3.deriv⟩

private lemma pe8_core1 (X X0 L L0 : ℝ) (hL : 0 < L) (hL0 : 1 ≤ L0) (hX0 : |X0| ≤ L0) :
    |X / L^2 - X0 / L0^2| ≤ |X - X0| * (L⁻¹)^2 + |L - L0| * (3 * (L⁻¹)^2 + L⁻¹) := by
  have hLne : L ≠ 0 := hL.ne'
  have hL0pos : 0 < L0 := by linarith
  have hL0ne : L0 ≠ 0 := hL0pos.ne'
  have hid : X / L^2 - X0 / L0^2 =
      (X - X0) / L^2 - X0 * (2 * L0 * (L - L0) + (L - L0)^2) / (L^2 * L0^2) := by
    field_simp
    ring
  rw [hid]
  have hε : 0 < L⁻¹ := inv_pos.mpr hL
  set e := L - L0 with he
  have h1 : |(X - X0) / L^2| = |X - X0| * (L⁻¹)^2 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < L^2)]; field_simp
  have h2 : |X0 * (2 * L0 * e + e^2) / (L^2 * L0^2)| ≤ |e| * (2 * (L⁻¹)^2 + (L⁻¹ + (L⁻¹)^2)) := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < L^2 * L0^2), div_le_iff₀ (by positivity)]
    have hee : |e^2| ≤ |e| * (L + L0) := by
      rw [abs_pow, sq]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [he, abs_le]; constructor <;> nlinarith
    have h3 : |2 * L0 * e + e^2| ≤ 2 * L0 * |e| + |e| * (L + L0) := by
      calc |2 * L0 * e + e^2| ≤ |2 * L0 * e| + |e^2| := abs_add_le _ _
        _ ≤ 2 * L0 * |e| + |e| * (L + L0) := by
          rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * L0)]; linarith
    have key : |X0| * |2 * L0 * e + e^2| ≤ L0 * (2 * L0 * |e| + |e| * (L + L0)) :=
      mul_le_mul hX0 h3 (abs_nonneg _) (by linarith)
    refine key.trans ?_
    have : |e| * (2 * (L⁻¹)^2 + (L⁻¹ + (L⁻¹)^2)) * (L^2 * L0^2)
        = |e| * (2 * L0^2 + (L * L0^2 + L0^2)) := by
      field_simp
    rw [this]
    have hpos : 0 ≤ |e| := abs_nonneg _
    nlinarith [mul_nonneg hpos (by positivity : (0:ℝ) ≤ L0 * L), mul_nonneg hpos hL.le,
      mul_nonneg hpos hL0pos.le, mul_nonneg (mul_nonneg hpos hL.le) (by nlinarith : (0:ℝ) ≤ L0 * L0 - L0),
      mul_nonneg (mul_nonneg hpos hL0pos.le) (by nlinarith : (0:ℝ) ≤ L - 1 + 1),
      mul_nonneg hpos (mul_nonneg hL0pos.le hL0pos.le), mul_nonneg hpos (mul_nonneg hL.le (mul_nonneg hL0pos.le hL0pos.le))]
  calc |(X - X0) / L^2 - X0 * (2 * L0 * e + e^2) / (L^2 * L0^2)|
      ≤ |(X - X0) / L^2| + |X0 * (2 * L0 * e + e^2) / (L^2 * L0^2)| := abs_sub _ _
    _ ≤ |X - X0| * (L⁻¹)^2 + |e| * (2 * (L⁻¹)^2 + (L⁻¹ + (L⁻¹)^2)) := by rw [h1]; linarith
    _ = _ := by ring

private lemma pe8_core2 (a L L0 : ℝ) (hL : 0 < L) (hL0 : 1 ≤ L0) :
    |a / L^2 - 1 / L0^2| ≤ |a - 1| * (L⁻¹)^2 + |L - L0| * (L⁻¹ + (L⁻¹)^2) := by
  have hLne : L ≠ 0 := hL.ne'
  have hL0pos : 0 < L0 := by linarith
  have hL0ne : L0 ≠ 0 := hL0pos.ne'
  have hid : a / L^2 - 1 / L0^2 = (a - 1) / L^2 - (L - L0) * (L + L0) / (L^2 * L0^2) := by
    field_simp
    ring
  rw [hid]
  have hε : 0 < L⁻¹ := inv_pos.mpr hL
  have h1 : |(a - 1) / L^2| = |a - 1| * (L⁻¹)^2 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < L^2)]; field_simp
  have h2 : |(L - L0) * (L + L0) / (L^2 * L0^2)| ≤ |L - L0| * (L⁻¹ + (L⁻¹)^2) := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < L^2 * L0^2),
      abs_of_pos (by linarith : 0 < L + L0), div_le_iff₀ (by positivity)]
    have : |L - L0| * (L⁻¹ + (L⁻¹)^2) * (L^2 * L0^2) = |L - L0| * (L * L0^2 + L0^2) := by
      field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    nlinarith [mul_nonneg hL.le (sq_nonneg L0), mul_nonneg hL.le (by nlinarith : (0:ℝ) ≤ L0 ^ 2 - 1),
      sq_nonneg L0, mul_nonneg hL0pos.le hL.le]
  calc |(a - 1) / L^2 - (L - L0) * (L + L0) / (L^2 * L0^2)|
      ≤ |(a - 1) / L^2| + |(L - L0) * (L + L0) / (L^2 * L0^2)| := abs_sub _ _
    _ ≤ _ := by rw [h1]; linarith

private lemma pe8_aeps (a L : ℝ) (hL : 0 < L) (ha : a^2 ≤ L) :
    |a| * L⁻¹ ≤ (1 + L⁻¹) / 2 := by
  have hε : 0 < L⁻¹ := inv_pos.mpr hL
  have h1 : a^2 * L⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hL]; exact ha
  have h2 : |a| ≤ (a^2 + 1) / 2 := by
    nlinarith [sq_abs a, sq_nonneg (|a| - 1), abs_nonneg a]
  calc |a| * L⁻¹ ≤ (a^2 + 1) / 2 * L⁻¹ := mul_le_mul_of_nonneg_right h2 hε.le
    _ = (a^2 * L⁻¹ + L⁻¹) / 2 := by ring
    _ ≤ _ := by linarith

private lemma pe8_dela (a L : ℝ) (hL : 0 < L) (ha : a^2 ≤ L) :
    (1 + |a|) * (L⁻¹ + (L⁻¹)^2) ≤ 3 * (1 + L⁻¹)^2 := by
  have hε : 0 < L⁻¹ := inv_pos.mpr hL
  have h := pe8_aeps a L hL ha
  have : (1 + |a|) * (L⁻¹ + (L⁻¹)^2) = (L⁻¹ + (L⁻¹)^2) + (|a| * L⁻¹) * (1 + L⁻¹) := by ring
  rw [this]
  have h3 : (|a| * L⁻¹) * (1 + L⁻¹) ≤ (1 + L⁻¹) / 2 * (1 + L⁻¹) :=
    mul_le_mul_of_nonneg_right h (by positivity)
  nlinarith [sq_nonneg L⁻¹]

private lemma pe8_T1 (a P P0 : ℝ) (hP : 0 ≤ P) (hP0 : 0 ≤ P0) (hL : 0 < a^2 + P) :
    |(a^2 - P) / (a^2 + P)^2 - (1 - P0) / (1 + P0)^2| ≤
      12 * (1 + (a^2 + P)⁻¹)^2 * (|a - 1| + |P - P0|) := by
  have h := pe8_core1 (a^2 - P) (1 - P0) (a^2 + P) (1 + P0) hL (by linarith)
    (by rw [abs_le]; constructor <;> linarith)
  have hε : 0 < (a^2 + P)⁻¹ := inv_pos.mpr hL
  have hX : |(a^2 - P) - (1 - P0)| ≤ |a^2 - 1| + |P - P0| := by
    have : (a^2 - P) - (1 - P0) = (a^2 - 1) + (-(P - P0)) := by ring
    rw [this]; exact (abs_add_le _ _).trans (by rw [abs_neg])
  have hLL : |(a^2 + P) - (1 + P0)| ≤ |a^2 - 1| + |P - P0| := by
    have : (a^2 + P) - (1 + P0) = (a^2 - 1) + (P - P0) := by ring
    rw [this]; exact abs_add_le _ _
  set ε := (a^2 + P)⁻¹ with hεdef
  have hda : |a^2 - 1| * (ε + ε^2) ≤ 3 * (1 + ε)^2 * |a - 1| := by
    have : |a^2 - 1| = |a - 1| * |a + 1| := by
      rw [← abs_mul]; congr 1; ring
    have hab : |a + 1| ≤ 1 + |a| := by
      calc |a + 1| ≤ |a| + |1| := abs_add_le _ _
        _ = 1 + |a| := by rw [abs_one]; ring
    have h4 := pe8_dela a (a^2 + P) hL (by linarith)
    rw [this]
    calc |a - 1| * |a + 1| * (ε + ε^2) ≤ |a - 1| * ((1 + |a|) * (ε + ε^2)) := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right hab (by positivity)
      _ ≤ |a - 1| * (3 * (1 + ε)^2) := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
      _ = _ := by ring
  have hmain : |(a^2 - P) / (a^2 + P)^2 - (1 - P0) / (1 + P0)^2| ≤
      (|a^2 - 1| + |P - P0|) * (4 * ε^2 + ε) := by
    refine h.trans ?_
    have e1 : |(a^2 - P) - (1 - P0)| * ε^2 ≤ (|a^2 - 1| + |P - P0|) * ε^2 :=
      mul_le_mul_of_nonneg_right hX (by positivity)
    have e2 : |(a^2 + P) - (1 + P0)| * (3 * ε^2 + ε) ≤ (|a^2 - 1| + |P - P0|) * (3 * ε^2 + ε) :=
      mul_le_mul_of_nonneg_right hLL (by positivity)
    nlinarith [e1, e2]
  refine hmain.trans ?_
  have h5 : |P - P0| * (4 * ε^2 + ε) ≤ 4 * (1 + ε)^2 * |P - P0| := by
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    nlinarith [sq_nonneg ε]
  have h6 : |a^2 - 1| * (4 * ε^2 + ε) ≤ 4 * (|a^2 - 1| * (ε + ε^2)) := by
    nlinarith [mul_nonneg (abs_nonneg (a^2 - 1)) (sq_nonneg ε), mul_nonneg (abs_nonneg (a^2 - 1)) hε.le]
  have h7 : 0 ≤ |a - 1| := abs_nonneg _
  have h8 : 0 ≤ |P - P0| := abs_nonneg _
  have h9 : 0 ≤ (1 + ε)^2 := by positivity
  nlinarith [h5, h6, hda, mul_nonneg h9 h7, mul_nonneg h9 h8]

private lemma pe8_aeps2 (a L : ℝ) (hL : 0 < L) (ha : a^2 ≤ L) :
    |a / L^2| ≤ (1 + L⁻¹)^2 := by
  have hε : 0 < L⁻¹ := inv_pos.mpr hL
  have h := pe8_aeps a L hL ha
  have : |a / L^2| = |a| * L⁻¹ * L⁻¹ := by
    rw [abs_div, abs_of_pos (by positivity : 0 < L^2)]; field_simp
  rw [this]
  calc |a| * L⁻¹ * L⁻¹ ≤ (1 + L⁻¹) / 2 * L⁻¹ := mul_le_mul_of_nonneg_right h hε.le
    _ ≤ (1 + L⁻¹)^2 := by nlinarith [sq_nonneg L⁻¹]

private lemma pe8_T2 (a P P0 U σ : ℝ) (hσ : 0 ≤ σ) (hP : 0 ≤ P) (hP0 : 0 ≤ P0)
    (hL : 0 < a^2 + P) :
    |U * a / (a^2 + P)^2 - σ / (1 + P0)^2| ≤
      (1 + (a^2 + P)⁻¹)^2 * (|U - σ| + 4 * σ * (|a - 1| + |P - P0|)) := by
  have hε : 0 < (a^2 + P)⁻¹ := inv_pos.mpr hL
  have hc := pe8_core2 a (a^2 + P) (1 + P0) hL (by linarith)
  have hLL : |(a^2 + P) - (1 + P0)| ≤ |a^2 - 1| + |P - P0| := by
    have : (a^2 + P) - (1 + P0) = (a^2 - 1) + (P - P0) := by ring
    rw [this]; exact abs_add_le _ _
  have hA := pe8_aeps2 a (a^2 + P) hL (by linarith)
  set ε := (a^2 + P)⁻¹ with hεdef
  have hda : |a^2 - 1| * (ε + ε^2) ≤ 3 * (1 + ε)^2 * |a - 1| := by
    have : |a^2 - 1| = |a - 1| * |a + 1| := by
      rw [← abs_mul]; congr 1; ring
    have hab : |a + 1| ≤ 1 + |a| := by
      calc |a + 1| ≤ |a| + |1| := abs_add_le _ _
        _ = 1 + |a| := by rw [abs_one]; ring
    have h4 := pe8_dela a (a^2 + P) hL (by linarith)
    rw [this]
    calc |a - 1| * |a + 1| * (ε + ε^2) ≤ |a - 1| * ((1 + |a|) * (ε + ε^2)) := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right hab (by positivity)
      _ ≤ |a - 1| * (3 * (1 + ε)^2) := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
      _ = _ := by ring
  have h7 : 0 ≤ |a - 1| := abs_nonneg _
  have h8 : 0 ≤ |P - P0| := abs_nonneg _
  have h9 : 0 ≤ (1 + ε)^2 := by positivity
  have hsec : |a / (a^2 + P)^2 - 1 / (1 + P0)^2| ≤ 4 * (1 + ε)^2 * (|a - 1| + |P - P0|) := by
    refine hc.trans ?_
    have e2 : |(a^2 + P) - (1 + P0)| * (ε + ε^2) ≤ (|a^2 - 1| + |P - P0|) * (ε + ε^2) :=
      mul_le_mul_of_nonneg_right hLL (by positivity)
    have e3 : |P - P0| * (ε + ε^2) ≤ (1 + ε)^2 * |P - P0| := by
      rw [mul_comm]; apply mul_le_mul_of_nonneg_right _ h8; nlinarith
    have e4 : |a - 1| * ε^2 ≤ (1 + ε)^2 * |a - 1| := by
      rw [mul_comm]; apply mul_le_mul_of_nonneg_right _ h7; nlinarith
    nlinarith [mul_nonneg h9 h7, mul_nonneg h9 h8]
  have hid : U * a / (a^2 + P)^2 - σ / (1 + P0)^2 =
      (U - σ) * (a / (a^2 + P)^2) + σ * (a / (a^2 + P)^2 - 1 / (1 + P0)^2) := by
    ring
  rw [hid]
  calc _ ≤ |(U - σ) * (a / (a^2 + P)^2)| + |σ * (a / (a^2 + P)^2 - 1 / (1 + P0)^2)| :=
        abs_add_le _ _
    _ ≤ |U - σ| * (1 + ε)^2 + σ * (4 * (1 + ε)^2 * (|a - 1| + |P - P0|)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hσ]
        gcongr
    _ = _ := by ring

private lemma pe8_u1 (a P : ℝ) (hP : 0 ≤ P) (hL : 0 < a^2 + P) :
    |(a^2 - P) / (a^2 + P)^2| ≤ (a^2 + P)⁻¹ := by
  rw [abs_div, abs_of_pos (by positivity : 0 < (a^2 + P)^2)]
  have : |a^2 - P| ≤ a^2 + P := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg a]
  rw [div_le_iff₀ (by positivity)]
  have h2 : (a^2 + P)⁻¹ * (a^2 + P)^2 = a^2 + P := by field_simp
  rw [h2]; exact this

private lemma pe8_u2 (a P U : ℝ) (hU : 0 ≤ U) (hP : 0 ≤ P) (hL : 0 < a^2 + P) :
    |U * a / (a^2 + P)^2| ≤ U * (1 + (a^2 + P)⁻¹)^2 := by
  have hA := pe8_aeps2 a (a^2 + P) hL (by linarith)
  rw [mul_div_assoc, abs_mul, abs_of_nonneg hU]
  exact mul_le_mul_of_nonneg_left hA hU

private lemma pe8_small (s0 K1 : ℝ) (hs0 : 0 < s0) (hK1 : 0 ≤ K1)
    (s ϖ d U V C σ σt N t Err : ℝ) (hs : s0 ≤ s) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1) (hU : 0 ≤ U)
    (hV : 0 ≤ V) (hσ : 0 ≤ σ) (hσt : 0 ≤ σt) (hUN : s * U ≤ N) (hVN : s * V ≤ N) (hN : 0 ≤ N)
    (hσK : s * σ ≤ K1) (hσtK : s * σt ≤ K1) (Λ : ℝ)
    (hinv : Λ⁻¹ ≤ (1 + 3 / (4 * Real.sqrt s) * |ϖ * d| * N)^2)
    (ht : t = (1 + |d|) * (1 + N))
    (hErr : Err = |s * U - s * σ| + |s * V - s * σt| + Real.sqrt s * |C|) :
    1 ≤ t ∧ |d| ≤ t ∧ N ≤ t ∧ |d| * N ≤ t ∧ 0 ≤ Err ∧
    |s * U - s * σ| ≤ Err ∧ |s * V - s * σt| ≤ Err ∧
    Λ⁻¹ ≤ (1 + 3 / (4 * Real.sqrt s0))^2 * t^2 ∧
    |ϖ * d * C| + |s * (ϖ * d)^2 * U * V - ϖ^2 * s * σ * σt * d^2| ≤
      (1 / Real.sqrt s0 + (1 + K1) / s0) * t^2 * Err := by
  have hs0r : 0 < Real.sqrt s0 := Real.sqrt_pos.mpr hs0
  have hs_pos : 0 < s := lt_of_lt_of_le hs0 hs
  have hsq : Real.sqrt s0 ≤ Real.sqrt s := Real.sqrt_le_sqrt hs
  have hsqpos : 0 < Real.sqrt s := lt_of_lt_of_le hs0r hsq
  have hd0 := abs_nonneg d
  have ht1 : 1 ≤ t := by rw [ht]; nlinarith only [hd0, hN]
  have hdt : |d| ≤ t := by rw [ht]; nlinarith only [hd0, hN]
  have hNt : N ≤ t := by rw [ht]; nlinarith only [hd0, hN]
  have hdNt : |d| * N ≤ t := by rw [ht]; nlinarith only [hd0, hN]
  have ht2t : t ≤ t^2 := le_self_pow₀ ht1 (by norm_num)
  have ht2 : 1 ≤ t^2 := ht1.trans ht2t
  have hA := abs_nonneg (s * U - s * σ)
  have hB := abs_nonneg (s * V - s * σt)
  have hCC := mul_nonneg hsqpos.le (abs_nonneg C)
  have hErr0 : 0 ≤ Err := by rw [hErr]; linarith
  have hE1 : |s * U - s * σ| ≤ Err := by rw [hErr]; linarith
  have hE2 : |s * V - s * σt| ≤ Err := by rw [hErr]; linarith
  have hE3 : Real.sqrt s0 * |C| ≤ Err := by
    have h1 : Real.sqrt s0 * |C| ≤ Real.sqrt s * |C| :=
      mul_le_mul_of_nonneg_right hsq (abs_nonneg C)
    rw [hErr]; linarith
  refine ⟨ht1, hdt, hNt, hdNt, hErr0, hE1, hE2, ?_, ?_⟩
  · refine hinv.trans ?_
    set c0 : ℝ := 3 / (4 * Real.sqrt s0) with hc0
    have hc0pos : 0 ≤ c0 := by positivity
    have h1 : 3 / (4 * Real.sqrt s) ≤ c0 := by
      rw [hc0]; apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      linarith
    have h2 : |ϖ * d| ≤ |d| := by
      rw [abs_mul, abs_of_nonneg hϖ0]
      nlinarith only [hd0, hϖ1]
    have h3 : 1 + 3 / (4 * Real.sqrt s) * |ϖ * d| * N ≤ (1 + c0) * t := by
      have hh : 3 / (4 * Real.sqrt s) * |ϖ * d| * N ≤ c0 * (|d| * N) := by
        have : 0 ≤ 3 / (4 * Real.sqrt s) := by positivity
        calc 3 / (4 * Real.sqrt s) * |ϖ * d| * N ≤ c0 * |d| * N := by gcongr
          _ = _ := by ring
      nlinarith only [hh, mul_nonneg hc0pos (sub_nonneg.mpr hdNt), ht1]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h3 2
  · have hVnn : 0 ≤ s * V := mul_nonneg hs_pos.le hV
    have hσnn : 0 ≤ s * σ := mul_nonneg hs_pos.le hσ
    have hid : s * (ϖ * d)^2 * U * V - ϖ^2 * s * σ * σt * d^2 =
        ((ϖ * d)^2 / s) * ((s * U - s * σ) * (s * V) + (s * σ) * (s * V - s * σt)) := by
      field_simp
      ring
    have hq0 : 0 ≤ (ϖ * d)^2 / s := by positivity
    have hq1 : (ϖ * d)^2 / s ≤ (1 + |d|)^2 / s0 := by
      have h1 : (ϖ * d)^2 ≤ (1 + |d|)^2 := by
        rw [mul_pow, ← sq_abs d]
        have : ϖ^2 ≤ 1 := by nlinarith only [hϖ0, hϖ1]
        nlinarith only [this, hd0, sq_nonneg (|d|)]
      calc (ϖ * d)^2 / s ≤ (1 + |d|)^2 / s := by gcongr
        _ ≤ (1 + |d|)^2 / s0 := by gcongr
    have hin : |(s * U - s * σ) * (s * V) + (s * σ) * (s * V - s * σt)| ≤ (N + K1) * Err := by
      calc _ ≤ |(s * U - s * σ) * (s * V)| + |(s * σ) * (s * V - s * σt)| := abs_add_le _ _
        _ = |s * U - s * σ| * (s * V) + (s * σ) * |s * V - s * σt| := by
          rw [abs_mul (s * U - s * σ) (s * V), abs_mul (s * σ) (s * V - s * σt), abs_of_nonneg hVnn,
            abs_of_nonneg hσnn]
        _ ≤ Err * N + K1 * Err := by
          gcongr
        _ = (N + K1) * Err := by ring
    have hDP : |s * (ϖ * d)^2 * U * V - ϖ^2 * s * σ * σt * d^2| ≤
        ((1 + K1) / s0) * t^2 * Err := by
      rw [hid, abs_mul, abs_of_nonneg hq0]
      calc (ϖ * d)^2 / s * |(s * U - s * σ) * (s * V) + (s * σ) * (s * V - s * σt)|
          ≤ ((1 + |d|)^2 / s0) * ((N + K1) * Err) := by
            gcongr
        _ ≤ ((1 + K1) / s0) * t^2 * Err := by
            have h1 : (1 + |d|)^2 * (N + K1) ≤ (1 + K1) * t^2 := by
              rw [ht]
              have h2 : N + K1 ≤ (1 + K1) * (1 + N) := by nlinarith only [hN, hK1]
              have h3 : (1 + N) ≤ (1 + N)^2 := le_self_pow₀ (by linarith) (by norm_num)
              calc (1 + |d|)^2 * (N + K1) ≤ (1 + |d|)^2 * ((1 + K1) * (1 + N)) := by gcongr
                _ ≤ (1 + |d|)^2 * ((1 + K1) * (1 + N)^2) := by gcongr
                _ = _ := by ring
            calc (1 + |d|)^2 / s0 * ((N + K1) * Err) = ((1 + |d|)^2 * (N + K1)) * Err / s0 := by
                  ring
              _ ≤ ((1 + K1) * t^2) * Err / s0 := by gcongr
              _ = _ := by ring
    have hCb : |ϖ * d * C| ≤ (1 / Real.sqrt s0) * t^2 * Err := by
      have h1 : |ϖ * d * C| ≤ |d| * |C| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hϖ0]
        have : 0 ≤ |d| * |C| := by positivity
        nlinarith only [hϖ1, mul_nonneg hd0 (abs_nonneg C), abs_nonneg C, hd0]
      have h2 : |d| * |C| ≤ t * Err / Real.sqrt s0 := by
        rw [le_div_iff₀ hs0r]
        calc |d| * |C| * Real.sqrt s0 = |d| * (Real.sqrt s0 * |C|) := by ring
          _ ≤ t * Err := by gcongr
      calc |ϖ * d * C| ≤ t * Err / Real.sqrt s0 := h1.trans h2
        _ ≤ t^2 * Err / Real.sqrt s0 := by gcongr
        _ = _ := by ring
    calc _ ≤ (1 / Real.sqrt s0) * t^2 * Err + ((1 + K1) / s0) * t^2 * Err := add_le_add hCb hDP
      _ = _ := by ring


set_option maxHeartbeats 2000000 in
private lemma pe8_master (s0 K1 : ℝ) (hs0 : 0 < s0) (hK1 : 0 ≤ K1) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (s ϖ d U V C σ σt N t Err x : ℝ), s0 ≤ s → 0 ≤ ϖ → ϖ ≤ 1 → 0 ≤ U → 0 ≤ V →
      0 ≤ σ → 0 ≤ σt → s * U ≤ N → s * V ≤ N → 0 ≤ N → s * σ ≤ K1 → s * σt ≤ K1 →
      0 < (1 + ϖ * d * C)^2 + s * (ϖ * d)^2 * U * V →
      ((1 + ϖ * d * C)^2 + s * (ϖ * d)^2 * U * V)⁻¹ ≤
        (1 + 3 / (4 * Real.sqrt s) * |ϖ * d| * N)^2 →
      t = (1 + |d|) * (1 + N) →
      Err = |s * U - s * σ| + |s * V - s * σt| + Real.sqrt s * |C| →
      x = ϖ^2 * s * σ * σt →
      |ϖ * ((1 + ϖ * d * C)^2 - s * (ϖ * d)^2 * U * V) /
          ((1 + ϖ * d * C)^2 + s * (ϖ * d)^2 * U * V)^2
        - ϖ * ((1 - x * d^2) / (1 + x * d^2)^2)| ≤ ϖ * (κ * t^8 * Err) ∧
      |2 * ϖ * (ϖ * d) * U * (1 + ϖ * d * C) /
          ((1 + ϖ * d * C)^2 + s * (ϖ * d)^2 * U * V)^2
        - ϖ^2 * σ * (2 * d / (1 + x * d^2)^2)| ≤ ϖ^2 * (κ * t^8 * Err) / s ∧
      |(-(2 * s * ϖ * (ϖ * d) * V * (1 + ϖ * d * C))) /
          ((1 + ϖ * d * C)^2 + s * (ϖ * d)^2 * U * V)^2
        + s * ϖ^2 * σt * (2 * d / (1 + x * d^2)^2)| ≤ ϖ^2 * (κ * t^8 * Err) ∧
      |ϖ * ((1 + ϖ * d * C)^2 - s * (ϖ * d)^2 * U * V) /
          ((1 + ϖ * d * C)^2 + s * (ϖ * d)^2 * U * V)^2| ≤ ϖ * (κ * t^8) ∧
      |2 * ϖ * (ϖ * d) * U * (1 + ϖ * d * C) /
          ((1 + ϖ * d * C)^2 + s * (ϖ * d)^2 * U * V)^2| ≤ ϖ^2 * (κ * t^8) / s ∧
      |(-(2 * s * ϖ * (ϖ * d) * V * (1 + ϖ * d * C))) /
          ((1 + ϖ * d * C)^2 + s * (ϖ * d)^2 * U * V)^2| ≤ ϖ^2 * (κ * t^8) := by
  have hs0r : 0 < Real.sqrt s0 := Real.sqrt_pos.mpr hs0
  set M : ℝ := (1 + 3 / (4 * Real.sqrt s0))^2 with hM
  have hM1 : 0 ≤ M := by positivity
  set ρ : ℝ := (1 + M)^2 with hρ
  have hρ1 : 1 ≤ ρ := by rw [hρ]; nlinarith only [hM1]
  set c2 : ℝ := 1 / Real.sqrt s0 + (1 + K1) / s0 with hc2
  have hc2pos : 0 ≤ c2 := by positivity
  refine ⟨12 * ρ * c2 + 2 * ρ * (1 + 4 * K1 * c2) + M + 2 * ρ, by positivity, ?_⟩
  intro s ϖ d U V C σ σt N t Err x hs hϖ0 hϖ1 hU hV hσ hσt hUN hVN hN hσK hσtK hL hinv ht hErr hx
  have hs_pos : 0 < s := lt_of_lt_of_le hs0 hs
  obtain ⟨ht1, hdt, hNt, hdNt, hErr0, hE1, hE2, hεM, hS⟩ := pe8_small s0 K1 hs0 hK1 s ϖ d U V C σ σt N t Err
    hs hϖ0 hϖ1 hU hV hσ hσt hUN hVN hN hσK hσtK _ hinv ht hErr
  subst hx
  set κ : ℝ := 12 * ρ * c2 + 2 * ρ * (1 + 4 * K1 * c2) + M + 2 * ρ with hκ
  set a : ℝ := 1 + ϖ * d * C with ha
  set P : ℝ := s * (ϖ * d)^2 * U * V with hPdef
  set P0 : ℝ := ϖ^2 * s * σ * σt * d^2 with hP0def
  have hP : 0 ≤ P := by rw [hPdef]; positivity
  have hP0 : 0 ≤ P0 := by rw [hP0def]; positivity
  have hd0 := abs_nonneg d
  have ht0 : 0 < t := by linarith
  have ht2t : t ≤ t^2 := le_self_pow₀ ht1 (by norm_num)
  have ht2 : 1 ≤ t^2 := ht1.trans ht2t
  set ε : ℝ := (a^2 + P)⁻¹ with hε
  have hε0 : 0 < ε := inv_pos.mpr hL
  have hε1 : (1 + ε)^2 ≤ ρ * t^4 := by
    have h1 : 1 + ε ≤ (1 + M) * t^2 := by nlinarith only [hεM, ht2, hM1]
    calc (1 + ε)^2 ≤ ((1 + M) * t^2)^2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = ρ * t^4 := by rw [hρ]; ring
  have hS' : |a - 1| + |P - P0| ≤ c2 * t^2 * Err := by
    have : a - 1 = ϖ * d * C := by rw [ha]; ring
    rw [this]; exact hS
  have ht4 : ∀ k : ℕ, k ≤ 8 → t^k ≤ t^8 := fun k hk => pow_le_pow_right₀ ht1 hk
  have hρ0 : 0 ≤ ρ := by linarith
  have hq1 : 0 ≤ 2 * ρ * (1 + 4 * K1 * c2) := by positivity
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  -- the key bound for (|a - 1| + |P - P0|)
  have hkey : (1 + ε)^2 * (|a - 1| + |P - P0|) ≤ ρ * c2 * t^6 * Err := by
    calc (1 + ε)^2 * (|a - 1| + |P - P0|) ≤ (ρ * t^4) * (c2 * t^2 * Err) := by
          gcongr
      _ = ρ * c2 * t^6 * Err := by ring
  -- the quantity (Err + 4 K1 S) bound
  have hkey2 : (1 + ε)^2 * (Err + 4 * K1 * (|a - 1| + |P - P0|)) ≤
      ρ * (1 + 4 * K1 * c2) * t^6 * Err := by
    have h1 : Err + 4 * K1 * (|a - 1| + |P - P0|) ≤ (1 + 4 * K1 * c2) * t^2 * Err := by
      have : 4 * K1 * (|a - 1| + |P - P0|) ≤ 4 * K1 * (c2 * t^2 * Err) := by gcongr
      nlinarith only [this, ht2, hErr0, hK1, hc2pos]
    calc (1 + ε)^2 * (Err + 4 * K1 * (|a - 1| + |P - P0|))
        ≤ (ρ * t^4) * ((1 + 4 * K1 * c2) * t^2 * Err) := by gcongr
      _ = _ := by ring
  have hT1 := pe8_T1 a P P0 hP hP0 hL
  have hT2 := pe8_T2 a P P0 U σ hσ hP hP0 hL
  have hT3 := pe8_T2 a P P0 V σt hσt hP hP0 hL
  have hu1 := pe8_u1 a P hP hL
  have hu2 := pe8_u2 a P U hU hP hL
  have hu3 := pe8_u2 a P V hV hP hL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- c1
    have e : ϖ * (a^2 - P) / (a^2 + P)^2 - ϖ * ((1 - P0) / (1 + P0)^2) =
        ϖ * ((a^2 - P) / (a^2 + P)^2 - (1 - P0) / (1 + P0)^2) := by ring
    rw [e, abs_mul, abs_of_nonneg hϖ0]
    apply mul_le_mul_of_nonneg_left _ hϖ0
    calc _ ≤ 12 * ((1 + ε)^2 * (|a - 1| + |P - P0|)) := by linarith
      _ ≤ 12 * (ρ * c2 * t^6 * Err) := by gcongr
      _ ≤ κ * t^8 * Err := by
        have h6 := ht4 6 (by norm_num)
        have : 12 * (ρ * c2 * t^6 * Err) = (12 * ρ * c2) * t^6 * Err := by ring
        rw [this]
        have hk : 12 * ρ * c2 ≤ κ := by rw [hκ]; linarith only [hq1, hM1, hρ0]
        calc (12 * ρ * c2) * t^6 * Err ≤ κ * t^6 * Err := by gcongr
          _ ≤ κ * t^8 * Err := by
            gcongr
  · -- c2
    have hUs : |U - σ| ≤ Err / s := by
      rw [le_div_iff₀ hs_pos]
      have : |s * U - s * σ| = |U - σ| * s := by
        rw [← mul_sub, abs_mul, abs_of_pos hs_pos, mul_comm]
      linarith
    have hσs : σ ≤ K1 / s := by rw [le_div_iff₀ hs_pos]; linarith
    have h2a : |U * a / (a^2 + P)^2 - σ / (1 + P0)^2| ≤
        (1 + ε)^2 * (Err + 4 * K1 * (|a - 1| + |P - P0|)) / s := by
      refine hT2.trans ?_
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hSn : 0 ≤ |a - 1| + |P - P0| := by positivity
      have : 4 * σ * (|a - 1| + |P - P0|) ≤ 4 * (K1 / s) * (|a - 1| + |P - P0|) := by gcongr
      calc |U - σ| + 4 * σ * (|a - 1| + |P - P0|) ≤ Err / s + 4 * (K1 / s) * (|a - 1| + |P - P0|) := by
            linarith
        _ = (Err + 4 * K1 * (|a - 1| + |P - P0|)) / s := by ring
    have e : 2 * ϖ * (ϖ * d) * U * a / (a^2 + P)^2 - ϖ^2 * σ * (2 * d / (1 + P0)^2) =
        (2 * ϖ^2 * d) * (U * a / (a^2 + P)^2 - σ / (1 + P0)^2) := by ring
    rw [e, abs_mul]
    have hc : |2 * ϖ^2 * d| ≤ 2 * ϖ^2 * t := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ϖ^2)]
      gcongr
    calc |2 * ϖ^2 * d| * |U * a / (a^2 + P)^2 - σ / (1 + P0)^2|
        ≤ (2 * ϖ^2 * t) * ((1 + ε)^2 * (Err + 4 * K1 * (|a - 1| + |P - P0|)) / s) := by
          gcongr
      _ ≤ (2 * ϖ^2 * t) * (ρ * (1 + 4 * K1 * c2) * t^6 * Err / s) := by
          gcongr
      _ = ϖ^2 * ((2 * ρ * (1 + 4 * K1 * c2)) * t^7 * Err) / s := by ring
      _ ≤ ϖ^2 * (κ * t^8 * Err) / s := by
          have h7 := ht4 7 (by norm_num)
          have hk : 2 * ρ * (1 + 4 * K1 * c2) ≤ κ := by
            rw [hκ]
            have := mul_nonneg (by norm_num : (0:ℝ) ≤ 12) (mul_nonneg hρ0 hc2pos)
            nlinarith only [this, hM1, hρ0, hq1]
          have hT : (2 * ρ * (1 + 4 * K1 * c2)) * t^7 * Err ≤ κ * t^8 * Err := by
            calc _ ≤ κ * t^7 * Err := by gcongr
              _ ≤ κ * t^8 * Err := by gcongr
          gcongr
  · -- c3
    have hVs : |V - σt| ≤ Err / s := by
      rw [le_div_iff₀ hs_pos]
      have : |s * V - s * σt| = |V - σt| * s := by
        rw [← mul_sub, abs_mul, abs_of_pos hs_pos, mul_comm]
      linarith
    have hσs : σt ≤ K1 / s := by rw [le_div_iff₀ hs_pos]; linarith
    have h2a : |V * a / (a^2 + P)^2 - σt / (1 + P0)^2| ≤
        (1 + ε)^2 * (Err + 4 * K1 * (|a - 1| + |P - P0|)) / s := by
      refine hT3.trans ?_
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hSn : 0 ≤ |a - 1| + |P - P0| := by positivity
      have : 4 * σt * (|a - 1| + |P - P0|) ≤ 4 * (K1 / s) * (|a - 1| + |P - P0|) := by gcongr
      calc |V - σt| + 4 * σt * (|a - 1| + |P - P0|) ≤ Err / s + 4 * (K1 / s) * (|a - 1| + |P - P0|) := by
            linarith
        _ = (Err + 4 * K1 * (|a - 1| + |P - P0|)) / s := by ring
    have e : (-(2 * s * ϖ * (ϖ * d) * V * a)) / (a^2 + P)^2 + s * ϖ^2 * σt * (2 * d / (1 + P0)^2) =
        -(2 * s * ϖ^2 * d) * (V * a / (a^2 + P)^2 - σt / (1 + P0)^2) := by ring
    rw [e, abs_mul, abs_neg]
    have hc : |2 * s * ϖ^2 * d| ≤ 2 * s * ϖ^2 * t := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * s * ϖ^2)]
      gcongr
    calc |2 * s * ϖ^2 * d| * |V * a / (a^2 + P)^2 - σt / (1 + P0)^2|
        ≤ (2 * s * ϖ^2 * t) * ((1 + ε)^2 * (Err + 4 * K1 * (|a - 1| + |P - P0|)) / s) := by
          gcongr
      _ ≤ (2 * s * ϖ^2 * t) * (ρ * (1 + 4 * K1 * c2) * t^6 * Err / s) := by
          gcongr
      _ = ϖ^2 * ((2 * ρ * (1 + 4 * K1 * c2)) * t^7 * Err) := by field_simp
      _ ≤ ϖ^2 * (κ * t^8 * Err) := by
          have h7 := ht4 7 (by norm_num)
          have hk : 2 * ρ * (1 + 4 * K1 * c2) ≤ κ := by
            rw [hκ]
            have := mul_nonneg (by norm_num : (0:ℝ) ≤ 12) (mul_nonneg hρ0 hc2pos)
            nlinarith only [this, hM1, hρ0, hq1]
          have hT : (2 * ρ * (1 + 4 * K1 * c2)) * t^7 * Err ≤ κ * t^8 * Err := by
            calc _ ≤ κ * t^7 * Err := by gcongr
              _ ≤ κ * t^8 * Err := by gcongr
          gcongr
  · -- u1
    have e : ϖ * (a^2 - P) / (a^2 + P)^2 = ϖ * ((a^2 - P) / (a^2 + P)^2) := by ring
    rw [e, abs_mul, abs_of_nonneg hϖ0]
    apply mul_le_mul_of_nonneg_left _ hϖ0
    calc _ ≤ ε := hu1
      _ ≤ M * t^2 := hεM
      _ ≤ κ * t^8 := by
        have h2 := ht4 2 (by norm_num)
        have hk : M ≤ κ := by
          rw [hκ]
          have := mul_nonneg (by norm_num : (0:ℝ) ≤ 12) (mul_nonneg hρ0 hc2pos)
          nlinarith only [this, hρ0, hq1]
        calc M * t^2 ≤ κ * t^2 := by gcongr
          _ ≤ κ * t^8 := by gcongr
  · -- u2
    have e : 2 * ϖ * (ϖ * d) * U * a / (a^2 + P)^2 = (2 * ϖ^2 * d) * (U * a / (a^2 + P)^2) := by ring
    rw [e, abs_mul]
    have hc : |2 * ϖ^2 * d| ≤ 2 * ϖ^2 * |d| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ϖ^2)]
    have hUn : 0 ≤ U := hU
    calc |2 * ϖ^2 * d| * |U * a / (a^2 + P)^2| ≤ (2 * ϖ^2 * |d|) * (U * (1 + ε)^2) := by
          gcongr
      _ = (2 * ϖ^2 / s) * (|d| * (s * U)) * (1 + ε)^2 := by field_simp
      _ ≤ (2 * ϖ^2 / s) * t * (ρ * t^4) := by
          have : |d| * (s * U) ≤ t := (mul_le_mul_of_nonneg_left hUN hd0).trans hdNt
          gcongr
      _ = ϖ^2 * ((2 * ρ) * t^5) / s := by ring
      _ ≤ ϖ^2 * (κ * t^8) / s := by
          have h5 := ht4 5 (by norm_num)
          have hk : 2 * ρ ≤ κ := by
            rw [hκ]
            have := mul_nonneg (by norm_num : (0:ℝ) ≤ 12) (mul_nonneg hρ0 hc2pos)
            nlinarith only [this, hρ0, hq1, hM1]
          have : (2 * ρ) * t^5 ≤ κ * t^8 := by
            calc _ ≤ κ * t^5 := by gcongr
              _ ≤ κ * t^8 := by gcongr
          gcongr
  · -- u3
    have e : (-(2 * s * ϖ * (ϖ * d) * V * a)) / (a^2 + P)^2 =
        -(2 * s * ϖ^2 * d) * (V * a / (a^2 + P)^2) := by ring
    rw [e, abs_mul, abs_neg]
    have hc : |2 * s * ϖ^2 * d| ≤ 2 * s * ϖ^2 * |d| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * s * ϖ^2)]
    calc |2 * s * ϖ^2 * d| * |V * a / (a^2 + P)^2| ≤ (2 * s * ϖ^2 * |d|) * (V * (1 + ε)^2) := by
          gcongr
      _ = (2 * ϖ^2) * (|d| * (s * V)) * (1 + ε)^2 := by ring
      _ ≤ (2 * ϖ^2) * t * (ρ * t^4) := by
          have : |d| * (s * V) ≤ t := (mul_le_mul_of_nonneg_left hVN hd0).trans hdNt
          gcongr
      _ = ϖ^2 * ((2 * ρ) * t^5) := by ring
      _ ≤ ϖ^2 * (κ * t^8) := by
          have h5 := ht4 5 (by norm_num)
          have hk : 2 * ρ ≤ κ := by
            rw [hκ]
            have := mul_nonneg (by norm_num : (0:ℝ) ≤ 12) (mul_nonneg hρ0 hc2pos)
            nlinarith only [this, hρ0, hq1, hM1]
          have : (2 * ρ) * t^5 ≤ κ * t^8 := by
            calc _ ≤ κ * t^5 := by gcongr
              _ ≤ κ * t^8 := by gcongr
          gcongr

private lemma pe8_holder {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f g : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (q : ℕ) (hq : 1 ≤ q) :
    eLpNorm (fun x => f x * g x) (q : ℝ≥0∞) μ ≤
      eLpNorm f ((2 * q : ℕ) : ℝ≥0∞) μ * eLpNorm g ((2 * q : ℕ) : ℝ≥0∞) μ := by
  have : ENNReal.HolderTriple ((2 * q : ℕ) : ℝ≥0∞) ((2 * q : ℕ) : ℝ≥0∞) (q : ℝ≥0∞) := by
    refine ⟨?_⟩
    have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have hqt : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top q
    push_cast
    rw [← two_mul, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← mul_assoc,
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  exact eLpNorm_smul_le_mul_eLpNorm (φ := f) (f := g) hf hg

private lemma pe8_pow_norm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (g : Ω → ℝ)
    (hg : AEStronglyMeasurable g μ) (hg0 : ∀ x, 0 ≤ g x) (k q : ℕ) (hk : 1 ≤ k) :
    eLpNorm (fun x => g x ^ k) (q : ℝ≥0∞) μ = eLpNorm g ((q * k : ℕ) : ℝ≥0∞) μ ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h := eLpNorm_norm_rpow g hg (p := (q : ℝ≥0∞)) hkpos
  have e1 : (fun x => ‖g x‖ ^ (k : ℝ)) = fun x => g x ^ k := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x), Real.rpow_natCast]
  rw [e1] at h
  rw [h, ENNReal.ofReal_natCast, ENNReal.rpow_natCast]
  congr 2
  push_cast
  rfl

private lemma pe8_one_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : AEStronglyMeasurable g μ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    eLpNorm (fun x => 1 + g x) p μ ≤ 1 + eLpNorm g p μ := by
  have h := eLpNorm_add_le (f := fun _ : Ω => (1 : ℝ)) (g := g) (μ := μ) hp
  have hc : eLpNorm (fun _ : Ω => (1 : ℝ)) p μ ≤ 1 := by
    rw [eLpNorm_const _ (by positivity) (IsProbabilityMeasure.ne_zero μ)]
    simp
  calc eLpNorm (fun x => 1 + g x) p μ ≤ eLpNorm (fun _ : Ω => (1 : ℝ)) p μ + eLpNorm g p μ := h
    _ ≤ 1 + eLpNorm g p μ := by gcongr

private lemma pe8_cont_momN {m n : ℕ} (Cv : Covariances m n) (B : ℕ) :
    Continuous (momN Cv B) := by
  unfold momN eucNorm momU momV
  fun_prop

private lemma pe8_cont_resid {m n : ℕ} (Ah : Mat m n) : Continuous (fun x => resid Ah x) := by
  unfold resid
  fun_prop

private lemma pe8_t_moment (k q : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) (γ CS : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {m n B : ℕ} (Cv : Covariances m n) (Ah : Mat m n), fro Ah = 1 →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B → opNorm Cv.Sout ≤ CS → opNorm Cv.Sin ≤ CS →
      eLpNorm (fun z : Vec m × Vec n => ((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ k)
        (q : ℝ≥0∞) (gaussPair m n) ≤ ENNReal.ofReal K := by
  set Q : ℕ := 2 * q * k with hQ
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  set D1 : ℝ := ((Nat.doubleFactorial (2 * (q * k) - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / (q * k : ℕ)) with hD1
  set D2 : ℝ := 2 * CS * γ * ((Nat.doubleFactorial (2 * Q - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / Q) with hD2
  have hD1nn : 0 ≤ D1 := by rw [hD1]; positivity
  refine ⟨(1 + D1) ^ k * (1 + max D2 0) ^ k, by positivity, ?_⟩
  intro m n B Cv Ah hA hm hn hCo hCi
  have hdc := pe8_cont_resid Ah
  have hNc := pe8_cont_momN Cv B
  have hmd : AEStronglyMeasurable (fun x => 1 + |resid Ah x|) (gaussPair m n) :=
    (by fun_prop : Continuous fun x => 1 + |resid Ah x|).aestronglyMeasurable
  have hmN : AEStronglyMeasurable (fun x => 1 + momN Cv B x) (gaussPair m n) :=
    (continuous_const.add hNc).aestronglyMeasurable
  have hmf : AEStronglyMeasurable (fun x => (1 + |resid Ah x|) ^ k) (gaussPair m n) :=
    (by fun_prop : Continuous fun x => (1 + |resid Ah x|) ^ k).aestronglyMeasurable
  have hmg : AEStronglyMeasurable (fun x => (1 + momN Cv B x) ^ k) (gaussPair m n) :=
    ((continuous_const.add hNc).pow k).aestronglyMeasurable
  have hN0 : ∀ x, 0 ≤ momN Cv B x := fun x => by unfold momN eucNorm; positivity
  have e : (fun z : Vec m × Vec n => ((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ k) =
      fun z => (1 + |resid Ah z|) ^ k * (1 + momN Cv B z) ^ k := by
    funext z; rw [mul_pow]
  rw [e]
  refine (pe8_holder _ _ hmf hmg q hq).trans ?_
  have hQe : (2 * q) * k = Q := by rw [hQ]
  -- first factor
  have h1 : eLpNorm (fun x => (1 + |resid Ah x|) ^ k) ((2 * q : ℕ) : ℝ≥0∞) (gaussPair m n) ≤
      ENNReal.ofReal ((1 + D1) ^ k) := by
    rw [pe8_pow_norm (fun x => 1 + |resid Ah x|) hmd (fun x => by positivity) k (2 * q) hk, hQe]
    have hd2 := lem_app_de_moments_ii Ah hA (q * k) (by nlinarith)
    have hQ' : ((Q : ℕ) : ℝ≥0∞) = ((2 * (q * k) : ℕ) : ℝ≥0∞) := by
      rw [hQ]; congr 1; ring
    have hlin := pe8_one_add (μ := gaussPair m n) (fun x => |resid Ah x|) (hdc.abs.aestronglyMeasurable)
      ((Q : ℕ) : ℝ≥0∞) (by exact_mod_cast hQ1)
    have habs : eLpNorm (fun x => |resid Ah x|) ((Q : ℕ) : ℝ≥0∞) (gaussPair m n) =
        eLpNorm (fun x => resid Ah x) ((Q : ℕ) : ℝ≥0∞) (gaussPair m n) := by
      have := eLpNorm_norm (μ := gaussPair m n) (p := ((Q : ℕ) : ℝ≥0∞)) (fun x => resid Ah x)
        hdc.aestronglyMeasurable
      simpa [Real.norm_eq_abs] using this
    rw [habs, hQ'] at hlin
    calc eLpNorm (fun x => 1 + |resid Ah x|) ((Q : ℕ) : ℝ≥0∞) (gaussPair m n) ^ k
        ≤ (1 + ENNReal.ofReal D1) ^ k := by
          rw [hQ']
          gcongr
          exact hlin.trans (by gcongr)
      _ = ENNReal.ofReal ((1 + D1) ^ k) := by
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (by norm_num) hD1nn,
            ENNReal.ofReal_one]
  have h2 : eLpNorm (fun x => (1 + momN Cv B x) ^ k) ((2 * q : ℕ) : ℝ≥0∞) (gaussPair m n) ≤
      ENNReal.ofReal ((1 + max D2 0) ^ k) := by
    rw [pe8_pow_norm (fun x => 1 + momN Cv B x) hmN (fun x => by have := hN0 x; positivity) k (2 * q) hk, hQe]
    have hm1 := lem_app_de_moments_i Cv B γ CS ⟨hm, hn⟩ ⟨hCo, hCi⟩ Q hQ1
    have hlin := pe8_one_add (μ := gaussPair m n) (momN Cv B) hNc.aestronglyMeasurable ((Q : ℕ) : ℝ≥0∞)
      (by exact_mod_cast hQ1)
    calc eLpNorm (fun x => 1 + momN Cv B x) ((Q : ℕ) : ℝ≥0∞) (gaussPair m n) ^ k
        ≤ (1 + ENNReal.ofReal (max D2 0)) ^ k := by
          gcongr
          refine hlin.trans ?_
          gcongr
          exact hm1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      _ = ENNReal.ofReal ((1 + max D2 0) ^ k) := by
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (by norm_num) (le_max_right _ _),
            ENNReal.ofReal_one]
  calc _ ≤ ENNReal.ofReal ((1 + D1) ^ k) * ENNReal.ofReal ((1 + max D2 0) ^ k) := by gcongr
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

private lemma pe8_abs_scale {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (c : ℝ)
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) :
    eLpNorm (fun z => |c * f z|) p μ = ENNReal.ofReal |c| * eLpNorm f p μ := by
  have h1 : eLpNorm (fun z => |c * f z|) p μ = eLpNorm (fun z => c * f z) p μ := by
    have := eLpNorm_norm (μ := μ) (p := p) (fun z => c * f z) (hf.const_mul c)
    simpa [Real.norm_eq_abs] using this
  rw [h1]
  have := eLpNorm_const_smul (μ := μ) (p := p) c f
  rw [show (fun z => c * f z) = c • f by rfl, this]
  rw [Real.enorm_eq_ofReal_abs]

private lemma pe8_Rs_psd {m n : ℕ} (M : Mat m n) (s : ℝ) (hs : 0 < s) : (Rs M s).PosSemidef := by
  unfold Rs
  refine Matrix.PosSemidef.inv ?_
  have hMM : (M * Mᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose M
  exact hMM.add (Matrix.PosSemidef.one.smul hs.le)

private lemma pe8_Rts_eq {m n : ℕ} (M : Mat m n) (s : ℝ) : Rts M s = Rs Mᵀ s := by
  unfold Rts Rs
  rw [Matrix.transpose_transpose]

private lemma pe8_sigma_nonneg_gen {k l : ℕ} (Sg : Mat k k) (hS : Sg.PosSemidef) (B : ℕ)
    (hB : 0 < B) (M : Mat k l) (s : ℝ) (hs : 0 < s) :
    0 ≤ (B : ℝ)⁻¹ * (Sg * Rs M s).trace := by
  rw [← pe8_quad_trace Sg hS B hB s M]
  have h1 : (CFC.sqrt Sg * Rs M s * CFC.sqrt Sg).PosSemidef := by
    have := (pe8_Rs_psd M s hs).conjTranspose_mul_mul_same (CFC.sqrt Sg)
    have hh : (CFC.sqrt Sg)ᴴ = CFC.sqrt Sg :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Sg)).isHermitian
    rwa [hh] at this
  exact (h1.smul (by positivity)).trace_nonneg

private lemma pe8_sigmaS_nonneg {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (hB : 0 < B)
    (M0 : Mat m n) (s : ℝ) (hs : 0 < s) : 0 ≤ sigmaS Cv B M0 s := by
  unfold sigmaS
  exact pe8_sigma_nonneg_gen Cv.Sout Cv.psdOut B hB M0 s hs

private lemma pe8_sigmaT_nonneg {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (hB : 0 < B)
    (M0 : Mat m n) (s : ℝ) (hs : 0 < s) : 0 ≤ sigmaT Cv B M0 s := by
  unfold sigmaT
  rw [pe8_Rts_eq]
  exact pe8_sigma_nonneg_gen Cv.Sin Cv.psdIn B hB M0ᵀ s hs

private lemma pe8_quad_le {a : ℕ} (R : Mat a a) (hR : R.PosSemidef) (c : ℝ)
    (hc : opNorm R ≤ c) (u : Vec a) :
    dotProduct u (R *ᵥ u) ≤ c * ∑ i, u i ^ 2 := by
  have h0 : 0 ≤ dotProduct u (R *ᵥ u) := hR.dotProduct_mulVec_nonneg u
  have hcs : (dotProduct u (R *ᵥ u)) ^ 2 ≤ (∑ i, u i ^ 2) * (∑ i, (R *ᵥ u) i ^ 2) := by
    simpa [dotProduct] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u (R *ᵥ u)
  have h2 := pe8_sum_sq_mulVec_le R u
  have hon := pe8_opNorm_nonneg R
  have hS0 : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq : (dotProduct u (R *ᵥ u)) ^ 2 ≤ (c * ∑ i, u i ^ 2) ^ 2 := by
    calc _ ≤ (∑ i, u i ^ 2) * (∑ i, (R *ᵥ u) i ^ 2) := hcs
      _ ≤ (∑ i, u i ^ 2) * (opNorm R ^ 2 * ∑ i, u i ^ 2) := by gcongr
      _ ≤ (∑ i, u i ^ 2) * (c ^ 2 * ∑ i, u i ^ 2) := by gcongr
      _ = (c * ∑ i, u i ^ 2) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ h0 (mul_nonneg (hon.trans hc) hS0) (by norm_num)).mp hsq

private lemma pe8_sU_le {m n : ℕ} (M : Mat m n) (u : Vec m) (s : ℝ) (hs : 0 < s) :
    s * delU M u s ≤ ∑ i, u i ^ 2 := by
  have h := pe8_quad_le (Rs M s) (pe8_Rs_psd M s hs) (1 / s) (lem_app_de_resolvent M s hs).1 u
  unfold delU
  calc s * dotProduct u (Rs M s *ᵥ u) ≤ s * ((1 / s) * ∑ i, u i ^ 2) := by gcongr
    _ = ∑ i, u i ^ 2 := by field_simp

private lemma pe8_sV_le {m n : ℕ} (M : Mat m n) (v : Vec n) (s : ℝ) (hs : 0 < s) :
    s * delV M v s ≤ ∑ i, v i ^ 2 := by
  have := pe8_sU_le Mᵀ v s hs
  unfold delU at this
  unfold delV
  rw [pe8_Rts_eq]
  exact this

private lemma pe8_momN_eq {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (z : Vec m × Vec n) :
    momN Cv B z = sqNorm (sampU Cv B z) + sqNorm (sampV Cv B z) := by
  unfold momN eucNorm sqNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  rfl

private lemma pe8_sU_le_N {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (M0 : Mat m n)
    (z : Vec m × Vec n) (s : ℝ) (hs : 0 < s) :
    s * delU M0 (sampU Cv B z) s ≤ momN Cv B z := by
  have h := pe8_sU_le M0 (sampU Cv B z) s hs
  rw [pe8_momN_eq]
  have : 0 ≤ sqNorm (sampV Cv B z) := Finset.sum_nonneg fun i _ => sq_nonneg _
  unfold sqNorm
  unfold sqNorm at this
  linarith

private lemma pe8_sV_le_N {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (M0 : Mat m n)
    (z : Vec m × Vec n) (s : ℝ) (hs : 0 < s) :
    s * delV M0 (sampV Cv B z) s ≤ momN Cv B z := by
  have h := pe8_sV_le M0 (sampV Cv B z) s hs
  rw [pe8_momN_eq]
  have : 0 ≤ sqNorm (sampU Cv B z) := Finset.sum_nonneg fun i _ => sq_nonneg _
  unfold sqNorm
  unfold sqNorm at this
  linarith

private lemma pe8_Lam {m n : ℕ} (M0 : Mat m n) (h : ℝ) (u : Vec m) (v : Vec n) (s : ℝ)
    (hs : 0 < s) :
    0 < delLambda M0 h u v s ∧ (delLambda M0 h u v s)⁻¹ ≤
      (1 + 3 / (4 * Real.sqrt s) * |h| * (sqNorm u + sqNorm v)) ^ 2 := by
  obtain ⟨h1, -, -, -, h5⟩ := lem_app_de_deletion M0 h u v (M0 + h • outer u v) s rfl hs
  exact ⟨h1, h5⟩

private lemma pe8_cont_delU {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (M0 : Mat m n) (s : ℝ) :
    Continuous (fun z : Vec m × Vec n => delU M0 (sampU Cv B z) s) := by
  unfold delU sampU
  fun_prop

private lemma pe8_cont_delV {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (M0 : Mat m n) (s : ℝ) :
    Continuous (fun z : Vec m × Vec n => delV M0 (sampV Cv B z) s) := by
  unfold delV sampV
  fun_prop

private lemma pe8_cont_delC {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (M0 : Mat m n) (s : ℝ) :
    Continuous (fun z : Vec m × Vec n => delC M0 (sampU Cv B z) (sampV Cv B z) s) := by
  unfold delC sampU sampV
  fun_prop

private lemma pe8_cont_dAlpha {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (M0 : Mat m n)
    (Ah : Mat m n) (ϖ s : ℝ) (hs : 0 < s) (hϖ : ϖ ∈ Icc (0 : ℝ) 1) :
    Continuous (fun z : Vec m × Vec n =>
      dAlpha1 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)) ∧
    Continuous (fun z : Vec m × Vec n =>
      dAlpha2 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)) ∧
    Continuous (fun z : Vec m × Vec n =>
      dAlpha3 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)) := by
  have hU := pe8_cont_delU Cv B M0 s
  have hV := pe8_cont_delV Cv B M0 s
  have hC := pe8_cont_delC Cv B M0 s
  have hd := pe8_cont_resid Ah
  have hden : ∀ z : Vec m × Vec n,
      (delLambda M0 (ϖ * resid Ah z) (sampU Cv B z) (sampV Cv B z) s) ^ 2 ≠ 0 :=
    fun z => pow_ne_zero 2 (pe8_Lam _ _ _ _ s hs).1.ne'
  have hL : Continuous (fun z : Vec m × Vec n =>
      (delLambda M0 (ϖ * resid Ah z) (sampU Cv B z) (sampV Cv B z) s) ^ 2) := by
    unfold delLambda
    fun_prop
  refine ⟨?_, ?_, ?_⟩
  · have e : (fun z : Vec m × Vec n =>
        dAlpha1 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)) = fun z =>
        ϖ * ((1 + (ϖ * resid Ah z) * delC M0 (sampU Cv B z) (sampV Cv B z) s) ^ 2 -
          s * (ϖ * resid Ah z) ^ 2 * delU M0 (sampU Cv B z) s * delV M0 (sampV Cv B z) s) /
          (delLambda M0 (ϖ * resid Ah z) (sampU Cv B z) (sampV Cv B z) s) ^ 2 := by
      funext z
      exact (pe8_dAlpha_formula M0 ϖ s _ _ _ hs hϖ).1
    rw [e]
    exact Continuous.div (by fun_prop) hL hden
  · have e : (fun z : Vec m × Vec n =>
        dAlpha2 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)) = fun z =>
        2 * ϖ * (ϖ * resid Ah z) * delU M0 (sampU Cv B z) s *
          (1 + (ϖ * resid Ah z) * delC M0 (sampU Cv B z) (sampV Cv B z) s) /
          (delLambda M0 (ϖ * resid Ah z) (sampU Cv B z) (sampV Cv B z) s) ^ 2 := by
      funext z
      exact (pe8_dAlpha_formula M0 ϖ s _ _ _ hs hϖ).2.1
    rw [e]
    exact Continuous.div (by fun_prop) hL hden
  · have e : (fun z : Vec m × Vec n =>
        dAlpha3 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)) = fun z =>
        (-(2 * s * ϖ * (ϖ * resid Ah z) * delV M0 (sampV Cv B z) s *
          (1 + (ϖ * resid Ah z) * delC M0 (sampU Cv B z) (sampV Cv B z) s))) /
          (delLambda M0 (ϖ * resid Ah z) (sampU Cv B z) (sampV Cv B z) s) ^ 2 := by
      funext z
      exact (pe8_dAlpha_formula M0 ϖ s _ _ _ hs hϖ).2.2
    rw [e]
    exact Continuous.div (by fun_prop) hL hden

private lemma pe8_cont_deriv {m n : ℕ} (Ah : Mat m n) (x : ℝ) (hx : 0 ≤ x) :
    Continuous (fun z : Vec m × Vec n => deriv (fX x) (resid Ah z)) ∧
    Continuous (fun z : Vec m × Vec n => deriv (psiX x) (resid Ah z)) := by
  have hd := pe8_cont_resid Ah
  constructor
  · have e : (fun z : Vec m × Vec n => deriv (fX x) (resid Ah z)) = fun z =>
        (1 - x * resid Ah z ^ 2) / (1 + x * resid Ah z ^ 2) ^ 2 := by
      funext z
      exact pe8_fX_deriv x _ hx
    rw [e]
    exact Continuous.div (by fun_prop) (by fun_prop) (fun z => by positivity)
  · have e : (fun z : Vec m × Vec n => deriv (psiX x) (resid Ah z)) = fun z =>
        2 * resid Ah z / (1 + x * resid Ah z ^ 2) ^ 2 := by
      funext z
      exact pe8_psiX_deriv x _ hx
    rw [e]
    exact Continuous.div (by fun_prop) (by fun_prop) (fun z => by positivity)

private lemma pe8_scale_norm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (c : ℝ)
    (f : Ω → ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun z => c * f z) p μ = ENNReal.ofReal |c| * eLpNorm f p μ := by
  have := eLpNorm_const_smul (μ := μ) (p := p) c f
  rw [show (fun z => c * f z) = c • f by rfl, this]
  rw [Real.enorm_eq_ofReal_abs]

private lemma pe8_bound_prod {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f T E : Ω → ℝ) (c KT KE : ℝ) (hc : 0 ≤ c) (hKT : 0 ≤ KT) (hfm : AEStronglyMeasurable f μ)
    (hT : AEStronglyMeasurable T μ) (hE : AEStronglyMeasurable E μ) (pe : ℕ) (hpe : 1 ≤ pe)
    (h : ∀ z, |f z| ≤ c * (T z * E z))
    (hKT' : eLpNorm T ((2 * pe : ℕ) : ℝ≥0∞) μ ≤ ENNReal.ofReal KT)
    (hKE' : eLpNorm E ((2 * pe : ℕ) : ℝ≥0∞) μ ≤ ENNReal.ofReal KE) :
    eLpNorm f (pe : ℝ≥0∞) μ ≤ ENNReal.ofReal (c * KT * KE) := by
  by_cases hf : AEStronglyMeasurable f μ
  · have h1 : eLpNorm f (pe : ℝ≥0∞) μ ≤ eLpNorm (fun z => c * (T z * E z)) (pe : ℝ≥0∞) μ := by
      apply eLpNorm_mono_real hf
      intro z
      rw [Real.norm_eq_abs]
      exact h z
    have h2 := pe8_scale_norm (μ := μ) c (fun z => T z * E z) (pe : ℝ≥0∞)
    rw [abs_of_nonneg hc] at h2
    have h3 := pe8_holder T E hT hE pe hpe
    calc eLpNorm f (pe : ℝ≥0∞) μ ≤ eLpNorm (fun z => c * (T z * E z)) (pe : ℝ≥0∞) μ := h1
      _ = ENNReal.ofReal c * eLpNorm (fun z => T z * E z) (pe : ℝ≥0∞) μ := h2
      _ ≤ ENNReal.ofReal c * (eLpNorm T ((2 * pe : ℕ) : ℝ≥0∞) μ *
          eLpNorm E ((2 * pe : ℕ) : ℝ≥0∞) μ) := by gcongr
      _ ≤ ENNReal.ofReal c * (ENNReal.ofReal KT * ENNReal.ofReal KE) := by gcongr
      _ = ENNReal.ofReal (c * KT * KE) := by
          rw [← ENNReal.ofReal_mul hKT, ← ENNReal.ofReal_mul hc, mul_assoc]
  · exact absurd hfm hf

private lemma pe8_bound_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f T : Ω → ℝ) (c KT : ℝ) (hc : 0 ≤ c) (hfm : AEStronglyMeasurable f μ) (pe : ℕ)
    (h : ∀ z, |f z| ≤ c * T z)
    (hKT' : eLpNorm T (pe : ℝ≥0∞) μ ≤ ENNReal.ofReal KT) :
    eLpNorm f (pe : ℝ≥0∞) μ ≤ ENNReal.ofReal (c * KT) := by
  by_cases hf : AEStronglyMeasurable f μ
  · have h1 : eLpNorm f (pe : ℝ≥0∞) μ ≤ eLpNorm (fun z => c * T z) (pe : ℝ≥0∞) μ := by
      apply eLpNorm_mono_real hf
      intro z
      rw [Real.norm_eq_abs]
      exact h z
    have h2 := pe8_scale_norm (μ := μ) c T (pe : ℝ≥0∞)
    rw [abs_of_nonneg hc] at h2
    calc eLpNorm f (pe : ℝ≥0∞) μ ≤ eLpNorm (fun z => c * T z) (pe : ℝ≥0∞) μ := h1
      _ = ENNReal.ofReal c * eLpNorm T (pe : ℝ≥0∞) μ := h2
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal KT := by gcongr
      _ = ENNReal.ofReal (c * KT) := by rw [← ENNReal.ofReal_mul hc]
  · exact absurd hfm hf

private lemma pe8_const_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X N : Ω → ℝ) (c e DN : ℝ)
    (hX : AEStronglyMeasurable X μ) (hX0 : ∀ z, 0 ≤ X z) (hXN : ∀ z, X z ≤ N z)
    (hc : 0 ≤ c) (he : 0 ≤ e)
    (hN : eLpNorm N 1 μ ≤ ENNReal.ofReal DN)
    (hXc : eLpNorm (fun z => X z - c) 1 μ ≤ ENNReal.ofReal e) :
    c ≤ max DN 0 + e := by
  have hconst : eLpNorm (fun _ : Ω => c) 1 μ = ENNReal.ofReal c := by
    rw [eLpNorm_const _ (by simp) (IsProbabilityMeasure.ne_zero μ)]
    simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg hc]
  have hmeas : AEStronglyMeasurable (fun z => X z - c) μ := hX.sub aestronglyMeasurable_const
  have h1 : eLpNorm (fun _ : Ω => c) 1 μ ≤ eLpNorm (fun z => X z + |X z - c|) 1 μ := by
    apply eLpNorm_mono_real aestronglyMeasurable_const
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg hc]
    have := hX0 z
    have h3 : c ≤ X z + |X z - c| := by
      have := neg_abs_le (X z - c)
      linarith [le_abs_self (X z - c), neg_abs_le (X z - c)]
    exact h3
  have h2 : eLpNorm (fun z => X z + |X z - c|) 1 μ ≤
      eLpNorm X 1 μ + eLpNorm (fun z => |X z - c|) 1 μ :=
    eLpNorm_add_le (f := X) (g := fun z => |X z - c|) (μ := μ) le_rfl
  have h3 : eLpNorm (fun z => |X z - c|) 1 μ = eLpNorm (fun z => X z - c) 1 μ := by
    have := eLpNorm_norm (μ := μ) (p := 1) (fun z => X z - c) hmeas
    simpa [Real.norm_eq_abs] using this
  have h4 : eLpNorm X 1 μ ≤ eLpNorm N 1 μ := by
    apply eLpNorm_mono_real hX
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 z)]
    exact hXN z
  have h5 : ENNReal.ofReal c ≤ ENNReal.ofReal (max DN 0) + ENNReal.ofReal e := by
    calc ENNReal.ofReal c = eLpNorm (fun _ : Ω => c) 1 μ := hconst.symm
      _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ eLpNorm N 1 μ + eLpNorm (fun z => X z - c) 1 μ := by rw [h3]; gcongr
      _ ≤ ENNReal.ofReal DN + ENNReal.ofReal e := by gcongr
      _ ≤ ENNReal.ofReal (max DN 0) + ENNReal.ofReal e := by
          gcongr
          exact le_max_left _ _
  rw [← ENNReal.ofReal_add (le_max_right _ _) he] at h5
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h5

private lemma pe8_sigma_bound (cert : Muon.External.GaussianQuadFormLp) (γ CS : ℝ) :
    ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ {m n : ℕ} (Cv : Covariances m n) (B : ℕ), 0 < B →
      ∀ (M0 : Mat m n) (s : ℝ), 0 < s →
      opNorm Cv.Sout ≤ CS → opNorm Cv.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      s * sigmaS Cv B M0 s ≤ K1 ∧ s * sigmaT Cv B M0 s ≤ K1 := by
  obtain ⟨KU, hKU0, hKU⟩ := pe8_U_concentration cert 1 le_rfl
  obtain ⟨KV, hKV0, hKV⟩ := pe8_V_concentration cert 1 le_rfl
  refine ⟨max (2 * CS * γ * ((Nat.doubleFactorial (2 * 1 - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / ((1 : ℕ) : ℝ))) 0
    + (KU + KV) * Real.sqrt γ * max CS 0, by positivity, ?_⟩
  intro m n Cv B hB M0 s hs hCo hCi hm hn
  have hCS : 0 ≤ CS := (pe8_opNorm_nonneg _).trans hCo
  have hBr : 1 ≤ Real.sqrt (B : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hB)
  have hBr0 : 0 < Real.sqrt (B : ℝ) := by linarith
  have hN1 := lem_app_de_moments_i Cv B γ CS ⟨hm, hn⟩ ⟨hCo, hCi⟩ 1 le_rfl
  have hU1 := hKU s hs γ CS Cv B hB M0 s hCo hm le_rfl
  have hV1 := hKV s hs γ CS Cv B hB M0 s hCi hn le_rfl
  rw [Nat.cast_one] at hN1 hU1 hV1
  have hsg : 0 ≤ Real.sqrt γ := Real.sqrt_nonneg _
  have hCm : CS ≤ max CS 0 := le_max_left _ _
  have hCm0 : 0 ≤ max CS 0 := le_max_right _ _
  have hσU := pe8_sigmaS_nonneg Cv B hB M0 s hs
  have hσV := pe8_sigmaT_nonneg Cv B hB M0 s hs
  -- the e term
  have heU : 0 ≤ KU * Real.sqrt γ * CS / Real.sqrt B := by positivity
  have heV : 0 ≤ KV * Real.sqrt γ * CS / Real.sqrt B := by positivity
  have hscaleU : eLpNorm (fun z : Vec m × Vec n => s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s)
      1 (gaussPair m n) ≤ ENNReal.ofReal (KU * Real.sqrt γ * CS / Real.sqrt B) := by
    have e1 : (fun z : Vec m × Vec n => s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s) =
        fun z => s * (delU M0 (sampU Cv B z) s - sigmaS Cv B M0 s) := by
      funext z; ring
    rw [e1, pe8_scale_norm, abs_of_pos hs]
    calc ENNReal.ofReal s * _ ≤ ENNReal.ofReal s * ENNReal.ofReal (KU * Real.sqrt γ * CS / s / Real.sqrt B) := by
          gcongr
      _ = ENNReal.ofReal (KU * Real.sqrt γ * CS / Real.sqrt B) := by
          rw [← ENNReal.ofReal_mul hs.le]
          congr 1
          field_simp
  have hscaleV : eLpNorm (fun z : Vec m × Vec n => s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s)
      1 (gaussPair m n) ≤ ENNReal.ofReal (KV * Real.sqrt γ * CS / Real.sqrt B) := by
    have e1 : (fun z : Vec m × Vec n => s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s) =
        fun z => s * (delV M0 (sampV Cv B z) s - sigmaT Cv B M0 s) := by
      funext z; ring
    rw [e1, pe8_scale_norm, abs_of_pos hs]
    calc ENNReal.ofReal s * _ ≤ ENNReal.ofReal s * ENNReal.ofReal (KV * Real.sqrt γ * CS / s / Real.sqrt B) := by
          gcongr
      _ = ENNReal.ofReal (KV * Real.sqrt γ * CS / Real.sqrt B) := by
          rw [← ENNReal.ofReal_mul hs.le]
          congr 1
          field_simp
  have h1 := pe8_const_le (μ := gaussPair m n)
    (fun z => s * delU M0 (sampU Cv B z) s) (momN Cv B) (s * sigmaS Cv B M0 s) _ _
    ((pe8_cont_delU Cv B M0 s).const_smul s |>.aestronglyMeasurable)
    (fun z => mul_nonneg hs.le (pe8_delU_nonneg M0 _ s hs))
    (fun z => pe8_sU_le_N Cv B M0 z s hs) (mul_nonneg hs.le hσU) heU hN1 hscaleU
  have h2 := pe8_const_le (μ := gaussPair m n)
    (fun z => s * delV M0 (sampV Cv B z) s) (momN Cv B) (s * sigmaT Cv B M0 s) _ _
    ((pe8_cont_delV Cv B M0 s).const_smul s |>.aestronglyMeasurable)
    (fun z => mul_nonneg hs.le (pe8_delV_nonneg M0 _ s hs))
    (fun z => pe8_sV_le_N Cv B M0 z s hs) (mul_nonneg hs.le hσV) heV hN1 hscaleV
  have hb : ∀ K : ℝ, 0 ≤ K → K * Real.sqrt γ * CS / Real.sqrt B ≤ K * Real.sqrt γ * max CS 0 := by
    intro K hK
    calc K * Real.sqrt γ * CS / Real.sqrt B ≤ K * Real.sqrt γ * CS := div_le_self (by positivity) hBr
      _ ≤ K * Real.sqrt γ * max CS 0 := by gcongr
  have hKUV : KU * Real.sqrt γ * max CS 0 ≤ (KU + KV) * Real.sqrt γ * max CS 0 := by
    have : 0 ≤ KV * Real.sqrt γ * max CS 0 := by positivity
    nlinarith
  have hKVU : KV * Real.sqrt γ * max CS 0 ≤ (KU + KV) * Real.sqrt γ * max CS 0 := by
    have : 0 ≤ KU * Real.sqrt γ * max CS 0 := by positivity
    nlinarith
  constructor
  · have := hb KU hKU0
    linarith
  · have := hb KV hKV0
    linarith

private lemma pe8_err_moment (cert : Muon.External.GaussianQuadFormLp) (q : ℕ) (hq : 1 ≤ q)
    (γ CS : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {m n : ℕ} (Cv : Covariances m n) (B : ℕ), 0 < B →
      ∀ (M0 : Mat m n) (s : ℝ), 0 < s →
      opNorm Cv.Sout ≤ CS → opNorm Cv.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      eLpNorm (fun z : Vec m × Vec n =>
        |s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s| +
        |s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s| +
        Real.sqrt s * |delC M0 (sampU Cv B z) (sampV Cv B z) s|) (q : ℝ≥0∞) (gaussPair m n)
        ≤ ENNReal.ofReal (K / Real.sqrt B) := by
  obtain ⟨KU, hKU0, hKU⟩ := pe8_U_concentration cert q hq
  obtain ⟨KV, hKV0, hKV⟩ := pe8_V_concentration cert q hq
  obtain ⟨KC, hKC0, hKC⟩ := pe8_C_concentration cert q hq
  refine ⟨(KU + KV + KC) * Real.sqrt γ * max CS 0, by positivity, ?_⟩
  intro m n Cv B hB M0 s hs hCo hCi hm hn
  have hCS : 0 ≤ CS := (pe8_opNorm_nonneg _).trans hCo
  have hBr : 1 ≤ Real.sqrt (B : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hB)
  have hBr0 : 0 < Real.sqrt (B : ℝ) := by linarith
  have hsq0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsg : 0 ≤ Real.sqrt γ := Real.sqrt_nonneg _
  have hU1 := hKU s hs γ CS Cv B hB M0 s hCo hm le_rfl
  have hV1 := hKV s hs γ CS Cv B hB M0 s hCi hn le_rfl
  have hC1 := hKC s hs γ CS Cv B hB M0 s hCo hCi hn le_rfl
  have hqe : (1 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by exact_mod_cast hq
  have mU : AEStronglyMeasurable (fun z : Vec m × Vec n => delU M0 (sampU Cv B z) s - sigmaS Cv B M0 s)
      (gaussPair m n) := ((pe8_cont_delU Cv B M0 s).sub continuous_const).aestronglyMeasurable
  have mV : AEStronglyMeasurable (fun z : Vec m × Vec n => delV M0 (sampV Cv B z) s - sigmaT Cv B M0 s)
      (gaussPair m n) := ((pe8_cont_delV Cv B M0 s).sub continuous_const).aestronglyMeasurable
  have mC : AEStronglyMeasurable (fun z : Vec m × Vec n => delC M0 (sampU Cv B z) (sampV Cv B z) s)
      (gaussPair m n) := (pe8_cont_delC Cv B M0 s).aestronglyMeasurable
  have tU : eLpNorm (fun z : Vec m × Vec n => |s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s|)
      (q : ℝ≥0∞) (gaussPair m n) ≤ ENNReal.ofReal (KU * Real.sqrt γ * CS / Real.sqrt B) := by
    have e1 : (fun z : Vec m × Vec n => |s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s|) =
        fun z => |s * (delU M0 (sampU Cv B z) s - sigmaS Cv B M0 s)| := by
      funext z; rw [mul_sub]
    rw [e1, pe8_abs_scale _ _ mU, abs_of_pos hs]
    calc ENNReal.ofReal s * _ ≤ ENNReal.ofReal s * ENNReal.ofReal (KU * Real.sqrt γ * CS / s / Real.sqrt B) := by
          gcongr
      _ = ENNReal.ofReal (KU * Real.sqrt γ * CS / Real.sqrt B) := by
          rw [← ENNReal.ofReal_mul hs.le]
          congr 1
          field_simp
  have tV : eLpNorm (fun z : Vec m × Vec n => |s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s|)
      (q : ℝ≥0∞) (gaussPair m n) ≤ ENNReal.ofReal (KV * Real.sqrt γ * CS / Real.sqrt B) := by
    have e1 : (fun z : Vec m × Vec n => |s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s|) =
        fun z => |s * (delV M0 (sampV Cv B z) s - sigmaT Cv B M0 s)| := by
      funext z; rw [mul_sub]
    rw [e1, pe8_abs_scale _ _ mV, abs_of_pos hs]
    calc ENNReal.ofReal s * _ ≤ ENNReal.ofReal s * ENNReal.ofReal (KV * Real.sqrt γ * CS / s / Real.sqrt B) := by
          gcongr
      _ = ENNReal.ofReal (KV * Real.sqrt γ * CS / Real.sqrt B) := by
          rw [← ENNReal.ofReal_mul hs.le]
          congr 1
          field_simp
  have tC : eLpNorm (fun z : Vec m × Vec n => Real.sqrt s * |delC M0 (sampU Cv B z) (sampV Cv B z) s|)
      (q : ℝ≥0∞) (gaussPair m n) ≤
      ENNReal.ofReal (KC * CS * Real.sqrt γ / 2 / Real.sqrt B) := by
    have e1 : (fun z : Vec m × Vec n => Real.sqrt s * |delC M0 (sampU Cv B z) (sampV Cv B z) s|) =
        fun z => |Real.sqrt s * delC M0 (sampU Cv B z) (sampV Cv B z) s| := by
      funext z; rw [abs_mul, abs_of_pos hsq0]
    rw [e1, pe8_abs_scale _ _ mC, abs_of_pos hsq0]
    calc ENNReal.ofReal (Real.sqrt s) * _ ≤ ENNReal.ofReal (Real.sqrt s) *
          ENNReal.ofReal (KC * (CS * Real.sqrt γ / (2 * Real.sqrt s)) / Real.sqrt B) := by gcongr
      _ = ENNReal.ofReal (KC * CS * Real.sqrt γ / 2 / Real.sqrt B) := by
          rw [← ENNReal.ofReal_mul hsq0.le]
          congr 1
          field_simp
  have hsum : eLpNorm (fun z : Vec m × Vec n =>
        |s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s| +
        |s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s| +
        Real.sqrt s * |delC M0 (sampU Cv B z) (sampV Cv B z) s|) (q : ℝ≥0∞) (gaussPair m n) ≤
      eLpNorm (fun z : Vec m × Vec n => |s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s|)
        (q : ℝ≥0∞) (gaussPair m n) +
      eLpNorm (fun z : Vec m × Vec n => |s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s|)
        (q : ℝ≥0∞) (gaussPair m n) +
      eLpNorm (fun z : Vec m × Vec n => Real.sqrt s * |delC M0 (sampU Cv B z) (sampV Cv B z) s|)
        (q : ℝ≥0∞) (gaussPair m n) := by
    refine (eLpNorm_add_le (f := fun z : Vec m × Vec n =>
        |s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s| +
        |s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s|)
      (g := fun z : Vec m × Vec n => Real.sqrt s * |delC M0 (sampU Cv B z) (sampV Cv B z) s|)
      hqe).trans ?_
    gcongr
    exact eLpNorm_add_le (f := fun z : Vec m × Vec n =>
        |s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s|)
      (g := fun z : Vec m × Vec n => |s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s|) hqe
  refine hsum.trans ?_
  have hpos1 : 0 ≤ KU * Real.sqrt γ * CS / Real.sqrt B := by positivity
  have hpos2 : 0 ≤ KV * Real.sqrt γ * CS / Real.sqrt B := by positivity
  have hpos3 : 0 ≤ KC * CS * Real.sqrt γ / 2 / Real.sqrt B := by positivity
  calc _ ≤ ENNReal.ofReal (KU * Real.sqrt γ * CS / Real.sqrt B) +
        ENNReal.ofReal (KV * Real.sqrt γ * CS / Real.sqrt B) +
        ENNReal.ofReal (KC * CS * Real.sqrt γ / 2 / Real.sqrt B) := by gcongr
    _ = ENNReal.ofReal (KU * Real.sqrt γ * CS / Real.sqrt B + KV * Real.sqrt γ * CS / Real.sqrt B
        + KC * CS * Real.sqrt γ / 2 / Real.sqrt B) := by
        rw [ENNReal.ofReal_add (by positivity) hpos3, ENNReal.ofReal_add hpos1 hpos2]
    _ ≤ ENNReal.ofReal ((KU + KV + KC) * Real.sqrt γ * max CS 0 / Real.sqrt B) := by
        apply ENNReal.ofReal_le_ofReal
        have hCm : CS ≤ max CS 0 := le_max_left _ _
        have : KU * Real.sqrt γ * CS / Real.sqrt B + KV * Real.sqrt γ * CS / Real.sqrt B
            + KC * CS * Real.sqrt γ / 2 / Real.sqrt B =
            (KU * Real.sqrt γ * CS + KV * Real.sqrt γ * CS + KC * CS * Real.sqrt γ / 2) / Real.sqrt B := by
          ring
        rw [this]
        apply div_le_div_of_nonneg_right _ hBr0.le
        have hh : KC * CS * Real.sqrt γ / 2 ≤ KC * Real.sqrt γ * CS := by
          have : 0 ≤ KC * Real.sqrt γ * CS := by positivity
          nlinarith
        have h1 : KU * Real.sqrt γ * CS ≤ KU * Real.sqrt γ * max CS 0 := by gcongr
        have h2 : KV * Real.sqrt γ * CS ≤ KV * Real.sqrt γ * max CS 0 := by gcongr
        have h3 : KC * Real.sqrt γ * CS ≤ KC * Real.sqrt γ * max CS 0 := by gcongr
        nlinarith

private lemma pe8_point (s0 K1 : ℝ) (hs0 : 0 < s0) (hK1 : 0 ≤ K1) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ {m n : ℕ} (M0 : Mat m n) (ϖ s : ℝ) (u : Vec m) (v : Vec n) (d σ σt N x : ℝ),
      s0 ≤ s → 0 ≤ ϖ → ϖ ≤ 1 → 0 ≤ σ → 0 ≤ σt → s * delU M0 u s ≤ N → s * delV M0 v s ≤ N →
      0 ≤ N → s * σ ≤ K1 → s * σt ≤ K1 → x = ϖ ^ 2 * s * σ * σt →
      (delLambda M0 (ϖ * d) u v s)⁻¹ ≤ (1 + 3 / (4 * Real.sqrt s) * |ϖ * d| * N) ^ 2 →
      |dAlpha1 M0 ϖ s u v d - ϖ * deriv (fX x) d| ≤
        (ϖ * κ) * (((1 + |d|) * (1 + N)) ^ 8 *
          (|s * delU M0 u s - s * σ| + |s * delV M0 v s - s * σt| +
            Real.sqrt s * |delC M0 u v s|)) ∧
      |dAlpha2 M0 ϖ s u v d - ϖ ^ 2 * σ * deriv (psiX x) d| ≤
        (ϖ ^ 2 * κ / s) * (((1 + |d|) * (1 + N)) ^ 8 *
          (|s * delU M0 u s - s * σ| + |s * delV M0 v s - s * σt| +
            Real.sqrt s * |delC M0 u v s|)) ∧
      |dAlpha3 M0 ϖ s u v d + s * ϖ ^ 2 * σt * deriv (psiX x) d| ≤
        (ϖ ^ 2 * κ) * (((1 + |d|) * (1 + N)) ^ 8 *
          (|s * delU M0 u s - s * σ| + |s * delV M0 v s - s * σt| +
            Real.sqrt s * |delC M0 u v s|)) ∧
      |dAlpha1 M0 ϖ s u v d| ≤ (ϖ * κ) * ((1 + |d|) * (1 + N)) ^ 8 ∧
      |dAlpha2 M0 ϖ s u v d| ≤ (ϖ ^ 2 * κ / s) * ((1 + |d|) * (1 + N)) ^ 8 ∧
      |dAlpha3 M0 ϖ s u v d| ≤ (ϖ ^ 2 * κ) * ((1 + |d|) * (1 + N)) ^ 8 := by
  obtain ⟨κ, hκ0, hκ⟩ := pe8_master s0 K1 hs0 hK1
  refine ⟨κ, hκ0, ?_⟩
  intro m n M0 ϖ s u v d σ σt N x hs hϖ0 hϖ1 hσ hσt hUN hVN hN hσK hσtK hx hinv
  have hs_pos : 0 < s := lt_of_lt_of_le hs0 hs
  obtain ⟨f1, f2, f3⟩ := pe8_dAlpha_formula M0 ϖ s u v d hs_pos ⟨hϖ0, hϖ1⟩
  have hLpos : 0 < delLambda M0 (ϖ * d) u v s := (pe8_Lam M0 (ϖ * d) u v s hs_pos).1
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hU := pe8_delU_nonneg M0 u s hs_pos
  have hV := pe8_delV_nonneg M0 v s hs_pos
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hκ s ϖ d (delU M0 u s) (delV M0 v s) (delC M0 u v s) σ σt N
    ((1 + |d|) * (1 + N))
    (|s * delU M0 u s - s * σ| + |s * delV M0 v s - s * σt| + Real.sqrt s * |delC M0 u v s|) x
    hs hϖ0 hϖ1 hU hV hσ hσt hUN hVN hN hσK hσtK hLpos hinv rfl rfl hx
  rw [pe8_fX_deriv x d hx0, pe8_psiX_deriv x d hx0]
  rw [f1, f2, f3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact c1.trans (le_of_eq (by ring))
  · exact c2.trans (le_of_eq (by ring))
  · exact c3.trans (le_of_eq (by ring))
  · exact c4.trans (le_of_eq (by ring))
  · exact c5.trans (le_of_eq (by ring))
  · exact c6.trans (le_of_eq (by ring))

/-- `lem:app-dyn-coefficients`, snapshot `cr-2026-10-23`. Statement verbatim from `section.tex` (ll. 1136–1151):
```latex
\begin{lemma}[Derivative coefficients]\label{lem:app-dyn-coefficients}
Let $s_\circ>0$ and $p\ge1$. In the setting of \cref{lem:app-dyn-derivative},
let $M_0$ be fixed, $(\mathsf u,\mathsf v)=(\Sigmaout^{1/2}z/\sqrt B,\Sigmain^{1/2}w/\sqrt B)$
and $d=z^\T\widehat Aw$ with $(z,w)$ standard Gaussian and $\norm{\widehat A}_\F=1$.
For $s\ge s_\circ$ and $\varpi\in[0,1]$,
\[
\begin{gathered}
\norm{\partial_d\alpha_1-\varpi f_x'(d)}_p\le\frac{C\varpi}{\sqrt B},\qquad
\norm{\partial_d\alpha_2-\varpi^2\sigma\psi_x'(d)}_p\le\frac{C\varpi^2}{s\sqrt B},\\
\norm{\partial_d\alpha_3+s\varpi^2\tilde\sigma\psi_x'(d)}_p\le\frac{C\varpi^2}{\sqrt B},
\end{gathered}
\]
and $\norm{\partial_d\alpha_1}_p\le C\varpi$, $\norm{\partial_d\alpha_2}_p\le C\varpi^2/s$,
$\norm{\partial_d\alpha_3}_p\le C\varpi^2$, with $C$ depending only on
$(p,s_\circ,\gamma_\star,C_\Sigma)$.
\end{lemma}
```
-/
theorem lem_app_dyn_coefficients (cert : Muon.External.GaussianQuadFormLp) (pe : ℕ)
    (hpe : 1 ≤ pe) (s0 : ℝ) (hs0 : 0 < s0) (γ CS : ℝ) :
    ∃ C : ℝ, ∀ (m n B : ℕ) (Cv : Covariances m n) (M0 Ah : Mat m n) (ϖ s : ℝ), 0 < B →
      opNorm Cv.Sout ≤ CS → opNorm Cv.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      fro Ah = 1 → s0 ≤ s → ϖ ∈ Icc (0 : ℝ) 1 →
      eLpNorm (fun z : Vec m × Vec n => dAlpha1 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)
          - ϖ * deriv (fX (xMinor Cv B M0 ϖ s)) (resid Ah z)) (pe : ℝ≥0∞) (gaussPair m n)
        ≤ ENNReal.ofReal (C * ϖ / Real.sqrt B) ∧
      eLpNorm (fun z : Vec m × Vec n => dAlpha2 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)
          - ϖ ^ 2 * sigmaS Cv B M0 s * deriv (psiX (xMinor Cv B M0 ϖ s)) (resid Ah z))
          (pe : ℝ≥0∞) (gaussPair m n)
        ≤ ENNReal.ofReal (C * ϖ ^ 2 / (s * Real.sqrt B)) ∧
      eLpNorm (fun z : Vec m × Vec n => dAlpha3 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)
          + s * ϖ ^ 2 * sigmaT Cv B M0 s * deriv (psiX (xMinor Cv B M0 ϖ s)) (resid Ah z))
          (pe : ℝ≥0∞) (gaussPair m n)
        ≤ ENNReal.ofReal (C * ϖ ^ 2 / Real.sqrt B) ∧
      eLpNorm (fun z : Vec m × Vec n => dAlpha1 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z))
          (pe : ℝ≥0∞) (gaussPair m n) ≤ ENNReal.ofReal (C * ϖ) ∧
      eLpNorm (fun z : Vec m × Vec n => dAlpha2 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z))
          (pe : ℝ≥0∞) (gaussPair m n) ≤ ENNReal.ofReal (C * ϖ ^ 2 / s) ∧
      eLpNorm (fun z : Vec m × Vec n => dAlpha3 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z))
          (pe : ℝ≥0∞) (gaussPair m n) ≤ ENNReal.ofReal (C * ϖ ^ 2) := by
  obtain ⟨K1, hK1, hσb⟩ := pe8_sigma_bound cert γ CS
  obtain ⟨κ, hκ0, hκ⟩ := pe8_point s0 K1 hs0 hK1
  obtain ⟨KT, hKT0, hKT⟩ := pe8_t_moment 8 (2 * pe) (by norm_num) (by omega) γ CS
  obtain ⟨KT1, hKT10, hKT1⟩ := pe8_t_moment 8 pe (by norm_num) hpe γ CS
  obtain ⟨KE, hKE0, hKE⟩ := pe8_err_moment cert (2 * pe) (by omega) γ CS
  refine ⟨κ * KT * KE + κ * KT1, ?_⟩
  intro m n B Cv M0 Ah ϖ s hB hCo hCi hm hn hA hs hϖ
  have hs_pos : 0 < s := lt_of_lt_of_le hs0 hs
  obtain ⟨hϖ0, hϖ1⟩ := hϖ
  have hBr0 : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hB)
  have hσ0 := pe8_sigmaS_nonneg Cv B hB M0 s hs_pos
  have hσt0 := pe8_sigmaT_nonneg Cv B hB M0 s hs_pos
  obtain ⟨hσK, hσtK⟩ := hσb Cv B hB M0 s hs_pos hCo hCi hm hn
  have hKTz := hKT Cv Ah hA hm hn hCo hCi
  have hKT1z := hKT1 Cv Ah hA hm hn hCo hCi
  have hKEz := hKE Cv B hB M0 s hs_pos hCo hCi hm hn
  -- measurability
  have mT : AEStronglyMeasurable (fun z : Vec m × Vec n =>
      ((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ 8) (gaussPair m n) :=
    (by have := pe8_cont_resid Ah; have := pe8_cont_momN Cv B; fun_prop :
      Continuous fun z : Vec m × Vec n => ((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ 8).aestronglyMeasurable
  have mE : AEStronglyMeasurable (fun z : Vec m × Vec n =>
        |s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s| +
        |s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s| +
        Real.sqrt s * |delC M0 (sampU Cv B z) (sampV Cv B z) s|) (gaussPair m n) := by
    have h1 := pe8_cont_delU Cv B M0 s
    have h2 := pe8_cont_delV Cv B M0 s
    have h3 := pe8_cont_delC Cv B M0 s
    exact (by fun_prop : Continuous fun z : Vec m × Vec n =>
        |s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s| +
        |s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s| +
        Real.sqrt s * |delC M0 (sampU Cv B z) (sampV Cv B z) s|).aestronglyMeasurable
  -- pointwise bounds
  have pt : ∀ z : Vec m × Vec n,
      (|dAlpha1 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)
          - ϖ * deriv (fX (xMinor Cv B M0 ϖ s)) (resid Ah z)| ≤
        (ϖ * κ) * (((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ 8 *
          (|s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s| +
           |s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s| +
           Real.sqrt s * |delC M0 (sampU Cv B z) (sampV Cv B z) s|))) ∧
      (|dAlpha2 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)
          - ϖ ^ 2 * sigmaS Cv B M0 s * deriv (psiX (xMinor Cv B M0 ϖ s)) (resid Ah z)| ≤
        (ϖ ^ 2 * κ / s) * (((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ 8 *
          (|s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s| +
           |s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s| +
           Real.sqrt s * |delC M0 (sampU Cv B z) (sampV Cv B z) s|))) ∧
      (|dAlpha3 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)
          + s * ϖ ^ 2 * sigmaT Cv B M0 s * deriv (psiX (xMinor Cv B M0 ϖ s)) (resid Ah z)| ≤
        (ϖ ^ 2 * κ) * (((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ 8 *
          (|s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s| +
           |s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s| +
           Real.sqrt s * |delC M0 (sampU Cv B z) (sampV Cv B z) s|))) ∧
      (|dAlpha1 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)| ≤
        (ϖ * κ) * ((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ 8) ∧
      (|dAlpha2 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)| ≤
        (ϖ ^ 2 * κ / s) * ((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ 8) ∧
      (|dAlpha3 M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)| ≤
        (ϖ ^ 2 * κ) * ((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ 8) := by
    intro z
    have hLam := pe8_Lam M0 (ϖ * resid Ah z) (sampU Cv B z) (sampV Cv B z) s hs_pos
    rw [← pe8_momN_eq] at hLam
    exact hκ M0 ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) (sigmaS Cv B M0 s)
      (sigmaT Cv B M0 s) (momN Cv B z) (xMinor Cv B M0 ϖ s) hs hϖ0 hϖ1 hσ0 hσt0
      (pe8_sU_le_N Cv B M0 z s hs_pos) (pe8_sV_le_N Cv B M0 z s hs_pos)
      (by rw [pe8_momN_eq]; unfold sqNorm; positivity) hσK hσtK rfl hLam.2
  have hC0 : 0 ≤ κ * KT * KE + κ * KT1 := by positivity
  have hKEs : eLpNorm (fun z : Vec m × Vec n =>
        |s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s| +
        |s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s| +
        Real.sqrt s * |delC M0 (sampU Cv B z) (sampV Cv B z) s|)
      ((2 * pe : ℕ) : ℝ≥0∞) (gaussPair m n) ≤ ENNReal.ofReal (KE / Real.sqrt B) := hKEz
  have hx0 : 0 ≤ xMinor Cv B M0 ϖ s := by
    unfold xMinor
    positivity
  obtain ⟨mα1, mα2, mα3⟩ := pe8_cont_dAlpha Cv B M0 Ah ϖ s hs_pos ⟨hϖ0, hϖ1⟩
  obtain ⟨mf, mψ⟩ := pe8_cont_deriv (m := m) (n := n) Ah (xMinor Cv B M0 ϖ s) hx0
  have hbp : ∀ (f : Vec m × Vec n → ℝ) (c : ℝ), 0 ≤ c → AEStronglyMeasurable f (gaussPair m n) →
      (∀ z, |f z| ≤ c * (((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ 8 *
          (|s * delU M0 (sampU Cv B z) s - s * sigmaS Cv B M0 s| +
           |s * delV M0 (sampV Cv B z) s - s * sigmaT Cv B M0 s| +
           Real.sqrt s * |delC M0 (sampU Cv B z) (sampV Cv B z) s|))) →
      eLpNorm f (pe : ℝ≥0∞) (gaussPair m n) ≤ ENNReal.ofReal (c * KT * (KE / Real.sqrt B)) :=
    fun f c hc hfm h => pe8_bound_prod f _ _ c KT (KE / Real.sqrt B) hc hKT0 hfm mT mE pe hpe h hKTz hKEs
  have hbo : ∀ (f : Vec m × Vec n → ℝ) (c : ℝ), 0 ≤ c → AEStronglyMeasurable f (gaussPair m n) →
      (∀ z, |f z| ≤ c * (((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ 8)) →
      eLpNorm f (pe : ℝ≥0∞) (gaussPair m n) ≤ ENNReal.ofReal (c * KT1) :=
    fun f c hc hfm h => pe8_bound_one f _ c KT1 hc hfm pe h hKT1z
  have hKEB : 0 ≤ KE / Real.sqrt B := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (hbp _ (ϖ * κ) (by positivity)
      (mα1.sub (continuous_const.mul mf)).aestronglyMeasurable (fun z => (pt z).1)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ ϖ * κ * KT1 / Real.sqrt B := by positivity
    calc ϖ * κ * KT * (KE / Real.sqrt B) ≤ ϖ * κ * KT * (KE / Real.sqrt B) + ϖ * κ * KT1 / Real.sqrt B := by
          linarith
      _ = (κ * KT * KE + κ * KT1) * ϖ / Real.sqrt B := by ring
  · refine (hbp _ (ϖ ^ 2 * κ / s) (by positivity)
      (mα2.sub (continuous_const.mul mψ)).aestronglyMeasurable (fun z => (pt z).2.1)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ ϖ ^ 2 * κ * KT1 / (s * Real.sqrt B) := by positivity
    calc ϖ ^ 2 * κ / s * KT * (KE / Real.sqrt B) ≤
          ϖ ^ 2 * κ / s * KT * (KE / Real.sqrt B) + ϖ ^ 2 * κ * KT1 / (s * Real.sqrt B) := by
          linarith
      _ = (κ * KT * KE + κ * KT1) * ϖ ^ 2 / (s * Real.sqrt B) := by
          field_simp
  · refine (hbp _ (ϖ ^ 2 * κ) (by positivity)
      (mα3.add (continuous_const.mul mψ)).aestronglyMeasurable (fun z => (pt z).2.2.1)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ ϖ ^ 2 * κ * KT1 / Real.sqrt B := by positivity
    calc ϖ ^ 2 * κ * KT * (KE / Real.sqrt B) ≤
          ϖ ^ 2 * κ * KT * (KE / Real.sqrt B) + ϖ ^ 2 * κ * KT1 / Real.sqrt B := by linarith
      _ = (κ * KT * KE + κ * KT1) * ϖ ^ 2 / Real.sqrt B := by ring
  · refine (hbo _ (ϖ * κ) (by positivity) mα1.aestronglyMeasurable
      (fun z => (pt z).2.2.2.1)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ κ * KT * KE * ϖ := by positivity
    calc ϖ * κ * KT1 ≤ ϖ * κ * KT1 + κ * KT * KE * ϖ := by linarith
      _ = (κ * KT * KE + κ * KT1) * ϖ := by ring
  · refine (hbo _ (ϖ ^ 2 * κ / s) (by positivity) mα2.aestronglyMeasurable
      (fun z => (pt z).2.2.2.2.1)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 ≤ κ * KT * KE * ϖ ^ 2 / s := by positivity
    calc ϖ ^ 2 * κ / s * KT1 ≤ ϖ ^ 2 * κ / s * KT1 + κ * KT * KE * ϖ ^ 2 / s := by linarith
      _ = (κ * KT * KE + κ * KT1) * ϖ ^ 2 / s := by ring
  · refine (hbo _ (ϖ ^ 2 * κ) (by positivity) mα3.aestronglyMeasurable
      (fun z => (pt z).2.2.2.2.2)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 ≤ κ * KT * KE * ϖ ^ 2 := by positivity
    calc ϖ ^ 2 * κ * KT1 ≤ ϖ ^ 2 * κ * KT1 + κ * KT * KE * ϖ ^ 2 := by linarith
      _ = (κ * KT * KE + κ * KT1) * ϖ ^ 2 := by ring

/-! ### Helpers for `lem:app-dyn-raw` (P-E.8.P4) -/

/-- denominators -/
private lemma pe8r_den (x d : ℝ) (hx : 0 ≤ x) : HasDerivAt (fun y : ℝ => 1 + x * y ^ 2) (2 * x * d) d := by
  convert (hasDerivAt_const d 1).add ((hasDerivAt_pow 2 d).const_mul x) using 1 <;> ring

private lemma pe8r_d2 (x d : ℝ) (hx : 0 ≤ x) :
    deriv (deriv (psiX x)) d = 2 * (1 - 3 * x * d ^ 2) / (1 + x * d ^ 2) ^ 3 := by
  have hden : 1 + x * d ^ 2 ≠ 0 := by positivity
  have e : deriv (psiX x) = fun y => 2 * y / (1 + x * y ^ 2) ^ 2 :=
    funext fun y => pe8_psiX_deriv x y hx
  rw [e]
  have hn : HasDerivAt (fun y : ℝ => 2 * y) 2 d := by simpa using (hasDerivAt_id d).const_mul 2
  have hd := (pe8r_den x d hx).pow 2
  have hq := hn.div hd (pow_ne_zero 2 hden)
  refine (show deriv (fun y : ℝ => 2 * y / (1 + x * y ^ 2) ^ 2) d = _ from hq.deriv).trans ?_
  simp only [Pi.pow_apply]
  beta_reduce
  push_cast
  field_simp
  ring

private lemma pe8r_d3 (x d : ℝ) (hx : 0 ≤ x) :
    deriv (deriv (deriv (psiX x))) d = 24 * x * d * (x * d ^ 2 - 1) / (1 + x * d ^ 2) ^ 4 := by
  have hden : 1 + x * d ^ 2 ≠ 0 := by positivity
  have e : deriv (deriv (psiX x)) = fun y => 2 * (1 - 3 * x * y ^ 2) / (1 + x * y ^ 2) ^ 3 :=
    funext fun y => pe8r_d2 x y hx
  rw [e]
  have hn : HasDerivAt (fun y : ℝ => 2 * (1 - 3 * x * y ^ 2)) (2 * (-(3 * x * (2 * d)))) d := by
    have := ((hasDerivAt_pow 2 d).const_mul (3 * x)).const_sub 1 |>.const_mul 2
    simpa using this
  have hd := (pe8r_den x d hx).pow 3
  have hq := hn.div hd (pow_ne_zero 3 hden)
  refine (show deriv (fun y : ℝ => 2 * (1 - 3 * x * y ^ 2) / (1 + x * y ^ 2) ^ 3) d = _ from hq.deriv).trans ?_
  simp only [Pi.pow_apply]
  beta_reduce
  push_cast
  field_simp
  ring

private lemma pe8r_d4 (x d : ℝ) (hx : 0 ≤ x) :
    deriv (deriv (deriv (deriv (psiX x)))) d =
      -(24 * x * (5 * x ^ 2 * d ^ 4 - 10 * x * d ^ 2 + 1)) / (1 + x * d ^ 2) ^ 5 := by
  have hden : 1 + x * d ^ 2 ≠ 0 := by positivity
  have e : deriv (deriv (deriv (psiX x))) = fun y => 24 * x * y * (x * y ^ 2 - 1) / (1 + x * y ^ 2) ^ 4 :=
    funext fun y => pe8r_d3 x y hx
  rw [e]
  have hn : HasDerivAt (fun y : ℝ => 24 * x * y * (x * y ^ 2 - 1))
      (24 * x * (x * d ^ 2 - 1) + 24 * x * d * (x * (2 * d))) d := by
    have h1 : HasDerivAt (fun y : ℝ => 24 * x * y) (24 * x) d := by
      simpa using (hasDerivAt_id d).const_mul (24 * x)
    have h2 : HasDerivAt (fun y : ℝ => x * y ^ 2 - 1) (x * (2 * d)) d := by
      simpa using ((hasDerivAt_pow 2 d).const_mul x).sub_const 1
    exact h1.mul h2
  have hd := (pe8r_den x d hx).pow 4
  have hq := hn.div hd (pow_ne_zero 4 hden)
  refine (show deriv (fun y : ℝ => 24 * x * y * (x * y ^ 2 - 1) / (1 + x * y ^ 2) ^ 4) d = _ from hq.deriv).trans ?_
  simp only [Pi.pow_apply]
  beta_reduce
  push_cast
  field_simp
  ring


private lemma pe8p_B2 (t : ℝ) (ht : 0 ≤ t) : |2 * (1 - 3 * t) / (1 + t) ^ 3| ≤ 2 := by
  have hp : 0 < (1 + t) ^ 3 := by positivity
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp, abs_le]
  constructor <;> nlinarith [mul_nonneg ht ht, pow_nonneg ht 3]

private lemma pe8p_B4 (t : ℝ) (ht : 0 ≤ t) :
    |(5 * t ^ 2 - 10 * t + 1)| ≤ (1 + t) ^ 5 := by
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg ht ht, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5]

private lemma pe8p_B3 (t : ℝ) (ht : 0 ≤ t) : |1 - t| ≤ 1 + t := by
  rw [abs_le]; constructor <;> linarith

private lemma pe8p_s2 (x d : ℝ) (hx : 0 ≤ x) :
    |2 * (1 - 3 * x * d ^ 2) / (1 + x * d ^ 2) ^ 3| ≤ 2 := by
  have h := pe8p_B2 (x * d ^ 2) (by positivity)
  rwa [show 3 * x * d ^ 2 = 3 * (x * d ^ 2) by ring]

private lemma pe8p_s4 (x d : ℝ) (hx : 0 ≤ x) :
    |-(24 * x * (5 * x ^ 2 * d ^ 4 - 10 * x * d ^ 2 + 1)) / (1 + x * d ^ 2) ^ 5| ≤ 24 * x := by
  have ht : 0 ≤ x * d ^ 2 := by positivity
  have h := pe8p_B4 (x * d ^ 2) ht
  have hp : 0 < (1 + x * d ^ 2) ^ 5 := by positivity
  have e : 5 * x ^ 2 * d ^ 4 - 10 * x * d ^ 2 + 1 = 5 * (x * d ^ 2) ^ 2 - 10 * (x * d ^ 2) + 1 := by ring
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 24 * x), e]
  calc 24 * x * |5 * (x * d ^ 2) ^ 2 - 10 * (x * d ^ 2) + 1| ≤ 24 * x * (1 + x * d ^ 2) ^ 5 :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

private lemma pe8p_s3 (x d : ℝ) (hx : 0 ≤ x) :
    |24 * x * d * (x * d ^ 2 - 1) / (1 + x * d ^ 2) ^ 4| ≤ 24 * x * |d| := by
  have ht : 0 ≤ x * d ^ 2 := by positivity
  have h := pe8p_B3 (x * d ^ 2) ht
  have hp : 0 < (1 + x * d ^ 2) ^ 4 := by positivity
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 24 * x),
    abs_sub_comm]
  have h1 : (1 + x * d ^ 2) ^ 4 ≥ (1 + x * d ^ 2) := by
    have : (1:ℝ) ≤ 1 + x * d ^ 2 := by linarith
    calc (1 + x * d ^ 2) = (1 + x * d ^ 2) ^ 1 := by ring
      _ ≤ _ := pow_le_pow_right₀ this (by norm_num)
  calc 24 * x * |d| * |1 - x * d ^ 2| ≤ 24 * x * |d| * (1 + x * d ^ 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ 24 * x * |d| * (1 + x * d ^ 2) ^ 4 := mul_le_mul_of_nonneg_left h1 (by positivity)

private lemma pe8p_s1 (x d : ℝ) (hx : 0 ≤ x) :
    |2 * d / (1 + x * d ^ 2) ^ 2| ≤ 2 * |d| := by
  have hp : 0 < (1 + x * d ^ 2) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have : (1:ℝ) ≤ (1 + x * d ^ 2) ^ 2 := by
    have : (1:ℝ) ≤ 1 + x * d ^ 2 := by nlinarith [mul_nonneg hx (sq_nonneg d)]
    nlinarith
  nlinarith [abs_nonneg d]

/-- x-derivative of `ψ''`. -/
private lemma pe8p_xderiv (x d : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => 2 * (1 - 3 * y * d ^ 2) / (1 + y * d ^ 2) ^ 3)
      (12 * d ^ 2 * (x * d ^ 2 - 1) / (1 + x * d ^ 2) ^ 4) x := by
  have hden : 1 + x * d ^ 2 ≠ 0 := by positivity
  have hd : HasDerivAt (fun y : ℝ => 1 + y * d ^ 2) (d ^ 2) x := by
    simpa using ((hasDerivAt_id x).mul_const (d ^ 2)).const_add 1
  have hn : HasDerivAt (fun y : ℝ => 2 * (1 - 3 * y * d ^ 2)) (2 * (-(3 * d ^ 2))) x := by
    have := (((hasDerivAt_id x).const_mul 3).mul_const (d ^ 2)).const_sub 1 |>.const_mul 2
    simpa using this
  have hq := hn.div (hd.pow 3) (pow_ne_zero 3 hden)
  refine (show HasDerivAt (fun y : ℝ => 2 * (1 - 3 * y * d ^ 2) / (1 + y * d ^ 2) ^ 3) _ x from hq).congr_deriv ?_
  simp only [Pi.pow_apply]
  beta_reduce
  push_cast
  field_simp
  ring

private lemma pe8p_lip (x x' d : ℝ) (hx : 0 ≤ x) (hx' : 0 ≤ x') :
    |2 * (1 - 3 * x * d ^ 2) / (1 + x * d ^ 2) ^ 3 - 2 * (1 - 3 * x' * d ^ 2) / (1 + x' * d ^ 2) ^ 3|
      ≤ 12 * d ^ 2 * |x - x'| := by
  set f : ℝ → ℝ := fun y => 2 * (1 - 3 * y * d ^ 2) / (1 + y * d ^ 2) ^ 3 with hf
  have hder : ∀ y ∈ Set.Ici (0:ℝ), HasDerivAt f (12 * d ^ 2 * (y * d ^ 2 - 1) / (1 + y * d ^ 2) ^ 4) y :=
    fun y hy => pe8p_xderiv y d hy
  have hb : ∀ y ∈ Set.Ici (0:ℝ), ‖deriv f y‖ ≤ 12 * d ^ 2 := by
    intro y hy
    have hy0 : 0 ≤ y := hy
    rw [(hder y hy).deriv, Real.norm_eq_abs]
    have ht : 0 ≤ y * d ^ 2 := by positivity
    have hp : 0 < (1 + y * d ^ 2) ^ 4 := by positivity
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 12 * d ^ 2),
      abs_sub_comm]
    have h := pe8p_B3 (y * d ^ 2) ht
    have h1 : (1 + y * d ^ 2) ^ 4 ≥ (1 + y * d ^ 2) := by
      have : (1:ℝ) ≤ 1 + y * d ^ 2 := by linarith
      calc (1 + y * d ^ 2) = (1 + y * d ^ 2) ^ 1 := by ring
        _ ≤ _ := pow_le_pow_right₀ this (by norm_num)
    calc 12 * d ^ 2 * |1 - y * d ^ 2| ≤ 12 * d ^ 2 * (1 + y * d ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ ≤ 12 * d ^ 2 * (1 + y * d ^ 2) ^ 4 := mul_le_mul_of_nonneg_left h1 (by positivity)
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.Ici (0:ℝ))
    (fun y hy => (hder y hy).differentiableAt) hb (convex_Ici 0) (x := x') (y := x) hx' hx
  simpa [Real.norm_eq_abs, hf, mul_comm] using this


private lemma pe8p_it1 (x : ℝ) (hx : 0 ≤ x) :
    iteratedDeriv 1 (psiX x) = fun d => 2 * d / (1 + x * d ^ 2) ^ 2 := by
  rw [iteratedDeriv_one]; exact funext fun d => pe8_psiX_deriv x d hx

private lemma pe8p_it2 (x : ℝ) (hx : 0 ≤ x) :
    iteratedDeriv 2 (psiX x) = fun d => 2 * (1 - 3 * x * d ^ 2) / (1 + x * d ^ 2) ^ 3 := by
  have : iteratedDeriv 2 (psiX x) = deriv (deriv (psiX x)) := by
    rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_zero]
  rw [this]; exact funext fun d => pe8r_d2 x d hx

private lemma pe8p_it3 (x : ℝ) (hx : 0 ≤ x) :
    iteratedDeriv 3 (psiX x) = fun d => 24 * x * d * (x * d ^ 2 - 1) / (1 + x * d ^ 2) ^ 4 := by
  have : iteratedDeriv 3 (psiX x) = deriv (deriv (deriv (psiX x))) := by
    rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_zero]
  rw [this]; exact funext fun d => pe8r_d3 x d hx

private lemma pe8p_it4 (x : ℝ) (hx : 0 ≤ x) :
    iteratedDeriv 4 (psiX x) = fun d =>
      -(24 * x * (5 * x ^ 2 * d ^ 4 - 10 * x * d ^ 2 + 1)) / (1 + x * d ^ 2) ^ 5 := by
  have : iteratedDeriv 4 (psiX x) = deriv (deriv (deriv (deriv (psiX x)))) := by
    rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ',
      iteratedDeriv_zero]
  rw [this]; exact funext fun d => pe8r_d4 x d hx

private lemma pe8p_cd (x : ℝ) (hx : 0 ≤ x) : ContDiff ℝ 3 (deriv (psiX x)) := by
  have e : deriv (psiX x) = fun d => 2 * d / (1 + x * d ^ 2) ^ 2 :=
    funext fun d => pe8_psiX_deriv x d hx
  rw [e]
  refine ContDiff.div (by fun_prop) (by fun_prop) fun d => ?_
  positivity

private lemma pe8p_poly (x : ℝ) (hx : 0 ≤ x) :
    ∀ j : ℕ, j ≤ 3 → ∃ (K : ℝ) (k : ℕ), ∀ d : ℝ,
      |iteratedDeriv j (deriv (psiX x)) d| ≤ K * (1 + |d| ^ k) := by
  intro j hj
  have e : iteratedDeriv j (deriv (psiX x)) = iteratedDeriv (j + 1) (psiX x) :=
    (iteratedDeriv_succ' (n := j) (f := psiX x)).symm
  rw [e]
  interval_cases j
  · refine ⟨2, 1, fun d => ?_⟩
    rw [show (0 + 1 = 1) from rfl, pe8p_it1 x hx]
    have := pe8p_s1 x d hx
    nlinarith [abs_nonneg d]
  · refine ⟨2, 0, fun d => ?_⟩
    rw [show (1 + 1 = 2) from rfl, pe8p_it2 x hx]
    have := pe8p_s2 x d hx
    simp only [pow_zero]; linarith
  · refine ⟨24 * x, 1, fun d => ?_⟩
    rw [show (2 + 1 = 3) from rfl, pe8p_it3 x hx]
    have := pe8p_s3 x d hx
    nlinarith [abs_nonneg d]
  · refine ⟨24 * x, 0, fun d => ?_⟩
    rw [show (3 + 1 = 4) from rfl, pe8p_it4 x hx]
    have := pe8p_s4 x d hx
    simp only [pow_zero]; nlinarith


/-! ### Gaussian integrability and operator-norm tools -/

private lemma pe8p_sq_coord (k : ℕ) (i : Fin k) :
    Integrable (fun z : Vec k => z i ^ 2) (Muon.Foundations.stdGaussianPi k) := by
  have h := Muon.Foundations.gaussian_integrable_pow 2
  rw [← Muon.Foundations.stdGaussianPi_map_coord k i] at h
  exact (integrable_map_measure (measurable_id.pow_const 2).aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable).1 h

private lemma pe8p_sqfst {m n : ℕ} (i : Fin m) :
    Integrable (fun z : Vec m × Vec n => z.1 i ^ 2) (gaussPair m n) := by
  unfold gaussPair; exact (pe8p_sq_coord m i).comp_fst _

private lemma pe8p_sqsnd {m n : ℕ} (j : Fin n) :
    Integrable (fun z : Vec m × Vec n => z.2 j ^ 2) (gaussPair m n) := by
  unfold gaussPair; exact (pe8p_sq_coord n j).comp_snd _

private lemma pe8p_prodsq {m n : ℕ} (i : Fin m) (j : Fin n) :
    Integrable (fun z : Vec m × Vec n => z.1 i ^ 2 * z.2 j ^ 2) (gaussPair m n) := by
  unfold gaussPair; exact (pe8p_sq_coord m i).mul_prod (pe8p_sq_coord n j)

private lemma pe8p_ww {m n : ℕ} (i j : Fin n) :
    Integrable (fun z : Vec m × Vec n => z.2 i * z.2 j) (gaussPair m n) := by
  have hI : Integrable (fun z : Vec m × Vec n => (z.2 i ^ 2 + z.2 j ^ 2) / 2) (gaussPair m n) :=
    ((pe8p_sqsnd i).add (pe8p_sqsnd j)).div_const 2
  refine hI.mono' (by fun_prop) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [sq_nonneg (z.2 i - z.2 j), sq_nonneg (z.2 i + z.2 j)]

private lemma pe8p_gww {m n : ℕ} (Ah : Mat m n) (g : ℝ → ℝ) (hc : Continuous g) (M : ℝ)
    (hM : ∀ u, |g u| ≤ M) (i j : Fin n) :
    Integrable (fun z : Vec m × Vec n => g (resid Ah z) * (z.2 i * z.2 j)) (gaussPair m n) := by
  refine (pe8p_ww i j).bdd_mul (c := M) (hc.comp (pe8_cont_resid Ah)).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]; exact hM _

private lemma pe8p_int_snd {m n : ℕ} (F : Vec n → ℝ) (hF : Continuous F) :
    ∫ x, F x.2 ∂(gaussPair m n) = ∫ w, F w ∂(Muon.Foundations.stdGaussianPi n) := by
  have hmap : (gaussPair m n).map Prod.snd = Muon.Foundations.stdGaussianPi n := by
    unfold gaussPair
    rw [Measure.map_snd_prod]; simp
  conv_rhs => rw [← hmap]
  rw [integral_map measurable_snd.aemeasurable hF.aestronglyMeasurable]

private lemma pe8p_ww_int {m n : ℕ} (i j : Fin n) :
    ∫ z, z.2 i * z.2 j ∂(gaussPair m n) = if i = j then 1 else 0 := by
  rw [pe8p_int_snd (m := m) (fun w : Vec n => w i * w j) (by fun_prop)]
  have := Muon.Foundations.gaussian_weighted_linear_moment n (Pi.single i 1) j
  simp only [single_dotProduct, one_mul] at this
  rw [this]
  simp [Pi.single_apply, eq_comm]

private lemma pe8p_lin_sq {m n : ℕ} (v : Vec n) :
    Integrable (fun z : Vec m × Vec n => (∑ i, v i * z.2 i) ^ 2) (gaussPair m n) ∧
    ∫ z, (∑ i, v i * z.2 i) ^ 2 ∂(gaussPair m n) = ∑ i, v i ^ 2 := by
  have e : ∀ z : Vec m × Vec n, (∑ i, v i * z.2 i) ^ 2 = ∑ i, ∑ j, v i * v j * (z.2 i * z.2 j) := by
    intro z
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (pe8p_ww i j).const_mul _, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (pe8p_ww i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (pe8p_ww i j).const_mul _]
  simp only [integral_const_mul, pe8p_ww_int]
  simp [sq]

private lemma pe8p_opSq {a b : ℕ} (U : Mat a b) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ x : Fin b → ℝ, ∑ k, (U *ᵥ x) k ^ 2 ≤ M ^ 2 * ∑ i, x i ^ 2) : opNorm U ≤ M := by
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

private lemma pe8p_opNorm_wmean {m n : ℕ} (Ah : Mat m n) (g : ℝ → ℝ) (hc : Continuous g) (M : ℝ)
    (hM : ∀ u : ℝ, |g u| ≤ M) :
    opNorm (Muon.mean (gaussPair m n)
      (fun x => g (resid Ah x) • outer x.2 x.2)) ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine pe8p_opSq _ M hM0 fun v => ?_
  set X := Muon.mean (gaussPair m n) (fun x => g (resid Ah x) • outer x.2 x.2) with hX
  have hXe : ∀ j i, X j i = ∫ x, g (resid Ah x) * (x.2 j * x.2 i) ∂(gaussPair m n) := by
    intro j i
    simp [hX, Muon.mean, Matrix.vecMulVec_apply]
  set u : Vec n := X *ᵥ v with hu
  set a : Vec m × Vec n → ℝ := fun x => ∑ k, u k * x.2 k with ha
  set b : Vec m × Vec n → ℝ := fun x => ∑ i, v i * x.2 i with hb
  have e : ∀ x : Vec m × Vec n, g (resid Ah x) * (a x * b x) =
      ∑ k, ∑ i, u k * v i * (g (resid Ah x) * (x.2 k * x.2 i)) := by
    intro x
    simp only [ha, hb]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hgi := pe8p_gww Ah g hc M hM
  have hS : ∑ k, u k ^ 2 = ∫ x, g (resid Ah x) * (a x * b x) ∂(gaussPair m n) := by
    simp_rw [e]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ =>
      (hgi k i).const_mul _]
    have : ∀ k, ∫ x, ∑ i, u k * v i * (g (resid Ah x) * (x.2 k * x.2 i)) ∂(gaussPair m n) =
        u k * ∑ i, X k i * v i := by
      intro k
      rw [integral_finsetSum _ fun i _ => (hgi k i).const_mul _, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, hXe]; ring
    simp_rw [this]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hu, Matrix.mulVec, dotProduct, sq]
  obtain ⟨ia, ha2⟩ := pe8p_lin_sq (m := m) u
  obtain ⟨ib, hb2⟩ := pe8p_lin_sq (m := m) v
  have ig : Integrable (fun x : Vec m × Vec n => g (resid Ah x) * (a x * b x)) (gaussPair m n) := by
    simp_rw [e]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ =>
      (hgi k i).const_mul _
  have hmono : ∫ x, g (resid Ah x) * (a x * b x) ∂(gaussPair m n) ≤
      ∫ x, ((a x) ^ 2 + M ^ 2 * (b x) ^ 2) / 2 ∂(gaussPair m n) := by
    refine integral_mono ig ((ia.add (ib.const_mul _)).div_const 2) fun x => ?_
    have h1 : |g (resid Ah x) * (a x * b x)| ≤ M * (|a x| * |b x|) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (hM _) le_rfl (by positivity) hM0
    have h2 : g (resid Ah x) * (a x * b x) ≤ M * (|a x| * |b x|) := (le_abs_self _).trans h1
    nlinarith [sq_nonneg (|a x| - M * |b x|), sq_abs (a x), sq_abs (b x)]
  have hrhs : ∫ x, ((a x) ^ 2 + M ^ 2 * (b x) ^ 2) / 2 ∂(gaussPair m n) =
      (∑ k, u k ^ 2 + M ^ 2 * ∑ i, v i ^ 2) / 2 := by
    rw [integral_div, integral_add ia (ib.const_mul _), integral_const_mul, ha2, hb2]
  rw [hS] at *
  linarith


/-! ### Assembly helpers -/

private lemma pe8p_cont2 (x : ℝ) (hx : 0 ≤ x) : Continuous (iteratedDeriv 2 (psiX x)) := by
  rw [pe8p_it2 x hx]
  exact Continuous.div (by fun_prop) (by fun_prop) (fun d => by positivity)

private lemma pe8p_cont4 (x : ℝ) (hx : 0 ≤ x) : Continuous (iteratedDeriv 4 (psiX x)) := by
  rw [pe8p_it4 x hx]
  exact Continuous.div (by fun_prop) (by fun_prop) (fun d => by positivity)

private lemma pe8p_bnd2 (x : ℝ) (hx : 0 ≤ x) (u : ℝ) : |iteratedDeriv 2 (psiX x) u| ≤ 2 := by
  rw [pe8p_it2 x hx]; exact pe8p_s2 x u hx

private lemma pe8p_bnd4 (x : ℝ) (hx : 0 ≤ x) (u : ℝ) : |iteratedDeriv 4 (psiX x) u| ≤ 24 * x := by
  rw [pe8p_it4 x hx]; exact pe8p_s4 x u hx

private lemma pe8p_sqint {m n : ℕ} (Ah : Mat m n) (hA : fro Ah = 1) :
    Integrable (fun z : Vec m × Vec n => resid Ah z ^ 2) (gaussPair m n) :=
  Integrable.of_integral_ne_zero (by rw [(lem_app_setup_residual_i Ah hA).2.1]; norm_num)

private lemma pe8p_entry_int {m n : ℕ} (Ah : Mat m n) (hA : fro Ah = 1) (x : ℝ) (hx : 0 ≤ x)
    (i : Fin m) (j : Fin n) :
    Integrable (fun z : Vec m × Vec n => deriv (psiX x) (resid Ah z) * (z.1 i * z.2 j))
      (gaussPair m n) := by
  have hI : Integrable (fun z : Vec m × Vec n => resid Ah z ^ 2 + z.1 i ^ 2 * z.2 j ^ 2)
      (gaussPair m n) := (pe8p_sqint Ah hA).add (pe8p_prodsq i j)
  refine hI.mono' ((pe8_cont_deriv Ah x hx).2.mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul, pe8_psiX_deriv x _ hx]
  have h1 := pe8p_s1 x (resid Ah z) hx
  have h2 : |z.1 i * z.2 j| ^ 2 = z.1 i ^ 2 * z.2 j ^ 2 := by rw [sq_abs]; ring
  have h3 := abs_nonneg (z.1 i * z.2 j)
  nlinarith [sq_nonneg (|resid Ah z| - |z.1 i * z.2 j|), sq_abs (resid Ah z),
    mul_le_mul_of_nonneg_right h1 h3]

private lemma pe8p_frobIP_eq {m n : ℕ} (X Y : Mat m n) :
    frobIP X Y = ∑ i, ∑ j, X i j * Y i j := by
  unfold frobIP
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]

private lemma pe8p_frobIP_comm {m n : ℕ} (X Y : Mat m n) : frobIP X Y = frobIP Y X := by
  rw [pe8p_frobIP_eq, pe8p_frobIP_eq]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

private lemma pe8p_frobIP_lin {m n : ℕ} (c : ℝ) (X Y Z : Mat m n) :
    frobIP X (c • Y + Z) = c * frobIP X Y + frobIP X Z := by
  unfold frobIP
  simp [Matrix.transpose_add, Matrix.transpose_smul, Matrix.mul_add, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_smul]

private lemma pe8p_nuc_gram {m n : ℕ} (Ah : Mat m n) (hA : fro Ah = 1) : nuc (Ahᵀ * Ah) = 1 := by
  have hS0 : 0 ≤ Ahᵀ * Ah := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa using Matrix.posSemidef_conjTranspose_mul_self Ah
  have hsym : (Ahᵀ * Ah)ᵀ = Ahᵀ * Ah := by simp [Matrix.transpose_mul]
  rw [nuc_eq_trace_cfc_sqrt, hsym, CFC.sqrt_mul_self _ hS0]
  have h1 : ∑ i, ∑ j, ‖Ah i j‖ ^ 2 = 1 := by
    have h := hA
    unfold fro at h
    have h0 : 0 ≤ ∑ i, ∑ j, ‖Ah i j‖ ^ 2 := by positivity
    have := Real.sqrt_eq_one.1 h
    exact this
  rw [← h1, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `lem:app-dyn-raw`, snapshot `cr-2026-10-23`. Statement verbatim from `section.tex` (ll. 1202–1210):
```latex
\begin{lemma}[Gaussian response of the derivative functional]\label{lem:app-dyn-raw}
Let $\norm{\widehat A}_\F=1$, $\delta=\norm{\widehat A}$, and let $E$ be deterministic
with $C_E=\Sigmaout^{1/2}E\Sigmain^{1/2}$ and $e=z^\T C_Ew$. For $x,x'\ge0$,
$\abs{b(x)}\le2$, $\abs{b(x)-b(x')}\le12\abs{x-x'}$ and $\norm{N_x}\le24x$, and
\begin{equation}\label{eqn:app-dyn-raw}
\EE\big[e\,\psi_x'(d)\big]=\langle\widehat A,C_E\rangle\,b(x)+\big\langle C_E,\widehat AN_x\widehat A^\T\widehat A\big\rangle,\qquad
\big|\big\langle C_E,\widehat AN_x\widehat A^\T\widehat A\big\rangle\big|\le24x\,\norm{C_E}\,\delta .
\end{equation}
\end{lemma}
```
-/
theorem lem_app_dyn_raw {m n : ℕ} (Ah : Mat m n) (hA : fro Ah = 1) :
    (∀ x : ℝ, 0 ≤ x →
      Integrable (fun z : Vec m × Vec n => iteratedDeriv 2 (psiX x) (resid Ah z))
        (gaussPair m n) ∧
      ∀ i j, Integrable (fun z : Vec m × Vec n =>
        iteratedDeriv 4 (psiX x) (resid Ah z) * outer z.2 z.2 i j) (gaussPair m n)) ∧
    (∀ x : ℝ, 0 ≤ x → |bFun Ah x| ≤ 2) ∧
    (∀ x x' : ℝ, 0 ≤ x → 0 ≤ x' → |bFun Ah x - bFun Ah x'| ≤ 12 * |x - x'|) ∧
    (∀ x : ℝ, 0 ≤ x → opNorm (NFun Ah x) ≤ 24 * x) ∧
    (∀ (CE : Mat m n) (x : ℝ), 0 ≤ x →
      Integrable (fun z : Vec m × Vec n => resid CE z * deriv (psiX x) (resid Ah z))
        (gaussPair m n) ∧
      ∫ z, resid CE z * deriv (psiX x) (resid Ah z) ∂(gaussPair m n)
        = frobIP Ah CE * bFun Ah x + frobIP CE (Ah * NFun Ah x * Ahᵀ * Ah) ∧
      |frobIP CE (Ah * NFun Ah x * Ahᵀ * Ah)| ≤ 24 * x * opNorm CE * opNorm Ah) := by
  have hint2 : ∀ x : ℝ, 0 ≤ x →
      Integrable (fun z : Vec m × Vec n => iteratedDeriv 2 (psiX x) (resid Ah z)) (gaussPair m n) := by
    intro x hx
    refine Integrable.of_bound ((pe8p_cont2 x hx).comp (pe8_cont_resid Ah)).aestronglyMeasurable 2
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]; exact pe8p_bnd2 x hx _
  have hNop : ∀ x : ℝ, 0 ≤ x → opNorm (NFun Ah x) ≤ 24 * x := fun x hx =>
    pe8p_opNorm_wmean Ah _ (pe8p_cont4 x hx) (24 * x) (pe8p_bnd4 x hx)
  refine ⟨fun x hx => ⟨hint2 x hx, fun i j => ?_⟩, fun x hx => ?_, fun x x' hx hx' => ?_, hNop, ?_⟩
  · exact pe8p_gww Ah _ (pe8p_cont4 x hx) (24 * x) (pe8p_bnd4 x hx) i j
  · have := norm_integral_le_of_norm_le_const (μ := gaussPair m n) (C := 2)
      (f := fun z : Vec m × Vec n => iteratedDeriv 2 (psiX x) (resid Ah z))
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact pe8p_bnd2 x hx _)
    simpa [bFun] using this
  · have hsub : bFun Ah x - bFun Ah x' = ∫ z, (iteratedDeriv 2 (psiX x) (resid Ah z) -
        iteratedDeriv 2 (psiX x') (resid Ah z)) ∂(gaussPair m n) := by
      unfold bFun; rw [integral_sub (hint2 x hx) (hint2 x' hx')]
    have hI : Integrable (fun z : Vec m × Vec n => 12 * |x - x'| * resid Ah z ^ 2) (gaussPair m n) :=
      (pe8p_sqint Ah hA).const_mul _
    have := norm_integral_le_of_norm_le (μ := gaussPair m n)
      (f := fun z : Vec m × Vec n => iteratedDeriv 2 (psiX x) (resid Ah z) -
        iteratedDeriv 2 (psiX x') (resid Ah z)) hI
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, pe8p_it2 x hx, pe8p_it2 x' hx']
        have := pe8p_lip x x' (resid Ah z) hx hx'
        simp only at this ⊢
        linarith)
    rw [hsub, ← Real.norm_eq_abs]
    refine this.trans (le_of_eq ?_)
    rw [integral_const_mul, (lem_app_setup_residual_i Ah hA).2.1]; ring
  · intro CE x hx
    have hent := pe8p_entry_int Ah hA x hx
    have epw : ∀ z : Vec m × Vec n, resid CE z * deriv (psiX x) (resid Ah z) =
        ∑ i, ∑ j, CE i j * (deriv (psiX x) (resid Ah z) * (z.1 i * z.2 j)) := by
      intro z
      unfold resid
      simp only [dotProduct, Matrix.mulVec, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hintA : Integrable (fun z : Vec m × Vec n => resid CE z * deriv (psiX x) (resid Ah z))
        (gaussPair m n) := by
      simp_rw [epw]
      exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (hent i j).const_mul _
    have hstein := lem_app_de_stein_i Ah (deriv (psiX x)) (pe8p_cd x hx) (pe8p_poly x hx)
    have e2 : deriv (deriv (psiX x)) = iteratedDeriv 2 (psiX x) := by
      rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_zero]
    have e4 : iteratedDeriv 3 (deriv (psiX x)) = iteratedDeriv 4 (psiX x) :=
      (iteratedDeriv_succ' (n := 3) (f := psiX x)).symm
    rw [e2, e4] at hstein
    have hst : Muon.mean (gaussPair m n)
        (fun z => deriv (psiX x) (resid Ah z) • outer z.1 z.2) =
        bFun Ah x • Ah + Ah * NFun Ah x * Ahᵀ * Ah := hstein
    have hint_eq : ∫ z, resid CE z * deriv (psiX x) (resid Ah z) ∂(gaussPair m n) =
        frobIP CE (Muon.mean (gaussPair m n)
          (fun z => deriv (psiX x) (resid Ah z) • outer z.1 z.2)) := by
      rw [pe8p_frobIP_eq]
      simp_rw [epw]
      have hI1 : ∀ i ∈ (Finset.univ : Finset (Fin m)), Integrable
          (fun z : Vec m × Vec n => ∑ j, CE i j * (deriv (psiX x) (resid Ah z) * (z.1 i * z.2 j)))
          (gaussPair m n) := fun i _ => integrable_finsetSum _ fun j _ => (hent i j).const_mul _
      rw [integral_finsetSum _ hI1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => (hent i j).const_mul _]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
      simp [Muon.mean, Matrix.vecMulVec_apply]
    refine ⟨hintA, ?_, ?_⟩
    · rw [hint_eq, hst, pe8p_frobIP_lin, pe8p_frobIP_comm CE Ah]
      ring
    · set R := Ah * NFun Ah x * Ahᵀ * Ah with hR
      have h1 := trace_mul_le_opNorm_mul_nuc CE Rᵀ
      rw [nuc_transpose] at h1
      have hR2 : R = (Ah * NFun Ah x) * (Ahᵀ * Ah) := by simp [hR, Matrix.mul_assoc]
      have h2 : nuc R ≤ opNorm (Ah * NFun Ah x) * nuc (Ahᵀ * Ah) := by
        rw [hR2]; exact nuc_mul_le_left _ _
      rw [pe8p_nuc_gram Ah hA, mul_one] at h2
      have h3 := pe8_opNorm_mul_le Ah (NFun Ah x)
      have h4 := hNop x hx
      have hc := pe8_opNorm_nonneg CE
      have ha := pe8_opNorm_nonneg Ah
      have hN0 := pe8_opNorm_nonneg (NFun Ah x)
      have : frobIP CE R = (CE * Rᵀ).trace := rfl
      rw [this]
      calc |(CE * Rᵀ).trace| ≤ opNorm CE * nuc R := h1
        _ ≤ opNorm CE * (opNorm Ah * (24 * x)) := by
            refine mul_le_mul_of_nonneg_left (h2.trans (h3.trans ?_)) hc
            exact mul_le_mul_of_nonneg_left h4 ha
        _ = 24 * x * opNorm CE * opNorm Ah := by ring

private lemma pe8q_Ahat_fro {m n : ℕ} (Cv : Covariances m n) (D : Mat m n)
    (hD : 0 < riskSigma Cv D) : fro (Ahat Cv D) = 1 := by
  have hsq : ∀ (c : ℝ) (K : Mat m n), fro (c • K) ^ 2 = c ^ 2 * fro K ^ 2 := by
    intro c K
    have hf : ∀ L : Mat m n, fro L ^ 2 = ∑ i, ∑ j, L i j ^ 2 := by
      intro L
      unfold fro
      rw [Real.sq_sqrt (by positivity)]
      simp only [Real.norm_eq_abs, sq_abs]
    simp only [hf, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  have hr := eqn_app_setup_whitened_risk Cv D
  have hs : fro (Ahat Cv D) ^ 2 = 1 := by
    rw [Ahat, hsq, inv_pow, Real.sq_sqrt (by linarith)]
    rw [show fro (Arot Cv D) ^ 2 = 2 * riskSigma Cv D by linarith,
      inv_mul_cancel₀ (by linarith)]
  have hn : 0 ≤ fro (Ahat Cv D) := Real.sqrt_nonneg _
  nlinarith

private lemma pe8q_emaW_mem_Icc (p : DynParams) (k : ℕ) : emaW p.β k ∈ Icc (0 : ℝ) 1 := by
  constructor
  · unfold emaW
    exact mul_nonneg (by linarith [p.hβ.2]) (pow_nonneg p.hβ.1 k)
  · unfold emaW
    have hb1 : p.β ≤ 1 := p.hβ.2.le
    have hp : p.β ^ k ≤ 1 := pow_le_one₀ p.hβ.1 hb1
    have hnb : 0 ≤ 1 - p.β := by linarith
    calc
      (1 - p.β) * p.β ^ k ≤ (1 - p.β) * 1 :=
        mul_le_mul_of_nonneg_left hp hnb
      _ ≤ 1 := by linarith [p.hβ.1]

private lemma pe8q_outer_samp {m n B : ℕ} (Cv : Covariances m n) (hB : 0 < B)
    (z : Vec m × Vec n) :
    outer (sampU Cv B z) (sampV Cv B z) =
      (B : ℝ)⁻¹ • outer (phys Cv z).1 (phys Cv z).2 := by
  have hBr : (0 : ℝ) ≤ B := by positivity
  have hsqrt : Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) = B :=
    Real.mul_self_sqrt hBr
  have hinv : (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ = (B : ℝ)⁻¹ := by
    rw [← mul_inv, hsqrt]
  ext i k
  simp only [sampU, sampV, phys, outer, Matrix.vecMulVec_apply, Pi.smul_apply,
    Matrix.smul_apply, smul_eq_mul]
  calc
    _ = ((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹) *
        ((rOut Cv *ᵥ z.1) i * (rIn Cv *ᵥ z.2) k) := by ring
    _ = _ := by rw [hinv]

private lemma pe8q_batchGrad_eq {m n B : ℕ} (Cv : Covariances m n) (hB : 0 < B)
    (E : Mat m n) (z : Fin B → Vec m × Vec n) :
    batchGrad E (fun a => phys Cv (z a)) =
      ∑ a, resid (Arot Cv E) (z a) • outer (sampU Cv B (z a)) (sampV Cv B (z a)) := by
  change Muon.Setup.grad E (fun a => phys Cv (z a)) = _
  rw [eqn_app_setup_whitened_grad, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pe8q_outer_samp Cv hB, smul_smul, smul_smul]
  have hout : rOut Cv * outer (z a).1 (z a).2 * rIn Cv =
      outer (phys Cv (z a)).1 (phys Cv (z a)).2 := by
    unfold phys outer rOut rIn
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    change Matrix.vecMulVec (CFC.sqrt Cv.Sout *ᵥ (z a).1)
      ((z a).2 ᵥ* CFC.sqrt Cv.Sin) =
        Matrix.vecMulVec (CFC.sqrt Cv.Sout *ᵥ (z a).1) (CFC.sqrt Cv.Sin *ᵥ (z a).2)
    rw [← Matrix.mulVec_transpose, pe8_sqrt_symm]
  rw [hout]
  unfold resid
  congr 1
  ring

private lemma pe8q_dirX_eq_dXExpr {m n B : ℕ} (N : Mat m n) (ϖ s : ℝ)
    (u : Fin B → Vec m) (v : Fin B → Vec n) (d e : Fin B → ℝ)
    (hs : 0 < s) (hϖ : ϖ ∈ Icc (0 : ℝ) 1) :
    dirX N (ϖ • ∑ a, e a • outer (u a) (v a)) s = dXExpr N ϖ s d e u v := by
  let Np : Mat m n := N - ϖ • ∑ a, d a • outer (u a) (v a)
  have hN : N = Np + ϖ • ∑ a, d a • outer (u a) (v a) := by
    simp only [Np, sub_add_cancel]
  have hd := lem_app_dyn_derivative_ii Np N ϖ s u v d e hs hϖ hN
  ext i k
  unfold dirX
  change deriv (fun t : ℝ =>
      Xs (N + t • (ϖ • ∑ a, e a • outer (u a) (v a))) s i k) 0 = _
  have hfun : (fun t : ℝ =>
      Xs (N + t • (ϖ • ∑ a, e a • outer (u a) (v a))) s i k) =
      fun t : ℝ => Xs (N + (t * ϖ) • ∑ a, e a • outer (u a) (v a)) s i k := by
    funext t
    rw [smul_smul]
  rw [hfun]
  exact (hd i k).deriv

private lemma pe8q_sampleMinor_eq_remainder {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (p : DynParams) (Cv : Covariances m n)
    (cs : ChainSamples P m n B) (t j r : ℕ) (D : Mat m n) (a : Fin B) (ω : Ω) :
    sampleMinor (stationaryN p Cv cs t D r ω) (emaW p.β (r - j))
      (fun b => resid (Ahat Cv D) (cs.act ((t : ℤ) + j + 1) b ω))
      (fun b => sampU Cv B (cs.act ((t : ℤ) + j + 1) b ω))
      (fun b => sampV Cv B (cs.act ((t : ℤ) + j + 1) b ω)) a =
        sampleRemainder p Cv cs t j r D a ω := by
  rfl

private lemma pe8q_stationaryN_aestronglyMeasurable {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (p : DynParams) (Cv : Covariances m n) (cs : ChainSamples P m n B)
    (t : ℕ) (D : Mat m n) (hD : 0 < riskSigma Cv D)
    (hsize : Muon.Volatility.SizeFin Cv B p.γstar p.CSig) (r : ℕ) :
    AEStronglyMeasurable (stationaryN p Cv cs t D r) P := by
  have hsum := (lem_app_dyn_chains_iii p Cv cs t D 0 hD hsize).1
  have hinit : AEStronglyMeasurable (chainInit p.β Cv D (cs.aux (t : ℤ))) P := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N ω => ∑ q ∈ Finset.range N,
        emaW p.β q • batchGrad D (physBatch Cv (cs.aux (t : ℤ) q) ω)) (fun N => ?_) ?_
    · refine (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun q _ => ?_).aestronglyMeasurable
      have hc : Continuous (fun z : Fin B → Vec m × Vec n =>
          batchGrad D (fun a => phys Cv (z a))) := by
        unfold batchGrad Muon.Setup.grad resid phys outer
        fun_prop
      change StronglyMeasurable (emaW p.β q •
        ((fun z : Fin B → Vec m × Vec n => batchGrad D (fun a => phys Cv (z a))) ∘
          fun ω a => cs.aux (t : ℤ) q a ω))
      exact (hc.measurable.comp (Measurable.of_eval fun a =>
        cs.meas_aux (t : ℤ) q a)).stronglyMeasurable.const_smul (emaW p.β q)
    · filter_upwards [hsum] with ω hω
      exact hω.hasSum.tendsto_sum_nat
  change AEStronglyMeasurable
    (fun ω => (def_app_dyn_chains p Cv cs t D 0 ω).stat (r + 1)) P
  induction r + 1 with
  | zero => exact hinit
  | succ k ih =>
      simp only [def_app_dyn_chains, emaChain]
      have hc : Continuous (fun z : Fin B → Vec m × Vec n =>
          batchGrad D (fun a => phys Cv (z a))) := by
        unfold batchGrad Muon.Setup.grad resid phys outer
        fun_prop
      refine (ih.const_smul p.β).add ?_
      change AEStronglyMeasurable ((1 - p.β) •
        ((fun z : Fin B → Vec m × Vec n => batchGrad D (fun a => phys Cv (z a))) ∘
          fun ω a => cs.act ((t : ℤ) + k + 1) a ω)) P
      exact (hc.measurable.comp (Measurable.of_eval fun a =>
        cs.meas_act ((t : ℤ) + k + 1) a)).stronglyMeasurable.aestronglyMeasurable.const_smul
          (1 - p.β)

private lemma pe8q_freeze_bound {Ω α β : Type*} (G : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    [MeasurableSpace α] [MeasurableSpace β] (hG : G ≤ mΩ)
    {X : Ω → α} {Y : Ω → β} (hX : Measurable[G] X) (hY : Measurable Y)
    (hind : Indep G (MeasurableSpace.comap Y inferInstance) P)
    {f : α → β → ℝ} (hf : Measurable (Function.uncurry f)) (hf0 : ∀ x y, 0 ≤ f x y)
    {g : α → ℝ} (hgint : Integrable (fun ω => g (X ω)) P)
    (hfx : ∀ x, Integrable (f x) (P.map Y))
    (hbound : ∀ x, ∫ y, f x y ∂(P.map Y) ≤ g x) :
    Integrable (fun ω => f (X ω) (Y ω)) P := by
  have hXm : Measurable X := hX.mono hG le_rfl
  have hindf : IndepFun X Y P := by
    refine indep_of_indep_of_le_left hind ?_
    exact hX.comap_le
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hY.aemeasurable).1 hindf
  have hpair : Measurable (fun ω => (X ω, Y ω)) := hXm.prodMk hY
  show Integrable ((Function.uncurry f) ∘ (fun ω => (X ω, Y ω))) P
  rw [← integrable_map_measure hf.aestronglyMeasurable hpair.aemeasurable, hmap]
  rw [integrable_prod_iff hf.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall hfx, ?_⟩
  have hm : Measurable (fun x => ∫ y, ‖Function.uncurry f (x, y)‖ ∂(P.map Y)) :=
    (hf.norm.stronglyMeasurable.integral_prod_right' (ν := P.map Y)).measurable
  refine (integrable_map_measure hm.aestronglyMeasurable hXm.aemeasurable).2 ?_
  refine hgint.mono' (hm.comp hXm).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have heq : ∫ y, |Function.uncurry f (X ω, y)| ∂(P.map Y) =
      ∫ y, f (X ω) y ∂(P.map Y) := integral_congr_ae
        (Filter.Eventually.of_forall fun y => by
          simp [Function.uncurry, abs_of_nonneg (hf0 _ y)])
  simp only [Function.comp, Real.norm_eq_abs]
  rw [heq, abs_of_nonneg (integral_nonneg fun y => hf0 _ y)]
  exact hbound _

private lemma pe8q_gaussian_mixed_moment (γ CS : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {m n B : ℕ} (Cv : Covariances m n) (Ah Ae : Mat m n),
      fro Ah = 1 → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      opNorm Cv.Sout ≤ CS → opNorm Cv.Sin ≤ CS →
      let H := fun z : Vec m × Vec n =>
        ((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ 8 *
          (|resid Ae z| * (1 + momN Cv B z))
      Integrable H (gaussPair m n) ∧ ∫ z, H z ∂(gaussPair m n) ≤ K * fro Ae := by
  obtain ⟨K8, hK8, hb8⟩ := pe8_t_moment 8 2 (by norm_num) (by norm_num) γ CS
  obtain ⟨K1, hK1, hb1⟩ := pe8_t_moment 1 2 (by norm_num) (by norm_num) γ CS
  refine ⟨K8 * K1, mul_nonneg hK8 hK1, ?_⟩
  intro m n B Cv Ah Ae hAh hm hn hCo hCi
  dsimp only
  let T : Vec m × Vec n → ℝ := fun z =>
    ((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ 8
  have hTm : AEStronglyMeasurable T (gaussPair m n) := by
    have hd := pe8_cont_resid Ah
    have hN := pe8_cont_momN Cv B
    exact (by unfold T; fun_prop : Continuous T).aestronglyMeasurable
  by_cases hAe : Ae = 0
  · subst Ae
    simp [resid, T, fro]
  · have hfpos : 0 < fro Ae := by
      unfold fro
      apply Real.sqrt_pos.2
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hAe
      obtain ⟨j, hij⟩ := Function.ne_iff.mp hi
      refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => by positivity)
        ⟨i, Finset.mem_univ i, ?_⟩
      refine Finset.sum_pos' (fun j _ => by positivity) ⟨j, Finset.mem_univ j, ?_⟩
      positivity
    let Aen : Mat m n := (fro Ae)⁻¹ • Ae
    have hAen : fro Aen = 1 := by
      change fro ((fro Ae)⁻¹ • Ae) = 1
      rw [pe8_fro_smul, abs_of_pos (inv_pos.mpr hfpos), inv_mul_cancel₀ hfpos.ne']
    let U : Vec m × Vec n → ℝ := fun z =>
      |resid Aen z| * (1 + momN Cv B z)
    let U1 : Vec m × Vec n → ℝ := fun z =>
      ((1 + |resid Aen z|) * (1 + momN Cv B z)) ^ 1
    have hUm : AEStronglyMeasurable U (gaussPair m n) := by
      have hd := pe8_cont_resid Aen
      have hN := pe8_cont_momN Cv B
      exact (by unfold U; fun_prop : Continuous U).aestronglyMeasurable
    have hU1m : AEStronglyMeasurable U1 (gaussPair m n) := by
      have hd := pe8_cont_resid Aen
      have hN := pe8_cont_momN Cv B
      exact (by unfold U1; fun_prop : Continuous U1).aestronglyMeasurable
    have hUle : eLpNorm U 2 (gaussPair m n) ≤ eLpNorm U1 2 (gaussPair m n) := by
      apply eLpNorm_mono_real hUm
      intro z
      have hN : 0 ≤ momN Cv B z := by unfold momN; positivity
      have hU0 : 0 ≤ U z := by unfold U; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hU0]
      unfold U U1
      simp only [pow_one]
      gcongr
      exact le_add_of_nonneg_left (by positivity)
    have hprod := pe8_holder T U hTm hUm 1 le_rfl
    have hLp : eLpNorm (fun z => T z * U z) 1 (gaussPair m n) ≤
        ENNReal.ofReal (K8 * K1) := by
      calc
        _ ≤ eLpNorm T 2 (gaussPair m n) * eLpNorm U 2 (gaussPair m n) := by
          simpa using hprod
        _ ≤ ENNReal.ofReal K8 * ENNReal.ofReal K1 := by
          gcongr
          · exact hb8 Cv Ah hAh hm hn hCo hCi
          · exact hUle.trans (by simpa [U1] using hb1 Cv Aen hAen hm hn hCo hCi)
        _ = ENNReal.ofReal (K8 * K1) := (ENNReal.ofReal_mul hK8).symm
    have hprodmem : MemLp (fun z => T z * U z) 1 (gaussPair m n) :=
      hLp.trans_lt ENNReal.ofReal_lt_top
    have hprodint : Integrable (fun z => T z * U z) (gaussPair m n) :=
      memLp_one_iff_integrable.mp hprodmem
    have hintle : ∫ z, T z * U z ∂(gaussPair m n) ≤ K8 * K1 := by
      have he := hprodmem.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
      have hTU : ∀ z, 0 ≤ T z * U z := by
        intro z
        unfold T U momN
        positivity
      simp only [ENNReal.toReal_one, inv_one, Real.rpow_one, Real.norm_eq_abs] at he
      have he' : eLpNorm (fun z => T z * U z) 1 (gaussPair m n) =
          ENNReal.ofReal (∫ z, T z * U z ∂(gaussPair m n)) := by
        rw [he]
        congr 2
        funext z
        exact abs_of_nonneg (hTU z)
      rw [he', ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK8 hK1)] at hLp
      exact hLp
    have hres : ∀ z, resid Ae z = fro Ae * resid Aen z := by
      intro z
      unfold Aen resid
      simp only [Matrix.smul_mulVec, dotProduct_smul]
      simp [smul_eq_mul, hfpos.ne']
    have hfun : (fun z : Vec m × Vec n =>
        ((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ 8 *
          (|resid Ae z| * (1 + momN Cv B z))) =
        fun z => fro Ae * (T z * U z) := by
      funext z
      rw [hres, abs_mul, abs_of_pos hfpos]
      change T z * (fro Ae * |resid Aen z| * (1 + momN Cv B z)) =
        fro Ae * (T z * U z)
      unfold U
      ring
    rw [hfun]
    refine ⟨hprodint.const_mul _, ?_⟩
    rw [integral_const_mul]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hintle hfpos.le

/-! ### Helpers for `prop:app-dyn-reduction` (P-E.8.P6) -/

private lemma pe8m_op_transpose_copy {m n : ℕ} (A : Mat m n) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
    rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.l2_opNorm_conjTranspose]

private lemma pe8m_frobIP_le_copy {m n : ℕ} (A D : Mat m n) :
    |frobIP A D| ≤ fro A * fro D := by
  have htr : frobIP A D = ∑ x : Fin m × Fin n, A x.1 x.2 * D x.1 x.2 := by
    simp [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [htr]
  calc
    |∑ x : Fin m × Fin n, A x.1 x.2 * D x.1 x.2| ≤
        ∑ x : Fin m × Fin n, |A x.1 x.2| * |D x.1 x.2| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun x : Fin m × Fin n => A x.1 x.2 * D x.1 x.2) Finset.univ
    _ ≤ _ := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m × Fin n))
        (fun x => |A x.1 x.2|) (fun x => |D x.1 x.2|)
      simpa [fro, Fintype.sum_prod_type, Real.norm_eq_abs] using h

private lemma pe8m_fro_le_sqrt_cols_op_copy {m n : ℕ} (A : Mat m n) :
    fro A ≤ Real.sqrt n * opNorm A := by
  have h0 : 0 ≤ fro A := Real.sqrt_nonneg _
  have h1 : 0 ≤ Real.sqrt n * opNorm A :=
    mul_nonneg (Real.sqrt_nonneg _) (pe8_opNorm_nonneg _)
  apply (pow_le_pow_iff_left₀ h0 h1 (by norm_num : (2 : ℕ) ≠ 0)).mp
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity),
    mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa [Real.norm_eq_abs, sq_abs] using pe8_fro_sq_le A

private lemma pe8s_frobIP_outer {m n p q : ℕ} (Pt : Mat m n) (L : Mat m p) (a : Vec p)
    (b : Vec q) (Rr : Mat q n) :
    frobIP Pt (L * outer a b * Rr) = a ⬝ᵥ ((Lᵀ * Pt * Rrᵀ) *ᵥ b) := by
  unfold frobIP outer
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.transpose_vecMulVec,
    Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec a,
    Matrix.vecMul_transpose, Matrix.mulVec_transpose, dotProduct_comm]

private lemma pe8s_dot_smul {p q : ℕ} (c : ℝ) (rA : Mat p p) (rB : Mat q q) (x : Vec p)
    (y : Vec q) (M : Mat p q) :
    (c • (rA *ᵥ x)) ⬝ᵥ (M *ᵥ (c • (rB *ᵥ y))) = c ^ 2 * (x ⬝ᵥ ((rAᵀ * M * rB) *ᵥ y)) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec]
  simp only [smul_eq_mul]
  ring

private lemma pe8s_dot_sum {p q : ℕ} (x : Vec p) (K : Mat p q) (y : Vec q) :
    x ⬝ᵥ (K *ᵥ y) = ∑ i, ∑ l, K i l * (x i * y l) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

private lemma pe8s_frobIP_add {m n : ℕ} (X Y Z : Mat m n) :
    frobIP X (Y + Z) = frobIP X Y + frobIP X Z := by
  simp [frobIP, Matrix.transpose_add, Matrix.mul_add, Matrix.trace_add]

private lemma pe8s_frobIP_sub {m n : ℕ} (X Y Z : Mat m n) :
    frobIP X (Y - Z) = frobIP X Y - frobIP X Z := by
  simp [frobIP, Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub]

private lemma pe8s_frobIP_smul {m n : ℕ} (c : ℝ) (X Y : Mat m n) :
    frobIP X (c • Y) = c * frobIP X Y := by
  simp [frobIP, Matrix.transpose_smul, Matrix.mul_smul, Matrix.trace_smul]

private lemma pe8s_frobIP_sum {m n B : ℕ} (X : Mat m n) (Y : Fin B → Mat m n) :
    frobIP X (∑ a, Y a) = ∑ a, frobIP X (Y a) := by
  simp [frobIP, Matrix.transpose_sum, Matrix.mul_sum, Matrix.trace_sum]

private lemma pe8s_fro_sq {a b : ℕ} (A : Mat a b) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (by positivity)]
  simp only [Real.norm_eq_abs, sq_abs]

private lemma pe8s_fro_nonneg {a b : ℕ} (A : Mat a b) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma pe8s_fro_transpose {a b : ℕ} (A : Mat a b) : fro Aᵀ = fro A := by
  unfold fro
  rw [Finset.sum_comm]
  rfl

private lemma pe8s_fro_mul_left {a b c : ℕ} (A : Mat a b) (M : Mat b c) :
    fro (A * M) ≤ opNorm A * fro M := by
  have h0 := pe8_opNorm_nonneg A
  refine (pow_le_pow_iff_left₀ (pe8s_fro_nonneg _) (mul_nonneg h0 (pe8s_fro_nonneg _))
    (by norm_num : (2 : ℕ) ≠ 0)).mp ?_
  rw [mul_pow, pe8s_fro_sq, pe8s_fro_sq]
  have hc : ∀ i j, (A * M) i j = (A *ᵥ fun k => M k j) i := by
    intro i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp_rw [hc]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => M i j ^ 2), Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => pe8_sum_sq_mulVec_le A _

private lemma pe8s_fro_mul_right {a b c : ℕ} (M : Mat a b) (C : Mat b c) :
    fro (M * C) ≤ fro M * opNorm C := by
  rw [← pe8s_fro_transpose, Matrix.transpose_mul]
  have h := pe8s_fro_mul_left Cᵀ Mᵀ
  rw [pe8m_op_transpose_copy, pe8s_fro_transpose] at h
  linarith

private lemma pe8s_fro_outer {a b : ℕ} (x : Vec a) (y : Vec b) :
    fro (outer x y) = Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ j, y j ^ 2) := by
  rw [← Real.sqrt_mul (by positivity), Finset.sum_mul]
  unfold fro outer
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.vecMulVec_apply, mul_pow]

private lemma pe8s_coord_pow (k p : ℕ) (i : Fin k) :
    Integrable (fun z : Vec k => z i ^ p) (Muon.Foundations.stdGaussianPi k) := by
  have h := Muon.Foundations.gaussian_integrable_pow p
  rw [← Muon.Foundations.stdGaussianPi_map_coord k i] at h
  exact (integrable_map_measure (measurable_id.pow_const p).aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable).1 h

private lemma pe8s_memLp_zw {m n : ℕ} (i : Fin m) (l : Fin n) :
    MemLp (fun z : Vec m × Vec n => z.1 i * z.2 l) 2 (gaussPair m n) := by
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
  have h : Integrable (fun z : Vec m × Vec n => z.1 i ^ 2 * z.2 l ^ 2) (gaussPair m n) := by
    unfold gaussPair; exact (pe8s_coord_pow m 2 i).mul_prod (pe8s_coord_pow n 2 l)
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only; ring

private lemma pe8s_memLp_zz {m n : ℕ} (i k : Fin m) :
    MemLp (fun z : Vec m × Vec n => z.1 i * z.1 k - (1 : Mat m m) i k) 2 (gaussPair m n) := by
  refine MemLp.sub ?_ (memLp_const _)
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
  have h4 : ∀ j : Fin m, Integrable (fun z : Vec m × Vec n => z.1 j ^ 4) (gaussPair m n) := by
    intro j; unfold gaussPair; exact (pe8s_coord_pow m 4 j).comp_fst _
  refine ((h4 i).add (h4 k)).mono' (by fun_prop) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (z.1 i ^ 2 - z.1 k ^ 2), sq_nonneg (z.1 i), sq_nonneg (z.1 k)]

private lemma pe8s_memLp_ww {m n : ℕ} (i k : Fin n) :
    MemLp (fun z : Vec m × Vec n => z.2 i * z.2 k - (1 : Mat n n) i k) 2 (gaussPair m n) := by
  refine MemLp.sub ?_ (memLp_const _)
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
  have h4 : ∀ j : Fin n, Integrable (fun z : Vec m × Vec n => z.2 j ^ 4) (gaussPair m n) := by
    intro j; unfold gaussPair; exact (pe8s_coord_pow n 4 j).comp_snd _
  refine ((h4 i).add (h4 k)).mono' (by fun_prop) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (z.2 i ^ 2 - z.2 k ^ 2), sq_nonneg (z.2 i), sq_nonneg (z.2 k)]

private lemma pe8s_sqrt_of_sqrt_le {a b : ℝ} (hb : 0 ≤ b) (h : Real.sqrt a ≤ Real.sqrt b) :
    a ≤ b ∨ a < 0 := by
  by_cases ha : 0 ≤ a
  · left; exact (Real.sqrt_le_sqrt_iff hb).1 h
  · right; linarith

private lemma pe8s_bessel1 {m n : ℕ} (c : Vec m × Vec n → ℝ) (hc : Measurable c)
    (h2 : MemLp c 2 (gaussPair m n)) :
    Real.sqrt (∑ i, ∑ l, (∫ z, z.1 i * z.2 l * c z ∂(gaussPair m n)) ^ 2) ≤
      Real.sqrt (∫ z, c z ^ 2 ∂(gaussPair m n)) := by
  have hm : Measurable[MeasurableSpace.comap (id : Vec m × Vec n → Vec m × Vec n) inferInstance ⊔ ⊥] c := by
    rw [MeasurableSpace.comap_id, sup_bot_eq]; exact hc
  have h := lem_app_de_bessel_i (𝕜 := ℝ) (gaussPair m n) id Measure.map_id ⊥ bot_le
    (indep_bot_right _) c hm h2
  simp only [condExp_bot, id, RCLike.ofReal_real_eq_id, Real.norm_eq_abs, sq_abs] at h
  obtain ⟨ζ, hζ⟩ := h.exists
  exact hζ

private lemma pe8s_bessel2 {m n : ℕ} (c : Vec m × Vec n → ℝ) (hc : Measurable c)
    (h2 : MemLp c 2 (gaussPair m n)) :
    Real.sqrt (∑ i, ∑ k, (∫ z, (z.1 i * z.1 k - (1 : Mat m m) i k) * c z ∂(gaussPair m n)) ^ 2) ≤
      Real.sqrt 2 * Real.sqrt (∫ z, c z ^ 2 ∂(gaussPair m n)) := by
  have hm : Measurable[MeasurableSpace.comap (id : Vec m × Vec n → Vec m × Vec n) inferInstance ⊔ ⊥] c := by
    rw [MeasurableSpace.comap_id, sup_bot_eq]; exact hc
  have h := lem_app_de_bessel_ii (𝕜 := ℝ) (gaussPair m n) id Measure.map_id ⊥ bot_le
    (indep_bot_right _) c hm h2
  simp only [condExp_bot, id, RCLike.ofReal_real_eq_id, Real.norm_eq_abs, sq_abs] at h
  obtain ⟨ζ, hζ⟩ := h.exists
  exact hζ

private lemma pe8s_bessel3 {m n : ℕ} (c : Vec m × Vec n → ℝ) (hc : Measurable c)
    (h2 : MemLp c 2 (gaussPair m n)) :
    Real.sqrt (∑ i, ∑ k, (∫ z, (z.2 i * z.2 k - (1 : Mat n n) i k) * c z ∂(gaussPair m n)) ^ 2) ≤
      Real.sqrt 2 * Real.sqrt (∫ z, c z ^ 2 ∂(gaussPair m n)) := by
  have hm : Measurable[MeasurableSpace.comap (id : Vec m × Vec n → Vec m × Vec n) inferInstance ⊔ ⊥] c := by
    rw [MeasurableSpace.comap_id, sup_bot_eq]; exact hc
  have h := lem_app_de_bessel_iii (𝕜 := ℝ) (gaussPair m n) id Measure.map_id ⊥ bot_le
    (indep_bot_right _) c hm h2
  simp only [condExp_bot, id, RCLike.ofReal_real_eq_id, Real.norm_eq_abs, sq_abs] at h
  obtain ⟨ζ, hζ⟩ := h.exists
  exact hζ

private lemma pe8s_pair_mixed {m n : ℕ} (c : Vec m × Vec n → ℝ) (hc : Measurable c)
    (h2 : MemLp c 2 (gaussPair m n)) (K : Mat m n) :
    Integrable (fun z : Vec m × Vec n => c z * (z.1 ⬝ᵥ (K *ᵥ z.2))) (gaussPair m n) ∧
    |∫ z, c z * (z.1 ⬝ᵥ (K *ᵥ z.2)) ∂(gaussPair m n)| ≤
      fro K * Real.sqrt (∫ z, c z ^ 2 ∂(gaussPair m n)) := by
  have hi : ∀ i l, Integrable (fun z : Vec m × Vec n => z.1 i * z.2 l * c z) (gaussPair m n) :=
    fun i l => (pe8s_memLp_zw i l).integrable_mul h2
  have he : ∀ z : Vec m × Vec n, c z * (z.1 ⬝ᵥ (K *ᵥ z.2)) =
      ∑ i, ∑ l, K i l * (z.1 i * z.2 l * c z) := by
    intro z; rw [pe8s_dot_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
  simp_rw [he]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ =>
    (hi i l).const_mul _, ?_⟩
  have h4 : ∫ z, ∑ i, ∑ l, K i l * (z.1 i * z.2 l * c z) ∂(gaussPair m n) =
      ∑ i, ∫ z, ∑ l, K i l * (z.1 i * z.2 l * c z) ∂(gaussPair m n) :=
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => (hi i l).const_mul _
  rw [h4]
  have h3 : ∀ i, ∫ z, ∑ l, K i l * (z.1 i * z.2 l * c z) ∂(gaussPair m n) =
      ∑ l, K i l * ∫ z, z.1 i * z.2 l * c z ∂(gaussPair m n) := by
    intro i
    rw [integral_finsetSum _ fun l _ => (hi i l).const_mul _]
    simp only [integral_const_mul]
  simp_rw [h3]
  let I : Mat m n := Matrix.of fun i l => ∫ z, z.1 i * z.2 l * c z ∂(gaussPair m n)
  have hI : ∑ i, ∑ l, K i l * ∫ z, z.1 i * z.2 l * c z ∂(gaussPair m n) = frobIP K I := by
    rw [pe8p_frobIP_eq]; rfl
  rw [hI]
  refine (pe8m_frobIP_le_copy K I).trans (mul_le_mul_of_nonneg_left ?_ (pe8s_fro_nonneg K))
  have : fro I = Real.sqrt (∑ i, ∑ l, (∫ z, z.1 i * z.2 l * c z ∂(gaussPair m n)) ^ 2) := by
    unfold fro; simp [I, Real.norm_eq_abs, sq_abs]
  rw [this]; exact pe8s_bessel1 c hc h2

private lemma pe8s_pair_mixed' {m n : ℕ} (c : Vec m × Vec n → ℝ) (hc : Measurable c)
    (h2 : MemLp c 2 (gaussPair m n)) (K : Mat n m) :
    Integrable (fun z : Vec m × Vec n => c z * (z.2 ⬝ᵥ (K *ᵥ z.1))) (gaussPair m n) ∧
    |∫ z, c z * (z.2 ⬝ᵥ (K *ᵥ z.1)) ∂(gaussPair m n)| ≤
      fro K * Real.sqrt (∫ z, c z ^ 2 ∂(gaussPair m n)) := by
  have he : ∀ z : Vec m × Vec n, z.2 ⬝ᵥ (K *ᵥ z.1) = z.1 ⬝ᵥ (Kᵀ *ᵥ z.2) := by
    intro z
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  simp_rw [he]
  have h := pe8s_pair_mixed c hc h2 Kᵀ
  rwa [pe8s_fro_transpose] at h

private lemma pe8s_quad_id {k : ℕ} (K : Mat k k) (x : Vec k) (c : ℝ) :
    c * (x ⬝ᵥ (K *ᵥ x)) = ∑ i, ∑ l, K i l * ((x i * x l - (1 : Mat k k) i l) * c) + K.trace * c := by
  rw [pe8s_dot_sum]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, mul_ite, ite_mul,
    mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.trace,
    Matrix.diag, Finset.mul_sum, Finset.sum_mul]
  ring_nf

private lemma pe8s_pair_quad1 {m n : ℕ} (c : Vec m × Vec n → ℝ) (hc : Measurable c)
    (h2 : MemLp c 2 (gaussPair m n)) (K : Mat m m) :
    Integrable (fun z : Vec m × Vec n => c z * (z.1 ⬝ᵥ (K *ᵥ z.1))) (gaussPair m n) ∧
    |∫ z, c z * (z.1 ⬝ᵥ (K *ᵥ z.1)) ∂(gaussPair m n) - K.trace * ∫ z, c z ∂(gaussPair m n)| ≤
      fro K * (Real.sqrt 2 * Real.sqrt (∫ z, c z ^ 2 ∂(gaussPair m n))) := by
  have hi : ∀ i l, Integrable (fun z : Vec m × Vec n =>
      (z.1 i * z.1 l - (1 : Mat m m) i l) * c z) (gaussPair m n) :=
    fun i l => (pe8s_memLp_zz i l).integrable_mul h2
  have hc1 : Integrable c (gaussPair m n) := h2.integrable (by norm_num)
  simp_rw [pe8s_quad_id]
  have hs : Integrable (fun z : Vec m × Vec n => ∑ i, ∑ l, K i l *
      ((z.1 i * z.1 l - (1 : Mat m m) i l) * c z)) (gaussPair m n) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => (hi i l).const_mul _
  refine ⟨hs.add (hc1.const_mul _), ?_⟩
  rw [integral_add hs (hc1.const_mul _), integral_const_mul, add_sub_cancel_right]
  have h4 : ∫ z, ∑ i, ∑ l, K i l * ((z.1 i * z.1 l - (1 : Mat _ _) i l) * c z) ∂(gaussPair m n) =
      ∑ i, ∫ z, ∑ l, K i l * ((z.1 i * z.1 l - (1 : Mat _ _) i l) * c z) ∂(gaussPair m n) :=
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => (hi i l).const_mul _
  rw [h4]
  have h3 : ∀ i, ∫ z, ∑ l, K i l * ((z.1 i * z.1 l - (1 : Mat m m) i l) * c z) ∂(gaussPair m n) =
      ∑ l, K i l * ∫ z, (z.1 i * z.1 l - (1 : Mat m m) i l) * c z ∂(gaussPair m n) := by
    intro i
    rw [integral_finsetSum _ fun l _ => (hi i l).const_mul _]
    simp only [integral_const_mul]
  simp_rw [h3]
  let I : Mat m m := Matrix.of fun i l =>
    ∫ z, (z.1 i * z.1 l - (1 : Mat m m) i l) * c z ∂(gaussPair m n)
  have hI : ∑ i, ∑ l, K i l * ∫ z, (z.1 i * z.1 l - (1 : Mat m m) i l) * c z ∂(gaussPair m n) =
      frobIP K I := by
    rw [pe8p_frobIP_eq]; rfl
  rw [hI]
  refine (pe8m_frobIP_le_copy K I).trans (mul_le_mul_of_nonneg_left ?_ (pe8s_fro_nonneg K))
  have : fro I = Real.sqrt (∑ i, ∑ l,
      (∫ z, (z.1 i * z.1 l - (1 : Mat m m) i l) * c z ∂(gaussPair m n)) ^ 2) := by
    unfold fro; simp [I, Real.norm_eq_abs, sq_abs]
  rw [this]; exact pe8s_bessel2 c hc h2

private lemma pe8s_pair_quad2 {m n : ℕ} (c : Vec m × Vec n → ℝ) (hc : Measurable c)
    (h2 : MemLp c 2 (gaussPair m n)) (K : Mat n n) :
    Integrable (fun z : Vec m × Vec n => c z * (z.2 ⬝ᵥ (K *ᵥ z.2))) (gaussPair m n) ∧
    |∫ z, c z * (z.2 ⬝ᵥ (K *ᵥ z.2)) ∂(gaussPair m n) - K.trace * ∫ z, c z ∂(gaussPair m n)| ≤
      fro K * (Real.sqrt 2 * Real.sqrt (∫ z, c z ^ 2 ∂(gaussPair m n))) := by
  have hi : ∀ i l, Integrable (fun z : Vec m × Vec n =>
      (z.2 i * z.2 l - (1 : Mat n n) i l) * c z) (gaussPair m n) :=
    fun i l => (pe8s_memLp_ww i l).integrable_mul h2
  have hc1 : Integrable c (gaussPair m n) := h2.integrable (by norm_num)
  simp_rw [pe8s_quad_id]
  have hs : Integrable (fun z : Vec m × Vec n => ∑ i, ∑ l, K i l *
      ((z.2 i * z.2 l - (1 : Mat n n) i l) * c z)) (gaussPair m n) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => (hi i l).const_mul _
  refine ⟨hs.add (hc1.const_mul _), ?_⟩
  rw [integral_add hs (hc1.const_mul _), integral_const_mul, add_sub_cancel_right]
  have h4 : ∫ z, ∑ i, ∑ l, K i l * ((z.2 i * z.2 l - (1 : Mat _ _) i l) * c z) ∂(gaussPair m n) =
      ∑ i, ∫ z, ∑ l, K i l * ((z.2 i * z.2 l - (1 : Mat _ _) i l) * c z) ∂(gaussPair m n) :=
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => (hi i l).const_mul _
  rw [h4]
  have h3 : ∀ i, ∫ z, ∑ l, K i l * ((z.2 i * z.2 l - (1 : Mat n n) i l) * c z) ∂(gaussPair m n) =
      ∑ l, K i l * ∫ z, (z.2 i * z.2 l - (1 : Mat n n) i l) * c z ∂(gaussPair m n) := by
    intro i
    rw [integral_finsetSum _ fun l _ => (hi i l).const_mul _]
    simp only [integral_const_mul]
  simp_rw [h3]
  let I : Mat n n := Matrix.of fun i l =>
    ∫ z, (z.2 i * z.2 l - (1 : Mat n n) i l) * c z ∂(gaussPair m n)
  have hI : ∑ i, ∑ l, K i l * ∫ z, (z.2 i * z.2 l - (1 : Mat n n) i l) * c z ∂(gaussPair m n) =
      frobIP K I := by
    rw [pe8p_frobIP_eq]; rfl
  rw [hI]
  refine (pe8m_frobIP_le_copy K I).trans (mul_le_mul_of_nonneg_left ?_ (pe8s_fro_nonneg K))
  have : fro I = Real.sqrt (∑ i, ∑ l,
      (∫ z, (z.2 i * z.2 l - (1 : Mat n n) i l) * c z ∂(gaussPair m n)) ^ 2) := by
    unfold fro; simp [I, Real.norm_eq_abs, sq_abs]
  rw [this]; exact pe8s_bessel3 c hc h2

private lemma pe8s_L2_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f : Ω → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (h : eLpNorm f 2 μ ≤ ENNReal.ofReal L) :
    MemLp f 2 μ ∧ Real.sqrt (∫ x, f x ^ 2 ∂μ) ≤ L := by
  have hm : MemLp f 2 μ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  refine ⟨hm, ?_⟩
  have he := hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  rw [he, ENNReal.ofReal_le_ofReal_iff hL] at h
  have e1 : (fun a => ‖f a‖ ^ (2 : ℝ≥0∞).toReal) = fun a => f a ^ 2 := by
    funext a
    rw [Real.norm_eq_abs, ENNReal.toReal_ofNat, Real.rpow_two, sq_abs]
  rw [e1] at h
  rw [Real.sqrt_eq_rpow]
  simpa using h

private lemma pe8s_int_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f g : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (A B : ℝ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hfA : eLpNorm f 2 μ ≤ ENNReal.ofReal A) (hgB : eLpNorm g 2 μ ≤ ENNReal.ofReal B) :
    Integrable (fun x => f x * g x) μ ∧ |∫ x, f x * g x ∂μ| ≤ A * B := by
  have h1 := pe8_holder f g hf hg 1 le_rfl
  have h2 : eLpNorm (fun x => f x * g x) 1 μ ≤ ENNReal.ofReal (A * B) := by
    rw [ENNReal.ofReal_mul hA]
    refine le_trans (by simpa using h1) (mul_le_mul' hfA hgB)
  have hm : AEStronglyMeasurable (fun x => f x * g x) μ := hf.mul hg
  have hi : Integrable (fun x => f x * g x) μ :=
    memLp_one_iff_integrable.mp (lt_of_le_of_lt h2 ENNReal.ofReal_lt_top)
  refine ⟨hi, ?_⟩
  calc |∫ x, f x * g x ∂μ| = ‖∫ x, f x * g x ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ‖f x * g x‖ ∂μ := norm_integral_le_integral_norm _
    _ = (eLpNorm (fun x => f x * g x) 1 μ).toReal := by
        rw [integral_norm_eq_lintegral_enorm hm, eLpNorm_one_eq_lintegral_enorm hm]
    _ ≤ A * B := ENNReal.toReal_le_of_le_ofReal (mul_nonneg hA hB) h2

private lemma pe8s_L4_prod {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f g : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (A B : ℝ) (hA : 0 ≤ A)
    (hfA : eLpNorm f 4 μ ≤ ENNReal.ofReal A) (hgB : eLpNorm g 4 μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun x => f x * g x) 2 μ ≤ ENNReal.ofReal (A * B) := by
  have h1 := pe8_holder f g hf hg 2 (by norm_num)
  rw [ENNReal.ofReal_mul hA]
  refine le_trans (by simpa using h1) (mul_le_mul' (by simpa using hfA) (by simpa using hgB))

private lemma pe8s_resid_moment (γ CS : ℝ) :
    ∃ Ke : ℝ, 0 ≤ Ke ∧ ∀ {m n B : ℕ} (Cv : Covariances m n) (CE : Mat m n),
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B → opNorm Cv.Sout ≤ CS → opNorm Cv.Sin ≤ CS →
      eLpNorm (fun z : Vec m × Vec n => resid CE z) 4 (gaussPair m n) ≤
        ENNReal.ofReal (Ke * fro CE) ∧
      eLpNorm (fun z : Vec m × Vec n => resid CE z) 2 (gaussPair m n) ≤
        ENNReal.ofReal (Ke * fro CE) := by
  obtain ⟨K1, hK1, hb1⟩ := pe8_t_moment 1 4 (by norm_num) (by norm_num) γ CS
  refine ⟨K1, hK1, ?_⟩
  intro m n B Cv CE hm hn hCo hCi
  have h4 : eLpNorm (fun z : Vec m × Vec n => resid CE z) 4 (gaussPair m n) ≤
      ENNReal.ofReal (K1 * fro CE) := by
    by_cases hCE : CE = 0
    · subst hCE
      have : (fun z : Vec m × Vec n => resid (0 : Mat m n) z) = fun _ => 0 := by
        funext z; simp [resid]
      rw [this]; simp
    · have hfpos : 0 < fro CE := by
        unfold fro
        apply Real.sqrt_pos.2
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hCE
        obtain ⟨j, hij⟩ := Function.ne_iff.mp hi
        refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => by positivity)
          ⟨i, Finset.mem_univ i, ?_⟩
        refine Finset.sum_pos' (fun j _ => by positivity) ⟨j, Finset.mem_univ j, ?_⟩
        positivity
      let Aen : Mat m n := (fro CE)⁻¹ • CE
      have hAen : fro Aen = 1 := by
        change fro ((fro CE)⁻¹ • CE) = 1
        rw [pe8_fro_smul, abs_of_pos (inv_pos.mpr hfpos), inv_mul_cancel₀ hfpos.ne']
      have hres : ∀ z, resid CE z = fro CE * resid Aen z := by
        intro z
        unfold Aen resid
        simp only [Matrix.smul_mulVec, dotProduct_smul]
        simp [smul_eq_mul, hfpos.ne']
      have hb := hb1 Cv Aen hAen hm hn hCo hCi
      have hd := pe8_cont_resid Aen
      have hN := pe8_cont_momN Cv B
      refine pe8_bound_one (fun z => resid CE z) _ (fro CE) K1 hfpos.le
        (pe8_cont_resid CE).aestronglyMeasurable 4 (fun z => ?_) (by simpa using hb) |>.trans ?_
      · rw [hres, abs_mul, abs_of_pos hfpos]
        refine mul_le_mul_of_nonneg_left ?_ hfpos.le
        have h0 : 0 ≤ momN Cv B z := by unfold momN; positivity
        nlinarith [abs_nonneg (resid Aen z)]
      · rw [mul_comm]
  refine ⟨h4, le_trans ?_ h4⟩
  exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)

private lemma pe8s_op_le_fro {p q : ℕ} (K : Mat p q) : opNorm K ≤ fro K := by
  refine pe8p_opSq K (fro K) (Real.sqrt_nonneg _) fun y => ?_
  rw [pe8s_fro_sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => K i j) y
  simpa [Matrix.mulVec, dotProduct] using this

private lemma pe8s_fro_sandwich {a b c d : ℕ} (A : Mat a b) (M : Mat b c) (C : Mat c d) :
    fro (A * M * C) ≤ opNorm A * fro M * opNorm C := by
  refine (pe8s_fro_mul_right _ C).trans ?_
  exact mul_le_mul_of_nonneg_right (pe8s_fro_mul_left A M) (pe8_opNorm_nonneg C)

private lemma pe8s_fro_K {a b p q : ℕ} (rA : Mat p p) (rB : Mat q q) (L : Mat a p) (Pt : Mat a b)
    (Rr : Mat q b) :
    fro (rAᵀ * (Lᵀ * Pt * Rrᵀ) * rB) ≤
      opNorm rA * opNorm rB * (opNorm L * opNorm Rr * fro Pt) := by
  refine (pe8s_fro_sandwich _ _ _).trans ?_
  have h1 := pe8s_fro_sandwich Lᵀ Pt Rrᵀ
  rw [pe8m_op_transpose_copy, pe8m_op_transpose_copy] at h1
  rw [pe8m_op_transpose_copy]
  have hA := pe8_opNorm_nonneg rA
  have hB := pe8_opNorm_nonneg rB
  calc opNorm rA * fro (Lᵀ * Pt * Rrᵀ) * opNorm rB
      ≤ opNorm rA * (opNorm L * fro Pt * opNorm Rr) * opNorm rB := by gcongr
    _ = _ := by ring

private lemma pe8s_trace_K {a b p : ℕ} (rA : Mat p p) (hr : rAᵀ = rA) (L : Mat a p)
    (Pt : Mat a b) (Rr : Mat p b) :
    (rAᵀ * (Lᵀ * Pt * Rrᵀ) * rA).trace = frobIP Pt (L * (rA * rA) * Rr) := by
  unfold frobIP
  rw [hr, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, hr]
  rw [Matrix.trace_mul_comm Pt]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm Rrᵀ]
  simp only [Matrix.mul_assoc]

private lemma pe8s_frobIP_tr_bound {a b p q : ℕ} (Pt : Mat a b) (L : Mat a p) (S : Mat p q)
    (Rr : Mat q b) :
    |frobIP Pt (L * S * Rr)| ≤ fro Pt * (Real.sqrt b * (opNorm L * opNorm S * opNorm Rr)) := by
  refine (pe8m_frobIP_le_copy _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (pe8s_fro_nonneg _)
  refine (pe8m_fro_le_sqrt_cols_op_copy _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine (pe8_opNorm_mul_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (pe8_opNorm_mul_le _ _) (pe8_opNorm_nonneg _)

private lemma pe8s_inv_sqrt_sq (B : ℕ) : ((Real.sqrt (B : ℝ))⁻¹) ^ 2 = (B : ℝ)⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg B)]

private lemma pe8s_q_uu {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (Pt : Mat m n) (L : Mat m m)
    (Rr : Mat m n) (z : Vec m × Vec n) :
    frobIP Pt (L * outer (sampU Cv B z) (sampU Cv B z) * Rr) =
      (B : ℝ)⁻¹ * (z.1 ⬝ᵥ (((rOut Cv)ᵀ * (Lᵀ * Pt * Rrᵀ) * rOut Cv) *ᵥ z.1)) := by
  rw [pe8s_frobIP_outer]; unfold sampU; rw [pe8s_dot_smul, pe8s_inv_sqrt_sq]

private lemma pe8s_q_uv {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (Pt : Mat m n) (L : Mat m m)
    (Rr : Mat n n) (z : Vec m × Vec n) :
    frobIP Pt (L * outer (sampU Cv B z) (sampV Cv B z) * Rr) =
      (B : ℝ)⁻¹ * (z.1 ⬝ᵥ (((rOut Cv)ᵀ * (Lᵀ * Pt * Rrᵀ) * rIn Cv) *ᵥ z.2)) := by
  rw [pe8s_frobIP_outer]; unfold sampU sampV; rw [pe8s_dot_smul, pe8s_inv_sqrt_sq]

private lemma pe8s_q_vu {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (Pt : Mat m n) (L : Mat m n)
    (Rr : Mat m n) (z : Vec m × Vec n) :
    frobIP Pt (L * outer (sampV Cv B z) (sampU Cv B z) * Rr) =
      (B : ℝ)⁻¹ * (z.2 ⬝ᵥ (((rIn Cv)ᵀ * (Lᵀ * Pt * Rrᵀ) * rOut Cv) *ᵥ z.1)) := by
  rw [pe8s_frobIP_outer]; unfold sampU sampV; rw [pe8s_dot_smul, pe8s_inv_sqrt_sq]

private lemma pe8s_q_vv {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (Pt : Mat m n) (L : Mat m n)
    (Rr : Mat n n) (z : Vec m × Vec n) :
    frobIP Pt (L * outer (sampV Cv B z) (sampV Cv B z) * Rr) =
      (B : ℝ)⁻¹ * (z.2 ⬝ᵥ (((rIn Cv)ᵀ * (Lᵀ * Pt * Rrᵀ) * rIn Cv) *ᵥ z.2)) := by
  rw [pe8s_frobIP_outer]; unfold sampV; rw [pe8s_dot_smul, pe8s_inv_sqrt_sq]

private lemma pe8s_rOut_sq {m n : ℕ} (Cv : Covariances m n) : rOut Cv * rOut Cv = Cv.Sout :=
  CFC.sqrt_mul_sqrt_self Cv.Sout (Matrix.nonneg_iff_posSemidef.mpr Cv.psdOut)

private lemma pe8s_rIn_sq {m n : ℕ} (Cv : Covariances m n) : rIn Cv * rIn Cv = Cv.Sin :=
  CFC.sqrt_mul_sqrt_self Cv.Sin (Matrix.nonneg_iff_posSemidef.mpr Cv.psdIn)

private lemma pe8s_rOut_T {m n : ℕ} (Cv : Covariances m n) : (rOut Cv)ᵀ = rOut Cv := by
  unfold rOut; exact pe8_sqrt_symm _

private lemma pe8s_rIn_T {m n : ℕ} (Cv : Covariances m n) : (rIn Cv)ᵀ = rIn Cv := by
  unfold rIn; exact pe8_sqrt_symm _

private lemma pe8s_rOut_op {m n : ℕ} (Cv : Covariances m n) (CS : ℝ) (h : opNorm Cv.Sout ≤ CS) :
    opNorm (rOut Cv) * opNorm (rOut Cv) ≤ CS := by
  unfold rOut; rw [pe8_opNorm_sqrt_mul_self _ Cv.psdOut]; exact h

private lemma pe8s_rIn_op {m n : ℕ} (Cv : Covariances m n) (CS : ℝ) (h : opNorm Cv.Sin ≤ CS) :
    opNorm (rIn Cv) * opNorm (rIn Cv) ≤ CS := by
  unfold rIn; rw [pe8_opNorm_sqrt_mul_self _ Cv.psdIn]; exact h

private lemma pe8s_ofReal_mono {x : ℝ≥0∞} {a b : ℝ} (h : x ≤ ENNReal.ofReal a) (hab : a ≤ b) :
    x ≤ ENNReal.ofReal b := h.trans (ENNReal.ofReal_le_ofReal hab)

private lemma pe8s_core_raw (certQ : Muon.External.GaussianQuadFormLp) (γ CS s0 : ℝ)
    (hs0 : 0 < s0) :
    ∃ C4 C2 K1 Ke : ℝ, 0 ≤ C4 ∧ 0 ≤ C2 ∧ 0 ≤ K1 ∧ 0 ≤ Ke ∧
    ∀ {m n B : ℕ} (Cv : Covariances m n) (T Ah CE Pt : Mat m n) (ϖ s : ℝ)
      (f : Vec m × Vec n → ℝ), 0 < B →
      opNorm Cv.Sout ≤ CS → opNorm Cv.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      fro Ah = 1 → s0 ≤ s → ϖ ∈ Icc (0 : ℝ) 1 →
      (∀ z, f z = resid CE z *
        (dAlpha3 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) *
            frobIP Pt (Rs T s * outer (sampU Cv B z) (sampU Cv B z) * Xs T s)
          + s * dAlpha1 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) *
            frobIP Pt (Rs T s * outer (sampU Cv B z) (sampV Cv B z) * Rts T s)
          - dAlpha1 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) *
            frobIP Pt (Xs T s * outer (sampV Cv B z) (sampU Cv B z) * Xs T s)
          - s * dAlpha2 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) *
            frobIP Pt (Xs T s * outer (sampV Cv B z) (sampV Cv B z) * Rts T s))) →
      Integrable f (gaussPair m n) ∧
      |∫ z, f z ∂(gaussPair m n) + ϖ ^ 2 / B * (Fs Cv B Ah Pt ϖ s T * frobIP Ah CE)| ≤
        (B : ℝ)⁻¹ * (
          fro ((rOut Cv)ᵀ * ((Rs T s)ᵀ * Pt * (Xs T s)ᵀ) * rOut Cv) *
              (Real.sqrt 2 * (Ke * fro CE * (C4 * ϖ ^ 2)))
          + s * (fro ((rOut Cv)ᵀ * ((Rs T s)ᵀ * Pt * (Rts T s)ᵀ) * rIn Cv) *
              (Ke * fro CE * (C4 * ϖ)))
          + fro ((rIn Cv)ᵀ * ((Xs T s)ᵀ * Pt * (Xs T s)ᵀ) * rOut Cv) * (Ke * fro CE * (C4 * ϖ))
          + s * (fro ((rIn Cv)ᵀ * ((Xs T s)ᵀ * Pt * (Rts T s)ᵀ) * rIn Cv) *
              (Real.sqrt 2 * (Ke * fro CE * (C4 * ϖ ^ 2 / s))))
          + |frobIP Pt (Rs T s * Cv.Sout * Xs T s)| * (Ke * fro CE * (C2 * ϖ ^ 2 / Real.sqrt B))
          + s * (|frobIP Pt (Xs T s * Cv.Sin * Rts T s)| *
              (Ke * fro CE * (C2 * ϖ ^ 2 / (s * Real.sqrt B))))
          + ϖ ^ 2 * (s * sigmaT Cv B T s * |frobIP Pt (Rs T s * Cv.Sout * Xs T s)|
              + s * sigmaS Cv B T s * |frobIP Pt (Xs T s * Cv.Sin * Rts T s)|) *
            (24 * xMinor Cv B T ϖ s * opNorm CE * opNorm Ah)) := by
  obtain ⟨C4r, hC4⟩ := lem_app_dyn_coefficients certQ 4 (by norm_num) s0 hs0 γ CS
  obtain ⟨C2r, hC2⟩ := lem_app_dyn_coefficients certQ 2 (by norm_num) s0 hs0 γ CS
  obtain ⟨K1, hK1, hσb⟩ := pe8_sigma_bound certQ γ CS
  obtain ⟨Ke, hKe, hKe'⟩ := pe8s_resid_moment γ CS
  refine ⟨max C4r 0, max C2r 0, K1, Ke, le_max_right _ _, le_max_right _ _, hK1, hKe, ?_⟩
  intro m n B Cv T Ah CE Pt ϖ s f hB hCo hCi hm hn hA hs hϖ hf
  have hs_pos : 0 < s := lt_of_lt_of_le hs0 hs
  obtain ⟨hϖ0, hϖ1⟩ := hϖ
  set C4 := max C4r 0 with hC4def
  set C2 := max C2r 0 with hC2def
  have hC40 : 0 ≤ C4 := le_max_right _ _
  have hC20 : 0 ≤ C2 := le_max_right _ _
  obtain ⟨_, _, _, hb31, hb32, hb33⟩ := hC4 m n B Cv T Ah ϖ s hB hCo hCi hm hn hA hs ⟨hϖ0, hϖ1⟩
  obtain ⟨_, he2, he3, _, _, _⟩ := hC2 m n B Cv T Ah ϖ s hB hCo hCi hm hn hA hs ⟨hϖ0, hϖ1⟩
  obtain ⟨hE4, hE2⟩ := hKe' Cv CE hm hn hCo hCi
  -- abbreviations
  obtain ⟨e, he⟩ : ∃ e : Vec m × Vec n → ℝ, e = fun z => resid CE z := ⟨_, rfl⟩
  obtain ⟨a1, ha1⟩ : ∃ a : Vec m × Vec n → ℝ,
      a = fun z => dAlpha1 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a : Vec m × Vec n → ℝ,
      a = fun z => dAlpha2 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ a : Vec m × Vec n → ℝ,
      a = fun z => dAlpha3 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) := ⟨_, rfl⟩
  obtain ⟨ma1, ma2, ma3⟩ := pe8_cont_dAlpha Cv B T Ah ϖ s hs_pos ⟨hϖ0, hϖ1⟩
  rw [← ha1] at ma1; rw [← ha2] at ma2; rw [← ha3] at ma3
  have me : Continuous e := by rw [he]; exact pe8_cont_resid CE
  set x := xMinor Cv B T ϖ s with hxdef
  set σ := sigmaS Cv B T s with hσdef
  set σt := sigmaT Cv B T s with hσtdef
  have hσ0 : 0 ≤ σ := pe8_sigmaS_nonneg Cv B hB T s hs_pos
  have hσt0 : 0 ≤ σt := pe8_sigmaT_nonneg Cv B hB T s hs_pos
  have hx0 : 0 ≤ x := by rw [hxdef]; unfold xMinor; positivity
  obtain ⟨mf, mψ⟩ := pe8_cont_deriv (m := m) (n := n) Ah x hx0
  -- L4 norms of the products
  have hE4' : eLpNorm e 4 (gaussPair m n) ≤ ENNReal.ofReal (Ke * fro CE) := by rw [he]; exact hE4
  have hE2' : eLpNorm e 2 (gaussPair m n) ≤ ENNReal.ofReal (Ke * fro CE) := by rw [he]; exact hE2
  have hKf : 0 ≤ Ke * fro CE := mul_nonneg hKe (pe8s_fro_nonneg _)
  have hA1 : eLpNorm a1 4 (gaussPair m n) ≤ ENNReal.ofReal (C4 * ϖ) := by
    rw [ha1]; exact pe8s_ofReal_mono (by simpa using hb31)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hϖ0)
  have hA2 : eLpNorm a2 4 (gaussPair m n) ≤ ENNReal.ofReal (C4 * ϖ ^ 2 / s) := by
    rw [ha2]; exact pe8s_ofReal_mono (by simpa using hb32)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        hs_pos.le)
  have hA3 : eLpNorm a3 4 (gaussPair m n) ≤ ENNReal.ofReal (C4 * ϖ ^ 2) := by
    rw [ha3]; exact pe8s_ofReal_mono (by simpa using hb33)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hc1 := pe8s_L2_sqrt (fun z => e z * a1 z) _ (mul_nonneg hKf (by positivity))
    (pe8s_L4_prod e a1 me.aestronglyMeasurable ma1.aestronglyMeasurable _ _ hKf hE4' hA1)
  have hc2 := pe8s_L2_sqrt (fun z => e z * a2 z) _ (mul_nonneg hKf (by positivity))
    (pe8s_L4_prod e a2 me.aestronglyMeasurable ma2.aestronglyMeasurable _ _ hKf hE4' hA2)
  have hc3 := pe8s_L2_sqrt (fun z => e z * a3 z) _ (mul_nonneg hKf (by positivity))
    (pe8s_L4_prod e a3 me.aestronglyMeasurable ma3.aestronglyMeasurable _ _ hKf hE4' hA3)
  -- the four kernels
  obtain ⟨K1m, hK1m⟩ : ∃ K : Mat m m, K = (rOut Cv)ᵀ * ((Rs T s)ᵀ * Pt * (Xs T s)ᵀ) * rOut Cv :=
    ⟨_, rfl⟩
  obtain ⟨K2m, hK2m⟩ : ∃ K : Mat m n, K = (rOut Cv)ᵀ * ((Rs T s)ᵀ * Pt * (Rts T s)ᵀ) * rIn Cv :=
    ⟨_, rfl⟩
  obtain ⟨K3m, hK3m⟩ : ∃ K : Mat n m, K = (rIn Cv)ᵀ * ((Xs T s)ᵀ * Pt * (Xs T s)ᵀ) * rOut Cv :=
    ⟨_, rfl⟩
  obtain ⟨K4m, hK4m⟩ : ∃ K : Mat n n, K = (rIn Cv)ᵀ * ((Xs T s)ᵀ * Pt * (Rts T s)ᵀ) * rIn Cv :=
    ⟨_, rfl⟩
  have hfz : ∀ z, f z = (B : ℝ)⁻¹ * ((e z * a3 z) * (z.1 ⬝ᵥ (K1m *ᵥ z.1))
      + s * ((e z * a1 z) * (z.1 ⬝ᵥ (K2m *ᵥ z.2)))
      - (e z * a1 z) * (z.2 ⬝ᵥ (K3m *ᵥ z.1))
      - s * ((e z * a2 z) * (z.2 ⬝ᵥ (K4m *ᵥ z.2)))) := by
    intro z
    rw [hf z, pe8s_q_uu, pe8s_q_uv, pe8s_q_vu, pe8s_q_vv, he, ha1, ha2, ha3, hK1m, hK2m, hK3m,
      hK4m]
    ring
  have P1 := pe8s_pair_quad1 (fun z => e z * a3 z) (me.mul ma3).measurable hc3.1 K1m
  have P2 := pe8s_pair_mixed (fun z => e z * a1 z) (me.mul ma1).measurable hc1.1 K2m
  have P3 := pe8s_pair_mixed' (fun z => e z * a1 z) (me.mul ma1).measurable hc1.1 K3m
  have P4 := pe8s_pair_quad2 (fun z => e z * a2 z) (me.mul ma2).measurable hc2.1 K4m
  have hint : Integrable (fun z => (B : ℝ)⁻¹ * ((e z * a3 z) * (z.1 ⬝ᵥ (K1m *ᵥ z.1))
      + s * ((e z * a1 z) * (z.1 ⬝ᵥ (K2m *ᵥ z.2)))
      - (e z * a1 z) * (z.2 ⬝ᵥ (K3m *ᵥ z.1))
      - s * ((e z * a2 z) * (z.2 ⬝ᵥ (K4m *ᵥ z.2))))) (gaussPair m n) :=
    (((P1.1.add (P2.1.const_mul s)).sub P3.1).sub (P4.1.const_mul s)).const_mul _
  have hfeq : f = fun z => (B : ℝ)⁻¹ * ((e z * a3 z) * (z.1 ⬝ᵥ (K1m *ᵥ z.1))
      + s * ((e z * a1 z) * (z.1 ⬝ᵥ (K2m *ᵥ z.2)))
      - (e z * a1 z) * (z.2 ⬝ᵥ (K3m *ᵥ z.1))
      - s * ((e z * a2 z) * (z.2 ⬝ᵥ (K4m *ᵥ z.2)))) := funext hfz
  refine ⟨hfeq ▸ hint, ?_⟩
  have hIf : ∫ z, f z ∂(gaussPair m n) = (B : ℝ)⁻¹ * (
      ∫ z, (e z * a3 z) * (z.1 ⬝ᵥ (K1m *ᵥ z.1)) ∂(gaussPair m n)
      + s * ∫ z, (e z * a1 z) * (z.1 ⬝ᵥ (K2m *ᵥ z.2)) ∂(gaussPair m n)
      - ∫ z, (e z * a1 z) * (z.2 ⬝ᵥ (K3m *ᵥ z.1)) ∂(gaussPair m n)
      - s * ∫ z, (e z * a2 z) * (z.2 ⬝ᵥ (K4m *ᵥ z.2)) ∂(gaussPair m n)) := by
    rw [hfeq, integral_const_mul, integral_sub _ (P4.1.const_mul s), integral_sub,
      integral_add P1.1 (P2.1.const_mul s), integral_const_mul, integral_const_mul]
    · exact P1.1.add (P2.1.const_mul s)
    · exact P3.1
    · exact (P1.1.add (P2.1.const_mul s)).sub P3.1
  -- coefficient errors
  obtain ⟨r3, hr3⟩ : ∃ r : Vec m × Vec n → ℝ,
      r = fun z => a3 z + s * ϖ ^ 2 * σt * deriv (psiX x) (resid Ah z) := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ r : Vec m × Vec n → ℝ,
      r = fun z => a2 z - ϖ ^ 2 * σ * deriv (psiX x) (resid Ah z) := ⟨_, rfl⟩
  have hR3 : eLpNorm r3 2 (gaussPair m n) ≤ ENNReal.ofReal (C2 * ϖ ^ 2 / Real.sqrt B) := by
    rw [hr3, ha3]; exact pe8s_ofReal_mono (by simpa using he3)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        (Real.sqrt_nonneg _))
  have hR2 : eLpNorm r2 2 (gaussPair m n) ≤ ENNReal.ofReal (C2 * ϖ ^ 2 / (s * Real.sqrt B)) := by
    rw [hr2, ha2]; exact pe8s_ofReal_mono (by simpa using he2)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        (by positivity))
  have mr3 : Continuous r3 := by rw [hr3]; exact ma3.add (continuous_const.mul mψ)
  have mr2 : Continuous r2 := by rw [hr2]; exact ma2.sub (continuous_const.mul mψ)
  have I3 := pe8s_int_mul_le e r3 me.aestronglyMeasurable mr3.aestronglyMeasurable _ _ hKf
    (by positivity) hE2' hR3
  have I2 := pe8s_int_mul_le e r2 me.aestronglyMeasurable mr2.aestronglyMeasurable _ _ hKf
    (by positivity) hE2' hR2
  -- Gaussian response
  obtain ⟨_, _, _, _, hraw⟩ := lem_app_dyn_raw Ah hA
  obtain ⟨hJi, hJ, hρ⟩ := hraw CE x hx0
  have hJi' : Integrable (fun z => e z * deriv (psiX x) (resid Ah z)) (gaussPair m n) := by
    rw [he]; exact hJi
  have hc3eq : ∫ z, e z * a3 z ∂(gaussPair m n) = ∫ z, e z * r3 z ∂(gaussPair m n)
      - s * ϖ ^ 2 * σt * ∫ z, e z * deriv (psiX x) (resid Ah z) ∂(gaussPair m n) := by
    rw [← integral_const_mul, ← integral_sub I3.1 (hJi'.const_mul _)]
    congr 1; funext z; rw [hr3]; ring
  have hc2eq : ∫ z, e z * a2 z ∂(gaussPair m n) = ∫ z, e z * r2 z ∂(gaussPair m n)
      + ϖ ^ 2 * σ * ∫ z, e z * deriv (psiX x) (resid Ah z) ∂(gaussPair m n) := by
    rw [← integral_const_mul, ← integral_add I2.1 (hJi'.const_mul _)]
    congr 1; funext z; rw [hr2]; ring
  have hJ' : ∫ z, e z * deriv (psiX x) (resid Ah z) ∂(gaussPair m n) =
      frobIP Ah CE * bFun Ah x + frobIP CE (Ah * NFun Ah x * Ahᵀ * Ah) := by rw [he]; exact hJ
  -- traces
  have htr1 : K1m.trace = frobIP Pt (Rs T s * Cv.Sout * Xs T s) := by
    rw [hK1m, pe8s_trace_K _ (pe8s_rOut_T Cv), pe8s_rOut_sq]
  have htr4 : K4m.trace = frobIP Pt (Xs T s * Cv.Sin * Rts T s) := by
    rw [hK4m, pe8s_trace_K _ (pe8s_rIn_T Cv), pe8s_rIn_sq]
  have hFs : Fs Cv B Ah Pt ϖ s T = s * bFun Ah x *
      (σt * frobIP Pt (Rs T s * Cv.Sout * Xs T s) + σ * frobIP Pt (Xs T s * Cv.Sin * Rts T s)) := rfl
  -- the identity
  set D1 := ∫ z, (e z * a3 z) * (z.1 ⬝ᵥ (K1m *ᵥ z.1)) ∂(gaussPair m n)
    - K1m.trace * ∫ z, e z * a3 z ∂(gaussPair m n) with hD1
  set D4 := ∫ z, (e z * a2 z) * (z.2 ⬝ᵥ (K4m *ᵥ z.2)) ∂(gaussPair m n)
    - K4m.trace * ∫ z, e z * a2 z ∂(gaussPair m n) with hD4
  set ρ := frobIP CE (Ah * NFun Ah x * Ahᵀ * Ah) with hρdef
  have key : ∫ z, f z ∂(gaussPair m n) + ϖ ^ 2 / B * (Fs Cv B Ah Pt ϖ s T * frobIP Ah CE) =
      (B : ℝ)⁻¹ * (D1 + s * ∫ z, (e z * a1 z) * (z.1 ⬝ᵥ (K2m *ᵥ z.2)) ∂(gaussPair m n)
        - ∫ z, (e z * a1 z) * (z.2 ⬝ᵥ (K3m *ᵥ z.1)) ∂(gaussPair m n) - s * D4
        + frobIP Pt (Rs T s * Cv.Sout * Xs T s) * ∫ z, e z * r3 z ∂(gaussPair m n)
        - s * (frobIP Pt (Xs T s * Cv.Sin * Rts T s) * ∫ z, e z * r2 z ∂(gaussPair m n))
        - ϖ ^ 2 * (s * σt * frobIP Pt (Rs T s * Cv.Sout * Xs T s)
            + s * σ * frobIP Pt (Xs T s * Cv.Sin * Rts T s)) * ρ) := by
    rw [hIf, hFs, hD1, hD4, hc3eq, hc2eq, hJ', htr1, htr4, div_eq_mul_inv]
    ring
  rw [key, ← hK1m, ← hK2m, ← hK3m, ← hK4m, abs_mul,
    abs_of_pos (inv_pos.mpr (by exact_mod_cast hB : (0 : ℝ) < B))]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg B))
  have b1 : |D1| ≤ fro K1m * (Real.sqrt 2 * (Ke * fro CE * (C4 * ϖ ^ 2))) :=
    P1.2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc3.2 (Real.sqrt_nonneg _))
      (pe8s_fro_nonneg _))
  have b2 : |s * ∫ z, (e z * a1 z) * (z.1 ⬝ᵥ (K2m *ᵥ z.2)) ∂(gaussPair m n)| ≤
      s * (fro K2m * (Ke * fro CE * (C4 * ϖ))) := by
    rw [abs_mul, abs_of_pos hs_pos]
    exact mul_le_mul_of_nonneg_left (P2.2.trans (mul_le_mul_of_nonneg_left hc1.2
      (pe8s_fro_nonneg _))) hs_pos.le
  have b3 : |∫ z, (e z * a1 z) * (z.2 ⬝ᵥ (K3m *ᵥ z.1)) ∂(gaussPair m n)| ≤
      fro K3m * (Ke * fro CE * (C4 * ϖ)) :=
    P3.2.trans (mul_le_mul_of_nonneg_left hc1.2 (pe8s_fro_nonneg _))
  have b4 : |s * D4| ≤ s * (fro K4m * (Real.sqrt 2 * (Ke * fro CE * (C4 * ϖ ^ 2 / s)))) := by
    rw [abs_mul, abs_of_pos hs_pos]
    exact mul_le_mul_of_nonneg_left (P4.2.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hc2.2 (Real.sqrt_nonneg _)) (pe8s_fro_nonneg _))) hs_pos.le
  have b5 : |frobIP Pt (Rs T s * Cv.Sout * Xs T s) * ∫ z, e z * r3 z ∂(gaussPair m n)| ≤
      |frobIP Pt (Rs T s * Cv.Sout * Xs T s)| * (Ke * fro CE * (C2 * ϖ ^ 2 / Real.sqrt B)) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left I3.2 (abs_nonneg _)
  have b6 : |s * (frobIP Pt (Xs T s * Cv.Sin * Rts T s) * ∫ z, e z * r2 z ∂(gaussPair m n))| ≤
      s * (|frobIP Pt (Xs T s * Cv.Sin * Rts T s)| *
        (Ke * fro CE * (C2 * ϖ ^ 2 / (s * Real.sqrt B)))) := by
    rw [abs_mul, abs_of_pos hs_pos, abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left I2.2 (abs_nonneg _)) hs_pos.le
  have b7 : |ϖ ^ 2 * (s * σt * frobIP Pt (Rs T s * Cv.Sout * Xs T s)
        + s * σ * frobIP Pt (Xs T s * Cv.Sin * Rts T s)) * ρ| ≤
      ϖ ^ 2 * (s * σt * |frobIP Pt (Rs T s * Cv.Sout * Xs T s)|
        + s * σ * |frobIP Pt (Xs T s * Cv.Sin * Rts T s)|) *
        (24 * x * opNorm CE * opNorm Ah) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ϖ ^ 2)]
    have hsum : |s * σt * frobIP Pt (Rs T s * Cv.Sout * Xs T s)
        + s * σ * frobIP Pt (Xs T s * Cv.Sin * Rts T s)| ≤
        s * σt * |frobIP Pt (Rs T s * Cv.Sout * Xs T s)|
          + s * σ * |frobIP Pt (Xs T s * Cv.Sin * Rts T s)| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul (s * σt), abs_mul (s * σ), abs_of_nonneg (by positivity : (0 : ℝ) ≤ s * σt),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ s * σ)]
    have hρ' : |ρ| ≤ 24 * x * opNorm CE * opNorm Ah := hρ
    have h1 : 0 ≤ ϖ ^ 2 := by positivity
    calc ϖ ^ 2 * |s * σt * frobIP Pt (Rs T s * Cv.Sout * Xs T s)
          + s * σ * frobIP Pt (Xs T s * Cv.Sin * Rts T s)| * |ρ|
        ≤ ϖ ^ 2 * (s * σt * |frobIP Pt (Rs T s * Cv.Sout * Xs T s)|
          + s * σ * |frobIP Pt (Xs T s * Cv.Sin * Rts T s)|) * |ρ| := by gcongr
      _ ≤ _ := by gcongr
  have l1 := le_abs_self D1
  have l1' := neg_abs_le D1
  have l2 := le_abs_self (s * ∫ z, (e z * a1 z) * (z.1 ⬝ᵥ (K2m *ᵥ z.2)) ∂(gaussPair m n))
  have l2' := neg_abs_le (s * ∫ z, (e z * a1 z) * (z.1 ⬝ᵥ (K2m *ᵥ z.2)) ∂(gaussPair m n))
  have l3 := le_abs_self (∫ z, (e z * a1 z) * (z.2 ⬝ᵥ (K3m *ᵥ z.1)) ∂(gaussPair m n))
  have l3' := neg_abs_le (∫ z, (e z * a1 z) * (z.2 ⬝ᵥ (K3m *ᵥ z.1)) ∂(gaussPair m n))
  have l4 := le_abs_self (s * D4)
  have l4' := neg_abs_le (s * D4)
  have l5 := le_abs_self (frobIP Pt (Rs T s * Cv.Sout * Xs T s) * ∫ z, e z * r3 z ∂(gaussPair m n))
  have l5' := neg_abs_le (frobIP Pt (Rs T s * Cv.Sout * Xs T s) * ∫ z, e z * r3 z ∂(gaussPair m n))
  have l6 := le_abs_self
    (s * (frobIP Pt (Xs T s * Cv.Sin * Rts T s) * ∫ z, e z * r2 z ∂(gaussPair m n)))
  have l6' := neg_abs_le
    (s * (frobIP Pt (Xs T s * Cv.Sin * Rts T s) * ∫ z, e z * r2 z ∂(gaussPair m n)))
  have l7 := le_abs_self (ϖ ^ 2 * (s * σt * frobIP Pt (Rs T s * Cv.Sout * Xs T s)
        + s * σ * frobIP Pt (Xs T s * Cv.Sin * Rts T s)) * ρ)
  have l7' := neg_abs_le (ϖ ^ 2 * (s * σt * frobIP Pt (Rs T s * Cv.Sout * Xs T s)
        + s * σ * frobIP Pt (Xs T s * Cv.Sin * Rts T s)) * ρ)
  rw [abs_le]
  constructor <;> linarith

private lemma pe8s_numeric (s0 CS cP cE γ C4 C2 K1 Ke : ℝ) (hs0 : 0 < s0) (hCS : 0 ≤ CS)
    (hcP : 0 ≤ cP) (hcE : 0 ≤ cE) (_hγ : 0 ≤ γ) (hC4 : 0 ≤ C4) (hC2 : 0 ≤ C2) (hK1 : 0 ≤ K1)
    (hKe : 0 ≤ Ke) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s ϖ b F f1 f2 f3 f4 t1 t4 st ss x oE oA : ℝ),
      s0 ≤ s → 0 ≤ ϖ → ϖ ≤ 1 → 0 < b →
      0 ≤ F → F ≤ cE * b →
      0 ≤ f1 → f1 ≤ CS * cP / (2 * s * Real.sqrt s) →
      0 ≤ f2 → f2 ≤ CS * cP / (s * s) →
      0 ≤ f3 → f3 ≤ CS * cP / (4 * s) →
      0 ≤ f4 → f4 ≤ CS * cP / (2 * s * Real.sqrt s) →
      0 ≤ t1 → t1 ≤ cP * Real.sqrt γ * b * CS / (2 * s * Real.sqrt s) →
      0 ≤ t4 → t4 ≤ cP * Real.sqrt γ * b * CS / (2 * s * Real.sqrt s) →
      0 ≤ st → st ≤ K1 → 0 ≤ ss → ss ≤ K1 → 0 ≤ x → x ≤ K1 ^ 2 / s →
      0 ≤ oE → oE ≤ cE → 0 ≤ oA → oA ≤ 1 →
      (b ^ 2)⁻¹ * (f1 * (Real.sqrt 2 * (Ke * F * (C4 * ϖ ^ 2)))
          + s * (f2 * (Ke * F * (C4 * ϖ)))
          + f3 * (Ke * F * (C4 * ϖ))
          + s * (f4 * (Real.sqrt 2 * (Ke * F * (C4 * ϖ ^ 2 / s))))
          + t1 * (Ke * F * (C2 * ϖ ^ 2 / b))
          + s * (t4 * (Ke * F * (C2 * ϖ ^ 2 / (s * b))))
          + ϖ ^ 2 * (st * t1 + ss * t4) * (24 * x * oE * oA)) ≤ K * ϖ / (s * b) := by
  set i0 := 1 / Real.sqrt s0 with hi0
  have hi00 : 0 ≤ i0 := by positivity
  set k1 := CS * cP * Real.sqrt 2 * Ke * cE * C4 / 2 * i0
  set k2 := CS * cP * Ke * cE * C4
  set k3 := CS * cP * Ke * cE * C4 / 4
  set k5 := cP * Real.sqrt γ * CS * Ke * cE * C2 / 2 * i0
  set k7 := 24 * K1 ^ 3 * cP * Real.sqrt γ * CS * cE * (1 / s0) * i0
  refine ⟨2 * k1 + k2 + k3 + 2 * k5 + k7, by positivity, ?_⟩
  intro s ϖ b F f1 f2 f3 f4 t1 t4 st ss x oE oA hs hϖ0 hϖ1 hb hF0 hF hf10 hf1 hf20 hf2 hf30 hf3
    hf40 hf4 ht10 ht1 ht40 ht4 hst0 hst hss0 hss hx0 hx hoE0 hoE hoA0 hoA
  have hs_pos : 0 < s := lt_of_lt_of_le hs0 hs
  have hq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs_pos
  have hqq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs_pos.le
  have hiq : 1 / Real.sqrt s ≤ i0 := by
    rw [hi0]; exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hs0) (Real.sqrt_le_sqrt hs)
  have his : 1 / s ≤ 1 / s0 := one_div_le_one_div_of_le hs0 hs
  have hϖ2 : ϖ ^ 2 ≤ ϖ := by nlinarith
  set W := ϖ * b / s with hW
  have hW0 : 0 ≤ W := by positivity
  have e1 : f1 * (Real.sqrt 2 * (Ke * F * (C4 * ϖ ^ 2))) ≤ k1 * W := by
    calc f1 * (Real.sqrt 2 * (Ke * F * (C4 * ϖ ^ 2)))
        ≤ CS * cP / (2 * s * Real.sqrt s) * (Real.sqrt 2 * (Ke * (cE * b) * (C4 * ϖ))) := by
          gcongr
      _ = CS * cP * Real.sqrt 2 * Ke * cE * C4 / 2 * (1 / Real.sqrt s) * W := by
          rw [hW]; ring
      _ ≤ k1 * W := by
          have : 0 ≤ CS * cP * Real.sqrt 2 * Ke * cE * C4 / 2 := by positivity
          calc CS * cP * Real.sqrt 2 * Ke * cE * C4 / 2 * (1 / Real.sqrt s) * W
              ≤ CS * cP * Real.sqrt 2 * Ke * cE * C4 / 2 * i0 * W := by gcongr
            _ = k1 * W := rfl
  have e4 : s * (f4 * (Real.sqrt 2 * (Ke * F * (C4 * ϖ ^ 2 / s)))) ≤ k1 * W := by
    have : s * (f4 * (Real.sqrt 2 * (Ke * F * (C4 * ϖ ^ 2 / s)))) =
        (s / s) * (f4 * (Real.sqrt 2 * (Ke * F * (C4 * ϖ ^ 2)))) := by ring
    rw [this, div_self hs_pos.ne', one_mul]
    calc f4 * (Real.sqrt 2 * (Ke * F * (C4 * ϖ ^ 2)))
        ≤ CS * cP / (2 * s * Real.sqrt s) * (Real.sqrt 2 * (Ke * (cE * b) * (C4 * ϖ))) := by
          gcongr
      _ = CS * cP * Real.sqrt 2 * Ke * cE * C4 / 2 * (1 / Real.sqrt s) * W := by
          rw [hW]; ring
      _ ≤ k1 * W := by
          have : 0 ≤ CS * cP * Real.sqrt 2 * Ke * cE * C4 / 2 := by positivity
          calc CS * cP * Real.sqrt 2 * Ke * cE * C4 / 2 * (1 / Real.sqrt s) * W
              ≤ CS * cP * Real.sqrt 2 * Ke * cE * C4 / 2 * i0 * W := by gcongr
            _ = k1 * W := rfl
  have e2 : s * (f2 * (Ke * F * (C4 * ϖ))) ≤ k2 * W := by
    calc s * (f2 * (Ke * F * (C4 * ϖ))) ≤ s * (CS * cP / (s * s) * (Ke * (cE * b) * (C4 * ϖ))) := by
          gcongr
      _ = k2 * W := by rw [hW]; field_simp; simp only [k2]; ring
  have e3 : f3 * (Ke * F * (C4 * ϖ)) ≤ k3 * W := by
    calc f3 * (Ke * F * (C4 * ϖ)) ≤ CS * cP / (4 * s) * (Ke * (cE * b) * (C4 * ϖ)) := by gcongr
      _ = k3 * W := by rw [hW]; field_simp; simp only [k3]; ring
  have hFb : F / b ≤ cE := by rw [div_le_iff₀ hb]; linarith
  have hFb0 : 0 ≤ F / b := by positivity
  have e5 : t1 * (Ke * F * (C2 * ϖ ^ 2 / b)) ≤ k5 * W := by
    calc t1 * (Ke * F * (C2 * ϖ ^ 2 / b)) = t1 * (Ke * (F / b) * (C2 * ϖ ^ 2)) := by ring
      _ ≤ cP * Real.sqrt γ * b * CS / (2 * s * Real.sqrt s) * (Ke * cE * (C2 * ϖ)) := by
          gcongr
      _ = cP * Real.sqrt γ * CS * Ke * cE * C2 / 2 * (1 / Real.sqrt s) * W := by
          rw [hW]; ring
      _ ≤ k5 * W := by
          have : 0 ≤ cP * Real.sqrt γ * CS * Ke * cE * C2 / 2 := by positivity
          calc cP * Real.sqrt γ * CS * Ke * cE * C2 / 2 * (1 / Real.sqrt s) * W
              ≤ cP * Real.sqrt γ * CS * Ke * cE * C2 / 2 * i0 * W := by gcongr
            _ = k5 * W := rfl
  have e6 : s * (t4 * (Ke * F * (C2 * ϖ ^ 2 / (s * b)))) ≤ k5 * W := by
    have : s * (t4 * (Ke * F * (C2 * ϖ ^ 2 / (s * b)))) =
        (s / s) * (t4 * (Ke * F * (C2 * ϖ ^ 2 / b))) := by ring
    rw [this, div_self hs_pos.ne', one_mul]
    calc t4 * (Ke * F * (C2 * ϖ ^ 2 / b)) = t4 * (Ke * (F / b) * (C2 * ϖ ^ 2)) := by ring
      _ ≤ cP * Real.sqrt γ * b * CS / (2 * s * Real.sqrt s) * (Ke * cE * (C2 * ϖ)) := by
          gcongr
      _ = cP * Real.sqrt γ * CS * Ke * cE * C2 / 2 * (1 / Real.sqrt s) * W := by
          rw [hW]; ring
      _ ≤ k5 * W := by
          have : 0 ≤ cP * Real.sqrt γ * CS * Ke * cE * C2 / 2 := by positivity
          calc cP * Real.sqrt γ * CS * Ke * cE * C2 / 2 * (1 / Real.sqrt s) * W
              ≤ cP * Real.sqrt γ * CS * Ke * cE * C2 / 2 * i0 * W := by gcongr
            _ = k5 * W := rfl
  have e7 : ϖ ^ 2 * (st * t1 + ss * t4) * (24 * x * oE * oA) ≤ k7 * W := by
    have hT : 0 ≤ cP * Real.sqrt γ * b * CS / (2 * s * Real.sqrt s) := by positivity
    calc ϖ ^ 2 * (st * t1 + ss * t4) * (24 * x * oE * oA)
        ≤ ϖ * (K1 * (cP * Real.sqrt γ * b * CS / (2 * s * Real.sqrt s))
            + K1 * (cP * Real.sqrt γ * b * CS / (2 * s * Real.sqrt s))) *
            (24 * (K1 ^ 2 / s) * cE * 1) := by gcongr
      _ = 24 * K1 ^ 3 * cP * Real.sqrt γ * CS * cE * (1 / s) * (1 / Real.sqrt s) * W := by
          rw [hW]; ring
      _ ≤ k7 * W := by
          have : 0 ≤ 24 * K1 ^ 3 * cP * Real.sqrt γ * CS * cE := by positivity
          calc 24 * K1 ^ 3 * cP * Real.sqrt γ * CS * cE * (1 / s) * (1 / Real.sqrt s) * W
              ≤ 24 * K1 ^ 3 * cP * Real.sqrt γ * CS * cE * (1 / s0) * i0 * W := by gcongr
            _ = k7 * W := rfl
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add e1 e2) e3)
    e4) e5) e6) e7
  have hb2 : 0 < (b ^ 2)⁻¹ := by positivity
  calc (b ^ 2)⁻¹ * _ ≤ (b ^ 2)⁻¹ * (k1 * W + k2 * W + k3 * W + k1 * W + k5 * W + k5 * W + k7 * W) :=
        mul_le_mul_of_nonneg_left hsum hb2.le
    _ = (b ^ 2)⁻¹ * ((2 * k1 + k2 + k3 + 2 * k5 + k7) * (ϖ * b / s)) := by rw [hW]; ring
    _ = (2 * k1 + k2 + k3 + 2 * k5 + k7) * ϖ / (s * b) := by
        rw [pow_two, mul_inv]
        rw [show b⁻¹ * b⁻¹ * ((2 * k1 + k2 + k3 + 2 * k5 + k7) * (ϖ * b / s)) =
          (b * b⁻¹) * ((2 * k1 + k2 + k3 + 2 * k5 + k7) * ϖ / (s * b)) by ring,
          mul_inv_cancel₀ hb.ne', one_mul]

private lemma pe8s_rr_op {m n : ℕ} (Cv : Covariances m n) (CS : ℝ) (hCo : opNorm Cv.Sout ≤ CS)
    (hCi : opNorm Cv.Sin ≤ CS) :
    opNorm (rOut Cv) * opNorm (rOut Cv) ≤ CS ∧ opNorm (rOut Cv) * opNorm (rIn Cv) ≤ CS ∧
    opNorm (rIn Cv) * opNorm (rOut Cv) ≤ CS ∧ opNorm (rIn Cv) * opNorm (rIn Cv) ≤ CS := by
  have h1 := pe8s_rOut_op Cv CS hCo
  have h2 := pe8s_rIn_op Cv CS hCi
  have a0 := pe8_opNorm_nonneg (rOut Cv)
  have b0 := pe8_opNorm_nonneg (rIn Cv)
  refine ⟨h1, ?_, ?_, h2⟩ <;> nlinarith [sq_nonneg (opNorm (rOut Cv) - opNorm (rIn Cv))]

private lemma pe8s_kbound {a b p q : ℕ} (rA : Mat p p) (rB : Mat q q) (L : Mat a p)
    (Pt : Mat a b) (Rr : Mat q b) (CS l r cP : ℝ) (hr : opNorm rA * opNorm rB ≤ CS)
    (hl : opNorm L ≤ l) (hrr : opNorm Rr ≤ r) (hP : fro Pt ≤ cP) :
    fro (rAᵀ * (Lᵀ * Pt * Rrᵀ) * rB) ≤ CS * (l * r * cP) := by
  refine (pe8s_fro_K rA rB L Pt Rr).trans ?_
  have h0 := pe8_opNorm_nonneg L
  have h1 := pe8_opNorm_nonneg Rr
  have h2 := pe8s_fro_nonneg Pt
  have h3 : 0 ≤ opNorm rA * opNorm rB := mul_nonneg (pe8_opNorm_nonneg _) (pe8_opNorm_nonneg _)
  have h4 : 0 ≤ l := h0.trans hl
  have h5 : 0 ≤ r := h1.trans hrr
  have h6 : 0 ≤ CS := h3.trans hr
  have h7 : 0 ≤ cP := h2.trans hP
  calc opNorm rA * opNorm rB * (opNorm L * opNorm Rr * fro Pt) ≤ CS * (l * r * cP) := by gcongr

private lemma pe8s_tbound {a b p q : ℕ} (Pt : Mat a b) (L : Mat a p) (S : Mat p q) (Rr : Mat q b)
    (cP nb l CS r : ℝ) (hP : fro Pt ≤ cP) (hb : Real.sqrt b ≤ nb) (hl : opNorm L ≤ l)
    (hS : opNorm S ≤ CS) (hr : opNorm Rr ≤ r) :
    |frobIP Pt (L * S * Rr)| ≤ cP * (nb * (l * CS * r)) := by
  refine (pe8s_frobIP_tr_bound Pt L S Rr).trans ?_
  have h0 := pe8_opNorm_nonneg L
  have h1 := pe8_opNorm_nonneg S
  have h2 := pe8_opNorm_nonneg Rr
  have h3 := pe8s_fro_nonneg Pt
  have h4 : 0 ≤ l := h0.trans hl
  have h5 : 0 ≤ CS := h1.trans hS
  have h6 : 0 ≤ r := h2.trans hr
  have h7 : 0 ≤ nb := (Real.sqrt_nonneg _).trans hb
  have h8 : 0 ≤ cP := h3.trans hP
  gcongr

private lemma pe8s_core (certQ : Muon.External.GaussianQuadFormLp) (γ CS s0 cP cE : ℝ)
    (hs0 : 0 < s0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {m n B : ℕ} (Cv : Covariances m n) (T Ah CE Pt : Mat m n) (piT ϖ s : ℝ)
      (f : Vec m × Vec n → ℝ), 0 < B →
      opNorm Cv.Sout ≤ CS → opNorm Cv.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      fro Ah = 1 → s0 ≤ s → ϖ ∈ Icc (0 : ℝ) 1 → IsTest cP piT Pt →
      fro CE ≤ cE * Real.sqrt B → opNorm CE ≤ cE →
      (∀ z, f z = resid CE z *
        (dAlpha3 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) *
            frobIP Pt (Rs T s * outer (sampU Cv B z) (sampU Cv B z) * Xs T s)
          + s * dAlpha1 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) *
            frobIP Pt (Rs T s * outer (sampU Cv B z) (sampV Cv B z) * Rts T s)
          - dAlpha1 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) *
            frobIP Pt (Xs T s * outer (sampV Cv B z) (sampU Cv B z) * Xs T s)
          - s * dAlpha2 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) *
            frobIP Pt (Xs T s * outer (sampV Cv B z) (sampV Cv B z) * Rts T s))) →
      Integrable f (gaussPair m n) ∧
      |∫ z, f z ∂(gaussPair m n) + ϖ ^ 2 / B * (Fs Cv B Ah Pt ϖ s T * frobIP Ah CE)| ≤
        K * ϖ / (s * Real.sqrt B) := by
  obtain ⟨C4, C2, _, Ke, hC4, hC2, _, hKe, hraw⟩ := pe8s_core_raw certQ γ CS s0 hs0
  obtain ⟨K1, hK1, hσb⟩ := pe8_sigma_bound certQ γ CS
  obtain ⟨K, hK, hnum⟩ := pe8s_numeric s0 (max CS 0) (max cP 0) (max cE 0) (max γ 0) C4 C2 K1 Ke
    hs0 (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) hC4 hC2 hK1 hKe
  refine ⟨K, hK, ?_⟩
  intro m n B Cv T Ah CE Pt piT ϖ s f hB hCo hCi hm hn hA hs hϖ hP hfE hoE hf
  obtain ⟨hint, hb⟩ := hraw Cv T Ah CE Pt ϖ s f hB hCo hCi hm hn hA hs hϖ hf
  refine ⟨hint, hb.trans ?_⟩
  have hs_pos : 0 < s := lt_of_lt_of_le hs0 hs
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hsqB : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.2 hBr
  have hBb : (B : ℝ)⁻¹ = (Real.sqrt B ^ 2)⁻¹ := by rw [Real.sq_sqrt hBr.le]
  rw [hBb]
  obtain ⟨hR, hRt, hX, _⟩ := lem_app_de_resolvent T s hs_pos
  have hRT : opNorm (Rs T s)ᵀ ≤ 1 / s := by rw [pe8m_op_transpose_copy]; exact hR
  have hRtT : opNorm (Rts T s)ᵀ ≤ 1 / s := by rw [pe8m_op_transpose_copy]; exact hRt
  have hXT : opNorm (Xs T s)ᵀ ≤ 1 / (2 * Real.sqrt s) := by rw [pe8m_op_transpose_copy]; exact hX
  have hCS' : CS ≤ max CS 0 := le_max_left _ _
  have hCo' := hCo.trans hCS'
  have hCi' := hCi.trans hCS'
  obtain ⟨r11, r12, r21, r22⟩ := pe8s_rr_op Cv (max CS 0) hCo' hCi'
  have hPf : fro Pt ≤ max cP 0 := hP.1.trans (le_max_left _ _)
  have hq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs_pos
  have hqq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs_pos.le
  have hsn : Real.sqrt n ≤ Real.sqrt (max γ 0) * Real.sqrt B := by
    rw [← Real.sqrt_mul (le_max_right _ _)]
    exact Real.sqrt_le_sqrt (hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hBr.le))
  obtain ⟨hσ1, hσt1⟩ := hσb Cv B hB T s hs_pos hCo hCi hm hn
  have hσ0 := pe8_sigmaS_nonneg Cv B hB T s hs_pos
  have hσt0 := pe8_sigmaT_nonneg Cv B hB T s hs_pos
  obtain ⟨hϖ0, hϖ1⟩ := hϖ
  refine hnum s ϖ (Real.sqrt B) (fro CE) _ _ _ _ _ _ (s * sigmaT Cv B T s) (s * sigmaS Cv B T s)
    (xMinor Cv B T ϖ s) (opNorm CE) (opNorm Ah) hs hϖ0 hϖ1 hsqB (pe8s_fro_nonneg _)
    (hfE.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsqB.le))
    (pe8s_fro_nonneg _) ?_ (pe8s_fro_nonneg _) ?_ (pe8s_fro_nonneg _) ?_ (pe8s_fro_nonneg _) ?_
    (abs_nonneg _) ?_ (abs_nonneg _) ?_ (by positivity) hσt1 (by positivity) hσ1
    (by unfold xMinor; positivity) ?_ (pe8_opNorm_nonneg _) (hoE.trans (le_max_left _ _))
    (pe8_opNorm_nonneg _) ((pe8s_op_le_fro Ah).trans hA.le)
  · refine (pe8s_kbound _ _ _ _ _ _ _ _ _ r11 hR hX hPf).trans (le_of_eq ?_)
    ring
  · refine (pe8s_kbound _ _ _ _ _ _ _ _ _ r12 hR hRt hPf).trans (le_of_eq ?_)
    ring
  · refine (pe8s_kbound _ _ _ _ _ _ _ _ _ r21 hX hX hPf).trans (le_of_eq ?_)
    calc max CS 0 * (1 / (2 * Real.sqrt s) * (1 / (2 * Real.sqrt s)) * max cP 0)
        = max CS 0 * max cP 0 / (4 * (Real.sqrt s * Real.sqrt s)) := by ring
      _ = _ := by rw [hqq]
  · refine (pe8s_kbound _ _ _ _ _ _ _ _ _ r22 hX hRt hPf).trans (le_of_eq ?_)
    ring
  · refine (pe8s_tbound _ _ _ _ _ _ _ _ _ hPf hsn hR hCo' hX).trans (le_of_eq ?_)
    ring
  · refine (pe8s_tbound _ _ _ _ _ _ _ _ _ hPf hsn hX hCi' hRt).trans (le_of_eq ?_)
    ring
  · rw [le_div_iff₀ hs_pos]
    unfold xMinor
    have : ϖ ^ 2 * s * sigmaS Cv B T s * sigmaT Cv B T s * s =
        ϖ ^ 2 * ((s * sigmaS Cv B T s) * (s * sigmaT Cv B T s)) := by ring
    rw [this]
    have hϖ2 : ϖ ^ 2 ≤ 1 := by nlinarith
    calc ϖ ^ 2 * ((s * sigmaS Cv B T s) * (s * sigmaT Cv B T s)) ≤ 1 * (K1 * K1) := by
          gcongr
      _ = K1 ^ 2 := by ring

private lemma pe8s_det_ne {a b : ℕ} (K : Mat a b) (s : ℝ) (hs : 0 < s) :
    (K * Kᵀ + s • (1 : Mat a a)).det ≠ 0 := by
  have h1 : (K * Kᵀ).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose K
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have h2 : (s • (1 : Mat a a)).PosDef := Matrix.PosDef.one.smul hs
  have h3 := Matrix.PosDef.add_posSemidef h2 h1
  rw [add_comm]
  exact h3.det_pos.ne'

private lemma pe8s_cont_Rs {m n : ℕ} (s : ℝ) (hs : 0 < s) :
    Continuous (fun T : Mat m n => Rs T s) := by
  unfold Rs
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  have hc : Continuous (fun T : Mat m n => T * Tᵀ + s • (1 : Mat m m)) :=
    (continuous_id.matrix_mul continuous_id.matrix_transpose).add continuous_const
  exact ((hc.matrix_det).inv₀ fun T => pe8s_det_ne T s hs).smul hc.matrix_adjugate

private lemma pe8s_cont_Rts {m n : ℕ} (s : ℝ) (hs : 0 < s) :
    Continuous (fun T : Mat m n => Rts T s) := by
  simp_rw [pe8_Rts_eq]
  exact (pe8s_cont_Rs (m := n) (n := m) s hs).comp continuous_id.matrix_transpose

private lemma pe8s_cont_Xs {m n : ℕ} (s : ℝ) (hs : 0 < s) :
    Continuous (fun T : Mat m n => Xs T s) := by
  unfold Xs
  exact (pe8s_cont_Rs s hs).matrix_mul continuous_id

private lemma pe8s_meas_dAlpha {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (Ah : Mat m n)
    (ϖ s : ℝ) (hs : 0 < s) (hϖ : ϖ ∈ Icc (0 : ℝ) 1) :
    Measurable (fun q : (Mat m n × Mat m n) × (Vec m × Vec n) =>
      dAlpha1 q.1.1 ϖ s (sampU Cv B q.2) (sampV Cv B q.2) (resid Ah q.2)) ∧
    Measurable (fun q : (Mat m n × Mat m n) × (Vec m × Vec n) =>
      dAlpha2 q.1.1 ϖ s (sampU Cv B q.2) (sampV Cv B q.2) (resid Ah q.2)) ∧
    Measurable (fun q : (Mat m n × Mat m n) × (Vec m × Vec n) =>
      dAlpha3 q.1.1 ϖ s (sampU Cv B q.2) (sampV Cv B q.2) (resid Ah q.2)) := by
  have h1 := pe8s_cont_Rs (m := m) (n := n) s hs
  have h2 := pe8s_cont_Xs (m := m) (n := n) s hs
  have h3 := pe8s_cont_Rts (m := m) (n := n) s hs
  have hL : Continuous (fun q : (Mat m n × Mat m n) × (Vec m × Vec n) =>
      (delLambda q.1.1 (ϖ * resid Ah q.2) (sampU Cv B q.2) (sampV Cv B q.2) s) ^ 2) := by
    unfold delLambda delC delU delV sampU sampV resid
    fun_prop
  refine ⟨?_, ?_, ?_⟩
  · have e : (fun q : (Mat m n × Mat m n) × (Vec m × Vec n) =>
        dAlpha1 q.1.1 ϖ s (sampU Cv B q.2) (sampV Cv B q.2) (resid Ah q.2)) = fun q =>
        ϖ * ((1 + (ϖ * resid Ah q.2) * delC q.1.1 (sampU Cv B q.2) (sampV Cv B q.2) s) ^ 2 -
          s * (ϖ * resid Ah q.2) ^ 2 * delU q.1.1 (sampU Cv B q.2) s *
            delV q.1.1 (sampV Cv B q.2) s) /
          (delLambda q.1.1 (ϖ * resid Ah q.2) (sampU Cv B q.2) (sampV Cv B q.2) s) ^ 2 :=
      funext fun q => (pe8_dAlpha_formula _ ϖ s _ _ _ hs hϖ).1
    rw [e]
    refine Measurable.div (Continuous.measurable ?_) hL.measurable
    simp only [delC, delU, delV, sampU, sampV, resid]
    fun_prop
  · have e : (fun q : (Mat m n × Mat m n) × (Vec m × Vec n) =>
        dAlpha2 q.1.1 ϖ s (sampU Cv B q.2) (sampV Cv B q.2) (resid Ah q.2)) = fun q =>
        2 * ϖ * (ϖ * resid Ah q.2) * delU q.1.1 (sampU Cv B q.2) s *
          (1 + (ϖ * resid Ah q.2) * delC q.1.1 (sampU Cv B q.2) (sampV Cv B q.2) s) /
          (delLambda q.1.1 (ϖ * resid Ah q.2) (sampU Cv B q.2) (sampV Cv B q.2) s) ^ 2 :=
      funext fun q => (pe8_dAlpha_formula _ ϖ s _ _ _ hs hϖ).2.1
    rw [e]
    refine Measurable.div (Continuous.measurable ?_) hL.measurable
    simp only [delC, delU, sampU, sampV, resid]
    fun_prop
  · have e : (fun q : (Mat m n × Mat m n) × (Vec m × Vec n) =>
        dAlpha3 q.1.1 ϖ s (sampU Cv B q.2) (sampV Cv B q.2) (resid Ah q.2)) = fun q =>
        (-(2 * s * ϖ * (ϖ * resid Ah q.2) * delV q.1.1 (sampV Cv B q.2) s *
          (1 + (ϖ * resid Ah q.2) * delC q.1.1 (sampU Cv B q.2) (sampV Cv B q.2) s))) /
          (delLambda q.1.1 (ϖ * resid Ah q.2) (sampU Cv B q.2) (sampV Cv B q.2) s) ^ 2 :=
      funext fun q => (pe8_dAlpha_formula _ ϖ s _ _ _ hs hϖ).2.2
    rw [e]
    refine Measurable.div (Continuous.measurable ?_) hL.measurable
    simp only [delC, delV, sampU, sampV, resid]
    fun_prop

private lemma pe8s_meas_phi {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (Ah Pt : Mat m n)
    (ϖ s : ℝ) (hs : 0 < s) (hϖ : ϖ ∈ Icc (0 : ℝ) 1) :
    Measurable (fun q : (Mat m n × Mat m n) × (Vec m × Vec n) =>
      resid (Arot Cv q.1.2) q.2 *
        (dAlpha3 q.1.1 ϖ s (sampU Cv B q.2) (sampV Cv B q.2) (resid Ah q.2) *
            frobIP Pt (Rs q.1.1 s * outer (sampU Cv B q.2) (sampU Cv B q.2) * Xs q.1.1 s)
          + s * dAlpha1 q.1.1 ϖ s (sampU Cv B q.2) (sampV Cv B q.2) (resid Ah q.2) *
            frobIP Pt (Rs q.1.1 s * outer (sampU Cv B q.2) (sampV Cv B q.2) * Rts q.1.1 s)
          - dAlpha1 q.1.1 ϖ s (sampU Cv B q.2) (sampV Cv B q.2) (resid Ah q.2) *
            frobIP Pt (Xs q.1.1 s * outer (sampV Cv B q.2) (sampU Cv B q.2) * Xs q.1.1 s)
          - s * dAlpha2 q.1.1 ϖ s (sampU Cv B q.2) (sampV Cv B q.2) (resid Ah q.2) *
            frobIP Pt (Xs q.1.1 s * outer (sampV Cv B q.2) (sampV Cv B q.2) * Rts q.1.1 s))) := by
  obtain ⟨d1, d2, d3⟩ := pe8s_meas_dAlpha Cv B Ah ϖ s hs hϖ
  have h1 := pe8s_cont_Rs (m := m) (n := n) s hs
  have h2 := pe8s_cont_Xs (m := m) (n := n) s hs
  have h3 := pe8s_cont_Rts (m := m) (n := n) s hs
  have c0 : Continuous (fun q : (Mat m n × Mat m n) × (Vec m × Vec n) =>
      resid (Arot Cv q.1.2) q.2) := by unfold resid Arot; fun_prop
  have c1 : Continuous (fun q : (Mat m n × Mat m n) × (Vec m × Vec n) =>
      frobIP Pt (Rs q.1.1 s * outer (sampU Cv B q.2) (sampU Cv B q.2) * Xs q.1.1 s)) := by
    unfold frobIP outer sampU; fun_prop
  have c2 : Continuous (fun q : (Mat m n × Mat m n) × (Vec m × Vec n) =>
      frobIP Pt (Rs q.1.1 s * outer (sampU Cv B q.2) (sampV Cv B q.2) * Rts q.1.1 s)) := by
    unfold frobIP outer sampU sampV; fun_prop
  have c3 : Continuous (fun q : (Mat m n × Mat m n) × (Vec m × Vec n) =>
      frobIP Pt (Xs q.1.1 s * outer (sampV Cv B q.2) (sampU Cv B q.2) * Xs q.1.1 s)) := by
    unfold frobIP outer sampU sampV; fun_prop
  have c4 : Continuous (fun q : (Mat m n × Mat m n) × (Vec m × Vec n) =>
      frobIP Pt (Xs q.1.1 s * outer (sampV Cv B q.2) (sampV Cv B q.2) * Rts q.1.1 s)) := by
    unfold frobIP outer sampV; fun_prop
  exact c0.measurable.mul ((((d3.mul c1.measurable).add
    ((measurable_const.mul d1).mul c2.measurable)).sub (d1.mul c3.measurable)).sub
    ((measurable_const.mul d2).mul c4.measurable))

private lemma pe8s_outer_le {a b : ℕ} (x : Vec a) (y : Vec b) (N : ℝ) (hx : ∑ i, x i ^ 2 ≤ N)
    (hy : ∑ j, y j ^ 2 ≤ N) : fro (outer x y) ≤ N := by
  rw [pe8s_fro_outer]
  have h1 := Real.sq_sqrt (show 0 ≤ ∑ i, x i ^ 2 by positivity)
  have h2 := Real.sq_sqrt (show 0 ≤ ∑ j, y j ^ 2 by positivity)
  nlinarith [sq_nonneg (Real.sqrt (∑ i, x i ^ 2) - Real.sqrt (∑ j, y j ^ 2)),
    Real.sqrt_nonneg (∑ i, x i ^ 2), Real.sqrt_nonneg (∑ j, y j ^ 2)]

private lemma pe8s_q_le {m n p q : ℕ} (Pt : Mat m n) (L : Mat m p) (x : Vec p) (y : Vec q)
    (Rr : Mat q n) (l r N : ℝ) (hl : opNorm L ≤ l) (hr : opNorm Rr ≤ r) (hx : ∑ i, x i ^ 2 ≤ N)
    (hy : ∑ j, y j ^ 2 ≤ N) :
    |frobIP Pt (L * outer x y * Rr)| ≤ fro Pt * (l * r * N) := by
  refine (pe8m_frobIP_le_copy _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (pe8s_fro_nonneg _)
  refine (pe8s_fro_sandwich _ _ _).trans ?_
  have h0 := pe8_opNorm_nonneg L
  have h1 := pe8_opNorm_nonneg Rr
  have h2 := pe8s_outer_le x y N hx hy
  have h3 := pe8s_fro_nonneg (outer x y)
  have hl0 : 0 ≤ l := h0.trans hl
  have hN0 : 0 ≤ N := h3.trans h2
  calc opNorm L * fro (outer x y) * opNorm Rr ≤ l * N * r :=
        mul_le_mul (mul_le_mul hl h2 h3 hl0) hr h1 (mul_nonneg hl0 hN0)
    _ = l * r * N := by ring

private lemma pe8s_phi_bound (certQ : Muon.External.GaussianQuadFormLp) (γ CS s0 : ℝ)
    (hs0 : 0 < s0) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ {m n B : ℕ} (Cv : Covariances m n) (T Ae Ah Pt : Mat m n) (ϖ s : ℝ)
      (z : Vec m × Vec n), 0 < B →
      opNorm Cv.Sout ≤ CS → opNorm Cv.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      s0 ≤ s → ϖ ∈ Icc (0 : ℝ) 1 →
      |resid Ae z *
        (dAlpha3 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) *
            frobIP Pt (Rs T s * outer (sampU Cv B z) (sampU Cv B z) * Xs T s)
          + s * dAlpha1 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) *
            frobIP Pt (Rs T s * outer (sampU Cv B z) (sampV Cv B z) * Rts T s)
          - dAlpha1 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) *
            frobIP Pt (Xs T s * outer (sampV Cv B z) (sampU Cv B z) * Xs T s)
          - s * dAlpha2 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z) *
            frobIP Pt (Xs T s * outer (sampV Cv B z) (sampV Cv B z) * Rts T s))| ≤
        κ * (3 + s) * fro Pt * (1 / s + 1 / (2 * Real.sqrt s)) ^ 2 *
          (((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ 8 *
            (|resid Ae z| * (1 + momN Cv B z))) := by
  obtain ⟨K1, hK1, hσb⟩ := pe8_sigma_bound certQ γ CS
  obtain ⟨κ, hκ0, hκ⟩ := pe8_point s0 K1 hs0 hK1
  refine ⟨κ, hκ0, ?_⟩
  intro m n B Cv T Ae Ah Pt ϖ s z hB hCo hCi hm hn hs hϖ
  have hs_pos : 0 < s := lt_of_lt_of_le hs0 hs
  obtain ⟨hϖ0, hϖ1⟩ := hϖ
  have hσ0 := pe8_sigmaS_nonneg Cv B hB T s hs_pos
  have hσt0 := pe8_sigmaT_nonneg Cv B hB T s hs_pos
  obtain ⟨hσK, hσtK⟩ := hσb Cv B hB T s hs_pos hCo hCi hm hn
  have hLam := pe8_Lam T (ϖ * resid Ah z) (sampU Cv B z) (sampV Cv B z) s hs_pos
  rw [← pe8_momN_eq] at hLam
  have hN0 : 0 ≤ momN Cv B z := by unfold momN; positivity
  obtain ⟨-, -, -, b1, b2, b3⟩ := hκ T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)
    (sigmaS Cv B T s) (sigmaT Cv B T s) (momN Cv B z) (xMinor Cv B T ϖ s) hs hϖ0 hϖ1 hσ0 hσt0
    (pe8_sU_le_N Cv B T z s hs_pos) (pe8_sV_le_N Cv B T z s hs_pos) hN0 hσK hσtK rfl hLam.2
  set P8 := ((1 + |resid Ah z|) * (1 + momN Cv B z)) ^ 8 with hP8
  have hP80 : 0 ≤ P8 := by positivity
  have hu : ∑ i, sampU Cv B z i ^ 2 ≤ momN Cv B z := by
    rw [pe8_momN_eq]; unfold sqNorm; have : 0 ≤ ∑ j, sampV Cv B z j ^ 2 := by positivity
    linarith
  have hv : ∑ i, sampV Cv B z i ^ 2 ≤ momN Cv B z := by
    rw [pe8_momN_eq]; unfold sqNorm; have : 0 ≤ ∑ j, sampU Cv B z j ^ 2 := by positivity
    linarith
  obtain ⟨hR, hRt, hX, _⟩ := lem_app_de_resolvent T s hs_pos
  set ℓ := 1 / s + 1 / (2 * Real.sqrt s) with hℓ
  have hq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs_pos
  have hℓ1 : 1 / s ≤ ℓ := by
    rw [hℓ]; have : 0 < 1 / (2 * Real.sqrt s) := by positivity
    linarith
  have hℓ2 : 1 / (2 * Real.sqrt s) ≤ ℓ := by
    rw [hℓ]; have : 0 < 1 / s := by positivity
    linarith
  have hR' : opNorm (Rs T s) ≤ ℓ := hR.trans hℓ1
  have hRt' : opNorm (Rts T s) ≤ ℓ := hRt.trans hℓ1
  have hX' : opNorm (Xs T s) ≤ ℓ := hX.trans hℓ2
  have q1 := pe8s_q_le Pt (Rs T s) _ _ (Xs T s) ℓ ℓ _ hR' hX' hu hu
  have q2 := pe8s_q_le Pt (Rs T s) _ _ (Rts T s) ℓ ℓ _ hR' hRt' hu hv
  have q3 := pe8s_q_le Pt (Xs T s) _ _ (Xs T s) ℓ ℓ _ hX' hX' hv hu
  have q4 := pe8s_q_le Pt (Xs T s) _ _ (Rts T s) ℓ ℓ _ hX' hRt' hv hv
  set Q := fro Pt * (ℓ * ℓ * momN Cv B z) with hQ
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; positivity
  have hQ0 : 0 ≤ Q := mul_nonneg (pe8s_fro_nonneg _) (mul_nonneg (mul_nonneg hℓ0 hℓ0) hN0)
  have hϖ2 : ϖ ^ 2 ≤ 1 := pow_le_one₀ hϖ0 hϖ1
  have hκP : 0 ≤ κ * P8 := mul_nonneg hκ0 hP80
  set A1 := dAlpha1 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)
  set A2 := dAlpha2 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)
  set A3 := dAlpha3 T ϖ s (sampU Cv B z) (sampV Cv B z) (resid Ah z)
  have c1 : |A1| ≤ κ * P8 := b1.trans (by
    calc ϖ * κ * P8 = ϖ * (κ * P8) := by ring
      _ ≤ 1 * (κ * P8) := mul_le_mul_of_nonneg_right hϖ1 hκP
      _ = κ * P8 := one_mul _)
  have c2 : |s * A2| ≤ κ * P8 := by
    rw [abs_mul, abs_of_pos hs_pos]
    calc s * |A2| ≤ s * (ϖ ^ 2 * κ / s * P8) := by gcongr
      _ = ϖ ^ 2 * (κ * P8) * (s / s) := by ring
      _ = ϖ ^ 2 * (κ * P8) := by rw [div_self hs_pos.ne', mul_one]
      _ ≤ 1 * (κ * P8) := mul_le_mul_of_nonneg_right hϖ2 hκP
      _ = κ * P8 := one_mul _
  have c3 : |A3| ≤ κ * P8 := b3.trans (by
    calc ϖ ^ 2 * κ * P8 = ϖ ^ 2 * (κ * P8) := by ring
      _ ≤ 1 * (κ * P8) := mul_le_mul_of_nonneg_right hϖ2 hκP
      _ = κ * P8 := one_mul _)
  have c1s : |s * A1| ≤ s * (κ * P8) := by
    rw [abs_mul, abs_of_pos hs_pos]; exact mul_le_mul_of_nonneg_left c1 hs_pos.le
  have hinner : |A3 * frobIP Pt (Rs T s * outer (sampU Cv B z) (sampU Cv B z) * Xs T s)
          + s * A1 * frobIP Pt (Rs T s * outer (sampU Cv B z) (sampV Cv B z) * Rts T s)
          - A1 * frobIP Pt (Xs T s * outer (sampV Cv B z) (sampU Cv B z) * Xs T s)
          - s * A2 * frobIP Pt (Xs T s * outer (sampV Cv B z) (sampV Cv B z) * Rts T s)| ≤
      (3 + s) * (κ * P8) * Q := by
    have t1 : |A3 * frobIP Pt (Rs T s * outer (sampU Cv B z) (sampU Cv B z) * Xs T s)| ≤
        κ * P8 * Q := by rw [abs_mul]; exact mul_le_mul c3 q1 (abs_nonneg _) (by positivity)
    have t2 : |s * A1 * frobIP Pt (Rs T s * outer (sampU Cv B z) (sampV Cv B z) * Rts T s)| ≤
        s * (κ * P8) * Q := by rw [abs_mul]; exact mul_le_mul c1s q2 (abs_nonneg _) (by positivity)
    have t3 : |A1 * frobIP Pt (Xs T s * outer (sampV Cv B z) (sampU Cv B z) * Xs T s)| ≤
        κ * P8 * Q := by rw [abs_mul]; exact mul_le_mul c1 q3 (abs_nonneg _) (by positivity)
    have t4 : |s * A2 * frobIP Pt (Xs T s * outer (sampV Cv B z) (sampV Cv B z) * Rts T s)| ≤
        κ * P8 * Q := by rw [abs_mul]; exact mul_le_mul c2 q4 (abs_nonneg _) (by positivity)
    have e : (3 + s) * (κ * P8) * Q = 3 * (κ * P8 * Q) + s * (κ * P8) * Q := by ring
    rw [e, abs_le]
    have l1 := abs_le.mp t1
    have l2 := abs_le.mp t2
    have l3 := abs_le.mp t3
    have l4 := abs_le.mp t4
    constructor <;> linarith [l1.1, l1.2, l2.1, l2.2, l3.1, l3.2, l4.1, l4.2]
  rw [abs_mul]
  calc |resid Ae z| * |A3 * frobIP Pt (Rs T s * outer (sampU Cv B z) (sampU Cv B z) * Xs T s)
          + s * A1 * frobIP Pt (Rs T s * outer (sampU Cv B z) (sampV Cv B z) * Rts T s)
          - A1 * frobIP Pt (Xs T s * outer (sampV Cv B z) (sampU Cv B z) * Xs T s)
          - s * A2 * frobIP Pt (Xs T s * outer (sampV Cv B z) (sampV Cv B z) * Rts T s)|
      ≤ |resid Ae z| * ((3 + s) * (κ * P8) * Q) := mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
    _ ≤ κ * (3 + s) * fro Pt * ℓ ^ 2 * (P8 * (|resid Ae z| * (1 + momN Cv B z))) := by
        rw [hQ]
        have ha : 0 ≤ |resid Ae z| := abs_nonneg _
        have hf : 0 ≤ fro Pt := pe8s_fro_nonneg _
        have h3s : 0 ≤ (3 + s) := by linarith
        have hall : 0 ≤ κ * P8 * |resid Ae z| * (3 + s) * fro Pt * ℓ ^ 2 :=
          mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hκP ha) h3s) hf) (sq_nonneg _)
        have hNN : momN Cv B z ≤ 1 + momN Cv B z := by linarith
        calc |resid Ae z| * ((3 + s) * (κ * P8) * (fro Pt * (ℓ * ℓ * momN Cv B z)))
            = (κ * P8 * |resid Ae z| * (3 + s) * fro Pt * ℓ ^ 2) * momN Cv B z := by ring
          _ ≤ (κ * P8 * |resid Ae z| * (3 + s) * fro Pt * ℓ ^ 2) * (1 + momN Cv B z) :=
            mul_le_mul_of_nonneg_left hNN hall
          _ = _ := by ring

private lemma pe8s_indep_sup {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (A S C : MeasurableSpace Ω) (hA : A ≤ mΩ) (hS : S ≤ mΩ)
    (hC : C ≤ mΩ) (h1 : Indep A (S ⊔ C) P) (h2 : Indep S C P) : Indep (A ⊔ S) C P := by
  let T : Set (Set Ω) := {u | ∃ a s, MeasurableSet[A] a ∧ MeasurableSet[S] s ∧ u = a ∩ s}
  have hgen : A ⊔ S = MeasurableSpace.generateFrom T := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro a ha
        exact MeasurableSpace.measurableSet_generateFrom ⟨a, univ, ha, MeasurableSet.univ, by simp⟩
      · intro x hx
        exact MeasurableSpace.measurableSet_generateFrom ⟨univ, x, MeasurableSet.univ, hx, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro u ⟨a, x, ha, hx, rfl⟩
      exact ((show A ≤ A ⊔ S from le_sup_left) _ ha).inter
        ((show S ≤ A ⊔ S from le_sup_right) _ hx)
  have hpi : IsPiSystem T := by
    rintro u ⟨a, x, ha, hx, rfl⟩ v ⟨b, y, hb, hy, rfl⟩ _
    exact ⟨a ∩ b, x ∩ y, ha.inter hb, hx.inter hy, by ext ω; simp only [mem_inter_iff]; tauto⟩
  refine IndepSets.indep (sup_le hA hS) hC hpi (@MeasurableSpace.isPiSystem_measurableSet Ω C)
    hgen (@MeasurableSpace.generateFrom_measurableSet Ω C).symm ?_
  rw [IndepSets_iff]
  rintro u c ⟨a, x, ha, hx, rfl⟩ hc
  have e1 := (Indep_iff _ _ P).1 h1 a (x ∩ c) ha
    (((show S ≤ S ⊔ C from le_sup_left) _ hx).inter ((show C ≤ S ⊔ C from le_sup_right) _ hc))
  have e2 := (Indep_iff _ _ P).1 h1 a x ha ((show S ≤ S ⊔ C from le_sup_left) _ hx)
  have e3 := (Indep_iff _ _ P).1 h2 x c hx hc
  rw [Set.inter_assoc, e1, e3, e2, mul_assoc]

private lemma pe8s_slot_indep {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (cs : ChainSamples P m n B) (s : ℤ) (a : Fin B) :
    Indep (⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act s b) inferInstance)
      (MeasurableSpace.comap (cs.act s a) inferInstance) P := by
  have hi := (iIndepFun_iff_iIndep
    (fun _ : (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B) => (inferInstance : MeasurableSpace (Vec m × Vec n)))
    _ P).mp cs.indep
  have hle : ∀ p : (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B),
      MeasurableSpace.comap ((Sum.elim (fun q : ℤ × Fin B => cs.act q.1 q.2)
        (fun q : ℤ × ℕ × Fin B => cs.aux q.1 q.2.1 q.2.2) p : Ω → Vec m × Vec n))
        inferInstance ≤ mΩ := by
    rintro (q | q)
    · exact (cs.meas_act q.1 q.2).comap_le
    · exact (cs.meas_aux q.1 q.2.1 q.2.2).comap_le
  let S1 : Set ((ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B)) := {p | ∃ b : Fin B, b ≠ a ∧ p = Sum.inl (s, b)}
  let T1 : Set ((ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B)) := {Sum.inl (s, a)}
  have hd : Disjoint S1 T1 := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨b, hb, he⟩
    simp only [Sum.inl.injEq, Prod.mk.injEq] at he
    exact hb he.2.symm
  have key := indep_iSup_of_disjoint hle hi hd
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left key ?_) ?_
  · refine iSup₂_le fun b hb => ?_
    exact le_iSup₂ (f := fun (p : (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B)) (_ : p ∈ S1) =>
      MeasurableSpace.comap ((Sum.elim (fun q : ℤ × Fin B => cs.act q.1 q.2)
        (fun q : ℤ × ℕ × Fin B => cs.aux q.1 q.2.1 q.2.2) p : Ω → Vec m × Vec n)) inferInstance)
      (Sum.inl (s, b)) ⟨b, hb, rfl⟩
  · exact le_iSup₂ (f := fun (p : (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B)) (_ : p ∈ T1) =>
      MeasurableSpace.comap ((Sum.elim (fun q : ℤ × Fin B => cs.act q.1 q.2)
        (fun q : ℤ × ℕ × Fin B => cs.aux q.1 q.2.1 q.2.2) p : Ω → Vec m × Vec n)) inferInstance)
      (Sum.inl (s, a)) (Set.mem_singleton _)

private lemma pe8s_emaChain_formula {m n B : ℕ} (β : ℝ) (D : Mat m n) (G : ℤ → Batch m n B)
    (t : ℕ) (init : Mat m n) (k : ℕ) :
    emaChain β D G t init k = β ^ k • init +
      ∑ i ∈ Finset.range k, emaW β (k - 1 - i) • batchGrad D (G ((t : ℤ) + i + 1)) := by
  induction k with
  | zero => simp [emaChain]
  | succ k ih =>
    rw [emaChain, ih, Finset.sum_range_succ, smul_add, Finset.smul_sum, smul_smul, pow_succ']
    have h : ∀ i ∈ Finset.range k, β • (emaW β (k - 1 - i) • batchGrad D (G ((t : ℤ) + i + 1))) =
        emaW β (k + 1 - 1 - i) • batchGrad D (G ((t : ℤ) + i + 1)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [smul_smul]
      congr 1
      unfold emaW
      have : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
      rw [this, pow_succ]
      ring
    rw [Finset.sum_congr rfl h]
    have h0 : emaW β (k + 1 - 1 - k) = 1 - β := by
      unfold emaW; simp
    rw [h0]
    abel

private lemma pe8s_sum_sub_single {M : Type*} [AddCommGroup M] {B : ℕ} (k j : ℕ) (hj : j < k)
    (a : Fin B) (g : ℕ → Fin B → M) :
    ∑ i ∈ Finset.range k, ∑ b, g i b - g j a =
      ∑ i ∈ Finset.range k, ∑ b, (if i = j ∧ b = a then 0 else g i b) := by
  have h : ∀ i b, g i b = (if i = j ∧ b = a then 0 else g i b) +
      (if i = j ∧ b = a then g i b else 0) := by
    intro i b; split_ifs <;> simp
  have hs : ∑ i ∈ Finset.range k, ∑ b, g i b =
      ∑ i ∈ Finset.range k, ∑ b, (if i = j ∧ b = a then 0 else g i b) +
      ∑ i ∈ Finset.range k, ∑ b, (if i = j ∧ b = a then g i b else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => h i b
  have h2 : ∑ i ∈ Finset.range k, ∑ b, (if i = j ∧ b = a then g i b else 0) = g j a := by
    simp only [ite_and]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hij]
    · intro hj'; exact absurd (Finset.mem_range.2 hj) hj'
  rw [hs, h2, add_sub_cancel_right]

private lemma pe8s_Ahat_eq {m n : ℕ} (Cv : Covariances m n) (D : Mat m n)
    (hD : riskSigma Cv D = 1 / 2) : Ahat Cv D = Arot Cv D := by
  unfold Ahat; rw [hD]; norm_num

private lemma pe8s_remainder_rep {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (Cv : Covariances m n) (cs : ChainSamples P m n B) (t j r : ℕ) (D : Mat m n)
    (a : Fin B) (hB : 0 < B) (hjr : j ≤ r) (hD : riskSigma Cv D = 1 / 2) :
    ∃ T' : Ω → Mat m n,
      Measurable[otherSigma cs t j ⊔ ⨆ (b : Fin B) (_ : b ≠ a),
        MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance] T' ∧
      ∀ ω, Summable (fun q : ℕ => emaW p.β q • batchGrad D (physBatch Cv (cs.aux (t : ℤ) q) ω)) →
        sampleRemainder p Cv cs t j r D a ω = T' ω := by
  have haux : ∀ q b, Measurable[(otherSigma cs t j ⊔ ⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance)] (cs.aux (t : ℤ) q b) := by
    intro q b
    refine measurable_iff_comap_le.2 (le_trans ?_ le_sup_left)
    refine le_trans ?_ le_sup_right
    exact le_trans (le_iSup₂ (f := fun (i : ℕ) (b : Fin B) =>
      MeasurableSpace.comap (cs.aux (t : ℤ) i b) inferInstance) q b)
      (le_iSup (fun t' : ℤ => ⨆ (i : ℕ) (b : Fin B),
        MeasurableSpace.comap (cs.aux t' i b) inferInstance) (t : ℤ))
  have hact : ∀ (i : ℕ) (b : Fin B), ¬ (i = j ∧ b = a) →
      Measurable[(otherSigma cs t j ⊔ ⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance)] (cs.act ((t : ℤ) + i + 1) b) := by
    intro i b hib
    refine measurable_iff_comap_le.2 ?_
    by_cases hi : i = j
    · subst hi
      have hb : b ≠ a := fun h => hib ⟨rfl, h⟩
      refine le_trans ?_ le_sup_right
      exact le_iSup₂ (f := fun (b : Fin B) (_ : b ≠ a) =>
        MeasurableSpace.comap (cs.act ((t : ℤ) + i + 1) b) inferInstance) b hb
    · refine le_trans ?_ le_sup_left
      refine le_trans ?_ le_sup_left
      have hne : (t : ℤ) + i + 1 ≠ (t : ℤ) + j + 1 := by
        intro h; apply hi; omega
      exact le_trans (le_iSup (fun b : Fin B =>
          MeasurableSpace.comap (cs.act ((t : ℤ) + i + 1) b) inferInstance) b)
        (le_trans (le_iSup (fun _ : (t : ℤ) + i + 1 ≠ (t : ℤ) + j + 1 => ⨆ b : Fin B,
          MeasurableSpace.comap (cs.act ((t : ℤ) + i + 1) b) inferInstance) hne)
          (le_iSup (fun s : ℤ => ⨆ (_ : s ≠ (t : ℤ) + j + 1) (b : Fin B),
            MeasurableSpace.comap (cs.act s b) inferInstance) ((t : ℤ) + i + 1)))
  let τ : Vec m × Vec n → Mat m n := fun z =>
    resid (Arot Cv D) z • outer (sampU Cv B z) (sampV Cv B z)
  have hτ : Continuous τ := by
    unfold τ resid outer sampU sampV; fun_prop
  have hcont : ∀ q : ℕ, Continuous (fun y : Fin B → Vec m × Vec n =>
      batchGrad D (fun b => phys Cv (y b))) := by
    intro q
    unfold batchGrad Muon.Setup.grad resid phys outer
    fun_prop
  let N0 : Ω → Mat m n := fun ω => Matrix.of fun i l => limUnder Filter.atTop (fun N : ℕ =>
    ∑ q ∈ Finset.range N, (emaW p.β q • batchGrad D (physBatch Cv (cs.aux (t : ℤ) q) ω)) i l)
  have hN0 : Measurable[(otherSigma cs t j ⊔ ⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance)] N0 := by
    refine @Measurable.of_eval Ω (Fin m) (fun _ => Fin n → ℝ) (otherSigma cs t j ⊔ ⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance) _ N0 fun i => ?_
    refine @Measurable.of_eval Ω (Fin n) (fun _ => ℝ) (otherSigma cs t j ⊔ ⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance) _ (fun ω => N0 ω i) fun l => ?_
    have hf : ∀ N : ℕ, StronglyMeasurable[(otherSigma cs t j ⊔ ⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance)] (fun ω => ∑ q ∈ Finset.range N,
        (emaW p.β q • batchGrad D (physBatch Cv (cs.aux (t : ℤ) q) ω)) i l) := fun N => by
      refine (Finset.measurable_sum _ fun q _ => ?_).stronglyMeasurable
      have hm : Measurable[(otherSigma cs t j ⊔ ⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance)] (fun ω => batchGrad D (physBatch Cv (cs.aux (t : ℤ) q) ω)) :=
        (hcont q).measurable.comp (@Measurable.of_eval Ω (Fin B) _ (otherSigma cs t j ⊔ ⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance) _ _ fun b => haux q b)
      exact ((measurable_pi_apply l).comp (measurable_pi_apply i)).comp
        (hm.const_smul (emaW p.β q))
    exact (@StronglyMeasurable.limUnder ℕ Ω ℝ (otherSigma cs t j ⊔ ⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance) _ _ Filter.atTop _ _ _ _ hf).measurable
  refine ⟨fun ω => p.β ^ (r + 1) • N0 ω + ∑ i ∈ Finset.range (r + 1), ∑ b : Fin B,
    (if i = j ∧ b = a then 0 else emaW p.β (r - i) • τ (cs.act ((t : ℤ) + i + 1) b ω)), ?_, ?_⟩
  · have h2 : Measurable[(otherSigma cs t j ⊔ ⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance)] (fun ω => ∑ i ∈ Finset.range (r + 1), ∑ b : Fin B,
        (if i = j ∧ b = a then 0 else emaW p.β (r - i) • τ (cs.act ((t : ℤ) + i + 1) b ω))) := by
      refine Finset.measurable_sum _ fun i _ => ?_
      refine Finset.measurable_sum _ fun b _ => ?_
      by_cases hib : i = j ∧ b = a
      · simp only [hib, and_self, ite_true]; exact measurable_const
      · simp only [hib, ite_false]
        exact (hτ.measurable.comp (hact i b hib)).const_smul (emaW p.β (r - i))
    exact (hN0.const_smul (p.β ^ (r + 1))).add h2
  · intro ω hs
    have hinit : chainInit p.β Cv D (cs.aux (t : ℤ)) ω = N0 ω := by
      ext i l
      change (∑' q : ℕ, emaW p.β q • batchGrad D (physBatch Cv (cs.aux (t : ℤ) q) ω)) i l = _
      rw [← (Pi.hasSum.1 (Pi.hasSum.1 hs.hasSum i) l).tsum_eq]
      have hsk : Summable fun q : ℕ =>
          (emaW p.β q • batchGrad D (physBatch Cv (cs.aux (t : ℤ) q) ω)) i l :=
        Pi.summable.1 (Pi.summable.1 hs i) l
      exact (hsk.hasSum.tendsto_sum_nat.limUnder_eq).symm
    have hN : stationaryN p Cv cs t D r ω = p.β ^ (r + 1) • N0 ω +
        ∑ i ∈ Finset.range (r + 1), ∑ b : Fin B,
          emaW p.β (r - i) • τ (cs.act ((t : ℤ) + i + 1) b ω) := by
      unfold stationaryN
      simp only [def_app_dyn_chains]
      rw [pe8s_emaChain_formula, hinit]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show r + 1 - 1 - i = r - i by omega]
      change emaW p.β (r - i) • batchGrad D (fun b => phys Cv (cs.act ((t : ℤ) + i + 1) b ω)) = _
      rw [pe8q_batchGrad_eq Cv hB, Finset.smul_sum]
    unfold sampleRemainder
    rw [hN, pe8s_Ahat_eq Cv D hD, add_sub_assoc]
    congr 1
    have hsub := pe8s_sum_sub_single (r + 1) j (by omega) a
      (fun i b => emaW p.β (r - i) • τ (cs.act ((t : ℤ) + i + 1) b ω))
    rw [← hsub, mul_smul]

private lemma pe8s_pointwise {m n B : ℕ} (Cv : Covariances m n) (hB : 0 < B) (N E Ah Pt : Mat m n)
    (ϖ s : ℝ) (hs : 0 < s) (hϖ : ϖ ∈ Icc (0 : ℝ) 1) (x : Fin B → Vec m × Vec n) :
    frobIP Pt (dirX N (ϖ • batchGrad E (fun b => phys Cv (x b))) s) =
      ∑ a, resid (Arot Cv E) (x a) *
        (dAlpha3 (sampleMinor N ϖ (fun b => resid Ah (x b)) (fun b => sampU Cv B (x b))
              (fun b => sampV Cv B (x b)) a) ϖ s (sampU Cv B (x a)) (sampV Cv B (x a))
              (resid Ah (x a)) *
            frobIP Pt (Rs (sampleMinor N ϖ (fun b => resid Ah (x b)) (fun b => sampU Cv B (x b))
              (fun b => sampV Cv B (x b)) a) s * outer (sampU Cv B (x a)) (sampU Cv B (x a)) *
              Xs (sampleMinor N ϖ (fun b => resid Ah (x b)) (fun b => sampU Cv B (x b))
              (fun b => sampV Cv B (x b)) a) s)
          + s * dAlpha1 (sampleMinor N ϖ (fun b => resid Ah (x b)) (fun b => sampU Cv B (x b))
              (fun b => sampV Cv B (x b)) a) ϖ s (sampU Cv B (x a)) (sampV Cv B (x a))
              (resid Ah (x a)) *
            frobIP Pt (Rs (sampleMinor N ϖ (fun b => resid Ah (x b)) (fun b => sampU Cv B (x b))
              (fun b => sampV Cv B (x b)) a) s * outer (sampU Cv B (x a)) (sampV Cv B (x a)) *
              Rts (sampleMinor N ϖ (fun b => resid Ah (x b)) (fun b => sampU Cv B (x b))
              (fun b => sampV Cv B (x b)) a) s)
          - dAlpha1 (sampleMinor N ϖ (fun b => resid Ah (x b)) (fun b => sampU Cv B (x b))
              (fun b => sampV Cv B (x b)) a) ϖ s (sampU Cv B (x a)) (sampV Cv B (x a))
              (resid Ah (x a)) *
            frobIP Pt (Xs (sampleMinor N ϖ (fun b => resid Ah (x b)) (fun b => sampU Cv B (x b))
              (fun b => sampV Cv B (x b)) a) s * outer (sampV Cv B (x a)) (sampU Cv B (x a)) *
              Xs (sampleMinor N ϖ (fun b => resid Ah (x b)) (fun b => sampU Cv B (x b))
              (fun b => sampV Cv B (x b)) a) s)
          - s * dAlpha2 (sampleMinor N ϖ (fun b => resid Ah (x b)) (fun b => sampU Cv B (x b))
              (fun b => sampV Cv B (x b)) a) ϖ s (sampU Cv B (x a)) (sampV Cv B (x a))
              (resid Ah (x a)) *
            frobIP Pt (Xs (sampleMinor N ϖ (fun b => resid Ah (x b)) (fun b => sampU Cv B (x b))
              (fun b => sampV Cv B (x b)) a) s * outer (sampV Cv B (x a)) (sampV Cv B (x a)) *
              Rts (sampleMinor N ϖ (fun b => resid Ah (x b)) (fun b => sampU Cv B (x b))
              (fun b => sampV Cv B (x b)) a) s)) := by
  rw [pe8q_batchGrad_eq Cv hB E x,
    pe8q_dirX_eq_dXExpr N ϖ s (fun b => sampU Cv B (x b)) (fun b => sampV Cv B (x b))
      (fun b => resid Ah (x b)) (fun b => resid (Arot Cv E) (x b)) hs hϖ]
  unfold dXExpr
  rw [pe8s_frobIP_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [pe8s_frobIP_smul, pe8s_frobIP_add, pe8s_frobIP_sub]

private lemma pe8s_pairSigma_eq {m n : ℕ} (Cv : Covariances m n) (D E : Mat m n) :
    pairSigma Cv D E = frobIP (Arot Cv D) (Arot Cv E) := by
  unfold pairSigma frobIP Arot
  rw [Matrix.transpose_mul, Matrix.transpose_mul, pe8s_rOut_T, pe8s_rIn_T]
  have e : rOut Cv * D * rIn Cv * (rIn Cv * (Eᵀ * rOut Cv)) =
      (rOut Cv * D * (rIn Cv * rIn Cv) * Eᵀ) * rOut Cv := by simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm (rOut Cv * D * (rIn Cv * rIn Cv) * Eᵀ), pe8s_rIn_sq]
  have e2 : rOut Cv * (rOut Cv * D * Cv.Sin * Eᵀ) = (rOut Cv * rOut Cv) * D * Cv.Sin * Eᵀ := by
    simp only [Matrix.mul_assoc]
  rw [e2, pe8s_rOut_sq]

private lemma pe8s_Arot_bounds {m n : ℕ} (Cv : Covariances m n) (CS : ℝ)
    (hCo : opNorm Cv.Sout ≤ CS) (hCi : opNorm Cv.Sin ≤ CS) (E : Mat m n) :
    fro (Arot Cv E) ≤ CS * fro E ∧ opNorm (Arot Cv E) ≤ CS * opNorm E := by
  obtain ⟨-, h12, -, -⟩ := pe8s_rr_op Cv CS hCo hCi
  have h0 := pe8_opNorm_nonneg (rOut Cv)
  have h1 := pe8_opNorm_nonneg (rIn Cv)
  constructor
  · refine (pe8s_fro_sandwich _ _ _).trans ?_
    calc opNorm (rOut Cv) * fro E * opNorm (rIn Cv) = opNorm (rOut Cv) * opNorm (rIn Cv) * fro E := by
          ring
      _ ≤ CS * fro E := mul_le_mul_of_nonneg_right h12 (pe8s_fro_nonneg _)
  · unfold Arot
    refine (pe8_opNorm_mul_le _ _).trans ?_
    have h2 := pe8_opNorm_mul_le (rOut Cv) E
    calc opNorm (rOut Cv * E) * opNorm (rIn Cv) ≤ opNorm (rOut Cv) * opNorm E * opNorm (rIn Cv) :=
          mul_le_mul_of_nonneg_right h2 h1
      _ = opNorm (rOut Cv) * opNorm (rIn Cv) * opNorm E := by ring
      _ ≤ CS * opNorm E := mul_le_mul_of_nonneg_right h12 (pe8_opNorm_nonneg _)

private lemma pe8s_meas_entries {Ω : Type*} {m n : ℕ} (G : MeasurableSpace Ω) (E : Ω → Mat m n)
    (h : ∀ i k, Measurable[G] (fun ω => E ω i k)) : Measurable[G] E :=
  Measurable.of_eval fun i => Measurable.of_eval fun k => h i k

private lemma pe8s_cont_fro {m n : ℕ} : Continuous (fun K : Mat m n => fro K) := by
  unfold fro; fun_prop

private lemma pe8s_cont_Fs {m n B : ℕ} (Cv : Covariances m n) (Ah Pt : Mat m n) (ϖ s : ℝ)
    (hs : 0 < s) (hB : 0 < B) (hA : fro Ah = 1) :
    Continuous (fun T : Mat m n => Fs Cv B Ah Pt ϖ s T) := by
  have h1 := pe8s_cont_Rs (m := m) (n := n) s hs
  have h2 := pe8s_cont_Xs (m := m) (n := n) s hs
  have h3 := pe8s_cont_Rts (m := m) (n := n) s hs
  obtain ⟨-, -, hlip, -, -⟩ := lem_app_dyn_raw Ah hA
  have hx : Continuous (fun T : Mat m n => xMinor Cv B T ϖ s) := by
    unfold xMinor sigmaS sigmaT; fun_prop
  have hb : ContinuousOn (bFun Ah) (Ici 0) := by
    refine Metric.continuousOn_iff.2 fun x hx ε hε => ⟨ε / 12, by positivity, fun y hy hxy => ?_⟩
    rw [Real.dist_eq] at hxy ⊢
    calc |bFun Ah y - bFun Ah x| ≤ 12 * |y - x| := hlip y x hy hx
      _ < 12 * (ε / 12) := by gcongr
      _ = ε := by ring
  have hbx : Continuous (fun T : Mat m n => bFun Ah (xMinor Cv B T ϖ s)) :=
    hb.comp_continuous hx fun T => by
      change 0 ≤ xMinor Cv B T ϖ s
      have := pe8_sigmaS_nonneg Cv B hB T s hs
      have := pe8_sigmaT_nonneg Cv B hB T s hs
      unfold xMinor; positivity
  unfold Fs sigmaS sigmaT frobIP
  fun_prop

private lemma pe8s_freeze_slot {Ω α : Type*} (G : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] [MeasurableSpace α] {m n : ℕ} (hG : G ≤ mΩ)
    {X : Ω → α} {Y : Ω → Vec m × Vec n} (hX : Measurable[G] X) (hY : Measurable Y)
    (hind : Indep G (MeasurableSpace.comap Y inferInstance) P) (hlaw : P.map Y = gaussPair m n)
    {φ : α → Vec m × Vec n → ℝ} (hφ : Measurable (Function.uncurry φ))
    (hfx : ∀ x, Integrable (φ x) (gaussPair m n)) (g : α → ℝ)
    (hbound : ∀ x, ∫ z, |φ x z| ∂(gaussPair m n) ≤ g x)
    (hgX : Integrable (fun ω => g (X ω)) P) :
    Integrable (fun ω => φ (X ω) (Y ω)) P ∧
    Integrable (fun ω => ∫ z, φ (X ω) z ∂(gaussPair m n)) P ∧
    ∫ ω, φ (X ω) (Y ω) ∂P = ∫ ω, ∫ z, φ (X ω) z ∂(gaussPair m n) ∂P := by
  have hXm : Measurable X := hX.mono hG le_rfl
  have habs : Measurable (Function.uncurry fun x z => |φ x z|) := hφ.abs
  have hint0 := pe8q_freeze_bound G hG hX hY hind habs (fun x z => abs_nonneg _) hgX
    (fun x => by rw [hlaw]; exact (hfx x).abs) (fun x => by rw [hlaw]; exact hbound x)
  have hm : AEStronglyMeasurable (fun ω => φ (X ω) (Y ω)) P :=
    (hφ.comp (hXm.prodMk hY)).aestronglyMeasurable
  have hint : Integrable (fun ω => φ (X ω) (Y ω)) P := by
    refine (integrable_norm_iff hm).1 ?_
    simpa only [Real.norm_eq_abs] using hint0
  have hfr := Muon.Foundations.freezing_condExp G hG hX hY hind hφ hint
  rw [hlaw] at hfr
  refine ⟨hint, integrable_condExp.congr hfr, ?_⟩
  rw [← integral_condExp hG]
  exact integral_congr_ae hfr

private lemma pe8s_Fs_bound {m n B : ℕ} (Cv : Covariances m n) (Ah Pt : Mat m n) (ϖ s CS K1 cP : ℝ)
    (hs : 0 < s) (hA : fro Ah = 1) (hP : fro Pt ≤ cP) (hCo : opNorm Cv.Sout ≤ CS)
    (hCi : opNorm Cv.Sin ≤ CS)
    (hσ : ∀ T : Mat m n, s * sigmaS Cv B T s ≤ K1 ∧ s * sigmaT Cv B T s ≤ K1)
    (hσ0 : ∀ T : Mat m n, 0 ≤ sigmaS Cv B T s ∧ 0 ≤ sigmaT Cv B T s) (T : Mat m n) :
    |Fs Cv B Ah Pt ϖ s T| ≤
      2 * K1 * (2 * (cP * (Real.sqrt n * (1 / s * CS * (1 / (2 * Real.sqrt s)))))) := by
  obtain ⟨-, hb2, -, -, -⟩ := lem_app_dyn_raw Ah hA
  obtain ⟨hR, hRt, hX, _⟩ := lem_app_de_resolvent T s hs
  have hx0 : 0 ≤ xMinor Cv B T ϖ s := by
    unfold xMinor; have := (hσ0 T).1; have := (hσ0 T).2; positivity
  have hb := hb2 _ hx0
  have t1 := pe8s_tbound Pt (Rs T s) Cv.Sout (Xs T s) cP (Real.sqrt n) (1 / s) CS
    (1 / (2 * Real.sqrt s)) hP le_rfl hR hCo hX
  have t4 := pe8s_tbound Pt (Xs T s) Cv.Sin (Rts T s) cP (Real.sqrt n) (1 / (2 * Real.sqrt s)) CS
    (1 / s) hP le_rfl hX hCi hRt
  set L := cP * (Real.sqrt n * (1 / s * CS * (1 / (2 * Real.sqrt s)))) with hL
  have t4' : |frobIP Pt (Xs T s * Cv.Sin * Rts T s)| ≤ L := t4.trans (le_of_eq (by rw [hL]; ring))
  obtain ⟨hs1, hs2⟩ := hσ T
  obtain ⟨h01, h02⟩ := hσ0 T
  have hL0 : 0 ≤ L := (abs_nonneg _).trans t1
  unfold Fs
  rw [abs_mul, abs_mul, abs_of_pos hs]
  have hsum : |sigmaT Cv B T s * frobIP Pt (Rs T s * Cv.Sout * Xs T s) +
      sigmaS Cv B T s * frobIP Pt (Xs T s * Cv.Sin * Rts T s)| ≤
      sigmaT Cv B T s * L + sigmaS Cv B T s * L := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg h01, abs_of_nonneg h02]
    exact add_le_add (mul_le_mul_of_nonneg_left t1 h02) (mul_le_mul_of_nonneg_left t4' h01)
  calc s * |bFun Ah (xMinor Cv B T ϖ s)| * |sigmaT Cv B T s * frobIP Pt (Rs T s * Cv.Sout * Xs T s) +
      sigmaS Cv B T s * frobIP Pt (Xs T s * Cv.Sin * Rts T s)|
      ≤ s * 2 * (sigmaT Cv B T s * L + sigmaS Cv B T s * L) := by
        gcongr
    _ = 2 * ((s * sigmaT Cv B T s) * L + (s * sigmaS Cv B T s) * L) := by ring
    _ ≤ 2 * (K1 * L + K1 * L) := by gcongr
    _ = 2 * K1 * (2 * L) := by ring

/-- `prop:app-dyn-reduction`, snapshot `cr-2026-10-23`. Statement verbatim from `section.tex` (ll. 1237–1256):
```latex
\begin{proposition}[Causal resolvent reduction]\label{prop:app-dyn-reduction}
Let $D$ be deterministic with $2\cR(D)=1$, consider the stationary chain at
$(t,D)$, let $0\le j\le r$, $\varpi\defeq\emaw{r-j}$ and $s\ge s_\circ>0$, and let
$E$ be a random matrix independent of the batch of step $t+j$ with
$\norm E\le c_E$ and $\norm E_\F\le c_E\sqrt B$. For each sample $a$ of that
batch let $T_a\defeq N_r-\varpi d_{j,a}\mathsf u_{j,a}\tensor\mathsf v_{j,a}$, let
$\sigma_a,\tilde\sigma_a,x_a$ be the quantities \cref{eqn:app-dyn-minor-traces}
of $T_a$, and put
\begin{equation}\label{eqn:app-dyn-F}
\begin{gathered}
F_s(T_a)\defeq s\,b(x_a)\Big\{\tilde\sigma_a\big\langle\Pi,R_s(T_a)\Sigmaout\mathsf X_s(T_a)\big\rangle+\sigma_a\big\langle\Pi,\mathsf X_s(T_a)\Sigmain\widetilde R_s(T_a)\big\rangle\Big\},\\
g(E)\defeq\langle\Sigmaout D\Sigmain,E\rangle .
\end{gathered}
\end{equation}
Then
\[
\Big|\EE\big\langle\Pi,D\mathsf X_s(N_r)\big[\varpi G^\circ_{t+j+1}[E]\big]\big\rangle+\frac{\varpi^2}{B}\sum_{a\le B}\EE\big[F_s(T_a)\,g(E)\big]\Big|\le\frac{C\sqrt B\,\varpi}{s},
\]
with $C$ depending only on $(s_\circ,c_\Pi,c_E,\gamma_\star,C_\Sigma)$.
\end{proposition}
```
-/
theorem prop_app_dyn_reduction (certQ : Muon.External.GaussianQuadFormLp) (γ CS s0 cP cE : ℝ) (hs0 : 0 < s0) :
    ∃ C : ℝ, ∀ (p : DynParams), p.γstar = γ → p.CSig = CS → ∀ (m n B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (Cv : Covariances m n) (cs : ChainSamples P m n B)
      (t j r : ℕ) (D Pt : Mat m n) (E : Ω → Mat m n) (piT s : ℝ),
      (m : ℝ) ≤ p.γstar * B → (n : ℝ) ≤ p.γstar * B →
      opNorm Cv.Sout ≤ p.CSig → opNorm Cv.Sin ≤ p.CSig → 0 < B →
      riskSigma Cv D = 1 / 2 → IsTest cP piT Pt → j ≤ r → s0 ≤ s →
      (∀ ω, opNorm (E ω) ≤ cE ∧ fro (E ω) ≤ cE * Real.sqrt B) →
      -- Independence in the strengthened form of CORRECTIONS row 19 (the source, ll. 1240–1241, asks only
      -- independence of `E` and the batch; its proof, l. 1259, uses joint independence with all other samples).
      (∀ (i : Fin m) (k : Fin n), Measurable (fun ω => E ω i k)) →
      Indep ((⨆ (i : Fin m) (k : Fin n), MeasurableSpace.comap (fun ω => E ω i k) inferInstance) ⊔
          otherSigma cs t j) (batchSigma cs t j) P →
      Integrable (fun ω => frobIP Pt (dirX (stationaryN p Cv cs t D r ω)
          (emaW p.β (r - j) • batchGrad (E ω) (physBatch Cv (cs.act ((t : ℤ) + j + 1)) ω)) s)) P ∧
      (∀ a : Fin B, Integrable (fun ω => Fs Cv B (Ahat Cv D) Pt (emaW p.β (r - j)) s
          (sampleRemainder p Cv cs t j r D a ω) * pairSigma Cv D (E ω)) P) ∧
      |(∫ ω, frobIP Pt (dirX (stationaryN p Cv cs t D r ω)
            (emaW p.β (r - j) • batchGrad (E ω) (physBatch Cv (cs.act ((t : ℤ) + j + 1)) ω)) s) ∂P)
          + (emaW p.β (r - j)) ^ 2 / (B : ℝ) * ∑ a : Fin B,
              (∫ ω, Fs Cv B (Ahat Cv D) Pt (emaW p.β (r - j)) s
                (sampleRemainder p Cv cs t j r D a ω) * pairSigma Cv D (E ω) ∂P)|
        ≤ C * Real.sqrt B * emaW p.β (r - j) / s := by
  obtain ⟨K, hK0, hcore⟩ := pe8s_core certQ γ CS s0 cP (max CS 0 * max cE 0) hs0
  obtain ⟨κ, hκ0, hκ⟩ := pe8s_phi_bound certQ γ CS s0 hs0
  obtain ⟨Kmix, hKmix0, hKmix⟩ := pe8q_gaussian_mixed_moment γ CS
  obtain ⟨K1, hK1, hσb⟩ := pe8_sigma_bound certQ γ CS
  refine ⟨K, ?_⟩
  intro p hpγ hpC m n B Ω _ P _ Cv cs t j r D Pt E piT s hm hn hCo hCi hB hD hP hjr hs hE hEm hind
  have hsize : Muon.Volatility.SizeFin Cv B p.γstar p.CSig :=
    ⟨by rw [Nat.cast_max]; exact max_le hm hn, hCo, hCi⟩
  rw [hpγ] at hm hn
  rw [hpC] at hCo hCi
  have hs_pos : 0 < s := lt_of_lt_of_le hs0 hs
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hϖ : emaW p.β (r - j) ∈ Icc (0 : ℝ) 1 := pe8q_emaW_mem_Icc p (r - j)
  have hDpos : 0 < riskSigma Cv D := by rw [hD]; norm_num
  have hAh : fro (Ahat Cv D) = 1 := pe8q_Ahat_fro Cv D hDpos
  have hsum := (lem_app_dyn_chains_iii p Cv cs t D 0 hDpos hsize).1
  have hCS' : CS ≤ max CS 0 := le_max_left _ _
  have hCS0 : 0 ≤ max CS 0 := le_max_right _ _
  have hcE0 : 0 ≤ max cE 0 := le_max_right _ _
  obtain ⟨φ, hφ⟩ : ∃ φ : Mat m n × Mat m n → Vec m × Vec n → ℝ, ∀ pr z, φ pr z =
      resid (Arot Cv pr.2) z *
        (dAlpha3 pr.1 (emaW p.β (r - j)) s (sampU Cv B z) (sampV Cv B z) (resid (Ahat Cv D) z) *
            frobIP Pt (Rs pr.1 s * outer (sampU Cv B z) (sampU Cv B z) * Xs pr.1 s)
          + s * dAlpha1 pr.1 (emaW p.β (r - j)) s (sampU Cv B z) (sampV Cv B z)
              (resid (Ahat Cv D) z) *
            frobIP Pt (Rs pr.1 s * outer (sampU Cv B z) (sampV Cv B z) * Rts pr.1 s)
          - dAlpha1 pr.1 (emaW p.β (r - j)) s (sampU Cv B z) (sampV Cv B z) (resid (Ahat Cv D) z) *
            frobIP Pt (Xs pr.1 s * outer (sampV Cv B z) (sampU Cv B z) * Xs pr.1 s)
          - s * dAlpha2 pr.1 (emaW p.β (r - j)) s (sampU Cv B z) (sampV Cv B z)
              (resid (Ahat Cv D) z) *
            frobIP Pt (Xs pr.1 s * outer (sampV Cv B z) (sampV Cv B z) * Rts pr.1 s)) :=
    ⟨_, fun _ _ => rfl⟩
  have hφm : Measurable (Function.uncurry φ) := by
    change Measurable (fun q : (Mat m n × Mat m n) × (Vec m × Vec n) => φ q.1 q.2)
    simp only [hφ]
    exact pe8s_meas_phi Cv B (Ahat Cv D) Pt _ s hs_pos hϖ
  have hpt : ∀ ω, frobIP Pt (dirX (stationaryN p Cv cs t D r ω)
      (emaW p.β (r - j) • batchGrad (E ω) (physBatch Cv (cs.act ((t : ℤ) + j + 1)) ω)) s) =
      ∑ a, φ (sampleRemainder p Cv cs t j r D a ω, E ω) (cs.act ((t : ℤ) + j + 1) a ω) := by
    intro ω
    simp only [hφ]
    exact pe8s_pointwise Cv hB _ (E ω) (Ahat Cv D) Pt _ s hs_pos hϖ
      (fun b => cs.act ((t : ℤ) + j + 1) b ω)
  have hEb : ∀ ω, fro (Arot Cv (E ω)) ≤ max CS 0 * max cE 0 * Real.sqrt B ∧
      opNorm (Arot Cv (E ω)) ≤ max CS 0 * max cE 0 := by
    intro ω
    obtain ⟨h1, h2⟩ := pe8s_Arot_bounds Cv (max CS 0) (hCo.trans hCS') (hCi.trans hCS') (E ω)
    obtain ⟨hE1, hE2⟩ := hE ω
    constructor
    · calc fro (Arot Cv (E ω)) ≤ max CS 0 * fro (E ω) := h1
        _ ≤ max CS 0 * (max cE 0 * Real.sqrt B) := mul_le_mul_of_nonneg_left
            (hE2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))) hCS0
        _ = _ := by ring
    · exact h2.trans (mul_le_mul_of_nonneg_left (hE1.trans (le_max_left _ _)) hCS0)
  have hEmeas : Measurable E := pe8s_meas_entries _ E hEm
  have hg : ∀ ω, |pairSigma Cv D (E ω)| ≤ max CS 0 * max cE 0 * Real.sqrt B := by
    intro ω
    rw [pe8s_pairSigma_eq, ← pe8s_Ahat_eq Cv D hD]
    refine (pe8m_frobIP_le_copy _ _).trans ?_
    rw [hAh, one_mul]; exact (hEb ω).1
  have hgc : Continuous (fun M : Mat m n => pairSigma Cv D M) := by unfold pairSigma; fun_prop
  have hFb := pe8s_Fs_bound (B := B) Cv (Ahat Cv D) Pt (emaW p.β (r - j)) s (max CS 0) K1 (max cP 0)
    hs_pos hAh (hP.1.trans (le_max_left _ _)) (hCo.trans hCS') (hCi.trans hCS')
    (fun T => hσb Cv B hB T s hs_pos hCo hCi hm hn)
    (fun T => ⟨pe8_sigmaS_nonneg Cv B hB T s hs_pos, pe8_sigmaT_nonneg Cv B hB T s hs_pos⟩)
  have hFc := pe8s_cont_Fs Cv (Ahat Cv D) Pt (emaW p.β (r - j)) s hs_pos hB hAh
  set cF := 2 * K1 * (2 * (max cP 0 * (Real.sqrt n * (1 / s * max CS 0 *
    (1 / (2 * Real.sqrt s)))))) with hcF
  have hcF0 : 0 ≤ cF := (abs_nonneg _).trans (hFb 0)
  set cφ := κ * (3 + s) * fro Pt * (1 / s + 1 / (2 * Real.sqrt s)) ^ 2 with hcφ
  have hcφ0 : 0 ≤ cφ := by
    have := pe8s_fro_nonneg Pt
    rw [hcφ]; have : (0 : ℝ) ≤ 3 + s := by linarith
    positivity
  have hdom : ∀ pr z, |φ pr z| ≤ cφ * (((1 + |resid (Ahat Cv D) z|) * (1 + momN Cv B z)) ^ 8 *
      (|resid (Arot Cv pr.2) z| * (1 + momN Cv B z))) := fun pr z => by
    rw [hφ]; exact hκ Cv pr.1 (Arot Cv pr.2) (Ahat Cv D) Pt _ s z hB hCo hCi hm hn hs hϖ
  have hHi := fun pr : Mat m n × Mat m n =>
    hKmix Cv (Ahat Cv D) (Arot Cv pr.2) hAh hm hn hCo hCi
  have hfx : ∀ pr, Integrable (φ pr) (gaussPair m n) := fun pr =>
    ((hHi pr).1.const_mul cφ).mono' (hφm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hdom pr z)
  have hbd : ∀ pr, ∫ z, |φ pr z| ∂(gaussPair m n) ≤ cφ * (Kmix * fro (Arot Cv pr.2)) := fun pr =>
    (integral_mono (hfx pr).abs ((hHi pr).1.const_mul cφ) (fun z => hdom pr z)).trans
      (by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (hHi pr).2 hcφ0)
  have hslot : ∀ a : Fin B,
      Integrable (fun ω => φ (sampleRemainder p Cv cs t j r D a ω, E ω)
        (cs.act ((t : ℤ) + j + 1) a ω)) P ∧
      Integrable (fun ω => Fs Cv B (Ahat Cv D) Pt (emaW p.β (r - j)) s
        (sampleRemainder p Cv cs t j r D a ω) * pairSigma Cv D (E ω)) P ∧
      |∫ ω, φ (sampleRemainder p Cv cs t j r D a ω, E ω) (cs.act ((t : ℤ) + j + 1) a ω) ∂P
        + (emaW p.β (r - j)) ^ 2 / (B : ℝ) * ∫ ω, Fs Cv B (Ahat Cv D) Pt (emaW p.β (r - j)) s
          (sampleRemainder p Cv cs t j r D a ω) * pairSigma Cv D (E ω) ∂P| ≤
        K * emaW p.β (r - j) / (s * Real.sqrt B) := by
    intro a
    obtain ⟨T', hT'm, hT'eq⟩ := pe8s_remainder_rep p Cv cs t j r D a hB hjr hD
    have hTae : ∀ᵐ ω ∂P, sampleRemainder p Cv cs t j r D a ω = T' ω :=
      hsum.mono fun ω hω => hT'eq ω hω
    have hEσ : (⨆ (i : Fin m) (k : Fin n), MeasurableSpace.comap (fun ω => E ω i k) inferInstance) ≤ ‹MeasurableSpace Ω› :=
      iSup₂_le fun i k => (hEm i k).comap_le
    have hO : otherSigma cs t j ≤ ‹MeasurableSpace Ω› :=
      sup_le (iSup_le fun s' => iSup_le fun _ => iSup_le fun b => (cs.meas_act s' b).comap_le)
        (iSup_le fun t' => iSup_le fun i => iSup_le fun b => (cs.meas_aux t' i b).comap_le)
    have hA : (⨆ (i : Fin m) (k : Fin n), MeasurableSpace.comap (fun ω => E ω i k) inferInstance) ⊔ otherSigma cs t j ≤ ‹MeasurableSpace Ω› := sup_le hEσ hO
    have hS : (⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance) ≤ ‹MeasurableSpace Ω› :=
      iSup_le fun b => iSup_le fun _ => (cs.meas_act _ b).comap_le
    have hC : MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) a) inferInstance ≤
        ‹MeasurableSpace Ω› := (cs.meas_act _ a).comap_le
    have h1 : Indep ((⨆ (i : Fin m) (k : Fin n), MeasurableSpace.comap (fun ω => E ω i k) inferInstance) ⊔ otherSigma cs t j)
        ((⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance) ⊔ MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) a) inferInstance) P :=
      indep_of_indep_of_le_right hind (sup_le (iSup₂_le fun b _ =>
        le_iSup (fun b => MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance) b)
        (le_iSup (fun b => MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance) a))
    have hindA := pe8s_indep_sup _ _ _ hA hS hC h1 (pe8s_slot_indep cs _ a)
    have hEG : Measurable[((⨆ (i : Fin m) (k : Fin n), MeasurableSpace.comap (fun ω => E ω i k) inferInstance) ⊔ otherSigma cs t j) ⊔ (⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance)] E := by
      refine (pe8s_meas_entries (⨆ (i : Fin m) (k : Fin n), MeasurableSpace.comap (fun ω => E ω i k) inferInstance) E fun i k => ?_).mono (le_sup_left.trans le_sup_left) le_rfl
      exact (measurable_iff_comap_le.2 le_rfl).mono (le_iSup₂ (f := fun (i : Fin m) (k : Fin n) =>
        MeasurableSpace.comap (fun ω => E ω i k) inferInstance) i k) le_rfl
    have hXm : Measurable[((⨆ (i : Fin m) (k : Fin n), MeasurableSpace.comap (fun ω => E ω i k) inferInstance) ⊔ otherSigma cs t j) ⊔ (⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance)] (fun ω => (T' ω, E ω)) :=
      (hT'm.mono (sup_le (le_sup_right.trans le_sup_left) le_sup_right) le_rfl).prodMk hEG
    have hT'meas : Measurable T' := hT'm.mono (sup_le hO hS) le_rfl
    have hgX : Integrable (fun ω => cφ * (Kmix * fro (Arot Cv (T' ω, E ω).2))) P := by
      refine Integrable.of_bound (((pe8s_cont_fro.comp (by unfold Arot; fun_prop :
        Continuous (fun M : Mat m n => Arot Cv M))).measurable.comp hEmeas).const_mul Kmix
          |>.const_mul cφ).aestronglyMeasurable
        (cφ * (Kmix * (max CS 0 * max cE 0 * Real.sqrt B))) (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := pe8s_fro_nonneg (Arot Cv (E ω)); positivity)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hEb ω).1 hKmix0) hcφ0
    obtain ⟨hI1, hI2, hI3⟩ := pe8s_freeze_slot (((⨆ (i : Fin m) (k : Fin n), MeasurableSpace.comap (fun ω => E ω i k) inferInstance) ⊔ otherSigma cs t j) ⊔ (⨆ (b : Fin B) (_ : b ≠ a), MeasurableSpace.comap (cs.act ((t : ℤ) + j + 1) b) inferInstance)) (sup_le hA hS) hXm
      (cs.meas_act _ a) hindA (by unfold gaussPair; exact cs.law_act _ _) hφm hfx _ (fun pr => hbd pr) hgX
    have hφae : (fun ω => φ (sampleRemainder p Cv cs t j r D a ω, E ω)
        (cs.act ((t : ℤ) + j + 1) a ω)) =ᵐ[P]
        fun ω => φ (T' ω, E ω) (cs.act ((t : ℤ) + j + 1) a ω) :=
      hTae.mono fun ω hω => by simp only [hω]
    have hFae : (fun ω => Fs Cv B (Ahat Cv D) Pt (emaW p.β (r - j)) s
        (sampleRemainder p Cv cs t j r D a ω) * pairSigma Cv D (E ω)) =ᵐ[P]
        fun ω => Fs Cv B (Ahat Cv D) Pt (emaW p.β (r - j)) s (T' ω) * pairSigma Cv D (E ω) :=
      hTae.mono fun ω hω => by simp only [hω]
    have hFint : Integrable (fun ω => Fs Cv B (Ahat Cv D) Pt (emaW p.β (r - j)) s (T' ω) *
        pairSigma Cv D (E ω)) P := by
      refine Integrable.of_bound ((hFc.measurable.comp hT'meas).mul
        (hgc.measurable.comp hEmeas)).aestronglyMeasurable
        (cF * (max CS 0 * max cE 0 * Real.sqrt B)) (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hFb _) (hg ω) (abs_nonneg _) hcF0
    refine ⟨hI1.congr hφae.symm, hFint.congr hFae.symm, ?_⟩
    rw [integral_congr_ae hφae, integral_congr_ae hFae, hI3, ← integral_const_mul,
      ← integral_add hI2 (hFint.const_mul _)]
    have hpt' : ∀ ω, ‖∫ z, φ (T' ω, E ω) z ∂(gaussPair m n) + (emaW p.β (r - j)) ^ 2 / (B : ℝ) *
        (Fs Cv B (Ahat Cv D) Pt (emaW p.β (r - j)) s (T' ω) * pairSigma Cv D (E ω))‖ ≤
        K * emaW p.β (r - j) / (s * Real.sqrt B) := by
      intro ω
      have hc := hcore Cv (T' ω) (Ahat Cv D) (Arot Cv (E ω)) Pt piT (emaW p.β (r - j)) s
        (φ (T' ω, E ω)) hB hCo hCi hm hn hAh hs hϖ hP (hEb ω).1 (hEb ω).2 (fun z => hφ _ z)
      rw [Real.norm_eq_abs, pe8s_pairSigma_eq, ← pe8s_Ahat_eq Cv D hD]
      exact hc.2
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (Eventually.of_forall hpt')).trans ?_
    simp
  have hint1 : Integrable (fun ω => frobIP Pt (dirX (stationaryN p Cv cs t D r ω)
      (emaW p.β (r - j) • batchGrad (E ω) (physBatch Cv (cs.act ((t : ℤ) + j + 1)) ω)) s)) P := by
    rw [funext hpt]
    exact integrable_finsetSum _ fun a _ => (hslot a).1
  refine ⟨hint1, fun a => (hslot a).2.1, ?_⟩
  rw [funext hpt, integral_finsetSum _ fun a _ => (hslot a).1, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  calc |∑ a : Fin B, (∫ ω, φ (sampleRemainder p Cv cs t j r D a ω, E ω)
          (cs.act ((t : ℤ) + j + 1) a ω) ∂P
        + (emaW p.β (r - j)) ^ 2 / (B : ℝ) * ∫ ω, Fs Cv B (Ahat Cv D) Pt (emaW p.β (r - j)) s
          (sampleRemainder p Cv cs t j r D a ω) * pairSigma Cv D (E ω) ∂P)|
      ≤ ∑ a : Fin B, |∫ ω, φ (sampleRemainder p Cv cs t j r D a ω, E ω)
          (cs.act ((t : ℤ) + j + 1) a ω) ∂P
        + (emaW p.β (r - j)) ^ 2 / (B : ℝ) * ∫ ω, Fs Cv B (Ahat Cv D) Pt (emaW p.β (r - j)) s
          (sampleRemainder p Cv cs t j r D a ω) * pairSigma Cv D (E ω) ∂P| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin B, K * emaW p.β (r - j) / (s * Real.sqrt B) :=
        Finset.sum_le_sum fun a _ => (hslot a).2.2
    _ = K * Real.sqrt B * emaW p.β (r - j) / s := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hq : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.2 hBr
        have hqq : Real.sqrt (B : ℝ) * Real.sqrt B = B := Real.mul_self_sqrt hBr.le
        calc (B : ℝ) * (K * emaW p.β (r - j) / (s * Real.sqrt B))
            = (Real.sqrt B * Real.sqrt B) * (K * emaW p.β (r - j) / (s * Real.sqrt B)) := by
              rw [hqq]
          _ = K * Real.sqrt B * emaW p.β (r - j) / s := by field_simp

private lemma pe8m_frobIP_le {m n : ℕ} (A D : Mat m n) :
    |frobIP A D| ≤ fro A * fro D := by
  have htr : frobIP A D = ∑ x : Fin m × Fin n, A x.1 x.2 * D x.1 x.2 := by
    simp [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [htr]
  calc
    |∑ x : Fin m × Fin n, A x.1 x.2 * D x.1 x.2| ≤
        ∑ x : Fin m × Fin n, |A x.1 x.2| * |D x.1 x.2| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun x : Fin m × Fin n => A x.1 x.2 * D x.1 x.2) Finset.univ
    _ ≤ _ := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m × Fin n))
        (fun x => |A x.1 x.2|) (fun x => |D x.1 x.2|)
      simpa [fro, Fintype.sum_prod_type, Real.norm_eq_abs] using h

private lemma pe8m_fro_le_sqrt_cols_op {m n : ℕ} (A : Mat m n) :
    fro A ≤ Real.sqrt n * opNorm A := by
  have h0 : 0 ≤ fro A := Real.sqrt_nonneg _
  have h1 : 0 ≤ Real.sqrt n * opNorm A :=
    mul_nonneg (Real.sqrt_nonneg _) (pe8_opNorm_nonneg _)
  apply (pow_le_pow_iff_left₀ h0 h1 (by norm_num : (2 : ℕ) ≠ 0)).mp
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity),
    mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa [Real.norm_eq_abs, sq_abs] using pe8_fro_sq_le A

private lemma pe8m_op_transpose {m n : ℕ} (A : Mat m n) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
    rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.l2_opNorm_conjTranspose]

private lemma pe8m_sigma_upper {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (hB : 0 < B)
    (T : Mat m n) (s : ℝ) (hs : 0 < s) (CS γ : ℝ)
    (hCo : opNorm Cv.Sout ≤ CS) (hCi : opNorm Cv.Sin ≤ CS)
    (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B) :
    sigmaS Cv B T s ≤ γ * CS / s ∧ sigmaT Cv B T s ≤ γ * CS / s := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCS : 0 ≤ CS := (pe8_opNorm_nonneg Cv.Sout).trans hCo
  have hRs := (lem_app_de_resolvent T s hs).1
  have hRt := (lem_app_de_resolvent T s hs).2.1
  have hrS := nuc_le_rank_mul_opNorm (Rs T s)
  have hrT := nuc_le_rank_mul_opNorm (Rts T s)
  have hm' : ((Rs T s).rank : ℝ) ≤ m := by
    exact_mod_cast Matrix.rank_le_height (Rs T s)
  have hn' : ((Rts T s).rank : ℝ) ≤ n := by
    exact_mod_cast Matrix.rank_le_height (Rts T s)
  have hnS : nuc (Rs T s) ≤ (m : ℝ) / s := by
    calc
      nuc (Rs T s) ≤ ((Rs T s).rank : ℝ) * opNorm (Rs T s) := hrS
      _ ≤ (m : ℝ) * (1 / s) :=
        mul_le_mul hm' hRs (pe8_opNorm_nonneg _) (Nat.cast_nonneg _)
      _ = (m : ℝ) / s := by ring
  have hnT : nuc (Rts T s) ≤ (n : ℝ) / s := by
    calc
      nuc (Rts T s) ≤ ((Rts T s).rank : ℝ) * opNorm (Rts T s) := hrT
      _ ≤ (n : ℝ) * (1 / s) :=
        mul_le_mul hn' hRt (pe8_opNorm_nonneg _) (Nat.cast_nonneg _)
      _ = (n : ℝ) / s := by ring
  constructor
  · unfold sigmaS
    calc
      (B : ℝ)⁻¹ * (Cv.Sout * Rs T s).trace
          ≤ (B : ℝ)⁻¹ * |(Cv.Sout * Rs T s).trace| := by gcongr; exact le_abs_self _
      _ ≤ (B : ℝ)⁻¹ * (opNorm Cv.Sout * nuc (Rs T s)) := by
        gcongr; exact trace_mul_le_opNorm_mul_nuc _ _
      _ ≤ (B : ℝ)⁻¹ * (CS * ((m : ℝ) / s)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul hCo hnS (nuc_nonneg _) hCS
      _ ≤ (B : ℝ)⁻¹ * (CS * ((γ * B) / s)) := by gcongr
      _ = γ * CS / s := by field_simp
  · unfold sigmaT
    calc
      (B : ℝ)⁻¹ * (Cv.Sin * Rts T s).trace
          ≤ (B : ℝ)⁻¹ * |(Cv.Sin * Rts T s).trace| := by gcongr; exact le_abs_self _
      _ ≤ (B : ℝ)⁻¹ * (opNorm Cv.Sin * nuc (Rts T s)) := by
        gcongr; exact trace_mul_le_opNorm_mul_nuc _ _
      _ ≤ (B : ℝ)⁻¹ * (CS * ((n : ℝ) / s)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul hCi hnT (nuc_nonneg _) hCS
      _ ≤ (B : ℝ)⁻¹ * (CS * ((γ * B) / s)) := by gcongr
      _ = γ * CS / s := by field_simp

private lemma pe8m_sigma_diff {m n : ℕ} (Cv : Covariances m n) (B : ℕ) (hB : 0 < B)
    (T T' : Mat m n) (s : ℝ) (hs : 0 < s) (CS : ℝ)
    (hCo : opNorm Cv.Sout ≤ CS) (hCi : opNorm Cv.Sin ≤ CS) :
    |sigmaS Cv B T s - sigmaS Cv B T' s| ≤
        2 * CS / ((B : ℝ) * s * Real.sqrt s) * nuc (T - T') ∧
      |sigmaT Cv B T s - sigmaT Cv B T' s| ≤
        2 * CS / ((B : ℝ) * s * Real.sqrt s) * nuc (T - T') := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCS : 0 ≤ CS := (pe8_opNorm_nonneg Cv.Sout).trans hCo
  have hR := lem_app_de_lipschitz T T' s hs
  have hRt : nuc (Rts T s - Rts T' s) ≤
      2 / (s * Real.sqrt s) * nuc (T - T') := by
    have h := lem_app_de_lipschitz Tᵀ T'ᵀ s hs
    rw [← nuc_transpose (T - T')]
    simpa [pe8_Rts_eq, Matrix.transpose_sub] using h
  constructor
  · have he : sigmaS Cv B T s - sigmaS Cv B T' s =
        (B : ℝ)⁻¹ * (Cv.Sout * (Rs T s - Rs T' s)).trace := by
      unfold sigmaS
      rw [Matrix.mul_sub, Matrix.trace_sub]
      ring
    rw [he, abs_mul, abs_of_nonneg (by positivity)]
    calc
      (B : ℝ)⁻¹ * |(Cv.Sout * (Rs T s - Rs T' s)).trace|
          ≤ (B : ℝ)⁻¹ * (opNorm Cv.Sout * nuc (Rs T s - Rs T' s)) := by
        gcongr; exact trace_mul_le_opNorm_mul_nuc _ _
      _ ≤ (B : ℝ)⁻¹ * (CS * (2 / (s * Real.sqrt s) * nuc (T - T'))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul hCo hR (nuc_nonneg _) hCS
      _ = 2 * CS / ((B : ℝ) * s * Real.sqrt s) * nuc (T - T') := by ring
  · have he : sigmaT Cv B T s - sigmaT Cv B T' s =
        (B : ℝ)⁻¹ * (Cv.Sin * (Rts T s - Rts T' s)).trace := by
      unfold sigmaT
      rw [Matrix.mul_sub, Matrix.trace_sub]
      ring
    rw [he, abs_mul, abs_of_nonneg (by positivity)]
    calc
      (B : ℝ)⁻¹ * |(Cv.Sin * (Rts T s - Rts T' s)).trace|
          ≤ (B : ℝ)⁻¹ * (opNorm Cv.Sin * nuc (Rts T s - Rts T' s)) := by
        gcongr; exact trace_mul_le_opNorm_mul_nuc _ _
      _ ≤ (B : ℝ)⁻¹ * (CS * (2 / (s * Real.sqrt s) * nuc (T - T'))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul hCi hRt (nuc_nonneg _) hCS
      _ = 2 * CS / ((B : ℝ) * s * Real.sqrt s) * nuc (T - T') := by ring

private lemma pe8m_pair_upper {m n : ℕ} (Cv : Covariances m n) (Pt T : Mat m n)
    (s CS cP : ℝ) (hs : 0 < s) (hCo : opNorm Cv.Sout ≤ CS)
    (hCi : opNorm Cv.Sin ≤ CS) (hPf : fro Pt ≤ cP) :
    |frobIP Pt (Rs T s * Cv.Sout * Xs T s)| ≤
        cP * (Real.sqrt n * ((1 / s * CS) * (1 / (2 * Real.sqrt s)))) ∧
      |frobIP Pt (Xs T s * Cv.Sin * Rts T s)| ≤
        cP * (Real.sqrt n * ((1 / (2 * Real.sqrt s) * CS) * (1 / s))) := by
  have hCS : 0 ≤ CS := (pe8_opNorm_nonneg Cv.Sout).trans hCo
  have hcP : 0 ≤ cP := (Real.sqrt_nonneg _).trans hPf
  obtain ⟨hR, hRt, hX, _⟩ := lem_app_de_resolvent T s hs
  have h1 : opNorm (Rs T s * Cv.Sout * Xs T s) ≤
      (1 / s * CS) * (1 / (2 * Real.sqrt s)) := by
    calc
      opNorm (Rs T s * Cv.Sout * Xs T s)
          ≤ opNorm (Rs T s * Cv.Sout) * opNorm (Xs T s) := pe8_opNorm_mul_le _ _
      _ ≤ (opNorm (Rs T s) * opNorm Cv.Sout) * opNorm (Xs T s) :=
        mul_le_mul_of_nonneg_right (pe8_opNorm_mul_le _ _) (pe8_opNorm_nonneg _)
      _ ≤ (1 / s * CS) * (1 / (2 * Real.sqrt s)) := by
        exact mul_le_mul
          (mul_le_mul hR hCo (pe8_opNorm_nonneg _) (by positivity)) hX
          (pe8_opNorm_nonneg _) (mul_nonneg (by positivity) hCS)
  have h2 : opNorm (Xs T s * Cv.Sin * Rts T s) ≤
      (1 / (2 * Real.sqrt s) * CS) * (1 / s) := by
    calc
      opNorm (Xs T s * Cv.Sin * Rts T s)
          ≤ opNorm (Xs T s * Cv.Sin) * opNorm (Rts T s) := pe8_opNorm_mul_le _ _
      _ ≤ (opNorm (Xs T s) * opNorm Cv.Sin) * opNorm (Rts T s) :=
        mul_le_mul_of_nonneg_right (pe8_opNorm_mul_le _ _) (pe8_opNorm_nonneg _)
      _ ≤ (1 / (2 * Real.sqrt s) * CS) * (1 / s) := by
        exact mul_le_mul
          (mul_le_mul hX hCi (pe8_opNorm_nonneg _) (by positivity)) hRt
          (pe8_opNorm_nonneg _) (mul_nonneg (by positivity) hCS)
  constructor
  · exact (pe8m_frobIP_le _ _).trans
      (mul_le_mul hPf ((pe8m_fro_le_sqrt_cols_op _).trans (mul_le_mul_of_nonneg_left h1
        (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _) hcP)
  · exact (pe8m_frobIP_le _ _).trans
      (mul_le_mul hPf ((pe8m_fro_le_sqrt_cols_op _).trans (mul_le_mul_of_nonneg_left h2
        (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _) hcP)

private lemma pe8m_frobIP_nuc {m n : ℕ} (A D : Mat m n) :
    |frobIP A D| ≤ opNorm A * nuc D := by
  have h := trace_mul_le_opNorm_mul_nuc A Dᵀ
  rw [← nuc_transpose D]
  simpa [frobIP] using h

private lemma pe8m_pair_diff {m n : ℕ} (Cv : Covariances m n) (Pt T T' : Mat m n)
    (s CS piT : ℝ) (hs : 0 < s) (hCo : opNorm Cv.Sout ≤ CS)
    (hCi : opNorm Cv.Sin ≤ CS) (hPo : opNorm Pt ≤ piT) :
    |frobIP Pt (Rs T s * Cv.Sout * Xs T s) -
        frobIP Pt (Rs T' s * Cv.Sout * Xs T' s)| ≤
          piT * (2 * CS / s ^ 2 * nuc (T - T')) ∧
      |frobIP Pt (Xs T s * Cv.Sin * Rts T s) -
        frobIP Pt (Xs T' s * Cv.Sin * Rts T' s)| ≤
          piT * (2 * CS / s ^ 2 * nuc (T - T')) := by
  have hCS : 0 ≤ CS := (pe8_opNorm_nonneg Cv.Sout).trans hCo
  have hpi : 0 ≤ piT := (pe8_opNorm_nonneg Pt).trans hPo
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  obtain ⟨hR, hRt, hX, _⟩ := lem_app_de_resolvent T s hs
  obtain ⟨hR', hRt', hX', _⟩ := lem_app_de_resolvent T' s hs
  have hRd := lem_app_de_lipschitz T T' s hs
  have hXd : nuc (Xs T s - Xs T' s) ≤ 1 / s * nuc (T - T') := by
    simpa [schatNorm] using
      (lem_app_dyn_schatten_i (p := 1) (Or.inl rfl) hs T T')
  have hRtd : nuc (Rts T s - Rts T' s) ≤
      2 / (s * Real.sqrt s) * nuc (T - T') := by
    have h := lem_app_de_lipschitz Tᵀ T'ᵀ s hs
    rw [← nuc_transpose (T - T')]
    simpa [pe8_Rts_eq, Matrix.transpose_sub] using h
  have hY1 : nuc ((Rs T s * Cv.Sout * Xs T s) -
      (Rs T' s * Cv.Sout * Xs T' s)) ≤ 2 * CS / s ^ 2 * nuc (T - T') := by
    have he : (Rs T s * Cv.Sout * Xs T s) - (Rs T' s * Cv.Sout * Xs T' s) =
        (Rs T s - Rs T' s) * Cv.Sout * Xs T s +
          Rs T' s * Cv.Sout * (Xs T s - Xs T' s) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]
      abel
    rw [he]
    refine (nuc_add_le _ _).trans ?_
    have ha : nuc ((Rs T s - Rs T' s) * Cv.Sout * Xs T s) ≤
        CS / s ^ 2 * nuc (T - T') := by
      calc
        nuc ((Rs T s - Rs T' s) * Cv.Sout * Xs T s)
            ≤ nuc ((Rs T s - Rs T' s) * Cv.Sout) * opNorm (Xs T s) := nuc_mul_le_right _ _
        _ ≤ (nuc (Rs T s - Rs T' s) * opNorm Cv.Sout) * opNorm (Xs T s) := by
          exact mul_le_mul_of_nonneg_right (nuc_mul_le_right _ _) (pe8_opNorm_nonneg _)
        _ ≤ ((2 / (s * Real.sqrt s) * nuc (T - T')) * CS) *
              (1 / (2 * Real.sqrt s)) := by
          exact mul_le_mul
            (mul_le_mul hRd hCo (pe8_opNorm_nonneg _)
              (mul_nonneg (by positivity) (nuc_nonneg _))) hX
            (pe8_opNorm_nonneg _) (mul_nonneg (mul_nonneg (by positivity) (nuc_nonneg _)) hCS)
        _ = CS / s ^ 2 * nuc (T - T') := by
          field_simp [hs.ne', hsqrt.ne']
          rw [show Real.sqrt s ^ 2 = s by nlinarith [hsq]]
    have hb : nuc (Rs T' s * Cv.Sout * (Xs T s - Xs T' s)) ≤
        CS / s ^ 2 * nuc (T - T') := by
      calc
        nuc (Rs T' s * Cv.Sout * (Xs T s - Xs T' s))
            ≤ opNorm (Rs T' s * Cv.Sout) * nuc (Xs T s - Xs T' s) := nuc_mul_le_left _ _
        _ ≤ (opNorm (Rs T' s) * opNorm Cv.Sout) * nuc (Xs T s - Xs T' s) := by
          exact mul_le_mul_of_nonneg_right (pe8_opNorm_mul_le _ _) (nuc_nonneg _)
        _ ≤ (1 / s * CS) * (1 / s * nuc (T - T')) := by
          exact mul_le_mul
            (mul_le_mul hR' hCo (pe8_opNorm_nonneg _) (by positivity)) hXd
            (nuc_nonneg _) (by positivity)
        _ = CS / s ^ 2 * nuc (T - T') := by ring
    exact (add_le_add ha hb).trans_eq (by ring)
  have hY2 : nuc ((Xs T s * Cv.Sin * Rts T s) -
      (Xs T' s * Cv.Sin * Rts T' s)) ≤ 2 * CS / s ^ 2 * nuc (T - T') := by
    have he : (Xs T s * Cv.Sin * Rts T s) - (Xs T' s * Cv.Sin * Rts T' s) =
        (Xs T s - Xs T' s) * Cv.Sin * Rts T s +
          Xs T' s * Cv.Sin * (Rts T s - Rts T' s) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]
      abel
    rw [he]
    refine (nuc_add_le _ _).trans ?_
    have ha : nuc ((Xs T s - Xs T' s) * Cv.Sin * Rts T s) ≤
        CS / s ^ 2 * nuc (T - T') := by
      calc
        nuc ((Xs T s - Xs T' s) * Cv.Sin * Rts T s)
            ≤ nuc ((Xs T s - Xs T' s) * Cv.Sin) * opNorm (Rts T s) := nuc_mul_le_right _ _
        _ ≤ (nuc (Xs T s - Xs T' s) * opNorm Cv.Sin) * opNorm (Rts T s) := by
          exact mul_le_mul_of_nonneg_right (nuc_mul_le_right _ _) (pe8_opNorm_nonneg _)
        _ ≤ ((1 / s * nuc (T - T')) * CS) * (1 / s) := by
          exact mul_le_mul
            (mul_le_mul hXd hCi (pe8_opNorm_nonneg _)
              (mul_nonneg (by positivity) (nuc_nonneg _))) hRt
            (pe8_opNorm_nonneg _)
              (mul_nonneg (mul_nonneg (by positivity) (nuc_nonneg _)) hCS)
        _ = CS / s ^ 2 * nuc (T - T') := by ring
    have hb : nuc (Xs T' s * Cv.Sin * (Rts T s - Rts T' s)) ≤
        CS / s ^ 2 * nuc (T - T') := by
      calc
        nuc (Xs T' s * Cv.Sin * (Rts T s - Rts T' s))
            ≤ opNorm (Xs T' s * Cv.Sin) * nuc (Rts T s - Rts T' s) := nuc_mul_le_left _ _
        _ ≤ (opNorm (Xs T' s) * opNorm Cv.Sin) * nuc (Rts T s - Rts T' s) := by
          exact mul_le_mul_of_nonneg_right (pe8_opNorm_mul_le _ _) (nuc_nonneg _)
        _ ≤ (1 / (2 * Real.sqrt s) * CS) *
              (2 / (s * Real.sqrt s) * nuc (T - T')) := by
          exact mul_le_mul
            (mul_le_mul hX' hCi (pe8_opNorm_nonneg _) (by positivity)) hRtd
            (nuc_nonneg _) (mul_nonneg (by positivity) hCS)
        _ = CS / s ^ 2 * nuc (T - T') := by
          field_simp [hs.ne', hsqrt.ne']
          rw [show Real.sqrt s ^ 2 = s by nlinarith [hsq]]
          ring
    exact (add_le_add ha hb).trans_eq (by ring)
  constructor
  · have he : frobIP Pt (Rs T s * Cv.Sout * Xs T s) -
        frobIP Pt (Rs T' s * Cv.Sout * Xs T' s) =
        frobIP Pt ((Rs T s * Cv.Sout * Xs T s) -
          (Rs T' s * Cv.Sout * Xs T' s)) := by
      unfold frobIP
      rw [Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub]
    rw [he]
    exact (pe8m_frobIP_nuc _ _).trans (mul_le_mul hPo hY1 (nuc_nonneg _) hpi)
  · have he : frobIP Pt (Xs T s * Cv.Sin * Rts T s) -
        frobIP Pt (Xs T' s * Cv.Sin * Rts T' s) =
        frobIP Pt ((Xs T s * Cv.Sin * Rts T s) -
          (Xs T' s * Cv.Sin * Rts T' s)) := by
      unfold frobIP
      rw [Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub]
    rw [he]
    exact (pe8m_frobIP_nuc _ _).trans (mul_le_mul hPo hY2 (nuc_nonneg _) hpi)

private lemma pe8m_rpow_mhalf (x : ℝ) (hx : 0 < x) :
    x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x := by
  rw [Real.rpow_neg hx.le, Real.sqrt_eq_rpow]
  simp [one_div]

private lemma pe8m_rpow_mthreehalf (x : ℝ) (hx : 0 < x) :
    x ^ (-(3 / 2 : ℝ)) = 1 / (x * Real.sqrt x) := by
  rw [Real.rpow_neg hx.le]
  simp only [one_div]
  congr 1
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

private lemma pe8m_xdiff (s ϖ σ τ σ' τ' a d : ℝ) (hs : 0 ≤ s)
    (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1) (hσ0 : 0 ≤ σ) (hτ0 : 0 ≤ τ)
    (hσ'0 : 0 ≤ σ') (hτ'0 : 0 ≤ τ') (hσ : σ ≤ a) (hτ : τ ≤ a)
    (hσ' : σ' ≤ a) (hτ' : τ' ≤ a) (hdσ : |σ - σ'| ≤ d)
    (hdτ : |τ - τ'| ≤ d) :
    |ϖ ^ 2 * s * σ * τ - ϖ ^ 2 * s * σ' * τ'| ≤ 2 * s * a * d := by
  have ha : 0 ≤ a := hσ0.trans hσ
  have hd : 0 ≤ d := (abs_nonneg _).trans hdσ
  have hw : ϖ ^ 2 ≤ 1 := by nlinarith
  have he : ϖ ^ 2 * s * σ * τ - ϖ ^ 2 * s * σ' * τ' =
      ϖ ^ 2 * s * ((σ - σ') * τ + σ' * (τ - τ')) := by ring
  rw [he, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ϖ), abs_of_nonneg hs]
  calc
    ϖ ^ 2 * s * |(σ - σ') * τ + σ' * (τ - τ')|
        ≤ ϖ ^ 2 * s * (|σ - σ'| * τ + σ' * |τ - τ'|) := by
          gcongr
          exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul, abs_of_nonneg hτ0,
            abs_of_nonneg hσ'0])
    _ ≤ 1 * s * (d * a + a * d) := by gcongr
    _ = 2 * s * a * d := by ring

private lemma pe8m_Fdiff (s b b' σ τ σ' τ' A D A' D' a d p e db : ℝ)
    (hs : 0 ≤ s) (hb : |b| ≤ 2) (hb' : |b'| ≤ 2) (hbd : |b - b'| ≤ db)
    (hσ0 : 0 ≤ σ) (hτ0 : 0 ≤ τ) (hσ'0 : 0 ≤ σ') (hτ'0 : 0 ≤ τ')
    (hσ : σ ≤ a) (hτ : τ ≤ a) (hσ' : σ' ≤ a) (hτ' : τ' ≤ a)
    (hdσ : |σ - σ'| ≤ d) (hdτ : |τ - τ'| ≤ d)
    (hA : |A| ≤ p) (hD : |D| ≤ p) (hA' : |A'| ≤ p) (hD' : |D'| ≤ p)
    (hdA : |A - A'| ≤ e) (hdD : |D - D'| ≤ e) :
    |s * b * (τ * A + σ * D) - s * b' * (τ' * A' + σ' * D')| ≤
      s * (db * (2 * a * p) + 2 * (2 * (d * p + a * e))) := by
  have ha : 0 ≤ a := hσ0.trans hσ
  have hd : 0 ≤ d := (abs_nonneg _).trans hdσ
  have hp : 0 ≤ p := (abs_nonneg _).trans hA
  have he0 : 0 ≤ e := (abs_nonneg _).trans hdA
  have hdb : 0 ≤ db := (abs_nonneg _).trans hbd
  have hq : |τ * A + σ * D| ≤ 2 * a * p := by
    calc
      |τ * A + σ * D| ≤ τ * |A| + σ * |D| := by
        exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul, abs_of_nonneg hτ0,
          abs_of_nonneg hσ0])
      _ ≤ a * p + a * p := by gcongr
      _ = 2 * a * p := by ring
  have hqd : |(τ * A + σ * D) - (τ' * A' + σ' * D')| ≤
      2 * (d * p + a * e) := by
    have h1 : |τ * A - τ' * A'| ≤ d * p + a * e := by
      have heq : τ * A - τ' * A' = (τ - τ') * A + τ' * (A - A') := by ring
      rw [heq]
      calc
        |(τ - τ') * A + τ' * (A - A')| ≤ |τ - τ'| * |A| + τ' * |A - A'| := by
          exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul, abs_of_nonneg hτ'0])
        _ ≤ d * p + a * e := by gcongr
    have h2 : |σ * D - σ' * D'| ≤ d * p + a * e := by
      have heq : σ * D - σ' * D' = (σ - σ') * D + σ' * (D - D') := by ring
      rw [heq]
      calc
        |(σ - σ') * D + σ' * (D - D')| ≤ |σ - σ'| * |D| + σ' * |D - D'| := by
          exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul, abs_of_nonneg hσ'0])
        _ ≤ d * p + a * e := by gcongr
    have heq : (τ * A + σ * D) - (τ' * A' + σ' * D') =
        (τ * A - τ' * A') + (σ * D - σ' * D') := by ring
    rw [heq]
    exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  have heq : s * b * (τ * A + σ * D) - s * b' * (τ' * A' + σ' * D') =
      s * ((b - b') * (τ * A + σ * D) +
        b' * ((τ * A + σ * D) - (τ' * A' + σ' * D'))) := by ring
  rw [heq, abs_mul, abs_of_nonneg hs]
  calc
    s * |(b - b') * (τ * A + σ * D) +
        b' * ((τ * A + σ * D) - (τ' * A' + σ' * D'))|
        ≤ s * (|b - b'| * |τ * A + σ * D| +
          |b'| * |(τ * A + σ * D) - (τ' * A' + σ' * D')|) := by
            apply mul_le_mul_of_nonneg_left _ hs
            exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])
    _ ≤ s * (db * (2 * a * p) + 2 * (2 * (d * p + a * e))) := by gcongr

/-- `lem:app-dyn-minor`, snapshot `cr-2026-10-23`. Statement verbatim from `section.tex` (ll. 1317–1326):
```latex
\begin{lemma}[The scalar of the minor]\label{lem:app-dyn-minor}
Let $s\ge s_\circ>0$, $\varpi\in[0,1]$, and let $F_s(T)$ be defined by
\cref{eqn:app-dyn-F} for an arbitrary real matrix $T$, with its own traces.
Then
\[
\abs{F_s(T)}\le C\sqrt B\,s^{-3/2},\qquad
\abs{F_s(T)-F_s(T')}\le C s^{-2}\big(\pi_\Pi+B^{-1/2}\big)\norm{T-T'}_*,
\]
with $C$ depending only on $(s_\circ,c_\Pi,\gamma_\star,C_\Sigma)$.
\end{lemma}
```
-/
theorem lem_app_dyn_minor (cP γ CS s0 : ℝ) (hs0 : 0 < s0) :
    ∃ C : ℝ, ∀ (m n B : ℕ) (Cv : Covariances m n) (Ah Pt T T' : Mat m n) (ϖ s piT : ℝ),
      0 < B → opNorm Cv.Sout ≤ CS → opNorm Cv.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      fro Ah = 1 → IsTest cP piT Pt → ϖ ∈ Icc (0 : ℝ) 1 → s0 ≤ s →
      (∀ x : ℝ, 0 ≤ x →
        Integrable (fun z : Vec m × Vec n => iteratedDeriv 2 (psiX x) (resid Ah z))
          (gaussPair m n)) ∧
      |Fs Cv B Ah Pt ϖ s T| ≤ C * Real.sqrt B * s ^ (-(3 / 2 : ℝ)) ∧
      |Fs Cv B Ah Pt ϖ s T - Fs Cv B Ah Pt ϖ s T'|
        ≤ C * (1 / s ^ 2) * (piT + (B : ℝ) ^ (-(1 / 2 : ℝ))) * nuc (T - T') := by
  let C : ℝ := 2 * γ * cP * CS ^ 2 * Real.sqrt γ + 8 * γ * CS ^ 2 +
    4 * cP * Real.sqrt γ * CS ^ 2 + 48 * γ ^ 2 * cP * Real.sqrt γ * CS ^ 4 / s0
  refine ⟨C, ?_⟩
  intro m n B Cv Ah Pt T T' ϖ s piT hB hCo hCi hm hn hA hTest hϖ hs
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hBsqrt : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBr
  have hnpos : 0 < n := by
    by_contra h
    push_neg at h
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero h
    subst n
    simp [fro] at hA
  have hncast : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hγ : 0 < γ := by
    have : (0 : ℝ) < γ * B := lt_of_lt_of_le hncast hn
    rcases (mul_pos_iff.mp this) with h | h
    · exact h.1
    · exfalso; linarith
  have hCS : 0 ≤ CS := (pe8_opNorm_nonneg Cv.Sout).trans hCo
  obtain ⟨hPf, hPo, hpic⟩ := hTest
  have hcP : 0 ≤ cP := (Real.sqrt_nonneg _).trans hPf
  have hpi : 0 ≤ piT := (pe8_opNorm_nonneg Pt).trans hPo
  obtain ⟨hϖ0, hϖ1⟩ := hϖ
  have hrootn : Real.sqrt n ≤ Real.sqrt γ * Real.sqrt B := by
    calc
      Real.sqrt n ≤ Real.sqrt (γ * B) := Real.sqrt_le_sqrt hn
      _ = Real.sqrt γ * Real.sqrt B := Real.sqrt_mul hγ.le _
  have hsigT := pe8m_sigma_upper Cv B hB T s hspos CS γ hCo hCi hm hn
  have hsigT' := pe8m_sigma_upper Cv B hB T' s hspos CS γ hCo hCi hm hn
  have hσ0 := pe8_sigmaS_nonneg Cv B hB T s hspos
  have hτ0 := pe8_sigmaT_nonneg Cv B hB T s hspos
  have hσ'0 := pe8_sigmaS_nonneg Cv B hB T' s hspos
  have hτ'0 := pe8_sigmaT_nonneg Cv B hB T' s hspos
  let a : ℝ := γ * CS / s
  let d : ℝ := 2 * CS / ((B : ℝ) * s * Real.sqrt s) * nuc (T - T')
  let p0 : ℝ := cP * (Real.sqrt γ * Real.sqrt B) * CS / (2 * s * Real.sqrt s)
  let e : ℝ := piT * (2 * CS / s ^ 2 * nuc (T - T'))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hd : 0 ≤ d := by
    dsimp [d]
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hCS) (by positivity)) (nuc_nonneg _)
  have hp0 : 0 ≤ p0 := by dsimp [p0]; positivity
  have he0 : 0 ≤ e := by
    dsimp [e]
    exact mul_nonneg hpi (mul_nonneg (by positivity) (nuc_nonneg _))
  have hpair (U : Mat m n) :
      |frobIP Pt (Rs U s * Cv.Sout * Xs U s)| ≤ p0 ∧
      |frobIP Pt (Xs U s * Cv.Sin * Rts U s)| ≤ p0 := by
    obtain ⟨h1, h2⟩ := pe8m_pair_upper Cv Pt U s CS cP hspos hCo hCi hPf
    constructor
    · refine h1.trans ?_
      dsimp [p0]
      calc
        cP * (Real.sqrt n * (1 / s * CS * (1 / (2 * Real.sqrt s))))
            ≤ cP * ((Real.sqrt γ * Real.sqrt B) *
              (1 / s * CS * (1 / (2 * Real.sqrt s)))) := by gcongr
        _ = cP * (Real.sqrt γ * Real.sqrt B) * CS / (2 * s * Real.sqrt s) := by ring
    · refine h2.trans ?_
      dsimp [p0]
      calc
        cP * (Real.sqrt n * (1 / (2 * Real.sqrt s) * CS * (1 / s)))
            ≤ cP * ((Real.sqrt γ * Real.sqrt B) *
              (1 / (2 * Real.sqrt s) * CS * (1 / s))) := by gcongr
        _ = cP * (Real.sqrt γ * Real.sqrt B) * CS / (2 * s * Real.sqrt s) := by ring
  obtain ⟨hA1, hD1⟩ := hpair T
  obtain ⟨hA1', hD1'⟩ := hpair T'
  have hpd := pe8m_pair_diff Cv Pt T T' s CS piT hspos hCo hCi hPo
  have hsd := pe8m_sigma_diff Cv B hB T T' s hspos CS hCo hCi
  have hsigTa : sigmaS Cv B T s ≤ a ∧ sigmaT Cv B T s ≤ a := by simpa [a] using hsigT
  have hsigT'a : sigmaS Cv B T' s ≤ a ∧ sigmaT Cv B T' s ≤ a := by simpa [a] using hsigT'
  have hxd : |xMinor Cv B T ϖ s - xMinor Cv B T' ϖ s| ≤
      2 * s * a * d := by
    unfold xMinor
    exact pe8m_xdiff s ϖ (sigmaS Cv B T s) (sigmaT Cv B T s)
      (sigmaS Cv B T' s) (sigmaT Cv B T' s) a d hspos.le hϖ0 hϖ1
      hσ0 hτ0 hσ'0 hτ'0 hsigTa.1 hsigTa.2 hsigT'a.1 hsigT'a.2 hsd.1 hsd.2
  have hx0 : 0 ≤ xMinor Cv B T ϖ s := by unfold xMinor; positivity
  have hx0' : 0 ≤ xMinor Cv B T' ϖ s := by unfold xMinor; positivity
  have hraw := lem_app_dyn_raw Ah hA
  have hb := hraw.2.1 (xMinor Cv B T ϖ s) hx0
  have hb' := hraw.2.1 (xMinor Cv B T' ϖ s) hx0'
  have hbd : |bFun Ah (xMinor Cv B T ϖ s) - bFun Ah (xMinor Cv B T' ϖ s)| ≤
      12 * (2 * s * a * d) :=
    (hraw.2.2.1 _ _ hx0 hx0').trans (mul_le_mul_of_nonneg_left hxd (by norm_num))
  refine ⟨fun x hx => (hraw.1 x hx).1, ?_, ?_⟩
  · unfold Fs
    rw [abs_mul, abs_mul, abs_of_pos hspos]
    have hq : |sigmaT Cv B T s * frobIP Pt (Rs T s * Cv.Sout * Xs T s) +
        sigmaS Cv B T s * frobIP Pt (Xs T s * Cv.Sin * Rts T s)| ≤ 2 * a * p0 := by
      calc
        _ ≤ sigmaT Cv B T s * |frobIP Pt (Rs T s * Cv.Sout * Xs T s)| +
            sigmaS Cv B T s * |frobIP Pt (Xs T s * Cv.Sin * Rts T s)| := by
          exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul, abs_of_nonneg hτ0,
            abs_of_nonneg hσ0])
        _ ≤ a * p0 + a * p0 := by
          exact add_le_add (mul_le_mul hsigTa.2 hA1 (abs_nonneg _) ha)
            (mul_le_mul hsigTa.1 hD1 (abs_nonneg _) ha)
        _ = 2 * a * p0 := by ring
    calc
      s * |bFun Ah (xMinor Cv B T ϖ s)| *
          |sigmaT Cv B T s * frobIP Pt (Rs T s * Cv.Sout * Xs T s) +
            sigmaS Cv B T s * frobIP Pt (Xs T s * Cv.Sin * Rts T s)|
          ≤ s * 2 * (2 * a * p0) := by gcongr
      _ = (2 * γ * cP * CS ^ 2 * Real.sqrt γ) * Real.sqrt B /
          (s * Real.sqrt s) := by
        dsimp [a, p0]
        field_simp [hspos.ne', hsqrt.ne']
      _ ≤ C * Real.sqrt B / (s * Real.sqrt s) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        dsimp [C]
        have h1 : 0 ≤ 8 * γ * CS ^ 2 := by positivity
        have h2 : 0 ≤ 4 * cP * Real.sqrt γ * CS ^ 2 := by positivity
        have h3 : 0 ≤ 48 * γ ^ 2 * cP * Real.sqrt γ * CS ^ 4 / s0 := by positivity
        linarith
      _ = C * Real.sqrt B * s ^ (-(3 / 2 : ℝ)) := by
        rw [pe8m_rpow_mthreehalf s hspos]
        ring
  · have hmain := pe8m_Fdiff s
      (bFun Ah (xMinor Cv B T ϖ s)) (bFun Ah (xMinor Cv B T' ϖ s))
      (sigmaS Cv B T s) (sigmaT Cv B T s) (sigmaS Cv B T' s) (sigmaT Cv B T' s)
      (frobIP Pt (Rs T s * Cv.Sout * Xs T s))
      (frobIP Pt (Xs T s * Cv.Sin * Rts T s))
      (frobIP Pt (Rs T' s * Cv.Sout * Xs T' s))
      (frobIP Pt (Xs T' s * Cv.Sin * Rts T' s)) a d p0 e (12 * (2 * s * a * d))
      hspos.le hb hb' hbd hσ0 hτ0 hσ'0 hτ'0 hsigTa.1 hsigTa.2 hsigT'a.1 hsigT'a.2
      hsd.1 hsd.2 hA1 hD1 hA1' hD1' hpd.1 hpd.2
    unfold Fs
    refine hmain.trans ?_
    rw [pe8m_rpow_mhalf B hBr]
    let k1 : ℝ := 48 * γ ^ 2 * cP * Real.sqrt γ * CS ^ 4
    let k2 : ℝ := 4 * cP * Real.sqrt γ * CS ^ 2
    let k3 : ℝ := 8 * γ * CS ^ 2
    have hk1 : 0 ≤ k1 := by dsimp [k1]; positivity
    have hk2 : 0 ≤ k2 := by dsimp [k2]; positivity
    have hk3 : 0 ≤ k3 := by dsimp [k3]; positivity
    have hq : 1 / s ≤ 1 / s0 := one_div_le_one_div_of_le hs0 hs
    have hform :
        s * (12 * (2 * s * a * d) * (2 * a * p0) +
          2 * (2 * (d * p0 + a * e))) =
        (k1 * (1 / s) ^ 3 * (1 / Real.sqrt B) +
          k2 * (1 / s) ^ 2 * (1 / Real.sqrt B) +
          k3 * (1 / s) ^ 2 * piT) * nuc (T - T') := by
      dsimp [a, d, p0, e, k1, k2, k3]
      field_simp [hspos.ne', hsqrt.ne', hBr.ne', hBsqrt.ne']
      ring_nf
      rw [Real.sq_sqrt hBr.le, Real.sq_sqrt hspos.le]
      ring
    rw [hform]
    have ht1 : k1 * (1 / s) ^ 3 * (1 / Real.sqrt B) ≤
        (k1 / s0) * (1 / s) ^ 2 * (1 / Real.sqrt B) := by
      calc
        k1 * (1 / s) ^ 3 * (1 / Real.sqrt B) =
            (k1 * (1 / s) ^ 2 * (1 / Real.sqrt B)) * (1 / s) := by ring
        _ ≤ (k1 * (1 / s) ^ 2 * (1 / Real.sqrt B)) * (1 / s0) := by gcongr
        _ = (k1 / s0) * (1 / s) ^ 2 * (1 / Real.sqrt B) := by ring
    have hC1 : k1 / s0 + k2 ≤ C := by
      dsimp [C, k1, k2, k3]
      have h0 : 0 ≤ 2 * γ * cP * CS ^ 2 * Real.sqrt γ := by positivity
      have h3 : 0 ≤ 8 * γ * CS ^ 2 := by positivity
      linarith
    have hC3 : k3 ≤ C := by
      dsimp [C, k1, k2, k3]
      have h0 : 0 ≤ 2 * γ * cP * CS ^ 2 * Real.sqrt γ := by positivity
      have h2 : 0 ≤ 4 * cP * Real.sqrt γ * CS ^ 2 := by positivity
      have h1 : 0 ≤ 48 * γ ^ 2 * cP * Real.sqrt γ * CS ^ 4 / s0 := by positivity
      linarith
    have hcoef :
        k1 * (1 / s) ^ 3 * (1 / Real.sqrt B) +
            k2 * (1 / s) ^ 2 * (1 / Real.sqrt B) +
            k3 * (1 / s) ^ 2 * piT ≤
          C * (1 / s) ^ 2 * (piT + 1 / Real.sqrt B) := by
      calc
        _ ≤ (k1 / s0) * (1 / s) ^ 2 * (1 / Real.sqrt B) +
            k2 * (1 / s) ^ 2 * (1 / Real.sqrt B) +
            k3 * (1 / s) ^ 2 * piT := by linarith
        _ = (k1 / s0 + k2) * (1 / s) ^ 2 * (1 / Real.sqrt B) +
            k3 * (1 / s) ^ 2 * piT := by ring
        _ ≤ C * (1 / s) ^ 2 * (1 / Real.sqrt B) +
            C * (1 / s) ^ 2 * piT := by gcongr
        _ = C * (1 / s) ^ 2 * (piT + 1 / Real.sqrt B) := by ring
    calc
      _ ≤ (C * (1 / s) ^ 2 * (piT + 1 / Real.sqrt B)) * nuc (T - T') :=
        mul_le_mul_of_nonneg_right hcoef (nuc_nonneg _)
      _ = C * (1 / s ^ 2) * (piT + 1 / Real.sqrt B) * nuc (T - T') := by ring

private lemma pe8t_normChainPath_aemeasurable {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (p : DynParams) (Cv : Covariances m n) (cs : ChainSamples P m n B)
    (t : ℕ) (D : Mat m n) (hD : 0 < riskSigma Cv D)
    (hsize : Muon.Volatility.SizeFin Cv B p.γstar p.CSig) :
    AEMeasurable (fun ω => normChainPath p Cv cs t D 0 ω) P := by
  have hsum := (lem_app_dyn_chains_iii p Cv cs t D 0 hD hsize).1
  apply AEMeasurable.of_eval
  intro q
  have hstat : AEStronglyMeasurable
      (fun ω => (def_app_dyn_chains p Cv cs t D 0 ω).stat q) P := by
    induction q with
    | zero =>
        refine aestronglyMeasurable_of_tendsto_ae atTop
          (f := fun N ω => ∑ j ∈ Finset.range N,
            emaW p.β j • batchGrad D (physBatch Cv (cs.aux (t : ℤ) j) ω)) (fun N => ?_) ?_
        · refine (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ => ?_).aestronglyMeasurable
          have hc : Continuous (fun z : Fin B → Vec m × Vec n =>
              batchGrad D (fun a => phys Cv (z a))) := by
            unfold batchGrad Muon.Setup.grad resid phys outer
            fun_prop
          exact (hc.measurable.comp (Measurable.of_eval fun a =>
            cs.meas_aux (t : ℤ) j a)).stronglyMeasurable.const_smul (emaW p.β j)
        · filter_upwards [hsum] with ω hω
          exact hω.hasSum.tendsto_sum_nat
    | succ q ih =>
        simp only [def_app_dyn_chains, emaChain]
        have hc : Continuous (fun z : Fin B → Vec m × Vec n =>
            batchGrad D (fun a => phys Cv (z a))) := by
          unfold batchGrad Muon.Setup.grad resid phys outer
          fun_prop
        refine (ih.const_smul p.β).add ?_
        exact (hc.measurable.comp (Measurable.of_eval fun a =>
          cs.meas_act ((t : ℤ) + q + 1) a)).stronglyMeasurable.aestronglyMeasurable.const_smul
            (1 - p.β)
  exact (hstat.const_smul ((Real.sqrt (2 * riskSigma Cv D))⁻¹)).aemeasurable

private lemma pe8t_measurable_ridgeDeriv {m n : ℕ} (ϱ : ℝ) (hϱ : 0 < ϱ) :
    Measurable (ridgeDeriv ϱ : Mat m n → Mat m n) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  let f : Mat m n → ℝ → ℝ := fun K x => Q (max x (ϱ / 2)) K i j
  have hc : 0 < ϱ / 2 := by linarith
  have hf : Continuous (Function.uncurry f) := by
    have hΦ := (Q_contDiffOn_pos m n).continuousOn
    have h1 : Continuous (fun q : Mat m n × ℝ =>
        ((q.1 : Fin m → Fin n → ℝ), max q.2 (ϱ / 2))) := by fun_prop
    have h2 := hΦ.comp_continuous h1
      (fun q => show (0 : ℝ) < max q.2 (ϱ / 2) from
        lt_of_lt_of_le hc (le_max_right _ _))
    exact (continuous_apply j).comp ((continuous_apply i).comp h2)
  have hd : Measurable (fun K : Mat m n => deriv (f K) ϱ) :=
    (measurable_deriv_with_param hf).comp (measurable_id.prodMk measurable_const)
  convert hd using 1
  funext K
  change deriv (fun x : ℝ => Q x K i j) ϱ = deriv (f K) ϱ
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds (show ϱ / 2 < ϱ by linarith)] with x hx
  have hx' : ϱ / 2 < x := hx
  simp [f, max_eq_left hx'.le]

/-- The finite-model part of `eqn_app_dyn_mean_physical`, without a proportional-regime
asymptotic: both stationary means are uniformly bounded in Frobenius norm. -/
private lemma eqn_app_dyn_mean_physical_fin (γ CS ϱ : ℝ) :
    ∃ C : ℝ, ∀ (p : DynParams), p.γstar = γ → p.CSig = CS → p.ϱ = ϱ →
      ∀ (m n B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (Cv : Covariances m n) (cs : ChainSamples P m n B)
      (t k r : ℕ) (D : Mat m n),
      ((max m n : ℕ) : ℝ) ≤ p.γstar * B →
      opNorm Cv.Sout ≤ p.CSig → opNorm Cv.Sin ≤ p.CSig → 0 < B →
      riskSigma Cv D = 1 / 2 →
      fro (mean P (stationaryV p Cv cs t D k)) ≤ C ∧
      fro (mean P (fun ω => ridgeDeriv p.ϱ (stationaryN p Cv cs t D r ω))) ≤ C := by
  by_cases hϱ : 0 < ϱ
  · obtain ⟨C, hC⟩ := lem_app_dyn_mean_iii_ema γ CS ϱ ϱ hϱ le_rfl
    refine ⟨max C 0, ?_⟩
    intro p hpγ hpCS hpϱ m n B Ω _ P _ Cv cs t k r D hdim hCo hCi hB hD
    have hDp : 0 < riskSigma Cv D := by rw [hD]; norm_num
    have hsize : Muon.Volatility.SizeFin Cv B p.γstar p.CSig :=
      ⟨by simpa [Nat.cast_max] using hdim, hCo, hCi⟩
    let F : FrozenParams m n B :=
      { C := Cv
        A := Ahat Cv D
        hA := pe8q_Ahat_fro Cv D hDp
        β := p.β
        hβ := p.hβ
        hB := hB }
    let S : FrozenSamples P m n B :=
      { zw := cs.act
        meas := cs.meas_act
        indep := cs.indep.precomp Sum.inl_injective
        law := cs.law_act }
    have hlaw := lem_app_dyn_chains_i p Cv cs t D 0 hDp F rfl rfl rfl S
    have hpath := pe8t_normChainPath_aemeasurable p Cv cs t D hDp hsize
    have hbuf : AEMeasurable
        (fun ω (q : ℕ) => frozenBuf F S ((t : ℤ) + (q : ℤ) - 1) ω) P := by
      apply AEMeasurable.of_eval
      intro q
      exact (lem_app_setup_ema_law_ii F S).2.1.eval ((t : ℤ) + (q : ℤ) - 1)
    have hQm : Measurable (fun K : Mat m n => Q p.ϱ K) := by
      have hp : 0 ≤ p.ϱ := p.hϱ.le
      exact measurable_Q.comp
        ((measurable_const (a := (⟨p.ϱ, hp⟩ : Ici (0 : ℝ)))).prodMk measurable_id)
    have hVpath : AEMeasurable
        (fun ω (q : ℕ) => (def_app_dyn_chains p Cv cs t D 0 ω).statV q) P := by
      have heq : (fun ω (q : ℕ) => (def_app_dyn_chains p Cv cs t D 0 ω).statV q) =
          (fun y : ℕ → Mat m n => fun q => Q p.ϱ (y q)) ∘
            (fun ω => normChainPath p Cv cs t D 0 ω) := by
        funext ω q
        simp only [Function.comp_apply, normChainPath, def_app_dyn_chains, physRidge, hD]
        norm_num
      rw [heq]
      exact (Measurable.of_eval fun q => hQm.comp (measurable_pi_apply q)).comp_aemeasurable hpath
    have hFVpath : AEMeasurable
        (fun ω (q : ℕ) => frozenUpd F S p.ϱ ((t : ℤ) + (q : ℤ) - 1) ω) P := by
      exact (Measurable.of_eval fun q => hQm.comp (measurable_pi_apply q)).comp_aemeasurable hbuf
    have hmeanV : mean P (stationaryV p Cv cs t D k) =
        mean P (fun ω => Q p.ϱ (frozenBuf F S ((t : ℤ) + (k : ℤ)) ω)) := by
      ext i j
      simp only [mean, Matrix.of_apply]
      have he : Measurable (fun y : ℕ → Mat m n => y (k + 1) i j) :=
        (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_pi_apply (k + 1)))
      have e1 := integral_map hVpath he.aestronglyMeasurable
      have e2 := integral_map hFVpath he.aestronglyMeasurable
      rw [hlaw.2.2.1] at e1
      have e3 := e1.symm.trans e2
      have ht : (t : ℤ) + ((k + 1 : ℕ) : ℤ) - 1 = (t : ℤ) + k := by push_cast; ring
      simpa only [stationaryV, ht, frozenUpd] using e3
    have hRD : Measurable (ridgeDeriv p.ϱ : Mat m n → Mat m n) :=
      pe8t_measurable_ridgeDeriv p.ϱ p.hϱ
    have hmeanR : mean P (fun ω => ridgeDeriv p.ϱ (stationaryN p Cv cs t D r ω)) =
        mean P (fun ω => dQ p.ϱ (frozenBuf F S ((t : ℤ) + (r : ℤ)) ω)) := by
      ext i j
      simp only [mean, Matrix.of_apply]
      have he : Measurable (fun y : ℕ → Mat m n => ridgeDeriv p.ϱ (y (r + 1)) i j) :=
        (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
          (hRD.comp (measurable_pi_apply (r + 1))))
      have e1 := integral_map hpath he.aestronglyMeasurable
      have e2 := integral_map hbuf he.aestronglyMeasurable
      rw [hlaw.2.1] at e1
      have e3 := e1.symm.trans e2
      have ht : (t : ℤ) + ((r + 1 : ℕ) : ℤ) - 1 = (t : ℤ) + r := by push_cast; ring
      simpa [normChainPath, stationaryN, hD, dQ, ridgeDeriv, Nat.cast_add,
        Nat.cast_one, add_sub_assoc] using e3
    have hbV := (hC m n B Ω P S F ((t : ℤ) + (k : ℤ))
      (by simpa [← hpγ] using hdim) (by simpa [← hpCS] using hCo)
      (by simpa [← hpCS] using hCi)).2.2.2 p.ϱ ⟨by simp [hpϱ], by simp [hpϱ]⟩
    have hbR := (hC m n B Ω P S F ((t : ℤ) + (r : ℤ))
      (by simpa [← hpγ] using hdim) (by simpa [← hpCS] using hCo)
      (by simpa [← hpCS] using hCi)).2.2.2 p.ϱ ⟨by simp [hpϱ], by simp [hpϱ]⟩
    constructor
    · rw [hmeanV]
      exact (le_add_of_nonneg_right (pe8s_fro_nonneg _)).trans (hbV.trans (le_max_left _ _))
    · rw [hmeanR]
      exact (le_add_of_nonneg_left (pe8s_fro_nonneg _)).trans (hbR.trans (le_max_left _ _))
  · refine ⟨0, ?_⟩
    intro p _ _ hpϱ
    have : 0 < ϱ := hpϱ ▸ p.hϱ
    exact (hϱ this).elim

/-- Moving a sample back by `d` steps multiplies its EMA weight by `β ^ d`. -/
private lemma pe8t_emaW_add (β : ℝ) (v d : ℕ) :
    emaW β (v + d) = β ^ d * emaW β v := by
  simp only [emaW, pow_add]
  ring

/-- The overlap of two stationary EMA histories, in the nonnegative extended reals
used by the countable-coordinate covariance inequality. -/
private lemma pe8t_ema_overlap (p : DynParams) (d : ℕ) :
    (∑' v : ℕ, ENNReal.ofReal (emaW p.β v) *
      ENNReal.ofReal (emaW p.β (v + d))) ≤ ENNReal.ofReal (p.β ^ d) := by
  have hw : ∀ v, 0 ≤ emaW p.β v := fun v => (pe8q_emaW_mem_Icc p v).1
  have hsum : Summable (emaW p.β) :=
    (summable_geometric_of_lt_one p.hβ.1 p.hβ.2).mul_left (1 - p.β)
  have hmass : ∑' v : ℕ, ENNReal.ofReal (emaW p.β v) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hw hsum, tsum_emaW p.hβ.1 p.hβ.2]
    simp
  calc
    (∑' v : ℕ, ENNReal.ofReal (emaW p.β v) *
        ENNReal.ofReal (emaW p.β (v + d)))
        ≤ ∑' v : ℕ, ENNReal.ofReal (p.β ^ d) * ENNReal.ofReal (emaW p.β v) := by
      apply ENNReal.tsum_le_tsum
      intro v
      rw [← ENNReal.ofReal_mul (hw v), ← ENNReal.ofReal_mul (pow_nonneg p.hβ.1 d)]
      apply ENNReal.ofReal_le_ofReal
      rw [pe8t_emaW_add]
      calc
        emaW p.β v * (p.β ^ d * emaW p.β v)
            ≤ 1 * (p.β ^ d * emaW p.β v) :=
          mul_le_mul_of_nonneg_right (pe8q_emaW_mem_Icc p v).2
            (mul_nonneg (pow_nonneg p.hβ.1 d) (hw v))
        _ = _ := one_mul _
    _ = ENNReal.ofReal (p.β ^ d) := by rw [ENNReal.tsum_mul_left, hmass, mul_one]

/-- Each age contains exactly `B` independent sample coordinates. -/
private lemma pe8t_ema_overlap_batch (p : DynParams) (B d : ℕ) :
    (∑' v : ℕ × Fin B, ENNReal.ofReal (emaW p.β v.1) *
      ENNReal.ofReal (emaW p.β (v.1 + d))) ≤
        (B : ℝ≥0∞) * ENNReal.ofReal (p.β ^ d) := by
  rw [ENNReal.tsum_prod (f := fun (v : ℕ) (_ : Fin B) =>
    ENNReal.ofReal (emaW p.β v) * ENNReal.ofReal (emaW p.β (v + d)))]
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ENNReal.tsum_mul_left]
  exact mul_le_mul_right (pe8t_ema_overlap p d) _

/-- The finite actual history and the infinite auxiliary history together form
one stationary EMA overlap. -/
private lemma pe8t_ema_overlap_split (p : DynParams) (k r : ℕ) (hkr : k ≤ r) :
    (∑ v ∈ Finset.range (k + 1), ENNReal.ofReal (emaW p.β (k - v)) *
      ENNReal.ofReal (emaW p.β (r - v))) +
    (∑' v : ℕ, ENNReal.ofReal (emaW p.β (v + k + 1)) *
      ENNReal.ofReal (emaW p.β (v + r + 1))) ≤
      ENNReal.ofReal (p.β ^ (r - k)) := by
  let f : ℕ → ℝ≥0∞ := fun v => ENNReal.ofReal (emaW p.β v) *
    ENNReal.ofReal (emaW p.β (v + (r - k)))
  have hfinite : (∑ v ∈ Finset.range (k + 1),
      ENNReal.ofReal (emaW p.β (k - v)) * ENNReal.ofReal (emaW p.β (r - v))) =
      ∑ v ∈ Finset.range (k + 1), f v := by
    rw [← Finset.sum_range_reflect f (k + 1)]
    apply Finset.sum_congr rfl
    intro v hv
    have hv' := Finset.mem_range.mp hv
    have h1 : k + 1 - 1 - v = k - v := by omega
    have h2 : k - v + (r - k) = r - v := by omega
    simp only [f, h1, h2]
  have hinfinite : (∑' v : ℕ, ENNReal.ofReal (emaW p.β (v + k + 1)) *
      ENNReal.ofReal (emaW p.β (v + r + 1))) = ∑' v : ℕ, f (v + (k + 1)) := by
    apply tsum_congr
    intro v
    have h : v + (k + 1) + (r - k) = v + r + 1 := by omega
    simp only [f, h, Nat.add_assoc]
  rw [hfinite, hinfinite, ENNReal.summable.sum_add_tsum_nat_add' (f := f) (k := k + 1)]
  exact pe8t_ema_overlap p (r - k)

/-- The overlap estimate in exactly the coordinate indexing used by the
covariance inequality, including the finite actual and infinite auxiliary parts. -/
private lemma pe8t_causal_weight_overlap (p : DynParams) (B k r : ℕ)
    (e : ℕ ≃ ((ℕ × Fin B) ⊕ (ℕ × Fin B))) :
    let w : ℕ → ((ℕ × Fin B) ⊕ (ℕ × Fin B)) → ℝ := fun u =>
      Sum.elim (fun qa : ℕ × Fin B => if qa.1 ≤ u then emaW p.β (u - qa.1) else 0)
        (fun qa : ℕ × Fin B => emaW p.β (qa.1 + u + 1))
    (∑' l : ℕ, ENNReal.ofReal (w k (e l)) * ENNReal.ofReal (w r (e l))) ≤
      (B : ℝ≥0∞) * ENNReal.ofReal (p.β ^ Nat.dist r k) := by
  classical
  dsimp only
  let w : ℕ → ((ℕ × Fin B) ⊕ (ℕ × Fin B)) → ℝ := fun u =>
    Sum.elim (fun qa : ℕ × Fin B => if qa.1 ≤ u then emaW p.β (u - qa.1) else 0)
      (fun qa : ℕ × Fin B => emaW p.β (qa.1 + u + 1))
  change (∑' l, ENNReal.ofReal (w k (e l)) * ENNReal.ofReal (w r (e l))) ≤ _
  have hord : ∀ u v : ℕ, u ≤ v →
      (∑' q, ENNReal.ofReal (w u q) * ENNReal.ofReal (w v q)) ≤
        (B : ℝ≥0∞) * ENNReal.ofReal (p.β ^ (v - u)) := by
    intro u v huv
    have hhead : (∑' q : ℕ × Fin B,
        ENNReal.ofReal (w u (Sum.inl q)) * ENNReal.ofReal (w v (Sum.inl q))) =
        (B : ℝ≥0∞) * ∑ i ∈ Finset.range (u + 1),
          ENNReal.ofReal (emaW p.β (u - i)) * ENNReal.ofReal (emaW p.β (v - i)) := by
      rw [ENNReal.tsum_prod']
      simp only [w, Sum.elim_inl, tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.tsum_mul_left]
      congr 1
      rw [tsum_eq_sum (s := Finset.range (u + 1)) (fun i hi => by
        have hni : ¬ i ≤ u := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
        simp [hni])]
      apply Finset.sum_congr rfl
      intro i hi
      have hiu : i ≤ u := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      simp [hiu, hiu.trans huv]
    have htail : (∑' q : ℕ × Fin B,
        ENNReal.ofReal (w u (Sum.inr q)) * ENNReal.ofReal (w v (Sum.inr q))) =
        (B : ℝ≥0∞) * ∑' i : ℕ,
          ENNReal.ofReal (emaW p.β (i + u + 1)) * ENNReal.ofReal (emaW p.β (i + v + 1)) := by
      rw [ENNReal.tsum_prod']
      simp only [w, Sum.elim_inr, tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.tsum_mul_left]
    rw [ENNReal.summable.tsum_sum ENNReal.summable, hhead, htail, ← mul_add]
    exact mul_le_mul_right (pe8t_ema_overlap_split p u v huv) _
  rw [e.tsum_eq (fun q => ENNReal.ofReal (w k q) * ENNReal.ofReal (w r q))]
  rcases le_total k r with hkr | hrk
  · simpa only [Nat.dist_eq_sub_of_le_right hkr] using hord k r hkr
  · have h := hord r k hrk
    simpa only [mul_comm, Nat.dist_eq_sub_of_le hrk] using h

/-- Enumerate the actual future and auxiliary past, reserving two unused auxiliary
families for the independent replacement coordinates. -/
private lemma pe8t_coordinates {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (cs : ChainSamples P m n B) (t : ℕ)
    (e : ℕ ≃ ((ℕ × Fin B) ⊕ (ℕ × Fin B))) :
    let ξ : ℕ → Ω → Vec m × Vec n := fun l =>
      Sum.elim (fun q : ℕ × Fin B => cs.act ((t : ℤ) + q.1 + 1) q.2)
        (fun q : ℕ × Fin B => cs.aux (t : ℤ) q.1 q.2) (e l)
    let ξ' : ℕ → Ω → Vec m × Vec n := fun l =>
      Sum.elim (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 1) q.1 q.2)
        (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 2) q.1 q.2) (e l)
    (∀ l, Measurable (ξ l)) ∧ (∀ l, Measurable (ξ' l)) ∧
      (∀ l, P.map (ξ' l) = P.map (ξ l)) ∧
      iIndepFun (Sum.elim ξ ξ' : ℕ ⊕ ℕ → Ω → Vec m × Vec n) P := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l
    rcases e l with q | q
    · exact cs.meas_act _ _
    · exact cs.meas_aux _ _ _
  · intro l
    rcases e l with q | q <;> exact cs.meas_aux _ _ _
  · intro l
    rcases e l with q | q
    · exact (cs.law_aux _ _ _).trans (cs.law_act _ _).symm
    · exact (cs.law_aux _ _ _).trans (cs.law_aux _ _ _).symm
  · let f : ((ℕ × Fin B) ⊕ (ℕ × Fin B)) ⊕ ((ℕ × Fin B) ⊕ (ℕ × Fin B)) →
        (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B) :=
      Sum.elim
        (Sum.elim (fun q => Sum.inl ((t : ℤ) + q.1 + 1, q.2))
          (fun q => Sum.inr ((t : ℤ), q.1, q.2)))
        (Sum.elim (fun q => Sum.inr ((t : ℤ) + 1, q.1, q.2))
          (fun q => Sum.inr ((t : ℤ) + 2, q.1, q.2)))
    have hf : Function.Injective f := by
      rintro ((⟨i, a⟩ | ⟨i, a⟩) | (⟨i, a⟩ | ⟨i, a⟩))
        ((⟨j, b⟩ | ⟨j, b⟩) | (⟨j, b⟩ | ⟨j, b⟩)) h
      all_goals simp only [f, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
        Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, Prod.mk.injEq] at h ⊢
      all_goals first | contradiction | omega | (rcases h with ⟨h1, h2⟩; constructor <;> omega)
    have he : Function.Injective (Sum.map e e) := (e.sumCongr e).injective
    have hi := cs.indep.precomp (hf.comp he)
    convert hi using 1
    funext l
    rcases l with l | l <;> cases heq : e l <;> simp [f, Function.comp_def, heq]

/-- An enumeration exists as soon as the batch is nonempty. -/
private lemma pe8t_coordinate_equiv (B : ℕ) (hB : 0 < B) :
    Nonempty (ℕ ≃ ((ℕ × Fin B) ⊕ (ℕ × Fin B))) := by
  letI : Nonempty (Fin B) := ⟨⟨0, hB⟩⟩
  infer_instance

/-- A measurable version of the stationary buffer as a function of the
countable sample coordinates. The formula holds on every summable history. -/
private lemma pe8t_chain_function {m n B : ℕ} (p : DynParams)
    (Cv : Covariances m n) (D : Mat m n)
    (e : ℕ ≃ ((ℕ × Fin B) ⊕ (ℕ × Fin B))) :
    ∃ N : ℕ → (ℕ → Vec m × Vec n) → Mat m n,
      (∀ r, Measurable (N r)) ∧
      ∀ r x,
        Summable (fun q : ℕ => emaW p.β q •
          batchGrad D (fun a => phys Cv (x (e.symm (Sum.inr (q, a)))))) →
        N r x = p.β ^ (r + 1) •
            (∑' q : ℕ, emaW p.β q •
              batchGrad D (fun a => phys Cv (x (e.symm (Sum.inr (q, a)))))) +
          ∑ i ∈ Finset.range (r + 1), emaW p.β (r - i) •
            batchGrad D (fun a => phys Cv (x (e.symm (Sum.inl (i, a))))) := by
  let g : (ℕ × Fin B) ⊕ (ℕ × Fin B) → (ℕ → Vec m × Vec n) → Vec m × Vec n :=
    fun q x => x (e.symm q)
  have hg : ∀ q, Measurable (g q) := fun q => measurable_pi_apply _
  have hc : Continuous (fun z : Fin B → Vec m × Vec n =>
      batchGrad D (fun a => phys Cv (z a))) := by
    unfold batchGrad Muon.Setup.grad resid phys outer
    fun_prop
  let H : ℕ → (ℕ → Vec m × Vec n) → Mat m n := fun q x =>
    emaW p.β q • batchGrad D (fun a => phys Cv (g (Sum.inr (q, a)) x))
  have hH : ∀ q, Measurable (H q) := by
    intro q
    exact (hc.measurable.comp (Measurable.of_eval fun a =>
      hg (Sum.inr (q, a)))).const_smul (emaW p.β q)
  let N0 : (ℕ → Vec m × Vec n) → Mat m n := fun x => Matrix.of fun i j =>
    limUnder atTop (fun L : ℕ => (∑ q ∈ Finset.range L, H q x) i j)
  have hN0 : Measurable N0 := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.limUnder
    intro L
    exact (((measurable_pi_apply j).comp (measurable_pi_apply i)).comp
      (Finset.measurable_sum (Finset.range L) fun q _ => hH q)).stronglyMeasurable
  let N : ℕ → (ℕ → Vec m × Vec n) → Mat m n := fun r x =>
    p.β ^ (r + 1) • N0 x + ∑ i ∈ Finset.range (r + 1),
      emaW p.β (r - i) • batchGrad D (fun a => phys Cv (g (Sum.inl (i, a)) x))
  refine ⟨N, ?_, ?_⟩
  · intro r
    dsimp only [N]
    refine (hN0.const_smul (p.β ^ (r + 1))).add
      (Finset.measurable_sum (Finset.range (r + 1)) fun i _ => ?_)
    exact (hc.measurable.comp (Measurable.of_eval fun a =>
      hg (Sum.inl (i, a)))).const_smul (emaW p.β (r - i))
  · intro r x hx
    have h0 : N0 x = ∑' q, H q x := by
      ext i j
      have hentry := Pi.summable.1 (Pi.summable.1 hx i) j
      change limUnder atTop (fun L : ℕ => (∑ q ∈ Finset.range L, H q x) i j) = _
      rw [← (Pi.hasSum.1 (Pi.hasSum.1 hx.hasSum i) j).tsum_eq]
      simpa only [Matrix.sum_apply, H, g] using hentry.hasSum.tendsto_sum_nat.limUnder_eq
    change p.β ^ (r + 1) • N0 x + _ = _
    rw [h0]

/-- The coordinate representation agrees almost surely with every buffer of the
original stationary chain. -/
private lemma pe8t_chain_function_ae {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (p : DynParams) (Cv : Covariances m n) (cs : ChainSamples P m n B)
    (t : ℕ) (D : Mat m n) (hD : 0 < riskSigma Cv D)
    (hsize : Muon.Volatility.SizeFin Cv B p.γstar p.CSig)
    (e : ℕ ≃ ((ℕ × Fin B) ⊕ (ℕ × Fin B)))
    (N : ℕ → (ℕ → Vec m × Vec n) → Mat m n)
    (hN : ∀ r x,
      Summable (fun q : ℕ => emaW p.β q •
        batchGrad D (fun a => phys Cv (x (e.symm (Sum.inr (q, a)))))) →
      N r x = p.β ^ (r + 1) •
          (∑' q : ℕ, emaW p.β q •
            batchGrad D (fun a => phys Cv (x (e.symm (Sum.inr (q, a)))))) +
        ∑ i ∈ Finset.range (r + 1), emaW p.β (r - i) •
          batchGrad D (fun a => phys Cv (x (e.symm (Sum.inl (i, a)))))) :
    ∀ᵐ ω ∂P, ∀ r,
      N r (fun l => Sum.elim
        (fun q : ℕ × Fin B => cs.act ((t : ℤ) + q.1 + 1) q.2 ω)
        (fun q : ℕ × Fin B => cs.aux (t : ℤ) q.1 q.2 ω) (e l)) =
      stationaryN p Cv cs t D r ω := by
  filter_upwards [(lem_app_dyn_chains_iii p Cv cs t D 0 hD hsize).1] with ω hω
  intro r
  have hω' : Summable (fun q => emaW p.β q •
      batchGrad D (fun a => phys Cv (cs.aux (t : ℤ) q a ω))) := by
    convert hω using 1
    rfl
  rw [hN r _ (by simpa only [e.apply_symm_apply, Sum.elim_inr] using hω')]
  simp only [e.apply_symm_apply, Sum.elim_inr, Sum.elim_inl]
  unfold stationaryN
  simp only [def_app_dyn_chains]
  rw [pe8s_emaChain_formula]
  simp only [Nat.add_sub_cancel]
  rfl

/-- A finite sum changes only at the replaced coordinate. -/
private lemma pe8t_sum_update {ι M : Type*} [DecidableEq ι] [AddCommGroup M]
    (s : Finset ι) (x : ι → M) (q : ι) (y : M) :
    (∑ i ∈ s, x i) - (∑ i ∈ s, Function.update x q y i) =
      if q ∈ s then x q - y else 0 := by
  rw [← Finset.sum_sub_distrib]
  by_cases hq : q ∈ s
  · rw [if_pos hq, Finset.sum_eq_single q]
    · simp
    · intro i hi hne
      simp [Function.update_of_ne hne]
    · exact fun h => (h hq).elim
  · rw [if_neg hq]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : i ≠ q := by intro h; subst i; exact hq hi
    simp [Function.update_of_ne hne]

/-- Updating one sample changes just one batch sum, and therefore preserves
summability of an EMA history. -/
private lemma pe8t_batch_history_update {m n B : ℕ} (β : ℝ)
    (x : ℕ × Fin B → Mat m n) (q : ℕ) (a : Fin B) (Y : Mat m n)
    (hx : Summable (fun v : ℕ => emaW β v • ∑ b : Fin B, x (v, b))) :
    Summable (fun v : ℕ => emaW β v •
      ∑ b : Fin B, Function.update x (q, a) Y (v, b)) ∧
    (∑' v : ℕ, emaW β v • ∑ b : Fin B, x (v, b)) -
      (∑' v : ℕ, emaW β v • ∑ b : Fin B, Function.update x (q, a) Y (v, b)) =
        emaW β q • (x (q, a) - Y) := by
  classical
  let f : ℕ → Mat m n := fun v => emaW β v • ∑ b : Fin B, x (v, b)
  have hpoint : (fun v : ℕ => emaW β v •
      ∑ b : Fin B, Function.update x (q, a) Y (v, b)) =
      Function.update f q (f q - emaW β q • (x (q, a) - Y)) := by
    funext v
    by_cases hv : v = q
    · subst v
      rw [Function.update_self]
      have hb : (fun b : Fin B => Function.update x (q, a) Y (q, b)) =
          Function.update (fun b : Fin B => x (q, b)) a Y := by
        funext b
        simp only [Function.update_apply, Prod.mk.injEq, true_and]
      rw [hb]
      have hd := pe8t_sum_update Finset.univ (fun b : Fin B => x (q, b)) a Y
      simp only [Finset.mem_univ, if_true] at hd
      have hd' := congrArg (fun Z : Mat m n => emaW β q • Z) hd
      dsimp [f]
      rw [smul_sub] at hd'
      rw [← hd', sub_sub_cancel]
    · rw [Function.update_of_ne hv]
      dsimp [f]
      congr 1
      apply Finset.sum_congr rfl
      intro b hb
      exact Function.update_of_ne (by intro h; exact hv (congrArg Prod.fst h)) _ _
  rw [hpoint]
  refine ⟨hx.update q _, ?_⟩
  rw [(hx.hasSum.update q (f q - emaW β q • (x (q, a) - Y))).tsum_eq]
  change (∑' v, f v) - (f q - emaW β q • (x (q, a) - Y) - f q + ∑' v, f v) = _
  abel

/-- The finite actual history has the expected causal single-coordinate change. -/
private lemma pe8t_finite_history_update {m n B : ℕ} (β : ℝ) (r : ℕ)
    (x : ℕ × Fin B → Mat m n) (q : ℕ) (a : Fin B) (Y : Mat m n) :
    (∑ v ∈ Finset.range (r + 1), emaW β (r - v) • ∑ b : Fin B, x (v, b)) -
      (∑ v ∈ Finset.range (r + 1), emaW β (r - v) •
        ∑ b : Fin B, Function.update x (q, a) Y (v, b)) =
      (if q ≤ r then emaW β (r - q) else 0) • (x (q, a) - Y) := by
  classical
  rw [← Finset.sum_sub_distrib]
  have hpoint : ∀ v,
      emaW β (r - v) • (∑ b : Fin B, x (v, b)) -
        emaW β (r - v) • (∑ b : Fin B, Function.update x (q, a) Y (v, b)) =
      if v = q then emaW β (r - q) • (x (q, a) - Y) else 0 := by
    intro v
    by_cases hv : v = q
    · subst v
      rw [if_pos rfl, ← smul_sub]
      congr 1
      have hb : (fun b : Fin B => Function.update x (q, a) Y (q, b)) =
          Function.update (fun b : Fin B => x (q, b)) a Y := by
        funext b
        simp only [Function.update_apply, Prod.mk.injEq, true_and]
      rw [hb]
      simpa only [Finset.mem_univ, if_true] using
        pe8t_sum_update Finset.univ (fun b : Fin B => x (q, b)) a Y
    · rw [if_neg hv]
      have he : (fun b : Fin B => Function.update x (q, a) Y (v, b)) =
          (fun b : Fin B => x (v, b)) := by
        funext b
        exact Function.update_of_ne (by intro h; exact hv (congrArg Prod.fst h)) _ _
      rw [he, sub_self]
  simp_rw [hpoint]
  by_cases hq : q ≤ r
  · simp [hq, Finset.mem_range, Nat.lt_succ_iff]
  · simp [hq, Finset.mem_range, Nat.lt_succ_iff]

/-- Combining the actual and auxiliary histories gives the exact causal weight
of a replaced sample. This is a pathwise identity on summable histories. -/
private lemma pe8t_ema_function_change {m n B : ℕ} (β : ℝ) (r : ℕ)
    (x : ((ℕ × Fin B) ⊕ (ℕ × Fin B)) → Mat m n)
    (q : (ℕ × Fin B) ⊕ (ℕ × Fin B)) (Y : Mat m n)
    (hx : Summable (fun v : ℕ => emaW β v • ∑ b : Fin B, x (Sum.inr (v, b)))) :
    let H := fun z : ((ℕ × Fin B) ⊕ (ℕ × Fin B)) → Mat m n =>
      β ^ (r + 1) • (∑' v : ℕ, emaW β v • ∑ b : Fin B, z (Sum.inr (v, b))) +
        ∑ v ∈ Finset.range (r + 1), emaW β (r - v) • ∑ b : Fin B, z (Sum.inl (v, b))
    Summable (fun v : ℕ => emaW β v •
      ∑ b : Fin B, Function.update x q Y (Sum.inr (v, b))) ∧
    H x - H (Function.update x q Y) =
      (Sum.elim (fun qa : ℕ × Fin B => if qa.1 ≤ r then emaW β (r - qa.1) else 0)
        (fun qa : ℕ × Fin B => emaW β (qa.1 + r + 1)) q) • (x q - Y) := by
  classical
  dsimp only
  rcases q with ⟨q, a⟩ | ⟨q, a⟩
  · have hR : (fun v b => Function.update x (Sum.inl (q, a)) Y (Sum.inr (v, b))) =
        (fun v b => x (Sum.inr (v, b))) := by
      funext v b
      simp
    have hL : (fun v b => Function.update x (Sum.inl (q, a)) Y (Sum.inl (v, b))) =
        (fun v b => Function.update (fun qa => x (Sum.inl qa)) (q, a) Y (v, b)) := by
      funext v b
      simp only [Function.update_apply, Sum.inl.injEq]
    simp_rw [show ∀ v b, Function.update x (Sum.inl (q, a)) Y (Sum.inr (v, b)) =
      x (Sum.inr (v, b)) from fun v b => congrFun (congrFun hR v) b]
    refine ⟨hx, ?_⟩
    rw [add_sub_add_left_eq_sub]
    simp_rw [show ∀ v b, Function.update x (Sum.inl (q, a)) Y (Sum.inl (v, b)) =
      Function.update (fun qa => x (Sum.inl qa)) (q, a) Y (v, b) from
        fun v b => congrFun (congrFun hL v) b]
    exact pe8t_finite_history_update β r (fun qa => x (Sum.inl qa)) q a Y
  · have hL : ∀ v b, Function.update x (Sum.inr (q, a)) Y (Sum.inl (v, b)) =
        x (Sum.inl (v, b)) := by intro v b; simp
    have hR : ∀ v b, Function.update x (Sum.inr (q, a)) Y (Sum.inr (v, b)) =
        Function.update (fun qa => x (Sum.inr qa)) (q, a) Y (v, b) := by
      intro v b
      simp only [Function.update_apply, Sum.inr.injEq]
    simp_rw [hL, hR]
    obtain ⟨hs, hd⟩ := pe8t_batch_history_update β (fun qa => x (Sum.inr qa)) q a Y hx
    refine ⟨hs, ?_⟩
    rw [add_sub_add_right_eq_sub, ← smul_sub, hd, smul_smul]
    congr 1
    simpa only [Nat.add_assoc, Sum.elim_inr] using (pe8t_emaW_add β q (r + 1)).symm

/-- Write the physical batch gradient as a sum of its individual sample terms. -/
private lemma pe8t_batchGrad_sum {m n B : ℕ} (Cv : Covariances m n)
    (D : Mat m n) (x : Fin B → Vec m × Vec n) :
    batchGrad D (fun a => phys Cv (x a)) =
      ∑ a : Fin B, ((B : ℝ)⁻¹ * resid D (phys Cv (x a))) •
        outer (phys Cv (x a)).1 (phys Cv (x a)).2 := by
  simp only [batchGrad, Muon.Setup.grad, Finset.smul_sum, smul_smul]

/-- Transfer the exact pathwise replacement identity to the measurable
coordinate representative of the stationary buffer. -/
private lemma pe8t_chain_function_change {m n B : ℕ} (p : DynParams)
    (Cv : Covariances m n) (D : Mat m n)
    (e : ℕ ≃ ((ℕ × Fin B) ⊕ (ℕ × Fin B)))
    (N : ℕ → (ℕ → Vec m × Vec n) → Mat m n)
    (hN : ∀ r x,
      Summable (fun q : ℕ => emaW p.β q •
        batchGrad D (fun a => phys Cv (x (e.symm (Sum.inr (q, a)))))) →
      N r x = p.β ^ (r + 1) •
          (∑' q : ℕ, emaW p.β q •
            batchGrad D (fun a => phys Cv (x (e.symm (Sum.inr (q, a)))))) +
        ∑ i ∈ Finset.range (r + 1), emaW p.β (r - i) •
          batchGrad D (fun a => phys Cv (x (e.symm (Sum.inl (i, a))))))
    (r : ℕ) (x : ℕ → Vec m × Vec n) (l : ℕ) (y : Vec m × Vec n)
    (hx : Summable (fun q : ℕ => emaW p.β q •
      batchGrad D (fun a => phys Cv (x (e.symm (Sum.inr (q, a))))))) :
    let τ : Vec m × Vec n → Mat m n := fun z =>
      ((B : ℝ)⁻¹ * resid D (phys Cv z)) • outer (phys Cv z).1 (phys Cv z).2
    N r x - N r (Function.update x l y) =
      (Sum.elim (fun qa : ℕ × Fin B => if qa.1 ≤ r then emaW p.β (r - qa.1) else 0)
        (fun qa : ℕ × Fin B => emaW p.β (qa.1 + r + 1)) (e l)) • (τ (x l) - τ y) := by
  classical
  dsimp only
  let τ : Vec m × Vec n → Mat m n := fun z =>
    ((B : ℝ)⁻¹ * resid D (phys Cv z)) • outer (phys Cv z).1 (phys Cv z).2
  let X : ((ℕ × Fin B) ⊕ (ℕ × Fin B)) → Mat m n := fun q => τ (x (e.symm q))
  have he : ∀ q, τ (Function.update x l y (e.symm q)) =
      Function.update X (e l) (τ y) q := by
    intro q
    by_cases hq : q = e l
    · subst q
      simp [X]
    · have hne : e.symm q ≠ l := by
        intro h
        apply hq
        simpa using congrArg e h
      simp [Function.update_of_ne hq, Function.update_of_ne hne, X]
  have hsum : Summable (fun q : ℕ => emaW p.β q • ∑ b : Fin B, X (Sum.inr (q, b))) := by
    simpa only [pe8t_batchGrad_sum] using hx
  obtain ⟨hs, hd⟩ := pe8t_ema_function_change p.β r X (e l) (τ y) hsum
  have hs' : Summable (fun q : ℕ => emaW p.β q • batchGrad D
      (fun a => phys Cv (Function.update x l y (e.symm (Sum.inr (q, a)))))) := by
    simp only [pe8t_batchGrad_sum]
    change Summable (fun q : ℕ => emaW p.β q •
      ∑ a : Fin B, τ (Function.update x l y (e.symm (Sum.inr (q, a)))))
    simp_rw [he]
    exact hs
  rw [hN r x hx, hN r _ hs']
  simp only [pe8t_batchGrad_sum]
  change (p.β ^ (r + 1) • (∑' q, emaW p.β q • ∑ a : Fin B, X (Sum.inr (q, a))) +
      ∑ i ∈ Finset.range (r + 1), emaW p.β (r - i) • ∑ a : Fin B, X (Sum.inl (i, a))) -
    (p.β ^ (r + 1) • (∑' q, emaW p.β q •
      ∑ a : Fin B, τ (Function.update x l y (e.symm (Sum.inr (q, a))))) +
      ∑ i ∈ Finset.range (r + 1), emaW p.β (r - i) •
        ∑ a : Fin B, τ (Function.update x l y (e.symm (Sum.inl (i, a))))) = _
  simp_rw [he]
  simpa only [X, e.symm_apply_apply] using hd

/-- Trace duality and Schatten sensitivity for the risk pairing. -/
private lemma pe8t_g_lipschitz {m n : ℕ} (p : DynParams)
    (Cv : Covariances m n) (D K K' : Mat m n)
    (hCo : opNorm Cv.Sout ≤ p.CSig) (hCi : opNorm Cv.Sin ≤ p.CSig)
    (hD : riskSigma Cv D = 1 / 2) :
    |pairSigma Cv D (Q p.ϱ K) - pairSigma Cv D (Q p.ϱ K')| ≤
      (p.CSig * diffuseness Cv D * p.ϱ ^ (-(1 / 2 : ℝ))) * nuc (K - K') := by
  have he : Arot Cv (Arot Cv D) = Cv.Sout * D * Cv.Sin := by
    unfold Arot
    calc
      _ = (rOut Cv * rOut Cv) * D * (rIn Cv * rIn Cv) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [pe8s_rOut_sq, pe8s_rIn_sq]
  have hA : opNorm (Cv.Sout * D * Cv.Sin) ≤ p.CSig * diffuseness Cv D := by
    have hb := (pe8s_Arot_bounds Cv p.CSig hCo hCi (Arot Cv D)).2
    rw [he] at hb
    simpa only [diffuseness, normState, pe8s_Ahat_eq Cv D hD] using hb
  have hd : nuc (Q p.ϱ K - Q p.ϱ K') ≤
      p.ϱ ^ (-(1 / 2 : ℝ)) * nuc (K - K') := by
    simpa [schatNorm] using
      (lem_app_dyn_schatten_ii (p := 1) (Or.inl rfl) p.hϱ K K')
  have hid : pairSigma Cv D (Q p.ϱ K) - pairSigma Cv D (Q p.ϱ K') =
      frobIP (Cv.Sout * D * Cv.Sin) (Q p.ϱ K - Q p.ϱ K') := by
    simp only [pairSigma, frobIP, Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub]
  rw [hid]
  calc
    _ ≤ opNorm (Cv.Sout * D * Cv.Sin) * nuc (Q p.ϱ K - Q p.ϱ K') := pe8m_frobIP_nuc _ _
    _ ≤ (p.CSig * diffuseness Cv D) * (p.ϱ ^ (-(1 / 2 : ℝ)) * nuc (K - K')) :=
      mul_le_mul hA hd (nuc_nonneg _) ((pe8_opNorm_nonneg _).trans hA)
    _ = _ := by ring

/-- The susceptibility pairing has a nuclear Lipschitz constant proportional to
the operator norm of the test matrix. -/
private lemma pe8t_ridge_lipschitz {m n : ℕ} (ϱ piT : ℝ) (hϱ : 0 < ϱ)
    (Pt K K' : Mat m n) (hP : opNorm Pt ≤ piT) :
    |frobIP Pt (ridgeDeriv ϱ K) - frobIP Pt (ridgeDeriv ϱ K')| ≤
      (piT * ((1 / 2) * ϱ ^ (-(3 / 2 : ℝ)))) * nuc (K - K') := by
  have hid : frobIP Pt (ridgeDeriv ϱ K) - frobIP Pt (ridgeDeriv ϱ K') =
      frobIP Pt (ridgeDeriv ϱ K - ridgeDeriv ϱ K') := by
    simp only [frobIP, Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub]
  rw [hid]
  calc
    _ ≤ opNorm Pt * nuc (ridgeDeriv ϱ K - ridgeDeriv ϱ K') := pe8m_frobIP_nuc _ _
    _ ≤ piT * ((1 / 2) * ϱ ^ (-(3 / 2 : ℝ)) * nuc (K - K')) :=
      mul_le_mul hP (lem_app_dyn_schatten_iii hϱ K K')
        (nuc_nonneg _) ((pe8_opNorm_nonneg _).trans hP)
    _ = _ := by ring

/-- The sum of the original and replacement sample nuclear norms has the
uniform `14 CΣ γ` second-moment bound. Independence between the two is unnecessary. -/
private lemma pe8t_sample_replacement_L2 {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Cv : Covariances m n) (γ CS : ℝ) (hB : 0 < B)
    (hsize : Muon.Volatility.SizeFin Cv B γ CS)
    (z z' : Fin B → Ω → Vec m × Vec n)
    (hz : IIDBatch P ((Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)) z)
    (hz' : IIDBatch P ((Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)) z')
    (D : Mat m n) (hD : riskSigma Cv D = 1 / 2) (a : Fin B) :
    eLpNorm (fun ω => nuc (batchSummand Cv D z a ω) +
      nuc (batchSummand Cv D z' a ω)) 2 P ≤ ENNReal.ofReal (14 * CS * γ) := by
  have hDp : 0 < riskSigma Cv D := by rw [hD]; norm_num
  have hA : fro (rOut Cv * D * rIn Cv) = 1 := by
    change fro (Arot Cv D) = 1
    rw [← pe8s_Ahat_eq Cv D hD]
    exact pe8q_Ahat_fro Cv D hDp
  have h1 := (lem_app_dyn_batch_iii Cv γ CS hB hsize z hz D a).2.2
  have h2 := (lem_app_dyn_batch_iii Cv γ CS hB hsize z' hz' D a).2.2
  rw [hA, mul_one] at h1 h2
  have hn : 0 ≤ 7 * CS * γ := by
    have hB' : (0 : ℝ) < B := by exact_mod_cast hB
    have hCS : 0 ≤ CS := (pe8_opNorm_nonneg _).trans hsize.2.1
    have hγ : 0 ≤ γ := by
      have hd := hsize.1
      have hm : (0 : ℝ) ≤ max (m : ℝ) (n : ℝ) := by positivity
      nlinarith
    positivity
  calc
    _ ≤ eLpNorm (fun ω => nuc (batchSummand Cv D z a ω)) 2 P +
        eLpNorm (fun ω => nuc (batchSummand Cv D z' a ω)) 2 P :=
      eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (7 * CS * γ) + ENNReal.ofReal (7 * CS * γ) := add_le_add h1 h2
    _ = ENNReal.ofReal (14 * CS * γ) := by rw [← ENNReal.ofReal_add hn hn]; congr 1; ring

private lemma pe8t_iid_act {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (cs : ChainSamples P m n B) (s : ℤ) :
    IIDBatch P ((Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)) (cs.act s) := by
  refine ⟨fun a => (cs.meas_act s a).aemeasurable, cs.law_act s, ?_⟩
  exact cs.indep.precomp (g := fun a : Fin B => Sum.inl (s, a))
    (by intro a b h; simpa using h)

private lemma pe8t_iid_aux {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (cs : ChainSamples P m n B) (s : ℤ) (q : ℕ) :
    IIDBatch P ((Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)) (cs.aux s q) := by
  refine ⟨fun a => (cs.meas_aux s q a).aemeasurable, cs.law_aux s q, ?_⟩
  exact cs.indep.precomp (g := fun a : Fin B => Sum.inr (s, q, a))
    (by intro a b h; simpa using h)

/-- The moment envelope for every coordinate in the enumeration and its copy. -/
private lemma pe8t_coordinates_L2 {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (p : DynParams) (Cv : Covariances m n) (cs : ChainSamples P m n B)
    (t : ℕ) (D : Mat m n) (hD : riskSigma Cv D = 1 / 2) (hB : 0 < B)
    (hsize : Muon.Volatility.SizeFin Cv B p.γstar p.CSig)
    (e : ℕ ≃ ((ℕ × Fin B) ⊕ (ℕ × Fin B))) :
    let ξ : ℕ → Ω → Vec m × Vec n := fun l =>
      Sum.elim (fun q : ℕ × Fin B => cs.act ((t : ℤ) + q.1 + 1) q.2)
        (fun q : ℕ × Fin B => cs.aux (t : ℤ) q.1 q.2) (e l)
    let ξ' : ℕ → Ω → Vec m × Vec n := fun l =>
      Sum.elim (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 1) q.1 q.2)
        (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 2) q.1 q.2) (e l)
    let τ : Vec m × Vec n → Mat m n := fun z =>
      ((B : ℝ)⁻¹ * resid D (phys Cv z)) • outer (phys Cv z).1 (phys Cv z).2
    ∀ l, eLpNorm (fun ω => nuc (τ (ξ l ω)) + nuc (τ (ξ' l ω))) 2 P ≤
      ENNReal.ofReal (14 * p.CSig * p.γstar) := by
  dsimp only
  intro l
  cases heq : e l with
  | inl qa =>
      simpa only [heq, Sum.elim_inl, batchSummand] using
        pe8t_sample_replacement_L2 Cv p.γstar p.CSig hB hsize
          (cs.act ((t : ℤ) + qa.1 + 1)) (cs.aux ((t : ℤ) + 1) qa.1)
          (pe8t_iid_act cs _) (pe8t_iid_aux cs _ _) D hD qa.2
  | inr qa =>
      simpa only [heq, Sum.elim_inr, batchSummand] using
        pe8t_sample_replacement_L2 Cv p.γstar p.CSig hB hsize
          (cs.aux (t : ℤ) qa.1) (cs.aux ((t : ℤ) + 2) qa.1)
          (pe8t_iid_aux cs _ _) (pe8t_iid_aux cs _ _) D hD qa.2

/-- Turn a pointwise sample sensitivity estimate into an `L²` replacement
bound without requiring independence of the original sample and its replacement. -/
private lemma pe8t_replacement_L2_of_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f H : Ω → ℝ) (hf : AEStronglyMeasurable f P)
    (L w C : ℝ) (hL : 0 ≤ L) (hw : 0 ≤ w)
    (hH : eLpNorm H 2 P ≤ ENNReal.ofReal C)
    (hpt : ∀ᵐ ω ∂P, |f ω| ≤ (L * w) * H ω) :
    eLpNorm f 2 P ≤ ENNReal.ofReal (L * w * C) := by
  have hc : 0 ≤ L * w := mul_nonneg hL hw
  calc
    _ ≤ eLpNorm ((L * w) • H) 2 P :=
      eLpNorm_mono_ae_real hf (by simpa only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul] using hpt)
    _ = ENNReal.ofReal (L * w) * eLpNorm H 2 P := by
      rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ ENNReal.ofReal (L * w) * ENNReal.ofReal C := mul_le_mul_right hH _
    _ = ENNReal.ofReal (L * w * C) := (ENNReal.ofReal_mul hc).symm

/-- A nuclear Lipschitz observable of the stationary coordinate model has the
required per-sample `L²` sensitivity, with the exact causal EMA weight. -/
private lemma pe8t_observable_replacement {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (p : DynParams) (Cv : Covariances m n) (cs : ChainSamples P m n B)
    (t : ℕ) (D : Mat m n) (hD : riskSigma Cv D = 1 / 2) (hB : 0 < B)
    (hsize : Muon.Volatility.SizeFin Cv B p.γstar p.CSig)
    (e : ℕ ≃ ((ℕ × Fin B) ⊕ (ℕ × Fin B)))
    (N : ℕ → (ℕ → Vec m × Vec n) → Mat m n)
    (hNm : ∀ r, Measurable (N r))
    (hN : ∀ r x,
      Summable (fun q : ℕ => emaW p.β q •
        batchGrad D (fun a => phys Cv (x (e.symm (Sum.inr (q, a)))))) →
      N r x = p.β ^ (r + 1) •
          (∑' q : ℕ, emaW p.β q •
            batchGrad D (fun a => phys Cv (x (e.symm (Sum.inr (q, a)))))) +
        ∑ i ∈ Finset.range (r + 1), emaW p.β (r - i) •
          batchGrad D (fun a => phys Cv (x (e.symm (Sum.inl (i, a))))))
    (f : Mat m n → ℝ) (hfm : Measurable f) (L : ℝ) (hL : 0 ≤ L)
    (hfL : ∀ K K', |f K - f K'| ≤ L * nuc (K - K')) :
    let ξ : ℕ → Ω → Vec m × Vec n := fun l =>
      Sum.elim (fun q : ℕ × Fin B => cs.act ((t : ℤ) + q.1 + 1) q.2)
        (fun q : ℕ × Fin B => cs.aux (t : ℤ) q.1 q.2) (e l)
    let ξ' : ℕ → Ω → Vec m × Vec n := fun l =>
      Sum.elim (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 1) q.1 q.2)
        (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 2) q.1 q.2) (e l)
    let w : ℕ → ℕ → ℝ := fun r l =>
      Sum.elim (fun qa : ℕ × Fin B => if qa.1 ≤ r then emaW p.β (r - qa.1) else 0)
        (fun qa : ℕ × Fin B => emaW p.β (qa.1 + r + 1)) (e l)
    ∀ r l, eLpNorm (fun ω => f (N r (fun i => ξ i ω)) -
      f (N r (Function.update (fun i => ξ i ω) l (ξ' l ω)))) 2 P ≤
      ENNReal.ofReal (L * (14 * p.CSig * p.γstar)) * ENNReal.ofReal (w r l) := by
  classical
  dsimp only
  let ξ : ℕ → Ω → Vec m × Vec n := fun l =>
    Sum.elim (fun q : ℕ × Fin B => cs.act ((t : ℤ) + q.1 + 1) q.2)
      (fun q : ℕ × Fin B => cs.aux (t : ℤ) q.1 q.2) (e l)
  let ξ' : ℕ → Ω → Vec m × Vec n := fun l =>
    Sum.elim (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 1) q.1 q.2)
      (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 2) q.1 q.2) (e l)
  let τ : Vec m × Vec n → Mat m n := fun z =>
    ((B : ℝ)⁻¹ * resid D (phys Cv z)) • outer (phys Cv z).1 (phys Cv z).2
  intro r l
  let w : ℝ := Sum.elim
    (fun qa : ℕ × Fin B => if qa.1 ≤ r then emaW p.β (r - qa.1) else 0)
    (fun qa : ℕ × Fin B => emaW p.β (qa.1 + r + 1)) (e l)
  have hw : 0 ≤ w := by
    dsimp only [w]
    cases he : e l with
    | inl qa => simp only [Sum.elim_inl]; split_ifs <;> first | exact (pe8q_emaW_mem_Icc p _).1 | exact le_rfl
    | inr qa => exact (pe8q_emaW_mem_Icc p _).1
  obtain ⟨hξ, hξ', -, -⟩ := pe8t_coordinates cs t e
  have hx : Measurable (fun ω i => ξ i ω) := Measurable.of_eval hξ
  have hx' : Measurable (fun ω => Function.update (fun i => ξ i ω) l (ξ' l ω)) := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i = l
    · subst i; simpa using hξ' l
    · simpa only [Function.update_of_ne hi] using hξ i
  have hmeas : AEStronglyMeasurable
      (fun ω => f (N r (fun i => ξ i ω)) -
        f (N r (Function.update (fun i => ξ i ω) l (ξ' l ω)))) P :=
    (((hfm.comp (hNm r)).comp hx).sub ((hfm.comp (hNm r)).comp hx')).aestronglyMeasurable
  have hmoment : eLpNorm (fun ω => nuc (τ (ξ l ω)) + nuc (τ (ξ' l ω))) 2 P ≤
      ENNReal.ofReal (14 * p.CSig * p.γstar) := pe8t_coordinates_L2 p Cv cs t D hD hB hsize e l
  have hpt : ∀ᵐ ω ∂P,
      |f (N r (fun i => ξ i ω)) - f (N r (Function.update (fun i => ξ i ω) l (ξ' l ω)))| ≤
      (L * w) * (nuc (τ (ξ l ω)) + nuc (τ (ξ' l ω))) := by
    have hDp : 0 < riskSigma Cv D := by rw [hD]; norm_num
    filter_upwards [(lem_app_dyn_chains_iii p Cv cs t D 0 hDp hsize).1] with ω hω
    have hsum : Summable (fun q => emaW p.β q •
        batchGrad D (fun a => phys Cv (ξ (e.symm (Sum.inr (q, a))) ω))) := by
      simp only [ξ, e.apply_symm_apply, Sum.elim_inr]
      convert hω using 1
      rfl
    have hdiff := pe8t_chain_function_change p Cv D e N hN r (fun i => ξ i ω) l (ξ' l ω) hsum
    change N r (fun i => ξ i ω) - N r (Function.update (fun i => ξ i ω) l (ξ' l ω)) =
      w • (τ (ξ l ω) - τ (ξ' l ω)) at hdiff
    have hnuc : nuc (τ (ξ l ω) - τ (ξ' l ω)) ≤ nuc (τ (ξ l ω)) + nuc (τ (ξ' l ω)) := by
      have hn : nuc (-τ (ξ' l ω)) = nuc (τ (ξ' l ω)) := by
        simpa using nuc_smul (-1 : ℝ) (τ (ξ' l ω))
      simpa only [sub_eq_add_neg, hn] using nuc_add_le (τ (ξ l ω)) (-τ (ξ' l ω))
    calc
      _ ≤ L * nuc (N r (fun i => ξ i ω) -
          N r (Function.update (fun i => ξ i ω) l (ξ' l ω))) := hfL _ _
      _ = L * (w * nuc (τ (ξ l ω) - τ (ξ' l ω))) := by rw [hdiff, nuc_smul, abs_of_nonneg hw]
      _ ≤ (L * w) * (nuc (τ (ξ l ω)) + nuc (τ (ξ' l ω))) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hnuc (mul_nonneg hL hw)
  have hb := pe8t_replacement_L2_of_bound P _ _ hmeas L w _ hL hw hmoment hpt
  change eLpNorm _ 2 P ≤ ENNReal.ofReal (L * (14 * p.CSig * p.γstar)) * ENNReal.ofReal w
  have hc : 0 ≤ L * (14 * p.CSig * p.γstar) :=
    mul_nonneg hL (mul_nonneg (mul_nonneg (by norm_num) (le_trans zero_le_one p.hC)) p.hγ)
  rw [← ENNReal.ofReal_mul hc]
  convert hb using 1 <;> congr 1 <;> ring

/-- Deleting one actual sample does not enlarge any replacement sensitivity. -/
private lemma pe8t_minor_observable_replacement {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (p : DynParams) (Cv : Covariances m n) (cs : ChainSamples P m n B)
    (t : ℕ) (D : Mat m n) (hD : riskSigma Cv D = 1 / 2) (hB : 0 < B)
    (hsize : Muon.Volatility.SizeFin Cv B p.γstar p.CSig)
    (e : ℕ ≃ ((ℕ × Fin B) ⊕ (ℕ × Fin B)))
    (N : ℕ → (ℕ → Vec m × Vec n) → Mat m n)
    (hNm : ∀ r, Measurable (N r))
    (hN : ∀ r x,
      Summable (fun q : ℕ => emaW p.β q •
        batchGrad D (fun a => phys Cv (x (e.symm (Sum.inr (q, a)))))) →
      N r x = p.β ^ (r + 1) •
          (∑' q : ℕ, emaW p.β q •
            batchGrad D (fun a => phys Cv (x (e.symm (Sum.inr (q, a)))))) +
        ∑ i ∈ Finset.range (r + 1), emaW p.β (r - i) •
          batchGrad D (fun a => phys Cv (x (e.symm (Sum.inl (i, a))))))
    (j : ℕ) (a : Fin B) (f : Mat m n → ℝ) (hfm : Measurable f) (L : ℝ) (hL : 0 ≤ L)
    (hfL : ∀ K K', |f K - f K'| ≤ L * nuc (K - K')) :
    let τ : Vec m × Vec n → Mat m n := fun z =>
      ((B : ℝ)⁻¹ * resid D (phys Cv z)) • outer (phys Cv z).1 (phys Cv z).2
    let M : ℕ → (ℕ → Vec m × Vec n) → Mat m n := fun r x =>
      N r x - emaW p.β (r - j) • τ (x (e.symm (Sum.inl (j, a))))
    let ξ : ℕ → Ω → Vec m × Vec n := fun l =>
      Sum.elim (fun q : ℕ × Fin B => cs.act ((t : ℤ) + q.1 + 1) q.2)
        (fun q : ℕ × Fin B => cs.aux (t : ℤ) q.1 q.2) (e l)
    let ξ' : ℕ → Ω → Vec m × Vec n := fun l =>
      Sum.elim (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 1) q.1 q.2)
        (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 2) q.1 q.2) (e l)
    let w : ℕ → ℕ → ℝ := fun r l =>
      Sum.elim (fun qa : ℕ × Fin B => if qa.1 ≤ r then emaW p.β (r - qa.1) else 0)
        (fun qa : ℕ × Fin B => emaW p.β (qa.1 + r + 1)) (e l)
    ∀ r, j ≤ r → ∀ l, eLpNorm (fun ω => f (M r (fun i => ξ i ω)) -
      f (M r (Function.update (fun i => ξ i ω) l (ξ' l ω)))) 2 P ≤
      ENNReal.ofReal (L * (14 * p.CSig * p.γstar)) * ENNReal.ofReal (w r l) := by
  classical
  dsimp only
  let ξ : ℕ → Ω → Vec m × Vec n := fun l =>
    Sum.elim (fun q : ℕ × Fin B => cs.act ((t : ℤ) + q.1 + 1) q.2)
      (fun q : ℕ × Fin B => cs.aux (t : ℤ) q.1 q.2) (e l)
  let ξ' : ℕ → Ω → Vec m × Vec n := fun l =>
    Sum.elim (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 1) q.1 q.2)
      (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 2) q.1 q.2) (e l)
  let τ : Vec m × Vec n → Mat m n := fun z =>
    ((B : ℝ)⁻¹ * resid D (phys Cv z)) • outer (phys Cv z).1 (phys Cv z).2
  let M : ℕ → (ℕ → Vec m × Vec n) → Mat m n := fun r x =>
    N r x - emaW p.β (r - j) • τ (x (e.symm (Sum.inl (j, a))))
  have hτm : Measurable τ := by
    have hc : Continuous τ := by unfold τ resid phys outer; fun_prop
    exact hc.measurable
  have hMm : ∀ r, Measurable (M r) := fun r =>
    (hNm r).sub ((hτm.comp (measurable_pi_apply (e.symm (Sum.inl (j, a))))).const_smul (emaW p.β (r - j)))
  intro r hjr l
  let w : ℝ := Sum.elim
    (fun qa : ℕ × Fin B => if qa.1 ≤ r then emaW p.β (r - qa.1) else 0)
    (fun qa : ℕ × Fin B => emaW p.β (qa.1 + r + 1)) (e l)
  have hw : 0 ≤ w := by
    dsimp only [w]
    cases he : e l with
    | inl qa => simp only [Sum.elim_inl]; split_ifs <;> first | exact (pe8q_emaW_mem_Icc p _).1 | exact le_rfl
    | inr qa => exact (pe8q_emaW_mem_Icc p _).1
  obtain ⟨hξ, hξ', -, -⟩ := pe8t_coordinates cs t e
  have hx : Measurable (fun ω i => ξ i ω) := Measurable.of_eval hξ
  have hx' : Measurable (fun ω => Function.update (fun i => ξ i ω) l (ξ' l ω)) := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i = l
    · subst i; simpa using hξ' l
    · simpa only [Function.update_of_ne hi] using hξ i
  have hmeas : AEStronglyMeasurable
      (fun ω => f (M r (fun i => ξ i ω)) -
        f (M r (Function.update (fun i => ξ i ω) l (ξ' l ω)))) P :=
    (((hfm.comp (hMm r)).comp hx).sub ((hfm.comp (hMm r)).comp hx')).aestronglyMeasurable
  have hmoment : eLpNorm (fun ω => nuc (τ (ξ l ω)) + nuc (τ (ξ' l ω))) 2 P ≤
      ENNReal.ofReal (14 * p.CSig * p.γstar) := pe8t_coordinates_L2 p Cv cs t D hD hB hsize e l
  have hpt : ∀ᵐ ω ∂P,
      |f (M r (fun i => ξ i ω)) - f (M r (Function.update (fun i => ξ i ω) l (ξ' l ω)))| ≤
      (L * w) * (nuc (τ (ξ l ω)) + nuc (τ (ξ' l ω))) := by
    have hDp : 0 < riskSigma Cv D := by rw [hD]; norm_num
    filter_upwards [(lem_app_dyn_chains_iii p Cv cs t D 0 hDp hsize).1] with ω hω
    have hsum : Summable (fun q => emaW p.β q •
        batchGrad D (fun a => phys Cv (ξ (e.symm (Sum.inr (q, a))) ω))) := by
      simp only [ξ, e.apply_symm_apply, Sum.elim_inr]
      convert hω using 1
      rfl
    have hdiff := pe8t_chain_function_change p Cv D e N hN r (fun i => ξ i ω) l (ξ' l ω) hsum
    change N r (fun i => ξ i ω) - N r (Function.update (fun i => ξ i ω) l (ξ' l ω)) =
      w • (τ (ξ l ω) - τ (ξ' l ω)) at hdiff
    have hdiffM : M r (fun i => ξ i ω) - M r (Function.update (fun i => ξ i ω) l (ξ' l ω)) =
        if l = e.symm (Sum.inl (j, a)) then 0 else w • (τ (ξ l ω) - τ (ξ' l ω)) := by
      by_cases hl : l = e.symm (Sum.inl (j, a))
      · have hwj : w = emaW p.β (r - j) := by simp [w, hl, hjr]
        dsimp only [M]
        rw [sub_sub_sub_comm, hdiff, hwj, if_pos hl]
        simp only [← hl, Function.update_self, smul_sub, sub_self]
      · dsimp only [M]
        rw [Function.update_of_ne (Ne.symm hl), sub_sub_sub_cancel_right, hdiff, if_neg hl]
    have hnuc : nuc (τ (ξ l ω) - τ (ξ' l ω)) ≤ nuc (τ (ξ l ω)) + nuc (τ (ξ' l ω)) := by
      have hn : nuc (-τ (ξ' l ω)) = nuc (τ (ξ' l ω)) := by
        simpa using nuc_smul (-1 : ℝ) (τ (ξ' l ω))
      simpa only [sub_eq_add_neg, hn] using nuc_add_le (τ (ξ l ω)) (-τ (ξ' l ω))
    calc
      _ ≤ L * nuc (M r (fun i => ξ i ω) -
          M r (Function.update (fun i => ξ i ω) l (ξ' l ω))) := hfL _ _
      _ ≤ L * (w * nuc (τ (ξ l ω) - τ (ξ' l ω))) := by
        rw [hdiffM]
        split_ifs
        · have hz : nuc (0 : Mat m n) = 0 := by simpa using nuc_smul (0 : ℝ) (0 : Mat m n)
          rw [hz, mul_zero]
          exact mul_nonneg hL (mul_nonneg hw (nuc_nonneg _))
        · rw [nuc_smul, abs_of_nonneg hw]
      _ ≤ (L * w) * (nuc (τ (ξ l ω)) + nuc (τ (ξ' l ω))) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hnuc (mul_nonneg hL hw)
  have hb := pe8t_replacement_L2_of_bound P _ _ hmeas L w _ hL hw hmoment hpt
  change eLpNorm _ 2 P ≤ ENNReal.ofReal (L * (14 * p.CSig * p.γstar)) * ENNReal.ofReal w
  have hc : 0 ≤ L * (14 * p.CSig * p.γstar) :=
    mul_nonneg hL (mul_nonneg (mul_nonneg (by norm_num) (le_trans zero_le_one p.hC)) p.hγ)
  rw [← ENNReal.ofReal_mul hc]
  convert hb using 1 <;> congr 1 <;> ring

/-- The covariance inequality with a prescribed summable envelope of
single-coordinate replacement norms. -/
private lemma pe8t_covariance_of_replacements {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ ξ' : ℕ → Ω → X) (hξ : ∀ l, Measurable (ξ l))
    (hξ' : ∀ l, Measurable (ξ' l)) (hlaw : ∀ l, P.map (ξ' l) = P.map (ξ l))
    (hind : iIndepFun (Sum.elim ξ ξ' : ℕ ⊕ ℕ → Ω → X) P)
    (F G : (ℕ → X) → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hF2 : MemLp (fun ω => F (fun l => ξ l ω)) 2 P)
    (hG2 : MemLp (fun ω => G (fun l => ξ l ω)) 2 P)
    (a b : ℕ → ℝ≥0∞) (C : ℝ) (hC : 0 ≤ C)
    (hFa : ∀ l, eLpNorm (fun ω => F (fun i => ξ i ω) -
      F (Function.update (fun i => ξ i ω) l (ξ' l ω))) 2 P ≤ a l)
    (hGb : ∀ l, eLpNorm (fun ω => G (fun i => ξ i ω) -
      G (Function.update (fun i => ξ i ω) l (ξ' l ω))) 2 P ≤ b l)
    (hsum : (∑' l, a l * b l) ≤ ENNReal.ofReal C) :
    |covariance (fun ω => F (fun l => ξ l ω)) (fun ω => G (fun l => ξ l ω)) P| ≤ C := by
  have h := lem_app_dyn_covariance P ξ ξ' hξ hξ' hlaw hind F G hF hG hF2 hG2
  have hbound : ENNReal.ofReal
      |covariance (fun ω => F (fun l => ξ l ω)) (fun ω => G (fun l => ξ l ω)) P| ≤
      ENNReal.ofReal C := h.trans ((ENNReal.tsum_le_tsum fun l =>
        mul_le_mul' (hFa l) (hGb l)).trans hsum)
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hbound

private lemma pe8t_covariance_congr_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f f' g g' : Ω → ℝ} (hf : f =ᵐ[P] f') (hg : g =ᵐ[P] g') :
    covariance f g P = covariance f' g' P := by
  unfold covariance
  rw [integral_congr_ae hf, integral_congr_ae hg]
  apply integral_congr_ae
  filter_upwards [hf, hg] with ω hfω hgω
  rw [hfω, hgω]

/-- Covariance of two bounded nuclear-Lipschitz observables of the stationary
chain, with decay given by the overlap of their causal sample histories. -/
private lemma pe8t_stationary_covariance {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (p : DynParams) (Cv : Covariances m n) (cs : ChainSamples P m n B)
    (t k r : ℕ) (D : Mat m n) (hD : riskSigma Cv D = 1 / 2) (hB : 0 < B)
    (hsize : Muon.Volatility.SizeFin Cv B p.γstar p.CSig)
    (f g : Mat m n → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (bf bg Lf Lg : ℝ) (hbf : ∀ K, |f K| ≤ bf) (hbg : ∀ K, |g K| ≤ bg)
    (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hfL : ∀ K K', |f K - f K'| ≤ Lf * nuc (K - K'))
    (hgL : ∀ K K', |g K - g K'| ≤ Lg * nuc (K - K')) :
    |covariance (fun ω => f (stationaryN p Cv cs t D k ω))
      (fun ω => g (stationaryN p Cv cs t D r ω)) P| ≤
      (Lf * (14 * p.CSig * p.γstar)) * (Lg * (14 * p.CSig * p.γstar)) *
        (B : ℝ) * p.β ^ Nat.dist r k := by
  classical
  obtain ⟨e⟩ := pe8t_coordinate_equiv B hB
  obtain ⟨N, hNm, hN⟩ := pe8t_chain_function p Cv D e
  let ξ : ℕ → Ω → Vec m × Vec n := fun l =>
    Sum.elim (fun q : ℕ × Fin B => cs.act ((t : ℤ) + q.1 + 1) q.2)
      (fun q : ℕ × Fin B => cs.aux (t : ℤ) q.1 q.2) (e l)
  let ξ' : ℕ → Ω → Vec m × Vec n := fun l =>
    Sum.elim (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 1) q.1 q.2)
      (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 2) q.1 q.2) (e l)
  let w : ℕ → ℕ → ℝ := fun u l =>
    Sum.elim (fun qa : ℕ × Fin B => if qa.1 ≤ u then emaW p.β (u - qa.1) else 0)
      (fun qa : ℕ × Fin B => emaW p.β (qa.1 + u + 1)) (e l)
  obtain ⟨hξ, hξ', hlaw, hind⟩ := pe8t_coordinates cs t e
  have hm : Measurable (fun ω l => ξ l ω) := Measurable.of_eval hξ
  let F : (ℕ → Vec m × Vec n) → ℝ := fun x => f (N k x)
  let G : (ℕ → Vec m × Vec n) → ℝ := fun x => g (N r x)
  have hF : Measurable F := hfm.comp (hNm k)
  have hG : Measurable G := hgm.comp (hNm r)
  have hF2 : MemLp (fun ω => F (fun l => ξ l ω)) 2 P :=
    MemLp.of_bound (hF.comp hm).aestronglyMeasurable bf
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbf (N k _))
  have hG2 : MemLp (fun ω => G (fun l => ξ l ω)) 2 P :=
    MemLp.of_bound (hG.comp hm).aestronglyMeasurable bg
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbg (N r _))
  let A : ℝ := Lf * (14 * p.CSig * p.γstar)
  let C : ℝ := Lg * (14 * p.CSig * p.γstar)
  have hmoment : 0 ≤ 14 * p.CSig * p.γstar :=
    mul_nonneg (mul_nonneg (by norm_num) (le_trans zero_le_one p.hC)) p.hγ
  have hA : 0 ≤ A := mul_nonneg hLf hmoment
  have hC : 0 ≤ C := mul_nonneg hLg hmoment
  have hFa := pe8t_observable_replacement p Cv cs t D hD hB hsize e N hNm hN f hfm Lf hLf hfL k
  have hGb := pe8t_observable_replacement p Cv cs t D hD hB hsize e N hNm hN g hgm Lg hLg hgL r
  have hsum : (∑' l : ℕ,
      (ENNReal.ofReal A * ENNReal.ofReal (w k l)) *
      (ENNReal.ofReal C * ENNReal.ofReal (w r l))) ≤
      ENNReal.ofReal (A * C * (B : ℝ) * p.β ^ Nat.dist r k) := by
    calc
      _ = (ENNReal.ofReal A * ENNReal.ofReal C) *
          ∑' l : ℕ, ENNReal.ofReal (w k l) * ENNReal.ofReal (w r l) := by
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro l
        ring
      _ ≤ (ENNReal.ofReal A * ENNReal.ofReal C) *
          ((B : ℝ≥0∞) * ENNReal.ofReal (p.β ^ Nat.dist r k)) :=
        mul_le_mul_right (pe8t_causal_weight_overlap p B k r e) _
      _ = _ := by
        rw [← ENNReal.ofReal_natCast B]
        rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ B by positivity),
          ← ENNReal.ofReal_mul (mul_nonneg hA hC)]
        congr 1
        ring
  have hb := pe8t_covariance_of_replacements P ξ ξ' hξ hξ' hlaw hind F G hF hG hF2 hG2
    (fun l => ENNReal.ofReal A * ENNReal.ofReal (w k l))
    (fun l => ENNReal.ofReal C * ENNReal.ofReal (w r l))
    (A * C * (B : ℝ) * p.β ^ Nat.dist r k)
    (by
      exact mul_nonneg (mul_nonneg (mul_nonneg hA hC) (Nat.cast_nonneg B))
        (pow_nonneg p.hβ.1 _)) hFa hGb hsum
  have hDp : 0 < riskSigma Cv D := by rw [hD]; norm_num
  have hae0 := pe8t_chain_function_ae p Cv cs t D hDp hsize e N hN
  have hae : ∀ᵐ ω ∂P, ∀ u, N u (fun l => ξ l ω) = stationaryN p Cv cs t D u ω := by
    filter_upwards [hae0] with ω hω
    intro u
    convert hω u using 1
    congr 1
    funext l
    dsimp only [ξ]
    cases e l <;> rfl
  have heF : (fun ω => F (fun l => ξ l ω)) =ᵐ[P]
      (fun ω => f (stationaryN p Cv cs t D k ω)) := by
    filter_upwards [hae] with ω hω
    exact congrArg f (hω k)
  have heG : (fun ω => G (fun l => ξ l ω)) =ᵐ[P]
      (fun ω => g (stationaryN p Cv cs t D r ω)) := by
    filter_upwards [hae] with ω hω
    exact congrArg g (hω r)
  simpa only [pe8t_covariance_congr_ae heF heG] using hb

/-- The normalized deleted sample is exactly one physical batch summand. -/
private lemma pe8t_sample_term {m n B : ℕ} (Cv : Covariances m n) (D : Mat m n)
    (hB : 0 < B) (hD : riskSigma Cv D = 1 / 2) (z : Vec m × Vec n) :
    ((B : ℝ)⁻¹ * resid D (phys Cv z)) • outer (phys Cv z).1 (phys Cv z).2 =
      resid (Ahat Cv D) z • outer (sampU Cv B z) (sampV Cv B z) := by
  rw [pe8s_Ahat_eq Cv D hD, pe8q_outer_samp Cv hB, smul_smul]
  congr 1
  rw [eqn_app_setup_whitened_resid]
  change (B : ℝ)⁻¹ * resid (Arot Cv D) z = resid (Arot Cv D) z * (B : ℝ)⁻¹
  ring

/-- The same covariance decay holds when one actual sample is deleted from
the second buffer. -/
private lemma pe8t_minor_covariance {m n B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (p : DynParams) (Cv : Covariances m n) (cs : ChainSamples P m n B)
    (t k j r : ℕ) (a : Fin B) (hjr : j ≤ r) (D : Mat m n) (hD : riskSigma Cv D = 1 / 2) (hB : 0 < B)
    (hsize : Muon.Volatility.SizeFin Cv B p.γstar p.CSig)
    (f g : Mat m n → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (bf bg Lf Lg : ℝ) (hbf : ∀ K, |f K| ≤ bf) (hbg : ∀ K, |g K| ≤ bg)
    (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hfL : ∀ K K', |f K - f K'| ≤ Lf * nuc (K - K'))
    (hgL : ∀ K K', |g K - g K'| ≤ Lg * nuc (K - K')) :
    |covariance (fun ω => f (stationaryN p Cv cs t D k ω))
      (fun ω => g (sampleRemainder p Cv cs t j r D a ω)) P| ≤
      (Lf * (14 * p.CSig * p.γstar)) * (Lg * (14 * p.CSig * p.γstar)) *
        (B : ℝ) * p.β ^ Nat.dist r k := by
  classical
  obtain ⟨e⟩ := pe8t_coordinate_equiv B hB
  obtain ⟨N, hNm, hN⟩ := pe8t_chain_function p Cv D e
  let ξ : ℕ → Ω → Vec m × Vec n := fun l =>
    Sum.elim (fun q : ℕ × Fin B => cs.act ((t : ℤ) + q.1 + 1) q.2)
      (fun q : ℕ × Fin B => cs.aux (t : ℤ) q.1 q.2) (e l)
  let ξ' : ℕ → Ω → Vec m × Vec n := fun l =>
    Sum.elim (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 1) q.1 q.2)
      (fun q : ℕ × Fin B => cs.aux ((t : ℤ) + 2) q.1 q.2) (e l)
  let w : ℕ → ℕ → ℝ := fun u l =>
    Sum.elim (fun qa : ℕ × Fin B => if qa.1 ≤ u then emaW p.β (u - qa.1) else 0)
      (fun qa : ℕ × Fin B => emaW p.β (qa.1 + u + 1)) (e l)
  obtain ⟨hξ, hξ', hlaw, hind⟩ := pe8t_coordinates cs t e
  have hm : Measurable (fun ω l => ξ l ω) := Measurable.of_eval hξ
  let F : (ℕ → Vec m × Vec n) → ℝ := fun x => f (N k x)
  let τ : Vec m × Vec n → Mat m n := fun z =>
    ((B : ℝ)⁻¹ * resid D (phys Cv z)) • outer (phys Cv z).1 (phys Cv z).2
  let M : (ℕ → Vec m × Vec n) → Mat m n := fun x =>
    N r x - emaW p.β (r - j) • τ (x (e.symm (Sum.inl (j, a))))
  have hτm : Measurable τ := by
    have hc : Continuous τ := by unfold τ resid phys outer; fun_prop
    exact hc.measurable
  have hMm : Measurable M :=
    (hNm r).sub ((hτm.comp (measurable_pi_apply (e.symm (Sum.inl (j, a))))).const_smul (emaW p.β (r - j)))
  let G : (ℕ → Vec m × Vec n) → ℝ := fun x => g (M x)
  have hF : Measurable F := hfm.comp (hNm k)
  have hG : Measurable G := hgm.comp hMm
  have hF2 : MemLp (fun ω => F (fun l => ξ l ω)) 2 P :=
    MemLp.of_bound (hF.comp hm).aestronglyMeasurable bf
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbf (N k _))
  have hG2 : MemLp (fun ω => G (fun l => ξ l ω)) 2 P :=
    MemLp.of_bound (hG.comp hm).aestronglyMeasurable bg
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbg (M _))
  let A : ℝ := Lf * (14 * p.CSig * p.γstar)
  let C : ℝ := Lg * (14 * p.CSig * p.γstar)
  have hmoment : 0 ≤ 14 * p.CSig * p.γstar :=
    mul_nonneg (mul_nonneg (by norm_num) (le_trans zero_le_one p.hC)) p.hγ
  have hA : 0 ≤ A := mul_nonneg hLf hmoment
  have hC : 0 ≤ C := mul_nonneg hLg hmoment
  have hFa := pe8t_observable_replacement p Cv cs t D hD hB hsize e N hNm hN f hfm Lf hLf hfL k
  have hGb := pe8t_minor_observable_replacement p Cv cs t D hD hB hsize e N hNm hN j a g hgm Lg hLg hgL r hjr
  have hsum : (∑' l : ℕ,
      (ENNReal.ofReal A * ENNReal.ofReal (w k l)) *
      (ENNReal.ofReal C * ENNReal.ofReal (w r l))) ≤
      ENNReal.ofReal (A * C * (B : ℝ) * p.β ^ Nat.dist r k) := by
    calc
      _ = (ENNReal.ofReal A * ENNReal.ofReal C) *
          ∑' l : ℕ, ENNReal.ofReal (w k l) * ENNReal.ofReal (w r l) := by
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro l
        ring
      _ ≤ (ENNReal.ofReal A * ENNReal.ofReal C) *
          ((B : ℝ≥0∞) * ENNReal.ofReal (p.β ^ Nat.dist r k)) :=
        mul_le_mul_right (pe8t_causal_weight_overlap p B k r e) _
      _ = _ := by
        rw [← ENNReal.ofReal_natCast B]
        rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ B by positivity),
          ← ENNReal.ofReal_mul (mul_nonneg hA hC)]
        congr 1
        ring
  have hb := pe8t_covariance_of_replacements P ξ ξ' hξ hξ' hlaw hind F G hF hG hF2 hG2
    (fun l => ENNReal.ofReal A * ENNReal.ofReal (w k l))
    (fun l => ENNReal.ofReal C * ENNReal.ofReal (w r l))
    (A * C * (B : ℝ) * p.β ^ Nat.dist r k)
    (by
      exact mul_nonneg (mul_nonneg (mul_nonneg hA hC) (Nat.cast_nonneg B))
        (pow_nonneg p.hβ.1 _)) hFa hGb hsum
  have hDp : 0 < riskSigma Cv D := by rw [hD]; norm_num
  have hae0 := pe8t_chain_function_ae p Cv cs t D hDp hsize e N hN
  have hae : ∀ᵐ ω ∂P, ∀ u, N u (fun l => ξ l ω) = stationaryN p Cv cs t D u ω := by
    filter_upwards [hae0] with ω hω
    intro u
    convert hω u using 1
    congr 1
    funext l
    dsimp only [ξ]
    cases e l <;> rfl
  have heF : (fun ω => F (fun l => ξ l ω)) =ᵐ[P]
      (fun ω => f (stationaryN p Cv cs t D k ω)) := by
    filter_upwards [hae] with ω hω
    exact congrArg f (hω k)
  have heG : (fun ω => G (fun l => ξ l ω)) =ᵐ[P]
      (fun ω => g (sampleRemainder p Cv cs t j r D a ω)) := by
    filter_upwards [hae] with ω hω
    apply congrArg g
    change N r (fun l => ξ l ω) - emaW p.β (r - j) •
      τ (ξ (e.symm (Sum.inl (j, a))) ω) = _
    rw [hω r]
    unfold sampleRemainder
    congr 1
    simp only [ξ, e.apply_symm_apply, Sum.elim_inl]
    rw [show τ (cs.act ((t : ℤ) + j + 1) a ω) =
      resid (Ahat Cv D) (cs.act ((t : ℤ) + j + 1) a ω) •
        outer (sampU Cv B (cs.act ((t : ℤ) + j + 1) a ω))
          (sampV Cv B (cs.act ((t : ℤ) + j + 1) a ω)) from
      pe8t_sample_term Cv D hB hD _]
    rw [mul_smul]
  simpa only [pe8t_covariance_congr_ae heF heG] using hb

private lemma pe8t_entry_le_fro {m n : ℕ} (M : Mat m n) (i : Fin m) (j : Fin n) :
    |M i j| ≤ fro M := by
  have hs : (M i j) ^ 2 ≤ ∑ a : Fin m, ∑ b : Fin n, (M a b) ^ 2 :=
    (Finset.single_le_sum (fun b _ => sq_nonneg (M i b)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg (M a b))
        (Finset.mem_univ i))
  have hnn : 0 ≤ ∑ a : Fin m, ∑ b : Fin n, (M a b) ^ 2 := by positivity
  have hsq := Real.sq_sqrt hnn
  have hf : 0 ≤ fro M := pe8s_fro_nonneg M
  simp only [fro, Real.norm_eq_abs, sq_abs]
  nlinarith [sq_abs (M i j), Real.sqrt_nonneg (∑ a : Fin m, ∑ b : Fin n, (M a b) ^ 2)]

/-- Entrywise integration commutes with a deterministic Frobenius pairing. -/
private lemma pe8t_frobIP_mean {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Mat m n) (M : Ω → Mat m n)
    (hM : ∀ i j, Integrable (fun ω => M ω i j) P) :
    Integrable (fun ω => frobIP A (M ω)) P ∧
      (∫ ω, frobIP A (M ω) ∂P) = frobIP A (mean P M) := by
  have hentry : ∀ i j, Integrable (fun ω => A i j * M ω i j) P :=
    fun i j => (hM i j).const_mul (A i j)
  constructor
  · unfold frobIP Matrix.trace
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hentry i j
  · simp only [frobIP, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, mean, Matrix.of_apply]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hentry i j)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finset_sum _ (fun j _ => hentry i j)]
    simp only [integral_const_mul]

/-- A uniform Frobenius bound ensures all matrix entries are integrable. -/
private lemma pe8t_entries_integrable {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : Ω → Mat m n)
    (hM : AEMeasurable M P) (C : ℝ) (hC : ∀ ω, fro (M ω) ≤ C) :
    ∀ i j, Integrable (fun ω => M ω i j) P := by
  intro i j
  have hm : AEStronglyMeasurable (fun ω => M ω i j) P :=
    ((show Measurable (fun K : Mat m n => K i j) from
      (show Continuous (fun K : Mat m n => K i j) by fun_prop).measurable).comp_aemeasurable hM).aestronglyMeasurable
  exact Integrable.of_bound hm C (Eventually.of_forall fun ω =>
    by simpa only [Real.norm_eq_abs] using (pe8t_entry_le_fro (M ω) i j).trans (hC ω))

/-- The scalar means needed in both contractions are bounded independently of
batch size, dimension, and momentum. -/
private lemma pe8t_stationary_scalar_means (γ CS ϱ cP : ℝ) :
    ∃ C : ℝ, ∀ (p : DynParams), p.γstar = γ → p.CSig = CS → p.ϱ = ϱ →
      ∀ (m n B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (Cv : Covariances m n) (cs : ChainSamples P m n B)
      (t k r : ℕ) (D Pt : Mat m n),
      ((max m n : ℕ) : ℝ) ≤ p.γstar * B →
      opNorm Cv.Sout ≤ p.CSig → opNorm Cv.Sin ≤ p.CSig → 0 < B →
      riskSigma Cv D = 1 / 2 → fro Pt ≤ cP →
      Integrable (fun ω => pairSigma Cv D (stationaryV p Cv cs t D k ω)) P ∧
      Integrable (fun ω => frobIP Pt (ridgeDeriv p.ϱ (stationaryN p Cv cs t D r ω))) P ∧
      |∫ ω, pairSigma Cv D (stationaryV p Cv cs t D k ω) ∂P| ≤ C ∧
      |∫ ω, frobIP Pt (ridgeDeriv p.ϱ (stationaryN p Cv cs t D r ω)) ∂P| ≤ C := by
  obtain ⟨CM, hCM⟩ := eqn_app_dyn_mean_physical_fin γ CS ϱ
  refine ⟨max (CS * max CM 0) (cP * max CM 0), ?_⟩
  intro p hpγ hpCS hpϱ m n B Ω _ P _ Cv cs t k r D Pt hdim hCo hCi hB hD hP
  have hDp : 0 < riskSigma Cv D := by rw [hD]; norm_num
  have hsize : Muon.Volatility.SizeFin Cv B p.γstar p.CSig :=
    ⟨by simpa [Nat.cast_max] using hdim, hCo, hCi⟩
  have hNm := pe8q_stationaryN_aestronglyMeasurable p Cv cs t D hDp hsize
  have hQm : Measurable (Q p.ϱ : Mat m n → Mat m n) :=
    measurable_Q.comp
      ((measurable_const (a := (⟨p.ϱ, p.hϱ.le⟩ : Ici (0 : ℝ)))).prodMk measurable_id)
  have hVeq : stationaryV p Cv cs t D k =
      fun ω => Q p.ϱ (stationaryN p Cv cs t D k ω) := by
    funext ω
    change Q (physRidge p Cv D) _ = _
    rw [show physRidge p Cv D = p.ϱ by simp [physRidge, hD]]
    rfl
  have hVm : AEMeasurable (stationaryV p Cv cs t D k) P := by
    rw [hVeq]
    exact hQm.comp_aemeasurable (hNm k).aemeasurable
  have hVb : ∀ ω, fro (stationaryV p Cv cs t D k ω) ≤ Real.sqrt n := by
    intro ω
    rw [hVeq]
    exact (pe8m_fro_le_sqrt_cols_op_copy _).trans (by
      simpa using mul_le_mul_of_nonneg_left
        (lem_app_setup_filter_i p.ϱ p.hϱ.le (stationaryN p Cv cs t D k ω)).1 (Real.sqrt_nonneg (n : ℝ)))
  have hRm : AEMeasurable
      (fun ω => ridgeDeriv p.ϱ (stationaryN p Cv cs t D r ω)) P :=
    (pe8t_measurable_ridgeDeriv p.ϱ p.hϱ).comp_aemeasurable (hNm r).aemeasurable
  obtain ⟨CR, hCR⟩ := lem_app_dyn_second_iv (ℓlo := p.ϱ) (ℓhi := p.ϱ) p.hϱ le_rfl
  have hRb : ∀ ω, fro (ridgeDeriv p.ϱ (stationaryN p Cv cs t D r ω)) ≤
      CR * Real.sqrt ((min m n : ℕ) : ℝ) := by
    intro ω
    have h := (hCR p.ϱ ⟨le_rfl, le_rfl⟩ (stationaryN p Cv cs t D r ω) 0).2.1
    exact (le_add_of_nonneg_right (pe8s_fro_nonneg _)).trans h
  have hVint := pe8t_frobIP_mean P (Cv.Sout * D * Cv.Sin) (stationaryV p Cv cs t D k)
    (pe8t_entries_integrable P _ hVm _ hVb)
  have hRint := pe8t_frobIP_mean P Pt (fun ω => ridgeDeriv p.ϱ (stationaryN p Cv cs t D r ω))
    (pe8t_entries_integrable P _ hRm _ hRb)
  have hmeans := hCM p hpγ hpCS hpϱ m n B Ω P Cv cs t k r D hdim hCo hCi hB hD
  have hA : fro (Cv.Sout * D * Cv.Sin) ≤ p.CSig := by
    have he : Arot Cv (Arot Cv D) = Cv.Sout * D * Cv.Sin := by
      unfold Arot
      calc
        _ = (rOut Cv * rOut Cv) * D * (rIn Cv * rIn Cv) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [pe8s_rOut_sq, pe8s_rIn_sq]
    have h := (pe8s_Arot_bounds Cv p.CSig hCo hCi (Arot Cv D)).1
    rw [he, ← pe8s_Ahat_eq Cv D hD, pe8q_Ahat_fro Cv D hDp, mul_one] at h
    exact h
  refine ⟨hVint.1, hRint.1, ?_, ?_⟩
  · change |∫ ω, frobIP (Cv.Sout * D * Cv.Sin) (stationaryV p Cv cs t D k ω) ∂P| ≤ _
    rw [hVint.2]
    exact ((pe8m_frobIP_le_copy _ _).trans
      (mul_le_mul (by simpa only [hpCS] using hA) (hmeans.1.trans (le_max_left _ _))
        (pe8s_fro_nonneg _) (by simpa only [hpCS] using le_trans zero_le_one p.hC))).trans
      (le_max_left _ _)
  · rw [hRint.2]
    exact ((pe8m_frobIP_le_copy _ _).trans
      (mul_le_mul hP (hmeans.2.trans (le_max_left _ _)) (pe8s_fro_nonneg _)
        ((pe8s_fro_nonneg Pt).trans hP))).trans (le_max_right _ _)

private lemma pe8t_g_bound {m n : ℕ} (p : DynParams) (Cv : Covariances m n)
    (D : Mat m n) (hCo : opNorm Cv.Sout ≤ p.CSig) (hCi : opNorm Cv.Sin ≤ p.CSig)
    (hD : riskSigma Cv D = 1 / 2) (K : Mat m n) :
    |pairSigma Cv D (Q p.ϱ K)| ≤ p.CSig * Real.sqrt n := by
  have hDp : 0 < riskSigma Cv D := by rw [hD]; norm_num
  have hCS : 0 ≤ p.CSig := le_trans zero_le_one p.hC
  rw [pe8s_pairSigma_eq, ← pe8s_Ahat_eq Cv D hD]
  refine (pe8m_frobIP_le_copy _ _).trans ?_
  rw [pe8q_Ahat_fro Cv D hDp, one_mul]
  calc
    _ ≤ p.CSig * fro (Q p.ϱ K) := (pe8s_Arot_bounds Cv p.CSig hCo hCi _).1
    _ ≤ p.CSig * (Real.sqrt n * opNorm (Q p.ϱ K)) :=
      mul_le_mul_of_nonneg_left (pe8m_fro_le_sqrt_cols_op_copy _) hCS
    _ ≤ p.CSig * (Real.sqrt n * 1) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (lem_app_setup_filter_i p.ϱ p.hϱ.le K).1 (Real.sqrt_nonneg _)) hCS
    _ = _ := by ring

private lemma pe8t_integral_mul_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f g : Ω → ℝ)
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) (A B C : ℝ)
    (hcov : |covariance f g P| ≤ A) (hmf : |∫ ω, f ω ∂P| ≤ B)
    (hmg : |∫ ω, g ω ∂P| ≤ C) :
    |∫ ω, f ω * g ω ∂P| ≤ A + B * C := by
  have he : (∫ ω, f ω * g ω ∂P) = covariance f g P +
      (∫ ω, f ω ∂P) * (∫ ω, g ω ∂P) := by
    simp only [covariance_eq_sub hf hg, Pi.mul_apply, sub_add_cancel]
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hcov (by
    rw [abs_mul]
    exact mul_le_mul hmf hmg (abs_nonneg _) ((abs_nonneg _).trans hmf)))

private lemma pe8t_scalar_coefficient (B : ℕ) (hB : 0 < B) (δ π : ℝ) (hδ : 0 ≤ δ) :
    (B : ℝ) * δ * (π + (B : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      1 + (B : ℝ) * (δ * (π + δ)) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  rw [pe8m_rpow_mhalf B hBr]
  have hsqrt : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBr
  have he : (B : ℝ) * δ * (π + 1 / Real.sqrt B) =
      (B : ℝ) * δ * π + Real.sqrt B * δ := by
    field_simp [hsqrt.ne']
    nlinarith [show (Real.sqrt (B : ℝ)) ^ 2 * δ = (B : ℝ) * δ by rw [Real.sq_sqrt hBr.le]]
  rw [he]
  have hsδ : (Real.sqrt (B : ℝ) * δ) ^ 2 = (B : ℝ) * δ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hBr.le]
  nlinarith [sq_nonneg (Real.sqrt B * δ - 1), mul_nonneg hBr.le (sq_nonneg δ)]

/-- Integrability of the product `F_s(T_a) g_k` of `prop_app_dyn_scalar`: `F_s` is bounded by
`lem_app_dyn_minor`, and `|g_k| ≤ C_Σ √n` since `‖V_k‖ ≤ 1`. -/
private lemma pe8t_scalar_int {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : DynParams) (Cv : Covariances m n) (cs : ChainSamples P m n B)
    (t k j r : ℕ) (D Pt : Mat m n) (piT s s0 cP : ℝ) (a : Fin B) (hs0 : 0 < s0) (hs : s0 ≤ s)
    (hm : (m : ℝ) ≤ p.γstar * B) (hn : (n : ℝ) ≤ p.γstar * B)
    (hCo : opNorm Cv.Sout ≤ p.CSig) (hCi : opNorm Cv.Sin ≤ p.CSig) (hB : 0 < B)
    (hD : riskSigma Cv D = 1 / 2) (hP : IsTest cP piT Pt) :
    Integrable (fun ω => Fs Cv B (Ahat Cv D) Pt (emaW p.β (r - j)) s
        (sampleRemainder p Cv cs t j r D a ω) * pairSigma Cv D (stationaryV p Cv cs t D k ω)) P := by
  have hs_pos : 0 < s := lt_of_lt_of_le hs0 hs
  have hDpos : 0 < riskSigma Cv D := by rw [hD]; norm_num
  have hAh : fro (Ahat Cv D) = 1 := pe8q_Ahat_fro Cv D hDpos
  have hϖ : emaW p.β (r - j) ∈ Icc (0 : ℝ) 1 := pe8q_emaW_mem_Icc p (r - j)
  have hsize : Muon.Volatility.SizeFin Cv B p.γstar p.CSig :=
    ⟨by rw [Nat.cast_max]; exact max_le hm hn, hCo, hCi⟩
  obtain ⟨CF, hCF⟩ := lem_app_dyn_minor cP p.γstar p.CSig s0 hs0
  have hFb : ∀ T : Mat m n, |Fs Cv B (Ahat Cv D) Pt (emaW p.β (r - j)) s T| ≤
      CF * Real.sqrt B * s ^ (-(3 / 2 : ℝ)) := fun T =>
    (hCF m n B Cv (Ahat Cv D) Pt T T (emaW p.β (r - j)) s piT hB hCo hCi hm hn hAh hP hϖ hs).2.1
  have hFc := pe8s_cont_Fs Cv (Ahat Cv D) Pt (emaW p.β (r - j)) s hs_pos hB hAh
  have hN := pe8q_stationaryN_aestronglyMeasurable p Cv cs t D hDpos hsize
  have hSR : AEStronglyMeasurable (sampleRemainder p Cv cs t j r D a) P := by
    have hc : Continuous (fun x : Vec m × Vec n => (emaW p.β (r - j) * resid (Ahat Cv D) x) •
        outer (sampU Cv B x) (sampV Cv B x)) := by
      unfold resid sampU sampV outer; fun_prop
    exact (hN r).sub (hc.measurable.comp (cs.meas_act _ a)).aestronglyMeasurable
  have hρ : (0 : ℝ) ≤ physRidge p Cv D := by
    unfold physRidge; rw [hD]; have := p.hϱ; positivity
  have hQm : Measurable (fun K : Mat m n => Q (physRidge p Cv D) K) :=
    (measurable_Q (m := m) (n := n)).comp
      ((measurable_const (a := (⟨physRidge p Cv D, hρ⟩ : Ici (0 : ℝ)))).prodMk measurable_id)
  have hgc : Continuous (fun M : Mat m n => pairSigma Cv D M) := by unfold pairSigma; fun_prop
  have hV : AEStronglyMeasurable (fun ω => pairSigma Cv D (stationaryV p Cv cs t D k ω)) P := by
    change AEStronglyMeasurable
      (fun ω => pairSigma Cv D (Q (physRidge p Cv D) (stationaryN p Cv cs t D k ω))) P
    exact ((hgc.measurable.comp hQm).comp_aemeasurable (hN k).aemeasurable).aestronglyMeasurable
  have hCS0 : 0 ≤ p.CSig := le_trans zero_le_one p.hC
  have hg : ∀ K : Mat m n, |pairSigma Cv D (Q (physRidge p Cv D) K)| ≤ p.CSig * Real.sqrt n := by
    intro K
    rw [pe8s_pairSigma_eq, ← pe8s_Ahat_eq Cv D hD]
    refine (pe8m_frobIP_le_copy _ _).trans ?_
    rw [hAh, one_mul]
    have hQ := (lem_app_setup_filter_i (physRidge p Cv D) hρ K).1
    calc fro (Arot Cv (Q (physRidge p Cv D) K)) ≤ p.CSig * fro (Q (physRidge p Cv D) K) :=
          (pe8s_Arot_bounds Cv p.CSig hCo hCi _).1
      _ ≤ p.CSig * (Real.sqrt n * opNorm (Q (physRidge p Cv D) K)) :=
          mul_le_mul_of_nonneg_left (pe8m_fro_le_sqrt_cols_op_copy _) hCS0
      _ ≤ p.CSig * (Real.sqrt n * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ (Real.sqrt_nonneg _)) hCS0
      _ = p.CSig * Real.sqrt n := by ring
  refine Integrable.of_bound ((hFc.comp_aestronglyMeasurable hSR).mul hV)
    (CF * Real.sqrt B * s ^ (-(3 / 2 : ℝ)) * (p.CSig * Real.sqrt n))
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hFb _) (hg _) (abs_nonneg _) ((abs_nonneg _).trans (hFb 0))

private lemma pe8t_ridge_int {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : DynParams) (Cv : Covariances m n) (cs : ChainSamples P m n B)
    (t k r : ℕ) (D Pt : Mat m n) (piT cP : ℝ)
    (hm : (m : ℝ) ≤ p.γstar * B) (hn : (n : ℝ) ≤ p.γstar * B)
    (hCo : opNorm Cv.Sout ≤ p.CSig) (hCi : opNorm Cv.Sin ≤ p.CSig) (hB : 0 < B)
    (hD : riskSigma Cv D = 1 / 2) (hP : IsTest cP piT Pt) :
    Integrable (fun ω => pairSigma Cv D (stationaryV p Cv cs t D k ω) *
        frobIP Pt (ridgeDeriv p.ϱ (stationaryN p Cv cs t D r ω))) P := by
  have hDp : 0 < riskSigma Cv D := by rw [hD]; norm_num
  have hsize : Muon.Volatility.SizeFin Cv B p.γstar p.CSig :=
    ⟨by rw [Nat.cast_max]; exact max_le hm hn, hCo, hCi⟩
  have hN := pe8q_stationaryN_aestronglyMeasurable p Cv cs t D hDp hsize
  have hQm : Measurable (fun K : Mat m n => Q p.ϱ K) :=
    measurable_Q.comp
      ((measurable_const (a := (⟨p.ϱ, p.hϱ.le⟩ : Ici (0 : ℝ)))).prodMk measurable_id)
  have hgc : Continuous (fun M : Mat m n => pairSigma Cv D M) := by
    unfold pairSigma
    fun_prop
  have hVeq : stationaryV p Cv cs t D k =
      fun ω => Q p.ϱ (stationaryN p Cv cs t D k ω) := by
    funext ω
    change Q (physRidge p Cv D) _ = _
    rw [show physRidge p Cv D = p.ϱ by simp [physRidge, hD]]
    rfl
  have hgmeas : AEStronglyMeasurable
      (fun ω => pairSigma Cv D (stationaryV p Cv cs t D k ω)) P := by
    rw [hVeq]
    exact ((hgc.measurable.comp hQm).comp_aemeasurable (hN k).aemeasurable).aestronglyMeasurable
  have hRD := pe8t_measurable_ridgeDeriv (m := m) (n := n) p.ϱ p.hϱ
  have hfc : Continuous (fun M : Mat m n => frobIP Pt M) := by
    unfold frobIP
    fun_prop
  have hfmeas : AEStronglyMeasurable
      (fun ω => frobIP Pt (ridgeDeriv p.ϱ (stationaryN p Cv cs t D r ω))) P :=
    ((hfc.measurable.comp hRD).comp_aemeasurable (hN r).aemeasurable).aestronglyMeasurable
  obtain ⟨CR, hCR⟩ := lem_app_dyn_second_iv (ℓlo := p.ϱ) (ℓhi := p.ϱ) p.hϱ le_rfl
  have hCS0 : 0 ≤ p.CSig := le_trans zero_le_one p.hC
  have hAh : fro (Ahat Cv D) = 1 := pe8q_Ahat_fro Cv D hDp
  have hg : ∀ K : Mat m n, |pairSigma Cv D (Q p.ϱ K)| ≤ p.CSig * Real.sqrt n := by
    intro K
    rw [pe8s_pairSigma_eq, ← pe8s_Ahat_eq Cv D hD]
    refine (pe8m_frobIP_le_copy _ _).trans ?_
    rw [hAh, one_mul]
    have hQ := (lem_app_setup_filter_i p.ϱ p.hϱ.le K).1
    calc
      fro (Arot Cv (Q p.ϱ K)) ≤ p.CSig * fro (Q p.ϱ K) :=
        (pe8s_Arot_bounds Cv p.CSig hCo hCi _).1
      _ ≤ p.CSig * (Real.sqrt n * opNorm (Q p.ϱ K)) :=
        mul_le_mul_of_nonneg_left (pe8m_fro_le_sqrt_cols_op_copy _) hCS0
      _ ≤ p.CSig * (Real.sqrt n * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hQ (Real.sqrt_nonneg _)) hCS0
      _ = p.CSig * Real.sqrt n := by ring
  have hf : ∀ K : Mat m n,
      |frobIP Pt (ridgeDeriv p.ϱ K)| ≤ cP * (CR * Real.sqrt ((min m n : ℕ) : ℝ)) := by
    intro K
    refine (pe8m_frobIP_le_copy _ _).trans ?_
    have hR := (hCR p.ϱ ⟨le_rfl, le_rfl⟩ K K).2.1
    have hR0 : 0 ≤ fro (ridgeDeriv2 p.ϱ K) := pe8s_fro_nonneg _
    have hR' : fro (ridgeDeriv p.ϱ K) ≤ CR * Real.sqrt ((min m n : ℕ) : ℝ) := by
      linarith
    exact mul_le_mul hP.1 hR' (pe8s_fro_nonneg _) (le_trans (pe8s_fro_nonneg _) hP.1)
  refine Integrable.of_bound (hgmeas.mul hfmeas)
    ((p.CSig * Real.sqrt n) * (cP * (CR * Real.sqrt ((min m n : ℕ) : ℝ))))
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  rw [hVeq]
  exact mul_le_mul (hg (stationaryN p Cv cs t D k ω))
      (hf (stationaryN p Cv cs t D r ω)) (abs_nonneg _) ((abs_nonneg _).trans (hg 0))

/-- `prop:app-dyn-scalar`, snapshot `cr-2026-10-23`. Statement verbatim from `section.tex` (ll. 1353–1362):
```latex
\begin{proposition}[Scalar contraction]\label{prop:app-dyn-scalar}
In the setting of \cref{prop:app-dyn-reduction}, let $0\le k<j$ and
$g_k\defeq g(V_k)=\langle\Sigmaout D\Sigmain,V_k\rangle$. Then for every
sample $a$ of the batch of step $t+j$,
\[
\big|\EE\big[F_s(T_a)\,g_k\big]\big|\le C\Big\{\sqrt B\,s^{-3/2}+\big(1+B\epsilon_\Pi\big)s^{-2}\bmom^{r-k}\Big\},
\]
with $C$ depending only on $(s_\circ,c_\Pi,\ridge,\gamma_\star,C_\Sigma)$.
No independence between $V_k$ and the traces of the minor is used.
\end{proposition}
```
-/
theorem prop_app_dyn_scalar (γ CS ϱ s0 cP : ℝ) (hs0 : 0 < s0) :
    ∃ C : ℝ, ∀ (p : DynParams), p.γstar = γ → p.CSig = CS → p.ϱ = ϱ → ∀ (m n B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (Cv : Covariances m n) (cs : ChainSamples P m n B)
      (t k j r : ℕ) (D Pt : Mat m n) (piT s : ℝ) (a : Fin B),
      (m : ℝ) ≤ p.γstar * B → (n : ℝ) ≤ p.γstar * B →
      opNorm Cv.Sout ≤ p.CSig → opNorm Cv.Sin ≤ p.CSig → 0 < B →
      riskSigma Cv D = 1 / 2 → IsTest cP piT Pt → k < j → j ≤ r → s0 ≤ s →
      Integrable (fun ω => Fs Cv B (Ahat Cv D) Pt (emaW p.β (r - j)) s
          (sampleRemainder p Cv cs t j r D a ω) * pairSigma Cv D (stationaryV p Cv cs t D k ω)) P ∧
      |∫ ω, Fs Cv B (Ahat Cv D) Pt (emaW p.β (r - j)) s
          (sampleRemainder p Cv cs t j r D a ω) * pairSigma Cv D (stationaryV p Cv cs t D k ω) ∂P|
        ≤ C * (Real.sqrt B * s ^ (-(3 / 2 : ℝ))
          + (1 + (B : ℝ) * (diffuseness Cv D * (piT + diffuseness Cv D)))
            * (1 / s ^ 2) * p.β ^ (r - k)) := by
  obtain ⟨CF0, hCF⟩ := lem_app_dyn_minor cP γ CS s0 hs0
  obtain ⟨CM0, hCM⟩ := pe8t_stationary_scalar_means γ CS ϱ cP
  let CF : ℝ := max CF0 0
  let CM : ℝ := max CM0 0
  let K : ℝ := |CS * ϱ ^ (-(1 / 2 : ℝ))| * CF * (14 * CS * γ) ^ 2
  refine ⟨K + CF * CM, ?_⟩
  intro p hpγ hpCS hpϱ m n B Ω _ P _ Cv cs t k j r D Pt piT s a hm hn hCo hCi hB hD hP hkj hjr hs
  subst γ
  subst CS
  subst ϱ
  have hDp : 0 < riskSigma Cv D := by rw [hD]; norm_num
  have hspos : 0 < s := hs0.trans_le hs
  have hAh := pe8q_Ahat_fro Cv D hDp
  have hϖ := pe8q_emaW_mem_Icc p (r - j)
  have hCF0 : 0 ≤ CF := le_max_right _ _
  have hCFle : CF0 ≤ CF := le_max_left _ _
  have hCM0 : 0 ≤ CM := le_max_right _ _
  have hδ : 0 ≤ diffuseness Cv D := pe8_opNorm_nonneg _
  have hpi : 0 ≤ piT := (pe8_opNorm_nonneg Pt).trans hP.2.1
  have hCS : 0 ≤ p.CSig := le_trans zero_le_one p.hC
  have hβ : 0 ≤ p.β := p.hβ.1
  have hpow : 0 ≤ p.ϱ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg p.hϱ.le _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsize : Muon.Volatility.SizeFin Cv B p.γstar p.CSig :=
    ⟨by rw [Nat.cast_max]; exact max_le hm hn, hCo, hCi⟩
  let f : Mat m n → ℝ := fun X => pairSigma Cv D (Q p.ϱ X)
  let g : Mat m n → ℝ := Fs Cv B (Ahat Cv D) Pt (emaW p.β (r - j)) s
  let Lf : ℝ := p.CSig * diffuseness Cv D * p.ϱ ^ (-(1 / 2 : ℝ))
  let Lg : ℝ := CF * (1 / s ^ 2) * (piT + (B : ℝ) ^ (-(1 / 2 : ℝ)))
  have hfm : Measurable f := by
    have hQm : Measurable (Q p.ϱ : Mat m n → Mat m n) := measurable_Q.comp
      ((measurable_const (a := (⟨p.ϱ, p.hϱ.le⟩ : Ici (0 : ℝ)))).prodMk measurable_id)
    exact (show Continuous (fun X : Mat m n => pairSigma Cv D X) by unfold pairSigma; fun_prop).measurable.comp hQm
  have hgc : Continuous g := pe8s_cont_Fs Cv (Ahat Cv D) Pt _ s hspos hB hAh
  have hfb : ∀ X, |f X| ≤ p.CSig * Real.sqrt n := pe8t_g_bound p Cv D hCo hCi hD
  have hgb : ∀ X, |g X| ≤ CF * Real.sqrt B * s ^ (-(3 / 2 : ℝ)) := by
    intro X
    have hb := (hCF m n B Cv (Ahat Cv D) Pt X X _ s piT hB hCo hCi hm hn hAh hP hϖ hs).2.1
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCFle (Real.sqrt_nonneg _)) (Real.rpow_nonneg hspos.le _))
  have hfL : ∀ X Y, |f X - f Y| ≤ Lf * nuc (X - Y) :=
    fun X Y => pe8t_g_lipschitz p Cv D X Y hCo hCi hD
  have hgL : ∀ X Y, |g X - g Y| ≤ Lg * nuc (X - Y) := by
    intro X Y
    have hb := (hCF m n B Cv (Ahat Cv D) Pt X Y _ s piT hB hCo hCi hm hn hAh hP hϖ hs).2.2
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCFle (by positivity))
        (by positivity)) (nuc_nonneg _))
  have hLf : 0 ≤ Lf := mul_nonneg (mul_nonneg hCS hδ) hpow
  have hLg : 0 ≤ Lg := by dsimp [Lg]; positivity
  have hcov := pe8t_minor_covariance p Cv cs t k j r a hjr D hD hB hsize
    f g hfm hgc.measurable (p.CSig * Real.sqrt n)
    (CF * Real.sqrt B * s ^ (-(3 / 2 : ℝ))) Lf Lg hfb hgb hLf hLg hfL hgL
  have hkr : k ≤ r := hkj.le.trans hjr
  have hceq : (Lf * (14 * p.CSig * p.γstar)) * (Lg * (14 * p.CSig * p.γstar)) *
      (B : ℝ) * p.β ^ Nat.dist r k =
      K * ((B : ℝ) * diffuseness Cv D * (piT + (B : ℝ) ^ (-(1 / 2 : ℝ)))) *
        (1 / s ^ 2) * p.β ^ (r - k) := by
    dsimp [Lf, Lg, K]
    rw [abs_of_nonneg (mul_nonneg hCS hpow), Nat.dist_eq_sub_of_le_right hkr]
    ring
  rw [hceq] at hcov
  have hcfinal : |covariance (fun ω => f (stationaryN p Cv cs t D k ω))
      (fun ω => g (sampleRemainder p Cv cs t j r D a ω)) P| ≤
      K * (1 + (B : ℝ) * (diffuseness Cv D * (piT + diffuseness Cv D))) *
        (1 / s ^ 2) * p.β ^ (r - k) := by
    exact hcov.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pe8t_scalar_coefficient B hB _ piT hδ) hK)
        (by positivity)) (pow_nonneg p.hβ.1 _))
  have hN := pe8q_stationaryN_aestronglyMeasurable p Cv cs t D hDp hsize
  have hSR : AEStronglyMeasurable (sampleRemainder p Cv cs t j r D a) P := by
    have hc : Continuous (fun x : Vec m × Vec n => (emaW p.β (r - j) * resid (Ahat Cv D) x) •
        outer (sampU Cv B x) (sampV Cv B x)) := by unfold resid sampU sampV outer; fun_prop
    exact (hN r).sub (hc.measurable.comp (cs.meas_act _ a)).aestronglyMeasurable
  have hf2 : MemLp (fun ω => f (stationaryN p Cv cs t D k ω)) 2 P :=
    MemLp.of_bound (hfm.comp_aemeasurable (hN k).aemeasurable).aestronglyMeasurable _
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hfb (stationaryN p Cv cs t D k ω))
  have hg2 : MemLp (fun ω => g (sampleRemainder p Cv cs t j r D a ω)) 2 P :=
    MemLp.of_bound (hgc.comp_aestronglyMeasurable hSR) _
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hgb (sampleRemainder p Cv cs t j r D a ω))
  have hVeq : (fun ω => f (stationaryN p Cv cs t D k ω)) =
      (fun ω => pairSigma Cv D (stationaryV p Cv cs t D k ω)) := by
    funext ω
    change pairSigma Cv D (Q p.ϱ _) = pairSigma Cv D (Q (physRidge p Cv D) _)
    rw [show physRidge p Cv D = p.ϱ by simp [physRidge, hD]]
    rfl
  have hmeans := hCM p rfl rfl rfl m n B Ω P Cv cs t k r D Pt
    (by rw [Nat.cast_max]; exact max_le hm hn) hCo hCi hB hD hP.1
  have hmf : |∫ ω, f (stationaryN p Cv cs t D k ω) ∂P| ≤ CM := by
    rw [hVeq]
    exact hmeans.2.2.1.trans (le_max_left _ _)
  have hmg : |∫ ω, g (sampleRemainder p Cv cs t j r D a ω) ∂P| ≤
      CF * Real.sqrt B * s ^ (-(3 / 2 : ℝ)) := by
    have hb := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => g (sampleRemainder p Cv cs t j r D a ω))
      (C := CF * Real.sqrt B * s ^ (-(3 / 2 : ℝ)))
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hgb (sampleRemainder p Cv cs t j r D a ω))
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb
  have hb := pe8t_integral_mul_le P _ _ hf2 hg2 _ _ _ hcfinal hmf hmg
  refine ⟨pe8t_scalar_int p Cv cs t k j r D Pt piT s s0 cP a hs0 hs hm hn hCo hCi hB hD hP, ?_⟩
  simp_rw [show ∀ ω, f (stationaryN p Cv cs t D k ω) =
    pairSigma Cv D (stationaryV p Cv cs t D k ω) from fun ω => congrFun hVeq ω] at hb
  have hfinal : |∫ ω, pairSigma Cv D (stationaryV p Cv cs t D k ω) *
      g (sampleRemainder p Cv cs t j r D a ω) ∂P| ≤
      (K + CF * CM) * (Real.sqrt B * s ^ (-(3 / 2 : ℝ)) +
        (1 + (B : ℝ) * (diffuseness Cv D * (piT + diffuseness Cv D))) *
          (1 / s ^ 2) * p.β ^ (r - k)) := by
    refine hb.trans ?_
    have hx : 0 ≤ Real.sqrt B * s ^ (-(3 / 2 : ℝ)) := by positivity
    have hy : 0 ≤ (1 + (B : ℝ) * (diffuseness Cv D * (piT + diffuseness Cv D))) *
        (1 / s ^ 2) * p.β ^ (r - k) := by positivity
    nlinarith [mul_nonneg hK hx, mul_nonneg (mul_nonneg hCF0 hCM0) hy]
  simpa only [g, mul_comm] using hfinal

/-- `lem:app-dyn-ridge`, snapshot `cr-2026-10-23`. Statement verbatim from `section.tex` (ll. 1394–1400):
```latex
\begin{lemma}[Ridge susceptibility covariance]\label{lem:app-dyn-ridge}
Let $D$ be deterministic with $2\cR(D)=1$, consider the stationary chain at
$(t,D)$ and let $k,r\ge0$. Then
\[
\big|\EE\big[g_k\,\big\langle\Pi,\partial_\ell\Qridge\ell(N_r)\big|_{\ell=\ridge}\big\rangle\big]\big|\le C\big(1+B\delta\pi_\Pi\,\bmom^{\abs{r-k}}\big).
\]
\end{lemma}
```
-/
theorem lem_app_dyn_ridge (γ CS ϱ cP : ℝ) :
    ∃ C : ℝ, ∀ (p : DynParams), p.γstar = γ → p.CSig = CS → p.ϱ = ϱ → ∀ (m n B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (Cv : Covariances m n) (cs : ChainSamples P m n B)
      (t k r : ℕ) (D Pt : Mat m n) (piT : ℝ),
      (m : ℝ) ≤ p.γstar * B → (n : ℝ) ≤ p.γstar * B →
      opNorm Cv.Sout ≤ p.CSig → opNorm Cv.Sin ≤ p.CSig → 0 < B →
      riskSigma Cv D = 1 / 2 → IsTest cP piT Pt →
      Integrable (fun ω => pairSigma Cv D (stationaryV p Cv cs t D k ω)
          * frobIP Pt (ridgeDeriv p.ϱ (stationaryN p Cv cs t D r ω))) P ∧
      |∫ ω, pairSigma Cv D (stationaryV p Cv cs t D k ω)
          * frobIP Pt (ridgeDeriv p.ϱ (stationaryN p Cv cs t D r ω)) ∂P|
        ≤ C * (1 + (B : ℝ) * diffuseness Cv D * piT * p.β ^ Nat.dist r k) := by
  obtain ⟨CM0, hCM⟩ := pe8t_stationary_scalar_means γ CS ϱ cP
  let CM : ℝ := max CM0 0
  let K : ℝ := |CS * ϱ ^ (-(1 / 2 : ℝ))| *
    |(1 / 2 : ℝ) * ϱ ^ (-(3 / 2 : ℝ))| * (14 * CS * γ) ^ 2
  refine ⟨K + CM ^ 2, ?_⟩
  intro p hpγ hpCS hpϱ m n B Ω _ P _ Cv cs t k r D Pt piT hm hn hCo hCi hB hD hP
  subst γ
  subst CS
  subst ϱ
  have hDp : 0 < riskSigma Cv D := by rw [hD]; norm_num
  have hCM0 : 0 ≤ CM := le_max_right _ _
  have hδ : 0 ≤ diffuseness Cv D := pe8_opNorm_nonneg _
  have hpi : 0 ≤ piT := (pe8_opNorm_nonneg Pt).trans hP.2.1
  have hCS : 0 ≤ p.CSig := le_trans zero_le_one p.hC
  have hβ : 0 ≤ p.β := p.hβ.1
  have hpow1 : 0 ≤ p.ϱ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg p.hϱ.le _
  have hpow3 : 0 ≤ p.ϱ ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg p.hϱ.le _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsize : Muon.Volatility.SizeFin Cv B p.γstar p.CSig :=
    ⟨by rw [Nat.cast_max]; exact max_le hm hn, hCo, hCi⟩
  let f : Mat m n → ℝ := fun X => pairSigma Cv D (Q p.ϱ X)
  let g : Mat m n → ℝ := fun X => frobIP Pt (ridgeDeriv p.ϱ X)
  let Lf : ℝ := p.CSig * diffuseness Cv D * p.ϱ ^ (-(1 / 2 : ℝ))
  let Lg : ℝ := piT * ((1 / 2 : ℝ) * p.ϱ ^ (-(3 / 2 : ℝ)))
  have hfm : Measurable f := by
    have hQm : Measurable (Q p.ϱ : Mat m n → Mat m n) := measurable_Q.comp
      ((measurable_const (a := (⟨p.ϱ, p.hϱ.le⟩ : Ici (0 : ℝ)))).prodMk measurable_id)
    exact (show Continuous (fun X : Mat m n => pairSigma Cv D X) by
      unfold pairSigma; fun_prop).measurable.comp hQm
  have hgm : Measurable g := by
    exact (show Continuous (fun X : Mat m n => frobIP Pt X) by
      unfold frobIP; fun_prop).measurable.comp (pe8t_measurable_ridgeDeriv p.ϱ p.hϱ)
  have hfb : ∀ X, |f X| ≤ p.CSig * Real.sqrt n := pe8t_g_bound p Cv D hCo hCi hD
  obtain ⟨CR, hCR⟩ := lem_app_dyn_second_iv (ℓlo := p.ϱ) (ℓhi := p.ϱ) p.hϱ le_rfl
  have hgb : ∀ X, |g X| ≤ cP * (CR * Real.sqrt ((min m n : ℕ) : ℝ)) := by
    intro X
    have hb := (hCR p.ϱ ⟨le_rfl, le_rfl⟩ X X).2.1
    have hb' : fro (ridgeDeriv p.ϱ X) ≤ CR * Real.sqrt ((min m n : ℕ) : ℝ) :=
      (le_add_of_nonneg_right (pe8s_fro_nonneg _)).trans hb
    exact (pe8m_frobIP_le_copy _ _).trans
      (mul_le_mul hP.1 hb' (pe8s_fro_nonneg _) ((pe8s_fro_nonneg Pt).trans hP.1))
  have hLf : 0 ≤ Lf := mul_nonneg (mul_nonneg hCS hδ) hpow1
  have hLg : 0 ≤ Lg := by dsimp [Lg]; positivity
  have hfL : ∀ X Y, |f X - f Y| ≤ Lf * nuc (X - Y) :=
    fun X Y => pe8t_g_lipschitz p Cv D X Y hCo hCi hD
  have hgL : ∀ X Y, |g X - g Y| ≤ Lg * nuc (X - Y) :=
    fun X Y => pe8t_ridge_lipschitz p.ϱ piT p.hϱ Pt X Y hP.2.1
  have hcov := pe8t_stationary_covariance p Cv cs t k r D hD hB hsize
    f g hfm hgm (p.CSig * Real.sqrt n)
    (cP * (CR * Real.sqrt ((min m n : ℕ) : ℝ))) Lf Lg hfb hgb hLf hLg hfL hgL
  have hceq : (Lf * (14 * p.CSig * p.γstar)) * (Lg * (14 * p.CSig * p.γstar)) *
      (B : ℝ) * p.β ^ Nat.dist r k =
      K * ((B : ℝ) * diffuseness Cv D * piT * p.β ^ Nat.dist r k) := by
    dsimp [Lf, Lg, K]
    rw [abs_of_nonneg (mul_nonneg hCS hpow1),
      abs_of_nonneg (mul_nonneg (by norm_num) hpow3)]
    ring
  rw [hceq] at hcov
  have hN := pe8q_stationaryN_aestronglyMeasurable p Cv cs t D hDp hsize
  have hf2 : MemLp (fun ω => f (stationaryN p Cv cs t D k ω)) 2 P :=
    MemLp.of_bound (hfm.comp_aemeasurable (hN k).aemeasurable).aestronglyMeasurable _
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hfb (stationaryN p Cv cs t D k ω))
  have hg2 : MemLp (fun ω => g (stationaryN p Cv cs t D r ω)) 2 P :=
    MemLp.of_bound (hgm.comp_aemeasurable (hN r).aemeasurable).aestronglyMeasurable _
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hgb (stationaryN p Cv cs t D r ω))
  have hVeq : (fun ω => f (stationaryN p Cv cs t D k ω)) =
      (fun ω => pairSigma Cv D (stationaryV p Cv cs t D k ω)) := by
    funext ω
    change pairSigma Cv D (Q p.ϱ _) = pairSigma Cv D (Q (physRidge p Cv D) _)
    rw [show physRidge p Cv D = p.ϱ by simp [physRidge, hD]]
    rfl
  have hmeans := hCM p rfl rfl rfl m n B Ω P Cv cs t k r D Pt
    (by rw [Nat.cast_max]; exact max_le hm hn) hCo hCi hB hD hP.1
  have hmf : |∫ ω, f (stationaryN p Cv cs t D k ω) ∂P| ≤ CM := by
    rw [hVeq]
    exact hmeans.2.2.1.trans (le_max_left _ _)
  have hmg : |∫ ω, g (stationaryN p Cv cs t D r ω) ∂P| ≤ CM :=
    hmeans.2.2.2.trans (le_max_left _ _)
  have hb := pe8t_integral_mul_le P _ _ hf2 hg2 _ _ _ hcov hmf hmg
  simp_rw [show ∀ ω, f (stationaryN p Cv cs t D k ω) =
    pairSigma Cv D (stationaryV p Cv cs t D k ω) from fun ω => congrFun hVeq ω] at hb
  refine ⟨pe8t_ridge_int p Cv cs t k r D Pt piT cP hm hn hCo hCi hB hD hP, ?_⟩
  refine hb.trans ?_
  have hY : 0 ≤ (B : ℝ) * diffuseness Cv D * piT * p.β ^ Nat.dist r k := by positivity
  nlinarith [mul_nonneg (sq_nonneg CM) hY]

private lemma pe8u_dirX_formula {m n : ℕ} (K R : Mat m n) (s : ℝ) (hs : 0 < s) :
    dirX K R s = Rs K s * R - Rs K s * (R * Kᵀ + K * Rᵀ) * (Rs K s * K) := by
  ext i j
  exact (pe8_dX K R s hs i j).deriv.trans (by simp only [Matrix.mul_assoc])

private lemma pe8u_Xs_entry_hasDerivAt {m n : ℕ} (K R : Mat m n) {s : ℝ}
    (hs : 0 < s) (t0 : ℝ) (i : Fin m) (j : Fin n) :
    HasDerivAt (fun t : ℝ => Xs (K + t • R) s i j) (dirX (K + t0 • R) R s i j) t0 := by
  have hd : HasDerivAt (fun θ : ℝ => Xs (K + t0 • R + θ • R) s i j)
      (dirX (K + t0 • R) R s i j) 0 := by
    rw [pe8u_dirX_formula _ _ _ hs]
    simpa only [Matrix.mul_assoc] using pe8_dX (K + t0 • R) R s hs i j
  have hh := hd.comp_of_eq t0 ((hasDerivAt_id t0).sub_const t0) (by simp)
  simp only [mul_one] at hh
  convert hh using 1
  funext t
  change Xs (K + t • R) s i j = Xs (K + t0 • R + (t - t0) • R) s i j
  have he : K + t0 • R + (t - t0) • R = K + t • R := by module
  rw [he]

open scoped Matrix.Norms.L2Operator in
private lemma pe8u_opNorm_one_le {n : ℕ} : opNorm (1 : Mat n n) ≤ 1 := by
  rw [opNorm_eq_norm, ← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun i => by simp

private lemma pe8u_fro_sub_le {a b : ℕ} (A M : Mat a b) : fro (A - M) ≤ fro A + fro M := by
  open scoped Matrix.Norms.Frobenius in
  rw [fro_eq_norm, fro_eq_norm, fro_eq_norm]; exact norm_sub_le _ _

private lemma pe8u_KRK_le {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    opNorm (Kᵀ * Rs K s * K) ≤ 2 := by
  obtain ⟨-, h2, -, -, h5, -, -⟩ := Muon.DetEquiv.lem_app_de_resolvent K s hs
  rw [h5]
  have : opNorm ((1 : Mat n n) - s • Rts K s) ≤ opNorm (1 : Mat n n) + s * opNorm (Rts K s) := by
    open scoped Matrix.Norms.L2Operator in
    rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  refine this.trans ?_
  have h1 := pe8u_opNorm_one_le (n := n)
  have : s * opNorm (Rts K s) ≤ 1 := by
    calc s * opNorm (Rts K s) ≤ s * (1 / s) := mul_le_mul_of_nonneg_left h2 hs.le
      _ = 1 := by field_simp
  linarith

private lemma pe8u_trdX_bound {m n : ℕ} (K R : Mat m n) {s : ℝ} (hs : 0 < s) :
    fro (dirX K R s) ≤ (13 / 4) / s * fro R := by
  obtain ⟨h1, -, h3, -, -, -, -⟩ := Muon.DetEquiv.lem_app_de_resolvent K s hs
  have hRK := pe8u_KRK_le K hs
  have he : dirX K R s = Rs K s * R - Rs K s * R * (Kᵀ * Rs K s * K) - Xs K s * Rᵀ * Xs K s := by
    rw [pe8u_dirX_formula _ _ _ hs]
    unfold Xs
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [he]
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hX2 : opNorm (Xs K s) * opNorm (Xs K s) ≤ 1 / (4 * s) := by
    have h0 := pe8_opNorm_nonneg (Xs K s)
    calc opNorm (Xs K s) * opNorm (Xs K s) ≤ (1 / (2 * Real.sqrt s)) * (1 / (2 * Real.sqrt s)) :=
          mul_le_mul h3 h3 h0 (by positivity)
      _ = 1 / (4 * s) := by
          field_simp
          rw [Real.sq_sqrt hs.le]; ring
  have hfR := pe8s_fro_nonneg R
  have hRs0 := pe8_opNorm_nonneg (Rs K s)
  have t1 : fro (Rs K s * R) ≤ 1 / s * fro R :=
    (pe8s_fro_mul_left _ _).trans (mul_le_mul_of_nonneg_right h1 hfR)
  have t2 : fro (Rs K s * R * (Kᵀ * Rs K s * K)) ≤ 1 / s * fro R * 2 :=
    (pe8s_fro_mul_right _ _).trans (mul_le_mul t1 hRK (pe8_opNorm_nonneg _) (by positivity))
  have t3 : fro (Xs K s * Rᵀ * Xs K s) ≤ 1 / (4 * s) * fro R := by
    refine (pe8s_fro_mul_right _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (pe8s_fro_mul_left _ _) (pe8_opNorm_nonneg _)).trans ?_
    rw [pe8s_fro_transpose]
    calc opNorm (Xs K s) * fro R * opNorm (Xs K s) = (opNorm (Xs K s) * opNorm (Xs K s)) * fro R := by ring
      _ ≤ 1 / (4 * s) * fro R := mul_le_mul_of_nonneg_right hX2 hfR
  calc fro (Rs K s * R - Rs K s * R * (Kᵀ * Rs K s * K) - Xs K s * Rᵀ * Xs K s)
      ≤ fro (Rs K s * R) + fro (Rs K s * R * (Kᵀ * Rs K s * K)) + fro (Xs K s * Rᵀ * Xs K s) :=
        (pe8u_fro_sub_le (Rs K s * R - Rs K s * R * (Kᵀ * Rs K s * K)) (Xs K s * Rᵀ * Xs K s)).trans
          (add_le_add_left (pe8u_fro_sub_le (Rs K s * R) (Rs K s * R * (Kᵀ * Rs K s * K))) _)
    _ ≤ 1 / s * fro R + 1 / s * fro R * 2 + 1 / (4 * s) * fro R := add_le_add (add_le_add t1 t2) t3
    _ = (13 / 4) / s * fro R := by
        have hs' : s ≠ 0 := hs.ne'
        field_simp
        ring

private lemma pe8u_Rs_meas {m n : ℕ} {α : Type*} [MeasurableSpace α] {f : α → Mat m n} {g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => Rs (f x) (g x)) := by
  have hc : Continuous (fun p : Mat m n × ℝ => p.1 * p.1ᵀ + p.2 • (1 : Mat m m)) := by
    fun_prop
  have hA : Measurable (fun x => f x * (f x)ᵀ + g x • (1 : Mat m m)) :=
    hc.measurable.comp (hf.prodMk hg)
  have hdet : Measurable (fun x => (f x * (f x)ᵀ + g x • (1 : Mat m m)).det) :=
    (continuous_id.matrix_det).measurable.comp hA
  have hadj : Measurable (fun x => (f x * (f x)ᵀ + g x • (1 : Mat m m)).adjugate) :=
    (continuous_id.matrix_adjugate).measurable.comp hA
  have he : (fun x => Rs (f x) (g x)) = fun x =>
      (f x * (f x)ᵀ + g x • (1 : Mat m m)).det⁻¹ • (f x * (f x)ᵀ + g x • (1 : Mat m m)).adjugate := by
    funext x
    unfold Rs
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [he]
  exact hdet.inv.smul hadj

private lemma pe8u_mat_mul_meas {a b c : ℕ} {α : Type*} [MeasurableSpace α] {f : α → Mat a b}
    {g : α → Mat b c} (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => f x * g x) :=
  (continuous_fst.matrix_mul continuous_snd).measurable.comp (hf.prodMk hg)

private lemma pe8u_mat_T_meas {a b : ℕ} {α : Type*} [MeasurableSpace α] {f : α → Mat a b}
    (hf : Measurable f) : Measurable (fun x => (f x)ᵀ) :=
  continuous_id.matrix_transpose.measurable.comp hf

private lemma pe8u_trdX_meas {m n : ℕ} {α : Type*} [MeasurableSpace α] {f g : α → Mat m n} {h : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (hp : ∀ x, 0 < h x) :
    Measurable (fun x => dirX (f x) (g x) (h x)) := by
  have hR := pe8u_Rs_meas hf hh
  simp_rw [pe8u_dirX_formula _ _ _ (hp _)]
  exact (pe8u_mat_mul_meas hR hg).sub (pe8u_mat_mul_meas (pe8u_mat_mul_meas hR
    ((pe8u_mat_mul_meas hg (pe8u_mat_T_meas hf)).add (pe8u_mat_mul_meas hf (pe8u_mat_T_meas hg))))
    (pe8u_mat_mul_meas hR hf))

private lemma pe8u_inv_sq_integrable {ϱ : ℝ} (hϱ : 0 < ϱ) :
    IntegrableOn (fun u : ℝ => (ϱ + u ^ 2)⁻¹) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (max 1 ϱ⁻¹)).integrableOn) ?_ ?_
  · exact (Continuous.inv₀ (by fun_prop) (fun u => by positivity)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u => ?_
    have h1 : 0 < ϱ + u ^ 2 := by positivity
    have h2 : 0 < 1 + u ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h1)]
    rw [inv_le_iff_one_le_mul₀ h1]
    have hc1 : 1 ≤ max 1 ϱ⁻¹ := le_max_left _ _
    have hc2 : ϱ⁻¹ ≤ max 1 ϱ⁻¹ := le_max_right _ _
    have hcϱ : 1 ≤ max 1 ϱ⁻¹ * ϱ := by
      calc (1 : ℝ) = ϱ⁻¹ * ϱ := (inv_mul_cancel₀ hϱ.ne').symm
        _ ≤ max 1 ϱ⁻¹ * ϱ := mul_le_mul_of_nonneg_right hc2 hϱ.le
    have he : max 1 ϱ⁻¹ * (1 + u ^ 2)⁻¹ * (ϱ + u ^ 2) = max 1 ϱ⁻¹ * (ϱ + u ^ 2) / (1 + u ^ 2) := by
      field_simp
    rw [he, le_div_iff₀ h2]
    nlinarith [sq_nonneg u]

private lemma pe8u_dirDeriv_integral {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (N R : Mat m n) (i : Fin m) (j : Fin n) :
    IntegrableOn (fun u : ℝ => dirX N R (ϱ + u ^ 2) i j) (Ioi (0 : ℝ)) ∧
    dirDeriv ϱ N R i j = (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), dirX N R (ϱ + u ^ 2) i j := by
  have hs : ∀ u : ℝ, 0 < ϱ + u ^ 2 := fun u => by positivity
  set F : ℝ → ℝ → ℝ := fun t u => Xs (N + t • R) (ϱ + u ^ 2) i j with hF
  set F' : ℝ → ℝ → ℝ := fun t u => dirX (N + t • R) R (ϱ + u ^ 2) i j with hF'
  have hQ : (fun t : ℝ => Q ϱ (N + t • R) i j) = fun t => (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), F t u := by
    funext t
    exact (Muon.Setup.lem_app_setup_contour ϱ hϱ (N + t • R)).1 i j
  have hmeasF : ∀ t, AEStronglyMeasurable (F t) (volume.restrict (Ioi (0 : ℝ))) := by
    intro t
    have : Measurable (fun u : ℝ => Rs (N + t • R) (ϱ + u ^ 2) * (N + t • R)) :=
      pe8u_mat_mul_meas (pe8u_Rs_meas measurable_const (by fun_prop)) measurable_const
    exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp this)).aestronglyMeasurable
  have hmeasF' : ∀ t, AEStronglyMeasurable (F' t) (volume.restrict (Ioi (0 : ℝ))) := by
    intro t
    have : Measurable (fun u : ℝ => dirX (N + t • R) R (ϱ + u ^ 2)) :=
      pe8u_trdX_meas measurable_const measurable_const (by fun_prop) hs
    exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp this)).aestronglyMeasurable
  have hbound_int : Integrable (fun u : ℝ => (13 / 4) * fro R * (ϱ + u ^ 2)⁻¹) (volume.restrict (Ioi (0 : ℝ))) :=
    (pe8u_inv_sq_integrable hϱ).const_mul _
  have hbd : ∀ t u, ‖F' t u‖ ≤ (13 / 4) * fro R * (ϱ + u ^ 2)⁻¹ := by
    intro t u
    rw [Real.norm_eq_abs]
    refine (pe8t_entry_le_fro _ i j).trans ((pe8u_trdX_bound _ R (hs u)).trans (le_of_eq ?_))
    field_simp
  have hint0 : Integrable (F 0) (volume.restrict (Ioi (0 : ℝ))) := by
    have := (Muon.Setup.lem_app_setup_contour ϱ hϱ (N + (0 : ℝ) • R)).2.1 i j
    exact this
  obtain ⟨hint', hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := F) (F' := F') (x₀ := 0) (s := univ)
    (bound := fun u => (13 / 4) * fro R * (ϱ + u ^ 2)⁻¹) Filter.univ_mem
    (Filter.Eventually.of_forall hmeasF) hint0 (hmeasF' 0)
    (Filter.Eventually.of_forall fun u t _ => hbd t u) hbound_int
    (Filter.Eventually.of_forall fun u t _ => pe8u_Xs_entry_hasDerivAt N R (hs u) t i j)
  have hF'0 : F' 0 = fun u => dirX N R (ϱ + u ^ 2) i j := by
    funext u; simp [hF']
  rw [hF'0] at hint' hderiv
  refine ⟨hint', ?_⟩
  unfold dirDeriv
  simp only [Matrix.of_apply]
  rw [hQ]
  exact (hderiv.const_mul (2 / Real.pi)).deriv

private lemma pe8u_indep_other_batch {m n B : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (cs : ChainSamples P m n B) (t j : ℕ) :
    Indep (otherSigma cs t j) (batchSigma cs t j) P := by
  have hind := (iIndepFun_iff_iIndep _ _ _).mp cs.indep
  have hle : ∀ i, MeasurableSpace.comap
      (Sum.elim (fun q : ℤ × Fin B => cs.act q.1 q.2)
        (fun q : ℤ × ℕ × Fin B => cs.aux q.1 q.2.1 q.2.2) i : Ω → Vec m × Vec n) inferInstance ≤ mΩ := by
    intro i
    rcases i with q | q
    · exact (cs.meas_act q.1 q.2).comap_le
    · exact (cs.meas_aux q.1 q.2.1 q.2.2).comap_le
  have hdisj : Disjoint
      {i : (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B) | (∃ q : ℤ × Fin B, i = Sum.inl q ∧ q.1 ≠ (t : ℤ) + j + 1) ∨
        (∃ q : ℤ × ℕ × Fin B, i = Sum.inr q)}
      {i | ∃ q : ℤ × Fin B, i = Sum.inl q ∧ q.1 = (t : ℤ) + j + 1} := by
    rw [Set.disjoint_left]
    rintro i (⟨q, rfl, h1⟩ | ⟨q, rfl⟩) ⟨q', hq', h3⟩
    · cases hq'; exact h1 h3
    · cases hq'
  have := indep_iSup_of_disjoint hle hind hdisj
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left this ?_) ?_
  · refine sup_le (iSup_le fun s => iSup_le fun hs => iSup_le fun a => ?_)
      (iSup_le fun t' => iSup_le fun i => iSup_le fun a => ?_)
    · exact le_iSup₂_of_le (Sum.inl (s, a)) (Or.inl ⟨(s, a), rfl, hs⟩) le_rfl
    · exact le_iSup₂_of_le (Sum.inr (t', i, a)) (Or.inr ⟨(t', i, a), rfl⟩) le_rfl
  · refine iSup_le fun a => ?_
    exact le_iSup₂_of_le (Sum.inl (((t : ℤ) + j + 1), a)) ⟨(((t : ℤ) + j + 1), a), rfl, rfl⟩ le_rfl

private lemma pe8u_batchGrad_cont {m n B : ℕ} (C : Covariances m n) :
    Continuous (fun x : Mat m n × (Fin B → Vec m × Vec n) => batchGrad x.1 (fun a => phys C (x.2 a))) := by
  unfold batchGrad grad resid phys outer
  fun_prop

private lemma pe8u_pairSigma_smul_left {m n : ℕ} (C : Covariances m n) (c : ℝ) (V W : Mat m n) :
    pairSigma C (c • V) W = c * pairSigma C V W := by
  unfold pairSigma
  simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]

private lemma pe8u_pairSigma_smul_right {m n : ℕ} (C : Covariances m n) (c : ℝ) (V W : Mat m n) :
    pairSigma C V (c • W) = c * pairSigma C V W := by
  unfold pairSigma
  simp [Matrix.mul_smul, Matrix.transpose_smul, Matrix.trace_smul]

private lemma pe8u_risk_smul {m n : ℕ} (C : Covariances m n) (c : ℝ) (D : Mat m n) :
    riskSigma C (c • D) = c ^ 2 * riskSigma C D := by
  unfold riskSigma
  rw [pe8u_pairSigma_smul_left, pe8u_pairSigma_smul_right]
  ring

private lemma pe8u_batchGrad_smul {m n B : ℕ} (c : ℝ) (D : Mat m n) (b : Batch m n B) :
    batchGrad (c • D) b = c • batchGrad D b := by
  unfold batchGrad grad resid
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring_nf

private lemma pe8u_chainInit_smul {m n B : ℕ} {Ω : Type*} (β : ℝ) (C : Covariances m n) (c : ℝ)
    (D : Mat m n) (aux : ℕ → Fin B → Ω → Vec m × Vec n) (ω : Ω) :
    chainInit β C (c • D) aux ω = c • chainInit β C D aux ω := by
  unfold chainInit
  simp_rw [pe8u_batchGrad_smul, smul_comm (emaW β _) c]
  exact tsum_const_smul'' (f := fun j => emaW β j • batchGrad D (physBatch C (aux j) ω)) c

private lemma pe8u_emaChain_smul {m n B : ℕ} (β : ℝ) (c : ℝ) (D : Mat m n) (G : ℤ → Batch m n B)
    (t : ℕ) (init : Mat m n) (k : ℕ) :
    emaChain β (c • D) G t (c • init) k = c • emaChain β D G t init k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [emaChain, ih, pe8u_batchGrad_smul, smul_add, smul_comm β c, smul_comm (1 - β) c]

private lemma pe8u_bg_meas {m n B : ℕ} {Ω : Type*} (𝓖 : MeasurableSpace Ω) [MeasurableSpace Ω]
    {P : Measure Ω} (C : Covariances m n) (cs : ChainSamples P m n B) (D : Mat m n) (s : ℤ)
    (hs : ∀ a, Measurable[𝓖] (cs.act s a)) :
    Measurable[𝓖] (fun ω => batchGrad D (physBatch C (cs.act s) ω)) := by
  have h1 : Measurable[𝓖] (fun ω => (D, fun a => cs.act s a ω)) :=
    measurable_const.prodMk (@Measurable.of_eval Ω (Fin B) (fun _ => Vec m × Vec n) 𝓖 _ _ fun a => hs a)
  have e : (fun ω => batchGrad D (physBatch C (cs.act s) ω)) =
      (fun x : Mat m n × (Fin B → Vec m × Vec n) => batchGrad x.1 (fun a => phys C (x.2 a))) ∘
        (fun ω => (D, fun a => cs.act s a ω)) := by
    funext ω; rfl
  rw [e]
  exact (pe8u_batchGrad_cont C).measurable.comp h1

private lemma pe8u_ema_meas {m n B : ℕ} {Ω : Type*} (𝓖 : MeasurableSpace Ω) [MeasurableSpace Ω]
    {P : Measure Ω} (β : ℝ) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n)
    (init : Ω → Mat m n) (hinit : Measurable[𝓖] init) (k : ℕ)
    (hk : ∀ i < k, ∀ a, Measurable[𝓖] (cs.act ((t : ℤ) + i + 1) a)) :
    Measurable[𝓖] (fun ω => emaChain β D (fun s => physBatch C (cs.act s) ω) t (init ω) k) := by
  induction k with
  | zero => exact hinit
  | succ k ih =>
    have ih' := ih (fun i hi a => hk i (by omega) a)
    have hb := pe8u_bg_meas 𝓖 C cs D ((t : ℤ) + k + 1) (hk k (by omega))
    exact (ih'.const_smul β).add (hb.const_smul (1 - β))

private lemma pe8u_N0_meas {m n B : ℕ} {Ω : Type*} (𝓖 : MeasurableSpace Ω) [MeasurableSpace Ω]
    {P : Measure Ω} (β : ℝ) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n)
    (haux : ∀ j a, Measurable[𝓖] (cs.aux (t : ℤ) j a)) :
    Measurable[𝓖] (fun ω => chainInit β C D (cs.aux (t : ℤ)) ω) := by
  have : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  have : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  have : MeasurableAdd₂ (Mat m n) :=
    inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  unfold chainInit
  have hb : ∀ j, Measurable[𝓖] (fun ω => batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) := by
    intro j
    have h1 : Measurable[𝓖] (fun ω => (D, fun a => cs.aux (t : ℤ) j a ω)) :=
      measurable_const.prodMk (@Measurable.of_eval Ω (Fin B) (fun _ => Vec m × Vec n) 𝓖 _ _ fun a => haux j a)
    have e : (fun ω => batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) =
        (fun x : Mat m n × (Fin B → Vec m × Vec n) => batchGrad x.1 (fun a => phys C (x.2 a))) ∘
          (fun ω => (D, fun a => cs.aux (t : ℤ) j a ω)) := by
      funext ω; rfl
    rw [e]
    exact (pe8u_batchGrad_cont C).measurable.comp h1
  have hb' : ∀ j, Measurable[𝓖] (fun ω => emaW β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω)) :=
    fun j => (hb j).const_smul (emaW β j)
  exact @Measurable.tsum Ω (Mat m n) ℕ 𝓖 _ _ _ _ _ _ _ _ _ _ _ _ hb'

private lemma pe8u_Q_meas {m n : ℕ} {Ω : Type*} (𝓖 : MeasurableSpace Ω) (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    {f : Ω → Mat m n} (hf : Measurable[𝓖] f) : Measurable[𝓖] (fun ω => Q ℓ (f ω)) := by
  have h1 : Measurable[𝓖] (fun ω => ((⟨ℓ, hℓ⟩ : Ici (0 : ℝ)), f ω)) := measurable_const.prodMk hf
  exact (measurable_Q (m := m) (n := n)).comp h1

private lemma pe8u_act_other {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (cs : ChainSamples P m n B) (t j : ℕ) (s : ℤ) (hs : s ≠ (t : ℤ) + j + 1) (a : Fin B) :
    Measurable[otherSigma cs t j] (cs.act s a) := by
  refine measurable_iff_comap_le.2 (le_sup_of_le_left ?_)
  exact le_iSup₂_of_le s hs (le_iSup_of_le a le_rfl)

private lemma pe8u_aux_other {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (cs : ChainSamples P m n B) (t j : ℕ) (t' : ℤ) (i : ℕ) (a : Fin B) :
    Measurable[otherSigma cs t j] (cs.aux t' i a) := by
  refine measurable_iff_comap_le.2 (le_sup_of_le_right ?_)
  exact le_iSup_of_le t' (le_iSup_of_le i (le_iSup_of_le a le_rfl))

private lemma pe8u_other_le {m n B : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (cs : ChainSamples P m n B) (t j : ℕ) : otherSigma cs t j ≤ mΩ :=
  sup_le (iSup_le fun s' => iSup_le fun _ => iSup_le fun b => (cs.meas_act s' b).comap_le)
    (iSup_le fun t' => iSup_le fun i => iSup_le fun b => (cs.meas_aux t' i b).comap_le)

private lemma pe8u_frozenV_other {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t j k : ℕ) (hkj : k < j)
    (D : Mat m n) (hℓ : 0 ≤ physRidge p C D) (init : Ω → Mat m n)
    (hinit : Measurable[otherSigma cs t j] init) :
    Measurable[otherSigma cs t j] (fun ω => Q (physRidge p C D)
      (emaChain p.β D (fun s => physBatch C (cs.act s) ω) t (init ω) (k + 1))) := by
  refine pe8u_Q_meas _ _ hℓ (pe8u_ema_meas _ p.β C cs t D init hinit (k + 1) fun i hi a => ?_)
  exact pe8u_act_other cs t j _ (by omega) a

private lemma pe8u_frobIP_neg_right {m n : ℕ} (X Y : Mat m n) :
    frobIP X (-Y) = -frobIP X Y := by
  simp [frobIP, Matrix.transpose_neg, Matrix.mul_neg, Matrix.trace_neg]

private lemma pe8u_frobIP_sum_right {m n : ℕ} {ι : Type*} (X : Mat m n) (s : Finset ι) (Y : ι → Mat m n) :
    frobIP X (∑ i ∈ s, Y i) = ∑ i ∈ s, frobIP X (Y i) := by
  simp [frobIP, Matrix.transpose_sum, Matrix.mul_sum, Matrix.trace_sum]

private lemma pe8u_frobIP_cont {m n : ℕ} (X : Mat m n) : Continuous (fun Y : Mat m n => frobIP X Y) := by
  unfold frobIP; fun_prop

private lemma pe8u_frobIP_dirDeriv_eq {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (T N R : Mat m n) :
    IntegrableOn (fun u : ℝ => frobIP T (dirX N R (ϱ + u ^ 2))) (Ioi (0 : ℝ)) ∧
    frobIP T (dirDeriv ϱ N R) = (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), frobIP T (dirX N R (ϱ + u ^ 2)) := by
  have hrep := fun i j => pe8u_dirDeriv_integral hϱ N R i j
  simp_rw [pe8p_frobIP_eq]
  have hint : ∀ i j, IntegrableOn (fun u : ℝ => T i j * dirX N R (ϱ + u ^ 2) i j) (Ioi (0 : ℝ)) :=
    fun i j => (hrep i j).1.const_mul _
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(hrep i j).2, integral_const_mul]
  ring

private lemma pe8u_emaW_mem {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (j : ℕ) : emaW β j ∈ Icc (0 : ℝ) 1 := by
  unfold emaW
  have h1 : 0 ≤ 1 - β := by linarith
  have h2 : β ^ j ≤ 1 := pow_le_one₀ hβ.1 hβ.2.le
  have h3 : 0 ≤ β ^ j := pow_nonneg hβ.1 j
  constructor
  · positivity
  · nlinarith

private lemma pe8u_Q_bounds {m n : ℕ} (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (K : Mat m n) :
    opNorm (Q ℓ K) ≤ 1 ∧ fro (Q ℓ K) ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
  obtain ⟨h1, h2, h3, -⟩ := lem_app_setup_filter_i ℓ hℓ K
  refine ⟨h1, ?_⟩
  rw [← Real.sqrt_sq (pe8s_fro_nonneg _)]
  exact Real.sqrt_le_sqrt (h2.trans (by exact_mod_cast h3))

private lemma pe8u_emaW_sum_le {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (r : ℕ) :
    ∑ j ∈ Finset.range (r + 1), emaW β (r - j) ≤ 1 := by
  have e : ∑ j ∈ Finset.range (r + 1), emaW β (r - j) =
      ∑ j ∈ Finset.range (r + 1), emaW β (r + 1 - 1 - j) :=
    Finset.sum_congr rfl fun j _ => by congr 1
  rw [e, Finset.sum_range_reflect (fun i => emaW β i) (r + 1)]
  unfold emaW
  rw [← Finset.mul_sum]
  have h := geom_sum_mul β (r + 1)
  have hb : 0 ≤ β ^ (r + 1) := pow_nonneg hβ.1 _
  have e : (1 - β) * ∑ i ∈ Finset.range (r + 1), β ^ i = 1 - β ^ (r + 1) := by linarith
  linarith

private lemma pe8u_double_sum_emaW_le {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (r : ℕ) :
    ∑ j ∈ Finset.range (r + 1), ∑ _k ∈ Finset.range j, emaW β (r - j) ≤ r := by
  have h : ∀ j ∈ Finset.range (r + 1), ∑ _k ∈ Finset.range j, emaW β (r - j) ≤ (r : ℝ) * emaW β (r - j) := by
    intro j hj
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      (pe8u_emaW_mem hβ _).1
  refine (Finset.sum_le_sum h).trans ?_
  rw [← Finset.mul_sum]
  calc (r : ℝ) * ∑ j ∈ Finset.range (r + 1), emaW β (r - j) ≤ r * 1 :=
        mul_le_mul_of_nonneg_left (pe8u_emaW_sum_le hβ r) (Nat.cast_nonneg _)
    _ = r := mul_one _

private lemma pe8u_Q_contDiff {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun N : Fin m → Fin n → ℝ => fun i j => Q ℓ (Matrix.of N) i j) := by
  apply contDiff_iff_contDiffAt.mpr
  intro N
  have hQ := (Q_contDiffOn_pos m n).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds
      (show 0 < (N, ℓ).2 from hℓ))
  exact hQ.comp N ((contDiff_id.prodMk contDiff_const).contDiffAt)

private lemma pe8u_filter_fderiv {m n : ℕ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (N R : Fin m → Fin n → ℝ) :
    (fderiv ℝ (fun M : Fin m → Fin n → ℝ =>
      fun i j => Q ℓ (Matrix.of M) i j) N) R = dirDeriv ℓ (Matrix.of N) (Matrix.of R) := by
  have hQ := (pe8u_Q_contDiff (m := m) (n := n) hℓ).differentiable (by simp)
  have hline : HasDerivAt (fun t : ℝ => N + t • R) R 0 := by
    exact (hasDerivAt_const_add_iff N).mpr (by
      simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const R)
  have hcomp := (hQ N).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline
    (by simp only [zero_smul, add_zero])
  ext i j
  exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hcomp i) j).deriv).symm

private lemma pe8u_dirDeriv_lin {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (N : Mat m n) :
    ∃ L : Mat m n →ₗ[ℝ] Mat m n, ∀ R, dirDeriv ℓ N R = L R := by
  let F := fderiv ℝ (fun M : Fin m → Fin n → ℝ => fun i j => Q ℓ (Matrix.of M) i j) N
  let L : Mat m n →ₗ[ℝ] Mat m n :=
    { toFun := fun R => Matrix.of (F (fun i j => R i j))
      map_add' := fun R R' => by
        have : (fun i j => (R + R') i j) = (fun i j => R i j) + (fun i j => R' i j) := rfl
        rw [this, map_add]; rfl
      map_smul' := fun c R => by
        have : (fun i j => (c • R) i j) = c • (fun i j => R i j) := rfl
        rw [this, map_smul]; rfl }
  refine ⟨L, fun R => ?_⟩
  exact (pe8u_filter_fderiv hℓ N R).symm

private lemma pe8u_dirDeriv_neg {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (N R : Mat m n) :
    dirDeriv ℓ N (-R) = -dirDeriv ℓ N R := by
  obtain ⟨L, hL⟩ := pe8u_dirDeriv_lin hℓ N
  rw [hL, hL, map_neg]

private lemma pe8u_dirDeriv_sum {m n : ℕ} {ι : Type*} {ℓ : ℝ} (hℓ : 0 < ℓ) (N : Mat m n) (s : Finset ι)
    (R : ι → Mat m n) : dirDeriv ℓ N (∑ i ∈ s, R i) = ∑ i ∈ s, dirDeriv ℓ N (R i) := by
  obtain ⟨L, hL⟩ := pe8u_dirDeriv_lin hℓ N
  rw [hL, map_sum]
  exact Finset.sum_congr rfl fun i _ => (hL _).symm

private lemma pe8u_causalDot_eq {m n B : ℕ} (p : DynParams) (C : Covariances m n) (G : ℤ → Batch m n B)
    (t : ℕ) (D m0 : Mat m n) (hD : 0 < riskSigma C D) (r : ℕ) :
    causalDot p C G t D m0 r =
      dirDeriv (physRidge p C D) (emaChain p.β D G t m0 (r + 1)) (tangentM p C G t D m0 r)
        + (-(2 * p.ϱ * pairSigma C D (∑ k ∈ Finset.range r, frozenV p C G t D m0 k))) •
          ridgeDeriv (physRidge p C D) (emaChain p.β D G t m0 (r + 1)) := by
  ext i j
  unfold causalDot
  simp only [Matrix.of_apply]
  exact ((lem_app_dyn_tangent p C G t D m0 hD).2.2 r i j).deriv

private lemma pe8u_integral_dsum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (r : ℕ)
    (f : ℕ → ℕ → Ω → ℝ) (hf : ∀ j ∈ Finset.range (r + 1), ∀ k ∈ Finset.range j, Integrable (f j k) P) :
    Integrable (fun ω => ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, f j k ω) P ∧
    ∫ ω, ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, f j k ω ∂P =
      ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, ∫ ω, f j k ω ∂P := by
  have hi : ∀ j ∈ Finset.range (r + 1), Integrable (fun ω => ∑ k ∈ Finset.range j, f j k ω) P :=
    fun j hj => integrable_finsetSum _ fun k hk => hf j hj k hk
  refine ⟨integrable_finsetSum _ hi, ?_⟩
  rw [integral_finsetSum _ hi]
  exact Finset.sum_congr rfl fun j hj => integral_finsetSum _ fun k hk => hf j hj k hk

private lemma pe8u_pairSigma_sum_right {m n : ℕ} {ι : Type*} (C : Covariances m n) (D : Mat m n)
    (s : Finset ι) (V : ι → Mat m n) : pairSigma C D (∑ i ∈ s, V i) = ∑ i ∈ s, pairSigma C D (V i) := by
  unfold pairSigma
  simp [Matrix.transpose_sum, Matrix.mul_sum, Matrix.trace_sum]

private lemma pe8u_fro_sum_le {m n : ℕ} {ι : Type*} (s : Finset ι) (X : ι → Mat m n) :
    fro (∑ i ∈ s, X i) ≤ ∑ i ∈ s, fro (X i) := by
  open scoped Matrix.Norms.Frobenius in
  simp only [fro_eq_norm]
  exact norm_sum_le _ _

private lemma pe8u_resid_le {m n : ℕ} (V : Mat m n) (x : Vec m × Vec n) :
    |resid V x| ≤ Real.sqrt (∑ i, x.1 i ^ 2) * fro V * Real.sqrt (∑ j, x.2 j ^ 2) := by
  unfold resid
  have h1 : |x.1 ⬝ᵥ (V *ᵥ x.2)| ≤ Real.sqrt (∑ i, x.1 i ^ 2) * Real.sqrt (∑ i, (V *ᵥ x.2) i ^ 2) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h2 : Real.sqrt (∑ i, (V *ᵥ x.2) i ^ 2) ≤ fro V * Real.sqrt (∑ j, x.2 j ^ 2) := by
    rw [← Real.sqrt_sq (pe8s_fro_nonneg V), ← Real.sqrt_mul (sq_nonneg _)]
    refine Real.sqrt_le_sqrt ((pe8_sum_sq_mulVec_le V x.2).trans ?_)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (pe8_opNorm_nonneg _) (pe8s_op_le_fro V) 2)
      (by positivity)
  calc |x.1 ⬝ᵥ (V *ᵥ x.2)| ≤ Real.sqrt (∑ i, x.1 i ^ 2) * Real.sqrt (∑ i, (V *ᵥ x.2) i ^ 2) := h1
    _ ≤ Real.sqrt (∑ i, x.1 i ^ 2) * (fro V * Real.sqrt (∑ j, x.2 j ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = _ := by ring

private lemma pe8u_grad_fro_le {m n B : ℕ} (V : Mat m n) (b : Batch m n B) :
    fro (batchGrad V b) ≤ fro V * ((B : ℝ)⁻¹ * ∑ a, (∑ i, (b a).1 i ^ 2) * (∑ j, (b a).2 j ^ 2)) := by
  unfold batchGrad grad
  rw [pe8_fro_smul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  have hB0 : (0 : ℝ) ≤ (B : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  refine (mul_le_mul_of_nonneg_left (pe8u_fro_sum_le _ _) hB0).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [pe8_fro_smul, pe8s_fro_outer]
  have h := pe8u_resid_le V (b a)
  have hx := Real.sq_sqrt (show 0 ≤ ∑ i, (b a).1 i ^ 2 by positivity)
  have hy := Real.sq_sqrt (show 0 ≤ ∑ j, (b a).2 j ^ 2 by positivity)
  have hsx := Real.sqrt_nonneg (∑ i, (b a).1 i ^ 2)
  have hsy := Real.sqrt_nonneg (∑ j, (b a).2 j ^ 2)
  calc (B : ℝ)⁻¹ * (|resid V (b a)| * (Real.sqrt (∑ i, (b a).1 i ^ 2) * Real.sqrt (∑ j, (b a).2 j ^ 2)))
      ≤ (B : ℝ)⁻¹ * ((Real.sqrt (∑ i, (b a).1 i ^ 2) * fro V * Real.sqrt (∑ j, (b a).2 j ^ 2)) *
          (Real.sqrt (∑ i, (b a).1 i ^ 2) * Real.sqrt (∑ j, (b a).2 j ^ 2))) := by
        gcongr
    _ = fro V * ((B : ℝ)⁻¹ * ((Real.sqrt (∑ i, (b a).1 i ^ 2)) ^ 2 * (Real.sqrt (∑ j, (b a).2 j ^ 2)) ^ 2)) := by
        ring
    _ = _ := by rw [hx, hy]

private lemma pe8u_phys_sq_le {m n : ℕ} (C : Covariances m n) (CS : ℝ) (hC : opNorm C.Sout ≤ CS)
    (hCi : opNorm C.Sin ≤ CS) (z : Vec m × Vec n) :
    (∑ i, (phys C z).1 i ^ 2) ≤ CS * ∑ i, z.1 i ^ 2 ∧ (∑ j, (phys C z).2 j ^ 2) ≤ CS * ∑ j, z.2 j ^ 2 := by
  have ho := pe8_opNorm_sqrt_mul_self C.Sout C.psdOut
  have hi := pe8_opNorm_sqrt_mul_self C.Sin C.psdIn
  constructor
  · refine (pe8_sum_sq_mulVec_le (rOut C) z.1).trans ?_
    exact mul_le_mul_of_nonneg_right (by unfold rOut; rw [sq, ho]; exact hC) (by positivity)
  · refine (pe8_sum_sq_mulVec_le (rIn C) z.2).trans ?_
    exact mul_le_mul_of_nonneg_right (by unfold rIn; rw [sq, hi]; exact hCi) (by positivity)

private lemma pe8u_physGrad_le {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Covariances m n) (CS : ℝ) (hC0 : 0 ≤ CS) (hC : opNorm C.Sout ≤ CS) (hCi : opNorm C.Sin ≤ CS)
    (cs : ChainSamples P m n B) (s : ℤ) (V : Mat m n) (ω : Ω) :
    fro (batchGrad V (physBatch C (cs.act s) ω)) ≤ fro V * (CS ^ 2 * ((B : ℝ)⁻¹ *
      ∑ a, (∑ i, (cs.act s a ω).1 i ^ 2) * (∑ j, (cs.act s a ω).2 j ^ 2))) := by
  refine (pe8u_grad_fro_le V _).trans (mul_le_mul_of_nonneg_left ?_ (pe8s_fro_nonneg _))
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  obtain ⟨h1, h2⟩ := pe8u_phys_sq_le C CS hC hCi (cs.act s a ω)
  have hB0 : (0 : ℝ) ≤ (B : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  change (B : ℝ)⁻¹ * ((∑ i, (phys C (cs.act s a ω)).1 i ^ 2) * (∑ j, (phys C (cs.act s a ω)).2 j ^ 2)) ≤ _
  calc (B : ℝ)⁻¹ * ((∑ i, (phys C (cs.act s a ω)).1 i ^ 2) * (∑ j, (phys C (cs.act s a ω)).2 j ^ 2))
      ≤ (B : ℝ)⁻¹ * ((CS * ∑ i, (cs.act s a ω).1 i ^ 2) * (CS * ∑ j, (cs.act s a ω).2 j ^ 2)) := by
        gcongr
    _ = _ := by ring

private lemma pe8u_H_integrable {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (cs : ChainSamples P m n B) (s : ℤ) :
    Integrable (fun ω => (B : ℝ)⁻¹ * ∑ a, (∑ i, (cs.act s a ω).1 i ^ 2) * (∑ j, (cs.act s a ω).2 j ^ 2)) P := by
  refine (integrable_finsetSum _ fun a _ => ?_).const_mul _
  have hg : Integrable (fun z : Vec m × Vec n => (∑ i, z.1 i ^ 2) * (∑ j, z.2 j ^ 2))
      ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) := by
    have h1 := (integrable_finsetSum Finset.univ fun i _ => pe8p_sq_coord m i)
    have h2 := (integrable_finsetSum Finset.univ fun i _ => pe8p_sq_coord n i)
    exact h1.mul_prod h2
  have hmeas : AEStronglyMeasurable (fun z : Vec m × Vec n => (∑ i, z.1 i ^ 2) * (∑ j, z.2 j ^ 2))
      (P.map (cs.act s a)) := by
    exact (by fun_prop : Continuous (fun z : Vec m × Vec n => (∑ i, z.1 i ^ 2) * (∑ j, z.2 j ^ 2))).aestronglyMeasurable
  rw [← cs.law_act s a] at hg
  exact (integrable_map_measure hmeas (cs.meas_act s a).aemeasurable).mp hg

private lemma pe8u_ridge_nonneg (p : DynParams) {m n : ℕ} (C : Covariances m n) (D : Mat m n) :
    0 ≤ physRidge p C D := by
  unfold physRidge
  rw [eqn_app_setup_whitened_risk]
  have := p.hϱ
  positivity

private lemma pe8u_causal_overlap (p : DynParams) (r : ℕ) :
    ∑ j ∈ Finset.range (r + 1), (emaW p.β (r - j)) ^ 2 *
      ∑ k ∈ Finset.range j, p.β ^ (r - k) ≤ 1 := by
  have hinner : ∀ j ≤ r + 1,
      (1 - p.β) * ∑ k ∈ Finset.range j, p.β ^ (r - k) ≤ 1 := by
    intro j hj
    rw [Finset.mul_sum]
    change ∑ k ∈ Finset.range j, emaW p.β (r - k) ≤ 1
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
      (fun k _ _ => (pe8q_emaW_mem_Icc p _).1)).trans (pe8u_emaW_sum_le p.hβ r)
  refine (Finset.sum_le_sum fun j hj => ?_).trans (pe8u_emaW_sum_le p.hβ r)
  have hw := pe8q_emaW_mem_Icc p (r - j)
  have hi := hinner j (Nat.le_of_lt (Finset.mem_range.mp hj))
  have hp : p.β ^ (r - j) ≤ 1 := pow_le_one₀ p.hβ.1 p.hβ.2.le
  have hi0 : 0 ≤ (1 - p.β) * ∑ k ∈ Finset.range j, p.β ^ (r - k) :=
    mul_nonneg (by linarith [p.hβ.2]) (Finset.sum_nonneg fun k _ => pow_nonneg p.hβ.1 _)
  calc (emaW p.β (r - j)) ^ 2 * ∑ k ∈ Finset.range j, p.β ^ (r - k)
      = emaW p.β (r - j) * (p.β ^ (r - j) *
          ((1 - p.β) * ∑ k ∈ Finset.range j, p.β ^ (r - k))) := by unfold emaW; ring
    _ ≤ emaW p.β (r - j) * 1 :=
      mul_le_mul_of_nonneg_left (by nlinarith) hw.1
    _ = _ := mul_one _

private lemma pe8u_causal_geometric (p : DynParams) (r : ℕ) :
    ∑ k ∈ Finset.range r, p.β ^ (r - k) ≤ (1 - p.β)⁻¹ := by
  have h : (1 - p.β) * ∑ k ∈ Finset.range r, p.β ^ (r - k) ≤ 1 := by
    rw [Finset.mul_sum]
    change ∑ k ∈ Finset.range r, emaW p.β (r - k) ≤ 1
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ r))
      (fun k _ _ => (pe8q_emaW_mem_Icc p _).1)).trans (pe8u_emaW_sum_le p.hβ r)
  rw [← one_div, le_div_iff₀ (sub_pos.mpr p.hβ.2)]
  linarith

private lemma pe8u_Q_scale {m n : ℕ} (p : DynParams) (Cv : Covariances m n)
    (D K : Mat m n) (a : ℝ) (ha : 0 < a) :
    Q (physRidge p Cv (a • D)) (a • K) = Q (physRidge p Cv D) K := by
  have he : physRidge p Cv (a • D) = a ^ 2 * physRidge p Cv D := by
    unfold physRidge
    rw [pe8u_risk_smul]
    ring
  rw [he, prop_app_setup_scaling_i _ (mul_nonneg (sq_nonneg _) (pe8u_ridge_nonneg p Cv D)) _ a ha]
  congr 1
  field_simp

private lemma pe8u_causalState_scale {m n B : ℕ} (p : DynParams) (Cv : Covariances m n)
    (G : ℤ → Batch m n B) (t : ℕ) (D M : Mat m n) (a : ℝ) (ha : 0 < a)
    (ε : ℝ) (r : ℕ) :
    causalState p Cv G t (a • D) (a • M) (a * ε) r =
      (a • (causalState p Cv G t D M ε r).1, a • (causalState p Cv G t D M ε r).2) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [causalState, ih, pe8u_batchGrad_smul]
    have he : p.β • (a • (causalState p Cv G t D M ε r).2) +
        (1 - p.β) • (a • batchGrad (causalState p Cv G t D M ε r).1 (G ((t : ℤ) + r + 1))) =
        a • (p.β • (causalState p Cv G t D M ε r).2 +
          (1 - p.β) • batchGrad (causalState p Cv G t D M ε r).1 (G ((t : ℤ) + r + 1))) := by module
    simp only [he, pe8u_Q_scale p Cv _ _ a ha]
    congr 1
    module

private lemma pe8u_causalS_scale {m n B : ℕ} (p : DynParams) (Cv : Covariances m n)
    (G : ℤ → Batch m n B) (t : ℕ) (D M : Mat m n) (a : ℝ) (ha : 0 < a)
    (ε : ℝ) (r : ℕ) :
    causalS p Cv G t (a • D) (a • M) ε r = causalS p Cv G t D M (a⁻¹ * ε) r := by
  have he : ε = a * (a⁻¹ * ε) := by field_simp
  conv_lhs => rw [he]
  unfold causalS
  rw [pe8u_causalState_scale p Cv G t D M a ha,
    pe8u_causalState_scale p Cv G t D M a ha]
  exact pe8u_Q_scale p Cv _ _ a ha

private lemma pe8u_causalDot_scale {m n B : ℕ} (p : DynParams) (Cv : Covariances m n)
    (G : ℤ → Batch m n B) (t : ℕ) (D M : Mat m n) (a : ℝ) (ha : 0 < a) (r : ℕ) :
    causalDot p Cv G t (a • D) (a • M) r = a⁻¹ • causalDot p Cv G t D M r := by
  ext i j
  simp only [causalDot, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    pe8u_causalS_scale p Cv G t D M a ha]
  simpa only [mul_zero, smul_eq_mul] using
    deriv_comp_mul_left a⁻¹ (fun ε => causalS p Cv G t D M ε r i j) 0

private lemma pe8u_diffuseness_scale {m n : ℕ} (Cv : Covariances m n)
    (D : Mat m n) (a : ℝ) (ha : 0 < a) : diffuseness Cv (a • D) = diffuseness Cv D := by
  have he : Ahat Cv (a • D) = Ahat Cv D := by
    unfold Ahat Arot
    rw [pe8u_risk_smul, show 2 * (a ^ 2 * riskSigma Cv D) = a ^ 2 * (2 * riskSigma Cv D) by ring,
      Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le, mul_inv,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1
    field_simp
  exact congrArg opNorm he

private lemma pe8u_stationaryV_other {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (Cv : Covariances m n) (cs : ChainSamples P m n B) (t j k : ℕ)
    (hkj : k < j) (D : Mat m n) :
    Measurable[otherSigma cs t j] (stationaryV p Cv cs t D k) := by
  exact pe8u_frozenV_other p Cv cs t j k hkj D (pe8u_ridge_nonneg p Cv D) _
    (pe8u_N0_meas _ p.β Cv cs t D fun q a => pe8u_aux_other cs t j _ q a)

private lemma pe8u_stationaryN_meas {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (Cv : Covariances m n) (cs : ChainSamples P m n B) (t r : ℕ) (D : Mat m n) :
    Measurable (stationaryN p Cv cs t D r) := by
  exact pe8u_ema_meas ‹MeasurableSpace Ω› p.β Cv cs t D _
    (pe8u_N0_meas _ p.β Cv cs t D fun q a => cs.meas_aux _ q a) (r + 1)
    (fun i _ a => cs.meas_act _ a)

private lemma pe8u_batch_fro_integrable {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (p : DynParams) (Cv : Covariances m n)
    (cs : ChainSamples P m n B) (s : ℤ) (E : Ω → Mat m n) (hE : Measurable E)
    (L : ℝ) (hL : ∀ ω, fro (E ω) ≤ L) (hCo : opNorm Cv.Sout ≤ p.CSig)
    (hCi : opNorm Cv.Sin ≤ p.CSig) :
    Integrable (fun ω => fro (batchGrad (E ω) (physBatch Cv (cs.act s) ω))) P := by
  have hm : Measurable (fun ω => batchGrad (E ω) (physBatch Cv (cs.act s) ω)) := by
    have hpair : Measurable (fun ω => (E ω, fun a => cs.act s a ω)) :=
      hE.prodMk (measurable_pi_iff.mpr fun a => cs.meas_act s a)
    have he : (fun ω => batchGrad (E ω) (physBatch Cv (cs.act s) ω)) =
        (fun x : Mat m n × (Fin B → Vec m × Vec n) => batchGrad x.1 (fun a => phys Cv (x.2 a))) ∘
          (fun ω => (E ω, fun a => cs.act s a ω)) := by funext ω; rfl
    rw [he]
    exact (pe8u_batchGrad_cont Cv).measurable.comp hpair
  refine ((pe8u_H_integrable cs s).const_mul (L * p.CSig ^ 2)).mono'
    (pe8s_cont_fro.measurable.comp hm).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pe8s_fro_nonneg _)]
  refine (pe8u_physGrad_le Cv p.CSig (le_trans zero_le_one p.hC) hCo hCi cs s (E ω) ω).trans ?_
  calc _ ≤ L * (p.CSig ^ 2 * ((B : ℝ)⁻¹ *
        ∑ a, (∑ i, (cs.act s a ω).1 i ^ 2) * (∑ j, (cs.act s a ω).2 j ^ 2))) :=
      mul_le_mul_of_nonneg_right (hL ω) (by positivity)
    _ = _ := by ring

private lemma pe8u_integrate_dir {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ϱ : ℝ) (hϱ : 0 < ϱ)
    (Pt : Mat m n) (N R : Ω → Mat m n) (hN : Measurable N) (hR : Measurable R)
    (hint : Integrable (fun ω => fro (R ω)) P) (L : ℝ)
    (hb : ∀ s, ϱ ≤ s → |∫ ω, frobIP Pt (dirX (N ω) (R ω) s) ∂P| ≤ L / s) :
    Integrable (fun ω => frobIP Pt (dirDeriv ϱ (N ω) (R ω))) P ∧
    |∫ ω, frobIP Pt (dirDeriv ϱ (N ω) (R ω)) ∂P| ≤
      ((2 / Real.pi) * ∫ u in Ioi (0 : ℝ), (ϱ + u ^ 2)⁻¹) * L := by
  let F : Ω → ℝ → ℝ := fun ω u => frobIP Pt (dirX (N ω) (R ω) (ϱ + u ^ 2))
  have hFm : Measurable (Function.uncurry F) :=
    (pe8u_frobIP_cont Pt).measurable.comp
      (pe8u_trdX_meas (hN.comp measurable_fst) (hR.comp measurable_fst)
        (by fun_prop) (fun z => by positivity))
  have hFbd : ∀ ω u, |F ω u| ≤ (fro Pt * (13 / 4) * fro (R ω)) * (ϱ + u ^ 2)⁻¹ := by
    intro ω u
    refine (pe8m_frobIP_le Pt _).trans ?_
    refine (mul_le_mul_of_nonneg_left (pe8u_trdX_bound _ _ (by positivity))
      (pe8s_fro_nonneg Pt)).trans (le_of_eq ?_)
    ring
  have hFint : Integrable (Function.uncurry F) (P.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    ((hint.const_mul (fro Pt * (13 / 4))).mul_prod (pe8u_inv_sq_integrable hϱ)).mono'
      hFm.aestronglyMeasurable (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact hFbd z.1 z.2)
  have he : (fun ω => frobIP Pt (dirDeriv ϱ (N ω) (R ω))) =
      fun ω => (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), F ω u :=
    funext fun ω => (pe8u_frobIP_dirDeriv_eq hϱ Pt (N ω) (R ω)).2
  rw [he]
  refine ⟨hFint.integral_prod_left.const_mul _, ?_⟩
  rw [integral_const_mul, integral_integral_swap hFint, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi)]
  have hbound := norm_integral_le_of_norm_le ((pe8u_inv_sq_integrable hϱ).const_mul L)
    (Eventually.of_forall fun u => show ‖∫ ω, F ω u ∂P‖ ≤ L * (ϱ + u ^ 2)⁻¹ by
      simpa only [Real.norm_eq_abs, div_eq_mul_inv] using hb (ϱ + u ^ 2) (by nlinarith [sq_nonneg u]))
  rw [Real.norm_eq_abs, integral_const_mul] at hbound
  exact (mul_le_mul_of_nonneg_left hbound (by positivity)).trans (le_of_eq (by ring))

private lemma pe8u_stationary_resolvent (certQ : Muon.External.GaussianQuadFormLp)
    (p : DynParams) (cP : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m n B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (Cv : Covariances m n) (cs : ChainSamples P m n B)
      (t k j r : ℕ) (D Pt : Mat m n) (piT s : ℝ),
      (m : ℝ) ≤ p.γstar * B → (n : ℝ) ≤ p.γstar * B →
      opNorm Cv.Sout ≤ p.CSig → opNorm Cv.Sin ≤ p.CSig → 0 < B →
      riskSigma Cv D = 1 / 2 → IsTest cP piT Pt → k < j → j ≤ r → p.ϱ ≤ s →
      Integrable (fun ω => frobIP Pt (dirX (stationaryN p Cv cs t D r ω)
        (emaW p.β (r - j) • batchGrad (stationaryV p Cv cs t D k ω)
          (physBatch Cv (cs.act ((t : ℤ) + j + 1)) ω)) s)) P ∧
      |∫ ω, frobIP Pt (dirX (stationaryN p Cv cs t D r ω)
        (emaW p.β (r - j) • batchGrad (stationaryV p Cv cs t D k ω)
          (physBatch Cv (cs.act ((t : ℤ) + j + 1)) ω)) s) ∂P| ≤
      K * (Real.sqrt B * emaW p.β (r - j) +
        (1 + (B : ℝ) * (diffuseness Cv D * (piT + diffuseness Cv D))) *
          (emaW p.β (r - j)) ^ 2 * p.β ^ (r - k)) / s := by
  let cE := max 1 (Real.sqrt p.γstar)
  obtain ⟨Cr0, hred⟩ := prop_app_dyn_reduction certQ p.γstar p.CSig p.ϱ cP cE p.hϱ
  obtain ⟨Cs0, hscalar⟩ := prop_app_dyn_scalar p.γstar p.CSig p.ϱ p.ϱ cP p.hϱ
  let Cr := max Cr0 0
  let Cs := max Cs0 0
  let a := p.ϱ ^ (-(1 / 2 : ℝ))
  let b := p.ϱ⁻¹
  have hCr : 0 ≤ Cr := le_max_right _ _
  have hCs : 0 ≤ Cs := le_max_right _ _
  have ha : 0 ≤ a := Real.rpow_nonneg p.hϱ.le _
  have hb : 0 ≤ b := inv_nonneg.mpr p.hϱ.le
  refine ⟨Cr + Cs * a + Cs * b, by positivity, ?_⟩
  intro m n B Ω _ P _ Cv cs t k j r D Pt piT s hm hn hCo hCi hB hD hP hkj hjr hs
  have hsp : 0 < s := p.hϱ.trans_le hs
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hδ : 0 ≤ diffuseness Cv D := pe8_opNorm_nonneg _
  have hπ : 0 ≤ piT := (pe8_opNorm_nonneg Pt).trans hP.2.1
  let w := emaW p.β (r - j)
  let Y := 1 + (B : ℝ) * (diffuseness Cv D * (piT + diffuseness Cv D))
  have hw := pe8q_emaW_mem_Icc p (r - j)
  have hw0 : 0 ≤ w := hw.1
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hq : 0 ≤ p.β ^ (r - k) := pow_nonneg p.hβ.1 _
  have hEo := pe8u_stationaryV_other p Cv cs t j k hkj D
  have hEm := hEo.mono (pe8u_other_le cs t j) le_rfl
  have hEbd : ∀ ω, opNorm (stationaryV p Cv cs t D k ω) ≤ cE ∧
      fro (stationaryV p Cv cs t D k ω) ≤ cE * Real.sqrt B := by
    intro ω
    have hq := pe8u_Q_bounds (physRidge p Cv D) (pe8u_ridge_nonneg p Cv D)
      (stationaryN p Cv cs t D k ω)
    refine ⟨hq.1.trans (le_max_left _ _), hq.2.trans ?_⟩
    calc Real.sqrt ((min m n : ℕ) : ℝ) ≤ Real.sqrt (p.γstar * B) :=
        Real.sqrt_le_sqrt ((by exact_mod_cast Nat.min_le_left m n : ((min m n : ℕ) : ℝ) ≤ m).trans hm)
      _ = Real.sqrt p.γstar * Real.sqrt B := Real.sqrt_mul' _ (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
  have hEi : Indep ((⨆ (i : Fin m) (l : Fin n),
      MeasurableSpace.comap (fun ω => stationaryV p Cv cs t D k ω i l) inferInstance) ⊔
      otherSigma cs t j) (batchSigma cs t j) P := by
    have hle : (⨆ (i : Fin m) (l : Fin n), MeasurableSpace.comap
        (fun ω => stationaryV p Cv cs t D k ω i l) inferInstance) ≤ otherSigma cs t j :=
      iSup₂_le fun i l => measurable_iff_comap_le.1
        ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp hEo))
    rw [sup_eq_right.mpr hle]
    exact pe8u_indep_other_batch cs t j
  obtain ⟨hInt, _, hR⟩ := hred p rfl rfl m n B Ω P Cv cs t j r D Pt
    (stationaryV p Cv cs t D k) piT s hm hn hCo hCi hB hD hP hjr hs hEbd
    (fun i l => (measurable_pi_apply l).comp ((measurable_pi_apply i).comp hEm)) hEi
  let J : Fin B → ℝ := fun z => ∫ ω, Fs Cv B (Ahat Cv D) Pt w s
    (sampleRemainder p Cv cs t j r D z ω) * pairSigma Cv D (stationaryV p Cv cs t D k ω) ∂P
  have hJ : ∀ z, |J z| ≤ Cs * (Real.sqrt B * s ^ (-(3 / 2 : ℝ)) + Y * (1 / s ^ 2) * p.β ^ (r - k)) := by
    intro z
    exact (hscalar p rfl rfl rfl m n B Ω P Cv cs t k j r D Pt piT s z
      hm hn hCo hCi hB hD hP hkj hjr hs).2.trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hcorr : |w ^ 2 / (B : ℝ) * ∑ z, J z| ≤
      w ^ 2 * (Cs * (Real.sqrt B * s ^ (-(3 / 2 : ℝ)) + Y * (1 / s ^ 2) * p.β ^ (r - k))) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ w ^ 2 / (B : ℝ))]
    have hh := (Finset.abs_sum_le_sum_abs J Finset.univ).trans (Finset.sum_le_sum fun z _ => hJ z)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans (le_of_eq (by field_simp))
  have hrpow : s ^ (-(3 / 2 : ℝ)) ≤ a * s⁻¹ := by
    rw [show (-(3 / 2 : ℝ)) = -(1 / 2 : ℝ) + (-1 : ℝ) by norm_num,
      Real.rpow_add hsp, Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos p.hϱ hs (by norm_num))
      (inv_nonneg.mpr hsp.le)
  have hrpow2 : 1 / s ^ 2 ≤ b * s⁻¹ := by
    calc 1 / s ^ 2 = s⁻¹ * s⁻¹ := by ring
      _ ≤ b * s⁻¹ := mul_le_mul_of_nonneg_right (inv_anti₀ p.hϱ hs) (inv_nonneg.mpr hsp.le)
  refine ⟨hInt, ?_⟩
  have htri := abs_sub
    ((∫ ω, frobIP Pt (dirX (stationaryN p Cv cs t D r ω)
      (w • batchGrad (stationaryV p Cv cs t D k ω) (physBatch Cv (cs.act ((t : ℤ) + j + 1)) ω)) s) ∂P) +
        w ^ 2 / (B : ℝ) * ∑ z, J z) (w ^ 2 / (B : ℝ) * ∑ z, J z)
  rw [add_sub_cancel_right] at htri
  refine (htri.trans (add_le_add hR hcorr)).trans ?_
  have hRle : Cr0 * Real.sqrt B * w / s ≤ Cr * Real.sqrt B * w / s := by
    gcongr
    exact le_max_left _ _
  have hSle : w ^ 2 * (Cs * (Real.sqrt B * s ^ (-(3 / 2 : ℝ)) + Y * (1 / s ^ 2) * p.β ^ (r - k))) ≤
      w ^ 2 * (Cs * (Real.sqrt B * (a * s⁻¹) + Y * (b * s⁻¹) * p.β ^ (r - k))) := by
    gcongr
  refine (add_le_add hRle hSle).trans ?_
  have hw2 : w ^ 2 ≤ w := by dsimp [w]; nlinarith [hw.1, hw.2]
  have hu : 0 ≤ Real.sqrt B * w := mul_nonneg (Real.sqrt_nonneg _) hw.1
  have hv : 0 ≤ Y * w ^ 2 * p.β ^ (r - k) := by positivity
  have haU := mul_le_mul_of_nonneg_left hw2 (mul_nonneg (mul_nonneg hCs ha) (Real.sqrt_nonneg (B : ℝ)))
  have hnum : Cr * Real.sqrt B * w + w ^ 2 * (Cs * (Real.sqrt B * a + Y * b * p.β ^ (r - k))) ≤
      (Cr + Cs * a + Cs * b) * (Real.sqrt B * w + Y * w ^ 2 * p.β ^ (r - k)) := by
    nlinarith [mul_nonneg hCr hv, mul_nonneg (mul_nonneg hCs ha) hv,
      mul_nonneg (mul_nonneg hCs hb) hu]
  convert mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hsp.le) using 1 <;> dsimp [w, Y] <;> ring

set_option maxHeartbeats 1000000 in
-- Checking the composed integral bound and its matrix-valued measurable maps needs extra reductions.
private lemma pe8u_stationary_direction (certQ : Muon.External.GaussianQuadFormLp)
    (p : DynParams) (cP : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m n B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (Cv : Covariances m n) (cs : ChainSamples P m n B)
      (t k j r : ℕ) (D Pt : Mat m n) (piT : ℝ),
      (m : ℝ) ≤ p.γstar * B → (n : ℝ) ≤ p.γstar * B →
      opNorm Cv.Sout ≤ p.CSig → opNorm Cv.Sin ≤ p.CSig → 0 < B →
      riskSigma Cv D = 1 / 2 → IsTest cP piT Pt → k < j → j ≤ r →
      Integrable (fun ω => frobIP Pt (dirDeriv p.ϱ (stationaryN p Cv cs t D r ω)
        (emaW p.β (r - j) • batchGrad (stationaryV p Cv cs t D k ω)
          (physBatch Cv (cs.act ((t : ℤ) + j + 1)) ω)))) P ∧
      |∫ ω, frobIP Pt (dirDeriv p.ϱ (stationaryN p Cv cs t D r ω)
        (emaW p.β (r - j) • batchGrad (stationaryV p Cv cs t D k ω)
          (physBatch Cv (cs.act ((t : ℤ) + j + 1)) ω))) ∂P| ≤
      K * (Real.sqrt B * emaW p.β (r - j) +
        (1 + (B : ℝ) * (diffuseness Cv D * (piT + diffuseness Cv D))) *
          (emaW p.β (r - j)) ^ 2 * p.β ^ (r - k)) := by
  obtain ⟨K, hK, hres⟩ := pe8u_stationary_resolvent certQ p cP
  let I : ℝ := (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), (p.ϱ + u ^ 2)⁻¹
  have hI : 0 ≤ I := mul_nonneg (by positivity)
    (setIntegral_nonneg measurableSet_Ioi fun u _ => by have := p.hϱ; positivity)
  refine ⟨I * K, mul_nonneg hI hK, ?_⟩
  intro m n B Ω _ P _ Cv cs t k j r D Pt piT hm hn hCo hCi hB hD hP hkj hjr
  have hE := (pe8u_stationaryV_other p Cv cs t j k hkj D).mono (pe8u_other_le cs t j) le_rfl
  have hG : Measurable (fun ω => batchGrad (stationaryV p Cv cs t D k ω)
      (physBatch Cv (cs.act ((t : ℤ) + j + 1)) ω)) := by
    have hh : Measurable (fun ω => (stationaryV p Cv cs t D k ω,
        fun a => cs.act ((t : ℤ) + j + 1) a ω)) :=
      hE.prodMk (measurable_pi_iff.mpr fun a => cs.meas_act _ a)
    have he : (fun ω => batchGrad (stationaryV p Cv cs t D k ω)
        (physBatch Cv (cs.act ((t : ℤ) + j + 1)) ω)) =
        (fun x : Mat m n × (Fin B → Vec m × Vec n) => batchGrad x.1 (fun a => phys Cv (x.2 a))) ∘
          (fun ω => (stationaryV p Cv cs t D k ω, fun a => cs.act ((t : ℤ) + j + 1) a ω)) := by
      funext ω; rfl
    rw [he]
    exact (pe8u_batchGrad_cont Cv).measurable.comp hh
  have hiG := pe8u_batch_fro_integrable p Cv cs ((t : ℤ) + j + 1)
    (stationaryV p Cv cs t D k) hE (Real.sqrt ((min m n : ℕ) : ℝ))
    (fun ω => (pe8u_Q_bounds _ (pe8u_ridge_nonneg p Cv D) (stationaryN p Cv cs t D k ω)).2) hCo hCi
  have hiR : Integrable (fun ω => fro (emaW p.β (r - j) •
      batchGrad (stationaryV p Cv cs t D k ω) (physBatch Cv (cs.act ((t : ℤ) + j + 1)) ω))) P := by
    simp_rw [pe8_fro_smul]
    exact hiG.const_mul _
  let R : Ω → Mat m n := fun ω => emaW p.β (r - j) •
    batchGrad (stationaryV p Cv cs t D k ω) (physBatch Cv (cs.act ((t : ℤ) + j + 1)) ω)
  let L : ℝ := K * (Real.sqrt B * emaW p.β (r - j) +
    (1 + (B : ℝ) * (diffuseness Cv D * (piT + diffuseness Cv D))) *
      (emaW p.β (r - j)) ^ 2 * p.β ^ (r - k))
  have hb : ∀ s, p.ϱ ≤ s →
      |∫ ω, frobIP Pt (dirX (stationaryN p Cv cs t D r ω) (R ω) s) ∂P| ≤ L / s := by
    intro s hs
    exact (hres m n B Ω P Cv cs t k j r D Pt piT s hm hn hCo hCi hB hD hP hkj hjr hs).2
  have hh := pe8u_integrate_dir p.ϱ p.hϱ Pt (stationaryN p Cv cs t D r) R
    (pe8u_stationaryN_meas p Cv cs t r D) (hG.const_smul (emaW p.β (r - j))) hiR L hb
  refine ⟨hh.1, hh.2.trans (le_of_eq ?_)⟩
  dsimp only [I, L]
  ring

private lemma pe8u_stationary_tangent_eq {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (p : DynParams) (Cv : Covariances m n) (cs : ChainSamples P m n B)
    (t r : ℕ) (D Pt : Mat m n) (hD : 0 < riskSigma Cv D) (ω : Ω) :
    frobIP Pt (causalDot p Cv (fun s => physBatch Cv (cs.act s) ω) t D
      (chainInit p.β Cv D (cs.aux (t : ℤ)) ω) r) =
      -(∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
        frobIP Pt (dirDeriv (physRidge p Cv D) (stationaryN p Cv cs t D r ω)
          (emaW p.β (r - j) • batchGrad (stationaryV p Cv cs t D k ω)
            (physBatch Cv (cs.act ((t : ℤ) + j + 1)) ω)))) -
      2 * p.ϱ * ∑ k ∈ Finset.range r,
        pairSigma Cv D (stationaryV p Cv cs t D k ω) *
          frobIP Pt (ridgeDeriv (physRidge p Cv D) (stationaryN p Cv cs t D r ω)) := by
  have hℓ : 0 < physRidge p Cv D := by unfold physRidge; exact mul_pos (mul_pos (by norm_num) hD) p.hϱ
  rw [pe8u_causalDot_eq p Cv _ t D _ hD r, pe8s_frobIP_add, pe8s_frobIP_smul]
  simp only [tangentM, pe8u_dirDeriv_neg hℓ, pe8u_dirDeriv_sum hℓ,
    pe8u_frobIP_neg_right, pe8u_frobIP_sum_right, pe8u_pairSigma_sum_right]
  simp only [Finset.sum_mul, Finset.mul_sum, neg_mul, mul_assoc, sub_eq_add_neg]
  rfl

private lemma pe8u_stationary_unit (certQ : Muon.External.GaussianQuadFormLp)
    (p : DynParams) (cP : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m n B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (Cv : Covariances m n) (cs : ChainSamples P m n B)
      (t r : ℕ) (D Pt : Mat m n) (piT : ℝ),
      (m : ℝ) ≤ p.γstar * B → (n : ℝ) ≤ p.γstar * B →
      opNorm Cv.Sout ≤ p.CSig → opNorm Cv.Sin ≤ p.CSig → 0 < B →
      riskSigma Cv D = 1 / 2 → IsTest cP piT Pt →
      Integrable (fun ω => frobIP Pt (causalDot p Cv (fun s => physBatch Cv (cs.act s) ω) t D
        (chainInit p.β Cv D (cs.aux (t : ℤ)) ω) r)) P ∧
      |∫ ω, frobIP Pt (causalDot p Cv (fun s => physBatch Cv (cs.act s) ω) t D
        (chainInit p.β Cv D (cs.aux (t : ℤ)) ω) r) ∂P| ≤
      K * (Real.sqrt B * r + 1 + (B : ℝ) * (diffuseness Cv D * (piT + diffuseness Cv D))) := by
  obtain ⟨CM, hCM, hM⟩ := pe8u_stationary_direction certQ p cP
  obtain ⟨CR0, hR⟩ := lem_app_dyn_ridge p.γstar p.CSig p.ϱ cP
  let CR := max CR0 0
  let b := (1 - p.β)⁻¹
  have hCR : 0 ≤ CR := le_max_right _ _
  have hb : 0 ≤ b := inv_nonneg.mpr (sub_nonneg.mpr p.hβ.2.le)
  have hϱ : 0 ≤ 2 * p.ϱ := by have := p.hϱ; positivity
  refine ⟨CM + 2 * p.ϱ * CR * (1 + b), by positivity, ?_⟩
  intro m n B Ω _ P _ Cv cs t r D Pt piT hm hn hCo hCi hB hD hP
  have hDp : 0 < riskSigma Cv D := by rw [hD]; norm_num
  have hℓ : physRidge p Cv D = p.ϱ := by simp [physRidge, hD]
  let F : ℕ → ℕ → Ω → ℝ := fun j k ω => frobIP Pt (dirDeriv p.ϱ (stationaryN p Cv cs t D r ω)
    (emaW p.β (r - j) • batchGrad (stationaryV p Cv cs t D k ω)
      (physBatch Cv (cs.act ((t : ℤ) + j + 1)) ω)))
  let H : ℕ → Ω → ℝ := fun k ω => pairSigma Cv D (stationaryV p Cv cs t D k ω) *
    frobIP Pt (ridgeDeriv p.ϱ (stationaryN p Cv cs t D r ω))
  let ε := diffuseness Cv D * (piT + diffuseness Cv D)
  have hδ : 0 ≤ diffuseness Cv D := pe8_opNorm_nonneg _
  have hπ : 0 ≤ piT := (pe8_opNorm_nonneg Pt).trans hP.2.1
  have hε : 0 ≤ ε := mul_nonneg hδ (add_nonneg hπ hδ)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hsB : 1 ≤ Real.sqrt B := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg B)).2 (by simpa using hB1)
  have hFi : ∀ j ∈ Finset.range (r + 1), ∀ k ∈ Finset.range j, Integrable (F j k) P := by
    intro j hj k hk
    exact (hM m n B Ω P Cv cs t k j r D Pt piT hm hn hCo hCi hB hD hP
      (Finset.mem_range.mp hk) (by have := Finset.mem_range.mp hj; omega)).1
  have hHi : ∀ k, Integrable (H k) P := fun k =>
    (hR p rfl rfl rfl m n B Ω P Cv cs t k r D Pt piT hm hn hCo hCi hB hD hP).1
  have hsum := pe8u_integral_dsum r F hFi
  have hsumH := integrable_finsetSum (Finset.range r) fun k _ => hHi k
  have he : (fun ω => frobIP Pt (causalDot p Cv (fun s => physBatch Cv (cs.act s) ω) t D
      (chainInit p.β Cv D (cs.aux (t : ℤ)) ω) r)) =
      fun ω => -(∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, F j k ω) -
        2 * p.ϱ * ∑ k ∈ Finset.range r, H k ω := by
    funext ω
    simpa only [hℓ] using pe8u_stationary_tangent_eq p Cv cs t r D Pt hDp ω
  rw [he]
  refine ⟨hsum.1.neg.sub (hsumH.const_mul _), ?_⟩
  have ei : (∫ ω, -(∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, F j k ω) -
      2 * p.ϱ * ∑ k ∈ Finset.range r, H k ω ∂P) =
      -(∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, ∫ ω, F j k ω ∂P) -
        2 * p.ϱ * ∑ k ∈ Finset.range r, ∫ ω, H k ω ∂P := by
    rw [integral_sub (by exact hsum.1.neg) (hsumH.const_mul (2 * p.ϱ)), integral_neg,
      integral_const_mul, hsum.2, integral_finsetSum _ (fun k _ => hHi k)]
  rw [ei]
  have hMb : |∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, ∫ ω, F j k ω ∂P| ≤
      CM * (Real.sqrt B * r + 1 + (B : ℝ) * ε) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.range (r + 1), |∑ k ∈ Finset.range j, ∫ ω, F j k ω ∂P|
        ≤ ∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j,
          CM * (Real.sqrt B * emaW p.β (r - j) +
            (1 + (B : ℝ) * ε) * (emaW p.β (r - j)) ^ 2 * p.β ^ (r - k)) := by
          apply Finset.sum_le_sum
          intro j hj
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
          exact (hM m n B Ω P Cv cs t k j r D Pt piT hm hn hCo hCi hB hD hP
            (Finset.mem_range.mp hk) (by have := Finset.mem_range.mp hj; omega)).2
      _ = CM * (Real.sqrt B * (∑ j ∈ Finset.range (r + 1), ∑ _k ∈ Finset.range j, emaW p.β (r - j)) +
          (1 + (B : ℝ) * ε) * (∑ j ∈ Finset.range (r + 1), (emaW p.β (r - j)) ^ 2 *
            ∑ k ∈ Finset.range j, p.β ^ (r - k))) := by
          simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_assoc]
      _ ≤ CM * (Real.sqrt B * r + (1 + (B : ℝ) * ε) * 1) := by
          gcongr
          · exact pe8u_double_sum_emaW_le p.hβ r
          · exact pe8u_causal_overlap p r
      _ = _ := by ring
  have hRb : |∑ k ∈ Finset.range r, ∫ ω, H k ω ∂P| ≤ CR * (r + (B : ℝ) * ε * b) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range r, |∫ ω, H k ω ∂P|
        ≤ ∑ k ∈ Finset.range r, CR * (1 + (B : ℝ) * ε * p.β ^ (r - k)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkr : k ≤ r := (Finset.mem_range.mp hk).le
          have hh := (hR p rfl rfl rfl m n B Ω P Cv cs t k r D Pt piT hm hn hCo hCi hB hD hP).2
          rw [Nat.dist_eq_sub_of_le_right hkr] at hh
          refine hh.trans ?_
          have heps : diffuseness Cv D * piT ≤ ε := by dsimp [ε]; nlinarith [sq_nonneg (diffuseness Cv D)]
          calc CR0 * (1 + (B : ℝ) * diffuseness Cv D * piT * p.β ^ (r - k))
              ≤ CR * (1 + (B : ℝ) * diffuseness Cv D * piT * p.β ^ (r - k)) := by
                exact mul_le_mul_of_nonneg_right (le_max_left _ _)
                  (by have := pow_nonneg p.hβ.1 (r - k); positivity)
            _ ≤ _ := by
                apply mul_le_mul_of_nonneg_left _ hCR
                have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heps (Nat.cast_nonneg B))
                  (pow_nonneg p.hβ.1 (r - k))
                nlinarith
      _ = CR * (r + (B : ℝ) * ε * ∑ k ∈ Finset.range r, p.β ^ (r - k)) := by
          simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul, mul_one, mul_assoc]
          ring
      _ ≤ _ := by
          gcongr
          exact pe8u_causal_geometric p r
  have htri := abs_sub (-(∑ j ∈ Finset.range (r + 1), ∑ k ∈ Finset.range j, ∫ ω, F j k ω ∂P))
    (2 * p.ϱ * ∑ k ∈ Finset.range r, ∫ ω, H k ω ∂P)
  rw [abs_neg, abs_mul, abs_of_nonneg hϱ] at htri
  refine (htri.trans (add_le_add hMb (mul_le_mul_of_nonneg_left hRb hϱ))).trans ?_
  have hr : (r : ℝ) ≤ Real.sqrt B * r := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsB (Nat.cast_nonneg r)
  have hX : 0 ≤ Real.sqrt B * r + 1 + (B : ℝ) * ε := by positivity
  have hy : (r : ℝ) + (B : ℝ) * ε * b ≤ (1 + b) * (Real.sqrt B * r + 1 + (B : ℝ) * ε) := by
    nlinarith [mul_nonneg hb (show 0 ≤ Real.sqrt B * r by positivity)]
  have hh := mul_le_mul_of_nonneg_left hy (mul_nonneg hϱ hCR)
  dsimp [ε] at *
  nlinarith

/-- `prop:app-dyn-stationary-tangent`, snapshot `cr-2026-10-23`. Statement verbatim from `section.tex` (ll. 1415–1425):
```latex
\begin{proposition}[Stationary causal tangent]\label{prop:app-dyn-stationary-tangent}
Let $D$ be deterministic with $r_-\le\cR(D)\le r_+$, let $\Pi$ be a test, and
let $\dot V_r$ be the tangent of \cref{lem:app-dyn-tangent} for the
stationary chain at $(t,D)$, with its initial buffer held fixed. Then for
$r\ge0$,
\[
\lr\,\abs{\EE\langle\Pi,\dot V_r\rangle}\le C\Big\{\frac{r}{\sqrt B}+\frac1B+\epsilon_\Pi\Big\},\qquad
\epsilon_\Pi=\delta(D)\big(\pi_\Pi+\delta(D)\big),
\]
with $C$ depending only on $(c_\Pi,r_-,r_+)$ and the fixed parameters.
\end{proposition}
```
-/
theorem prop_app_dyn_stationary_tangent (certQ : Muon.External.GaussianQuadFormLp) (p : DynParams) (cP rlo rhi : ℝ) :
    ∃ C : ℝ, ∀ (m n B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (Cv : Covariances m n) (cs : ChainSamples P m n B)
      (t r : ℕ) (D Pt : Mat m n) (piT : ℝ),
      (m : ℝ) ≤ p.γstar * B → (n : ℝ) ≤ p.γstar * B →
      opNorm Cv.Sout ≤ p.CSig → opNorm Cv.Sin ≤ p.CSig → 0 < B → 0 < rlo →
      rlo ≤ riskSigma Cv D → riskSigma Cv D ≤ rhi → IsTest cP piT Pt →
      Integrable (fun ω => frobIP Pt (causalDot p Cv (fun s => physBatch Cv (cs.act s) ω) t D
          (chainInit p.β Cv D (cs.aux (t : ℤ)) ω) r)) P ∧
      (p.h / (B : ℝ)) * |∫ ω, frobIP Pt (causalDot p Cv (fun s => physBatch Cv (cs.act s) ω) t D
          (chainInit p.β Cv D (cs.aux (t : ℤ)) ω) r) ∂P|
        ≤ C * ((r : ℝ) / Real.sqrt B + 1 / (B : ℝ)
          + diffuseness Cv D * (piT + diffuseness Cv D)) := by
  obtain ⟨K, hK, hunit⟩ := pe8u_stationary_unit certQ p cP
  by_cases hlo : 0 < rlo
  · let alo := Real.sqrt (2 * rlo)
    have halo : 0 < alo := Real.sqrt_pos.mpr (by linarith)
    refine ⟨p.h * alo⁻¹ * K, ?_⟩
    intro m n B Ω _ P _ Cv cs t r D Pt piT hm hn hCo hCi hB _ hRlo _ hP
    have hD : 0 < riskSigma Cv D := hlo.trans_le hRlo
    let a := Real.sqrt (2 * riskSigma Cv D)
    have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
    have hasq : a ^ 2 = 2 * riskSigma Cv D := Real.sq_sqrt (by linarith)
    have hale : alo ≤ a := Real.sqrt_le_sqrt (by linarith)
    let D' := a⁻¹ • D
    have heD : D = a • D' := by dsimp [D']; rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    have hD' : riskSigma Cv D' = 1 / 2 := by
      dsimp [D']
      rw [pe8u_risk_smul, inv_pow, hasq]
      field_simp
    have hδ : diffuseness Cv D' = diffuseness Cv D :=
      pe8u_diffuseness_scale Cv D a⁻¹ (inv_pos.mpr ha)
    have hu := hunit m n B Ω P Cv cs t r D' Pt piT hm hn hCo hCi hB hD' hP
    let f : Ω → ℝ := fun ω => frobIP Pt (causalDot p Cv (fun s => physBatch Cv (cs.act s) ω) t D'
      (chainInit p.β Cv D' (cs.aux (t : ℤ)) ω) r)
    have he : (fun ω => frobIP Pt (causalDot p Cv (fun s => physBatch Cv (cs.act s) ω) t D
        (chainInit p.β Cv D (cs.aux (t : ℤ)) ω) r)) = fun ω => a⁻¹ * f ω := by
      funext ω
      conv_lhs => rw [heD]
      rw [pe8u_chainInit_smul, pe8u_causalDot_scale p Cv _ t D' _ a ha,
        pe8s_frobIP_smul]
    rw [he]
    refine ⟨hu.1.const_mul _, ?_⟩
    rw [integral_const_mul, abs_mul, abs_of_pos (inv_pos.mpr ha)]
    have hBr : (0 : ℝ) < B := by exact_mod_cast hB
    have hδ0 : 0 ≤ diffuseness Cv D := pe8_opNorm_nonneg _
    have hπ : 0 ≤ piT := (pe8_opNorm_nonneg Pt).trans hP.2.1
    have hX : 0 ≤ Real.sqrt B * r + 1 + (B : ℝ) *
        (diffuseness Cv D * (piT + diffuseness Cv D)) := by positivity
    have hbound : |∫ ω, f ω ∂P| ≤ K * (Real.sqrt B * r + 1 + (B : ℝ) *
        (diffuseness Cv D * (piT + diffuseness Cv D))) := by
      simpa only [hδ] using hu.2
    calc (p.h / (B : ℝ)) * (a⁻¹ * |∫ ω, f ω ∂P|)
        ≤ (p.h / (B : ℝ)) * (alo⁻¹ * (K * (Real.sqrt B * r + 1 + (B : ℝ) *
            (diffuseness Cv D * (piT + diffuseness Cv D))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (inv_anti₀ halo hale) hbound
            (abs_nonneg _) (inv_nonneg.mpr halo.le)) (div_nonneg p.hh.le hBr.le)
      _ = p.h * alo⁻¹ * K * ((r : ℝ) / Real.sqrt B + 1 / (B : ℝ) +
          diffuseness Cv D * (piT + diffuseness Cv D)) := by
        have hs : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBr
        field_simp
        ring_nf
        rw [Real.sq_sqrt hBr.le]
        ring
  · refine ⟨0, ?_⟩
    intro m n B Ω _ P _ Cv cs t r D Pt piT hm hn hCo hCi hB hrlo
    exact (hlo hrlo).elim

end Muon.Dynamics

end

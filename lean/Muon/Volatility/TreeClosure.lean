import Muon.Volatility.TreeDef
import Muon.Foundations.GaussianCombinatorics
import Muon.Volatility.Defs
import Muon.Volatility.OddSpectral
import Muon.External.Certificates

/-!
# Appendix D, part 12: moment closure, norm control and cutoff removal

Work package L-D.12 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/04-volatility/section.tex`: `lem:app-vol-tree-closure` (l.1076–1085, with
`eqn:app-vol-tree-closure`), `lem:app-vol-norm` (l.1158–1167), `lem:app-vol-cutoff` (l.1244–1258),
and the two displays they use: `eqn:app-vol-deltaJR` (l.997–1000, with `τ_R` and `δ_{J,R}`) and
`eqn:app-vol-cutoff-matrices` (l.1002–1004, the cutoff matrices `K_l`). Card:
`sections/04-volatility/CARD.md` §2, §3 (rows of the three labels), §5 (row L-D.12), §6 (R3, R22, R24).

Reused, not redefined: `Muon.Volatility.treeWord`, `treeVarpi`, `def_app_vol_tree` (`TreeDef`, L-D.11);
`def_app_vol_product`, `indepSpaceLaw`, `SizeFin` (`Defs`, L-D.2); `contraction`, `oddSharp`,
`IsOddBddLip`, `supNorm`, `lipConst` (`OddSpectral`); `Muon.Setup.FrozenParams`, `Muon.Setup.SpectralData`,
`rOut`, `rIn`; `Muon.opNorm`, `Muon.fro`, `Muon.outer`, `Muon.Covariances`; `Muon.External.GaussianOpNorm`
(certificate, `Certificates.lean`). The Gaussian Isserlis formula is `Muon.Foundations.isserlis_wick`
(`GaussianCombinatorics`, a proved-statement row of the registry, not a certificate): it is used only
in the proof of `lem_app_vol_tree_closure`, so it does not appear in any statement here.

Encoding decisions (shared by the three labels):
* The sample space of the cutoff model is the independent product model `indepSpaceLaw m n B`
  (`Muon.Volatility`, L-D.2): the slots `(s, a)` carry `(g, z, w)`. The cutoff matrices `K_l` are
  functions of this sample. Both `K_1` and `K_2` are built from the slots of one time `t : ℤ`: the
  label `α` of `eqn:app-vol-cutoff-matrices` is the slot time `t + 1 + α`, which is the batch time of
  `M^g_t` (for `α = -j`) and of `M^g_{t+ℓ}` (for `α = m ≥ 1`), by the coefficients
  `eqn:app-vol-tree-coefficients`. The source writes `K_l` without `t` ("for explanation only"); `t` is
  added so that the coupling of `lem:app-vol-cutoff` is a statement about one sample space.
  The statements are for every `t`, since the law of the samples is shift invariant.
* The Gaussian law of `g` is `gaussianReal 0 1`; `m_d(R)` is `treeTruncMoment`; `ϖ_{l,α}` is
  `treeVarpi`. The truncation `1_{|g| ≤ R}` is written as `if |g| ≤ R then g else 0`.
* The source constant `C_0` of `\cite[Theorem~4.4.5]{vershynin2018high}` is not a free parameter:
  it is `gaussOpConst hG`, the witness chosen from the certificate `hG : GaussianOpNorm`. Every
  statement holds for the chosen witness, and `T_⋆`, `D_R` and the event `𝓔` are the defined
  quantities `volTStar`, `volDR`, `cutoffEvent`, not re-quantified.
* Test matrices of `lem:app-vol-tree-closure` are diagonal in the eigenbases of the covariance
  `S : SpectralData Fp.C`: `F = u Diag(F_i) uᵀ`, with `F_i` the entries `Fd`; the response depends
  on the spectra `S.μ`, `S.lam` through `def_app_vol_tree`.
* The tree-closure expectation is asserted to exist (Bochner `Integrable` conjunct), as the source
  takes `𝔼` to be defined. The expectations in `lem_app_vol_cutoff_i` are lower integrals of
  nonnegative quantities (no junk value). The cutoff difference in `lem_app_vol_cutoff_ii` is over
  bounded integrands: `‖f^♯(K)‖ ≤ sup|f|` for odd bounded `f`, so the contraction is bounded.
* The sequence limit of `lem:app-vol-norm` (last clause, "→ 0") is read along dimensions `k` with
  `B_k → ∞` and `SizeFin` at each `k` (the source gives no sequence; the proof uses only `B → ∞`).
  The moment `𝔼[‖K_l‖^p 1_{𝓔^c}]` is the lower integral over `𝓔^c` (no junk value).
* `R > 0` (the setup of the cutoff model, "Fix ... a scalar cutoff `R > 0`") and the size conditions
  `SizeFin` are hypotheses of each statement, as in the source's standing setting.
-/

noncomputable section

open scoped Matrix MatrixOrder ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Topology Polynomial
open Muon Muon.Setup

namespace Muon.Volatility

variable {m n B : ℕ}

/-! ## Cutoff constants and cutoff matrices -/

/-- `τ_R = 𝔼[g² 1_{|g| > R}]` for `g ∼ N(0,1)`, the first display of `eqn:app-vol-deltaJR`
(snapshot `cr-2026-10-23`). Verbatim LaTeX:
```latex
\begin{equation}\label{eqn:app-vol-deltaJR}
\tau_R\defeq\EE\big[g^2\mathbf 1_{\abs g>R}\big],\qquad
\delta_{J,R}\defeq\bmom^{J+1}+\tau_R^{1/2},
\end{equation}
```
-/
def cutoffTau (R : ℝ) : ℝ :=
  ∫ x, (if R < |x| then x ^ 2 else 0) ∂(gaussianReal 0 1)

/-- `δ_{J,R} = β^{J+1} + τ_R^{1/2}`, `eqn:app-vol-deltaJR` (snapshot `cr-2026-10-23`); the convention
`β^{J+1} = 0` for `β = 0` holds for the power with exponent `J + 1 ≥ 1`. Verbatim LaTeX:
```latex
\begin{equation}\label{eqn:app-vol-deltaJR}
\tau_R\defeq\EE\big[g^2\mathbf 1_{\abs g>R}\big],\qquad
\delta_{J,R}\defeq\bmom^{J+1}+\tau_R^{1/2},
\end{equation}
```
-/
def cutoffDelta (β : ℝ) (J : ℕ) (R : ℝ) : ℝ :=
  β ^ (J + 1) + Real.sqrt (cutoffTau R)

/-- The cutoff matrix `K_l` of `eqn:app-vol-cutoff-matrices` (snapshot `cr-2026-10-23`), at time `t`:
`K_l = (1/B) ∑_{α∈𝒜} ∑_{a≤B} ϖ_{l,α} g_{αa} 1_{|g_{αa}| ≤ R} Σ_out^{1/2}(z_{αa} ⊗ w_{αa}) Σ_in^{1/2}`,
with `𝒜 = {-J, …, ℓ}` (`Finset.Icc (-J) ℓ`), `ϖ_{l,α} = treeVarpi β ℓ l α`, and the label `α` read at the
slot `(t + 1 + α, a)` of the independent product model. Verbatim LaTeX:
```latex
\begin{equation}\label{eqn:app-vol-cutoff-matrices}
\mathsf K_l\defeq\frac1B\sum_{\alpha\in\mathcal A}\sum_{a=1}^B\varpi_{l,\alpha}\,g_{\alpha a}\mathbf 1_{\abs{g_{\alpha a}}\le R}\,\Sigmaout^{1/2}(z_{\alpha a}\tensor w_{\alpha a})\Sigmain^{1/2},\qquad l=1,2,
\end{equation}
```
-/
def cutoffMat (Fp : FrozenParams m n B) (ℓ J : ℕ) (R : ℝ) (t : ℤ) (l : ℕ)
    (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) : Mat m n :=
  ((B : ℝ))⁻¹ • ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ), ∑ a : Fin B,
    (treeVarpi Fp.β ℓ l α * (if |(ω (t + 1 + α, a)).1| ≤ R then (ω (t + 1 + α, a)).1 else 0)) •
      (rOut Fp.C * outer (ω (t + 1 + α, a)).2.1 (ω (t + 1 + α, a)).2.2 * rIn Fp.C)

/-- The matrix `Z_α = [z_{αa}]_{a ≤ B} ∈ ℝ^{m×B}` of `lem:app-vol-norm` (snapshot `cr-2026-10-23`),
at time `t`, read at the slots `(t + 1 + α, a)`. -/
def cutoffZ (t α : ℤ) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) : Mat m B :=
  fun i a => (ω (t + 1 + α, a)).2.1 i

/-- The matrix `W_α = [w_{αa}]_{a ≤ B} ∈ ℝ^{n×B}` of `lem:app-vol-norm` (snapshot `cr-2026-10-23`). -/
def cutoffW (t α : ℤ) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) : Mat n B :=
  fun j a => (ω (t + 1 + α, a)).2.2 j

/-- The absolute constant `C_0` of `\cite[Theorem~4.4.5]{vershynin2018high}` (`lem:app-vol-norm`),
taken as the witness of the certificate `GaussianOpNorm` (its existential, CAMPAIGN §5). Every
statement below holds for this witness, and no other choice is made. -/
def gaussOpConst (hG : Muon.External.GaussianOpNorm) : ℝ :=
  Classical.choose hG.holds

/-- `T_⋆ = C_0 (√γ_⋆ + 2)` of `lem:app-vol-norm` (snapshot `cr-2026-10-23`). -/
def volTStar (hG : Muon.External.GaussianOpNorm) (γstar : ℝ) : ℝ :=
  gaussOpConst hG * (Real.sqrt γstar + 2)

/-- `D_R = R C_Σ T_⋆²` of `lem:app-vol-norm` (snapshot `cr-2026-10-23`). -/
def volDR (hG : Muon.External.GaussianOpNorm) (R CSig γstar : ℝ) : ℝ :=
  R * CSig * volTStar hG γstar ^ 2

/-- The event `𝓔 = {‖Z_α‖, ‖W_α‖ ≤ T_⋆ √B for all α ∈ 𝒜}` of `lem:app-vol-norm` (snapshot
`cr-2026-10-23`), at time `t`. -/
def cutoffEvent (hG : Muon.External.GaussianOpNorm) (m n B : ℕ) (ℓ J : ℕ) (γstar : ℝ) (t : ℤ) :
    Set ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) :=
  {ω | ∀ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
    opNorm (cutoffZ t α ω) ≤ volTStar hG γstar * Real.sqrt (B : ℝ) ∧
      opNorm (cutoffW t α ω) ≤ volTStar hG γstar * Real.sqrt (B : ℝ)}

/-! ## Moment closure -/

/-- The polynomial wrapper in `def_app_vol_tree` selects the requested monomial response. -/
private lemma treeClosure_monomial {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (a b : ℕ) :
    def_app_vol_tree β ℓ J R B μ lam Fd Gd
        (Polynomial.X ^ (2 * a + 1)) (Polynomial.X ^ (2 * b + 1)) =
      treeMono β ℓ J R B μ lam Fd Gd a b := by
  have ha : a ≤ 2 * a + 1 := by omega
  have hb : b ≤ 2 * b + 1 := by omega
  simp [def_app_vol_tree, ha, hb]

/-- The graph-theoretic counting step used after the Wick pairing expansion. -/
private lemma treeClosure_vertex_card_le {V : Type*} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hG : G.Connected) (hedges : Nat.card G.edgeSet ≤ k) : Nat.card V ≤ k + 1 := by
  exact hG.card_vert_le_card_edgeSet_add_one.trans (Nat.add_le_add_right hedges 1)

/-- Wick's formula rewritten with the matching type used by the tree response. -/
private lemma treeClosure_isserlis (d k : ℕ) (c : Fin k → Fin d) :
    ∫ z, (∏ r : Fin k, z (c r)) ∂(Muon.Foundations.stdGaussianPi d) =
      (Nat.card {σ : TreeMatch k // ∀ i, c (σ.1 i) = c i} : ℝ) := by
  rw [Muon.Foundations.isserlis_wick]
  congr 1
  apply Nat.card_congr
  exact
    { toFun := fun σ => ⟨⟨σ.1, σ.2.1⟩, σ.2.2⟩
      invFun := fun σ => ⟨σ.1.1, ⟨σ.1.2, σ.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Every coordinate monomial in one independent Gaussian slot is integrable. -/
private lemma treeClosure_slot_monomial_integrable {m n : ℕ} (dg : ℕ)
    (dz : Fin m → ℕ) (dw : Fin n → ℕ) :
    Integrable (fun p : ℝ × (Vec m × Vec n) =>
      p.1 ^ dg * ((∏ i, p.2.1 i ^ dz i) * ∏ j, p.2.2 j ^ dw j))
      (indepSlotLaw m n) := by
  exact (Muon.Foundations.gaussian_integrable_pow dg).mul_prod
    ((Integrable.fintype_prod fun i => Muon.Foundations.gaussian_integrable_pow (dz i)).mul_prod
      (Integrable.fintype_prod fun j => Muon.Foundations.gaussian_integrable_pow (dw j)))

/-- Truncating the scalar coordinate preserves integrability of a one-slot monomial. -/
private lemma treeClosure_slot_trunc_monomial_integrable {m n : ℕ} (R : ℝ) (dg : ℕ)
    (dz : Fin m → ℕ) (dw : Fin n → ℕ) :
    Integrable (fun p : ℝ × (Vec m × Vec n) =>
      (if |p.1| ≤ R then p.1 else 0) ^ dg *
        ((∏ i, p.2.1 i ^ dz i) * ∏ j, p.2.2 j ^ dw j))
      (indepSlotLaw m n) := by
  refine (treeClosure_slot_monomial_integrable dg dz dw).norm.mono' ?_ ?_
  · have ht : Measurable (fun p : ℝ × (Vec m × Vec n) =>
        if |p.1| ≤ R then p.1 else 0) := by
      exact Measurable.ite
        (measurableSet_le (measurable_abs.comp measurable_fst) measurable_const)
        measurable_fst measurable_const
    exact ((ht.pow_const dg).mul (by fun_prop)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    simp only [norm_mul]
    gcongr
    rw [norm_pow, norm_pow]
    gcongr
    split_ifs <;> simp

/-- Pullback of a one-slot Gaussian monomial to any coordinate of the infinite product model. -/
private lemma treeClosure_eval_monomial_integrable {m n B : ℕ} (s : ℤ × Fin B) (dg : ℕ)
    (dz : Fin m → ℕ) (dw : Fin n → ℕ) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      (ω s).1 ^ dg * ((∏ i, (ω s).2.1 i ^ dz i) * ∏ j, (ω s).2.2 j ^ dw j))
      (indepSpaceLaw m n B) := by
  have hm : MeasurePreserving
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω s)
      (indepSpaceLaw m n B) (indepSlotLaw m n) :=
    ⟨measurable_pi_apply s, by
      unfold indepSpaceLaw
      exact Measure.infinitePi_map_eval _ s⟩
  exact hm.integrable_comp_of_integrable
    (treeClosure_slot_monomial_integrable dg dz dw)

/-- Products of integrable functions of finitely many distinct slots remain integrable. -/
private lemma treeClosure_finite_slot_prod_integrable {m n B : ℕ}
    (I : Finset (ℤ × Fin B)) (f : (ℤ × Fin B) → ℝ × (Vec m × Vec n) → ℝ)
    (hf : ∀ s ∈ I, Integrable (f s) (indepSlotLaw m n)) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ∏ s ∈ I, f s (ω s))
      (indepSpaceLaw m n B) := by
  have hm : MeasurePreserving I.restrict (indepSpaceLaw m n B)
      (Measure.pi fun _ : I => indepSlotLaw m n) := by
    refine ⟨Finset.measurable_restrict I, ?_⟩
    unfold indepSpaceLaw
    exact Measure.infinitePi_map_restrict (μ := fun _ : ℤ × Fin B => indepSlotLaw m n)
  have hprod : Integrable (fun x : (s : I) → ℝ × (Vec m × Vec n) =>
      ∏ s : I, f s.1 (x s)) (Measure.pi fun _ : I => indepSlotLaw m n) :=
    Integrable.fintype_prod fun s : I => hf s.1 s.2
  refine (hm.integrable_comp_of_integrable hprod).congr
    (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only [Function.comp_apply, Finset.restrict]
  exact (Finset.prod_subtype (p := fun s => s ∈ I) I (by simp) (fun s => f s (ω s))).symm

/-- Finite products of (possibly different) truncated Gaussian slot monomials are integrable. -/
private lemma treeClosure_finite_trunc_prod_integrable {m n B : ℕ}
    (I : Finset (ℤ × Fin B)) (R : ℝ) (dg : (ℤ × Fin B) → ℕ)
    (dz : (ℤ × Fin B) → Fin m → ℕ) (dw : (ℤ × Fin B) → Fin n → ℕ) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      ∏ s ∈ I, (if |(ω s).1| ≤ R then (ω s).1 else 0) ^ dg s *
        ((∏ i, (ω s).2.1 i ^ dz s i) * ∏ j, (ω s).2.2 j ^ dw s j))
      (indepSpaceLaw m n B) := by
  exact treeClosure_finite_slot_prod_integrable I
    (fun s p => (if |p.1| ≤ R then p.1 else 0) ^ dg s *
      ((∏ i, p.2.1 i ^ dz s i) * ∏ j, p.2.2 j ^ dw s j))
    (fun s _ => treeClosure_slot_trunc_monomial_integrable R (dg s) (dz s) (dw s))

/-! ### Private helpers for `lem:app-vol-tree-closure` (Wick expansion, pairings, counting) -/

-- ===== P12a =====
/-- General-index Isserlis. -/
private lemma tc_isserlis_gen {R' ι' : Type} [Fintype R'] [DecidableEq R'] [Fintype ι'] [DecidableEq ι']
    (L : R' → ι') :
    ∫ y, (∏ r : R', y (L r)) ∂(Measure.pi fun _ : ι' => gaussianReal 0 1) =
      (Nat.card {τ : Equiv.Perm R' // (∀ x, τ (τ x) = x) ∧ (∀ x, τ x ≠ x) ∧ ∀ r, L (τ r) = L r} : ℝ) := by
  classical
  set eR : R' ≃ Fin (Fintype.card R') := Fintype.equivFin R'
  set eI : ι' ≃ Fin (Fintype.card ι') := Fintype.equivFin ι'
  set c : Fin (Fintype.card R') → Fin (Fintype.card ι') := fun q => eI (L (eR.symm q)) with hc
  have h1 := Muon.Foundations.isserlis_wick (Fintype.card ι') (Fintype.card R') c
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ι' => ℝ) eI.symm)
      (Measure.pi fun _ : Fin (Fintype.card ι') => gaussianReal 0 1)
      (Measure.pi fun _ : ι' => gaussianReal 0 1) :=
    measurePreserving_piCongrLeft (fun _ => gaussianReal 0 1) eI.symm
  rw [← hmp.integral_comp']
  have hap : ∀ (x : Fin (Fintype.card ι') → ℝ) (i' : ι'),
      (MeasurableEquiv.piCongrLeft (fun _ : ι' => ℝ) eI.symm) x i' = x (eI i') := by
    intro x i'
    have := MeasurableEquiv.piCongrLeft_apply_apply eI.symm (β := fun _ : ι' => ℝ) x (eI i')
    simpa using this
  simp_rw [hap]
  have hprod : ∀ x : Fin (Fintype.card ι') → ℝ, ∏ r : R', x (eI (L r)) = ∏ q, x (c q) := by
    intro x
    exact Fintype.prod_equiv eR _ _ (fun r => by simp [hc])
  simp_rw [hprod]
  rw [show (Measure.pi fun _ : Fin (Fintype.card ι') => gaussianReal 0 1) =
    Muon.Foundations.stdGaussianPi _ from rfl, h1]
  congr 1
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (eR.symm.permCongr) (fun σ => ?_)
  unfold Muon.Foundations.IsPerfectMatchingInv
  simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply, hc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun x => ?_, fun x h => ?_, fun r => ?_⟩
    · rw [h1 (eR x)]; simp
    · apply h2 (eR x)
      have := congrArg eR h; simpa using this
    · have := h3 (eR r); simpa using this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨fun x => ?_, fun x h => ?_⟩, fun r => ?_⟩
    · have := h1 (eR.symm x); simpa using this
    · apply h2 (eR.symm x)
      have := congrArg eR.symm h; simpa using this
    · have := h3 (eR.symm r); simpa using this

/-- Rotation as a linear isometry equivalence (copy of the foundations helper). -/
private def tc_rotE (k : ℕ) (O : Matrix (Fin k) (Fin k) ℝ) (h1 : Oᵀ * O = 1) (h2 : O * Oᵀ = 1) :
    EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) :=
  LinearEquiv.isometryOfInner
    { toFun := fun x => WithLp.toLp 2 (O *ᵥ WithLp.ofLp x)
      invFun := fun x => WithLp.toLp 2 (Oᵀ *ᵥ WithLp.ofLp x)
      map_add' := by
        intro x y
        ext i
        simp [Matrix.mulVec_add]
      map_smul' := by
        intro c x
        ext i
        simp [Matrix.mulVec_smul]
      left_inv := by
        intro x
        ext i
        change (Oᵀ *ᵥ (O *ᵥ WithLp.ofLp x)) i = WithLp.ofLp x i
        rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
      right_inv := by
        intro x
        ext i
        change (O *ᵥ (Oᵀ *ᵥ WithLp.ofLp x)) i = WithLp.ofLp x i
        rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] }
    (by
      intro x y
      simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.star_mulVec,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one,
        dotProduct_comm])

private lemma tc_map_orthogonal (k : ℕ) (O : Matrix (Fin k) (Fin k) ℝ) (h1 : Oᵀ * O = 1) (h2 : O * Oᵀ = 1) :
    (Muon.Foundations.stdGaussianPi k).map (fun z : Fin k → ℝ => O *ᵥ z)
      = Muon.Foundations.stdGaussianPi k := by
  have hrot : Measurable (tc_rotE k O h1 h2) := (tc_rotE k O h1 h2).continuous.measurable
  have hf : Measurable (fun z : Fin k → ℝ => O *ᵥ z) := by fun_prop
  have he : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) :=
    (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) :=
    (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurableEmbedding
  have hG := stdGaussian_map (tc_rotE k O h1 h2)
  have hcomp : (WithLp.toLp 2 ∘ fun z : Fin k → ℝ => O *ᵥ z)
      = (tc_rotE k O h1 h2) ∘ (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) := by
    funext z
    ext i
    simp [tc_rotE]
  have hbridge : (Muon.Foundations.stdGaussianPi k).map
      (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k))
      = stdGaussian (EuclideanSpace ℝ (Fin k)) := by
    unfold Muon.Foundations.stdGaussianPi
    exact map_pi_eq_stdGaussian
  have key : ((Muon.Foundations.stdGaussianPi k).map (fun z : Fin k → ℝ => O *ᵥ z)).map (WithLp.toLp 2)
      = (Muon.Foundations.stdGaussianPi k).map (WithLp.toLp 2) := by
    rw [Measure.map_map he hf, hcomp, ← Measure.map_map hrot he, hbridge, hG]
  exact hemb.map_injective key
private abbrev TcLam (J ℓ B : ℕ) := {α : ℤ // α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ)} × Fin B

private def tcSlot (t : ℤ) (J ℓ : ℕ) (σ : TcLam J ℓ B) : ℤ × Fin B := (t + 1 + σ.1.1, σ.2)

private lemma tcSlot_injective (t : ℤ) (J ℓ : ℕ) : Function.Injective (tcSlot (B := B) t J ℓ) := by
  intro x y h
  simp only [tcSlot, Prod.mk.injEq] at h
  exact Prod.ext (Subtype.ext (by omega)) h.2

private def tcCoord (t : ℤ) (J ℓ : ℕ) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) :
    TcLam J ℓ B ⊕ (TcLam J ℓ B × (Fin m ⊕ Fin n)) → ℝ
  | Sum.inl σ => (ω (tcSlot t J ℓ σ)).1
  | Sum.inr (σ, Sum.inl i) => (ω (tcSlot t J ℓ σ)).2.1 i
  | Sum.inr (σ, Sum.inr j) => (ω (tcSlot t J ℓ σ)).2.2 j

private lemma tcCoord_measurable (t : ℤ) (J ℓ : ℕ) :
    Measurable (tcCoord (m := m) (n := n) (B := B) t J ℓ) := by
  rw [measurable_pi_iff]
  intro x
  rcases x with σ | ⟨σ, i | j⟩
  · exact (measurable_fst.comp (measurable_pi_apply (tcSlot t J ℓ σ)))
  · exact ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp
      (measurable_pi_apply (tcSlot t J ℓ σ)))))
  · exact ((measurable_pi_apply j).comp (measurable_snd.comp (measurable_snd.comp
      (measurable_pi_apply (tcSlot t J ℓ σ)))))

private lemma tc_coord_law (t : ℤ) (J ℓ : ℕ) :
    (indepSpaceLaw m n B).map (tcCoord t J ℓ) =
      Measure.pi (fun _ : TcLam J ℓ B ⊕ (TcLam J ℓ B × (Fin m ⊕ Fin n)) => gaussianReal 0 1) := by
  classical
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply (tcCoord_measurable t J ℓ) (MeasurableSet.univ_pi hs)]
  set Isl : Finset (ℤ × Fin B) := Finset.univ.image (tcSlot (B := B) t J ℓ) with hIsl
  set bx : TcLam J ℓ B → Set (ℝ × (Vec m × Vec n)) := fun σ =>
    (s (Sum.inl σ)) ×ˢ (Set.pi Set.univ (fun i : Fin m => s (Sum.inr (σ, Sum.inl i))) ×ˢ
      Set.pi Set.univ (fun j : Fin n => s (Sum.inr (σ, Sum.inr j)))) with hbx
  have hbxm : ∀ σ, MeasurableSet (bx σ) := fun σ =>
    (hs _).prod ((MeasurableSet.univ_pi fun i => hs _).prod (MeasurableSet.univ_pi fun j => hs _))
  set tt : ℤ × Fin B → Set (ℝ × (Vec m × Vec n)) :=
    fun x => {q | ∀ σ, tcSlot (B := B) t J ℓ σ = x → q ∈ bx σ} with htt
  have httm : ∀ x, MeasurableSet (tt x) := by
    intro x
    simp only [htt, Set.setOf_forall]
    exact MeasurableSet.iInter fun σ => MeasurableSet.iInter fun _ => hbxm σ
  have hpre : tcCoord (m := m) (n := n) (B := B) t J ℓ ⁻¹' (Set.univ.pi s) =
      Set.pi (↑Isl : Set (ℤ × Fin B)) tt := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_pi, Finset.mem_coe, hIsl,
      Finset.mem_image, Finset.mem_univ, true_and, htt, Set.mem_setOf_eq, hbx, Set.mem_prod]
    constructor
    · rintro h x ⟨σ0, rfl⟩ σ hσ
      have := tcSlot_injective t J ℓ hσ
      subst this
      refine ⟨h (Sum.inl _) (Set.mem_univ _), fun i _ => h (Sum.inr (_, Sum.inl i)) (Set.mem_univ _),
        fun j _ => h (Sum.inr (_, Sum.inr j)) (Set.mem_univ _)⟩
    · intro h a
      rcases a with σ | ⟨σ, i | j⟩
      · exact fun _ => (h _ ⟨σ, rfl⟩ σ rfl).1
      · exact fun _ => (h _ ⟨σ, rfl⟩ σ rfl).2.1 i (Set.mem_univ _)
      · exact fun _ => (h _ ⟨σ, rfl⟩ σ rfl).2.2 j (Set.mem_univ _)
  rw [hpre, indepSpaceLaw, Measure.infinitePi_pi _ (fun x _ => httm x),
    Finset.prod_image (fun x _ y _ hxy => tcSlot_injective t J ℓ hxy)]
  have hbox : ∀ σ : TcLam J ℓ B, tt (tcSlot t J ℓ σ) = bx σ := by
    intro σ
    ext q
    simp only [htt, Set.mem_setOf_eq]
    constructor
    · intro h; exact h σ rfl
    · intro h σ' hσ'
      have := tcSlot_injective t J ℓ hσ'
      subst this
      exact h
  simp_rw [hbox]
  have hslot : ∀ σ : TcLam J ℓ B, indepSlotLaw m n (bx σ) =
      gaussianReal 0 1 (s (Sum.inl σ)) *
        ((∏ i : Fin m, gaussianReal 0 1 (s (Sum.inr (σ, Sum.inl i)))) *
          ∏ j : Fin n, gaussianReal 0 1 (s (Sum.inr (σ, Sum.inr j)))) := by
    intro σ
    simp only [hbx]
    unfold indepSlotLaw Muon.Foundations.stdGaussianPi
    rw [Measure.prod_prod, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
  simp_rw [hslot]
  have e2 := Fintype.prod_prod_type
    (fun p : TcLam J ℓ B × (Fin m ⊕ Fin n) => gaussianReal 0 1 (s (Sum.inr p)))
  rw [Fintype.prod_sum_type, e2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [Fintype.prod_sum_type]

private def tcRot (P : Matrix (Fin m) (Fin m) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) : (ℤ × Fin B) → ℝ × (Vec m × Vec n) :=
  fun s => ((ω s).1, (P *ᵥ (ω s).2.1, Q *ᵥ (ω s).2.2))

private lemma tc_rot_law (P : Matrix (Fin m) (Fin m) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hP1 : Pᵀ * P = 1) (hP2 : P * Pᵀ = 1) (hQ1 : Qᵀ * Q = 1) (hQ2 : Q * Qᵀ = 1) :
    (indepSpaceLaw m n B).map (tcRot P Q) = indepSpaceLaw m n B := by
  have hslot : (indepSlotLaw m n).map (fun q : ℝ × (Vec m × Vec n) => (q.1, (P *ᵥ q.2.1, Q *ᵥ q.2.2)))
      = indepSlotLaw m n := by
    have hm1 : Measurable (fun z : Vec m => P *ᵥ z) := by fun_prop
    have hm2 : Measurable (fun w : Vec n => Q *ᵥ w) := by fun_prop
    have e1 : (fun q : ℝ × (Vec m × Vec n) => (q.1, (P *ᵥ q.2.1, Q *ᵥ q.2.2))) =
        Prod.map id (Prod.map (fun z : Vec m => P *ᵥ z) (fun w : Vec n => Q *ᵥ w)) := rfl
    rw [e1]
    unfold indepSlotLaw
    rw [← Measure.map_prod_map _ _ measurable_id (hm1.prodMap hm2),
      ← Measure.map_prod_map _ _ hm1 hm2, tc_map_orthogonal m P hP1 hP2,
      tc_map_orthogonal n Q hQ1 hQ2, Measure.map_id]
  have hmeas : ∀ s : ℤ × Fin B, Measurable (fun q : ℝ × (Vec m × Vec n) =>
      (q.1, (P *ᵥ q.2.1, Q *ᵥ q.2.2))) := fun _ => by fun_prop
  have := Measure.infinitePi_map_pi (μ := fun _ : ℤ × Fin B => indepSlotLaw m n)
    (f := fun _ q => (q.1, (P *ᵥ q.2.1, Q *ᵥ q.2.2))) hmeas
  simp only [hslot] at this
  exact this

private lemma tc_theta_integral {Λ' E' K2 : Type} [Fintype Λ'] [DecidableEq Λ'] [Fintype E'] [DecidableEq E']
    [Fintype K2] [DecidableEq K2] (k : ℕ) (R : ℝ) (ξ : Fin k → Λ') (Lab : K2 → Λ' × E') :
    ∫ x, ((∏ s : Fin k, (if |x (Sum.inl (ξ s))| ≤ R then x (Sum.inl (ξ s)) else 0)) *
        ∏ r : K2, x (Sum.inr (Lab r)))
      ∂(Measure.pi (fun _ : Λ' ⊕ (Λ' × E') => gaussianReal 0 1)) =
    (∏ σ : Λ', ∫ u, (if |u| ≤ R then u else 0) ^ (Finset.univ.filter fun s : Fin k => ξ s = σ).card
        ∂(gaussianReal 0 1)) *
      (Nat.card {τ : Equiv.Perm K2 // (∀ x, τ (τ x) = x) ∧ (∀ x, τ x ≠ x) ∧
        ∀ r, Lab (τ r) = Lab r} : ℝ) := by
  classical
  have hmp := measurePreserving_sumPiEquivProdPi (X := fun _ : Λ' ⊕ (Λ' × E') => ℝ)
    (fun _ => gaussianReal 0 1)
  have := hmp.integral_comp' (g := fun p : (Λ' → ℝ) × ((Λ' × E') → ℝ) =>
    (∏ s : Fin k, (if |p.1 (ξ s)| ≤ R then p.1 (ξ s) else 0)) * ∏ r : K2, p.2 (Lab r))
  have e : ∀ x : Λ' ⊕ (Λ' × E') → ℝ, (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Λ' ⊕ (Λ' × E') => ℝ)) x = (fun i => x (Sum.inl i), fun i' => x (Sum.inr i')) :=
    fun x => rfl
  simp only [e] at this
  rw [this]
  refine (integral_prod_mul (μ := Measure.pi (fun _ : Λ' => gaussianReal 0 1))
    (ν := Measure.pi (fun _ : Λ' × E' => gaussianReal 0 1))
    (fun y : Λ' → ℝ => ∏ s : Fin k, (if |y (ξ s)| ≤ R then y (ξ s) else 0))
    (fun y : Λ' × E' → ℝ => ∏ r : K2, y (Lab r))).trans ?_
  congr 1
  · -- g part
    have h1 : ∀ y : Λ' → ℝ, ∏ s : Fin k, (if |y (ξ s)| ≤ R then y (ξ s) else 0) =
        ∏ σ : Λ', (if |y σ| ≤ R then y σ else 0) ^
          (Finset.univ.filter fun s : Fin k => ξ s = σ).card := by
      intro y
      rw [← Finset.prod_fiberwise Finset.univ ξ (fun s => (if |y (ξ s)| ≤ R then y (ξ s) else 0))]
      refine Finset.prod_congr rfl fun σ _ => ?_
      rw [Finset.prod_congr rfl (g := fun _ => (if |y σ| ≤ R then y σ else 0))
        (fun s hs => by rw [(Finset.mem_filter.mp hs).2])]
      rw [Finset.prod_const]
    simp_rw [h1]
    exact integral_fintype_prod_eq_prod (f := fun (σ : Λ') (u : ℝ) =>
      (if |u| ≤ R then u else 0) ^ (Finset.univ.filter fun s : Fin k => ξ s = σ).card)
  · exact tc_isserlis_gen Lab

private lemma tc_theta_integrable {Λ' E' K2 : Type} [Fintype Λ'] [DecidableEq Λ'] [Fintype E'] [DecidableEq E']
    [Fintype K2] [DecidableEq K2] (k : ℕ) (R : ℝ) (ξ : Fin k → Λ') (Lab : K2 → Λ' × E') :
    Integrable (fun x : Λ' ⊕ (Λ' × E') → ℝ =>
      (∏ s : Fin k, (if |x (Sum.inl (ξ s))| ≤ R then x (Sum.inl (ξ s)) else 0)) *
        ∏ r : K2, x (Sum.inr (Lab r)))
      (Measure.pi (fun _ : Λ' ⊕ (Λ' × E') => gaussianReal 0 1)) := by
  classical
  have hmp := measurePreserving_sumPiEquivProdPi (X := fun _ : Λ' ⊕ (Λ' × E') => ℝ)
    (fun _ => gaussianReal 0 1)
  have hA : Integrable (fun y : Λ' → ℝ =>
      ∏ s : Fin k, (if |y (ξ s)| ≤ R then y (ξ s) else 0))
      (Measure.pi (fun _ : Λ' => gaussianReal 0 1)) := by
    refine Integrable.of_bound (C := |R| ^ k) ?_ ?_
    · refine Finset.measurable_prod _ (fun s _ => ?_) |>.aestronglyMeasurable
      exact Measurable.ite (measurableSet_le (measurable_abs.comp (measurable_pi_apply _))
        measurable_const) (measurable_pi_apply _) measurable_const
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [norm_prod]
      calc ∏ s : Fin k, ‖(if |y (ξ s)| ≤ R then y (ξ s) else 0)‖ ≤ ∏ s : Fin k, |R| := by
            refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun s _ => ?_)
            split_ifs with h
            · rw [Real.norm_eq_abs]; exact h.trans (le_abs_self _)
            · simp
        _ = |R| ^ k := by simp
  have hB : Integrable (fun y : Λ' × E' → ℝ => ∏ r : K2, y (Lab r))
      (Measure.pi (fun _ : Λ' × E' => gaussianReal 0 1)) := by
    have h1 : ∀ y : Λ' × E' → ℝ, ∏ r : K2, y (Lab r) =
        ∏ x : Λ' × E', y x ^ (Finset.univ.filter fun r : K2 => Lab r = x).card := by
      intro y
      rw [← Finset.prod_fiberwise Finset.univ Lab (fun r => y (Lab r))]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [Finset.prod_congr rfl (g := fun _ => y x)
        (fun r hr => by rw [(Finset.mem_filter.mp hr).2]), Finset.prod_const]
    simp_rw [h1]
    exact Integrable.fintype_prod (f := fun (x : Λ' × E') (u : ℝ) =>
      u ^ (Finset.univ.filter fun r : K2 => Lab r = x).card)
      (fun x => Muon.Foundations.gaussian_integrable_pow _)
  have hprod := hA.mul_prod hB
  have := hmp.integrable_comp_of_integrable hprod
  exact this

private lemma tc_transfer (t : ℤ) (J ℓ : ℕ) (P : Matrix (Fin m) (Fin m) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hP1 : Pᵀ * P = 1) (hP2 : P * Pᵀ = 1) (hQ1 : Qᵀ * Q = 1) (hQ2 : Q * Qᵀ = 1)
    (F : (TcLam J ℓ B ⊕ (TcLam J ℓ B × (Fin m ⊕ Fin n)) → ℝ) → ℝ)
    (hF : Integrable F (Measure.pi (fun _ : TcLam J ℓ B ⊕ (TcLam J ℓ B × (Fin m ⊕ Fin n)) =>
      gaussianReal 0 1))) :
    Integrable (fun ω => F (tcCoord t J ℓ (tcRot P Q ω))) (indepSpaceLaw m n B) ∧
    ∫ ω, F (tcCoord t J ℓ (tcRot P Q ω)) ∂(indepSpaceLaw m n B) =
      ∫ x, F x ∂(Measure.pi (fun _ : TcLam J ℓ B ⊕ (TcLam J ℓ B × (Fin m ⊕ Fin n)) =>
      gaussianReal 0 1)) := by
  have hrot : Measurable (tcRot (m := m) (n := n) (B := B) P Q) := by
    unfold tcRot
    rw [measurable_pi_iff]
    intro s
    refine (measurable_fst.comp (measurable_pi_apply s)).prodMk ?_
    exact (by fun_prop : Measurable (fun z : Vec m => P *ᵥ z)).comp
        (measurable_fst.comp (measurable_snd.comp (measurable_pi_apply s))) |>.prodMk
      ((by fun_prop : Measurable (fun w : Vec n => Q *ᵥ w)).comp
        (measurable_snd.comp (measurable_snd.comp (measurable_pi_apply s))))
  have hlaw : (indepSpaceLaw m n B).map (fun ω => tcCoord t J ℓ (tcRot P Q ω)) =
      Measure.pi (fun _ : TcLam J ℓ B ⊕ (TcLam J ℓ B × (Fin m ⊕ Fin n)) => gaussianReal 0 1) := by
    rw [← tc_coord_law (m := m) (n := n) (B := B) t J ℓ]
    calc (indepSpaceLaw m n B).map (fun ω => tcCoord t J ℓ (tcRot P Q ω))
        = (indepSpaceLaw m n B).map (tcCoord t J ℓ ∘ tcRot P Q) := rfl
      _ = ((indepSpaceLaw m n B).map (tcRot P Q)).map (tcCoord t J ℓ) :=
          (Measure.map_map (tcCoord_measurable t J ℓ) hrot).symm
      _ = _ := by rw [tc_rot_law P Q hP1 hP2 hQ1 hQ2]
  have hmeas : Measurable (fun ω => tcCoord (m := m) (n := n) (B := B) t J ℓ (tcRot P Q ω)) :=
    (tcCoord_measurable t J ℓ).comp hrot
  rw [← hlaw] at hF
  refine ⟨?_, ?_⟩
  · exact (integrable_map_measure hF.aestronglyMeasurable hmeas.aemeasurable).mp hF
  · rw [← hlaw]
    exact (integral_map hmeas.aemeasurable hF.aestronglyMeasurable).symm

-- ===== P12b =====
private lemma tc_path {E : Type} [Fintype E] [DecidableEq E] (r : ℕ) (X : Fin r → Matrix E E ℝ) (x y : E) :
    (List.ofFn X).prod x y = ∑ c : Fin (r + 1) → E,
      (if c 0 = x ∧ c (Fin.last r) = y then ∏ s : Fin r, X s (c s.castSucc) (c s.succ) else 0) := by
  induction r generalizing x with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, Matrix.one_apply]
    rw [← (Equiv.funUnique (Fin 1) E).symm.sum_comp]
    simp only [Equiv.funUnique_symm_apply, Finset.univ_eq_empty, Finset.prod_empty]
    have h1 : ∀ e : E, (if (uniqueElim e : Fin 1 → E) 0 = x ∧
        (uniqueElim e : Fin 1 → E) (Fin.last 0) = y then (1:ℝ) else 0) =
        if e = x ∧ e = y then 1 else 0 := by
      intro e; simp [uniqueElim_const]
    rw [Finset.sum_congr rfl (fun e _ => h1 e)]
    by_cases h : x = y
    · subst h; simp
    · have : ∀ z : E, (if z = x ∧ z = y then (1:ℝ) else 0) = 0 :=
        fun z => ite_eq_right_iff.mpr (fun ⟨h1, h2⟩ => absurd (h1.symm.trans h2) h)
      simp [this, h]
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    rw [← (Fin.consEquiv (fun _ : Fin (r + 2) => E)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply]
    have hR : ∀ (x₁ : E) (x₂ : Fin (r + 1) → E),
        (if (Fin.cons x₁ x₂ : Fin (r + 2) → E) 0 = x ∧
          (Fin.cons x₁ x₂ : Fin (r + 2) → E) (Fin.last (r + 1)) = y then
          ∏ s : Fin (r + 1), X s ((Fin.cons x₁ x₂ : Fin (r + 2) → E) s.castSucc)
            ((Fin.cons x₁ x₂ : Fin (r + 2) → E) s.succ) else 0) =
        if x₁ = x ∧ x₂ (Fin.last r) = y then
          X 0 x₁ (x₂ 0) * ∏ s : Fin r, X s.succ (x₂ s.castSucc) (x₂ s.succ) else 0 := by
      intro x₁ x₂
      rw [Fin.prod_univ_succ]
      have e1 : (Fin.cons x₁ x₂ : Fin (r + 2) → E) 0 = x₁ := rfl
      have e2 : (Fin.cons x₁ x₂ : Fin (r + 2) → E) (Fin.last (r + 1)) = x₂ (Fin.last r) := by
        rw [← Fin.succ_last, Fin.cons_succ]
      have e3 : (Fin.cons x₁ x₂ : Fin (r + 2) → E) (Fin.castSucc 0) = x₁ := rfl
      have e4 : (Fin.cons x₁ x₂ : Fin (r + 2) → E) (Fin.succ 0) = x₂ 0 := rfl
      have e5 : ∀ s : Fin r, (Fin.cons x₁ x₂ : Fin (r + 2) → E) (Fin.castSucc s.succ) =
          x₂ s.castSucc := fun s => by
        rw [← Fin.succ_castSucc, Fin.cons_succ]
      have e6 : ∀ s : Fin r, (Fin.cons x₁ x₂ : Fin (r + 2) → E) (Fin.succ s.succ) = x₂ s.succ :=
        fun s => by rw [Fin.cons_succ]
      simp only [e1, e2, e3, e4, e5, e6]
    simp only [hR]
    have hL : ∀ j, (List.ofFn fun i : Fin r => X i.succ).prod j y = ∑ c : Fin (r + 1) → E,
        (if c 0 = j ∧ c (Fin.last r) = y then ∏ s : Fin r, X s.succ (c s.castSucc) (c s.succ)
          else 0) := fun j => ih (fun i => X i.succ) j
    simp only [hL, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ (x₁ : E), ∑ x₂ : Fin (r + 1) → E,
        (if x₁ = x ∧ x₂ (Fin.last r) = y then
          X 0 x₁ (x₂ 0) * ∏ s : Fin r, X s.succ (x₂ s.castSucc) (x₂ s.succ) else 0) =
        if x₁ = x then ∑ x₂ : Fin (r + 1) → E, (if x₂ (Fin.last r) = y then
          X 0 x (x₂ 0) * ∏ s : Fin r, X s.succ (x₂ s.castSucc) (x₂ s.succ) else 0) else 0 := by
      intro x₁
      by_cases h : x₁ = x
      · subst h; simp
      · simp [h]
    simp only [h2]
    rw [Finset.sum_ite_eq' Finset.univ x]
    simp only [Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single (c 0)]
    · by_cases hc : c (Fin.last r) = y <;> simp [hc]
    · intro j _ hj
      have : ¬ (c 0 = j ∧ c (Fin.last r) = y) := fun h => hj h.1.symm
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h

private lemma tc_prev_val {k : ℕ} (s : Fin k) :
    (treePrev s).val = if s.val = 0 then k - 1 else s.val - 1 := by
  obtain ⟨v, hv⟩ := s
  unfold treePrev
  dsimp only
  rcases Nat.eq_zero_or_pos v with rfl | hpos
  · simp [Nat.mod_eq_of_lt (show k - 1 < k by omega)]
  · rw [if_neg (show ¬ (v = 0) by omega)]
    have e : v + (k - 1) = (v - 1) + k := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (show v - 1 < k by omega)]

private lemma tc_trace_cyc {E : Type} [Fintype E] [DecidableEq E] (k : ℕ) (hk : 0 < k)
    (X : Fin k → Matrix E E ℝ) :
    Matrix.trace (List.ofFn X).prod = ∑ e : Fin k → E, ∏ s : Fin k, X s (e (treePrev s)) (e s) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  simp only [Matrix.trace, Matrix.diag, tc_path]
  rw [Finset.sum_comm]
  have h1 : ∀ c : Fin (r + 1 + 1) → E, ∑ x : E,
      (if c 0 = x ∧ c (Fin.last (r + 1)) = x then
        ∏ s : Fin (r + 1), X s (c s.castSucc) (c s.succ) else 0) =
      if c 0 = c (Fin.last (r + 1)) then ∏ s : Fin (r + 1), X s (c s.castSucc) (c s.succ) else 0 := by
    intro c
    rw [Finset.sum_eq_single (c 0)]
    · by_cases h : c 0 = c (Fin.last (r + 1))
      · simp [h]
      · rw [if_neg h]; exact if_neg (fun hh => h hh.2.symm)
    · intro j _ hj
      have : ¬ (c 0 = j ∧ c (Fin.last (r + 1)) = j) := fun h => hj h.1.symm
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [h1]
  rw [← (Fin.consEquiv (fun _ : Fin (r + 2) => E)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply]
  have h2 : ∀ (z : E) (e : Fin (r + 1) → E),
      (if (Fin.cons z e : Fin (r + 2) → E) 0 = (Fin.cons z e : Fin (r + 2) → E) (Fin.last (r + 1))
        then ∏ s : Fin (r + 1), X s ((Fin.cons z e : Fin (r + 2) → E) s.castSucc)
          ((Fin.cons z e : Fin (r + 2) → E) s.succ) else 0) =
      if z = e (Fin.last r) then ∏ s : Fin (r + 1), X s (e (treePrev s)) (e s) else 0 := by
    intro z e
    have e1 : (Fin.cons z e : Fin (r + 2) → E) 0 = z := rfl
    have e2 : (Fin.cons z e : Fin (r + 2) → E) (Fin.last (r + 1)) = e (Fin.last r) := by
      rw [← Fin.succ_last, Fin.cons_succ]
    rw [e1, e2]
    by_cases h : z = e (Fin.last r)
    · rw [if_pos h, if_pos h]
      refine Finset.prod_congr rfl fun s _ => ?_
      have e3 : (Fin.cons z e : Fin (r + 2) → E) s.succ = e s := by rw [Fin.cons_succ]
      rw [e3]
      congr 1
      rcases Fin.eq_zero_or_eq_succ s with rfl | ⟨s', rfl⟩
      · have : treePrev (0 : Fin (r + 1)) = Fin.last r := by
          apply Fin.ext
          rw [tc_prev_val]; simp
        rw [this, ← h]; rfl
      · have : treePrev s'.succ = s'.castSucc := by
          apply Fin.ext
          rw [tc_prev_val]; simp
        rw [this, ← Fin.succ_castSucc, Fin.cons_succ]
    · rw [if_neg h, if_neg h]
  simp only [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_ite_eq']
  simp

private def tcDil (K : Mat m n) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 0 K Kᵀ 0

private lemma tc_pow_comm_T (K : Mat m n) (a : ℕ) : (Kᵀ * K) ^ a * Kᵀ = Kᵀ * (K * Kᵀ) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h : (Kᵀ * K) ^ a * (Kᵀ * K) * Kᵀ = ((Kᵀ * K) ^ a * Kᵀ) * (K * Kᵀ) := by
      simp only [Matrix.mul_assoc]
    rw [pow_succ, pow_succ, h, ih]
    simp only [Matrix.mul_assoc]

private lemma tc_dil_pow_odd (K : Mat m n) (a : ℕ) :
    tcDil K ^ (2 * a + 1) =
      Matrix.fromBlocks 0 ((K * Kᵀ) ^ a * K) (Kᵀ * (K * Kᵀ) ^ a) 0 := by
  have hsq : tcDil K * tcDil K = Matrix.fromBlocks (K * Kᵀ) 0 0 (Kᵀ * K) := by
    unfold tcDil; rw [Matrix.fromBlocks_multiply]; simp
  have hpow : ∀ a : ℕ, (Matrix.fromBlocks (K * Kᵀ) 0 0 (Kᵀ * K)) ^ a =
      Matrix.fromBlocks ((K * Kᵀ) ^ a) 0 0 ((Kᵀ * K) ^ a) := by
    intro a
    induction a with
    | zero => simp [Matrix.fromBlocks_one]
    | succ a ih => rw [pow_succ, ih, Matrix.fromBlocks_multiply]; simp [pow_succ]
  rw [pow_succ, pow_mul, pow_two, hsq, hpow]
  unfold tcDil
  rw [Matrix.fromBlocks_multiply]
  simp [tc_pow_comm_T]

private lemma tc_trace_dil (F : Mat m m) (G : Mat n n) (K₁ K₂ : Mat m n) (a b : ℕ) :
    Matrix.trace (treeWord F G K₁ K₂ a b) =
      Matrix.trace (Matrix.fromBlocks F 0 0 0 * tcDil K₁ ^ (2 * a + 1) *
        Matrix.fromBlocks 0 0 0 G * tcDil K₂ ^ (2 * b + 1)) := by
  rw [tc_dil_pow_odd, tc_dil_pow_odd]
  simp only [Matrix.fromBlocks_multiply]
  unfold treeWord
  simp [Matrix.mul_assoc, Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

private lemma tc_ofFn_range {α : Type} (k : ℕ) (W : ℕ → α) :
    List.ofFn (fun s : Fin k => W s.val) = (List.range k).map W := by
  apply List.ext_getElem <;> simp

private lemma tc_block_prod {E : Type} [Fintype E] [DecidableEq E] (p : ℕ) (Fh Gh D : Matrix E E ℝ) :
    ((List.range (p + 1)).map (fun s => (if s = 0 then Fh else 1) * D * (if s = p then Gh else 1))).prod
      = Fh * D ^ (p + 1) * Gh := by
  induction p generalizing Fh with
  | zero => simp
  | succ p ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.prod_cons]
    have : ((fun s : ℕ => (if s = 0 then Fh else 1) * D * (if s = p + 1 then Gh else 1)) ∘
        Nat.succ) = fun s => ((if s = 0 then (1 : Matrix E E ℝ) else 1) * D * (if s = p then Gh else 1)) := by
      funext s
      simp
    rw [this, ih]
    simp [pow_succ', Matrix.mul_assoc]

private lemma tc_word_prod {E : Type} [Fintype E] [DecidableEq E] (a b : ℕ) (Fh Gh D1 D2 : Matrix E E ℝ) :
    ((List.range (2 * a + 2 * b + 2)).map (fun s => (if s = 0 then Fh else 1) *
      (if s ≤ 2 * a then D1 else D2) * (if s = 2 * a then Gh else 1))).prod =
      Fh * D1 ^ (2 * a + 1) * Gh * D2 ^ (2 * b + 1) := by
  rw [show 2 * a + 2 * b + 2 = (2 * a + 1) + (2 * b + 1) by ring, List.range_add, List.map_append,
    List.prod_append, List.map_map]
  congr 1
  · have : (List.range (2 * a + 1)).map (fun s => (if s = 0 then Fh else 1) *
        (if s ≤ 2 * a then D1 else D2) * (if s = 2 * a then Gh else 1)) =
        (List.range (2 * a + 1)).map (fun s => (if s = 0 then Fh else 1) * D1 *
          (if s = 2 * a then Gh else 1)) := by
      refine List.map_congr_left (fun s hs => ?_)
      have : s ≤ 2 * a := by simp at hs; omega
      simp [this]
    rw [this, tc_block_prod]
  · have : (List.range (2 * b + 1)).map ((fun s => (if s = 0 then Fh else 1) *
        (if s ≤ 2 * a then D1 else D2) * (if s = 2 * a then Gh else 1)) ∘ fun x => 2 * a + 1 + x) =
        (List.range (2 * b + 1)).map (fun _ => D2) := by
      refine List.map_congr_left (fun s hs => ?_)
      simp only [Function.comp]
      have h1 : ¬ (2 * a + 1 + s = 0) := by omega
      have h2 : ¬ (2 * a + 1 + s ≤ 2 * a) := by omega
      have h3 : ¬ (2 * a + 1 + s = 2 * a) := by omega
      simp [h1, h2, h3]
    rw [this]
    simp

private lemma tc_prev_zero {k : ℕ} (hk : 0 < k) : treePrev (⟨0, hk⟩ : Fin k) = ⟨k - 1, by omega⟩ := by
  apply Fin.ext; rw [tc_prev_val]; simp

private lemma tc_trace_word_cyc (f : Fin m → ℝ) (g : Fin n → ℝ) (K₁ K₂ : Mat m n) (a b : ℕ) :
    Matrix.trace (treeWord (Matrix.diagonal f) (Matrix.diagonal g) K₁ K₂ a b) =
      ∑ e : Fin (treeK a b) → (Fin m ⊕ Fin n),
        (Sum.elim f (fun _ => 0) (e (treeFMark a b))) * (Sum.elim (fun _ => 0) g (e (treeGMark a b))) *
          ∏ s : Fin (treeK a b), tcDil (if s.val ≤ 2 * a then K₁ else K₂) (e (treePrev s)) (e s) := by
  classical
  rw [tc_trace_dil]
  have hF : (Matrix.fromBlocks (Matrix.diagonal f) 0 0 0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ)
      = Matrix.diagonal (Sum.elim f (fun _ => 0)) := by
    rw [← Matrix.fromBlocks_diagonal]; simp
  have hG : (Matrix.fromBlocks 0 0 0 (Matrix.diagonal g) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ)
      = Matrix.diagonal (Sum.elim (fun _ => 0) g) := by
    rw [← Matrix.fromBlocks_diagonal]; simp
  rw [hF, hG]
  have hprod := tc_word_prod (E := Fin m ⊕ Fin n) a b (Matrix.diagonal (Sum.elim f (fun _ => 0)))
    (Matrix.diagonal (Sum.elim (fun _ => 0) g)) (tcDil K₁) (tcDil K₂)
  rw [← hprod, ← tc_ofFn_range (treeK a b), tc_trace_cyc (treeK a b) (by unfold treeK; omega)]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hent : ∀ (p q : Prop) [Decidable p] [Decidable q] (d d' : Fin m ⊕ Fin n → ℝ)
      (D : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) (x y : Fin m ⊕ Fin n),
      ((if p then Matrix.diagonal d else 1) * D * (if q then Matrix.diagonal d' else 1)) x y =
        (if p then d x else 1) * D x y * (if q then d' y else 1) := by
    intro p q _ _ d d' D x y
    by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [hent]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hk : 0 < treeK a b := by unfold treeK; omega
  have h1 : ∏ s : Fin (treeK a b), (if s.val = 0 then Sum.elim f (fun _ => (0:ℝ)) (e (treePrev s)) else 1)
      = Sum.elim f (fun _ => (0:ℝ)) (e (treeFMark a b)) := by
    rw [Finset.prod_eq_single (⟨0, hk⟩ : Fin (treeK a b))]
    · have hpz : treePrev (⟨0, hk⟩ : Fin (treeK a b)) = treeFMark a b := by
        rw [tc_prev_zero hk]; apply Fin.ext; simp [treeFMark, treeK]
      simp [hpz, show treePrev (0 : Fin (treeK a b)) = treeFMark a b from hpz]
    · intro s _ hs
      have : s.val ≠ 0 := fun h => hs (Fin.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : ∏ s : Fin (treeK a b), (if s.val = 2 * a then Sum.elim (fun _ => (0:ℝ)) g (e s) else 1)
      = Sum.elim (fun _ => (0:ℝ)) g (e (treeGMark a b)) := by
    rw [Finset.prod_eq_single (treeGMark a b)]
    · simp [treeGMark]
    · intro s _ hs
      have : s.val ≠ 2 * a := fun h => hs (Fin.ext (by simpa [treeGMark] using h))
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, h2]
  have h3 : ∀ s : Fin (treeK a b), (if s.val ≤ 2 * a then tcDil K₁ else tcDil K₂) =
      tcDil (if s.val ≤ 2 * a then K₁ else K₂) := fun s => by split_ifs <;> rfl
  simp only [h3]
  ring

-- ===== P12c =====
private lemma tc_sqrt_spec {p : ℕ} (Sm : Mat p p) (hS : Sm.PosSemidef) (U : Mat p p) (μ : Fin p → ℝ)
    (hU : Uᵀ * U = 1)
    (hE : ∀ i, Sm *ᵥ (fun k => U k i) = μ i • (fun k => U k i)) :
    (∀ i, 0 ≤ μ i) ∧ Sm = U * Matrix.diagonal μ * Uᵀ ∧
      CFC.sqrt Sm = U * Matrix.diagonal (fun i => Real.sqrt (μ i)) * Uᵀ := by
  have hU' : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hSU : Sm * U = U * Matrix.diagonal μ := by
    ext i j
    have := congrFun (hE j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal, Matrix.mul_apply, this]; ring
  have hSeq : Sm = U * Matrix.diagonal μ * Uᵀ := by
    calc Sm = Sm * (U * Uᵀ) := by rw [hU', Matrix.mul_one]
      _ = (Sm * U) * Uᵀ := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hSU]
  have hD : Uᵀ * Sm * U = Matrix.diagonal μ := by
    rw [Matrix.mul_assoc, hSU, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hpsd : (Uᵀ * Sm * U).PosSemidef := by
    have := hS.conjTranspose_mul_mul_same U
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hmu : ∀ i, 0 ≤ μ i := by
    intro i
    have := hpsd.diag_nonneg (i := i)
    rw [hD] at this
    simpa using this
  refine ⟨hmu, hSeq, ?_⟩
  have hRR : (U * Matrix.diagonal (fun i => Real.sqrt (μ i)) * Uᵀ) *
      (U * Matrix.diagonal (fun i => Real.sqrt (μ i)) * Uᵀ) = Sm := by
    calc _ = U * Matrix.diagonal (fun i => Real.sqrt (μ i)) * (Uᵀ * U) *
          Matrix.diagonal (fun i => Real.sqrt (μ i)) * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal (fun i => Real.sqrt (μ i)) * Matrix.diagonal (fun i => Real.sqrt (μ i))) * Uᵀ := by
          rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal μ * Uᵀ := by
          rw [Matrix.diagonal_mul_diagonal]
          have : (fun i => Real.sqrt (μ i) * Real.sqrt (μ i)) = μ :=
            funext fun i => Real.mul_self_sqrt (hmu i)
          rw [this]
      _ = Sm := hSeq.symm
  have hRpsd : (U * Matrix.diagonal (fun i => Real.sqrt (μ i)) * Uᵀ).PosSemidef := by
    have hdp : (Matrix.diagonal (fun i => Real.sqrt (μ i))).PosSemidef :=
      Matrix.posSemidef_diagonal_iff.mpr (fun i => Real.sqrt_nonneg _)
    have := hdp.mul_mul_conjTranspose_same U
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  exact (CFC.sqrt_eq_iff Sm _ (Matrix.nonneg_iff_posSemidef.mpr hS)
    (Matrix.nonneg_iff_posSemidef.mpr hRpsd)).mpr hRR

private lemma tc_spec_out (Fp : FrozenParams m n B) (S : SpectralData Fp.C) :
    (∀ i, 0 ≤ S.μ i) ∧ Fp.C.Sout = S.uOut * Matrix.diagonal S.μ * S.uOutᵀ ∧
      rOut Fp.C = S.uOut * Matrix.diagonal (fun i => Real.sqrt (S.μ i)) * S.uOutᵀ :=
  tc_sqrt_spec Fp.C.Sout Fp.C.psdOut S.uOut S.μ S.huOut S.eigOut

private lemma tc_spec_in (Fp : FrozenParams m n B) (S : SpectralData Fp.C) :
    (∀ j, 0 ≤ S.lam j) ∧ Fp.C.Sin = S.vIn * Matrix.diagonal S.lam * S.vInᵀ ∧
      rIn Fp.C = S.vIn * Matrix.diagonal (fun j => Real.sqrt (S.lam j)) * S.vInᵀ :=
  tc_sqrt_spec Fp.C.Sin Fp.C.psdIn S.vIn S.lam S.hvIn S.eigIn

/-- Truncation. -/
private def tcGt (R : ℝ) (u : ℝ) : ℝ := if |u| ≤ R then u else 0

/-- Cutoff matrix in the eigenframe. -/
private def tcKt (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (ℓ J : ℕ) (R : ℝ) (t : ℤ) (l : ℕ)
    (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) : Mat m n :=
  fun i j => (B : ℝ)⁻¹ * ∑ σ : TcLam J ℓ B, treeVarpi Fp.β ℓ l σ.1.1 * tcGt R (ω (tcSlot t J ℓ σ)).1 *
    ((Real.sqrt (S.μ i) * (ω (tcSlot t J ℓ σ)).2.1 i) * (Real.sqrt (S.lam j) * (ω (tcSlot t J ℓ σ)).2.2 j))

private lemma tc_frame_outer (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (z : Vec m) (w : Vec n) :
    S.uOutᵀ * (rOut Fp.C * outer z w * rIn Fp.C) * S.vIn =
      outer (fun i => Real.sqrt (S.μ i) * (S.uOutᵀ *ᵥ z) i)
        (fun j => Real.sqrt (S.lam j) * (S.vInᵀ *ᵥ w) j) := by
  obtain ⟨-, -, hR⟩ := tc_spec_out Fp S
  obtain ⟨-, -, hR'⟩ := tc_spec_in Fp S
  have hsymIn : (rIn Fp.C)ᵀ = rIn Fp.C := by
    rw [hR']; simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have h1 : rOut Fp.C * outer z w * rIn Fp.C =
      outer (rOut Fp.C *ᵥ z) (rIn Fp.C *ᵥ w) := by
    unfold outer
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose, hsymIn]
  rw [h1]
  unfold outer
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  have hUr : S.uOutᵀ * rOut Fp.C = Matrix.diagonal (fun i => Real.sqrt (S.μ i)) * S.uOutᵀ := by
    rw [hR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, S.huOut, Matrix.one_mul]
  have hVr : S.vInᵀ * rIn Fp.C = Matrix.diagonal (fun j => Real.sqrt (S.lam j)) * S.vInᵀ := by
    rw [hR', ← Matrix.mul_assoc, ← Matrix.mul_assoc, S.hvIn, Matrix.one_mul]
  rw [hUr, hVr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  congr 1 <;> (funext i; simp [Matrix.mulVec_diagonal])

private lemma tc_cutoff_frame (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (ℓ J : ℕ) (R : ℝ) (t : ℤ)
    (l : ℕ) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) :
    S.uOutᵀ * cutoffMat Fp ℓ J R t l ω * S.vIn =
      tcKt Fp S ℓ J R t l (tcRot S.uOutᵀ S.vInᵀ ω) := by
  unfold cutoffMat
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul, tc_frame_outer]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, outer, Matrix.vecMulVec_apply]
  unfold tcKt
  congr 1
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_coe_sort (Finset.Icc (-(J : ℤ)) (ℓ : ℤ))]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [tcSlot, tcRot, tcGt]
  rfl

private lemma tc_word_conj (U : Mat m m) (V : Mat n n) (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (hV : Vᵀ * V = 1) (F0 : Mat m m) (G0 : Mat n n) (K₁ K₂ : Mat m n) (a b : ℕ) :
    treeWord (U * F0 * Uᵀ) (V * G0 * Vᵀ) (U * K₁ * Vᵀ) (U * K₂ * Vᵀ) a b =
      U * treeWord F0 G0 K₁ K₂ a b * Uᵀ := by
  have hmul : ∀ A B : Mat m m, (U * A * Uᵀ) * (U * B * Uᵀ) = U * (A * B) * Uᵀ := by
    intro A B
    calc (U * A * Uᵀ) * (U * B * Uᵀ) = U * A * (Uᵀ * U) * B * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hpow : ∀ (M : Mat m m) (c : ℕ), (U * M * Uᵀ) ^ c = U * M ^ c * Uᵀ := by
    intro M c
    induction c with
    | zero => simp [hU']
    | succ c ih => rw [pow_succ, ih, hmul, ← pow_succ]
  have hKK : ∀ K : Mat m n, (U * K * Vᵀ) * (U * K * Vᵀ)ᵀ = U * (K * Kᵀ) * Uᵀ := by
    intro K
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc U * K * Vᵀ * (V * (Kᵀ * Uᵀ)) = U * K * (Vᵀ * V) * Kᵀ * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  unfold treeWord
  rw [hKK, hKK, hpow, hpow, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc U * F0 * Uᵀ * (U * (K₁ * K₁ᵀ) ^ a * Uᵀ) * (U * K₁ * Vᵀ) * (V * G0 * Vᵀ) *
        (V * (K₂ᵀ * Uᵀ)) * (U * (K₂ * K₂ᵀ) ^ b * Uᵀ)
      = U * F0 * (Uᵀ * U) * (K₁ * K₁ᵀ) ^ a * (Uᵀ * U) * K₁ * (Vᵀ * V) * G0 * (Vᵀ * V) * K₂ᵀ *
          (Uᵀ * U) * (K₂ * K₂ᵀ) ^ b * Uᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, hV]; simp only [Matrix.mul_one, Matrix.mul_assoc]

private lemma tc_trace_frame (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (ℓ J : ℕ) (R : ℝ) (t : ℤ)
    (a b : ℕ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (Fm : Mat m m) (Gm : Mat n n)
    (hF : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hG : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) :
    Matrix.trace (treeWord Fm Gm (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω) a b) =
      Matrix.trace (treeWord (Matrix.diagonal Fd) (Matrix.diagonal Gd)
        (tcKt Fp S ℓ J R t 1 (tcRot S.uOutᵀ S.vInᵀ ω))
        (tcKt Fp S ℓ J R t 2 (tcRot S.uOutᵀ S.vInᵀ ω)) a b) := by
  have hU' : S.uOut * S.uOutᵀ = 1 := mul_eq_one_comm.mp S.huOut
  have hV' : S.vIn * S.vInᵀ = 1 := mul_eq_one_comm.mp S.hvIn
  have hK : ∀ l, cutoffMat Fp ℓ J R t l ω =
      S.uOut * tcKt Fp S ℓ J R t l (tcRot S.uOutᵀ S.vInᵀ ω) * S.vInᵀ := by
    intro l
    rw [← tc_cutoff_frame]
    calc cutoffMat Fp ℓ J R t l ω = (S.uOut * S.uOutᵀ) * cutoffMat Fp ℓ J R t l ω *
          (S.vIn * S.vInᵀ) := by rw [hU', hV', Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hK 1, hK 2, hF, hG, tc_word_conj S.uOut S.vIn S.huOut hU' S.hvIn, Matrix.trace_mul_cycle, S.huOut, Matrix.one_mul]

-- ===== P12d =====
/-- `√μ` on external labels. -/
private def tcSqE (μ : Fin m → ℝ) (lam : Fin n → ℝ) : Fin m ⊕ Fin n → ℝ :=
  Sum.elim (fun i => Real.sqrt (μ i)) (fun j => Real.sqrt (lam j))

/-- `μ` on external labels. -/
private def tcNuE (μ : Fin m → ℝ) (lam : Fin n → ℝ) : Fin m ⊕ Fin n → ℝ := Sum.elim μ lam

/-- Pair weight of slot `σ` on external labels. -/
private def tcQQ {J ℓ : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (x : TcLam J ℓ B ⊕ (TcLam J ℓ B × (Fin m ⊕ Fin n)) → ℝ)
    (σ : TcLam J ℓ B) (ε ε' : Fin m ⊕ Fin n) : ℝ :=
  if ε.isLeft = ε'.isLeft then 0 else
    (tcSqE μ lam ε * x (Sum.inr (σ, ε))) * (tcSqE μ lam ε' * x (Sum.inr (σ, ε')))

private lemma tc_dil_entry (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (ℓ J : ℕ) (R : ℝ) (t : ℤ)
    (l : ℕ) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (ε ε' : Fin m ⊕ Fin n) :
    tcDil (tcKt Fp S ℓ J R t l ω) ε ε' =
      (B : ℝ)⁻¹ * ∑ σ : TcLam J ℓ B, treeVarpi Fp.β ℓ l σ.1.1 *
        tcGt R (tcCoord t J ℓ ω (Sum.inl σ)) *
        tcQQ S.μ S.lam (tcCoord t J ℓ ω) σ ε ε' := by
  rcases ε with i | j <;> rcases ε' with i' | j'
  · simp [tcDil, tcQQ]
  · simp only [tcDil, Matrix.fromBlocks_apply₁₂, tcKt, tcQQ, tcSqE, tcCoord]
    congr 1
  · simp only [tcDil, Matrix.fromBlocks_apply₂₁, tcKt, tcQQ, tcSqE, tcCoord, Matrix.transpose_apply]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Sum.isLeft_inr, Sum.isLeft_inl, Bool.false_eq_true, if_false, Sum.elim_inr,
      Sum.elim_inl]
    ring
  · simp [tcDil, tcQQ]

private lemma tc_k_even (a b : ℕ) : (treeK a b) % 2 = 0 := by unfold treeK; omega

private lemma tc_alt_kind (a b : ℕ) (e : Fin (treeK a b) → Fin m ⊕ Fin n)
    (h0 : (e (treeFMark a b)).isLeft = true)
    (hopp : ∀ s, (e (treePrev s)).isLeft ≠ (e s).isLeft) :
    ∀ s : Fin (treeK a b), (e s).isLeft = decide (s.val % 2 = 1) := by
  have key : ∀ N : ℕ, ∀ hn : N < treeK a b, (e ⟨N, hn⟩).isLeft = decide (N % 2 = 1) := by
    intro N
    induction N with
    | zero =>
      intro hn
      have h := hopp ⟨0, hn⟩
      have hp : treePrev (⟨0, hn⟩ : Fin (treeK a b)) = treeFMark a b := by
        apply Fin.ext; rw [tc_prev_val]; simp [treeFMark, treeK]
      rw [hp, h0] at h
      simpa using h
    | succ N ih =>
      intro hn
      have h := hopp ⟨N + 1, hn⟩
      have hp : treePrev (⟨N + 1, hn⟩ : Fin (treeK a b)) = ⟨N, by omega⟩ := by
        apply Fin.ext; rw [tc_prev_val]; simp
      rw [hp, ih (by omega)] at h
      by_cases hN : N % 2 = 1
      · have : ¬ ((N + 1) % 2 = 1) := by omega
        simp only [hN, this, decide_true, decide_false] at h ⊢
        simpa using h
      · have : (N + 1) % 2 = 1 := by omega
        simp only [hN, this, decide_true, decide_false] at h ⊢
        simpa using h
  intro s
  exact key s.val s.isLt

private lemma tc_prev_par (a b : ℕ) (s : Fin (treeK a b)) :
    ((treePrev s).val % 2 = 1) ↔ (s.val % 2 = 0) := by
  have hs := s.isLt
  have hk := tc_k_even a b
  rw [tc_prev_val]
  split_ifs with h <;> omega

private lemma tc_out_in_even (a b : ℕ) (s : Fin (treeK a b)) (h : s.val % 2 = 0) :
    treeOutV s = treePrev s ∧ treeInV s = s := by
  simp [treeOutV, treeInV, treeUntransposed, h]

private lemma tc_out_in_odd (a b : ℕ) (s : Fin (treeK a b)) (h : ¬ s.val % 2 = 0) :
    treeOutV s = s ∧ treeInV s = treePrev s := by
  simp [treeOutV, treeInV, treeUntransposed, h]

private lemma tc_prev_inj (k : ℕ) : Function.Injective (treePrev : Fin k → Fin k) := by
  intro s t h
  have h1 := congrArg Fin.val h
  rw [tc_prev_val, tc_prev_val] at h1
  have := s.isLt
  have := t.isLt
  apply Fin.ext
  split_ifs at h1 <;> omega

private def tcKappa {k : ℕ} (s : Fin k) (ε : Fin m ⊕ Fin n) : ℝ :=
  if ε.isLeft = decide (s.val % 2 = 1) then 1 else 0

private def tcFh (Fd : Fin m → ℝ) : Fin m ⊕ Fin n → ℝ := Sum.elim Fd (fun _ => 0)
private def tcGh (Gd : Fin n → ℝ) : Fin m ⊕ Fin n → ℝ := Sum.elim (fun _ => 0) Gd

private def tcRho {J ℓ : ℕ} (β : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ)
    (Gd : Fin n → ℝ) : TreeVtx (treeK a b) → (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B → ℝ
  | Sum.inl s, Sum.inl ε => tcNuE μ lam ε * tcKappa s ε *
      (if s = treeFMark a b then tcFh Fd ε else 1) * (if s = treeGMark a b then tcGh Gd ε else 1)
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr s, Sum.inr σ => treeVarpi β ℓ (treeLabel a s) σ.1.1

private def tcPsi {J ℓ : ℕ} (a b : ℕ) (e : Fin (treeK a b) → Fin m ⊕ Fin n)
    (ξ : Fin (treeK a b) → TcLam J ℓ B) : TreeVtx (treeK a b) → (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B :=
  Sum.elim (fun s => Sum.inl (e s)) (fun s => Sum.inr (ξ s))

private def tcLab {J ℓ : ℕ} (a b : ℕ) (e : Fin (treeK a b) → Fin m ⊕ Fin n)
    (ξ : Fin (treeK a b) → TcLam J ℓ B) :
    Fin (treeK a b) ⊕ Fin (treeK a b) → TcLam J ℓ B × (Fin m ⊕ Fin n)
  | Sum.inl s => (ξ s, e (treeOutV s))
  | Sum.inr s => (ξ s, e (treeInV s))

private def tcTheta {J ℓ : ℕ} (a b : ℕ) (R : ℝ) (e : Fin (treeK a b) → Fin m ⊕ Fin n)
    (ξ : Fin (treeK a b) → TcLam J ℓ B)
    (x : TcLam J ℓ B ⊕ (TcLam J ℓ B × (Fin m ⊕ Fin n)) → ℝ) : ℝ :=
  (∏ s : Fin (treeK a b), tcGt R (x (Sum.inl (ξ s)))) *
    ∏ r : Fin (treeK a b) ⊕ Fin (treeK a b), x (Sum.inr (tcLab a b e ξ r))

private lemma tc_sq_mul_self (μ : Fin m → ℝ) (lam : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hlam : ∀ j, 0 ≤ lam j)
    (ε : Fin m ⊕ Fin n) : tcSqE μ lam ε * tcSqE μ lam ε = tcNuE μ lam ε := by
  rcases ε with i | j
  · exact Real.mul_self_sqrt (hμ i)
  · exact Real.mul_self_sqrt (hlam j)

private lemma tc_term_pos (β : ℝ) (ℓ J : ℕ) (R : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hlam : ∀ j, 0 ≤ lam j) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (x : TcLam J ℓ B ⊕ (TcLam J ℓ B × (Fin m ⊕ Fin n)) → ℝ)
    (e : Fin (treeK a b) → Fin m ⊕ Fin n) (ξ : Fin (treeK a b) → TcLam J ℓ B)
    (hk : ∀ s, (e s).isLeft = decide (s.val % 2 = 1)) :
    tcFh Fd (e (treeFMark a b)) * tcGh Gd (e (treeGMark a b)) *
      ∏ s : Fin (treeK a b), ((treeVarpi β ℓ (treeLabel a s) (ξ s).1.1 *
        tcGt R (x (Sum.inl (ξ s)))) * tcQQ μ lam x (ξ s) (e (treePrev s)) (e s)) =
    (∏ v : TreeVtx (treeK a b), tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v (tcPsi a b e ξ v)) *
      tcTheta a b R e ξ x := by
  classical
  have hqq : ∀ s, tcQQ μ lam x (ξ s) (e (treePrev s)) (e s) =
      tcSqE μ lam (e (treePrev s)) * tcSqE μ lam (e s) *
        (x (Sum.inr (ξ s, e (treeOutV s))) * x (Sum.inr (ξ s, e (treeInV s)))) := by
    intro s
    have h1 := hk (treePrev s)
    have h2 := hk s
    have hpp := tc_prev_par a b s
    unfold tcQQ
    by_cases hs : s.val % 2 = 0
    · have hp : (treePrev s).val % 2 = 1 := hpp.mpr hs
      have hs' : ¬ (s.val % 2 = 1) := by omega
      rw [if_neg (by rw [h1, h2]; simp [hp, hs'])]
      obtain ⟨ho, hi⟩ := tc_out_in_even a b s hs
      rw [ho, hi]; ring
    · have hp : ¬ (treePrev s).val % 2 = 1 := fun h => hs (hpp.mp h)
      have hs' : s.val % 2 = 1 := by omega
      rw [if_neg (by rw [h1, h2]; simp [hp, hs'])]
      obtain ⟨ho, hi⟩ := tc_out_in_odd a b s hs
      rw [ho, hi]; ring
  have hbij : Function.Bijective (treePrev : Fin (treeK a b) → Fin (treeK a b)) :=
    Finite.injective_iff_bijective.mp (tc_prev_inj _)
  have hsqprod : ∏ s : Fin (treeK a b), tcSqE μ lam (e (treePrev s)) * tcSqE μ lam (e s) =
      ∏ s : Fin (treeK a b), tcNuE μ lam (e s) := by
    rw [Finset.prod_mul_distrib, hbij.prod_comp (fun s => tcSqE μ lam (e s)),
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => tc_sq_mul_self μ lam hμ hlam _
  have hκ : ∏ s : Fin (treeK a b), tcKappa s (e s) = 1 := by
    refine Finset.prod_eq_one fun s _ => ?_
    simp [tcKappa, hk s]
  have hFi : ∏ s : Fin (treeK a b), (if s = treeFMark a b then tcFh Fd (e s) else 1) =
      tcFh Fd (e (treeFMark a b)) := by
    rw [Finset.prod_ite_eq' Finset.univ (treeFMark a b) (fun s => tcFh Fd (e s))]
    simp
  have hGi : ∏ s : Fin (treeK a b), (if s = treeGMark a b then tcGh Gd (e s) else 1) =
      tcGh Gd (e (treeGMark a b)) := by
    rw [Finset.prod_ite_eq' Finset.univ (treeGMark a b) (fun s => tcGh Gd (e s))]
    simp
  have hΘ : ∏ r : Fin (treeK a b) ⊕ Fin (treeK a b), x (Sum.inr (tcLab a b e ξ r)) =
      ∏ s : Fin (treeK a b), (x (Sum.inr (ξ s, e (treeOutV s))) * x (Sum.inr (ξ s, e (treeInV s)))) := by
    rw [Fintype.prod_sum_type, Finset.prod_mul_distrib]
    rfl
  have hρ : ∏ v : TreeVtx (treeK a b), tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v (tcPsi a b e ξ v) =
      (∏ s : Fin (treeK a b), tcNuE μ lam (e s)) *
        (tcFh Fd (e (treeFMark a b)) * tcGh Gd (e (treeGMark a b))) *
        ∏ s : Fin (treeK a b), treeVarpi β ℓ (treeLabel a s) (ξ s).1.1 := by
    rw [Fintype.prod_sum_type]
    simp only [tcPsi, Sum.elim_inl, Sum.elim_inr, tcRho]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hκ, hFi, hGi]
    ring
  rw [hρ, tcTheta, hΘ]
  simp only [hqq]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hsqprod,
    Finset.prod_mul_distrib]
  ring

private lemma tc_term_neg (β : ℝ) (ℓ J : ℕ) (R : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (x : TcLam J ℓ B ⊕ (TcLam J ℓ B × (Fin m ⊕ Fin n)) → ℝ)
    (e : Fin (treeK a b) → Fin m ⊕ Fin n) (ξ : Fin (treeK a b) → TcLam J ℓ B)
    (hk : ¬ ∀ s, (e s).isLeft = decide (s.val % 2 = 1)) :
    tcFh Fd (e (treeFMark a b)) * tcGh Gd (e (treeGMark a b)) *
      ∏ s : Fin (treeK a b), ((treeVarpi β ℓ (treeLabel a s) (ξ s).1.1 *
        tcGt R (x (Sum.inl (ξ s)))) * tcQQ μ lam x (ξ s) (e (treePrev s)) (e s)) =
    (∏ v : TreeVtx (treeK a b), tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v (tcPsi a b e ξ v)) *
      tcTheta a b R e ξ x := by
  classical
  have hR : (∏ v : TreeVtx (treeK a b), tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v (tcPsi a b e ξ v)) = 0 := by
    obtain ⟨s, hs⟩ : ∃ s, ¬ (e s).isLeft = decide (s.val % 2 = 1) := by
      by_contra hcon
      exact hk (fun s => by by_contra hs; exact hcon ⟨s, hs⟩)
    refine Finset.prod_eq_zero (Finset.mem_univ (Sum.inl s)) ?_
    simp [tcRho, tcPsi, tcKappa, hs]
  rw [hR, zero_mul]
  by_contra hne
  have h1 : tcFh Fd (e (treeFMark a b)) ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have h3 : ∏ s : Fin (treeK a b), ((treeVarpi β ℓ (treeLabel a s) (ξ s).1.1 *
        tcGt R (x (Sum.inl (ξ s)))) * tcQQ μ lam x (ξ s) (e (treePrev s)) (e s)) ≠ 0 :=
    right_ne_zero_of_mul hne
  have hleft : (e (treeFMark a b)).isLeft = true := by
    unfold tcFh at h1
    rcases hF : e (treeFMark a b) with i | j
    · rfl
    · rw [hF] at h1; simp at h1
  have hopp : ∀ s, (e (treePrev s)).isLeft ≠ (e s).isLeft := by
    intro s hs
    have := (Finset.prod_ne_zero_iff.mp h3) s (Finset.mem_univ s)
    apply this
    unfold tcQQ
    rw [if_pos hs]
    ring
  exact hk (tc_alt_kind a b e hleft hopp)

private lemma tc_term (β : ℝ) (ℓ J : ℕ) (R : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hlam : ∀ j, 0 ≤ lam j) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (x : TcLam J ℓ B ⊕ (TcLam J ℓ B × (Fin m ⊕ Fin n)) → ℝ)
    (e : Fin (treeK a b) → Fin m ⊕ Fin n) (ξ : Fin (treeK a b) → TcLam J ℓ B) :
    tcFh Fd (e (treeFMark a b)) * tcGh Gd (e (treeGMark a b)) *
      ∏ s : Fin (treeK a b), ((treeVarpi β ℓ (treeLabel a s) (ξ s).1.1 *
        tcGt R (x (Sum.inl (ξ s)))) * tcQQ μ lam x (ξ s) (e (treePrev s)) (e s)) =
    (∏ v : TreeVtx (treeK a b), tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v (tcPsi a b e ξ v)) *
      tcTheta a b R e ξ x := by
  by_cases hk : ∀ s, (e s).isLeft = decide (s.val % 2 = 1)
  · exact tc_term_pos β ℓ J R a b μ lam hμ hlam Fd Gd x e ξ hk
  · exact tc_term_neg β ℓ J R a b μ lam Fd Gd x e ξ hk

-- ===== P12e =====
private theorem tc_expansion (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (ℓ J : ℕ) (R : ℝ) (t : ℤ)
    (a b : ℕ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (Fm : Mat m m) (Gm : Mat n n)
    (hF : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hG : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) :
    (B : ℝ)⁻¹ * Matrix.trace
        (treeWord Fm Gm (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω) a b) =
      ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        ((B : ℝ)⁻¹) ^ (treeK a b + 1) *
          ((∏ v : TreeVtx (treeK a b),
              tcRho (J := J) (ℓ := ℓ) Fp.β a b S.μ S.lam Fd Gd v (tcPsi a b e ξ v)) *
            tcTheta a b R e ξ (tcCoord t J ℓ (tcRot S.uOutᵀ S.vInᵀ ω))) := by
  classical
  obtain ⟨hμ, -, -⟩ := tc_spec_out Fp S
  obtain ⟨hlam, -, -⟩ := tc_spec_in Fp S
  rw [tc_trace_frame Fp S ℓ J R t a b Fd Gd Fm Gm hF hG ω, tc_trace_word_cyc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  set ω' := tcRot S.uOutᵀ S.vInᵀ ω with hω'
  set x := tcCoord t J ℓ ω' with hx
  have hlab : ∀ s : Fin (treeK a b), tcDil (if s.val ≤ 2 * a then tcKt Fp S ℓ J R t 1 ω'
      else tcKt Fp S ℓ J R t 2 ω') = tcDil (tcKt Fp S ℓ J R t (treeLabel a s) ω') := by
    intro s
    unfold treeLabel
    split_ifs <;> rfl
  have hprod : ∏ s : Fin (treeK a b), tcDil (if s.val ≤ 2 * a then tcKt Fp S ℓ J R t 1 ω'
      else tcKt Fp S ℓ J R t 2 ω') (e (treePrev s)) (e s) =
      ((B : ℝ)⁻¹) ^ (treeK a b) * ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        ∏ s : Fin (treeK a b), ((treeVarpi Fp.β ℓ (treeLabel a s) (ξ s).1.1 *
          tcGt R (x (Sum.inl (ξ s)))) * tcQQ S.μ S.lam x (ξ s) (e (treePrev s)) (e s)) := by
    have h1 : ∀ s : Fin (treeK a b), tcDil (if s.val ≤ 2 * a then tcKt Fp S ℓ J R t 1 ω'
        else tcKt Fp S ℓ J R t 2 ω') (e (treePrev s)) (e s) =
        (B : ℝ)⁻¹ * ∑ σ : TcLam J ℓ B, ((treeVarpi Fp.β ℓ (treeLabel a s) σ.1.1 *
          tcGt R (x (Sum.inl σ))) * tcQQ S.μ S.lam x σ (e (treePrev s)) (e s)) := by
      intro s
      rw [hlab s, tc_dil_entry]
    simp only [h1]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_univ_sum]
    rw [Fintype.piFinset_univ]
  rw [hprod]
  have hc : ∀ u : ℝ, (B : ℝ)⁻¹ * (Sum.elim Fd (fun _ => (0 : ℝ)) (e (treeFMark a b)) *
      Sum.elim (fun _ => (0 : ℝ)) Gd (e (treeGMark a b)) *
      (((B : ℝ)⁻¹) ^ (treeK a b) * u)) = ((B : ℝ)⁻¹ ^ (treeK a b + 1) *
        (Sum.elim Fd (fun _ => (0 : ℝ)) (e (treeFMark a b)) *
          Sum.elim (fun _ => (0 : ℝ)) Gd (e (treeGMark a b)))) * u := by
    intro u; ring
  rw [hc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  have this : Sum.elim Fd (fun _ => (0 : ℝ)) (e (treeFMark a b)) *
      Sum.elim (fun _ => (0 : ℝ)) Gd (e (treeGMark a b)) *
      ∏ s : Fin (treeK a b), ((treeVarpi Fp.β ℓ (treeLabel a s) (ξ s).1.1 *
        tcGt R (x (Sum.inl (ξ s)))) * tcQQ S.μ S.lam x (ξ s) (e (treePrev s)) (e s)) =
      (∏ v : TreeVtx (treeK a b),
        tcRho (J := J) (ℓ := ℓ) Fp.β a b S.μ S.lam Fd Gd v (tcPsi a b e ξ v)) *
        tcTheta a b R e ξ x := tc_term Fp.β ℓ J R a b S.μ S.lam hμ hlam Fd Gd x e ξ
  calc _ = ((B : ℝ)⁻¹ ^ (treeK a b + 1)) * (Sum.elim Fd (fun _ => (0 : ℝ)) (e (treeFMark a b)) *
        Sum.elim (fun _ => (0 : ℝ)) Gd (e (treeGMark a b)) *
        ∏ s : Fin (treeK a b), ((treeVarpi Fp.β ℓ (treeLabel a s) (ξ s).1.1 *
          tcGt R (x (Sum.inl (ξ s)))) * tcQQ S.μ S.lam x (ξ s) (e (treePrev s)) (e s))) := by ring
    _ = _ := by rw [this]

-- ===== P12f =====
/-- Expected value of the `g`-truncation product. -/
private def tcEg {J ℓ : ℕ} (a b : ℕ) (R : ℝ) (ξ : Fin (treeK a b) → TcLam J ℓ B) : ℝ :=
  ∏ σ : TcLam J ℓ B, ∫ u, tcGt R u ^ (Finset.univ.filter fun s : Fin (treeK a b) => ξ s = σ).card
    ∂(gaussianReal 0 1)

/-- Number of label-preserving perfect matchings. -/
private def tcNmatch {J ℓ : ℕ} (a b : ℕ) (e : Fin (treeK a b) → Fin m ⊕ Fin n)
    (ξ : Fin (treeK a b) → TcLam J ℓ B) : ℝ :=
  (Nat.card {τ : Equiv.Perm (Fin (treeK a b) ⊕ Fin (treeK a b)) // (∀ x, τ (τ x) = x) ∧
    (∀ x, τ x ≠ x) ∧ ∀ r, tcLab a b e ξ (τ r) = tcLab a b e ξ r} : ℝ)

private theorem tc_expectation (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (ℓ J : ℕ) (R : ℝ) (t : ℤ)
    (a b : ℕ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (Fm : Mat m m) (Gm : Mat n n)
    (hF : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hG : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => (B : ℝ)⁻¹ * Matrix.trace
        (treeWord Fm Gm (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω) a b))
      (indepSpaceLaw m n B) ∧
    ∫ ω, (B : ℝ)⁻¹ * Matrix.trace
        (treeWord Fm Gm (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω) a b)
      ∂(indepSpaceLaw m n B) =
    ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      ((B : ℝ)⁻¹) ^ (treeK a b + 1) *
        ((∏ v : TreeVtx (treeK a b),
          tcRho (J := J) (ℓ := ℓ) Fp.β a b S.μ S.lam Fd Gd v (tcPsi a b e ξ v)) *
          (tcEg a b R ξ * tcNmatch a b e ξ)) := by
  classical
  have hP1 : S.uOutᵀᵀ * S.uOutᵀ = 1 := by
    rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp S.huOut
  have hP2 : S.uOutᵀ * S.uOutᵀᵀ = 1 := by rw [Matrix.transpose_transpose]; exact S.huOut
  have hQ1 : S.vInᵀᵀ * S.vInᵀ = 1 := by
    rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp S.hvIn
  have hQ2 : S.vInᵀ * S.vInᵀᵀ = 1 := by rw [Matrix.transpose_transpose]; exact S.hvIn
  set c : (Fin (treeK a b) → Fin m ⊕ Fin n) → (Fin (treeK a b) → TcLam J ℓ B) → ℝ :=
    fun e ξ => ((B : ℝ)⁻¹) ^ (treeK a b + 1) *
      ∏ v : TreeVtx (treeK a b),
        tcRho (J := J) (ℓ := ℓ) Fp.β a b S.μ S.lam Fd Gd v (tcPsi a b e ξ v) with hc
  set F : (TcLam J ℓ B ⊕ (TcLam J ℓ B × (Fin m ⊕ Fin n)) → ℝ) → ℝ := fun x =>
    ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      c e ξ * tcTheta a b R e ξ x with hFdef
  have hΦ : ∀ ω, (B : ℝ)⁻¹ * Matrix.trace
        (treeWord Fm Gm (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω) a b) =
      F (tcCoord t J ℓ (tcRot S.uOutᵀ S.vInᵀ ω)) := by
    intro ω
    rw [tc_expansion Fp S ℓ J R t a b Fd Gd Fm Gm hF hG ω]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ξ _ => ?_
    simp only [hc]; ring
  have hΘint : ∀ (e : Fin (treeK a b) → Fin m ⊕ Fin n) (ξ : Fin (treeK a b) → TcLam J ℓ B),
      Integrable (fun x => tcTheta a b R e ξ x)
        (Measure.pi (fun _ : TcLam J ℓ B ⊕ (TcLam J ℓ B × (Fin m ⊕ Fin n)) => gaussianReal 0 1)) := by
    intro e ξ
    exact tc_theta_integrable (Λ' := TcLam J ℓ B) (E' := Fin m ⊕ Fin n)
      (K2 := Fin (treeK a b) ⊕ Fin (treeK a b)) (treeK a b) R ξ (tcLab a b e ξ)
  have hFint : Integrable F
      (Measure.pi (fun _ : TcLam J ℓ B ⊕ (TcLam J ℓ B × (Fin m ⊕ Fin n)) => gaussianReal 0 1)) :=
    integrable_finset_sum _ fun e _ => integrable_finset_sum _ fun ξ _ => (hΘint e ξ).const_mul _
  have htr := tc_transfer (m := m) (n := n) (B := B) t J ℓ S.uOutᵀ S.vInᵀ hP1 hP2 hQ1 hQ2 F hFint
  simp_rw [hΦ]
  refine ⟨htr.1, ?_⟩
  rw [htr.2]
  simp only [hFdef]
  rw [integral_finset_sum _ fun e _ => integrable_finset_sum _ fun ξ _ => (hΘint e ξ).const_mul _]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_finset_sum _ fun ξ _ => (hΘint e ξ).const_mul _]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [integral_const_mul]
  have hI : ∫ x, tcTheta a b R e ξ x ∂(Measure.pi (fun _ : TcLam J ℓ B ⊕ (TcLam J ℓ B × (Fin m ⊕ Fin n)) =>
      gaussianReal 0 1)) = tcEg a b R ξ * tcNmatch a b e ξ :=
    tc_theta_integral (Λ' := TcLam J ℓ B) (E' := Fin m ⊕ Fin n)
      (K2 := Fin (treeK a b) ⊕ Fin (treeK a b)) (treeK a b) R ξ (tcLab a b e ξ)
  rw [hI]
  simp only [hc]; ring

-- ===== P12g =====
private lemma tc_lab_ne (a b : ℕ) {J ℓ : ℕ} (e : Fin (treeK a b) → Fin m ⊕ Fin n)
    (ξ : Fin (treeK a b) → TcLam J ℓ B)
    (hk : ∀ s, (e s).isLeft = decide (s.val % 2 = 1)) (s s' : Fin (treeK a b)) :
    tcLab a b e ξ (Sum.inl s) ≠ tcLab a b e ξ (Sum.inr s') := by
  intro h
  have h2 : e (treeOutV s) = e (treeInV s') := congrArg Prod.snd h
  have h3 := hk (treeOutV s)
  have h4 := hk (treeInV s')
  have ho : (treeOutV s).val % 2 = 1 := by
    have := (tc_out_in_even a b s)
    by_cases hs : s.val % 2 = 0
    · rw [(tc_out_in_even a b s hs).1]
      exact (tc_prev_par a b s).mpr hs
    · rw [(tc_out_in_odd a b s hs).1]; omega
  have hi : (treeInV s').val % 2 = 0 := by
    by_cases hs : s'.val % 2 = 0
    · rw [(tc_out_in_even a b s' hs).2]; exact hs
    · rw [(tc_out_in_odd a b s' hs).2]
      have := (tc_prev_par a b s')
      by_contra hc
      exact hs (this.mp (by omega))
  rw [h2] at h3
  rw [h3] at h4
  simp [ho, hi] at h4

private lemma tc_N_eq (a b : ℕ) {J ℓ : ℕ} (e : Fin (treeK a b) → Fin m ⊕ Fin n)
    (ξ : Fin (treeK a b) → TcLam J ℓ B)
    (hk : ∀ s, (e s).isLeft = decide (s.val % 2 = 1)) :
    Nat.card {τ : Equiv.Perm (Fin (treeK a b) ⊕ Fin (treeK a b)) // (∀ x, τ (τ x) = x) ∧
      (∀ x, τ x ≠ x) ∧ ∀ r, tcLab a b e ξ (τ r) = tcLab a b e ξ r} =
    Nat.card {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) //
      ∀ s, tcLab a b e ξ (Sum.inl (p.1.1 s)) = tcLab a b e ξ (Sum.inl s) ∧
        tcLab a b e ξ (Sum.inr (p.2.1 s)) = tcLab a b e ξ (Sum.inr s)} := by
  classical
  symm
  refine Nat.card_eq_of_bijective (fun p => ⟨Equiv.sumCongr p.1.1.1 p.1.2.1, ?_, ?_, ?_⟩) ⟨?_, ?_⟩
  · intro x
    rcases x with s | s
    · simp [p.1.1.2.1 s]
    · simp [p.1.2.2.1 s]
  · intro x
    rcases x with s | s
    · simp [p.1.1.2.2 s]
    · simp [p.1.2.2.2 s]
  · intro r
    rcases r with s | s
    · exact (p.2 s).1
    · exact (p.2 s).2
  · intro p q h
    have h' : Equiv.sumCongr p.1.1.1 p.1.2.1 = Equiv.sumCongr q.1.1.1 q.1.2.1 :=
      congrArg Subtype.val h
    have h1 : p.1.1.1 = q.1.1.1 := by
      refine Equiv.ext fun s => ?_
      have := congrFun (congrArg DFunLike.coe h') (Sum.inl s)
      simpa using this
    have h2 : p.1.2.1 = q.1.2.1 := by
      refine Equiv.ext fun s => ?_
      have := congrFun (congrArg DFunLike.coe h') (Sum.inr s)
      simpa using this
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext h1
    · exact Subtype.ext h2
  · rintro ⟨τ, h1, h2, h3⟩
    have hl : ∀ s, ∃ s', τ (Sum.inl s) = Sum.inl s' := by
      intro s
      rcases h : τ (Sum.inl s) with s' | s'
      · exact ⟨s', rfl⟩
      · exfalso
        have := h3 (Sum.inl s)
        rw [h] at this
        exact tc_lab_ne a b e ξ hk s s' this.symm
    have hr : ∀ s, ∃ s', τ (Sum.inr s) = Sum.inr s' := by
      intro s
      rcases h : τ (Sum.inr s) with s' | s'
      · exfalso
        have := h3 (Sum.inr s)
        rw [h] at this
        exact tc_lab_ne a b e ξ hk s' s this
      · exact ⟨s', rfl⟩
    choose f hf using hl
    choose g hg using hr
    have hff : ∀ s, f (f s) = s := by
      intro s
      have := h1 (Sum.inl s)
      rw [hf s, hf (f s)] at this
      exact Sum.inl_injective this
    have hgg : ∀ s, g (g s) = s := by
      intro s
      have := h1 (Sum.inr s)
      rw [hg s, hg (g s)] at this
      exact Sum.inr_injective this
    have hf0 : ∀ s, f s ≠ s := by
      intro s hs
      have := h2 (Sum.inl s)
      rw [hf s, hs] at this
      exact this rfl
    have hg0 : ∀ s, g s ≠ s := by
      intro s hs
      have := h2 (Sum.inr s)
      rw [hg s, hs] at this
      exact this rfl
    refine ⟨⟨(⟨Function.Involutive.toPerm f hff, fun x => hff x, hf0⟩,
      ⟨Function.Involutive.toPerm g hgg, fun x => hgg x, hg0⟩), ?_⟩, ?_⟩
    · intro s
      refine ⟨?_, ?_⟩
      · have := h3 (Sum.inl s)
        rw [hf s] at this
        exact this
      · have := h3 (Sum.inr s)
        rw [hg s] at this
        exact this
    · apply Subtype.ext
      ext x
      rcases x with s | s
      · simp [hf s]; rfl
      · simp [hg s]; rfl

-- ===== P12h =====
/-- Label-compatibility of a pairing with an assignment. -/
private def TcCompat {J ℓ : ℕ} (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b))
    (e : Fin (treeK a b) → Fin m ⊕ Fin n) (ξ : Fin (treeK a b) → TcLam J ℓ B) : Prop :=
  ∀ s, tcLab a b e ξ (Sum.inl (p.1.1 s)) = tcLab a b e ξ (Sum.inl s) ∧
    tcLab a b e ξ (Sum.inr (p.2.1 s)) = tcLab a b e ξ (Sum.inr s)

/-- The weight `c(e, ξ)`. -/
private def tcC {J ℓ : ℕ} (β : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ)
    (Gd : Fin n → ℝ) (e : Fin (treeK a b) → Fin m ⊕ Fin n)
    (ξ : Fin (treeK a b) → TcLam J ℓ B) : ℝ :=
  ((B : ℝ)⁻¹) ^ (treeK a b + 1) *
    ∏ v : TreeVtx (treeK a b), tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v (tcPsi a b e ξ v)

private lemma tc_C_zero {J ℓ : ℕ} (β : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ)
    (Gd : Fin n → ℝ) (e : Fin (treeK a b) → Fin m ⊕ Fin n)
    (ξ : Fin (treeK a b) → TcLam J ℓ B)
    (hk : ¬ ∀ s, (e s).isLeft = decide (s.val % 2 = 1)) :
    tcC (B := B) β a b μ lam Fd Gd e ξ = 0 := by
  classical
  obtain ⟨s, hs⟩ : ∃ s, ¬ (e s).isLeft = decide (s.val % 2 = 1) := by
    by_contra hcon
    exact hk (fun s => by by_contra hs; exact hcon ⟨s, hs⟩)
  unfold tcC
  rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl s)) (by simp [tcRho, tcPsi, tcKappa, hs])]
  ring

open Classical in
private lemma tc_sum_pairings {J ℓ : ℕ} (β : ℝ) (a b : ℕ) (R : ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) :
    ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      tcC β a b μ lam Fd Gd e ξ * (tcEg a b R ξ * tcNmatch a b e ξ) =
    ∑ p : TreeMatch (treeK a b) × TreeMatch (treeK a b), ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n,
      ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        (if TcCompat a b p e ξ then tcC β a b μ lam Fd Gd e ξ * tcEg a b R ξ else 0) := by
  classical
  have hswap : ∑ p : TreeMatch (treeK a b) × TreeMatch (treeK a b),
      ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        (if TcCompat a b p e ξ then tcC β a b μ lam Fd Gd e ξ * tcEg a b R ξ else 0) =
      ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        ∑ p : TreeMatch (treeK a b) × TreeMatch (treeK a b),
        (if TcCompat a b p e ξ then tcC β a b μ lam Fd Gd e ξ * tcEg a b R ξ else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_comm]
  rw [hswap]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ξ _ => ?_
  by_cases hk : ∀ s, (e s).isLeft = decide (s.val % 2 = 1)
  · have hN : tcNmatch a b e ξ = (Finset.univ.filter fun p : TreeMatch (treeK a b) × TreeMatch (treeK a b) =>
        TcCompat a b p e ξ).card := by
      unfold tcNmatch
      rw [tc_N_eq a b e ξ hk, Nat.card_eq_fintype_card, Fintype.card_subtype]
      norm_cast
      exact congrArg Finset.card (Finset.filter_congr (fun p _ => Iff.rfl))
    rw [hN, ← Finset.sum_boole, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  · rw [tc_C_zero β a b μ lam Fd Gd e ξ hk]
    simp

-- ===== P12i =====
private lemma tc_class_sum {V X : Type} [Fintype V] [DecidableEq V] [Fintype X] (r : Setoid V)
    [Fintype (Quotient r)] [DecidableEq (Quotient r)]
    (P : (V → X) → Prop) [DecidablePred P] (hP : ∀ ψ, P ψ ↔ ∀ x y, r x y → ψ x = ψ y)
    (ρ : V → X → ℝ) :
    ∑ ψ : V → X, (if P ψ then ∏ v, ρ v (ψ v) else 0) =
      ∏ q : Quotient r, ∑ x : X, ∏ v ∈ Finset.univ.filter (fun v => (Quotient.mk r v) = q), ρ v x := by
  classical
  let Φ : (Quotient r → X) → (V → X) := fun h v => h (Quotient.mk r v)
  have hΦinj : Function.Injective Φ := by
    intro h h' hh
    funext q
    obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    exact congrFun hh v
  have himg : ∀ ψ : V → X, P ψ → ∃ h, Φ h = ψ := by
    intro ψ hψ
    refine ⟨Quotient.lift ψ (fun x y hxy => (hP ψ).mp hψ x y hxy), ?_⟩
    funext v
    rfl
  have hresp : ∀ h : Quotient r → X, P (Φ h) := by
    intro h
    rw [hP]
    intro x y hxy
    exact congrArg h (Quotient.sound hxy)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ψ : V → X => P ψ)]
  have hz : ∑ ψ ∈ Finset.univ.filter (fun ψ : V → X => ¬ P ψ),
      (if P ψ then ∏ v, ρ v (ψ v) else 0) = 0 :=
    Finset.sum_eq_zero fun ψ hψ => by simp only [Finset.mem_filter] at hψ; simp [hψ.2]
  rw [hz, add_zero]
  have hfilt : Finset.univ.filter (fun ψ : V → X => P ψ) = Finset.univ.image Φ := by
    ext ψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hψ
      obtain ⟨h, hh⟩ := himg ψ hψ
      exact ⟨h, hh⟩
    · rintro ⟨h, rfl⟩
      exact hresp h
  rw [Finset.sum_congr rfl (fun ψ hψ => if_pos (Finset.mem_filter.mp hψ).2), hfilt,
    Finset.sum_image (fun h _ h' _ hh => hΦinj hh)]
  have hprod : ∀ h : Quotient r → X, ∏ v, ρ v (Φ h v) =
      ∏ q : Quotient r, ∏ v ∈ Finset.univ.filter (fun v => (Quotient.mk r v) = q), ρ v (h q) := by
    intro h
    rw [← Finset.prod_fiberwise Finset.univ (fun v => Quotient.mk r v) (fun v => ρ v (Φ h v))]
    refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun v hv => ?_
    have := (Finset.mem_filter.mp hv).2
    simp only [Φ, this]
  simp only [hprod]
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]

-- ===== P12j =====
private lemma tc_compat_iff {J ℓ : ℕ} (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b))
    (e : Fin (treeK a b) → Fin m ⊕ Fin n) (ξ : Fin (treeK a b) → TcLam J ℓ B) :
    TcCompat a b p e ξ ↔ ∀ x y, treeSetoid p x y → tcPsi a b e ξ x = tcPsi a b e ξ y := by
  constructor
  · intro hc x y h
    change Relation.EqvGen (treeRel p) x y at h
    induction h with
    | rel x y hxy =>
      unfold treeRel at hxy
      obtain ⟨s, h1 | h1 | h1 | h1⟩ := hxy <;> obtain ⟨h1a, h1b⟩ := h1 <;> subst h1a <;> subst h1b
      · have := congrArg Prod.fst (hc s).1
        simp only [tcLab] at this
        simp [tcPsi, this]
      · have := congrArg Prod.fst (hc s).2
        simp only [tcLab] at this
        simp [tcPsi, this]
      · have := congrArg Prod.snd (hc s).1
        simp only [tcLab] at this
        simp [tcPsi, this]
      · have := congrArg Prod.snd (hc s).2
        simp only [tcLab] at this
        simp [tcPsi, this]
    | refl => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h s
    have hr : ∀ x y, treeRel p x y → treeSetoid p x y := fun x y hxy =>
      (Relation.EqvGen.rel x y hxy : Relation.EqvGen (treeRel p) x y)
    have h1 := h _ _ (hr (Sum.inr s) (Sum.inr (p.1.1 s)) ⟨s, Or.inl ⟨rfl, rfl⟩⟩)
    have h2 := h _ _ (hr (Sum.inl (treeOutV s)) (Sum.inl (treeOutV (p.1.1 s)))
      ⟨s, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)
    have h3 := h _ _ (hr (Sum.inr s) (Sum.inr (p.2.1 s)) ⟨s, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
    have h4 := h _ _ (hr (Sum.inl (treeInV s)) (Sum.inl (treeInV (p.2.1 s)))
      ⟨s, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩)
    simp only [tcPsi, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq] at h1 h2 h3 h4
    refine ⟨?_, ?_⟩
    · simp only [tcLab, h1, h2]
    · simp only [tcLab, h3, h4]

-- ===== P12k =====
private lemma tc_setoid_isLeft {k : ℕ} (p : TreeMatch k × TreeMatch k) {x y : TreeVtx k}
    (h : treeSetoid p x y) : x.isLeft = y.isLeft := by
  change Relation.EqvGen (treeRel p) x y at h
  induction h with
  | rel x y hxy =>
    unfold treeRel at hxy
    obtain ⟨s, h1 | h1 | h1 | h1⟩ := hxy <;> obtain ⟨h1a, h1b⟩ := h1 <;>
      subst h1a <;> subst h1b <;> rfl
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

private def tcPar {k : ℕ} : TreeVtx k → ℕ
  | Sum.inl e => e.val % 2
  | Sum.inr _ => 2

private lemma tc_outV_odd {k : ℕ} (hk : k % 2 = 0) (s : Fin k) : (treeOutV s).val % 2 = 1 := by
  have hs := s.isLt
  unfold treeOutV
  split_ifs with h
  · have h' : s.val % 2 = 0 := h
    rw [tc_prev_val]
    split_ifs with h0 <;> omega
  · have h' : ¬ s.val % 2 = 0 := h
    omega

private lemma tc_inV_even {k : ℕ} (s : Fin k) : (treeInV s).val % 2 = 0 := by
  have hs := s.isLt
  unfold treeInV
  split_ifs with h
  · have h' : s.val % 2 = 0 := h
    exact h'
  · have h' : ¬ s.val % 2 = 0 := h
    rw [tc_prev_val]
    split_ifs with h0 <;> omega

private lemma tc_setoid_par {k : ℕ} (hk : k % 2 = 0) (p : TreeMatch k × TreeMatch k) {x y : TreeVtx k}
    (h : treeSetoid p x y) : tcPar x = tcPar y := by
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
      simp only [tcPar]
      rw [tc_outV_odd hk s, tc_outV_odd hk (p.1.1 s)]
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a; subst h1b
      simp only [tcPar]
      rw [tc_inV_even s, tc_inV_even (p.2.1 s)]
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

private lemma tc_gmark_pure (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) :
    ¬ ∃ e : Fin (treeK a b),
      treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeGMark a b)) ∧ e.val % 2 = 1 := by
  rintro ⟨e, heq, hodd⟩
  unfold treeMk at heq
  have h2 := tc_setoid_par (tc_k_even a b) p (Quotient.exact heq)
  simp only [tcPar, treeGMark, Fin.val_mk] at h2
  omega

private lemma tc_card_le (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) :
    Nat.card (Quotient (treeSetoid p)) ≤ treeK a b + 1 := by
  classical
  have hconn := def_app_vol_tree_connected a b p
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  set Z : Finset (Fin (treeK a b)) := Finset.univ.filter fun s => s.val < (p.1.1 s).val with hZ
  set W : Finset (Fin (treeK a b)) := Finset.univ.filter fun s => s.val < (p.2.1 s).val with hW
  have hcard : Z.card + W.card = treeK a b := def_app_vol_tree_edges a b p
  set fz : Fin (treeK a b) → Sym2 (Quotient (treeSetoid p)) := fun s =>
    s(treeMk p (Sum.inr s), treeMk p (Sum.inl (treeOutV s))) with hfz
  set fw : Fin (treeK a b) → Sym2 (Quotient (treeSetoid p)) := fun s =>
    s(treeMk p (Sum.inr s), treeMk p (Sum.inl (treeInV s))) with hfw
  set Es : Finset (Sym2 (Quotient (treeSetoid p))) := Z.image fz ∪ W.image fw with hEs
  have hsub : (SimpleGraph.fromRel fun x y : Quotient (treeSetoid p) =>
      ∃ s : Fin (treeK a b),
        (x = treeMk p (Sum.inr s) ∧ y = treeMk p (Sum.inl (treeOutV s))) ∨
        (x = treeMk p (Sum.inr s) ∧ y = treeMk p (Sum.inl (treeInV s)))).edgeSet ⊆ (Es : Set _) := by
    intro z hz
    induction z using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at hz
      obtain ⟨-, hr⟩ := hz
      have key : ∀ x y : Quotient (treeSetoid p), (∃ s : Fin (treeK a b),
          (x = treeMk p (Sum.inr s) ∧ y = treeMk p (Sum.inl (treeOutV s))) ∨
          (x = treeMk p (Sum.inr s) ∧ y = treeMk p (Sum.inl (treeInV s)))) →
          s(x, y) ∈ Es := by
        rintro x y ⟨s, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · by_cases hs : s.val < (p.1.1 s).val
          · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, by rw [hZ]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, rfl⟩)
          · have hne : p.1.1 s ≠ s := p.1.2.2 s
            have hlt : (p.1.1 s).val < s.val := by
              have : (p.1.1 s).val ≠ s.val := fun h => hne (Fin.ext h)
              omega
            refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p.1.1 s, ?_, ?_⟩)
            · simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [p.1.2.1 s]; exact hlt
            · simp only [hfz]
              have e1 : treeMk p (Sum.inr (p.1.1 s)) = treeMk p (Sum.inr s) := by
                apply Quotient.sound
                exact (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨s, Or.inl ⟨rfl, rfl⟩⟩))
              have e2 : treeMk p (Sum.inl (treeOutV (p.1.1 s))) = treeMk p (Sum.inl (treeOutV s)) := by
                apply Quotient.sound
                exact (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
                  ⟨s, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩))
              rw [e1, e2]
        · by_cases hs : s.val < (p.2.1 s).val
          · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, by rw [hW]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, rfl⟩)
          · have hne : p.2.1 s ≠ s := p.2.2.2 s
            have hlt : (p.2.1 s).val < s.val := by
              have : (p.2.1 s).val ≠ s.val := fun h => hne (Fin.ext h)
              omega
            refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p.2.1 s, ?_, ?_⟩)
            · simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [p.2.2.1 s]; exact hlt
            · simp only [hfw]
              have e1 : treeMk p (Sum.inr (p.2.1 s)) = treeMk p (Sum.inr s) := by
                apply Quotient.sound
                exact (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
                  ⟨s, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩))
              have e2 : treeMk p (Sum.inl (treeInV (p.2.1 s))) = treeMk p (Sum.inl (treeInV s)) := by
                apply Quotient.sound
                exact (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
                  ⟨s, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩))
              rw [e1, e2]
      rcases hr with hr | hr
      · exact key x y hr
      · rw [Sym2.eq_swap]; exact key y x hr
  have h2 : Nat.card (SimpleGraph.fromRel fun x y : Quotient (treeSetoid p) =>
      ∃ s : Fin (treeK a b),
        (x = treeMk p (Sum.inr s) ∧ y = treeMk p (Sum.inl (treeOutV s))) ∨
        (x = treeMk p (Sum.inr s) ∧ y = treeMk p (Sum.inl (treeInV s)))).edgeSet ≤ Es.card := by
    calc _ ≤ Nat.card (Es : Set _) := Nat.card_mono (Set.toFinite _) hsub
      _ = Es.card := by simp
  have h3 : Es.card ≤ Z.card + W.card :=
    (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le Finset.card_image_le)
  omega

-- ===== P12l =====
private lemma tc_psi_inj {J ℓ : ℕ} (a b : ℕ) :
    Function.Injective (fun q : (Fin (treeK a b) → Fin m ⊕ Fin n) × (Fin (treeK a b) → TcLam J ℓ B) =>
      tcPsi (B := B) a b q.1 q.2) := by
  intro q q' h
  have h1 : ∀ s, q.1 s = q'.1 s := fun s => by
    have := congrFun h (Sum.inl s)
    simpa [tcPsi] using this
  have h2 : ∀ s, q.2 s = q'.2 s := fun s => by
    have := congrFun h (Sum.inr s)
    simpa [tcPsi] using this
  exact Prod.ext (funext h1) (funext h2)

private lemma tc_rho_zero_of_not_range {J ℓ : ℕ} (β : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (ψ : TreeVtx (treeK a b) → (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B)
    (hψ : ¬ ∃ (e : Fin (treeK a b) → Fin m ⊕ Fin n) (ξ : Fin (treeK a b) → TcLam J ℓ B),
      tcPsi a b e ξ = ψ) :
    ∃ v, tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v (ψ v) = 0 := by
  by_contra hcon
  push Not at hcon
  apply hψ
  have hl : ∀ s, ∃ ε, ψ (Sum.inl s) = Sum.inl ε := by
    intro s
    rcases h : ψ (Sum.inl s) with ε | σ
    · exact ⟨ε, rfl⟩
    · exfalso; have := hcon (Sum.inl s); rw [h] at this; simp [tcRho] at this
  have hr : ∀ s, ∃ σ, ψ (Sum.inr s) = Sum.inr σ := by
    intro s
    rcases h : ψ (Sum.inr s) with ε | σ
    · exfalso; have := hcon (Sum.inr s); rw [h] at this; simp [tcRho] at this
    · exact ⟨σ, rfl⟩
  choose e he using hl
  choose ξ hξ using hr
  refine ⟨e, ξ, ?_⟩
  funext v
  rcases v with s | s
  · simp [tcPsi, he s]
  · simp [tcPsi, hξ s]

open Classical in
private lemma tc_sum_psi {J ℓ : ℕ} (β : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (G : (TreeVtx (treeK a b) → (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) → ℝ)
    (hG : ∀ ψ, (∃ v, tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v (ψ v) = 0) → G ψ = 0) :
    ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      G (tcPsi a b e ξ) = ∑ ψ, G ψ := by
  rw [← Fintype.sum_prod_type']
  rw [← Finset.sum_image (f := G) (s := Finset.univ)
    (g := fun q : (Fin (treeK a b) → Fin m ⊕ Fin n) × (Fin (treeK a b) → TcLam J ℓ B) =>
      tcPsi (B := B) a b q.1 q.2) (fun x _ y _ h => tc_psi_inj a b h)]
  refine Finset.sum_subset (Finset.subset_univ _) fun ψ _ hψ => ?_
  apply hG
  apply tc_rho_zero_of_not_range β a b μ lam Fd Gd ψ
  rintro ⟨e, ξ, h⟩
  exact hψ (Finset.mem_image.mpr ⟨(e, ξ), Finset.mem_univ _, h⟩)

-- ===== P12m =====
open Classical in
private lemma tc_weighted_sum {J ℓ : ℕ} (β : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (c0 : ℝ)
    (ρ' : TreeVtx (treeK a b) → (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B → ℝ)
    (hρ' : ∀ v x, tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x = 0 → ρ' v x = 0)
    (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) :
    ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      (if TcCompat a b p e ξ then c0 * ∏ v, ρ' v (tcPsi a b e ξ v) else 0) =
    c0 * ∏ q : Quotient (treeSetoid p), ∑ x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B,
      ∏ v ∈ Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q), ρ' v x := by
  set P : (TreeVtx (treeK a b) → (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) → Prop :=
    fun ψ => ∀ x y, treeSetoid p x y → ψ x = ψ y with hPdef
  have hcs := tc_class_sum (treeSetoid p) P (fun ψ => Iff.rfl) ρ'
  have hsum : ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      c0 * (if P (tcPsi a b e ξ) then ∏ v, ρ' v (tcPsi a b e ξ v) else 0) =
      ∑ ψ : TreeVtx (treeK a b) → (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B,
        c0 * (if P ψ then ∏ v, ρ' v (ψ v) else 0) :=
    tc_sum_psi (B := B) β a b μ lam Fd Gd (fun ψ => c0 * (if P ψ then ∏ v, ρ' v (ψ v) else 0)) (by
      intro ψ ⟨v, hv⟩
      split_ifs
      · rw [Finset.prod_eq_zero (Finset.mem_univ v) (hρ' v _ hv), mul_zero]
      · rw [mul_zero])
  calc _ = ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      c0 * (if P (tcPsi a b e ξ) then ∏ v, ρ' v (tcPsi a b e ξ v) else 0) := by
        refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ξ _ => ?_
        by_cases h : TcCompat a b p e ξ
        · rw [if_pos h, if_pos ((tc_compat_iff a b p e ξ).mp h)]
        · rw [if_neg h, if_neg (fun h' => h ((tc_compat_iff a b p e ξ).mpr h')), mul_zero]
    _ = _ := by rw [hsum, ← Finset.mul_sum, hcs]

open Classical in
private lemma tc_free_sum {J ℓ : ℕ} (β : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) :
    ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      (if TcCompat a b p e ξ then tcC β a b μ lam Fd Gd e ξ else 0) =
    ((B : ℝ)⁻¹) ^ (treeK a b + 1) * ∏ q : Quotient (treeSetoid p), ∑ x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B,
      ∏ v ∈ Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q),
        tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x := by
  have := tc_weighted_sum (B := B) β a b μ lam Fd Gd (((B : ℝ)⁻¹) ^ (treeK a b + 1))
    (fun v x => tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x) (fun v x h => h) p
  rw [← this]
  rfl

-- ===== P12n =====
private lemma tc_varpi_abs_le {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ l : ℕ) (α : ℤ) :
    |treeVarpi β ℓ l α| ≤ 1 := by
  have h1 : ∀ j : ℕ, 0 ≤ Muon.emaW β j ∧ Muon.emaW β j ≤ 1 := by
    intro j
    unfold Muon.emaW
    have hp : 0 ≤ β ^ j := pow_nonneg hβ.1 j
    have hp1 : β ^ j ≤ 1 := pow_le_one₀ hβ.1 hβ.2.le
    refine ⟨mul_nonneg (by linarith [hβ.2]) hp, ?_⟩
    nlinarith [hβ.1]
  have hb : 0 ≤ β ^ ℓ ∧ β ^ ℓ ≤ 1 := ⟨pow_nonneg hβ.1 ℓ, pow_le_one₀ hβ.1 hβ.2.le⟩
  unfold treeVarpi
  split_ifs
  · rw [abs_of_nonneg (h1 _).1]; exact (h1 _).2
  · rw [abs_of_nonneg (mul_nonneg hb.1 (h1 _).1)]
    exact mul_le_one₀ hb.2 (h1 _).1 (h1 _).2
  · simp
  · rw [abs_of_nonneg (h1 _).1]; exact (h1 _).2

private lemma tc_rho_abs_le {J ℓ : ℕ} {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (a b : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ C) (hlam : ∀ j, 0 ≤ lam j ∧ lam j ≤ C)
    (hF : ∀ i, |Fd i| ≤ 1) (hG : ∀ j, |Gd j| ≤ 1)
    (v : TreeVtx (treeK a b)) (x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) :
    |tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x| ≤ C := by
  have hC0 : 0 ≤ C := by linarith
  rcases v with s | s <;> rcases x with ε | σ
  · simp only [tcRho, abs_mul]
    have h1 : |tcNuE μ lam ε| ≤ C := by
      rcases ε with i | j
      · rw [tcNuE, Sum.elim_inl, abs_of_nonneg (hμ i).1]; exact (hμ i).2
      · rw [tcNuE, Sum.elim_inr, abs_of_nonneg (hlam j).1]; exact (hlam j).2
    have h2 : |tcKappa s ε| ≤ 1 := by unfold tcKappa; split_ifs <;> simp
    have h3 : |(if s = treeFMark a b then tcFh Fd ε else 1)| ≤ 1 := by
      split_ifs
      · rcases ε with i | j
        · exact hF i
        · simp [tcFh]
      · simp
    have h4 : |(if s = treeGMark a b then tcGh Gd ε else 1)| ≤ 1 := by
      split_ifs
      · rcases ε with i | j
        · simp [tcGh]
        · exact hG j
      · simp
    calc |tcNuE μ lam ε| * |tcKappa s ε| * |(if s = treeFMark a b then tcFh Fd ε else 1)| *
          |(if s = treeGMark a b then tcGh Gd ε else 1)| ≤ C * 1 * 1 * 1 := by
          gcongr
      _ = C := by ring
  · simp [tcRho, hC0]
  · simp [tcRho, hC0]
  · simp only [tcRho]
    exact (tc_varpi_abs_le hβ ℓ _ _).trans hC

private lemma tc_prod_abs_le {ι : Type} (s : Finset ι) (f : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i, |f i| ≤ C) : ∏ i ∈ s, |f i| ≤ C ^ s.card := by
  calc ∏ i ∈ s, |f i| ≤ ∏ _i ∈ s, C := Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => h i)
    _ = C ^ s.card := by simp

private lemma tc_fiber_card_sum {V : Type} [Fintype V] (r : Setoid V) [DecidableEq (Quotient r)]
    [Fintype (Quotient r)] :
    ∑ q : Quotient r, (Finset.univ.filter (fun v : V => Quotient.mk r v = q)).card =
      Fintype.card V := by
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise (f := fun v : V => Quotient.mk r v)
    (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm

open Classical in
private lemma tc_abs_total {J ℓ : ℕ} {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (a b : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ C) (hlam : ∀ j, 0 ≤ lam j ∧ lam j ≤ C)
    (hF : ∀ i, |Fd i| ≤ 1) (hG : ∀ j, |Gd j| ≤ 1)
    (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) :
    ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      (if TcCompat a b p e ξ then |tcC β a b μ lam Fd Gd e ξ| else 0) ≤
    |(B : ℝ)⁻¹| ^ (treeK a b + 1) *
      ((Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) ^ (Nat.card (Quotient (treeSetoid p))) *
        C ^ (2 * treeK a b)) := by
  have hC0 : 0 ≤ C := by linarith
  have := tc_weighted_sum (B := B) β a b μ lam Fd Gd (|(B : ℝ)⁻¹| ^ (treeK a b + 1))
    (fun v x => |tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x|) (fun v x h => by simp [h]) p
  have hL : ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      (if TcCompat a b p e ξ then |tcC β a b μ lam Fd Gd e ξ| else 0) =
      ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      (if TcCompat a b p e ξ then |(B : ℝ)⁻¹| ^ (treeK a b + 1) *
        ∏ v, |tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v (tcPsi a b e ξ v)| else 0) := by
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ξ _ => ?_
    unfold tcC
    rw [abs_mul, abs_pow, Finset.abs_prod]
  rw [hL, this]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hq : ∀ q : Quotient (treeSetoid p), ∑ x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B,
      ∏ v ∈ Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q),
        |tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x| ≤
      (Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) *
        C ^ (Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q)).card := by
    intro q
    calc _ ≤ ∑ _x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B,
          C ^ (Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q)).card :=
          Finset.sum_le_sum fun x _ => tc_prod_abs_le _ _ C hC0 fun v =>
            tc_rho_abs_le hβ a b μ lam Fd Gd C hC hμ hlam hF hG v x
      _ = _ := by simp
  calc _ ≤ ∏ q : Quotient (treeSetoid p), ((Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) *
        C ^ (Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q)).card) :=
        Finset.prod_le_prod₀ (fun q _ => Finset.sum_nonneg fun x _ =>
          Finset.prod_nonneg fun v _ => abs_nonneg _) (fun q _ => hq q)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow_eq_pow_sum,
        tc_fiber_card_sum]
      have : Fintype.card (TreeVtx (treeK a b)) = 2 * treeK a b := by
        simp [TreeVtx, Fintype.card_sum]; ring
      rw [this, Nat.card_eq_fintype_card (α := Quotient (treeSetoid p))]

-- ===== P12o =====
private lemma tc_gt_abs_le {R : ℝ} (hR : 0 < R) (u : ℝ) : |tcGt R u| ≤ R := by
  unfold tcGt
  split_ifs with h
  · exact h
  · simpa using hR.le

private lemma tc_trunc_eq (d : ℕ) (R : ℝ) :
    treeTruncMoment d R = ∫ u, tcGt R u ^ d ∂(gaussianReal 0 1) := by
  unfold treeTruncMoment
  by_cases hd : d = 0
  · subst hd; simp
  · rw [if_neg hd]
    congr 1
    funext u
    unfold tcGt
    split_ifs with h
    · rfl
    · simp [zero_pow hd]

private lemma tc_trunc_abs_le {R : ℝ} (hR : 0 < R) (d : ℕ) :
    |∫ u, tcGt R u ^ d ∂(gaussianReal 0 1)| ≤ R ^ d := by
  have h := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1) (f := fun u => tcGt R u ^ d)
    (C := R ^ d) (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (tc_gt_abs_le hR u) d)
  simpa [Real.norm_eq_abs] using h

private lemma tc_Eg_abs_le {J ℓ : ℕ} {R : ℝ} (hR : 0 < R) (a b : ℕ) (ξ : Fin (treeK a b) → TcLam J ℓ B) :
    |tcEg a b R ξ| ≤ R ^ (treeK a b) := by
  classical
  unfold tcEg
  rw [Finset.abs_prod]
  calc ∏ σ : TcLam J ℓ B, |∫ u, tcGt R u ^ (Finset.univ.filter fun s : Fin (treeK a b) => ξ s = σ).card
          ∂(gaussianReal 0 1)| ≤ ∏ σ : TcLam J ℓ B,
        R ^ (Finset.univ.filter fun s : Fin (treeK a b) => ξ s = σ).card :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun σ _ => tc_trunc_abs_le hR _)
    _ = R ^ (treeK a b) := by
        rw [Finset.prod_pow_eq_pow_sum]
        congr 1
        have := Finset.card_eq_sum_card_fiberwise (f := ξ) (s := (Finset.univ : Finset (Fin (treeK a b))))
          (t := (Finset.univ : Finset (TcLam J ℓ B))) (fun _ _ => Finset.mem_univ _)
        rw [← this]
        simp

-- ===== P12p =====
open Classical in
private lemma tc_fiber_prod {k : ℕ} (p : TreeMatch k × TreeMatch k) (f : TreeVtx k → ℝ)
    (q : Quotient (treeSetoid p)) :
    ∏ v ∈ Finset.univ.filter (fun v : TreeVtx k => Quotient.mk (treeSetoid p) v = q), f v =
      (∏ e ∈ Finset.univ.filter (fun e : Fin k => treeMk p (Sum.inl e) = q), f (Sum.inl e)) *
      ∏ r ∈ Finset.univ.filter (fun r : Fin k => treeMk p (Sum.inr r) = q), f (Sum.inr r) := by
  rw [Finset.prod_filter, Finset.prod_filter, Finset.prod_filter, Fintype.prod_sum_type]
  rfl

open Classical in
private lemma tc_ext_no_latent {k : ℕ} (p : TreeMatch k × TreeMatch k) (q : Quotient (treeSetoid p))
    (h : ∃ e : Fin k, treeMk p (Sum.inl e) = q) :
    Finset.univ.filter (fun r : Fin k => treeMk p (Sum.inr r) = q) = ∅ := by
  obtain ⟨e, he⟩ := h
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  intro hr
  have := tc_setoid_isLeft p (Quotient.exact (hr.trans he.symm))
  simp at this

open Classical in
private lemma tc_lat_no_ext {k : ℕ} (p : TreeMatch k × TreeMatch k) (q : Quotient (treeSetoid p))
    (h : ¬ ∃ e : Fin k, treeMk p (Sum.inl e) = q) :
    Finset.univ.filter (fun e : Fin k => treeMk p (Sum.inl e) = q) = ∅ := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  exact fun he => h ⟨e, he⟩

open Classical in
private lemma tc_cls_out {J ℓ : ℕ} (β : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b))
    (q : Quotient (treeSetoid p))
    (hq : ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q ∧ e.val % 2 = 1) :
    ∑ x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B,
      ∏ v ∈ Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q),
        tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x =
    ∑ i : Fin m, μ i ^ (Finset.univ.filter fun e : Fin (treeK a b) => treeMk p (Sum.inl e) = q).card *
      Fd i ^ (if treeMk p (Sum.inl (treeFMark a b)) = q then 1 else 0) := by
  obtain ⟨e0, he0, ho0⟩ := hq
  have hex : ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q := ⟨e0, he0⟩
  set Ee := Finset.univ.filter (fun e : Fin (treeK a b) => treeMk p (Sum.inl e) = q) with hEe
  have hodd : ∀ e ∈ Ee, e.val % 2 = 1 := by
    intro e he
    have he' : treeMk p (Sum.inl e) = q := (Finset.mem_filter.mp he).2
    have := tc_setoid_par (tc_k_even a b) p (Quotient.exact (he'.trans he0.symm))
    simp only [tcPar] at this
    omega
  have hG : ∀ e ∈ Ee, e ≠ treeGMark a b := by
    intro e he hGe
    subst hGe
    exact tc_gmark_pure a b p ⟨e0, he0.trans (Finset.mem_filter.mp he).2.symm, ho0⟩
  have hfib : ∀ x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B,
      ∏ v ∈ Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q),
        tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x =
      ∏ e ∈ Ee, tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd (Sum.inl e) x := by
    intro x
    rw [tc_fiber_prod p (fun v => tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x) q,
      tc_ext_no_latent p q hex, Finset.prod_empty, mul_one]
  simp only [hfib]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h2 : ∀ σ : TcLam J ℓ B, ∏ e ∈ Ee, tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd (Sum.inl e)
      (Sum.inr σ) = 0 :=
    fun σ => Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ e0, he0⟩) (by simp [tcRho])
  have h3 : ∀ j : Fin n, ∏ e ∈ Ee, tcRho (B := B) (J := J) (ℓ := ℓ) β a b μ lam Fd Gd (Sum.inl e)
      (Sum.inl (Sum.inr j)) = 0 := by
    intro j
    refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ e0, he0⟩) ?_
    simp [tcRho, tcKappa, ho0]
  simp only [h2, h3, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h4 : ∀ e ∈ Ee, tcRho (B := B) (J := J) (ℓ := ℓ) β a b μ lam Fd Gd (Sum.inl e) (Sum.inl (Sum.inl i)) =
      μ i * (if e = treeFMark a b then Fd i else 1) := by
    intro e he
    have := hodd e he
    simp [tcRho, tcKappa, tcNuE, tcFh, tcGh, this, hG e he]
  rw [Finset.prod_congr rfl h4, Finset.prod_mul_distrib, Finset.prod_const]
  congr 1
  rw [Finset.prod_ite_eq' Ee (treeFMark a b) (fun _ => Fd i)]
  by_cases hF : treeMk p (Sum.inl (treeFMark a b)) = q
  · have : treeFMark a b ∈ Ee := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF⟩
    simp [this, hF]
  · have : treeFMark a b ∉ Ee := fun h => hF (Finset.mem_filter.mp h).2
    simp [this, hF]

open Classical in
private lemma tc_cls_in {J ℓ : ℕ} (β : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b))
    (q : Quotient (treeSetoid p))
    (hex : ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q)
    (hq : ¬ ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q ∧ e.val % 2 = 1) :
    ∑ x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B,
      ∏ v ∈ Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q),
        tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x =
    ∑ j : Fin n, lam j ^ (Finset.univ.filter fun e : Fin (treeK a b) => treeMk p (Sum.inl e) = q).card *
      Gd j ^ (if treeMk p (Sum.inl (treeGMark a b)) = q then 1 else 0) := by
  obtain ⟨e0, he0⟩ := hex
  have hex : ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q := ⟨e0, he0⟩
  set Ee := Finset.univ.filter (fun e : Fin (treeK a b) => treeMk p (Sum.inl e) = q) with hEe
  have heven : ∀ e ∈ Ee, ¬ e.val % 2 = 1 := by
    intro e he ho
    exact hq ⟨e, (Finset.mem_filter.mp he).2, ho⟩
  have hFm : ∀ e ∈ Ee, e ≠ treeFMark a b := by
    intro e he hFe
    subst hFe
    exact heven _ he (by show (2 * a + 2 * b + 1) % 2 = 1; omega)
  have hfib : ∀ x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B,
      ∏ v ∈ Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q),
        tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x =
      ∏ e ∈ Ee, tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd (Sum.inl e) x := by
    intro x
    rw [tc_fiber_prod p (fun v => tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x) q,
      tc_ext_no_latent p q hex, Finset.prod_empty, mul_one]
  simp only [hfib]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h2 : ∀ σ : TcLam J ℓ B, ∏ e ∈ Ee, tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd (Sum.inl e)
      (Sum.inr σ) = 0 :=
    fun σ => Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ e0, he0⟩) (by simp [tcRho])
  have h3 : ∀ i : Fin m, ∏ e ∈ Ee, tcRho (B := B) (J := J) (ℓ := ℓ) β a b μ lam Fd Gd (Sum.inl e)
      (Sum.inl (Sum.inl i)) = 0 := by
    intro i
    refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ e0, he0⟩) ?_
    have := heven e0 (Finset.mem_filter.mpr ⟨Finset.mem_univ e0, he0⟩)
    simp [tcRho, tcKappa, this]
  simp only [h2, h3, Finset.sum_const_zero, zero_add, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h4 : ∀ e ∈ Ee, tcRho (B := B) (J := J) (ℓ := ℓ) β a b μ lam Fd Gd (Sum.inl e) (Sum.inl (Sum.inr j)) =
      lam j * (if e = treeGMark a b then Gd j else 1) := by
    intro e he
    have := heven e he
    simp [tcRho, tcKappa, tcNuE, tcFh, tcGh, this, hFm e he]
  rw [Finset.prod_congr rfl h4, Finset.prod_mul_distrib, Finset.prod_const]
  congr 1
  rw [Finset.prod_ite_eq' Ee (treeGMark a b) (fun _ => Gd j)]
  by_cases hF : treeMk p (Sum.inl (treeGMark a b)) = q
  · have : treeGMark a b ∈ Ee := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF⟩
    simp [this, hF]
  · have : treeGMark a b ∉ Ee := fun h => hF (Finset.mem_filter.mp h).2
    simp [this, hF]

open Classical in
private lemma tc_cls_lat {J ℓ : ℕ} (β : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b))
    (q : Quotient (treeSetoid p))
    (hq : ¬ ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q)
    (hne : ∃ r : Fin (treeK a b), treeMk p (Sum.inr r) = q) :
    ∑ x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B,
      ∏ v ∈ Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q),
        tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x =
    (B : ℝ) * ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
      ∏ r ∈ Finset.univ.filter (fun r : Fin (treeK a b) => treeMk p (Sum.inr r) = q),
        treeVarpi β ℓ (treeLabel a r) α := by
  obtain ⟨r0, hr0⟩ := hne
  set Sq := Finset.univ.filter (fun r : Fin (treeK a b) => treeMk p (Sum.inr r) = q) with hSq
  have hfib : ∀ x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B,
      ∏ v ∈ Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q),
        tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x =
      ∏ r ∈ Sq, tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd (Sum.inr r) x := by
    intro x
    rw [tc_fiber_prod p (fun v => tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x) q,
      tc_lat_no_ext p q hq, Finset.prod_empty, one_mul]
  simp only [hfib]
  rw [Fintype.sum_sum_type]
  have h1 : ∀ ε : Fin m ⊕ Fin n, ∏ r ∈ Sq, tcRho (B := B) (J := J) (ℓ := ℓ) β a b μ lam Fd Gd (Sum.inr r)
      (Sum.inl ε) = 0 :=
    fun ε => Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ r0, hr0⟩) (by simp [tcRho])
  simp only [h1, Finset.sum_const_zero, zero_add]
  simp only [tcRho]
  rw [Fintype.sum_prod_type]
  have : ∀ α : {α : ℤ // α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ)},
      ∑ _c : Fin B, ∏ r ∈ Sq, treeVarpi β ℓ (treeLabel a r) α.1 =
      (B : ℝ) * ∏ r ∈ Sq, treeVarpi β ℓ (treeLabel a r) α.1 := by
    intro α; simp
  simp only [this]
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_coe_sort (Finset.Icc (-(J : ℤ)) (ℓ : ℤ))
    (fun α => ∏ r ∈ Sq, treeVarpi β ℓ (treeLabel a r) α)

-- ===== P12q =====
open Classical in
/-- The product of truncated moments over latent classes. -/
private def tcM (a b : ℕ) (R : ℝ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) : ℝ :=
  ∏ q ∈ Finset.univ.filter (fun q : Quotient (treeSetoid p) =>
      ¬ ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q),
    treeTruncMoment (Finset.univ.filter fun r : Fin (treeK a b) => treeMk p (Sum.inr r) = q).card R

open Classical in
private lemma tc_class_factor_eq (β : ℝ) (ℓ J : ℕ) (R : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (hB : (B : ℝ) ≠ 0)
    (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) (q : Quotient (treeSetoid p)) :
    treeClassFactor β ℓ J R B μ lam Fd Gd a b p q =
      (B : ℝ)⁻¹ * (∑ x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B,
        ∏ v ∈ Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q),
          tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x) *
      (if ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q then 1 else
        treeTruncMoment (Finset.univ.filter fun r : Fin (treeK a b) => treeMk p (Sum.inr r) = q).card R) := by
  unfold treeClassFactor
  by_cases hex : ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q
  · rw [if_pos hex, if_pos hex, mul_one]
    by_cases hod : ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q ∧ e.val % 2 = 1
    · rw [if_pos hod, tc_cls_out β a b μ lam Fd Gd p q hod]
    · rw [if_neg hod, tc_cls_in β a b μ lam Fd Gd p q hex hod]
  · rw [if_neg hex, if_neg hex]
    have hne : ∃ r : Fin (treeK a b), treeMk p (Sum.inr r) = q := by
      obtain ⟨v, rfl⟩ := Quotient.exists_rep q
      rcases v with e | r
      · exact absurd ⟨e, rfl⟩ hex
      · exact ⟨r, rfl⟩
    rw [tc_cls_lat β a b μ lam Fd Gd p q hex hne]
    field_simp

open Classical in
private lemma tc_retained_eq (β : ℝ) (ℓ J : ℕ) (R : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (hB : (B : ℝ) ≠ 0)
    (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) (hret : treeRetained p) :
    ∏ V : Quotient (treeSetoid p), treeClassFactor β ℓ J R B μ lam Fd Gd a b p V =
      tcM a b R p * ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        (if TcCompat a b p e ξ then tcC β a b μ lam Fd Gd e ξ else 0) := by
  rw [tc_free_sum]
  simp only [tc_class_factor_eq β ℓ J R a b μ lam Fd Gd hB p]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hcard : Fintype.card (Quotient (treeSetoid p)) = treeK a b + 1 := by
    rw [← Nat.card_eq_fintype_card]; exact hret
  rw [hcard]
  unfold tcM
  rw [Finset.prod_filter]
  have : ∀ q : Quotient (treeSetoid p),
      (if ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q then (1 : ℝ) else
        treeTruncMoment (Finset.univ.filter fun r : Fin (treeK a b) => treeMk p (Sum.inr r) = q).card R) =
      (if ¬ ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q then
        treeTruncMoment (Finset.univ.filter fun r : Fin (treeK a b) => treeMk p (Sum.inr r) = q).card R
        else 1) := by
    intro q
    by_cases h : ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q <;> simp [h]
  simp only [this]
  ring

-- ===== P12r =====
open Classical in
private lemma tc_Eg_eq_M {J ℓ : ℕ} (R : ℝ) (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b))
    (ξ : Fin (treeK a b) → TcLam J ℓ B)
    (hconst : ∀ r r', treeMk p (Sum.inr r) = treeMk p (Sum.inr r') → ξ r = ξ r')
    (hinj : ∀ r r', ξ r = ξ r' → treeMk p (Sum.inr r) = treeMk p (Sum.inr r')) :
    tcEg a b R ξ = tcM a b R p := by
  unfold tcEg tcM
  simp only [← tc_trunc_eq]
  set F : ℕ → ℝ := fun d => treeTruncMoment d R with hF
  have hF0 : F 0 = 1 := by simp [hF, treeTruncMoment]
  set I : Finset (TcLam J ℓ B) := Finset.univ.image ξ with hI
  rw [← Finset.prod_subset (Finset.subset_univ I) (f := fun σ : TcLam J ℓ B =>
    F (Finset.univ.filter fun s : Fin (treeK a b) => ξ s = σ).card)]
  · have hlat : ∀ q ∈ Finset.univ.filter (fun q : Quotient (treeSetoid p) =>
        ¬ ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q), ∃ r : Fin (treeK a b),
        treeMk p (Sum.inr r) = q := by
      intro q hq
      have hq' := (Finset.mem_filter.mp hq).2
      obtain ⟨v, rfl⟩ := Quotient.exists_rep q
      rcases v with e | r
      · exact absurd ⟨e, rfl⟩ hq'
      · exact ⟨r, rfl⟩
    symm
    refine Finset.prod_bij (fun q hq => ξ (Classical.choose (hlat q hq))) ?_ ?_ ?_ ?_
    · intro q hq
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · intro q hq q' hq' h
      have h1 := Classical.choose_spec (hlat q hq)
      have h2 := Classical.choose_spec (hlat q' hq')
      rw [← h1, ← h2]
      exact hinj _ _ h
    · intro σ hσ
      obtain ⟨r0, -, rfl⟩ := Finset.mem_image.mp hσ
      have hq : treeMk p (Sum.inr r0) ∈ Finset.univ.filter (fun q : Quotient (treeSetoid p) =>
          ¬ ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rintro ⟨e, he⟩
        have := tc_setoid_isLeft p (Quotient.exact he)
        simp at this
      refine ⟨treeMk p (Sum.inr r0), hq, ?_⟩
      have h1 := Classical.choose_spec (hlat _ hq)
      exact hconst _ _ h1
    · intro q hq
      have h1 := Classical.choose_spec (hlat q hq)
      congr 2
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hs
        exact hconst _ _ (hs.trans h1.symm)
      · intro hs
        exact (hinj _ _ hs).trans h1
  · intro σ _ hσ
    have : (Finset.univ.filter fun s : Fin (treeK a b) => ξ s = σ) = ∅ := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hs
      exact hσ (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hs⟩)
    rw [this, Finset.card_empty, hF0]

open Classical in
private lemma tc_M_abs_le {R : ℝ} (hR : 0 < R) (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) :
    |tcM a b R p| ≤ R ^ (treeK a b) := by
  unfold tcM
  rw [Finset.abs_prod]
  calc _ ≤ ∏ q ∈ Finset.univ.filter (fun q : Quotient (treeSetoid p) =>
        ¬ ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q),
        R ^ (Finset.univ.filter fun r : Fin (treeK a b) => treeMk p (Sum.inr r) = q).card :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun q _ => by
          rw [tc_trunc_eq]; exact tc_trunc_abs_le hR _)
    _ = R ^ (treeK a b) := by
        rw [Finset.prod_pow_eq_pow_sum]
        congr 1
        have h1 := Finset.card_eq_sum_card_fiberwise (f := fun r : Fin (treeK a b) =>
          (Quotient.mk (treeSetoid p) (Sum.inr r) : Quotient (treeSetoid p)))
          (s := (Finset.univ : Finset (Fin (treeK a b))))
          (t := (Finset.univ : Finset (Quotient (treeSetoid p)))) (fun _ _ => Finset.mem_univ _)
        rw [Finset.card_univ, Fintype.card_fin] at h1
        refine Eq.trans ?_ h1.symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun q _ hq => ?_
        have : ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = q := by
          by_contra h; exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        have h2 := tc_ext_no_latent p q this
        exact (congrArg Finset.card h2).trans Finset.card_empty

-- ===== P12s =====
open Classical in
private lemma tc_Sp_abs_le {J ℓ : ℕ} {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) {R : ℝ} (hR : 0 < R) (a b : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ C) (hlam : ∀ j, 0 ≤ lam j ∧ lam j ≤ C)
    (hF : ∀ i, |Fd i| ≤ 1) (hG : ∀ j, |Gd j| ≤ 1)
    (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) :
    |∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      (if TcCompat a b p e ξ then tcC β a b μ lam Fd Gd e ξ * tcEg a b R ξ else 0)| ≤
    R ^ (treeK a b) * (|(B : ℝ)⁻¹| ^ (treeK a b + 1) *
      ((Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) ^ (Nat.card (Quotient (treeSetoid p))) *
        C ^ (2 * treeK a b))) := by
  have habs := tc_abs_total (B := B) (J := J) (ℓ := ℓ) hβ a b μ lam Fd Gd C hC hμ hlam hF hG p
  calc _ ≤ ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        |(if TcCompat a b p e ξ then tcC β a b μ lam Fd Gd e ξ * tcEg a b R ξ else 0)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        R ^ (treeK a b) * (if TcCompat a b p e ξ then |tcC β a b μ lam Fd Gd e ξ| else 0) := by
        refine Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun ξ _ => ?_
        by_cases h : TcCompat a b p e ξ
        · simp only [if_pos h]
          rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (tc_Eg_abs_le hR a b ξ) (abs_nonneg _)
        · simp [h]
    _ = R ^ (treeK a b) * ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        (if TcCompat a b p e ξ then |tcC β a b μ lam Fd Gd e ξ| else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left habs (by positivity)

-- ===== P12t =====
/-- Modified (collision) weights. -/
private def tcRho2 {J ℓ : ℕ} (β : ℝ) (a b : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ)
    (Gd : Fin n → ℝ) (s s' : Fin (treeK a b)) (σ : TcLam J ℓ B)
    (v : TreeVtx (treeK a b)) (x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ :=
  |tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x| *
    (if v = Sum.inr s then (if x = Sum.inr σ then 1 else 0) else 1) *
    (if v = Sum.inr s' then (if x = Sum.inr σ then 1 else 0) else 1)

open Classical in
private lemma tc_Fq_le {J ℓ : ℕ} {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (a b : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ C) (hlam : ∀ j, 0 ≤ lam j ∧ lam j ≤ C)
    (hF : ∀ i, |Fd i| ≤ 1) (hG : ∀ j, |Gd j| ≤ 1)
    (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) (s s' : Fin (treeK a b))
    (σ : TcLam J ℓ B) (q : Quotient (treeSetoid p)) :
    ∑ x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B,
      ∏ v ∈ Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q),
        tcRho2 (B := B) (J := J) (ℓ := ℓ) β a b μ lam Fd Gd s s' σ v x ≤
    (if q = treeMk p (Sum.inr s) ∨ q = treeMk p (Sum.inr s') then 1 else
      (Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ)) *
      C ^ (Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q)).card := by
  have hC0 : 0 ≤ C := by linarith
  set fib := Finset.univ.filter (fun v : TreeVtx (treeK a b) => Quotient.mk (treeSetoid p) v = q) with hfib
  have hprod : ∀ x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B,
      ∏ v ∈ fib, tcRho2 (B := B) (J := J) (ℓ := ℓ) β a b μ lam Fd Gd s s' σ v x =
      (∏ v ∈ fib, |tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x|) *
        ((if Sum.inr s ∈ fib then (if x = Sum.inr σ then (1 : ℝ) else 0) else 1) *
          (if Sum.inr s' ∈ fib then (if x = Sum.inr σ then (1 : ℝ) else 0) else 1)) := by
    intro x
    unfold tcRho2
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_ite_eq' fib (Sum.inr s) (fun _ => (if x = Sum.inr σ then (1 : ℝ) else 0)),
      Finset.prod_ite_eq' fib (Sum.inr s') (fun _ => (if x = Sum.inr σ then (1 : ℝ) else 0))]
    ring
  have hbd : ∀ x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B,
      ∏ v ∈ fib, |tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x| ≤ C ^ fib.card := fun x =>
    tc_prod_abs_le _ _ C hC0 fun v => tc_rho_abs_le hβ a b μ lam Fd Gd C hC hμ hlam hF hG v x
  have hs : Sum.inr s ∈ fib ↔ q = treeMk p (Sum.inr s) := by
    simp [hfib, treeMk, eq_comm]
  have hs' : Sum.inr s' ∈ fib ↔ q = treeMk p (Sum.inr s') := by
    simp [hfib, treeMk, eq_comm]
  simp only [hprod]
  set ind : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B → ℝ := fun x => if x = Sum.inr σ then 1 else 0 with hind
  have hind01 : ∀ x, 0 ≤ ind x ∧ ind x ≤ 1 := fun x => by
    simp only [hind]; split_ifs <;> simp
  set w : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B → ℝ := fun x =>
    (if Sum.inr s ∈ fib then ind x else 1) * (if Sum.inr s' ∈ fib then ind x else 1) with hw
  have hw01 : ∀ x, 0 ≤ w x ∧ w x ≤ 1 := by
    intro x
    obtain ⟨h0, h1⟩ := hind01 x
    simp only [hw]
    split_ifs <;> constructor <;> nlinarith
  have hPbd : ∀ x, (∏ v ∈ fib, |tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x|) * w x ≤ C ^ fib.card := by
    intro x
    calc _ ≤ C ^ fib.card * 1 := mul_le_mul (hbd x) (hw01 x).2 (hw01 x).1 (by positivity)
      _ = _ := by ring
  have hPnn : ∀ x, 0 ≤ (∏ v ∈ fib, |tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x|) * w x :=
    fun x => mul_nonneg (Finset.prod_nonneg fun v _ => abs_nonneg _) (hw01 x).1
  show ∑ x, (∏ v ∈ fib, |tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v x|) * w x ≤ _
  by_cases hsp : q = treeMk p (Sum.inr s) ∨ q = treeMk p (Sum.inr s')
  · rw [if_pos hsp]
    have hwsp : ∀ x, w x ≤ ind x := by
      intro x
      obtain ⟨h0, h1⟩ := hind01 x
      simp only [hw]
      rcases hsp with h | h
      · rw [if_pos (hs.mpr h)]
        by_cases h' : Sum.inr s' ∈ fib
        · rw [if_pos h']; nlinarith
        · rw [if_neg h']; linarith
      · rw [if_pos (hs'.mpr h)]
        by_cases h' : Sum.inr s ∈ fib
        · rw [if_pos h']; nlinarith
        · rw [if_neg h']; linarith
    calc _ ≤ ∑ x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B, C ^ fib.card * ind x := by
          refine Finset.sum_le_sum fun x _ => ?_
          calc _ ≤ C ^ fib.card * w x := mul_le_mul_of_nonneg_right (hbd x) (hw01 x).1
            _ ≤ _ := mul_le_mul_of_nonneg_left (hwsp x) (by positivity)
      _ = 1 * C ^ fib.card := by
          rw [← Finset.mul_sum]
          simp [hind, mul_comm]
  · rw [if_neg hsp]
    have hw1 : ∀ x, w x = 1 := by
      intro x
      have h1 : ¬ Sum.inr s ∈ fib := fun h => hsp (Or.inl (hs.mp h))
      have h2 : ¬ Sum.inr s' ∈ fib := fun h => hsp (Or.inr (hs'.mp h))
      simp [hw, h1, h2]
    calc _ ≤ ∑ _x : (Fin m ⊕ Fin n) ⊕ TcLam J ℓ B, C ^ fib.card :=
          Finset.sum_le_sum fun x _ => hPbd x
      _ = _ := by simp

open Classical in
private lemma tc_coll_sum_le {J ℓ : ℕ} {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (a b : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ C) (hlam : ∀ j, 0 ≤ lam j ∧ lam j ≤ C)
    (hF : ∀ i, |Fd i| ≤ 1) (hG : ∀ j, |Gd j| ≤ 1)
    (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) (s s' : Fin (treeK a b))
    (hne : treeMk p (Sum.inr s) ≠ treeMk p (Sum.inr s')) (σ : TcLam J ℓ B) :
    ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      (if TcCompat a b p e ξ ∧ ξ s = σ ∧ ξ s' = σ then |tcC β a b μ lam Fd Gd e ξ| else 0) ≤
    |(B : ℝ)⁻¹| ^ (treeK a b + 1) *
      ((Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) ^ (Nat.card (Quotient (treeSetoid p)) - 2) *
        C ^ (2 * treeK a b)) := by
  have hC0 : 0 ≤ C := by linarith
  have hw := tc_weighted_sum (B := B) β a b μ lam Fd Gd (|(B : ℝ)⁻¹| ^ (treeK a b + 1))
    (fun v x => tcRho2 (B := B) (J := J) (ℓ := ℓ) β a b μ lam Fd Gd s s' σ v x)
    (fun v x h => by simp [tcRho2, h]) p
  have hL : ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      (if TcCompat a b p e ξ ∧ ξ s = σ ∧ ξ s' = σ then |tcC β a b μ lam Fd Gd e ξ| else 0) =
      ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        (if TcCompat a b p e ξ then |(B : ℝ)⁻¹| ^ (treeK a b + 1) *
          ∏ v, tcRho2 (B := B) (J := J) (ℓ := ℓ) β a b μ lam Fd Gd s s' σ v (tcPsi a b e ξ v)
          else 0) := by
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ξ _ => ?_
    by_cases h : TcCompat a b p e ξ
    · rw [if_pos h]
      have hprod : ∏ v, tcRho2 (B := B) (J := J) (ℓ := ℓ) β a b μ lam Fd Gd s s' σ v (tcPsi a b e ξ v) =
          (∏ v, |tcRho (J := J) (ℓ := ℓ) β a b μ lam Fd Gd v (tcPsi a b e ξ v)|) *
            ((if ξ s = σ then 1 else 0) * (if ξ s' = σ then 1 else 0)) := by
        unfold tcRho2
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_ite_eq' Finset.univ (Sum.inr s : TreeVtx (treeK a b))
            (fun v => (if tcPsi (B := B) (J := J) (ℓ := ℓ) a b e ξ v = Sum.inr σ then (1 : ℝ) else 0)),
          Finset.prod_ite_eq' Finset.univ (Sum.inr s' : TreeVtx (treeK a b))
            (fun v => (if tcPsi (B := B) (J := J) (ℓ := ℓ) a b e ξ v = Sum.inr σ then (1 : ℝ) else 0))]
        simp [tcPsi]
      rw [hprod]
      unfold tcC
      rw [abs_mul, abs_pow, Finset.abs_prod]
      by_cases h1 : ξ s = σ <;> by_cases h2 : ξ s' = σ <;> simp [h, h1, h2]
    · rw [if_neg h, if_neg (fun h' => h h'.1)]
  rw [hL, hw]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set NX : ℝ := (Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) with hNX
  set q1 := treeMk p (Sum.inr s)
  set q2 := treeMk p (Sum.inr s')
  calc _ ≤ ∏ q : Quotient (treeSetoid p), ((if q = q1 ∨ q = q2 then (1 : ℝ) else NX) *
        C ^ (Finset.univ.filter (fun v => Quotient.mk (treeSetoid p) v = q)).card) :=
        Finset.prod_le_prod₀ (fun q _ => Finset.sum_nonneg fun x _ => Finset.prod_nonneg fun v _ =>
          by unfold tcRho2; split_ifs <;> simp [abs_nonneg]) (fun q _ =>
          tc_Fq_le hβ a b μ lam Fd Gd C hC hμ hlam hF hG p s s' σ q)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, tc_fiber_card_sum]
      have h2k : Fintype.card (TreeVtx (treeK a b)) = 2 * treeK a b := by
        simp [TreeVtx, Fintype.card_sum]; ring
      rw [h2k]
      congr 1
      rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
      congr 1
      have hsum := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Quotient (treeSetoid p)))) (fun q => q = q1 ∨ q = q2)
      have hpair : (Finset.univ.filter (fun q : Quotient (treeSetoid p) => q = q1 ∨ q = q2)).card = 2 := by
        have : Finset.univ.filter (fun q : Quotient (treeSetoid p) => q = q1 ∨ q = q2) = {q1, q2} := by
          ext q; simp
        rw [this, Finset.card_pair hne]
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hsum
      omega

-- ===== P12u =====
private lemma tc_sum_swap3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ c, ∑ b, f a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

open Classical in
private lemma tc_compat_const {J ℓ : ℕ} (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b))
    (e : Fin (treeK a b) → Fin m ⊕ Fin n) (ξ : Fin (treeK a b) → TcLam J ℓ B)
    (h : TcCompat a b p e ξ) (r r' : Fin (treeK a b))
    (hr : treeMk p (Sum.inr r) = treeMk p (Sum.inr r')) : ξ r = ξ r' := by
  have := (tc_compat_iff a b p e ξ).mp h _ _ (Quotient.exact hr)
  simpa [tcPsi] using this

open Classical in
private lemma tc_ret_err {J ℓ : ℕ} {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) {R : ℝ} (hR : 0 < R) (a b : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ C) (hlam : ∀ j, 0 ≤ lam j ∧ lam j ≤ C)
    (hF : ∀ i, |Fd i| ≤ 1) (hG : ∀ j, |Gd j| ≤ 1)
    (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) (hret : treeRetained p) :
    |∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      (if TcCompat a b p e ξ then tcC β a b μ lam Fd Gd e ξ * tcEg a b R ξ else 0) -
      tcM a b R p * ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        (if TcCompat a b p e ξ then tcC β a b μ lam Fd Gd e ξ else 0)| ≤
    2 * R ^ (treeK a b) * ((treeK a b : ℝ) * (treeK a b : ℝ) *
      ((Fintype.card (TcLam J ℓ B) : ℝ) * (|(B : ℝ)⁻¹| ^ (treeK a b + 1) *
        ((Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) ^ (treeK a b - 1) *
          C ^ (2 * treeK a b))))) := by
  have hcard : Nat.card (Quotient (treeSetoid p)) = treeK a b + 1 := hret
  set Coll : (Fin (treeK a b) → TcLam J ℓ B) → Prop := fun ξ =>
    ∃ s s', treeMk p (Sum.inr s) ≠ treeMk p (Sum.inr s') ∧ ξ s = ξ s' with hColl
  have hdiff : ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      (if TcCompat a b p e ξ then tcC β a b μ lam Fd Gd e ξ * tcEg a b R ξ else 0) -
      tcM a b R p * ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        (if TcCompat a b p e ξ then tcC β a b μ lam Fd Gd e ξ else 0) =
      ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        (if TcCompat a b p e ξ then tcC β a b μ lam Fd Gd e ξ * (tcEg a b R ξ - tcM a b R p) else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    split_ifs <;> ring
  rw [hdiff]
  -- pointwise bound
  have hpt : ∀ (e : Fin (treeK a b) → Fin m ⊕ Fin n) (ξ : Fin (treeK a b) → TcLam J ℓ B),
      |(if TcCompat a b p e ξ then tcC β a b μ lam Fd Gd e ξ * (tcEg a b R ξ - tcM a b R p) else 0)| ≤
      2 * R ^ (treeK a b) * ∑ s : Fin (treeK a b), ∑ s' : Fin (treeK a b), ∑ σ : TcLam J ℓ B,
        (if treeMk p (Sum.inr s) ≠ treeMk p (Sum.inr s') then
          (if TcCompat a b p e ξ ∧ ξ s = σ ∧ ξ s' = σ then |tcC β a b μ lam Fd Gd e ξ| else 0) else 0) := by
    intro e ξ
    by_cases hc : TcCompat a b p e ξ
    · rw [if_pos hc]
      by_cases hcoll : Coll ξ
      · obtain ⟨s, s', hne, hs⟩ := hcoll
        have hsingle : |tcC β a b μ lam Fd Gd e ξ| ≤ ∑ s : Fin (treeK a b), ∑ s' : Fin (treeK a b),
            ∑ σ : TcLam J ℓ B, (if treeMk p (Sum.inr s) ≠ treeMk p (Sum.inr s') then
              (if TcCompat a b p e ξ ∧ ξ s = σ ∧ ξ s' = σ then |tcC β a b μ lam Fd Gd e ξ| else 0)
              else 0) := by
          have hnn : ∀ s s' : Fin (treeK a b), ∀ σ : TcLam J ℓ B,
              0 ≤ (if treeMk p (Sum.inr s) ≠ treeMk p (Sum.inr s') then
              (if TcCompat a b p e ξ ∧ ξ s = σ ∧ ξ s' = σ then |tcC β a b μ lam Fd Gd e ξ| else 0)
              else 0) := by
            intro s s' σ; split_ifs <;> simp
          refine le_trans ?_ (Finset.single_le_sum (f := fun s : Fin (treeK a b) => ∑ s' : Fin (treeK a b),
            ∑ σ : TcLam J ℓ B, (if treeMk p (Sum.inr s) ≠ treeMk p (Sum.inr s') then
              (if TcCompat a b p e ξ ∧ ξ s = σ ∧ ξ s' = σ then |tcC β a b μ lam Fd Gd e ξ| else 0)
              else 0)) (fun s _ => Finset.sum_nonneg fun s' _ => Finset.sum_nonneg fun σ _ => hnn s s' σ)
            (Finset.mem_univ s))
          refine le_trans ?_ (Finset.single_le_sum (f := fun s' : Fin (treeK a b) =>
            ∑ σ : TcLam J ℓ B, (if treeMk p (Sum.inr s) ≠ treeMk p (Sum.inr s') then
              (if TcCompat a b p e ξ ∧ ξ s = σ ∧ ξ s' = σ then |tcC β a b μ lam Fd Gd e ξ| else 0)
              else 0)) (fun s' _ => Finset.sum_nonneg fun σ _ => hnn s s' σ) (Finset.mem_univ s'))
          refine le_trans ?_ (Finset.single_le_sum (f := fun σ : TcLam J ℓ B =>
            (if treeMk p (Sum.inr s) ≠ treeMk p (Sum.inr s') then
              (if TcCompat a b p e ξ ∧ ξ s = σ ∧ ξ s' = σ then |tcC β a b μ lam Fd Gd e ξ| else 0)
              else 0)) (fun σ _ => hnn s s' σ) (Finset.mem_univ (ξ s)))
          rw [if_pos hne, if_pos ⟨hc, rfl, hs.symm⟩]
        rw [abs_mul]
        have h2 : |tcEg a b R ξ - tcM a b R p| ≤ 2 * R ^ (treeK a b) := by
          calc _ ≤ |tcEg a b R ξ| + |tcM a b R p| := abs_sub _ _
            _ ≤ R ^ (treeK a b) + R ^ (treeK a b) := add_le_add (tc_Eg_abs_le hR a b ξ) (tc_M_abs_le hR a b p)
            _ = _ := by ring
        calc _ ≤ |tcC β a b μ lam Fd Gd e ξ| * (2 * R ^ (treeK a b)) :=
              mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
          _ ≤ (∑ s : Fin (treeK a b), ∑ s' : Fin (treeK a b), ∑ σ : TcLam J ℓ B,
              (if treeMk p (Sum.inr s) ≠ treeMk p (Sum.inr s') then
              (if TcCompat a b p e ξ ∧ ξ s = σ ∧ ξ s' = σ then |tcC β a b μ lam Fd Gd e ξ| else 0)
              else 0)) * (2 * R ^ (treeK a b)) := mul_le_mul_of_nonneg_right hsingle (by positivity)
          _ = _ := by ring
      · have hEq : tcEg a b R ξ = tcM a b R p := by
          refine tc_Eg_eq_M R a b p ξ (fun r r' hr => tc_compat_const a b p e ξ hc r r' hr) ?_
          intro r r' hrr
          by_contra hne
          exact hcoll ⟨r, r', hne, hrr⟩
        rw [hEq, sub_self, mul_zero, abs_zero]
        positivity
    · rw [if_neg hc, abs_zero]
      positivity
  set BD : ℝ := |(B : ℝ)⁻¹| ^ (treeK a b + 1) *
    ((Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) ^ (treeK a b - 1) * C ^ (2 * treeK a b)) with hBD
  have hBD0 : 0 ≤ BD := by positivity
  set g : (Fin (treeK a b) → Fin m ⊕ Fin n) → (Fin (treeK a b) → TcLam J ℓ B) → Fin (treeK a b) →
      Fin (treeK a b) → TcLam J ℓ B → ℝ := fun e ξ s s' σ =>
    (if treeMk p (Sum.inr s) ≠ treeMk p (Sum.inr s') then
      (if TcCompat a b p e ξ ∧ ξ s = σ ∧ ξ s' = σ then |tcC β a b μ lam Fd Gd e ξ| else 0) else 0)
    with hg
  have hswap : ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      ∑ s : Fin (treeK a b), ∑ s' : Fin (treeK a b), ∑ σ : TcLam J ℓ B, g e ξ s s' σ =
      ∑ s : Fin (treeK a b), ∑ s' : Fin (treeK a b), ∑ σ : TcLam J ℓ B,
        ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B, g e ξ s s' σ := by
    rw [tc_sum_swap3 (fun e ξ s => ∑ s' : Fin (treeK a b), ∑ σ : TcLam J ℓ B, g e ξ s s' σ)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [tc_sum_swap3 (fun e ξ s' => ∑ σ : TcLam J ℓ B, g e ξ s s' σ)]
    refine Finset.sum_congr rfl fun s' _ => ?_
    exact tc_sum_swap3 (fun e ξ σ => g e ξ s s' σ)
  have hterm : ∀ s s' : Fin (treeK a b), ∀ σ : TcLam J ℓ B,
      ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B, g e ξ s s' σ ≤
        BD := by
    intro s s' σ
    by_cases hne : treeMk p (Sum.inr s) ≠ treeMk p (Sum.inr s')
    · have := tc_coll_sum_le (B := B) (J := J) (ℓ := ℓ) hβ a b μ lam Fd Gd C hC hμ hlam hF hG p s s'
        hne σ
      rw [show Nat.card (Quotient (treeSetoid p)) - 2 = treeK a b - 1 by omega] at this
      simp only [hg, if_pos hne]
      exact this
    · simp only [hg, if_neg hne]
      simp
      exact hBD0
  calc _ ≤ ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        |(if TcCompat a b p e ξ then tcC β a b μ lam Fd Gd e ξ * (tcEg a b R ξ - tcM a b R p) else 0)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        2 * R ^ (treeK a b) * ∑ s : Fin (treeK a b), ∑ s' : Fin (treeK a b), ∑ σ : TcLam J ℓ B, g e ξ s s' σ :=
        Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun ξ _ => hpt e ξ
    _ = 2 * R ^ (treeK a b) * ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
        ∑ s : Fin (treeK a b), ∑ s' : Fin (treeK a b), ∑ σ : TcLam J ℓ B, g e ξ s s' σ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]
    _ = 2 * R ^ (treeK a b) * ∑ s : Fin (treeK a b), ∑ s' : Fin (treeK a b), ∑ σ : TcLam J ℓ B,
        ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B, g e ξ s s' σ := by
        rw [hswap]
    _ ≤ 2 * R ^ (treeK a b) * ∑ _s : Fin (treeK a b), ∑ _s' : Fin (treeK a b), ∑ _σ : TcLam J ℓ B, BD := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun s' _ => Finset.sum_le_sum fun σ _ =>
          hterm s s' σ
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

-- ===== P12v =====
section TcNorms

open scoped Matrix.Norms.L2Operator

private lemma tc_opNorm_mul_le {a b c : ℕ} (A : Mat a b) (B' : Mat b c) :
    opNorm (A * B') ≤ opNorm A * opNorm B' := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B'

private lemma tc_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma tc_abs_entry_le_opNorm {p q : ℕ} (K : Mat p q) (i : Fin p) (j : Fin q) :
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

private lemma tc_opNorm_orth_le {p : ℕ} (U : Mat p p) (hU : Uᵀ * U = 1) : opNorm U ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hU] at h
  have h1 : ‖(1 : Mat p p)‖ ≤ 1 := by
    have : (1 : Mat p p) = Matrix.diagonal (fun _ => (1 : ℝ)) := by simp
    rw [this, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => by simp)
  rw [opNorm_eq_norm]
  nlinarith [norm_nonneg U]

private lemma tc_diag_bound {p : ℕ} (U : Mat p p) (hU : Uᵀ * U = 1) (M : Mat p p) (d : Fin p → ℝ)
    (hM : M = U * Matrix.diagonal d * Uᵀ) (c : ℝ) (hc : opNorm M ≤ c) (i : Fin p) : |d i| ≤ c := by
  have hU' : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hD : Matrix.diagonal d = Uᵀ * M * U := by
    rw [hM]
    calc Matrix.diagonal d = (Uᵀ * U) * Matrix.diagonal d * (Uᵀ * U) := by rw [hU]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hentry : (Uᵀ * M * U) i i = d i := by rw [← hD]; simp
  have h1 : |d i| ≤ opNorm (Uᵀ * M * U) := by
    have h := tc_abs_entry_le_opNorm (Uᵀ * M * U) i i
    rw [hentry] at h
    exact h
  have hn : opNorm U ≤ 1 := tc_opNorm_orth_le U hU
  have hn' : opNorm Uᵀ ≤ 1 := by rw [tc_opNorm_transpose]; exact hn
  have h0 : 0 ≤ opNorm M := by rw [opNorm_eq_norm]; exact norm_nonneg _
  have h00 : 0 ≤ opNorm Uᵀ := by rw [opNorm_eq_norm]; exact norm_nonneg _
  have h000 : 0 ≤ opNorm U := by rw [opNorm_eq_norm]; exact norm_nonneg _
  have hc0 : 0 ≤ c := h0.trans hc
  have h2 : opNorm (Uᵀ * M * U) ≤ 1 * c * 1 := by
    calc opNorm (Uᵀ * M * U) ≤ opNorm (Uᵀ * M) * opNorm U := tc_opNorm_mul_le _ _
      _ ≤ (opNorm Uᵀ * opNorm M) * opNorm U :=
          mul_le_mul_of_nonneg_right (tc_opNorm_mul_le _ _) h000
      _ ≤ (1 * c) * 1 :=
          mul_le_mul (mul_le_mul hn' hc h0 zero_le_one) hn h000 (by positivity)
  linarith

end TcNorms

-- ===== P12w =====
private lemma tc_card_lam (J ℓ B : ℕ) : Fintype.card (TcLam J ℓ B) = (J + ℓ + 1) * B := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Int.card_Icc]
  congr 1
  omega

private lemma tc_arith (K : ℕ) (c B : ℝ) (hB : 0 < B) :
    |B⁻¹| ^ (K + 1) * (c * B) ^ K = c ^ K * B⁻¹ := by
  rw [abs_of_pos (inv_pos.mpr hB)]
  calc B⁻¹ ^ (K + 1) * (c * B) ^ K = B⁻¹ * c ^ K * (B⁻¹ * B) ^ K := by
        rw [pow_succ, mul_pow, mul_pow]; ring
    _ = _ := by rw [inv_mul_cancel₀ hB.ne', one_pow]; ring

private lemma tc_card_X (m n J ℓ B : ℕ) :
    Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) = m + n + (J + ℓ + 1) * B := by
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, tc_card_lam]

-- ===== P12x =====
open Classical in
private lemma tc_per_pairing {J ℓ : ℕ} {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) {R : ℝ} (hR : 0 < R) (a b : ℕ)
    (hB1 : 1 ≤ B) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (C : ℝ) (hC : 1 ≤ C)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ C) (hlam : ∀ j, 0 ≤ lam j ∧ lam j ≤ C)
    (hF : ∀ i, |Fd i| ≤ 1) (hG : ∀ j, |Gd j| ≤ 1)
    (Cx : ℝ) (hCx : 1 ≤ Cx)
    (hX : (Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) ≤ Cx * B)
    (hL : (Fintype.card (TcLam J ℓ B) : ℝ) ≤ Cx * B)
    (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) :
    |∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      (if TcCompat a b p e ξ then tcC β a b μ lam Fd Gd e ξ * tcEg a b R ξ else 0) -
      (if treeRetained p then
        ∏ V : Quotient (treeSetoid p), treeClassFactor β ℓ J R B μ lam Fd Gd a b p V else 0)| ≤
    (2 * R ^ (treeK a b) * ((treeK a b : ℝ) * (treeK a b : ℝ)) * Cx ^ (treeK a b) *
      C ^ (2 * treeK a b)) / B := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB1
  have hB1' : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hk2 : 2 ≤ treeK a b := by unfold treeK; omega
  have hkR : (1 : ℝ) ≤ (treeK a b : ℝ) := by exact_mod_cast (by omega : 1 ≤ treeK a b)
  have hC0 : 0 ≤ C := by linarith
  have hCx0 : 0 ≤ Cx := by linarith
  have hNX1 : (1 : ℝ) ≤ (Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) := by
    rw [tc_card_X]
    have : 1 ≤ m + n + (J + ℓ + 1) * B := by nlinarith
    exact_mod_cast this
  have hA1 : (1 : ℝ) ≤ Cx * B := by nlinarith
  by_cases hret : treeRetained p
  · rw [if_pos hret, tc_retained_eq β ℓ J R a b μ lam Fd Gd hBpos.ne' p hret]
    refine (tc_ret_err hβ hR a b μ lam Fd Gd C hC hμ hlam hF hG p hret).trans ?_
    have hpow1 : (Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) ^ (treeK a b - 1) ≤
        (Cx * B) ^ (treeK a b - 1) := pow_le_pow_left₀ (by positivity) hX _
    have hcomb : (Fintype.card (TcLam J ℓ B) : ℝ) *
        (Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) ^ (treeK a b - 1) ≤ (Cx * B) ^ (treeK a b) := by
      calc _ ≤ (Cx * B) * (Cx * B) ^ (treeK a b - 1) :=
            mul_le_mul hL hpow1 (by positivity) (by positivity)
        _ = _ := by
            rw [← pow_succ']; congr 1
    have hK := tc_arith (treeK a b) Cx B hBpos
    calc _ ≤ 2 * R ^ (treeK a b) * ((treeK a b : ℝ) * (treeK a b : ℝ) *
          (|(B : ℝ)⁻¹| ^ (treeK a b + 1) * ((Cx * B) ^ (treeK a b) * C ^ (2 * treeK a b)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc _ = |(B : ℝ)⁻¹| ^ (treeK a b + 1) * ((Fintype.card (TcLam J ℓ B) : ℝ) *
                ((Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) ^ (treeK a b - 1) *
                  C ^ (2 * treeK a b))) := by ring
            _ ≤ |(B : ℝ)⁻¹| ^ (treeK a b + 1) * ((Cx * B) ^ (treeK a b) * C ^ (2 * treeK a b)) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                calc (Fintype.card (TcLam J ℓ B) : ℝ) *
                    ((Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) ^ (treeK a b - 1) *
                      C ^ (2 * treeK a b)) =
                    ((Fintype.card (TcLam J ℓ B) : ℝ) *
                      (Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) ^ (treeK a b - 1)) *
                      C ^ (2 * treeK a b) := by ring
                  _ ≤ _ := mul_le_mul_of_nonneg_right hcomb (by positivity)
      _ = 2 * R ^ (treeK a b) * ((treeK a b : ℝ) * (treeK a b : ℝ) *
          (Cx ^ (treeK a b) * (B : ℝ)⁻¹ * C ^ (2 * treeK a b))) := by
          have hrew : |(B : ℝ)⁻¹| ^ (treeK a b + 1) * ((Cx * B) ^ (treeK a b) * C ^ (2 * treeK a b)) =
              Cx ^ (treeK a b) * (B : ℝ)⁻¹ * C ^ (2 * treeK a b) := by
            rw [← mul_assoc, hK]
          rw [hrew]
      _ = _ := by ring
  · rw [if_neg hret, sub_zero]
    have hcardQ : Nat.card (Quotient (treeSetoid p)) ≤ treeK a b := by
      have h1 := tc_card_le a b p
      have h2 : Nat.card (Quotient (treeSetoid p)) ≠ treeK a b + 1 := hret
      omega
    refine (tc_Sp_abs_le hβ hR a b μ lam Fd Gd C hC hμ hlam hF hG p).trans ?_
    have hpow : (Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) ^ (Nat.card (Quotient (treeSetoid p))) ≤
        (Cx * B) ^ (treeK a b) :=
      (pow_le_pow_right₀ hNX1 hcardQ).trans (pow_le_pow_left₀ (by positivity) hX _)
    have hK := tc_arith (treeK a b) Cx B hBpos
    have hrew : |(B : ℝ)⁻¹| ^ (treeK a b + 1) * ((Cx * B) ^ (treeK a b) * C ^ (2 * treeK a b)) =
        Cx ^ (treeK a b) * (B : ℝ)⁻¹ * C ^ (2 * treeK a b) := by
      rw [← mul_assoc, hK]
    calc _ ≤ R ^ (treeK a b) * (|(B : ℝ)⁻¹| ^ (treeK a b + 1) *
          ((Cx * B) ^ (treeK a b) * C ^ (2 * treeK a b))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = R ^ (treeK a b) * (Cx ^ (treeK a b) * (B : ℝ)⁻¹ * C ^ (2 * treeK a b)) := by rw [hrew]
      _ ≤ 2 * R ^ (treeK a b) * ((treeK a b : ℝ) * (treeK a b : ℝ)) * (Cx ^ (treeK a b) *
            (B : ℝ)⁻¹ * C ^ (2 * treeK a b)) := by
          have h0 : 0 ≤ Cx ^ (treeK a b) * (B : ℝ)⁻¹ * C ^ (2 * treeK a b) := by positivity
          have h1 : (1 : ℝ) ≤ 2 * ((treeK a b : ℝ) * (treeK a b : ℝ)) := by nlinarith
          have h2 : 0 ≤ R ^ (treeK a b) := by positivity
          calc R ^ (treeK a b) * (Cx ^ (treeK a b) * (B : ℝ)⁻¹ * C ^ (2 * treeK a b))
              = (R ^ (treeK a b) * 1) * (Cx ^ (treeK a b) * (B : ℝ)⁻¹ * C ^ (2 * treeK a b)) := by ring
            _ ≤ (R ^ (treeK a b) * (2 * ((treeK a b : ℝ) * (treeK a b : ℝ)))) *
                (Cx ^ (treeK a b) * (B : ℝ)⁻¹ * C ^ (2 * treeK a b)) := by
                gcongr
            _ = _ := by ring
      _ = _ := by field_simp


/-- `lem:app-vol-tree-closure`, snapshot `cr-2026-10-23`. Declaration of record. Moment closure: the
constant `C_W` depends only on `(a, b, ℓ, J, R, C_Σ, γ_⋆)`, so it is quantified before the model data
(dimensions, frozen parameters, spectra, test matrices and time); the probability space is the
independent product model `indepSpaceLaw`. The test matrices are diagonal in the eigenbases of
`S : SpectralData Fp.C`, with diagonal entries `Fd`, `Gd`; the response is `def_app_vol_tree` on the
monomials `x^{2a+1}`, `x^{2b+1}` (`def_app_vol_tree` is `𝔑^{J,R}_ℓ`). The integrability clause is the
source's existence of `𝔼 Tr 𝖶_{a,b}`. The statement, verbatim from `section.tex`:
```latex
\begin{lemma}[Moment closure]\label{lem:app-vol-tree-closure}
Fix $(\ell,J,R)$ and $a,b\ge0$. There is $C_{\mathsf W}$, depending only on
$(a,b,\ell,J,R,C_\Sigma,\gamma_\star)$, such that for all diagonal $F,G$ with
$\norm F,\norm G\le1$,
\begin{equation}\label{eqn:app-vol-tree-closure}
\Big|\frac1B\EE\Tr\mathsf W_{a,b}-\mathfrak R^{J,R}_\ell[F,G](x^{2a+1},x^{2b+1})\Big|\le\frac{C_{\mathsf W}}{B}.
\end{equation}
The response is unchanged under the replications of
\cref{def:app-vol-replication}.
\end{lemma}
```
-/
theorem lem_app_vol_tree_closure (a b ℓ J : ℕ) (R γstar CSig : ℝ) (hR : 0 < R) :
    ∃ CW : ℝ, ∀ (m n B : ℕ) (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (t : ℤ)
      (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (Fm : Mat m m) (Gm : Mat n n),
      SizeFin Fp.C B γstar CSig →
      Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ →
      Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
          (B : ℝ)⁻¹ * Matrix.trace
            (treeWord Fm Gm (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω) a b))
        (indepSpaceLaw m n B) ∧
      |(∫ ω, (B : ℝ)⁻¹ * Matrix.trace
            (treeWord Fm Gm (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω) a b)
          ∂(indepSpaceLaw m n B))
        - def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd
            (Polynomial.X ^ (2 * a + 1)) (Polynomial.X ^ (2 * b + 1))|
        ≤ CW / (B : ℝ) := by
  classical
  set Cx : ℝ := 2 * max γstar 0 + J + ℓ + 1 with hCx
  set Cmu : ℝ := max 1 CSig with hCmu
  set K1 : ℝ := 2 * R ^ (treeK a b) * ((treeK a b : ℝ) * (treeK a b : ℝ)) * Cx ^ (treeK a b) *
    Cmu ^ (2 * treeK a b) with hK1
  set N : ℝ := (Fintype.card (TreeMatch (treeK a b) × TreeMatch (treeK a b)) : ℝ) with hN
  refine ⟨N * K1, ?_⟩
  intro m n B Fp S t Fd Gd Fm Gm hSize hF hG hFn hGn
  have hB1 : 1 ≤ B := Fp.hB
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB1
  obtain ⟨hint, hval⟩ := tc_expectation Fp S ℓ J R t a b Fd Gd Fm Gm hF hG
  refine ⟨hint, ?_⟩
  rw [hval, treeClosure_monomial]
  have hC1 : (1 : ℝ) ≤ Cmu := le_max_left _ _
  obtain ⟨hμ0, hSout, -⟩ := tc_spec_out Fp S
  obtain ⟨hlam0, hSin, -⟩ := tc_spec_in Fp S
  have hμ : ∀ i, 0 ≤ S.μ i ∧ S.μ i ≤ Cmu := fun i =>
    ⟨hμ0 i, (le_abs_self _).trans ((tc_diag_bound S.uOut S.huOut Fp.C.Sout S.μ hSout CSig
      hSize.2.1 i).trans (le_max_right _ _))⟩
  have hlam : ∀ j, 0 ≤ S.lam j ∧ S.lam j ≤ Cmu := fun j =>
    ⟨hlam0 j, (le_abs_self _).trans ((tc_diag_bound S.vIn S.hvIn Fp.C.Sin S.lam hSin CSig
      hSize.2.2 j).trans (le_max_right _ _))⟩
  have hFd : ∀ i, |Fd i| ≤ 1 := fun i => tc_diag_bound S.uOut S.huOut Fm Fd hF 1 hFn i
  have hGd : ∀ j, |Gd j| ≤ 1 := fun j => tc_diag_bound S.vIn S.hvIn Gm Gd hG 1 hGn j
  have hmB : (m : ℝ) ≤ max γstar 0 * B := by
    have h1 : (m : ℝ) ≤ ((max m n : ℕ) : ℝ) := by exact_mod_cast le_max_left m n
    exact h1.trans (hSize.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hBpos.le))
  have hnB : (n : ℝ) ≤ max γstar 0 * B := by
    have h1 : (n : ℝ) ≤ ((max m n : ℕ) : ℝ) := by exact_mod_cast le_max_right m n
    exact h1.trans (hSize.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hBpos.le))
  have hCx1 : (1 : ℝ) ≤ Cx := by
    have : 0 ≤ max γstar 0 := le_max_right _ _
    simp only [hCx]
    have h1 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have h2 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    linarith
  have hL : (Fintype.card (TcLam J ℓ B) : ℝ) ≤ Cx * B := by
    rw [tc_card_lam]
    push_cast
    simp only [hCx]
    have : 0 ≤ max γstar 0 := le_max_right _ _
    nlinarith
  have hX : (Fintype.card ((Fin m ⊕ Fin n) ⊕ TcLam J ℓ B) : ℝ) ≤ Cx * B := by
    rw [tc_card_X]
    push_cast
    simp only [hCx]
    nlinarith
  have hβ := Fp.hβ
  -- rewrite the sum over assignments as a sum over pairings
  have hsum : ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n, ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
      ((B : ℝ)⁻¹) ^ (treeK a b + 1) *
        ((∏ v : TreeVtx (treeK a b),
          tcRho (J := J) (ℓ := ℓ) Fp.β a b S.μ S.lam Fd Gd v (tcPsi a b e ξ v)) *
          (tcEg a b R ξ * tcNmatch a b e ξ)) =
      ∑ p : TreeMatch (treeK a b) × TreeMatch (treeK a b), ∑ e : Fin (treeK a b) → Fin m ⊕ Fin n,
        ∑ ξ : Fin (treeK a b) → TcLam J ℓ B,
          (if TcCompat a b p e ξ then tcC Fp.β a b S.μ S.lam Fd Gd e ξ * tcEg a b R ξ else 0) := by
    rw [← tc_sum_pairings (B := B) (J := J) (ℓ := ℓ) Fp.β a b R S.μ S.lam Fd Gd]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ξ _ => ?_
    unfold tcC
    ring
  rw [hsum]
  unfold treeMono
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ p : TreeMatch (treeK a b) × TreeMatch (treeK a b), K1 / (B : ℝ) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        exact tc_per_pairing (B := B) hβ hR a b hB1 S.μ S.lam Fd Gd Cmu hC1 hμ hlam hFd hGd Cx
          hCx1 hX hL p
    _ = N * K1 / (B : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring


/-! ### Private helpers for `lem:app-vol-norm` (proved here; no upstream dependence) -/

section NormHelpers

open scoped Matrix.Norms.L2Operator

private lemma nrm_opNorm_nonneg {p q : ℕ} (K : Mat p q) : 0 ≤ opNorm K := by
  unfold opNorm
  exact norm_nonneg _

private lemma nrm_opNorm_mul_le {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B

private lemma nrm_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma nrm_opNorm_smul {a b : ℕ} (c : ℝ) (A : Mat a b) :
    opNorm (c • A) = |c| * opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma nrm_opNorm_add_le {a b : ℕ} (A C : Mat a b) :
    opNorm (A + C) ≤ opNorm A + opNorm C := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact norm_add_le A C

private lemma nrm_opNorm_sum_le {a b : ℕ} {ι : Type*} (s : Finset ι) (M : ι → Mat a b) :
    opNorm (∑ i ∈ s, M i) ≤ ∑ i ∈ s, opNorm (M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [opNorm_eq_norm]
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact (nrm_opNorm_add_le _ _).trans (add_le_add le_rfl ih)

private lemma nrm_opNorm_sqrt_mul_self {a : ℕ} (S : Mat a a) (hS : S.PosSemidef) :
    opNorm (CFC.sqrt S) * opNorm (CFC.sqrt S) = opNorm S := by
  have hh : (CFC.sqrt S)ᴴ = CFC.sqrt S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).isHermitian
  have hsq : CFC.sqrt S * CFC.sqrt S = S :=
    CFC.sqrt_mul_sqrt_self S (Matrix.nonneg_iff_posSemidef.mpr hS)
  have := Matrix.l2_opNorm_conjTranspose_mul_self (CFC.sqrt S)
  rw [hh, hsq] at this
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact this.symm

private lemma nrm_opNorm_diagonal_le {a : ℕ} (d : Fin a → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hd : ∀ i, |d i| ≤ c) : opNorm (Matrix.diagonal d) ≤ c := by
  rw [opNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hc).2 (fun i => by simpa [Real.norm_eq_abs] using hd i)

private lemma nrm_trunc_abs_le {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |if |x| ≤ R then x else 0| ≤ R := by
  split_ifs with h
  · exact h
  · simpa using hR.le

end NormHelpers

/-- Factorisation of one tree-coefficient block: `∑_a c_a (r_out z_a w_aᵀ r_in) = r_out (Z diag(c) Wᵀ) r_in`. -/
private lemma nrm_sum_outer_eq {m n B : ℕ} (rO : Mat m m) (rI : Mat n n) (c : Fin B → ℝ)
    (Z : Mat m B) (W : Mat n B) (z : Fin B → Vec m) (w : Fin B → Vec n)
    (hz : ∀ i a, Z i a = z a i) (hw : ∀ j a, W j a = w a j) :
    ∑ a, c a • (rO * outer (z a) (w a) * rI) = rO * (Z * Matrix.diagonal c * Wᵀ) * rI := by
  have hsum : ∑ a, c a • outer (z a) (w a) = Z * Matrix.diagonal c * Wᵀ := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, outer, Matrix.vecMulVec_apply,
      Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul, hz, hw, Matrix.diagonal_apply,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [← hsum, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- One block of `lem:app-vol-norm`: `‖r_out Z diag(c) Wᵀ r_in‖ ≤ C_Σ X ρ X` when `‖Z‖, ‖W‖ ≤ X`,
`|c_a| ≤ ρ` and `‖r_out‖ ‖r_in‖ ≤ C_Σ`. -/
private lemma nrm_block {m n B : ℕ} (rO : Mat m m) (rI : Mat n n) (Z : Mat m B) (W : Mat n B)
    (c : Fin B → ℝ) (X ρ CSig : ℝ) (hX : 0 ≤ X) (hρ : 0 ≤ ρ) (hCS : 0 ≤ CSig)
    (hab : opNorm rO * opNorm rI ≤ CSig) (hZ : opNorm Z ≤ X) (hW : opNorm W ≤ X)
    (hc : ∀ a, |c a| ≤ ρ) :
    opNorm (rO * (Z * Matrix.diagonal c * Wᵀ) * rI) ≤ CSig * (X * ρ * X) := by
  have hd : opNorm (Matrix.diagonal c) ≤ ρ := nrm_opNorm_diagonal_le c ρ hρ hc
  have hM : opNorm (Z * Matrix.diagonal c * Wᵀ) ≤ X * ρ * X := by
    calc opNorm (Z * Matrix.diagonal c * Wᵀ)
        ≤ opNorm (Z * Matrix.diagonal c) * opNorm Wᵀ := nrm_opNorm_mul_le _ _
      _ ≤ (opNorm Z * opNorm (Matrix.diagonal c)) * opNorm Wᵀ :=
          mul_le_mul_of_nonneg_right (nrm_opNorm_mul_le _ _) (nrm_opNorm_nonneg _)
      _ = (opNorm Z * opNorm (Matrix.diagonal c)) * opNorm W := by rw [nrm_opNorm_transpose]
      _ ≤ (X * ρ) * X :=
          mul_le_mul (mul_le_mul hZ hd (nrm_opNorm_nonneg _) hX) hW (nrm_opNorm_nonneg _)
            (mul_nonneg hX hρ)
  calc opNorm (rO * (Z * Matrix.diagonal c * Wᵀ) * rI)
      ≤ opNorm (rO * (Z * Matrix.diagonal c * Wᵀ)) * opNorm rI := nrm_opNorm_mul_le _ _
    _ ≤ (opNorm rO * opNorm (Z * Matrix.diagonal c * Wᵀ)) * opNorm rI :=
        mul_le_mul_of_nonneg_right (nrm_opNorm_mul_le _ _) (nrm_opNorm_nonneg _)
    _ = (opNorm rO * opNorm rI) * opNorm (Z * Matrix.diagonal c * Wᵀ) := by ring
    _ ≤ CSig * (X * ρ * X) := mul_le_mul hab hM (nrm_opNorm_nonneg _) hCS

/-- The cutoff matrix as a sum of blocks over `α`. -/
private lemma nrm_cutoffMat_eq {m n B : ℕ} (Fp : FrozenParams m n B) (ℓ J : ℕ) (R : ℝ) (t : ℤ)
    (l : ℕ) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) :
    cutoffMat Fp ℓ J R t l ω = ((B : ℝ))⁻¹ • ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
      rOut Fp.C * (cutoffZ t α ω * Matrix.diagonal (fun a => treeVarpi Fp.β ℓ l α *
        (if |(ω (t + 1 + α, a)).1| ≤ R then (ω (t + 1 + α, a)).1 else 0)) *
          (cutoffW t α ω)ᵀ) * rIn Fp.C := by
  unfold cutoffMat
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  exact nrm_sum_outer_eq (rOut Fp.C) (rIn Fp.C)
    (fun a => treeVarpi Fp.β ℓ l α * (if |(ω (t + 1 + α, a)).1| ≤ R then (ω (t + 1 + α, a)).1 else 0))
    (cutoffZ t α ω) (cutoffW t α ω) (fun a => (ω (t + 1 + α, a)).2.1)
    (fun a => (ω (t + 1 + α, a)).2.2) (fun _ _ => rfl) (fun _ _ => rfl)

section VarpiSum

private lemma nrm_emaW_partial (β : ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range k, Muon.emaW β j = 1 - β ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    unfold Muon.emaW
    ring

private lemma nrm_treeVarpi_nonneg {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ l : ℕ) (α : ℤ) :
    0 ≤ treeVarpi β ℓ l α := by
  have h1 : 0 ≤ Muon.emaW β α.natAbs := by
    unfold Muon.emaW
    exact mul_nonneg (by linarith [hβ.2]) (pow_nonneg hβ.1 _)
  have h2 : 0 ≤ Muon.emaW β (ℓ - α.toNat) := by
    unfold Muon.emaW
    exact mul_nonneg (by linarith [hβ.2]) (pow_nonneg hβ.1 _)
  unfold treeVarpi
  split_ifs <;> first
    | exact h1
    | exact mul_nonneg (pow_nonneg hβ.1 _) h1
    | exact le_rfl
    | exact h2

private lemma nrm_sum_Icc_neg (J : ℕ) (f : ℤ → ℝ) :
    ∑ α ∈ Finset.Icc (-(J : ℤ)) 0, f α = ∑ j ∈ Finset.range (J + 1), f (-(j : ℤ)) := by
  apply Finset.sum_nbij' (fun α : ℤ => (-α).toNat) (fun j : ℕ => -(j : ℤ))
  · intro α hα; simp only [Finset.mem_Icc, Finset.mem_range] at hα ⊢; omega
  · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
  · intro α hα; simp only [Finset.mem_Icc] at hα; try dsimp only
    omega
  · intro j hj; simp only [Finset.mem_range] at hj; try dsimp only
    omega
  · intro α hα; simp only [Finset.mem_Icc] at hα; try dsimp only
    congr 1
    omega

private lemma nrm_sum_Icc_pos (ℓ : ℕ) (f : ℤ → ℝ) :
    ∑ α ∈ Finset.Icc (1 : ℤ) (ℓ : ℤ), f α = ∑ k ∈ Finset.range ℓ, f ((ℓ : ℤ) - (k : ℤ)) := by
  apply Finset.sum_nbij' (fun α : ℤ => ℓ - α.toNat) (fun k : ℕ => (ℓ : ℤ) - (k : ℤ))
  · intro α hα; simp only [Finset.mem_Icc, Finset.mem_range] at hα ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
  · intro α hα; simp only [Finset.mem_Icc] at hα; try dsimp only
    omega
  · intro k hk; simp only [Finset.mem_range] at hk; try dsimp only
    omega
  · intro α hα; simp only [Finset.mem_Icc] at hα; try dsimp only
    congr 1
    omega

/-- The coefficient mass `∑_{α} |ϖ_{l,α}| ≤ 1` (the EMA weights sum to one). -/
private lemma nrm_varpi_sum_le (β : ℝ) (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (l : ℕ)
    (hl : l = 1 ∨ l = 2) :
    ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ), |treeVarpi β ℓ l α| ≤ 1 := by
  have habs : ∀ α, |treeVarpi β ℓ l α| = treeVarpi β ℓ l α := fun α =>
    abs_of_nonneg (nrm_treeVarpi_nonneg hβ ℓ l α)
  simp only [habs]
  have hU : Finset.Icc (-(J : ℤ)) (ℓ : ℤ) = Finset.Icc (-(J : ℤ)) 0 ∪ Finset.Icc 1 (ℓ : ℤ) := by
    ext α; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hD : Disjoint (Finset.Icc (-(J : ℤ)) 0) (Finset.Icc 1 (ℓ : ℤ)) := by
    rw [Finset.disjoint_left]
    intro α h1 h2
    simp only [Finset.mem_Icc] at h1 h2
    omega
  have hpart := nrm_emaW_partial β (J + 1)
  have hβl : 0 ≤ β ^ ℓ := pow_nonneg hβ.1 ℓ
  have hβJ : 0 ≤ β ^ (J + 1) := pow_nonneg hβ.1 _
  have hβk := nrm_emaW_partial β ℓ
  rw [hU, Finset.sum_union hD, nrm_sum_Icc_neg, nrm_sum_Icc_pos]
  rcases hl with rfl | rfl
  · have e1 : ∀ j ∈ Finset.range (J + 1),
        treeVarpi β ℓ 1 (-(j : ℤ)) = Muon.emaW β j := by
      intro j _
      unfold treeVarpi
      simp
    have e2 : ∀ k ∈ Finset.range ℓ, treeVarpi β ℓ 1 ((ℓ : ℤ) - (k : ℤ)) = 0 := by
      intro k hk
      simp only [Finset.mem_range] at hk
      have h : ¬ ((ℓ : ℤ) - (k : ℤ) ≤ 0) := by omega
      unfold treeVarpi
      simp [h]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_const_zero, add_zero, hpart]
    linarith
  · have e1 : ∀ j ∈ Finset.range (J + 1),
        treeVarpi β ℓ 2 (-(j : ℤ)) = β ^ ℓ * Muon.emaW β j := by
      intro j _
      unfold treeVarpi
      simp
    have e2 : ∀ k ∈ Finset.range ℓ, treeVarpi β ℓ 2 ((ℓ : ℤ) - (k : ℤ)) = Muon.emaW β k := by
      intro k hk
      simp only [Finset.mem_range] at hk
      have h : ¬ ((ℓ : ℤ) - (k : ℤ) ≤ 0) := by omega
      have hto : ((ℓ : ℤ) - (k : ℤ)).toNat = ℓ - k := by omega
      unfold treeVarpi
      rw [if_neg h, if_neg (by norm_num : ¬ (2 : ℕ) = 1), hto]
      congr 1
      omega
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, hpart, hβk]
    nlinarith [mul_nonneg hβl hβJ]

end VarpiSum

/-! ## Norm control -/

/-! ### Private helpers for `lem:app-vol-norm` part (i): i.i.d. marginals of the product model -/

section NormIid

private lemma nrm_pick_z (m n : ℕ) :
    (indepSlotLaw m n).map (fun x : ℝ × (Vec m × Vec n) => x.2.1) =
      Muon.Foundations.stdGaussianPi m := by
  unfold indepSlotLaw
  rw [show (fun x : ℝ × (Vec m × Vec n) => x.2.1) = Prod.fst ∘ Prod.snd from rfl,
    ← Measure.map_map measurable_fst measurable_snd, Measure.map_snd_prod, measure_univ, one_smul,
    Measure.map_fst_prod, measure_univ, one_smul]

private lemma nrm_pick_w (m n : ℕ) :
    (indepSlotLaw m n).map (fun x : ℝ × (Vec m × Vec n) => x.2.2) =
      Muon.Foundations.stdGaussianPi n := by
  unfold indepSlotLaw
  rw [show (fun x : ℝ × (Vec m × Vec n) => x.2.2) = Prod.snd ∘ Prod.snd from rfl,
    ← Measure.map_map measurable_snd measurable_snd, Measure.map_snd_prod, measure_univ, one_smul,
    Measure.map_snd_prod, measure_univ, one_smul]

/-- A block of one coordinate of the slots at time `τ` is an i.i.d. `N(0,1)` matrix. -/
private lemma nrm_iid_slot {m n B k : ℕ} (τ : ℤ) (pick : ℝ × (Vec m × Vec n) → Vec k)
    (hmeas : Measurable pick)
    (hpick : (indepSlotLaw m n).map pick = Muon.Foundations.stdGaussianPi k) :
    Muon.External.IsIIDGaussianMatrix (indepSpaceLaw m n B)
      (fun (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (i : Fin k) (a : Fin B) => pick (ω (τ, a)) i) := by
  have hF : Measurable (fun (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (ij : Fin k × Fin B) =>
      pick (ω (τ, ij.2)) ij.1) := by
    refine measurable_pi_iff.mpr (fun ij => ?_)
    exact ((measurable_pi_apply ij.1).comp hmeas).comp (measurable_pi_apply (τ, ij.2))
  unfold Muon.External.IsIIDGaussianMatrix
  show (indepSpaceLaw m n B).map (fun (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n))
      (ij : Fin k × Fin B) => pick (ω (τ, ij.2)) ij.1) =
    Measure.pi (fun _ : Fin k × Fin B => gaussianReal 0 1)
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply hF (MeasurableSet.univ_pi hs)]
  have hpre : (fun (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (ij : Fin k × Fin B) =>
        pick (ω (τ, ij.2)) ij.1) ⁻¹' (Set.univ.pi s) =
      Set.pi (↑(Finset.univ.image (fun a : Fin B => ((τ, a) : ℤ × Fin B))) : Set (ℤ × Fin B))
        (fun sl => pick ⁻¹' (Set.univ.pi fun i => s (i, sl.2))) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_pi, Finset.coe_image,
      Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and]
    constructor
    · rintro h _ ⟨a, rfl⟩ i
      exact h (i, a)
    · intro h ij
      exact h (τ, ij.2) ⟨ij.2, rfl⟩ ij.1
  have hslot : ∀ a : Fin B, indepSlotLaw m n (pick ⁻¹' (Set.univ.pi fun i => s (i, a))) =
      ∏ i, gaussianReal 0 1 (s (i, a)) := by
    intro a
    rw [← Measure.map_apply hmeas (MeasurableSet.univ_pi fun i => hs (i, a)), hpick]
    unfold Muon.Foundations.stdGaussianPi
    rw [Measure.pi_pi]
  have hmt : ∀ sl ∈ Finset.univ.image (fun a : Fin B => ((τ, a) : ℤ × Fin B)),
      MeasurableSet (pick ⁻¹' (Set.univ.pi fun i => s (i, sl.2))) :=
    fun sl _ => hmeas (MeasurableSet.univ_pi fun i => hs (i, sl.2))
  rw [hpre, indepSpaceLaw, Measure.infinitePi_pi _ hmt, Finset.prod_image
    (fun x _ y _ hxy => (Prod.mk.inj hxy).2)]
  refine (Finset.prod_congr rfl fun a _ => hslot a).trans ?_
  rw [Fintype.prod_prod_type, Finset.prod_comm]

end NormIid


/-- `lem:app-vol-norm`, part (i), snapshot `cr-2026-10-23`. Declaration of record for this part:
under the size conditions, `Pr(𝓔^c) ≤ 4|𝒜| e^{-B}`. The certificate `hG` supplies `C_0`.
Verbatim LaTeX of the lemma (the whole statement is read in parts (i)–(iii)):
```latex
\begin{lemma}[Norm control]\label{lem:app-vol-norm}
Fix $(\ell,J,R)$. Let $Z_\alpha\defeq[z_{\alpha a}]_{a\le B}$ and
$W_\alpha\defeq[w_{\alpha a}]_{a\le B}$, let $C_0$ be the absolute constant of
\cite[Theorem~4.4.5]{vershynin2018high}, and put
$T_\star\defeq C_0(\sqrt{\gamma_\star}+2)$, $D_R\defeq RC_\Sigma T_\star^2$ and
$\mathcal E\defeq\{\norm{Z_\alpha},\norm{W_\alpha}\le T_\star\sqrt B\ \text{for all }\alpha\in\mathcal A\}$.
Under the size conditions, $\Pr(\mathcal E^c)\le4\abs{\mathcal A}e^{-B}$, on
$\mathcal E$ both $\norm{\mathsf K_1}$ and $\norm{\mathsf K_2}$ are at most $D_R$, and for
every $p\ge1$, $\EE[\norm{\mathsf K_l}^p\mathbf 1_{\mathcal E^c}]\to0$.
\end{lemma}
```
-/
theorem lem_app_vol_norm_i (hG : Muon.External.GaussianOpNorm) (ℓ J : ℕ) (γstar CSig : ℝ)
    (C : Covariances m n) (hS : SizeFin C B γstar CSig) (t : ℤ) :
    indepSpaceLaw m n B (cutoffEvent hG m n B ℓ J γstar t)ᶜ ≤
      ENNReal.ofReal (4 * ((Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card : ℝ) * Real.exp (-(B : ℝ))) := by
  have hspec := Classical.choose_spec hG.holds
  have hC0 : 0 < gaussOpConst hG := hspec.1
  obtain ⟨hmax, -, -⟩ := hS
  have hBnn : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  haveI : IsProbabilityMeasure (indepSpaceLaw m n B) := by
    unfold indepSpaceLaw
    infer_instance
  have hsq : ∀ d : ℕ, d ≤ max m n → Real.sqrt (d : ℝ) ≤ Real.sqrt γstar * Real.sqrt (B : ℝ) := by
    intro d hd
    have h1 : (d : ℝ) ≤ γstar * B := le_trans (Nat.cast_le.2 hd) hmax
    calc Real.sqrt (d : ℝ) ≤ Real.sqrt (γstar * B) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt γstar * Real.sqrt (B : ℝ) := Real.sqrt_mul' γstar hBnn
  have hbound : ∀ d : ℕ, d ≤ max m n →
      gaussOpConst hG * (Real.sqrt (d : ℝ) + Real.sqrt (B : ℝ) + Real.sqrt (B : ℝ)) ≤
        volTStar hG γstar * Real.sqrt (B : ℝ) := by
    intro d hd
    have h2 : Real.sqrt (d : ℝ) + Real.sqrt (B : ℝ) + Real.sqrt (B : ℝ) ≤
        (Real.sqrt γstar + 2) * Real.sqrt (B : ℝ) := by
      nlinarith [hsq d hd]
    calc gaussOpConst hG * (Real.sqrt (d : ℝ) + Real.sqrt (B : ℝ) + Real.sqrt (B : ℝ))
        ≤ gaussOpConst hG * ((Real.sqrt γstar + 2) * Real.sqrt (B : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hC0.le
      _ = volTStar hG γstar * Real.sqrt (B : ℝ) := by
          unfold volTStar
          ring
  -- one-block tail bound, from the certificate `hG`
  have htail : ∀ (p : ℕ) (Y : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Matrix (Fin p) (Fin B) ℝ),
      Muon.External.IsIIDGaussianMatrix (indepSpaceLaw m n B) Y →
      indepSpaceLaw m n B {ω | gaussOpConst hG *
          (Real.sqrt (p : ℝ) + Real.sqrt (B : ℝ) + Real.sqrt (B : ℝ)) <
            Muon.External.matOpNorm (Y ω)} ≤
        ENNReal.ofReal (2 * Real.exp (-(B : ℝ))) := by
    intro p Y hY
    have := hspec.2 p B (Real.sqrt (B : ℝ)) (Real.sqrt_nonneg _) _ (indepSpaceLaw m n B) Y hY
    rw [Real.sq_sqrt hBnn] at this
    exact this
  have hZ : ∀ α : ℤ, indepSpaceLaw m n B
      {ω | gaussOpConst hG * (Real.sqrt (m : ℝ) + Real.sqrt (B : ℝ) + Real.sqrt (B : ℝ)) <
        opNorm (cutoffZ t α ω)} ≤ ENNReal.ofReal (2 * Real.exp (-(B : ℝ))) := fun α =>
    htail m (cutoffZ t α) (nrm_iid_slot (t + 1 + α) (fun x : ℝ × (Vec m × Vec n) => x.2.1)
      (measurable_fst.comp measurable_snd) (nrm_pick_z m n))
  have hW : ∀ α : ℤ, indepSpaceLaw m n B
      {ω | gaussOpConst hG * (Real.sqrt (n : ℝ) + Real.sqrt (B : ℝ) + Real.sqrt (B : ℝ)) <
        opNorm (cutoffW t α ω)} ≤ ENNReal.ofReal (2 * Real.exp (-(B : ℝ))) := fun α =>
    htail n (cutoffW t α) (nrm_iid_slot (t + 1 + α) (fun x : ℝ × (Vec m × Vec n) => x.2.2)
      (measurable_snd.comp measurable_snd) (nrm_pick_w m n))
  have hsub : (cutoffEvent hG m n B ℓ J γstar t)ᶜ ⊆
      ⋃ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
        ({ω | gaussOpConst hG * (Real.sqrt (m : ℝ) + Real.sqrt (B : ℝ) + Real.sqrt (B : ℝ)) <
            opNorm (cutoffZ t α ω)} ∪
          {ω | gaussOpConst hG * (Real.sqrt (n : ℝ) + Real.sqrt (B : ℝ) + Real.sqrt (B : ℝ)) <
            opNorm (cutoffW t α ω)}) := by
    intro ω hω
    simp only [cutoffEvent, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_and_or,
      not_le, not_imp] at hω
    obtain ⟨α, hα, h⟩ := hω
    refine Set.mem_iUnion₂.2 ⟨α, hα, ?_⟩
    rcases h with h | h
    · exact Set.mem_union_left _ (lt_of_le_of_lt (hbound m (le_max_left m n)) h)
    · exact Set.mem_union_right _ (lt_of_le_of_lt (hbound n (le_max_right m n)) h)
  have h2 : (0 : ℝ) ≤ 2 * Real.exp (-(B : ℝ)) := by positivity
  have h4 : (0 : ℝ) ≤ 2 * Real.exp (-(B : ℝ)) + 2 * Real.exp (-(B : ℝ)) := by positivity
  have hfin : ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
      (ENNReal.ofReal (2 * Real.exp (-(B : ℝ))) + ENNReal.ofReal (2 * Real.exp (-(B : ℝ)))) =
        ENNReal.ofReal (4 * ((Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card : ℝ) * Real.exp (-(B : ℝ))) := by
    simp only [← ENNReal.ofReal_add h2 h2]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => h4), Finset.sum_const, nsmul_eq_mul]
    congr 1
    push_cast
    ring
  exact (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
    ((Finset.sum_le_sum fun α _ => (measure_union_le _ _).trans (add_le_add (hZ α) (hW α))).trans
      (le_of_eq hfin)))

/-- `lem:app-vol-norm`, part (ii), snapshot `cr-2026-10-23`. Declaration of record for this part:
on `𝓔`, both `‖K_1‖` and `‖K_2‖` are at most `D_R`. The statement is the lemma's second clause (the
same verbatim LaTeX as `lem_app_vol_norm_i`). -/
theorem lem_app_vol_norm_ii (hG : Muon.External.GaussianOpNorm) (Fp : FrozenParams m n B)
    (ℓ J : ℕ) (R γstar CSig : ℝ) (hR : 0 < R) (hS : SizeFin Fp.C B γstar CSig) (t : ℤ)
    (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (hω : ω ∈ cutoffEvent hG m n B ℓ J γstar t) :
    opNorm (cutoffMat Fp ℓ J R t 1 ω) ≤ volDR hG R CSig γstar ∧
      opNorm (cutoffMat Fp ℓ J R t 2 ω) ≤ volDR hG R CSig γstar := by
  set T := volTStar hG γstar with hT
  have hC0 : 0 < gaussOpConst hG := (Classical.choose_spec hG.holds).1
  have hT0 : 0 ≤ T := by
    rw [hT]
    unfold volTStar
    exact mul_nonneg hC0.le (by positivity)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  have hBnn : (0 : ℝ) ≤ B := hBpos.le
  have hSo : opNorm Fp.C.Sout ≤ CSig := hS.2.1
  have hSi : opNorm Fp.C.Sin ≤ CSig := hS.2.2
  have hCS0 : 0 ≤ CSig := (nrm_opNorm_nonneg _).trans hSo
  have hA : opNorm (rOut Fp.C) * opNorm (rOut Fp.C) = opNorm Fp.C.Sout :=
    nrm_opNorm_sqrt_mul_self _ Fp.C.psdOut
  have hBb : opNorm (rIn Fp.C) * opNorm (rIn Fp.C) = opNorm Fp.C.Sin :=
    nrm_opNorm_sqrt_mul_self _ Fp.C.psdIn
  have hab : opNorm (rOut Fp.C) * opNorm (rIn Fp.C) ≤ CSig := by
    nlinarith [sq_nonneg (opNorm (rOut Fp.C) - opNorm (rIn Fp.C)),
      nrm_opNorm_nonneg (rOut Fp.C), nrm_opNorm_nonneg (rIn Fp.C)]
  set X := T * Real.sqrt (B : ℝ) with hX
  have hX0 : 0 ≤ X := mul_nonneg hT0 (Real.sqrt_nonneg _)
  have hXX : X * X = T ^ 2 * B := by
    rw [hX]
    calc T * Real.sqrt B * (T * Real.sqrt B) = T ^ 2 * (Real.sqrt B * Real.sqrt B) := by ring
      _ = T ^ 2 * B := by rw [Real.mul_self_sqrt hBnn]
  have hω' : ∀ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
      opNorm (cutoffZ t α ω) ≤ X ∧ opNorm (cutoffW t α ω) ≤ X := hω
  have key : ∀ l : ℕ, (l = 1 ∨ l = 2) →
      opNorm (cutoffMat Fp ℓ J R t l ω) ≤ volDR hG R CSig γstar := by
    intro l hl
    have hterm : ∀ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
        opNorm (rOut Fp.C * (cutoffZ t α ω * Matrix.diagonal (fun a => treeVarpi Fp.β ℓ l α *
          (if |(ω (t + 1 + α, a)).1| ≤ R then (ω (t + 1 + α, a)).1 else 0)) *
            (cutoffW t α ω)ᵀ) * rIn Fp.C)
          ≤ (CSig * (X * R * X)) * |treeVarpi Fp.β ℓ l α| := by
      intro α hα
      obtain ⟨hZ, hW⟩ := hω' α hα
      have hc : ∀ a, |treeVarpi Fp.β ℓ l α *
          (if |(ω (t + 1 + α, a)).1| ≤ R then (ω (t + 1 + α, a)).1 else 0)| ≤
            |treeVarpi Fp.β ℓ l α| * R := by
        intro a
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (nrm_trunc_abs_le hR _) (abs_nonneg _)
      calc _ ≤ CSig * (X * (|treeVarpi Fp.β ℓ l α| * R) * X) :=
            nrm_block (rOut Fp.C) (rIn Fp.C) (cutoffZ t α ω) (cutoffW t α ω) _ X
              (|treeVarpi Fp.β ℓ l α| * R) CSig hX0 (mul_nonneg (abs_nonneg _) hR.le) hCS0
              hab hZ hW hc
        _ = (CSig * (X * R * X)) * |treeVarpi Fp.β ℓ l α| := by ring
    rw [nrm_cutoffMat_eq, nrm_opNorm_smul, abs_of_pos (inv_pos.2 hBpos)]
    refine le_trans (mul_le_mul_of_nonneg_left (nrm_opNorm_sum_le _ _) (inv_nonneg.2 hBnn)) ?_
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (inv_nonneg.2 hBnn)) ?_
    have hK0 : 0 ≤ CSig * (X * R * X) :=
      mul_nonneg hCS0 (mul_nonneg (mul_nonneg hX0 hR.le) hX0)
    have hsum := nrm_varpi_sum_le Fp.β Fp.hβ ℓ J l hl
    rw [← Finset.mul_sum]
    have h1 : CSig * (X * R * X) * ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ), |treeVarpi Fp.β ℓ l α|
        ≤ CSig * (X * R * X) := mul_le_of_le_one_right hK0 hsum
    refine le_trans (mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hBnn)) ?_
    have hval : (B : ℝ)⁻¹ * (CSig * (X * R * X)) = R * CSig * T ^ 2 := by
      have hXRX : X * R * X = R * (T ^ 2 * B) := by
        rw [← hXX]
        ring
      rw [hXRX]
      field_simp
    exact hval.le
  exact ⟨key 1 (Or.inl rfl), key 2 (Or.inr rfl)⟩

/-- Deterministic bound on the cutoff matrix: `‖K_l‖ ≤ C_Σ R B⁻¹ ∑_α (‖Z_α‖ + ‖W_α‖)²`, for every
sample `ω` (no event). Private helper for `lem_app_vol_norm_iii`. -/
private lemma nrm_K_det_bound {m n B : ℕ} (Fp : FrozenParams m n B) (ℓ J : ℕ) (R CSig : ℝ)
    (hR : 0 < R) (hab : opNorm (rOut Fp.C) * opNorm (rIn Fp.C) ≤ CSig) (hCS : 0 ≤ CSig)
    (t : ℤ) (l : ℕ) (hl : l = 1 ∨ l = 2) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) :
    opNorm (cutoffMat Fp ℓ J R t l ω) ≤
      CSig * R * ((B : ℝ))⁻¹ * ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
        (opNorm (cutoffZ t α ω) + opNorm (cutoffW t α ω)) ^ 2 := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  have hBnn : (0 : ℝ) ≤ B := hBpos.le
  have hϖ1 : ∀ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ), |treeVarpi Fp.β ℓ l α| ≤ 1 := fun α hα =>
    (Finset.single_le_sum (f := fun α => |treeVarpi Fp.β ℓ l α|)
      (fun _ _ => abs_nonneg _) hα).trans (nrm_varpi_sum_le Fp.β Fp.hβ ℓ J l hl)
  have hterm : ∀ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
      opNorm (rOut Fp.C * (cutoffZ t α ω * Matrix.diagonal (fun a => treeVarpi Fp.β ℓ l α *
        (if |(ω (t + 1 + α, a)).1| ≤ R then (ω (t + 1 + α, a)).1 else 0)) *
          (cutoffW t α ω)ᵀ) * rIn Fp.C)
        ≤ CSig * ((opNorm (cutoffZ t α ω) + opNorm (cutoffW t α ω)) * R *
          (opNorm (cutoffZ t α ω) + opNorm (cutoffW t α ω))) := by
    intro α hα
    have hX0 : 0 ≤ opNorm (cutoffZ t α ω) + opNorm (cutoffW t α ω) :=
      add_nonneg (nrm_opNorm_nonneg _) (nrm_opNorm_nonneg _)
    have hc : ∀ a, |treeVarpi Fp.β ℓ l α *
        (if |(ω (t + 1 + α, a)).1| ≤ R then (ω (t + 1 + α, a)).1 else 0)| ≤ R := by
      intro a
      rw [abs_mul]
      calc |treeVarpi Fp.β ℓ l α| * |if |(ω (t + 1 + α, a)).1| ≤ R then (ω (t + 1 + α, a)).1
            else 0| ≤ 1 * R := mul_le_mul (hϖ1 α hα) (nrm_trunc_abs_le hR _) (abs_nonneg _)
              zero_le_one
        _ = R := one_mul R
    exact nrm_block (rOut Fp.C) (rIn Fp.C) (cutoffZ t α ω) (cutoffW t α ω) _
      (opNorm (cutoffZ t α ω) + opNorm (cutoffW t α ω)) R CSig hX0 hR.le hCS hab
      (le_add_of_nonneg_right (nrm_opNorm_nonneg _))
      (le_add_of_nonneg_left (nrm_opNorm_nonneg _)) hc
  rw [nrm_cutoffMat_eq, nrm_opNorm_smul, abs_of_pos (inv_pos.2 hBpos)]
  refine le_trans (mul_le_mul_of_nonneg_left (nrm_opNorm_sum_le _ _) (inv_nonneg.2 hBnn)) ?_
  calc ((B : ℝ))⁻¹ * ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ), opNorm (rOut Fp.C * (cutoffZ t α ω *
        Matrix.diagonal (fun a => treeVarpi Fp.β ℓ l α *
          (if |(ω (t + 1 + α, a)).1| ≤ R then (ω (t + 1 + α, a)).1 else 0)) *
            (cutoffW t α ω)ᵀ) * rIn Fp.C)
      ≤ ((B : ℝ))⁻¹ * ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ), CSig *
          ((opNorm (cutoffZ t α ω) + opNorm (cutoffW t α ω)) * R *
            (opNorm (cutoffZ t α ω) + opNorm (cutoffW t α ω))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (inv_nonneg.2 hBnn)
    _ = CSig * R * ((B : ℝ))⁻¹ * ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
          (opNorm (cutoffZ t α ω) + opNorm (cutoffW t α ω)) ^ 2 := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        ring
















-- BEGIN P3 EXTRA
/-- Operator norm is at most the Frobenius norm. Private helper for `lem_app_vol_norm_iii`. -/
private lemma nrm_opNorm_le_fro {p q : ℕ} (K : Mat p q) : opNorm K ≤ fro K := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, fro, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have hK : ∀ i, ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)) x).ofLp i =
      ∑ j, K i j * x.ofLp j := fun i => by
    simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
  have hi : ∀ i, ‖∑ j, K i j * x.ofLp j‖ ^ 2 ≤
      (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) := by
    intro i
    calc ‖∑ j, K i j * x.ofLp j‖ ^ 2 ≤ (∑ j, ‖K i j‖ * ‖x.ofLp j‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
          exact norm_mul _ _
      _ ≤ (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ i, ‖((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)) x).ofLp i‖ ^ 2
      = ∑ i, ‖∑ j, K i j * x.ofLp j‖ ^ 2 := Finset.sum_congr rfl fun i _ => by rw [hK i]
    _ ≤ ∑ i, (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) := Finset.sum_le_sum fun i _ => hi i
    _ = (∑ i, ∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) := (Finset.sum_mul _ _ _).symm

/-- Finite Gaussian moments of every positive real order (private helper, `lem_app_vol_norm_iii`). -/
private lemma nrm_gauss_sq_rpow_lt_top (q : ℝ) (hq : 0 < q) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ^ q ∂(gaussianReal 0 1) < ⊤ := by
  have hf : MemLp (fun x : ℝ => x) (ENNReal.ofReal (2 * q)) (gaussianReal 0 1) :=
    memLp_id_gaussianReal' _ ENNReal.ofReal_ne_top
  have h2 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by simp; linarith) ENNReal.ofReal_ne_top hf.aestronglyMeasurable).1 hf.eLpNorm_lt_top
  rw [ENNReal.toReal_ofReal (by linarith)] at h2
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) h2
  have he : ‖x‖ₑ = ENNReal.ofReal |x| := Real.enorm_eq_ofReal_abs x
  rw [he, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg x) (by linarith),
    ENNReal.ofReal_rpow_of_nonneg (sq_nonneg x) hq.le]
  congr 1
  rw [← sq_abs x, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
  norm_num

/-- Jensen bound for a finite sum of squared coordinates with Gaussian marginals (private helper,
`lem_app_vol_norm_iii`). -/
private lemma nrm_gauss_jensen {Ω κ : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (I : Finset κ)
    (y : κ → Ω → ℝ) (hy : ∀ k, Measurable (y k))
    (hlaw : ∀ k ∈ I, μ.map (y k) = gaussianReal 0 1) (q : ℝ) (hq : 1 ≤ q) :
    ∫⁻ ω, (∑ k ∈ I, ENNReal.ofReal (y k ω ^ 2)) ^ q ∂μ ≤
      (I.card : ℝ≥0∞) ^ (q - 1) * ∑ k ∈ I, ∫⁻ x, ENNReal.ofReal (x ^ 2) ^ q ∂(gaussianReal 0 1) := by
  have hne : (I.card : ℝ≥0∞) ^ (q - 1) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) (ENNReal.natCast_ne_top _)
  calc ∫⁻ ω, (∑ k ∈ I, ENNReal.ofReal (y k ω ^ 2)) ^ q ∂μ
      ≤ ∫⁻ ω, (I.card : ℝ≥0∞) ^ (q - 1) * ∑ k ∈ I, ENNReal.ofReal (y k ω ^ 2) ^ q ∂μ :=
        lintegral_mono fun ω => ENNReal.rpow_sum_le_const_mul_sum_rpow I
          (fun k => ENNReal.ofReal (y k ω ^ 2)) hq
    _ = (I.card : ℝ≥0∞) ^ (q - 1) * ∑ k ∈ I, ∫⁻ ω, ENNReal.ofReal (y k ω ^ 2) ^ q ∂μ := by
        rw [lintegral_const_mul' _ _ hne, lintegral_finsetSum]
        intro k _
        exact ((((hy k).pow_const 2)).ennreal_ofReal).pow_const q
    _ = (I.card : ℝ≥0∞) ^ (q - 1) * ∑ k ∈ I, ∫⁻ x, ENNReal.ofReal (x ^ 2) ^ q
          ∂(gaussianReal 0 1) := by
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        have hF : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ 2) ^ q) :=
          (((measurable_id.pow_const 2)).ennreal_ofReal).pow_const q
        rw [← hlaw k hk, lintegral_map hF (hy k)]

/-- A single Gaussian coordinate of one slot is `N(0,1)` under the product model (private helper,
`lem_app_vol_norm_iii`). -/
private lemma nrm_coord_law_z (m n B : ℕ) (s : ℤ × Fin B) (i : Fin m) :
    (indepSpaceLaw m n B).map (fun ω => (ω s).2.1 i) = gaussianReal 0 1 := by
  have h1 : (indepSpaceLaw m n B).map (fun ω => ω s) = indepSlotLaw m n := by
    unfold indepSpaceLaw; exact Measure.infinitePi_map_eval _ s
  have h2 : (indepSlotLaw m n).map (fun x : ℝ × (Vec m × Vec n) => x.2.1 i) = gaussianReal 0 1 := by
    unfold indepSlotLaw
    rw [show (fun x : ℝ × (Vec m × Vec n) => x.2.1 i) =
        (fun v : Vec m => v i) ∘ Prod.fst ∘ Prod.snd from rfl,
      ← Measure.map_map (measurable_pi_apply i) (measurable_fst.comp measurable_snd),
      ← Measure.map_map measurable_fst measurable_snd, Measure.map_snd_prod, measure_univ, one_smul,
      Measure.map_fst_prod, measure_univ, one_smul]
    unfold Muon.Foundations.stdGaussianPi
    rw [Measure.pi_map_eval]
    simp [measure_univ]
  have hm : Measurable (fun x : ℝ × (Vec m × Vec n) => x.2.1 i) := by fun_prop
  calc (indepSpaceLaw m n B).map (fun ω => (ω s).2.1 i)
      = ((indepSpaceLaw m n B).map (fun ω => ω s)).map (fun x : ℝ × (Vec m × Vec n) => x.2.1 i) := by
        rw [Measure.map_map hm (measurable_pi_apply s)]; rfl
    _ = gaussianReal 0 1 := by rw [h1, h2]

/-- Same as `nrm_coord_law_z` for the `w` coordinates. -/
private lemma nrm_coord_law_w (m n B : ℕ) (s : ℤ × Fin B) (j : Fin n) :
    (indepSpaceLaw m n B).map (fun ω => (ω s).2.2 j) = gaussianReal 0 1 := by
  have h1 : (indepSpaceLaw m n B).map (fun ω => ω s) = indepSlotLaw m n := by
    unfold indepSpaceLaw; exact Measure.infinitePi_map_eval _ s
  have h2 : (indepSlotLaw m n).map (fun x : ℝ × (Vec m × Vec n) => x.2.2 j) = gaussianReal 0 1 := by
    unfold indepSlotLaw
    rw [show (fun x : ℝ × (Vec m × Vec n) => x.2.2 j) =
        (fun v : Vec n => v j) ∘ Prod.snd ∘ Prod.snd from rfl,
      ← Measure.map_map (measurable_pi_apply j) (measurable_snd.comp measurable_snd),
      ← Measure.map_map measurable_snd measurable_snd, Measure.map_snd_prod, measure_univ, one_smul,
      Measure.map_snd_prod, measure_univ, one_smul]
    unfold Muon.Foundations.stdGaussianPi
    rw [Measure.pi_map_eval]
    simp [measure_univ]
  have hm : Measurable (fun x : ℝ × (Vec m × Vec n) => x.2.2 j) := by fun_prop
  calc (indepSpaceLaw m n B).map (fun ω => (ω s).2.2 j)
      = ((indepSpaceLaw m n B).map (fun ω => ω s)).map (fun x : ℝ × (Vec m × Vec n) => x.2.2 j) := by
        rw [Measure.map_map hm (measurable_pi_apply s)]; rfl
    _ = gaussianReal 0 1 := by rw [h1, h2]

/-- Pointwise bound by squared Gaussian entries (private helper, `lem_app_vol_norm_iii`). -/
private lemma nrm_K_sq_bound {m n B : ℕ} (Fp : FrozenParams m n B) (ℓ J : ℕ) (R CSig : ℝ)
    (hR : 0 < R) (hab : opNorm (rOut Fp.C) * opNorm (rIn Fp.C) ≤ CSig) (hCS : 0 ≤ CSig)
    (t : ℤ) (l : ℕ) (hl : l = 1 ∨ l = 2) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) :
    opNorm (cutoffMat Fp ℓ J R t l ω) ≤
      2 * CSig * R * ((B : ℝ))⁻¹ * ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
        (∑ i, ∑ a, (ω (t + 1 + α, a)).2.1 i ^ 2 + ∑ j, ∑ a, (ω (t + 1 + α, a)).2.2 j ^ 2) := by
  have hBnn : (0 : ℝ) ≤ ((B : ℝ))⁻¹ := inv_nonneg.2 (Nat.cast_nonneg B)
  have hsq : ∀ {p : ℕ} (K : Mat p B), opNorm K ^ 2 ≤ ∑ i, ∑ a, K i a ^ 2 := by
    intro p K
    have h1 := nrm_opNorm_le_fro K
    have h0 := nrm_opNorm_nonneg K
    have hf : fro K ^ 2 = ∑ i, ∑ a, K i a ^ 2 := by
      unfold fro
      rw [Real.sq_sqrt (by positivity)]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by
        rw [Real.norm_eq_abs, sq_abs]
    rw [← hf]
    exact pow_le_pow_left₀ h0 h1 2
  have hα : ∀ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
      (opNorm (cutoffZ t α ω) + opNorm (cutoffW t α ω)) ^ 2 ≤
        2 * (∑ i, ∑ a, (ω (t + 1 + α, a)).2.1 i ^ 2 + ∑ j, ∑ a, (ω (t + 1 + α, a)).2.2 j ^ 2) := by
    intro α _
    have hz := hsq (cutoffZ t α ω)
    have hw := hsq (cutoffW t α ω)
    have hzz : ∑ i, ∑ a, cutoffZ t α ω i a ^ 2 = ∑ i, ∑ a, (ω (t + 1 + α, a)).2.1 i ^ 2 := rfl
    have hww : ∑ j, ∑ a, cutoffW t α ω j a ^ 2 = ∑ j, ∑ a, (ω (t + 1 + α, a)).2.2 j ^ 2 := rfl
    rw [hzz] at hz
    rw [hww] at hw
    nlinarith [sq_nonneg (opNorm (cutoffZ t α ω) - opNorm (cutoffW t α ω))]
  have hdet := nrm_K_det_bound Fp ℓ J R CSig hR hab hCS t l hl ω
  refine hdet.trans ?_
  have hsum : ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
      (opNorm (cutoffZ t α ω) + opNorm (cutoffW t α ω)) ^ 2 ≤
        ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
          2 * (∑ i, ∑ a, (ω (t + 1 + α, a)).2.1 i ^ 2 + ∑ j, ∑ a, (ω (t + 1 + α, a)).2.2 j ^ 2) :=
    Finset.sum_le_sum hα
  rw [← Finset.mul_sum] at hsum
  have hc : 0 ≤ CSig * R * ((B : ℝ))⁻¹ := mul_nonneg (mul_nonneg hCS hR.le) hBnn
  calc CSig * R * ((B : ℝ))⁻¹ * ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
        (opNorm (cutoffZ t α ω) + opNorm (cutoffW t α ω)) ^ 2
      ≤ CSig * R * ((B : ℝ))⁻¹ * (2 * ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
          (∑ i, ∑ a, (ω (t + 1 + α, a)).2.1 i ^ 2 + ∑ j, ∑ a, (ω (t + 1 + α, a)).2.2 j ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum hc
    _ = 2 * CSig * R * ((B : ℝ))⁻¹ * ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
        (∑ i, ∑ a, (ω (t + 1 + α, a)).2.1 i ^ 2 + ∑ j, ∑ a, (ω (t + 1 + α, a)).2.2 j ^ 2) := by
        ring

/-- Flattened Gaussian coordinates of the blocks `α ∈ 𝒜` (private helper, `lem_app_vol_norm_iii`). -/
private def nrmCoord (m n B : ℕ) (t : ℤ) (k : ℤ × Fin B × (Fin m ⊕ Fin n))
    (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) : ℝ :=
  Sum.elim (fun i : Fin m => (ω (t + 1 + k.1, k.2.1)).2.1 i)
    (fun j : Fin n => (ω (t + 1 + k.1, k.2.1)).2.2 j) k.2.2

private lemma nrm_coord_sum_eq {m n B : ℕ} (t : ℤ) (J ℓ : ℕ)
    (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) :
    ∑ k ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ) ×ˢ (Finset.univ : Finset (Fin B × (Fin m ⊕ Fin n))),
        nrmCoord m n B t (k.1, k.2) ω ^ 2 =
      ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
        (∑ i, ∑ a, (ω (t + 1 + α, a)).2.1 i ^ 2 + ∑ j, ∑ a, (ω (t + 1 + α, a)).2.2 j ^ 2) := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, nrmCoord, Sum.elim_inl,
    Sum.elim_inr, Finset.sum_add_distrib]
  congr 1 <;> exact Finset.sum_comm

/-- Moment bound for the squared Gaussian block sum (private helper, `lem_app_vol_norm_iii`). -/
private lemma nrm_block_moment (m n B : ℕ) (t : ℤ) (J ℓ : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal ((∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
        (∑ i, ∑ a, (ω (t + 1 + α, a)).2.1 i ^ 2 + ∑ j, ∑ a, (ω (t + 1 + α, a)).2.2 j ^ 2)) ^ q)
      ∂(indepSpaceLaw m n B) ≤
    ((Finset.Icc (-(J : ℤ)) (ℓ : ℤ) ×ˢ (Finset.univ : Finset (Fin B × (Fin m ⊕ Fin n)))).card :
        ℝ≥0∞) ^ (q - 1) *
      ((Finset.Icc (-(J : ℤ)) (ℓ : ℤ) ×ˢ (Finset.univ : Finset (Fin B × (Fin m ⊕ Fin n)))).card *
        ∫⁻ x, ENNReal.ofReal (x ^ 2) ^ q ∂(gaussianReal 0 1)) := by
  set I := Finset.Icc (-(J : ℤ)) (ℓ : ℤ) ×ˢ (Finset.univ : Finset (Fin B × (Fin m ⊕ Fin n)))
    with hI
  have hnn : ∀ ω, 0 ≤ ∑ k ∈ I, nrmCoord m n B t k ω ^ 2 := fun ω =>
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hpt : ∀ ω, ENNReal.ofReal ((∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
        (∑ i, ∑ a, (ω (t + 1 + α, a)).2.1 i ^ 2 + ∑ j, ∑ a, (ω (t + 1 + α, a)).2.2 j ^ 2)) ^ q) =
      (∑ k ∈ I, ENNReal.ofReal (nrmCoord m n B t k ω ^ 2)) ^ q := by
    intro ω
    rw [← nrm_coord_sum_eq t J ℓ ω, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (hnn ω) (by linarith)]
  simp only [hpt]
  have hy : ∀ k : ℤ × (Fin B × (Fin m ⊕ Fin n)), Measurable (fun ω => nrmCoord m n B t k ω) := by
    rintro ⟨α, a, s | j⟩
    · simp only [nrmCoord, Sum.elim_inl]
      fun_prop
    · simp only [nrmCoord, Sum.elim_inr]
      fun_prop
  have hlaw : ∀ k ∈ I, (indepSpaceLaw m n B).map (fun ω => nrmCoord m n B t k ω) =
      gaussianReal 0 1 := by
    rintro ⟨α, a, s | j⟩ _
    · simp only [nrmCoord, Sum.elim_inl]
      exact nrm_coord_law_z m n B (t + 1 + α, a) _
    · simp only [nrmCoord, Sum.elim_inr]
      exact nrm_coord_law_w m n B (t + 1 + α, a) _
  have hJ := nrm_gauss_jensen (indepSpaceLaw m n B) I (fun k ω => nrmCoord m n B t k ω) hy hlaw q hq
  refine hJ.trans (le_of_eq ?_)
  congr 1
  rw [Finset.sum_const, nsmul_eq_mul]
/-- AM-GM tail split (private helper, `lem_app_vol_norm_iii`). -/
private lemma nrm_tail_split {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (E : Set Ω) (p : ℝ) (hp : 0 < p) (lam : ℝ) (hlam : 0 < lam) :
    ∫⁻ ω in E, ENNReal.ofReal (X ω ^ p) ∂μ ≤
      ENNReal.ofReal lam * ∫⁻ ω, ENNReal.ofReal (X ω ^ (2 * p)) ∂μ +
        ENNReal.ofReal (1 / (4 * lam)) * μ E := by
  have hpt : ∀ ω, ENNReal.ofReal (X ω ^ p) ≤
      ENNReal.ofReal lam * ENNReal.ofReal (X ω ^ (2 * p)) + ENNReal.ofReal (1 / (4 * lam)) := by
    intro ω
    have hy : 0 ≤ X ω ^ p := Real.rpow_nonneg (hX ω) p
    have h2 : X ω ^ (2 * p) = (X ω ^ p) ^ 2 := by
      rw [mul_comm, Real.rpow_mul (hX ω)]; norm_cast
    rw [h2, ← ENNReal.ofReal_mul hlam.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ (lam * X ω ^ p - 1 / 2) ^ 2 := sq_nonneg _
    have e : lam * (X ω ^ p) ^ 2 + 1 / (4 * lam) - X ω ^ p =
        (lam * X ω ^ p - 1 / 2) ^ 2 / lam := by field_simp; ring
    have : 0 ≤ (lam * X ω ^ p - 1 / 2) ^ 2 / lam := by positivity
    linarith
  calc ∫⁻ ω in E, ENNReal.ofReal (X ω ^ p) ∂μ
      ≤ ∫⁻ ω in E, (ENNReal.ofReal lam * ENNReal.ofReal (X ω ^ (2 * p)) +
          ENNReal.ofReal (1 / (4 * lam))) ∂μ := lintegral_mono hpt
    _ = ∫⁻ ω in E, ENNReal.ofReal lam * ENNReal.ofReal (X ω ^ (2 * p)) ∂μ +
          ENNReal.ofReal (1 / (4 * lam)) * μ E := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have := setLIntegral_le_lintegral (μ := μ) E (fun ω => ENNReal.ofReal (X ω ^ (2 * p)))
        gcongr

/-- Pointwise domination of the `2p`-th moment (private helper, `lem_app_vol_norm_iii`). -/
private lemma nrm_moment_dom {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X S : Ω → ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (hS : ∀ ω, 0 ≤ S ω) (c : ℝ) (hc : 0 ≤ c) (hXS : ∀ ω, X ω ≤ c * S ω) (q : ℝ) (hq : 0 < q) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ q) ∂μ ≤
      ENNReal.ofReal (c ^ q) * ∫⁻ ω, ENNReal.ofReal (S ω ^ q) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hc q)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.mul_rpow hc (hS ω)]
  exact Real.rpow_le_rpow (hX ω) (hXS ω) hq.le
/-- Real form of the block moment bound (private helper, `lem_app_vol_norm_iii`). -/
private lemma nrm_block_moment_real (m n B : ℕ) (t : ℤ) (J ℓ : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal ((∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
        (∑ i, ∑ a, (ω (t + 1 + α, a)).2.1 i ^ 2 + ∑ j, ∑ a, (ω (t + 1 + α, a)).2.2 j ^ 2)) ^ q)
      ∂(indepSpaceLaw m n B) ≤
    ENNReal.ofReal ((((Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card * (B * (m + n)) : ℕ) : ℝ) ^ q *
      (∫⁻ x, ENNReal.ofReal (x ^ 2) ^ q ∂(gaussianReal 0 1)).toReal) := by
  refine (nrm_block_moment m n B t J ℓ q hq).trans (le_of_eq ?_)
  set G := ∫⁻ x, ENNReal.ofReal (x ^ 2) ^ q ∂(gaussianReal 0 1) with hGdef
  have hG : G ≠ ⊤ := (nrm_gauss_sq_rpow_lt_top q (by linarith)).ne
  have hcard : ((Finset.Icc (-(J : ℤ)) (ℓ : ℤ) ×ˢ
      (Finset.univ : Finset (Fin B × (Fin m ⊕ Fin n)))).card : ℕ) =
      (Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card * (B * (m + n)) := by
    rw [Finset.card_product]
    simp [Fintype.card_prod, Fintype.card_sum]
  rw [hcard]
  set Nn : ℕ := (Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card * (B * (m + n)) with hNn
  have hN0 : (0 : ℝ) ≤ (Nn : ℝ) := Nat.cast_nonneg _
  have e1 : ((Nn : ℕ) : ℝ≥0∞) = ENNReal.ofReal (Nn : ℝ) := (ENNReal.ofReal_natCast Nn).symm
  have e2 : ((Nn : ℕ) : ℝ≥0∞) ^ (q - 1) = ENNReal.ofReal ((Nn : ℝ) ^ (q - 1)) := by
    rw [e1, ENNReal.ofReal_rpow_of_nonneg hN0 (by linarith)]
  have e3 : G = ENNReal.ofReal G.toReal := (ENNReal.ofReal_toReal hG).symm
  rw [e2, e1]
  conv_lhs => rw [e3]
  rw [← ENNReal.ofReal_mul hN0, ← ENNReal.ofReal_mul (Real.rpow_nonneg hN0 _)]
  congr 1
  have : (Nn : ℝ) ^ (q - 1) * (Nn : ℝ) = (Nn : ℝ) ^ q := by
    have := Real.rpow_add' hN0 (show q - 1 + 1 ≠ 0 by linarith) (x := (Nn : ℝ))
    rw [Real.rpow_one] at this
    rw [← this]; congr 1; ring
  rw [← mul_assoc, this]
/-- Quantitative tail moment bound (private helper, `lem_app_vol_norm_iii`). -/
private lemma nrm_tail_bound (hG : Muon.External.GaussianOpNorm) {m n B : ℕ}
    (Fp : FrozenParams m n B) (ℓ J : ℕ) (R γstar CSig : ℝ)
    (hR : 0 < R) (hS : SizeFin Fp.C B γstar CSig) (t : ℤ) (l : ℕ) (hl : l = 1 ∨ l = 2)
    (p : ℝ) (hp : 1 ≤ p) :
    ∫⁻ ω in (cutoffEvent hG m n B ℓ J γstar t)ᶜ,
        ENNReal.ofReal (opNorm (cutoffMat Fp ℓ J R t l ω) ^ p) ∂(indepSpaceLaw m n B) ≤
      ENNReal.ofReal (Real.exp (-((B : ℝ) / 2)) *
        ((4 * CSig * R * ((Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card : ℝ) * γstar * B) ^ (2 * p) *
          (∫⁻ x, ENNReal.ofReal (x ^ 2) ^ (2 * p) ∂(gaussianReal 0 1)).toReal +
          ((Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card : ℝ))) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  have hSo : opNorm Fp.C.Sout ≤ CSig := hS.2.1
  have hSi : opNorm Fp.C.Sin ≤ CSig := hS.2.2
  have hCS0 : 0 ≤ CSig := (nrm_opNorm_nonneg _).trans hSo
  have hA : opNorm (rOut Fp.C) * opNorm (rOut Fp.C) = opNorm Fp.C.Sout :=
    nrm_opNorm_sqrt_mul_self _ Fp.C.psdOut
  have hBb : opNorm (rIn Fp.C) * opNorm (rIn Fp.C) = opNorm Fp.C.Sin :=
    nrm_opNorm_sqrt_mul_self _ Fp.C.psdIn
  have hab : opNorm (rOut Fp.C) * opNorm (rIn Fp.C) ≤ CSig := by
    nlinarith [sq_nonneg (opNorm (rOut Fp.C) - opNorm (rIn Fp.C)),
      nrm_opNorm_nonneg (rOut Fp.C), nrm_opNorm_nonneg (rIn Fp.C)]
  have hγ : 0 ≤ γstar := by
    have := hS.1
    have h0 : (0 : ℝ) ≤ ((max m n : ℕ) : ℝ) := Nat.cast_nonneg _
    by_contra h
    push Not at h
    nlinarith
  set A : ℝ := ((Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card : ℝ) with hAdef
  have hA0 : 0 ≤ A := Nat.cast_nonneg _
  set lam : ℝ := Real.exp (-((B : ℝ) / 2)) with hlam
  have hlam0 : 0 < lam := Real.exp_pos _
  set q : ℝ := 2 * p with hq
  have hq1 : 1 ≤ q := by rw [hq]; linarith
  set c' : ℝ := 2 * CSig * R * ((B : ℝ))⁻¹ with hc'
  have hc'0 : 0 ≤ c' := by rw [hc']; positivity
  set X : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → ℝ := fun ω => opNorm (cutoffMat Fp ℓ J R t l ω)
    with hX
  set Sf : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → ℝ := fun ω => ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ),
        (∑ i, ∑ a, (ω (t + 1 + α, a)).2.1 i ^ 2 + ∑ j, ∑ a, (ω (t + 1 + α, a)).2.2 j ^ 2)
    with hSf
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => nrm_opNorm_nonneg _
  have hSf0 : ∀ ω, 0 ≤ Sf ω := fun ω => Finset.sum_nonneg fun α _ =>
    add_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _)
      (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun a _ => sq_nonneg _)
  have hXS : ∀ ω, X ω ≤ c' * Sf ω := fun ω =>
    nrm_K_sq_bound Fp ℓ J R CSig hR hab hCS0 t l hl ω
  have h1 := nrm_tail_split (indepSpaceLaw m n B) X hX0 (cutoffEvent hG m n B ℓ J γstar t)ᶜ p
    (by linarith) lam hlam0
  have h2 := nrm_moment_dom (indepSpaceLaw m n B) X Sf hX0 hSf0 c' hc'0 hXS q (by linarith)
  have h3 := nrm_block_moment_real m n B t J ℓ q hq1
  have h4 := lem_app_vol_norm_i hG ℓ J γstar CSig Fp.C hS t
  set G' : ℝ := (∫⁻ x, ENNReal.ofReal (x ^ 2) ^ q ∂(gaussianReal 0 1)).toReal with hG'
  have hG'0 : 0 ≤ G' := ENNReal.toReal_nonneg
  set Nr : ℝ := (((Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card * (B * (m + n)) : ℕ) : ℝ) with hNr
  have hNr0 : 0 ≤ Nr := Nat.cast_nonneg _
  have hcN : c' * Nr ≤ 4 * CSig * R * A * γstar * B := by
    have hmn : ((m : ℝ) + n) ≤ 2 * (γstar * B) := by
      have h := hS.1
      have hm : (m : ℝ) ≤ ((max m n : ℕ) : ℝ) := by exact_mod_cast le_max_left m n
      have hn : (n : ℝ) ≤ ((max m n : ℕ) : ℝ) := by exact_mod_cast le_max_right m n
      linarith
    have hNr' : Nr = A * (B * ((m : ℝ) + n)) := by rw [hNr, hAdef]; push_cast; ring
    rw [hNr', hc']
    have : 2 * CSig * R * (B : ℝ)⁻¹ * (A * (B * ((m : ℝ) + n))) = 2 * CSig * R * A * ((m : ℝ) + n) := by
      field_simp
    rw [this]
    have h2CR : 0 ≤ 2 * CSig * R * A := by positivity
    calc 2 * CSig * R * A * ((m : ℝ) + n) ≤ 2 * CSig * R * A * (2 * (γstar * B)) :=
          mul_le_mul_of_nonneg_left hmn h2CR
      _ = 4 * CSig * R * A * γstar * B := by ring
  have hlast : ENNReal.ofReal lam * (ENNReal.ofReal (c' ^ q) * ENNReal.ofReal (Nr ^ q * G')) ≤
      ENNReal.ofReal (lam * ((4 * CSig * R * A * γstar * B) ^ q * G')) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hc'0 q), ← ENNReal.ofReal_mul hlam0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have : c' ^ q * (Nr ^ q * G') = (c' * Nr) ^ q * G' := by
      rw [Real.mul_rpow hc'0 hNr0]; ring
    rw [this]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hG'0) hlam0.le
    exact Real.rpow_le_rpow (mul_nonneg hc'0 hNr0) hcN (by linarith)
  have hexp : 1 / (4 * lam) * (4 * A * Real.exp (-(B : ℝ))) = A * lam := by
    have : Real.exp (-(B : ℝ)) = lam * lam := by
      rw [hlam, ← Real.exp_add]; congr 1; ring
    rw [this]; field_simp
  calc _ ≤ _ := h1
    _ ≤ ENNReal.ofReal lam * (ENNReal.ofReal (c' ^ q) * ENNReal.ofReal (Nr ^ q * G')) +
        ENNReal.ofReal (1 / (4 * lam)) * ENNReal.ofReal (4 * A * Real.exp (-(B : ℝ))) := by
        gcongr
        exact h2.trans (by gcongr)
    _ ≤ ENNReal.ofReal (lam * ((4 * CSig * R * A * γstar * B) ^ q * G')) +
        ENNReal.ofReal (A * lam) := by
        refine add_le_add hlast (le_of_eq ?_)
        rw [← ENNReal.ofReal_mul (by positivity), hexp]
    _ = ENNReal.ofReal (lam * ((4 * CSig * R * A * γstar * B) ^ q * G' + A)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
-- END P3 EXTRA

/-- `lem:app-vol-norm`, part (iii), snapshot `cr-2026-10-23`. Declaration of record for this part:
along a sequence of dimensions with `B_k → ∞` and the size conditions at every index, and for every
`p ≥ 1`, `𝔼[‖K_l‖^p 1_{𝓔^c}] → 0`, read as the lower integral over `𝓔^c`. The sequence is the
reading of the source's unqualified "→ 0" (see the module note). -/
theorem lem_app_vol_norm_iii (hG : Muon.External.GaussianOpNorm) (ℓ J : ℕ) (R γstar CSig : ℝ)
    (hR : 0 < R) (mm nn BB : ℕ → ℕ) (Fp : ∀ k, FrozenParams (mm k) (nn k) (BB k))
    (hB : Tendsto BB atTop atTop) (hS : ∀ k, SizeFin (Fp k).C (BB k) γstar CSig)
    (t : ℤ) (l : ℕ) (hl : l = 1 ∨ l = 2) (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun k => ∫⁻ ω in (cutoffEvent hG (mm k) (nn k) (BB k) ℓ J γstar t)ᶜ,
        ENNReal.ofReal (opNorm (cutoffMat (Fp k) ℓ J R t l ω) ^ p)
          ∂(indepSpaceLaw (mm k) (nn k) (BB k)))
      atTop (𝓝 0) := by
  set A : ℝ := ((Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card : ℝ) with hAdef
  set K1 : ℝ := 4 * CSig * R * A * γstar with hK1
  set G' : ℝ := (∫⁻ x, ENNReal.ofReal (x ^ 2) ^ (2 * p) ∂(gaussianReal 0 1)).toReal with hG'
  have hCS0 : ∀ k, 0 ≤ CSig := fun k =>
    (nrm_opNorm_nonneg _).trans (hS k).2.1
  have hBpos : ∀ k, (0 : ℝ) < BB k := fun k => by exact_mod_cast (Fp k).hB
  have hγ0 : 0 ≤ γstar := by
    have h1 := (hS 0).1
    have h0 : (0 : ℝ) ≤ ((max (mm 0) (nn 0) : ℕ) : ℝ) := Nat.cast_nonneg _
    by_contra h
    push Not at h
    nlinarith [hBpos 0]
  have hK10 : 0 ≤ K1 := by
    have := hCS0 0
    positivity
  have hq : 0 < 2 * p := by linarith
  -- the real function tends to zero
  have hreal : Tendsto (fun x : ℝ => Real.exp (-(x / 2)) * ((K1 * x) ^ (2 * p) * G' + A))
      atTop (𝓝 0) := by
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * p) (1 / 2) (by norm_num)
    have h2 : Tendsto (fun x : ℝ => Real.exp (-(1 / 2) * x)) atTop (𝓝 0) := by
      have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1 / 2) (by norm_num)
      simpa using this
    have h3 := (h1.const_mul (K1 ^ (2 * p) * G')).add (h2.const_mul A)
    simp only [mul_zero, add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.mul_rpow hK10 hx]
    have : -(x / 2) = -(1 / 2) * x := by ring
    rw [this]
    ring
  have hseq : Tendsto (fun k => Real.exp (-((BB k : ℝ) / 2)) *
      ((K1 * (BB k : ℝ)) ^ (2 * p) * G' + A)) atTop (𝓝 0) :=
    hreal.comp (tendsto_natCast_atTop_atTop.comp hB)
  have hseq' : Tendsto (fun k => ENNReal.ofReal (Real.exp (-((BB k : ℝ) / 2)) *
      ((K1 * (BB k : ℝ)) ^ (2 * p) * G' + A))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hseq
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hseq' (fun _ => bot_le)
    (fun k => ?_)
  exact nrm_tail_bound hG (Fp k) ℓ J R γstar CSig hR (hS k) t l hl p hp

/-! ## Removal of the cutoffs -/

private lemma tc4_rOut_symm (C : Covariances m n) : (rOut C)ᵀ = rOut C := by
  have h : (CFC.sqrt C.Sout)ᴴ = CFC.sqrt C.Sout :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sout)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma tc4_rIn_symm (C : Covariances m n) : (rIn C)ᵀ = rIn C := by
  have h : (CFC.sqrt C.Sin)ᴴ = CFC.sqrt C.Sin :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma tc4_rOut_mul (C : Covariances m n) : rOut C * rOut C = C.Sout :=
  CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)

private lemma tc4_rIn_mul (C : Covariances m n) : rIn C * rIn C = C.Sin :=
  CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)

private lemma tc4_sq_coord_integrable (k : ℕ) (i : Fin k) :
    Integrable (fun z : Vec k => z i ^ 2) (Muon.Foundations.stdGaussianPi k) := by
  have hm : MeasurePreserving (fun z : Vec k => z i) (Muon.Foundations.stdGaussianPi k)
      (gaussianReal 0 1) := measurePreserving_eval _ i
  exact (hm.integrable_comp (g := fun x : ℝ => x ^ 2) (by fun_prop)).2
    (Muon.Foundations.gaussian_integrable_pow 2)

private lemma tc4_coord_mul_integrable (k : ℕ) (i j : Fin k) :
    Integrable (fun z : Vec k => z i * z j) (Muon.Foundations.stdGaussianPi k) := by
  refine ((((tc4_sq_coord_integrable k i).add (tc4_sq_coord_integrable k j)).div_const 2)).mono'
    (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun z => ?_)
  show ‖z i * z j‖ ≤ (z i ^ 2 + z j ^ 2) / 2
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|z i| - |z j|), sq_abs (z i), sq_abs (z j)]

private lemma tc4_zz (k : ℕ) (L : Matrix (Fin k) (Fin k) ℝ) (b a : Fin k) :
    Integrable (fun z : Vec k => L.mulVec z b * L.mulVec z a) (Muon.Foundations.stdGaussianPi k) ∧
    ∫ z : Vec k, L.mulVec z b * L.mulVec z a ∂(Muon.Foundations.stdGaussianPi k)
      = (L * Lᵀ) b a := by
  have e : ∀ z : Vec k, L.mulVec z b * L.mulVec z a =
      ∑ i, ∑ j, (L b i * L a j) * (z i * z j) := by
    intro z
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∀ z : Vec k, L.mulVec z b * L.mulVec z a =
      ∑ i, ∑ j, z i * (Matrix.of fun i j => L b i * L a j) i j * z j := by
    intro z
    rw [e z]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      simp only [Matrix.of_apply]; ring
  refine ⟨?_, ?_⟩
  · simp_rw [e]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (tc4_coord_mul_integrable k i j).const_mul _
  · simp_rw [e2]
    rw [Muon.Foundations.stdGaussianPi_quadratic_mean k]
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]

/-- Single-slot second moment with a general odd-type scalar factor `q(g)`. -/
private lemma tc4_slot (F : FrozenParams m n B) (q : ℝ → ℝ) (hqm : Measurable q)
    (hql : ∀ x, |q x| ≤ |x|) (b : Fin m) (c : Fin n) :
    Integrable (fun x : ℝ × (Vec m × Vec n) =>
      (q x.1 * ((rOut F.C).mulVec x.2.1 b * (rIn F.C).mulVec x.2.2 c)) *
        (q x.1 * ((rOut F.C).mulVec x.2.1 b * (rIn F.C).mulVec x.2.2 c))) (indepSlotLaw m n) ∧
    ∫ x : ℝ × (Vec m × Vec n),
      (q x.1 * ((rOut F.C).mulVec x.2.1 b * (rIn F.C).mulVec x.2.2 c)) *
        (q x.1 * ((rOut F.C).mulVec x.2.1 b * (rIn F.C).mulVec x.2.2 c)) ∂(indepSlotLaw m n)
      = (∫ x, q x ^ 2 ∂(gaussianReal 0 1)) * (F.C.Sout b b * F.C.Sin c c) := by
  have hfun : (fun x : ℝ × (Vec m × Vec n) =>
      (q x.1 * ((rOut F.C).mulVec x.2.1 b * (rIn F.C).mulVec x.2.2 c)) *
        (q x.1 * ((rOut F.C).mulVec x.2.1 b * (rIn F.C).mulVec x.2.2 c))) =
      fun x => q x.1 ^ 2 * (((rOut F.C).mulVec x.2.1 b * (rOut F.C).mulVec x.2.1 b) *
        ((rIn F.C).mulVec x.2.2 c * (rIn F.C).mulVec x.2.2 c)) := by
    funext x; ring
  rw [hfun]
  have h1 := tc4_zz m (rOut F.C) b b
  have h2 := tc4_zz n (rIn F.C) c c
  have hg2 : Integrable (fun x : ℝ => q x ^ 2) (gaussianReal 0 1) := by
    refine (Muon.Foundations.gaussian_integrable_pow 2).mono' (hqm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    show ‖q x ^ 2‖ ≤ x ^ 2
    rw [Real.norm_eq_abs, abs_pow]
    calc |q x| ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hql x) 2
      _ = x ^ 2 := sq_abs x
  refine ⟨hg2.mul_prod (h1.1.mul_prod h2.1), ?_⟩
  rw [integral_prod_mul (f := fun x : ℝ => q x ^ 2)
    (g := fun q' : Vec m × Vec n =>
      ((rOut F.C).mulVec q'.1 b * (rOut F.C).mulVec q'.1 b) *
        ((rIn F.C).mulVec q'.2 c * (rIn F.C).mulVec q'.2 c)),
    integral_prod_mul (f := fun z : Vec m => (rOut F.C).mulVec z b * (rOut F.C).mulVec z b)
      (g := fun w : Vec n => (rIn F.C).mulVec w c * (rIn F.C).mulVec w c), h1.2, h2.2]
  have e1 : (rOut F.C * (rOut F.C)ᵀ) b b = F.C.Sout b b := by
    rw [tc4_rOut_symm, tc4_rOut_mul]
  have e2 : (rIn F.C * (rIn F.C)ᵀ) c c = F.C.Sin c c := by
    rw [tc4_rIn_symm, tc4_rIn_mul]
  rw [e1, e2]

private lemma tc4_diag (F : FrozenParams m n B) (q : ℝ → ℝ) (hqm : Measurable q)
    (hql : ∀ x, |q x| ≤ |x|) (p : ℤ × Fin B) (b : Fin m) (c : Fin n) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      (q (ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c)) *
        (q (ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c)))
      (indepSpaceLaw m n B) ∧
    ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      (q (ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c)) *
        (q (ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c))
      ∂(indepSpaceLaw m n B) = (∫ x, q x ^ 2 ∂(gaussianReal 0 1)) * (F.C.Sout b b * F.C.Sin c c) := by
  have hm : MeasurePreserving (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω p)
      (indepSpaceLaw m n B) (indepSlotLaw m n) :=
    ⟨measurable_pi_apply p, by unfold indepSpaceLaw; exact Measure.infinitePi_map_eval _ p⟩
  obtain ⟨h1, h2⟩ := tc4_slot F q hqm hql b c
  refine ⟨hm.integrable_comp_of_integrable h1, ?_⟩
  have h1' := h1.aestronglyMeasurable
  rw [← hm.map_eq] at h1'
  have h3 := integral_map (μ := indepSpaceLaw m n B) hm.measurable.aemeasurable h1'
  rw [hm.map_eq] at h3
  exact h3.symm.trans h2

private lemma tc4_flip_slot (p : ℤ × Fin B) :
    MeasurePreserving (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      fun i => if i = p then (-(ω i).1, (ω i).2) else ω i)
      (indepSpaceLaw m n B) (indepSpaceLaw m n B) := by
  classical
  have hmeasS : Measurable (fun x : ℝ × (Vec m × Vec n) => (-x.1, x.2)) := by fun_prop
  have hS : MeasurePreserving (fun x : ℝ × (Vec m × Vec n) => (-x.1, x.2))
      (indepSlotLaw m n) (indepSlotLaw m n) := by
    have hg : MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 1) (gaussianReal 0 1) :=
      ⟨measurable_neg, by rw [gaussianReal_map_neg, neg_zero]⟩
    exact hg.prod (MeasurePreserving.id _)
  have hmeas : ∀ i : ℤ × Fin B, Measurable (fun x : ℝ × (Vec m × Vec n) =>
      if i = p then (-x.1, x.2) else x) := fun i => by
    by_cases h : i = p
    · simpa [h] using hmeasS
    · simp only [h, ite_false]; exact measurable_id
  have hmap := Measure.infinitePi_map_pi (μ := fun _ : ℤ × Fin B => indepSlotLaw m n)
    (f := fun i x => if i = p then (-x.1, x.2) else x) hmeas
  have hmapi : ∀ i : ℤ × Fin B, (indepSlotLaw m n).map (fun x : ℝ × (Vec m × Vec n) =>
      if i = p then (-x.1, x.2) else x) = indepSlotLaw m n := fun i => by
    by_cases h : i = p
    · simpa [h] using hS.map_eq
    · simp [h]
  simp only [hmapi] at hmap
  refine ⟨measurable_pi_iff.2 fun i => (hmeas i).comp (measurable_pi_apply i), ?_⟩
  unfold indepSpaceLaw
  exact hmap

private lemma tc4_hh_meas (F : FrozenParams m n B) (q : ℝ → ℝ) (hqm : Measurable q)
    (p : ℤ × Fin B) (b : Fin m) (c : Fin n) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      q (ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c)) := by
  simp only [Matrix.mulVec, dotProduct]
  have : Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => (ω p).1) := by fun_prop
  exact (hqm.comp this).mul (by fun_prop)

private lemma tc4_cross (F : FrozenParams m n B) (q q' : ℝ → ℝ) (hqm : Measurable q)
    (hql : ∀ x, |q x| ≤ |x|) (hqo : ∀ x, q (-x) = - q x)
    (hqm' : Measurable q') (hql' : ∀ x, |q' x| ≤ |x|)
    {p r : ℤ × Fin B} (hpr : p ≠ r) (b : Fin m) (c : Fin n) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      (q (ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c)) *
        (q' (ω r).1 * ((rOut F.C).mulVec (ω r).2.1 b * (rIn F.C).mulVec (ω r).2.2 c)))
      (indepSpaceLaw m n B) ∧
    ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      (q (ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c)) *
        (q' (ω r).1 * ((rOut F.C).mulVec (ω r).2.1 b * (rIn F.C).mulVec (ω r).2.2 c))
      ∂(indepSpaceLaw m n B) = 0 := by
  classical
  set U : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → ℝ := fun ω =>
    q (ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c) with hU
  set V : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → ℝ := fun ω =>
    q' (ω r).1 * ((rOut F.C).mulVec (ω r).2.1 b * (rIn F.C).mulVec (ω r).2.2 c) with hV
  have hUm : Measurable U := tc4_hh_meas F q hqm p b c
  have hVm : Measurable V := tc4_hh_meas F q' hqm' r b c
  have hUU : Integrable (fun ω => U ω * U ω) (indepSpaceLaw m n B) :=
    (tc4_diag F q hqm hql p b c).1
  have hVV : Integrable (fun ω => V ω * V ω) (indepSpaceLaw m n B) :=
    (tc4_diag F q' hqm' hql' r b c).1
  have hint : Integrable (fun ω => U ω * V ω) (indepSpaceLaw m n B) := by
    refine ((hUU.add hVV).div_const 2).mono' (hUm.mul hVm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    show ‖U ω * V ω‖ ≤ (U ω * U ω + V ω * V ω) / 2
    rw [Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (U ω - V ω), sq_nonneg (U ω + V ω)]
  refine ⟨hint, ?_⟩
  have hT := tc4_flip_slot (m := m) (n := n) (B := B) p
  let e : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) ≃ᵐ ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) :=
    { toFun := fun ω i => if i = p then (-(ω i).1, (ω i).2) else ω i
      invFun := fun ω i => if i = p then (-(ω i).1, (ω i).2) else ω i
      left_inv := fun ω => by funext i; by_cases h : i = p <;> simp [h]
      right_inv := fun ω => by funext i; by_cases h : i = p <;> simp [h]
      measurable_toFun := hT.measurable
      measurable_invFun := hT.measurable }
  have hTe : MeasurePreserving e (indepSpaceLaw m n B) (indepSpaceLaw m n B) := hT
  have hkey : ∀ ω, (fun ω => U ω * V ω) (e ω) = -(U ω * V ω) := by
    intro ω
    have h1 : (e ω) p = (-(ω p).1, (ω p).2) := by simp [e]
    have h2 : (e ω) r = ω r := by simp [e, hpr.symm]
    simp only [hU, hV, h1, h2, hqo]
    ring
  have h1 : ∫ ω, (fun ω => U ω * V ω) (e ω) ∂(indepSpaceLaw m n B) =
      ∫ ω, U ω * V ω ∂(indepSpaceLaw m n B) :=
    hTe.integral_comp' (fun ω => U ω * V ω)
  have h2 : ∫ ω, (fun ω => U ω * V ω) (e ω) ∂(indepSpaceLaw m n B) =
      -∫ ω, U ω * V ω ∂(indepSpaceLaw m n B) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => hkey ω)
  linarith [h1, h2]


/-- Orthogonality of centred slot variables: the second moment of a finite sum of slot terms
`c_i q_i(g_{π i}) h_{π i}(b,c)` over distinct slots is the sum of the diagonal moments. -/
private lemma tc4_orth (F : FrozenParams m n B) (T : ℤ) (N' : ℕ) (cc : ℕ → ℝ) (q : ℕ → ℝ → ℝ)
    (hqm : ∀ j, Measurable (q j)) (hql : ∀ j x, |q j x| ≤ |x|) (hqo : ∀ j x, q j (-x) = - q j x)
    (b : Fin m) (c : Fin n) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      (∑ i ∈ Finset.range N' ×ˢ (Finset.univ : Finset (Fin B)), cc i.1 *
        (q i.1 (ω (T + 1 - (i.1 : ℤ), i.2)).1 * ((rOut F.C).mulVec (ω (T + 1 - (i.1 : ℤ), i.2)).2.1 b *
          (rIn F.C).mulVec (ω (T + 1 - (i.1 : ℤ), i.2)).2.2 c))) ^ 2) (indepSpaceLaw m n B) ∧
    ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      (∑ i ∈ Finset.range N' ×ˢ (Finset.univ : Finset (Fin B)), cc i.1 *
        (q i.1 (ω (T + 1 - (i.1 : ℤ), i.2)).1 * ((rOut F.C).mulVec (ω (T + 1 - (i.1 : ℤ), i.2)).2.1 b *
          (rIn F.C).mulVec (ω (T + 1 - (i.1 : ℤ), i.2)).2.2 c))) ^ 2 ∂(indepSpaceLaw m n B)
      = ∑ j ∈ Finset.range N', (B : ℝ) * cc j ^ 2 * (∫ x, q j x ^ 2 ∂(gaussianReal 0 1)) *
          (F.C.Sout b b * F.C.Sin c c) := by
  classical
  set A : ℕ × Fin B → ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → ℝ := fun i ω =>
    q i.1 (ω (T + 1 - (i.1 : ℤ), i.2)).1 * ((rOut F.C).mulVec (ω (T + 1 - (i.1 : ℤ), i.2)).2.1 b *
          (rIn F.C).mulVec (ω (T + 1 - (i.1 : ℤ), i.2)).2.2 c) with hA
  set s : Finset (ℕ × Fin B) := Finset.range N' ×ˢ (Finset.univ : Finset (Fin B)) with hs
  have hpair : ∀ i k : ℕ × Fin B,
      Integrable (fun ω => A i ω * A k ω) (indepSpaceLaw m n B) ∧
      ∫ ω, A i ω * A k ω ∂(indepSpaceLaw m n B) =
        if i = k then (∫ x, q i.1 x ^ 2 ∂(gaussianReal 0 1)) * (F.C.Sout b b * F.C.Sin c c)
        else 0 := by
    intro i k
    by_cases h : i = k
    · subst h
      simpa using tc4_diag F (q i.1) (hqm _) (hql _) (T + 1 - (i.1 : ℤ), i.2) b c
    · have hne : (T + 1 - (i.1 : ℤ), i.2) ≠ (T + 1 - (k.1 : ℤ), k.2) := by
        intro hh
        apply h
        simp only [Prod.mk.injEq] at hh
        exact Prod.ext (by exact_mod_cast (by omega : (i.1 : ℤ) = k.1)) hh.2
      simpa [h] using tc4_cross F (q i.1) (q k.1) (hqm _) (hql _) (hqo _) (hqm _) (hql _) hne b c
  have hexp : ∀ ω, (∑ i ∈ s, cc i.1 * A i ω) ^ 2 =
      ∑ i ∈ s, ∑ k ∈ s, (cc i.1 * cc k.1) * (A i ω * A k ω) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hint : ∀ i ∈ s, ∀ k ∈ s, Integrable (fun ω => (cc i.1 * cc k.1) * (A i ω * A k ω))
      (indepSpaceLaw m n B) := fun i _ k _ => (hpair i k).1.const_mul _
  have hfun : (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => (∑ i ∈ s, cc i.1 * A i ω) ^ 2) =
      fun ω => ∑ i ∈ s, ∑ k ∈ s, (cc i.1 * cc k.1) * (A i ω * A k ω) := funext hexp
  show Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => (∑ i ∈ s, cc i.1 * A i ω) ^ 2)
      (indepSpaceLaw m n B) ∧ _
  rw [hfun]
  refine ⟨?_, ?_⟩
  · exact integrable_finsetSum _ fun i hi => integrable_finsetSum _ fun k hk => hint i hi k hk
  · rw [integral_finsetSum _ fun i hi => integrable_finsetSum _ fun k hk => hint i hi k hk]
    have h1 : ∀ i ∈ s, ∫ ω, ∑ k ∈ s, (cc i.1 * cc k.1) * (A i ω * A k ω) ∂(indepSpaceLaw m n B)
        = cc i.1 ^ 2 * ((∫ x, q i.1 x ^ 2 ∂(gaussianReal 0 1)) * (F.C.Sout b b * F.C.Sin c c)) := by
      intro i hi
      rw [integral_finsetSum _ fun k hk => hint i hi k hk]
      have h2 : ∀ k ∈ s, ∫ ω, (cc i.1 * cc k.1) * (A i ω * A k ω) ∂(indepSpaceLaw m n B) =
          if k = i then cc i.1 ^ 2 * ((∫ x, q i.1 x ^ 2 ∂(gaussianReal 0 1)) *
            (F.C.Sout b b * F.C.Sin c c)) else 0 := by
        intro k hk
        rw [integral_const_mul, (hpair i k).2]
        by_cases hki : k = i
        · subst hki; simp [sq]
        · have : ¬ i = k := fun h => hki h.symm
          simp [hki, this]
      rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq' s i]
      simp [hi]
    rw [Finset.sum_congr rfl h1, hs, Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring


private lemma tc4_emaW_partial (β : ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range k, Muon.emaW β j = 1 - β ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    unfold Muon.emaW
    ring

private lemma tc4_wsq_total (β : ℝ) (hβ : 0 ≤ β ∧ β < 1) (N' : ℕ) :
    ∑ j ∈ Finset.range N', Muon.emaW β j ^ 2 ≤ 1 := by
  have h1 : ∀ j, Muon.emaW β j ^ 2 ≤ Muon.emaW β j := by
    intro j
    have h0 : 0 ≤ Muon.emaW β j := by
      unfold Muon.emaW
      exact mul_nonneg (by linarith [hβ.2]) (pow_nonneg hβ.1 j)
    have h2 : Muon.emaW β j ≤ 1 := by
      unfold Muon.emaW
      have : β ^ j ≤ 1 := pow_le_one₀ hβ.1 hβ.2.le
      nlinarith [hβ.1]
    nlinarith
  calc ∑ j ∈ Finset.range N', Muon.emaW β j ^ 2 ≤ ∑ j ∈ Finset.range N', Muon.emaW β j :=
        Finset.sum_le_sum fun j _ => h1 j
    _ = 1 - β ^ N' := tc4_emaW_partial β N'
    _ ≤ 1 := by linarith [pow_nonneg hβ.1 N']

private lemma tc4_wsq_tail (β : ℝ) (hβ : 0 ≤ β ∧ β < 1) (N N' : ℕ) :
    ∑ j ∈ Finset.range N', (if N ≤ j then Muon.emaW β j ^ 2 else 0) ≤ β ^ (2 * N) := by
  have hβ2 : β ^ 2 < 1 := by nlinarith [hβ.1, hβ.2]
  have hf : (Finset.range N').filter (fun j => N ≤ j) = Finset.Ico N N' := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [← Finset.sum_filter, hf]
  have h1 : ∀ j, Muon.emaW β j ^ 2 = (1 - β) ^ 2 * (β ^ 2) ^ j := by
    intro j; unfold Muon.emaW; rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j 2]
  simp_rw [h1]
  rw [← Finset.mul_sum]
  have h2 := geom_sum_Ico_le_of_lt_one (x := β ^ 2) (m := N) (n := N') (by positivity) hβ2
  have h3 : (1 - β) ^ 2 * ((β ^ 2) ^ N / (1 - β ^ 2)) ≤ β ^ (2 * N) := by
    have hpos : 0 < 1 - β ^ 2 := by linarith
    rw [← pow_mul]
    rw [mul_div_assoc', div_le_iff₀ hpos]
    have : (1 - β) ^ 2 ≤ 1 - β ^ 2 := by nlinarith [hβ.1, hβ.2]
    rw [mul_comm (β ^ (2 * N))]; exact mul_le_mul_of_nonneg_right this (pow_nonneg hβ.1 _)
  exact (mul_le_mul_of_nonneg_left h2 (by positivity)).trans h3

private lemma tc4_abs_entry_le_opNorm {p q : ℕ} (K : Mat p q) (i : Fin p) (j : Fin q) :
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

private lemma tc4_trace_le {p : ℕ} (S : Mat p p) (C : ℝ) (h : opNorm S ≤ C) :
    ∑ i, S i i ≤ (p : ℝ) * C := by
  calc ∑ i, S i i ≤ ∑ _i : Fin p, C := Finset.sum_le_sum fun i _ =>
        (le_abs_self _).trans ((tc4_abs_entry_le_opNorm S i i).trans h)
    _ = (p : ℝ) * C := by simp


private lemma tc4_rOut_outer_rIn (F : FrozenParams m n B) (z : Vec m) (w : Vec n) :
    rOut F.C * outer z w * rIn F.C =
      outer (Matrix.mulVec (rOut F.C) z) (Matrix.mulVec (rIn F.C) w) := by
  have hv : Matrix.vecMul w (rIn F.C) = Matrix.mulVec (rIn F.C) w := by
    rw [← Matrix.vecMul_transpose, tc4_rIn_symm]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]

private lemma tc4_batch_entry (F : FrozenParams m n B)
    (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (s : ℤ) (b : Fin m) (c : Fin n) :
    indepBatchG F ω s b c = (B : ℝ)⁻¹ * ∑ a' : Fin B, (ω (s, a')).1 *
      ((rOut F.C).mulVec (ω (s, a')).2.1 b * (rIn F.C).mulVec (ω (s, a')).2.2 c) := by
  unfold indepBatchG
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [tc4_rOut_outer_rIn]
  simp [outer, Matrix.vecMulVec_apply]


private lemma tc4_abs_entry_le_fro (K : Mat m n) (i : Fin m) (k : Fin n) : |K i k| ≤ fro K := by
  unfold fro
  refine Real.abs_le_sqrt ?_
  have h1 : ‖K i k‖ ^ 2 ≤ ∑ k', ‖K i k'‖ ^ 2 :=
    Finset.single_le_sum (f := fun k' => ‖K i k'‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ k)
  have h2 : ∑ k', ‖K i k'‖ ^ 2 ≤ ∑ i', ∑ k', ‖K i' k'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ k', ‖K i' k'‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
  have h3 : K i k ^ 2 = ‖K i k‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [h3]
  exact h1.trans h2

private lemma tc4_emaW_nonneg (F : FrozenParams m n B) (j : ℕ) : 0 ≤ emaW F.β j := by
  unfold emaW
  exact mul_nonneg (by linarith [F.hβ.2]) (pow_nonneg F.hβ.1 j)

private lemma tc4_emaW_summable (F : FrozenParams m n B) : Summable (fun j : ℕ => emaW F.β j) := by
  unfold emaW
  exact (summable_geometric_of_lt_one F.hβ.1 F.hβ.2).mul_left _

open scoped Matrix.Norms.Frobenius in
private lemma tc4_ae_hasSum (F : FrozenParams m n B) :
    ∀ᵐ ω ∂(indepSpaceLaw m n B), ∀ (t' : ℤ) (b : Fin m) (c : Fin n),
      HasSum (fun j : ℕ => emaW F.β j * indepBatchG F ω (t' + 1 - (j : ℤ)) b c)
        (def_app_vol_product F ω t' b c) ∧
      Summable (fun j : ℕ => |emaW F.β j * indepBatchG F ω (t' + 1 - (j : ℤ)) b c|) := by
  filter_upwards [def_app_vol_product_summable F] with ω hω t' b c
  have hs : Summable fun j : ℕ => emaW F.β j • indepBatchG F ω (t' + 1 - (j : ℤ)) := by
    refine Summable.of_norm ?_
    simpa [fro_eq_norm] using hω t'
  refine ⟨?_, ?_⟩
  · have h := hs.hasSum
    have h2 := Pi.hasSum.mp h b
    have h3 := Pi.hasSum.mp h2 c
    simpa [def_app_vol_product] using h3
  · refine Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ?_) (hω t')
    have := tc4_abs_entry_le_fro (emaW F.β j • indepBatchG F ω (t' + 1 - (j : ℤ))) b c
    simpa using this

private lemma tc4_batch_meas (F : FrozenParams m n B) (s : ℤ) (b : Fin m) (c : Fin n) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => indepBatchG F ω s b c) := by
  simp_rw [tc4_batch_entry]
  exact Measurable.const_mul (Finset.measurable_sum _ fun a' _ => tc4_hh_meas F id measurable_id (s, a') b c) _

private lemma tc4_entry_aem (F : FrozenParams m n B) (t : ℤ) (b : Fin m) (c : Fin n) :
    AEMeasurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      def_app_vol_product F ω t b c) (indepSpaceLaw m n B) := by
  refine aemeasurable_of_tendsto_metrizable_ae Filter.atTop
    (f := fun (N : ℕ) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) =>
      ∑ j ∈ Finset.range N, emaW F.β j * indepBatchG F ω (t + 1 - (j : ℤ)) b c)
    (fun N => by
      have : Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
          ∑ j ∈ Finset.range N, emaW F.β j * indepBatchG F ω (t + 1 - (j : ℤ)) b c) :=
        Finset.measurable_sum _ fun j _ =>
          (tc4_batch_meas F (t + 1 - (j : ℤ)) b c).const_mul (emaW F.β j)
      exact this.aemeasurable) ?_
  filter_upwards [tc4_ae_hasSum F] with ω hω
  exact (hω t b c).1.tendsto_sum_nat



private lemma tc4_tau_nonneg (R : ℝ) : 0 ≤ cutoffTau R := by
  unfold cutoffTau
  exact integral_nonneg fun x => by split_ifs <;> positivity

private lemma tc4_q_meas (R : ℝ) (N j : ℕ) :
    Measurable (fun x : ℝ => if j < N ∧ |x| ≤ R then (0 : ℝ) else x) := by
  by_cases h : j < N
  · simp only [h, true_and]
    exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const
      measurable_id
  · simp only [h, false_and, if_false]
    exact measurable_id

private lemma tc4_q_le (R : ℝ) (N j : ℕ) (x : ℝ) :
    |(if j < N ∧ |x| ≤ R then (0 : ℝ) else x)| ≤ |x| := by
  split_ifs <;> simp

private lemma tc4_q_odd (R : ℝ) (N j : ℕ) (x : ℝ) :
    (if j < N ∧ |-x| ≤ R then (0 : ℝ) else -x) = -(if j < N ∧ |x| ≤ R then (0 : ℝ) else x) := by
  simp only [abs_neg]
  split_ifs <;> simp

private lemma tc4_q_kappa (R : ℝ) (N j : ℕ) :
    ∫ x, (if j < N ∧ |x| ≤ R then (0 : ℝ) else x) ^ 2 ∂(gaussianReal 0 1)
      = if j < N then cutoffTau R else 1 := by
  by_cases h : j < N
  · simp only [h, if_true]
    unfold cutoffTau
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (if True ∧ |x| ≤ R then (0 : ℝ) else x) ^ 2 = if R < |x| then x ^ 2 else 0
    by_cases hx : |x| ≤ R
    · simp [hx, not_lt.2 hx]
    · simp [hx, not_le.1 hx]
  · simp only [h, false_and, if_false]
    exact Muon.Foundations.gaussian_moment_two

private lemma tc4_Sdiag_nonneg (F : FrozenParams m n B) (b : Fin m) : 0 ≤ F.C.Sout b b := by
  have := F.C.psdOut.diag_nonneg (i := b)
  simpa using this

private lemma tc4_Sindiag_nonneg (F : FrozenParams m n B) (c : Fin n) : 0 ≤ F.C.Sin c c := by
  have := F.C.psdIn.diag_nonneg (i := c)
  simpa using this


private lemma tc4_entry_bound (F : FrozenParams m n B) (R : ℝ) (T : ℤ) (N : ℕ) (b : Fin m)
    (c : Fin n)
    (Kent : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → ℝ)
    (hK : ∀ ω, Kent ω = ∑ j ∈ Finset.range N, emaW F.β j * ((B : ℝ)⁻¹ * ∑ a : Fin B,
        (if |(ω (T + 1 - (j : ℤ), a)).1| ≤ R then (ω (T + 1 - (j : ℤ), a)).1 else 0) *
          ((rOut F.C).mulVec (ω (T + 1 - (j : ℤ), a)).2.1 b *
            (rIn F.C).mulVec (ω (T + 1 - (j : ℤ), a)).2.2 c))) :
    ∫⁻ ω, ENNReal.ofReal ((def_app_vol_product F ω T b c - Kent ω) ^ 2) ∂(indepSpaceLaw m n B)
      ≤ ENNReal.ofReal ((B : ℝ)⁻¹ * (cutoffTau R + F.β ^ (2 * N)) *
          (F.C.Sout b b * F.C.Sin c c)) := by
  classical
  have hBpos : (0 : ℝ) < B := by exact_mod_cast F.hB
  set q : ℕ → ℝ → ℝ := fun j x => if j < N ∧ |x| ≤ R then 0 else x with hq
  have hqm : ∀ j, Measurable (q j) := fun j => tc4_q_meas R N j
  have hql : ∀ j x, |q j x| ≤ |x| := fun j x => tc4_q_le R N j x
  have hqo : ∀ j x, q j (-x) = - q j x := fun j x => tc4_q_odd R N j x
  set cc : ℕ → ℝ := fun j => emaW F.β j * (B : ℝ)⁻¹ with hcc
  set S : ℕ → ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → ℝ := fun N' ω =>
    ∑ i ∈ Finset.range N' ×ˢ (Finset.univ : Finset (Fin B)), cc i.1 *
        (q i.1 (ω (T + 1 - (i.1 : ℤ), i.2)).1 * ((rOut F.C).mulVec (ω (T + 1 - (i.1 : ℤ), i.2)).2.1 b *
          (rIn F.C).mulVec (ω (T + 1 - (i.1 : ℤ), i.2)).2.2 c)) with hS
  have hSmeas : ∀ N', Measurable (S N') := by
    intro N'
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (tc4_hh_meas F (q i.1) (hqm _) (T + 1 - (i.1 : ℤ), i.2) b c).const_mul _
  -- almost sure convergence
  have hconv : ∀ᵐ ω ∂(indepSpaceLaw m n B), Tendsto (fun N' => S N' ω) atTop
      (𝓝 (def_app_vol_product F ω T b c - Kent ω)) := by
    filter_upwards [tc4_ae_hasSum F] with ω hω
    have h1 := (hω T b c).1
    have h2 : HasSum (fun j : ℕ => if j ∈ Finset.range N then emaW F.β j * ((B : ℝ)⁻¹ * ∑ a : Fin B,
        (if |(ω (T + 1 - (j : ℤ), a)).1| ≤ R then (ω (T + 1 - (j : ℤ), a)).1 else 0) *
          ((rOut F.C).mulVec (ω (T + 1 - (j : ℤ), a)).2.1 b *
            (rIn F.C).mulVec (ω (T + 1 - (j : ℤ), a)).2.2 c)) else 0) (Kent ω) := by
      rw [hK ω]
      have : HasSum (fun j : ℕ =>
        if j ∈ Finset.range N then emaW F.β j * ((B : ℝ)⁻¹ * ∑ a : Fin B,
        (if |(ω (T + 1 - (j : ℤ), a)).1| ≤ R then (ω (T + 1 - (j : ℤ), a)).1 else 0) *
          ((rOut F.C).mulVec (ω (T + 1 - (j : ℤ), a)).2.1 b *
            (rIn F.C).mulVec (ω (T + 1 - (j : ℤ), a)).2.2 c)) else 0)
        (∑ j ∈ Finset.range N, (fun j : ℕ =>
        if j ∈ Finset.range N then emaW F.β j * ((B : ℝ)⁻¹ * ∑ a : Fin B,
        (if |(ω (T + 1 - (j : ℤ), a)).1| ≤ R then (ω (T + 1 - (j : ℤ), a)).1 else 0) *
          ((rOut F.C).mulVec (ω (T + 1 - (j : ℤ), a)).2.1 b *
            (rIn F.C).mulVec (ω (T + 1 - (j : ℤ), a)).2.2 c)) else 0) j) :=
        hasSum_sum_of_ne_finset_zero (fun j hj => if_neg hj)
      convert this using 1
      exact Finset.sum_congr rfl fun j hj => (if_pos hj).symm
    have h3 := (h1.sub h2).tendsto_sum_nat
    refine h3.congr fun N' => ?_
    simp only [hS]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tc4_batch_entry]
    by_cases hj : j < N
    · have hjm : j ∈ Finset.range N := Finset.mem_range.2 hj
      simp only [hjm, if_true, hq, hj, true_and, hcc]
      rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> ring
    · have hjm : j ∉ Finset.range N := fun h => hj (Finset.mem_range.1 h)
      simp only [hjm, if_false, hq, hj, false_and, hcc]
      rw [sub_zero, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
  -- uniform second-moment bound
  have hbound : ∀ N', ∫ ω, S N' ω ^ 2 ∂(indepSpaceLaw m n B) ≤
      (B : ℝ)⁻¹ * (cutoffTau R + F.β ^ (2 * N)) * (F.C.Sout b b * F.C.Sin c c) := by
    intro N'
    have horth := (tc4_orth F T N' cc q hqm hql hqo b c).2
    have e : ∫ ω, S N' ω ^ 2 ∂(indepSpaceLaw m n B) = _ := horth
    rw [e]
    have hSS : 0 ≤ F.C.Sout b b * F.C.Sin c c :=
      mul_nonneg (tc4_Sdiag_nonneg F b) (tc4_Sindiag_nonneg F c)
    have hτ := tc4_tau_nonneg R
    have hterm : ∀ j ∈ Finset.range N', (B : ℝ) * cc j ^ 2 * (∫ x, q j x ^ 2 ∂(gaussianReal 0 1)) ≤
        (B : ℝ)⁻¹ * (cutoffTau R * emaW F.β j ^ 2 + (if N ≤ j then emaW F.β j ^ 2 else 0)) := by
      intro j _
      have hk : (∫ x, q j x ^ 2 ∂(gaussianReal 0 1)) = if j < N then cutoffTau R else 1 :=
        tc4_q_kappa R N j
      rw [hk]
      have hB2 : (B : ℝ) * cc j ^ 2 = (B : ℝ)⁻¹ * emaW F.β j ^ 2 := by
        simp only [hcc]; field_simp
      rw [hB2]
      by_cases hj : j < N
      · rw [if_pos hj, if_neg (not_le.2 hj)]
        apply le_of_eq; ring
      · rw [if_neg hj, if_pos (not_lt.1 hj)]
        have : 0 ≤ cutoffTau R * emaW F.β j ^ 2 := by positivity
        nlinarith [mul_nonneg (inv_nonneg.2 hBpos.le) this, mul_nonneg (inv_nonneg.2 hBpos.le) (sq_nonneg (emaW F.β j))]
    have hsum : ∑ j ∈ Finset.range N', (B : ℝ) * cc j ^ 2 * (∫ x, q j x ^ 2 ∂(gaussianReal 0 1)) ≤
        (B : ℝ)⁻¹ * (cutoffTau R + F.β ^ (2 * N)) := by
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hBpos.le)
      have h1 := tc4_wsq_total F.β F.hβ N'
      have h2 := tc4_wsq_tail F.β F.hβ N N'
      nlinarith [mul_le_mul_of_nonneg_left h1 hτ]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hsum hSS
  -- Fatou
  have hint : ∀ N', ∫⁻ ω, ENNReal.ofReal (S N' ω ^ 2) ∂(indepSpaceLaw m n B) ≤
      ENNReal.ofReal ((B : ℝ)⁻¹ * (cutoffTau R + F.β ^ (2 * N)) *
          (F.C.Sout b b * F.C.Sin c c)) := by
    intro N'
    have hI : Integrable (fun ω => S N' ω ^ 2) (indepSpaceLaw m n B) :=
      (tc4_orth F T N' cc q hqm hql hqo b c).1
    rw [← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hbound N')
  calc ∫⁻ ω, ENNReal.ofReal ((def_app_vol_product F ω T b c - Kent ω) ^ 2) ∂(indepSpaceLaw m n B)
      = ∫⁻ ω, Filter.liminf (fun N' => ENNReal.ofReal (S N' ω ^ 2)) atTop
          ∂(indepSpaceLaw m n B) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hconv] with ω hω
        exact ((ENNReal.tendsto_ofReal (hω.pow 2)).liminf_eq).symm
    _ ≤ Filter.liminf (fun N' => ∫⁻ ω, ENNReal.ofReal (S N' ω ^ 2) ∂(indepSpaceLaw m n B)) atTop :=
        lintegral_liminf_le (fun N' => ((hSmeas N').pow_const 2).ennreal_ofReal)
    _ ≤ ENNReal.ofReal ((B : ℝ)⁻¹ * (cutoffTau R + F.β ^ (2 * N)) *
          (F.C.Sout b b * F.C.Sin c c)) := by
        refine (Filter.liminf_le_limsup).trans ?_
        exact Filter.limsup_le_of_le (h := Filter.Eventually.of_forall hint)


private lemma tc4_cutoff_entry (Fp : FrozenParams m n B) (ℓ J : ℕ) (R : ℝ) (t : ℤ) (l : ℕ)
    (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (b : Fin m) (c : Fin n) (Ef : ℤ → ℝ)
    (hE : ∀ s, Ef s = ∑ a : Fin B, (if |(ω (s, a)).1| ≤ R then (ω (s, a)).1 else 0) *
        ((rOut Fp.C).mulVec (ω (s, a)).2.1 b * (rIn Fp.C).mulVec (ω (s, a)).2.2 c)) :
    cutoffMat Fp ℓ J R t l ω b c = (B : ℝ)⁻¹ *
      ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ), treeVarpi Fp.β ℓ l α * Ef (t + 1 + α) := by
  unfold cutoffMat
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hE, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tc4_rOut_outer_rIn]
  simp [outer, Matrix.vecMulVec_apply]
  ring

private lemma tc4_sum_Icc_neg (J : ℕ) (f : ℤ → ℝ) :
    ∑ α ∈ Finset.Icc (-(J : ℤ)) 0, f α = ∑ j ∈ Finset.range (J + 1), f (-(j : ℤ)) := by
  apply Finset.sum_nbij' (fun α : ℤ => (-α).toNat) (fun j : ℕ => -(j : ℤ))
  · intro α hα; simp only [Finset.mem_Icc, Finset.mem_range] at hα ⊢; omega
  · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
  · intro α hα; simp only [Finset.mem_Icc] at hα; try dsimp only
    omega
  · intro j hj; simp only [Finset.mem_range] at hj; try dsimp only
    omega
  · intro α hα; simp only [Finset.mem_Icc] at hα; try dsimp only
    congr 1
    omega

private lemma tc4_sum_Icc_pos (ℓ : ℕ) (f : ℤ → ℝ) :
    ∑ α ∈ Finset.Icc (1 : ℤ) (ℓ : ℤ), f α = ∑ k ∈ Finset.range ℓ, f ((ℓ : ℤ) - (k : ℤ)) := by
  apply Finset.sum_nbij' (fun α : ℤ => ℓ - α.toNat) (fun k : ℕ => (ℓ : ℤ) - (k : ℤ))
  · intro α hα; simp only [Finset.mem_Icc, Finset.mem_range] at hα ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
  · intro α hα; simp only [Finset.mem_Icc] at hα; try dsimp only
    omega
  · intro k hk; simp only [Finset.mem_range] at hk; try dsimp only
    omega
  · intro α hα; simp only [Finset.mem_Icc] at hα; try dsimp only
    congr 1
    omega

private lemma tc4_split_Icc (J ℓ : ℕ) (f : ℤ → ℝ) :
    ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ), f α =
      ∑ j ∈ Finset.range (J + 1), f (-(j : ℤ)) +
        ∑ k ∈ Finset.range ℓ, f ((ℓ : ℤ) - (k : ℤ)) := by
  have hU : Finset.Icc (-(J : ℤ)) (ℓ : ℤ) = Finset.Icc (-(J : ℤ)) 0 ∪ Finset.Icc 1 (ℓ : ℤ) := by
    ext α; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hD : Disjoint (Finset.Icc (-(J : ℤ)) 0) (Finset.Icc 1 (ℓ : ℤ)) := by
    rw [Finset.disjoint_left]
    intro α h1 h2
    simp only [Finset.mem_Icc] at h1 h2
    omega
  rw [hU, Finset.sum_union hD, tc4_sum_Icc_neg, tc4_sum_Icc_pos]

private lemma tc4_cutoff_sum1 (β : ℝ) (ℓ J : ℕ) (t : ℤ) (Ef : ℤ → ℝ) :
    (B : ℝ)⁻¹ * ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ), treeVarpi β ℓ 1 α * Ef (t + 1 + α) =
      ∑ j ∈ Finset.range (J + 1), emaW β j * ((B : ℝ)⁻¹ * Ef (t + 1 - (j : ℤ))) := by
  rw [tc4_split_Icc]
  have e2 : ∀ k ∈ Finset.range ℓ, treeVarpi β ℓ 1 ((ℓ : ℤ) - (k : ℤ)) = 0 := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have h : ¬ ((ℓ : ℤ) - (k : ℤ) ≤ 0) := by omega
    unfold treeVarpi
    simp [h]
  have h0 : ∑ k ∈ Finset.range ℓ, treeVarpi β ℓ 1 ((ℓ : ℤ) - (k : ℤ)) *
      Ef (t + 1 + ((ℓ : ℤ) - (k : ℤ))) = 0 :=
    Finset.sum_eq_zero fun k hk => by rw [e2 k hk, zero_mul]
  rw [h0, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : treeVarpi β ℓ 1 (-(j : ℤ)) = emaW β j := by
    unfold treeVarpi; simp
  rw [this, show t + 1 + -(j : ℤ) = t + 1 - (j : ℤ) by ring]
  ring

private lemma tc4_cutoff_sum2 (β : ℝ) (ℓ J : ℕ) (t : ℤ) (Ef : ℤ → ℝ) :
    (B : ℝ)⁻¹ * ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ), treeVarpi β ℓ 2 α * Ef (t + 1 + α) =
      ∑ j ∈ Finset.range (ℓ + J + 1), emaW β j * ((B : ℝ)⁻¹ * Ef (t + (ℓ : ℤ) + 1 - (j : ℤ))) := by
  rw [tc4_split_Icc, mul_add]
  have e1 : ∀ j ∈ Finset.range (J + 1), (B : ℝ)⁻¹ * (treeVarpi β ℓ 2 (-(j : ℤ)) *
      Ef (t + 1 + -(j : ℤ))) = emaW β (ℓ + j) * ((B : ℝ)⁻¹ * Ef (t + (ℓ : ℤ) + 1 - ((ℓ + j : ℕ) : ℤ))) := by
    intro j _
    have : treeVarpi β ℓ 2 (-(j : ℤ)) = β ^ ℓ * emaW β j := by
      unfold treeVarpi; simp
    have h2 : emaW β (ℓ + j) = β ^ ℓ * emaW β j := by
      unfold emaW; rw [pow_add]; ring
    rw [this, h2, show t + (ℓ : ℤ) + 1 - ((ℓ + j : ℕ) : ℤ) = t + 1 + -(j : ℤ) by push_cast; ring]
    ring
  have e2 : ∀ k ∈ Finset.range ℓ, (B : ℝ)⁻¹ * (treeVarpi β ℓ 2 ((ℓ : ℤ) - (k : ℤ)) *
      Ef (t + 1 + ((ℓ : ℤ) - (k : ℤ)))) = emaW β k * ((B : ℝ)⁻¹ * Ef (t + (ℓ : ℤ) + 1 - (k : ℤ))) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have h : ¬ ((ℓ : ℤ) - (k : ℤ) ≤ 0) := by omega
    have hto : ((ℓ : ℤ) - (k : ℤ)).toNat = ℓ - k := by omega
    have : treeVarpi β ℓ 2 ((ℓ : ℤ) - (k : ℤ)) = emaW β k := by
      unfold treeVarpi
      rw [if_neg h, if_neg (by norm_num : ¬ (2 : ℕ) = 1), hto]
      congr 1
      omega
    rw [this, show t + 1 + ((ℓ : ℤ) - (k : ℤ)) = t + (ℓ : ℤ) + 1 - (k : ℤ) by ring]
    ring
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2,
    show ℓ + J + 1 = ℓ + (J + 1) from rfl,
    Finset.sum_range_add (fun j => emaW β j * ((B : ℝ)⁻¹ * Ef (t + (ℓ : ℤ) + 1 - (j : ℤ)))) ℓ (J + 1),
    add_comm]


private lemma tc4_fro_sq (K : Mat m n) : fro K ^ 2 = ∑ b, ∑ c, K b c ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma tc4_real_ineq (Fp : FrozenParams m n B) (γstar CSig V : ℝ)
    (hS : SizeFin Fp.C B γstar CSig) (hV : 0 ≤ V) :
    (B : ℝ)⁻¹ * ((B : ℝ)⁻¹ * V * ∑ b, ∑ c, Fp.C.Sout b b * Fp.C.Sin c c) ≤
      CSig ^ 2 * γstar ^ 2 * V := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  obtain ⟨h1, h2, h3⟩ := hS
  have hm : (m : ℝ) ≤ γstar * B := (Nat.cast_le.2 (le_max_left m n)).trans h1
  have hn : (n : ℝ) ≤ γstar * B := (Nat.cast_le.2 (le_max_right m n)).trans h1
  have hTo := tc4_trace_le Fp.C.Sout CSig h2
  have hTi := tc4_trace_le Fp.C.Sin CSig h3
  have hTo0 : 0 ≤ ∑ b, Fp.C.Sout b b := Finset.sum_nonneg fun b _ => tc4_Sdiag_nonneg Fp b
  have hTi0 : 0 ≤ ∑ c, Fp.C.Sin c c := Finset.sum_nonneg fun c _ => tc4_Sindiag_nonneg Fp c
  have hC0 : 0 ≤ CSig := by
    have : 0 ≤ opNorm Fp.C.Sout := by
      unfold opNorm
      exact norm_nonneg _
    linarith
  have hprod : (∑ b, ∑ c, Fp.C.Sout b b * Fp.C.Sin c c) ≤ (γstar * B) ^ 2 * CSig ^ 2 := by
    rw [← Finset.sum_mul_sum]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc (∑ b, Fp.C.Sout b b) * ∑ c, Fp.C.Sin c c ≤ ((m : ℝ) * CSig) * ((n : ℝ) * CSig) :=
          mul_le_mul hTo hTi hTi0 (mul_nonneg hm0 hC0)
      _ = ((m : ℝ) * n) * CSig ^ 2 := by ring
      _ ≤ ((γstar * B) * (γstar * B)) * CSig ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul hm hn hn0 (hm0.trans hm)) (sq_nonneg _)
      _ = (γstar * B) ^ 2 * CSig ^ 2 := by ring
  have hBi : 0 ≤ (B : ℝ)⁻¹ := inv_nonneg.2 hBpos.le
  calc (B : ℝ)⁻¹ * ((B : ℝ)⁻¹ * V * ∑ b, ∑ c, Fp.C.Sout b b * Fp.C.Sin c c)
      ≤ (B : ℝ)⁻¹ * ((B : ℝ)⁻¹ * V * ((γstar * B) ^ 2 * CSig ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod (mul_nonneg hBi hV)) hBi
    _ = CSig ^ 2 * γstar ^ 2 * V := by field_simp


private lemma tc4_K_meas (Fp : FrozenParams m n B) (R : ℝ) (T : ℤ) (N : ℕ)
    (K : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n)
    (hK : ∀ ω b c, K ω b c = ∑ j ∈ Finset.range N, emaW Fp.β j * ((B : ℝ)⁻¹ * ∑ a : Fin B,
        (if |(ω (T + 1 - (j : ℤ), a)).1| ≤ R then (ω (T + 1 - (j : ℤ), a)).1 else 0) *
          ((rOut Fp.C).mulVec (ω (T + 1 - (j : ℤ), a)).2.1 b *
            (rIn Fp.C).mulVec (ω (T + 1 - (j : ℤ), a)).2.2 c))) :
    ∀ b c, Measurable (fun ω => K ω b c) := by
  have hqm : Measurable (fun x : ℝ => if |x| ≤ R then x else 0) :=
    Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_id measurable_const
  intro b c
  have : (fun ω => K ω b c) = fun ω => ∑ j ∈ Finset.range N, emaW Fp.β j * ((B : ℝ)⁻¹ *
      ∑ a : Fin B, (if |(ω (T + 1 - (j : ℤ), a)).1| ≤ R then (ω (T + 1 - (j : ℤ), a)).1 else 0) *
        ((rOut Fp.C).mulVec (ω (T + 1 - (j : ℤ), a)).2.1 b *
          (rIn Fp.C).mulVec (ω (T + 1 - (j : ℤ), a)).2.2 c)) := funext fun ω => hK ω b c
  rw [this]
  refine Finset.measurable_sum _ fun j _ => Measurable.const_mul (Measurable.const_mul
    (Finset.measurable_sum _ fun a _ => ?_) _) _
  exact tc4_hh_meas Fp (fun x => if |x| ≤ R then x else 0) hqm (T + 1 - (j : ℤ), a) b c

private lemma tc4_fro_bound (Fp : FrozenParams m n B) (R γstar CSig : ℝ)
    (hS : SizeFin Fp.C B γstar CSig) (T : ℤ) (N : ℕ)
    (K : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n)
    (hK : ∀ ω b c, K ω b c = ∑ j ∈ Finset.range N, emaW Fp.β j * ((B : ℝ)⁻¹ * ∑ a : Fin B,
        (if |(ω (T + 1 - (j : ℤ), a)).1| ≤ R then (ω (T + 1 - (j : ℤ), a)).1 else 0) *
          ((rOut Fp.C).mulVec (ω (T + 1 - (j : ℤ), a)).2.1 b *
            (rIn Fp.C).mulVec (ω (T + 1 - (j : ℤ), a)).2.2 c))) :
    ENNReal.ofReal ((B : ℝ)⁻¹) *
      ∫⁻ ω, ENNReal.ofReal (fro (def_app_vol_product Fp ω T - K ω) ^ 2) ∂(indepSpaceLaw m n B)
      ≤ ENNReal.ofReal (CSig ^ 2 * γstar ^ 2 * (cutoffTau R + Fp.β ^ (2 * N))) := by
  classical
  have hBpos : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  have hV : 0 ≤ cutoffTau R + Fp.β ^ (2 * N) :=
    add_nonneg (tc4_tau_nonneg R) (pow_nonneg Fp.hβ.1 _)
  have hKm := tc4_K_meas Fp R T N K hK
  have hDm : ∀ b c, AEMeasurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      ENNReal.ofReal ((def_app_vol_product Fp ω T b c - K ω b c) ^ 2)) (indepSpaceLaw m n B) :=
    fun b c => (((tc4_entry_aem Fp T b c).sub (hKm b c).aemeasurable).pow_const 2).ennreal_ofReal
  have hfro : ∀ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      ENNReal.ofReal (fro (def_app_vol_product Fp ω T - K ω) ^ 2) =
        ∑ b, ∑ c, ENNReal.ofReal ((def_app_vol_product Fp ω T b c - K ω b c) ^ 2) := by
    intro ω
    rw [tc4_fro_sq]
    simp only [Matrix.sub_apply]
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun b _ => ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)
  simp_rw [hfro]
  have hDs : ∀ b : Fin m, AEMeasurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      ∑ c : Fin n, ENNReal.ofReal ((def_app_vol_product Fp ω T b c - K ω b c) ^ 2))
      (indepSpaceLaw m n B) := fun b =>
    Finset.aemeasurable_fun_sum _ fun c _ => hDm b c
  rw [lintegral_finsetSum' _ fun b _ => hDs b]
  have hb : ∀ b ∈ (Finset.univ : Finset (Fin m)),
      ∫⁻ ω, ∑ c, ENNReal.ofReal ((def_app_vol_product Fp ω T b c - K ω b c) ^ 2)
          ∂(indepSpaceLaw m n B) ≤
        ∑ c, ENNReal.ofReal ((B : ℝ)⁻¹ * (cutoffTau R + Fp.β ^ (2 * N)) *
          (Fp.C.Sout b b * Fp.C.Sin c c)) := by
    intro b _
    rw [lintegral_finsetSum' _ fun c _ => hDm b c]
    exact Finset.sum_le_sum fun c _ =>
      tc4_entry_bound Fp R T N b c (fun ω => K ω b c) (fun ω => hK ω b c)
  refine (mul_le_mul' le_rfl (Finset.sum_le_sum hb)).trans ?_
  have hnn : ∀ b c, 0 ≤ (B : ℝ)⁻¹ * (cutoffTau R + Fp.β ^ (2 * N)) *
      (Fp.C.Sout b b * Fp.C.Sin c c) := fun b c =>
    mul_nonneg (mul_nonneg (inv_nonneg.2 hBpos.le) hV)
      (mul_nonneg (tc4_Sdiag_nonneg Fp b) (tc4_Sindiag_nonneg Fp c))
  rw [Finset.sum_congr rfl (fun b _ => (ENNReal.ofReal_sum_of_nonneg (fun c _ => hnn b c)).symm),
    ← ENNReal.ofReal_sum_of_nonneg (fun b _ => Finset.sum_nonneg fun c _ => hnn b c),
    ← ENNReal.ofReal_mul (inv_nonneg.2 hBpos.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := tc4_real_ineq Fp γstar CSig _ hS hV
  refine le_trans (le_of_eq ?_) this
  congr 1
  simp only [Finset.mul_sum]


private lemma tc4_delta_sq (β : ℝ) (hβ : 0 ≤ β ∧ β < 1) (J : ℕ) (R : ℝ) :
    cutoffTau R + β ^ (2 * (J + 1)) ≤ cutoffDelta β J R ^ 2 := by
  unfold cutoffDelta
  have h1 := tc4_tau_nonneg R
  have h2 : Real.sqrt (cutoffTau R) ^ 2 = cutoffTau R := Real.sq_sqrt h1
  have h3 : (β ^ (J + 1)) ^ 2 = β ^ (2 * (J + 1)) := by rw [← pow_mul, mul_comm]
  have h4 : 0 ≤ β ^ (J + 1) * Real.sqrt (cutoffTau R) :=
    mul_nonneg (pow_nonneg hβ.1 _) (Real.sqrt_nonneg _)
  nlinarith

private lemma tc4_cutoff_entries1 (Fp : FrozenParams m n B) (ℓ J : ℕ) (R : ℝ) (t : ℤ)
    (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (b : Fin m) (c : Fin n) :
    cutoffMat Fp ℓ J R t 1 ω b c = ∑ j ∈ Finset.range (J + 1), emaW Fp.β j * ((B : ℝ)⁻¹ *
      ∑ a : Fin B, (if |(ω (t + 1 - (j : ℤ), a)).1| ≤ R then (ω (t + 1 - (j : ℤ), a)).1 else 0) *
        ((rOut Fp.C).mulVec (ω (t + 1 - (j : ℤ), a)).2.1 b *
          (rIn Fp.C).mulVec (ω (t + 1 - (j : ℤ), a)).2.2 c)) := by
  rw [tc4_cutoff_entry Fp ℓ J R t 1 ω b c (fun s => ∑ a : Fin B,
    (if |(ω (s, a)).1| ≤ R then (ω (s, a)).1 else 0) *
      ((rOut Fp.C).mulVec (ω (s, a)).2.1 b * (rIn Fp.C).mulVec (ω (s, a)).2.2 c)) (fun s => rfl)]
  exact tc4_cutoff_sum1 (B := B) Fp.β ℓ J t (fun s => ∑ a : Fin B,
    (if |(ω (s, a)).1| ≤ R then (ω (s, a)).1 else 0) *
      ((rOut Fp.C).mulVec (ω (s, a)).2.1 b * (rIn Fp.C).mulVec (ω (s, a)).2.2 c))

private lemma tc4_cutoff_entries2 (Fp : FrozenParams m n B) (ℓ J : ℕ) (R : ℝ) (t : ℤ)
    (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (b : Fin m) (c : Fin n) :
    cutoffMat Fp ℓ J R t 2 ω b c = ∑ j ∈ Finset.range (ℓ + J + 1), emaW Fp.β j * ((B : ℝ)⁻¹ *
      ∑ a : Fin B, (if |(ω (t + (ℓ : ℤ) + 1 - (j : ℤ), a)).1| ≤ R then
        (ω (t + (ℓ : ℤ) + 1 - (j : ℤ), a)).1 else 0) *
        ((rOut Fp.C).mulVec (ω (t + (ℓ : ℤ) + 1 - (j : ℤ), a)).2.1 b *
          (rIn Fp.C).mulVec (ω (t + (ℓ : ℤ) + 1 - (j : ℤ), a)).2.2 c)) := by
  rw [tc4_cutoff_entry Fp ℓ J R t 2 ω b c (fun s => ∑ a : Fin B,
    (if |(ω (s, a)).1| ≤ R then (ω (s, a)).1 else 0) *
      ((rOut Fp.C).mulVec (ω (s, a)).2.1 b * (rIn Fp.C).mulVec (ω (s, a)).2.2 c)) (fun s => rfl)]
  exact tc4_cutoff_sum2 (B := B) Fp.β ℓ J t (fun s => ∑ a : Fin B,
    (if |(ω (s, a)).1| ≤ R then (ω (s, a)).1 else 0) *
      ((rOut Fp.C).mulVec (ω (s, a)).2.1 b * (rIn Fp.C).mulVec (ω (s, a)).2.2 c))

private lemma tc4_cutoff_each (Fp : FrozenParams m n B) (ℓ J : ℕ) (R γstar CSig : ℝ)
    (hS : SizeFin Fp.C B γstar CSig) (t : ℤ) :
    ENNReal.ofReal ((B : ℝ)⁻¹) *
        ∫⁻ ω, ENNReal.ofReal (fro (def_app_vol_product Fp ω t - cutoffMat Fp ℓ J R t 1 ω) ^ 2)
          ∂(indepSpaceLaw m n B) ≤ ENNReal.ofReal (CSig ^ 2 * γstar ^ 2 * cutoffDelta Fp.β J R ^ 2)
    ∧ ENNReal.ofReal ((B : ℝ)⁻¹) *
        ∫⁻ ω, ENNReal.ofReal
            (fro (def_app_vol_product Fp ω (t + (ℓ : ℤ)) - cutoffMat Fp ℓ J R t 2 ω) ^ 2)
          ∂(indepSpaceLaw m n B) ≤ ENNReal.ofReal (CSig ^ 2 * γstar ^ 2 * cutoffDelta Fp.β J R ^ 2) := by
  have h1 := tc4_fro_bound Fp R γstar CSig hS t (J + 1) (cutoffMat Fp ℓ J R t 1)
    (fun ω b c => tc4_cutoff_entries1 Fp ℓ J R t ω b c)
  have h2 := tc4_fro_bound Fp R γstar CSig hS (t + (ℓ : ℤ)) (ℓ + J + 1) (cutoffMat Fp ℓ J R t 2)
    (fun ω b c => tc4_cutoff_entries2 Fp ℓ J R t ω b c)
  have hd := tc4_delta_sq Fp.β Fp.hβ J R
  have hb : Fp.β ^ (2 * (ℓ + J + 1)) ≤ Fp.β ^ (2 * (J + 1)) :=
    pow_le_pow_of_le_one Fp.hβ.1 Fp.hβ.2.le (by omega)
  have hc : 0 ≤ CSig ^ 2 * γstar ^ 2 := by positivity
  refine ⟨h1.trans (ENNReal.ofReal_le_ofReal ?_), h2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · exact mul_le_mul_of_nonneg_left hd hc
  · exact mul_le_mul_of_nonneg_left (by linarith) hc

private lemma tc4_sup_nonneg (f : ℝ → ℝ) : 0 ≤ supNorm f :=
  Real.iSup_nonneg fun _ => abs_nonneg _

private lemma tc4_lip_nonneg (f : ℝ → ℝ) : 0 ≤ lipConst f :=
  Real.iSup_nonneg fun p => by
    split_ifs
    · exact le_rfl
    · positivity

open scoped Matrix.Norms.Frobenius in
private lemma tc4_oddSharp_cont (f : ℝ → ℝ) (hf : IsOddBddLip f) :
    Continuous (fun K : Mat m n => oddSharp f K) := by
  have hL : LipschitzWith (Real.toNNReal (lipConst f)) (fun K : Mat m n => oddSharp f K) := by
    refine LipschitzWith.of_dist_le_mul fun K K' => ?_
    rw [dist_eq_norm, dist_eq_norm, ← fro_eq_norm, ← fro_eq_norm,
      Real.coe_toNNReal _ (tc4_lip_nonneg f)]
    exact (lem_app_vol_sharp_i f hf K K').2.2
  exact hL.continuous

private lemma tc4_fro_aem {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → Mat m n) (hD : ∀ b c, AEMeasurable (fun ω => D ω b c) μ) :
    AEMeasurable (fun ω => fro (D ω)) μ := by
  unfold fro
  refine Measurable.comp_aemeasurable Real.continuous_sqrt.measurable ?_
  refine Finset.aemeasurable_fun_sum _ fun b _ => Finset.aemeasurable_fun_sum _ fun c _ => ?_
  have : (fun ω => ‖D ω b c‖ ^ 2) = fun ω => (D ω b c) ^ 2 := by
    funext ω; rw [Real.norm_eq_abs, sq_abs]
  rw [this]
  exact (hD b c).pow_const 2

private lemma tc4_L1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → ℝ) (hm : AEMeasurable h μ) (s : ℝ) (hs : 0 ≤ s)
    (hh : ∫⁻ ω, ENNReal.ofReal (h ω ^ 2) ∂μ ≤ ENNReal.ofReal (s ^ 2)) :
    ∫⁻ ω, ENNReal.ofReal (h ω) ∂μ ≤ ENNReal.ofReal s := by
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    have h1 : ∫⁻ ω, ENNReal.ofReal (h ω ^ 2) ∂μ = 0 := by
      refine le_antisymm ?_ bot_le
      simpa using hh
    have h2 := (lintegral_eq_zero_iff' (hm.pow_const 2).ennreal_ofReal).1 h1
    have h3 : ∫⁻ ω, ENNReal.ofReal (h ω) ∂μ = 0 := by
      rw [lintegral_eq_zero_iff' hm.ennreal_ofReal]
      filter_upwards [h2] with ω hω
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hω ⊢
      nlinarith [sq_nonneg (h ω)]
    simp [h3]
  · have hpt : ∀ ω, ENNReal.ofReal (h ω) ≤
        ENNReal.ofReal (s / 2) + ENNReal.ofReal (1 / (2 * s)) * ENNReal.ofReal (h ω ^ 2) := by
      intro ω
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have e : s / 2 + 1 / (2 * s) * h ω ^ 2 - h ω = (h ω - s) ^ 2 / (2 * s) := by
        field_simp; ring
      have : 0 ≤ (h ω - s) ^ 2 / (2 * s) := by positivity
      linarith
    calc ∫⁻ ω, ENNReal.ofReal (h ω) ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal (s / 2) + ENNReal.ofReal (1 / (2 * s)) *
            ENNReal.ofReal (h ω ^ 2)) ∂μ := lintegral_mono hpt
      _ = ENNReal.ofReal (s / 2) + ENNReal.ofReal (1 / (2 * s)) *
            ∫⁻ ω, ENNReal.ofReal (h ω ^ 2) ∂μ := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (s / 2) + ENNReal.ofReal (1 / (2 * s)) * ENNReal.ofReal (s ^ 2) :=
          add_le_add le_rfl (mul_le_mul' le_rfl hh)
      _ = ENNReal.ofReal s := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          congr 1
          field_simp
          ring

private lemma tc4_aem_comp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ → ℝ) (hg : Continuous g)
    (P Q : Ω → Matrix (Fin m) (Fin n) ℝ) (hP : AEMeasurable P μ) (hQ : AEMeasurable Q μ) :
    AEMeasurable (fun ω => g (P ω, Q ω)) μ := by
  have h1 : Measurable g := hg.measurable
  exact h1.comp_aemeasurable (hP.prodMk hQ)

private lemma tc4_contr_int {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hB : 0 < B) (γstar : ℝ)
    (hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B) (Fm : Mat m m) (Gm : Mat n n)
    (hFm : opNorm Fm ≤ 1) (hGm : opNorm Gm ≤ 1) (f₁ f₂ : ℝ → ℝ)
    (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂) (P Q : Ω → Mat m n)
    (hP : AEMeasurable P μ) (hQ : AEMeasurable Q μ) :
    Integrable (fun ω => contraction B Fm Gm f₁ f₂ (P ω) (Q ω)) μ := by
  have hc1 := tc4_oddSharp_cont (m := m) (n := n) f₁ hf₁
  have hc2 := tc4_oddSharp_cont (m := m) (n := n) f₂ hf₂
  have hcont : Continuous (fun p : Mat m n × Mat m n =>
      contraction B Fm Gm f₁ f₂ p.1 p.2) := by
    unfold contraction
    refine continuous_const.mul (Continuous.matrix_trace ?_)
    exact Continuous.matrix_mul (Continuous.matrix_mul (Continuous.matrix_mul continuous_const
      (hc1.comp continuous_fst)) continuous_const) (Continuous.matrix_transpose
        (hc2.comp continuous_snd))
  have ha : AEMeasurable (fun ω => contraction B Fm Gm f₁ f₂ (P ω) (Q ω)) μ :=
    tc4_aem_comp μ _ hcont P Q hP hQ
  refine Integrable.of_bound ha.aestronglyMeasurable (γstar * supNorm f₁ * supNorm f₂)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact lem_app_vol_finite_i hB γstar hdim Fm Gm hFm hGm f₁ f₂ hf₁ hf₂ _ _

private lemma tc4_abstract {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (a b D1 D2 : Ω → ℝ) (hai : Integrable a μ) (hbi : Integrable b μ)
    (hD1m : AEMeasurable D1 μ) (hD1 : ∀ ω, 0 ≤ D1 ω) (hD2 : ∀ ω, 0 ≤ D2 ω)
    (c1 c2 s : ℝ) (hc10 : 0 ≤ c1) (hc20 : 0 ≤ c2) (hs0 : 0 ≤ s)
    (hpt : ∀ ω, |a ω - b ω| ≤ c1 * D1 ω + c2 * D2 ω)
    (hE1 : ∫⁻ ω, ENNReal.ofReal (D1 ω) ∂μ ≤ ENNReal.ofReal s)
    (hE2 : ∫⁻ ω, ENNReal.ofReal (D2 ω) ∂μ ≤ ENNReal.ofReal s) :
    |(∫ ω, a ω ∂μ) - ∫ ω, b ω ∂μ| ≤ (c1 + c2) * s := by
  have hint : Integrable (fun ω => a ω - b ω) μ := hai.sub hbi
  have hG : ENNReal.ofReal (∫ ω, |a ω - b ω| ∂μ) ≤ ENNReal.ofReal ((c1 + c2) * s) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint.abs
      (Filter.Eventually.of_forall fun ω => abs_nonneg _)]
    calc ∫⁻ ω, ENNReal.ofReal |a ω - b ω| ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal c1 * ENNReal.ofReal (D1 ω) +
            ENNReal.ofReal c2 * ENNReal.ofReal (D2 ω)) ∂μ := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_mul hc10, ← ENNReal.ofReal_mul hc20,
            ← ENNReal.ofReal_add (mul_nonneg hc10 (hD1 ω)) (mul_nonneg hc20 (hD2 ω))]
          exact ENNReal.ofReal_le_ofReal (hpt ω)
      _ = ENNReal.ofReal c1 * ∫⁻ ω, ENNReal.ofReal (D1 ω) ∂μ +
          ENNReal.ofReal c2 * ∫⁻ ω, ENNReal.ofReal (D2 ω) ∂μ := by
          rw [lintegral_add_left' (hD1m.ennreal_ofReal.const_mul _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal c1 * ENNReal.ofReal s + ENNReal.ofReal c2 * ENNReal.ofReal s :=
          add_le_add (mul_le_mul' le_rfl hE1) (mul_le_mul' le_rfl hE2)
      _ = ENNReal.ofReal ((c1 + c2) * s) := by
          rw [← ENNReal.ofReal_mul hc10, ← ENNReal.ofReal_mul hc20,
            ← ENNReal.ofReal_add (mul_nonneg hc10 hs0) (mul_nonneg hc20 hs0)]
          congr 1; ring
  have hG' : ∫ ω, |a ω - b ω| ∂μ ≤ (c1 + c2) * s :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (add_nonneg hc10 hc20) hs0)).1 hG
  rw [← integral_sub hai hbi]
  exact (abs_integral_le_integral_abs).trans hG'


/-- `lem:app-vol-cutoff`, part (i), snapshot `cr-2026-10-23`. Declaration of record for this part:
the coupling `(K_1, K_2)` with `(M^g_t, M^g_{t+ℓ})` on the same samples, and the mean square bound
`(1/B)𝔼‖M^g_t − K_1‖_F² + (1/B)𝔼‖M^g_{t+ℓ} − K_2‖_F² ≤ 3 C_Σ² γ_⋆² δ_{J,R}²`. The expectations are
lower integrals of nonnegative functions. Verbatim LaTeX of the lemma (both parts):
```latex
\begin{lemma}[Removal of the cutoffs in the model]\label{lem:app-vol-cutoff}
Couple $(\mathsf K_1,\mathsf K_2)$ with $(M^{\mathrm g}_t,M^{\mathrm g}_{t+\ell})$ by building both from
the same samples. Under the size conditions, with $\delta_{J,R}$ of
\cref{eqn:app-vol-deltaJR},
\begin{equation}\label{eqn:app-vol-cutoff}
\frac1B\EE\norm{M^{\mathrm g}_t-\mathsf K_1}_\F^2+\frac1B\EE\norm{M^{\mathrm g}_{t+\ell}-\mathsf K_2}_\F^2\le3C_\Sigma^2\gamma_\star^2\delta_{J,R}^2 ,
\end{equation}
and for odd bounded Lipschitz $f_1,f_2$ and $\norm F,\norm G\le1$,
\[
\begin{aligned}
&\abs{\EE\,\mathcal K^{F,G}[f_1,f_2](M^{\mathrm g}_t,M^{\mathrm g}_{t+\ell})-\EE\,\mathcal K^{F,G}[f_1,f_2](\mathsf K_1,\mathsf K_2)}\\
&\qquad\le\sqrt3\,C_\Sigma\gamma_\star^{3/2}\big(\operatorname{Lip}(f_1)\norm{f_2}_\infty+\norm{f_1}_\infty\operatorname{Lip}(f_2)\big)\,\delta_{J,R}.
\end{aligned}
\]
\end{lemma}
```
-/
theorem lem_app_vol_cutoff_i (Fp : FrozenParams m n B) (ℓ J : ℕ) (R γstar CSig : ℝ)
    (hR : 0 < R) (hS : SizeFin Fp.C B γstar CSig) (t : ℤ) :
    ENNReal.ofReal ((B : ℝ)⁻¹) *
        ∫⁻ ω, ENNReal.ofReal (fro (def_app_vol_product Fp ω t - cutoffMat Fp ℓ J R t 1 ω) ^ 2)
          ∂(indepSpaceLaw m n B)
      + ENNReal.ofReal ((B : ℝ)⁻¹) *
        ∫⁻ ω, ENNReal.ofReal
            (fro (def_app_vol_product Fp ω (t + (ℓ : ℤ)) - cutoffMat Fp ℓ J R t 2 ω) ^ 2)
          ∂(indepSpaceLaw m n B)
      ≤ ENNReal.ofReal (3 * CSig ^ 2 * γstar ^ 2 * cutoffDelta Fp.β J R ^ 2) := by
  obtain ⟨h1, h2⟩ := tc4_cutoff_each Fp ℓ J R γstar CSig hS t
  refine (add_le_add h1 h2).trans ?_
  have hX : 0 ≤ CSig ^ 2 * γstar ^ 2 * cutoffDelta Fp.β J R ^ 2 := by positivity
  rw [← ENNReal.ofReal_add hX hX]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith

/-- `lem:app-vol-cutoff`, part (ii), snapshot `cr-2026-10-23`. Declaration of record for this part:
for odd bounded Lipschitz `f₁, f₂` and `‖F‖, ‖G‖ ≤ 1`, the difference of the tested contractions
`𝒦^{F,G}[f₁,f₂]` of the two couplings is at most
`√3 C_Σ γ_⋆^{3/2} (Lip(f₁)‖f₂‖_∞ + ‖f₁‖_∞ Lip(f₂)) δ_{J,R}`. The statement is the second display of
the lemma (see the verbatim LaTeX on `lem_app_vol_cutoff_i`). -/
theorem lem_app_vol_cutoff_ii (Fp : FrozenParams m n B) (ℓ J : ℕ) (R γstar CSig : ℝ)
    (hR : 0 < R) (hS : SizeFin Fp.C B γstar CSig) (t : ℤ) (Fm : Mat m m) (Gm : Mat n n)
    (hFm : opNorm Fm ≤ 1) (hGm : opNorm Gm ≤ 1) (f₁ f₂ : ℝ → ℝ)
    (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂) :
    |(∫ ω, contraction B Fm Gm f₁ f₂ (def_app_vol_product Fp ω t)
          (def_app_vol_product Fp ω (t + (ℓ : ℤ))) ∂(indepSpaceLaw m n B))
      - ∫ ω, contraction B Fm Gm f₁ f₂ (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω)
          ∂(indepSpaceLaw m n B)|
      ≤ Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) *
          (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) * cutoffDelta Fp.β J R := by
  classical
  have hBpos : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  haveI : IsProbabilityMeasure (indepSpaceLaw m n B) := by
    unfold indepSpaceLaw; infer_instance
  have hγ0 : 0 ≤ γstar := by
    have h1 := hS.1
    have h0 : (0 : ℝ) ≤ ((max m n : ℕ) : ℝ) := Nat.cast_nonneg _
    by_contra h
    push Not at h
    nlinarith
  have hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B :=
    (Nat.cast_le.2 ((min_le_left m n).trans (le_max_left m n))).trans hS.1
  have hC0 : 0 ≤ CSig := by
    have : 0 ≤ opNorm Fp.C.Sout := by
      unfold opNorm
      exact norm_nonneg _
    linarith [hS.2.1]
  obtain ⟨h1, h2⟩ := tc4_cutoff_each Fp ℓ J R γstar CSig hS t
  have hδ0 : 0 ≤ cutoffDelta Fp.β J R :=
    add_nonneg (pow_nonneg Fp.hβ.1 _) (Real.sqrt_nonneg _)
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = cutoffDelta Fp.β J R := ⟨_, rfl⟩
  rw [← hδ] at hδ0 h1 h2 ⊢
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (B : ℝ) * (CSig * γstar * δ) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hs2 : s ^ 2 = (B : ℝ) * (CSig ^ 2 * γstar ^ 2 * δ ^ 2) := by
    rw [hs, mul_pow, Real.sq_sqrt hBpos.le]; ring
  have hL2 : ∀ I : ℝ≥0∞, ENNReal.ofReal ((B : ℝ)⁻¹) * I ≤
      ENNReal.ofReal (CSig ^ 2 * γstar ^ 2 * δ ^ 2) → I ≤ ENNReal.ofReal (s ^ 2) := by
    intro I hI
    have e : I = ENNReal.ofReal (B : ℝ) * (ENNReal.ofReal ((B : ℝ)⁻¹) * I) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hBpos.le, mul_inv_cancel₀ hBpos.ne',
        ENNReal.ofReal_one, one_mul]
    rw [e, hs2, ENNReal.ofReal_mul hBpos.le]
    exact mul_le_mul' le_rfl hI
  -- measurability
  have hK1m := tc4_K_meas Fp R t (J + 1) (cutoffMat Fp ℓ J R t 1)
    (fun ω b c => tc4_cutoff_entries1 Fp ℓ J R t ω b c)
  have hK2m := tc4_K_meas Fp R (t + (ℓ : ℤ)) (ℓ + J + 1) (cutoffMat Fp ℓ J R t 2)
    (fun ω b c => tc4_cutoff_entries2 Fp ℓ J R t ω b c)
  have hM1 : AEMeasurable (fun ω => def_app_vol_product Fp ω t) (indepSpaceLaw m n B) :=
    aemeasurable_pi_iff.2 fun b => aemeasurable_pi_iff.2 fun c => tc4_entry_aem Fp t b c
  have hM2 : AEMeasurable (fun ω => def_app_vol_product Fp ω (t + (ℓ : ℤ)))
      (indepSpaceLaw m n B) :=
    aemeasurable_pi_iff.2 fun b => aemeasurable_pi_iff.2 fun c => tc4_entry_aem Fp _ b c
  have hK1 : Measurable (fun ω => cutoffMat Fp ℓ J R t 1 ω) :=
    measurable_pi_iff.2 fun b => measurable_pi_iff.2 fun c => hK1m b c
  have hK2 : Measurable (fun ω => cutoffMat Fp ℓ J R t 2 ω) :=
    measurable_pi_iff.2 fun b => measurable_pi_iff.2 fun c => hK2m b c
  have hai := tc4_contr_int (indepSpaceLaw m n B) Fp.hB γstar hdim Fm Gm hFm hGm f₁ f₂ hf₁ hf₂
    _ _ hM1 hM2
  have hbi := tc4_contr_int (indepSpaceLaw m n B) Fp.hB γstar hdim Fm Gm hFm hGm f₁ f₂ hf₁ hf₂
    _ _ hK1.aemeasurable hK2.aemeasurable
  have hD1 : ∀ b c, AEMeasurable (fun ω => (def_app_vol_product Fp ω t -
      cutoffMat Fp ℓ J R t 1 ω) b c) (indepSpaceLaw m n B) :=
    fun b c => (tc4_entry_aem Fp t b c).sub (hK1m b c).aemeasurable
  have hD2 : ∀ b c, AEMeasurable (fun ω => (def_app_vol_product Fp ω (t + (ℓ : ℤ)) -
      cutoffMat Fp ℓ J R t 2 ω) b c) (indepSpaceLaw m n B) :=
    fun b c => (tc4_entry_aem Fp _ b c).sub (hK2m b c).aemeasurable
  have hE1 := tc4_L1 (indepSpaceLaw m n B)
    (fun ω => fro (def_app_vol_product Fp ω t - cutoffMat Fp ℓ J R t 1 ω))
    (tc4_fro_aem _ _ hD1) s hs0 (hL2 _ h1)
  have hE2 := tc4_L1 (indepSpaceLaw m n B)
    (fun ω => fro (def_app_vol_product Fp ω (t + (ℓ : ℤ)) - cutoffMat Fp ℓ J R t 2 ω))
    (tc4_fro_aem _ _ hD2) s hs0 (hL2 _ h2)
  have hL1 := tc4_lip_nonneg f₁
  have hL2' := tc4_lip_nonneg f₂
  have hS1 := tc4_sup_nonneg f₁
  have hS2 := tc4_sup_nonneg f₂
  have hc10 : 0 ≤ Real.sqrt (γstar / B) * (lipConst f₁ * supNorm f₂) := by positivity
  have hc20 : 0 ≤ Real.sqrt (γstar / B) * (supNorm f₁ * lipConst f₂) := by positivity
  have hmain := tc4_abstract (indepSpaceLaw m n B) _ _ _ _ hai hbi
    (tc4_fro_aem _ _ hD1) (fun ω => by unfold fro; exact Real.sqrt_nonneg _)
    (fun ω => by unfold fro; exact Real.sqrt_nonneg _) _ _ s hc10 hc20 hs0
    (fun ω => by
      have := lem_app_vol_finite_ii Fp.hB γstar hdim Fm Gm hFm hGm f₁ f₂ hf₁ hf₂
        (def_app_vol_product Fp ω t) (cutoffMat Fp ℓ J R t 1 ω)
        (def_app_vol_product Fp ω (t + (ℓ : ℤ))) (cutoffMat Fp ℓ J R t 2 ω)
      refine this.trans (le_of_eq ?_)
      ring) hE1 hE2
  refine hmain.trans ?_
  -- arithmetic
  have hg : γstar ^ (3 / 2 : ℝ) = γstar * Real.sqrt γstar := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hγ0 (by norm_num),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hsq : Real.sqrt (γstar / B) * Real.sqrt (B : ℝ) = Real.sqrt γstar := by
    rw [← Real.sqrt_mul (div_nonneg hγ0 hBpos.le), div_mul_cancel₀ _ hBpos.ne']
  have hQ : (Real.sqrt (γstar / B) * (lipConst f₁ * supNorm f₂) +
      Real.sqrt (γstar / B) * (supNorm f₁ * lipConst f₂)) * s = CSig * γstar ^ (3 / 2 : ℝ) *
      (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) * δ := by
    rw [hs, hg]
    have : (Real.sqrt (γstar / B) * (lipConst f₁ * supNorm f₂) +
        Real.sqrt (γstar / B) * (supNorm f₁ * lipConst f₂)) * (Real.sqrt (B : ℝ) *
          (CSig * γstar * δ)) = (Real.sqrt (γstar / B) * Real.sqrt (B : ℝ)) *
        ((lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) * (CSig * γstar * δ)) := by ring
    rw [this, hsq]; ring
  rw [hQ]
  have h3 : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hQ0 : 0 ≤ CSig * γstar ^ (3 / 2 : ℝ) *
      (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) * δ := by
    have := Real.rpow_nonneg hγ0 (3 / 2 : ℝ)
    positivity
  calc CSig * γstar ^ (3 / 2 : ℝ) * (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) * δ
      ≤ Real.sqrt 3 * (CSig * γstar ^ (3 / 2 : ℝ) *
        (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) * δ) := le_mul_of_one_le_left hQ0 h3
    _ = _ := by ring

end Muon.Volatility

end

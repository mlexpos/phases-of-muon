import Muon.Foundations.Nuclear
import Muon.DetEquiv.Resolvent
import Muon.Setup.RegularizedMap
import Muon.Volatility.OddSpectral

/-!
# Appendix E: finite filter estimates (`lem:app-dyn-schatten`, `lem:app-dyn-second`)

Snapshot `cr-2026-10-23`. Source: `sections/05-dynamics/section.tex` ll. 599–609
(`lem:app-dyn-schatten`) and ll. 660–673 (`lem:app-dyn-second`). The unnumbered smoothness
claim of ll. 675–677 is promoted to the helper `Q_contDiffOn_pos`. Card:
`sections/05-dynamics/CARD.md` §2–§5 (work package L-E.5). Statements only; proofs are `sorry`.

Reused, not redefined: `Muon.Q` (`eqn:app-setup-Q`, `Muon.Foundations.Conventions`),
`Muon.DetEquiv.Xs` (`eqn:app-de-RXdef`), `Muon.nuc`, `Muon.opNorm`, `Muon.fro`,
`Muon.Mat`, `Muon.Vec`.

Design decisions (see also the result JSON `open_questions`):
* `S_p`, `p ∈ {1, ∞}`: `schatNorm p K` is `nuc K` at `p = 1` and `opNorm K` at `p = ∞`. Each
  statement carries `hp : p = 1 ∨ p = ⊤`, so the two instances of the source are covered by one
  declaration. The ideal property the proof needs is Foundations' `nuc_mul_three_le` (S_1) and
  `Matrix.l2_opNorm_mul` (S_∞); no `External` certificate is used (card §4 `SchattenIdeal` is
  superseded).
* Derivatives `∂_ϱ Q_ϱ(N)`, `D Q_ϱ(N)[R]`, `∂_ϱ² Q_ϱ(N)` are defined entrywise through `deriv`
  on `Matrix.of`, so no norm instance on `Matrix` is needed. Under `Q_contDiffOn_pos` they are the
  Fréchet derivatives in the source's sense.
* `lem:app-dyn-second`: the constant `C` is quantified before `∀ m n`, since it depends on
  `(ℓlo, ℓhi)` only. Each part carries its own `∃ C`. Every bound is monotone in `C`, so the
  conjunction of the four parts with separate constants is equivalent to the source's single `C`.
-/

set_option linter.style.longLine false

noncomputable section

open scoped Matrix MatrixOrder ENNReal ContDiff
open Matrix Set Filter Topology

namespace Muon.Dynamics

/-- `S_p` norm for the two values `p ∈ {1, ∞}` used by `lem:app-dyn-schatten`: the nuclear norm at
`p = 1`, the operator norm at `p = ∞` (`Muon.nuc`, `Muon.opNorm`). Values at other `p` are not used. -/
def schatNorm {m n : ℕ} (p : ENNReal) (K : Mat m n) : ℝ :=
  if p = 1 then nuc K else opNorm K

/-- Ridge derivative `∂_ϱ Q_ϱ(K)`, entrywise (`Matrix.of`). The derivative of the map `ϱ ↦ Q_ϱ(K)`. -/
def ridgeDeriv {m n : ℕ} (ϱ : ℝ) (K : Mat m n) : Mat m n :=
  Matrix.of fun i j => deriv (fun x : ℝ => Q x K i j) ϱ

/-- Directional derivative `D Q_ϱ(N)[R]`, entrywise: the derivative at `0` of `t ↦ Q_ϱ(N + tR)`. -/
def dirDeriv {m n : ℕ} (ϱ : ℝ) (N R : Mat m n) : Mat m n :=
  Matrix.of fun i j => deriv (fun t : ℝ => Q ϱ (N + t • R) i j) 0

/-- Second ridge derivative `∂_ϱ² Q_ϱ(K)`, entrywise. -/
def ridgeDeriv2 {m n : ℕ} (ϱ : ℝ) (K : Mat m n) : Mat m n :=
  Matrix.of fun i j => deriv (fun x : ℝ => ridgeDeriv x K i j) ϱ

section SqrtSmooth
open scoped Matrix.Norms.L2Operator

private theorem sylv_injective {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : 0 ≤ S) (hU : IsUnit S)
    (H : Matrix (Fin m) (Fin m) ℝ) (h : S * H + H * S = 0) : H = 0 := by
  set R := CFC.sqrt S with hR
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hS
  have hRs : Rᵀ = R := by
    have : IsSelfAdjoint R := (CFC.sqrt_nonneg S).isSelfAdjoint
    simpa [Matrix.star_eq_conjTranspose] using this.star_eq
  have e1 : Matrix.trace ((R * H)ᴴ * (R * H)) + Matrix.trace ((H * R)ᴴ * (H * R)) = 0 := by
    have hc : ∀ X : Matrix (Fin m) (Fin m) ℝ, Xᴴ = Xᵀ := fun X => rfl
    have a1 : (R * H)ᴴ * (R * H) = Hᵀ * (R * R) * H := by
      rw [hc, Matrix.transpose_mul, hRs]; simp only [Matrix.mul_assoc]
    have a2 : Matrix.trace ((H * R)ᴴ * (H * R)) = Matrix.trace (Hᵀ * H * (R * R)) := by
      rw [hc, Matrix.transpose_mul, hRs]
      have := Matrix.trace_mul_comm R (Hᵀ * (H * R))
      simp only [Matrix.mul_assoc] at this ⊢
      exact this
    rw [a1, a2, hRR, ← Matrix.trace_add]
    have : Hᵀ * S * H + Hᵀ * H * S = Hᵀ * (S * H + H * S) := by
      simp only [Matrix.mul_add, Matrix.mul_assoc]
    rw [this, h]; simp
  have n1 := (Matrix.posSemidef_conjTranspose_mul_self (R * H)).trace_nonneg
  have n2 := (Matrix.posSemidef_conjTranspose_mul_self (H * R)).trace_nonneg
  have z : Matrix.trace ((R * H)ᴴ * (R * H)) = 0 := by linarith
  have hRH : R * H = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp z
  have : S * H = 0 := by rw [← hRR, Matrix.mul_assoc, hRH, Matrix.mul_zero]
  obtain ⟨u, rfl⟩ := hU
  have := congrArg (fun X => (↑u⁻¹ : Matrix (Fin m) (Fin m) ℝ) * X) this
  simpa [← Matrix.mul_assoc] using this


private theorem sqrt_local {m : ℕ} (A0 : Matrix (Fin m) (Fin m) ℝ) (hA0 : 0 ≤ A0) (hU : IsUnit A0) :
    ∃ g : Matrix (Fin m) (Fin m) ℝ → Matrix (Fin m) (Fin m) ℝ,
      ContDiffAt ℝ ∞ g A0 ∧ g A0 = CFC.sqrt A0 ∧
      ∀ᶠ A in 𝓝 A0, 0 ≤ A → g A = CFC.sqrt A := by
  set S0 := CFC.sqrt A0 with hS0
  have hS0sq : S0 * S0 = A0 := CFC.sqrt_mul_sqrt_self A0 hA0
  have hS0nn : 0 ≤ S0 := CFC.sqrt_nonneg A0
  have hS0U : IsUnit S0 := by
    have : IsUnit (S0 * S0) := hS0sq ▸ hU
    exact (isUnit_mul_self_iff.mp this)
  set F : Matrix (Fin m) (Fin m) ℝ → Matrix (Fin m) (Fin m) ℝ := fun S => S * S with hF
  have hFc : ContDiff ℝ ∞ F := contDiff_id.mul contDiff_id
  set L : Matrix (Fin m) (Fin m) ℝ →L[ℝ] Matrix (Fin m) (Fin m) ℝ :=
    ContinuousLinearMap.mul ℝ _ S0 + (ContinuousLinearMap.mul ℝ _).flip S0 with hL
  have hLapp : ∀ H, L H = S0 * H + H * S0 := fun H => by simp [hL]
  have hFd : HasFDerivAt F L S0 := by
    have := (hasFDerivAt_id (𝕜 := ℝ) S0).mul' (hasFDerivAt_id (𝕜 := ℝ) S0)
    refine this.congr_fderiv ?_
    ext H : 1
    simp [hLapp]
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro H hH
    exact sylv_injective S0 hS0nn hS0U H (by rw [← hLapp]; exact hH)
  let Le : Matrix (Fin m) (Fin m) ℝ ≃L[ℝ] Matrix (Fin m) (Fin m) ℝ :=
    (LinearEquiv.ofInjectiveEndo L.toLinearMap hinj).toContinuousLinearEquiv
  have hLe : (Le : Matrix (Fin m) (Fin m) ℝ →L[ℝ] Matrix (Fin m) (Fin m) ℝ) = L := by
    ext H : 1; rfl
  have hFd' : HasFDerivAt F (Le : Matrix (Fin m) (Fin m) ℝ →L[ℝ] Matrix (Fin m) (Fin m) ℝ) S0 := by
    rw [hLe]; exact hFd
  have hFs : HasStrictFDerivAt F (Le : Matrix (Fin m) (Fin m) ℝ →L[ℝ] Matrix (Fin m) (Fin m) ℝ) S0 :=
    (hFc.contDiffAt.hasStrictFDerivAt (by simp)).congr_fderiv (by rw [hFd'.fderiv])
  have hcd : ContDiffAt ℝ ∞ F S0 := hFc.contDiffAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hFs.localInverse F Le S0, ?_, ?_, ?_⟩
  · have := hcd.to_localInverse hFd' hn
    rwa [show F S0 = A0 from hS0sq] at this
  · have := hFs.localInverse_apply_image
    rwa [show F S0 = A0 from hS0sq] at this
  · have hleft := hFs.eventually_left_inverse
    have hcont : ContinuousWithinAt CFC.sqrt {a : Matrix (Fin m) (Fin m) ℝ | 0 ≤ a} A0 :=
      CFC.continuousOn_sqrt A0 hA0
    have ht : ∀ᶠ A in 𝓝[{a : Matrix (Fin m) (Fin m) ℝ | 0 ≤ a}] A0, CFC.sqrt A ∈ {x | hFs.localInverse F Le S0 (F x) = x} :=
      hcont.tendsto.eventually (by exact hleft)
    rw [eventually_nhdsWithin_iff] at ht
    filter_upwards [ht] with A hA hA0'
    have h1 : hFs.localInverse F Le S0 (F (CFC.sqrt A)) = CFC.sqrt A := hA hA0'
    have h2 : F (CFC.sqrt A) = A := CFC.sqrt_mul_sqrt_self A hA0'
    rw [h2] at h1
    exact h1


private theorem Q_contDiffOn_pos_aux (m n : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : (Fin m → Fin n → ℝ) × ℝ => fun i j => Q p.2 (Matrix.of p.1) i j)
      {p | 0 < p.2} := by
  intro p0 hp0
  have hp0' : 0 < p0.2 := hp0
  refine ContDiffAt.contDiffWithinAt ?_
  let e : Matrix (Fin m) (Fin m) ℝ ≃L[ℝ] (Fin m → Fin m → ℝ) :=
    (Matrix.ofLinearEquiv ℝ).symm.toContinuousLinearEquiv
  let A : (Fin m → Fin n → ℝ) × ℝ → Matrix (Fin m) (Fin m) ℝ :=
    fun p => Matrix.of p.1 * (Matrix.of p.1)ᵀ + p.2 • (1 : Matrix (Fin m) (Fin m) ℝ)
  have hA : ContDiff ℝ ∞ A := by
    have h1 : ContDiff ℝ ∞ (fun p => e (A p)) := by
      refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
      have hent : ∀ p : (Fin m → Fin n → ℝ) × ℝ, e (A p) i j =
          ∑ k, p.1 i k * p.1 j k + (if i = j then p.2 else 0) := by
        intro p
        simp [e, A, Matrix.mul_apply, Matrix.one_apply, Matrix.ofLinearEquiv]
      simp only [hent]
      refine ContDiff.add (ContDiff.sum fun k _ => ?_) ?_
      · have c1 : ContDiff ℝ ∞ (fun p : (Fin m → Fin n → ℝ) × ℝ => p.1 i k) :=
          ((contDiff_apply ℝ ℝ k).comp (contDiff_apply ℝ _ i)).comp contDiff_fst
        have c2 : ContDiff ℝ ∞ (fun p : (Fin m → Fin n → ℝ) × ℝ => p.1 j k) :=
          ((contDiff_apply ℝ ℝ k).comp (contDiff_apply ℝ _ j)).comp contDiff_fst
        exact c1.mul c2
      · by_cases hij : i = j
        · simpa [hij] using contDiff_snd
        · simpa [hij] using contDiff_const
    have h2 := e.symm.contDiff.comp h1
    have h3 : (e.symm ∘ fun p => e (A p)) = A := funext fun p => by simp
    rwa [h3] at h2
  have hAnn : ∀ p : (Fin m → Fin n → ℝ) × ℝ, 0 ≤ p.2 → 0 ≤ A p := by
    intro p hp
    have hB0 : 0 ≤ Matrix.of p.1 * (Matrix.of p.1)ᵀ := by
      rw [Matrix.nonneg_iff_posSemidef]
      simpa using Matrix.posSemidef_conjTranspose_mul_self (Matrix.of p.1)ᵀ
    exact add_nonneg hB0 (smul_nonneg hp zero_le_one)
  have hAU : ∀ p : (Fin m → Fin n → ℝ) × ℝ, 0 < p.2 → IsUnit (A p) := by
    intro p hp
    have h0 : (Matrix.of p.1 * (Matrix.of p.1)ᵀ).PosSemidef := by
      simpa using Matrix.posSemidef_self_mul_conjTranspose (Matrix.of p.1)
    have hd : (p.2 • (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef := by
      have : p.2 • (1 : Matrix (Fin m) (Fin m) ℝ) = Matrix.diagonal (fun _ : Fin m => p.2) := by
        ext i j
        by_cases h : i = j <;> simp [h]
      rw [this]
      exact Matrix.posDef_diagonal_iff.mpr (fun _ => hp)
    have : (A p).PosDef := by
      show (Matrix.of p.1 * (Matrix.of p.1)ᵀ + p.2 • (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef
      rw [add_comm]
      exact hd.add_posSemidef h0
    exact this.isUnit
  obtain ⟨g, hg, hg0, hgev⟩ := sqrt_local (A p0) (hAnn p0 hp0'.le) (hAU p0 hp0')
  have hSU : IsUnit (g (A p0)) := by
    rw [hg0]
    have h := hAU p0 hp0'
    have hsq : CFC.sqrt (A p0) * CFC.sqrt (A p0) = A p0 :=
      CFC.sqrt_mul_sqrt_self _ (hAnn p0 hp0'.le)
    have h' : IsUnit (CFC.sqrt (A p0) * CFC.sqrt (A p0)) := by rw [hsq]; exact h
    exact isUnit_mul_self_iff.mp h'
  have hGd : ContDiffAt ℝ ∞ (fun p => Ring.inverse (g (A p))) p0 := by
    have h1 := contDiffAt_ringInverse ℝ (n := ∞) hSU.unit
    have h2 : ContDiffAt ℝ ∞ (fun p => g (A p)) p0 := hg.comp p0 hA.contDiffAt
    have h1' : ContDiffAt ℝ ∞ Ring.inverse (g (A p0)) := by
      simpa using h1
    exact h1'.comp p0 h2
  have hev1 : ∀ᶠ p in 𝓝 p0, 0 ≤ A p → g (A p) = CFC.sqrt (A p) :=
    hA.continuous.continuousAt.eventually hgev
  have hev2 : ∀ᶠ p : (Fin m → Fin n → ℝ) × ℝ in 𝓝 p0, 0 < p.2 :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hp0'
  have hEq : (fun p : (Fin m → Fin n → ℝ) × ℝ => fun i j => Q p.2 (Matrix.of p.1) i j) =ᶠ[𝓝 p0]
      (fun p => fun i j => ∑ k, (Ring.inverse (g (A p))) i k * p.1 k j) := by
    filter_upwards [hev1, hev2] with p h1 h2
    have hq := Q_eq_inv_sqrt_mul h2 (Matrix.of p.1)
    have hAeq : Matrix.of p.1 * (Matrix.of p.1)ᵀ + p.2 • (1 : Matrix (Fin m) (Fin m) ℝ) = A p := rfl
    rw [hAeq] at hq
    rw [← h1 (hAnn p h2.le), Matrix.nonsing_inv_eq_ringInverse] at hq
    funext i j
    rw [hq, Matrix.mul_apply]
    rfl
  refine ContDiffAt.congr_of_eventuallyEq ?_ hEq
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  refine ContDiffAt.sum fun k _ => ?_
  refine ContDiffAt.mul ?_ ?_
  · have h3 : ContDiffAt ℝ ∞ (fun p => e (Ring.inverse (g (A p)))) p0 := e.contDiff.contDiffAt.comp p0 hGd
    exact contDiffAt_pi.1 (contDiffAt_pi.1 h3 i) k
  · exact ((contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ _ k)).comp contDiff_fst |>.contDiffAt

end SqrtSmooth

/-- Helper promoted from the unnumbered claim of `section.tex` ll. 675–677 (proof of
`lem:app-dyn-second`): "The map `(N,ℓ) ↦ Q_ℓ(N)` is smooth on `ℓ > 0`, by the integral representation of
`lem:app-setup-contour`, so the derivatives in the statement exist." Entries are written in the
coordinates `Fin m → Fin n → ℝ` of `Mat m n`. -/
theorem Q_contDiffOn_pos (m n : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : (Fin m → Fin n → ℝ) × ℝ => fun i j => Q p.2 (Matrix.of p.1) i j)
      {p | 0 < p.2} := by
  exact Q_contDiffOn_pos_aux m n

/-! ### Private helpers for `lem_app_dyn_schatten_i`, `_ii` (task P-E.5.P1) -/

section FilterAux

open Muon.DetEquiv

private lemma fl_dot_mulVec {a b : ℕ} (K : Mat a b) (y : Vec a) (x : Vec b) :
    y ⬝ᵥ (K *ᵥ x) = (Kᵀ *ᵥ y) ⬝ᵥ x := by
  rw [Matrix.dotProduct_mulVec]
  have h := Matrix.vecMul_transpose Kᵀ y
  rw [Matrix.transpose_transpose] at h
  rw [h]

open scoped Matrix.Norms.L2Operator in
private lemma fl_opNorm_le {a b : ℕ} (K : Mat a b) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Vec b, sqNorm (K *ᵥ x) ≤ c ^ 2 * sqNorm x) : opNorm K ≤ c := by
  rw [opNorm_eq_norm, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  show ‖(EuclideanSpace.equiv (Fin a) ℝ).symm (K *ᵥ (EuclideanSpace.equiv (Fin b) ℝ x))‖
      ≤ c * ‖x‖
  have hx : sqNorm (EuclideanSpace.equiv (Fin b) ℝ x) = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [sqNorm, Real.norm_eq_abs, sq_abs]
  have hy : sqNorm (K *ᵥ (EuclideanSpace.equiv (Fin b) ℝ x))
      = ‖(EuclideanSpace.equiv (Fin a) ℝ).symm (K *ᵥ (EuclideanSpace.equiv (Fin b) ℝ x))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [sqNorm, Real.norm_eq_abs, sq_abs]
  have h2 := h (EuclideanSpace.equiv (Fin b) ℝ x)
  rw [hx, hy] at h2
  refine le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hc (norm_nonneg _)) ?_
  rw [mul_pow]
  exact h2

private lemma fl_sq_mulVec_le {m n : ℕ} (U : Mat m n) (x : Vec n) :
    sqNorm (U *ᵥ x) ≤ opNorm U ^ 2 * sqNorm x := by
  have hb : ‖Matrix.toEuclideanLin U (WithLp.toLp 2 x)‖ ≤ opNorm U * ‖WithLp.toLp 2 x‖ :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin U)).le_opNorm (WithLp.toLp 2 x)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)] at hsq
  simpa [sqNorm, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Real.norm_eq_abs, sq_abs] using hsq

private lemma fl_sqNorm_nonneg {a : ℕ} (x : Vec a) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma fl_sqNorm_eq_dot {a : ℕ} (x : Vec a) : sqNorm x = x ⬝ᵥ x := by
  simp [sqNorm, dotProduct, sq]

private lemma fl_cs {a : ℕ} (y x : Vec a) : (y ⬝ᵥ x) ^ 2 ≤ sqNorm y * sqNorm x := by
  simpa [dotProduct, sqNorm] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y x

/-- one term: `(a ⬝ N p)² ≤ μ² |a|² |p|²`. -/
private lemma fl_term_sq {a b : ℕ} (N : Mat a b) (μ : ℝ) (hN : opNorm N ≤ μ) (u : Vec a) (p : Vec b) :
    (u ⬝ᵥ (N *ᵥ p)) ^ 2 ≤ μ ^ 2 * (sqNorm u * sqNorm p) := by
  have h1 := fl_cs u (N *ᵥ p)
  have h2 := fl_sq_mulVec_le N p
  have hμ : opNorm N ^ 2 ≤ μ ^ 2 := by
    have : 0 ≤ opNorm N := by
      rw [show opNorm N = ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin N)‖ from rfl]
      exact norm_nonneg _
    exact pow_le_pow_left₀ this hN 2
  have hu := fl_sqNorm_nonneg u
  have hp := fl_sqNorm_nonneg p
  calc (u ⬝ᵥ (N *ᵥ p)) ^ 2 ≤ sqNorm u * sqNorm (N *ᵥ p) := h1
    _ ≤ sqNorm u * (opNorm N ^ 2 * sqNorm p) := mul_le_mul_of_nonneg_left h2 hu
    _ ≤ sqNorm u * (μ ^ 2 * sqNorm p) := by gcongr
    _ = μ ^ 2 * (sqNorm u * sqNorm p) := by ring

private lemma fl_core {m n a b a' b' : ℕ} {s : ℝ} (hs : 0 < s)
    (F1 : Mat m a) (N1 : Mat a b) (G1 : Mat b n) (F2 : Mat m a') (N2 : Mat a' b') (G2 : Mat b' n)
    {μ : ℝ} (hμ : 0 ≤ μ) (h1 : opNorm N1 ≤ μ) (h2 : opNorm N2 ≤ μ)
    (hy : ∀ y : Vec m, sqNorm (F1ᵀ *ᵥ y) + s * sqNorm (F2ᵀ *ᵥ y) ≤ sqNorm y / s)
    (hx : ∀ x : Vec n, sqNorm (G1 *ᵥ x) + s * sqNorm (G2 *ᵥ x) ≤ sqNorm x / s) :
    opNorm (s • (F2 * N2 * G2) - F1 * N1 * G1) ≤ μ / s := by
  refine fl_opNorm_le _ (div_nonneg hμ hs.le) fun x => ?_
  set Φ := s • (F2 * N2 * G2) - F1 * N1 * G1 with hΦ
  set y := Φ *ᵥ x with hy_def
  set Y := sqNorm y with hY
  set Xn := sqNorm x with hXn
  have hYnn : 0 ≤ Y := fl_sqNorm_nonneg _
  have hXnn : 0 ≤ Xn := fl_sqNorm_nonneg _
  have hYdot : Y = y ⬝ᵥ (Φ *ᵥ x) := by rw [hY, fl_sqNorm_eq_dot]
  have hF : ∀ {a b : ℕ} (F : Mat m a) (N : Mat a b) (G : Mat b n),
      y ⬝ᵥ ((F * N * G) *ᵥ x) = (Fᵀ *ᵥ y) ⬝ᵥ (N *ᵥ (G *ᵥ x)) := by
    intro a b F N G
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, fl_dot_mulVec]
  have hexp : y ⬝ᵥ (Φ *ᵥ x) = s * ((F2ᵀ *ᵥ y) ⬝ᵥ (N2 *ᵥ (G2 *ᵥ x)))
      - (F1ᵀ *ᵥ y) ⬝ᵥ (N1 *ᵥ (G1 *ᵥ x)) := by
    rw [hΦ, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul, hF, hF]
  set T1 := (F1ᵀ *ᵥ y) ⬝ᵥ (N1 *ᵥ (G1 *ᵥ x)) with hT1
  set T2 := (F2ᵀ *ᵥ y) ⬝ᵥ (N2 *ᵥ (G2 *ᵥ x)) with hT2
  have e1 := fl_term_sq N1 μ h1 (F1ᵀ *ᵥ y) (G1 *ᵥ x)
  have e2 := fl_term_sq N2 μ h2 (F2ᵀ *ᵥ y) (G2 *ᵥ x)
  set A1 := sqNorm (F1ᵀ *ᵥ y)
  set A2 := sqNorm (F2ᵀ *ᵥ y)
  set B1 := sqNorm (G1 *ᵥ x)
  set B2 := sqNorm (G2 *ᵥ x)
  have hA1 : 0 ≤ A1 := fl_sqNorm_nonneg _
  have hA2 : 0 ≤ A2 := fl_sqNorm_nonneg _
  have hB1 : 0 ≤ B1 := fl_sqNorm_nonneg _
  have hB2 : 0 ≤ B2 := fl_sqNorm_nonneg _
  have hyy := hy y
  have hxx := hx x
  -- sqrt variables
  set α1 := Real.sqrt A1
  set α2 := Real.sqrt A2
  set β1 := Real.sqrt B1
  set β2 := Real.sqrt B2
  have ha1 : α1 ^ 2 = A1 := Real.sq_sqrt hA1
  have ha2 : α2 ^ 2 = A2 := Real.sq_sqrt hA2
  have hb1 : β1 ^ 2 = B1 := Real.sq_sqrt hB1
  have hb2 : β2 ^ 2 = B2 := Real.sq_sqrt hB2
  have p1 : 0 ≤ α1 := Real.sqrt_nonneg _
  have p2 : 0 ≤ α2 := Real.sqrt_nonneg _
  have q1 : 0 ≤ β1 := Real.sqrt_nonneg _
  have q2 : 0 ≤ β2 := Real.sqrt_nonneg _
  have hT1b : |T1| ≤ μ * (α1 * β1) := by
    apply abs_le_of_sq_le_sq _ (by positivity)
    calc T1 ^ 2 ≤ μ ^ 2 * (A1 * B1) := e1
      _ = (μ * (α1 * β1)) ^ 2 := by rw [mul_pow, mul_pow, ha1, hb1]
  have hT2b : |T2| ≤ μ * (α2 * β2) := by
    apply abs_le_of_sq_le_sq _ (by positivity)
    calc T2 ^ 2 ≤ μ ^ 2 * (A2 * B2) := e2
      _ = (μ * (α2 * β2)) ^ 2 := by rw [mul_pow, mul_pow, ha2, hb2]
  have hE : (α1 * β1 + s * (α2 * β2)) ^ 2 ≤ (Y / s) * (Xn / s) := by
    have hcs : (α1 * β1 + s * (α2 * β2)) ^ 2 ≤ (A1 + s * A2) * (B1 + s * B2) := by
      rw [← ha1, ← ha2, ← hb1, ← hb2]
      nlinarith [mul_nonneg hs.le (sq_nonneg (α1 * β2 - α2 * β1))]
    calc _ ≤ (A1 + s * A2) * (B1 + s * B2) := hcs
      _ ≤ (Y / s) * (Xn / s) := by
        apply mul_le_mul hyy hxx (by positivity) (by positivity)
  have hYle : Y ≤ μ * (α1 * β1 + s * (α2 * β2)) := by
    have : Y = s * T2 - T1 := by rw [hYdot, hexp]
    have h3 : s * T2 ≤ s * |T2| := mul_le_mul_of_nonneg_left (le_abs_self _) hs.le
    have h4 : -T1 ≤ |T1| := neg_le_abs _
    nlinarith [mul_le_mul_of_nonneg_left hT2b hs.le]
  have hEnn : 0 ≤ α1 * β1 + s * (α2 * β2) := by positivity
  rcases eq_or_lt_of_le hYnn with h0 | hpos
  · rw [← h0]; positivity
  · have hsq : Y ^ 2 ≤ μ ^ 2 * ((Y / s) * (Xn / s)) := by
      calc Y ^ 2 ≤ (μ * (α1 * β1 + s * (α2 * β2))) ^ 2 := pow_le_pow_left₀ hYnn hYle 2
        _ = μ ^ 2 * (α1 * β1 + s * (α2 * β2)) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hE (by positivity)
    have : Y * Y ≤ Y * ((μ / s) ^ 2 * Xn) := by
      calc Y * Y = Y ^ 2 := by ring
        _ ≤ μ ^ 2 * ((Y / s) * (Xn / s)) := hsq
        _ = Y * ((μ / s) ^ 2 * Xn) := by field_simp
    exact le_of_mul_le_mul_left this hpos

private lemma fl_Rs_symm {a b : ℕ} (K : Mat a b) (s : ℝ) : (Rs K s)ᵀ = Rs K s := by
  unfold Rs
  rw [Matrix.transpose_nonsing_inv]
  simp [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_smul]

private lemma fl_Rts_symm {a b : ℕ} (K : Mat a b) (s : ℝ) : (Rts K s)ᵀ = Rts K s := by
  unfold Rts
  rw [Matrix.transpose_nonsing_inv]
  simp [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_smul]

private lemma fl_Rts_eq {a b : ℕ} (K : Mat a b) (s : ℝ) : Rs Kᵀ s = Rts K s := by
  unfold Rs Rts
  simp

private lemma fl_Xs_T_mulVec {a b : ℕ} (K : Mat a b) (s : ℝ) (y : Vec a) :
    (Xs K s)ᵀ *ᵥ y = Kᵀ *ᵥ (Rs K s *ᵥ y) := by
  unfold Xs
  rw [Matrix.transpose_mul, fl_Rs_symm, Matrix.mulVec_mulVec]

private lemma fl_Xs_mulVec {a b : ℕ} (K : Mat a b) (s : ℝ) (hs : 0 < s) (x : Vec b) :
    Xs K s *ᵥ x = K *ᵥ (Rts K s *ᵥ x) := by
  unfold Xs
  rw [(lem_app_de_resolvent K s hs).2.2.2.1, ← Matrix.mulVec_mulVec]

private lemma fl_S1 {a b : ℕ} (K : Mat a b) {s : ℝ} (hs : 0 < s) (y : Vec a) :
    sqNorm (Kᵀ *ᵥ (Rs K s *ᵥ y)) + s * sqNorm (Rs K s *ᵥ y) ≤ sqNorm y / s := by
  have h6 := (lem_app_de_resolvent K s hs).2.2.2.2.2.1
  have hRA : Rs K s * (K * Kᵀ + s • (1 : Mat a a)) = 1 := by
    rw [Matrix.mul_add, h6, Matrix.mul_smul, Matrix.mul_one]; simp
  have hAR : (K * Kᵀ + s • (1 : Mat a a)) * Rs K s = 1 := mul_eq_one_comm.mp hRA
  set z := Rs K s *ᵥ y with hz
  have hy : (K * Kᵀ + s • (1 : Mat a a)) *ᵥ z = y := by
    rw [hz, Matrix.mulVec_mulVec, hAR, Matrix.one_mulVec]
  have hP : z ⬝ᵥ y = sqNorm (Kᵀ *ᵥ z) + s * sqNorm z := by
    rw [← hy, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec, fl_dot_mulVec, fl_sqNorm_eq_dot,
      fl_sqNorm_eq_dot]
  have hcs := fl_cs z y
  have h1 := fl_sqNorm_nonneg (Kᵀ *ᵥ z)
  have h2 := fl_sqNorm_nonneg z
  have h3 := fl_sqNorm_nonneg y
  set P := sqNorm (Kᵀ *ᵥ z) + s * sqNorm z with hPdef
  rw [hP] at hcs
  have hPnn : 0 ≤ P := by positivity
  rcases eq_or_lt_of_le hPnn with h0 | hpos
  · rw [← h0]; exact div_nonneg h3 hs.le
  · have : s * P ≤ sqNorm y := by
      by_contra hcon
      push Not at hcon
      have h4 : s * sqNorm z ≤ P := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h4 h3]
    rw [le_div_iff₀ hs]
    linarith

private lemma fl_S2 {a b : ℕ} (K : Mat a b) {s : ℝ} (hs : 0 < s) (x : Vec b) :
    sqNorm (K *ᵥ (Rts K s *ᵥ x)) + s * sqNorm (Rts K s *ᵥ x) ≤ sqNorm x / s := by
  have h := fl_S1 Kᵀ hs x
  rw [fl_Rts_eq, Matrix.transpose_transpose] at h
  exact h

private lemma fl_ident {m n : ℕ} (K K' : Mat m n) {s : ℝ} (hs : 0 < s) :
    Xs K s - Xs K' s = s • (Rs K s * (K - K') * Rts K' s) - Xs K s * (K - K')ᵀ * Xs K' s := by
  have h5 := (lem_app_de_resolvent K' s hs).2.2.2.2.1
  have h6 := (lem_app_de_resolvent K s hs).2.2.2.2.2.1
  have h4 := (lem_app_de_resolvent K' s hs).2.2.2.1
  have e1 : Xs K s * Kᵀ = 1 - s • Rs K s := by unfold Xs; rw [Matrix.mul_assoc]; exact h6
  have e2 : K'ᵀ * Xs K' s = 1 - s • Rts K' s := by unfold Xs; rw [← Matrix.mul_assoc]; exact h5
  have e3 : Xs K' s = K' * Rts K' s := by unfold Xs; exact h4
  have t1 : Xs K s * (K - K')ᵀ * Xs K' s
      = (1 - s • Rs K s) * Xs K' s - Xs K s * (1 - s • Rts K' s) := by
    rw [Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul, e1, Matrix.mul_assoc, e2]
  have t2 : s • (Rs K s * (K - K') * Rts K' s)
      = s • (Xs K s * Rts K' s) - s • (Rs K s * Xs K' s) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, smul_sub, Matrix.mul_assoc (Rs K s) K', ← e3]
    rfl
  rw [t1, t2]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_sub]
  abel

private lemma fl_opNorm_transpose {m n : ℕ} (A : Mat m n) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma fl_opNorm_nonneg {m n : ℕ} (A : Mat m n) : 0 ≤ opNorm A := by
  rw [show opNorm A = ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖ from rfl]
  exact norm_nonneg _

/-- Operator-norm form of (i). -/
private lemma fl_op_bound {m n : ℕ} (K K' : Mat m n) {s : ℝ} (hs : 0 < s) :
    opNorm (Xs K s - Xs K' s) ≤ s⁻¹ * opNorm (K - K') := by
  rw [fl_ident K K' hs, inv_mul_eq_div]
  exact fl_core (m := m) (n := n) hs (Xs K s) (K - K')ᵀ (Xs K' s) (Rs K s) (K - K') (Rts K' s)
    (μ := opNorm (K - K')) (fl_opNorm_nonneg _) (by rw [fl_opNorm_transpose]) le_rfl
    (fun y => by rw [fl_Xs_T_mulVec, fl_Rs_symm]; exact fl_S1 K hs y)
    (fun x => by rw [fl_Xs_mulVec K' s hs]; exact fl_S2 K' hs x)

private lemma fl_cyc_a {m n : ℕ} (S : Mat n n) (Δ : Mat m n) (R' : Mat m m) (U : Mat m n) :
    Matrix.trace (S * (Δᵀ * R') * U) = Matrix.trace (R' * U * S * Δᵀ) := by
  rw [show S * (Δᵀ * R') * U = (S * Δᵀ) * (R' * U) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

private lemma fl_cyc_b {m n : ℕ} (P : Mat n m) (Δ : Mat m n) (Q : Mat n m) (U : Mat m n) :
    Matrix.trace (P * (Δ * Q) * U) = Matrix.trace (Q * U * P * Δ) := by
  rw [show P * (Δ * Q) * U = (P * Δ) * (Q * U) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

private lemma fl_trace {m n : ℕ} (K K' : Mat m n) {s : ℝ} (hs : 0 < s) (U : Mat m n) :
    2 * Matrix.trace (Uᵀ * (Xs K s - Xs K' s)) =
      Matrix.trace ((s • (Rts K' s * Uᵀ * Rs K s) - (Xs K' s)ᵀ * U * (Xs K s)ᵀ) * (K - K')) +
      Matrix.trace ((s • (Rs K' s * U * Rts K s) - Xs K' s * Uᵀ * Xs K s) * (K - K')ᵀ) := by
  have hZ1 := fl_ident K K' hs
  have hZ2 : Xs K s - Xs K' s = s • (Rs K' s * (K - K') * Rts K s) - Xs K' s * (K - K')ᵀ * Xs K s := by
    have h := fl_ident K' K hs
    have hn : K' - K = -(K - K') := by abel
    rw [hn, Matrix.mul_neg, Matrix.neg_mul, Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul] at h
    rw [← neg_sub, h]
    rw [smul_neg]; abel
  set R := Rs K s
  set R' := Rs K' s
  set S := Rts K s
  set S' := Rts K' s
  set X := Xs K s
  set X' := Xs K' s
  set Δ := K - K' with hΔ
  have hR := fl_Rs_symm K s
  have hR' := fl_Rs_symm K' s
  have hS := fl_Rts_symm K s
  have hS' := fl_Rts_symm K' s
  set Z := X - X' with hZ
  -- A : first form
  have hA : Matrix.trace (Uᵀ * Z) =
      s * Matrix.trace ((S' * Uᵀ * R) * Δ) - Matrix.trace ((X' * Uᵀ * X) * Δᵀ) := by
    rw [hZ1, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    congr 1
    · congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
      simp only [Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
      simp only [Matrix.mul_assoc]
  have hB : Matrix.trace (Uᵀ * Z) =
      s * Matrix.trace ((R' * U * S) * Δᵀ) - Matrix.trace ((X'ᵀ * U * Xᵀ) * Δ) := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose, hZ2,
      Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hS, hR',
      Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [fl_cyc_a, fl_cyc_b]
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_sub, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  linarith [hA, hB]

private lemma fl_nuc_bound {m n : ℕ} (K K' : Mat m n) {s : ℝ} (hs : 0 < s) :
    nuc (Xs K s - Xs K' s) ≤ s⁻¹ * nuc (K - K') := by
  obtain ⟨U, hU, htr⟩ := (nuc_isGreatest_dual (Xs K s - Xs K' s)).1
  have hT := fl_trace K K' hs U
  rw [← htr] at hT
  have hUT : opNorm Uᵀ ≤ 1 := by rw [fl_opNorm_transpose]; exact hU
  have hW21 : opNorm (s • (Rts K' s * Uᵀ * Rs K s) - (Xs K' s)ᵀ * U * (Xs K s)ᵀ) ≤ 1 / s :=
    fl_core (m := n) (n := m) hs (Xs K' s)ᵀ U (Xs K s)ᵀ (Rts K' s) Uᵀ (Rs K s)
      (μ := 1) zero_le_one hU hUT
      (fun y => by
        rw [Matrix.transpose_transpose, fl_Xs_mulVec K' s hs, fl_Rts_symm]; exact fl_S2 K' hs y)
      (fun x => by rw [fl_Xs_T_mulVec]; exact fl_S1 K hs x)
  have hW12 : opNorm (s • (Rs K' s * U * Rts K s) - Xs K' s * Uᵀ * Xs K s) ≤ 1 / s :=
    fl_core (m := m) (n := n) hs (Xs K' s) Uᵀ (Xs K s) (Rs K' s) U (Rts K s)
      (μ := 1) zero_le_one hUT hU
      (fun y => by rw [fl_Xs_T_mulVec, fl_Rs_symm]; exact fl_S1 K' hs y)
      (fun x => by rw [fl_Xs_mulVec K s hs]; exact fl_S2 K hs x)
  have t1 := trace_mul_le_opNorm_mul_nuc _ (K - K') |>.trans
    (mul_le_mul_of_nonneg_right hW21 (nuc_nonneg _))
  have t2 := trace_mul_le_opNorm_mul_nuc _ (K - K')ᵀ |>.trans
    (mul_le_mul_of_nonneg_right hW12 (nuc_nonneg _))
  rw [nuc_transpose] at t2
  have := (le_abs_self _).trans t1
  have := (le_abs_self _).trans t2
  rw [inv_eq_one_div]
  have e : 1 / s * nuc (K - K') = (1 / s * nuc (K - K') + 1 / s * nuc (K - K')) / 2 := by ring
  rw [e, le_div_iff₀ two_pos]
  linarith

end FilterAux

/-- `lem:app-dyn-schatten`, part (i). Snapshot `cr-2026-10-23`. Statement, verbatim from
`section.tex` (full environment shown; this declaration is part (i)):

    \begin{lemma}[Schatten sensitivity of the filter]\label{lem:app-dyn-schatten}
    Let $K,K'\in\R^{\Nout\times\Nin}$, $s>0$, $\ridge'>0$ and $p\in\{1,\infty\}$. Then
    \begin{enumerate}[label=(\roman*)]
    \item $\norm{\mathsf X_s(K)-\mathsf X_s(K')}_{S_p}\le s^{-1}\norm{K-K'}_{S_p}$;
    \item $\norm{\Qridge{\ridge'}(K)-\Qridge{\ridge'}(K')}_{S_p}\le\ridge'^{-1/2}\norm{K-K'}_{S_p}$;
    \item $\norm{\partial_{\ridge'}\Qridge{\ridge'}(K)-\partial_{\ridge'}\Qridge{\ridge'}(K')}_*\le\frac12\ridge'^{-3/2}\norm{K-K'}_*$;
    \item if $\ridge_1,\ridge_2\ge\ridge_\circ>0$, then
    $\norm{\Qridge{\ridge_1}(K)-\Qridge{\ridge_2}(K)}\le\abs{\ridge_1-\ridge_2}/(2\ridge_\circ)$
    and the same bound multiplied by $\sqrt{\min(\Nout,\Nin)}$ holds in Frobenius norm.
    \end{enumerate}
    \end{lemma}
-/
theorem lem_app_dyn_schatten_i {m n : ℕ} {p : ENNReal} (hp : p = 1 ∨ p = ⊤)
    {s : ℝ} (hs : 0 < s) (K K' : Mat m n) :
    schatNorm p (Muon.DetEquiv.Xs K s - Muon.DetEquiv.Xs K' s) ≤ s⁻¹ * schatNorm p (K - K') := by
  rcases hp with rfl | rfl
  · simp only [schatNorm, ite_true]
    exact fl_nuc_bound K K' hs
  · simp only [schatNorm, ENNReal.top_ne_one, ite_false]
    exact fl_op_bound K K' hs

section FilterAuxII

open Muon.DetEquiv MeasureTheory

private lemma fl_ioi_integral {ϱ : ℝ} (hϱ : 0 < ϱ) :
    IntegrableOn (fun u : ℝ => (ϱ + u ^ 2)⁻¹) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), (ϱ + u ^ 2)⁻¹ = Real.pi / 2 * ϱ ^ (-(1 / 2 : ℝ)) := by
  have hr : 0 < Real.sqrt ϱ := Real.sqrt_pos.mpr hϱ
  have hb : 0 < (Real.sqrt ϱ)⁻¹ := inv_pos.mpr hr
  have hfun : (fun u : ℝ => (ϱ + u ^ 2)⁻¹) =
      fun u => ϱ⁻¹ * (fun x : ℝ => (1 + x ^ 2)⁻¹) ((Real.sqrt ϱ)⁻¹ * u) := by
    funext u
    have : ϱ + u ^ 2 = ϱ * (1 + ((Real.sqrt ϱ)⁻¹ * u) ^ 2) := by
      rw [mul_pow, inv_pow, Real.sq_sqrt hϱ.le]; field_simp
    rw [this, mul_inv]
  have hint : IntegrableOn (fun x : ℝ => (1 + x ^ 2)⁻¹) (Ioi 0) :=
    integrable_inv_one_add_sq.integrableOn
  refine ⟨?_, ?_⟩
  · rw [hfun]
    refine Integrable.const_mul ?_ _
    exact (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 hb).mpr
      (by simpa using hint)
  · rw [hfun, integral_const_mul, integral_comp_mul_left_Ioi (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 hb]
    simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero, smul_eq_mul,
      inv_inv]
    have h1 : ϱ ^ (-(1 / 2 : ℝ)) = (Real.sqrt ϱ)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hϱ.le]; norm_num
    rw [h1]
    have : ϱ⁻¹ = (Real.sqrt ϱ)⁻¹ * (Real.sqrt ϱ)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hϱ.le]
    rw [this]
    field_simp

private lemma fl_trace_eq_sum {m n : ℕ} (A B : Mat m n) :
    Matrix.trace (Aᵀ * B) = ∑ i, ∑ j, A i j * B i j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

private lemma fl_sum_dot {m n : ℕ} (w : Vec m) (x : Vec n) (M : Mat m n) :
    ∑ i, ∑ j, (Matrix.of fun i j => w i * x j) i j * M i j = w ⬝ᵥ (M *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma fl_Q_diff_entry {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K K' : Mat m n) (i : Fin m)
    (j : Fin n) :
    (Q ϱ K - Q ϱ K') i j =
      (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), (Xs K (ϱ + u ^ 2) - Xs K' (ϱ + u ^ 2)) i j := by
  obtain ⟨h1, h2, -⟩ := Muon.Setup.lem_app_setup_contour ϱ hϱ K
  obtain ⟨h1', h2', -⟩ := Muon.Setup.lem_app_setup_contour ϱ hϱ K'
  rw [Matrix.sub_apply, h1 i j, h1' i j, ← mul_sub, ← integral_sub (h2 i j) (h2' i j)]
  rfl

private lemma fl_entry_int {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K K' : Mat m n) (i : Fin m)
    (j : Fin n) :
    IntegrableOn (fun u : ℝ => (Xs K (ϱ + u ^ 2) - Xs K' (ϱ + u ^ 2)) i j) (Ioi 0) := by
  obtain ⟨-, h2, -⟩ := Muon.Setup.lem_app_setup_contour ϱ hϱ K
  obtain ⟨-, h2', -⟩ := Muon.Setup.lem_app_setup_contour ϱ hϱ K'
  exact (h2 i j).sub (h2' i j)

private lemma fl_lin_int {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K K' : Mat m n) (C : Mat m n) :
    IntegrableOn (fun u : ℝ => ∑ i, ∑ j, C i j * (Xs K (ϱ + u ^ 2) - Xs K' (ϱ + u ^ 2)) i j)
      (Ioi 0) := by
  refine integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => ?_
  exact (fl_entry_int hϱ K K' i j).const_mul _

private lemma fl_lin_eq {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K K' : Mat m n) (C : Mat m n) :
    ∑ i, ∑ j, C i j * (Q ϱ K - Q ϱ K') i j =
      (2 / Real.pi) * ∫ u in Ioi (0 : ℝ),
        ∑ i, ∑ j, C i j * (Xs K (ϱ + u ^ 2) - Xs K' (ϱ + u ^ 2)) i j := by
  have hi : ∀ i, Integrable (fun u : ℝ => ∑ j, C i j * (Xs K (ϱ + u ^ 2) - Xs K' (ϱ + u ^ 2)) i j)
      (volume.restrict (Ioi (0 : ℝ))) := fun i =>
    integrable_finset_sum _ fun j _ => (fl_entry_int hϱ K K' i j).const_mul _
  rw [integral_finset_sum Finset.univ (fun i _ => hi i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum Finset.univ
    (fun j _ => (fl_entry_int hϱ K K' i j).const_mul _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, fl_Q_diff_entry hϱ K K' i j]
  ring

private lemma fl_lin_le {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K K' : Mat m n) (C : Mat m n) {c : ℝ}
    (h : ∀ u : ℝ, 0 < u →
      ∑ i, ∑ j, C i j * (Xs K (ϱ + u ^ 2) - Xs K' (ϱ + u ^ 2)) i j ≤ c * (ϱ + u ^ 2)⁻¹) :
    ∑ i, ∑ j, C i j * (Q ϱ K - Q ϱ K') i j ≤ c * ϱ ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨hint, hval⟩ := fl_ioi_integral hϱ
  rw [fl_lin_eq hϱ K K' C]
  have hle : ∫ u in Ioi (0 : ℝ),
        ∑ i, ∑ j, C i j * (Xs K (ϱ + u ^ 2) - Xs K' (ϱ + u ^ 2)) i j ≤
      ∫ u in Ioi (0 : ℝ), c * (ϱ + u ^ 2)⁻¹ :=
    setIntegral_mono_on (fl_lin_int hϱ K K' C) (hint.const_mul c) measurableSet_Ioi
      fun u hu => h u hu
  rw [integral_const_mul, hval] at hle
  have hpi : 0 < 2 / Real.pi := by positivity
  calc _ ≤ (2 / Real.pi) * (c * (Real.pi / 2 * ϱ ^ (-(1 / 2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hle hpi.le
    _ = c * ϱ ^ (-(1 / 2 : ℝ)) := by field_simp

private lemma fl_nuc_Q {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K K' : Mat m n) :
    nuc (Q ϱ K - Q ϱ K') ≤ ϱ ^ (-(1 / 2 : ℝ)) * nuc (K - K') := by
  obtain ⟨U, hU, htr⟩ := (nuc_isGreatest_dual (Q ϱ K - Q ϱ K')).1
  rw [htr, fl_trace_eq_sum, mul_comm]
  refine fl_lin_le hϱ K K' U fun u hu => ?_
  have hs : 0 < ϱ + u ^ 2 := by positivity
  rw [← fl_trace_eq_sum]
  have h1 := (nuc_isGreatest_dual (Xs K (ϱ + u ^ 2) - Xs K' (ϱ + u ^ 2))).2 ⟨U, hU, rfl⟩
  have h2 := fl_nuc_bound K K' hs
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := by ring

private lemma fl_op_Q {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K K' : Mat m n) :
    opNorm (Q ϱ K - Q ϱ K') ≤ ϱ ^ (-(1 / 2 : ℝ)) * opNorm (K - K') := by
  have hL : 0 ≤ ϱ ^ (-(1 / 2 : ℝ)) * opNorm (K - K') :=
    mul_nonneg (Real.rpow_nonneg hϱ.le _) (fl_opNorm_nonneg _)
  refine fl_opNorm_le _ hL fun x => ?_
  set Z := Q ϱ K - Q ϱ K' with hZ
  set w := Z *ᵥ x with hw
  set Y := sqNorm w with hY
  set Xn := sqNorm x with hXn
  set L := ϱ ^ (-(1 / 2 : ℝ)) * opNorm (K - K') with hLdef
  have hYnn : 0 ≤ Y := fl_sqNorm_nonneg _
  have hXnn : 0 ≤ Xn := fl_sqNorm_nonneg _
  set r := Real.sqrt (Y * Xn) with hr
  have hrnn : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = sqNorm w * sqNorm x := Real.sq_sqrt (by positivity)
  have hYsum : Y = ∑ i, ∑ j, (Matrix.of fun i j => w i * x j) i j * Z i j := by
    rw [fl_sum_dot, hY, fl_sqNorm_eq_dot, ← hw]
  have hbound : ∑ i, ∑ j, (Matrix.of fun i j => w i * x j) i j * Z i j ≤ (opNorm (K - K') * r) * ϱ ^ (-(1 / 2 : ℝ)) := by
    refine fl_lin_le hϱ K K' (Matrix.of fun i j => w i * x j) fun u hu => ?_
    have hs : 0 < ϱ + u ^ 2 := by positivity
    have hsum : ∑ i, ∑ j, (Matrix.of fun i j => w i * x j) i j *
        (Xs K (ϱ + u ^ 2) - Xs K' (ϱ + u ^ 2)) i j =
        w ⬝ᵥ ((Xs K (ϱ + u ^ 2) - Xs K' (ϱ + u ^ 2)) *ᵥ x) := by
      exact fl_sum_dot _ _ _
    rw [hsum]
    have hop := fl_op_bound K K' hs
    have hsq := fl_term_sq (Xs K (ϱ + u ^ 2) - Xs K' (ϱ + u ^ 2)) _ hop w x
    have hμ : 0 ≤ (ϱ + u ^ 2)⁻¹ * opNorm (K - K') := by
      have := fl_opNorm_nonneg (K - K'); positivity
    have habs : |w ⬝ᵥ ((Xs K (ϱ + u ^ 2) - Xs K' (ϱ + u ^ 2)) *ᵥ x)| ≤
        ((ϱ + u ^ 2)⁻¹ * opNorm (K - K')) * r := by
      apply abs_le_of_sq_le_sq _ (by positivity)
      calc _ ≤ _ := hsq
        _ = _ := by
          rw [show ((ϱ + u ^ 2)⁻¹ * opNorm (K - K') * r) ^ 2 =
            ((ϱ + u ^ 2)⁻¹ * opNorm (K - K')) ^ 2 * r ^ 2 by ring, hr2]
    calc _ ≤ _ := le_abs_self _
      _ ≤ _ := habs
      _ = _ := by ring
  have hYle : Y ≤ L * r := by
    rw [hYsum]; calc _ ≤ _ := hbound
      _ = L * r := by rw [hLdef]; ring
  rcases eq_or_lt_of_le hYnn with h0 | hpos
  · rw [← h0]; positivity
  · have : Y * Y ≤ Y * (L ^ 2 * Xn) := by
      calc Y * Y ≤ (L * r) * (L * r) := mul_self_le_mul_self hYnn hYle
        _ = L ^ 2 * r ^ 2 := by ring
        _ = Y * (L ^ 2 * Xn) := by rw [hr2, hY, hXn]; ring
    exact le_of_mul_le_mul_left this hpos

end FilterAuxII


/-- `lem:app-dyn-schatten`, part (ii). Snapshot `cr-2026-10-23`. Statement, verbatim from
`section.tex` (full environment shown; this declaration is part (ii)):

    \begin{lemma}[Schatten sensitivity of the filter]\label{lem:app-dyn-schatten}
    Let $K,K'\in\R^{\Nout\times\Nin}$, $s>0$, $\ridge'>0$ and $p\in\{1,\infty\}$. Then
    \begin{enumerate}[label=(\roman*)]
    \item $\norm{\mathsf X_s(K)-\mathsf X_s(K')}_{S_p}\le s^{-1}\norm{K-K'}_{S_p}$;
    \item $\norm{\Qridge{\ridge'}(K)-\Qridge{\ridge'}(K')}_{S_p}\le\ridge'^{-1/2}\norm{K-K'}_{S_p}$;
    \item $\norm{\partial_{\ridge'}\Qridge{\ridge'}(K)-\partial_{\ridge'}\Qridge{\ridge'}(K')}_*\le\frac12\ridge'^{-3/2}\norm{K-K'}_*$;
    \item if $\ridge_1,\ridge_2\ge\ridge_\circ>0$, then
    $\norm{\Qridge{\ridge_1}(K)-\Qridge{\ridge_2}(K)}\le\abs{\ridge_1-\ridge_2}/(2\ridge_\circ)$
    and the same bound multiplied by $\sqrt{\min(\Nout,\Nin)}$ holds in Frobenius norm.
    \end{enumerate}
    \end{lemma}
-/
theorem lem_app_dyn_schatten_ii {m n : ℕ} {p : ENNReal} (hp : p = 1 ∨ p = ⊤)
    {ϱ' : ℝ} (hϱ : 0 < ϱ') (K K' : Mat m n) :
    schatNorm p (Q ϱ' K - Q ϱ' K') ≤ ϱ' ^ (-(1 / 2 : ℝ)) * schatNorm p (K - K') := by
  rcases hp with rfl | rfl
  · simp only [schatNorm, ite_true]
    exact fl_nuc_Q hϱ K K'
  · simp only [schatNorm, ENNReal.top_ne_one, ite_false]
    exact fl_op_Q hϱ K K'

/-! ### Private helpers for `lem_app_dyn_schatten_iv` (task P-E.5.P2) -/

section FilterAuxIV

open Muon.DetEquiv

/-- Gram identity for an orthonormal family (private helper). -/
private lemma fl_gram {m r : ℕ} (p : Fin r → Vec m)
    (hp : ∀ k l, p k ⬝ᵥ p l = if k = l then 1 else 0) (w : Fin r → ℝ) :
    ∑ i, (∑ k, w k * p k i) ^ 2 = ∑ k, w k ^ 2 := by
  have h1 : ∀ i, (∑ k, w k * p k i) ^ 2 = ∑ k, ∑ l, (w k * w l) * (p k i * p l i) := by
    intro i
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  have h2 : ∀ l, ∑ i, (w k * w l) * (p k i * p l i) = (w k * w l) * (p k ⬝ᵥ p l) := by
    intro l
    rw [dotProduct, Finset.mul_sum]
  simp [h2, hp, sq]

/-- Bessel inequality for an orthonormal family (private helper). -/
private lemma fl_bessel {n r : ℕ} (q : Fin r → Vec n)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0) (x : Vec n) :
    ∑ k, (q k ⬝ᵥ x) ^ 2 ≤ sqNorm x := by
  have hg : ∑ i, (∑ k, (q k ⬝ᵥ x) * q k i) ^ 2 = ∑ k, (q k ⬝ᵥ x) ^ 2 :=
    fl_gram q hq (fun k => q k ⬝ᵥ x)
  have hcross : ∑ i, x i * (∑ k, (q k ⬝ᵥ x) * q k i) = ∑ k, (q k ⬝ᵥ x) ^ 2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    calc ∑ i, x i * ((q k ⬝ᵥ x) * q k i) = (q k ⬝ᵥ x) * ∑ i, q k i * x i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = (q k ⬝ᵥ x) ^ 2 := by
          simp only [dotProduct]
          ring
  have hnn : 0 ≤ ∑ i, (x i - ∑ k, (q k ⬝ᵥ x) * q k i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexp : ∑ i, (x i - ∑ k, (q k ⬝ᵥ x) * q k i) ^ 2 =
      sqNorm x - 2 * ∑ k, (q k ⬝ᵥ x) ^ 2 + ∑ k, (q k ⬝ᵥ x) ^ 2 := by
    have e1 : ∀ i, (x i - ∑ k, (q k ⬝ᵥ x) * q k i) ^ 2 =
        x i ^ 2 - 2 * (x i * ∑ k, (q k ⬝ᵥ x) * q k i) + (∑ k, (q k ⬝ᵥ x) * q k i) ^ 2 :=
      fun i => by ring
    simp only [e1]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hcross, hg]
    simp only [sqNorm, sq]
  linarith

/-- Scalar core of `lem_app_dyn_schatten_iv`: with `X² = s² + a`, `Y² = s² + b`, `a, b ≥ ϱo > 0`,
`|s/X - s/Y| ≤ |a - b|/(2ϱo)` (private helper). -/
private lemma fl_scalar_core {s ϱo a b X Y : ℝ} (hs : 0 ≤ s) (hϱo : 0 < ϱo)
    (hX : 0 < X) (hY : 0 < Y) (hX2 : X ^ 2 = s ^ 2 + a) (hY2 : Y ^ 2 = s ^ 2 + b)
    (ha : ϱo ≤ a) (hb : ϱo ≤ b) :
    |s / X - s / Y| ≤ |a - b| / (2 * ϱo) := by
  have hXs : s ≤ X := by nlinarith [sq_nonneg s]
  have hYs : s ≤ Y := by nlinarith [sq_nonneg s]
  have hX2' : ϱo ≤ X ^ 2 := by rw [hX2]; nlinarith [sq_nonneg s]
  have hY2' : ϱo ≤ Y ^ 2 := by rw [hY2]; nlinarith [sq_nonneg s]
  have key : s / X - s / Y = s * (b - a) / (X * Y * (X + Y)) := by
    rw [div_sub_div _ _ hX.ne' hY.ne',
      div_eq_div_iff (mul_pos hX hY).ne' (mul_pos (mul_pos hX hY) (by linarith)).ne']
    linear_combination (X * Y * s) * (hY2 - hX2)
  have hprod : 2 * ϱo * s ≤ X * Y * (X + Y) := by
    have h1 : ϱo * s ≤ X ^ 2 * Y := mul_le_mul hX2' hYs hs (sq_nonneg X)
    have h2 : ϱo * s ≤ Y ^ 2 * X := mul_le_mul hY2' hXs hs (sq_nonneg Y)
    have e : X * Y * (X + Y) = X ^ 2 * Y + Y ^ 2 * X := by ring
    rw [e]
    linarith
  rw [key, abs_div, abs_mul, abs_of_nonneg hs,
    abs_of_pos (mul_pos (mul_pos hX hY) (by linarith : (0 : ℝ) < X + Y)), abs_sub_comm b a,
    div_le_div_iff₀ (mul_pos (mul_pos hX hY) (by linarith)) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hprod (abs_nonneg (a - b))]

/-- Scalar bound for `s/√(s²+a) - s/√(s²+b)` (private helper). -/
private lemma fl_scalar_bound {s ϱo a b : ℝ} (hs : 0 ≤ s) (hϱo : 0 < ϱo) (ha : ϱo ≤ a)
    (hb : ϱo ≤ b) :
    |s / Real.sqrt (s ^ 2 + a) - s / Real.sqrt (s ^ 2 + b)| ≤ |a - b| / (2 * ϱo) :=
  fl_scalar_core hs hϱo (Real.sqrt_pos.mpr (by linarith [sq_nonneg s]))
    (Real.sqrt_pos.mpr (by linarith [sq_nonneg s])) (Real.sq_sqrt (by linarith [sq_nonneg s]))
    (Real.sq_sqrt (by linarith [sq_nonneg s])) ha hb

/-- Entries of a sum of rank-one terms (private helper). -/
private lemma fl_outer_sum_apply {m n r : ℕ} (c : Fin r → ℝ) (p : Fin r → Vec m)
    (q : Fin r → Vec n) (i : Fin m) (j : Fin n) :
    (∑ k, c k • outer (p k) (q k)) i j = ∑ k, c k * (p k i * q k j) := by
  simp [Matrix.sum_apply, Matrix.smul_apply, outer, Matrix.vecMulVec_apply]

/-- Matrix-vector product of a sum of rank-one terms (private helper). -/
private lemma fl_outer_sum_mulVec {m n r : ℕ} (c : Fin r → ℝ) (p : Fin r → Vec m)
    (q : Fin r → Vec n) (x : Vec n) (i : Fin m) :
    ((∑ k, c k • outer (p k) (q k)) *ᵥ x) i = ∑ k, (c k * (q k ⬝ᵥ x)) * p k i := by
  simp only [Matrix.mulVec, dotProduct, fl_outer_sum_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Sum of squared entries of a sum of rank-one terms (private helper). -/
private lemma fl_sum_norm_outer {m n r : ℕ} (c : Fin r → ℝ) (p : Fin r → Vec m)
    (q : Fin r → Vec n) (hp : ∀ k l, p k ⬝ᵥ p l = if k = l then 1 else 0)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0) :
    ∑ i, ∑ j, ‖(∑ k, c k • outer (p k) (q k)) i j‖ ^ 2 = ∑ k, c k ^ 2 := by
  have e : ∀ i, ∑ j, ‖(∑ k, c k • outer (p k) (q k)) i j‖ ^ 2 = ∑ k, (c k * p k i) ^ 2 := by
    intro i
    have h2 : ∀ j, (∑ k, c k * (p k i * q k j)) = ∑ k, (c k * p k i) * q k j :=
      fun j => Finset.sum_congr rfl fun k _ => by ring
    have hg := fl_gram q hq (fun k => c k * p k i)
    simp only [fl_outer_sum_apply, Real.norm_eq_abs, sq_abs, h2]
    exact hg
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hpk := hp k k
  rw [if_pos rfl] at hpk
  calc ∑ i, (c k * p k i) ^ 2 = c k ^ 2 * (p k ⬝ᵥ p k) := by
        simp only [dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = c k ^ 2 := by rw [hpk, mul_one]

/-- Core of `lem_app_dyn_schatten_iv` for any orthonormal SVD-type decomposition (private). -/
private lemma fl_iv_core {m n r : ℕ} {ϱo ϱ1 ϱ2 : ℝ} (hϱo : 0 < ϱo) (h1 : ϱo ≤ ϱ1)
    (h2 : ϱo ≤ ϱ2) (K : Mat m n) (s : Fin r → ℝ) (p : Fin r → Vec m) (q : Fin r → Vec n)
    (hs : ∀ k, 0 < s k) (hp : ∀ k l, p k ⬝ᵥ p l = if k = l then 1 else 0)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0)
    (hK : K = ∑ k, s k • outer (p k) (q k)) :
    opNorm (Q ϱ1 K - Q ϱ2 K) ≤ |ϱ1 - ϱ2| / (2 * ϱo) ∧
      fro (Q ϱ1 K - Q ϱ2 K) ≤ Real.sqrt (r : ℝ) * (|ϱ1 - ϱ2| / (2 * ϱo)) := by
  have hϱ1 : 0 < ϱ1 := lt_of_lt_of_le hϱo h1
  have hϱ2 : 0 < ϱ2 := lt_of_lt_of_le hϱo h2
  have hQ1 := Muon.Setup.Q_eq_svd ϱ1 hϱ1.le K s p q hs hp hq hK
  have hQ2 := Muon.Setup.Q_eq_svd ϱ2 hϱ2.le K s p q hs hp hq hK
  have hD : Q ϱ1 K - Q ϱ2 K = ∑ k, (s k / Real.sqrt (s k ^ 2 + ϱ1)
      - s k / Real.sqrt (s k ^ 2 + ϱ2)) • outer (p k) (q k) := by
    rw [hQ1, hQ2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => (sub_smul _ _ _).symm
  have hcb : ∀ k, |s k / Real.sqrt (s k ^ 2 + ϱ1) - s k / Real.sqrt (s k ^ 2 + ϱ2)|
      ≤ |ϱ1 - ϱ2| / (2 * ϱo) := fun k => fl_scalar_bound (hs k).le hϱo h1 h2
  have hδnn : 0 ≤ |ϱ1 - ϱ2| / (2 * ϱo) := by positivity
  rw [hD]
  constructor
  · refine fl_opNorm_le _ hδnn fun x => ?_
    have hsq : sqNorm ((∑ k, (s k / Real.sqrt (s k ^ 2 + ϱ1)
        - s k / Real.sqrt (s k ^ 2 + ϱ2)) • outer (p k) (q k)) *ᵥ x)
        = ∑ k, ((s k / Real.sqrt (s k ^ 2 + ϱ1) - s k / Real.sqrt (s k ^ 2 + ϱ2))
            * (q k ⬝ᵥ x)) ^ 2 := by
      unfold sqNorm
      simp only [fl_outer_sum_mulVec]
      exact fl_gram p hp (fun k => (s k / Real.sqrt (s k ^ 2 + ϱ1)
        - s k / Real.sqrt (s k ^ 2 + ϱ2)) * (q k ⬝ᵥ x))
    rw [hsq]
    calc ∑ k, ((s k / Real.sqrt (s k ^ 2 + ϱ1) - s k / Real.sqrt (s k ^ 2 + ϱ2))
            * (q k ⬝ᵥ x)) ^ 2
        ≤ ∑ k, (|ϱ1 - ϱ2| / (2 * ϱo)) ^ 2 * (q k ⬝ᵥ x) ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [mul_pow]
          have h := pow_le_pow_left₀ (abs_nonneg _) (hcb k) 2
          rw [sq_abs] at h
          exact mul_le_mul_of_nonneg_right h (sq_nonneg _)
      _ = (|ϱ1 - ϱ2| / (2 * ϱo)) ^ 2 * ∑ k, (q k ⬝ᵥ x) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (|ϱ1 - ϱ2| / (2 * ϱo)) ^ 2 * sqNorm x :=
          mul_le_mul_of_nonneg_left (fl_bessel q hq x) (sq_nonneg _)
  · have hfro := fl_sum_norm_outer (fun k => s k / Real.sqrt (s k ^ 2 + ϱ1)
        - s k / Real.sqrt (s k ^ 2 + ϱ2)) p q hp hq
    beta_reduce at hfro
    unfold fro
    rw [hfro]
    have hle : ∑ k, (s k / Real.sqrt (s k ^ 2 + ϱ1) - s k / Real.sqrt (s k ^ 2 + ϱ2)) ^ 2
        ≤ (r : ℝ) * (|ϱ1 - ϱ2| / (2 * ϱo)) ^ 2 := by
      calc ∑ k, (s k / Real.sqrt (s k ^ 2 + ϱ1) - s k / Real.sqrt (s k ^ 2 + ϱ2)) ^ 2
          ≤ ∑ _k : Fin r, (|ϱ1 - ϱ2| / (2 * ϱo)) ^ 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            have h := pow_le_pow_left₀ (abs_nonneg _) (hcb k) 2
            rwa [sq_abs] at h
        _ = (r : ℝ) * (|ϱ1 - ϱ2| / (2 * ϱo)) ^ 2 := by simp
    calc Real.sqrt _ ≤ Real.sqrt ((r : ℝ) * (|ϱ1 - ϱ2| / (2 * ϱo)) ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = Real.sqrt (r : ℝ) * (|ϱ1 - ϱ2| / (2 * ϱo)) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg r), Real.sqrt_sq hδnn]

end FilterAuxIV


/-! ### Private helpers for `lem_app_dyn_schatten_iii` (task P-E.5.P2) -/

section Gen
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma gen_D {T S P Q P' Q' : Matrix ι ι ℝ} {c : ℝ}
    (hPT : P * T = 1 - c • Q) (hQT : Q * T = c • P) (hSP : S * P' = 1 - c • Q')
    (hSQ : S * Q' = c • P') :
    P - P' = P * (S - T) * P' - Q * (S - T) * Q' ∧
    Q - Q' = P * (S - T) * Q' + Q * (S - T) * P' := by
  have a1 : P * S * P' = P - c • (P * Q') := by
    rw [Matrix.mul_assoc, hSP, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  have a2 : P * T * P' = P' - c • (Q * P') := by
    rw [hPT, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  have a3 : Q * S * Q' = c • (Q * P') := by
    rw [Matrix.mul_assoc, hSQ, Matrix.mul_smul]
  have a4 : Q * T * Q' = c • (P * Q') := by
    rw [hQT, Matrix.smul_mul]
  have b1 : P * S * Q' = c • (P * P') := by
    rw [Matrix.mul_assoc, hSQ, Matrix.mul_smul]
  have b2 : P * T * Q' = Q' - c • (Q * Q') := by
    rw [hPT, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  have b3 : Q * S * P' = Q - c • (Q * Q') := by
    rw [Matrix.mul_assoc, hSP, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  have b4 : Q * T * P' = c • (P * P') := by
    rw [hQT, Matrix.smul_mul]
  constructor
  · rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul, a1, a2, a3, a4]; abel
  · rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul, b1, b2, b3, b4]; abel

private lemma gen_main {T S P Q P' Q' : Matrix ι ι ℝ} {c : ℝ}
    (hPT : P * T = 1 - c • Q) (hQT : Q * T = c • P) (hSP : S * P' = 1 - c • Q')
    (hSQ : S * Q' = c • P') (hPQ : P * Q = Q * P) (hPQ' : P' * Q' = Q' * P') :
    (2 : ℝ) • (P * Q) - (2 : ℝ) • (P' * Q') =
      (P * P - Q * Q) * (S - T) * Q' + ((2 : ℝ) • (P * Q)) * (S - T) * P'
      + P * (S - T) * ((2 : ℝ) • (P' * Q')) + Q * (S - T) * (P' * P' - Q' * Q') := by
  obtain ⟨d1, d2⟩ := gen_D hPT hQT hSP hSQ
  have h : (2 : ℝ) • (P * Q) - (2 : ℝ) • (P' * Q') =
      P * (Q - Q') + Q * (P - P') + (P - P') * Q' + (Q - Q') * P' := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, two_smul]
    rw [← hPQ, ← hPQ']
    abel
  rw [h, d1, d2]
  have e1 : ∀ Y : Matrix ι ι ℝ, Q * (P * Y) = P * (Q * Y) := fun Y => by
    rw [← Matrix.mul_assoc, ← hPQ, Matrix.mul_assoc]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.mul_assoc, two_smul]
  simp only [e1, ← hPQ']
  abel

private lemma gen_tr_cyc (A D B : Matrix ι ι ℝ) :
    Matrix.trace (A * D * B) = Matrix.trace (D * (B * A)) := by
  rw [Matrix.trace_mul_comm (A * D) B, ← Matrix.mul_assoc, Matrix.trace_mul_comm]

private lemma gen_trace {T S P Q P' Q' V : Matrix ι ι ℝ} {c : ℝ}
    (hPT : P * T = 1 - c • Q) (hQT : Q * T = c • P) (hSP : S * P' = 1 - c • Q')
    (hSQ : S * Q' = c • P') (hPQ : P * Q = Q * P) (hPQ' : P' * Q' = Q' * P') :
    Matrix.trace (V * ((2 : ℝ) • (P * Q) - (2 : ℝ) • (P' * Q'))) =
      Matrix.trace ((S - T) * (Q' * (V * (P * P - Q * Q)) + P' * (V * ((2 : ℝ) • (P * Q))))) +
      Matrix.trace ((S - T) * (((2 : ℝ) • (P' * Q')) * (V * P) + (P' * P' - Q' * Q') * (V * Q))) := by
  rw [gen_main hPT hQT hSP hSQ hPQ hPQ']
  simp only [Matrix.mul_add, Matrix.trace_add]
  have k : ∀ X Y : Matrix ι ι ℝ, Matrix.trace (V * (X * (S - T) * Y)) =
      Matrix.trace ((S - T) * (Y * (V * X))) := fun X Y => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← gen_tr_cyc (V * X) (S - T) Y]
  rw [k, k, k, k]
  ring

private lemma gen_dot_mulVec (M : Matrix ι ι ℝ) (hM : Mᵀ = M) (y v : ι → ℝ) :
    y ⬝ᵥ (M *ᵥ v) = (M *ᵥ y) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec]
  have h : y ᵥ* M = M *ᵥ y := by
    conv_lhs => rw [← hM]
    exact Matrix.vecMul_transpose M y
  rw [h]

private lemma gen_cs (a b : ι → ℝ) : (a ⬝ᵥ b) ^ 2 ≤ (a ⬝ᵥ a) * (b ⬝ᵥ b) := by
  simpa [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b

private lemma gen_dot_nonneg (a : ι → ℝ) : 0 ≤ a ⬝ᵥ a :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

private lemma gen_cs2 {V : Matrix ι ι ℝ} (hV : ∀ w : ι → ℝ, (V *ᵥ w) ⬝ᵥ (V *ᵥ w) ≤ w ⬝ᵥ w)
    (e1 e2 f1 f2 : ι → ℝ) :
    (e1 ⬝ᵥ (V *ᵥ f1) + e2 ⬝ᵥ (V *ᵥ f2)) ^ 2 ≤
      (e1 ⬝ᵥ e1 + e2 ⬝ᵥ e2) * (f1 ⬝ᵥ f1 + f2 ⬝ᵥ f2) := by
  have h1 : (e1 ⬝ᵥ (V *ᵥ f1)) ^ 2 ≤ (e1 ⬝ᵥ e1) * (f1 ⬝ᵥ f1) :=
    (gen_cs _ _).trans (mul_le_mul_of_nonneg_left (hV f1) (gen_dot_nonneg _))
  have h2 : (e2 ⬝ᵥ (V *ᵥ f2)) ^ 2 ≤ (e2 ⬝ᵥ e2) * (f2 ⬝ᵥ f2) :=
    (gen_cs _ _).trans (mul_le_mul_of_nonneg_left (hV f2) (gen_dot_nonneg _))
  set t1 := e1 ⬝ᵥ (V *ᵥ f1)
  set t2 := e2 ⬝ᵥ (V *ᵥ f2)
  have a1 := gen_dot_nonneg e1
  have a2 := gen_dot_nonneg e2
  have b1 := gen_dot_nonneg f1
  have b2 := gen_dot_nonneg f2
  set A1 := e1 ⬝ᵥ e1
  set A2 := e2 ⬝ᵥ e2
  set B1 := f1 ⬝ᵥ f1
  set B2 := f2 ⬝ᵥ f2
  have hc : 2 * t1 * t2 ≤ A1 * B2 + A2 * B1 := by
    refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ (by positivity))
    have : (2 * t1 * t2) ^ 2 = 4 * (t1 ^ 2 * t2 ^ 2) := by ring
    rw [this]
    have h3 : t1 ^ 2 * t2 ^ 2 ≤ (A1 * B1) * (A2 * B2) :=
      mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    nlinarith [sq_nonneg (A1 * B2 - A2 * B1)]
  nlinarith

private lemma gen_quad {P Q : Matrix ι ι ℝ} (hP : Pᵀ = P) (hQ : Qᵀ = Q) (hPQ : P * Q = Q * P)
    {ν : ℝ}
    (hn : ∀ z : ι → ℝ, (P *ᵥ z) ⬝ᵥ (P *ᵥ z) + (Q *ᵥ z) ⬝ᵥ (Q *ᵥ z) ≤ ν * (z ⬝ᵥ z))
    (hν : 0 ≤ ν) (z : ι → ℝ) :
    (((P * P - Q * Q) *ᵥ z) ⬝ᵥ ((P * P - Q * Q) *ᵥ z) +
      (((2 : ℝ) • (P * Q)) *ᵥ z) ⬝ᵥ (((2 : ℝ) • (P * Q)) *ᵥ z)) ≤ ν ^ 2 * (z ⬝ᵥ z) := by
  set a := P *ᵥ z with ha
  set b := Q *ᵥ z with hb
  have e1 : (P * P - Q * Q) *ᵥ z = P *ᵥ a - Q *ᵥ b := by
    rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have e2 : ((2 : ℝ) • (P * Q)) *ᵥ z = P *ᵥ b + Q *ᵥ a := by
    have h1 : (P * Q) *ᵥ z = P *ᵥ b := by rw [hb, Matrix.mulVec_mulVec]
    have h2 : (P * Q) *ᵥ z = Q *ᵥ a := by rw [hPQ, ha, Matrix.mulVec_mulVec]
    rw [Matrix.smul_mulVec, two_smul]
    nth_rewrite 1 [h1]; rw [h2]
  have comm : ∀ v : ι → ℝ, Q *ᵥ (P *ᵥ v) = P *ᵥ (Q *ᵥ v) := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hPQ]
  have c1 : (P *ᵥ a) ⬝ᵥ (Q *ᵥ b) = (P *ᵥ b) ⬝ᵥ (Q *ᵥ a) := by
    rw [← gen_dot_mulVec P hP a, dotProduct_comm (P *ᵥ b), ← gen_dot_mulVec Q hQ a, comm]
  have ha' := hn z
  rw [e1, e2]
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_add, add_dotProduct]
  rw [dotProduct_comm (Q *ᵥ b) (P *ᵥ a), dotProduct_comm (Q *ᵥ a) (P *ᵥ b)]
  have h3 := hn a
  have h4 := hn b
  have h5 : a ⬝ᵥ a + b ⬝ᵥ b ≤ ν * (z ⬝ᵥ z) := ha'
  nlinarith

private lemma gen_bilA {P Q P' Q' V : Matrix ι ι ℝ} (hP : Pᵀ = P) (hQ : Qᵀ = Q) (hP' : P'ᵀ = P')
    (hQ' : Q'ᵀ = Q') (hPQ : P * Q = Q * P) {ν : ℝ} (hν : 0 ≤ ν)
    (hn : ∀ z : ι → ℝ, (P *ᵥ z) ⬝ᵥ (P *ᵥ z) + (Q *ᵥ z) ⬝ᵥ (Q *ᵥ z) ≤ ν * (z ⬝ᵥ z))
    (hn' : ∀ z : ι → ℝ, (P' *ᵥ z) ⬝ᵥ (P' *ᵥ z) + (Q' *ᵥ z) ⬝ᵥ (Q' *ᵥ z) ≤ ν * (z ⬝ᵥ z))
    (hV : ∀ w : ι → ℝ, (V *ᵥ w) ⬝ᵥ (V *ᵥ w) ≤ w ⬝ᵥ w) (x y : ι → ℝ) :
    (y ⬝ᵥ ((Q' * (V * (P * P - Q * Q)) + P' * (V * ((2 : ℝ) • (P * Q)))) *ᵥ x)) ^ 2 ≤
      ν ^ 3 * ((y ⬝ᵥ y) * (x ⬝ᵥ x)) := by
  have e : y ⬝ᵥ ((Q' * (V * (P * P - Q * Q)) + P' * (V * ((2 : ℝ) • (P * Q)))) *ᵥ x) =
      (Q' *ᵥ y) ⬝ᵥ (V *ᵥ ((P * P - Q * Q) *ᵥ x)) +
      (P' *ᵥ y) ⬝ᵥ (V *ᵥ (((2 : ℝ) • (P * Q)) *ᵥ x)) := by
    rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, gen_dot_mulVec Q' hQ', gen_dot_mulVec P' hP']
  rw [e]
  refine (gen_cs2 hV _ _ _ _).trans ?_
  have h1 : (Q' *ᵥ y) ⬝ᵥ (Q' *ᵥ y) + (P' *ᵥ y) ⬝ᵥ (P' *ᵥ y) ≤ ν * (y ⬝ᵥ y) := by
    have := hn' y; linarith
  have h2 := gen_quad hP hQ hPQ hn hν x
  calc _ ≤ (ν * (y ⬝ᵥ y)) * (ν ^ 2 * (x ⬝ᵥ x)) :=
        mul_le_mul h1 h2 (add_nonneg (gen_dot_nonneg _) (gen_dot_nonneg _))
          (mul_nonneg hν (gen_dot_nonneg y))
    _ = _ := by ring

private lemma gen_bilB {P Q P' Q' V : Matrix ι ι ℝ} (hP : Pᵀ = P) (hQ : Qᵀ = Q) (hP' : P'ᵀ = P')
    (hQ' : Q'ᵀ = Q') (hPQ' : P' * Q' = Q' * P') {ν : ℝ} (hν : 0 ≤ ν)
    (hn : ∀ z : ι → ℝ, (P *ᵥ z) ⬝ᵥ (P *ᵥ z) + (Q *ᵥ z) ⬝ᵥ (Q *ᵥ z) ≤ ν * (z ⬝ᵥ z))
    (hn' : ∀ z : ι → ℝ, (P' *ᵥ z) ⬝ᵥ (P' *ᵥ z) + (Q' *ᵥ z) ⬝ᵥ (Q' *ᵥ z) ≤ ν * (z ⬝ᵥ z))
    (hV : ∀ w : ι → ℝ, (V *ᵥ w) ⬝ᵥ (V *ᵥ w) ≤ w ⬝ᵥ w) (x y : ι → ℝ) :
    (y ⬝ᵥ ((((2 : ℝ) • (P' * Q')) * (V * P) + (P' * P' - Q' * Q') * (V * Q)) *ᵥ x)) ^ 2 ≤
      ν ^ 3 * ((y ⬝ᵥ y) * (x ⬝ᵥ x)) := by
  have t1 : (((2 : ℝ) • (P' * Q')))ᵀ = (2 : ℝ) • (P' * Q') := by
    rw [Matrix.transpose_smul, Matrix.transpose_mul, hP', hQ', ← hPQ']
  have t2 : (P' * P' - Q' * Q')ᵀ = P' * P' - Q' * Q' := by
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, hP', hQ']
  have e : y ⬝ᵥ ((((2 : ℝ) • (P' * Q')) * (V * P) + (P' * P' - Q' * Q') * (V * Q)) *ᵥ x) =
      (((2 : ℝ) • (P' * Q')) *ᵥ y) ⬝ᵥ (V *ᵥ (P *ᵥ x)) +
      ((P' * P' - Q' * Q') *ᵥ y) ⬝ᵥ (V *ᵥ (Q *ᵥ x)) := by
    rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, gen_dot_mulVec _ t1, gen_dot_mulVec _ t2]
  rw [e]
  refine (gen_cs2 hV _ _ _ _).trans ?_
  have h1 := gen_quad hP' hQ' hPQ' hn' hν y
  have h2 : (P *ᵥ x) ⬝ᵥ (P *ᵥ x) + (Q *ᵥ x) ⬝ᵥ (Q *ᵥ x) ≤ ν * (x ⬝ᵥ x) := hn x
  have h1' : (((2 : ℝ) • (P' * Q')) *ᵥ y) ⬝ᵥ (((2 : ℝ) • (P' * Q')) *ᵥ y) +
      ((P' * P' - Q' * Q') *ᵥ y) ⬝ᵥ ((P' * P' - Q' * Q') *ᵥ y) ≤ ν ^ 2 * (y ⬝ᵥ y) := by
    linarith
  calc _ ≤ (ν ^ 2 * (y ⬝ᵥ y)) * (ν * (x ⬝ᵥ x)) :=
        mul_le_mul h1' h2 (add_nonneg (gen_dot_nonneg _) (gen_dot_nonneg _))
          (mul_nonneg (sq_nonneg ν) (gen_dot_nonneg y))
    _ = _ := by ring

end Gen


section Blk
open Muon.DetEquiv Matrix

private lemma blk_one_sub {m n : ℕ} (A : Mat m m) (D : Mat n n) (c : ℝ) :
    (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) - c • Matrix.fromBlocks A 0 0 D =
      Matrix.fromBlocks (1 - c • A) 0 0 (1 - c • D) := by
  rw [← Matrix.fromBlocks_one]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

private lemma blk_X_eq {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) : Xs K s = K * Rts K s := by
  have h := (lem_app_de_resolvent K s hs).2.2.2.1
  unfold Xs; exact h

private lemma blk_XT1 {m n : ℕ} (K : Mat m n) (s : ℝ) : (Xs K s)ᵀ = Kᵀ * Rs K s := by
  unfold Xs; rw [Matrix.transpose_mul, fl_Rs_symm]

private lemma blk_XT2 {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    (Xs K s)ᵀ = Rts K s * Kᵀ := by
  rw [blk_X_eq K hs, Matrix.transpose_mul, fl_Rts_symm]

private lemma blk_XR {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    Xs K s * Rts K s = Rs K s * Xs K s := by
  conv_rhs => rw [blk_X_eq K hs]
  unfold Xs
  rw [Matrix.mul_assoc]

private lemma blk_XKT {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    Xs K s * Kᵀ = 1 - s • Rs K s := by
  unfold Xs; rw [Matrix.mul_assoc]; exact (lem_app_de_resolvent K s hs).2.2.2.2.2.1

private lemma blk_XTK {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    (Xs K s)ᵀ * K = 1 - s • Rts K s := by
  rw [blk_XT1, Matrix.mul_assoc]
  have := (lem_app_de_resolvent K s hs).2.2.2.2.1
  rw [← Matrix.mul_assoc]; exact this

private lemma blk_rel1 {m n : ℕ} (K : Mat m n) {c s : ℝ} (hs : 0 < s) (hc : c * c = s) :
    Matrix.fromBlocks 0 (Xs K s) (Xs K s)ᵀ 0 * Matrix.fromBlocks 0 K Kᵀ 0 =
      1 - c • (c • Matrix.fromBlocks (Rs K s) 0 0 (Rts K s)) := by
  rw [smul_smul, hc, blk_one_sub, Matrix.fromBlocks_multiply]
  simp only [smul_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  rw [blk_XKT K hs, blk_XTK K hs]

private lemma blk_rel2 {m n : ℕ} (K : Mat m n) {c s : ℝ} (hs : 0 < s) :
    (c • Matrix.fromBlocks (Rs K s) 0 0 (Rts K s)) * Matrix.fromBlocks 0 K Kᵀ 0 =
      c • Matrix.fromBlocks 0 (Xs K s) (Xs K s)ᵀ 0 := by
  rw [Matrix.smul_mul, Matrix.fromBlocks_multiply]
  congr 1
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  rw [← blk_XT2 K hs]
  rfl


private lemma blk_XTR {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    (Xs K s)ᵀ * Rs K s = Rts K s * (Xs K s)ᵀ := by
  have h := congrArg Matrix.transpose (blk_XR K hs)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, fl_Rs_symm, fl_Rts_symm] at h
  exact h.symm

private lemma blk_P_symm {m n : ℕ} (X : Mat m n) :
    (Matrix.fromBlocks 0 X Xᵀ 0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ)ᵀ =
      Matrix.fromBlocks 0 X Xᵀ 0 := by
  rw [Matrix.fromBlocks_transpose]; simp

private lemma blk_Q_symm {m n : ℕ} (K : Mat m n) (c s : ℝ) :
    (c • Matrix.fromBlocks (Rs K s) 0 0 (Rts K s))ᵀ =
      c • Matrix.fromBlocks (Rs K s) 0 0 (Rts K s) := by
  rw [Matrix.transpose_smul, Matrix.fromBlocks_transpose, fl_Rs_symm, fl_Rts_symm]; simp

private lemma blk_PQ {m n : ℕ} (K : Mat m n) (c : ℝ) {s : ℝ} (hs : 0 < s) :
    Matrix.fromBlocks 0 (Xs K s) (Xs K s)ᵀ 0 * (c • Matrix.fromBlocks (Rs K s) 0 0 (Rts K s)) =
      c • Matrix.fromBlocks 0 (Rs K s * Xs K s) (Rs K s * Xs K s)ᵀ 0 := by
  rw [Matrix.mul_smul, Matrix.fromBlocks_multiply]
  congr 1
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  rw [Matrix.transpose_mul, fl_Rs_symm, blk_XR K hs, blk_XTR K hs]

private lemma blk_QP {m n : ℕ} (K : Mat m n) (c : ℝ) {s : ℝ} (hs : 0 < s) :
    (c • Matrix.fromBlocks (Rs K s) 0 0 (Rts K s)) * Matrix.fromBlocks 0 (Xs K s) (Xs K s)ᵀ 0 =
      c • Matrix.fromBlocks 0 (Rs K s * Xs K s) (Rs K s * Xs K s)ᵀ 0 := by
  rw [Matrix.smul_mul, Matrix.fromBlocks_multiply]
  congr 1
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  rw [Matrix.transpose_mul, fl_Rs_symm, blk_XTR K hs]

private lemma blk_dot_elim {m n : ℕ} (a c : Vec m) (b d : Vec n) :
    (Sum.elim a b) ⬝ᵥ (Sum.elim c d) = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

private lemma blk_split {m n : ℕ} (z : Fin m ⊕ Fin n → ℝ) :
    z = Sum.elim (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) := by
  funext i; rcases i with i | i <;> rfl

private lemma blk_hn {m n : ℕ} (K : Mat m n) {c s : ℝ} (hs : 0 < s) (hc : c * c = s)
    (z : Fin m ⊕ Fin n → ℝ) :
    ((Matrix.fromBlocks 0 (Xs K s) (Xs K s)ᵀ 0) *ᵥ z) ⬝ᵥ ((Matrix.fromBlocks 0 (Xs K s) (Xs K s)ᵀ 0) *ᵥ z)
    + ((c • Matrix.fromBlocks (Rs K s) 0 0 (Rts K s)) *ᵥ z) ⬝ᵥ
        ((c • Matrix.fromBlocks (Rs K s) 0 0 (Rts K s)) *ᵥ z) ≤ s⁻¹ * (z ⬝ᵥ z) := by
  rw [blk_split z]
  generalize (fun i => z (Sum.inl i)) = z1
  generalize (fun j => z (Sum.inr j)) = z2
  simp only [Matrix.smul_mulVec, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, zero_add, add_zero,
    smul_dotProduct, dotProduct_smul, blk_dot_elim, smul_eq_mul, Sum.elim_comp_inl,
    Sum.elim_comp_inr]
  have h1 := fl_S1 K hs z1
  have h2 := fl_S2 K hs z2
  simp only [fl_sqNorm_eq_dot] at h1 h2
  rw [blk_XT1, blk_X_eq K hs, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have e : c * (c * (Rs K s *ᵥ z1 ⬝ᵥ Rs K s *ᵥ z1 + Rts K s *ᵥ z2 ⬝ᵥ Rts K s *ᵥ z2)) =
      s * (Rs K s *ᵥ z1 ⬝ᵥ Rs K s *ᵥ z1) + s * (Rts K s *ᵥ z2 ⬝ᵥ Rts K s *ᵥ z2) := by
    rw [← mul_assoc, hc]; ring
  rw [e]
  rw [div_eq_inv_mul] at h1 h2
  nlinarith

private lemma blk_hV {m n : ℕ} (U : Mat m n) (hU : opNorm U ≤ 1) (w : Fin m ⊕ Fin n → ℝ) :
    ((Matrix.fromBlocks 0 U Uᵀ 0) *ᵥ w) ⬝ᵥ ((Matrix.fromBlocks 0 U Uᵀ 0) *ᵥ w) ≤ w ⬝ᵥ w := by
  rw [blk_split w]
  generalize (fun i => w (Sum.inl i)) = w1
  generalize (fun j => w (Sum.inr j)) = w2
  simp only [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, zero_add, add_zero, blk_dot_elim,
    Sum.elim_comp_inl, Sum.elim_comp_inr]
  have h1 := fl_sq_mulVec_le U w2
  have h2 := fl_sq_mulVec_le Uᵀ w1
  rw [fl_opNorm_transpose] at h2
  simp only [fl_sqNorm_eq_dot] at h1 h2
  have h0 := fl_opNorm_nonneg U
  have hsq : opNorm U ^ 2 ≤ 1 := by nlinarith
  have a1 := fl_sqNorm_nonneg w1
  have a2 := fl_sqNorm_nonneg w2
  simp only [fl_sqNorm_eq_dot] at a1 a2
  nlinarith

private lemma fl_bil_to_op {a b : ℕ} (M : Mat a b) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ (x : Vec b) (y : Vec a), (y ⬝ᵥ (M *ᵥ x)) ^ 2 ≤ L ^ 2 * (sqNorm y * sqNorm x)) :
    opNorm M ≤ L := by
  refine fl_opNorm_le M hL fun x => ?_
  set y := M *ᵥ x with hy
  have h1 := h x y
  rw [← hy, ← fl_sqNorm_eq_dot] at h1
  have hY := fl_sqNorm_nonneg y
  have hX := fl_sqNorm_nonneg x
  rcases eq_or_lt_of_le hY with h0 | hpos
  · rw [← h0]; positivity
  · have : sqNorm y * sqNorm y ≤ sqNorm y * (L ^ 2 * sqNorm x) := by nlinarith
    exact le_of_mul_le_mul_left this hpos

private lemma blk_op21 {m n : ℕ} (W : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ x y : Fin m ⊕ Fin n → ℝ, (y ⬝ᵥ (W *ᵥ x)) ^ 2 ≤ L ^ 2 * ((y ⬝ᵥ y) * (x ⬝ᵥ x))) :
    opNorm (Matrix.of fun (b : Fin n) (a : Fin m) => W (Sum.inr b) (Sum.inl a)) ≤ L := by
  refine fl_bil_to_op _ hL fun x y => ?_
  have h1 := h (Sum.elim x 0) (Sum.elim 0 y)
  have e : y ⬝ᵥ ((Matrix.of fun (b : Fin n) (a : Fin m) => W (Sum.inr b) (Sum.inl a)) *ᵥ x) =
      (Sum.elim (0 : Vec m) y) ⬝ᵥ (W *ᵥ Sum.elim x (0 : Vec n)) := by
    simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type]
  rw [e]
  simpa [blk_dot_elim, fl_sqNorm_eq_dot] using h1

private lemma blk_op12 {m n : ℕ} (W : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ x y : Fin m ⊕ Fin n → ℝ, (y ⬝ᵥ (W *ᵥ x)) ^ 2 ≤ L ^ 2 * ((y ⬝ᵥ y) * (x ⬝ᵥ x))) :
    opNorm (Matrix.of fun (a : Fin m) (b : Fin n) => W (Sum.inl a) (Sum.inr b)) ≤ L := by
  refine fl_bil_to_op _ hL fun x y => ?_
  have h1 := h (Sum.elim 0 x) (Sum.elim y 0)
  have e : y ⬝ᵥ ((Matrix.of fun (a : Fin m) (b : Fin n) => W (Sum.inl a) (Sum.inr b)) *ᵥ x) =
      (Sum.elim y (0 : Vec n)) ⬝ᵥ (W *ᵥ Sum.elim (0 : Vec m) x) := by
    simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type]
  rw [e]
  simpa [blk_dot_elim, fl_sqNorm_eq_dot] using h1

private lemma blk_trace {m n : ℕ} (E : Mat m n) (W : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) :
    Matrix.trace (Matrix.fromBlocks 0 E Eᵀ 0 * W) =
      Matrix.trace (E * Matrix.of fun (b : Fin n) (a : Fin m) => W (Sum.inr b) (Sum.inl a)) +
      Matrix.trace (Eᵀ * Matrix.of fun (a : Fin m) (b : Fin n) => W (Sum.inl a) (Sum.inr b)) := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_sum_type]

private lemma blk_flip1 {ι : Type*} [Fintype ι] [DecidableEq ι] {A B C : Matrix ι ι ℝ} {c : ℝ}
    (hA : Aᵀ = A) (hB : Bᵀ = B) (hC : Cᵀ = C) (h : A * B = 1 - c • C) :
    B * A = 1 - c • C := by
  have := congrArg Matrix.transpose h
  rwa [Matrix.transpose_mul, hA, hB, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_smul, hC] at this

private lemma blk_flip2 {ι : Type*} [Fintype ι] [DecidableEq ι] {A B D : Matrix ι ι ℝ} {c : ℝ}
    (hA : Aᵀ = A) (hB : Bᵀ = B) (hD : Dᵀ = D) (h : A * B = c • D) :
    B * A = c • D := by
  have := congrArg Matrix.transpose h
  rwa [Matrix.transpose_mul, hA, hB, Matrix.transpose_smul, hD] at this

private lemma blk_sub {m n : ℕ} (A B : Mat m n) :
    Matrix.fromBlocks 0 A Aᵀ 0 - Matrix.fromBlocks 0 B Bᵀ 0 =
      (Matrix.fromBlocks 0 (A - B) (A - B)ᵀ 0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) := by
  ext (i | i) (j | j) <;> simp

private lemma blk_tr2 {m n : ℕ} (U Z : Mat m n) :
    Matrix.trace (Matrix.fromBlocks 0 U Uᵀ 0 * Matrix.fromBlocks 0 Z Zᵀ 0) =
      2 * Matrix.trace (Uᵀ * Z) := by
  have h : Matrix.trace (U * Zᵀ) = Matrix.trace (Uᵀ * Z) := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.trace_mul_comm]
  have h2 : Matrix.trace (Matrix.fromBlocks 0 U Uᵀ 0 * Matrix.fromBlocks 0 Z Zᵀ 0) =
      Matrix.trace (U * Zᵀ) + Matrix.trace (Uᵀ * Z) := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_sum_type]
  rw [h2, h]; ring

private lemma blk_tr_bound {m n : ℕ} (E : Mat m n)
    (W : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ x y : Fin m ⊕ Fin n → ℝ, (y ⬝ᵥ (W *ᵥ x)) ^ 2 ≤ L ^ 2 * ((y ⬝ᵥ y) * (x ⬝ᵥ x))) :
    |Matrix.trace (Matrix.fromBlocks 0 E Eᵀ 0 * W)| ≤ 2 * L * nuc E := by
  rw [blk_trace]
  have h1 := trace_mul_le_opNorm_mul_nuc
    (Matrix.of fun (b : Fin n) (a : Fin m) => W (Sum.inr b) (Sum.inl a)) E
  have h2 := trace_mul_le_opNorm_mul_nuc
    (Matrix.of fun (a : Fin m) (b : Fin n) => W (Sum.inl a) (Sum.inr b)) Eᵀ
  rw [← Matrix.trace_mul_comm] at h1 h2
  rw [nuc_transpose] at h2
  have o1 := blk_op21 W hL h
  have o2 := blk_op12 W hL h
  have n0 := nuc_nonneg E
  have h1' := h1.trans (mul_le_mul_of_nonneg_right o1 n0)
  have h2' := h2.trans (mul_le_mul_of_nonneg_right o2 n0)
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ L * nuc E + L * nuc E := add_le_add h1' h2'
    _ = _ := by ring

private lemma blk_key {m n : ℕ} (K K' : Mat m n) {s : ℝ} (hs : 0 < s) (U : Mat m n)
    (hU : opNorm U ≤ 1) :
    |Matrix.trace (Uᵀ * (Rs K s * Xs K s - Rs K' s * Xs K' s))| ≤ (s ^ 2)⁻¹ * nuc (K - K') := by
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ c * c = s :=
    ⟨Real.sqrt s, Real.sqrt_pos.mpr hs, Real.mul_self_sqrt hs.le⟩
  have hν : (0 : ℝ) ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have sP := blk_P_symm (Xs K s)
  have sP' := blk_P_symm (Xs K' s)
  have sQ := blk_Q_symm K c s
  have sQ' := blk_Q_symm K' c s
  have sS := blk_P_symm K'
  have hPT := blk_rel1 K hs hc
  have hQT := blk_rel2 K (c := c) hs
  have hSP := blk_flip1 sP' sS sQ' (blk_rel1 K' hs hc)
  have hSQ := blk_flip2 sQ' sS sP' (blk_rel2 K' (c := c) hs)
  have hPQ : Matrix.fromBlocks 0 (Xs K s) (Xs K s)ᵀ 0 * (c • Matrix.fromBlocks (Rs K s) 0 0 (Rts K s)) =
      (c • Matrix.fromBlocks (Rs K s) 0 0 (Rts K s)) * Matrix.fromBlocks 0 (Xs K s) (Xs K s)ᵀ 0 := by
    rw [blk_PQ K c hs, blk_QP K c hs]
  have hPQ' : Matrix.fromBlocks 0 (Xs K' s) (Xs K' s)ᵀ 0 * (c • Matrix.fromBlocks (Rs K' s) 0 0 (Rts K' s)) =
      (c • Matrix.fromBlocks (Rs K' s) 0 0 (Rts K' s)) * Matrix.fromBlocks 0 (Xs K' s) (Xs K' s)ᵀ 0 := by
    rw [blk_PQ K' c hs, blk_QP K' c hs]
  have key := gen_trace (V := Matrix.fromBlocks 0 U Uᵀ 0) hPT hQT hSP hSQ hPQ hPQ'
  have hn := blk_hn K hs hc
  have hn' := blk_hn K' hs hc
  have hV := blk_hV U hU
  set L : ℝ := (c⁻¹) ^ 3 with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hL2 : L ^ 2 = (s⁻¹) ^ 3 := by
    rw [hLdef, ← hc, mul_inv]; ring
  have bA := fun x y => gen_bilA sP sQ sP' sQ' hPQ hν hn hn' hV x y
  have bB := fun x y => gen_bilB sP sQ sP' sQ' hPQ' hν hn hn' hV x y
  simp only [← hL2] at bA bB
  rw [blk_sub K' K] at key
  have tA := blk_tr_bound (K' - K) _ hL0 bA
  have tB := blk_tr_bound (K' - K) _ hL0 bB
  have hlhs : Matrix.trace (Matrix.fromBlocks 0 U Uᵀ 0 *
      ((2 : ℝ) • (Matrix.fromBlocks 0 (Xs K s) (Xs K s)ᵀ 0 * (c • Matrix.fromBlocks (Rs K s) 0 0 (Rts K s))) -
       (2 : ℝ) • (Matrix.fromBlocks 0 (Xs K' s) (Xs K' s)ᵀ 0 * (c • Matrix.fromBlocks (Rs K' s) 0 0 (Rts K' s))))) =
      4 * c * Matrix.trace (Uᵀ * (Rs K s * Xs K s - Rs K' s * Xs K' s)) := by
    rw [blk_PQ K c hs, blk_PQ K' c hs, smul_smul, smul_smul, ← smul_sub, blk_sub, Matrix.mul_smul,
      Matrix.trace_smul, blk_tr2, smul_eq_mul]
    ring
  rw [hlhs] at key
  have hE : nuc (K' - K) = nuc (K - K') := by
    rw [show K' - K = (-1 : ℝ) • (K - K') by simp, nuc_smul]; simp
  rw [hE] at tA tB
  have hb : |4 * c * Matrix.trace (Uᵀ * (Rs K s * Xs K s - Rs K' s * Xs K' s))| ≤
      4 * L * nuc (K - K') := by
    rw [key]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ 2 * L * nuc (K - K') + 2 * L * nuc (K - K') := add_le_add tA tB
      _ = _ := by ring
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * c)] at hb
  have hLc : L / c = (s ^ 2)⁻¹ := by
    rw [hLdef, ← hc]; field_simp
  rw [← hLc, div_mul_eq_mul_div, le_div_iff₀ hc0]
  nlinarith

end Blk


section Dv
open Muon.DetEquiv Matrix
open scoped Matrix.Norms.L2Operator

private lemma dv_unit {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    IsUnit (K * Kᵀ + s • (1 : Mat m m)) := by
  have h1 : (K * Kᵀ).PosSemidef := by simpa using Matrix.posSemidef_self_mul_conjTranspose K
  have h2 : (s • (1 : Mat m m)).PosDef := Matrix.PosDef.one.smul hs
  exact (Matrix.PosDef.add_posSemidef h2 h1 |> fun h => by rwa [add_comm] at h : (K * Kᵀ + s • (1 : Mat m m)).PosDef).isUnit

private lemma dv_Rs_deriv {m n : ℕ} (K : Mat m n) {s0 : ℝ} (hs : 0 < s0) :
    HasDerivAt (fun s : ℝ => Rs K s) (-(Rs K s0 * Rs K s0)) s0 := by
  have hu := dv_unit K hs
  have h1 : HasDerivAt (fun s : ℝ => K * Kᵀ + s • (1 : Mat m m)) (1 : Mat m m) s0 := by
    have := ((hasDerivAt_id s0).smul_const (1 : Mat m m)).const_add (K * Kᵀ)
    simpa using this
  have h2 := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  have h3 := h2.comp_hasDerivAt s0 h1
  have e : ∀ s, Rs K s = Ring.inverse (K * Kᵀ + s • (1 : Mat m m)) := fun s => by
    unfold Rs; rw [Matrix.nonsing_inv_eq_ringInverse]
  have e2 : (hu.unit⁻¹ : Units (Mat m m)).val = Rs K s0 := by
    rw [e s0, ← Ring.inverse_unit hu.unit]
    rfl
  have hfun : (fun s : ℝ => Rs K s) = Ring.inverse ∘ fun s : ℝ => K * Kᵀ + s • (1 : Mat m m) :=
    funext fun s => e s
  rw [hfun]
  convert h3 using 1
  simp [ContinuousLinearMap.mulLeftRight_apply, e2]

private lemma dv_phi_ex {m n : ℕ} (U K : Mat m n) :
    ∃ Φ : Mat m m →L[ℝ] ℝ, ∀ R : Mat m m, Φ R = Matrix.trace (Uᵀ * (R * K)) := by
  refine ⟨LinearMap.toContinuousLinearMap
    { toFun := fun R => Matrix.trace (Uᵀ * (R * K))
      map_add' := fun R R' => by simp [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
      map_smul' := fun c R => by simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul] },
    fun R => rfl⟩

private lemma dv_g_deriv {m n : ℕ} (K K' U : Mat m n) {s0 : ℝ} (hs : 0 < s0) :
    HasDerivAt (fun s : ℝ => Matrix.trace (Uᵀ * (Xs K s - Xs K' s)))
      (-Matrix.trace (Uᵀ * (Rs K s0 * Xs K s0 - Rs K' s0 * Xs K' s0))) s0 := by
  obtain ⟨Φ, hΦ⟩ := dv_phi_ex U K
  obtain ⟨Φ', hΦ'⟩ := dv_phi_ex U K'
  have h1 := Φ.hasFDerivAt.comp_hasDerivAt s0 (dv_Rs_deriv K hs)
  have h2 := Φ'.hasFDerivAt.comp_hasDerivAt s0 (dv_Rs_deriv K' hs)
  have h3 := h1.sub h2
  have hf : (fun s : ℝ => Matrix.trace (Uᵀ * (Xs K s - Xs K' s))) =
      (Φ ∘ fun s : ℝ => Rs K s) - (Φ' ∘ fun s : ℝ => Rs K' s) := by
    funext s
    simp only [Pi.sub_apply, Function.comp, hΦ, hΦ', Xs, Matrix.mul_sub, Matrix.trace_sub]
  rw [hf]
  convert h3 using 1
  simp only [hΦ, hΦ', Xs, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_sub, Matrix.trace_neg,
    Matrix.trace_sub, Matrix.mul_assoc]
  ring

end Dv


section Ig
open Set MeasureTheory Filter Topology

private lemma ig_base :
    IntegrableOn (fun x : ℝ => ((1 + x ^ 2)⁻¹) ^ 2) (Ioi 0) ∧
    ∫ x in Ioi (0 : ℝ), ((1 + x ^ 2)⁻¹) ^ 2 = Real.pi / 4 := by
  have hint : IntegrableOn (fun x : ℝ => ((1 + x ^ 2)⁻¹) ^ 2) (Ioi 0) := by
    refine Integrable.mono' (integrable_inv_one_add_sq.integrableOn (s := Ioi (0 : ℝ))) ?_ ?_
    · exact ((Continuous.inv₀ (by fun_prop) (fun x => by positivity)).pow 2 : Continuous fun x : ℝ => ((1 + x ^ 2)⁻¹) ^ 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have h1 : 0 < 1 + x ^ 2 := by positivity
      have h2 : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ((1 + x ^ 2)⁻¹) ^ 2 = (1 + x ^ 2)⁻¹ * (1 + x ^ 2)⁻¹ := sq _
        _ ≤ (1 + x ^ 2)⁻¹ * 1 := by gcongr
        _ = _ := mul_one _
  refine ⟨hint, ?_⟩
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => x / (2 * (1 + x ^ 2)) + Real.arctan x / 2)
      (((1 + x ^ 2)⁻¹) ^ 2) x := by
    intro x _
    have h1 : (1 + x ^ 2) ≠ 0 := by positivity
    have hden : HasDerivAt (fun x : ℝ => 2 * (1 + x ^ 2)) (4 * x) x := by
      have := ((hasDerivAt_pow 2 x).const_add 1).const_mul 2
      convert this using 1
      simp; ring
    have h2 := (hasDerivAt_id' x).div hden (by positivity)
    have h3 := (Real.hasDerivAt_arctan x).div_const 2
    convert h2.add h3 using 1
    field_simp
    ring
  have := integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
    (f := fun x : ℝ => x / (2 * (1 + x ^ 2)) + Real.arctan x / 2) (m := Real.pi / 4)
    (Continuous.continuousWithinAt (Continuous.add (Continuous.div continuous_id (by fun_prop) (fun x => by positivity)) (Real.continuous_arctan.div_const 2))) hd hint ?_
  · rw [this]; simp
  · have t1 : Tendsto (fun x : ℝ => x / (2 * (1 + x ^ 2))) atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
        positivity
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
        have hx0 : 0 < x := by linarith
        rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hx0]
        nlinarith
    have t2 : Tendsto (fun x : ℝ => Real.arctan x / 2) atTop (𝓝 (Real.pi / 4)) := by
      have := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).div_const 2
      convert this using 2; ring
    convert t1.add t2 using 2; ring

private lemma ig_scaled {ϱ : ℝ} (hϱ : 0 < ϱ) :
    IntegrableOn (fun u : ℝ => ((ϱ + u ^ 2)⁻¹) ^ 2) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), ((ϱ + u ^ 2)⁻¹) ^ 2 = Real.pi / 4 * ϱ ^ (-(3 / 2 : ℝ)) := by
  have hr : 0 < Real.sqrt ϱ := Real.sqrt_pos.mpr hϱ
  have hb : 0 < (Real.sqrt ϱ)⁻¹ := inv_pos.mpr hr
  have hfun : (fun u : ℝ => ((ϱ + u ^ 2)⁻¹) ^ 2) =
      fun u => (ϱ⁻¹) ^ 2 * (fun x : ℝ => ((1 + x ^ 2)⁻¹) ^ 2) ((Real.sqrt ϱ)⁻¹ * u) := by
    funext u
    have : ϱ + u ^ 2 = ϱ * (1 + ((Real.sqrt ϱ)⁻¹ * u) ^ 2) := by
      rw [mul_pow, inv_pow, Real.sq_sqrt hϱ.le]; field_simp
    simp only [this, mul_inv, mul_pow]
  obtain ⟨hint, hval⟩ := ig_base
  refine ⟨?_, ?_⟩
  · rw [hfun]
    refine Integrable.const_mul ?_ _
    exact (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => ((1 + x ^ 2)⁻¹) ^ 2) 0 hb).mpr
      (by simpa using hint)
  · rw [hfun, integral_const_mul,
      integral_comp_mul_left_Ioi (fun x : ℝ => ((1 + x ^ 2)⁻¹) ^ 2) 0 hb]
    simp only [mul_zero, hval, smul_eq_mul, inv_inv]
    have h1 : ϱ ^ (-(3 / 2 : ℝ)) = ((Real.sqrt ϱ)⁻¹) ^ 3 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul hϱ.le,
        ← Real.rpow_mul hϱ.le]; norm_num
    have h2 : ϱ⁻¹ = (Real.sqrt ϱ)⁻¹ * (Real.sqrt ϱ)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hϱ.le]
    rw [h1, h2]
    field_simp

end Ig


section An
open Muon.DetEquiv MeasureTheory Matrix

private lemma an_q_diff {m n : ℕ} (K : Mat m n) {ϱ : ℝ} (hϱ : 0 < ϱ) (i : Fin m) (j : Fin n) :
    DifferentiableAt ℝ (fun x : ℝ => Q x K i j) ϱ := by
  have h := (Q_contDiffOn_pos m n).contDiffAt
    (show {p : (Fin m → Fin n → ℝ) × ℝ | 0 < p.2} ∈ 𝓝 ((fun i j => K i j), ϱ) from
      (isOpen_lt continuous_const continuous_snd).mem_nhds hϱ)
  have hc : ContDiffAt ℝ ∞ (fun x : ℝ => ((fun i j => K i j : Fin m → Fin n → ℝ), x)) ϱ :=
    (contDiff_const.prodMk contDiff_id).contDiffAt
  have h2 := h.comp ϱ hc
  have h3 := h2.differentiableAt (by simp)
  have h4 := (differentiableAt_pi.1 (differentiableAt_pi.1 h3 i) j)
  exact h4

private lemma an_F_form {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K K' U : Mat m n) :
    Matrix.trace (Uᵀ * (Q ϱ K - Q ϱ K')) = (2 / Real.pi) * ∫ u in Ioi (0 : ℝ),
      Matrix.trace (Uᵀ * (Xs K (ϱ + u ^ 2) - Xs K' (ϱ + u ^ 2))) := by
  simp only [fl_trace_eq_sum]
  exact fl_lin_eq hϱ K K' U

private lemma an_g_int {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K K' U : Mat m n) :
    IntegrableOn (fun u : ℝ => Matrix.trace (Uᵀ * (Xs K (ϱ + u ^ 2) - Xs K' (ϱ + u ^ 2)))) (Ioi 0) := by
  simp only [fl_trace_eq_sum]
  exact fl_lin_int hϱ K K' U

private lemma an_g_lip {m n : ℕ} (K K' U : Mat m n) (hU : opNorm U ≤ 1) {s2 s1 : ℝ} (hs2 : 0 < s2)
    (h : s2 ≤ s1) :
    |Matrix.trace (Uᵀ * (Xs K s1 - Xs K' s1)) - Matrix.trace (Uᵀ * (Xs K s2 - Xs K' s2))| ≤
      ((s2 ^ 2)⁻¹ * nuc (K - K')) * (s1 - s2) := by
  have hd : ∀ t ∈ Icc s2 s1, DifferentiableAt ℝ
      (fun s : ℝ => Matrix.trace (Uᵀ * (Xs K s - Xs K' s))) t := fun t ht =>
    (dv_g_deriv K K' U (lt_of_lt_of_le hs2 ht.1)).differentiableAt
  have hb : ∀ t ∈ Icc s2 s1, ‖deriv (fun s : ℝ => Matrix.trace (Uᵀ * (Xs K s - Xs K' s))) t‖ ≤
      (s2 ^ 2)⁻¹ * nuc (K - K') := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hs2 ht.1
    rw [(dv_g_deriv K K' U ht0).deriv, norm_neg, Real.norm_eq_abs]
    refine (blk_key K K' ht0 U hU).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (nuc_nonneg _)
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    exact pow_le_pow_left₀ hs2.le ht.1 2
  have := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc s2 s1)
    (show s2 ∈ Icc s2 s1 from ⟨le_rfl, h⟩) (show s1 ∈ Icc s2 s1 from ⟨h, le_rfl⟩)
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 h)] at this

private lemma an_F_diff {m n : ℕ} {ϱ h : ℝ} (hϱ : 0 < ϱ) (hh : 0 < h) (K K' U : Mat m n)
    (hU : opNorm U ≤ 1) :
    |Matrix.trace (Uᵀ * (Q (ϱ + h) K - Q (ϱ + h) K')) - Matrix.trace (Uᵀ * (Q ϱ K - Q ϱ K'))| ≤
      h * ((1 / 2) * ϱ ^ (-(3 / 2 : ℝ)) * nuc (K - K')) := by
  have hϱh : 0 < ϱ + h := by linarith
  rw [an_F_form hϱh, an_F_form hϱ, ← mul_sub, ← integral_sub (an_g_int hϱh K K' U) (an_g_int hϱ K K' U)]
  obtain ⟨hint, hval⟩ := ig_scaled hϱ
  have hB : IntegrableOn (fun u : ℝ => (h * nuc (K - K')) * ((ϱ + u ^ 2)⁻¹) ^ 2) (Ioi 0) :=
    hint.const_mul _
  have hle : ‖∫ u in Ioi (0 : ℝ), (Matrix.trace (Uᵀ * (Xs K (ϱ + h + u ^ 2) - Xs K' (ϱ + h + u ^ 2))) -
      Matrix.trace (Uᵀ * (Xs K (ϱ + u ^ 2) - Xs K' (ϱ + u ^ 2))))‖ ≤
      ∫ u in Ioi (0 : ℝ), (h * nuc (K - K')) * ((ϱ + u ^ 2)⁻¹) ^ 2 := by
    refine norm_integral_le_of_norm_le hB ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_
    have hs2 : 0 < ϱ + u ^ 2 := by positivity
    have := an_g_lip K K' U hU hs2 (s1 := ϱ + h + u ^ 2) (by linarith)
    rw [Real.norm_eq_abs]
    refine this.trans (le_of_eq ?_)
    rw [inv_pow]
    have : ϱ + h + u ^ 2 - (ϱ + u ^ 2) = h := by ring
    rw [this]; ring
  rw [integral_const_mul, hval] at hle
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi)]
  rw [Real.norm_eq_abs] at hle
  calc _ ≤ (2 / Real.pi) * ((h * nuc (K - K')) * (Real.pi / 4 * ϱ ^ (-(3 / 2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by field_simp; ring

private lemma an_final {m n : ℕ} {ϱ' : ℝ} (hϱ : 0 < ϱ') (K K' : Mat m n) :
    nuc (ridgeDeriv ϱ' K - ridgeDeriv ϱ' K') ≤ (1 / 2) * ϱ' ^ (-(3 / 2 : ℝ)) * nuc (K - K') := by
  obtain ⟨U, hU, htr⟩ := (nuc_isGreatest_dual (ridgeDeriv ϱ' K - ridgeDeriv ϱ' K')).1
  rw [htr]
  have hF : HasDerivAt (fun x : ℝ => ∑ i, ∑ j, U i j * (Q x K i j - Q x K' i j))
      (∑ i, ∑ j, U i j * (ridgeDeriv ϱ' K i j - ridgeDeriv ϱ' K' i j)) ϱ' := by
    have hin : ∀ i : Fin m, HasDerivAt (fun x : ℝ => ∑ j, U i j * (Q x K i j - Q x K' i j))
        (∑ j, U i j * (ridgeDeriv ϱ' K i j - ridgeDeriv ϱ' K' i j)) ϱ' := fun i =>
      HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n))) fun j _ =>
        ((an_q_diff K hϱ i j).hasDerivAt.sub (an_q_diff K' hϱ i j).hasDerivAt).const_mul (U i j)
    exact HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin m))) fun i _ => hin i
  have hfun : (fun x : ℝ => Matrix.trace (Uᵀ * (Q x K - Q x K'))) =
      fun x : ℝ => ∑ i, ∑ j, U i j * (Q x K i j - Q x K' i j) := by
    funext x; rw [fl_trace_eq_sum]; rfl
  have hval : Matrix.trace (Uᵀ * (ridgeDeriv ϱ' K - ridgeDeriv ϱ' K')) =
      ∑ i, ∑ j, U i j * (ridgeDeriv ϱ' K i j - ridgeDeriv ϱ' K' i j) := by
    rw [fl_trace_eq_sum]; rfl
  rw [← hfun] at hF
  rw [hval]
  have hsl := hF.tendsto_slope_zero_right
  have habs := hsl.abs
  refine (le_abs_self _).trans ?_
  refine le_of_tendsto habs ?_
  refine eventually_nhdsWithin_of_forall fun t ht => ?_
  have ht' : 0 < t := ht
  have := an_F_diff hϱ ht' K K' U hU
  simp only [Function.comp, smul_eq_mul]
  rw [abs_mul, abs_inv, abs_of_pos ht']
  rw [inv_mul_le_iff₀ ht']
  linarith

end An

/-- `lem:app-dyn-schatten`, part (iii). Snapshot `cr-2026-10-23`. Statement, verbatim from
`section.tex` (full environment shown; this declaration is part (iii)):

    \begin{lemma}[Schatten sensitivity of the filter]\label{lem:app-dyn-schatten}
    Let $K,K'\in\R^{\Nout\times\Nin}$, $s>0$, $\ridge'>0$ and $p\in\{1,\infty\}$. Then
    \begin{enumerate}[label=(\roman*)]
    \item $\norm{\mathsf X_s(K)-\mathsf X_s(K')}_{S_p}\le s^{-1}\norm{K-K'}_{S_p}$;
    \item $\norm{\Qridge{\ridge'}(K)-\Qridge{\ridge'}(K')}_{S_p}\le\ridge'^{-1/2}\norm{K-K'}_{S_p}$;
    \item $\norm{\partial_{\ridge'}\Qridge{\ridge'}(K)-\partial_{\ridge'}\Qridge{\ridge'}(K')}_*\le\frac12\ridge'^{-3/2}\norm{K-K'}_*$;
    \item if $\ridge_1,\ridge_2\ge\ridge_\circ>0$, then
    $\norm{\Qridge{\ridge_1}(K)-\Qridge{\ridge_2}(K)}\le\abs{\ridge_1-\ridge_2}/(2\ridge_\circ)$
    and the same bound multiplied by $\sqrt{\min(\Nout,\Nin)}$ holds in Frobenius norm.
    \end{enumerate}
    \end{lemma}
-/
theorem lem_app_dyn_schatten_iii {m n : ℕ} {ϱ' : ℝ} (hϱ : 0 < ϱ') (K K' : Mat m n) :
    nuc (ridgeDeriv ϱ' K - ridgeDeriv ϱ' K') ≤ (1 / 2) * ϱ' ^ (-(3 / 2 : ℝ)) * nuc (K - K') := by
  exact an_final hϱ K K'

/-- `lem:app-dyn-schatten`, part (iv). Snapshot `cr-2026-10-23`. Statement, verbatim from
`section.tex` (full environment shown; this declaration is part (iv)):

    \begin{lemma}[Schatten sensitivity of the filter]\label{lem:app-dyn-schatten}
    Let $K,K'\in\R^{\Nout\times\Nin}$, $s>0$, $\ridge'>0$ and $p\in\{1,\infty\}$. Then
    \begin{enumerate}[label=(\roman*)]
    \item $\norm{\mathsf X_s(K)-\mathsf X_s(K')}_{S_p}\le s^{-1}\norm{K-K'}_{S_p}$;
    \item $\norm{\Qridge{\ridge'}(K)-\Qridge{\ridge'}(K')}_{S_p}\le\ridge'^{-1/2}\norm{K-K'}_{S_p}$;
    \item $\norm{\partial_{\ridge'}\Qridge{\ridge'}(K)-\partial_{\ridge'}\Qridge{\ridge'}(K')}_*\le\frac12\ridge'^{-3/2}\norm{K-K'}_*$;
    \item if $\ridge_1,\ridge_2\ge\ridge_\circ>0$, then
    $\norm{\Qridge{\ridge_1}(K)-\Qridge{\ridge_2}(K)}\le\abs{\ridge_1-\ridge_2}/(2\ridge_\circ)$
    and the same bound multiplied by $\sqrt{\min(\Nout,\Nin)}$ holds in Frobenius norm.
    \end{enumerate}
    \end{lemma}
-/
theorem lem_app_dyn_schatten_iv {m n : ℕ} {ϱo ϱ1 ϱ2 : ℝ} (hϱo : 0 < ϱo)
    (h1 : ϱo ≤ ϱ1) (h2 : ϱo ≤ ϱ2) (K : Mat m n) :
    opNorm (Q ϱ1 K - Q ϱ2 K) ≤ |ϱ1 - ϱ2| / (2 * ϱo) ∧
      fro (Q ϱ1 K - Q ϱ2 K) ≤ Real.sqrt ((min m n : ℕ) : ℝ) * (|ϱ1 - ϱ2| / (2 * ϱo)) := by
  obtain ⟨p, r, hp, hr, hK⟩ := Muon.Foundations.svd_rect_exists K
  have hpos : ∀ k : Fin K.rank, 0 < (Matrix.toEuclideanLin K).singularValues (k : ℕ) :=
    fun k => Muon.Foundations.singularValues_pos_of_lt_rank K k.isLt
  obtain ⟨hop, hfr⟩ := fl_iv_core hϱo h1 h2 K
    (fun k : Fin K.rank => (Matrix.toEuclideanLin K).singularValues (k : ℕ)) p r hpos hp hr hK
  refine ⟨hop, hfr.trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine Real.sqrt_le_sqrt ?_
  exact Nat.cast_le.mpr (le_min (Matrix.rank_le_height K) (Matrix.rank_le_width K))

private lemma fl_fro_sq {m n : ℕ} (A : Mat m n) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma fl_fro_smul {m n : ℕ} (t : ℝ) (R : Mat m n) : fro (t • R) = |t| * fro R := by
  unfold fro
  have h : ∑ i, ∑ j, ‖(t • R) i j‖ ^ 2 = t ^ 2 * ∑ i, ∑ j, ‖R i j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- `lem:app-dyn-second`, part (i). Snapshot `cr-2026-10-23`. Statement, verbatim from
`section.tex` (full environment shown; this declaration is part (i)):

    \begin{lemma}[Second-order filter estimates]\label{lem:app-dyn-second}
    Let $0<\ell_-\le\ell_+<\infty$. There is $C$, depending only on
    $(\ell_-,\ell_+)$, such that for $\ell\in[\ell_-,\ell_+]$ and all
    $N,N',R\in\R^{\Nout\times\Nin}$, with $D\Qridge\ell(N)[R]$ the derivative of
    $\Qridge\ell$ at $N$ in the direction $R$:
    \begin{enumerate}[label=(\roman*)]
    \item $\norm{D\Qridge\ell(N)[R]}_\F\le\ell^{-1/2}\norm R_\F$;
    \item $\norm{\Qridge\ell(N+R)-\Qridge\ell(N)-D\Qridge\ell(N)[R]}_\F\le C\norm R\norm R_\F$;
    \item $\norm{D\Qridge\ell(N)[R]-D\Qridge\ell(N')[R]}_\F\le C\norm{N-N'}\norm R_\F$;
    \item $\norm{\partial_\ell\Qridge\ell(N)}\le C$,
    $\norm{\partial_\ell\Qridge\ell(N)}_\F+\norm{\partial_\ell^2\Qridge\ell(N)}_\F\le C\sqrt{\min(\Nout,\Nin)}$,
    and $\norm{\partial_\ell\Qridge\ell(N)-\partial_\ell\Qridge\ell(N')}_\F\le C\norm{N-N'}_\F$.
    \end{enumerate}
    \end{lemma}
-/
theorem lem_app_dyn_second_i {ℓlo ℓhi : ℝ} (hlo : 0 < ℓlo) (hle : ℓlo ≤ ℓhi) :
    ∀ {m n : ℕ} (ℓ : ℝ), ℓ ∈ Icc ℓlo ℓhi → ∀ N R : Mat m n,
      fro (dirDeriv ℓ N R) ≤ ℓ ^ (-(1 / 2 : ℝ)) * fro R := by
  intro m n ℓ hℓ N R
  have hℓpos : 0 < ℓ := lt_of_lt_of_le hlo hℓ.1
  have hc0 : 0 ≤ ℓ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hℓpos.le _
  set c : ℝ := ℓ ^ (-(1 / 2 : ℝ)) with hc
  have hfroR : 0 ≤ fro R := Real.sqrt_nonneg _
  -- Lipschitz bound along the line t ↦ N + t R (from lem:app-setup-filter, part (iii))
  have hlip : ∀ t : ℝ, fro (Q ℓ (N + t • R) - Q ℓ N) ≤ c * (|t| * fro R) := by
    intro t
    have h := Muon.Setup.lem_app_setup_filter_iii ℓ hℓpos (N + t • R) N
    have hsub : N + t • R - N = t • R := by abel
    rw [hsub, fl_fro_smul] at h
    exact h
  -- smoothness of the entries of t ↦ Q ℓ (N + t R), via Q_contDiffOn_pos
  have hΦ := Q_contDiffOn_pos m n
  have hγd : DifferentiableAt ℝ (fun t : ℝ => ((fun a b => N a b + t * R a b), ℓ)) 0 := by
    fun_prop
  have hopen : {p : (Fin m → Fin n → ℝ) × ℝ | 0 < p.2} ∈
      𝓝 ((fun a b => N a b + (0 : ℝ) * R a b), ℓ) :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds (show (0 : ℝ) < ℓ from hℓpos)
  have hG : ∀ i j, DifferentiableAt ℝ
      (fun t : ℝ => Q ℓ (Matrix.of fun a b => N a b + t * R a b) i j) 0 := by
    intro i j
    have hcd : ContDiffAt ℝ ∞
        (fun p : (Fin m → Fin n → ℝ) × ℝ => Q p.2 (Matrix.of p.1) i j)
        ((fun a b => N a b + (0 : ℝ) * R a b), ℓ) :=
      contDiffAt_pi.1 (contDiffAt_pi.1 (hΦ.contDiffAt hopen) i) j
    have hdiff : DifferentiableAt ℝ
        ((fun p : (Fin m → Fin n → ℝ) × ℝ => Q p.2 (Matrix.of p.1) i j) ∘
          (fun t : ℝ => ((fun a b => N a b + t * R a b), ℓ))) 0 :=
      DifferentiableAt.comp (0 : ℝ) (hcd.differentiableAt (by norm_num)) hγd
    exact hdiff
  have hD : ∀ i j, HasDerivAt (fun t : ℝ => Q ℓ (N + t • R) i j) (dirDeriv ℓ N R i j) 0 := by
    intro i j
    have hf : (fun t : ℝ => Q ℓ (N + t • R) i j)
        = (fun t : ℝ => Q ℓ (Matrix.of fun a b => N a b + t * R a b) i j) := by
      funext t
      congr 2
    have h := (hG i j).hasDerivAt
    have hd : dirDeriv ℓ N R i j
        = deriv (fun t : ℝ => Q ℓ (Matrix.of fun a b => N a b + t * R a b) i j) 0 := by
      unfold dirDeriv
      simp only [Matrix.of_apply]
      rw [hf]
    rw [hd, hf]
    exact h
  -- difference quotients converge entrywise
  have hlim : ∀ i j, Tendsto (fun t : ℝ => (Q ℓ (N + t • R) i j - Q ℓ N i j) / t)
      (𝓝[≠] 0) (𝓝 (dirDeriv ℓ N R i j)) := by
    intro i j
    have h := hasDerivAt_iff_tendsto_slope.mp (hD i j)
    refine Tendsto.congr' ?_ h
    filter_upwards with t
    simp [slope_def_field]
  have hsum : Tendsto (fun t : ℝ => ∑ i, ∑ j, ((Q ℓ (N + t • R) i j - Q ℓ N i j) / t) ^ 2)
      (𝓝[≠] 0) (𝓝 (∑ i, ∑ j, (dirDeriv ℓ N R i j) ^ 2)) :=
    tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => (hlim i j).pow 2
  set S : ℝ := ∑ i, ∑ j, R i j ^ 2 with hS
  have hbound : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      ∑ i, ∑ j, ((Q ℓ (N + t • R) i j - Q ℓ N i j) / t) ^ 2 ≤ c ^ 2 * S := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    have ht2 : 0 < t ^ 2 := by positivity
    have h2 : fro (Q ℓ (N + t • R) - Q ℓ N) ^ 2 ≤ (c * (|t| * fro R)) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (hlip t) 2
    have h3 : (c * (|t| * fro R)) ^ 2 = c ^ 2 * t ^ 2 * S := by
      rw [mul_pow, mul_pow, sq_abs, fl_fro_sq R]
      ring
    rw [fl_fro_sq (Q ℓ (N + t • R) - Q ℓ N), h3] at h2
    simp only [Matrix.sub_apply] at h2
    have hsq : ∑ i, ∑ j, ((Q ℓ (N + t • R) i j - Q ℓ N i j) / t) ^ 2
        = (∑ i, ∑ j, (Q ℓ (N + t • R) i j - Q ℓ N i j) ^ 2) / t ^ 2 := by
      simp only [div_pow, Finset.sum_div]
    rw [hsq, div_le_iff₀ ht2]
    linarith
  have hle' : ∑ i, ∑ j, (dirDeriv ℓ N R i j) ^ 2 ≤ c ^ 2 * S :=
    le_of_tendsto hsum hbound
  have hL : fro (dirDeriv ℓ N R) ^ 2 = ∑ i, ∑ j, (dirDeriv ℓ N R i j) ^ 2 := fl_fro_sq _
  have hR : fro R ^ 2 = S := fl_fro_sq R
  have key : fro (dirDeriv ℓ N R) ^ 2 ≤ (c * fro R) ^ 2 := by
    rw [hL, mul_pow, hR]
    exact hle'
  have hnn : 0 ≤ c * fro R := mul_nonneg hc0 hfroR
  nlinarith [Real.sqrt_nonneg (∑ i, ∑ j, (dirDeriv ℓ N R i j) ^ 2), key, hnn]

section SecondAux
open Muon.DetEquiv MeasureTheory Matrix

private lemma sd_fro_nn {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma sd_fro_T {k l : ℕ} (A : Mat k l) : fro Aᵀ = fro A := by
  unfold fro
  congr 1
  exact Finset.sum_comm

private lemma sd_op_T {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := fl_opNorm_transpose A

open scoped Matrix.Norms.L2Operator in
private lemma sd_op_mul {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B

private lemma sd_fro_sq {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := fl_fro_sq A

private lemma sd_fro_mul_l {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ opNorm M * fro N := by
  have hcol : ∀ j : Fin r, ∑ i, (M * N) i j ^ 2 ≤ opNorm M ^ 2 * ∑ k, N k j ^ 2 := by
    intro j
    obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin q), ∀ k, v.ofLp k = N k j :=
      ⟨(EuclideanSpace.equiv (Fin q) ℝ).symm (fun k => N k j), fun k => rfl⟩
    have h1 : ‖(EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)‖ ≤ opNorm M * ‖v‖ := by
      open scoped Matrix.Norms.L2Operator in
      rw [opNorm_eq_norm]
      exact Matrix.l2_opNorm_mulVec M v
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at h2
    have e1 : ∀ i, ((EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)).ofLp i = (M * N) i j := by
      intro i
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, hv]
    have e2 : ∑ k, v.ofLp k ^ 2 = ∑ k, N k j ^ 2 :=
      Finset.sum_congr rfl fun k _ => by rw [hv]
    simp only [e1, e2] at h2
    exact h2
  have hfro : fro (M * N) ^ 2 ≤ (opNorm M * fro N) ^ 2 := by
    rw [sd_fro_sq, mul_pow, sd_fro_sq, Finset.sum_comm]
    calc ∑ j, ∑ i, (M * N) i j ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, N k j ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, N k j ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (sd_fro_nn _) (mul_nonneg (fl_opNorm_nonneg M) (sd_fro_nn N))
    two_ne_zero).mp hfro

private lemma sd_fro_mul_r {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ fro M * opNorm N := by
  have h := sd_fro_mul_l Nᵀ Mᵀ
  rw [sd_op_T, sd_fro_T, ← Matrix.transpose_mul, sd_fro_T] at h
  linarith [mul_comm (opNorm N) (fro M)]

/-- `‖A B C‖_F ≤ ‖A‖ ‖B‖_F ‖C‖`. -/
private lemma sd_fro3_mid {a b c d : ℕ} (A : Mat a b) (B : Mat b c) (C : Mat c d) :
    fro (A * B * C) ≤ opNorm A * fro B * opNorm C := by
  calc fro (A * B * C) ≤ fro (A * B) * opNorm C := sd_fro_mul_r _ _
    _ ≤ (opNorm A * fro B) * opNorm C :=
        mul_le_mul_of_nonneg_right (sd_fro_mul_l _ _) (fl_opNorm_nonneg _)

/-- `‖A B C‖_F ≤ ‖A‖_F ‖B‖ ‖C‖`. -/
private lemma sd_fro3_left {a b c d : ℕ} (A : Mat a b) (B : Mat b c) (C : Mat c d) :
    fro (A * B * C) ≤ fro A * opNorm B * opNorm C := by
  calc fro (A * B * C) ≤ fro (A * B) * opNorm C := sd_fro_mul_r _ _
    _ ≤ (fro A * opNorm B) * opNorm C :=
        mul_le_mul_of_nonneg_right (sd_fro_mul_r _ _) (fl_opNorm_nonneg _)

/-- `‖A B C‖_F ≤ ‖A‖ ‖B‖ ‖C‖_F`. -/
private lemma sd_fro3_right {a b c d : ℕ} (A : Mat a b) (B : Mat b c) (C : Mat c d) :
    fro (A * B * C) ≤ opNorm A * opNorm B * fro C := by
  calc fro (A * B * C) ≤ opNorm (A * B) * fro C := sd_fro_mul_l _ _
    _ ≤ (opNorm A * opNorm B) * fro C :=
        mul_le_mul_of_nonneg_right (sd_op_mul _ _) (sd_fro_nn _)

private lemma sd_fro_add {m n : ℕ} (A B : Mat m n) : fro (A + B) ≤ fro A + fro B := by
  have h := fro_eq_norm (𝕜 := ℝ) (A + B)
  have hA := fro_eq_norm (𝕜 := ℝ) A
  have hB := fro_eq_norm (𝕜 := ℝ) B
  open scoped Matrix.Norms.Frobenius in
  rw [h, hA, hB]
  exact norm_add_le A B

private lemma sd_fro_neg {m n : ℕ} (A : Mat m n) : fro (-A) = fro A := by
  have h := fl_fro_smul (-1) A
  simpa using h

private lemma sd_fro_sub {m n : ℕ} (A B : Mat m n) : fro (A - B) ≤ fro A + fro B := by
  rw [sub_eq_add_neg]
  have := sd_fro_add A (-B)
  rwa [sd_fro_neg] at this

private lemma sd_inv {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    Rs K s * (K * Kᵀ + s • (1 : Mat m m)) = 1 ∧ (K * Kᵀ + s • (1 : Mat m m)) * Rs K s = 1 := by
  have h6 := (lem_app_de_resolvent K s hs).2.2.2.2.2.1
  have hRA : Rs K s * (K * Kᵀ + s • (1 : Mat m m)) = 1 := by
    rw [Matrix.mul_add, h6, Matrix.mul_smul, Matrix.mul_one]; simp
  exact ⟨hRA, mul_eq_one_comm.mp hRA⟩

/-- Resolvent difference. -/
private lemma sd_Rs_ident {m n : ℕ} (K1 K3 : Mat m n) {s : ℝ} (hs : 0 < s) :
    Rs K1 s - Rs K3 s = -(Rs K1 s * (K1 - K3) * (K3ᵀ * Rs K3 s)
      + (Rs K1 s * K1) * (K1 - K3)ᵀ * Rs K3 s) := by
  obtain ⟨h1, -⟩ := sd_inv K1 hs
  obtain ⟨-, h3⟩ := sd_inv K3 hs
  have e : Rs K1 s - Rs K3 s
      = Rs K1 s * ((K3 * K3ᵀ + s • (1 : Mat m m)) - (K1 * K1ᵀ + s • (1 : Mat m m))) * Rs K3 s := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc (Rs K1 s) (K3 * K3ᵀ + s • (1 : Mat m m)),
      h3, Matrix.mul_one, h1, Matrix.one_mul]
  rw [e]
  have e2 : (K3 * K3ᵀ + s • (1 : Mat m m)) - (K1 * K1ᵀ + s • (1 : Mat m m))
      = -((K1 - K3) * K3ᵀ + K1 * (K1 - K3)ᵀ) := by
    simp only [Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [e2]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

end SecondAux

section SecondAux2
open Muon.DetEquiv MeasureTheory Matrix

private lemma sd_b_facts {s : ℝ} (hs : 0 < s) :
    0 < (Real.sqrt s)⁻¹ ∧ ((Real.sqrt s)⁻¹) ^ 2 * s = 1 ∧ 1 / s = ((Real.sqrt s)⁻¹) ^ 2 ∧
      1 / (2 * Real.sqrt s) = (Real.sqrt s)⁻¹ / 2 := by
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  refine ⟨inv_pos.mpr hr, ?_, ?_, ?_⟩
  · rw [inv_pow, h2]; field_simp
  · rw [inv_pow, h2]; field_simp
  · field_simp

private lemma sd_op_Rs {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    opNorm (Rs K s) ≤ ((Real.sqrt s)⁻¹) ^ 2 := by
  have := (lem_app_de_resolvent K s hs).1
  rwa [(sd_b_facts hs).2.2.1] at this

private lemma sd_op_Rts {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    opNorm (Rts K s) ≤ ((Real.sqrt s)⁻¹) ^ 2 := by
  have := (lem_app_de_resolvent K s hs).2.1
  rwa [(sd_b_facts hs).2.2.1] at this

private lemma sd_op_Xs {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    opNorm (Xs K s) ≤ (Real.sqrt s)⁻¹ / 2 := by
  have := (lem_app_de_resolvent K s hs).2.2.1
  rwa [(sd_b_facts hs).2.2.2] at this

private lemma sd_Rs_diff_fro {m n : ℕ} (K1 K3 : Mat m n) {s : ℝ} (hs : 0 < s) :
    fro (Rs K1 s - Rs K3 s) ≤ ((Real.sqrt s)⁻¹) ^ 3 * fro (K1 - K3) := by
  obtain ⟨hb, -, -, -⟩ := sd_b_facts hs
  set b := (Real.sqrt s)⁻¹ with hbdef
  rw [sd_Rs_ident K1 K3 hs, sd_fro_neg]
  have t1 : fro (Rs K1 s * (K1 - K3) * (K3ᵀ * Rs K3 s)) ≤ b ^ 2 * fro (K1 - K3) * (b / 2) := by
    refine (sd_fro3_mid _ _ _).trans ?_
    have h1 := sd_op_Rs K1 hs
    have h2 : opNorm (K3ᵀ * Rs K3 s) ≤ b / 2 := by
      rw [← blk_XT1, sd_op_T]; exact sd_op_Xs K3 hs
    have hf := sd_fro_nn (K1 - K3)
    have := fl_opNorm_nonneg (K3ᵀ * Rs K3 s)
    gcongr
  have t2 : fro ((Rs K1 s * K1) * (K1 - K3)ᵀ * Rs K3 s) ≤ (b / 2) * fro (K1 - K3) * b ^ 2 := by
    refine (sd_fro3_mid _ _ _).trans ?_
    have h1 : opNorm (Rs K1 s * K1) ≤ b / 2 := sd_op_Xs K1 hs
    have h2 := sd_op_Rs K3 hs
    have hf := sd_fro_nn (K1 - K3)
    have := fl_opNorm_nonneg (Rs K3 s)
    rw [sd_fro_T]
    gcongr
  have := sd_fro_add (Rs K1 s * (K1 - K3) * (K3ᵀ * Rs K3 s))
    ((Rs K1 s * K1) * (K1 - K3)ᵀ * Rs K3 s)
  nlinarith

private lemma sd_Rts_diff_fro {m n : ℕ} (K1 K3 : Mat m n) {s : ℝ} (hs : 0 < s) :
    fro (Rts K1 s - Rts K3 s) ≤ ((Real.sqrt s)⁻¹) ^ 3 * fro (K1 - K3) := by
  have h := sd_Rs_diff_fro K1ᵀ K3ᵀ hs
  rw [fl_Rts_eq, fl_Rts_eq, ← Matrix.transpose_sub, sd_fro_T] at h
  exact h

private lemma sd_Xs_diff_fro {m n : ℕ} (K1 K3 : Mat m n) {s : ℝ} (hs : 0 < s) :
    fro (Xs K1 s - Xs K3 s) ≤ (5 / 4) * ((Real.sqrt s)⁻¹) ^ 2 * fro (K1 - K3) := by
  obtain ⟨hb, hbs, -, -⟩ := sd_b_facts hs
  set b := (Real.sqrt s)⁻¹ with hbdef
  rw [fl_ident K1 K3 hs]
  have hf := sd_fro_nn (K1 - K3)
  have t1 : fro (s • (Rs K1 s * (K1 - K3) * Rts K3 s)) ≤ s * (b ^ 2 * fro (K1 - K3) * b ^ 2) := by
    rw [fl_fro_smul, abs_of_pos hs]
    refine mul_le_mul_of_nonneg_left ((sd_fro3_mid _ _ _).trans ?_) hs.le
    have h1 := sd_op_Rs K1 hs
    have h2 := sd_op_Rts K3 hs
    have := fl_opNorm_nonneg (Rts K3 s)
    gcongr
  have t2 : fro (Xs K1 s * (K1 - K3)ᵀ * Xs K3 s) ≤ (b / 2) * fro (K1 - K3) * (b / 2) := by
    refine (sd_fro3_mid _ _ _).trans ?_
    have h1 := sd_op_Xs K1 hs
    have h2 := sd_op_Xs K3 hs
    have := fl_opNorm_nonneg (Xs K3 s)
    rw [sd_fro_T]
    gcongr
  have := sd_fro_sub (s • (Rs K1 s * (K1 - K3) * Rts K3 s)) (Xs K1 s * (K1 - K3)ᵀ * Xs K3 s)
  have e : s * (b ^ 2 * fro (K1 - K3) * b ^ 2) = b ^ 2 * fro (K1 - K3) := by
    linear_combination (b ^ 2 * fro (K1 - K3)) * hbs
  nlinarith

end SecondAux2

section SecondAux3
open Muon.DetEquiv MeasureTheory Matrix

private lemma sd_E_alg {m n : ℕ} (s : ℝ) (A1 A3 : Mat m m) (B2 B4 : Mat n n)
    (X1 X2 X3 X4 H : Mat m n) :
    (s • (A1 * H * B2) - X1 * Hᵀ * X2) - (s • (A3 * H * B4) - X3 * Hᵀ * X4)
      = (s • ((A1 - A3) * H * B2) + s • (A3 * H * (B2 - B4)))
        - (((X1 - X3) * Hᵀ * X2) + X3 * Hᵀ * (X2 - X4)) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, smul_sub]
  abel

private lemma sd_E_fro {m n : ℕ} (K1 K2 K3 K4 : Mat m n) {s : ℝ} (hs : 0 < s)
    (hK : K1 - K3 = K2 - K4) (hH : K1 - K2 = K3 - K4) :
    fro ((Xs K1 s - Xs K2 s) - (Xs K3 s - Xs K4 s))
      ≤ (13 / 4) * ((Real.sqrt s)⁻¹) ^ 3 * (fro (K1 - K3) * opNorm (K1 - K2)) := by
  obtain ⟨hb, hbs, -, -⟩ := sd_b_facts hs
  set b := (Real.sqrt s)⁻¹ with hbdef
  set H := K1 - K2 with hHdef
  have hf := sd_fro_nn (K1 - K3)
  have hh := fl_opNorm_nonneg H
  have e : (Xs K1 s - Xs K2 s) - (Xs K3 s - Xs K4 s)
      = (s • ((Rs K1 s - Rs K3 s) * H * Rts K2 s) + s • (Rs K3 s * H * (Rts K2 s - Rts K4 s)))
        - (((Xs K1 s - Xs K3 s) * Hᵀ * Xs K2 s) + Xs K3 s * Hᵀ * (Xs K2 s - Xs K4 s)) := by
    rw [fl_ident K1 K2 hs, fl_ident K3 K4 hs, ← hH]
    exact sd_E_alg s _ _ _ _ _ _ _ _ H
  rw [e]
  have ta : fro (s • ((Rs K1 s - Rs K3 s) * H * Rts K2 s)) ≤ s * ((b ^ 3 * fro (K1 - K3)) * opNorm H * b ^ 2) := by
    rw [fl_fro_smul, abs_of_pos hs]
    refine mul_le_mul_of_nonneg_left ((sd_fro3_left _ _ _).trans ?_) hs.le
    have h1 := sd_Rs_diff_fro K1 K3 hs
    have h2 := sd_op_Rts K2 hs
    have := fl_opNorm_nonneg (Rts K2 s)
    gcongr
  have tb : fro (s • (Rs K3 s * H * (Rts K2 s - Rts K4 s))) ≤ s * (b ^ 2 * opNorm H * (b ^ 3 * fro (K1 - K3))) := by
    rw [fl_fro_smul, abs_of_pos hs]
    refine mul_le_mul_of_nonneg_left ((sd_fro3_right _ _ _).trans ?_) hs.le
    have h1 := sd_op_Rs K3 hs
    have h2 := sd_Rts_diff_fro K2 K4 hs
    rw [← hK] at h2
    have := fl_opNorm_nonneg (Rs K3 s)
    have := sd_fro_nn (Rts K2 s - Rts K4 s)
    gcongr
  have tc : fro ((Xs K1 s - Xs K3 s) * Hᵀ * Xs K2 s) ≤ ((5 / 4 * b ^ 2 * fro (K1 - K3)) * opNorm H * (b / 2)) := by
    refine (sd_fro3_left _ _ _).trans ?_
    have h1 := sd_Xs_diff_fro K1 K3 hs
    have h2 := sd_op_Xs K2 hs
    have := fl_opNorm_nonneg (Xs K2 s)
    rw [sd_op_T]
    gcongr
  have td : fro (Xs K3 s * Hᵀ * (Xs K2 s - Xs K4 s)) ≤ ((b / 2) * opNorm H * (5 / 4 * b ^ 2 * fro (K1 - K3))) := by
    refine (sd_fro3_right _ _ _).trans ?_
    have h1 := sd_op_Xs K3 hs
    have h2 := sd_Xs_diff_fro K2 K4 hs
    rw [← hK] at h2
    have := fl_opNorm_nonneg (Xs K3 s)
    have := sd_fro_nn (Xs K2 s - Xs K4 s)
    rw [sd_op_T]
    gcongr
  have ea : s * ((b ^ 3 * fro (K1 - K3)) * opNorm H * b ^ 2) = b ^ 3 * (fro (K1 - K3) * opNorm H) := by
    linear_combination (b ^ 3 * (fro (K1 - K3) * opNorm H)) * hbs
  have eb : s * (b ^ 2 * opNorm H * (b ^ 3 * fro (K1 - K3))) = b ^ 3 * (fro (K1 - K3) * opNorm H) := by
    linear_combination (b ^ 3 * (fro (K1 - K3) * opNorm H)) * hbs
  have h1 := sd_fro_sub (s • ((Rs K1 s - Rs K3 s) * H * Rts K2 s) + s • (Rs K3 s * H * (Rts K2 s - Rts K4 s)))
    (((Xs K1 s - Xs K3 s) * Hᵀ * Xs K2 s) + Xs K3 s * Hᵀ * (Xs K2 s - Xs K4 s))
  have h2 := sd_fro_add (s • ((Rs K1 s - Rs K3 s) * H * Rts K2 s)) (s • (Rs K3 s * H * (Rts K2 s - Rts K4 s)))
  have h3 := sd_fro_add ((Xs K1 s - Xs K3 s) * Hᵀ * Xs K2 s) (Xs K3 s * Hᵀ * (Xs K2 s - Xs K4 s))
  have hq : b ^ 3 * (fro (K1 - K3) * opNorm H) ≥ 0 := by positivity
  nlinarith

end SecondAux3

section SecondAux4
open Muon.DetEquiv MeasureTheory Matrix

private lemma sd_cs {m n : ℕ} (a b : Mat m n) : ∑ i, ∑ j, a i j * b i j ≤ fro a * fro b := by
  have h1 : ∑ i, ∑ j, a i j * b i j = ∑ x : Fin m × Fin n, a x.1 x.2 * b x.1 x.2 := by
    rw [Fintype.sum_prod_type]
  have h2 : ∑ i, ∑ j, a i j ^ 2 = ∑ x : Fin m × Fin n, a x.1 x.2 ^ 2 := by
    rw [Fintype.sum_prod_type]
  have h3 : ∑ i, ∑ j, b i j ^ 2 = ∑ x : Fin m × Fin n, b x.1 x.2 ^ 2 := by
    rw [Fintype.sum_prod_type]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
    (fun x => a x.1 x.2) (fun x => b x.1 x.2)
  refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ (mul_nonneg (sd_fro_nn a) (sd_fro_nn b)))
  rw [mul_pow, sd_fro_sq, sd_fro_sq, h1, h2, h3]
  exact hcs

private lemma sd_E_eq {m n : ℕ} {ϱ : ℝ} (K1 K2 K3 K4 C : Mat m n) :
    (fun u : ℝ => ∑ i, ∑ j, C i j * ((Xs K1 (ϱ + u ^ 2) - Xs K2 (ϱ + u ^ 2)) -
        (Xs K3 (ϱ + u ^ 2) - Xs K4 (ϱ + u ^ 2))) i j)
      = fun u : ℝ => (∑ i, ∑ j, C i j * (Xs K1 (ϱ + u ^ 2) - Xs K2 (ϱ + u ^ 2)) i j)
        - ∑ i, ∑ j, C i j * (Xs K3 (ϱ + u ^ 2) - Xs K4 (ϱ + u ^ 2)) i j := by
  funext u
  simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma sd_int {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K1 K2 K3 K4 C : Mat m n) :
    IntegrableOn (fun u : ℝ => ∑ i, ∑ j, C i j * ((Xs K1 (ϱ + u ^ 2) - Xs K2 (ϱ + u ^ 2)) -
        (Xs K3 (ϱ + u ^ 2) - Xs K4 (ϱ + u ^ 2))) i j) (Ioi 0) := by
  rw [sd_E_eq (ϱ := ϱ)]
  exact (fl_lin_int hϱ K1 K2 C).sub (fl_lin_int hϱ K3 K4 C)

private lemma sd_pair {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K1 K2 K3 K4 C : Mat m n) :
    ∑ i, ∑ j, C i j * (Q ϱ K1 - Q ϱ K2 - (Q ϱ K3 - Q ϱ K4)) i j
      = (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), ∑ i, ∑ j, C i j * ((Xs K1 (ϱ + u ^ 2) - Xs K2 (ϱ + u ^ 2)) -
        (Xs K3 (ϱ + u ^ 2) - Xs K4 (ϱ + u ^ 2))) i j := by
  have a := fl_lin_eq hϱ K1 K2 C
  have b := fl_lin_eq hϱ K3 K4 C
  have hL : ∑ i, ∑ j, C i j * (Q ϱ K1 - Q ϱ K2 - (Q ϱ K3 - Q ϱ K4)) i j
      = (∑ i, ∑ j, C i j * (Q ϱ K1 - Q ϱ K2) i j) - ∑ i, ∑ j, C i j * (Q ϱ K3 - Q ϱ K4) i j := by
    simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hL, a, b, sd_E_eq (ϱ := ϱ), integral_sub (fl_lin_int hϱ K1 K2 C) (fl_lin_int hϱ K3 K4 C)]
  ring

private lemma sd_mixed_Q {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K1 K2 K3 K4 : Mat m n)
    (hK : K1 - K3 = K2 - K4) (hH : K1 - K2 = K3 - K4) :
    fro (Q ϱ K1 - Q ϱ K2 - (Q ϱ K3 - Q ϱ K4))
      ≤ (13 / 4) * ϱ⁻¹ * (fro (K1 - K3) * opNorm (K1 - K2)) := by
  set W := Q ϱ K1 - Q ϱ K2 - (Q ϱ K3 - Q ϱ K4) with hW
  set P := fro W with hP
  have hP0 : 0 ≤ P := sd_fro_nn W
  set c0 : ℝ := (13 / 4) * (fro (K1 - K3) * opNorm (K1 - K2)) with hc0
  have hc00 : 0 ≤ c0 := by
    have := sd_fro_nn (K1 - K3); have := fl_opNorm_nonneg (K1 - K2); positivity
  obtain ⟨hint, hval⟩ := fl_ioi_integral hϱ
  have hrs : 0 < Real.sqrt ϱ := Real.sqrt_pos.mpr hϱ
  have hpt : ∀ u : ℝ, 0 < u → ∑ i, ∑ j, W i j * ((Xs K1 (ϱ + u ^ 2) - Xs K2 (ϱ + u ^ 2)) -
        (Xs K3 (ϱ + u ^ 2) - Xs K4 (ϱ + u ^ 2))) i j
      ≤ (P * c0 * (Real.sqrt ϱ)⁻¹) * (ϱ + u ^ 2)⁻¹ := by
    intro u hu
    have hs : 0 < ϱ + u ^ 2 := by positivity
    obtain ⟨hb, -, hb2, -⟩ := sd_b_facts hs
    have hE := sd_E_fro K1 K2 K3 K4 hs hK hH
    have hcs := sd_cs W ((Xs K1 (ϱ + u ^ 2) - Xs K2 (ϱ + u ^ 2)) -
        (Xs K3 (ϱ + u ^ 2) - Xs K4 (ϱ + u ^ 2)))
    set b := (Real.sqrt (ϱ + u ^ 2))⁻¹ with hbdef
    have hble : b ≤ (Real.sqrt ϱ)⁻¹ := by
      rw [hbdef]
      exact inv_anti₀ hrs (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u]))
    have hb2' : b ^ 2 = (ϱ + u ^ 2)⁻¹ := by rw [← one_div, hb2]
    have hE2 : fro ((Xs K1 (ϱ + u ^ 2) - Xs K2 (ϱ + u ^ 2)) -
        (Xs K3 (ϱ + u ^ 2) - Xs K4 (ϱ + u ^ 2))) ≤ c0 * ((Real.sqrt ϱ)⁻¹ * (ϱ + u ^ 2)⁻¹) := by
      refine hE.trans ?_
      rw [hc0, ← hb2', show b ^ 3 = b * b ^ 2 by ring]
      have hq := mul_nonneg (sd_fro_nn (K1 - K3)) (fl_opNorm_nonneg (K1 - K2))
      have : 0 ≤ b ^ 2 := by positivity
      calc 13 / 4 * (b * b ^ 2) * (fro (K1 - K3) * opNorm (K1 - K2))
          = (13 / 4 * (fro (K1 - K3) * opNorm (K1 - K2))) * (b * b ^ 2) := by ring
        _ ≤ (13 / 4 * (fro (K1 - K3) * opNorm (K1 - K2))) * ((Real.sqrt ϱ)⁻¹ * b ^ 2) := by gcongr
    calc _ ≤ P * fro ((Xs K1 (ϱ + u ^ 2) - Xs K2 (ϱ + u ^ 2)) -
        (Xs K3 (ϱ + u ^ 2) - Xs K4 (ϱ + u ^ 2))) := hcs
      _ ≤ P * (c0 * ((Real.sqrt ϱ)⁻¹ * (ϱ + u ^ 2)⁻¹)) := mul_le_mul_of_nonneg_left hE2 hP0
      _ = _ := by ring
  have hle : ∫ u in Ioi (0 : ℝ), ∑ i, ∑ j, W i j * ((Xs K1 (ϱ + u ^ 2) - Xs K2 (ϱ + u ^ 2)) -
        (Xs K3 (ϱ + u ^ 2) - Xs K4 (ϱ + u ^ 2))) i j
      ≤ ∫ u in Ioi (0 : ℝ), (P * c0 * (Real.sqrt ϱ)⁻¹) * (ϱ + u ^ 2)⁻¹ :=
    setIntegral_mono_on (sd_int hϱ K1 K2 K3 K4 W) (hint.const_mul _) measurableSet_Ioi
      fun u hu => hpt u hu
  rw [integral_const_mul, hval] at hle
  have hpair := sd_pair hϱ K1 K2 K3 K4 W
  have hsq : ∑ i, ∑ j, W i j * W i j = P ^ 2 := by
    rw [hP, sd_fro_sq]; simp only [sq]
  rw [hsq] at hpair
  have h1 : ϱ ^ (-(1 / 2 : ℝ)) = (Real.sqrt ϱ)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hϱ.le]; norm_num
  have hinv : ϱ⁻¹ = (Real.sqrt ϱ)⁻¹ * (Real.sqrt ϱ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hϱ.le]
  have hpi : 0 < 2 / Real.pi := by positivity
  have hP2 : P ^ 2 ≤ P * (c0 * ϱ⁻¹) := by
    rw [hpair]
    calc (2 / Real.pi) * _ ≤ (2 / Real.pi) * ((P * c0 * (Real.sqrt ϱ)⁻¹) * (Real.pi / 2 * ϱ ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hle hpi.le
      _ = P * (c0 * ϱ⁻¹) := by
          rw [h1, hinv]; field_simp
  have : (13 / 4) * ϱ⁻¹ * (fro (K1 - K3) * opNorm (K1 - K2)) = c0 * ϱ⁻¹ := by rw [hc0]; ring
  rw [this]
  rcases eq_or_lt_of_le hP0 with h0 | hpos
  · rw [← h0]; positivity
  · nlinarith

end SecondAux4

section SecondAux5
open Muon.DetEquiv MeasureTheory Matrix

private lemma sd_hasDeriv {m n : ℕ} {ℓ : ℝ} (hℓpos : 0 < ℓ) (N R : Mat m n) (i : Fin m) (j : Fin n) :
    HasDerivAt (fun t : ℝ => Q ℓ (N + t • R) i j) (dirDeriv ℓ N R i j) 0 := by
  have hΦ := Q_contDiffOn_pos m n
  have hγd : DifferentiableAt ℝ (fun t : ℝ => ((fun a b => N a b + t * R a b), ℓ)) 0 := by
    fun_prop
  have hopen : {p : (Fin m → Fin n → ℝ) × ℝ | 0 < p.2} ∈
      𝓝 ((fun a b => N a b + (0 : ℝ) * R a b), ℓ) :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds (show (0 : ℝ) < ℓ from hℓpos)
  have hG : DifferentiableAt ℝ
      (fun t : ℝ => Q ℓ (Matrix.of fun a b => N a b + t * R a b) i j) 0 := by
    have hcd : ContDiffAt ℝ ∞
        (fun p : (Fin m → Fin n → ℝ) × ℝ => Q p.2 (Matrix.of p.1) i j)
        ((fun a b => N a b + (0 : ℝ) * R a b), ℓ) :=
      contDiffAt_pi.1 (contDiffAt_pi.1 (hΦ.contDiffAt hopen) i) j
    have hdiff : DifferentiableAt ℝ
        ((fun p : (Fin m → Fin n → ℝ) × ℝ => Q p.2 (Matrix.of p.1) i j) ∘
          (fun t : ℝ => ((fun a b => N a b + t * R a b), ℓ))) 0 :=
      DifferentiableAt.comp (0 : ℝ) (hcd.differentiableAt (by norm_num)) hγd
    exact hdiff
  have hf : (fun t : ℝ => Q ℓ (N + t • R) i j)
      = (fun t : ℝ => Q ℓ (Matrix.of fun a b => N a b + t * R a b) i j) := by
    funext t
    congr 2
  have h := hG.hasDerivAt
  have hd : dirDeriv ℓ N R i j
      = deriv (fun t : ℝ => Q ℓ (Matrix.of fun a b => N a b + t * R a b) i j) 0 := by
    unfold dirDeriv
    simp only [Matrix.of_apply]
    rw [hf]
  rw [hd, hf]
  exact h

private lemma sd_slope {m n : ℕ} {ℓ : ℝ} (hℓpos : 0 < ℓ) (N R : Mat m n) (i : Fin m) (j : Fin n) :
    Tendsto (fun t : ℝ => (Q ℓ (N + t • R) i j - Q ℓ N i j) / t)
      (𝓝[≠] 0) (𝓝 (dirDeriv ℓ N R i j)) := by
  have h := hasDerivAt_iff_tendsto_slope.mp (sd_hasDeriv hℓpos N R i j)
  refine Tendsto.congr' ?_ h
  filter_upwards with t
  simp [slope_def_field]

private lemma sd_fro_of_quot {m n : ℕ} {F : ℝ → Mat m n} {D : Mat m n} {L : ℝ}
    (hlim : ∀ i j, Tendsto (fun t : ℝ => F t i j / t) (𝓝[≠] 0) (𝓝 (D i j)))
    (hb : ∀ t : ℝ, t ≠ 0 → fro (F t) ≤ L * |t|) : fro D ≤ L := by
  have hL : 0 ≤ L := by
    have := hb 1 one_ne_zero
    have h2 := sd_fro_nn (F 1)
    simp only [abs_one, mul_one] at this
    linarith
  have hsum : Tendsto (fun t : ℝ => ∑ i, ∑ j, (F t i j / t) ^ 2)
      (𝓝[≠] 0) (𝓝 (∑ i, ∑ j, (D i j) ^ 2)) :=
    tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => (hlim i j).pow 2
  have hbound : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∑ i, ∑ j, (F t i j / t) ^ 2 ≤ L ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    have ht2 : 0 < t ^ 2 := by positivity
    have h2 : fro (F t) ^ 2 ≤ (L * |t|) ^ 2 :=
      pow_le_pow_left₀ (sd_fro_nn _) (hb t ht0) 2
    rw [mul_pow, sq_abs, sd_fro_sq] at h2
    have hsq : ∑ i, ∑ j, (F t i j / t) ^ 2 = (∑ i, ∑ j, F t i j ^ 2) / t ^ 2 := by
      simp only [div_pow, Finset.sum_div]
    rw [hsq, div_le_iff₀ ht2]
    linarith
  have hle : ∑ i, ∑ j, (D i j) ^ 2 ≤ L ^ 2 := le_of_tendsto hsum hbound
  rw [← sd_fro_sq] at hle
  exact (pow_le_pow_iff_left₀ (sd_fro_nn _) hL two_ne_zero).mp hle

private lemma sd_dd_diff {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (N N' R : Mat m n) :
    fro (dirDeriv ℓ N R - dirDeriv ℓ N' R)
      ≤ ((13 / 4) * ℓ⁻¹ * (fro R * opNorm (N - N'))) := by
  refine sd_fro_of_quot (F := fun t : ℝ => Q ℓ (N + t • R) - Q ℓ (N' + t • R) - (Q ℓ N - Q ℓ N')) ?_ ?_
  · intro i j
    have h := (sd_slope hℓ N R i j).sub (sd_slope hℓ N' R i j)
    refine Tendsto.congr' ?_ (by simpa [Matrix.sub_apply] using h)
    filter_upwards with t
    simp only [Matrix.sub_apply]
    ring
  · intro t ht
    have h := sd_mixed_Q hℓ (N + t • R) (N' + t • R) N N' (by abel) (by abel)
    have e1 : N + t • R - N = t • R := by abel
    have e2 : N + t • R - (N' + t • R) = N - N' := by abel
    rw [e1, e2, fl_fro_smul] at h
    refine h.trans (le_of_eq ?_)
    ring

end SecondAux5

section SecondAux6
open Muon.DetEquiv MeasureTheory Matrix

open scoped Matrix.Norms.L2Operator in
private lemma sd_op_smul {m n : ℕ} (t : ℝ) (R : Mat m n) : opNorm (t • R) = |t| * opNorm R := by
  rw [opNorm_eq_norm, opNorm_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma sd_abs_cs {m n : ℕ} (a b : Mat m n) :
    |∑ i, ∑ j, a i j * b i j| ≤ fro a * fro b := by
  have h1 := sd_cs a b
  have h2 := sd_cs a (-b)
  rw [sd_fro_neg] at h2
  simp only [Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib] at h2
  exact abs_le.2 ⟨by linarith, h1⟩

private lemma sd_hasDeriv_line {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (N R : Mat m n) (τ : ℝ)
    (i : Fin m) (j : Fin n) :
    HasDerivAt (fun x : ℝ => Q ℓ (N + x • R) i j) (dirDeriv ℓ (N + τ • R) R i j) τ := by
  have h := sd_hasDeriv hℓ (N + τ • R) R i j
  have h2 := HasDerivAt.comp_sub_const τ τ (by rw [sub_self]; exact h)
  convert h2 using 2
  rename_i x
  have : N + τ • R + (x - τ) • R = N + x • R := by rw [sub_smul]; abel
  rw [this]

private lemma sd_second_core {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (N R : Mat m n) :
    fro (Q ℓ (N + R) - Q ℓ N - dirDeriv ℓ N R) ≤ (13 / 4) * ℓ⁻¹ * (fro R * opNorm R) := by
  set Z := Q ℓ (N + R) - Q ℓ N - dirDeriv ℓ N R with hZ
  set B := (13 / 4) * ℓ⁻¹ * (fro R * opNorm R) with hB
  have hB0 : 0 ≤ B := by
    have := sd_fro_nn R; have := fl_opNorm_nonneg R; positivity
  set ψ : ℝ → ℝ := fun τ => ∑ i, ∑ j, Z i j * (Q ℓ (N + τ • R) i j - Q ℓ N i j - τ * dirDeriv ℓ N R i j)
    with hψ
  have hder : ∀ τ : ℝ, HasDerivAt ψ
      (∑ i, ∑ j, Z i j * (dirDeriv ℓ (N + τ • R) R i j - dirDeriv ℓ N R i j)) τ := by
    intro τ
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
    have h1 := sd_hasDeriv_line hℓ N R τ i j
    have h2 : HasDerivAt (fun x : ℝ => x * dirDeriv ℓ N R i j) (dirDeriv ℓ N R i j) τ := by
      simpa using (hasDerivAt_id τ).mul_const (dirDeriv ℓ N R i j)
    have h3 := ((h1.sub_const (Q ℓ N i j)).sub h2).const_mul (Z i j)
    convert h3 using 1
  have hbd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖∑ i, ∑ j, Z i j * (dirDeriv ℓ (N + τ • R) R i j - dirDeriv ℓ N R i j)‖ ≤ fro Z * B := by
    intro τ hτ
    rw [Real.norm_eq_abs]
    have hcs := sd_abs_cs Z (dirDeriv ℓ (N + τ • R) R - dirDeriv ℓ N R)
    simp only [Matrix.sub_apply] at hcs
    refine hcs.trans (mul_le_mul_of_nonneg_left ?_ (sd_fro_nn Z))
    have hd := sd_dd_diff hℓ (N + τ • R) N R
    rw [show N + τ • R - N = τ • R by abel, sd_op_smul, abs_of_nonneg hτ.1] at hd
    refine hd.trans ?_
    rw [hB]
    have := sd_fro_nn R; have := fl_opNorm_nonneg R
    have hτ1 := hτ.2
    have : τ * opNorm R ≤ opNorm R := by nlinarith
    have hh : 0 ≤ (13 / 4) * ℓ⁻¹ * fro R := by positivity
    calc 13 / 4 * ℓ⁻¹ * (fro R * (τ * opNorm R)) = ((13 / 4) * ℓ⁻¹ * fro R) * (τ * opNorm R) := by ring
      _ ≤ ((13 / 4) * ℓ⁻¹ * fro R) * opNorm R := mul_le_mul_of_nonneg_left this hh
      _ = _ := by ring
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (f := ψ)
    (f' := fun τ => ∑ i, ∑ j, Z i j * (dirDeriv ℓ (N + τ • R) R i j - dirDeriv ℓ N R i j))
    (s := Set.Icc (0 : ℝ) 1) (C := fro Z * B) (fun τ _ => (hder τ).hasDerivWithinAt) hbd
    (convex_Icc 0 1) (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  have h0 : ψ 0 = 0 := by simp [hψ]
  have h1 : ψ 1 = fro Z ^ 2 := by
    rw [sd_fro_sq]
    simp only [hψ, one_smul, one_mul, sq]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hZ]
    simp only [Matrix.sub_apply]
  rw [h0, h1, sub_zero, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hmvt
  rw [sub_zero, norm_one, mul_one] at hmvt
  have hZ0 := sd_fro_nn Z
  rcases eq_or_lt_of_le hZ0 with h | h
  · rw [← h]; exact hB0
  · nlinarith

/-- Core of (iii). -/
private lemma sd_core_iii {ℓlo : ℝ} (hlo : 0 < ℓlo) {m n : ℕ} {ℓ : ℝ} (hℓ : ℓlo ≤ ℓ)
    (N N' R : Mat m n) :
    fro (dirDeriv ℓ N R - dirDeriv ℓ N' R) ≤ (13 / (4 * ℓlo)) * opNorm (N - N') * fro R := by
  have hℓpos : 0 < ℓ := lt_of_lt_of_le hlo hℓ
  refine (sd_dd_diff hℓpos N N' R).trans ?_
  have hinv : ℓ⁻¹ ≤ ℓlo⁻¹ := inv_anti₀ hlo hℓ
  have := sd_fro_nn R; have := fl_opNorm_nonneg (N - N')
  calc (13 / 4) * ℓ⁻¹ * (fro R * opNorm (N - N')) ≤ (13 / 4) * ℓlo⁻¹ * (fro R * opNorm (N - N')) := by gcongr
    _ = _ := by field_simp

end SecondAux6

/-- `lem:app-dyn-second`, part (ii). Snapshot `cr-2026-10-23`. Statement, verbatim from
`section.tex` (full environment shown; this declaration is part (ii)):

    \begin{lemma}[Second-order filter estimates]\label{lem:app-dyn-second}
    Let $0<\ell_-\le\ell_+<\infty$. There is $C$, depending only on
    $(\ell_-,\ell_+)$, such that for $\ell\in[\ell_-,\ell_+]$ and all
    $N,N',R\in\R^{\Nout\times\Nin}$, with $D\Qridge\ell(N)[R]$ the derivative of
    $\Qridge\ell$ at $N$ in the direction $R$:
    \begin{enumerate}[label=(\roman*)]
    \item $\norm{D\Qridge\ell(N)[R]}_\F\le\ell^{-1/2}\norm R_\F$;
    \item $\norm{\Qridge\ell(N+R)-\Qridge\ell(N)-D\Qridge\ell(N)[R]}_\F\le C\norm R\norm R_\F$;
    \item $\norm{D\Qridge\ell(N)[R]-D\Qridge\ell(N')[R]}_\F\le C\norm{N-N'}\norm R_\F$;
    \item $\norm{\partial_\ell\Qridge\ell(N)}\le C$,
    $\norm{\partial_\ell\Qridge\ell(N)}_\F+\norm{\partial_\ell^2\Qridge\ell(N)}_\F\le C\sqrt{\min(\Nout,\Nin)}$,
    and $\norm{\partial_\ell\Qridge\ell(N)-\partial_\ell\Qridge\ell(N')}_\F\le C\norm{N-N'}_\F$.
    \end{enumerate}
    \end{lemma}
-/
theorem lem_app_dyn_second_ii {ℓlo ℓhi : ℝ} (hlo : 0 < ℓlo) (hle : ℓlo ≤ ℓhi) :
    ∃ C : ℝ, ∀ {m n : ℕ} (ℓ : ℝ), ℓ ∈ Icc ℓlo ℓhi → ∀ N R : Mat m n,
      fro (Q ℓ (N + R) - Q ℓ N - dirDeriv ℓ N R) ≤ C * opNorm R * fro R := by
  refine ⟨13 / (4 * ℓlo), fun {m n} ℓ hℓ N R => ?_⟩
  have hℓpos : 0 < ℓ := lt_of_lt_of_le hlo hℓ.1
  refine (sd_second_core hℓpos N R).trans ?_
  have hinv : ℓ⁻¹ ≤ ℓlo⁻¹ := inv_anti₀ hlo hℓ.1
  have := sd_fro_nn R; have := fl_opNorm_nonneg R
  calc (13 / 4) * ℓ⁻¹ * (fro R * opNorm R) ≤ (13 / 4) * ℓlo⁻¹ * (fro R * opNorm R) := by gcongr
    _ = _ := by field_simp

/-- `lem:app-dyn-second`, part (iii). Snapshot `cr-2026-10-23`. Statement, verbatim from
`section.tex` (full environment shown; this declaration is part (iii)):

    \begin{lemma}[Second-order filter estimates]\label{lem:app-dyn-second}
    Let $0<\ell_-\le\ell_+<\infty$. There is $C$, depending only on
    $(\ell_-,\ell_+)$, such that for $\ell\in[\ell_-,\ell_+]$ and all
    $N,N',R\in\R^{\Nout\times\Nin}$, with $D\Qridge\ell(N)[R]$ the derivative of
    $\Qridge\ell$ at $N$ in the direction $R$:
    \begin{enumerate}[label=(\roman*)]
    \item $\norm{D\Qridge\ell(N)[R]}_\F\le\ell^{-1/2}\norm R_\F$;
    \item $\norm{\Qridge\ell(N+R)-\Qridge\ell(N)-D\Qridge\ell(N)[R]}_\F\le C\norm R\norm R_\F$;
    \item $\norm{D\Qridge\ell(N)[R]-D\Qridge\ell(N')[R]}_\F\le C\norm{N-N'}\norm R_\F$;
    \item $\norm{\partial_\ell\Qridge\ell(N)}\le C$,
    $\norm{\partial_\ell\Qridge\ell(N)}_\F+\norm{\partial_\ell^2\Qridge\ell(N)}_\F\le C\sqrt{\min(\Nout,\Nin)}$,
    and $\norm{\partial_\ell\Qridge\ell(N)-\partial_\ell\Qridge\ell(N')}_\F\le C\norm{N-N'}_\F$.
    \end{enumerate}
    \end{lemma}
-/
theorem lem_app_dyn_second_iii {ℓlo ℓhi : ℝ} (hlo : 0 < ℓlo) (hle : ℓlo ≤ ℓhi) :
    ∃ C : ℝ, ∀ {m n : ℕ} (ℓ : ℝ), ℓ ∈ Icc ℓlo ℓhi → ∀ N N' R : Mat m n,
      fro (dirDeriv ℓ N R - dirDeriv ℓ N' R) ≤ C * opNorm (N - N') * fro R := by
  exact ⟨13 / (4 * ℓlo), fun {m n} ℓ hℓ N N' R => sd_core_iii hlo hℓ.1 N N' R⟩

section SecondIV
open Muon.Volatility

private lemma p5_sq_pos {x ℓ : ℝ} (hℓ : 0 < ℓ) : 0 < x ^ 2 + ℓ := by nlinarith [sq_nonneg x]

private lemma p5_s_pos {x ℓ : ℝ} (hℓ : 0 < ℓ) : 0 < Real.sqrt (x ^ 2 + ℓ) :=
  Real.sqrt_pos.mpr (p5_sq_pos hℓ)

private lemma p5_s_ge {x ℓ : ℝ} : Real.sqrt ℓ ≤ Real.sqrt (x ^ 2 + ℓ) :=
  Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])

private lemma p5_s_sq {x ℓ : ℝ} (hℓ : 0 < ℓ) : Real.sqrt (x ^ 2 + ℓ) ^ 2 = x ^ 2 + ℓ :=
  Real.sq_sqrt (p5_sq_pos hℓ).le

/-- derivative in ℓ -/
private lemma p5_hasDeriv_l (c : ℝ) (k : ℕ) (x : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    HasDerivAt (fun l : ℝ => c * x / Real.sqrt (x ^ 2 + l) ^ k)
      (-(c * k) * x / 2 / Real.sqrt (x ^ 2 + ℓ) ^ (k + 2)) ℓ := by
  have hP := p5_sq_pos (x := x) hℓ
  have hs := p5_s_pos (x := x) hℓ
  have h1 : HasDerivAt (fun l : ℝ => x ^ 2 + l) 1 ℓ := by
    simpa using (hasDerivAt_id ℓ).const_add (x ^ 2)
  have h2 := h1.sqrt hP.ne'
  have h3 := h2.pow k
  have h4 := (hasDerivAt_const ℓ (c * x)).div h3 (pow_ne_zero k hs.ne')
  refine h4.congr_deriv ?_
  rcases k with _ | j
  · simp
  · simp only [Pi.pow_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
    ring



private lemma p5_pow_ge {x ℓ : ℝ} (n : ℕ) :
    Real.sqrt ℓ ^ n ≤ Real.sqrt (x ^ 2 + ℓ) ^ n :=
  pow_le_pow_left₀ (Real.sqrt_nonneg _) p5_s_ge n

private lemma p5_r_pos {ℓ : ℝ} (hℓ : 0 < ℓ) : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ

/-- derivative in x -/
private lemma p5_hasDeriv_x (c : ℝ) (j : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => c * y / Real.sqrt (y ^ 2 + ℓ) ^ (j + 1))
      (c * (x ^ 2 + ℓ - (j + 1) * x ^ 2) / Real.sqrt (x ^ 2 + ℓ) ^ (j + 1 + 2)) x := by
  have hP := p5_sq_pos (x := x) hℓ
  have hs := p5_s_pos (x := x) hℓ
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + ℓ) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const ℓ
  have h2 := h1.sqrt hP.ne'
  have h3 := h2.pow (j + 1)
  have h4 := ((hasDerivAt_id x).const_mul c).div h3 (pow_ne_zero _ hs.ne')
  refine h4.congr_deriv ?_
  have hsq := p5_s_sq (x := x) hℓ
  simp only [Pi.pow_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, id]
  field_simp
  generalize Real.sqrt (x ^ 2 + ℓ) = s at hsq hs ⊢
  have hl : ℓ = s ^ 2 - x ^ 2 := by linarith
  subst hl
  ring



private lemma p5_abs_le_s (x ℓ : ℝ) (hℓ : 0 < ℓ) : |x| ≤ Real.sqrt (x ^ 2 + ℓ) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

/-- reduce `|E| / s^(q+m)` -/
private lemma p5_red {E K s r : ℝ} {m q : ℕ} (hr : 0 < r) (hrs : r ≤ s) (hK : 0 ≤ K)
    (hE : |E| ≤ K * s ^ m) :
    |E / s ^ (m + q)| ≤ K / r ^ q := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  rw [abs_div, abs_of_pos (pow_pos hs _), div_le_iff₀ (pow_pos hs _)]
  calc |E| ≤ K * s ^ m := hE
    _ = K / s ^ q * s ^ (m + q) := by rw [pow_add]; field_simp
    _ ≤ K / r ^ q * s ^ (m + q) := by
        gcongr

private lemma p5_bound (c : ℝ) (j : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    |c * x / Real.sqrt (x ^ 2 + ℓ) ^ (j + 1)| ≤ |c| / Real.sqrt ℓ ^ j := by
  have h := p5_red (E := c * x) (K := |c|) (s := Real.sqrt (x ^ 2 + ℓ)) (r := Real.sqrt ℓ) (m := 1) (q := j)
    (p5_r_pos hℓ) p5_s_ge (abs_nonneg _) (by
      rw [abs_mul, pow_one]; exact mul_le_mul_of_nonneg_left (p5_abs_le_s x ℓ hℓ) (abs_nonneg _))
  rw [add_comm 1 j] at h
  exact h

private lemma p5_dx_bound (c : ℝ) (j : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    |c * (x ^ 2 + ℓ - (j + 1) * x ^ 2) / Real.sqrt (x ^ 2 + ℓ) ^ (j + 1 + 2)| ≤
      |c| * (j + 1) / Real.sqrt ℓ ^ (j + 1) := by
  have hsq := p5_s_sq (x := x) hℓ
  have h := p5_red (E := c * (x ^ 2 + ℓ - (j + 1) * x ^ 2)) (K := |c| * (j + 1))
    (s := Real.sqrt (x ^ 2 + ℓ)) (r := Real.sqrt ℓ) (m := 2) (q := j + 1)
    (p5_r_pos hℓ) p5_s_ge (by positivity) (by
      rw [abs_mul, hsq, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [abs_le]
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      constructor <;> nlinarith [sq_nonneg x])
  rw [show 2 + (j + 1) = j + 1 + 2 by ring] at h
  exact h

private lemma p5_dl_bound (c : ℝ) (j : ℕ) {a ℓ : ℝ} (ha : 0 < a) (hal : a ≤ ℓ) (x : ℝ) :
    |-(c * ((j + 1 : ℕ) : ℝ)) * x / 2 / Real.sqrt (x ^ 2 + ℓ) ^ (j + 1 + 2)| ≤
      |c| * (j + 1) / 2 / Real.sqrt a ^ (j + 2) := by
  have hℓ : 0 < ℓ := lt_of_lt_of_le ha hal
  have h := p5_red (E := -(c * ((j + 1 : ℕ) : ℝ)) * x / 2) (K := |c| * (j + 1) / 2)
    (s := Real.sqrt (x ^ 2 + ℓ)) (r := Real.sqrt a) (m := 1) (q := j + 2)
    (p5_r_pos ha) ((Real.sqrt_le_sqrt hal).trans p5_s_ge) (by positivity) (by
      rw [pow_one]
      have h1 := p5_abs_le_s x ℓ hℓ
      have : |-(c * ((j + 1 : ℕ) : ℝ)) * x / 2| = |c| * (j + 1) / 2 * |x| := by
        rw [abs_div, abs_mul, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((j + 1 : ℕ) : ℝ)),
          abs_two]
        push_cast; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left h1 (by positivity))
  rw [show 1 + (j + 2) = j + 1 + 2 by ring] at h
  exact h

private lemma p5_lip_x (c : ℝ) (j : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (x y : ℝ) :
    |c * x / Real.sqrt (x ^ 2 + ℓ) ^ (j + 1) - c * y / Real.sqrt (y ^ 2 + ℓ) ^ (j + 1)| ≤
      (|c| * (j + 1) / Real.sqrt ℓ ^ (j + 1)) * |x - y| := by
  have hd : ∀ z ∈ (Set.univ : Set ℝ), HasDerivWithinAt (fun y : ℝ => c * y / Real.sqrt (y ^ 2 + ℓ) ^ (j + 1))
      (c * (z ^ 2 + ℓ - (j + 1) * z ^ 2) / Real.sqrt (z ^ 2 + ℓ) ^ (j + 1 + 2)) Set.univ z :=
    fun z _ => (p5_hasDeriv_x c j hℓ z).hasDerivWithinAt
  have hb : ∀ z ∈ (Set.univ : Set ℝ), ‖c * (z ^ 2 + ℓ - (j + 1) * z ^ 2) / Real.sqrt (z ^ 2 + ℓ) ^ (j + 1 + 2)‖ ≤
      |c| * (j + 1) / Real.sqrt ℓ ^ (j + 1) :=
    fun z _ => by rw [Real.norm_eq_abs]; exact p5_dx_bound c j hℓ z
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  exact this

private lemma p5_iob (c : ℝ) (j : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsOddBddLip (fun x : ℝ => c * x / Real.sqrt (x ^ 2 + ℓ) ^ (j + 1)) := by
  refine ⟨fun x => ?_, ⟨|c| / Real.sqrt ℓ ^ j, p5_bound c j hℓ⟩,
    ⟨|c| * (j + 1) / Real.sqrt ℓ ^ (j + 1), p5_lip_x c j hℓ⟩⟩
  simp only [neg_sq, mul_neg, neg_div]

private lemma p5_lip_l (c : ℝ) (j : ℕ) {a : ℝ} (ha : 0 < a) (x l1 l2 : ℝ) (h1 : a ≤ l1) (h2 : a ≤ l2) :
    |c * x / Real.sqrt (x ^ 2 + l1) ^ (j + 1) - c * x / Real.sqrt (x ^ 2 + l2) ^ (j + 1)| ≤
      (|c| * (j + 1) / 2 / Real.sqrt a ^ (j + 2)) * |l1 - l2| := by
  have hd : ∀ z ∈ Set.Ici a, HasDerivWithinAt (fun l : ℝ => c * x / Real.sqrt (x ^ 2 + l) ^ (j + 1))
      (-(c * ((j + 1 : ℕ) : ℝ)) * x / 2 / Real.sqrt (x ^ 2 + z) ^ (j + 1 + 2)) (Set.Ici a) z :=
    fun z hz => (p5_hasDeriv_l c (j + 1) x (lt_of_lt_of_le ha hz)).hasDerivWithinAt
  have hb : ∀ z ∈ Set.Ici a, ‖-(c * ((j + 1 : ℕ) : ℝ)) * x / 2 / Real.sqrt (x ^ 2 + z) ^ (j + 1 + 2)‖ ≤
      |c| * (j + 1) / 2 / Real.sqrt a ^ (j + 2) :=
    fun z hz => by rw [Real.norm_eq_abs]; exact p5_dl_bound c j ha hz x
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Ici a)
    (Set.mem_Ici.mpr h2) (Set.mem_Ici.mpr h1)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  exact this



private lemma p5_cont (f : ℝ → ℝ) (hf : IsOddBddLip f) : Continuous f := by
  obtain ⟨_, _, ⟨L, hL⟩⟩ := hf
  have hLW : LipschitzWith (Real.toNNReal L) f := by
    refine LipschitzWith.of_dist_le' (fun x y => ?_)
    simp only [Real.dist_eq]
    exact (hL x y).trans (mul_le_mul_of_nonneg_right le_rfl (abs_nonneg _))
  exact hLW.continuous

private lemma p5_iob_sub (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) :
    IsOddBddLip (fun x => f x - g x) := by
  obtain ⟨hfo, ⟨M1, hM1⟩, ⟨L1, hL1⟩⟩ := hf
  obtain ⟨hgo, ⟨M2, hM2⟩, ⟨L2, hL2⟩⟩ := hg
  refine ⟨fun x => ?_, ⟨M1 + M2, fun x => ?_⟩, ⟨L1 + L2, fun x y => ?_⟩⟩
  · change f (-x) - g (-x) = -(f x - g x)
    rw [hfo x, hgo x]; ring
  · have h1 := abs_le.mp (hM1 x)
    have h2 := abs_le.mp (hM2 x)
    change |f x - g x| ≤ M1 + M2
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · have h1 := abs_le.mp (hL1 x y)
    have h2 := abs_le.mp (hL2 x y)
    have e : (L1 + L2) * |x - y| = L1 * |x - y| + L2 * |x - y| := by ring
    change |(f x - g x) - (f y - g y)| ≤ (L1 + L2) * |x - y|
    rw [e, abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

private lemma p5_iob_smul (a : ℝ) (f : ℝ → ℝ) (hf : IsOddBddLip f) :
    IsOddBddLip (fun x => a * f x) := by
  obtain ⟨hfo, ⟨M1, hM1⟩, ⟨L1, hL1⟩⟩ := hf
  refine ⟨fun x => ?_, ⟨|a| * M1, fun x => ?_⟩, ⟨|a| * L1, fun x y => ?_⟩⟩
  · change a * f (-x) = -(a * f x)
    rw [hfo x]; ring
  · change |a * f x| ≤ |a| * M1
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM1 x) (abs_nonneg _)
  · change |a * f x - a * f y| ≤ |a| * L1 * |x - y|
    rw [← mul_sub, abs_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hL1 x y) (abs_nonneg _)

private lemma p5_ur_sub {m n : ℕ} (X Y : Mat (m + n) (m + n)) :
    Muon.Foundations.upperRight (X - Y) = Muon.Foundations.upperRight X - Muon.Foundations.upperRight Y := by
  ext i j; simp [Muon.Foundations.upperRight]

private lemma p5_ur_smul {m n : ℕ} (a : ℝ) (X : Mat (m + n) (m + n)) :
    Muon.Foundations.upperRight (a • X) = a • Muon.Foundations.upperRight X := by
  ext i j; simp [Muon.Foundations.upperRight]

private lemma p5_sharp_sub {m n : ℕ} (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g)
    (K : Mat m n) : oddSharp (fun x => f x - g x) K = oddSharp f K - oddSharp g K := by
  unfold oddSharp
  rw [cfc_sub f g (Muon.Foundations.hermDilation K) (p5_cont f hf).continuousOn
    (p5_cont g hg).continuousOn, p5_ur_sub]

private lemma p5_sharp_smul {m n : ℕ} (a : ℝ) (f : ℝ → ℝ) (hf : IsOddBddLip f) (K : Mat m n) :
    oddSharp (fun x => a * f x) K = a • oddSharp f K := by
  unfold oddSharp
  rw [cfc_const_mul a f (Muon.Foundations.hermDilation K) (p5_cont f hf).continuousOn, p5_ur_smul]

private lemma p5_supNorm_le (f : ℝ → ℝ) {M : ℝ} (_hM : 0 ≤ M) (h : ∀ x, |f x| ≤ M) : supNorm f ≤ M :=
  ciSup_le h

private lemma p5_lipConst_le (f : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) (h : ∀ x y, |f x - f y| ≤ L * |x - y|) :
    lipConst f ≤ L := by
  refine ciSup_le (fun p => ?_)
  by_cases hp : p.1 = p.2
  · simp only [hp, ite_true]; exact hL
  · simp only [hp, ite_false]
    have hpos : 0 < |p.1 - p.2| := abs_pos.mpr (sub_ne_zero.mpr hp)
    rw [div_le_iff₀ hpos]
    exact h p.1 p.2

private lemma p5_entry_le {m n : ℕ} (A : Mat m n) (i : Fin m) (j : Fin n) : |A i j| ≤ fro A := by
  have h : A i j ^ 2 ≤ fro A ^ 2 := by
    rw [show fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 by
      unfold fro
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
      simp [Real.norm_eq_abs, sq_abs]]
    calc A i j ^ 2 ≤ ∑ j', A i j' ^ 2 :=
          Finset.single_le_sum (f := fun j' => A i j' ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', A i' j' ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', A i' j' ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact abs_le_of_sq_le_sq h (Real.sqrt_nonneg _)



private lemma p5_taylor (g g' : ℝ → ℝ → ℝ) {ℓ0 : ℝ} (hℓ0 : 0 < ℓ0)
    (hder : ∀ ℓ, 0 < ℓ → ∀ x, HasDerivAt (fun l => g l x) (g' ℓ x) ℓ)
    {B : ℝ} (hB : 0 ≤ B) (hlip : ∀ ℓ, ℓ0 / 2 ≤ ℓ → ∀ x, |g' ℓ x - g' ℓ0 x| ≤ B * |ℓ - ℓ0|)
    {h : ℝ} (hh : |h| < ℓ0 / 2) (x : ℝ) :
    |(g (ℓ0 + h) x - g ℓ0 x) - h * g' ℓ0 x| ≤ B * h ^ 2 := by
  have hd : ∀ t ∈ Metric.closedBall (0 : ℝ) |h|, HasDerivWithinAt
      (fun t : ℝ => g (ℓ0 + t) x - t * g' ℓ0 x) (g' (ℓ0 + t) x - g' ℓ0 x)
      (Metric.closedBall (0 : ℝ) |h|) t := by
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
    have htl : |t| < ℓ0 / 2 := lt_of_le_of_lt ht hh
    have hpos : 0 < ℓ0 + t := by have := (abs_lt.mp htl).1; linarith
    have h1 : HasDerivAt (fun t : ℝ => g (ℓ0 + t) x) (g' (ℓ0 + t) x) t := by
      exact HasDerivAt.comp_const_add ℓ0 t (hder (ℓ0 + t) hpos x)
    have h2 : HasDerivAt (fun t : ℝ => t * g' ℓ0 x) (g' ℓ0 x) t := by
      simpa using (hasDerivAt_id t).mul_const (g' ℓ0 x)
    exact (h1.sub h2).hasDerivWithinAt
  have hb : ∀ t ∈ Metric.closedBall (0 : ℝ) |h|, ‖g' (ℓ0 + t) x - g' ℓ0 x‖ ≤ B * |h| := by
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
    have htl : |t| < ℓ0 / 2 := lt_of_le_of_lt ht hh
    have := (abs_lt.mp htl).1
    rw [Real.norm_eq_abs]
    refine (hlip (ℓ0 + t) (by linarith) x).trans ?_
    rw [show ℓ0 + t - ℓ0 = t by ring]
    exact mul_le_mul_of_nonneg_left ht hB
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_closedBall (0 : ℝ) |h|)
    (Metric.mem_closedBall_self (abs_nonneg h))
    (by rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] : h ∈ Metric.closedBall (0 : ℝ) |h|)
  simp only [add_zero, zero_mul, sub_zero, Real.norm_eq_abs] at this
  have e : g (ℓ0 + h) x - h * g' ℓ0 x - g ℓ0 x = (g (ℓ0 + h) x - g ℓ0 x) - h * g' ℓ0 x := by ring
  rw [e] at this
  calc _ ≤ B * |h| * |h| := this
    _ = B * h ^ 2 := by rw [mul_assoc, ← sq, sq_abs]



private lemma p5_gen {m n : ℕ} (g g' : ℝ → ℝ → ℝ) (N : Mat m n) (i : Fin m) (j : Fin n) {ℓ0 : ℝ}
    (hℓ0 : 0 < ℓ0)
    (hder : ∀ ℓ, 0 < ℓ → ∀ x, HasDerivAt (fun l => g l x) (g' ℓ x) ℓ)
    (hg : ∀ ℓ, 0 < ℓ → IsOddBddLip (g ℓ)) (hg' : ∀ ℓ, 0 < ℓ → IsOddBddLip (g' ℓ))
    {B : ℝ} (hB : 0 ≤ B) (hlip : ∀ ℓ, ℓ0 / 2 ≤ ℓ → ∀ x, |g' ℓ x - g' ℓ0 x| ≤ B * |ℓ - ℓ0|) :
    HasDerivAt (fun l => oddSharp (g l) N i j) (oddSharp (g' ℓ0) N i j) ℓ0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hbig : (fun h : ℝ => oddSharp (g (ℓ0 + h)) N i j - oddSharp (g ℓ0) N i j - h • oddSharp (g' ℓ0) N i j)
      =O[𝓝 0] (fun h : ℝ => h ^ 2) := by
    refine Asymptotics.IsBigO.of_bound (Real.sqrt ((min m n : ℕ) : ℝ) * B) ?_
    have hev : ∀ᶠ h : ℝ in 𝓝 0, |h| < ℓ0 / 2 := by
      have : Metric.ball (0 : ℝ) (ℓ0 / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by linarith)
      filter_upwards [this] with h hh
      simpa [Real.dist_eq] using hh
    filter_upwards [hev] with h hh
    have hpos : 0 < ℓ0 + h := by have := (abs_lt.mp hh).1; linarith
    have hiob : IsOddBddLip (fun x => (g (ℓ0 + h) x - g ℓ0 x) - h * g' ℓ0 x) :=
      p5_iob_sub _ _ (p5_iob_sub _ _ (hg _ hpos) (hg _ hℓ0)) (p5_iob_smul h _ (hg' _ hℓ0))
    have hsh : oddSharp (fun x => (g (ℓ0 + h) x - g ℓ0 x) - h * g' ℓ0 x) N =
        oddSharp (g (ℓ0 + h)) N - oddSharp (g ℓ0) N - h • oddSharp (g' ℓ0) N := by
      rw [p5_sharp_sub _ _ (p5_iob_sub _ _ (hg _ hpos) (hg _ hℓ0)) (p5_iob_smul h _ (hg' _ hℓ0)),
        p5_sharp_sub _ _ (hg _ hpos) (hg _ hℓ0), p5_sharp_smul h _ (hg' _ hℓ0)]
    have hentry : oddSharp (g (ℓ0 + h)) N i j - oddSharp (g ℓ0) N i j - h • oddSharp (g' ℓ0) N i j =
        oddSharp (fun x => (g (ℓ0 + h) x - g ℓ0 x) - h * g' ℓ0 x) N i j := by
      rw [hsh]; simp
    rw [hentry, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    refine (p5_entry_le _ i j).trans ?_
    refine ((lem_app_vol_sharp_i _ hiob N N).2.1).trans ?_
    have hsup : supNorm (fun x => (g (ℓ0 + h) x - g ℓ0 x) - h * g' ℓ0 x) ≤ B * h ^ 2 :=
      p5_supNorm_le _ (by positivity) (fun x => p5_taylor g g' hℓ0 hder hB hlip hh x)
    calc _ ≤ Real.sqrt ((min m n : ℕ) : ℝ) * (B * h ^ 2) :=
          mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)
      _ = _ := by ring
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))



private lemma p5_der1 {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    HasDerivAt (fun l : ℝ => (1 : ℝ) * x / Real.sqrt (x ^ 2 + l) ^ (0 + 1))
      ((-(1 / 2) : ℝ) * x / Real.sqrt (x ^ 2 + ℓ) ^ (2 + 1)) ℓ := by
  have := p5_hasDeriv_l 1 (0 + 1) x hℓ
  refine this.congr_deriv ?_
  norm_num
  ring

private lemma p5_der2 {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    HasDerivAt (fun l : ℝ => (-(1 / 2) : ℝ) * x / Real.sqrt (x ^ 2 + l) ^ (2 + 1))
      ((3 / 4 : ℝ) * x / Real.sqrt (x ^ 2 + ℓ) ^ (4 + 1)) ℓ := by
  have := p5_hasDeriv_l (-(1 / 2)) (2 + 1) x hℓ
  refine this.congr_deriv ?_
  norm_num
  ring

private lemma p5_Q_eq {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (K : Mat m n) :
    Q ℓ K = oddSharp (fun x : ℝ => (1 : ℝ) * x / Real.sqrt (x ^ 2 + ℓ) ^ (0 + 1)) K := by
  rw [← eqn_app_vol_filters_sharp_ii hℓ K]
  congr 1
  funext x
  simp [omegaF]

private lemma p5_ridgeDeriv_eq {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (N : Mat m n) :
    ridgeDeriv ℓ N = oddSharp (fun x : ℝ => (-(1 / 2) : ℝ) * x / Real.sqrt (x ^ 2 + ℓ) ^ (2 + 1)) N := by
  ext i j
  have hB : (0 : ℝ) ≤ |(-(1 / 2) : ℝ)| * ((2 : ℕ) + 1) / 2 / Real.sqrt (ℓ / 2) ^ (2 + 2) := by positivity
  have hd := p5_gen (fun l x => (1 : ℝ) * x / Real.sqrt (x ^ 2 + l) ^ (0 + 1))
    (fun l x => (-(1 / 2) : ℝ) * x / Real.sqrt (x ^ 2 + l) ^ (2 + 1)) N i j hℓ
    (fun l hl x => p5_der1 hl x) (fun l hl => p5_iob 1 0 hl) (fun l hl => p5_iob (-(1 / 2)) 2 hl) hB
    (fun l hl x => p5_lip_l (-(1 / 2)) 2 (half_pos hℓ) x l ℓ hl (half_le_self hℓ.le))
  have hev : (fun x : ℝ => Q x N i j) =ᶠ[𝓝 ℓ]
      (fun l : ℝ => oddSharp (fun x : ℝ => (1 : ℝ) * x / Real.sqrt (x ^ 2 + l) ^ (0 + 1)) N i j) := by
    filter_upwards [Ioi_mem_nhds hℓ] with l hl
    rw [p5_Q_eq hl N]
  unfold ridgeDeriv
  simp only [Matrix.of_apply]
  rw [hev.deriv_eq]
  exact hd.deriv



private lemma p5_ridgeDeriv2_eq {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (N : Mat m n) :
    ridgeDeriv2 ℓ N = oddSharp (fun x : ℝ => (3 / 4 : ℝ) * x / Real.sqrt (x ^ 2 + ℓ) ^ (4 + 1)) N := by
  ext i j
  have hB : (0 : ℝ) ≤ |(3 / 4 : ℝ)| * ((4 : ℕ) + 1) / 2 / Real.sqrt (ℓ / 2) ^ (4 + 2) := by positivity
  have hd := p5_gen (fun l x => (-(1 / 2) : ℝ) * x / Real.sqrt (x ^ 2 + l) ^ (2 + 1))
    (fun l x => (3 / 4 : ℝ) * x / Real.sqrt (x ^ 2 + l) ^ (4 + 1)) N i j hℓ
    (fun l hl x => p5_der2 hl x) (fun l hl => p5_iob (-(1 / 2)) 2 hl) (fun l hl => p5_iob (3 / 4) 4 hl) hB
    (fun l hl x => p5_lip_l (3 / 4) 4 (half_pos hℓ) x l ℓ hl (half_le_self hℓ.le))
  have hev : (fun x : ℝ => ridgeDeriv x N i j) =ᶠ[𝓝 ℓ]
      (fun l : ℝ => oddSharp (fun x : ℝ => (-(1 / 2) : ℝ) * x / Real.sqrt (x ^ 2 + l) ^ (2 + 1)) N i j) := by
    filter_upwards [Ioi_mem_nhds hℓ] with l hl
    rw [p5_ridgeDeriv_eq hl N]
  unfold ridgeDeriv2
  simp only [Matrix.of_apply]
  rw [hev.deriv_eq]
  exact hd.deriv



private lemma p5_sup_le (c : ℝ) (j : ℕ) {a ℓ : ℝ} (ha : 0 < a) (hal : a ≤ ℓ) :
    supNorm (fun x : ℝ => c * x / Real.sqrt (x ^ 2 + ℓ) ^ (j + 1)) ≤ |c| / Real.sqrt a ^ j := by
  have hℓ : 0 < ℓ := lt_of_lt_of_le ha hal
  refine p5_supNorm_le _ (by positivity) (fun x => (p5_bound c j hℓ x).trans ?_)
  gcongr

private lemma p5_lip_le (c : ℝ) (j : ℕ) {a ℓ : ℝ} (ha : 0 < a) (hal : a ≤ ℓ) :
    lipConst (fun x : ℝ => c * x / Real.sqrt (x ^ 2 + ℓ) ^ (j + 1)) ≤
      |c| * (j + 1) / Real.sqrt a ^ (j + 1) := by
  have hℓ : 0 < ℓ := lt_of_lt_of_le ha hal
  refine p5_lipConst_le _ (by positivity) (fun x y => (p5_lip_x c j hℓ x y).trans ?_)
  gcongr

end SecondIV

/-- `lem:app-dyn-second`, part (iv). Snapshot `cr-2026-10-23`. Statement, verbatim from
`section.tex` (full environment shown; this declaration is part (iv)):

    \begin{lemma}[Second-order filter estimates]\label{lem:app-dyn-second}
    Let $0<\ell_-\le\ell_+<\infty$. There is $C$, depending only on
    $(\ell_-,\ell_+)$, such that for $\ell\in[\ell_-,\ell_+]$ and all
    $N,N',R\in\R^{\Nout\times\Nin}$, with $D\Qridge\ell(N)[R]$ the derivative of
    $\Qridge\ell$ at $N$ in the direction $R$:
    \begin{enumerate}[label=(\roman*)]
    \item $\norm{D\Qridge\ell(N)[R]}_\F\le\ell^{-1/2}\norm R_\F$;
    \item $\norm{\Qridge\ell(N+R)-\Qridge\ell(N)-D\Qridge\ell(N)[R]}_\F\le C\norm R\norm R_\F$;
    \item $\norm{D\Qridge\ell(N)[R]-D\Qridge\ell(N')[R]}_\F\le C\norm{N-N'}\norm R_\F$;
    \item $\norm{\partial_\ell\Qridge\ell(N)}\le C$,
    $\norm{\partial_\ell\Qridge\ell(N)}_\F+\norm{\partial_\ell^2\Qridge\ell(N)}_\F\le C\sqrt{\min(\Nout,\Nin)}$,
    and $\norm{\partial_\ell\Qridge\ell(N)-\partial_\ell\Qridge\ell(N')}_\F\le C\norm{N-N'}_\F$.
    \end{enumerate}
    \end{lemma}
-/
theorem lem_app_dyn_second_iv {ℓlo ℓhi : ℝ} (hlo : 0 < ℓlo) (hle : ℓlo ≤ ℓhi) :
    ∃ C : ℝ, ∀ {m n : ℕ} (ℓ : ℝ), ℓ ∈ Icc ℓlo ℓhi → ∀ N N' : Mat m n,
      opNorm (ridgeDeriv ℓ N) ≤ C ∧
      fro (ridgeDeriv ℓ N) + fro (ridgeDeriv2 ℓ N) ≤ C * Real.sqrt ((min m n : ℕ) : ℝ) ∧
      fro (ridgeDeriv ℓ N - ridgeDeriv ℓ N') ≤ C * fro (N - N') := by
  set A1 : ℝ := |(-(1 / 2) : ℝ)| / Real.sqrt ℓlo ^ 2 with hA1
  set A2 : ℝ := |(3 / 4 : ℝ)| / Real.sqrt ℓlo ^ 4 with hA2
  set L1 : ℝ := |(-(1 / 2) : ℝ)| * ((2 : ℕ) + 1) / Real.sqrt ℓlo ^ (2 + 1) with hL1
  have hA1n : 0 ≤ A1 := by positivity
  have hA2n : 0 ≤ A2 := by positivity
  have hL1n : 0 ≤ L1 := by positivity
  refine ⟨A1 + A2 + L1, fun {m n} ℓ hℓ N N' => ?_⟩
  have hl : 0 < ℓ := lt_of_lt_of_le hlo hℓ.1
  have hiob1 := p5_iob (-(1 / 2)) 2 hl
  have hiob2 := p5_iob (3 / 4) 4 hl
  have s1 := p5_sup_le (-(1 / 2)) 2 hlo hℓ.1
  have s2 := p5_sup_le (3 / 4) 4 hlo hℓ.1
  have l1 := p5_lip_le (-(1 / 2)) 2 hlo hℓ.1
  have e1 := p5_ridgeDeriv_eq hl N
  have e1' := p5_ridgeDeriv_eq hl N'
  have e2 := p5_ridgeDeriv2_eq hl N
  obtain ⟨o1, f1, d1⟩ := Muon.Volatility.lem_app_vol_sharp_i _ hiob1 N N'
  obtain ⟨_, f2, _⟩ := Muon.Volatility.lem_app_vol_sharp_i _ hiob2 N N'
  have hsq := Real.sqrt_nonneg (((min m n : ℕ) : ℝ))
  rw [← e1] at o1 f1
  rw [← e1, ← e1'] at d1
  rw [← e2] at f2
  refine ⟨o1.trans (s1.trans (by linarith)), ?_, d1.trans ?_⟩
  · calc fro (ridgeDeriv ℓ N) + fro (ridgeDeriv2 ℓ N)
        ≤ Real.sqrt ((min m n : ℕ) : ℝ) * (A1 + A2) := by
          have := mul_le_mul_of_nonneg_left s1 hsq
          have := mul_le_mul_of_nonneg_left s2 hsq
          nlinarith
      _ ≤ _ := by nlinarith
  · have : 0 ≤ fro (N - N') := Real.sqrt_nonneg _
    exact mul_le_mul_of_nonneg_right (l1.trans (by linarith)) this

end Muon.Dynamics

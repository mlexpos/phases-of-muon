import Muon.External.Certificates
import Muon.Volatility.LagKernel
import Muon.Volatility.HalfCandidates
import Muon.Volatility.Closed.Profile
import Muon.Volatility.OddSpectral
import Muon.Volatility.Replication
import Muon.Dynamics.Basic

/-!
# Appendix D, work package L-D.14: same-step marginals, mode kernels, joint forcing, disintegration

Work package L-D.14 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/04-volatility/section.tex`: `thm:app-vol-mode-kernels` (l.2786–2806),
`thm:app-vol-joint-forcing` (l.2862–2888), `prop:app-vol-disintegration` (l.2941–2960),
`prop:app-vol-half-recovery` (l.2997–3002), `cor:app-vol-marginals` (l.3030–3041), with the
displays `eqn:app-vol-rows` (l.2776), `eqn:app-vol-marginals-tests` and `eqn:app-vol-marginals`
(inside `cor:app-vol-marginals`), the finite-time measure `𝔉_T` (l.2882–2884), and the closed
mode kernel `eqn:app-vol-closed-mode-kernel` (l.1596) with `eqn:app-vol-closed-cl` (l.1600).
Card: `sections/04-volatility/CARD.md` §2, §3 (rows of these five labels), §5 (row L-D.14), §6
(R5, R9, R10, R17, R24).

Reused, not redefined: `lagResp`, `lagRowBar`, `rowVBar`, `measureCl`, `measureClBar`,
`measureInt`, `measureZeta`, `modeVij`, `modeVijActual`, `classDiag`, `projOut`, `projIn`
(`Muon.Volatility.LagKernel`); `rowLag`, `rowGamma`, `centredUpd`, `SizeFin`, `SizeSeq`
(`Muon.Volatility.Defs`); `volraw`, `volTildeZero` (`HalfCandidates`, via `branchSol`);
`replVec` (`LagKernel`), `replCov`, `def_app_vol_replication`, `replState`
(`Replication`); `omegaF` (`OddSpectral`); `IsStdGaussianFamily`, `emaXi₁`, `emaXi₂`,
`profileF`, `pairedB`, `branchPt`, `profileDelta` (`Closed.Profile`); `SetupRegime`
(`Setup.Regime`); `Muon.nuOut`, `Muon.nuIn`, `Muon.Dynamics.kStar`.

Encoding decisions:
* Regime sequences use `R : SetupRegime`, `Ω : ℕ → Type`; fixed-dimension statements use
  `SizeFin` (and `1 ≤ C_Σ`) as top-level hypotheses. Every statement that carries a constant
  depending only on `(ϱ_-, γ⋆, C_Σ, β)` takes `ϱ_-` before the ridges, times and tests.
* Suprema are written as "for every `ε > 0`, eventually, every point is within `ε`" (the
  sup-to-zero convention of `LagKernel`), so no `iSup` without `BddAbove` occurs.
* Total variation of a finitely supported signed measure `(ℝ × ℝ) →₀ ℝ` is `finTV` (sum of
  absolute atoms), bridged to `Muon.Dynamics.tvNorm` by `finTV_eq_tvNorm`. The bounded-Lipschitz
  norm uses the project's `Muon.Dynamics.blTest R.CSig` (test functions bounded by one and
  l1-Lipschitz on the rectangle `[0,C_Σ]²`, the source's norm at l.2860); it is stated as
  "every test `φ ∈ blTest` has `|finInt m φ| ≤ ε`", which avoids a supremum.
* Mode entries `V_ij = u_iᵀ V v_j` are the entries in the eigenbases `SP.uOutᵀ · · SP.vIn`
  (`modeVijActual`); the closed form is stated for scalar eigenvalues.
* `closedModeH`, `closedModeCl` transcribe `eqn:app-vol-closed-mode-kernel` and
  `eqn:app-vol-closed-cl` (no Lean object exists yet; L-D.18 owns the closed-modes corollary
  and should reuse these two definitions, see the report). They use the EMA paired profile at
  lag `ℓ` with a standard Gaussian family `g` (`IsStdGaussianFamily`).
* Replications: `def_app_vol_replication` takes the state proof `hA`; the replicated eigenvalue
  data are `replVec`. The replicated spectral data `SP'` are universally quantified with the
  required eigenvalues; `measureZeta` uses only the eigenvalues of the spectral data.
* The finite-time measure `finiteTimeMeasure` is the atomic form of `𝔉_T`; its integrability is
  a conjunct of the theorem using it. The integrated measure `𝔠_int` is quantified over all times
  `t` in the regime and fixed-model statements (it is time-free by stationarity; `𝔉_T` uses the
  times `1, …, T` directly).
* Integrals and sums in statements: every `∫`/`tsum` used as a value that the source claims to
  converge carries an `Integrable` or `Summable` conjunct.

Card corrections in force (`CORRECTIONS.md` / card §6): R5 (replicated state `Â^(N)` is a
hypothesis `hA` of the replication), R9 (joint-forcing constant `4max(γ⋆, K⋆)ε` is not stated
here; the statement is qualitative), R10 (mode-kernels (iv) split into four declarations),
R17 (deterministic statements at an arbitrary compact `I ⊂ (0,∞)` with `ϱ_- = min I`), R24
(the marginal identities are stated at a fixed dimension for every `ϱ > 0`).
-/

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped Matrix MatrixOrder ENNReal
open Matrix
open Muon Muon.Setup Muon.DetEquiv

noncomputable section

namespace Muon.Volatility

/-! ## Private helpers for the mode-kernel bounds (P-D.14.P2) -/

private lemma md_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma md_opNorm_mul {k l p : ℕ} (A : Mat k l) (B : Mat l p) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B

private lemma md_opNorm_diag {k : ℕ} (d : Fin k → ℝ) (hd : ∀ i, |d i| ≤ 1) :
    opNorm (Matrix.diagonal d) ≤ 1 := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simpa [Real.norm_eq_abs] using hd i

private lemma md_opNorm_orth {k : ℕ} (U : Mat k k) (hU : Uᵀ * U = 1) : opNorm U ≤ 1 := by
  open scoped Matrix.Norms.L2Operator in
  have h1 : opNorm (1 : Mat k k) ≤ 1 := by
    have : (1 : Mat k k) = Matrix.diagonal (fun _ => (1 : ℝ)) := Matrix.diagonal_one.symm
    rw [this]
    exact md_opNorm_diag _ (fun i => by simp)
  have h2 : ‖U‖ * ‖U‖ = ‖Uᵀ * U‖ := by
    have := CStarRing.norm_star_mul_self (x := U)
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact this.symm
  rw [hU, ← opNorm_eq_norm] at h2
  rw [opNorm_eq_norm]
  have hn : 0 ≤ ‖U‖ := norm_nonneg _
  rw [← opNorm_eq_norm] at h2 ⊢
  by_contra hcon
  push_neg at hcon
  have := h1
  nlinarith [h2]

private lemma md_opNorm_conj {k : ℕ} (U : Mat k k) (hU : Uᵀ * U = 1) (d : Fin k → ℝ)
    (hd : ∀ i, |d i| ≤ 1) : opNorm (U * Matrix.diagonal d * Uᵀ) ≤ 1 := by
  have hU1 := md_opNorm_orth U hU
  have hUt : opNorm Uᵀ ≤ 1 := by rw [md_opNorm_transpose]; exact hU1
  have hD := md_opNorm_diag d hd
  have n0 : ∀ {p q : ℕ} (A : Mat p q), 0 ≤ opNorm A := fun A => by unfold opNorm; exact norm_nonneg _
  calc opNorm (U * Matrix.diagonal d * Uᵀ) ≤ opNorm (U * Matrix.diagonal d) * opNorm Uᵀ :=
        md_opNorm_mul _ _
    _ ≤ (opNorm U * opNorm (Matrix.diagonal d)) * opNorm Uᵀ :=
        mul_le_mul_of_nonneg_right (md_opNorm_mul _ _) (n0 _)
    _ ≤ 1 := by
        have a1 := mul_le_mul hU1 hD (n0 _) zero_le_one
        have a2 := mul_le_mul a1 hUt (n0 _) (by norm_num)
        simpa using a2

private lemma md_sizefin_pos {m n B : ℕ} (Fp : FrozenParams m n B) (γstar CSig : ℝ)
    (hS : SizeFin Fp.C B γstar CSig) : 0 < γstar := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      have := Fp.hA
      simp [fro] at this
    · exact h
  have hB : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  have h1 : (1 : ℝ) ≤ ((max m n : ℕ) : ℝ) := by
    exact_mod_cast (le_trans hm (le_max_left m n))
  have h2 := hS.1
  by_contra hcon
  push_neg at hcon
  nlinarith

/-- Linearity of `lagResp` in the output diagonal test, as a finite sum over unit vectors. -/
private lemma md_lin_sum (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ) (ϱ ϱ' : ℝ) (hϱ : 0 < ϱ)
    (hϱ' : 0 < ϱ') (a : Fin m → ℝ) :
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam a (fun _ : Fin n => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ') =
      ∑ i, a i * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1)
        (fun _ : Fin n => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ') := by
  obtain ⟨-, hlin, -⟩ := thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS
    hCSig ℓ (omegaF ϱ) (omegaF ϱ') (lem_app_vol_sharp_ii hϱ hϱ).2.1 (lem_app_vol_sharp_ii hϱ' hϱ').2.1
  set G : Fin n → ℝ := fun _ => (1 : ℝ) with hG
  have h0 : lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (fun _ => (0 : ℝ)) G (omegaF ϱ)
      (omegaF ϱ') = 0 := by
    have := hlin 1 (fun _ => 0) (fun _ => 0) G
    simp only [mul_zero, zero_add, one_mul] at this
    linarith
  have step : ∀ s : Finset (Fin m),
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (fun j => ∑ i ∈ s, a i * (Pi.single i 1 : Fin m → ℝ) j) G
          (omegaF ϱ) (omegaF ϱ') =
        ∑ i ∈ s, a i * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1) G (omegaF ϱ)
          (omegaF ϱ') := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert k s hk ih =>
      have := hlin (a k) (Pi.single k 1) (fun j => ∑ i ∈ s, a i * (Pi.single i 1 : Fin m → ℝ) j) G
      simp only [Finset.sum_insert hk]
      rw [← ih]
      rw [← this]
  have := step Finset.univ
  have hfun : (fun j => ∑ i ∈ (Finset.univ : Finset (Fin m)), a i * (Pi.single i 1 : Fin m → ℝ) j) = a := by
    funext j
    simp [Pi.single_apply]
  rwa [hfun] at this

private lemma md_rowbar_sum {m n : ℕ} (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    (β : ℝ) (ℓ B : ℕ) (hB : 0 < B) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (ϱ ϱ' : ℝ) :
    (B : ℝ)⁻¹ * (∑ i : Fin m, |lagRowBar cert γstar CSig β ℓ B μ lam i ϱ ϱ'|) =
      ∑ i : Fin m, |lagResp cert γstar CSig β ℓ B μ lam (Pi.single i 1)
        (fun _ : Fin n => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ')| := by
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold lagRowBar
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg B), inv_mul_cancel_left₀ hB']

private lemma md_FG_norm {m n B : ℕ} {Fp : FrozenParams m n B} (S : SpectralData Fp.C)
    (Fd : Fin m → ℝ) (hFd : ∀ i, |Fd i| ≤ 1) :
    opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1 ∧
      opNorm (S.vIn * Matrix.diagonal (fun _ : Fin n => (1 : ℝ)) * S.vInᵀ) ≤ 1 :=
  ⟨md_opNorm_conj _ S.huOut _ hFd, md_opNorm_conj _ S.hvIn _ (fun _ => by simp)⟩

/-- Sum of absolute values of the unit-vector responses is bounded by any uniform bound for
sign tests. -/
private lemma md_sum_abs (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ) (ϱ ϱ' : ℝ) (hϱ : 0 < ϱ)
    (hϱ' : 0 < ϱ') (M : ℝ)
    (hM : ∀ Fd : Fin m → ℝ, (∀ i, |Fd i| ≤ 1) →
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd (fun _ : Fin n => (1 : ℝ)) (omegaF ϱ)
        (omegaF ϱ')| ≤ M) :
    ∑ i, |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1)
        (fun _ : Fin n => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ')| ≤ M := by
  set L : Fin m → ℝ := fun i => lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1)
    (fun _ : Fin n => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ') with hL
  let s : Fin m → ℝ := fun i => if 0 ≤ L i then 1 else -1
  have hs : ∀ i, |s i| ≤ 1 := fun i => by
    simp only [s]; split_ifs <;> simp
  have hsum : ∑ i, |L i| = ∑ i, s i * L i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [s]
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.mp h)]; ring
  have := hM s hs
  rw [md_lin_sum cert γstar CSig Fp S hS hCSig ℓ ϱ ϱ' hϱ hϱ' s] at this
  change ∑ i, |L i| ≤ M
  rw [hsum]
  exact (le_abs_self _).trans this

private lemma mm_replMat_apply {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (N : ℕ) (a b : Fin (N * m)) :
    replMat S N a b = S ((replIdx m N).symm a).1 ((replIdx m N).symm b).1 *
      (if ((replIdx m N).symm a).2 = ((replIdx m N).symm b).2 then 1 else 0) := by
  simp [replMat, repKron, Matrix.one_apply]

private lemma mm_replMat_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (N : ℕ) :
    replMat (A * B) N = replMat A N * replMat B N := by
  unfold replMat repKron
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  erw [← Matrix.mul_kronecker_mul, mul_one]
  rfl

private lemma mm_replMat_transpose {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (N : ℕ) :
    (replMat A N)ᵀ = replMat Aᵀ N := by
  unfold replMat repKron
  rw [Matrix.transpose_submatrix]
  congr 1
  have hT : (Matrix.kronecker A (1 : Matrix (Fin N) (Fin N) ℝ))ᵀ =
      Matrix.kronecker Aᵀ (1 : Matrix (Fin N) (Fin N) ℝ)ᵀ :=
    (Matrix.kroneckerMap_transpose _ _ _).symm
  rw [hT, Matrix.transpose_one]

private lemma mm_replMat_diagonal {m : ℕ} (d : Fin m → ℝ) (N : ℕ) :
    replMat (Matrix.diagonal d) N = Matrix.diagonal (replVec N d) := by
  ext a b
  rw [mm_replMat_apply]
  unfold replVec
  simp only [Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h; simp
  · have : ¬ (((replIdx m N).symm a).1 = ((replIdx m N).symm b).1 ∧
        ((replIdx m N).symm a).2 = ((replIdx m N).symm b).2) := by
      rintro ⟨h1, h2⟩
      exact h ((replIdx m N).symm.injective (Prod.ext h1 h2))
    by_cases h1 : ((replIdx m N).symm a).1 = ((replIdx m N).symm b).1
    · have h2 : ¬ ((replIdx m N).symm a).2 = ((replIdx m N).symm b).2 := fun h2 => this ⟨h1, h2⟩
      simp [h, h2]
    · simp [h, h1]

private lemma mm_replMat_one {m : ℕ} (N : ℕ) : replMat (1 : Matrix (Fin m) (Fin m) ℝ) N = 1 := by
  unfold replMat repKron
  have h : Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℝ) (1 : Matrix (Fin N) (Fin N) ℝ) = 1 :=
    Matrix.one_kronecker_one
  rw [h, Matrix.submatrix_one_equiv]

private lemma mm_replMat_orth {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : Sᵀ * S = 1) (N : ℕ) :
    (replMat S N)ᵀ * replMat S N = 1 := by
  rw [mm_replMat_transpose, ← mm_replMat_mul, hS, mm_replMat_one]

private lemma mm_eig_matrix {k : ℕ} (S U : Matrix (Fin k) (Fin k) ℝ) (μ : Fin k → ℝ)
    (h : ∀ i : Fin k, S *ᵥ (fun r => U r i) = μ i • (fun r => U r i)) :
    S * U = U * Matrix.diagonal μ := by
  ext r i
  have := congrFun (h i) r
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  rw [this]; ring

private lemma mm_eig_vec {k : ℕ} (S U : Matrix (Fin k) (Fin k) ℝ) (μ : Fin k → ℝ)
    (h : S * U = U * Matrix.diagonal μ) (i : Fin k) :
    S *ᵥ (fun r => U r i) = μ i • (fun r => U r i) := by
  funext r
  have := congrFun (congrFun h r) i
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at this
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [this]; ring

private lemma mm_exists_replSpec {m n : ℕ} (C : Covariances m n) (S : SpectralData C) (N : ℕ) :
    ∃ S' : SpectralData (replCov C N), S'.uOut = replMat S.uOut N ∧ S'.vIn = replMat S.vIn N ∧
      S'.μ = replVec N S.μ ∧ S'.lam = replVec N S.lam := by
  have h1 := mm_eig_matrix C.Sout S.uOut S.μ S.eigOut
  have h2 := mm_eig_matrix C.Sin S.vIn S.lam S.eigIn
  refine ⟨⟨replMat S.uOut N, replMat S.vIn N, replVec N S.μ, replVec N S.lam,
    mm_replMat_orth _ S.huOut N, mm_replMat_orth _ S.hvIn N, ?_, ?_⟩, rfl, rfl, rfl, rfl⟩
  · intro i
    refine mm_eig_vec _ _ _ ?_ i
    change replMat C.Sout N * replMat S.uOut N = replMat S.uOut N * Matrix.diagonal (replVec N S.μ)
    rw [← mm_replMat_diagonal, ← mm_replMat_mul, ← mm_replMat_mul, h1]
  · intro i
    refine mm_eig_vec _ _ _ ?_ i
    change replMat C.Sin N * replMat S.vIn N = replMat S.vIn N * Matrix.diagonal (replVec N S.lam)
    rw [← mm_replMat_diagonal, ← mm_replMat_mul, ← mm_replMat_mul, h2]

private lemma mm_vals_repl {m : ℕ} (x : Fin m → ℝ) (N : ℕ) (hN : 0 < N) :
    Finset.univ.image (replVec N x) = Finset.univ.image x := by
  classical
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨((replIdx m N).symm k).1, rfl⟩
  · rintro ⟨i, rfl⟩
    let q : Fin N := ⟨0, hN⟩
    refine ⟨replIdx m N (i, q), ?_⟩
    simp [replVec]

private lemma mm_classDiag_repl {m : ℕ} (x : Fin m → ℝ) (N : ℕ) (a : ℝ) :
    classDiag (replVec N x) a = replVec N (classDiag x a) := by
  classical
  funext k
  rfl

private lemma mm_lagResp_repl (cert : Muon.External.GaussianOpNorm) (γstar CSig β : ℝ)
    {m n : ℕ} (ℓ B N : ℕ) (hN : 0 < N) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f g : ℝ → ℝ) :
    lagResp cert γstar CSig β ℓ (N * B) (replVec N μ) (replVec N lam)
        (replVec N Fd) (replVec N Gd) f g =
      lagResp cert γstar CSig β ℓ B μ lam Fd Gd f g := by
  unfold lagResp lagRespCut treeRespExt
  apply congrArg ((atTop ×ˢ atTop).limUnder)
  funext p
  apply congrArg atTop.limUnder
  funext k
  exact def_app_vol_tree_replication β ℓ p.1 p.2 B μ lam Fd Gd N hN
    (treeApprox (volDR cert p.2 CSig γstar) f k)
    (treeApprox (volDR cert p.2 CSig γstar) g k)

private lemma mm_lagGammaBar_repl (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n : ℕ} (β : ℝ) (B N : ℕ) (hN : 0 < N) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (ϱ ϱ' : ℝ) :
    lagGammaBar cert γstar CSig β (N * B) (replVec N μ) (replVec N lam)
        (replVec N Fd) (replVec N Gd) ϱ ϱ' =
      lagGammaBar cert γstar CSig β B μ lam Fd Gd ϱ ϱ' := by
  have hrepl := fun ℓ => mm_lagResp_repl cert γstar CSig β ℓ B N hN μ lam Fd Gd
    (omegaF ϱ) (omegaF ϱ')
  have hrepl' := fun ℓ => mm_lagResp_repl cert γstar CSig β ℓ B N hN μ lam Fd Gd
    (omegaF ϱ') (omegaF ϱ)
  unfold lagGammaBar
  rw [hrepl 0]
  have hs : (∑' ℓ : ℕ,
      (lagResp cert γstar CSig β (ℓ + 1) (N * B) (replVec N μ) (replVec N lam)
          (replVec N Fd) (replVec N Gd) (omegaF ϱ) (omegaF ϱ') +
        lagResp cert γstar CSig β (ℓ + 1) (N * B) (replVec N μ) (replVec N lam)
          (replVec N Fd) (replVec N Gd) (omegaF ϱ') (omegaF ϱ))) =
      ∑' ℓ : ℕ, (lagResp cert γstar CSig β (ℓ + 1) B μ lam Fd Gd
          (omegaF ϱ) (omegaF ϱ') +
        lagResp cert γstar CSig β (ℓ + 1) B μ lam Fd Gd
          (omegaF ϱ') (omegaF ϱ)) := by
    refine tsum_congr fun ℓ => ?_
    rw [hrepl (ℓ + 1), hrepl' (ℓ + 1)]
  rw [hs]


private lemma mm_pos_of_fro {m n : ℕ} (A : Mat m n) (h : fro A = 1) : 0 < m ∧ 0 < n := by
  constructor
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp [fro] at h
    · exact h0
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp [fro] at h
    · exact h0

private lemma mm_fro_nn {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma mm_fro_transpose {k l : ℕ} (A : Mat k l) : fro Aᵀ = fro A := by
  unfold fro
  congr 1
  exact Finset.sum_comm

private lemma mm_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma mm_opNorm_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ opNorm A := by
  unfold opNorm
  exact norm_nonneg _

private lemma mm_fro_sq {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma mm_fro_mul_le_left {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ opNorm M * fro N := by
  have hcol : ∀ j : Fin r, ∑ i, (M * N) i j ^ 2 ≤ opNorm M ^ 2 * ∑ k, N k j ^ 2 := by
    intro j
    obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin q), ∀ k, v.ofLp k = N k j :=
      ⟨(EuclideanSpace.equiv (Fin q) ℝ).symm (fun k => N k j), fun k => rfl⟩
    have h1 : ‖(EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)‖ ≤ opNorm M * ‖v‖ := by
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
    rw [mm_fro_sq, mul_pow, mm_fro_sq, Finset.sum_comm]
    calc ∑ j, ∑ i, (M * N) i j ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, N k j ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, N k j ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (mm_fro_nn _) (mul_nonneg (mm_opNorm_nonneg M) (mm_fro_nn N))
    two_ne_zero).mp hfro

private lemma mm_fro_mul_le_right {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ fro M * opNorm N := by
  have h := mm_fro_mul_le_left Nᵀ Mᵀ
  rw [mm_opNorm_transpose, mm_fro_transpose, ← Matrix.transpose_mul, mm_fro_transpose] at h
  linarith [mul_comm (opNorm N) (fro M)]

private lemma mm_abs_entry_le_fro {k l : ℕ} (K : Mat k l) (i : Fin k) (j : Fin l) :
    |K i j| ≤ fro K := by
  unfold fro
  apply Real.abs_le_sqrt
  have h1 : ‖K i j‖ ^ 2 ≤ ∑ j', ‖K i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖K i j'‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖K i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖K i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖K i' j'‖ ^ 2)
      (fun i' _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
  have h3 : ‖K i j‖ ^ 2 = K i j ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  linarith

private lemma mm_summable_mat_of_fro {k l : ℕ} {ι : Type*} (f : ι → Mat k l)
    (hf : Summable fun j => fro (f j)) : Summable f := by
  refine (Pi.summable).2 fun i => (Pi.summable).2 fun k => ?_
  refine Summable.of_norm_bounded hf (fun j => ?_)
  rw [Real.norm_eq_abs]
  exact mm_abs_entry_le_fro (f j) i k

private lemma mm_summand_cont {m n B : ℕ} (F : FrozenParams m n B) :
    Continuous (fun p : Vec m × Vec n =>
      (dotProduct p.1 (Matrix.mulVec F.A p.2)) • (rOut F.C * outer p.1 p.2 * rIn F.C)) := by
  fun_prop

private lemma mm_batch_sm {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    StronglyMeasurable (frozenBatchG F S s) := by
  unfold frozenBatchG
  refine StronglyMeasurable.const_smul ?_ ((B : ℝ))⁻¹
  exact Finset.stronglyMeasurable_fun_sum Finset.univ fun a _ =>
    (mm_summand_cont F).comp_stronglyMeasurable (S.meas s a).stronglyMeasurable

private lemma mm_buf_aesm {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) : AEStronglyMeasurable (frozenBuf F S t) P := by
  have : TopologicalSpace.PseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin n → ℝ))
  have hae := (lem_app_setup_ema_law_i F S).1
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
    ∑ j ∈ Finset.range N, emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) (fun N => ?_) ?_
  · exact (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ =>
      (mm_batch_sm F S (t + 1 - (j : ℤ))).const_smul (emaW F.β j)).aestronglyMeasurable
  · filter_upwards [hae] with ω hω
    have hs : Summable (fun j : ℕ => emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) :=
      mm_summable_mat_of_fro _ (hω t)
    exact hs.hasSum.tendsto_sum_nat

private lemma mm_Q_meas {k l : ℕ} (ϱ : ℝ) (hϱ : 0 < ϱ) : Measurable (fun K : Mat k l => Q ϱ K) :=
  (measurable_Q (m := k) (n := l)).comp
    ((measurable_const (a := (⟨ϱ, hϱ.le⟩ : Set.Ici (0 : ℝ)))).prodMk measurable_id)

private lemma mm_upd_aesm {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 < ϱ) (t : ℤ) : AEStronglyMeasurable (frozenUpd F S ϱ t) P := by
  exact ((mm_Q_meas ϱ hϱ).comp_aemeasurable (mm_buf_aesm F S t).aemeasurable).aestronglyMeasurable

private lemma mm_upd_fro_le {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 < ϱ) (t : ℤ) (ω : Ω) : fro (frozenUpd F S ϱ t ω) ≤ (m : ℝ) + 1 := by
  obtain ⟨-, h2, h3, -⟩ := lem_app_setup_filter_i ϱ hϱ.le (frozenBuf F S t ω)
  have h4 : ((frozenBuf F S t ω).rank : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast h3.trans (min_le_left _ _)
  have h5 : fro (frozenUpd F S ϱ t ω) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by
    have : fro (Q ϱ (frozenBuf F S t ω)) ^ 2 ≤ (m : ℝ) := h2.trans h4
    unfold frozenUpd; nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by positivity) two_ne_zero).mp h5

private lemma mm_int_trace_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {a b : ℕ} (A : Mat a b) (M : Ω → Mat b a)
    (hM : ∀ i j, Integrable (fun ω => M ω i j) P) :
    Integrable (fun ω => Matrix.trace (A * M ω)) P ∧
      ∫ ω, Matrix.trace (A * M ω) ∂P = Matrix.trace (A * Muon.mean P M) := by
  have hf : ∀ ω, Matrix.trace (A * M ω) = ∑ i, ∑ j, A i j * M ω j i := by
    intro ω; simp [Matrix.trace, Matrix.mul_apply]
  simp_rw [hf]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hM j i).const_mul _, ?_⟩
  rw [integral_finsetSum (Finset.univ : Finset (Fin a)) (f := fun i ω => ∑ j, A i j * M ω j i)
    (fun i _ => integrable_finsetSum _ fun j _ => (hM j i).const_mul _)]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Muon.mean, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum (Finset.univ : Finset (Fin b)) (f := fun j ω => A i j * M ω j i)
    (fun j _ => (hM j i).const_mul _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]

private lemma mm_branch_nonneg (Fw' : ℝ → ℝ) (ν ν' : FiniteMeasure ℝ) (s : ℝ) :
    0 ≤ (branchSol Fw' ν ν' s).2.2.1 ∧ 0 ≤ (branchSol Fw' ν ν' s).2.2.2 := by
  unfold branchSol
  split_ifs with h
  · have hs := h.choose_spec
    revert hs
    generalize h.choose = x
    obtain ⟨σ, σ', a, c⟩ := x
    intro hs
    exact ⟨hs.2.2.1, hs.2.2.2.1⟩
  · simp

private lemma mm_gram_eq {d : ℕ} (A : Mat d d) (hA : A.PosSemidef) {a ϱ : ℝ} (ha : 0 ≤ a)
    (hϱ : 0 < ϱ) :
    (a • A) * (a • A + ϱ • (1 : Mat d d))⁻¹ = 1 - ϱ • (ϱ • (1 : Mat d d) + a • A)⁻¹ := by
  have hU : IsUnit (ϱ • (1 : Mat d d) + a • A) :=
    ((Matrix.PosDef.one.smul hϱ).add_posSemidef (hA.smul ha)).isUnit
  rw [add_comm (a • A)]
  have hdet : IsUnit (ϱ • (1 : Mat d d) + a • A).det := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have h1 : (ϱ • (1 : Mat d d) + a • A) * (ϱ • (1 : Mat d d) + a • A)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdet
  have h2 : a • A = (ϱ • (1 : Mat d d) + a • A) - ϱ • (1 : Mat d d) := by abel
  calc (a • A) * (ϱ • (1 : Mat d d) + a • A)⁻¹
      = ((ϱ • (1 : Mat d d) + a • A) - ϱ • (1 : Mat d d)) * (ϱ • (1 : Mat d d) + a • A)⁻¹ :=
        congrArg (· * (ϱ • (1 : Mat d d) + a • A)⁻¹) h2
    _ = 1 - ϱ • (ϱ • (1 : Mat d d) + a • A)⁻¹ := by
        rw [Matrix.sub_mul, h1, Matrix.smul_mul, Matrix.one_mul]

private lemma mm_gram_int {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {k l : ℕ} (Z : Ω → Mat k l)
    (hZ : AEStronglyMeasurable Z P) (c : ℝ) (hc : ∀ ω, fro (Z ω) ≤ c)
    (ho : ∀ ω, opNorm (Z ω) ≤ 1) :
    (∀ i j : Fin k, Integrable (fun ω => (Z ω * (Z ω)ᵀ) i j) P) ∧
      (∀ i' j' : Fin l, Integrable (fun ω => ((Z ω)ᵀ * Z ω) i' j') P) := by
  have h1 : Continuous (fun K : Mat k l => K * Kᵀ) :=
    continuous_id.matrix_mul continuous_id.matrix_transpose
  have h2 : Continuous (fun K : Mat k l => Kᵀ * K) :=
    continuous_id.matrix_transpose.matrix_mul continuous_id
  refine ⟨fun i j => ?_, fun i' j' => ?_⟩
  · refine Integrable.of_bound (C := c) ?_ ?_
    · exact ((continuous_apply j).comp ((continuous_apply i).comp h1)).comp_aestronglyMeasurable hZ
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs]
      refine (mm_abs_entry_le_fro _ i j).trans ?_
      refine (mm_fro_mul_le_right _ _).trans ?_
      rw [mm_opNorm_transpose]
      calc fro (Z ω) * opNorm (Z ω) ≤ fro (Z ω) * 1 :=
            mul_le_mul_of_nonneg_left (ho ω) (mm_fro_nn _)
        _ ≤ c := by rw [mul_one]; exact hc ω
  · refine Integrable.of_bound (C := c) ?_ ?_
    · exact ((continuous_apply j').comp ((continuous_apply i').comp h2)).comp_aestronglyMeasurable hZ
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs]
      refine (mm_abs_entry_le_fro _ i' j').trans ?_
      refine (mm_fro_mul_le_right _ _).trans ?_
      calc fro (Z ω)ᵀ * opNorm (Z ω) ≤ fro (Z ω)ᵀ * 1 :=
            mul_le_mul_of_nonneg_left (ho ω) (mm_fro_nn _)
        _ ≤ c := by rw [mul_one, mm_fro_transpose]; exact hc ω

private lemma mm_upd_gram_int {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 < ϱ) (t : ℤ) :
    (∀ i j : Fin m, Integrable (fun ω => (frozenUpd F S ϱ t ω * (frozenUpd F S ϱ t ω)ᵀ) i j) P) ∧
      (∀ i' j' : Fin n,
        Integrable (fun ω => ((frozenUpd F S ϱ t ω)ᵀ * frozenUpd F S ϱ t ω) i' j') P) := by
  exact mm_gram_int (frozenUpd F S ϱ t) (mm_upd_aesm F S hϱ t) ((m : ℝ) + 1)
    (mm_upd_fro_le F S hϱ t)
    (fun ω => (lem_app_setup_filter_i ϱ hϱ.le (frozenBuf F S t ω)).1)

private lemma mm_quad_le {d : ℕ} (D : Mat d d) (x : Vec d) (hx : x ⬝ᵥ x = 1) :
    |x ⬝ᵥ (D *ᵥ x)| ≤ opNorm D := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm]
  set xe : EuclideanSpace ℝ (Fin d) := (EuclideanSpace.equiv (Fin d) ℝ).symm x with hxe
  set ye : EuclideanSpace ℝ (Fin d) := (EuclideanSpace.equiv (Fin d) ℝ).symm (D *ᵥ x) with hye
  have hD := D.l2_opNorm_mulVec xe
  have hxn : ‖xe‖ = 1 := by
    have h1 : ‖xe‖ ^ 2 = x ⬝ᵥ x := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [hxe, dotProduct, Real.norm_eq_abs, sq_abs, sq]
    rw [hx] at h1
    nlinarith [norm_nonneg xe]
  have hinner : x ⬝ᵥ (D *ᵥ x) = @inner ℝ _ _ xe ye := by
    simp [hxe, hye, dotProduct, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hye' : ‖ye‖ ≤ ‖D‖ := by
    have : ‖ye‖ ≤ ‖D‖ * ‖xe‖ := hD
    rwa [hxn, mul_one] at this
  calc |x ⬝ᵥ (D *ᵥ x)| = |@inner ℝ _ _ xe ye| := by rw [hinner]
    _ ≤ ‖xe‖ * ‖ye‖ := abs_real_inner_le_norm xe ye
    _ ≤ 1 * ‖D‖ := by rw [hxn]; exact mul_le_mul_of_nonneg_left hye' (by norm_num)
    _ = ‖D‖ := one_mul _

private lemma mm_col_dot {d : ℕ} (U : Mat d d) (hU : Uᵀ * U = 1) (i : Fin d) :
    (fun k => U k i) ⬝ᵥ (fun k => U k i) = 1 := by
  have h := congrFun (congrFun hU i) i
  simpa [Matrix.mul_apply, dotProduct] using h

private lemma mm_halfGram_eig {d : ℕ} (Sg : Mat d d) (hSg : Sg.PosSemidef) {a ϱ μ : ℝ}
    (ha : 0 ≤ a) (hϱ : 0 < ϱ) (x : Vec d) (hx : x ⬝ᵥ x = 1) (heig : Sg *ᵥ x = μ • x) :
    x ⬝ᵥ (((a • Sg) * (a • Sg + ϱ • (1 : Mat d d))⁻¹) *ᵥ x) = a * μ / (ϱ + a * μ) := by
  rw [mm_gram_eq Sg hSg ha hϱ]
  have hU : IsUnit (ϱ • (1 : Mat d d) + a • Sg) :=
    ((Matrix.PosDef.one.smul hϱ).add_posSemidef (hSg.smul ha)).isUnit
  have hdet : IsUnit (ϱ • (1 : Mat d d) + a • Sg).det := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hKx : (ϱ • (1 : Mat d d) + a • Sg) *ᵥ x = (ϱ + a * μ) • x := by
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, heig, smul_smul,
      add_smul]
  have hcancel : (ϱ + a * μ) • ((ϱ • (1 : Mat d d) + a • Sg)⁻¹ *ᵥ x) = x := by
    rw [← Matrix.mulVec_smul, ← hKx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
      Matrix.one_mulVec]
  have hc : ϱ + a * μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hcancel
    rw [← hcancel] at hx
    simp at hx
  have hinv : (ϱ • (1 : Mat d d) + a • Sg)⁻¹ *ᵥ x = (ϱ + a * μ)⁻¹ • x := by
    calc (ϱ • (1 : Mat d d) + a • Sg)⁻¹ *ᵥ x
        = (ϱ + a * μ)⁻¹ • ((ϱ + a * μ) • ((ϱ • (1 : Mat d d) + a • Sg)⁻¹ *ᵥ x)) := by
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = (ϱ + a * μ)⁻¹ • x := by rw [hcancel]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hinv, smul_smul,
    dotProduct_sub, dotProduct_smul, hx, smul_eq_mul, mul_one]
  field_simp
  ring

private lemma mm_trace_basis {d : ℕ} (D U : Mat d d) (hU : Uᵀ * U = 1) :
    D.trace = ∑ i, (fun k => U k i) ⬝ᵥ (D *ᵥ (fun k => U k i)) := by
  have hU' : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  calc D.trace = (D * (U * Uᵀ)).trace := by rw [hU', Matrix.mul_one]
    _ = (Uᵀ * D * U).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (D * U), Matrix.mul_assoc]
    _ = _ := by simp [Matrix.trace, Matrix.mul_apply, dotProduct, Matrix.mulVec,
      Finset.mul_sum, mul_assoc]

private lemma mm_trace_weighted_basis {d : ℕ} (A D U : Mat d d) (μ : Fin d → ℝ)
    (hA : Aᵀ = A) (hU : Uᵀ * U = 1)
    (heig : ∀ i, A *ᵥ (fun k => U k i) = μ i • (fun k => U k i)) :
    (A * D).trace = ∑ i, μ i * ((fun k => U k i) ⬝ᵥ (D *ᵥ (fun k => U k i))) := by
  rw [mm_trace_basis (A * D) U hU]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA,
    heig i, smul_dotProduct, smul_eq_mul]

private lemma mm_abs_trace_mul {d : ℕ} (A D : Mat d d) :
    |(A * D).trace| ≤ (d : ℝ) * opNorm A * opNorm D := by
  have htrace : |(A * D).trace| ≤ (d : ℝ) * opNorm (A * D) := by
    calc |(A * D).trace| ≤ ∑ i, |(A * D) i i| := by
          simpa [Matrix.trace] using Finset.abs_sum_le_sum_abs (fun i => (A * D) i i) Finset.univ
      _ ≤ ∑ i : Fin d, opNorm (A * D) := Finset.sum_le_sum fun i _ => by
          have h := mm_quad_le (A * D) (Pi.single i 1) (by simp only [single_dotProduct, Pi.single_eq_same, one_mul])
          simpa only [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] using h
      _ = _ := by simp
  have hmul : opNorm (A * D) ≤ opNorm A * opNorm D := by
    open scoped Matrix.Norms.L2Operator in
    simpa only [opNorm_eq_norm] using Matrix.l2_opNorm_mul A D
  exact htrace.trans (by nlinarith [mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg d : (0:ℝ) ≤ d)])

private lemma mm_total_trace_bound {d B : ℕ} (A D : Mat d d) {γ CS e : ℝ}
    (hB : 0 < B) (hd : (d : ℝ) ≤ γ * B) (hA : opNorm A ≤ CS)
    (hD : opNorm D ≤ e) :
    |(B : ℝ)⁻¹ * (A * D).trace| ≤ γ * CS * e := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hCS := (mm_opNorm_nonneg A).trans hA
  have he := (mm_opNorm_nonneg D).trans hD
  have hγB : 0 ≤ γ * B := (Nat.cast_nonneg d : (0:ℝ) ≤ d).trans hd
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hB'.le)]
  calc (B : ℝ)⁻¹ * |(A * D).trace|
      ≤ (B : ℝ)⁻¹ * ((d : ℝ) * opNorm A * opNorm D) :=
        mul_le_mul_of_nonneg_left (mm_abs_trace_mul A D) (by positivity)
    _ ≤ (B : ℝ)⁻¹ * ((γ * B) * CS * e) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (mul_le_mul hd hA (mm_opNorm_nonneg A) hγB) hD
        (mm_opNorm_nonneg D) (mul_nonneg hγB hCS)
    _ = γ * CS * e := by field_simp

private lemma mm_diag_trace {d : ℕ} (U D : Mat d d) (hU : Uᵀ * U = 1)
    (a : Fin d → ℝ) :
    (U * Matrix.diagonal a * Uᵀ * D).trace =
      ∑ i, a i * ((fun k => U k i) ⬝ᵥ (D *ᵥ (fun k => U k i))) := by
  apply mm_trace_weighted_basis _ D U a
  · simp [Matrix.transpose_mul, Matrix.mul_assoc]
  · exact hU
  · apply mm_eig_vec
    simp [Matrix.mul_assoc, hU]

private lemma mm_trace_half_out {m n B : ℕ} (F : FrozenParams m n B)
    (S : SpectralData F.C) (a : Fin m → ℝ) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    (S.uOut * Matrix.diagonal a * S.uOutᵀ * halfGramOut F ϱ).trace =
      ∑ i, a i * volraw F.β (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) (S.μ i) ϱ := by
  rw [mm_diag_trace _ _ S.huOut]
  refine Finset.sum_congr rfl fun i _ => congrArg (a i * ·) ?_
  exact mm_halfGram_eig F.C.Sout F.C.psdOut
    (mm_branch_nonneg _ _ _ _).1 hϱ _ (mm_col_dot _ S.huOut i) (S.eigOut i)

private lemma mm_trace_half_in {m n B : ℕ} (F : FrozenParams m n B)
    (S : SpectralData F.C) (b : Fin n → ℝ) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    (S.vIn * Matrix.diagonal b * S.vInᵀ * halfGramIn F ϱ).trace =
      ∑ j, b j * volTildeZero F.β (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) (S.lam j) ϱ := by
  rw [mm_diag_trace _ _ S.hvIn]
  refine Finset.sum_congr rfl fun j _ => congrArg (b j * ·) ?_
  exact mm_halfGram_eig F.C.Sin F.C.psdIn
    (mm_branch_nonneg _ _ _ _).2 hϱ _ (mm_col_dot _ S.hvIn j) (S.eigIn j)

private lemma mm_raw_bounds {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (Sp : SpectralData F.C) (γ CS ϱ : ℝ)
    (hS : SizeFin F.C B γ CS) (hϱ : 0 < ϱ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ j, |b j| ≤ 1) (eO eI : ℝ)
    (hO : opNorm (expRes (emaW F.β) F S 0 ϱ -
      Rbar (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) F.C ϱ) ≤ eO)
    (hI : opNorm (expResT (emaW F.β) F S 0 ϱ -
      Rtbar (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) F.C ϱ) ≤ eI) :
    |(∫ ω, contraction B (Sp.uOut * Matrix.diagonal a * Sp.uOutᵀ) 1
        (omegaF ϱ) (omegaF ϱ) (frozenBuf F S 0 ω) (frozenBuf F S 0 ω) ∂P) -
      (B : ℝ)⁻¹ * ∑ i, a i * volraw F.β (Muon.Drift.specOutFM F)
        (Muon.Drift.specInFM F) (Sp.μ i) ϱ| ≤ γ * ϱ * eO ∧
    |(∫ ω, contraction B 1 (Sp.vIn * Matrix.diagonal b * Sp.vInᵀ)
        (omegaF ϱ) (omegaF ϱ) (frozenBuf F S 0 ω) (frozenBuf F S 0 ω) ∂P) -
      (B : ℝ)⁻¹ * ∑ j, b j * volTildeZero F.β (Muon.Drift.specOutFM F)
        (Muon.Drift.specInFM F) (Sp.lam j) ϱ| ≤ γ * ϱ * eI := by
  have hMO := thm_app_vol_half_same_i_out F S 0 ϱ ϱ eO hϱ
    (fun s hs => by have : s = ϱ := le_antisymm hs.2 hs.1; subst s; exact hO) ϱ ⟨le_rfl, le_rfl⟩
  have hMI := thm_app_vol_half_same_i_in F S 0 ϱ ϱ eI hϱ
    (fun s hs => by have : s = ϱ := le_antisymm hs.2 hs.1; subst s; exact hI) ϱ ⟨le_rfl, le_rfl⟩
  have hdimO : (m : ℝ) ≤ γ * B := (show (m : ℝ) ≤ (max m n : ℕ) by exact_mod_cast le_max_left m n).trans hS.1
  have hdimI : (n : ℝ) ≤ γ * B := (show (n : ℝ) ≤ (max m n : ℕ) by exact_mod_cast le_max_right m n).trans hS.1
  constructor
  · have hr : (∫ ω, contraction B (Sp.uOut * Matrix.diagonal a * Sp.uOutᵀ) 1
          (omegaF ϱ) (omegaF ϱ) (frozenBuf F S 0 ω) (frozenBuf F S 0 ω) ∂P) =
        (B : ℝ)⁻¹ * (Sp.uOut * Matrix.diagonal a * Sp.uOutᵀ *
          Muon.mean P (fun ω => frozenUpd F S ϱ 0 ω * (frozenUpd F S ϱ 0 ω)ᵀ)).trace := by
      simp only [contraction, eqn_app_vol_filters_sharp_ii hϱ, Matrix.mul_one]
      rw [integral_const_mul]
      congr 1
      simpa only [frozenUpd, Matrix.mul_assoc] using
        (mm_int_trace_mul (Sp.uOut * Matrix.diagonal a * Sp.uOutᵀ) _
          (mm_upd_gram_int F S hϱ 0).1).2
    rw [hr, ← mm_trace_half_out F Sp a hϱ, ← mul_sub, ← Matrix.trace_sub, ← Matrix.mul_sub]
    simpa only [mul_one, mul_assoc] using
      mm_total_trace_bound (B := B) _ _ F.hB hdimO
        (md_opNorm_conj _ Sp.huOut a ha) hMO
  · have hc : ∀ ω, (frozenUpd F S ϱ 0 ω * (Sp.vIn * Matrix.diagonal b * Sp.vInᵀ) *
        (frozenUpd F S ϱ 0 ω)ᵀ).trace =
        ((Sp.vIn * Matrix.diagonal b * Sp.vInᵀ) *
          ((frozenUpd F S ϱ 0 ω)ᵀ * frozenUpd F S ϱ 0 ω)).trace := by
      intro ω
      rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm
        ((frozenUpd F S ϱ 0 ω)ᵀ * frozenUpd F S ϱ 0 ω)]
    have hr : (∫ ω, contraction B 1 (Sp.vIn * Matrix.diagonal b * Sp.vInᵀ)
          (omegaF ϱ) (omegaF ϱ) (frozenBuf F S 0 ω) (frozenBuf F S 0 ω) ∂P) =
        (B : ℝ)⁻¹ * (Sp.vIn * Matrix.diagonal b * Sp.vInᵀ *
          Muon.mean P (fun ω => (frozenUpd F S ϱ 0 ω)ᵀ * frozenUpd F S ϱ 0 ω)).trace := by
      simp only [contraction, eqn_app_vol_filters_sharp_ii hϱ, Matrix.one_mul]
      change (∫ ω, (B : ℝ)⁻¹ * (frozenUpd F S ϱ 0 ω *
        (Sp.vIn * Matrix.diagonal b * Sp.vInᵀ) * (frozenUpd F S ϱ 0 ω)ᵀ).trace ∂P) = _
      simp_rw [hc]
      rw [integral_const_mul, (mm_int_trace_mul _ _ (mm_upd_gram_int F S hϱ 0).2).2]
    rw [hr, ← mm_trace_half_in F Sp b hϱ, ← mul_sub, ← Matrix.trace_sub, ← Matrix.mul_sub]
    simpa only [mul_one, mul_assoc] using
      mm_total_trace_bound (B := B) _ _ F.hB hdimI
        (md_opNorm_conj _ Sp.hvIn b hb) hMI

private lemma mm_sup_singleton (f : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ f x) :
    (⨆ s ∈ ({x} : Set ℝ), f s) = f x := by
  have hb : ∀ s : ℝ, (⨆ (_ : s ∈ ({x} : Set ℝ)), f s) ≤ f x := by
    intro s
    by_cases hs : s ∈ ({x} : Set ℝ)
    · rw [ciSup_pos hs]
      rcases hs with rfl
      exact le_rfl
    · rw [ciSup_neg hs]
      simpa only [Real.sSup_empty] using hx
  apply le_antisymm (ciSup_le hb)
  have h := le_ciSup (show BddAbove (Set.range (fun s : ℝ => ⨆ (_ : s ∈ ({x} : Set ℝ)), f s))
    from ⟨f x, by rintro _ ⟨s, rfl⟩; exact hb s⟩) x
  simpa only [ciSup_pos (Set.mem_singleton x)] using h

private lemma mm_marginal_approx (cert : Muon.External.GaussianOpNorm) (R : SetupRegime)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (Sp : ∀ k, SpectralData (R.F k).C) (ϱ : ℝ) (hϱ : ϱ ∈ Icc R.ϱlo R.ϱhi)
    (a : ∀ k, Fin (R.m k) → ℝ) (b : ∀ k, Fin (R.n k) → ℝ)
    (ha : ∀ k i, |a k i| ≤ 1) (hb : ∀ k j, |b k j| ≤ 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      |lagResp cert R.γstar R.CSig (R.F k).β 0 (R.B k) (Sp k).μ (Sp k).lam
          (a k) (fun _ => 1) (omegaF ϱ) (omegaF ϱ) -
        (R.B k : ℝ)⁻¹ * ∑ i, a k i * volraw (R.F k).β (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) ((Sp k).μ i) ϱ| ≤ ε ∧
      |lagResp cert R.γstar R.CSig (R.F k).β 0 (R.B k) (Sp k).μ (Sp k).lam
          (fun _ => 1) (b k) (omegaF ϱ) (omegaF ϱ) -
        (R.B k : ℝ)⁻¹ * ∑ j, b k j * volTildeZero (R.F k).β (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) ((Sp k).lam j) ϱ| ≤ ε := by
  have hϱ0 : 0 < ϱ := R.hϱ.1.trans_le hϱ.1
  have hs : SizeSeq (B := R.B) (fun k => (R.F k).C) R.γstar R.CSig R.prop.γout R.prop.γin :=
    ⟨fun k => ⟨R.dims k, R.normOut k, R.normIn k⟩, R.prop.B_top,
      R.prop.ratio_in, R.prop.ratio_out⟩
  let eo : ℕ → ℝ := fun k => opNorm (expRes (emaW (R.F k).β) (R.F k) (S k) 0 ϱ -
    Rbar (Fw (emaW (R.F k).β)) (Muon.Drift.specOutFM (R.F k))
      (Muon.Drift.specInFM (R.F k)) (R.F k).C ϱ)
  let ei : ℕ → ℝ := fun k => opNorm (expResT (emaW (R.F k).β) (R.F k) (S k) 0 ϱ -
    Rtbar (Fw (emaW (R.F k).β)) (Muon.Drift.specOutFM (R.F k))
      (Muon.Drift.specInFM (R.F k)) (R.F k).C ϱ)
  have hgram : Tendsto (fun k => eo k + ei k) atTop (𝓝 0) := by
    have h := thm_app_de_gram R (emaW R.β) (Muon.Drift.emaW_weightClass_regime R) P S
      (fun k => Muon.Drift.specOutFM (R.F k)) (fun k => Muon.Drift.specInFM (R.F k))
      (fun _ => rfl) (fun _ => rfl) 0 {ϱ} (isCompact_singleton)
      (by intro x hx; rcases hx with rfl; exact hϱ0)
    have heq : ∀ k, (⨆ s ∈ ({ϱ} : Set ℝ),
        opNorm (expRes (emaW R.β) (R.F k) (S k) 0 s -
          Rbar (Fw (emaW R.β)) (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) (R.F k).C s) +
        opNorm (expResT (emaW R.β) (R.F k) (S k) 0 s -
          Rtbar (Fw (emaW R.β)) (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) (R.F k).C s)) = eo k + ei k := by
      intro k
      rw [mm_sup_singleton]
      · simp only [eo, ei, R.hβ]
      · exact add_nonneg (mm_opNorm_nonneg _) (mm_opNorm_nonneg _)
    simpa only [heq] using h
  obtain ⟨δ, hδ, hrep⟩ := cor_app_vol_filtered_replacement_i R P S
  have htot : Tendsto (fun k => δ k + R.γstar * ϱ * (eo k + ei k)) atTop (𝓝 0) := by
    simpa using hδ.add (hgram.const_mul (R.γstar * ϱ))
  intro ε hε
  have hc := lag_closure_generic cert R.γstar R.CSig R.prop.γout R.prop.γin R.hC
    R.m R.n R.B R.F Sp hs R.β (by rw [← R.hβ 0]; exact (R.F 0).hβ.2) (fun k => (R.hβ k).le)
    0 (omegaF ϱ) (omegaF ϱ)
      (lem_app_vol_sharp_ii hϱ0 hϱ0).2.1 (lem_app_vol_sharp_ii hϱ0 hϱ0).2.1
      (ε / 3) (by positivity)
  have ht := (tendsto_order.1 htot).2 (2 * ε / 3) (by positivity)
  filter_upwards [hc, ht] with k hck htk
  let Fo := (Sp k).uOut * Matrix.diagonal (a k) * (Sp k).uOutᵀ
  let Gi := (Sp k).vIn * Matrix.diagonal (b k) * (Sp k).vInᵀ
  have hFo : opNorm Fo ≤ 1 := md_opNorm_conj _ (Sp k).huOut _ (ha k)
  have hGi : opNorm Gi ≤ 1 := md_opNorm_conj _ (Sp k).hvIn _ (hb k)
  have ho : (Sp k).uOut * Matrix.diagonal (fun _ => (1 : ℝ)) * (Sp k).uOutᵀ = 1 := by
    simpa using mul_eq_one_comm.mp (Sp k).huOut
  have hi : (Sp k).vIn * Matrix.diagonal (fun _ => (1 : ℝ)) * (Sp k).vInᵀ = 1 := by
    simpa using mul_eq_one_comm.mp (Sp k).hvIn
  have hOneO : opNorm (1 : Mat (R.m k) (R.m k)) ≤ 1 := by
    rw [← ho]; exact md_opNorm_conj _ (Sp k).huOut _ (by simp)
  have hOneI : opNorm (1 : Mat (R.n k) (R.n k)) ≤ 1 := by
    rw [← hi]; exact md_opNorm_conj _ (Sp k).hvIn _ (by simp)
  have hro := hrep 0 0 k ϱ ϱ hϱ hϱ Fo hFo 1 hOneI
  have hri := hrep 0 0 k ϱ ϱ hϱ hϱ 1 hOneO Gi hGi
  have hco := hck 0 (a k) (fun _ => 1) Fo 1 rfl hi.symm hFo hOneI
  have hci := hck 0 (fun _ => 1) (b k) 1 Gi ho.symm rfl hOneO hGi
  have hr := mm_raw_bounds (R.F k) (S k) (Sp k) R.γstar R.CSig ϱ (hs.1 k) hϱ0
    (a k) (b k) (ha k) (hb k) (eo k) (ei k) le_rfl le_rfl
  have hγ : 0 ≤ R.γstar := (md_sizefin_pos (R.F k) R.γstar R.CSig (hs.1 k)).le
  have heo : R.γstar * ϱ * eo k ≤ R.γstar * ϱ * (eo k + ei k) := by
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mm_opNorm_nonneg _)) (by positivity)
  have hei : R.γstar * ϱ * ei k ≤ R.γstar * ϱ * (eo k + ei k) := by
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (mm_opNorm_nonneg _)) (by positivity)
  simp only [Nat.cast_zero, add_zero] at hro hri hco hci
  constructor
  · have ht1 := abs_sub_le
      (lagResp cert R.γstar R.CSig (R.F k).β 0 (R.B k) (Sp k).μ (Sp k).lam
        (a k) (fun _ => 1) (omegaF ϱ) (omegaF ϱ))
      (∫ ω, contraction (R.B k) Fo 1 (omegaF ϱ) (omegaF ϱ)
        (def_app_vol_product (R.F k) ω 0) (def_app_vol_product (R.F k) ω 0)
        ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k)))
      ((R.B k : ℝ)⁻¹ * ∑ i, a k i * volraw (R.F k).β (Muon.Drift.specOutFM (R.F k))
        (Muon.Drift.specInFM (R.F k)) ((Sp k).μ i) ϱ)
    have ht2 := abs_sub_le
      (∫ ω, contraction (R.B k) Fo 1 (omegaF ϱ) (omegaF ϱ)
        (def_app_vol_product (R.F k) ω 0) (def_app_vol_product (R.F k) ω 0)
        ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k)))
      (∫ ω, contraction (R.B k) Fo 1 (omegaF ϱ) (omegaF ϱ)
        (frozenBuf (R.F k) (S k) 0 ω) (frozenBuf (R.F k) (S k) 0 ω) ∂(P k))
      ((R.B k : ℝ)⁻¹ * ∑ i, a k i * volraw (R.F k).β (Muon.Drift.specOutFM (R.F k))
        (Muon.Drift.specInFM (R.F k)) ((Sp k).μ i) ϱ)
    rw [abs_sub_comm] at hco hro
    dsimp only [Fo] at *
    linarith [hr.1]
  · have ht1 := abs_sub_le
      (lagResp cert R.γstar R.CSig (R.F k).β 0 (R.B k) (Sp k).μ (Sp k).lam
        (fun _ => 1) (b k) (omegaF ϱ) (omegaF ϱ))
      (∫ ω, contraction (R.B k) 1 Gi (omegaF ϱ) (omegaF ϱ)
        (def_app_vol_product (R.F k) ω 0) (def_app_vol_product (R.F k) ω 0)
        ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k)))
      ((R.B k : ℝ)⁻¹ * ∑ j, b k j * volTildeZero (R.F k).β (Muon.Drift.specOutFM (R.F k))
        (Muon.Drift.specInFM (R.F k)) ((Sp k).lam j) ϱ)
    have ht2 := abs_sub_le
      (∫ ω, contraction (R.B k) 1 Gi (omegaF ϱ) (omegaF ϱ)
        (def_app_vol_product (R.F k) ω 0) (def_app_vol_product (R.F k) ω 0)
        ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k)))
      (∫ ω, contraction (R.B k) 1 Gi (omegaF ϱ) (omegaF ϱ)
        (frozenBuf (R.F k) (S k) 0 ω) (frozenBuf (R.F k) (S k) 0 ω) ∂(P k))
      ((R.B k : ℝ)⁻¹ * ∑ j, b k j * volTildeZero (R.F k).β (Muon.Drift.specOutFM (R.F k))
        (Muon.Drift.specInFM (R.F k)) ((Sp k).lam j) ϱ)
    rw [abs_sub_comm] at hci hri
    dsimp only [Gi] at *
    linarith [hr.2]

private lemma mm_repl_sum {d : ℕ} (N B : ℕ) (hN : 0 < N) (hB : 0 < B)
    (a μ : Fin d → ℝ) (v : ℝ → ℝ) :
    ((N * B : ℕ) : ℝ)⁻¹ * ∑ i, replVec N a i * v (replVec N μ i) =
      (B : ℝ)⁻¹ * ∑ i, a i * v (μ i) := by
  rw [← Equiv.sum_comp (replIdx d N) (fun i => replVec N a i * v (replVec N μ i))]
  simp only [replVec, Equiv.symm_apply_apply, Fintype.sum_prod_type_right,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  field_simp

private lemma mm_marginal_identity (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut Fp.C B) (hν' : (ν' : Measure ℝ) = Muon.nuIn Fp.C B)
    (ϱ : ℝ) (hϱ : 0 < ϱ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ j, |b j| ≤ 1) :
    lagResp cert γstar CSig Fp.β 0 B S.μ S.lam a (fun _ => 1) (omegaF ϱ) (omegaF ϱ) =
      (B : ℝ)⁻¹ * ∑ i, a i * volraw Fp.β ν ν' (S.μ i) ϱ ∧
    lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (fun _ => 1) b (omegaF ϱ) (omegaF ϱ) =
      (B : ℝ)⁻¹ * ∑ j, b j * volTildeZero Fp.β ν ν' (S.lam j) ϱ := by
  obtain ⟨hm, hn⟩ := mm_pos_of_fro Fp.A Fp.hA
  obtain ⟨R, hmR, hnR, hBR, hγR, hCR, hβR, hloR, hhiR, hR⟩ :=
    def_app_vol_replication_regime Fp S γstar CSig ϱ ϱ hCSig hS hm hn ⟨hϱ, le_rfl⟩
  rcases R with ⟨rm, rn, rB, rF, rprop, rγ, rC, rhC, rdims, rnormO, rnormI,
    rβ, rhβ, rlo, rhi, rhϱ, rdiff⟩
  dsimp only at hmR hnR hBR hγR hCR hβR hloR hhiR hR
  subst rm rn rB rγ rC rβ rlo rhi
  let R : SetupRegime := ⟨_, _, _, rF, rprop, γstar, CSig, rhC, rdims, rnormO, rnormI,
    Fp.β, rhβ, ϱ, ϱ, rhϱ, rdiff⟩
  have hCov : ∀ k, (rF k).C = replCov Fp.C (k + 1) := fun k => eq_of_heq (hR k).1
  have hspec : ∀ k, ∃ Sp : SpectralData (rF k).C,
      Sp.μ = replVec (k + 1) S.μ ∧ Sp.lam = replVec (k + 1) S.lam := by
    intro k
    rw [hCov k]
    obtain ⟨Sp, -, -, hμ, hl⟩ := mm_exists_replSpec Fp.C S (k + 1)
    exact ⟨Sp, hμ, hl⟩
  choose Sp hμ hl using hspec
  have hνO : ∀ k, Muon.Drift.specOutFM (rF k) = ν := by
    intro k
    apply FiniteMeasure.toMeasure_injective
    change Muon.nuOut (rF k).C ((k + 1) * B) = (ν : Measure ℝ)
    rw [hCov k, def_app_vol_replication_i Fp.C Fp.hB (k + 1) (Nat.succ_pos k), hν]
  have hνI : ∀ k, Muon.Drift.specInFM (rF k) = ν' := by
    intro k
    apply FiniteMeasure.toMeasure_injective
    change Muon.nuIn (rF k).C ((k + 1) * B) = (ν' : Measure ℝ)
    rw [hCov k, def_app_vol_replication_ii Fp.C Fp.hB (k + 1) (Nat.succ_pos k), hν']
  let Ω : ℕ → Type := fun k => (ℤ × Fin (R.B k)) → Vec (R.m k) × Vec (R.n k)
  let P : ∀ k, Measure (Ω k) := fun k => Measure.infinitePi fun _ : ℤ × Fin (R.B k) =>
    (Muon.Foundations.stdGaussianPi (R.m k)).prod (Muon.Foundations.stdGaussianPi (R.n k))
  let samples : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k) := fun k =>
    (frozenSamples_nonempty (R.m k) (R.n k) (R.B k)).some
  have happ := mm_marginal_approx cert R P samples Sp ϱ ⟨le_rfl, le_rfl⟩
    (fun k => replVec (k + 1) a) (fun k => replVec (k + 1) b)
    (fun k i => ha _) (fun k j => hb _)
  have hrepl := (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hCSig
    0 (omegaF ϱ) (omegaF ϱ) (lem_app_vol_sharp_ii hϱ hϱ).2.1
      (lem_app_vol_sharp_ii hϱ hϱ).2.1).2.2.2.2.2
  have hsmall : ∀ ε : ℝ, 0 < ε →
      |lagResp cert γstar CSig Fp.β 0 B S.μ S.lam a (fun _ => 1) (omegaF ϱ) (omegaF ϱ) -
        (B : ℝ)⁻¹ * ∑ i, a i * volraw Fp.β ν ν' (S.μ i) ϱ| ≤ ε ∧
      |lagResp cert γstar CSig Fp.β 0 B S.μ S.lam (fun _ => 1) b (omegaF ϱ) (omegaF ϱ) -
        (B : ℝ)⁻¹ * ∑ j, b j * volTildeZero Fp.β ν ν' (S.lam j) ϱ| ≤ ε := by
    intro ε hε
    obtain ⟨k, hk⟩ := (happ ε hε).exists
    change _ ∧ _ at hk
    dsimp only [R] at hk
    rw [rhβ k, hμ k, hl k, hνO k, hνI k,
      mm_repl_sum (k + 1) B (Nat.succ_pos k) Fp.hB a S.μ (fun x => volraw Fp.β ν ν' x ϱ),
      mm_repl_sum (k + 1) B (Nat.succ_pos k) Fp.hB b S.lam (fun x => volTildeZero Fp.β ν ν' x ϱ)] at hk
    have ho := hrepl (k + 1) (Nat.succ_pos k) a (fun _ => 1)
    have hi := hrepl (k + 1) (Nat.succ_pos k) (fun _ => 1) b
    change lagResp _ _ _ _ _ _ _ _ _ (fun _ => 1) _ _ = _ at ho
    change lagResp _ _ _ _ _ _ _ _ (fun _ => 1) _ _ _ = _ at hi
    rwa [ho, hi] at hk
  constructor
  · apply sub_eq_zero.mp
    exact abs_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add
      (fun ε hε => by simpa using (hsmall ε hε).1)) (abs_nonneg _))
  · apply sub_eq_zero.mp
    exact abs_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add
      (fun ε hε => by simpa using (hsmall ε hε).2)) (abs_nonneg _))

/-! ## Measures on `ℝ × ℝ`: integrals, total variation, bounded-Lipschitz tests -/

/-- `∫ φ dm` for a finitely supported signed measure `m` on `ℝ × ℝ` (the sum over atoms). The
integrals of `eqn:app-vol-measures` are finite sums (`pairMeasure`). -/
def finInt (m : (ℝ × ℝ) →₀ ℝ) (φ : ℝ × ℝ → ℝ) : ℝ :=
  m.sum fun p v => v * φ p

/-- Total variation `‖m‖_TV` of a finitely supported signed measure: the sum of the absolute
atoms (`eqn:app-vol-measures` and the TV norm of `thm:app-vol-joint-forcing`). -/
def finTV (m : (ℝ × ℝ) →₀ ℝ) : ℝ :=
  m.sum fun _ v => |v|

private lemma mm_pairMeasure_apply (xs ys : Finset ℝ) (v : ℝ → ℝ → ℝ) (x y : ℝ) :
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

private lemma mm_classDiag_psd {d : ℕ} (U : Mat d d) (x : Fin d → ℝ) (a : ℝ) :
    (U * Matrix.diagonal (classDiag x a) * Uᵀ).PosSemidef := by
  have hd : (Matrix.diagonal (classDiag x a)).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    by_cases h : x i = a <;> simp [classDiag, h]
  have := hd.mul_mul_conjTranspose_same U
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this

private lemma mm_measureZeta_nonneg (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ϱ : ℝ) (hϱ : 0 < ϱ)
    (μ l : ℝ) : 0 ≤ measureZeta cert γstar CSig Fp S ϱ (μ, l) := by
  rw [measureZeta, mm_pairMeasure_apply]
  split_ifs
  · exact (thm_app_vol_integrated_iii cert γstar CSig Fp S hS hCSig
      (S.uOut * Matrix.diagonal (classDiag S.μ μ) * S.uOutᵀ)
      (S.vIn * Matrix.diagonal (classDiag S.lam l) * S.vInᵀ)
      (classDiag S.μ μ) (classDiag S.lam l) rfl rfl ϱ ϱ ⟨hϱ, le_rfl⟩
      ϱ ϱ ⟨le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl⟩).2
      (mm_classDiag_psd S.uOut S.μ μ) (mm_classDiag_psd S.vIn S.lam l)
  · exact le_rfl

private lemma mm_class_card_pos {d : ℕ} (x : Fin d → ℝ) (i : Fin d) :
    0 < ((Finset.univ.filter fun k => x k = x i).card : ℝ) := by
  exact_mod_cast Finset.card_pos.mpr ⟨i, by simp⟩

private lemma mm_modeVij_nonneg (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ϱ : ℝ) (hϱ : 0 < ϱ)
    (i : Fin m) (j : Fin n) : 0 ≤ modeVij cert γstar CSig Fp S ϱ i j := by
  unfold modeVij
  exact div_nonneg
    (mul_nonneg (Nat.cast_nonneg B)
      (mm_measureZeta_nonneg cert γstar CSig Fp S hS hCSig ϱ hϱ (S.μ i) (S.lam j)))
    (mul_nonneg (mm_class_card_pos S.μ i).le (mm_class_card_pos S.lam j).le)

private lemma mm_modeVij_eq_of_eigs (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (ϱ : ℝ)
    (i i' : Fin m) (j j' : Fin n) (hi : S.μ i = S.μ i') (hj : S.lam j = S.lam j') :
    modeVij cert γstar CSig Fp S ϱ i j = modeVij cert γstar CSig Fp S ϱ i' j' := by
  unfold modeVij
  rw [hi, hj]

private lemma mm_finTV_pairMeasure (xs ys : Finset ℝ) (v : ℝ → ℝ → ℝ) :
    finTV (pairMeasure xs ys v) = ∑ x ∈ xs, ∑ y ∈ ys, |v x y| := by
  classical
  have hsupp : (pairMeasure xs ys v).support ⊆ xs.product ys := by
    intro p hp
    rw [Finsupp.mem_support_iff] at hp
    by_contra hn
    have hn' : ¬(p.1 ∈ xs ∧ p.2 ∈ ys) := by simpa using hn
    exact hp (by simpa [mm_pairMeasure_apply, hn'] using
      (mm_pairMeasure_apply xs ys v p.1 p.2))
  unfold finTV
  rw [Finsupp.sum_of_support_subset _ hsupp _ (fun _ _ => by simp)]
  change (Finset.product xs ys).sum (fun p => |pairMeasure xs ys v p|) = _
  rw [show xs.product ys = (xs ×ˢ ys : Finset (ℝ × ℝ)) from rfl]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [mm_pairMeasure_apply]
  simp [hx, hy]

private lemma mm_finTV_eq_finInt_one {m : (ℝ × ℝ) →₀ ℝ} (hm : ∀ p, 0 ≤ m p) :
    finTV m = finInt m (fun _ => 1) := by
  unfold finTV finInt
  apply Finsupp.sum_congr
  intro p hp
  rw [abs_of_nonneg (hm p)]
  ring

private lemma mm_finTV_nonneg (m : (ℝ × ℝ) →₀ ℝ) : 0 ≤ finTV m := by
  unfold finTV
  exact Finsupp.sum_nonneg fun _ _ => abs_nonneg _

private lemma mm_abs_add_tsum_le (x : ℝ) (f : ℕ → ℝ) (hf : Summable fun q => |f q|) :
    |x + ∑' q, f q| ≤ |x| + ∑' q, |f q| := by
  have h₁ : |x + ∑' q, f q| ≤ |x| + |∑' q, f q| := abs_add_le _ _
  have h₂ : |∑' q, f q| ≤ ∑' q, |f q| := by
    have hn : Summable fun q => ‖f q‖ := by simpa only [Real.norm_eq_abs] using hf
    have := norm_tsum_le_tsum_norm hn
    simpa only [Real.norm_eq_abs] using this
  exact h₁.trans (add_le_add le_rfl h₂)

/-- Bridge (proof card P8): the atomic total variation `finTV` equals the project's total
variation functional `Muon.Dynamics.tvNorm` applied to the integral functional `finInt m`. -/
theorem finTV_eq_tvNorm (m : (ℝ × ℝ) →₀ ℝ) : finTV m = Muon.Dynamics.tvNorm (finInt m) := by
  have hbound : ∀ φ : ℝ × ℝ → ℝ, (∀ x, |φ x| ≤ 1) → |finInt m φ| ≤ finTV m := by
    intro φ hφ
    unfold finInt finTV
    change |∑ p ∈ m.support, m p * φ p| ≤ ∑ p ∈ m.support, |m p|
    calc
      |∑ p ∈ m.support, m p * φ p| ≤ ∑ p ∈ m.support, |m p * φ p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ m.support, |m p| := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul]
        calc
          |m p| * |φ p| ≤ |m p| * 1 := mul_le_mul_of_nonneg_left (hφ p) (abs_nonneg _)
          _ = |m p| := mul_one _
  let s : ℝ × ℝ → ℝ := fun p => if 0 ≤ m p then 1 else -1
  have hs_meas : Measurable s := by
    apply (measurable_const : Measurable (fun _ : ℝ × ℝ => (1 : ℝ))).measurable_of_countable_ne
    refine m.support.finite_toSet.countable.mono ?_
    intro p hp
    simp only [s] at hp
    by_contra hn
    have hm0 : m p = 0 := Finsupp.notMem_support_iff.mp hn
    simp [hm0] at hp
  have hs_one : ∀ p, |s p| ≤ 1 := by
    intro p
    simp only [s]
    split_ifs <;> simp
  have hattain : |finInt m s| = finTV m := by
    have hi : finInt m s = finTV m := by
      unfold finInt finTV
      apply Finsupp.sum_congr
      intro p hp
      simp only [s]
      split_ifs with h
      · rw [abs_of_nonneg h]
        ring
      · rw [abs_of_neg (not_le.mp h)]
        ring
    rw [hi, abs_of_nonneg (mm_finTV_nonneg m)]
  unfold Muon.Dynamics.tvNorm
  apply le_antisymm
  · rw [← hattain]
    apply le_csSup
    · refine ⟨finTV m, ?_⟩
      intro b hb
      rcases hb with ⟨φ, ⟨hφm, hφ⟩, rfl⟩
      exact hbound φ hφ
    · exact ⟨s, ⟨hs_meas, hs_one⟩, rfl⟩
  · apply csSup_le
    · refine ⟨0, ?_⟩
      refine ⟨fun _ => 0, ?_, ?_⟩
      · exact ⟨measurable_const, fun x => by simp⟩
      · simp [finInt]
    · intro b hb
      rcases hb with ⟨φ, ⟨hφm, hφ⟩, rfl⟩
      exact hbound φ hφ

/-! ## The finite-time measure `𝔉_T` -/

/-- Atomic form of the finite-time measure `𝔉_T(ϱ)` displayed inside `thm:app-vol-joint-forcing`
(snapshot `cr-2026-10-23`, source l.2882–2884):

\[
\mathfrak F_T(\ridge)\defeq\frac1{BT}\sum_{i,j}\EE\Big(\sum_{t'=1}^T({\mathsf S}^{\mathrm c}_{t'}(\ridge))_{ij}\Big)^2\,\delta_{(\mu_i,\lambda_j)}
\]

Its atoms are `(1/(BT)) 𝔼 (∑_{t'=1}^T (S^c_{t'}(ϱ))_{ij})²` at `(μ_i, λ_j)` in the eigenbases
of `SP` (the entries of `SP.uOutᵀ · · SP.vIn`, as in `modeVijActual`), summed over `i, j`. -/
def finiteTimeMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (SP : SpectralData F.C) (T : ℕ) (ϱ : ℝ) :
    (ℝ × ℝ) →₀ ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, Finsupp.single (SP.μ i, SP.lam j)
    (((B : ℝ) * (T : ℝ))⁻¹ * (∫ ω,
      ((SP.uOutᵀ * (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), centredUpd F S ϱ s ω) * SP.vIn) i j) ^ 2 ∂P))

/-! ## The closed-form mode kernel (`eqn:app-vol-closed-mode-kernel`, `eqn:app-vol-closed-cl`) -/

/-- `𝔥_ℓ(μ,λ;s,u)` of `eqn:app-vol-closed-mode-kernel`, snapshot `cr-2026-10-23`. The branch
points of the EMA paired profile at lag `ℓ` (`emaXi₁`, `emaXi₂`) at `s` (first buffer) and `u`
(second buffer), `b_ℓ` and `Δ_ℓ` as in `profileDelta`. LaTeX, verbatim from `section.tex`:

\begin{equation}\label{eqn:app-vol-closed-mode-kernel}
\mathfrak h_\ell(\mu,\lambda;s,u)\defeq\frac{su\,\mu\lambda\,b_\ell(s,u)}{(s+\tilde s_1\mu)(u+\tilde s_1'\mu)(s+s_1\lambda)(u+s_1'\lambda)\,\Delta_\ell(s,u)},
\end{equation} -/
def closedModeH {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} (P : Measure Ω) (C : Muon.Covariances m n)
    (B : ℕ) (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (μ l s u : ℝ) : ℝ :=
  let ξ₁ := emaXi₁ β ℓ g
  let ξ₂ := emaXi₂ β ℓ g
  let x := branchPt (profileF P ξ₁) C B s
  let y := branchPt (profileF P ξ₂) C B u
  s * u * μ * l * pairedB P ξ₁ ξ₂ (s * x.1 * x.2.1) (u * y.1 * y.2.1) /
    ((s + x.2.2.1 * μ) * (u + y.2.2.1 * μ) * (s + x.2.2.2 * l) * (u + y.2.2.2 * l) *
      profileDelta P C B ξ₁ ξ₂ s u)

/-- `𝔠_ℓ(μ,λ;ϱ)` of `eqn:app-vol-closed-cl`, snapshot `cr-2026-10-23`: `(4/π²)` times the
integral of `𝔥_ℓ(μ,λ;ϱ+x²,ϱ+y²)` over `(0,∞)²`. LaTeX, verbatim from `section.tex`:

\begin{equation}\label{eqn:app-vol-closed-cl}
\mathfrak c_\ell(\mu,\lambda;\ridge)\defeq\frac4{\pi^2}\int_0^\infty\!\!\int_0^\infty\mathfrak h_\ell(\mu,\lambda;\ridge+x^2,\ridge+y^2)\,dx\,dy .
\end{equation} -/
def closedModeCl {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} (P : Measure Ω) (C : Muon.Covariances m n)
    (B : ℕ) (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (μ l ϱ : ℝ) : ℝ :=
  (4 / Real.pi ^ 2) * (∫ x in Set.Ioi (0 : ℝ),
    (∫ y in Set.Ioi (0 : ℝ), closedModeH P C B β ℓ g μ l (ϱ + x ^ 2) (ϱ + y ^ 2)))

/-! ## Same-step marginals (`cor:app-vol-marginals`) -/

/-- `cor:app-vol-marginals`, row and column test form (`eqn:app-vol-marginals-tests`), snapshot
`cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

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
\end{corollary} -/
theorem cor_app_vol_marginals_tests (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut Fp.C B) (hν' : (ν' : Measure ℝ) = Muon.nuIn Fp.C B)
    (ϱ : ℝ) (hϱ : 0 < ϱ) :
    (∀ i : Fin m, lagRowBar cert γstar CSig Fp.β 0 B S.μ S.lam i ϱ ϱ =
        volraw Fp.β ν ν' (S.μ i) ϱ) ∧
      (∀ j : Fin n, (B : ℝ) * lagResp cert γstar CSig Fp.β 0 B S.μ S.lam
          (fun _ : Fin m => (1 : ℝ)) (Pi.single j (1 : ℝ)) (omegaF ϱ) (omegaF ϱ) =
        volTildeZero Fp.β ν ν' (S.lam j) ϱ) := by
  have hB : (B : ℝ) ≠ 0 := by exact_mod_cast Fp.hB.ne'
  constructor
  · intro i
    have ha : ∀ k : Fin m, |(Pi.single i (1 : ℝ) : Fin m → ℝ) k| ≤ 1 := by
      intro k
      by_cases hk : k = i <;> simp [Pi.single_apply, hk]
    have h := (mm_marginal_identity cert γstar CSig Fp S hS hCSig ν ν' hν hν' ϱ hϱ
      (Pi.single i 1) (fun _ => 0) ha (by simp)).1
    simp only [lagRowBar]
    rw [h]
    simp [Pi.single_apply, hB]
  · intro j
    have hb : ∀ k : Fin n, |(Pi.single j (1 : ℝ) : Fin n → ℝ) k| ≤ 1 := by
      intro k
      by_cases hk : k = j <;> simp [Pi.single_apply, hk]
    have h := (mm_marginal_identity cert γstar CSig Fp S hS hCSig ν ν' hν hν' ϱ hϱ
      (fun _ => 0) (Pi.single j 1) (by simp) hb).2
    rw [h]
    simp [Pi.single_apply, hB]

/-! ## Private helpers for the mode-kernel limits (P-D.14.P5) -/

section PHelpers

private lemma mp_fro_sandwich {m n : ℕ} (F : Mat m m) (D : Mat m n) (G : Mat n n)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) : fro (F * D * G) ≤ fro D := by
  have h1 : opNorm F * fro D ≤ fro D := mul_le_of_le_one_left (mm_fro_nn D) hF
  calc fro (F * D * G) ≤ fro (F * D) * opNorm G := mm_fro_mul_le_right _ _
    _ ≤ (opNorm F * fro D) * opNorm G :=
        mul_le_mul_of_nonneg_right (mm_fro_mul_le_left _ _) (mm_opNorm_nonneg _)
    _ ≤ fro D * 1 := mul_le_mul h1 hG (mm_opNorm_nonneg G) (mm_fro_nn D)
    _ = fro D := mul_one _

private lemma mp_trace_mul_transpose_le {m n : ℕ} (X C : Mat m n) :
    |Matrix.trace (X * Cᵀ)| ≤ fro X * fro C := by
  have htr : Matrix.trace (X * Cᵀ) = ∑ p : Fin m × Fin n, X p.1 p.2 * C p.1 p.2 := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [htr]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
    (fun p => X p.1 p.2) (fun p => C p.1 p.2)
  have hX : ∑ p : Fin m × Fin n, X p.1 p.2 ^ 2 = fro X ^ 2 := by
    rw [mm_fro_sq, Fintype.sum_prod_type]
  have hC : ∑ p : Fin m × Fin n, C p.1 p.2 ^ 2 = fro C ^ 2 := by
    rw [mm_fro_sq, Fintype.sum_prod_type]
  rw [hX, hC] at cs
  refine (pow_le_pow_iff_left₀ (abs_nonneg _) (mul_nonneg (mm_fro_nn X) (mm_fro_nn C))
    two_ne_zero).mp ?_
  rw [sq_abs, mul_pow]
  exact cs

private lemma mp_tested_le {m n : ℕ} (Fo : Mat m m) (Gi : Mat n n) (hF : opNorm Fo ≤ 1)
    (hG : opNorm Gi ≤ 1) (X Y : Mat m n) :
    |Matrix.trace (Fo * X * Gi * Yᵀ)| ≤ fro X * fro Y :=
  (mp_trace_mul_transpose_le (Fo * X * Gi) Y).trans
    (mul_le_mul_of_nonneg_right (mp_fro_sandwich Fo X Gi hF hG) (mm_fro_nn Y))

private lemma mp_fro_le_of_entries {m n : ℕ} (K : Mat m n) (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ i j, |K i j| ≤ a) : fro K ≤ Real.sqrt ((m : ℝ) * n) * a := by
  have h1 : fro K ^ 2 ≤ ((m : ℝ) * n) * a ^ 2 := by
    rw [mm_fro_sq]
    calc ∑ i, ∑ j, K i j ^ 2 ≤ ∑ _i : Fin m, ∑ _j : Fin n, a ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
      _ = ((m : ℝ) * n) * a ^ 2 := by simp [mul_assoc]
  have h2 : Real.sqrt (((m : ℝ) * n) * a ^ 2) = Real.sqrt ((m : ℝ) * n) * a := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ha]
  rw [← h2]
  exact Real.le_sqrt_of_sq_le h1

private lemma mp_cen_aesm {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 < ϱ) (t : ℤ) : AEStronglyMeasurable (centredUpd F S ϱ t) P := by
  unfold centredUpd
  exact (mm_upd_aesm F S hϱ t).sub aestronglyMeasurable_const

private lemma mp_cen_fro_le {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 < ϱ) (t : ℤ) (ω : Ω) :
    fro (centredUpd F S ϱ t ω) ≤ Real.sqrt ((m : ℝ) * n) * (2 * ((m : ℝ) + 1)) := by
  refine mp_fro_le_of_entries _ _ (by positivity) fun i j => ?_
  have h1 : ∀ ω, |frozenUpd F S ϱ t ω i j| ≤ (m : ℝ) + 1 := fun ω =>
    (mm_abs_entry_le_fro _ i j).trans (mm_upd_fro_le F S hϱ t ω)
  have h2 : |mean P (frozenUpd F S ϱ t) i j| ≤ (m : ℝ) + 1 := by
    have h := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => frozenUpd F S ϱ t ω i j)
      (C := (m : ℝ) + 1)
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact h1 ω)
    simpa [mean, Real.norm_eq_abs] using h
  have := h1 ω
  simp only [centredUpd, Matrix.sub_apply]
  calc |frozenUpd F S ϱ t ω i j - mean P (frozenUpd F S ϱ t) i j|
      ≤ |frozenUpd F S ϱ t ω i j| + |mean P (frozenUpd F S ϱ t) i j| := abs_sub _ _
    _ ≤ 2 * ((m : ℝ) + 1) := by linarith

private lemma mp_trace_cont {m n : ℕ} (Fo : Mat m m) (Gi : Mat n n) :
    Continuous (fun p : Mat m n × Mat m n => Matrix.trace (Fo * p.1 * Gi * p.2ᵀ)) := by
  fun_prop

private lemma mp_trace_int {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ ϱ' : ℝ}
    (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') (s s' : ℤ) (Fo : Mat m m) (Gi : Mat n n)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1) :
    Integrable (fun ω => Matrix.trace (Fo * centredUpd F S ϱ s ω * Gi *
      (centredUpd F S ϱ' s' ω)ᵀ)) P := by
  have hc := mp_trace_cont (m := m) (n := n) Fo Gi
  have hm : AEStronglyMeasurable (fun ω => (centredUpd F S ϱ s ω, centredUpd F S ϱ' s' ω)) P :=
    (mp_cen_aesm F S hϱ s).prodMk (mp_cen_aesm F S hϱ' s')
  have hmeas := hc.comp_aestronglyMeasurable hm
  set D : ℝ := Real.sqrt ((m : ℝ) * n) * (2 * ((m : ℝ) + 1)) with hD
  have hD0 : 0 ≤ D := by positivity
  refine Integrable.of_bound (C := D * D) hmeas (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact (mp_tested_le Fo Gi hF hG _ _).trans
    (mul_le_mul (mp_cen_fro_le F S hϱ s ω) (mp_cen_fro_le F S hϱ' s' ω) (mm_fro_nn _) hD0)

private lemma mp_lag_lin {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ ϱ' : ℝ}
    (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') (ℓ : ℕ) (t : ℤ) (Gi : Mat n n) (hG : opNorm Gi ≤ 1)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Fi : ι → Mat m m) (hF : ∀ i, opNorm (Fi i) ≤ 1) :
    def_app_vol_lag F S ℓ t (∑ i ∈ s, c i • Fi i) Gi ϱ ϱ' =
      ∑ i ∈ s, c i * def_app_vol_lag F S ℓ t (Fi i) Gi ϱ ϱ' := by
  unfold def_app_vol_lag
  have hpt : ∀ ω, Matrix.trace ((∑ i ∈ s, c i • Fi i) * centredUpd F S ϱ t ω * Gi *
      (centredUpd F S ϱ' (t + (ℓ : ℤ)) ω)ᵀ) =
      ∑ i ∈ s, c i * Matrix.trace (Fi i * centredUpd F S ϱ t ω * Gi *
        (centredUpd F S ϱ' (t + (ℓ : ℤ)) ω)ᵀ) := by
    intro ω
    rw [Matrix.sum_mul, Matrix.sum_mul, Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun i _ => (mp_trace_int F S hϱ hϱ' t (t + (ℓ : ℤ)) (Fi i) Gi
    (hF i) hG).const_mul _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  ring

private lemma mp_sign_sum {m : ℕ} (d : Fin m → ℝ) :
    ∃ s : Fin m → ℝ, (∀ i, |s i| ≤ 1) ∧ ∑ i, |d i| = ∑ i, s i * d i := by
  refine ⟨fun i => if 0 ≤ d i then 1 else -1, fun i => ?_, ?_⟩
  · dsimp only
    split_ifs <;> simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.mp h)]; ring

private lemma mp_G_one {n : ℕ} (V : Mat n n) (hV : Vᵀ * V = 1) :
    V * Matrix.diagonal (fun _ : Fin n => (1 : ℝ)) * Vᵀ = 1 := by
  have h : V * Vᵀ = 1 := mul_eq_one_comm.mp hV
  simpa using h

private lemma mp_F_row {m : ℕ} (U : Mat m m) (i : Fin m) :
    outer (fun k => U k i) (fun k => U k i) =
      U * Matrix.diagonal (Pi.single i (1 : ℝ) : Fin m → ℝ) * Uᵀ := by
  ext a b
  simp [outer, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
    Pi.single_apply]

private lemma mp_F_sum {m : ℕ} (U : Mat m m) (d : Fin m → ℝ) :
    U * Matrix.diagonal d * Uᵀ =
      ∑ i : Fin m, d i • (U * Matrix.diagonal (Pi.single i (1 : ℝ) : Fin m → ℝ) * Uᵀ) := by
  have h : Matrix.diagonal d = ∑ i : Fin m, d i • Matrix.diagonal (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
    ext a b
    simp [Matrix.diagonal_apply, Matrix.sum_apply, Pi.single_apply]
  rw [h, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

private lemma mp_single_norm {k : ℕ} (U : Mat k k) (hU : Uᵀ * U = 1) (i : Fin k) :
    opNorm (U * Matrix.diagonal (Pi.single i (1 : ℝ) : Fin k → ℝ) * Uᵀ) ≤ 1 :=
  md_opNorm_conj U hU _ (fun i' => by
    by_cases h : i' = i <;> simp [Pi.single_apply, h])

private lemma mp_one_norm {n : ℕ} (V : Mat n n) (hV : Vᵀ * V = 1) :
    opNorm (1 : Mat n n) ≤ 1 := by
  have := md_opNorm_conj V hV (fun _ => (1 : ℝ)) (fun _ => by simp)
  rwa [mp_G_one V hV] at this

private lemma mp_sum_lin {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (Sp : SpectralData F.C) {ϱ ϱ' : ℝ} (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') (ℓ : ℕ) (t : ℤ)
    (d : Fin m → ℝ) :
    def_app_vol_lag F S ℓ t (Sp.uOut * Matrix.diagonal d * Sp.uOutᵀ) (1 : Mat n n) ϱ ϱ' =
      ∑ i, d i * ((B : ℝ)⁻¹ * rowLag F S Sp i ℓ t ϱ ϱ') := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast F.hB
  rw [mp_F_sum Sp.uOut d, mp_lag_lin F S hϱ hϱ' ℓ t (1 : Mat n n) (mp_one_norm Sp.vIn Sp.hvIn)
    Finset.univ d _ (fun i => mp_single_norm Sp.uOut Sp.huOut i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold rowLag
  have hrow : outer (Sp.u i) (Sp.u i) =
      Sp.uOut * Matrix.diagonal (Pi.single i (1 : ℝ) : Fin m → ℝ) * Sp.uOutᵀ :=
    mp_F_row Sp.uOut i
  rw [hrow]
  field_simp

private lemma mp_row_abs_diff {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (Sp : SpectralData F.C) {ϱ ϱ' : ℝ} (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') (ℓ : ℕ) (t : ℤ)
    (resp : Fin m → ℝ) :
    ∃ s : Fin m → ℝ, (∀ i, |s i| ≤ 1) ∧
      (B : ℝ)⁻¹ * ∑ i, |rowLag F S Sp i ℓ t ϱ ϱ' - (B : ℝ) * resp i| =
        def_app_vol_lag F S ℓ t (Sp.uOut * Matrix.diagonal s * Sp.uOutᵀ) (1 : Mat n n) ϱ ϱ' -
          ∑ i, s i * resp i := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast F.hB
  obtain ⟨s, hs, hsum⟩ := mp_sign_sum (fun i => (B : ℝ)⁻¹ * rowLag F S Sp i ℓ t ϱ ϱ' - resp i)
  refine ⟨s, hs, ?_⟩
  rw [mp_sum_lin F S Sp hϱ hϱ' ℓ t s, Finset.mul_sum]
  have e1 : ∀ i, (B : ℝ)⁻¹ * |rowLag F S Sp i ℓ t ϱ ϱ' - (B : ℝ) * resp i| =
      |(B : ℝ)⁻¹ * rowLag F S Sp i ℓ t ϱ ϱ' - resp i| := by
    intro i
    have : (B : ℝ)⁻¹ * rowLag F S Sp i ℓ t ϱ ϱ' - resp i =
        (B : ℝ)⁻¹ * (rowLag F S Sp i ℓ t ϱ ϱ' - (B : ℝ) * resp i) := by
      field_simp
    rw [this, abs_mul, abs_of_pos (inv_pos.mpr hBpos)]
  simp_rw [e1]
  rw [hsum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private lemma mp_rowLag_eq {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (Sp : SpectralData F.C) (i : Fin m)
    (ℓ : ℕ) (t : ℤ) (ϱ ϱ' : ℝ) :
    rowLag F S Sp i ℓ t ϱ ϱ' = (B : ℝ) * def_app_vol_lag F S ℓ t
      (Sp.uOut * Matrix.diagonal (Pi.single i (1 : ℝ) : Fin m → ℝ) * Sp.uOutᵀ) (1 : Mat n n) ϱ ϱ' := by
  have hrow : outer (Sp.u i) (Sp.u i) =
      Sp.uOut * Matrix.diagonal (Pi.single i (1 : ℝ) : Fin m → ℝ) * Sp.uOutᵀ :=
    mp_F_row Sp.uOut i
  unfold rowLag
  rw [hrow]

private lemma mp_tsum_sum {m : ℕ} (c : Fin m → ℝ) (u : Fin m → ℕ → ℝ)
    (hu : ∀ i, Summable (u i)) :
    ∑' ℓ, ∑ i, c i * u i ℓ = ∑ i, c i * ∑' ℓ, u i ℓ := by
  rw [Summable.tsum_finsetSum (fun i _ => (hu i).mul_left (c i))]
  exact Finset.sum_congr rfl fun i _ => tsum_mul_left

private lemma mp_symm {k : ℕ} (U : Mat k k) (x : Fin k → ℝ) :
    (U * Matrix.diagonal x * Uᵀ)ᵀ = U * Matrix.diagonal x * Uᵀ := by
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

end PHelpers


/-! ## Mode-resolved coefficients (`thm:app-vol-mode-kernels`, `Σ_in = Id`) -/

/-- `thm:app-vol-mode-kernels`, part (i): the actual row coefficients `C_{i,ℓ}` (`rowLag`,
`eqn:app-vol-Cil`) approximate the deterministic `C̄_{i,ℓ}` (`lagRowBar`) in the normalized absolute
sum, uniformly over `ϱ, ϱ' ∈ I` and over all times `t`, for every fixed lag `ℓ`. Snapshot
`cr-2026-10-23`. LaTeX, verbatim from `section.tex` (the whole environment):

\begin{theorem}[Mode-resolved coefficients, $\Sigmain=\Id$]\label{thm:app-vol-mode-kernels}
Let $\Sigmain=\Id_{\Nin}$.
\begin{enumerate}[label=(\roman*)]
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\begin{equation}\label{eqn:app-vol-rows-lag}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{C_{i,\ell}(\ridge,\ridge')-\overline C_{i,\ell}(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item At every finite dimension, $B^{-1}\sum_i\abs{\overline C_{i,0}}\le\gamma_\star$ and
$B^{-1}\sum_i\abs{\overline C_{i,\ell}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same bounds
hold for $C_{i,\ell}$ under \cref{assum:app-setup-regime}.
\item Each series $\mathfrak v_i$ converges absolutely, $\mathfrak v_i(\ridge)\ge0$, and
under \cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-rows-integrated}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{\Gamma_i(\ridge,\ridge')-\mathfrak v_i(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item The coefficients $\overline C_{i,\ell}$ and $\mathfrak v_i$ depend on $i$ only
through $\mu_i$, and vanish when $\mu_i=0$, as do $C_{i,\ell}$ and $\Gamma_i$. At
$\bmom=0$, $\overline C_{i,\ell}=0$ for $\ell\ge1$. At zero lag and equal ridges,
$\overline C_{i,0}(\ridge,\ridge)=\volraw_i(\ridge)$ of \cref{eqn:app-vol-half-candidates}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_mode_kernels_i (cert : Muon.External.GaussianOpNorm)
    (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (Sp : ∀ k : ℕ, SpectralData (R.F k).C)
    (hId : ∀ k : ℕ, (R.F k).C.Sin = 1) :
    ∀ ℓ : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi,
      ∀ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi,
      (R.B k : ℝ)⁻¹ * (∑ i : Fin (R.m k),
        |rowLag (R.F k) (S k) (Sp k) i ℓ t ϱ ϱ' -
          lagRowBar cert R.γstar R.CSig (R.F k).β ℓ (R.B k) (Sp k).μ (Sp k).lam i ϱ ϱ'|) ≤ ε := by
  intro ℓ ε hε
  have h := (thm_app_vol_lag_kernel_closure_actual cert R Ω P S Sp ℓ (Set.Icc R.ϱlo R.ϱhi)
    isCompact_Icc (fun x hx => lt_of_lt_of_le R.hϱ.1 hx.1)).2 ε hε
  filter_upwards [h] with k hk t ϱ hϱI ϱ' hϱ'I
  have hS : SizeFin (R.F k).C (R.B k) R.γstar R.CSig := ⟨R.dims k, R.normOut k, R.normIn k⟩
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le R.hϱ.1 hϱI.1
  have hϱ0' : 0 < ϱ' := lt_of_lt_of_le R.hϱ.1 hϱ'I.1
  obtain ⟨s, hs, he⟩ := mp_row_abs_diff (R.F k) (S k) (Sp k) hϱ0 hϱ0' ℓ t
    (fun i => lagResp cert R.γstar R.CSig (R.F k).β ℓ (R.B k) (Sp k).μ (Sp k).lam (Pi.single i 1)
      (fun _ : Fin (R.n k) => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ'))
  have hrb : ∀ i, lagRowBar cert R.γstar R.CSig (R.F k).β ℓ (R.B k) (Sp k).μ (Sp k).lam i ϱ ϱ' =
      (R.B k : ℝ) * lagResp cert R.γstar R.CSig (R.F k).β ℓ (R.B k) (Sp k).μ (Sp k).lam
        (Pi.single i 1) (fun _ : Fin (R.n k) => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ') := fun i => rfl
  simp_rw [hrb]
  rw [he]
  have hlin := md_lin_sum cert R.γstar R.CSig (R.F k) (Sp k) hS R.hC ℓ ϱ ϱ' hϱ0 hϱ0' s
  rw [← hlin]
  have hF := md_opNorm_conj (Sp k).uOut (Sp k).huOut s hs
  have hG := (md_FG_norm (Fp := R.F k) (Sp k) s hs).2
  have := hk t ϱ hϱI ϱ' hϱ'I s (fun _ => 1) ((Sp k).uOut * Matrix.diagonal s * (Sp k).uOutᵀ)
    ((Sp k).vIn * Matrix.diagonal (fun _ => (1 : ℝ)) * (Sp k).vInᵀ) rfl rfl hF hG
  rw [mp_G_one _ (Sp k).hvIn] at this
  exact (le_abs_self _).trans this

/-- `thm:app-vol-mode-kernels`, part (ii), deterministic bounds at every finite dimension:
`B⁻¹ ∑_i |C̄_{i,0}| ≤ γ⋆` and `B⁻¹ ∑_i |C̄_{i,ℓ}| ≤ K⋆ β^ℓ` for `ℓ ≥ 1`, for `ϱ, ϱ' ∈ I`
(`ϱ_- = min I`, card R17). Snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex` (the whole
environment):

\begin{theorem}[Mode-resolved coefficients, $\Sigmain=\Id$]\label{thm:app-vol-mode-kernels}
Let $\Sigmain=\Id_{\Nin}$.
\begin{enumerate}[label=(\roman*)]
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\begin{equation}\label{eqn:app-vol-rows-lag}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{C_{i,\ell}(\ridge,\ridge')-\overline C_{i,\ell}(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item At every finite dimension, $B^{-1}\sum_i\abs{\overline C_{i,0}}\le\gamma_\star$ and
$B^{-1}\sum_i\abs{\overline C_{i,\ell}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same bounds
hold for $C_{i,\ell}$ under \cref{assum:app-setup-regime}.
\item Each series $\mathfrak v_i$ converges absolutely, $\mathfrak v_i(\ridge)\ge0$, and
under \cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-rows-integrated}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{\Gamma_i(\ridge,\ridge')-\mathfrak v_i(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item The coefficients $\overline C_{i,\ell}$ and $\mathfrak v_i$ depend on $i$ only
through $\mu_i$, and vanish when $\mu_i=0$, as do $C_{i,\ell}$ and $\Gamma_i$. At
$\bmom=0$, $\overline C_{i,\ell}=0$ for $\ell\ge1$. At zero lag and equal ridges,
$\overline C_{i,0}(\ridge,\ridge)=\volraw_i(\ridge)$ of \cref{eqn:app-vol-half-candidates}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_mode_kernels_ii_bar (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (hId : Fp.C.Sin = 1) (ϱlo ϱhi : ℝ) (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) :
    (∀ ϱ ∈ Set.Icc ϱlo ϱhi, ∀ ϱ' ∈ Set.Icc ϱlo ϱhi,
      (B : ℝ)⁻¹ * (∑ i : Fin m, |lagRowBar cert γstar CSig Fp.β 0 B S.μ S.lam i ϱ ϱ'|) ≤ γstar) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ∀ ϱ ∈ Set.Icc ϱlo ϱhi, ∀ ϱ' ∈ Set.Icc ϱlo ϱhi,
      (B : ℝ)⁻¹ * (∑ i : Fin m, |lagRowBar cert γstar CSig Fp.β ℓ B S.μ S.lam i ϱ ϱ'|) ≤
        Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β ^ ℓ) := by
  have hγ := md_sizefin_pos Fp γstar CSig hS
  have hk : 0 ≤ Muon.Dynamics.kStar CSig γstar ϱlo := by
    unfold Muon.Dynamics.kStar
    exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hβ0 := Fp.hβ.1
  have hmem : ∀ x ∈ Set.Icc ϱlo ϱhi, 0 < x := fun x hx => lt_of_lt_of_le hϱ.1 hx.1
  have key : ∀ ϱ ∈ Set.Icc ϱlo ϱhi, ∀ ϱ' ∈ Set.Icc ϱlo ϱhi, ∀ Fd : Fin m → ℝ, (∀ i, |Fd i| ≤ 1) →
      |lagResp cert γstar CSig Fp.β 0 B S.μ S.lam Fd (fun _ : Fin n => (1 : ℝ)) (omegaF ϱ)
        (omegaF ϱ')| ≤ γstar ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd (fun _ : Fin n => (1 : ℝ))
        (omegaF ϱ) (omegaF ϱ')| ≤ Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β ^ ℓ := by
    intro ϱ hϱI ϱ' hϱ'I Fd hFd
    obtain ⟨hF, hG⟩ := md_FG_norm (Fp := Fp) S Fd hFd
    have n0 : ∀ {p q : ℕ} (A : Mat p q), 0 ≤ opNorm A := fun A => by unfold opNorm; exact norm_nonneg _
    have hI := thm_app_vol_integrated_ii cert γstar CSig Fp S hS hCSig ϱlo ϱhi hϱ
      _ _ Fd (fun _ => 1) rfl rfl ϱ ϱ' hϱI hϱ'I
    have hFG : opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) *
        opNorm (S.vIn * Matrix.diagonal (fun _ : Fin n => (1 : ℝ)) * S.vInᵀ) ≤ 1 := by
      simpa using mul_le_mul hF hG (n0 _) zero_le_one
    refine ⟨?_, fun ℓ hℓ => ?_⟩
    · refine hI.1.trans ?_
      calc _ = γstar * (opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) *
              opNorm (S.vIn * Matrix.diagonal (fun _ : Fin n => (1 : ℝ)) * S.vInᵀ)) := by ring
        _ ≤ γstar * 1 := mul_le_mul_of_nonneg_left hFG hγ.le
        _ = γstar := mul_one _
    · refine (hI.2.1 ℓ hℓ).trans ?_
      have hp : 0 ≤ Fp.β ^ ℓ := pow_nonneg hβ0 ℓ
      calc _ = Muon.Dynamics.kStar CSig γstar ϱlo *
              (opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) *
                opNorm (S.vIn * Matrix.diagonal (fun _ : Fin n => (1 : ℝ)) * S.vInᵀ)) * Fp.β ^ ℓ := by
            ring
        _ ≤ Muon.Dynamics.kStar CSig γstar ϱlo * 1 * Fp.β ^ ℓ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFG hk) hp
        _ = _ := by ring
  refine ⟨fun ϱ hϱI ϱ' hϱ'I => ?_, fun ℓ hℓ ϱ hϱI ϱ' hϱ'I => ?_⟩
  · rw [md_rowbar_sum cert γstar CSig Fp.β 0 B Fp.hB]
    exact md_sum_abs cert γstar CSig Fp S hS hCSig 0 ϱ ϱ' (hmem ϱ hϱI) (hmem ϱ' hϱ'I) γstar
      (fun Fd hFd => (key ϱ hϱI ϱ' hϱ'I Fd hFd).1)
  · rw [md_rowbar_sum cert γstar CSig Fp.β ℓ B Fp.hB]
    exact md_sum_abs cert γstar CSig Fp S hS hCSig ℓ ϱ ϱ' (hmem ϱ hϱI) (hmem ϱ' hϱ'I) _
      (fun Fd hFd => (key ϱ hϱI ϱ' hϱ'I Fd hFd).2 ℓ hℓ)

/-- `thm:app-vol-mode-kernels`, part (ii), the same bounds for the actual rows `C_{i,ℓ}` under
`assum:app-setup-regime` (read as: at every index `k` of the regime, every time `t`). Snapshot
`cr-2026-10-23`. LaTeX, verbatim from `section.tex` (the whole environment):

\begin{theorem}[Mode-resolved coefficients, $\Sigmain=\Id$]\label{thm:app-vol-mode-kernels}
Let $\Sigmain=\Id_{\Nin}$.
\begin{enumerate}[label=(\roman*)]
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\begin{equation}\label{eqn:app-vol-rows-lag}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{C_{i,\ell}(\ridge,\ridge')-\overline C_{i,\ell}(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item At every finite dimension, $B^{-1}\sum_i\abs{\overline C_{i,0}}\le\gamma_\star$ and
$B^{-1}\sum_i\abs{\overline C_{i,\ell}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same bounds
hold for $C_{i,\ell}$ under \cref{assum:app-setup-regime}.
\item Each series $\mathfrak v_i$ converges absolutely, $\mathfrak v_i(\ridge)\ge0$, and
under \cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-rows-integrated}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{\Gamma_i(\ridge,\ridge')-\mathfrak v_i(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item The coefficients $\overline C_{i,\ell}$ and $\mathfrak v_i$ depend on $i$ only
through $\mu_i$, and vanish when $\mu_i=0$, as do $C_{i,\ell}$ and $\Gamma_i$. At
$\bmom=0$, $\overline C_{i,\ell}=0$ for $\ell\ge1$. At zero lag and equal ridges,
$\overline C_{i,0}(\ridge,\ridge)=\volraw_i(\ridge)$ of \cref{eqn:app-vol-half-candidates}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_mode_kernels_ii_actual (cert : Muon.External.GaussianOpNorm)
    (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (Sp : ∀ k : ℕ, SpectralData (R.F k).C)
    (hId : ∀ k : ℕ, (R.F k).C.Sin = 1) :
    ∀ k : ℕ, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi, ∀ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi,
      (R.B k : ℝ)⁻¹ * (∑ i : Fin (R.m k), |rowLag (R.F k) (S k) (Sp k) i 0 t ϱ ϱ'|) ≤ R.γstar ∧
      (∀ ℓ : ℕ, 1 ≤ ℓ → (R.B k : ℝ)⁻¹ * (∑ i : Fin (R.m k),
          |rowLag (R.F k) (S k) (Sp k) i ℓ t ϱ ϱ'|) ≤
            Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo * (R.F k).β ^ ℓ) := by
  intro k t ϱ hϱI ϱ' hϱ'I
  have hS : SizeFin (R.F k).C (R.B k) R.γstar R.CSig := ⟨R.dims k, R.normOut k, R.normIn k⟩
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le R.hϱ.1 hϱI.1
  have hϱ0' : 0 < ϱ' := lt_of_lt_of_le R.hϱ.1 hϱ'I.1
  have main : ∀ ℓ : ℕ, ∃ s : Fin (R.m k) → ℝ, (∀ i, |s i| ≤ 1) ∧
      (R.B k : ℝ)⁻¹ * (∑ i : Fin (R.m k), |rowLag (R.F k) (S k) (Sp k) i ℓ t ϱ ϱ'|) =
        def_app_vol_lag (R.F k) (S k) ℓ t ((Sp k).uOut * Matrix.diagonal s * (Sp k).uOutᵀ)
          (1 : Mat (R.n k) (R.n k)) ϱ ϱ' := by
    intro ℓ
    obtain ⟨s, hs, h⟩ := mp_row_abs_diff (R.F k) (S k) (Sp k) hϱ0 hϱ0' ℓ t (fun _ => 0)
    refine ⟨s, hs, ?_⟩
    simpa using h
  have bnd : ∀ ℓ : ℕ, ∀ s : Fin (R.m k) → ℝ, (∀ i, |s i| ≤ 1) →
      |def_app_vol_lag (R.F k) (S k) ℓ t ((Sp k).uOut * Matrix.diagonal s * (Sp k).uOutᵀ)
          (1 : Mat (R.n k) (R.n k)) ϱ ϱ'| ≤ (if ℓ = 0 then R.γstar else
        Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo * (R.F k).β ^ ℓ) := by
    intro ℓ s hs
    have := thm_app_vol_lag_reduction_ii_actual (R.F k) (S k) R.γstar R.CSig R.ϱlo R.ϱhi hS R.hC
      R.hϱ ((Sp k).uOut * Matrix.diagonal s * (Sp k).uOutᵀ) (1 : Mat (R.n k) (R.n k))
      (mp_symm _ _) Matrix.transpose_one (md_opNorm_conj _ (Sp k).huOut s hs)
      (mp_one_norm _ (Sp k).hvIn) ϱ ϱ' hϱI hϱ'I t
    by_cases hℓ : ℓ = 0
    · subst hℓ; simpa using this.1
    · simpa [hℓ] using this.2 ℓ (Nat.one_le_iff_ne_zero.mpr hℓ)
  refine ⟨?_, fun ℓ hℓ => ?_⟩
  · obtain ⟨s, hs, h⟩ := main 0
    rw [h]
    exact (le_abs_self _).trans (by simpa using bnd 0 s hs)
  · obtain ⟨s, hs, h⟩ := main ℓ
    rw [h]
    exact (le_abs_self _).trans (by simpa [Nat.pos_iff_ne_zero.mp hℓ, show ℓ ≠ 0 by omega] using bnd ℓ s hs)

/-- `thm:app-vol-mode-kernels`, part (iii), absolute convergence and nonnegativity at every
finite dimension: each series `𝔳_i(ϱ,ϱ')` converges absolutely for `ϱ, ϱ' ∈ I`, and
`𝔳_i(ϱ) = 𝔳_i(ϱ,ϱ) ≥ 0`. Snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex` (the whole
environment):

\begin{theorem}[Mode-resolved coefficients, $\Sigmain=\Id$]\label{thm:app-vol-mode-kernels}
Let $\Sigmain=\Id_{\Nin}$.
\begin{enumerate}[label=(\roman*)]
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\begin{equation}\label{eqn:app-vol-rows-lag}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{C_{i,\ell}(\ridge,\ridge')-\overline C_{i,\ell}(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item At every finite dimension, $B^{-1}\sum_i\abs{\overline C_{i,0}}\le\gamma_\star$ and
$B^{-1}\sum_i\abs{\overline C_{i,\ell}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same bounds
hold for $C_{i,\ell}$ under \cref{assum:app-setup-regime}.
\item Each series $\mathfrak v_i$ converges absolutely, $\mathfrak v_i(\ridge)\ge0$, and
under \cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-rows-integrated}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{\Gamma_i(\ridge,\ridge')-\mathfrak v_i(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item The coefficients $\overline C_{i,\ell}$ and $\mathfrak v_i$ depend on $i$ only
through $\mu_i$, and vanish when $\mu_i=0$, as do $C_{i,\ell}$ and $\Gamma_i$. At
$\bmom=0$, $\overline C_{i,\ell}=0$ for $\ell\ge1$. At zero lag and equal ridges,
$\overline C_{i,0}(\ridge,\ridge)=\volraw_i(\ridge)$ of \cref{eqn:app-vol-half-candidates}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_mode_kernels_iii_series (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (hId : Fp.C.Sin = 1) (ϱlo ϱhi : ℝ) (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) :
    (∀ i : Fin m, ∀ ϱ ∈ Set.Icc ϱlo ϱhi, ∀ ϱ' ∈ Set.Icc ϱlo ϱhi,
      Summable (fun ℓ : ℕ => |lagRowBar cert γstar CSig Fp.β (ℓ + 1) B S.μ S.lam i ϱ ϱ' +
        lagRowBar cert γstar CSig Fp.β (ℓ + 1) B S.μ S.lam i ϱ' ϱ|)) ∧
    (∀ i : Fin m, ∀ ϱ ∈ Set.Icc ϱlo ϱhi, 0 ≤ rowVBar cert γstar CSig Fp.β B S.μ S.lam i ϱ ϱ) := by
  have hmem : ∀ x ∈ Set.Icc ϱlo ϱhi, 0 < x := fun x hx => lt_of_lt_of_le hϱ.1 hx.1
  have hFd : ∀ i : Fin m, ∀ i' : Fin m, |(Pi.single i 1 : Fin m → ℝ) i'| ≤ 1 := fun i i' => by
    by_cases h : i' = i <;> simp [Pi.single_apply, h]
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  refine ⟨fun i ϱ hϱI ϱ' hϱ'I => ?_, fun i ϱ hϱI => ?_⟩
  · have h := (thm_app_vol_integrated_iii cert γstar CSig Fp S hS hCSig
      (S.uOut * Matrix.diagonal (Pi.single i 1) * S.uOutᵀ)
      (S.vIn * Matrix.diagonal (fun _ : Fin n => (1 : ℝ)) * S.vInᵀ) (Pi.single i 1)
      (fun _ => 1) rfl rfl ϱlo ϱhi hϱ ϱ ϱ' hϱI hϱ'I).1
    have h2 := h.mul_left (B : ℝ)
    refine h2.congr fun ℓ => ?_
    unfold lagRowBar
    rw [← mul_add, abs_mul, abs_of_nonneg hB]
  · have hPSD := (thm_app_vol_integrated_iii cert γstar CSig Fp S hS hCSig
      (S.uOut * Matrix.diagonal (Pi.single i 1) * S.uOutᵀ)
      (S.vIn * Matrix.diagonal (fun _ : Fin n => (1 : ℝ)) * S.vInᵀ) (Pi.single i 1)
      (fun _ => 1) rfl rfl ϱlo ϱhi hϱ ϱ ϱ hϱI hϱI).2
    have hF : (S.uOut * Matrix.diagonal (Pi.single i 1 : Fin m → ℝ) * S.uOutᵀ).PosSemidef := by
      have hd : (Matrix.diagonal (Pi.single i 1 : Fin m → ℝ)).PosSemidef := by
        rw [Matrix.posSemidef_diagonal_iff]
        intro i'
        by_cases h : i' = i <;> simp [Pi.single_apply, h]
      have := hd.mul_mul_conjTranspose_same S.uOut
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
    have hG : (S.vIn * Matrix.diagonal (fun _ : Fin n => (1 : ℝ)) * S.vInᵀ).PosSemidef := by
      have hd : (Matrix.diagonal (fun _ : Fin n => (1 : ℝ))).PosSemidef := by
        rw [Matrix.posSemidef_diagonal_iff]
        intro _
        exact zero_le_one
      have := hd.mul_mul_conjTranspose_same S.vIn
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
    have h0 := hPSD hF hG
    have : rowVBar cert γstar CSig Fp.β B S.μ S.lam i ϱ ϱ =
        (B : ℝ) * lagGammaBar cert γstar CSig Fp.β B S.μ S.lam (Pi.single i 1)
          (fun _ : Fin n => (1 : ℝ)) ϱ ϱ := by
      unfold rowVBar lagGammaBar lagRowBar
      rw [mul_add, ← tsum_mul_left]
      congr 1
      refine tsum_congr fun ℓ => ?_
      ring
    rw [this]
    exact mul_nonneg hB h0

/-- `thm:app-vol-mode-kernels`, part (iii), absolute convergence of the actual integrated row series:
under `assum:app-setup-regime`, for every index `k`, time `t` and `ϱ, ϱ' ∈ I`, the series defining
`Γ_i` (`rowGamma`, `eqn:app-vol-Gamma`) converges absolutely (lag-reduction (iii) supplies the
geometric tail). Snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex` (the whole
environment):

\begin{theorem}[Mode-resolved coefficients, $\Sigmain=\Id$]\label{thm:app-vol-mode-kernels}
Let $\Sigmain=\Id_{\Nin}$.
\begin{enumerate}[label=(\roman*)]
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\begin{equation}\label{eqn:app-vol-rows-lag}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{C_{i,\ell}(\ridge,\ridge')-\overline C_{i,\ell}(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item At every finite dimension, $B^{-1}\sum_i\abs{\overline C_{i,0}}\le\gamma_\star$ and
$B^{-1}\sum_i\abs{\overline C_{i,\ell}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same bounds
hold for $C_{i,\ell}$ under \cref{assum:app-setup-regime}.
\item Each series $\mathfrak v_i$ converges absolutely, $\mathfrak v_i(\ridge)\ge0$, and
under \cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-rows-integrated}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{\Gamma_i(\ridge,\ridge')-\mathfrak v_i(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item The coefficients $\overline C_{i,\ell}$ and $\mathfrak v_i$ depend on $i$ only
through $\mu_i$, and vanish when $\mu_i=0$, as do $C_{i,\ell}$ and $\Gamma_i$. At
$\bmom=0$, $\overline C_{i,\ell}=0$ for $\ell\ge1$. At zero lag and equal ridges,
$\overline C_{i,0}(\ridge,\ridge)=\volraw_i(\ridge)$ of \cref{eqn:app-vol-half-candidates}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_mode_kernels_iii_summable (cert : Muon.External.GaussianOpNorm)
    (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (Sp : ∀ k : ℕ, SpectralData (R.F k).C)
    (hId : ∀ k : ℕ, (R.F k).C.Sin = 1) :
    ∀ k : ℕ, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi, ∀ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi, ∀ i : Fin (R.m k),
      Summable (fun ℓ : ℕ => |rowLag (R.F k) (S k) (Sp k) i (ℓ + 1) t ϱ ϱ' +
        rowLag (R.F k) (S k) (Sp k) i (ℓ + 1) t ϱ' ϱ|) := by
  intro k t ϱ hϱI ϱ' hϱ'I i
  have hS : SizeFin (R.F k).C (R.B k) R.γstar R.CSig := ⟨R.dims k, R.normOut k, R.normIn k⟩
  have h := thm_app_vol_lag_reduction_iii_summable (R.F k) (S k) R.γstar R.CSig R.ϱlo R.ϱhi hS R.hC
    R.hϱ ((Sp k).uOut * Matrix.diagonal (Pi.single i (1 : ℝ) : Fin (R.m k) → ℝ) * (Sp k).uOutᵀ)
    (1 : Mat (R.n k) (R.n k)) (mp_symm _ _) Matrix.transpose_one
    (mp_single_norm _ (Sp k).huOut i) (mp_one_norm _ (Sp k).hvIn) ϱ ϱ' hϱI hϱ'I t
  have h2 := h.mul_left ((R.B k : ℝ))
  refine h2.congr fun ℓ => ?_
  rw [mp_rowLag_eq, mp_rowLag_eq, ← mul_add, abs_mul, abs_of_nonneg (Nat.cast_nonneg (R.B k) : (0 : ℝ) ≤ (R.B k : ℝ))]

/-- `thm:app-vol-mode-kernels`, part (iii), the normalized limit of the integrated rows: under
`assum:app-setup-regime`, `B⁻¹ ∑_i |Γ_i(ϱ,ϱ') - 𝔳_i(ϱ,ϱ')| → 0` uniformly over `ϱ, ϱ' ∈ I` and all
times `t` (`rowGamma`, `rowVBar`). Snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex`
(the whole environment):

\begin{theorem}[Mode-resolved coefficients, $\Sigmain=\Id$]\label{thm:app-vol-mode-kernels}
Let $\Sigmain=\Id_{\Nin}$.
\begin{enumerate}[label=(\roman*)]
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\begin{equation}\label{eqn:app-vol-rows-lag}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{C_{i,\ell}(\ridge,\ridge')-\overline C_{i,\ell}(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item At every finite dimension, $B^{-1}\sum_i\abs{\overline C_{i,0}}\le\gamma_\star$ and
$B^{-1}\sum_i\abs{\overline C_{i,\ell}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same bounds
hold for $C_{i,\ell}$ under \cref{assum:app-setup-regime}.
\item Each series $\mathfrak v_i$ converges absolutely, $\mathfrak v_i(\ridge)\ge0$, and
under \cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-rows-integrated}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{\Gamma_i(\ridge,\ridge')-\mathfrak v_i(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item The coefficients $\overline C_{i,\ell}$ and $\mathfrak v_i$ depend on $i$ only
through $\mu_i$, and vanish when $\mu_i=0$, as do $C_{i,\ell}$ and $\Gamma_i$. At
$\bmom=0$, $\overline C_{i,\ell}=0$ for $\ell\ge1$. At zero lag and equal ridges,
$\overline C_{i,0}(\ridge,\ridge)=\volraw_i(\ridge)$ of \cref{eqn:app-vol-half-candidates}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_mode_kernels_iii_limit (cert : Muon.External.GaussianOpNorm)
    (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (Sp : ∀ k : ℕ, SpectralData (R.F k).C)
    (hId : ∀ k : ℕ, (R.F k).C.Sin = 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi,
      ∀ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi,
      (R.B k : ℝ)⁻¹ * (∑ i : Fin (R.m k),
        |rowGamma (R.F k) (S k) (Sp k) i t ϱ ϱ' -
          rowVBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam i ϱ ϱ'|) ≤ ε := by
  intro ε hε
  have h := (thm_app_vol_integrated_iv cert R Ω P S Sp).1 ε hε
  filter_upwards [h] with k hk t ϱ hϱI ϱ' hϱ'I
  have hS : SizeFin (R.F k).C (R.B k) R.γstar R.CSig := ⟨R.dims k, R.normOut k, R.normIn k⟩
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le R.hϱ.1 hϱI.1
  have hϱ0' : 0 < ϱ' := lt_of_lt_of_le R.hϱ.1 hϱ'I.1
  have hBpos : (0 : ℝ) < R.B k := by exact_mod_cast (R.F k).hB
  have hu : ∀ i, Summable (fun ℓ : ℕ => rowLag (R.F k) (S k) (Sp k) i (ℓ + 1) t ϱ ϱ' +
      rowLag (R.F k) (S k) (Sp k) i (ℓ + 1) t ϱ' ϱ) := fun i =>
    summable_abs_iff.mp
      (thm_app_vol_mode_kernels_iii_summable cert R Ω P S Sp hId k t ϱ hϱI ϱ' hϱ'I i)
  have hw : ∀ i, Summable (fun ℓ : ℕ => lagRowBar cert R.γstar R.CSig (R.F k).β (ℓ + 1) (R.B k)
      (Sp k).μ (Sp k).lam i ϱ ϱ' + lagRowBar cert R.γstar R.CSig (R.F k).β (ℓ + 1) (R.B k)
      (Sp k).μ (Sp k).lam i ϱ' ϱ) := fun i =>
    summable_abs_iff.mp
      ((thm_app_vol_mode_kernels_iii_series cert R.γstar R.CSig (R.F k) (Sp k) hS R.hC (hId k)
        R.ϱlo R.ϱhi R.hϱ).1 i ϱ hϱI ϱ' hϱ'I)
  obtain ⟨s, hs, hsum⟩ := mp_sign_sum (fun i => (R.B k : ℝ)⁻¹ *
    rowGamma (R.F k) (S k) (Sp k) i t ϱ ϱ' - (R.B k : ℝ)⁻¹ *
    rowVBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam i ϱ ϱ')
  have key1 : integratedLag (R.F k) (S k) t ((Sp k).uOut * Matrix.diagonal s * (Sp k).uOutᵀ)
      (1 : Mat (R.n k) (R.n k)) ϱ ϱ' =
      ∑ i, s i * ((R.B k : ℝ)⁻¹ * rowGamma (R.F k) (S k) (Sp k) i t ϱ ϱ') := by
    have hterm : ∀ ℓ : ℕ, def_app_vol_lag (R.F k) (S k) (ℓ + 1) t
        ((Sp k).uOut * Matrix.diagonal s * (Sp k).uOutᵀ) (1 : Mat (R.n k) (R.n k)) ϱ ϱ' +
        def_app_vol_lag (R.F k) (S k) (ℓ + 1) t
        ((Sp k).uOut * Matrix.diagonal s * (Sp k).uOutᵀ) (1 : Mat (R.n k) (R.n k)) ϱ' ϱ =
        ∑ i, (s i * (R.B k : ℝ)⁻¹) * (rowLag (R.F k) (S k) (Sp k) i (ℓ + 1) t ϱ ϱ' +
          rowLag (R.F k) (S k) (Sp k) i (ℓ + 1) t ϱ' ϱ) := by
      intro ℓ
      rw [mp_sum_lin (R.F k) (S k) (Sp k) hϱ0 hϱ0' (ℓ + 1) t s,
        mp_sum_lin (R.F k) (S k) (Sp k) hϱ0' hϱ0 (ℓ + 1) t s, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hts := mp_tsum_sum (fun i => s i * (R.B k : ℝ)⁻¹)
      (fun i ℓ => rowLag (R.F k) (S k) (Sp k) i (ℓ + 1) t ϱ ϱ' +
        rowLag (R.F k) (S k) (Sp k) i (ℓ + 1) t ϱ' ϱ) hu
    beta_reduce at hts
    unfold integratedLag
    rw [tsum_congr hterm, hts, mp_sum_lin (R.F k) (S k) (Sp k) hϱ0 hϱ0' 0 t s]
    unfold rowGamma
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have key2 : lagGammaBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam s
      (fun _ : Fin (R.n k) => (1 : ℝ)) ϱ ϱ' =
      ∑ i, s i * ((R.B k : ℝ)⁻¹ *
        rowVBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam i ϱ ϱ') := by
    have hlin : ∀ (ℓ : ℕ) (x y : ℝ), 0 < x → 0 < y →
        lagResp cert R.γstar R.CSig (R.F k).β ℓ (R.B k) (Sp k).μ (Sp k).lam s
          (fun _ : Fin (R.n k) => (1 : ℝ)) (omegaF x) (omegaF y) =
        ∑ i, s i * lagResp cert R.γstar R.CSig (R.F k).β ℓ (R.B k) (Sp k).μ (Sp k).lam
          (Pi.single i 1) (fun _ : Fin (R.n k) => (1 : ℝ)) (omegaF x) (omegaF y) :=
      fun ℓ x y hx hy => md_lin_sum cert R.γstar R.CSig (R.F k) (Sp k) hS R.hC ℓ x y hx hy s
    have hrb : ∀ (ℓ : ℕ) (i : Fin (R.m k)) (x y : ℝ),
        lagResp cert R.γstar R.CSig (R.F k).β ℓ (R.B k) (Sp k).μ (Sp k).lam
          (Pi.single i 1) (fun _ : Fin (R.n k) => (1 : ℝ)) (omegaF x) (omegaF y) =
        (R.B k : ℝ)⁻¹ * lagRowBar cert R.γstar R.CSig (R.F k).β ℓ (R.B k) (Sp k).μ (Sp k).lam
          i x y := by
      intro ℓ i x y
      unfold lagRowBar
      field_simp
    have hterm : ∀ ℓ : ℕ,
        lagResp cert R.γstar R.CSig (R.F k).β (ℓ + 1) (R.B k) (Sp k).μ (Sp k).lam s
          (fun _ : Fin (R.n k) => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ') +
        lagResp cert R.γstar R.CSig (R.F k).β (ℓ + 1) (R.B k) (Sp k).μ (Sp k).lam s
          (fun _ : Fin (R.n k) => (1 : ℝ)) (omegaF ϱ') (omegaF ϱ) =
        ∑ i, (s i * (R.B k : ℝ)⁻¹) * (lagRowBar cert R.γstar R.CSig (R.F k).β (ℓ + 1) (R.B k)
          (Sp k).μ (Sp k).lam i ϱ ϱ' + lagRowBar cert R.γstar R.CSig (R.F k).β (ℓ + 1) (R.B k)
          (Sp k).μ (Sp k).lam i ϱ' ϱ) := by
      intro ℓ
      rw [hlin _ ϱ ϱ' hϱ0 hϱ0', hlin _ ϱ' ϱ hϱ0' hϱ0, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hrb, hrb]
      ring
    have hts := mp_tsum_sum (fun i => s i * (R.B k : ℝ)⁻¹)
      (fun i ℓ => lagRowBar cert R.γstar R.CSig (R.F k).β (ℓ + 1) (R.B k)
          (Sp k).μ (Sp k).lam i ϱ ϱ' + lagRowBar cert R.γstar R.CSig (R.F k).β (ℓ + 1) (R.B k)
          (Sp k).μ (Sp k).lam i ϱ' ϱ) hw
    beta_reduce at hts
    unfold lagGammaBar
    rw [tsum_congr hterm, hts, hlin 0 ϱ ϱ' hϱ0 hϱ0']
    unfold rowVBar
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrb]
    ring
  have e1 : ∀ i, (R.B k : ℝ)⁻¹ * |rowGamma (R.F k) (S k) (Sp k) i t ϱ ϱ' -
      rowVBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam i ϱ ϱ'| =
      |(R.B k : ℝ)⁻¹ * rowGamma (R.F k) (S k) (Sp k) i t ϱ ϱ' - (R.B k : ℝ)⁻¹ *
        rowVBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam i ϱ ϱ'| := by
    intro i
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hBpos)]
  rw [Finset.mul_sum]
  simp_rw [e1]
  rw [hsum]
  have hdiff : ∑ i, s i * ((R.B k : ℝ)⁻¹ * rowGamma (R.F k) (S k) (Sp k) i t ϱ ϱ' -
      (R.B k : ℝ)⁻¹ * rowVBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam i ϱ ϱ') =
      integratedLag (R.F k) (S k) t ((Sp k).uOut * Matrix.diagonal s * (Sp k).uOutᵀ)
        (1 : Mat (R.n k) (R.n k)) ϱ ϱ' -
      lagGammaBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam s
        (fun _ : Fin (R.n k) => (1 : ℝ)) ϱ ϱ' := by
    rw [key1, key2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hdiff]
  have hF := md_opNorm_conj (Sp k).uOut (Sp k).huOut s hs
  have hG := (md_FG_norm (Fp := R.F k) (Sp k) s hs).2
  have := hk t ϱ hϱI ϱ' hϱ'I s (fun _ => 1) ((Sp k).uOut * Matrix.diagonal s * (Sp k).uOutᵀ)
    ((Sp k).vIn * Matrix.diagonal (fun _ => (1 : ℝ)) * (Sp k).vInᵀ) rfl rfl hF hG
  rw [mp_G_one _ (Sp k).hvIn] at this
  exact (le_abs_self _).trans this

/-- `thm:app-vol-mode-kernels`, part (iv), first clause: `C̄_{i,ℓ}` and `𝔳_i` depend on the row
index only through `μ_i` (`lagRowBar`, `rowVBar`). Snapshot `cr-2026-10-23`. LaTeX, verbatim from
`section.tex` (the whole environment):

\begin{theorem}[Mode-resolved coefficients, $\Sigmain=\Id$]\label{thm:app-vol-mode-kernels}
Let $\Sigmain=\Id_{\Nin}$.
\begin{enumerate}[label=(\roman*)]
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\begin{equation}\label{eqn:app-vol-rows-lag}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{C_{i,\ell}(\ridge,\ridge')-\overline C_{i,\ell}(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item At every finite dimension, $B^{-1}\sum_i\abs{\overline C_{i,0}}\le\gamma_\star$ and
$B^{-1}\sum_i\abs{\overline C_{i,\ell}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same bounds
hold for $C_{i,\ell}$ under \cref{assum:app-setup-regime}.
\item Each series $\mathfrak v_i$ converges absolutely, $\mathfrak v_i(\ridge)\ge0$, and
under \cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-rows-integrated}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{\Gamma_i(\ridge,\ridge')-\mathfrak v_i(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item The coefficients $\overline C_{i,\ell}$ and $\mathfrak v_i$ depend on $i$ only
through $\mu_i$, and vanish when $\mu_i=0$, as do $C_{i,\ell}$ and $\Gamma_i$. At
$\bmom=0$, $\overline C_{i,\ell}=0$ for $\ell\ge1$. At zero lag and equal ridges,
$\overline C_{i,0}(\ridge,\ridge)=\volraw_i(\ridge)$ of \cref{eqn:app-vol-half-candidates}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_mode_kernels_iv_mu (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (hId : Fp.C.Sin = 1) (ℓ : ℕ) (ϱ ϱ' : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ')
    (i i' : Fin m) (hμ : S.μ i = S.μ i') :
    lagRowBar cert γstar CSig Fp.β ℓ B S.μ S.lam i ϱ ϱ' =
        lagRowBar cert γstar CSig Fp.β ℓ B S.μ S.lam i' ϱ ϱ' ∧
      rowVBar cert γstar CSig Fp.β B S.μ S.lam i ϱ ϱ' =
        rowVBar cert γstar CSig Fp.β B S.μ S.lam i' ϱ ϱ' := by
  have hRow : ∀ (ℓ : ℕ) (x y : ℝ), lagRowBar cert γstar CSig Fp.β ℓ B S.μ S.lam i x y =
      lagRowBar cert γstar CSig Fp.β ℓ B S.μ S.lam i' x y := by
    intro ℓ x y
    unfold lagRowBar lagResp lagRespCut treeRespExt def_app_vol_tree treeMono treeClassFactor
    have key : ∀ q r : ℕ, ∑ k : Fin m, S.μ k ^ q * (Pi.single i (1 : ℝ) : Fin m → ℝ) k ^ r =
        ∑ k : Fin m, S.μ k ^ q * (Pi.single i' (1 : ℝ) : Fin m → ℝ) k ^ r := by
      intro q r
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; simp
      · have hs : ∀ j : Fin m, ∑ k : Fin m, S.μ k ^ q * (Pi.single j (1 : ℝ) : Fin m → ℝ) k ^ r =
            S.μ j ^ q := by
          intro j
          rw [Finset.sum_eq_single j]
          · simp
          · intro k _ hk
            simp [Pi.single_apply, hk, h.ne']
          · intro hj; exact absurd (Finset.mem_univ j) hj
        rw [hs i, hs i', hμ]
    simp only [key]
  refine ⟨hRow ℓ ϱ ϱ', ?_⟩
  unfold rowVBar
  simp only [hRow]

private lemma vz_prev_val {k : ℕ} (s : Fin k) :
    (treePrev s).val = if s.val = 0 then k - 1 else s.val - 1 := by
  obtain ⟨v, hv⟩ := s
  unfold treePrev
  dsimp only
  rcases Nat.eq_zero_or_pos v with rfl | hpos
  · simp [Nat.mod_eq_of_lt (show k - 1 < k by omega)]
  · rw [if_neg (show ¬ (v = 0) by omega)]
    have e : v + (k - 1) = (v - 1) + k := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (show v - 1 < k by omega)]

private lemma vz_outV_odd {k : ℕ} (hk : k % 2 = 0) (s : Fin k) :
    (treeOutV s).val % 2 = 1 := by
  have hs := s.isLt
  unfold treeOutV
  split_ifs with h
  · have h' : s.val % 2 = 0 := h
    rw [vz_prev_val]
    split_ifs with h0 <;> omega
  · have h' : ¬ s.val % 2 = 0 := h
    omega

private lemma vz_inV_even {k : ℕ} (s : Fin k) : (treeInV s).val % 2 = 0 := by
  have hs := s.isLt
  unfold treeInV
  split_ifs with h
  · have h' : s.val % 2 = 0 := h
    exact h'
  · have h' : ¬ s.val % 2 = 0 := h
    rw [vz_prev_val]
    split_ifs with h0 <;> omega

/-- Private helper: the identifications preserve the parity of external indices. -/
private lemma vz_setoid_par {k : ℕ} (hk : k % 2 = 0) (p : TreeMatch k × TreeMatch k) {x y : TreeVtx k}
    (h : treeSetoid p x y) : Sum.elim (fun e : Fin k => e.val % 2) (fun _ : Fin k => 2) x =
      Sum.elim (fun e : Fin k => e.val % 2) (fun _ : Fin k => 2) y := by
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
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [vz_outV_odd hk s, vz_outV_odd hk (p.1.1 s)]
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a; subst h1b
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [vz_inV_even s, vz_inV_even (p.2.1 s)]
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Private helper: the class of the `G`-mark contains no odd (output) external vertex. -/
private lemma vz_gmark_pure (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) :
    ¬ ∃ e : Fin (treeK a b),
      treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeGMark a b)) ∧ e.val % 2 = 1 := by
  rintro ⟨e, heq, hodd⟩
  unfold treeMk at heq
  have h2 := vz_setoid_par (by unfold treeK; omega) p (Quotient.exact heq)
  simp only [Sum.elim_inl, treeGMark, Fin.val_mk] at h2
  omega


open Classical in
private lemma vz_prod_zero_of_factor {a b : ℕ} (p : TreeMatch (treeK a b) × TreeMatch (treeK a b))
    (f : Quotient (treeSetoid p) → ℝ) (V : Quotient (treeSetoid p)) (h : f V = 0) :
    ∏ W : Quotient (treeSetoid p), f W = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ V) h

open Classical in
private lemma vz_treeMono_zero_F {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (hF : ∀ i, μ i * Fd i = 0) (a b : ℕ) :
    treeMono β ℓ J R B μ lam Fd Gd a b = 0 := by
  unfold treeMono
  refine Finset.sum_eq_zero fun p _ => ?_
  split_ifs with hp
  · refine vz_prod_zero_of_factor p _ (treeMk p (Sum.inl (treeFMark a b))) ?_
    have hex : ∃ e : Fin (treeK a b),
        treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeFMark a b)) := ⟨_, rfl⟩
    have hodd : ∃ e : Fin (treeK a b),
        treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeFMark a b)) ∧ e.val % 2 = 1 :=
      ⟨treeFMark a b, rfl, by unfold treeFMark; dsimp only; omega⟩
    unfold treeClassFactor
    simp only [if_pos hex, if_pos hodd, if_true, pow_one]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => ?_)
    have hpos : 0 < (Finset.univ.filter fun e : Fin (treeK a b) =>
        treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeFMark a b))).card :=
      Finset.card_pos.mpr ⟨treeFMark a b, by simp⟩
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hq, pow_succ, mul_assoc, hF i, mul_zero]
  · rfl

open Classical in
private lemma vz_treeMono_zero_G {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (hG : ∀ j, lam j * Gd j = 0) (a b : ℕ) :
    treeMono β ℓ J R B μ lam Fd Gd a b = 0 := by
  unfold treeMono
  refine Finset.sum_eq_zero fun p _ => ?_
  split_ifs with hp
  · refine vz_prod_zero_of_factor p _ (treeMk p (Sum.inl (treeGMark a b))) ?_
    have hex : ∃ e : Fin (treeK a b),
        treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeGMark a b)) := ⟨_, rfl⟩
    have hnot := vz_gmark_pure a b p
    unfold treeClassFactor
    simp only [if_pos hex, if_neg hnot, if_true, pow_one]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => ?_)
    have hpos : 0 < (Finset.univ.filter fun e : Fin (treeK a b) =>
        treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeGMark a b))).card :=
      Finset.card_pos.mpr ⟨treeGMark a b, by simp⟩
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hq, pow_succ, mul_assoc, hG j, mul_zero]
  · rfl

private lemma vz_lagResp_zero_aux (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n : ℕ} (β : ℝ) (ℓ B : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ)
    (Gd : Fin n → ℝ) (f g : ℝ → ℝ)
    (h0 : ∀ (J : ℕ) (R : ℝ) (f₁ f₂ : Polynomial ℝ),
      def_app_vol_tree β ℓ J R B μ lam Fd Gd f₁ f₂ = 0) :
    lagResp cert γstar CSig β ℓ B μ lam Fd Gd f g = 0 := by
  have e1 : ∀ p : ℕ × ℝ, lagRespCut cert γstar CSig β ℓ p.1 p.2 B μ lam Fd Gd f g = 0 := by
    intro p
    unfold lagRespCut treeRespExt
    simp_rw [h0]
    exact tendsto_const_nhds.limUnder_eq
  unfold lagResp
  simp_rw [e1]
  exact tendsto_const_nhds.limUnder_eq

private lemma vz_lagResp_zero_F (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n : ℕ} (β : ℝ) (ℓ B : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ)
    (Gd : Fin n → ℝ) (hF : ∀ i, μ i * Fd i = 0) (f g : ℝ → ℝ) :
    lagResp cert γstar CSig β ℓ B μ lam Fd Gd f g = 0 := by
  refine vz_lagResp_zero_aux cert γstar CSig β ℓ B μ lam Fd Gd f g fun J R f₁ f₂ => ?_
  unfold def_app_vol_tree
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rw [vz_treeMono_zero_F β ℓ J R B μ lam Fd Gd hF a b, mul_zero]


private lemma vz_entry_int {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (Fp : FrozenParams m n B) (S : FrozenSamples P m n B)
    {ϱ : ℝ} (hϱ : 0 < ϱ) (t : ℤ) (k : Fin m) (j : Fin n) :
    Integrable (fun ω => frozenUpd Fp S ϱ t ω k j) P := by
  refine Integrable.of_bound (C := (m : ℝ) + 1) ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · have h : Continuous (fun K : Mat m n => K k j) := by fun_prop
    exact h.comp_aestronglyMeasurable (mm_upd_aesm Fp S hϱ t)
  · rw [Real.norm_eq_abs]
    exact (mm_abs_entry_le_fro _ k j).trans (mm_upd_fro_le Fp S hϱ t ω)

private lemma vz_cent_row {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (Fp : FrozenParams m n B) (S : FrozenSamples P m n B)
    (Sp : SpectralData Fp.C) {ϱ : ℝ} (hϱ : 0 < ϱ) (t : ℤ) (i : Fin m) (hμ : Sp.μ i = 0)
    (ω : Ω) : (centredUpd Fp S ϱ t ω)ᵀ *ᵥ Sp.u i = 0 := by
  have h0 := fun ω' => thm_app_vol_half_same_ii_zero_rows Fp S t Sp ϱ ϱ hϱ ϱ ⟨le_rfl, le_rfl⟩ ω' i hμ
  have hmean : (mean P (frozenUpd Fp S ϱ t))ᵀ *ᵥ Sp.u i = 0 := by
    funext j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mean, Matrix.of_apply, Pi.zero_apply]
    have hj : ∀ ω', ∑ k, frozenUpd Fp S ϱ t ω' k j * Sp.u i k = 0 := by
      intro ω'
      have := congrFun (h0 ω') j
      simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using this
    have : ∑ k, (∫ ω', frozenUpd Fp S ϱ t ω' k j ∂P) * Sp.u i k =
        ∫ ω', ∑ k, frozenUpd Fp S ϱ t ω' k j * Sp.u i k ∂P := by
      rw [integral_finset_sum _ (fun k _ => (vz_entry_int Fp S hϱ t k j).mul_const _)]
      exact Finset.sum_congr rfl fun k _ => (integral_mul_const _ _).symm
    rw [this]
    simp [hj]
  unfold centredUpd
  rw [Matrix.transpose_sub, Matrix.sub_mulVec, h0 ω, hmean, sub_zero]

private lemma vz_trace_zero {m n : ℕ} (u : Vec m) (A Bm : Mat m n) (hA : Aᵀ *ᵥ u = 0) :
    Matrix.trace (outer u u * A * (1 : Mat n n) * Bmᵀ) = 0 := by
  have h : outer u u * A = 0 := by
    ext a b
    simp only [outer, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
    have := congrFun hA b
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at this
    calc ∑ x, u a * u x * A x b = u a * ∑ x, A x b * u x := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      _ = 0 := by rw [this, mul_zero]
  rw [h]; simp

/-- `thm:app-vol-mode-kernels`, part (iv), second clause: a row with `μ_i = 0` has vanishing
deterministic coefficients `C̄_{i,ℓ}`, `𝔳_i`, and vanishing actual coefficients `C_{i,ℓ}` (`rowLag`,
all times) and `Γ_i` (`rowGamma`). Snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex`
(the whole environment):

\begin{theorem}[Mode-resolved coefficients, $\Sigmain=\Id$]\label{thm:app-vol-mode-kernels}
Let $\Sigmain=\Id_{\Nin}$.
\begin{enumerate}[label=(\roman*)]
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\begin{equation}\label{eqn:app-vol-rows-lag}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{C_{i,\ell}(\ridge,\ridge')-\overline C_{i,\ell}(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item At every finite dimension, $B^{-1}\sum_i\abs{\overline C_{i,0}}\le\gamma_\star$ and
$B^{-1}\sum_i\abs{\overline C_{i,\ell}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same bounds
hold for $C_{i,\ell}$ under \cref{assum:app-setup-regime}.
\item Each series $\mathfrak v_i$ converges absolutely, $\mathfrak v_i(\ridge)\ge0$, and
under \cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-rows-integrated}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{\Gamma_i(\ridge,\ridge')-\mathfrak v_i(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item The coefficients $\overline C_{i,\ell}$ and $\mathfrak v_i$ depend on $i$ only
through $\mu_i$, and vanish when $\mu_i=0$, as do $C_{i,\ell}$ and $\Gamma_i$. At
$\bmom=0$, $\overline C_{i,\ell}=0$ for $\ell\ge1$. At zero lag and equal ridges,
$\overline C_{i,0}(\ridge,\ridge)=\volraw_i(\ridge)$ of \cref{eqn:app-vol-half-candidates}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_mode_kernels_iv_vanish {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : FrozenSamples P m n B) (Sp : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (hId : Fp.C.Sin = 1)
    (i : Fin m) (hμ : Sp.μ i = 0) (ℓ : ℕ) (ϱ ϱ' : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') :
    lagRowBar cert γstar CSig Fp.β ℓ B Sp.μ Sp.lam i ϱ ϱ' = 0 ∧
      rowVBar cert γstar CSig Fp.β B Sp.μ Sp.lam i ϱ ϱ' = 0 ∧
      (∀ t : ℤ, rowLag Fp S Sp i ℓ t ϱ ϱ' = 0) ∧
      (∀ t : ℤ, rowGamma Fp S Sp i t ϱ ϱ' = 0) := by
  have hF : ∀ k, Sp.μ k * (Pi.single i (1 : ℝ) : Fin m → ℝ) k = 0 := by
    intro k
    by_cases h : k = i
    · subst h; simp [hμ]
    · simp [Pi.single_apply, h]
  have hbar : ∀ (ℓ : ℕ) (x y : ℝ), lagRowBar cert γstar CSig Fp.β ℓ B Sp.μ Sp.lam i x y = 0 := by
    intro ℓ x y
    unfold lagRowBar
    rw [vz_lagResp_zero_F cert γstar CSig Fp.β ℓ B Sp.μ Sp.lam _ _ hF, mul_zero]
  have hrow : ∀ (ℓ : ℕ) (t : ℤ) (x y : ℝ), 0 < x → 0 < y → rowLag Fp S Sp i ℓ t x y = 0 := by
    intro ℓ t x y hx hy
    unfold rowLag def_app_vol_lag
    have : ∀ ω, Matrix.trace (outer (Sp.u i) (Sp.u i) * centredUpd Fp S x t ω * (1 : Mat n n) *
        (centredUpd Fp S y (t + (ℓ : ℤ)) ω)ᵀ) = 0 := fun ω =>
      vz_trace_zero _ _ _ (vz_cent_row Fp S Sp hx t i hμ ω)
    simp only [this, integral_zero, mul_zero]
  refine ⟨hbar ℓ ϱ ϱ', ?_, fun t => hrow ℓ t ϱ ϱ' hϱ hϱ', fun t => ?_⟩
  · unfold rowVBar
    simp [hbar]
  · unfold rowGamma
    simp [hrow _ t ϱ ϱ' hϱ hϱ', hrow _ t ϱ' ϱ hϱ' hϱ]

/-- `thm:app-vol-mode-kernels`, part (iv), third clause: at `β = 0` the deterministic lag-`ℓ`
row coefficients vanish for `ℓ ≥ 1`. Snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex`
(the whole environment):

\begin{theorem}[Mode-resolved coefficients, $\Sigmain=\Id$]\label{thm:app-vol-mode-kernels}
Let $\Sigmain=\Id_{\Nin}$.
\begin{enumerate}[label=(\roman*)]
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\begin{equation}\label{eqn:app-vol-rows-lag}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{C_{i,\ell}(\ridge,\ridge')-\overline C_{i,\ell}(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item At every finite dimension, $B^{-1}\sum_i\abs{\overline C_{i,0}}\le\gamma_\star$ and
$B^{-1}\sum_i\abs{\overline C_{i,\ell}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same bounds
hold for $C_{i,\ell}$ under \cref{assum:app-setup-regime}.
\item Each series $\mathfrak v_i$ converges absolutely, $\mathfrak v_i(\ridge)\ge0$, and
under \cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-rows-integrated}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{\Gamma_i(\ridge,\ridge')-\mathfrak v_i(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item The coefficients $\overline C_{i,\ell}$ and $\mathfrak v_i$ depend on $i$ only
through $\mu_i$, and vanish when $\mu_i=0$, as do $C_{i,\ell}$ and $\Gamma_i$. At
$\bmom=0$, $\overline C_{i,\ell}=0$ for $\ell\ge1$. At zero lag and equal ridges,
$\overline C_{i,0}(\ridge,\ridge)=\volraw_i(\ridge)$ of \cref{eqn:app-vol-half-candidates}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_mode_kernels_iv_beta0 (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (hId : Fp.C.Sin = 1) (hβ : Fp.β = 0) (i : Fin m) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (ϱ ϱ' : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') :
    lagRowBar cert γstar CSig Fp.β ℓ B S.μ S.lam i ϱ ϱ' = 0 := by
  have hF : opNorm (S.uOut * Matrix.diagonal (Pi.single i 1 : Fin m → ℝ) * S.uOutᵀ) ≤ 1 := by
    refine (md_FG_norm (Fp := Fp) (n := n) S _ ?_).1
    intro i'
    by_cases h : i' = i <;> simp [Pi.single_apply, h]
  have h := (thm_app_vol_integrated_ii cert γstar CSig Fp S hS hCSig (min ϱ ϱ') (max ϱ ϱ')
    ⟨lt_min hϱ hϱ', min_le_max⟩ _ _ (Pi.single i 1) (fun _ => 1) rfl rfl ϱ ϱ'
    ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩).2.2 hβ ℓ hℓ
  unfold lagRowBar
  rw [h, mul_zero]

/-- `thm:app-vol-mode-kernels`, part (iv), fourth clause (zero lag, equal ridges): the deterministic
zero-lag row coefficient is the same-step raw volatility, `C̄_{i,0}(ϱ,ϱ) = volraw_i(ϱ)` (the
identity `eqn:app-vol-marginals-tests`). Snapshot `cr-2026-10-23`. LaTeX, verbatim from
`section.tex` (the whole environment):

\begin{theorem}[Mode-resolved coefficients, $\Sigmain=\Id$]\label{thm:app-vol-mode-kernels}
Let $\Sigmain=\Id_{\Nin}$.
\begin{enumerate}[label=(\roman*)]
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\begin{equation}\label{eqn:app-vol-rows-lag}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{C_{i,\ell}(\ridge,\ridge')-\overline C_{i,\ell}(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item At every finite dimension, $B^{-1}\sum_i\abs{\overline C_{i,0}}\le\gamma_\star$ and
$B^{-1}\sum_i\abs{\overline C_{i,\ell}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same bounds
hold for $C_{i,\ell}$ under \cref{assum:app-setup-regime}.
\item Each series $\mathfrak v_i$ converges absolutely, $\mathfrak v_i(\ridge)\ge0$, and
under \cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-rows-integrated}
\sup_{\ridge,\ridge'\in I}\frac1B\sum_{i=1}^{\Nout}\abs{\Gamma_i(\ridge,\ridge')-\mathfrak v_i(\ridge,\ridge')}\longrightarrow0 .
\end{equation}
\item The coefficients $\overline C_{i,\ell}$ and $\mathfrak v_i$ depend on $i$ only
through $\mu_i$, and vanish when $\mu_i=0$, as do $C_{i,\ell}$ and $\Gamma_i$. At
$\bmom=0$, $\overline C_{i,\ell}=0$ for $\ell\ge1$. At zero lag and equal ridges,
$\overline C_{i,0}(\ridge,\ridge)=\volraw_i(\ridge)$ of \cref{eqn:app-vol-half-candidates}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_mode_kernels_iv_zero_lag (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (hId : Fp.C.Sin = 1) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut Fp.C B) (hν' : (ν' : Measure ℝ) = Muon.nuIn Fp.C B)
    (i : Fin m) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    lagRowBar cert γstar CSig Fp.β 0 B S.μ S.lam i ϱ ϱ = volraw Fp.β ν ν' (S.μ i) ϱ := by
  exact (cor_app_vol_marginals_tests cert γstar CSig Fp S hS hCSig ν ν' hν hν' ϱ hϱ).1 i

/-! ### Private coupling helpers (copied from `LagReduction`, prefix `mt_`/`mti_`) -/

section MtCopy
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}

private lemma mt_fro_nn {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma mt_fro_transpose {k l : ℕ} (A : Mat k l) : fro Aᵀ = fro A := by
  unfold fro
  congr 1
  exact Finset.sum_comm

private lemma mt_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma mt_opNorm_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ opNorm A := by
  unfold opNorm
  exact norm_nonneg _

private lemma mt_fro_sq {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma mt_fro_mul_le_left {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ opNorm M * fro N := by
  have hcol : ∀ j : Fin r, ∑ i, (M * N) i j ^ 2 ≤ opNorm M ^ 2 * ∑ k, N k j ^ 2 := by
    intro j
    obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin q), ∀ k, v.ofLp k = N k j :=
      ⟨(EuclideanSpace.equiv (Fin q) ℝ).symm (fun k => N k j), fun k => rfl⟩
    have h1 : ‖(EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)‖ ≤ opNorm M * ‖v‖ := by
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
    rw [mt_fro_sq, mul_pow, mt_fro_sq, Finset.sum_comm]
    calc ∑ j, ∑ i, (M * N) i j ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, N k j ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, N k j ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (mt_fro_nn _) (mul_nonneg (mt_opNorm_nonneg M) (mt_fro_nn N))
    two_ne_zero).mp hfro

private lemma mt_fro_mul_le_right {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ fro M * opNorm N := by
  have h := mt_fro_mul_le_left Nᵀ Mᵀ
  rw [mt_opNorm_transpose, mt_fro_transpose, ← Matrix.transpose_mul, mt_fro_transpose] at h
  linarith [mul_comm (opNorm N) (fro M)]

private lemma mt_fro_sandwich {m n : ℕ} (F : Mat m m) (D : Mat m n) (G : Mat n n)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) : fro (F * D * G) ≤ fro D := by
  have h1 : opNorm F * fro D ≤ fro D := mul_le_of_le_one_left (mt_fro_nn D) hF
  calc fro (F * D * G) ≤ fro (F * D) * opNorm G := mt_fro_mul_le_right _ _
    _ ≤ (opNorm F * fro D) * opNorm G :=
        mul_le_mul_of_nonneg_right (mt_fro_mul_le_left _ _) (mt_opNorm_nonneg _)
    _ ≤ fro D * 1 := mul_le_mul h1 hG (mt_opNorm_nonneg G) (mt_fro_nn D)
    _ = fro D := mul_one _

private lemma mt_trace_mul_transpose_le {m n : ℕ} (X C : Mat m n) :
    |Matrix.trace (X * Cᵀ)| ≤ fro X * fro C := by
  have htr : Matrix.trace (X * Cᵀ) = ∑ p : Fin m × Fin n, X p.1 p.2 * C p.1 p.2 := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [htr]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
    (fun p => X p.1 p.2) (fun p => C p.1 p.2)
  have hX : ∑ p : Fin m × Fin n, X p.1 p.2 ^ 2 = fro X ^ 2 := by
    rw [mt_fro_sq, Fintype.sum_prod_type]
  have hC : ∑ p : Fin m × Fin n, C p.1 p.2 ^ 2 = fro C ^ 2 := by
    rw [mt_fro_sq, Fintype.sum_prod_type]
  rw [hX, hC] at cs
  refine (pow_le_pow_iff_left₀ (abs_nonneg _) (mul_nonneg (mt_fro_nn X) (mt_fro_nn C))
    two_ne_zero).mp ?_
  rw [sq_abs, mul_pow]
  exact cs

/-- Tested pairing bound `|Tr[F X G Yᵀ]| ≤ ‖X‖_F ‖Y‖_F` for contractions `F`, `G`. -/
private lemma mt_tested_le {m n : ℕ} (Fo : Mat m m) (Gi : Mat n n) (hF : opNorm Fo ≤ 1)
    (hG : opNorm Gi ≤ 1) (X Y : Mat m n) :
    |Matrix.trace (Fo * X * Gi * Yᵀ)| ≤ fro X * fro Y :=
  (mt_trace_mul_transpose_le (Fo * X * Gi) Y).trans
    (mul_le_mul_of_nonneg_right (mt_fro_sandwich Fo X Gi hF hG) (mt_fro_nn Y))

private lemma mt_abs_entry_le_fro {m n : ℕ} (K : Mat m n) (i : Fin m) (j : Fin n) :
    |K i j| ≤ fro K := by
  unfold fro
  apply Real.abs_le_sqrt
  have h1 : ‖K i j‖ ^ 2 ≤ ∑ j', ‖K i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖K i j'‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖K i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖K i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖K i' j'‖ ^ 2)
      (fun i' _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
  have h3 : ‖K i j‖ ^ 2 = K i j ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  linarith

private lemma mt_borel (m n : ℕ) : BorelSpace (Mat m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))

private lemma mt_sc (m n : ℕ) : SecondCountableTopology (Mat m n) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))

private lemma mt_tsum_meas {Ω' : Type*} (m1 : MeasurableSpace Ω') (f : ℕ → Ω' → Mat m n)
    (hf : ∀ j, Measurable[m1] (f j)) : Measurable[m1] (fun ω => ∑' j, f j ω) := by
  letI : MeasurableSpace Ω' := m1
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  exact Measurable.tsum hf

private lemma mt_Q_meas {ϱ : ℝ} (hϱ : 0 ≤ ϱ) : Measurable (fun K : Mat m n => Q ϱ K) :=
  (measurable_Q (m := m) (n := n)).comp
    ((measurable_const (a := (⟨ϱ, hϱ⟩ : Set.Ici (0 : ℝ)))).prodMk measurable_id)

private lemma mt_trace_cont {m n : ℕ} (Fo : Mat m m) (Gi : Mat n n) :
    Continuous (fun p : Mat m n × Mat m n => Matrix.trace (Fo * p.1 * Gi * p.2ᵀ)) := by
  fun_prop

/-- Integrability of the tested pairing of two bounded measurable random matrices. -/
private lemma mt_trace_integrable [IsProbabilityMeasure P] (Fo : Mat m m) (Gi : Mat n n)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1) (X Y : Ω → Mat m n) (hX : Measurable X)
    (hY : Measurable Y) (D D' : ℝ) (hXD : ∀ ω, fro (X ω) ≤ D) (hYD : ∀ ω, fro (Y ω) ≤ D') :
    Integrable (fun ω => Matrix.trace (Fo * X ω * Gi * (Y ω)ᵀ)) P := by
  haveI := mt_borel m n
  haveI := mt_sc m n
  refine Integrable.of_bound (C := D * D') ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((mt_trace_cont Fo Gi).measurable.comp (hX.prodMk hY)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact (mt_tested_le Fo Gi hF hG _ _).trans
      (mul_le_mul (hXD ω) (hYD ω) (mt_fro_nn _) ((mt_fro_nn _).trans (hXD ω)))


private lemma mt_fsum_meas {Ω' : Type*} {m1 : MeasurableSpace Ω'} (f : ℕ → Ω' → Mat m n) (s : Finset ℕ)
    (hf : ∀ j ∈ s, Measurable[m1] (f j)) : Measurable[m1] (fun ω => ∑ j ∈ s, f j ω) := by
  letI : MeasurableSpace Ω' := m1
  haveI := mt_borel m n
  haveI := mt_sc m n
  exact Finset.measurable_sum _ hf

private lemma mt_expand (Fo : Mat m m) (Gi : Mat n n) (X N : Mat m n) :
    Matrix.trace (Fo * X * Gi * Nᵀ) = ∑ a, ∑ b, X a b * (Gi * Nᵀ * Fo) b a := by
  have h : Matrix.trace (Fo * X * Gi * Nᵀ) = Matrix.trace (X * (Gi * Nᵀ * Fo)) := by
    rw [show Fo * X * Gi * Nᵀ = Fo * (X * Gi * Nᵀ) by simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  rw [h]
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

private lemma mt_Q_fro_le {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (K : Mat m n) :
    fro (Q ϱ K) ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
  obtain ⟨-, h2, h3, -⟩ := lem_app_setup_filter_i ϱ hϱ K
  exact Real.le_sqrt_of_sq_le (h2.trans (by exact_mod_cast h3))

private lemma mt_int_mul_bdd [IsProbabilityMeasure P] (φ ψ : Ω → ℝ) (hφ : Measurable φ)
    (hψ : Measurable ψ) (c d : ℝ) (hc : ∀ ω, |φ ω| ≤ c) (hd : ∀ ω, |ψ ω| ≤ d) :
    Integrable (fun ω => φ ω * ψ ω) P := by
  refine Integrable.of_bound (C := c * d) (hφ.mul hψ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hc ω) (hd ω) (abs_nonneg _) ((abs_nonneg _).trans (hc ω))

private lemma mt_cs [IsProbabilityMeasure P] (a b : Ω → ℝ) (ha : Measurable a)
    (hb : Measurable b) (hA : Integrable (fun ω => a ω ^ 2) P)
    (hB : Integrable (fun ω => b ω ^ 2) P) :
    (∫ ω, a ω * b ω ∂P) ^ 2 ≤ (∫ ω, a ω ^ 2 ∂P) * (∫ ω, b ω ^ 2 ∂P) := by
  have hab : Integrable (fun ω => a ω * b ω) P := by
    refine Integrable.mono' ((hA.add hB).div_const 2) (ha.mul hb).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith [sq_nonneg (a ω + b ω), sq_nonneg (a ω - b ω)]
  have hq : ∀ x : ℝ, 0 ≤ (∫ ω, a ω ^ 2 ∂P) * (x * x) + (-2 * ∫ ω, a ω * b ω ∂P) * x +
      ∫ ω, b ω ^ 2 ∂P := by
    intro x
    have h1 : ∫ ω, (x * a ω - b ω) ^ 2 ∂P = (∫ ω, a ω ^ 2 ∂P) * (x * x) +
        (-2 * ∫ ω, a ω * b ω ∂P) * x + ∫ ω, b ω ^ 2 ∂P := by
      have e : (fun ω => (x * a ω - b ω) ^ 2) =
          fun ω => (x * x) * a ω ^ 2 - (2 * x) * (a ω * b ω) + b ω ^ 2 := by
        funext ω; ring
      have i1 : Integrable (fun ω => (x * x) * a ω ^ 2) P := hA.const_mul _
      have i2 : Integrable (fun ω => (2 * x) * (a ω * b ω)) P := hab.const_mul _
      have i3 : Integrable (fun ω => (x * x) * a ω ^ 2 - (2 * x) * (a ω * b ω)) P := i1.sub i2
      rw [e, integral_add i3 hB, integral_sub i1 i2, integral_const_mul,
        integral_const_mul]
      ring
    rw [← h1]
    exact integral_nonneg fun ω => sq_nonneg _
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith [this]

private lemma mt_numeric (γ CSig ϱlo ϱ' β b I0 x0 d0 mm nn c1 s2 V : ℝ) (ℓ : ℕ)
    (hb : 1 ≤ b) (hγ : 0 ≤ γ) (hC : 0 ≤ CSig) (hϱlo : 0 < ϱlo) (hϱ' : ϱlo ≤ ϱ')
    (hβ : 0 ≤ β) (hI : I0 ^ 2 ≤ x0 * d0) (hx0 : x0 ≤ γ * b) (hx0n : 0 ≤ x0)
    (hd0n : 0 ≤ d0) (hd0 : d0 ≤ ϱ'⁻¹ * (β ^ (2 * ℓ) * (c1 + s2 * V)))
    (hc1 : 0 ≤ c1) (hc1' : c1 ≤ CSig ^ 2) (hs2 : 0 ≤ s2) (hs2' : s2 ≤ 1)
    (hV : 0 ≤ V) (hV' : V ≤ CSig ^ 2 * (mm * nn + 2 * mm + 2 * nn + 3) / b)
    (hmm : 0 ≤ mm) (hmm' : mm ≤ γ * b) (hnn : 0 ≤ nn) (hnn' : nn ≤ γ * b) :
    |b⁻¹ * I0| ≤ CSig * Real.sqrt (2 * γ * (γ ^ 2 + 4 * γ + 3) / ϱlo) * β ^ ℓ := by
  have hbpos : 0 < b := by linarith
  have hZ : 0 ≤ 2 * γ * (γ ^ 2 + 4 * γ + 3) / ϱlo := by positivity
  have hR : 0 ≤ CSig * Real.sqrt (2 * γ * (γ ^ 2 + 4 * γ + 3) / ϱlo) * β ^ ℓ := by positivity
  refine abs_le_of_sq_le_sq ?_ hR
  have hVb : V ≤ CSig ^ 2 * (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b := by
    refine hV'.trans ?_
    refine div_le_div_of_nonneg_right ?_ hbpos.le
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    nlinarith [mul_le_mul hmm' hnn' hnn (by positivity : 0 ≤ γ * b)]
  have hsV : s2 * V ≤ V := mul_le_of_le_one_left hV hs2'
  have hinv : ϱ'⁻¹ ≤ ϱlo⁻¹ := inv_anti₀ hϱlo hϱ'
  have hbeta : 0 ≤ β ^ (2 * ℓ) := by positivity
  have hd1 : d0 ≤ ϱlo⁻¹ * (β ^ (2 * ℓ) * (CSig ^ 2 +
      CSig ^ 2 * (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b)) := by
    refine hd0.trans ?_
    have h1 : c1 + s2 * V ≤ CSig ^ 2 + CSig ^ 2 * (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b := by
      linarith
    have h2 : 0 ≤ c1 + s2 * V := by positivity
    calc ϱ'⁻¹ * (β ^ (2 * ℓ) * (c1 + s2 * V))
        ≤ ϱlo⁻¹ * (β ^ (2 * ℓ) * (c1 + s2 * V)) :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hbeta) (by positivity)
  have hkey : (1 + (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b) / b ≤ γ ^ 2 + 4 * γ + 4 := by
    have e : (1 + (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b) / b =
        (b + γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b ^ 2 := by
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hγ (sub_nonneg.mpr hb), sq_nonneg (b - 1), mul_nonneg hγ hbpos.le]
  have hfin : (b⁻¹ * I0) ^ 2 ≤ γ * d0 / b := by
    calc (b⁻¹ * I0) ^ 2 = I0 ^ 2 / b ^ 2 := by field_simp
      _ ≤ (x0 * d0) / b ^ 2 := div_le_div_of_nonneg_right hI (by positivity)
      _ ≤ (γ * b * d0) / b ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hx0 hd0n) (by positivity)
      _ = γ * d0 / b := by field_simp
  have hRsq : (CSig * Real.sqrt (2 * γ * (γ ^ 2 + 4 * γ + 3) / ϱlo) * β ^ ℓ) ^ 2 =
      ϱlo⁻¹ * (β ^ (2 * ℓ) * (CSig ^ 2 * (2 * γ * (γ ^ 2 + 4 * γ + 3)))) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hZ, ← pow_mul, mul_comm ℓ 2]
    field_simp
  rw [hRsq]
  calc (b⁻¹ * I0) ^ 2 ≤ γ * d0 / b := hfin
    _ ≤ γ * (ϱlo⁻¹ * (β ^ (2 * ℓ) * (CSig ^ 2 +
          CSig ^ 2 * (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b))) / b :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd1 hγ) hbpos.le
    _ = ϱlo⁻¹ * (β ^ (2 * ℓ) * (CSig ^ 2 * γ *
          ((1 + (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b) / b))) := by
        field_simp
    _ ≤ ϱlo⁻¹ * (β ^ (2 * ℓ) * (CSig ^ 2 * γ * (γ ^ 2 + 4 * γ + 4))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hbeta) (by positivity)
        exact mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hbeta) (by positivity)
        nlinarith [mul_nonneg (sq_nonneg CSig) hγ, mul_nonneg (mul_nonneg (sq_nonneg CSig) hγ)
          (by positivity : (0:ℝ) ≤ γ ^ 2 + 4 * γ + 2)]

private lemma mt_fro_triangle (K L : Mat m n) : fro (K - L) ≤ fro K + fro L := by
  have h := mt_fro_sq (K - L)
  have hK := mt_fro_sq K
  have hL := mt_fro_sq L
  have hcs : (∑ i, ∑ j, K i j * L i j) ≤ fro K * fro L := by
    have := mt_trace_mul_transpose_le K L
    have htr : Matrix.trace (K * Lᵀ) = ∑ i, ∑ j, K i j * L i j := by
      simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    rw [htr] at this
    exact (le_abs_self _).trans this
  have hexp : fro (K - L) ^ 2 = fro K ^ 2 + fro L ^ 2 - 2 * ∑ i, ∑ j, K i j * L i j := by
    rw [h, hK, hL]
    simp only [Matrix.sub_apply, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum]
    ring_nf
  have hle : fro (K - L) ^ 2 ≤ (fro K + fro L) ^ 2 := by
    rw [hexp]
    have : 0 ≤ ∑ i, ∑ j, K i j * L i j + fro K * fro L := by
      have h0 := mt_trace_mul_transpose_le K L
      have htr : Matrix.trace (K * Lᵀ) = ∑ i, ∑ j, K i j * L i j := by
        simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      rw [htr] at h0
      have := neg_abs_le (∑ i, ∑ j, K i j * L i j)
      linarith
    nlinarith
  exact (pow_le_pow_iff_left₀ (mt_fro_nn _) (add_nonneg (mt_fro_nn _) (mt_fro_nn _))
    two_ne_zero).mp hle

private lemma mt_fro_meas : Measurable (fun K : Mat m n => fro K) := by
  unfold fro
  fun_prop

/-- Expansion of the trace pairing against a difference in the second slot. -/
private lemma mt_trace_sub_right {m n : ℕ} (Fo : Mat m m) (Gi : Mat n n) (X Y N : Mat m n) :
    Matrix.trace (Fo * X * Gi * (Y - N)ᵀ) =
      Matrix.trace (Fo * X * Gi * Yᵀ) - Matrix.trace (Fo * X * Gi * Nᵀ) := by
  rw [Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub]

private lemma mti_prob (m n B : ℕ) : IsProbabilityMeasure (indepSpaceLaw m n B) := by
  unfold indepSpaceLaw indepSlotLaw
  infer_instance

private lemma mti_fro_smul {k l : ℕ} (c : ℝ) (K : Mat k l) : fro (c • K) = |c| * fro K := by
  have h : ∀ i j, ‖(c • K) i j‖ ^ 2 = c ^ 2 * ‖K i j‖ ^ 2 := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs, mul_pow, sq_abs]
  unfold fro
  simp only [h, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

private lemma mti_batch_meas_sub (F : FrozenParams m n B) (s : ℤ) (T : Set (ℤ × Fin B))
    (hT : ∀ a, (s, a) ∈ T) :
    Measurable[⨆ i ∈ T, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance]
      (fun ω => indepBatchG F ω s) := by
  have h : ∀ a, Measurable[⨆ i ∈ T, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance]
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω (s, a)) := fun a =>
    Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ T) => MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance) (s, a) (hT a))
  generalize (⨆ i ∈ T, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance) = m1 at h ⊢
  letI : MeasurableSpace ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) := m1
  haveI := mt_borel m n
  haveI := mt_sc m n
  unfold indepBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : ℝ × (Vec m × Vec n) =>
      p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (h a)

private lemma mti_prod_meas (F : FrozenParams m n B) (s : ℤ) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => def_app_vol_product F ω s) := by
  haveI := mt_borel m n
  haveI := mt_sc m n
  unfold def_app_vol_product
  refine mt_tsum_meas _ _ fun j => ?_
  refine Measurable.const_smul ?_ (emaW F.β j)
  unfold indepBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : ℝ × (Vec m × Vec n) =>
      p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (measurable_pi_apply (s + 1 - (j : ℤ), a))

private lemma mti_batch_meas (F : FrozenParams m n B) (s : ℤ) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => indepBatchG F ω s) := by
  haveI := mt_borel m n
  haveI := mt_sc m n
  unfold indepBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : ℝ × (Vec m × Vec n) =>
      p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (measurable_pi_apply (s, a))

private lemma mti_indep (F : FrozenParams m n B) (t : ℤ) (ℓ : ℕ) :
    IndepFun (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => def_app_vol_product F ω t)
      (fun ω => ∑ j ∈ Finset.range ℓ,
        emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ)))
      (indepSpaceLaw m n B) := by
  haveI := mti_prob m n B
  have hI : iIndepFun (fun (p : ℤ × Fin B) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) => ω p)
      (indepSpaceLaw m n B) :=
    iIndepFun_infinitePi (P := fun _ : ℤ × Fin B => indepSlotLaw m n)
      (X := fun _ x => x) (fun _ => measurable_id)
  have hind := (iIndepFun_iff_iIndep
    (fun _ : ℤ × Fin B => (inferInstance : MeasurableSpace (ℝ × (Vec m × Vec n))))
    (fun (p : ℤ × Fin B) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) => ω p)
    (indepSpaceLaw m n B)).mp hI
  have hdisj : Disjoint {p : ℤ × Fin B | p.1 ≤ t + 1} {p : ℤ × Fin B | t + 2 ≤ p.1} := by
    rw [Set.disjoint_left]
    intro p h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    omega
  have key := indep_iSup_of_disjoint
    (fun p : ℤ × Fin B => (measurable_pi_apply (X := fun _ : ℤ × Fin B => ℝ × (Vec m × Vec n)) p).comap_le)
    hind hdisj
  have hA : Measurable[⨆ i ∈ {p : ℤ × Fin B | p.1 ≤ t + 1}, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance]
      (fun ω => def_app_vol_product F ω t) := by
    unfold def_app_vol_product
    refine mt_tsum_meas _ _ fun j => ?_
    refine Measurable.const_smul ?_ (emaW F.β j)
    exact mti_batch_meas_sub F _ _ (fun a => by
      show t + 1 - (j : ℤ) ≤ t + 1
      omega)
  have hB : Measurable[⨆ i ∈ {p : ℤ × Fin B | t + 2 ≤ p.1}, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance]
      (fun ω => ∑ j ∈ Finset.range ℓ,
        emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ))) := by
    refine mt_fsum_meas _ _ fun j hj => ?_
    rw [Finset.mem_range] at hj
    refine Measurable.const_smul ?_ (emaW F.β j)
    exact mti_batch_meas_sub F _ _ (fun a => by
      show t + 2 ≤ t + (ℓ : ℤ) + 1 - (j : ℤ)
      omega)
  exact (IndepFun_iff_Indep _ _ (indepSpaceLaw m n B)).mpr
    (indep_of_indep_of_le_left (indep_of_indep_of_le_right key (measurable_iff_comap_le.mp hB))
      (measurable_iff_comap_le.mp hA))

private lemma mti_mean_zero (F : FrozenParams m n B) {ϱ : ℝ} (hϱ : 0 < ϱ) (t : ℤ)
    (a : Fin m) (b : Fin n) :
    ∫ ω, Q ϱ (def_app_vol_product F ω t) a b ∂(indepSpaceLaw m n B) = 0 := by
  have hodd : ∀ x : ℝ, omegaF ϱ (-x) = -omegaF ϱ x := by
    intro x
    simp [omegaF, neg_div]
  have hbdd : ∃ M : ℝ, ∀ x : ℝ, |omegaF ϱ x| ≤ M := by
    refine ⟨1, fun x => ?_⟩
    have hpos : 0 < Real.sqrt (x ^ 2 + ϱ) := Real.sqrt_pos.mpr (by positivity)
    unfold omegaF
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    exact Real.abs_le_sqrt (by linarith)
  have h := def_app_vol_product_mean_oddSharp F (omegaF ϱ) hodd hbdd t
  have h2 := congrFun (congrFun h a) b
  simp only [mean, Matrix.of_apply, Matrix.zero_apply] at h2
  have e : ∀ ω, oddSharp (omegaF ϱ) (def_app_vol_product F ω t) =
      Q ϱ (def_app_vol_product F ω t) := fun ω => eqn_app_vol_filters_sharp_ii hϱ _
  simp_rw [e] at h2
  exact h2

open scoped Matrix.Norms.Frobenius in
private lemma mti_decomp (F : FrozenParams m n B) (t : ℤ) (ℓ : ℕ) :
    ∀ᵐ ω ∂(indepSpaceLaw m n B), def_app_vol_product F ω (t + (ℓ : ℤ)) =
      (∑ j ∈ Finset.range ℓ, emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ))) +
      F.β ^ ℓ • def_app_vol_product F ω t := by
  filter_upwards [def_app_vol_product_summable F] with ω hω
  have hs : Summable fun j : ℕ =>
      emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ)) := by
    refine Summable.of_norm ?_
    simpa [fro_eq_norm] using hω (t + (ℓ : ℤ))
  unfold def_app_vol_product
  rw [← Summable.sum_add_tsum_nat_add' ((summable_nat_add_iff ℓ).2 hs)]
  congr 1
  have hshift : ∀ i : ℕ, emaW F.β (i + ℓ) • indepBatchG F ω (t + (ℓ : ℤ) + 1 - ((i + ℓ : ℕ) : ℤ)) =
      F.β ^ ℓ • (emaW F.β i • indepBatchG F ω (t + 1 - (i : ℤ))) := by
    intro i
    have e1 : t + (ℓ : ℤ) + 1 - ((i + ℓ : ℕ) : ℤ) = t + 1 - (i : ℤ) := by push_cast; ring
    have e2 : emaW F.β (i + ℓ) = F.β ^ ℓ * emaW F.β i := by
      unfold emaW; ring
    rw [e1, e2, smul_smul]
  simp_rw [hshift]
  exact tsum_const_smul'' _

private lemma mti_moment (F : FrozenParams m n B) (γstar CSig : ℝ)
    (hS : SizeFin F.C B γstar CSig) (t : ℤ) :
    Integrable (fun ω => fro (def_app_vol_product F ω t) ^ 2) (indepSpaceLaw m n B) ∧
    ∫ ω, fro (def_app_vol_product F ω t) ^ 2 ∂(indepSpaceLaw m n B) ≤
      CSig ^ 2 * γstar ^ 2 * B := by
  have hB : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hβ0 := F.hβ.1
  have hβ1 := F.hβ.2
  refine ⟨?_, ?_⟩
  · by_contra hni
    have h0 := integral_undef hni
    have hm := def_app_vol_product_moment F t
    rw [h0, mul_zero, sPow_two hβ0 hβ1] at hm
    have hs2 : 0 < (1 - F.β) / (1 + F.β) := div_pos (by linarith) (by linarith)
    have hB2 : (0 : ℝ) < (B : ℝ) ^ 2 := by positivity
    have hprod : Matrix.trace F.C.Sout * Matrix.trace F.C.Sin = 0 := by
      have h1 : (1 - F.β) / (1 + F.β) / (B : ℝ) ^ 2 * Matrix.trace F.C.Sout *
          Matrix.trace F.C.Sin = 0 := hm.symm
      have h2 : (1 - F.β) / (1 + F.β) / (B : ℝ) ^ 2 ≠ 0 := (div_pos hs2 hB2).ne'
      rw [mul_assoc] at h1
      exact (mul_eq_zero.mp h1).resolve_left h2
    have hG : ∀ ω s, indepBatchG F ω s = 0 := by
      intro ω s
      rcases mul_eq_zero.mp hprod with h | h
      · have h0 : F.C.Sout = 0 := (F.C.psdOut.trace_eq_zero_iff).mp h
        unfold indepBatchG
        simp [rOut, h0, CFC.sqrt_zero]
      · have h0 : F.C.Sin = 0 := (F.C.psdIn.trace_eq_zero_iff).mp h
        unfold indepBatchG
        simp [rIn, h0, CFC.sqrt_zero]
    have hz : ∀ ω, def_app_vol_product F ω t = 0 := by
      intro ω
      unfold def_app_vol_product
      simp [hG]
    apply hni
    have : (fun ω => fro (def_app_vol_product F ω t) ^ 2) = fun _ => 0 := by
      funext ω
      rw [hz]
      simp [fro]
    rw [this]
    exact integrable_zero _ _ _
  · have h := def_app_vol_product_moment_le F γstar CSig hS t
    rw [inv_mul_le_iff₀ hB] at h
    calc _ ≤ (B : ℝ) * (CSig ^ 2 * γstar ^ 2) := h
      _ = _ := by ring

private lemma mti_zero (F : FrozenParams m n B) (Fo : Mat m m) (Gi : Mat n n)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1) {ϱ ϱ' : ℝ} (hϱ : 0 < ϱ) (hϱ' : 0 ≤ ϱ') (t : ℤ)
    (Ntr : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n) (htr : Measurable Ntr)
    (hind : IndepFun (fun ω => def_app_vol_product F ω t) Ntr (indepSpaceLaw m n B)) :
    ∫ ω, Matrix.trace (Fo * Q ϱ (def_app_vol_product F ω t) * Gi * (Q ϱ' (Ntr ω))ᵀ)
      ∂(indepSpaceLaw m n B) = 0 := by
  haveI := mti_prob m n B
  haveI := mt_borel m n
  haveI := mt_sc m n
  obtain ⟨f, hf⟩ : ∃ f : Fin m → Fin n → Mat m n → ℝ, f = fun a b K => (Q ϱ K) a b :=
    ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin m → Fin n → Mat m n → ℝ, g = fun a b K =>
      (Gi * (Q ϱ' K)ᵀ * Fo) b a := ⟨_, rfl⟩
  have hfm : ∀ a b, Measurable (f a b) := fun a b => by
    rw [hf]
    exact (measurable_pi_apply b).comp ((measurable_pi_apply a).comp (mt_Q_meas hϱ.le))
  have hgm : ∀ a b, Measurable (g a b) := fun a b => by
    rw [hg]
    have hc : Continuous (fun N : Mat m n => (Gi * Nᵀ * Fo) b a) := by fun_prop
    exact hc.measurable.comp (mt_Q_meas hϱ')
  have hbuf := mti_prod_meas F t
  have e1 : ∀ ω, Matrix.trace (Fo * Q ϱ (def_app_vol_product F ω t) * Gi *
      (Q ϱ' (Ntr ω))ᵀ) = ∑ a, ∑ b,
        f a b (def_app_vol_product F ω t) * g a b (Ntr ω) := by
    intro ω
    rw [mt_expand, hf, hg]
  have hint : ∀ a b, Integrable (fun ω => f a b (def_app_vol_product F ω t) *
      g a b (Ntr ω)) (indepSpaceLaw m n B) := by
    intro a b
    refine mt_int_mul_bdd _ _ ((hfm a b).comp hbuf) ((hgm a b).comp htr)
      (Real.sqrt ((min m n : ℕ) : ℝ)) (Real.sqrt ((min m n : ℕ) : ℝ)) (fun ω => ?_) (fun ω => ?_)
    · have : f a b (def_app_vol_product F ω t) = Q ϱ (def_app_vol_product F ω t) a b := by
        rw [hf]
      rw [this]
      exact (mt_abs_entry_le_fro _ a b).trans (mt_Q_fro_le hϱ.le _)
    · have : g a b (Ntr ω) = (Gi * (Q ϱ' (Ntr ω))ᵀ * Fo) b a := by
        rw [hg]
      rw [this]
      refine (mt_abs_entry_le_fro _ b a).trans ?_
      refine (mt_fro_sandwich Gi _ Fo hG hF).trans ?_
      rw [mt_fro_transpose]
      exact mt_Q_fro_le hϱ' _
  simp_rw [e1]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hint a b))]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => hint a b)]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [hind.integral_fun_comp_mul_comp hbuf.aemeasurable htr.aemeasurable
    (hfm a b).aestronglyMeasurable (hgm a b).aestronglyMeasurable]
  have : ∫ ω, f a b (def_app_vol_product F ω t) ∂(indepSpaceLaw m n B) = 0 := by
    have e : ∀ ω, f a b (def_app_vol_product F ω t) = Q ϱ (def_app_vol_product F ω t) a b := by
      intro ω; rw [hf]
    simp_rw [e]
    exact mti_mean_zero F hϱ t a b
  rw [this, zero_mul]


private lemma mt_trace_atom {m n : ℕ} (U : Mat m m) (V : Mat n n) (dx : Fin m → ℝ) (ey : Fin n → ℝ)
    (X D : Mat m n) :
    Matrix.trace (U * Matrix.diagonal dx * Uᵀ * X * (V * Matrix.diagonal ey * Vᵀ) * Dᵀ) =
      ∑ a, ∑ b, dx a * ey b * ((Uᵀ * X * V) a b * (Uᵀ * D * V) a b) := by
  have h : Matrix.trace (U * Matrix.diagonal dx * Uᵀ * X * (V * Matrix.diagonal ey * Vᵀ) * Dᵀ) =
      Matrix.trace (Matrix.diagonal dx * (Uᵀ * X * V) * Matrix.diagonal ey * (Uᵀ * D * V)ᵀ) := by
    rw [show U * Matrix.diagonal dx * Uᵀ * X * (V * Matrix.diagonal ey * Vᵀ) * Dᵀ =
      U * (Matrix.diagonal dx * Uᵀ * X * V * Matrix.diagonal ey * Vᵀ * Dᵀ) by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h, mt_expand]
  generalize Uᵀ * X * V = Xt
  generalize Uᵀ * D * V = Dt
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
  ring

private lemma mt_fro_orth_le {m n : ℕ} (U : Mat m m) (V : Mat n n) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (X : Mat m n) : fro (Uᵀ * X * V) ≤ fro X := by
  have h1 : opNorm Uᵀ ≤ 1 := by
    refine md_opNorm_orth Uᵀ ?_
    rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hU
  exact mt_fro_sandwich _ _ _ h1 (md_opNorm_orth V hV)

private lemma mt_classDiag_nonneg {k : ℕ} (x : Fin k → ℝ) (μ : ℝ) (a : Fin k) :
    0 ≤ classDiag x μ a := by
  unfold classDiag; split_ifs <;> norm_num

private lemma mt_sum_classDiag {k : ℕ} (x : Fin k → ℝ) (a : Fin k) :
    ∑ μ ∈ Finset.univ.image x, classDiag x μ a = 1 := by
  unfold classDiag
  rw [Finset.sum_ite_eq]
  simp

private lemma mt_abs_sum_le_fro {m n : ℕ} (Xt Dt : Mat m n) :
    ∑ a, ∑ b, |Xt a b * Dt a b| ≤ fro Xt * fro Dt := by
  have htr : ∑ a, ∑ b, |Xt a b * Dt a b| = ∑ p : Fin m × Fin n, |Xt p.1 p.2| * |Dt p.1 p.2| := by
    rw [Fintype.sum_prod_type]
    simp [abs_mul]
  rw [htr]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
    (fun p => |Xt p.1 p.2|) (fun p => |Dt p.1 p.2|)
  have hX : ∑ p : Fin m × Fin n, |Xt p.1 p.2| ^ 2 = fro Xt ^ 2 := by
    rw [mt_fro_sq, Fintype.sum_prod_type]
    simp [sq_abs]
  have hC : ∑ p : Fin m × Fin n, |Dt p.1 p.2| ^ 2 = fro Dt ^ 2 := by
    rw [mt_fro_sq, Fintype.sum_prod_type]
    simp [sq_abs]
  rw [hX, hC] at cs
  refine (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun p _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (mul_nonneg (mt_fro_nn Xt) (mt_fro_nn Dt)) two_ne_zero).mp ?_
  rw [mul_pow]
  exact cs

private lemma mt_atoms_pointwise {m n : ℕ} (U : Mat m m) (V : Mat n n) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (x : Fin m → ℝ) (y : Fin n → ℝ) (X D : Mat m n) :
    ∑ μ ∈ Finset.univ.image x, ∑ l ∈ Finset.univ.image y,
      |Matrix.trace (U * Matrix.diagonal (classDiag x μ) * Uᵀ * X *
        (V * Matrix.diagonal (classDiag y l) * Vᵀ) * Dᵀ)| ≤ fro X * fro D := by
  have hz : ∀ μ l, |Matrix.trace (U * Matrix.diagonal (classDiag x μ) * Uᵀ * X *
        (V * Matrix.diagonal (classDiag y l) * Vᵀ) * Dᵀ)| ≤
      ∑ a, ∑ b, classDiag x μ a * classDiag y l b * |(Uᵀ * X * V) a b * (Uᵀ * D * V) a b| := by
    intro μ l
    rw [mt_trace_atom]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [abs_mul, abs_of_nonneg (mul_nonneg (mt_classDiag_nonneg x μ a) (mt_classDiag_nonneg y l b))]
  generalize hF : (fun a b => |(Uᵀ * X * V) a b * (Uᵀ * D * V) a b|) = F
  have hz' : ∀ μ l, |Matrix.trace (U * Matrix.diagonal (classDiag x μ) * Uᵀ * X *
        (V * Matrix.diagonal (classDiag y l) * Vᵀ) * Dᵀ)| ≤
      ∑ a, ∑ b, classDiag x μ a * classDiag y l b * F a b := by
    intro μ l
    rw [← hF]; exact hz μ l
  have hsum : ∑ μ ∈ Finset.univ.image x, ∑ l ∈ Finset.univ.image y,
      ∑ a, ∑ b, classDiag x μ a * classDiag y l b * F a b = ∑ a, ∑ b, F a b := by
    have h1 : ∀ μ, ∑ l ∈ Finset.univ.image y, ∑ a, ∑ b, classDiag x μ a * classDiag y l b * F a b =
        ∑ a, ∑ b, classDiag x μ a * F a b := by
      intro μ
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      have : ∀ l, classDiag x μ a * classDiag y l b * F a b =
          (classDiag x μ a * F a b) * classDiag y l b := fun l => by ring
      simp_rw [this]
      rw [← Finset.mul_sum, mt_sum_classDiag, mul_one]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_mul, mt_sum_classDiag, one_mul]
  calc _ ≤ ∑ μ ∈ Finset.univ.image x, ∑ l ∈ Finset.univ.image y,
        ∑ a, ∑ b, classDiag x μ a * classDiag y l b * F a b :=
        Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun l _ => hz' μ l
    _ = ∑ a, ∑ b, F a b := hsum
    _ ≤ fro (Uᵀ * X * V) * fro (Uᵀ * D * V) := by rw [← hF]; exact mt_abs_sum_le_fro _ _
    _ ≤ fro X * fro D :=
        mul_le_mul (mt_fro_orth_le U V hU hV X) (mt_fro_orth_le U V hU hV D) (mt_fro_nn _)
          (mt_fro_nn _)

private lemma mt_proj_opNorm {m n : ℕ} {C : Covariances m n} (Sp : SpectralData C) (μ l : ℝ) :
    opNorm (projOut Sp μ) ≤ 1 ∧ opNorm (projIn Sp l) ≤ 1 := by
  constructor
  · exact md_opNorm_conj _ Sp.huOut _ (fun i => by
      unfold classDiag; split_ifs <;> simp)
  · exact md_opNorm_conj _ Sp.hvIn _ (fun i => by
      unfold classDiag; split_ifs <;> simp)

private lemma mt_atoms_integral_le [IsProbabilityMeasure P] {C : Covariances m n}
    (Sp : SpectralData C) (X D : Ω → Mat m n) (hX : Measurable X) (hD : Measurable D)
    (cX cD : ℝ) (hXb : ∀ ω, fro (X ω) ≤ cX) (hDb : ∀ ω, fro (D ω) ≤ cD) :
    ∑ μ ∈ muVals Sp, ∑ l ∈ lamVals Sp,
      |∫ ω, Matrix.trace (projOut Sp μ * X ω * projIn Sp l * (D ω)ᵀ) ∂P| ≤
      ∫ ω, fro (X ω) * fro (D ω) ∂P := by
  have hint : ∀ μ l, Integrable (fun ω => Matrix.trace (projOut Sp μ * X ω * projIn Sp l *
      (D ω)ᵀ)) P := fun μ l =>
    mt_trace_integrable _ _ (mt_proj_opNorm Sp μ l).1 (mt_proj_opNorm Sp μ l).2 X D hX hD cX cD
      hXb hDb
  have hfm : Measurable (fun ω => fro (X ω)) := mt_fro_meas.comp hX
  have hgm : Measurable (fun ω => fro (D ω)) := mt_fro_meas.comp hD
  have hfg : Integrable (fun ω => fro (X ω) * fro (D ω)) P :=
    mt_int_mul_bdd _ _ hfm hgm cX cD (fun ω => by rw [abs_of_nonneg (mt_fro_nn _)]; exact hXb ω)
      (fun ω => by rw [abs_of_nonneg (mt_fro_nn _)]; exact hDb ω)
  calc ∑ μ ∈ muVals Sp, ∑ l ∈ lamVals Sp,
        |∫ ω, Matrix.trace (projOut Sp μ * X ω * projIn Sp l * (D ω)ᵀ) ∂P|
      ≤ ∑ μ ∈ muVals Sp, ∑ l ∈ lamVals Sp,
        ∫ ω, |Matrix.trace (projOut Sp μ * X ω * projIn Sp l * (D ω)ᵀ)| ∂P :=
        Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun l _ =>
          abs_integral_le_integral_abs
    _ = ∫ ω, ∑ μ ∈ muVals Sp, ∑ l ∈ lamVals Sp,
        |Matrix.trace (projOut Sp μ * X ω * projIn Sp l * (D ω)ᵀ)| ∂P := by
        rw [integral_finsetSum _ (fun μ _ => integrable_finsetSum _ (fun l _ => (hint μ l).abs))]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [integral_finsetSum _ (fun l _ => (hint μ l).abs)]
    _ ≤ ∫ ω, fro (X ω) * fro (D ω) ∂P := by
        refine integral_mono (integrable_finsetSum _ (fun μ _ => integrable_finsetSum _
          (fun l _ => (hint μ l).abs))) hfg fun ω => ?_
        exact mt_atoms_pointwise Sp.uOut Sp.vIn Sp.huOut Sp.hvIn Sp.μ Sp.lam (X ω) (D ω)

private lemma mt_indep_tv_zero (F : FrozenParams m n B) (γstar CSig : ℝ)
    (hS : SizeFin F.C B γstar CSig) (Sp : SpectralData F.C) {ϱ ϱ' : ℝ} (hϱ : 0 ≤ ϱ)
    (hϱ' : 0 ≤ ϱ') (t : ℤ) :
    ∑ μ ∈ muVals Sp, ∑ l ∈ lamVals Sp,
      |(B : ℝ)⁻¹ * ∫ ω, Matrix.trace (projOut Sp μ * indepUpd F ϱ ω t * projIn Sp l *
        (indepUpd F ϱ' ω t)ᵀ) ∂(indepSpaceLaw m n B)| ≤ γstar := by
  haveI := mti_prob m n B
  haveI := mt_borel m n
  haveI := mt_sc m n
  have hB : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hmin : ((min m n : ℕ) : ℝ) ≤ γstar * B :=
    le_trans (by exact_mod_cast (min_le_max : min m n ≤ max m n)) hS.1
  have hXm : Measurable (fun ω => indepUpd F ϱ ω t) :=
    (mt_Q_meas hϱ).comp (mti_prod_meas F t)
  have hYm : Measurable (fun ω => indepUpd F ϱ' ω t) :=
    (mt_Q_meas hϱ').comp (mti_prod_meas F t)
  have hmain := mt_atoms_integral_le (P := indepSpaceLaw m n B) Sp _ _ hXm hYm
    (Real.sqrt ((min m n : ℕ) : ℝ)) (Real.sqrt ((min m n : ℕ) : ℝ))
    (fun ω => mt_Q_fro_le hϱ _) (fun ω => mt_Q_fro_le hϱ' _)
  have hcst : ∫ ω, fro (indepUpd F ϱ ω t) * fro (indepUpd F ϱ' ω t) ∂(indepSpaceLaw m n B) ≤
      ((min m n : ℕ) : ℝ) := by
    have : ∀ ω, fro (indepUpd F ϱ ω t) * fro (indepUpd F ϱ' ω t) ≤ ((min m n : ℕ) : ℝ) := by
      intro ω
      have h3 := mul_le_mul (mt_Q_fro_le (m := m) (n := n) hϱ (def_app_vol_product F ω t))
        (mt_Q_fro_le (m := m) (n := n) hϱ' (def_app_vol_product F ω t)) (mt_fro_nn _)
        (Real.sqrt_nonneg _)
      rw [Real.mul_self_sqrt (Nat.cast_nonneg _)] at h3
      exact h3
    calc _ ≤ ∫ _ω, ((min m n : ℕ) : ℝ) ∂(indepSpaceLaw m n B) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
            mul_nonneg (mt_fro_nn _) (mt_fro_nn _)) (integrable_const _)
            (Filter.Eventually.of_forall this)
      _ = _ := by simp
  have e : ∀ μ l, |(B : ℝ)⁻¹ * ∫ ω, Matrix.trace (projOut Sp μ * indepUpd F ϱ ω t *
      projIn Sp l * (indepUpd F ϱ' ω t)ᵀ) ∂(indepSpaceLaw m n B)| =
      (B : ℝ)⁻¹ * |∫ ω, Matrix.trace (projOut Sp μ * indepUpd F ϱ ω t *
      projIn Sp l * (indepUpd F ϱ' ω t)ᵀ) ∂(indepSpaceLaw m n B)| := fun μ l => by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hB)]
  have hsum : ∑ μ ∈ muVals Sp, ∑ l ∈ lamVals Sp, |(B : ℝ)⁻¹ * ∫ ω, Matrix.trace (projOut Sp μ *
      indepUpd F ϱ ω t * projIn Sp l * (indepUpd F ϱ' ω t)ᵀ) ∂(indepSpaceLaw m n B)| =
      (B : ℝ)⁻¹ * ∑ μ ∈ muVals Sp, ∑ l ∈ lamVals Sp, |∫ ω, Matrix.trace (projOut Sp μ *
      indepUpd F ϱ ω t * projIn Sp l * (indepUpd F ϱ' ω t)ᵀ) ∂(indepSpaceLaw m n B)| := by
    simp_rw [e, ← Finset.mul_sum]
  rw [hsum, inv_mul_le_iff₀ hB]
  calc _ ≤ ((min m n : ℕ) : ℝ) := hmain.trans hcst
    _ ≤ γstar * B := hmin
    _ = B * γstar := mul_comm _ _

private lemma mt_indep_tv_pos (F : FrozenParams m n B) (γstar CSig ϱlo : ℝ)
    (hS : SizeFin F.C B γstar CSig) (Sp : SpectralData F.C) (hϱlo : 0 < ϱlo)
    {ϱ ϱ' : ℝ} (hϱ1 : ϱlo ≤ ϱ) (hϱ'1 : ϱlo ≤ ϱ') (t : ℤ) (ℓ : ℕ) :
    ∑ μ ∈ muVals Sp, ∑ l ∈ lamVals Sp,
      |(B : ℝ)⁻¹ * ∫ ω, Matrix.trace (projOut Sp μ * indepUpd F ϱ ω t * projIn Sp l *
        (indepUpd F ϱ' ω (t + (ℓ : ℤ)))ᵀ) ∂(indepSpaceLaw m n B)| ≤
      Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ ℓ := by
  have hϱ0' : 0 < ϱ := lt_of_lt_of_le hϱlo hϱ1
  have hϱ'pos : 0 < ϱ' := lt_of_lt_of_le hϱlo hϱ'1
  haveI := mti_prob m n B
  haveI := mt_borel m n
  haveI := mt_sc m n
  have hBpos : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast F.hB
  obtain ⟨hβ0, hβ1⟩ := F.hβ
  have hγ : 0 ≤ γstar := by
    have h1 : (0 : ℝ) ≤ ((max m n : ℕ) : ℝ) := Nat.cast_nonneg _
    have := hS.1
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg hBpos]
  have hCs : 0 ≤ CSig := le_trans (mt_opNorm_nonneg _) hS.2.1
  have hminle : ((min m n : ℕ) : ℝ) ≤ γstar * B :=
    le_trans (by exact_mod_cast (min_le_max : min m n ≤ max m n)) hS.1
  obtain ⟨Nl, hNl⟩ : ∃ Nl : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n,
      Nl = fun ω => ∑ j ∈ Finset.range ℓ,
        emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ)) := ⟨_, rfl⟩
  have hNlm : Measurable Nl := by
    rw [hNl]
    exact Finset.measurable_sum _ fun j _ =>
      (mti_batch_meas F (t + (ℓ : ℤ) + 1 - (j : ℤ))).const_smul (emaW F.β j)
  have hind : IndepFun (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => def_app_vol_product F ω t)
      Nl (indepSpaceLaw m n B) := by
    rw [hNl]
    exact mti_indep F t ℓ
  obtain ⟨X, hXd⟩ : ∃ X : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n,
      X = fun ω => Q ϱ (def_app_vol_product F ω t) := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n,
      Y = fun ω => Q ϱ' (def_app_vol_product F ω (t + (ℓ : ℤ))) := ⟨_, rfl⟩
  obtain ⟨Nq, hNqd⟩ : ∃ Nq : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n,
      Nq = fun ω => Q ϱ' (Nl ω) := ⟨_, rfl⟩
  have hXm : Measurable X := by
    rw [hXd]; exact (mt_Q_meas hϱ0'.le).comp (mti_prod_meas F t)
  have hYm : Measurable Y := by
    rw [hYd]; exact (mt_Q_meas hϱ'pos.le).comp (mti_prod_meas F _)
  have hNqm : Measurable Nq := by
    rw [hNqd]; exact (mt_Q_meas hϱ'pos.le).comp hNlm
  have hXb : ∀ ω, fro (X ω) ≤ Real.sqrt ((min m n : ℕ) : ℝ) := fun ω => by
    rw [hXd]; exact mt_Q_fro_le hϱ0'.le _
  have hYb : ∀ ω, fro (Y ω) ≤ Real.sqrt ((min m n : ℕ) : ℝ) := fun ω => by
    rw [hYd]; exact mt_Q_fro_le hϱ'pos.le _
  have hNqb : ∀ ω, fro (Nq ω) ≤ Real.sqrt ((min m n : ℕ) : ℝ) := fun ω => by
    rw [hNqd]; exact mt_Q_fro_le hϱ'pos.le _
  have hDm : Measurable (fun ω => Y ω - Nq ω) := by
    have hsub : Measurable (fun p : Mat m n × Mat m n => p.1 - p.2) :=
      (continuous_fst.sub continuous_snd).measurable
    exact hsub.comp (hYm.prodMk hNqm)
  have hDb : ∀ ω, fro (Y ω - Nq ω) ≤ 2 * Real.sqrt ((min m n : ℕ) : ℝ) := fun ω => by
    have := mt_fro_triangle (Y ω) (Nq ω)
    linarith [hYb ω, hNqb ω]
  have hzA : ∀ μ l, ∫ ω, Matrix.trace (projOut Sp μ * X ω * projIn Sp l * (Nq ω)ᵀ)
      ∂(indepSpaceLaw m n B) = 0 := fun μ l => by
    rw [hXd, hNqd]
    exact mti_zero F _ _ (mt_proj_opNorm Sp μ l).1 (mt_proj_opNorm Sp μ l).2 hϱ0' hϱ'pos.le t Nl
      hNlm hind
  have hI0 : ∀ μ l, ∫ ω, Matrix.trace (projOut Sp μ * X ω * projIn Sp l * (Y ω)ᵀ)
      ∂(indepSpaceLaw m n B) =
      ∫ ω, Matrix.trace (projOut Sp μ * X ω * projIn Sp l * (Y ω - Nq ω)ᵀ)
        ∂(indepSpaceLaw m n B) := fun μ l => by
    have hpt : ∀ ω, Matrix.trace (projOut Sp μ * X ω * projIn Sp l * (Y ω)ᵀ) =
        Matrix.trace (projOut Sp μ * X ω * projIn Sp l * (Y ω - Nq ω)ᵀ) +
        Matrix.trace (projOut Sp μ * X ω * projIn Sp l * (Nq ω)ᵀ) := fun ω => by
      rw [mt_trace_sub_right]; ring
    have iA : Integrable (fun ω => Matrix.trace (projOut Sp μ * X ω * projIn Sp l *
        (Y ω - Nq ω)ᵀ)) (indepSpaceLaw m n B) :=
      mt_trace_integrable _ _ (mt_proj_opNorm Sp μ l).1 (mt_proj_opNorm Sp μ l).2 _ _ hXm hDm _ _
        hXb hDb
    have iB : Integrable (fun ω => Matrix.trace (projOut Sp μ * X ω * projIn Sp l *
        (Nq ω)ᵀ)) (indepSpaceLaw m n B) :=
      mt_trace_integrable _ _ (mt_proj_opNorm Sp μ l).1 (mt_proj_opNorm Sp μ l).2 _ _ hXm hNqm _ _
        hXb hNqb
    simp_rw [hpt]
    rw [integral_add iA iB, hzA, add_zero]
  -- Cauchy–Schwarz
  have hsqint : ∀ (f : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → ℝ), Measurable f → ∀ c : ℝ,
      (∀ ω, |f ω| ≤ c) → Integrable (fun ω => f ω ^ 2) (indepSpaceLaw m n B) :=
    fun f hf c hc =>
    Integrable.of_bound (C := c ^ 2) (hf.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hc ω) 2)
  have haM : Measurable (fun ω => fro (X ω)) := mt_fro_meas.comp hXm
  have hbM : Measurable (fun ω => fro (Y ω - Nq ω)) := mt_fro_meas.comp hDm
  have haI := hsqint _ haM _ (fun ω => by
    rw [abs_of_nonneg (mt_fro_nn _)]; exact hXb ω)
  have hbI := hsqint _ hbM _ (fun ω => by
    rw [abs_of_nonneg (mt_fro_nn _)]; exact hDb ω)
  have hcs := mt_cs _ _ haM hbM haI hbI
  have habI : Integrable (fun ω => fro (X ω) * fro (Y ω - Nq ω)) (indepSpaceLaw m n B) :=
    mt_int_mul_bdd _ _ haM hbM _ _
      (fun ω => by rw [abs_of_nonneg (mt_fro_nn _)]; exact hXb ω)
      (fun ω => by rw [abs_of_nonneg (mt_fro_nn _)]; exact hDb ω)
  obtain ⟨Sab, hSab⟩ : ∃ Sab : ℝ, Sab = ∑ μ ∈ muVals Sp, ∑ l ∈ lamVals Sp,
      |∫ ω, Matrix.trace (projOut Sp μ * X ω * projIn Sp l * (Y ω - Nq ω)ᵀ)
        ∂(indepSpaceLaw m n B)| := ⟨_, rfl⟩
  have hSle : Sab ≤ ∫ ω, fro (X ω) * fro (Y ω - Nq ω) ∂(indepSpaceLaw m n B) := by
    rw [hSab]
    exact mt_atoms_integral_le Sp X (fun ω => Y ω - Nq ω) hXm hDm _ _ hXb hDb
  have hSnn : 0 ≤ Sab := by
    rw [hSab]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- second moment of the difference
  have hmom := mti_moment F γstar CSig hS t
  have hdec := mti_decomp F t ℓ
  have hρ : (ϱ' ^ (-(1 / 2 : ℝ))) ^ 2 = ϱ'⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hϱ'pos.le]
    norm_num
    exact Real.rpow_neg_one ϱ'
  have hpw : ∀ᵐ ω ∂(indepSpaceLaw m n B), fro (Y ω - Nq ω) ^ 2 ≤
      ϱ'⁻¹ * (F.β ^ (2 * ℓ) * fro (def_app_vol_product F ω t) ^ 2) := by
    filter_upwards [hdec] with ω hω
    have h1 := Muon.Foundations.fro_Q_sub_Q_le hϱ'pos (def_app_vol_product F ω (t + (ℓ : ℤ))) (Nl ω)
    have h2 : def_app_vol_product F ω (t + (ℓ : ℤ)) - Nl ω =
        F.β ^ ℓ • def_app_vol_product F ω t := by
      rw [hω, hNl]
      abel
    rw [h2, mti_fro_smul, abs_of_nonneg (pow_nonneg hβ0 _)] at h1
    have h3 : fro (Y ω - Nq ω) ≤ ϱ' ^ (-(1 / 2 : ℝ)) *
        (F.β ^ ℓ * fro (def_app_vol_product F ω t)) := by
      rw [hYd, hNqd]
      exact h1
    calc fro (Y ω - Nq ω) ^ 2 ≤ (ϱ' ^ (-(1 / 2 : ℝ)) *
        (F.β ^ ℓ * fro (def_app_vol_product F ω t))) ^ 2 :=
          pow_le_pow_left₀ (mt_fro_nn _) h3 2
      _ = ϱ'⁻¹ * (F.β ^ (2 * ℓ) * fro (def_app_vol_product F ω t) ^ 2) := by
          rw [mul_pow, mul_pow, ← pow_mul, mul_comm ℓ 2, hρ]
  have hg_int : Integrable (fun ω => ϱ'⁻¹ * (F.β ^ (2 * ℓ) *
      fro (def_app_vol_product F ω t) ^ 2)) (indepSpaceLaw m n B) :=
    (hmom.1.const_mul _).const_mul _
  have hd1 : ∫ ω, fro (Y ω - Nq ω) ^ 2 ∂(indepSpaceLaw m n B) ≤
      ∫ ω, ϱ'⁻¹ * (F.β ^ (2 * ℓ) * fro (def_app_vol_product F ω t) ^ 2)
        ∂(indepSpaceLaw m n B) := integral_mono_ae hbI hg_int hpw
  have hd2 : ∫ ω, ϱ'⁻¹ * (F.β ^ (2 * ℓ) * fro (def_app_vol_product F ω t) ^ 2)
        ∂(indepSpaceLaw m n B) =
      ϱ'⁻¹ * (F.β ^ (2 * ℓ) * ∫ ω, fro (def_app_vol_product F ω t) ^ 2
        ∂(indepSpaceLaw m n B)) := by
    rw [integral_const_mul, integral_const_mul]
  have hd0 : ∫ ω, fro (Y ω - Nq ω) ^ 2 ∂(indepSpaceLaw m n B) ≤
      ϱ'⁻¹ * (F.β ^ (2 * ℓ) * (0 + 1 * (CSig ^ 2 * γstar ^ 2 * B))) := by
    refine hd1.trans ?_
    rw [hd2]
    have hb : 0 ≤ F.β ^ (2 * ℓ) := by positivity
    have h5 : ∫ ω, fro (def_app_vol_product F ω t) ^ 2 ∂(indepSpaceLaw m n B) ≤
        0 + 1 * (CSig ^ 2 * γstar ^ 2 * B) := by linarith [hmom.2]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hb) (inv_nonneg.2 hϱ'pos.le)
  have hx0 : ∫ ω, fro (X ω) ^ 2 ∂(indepSpaceLaw m n B) ≤ γstar * B := by
    have hle : ∀ ω, fro (X ω) ^ 2 ≤ γstar * B := fun ω => by
      have h1 := pow_le_pow_left₀ (mt_fro_nn _) (hXb ω) 2
      rw [Real.sq_sqrt (Nat.cast_nonneg _)] at h1
      linarith
    calc ∫ ω, fro (X ω) ^ 2 ∂(indepSpaceLaw m n B) ≤
        ∫ _ω, γstar * B ∂(indepSpaceLaw m n B) := integral_mono haI (integrable_const _) hle
      _ = γstar * B := by simp
  have hI : Sab ^ 2 ≤
      (∫ ω, fro (X ω) ^ 2 ∂(indepSpaceLaw m n B)) *
        (∫ ω, fro (Y ω - Nq ω) ^ 2 ∂(indepSpaceLaw m n B)) :=
    (pow_le_pow_left₀ hSnn hSle 2).trans hcs
  have hV : 0 ≤ CSig ^ 2 * γstar ^ 2 * B := by positivity
  have hV' : CSig ^ 2 * γstar ^ 2 * B ≤
      CSig ^ 2 * ((γstar * B) * (γstar * B) + 2 * (γstar * B) + 2 * (γstar * B) + 3) / B := by
    rw [le_div_iff₀ hBpos]
    have h1 : 0 ≤ CSig ^ 2 * (4 * (γstar * B) + 3) := by positivity
    nlinarith [h1]
  have hGB : 0 ≤ γstar * B := by positivity
  have hnum := mt_numeric γstar CSig ϱlo ϱ' F.β (B : ℝ)
    Sab
    (∫ ω, fro (X ω) ^ 2 ∂(indepSpaceLaw m n B))
    (∫ ω, fro (Y ω - Nq ω) ^ 2 ∂(indepSpaceLaw m n B))
    (γstar * B) (γstar * B) 0 1 (CSig ^ 2 * γstar ^ 2 * B) ℓ hB1 hγ hCs hϱlo hϱ'1 hβ0
    hI hx0 (integral_nonneg fun ω => sq_nonneg _) (integral_nonneg fun ω => sq_nonneg _) hd0
    le_rfl (sq_nonneg _) zero_le_one le_rfl hV hV' hGB le_rfl hGB le_rfl
  have hsum : ∑ μ ∈ muVals Sp, ∑ l ∈ lamVals Sp, |(B : ℝ)⁻¹ * ∫ ω, Matrix.trace (projOut Sp μ *
      indepUpd F ϱ ω t * projIn Sp l * (indepUpd F ϱ' ω (t + (ℓ : ℤ)))ᵀ)
        ∂(indepSpaceLaw m n B)| = (B : ℝ)⁻¹ * Sab := by
    rw [hSab, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [abs_mul, abs_of_pos (inv_pos.mpr hBpos)]
    have := hI0 μ l
    rw [hXd, hYd] at this
    rw [hXd, hYd]
    exact congrArg (fun z => (B : ℝ)⁻¹ * |z|) this
  rw [hsum, ← abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hBpos.le) hSnn)]
  unfold Muon.Dynamics.kStar
  exact hnum

/-- Private helper: the parity of an external index (`2` on latent vertices). -/
private def mtPar {k : ℕ} : TreeVtx k → ℕ
  | Sum.inl e => e.val % 2
  | Sum.inr _ => 2

private lemma mt_prev_val {k : ℕ} (s : Fin k) :
    (treePrev s).val = if s.val = 0 then k - 1 else s.val - 1 := by
  obtain ⟨v, hv⟩ := s
  unfold treePrev
  dsimp only
  rcases Nat.eq_zero_or_pos v with rfl | hpos
  · simp [Nat.mod_eq_of_lt (show k - 1 < k by omega)]
  · rw [if_neg (show ¬ (v = 0) by omega)]
    have e : v + (k - 1) = (v - 1) + k := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (show v - 1 < k by omega)]

private lemma mt_outV_odd {k : ℕ} (hk : k % 2 = 0) (s : Fin k) :
    (treeOutV s).val % 2 = 1 := by
  have hs := s.isLt
  unfold treeOutV
  split_ifs with h
  · have h' : s.val % 2 = 0 := h
    rw [mt_prev_val]
    split_ifs with h0 <;> omega
  · have h' : ¬ s.val % 2 = 0 := h
    omega

private lemma mt_inV_even {k : ℕ} (s : Fin k) : (treeInV s).val % 2 = 0 := by
  have hs := s.isLt
  unfold treeInV
  split_ifs with h
  · have h' : s.val % 2 = 0 := h
    exact h'
  · have h' : ¬ s.val % 2 = 0 := h
    rw [mt_prev_val]
    split_ifs with h0 <;> omega

/-- Private helper: the identifications preserve the parity of external indices. -/
private lemma mt_setoid_par {k : ℕ} (hk : k % 2 = 0) (p : TreeMatch k × TreeMatch k) {x y : TreeVtx k}
    (h : treeSetoid p x y) : mtPar x = mtPar y := by
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
      simp only [mtPar]
      rw [mt_outV_odd hk s, mt_outV_odd hk (p.1.1 s)]
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a; subst h1b
      simp only [mtPar]
      rw [mt_inV_even s, mt_inV_even (p.2.1 s)]
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Private helper: the class of the `G`-mark contains no odd (output) external vertex. -/
private lemma mt_gmark_pure (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) :
    ¬ ∃ e : Fin (treeK a b),
      treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeGMark a b)) ∧ e.val % 2 = 1 := by
  rintro ⟨e, heq, hodd⟩
  unfold treeMk at heq
  have h2 := mt_setoid_par (by unfold treeK; omega) p (Quotient.exact heq)
  simp only [mtPar, treeGMark, Fin.val_mk] at h2
  omega


open Classical in
private lemma mt_prod_zero_of_factor {a b : ℕ} (p : TreeMatch (treeK a b) × TreeMatch (treeK a b))
    (f : Quotient (treeSetoid p) → ℝ) (V : Quotient (treeSetoid p)) (h : f V = 0) :
    ∏ W : Quotient (treeSetoid p), f W = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ V) h

open Classical in
private lemma mt_treeMono_zero_F {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (hF : ∀ i, μ i * Fd i = 0) (a b : ℕ) :
    treeMono β ℓ J R B μ lam Fd Gd a b = 0 := by
  unfold treeMono
  refine Finset.sum_eq_zero fun p _ => ?_
  split_ifs with hp
  · refine mt_prod_zero_of_factor p _ (treeMk p (Sum.inl (treeFMark a b))) ?_
    have hex : ∃ e : Fin (treeK a b),
        treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeFMark a b)) := ⟨_, rfl⟩
    have hodd : ∃ e : Fin (treeK a b),
        treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeFMark a b)) ∧ e.val % 2 = 1 :=
      ⟨treeFMark a b, rfl, by unfold treeFMark; dsimp only; omega⟩
    unfold treeClassFactor
    simp only [if_pos hex, if_pos hodd, if_true, pow_one]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => ?_)
    have hpos : 0 < (Finset.univ.filter fun e : Fin (treeK a b) =>
        treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeFMark a b))).card :=
      Finset.card_pos.mpr ⟨treeFMark a b, by simp⟩
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hq, pow_succ, mul_assoc, hF i, mul_zero]
  · rfl

open Classical in
private lemma mt_treeMono_zero_G {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (hG : ∀ j, lam j * Gd j = 0) (a b : ℕ) :
    treeMono β ℓ J R B μ lam Fd Gd a b = 0 := by
  unfold treeMono
  refine Finset.sum_eq_zero fun p _ => ?_
  split_ifs with hp
  · refine mt_prod_zero_of_factor p _ (treeMk p (Sum.inl (treeGMark a b))) ?_
    have hex : ∃ e : Fin (treeK a b),
        treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeGMark a b)) := ⟨_, rfl⟩
    have hnot := mt_gmark_pure a b p
    unfold treeClassFactor
    simp only [if_pos hex, if_neg hnot, if_true, pow_one]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => ?_)
    have hpos : 0 < (Finset.univ.filter fun e : Fin (treeK a b) =>
        treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeGMark a b))).card :=
      Finset.card_pos.mpr ⟨treeGMark a b, by simp⟩
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hq, pow_succ, mul_assoc, hG j, mul_zero]
  · rfl

private lemma mt_lagResp_zero_aux (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n : ℕ} (β : ℝ) (ℓ B : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ)
    (Gd : Fin n → ℝ) (f g : ℝ → ℝ)
    (h0 : ∀ (J : ℕ) (R : ℝ) (f₁ f₂ : Polynomial ℝ),
      def_app_vol_tree β ℓ J R B μ lam Fd Gd f₁ f₂ = 0) :
    lagResp cert γstar CSig β ℓ B μ lam Fd Gd f g = 0 := by
  have e1 : ∀ p : ℕ × ℝ, lagRespCut cert γstar CSig β ℓ p.1 p.2 B μ lam Fd Gd f g = 0 := by
    intro p
    unfold lagRespCut treeRespExt
    simp_rw [h0]
    exact tendsto_const_nhds.limUnder_eq
  unfold lagResp
  simp_rw [e1]
  exact tendsto_const_nhds.limUnder_eq

private lemma mt_lagResp_zero_F (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n : ℕ} (β : ℝ) (ℓ B : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ)
    (Gd : Fin n → ℝ) (hF : ∀ i, μ i * Fd i = 0) (f g : ℝ → ℝ) :
    lagResp cert γstar CSig β ℓ B μ lam Fd Gd f g = 0 := by
  refine mt_lagResp_zero_aux cert γstar CSig β ℓ B μ lam Fd Gd f g fun J R f₁ f₂ => ?_
  unfold def_app_vol_tree
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rw [mt_treeMono_zero_F β ℓ J R B μ lam Fd Gd hF a b, mul_zero]

private lemma mt_lagResp_zero_G (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n : ℕ} (β : ℝ) (ℓ B : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ)
    (Gd : Fin n → ℝ) (hG : ∀ j, lam j * Gd j = 0) (f g : ℝ → ℝ) :
    lagResp cert γstar CSig β ℓ B μ lam Fd Gd f g = 0 := by
  refine mt_lagResp_zero_aux cert γstar CSig β ℓ B μ lam Fd Gd f g fun J R f₁ f₂ => ?_
  unfold def_app_vol_tree
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rw [mt_treeMono_zero_G β ℓ J R B μ lam Fd Gd hG a b, mul_zero]

private lemma mt_classDiag_zero {k : ℕ} (x : Fin k → ℝ) (i : Fin k) :
    x i * classDiag x 0 i = 0 := by
  unfold classDiag
  split_ifs with h <;> simp [h]

private lemma mt_tv_atoms (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ϱlo ϱhi : ℝ)
    (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) (ℓ : ℕ) (T : ℝ)
    (hmodel : ∀ {m' n' B' : ℕ} (F' : FrozenParams m' n' B') (Sp' : SpectralData F'.C),
      SizeFin F'.C B' γstar CSig → F'.β = Fp.β →
      ∀ ϱ ∈ Set.Icc ϱlo ϱhi, ∀ ϱ' ∈ Set.Icc ϱlo ϱhi,
        ∑ μ ∈ muVals Sp', ∑ l ∈ lamVals Sp',
          |(B' : ℝ)⁻¹ * ∫ ω, Matrix.trace (projOut Sp' μ * indepUpd F' ϱ ω 0 * projIn Sp' l *
            (indepUpd F' ϱ' ω (0 + (ℓ : ℤ)))ᵀ) ∂(indepSpaceLaw m' n' B')| ≤ T)
    (ϱ : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) (ϱ' : ℝ) (hϱ'I : ϱ' ∈ Set.Icc ϱlo ϱhi) :
    ∑ μ ∈ muVals S, ∑ l ∈ lamVals S,
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (classDiag S.μ μ) (classDiag S.lam l)
        (omegaF ϱ) (omegaF ϱ')| ≤ T := by
  obtain ⟨hm, hn⟩ := mm_pos_of_fro Fp.A Fp.hA
  obtain ⟨R, hmR, hnR, hBR, hγR, hCR, hβR, hloR, hhiR, hR⟩ :=
    def_app_vol_replication_regime Fp S γstar CSig ϱlo ϱhi hCSig hS hm hn hϱ
  rcases R with ⟨rm, rn, rB, rF, rprop, rγ, rC, rhC, rdims, rnormO, rnormI,
    rβ, rhβ, rlo, rhi, rhϱ, rdiff⟩
  dsimp only at hmR hnR hBR hγR hCR hβR hloR hhiR hR
  subst rm rn rB rγ rC rβ rlo rhi
  have hCov : ∀ k, (rF k).C = replCov Fp.C (k + 1) := fun k => eq_of_heq (hR k).1
  have hspec : ∀ k, ∃ Sp : SpectralData (rF k).C,
      Sp.μ = replVec (k + 1) S.μ ∧ Sp.lam = replVec (k + 1) S.lam := by
    intro k
    rw [hCov k]
    obtain ⟨Sp, -, -, hμ, hl⟩ := mm_exists_replSpec Fp.C S (k + 1)
    exact ⟨Sp, hμ, hl⟩
  choose Sp hμ hl using hspec
  have hs : SizeSeq (B := fun k => (k + 1) * B) (fun k => (rF k).C) γstar CSig rprop.γout
      rprop.γin :=
    ⟨fun k => ⟨rdims k, rnormO k, rnormI k⟩, rprop.B_top, rprop.ratio_in, rprop.ratio_out⟩
  have hclo := (thm_app_vol_lag_kernel_closure_indep cert γstar CSig rprop.γout rprop.γin hCSig
    ϱlo ϱhi hϱ (fun k => (k + 1) * m) (fun k => (k + 1) * n) (fun k => (k + 1) * B) rF Sp hs
    Fp.β Fp.hβ.2 (fun k => (rhβ k).le) ℓ {1} isCompact_singleton
    (by intro x hx; rcases hx with rfl; norm_num)).2
  have hmu : ∀ k, muVals (Sp k) = muVals S := by
    intro k
    unfold muVals
    rw [hμ k]
    exact mm_vals_repl S.μ (k + 1) (Nat.succ_pos k)
  have hla : ∀ k, lamVals (Sp k) = lamVals S := by
    intro k
    unfold lamVals
    rw [hl k]
    exact mm_vals_repl S.lam (k + 1) (Nat.succ_pos k)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set N : ℝ := ((muVals S).card : ℝ) * ((lamVals S).card : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  have hε' : 0 < ε / (N + 1) := by positivity
  obtain ⟨k, hk⟩ := (hclo (ε / (N + 1)) hε').exists
  have hmod := hmodel (rF k) (Sp k) ⟨rdims k, rnormO k, rnormI k⟩ (rhβ k) ϱ hϱI ϱ' hϱ'I
  rw [hmu k, hla k] at hmod
  have hatom : ∀ μ ∈ muVals S, ∀ l ∈ lamVals S,
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (classDiag S.μ μ) (classDiag S.lam l)
        (omegaF ϱ) (omegaF ϱ')| ≤
      |(((k + 1) * B : ℕ) : ℝ)⁻¹ * ∫ ω, Matrix.trace (projOut (Sp k) μ * indepUpd (rF k) ϱ ω 0 *
        projIn (Sp k) l * (indepUpd (rF k) ϱ' ω (0 + (ℓ : ℤ)))ᵀ)
          ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B))| + ε / (N + 1) := by
    intro μ _ l _
    have key := hk 0 ϱ hϱI ϱ' hϱ'I (classDiag (Sp k).μ μ) (classDiag (Sp k).lam l)
      (projOut (Sp k) μ) (projIn (Sp k) l) rfl rfl (mt_proj_opNorm (Sp k) μ l).1
      (mt_proj_opNorm (Sp k) μ l).2
    have hw : lagResp cert γstar CSig (rF k).β ℓ ((k + 1) * B) (Sp k).μ (Sp k).lam
        (classDiag (Sp k).μ μ) (classDiag (Sp k).lam l) (omegaF ϱ) (omegaF ϱ') =
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (classDiag S.μ μ) (classDiag S.lam l)
          (omegaF ϱ) (omegaF ϱ') := by
      rw [rhβ k, hμ k, hl k, mm_classDiag_repl, mm_classDiag_repl]
      exact mm_lagResp_repl cert γstar CSig Fp.β ℓ B (k + 1) (Nat.succ_pos k) S.μ S.lam _ _ _ _
    rw [hw] at key
    have := abs_sub_abs_le_abs_sub
      (lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (classDiag S.μ μ) (classDiag S.lam l)
        (omegaF ϱ) (omegaF ϱ'))
      ((((k + 1) * B : ℕ) : ℝ)⁻¹ * ∫ ω, Matrix.trace (projOut (Sp k) μ * indepUpd (rF k) ϱ ω 0 *
        projIn (Sp k) l * (indepUpd (rF k) ϱ' ω (0 + (ℓ : ℤ)))ᵀ)
          ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B)))
    rw [abs_sub_comm] at this
    linarith
  calc ∑ μ ∈ muVals S, ∑ l ∈ lamVals S,
        |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (classDiag S.μ μ) (classDiag S.lam l)
          (omegaF ϱ) (omegaF ϱ')|
      ≤ ∑ μ ∈ muVals S, ∑ l ∈ lamVals S,
        (|(((k + 1) * B : ℕ) : ℝ)⁻¹ * ∫ ω, Matrix.trace (projOut (Sp k) μ *
          indepUpd (rF k) ϱ ω 0 * projIn (Sp k) l *
          (indepUpd (rF k) ϱ' ω (0 + (ℓ : ℤ)))ᵀ)
            ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B))| + ε / (N + 1)) :=
        Finset.sum_le_sum fun μ hμ => Finset.sum_le_sum fun l hl => hatom μ hμ l hl
    _ = (∑ μ ∈ muVals S, ∑ l ∈ lamVals S,
        |(((k + 1) * B : ℕ) : ℝ)⁻¹ * ∫ ω, Matrix.trace (projOut (Sp k) μ *
          indepUpd (rF k) ϱ ω 0 * projIn (Sp k) l *
          (indepUpd (rF k) ϱ' ω (0 + (ℓ : ℤ)))ᵀ)
            ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B))|) + N * (ε / (N + 1)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hN]
        ring
    _ ≤ T + ε := by
        have h1 : N * (ε / (N + 1)) ≤ ε := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith
        linarith


end MtCopy

section MaCopy
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}

private lemma ma_fro_nn {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma ma_fro_transpose {k l : ℕ} (A : Mat k l) : fro Aᵀ = fro A := by
  unfold fro
  congr 1
  exact Finset.sum_comm

private lemma ma_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma ma_opNorm_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ opNorm A := by
  unfold opNorm
  exact norm_nonneg _

private lemma ma_fro_sq {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma ma_fro_mul_le_left {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ opNorm M * fro N := by
  have hcol : ∀ j : Fin r, ∑ i, (M * N) i j ^ 2 ≤ opNorm M ^ 2 * ∑ k, N k j ^ 2 := by
    intro j
    obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin q), ∀ k, v.ofLp k = N k j :=
      ⟨(EuclideanSpace.equiv (Fin q) ℝ).symm (fun k => N k j), fun k => rfl⟩
    have h1 : ‖(EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)‖ ≤ opNorm M * ‖v‖ := by
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
    rw [ma_fro_sq, mul_pow, ma_fro_sq, Finset.sum_comm]
    calc ∑ j, ∑ i, (M * N) i j ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, N k j ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, N k j ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (ma_fro_nn _) (mul_nonneg (ma_opNorm_nonneg M) (ma_fro_nn N))
    two_ne_zero).mp hfro

private lemma ma_fro_mul_le_right {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ fro M * opNorm N := by
  have h := ma_fro_mul_le_left Nᵀ Mᵀ
  rw [ma_opNorm_transpose, ma_fro_transpose, ← Matrix.transpose_mul, ma_fro_transpose] at h
  linarith [mul_comm (opNorm N) (fro M)]

private lemma ma_fro_sandwich {m n : ℕ} (F : Mat m m) (D : Mat m n) (G : Mat n n)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) : fro (F * D * G) ≤ fro D := by
  have h1 : opNorm F * fro D ≤ fro D := mul_le_of_le_one_left (ma_fro_nn D) hF
  calc fro (F * D * G) ≤ fro (F * D) * opNorm G := ma_fro_mul_le_right _ _
    _ ≤ (opNorm F * fro D) * opNorm G :=
        mul_le_mul_of_nonneg_right (ma_fro_mul_le_left _ _) (ma_opNorm_nonneg _)
    _ ≤ fro D * 1 := mul_le_mul h1 hG (ma_opNorm_nonneg G) (ma_fro_nn D)
    _ = fro D := mul_one _

private lemma ma_trace_mul_transpose_le {m n : ℕ} (X C : Mat m n) :
    |Matrix.trace (X * Cᵀ)| ≤ fro X * fro C := by
  have htr : Matrix.trace (X * Cᵀ) = ∑ p : Fin m × Fin n, X p.1 p.2 * C p.1 p.2 := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [htr]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
    (fun p => X p.1 p.2) (fun p => C p.1 p.2)
  have hX : ∑ p : Fin m × Fin n, X p.1 p.2 ^ 2 = fro X ^ 2 := by
    rw [ma_fro_sq, Fintype.sum_prod_type]
  have hC : ∑ p : Fin m × Fin n, C p.1 p.2 ^ 2 = fro C ^ 2 := by
    rw [ma_fro_sq, Fintype.sum_prod_type]
  rw [hX, hC] at cs
  refine (pow_le_pow_iff_left₀ (abs_nonneg _) (mul_nonneg (ma_fro_nn X) (ma_fro_nn C))
    two_ne_zero).mp ?_
  rw [sq_abs, mul_pow]
  exact cs

/-- Tested pairing bound `|Tr[F X G Yᵀ]| ≤ ‖X‖_F ‖Y‖_F` for contractions `F`, `G`. -/
private lemma ma_tested_le {m n : ℕ} (Fo : Mat m m) (Gi : Mat n n) (hF : opNorm Fo ≤ 1)
    (hG : opNorm Gi ≤ 1) (X Y : Mat m n) :
    |Matrix.trace (Fo * X * Gi * Yᵀ)| ≤ fro X * fro Y :=
  (ma_trace_mul_transpose_le (Fo * X * Gi) Y).trans
    (mul_le_mul_of_nonneg_right (ma_fro_sandwich Fo X Gi hF hG) (ma_fro_nn Y))

private lemma ma_abs_entry_le_fro {m n : ℕ} (K : Mat m n) (i : Fin m) (j : Fin n) :
    |K i j| ≤ fro K := by
  unfold fro
  apply Real.abs_le_sqrt
  have h1 : ‖K i j‖ ^ 2 ≤ ∑ j', ‖K i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖K i j'‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖K i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖K i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖K i' j'‖ ^ 2)
      (fun i' _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
  have h3 : ‖K i j‖ ^ 2 = K i j ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  linarith

private lemma ma_fro_le_of_entries {m n : ℕ} (K : Mat m n) (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ i j, |K i j| ≤ a) : fro K ≤ Real.sqrt ((m : ℝ) * n) * a := by
  have h1 : fro K ^ 2 ≤ ((m : ℝ) * n) * a ^ 2 := by
    rw [ma_fro_sq]
    calc ∑ i, ∑ j, K i j ^ 2 ≤ ∑ _i : Fin m, ∑ _j : Fin n, a ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
      _ = ((m : ℝ) * n) * a ^ 2 := by simp [mul_assoc]
  have h2 : Real.sqrt (((m : ℝ) * n) * a ^ 2) = Real.sqrt ((m : ℝ) * n) * a := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ha]
  rw [← h2]
  exact Real.le_sqrt_of_sq_le h1

/-! ### Measurability and boundedness of the centred updates -/

private lemma ma_borel (m n : ℕ) : BorelSpace (Mat m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))

private lemma ma_sc (m n : ℕ) : SecondCountableTopology (Mat m n) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))

private lemma ma_batch_meas (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    Measurable (frozenBatchG F S s) := by
  haveI := ma_borel m n
  haveI := ma_sc m n
  unfold frozenBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : Vec m × Vec n =>
      (dotProduct p.1 (Matrix.mulVec F.A p.2)) • (rOut F.C * outer p.1 p.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (S.meas s a)

private lemma ma_tsum_meas {Ω' : Type*} (m1 : MeasurableSpace Ω') (f : ℕ → Ω' → Mat m n)
    (hf : ∀ j, Measurable[m1] (f j)) : Measurable[m1] (fun ω => ∑' j, f j ω) := by
  letI : MeasurableSpace Ω' := m1
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  exact Measurable.tsum hf

private lemma ma_buf_meas (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) :
    Measurable (frozenBuf F S t) := by
  unfold frozenBuf
  exact ma_tsum_meas _ _ fun j => (ma_batch_meas F S _).const_smul (emaW F.β j)

private lemma ma_Q_meas {ϱ : ℝ} (hϱ : 0 ≤ ϱ) : Measurable (fun K : Mat m n => Q ϱ K) :=
  (measurable_Q (m := m) (n := n)).comp
    ((measurable_const (a := (⟨ϱ, hϱ⟩ : Set.Ici (0 : ℝ)))).prodMk measurable_id)

private lemma ma_upd_meas (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 ≤ ϱ) (t : ℤ) : Measurable (frozenUpd F S ϱ t) :=
  (ma_Q_meas hϱ).comp (ma_buf_meas F S t)

private lemma ma_cen_meas (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 ≤ ϱ) (t : ℤ) : Measurable (centredUpd F S ϱ t) := by
  haveI := ma_borel m n
  haveI := ma_sc m n
  unfold centredUpd
  exact ((continuous_id.sub continuous_const).measurable).comp (ma_upd_meas F S hϱ t)

private lemma ma_upd_fro_sq (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 ≤ ϱ) (t : ℤ) (ω : Ω) : fro (frozenUpd F S ϱ t ω) ^ 2 ≤ (min m n : ℕ) := by
  obtain ⟨-, h2, h3, -⟩ := lem_app_setup_filter_i ϱ hϱ (frozenBuf F S t ω)
  exact h2.trans (by exact_mod_cast h3)

private lemma ma_upd_entry (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 ≤ ϱ) (t : ℤ) (ω : Ω) (i : Fin m) (j : Fin n) :
    |frozenUpd F S ϱ t ω i j| ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
  refine (ma_abs_entry_le_fro _ i j).trans ?_
  exact Real.le_sqrt_of_sq_le (ma_upd_fro_sq F S hϱ t ω)

private lemma ma_mean_entry [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (t : ℤ) (i : Fin m) (j : Fin n) :
    |mean P (frozenUpd F S ϱ t) i j| ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
  have h := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => frozenUpd F S ϱ t ω i j)
    (C := Real.sqrt ((min m n : ℕ) : ℝ))
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact ma_upd_entry F S hϱ t ω i j)
  simpa [mean, Real.norm_eq_abs] using h

/-- Uniform Frobenius bound for the centred updates. -/
private lemma ma_cen_fro_le [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (t : ℤ) (ω : Ω) :
    fro (centredUpd F S ϱ t ω) ≤
      Real.sqrt ((m : ℝ) * n) * (2 * Real.sqrt ((min m n : ℕ) : ℝ)) := by
  refine ma_fro_le_of_entries _ _ (by positivity) fun i j => ?_
  have h1 := ma_upd_entry F S hϱ t ω i j
  have h2 := ma_mean_entry F S hϱ t i j
  simp only [centredUpd, Matrix.sub_apply]
  calc |frozenUpd F S ϱ t ω i j - mean P (frozenUpd F S ϱ t) i j|
      ≤ |frozenUpd F S ϱ t ω i j| + |mean P (frozenUpd F S ϱ t) i j| := abs_sub _ _
    _ ≤ 2 * Real.sqrt ((min m n : ℕ) : ℝ) := by linarith

private lemma ma_trace_cont {m n : ℕ} (Fo : Mat m m) (Gi : Mat n n) :
    Continuous (fun p : Mat m n × Mat m n => Matrix.trace (Fo * p.1 * Gi * p.2ᵀ)) := by
  fun_prop

private lemma ma_meas_trace {α : Type*} [MeasurableSpace α] (Fo : Mat m m) (Gi : Mat n n)
    (f g : α → Mat m n) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => Matrix.trace (Fo * f x * Gi * (g x)ᵀ)) := by
  haveI := ma_borel m n
  haveI := ma_sc m n
  have h := ((ma_trace_cont Fo Gi).measurable).comp (hf.prodMk hg)
  exact h

/-- Integrability of the tested pairing of two bounded measurable random matrices. -/
private lemma ma_trace_integrable [IsProbabilityMeasure P] (Fo : Mat m m) (Gi : Mat n n)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1) (X Y : Ω → Mat m n) (hX : Measurable X)
    (hY : Measurable Y) (D D' : ℝ) (hXD : ∀ ω, fro (X ω) ≤ D) (hYD : ∀ ω, fro (Y ω) ≤ D') :
    Integrable (fun ω => Matrix.trace (Fo * X ω * Gi * (Y ω)ᵀ)) P := by
  haveI := ma_borel m n
  haveI := ma_sc m n
  refine Integrable.of_bound (C := D * D') ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((ma_trace_cont Fo Gi).measurable.comp (hX.prodMk hY)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact (ma_tested_le Fo Gi hF hG _ _).trans
      (mul_le_mul (hXD ω) (hYD ω) (ma_fro_nn _) ((ma_fro_nn _).trans (hXD ω)))



/-! ### Same-time bound -/

private lemma ma_entry_meas (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 ≤ ϱ) (t : ℤ) (i : Fin m) (j : Fin n) :
    Measurable (fun ω => frozenUpd F S ϱ t ω i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (ma_upd_meas F S hϱ t))

private lemma ma_cen_sq_int_le [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (t : ℤ) :
    ∫ ω, fro (centredUpd F S ϱ t ω) ^ 2 ∂P ≤ ((min m n : ℕ) : ℝ) := by
  have hmem : ∀ i j, MemLp (fun ω => frozenUpd F S ϱ t ω i j) 2 P := fun i j =>
    MemLp.of_bound (ma_entry_meas F S hϱ t i j).aestronglyMeasurable
      (Real.sqrt ((min m n : ℕ) : ℝ)) (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact ma_upd_entry F S hϱ t ω i j)
  have hsq : ∀ i j, Integrable (fun ω => frozenUpd F S ϱ t ω i j ^ 2) P := fun i j =>
    (hmem i j).integrable_sq
  have hcsq : ∀ i j, Integrable (fun ω => (frozenUpd F S ϱ t ω i j -
      mean P (frozenUpd F S ϱ t) i j) ^ 2) P := fun i j => by
    have : MemLp (fun ω => frozenUpd F S ϱ t ω i j - mean P (frozenUpd F S ϱ t) i j) 2 P :=
      (hmem i j).sub (memLp_const _)
    exact this.integrable_sq
  have hent : ∀ i j, ∫ ω, (frozenUpd F S ϱ t ω i j - mean P (frozenUpd F S ϱ t) i j) ^ 2 ∂P ≤
      ∫ ω, frozenUpd F S ϱ t ω i j ^ 2 ∂P := by
    intro i j
    have h1 := variance_eq_integral (μ := P) (ma_entry_meas F S hϱ t i j).aemeasurable
    have h2 := variance_le_expectation_sq (μ := P)
      (ma_entry_meas F S hϱ t i j).aestronglyMeasurable
    have h3 : mean P (frozenUpd F S ϱ t) i j = ∫ ω, frozenUpd F S ϱ t ω i j ∂P := rfl
    rw [h3]
    simp only [Pi.pow_apply] at h2
    rw [← h1]
    exact h2
  have hcen_sq : ∀ ω, fro (centredUpd F S ϱ t ω) ^ 2 = ∑ i, ∑ j,
      (frozenUpd F S ϱ t ω i j - mean P (frozenUpd F S ϱ t) i j) ^ 2 := by
    intro ω
    rw [ma_fro_sq]
    rfl
  have hint1 : ∫ ω, fro (centredUpd F S ϱ t ω) ^ 2 ∂P ≤
      ∫ ω, fro (frozenUpd F S ϱ t ω) ^ 2 ∂P := by
    simp_rw [hcen_sq, ma_fro_sq]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hcsq i j)),
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hsq i j))]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hcsq i j), integral_finsetSum _ (fun j _ => hsq i j)]
    exact Finset.sum_le_sum fun j _ => hent i j
  have hint2 : Integrable (fun ω => fro (frozenUpd F S ϱ t ω) ^ 2) P := by
    simp_rw [ma_fro_sq]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hsq i j
  refine hint1.trans ?_
  calc ∫ ω, fro (frozenUpd F S ϱ t ω) ^ 2 ∂P ≤ ∫ _ω, ((min m n : ℕ) : ℝ) ∂P :=
        integral_mono hint2 (integrable_const _) fun ω => ma_upd_fro_sq F S hϱ t ω
    _ = ((min m n : ℕ) : ℝ) := by simp

/-! ### Independence of the past buffer from a later truncated buffer -/

private lemma ma_batch_meas_sub (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (T : Set (ℤ × Fin B)) (hT : ∀ a, (s, a) ∈ T) :
    Measurable[⨆ i ∈ T, MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance]
      (frozenBatchG F S s) := by
  have h : ∀ a, Measurable[⨆ i ∈ T, MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance]
      (S.zw s a) := fun a => Measurable.of_comap_le (le_iSup₂
      (f := fun i (_ : i ∈ T) =>
        MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance) (s, a) (hT a))
  generalize (⨆ i ∈ T, MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance) = m1 at h ⊢
  letI : MeasurableSpace Ω := m1
  haveI := ma_borel m n
  haveI := ma_sc m n
  unfold frozenBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : Vec m × Vec n =>
      (dotProduct p.1 (Matrix.mulVec F.A p.2)) • (rOut F.C * outer p.1 p.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (h a)

private lemma ma_fsum_meas {Ω' : Type*} {m1 : MeasurableSpace Ω'} (f : ℕ → Ω' → Mat m n) (s : Finset ℕ)
    (hf : ∀ j ∈ s, Measurable[m1] (f j)) : Measurable[m1] (fun ω => ∑ j ∈ s, f j ω) := by
  letI : MeasurableSpace Ω' := m1
  haveI := ma_borel m n
  haveI := ma_sc m n
  exact Finset.measurable_sum _ hf

private lemma ma_indep [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t t' : ℤ) (J : ℕ) (h : t + 2 ≤ t' + 1 - (J : ℤ)) :
    IndepFun (frozenBuf F S t) (fun ω => ∑ j ∈ Finset.range (J + 1),
      emaW F.β j • frozenBatchG F S (t' + 1 - (j : ℤ)) ω) P := by
  have hind := (iIndepFun_iff_iIndep
    (fun _ : ℤ × Fin B => (inferInstance : MeasurableSpace (Vec m × Vec n)))
    (fun p : ℤ × Fin B => fun ω => S.zw p.1 p.2 ω) P).mp S.indep
  have hdisj : Disjoint {p : ℤ × Fin B | p.1 ≤ t + 1} {p : ℤ × Fin B | t + 2 ≤ p.1} := by
    rw [Set.disjoint_left]
    intro p h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    omega
  have key := indep_iSup_of_disjoint (fun p : ℤ × Fin B => (S.meas p.1 p.2).comap_le) hind hdisj
  have hbat1 : ∀ s : ℤ, s ≤ t + 1 → Measurable[⨆ i ∈ {p : ℤ × Fin B | p.1 ≤ t + 1},
      MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance] (frozenBatchG F S s) :=
    fun s hs => ma_batch_meas_sub F S s _ (fun a => hs)
  have hbat2 : ∀ s : ℤ, t + 2 ≤ s → Measurable[⨆ i ∈ {p : ℤ × Fin B | t + 2 ≤ p.1},
      MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance] (frozenBatchG F S s) :=
    fun s hs => ma_batch_meas_sub F S s _ (fun a => hs)
  have hA : Measurable[⨆ i ∈ {p : ℤ × Fin B | p.1 ≤ t + 1},
      MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance] (frozenBuf F S t) := by
    unfold frozenBuf
    refine ma_tsum_meas _ _ fun j => ?_
    exact (hbat1 _ (by omega)).const_smul (emaW F.β j)
  have hB : Measurable[⨆ i ∈ {p : ℤ × Fin B | t + 2 ≤ p.1},
      MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance] (fun ω => ∑ j ∈ Finset.range (J + 1),
      emaW F.β j • frozenBatchG F S (t' + 1 - (j : ℤ)) ω) := by
    refine ma_fsum_meas _ _ fun j hj => ?_
    rw [Finset.mem_range] at hj
    exact (hbat2 _ (by omega)).const_smul (emaW F.β j)
  exact (IndepFun_iff_Indep _ _ P).mpr
    (indep_of_indep_of_le_left (indep_of_indep_of_le_right key (measurable_iff_comap_le.mp hB))
      (measurable_iff_comap_le.mp hA))

/-! ### Vanishing of the centred pairing against independent or constant matrices -/

private lemma ma_expand (Fo : Mat m m) (Gi : Mat n n) (X N : Mat m n) :
    Matrix.trace (Fo * X * Gi * Nᵀ) = ∑ a, ∑ b, X a b * (Gi * Nᵀ * Fo) b a := by
  have h : Matrix.trace (Fo * X * Gi * Nᵀ) = Matrix.trace (X * (Gi * Nᵀ * Fo)) := by
    rw [show Fo * X * Gi * Nᵀ = Fo * (X * Gi * Nᵀ) by simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  rw [h]
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

private lemma ma_zero_const [IsProbabilityMeasure P] (Fo : Mat m m) (Gi : Mat n n)
    (X : Ω → Mat m n) (hX : ∀ a b, Integrable (fun ω => X ω a b) P)
    (h0 : ∀ a b, ∫ ω, X ω a b ∂P = 0) (A : Mat m n) :
    ∫ ω, Matrix.trace (Fo * X ω * Gi * Aᵀ) ∂P = 0 := by
  simp_rw [ma_expand]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => (hX a b).mul_const _))]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => (hX a b).mul_const _)]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [integral_mul_const, h0, zero_mul]

private lemma ma_cen_entry_int [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (t : ℤ) (a : Fin m) (b : Fin n) :
    Integrable (fun ω => centredUpd F S ϱ t ω a b) P := by
  refine Integrable.of_bound (C := Real.sqrt ((m : ℝ) * n) * (2 * Real.sqrt ((min m n : ℕ) : ℝ)))
    ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp
      (ma_cen_meas F S hϱ t))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact (ma_abs_entry_le_fro _ a b).trans (ma_cen_fro_le F S hϱ t ω)

private lemma ma_cen_entry_zero [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (t : ℤ) (a : Fin m) (b : Fin n) :
    ∫ ω, centredUpd F S ϱ t ω a b ∂P = 0 := by
  have hint : Integrable (fun ω => frozenUpd F S ϱ t ω a b) P :=
    Integrable.of_bound (C := Real.sqrt ((min m n : ℕ) : ℝ))
      (ma_entry_meas F S hϱ t a b).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact ma_upd_entry F S hϱ t ω a b)
  simp only [centredUpd, Matrix.sub_apply]
  rw [integral_sub hint (integrable_const _), integral_const]
  simp [mean]

private lemma ma_Q_fro_le {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (K : Mat m n) :
    fro (Q ϱ K) ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
  obtain ⟨-, h2, h3, -⟩ := lem_app_setup_filter_i ϱ hϱ K
  exact Real.le_sqrt_of_sq_le (h2.trans (by exact_mod_cast h3))

private lemma ma_int_mul_bdd [IsProbabilityMeasure P] (φ ψ : Ω → ℝ) (hφ : Measurable φ)
    (hψ : Measurable ψ) (c d : ℝ) (hc : ∀ ω, |φ ω| ≤ c) (hd : ∀ ω, |ψ ω| ≤ d) :
    Integrable (fun ω => φ ω * ψ ω) P := by
  refine Integrable.of_bound (C := c * d) (hφ.mul hψ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hc ω) (hd ω) (abs_nonneg _) ((abs_nonneg _).trans (hc ω))

private lemma ma_zero_indep [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (Fo : Mat m m) (Gi : Mat n n) (hF : opNorm Fo ≤ 1)
    (hG : opNorm Gi ≤ 1) {ϱ ϱ' : ℝ} (hϱ : 0 ≤ ϱ) (hϱ' : 0 ≤ ϱ') (t : ℤ)
    (Mtr : Ω → Mat m n) (htr : Measurable Mtr) (hind : IndepFun (frozenBuf F S t) Mtr P) :
    ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
      (Q ϱ' (Mtr ω))ᵀ) ∂P = 0 := by
  haveI := ma_borel m n
  haveI := ma_sc m n
  obtain ⟨f, hf⟩ : ∃ f : Fin m → Fin n → Mat m n → ℝ, f = fun a b K =>
      (Q ϱ K - mean P (frozenUpd F S ϱ t)) a b := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin m → Fin n → Mat m n → ℝ, g = fun a b K =>
      (Gi * (Q ϱ' K)ᵀ * Fo) b a := ⟨_, rfl⟩
  have hfm : ∀ a b, Measurable (f a b) := fun a b => by
    rw [hf]
    have hsub : Measurable (fun K : Mat m n => K - mean P (frozenUpd F S ϱ t)) :=
      (continuous_id.sub continuous_const).measurable
    exact (measurable_pi_apply b).comp ((measurable_pi_apply a).comp
      (hsub.comp (ma_Q_meas hϱ)))
  have hgm : ∀ a b, Measurable (g a b) := fun a b => by
    rw [hg]
    have hc : Continuous (fun N : Mat m n => (Gi * Nᵀ * Fo) b a) := by fun_prop
    exact hc.measurable.comp (ma_Q_meas hϱ')
  have hbuf := ma_buf_meas F S t
  have e1 : ∀ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
      (Q ϱ' (Mtr ω))ᵀ) = ∑ a, ∑ b,
        f a b (frozenBuf F S t ω) * g a b (Mtr ω) := by
    intro ω
    rw [ma_expand, hf, hg]
    rfl
  have hint : ∀ a b, Integrable (fun ω => f a b (frozenBuf F S t ω) *
      g a b (Mtr ω)) P := by
    intro a b
    refine ma_int_mul_bdd _ _ ((hfm a b).comp hbuf) ((hgm a b).comp htr)
      (Real.sqrt ((m : ℝ) * n) * (2 * Real.sqrt ((min m n : ℕ) : ℝ)))
      (Real.sqrt ((min m n : ℕ) : ℝ)) (fun ω => ?_) (fun ω => ?_)
    · have : f a b (frozenBuf F S t ω) = centredUpd F S ϱ t ω a b := by rw [hf]; rfl
      rw [this]
      exact (ma_abs_entry_le_fro _ a b).trans (ma_cen_fro_le F S hϱ t ω)
    · have : g a b (Mtr ω) = (Gi * (Q ϱ' (Mtr ω))ᵀ * Fo) b a := by
        rw [hg]
      rw [this]
      refine (ma_abs_entry_le_fro _ b a).trans ?_
      refine (ma_fro_sandwich Gi _ Fo hG hF).trans ?_
      rw [ma_fro_transpose]
      exact ma_Q_fro_le hϱ' _
  simp_rw [e1]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hint a b))]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => hint a b)]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [hind.integral_fun_comp_mul_comp hbuf.aemeasurable htr.aemeasurable
    (hfm a b).aestronglyMeasurable (hgm a b).aestronglyMeasurable]
  have : ∫ ω, f a b (frozenBuf F S t ω) ∂P = 0 := by
    have e : ∀ ω, f a b (frozenBuf F S t ω) = centredUpd F S ϱ t ω a b := by
      intro ω; rw [hf]; rfl
    simp_rw [e]
    exact ma_cen_entry_zero F S hϱ t a b
  rw [this, zero_mul]

/-! ### Cauchy–Schwarz and the lag bound -/

private lemma ma_cs [IsProbabilityMeasure P] (a b : Ω → ℝ) (ha : Measurable a)
    (hb : Measurable b) (hA : Integrable (fun ω => a ω ^ 2) P)
    (hB : Integrable (fun ω => b ω ^ 2) P) :
    (∫ ω, a ω * b ω ∂P) ^ 2 ≤ (∫ ω, a ω ^ 2 ∂P) * (∫ ω, b ω ^ 2 ∂P) := by
  have hab : Integrable (fun ω => a ω * b ω) P := by
    refine Integrable.mono' ((hA.add hB).div_const 2) (ha.mul hb).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith [sq_nonneg (a ω + b ω), sq_nonneg (a ω - b ω)]
  have hq : ∀ x : ℝ, 0 ≤ (∫ ω, a ω ^ 2 ∂P) * (x * x) + (-2 * ∫ ω, a ω * b ω ∂P) * x +
      ∫ ω, b ω ^ 2 ∂P := by
    intro x
    have h1 : ∫ ω, (x * a ω - b ω) ^ 2 ∂P = (∫ ω, a ω ^ 2 ∂P) * (x * x) +
        (-2 * ∫ ω, a ω * b ω ∂P) * x + ∫ ω, b ω ^ 2 ∂P := by
      have e : (fun ω => (x * a ω - b ω) ^ 2) =
          fun ω => (x * x) * a ω ^ 2 - (2 * x) * (a ω * b ω) + b ω ^ 2 := by
        funext ω; ring
      have i1 : Integrable (fun ω => (x * x) * a ω ^ 2) P := hA.const_mul _
      have i2 : Integrable (fun ω => (2 * x) * (a ω * b ω)) P := hab.const_mul _
      have i3 : Integrable (fun ω => (x * x) * a ω ^ 2 - (2 * x) * (a ω * b ω)) P := i1.sub i2
      rw [e, integral_add i3 hB, integral_sub i1 i2, integral_const_mul,
        integral_const_mul]
      ring
    rw [← h1]
    exact integral_nonneg fun ω => sq_nonneg _
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith [this]

/-! ### The numerical constant -/

private lemma ma_numeric (γ CSig ϱlo ϱ' β b I0 x0 d0 mm nn c1 s2 V : ℝ) (ℓ : ℕ)
    (hb : 1 ≤ b) (hγ : 0 ≤ γ) (hC : 0 ≤ CSig) (hϱlo : 0 < ϱlo) (hϱ' : ϱlo ≤ ϱ')
    (hβ : 0 ≤ β) (hI : I0 ^ 2 ≤ x0 * d0) (hx0 : x0 ≤ γ * b) (hx0n : 0 ≤ x0)
    (hd0n : 0 ≤ d0) (hd0 : d0 ≤ ϱ'⁻¹ * (β ^ (2 * ℓ) * (c1 + s2 * V)))
    (hc1 : 0 ≤ c1) (hc1' : c1 ≤ CSig ^ 2) (hs2 : 0 ≤ s2) (hs2' : s2 ≤ 1)
    (hV : 0 ≤ V) (hV' : V ≤ CSig ^ 2 * (mm * nn + 2 * mm + 2 * nn + 3) / b)
    (hmm : 0 ≤ mm) (hmm' : mm ≤ γ * b) (hnn : 0 ≤ nn) (hnn' : nn ≤ γ * b) :
    |b⁻¹ * I0| ≤ CSig * Real.sqrt (2 * γ * (γ ^ 2 + 4 * γ + 3) / ϱlo) * β ^ ℓ := by
  have hbpos : 0 < b := by linarith
  have hZ : 0 ≤ 2 * γ * (γ ^ 2 + 4 * γ + 3) / ϱlo := by positivity
  have hR : 0 ≤ CSig * Real.sqrt (2 * γ * (γ ^ 2 + 4 * γ + 3) / ϱlo) * β ^ ℓ := by positivity
  refine abs_le_of_sq_le_sq ?_ hR
  have hVb : V ≤ CSig ^ 2 * (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b := by
    refine hV'.trans ?_
    refine div_le_div_of_nonneg_right ?_ hbpos.le
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    nlinarith [mul_le_mul hmm' hnn' hnn (by positivity : 0 ≤ γ * b)]
  have hsV : s2 * V ≤ V := mul_le_of_le_one_left hV hs2'
  have hinv : ϱ'⁻¹ ≤ ϱlo⁻¹ := inv_anti₀ hϱlo hϱ'
  have hbeta : 0 ≤ β ^ (2 * ℓ) := by positivity
  have hd1 : d0 ≤ ϱlo⁻¹ * (β ^ (2 * ℓ) * (CSig ^ 2 +
      CSig ^ 2 * (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b)) := by
    refine hd0.trans ?_
    have h1 : c1 + s2 * V ≤ CSig ^ 2 + CSig ^ 2 * (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b := by
      linarith
    have h2 : 0 ≤ c1 + s2 * V := by positivity
    calc ϱ'⁻¹ * (β ^ (2 * ℓ) * (c1 + s2 * V))
        ≤ ϱlo⁻¹ * (β ^ (2 * ℓ) * (c1 + s2 * V)) :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hbeta) (by positivity)
  have hkey : (1 + (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b) / b ≤ γ ^ 2 + 4 * γ + 4 := by
    have e : (1 + (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b) / b =
        (b + γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b ^ 2 := by
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hγ (sub_nonneg.mpr hb), sq_nonneg (b - 1), mul_nonneg hγ hbpos.le]
  have hfin : (b⁻¹ * I0) ^ 2 ≤ γ * d0 / b := by
    calc (b⁻¹ * I0) ^ 2 = I0 ^ 2 / b ^ 2 := by field_simp
      _ ≤ (x0 * d0) / b ^ 2 := div_le_div_of_nonneg_right hI (by positivity)
      _ ≤ (γ * b * d0) / b ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hx0 hd0n) (by positivity)
      _ = γ * d0 / b := by field_simp
  have hRsq : (CSig * Real.sqrt (2 * γ * (γ ^ 2 + 4 * γ + 3) / ϱlo) * β ^ ℓ) ^ 2 =
      ϱlo⁻¹ * (β ^ (2 * ℓ) * (CSig ^ 2 * (2 * γ * (γ ^ 2 + 4 * γ + 3)))) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hZ, ← pow_mul, mul_comm ℓ 2]
    field_simp
  rw [hRsq]
  calc (b⁻¹ * I0) ^ 2 ≤ γ * d0 / b := hfin
    _ ≤ γ * (ϱlo⁻¹ * (β ^ (2 * ℓ) * (CSig ^ 2 +
          CSig ^ 2 * (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b))) / b :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd1 hγ) hbpos.le
    _ = ϱlo⁻¹ * (β ^ (2 * ℓ) * (CSig ^ 2 * γ *
          ((1 + (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b) / b))) := by
        field_simp
    _ ≤ ϱlo⁻¹ * (β ^ (2 * ℓ) * (CSig ^ 2 * γ * (γ ^ 2 + 4 * γ + 4))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hbeta) (by positivity)
        exact mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hbeta) (by positivity)
        nlinarith [mul_nonneg (sq_nonneg CSig) hγ, mul_nonneg (mul_nonneg (sq_nonneg CSig) hγ)
          (by positivity : (0:ℝ) ≤ γ ^ 2 + 4 * γ + 2)]

/-! ### The lag bound for `ℓ ≥ 1` -/

private lemma ma_fro_triangle (K L : Mat m n) : fro (K - L) ≤ fro K + fro L := by
  have h := ma_fro_sq (K - L)
  have hK := ma_fro_sq K
  have hL := ma_fro_sq L
  have hcs : (∑ i, ∑ j, K i j * L i j) ≤ fro K * fro L := by
    have := ma_trace_mul_transpose_le K L
    have htr : Matrix.trace (K * Lᵀ) = ∑ i, ∑ j, K i j * L i j := by
      simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    rw [htr] at this
    exact (le_abs_self _).trans this
  have hexp : fro (K - L) ^ 2 = fro K ^ 2 + fro L ^ 2 - 2 * ∑ i, ∑ j, K i j * L i j := by
    rw [h, hK, hL]
    simp only [Matrix.sub_apply, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum]
    ring_nf
  have hle : fro (K - L) ^ 2 ≤ (fro K + fro L) ^ 2 := by
    rw [hexp]
    have : 0 ≤ ∑ i, ∑ j, K i j * L i j + fro K * fro L := by
      have h0 := ma_trace_mul_transpose_le K L
      have htr : Matrix.trace (K * Lᵀ) = ∑ i, ∑ j, K i j * L i j := by
        simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      rw [htr] at h0
      have := neg_abs_le (∑ i, ∑ j, K i j * L i j)
      linarith
    nlinarith
  exact (pow_le_pow_iff_left₀ (ma_fro_nn _) (add_nonneg (ma_fro_nn _) (ma_fro_nn _))
    two_ne_zero).mp hle

private lemma ma_fro_meas : Measurable (fun K : Mat m n => fro K) := by
  unfold fro
  fun_prop


private lemma ma_reduce [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (Fo : Mat m m) (Gi : Mat n n)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1) {ϱ ϱ' : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ'0 : 0 ≤ ϱ')
    (t : ℤ) (ℓ : ℕ) (Mtr : Ω → Mat m n) (htr : Measurable Mtr)
    (hind : IndepFun (frozenBuf F S t) Mtr P) :
    ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (centredUpd F S ϱ' (t + (ℓ : ℤ)) ω)ᵀ) ∂P =
      ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) - Q ϱ' (Mtr ω))ᵀ) ∂P := by
  haveI := ma_borel m n
  haveI := ma_sc m n
  -- measurable ingredients
  have hbuf := ma_buf_meas F S (t + (ℓ : ℤ))
  have hX := ma_cen_meas F S hϱ0 t
  have hNt : Measurable (fun ω => Q ϱ' (Mtr ω)) :=
    (ma_Q_meas hϱ'0).comp htr
  have hUn : Measurable (fun ω => Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω)) :=
    (ma_Q_meas hϱ'0).comp hbuf
  have hDd : Measurable (fun ω => Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
      Q ϱ' (Mtr ω)) := by
    have hsub : Measurable (fun p : Mat m n × Mat m n => p.1 - p.2) :=
      (continuous_fst.sub continuous_snd).measurable
    exact hsub.comp (hUn.prodMk hNt)
  have hsq : Real.sqrt ((min m n : ℕ) : ℝ) ≥ 0 := Real.sqrt_nonneg _
  have hXi := ma_cen_fro_le F S hϱ0 t
  -- bounds on Nt, Dd
  have hNtb : ∀ ω, fro (Q ϱ' (Mtr ω)) ≤
      Real.sqrt ((min m n : ℕ) : ℝ) := fun ω => ma_Q_fro_le hϱ'0 _
  have hDdb : ∀ ω, fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
      Q ϱ' (Mtr ω)) ≤ 2 * Real.sqrt ((min m n : ℕ) : ℝ) := by
    intro ω
    have h1 := ma_Q_fro_le hϱ'0 (frozenBuf F S (t + (ℓ : ℤ)) ω)
    have h2 := ma_Q_fro_le hϱ'0 (Mtr ω)
    have h3 : fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
        Q ϱ' (Mtr ω)) ≤
        fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω)) +
        fro (Q ϱ' (Mtr ω)) := by
      have := ma_fro_triangle (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω))
        (Q ϱ' (Mtr ω))
      exact this
    linarith
  -- the three pieces of the pairing
  set ν := mean P (frozenUpd F S ϱ' (t + (ℓ : ℤ))) with hν
  have hνb : ∀ i j, |ν i j| ≤ Real.sqrt ((min m n : ℕ) : ℝ) :=
    fun i j => ma_mean_entry F S hϱ'0 _ i j
  have hνf : fro ν ≤ Real.sqrt ((m : ℝ) * n) * Real.sqrt ((min m n : ℕ) : ℝ) :=
    ma_fro_le_of_entries ν _ hsq hνb
  have hpt : ∀ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (centredUpd F S ϱ' (t + (ℓ : ℤ)) ω)ᵀ) =
      Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) - Q ϱ' (Mtr ω))ᵀ) +
      Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (Mtr ω))ᵀ) -
      Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi * νᵀ) := by
    intro ω
    have e : centredUpd F S ϱ' (t + (ℓ : ℤ)) ω =
        (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) - Q ϱ' (Mtr ω)) +
          Q ϱ' (Mtr ω) - ν := by
      simp only [centredUpd, frozenUpd, hν]
      abel
    rw [e]
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.mul_add, Matrix.mul_sub,
      Matrix.trace_add, Matrix.trace_sub]
  have iA : Integrable (fun ω => Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
          Q ϱ' (Mtr ω))ᵀ)) P :=
    ma_trace_integrable Fo Gi hF hG _ _ hX hDd _ _ hXi hDdb
  have iB : Integrable (fun ω => Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (Mtr ω))ᵀ)) P :=
    ma_trace_integrable Fo Gi hF hG _ _ hX hNt _ _ hXi hNtb
  have iC : Integrable (fun ω => Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi * νᵀ)) P :=
    ma_trace_integrable Fo Gi hF hG _ (fun _ => ν) hX measurable_const _ _ hXi (fun _ => hνf)
  have zB := ma_zero_indep F S Fo Gi hF hG hϱ0 hϱ'0 t Mtr htr hind
  have zC := ma_zero_const (P := P) Fo Gi (centredUpd F S ϱ t)
    (ma_cen_entry_int F S hϱ0 t) (ma_cen_entry_zero F S hϱ0 t) ν
  have hI0 : ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (centredUpd F S ϱ' (t + (ℓ : ℤ)) ω)ᵀ) ∂P =
      ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
          Q ϱ' (Mtr ω))ᵀ) ∂P := by
    have iAB : Integrable (fun ω => Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
          Q ϱ' (Mtr ω))ᵀ) +
        Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (Mtr ω))ᵀ)) P := iA.add iB
    simp_rw [hpt]
    rw [integral_sub iAB iC, integral_add iA iB, zB, zC]
    ring
  exact hI0

private lemma ma_atoms_zero [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (γstar CSig : ℝ) (hS : SizeFin F.C B γstar CSig)
    (SP : SpectralData F.C) {ϱ ϱ' : ℝ} (hϱ : 0 ≤ ϱ) (hϱ' : 0 ≤ ϱ') (t : ℤ) :
    ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP,
      |def_app_vol_lag F S 0 t (projOut SP μ) (projIn SP l) ϱ ϱ'| ≤ γstar := by
  haveI := ma_borel m n
  haveI := ma_sc m n
  have hBpos : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hX := ma_cen_meas F S hϱ t
  have hY := ma_cen_meas F S hϱ' t
  have hXi := ma_cen_fro_le F S hϱ t
  have hYi := ma_cen_fro_le F S hϱ' t
  have hsqX : Integrable (fun ω => fro (centredUpd F S ϱ t ω) ^ 2) P := by
    refine Integrable.of_bound (C := (Real.sqrt ((m : ℝ) * n) * (2 * Real.sqrt ((min m n : ℕ) : ℝ))) ^ 2) ?_
      (Filter.Eventually.of_forall fun ω => ?_)
    · have hfro : Measurable (fun K : Mat m n => fro K ^ 2) := by
        unfold fro; fun_prop
      exact (hfro.comp hX).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (ma_fro_nn _) (hXi ω) 2
  have hsqY : Integrable (fun ω => fro (centredUpd F S ϱ' t ω) ^ 2) P := by
    refine Integrable.of_bound (C := (Real.sqrt ((m : ℝ) * n) * (2 * Real.sqrt ((min m n : ℕ) : ℝ))) ^ 2) ?_
      (Filter.Eventually.of_forall fun ω => ?_)
    · have hfro : Measurable (fun K : Mat m n => fro K ^ 2) := by
        unfold fro; fun_prop
      exact (hfro.comp hY).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (ma_fro_nn _) (hYi ω) 2
  have h1 := mt_atoms_integral_le (P := P) SP (centredUpd F S ϱ t) (centredUpd F S ϱ' t) hX hY _ _
    hXi hYi
  have h1' : ∫ ω, fro (centredUpd F S ϱ t ω) * fro (centredUpd F S ϱ' t ω) ∂P ≤
      ∫ ω, (fro (centredUpd F S ϱ t ω) ^ 2 / 2 + fro (centredUpd F S ϱ' t ω) ^ 2 / 2) ∂P := by
    have hfm : Measurable (fun ω => fro (centredUpd F S ϱ t ω)) := ma_fro_meas.comp hX
    have hgm : Measurable (fun ω => fro (centredUpd F S ϱ' t ω)) := ma_fro_meas.comp hY
    refine integral_mono ?_ ((hsqX.div_const 2).add (hsqY.div_const 2)) fun ω => ?_
    · exact ma_int_mul_bdd _ _ hfm hgm _ _
        (fun ω => by rw [abs_of_nonneg (ma_fro_nn _)]; exact hXi ω)
        (fun ω => by rw [abs_of_nonneg (ma_fro_nn _)]; exact hYi ω)
    · nlinarith [sq_nonneg (fro (centredUpd F S ϱ t ω) - fro (centredUpd F S ϱ' t ω))]
  have h2 : ∫ ω, (fro (centredUpd F S ϱ t ω) ^ 2 / 2 + fro (centredUpd F S ϱ' t ω) ^ 2 / 2) ∂P
      ≤ ((min m n : ℕ) : ℝ) := by
    rw [integral_add (hsqX.div_const 2) (hsqY.div_const 2), integral_div, integral_div]
    have a1 := ma_cen_sq_int_le F S hϱ t
    have a2 := ma_cen_sq_int_le F S hϱ' t
    linarith
  have h3 : ((min m n : ℕ) : ℝ) ≤ γstar * B :=
    le_trans (by exact_mod_cast min_le_max) hS.1
  have hrw : ∀ μ l, |def_app_vol_lag F S 0 t (projOut SP μ) (projIn SP l) ϱ ϱ'| =
      (B : ℝ)⁻¹ * |∫ ω, Matrix.trace (projOut SP μ * centredUpd F S ϱ t ω * projIn SP l *
        (centredUpd F S ϱ' t ω)ᵀ) ∂P| := by
    intro μ l
    unfold def_app_vol_lag
    simp only [Nat.cast_zero, add_zero]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hBpos)]
  simp_rw [hrw]
  simp_rw [← Finset.mul_sum]
  rw [inv_mul_le_iff₀ hBpos]
  linarith

private lemma ma_atoms_pos [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (γstar CSig ϱlo ϱhi : ℝ) (hS : SizeFin F.C B γstar CSig)
    (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) (SP : SpectralData F.C) (ϱ ϱ' : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi)
    (hϱ'I : ϱ' ∈ Set.Icc ϱlo ϱhi) (t : ℤ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (Mtr : Ω → Mat m n)
    (htr : Measurable Mtr) (hind : IndepFun (frozenBuf F S t) Mtr P)
    (hd : ∫ ω, (fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) - Q ϱ' (Mtr ω))) ^ 2 ∂P ≤
      ϱ'⁻¹ * (F.β ^ (2 * ℓ) *
        (fro (mean P (frozenBatchG F S (t + (ℓ : ℤ) + 1))) ^ 2 + sPow F.β 2 * frozenVB S F)))
    (hmean : fro (mean P (frozenBatchG F S (t + (ℓ : ℤ) + 1))) ≤ CSig)
    (hVB : frozenVB S F ≤ CSig ^ 2 * ((m : ℝ) * n + 2 * m + 2 * n + 3) / (B : ℝ)) :
    ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP,
      |def_app_vol_lag F S ℓ t (projOut SP μ) (projIn SP l) ϱ ϱ'| ≤
        Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ ℓ := by
  haveI := ma_borel m n
  haveI := ma_sc m n
  have hϱ0 : 0 ≤ ϱ := le_trans hϱ.1.le hϱI.1
  have hϱ'pos : 0 < ϱ' := lt_of_lt_of_le hϱ.1 hϱ'I.1
  have hϱ'0 : 0 ≤ ϱ' := hϱ'pos.le
  have hBpos : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast F.hB
  obtain ⟨hβ0, hβ1⟩ := F.hβ
  have hbuf := ma_buf_meas F S (t + (ℓ : ℤ))
  have hX := ma_cen_meas F S hϱ0 t
  have hNt : Measurable (fun ω => Q ϱ' (Mtr ω)) :=
    (ma_Q_meas hϱ'0).comp htr
  have hUn : Measurable (fun ω => Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω)) :=
    (ma_Q_meas hϱ'0).comp hbuf
  have hDd : Measurable (fun ω => Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
      Q ϱ' (Mtr ω)) := by
    have hsub : Measurable (fun p : Mat m n × Mat m n => p.1 - p.2) :=
      (continuous_fst.sub continuous_snd).measurable
    exact hsub.comp (hUn.prodMk hNt)
  have hsq : Real.sqrt ((min m n : ℕ) : ℝ) ≥ 0 := Real.sqrt_nonneg _
  have hXi := ma_cen_fro_le F S hϱ0 t
  have hDdb : ∀ ω, fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
      Q ϱ' (Mtr ω)) ≤ 2 * Real.sqrt ((min m n : ℕ) : ℝ) := by
    intro ω
    have h1 := ma_Q_fro_le hϱ'0 (frozenBuf F S (t + (ℓ : ℤ)) ω)
    have h2 := ma_Q_fro_le hϱ'0 (Mtr ω)
    have h3 := ma_fro_triangle (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω)) (Q ϱ' (Mtr ω))
    linarith
  -- sum of atoms
  have hatoms := mt_atoms_integral_le (P := P) SP (centredUpd F S ϱ t)
    (fun ω => Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) - Q ϱ' (Mtr ω)) hX hDd _ _ hXi hDdb
  have hrw : ∀ μ l, |def_app_vol_lag F S ℓ t (projOut SP μ) (projIn SP l) ϱ ϱ'| =
      (B : ℝ)⁻¹ * |∫ ω, Matrix.trace (projOut SP μ * centredUpd F S ϱ t ω * projIn SP l *
        (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) - Q ϱ' (Mtr ω))ᵀ) ∂P| := by
    intro μ l
    unfold def_app_vol_lag
    rw [ma_reduce F S _ _ (mt_proj_opNorm SP μ l).1 (mt_proj_opNorm SP μ l).2 hϱ0 hϱ'0 t ℓ Mtr htr hind,
      abs_mul, abs_of_pos (inv_pos.mpr hBpos)]
  simp_rw [hrw]
  simp_rw [← Finset.mul_sum]
  -- Cauchy–Schwarz
  have hsqint : ∀ (f : Ω → ℝ), Measurable f → ∀ c : ℝ, (∀ ω, |f ω| ≤ c) →
      Integrable (fun ω => f ω ^ 2) P := fun f hf c hc =>
    Integrable.of_bound (C := c ^ 2) (hf.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hc ω) 2)
  have haM : Measurable (fun ω => fro (centredUpd F S ϱ t ω)) := ma_fro_meas.comp hX
  have hbM : Measurable (fun ω => fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
      Q ϱ' (Mtr ω))) := ma_fro_meas.comp hDd
  have haI := hsqint _ haM _ (fun ω => by
    rw [abs_of_nonneg (ma_fro_nn _)]; exact hXi ω)
  have hbI := hsqint _ hbM _ (fun ω => by
    rw [abs_of_nonneg (ma_fro_nn _)]; exact hDdb ω)
  have hcs := ma_cs _ _ haM hbM haI hbI
  have hI1' : 0 ≤ ∫ ω, fro (centredUpd F S ϱ t ω) * fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
        Q ϱ' (Mtr ω)) ∂P :=
    integral_nonneg fun ω => mul_nonneg (ma_fro_nn _) (ma_fro_nn _)
  have hs2 : sPow F.β 2 = (1 - F.β) / (1 + F.β) := eqn_app_setup_weights_iii hβ0 hβ1
  have hs2n : 0 ≤ sPow F.β 2 := by rw [hs2]; exact div_nonneg (by linarith) (by linarith)
  have hs2l : sPow F.β 2 ≤ 1 := by
    rw [hs2, div_le_one (by linarith)]; linarith
  have hVn : 0 ≤ frozenVB S F := integral_nonneg fun ω => sq_nonneg _
  have hγ : 0 ≤ γstar := by
    have h1 : (0 : ℝ) ≤ ((max m n : ℕ) : ℝ) := Nat.cast_nonneg _
    have := hS.1
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg hBpos]
  have hCs : 0 ≤ CSig := le_trans (ma_opNorm_nonneg _) hS.2.1
  have hx0 : ∫ ω, fro (centredUpd F S ϱ t ω) ^ 2 ∂P ≤ γstar * B := by
    refine (ma_cen_sq_int_le F S hϱ0 t).trans ?_
    exact le_trans (by exact_mod_cast min_le_max) hS.1
  have hmm' : (m : ℝ) ≤ γstar * B := le_trans (by exact_mod_cast le_max_left m n) hS.1
  have hnn' : (n : ℝ) ≤ γstar * B := le_trans (by exact_mod_cast le_max_right m n) hS.1
  have hnum := ma_numeric γstar CSig ϱlo ϱ' F.β (B : ℝ)
    (∫ ω, fro (centredUpd F S ϱ t ω) * fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
        Q ϱ' (Mtr ω)) ∂P)
    (∫ ω, fro (centredUpd F S ϱ t ω) ^ 2 ∂P)
    (∫ ω, fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
        Q ϱ' (Mtr ω)) ^ 2 ∂P)
    (m : ℝ) (n : ℝ) (fro (mean P (frozenBatchG F S (t + (ℓ : ℤ) + 1))) ^ 2) (sPow F.β 2)
    (frozenVB S F) ℓ hB1 hγ hCs hϱ.1 hϱ'I.1 hβ0
    hcs hx0 (integral_nonneg fun ω => sq_nonneg _) (integral_nonneg fun ω => sq_nonneg _) hd
    (sq_nonneg _) (pow_le_pow_left₀ (ma_fro_nn _) hmean 2) hs2n hs2l hVn hVB (Nat.cast_nonneg _) hmm'
    (Nat.cast_nonneg _) hnn'
  have hle : (B : ℝ)⁻¹ * (∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP,
      |∫ ω, Matrix.trace (projOut SP μ * centredUpd F S ϱ t ω * projIn SP l *
        (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) - Q ϱ' (Mtr ω))ᵀ) ∂P|) ≤
      (B : ℝ)⁻¹ * ∫ ω, fro (centredUpd F S ϱ t ω) * fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
        Q ϱ' (Mtr ω)) ∂P :=
    mul_le_mul_of_nonneg_left hatoms (inv_nonneg.mpr hBpos.le)
  refine hle.trans ?_
  refine (le_abs_self _).trans ?_
  unfold Muon.Dynamics.kStar
  exact hnum

private lemma ma_tv_actual [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (γstar CSig ϱlo ϱhi : ℝ) (hS : SizeFin F.C B γstar CSig)
    (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) (SP : SpectralData F.C) (ϱ ϱ' : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi)
    (hϱ'I : ϱ' ∈ Set.Icc ϱlo ϱhi) (t : ℤ) (ℓ : ℕ) :
    (ℓ = 0 → ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP,
      |def_app_vol_lag F S 0 t (projOut SP μ) (projIn SP l) ϱ ϱ'| ≤ γstar) ∧
    (1 ≤ ℓ → ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP,
      |def_app_vol_lag F S ℓ t (projOut SP μ) (projIn SP l) ϱ ϱ'| ≤
        Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ ℓ) := by
  have hϱ0 : 0 ≤ ϱ := le_trans hϱ.1.le hϱI.1
  have hϱ'pos : 0 < ϱ' := lt_of_lt_of_le hϱ.1 hϱ'I.1
  refine ⟨fun h => ?_, fun hℓ => ?_⟩
  · subst h
    exact ma_atoms_zero F S γstar CSig hS SP hϱ0 hϱ'pos.le t
  · obtain ⟨J, hJ⟩ : ∃ J : ℕ, J + 1 = ℓ := ⟨ℓ - 1, by omega⟩
    obtain ⟨-, hd⟩ := lem_app_setup_truncation_ii ϱ' hϱ'pos F S (t + (ℓ : ℤ)) J
    obtain ⟨hmean, hVB⟩ := lem_app_setup_truncation_iv ϱ' hϱ'pos F S (t + (ℓ : ℤ)) CSig hS.2.1 hS.2.2
    have hexp : 2 * (J + 1) = 2 * ℓ := by omega
    rw [hexp] at hd
    have hind := ma_indep F S t (t + (ℓ : ℤ)) J (by omega)
    have hmeas : Measurable (fun ω => ∑ j ∈ Finset.range (J + 1),
        emaW F.β j • frozenBatchG F S (t + (ℓ : ℤ) + 1 - (j : ℤ)) ω) := by
      haveI := ma_borel m n
      haveI := ma_sc m n
      exact Finset.measurable_sum _ fun j _ => (ma_batch_meas F S _).const_smul (emaW F.β j)
    exact ma_atoms_pos F S γstar CSig ϱlo ϱhi hS hϱ SP ϱ ϱ' hϱI hϱ'I t ℓ hℓ _ hmeas hind hd hmean hVB

open Classical in
private lemma ma_pair_regroup {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) (c : Fin m → Fin n → ℝ) :
    ∑ a : Fin m, ∑ b : Fin n, Finsupp.single (x a, y b) (c a b) =
      pairMeasure (Finset.univ.image x) (Finset.univ.image y)
        (fun μ l => ∑ a, ∑ b, classDiag x μ a * classDiag y l b * c a b) := by
  ext ⟨u, v⟩
  rw [mm_pairMeasure_apply]
  simp_rw [Finsupp.finsetSum_apply, Finsupp.single_apply]
  by_cases hu : u ∈ Finset.univ.image x
  · by_cases hv : v ∈ Finset.univ.image y
    · rw [if_pos ⟨hu, hv⟩]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases h1 : x a = u <;> by_cases h2 : y b = v <;> simp [classDiag, h1, h2, Prod.ext_iff]
    · rw [if_neg (fun h => hv h.2)]
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      intro h
      exact hv (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, (Prod.ext_iff.mp h).2⟩)
  · rw [if_neg (fun h => hu h.1)]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    intro h
    exact hu (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, (Prod.ext_iff.mp h).1⟩)

private lemma ma_pair_sub (xs ys : Finset ℝ) (v w : ℝ → ℝ → ℝ) :
    pairMeasure xs ys v - pairMeasure xs ys w = pairMeasure xs ys (fun μ l => v μ l - w μ l) := by
  ext ⟨u, y⟩
  rw [Finsupp.sub_apply, mm_pairMeasure_apply, mm_pairMeasure_apply, mm_pairMeasure_apply]
  split_ifs <;> simp

private lemma ma_entry_sq_int [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (SP : SpectralData F.C) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (T : ℕ)
    (i : Fin m) (j : Fin n) :
    Integrable (fun ω =>
      ((SP.uOutᵀ * (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), centredUpd F S ϱ s ω) * SP.vIn) i j) ^ 2) P := by
  haveI := ma_borel m n
  haveI := ma_sc m n
  have hmeasS : Measurable (fun ω => ∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), centredUpd F S ϱ s ω) :=
    Finset.measurable_sum _ fun s _ => ma_cen_meas F S hϱ s
  have hc : Continuous (fun K : Mat m n => (SP.uOutᵀ * K * SP.vIn) i j) := by fun_prop
  have hmeas : Measurable (fun ω =>
      (SP.uOutᵀ * (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), centredUpd F S ϱ s ω) * SP.vIn) i j) :=
    hc.measurable.comp hmeasS
  set c0 : ℝ := Real.sqrt ((m : ℝ) * n) * (2 * Real.sqrt ((min m n : ℕ) : ℝ)) with hc0
  have hbd : ∀ ω, |(SP.uOutᵀ * (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), centredUpd F S ϱ s ω) *
      SP.vIn) i j| ≤ (T : ℝ) * c0 := by
    intro ω
    have : (SP.uOutᵀ * (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), centredUpd F S ϱ s ω) * SP.vIn) i j =
        ∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), (SP.uOutᵀ * centredUpd F S ϱ s ω * SP.vIn) i j := by
      rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), |(SP.uOutᵀ * centredUpd F S ϱ s ω * SP.vIn) i j|
        ≤ ∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), c0 := by
          refine Finset.sum_le_sum fun s _ => ?_
          exact (ma_abs_entry_le_fro _ i j).trans
            ((mt_fro_orth_le SP.uOut SP.vIn SP.huOut SP.hvIn _).trans (ma_cen_fro_le F S hϱ s ω))
      _ = (T : ℝ) * c0 := by simp
  refine Integrable.of_bound (C := ((T : ℝ) * c0) ^ 2) (hmeas.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hbd ω) 2

private lemma ma_ftc_atom [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (SP : SpectralData F.C) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (T : ℕ) (μ l : ℝ) :
    finiteTimeCov F S T ϱ ϱ (projOut SP μ) (projIn SP l) =
      ∑ a : Fin m, ∑ b : Fin n, classDiag SP.μ μ a * classDiag SP.lam l b *
        (((B : ℝ) * (T : ℝ))⁻¹ * ∫ ω,
          ((SP.uOutᵀ * (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), centredUpd F S ϱ s ω) * SP.vIn) a b) ^ 2 ∂P) := by
  have hsq : ∀ a b, Integrable (fun ω =>
      (SP.uOutᵀ * (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), centredUpd F S ϱ s ω) * SP.vIn) a b *
      (SP.uOutᵀ * (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), centredUpd F S ϱ s ω) * SP.vIn) a b) P := by
    intro a b
    simpa [sq] using ma_entry_sq_int F S SP hϱ T a b
  unfold finiteTimeCov projOut projIn
  simp_rw [mt_trace_atom]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (hsq a b).const_mul _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => (hsq a b).const_mul _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]
  simp_rw [← sq]
  ring

private lemma ma_core (c : ℕ → ℝ) (M β : ℝ) (hM : 0 ≤ M) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc : ∀ ℓ : ℕ, 1 ≤ ℓ → |c ℓ| ≤ M * β ^ ℓ) (T : ℕ) (hT : 1 ≤ T) (a0 : ℝ) :
    |(a0 + ∑' ℓ : ℕ, c (ℓ + 1)) - (a0 + ∑ ℓ ∈ Finset.Ico 1 T, (1 - (ℓ : ℝ) / (T : ℝ)) * c ℓ)| ≤
      M * (β ^ T / (1 - β) + β / ((T : ℝ) * (1 - β) ^ 2)) := by
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  push_cast
  have hr : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1
  have hgeo : Summable (fun n : ℕ => β ^ n) := summable_geometric_of_lt_one hβ0 hβ1
  have hgeo1 : Summable (fun n : ℕ => β ^ (n + 1)) := (summable_nat_add_iff 1).mpr hgeo
  have hsl : Summable (fun n : ℕ => (n : ℝ) * β ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hsumg : Summable (fun j : ℕ => c (j + 1)) :=
    Summable.of_norm_bounded (hgeo1.mul_left M) (fun j => by
      rw [Real.norm_eq_abs]; exact hc (j + 1) (by omega))
  have hsplit : ∑ j ∈ Finset.range T', c (j + 1) + ∑' i : ℕ, c (i + T' + 1) =
      ∑' j : ℕ, c (j + 1) := hsumg.sum_add_tsum_nat_add T'
  have hIco : ∑ j ∈ Finset.range T', c (j + 1) = ∑ ℓ ∈ Finset.Ico 1 (T' + 1), c ℓ := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun j _ => by rw [add_comm]
  -- tail
  have hb : Summable (fun j : ℕ => M * β ^ (j + T' + 1)) := by
    have h1 : Summable (fun j : ℕ => β ^ (j + (T' + 1))) :=
      (summable_nat_add_iff (T' + 1)).mpr hgeo
    have h2 : Summable (fun j : ℕ => β ^ (j + T' + 1)) := by
      simpa only [add_assoc] using h1
    exact h2.mul_left M
  have hab : Summable (fun j : ℕ => |c (j + T' + 1)|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => hc _ (by omega)) hb
  have htail : |∑' j : ℕ, c (j + T' + 1)| ≤ M * β ^ (T' + 1) / (1 - β) := by
    have hab' : Summable (fun j : ℕ => ‖c (j + T' + 1)‖) := by
      simpa only [Real.norm_eq_abs] using hab
    have e1 := norm_tsum_le_tsum_norm hab'
    have e2 : ∑' j : ℕ, |c (j + T' + 1)| ≤ ∑' j : ℕ, M * β ^ (j + T' + 1) :=
      Summable.tsum_le_tsum (fun j => hc (j + T' + 1) (by omega)) hab hb
    have e3 : ∑' j : ℕ, M * β ^ (j + T' + 1) = M * β ^ (T' + 1) / (1 - β) := by
      have : (fun j : ℕ => M * β ^ (j + T' + 1)) = fun j => (M * β ^ (T' + 1)) * β ^ j :=
        funext fun j => by ring
      rw [this, tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1, div_eq_mul_inv]
    simp only [Real.norm_eq_abs] at e1
    linarith
  -- middle
  have hW1 : |∑ ℓ ∈ Finset.Ico 1 (T' + 1), ((ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ| ≤
      ∑ ℓ ∈ Finset.Ico 1 (T' + 1), (M / ((T' : ℝ) + 1)) * ((ℓ : ℝ) * β ^ ℓ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ℓ hℓ => ?_)
    have hℓ1 : 1 ≤ ℓ := (Finset.mem_Ico.mp hℓ).1
    have hnn : (0 : ℝ) ≤ (ℓ : ℝ) / ((T' : ℝ) + 1) := by positivity
    rw [abs_mul, abs_of_nonneg hnn]
    calc (ℓ : ℝ) / ((T' : ℝ) + 1) * |c ℓ| ≤ (ℓ : ℝ) / ((T' : ℝ) + 1) * (M * β ^ ℓ) :=
          mul_le_mul_of_nonneg_left (hc ℓ hℓ1) hnn
      _ = (M / ((T' : ℝ) + 1)) * ((ℓ : ℝ) * β ^ ℓ) := by ring
  have hW2 : ∑ ℓ ∈ Finset.Ico 1 (T' + 1), (M / ((T' : ℝ) + 1)) * ((ℓ : ℝ) * β ^ ℓ) ≤
      M / ((T' : ℝ) + 1) * (β / (1 - β) ^ 2) := by
    have h := Summable.sum_le_tsum (Finset.Ico 1 (T' + 1)) (fun ℓ _ => mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg hβ0 _)) hsl
    rw [tsum_coe_mul_geometric_of_norm_lt_one hr] at h
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h (div_nonneg hM (by positivity))
  -- assembly
  have hid : ∑ ℓ ∈ Finset.Ico 1 (T' + 1), (1 - (ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ =
      ∑ ℓ ∈ Finset.Ico 1 (T' + 1), c ℓ -
        ∑ ℓ ∈ Finset.Ico 1 (T' + 1), ((ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ℓ _ => by ring
  have key : (a0 + ∑' j : ℕ, c (j + 1)) - (a0 + ∑ ℓ ∈ Finset.Ico 1 (T' + 1),
      (1 - (ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ) =
      ∑' i : ℕ, c (i + T' + 1) + ∑ ℓ ∈ Finset.Ico 1 (T' + 1),
        ((ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ := by
    rw [hid, ← hIco, ← hsplit]
    ring
  rw [key]
  have hβ1' : (0 : ℝ) < 1 - β := sub_pos.mpr hβ1
  calc _ ≤ |∑' i : ℕ, c (i + T' + 1)| + |∑ ℓ ∈ Finset.Ico 1 (T' + 1),
        ((ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ| := abs_add_le _ _
    _ ≤ M * β ^ (T' + 1) / (1 - β) + M / ((T' : ℝ) + 1) * (β / (1 - β) ^ 2) :=
        add_le_add htail (hW1.trans hW2)
    _ = M * (β ^ (T' + 1) / (1 - β) + β / (((T' : ℝ) + 1) * (1 - β) ^ 2)) := by
        field_simp

private lemma ma_core_vec (xs ys : Finset ℝ) (c : ℝ → ℝ → ℕ → ℝ) (M β : ℝ) (hM : 0 ≤ M)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc : ∀ ℓ : ℕ, 1 ≤ ℓ → ∑ x ∈ xs, ∑ y ∈ ys, |c x y ℓ| ≤ M * β ^ ℓ) (T : ℕ) (hT : 1 ≤ T) :
    ∑ x ∈ xs, ∑ y ∈ ys, |∑' ℓ : ℕ, c x y (ℓ + 1) -
        ∑ ℓ ∈ Finset.Ico 1 T, (1 - (ℓ : ℝ) / (T : ℝ)) * c x y ℓ| ≤
      M * (β ^ T / (1 - β) + β / ((T : ℝ) * (1 - β) ^ 2)) := by
  have hgeo : Summable (fun n : ℕ => β ^ n) := summable_geometric_of_lt_one hβ0 hβ1
  have hgeo1 : Summable (fun n : ℕ => β ^ (n + 1)) := (summable_nat_add_iff 1).mpr hgeo
  have hsingle : ∀ x ∈ xs, ∀ y ∈ ys, ∀ ℓ : ℕ, 1 ≤ ℓ → |c x y ℓ| ≤ M * β ^ ℓ := by
    intro x hx y hy ℓ hℓ
    refine le_trans ?_ (hc ℓ hℓ)
    refine le_trans ?_ (Finset.single_le_sum (f := fun x => ∑ y ∈ ys, |c x y ℓ|)
      (fun x _ => Finset.sum_nonneg fun y _ => abs_nonneg _) hx)
    exact Finset.single_le_sum (f := fun y => |c x y ℓ|) (fun y _ => abs_nonneg _) hy
  have hsum : ∀ x ∈ xs, ∀ y ∈ ys, Summable (fun ℓ : ℕ => c x y (ℓ + 1)) := by
    intro x hx y hy
    exact Summable.of_norm_bounded (hgeo1.mul_left M) (fun j => by
      rw [Real.norm_eq_abs]; exact hsingle x hx y hy (j + 1) (by omega))
  set D : ℝ → ℝ → ℝ := fun x y => ∑' ℓ : ℕ, c x y (ℓ + 1) -
        ∑ ℓ ∈ Finset.Ico 1 T, (1 - (ℓ : ℝ) / (T : ℝ)) * c x y ℓ with hD
  set s : ℝ → ℝ → ℝ := fun x y => if 0 ≤ D x y then 1 else -1 with hs
  have habs : ∀ x y, |D x y| = s x y * D x y := by
    intro x y
    simp only [hs]
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.mp h)]; ring
  have hs1 : ∀ x y, |s x y| ≤ 1 := by
    intro x y; simp only [hs]; split_ifs <;> simp
  set cs : ℕ → ℝ := fun ℓ => ∑ x ∈ xs, ∑ y ∈ ys, s x y * c x y ℓ with hcs
  have hcsb : ∀ ℓ : ℕ, 1 ≤ ℓ → |cs ℓ| ≤ M * β ^ ℓ := by
    intro ℓ hℓ
    refine (hc ℓ hℓ).trans' ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hs1 x y)
  have hcore := ma_core cs M β hM hβ0 hβ1 hcsb T hT 0
  have e1 : ∑' ℓ : ℕ, cs (ℓ + 1) = ∑ x ∈ xs, ∑ y ∈ ys, s x y * ∑' ℓ : ℕ, c x y (ℓ + 1) := by
    simp only [hcs]
    rw [Summable.tsum_finsetSum]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [Summable.tsum_finsetSum]
      · refine Finset.sum_congr rfl fun y hy => ?_
        rw [tsum_mul_left]
      · intro y hy
        exact (hsum x hx y hy).mul_left _
    · intro x hx
      refine summable_sum fun y hy => ?_
      exact (hsum x hx y hy).mul_left _
  have e2 : ∑ ℓ ∈ Finset.Ico 1 T, (1 - (ℓ : ℝ) / (T : ℝ)) * cs ℓ =
      ∑ x ∈ xs, ∑ y ∈ ys, s x y * ∑ ℓ ∈ Finset.Ico 1 T, (1 - (ℓ : ℝ) / (T : ℝ)) * c x y ℓ := by
    simp only [hcs]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun ℓ _ => ?_
    ring
  have e3 : ∑ x ∈ xs, ∑ y ∈ ys, |D x y| = (0 + ∑' ℓ : ℕ, cs (ℓ + 1)) -
      (0 + ∑ ℓ ∈ Finset.Ico 1 T, (1 - (ℓ : ℝ) / (T : ℝ)) * cs ℓ) := by
    rw [zero_add, zero_add, e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [habs, hD]
    simp only
    ring
  have e4 : ∑ x ∈ xs, ∑ y ∈ ys, |D x y| = ∑ x ∈ xs, ∑ y ∈ ys, |∑' ℓ : ℕ, c x y (ℓ + 1) -
      ∑ ℓ ∈ Finset.Ico 1 T, (1 - (ℓ : ℝ) / (T : ℝ)) * c x y ℓ| := rfl
  rw [← e4, e3]
  exact (le_abs_self _).trans hcore

private lemma ma_entry_prod_int [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (SP : SpectralData F.C) {ϱ ϱ' : ℝ} (hϱ : 0 ≤ ϱ) (hϱ' : 0 ≤ ϱ')
    (s s' : ℤ) (i : Fin m) (j : Fin n) :
    Integrable (fun ω => (SP.uOutᵀ * centredUpd F S ϱ s ω * SP.vIn) i j *
      (SP.uOutᵀ * centredUpd F S ϱ' s' ω * SP.vIn) i j) P := by
  haveI := ma_borel m n
  haveI := ma_sc m n
  have hc : Continuous (fun K : Mat m n => (SP.uOutᵀ * K * SP.vIn) i j) := by fun_prop
  refine ma_int_mul_bdd _ _ (hc.measurable.comp (ma_cen_meas F S hϱ s))
    (hc.measurable.comp (ma_cen_meas F S hϱ' s'))
    (Real.sqrt ((m : ℝ) * n) * (2 * Real.sqrt ((min m n : ℕ) : ℝ)))
    (Real.sqrt ((m : ℝ) * n) * (2 * Real.sqrt ((min m n : ℕ) : ℝ))) (fun ω => ?_) (fun ω => ?_)
  · exact (ma_abs_entry_le_fro _ i j).trans
      ((mt_fro_orth_le SP.uOut SP.vIn SP.huOut SP.hvIn _).trans (ma_cen_fro_le F S hϱ s ω))
  · exact (ma_abs_entry_le_fro _ i j).trans
      ((mt_fro_orth_le SP.uOut SP.vIn SP.huOut SP.hvIn _).trans (ma_cen_fro_le F S hϱ' s' ω))

private lemma ma_lag_atom [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (SP : SpectralData F.C) {ϱ ϱ' : ℝ} (hϱ : 0 ≤ ϱ) (hϱ' : 0 ≤ ϱ')
    (ℓ : ℕ) (t : ℤ) (dx : Fin m → ℝ) (ey : Fin n → ℝ) :
    def_app_vol_lag F S ℓ t (SP.uOut * Matrix.diagonal dx * SP.uOutᵀ)
        (SP.vIn * Matrix.diagonal ey * SP.vInᵀ) ϱ ϱ' =
      (B : ℝ)⁻¹ * ∑ a : Fin m, ∑ b : Fin n, dx a * ey b *
        ∫ ω, (SP.uOutᵀ * centredUpd F S ϱ t ω * SP.vIn) a b *
          (SP.uOutᵀ * centredUpd F S ϱ' (t + (ℓ : ℤ)) ω * SP.vIn) a b ∂P := by
  unfold def_app_vol_lag
  simp_rw [mt_trace_atom]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ =>
    (ma_entry_prod_int F S SP hϱ hϱ' t (t + (ℓ : ℤ)) a b).const_mul _)]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ =>
    (ma_entry_prod_int F S SP hϱ hϱ' t (t + (ℓ : ℤ)) a b).const_mul _)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]

private lemma ma_single_diag_norm {k : ℕ} (U : Mat k k) (hU : Uᵀ * U = 1) (i : Fin k) :
    opNorm (U * Matrix.diagonal (Pi.single i (1 : ℝ) : Fin k → ℝ) * Uᵀ) ≤ 1 :=
  md_opNorm_conj U hU _ (fun i' => by
    by_cases h : i' = i <;> simp [Pi.single_apply, h])

private lemma ma_single_diag_symm {k : ℕ} (U : Mat k k) (x : Fin k → ℝ) :
    (U * Matrix.diagonal x * Uᵀ)ᵀ = U * Matrix.diagonal x * Uᵀ := by
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

private lemma ma_collapse {m n : ℕ} (i : Fin m) (j : Fin n) (f : Fin m → Fin n → ℝ) :
    ∑ a : Fin m, ∑ b : Fin n, (Pi.single i (1 : ℝ) : Fin m → ℝ) a *
      (Pi.single j (1 : ℝ) : Fin n → ℝ) b * f a b = f i j := by
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [Pi.single_apply, ha]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma ma_dis_entry [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (γstar CSig ϱlo ϱhi : ℝ) (hS : SizeFin F.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) (SP : SpectralData F.C) (ϱ : ℝ)
    (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) (t : ℤ) (i : Fin m) (j : Fin n) :
    Summable (fun ℓ : ℕ => |∫ ω,
        (SP.uOutᵀ * centredUpd F S ϱ t ω * SP.vIn) i j *
          (SP.uOutᵀ * centredUpd F S ϱ (t + ((ℓ : ℤ) + 1)) ω * SP.vIn) i j ∂P|) ∧
      integratedLag F S t (SP.uOut * Matrix.diagonal (Pi.single i (1 : ℝ) : Fin m → ℝ) * SP.uOutᵀ)
        (SP.vIn * Matrix.diagonal (Pi.single j (1 : ℝ) : Fin n → ℝ) * SP.vInᵀ) ϱ ϱ =
        (B : ℝ)⁻¹ * modeVijActual F S SP t ϱ i j ∧
      0 ≤ modeVijActual F S SP t ϱ i j ∧
      Summable (fun ℓ : ℕ => def_app_vol_lag F S (ℓ + 1) t
        (SP.uOut * Matrix.diagonal (Pi.single i (1 : ℝ) : Fin m → ℝ) * SP.uOutᵀ)
        (SP.vIn * Matrix.diagonal (Pi.single j (1 : ℝ) : Fin n → ℝ) * SP.vInᵀ) ϱ ϱ) := by
  have hϱ0 : 0 ≤ ϱ := le_trans hϱ.1.le hϱI.1
  have hBpos : (0 : ℝ) < B := by exact_mod_cast F.hB
  set Fi := SP.uOut * Matrix.diagonal (Pi.single i (1 : ℝ) : Fin m → ℝ) * SP.uOutᵀ with hFi
  set Gj := SP.vIn * Matrix.diagonal (Pi.single j (1 : ℝ) : Fin n → ℝ) * SP.vInᵀ with hGj
  have hFn : opNorm Fi ≤ 1 := ma_single_diag_norm SP.uOut SP.huOut i
  have hGn : opNorm Gj ≤ 1 := ma_single_diag_norm SP.vIn SP.hvIn j
  have hC : ∀ ℓ : ℕ, def_app_vol_lag F S ℓ t Fi Gj ϱ ϱ = (B : ℝ)⁻¹ * ∫ ω,
      (SP.uOutᵀ * centredUpd F S ϱ t ω * SP.vIn) i j *
        (SP.uOutᵀ * centredUpd F S ϱ (t + (ℓ : ℤ)) ω * SP.vIn) i j ∂P := by
    intro ℓ
    rw [hFi, hGj, ma_lag_atom F S SP hϱ0 hϱ0 ℓ t, ma_collapse i j]
  have hbd := (thm_app_vol_lag_reduction_ii_actual F S γstar CSig ϱlo ϱhi hS hCSig hϱ Fi Gj
    (ma_single_diag_symm _ _) (ma_single_diag_symm _ _) hFn hGn ϱ ϱ hϱI hϱI t).2
  have hg : ∀ ℓ : ℕ, ∫ ω, (SP.uOutᵀ * centredUpd F S ϱ t ω * SP.vIn) i j *
        (SP.uOutᵀ * centredUpd F S ϱ (t + ((ℓ : ℤ) + 1)) ω * SP.vIn) i j ∂P =
      (B : ℝ) * def_app_vol_lag F S (ℓ + 1) t Fi Gj ϱ ϱ := by
    intro ℓ
    rw [hC (ℓ + 1), ← mul_assoc, mul_inv_cancel₀ hBpos.ne', one_mul]
    push_cast
    rfl
  have hsum : Summable (fun ℓ : ℕ => def_app_vol_lag F S (ℓ + 1) t Fi Gj ϱ ϱ) := by
    have hgeo : Summable (fun n : ℕ => F.β ^ n) := summable_geometric_of_lt_one F.hβ.1 F.hβ.2
    have hgeo1 : Summable (fun n : ℕ => F.β ^ (n + 1)) := (summable_nat_add_iff 1).mpr hgeo
    exact Summable.of_norm_bounded (hgeo1.mul_left (Muon.Dynamics.kStar CSig γstar ϱlo))
      (fun ℓ => by rw [Real.norm_eq_abs]; exact hbd (ℓ + 1) (by omega))
  have hmv : modeVijActual F S SP t ϱ i j =
      (B : ℝ) * integratedLag F S t Fi Gj ϱ ϱ := by
    unfold modeVijActual integratedLag
    simp_rw [hg]
    rw [tsum_mul_left, hC 0]
    simp only [Nat.cast_zero, add_zero]
    have : ∀ ℓ : ℕ, def_app_vol_lag F S (ℓ + 1) t Fi Gj ϱ ϱ + def_app_vol_lag F S (ℓ + 1) t Fi Gj ϱ ϱ =
        2 * def_app_vol_lag F S (ℓ + 1) t Fi Gj ϱ ϱ := fun ℓ => by ring
    simp_rw [this]
    rw [tsum_mul_left, mul_add, ← mul_assoc (B : ℝ), mul_inv_cancel₀ hBpos.ne', one_mul]
    simp only [sq]
    ring
  refine ⟨?_, ?_, ?_, hsum⟩
  · simp_rw [hg, abs_mul, abs_of_pos hBpos]
    exact (hsum.abs).mul_left _
  · rw [hmv, ← mul_assoc, inv_mul_cancel₀ hBpos.ne', one_mul]
  · rw [hmv]
    refine mul_nonneg hBpos.le ?_
    -- nonnegativity of the integrated covariance via the finite-time identity
    have hT : ∀ T : ℕ, 0 ≤ finiteTimeCov F S T ϱ ϱ Fi Gj := by
      intro T
      unfold finiteTimeCov
      refine mul_nonneg (inv_nonneg.mpr (mul_nonneg hBpos.le (Nat.cast_nonneg T)))
        (integral_nonneg fun ω => ?_)
      rw [hFi, hGj, mt_trace_atom]
      refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
      have h1 : 0 ≤ (Pi.single i (1 : ℝ) : Fin m → ℝ) a := by
        by_cases h : a = i <;> simp [Pi.single_apply, h]
      have h2 : 0 ≤ (Pi.single j (1 : ℝ) : Fin n → ℝ) b := by
        by_cases h : b = j <;> simp [Pi.single_apply, h]
      exact mul_nonneg (mul_nonneg h1 h2) (mul_self_nonneg _)
    have hbound : ∀ T : ℕ, 1 ≤ T →
        |finiteTimeCov F S T ϱ ϱ Fi Gj - integratedLag F S t Fi Gj ϱ ϱ| ≤
          2 * Muon.Dynamics.kStar CSig γstar ϱlo *
            (F.β ^ T / (1 - F.β) + F.β / ((T : ℝ) * (1 - F.β) ^ 2)) := fun T hT1 =>
      thm_app_vol_lag_reduction_iii_bound F S γstar CSig ϱlo ϱhi hS hCSig hϱ Fi Gj
        (ma_single_diag_symm _ _) (ma_single_diag_symm _ _) hFn hGn ϱ ϱ hϱI hϱI T hT1 t
    obtain ⟨hβ0, hβ1⟩ := F.hβ
    have hlim : Filter.Tendsto (fun T : ℕ => 2 * Muon.Dynamics.kStar CSig γstar ϱlo *
        (F.β ^ T / (1 - F.β) + F.β / ((T : ℝ) * (1 - F.β) ^ 2))) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun T : ℕ => F.β ^ T / (1 - F.β)) Filter.atTop (nhds 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).div_const (1 - F.β)
      have h2 : Filter.Tendsto (fun T : ℕ => F.β / ((T : ℝ) * (1 - F.β) ^ 2)) Filter.atTop
          (nhds 0) := by
        have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const
          (show 0 < (1 - F.β) ^ 2 from by have : 0 < 1 - F.β := by linarith
                                          positivity)
        simpa using Filter.Tendsto.div_atTop (tendsto_const_nhds (x := F.β)) this
      simpa using (h1.add h2).const_mul (2 * Muon.Dynamics.kStar CSig γstar ϱlo)
    have hconv : Filter.Tendsto (fun T : ℕ => finiteTimeCov F S T ϱ ϱ Fi Gj - integratedLag F S t Fi Gj ϱ ϱ)
        Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [Filter.eventually_ge_atTop 1] with T hT1
      rw [Real.norm_eq_abs]
      exact hbound T hT1
    have hconv' : Filter.Tendsto (fun T : ℕ => finiteTimeCov F S T ϱ ϱ Fi Gj) Filter.atTop
        (nhds (integratedLag F S t Fi Gj ϱ ϱ)) := by
      simpa using hconv.add_const (integratedLag F S t Fi Gj ϱ ϱ)
    exact ge_of_tendsto' hconv' hT


private lemma ma_int_lin [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (γstar CSig : ℝ) (hS : SizeFin F.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (SP : SpectralData F.C) (ϱ : ℝ) (hϱ : 0 < ϱ) (t : ℤ)
    (dx : Fin m → ℝ) (ey : Fin n → ℝ) :
    integratedLag F S t (SP.uOut * Matrix.diagonal dx * SP.uOutᵀ)
        (SP.vIn * Matrix.diagonal ey * SP.vInᵀ) ϱ ϱ =
      ∑ a : Fin m, ∑ b : Fin n, dx a * ey b * integratedLag F S t
        (SP.uOut * Matrix.diagonal (Pi.single a (1 : ℝ) : Fin m → ℝ) * SP.uOutᵀ)
        (SP.vIn * Matrix.diagonal (Pi.single b (1 : ℝ) : Fin n → ℝ) * SP.vInᵀ) ϱ ϱ := by
  have hϱ0 : 0 ≤ ϱ := hϱ.le
  have hϱI : ϱ ∈ Set.Icc ϱ ϱ := ⟨le_rfl, le_rfl⟩
  have hlag : ∀ ℓ : ℕ, def_app_vol_lag F S ℓ t (SP.uOut * Matrix.diagonal dx * SP.uOutᵀ)
      (SP.vIn * Matrix.diagonal ey * SP.vInᵀ) ϱ ϱ = ∑ a : Fin m, ∑ b : Fin n, dx a * ey b *
        def_app_vol_lag F S ℓ t
          (SP.uOut * Matrix.diagonal (Pi.single a (1 : ℝ) : Fin m → ℝ) * SP.uOutᵀ)
          (SP.vIn * Matrix.diagonal (Pi.single b (1 : ℝ) : Fin n → ℝ) * SP.vInᵀ) ϱ ϱ := by
    intro ℓ
    rw [ma_lag_atom F S SP hϱ0 hϱ0 ℓ t dx ey, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ma_lag_atom F S SP hϱ0 hϱ0 ℓ t, ma_collapse a b (fun a' b' => ∫ ω,
      (SP.uOutᵀ * centredUpd F S ϱ t ω * SP.vIn) a' b' *
        (SP.uOutᵀ * centredUpd F S ϱ (t + (ℓ : ℤ)) ω * SP.vIn) a' b' ∂P)]
    ring
  have hsum := fun a b => (ma_dis_entry F S γstar CSig ϱ ϱ hS hCSig ⟨hϱ, le_rfl⟩ SP ϱ hϱI t a b).2.2.2
  unfold integratedLag
  simp_rw [hlag]
  have e1 : ∀ ℓ : ℕ, (∑ a : Fin m, ∑ b : Fin n, dx a * ey b * def_app_vol_lag F S (ℓ + 1) t
          (SP.uOut * Matrix.diagonal (Pi.single a (1 : ℝ) : Fin m → ℝ) * SP.uOutᵀ)
          (SP.vIn * Matrix.diagonal (Pi.single b (1 : ℝ) : Fin n → ℝ) * SP.vInᵀ) ϱ ϱ) +
        (∑ a : Fin m, ∑ b : Fin n, dx a * ey b * def_app_vol_lag F S (ℓ + 1) t
          (SP.uOut * Matrix.diagonal (Pi.single a (1 : ℝ) : Fin m → ℝ) * SP.uOutᵀ)
          (SP.vIn * Matrix.diagonal (Pi.single b (1 : ℝ) : Fin n → ℝ) * SP.vInᵀ) ϱ ϱ) =
      ∑ a : Fin m, ∑ b : Fin n, dx a * ey b * (def_app_vol_lag F S (ℓ + 1) t
          (SP.uOut * Matrix.diagonal (Pi.single a (1 : ℝ) : Fin m → ℝ) * SP.uOutᵀ)
          (SP.vIn * Matrix.diagonal (Pi.single b (1 : ℝ) : Fin n → ℝ) * SP.vInᵀ) ϱ ϱ +
        def_app_vol_lag F S (ℓ + 1) t
          (SP.uOut * Matrix.diagonal (Pi.single a (1 : ℝ) : Fin m → ℝ) * SP.uOutᵀ)
          (SP.vIn * Matrix.diagonal (Pi.single b (1 : ℝ) : Fin n → ℝ) * SP.vInᵀ) ϱ ϱ) := by
    intro ℓ
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp_rw [e1]
  rw [Summable.tsum_finsetSum]
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Summable.tsum_finsetSum]
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [tsum_mul_left]
      ring
    · intro b _
      exact Summable.mul_left (dx a * ey b) ((hsum a b).add (hsum a b))
  · intro a _
    refine summable_sum fun b _ => ?_
    exact Summable.mul_left (dx a * ey b) ((hsum a b).add (hsum a b))

end MaCopy

section JFHelpers

open scoped Matrix.Norms.L2Operator in
private lemma jf_abs_eig_le_opNorm {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (w : Fin k → ℝ) (μ : ℝ)
    (hw : ∑ a, w a * w a = 1) (he : A *ᵥ w = μ • w) : |μ| ≤ opNorm A := by
  set x : EuclideanSpace ℝ (Fin k) := (EuclideanSpace.equiv (Fin k) ℝ).symm w with hxdef
  have hsum : ∑ a, ‖x a‖ ^ 2 = 1 := by
    have hterm : ∀ a, ‖x a‖ ^ 2 = w a * w a := fun a => by
      rw [Real.norm_eq_abs, sq_abs, sq]
      rfl
    simp only [hterm]
    exact hw
  have hx : ‖x‖ = 1 := by rw [EuclideanSpace.norm_eq, hsum, Real.sqrt_one]
  have h1 := Matrix.l2_opNorm_mulVec A x
  have h2 : (EuclideanSpace.equiv (Fin k) ℝ).symm (A *ᵥ ⇑x) = μ • x := by
    ext a
    have ha := congrFun he a
    simp only [hxdef, Pi.smul_apply, smul_eq_mul] at ha ⊢
    exact ha
  rw [h2, norm_smul, hx, Real.norm_eq_abs] at h1
  simp only [mul_one] at h1
  rw [opNorm_eq_norm]
  exact h1

private lemma jf_spec_mem {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (Cs : ℝ)
    (hout : opNorm C.Sout ≤ Cs) (hin : opNorm C.Sin ≤ Cs) :
    (∀ i, S.μ i ∈ Set.Icc (0 : ℝ) Cs) ∧ (∀ j, S.lam j ∈ Set.Icc (0 : ℝ) Cs) :=
  ⟨fun i => ⟨μ_nonneg S i, (le_abs_self _).trans ((jf_abs_eig_le_opNorm C.Sout (fun a => S.uOut a i)
      (S.μ i) (sum_col_sq_eq_one S.uOut S.huOut i) (S.eigOut i)).trans hout)⟩,
   fun j => ⟨lam_nonneg S j, (le_abs_self _).trans ((jf_abs_eig_le_opNorm C.Sin (fun a => S.vIn a j)
      (S.lam j) (sum_col_sq_eq_one S.vIn S.hvIn j) (S.eigIn j)).trans hin)⟩⟩

private lemma jf_finInt_pair (xs ys : Finset ℝ) (v : ℝ → ℝ → ℝ) (φ : ℝ × ℝ → ℝ) :
    finInt (pairMeasure xs ys v) φ = ∑ μ ∈ xs, ∑ l ∈ ys, v μ l * φ (μ, l) := by
  unfold finInt pairMeasure
  rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul])]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul])]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finsupp.sum_single_index (by simp)]

private lemma jf_lin_fsum {m : ℕ} (T : (Fin m → ℝ) → ℝ)
    (h : ∀ (c : ℝ) (F1 F2 : Fin m → ℝ), T (fun i => c * F1 i + F2 i) = c * T F1 + T F2)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (D : ι → Fin m → ℝ) :
    T (fun i => ∑ k ∈ s, c k * D k i) = ∑ k ∈ s, c k * T (D k) := by
  classical
  have h0 : T (fun _ => 0) = 0 := by
    have := h 1 (fun _ => 0) (fun _ => 0)
    simp only [mul_zero, zero_add] at this
    linarith
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    rw [← ih]
    exact h (c k) (D k) (fun i => ∑ k ∈ s, c k * D k i)

private lemma jf_bil {m n : ℕ} (T : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (h1 : ∀ (c : ℝ) (F1 F2 : Fin m → ℝ) (G : Fin n → ℝ),
      T (fun i => c * F1 i + F2 i) G = c * T F1 G + T F2 G)
    (h2 : ∀ (c : ℝ) (F : Fin m → ℝ) (G1 G2 : Fin n → ℝ),
      T F (fun j => c * G1 j + G2 j) = c * T F G1 + T F G2)
    (xs ys : Finset ℝ) (μv : Fin m → ℝ) (lv : Fin n → ℝ) (hx : ∀ i, μv i ∈ xs)
    (hy : ∀ j, lv j ∈ ys) (f g : ℝ → ℝ) :
    ∑ μ ∈ xs, ∑ l ∈ ys, f μ * g l * T (classDiag μv μ) (classDiag lv l) =
      T (fun i => f (μv i)) (fun j => g (lv j)) := by
  classical
  have ef : (fun i => f (μv i)) = fun i => ∑ μ ∈ xs, f μ * classDiag μv μ i := by
    funext i
    simp only [classDiag, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [hx i]
  have eg : (fun j => g (lv j)) = fun j => ∑ l ∈ ys, g l * classDiag lv l j := by
    funext j
    simp only [classDiag, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [hy j]
  rw [ef, eg]
  have hs : ∀ G : Fin n → ℝ, T (fun i => ∑ μ ∈ xs, f μ * classDiag μv μ i) G =
      ∑ μ ∈ xs, f μ * T (classDiag μv μ) G := fun G =>
    jf_lin_fsum (fun F => T F G) (fun c F1 F2 => h1 c F1 F2 G) xs f _
  have ht : ∀ F : Fin m → ℝ, T F (fun j => ∑ l ∈ ys, g l * classDiag lv l j) =
      ∑ l ∈ ys, g l * T F (classDiag lv l) := fun F =>
    jf_lin_fsum (fun G => T F G) (fun c G1 G2 => h2 c F G1 G2) ys g _
  rw [hs]
  simp_rw [ht, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => ?_
  ring

private lemma jf_BL (Cs h : ℝ) (hCs : 0 ≤ Cs) (hh : 0 < h) (xs ys : Finset ℝ)
    (hx : ∀ x ∈ xs, x ∈ Set.Icc (0 : ℝ) Cs) (hy : ∀ y ∈ ys, y ∈ Set.Icc (0 : ℝ) Cs)
    (v : ℝ → ℝ → ℝ) (δ : ℝ)
    (hprod : ∀ f g : ℝ → ℝ, (∀ x, |f x| ≤ 1) → (∀ x, |g x| ≤ 1) →
      |finInt (pairMeasure xs ys v) (fun p => f p.1 * g p.2)| ≤ δ)
    (φ : ℝ × ℝ → ℝ) (hφ : φ ∈ Muon.Dynamics.blTest Cs) :
    |finInt (pairMeasure xs ys v) φ| ≤
      ((⌊Cs / h⌋₊ + 1 : ℕ) : ℝ) ^ 2 * δ + 2 * h * ∑ μ ∈ xs, ∑ l ∈ ys, |v μ l| := by
  classical
  set N : ℕ := ⌊Cs / h⌋₊ with hN
  let r : ℝ → ℕ := fun x => ⌊x / h⌋₊
  have hr_le : ∀ x ∈ Set.Icc (0 : ℝ) Cs, r x ≤ N := fun x hx =>
    Nat.floor_le_floor (div_le_div_of_nonneg_right hx.2 hh.le)
  have hc_mem : ∀ a : ℕ, a ≤ N → h * a ∈ Set.Icc (0 : ℝ) Cs := by
    intro a ha
    refine ⟨by positivity, ?_⟩
    have h1 : (a : ℝ) ≤ Cs / h := (Nat.cast_le.mpr ha).trans (Nat.floor_le (div_nonneg hCs hh.le))
    calc h * a ≤ h * (Cs / h) := mul_le_mul_of_nonneg_left h1 hh.le
      _ = Cs := by field_simp
  have hcl : ∀ x ∈ Set.Icc (0 : ℝ) Cs, h * r x ≤ x ∧ x - h * r x ≤ h := by
    intro x hx
    have h0 : 0 ≤ x / h := div_nonneg hx.1 hh.le
    have a1 : (r x : ℝ) ≤ x / h := Nat.floor_le h0
    have a2 : x / h < r x + 1 := Nat.lt_floor_add_one _
    constructor
    · calc h * r x ≤ h * (x / h) := mul_le_mul_of_nonneg_left a1 hh.le
        _ = x := by field_simp
    · have : x < h * (r x + 1) := by
        have := mul_lt_mul_of_pos_left a2 hh
        rwa [show h * (x / h) = x by field_simp] at this
      linarith
  have hpt : ∀ μ ∈ xs, ∀ l ∈ ys, |φ (μ, l) - φ (h * r μ, h * r l)| ≤ 2 * h := by
    intro μ hμ l hl
    have h1 := hcl μ (hx μ hμ)
    have h2 := hcl l (hy l hl)
    have := hφ.2 (μ, l) ⟨hx μ hμ, hy l hl⟩ (h * r μ, h * r l)
      ⟨hc_mem _ (hr_le μ (hx μ hμ)), hc_mem _ (hr_le l (hy l hl))⟩
    refine this.trans ?_
    unfold Muon.Dynamics.l1
    simp only
    rw [abs_of_nonneg (by linarith [h1.1]), abs_of_nonneg (by linarith [h2.1])]
    linarith [h1.2, h2.2]
  -- the cell expansion
  let fr : ℕ → ℝ → ℝ := fun a x => if r x = a then 1 else 0
  have hfr : ∀ a x, |fr a x| ≤ 1 := by
    intro a x
    simp only [fr]
    split_ifs <;> simp
  have hcell : ∀ μ ∈ xs, ∀ l ∈ ys, φ (h * r μ, h * r l) =
      ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
        φ (h * a, h * b) * (fr a μ * fr b l) := by
    intro μ hμ l hl
    have ha : r μ ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (hr_le μ (hx μ hμ)))
    have hb : r l ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (hr_le l (hy l hl)))
    simp only [fr, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
    rw [Finset.sum_eq_single (r μ)]
    · rw [Finset.sum_eq_single (r l)]
      · simp
      · intro b _ hb'; simp [Ne.symm hb']
      · intro hn; exact absurd hb hn
    · intro a _ ha'; simp [Ne.symm ha']
    · intro hn; exact absurd ha hn
  have step1 : finInt (pairMeasure xs ys v) φ =
      ∑ μ ∈ xs, ∑ l ∈ ys, v μ l * (φ (μ, l) - φ (h * r μ, h * r l)) +
      ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), φ (h * a, h * b) *
        finInt (pairMeasure xs ys v) (fun p => fr a p.1 * fr b p.2) := by
    rw [jf_finInt_pair]
    have e2 : ∀ a b : ℕ, finInt (pairMeasure xs ys v) (fun p => fr a p.1 * fr b p.2) =
        ∑ μ ∈ xs, ∑ l ∈ ys, v μ l * (fr a μ * fr b l) := fun a b => jf_finInt_pair _ _ _ _
    simp_rw [e2]
    have : ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), φ (h * a, h * b) *
        ∑ μ ∈ xs, ∑ l ∈ ys, v μ l * (fr a μ * fr b l) =
        ∑ μ ∈ xs, ∑ l ∈ ys, v μ l * φ (h * r μ, h * r l) := by
      have hv : ∀ μ ∈ xs, ∀ l ∈ ys, v μ l * φ (h * r μ, h * r l) =
          ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
            φ (h * a, h * b) * (v μ l * (fr a μ * fr b l)) := by
        intro μ hμ l hl
        rw [hcell μ hμ l hl, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
      rw [Finset.sum_congr rfl fun μ hμ => Finset.sum_congr rfl fun l hl => hv μ hμ l hl]
      simp_rw [Finset.mul_sum]
      calc _ = ∑ a ∈ Finset.range (N + 1), ∑ μ ∈ xs, ∑ b ∈ Finset.range (N + 1), ∑ l ∈ ys,
              φ (h * a, h * b) * (v μ l * (fr a μ * fr b l)) :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ μ ∈ xs, ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ l ∈ ys,
              φ (h * a, h * b) * (v μ l * (fr a μ * fr b l)) := Finset.sum_comm
        _ = ∑ μ ∈ xs, ∑ a ∈ Finset.range (N + 1), ∑ l ∈ ys, ∑ b ∈ Finset.range (N + 1),
              φ (h * a, h * b) * (v μ l * (fr a μ * fr b l)) :=
            Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun μ _ => Finset.sum_comm
    rw [this, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    ring
  rw [step1]
  refine (abs_add_le _ _).trans ?_
  rw [add_comm]
  refine add_le_add ?_ ?_
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ a ∈ Finset.range (N + 1), |∑ b ∈ Finset.range (N + 1), φ (h * a, h * b) *
        finInt (pairMeasure xs ys v) (fun p => fr a p.1 * fr b p.2)| ≤ ((N + 1 : ℕ) : ℝ) * δ := by
      intro a ha
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ b ∈ Finset.range (N + 1), |φ (h * a, h * b) *
          finInt (pairMeasure xs ys v) (fun p => fr a p.1 * fr b p.2)| ≤ δ := by
        intro b hb
        rw [abs_mul]
        have h1 := hφ.1 (h * a, h * b) ⟨hc_mem a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)),
          hc_mem b (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))⟩
        have h2 := hprod (fr a) (fr b) (hfr a) (hfr b)
        have h3 : 0 ≤ δ := (abs_nonneg _).trans h2
        calc _ ≤ 1 * δ := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = δ := one_mul δ
      refine (Finset.sum_le_sum this).trans ?_
      simp
    refine (Finset.sum_le_sum this).trans ?_
    simp
    nlinarith
  · have : |∑ μ ∈ xs, ∑ l ∈ ys, v μ l * (φ (μ, l) - φ (h * r μ, h * r l))| ≤
        ∑ μ ∈ xs, ∑ l ∈ ys, |v μ l| * (2 * h) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun μ hμ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hpt μ hμ l hl) (abs_nonneg _)
    refine this.trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

private lemma jf_BL_total (Cs ε M : ℝ) (hCs : 0 ≤ Cs) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∀ (xs ys : Finset ℝ), (∀ x ∈ xs, x ∈ Set.Icc (0 : ℝ) Cs) →
      (∀ y ∈ ys, y ∈ Set.Icc (0 : ℝ) Cs) → ∀ v : ℝ → ℝ → ℝ,
      ∑ μ ∈ xs, ∑ l ∈ ys, |v μ l| ≤ 2 * M →
      (∀ f g : ℝ → ℝ, (∀ x, |f x| ≤ 1) → (∀ x, |g x| ≤ 1) →
        |finInt (pairMeasure xs ys v) (fun p => f p.1 * g p.2)| ≤ δ) →
      ∀ φ ∈ Muon.Dynamics.blTest Cs, |finInt (pairMeasure xs ys v) φ| ≤ ε := by
  have hh : 0 < ε / (8 * (M + 1)) := by positivity
  set h := ε / (8 * (M + 1)) with hhdef
  set N : ℕ := ⌊Cs / h⌋₊ with hN
  have hNpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) ^ 2 := by positivity
  refine ⟨ε / (2 * ((N + 1 : ℕ) : ℝ) ^ 2), by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast Nat.succ_pos N)
    nlinarith
  intro xs ys hx hy v hTV hprod φ hφ
  have := jf_BL Cs h hCs hh xs ys hx hy v _ hprod φ hφ
  refine this.trans ?_
  have e1 : ((⌊Cs / h⌋₊ + 1 : ℕ) : ℝ) ^ 2 * (ε / (2 * ((N + 1 : ℕ) : ℝ) ^ 2)) = ε / 2 := by
    rw [← hN]; field_simp
  have e2 : 2 * h * ∑ μ ∈ xs, ∑ l ∈ ys, |v μ l| ≤ ε / 2 := by
    calc 2 * h * ∑ μ ∈ xs, ∑ l ∈ ys, |v μ l| ≤ 2 * h * (2 * M) :=
          mul_le_mul_of_nonneg_left hTV (by positivity)
      _ = ε * M / (2 * (M + 1)) := by rw [hhdef]; field_simp; ring
      _ ≤ ε / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  linarith

end JFHelpers

section JFApp

private lemma jf_alg1 {m n : ℕ} (Bi c : ℝ) (A : Fin m → Fin n → ℝ) (x1 x2 : Fin m → ℝ)
    (y : Fin n → ℝ) :
    Bi * ∑ a, ∑ b, (c * x1 a + x2 a) * y b * A a b =
      c * (Bi * ∑ a, ∑ b, x1 a * y b * A a b) + Bi * ∑ a, ∑ b, x2 a * y b * A a b := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma jf_alg2 {m n : ℕ} (Bi c : ℝ) (A : Fin m → Fin n → ℝ) (x : Fin m → ℝ)
    (y1 y2 : Fin n → ℝ) :
    Bi * ∑ a, ∑ b, x a * (c * y1 b + y2 b) * A a b =
      c * (Bi * ∑ a, ∑ b, x a * y1 b * A a b) + Bi * ∑ a, ∑ b, x a * y2 b * A a b := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}

private lemma jf_lag_pair [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (SP : SpectralData F.C) {ϱ ϱ' : ℝ} (hϱ : 0 ≤ ϱ) (hϱ' : 0 ≤ ϱ')
    (ℓ : ℕ) (t : ℤ) (f g : ℝ → ℝ) :
    ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP,
        f μ * g l * def_app_vol_lag F S ℓ t (projOut SP μ) (projIn SP l) ϱ ϱ' =
      def_app_vol_lag F S ℓ t (SP.uOut * Matrix.diagonal (fun i => f (SP.μ i)) * SP.uOutᵀ)
        (SP.vIn * Matrix.diagonal (fun j => g (SP.lam j)) * SP.vInᵀ) ϱ ϱ' := by
  classical
  refine jf_bil (fun dx ey => def_app_vol_lag F S ℓ t (SP.uOut * Matrix.diagonal dx * SP.uOutᵀ)
    (SP.vIn * Matrix.diagonal ey * SP.vInᵀ) ϱ ϱ') ?_ ?_ (muVals SP) (lamVals SP) SP.μ SP.lam
    (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    (fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩) f g
  · intro c F1 F2 G
    simp only [ma_lag_atom F S SP hϱ hϱ' ℓ t]
    exact jf_alg1 _ _ _ _ _ _
  · intro c F0 G1 G2
    simp only [ma_lag_atom F S SP hϱ hϱ' ℓ t]
    exact jf_alg2 _ _ _ _ _ _


private lemma jf_resp_pair (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    (F : FrozenParams m n B) (SP : SpectralData F.C) (hS : SizeFin F.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (ℓ : ℕ) {ϱ ϱ' : ℝ} (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') (f g : ℝ → ℝ) :
    ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP, f μ * g l *
        lagResp cert γstar CSig F.β ℓ B SP.μ SP.lam (classDiag SP.μ μ) (classDiag SP.lam l)
          (omegaF ϱ) (omegaF ϱ') =
      lagResp cert γstar CSig F.β ℓ B SP.μ SP.lam (fun i => f (SP.μ i)) (fun j => g (SP.lam j))
        (omegaF ϱ) (omegaF ϱ') := by
  classical
  obtain ⟨-, hl1, hl2, -⟩ := thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig F SP
    hS hCSig ℓ (omegaF ϱ) (omegaF ϱ') (lem_app_vol_sharp_ii hϱ hϱ).2.1
    (lem_app_vol_sharp_ii hϱ' hϱ').2.1
  exact jf_bil (fun dx ey => lagResp cert γstar CSig F.β ℓ B SP.μ SP.lam dx ey
    (omegaF ϱ) (omegaF ϱ')) (fun c F1 F2 G => hl1 c F1 F2 G) (fun c F0 G1 G2 => hl2 c F0 G1 G2)
    (muVals SP) (lamVals SP) SP.μ SP.lam
    (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    (fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩) f g

private lemma jf_prod_cl [IsProbabilityMeasure P] (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (SP : SpectralData F.C) (hS : SizeFin F.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (ℓ : ℕ) (t : ℤ) {ϱ ϱ' : ℝ} (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') (f g : ℝ → ℝ) :
    finInt (measureCl F S SP ℓ t ϱ ϱ' - measureClBar cert γstar CSig F SP ℓ ϱ ϱ')
        (fun p => f p.1 * g p.2) =
      def_app_vol_lag F S ℓ t (SP.uOut * Matrix.diagonal (fun i => f (SP.μ i)) * SP.uOutᵀ)
        (SP.vIn * Matrix.diagonal (fun j => g (SP.lam j)) * SP.vInᵀ) ϱ ϱ' -
      lagResp cert γstar CSig F.β ℓ B SP.μ SP.lam (fun i => f (SP.μ i)) (fun j => g (SP.lam j))
        (omegaF ϱ) (omegaF ϱ') := by
  classical
  rw [← jf_lag_pair F S SP hϱ.le hϱ'.le ℓ t f g, ← jf_resp_pair cert γstar CSig F SP hS hCSig ℓ hϱ hϱ' f g]
  unfold measureCl measureClBar
  rw [ma_pair_sub, jf_finInt_pair, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring



private lemma jf_int_pair [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (γstar CSig : ℝ) (hS : SizeFin F.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (SP : SpectralData F.C) (ϱ : ℝ) (hϱ : 0 < ϱ) (t : ℤ) (f g : ℝ → ℝ) :
    ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP,
        f μ * g l * integratedLag F S t (projOut SP μ) (projIn SP l) ϱ ϱ =
      integratedLag F S t (SP.uOut * Matrix.diagonal (fun i => f (SP.μ i)) * SP.uOutᵀ)
        (SP.vIn * Matrix.diagonal (fun j => g (SP.lam j)) * SP.vInᵀ) ϱ ϱ := by
  classical
  refine jf_bil (fun dx ey => integratedLag F S t (SP.uOut * Matrix.diagonal dx * SP.uOutᵀ)
    (SP.vIn * Matrix.diagonal ey * SP.vInᵀ) ϱ ϱ) ?_ ?_ (muVals SP) (lamVals SP) SP.μ SP.lam
    (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    (fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩) f g
  · intro c F1 F2 G
    beta_reduce
    rw [ma_int_lin F S γstar CSig hS hCSig SP ϱ hϱ t (fun i => c * F1 i + F2 i) G,
      ma_int_lin F S γstar CSig hS hCSig SP ϱ hϱ t F1 G,
      ma_int_lin F S γstar CSig hS hCSig SP ϱ hϱ t F2 G]
    have := jf_alg1 1 c (fun a b => integratedLag F S t
        (SP.uOut * Matrix.diagonal (Pi.single a (1 : ℝ) : Fin m → ℝ) * SP.uOutᵀ)
        (SP.vIn * Matrix.diagonal (Pi.single b (1 : ℝ) : Fin n → ℝ) * SP.vInᵀ) ϱ ϱ) F1 F2 G
    simpa only [one_mul] using this
  · intro c F0 G1 G2
    beta_reduce
    rw [ma_int_lin F S γstar CSig hS hCSig SP ϱ hϱ t F0 (fun j => c * G1 j + G2 j),
      ma_int_lin F S γstar CSig hS hCSig SP ϱ hϱ t F0 G1,
      ma_int_lin F S γstar CSig hS hCSig SP ϱ hϱ t F0 G2]
    have := jf_alg2 1 c (fun a b => integratedLag F S t
        (SP.uOut * Matrix.diagonal (Pi.single a (1 : ℝ) : Fin m → ℝ) * SP.uOutᵀ)
        (SP.vIn * Matrix.diagonal (Pi.single b (1 : ℝ) : Fin n → ℝ) * SP.vInᵀ) ϱ ϱ) F0 G1 G2
    simpa only [one_mul] using this

private lemma jf_tsum_lin (c : ℝ) (x y : ℕ → ℝ) (hx : Summable fun q => x q + x q)
    (hy : Summable fun q => y q + y q) :
    ∑' q, ((c * x q + y q) + (c * x q + y q)) = c * ∑' q, (x q + x q) + ∑' q, (y q + y q) := by
  have : ∀ q, ((c * x q + y q) + (c * x q + y q)) = c * (x q + x q) + (y q + y q) := fun q => by ring
  simp_rw [this]
  rw [Summable.tsum_add (hx.mul_left c) hy, tsum_mul_left]

private lemma jf_gamma_pair (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    (F : FrozenParams m n B) (SP : SpectralData F.C) (hS : SizeFin F.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (ϱlo ϱhi : ℝ) (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) (ϱ : ℝ)
    (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) (f g : ℝ → ℝ) :
    ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP, f μ * g l *
        lagGammaBar cert γstar CSig F.β B SP.μ SP.lam (classDiag SP.μ μ) (classDiag SP.lam l) ϱ ϱ =
      lagGammaBar cert γstar CSig F.β B SP.μ SP.lam (fun i => f (SP.μ i)) (fun j => g (SP.lam j))
        ϱ ϱ := by
  classical
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le hϱ.1 hϱI.1
  have hsum : ∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ), Summable (fun q : ℕ =>
      lagResp cert γstar CSig F.β (q + 1) B SP.μ SP.lam Fd Gd (omegaF ϱ) (omegaF ϱ) +
      lagResp cert γstar CSig F.β (q + 1) B SP.μ SP.lam Fd Gd (omegaF ϱ) (omegaF ϱ)) := fun Fd Gd =>
    summable_abs_iff.mp (thm_app_vol_integrated_iii cert γstar CSig F SP hS hCSig
      (SP.uOut * Matrix.diagonal Fd * SP.uOutᵀ) (SP.vIn * Matrix.diagonal Gd * SP.vInᵀ) Fd Gd
      rfl rfl ϱlo ϱhi hϱ ϱ ϱ hϱI hϱI).1
  have hlin : ∀ q : ℕ, (∀ (c : ℝ) (Fd₁ Fd₂ : Fin m → ℝ) (Gd : Fin n → ℝ),
      lagResp cert γstar CSig F.β q B SP.μ SP.lam (fun i => c * Fd₁ i + Fd₂ i) Gd (omegaF ϱ) (omegaF ϱ) =
        c * lagResp cert γstar CSig F.β q B SP.μ SP.lam Fd₁ Gd (omegaF ϱ) (omegaF ϱ) +
          lagResp cert γstar CSig F.β q B SP.μ SP.lam Fd₂ Gd (omegaF ϱ) (omegaF ϱ)) ∧
      (∀ (c : ℝ) (Fd : Fin m → ℝ) (Gd₁ Gd₂ : Fin n → ℝ),
      lagResp cert γstar CSig F.β q B SP.μ SP.lam Fd (fun j => c * Gd₁ j + Gd₂ j) (omegaF ϱ) (omegaF ϱ) =
        c * lagResp cert γstar CSig F.β q B SP.μ SP.lam Fd Gd₁ (omegaF ϱ) (omegaF ϱ) +
          lagResp cert γstar CSig F.β q B SP.μ SP.lam Fd Gd₂ (omegaF ϱ) (omegaF ϱ)) := fun q => by
    obtain ⟨-, hl1, hl2, -⟩ := thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig F SP
      hS hCSig q (omegaF ϱ) (omegaF ϱ) (lem_app_vol_sharp_ii hϱ0 hϱ0).2.1
      (lem_app_vol_sharp_ii hϱ0 hϱ0).2.1
    exact ⟨hl1, hl2⟩
  refine jf_bil (fun Fd Gd => lagGammaBar cert γstar CSig F.β B SP.μ SP.lam Fd Gd ϱ ϱ) ?_ ?_
    (muVals SP) (lamVals SP) SP.μ SP.lam
    (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    (fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩) f g
  · intro c F1 F2 G
    have ht : ∀ q, lagResp cert γstar CSig F.β q B SP.μ SP.lam (fun i => c * F1 i + F2 i) G
        (omegaF ϱ) (omegaF ϱ) = c * lagResp cert γstar CSig F.β q B SP.μ SP.lam F1 G
        (omegaF ϱ) (omegaF ϱ) + lagResp cert γstar CSig F.β q B SP.μ SP.lam F2 G
        (omegaF ϱ) (omegaF ϱ) := fun q => (hlin q).1 c F1 F2 G
    simp only [lagGammaBar, ht]
    rw [jf_tsum_lin c _ _ (hsum F1 G) (hsum F2 G)]
    ring
  · intro c F0 G1 G2
    have ht : ∀ q, lagResp cert γstar CSig F.β q B SP.μ SP.lam F0 (fun j => c * G1 j + G2 j)
        (omegaF ϱ) (omegaF ϱ) = c * lagResp cert γstar CSig F.β q B SP.μ SP.lam F0 G1
        (omegaF ϱ) (omegaF ϱ) + lagResp cert γstar CSig F.β q B SP.μ SP.lam F0 G2
        (omegaF ϱ) (omegaF ϱ) := fun q => (hlin q).2 c F0 G1 G2
    simp only [lagGammaBar, ht]
    rw [jf_tsum_lin c _ _ (hsum F0 G1) (hsum F0 G2)]
    ring

private lemma jf_prod_int [IsProbabilityMeasure P] (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (SP : SpectralData F.C) (hS : SizeFin F.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (ϱlo ϱhi : ℝ) (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) (ϱ : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) (t : ℤ)
    (f g : ℝ → ℝ) :
    finInt (measureInt F S SP t ϱ - measureZeta cert γstar CSig F SP ϱ) (fun p => f p.1 * g p.2) =
      integratedLag F S t (SP.uOut * Matrix.diagonal (fun i => f (SP.μ i)) * SP.uOutᵀ)
        (SP.vIn * Matrix.diagonal (fun j => g (SP.lam j)) * SP.vInᵀ) ϱ ϱ -
      lagGammaBar cert γstar CSig F.β B SP.μ SP.lam (fun i => f (SP.μ i)) (fun j => g (SP.lam j))
        ϱ ϱ := by
  classical
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le hϱ.1 hϱI.1
  rw [← jf_int_pair F S γstar CSig hS hCSig SP ϱ hϱ0 t f g,
    ← jf_gamma_pair cert γstar CSig F SP hS hCSig ϱlo ϱhi hϱ ϱ hϱI f g]
  unfold measureInt measureZeta
  rw [ma_pair_sub, jf_finInt_pair, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

private lemma jf_swap (xs ys : Finset ℝ) (g : ℕ → ℝ → ℝ → ℝ)
    (hs : ∀ μ ∈ xs, ∀ l ∈ ys, Summable (fun q => g q μ l)) :
    ∑ μ ∈ xs, ∑ l ∈ ys, ∑' q, g q μ l = ∑' q, ∑ μ ∈ xs, ∑ l ∈ ys, g q μ l := by
  rw [Summable.tsum_finsetSum fun μ hμ => summable_sum fun l hl => hs μ hμ l hl]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [Summable.tsum_finsetSum fun l hl => hs μ hμ l hl]

end JFApp

/-! ## Joint forcing measure (`thm:app-vol-joint-forcing`) -/

/-- `thm:app-vol-joint-forcing`, part (i), deterministic: the total variation of `C̄_0` is at most
`γ⋆`, and that of `C̄_ℓ` (`ℓ ≥ 1`) at most `K⋆ β^ℓ`, at every finite dimension and `ϱ, ϱ' ∈ I`;
the atoms of `C̄_ℓ` and of `ζ_ϱ` with `μ = 0` or `λ = 0` vanish. Snapshot `cr-2026-10-23`.
LaTeX, verbatim from `section.tex` (the whole environment):

\begin{theorem}[Joint forcing measure]\label{thm:app-vol-joint-forcing}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item At every finite dimension, $\norm{\overline{\mathfrak C}_0}_{\mathrm{TV}}\le\gamma_\star$ and
$\norm{\overline{\mathfrak C}_\ell}_{\mathrm{TV}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same holds
for $\mathfrak C_\ell$ under \cref{assum:app-setup-regime}. The atoms of
$\overline{\mathfrak C}_\ell$ and of $\zeta_\ridge$ with $\mu=0$ or $\lambda=0$ vanish.
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\[
\sup_{\ridge,\ridge'\in I}\ \sup_{\norm f_\infty,\norm g_\infty\le1}\Big|\int f\tensor g\,d\big(\mathfrak C_\ell-\overline{\mathfrak C}_\ell\big)\Big|\to0,\qquad
\sup_{\ridge,\ridge'\in I}\norm{\mathfrak C_\ell-\overline{\mathfrak C}_\ell}_\BL\to0 .
\]
\item The forcing measure $\zeta_\ridge$ is a nonnegative measure, unchanged under
replication, of total mass at most $\gamma_\star+2\mathsf K_\star\bmom/(1-\bmom)$, and under
\cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-forcing}
\sup_{\ridge\in I}\norm{\mathfrak C_{\mathrm{int}}(\ridge)-\zeta_\ridge}_\BL\to0,
\end{equation}
together with the product-test form of (ii).
\item The finite-time measure
\[
\mathfrak F_T(\ridge)\defeq\frac1{BT}\sum_{i,j}\EE\Big(\sum_{t'=1}^T({\mathsf S}^{\mathrm c}_{t'}(\ridge))_{ij}\Big)^2\,\delta_{(\mu_i,\lambda_j)}
\]
is nonnegative, and $\norm{\mathfrak F_T(\ridge)-\mathfrak C_{\mathrm{int}}(\ridge)}_{\mathrm{TV}}$ is at most
\cref{eqn:app-vol-finite-time-error}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_joint_forcing_i_bar (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (ϱlo ϱhi : ℝ) (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) :
    (∀ ϱ ∈ Set.Icc ϱlo ϱhi, ∀ ϱ' ∈ Set.Icc ϱlo ϱhi,
      finTV (measureClBar cert γstar CSig Fp S 0 ϱ ϱ') ≤ γstar) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ∀ ϱ ∈ Set.Icc ϱlo ϱhi, ∀ ϱ' ∈ Set.Icc ϱlo ϱhi,
      finTV (measureClBar cert γstar CSig Fp S ℓ ϱ ϱ') ≤
        Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β ^ ℓ) ∧
    (∀ ℓ : ℕ, ∀ μ l : ℝ, (μ = 0 ∨ l = 0) → ∀ ϱ ∈ Set.Icc ϱlo ϱhi, ∀ ϱ' ∈ Set.Icc ϱlo ϱhi,
      measureClBar cert γstar CSig Fp S ℓ ϱ ϱ' (μ, l) = 0) ∧
    (∀ μ l : ℝ, (μ = 0 ∨ l = 0) → ∀ ϱ ∈ Set.Icc ϱlo ϱhi,
      measureZeta cert γstar CSig Fp S ϱ (μ, l) = 0) := by
  have hpos : ∀ ϱ ∈ Set.Icc ϱlo ϱhi, 0 ≤ ϱ := fun ϱ h => hϱ.1.le.trans h.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ϱ hϱI ϱ' hϱ'I
    rw [measureClBar, mm_finTV_pairMeasure]
    refine mt_tv_atoms cert γstar CSig Fp S hS hCSig ϱlo ϱhi hϱ 0 γstar ?_ ϱ hϱI ϱ' hϱ'I
    intro m' n' B' F' Sp' hS' _ ϱ₁ h₁ ϱ₂ h₂
    have e : (0 : ℤ) + ((0 : ℕ) : ℤ) = 0 := by norm_num
    rw [e]
    exact mt_indep_tv_zero F' γstar CSig hS' Sp' (hpos _ h₁) (hpos _ h₂) 0
  · intro ℓ _ ϱ hϱI ϱ' hϱ'I
    rw [measureClBar, mm_finTV_pairMeasure]
    refine mt_tv_atoms cert γstar CSig Fp S hS hCSig ϱlo ϱhi hϱ ℓ _ ?_ ϱ hϱI ϱ' hϱ'I
    intro m' n' B' F' Sp' hS' hβ ϱ₁ h₁ ϱ₂ h₂
    rw [← hβ]
    exact mt_indep_tv_pos F' γstar CSig ϱlo hS' Sp' hϱ.1 h₁.1 h₂.1 0 ℓ
  · intro ℓ μ l h ϱ _ ϱ' _
    rw [measureClBar, mm_pairMeasure_apply]
    split_ifs
    · rcases h with h | h
      · subst h
        exact mt_lagResp_zero_F cert γstar CSig Fp.β ℓ B S.μ S.lam _ _
          (fun i => mt_classDiag_zero S.μ i) _ _
      · subst h
        exact mt_lagResp_zero_G cert γstar CSig Fp.β ℓ B S.μ S.lam _ _
          (fun j => mt_classDiag_zero S.lam j) _ _
    · rfl
  · intro μ l h ϱ _
    rw [measureZeta, mm_pairMeasure_apply]
    split_ifs
    · have hz : ∀ (ℓ : ℕ) (f g : ℝ → ℝ),
          lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (classDiag S.μ μ) (classDiag S.lam l) f g
            = 0 := by
        intro ℓ f g
        rcases h with h | h
        · subst h
          exact mt_lagResp_zero_F cert γstar CSig Fp.β ℓ B S.μ S.lam _ _
            (fun i => mt_classDiag_zero S.μ i) _ _
        · subst h
          exact mt_lagResp_zero_G cert γstar CSig Fp.β ℓ B S.μ S.lam _ _
            (fun j => mt_classDiag_zero S.lam j) _ _
      unfold lagGammaBar
      simp [hz]
    · rfl

section JFApp2
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}

private lemma jf_tv_M [IsProbabilityMeasure P] (cert : Muon.External.GaussianOpNorm)
    (γstar CSig ϱlo ϱhi : ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (SP : SpectralData F.C) (hS : SizeFin F.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) (ϱ ϱ' : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi)
    (hϱ'I : ϱ' ∈ Set.Icc ϱlo ϱhi) (t : ℤ) (ℓ : ℕ) :
    (∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP,
      |def_app_vol_lag F S ℓ t (projOut SP μ) (projIn SP l) ϱ ϱ'| ≤
        |γstar| + |Muon.Dynamics.kStar CSig γstar ϱlo|) ∧
    (∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP,
      |lagResp cert γstar CSig F.β ℓ B SP.μ SP.lam (classDiag SP.μ μ) (classDiag SP.lam l)
        (omegaF ϱ) (omegaF ϱ')| ≤ |γstar| + |Muon.Dynamics.kStar CSig γstar ϱlo|) := by
  have hact := ma_tv_actual F S γstar CSig ϱlo ϱhi hS hϱ SP ϱ ϱ' hϱI hϱ'I t ℓ
  have hbar := thm_app_vol_joint_forcing_i_bar cert γstar CSig F SP hS hCSig ϱlo ϱhi hϱ
  have hb : ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP,
      |lagResp cert γstar CSig F.β ℓ B SP.μ SP.lam (classDiag SP.μ μ) (classDiag SP.lam l)
        (omegaF ϱ) (omegaF ϱ')| = finTV (measureClBar cert γstar CSig F SP ℓ ϱ ϱ') := by
    rw [measureClBar, mm_finTV_pairMeasure]
  have hβ1 : F.β ^ ℓ ≤ 1 := pow_le_one₀ F.hβ.1 F.hβ.2.le
  have hK : Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ ℓ ≤ |Muon.Dynamics.kStar CSig γstar ϱlo| := by
    calc _ ≤ |Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ ℓ| := le_abs_self _
      _ = |Muon.Dynamics.kStar CSig γstar ϱlo| * F.β ^ ℓ := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg F.hβ.1 _)]
      _ ≤ |Muon.Dynamics.kStar CSig γstar ϱlo| * 1 :=
          mul_le_mul_of_nonneg_left hβ1 (abs_nonneg _)
      _ = _ := mul_one _
  have h1 := le_abs_self γstar
  have h2 := abs_nonneg γstar
  have h3 := abs_nonneg (Muon.Dynamics.kStar CSig γstar ϱlo)
  rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
  · subst h0
    refine ⟨?_, ?_⟩
    · linarith [hact.1 rfl]
    · rw [hb]; linarith [hbar.1 ϱ hϱI ϱ' hϱ'I]
  · refine ⟨?_, ?_⟩
    · linarith [hact.2 hpos]
    · rw [hb]; linarith [hbar.2.1 ℓ hpos ϱ hϱI ϱ' hϱ'I]


private lemma jf_int_tv [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (γstar CSig ϱlo ϱhi : ℝ) (hS : SizeFin F.C B γstar CSig)
    (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) (SP : SpectralData F.C) (ϱ : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi)
    (t : ℤ) :
    ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP,
        |integratedLag F S t (projOut SP μ) (projIn SP l) ϱ ϱ| ≤
      |γstar| + 2 * (|Muon.Dynamics.kStar CSig γstar ϱlo| * F.β / (1 - F.β)) := by
  classical
  set K := Muon.Dynamics.kStar CSig γstar ϱlo with hK
  let a : ℕ → ℝ → ℝ → ℝ := fun q μ l =>
    def_app_vol_lag F S q t (projOut SP μ) (projIn SP l) ϱ ϱ
  have hact := fun q => ma_tv_actual F S γstar CSig ϱlo ϱhi hS hϱ SP ϱ ϱ hϱI hϱI t q
  have hatom : ∀ μ ∈ muVals SP, ∀ l ∈ lamVals SP, ∀ q : ℕ, |a (q + 1) μ l| ≤ K * F.β ^ (q + 1) := by
    intro μ hμ l hl q
    have h := (hact (q + 1)).2 (Nat.succ_le_succ (Nat.zero_le q))
    refine le_trans ?_ h
    refine le_trans ?_ (Finset.single_le_sum (f := fun μ' => ∑ l' ∈ lamVals SP,
      |def_app_vol_lag F S (q + 1) t (projOut SP μ') (projIn SP l') ϱ ϱ|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hμ)
    exact Finset.single_le_sum (f := fun l' =>
      |def_app_vol_lag F S (q + 1) t (projOut SP μ) (projIn SP l') ϱ ϱ|)
      (fun _ _ => abs_nonneg _) hl
  have hgeo : Summable (fun q : ℕ => 2 * (K * F.β ^ (q + 1))) := by
    have := (summable_geometric_of_lt_one F.hβ.1 F.hβ.2).mul_left (2 * (K * F.β))
    convert this using 1
    funext q
    rw [pow_succ]
    ring
  have hs : ∀ μ ∈ muVals SP, ∀ l ∈ lamVals SP,
      Summable (fun q : ℕ => |a (q + 1) μ l + a (q + 1) μ l|) := by
    intro μ hμ l hl
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun q => ?_) hgeo
    have := hatom μ hμ l hl q
    rw [← two_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hpoint : ∀ μ ∈ muVals SP, ∀ l ∈ lamVals SP,
      |integratedLag F S t (projOut SP μ) (projIn SP l) ϱ ϱ| ≤
        |a 0 μ l| + ∑' q : ℕ, |a (q + 1) μ l + a (q + 1) μ l| := by
    intro μ hμ l hl
    unfold integratedLag
    exact mm_abs_add_tsum_le (a 0 μ l) (fun q => a (q + 1) μ l + a (q + 1) μ l) (hs μ hμ l hl)
  refine (Finset.sum_le_sum fun μ hμ => Finset.sum_le_sum fun l hl => hpoint μ hμ l hl).trans ?_
  simp_rw [Finset.sum_add_distrib]
  rw [jf_swap _ _ (fun q μ l => |a (q + 1) μ l + a (q + 1) μ l|) hs]
  have hlag : ∀ q : ℕ, (∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP, |a (q + 1) μ l + a (q + 1) μ l|) ≤
      2 * (K * F.β ^ (q + 1)) := by
    intro q
    have h := (hact (q + 1)).2 (Nat.succ_le_succ (Nat.zero_le q))
    calc _ = 2 * ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP, |a (q + 1) μ l| := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun μ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← two_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ _ := by
          have : (∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP, |a (q + 1) μ l|) ≤ K * F.β ^ (q + 1) := h
          linarith
  have hsum2 : Summable (fun q : ℕ =>
      ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP, |a (q + 1) μ l + a (q + 1) μ l|) :=
    Summable.of_nonneg_of_le (fun q => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg
      fun _ _ => abs_nonneg _) hlag hgeo
  have htail : (∑' q : ℕ, ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP, |a (q + 1) μ l + a (q + 1) μ l|) ≤
      2 * (K * F.β / (1 - F.β)) := by
    calc _ ≤ ∑' q : ℕ, 2 * (K * F.β ^ (q + 1)) := Summable.tsum_le_tsum hlag hsum2 hgeo
      _ = _ := by
        rw [show (fun q : ℕ => 2 * (K * F.β ^ (q + 1))) = fun q => (2 * (K * F.β)) * F.β ^ q by
          funext q; rw [pow_succ]; ring]
        rw [tsum_mul_left, tsum_geometric_of_lt_one F.hβ.1 F.hβ.2]
        ring
  have h0 : (∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP, |a 0 μ l|) ≤ |γstar| :=
    ((hact 0).1 rfl).trans (le_abs_self _)
  have hKabs : K * F.β / (1 - F.β) ≤ |K| * F.β / (1 - F.β) := by
    have hpos : 0 < 1 - F.β := sub_pos.mpr F.hβ.2
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) F.hβ.1) hpos.le
  linarith

end JFApp2

/-- `thm:app-vol-joint-forcing`, part (i), actual: the same total-variation bounds hold for the
actual measures `𝔠_ℓ` (`measureCl`) under `assum:app-setup-regime`, read at every index `k`
and every time `t`. Snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex` (the whole
environment):

\begin{theorem}[Joint forcing measure]\label{thm:app-vol-joint-forcing}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item At every finite dimension, $\norm{\overline{\mathfrak C}_0}_{\mathrm{TV}}\le\gamma_\star$ and
$\norm{\overline{\mathfrak C}_\ell}_{\mathrm{TV}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same holds
for $\mathfrak C_\ell$ under \cref{assum:app-setup-regime}. The atoms of
$\overline{\mathfrak C}_\ell$ and of $\zeta_\ridge$ with $\mu=0$ or $\lambda=0$ vanish.
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\[
\sup_{\ridge,\ridge'\in I}\ \sup_{\norm f_\infty,\norm g_\infty\le1}\Big|\int f\tensor g\,d\big(\mathfrak C_\ell-\overline{\mathfrak C}_\ell\big)\Big|\to0,\qquad
\sup_{\ridge,\ridge'\in I}\norm{\mathfrak C_\ell-\overline{\mathfrak C}_\ell}_\BL\to0 .
\]
\item The forcing measure $\zeta_\ridge$ is a nonnegative measure, unchanged under
replication, of total mass at most $\gamma_\star+2\mathsf K_\star\bmom/(1-\bmom)$, and under
\cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-forcing}
\sup_{\ridge\in I}\norm{\mathfrak C_{\mathrm{int}}(\ridge)-\zeta_\ridge}_\BL\to0,
\end{equation}
together with the product-test form of (ii).
\item The finite-time measure
\[
\mathfrak F_T(\ridge)\defeq\frac1{BT}\sum_{i,j}\EE\Big(\sum_{t'=1}^T({\mathsf S}^{\mathrm c}_{t'}(\ridge))_{ij}\Big)^2\,\delta_{(\mu_i,\lambda_j)}
\]
is nonnegative, and $\norm{\mathfrak F_T(\ridge)-\mathfrak C_{\mathrm{int}}(\ridge)}_{\mathrm{TV}}$ is at most
\cref{eqn:app-vol-finite-time-error}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_joint_forcing_i_actual (cert : Muon.External.GaussianOpNorm)
    (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (Sp : ∀ k : ℕ, SpectralData (R.F k).C) :
    ∀ k : ℕ, ∀ t : ℤ, ∀ ℓ : ℕ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi, ∀ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi,
      (ℓ = 0 → finTV (measureCl (R.F k) (S k) (Sp k) ℓ t ϱ ϱ') ≤ R.γstar) ∧
      (1 ≤ ℓ → finTV (measureCl (R.F k) (S k) (Sp k) ℓ t ϱ ϱ') ≤
        Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo * (R.F k).β ^ ℓ) := by
  intro k t ℓ ϱ hϱI ϱ' hϱ'I
  have hS : SizeFin (R.F k).C (R.B k) R.γstar R.CSig := ⟨R.dims k, R.normOut k, R.normIn k⟩
  have h := ma_tv_actual (R.F k) (S k) R.γstar R.CSig R.ϱlo R.ϱhi hS R.hϱ (Sp k) ϱ ϱ' hϱI hϱ'I t ℓ
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · rw [measureCl, mm_finTV_pairMeasure]
    subst h0
    exact h.1 rfl
  · rw [measureCl, mm_finTV_pairMeasure]
    exact h.2 h1

/-- `thm:app-vol-joint-forcing`, part (ii): under `assum:app-setup-regime`, for every fixed lag
`ℓ`, the tested measures `𝔠_ℓ` and `C̄_ℓ` agree uniformly over `ϱ, ϱ' ∈ I`, all times `t`, and all
test functions bounded by one, in the product-test form and in the bounded-Lipschitz norm.
Snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex` (the whole environment):

\begin{theorem}[Joint forcing measure]\label{thm:app-vol-joint-forcing}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item At every finite dimension, $\norm{\overline{\mathfrak C}_0}_{\mathrm{TV}}\le\gamma_\star$ and
$\norm{\overline{\mathfrak C}_\ell}_{\mathrm{TV}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same holds
for $\mathfrak C_\ell$ under \cref{assum:app-setup-regime}. The atoms of
$\overline{\mathfrak C}_\ell$ and of $\zeta_\ridge$ with $\mu=0$ or $\lambda=0$ vanish.
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\[
\sup_{\ridge,\ridge'\in I}\ \sup_{\norm f_\infty,\norm g_\infty\le1}\Big|\int f\tensor g\,d\big(\mathfrak C_\ell-\overline{\mathfrak C}_\ell\big)\Big|\to0,\qquad
\sup_{\ridge,\ridge'\in I}\norm{\mathfrak C_\ell-\overline{\mathfrak C}_\ell}_\BL\to0 .
\]
\item The forcing measure $\zeta_\ridge$ is a nonnegative measure, unchanged under
replication, of total mass at most $\gamma_\star+2\mathsf K_\star\bmom/(1-\bmom)$, and under
\cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-forcing}
\sup_{\ridge\in I}\norm{\mathfrak C_{\mathrm{int}}(\ridge)-\zeta_\ridge}_\BL\to0,
\end{equation}
together with the product-test form of (ii).
\item The finite-time measure
\[
\mathfrak F_T(\ridge)\defeq\frac1{BT}\sum_{i,j}\EE\Big(\sum_{t'=1}^T({\mathsf S}^{\mathrm c}_{t'}(\ridge))_{ij}\Big)^2\,\delta_{(\mu_i,\lambda_j)}
\]
is nonnegative, and $\norm{\mathfrak F_T(\ridge)-\mathfrak C_{\mathrm{int}}(\ridge)}_{\mathrm{TV}}$ is at most
\cref{eqn:app-vol-finite-time-error}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_joint_forcing_ii (cert : Muon.External.GaussianOpNorm)
    (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (Sp : ∀ k : ℕ, SpectralData (R.F k).C) :
    ∀ ℓ : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi,
      ∀ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi,
      (∀ f g : ℝ → ℝ, (∀ x, |f x| ≤ 1) → (∀ x, |g x| ≤ 1) →
        |finInt (measureCl (R.F k) (S k) (Sp k) ℓ t ϱ ϱ' -
            measureClBar cert R.γstar R.CSig (R.F k) (Sp k) ℓ ϱ ϱ')
          (fun p => f p.1 * g p.2)| ≤ ε) ∧
      (∀ φ ∈ Muon.Dynamics.blTest R.CSig,
        |finInt (measureCl (R.F k) (S k) (Sp k) ℓ t ϱ ϱ' -
            measureClBar cert R.γstar R.CSig (R.F k) (Sp k) ℓ ϱ ϱ') φ| ≤ ε) := by
  intro ℓ ε hε
  have hCs : 0 ≤ R.CSig := by linarith [R.hC]
  have hM : 0 ≤ |R.γstar| + |Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  obtain ⟨δ, hδ, hδε, hBL⟩ := jf_BL_total R.CSig ε _ hCs hM hε
  have h := (thm_app_vol_lag_kernel_closure_actual cert R Ω P S Sp ℓ (Set.Icc R.ϱlo R.ϱhi)
    isCompact_Icc (fun x hx => lt_of_lt_of_le R.hϱ.1 hx.1)).2 δ hδ
  filter_upwards [h] with k hk t ϱ hϱI ϱ' hϱ'I
  have hS : SizeFin (R.F k).C (R.B k) R.γstar R.CSig := ⟨R.dims k, R.normOut k, R.normIn k⟩
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le R.hϱ.1 hϱI.1
  have hϱ0' : 0 < ϱ' := lt_of_lt_of_le R.hϱ.1 hϱ'I.1
  have hprod : ∀ f g : ℝ → ℝ, (∀ x, |f x| ≤ 1) → (∀ x, |g x| ≤ 1) →
      |finInt (measureCl (R.F k) (S k) (Sp k) ℓ t ϱ ϱ' -
          measureClBar cert R.γstar R.CSig (R.F k) (Sp k) ℓ ϱ ϱ')
        (fun p => f p.1 * g p.2)| ≤ δ := by
    intro f g hf hg
    rw [jf_prod_cl cert R.γstar R.CSig (R.F k) (S k) (Sp k) hS R.hC ℓ t hϱ0 hϱ0' f g]
    exact hk t ϱ hϱI ϱ' hϱ'I _ _ _ _ rfl rfl
      (md_opNorm_conj _ (Sp k).huOut _ (fun i => hf _))
      (md_opNorm_conj _ (Sp k).hvIn _ (fun j => hg _))
  refine ⟨fun f g hf hg => (hprod f g hf hg).trans hδε, ?_⟩
  intro φ hφ
  obtain ⟨hmu, hlam⟩ := jf_spec_mem (Sp k) R.CSig (R.normOut k) (R.normIn k)
  have hxs : ∀ x ∈ muVals (Sp k), x ∈ Set.Icc (0 : ℝ) R.CSig := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hmu i
  have hys : ∀ y ∈ lamVals (Sp k), y ∈ Set.Icc (0 : ℝ) R.CSig := by
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    exact hlam j
  have hmeas : measureCl (R.F k) (S k) (Sp k) ℓ t ϱ ϱ' -
      measureClBar cert R.γstar R.CSig (R.F k) (Sp k) ℓ ϱ ϱ' =
      pairMeasure (muVals (Sp k)) (lamVals (Sp k)) (fun μ l =>
        def_app_vol_lag (R.F k) (S k) ℓ t (projOut (Sp k) μ) (projIn (Sp k) l) ϱ ϱ' -
        lagResp cert R.γstar R.CSig (R.F k).β ℓ (R.B k) (Sp k).μ (Sp k).lam
          (classDiag (Sp k).μ μ) (classDiag (Sp k).lam l) (omegaF ϱ) (omegaF ϱ')) := by
    unfold measureCl measureClBar
    exact ma_pair_sub _ _ _ _
  rw [hmeas] at hprod ⊢
  obtain ⟨hT1, hT2⟩ := jf_tv_M cert R.γstar R.CSig R.ϱlo R.ϱhi (R.F k) (S k) (Sp k) hS R.hC
    R.hϱ ϱ ϱ' hϱI hϱ'I t ℓ
  refine hBL _ _ hxs hys _ ?_ hprod φ hφ
  calc _ ≤ ∑ μ ∈ muVals (Sp k), ∑ l ∈ lamVals (Sp k),
        (|def_app_vol_lag (R.F k) (S k) ℓ t (projOut (Sp k) μ) (projIn (Sp k) l) ϱ ϱ'| +
        |lagResp cert R.γstar R.CSig (R.F k).β ℓ (R.B k) (Sp k).μ (Sp k).lam
          (classDiag (Sp k).μ μ) (classDiag (Sp k).lam l) (omegaF ϱ) (omegaF ϱ')|) :=
        Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun l _ => abs_sub _ _
    _ ≤ _ := by
        simp only [Finset.sum_add_distrib]
        linarith

/-- `thm:app-vol-joint-forcing`, part (iii), nonnegativity and total mass at every finite
dimension: the forcing measure `ζ_ϱ` (`measureZeta`) has nonnegative atoms for `ϱ ∈ I`, and total
mass at most `γ⋆ + 2 K⋆ β/(1-β)`. Snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex`
(the whole environment):

\begin{theorem}[Joint forcing measure]\label{thm:app-vol-joint-forcing}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item At every finite dimension, $\norm{\overline{\mathfrak C}_0}_{\mathrm{TV}}\le\gamma_\star$ and
$\norm{\overline{\mathfrak C}_\ell}_{\mathrm{TV}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same holds
for $\mathfrak C_\ell$ under \cref{assum:app-setup-regime}. The atoms of
$\overline{\mathfrak C}_\ell$ and of $\zeta_\ridge$ with $\mu=0$ or $\lambda=0$ vanish.
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\[
\sup_{\ridge,\ridge'\in I}\ \sup_{\norm f_\infty,\norm g_\infty\le1}\Big|\int f\tensor g\,d\big(\mathfrak C_\ell-\overline{\mathfrak C}_\ell\big)\Big|\to0,\qquad
\sup_{\ridge,\ridge'\in I}\norm{\mathfrak C_\ell-\overline{\mathfrak C}_\ell}_\BL\to0 .
\]
\item The forcing measure $\zeta_\ridge$ is a nonnegative measure, unchanged under
replication, of total mass at most $\gamma_\star+2\mathsf K_\star\bmom/(1-\bmom)$, and under
\cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-forcing}
\sup_{\ridge\in I}\norm{\mathfrak C_{\mathrm{int}}(\ridge)-\zeta_\ridge}_\BL\to0,
\end{equation}
together with the product-test form of (ii).
\item The finite-time measure
\[
\mathfrak F_T(\ridge)\defeq\frac1{BT}\sum_{i,j}\EE\Big(\sum_{t'=1}^T({\mathsf S}^{\mathrm c}_{t'}(\ridge))_{ij}\Big)^2\,\delta_{(\mu_i,\lambda_j)}
\]
is nonnegative, and $\norm{\mathfrak F_T(\ridge)-\mathfrak C_{\mathrm{int}}(\ridge)}_{\mathrm{TV}}$ is at most
\cref{eqn:app-vol-finite-time-error}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_joint_forcing_iii_nonneg (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (ϱlo ϱhi : ℝ) (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) :
    (∀ ϱ ∈ Set.Icc ϱlo ϱhi, ∀ μ l : ℝ, 0 ≤ measureZeta cert γstar CSig Fp S ϱ (μ, l)) ∧
    (∀ ϱ ∈ Set.Icc ϱlo ϱhi,
      finTV (measureZeta cert γstar CSig Fp S ϱ) ≤
        γstar + 2 * Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β / (1 - Fp.β)) := by
  classical
  have hbar := thm_app_vol_joint_forcing_i_bar cert γstar CSig Fp S hS hCSig ϱlo ϱhi hϱ
  refine ⟨fun ϱ hϱI μ l => mm_measureZeta_nonneg cert γstar CSig Fp S hS hCSig ϱ
    (hϱ.1.trans_le hϱI.1) μ l, ?_⟩
  intro ϱ hϱI
  have hϱpos : 0 < ϱ := hϱ.1.trans_le hϱI.1
  let a : ℕ → ℝ → ℝ → ℝ := fun q μ l =>
    lagResp cert γstar CSig Fp.β q B S.μ S.lam (classDiag S.μ μ) (classDiag S.lam l)
      (omegaF ϱ) (omegaF ϱ)
  have hs : ∀ μ l, Summable (fun q : ℕ => |a (q + 1) μ l + a (q + 1) μ l|) := by
    intro μ l
    exact (thm_app_vol_integrated_iii cert γstar CSig Fp S hS hCSig
      (S.uOut * Matrix.diagonal (classDiag S.μ μ) * S.uOutᵀ)
      (S.vIn * Matrix.diagonal (classDiag S.lam l) * S.vInᵀ)
      (classDiag S.μ μ) (classDiag S.lam l) rfl rfl ϱlo ϱhi hϱ ϱ ϱ hϱI hϱI).1
  have hpoint : ∀ μ l,
      |lagGammaBar cert γstar CSig Fp.β B S.μ S.lam
          (classDiag S.μ μ) (classDiag S.lam l) ϱ ϱ| ≤
        |a 0 μ l| + ∑' q : ℕ, |a (q + 1) μ l + a (q + 1) μ l| := by
    intro μ l
    unfold lagGammaBar
    change |a 0 μ l + ∑' q : ℕ, (a (q + 1) μ l + a (q + 1) μ l)| ≤ _
    exact mm_abs_add_tsum_le (a 0 μ l) (fun q => a (q + 1) μ l + a (q + 1) μ l) (hs μ l)
  rw [measureZeta, mm_finTV_pairMeasure]
  refine (Finset.sum_le_sum fun μ hμ => Finset.sum_le_sum fun l hl => hpoint μ l).trans ?_
  simp_rw [Finset.sum_add_distrib]
  have hswap :
      (∑ μ ∈ muVals S, ∑ l ∈ lamVals S,
          ∑' q : ℕ, |a (q + 1) μ l + a (q + 1) μ l|) =
        ∑' q : ℕ, ∑ μ ∈ muVals S, ∑ l ∈ lamVals S,
          |a (q + 1) μ l + a (q + 1) μ l| := by
    have hsμ : ∀ μ, Summable (fun q : ℕ => ∑ l ∈ lamVals S,
        |a (q + 1) μ l + a (q + 1) μ l|) := by
      intro μ
      induction lamVals S using Finset.induction_on with
      | empty => simpa
      | @insert l s hl ih =>
          simp only [Finset.sum_insert hl]
          exact (hs μ l).add ih
    calc
      _ = ∑ μ ∈ muVals S, ∑' q : ℕ, ∑ l ∈ lamVals S,
            |a (q + 1) μ l + a (q + 1) μ l| := by
          refine Finset.sum_congr rfl fun μ _ => ?_
          exact (Summable.tsum_finsetSum (fun l _ => hs μ l)).symm
      _ = _ := (Summable.tsum_finsetSum (fun μ _ => hsμ μ)).symm
  rw [hswap]
  have hzero : (∑ μ ∈ muVals S, ∑ l ∈ lamVals S, |a 0 μ l|) =
      finTV (measureClBar cert γstar CSig Fp S 0 ϱ ϱ) := by
    rw [measureClBar, mm_finTV_pairMeasure]
  rw [hzero]
  have hlag : ∀ q : ℕ,
      (∑ μ ∈ muVals S, ∑ l ∈ lamVals S,
          |a (q + 1) μ l + a (q + 1) μ l|) =
        2 * finTV (measureClBar cert γstar CSig Fp S (q + 1) ϱ ϱ) := by
    intro q
    rw [measureClBar, mm_finTV_pairMeasure]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← two_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  simp_rw [hlag]
  rw [tsum_mul_left]
  have hK : 0 ≤ Muon.Dynamics.kStar CSig γstar ϱlo := by
    unfold Muon.Dynamics.kStar
    exact mul_nonneg (le_trans zero_le_one hCSig) (Real.sqrt_nonneg _)
  have htail : (∑' q : ℕ, finTV (measureClBar cert γstar CSig Fp S (q + 1) ϱ ϱ)) ≤
      Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β / (1 - Fp.β) := by
    have hsumfin : Summable (fun q : ℕ =>
        finTV (measureClBar cert γstar CSig Fp S (q + 1) ϱ ϱ)) := by
      apply Summable.of_nonneg_of_le (fun q => mm_finTV_nonneg _)
        (fun q => hbar.2.1 (q + 1) (Nat.succ_le_succ (Nat.zero_le q)) ϱ hϱI ϱ hϱI)
      have hg := (summable_geometric_of_lt_one Fp.hβ.1 Fp.hβ.2).mul_left
        (Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β)
      convert hg using 1
      funext q
      rw [pow_succ]
      ring
    calc
      _ ≤ ∑' q : ℕ, Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β ^ (q + 1) :=
        Summable.tsum_le_tsum
          (fun q => hbar.2.1 (q + 1) (Nat.succ_le_succ (Nat.zero_le q)) ϱ hϱI ϱ hϱI)
          hsumfin (by
            have hg := (summable_geometric_of_lt_one Fp.hβ.1 Fp.hβ.2).mul_left
              (Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β)
            convert hg using 1
            funext q
            rw [pow_succ]
            ring)
      _ = _ := by
        rw [show (fun q : ℕ => Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β ^ (q + 1)) =
          fun q => (Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β) * Fp.β ^ q by
            funext q; rw [pow_succ]; ring]
        rw [tsum_mul_left, tsum_geometric_of_lt_one Fp.hβ.1 Fp.hβ.2]
        ring
  have h0 := hbar.1 ϱ hϱI ϱ hϱI
  calc
    _ ≤ γstar + 2 * (Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β / (1 - Fp.β)) :=
      add_le_add h0 (mul_le_mul_of_nonneg_left htail (by norm_num))
    _ = _ := by ring

/-- `thm:app-vol-joint-forcing`, part (iii), replication invariance: for every `N ≥ 1` with the
replicated state of unit Frobenius norm (`hA`, `def_app_vol_replication`), the forcing measure of
the replicated model equals that of the base model, for any replicated spectral data `SP'` with
the replicated eigenvalues (`replVec`). Snapshot `cr-2026-10-23`. LaTeX, verbatim from
`section.tex` (the whole environment):

\begin{theorem}[Joint forcing measure]\label{thm:app-vol-joint-forcing}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item At every finite dimension, $\norm{\overline{\mathfrak C}_0}_{\mathrm{TV}}\le\gamma_\star$ and
$\norm{\overline{\mathfrak C}_\ell}_{\mathrm{TV}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same holds
for $\mathfrak C_\ell$ under \cref{assum:app-setup-regime}. The atoms of
$\overline{\mathfrak C}_\ell$ and of $\zeta_\ridge$ with $\mu=0$ or $\lambda=0$ vanish.
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\[
\sup_{\ridge,\ridge'\in I}\ \sup_{\norm f_\infty,\norm g_\infty\le1}\Big|\int f\tensor g\,d\big(\mathfrak C_\ell-\overline{\mathfrak C}_\ell\big)\Big|\to0,\qquad
\sup_{\ridge,\ridge'\in I}\norm{\mathfrak C_\ell-\overline{\mathfrak C}_\ell}_\BL\to0 .
\]
\item The forcing measure $\zeta_\ridge$ is a nonnegative measure, unchanged under
replication, of total mass at most $\gamma_\star+2\mathsf K_\star\bmom/(1-\bmom)$, and under
\cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-forcing}
\sup_{\ridge\in I}\norm{\mathfrak C_{\mathrm{int}}(\ridge)-\zeta_\ridge}_\BL\to0,
\end{equation}
together with the product-test form of (ii).
\item The finite-time measure
\[
\mathfrak F_T(\ridge)\defeq\frac1{BT}\sum_{i,j}\EE\Big(\sum_{t'=1}^T({\mathsf S}^{\mathrm c}_{t'}(\ridge))_{ij}\Big)^2\,\delta_{(\mu_i,\lambda_j)}
\]
is nonnegative, and $\norm{\mathfrak F_T(\ridge)-\mathfrak C_{\mathrm{int}}(\ridge)}_{\mathrm{TV}}$ is at most
\cref{eqn:app-vol-finite-time-error}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_joint_forcing_iii_replication (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (N : ℕ) (hN : 0 < N) (hA : Muon.fro (replState Fp.C S N) = 1)
    (SP' : SpectralData (replCov Fp.C N))
    (hμ : SP'.μ = replVec N S.μ) (hlam : SP'.lam = replVec N S.lam)
    (ϱ : ℝ) (hϱ : 0 < ϱ) :
    measureZeta cert γstar CSig (def_app_vol_replication Fp S N hN hA) SP' ϱ =
      measureZeta cert γstar CSig Fp S ϱ := by
  classical
  dsimp only [def_app_vol_replication]
  unfold measureZeta muVals lamVals
  rw [hμ, hlam, mm_vals_repl S.μ N hN, mm_vals_repl S.lam N hN]
  apply congrArg (pairMeasure (muVals S) (lamVals S))
  funext μ l
  rw [mm_classDiag_repl, mm_classDiag_repl]
  exact mm_lagGammaBar_repl cert γstar CSig Fp.β B N hN S.μ S.lam
    (classDiag S.μ μ) (classDiag S.lam l) ϱ ϱ

/-- `thm:app-vol-joint-forcing`, part (iii), absolute convergence of the integrated measure: under
`assum:app-setup-regime`, for every index `k`, `ϱ, ϱ' ∈ I` and atom `(μ_i, λ_j)`, the lag series
of `measureInt` (`integratedLag` at the projections `projOut`, `projIn`, any time `t`) converge
absolutely. Snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex` (the whole environment):

\begin{theorem}[Joint forcing measure]\label{thm:app-vol-joint-forcing}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item At every finite dimension, $\norm{\overline{\mathfrak C}_0}_{\mathrm{TV}}\le\gamma_\star$ and
$\norm{\overline{\mathfrak C}_\ell}_{\mathrm{TV}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same holds
for $\mathfrak C_\ell$ under \cref{assum:app-setup-regime}. The atoms of
$\overline{\mathfrak C}_\ell$ and of $\zeta_\ridge$ with $\mu=0$ or $\lambda=0$ vanish.
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\[
\sup_{\ridge,\ridge'\in I}\ \sup_{\norm f_\infty,\norm g_\infty\le1}\Big|\int f\tensor g\,d\big(\mathfrak C_\ell-\overline{\mathfrak C}_\ell\big)\Big|\to0,\qquad
\sup_{\ridge,\ridge'\in I}\norm{\mathfrak C_\ell-\overline{\mathfrak C}_\ell}_\BL\to0 .
\]
\item The forcing measure $\zeta_\ridge$ is a nonnegative measure, unchanged under
replication, of total mass at most $\gamma_\star+2\mathsf K_\star\bmom/(1-\bmom)$, and under
\cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-forcing}
\sup_{\ridge\in I}\norm{\mathfrak C_{\mathrm{int}}(\ridge)-\zeta_\ridge}_\BL\to0,
\end{equation}
together with the product-test form of (ii).
\item The finite-time measure
\[
\mathfrak F_T(\ridge)\defeq\frac1{BT}\sum_{i,j}\EE\Big(\sum_{t'=1}^T({\mathsf S}^{\mathrm c}_{t'}(\ridge))_{ij}\Big)^2\,\delta_{(\mu_i,\lambda_j)}
\]
is nonnegative, and $\norm{\mathfrak F_T(\ridge)-\mathfrak C_{\mathrm{int}}(\ridge)}_{\mathrm{TV}}$ is at most
\cref{eqn:app-vol-finite-time-error}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_joint_forcing_iii_summable (cert : Muon.External.GaussianOpNorm)
    (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (Sp : ∀ k : ℕ, SpectralData (R.F k).C) :
    ∀ k : ℕ, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi, ∀ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi,
      ∀ μ ∈ Set.range (Sp k).μ, ∀ l ∈ Set.range (Sp k).lam,
        Summable (fun ℓ : ℕ => |def_app_vol_lag (R.F k) (S k) (ℓ + 1) t (projOut (Sp k) μ)
            (projIn (Sp k) l) ϱ ϱ' + def_app_vol_lag (R.F k) (S k) (ℓ + 1) t (projOut (Sp k) μ)
            (projIn (Sp k) l) ϱ' ϱ|) := by
  classical
  intro k t ϱ hϱI ϱ' hϱ'I μ hμ l hl
  have hS : SizeFin (R.F k).C (R.B k) R.γstar R.CSig := ⟨R.dims k, R.normOut k, R.normIn k⟩
  have hμ' : μ ∈ muVals (Sp k) := by
    obtain ⟨i, rfl⟩ := hμ
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hl' : l ∈ lamVals (Sp k) := by
    obtain ⟨j, rfl⟩ := hl
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hatom : ∀ (a b : ℝ), a ∈ Set.Icc R.ϱlo R.ϱhi → b ∈ Set.Icc R.ϱlo R.ϱhi → ∀ q : ℕ,
      |def_app_vol_lag (R.F k) (S k) (q + 1) t (projOut (Sp k) μ) (projIn (Sp k) l) a b| ≤
        Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo * (R.F k).β ^ (q + 1) := by
    intro a b ha hb q
    have h := (ma_tv_actual (R.F k) (S k) R.γstar R.CSig R.ϱlo R.ϱhi hS R.hϱ (Sp k) a b ha hb t
      (q + 1)).2 (Nat.succ_le_succ (Nat.zero_le q))
    refine le_trans ?_ h
    refine le_trans ?_ (Finset.single_le_sum (f := fun μ' => ∑ l' ∈ lamVals (Sp k),
      |def_app_vol_lag (R.F k) (S k) (q + 1) t (projOut (Sp k) μ') (projIn (Sp k) l') a b|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hμ')
    exact Finset.single_le_sum (f := fun l' =>
      |def_app_vol_lag (R.F k) (S k) (q + 1) t (projOut (Sp k) μ) (projIn (Sp k) l') a b|)
      (fun _ _ => abs_nonneg _) hl'
  have hg : Summable (fun q : ℕ => 2 * (Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo *
      (R.F k).β ^ (q + 1))) := by
    have := (summable_geometric_of_lt_one (R.F k).hβ.1 (R.F k).hβ.2).mul_left
      (2 * (Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo * (R.F k).β))
    convert this using 1
    funext q
    rw [pow_succ]
    ring
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun q => ?_) hg
  have h1 := hatom ϱ ϱ' hϱI hϱ'I q
  have h2 := hatom ϱ' ϱ hϱ'I hϱI q
  refine (abs_add_le _ _).trans ?_
  linarith

/-- `thm:app-vol-joint-forcing`, part (iii), limit: under `assum:app-setup-regime`,
`C_int(ϱ) - ζ_ϱ → 0` in the bounded-Lipschitz norm and in the product-test form, uniformly over
`ϱ ∈ I` and at every time `t` (`measureInt`). Snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex`
(the whole environment):

\begin{theorem}[Joint forcing measure]\label{thm:app-vol-joint-forcing}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item At every finite dimension, $\norm{\overline{\mathfrak C}_0}_{\mathrm{TV}}\le\gamma_\star$ and
$\norm{\overline{\mathfrak C}_\ell}_{\mathrm{TV}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same holds
for $\mathfrak C_\ell$ under \cref{assum:app-setup-regime}. The atoms of
$\overline{\mathfrak C}_\ell$ and of $\zeta_\ridge$ with $\mu=0$ or $\lambda=0$ vanish.
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\[
\sup_{\ridge,\ridge'\in I}\ \sup_{\norm f_\infty,\norm g_\infty\le1}\Big|\int f\tensor g\,d\big(\mathfrak C_\ell-\overline{\mathfrak C}_\ell\big)\Big|\to0,\qquad
\sup_{\ridge,\ridge'\in I}\norm{\mathfrak C_\ell-\overline{\mathfrak C}_\ell}_\BL\to0 .
\]
\item The forcing measure $\zeta_\ridge$ is a nonnegative measure, unchanged under
replication, of total mass at most $\gamma_\star+2\mathsf K_\star\bmom/(1-\bmom)$, and under
\cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-forcing}
\sup_{\ridge\in I}\norm{\mathfrak C_{\mathrm{int}}(\ridge)-\zeta_\ridge}_\BL\to0,
\end{equation}
together with the product-test form of (ii).
\item The finite-time measure
\[
\mathfrak F_T(\ridge)\defeq\frac1{BT}\sum_{i,j}\EE\Big(\sum_{t'=1}^T({\mathsf S}^{\mathrm c}_{t'}(\ridge))_{ij}\Big)^2\,\delta_{(\mu_i,\lambda_j)}
\]
is nonnegative, and $\norm{\mathfrak F_T(\ridge)-\mathfrak C_{\mathrm{int}}(\ridge)}_{\mathrm{TV}}$ is at most
\cref{eqn:app-vol-finite-time-error}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_joint_forcing_iii_limit (cert : Muon.External.GaussianOpNorm)
    (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (Sp : ∀ k : ℕ, SpectralData (R.F k).C) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi,
      (∀ φ ∈ Muon.Dynamics.blTest R.CSig,
        |finInt (measureInt (R.F k) (S k) (Sp k) t ϱ -
            measureZeta cert R.γstar R.CSig (R.F k) (Sp k) ϱ) φ| ≤ ε) ∧
      (∀ f g : ℝ → ℝ, (∀ x, |f x| ≤ 1) → (∀ x, |g x| ≤ 1) →
        |finInt (measureInt (R.F k) (S k) (Sp k) t ϱ -
            measureZeta cert R.γstar R.CSig (R.F k) (Sp k) ϱ)
          (fun p => f p.1 * g p.2)| ≤ ε) := by
  intro ε hε
  have hCs : 0 ≤ R.CSig := by linarith [R.hC]
  set K := Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo with hK
  set M := |R.γstar| + |K| * (R.β) / (1 - R.β) with hMdef
  have hβ : 0 ≤ R.β ∧ R.β < 1 := by
    have := (R.F 0).hβ
    rw [R.hβ 0] at this
    exact this
  have hM : 0 ≤ |R.γstar| + 2 * (|K| * R.β / (1 - R.β)) := by
    have : 0 ≤ |K| * R.β / (1 - R.β) :=
      div_nonneg (mul_nonneg (abs_nonneg _) hβ.1) (sub_pos.mpr hβ.2).le
    have := abs_nonneg R.γstar
    linarith
  obtain ⟨δ, hδ, hδε, hBL⟩ := jf_BL_total R.CSig ε
    (|R.γstar| + 2 * (|K| * R.β / (1 - R.β))) hCs hM hε
  have h := (thm_app_vol_integrated_iv cert R Ω P S Sp).1 δ hδ
  filter_upwards [h] with k hk t ϱ hϱI
  have hS : SizeFin (R.F k).C (R.B k) R.γstar R.CSig := ⟨R.dims k, R.normOut k, R.normIn k⟩
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le R.hϱ.1 hϱI.1
  have hprod : ∀ f g : ℝ → ℝ, (∀ x, |f x| ≤ 1) → (∀ x, |g x| ≤ 1) →
      |finInt (measureInt (R.F k) (S k) (Sp k) t ϱ -
          measureZeta cert R.γstar R.CSig (R.F k) (Sp k) ϱ) (fun p => f p.1 * g p.2)| ≤ δ := by
    intro f g hf hg
    rw [jf_prod_int cert R.γstar R.CSig (R.F k) (S k) (Sp k) hS R.hC R.ϱlo R.ϱhi R.hϱ ϱ hϱI t f g]
    exact hk t ϱ hϱI ϱ hϱI _ _ _ _ rfl rfl
      (md_opNorm_conj _ (Sp k).huOut _ (fun i => hf _))
      (md_opNorm_conj _ (Sp k).hvIn _ (fun j => hg _))
  refine ⟨?_, fun f g hf hg => (hprod f g hf hg).trans hδε⟩
  intro φ hφ
  obtain ⟨hmu, hlam⟩ := jf_spec_mem (Sp k) R.CSig (R.normOut k) (R.normIn k)
  have hxs : ∀ x ∈ muVals (Sp k), x ∈ Set.Icc (0 : ℝ) R.CSig := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hmu i
  have hys : ∀ y ∈ lamVals (Sp k), y ∈ Set.Icc (0 : ℝ) R.CSig := by
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    exact hlam j
  have hmeas : measureInt (R.F k) (S k) (Sp k) t ϱ -
      measureZeta cert R.γstar R.CSig (R.F k) (Sp k) ϱ =
      pairMeasure (muVals (Sp k)) (lamVals (Sp k)) (fun μ l =>
        integratedLag (R.F k) (S k) t (projOut (Sp k) μ) (projIn (Sp k) l) ϱ ϱ -
        lagGammaBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam
          (classDiag (Sp k).μ μ) (classDiag (Sp k).lam l) ϱ ϱ) := by
    unfold measureInt measureZeta
    exact ma_pair_sub _ _ _ _
  rw [hmeas] at hprod ⊢
  have hT1 := jf_int_tv (R.F k) (S k) R.γstar R.CSig R.ϱlo R.ϱhi hS R.hϱ (Sp k) ϱ hϱI t
  have hT2 := (thm_app_vol_joint_forcing_iii_nonneg cert R.γstar R.CSig (R.F k) (Sp k) hS R.hC
    R.ϱlo R.ϱhi R.hϱ).2 ϱ hϱI
  rw [measureZeta, mm_finTV_pairMeasure] at hT2
  rw [R.hβ k] at hT1 hT2
  rw [← hK] at hT1 hT2
  have hKle : 2 * K * R.β / (1 - R.β) ≤ 2 * (|K| * R.β / (1 - R.β)) := by
    have hpos : 0 < 1 - R.β := sub_pos.mpr hβ.2
    have : K * R.β / (1 - R.β) ≤ |K| * R.β / (1 - R.β) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) hβ.1) hpos.le
    have e : 2 * K * R.β / (1 - R.β) = 2 * (K * R.β / (1 - R.β)) := by ring
    rw [e]; linarith
  have h1 := le_abs_self R.γstar
  refine hBL _ _ hxs hys _ ?_ hprod φ hφ
  calc _ ≤ ∑ μ ∈ muVals (Sp k), ∑ l ∈ lamVals (Sp k),
        (|integratedLag (R.F k) (S k) t (projOut (Sp k) μ) (projIn (Sp k) l) ϱ ϱ| +
        |lagGammaBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam
          (classDiag (Sp k).μ μ) (classDiag (Sp k).lam l) ϱ ϱ|) :=
        Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun l _ => abs_sub _ _
    _ ≤ _ := by
        simp only [Finset.sum_add_distrib, R.hβ k]
        linarith

/-- `thm:app-vol-joint-forcing`, part (iv): the finite-time measure `𝔉_T(ϱ)` (`finiteTimeMeasure`)
is nonnegative, and its total variation distance to `𝔠_int(ϱ)` (`measureInt` at any time `t`) is at
most `2 K⋆ (β^T/(1-β) + β/(T(1-β)²))` (`eqn:app-vol-finite-time-error`), for every `T ≥ 1` and
`ϱ ∈ I`. The entries are integrable (conjunct). Snapshot `cr-2026-10-23`. LaTeX, verbatim from
`section.tex` (the whole environment):

\begin{theorem}[Joint forcing measure]\label{thm:app-vol-joint-forcing}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item At every finite dimension, $\norm{\overline{\mathfrak C}_0}_{\mathrm{TV}}\le\gamma_\star$ and
$\norm{\overline{\mathfrak C}_\ell}_{\mathrm{TV}}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$, and the same holds
for $\mathfrak C_\ell$ under \cref{assum:app-setup-regime}. The atoms of
$\overline{\mathfrak C}_\ell$ and of $\zeta_\ridge$ with $\mu=0$ or $\lambda=0$ vanish.
\item Under \cref{assum:app-setup-regime}, for every fixed $\ell\ge0$,
\[
\sup_{\ridge,\ridge'\in I}\ \sup_{\norm f_\infty,\norm g_\infty\le1}\Big|\int f\tensor g\,d\big(\mathfrak C_\ell-\overline{\mathfrak C}_\ell\big)\Big|\to0,\qquad
\sup_{\ridge,\ridge'\in I}\norm{\mathfrak C_\ell-\overline{\mathfrak C}_\ell}_\BL\to0 .
\]
\item The forcing measure $\zeta_\ridge$ is a nonnegative measure, unchanged under
replication, of total mass at most $\gamma_\star+2\mathsf K_\star\bmom/(1-\bmom)$, and under
\cref{assum:app-setup-regime}
\begin{equation}\label{eqn:app-vol-forcing}
\sup_{\ridge\in I}\norm{\mathfrak C_{\mathrm{int}}(\ridge)-\zeta_\ridge}_\BL\to0,
\end{equation}
together with the product-test form of (ii).
\item The finite-time measure
\[
\mathfrak F_T(\ridge)\defeq\frac1{BT}\sum_{i,j}\EE\Big(\sum_{t'=1}^T({\mathsf S}^{\mathrm c}_{t'}(\ridge))_{ij}\Big)^2\,\delta_{(\mu_i,\lambda_j)}
\]
is nonnegative, and $\norm{\mathfrak F_T(\ridge)-\mathfrak C_{\mathrm{int}}(\ridge)}_{\mathrm{TV}}$ is at most
\cref{eqn:app-vol-finite-time-error}.
\end{enumerate}
\end{theorem} -/
theorem thm_app_vol_joint_forcing_iv (cert : Muon.External.GaussianOpNorm) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (γstar CSig : ℝ) {m n B : ℕ} (Fp : FrozenParams m n B)
    (S : FrozenSamples P m n B) (SP : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (ϱlo ϱhi : ℝ) (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) :
    (∀ T : ℕ, ∀ ϱ ∈ Set.Icc ϱlo ϱhi, ∀ μ l : ℝ, 0 ≤ finiteTimeMeasure Fp S SP T ϱ (μ, l)) ∧
    (∀ t : ℤ, ∀ T : ℕ, 1 ≤ T → ∀ ϱ ∈ Set.Icc ϱlo ϱhi,
      (∀ i : Fin m, ∀ j : Fin n, Integrable (fun ω =>
        ((SP.uOutᵀ * (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), centredUpd Fp S ϱ s ω) * SP.vIn) i j) ^ 2) P) ∧
      finTV (finiteTimeMeasure Fp S SP T ϱ - measureInt Fp S SP t ϱ) ≤
        2 * Muon.Dynamics.kStar CSig γstar ϱlo *
          (Fp.β ^ T / (1 - Fp.β) + Fp.β / ((T : ℝ) * (1 - Fp.β) ^ 2))) := by
  classical
  have hBpos : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  refine ⟨?_, fun t T hT ϱ hϱI => ?_⟩
  · intro T ϱ hϱI μ l
    unfold finiteTimeMeasure
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_nonneg fun j _ => ?_
    rw [Finsupp.single_apply]
    split_ifs
    · exact mul_nonneg (inv_nonneg.mpr (mul_nonneg hBpos.le (Nat.cast_nonneg T)))
        (integral_nonneg fun ω => sq_nonneg _)
    · exact le_rfl
  · have hϱ0 : 0 ≤ ϱ := le_trans hϱ.1.le hϱI.1
    refine ⟨fun i j => ma_entry_sq_int Fp S SP hϱ0 T i j, ?_⟩
    have hsymm : ∀ (k : ℕ) (U : Mat k k) (x : Fin k → ℝ),
        (U * Matrix.diagonal x * Uᵀ)ᵀ = U * Matrix.diagonal x * Uᵀ := by
      intro k U x
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    have hFT : finiteTimeMeasure Fp S SP T ϱ = pairMeasure (muVals SP) (lamVals SP)
        (fun μ l => finiteTimeCov Fp S T ϱ ϱ (projOut SP μ) (projIn SP l)) := by
      unfold finiteTimeMeasure
      rw [ma_pair_regroup SP.μ SP.lam (fun a b => ((B : ℝ) * (T : ℝ))⁻¹ * ∫ ω,
        ((SP.uOutᵀ * (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), centredUpd Fp S ϱ s ω) * SP.vIn) a b) ^ 2 ∂P)]
      unfold muVals lamVals
      congr 1
      funext μ l
      rw [ma_ftc_atom Fp S SP hϱ0 T μ l]
    rw [hFT, measureInt, ma_pair_sub, mm_finTV_pairMeasure]
    have hCs : 0 ≤ CSig := by
      have := hS.2.1
      exact le_trans (ma_opNorm_nonneg _) this
    have hK : 0 ≤ Muon.Dynamics.kStar CSig γstar ϱlo := by
      unfold Muon.Dynamics.kStar
      exact mul_nonneg hCs (Real.sqrt_nonneg _)
    obtain ⟨hβ0, hβ1⟩ := Fp.hβ
    have hcore := ma_core_vec (muVals SP) (lamVals SP)
      (fun μ l ℓ => def_app_vol_lag Fp S ℓ t (projOut SP μ) (projIn SP l) ϱ ϱ +
        def_app_vol_lag Fp S ℓ t (projOut SP μ) (projIn SP l) ϱ ϱ)
      (2 * Muon.Dynamics.kStar CSig γstar ϱlo) Fp.β (by linarith) hβ0 hβ1 (fun ℓ hℓ => by
        have h := (ma_tv_actual Fp S γstar CSig ϱlo ϱhi hS hϱ SP ϱ ϱ hϱI hϱI t ℓ).2 hℓ
        calc ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP, |def_app_vol_lag Fp S ℓ t (projOut SP μ) (projIn SP l) ϱ ϱ +
              def_app_vol_lag Fp S ℓ t (projOut SP μ) (projIn SP l) ϱ ϱ|
            ≤ ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP, (|def_app_vol_lag Fp S ℓ t (projOut SP μ) (projIn SP l) ϱ ϱ| +
              |def_app_vol_lag Fp S ℓ t (projOut SP μ) (projIn SP l) ϱ ϱ|) :=
              Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun l _ => abs_add_le _ _
          _ = 2 * ∑ μ ∈ muVals SP, ∑ l ∈ lamVals SP,
              |def_app_vol_lag Fp S ℓ t (projOut SP μ) (projIn SP l) ϱ ϱ| := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun μ _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun l _ => ?_
              ring
          _ ≤ 2 * (Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β ^ ℓ) := by linarith
          _ = _ := by ring) T hT
    refine le_trans (le_of_eq ?_) hcore
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => ?_
    have hI := thm_app_vol_lag_reduction_i Fp S γstar CSig ϱlo ϱhi hS hCSig hϱ (projOut SP μ)
      (projIn SP l) (hsymm m SP.uOut _) (hsymm n SP.vIn _) (mt_proj_opNorm SP μ l).1
      (mt_proj_opNorm SP μ l).2 ϱ ϱ hϱI hϱI T hT t
    rw [hI]
    unfold integratedLag
    rw [← abs_neg]
    congr 1
    ring

/-! ## Mode disintegration (`prop:app-vol-disintegration`) and row recovery -/

/-- `prop:app-vol-disintegration`, part (i), deterministic: `𝔳_ij(ϱ) ≥ 0` (`modeVij`), it depends on
`(i,j)` only through `(μ_i,λ_j)`, vanishes when `μ_iλ_j = 0`, and
`ζ_ϱ = B⁻¹ ∑_{i,j} 𝔳_ij(ϱ) δ_{(μ_i,λ_j)}`. Snapshot `cr-2026-10-23`. LaTeX, verbatim from
`section.tex` (the whole environment):

\begin{proposition}[Mode coefficients]\label{prop:app-vol-disintegration}
For an eigenvalue $\mu$ of $\Sigmaout$ and $\lambda$ of $\Sigmain$ let
$r_\mu\defeq\#\{i:\mu_i=\mu\}$ and $t_\lambda\defeq\#\{j:\lambda_j=\lambda\}$, and put
\begin{equation}\label{eqn:app-vol-vij}
\mathfrak v_{ij}(\ridge)\defeq\frac{B\,\zeta_\ridge(\{(\mu_i,\lambda_j)\})}{r_{\mu_i}\,t_{\lambda_j}} .
\end{equation}
Then $\mathfrak v_{ij}(\ridge)\ge0$, it depends on $(i,j)$ only through
$(\mu_i,\lambda_j)$, it vanishes when $\mu_i\lambda_j=0$, and
$\zeta_\ridge=B^{-1}\sum_{i,j}\mathfrak v_{ij}(\ridge)\,\delta_{(\mu_i,\lambda_j)}$. The actual
entry coefficients
\begin{equation}\label{eqn:app-vol-vij-actual}
\mathsf v_{ij}(\ridge)\defeq\EE\big(({\mathsf S}^{\mathrm c}_t(\ridge))_{ij}\big)^2+2\sum_{\ell\ge1}\EE\big[({\mathsf S}^{\mathrm c}_t(\ridge))_{ij}({\mathsf S}^{\mathrm c}_{t+\ell}(\ridge))_{ij}\big]
\end{equation}
converge absolutely, are nonnegative, and satisfy
$\mathfrak C_{\mathrm{int}}(\ridge)=B^{-1}\sum_{i,j}\mathsf v_{ij}(\ridge)\,\delta_{(\mu_i,\lambda_j)}$; consequently,
under \cref{assum:app-setup-regime},
\[
\sup_{\ridge\in I}\Big\|\frac1B\sum_{i,j}\big(\mathsf v_{ij}(\ridge)-\mathfrak v_{ij}(\ridge)\big)\delta_{(\mu_i,\lambda_j)}\Big\|_\BL\longrightarrow0 .
\]
\end{proposition} -/
theorem prop_app_vol_disintegration_i (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (SP : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    (∀ i : Fin m, ∀ j : Fin n, 0 ≤ modeVij cert γstar CSig Fp SP ϱ i j) ∧
    (∀ i i' : Fin m, ∀ j j' : Fin n, SP.μ i = SP.μ i' → SP.lam j = SP.lam j' →
      modeVij cert γstar CSig Fp SP ϱ i j = modeVij cert γstar CSig Fp SP ϱ i' j') ∧
    (∀ i : Fin m, ∀ j : Fin n, SP.μ i * SP.lam j = 0 → modeVij cert γstar CSig Fp SP ϱ i j = 0) ∧
    (measureZeta cert γstar CSig Fp SP ϱ =
      ∑ i : Fin m, ∑ j : Fin n, Finsupp.single (SP.μ i, SP.lam j)
        ((B : ℝ)⁻¹ * modeVij cert γstar CSig Fp SP ϱ i j)) := by
  classical
  refine ⟨fun i j => mm_modeVij_nonneg cert γstar CSig Fp SP hS hCSig ϱ hϱ i j,
    fun i i' j j' hi hj => mm_modeVij_eq_of_eigs cert γstar CSig Fp SP ϱ i i' j j' hi hj,
    ?_, ?_⟩
  · intro i j hij
    have hz : SP.μ i = 0 ∨ SP.lam j = 0 := mul_eq_zero.mp hij
    have haxis := (thm_app_vol_joint_forcing_i_bar cert γstar CSig Fp SP hS hCSig
      ϱ ϱ ⟨hϱ, le_rfl⟩).2.2.2 (SP.μ i) (SP.lam j) hz ϱ ⟨le_rfl, le_rfl⟩
    unfold modeVij
    rw [haxis]
    simp
  · ext p
    rcases p with ⟨x, y⟩
    rw [measureZeta, mm_pairMeasure_apply]
    simp_rw [Finsupp.finsetSum_apply, Finsupp.single_apply]
    change (if x ∈ muVals SP ∧ y ∈ lamVals SP then
        lagGammaBar cert γstar CSig Fp.β B SP.μ SP.lam
          (classDiag SP.μ x) (classDiag SP.lam y) ϱ ϱ else 0) =
      ∑ i : Fin m, ∑ j : Fin n,
        if (SP.μ i, SP.lam j) = (x, y) then
          (B : ℝ)⁻¹ * modeVij cert γstar CSig Fp SP ϱ i j else 0
    by_cases hx : x ∈ muVals SP
    · obtain ⟨i₀, -, hi₀⟩ := Finset.mem_image.mp hx
      subst x
      by_cases hy : y ∈ lamVals SP
      · obtain ⟨j₀, -, hj₀⟩ := Finset.mem_image.mp hy
        subst y
        simp only [hx, hy, and_self, if_true]
        have hB : (B : ℝ) ≠ 0 := by exact_mod_cast Fp.hB.ne'
        let r : ℝ := ((Finset.univ.filter fun i => SP.μ i = SP.μ i₀).card : ℝ)
        let t : ℝ := ((Finset.univ.filter fun j => SP.lam j = SP.lam j₀).card : ℝ)
        have hr : r ≠ 0 := ne_of_gt (mm_class_card_pos SP.μ i₀)
        have ht : t ≠ 0 := ne_of_gt (mm_class_card_pos SP.lam j₀)
        have hterm : ∀ i : Fin m,
            (∑ j : Fin n, if (SP.μ i, SP.lam j) = (SP.μ i₀, SP.lam j₀) then
                (B : ℝ)⁻¹ * modeVij cert γstar CSig Fp SP ϱ i j else 0) =
              if SP.μ i = SP.μ i₀ then
                ((Finset.univ.filter fun j => SP.lam j = SP.lam j₀).card : ℝ) *
                  ((B : ℝ)⁻¹ * modeVij cert γstar CSig Fp SP ϱ i₀ j₀) else 0 := by
          intro i
          by_cases hi : SP.μ i = SP.μ i₀
          · rw [if_pos hi]
            calc
              _ = ∑ j ∈ Finset.univ.filter (fun j => SP.lam j = SP.lam j₀),
                    (B : ℝ)⁻¹ * modeVij cert γstar CSig Fp SP ϱ i₀ j₀ := by
                  rw [Finset.sum_filter]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  by_cases hj : SP.lam j = SP.lam j₀
                  · rw [if_pos (Prod.ext hi hj)]
                    rw [mm_modeVij_eq_of_eigs cert γstar CSig Fp SP ϱ i i₀ j j₀ hi hj]
                    simp [hj]
                  · rw [if_neg]
                    · simp [hj]
                    · intro hp
                      exact hj (congrArg Prod.snd hp)
              _ = _ := by simp
          · rw [if_neg hi]
            apply Finset.sum_eq_zero
            intro j _
            rw [if_neg]
            intro hp
            exact hi (congrArg Prod.fst hp)
        rw [Finset.sum_congr rfl (fun i _ => hterm i)]
        have hout :
            (∑ i : Fin m, if SP.μ i = SP.μ i₀ then
                ((Finset.univ.filter fun j => SP.lam j = SP.lam j₀).card : ℝ) *
                  ((B : ℝ)⁻¹ * modeVij cert γstar CSig Fp SP ϱ i₀ j₀) else 0) =
              ∑ i ∈ Finset.univ.filter (fun i => SP.μ i = SP.μ i₀),
                ((Finset.univ.filter fun j => SP.lam j = SP.lam j₀).card : ℝ) *
                  ((B : ℝ)⁻¹ * modeVij cert γstar CSig Fp SP ϱ i₀ j₀) := by
          rw [Finset.sum_filter]
        rw [hout]
        simp only [Finset.sum_const, nsmul_eq_mul]
        unfold modeVij
        have hzeta : measureZeta cert γstar CSig Fp SP ϱ (SP.μ i₀, SP.lam j₀) =
            lagGammaBar cert γstar CSig Fp.β B SP.μ SP.lam
              (classDiag SP.μ (SP.μ i₀)) (classDiag SP.lam (SP.lam j₀)) ϱ ϱ := by
          rw [measureZeta, mm_pairMeasure_apply]
          simp [muVals, lamVals]
        rw [hzeta]
        dsimp [r, t] at hr ht ⊢
        field_simp
      · have hy' : ∀ j, SP.lam j ≠ y := by
          intro j h
          exact hy (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h⟩)
        simp only [hx, hy, and_false, if_false]
        symm
        apply Finset.sum_eq_zero
        intro i _
        apply Finset.sum_eq_zero
        intro j _
        rw [if_neg]
        intro hp
        exact hy' j (congrArg Prod.snd hp)
    · have hx' : ∀ i, SP.μ i ≠ x := by
        intro i h
        exact hx (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h⟩)
      simp only [hx, false_and, if_false]
      symm
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      intro hp
      exact hx' i (congrArg Prod.fst hp)

/-- `prop:app-vol-disintegration`, part (ii), actual: for every time `t`, each entry series
`𝔳^{act}_ij(ϱ) = modeVijActual` converges absolutely (with integrable terms) and is nonnegative,
and `𝔠_int(ϱ) = B⁻¹ ∑_{i,j} 𝔳^{act}_ij(ϱ) δ_{(μ_i,λ_j)}` (`measureInt`). Snapshot
`cr-2026-10-23`. LaTeX, verbatim from `section.tex` (the whole environment):

\begin{proposition}[Mode coefficients]\label{prop:app-vol-disintegration}
For an eigenvalue $\mu$ of $\Sigmaout$ and $\lambda$ of $\Sigmain$ let
$r_\mu\defeq\#\{i:\mu_i=\mu\}$ and $t_\lambda\defeq\#\{j:\lambda_j=\lambda\}$, and put
\begin{equation}\label{eqn:app-vol-vij}
\mathfrak v_{ij}(\ridge)\defeq\frac{B\,\zeta_\ridge(\{(\mu_i,\lambda_j)\})}{r_{\mu_i}\,t_{\lambda_j}} .
\end{equation}
Then $\mathfrak v_{ij}(\ridge)\ge0$, it depends on $(i,j)$ only through
$(\mu_i,\lambda_j)$, it vanishes when $\mu_i\lambda_j=0$, and
$\zeta_\ridge=B^{-1}\sum_{i,j}\mathfrak v_{ij}(\ridge)\,\delta_{(\mu_i,\lambda_j)}$. The actual
entry coefficients
\begin{equation}\label{eqn:app-vol-vij-actual}
\mathsf v_{ij}(\ridge)\defeq\EE\big(({\mathsf S}^{\mathrm c}_t(\ridge))_{ij}\big)^2+2\sum_{\ell\ge1}\EE\big[({\mathsf S}^{\mathrm c}_t(\ridge))_{ij}({\mathsf S}^{\mathrm c}_{t+\ell}(\ridge))_{ij}\big]
\end{equation}
converge absolutely, are nonnegative, and satisfy
$\mathfrak C_{\mathrm{int}}(\ridge)=B^{-1}\sum_{i,j}\mathsf v_{ij}(\ridge)\,\delta_{(\mu_i,\lambda_j)}$; consequently,
under \cref{assum:app-setup-regime},
\[
\sup_{\ridge\in I}\Big\|\frac1B\sum_{i,j}\big(\mathsf v_{ij}(\ridge)-\mathfrak v_{ij}(\ridge)\big)\delta_{(\mu_i,\lambda_j)}\Big\|_\BL\longrightarrow0 .
\]
\end{proposition} -/
theorem prop_app_vol_disintegration_ii {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (γstar CSig : ℝ) (Fp : FrozenParams m n B)
    (S : FrozenSamples P m n B) (SP : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (ϱ : ℝ) (hϱ : 0 < ϱ) (t : ℤ) :
    (∀ i : Fin m, ∀ j : Fin n,
      Integrable (fun ω => ((SP.uOutᵀ * centredUpd Fp S ϱ t ω * SP.vIn) i j) ^ 2) P ∧
      (∀ ℓ : ℕ, Integrable (fun ω =>
        (SP.uOutᵀ * centredUpd Fp S ϱ t ω * SP.vIn) i j *
          (SP.uOutᵀ * centredUpd Fp S ϱ (t + ((ℓ : ℤ) + 1)) ω * SP.vIn) i j) P) ∧
      Summable (fun ℓ : ℕ => |∫ ω,
        (SP.uOutᵀ * centredUpd Fp S ϱ t ω * SP.vIn) i j *
          (SP.uOutᵀ * centredUpd Fp S ϱ (t + ((ℓ : ℤ) + 1)) ω * SP.vIn) i j ∂P|) ∧
      0 ≤ modeVijActual Fp S SP t ϱ i j) ∧
    measureInt Fp S SP t ϱ = ∑ i : Fin m, ∑ j : Fin n,
      Finsupp.single (SP.μ i, SP.lam j) ((B : ℝ)⁻¹ * modeVijActual Fp S SP t ϱ i j) := by
  classical
  have hI : ϱ ∈ Set.Icc ϱ ϱ := ⟨le_rfl, le_rfl⟩
  have hϱ' : 0 < ϱ ∧ ϱ ≤ ϱ := ⟨hϱ, le_rfl⟩
  refine ⟨fun i j => ⟨?_, fun ℓ => ?_, ?_, ?_⟩, ?_⟩
  · simpa [sq] using ma_entry_prod_int Fp S SP hϱ.le hϱ.le t t i j
  · exact ma_entry_prod_int Fp S SP hϱ.le hϱ.le t (t + ((ℓ : ℤ) + 1)) i j
  · exact (ma_dis_entry Fp S γstar CSig ϱ ϱ hS hCSig hϱ' SP ϱ hI t i j).1
  · exact (ma_dis_entry Fp S γstar CSig ϱ ϱ hS hCSig hϱ' SP ϱ hI t i j).2.2.1
  · rw [ma_pair_regroup SP.μ SP.lam (fun a b => (B : ℝ)⁻¹ * modeVijActual Fp S SP t ϱ a b)]
    unfold measureInt muVals lamVals
    congr 1
    funext μ l
    unfold projOut projIn
    rw [ma_int_lin Fp S γstar CSig hS hCSig SP ϱ hϱ t]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [(ma_dis_entry Fp S γstar CSig ϱ ϱ hS hCSig hϱ' SP ϱ hI t a b).2.1]

/-- `prop:app-vol-disintegration`, part (iii), limit: under `assum:app-setup-regime`, the actual
mode coefficients approximate the deterministic ones in the bounded-Lipschitz norm, uniformly over
`ϱ ∈ I` and all times `t`. Snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex` (the whole
environment):

\begin{proposition}[Mode coefficients]\label{prop:app-vol-disintegration}
For an eigenvalue $\mu$ of $\Sigmaout$ and $\lambda$ of $\Sigmain$ let
$r_\mu\defeq\#\{i:\mu_i=\mu\}$ and $t_\lambda\defeq\#\{j:\lambda_j=\lambda\}$, and put
\begin{equation}\label{eqn:app-vol-vij}
\mathfrak v_{ij}(\ridge)\defeq\frac{B\,\zeta_\ridge(\{(\mu_i,\lambda_j)\})}{r_{\mu_i}\,t_{\lambda_j}} .
\end{equation}
Then $\mathfrak v_{ij}(\ridge)\ge0$, it depends on $(i,j)$ only through
$(\mu_i,\lambda_j)$, it vanishes when $\mu_i\lambda_j=0$, and
$\zeta_\ridge=B^{-1}\sum_{i,j}\mathfrak v_{ij}(\ridge)\,\delta_{(\mu_i,\lambda_j)}$. The actual
entry coefficients
\begin{equation}\label{eqn:app-vol-vij-actual}
\mathsf v_{ij}(\ridge)\defeq\EE\big(({\mathsf S}^{\mathrm c}_t(\ridge))_{ij}\big)^2+2\sum_{\ell\ge1}\EE\big[({\mathsf S}^{\mathrm c}_t(\ridge))_{ij}({\mathsf S}^{\mathrm c}_{t+\ell}(\ridge))_{ij}\big]
\end{equation}
converge absolutely, are nonnegative, and satisfy
$\mathfrak C_{\mathrm{int}}(\ridge)=B^{-1}\sum_{i,j}\mathsf v_{ij}(\ridge)\,\delta_{(\mu_i,\lambda_j)}$; consequently,
under \cref{assum:app-setup-regime},
\[
\sup_{\ridge\in I}\Big\|\frac1B\sum_{i,j}\big(\mathsf v_{ij}(\ridge)-\mathfrak v_{ij}(\ridge)\big)\delta_{(\mu_i,\lambda_j)}\Big\|_\BL\longrightarrow0 .
\]
\end{proposition} -/
theorem prop_app_vol_disintegration_iii (cert : Muon.External.GaussianOpNorm) (R : SetupRegime)
    (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (Sp : ∀ k : ℕ, SpectralData (R.F k).C) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi,
      ∀ φ ∈ Muon.Dynamics.blTest R.CSig,
        |finInt (∑ i : Fin (R.m k), ∑ j : Fin (R.n k),
            Finsupp.single ((Sp k).μ i, (Sp k).lam j)
              ((R.B k : ℝ)⁻¹ * (modeVijActual (R.F k) (S k) (Sp k) t ϱ i j -
                modeVij cert R.γstar R.CSig (R.F k) (Sp k) ϱ i j))) φ| ≤ ε := by
  intro ε hε
  have h := thm_app_vol_joint_forcing_iii_limit cert R Ω P S Sp ε hε
  filter_upwards [h] with k hk
  intro t ϱ hϱI φ hφ
  have hS : SizeFin (R.F k).C (R.B k) R.γstar R.CSig :=
    ⟨R.dims k, R.normOut k, R.normIn k⟩
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le R.hϱ.1 hϱI.1
  have hInt := (prop_app_vol_disintegration_ii R.γstar R.CSig (R.F k) (S k) (Sp k)
    hS R.hC ϱ hϱ0 t).2
  have hZeta := (prop_app_vol_disintegration_i cert R.γstar R.CSig (R.F k) (Sp k)
    hS R.hC ϱ hϱ0).2.2.2
  have hmeasure :
      (∑ i : Fin (R.m k), ∑ j : Fin (R.n k),
        Finsupp.single ((Sp k).μ i, (Sp k).lam j)
          ((R.B k : ℝ)⁻¹ * (modeVijActual (R.F k) (S k) (Sp k) t ϱ i j -
            modeVij cert R.γstar R.CSig (R.F k) (Sp k) ϱ i j))) =
        measureInt (R.F k) (S k) (Sp k) t ϱ -
          measureZeta cert R.γstar R.CSig (R.F k) (Sp k) ϱ := by
    rw [hInt, hZeta]
    simp only [mul_sub, Finsupp.single_sub, Finset.sum_sub_distrib]
  rw [hmeasure]
  exact (hk t ϱ hϱI).1 φ hφ

private lemma hr_lam_one (cert : Muon.External.GaussianOpNorm) {m n B : ℕ} (Fp : FrozenParams m n B)
    (S : SpectralData Fp.C) (hId : Fp.C.Sin = 1) (j : Fin n) : S.lam j = 1 := by
  have h := S.eigIn j
  rw [hId, Matrix.one_mulVec] at h
  have hd := mm_col_dot S.vIn S.hvIn j
  by_contra hne
  have h2 : (S.lam j - 1) • (fun k => S.vIn k j) = 0 := by
    rw [sub_smul, ← h, one_smul, sub_self]
  have h3 : (S.lam j - 1) • ((fun k => S.vIn k j) ⬝ᵥ (fun k => S.vIn k j)) = 0 := by
    rw [← smul_dotProduct, h2, zero_dotProduct]
  rw [hd, smul_eq_mul, mul_one] at h3
  exact hne (by linarith)

private lemma hr_gamma (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (hId : Fp.C.Sin = 1)
    (ϱ : ℝ) (hϱ : 0 < ϱ) (i0 : Fin m) :
    lagGammaBar cert γstar CSig Fp.β B S.μ S.lam (classDiag S.μ (S.μ i0)) (classDiag S.lam 1) ϱ ϱ =
      ((Finset.univ.filter fun k => S.μ k = S.μ i0).card : ℝ) * ((B : ℝ)⁻¹ *
        rowVBar cert γstar CSig Fp.β B S.μ S.lam i0 ϱ ϱ) := by
  classical
  have hB : (B : ℝ) ≠ 0 := by exact_mod_cast Fp.hB.ne'
  have hcd : classDiag S.lam 1 = fun _ => (1 : ℝ) := by
    funext j; simp [classDiag, hr_lam_one cert Fp S hId j]
  have hL : ∀ ℓ : ℕ, lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (classDiag S.μ (S.μ i0))
      (fun _ : Fin n => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ) =
      ((Finset.univ.filter fun k => S.μ k = S.μ i0).card : ℝ) *
        ((B : ℝ)⁻¹ * lagRowBar cert γstar CSig Fp.β ℓ B S.μ S.lam i0 ϱ ϱ) := by
    intro ℓ
    rw [md_lin_sum cert γstar CSig Fp S hS hCSig ℓ ϱ ϱ hϱ hϱ]
    have hrow : ∀ i : Fin m, S.μ i = S.μ i0 →
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1) (fun _ : Fin n => (1 : ℝ))
          (omegaF ϱ) (omegaF ϱ) = (B : ℝ)⁻¹ * lagRowBar cert γstar CSig Fp.β ℓ B S.μ S.lam i0 ϱ ϱ := by
      intro i hi
      have := (thm_app_vol_mode_kernels_iv_mu cert γstar CSig Fp S hS hCSig hId ℓ ϱ ϱ hϱ hϱ i i0 hi).1
      rw [← this]
      unfold lagRowBar
      rw [inv_mul_cancel_left₀ hB]
    have : ∀ i : Fin m, classDiag S.μ (S.μ i0) i *
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (Pi.single i 1) (fun _ : Fin n => (1 : ℝ))
          (omegaF ϱ) (omegaF ϱ) =
        if S.μ i = S.μ i0 then (B : ℝ)⁻¹ * lagRowBar cert γstar CSig Fp.β ℓ B S.μ S.lam i0 ϱ ϱ else 0 := by
      intro i
      by_cases hi : S.μ i = S.μ i0
      · simp [classDiag, hi, hrow i hi]
      · simp [classDiag, hi]
    rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.sum_filter]
    simp
  unfold lagGammaBar rowVBar
  rw [hcd]
  simp_rw [hL]
  set c : ℝ := ((Finset.univ.filter fun k => S.μ k = S.μ i0).card : ℝ)
  have h2 : ∀ ℓ : ℕ, c * ((B : ℝ)⁻¹ * lagRowBar cert γstar CSig Fp.β (ℓ + 1) B S.μ S.lam i0 ϱ ϱ) +
      c * ((B : ℝ)⁻¹ * lagRowBar cert γstar CSig Fp.β (ℓ + 1) B S.μ S.lam i0 ϱ ϱ) =
      (c * (B : ℝ)⁻¹) * (lagRowBar cert γstar CSig Fp.β (ℓ + 1) B S.μ S.lam i0 ϱ ϱ +
        lagRowBar cert γstar CSig Fp.β (ℓ + 1) B S.μ S.lam i0 ϱ ϱ) := fun ℓ => by ring
  simp_rw [h2]
  rw [tsum_mul_left]
  ring

private lemma hr_half_main (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (hId : Fp.C.Sin = 1) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    ∀ i : Fin m, ∀ j : Fin n,
      modeVij cert γstar CSig Fp S ϱ i j = rowVBar cert γstar CSig Fp.β B S.μ S.lam i ϱ ϱ / (n : ℝ) := by
  classical
  intro i j
  have hB : (B : ℝ) ≠ 0 := by exact_mod_cast Fp.hB.ne'
  have hn : (0 : ℝ) < n := by exact_mod_cast (mm_pos_of_fro Fp.A Fp.hA).2
  have hz : measureZeta cert γstar CSig Fp S ϱ (S.μ i, S.lam j) =
      lagGammaBar cert γstar CSig Fp.β B S.μ S.lam
        (classDiag S.μ (S.μ i)) (classDiag S.lam 1) ϱ ϱ := by
    rw [measureZeta, mm_pairMeasure_apply, hr_lam_one cert Fp S hId j]
    simp [muVals, lamVals]
    intro h; exact absurd (hr_lam_one cert Fp S hId j) (h j)
  have hc : (Finset.univ.filter fun k => S.lam k = S.lam j).card = n := by
    rw [Finset.filter_true_of_mem]; simp
    intro k _; rw [hr_lam_one cert Fp S hId k, hr_lam_one cert Fp S hId j]
  unfold modeVij
  rw [hz, hr_gamma cert γstar CSig Fp S hS hCSig hId ϱ hϱ i, hc]
  have := mm_class_card_pos S.μ i
  field_simp

/-- `prop:app-vol-half-recovery`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim
from `section.tex` (the whole environment):

\begin{proposition}[Recovery of the rows]\label{prop:app-vol-half-recovery}
If $\Sigmain=\Id_{\Nin}$, then
$\zeta_\ridge=B^{-1}\sum_i\mathfrak v_i(\ridge)\,\delta_{(\mu_i,1)}$, and
$\mathfrak v_{ij}(\ridge)=\mathfrak v_i(\ridge)/\Nin$, so that $\sum_j\mathfrak v_{ij}(\ridge)=\mathfrak v_i(\ridge)$ for
every $i$.
\end{proposition} -/
theorem prop_app_vol_half_recovery (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (hId : Fp.C.Sin = 1) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    measureZeta cert γstar CSig Fp S ϱ =
      ∑ i : Fin m, Finsupp.single (S.μ i, 1)
        ((B : ℝ)⁻¹ * rowVBar cert γstar CSig Fp.β B S.μ S.lam i ϱ ϱ) ∧
    (∀ i : Fin m, ∀ j : Fin n,
      modeVij cert γstar CSig Fp S ϱ i j = rowVBar cert γstar CSig Fp.β B S.μ S.lam i ϱ ϱ / (n : ℝ)) ∧
    (∀ i : Fin m, ∑ j : Fin n, modeVij cert γstar CSig Fp S ϱ i j =
      rowVBar cert γstar CSig Fp.β B S.μ S.lam i ϱ ϱ) := by
  classical
  have h2 := hr_half_main cert γstar CSig Fp S hS hCSig hId ϱ hϱ
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (mm_pos_of_fro Fp.A Fp.hA).2.ne'
  have h3 : ∀ i : Fin m, ∑ j : Fin n, modeVij cert γstar CSig Fp S ϱ i j =
      rowVBar cert γstar CSig Fp.β B S.μ S.lam i ϱ ϱ := by
    intro i
    simp_rw [h2 i]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨?_, h2, h3⟩
  rw [(prop_app_vol_disintegration_i cert γstar CSig Fp S hS hCSig ϱ hϱ).2.2.2]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [hr_lam_one cert Fp S hId]
  rw [← Finsupp.single_finset_sum, ← Finset.mul_sum, h3 i]

end Muon.Volatility

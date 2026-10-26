import Muon.External.Certificates
import Muon.Dynamics.ODE
import Muon.Setup.Algorithm
import Muon.Setup.Frozen
import Muon.Drift.Defs
import Muon.Volatility.Modes

/-!
# Appendix E, work package L-E.4: the half-anisotropic and continuum corollaries

Snapshot `cr-2026-10-23`. Source: `sections/05-dynamics/section.tex`, `cor:app-dyn-half` (ll. 376–392, with
the row system `eqn:app-dyn-ode-rows`, l. 380) and `cor:app-dyn-continuum` (ll. 401–422, with the measure
equation `eqn:app-dyn-continuum`, l. 410). Card: `sections/05-dynamics/CARD.md` §2, §3 and the L-E.4 row of §5.

Interface only: every proof is `sorry`. Reused, not redefined: `Muon.Dynamics.DynParams`, `DynHyp`, `DynCoeff`,
`Tstar`, `specRect`, `blDist`, `blNorm`, `atomMeasure`, `admMeasures`, `fieldOp`, `riskOf`, `odeMeasure`,
`def_app_dyn_ode` (L-E.2); from `Muon.Setup`: `SpectralData`, `rowQ`, `specMeasure`, `riskSigma`, `devRand`,
`initState`, `Covariances`, `Mat`, `opNorm`, `fro`.

Representation choices (also in the result JSON `open_questions`):
* `eqn:app-dyn-ode-rows` is the Prop `eqn_app_dyn_ode_rows`; `eqn:app-dyn-continuum` is the Prop
  `eqn_app_dyn_continuum`. Both are used as records of their equations, not as declarations of a source label.
* The row coefficient `𝔳_i` is `rowCoef c i = ∑_j 𝔳_ij` (`c.v`). The source defines `𝔳_i` as the row coefficient
  of `eqn:app-vol-rows`; by `prop:app-vol-half-recovery`(iii) (D, under `Σ_in = Id`) the two agree. The
  Lean `rowVBar` of D needs a `FrozenParams` that `DynCoeff` does not carry, so the sum form is used here.
* The row measures live on the line `λ = 1` of `K` (`rowMeas`, atoms at `(μ_i, 1)`). Under `Σ_in = Id` every
  `λ_j = 1`, and the bounded-Lipschitz distance on `K` between measures on that line equals the one-dimensional
  distance on `[0, C_Σ]`, so the BL statements are the source's.
* "Measures weighted by `μ`" is `blDistMu`: `blNorm` applied to `φ ↦ ∫ x.1 φ x dμ − ∫ x.1 φ x dν`.
* `blNorm` and every sup over `τ` or `ω` are guarded by `BddAbove` conjuncts (no `sSup` junk).
* Every "→ 0 in probability" is `∀ ε > 0, Tendsto (fun k ↦ P {ω | ε < sSup …}) atTop (𝓝 0)`.
* `B → ∞` (`hB`), stated in the source as the standing "along a sequence of dimensions with `B → ∞`", is an
  explicit hypothesis of every part that has a limit in `k`.
* The continuum limit (`contLimit`) and the solution class (`eqn_app_dyn_continuum`) follow the source's
  quantifiers: part (i) gives a subsequence; part (ii) is conditional on a subsequence `ι` on which the limits hold.
  Weak convergence on `K` is tested against functions continuous on `K` (the measures are carried by `K`).
* The coefficient data `c` of each dimension are arbitrary in the deterministic statements. Every probabilistic
  statement takes `hc : IsActualCoeff cert (F k) (S k) (c k)`, which identifies `c` with the model's true
  coefficients (drift kernel of C, mode coefficients and forcing of D), as CARD E section 2 instantiates them.
  Without it the probabilistic claims are false for wrong coefficients.
* The covariances are `(F k).C` for a family of frozen parameters `F k` (`FrozenParams`), so that the Lean objects
  of C and D (which take a `FrozenParams`) apply to the same covariance type as `DynHyp`.
-/

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open Muon Muon.Setup

noncomputable section

namespace Muon.Dynamics

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams}
  {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)}

/-! ## Helpers -/

/-- The error process `Δ_t = W_t − W⋆` of the algorithm of `DynHyp`: `devRand` started from `(W_0, M°_{-1})`. -/
def errPath (hyp : DynHyp p P m n B C) (k t : ℕ) : Ω → Mat (m k) (n k) :=
  devRand (C k) (hyp.alg k) (fun ω => initState (hyp.W0 k) (hyp.Mm1 k ω)) (hyp.x k) t

/-- The initial error `Δ_0 = W_0 − W⋆` (`hyp:app-dyn-initial`). -/
def dev0 (hyp : DynHyp p P m n B C) (k : ℕ) : Mat (m k) (n k) :=
  hyp.W0 k - (hyp.alg k).Wstar

/-- The atomic measure `∑_i q_i δ_{(μ_i, 1)}` on `K` of a row array `q` (the row measures of `cor:app-dyn-half`
live on the line `λ = 1`, which is `Σ_in = Id`). -/
def rowMeas {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (q : Fin m → ℝ) : Measure (ℝ × ℝ) :=
  atomMeasure S.μ (fun _ : Fin 1 => (1 : ℝ)) (fun i _ => q i)

/-- Row risk `𝓡 = ½ ∑_i μ_i 𝔮_i` of the row equations (`cor:app-dyn-half`). -/
def rowRisk {m : ℕ} (μ : Fin m → ℝ) (q : Fin m → ℝ) : ℝ :=
  (1 / 2) * ∑ i, μ i * q i

/-- The row coefficient `𝔳_i = ∑_j 𝔳_ij` of `DynCoeff` (see the module docstring). -/
def rowCoef {m n : ℕ} {C : Covariances m n} {S : SpectralData C} {Bk : ℕ}
    (c : DynCoeff p S Bk) (i : Fin m) : ℝ :=
  ∑ j, c.v i j

/-- The actual row measure at macroscopic time `τ`: `χ^act_row(τ) = ∑_i 𝒬_i(Δ_{⌊Bτ⌋}) δ_{μ_i}`
(`cor:app-dyn-half`). -/
def actRow (hyp : DynHyp p P m n B C) (S : ∀ k : ℕ, SpectralData (C k)) (k : ℕ) (ω : Ω) (τ : ℝ) :
    Measure (ℝ × ℝ) :=
  rowMeas (S k) (fun i => rowQ (S k) (errPath hyp k ⌊((B k : ℕ) : ℝ) * τ⌋₊ ω) i)

/-- The actual spectral energy measure at macroscopic time `τ`: `χ^act(τ) = χ(Δ_{⌊Bτ⌋})` (l. 333), the
reused `actMeasure` along the error path of `errPath`. -/
def actMeas (hyp : DynHyp p P m n B C) (S : ∀ k : ℕ, SpectralData (C k)) (k : ℕ) (ω : Ω) (τ : ℝ) :
    Measure (ℝ × ℝ) :=
  actMeasure (S k) (B k) (fun t => errPath hyp k t ω) τ

/-- The bounded-Lipschitz distance of the measures weighted by `μ` (the first coordinate on `K`):
`‖μ m − μ ν‖_BL` read as `blNorm` of `φ ↦ ∫ x.1 φ dμ − ∫ x.1 φ dν`. -/
def blDistMu (Cs : ℝ) (μ ν : Measure (ℝ × ℝ)) : ℝ :=
  blNorm Cs (fun φ => ∫ x, x.1 * φ x ∂μ - ∫ x, x.1 * φ x ∂ν)

/-- The row system `eqn:app-dyn-ode-rows` (`cor:app-dyn-half`) for the row array `q` on `[0, T]`, with
risk positive on `[0, T]` (the field is defined only there, as in `def_app_dyn_ode`). Written in the variables
`B 𝔮_i`, `B = Bc`:
`d/dτ (B 𝔮_i) = −2h 𝔡_i (B 𝔮_i)/√𝓡 + h² 𝔳_i`, `𝓡 = ½ ∑_i μ_i 𝔮_i`, `𝔮_i(0) = q0_i`,
with `𝔡_i = 𝔡(μ_i, 1)`. -/
def eqn_app_dyn_ode_rows {m : ℕ} (h Bc : ℝ) (μ : Fin m → ℝ) (d : ℝ × ℝ → ℝ) (v : Fin m → ℝ) (T : ℝ)
    (q0 : Fin m → ℝ) (q : ℝ → Fin m → ℝ) : Prop :=
  q 0 = q0 ∧ (∀ τ ∈ Icc 0 T, 0 < rowRisk μ (q τ)) ∧
    ∀ τ ∈ Icc 0 T, HasDerivWithinAt (fun σ i => Bc * q σ i)
      (fun i => -(2 * h * d (μ i, 1)) / Real.sqrt (rowRisk μ (q τ)) * (Bc * q τ i) + h ^ 2 * v i)
      (Icc 0 T) τ

/-- The limit data of `cor:app-dyn-continuum`(i) along a subsequence `ι` of dimensions: uniform convergence of
`𝔡_B` on `K`, weak convergence of `ζ_B` and of `χ^act_B(0) = χ(Δ_0)` on `K`, with the limits finite and carried
by `K`. -/
def contLimit (hyp : DynHyp p P m n B C) (S : ∀ k : ℕ, SpectralData (C k))
    (c : ∀ k : ℕ, DynCoeff p (S k) (B k)) (ι : ℕ → ℕ) (dinf : ℝ × ℝ → ℝ) (ζinf χ0 : Measure (ℝ × ℝ)) :
    Prop :=
  TendstoUniformlyOn (fun n => (c (ι n)).d) dinf atTop (specRect p.CSig) ∧
  (IsFiniteMeasure ζinf ∧ ζinf (specRect p.CSig)ᶜ = 0 ∧
    ∀ f : ℝ × ℝ → ℝ, ContinuousOn f (specRect p.CSig) →
      Tendsto (fun n => ∫ x, f x ∂(c (ι n)).ζ) atTop (𝓝 (∫ x, f x ∂ζinf))) ∧
  (IsFiniteMeasure χ0 ∧ χ0 (specRect p.CSig)ᶜ = 0 ∧
    ∀ f : ℝ × ℝ → ℝ, ContinuousOn f (specRect p.CSig) →
      Tendsto (fun n => ∫ x, f x ∂(specMeasure (S (ι n)) (dev0 hyp (ι n)))) atTop
        (𝓝 (∫ x, f x ∂χ0)))

/-- The measure equation `eqn:app-dyn-continuum` on `[0, T⋆]` for a path `χ` with values in `𝔐`, continuous for
the bounded-Lipschitz norm, with the field `fieldOp` (weak form of `𝖥_B`) built from `𝔡_∞`, `ζ_∞`. -/
def eqn_app_dyn_continuum (p : DynParams) (dinf : ℝ × ℝ → ℝ) (ζinf χ0 : Measure (ℝ × ℝ))
    (χ : ℝ → Measure (ℝ × ℝ)) : Prop :=
  χ 0 = χ0 ∧ (∀ τ ∈ Icc 0 (Tstar p), χ τ ∈ admMeasures p) ∧
  (∀ τ ∈ Icc 0 (Tstar p), ∀ ε > 0, ∃ δ > 0, ∀ σ ∈ Icc 0 (Tstar p), |σ - τ| < δ →
    blDist p.CSig (χ σ) (χ τ) < ε) ∧
  ∀ τ ∈ Icc 0 (Tstar p), ∀ φ : ℝ × ℝ → ℝ, Measurable φ → (∃ M0 : ℝ, ∀ x, |φ x| ≤ M0) →
    IntervalIntegrable (fun σ => fieldOp p.h dinf ζinf (χ σ) φ) volume 0 τ ∧
    ∫ x, φ x ∂(χ τ) = ∫ x, φ x ∂χ0 + ∫ σ in (0 : ℝ)..τ, fieldOp p.h dinf ζinf (χ σ) φ

/-- The identification `IsActualCoeff` of the coefficient data `c` of one dimension with the model's true
coefficients, instantiated from C and D (CARD E section 2): `F.β = p.β`; `c.d = 𝔡` on `K`, the drift kernel of
`cor:app-drift-kernel` (`Muon.Drift.kernel` with the EMA weights `emaW β` and the spectral measures of `F`);
`c.v i j = 𝔳_ij(ϱ)` (`modeVij`, `eqn:app-vol-vij`); `c.ζ = ζ_ϱ` (`measureZeta`, `eqn:app-vol-measures`, as
the atomic measure `∑ Γ̄ δ`). Source: `eqn:app-drift-kernel`, `eqn:app-vol-vij`, `eqn:app-vol-measures`. -/
def IsActualCoeff (cert : Muon.External.GaussianOpNorm) {m n B : ℕ} (F : FrozenParams m n B)
    (S : SpectralData F.C) (c : DynCoeff p S B) : Prop :=
  F.β = p.β ∧
  (∀ x ∈ specRect p.CSig, c.d x =
    Muon.Drift.kernel (emaW p.β) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) p.ϱ x.1 x.2) ∧
  (∀ i j, c.v i j = Muon.Volatility.modeVij cert p.γstar p.CSig F S p.ϱ i j) ∧
  c.ζ = Finsupp.sum (Muon.Volatility.measureZeta cert p.γstar p.CSig F S p.ϱ)
    (fun x r => ENNReal.ofReal r • Measure.dirac x)

private lemma actual_finsupp_measure_mass (a : (ℝ × ℝ) →₀ ℝ) (ha : ∀ x, 0 ≤ a x) :
    (Finsupp.sum a (fun x r => ENNReal.ofReal r • Measure.dirac x)).real univ =
      Muon.Volatility.finTV a := by
  rw [Measure.real_def]
  unfold Muon.Volatility.finTV Finsupp.sum
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [ENNReal.toReal_sum (fun x _ ↦ ENNReal.ofReal_ne_top)]
  exact Finset.sum_congr rfl fun x _ ↦ by
    rw [ENNReal.toReal_ofReal (ha x), abs_of_nonneg (ha x)]

private lemma actual_finsupp_measure_eq_atom {m n : ℕ} (mu : Fin m → ℝ) (lam : Fin n → ℝ)
    (a : (ℝ × ℝ) →₀ ℝ) (q : Fin m → Fin n → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hq : ∀ i j, 0 ≤ q i j)
    (heq : a = ∑ i : Fin m, ∑ j : Fin n, Finsupp.single (mu i, lam j) (q i j)) :
    Finsupp.sum a (fun x r => ENNReal.ofReal r • Measure.dirac x) = atomMeasure mu lam q := by
  classical
  ext s hs
  have hreal := congrArg
    (fun b : (ℝ × ℝ) →₀ ℝ => b.sum fun x r => if x ∈ s then r else 0) heq
  have hreal' :
      a.sum (fun x r => if x ∈ s then r else 0) =
        ∑ i : Fin m, ∑ j : Fin n, if (mu i, lam j) ∈ s then q i j else 0 := by
    rw [hreal]
    rw [← Finsupp.sum_finsetSum_index (fun _ ↦ by simp)
      (fun _ x y ↦ by split_ifs <;> simp_all)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finsupp.sum_finsetSum_index (fun _ ↦ by simp)
      (fun _ x y ↦ by split_ifs <;> simp_all)]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finsupp.sum_single_index (by simp)]
  unfold atomMeasure Finsupp.sum
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs, Set.indicator_apply, Pi.one_apply]
  calc
    ∑ x ∈ a.support, ENNReal.ofReal (a x) * (if x ∈ s then 1 else 0) =
        ENNReal.ofReal (∑ x ∈ a.support, if x ∈ s then a x else 0) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun x _ ↦ by split_ifs <;> simp_all)]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ s <;> simp [hx]
    _ = ENNReal.ofReal (∑ i : Fin m, ∑ j : Fin n,
          if (mu i, lam j) ∈ s then q i j else 0) := by
      exact congrArg ENNReal.ofReal (by simpa only [Finsupp.sum] using hreal')
    _ = ∑ i : Fin m, ∑ j : Fin n,
        ENNReal.ofReal (q i j) * (if (mu i, lam j) ∈ s then 1 else 0) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦
        Finset.sum_nonneg fun j _ ↦ by split_ifs <;> simp_all)]
      apply Finset.sum_congr rfl
      intro i _
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ by split_ifs <;> simp_all)]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : (mu i, lam j) ∈ s <;> simp [hij]

/-- Existence of the actual coefficients at one dimension under the standing size conditions (`SizeFin`,
`1 ≤ C_Σ`) and `F.β = p.β`. Card E section 5 / C and D coefficient identities; sorried, its own proof card.
Makes `IsActualCoeff` non-vacuous: the probabilistic statements are instantiated at these coefficients. -/
theorem actualCoeff_exists (cert : Muon.External.GaussianOpNorm) {m n B : ℕ} (F : FrozenParams m n B)
    (S : SpectralData F.C) (hβ : F.β = p.β) (hS : Muon.Volatility.SizeFin F.C B p.γstar p.CSig) :
    ∃ c : DynCoeff p S B, IsActualCoeff cert F S c := by
  classical
  let d : ℝ × ℝ → ℝ := fun x ↦
    Muon.Drift.kernel (emaW p.β) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) p.ϱ x.1 x.2
  let v : Fin m → Fin n → ℝ := fun i j ↦
    Muon.Volatility.modeVij cert p.γstar p.CSig F S p.ϱ i j
  let z : (ℝ × ℝ) →₀ ℝ := Muon.Volatility.measureZeta cert p.γstar p.CSig F S p.ϱ
  have hmax : 0 < max m n := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hm : m = 0 := by omega
    have hn : n = 0 := by omega
    have hA := F.hA
    simp [hm, hn, fro] at hA
  have hmaxR : (0 : ℝ) < (max m n : ℕ) := by exact_mod_cast hmax
  have hBR : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hgamma : 0 < p.γstar := by
    nlinarith [hS.1]
  have hC : 0 < p.CSig := lt_of_lt_of_le zero_lt_one p.hC
  have hDB : Muon.Drift.DriftBound F p.CSig p.γstar := ⟨hS.2.1, hS.2.2, hS.1⟩
  have hd := Muon.Drift.cor_app_drift_kernel_ii hC hgamma
    (Muon.Drift.emaW_weightClass p.β p.hβ) F hDB p.hϱ
  have hdlip := Muon.Drift.cor_app_drift_kernel_ii_lip hC hgamma p.hϱ le_rfl
    (Muon.Drift.emaW_weightClass p.β p.hβ) F hDB (ϱ := p.ϱ) ⟨le_rfl, le_rfl⟩
  have hvfacts := Muon.Volatility.prop_app_vol_disintegration_i cert p.γstar p.CSig F S hS
    p.hC p.ϱ p.hϱ
  have hzfacts := Muon.Volatility.thm_app_vol_joint_forcing_iii_nonneg cert p.γstar p.CSig F S hS
    p.hC p.ϱ p.ϱ ⟨p.hϱ, le_rfl⟩
  have hznonneg : ∀ x, 0 ≤ z x := by
    intro x
    exact hzfacts.1 p.ϱ ⟨le_rfl, le_rfl⟩ x.1 x.2
  have hvnonneg : ∀ i j, 0 ≤ v i j := hvfacts.1
  have hzrepr : z =
      ∑ i : Fin m, ∑ j : Fin n, Finsupp.single (S.μ i, S.lam j) ((B : ℝ)⁻¹ * v i j) :=
    hvfacts.2.2.2
  have hqnonneg : ∀ i j, 0 ≤ v i j / (B : ℝ) := fun i j ↦
    div_nonneg (hvnonneg i j) hBR.le
  have hzmeasure : Finsupp.sum z (fun x r ↦ ENNReal.ofReal r • Measure.dirac x) =
      atomMeasure S.μ S.lam (fun i j ↦ v i j / (B : ℝ)) := by
    apply actual_finsupp_measure_eq_atom S.μ S.lam z (fun i j ↦ v i j / (B : ℝ))
      hznonneg hqnonneg
    simpa [div_eq_inv_mul] using hzrepr
  let c : DynCoeff p S B := {
    d := d
    d_nonneg := by
      intro x hx
      exact (hd.2.2.2.1 x.1 x.2 hx.1.1 hx.2.1).1
    d_le := by
      intro x hx
      have hk := (hd.2.2.2.1 x.1 x.2 hx.1.1 hx.2.1).2
      have hprod : x.1 * x.2 ≤ p.CSig ^ 2 := by
        simpa [pow_two] using mul_le_mul hx.1.2 hx.2.2 hx.2.1
          (hx.1.1.trans hx.1.2)
      have hsqrt : 0 < Real.sqrt (2 * p.ϱ) :=
        Real.sqrt_pos.2 (mul_pos (by norm_num) p.hϱ)
      exact hk.trans (by
        unfold dMax
        exact div_le_div_of_nonneg_right hprod hsqrt.le)
    d_lip := by
      intro x hx y hy
      have h1 := hdlip.1 x.1 y.1 x.2 hx.1 hy.1 hx.2
      have h2 := hdlip.2 y.1 x.2 y.2 hy.1 hx.2 hy.2
      calc
        |d x - d y| ≤ |d x - d (y.1, x.2)| + |d (y.1, x.2) - d y| := by
          dsimp [d]
          exact abs_sub_le _ _ _
        _ ≤ p.CSig / Real.sqrt (2 * p.ϱ) * |x.1 - y.1| +
            p.CSig / Real.sqrt (2 * p.ϱ) * |x.2 - y.2| := add_le_add h1 h2
        _ = p.CSig / Real.sqrt (2 * p.ϱ) * l1 x y := by
          unfold l1
          ring
    v := v
    v_nonneg := hvnonneg
    ζ := Finsupp.sum z (fun x r ↦ ENNReal.ofReal r • Measure.dirac x)
    ζ_eq := hzmeasure
    ζ_mass := by
      rw [actual_finsupp_measure_mass z hznonneg]
      simpa [mZeta, hβ] using hzfacts.2 p.ϱ ⟨le_rfl, le_rfl⟩
  }
  refine ⟨c, hβ, ?_, ?_, rfl⟩
  · intro x hx
    rfl
  · intro i j
    rfl

/-! ## `cor:app-dyn-half` -/

private lemma half_lam_eq_one {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (hSin : C.Sin = 1) (j : Fin n) : S.lam j = 1 := by
  have h := eig_v S j
  rw [hSin, Matrix.one_mulVec] at h
  have hn := sum_col_sq_eq_one S.vIn S.hvIn j
  have hvv : S.v j ⬝ᵥ S.v j = 1 := by
    simpa [dotProduct, SpectralData.v, sq] using hn
  have h2 := congrArg (fun w => S.v j ⬝ᵥ w) h
  simp only [dotProduct_smul, smul_eq_mul] at h2
  rw [hvv] at h2
  linarith

private lemma half_odeRisk_eq_rowRisk {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (B : ℝ) (e : Fin m → Fin n → ℝ) (hlam : ∀ j, lam j = 1) :
    odeRisk μ lam B e = rowRisk μ (fun i => (∑ j, e i j) / B ^ 2) := by
  unfold odeRisk rowRisk
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  calc
    ∑ j, μ i * lam j * e i j / B ^ 2 = ∑ j, μ i * (e i j / B ^ 2) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hlam j]
      ring
    _ = μ i * ∑ j, e i j / B ^ 2 := by rw [Finset.mul_sum]
    _ = μ i * ((∑ j, e i j) / B ^ 2) := by rw [Finset.sum_div]

private lemma half_mode_to_row {m n : ℕ} {C : Covariances m n} (p : DynParams)
    (S : SpectralData C) {B : ℕ} (c : DynCoeff p S B) (Δ0 : Mat m n)
    (hSin : C.Sin = 1) (hBpos : 0 < B) (e : ℝ → Fin m → Fin n → ℝ)
    (he : def_app_dyn_ode p S c Δ0 (Tstar p) e) :
    eqn_app_dyn_ode_rows p.h (B : ℝ) S.μ c.d (rowCoef c) (Tstar p)
      (fun i => rowQ S Δ0 i) (fun τ i => (∑ j, e τ i j) / (B : ℝ) ^ 2) := by
  have hB : (B : ℝ) ≠ 0 := by exact_mod_cast hBpos.ne'
  have hlam : ∀ j, S.lam j = 1 := half_lam_eq_one S hSin
  refine ⟨?_, ?_, ?_⟩
  · funext i
    change (∑ j, e 0 i j) / (B : ℝ) ^ 2 = rowQ S Δ0 i
    rw [he.1.1]
    simp only [odeInit]
    rw [lem_app_setup_decomposition_i S Δ0 i, ← Finset.mul_sum]
    field_simp
  · intro τ hτ
    rw [← half_odeRisk_eq_rowRisk S.μ S.lam (B : ℝ) (e τ) hlam]
    exact he.2 τ hτ
  · intro τ hτ
    rw [hasDerivWithinAt_pi]
    intro i
    have hij : ∀ j, HasDerivWithinAt (fun σ => e σ i j)
        (odeRHS p.h (B : ℝ) S.μ S.lam c.d c.v (e τ) i j)
        (Icc 0 (Tstar p)) τ := fun j =>
      hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp (he.1.2 τ hτ) i) j
    have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ)
      (fun j _ => hij j)
    convert hsum.const_mul ((B : ℝ) / (B : ℝ) ^ 2) using 1
    · funext σ
      field_simp
    · unfold odeRHS rowCoef
      rw [half_odeRisk_eq_rowRisk S.μ S.lam (B : ℝ) (e τ) hlam]
      simp_rw [hlam]
      rw [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
      field_simp

private lemma half_row_unique {m : ℕ} (h B : ℝ) (μ : Fin m → ℝ)
    (d : ℝ × ℝ → ℝ) (v : Fin m → ℝ) (T : ℝ) (hT : 0 ≤ T) (hB : B ≠ 0)
    (q0 : Fin m → ℝ) (q q' : ℝ → Fin m → ℝ)
    (hq : eqn_app_dyn_ode_rows h B μ d v T q0 q)
    (hq' : eqn_app_dyn_ode_rows h B μ d v T q0 q') :
    EqOn q q' (Icc 0 T) := by
  let R : (Fin m → ℝ) → ℝ := fun y => rowRisk μ (fun i => y i / B)
  let f : (Fin m → ℝ) → (Fin m → ℝ) := fun y i =>
    -(2 * h * d (μ i, 1)) / Real.sqrt (R y) * y i + h ^ 2 * v i
  let y : ℝ → Fin m → ℝ := fun t i => B * q t i
  let y' : ℝ → Fin m → ℝ := fun t i => B * q' t i
  have hR : Continuous R := by
    dsimp only [R, rowRisk]
    fun_prop
  have hRlin : IsLinearMap ℝ R := by
    constructor
    · intro x z
      dsimp only [R, rowRisk]
      simp_rw [Pi.add_apply, add_div, mul_add, Finset.sum_add_distrib]
      ring
    · intro a x
      dsimp only [R, rowRisk]
      simp_rw [Pi.smul_apply, smul_eq_mul]
      have heq : ∀ i, μ i * (a * x i / B) = a * (μ i * (x i / B)) := by
        intro i
        ring
      simp_rw [heq, ← Finset.mul_sum]
      ring
  have hf : ContDiffOn ℝ 1 f {y | 0 < R y} := by
    have hRdiff : ContDiff ℝ 1 R := by
      dsimp only [R, rowRisk]
      fun_prop
    have hsqrt : ContDiffOn ℝ 1 (fun y => Real.sqrt (R y)) {y | 0 < R y} :=
      hRdiff.contDiffOn.sqrt (fun y hy => ne_of_gt hy)
    have hsqrt_ne : ∀ y ∈ {y | 0 < R y}, Real.sqrt (R y) ≠ 0 :=
      fun y hy => (Real.sqrt_pos.2 hy).ne'
    dsimp only [f]
    apply contDiffOn_pi'
    intro i
    exact ((contDiffOn_const.div hsqrt hsqrt_ne).mul (by fun_prop)).add contDiffOn_const
  have hy_cont : ContinuousOn y (Icc 0 T) :=
    fun t ht => (hq.2.2 t ht).continuousWithinAt
  have hy'_cont : ContinuousOn y' (Icc 0 T) :=
    fun t ht => (hq'.2.2 t ht).continuousWithinAt
  have hRy : ∀ t ∈ Icc 0 T, 0 < R (y t) := by
    intro t ht
    simpa [R, y, hB] using hq.2.1 t ht
  have hRy' : ∀ t ∈ Icc 0 T, 0 < R (y' t) := by
    intro t ht
    simpa [R, y', hB] using hq'.2.1 t ht
  have hRy_cont : ContinuousOn (fun t => R (y t)) (Icc 0 T) :=
    hR.comp_continuousOn hy_cont
  have hRy'_cont : ContinuousOn (fun t => R (y' t)) (Icc 0 T) :=
    hR.comp_continuousOn hy'_cont
  obtain ⟨ty, hty, hmRy⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT) hRy_cont
  obtain ⟨ty', hty', hmRy'⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT) hRy'_cont
  obtain ⟨uy, huy, hmuy⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 hT) (continuous_norm.comp_continuousOn hy_cont)
  obtain ⟨uy', huy', hmuy'⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 hT) (continuous_norm.comp_continuousOn hy'_cont)
  let δ := min (R (y ty)) (R (y' ty'))
  let M := max ‖y uy‖ ‖y' uy'‖
  let s : Set (Fin m → ℝ) := Metric.closedBall 0 M ∩ {x | δ ≤ R x}
  have hδ : 0 < δ := lt_min (hRy ty hty) (hRy' ty' hty')
  have hsconv : Convex ℝ s := by
    dsimp only [s]
    exact (convex_closedBall 0 M).inter (convex_halfSpace_ge hRlin δ)
  have hscompact : IsCompact s := by
    dsimp only [s]
    exact (isCompact_closedBall 0 M).inter_right (isClosed_le continuous_const hR)
  have hspos : s ⊆ {x | 0 < R x} := by
    intro x hx
    exact hδ.trans_le hx.2
  obtain ⟨K, hLip⟩ :=
    (hf.mono hspos).exists_lipschitzOnWith one_ne_zero hsconv hscompact
  have hyy' : EqOn y y' (Icc 0 T) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => f) (s := fun _ => s) (K := K)
    · intro t ht
      exact hLip
    · exact hy_cont
    · intro t ht
      convert (hq.2.2 t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht) using 1 <;> simp [f, R, y, hB]
    · intro t ht
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall_zero_iff]
        exact (hmuy (mem_Icc_of_Ico ht)).trans (le_max_left _ _)
      · exact (min_le_left _ _).trans
          (show R (y ty) ≤ R (y t) from hmRy (mem_Icc_of_Ico ht))
    · exact hy'_cont
    · intro t ht
      convert (hq'.2.2 t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht) using 1 <;> simp [f, R, y', hB]
    · intro t ht
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall_zero_iff]
        exact (hmuy' (mem_Icc_of_Ico ht)).trans (le_max_right _ _)
      · exact (min_le_right _ _).trans
          (show R (y' ty') ≤ R (y' t) from hmRy' (mem_Icc_of_Ico ht))
    · funext i
      simp [y, y', hq.1, hq'.1]
  intro t ht
  funext i
  have hi := congrFun (hyy' ht) i
  dsimp only [y, y'] at hi
  exact (mul_left_cancel₀ hB hi)

private lemma half_dMax_nonneg (p : DynParams) : 0 ≤ dMax p := by
  unfold dMax
  exact div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)

private lemma half_mZeta_nonneg (p : DynParams) : 0 ≤ mZeta p := by
  have hk : 0 ≤ kStar p.CSig p.γstar p.ϱ := by
    unfold kStar
    exact mul_nonneg (by linarith [p.hC]) (Real.sqrt_nonneg _)
  unfold mZeta
  exact add_nonneg p.hγ
    (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk) p.hβ.1)
      (by linarith [p.hβ.2]))

private lemma half_CE_nonneg (p : DynParams) : 0 ≤ CE p := by
  unfold CE
  exact add_nonneg
    (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hh.le)
      (half_dMax_nonneg p)) (by linarith [p.hE])) (Real.sqrt_nonneg _))
    (mul_nonneg (sq_nonneg _) (half_mZeta_nonneg p))

private lemma half_CR_nonneg (p : DynParams) : 0 ≤ CR p := by
  unfold CR
  exact add_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hh.le) (half_dMax_nonneg p))
      (Real.sqrt_nonneg _))
    (div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (half_mZeta_nonneg p)) (by norm_num))

private lemma half_Tstar_nonneg (p : DynParams) : 0 ≤ Tstar p := by
  unfold Tstar
  exact div_nonneg (le_of_lt (lt_min p.hr0 zero_lt_one))
    (mul_nonneg (by norm_num) (by linarith [half_CE_nonneg p, half_CR_nonneg p]))

private lemma half_rowMeas_eq_atomMeasure {m n : ℕ} {C : Covariances m n}
    (S : SpectralData C) (a : Fin m → Fin n → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    rowMeas S (fun i ↦ ∑ j, a i j) = atomMeasure S.μ (fun _ : Fin n ↦ (1 : ℝ)) a := by
  unfold rowMeas atomMeasure
  ext s hs
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, hs,
    Measure.dirac_apply']
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ ha _ j)]
  simp only [Fin.sum_univ_one, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_mul Finset.univ (fun j ↦ ENNReal.ofReal (a i j))
    (s.indicator 1 (S.μ i, 1))

private lemma half_actRow_eq_actMeas
    (hyp : DynHyp p P m n B C) (S : ∀ k : ℕ, SpectralData (C k))
    (hSin : ∀ k : ℕ, (C k).Sin = 1) (k : ℕ) (omega : Ω) (tau : ℝ) :
    actRow hyp S k omega tau = actMeas hyp S k omega tau := by
  unfold actRow actMeas Muon.Dynamics.actMeasure specMeasure
  rw [show (fun i ↦ rowQ (S k) (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i) =
      (fun i ↦ ∑ j, modeQ (S k) (errPath hyp k ⌊(B k : ℝ) * tau⌋₊ omega) i j) by
    funext i
    exact lem_app_setup_decomposition_i (S k) _ i]
  rw [half_rowMeas_eq_atomMeasure]
  · congr 2
    funext j
    exact (half_lam_eq_one (S k) (hSin k) j).symm
  · intro i j
    exact sq_nonneg _

private lemma half_rowMeas_eq_odeMeasure {m n : ℕ} {C : Covariances m n}
    (S : SpectralData C) (hSin : C.Sin = 1) (Bc : ℝ)
    (e : Fin m → Fin n → ℝ) (he : ∀ i j, 0 ≤ e i j / Bc ^ 2) :
    rowMeas S (fun i ↦ ∑ j, e i j / Bc ^ 2) = odeMeasure Bc S.μ S.lam e := by
  unfold odeMeasure
  rw [half_rowMeas_eq_atomMeasure S (fun i j ↦ e i j / Bc ^ 2) he]
  congr 2
  funext j
  exact (half_lam_eq_one S hSin j).symm

private lemma half_row_solution_eq_mode_sum {m n : ℕ} {C : Covariances m n}
    (p : DynParams) (S : SpectralData C) {Bk : ℕ} (c : DynCoeff p S Bk)
    (Delta0 : Mat m n) (hSin : C.Sin = 1) (hBpos : 0 < Bk)
    (e : ℝ → Fin m → Fin n → ℝ) (he : def_app_dyn_ode p S c Delta0 (Tstar p) e)
    (q : ℝ → Fin m → ℝ)
    (hq : eqn_app_dyn_ode_rows p.h (Bk : ℝ) S.μ c.d (rowCoef c) (Tstar p)
      (fun i ↦ rowQ S Delta0 i) q) :
    ∀ tau ∈ Icc 0 (Tstar p), ∀ i, q tau i = (∑ j, e tau i j) / (Bk : ℝ) ^ 2 := by
  have hBc : (Bk : ℝ) ≠ 0 := by exact_mod_cast hBpos.ne'
  have hEq := half_row_unique p.h (Bk : ℝ) S.μ c.d (rowCoef c) (Tstar p)
    (half_Tstar_nonneg p) hBc (fun i ↦ rowQ S Delta0 i) q
    (fun tau i ↦ (∑ j, e tau i j) / (Bk : ℝ) ^ 2) hq
    (half_mode_to_row p S c Delta0 hSin hBpos e he)
  intro tau ht i
  exact congrFun (hEq ht) i

private lemma half_integral_mul_snd_rowMeas {m n : ℕ} {C : Covariances m n}
    (S : SpectralData C) (q : Fin m → ℝ) (phi : ℝ × ℝ → ℝ) :
    (∫ x, x.1 * x.2 * phi x ∂(rowMeas S q)) =
      ∫ x, x.1 * phi x ∂(rowMeas S q) := by
  unfold rowMeas atomMeasure
  simp only [Fin.sum_univ_one]
  rw [MeasureTheory.integral_finsetSum_measure (fun i _ ↦
    (MeasureTheory.integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  rw [MeasureTheory.integral_finsetSum_measure (fun i _ ↦
    (MeasureTheory.integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  simp

private lemma half_blDistMu_eq_mul_snd_rowMeas {m n : ℕ} {C : Covariances m n}
    (Cs : ℝ) (S : SpectralData C) (q r : Fin m → ℝ) :
    blDistMu Cs (rowMeas S q) (rowMeas S r) =
      blNorm Cs (fun phi ↦
        ∫ x, x.1 * x.2 * phi x ∂(rowMeas S q) -
          ∫ x, x.1 * x.2 * phi x ∂(rowMeas S r)) := by
  unfold blDistMu
  apply congrArg (blNorm Cs)
  funext phi
  rw [half_integral_mul_snd_rowMeas, half_integral_mul_snd_rowMeas]

/-- `cor:app-dyn-half`(i), snapshot `cr-2026-10-23`. Row system `eqn:app-dyn-ode-rows`: at each dimension, the row
equations `eqn_app_dyn_ode_rows` (initial value `‖Δ_0ᵀ u_i‖² = rowQ`) have a solution on `[0, T⋆]`, it is unique
there, and for every mode solution `e` of `def_app_dyn_ode` the row solution is `𝔮_i = ∑_j 𝔮_ij`.
Deterministic, arbitrary coefficient data `c`, under `Σ_in = Id`.

Source (`section.tex`, whole environment):
```latex
\begin{corollary}[Half-anisotropic input]\label{cor:app-dyn-half}
Assume the hypotheses of \cref{thm:app-dyn-main} with $\Sigmain=\Id_{\Nin}$.
Let $\mathfrak d_i\defeq\mathfrak d(\mu_i,1)$ and let $\mathfrak v_i\defeq\mathfrak v_i(\ridge)$
be the row coefficient of \cref{eqn:app-vol-rows}. Then the row equations
\begin{equation}\label{eqn:app-dyn-ode-rows}
\frac{\dif}{\dif\macrotime}\big(B\fQ_i(\macrotime)\big)=-\frac{2\macrostep\,\mathfrak d_i}{\sqrt{\fRisk(\macrotime)}}\,B\fQ_i(\macrotime)+\macrostep^2\mathfrak v_i,\qquad
\fRisk(\macrotime)=\frac12\sum_i\mu_i\fQ_i(\macrotime),\qquad
\fQ_i(0)=\norm{\Delta_0^\T u_i}^2,
\end{equation}
have a unique solution on $[0,T_\star]$, given by $\fQ_i=\sum_j\fQ_{ij}$
with $(\fQ_{ij})$ the solution of \cref{eqn:app-dyn-ode}. The row measures
$\chi^{\mathrm{act}}_{\mathrm{row}}(\macrotime)\defeq\sum_i\CMscr Q_i(\lfloor B\macrotime\rfloor)\,\delta_{\mu_i}$
and $\chi^{\mathrm{ode}}_{\mathrm{row}}(\macrotime)\defeq\sum_i\fQ_i(\macrotime)\,\delta_{\mu_i}$
on $[0,C_\Sigma]$ satisfy
$\sup_{\macrotime\le T_\star}\norm{\chi^{\mathrm{act}}_{\mathrm{row}}(\macrotime)-\chi^{\mathrm{ode}}_{\mathrm{row}}(\macrotime)}_\BL\to0$
in probability, and the same holds for the measures weighted by $\mu$.
\end{corollary}
```
Row system (`eqn:app-dyn-ode-rows`):
```latex
\begin{equation}\label{eqn:app-dyn-ode-rows}
\frac{\dif}{\dif\macrotime}\big(B\fQ_i(\macrotime)\big)=-\frac{2\macrostep\,\mathfrak d_i}{\sqrt{\fRisk(\macrotime)}}\,B\fQ_i(\macrotime)+\macrostep^2\mathfrak v_i,\qquad
\fRisk(\macrotime)=\frac12\sum_i\mu_i\fQ_i(\macrotime),\qquad
\fQ_i(0)=\norm{\Delta_0^\T u_i}^2,
\end{equation}
```
-/
theorem cor_app_dyn_half_i (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C)) (hSin : ∀ k : ℕ, (F k).C.Sin = 1)
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k)) (k : ℕ) :
    (∃ q : ℝ → Fin (m k) → ℝ,
      eqn_app_dyn_ode_rows p.h ((B k : ℕ) : ℝ) (S k).μ (c k).d (rowCoef (c k)) (Tstar p)
        (fun i => rowQ (S k) (dev0 hyp k) i) q) ∧
    (∀ q q' : ℝ → Fin (m k) → ℝ,
      eqn_app_dyn_ode_rows p.h ((B k : ℕ) : ℝ) (S k).μ (c k).d (rowCoef (c k)) (Tstar p)
        (fun i => rowQ (S k) (dev0 hyp k) i) q →
      eqn_app_dyn_ode_rows p.h ((B k : ℕ) : ℝ) (S k).μ (c k).d (rowCoef (c k)) (Tstar p)
        (fun i => rowQ (S k) (dev0 hyp k) i) q' →
      EqOn q q' (Icc 0 (Tstar p))) ∧
    (∀ e : ℝ → Fin (m k) → Fin (n k) → ℝ, def_app_dyn_ode p (S k) (c k) (dev0 hyp k) (Tstar p) e →
      ∃ q : ℝ → Fin (m k) → ℝ,
        eqn_app_dyn_ode_rows p.h ((B k : ℕ) : ℝ) (S k).μ (c k).d (rowCoef (c k)) (Tstar p)
          (fun i => rowQ (S k) (dev0 hyp k) i) q ∧
        ∀ τ ∈ Icc 0 (Tstar p), ∀ i : Fin (m k), q τ i = (∑ j, e τ i j) / ((B k : ℕ) : ℝ) ^ 2) := by
  have hmode := prop_app_dyn_ode_i p (S k) (c k) (dev0 hyp k)
    (hyp.normBd k).2 (hyp.normBd k).1 (hyp.dims k) (hyp.W0_norm k)
    (hyp.W0_risk k).1 (hyp.W0_risk k).2
  obtain ⟨⟨e, he⟩, -, -⟩ := hmode
  have hB : ((B k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (F k).hB.ne'
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨fun τ i => (∑ j, e τ i j) / ((B k : ℕ) : ℝ) ^ 2,
      half_mode_to_row p (S k) (c k) (dev0 hyp k) (hSin k) (F k).hB e he⟩
  · intro q q' hq hq'
    exact half_row_unique p.h ((B k : ℕ) : ℝ) (S k).μ (c k).d
      (rowCoef (c k)) (Tstar p) (half_Tstar_nonneg p) hB
      (fun i => rowQ (S k) (dev0 hyp k) i) q q' hq hq'
  · intro e' he'
    refine ⟨fun τ i => (∑ j, e' τ i j) / ((B k : ℕ) : ℝ) ^ 2,
      half_mode_to_row p (S k) (c k) (dev0 hyp k) (hSin k) (F k).hB e' he', ?_⟩
    intro τ hτ i
    rfl

/-! ## `cor:app-dyn-continuum` -/

private lemma continuum_measure_compact_subseq
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (x0 : ℝ × ℝ) (hx0 : x0 ∈ K) (C : NNReal)
    (μ : ℕ → Measure (ℝ × ℝ)) (hfin : ∀ n, IsFiniteMeasure (μ n))
    (hmass : ∀ n, (show FiniteMeasure (ℝ × ℝ) from ⟨μ n, hfin n⟩).mass ≤ C)
    (hsupp : ∀ n, μ n Kᶜ = 0) :
    ∃ (ν : FiniteMeasure (ℝ × ℝ)) (ι : ℕ → ℕ), StrictMono ι ∧
      ν.mass ≤ C ∧ (ν : Measure (ℝ × ℝ)) Kᶜ = 0 ∧
      ∀ f : ℝ × ℝ → ℝ, ContinuousOn f K →
        Tendsto (fun n => ∫ x, f x ∂μ (ι n)) atTop
          (𝓝 (∫ x, f x ∂(ν : Measure (ℝ × ℝ)))) := by
  let μf : ℕ → FiniteMeasure (ℝ × ℝ) := fun n => ⟨μ n, hfin n⟩
  let pr : ℕ → ProbabilityMeasure (ℝ × ℝ) := fun n =>
    if (μf n).mass = 0 then ⟨Measure.dirac x0, Measure.dirac.isProbabilityMeasure⟩
    else (μf n).normalize
  have hrepr : ∀ n, μf n = (μf n).mass • (pr n).toFiniteMeasure := by
    intro n
    by_cases hz : (μf n).mass = 0
    · have hm0 : μf n = 0 := (FiniteMeasure.mass_zero_iff _).mp hz
      simp [hm0]
    · simpa [pr, hz] using (μf n).self_eq_mass_smul_normalize
  have hpr_supp : ∀ n, (pr n : Measure (ℝ × ℝ)) Kᶜ = 0 := by
    intro n
    by_cases hz : (μf n).mass = 0
    · simp [pr, hz, hx0]
    · rw [show pr n = (μf n).normalize by simp [pr, hz],
        (μf n).toMeasure_normalize_eq_of_nonzero ((μf n).mass_nonzero_iff.mp hz)]
      have hμf_supp : (μf n : Measure (ℝ × ℝ)) Kᶜ = 0 := by
        dsimp only [μf]
        exact hsupp n
      rw [Measure.coe_smul, Pi.smul_apply, Measure.nnreal_smul_coe_apply, hμf_supp, mul_zero]
  let KP : ℕ → Set (ℝ × ℝ) := fun _ => K
  let uz : ℕ → NNReal := fun _ => 0
  have hcpr := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
    (E := ℝ × ℝ) (K := KP) (u := uz) tendsto_const_nhds (fun _ => hK) (Or.inr monotone_const)
  have hcmass : IsCompact (Icc (0 : NNReal) C) := isCompact_Icc
  have hcpair := hcmass.prod hcpr
  obtain ⟨z, hz, ι, hι, hlim⟩ := hcpair.tendsto_subseq
    (x := fun n => ((μf n).mass, pr n)) (fun n => ⟨⟨zero_le, hmass n⟩, by
      intro j
      dsimp only [KP, uz]
      simpa using hpr_supp n⟩)
  let ν : FiniteMeasure (ℝ × ℝ) := z.1 • z.2.toFiniteMeasure
  have hνmass : ν.mass ≤ C := by
    dsimp only [ν]
    have heq : (z.1 • z.2.toFiniteMeasure).mass = z.1 := by
      apply ENNReal.coe_injective
      rw [FiniteMeasure.ennreal_mass]
      simp
    rw [heq]
    exact hz.1.2
  have hνsupp : (ν : Measure (ℝ × ℝ)) Kᶜ = 0 := by
    rw [show (ν : Measure (ℝ × ℝ)) = z.1 • (z.2.toFiniteMeasure : Measure (ℝ × ℝ)) by
      simp [ν]]
    simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply]
    change (z.1 : ENNReal) * (z.2 : Measure (ℝ × ℝ)) Kᶜ = 0
    rw [show (z.2 : Measure (ℝ × ℝ)) Kᶜ = 0 by simpa [KP, uz] using hz.2 0]
    simp
  refine ⟨ν, ι, hι, hνmass, hνsupp, ?_⟩
  intro f hf
  letI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  let fk : BoundedContinuousFunction ↥K ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => f x, continuousOn_iff_continuous_restrict.mp hf⟩
  obtain ⟨g, -, hg⟩ := fk.exists_extension_norm_eq_of_isClosedEmbedding
    (IsCompact.isClosed hK).isClosedEmbedding_subtypeVal
  have hpair : Tendsto (fun n => ((μf (ι n)).mass, pr (ι n))) atTop (𝓝 z) := by
    simpa [Function.comp_def] using hlim
  have hm_lim : Tendsto (fun n => ((μf (ι n)).mass : ℝ)) atTop (𝓝 (z.1 : ℝ)) :=
    (NNReal.continuous_coe.tendsto z.1).comp ((continuous_fst.tendsto z).comp hpair)
  have hp_lim : Tendsto (fun n => pr (ι n)) atTop (𝓝 z.2) :=
    (continuous_snd.tendsto z).comp hpair
  have hp_int := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hp_lim g
  have ht := hm_lim.mul hp_int
  have haeμ : ∀ n, ∀ᵐ x ∂μ (ι n), x ∈ K := fun n => ae_iff.mpr (hsupp (ι n))
  have haeν : ∀ᵐ x ∂(ν : Measure (ℝ × ℝ)), x ∈ K := ae_iff.mpr hνsupp
  have hseq : (fun n => ∫ x, f x ∂μ (ι n)) =
      fun n => ((μf (ι n)).mass : ℝ) * ∫ x, g x ∂(pr (ι n) : Measure (ℝ × ℝ)) := by
    funext n
    calc
      ∫ x, f x ∂μ (ι n) = ∫ x, g x ∂μ (ι n) := by
        apply integral_congr_ae
        filter_upwards [haeμ n] with x hx
        exact (congrFun hg ⟨x, hx⟩).symm
      _ = ((μf (ι n)).mass : ℝ) * ∫ x, g x ∂(pr (ι n) : Measure (ℝ × ℝ)) := by
        rw [show μ (ι n) = (μf (ι n) : Measure (ℝ × ℝ)) by rfl]
        have hm := congrArg (fun q : FiniteMeasure (ℝ × ℝ) => (q : Measure (ℝ × ℝ)))
          (hrepr (ι n))
        rw [hm]
        change ∫ x, g x ∂(((μf (ι n)).mass : ENNReal) •
          (pr (ι n) : Measure (ℝ × ℝ))) = _
        rw [integral_smul_measure]
        change (((μf (ι n)).mass : ENNReal).toReal) * _ = ((μf (ι n)).mass : ℝ) * _
        rw [ENNReal.coe_toReal]
  have hlimit : ∫ x, f x ∂(ν : Measure (ℝ × ℝ)) =
      (z.1 : ℝ) * ∫ x, g x ∂(z.2 : Measure (ℝ × ℝ)) := by
    calc
      ∫ x, f x ∂(ν : Measure (ℝ × ℝ)) = ∫ x, g x ∂(ν : Measure (ℝ × ℝ)) := by
        apply integral_congr_ae
        filter_upwards [haeν] with x hx
        exact (congrFun hg ⟨x, hx⟩).symm
      _ = (z.1 : ℝ) * ∫ x, g x ∂(z.2 : Measure (ℝ × ℝ)) := by
        rw [show (ν : Measure (ℝ × ℝ)) = (z.1 : ENNReal) •
          (z.2 : Measure (ℝ × ℝ)) by simp [ν]]
        rw [integral_smul_measure]
        change ((z.1 : ENNReal).toReal) * _ = (z.1 : ℝ) * _
        rw [ENNReal.coe_toReal]
  rw [hseq, hlimit]
  exact ht

private lemma continuum_local_lip_cont {Cs L : ℝ} {g : ℝ × ℝ → ℝ} (hL : 0 ≤ L)
    (hl : ∀ x ∈ specRect Cs, ∀ y ∈ specRect Cs, |g x - g y| ≤ L * l1 x y) :
    ContinuousOn g (specRect Cs) := by
  have h : LipschitzOnWith ⟨2 * L, by positivity⟩ g (specRect Cs) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Real.dist_eq]
    have hd : l1 x y ≤ 2 * dist x y := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      unfold l1
      linarith [le_max_left |x.1 - y.1| |x.2 - y.2|,
        le_max_right |x.1 - y.1| |x.2 - y.2|]
    exact (hl x hx y hy).trans (by
      change L * l1 x y ≤ (2 * L) * dist x y
      nlinarith [mul_le_mul_of_nonneg_left hd hL])
  exact h.continuousOn

private lemma continuum_drift_compact_subseq (p : DynParams) (d : ℕ → ℝ × ℝ → ℝ)
    (hd0 : ∀ n x, x ∈ specRect p.CSig → 0 ≤ d n x)
    (hd1 : ∀ n x, x ∈ specRect p.CSig → d n x ≤ dMax p)
    (hdlip : ∀ n x, x ∈ specRect p.CSig → ∀ y, y ∈ specRect p.CSig →
      |d n x - d n y| ≤ p.CSig / Real.sqrt (2 * p.ϱ) * l1 x y) :
    ∃ (dinf : ℝ × ℝ → ℝ) (ι : ℕ → ℕ), StrictMono ι ∧
      TendstoUniformlyOn (fun n => d (ι n)) dinf atTop (specRect p.CSig) := by
  classical
  let K := specRect p.CSig
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  letI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  let L : ℝ := p.CSig / Real.sqrt (2 * p.ϱ)
  have hL : 0 ≤ L := div_nonneg (by linarith [p.hC]) (Real.sqrt_nonneg _)
  let df : ℕ → BoundedContinuousFunction ↥K ℝ := fun n =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x => d n x, continuousOn_iff_continuous_restrict.mp
        (continuum_local_lip_cont hL (hdlip n))⟩
  let A : Set (BoundedContinuousFunction ↥K ℝ) := range df
  have hAc : IsCompact (closure A) := by
    apply BoundedContinuousFunction.arzela_ascoli (Icc (0 : ℝ) (dMax p)) isCompact_Icc A
    · rintro f x ⟨n, rfl⟩
      exact ⟨hd0 n x x.2, hd1 n x x.2⟩
    · apply Metric.equicontinuous_of_continuity_modulus (fun t => (2 * L) * t)
        (by
          have hc : Continuous (fun t : ℝ => (2 * L) * t) := continuous_const.mul continuous_id
          simpa using hc.tendsto 0)
      intro x y q
      obtain ⟨n, hn⟩ := q.2
      rw [← hn, Real.dist_eq]
      have hxy : l1 x y ≤ 2 * dist x y := by
        change l1 x.1 y.1 ≤ 2 * dist x.1 y.1
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        unfold l1
        linarith [le_max_left |x.1.1 - y.1.1| |x.1.2 - y.1.2|,
          le_max_right |x.1.1 - y.1.1| |x.1.2 - y.1.2|]
      exact (hdlip n x x.2 y y.2).trans (by
        change L * l1 x y ≤ (2 * L) * dist x y
        nlinarith [mul_le_mul_of_nonneg_left hxy hL])
  obtain ⟨g, -, ι, hι, hlim⟩ := hAc.tendsto_subseq
    (x := df) (fun n => subset_closure ⟨n, rfl⟩)
  let dinf : ℝ × ℝ → ℝ := fun x => if hx : x ∈ K then g ⟨x, hx⟩ else 0
  refine ⟨dinf, ι, hι, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.1 hlim ε hε)] with n hn x hx
  have hp := BoundedContinuousFunction.dist_coe_le_dist (f := df (ι n)) (g := g) ⟨x, hx⟩
  change dist (dinf x) (d (ι n) x) < ε
  rw [show dinf x = g ⟨x, hx⟩ by dsimp only [dinf]; rw [dif_pos hx]]
  calc
    dist (g ⟨x, hx⟩) (d (ι n) x) ≤ dist (df (ι n)) g := by
      change dist (d (ι n) x) (g ⟨x, hx⟩) ≤ dist (df (ι n)) g at hp
      rw [dist_comm (g ⟨x, hx⟩) (d (ι n) x)]
      exact hp
    _ < ε := by simpa [Function.comp_def] using hn

private lemma continuum_atom_isFinite {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (q : Fin m → Fin n → ℝ) : IsFiniteMeasure (atomMeasure μ lam q) := by
  constructor
  unfold atomMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.2 fun i _ =>
    ENNReal.sum_lt_top.2 fun j _ => ENNReal.ofReal_lt_top

private lemma continuum_atom_mass {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (q : Fin m → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j) :
    (atomMeasure μ lam q).real univ = ∑ i, ∑ j, q i j := by
  unfold atomMeasure
  rw [Measure.real_def]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.sum_ne_top.mpr fun j _ => ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.toReal_sum (fun j _ => ENNReal.ofReal_ne_top)]
  exact Finset.sum_congr rfl fun j _ => ENNReal.toReal_ofReal (hq i j)

private lemma continuum_fro_sq {m n : ℕ} (K : Mat m n) :
    fro K ^ 2 = ∑ i, ∑ j, K i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma continuum_modeQ_sum {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (Δ : Mat m n) : ∑ i, ∑ j, modeQ S Δ i j = fro Δ ^ 2 := by
  have ht : ∀ {a b : ℕ} (Y : Mat a b), (Y * Matrix.transpose Y).trace = fro Y ^ 2 := by
    intro a b Y
    rw [continuum_fro_sq]
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_two]
  have he : fro (Matrix.transpose S.uOut * Δ * S.vIn) ^ 2 = fro Δ ^ 2 := by
    rw [← ht, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S.vIn (Matrix.transpose S.vIn), mul_eq_one_comm.mp S.hvIn,
      Matrix.one_mul]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
    rw [mul_eq_one_comm.mp S.huOut, Matrix.mul_one, ht]
  rw [← he, continuum_fro_sq]
  simp_rw [P_apply, modeQ]

private lemma continuum_abs_eig_le_opNorm {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (w : Fin k → ℝ) (μ : ℝ) (hw : ∑ a, w a * w a = 1) (he : Matrix.mulVec A w = μ • w) :
    |μ| ≤ opNorm A := by
  set x : EuclideanSpace ℝ (Fin k) := (EuclideanSpace.equiv (Fin k) ℝ).symm w with hxdef
  have hsum : ∑ a, ‖x a‖ ^ 2 = 1 := by
    have hterm : ∀ a, ‖x a‖ ^ 2 = w a * w a := fun a => by
      rw [Real.norm_eq_abs, sq_abs, sq]
      rfl
    simp only [hterm]
    exact hw
  have hx : ‖x‖ = 1 := by rw [EuclideanSpace.norm_eq, hsum, Real.sqrt_one]
  have h1 := Matrix.l2_opNorm_mulVec A x
  have h2 : (EuclideanSpace.equiv (Fin k) ℝ).symm (Matrix.mulVec A ⇑x) = μ • x := by
    ext a
    have ha := congrFun he a
    simp only [hxdef, Pi.smul_apply, smul_eq_mul] at ha ⊢
    exact ha
  rw [h2, norm_smul, hx, Real.norm_eq_abs] at h1
  simp only [mul_one] at h1
  rw [opNorm_eq_norm]
  exact h1

private lemma continuum_atom_support {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (q : Fin m → Fin n → ℝ) (Cs : ℝ) (hout : opNorm C.Sout ≤ Cs)
    (hin : opNorm C.Sin ≤ Cs) : atomMeasure S.μ S.lam q (specRect Cs)ᶜ = 0 := by
  have hμ : ∀ i, S.μ i ∈ Icc (0 : ℝ) Cs := fun i => ⟨μ_nonneg S i, by
    exact (le_abs_self _).trans ((continuum_abs_eig_le_opNorm C.Sout (fun a => S.uOut a i) (S.μ i)
      (sum_col_sq_eq_one S.uOut S.huOut i) (S.eigOut i)).trans hout)⟩
  have hlam : ∀ j, S.lam j ∈ Icc (0 : ℝ) Cs := fun j => ⟨lam_nonneg S j, by
    exact (le_abs_self _).trans ((continuum_abs_eig_le_opNorm C.Sin (fun a => S.vIn a j) (S.lam j)
      (sum_col_sq_eq_one S.vIn S.hvIn j) (S.eigIn j)).trans hin)⟩
  have hc : MeasurableSet (specRect Cs)ᶜ := (measurableSet_Icc.prod measurableSet_Icc).compl
  unfold atomMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [Measure.dirac_apply' _ hc, Set.indicator_of_notMem]
  · simp
  · exact fun h => h ⟨hμ i, hlam j⟩

private lemma continuum_spec_mass {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (Δ : Mat m n) : (specMeasure S Δ).real univ = fro Δ ^ 2 := by
  rw [show specMeasure S Δ = atomMeasure S.μ S.lam (modeQ S Δ) by rfl,
    continuum_atom_mass S.μ S.lam (modeQ S Δ) (fun i j => sq_nonneg _), continuum_modeQ_sum]

private lemma continuum_mass_le_toNNReal (μ : Measure (ℝ × ℝ)) (hfin : IsFiniteMeasure μ)
    (C : ℝ) (hC : 0 ≤ C) (h : μ.real univ ≤ C) :
    (show FiniteMeasure (ℝ × ℝ) from ⟨μ, hfin⟩).mass ≤ Real.toNNReal C := by
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ hC]
  change (μ univ).toReal ≤ C
  simpa [Measure.real_def] using h

private lemma continuum_uniform_subseq {α : Type*} [UniformSpace α]
    {F : ℕ → (ℝ × ℝ → α)} {f : ℝ × ℝ → α} {K : Set (ℝ × ℝ)}
    (h : TendstoUniformlyOn F f atTop K) (ι : ℕ → ℕ) (hι : StrictMono ι) :
    TendstoUniformlyOn (fun n => F (ι n)) f atTop K := by
  intro u hu
  exact hι.tendsto_atTop.eventually (h u hu)

/-- `cor:app-dyn-continuum`(i), snapshot `cr-2026-10-23`. Every sequence of dimensions has a subsequence along
which `𝔡_B → 𝔡_∞` uniformly on `K`, `ζ_B → ζ_∞` weakly and `χ^act_B(0) → χ_0` weakly (`contLimit`).
Deterministic in the limit data; no identification needed.

Source (`section.tex`, whole environment):
```latex
\begin{corollary}[Continuum equation]\label{cor:app-dyn-continuum}
Assume the hypotheses of \cref{thm:app-dyn-main}, and write $\mathfrak d_B$,
$\zeta_B$, $\chi^{\mathrm{act}}_B$, $\chi^{\mathrm{ode}}_B$ for the objects
at the dimension indexed by $B$.
\begin{enumerate}[label=(\roman*)]
\item Every sequence of dimensions has a subsequence along which $\mathfrak d_B\to\mathfrak d_\infty$
uniformly on $\mathbb K$, $\zeta_B\to\zeta_\infty$ weakly and
$\chi^{\mathrm{act}}_B(0)\to\chi_0$ weakly.
\item Along any such subsequence, the measure equation
\begin{equation}\label{eqn:app-dyn-continuum}
\chi(\macrotime)=\chi_0+\int_0^\macrotime\Big(-\frac{2\macrostep\,\mathfrak d_\infty\,\chi(\sigma)}{\sqrt{\fRisk(\chi(\sigma))}}+\macrostep^2\zeta_\infty\Big)\dif\sigma
\end{equation}
has a unique solution $\chi$ on $[0,T_\star]$ among paths with values in
$\mathfrak M$ that are continuous for the bounded-Lipschitz norm, and
\[
\sup_{\macrotime\le T_\star}\norm{\chi^{\mathrm{ode}}_B(\macrotime)-\chi(\macrotime)}_\BL\to0,\qquad
\sup_{\macrotime\le T_\star}\norm{\chi^{\mathrm{act}}_B(\macrotime)-\chi(\macrotime)}_\BL\to0\ \text{in probability}.
\]
\item Along any such subsequence,
$\sup_{\macrotime\le T_\star}\abs{\cR(\lfloor B\macrotime\rfloor)-\fRisk(\chi(\macrotime))}\to0$ in probability.
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_dyn_continuum_i (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C)) (hB : Tendsto B atTop atTop)
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k)) :
    ∀ κ : ℕ → ℕ, StrictMono κ → ∃ ι : ℕ → ℕ, StrictMono ι ∧
      ∃ (dinf : ℝ × ℝ → ℝ) (ζinf χ0 : Measure (ℝ × ℝ)),
        contLimit hyp S c (fun n => κ (ι n)) dinf ζinf χ0 := by
  intro κ hκ
  obtain ⟨dinf, ιd, hιd, hd⟩ := continuum_drift_compact_subseq p
    (fun n => (c (κ n)).d)
    (fun n => (c (κ n)).d_nonneg) (fun n => (c (κ n)).d_le)
    (fun n => (c (κ n)).d_lip)
  have hK : IsCompact (specRect p.CSig) := isCompact_Icc.prod isCompact_Icc
  have hx0 : ((0, 0) : ℝ × ℝ) ∈ specRect p.CSig := by
    exact ⟨⟨le_rfl, by linarith [p.hC]⟩, ⟨le_rfl, by linarith [p.hC]⟩⟩
  let ζseq : ℕ → Measure (ℝ × ℝ) := fun n => (c (κ (ιd n))).ζ
  have hζfin : ∀ n, IsFiniteMeasure (ζseq n) := by
    intro n
    rw [show ζseq n = (c (κ (ιd n))).ζ by rfl, (c (κ (ιd n))).ζ_eq]
    exact continuum_atom_isFinite _ _ _
  have hζmass : ∀ n,
      (show FiniteMeasure (ℝ × ℝ) from ⟨ζseq n, hζfin n⟩).mass ≤
        Real.toNNReal (mZeta p) := by
    intro n
    exact continuum_mass_le_toNNReal (ζseq n) (hζfin n) (mZeta p)
      (half_mZeta_nonneg p) (by simpa [ζseq] using (c (κ (ιd n))).ζ_mass)
  have hζsupp : ∀ n, ζseq n (specRect p.CSig)ᶜ = 0 := by
    intro n
    rw [show ζseq n = (c (κ (ιd n))).ζ by rfl, (c (κ (ιd n))).ζ_eq]
    exact continuum_atom_support (S (κ (ιd n))) _ p.CSig
      (hyp.normBd (κ (ιd n))).2 (hyp.normBd (κ (ιd n))).1
  obtain ⟨ζlim, ιζ, hιζ, -, hζlim_supp, hζlim⟩ :=
    continuum_measure_compact_subseq (specRect p.CSig) hK (0, 0) hx0
      (Real.toNNReal (mZeta p)) ζseq hζfin hζmass hζsupp
  let χseq : ℕ → Measure (ℝ × ℝ) := fun n =>
    specMeasure (S (κ (ιd (ιζ n)))) (dev0 hyp (κ (ιd (ιζ n))))
  have hχfin : ∀ n, IsFiniteMeasure (χseq n) := by
    intro n
    unfold χseq specMeasure
    exact continuum_atom_isFinite _ _ _
  have hχmass : ∀ n,
      (show FiniteMeasure (ℝ × ℝ) from ⟨χseq n, hχfin n⟩).mass ≤
        Real.toNNReal p.Estar := by
    intro n
    apply continuum_mass_le_toNNReal (χseq n) (hχfin n) p.Estar p.hE
    rw [show χseq n = specMeasure (S (κ (ιd (ιζ n))))
      (dev0 hyp (κ (ιd (ιζ n)))) by rfl, continuum_spec_mass]
    exact hyp.W0_norm (κ (ιd (ιζ n)))
  have hχsupp : ∀ n, χseq n (specRect p.CSig)ᶜ = 0 := by
    intro n
    unfold χseq specMeasure
    exact continuum_atom_support (S (κ (ιd (ιζ n)))) _ p.CSig
      (hyp.normBd (κ (ιd (ιζ n)))).2 (hyp.normBd (κ (ιd (ιζ n)))).1
  obtain ⟨χlim, ιχ, hιχ, -, hχlim_supp, hχlim⟩ :=
    continuum_measure_compact_subseq (specRect p.CSig) hK (0, 0) hx0
      (Real.toNNReal p.Estar) χseq hχfin hχmass hχsupp
  refine ⟨fun n => ιd (ιζ (ιχ n)), hιd.comp (hιζ.comp hιχ), dinf,
    (ζlim : Measure (ℝ × ℝ)), (χlim : Measure (ℝ × ℝ)), ?_⟩
  refine ⟨?_, ⟨inferInstance, hζlim_supp, ?_⟩, ⟨inferInstance, hχlim_supp, ?_⟩⟩
  · exact continuum_uniform_subseq hd (fun n => ιζ (ιχ n)) (hιζ.comp hιχ)
  · intro f hf
    exact (hζlim f hf).comp hιχ.tendsto_atTop
  · intro f hf
    exact hχlim f hf

private lemma continuum_limit_d_bounds
    (S : ∀ k : ℕ, SpectralData (C k)) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hyp : DynHyp p P m n B C)
    (ι : ℕ → ℕ) (dinf : ℝ × ℝ → ℝ) (ζinf χ0 : Measure (ℝ × ℝ))
    (hL : contLimit hyp S c ι dinf ζinf χ0) :
    ∀ x ∈ specRect p.CSig, 0 ≤ dinf x ∧ dinf x ≤ dMax p := by
  intro x hx
  have hd : Tendsto (fun n => (c (ι n)).d x) atTop (nhds (dinf x)) :=
    hL.1.tendsto_at hx
  constructor
  · exact isClosed_Ici.mem_of_tendsto hd (Eventually.of_forall fun n => (c (ι n)).d_nonneg x hx)
  · exact isClosed_Iic.mem_of_tendsto hd (Eventually.of_forall fun n => (c (ι n)).d_le x hx)

private lemma continuum_limit_d_lipschitz
    (S : ∀ k : ℕ, SpectralData (C k)) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hyp : DynHyp p P m n B C) (ι : ℕ → ℕ) (dinf : ℝ × ℝ → ℝ)
    (ζinf χ0 : Measure (ℝ × ℝ)) (hL : contLimit hyp S c ι dinf ζinf χ0) :
    ∀ x ∈ specRect p.CSig, ∀ y ∈ specRect p.CSig,
      |dinf x - dinf y| ≤ p.CSig / Real.sqrt (2 * p.ϱ) * l1 x y := by
  intro x hx y hy
  have hdx : Tendsto (fun n => (c (ι n)).d x) atTop (nhds (dinf x)) :=
    hL.1.tendsto_at hx
  have hdy : Tendsto (fun n => (c (ι n)).d y) atTop (nhds (dinf y)) :=
    hL.1.tendsto_at hy
  have hd := (hdx.sub hdy).abs
  exact isClosed_Iic.mem_of_tendsto hd (Eventually.of_forall fun n =>
    (c (ι n)).d_lip x hx y hy)

private lemma continuum_limit_d_continuousOn
    (S : ∀ k : ℕ, SpectralData (C k)) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hyp : DynHyp p P m n B C) (ι : ℕ → ℕ) (dinf : ℝ × ℝ → ℝ)
    (ζinf χ0 : Measure (ℝ × ℝ)) (hL : contLimit hyp S c ι dinf ζinf χ0) :
    ContinuousOn dinf (specRect p.CSig) := by
  apply continuum_local_lip_cont
    (div_nonneg (by linarith [p.hC]) (Real.sqrt_nonneg _))
  exact continuum_limit_d_lipschitz S c hyp ι dinf ζinf χ0 hL

private lemma continuum_limit_zeta_mass
    (S : ∀ k : ℕ, SpectralData (C k)) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hyp : DynHyp p P m n B C) (ι : ℕ → ℕ) (dinf : ℝ × ℝ → ℝ)
    (ζinf χ0 : Measure (ℝ × ℝ)) (hL : contLimit hyp S c ι dinf ζinf χ0) :
    ζinf.real univ ≤ mZeta p := by
  have ht := hL.2.1.2.2 (fun _ => (1 : ℝ)) continuousOn_const
  have ht' : Tendsto (fun n => (c (ι n)).ζ.real univ) atTop
      (nhds (ζinf.real univ)) := by
    simpa only [integral_const, measureReal_def, smul_eq_mul, mul_one] using ht
  exact isClosed_Iic.mem_of_tendsto ht'
    (Eventually.of_forall fun n => (c (ι n)).ζ_mass)

private lemma continuum_atom_integral {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (q : Fin m → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j) (f : ℝ × ℝ → ℝ) :
    ∫ x, f x ∂(atomMeasure μ lam q) = ∑ i, ∑ j, q i j * f (μ i, lam j) := by
  have hint : ∀ i j, Integrable f (ENNReal.ofReal (q i j) • Measure.dirac (μ i, lam j)) :=
    fun i j => (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  unfold atomMeasure
  rw [integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.2 (fun j _ => hint i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum_measure (fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hq i j), smul_eq_mul]

private lemma continuum_spec_risk {m n : ℕ} {C : Covariances m n}
    (S : SpectralData C) (Δ : Mat m n) :
    riskOf (specMeasure S Δ) = riskSigma C Δ := by
  unfold riskOf specMeasure riskSigma
  rw [continuum_atom_integral S.μ S.lam (modeQ S Δ) (fun i j => sq_nonneg _)]
  have hsum : ∑ i, ∑ j, modeQ S Δ i j * (S.μ i * S.lam j) =
      ∑ i, ∑ j, S.μ i * S.lam j * modeQ S Δ i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum, ← lem_app_setup_decomposition_ii S Δ]
  ring

private lemma continuum_limit_initial_adm
    (S : ∀ k : ℕ, SpectralData (C k)) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hyp : DynHyp p P m n B C) (ι : ℕ → ℕ) (dinf : ℝ × ℝ → ℝ)
    (ζinf χ0 : Measure (ℝ × ℝ)) (hL : contLimit hyp S c ι dinf ζinf χ0) :
    χ0 ∈ admMeasures p := by
  have hmass0 := hL.2.2.2.2 (fun _ => (1 : ℝ)) continuousOn_const
  have hmass : Tendsto
      (fun n => (specMeasure (S (ι n)) (dev0 hyp (ι n))).real univ) atTop
      (nhds (χ0.real univ)) := by
    simpa only [integral_const, measureReal_def, smul_eq_mul, mul_one] using hmass0
  have hmass_le : χ0.real univ ≤ p.Estar := by
    apply isClosed_Iic.mem_of_tendsto hmass
    exact Eventually.of_forall fun n => by
      rw [continuum_spec_mass]
      exact hyp.W0_norm (ι n)
  have hrisk0 := hL.2.2.2.2 (fun x => x.1 * x.2) (by fun_prop)
  have hrisk : Tendsto
      (fun n => riskOf (specMeasure (S (ι n)) (dev0 hyp (ι n)))) atTop
      (nhds (riskOf χ0)) := by
    simpa only [riskOf] using hrisk0.const_mul (1 / 2)
  have hrlo : p.r0 ≤ riskOf χ0 := by
    apply isClosed_Ici.mem_of_tendsto hrisk
    exact Eventually.of_forall fun n => by
      rw [continuum_spec_risk]
      exact (hyp.W0_risk (ι n)).1
  have hrhi : riskOf χ0 ≤ p.r1 := by
    apply isClosed_Iic.mem_of_tendsto hrisk
    exact Eventually.of_forall fun n => by
      rw [continuum_spec_risk]
      exact (hyp.W0_risk (ι n)).2
  refine ⟨hL.2.2.1, hL.2.2.2.1, ?_, ?_, ?_⟩
  · linarith
  · linarith [p.hr0]
  · linarith

private lemma continuum_ae_K {Cs : ℝ} {χ : Measure (ℝ × ℝ)} (hK : χ (specRect Cs)ᶜ = 0) :
    ∀ᵐ x ∂χ, x ∈ specRect Cs := by
  rw [ae_iff]
  exact hK

private lemma continuum_K_meas (Cs : ℝ) : MeasurableSet (specRect Cs) :=
  measurableSet_Icc.prod measurableSet_Icc

private lemma continuum_integrable_K {Cs M : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (specRect Cs)) (hb : ∀ x ∈ specRect Cs, |f x| ≤ M)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (hμ : μ (specRect Cs)ᶜ = 0) :
    Integrable f μ := by
  have hres : μ.restrict (specRect Cs) = μ :=
    Measure.restrict_eq_self_of_ae_mem (continuum_ae_K hμ)
  have hm : AEStronglyMeasurable f μ := by
    rw [← hres]
    exact hf.aestronglyMeasurable (continuum_K_meas Cs)
  refine Integrable.of_bound hm M ?_
  filter_upwards [continuum_ae_K hμ] with x hx
  rw [Real.norm_eq_abs]
  exact hb x hx

/-- Every bounded-Lipschitz test function agrees on `K` with a continuous one, globally bounded by `1`,
still in the test class. -/
private lemma continuum_test_ext {Cs : ℝ} (hCs : 0 ≤ Cs) (φ : ℝ × ℝ → ℝ) (hφ : φ ∈ blTest Cs) :
    ∃ ψ : ℝ × ℝ → ℝ, Continuous ψ ∧ (∀ x, |ψ x| ≤ 1) ∧ ψ ∈ blTest Cs ∧
      ∀ x ∈ specRect Cs, ψ x = φ x := by
  let pr : ℝ × ℝ → ℝ × ℝ := fun x => ((projIcc 0 Cs hCs x.1 : ℝ), (projIcc 0 Cs hCs x.2 : ℝ))
  have hpr : ∀ x, pr x ∈ specRect Cs := fun x =>
    ⟨(projIcc 0 Cs hCs x.1).2, (projIcc 0 Cs hCs x.2).2⟩
  have hprc : Continuous pr :=
    (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
  have hprK : ∀ x ∈ specRect Cs, pr x = x := by
    intro x hx
    simp only [pr, projIcc_of_mem hCs hx.1, projIcc_of_mem hCs hx.2]
  have hφc : ContinuousOn φ (specRect Cs) :=
    continuum_local_lip_cont zero_le_one (fun x hx y hy => by
      simpa only [one_mul] using hφ.2 x hx y hy)
  refine ⟨fun x => φ (pr x), hφc.comp_continuous hprc hpr, fun x => hφ.1 _ (hpr x), ?_, ?_⟩
  · refine ⟨fun x hx => by simp only [hprK x hx]; exact hφ.1 x hx, fun x hx y hy => ?_⟩
    simp only [hprK x hx, hprK y hy]
    exact hφ.2 x hx y hy
  · intro x hx
    simp only [hprK x hx]

private lemma continuum_integral_congr_K {Cs : ℝ} {f g : ℝ × ℝ → ℝ}
    (hfg : ∀ x ∈ specRect Cs, f x = g x) (μ : Measure (ℝ × ℝ)) (hμ : μ (specRect Cs)ᶜ = 0) :
    ∫ x, f x ∂μ = ∫ x, g x ∂μ :=
  integral_congr_ae ((continuum_ae_K hμ).mono fun x hx => hfg x hx)

private lemma continuum_test_abs_le {Cs : ℝ} (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hμ : μ (specRect Cs)ᶜ = 0) (φ : ℝ × ℝ → ℝ) (hφ : ∀ x ∈ specRect Cs, |φ x| ≤ 1) :
    |∫ x, φ x ∂μ| ≤ μ.real univ := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := φ) (C := 1)
    ((continuum_ae_K hμ).mono fun x hx => by rw [Real.norm_eq_abs]; exact hφ x hx)
  simpa only [Real.norm_eq_abs, one_mul] using h

private lemma continuum_bl_bdd {Cs : ℝ} (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0) :
    BddAbove ((fun φ => |∫ x, φ x ∂μ - ∫ x, φ x ∂ν|) '' blTest Cs) := by
  refine ⟨μ.real univ + ν.real univ, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  exact (abs_sub _ _).trans (add_le_add (continuum_test_abs_le μ hμ φ hφ.1)
    (continuum_test_abs_le ν hν φ hφ.1))

private lemma continuum_bl_le {Cs : ℝ} (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0)
    (φ : ℝ × ℝ → ℝ) (hφ : φ ∈ blTest Cs) :
    |∫ x, φ x ∂μ - ∫ x, φ x ∂ν| ≤ blDist Cs μ ν :=
  le_csSup (continuum_bl_bdd μ ν hμ hν) ⟨φ, hφ, rfl⟩

private lemma continuum_bl_nonneg (Cs : ℝ) (μ ν : Measure (ℝ × ℝ)) : 0 ≤ blDist Cs μ ν := by
  unfold blDist blNorm
  exact Real.sSup_nonneg (by rintro _ ⟨φ, _, rfl⟩; exact abs_nonneg _)

private lemma continuum_bl_le_of {Cs A : ℝ} (μ ν : Measure (ℝ × ℝ)) (hA : 0 ≤ A)
    (h : ∀ φ ∈ blTest Cs, |∫ x, φ x ∂μ - ∫ x, φ x ∂ν| ≤ A) : blDist Cs μ ν ≤ A := by
  unfold blDist blNorm
  exact Real.sSup_le (by rintro _ ⟨φ, hφ, rfl⟩; exact h φ hφ) hA

private lemma continuum_bl_le_mass {Cs : ℝ} (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμ : μ (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0) :
    blDist Cs μ ν ≤ μ.real univ + ν.real univ :=
  continuum_bl_le_of μ ν (add_nonneg measureReal_nonneg measureReal_nonneg) fun φ hφ =>
    (abs_sub _ _).trans (add_le_add (continuum_test_abs_le μ hμ φ hφ.1)
      (continuum_test_abs_le ν hν φ hφ.1))

/-- Two finite measures with the same integrals on the bounded-Lipschitz class are equal. -/
private lemma continuum_ext_of_bl {Cs : ℝ} (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ∀ φ ∈ blTest Cs, ∫ x, φ x ∂μ = ∫ x, φ x ∂ν) : μ = ν := by
  have hthick : ∀ (δ : ℝ) (hδ : 0 < δ) (F : Set (ℝ × ℝ)),
      ∫ x, (thickenedIndicator hδ F x : ℝ) ∂μ = ∫ x, (thickenedIndicator hδ F x : ℝ) ∂ν := by
    intro δ hδ F
    set s : ℝ := min 1 δ with hs
    have hs0 : 0 < s := lt_min one_pos hδ
    have hs1 : s ≤ 1 := min_le_left _ _
    have hsδ : s ≤ δ := min_le_right _ _
    have hlip := lipschitzWith_thickenedIndicator hδ F
    have hmem : (fun x => s * (thickenedIndicator hδ F x : ℝ)) ∈ blTest Cs := by
      refine ⟨fun x _ => ?_, fun x _ y _ => ?_⟩
      · have h1 : (thickenedIndicator hδ F x : ℝ) ≤ 1 := by
          exact_mod_cast thickenedIndicator_le_one hδ F x
        have h0 : (0 : ℝ) ≤ thickenedIndicator hδ F x := NNReal.coe_nonneg _
        rw [abs_of_nonneg (mul_nonneg hs0.le h0)]
        nlinarith
      · have hd := hlip.dist_le_mul x y
        rw [NNReal.dist_eq] at hd
        have hc : ((δ.toNNReal⁻¹ : NNReal) : ℝ) = 1 / δ := by
          rw [NNReal.coe_inv, Real.coe_toNNReal _ hδ.le, one_div]
        rw [hc] at hd
        have hl1 : dist x y ≤ l1 x y := by
          rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
          unfold l1
          exact max_le (by linarith [abs_nonneg (x.2 - y.2)])
            (by linarith [abs_nonneg (x.1 - y.1)])
        rw [← mul_sub, abs_mul, abs_of_pos hs0]
        calc s * |(thickenedIndicator hδ F x : ℝ) - thickenedIndicator hδ F y|
            ≤ s * (1 / δ * dist x y) := mul_le_mul_of_nonneg_left hd hs0.le
          _ ≤ dist x y := by
            rw [← mul_assoc]
            have : s * (1 / δ) ≤ 1 := by
              rw [mul_one_div]; exact (div_le_one hδ).2 hsδ
            nlinarith [dist_nonneg (x := x) (y := y)]
          _ ≤ l1 x y := hl1
    have := h _ hmem
    rw [integral_const_mul, integral_const_mul] at this
    exact mul_left_cancel₀ hs0.ne' this
  have hclosed : ∀ F : Set (ℝ × ℝ), IsClosed F → μ F = ν F := by
    intro F hF
    have hpos : ∀ n : ℕ, 0 < (1 : ℝ) / (n + 1) := fun n => Nat.one_div_pos_of_nat
    have hlim := thickenedIndicator_tendsto_indicator_closure hpos
      tendsto_one_div_add_atTop_nhds_zero_nat F
    rw [hF.closure_eq] at hlim
    have hμ := measure_of_cont_bdd_of_tendsto_indicator μ hF.measurableSet
      (fun n => thickenedIndicator (hpos n) F) (fun n x => thickenedIndicator_le_one _ F x) hlim
    have hν := measure_of_cont_bdd_of_tendsto_indicator ν hF.measurableSet
      (fun n => thickenedIndicator (hpos n) F) (fun n x => thickenedIndicator_le_one _ F x) hlim
    have heq : ∀ n : ℕ, (∫⁻ x, (thickenedIndicator (hpos n) F x : ℝ≥0∞) ∂μ) =
        ∫⁻ x, (thickenedIndicator (hpos n) F x : ℝ≥0∞) ∂ν := by
      intro n
      apply (ENNReal.toReal_eq_toReal_iff' (BoundedContinuousFunction.lintegral_lt_top_of_nnreal μ _).ne
        (BoundedContinuousFunction.lintegral_lt_top_of_nnreal ν _).ne).mp
      rw [BoundedContinuousFunction.toReal_lintegral_coe_eq_integral,
        BoundedContinuousFunction.toReal_lintegral_coe_eq_integral]
      exact hthick _ (hpos n) F
    simp_rw [heq] at hμ
    exact tendsto_nhds_unique hμ hν
  apply ext_of_generate_finite _ ?_ isPiSystem_isClosed
  · exact fun F hF => hclosed F hF
  · exact hclosed univ isClosed_univ
  · rw [BorelSpace.measurable_eq (α := ℝ × ℝ), borel_eq_generateFrom_isClosed]

/-- Weak convergence on `K` with bounded masses gives convergence in `blDist` (Dudley, through
`blDist_bridge` and `Foundations.weak_implies_bl`). -/
private lemma continuum_bl_of_weak {Cs : ℝ} (hCs : 0 ≤ Cs) (μ : ℕ → Measure (ℝ × ℝ))
    (ν : Measure (ℝ × ℝ)) [hμf : ∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν]
    (hμ : ∀ n, μ n (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0)
    (hmass : ∃ M : ℝ, ∀ n, (μ n).real univ ≤ M)
    (hw : ∀ f : ℝ × ℝ → ℝ, ContinuousOn f (specRect Cs) →
      Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun n => blDist Cs (μ n) ν) atTop (𝓝 0) := by
  have hK := continuum_K_meas Cs
  haveI : CompactSpace (specRect Cs) :=
    isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  have hpush : ∀ ρ : Measure (ℝ × ℝ), ρ (specRect Cs)ᶜ = 0 → ∀ φ : ℝ × ℝ → ℝ,
      ∫ x : specRect Cs, φ x.1 ∂(Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) ρ)
        = ∫ x, φ x ∂ρ := by
    intro ρ hρ φ
    rw [← (MeasurableEmbedding.subtype_coe hK).integral_map φ,
      (MeasurableEmbedding.subtype_coe hK).map_comap ρ, Subtype.range_coe,
      Measure.restrict_eq_self_of_ae_mem (continuum_ae_K hρ)]
  have hcomap : ∀ ρ : Measure (ℝ × ℝ), (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) ρ) univ
      = ρ (specRect Cs) := by
    intro ρ
    rw [Measure.comap_apply _ (MeasurableEmbedding.subtype_coe hK).injective
      (MeasurableEmbedding.subtype_coe hK).measurableSet_image' _ MeasurableSet.univ,
      Set.image_univ, Subtype.range_coe]
  have hfin : ∀ ρ : Measure (ℝ × ℝ), IsFiniteMeasure ρ →
      IsFiniteMeasure (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) ρ) := by
    intro ρ hρ
    exact ⟨by rw [hcomap]; exact measure_lt_top _ _⟩
  haveI : ∀ n, IsFiniteMeasure (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) (μ n)) :=
    fun n => hfin _ inferInstance
  haveI : IsFiniteMeasure (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) ν) :=
    hfin _ inferInstance
  let pr : ℝ × ℝ → specRect Cs := fun x =>
    ⟨((projIcc 0 Cs hCs x.1 : ℝ), (projIcc 0 Cs hCs x.2 : ℝ)),
      ⟨(projIcc 0 Cs hCs x.1).2, (projIcc 0 Cs hCs x.2).2⟩⟩
  have hprc : Continuous pr :=
    ((continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))).subtype_mk _
  have hprK : ∀ x : specRect Cs, pr x.1 = x := by
    intro x
    apply Subtype.ext
    simp only [pr, projIcc_of_mem hCs x.2.1, projIcc_of_mem hCs x.2.2]
  have hlim := Muon.Foundations.weak_implies_bl
    (fun n => Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) (μ n))
    (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) ν) (by
      obtain ⟨M, hM⟩ := hmass
      refine ⟨M, fun n => ?_⟩
      rw [hcomap]
      exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))).trans
        (hM n)) (by
      intro f hf
      have hfe : ∀ ρ : Measure (ℝ × ℝ), ρ (specRect Cs)ᶜ = 0 →
          ∫ x, f x ∂(Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) ρ)
            = ∫ x, f (pr x) ∂ρ := by
        intro ρ hρ
        rw [← hpush ρ hρ (fun x => f (pr x))]
        simp only [hprK]
      simp only [hfe _ (hμ _), hfe _ hν]
      exact hw _ (hf.comp hprc).continuousOn)
  have hup : ∀ n, blDist Cs (μ n) ν ≤ 2 * Muon.Foundations.blDist
      (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) (μ n))
      (Measure.comap (Subtype.val : specRect Cs → ℝ × ℝ) ν) :=
    fun n => (blDist_bridge Cs (μ n) ν (hμ n) hν).2
  have h2 := hlim.const_mul 2
  rw [mul_zero] at h2
  exact squeeze_zero (fun n => continuum_bl_nonneg Cs _ _) hup h2

/-- The fields of two coefficient data at the same measure: the forcing terms differ by the
`blDist` of the forcing measures, the drift terms by the sup distance of the kernels on `K`. -/
private lemma continuum_field_coef_diff {m n : ℕ} {C : Covariances m n} {S : SpectralData C}
    {B : ℕ} (c : DynCoeff p S B) [IsFiniteMeasure c.ζ] (hζK : c.ζ (specRect p.CSig)ᶜ = 0)
    (dinf : ℝ × ℝ → ℝ) (hdc : ContinuousOn dinf (specRect p.CSig))
    (hdb : ∀ x ∈ specRect p.CSig, 0 ≤ dinf x ∧ dinf x ≤ dMax p)
    (ζinf : Measure (ℝ × ℝ)) [IsFiniteMeasure ζinf] (hζinfK : ζinf (specRect p.CSig)ᶜ = 0)
    (χ : Measure (ℝ × ℝ)) (hχ : χ ∈ admMeasures p) (φ : ℝ × ℝ → ℝ) (hφc : Continuous φ)
    (hφ : φ ∈ blTest p.CSig) (δ : ℝ) (hδ : ∀ x ∈ specRect p.CSig, |c.d x - dinf x| ≤ δ) :
    |fieldOp p.h c.d c.ζ χ φ - fieldOp p.h dinf ζinf χ φ| ≤
      2 * p.h / Real.sqrt (p.r0 / 2) * (δ * (p.Estar + 1)) +
        p.h ^ 2 * blDist p.CSig c.ζ ζinf := by
  haveI := hχ.1
  have hK := hχ.2.1
  have hr : p.r0 / 2 ≤ riskOf χ := hχ.2.2.2.1
  have hr0 : 0 < p.r0 / 2 := by linarith [p.hr0]
  have hhpos := p.hh
  have hCs : 0 ≤ p.CSig := by linarith [p.hC]
  have hcdc : ContinuousOn c.d (specRect p.CSig) :=
    continuum_local_lip_cont (div_nonneg hCs (Real.sqrt_nonneg _)) c.d_lip
  have hi1 : Integrable (fun x => φ x * c.d x) χ :=
    continuum_integrable_K (M := dMax p) (hφc.continuousOn.mul hcdc) (fun x hx => by
      rw [Pi.mul_apply, abs_mul, abs_of_nonneg (c.d_nonneg x hx)]
      nlinarith [hφ.1 x hx, c.d_le x hx, c.d_nonneg x hx, abs_nonneg (φ x)]) χ hK
  have hi2 : Integrable (fun x => φ x * dinf x) χ :=
    continuum_integrable_K (M := dMax p) (hφc.continuousOn.mul hdc) (fun x hx => by
      rw [Pi.mul_apply, abs_mul, abs_of_nonneg (hdb x hx).1]
      nlinarith [hφ.1 x hx, (hdb x hx).2, (hdb x hx).1, abs_nonneg (φ x)]) χ hK
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ (0, 0) ⟨⟨le_rfl, hCs⟩, ⟨le_rfl, hCs⟩⟩)
  have hdiff : |(∫ x, φ x * c.d x ∂χ) - ∫ x, φ x * dinf x ∂χ| ≤ δ * (p.Estar + 1) := by
    rw [← integral_sub hi1 hi2]
    have h := norm_integral_le_of_norm_le_const (μ := χ)
      (f := fun x => φ x * c.d x - φ x * dinf x) (C := δ)
      ((continuum_ae_K hK).mono fun x hx => by
        rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
        nlinarith [hφ.1 x hx, hδ x hx, abs_nonneg (φ x), abs_nonneg (c.d x - dinf x)])
    rw [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left hχ.2.2.1 hδ0)
  have hz := continuum_bl_le c.ζ ζinf hζK hζinfK φ hφ
  have ha0 : 0 ≤ 2 * p.h / Real.sqrt (riskOf χ) := by positivity
  have ha : 2 * p.h / Real.sqrt (riskOf χ) ≤ 2 * p.h / Real.sqrt (p.r0 / 2) :=
    div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 hr0) (Real.sqrt_le_sqrt hr)
  unfold fieldOp
  rw [if_pos (hr0.trans_le hr), if_pos (hr0.trans_le hr)]
  have he : -(2 * p.h / Real.sqrt (riskOf χ)) * (∫ x, φ x * c.d x ∂χ) +
      p.h ^ 2 * (∫ x, φ x ∂c.ζ) -
      (-(2 * p.h / Real.sqrt (riskOf χ)) * (∫ x, φ x * dinf x ∂χ) +
        p.h ^ 2 * (∫ x, φ x ∂ζinf)) =
      -(2 * p.h / Real.sqrt (riskOf χ)) *
        ((∫ x, φ x * c.d x ∂χ) - ∫ x, φ x * dinf x ∂χ) +
      p.h ^ 2 * ((∫ x, φ x ∂c.ζ) - ∫ x, φ x ∂ζinf) := by ring
  rw [he]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg ha0, abs_of_nonneg (sq_nonneg p.h)]
  exact add_le_add (mul_le_mul ha hdiff (abs_nonneg _) (by positivity))
    (mul_le_mul_of_nonneg_left hz (sq_nonneg _))

/-- Gronwall in exponentially weighted sup form. -/
private lemma continuum_exp_gronwall {T CF A : ℝ} (hT : 0 ≤ T) (hCF : 0 ≤ CF) (hA : 0 ≤ A)
    (D : ℝ → ℝ) (hDb : ∃ M, ∀ τ ∈ Icc 0 T, D τ ≤ M)
    (hD : ∀ M : ℝ, 0 ≤ M → (∀ σ ∈ Icc 0 T, D σ ≤ M * Real.exp ((2 * CF + 1) * σ)) →
      ∀ τ ∈ Icc 0 T, D τ ≤ A + CF * M * (Real.exp ((2 * CF + 1) * τ) - 1) / (2 * CF + 1)) :
    ∀ τ ∈ Icc 0 T, D τ ≤ 2 * A * Real.exp ((2 * CF + 1) * T) := by
  have hL0 : 0 < 2 * CF + 1 := by linarith
  obtain ⟨M0, hM0⟩ := hDb
  set s : Set ℝ := (fun τ => (Real.exp ((2 * CF + 1) * τ))⁻¹ * D τ) '' Icc 0 T with hs
  have hbdd : BddAbove s := by
    refine ⟨max M0 0, ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    have he1 : 1 ≤ Real.exp ((2 * CF + 1) * τ) := Real.one_le_exp (by nlinarith [hτ.1])
    have hi0 : 0 < (Real.exp ((2 * CF + 1) * τ))⁻¹ := inv_pos.2 (Real.exp_pos _)
    have hi1 : (Real.exp ((2 * CF + 1) * τ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ he1
    calc (Real.exp ((2 * CF + 1) * τ))⁻¹ * D τ ≤ (Real.exp ((2 * CF + 1) * τ))⁻¹ * max M0 0 :=
          mul_le_mul_of_nonneg_left ((hM0 τ hτ).trans (le_max_left _ _)) hi0.le
      _ ≤ 1 * max M0 0 := mul_le_mul_of_nonneg_right hi1 (le_max_right _ _)
      _ = max M0 0 := one_mul _
  set M := max (sSup s) 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hDM : ∀ σ ∈ Icc 0 T, D σ ≤ M * Real.exp ((2 * CF + 1) * σ) := by
    intro σ hσ
    have h1 : (Real.exp ((2 * CF + 1) * σ))⁻¹ * D σ ≤ M :=
      (le_csSup hbdd ⟨σ, hσ, rfl⟩).trans (le_max_left _ _)
    have hp := Real.exp_pos ((2 * CF + 1) * σ)
    rw [inv_mul_le_iff₀ hp] at h1
    linarith
  have hkey : ∀ τ ∈ Icc 0 T, (Real.exp ((2 * CF + 1) * τ))⁻¹ * D τ ≤ A + M / 2 := by
    intro τ hτ
    have hE1 : 1 ≤ Real.exp ((2 * CF + 1) * τ) := Real.one_le_exp (by nlinarith [hτ.1])
    set E := Real.exp ((2 * CF + 1) * τ) with hE
    have h1 := hD M hM hDM τ hτ
    have h2 : CF * M * (E - 1) / (2 * CF + 1) ≤ M / 2 * E := by
      rw [div_le_iff₀ hL0]
      have hME : 0 ≤ M * E := mul_nonneg hM (by linarith)
      nlinarith [mul_nonneg hCF hM, mul_nonneg hCF hME]
    have hp : 0 < E := by rw [hE]; exact Real.exp_pos _
    rw [inv_mul_le_iff₀ hp]
    nlinarith
  have hsup : sSup s ≤ A + M / 2 :=
    csSup_le ⟨_, 0, ⟨le_rfl, hT⟩, rfl⟩ (by rintro _ ⟨τ, hτ, rfl⟩; exact hkey τ hτ)
  have hM2 : M ≤ 2 * A := by
    have : M ≤ A + M / 2 := max_le hsup (by linarith)
    linarith
  intro τ hτ
  have hmono : Real.exp ((2 * CF + 1) * τ) ≤ Real.exp ((2 * CF + 1) * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτ.2 hL0.le)
  calc D τ ≤ M * Real.exp ((2 * CF + 1) * τ) := hDM τ hτ
    _ ≤ 2 * A * Real.exp ((2 * CF + 1) * T) :=
      mul_le_mul hM2 hmono (Real.exp_pos _).le (by linarith)

/-- BL comparison of a finite-dimensional solution `ψ` (field of `c`) with a solution `χ` of the
measure equation (field of `dinf`, `ζinf`), by Gronwall. -/
private lemma continuum_compare {m n : ℕ} {C : Covariances m n} (S : SpectralData C) {B : ℕ}
    (c : DynCoeff p S B) (CF : ℝ) (hCF0 : 0 ≤ CF)
    (hCF : ∀ χ χ' : Measure (ℝ × ℝ), χ ∈ admMeasures p → χ' ∈ admMeasures p →
      BddAbove ((fun φ => |fieldOp p.h c.d c.ζ χ φ - fieldOp p.h c.d c.ζ χ' φ|) ''
        blTest p.CSig) ∧
      blNorm p.CSig (fun φ => fieldOp p.h c.d c.ζ χ φ - fieldOp p.h c.d c.ζ χ' φ) ≤
        CF * blDist p.CSig χ χ')
    [IsFiniteMeasure c.ζ] (hζK : c.ζ (specRect p.CSig)ᶜ = 0)
    (dinf : ℝ × ℝ → ℝ) (hdc : ContinuousOn dinf (specRect p.CSig))
    (hdb : ∀ x ∈ specRect p.CSig, 0 ≤ dinf x ∧ dinf x ≤ dMax p)
    (ζinf χ0 : Measure (ℝ × ℝ)) [IsFiniteMeasure ζinf] (hζinfK : ζinf (specRect p.CSig)ᶜ = 0)
    (ψ : ℝ → Measure (ℝ × ℝ)) (hψ : ∀ τ ∈ Icc 0 (Tstar p), ψ τ ∈ admMeasures p)
    (hψeq : ∀ φ : ℝ × ℝ → ℝ, Measurable φ → (∃ M0 : ℝ, ∀ x, |φ x| ≤ M0) →
      ∀ τ ∈ Icc 0 (Tstar p),
        IntervalIntegrable (fun σ => fieldOp p.h c.d c.ζ (ψ σ) φ) volume 0 τ ∧
        ∫ x, φ x ∂(ψ τ) = ∫ x, φ x ∂(ψ 0) + ∫ σ in (0 : ℝ)..τ, fieldOp p.h c.d c.ζ (ψ σ) φ)
    (χ : ℝ → Measure (ℝ × ℝ)) (hχ0 : χ 0 = χ0)
    (hχadm : ∀ τ ∈ Icc 0 (Tstar p), χ τ ∈ admMeasures p)
    (hχeq : ∀ τ ∈ Icc 0 (Tstar p), ∀ φ : ℝ × ℝ → ℝ, Measurable φ → (∃ M0 : ℝ, ∀ x, |φ x| ≤ M0) →
      IntervalIntegrable (fun σ => fieldOp p.h dinf ζinf (χ σ) φ) volume 0 τ ∧
      ∫ x, φ x ∂(χ τ) = ∫ x, φ x ∂χ0 + ∫ σ in (0 : ℝ)..τ, fieldOp p.h dinf ζinf (χ σ) φ)
    (α δ : ℝ) (hα : blDist p.CSig (ψ 0) χ0 ≤ α)
    (hδ : ∀ x ∈ specRect p.CSig, |c.d x - dinf x| ≤ δ) :
    ∀ τ ∈ Icc 0 (Tstar p), blDist p.CSig (ψ τ) (χ τ) ≤
      2 * (α + (2 * p.h / Real.sqrt (p.r0 / 2) * (δ * (p.Estar + 1)) +
        p.h ^ 2 * blDist p.CSig c.ζ ζinf) * Tstar p) * Real.exp ((2 * CF + 1) * Tstar p) := by
  have hT := half_Tstar_nonneg p
  have hCs : 0 ≤ p.CSig := by linarith [p.hC]
  have hhpos := p.hh
  have hEs := p.hE
  set b := 2 * p.h / Real.sqrt (p.r0 / 2) * (δ * (p.Estar + 1)) +
    p.h ^ 2 * blDist p.CSig c.ζ ζinf with hb
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ (0, 0) ⟨⟨le_rfl, hCs⟩, ⟨le_rfl, hCs⟩⟩)
  have hz0 := continuum_bl_nonneg p.CSig c.ζ ζinf
  have hb0 : 0 ≤ b := by positivity
  have hα0 : 0 ≤ α := (continuum_bl_nonneg _ _ _).trans hα
  have h0 : (0 : ℝ) ∈ Icc 0 (Tstar p) := ⟨le_rfl, hT⟩
  have hχ0adm : χ0 ∈ admMeasures p := hχ0 ▸ hχadm 0 h0
  have hψ0 := hψ 0 h0
  haveI := hχ0adm.1
  haveI := hψ0.1
  apply continuum_exp_gronwall (D := fun τ => blDist p.CSig (ψ τ) (χ τ)) hT hCF0
    (by positivity : 0 ≤ α + b * Tstar p)
  · refine ⟨2 * (p.Estar + 1), fun τ hτ => ?_⟩
    haveI := (hψ τ hτ).1
    haveI := (hχadm τ hτ).1
    exact (continuum_bl_le_mass _ _ (hψ τ hτ).2.1 (hχadm τ hτ).2.1).trans
      (by linarith [(hψ τ hτ).2.2.1, (hχadm τ hτ).2.2.1])
  · intro M hM hDM τ hτ
    haveI := (hψ τ hτ).1
    haveI := (hχadm τ hτ).1
    have hE1 : 1 ≤ Real.exp ((2 * CF + 1) * τ) := Real.one_le_exp (by nlinarith [hτ.1])
    have hL0 : 0 < 2 * CF + 1 := by linarith
    have hpos : 0 ≤ CF * M * (Real.exp ((2 * CF + 1) * τ) - 1) / (2 * CF + 1) := by
      apply div_nonneg _ hL0.le
      exact mul_nonneg (mul_nonneg hCF0 hM) (by linarith)
    apply continuum_bl_le_of _ _ (by positivity)
    intro φ0 hφ0
    obtain ⟨φ, hφc, hφb, hφ, hφeq⟩ := continuum_test_ext hCs φ0 hφ0
    rw [continuum_integral_congr_K (fun x hx => (hφeq x hx).symm) (ψ τ) (hψ τ hτ).2.1,
      continuum_integral_congr_K (fun x hx => (hφeq x hx).symm) (χ τ) (hχadm τ hτ).2.1]
    have hφm : Measurable φ := hφc.measurable
    have hφB : ∃ M0 : ℝ, ∀ x, |φ x| ≤ M0 := ⟨1, hφb⟩
    obtain ⟨hI1, hE1'⟩ := hψeq φ hφm hφB τ hτ
    obtain ⟨hI2, hE2'⟩ := hχeq τ hτ φ hφm hφB
    rw [hE1', hE2']
    have hsub : (∫ x, φ x ∂(ψ 0)) + (∫ σ in (0 : ℝ)..τ, fieldOp p.h c.d c.ζ (ψ σ) φ) -
        ((∫ x, φ x ∂χ0) + ∫ σ in (0 : ℝ)..τ, fieldOp p.h dinf ζinf (χ σ) φ) =
        ((∫ x, φ x ∂(ψ 0)) - ∫ x, φ x ∂χ0) + ∫ σ in (0 : ℝ)..τ,
          (fieldOp p.h c.d c.ζ (ψ σ) φ - fieldOp p.h dinf ζinf (χ σ) φ) := by
      rw [intervalIntegral.integral_sub hI1 hI2]
      ring
    rw [hsub]
    have hpt : ∀ σ ∈ Icc 0 τ,
        |fieldOp p.h c.d c.ζ (ψ σ) φ - fieldOp p.h dinf ζinf (χ σ) φ| ≤
          CF * M * Real.exp ((2 * CF + 1) * σ) + b := by
      intro σ hσ
      have hσ' : σ ∈ Icc 0 (Tstar p) := ⟨hσ.1, hσ.2.trans hτ.2⟩
      obtain ⟨hbdd, hle⟩ := hCF (ψ σ) (χ σ) (hψ σ hσ') (hχadm σ hσ')
      have h1 : |fieldOp p.h c.d c.ζ (ψ σ) φ - fieldOp p.h c.d c.ζ (χ σ) φ| ≤
          CF * blDist p.CSig (ψ σ) (χ σ) :=
        (le_csSup hbdd ⟨φ, hφ, rfl⟩).trans hle
      have h2 := continuum_field_coef_diff c hζK dinf hdc hdb ζinf hζinfK (χ σ) (hχadm σ hσ')
        φ hφc hφ δ hδ
      have h3 : CF * blDist p.CSig (ψ σ) (χ σ) ≤ CF * M * Real.exp ((2 * CF + 1) * σ) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hDM σ hσ') hCF0
      calc |fieldOp p.h c.d c.ζ (ψ σ) φ - fieldOp p.h dinf ζinf (χ σ) φ|
          = |(fieldOp p.h c.d c.ζ (ψ σ) φ - fieldOp p.h c.d c.ζ (χ σ) φ) +
              (fieldOp p.h c.d c.ζ (χ σ) φ - fieldOp p.h dinf ζinf (χ σ) φ)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
        _ ≤ CF * M * Real.exp ((2 * CF + 1) * σ) + b := add_le_add (h1.trans h3) h2
    have hderiv : ∀ x ∈ uIcc (0 : ℝ) τ, HasDerivAt
        (fun σ => CF * M * Real.exp ((2 * CF + 1) * σ) / (2 * CF + 1) + b * σ)
        (CF * M * Real.exp ((2 * CF + 1) * x) + b) x := by
      intro x _
      have h := ((((hasDerivAt_id x).const_mul (2 * CF + 1)).exp.const_mul (CF * M)).div_const
        (2 * CF + 1)).add ((hasDerivAt_id x).const_mul b)
      convert h using 1
      · ext y
        simp only [id, Pi.add_apply]
      · field_simp
        rfl
    have hcont : Continuous fun σ => CF * M * Real.exp ((2 * CF + 1) * σ) + b := by fun_prop
    have hcalc : ∫ σ in (0 : ℝ)..τ, (CF * M * Real.exp ((2 * CF + 1) * σ) + b) =
        CF * M * (Real.exp ((2 * CF + 1) * τ) - 1) / (2 * CF + 1) + b * τ := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
      simp only [mul_zero, Real.exp_zero, mul_one]
      ring
    have hint : |∫ σ in (0 : ℝ)..τ,
        (fieldOp p.h c.d c.ζ (ψ σ) φ - fieldOp p.h dinf ζinf (χ σ) φ)| ≤
        CF * M * (Real.exp ((2 * CF + 1) * τ) - 1) / (2 * CF + 1) + b * τ := by
      refine (intervalIntegral.abs_integral_le_integral_abs hτ.1).trans ?_
      rw [← hcalc]
      exact intervalIntegral.integral_mono_on hτ.1 (hI1.sub hI2).abs
        (hcont.intervalIntegrable _ _) hpt
    have hα' := (continuum_bl_le (ψ 0) χ0 hψ0.2.1 hχ0adm.2.1 φ hφ).trans hα
    have hbτ : b * τ ≤ b * Tstar p := mul_le_mul_of_nonneg_left hτ.2 hb0
    calc _ ≤ |(∫ x, φ x ∂(ψ 0)) - ∫ x, φ x ∂χ0| + |∫ σ in (0 : ℝ)..τ,
          (fieldOp p.h c.d c.ζ (ψ σ) φ - fieldOp p.h dinf ζinf (χ σ) φ)| := abs_add_le _ _
      _ ≤ _ := by linarith

/-- The finite-dimensional facts at dimension `k`: `χ^ode_k(τ) ∈ 𝔐`, its weak equation, and
`χ^ode_k(0) = χ(Δ_0)`. -/
private lemma continuum_ode_facts (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (e : ∀ k : ℕ, ℝ → Fin (m k) → Fin (n k) → ℝ)
    (he : ∀ k : ℕ, def_app_dyn_ode p (S k) (c k) (dev0 hyp k) (Tstar p) (e k)) (k : ℕ) :
    (∀ τ ∈ Icc 0 (Tstar p),
      odeMeasure (((B k : ℕ) : ℝ)) (S k).μ (S k).lam (e k τ) ∈ admMeasures p) ∧
    (∀ φ : ℝ × ℝ → ℝ, Measurable φ → (∃ M0 : ℝ, ∀ x, |φ x| ≤ M0) →
      ∀ τ ∈ Icc 0 (Tstar p),
        IntervalIntegrable (fun σ => fieldOp p.h (c k).d (c k).ζ
          (odeMeasure (((B k : ℕ) : ℝ)) (S k).μ (S k).lam (e k σ)) φ) volume 0 τ ∧
        ∫ x, φ x ∂(odeMeasure (((B k : ℕ) : ℝ)) (S k).μ (S k).lam (e k τ)) =
          ∫ x, φ x ∂(odeMeasure (((B k : ℕ) : ℝ)) (S k).μ (S k).lam (e k 0)) +
            ∫ σ in (0 : ℝ)..τ, fieldOp p.h (c k).d (c k).ζ
              (odeMeasure (((B k : ℕ) : ℝ)) (S k).μ (S k).lam (e k σ)) φ) ∧
    odeMeasure (((B k : ℕ) : ℝ)) (S k).μ (S k).lam (e k 0) = specMeasure (S k) (dev0 hyp k) := by
  have hT := half_Tstar_nonneg p
  have h0 : (0 : ℝ) ∈ Icc 0 (Tstar p) := ⟨le_rfl, hT⟩
  refine ⟨fun τ hτ => (prop_app_dyn_ode_ii p (S k) (c k) (dev0 hyp k) (hyp.normBd k).2
      (hyp.normBd k).1 (hyp.dims k) (hyp.W0_norm k) (hyp.W0_risk k).1 (hyp.W0_risk k).2
      (e k) (he k) τ hτ).2.2,
    fun φ hφ hb τ hτ => prop_app_dyn_ode_iii p (S k) (c k) (dev0 hyp k) (hyp.normBd k).2
      (hyp.normBd k).1 (hyp.dims k) (hyp.W0_norm k) (hyp.W0_risk k).1 (hyp.W0_risk k).2
      (e k) (he k) φ hφ hb τ hτ, ?_⟩
  have hB : ((B k : ℕ) : ℝ) ≠ 0 := by
    intro hB0
    have := (he k).2 0 h0
    unfold odeRisk at this
    simp [hB0] at this
  rw [(he k).1.1]
  unfold odeMeasure odeInit specMeasure
  congr 1
  funext i j
  field_simp

/-- `sup_τ ‖χ^ode_B(τ) − χ(τ)‖_BL → 0` for every solution `χ` of the measure equation. -/
private lemma continuum_ode_conv (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (ι : ℕ → ℕ) (dinf : ℝ × ℝ → ℝ) (ζinf χ0 : Measure (ℝ × ℝ))
    (hL : contLimit hyp S c ι dinf ζinf χ0)
    (e : ∀ k : ℕ, ℝ → Fin (m k) → Fin (n k) → ℝ)
    (he : ∀ k : ℕ, def_app_dyn_ode p (S k) (c k) (dev0 hyp k) (Tstar p) (e k))
    (χ : ℝ → Measure (ℝ × ℝ)) (hχ : eqn_app_dyn_continuum p dinf ζinf χ0 χ) :
      (∀ n : ℕ, BddAbove ((fun τ => blDist p.CSig
          (odeMeasure (((B (ι n) : ℕ) : ℝ)) (S (ι n)).μ (S (ι n)).lam (e (ι n) τ)) (χ τ)) ''
        Icc 0 (Tstar p))) ∧
      Tendsto (fun n : ℕ => sSup ((fun τ => blDist p.CSig
          (odeMeasure (((B (ι n) : ℕ) : ℝ)) (S (ι n)).μ (S (ι n)).lam (e (ι n) τ)) (χ τ)) ''
        Icc 0 (Tstar p))) atTop (𝓝 0) := by
  have hT := half_Tstar_nonneg p
  have h0 : (0 : ℝ) ∈ Icc 0 (Tstar p) := ⟨le_rfl, hT⟩
  have hCs : 0 ≤ p.CSig := by linarith [p.hC]
  have hhpos := p.hh
  have hEs := p.hE
  obtain ⟨CF0, hCF0⟩ := lem_app_dyn_field_iii p (p.Estar + 1) (p.r0 / 2) (p.r1 + 1 / 2)
    (by linarith [p.hr0])
  set CF := max CF0 0 with hCFdef
  have hCFnn : 0 ≤ CF := le_max_right _ _
  have hCF : ∀ k, ∀ χ χ' : Measure (ℝ × ℝ), χ ∈ admMeasures p → χ' ∈ admMeasures p →
      BddAbove ((fun φ => |fieldOp p.h (c k).d (c k).ζ χ φ - fieldOp p.h (c k).d (c k).ζ χ' φ|) ''
        blTest p.CSig) ∧
      blNorm p.CSig (fun φ => fieldOp p.h (c k).d (c k).ζ χ φ - fieldOp p.h (c k).d (c k).ζ χ' φ)
        ≤ CF * blDist p.CSig χ χ' := by
    intro k χ χ' h1 h2
    obtain ⟨hb, hle⟩ := hCF0 (S k) (c k) χ χ' h1 h2
    exact ⟨hb, hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (continuum_bl_nonneg _ _ _))⟩
  have hζfin : ∀ k, IsFiniteMeasure (c k).ζ := fun k => by
    rw [(c k).ζ_eq]
    exact continuum_atom_isFinite _ _ _
  have hζK : ∀ k, (c k).ζ (specRect p.CSig)ᶜ = 0 := fun k => by
    rw [(c k).ζ_eq]
    exact continuum_atom_support (S k) _ p.CSig (hyp.normBd k).2 (hyp.normBd k).1
  haveI := hL.2.1.1
  haveI := hL.2.2.1
  have hζinfK := hL.2.1.2.1
  have hdc := continuum_limit_d_continuousOn S c hyp ι dinf ζinf χ0 hL
  have hdb := continuum_limit_d_bounds S c hyp ι dinf ζinf χ0 hL
  have hχadm := hχ.2.1
  refine ⟨fun n => ?_, ?_⟩
  · refine ⟨2 * (p.Estar + 1), ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    have hψ := (continuum_ode_facts F hyp S c e he (ι n)).1 τ hτ
    haveI := hψ.1
    haveI := (hχadm τ hτ).1
    exact (continuum_bl_le_mass _ _ hψ.2.1 (hχadm τ hτ).2.1).trans
      (by linarith [hψ.2.2.1, (hχadm τ hτ).2.2.1])
  -- convergence of the initial data and of the forcing in `blDist`
  haveI : ∀ n, IsFiniteMeasure (specMeasure (S (ι n)) (dev0 hyp (ι n))) := fun n => by
    unfold specMeasure
    exact continuum_atom_isFinite _ _ _
  have hαlim : Tendsto (fun n => blDist p.CSig (specMeasure (S (ι n)) (dev0 hyp (ι n))) χ0)
      atTop (𝓝 0) :=
    continuum_bl_of_weak hCs _ χ0 (fun n => by
        unfold specMeasure
        exact continuum_atom_support (S (ι n)) _ p.CSig (hyp.normBd _).2 (hyp.normBd _).1)
      hL.2.2.2.1 ⟨p.Estar, fun n => by rw [continuum_spec_mass]; exact hyp.W0_norm _⟩
      hL.2.2.2.2
  haveI : ∀ n, IsFiniteMeasure (c (ι n)).ζ := fun n => hζfin _
  have hzlim : Tendsto (fun n => blDist p.CSig (c (ι n)).ζ ζinf) atTop (𝓝 0) :=
    continuum_bl_of_weak hCs _ ζinf (fun n => hζK _) hζinfK
      ⟨mZeta p, fun n => (c (ι n)).ζ_mass⟩ hL.2.1.2.2
  rw [Metric.tendsto_atTop]
  intro η hη
  set c1 := 2 * p.h / Real.sqrt (p.r0 / 2) with hc1
  have hc1nn : 0 ≤ c1 := by positivity
  set c2 := 2 * Real.exp ((2 * CF + 1) * Tstar p) *
    (1 + (c1 * (p.Estar + 1) + p.h ^ 2) * Tstar p) with hc2
  have hc2nn : 0 ≤ c2 := by
    have := Real.exp_pos ((2 * CF + 1) * Tstar p)
    have : 0 ≤ (c1 * (p.Estar + 1) + p.h ^ 2) * Tstar p :=
      mul_nonneg (by positivity) hT
    positivity
  set ε := η / (c2 + 1) with hε
  have hεpos : 0 < ε := div_pos hη (by linarith)
  have ev1 := (Metric.tendsto_nhds.1 hαlim) ε hεpos
  have ev2 := (Metric.tendsto_nhds.1 hzlim) ε hεpos
  have ev3 := Metric.tendstoUniformlyOn_iff.1 hL.1 ε hεpos
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((ev1.and ev2).and ev3)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨⟨hα, hz⟩, hd⟩ := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (continuum_bl_nonneg _ _ _)] at hα hz
  obtain ⟨hψadm, hψeq, hψ0⟩ := continuum_ode_facts F hyp S c e he (ι n)
  have hcomp := continuum_compare (S (ι n)) (c (ι n)) CF hCFnn (hCF (ι n)) (hζK (ι n)) dinf hdc
    hdb ζinf χ0 hζinfK _ hψadm hψeq χ hχ.1 hχ.2.1 hχ.2.2.2 ε ε (by rw [hψ0]; exact hα.le)
    (fun x hx => by rw [abs_sub_comm, ← Real.dist_eq]; exact (hd x hx).le)
  have hbound : ∀ τ ∈ Icc 0 (Tstar p), blDist p.CSig
      (odeMeasure (((B (ι n) : ℕ) : ℝ)) (S (ι n)).μ (S (ι n)).lam (e (ι n) τ)) (χ τ) ≤ ε * c2 := by
    intro τ hτ
    refine (hcomp τ hτ).trans ?_
    have hexp := Real.exp_pos ((2 * CF + 1) * Tstar p)
    have h1 : p.h ^ 2 * blDist p.CSig (c (ι n)).ζ ζinf ≤ p.h ^ 2 * ε :=
      mul_le_mul_of_nonneg_left hz.le (sq_nonneg _)
    have h2 : (c1 * (ε * (p.Estar + 1)) + p.h ^ 2 * blDist p.CSig (c (ι n)).ζ ζinf) * Tstar p ≤
        (c1 * (ε * (p.Estar + 1)) + p.h ^ 2 * ε) * Tstar p :=
      mul_le_mul_of_nonneg_right (by linarith) hT
    have h3 := mul_le_mul_of_nonneg_right (add_le_add_left h2 ε) (mul_nonneg zero_le_two hexp.le)
    rw [hc2]
    nlinarith
  have hnn : 0 ≤ sSup ((fun τ => blDist p.CSig
      (odeMeasure (((B (ι n) : ℕ) : ℝ)) (S (ι n)).μ (S (ι n)).lam (e (ι n) τ)) (χ τ)) ''
        Icc 0 (Tstar p)) :=
    Real.sSup_nonneg (by rintro _ ⟨τ, _, rfl⟩; exact continuum_bl_nonneg _ _ _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have hle : sSup ((fun τ => blDist p.CSig
      (odeMeasure (((B (ι n) : ℕ) : ℝ)) (S (ι n)).μ (S (ι n)).lam (e (ι n) τ)) (χ τ)) ''
        Icc 0 (Tstar p)) ≤ ε * c2 :=
    csSup_le ⟨_, 0, h0, rfl⟩ (by rintro _ ⟨τ, hτ, rfl⟩; exact hbound τ hτ)
  refine hle.trans_lt ?_
  rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  nlinarith

/-- Uniqueness of the solution of the measure equation on `[0, T⋆]`, from the convergence of
`χ^ode_B` to every solution. -/
private lemma continuum_unique (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (ι : ℕ → ℕ) (dinf : ℝ × ℝ → ℝ) (ζinf χ0 : Measure (ℝ × ℝ))
    (hL : contLimit hyp S c ι dinf ζinf χ0)
    (e : ∀ k : ℕ, ℝ → Fin (m k) → Fin (n k) → ℝ)
    (he : ∀ k : ℕ, def_app_dyn_ode p (S k) (c k) (dev0 hyp k) (Tstar p) (e k))
    (χ χ' : ℝ → Measure (ℝ × ℝ)) (hχ : eqn_app_dyn_continuum p dinf ζinf χ0 χ)
    (hχ' : eqn_app_dyn_continuum p dinf ζinf χ0 χ') :
    ∀ τ ∈ Icc 0 (Tstar p), χ τ = χ' τ := by
  intro τ hτ
  obtain ⟨hb1, ht1⟩ := continuum_ode_conv F hyp S c ι dinf ζinf χ0 hL e he χ hχ
  obtain ⟨hb2, ht2⟩ := continuum_ode_conv F hyp S c ι dinf ζinf χ0 hL e he χ' hχ'
  have hadm := hχ.2.1 τ hτ
  have hadm' := hχ'.2.1 τ hτ
  haveI := hadm.1
  haveI := hadm'.1
  apply continuum_ext_of_bl (Cs := p.CSig)
  intro φ hφ
  have key : ∀ n : ℕ, |∫ x, φ x ∂(χ τ) - ∫ x, φ x ∂(χ' τ)| ≤
      sSup ((fun τ => blDist p.CSig
          (odeMeasure (((B (ι n) : ℕ) : ℝ)) (S (ι n)).μ (S (ι n)).lam (e (ι n) τ)) (χ τ)) ''
        Icc 0 (Tstar p)) +
      sSup ((fun τ => blDist p.CSig
          (odeMeasure (((B (ι n) : ℕ) : ℝ)) (S (ι n)).μ (S (ι n)).lam (e (ι n) τ)) (χ' τ)) ''
        Icc 0 (Tstar p)) := by
    intro n
    have hψ := (continuum_ode_facts F hyp S c e he (ι n)).1 τ hτ
    haveI := hψ.1
    have h1 := (continuum_bl_le _ (χ τ) hψ.2.1 hadm.2.1 φ hφ).trans
      (le_csSup (hb1 n) ⟨τ, hτ, rfl⟩)
    have h2 := (continuum_bl_le _ (χ' τ) hψ.2.1 hadm'.2.1 φ hφ).trans
      (le_csSup (hb2 n) ⟨τ, hτ, rfl⟩)
    have h3 := abs_sub_le (∫ x, φ x ∂(χ τ))
      (∫ x, φ x ∂(odeMeasure (((B (ι n) : ℕ) : ℝ)) (S (ι n)).μ (S (ι n)).lam (e (ι n) τ)))
      (∫ x, φ x ∂(χ' τ))
    have h4 := abs_sub_comm (∫ x, φ x ∂(χ τ))
      (∫ x, φ x ∂(odeMeasure (((B (ι n) : ℕ) : ℝ)) (S (ι n)).μ (S (ι n)).lam (e (ι n) τ)))
    linarith
  have hlim := ht1.add ht2
  rw [add_zero] at hlim
  have hle : |∫ x, φ x ∂(χ τ) - ∫ x, φ x ∂(χ' τ)| ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall key)
  exact sub_eq_zero.1 (abs_nonpos_iff.1 hle)

private lemma continuum_int_mul {Cs M D : ℝ} {φ d : ℝ × ℝ → ℝ} (hφ : Measurable φ)
    (hφb : ∀ x, |φ x| ≤ M) (hd : ContinuousOn d (specRect Cs))
    (hdb : ∀ x ∈ specRect Cs, |d x| ≤ D)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (hμ : μ (specRect Cs)ᶜ = 0) :
    Integrable (fun x => φ x * d x) μ := by
  have hres : μ.restrict (specRect Cs) = μ :=
    Measure.restrict_eq_self_of_ae_mem (continuum_ae_K hμ)
  have hm : AEStronglyMeasurable d μ := by
    rw [← hres]
    exact hd.aestronglyMeasurable (continuum_K_meas Cs)
  refine Integrable.of_bound (hφ.aestronglyMeasurable.mul hm) (M * D) ?_
  filter_upwards [continuum_ae_K hμ] with x hx
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hφb x) (hdb x hx) (abs_nonneg _) ((abs_nonneg _).trans (hφb x))

private lemma continuum_int_bdd {M : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : Measurable φ)
    (hφb : ∀ x, |φ x| ≤ M) (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] : Integrable φ μ :=
  Integrable.of_bound hφ.aestronglyMeasurable M
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hφb x)

private lemma continuum_field_lin {d : ℝ × ℝ → ℝ} (hd : ContinuousOn d (specRect p.CSig))
    (hdb : ∀ x ∈ specRect p.CSig, 0 ≤ d x ∧ d x ≤ dMax p) (ζ : Measure (ℝ × ℝ))
    [IsFiniteMeasure ζ] (χ : Measure (ℝ × ℝ)) (hχ : χ ∈ admMeasures p) {φ ψ : ℝ × ℝ → ℝ}
    {M1 M2 : ℝ} (hφ : Measurable φ) (hφb : ∀ x, |φ x| ≤ M1) (hψ : Measurable ψ)
    (hψb : ∀ x, |ψ x| ≤ M2) (a b : ℝ) :
    fieldOp p.h d ζ χ (fun x => a * φ x + b * ψ x) =
      a * fieldOp p.h d ζ χ φ + b * fieldOp p.h d ζ χ ψ := by
  haveI := hχ.1
  have hr : 0 < riskOf χ := by linarith [hχ.2.2.2.1, p.hr0]
  have hdb' : ∀ x ∈ specRect p.CSig, |d x| ≤ dMax p := fun x hx => by
    rw [abs_of_nonneg (hdb x hx).1]; exact (hdb x hx).2
  have i1 := continuum_int_mul hφ hφb hd hdb' χ hχ.2.1
  have i2 := continuum_int_mul hψ hψb hd hdb' χ hχ.2.1
  have j1 := continuum_int_bdd hφ hφb ζ
  have j2 := continuum_int_bdd hψ hψb ζ
  unfold fieldOp
  rw [if_pos hr, if_pos hr, if_pos hr]
  have e1 : ∫ x, (a * φ x + b * ψ x) * d x ∂χ =
      a * ∫ x, φ x * d x ∂χ + b * ∫ x, ψ x * d x ∂χ := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (i1.const_mul a) (i2.const_mul b)]
    congr 1
    funext x
    ring
  have e2 : ∫ x, (a * φ x + b * ψ x) ∂ζ = a * ∫ x, φ x ∂ζ + b * ∫ x, ψ x ∂ζ := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (j1.const_mul a) (j2.const_mul b)]
  rw [e1, e2]
  ring

private lemma continuum_field_bdd {d : ℝ × ℝ → ℝ}
    (hdb : ∀ x ∈ specRect p.CSig, 0 ≤ d x ∧ d x ≤ dMax p) (ζ : Measure (ℝ × ℝ))
    [IsFiniteMeasure ζ] (χ : Measure (ℝ × ℝ)) (hχ : χ ∈ admMeasures p) {φ : ℝ × ℝ → ℝ}
    {M : ℝ} (hM : 0 ≤ M) (hφb : ∀ x, |φ x| ≤ M) :
    |fieldOp p.h d ζ χ φ| ≤ 2 * p.h / Real.sqrt (p.r0 / 2) * (M * dMax p * (p.Estar + 1)) +
      p.h ^ 2 * (M * ζ.real univ) := by
  haveI := hχ.1
  have hr0 : 0 < p.r0 / 2 := by linarith [p.hr0]
  have hr : p.r0 / 2 ≤ riskOf χ := hχ.2.2.2.1
  have hhpos := p.hh
  have hdM := half_dMax_nonneg p
  have h1 : |∫ x, φ x * d x ∂χ| ≤ M * dMax p * (p.Estar + 1) := by
    have h := norm_integral_le_of_norm_le_const (μ := χ) (f := fun x => φ x * d x)
      (C := M * dMax p) ((continuum_ae_K hχ.2.1).mono fun x hx => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hdb x hx).1]
        exact mul_le_mul (hφb x) (hdb x hx).2 (hdb x hx).1 hM)
    rw [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left hχ.2.2.1 (mul_nonneg hM hdM))
  have h2 : |∫ x, φ x ∂ζ| ≤ M * ζ.real univ := by
    have h := norm_integral_le_of_norm_le_const (μ := ζ) (f := φ) (C := M)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hφb x)
    rw [Real.norm_eq_abs] at h
    linarith
  have ha0 : 0 ≤ 2 * p.h / Real.sqrt (riskOf χ) := by positivity
  have ha : 2 * p.h / Real.sqrt (riskOf χ) ≤ 2 * p.h / Real.sqrt (p.r0 / 2) :=
    div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 hr0) (Real.sqrt_le_sqrt hr)
  unfold fieldOp
  rw [if_pos (hr0.trans_le hr)]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg ha0, abs_of_nonneg (sq_nonneg p.h)]
  exact add_le_add (mul_le_mul ha h1 (abs_nonneg _) (by positivity))
    (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))

private lemma continuum_thick_test {Cs δ : ℝ} (hδ : 0 < δ) (F : Set (ℝ × ℝ)) :
    Continuous (fun x => min 1 δ * (thickenedIndicator hδ F x : ℝ)) ∧
    (∀ x, |min 1 δ * (thickenedIndicator hδ F x : ℝ)| ≤ 1) ∧
    (fun x => min 1 δ * (thickenedIndicator hδ F x : ℝ)) ∈ blTest Cs := by
  set s : ℝ := min 1 δ with hs
  have hs0 : 0 < s := lt_min one_pos hδ
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsδ : s ≤ δ := min_le_right _ _
  have hlip := lipschitzWith_thickenedIndicator hδ F
  have hb : ∀ x, |s * (thickenedIndicator hδ F x : ℝ)| ≤ 1 := by
    intro x
    have h1 : (thickenedIndicator hδ F x : ℝ) ≤ 1 := by
      exact_mod_cast thickenedIndicator_le_one hδ F x
    have h0 : (0 : ℝ) ≤ thickenedIndicator hδ F x := NNReal.coe_nonneg _
    rw [abs_of_nonneg (mul_nonneg hs0.le h0)]
    nlinarith
  refine ⟨continuous_const.mul (NNReal.continuous_coe.comp (thickenedIndicator hδ F).continuous),
    hb, fun x _ => hb x, fun x _ y _ => ?_⟩
  have hd := hlip.dist_le_mul x y
  rw [NNReal.dist_eq] at hd
  have hc : ((δ.toNNReal⁻¹ : NNReal) : ℝ) = 1 / δ := by
    rw [NNReal.coe_inv, Real.coe_toNNReal _ hδ.le, one_div]
  rw [hc] at hd
  have hl1 : dist x y ≤ l1 x y := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    unfold l1
    exact max_le (by linarith [abs_nonneg (x.2 - y.2)]) (by linarith [abs_nonneg (x.1 - y.1)])
  show |s * (thickenedIndicator hδ F x : ℝ) - s * (thickenedIndicator hδ F y : ℝ)| ≤ l1 x y
  rw [← mul_sub, abs_mul, abs_of_pos hs0]
  calc s * |(thickenedIndicator hδ F x : ℝ) - thickenedIndicator hδ F y|
      ≤ s * (1 / δ * dist x y) := mul_le_mul_of_nonneg_left hd hs0.le
    _ ≤ dist x y := by
      rw [← mul_assoc]
      have : s * (1 / δ) ≤ 1 := by
        rw [mul_one_div]; exact (div_le_one hδ).2 hsδ
      nlinarith [dist_nonneg (x := x) (y := y)]
    _ ≤ l1 x y := hl1

/-- Monotone-class extension: the weak equation for continuous bounded-Lipschitz test functions
gives it for every bounded measurable test function. -/
private lemma continuum_weak_extend {d : ℝ × ℝ → ℝ} (hd : ContinuousOn d (specRect p.CSig))
    (hdb : ∀ x ∈ specRect p.CSig, 0 ≤ d x ∧ d x ≤ dMax p) (ζ χ0 : Measure (ℝ × ℝ))
    [IsFiniteMeasure ζ] (hζK : ζ (specRect p.CSig)ᶜ = 0) [IsFiniteMeasure χ0]
    (χ : ℝ → Measure (ℝ × ℝ)) (hχ : ∀ σ ∈ Icc 0 (Tstar p), χ σ ∈ admMeasures p)
    (τ : ℝ) (hτ : τ ∈ Icc 0 (Tstar p))
    (hbase : ∀ φ : ℝ × ℝ → ℝ, Continuous φ → (∀ x, |φ x| ≤ 1) → φ ∈ blTest p.CSig →
      IntervalIntegrable (fun σ => fieldOp p.h d ζ (χ σ) φ) volume 0 τ ∧
      ∫ x, φ x ∂(χ τ) = ∫ x, φ x ∂χ0 + ∫ σ in (0 : ℝ)..τ, fieldOp p.h d ζ (χ σ) φ) :
    ∀ φ : ℝ × ℝ → ℝ, Measurable φ → (∃ M0 : ℝ, ∀ x, |φ x| ≤ M0) →
      IntervalIntegrable (fun σ => fieldOp p.h d ζ (χ σ) φ) volume 0 τ ∧
      ∫ x, φ x ∂(χ τ) = ∫ x, φ x ∂χ0 + ∫ σ in (0 : ℝ)..τ, fieldOp p.h d ζ (χ σ) φ := by
  obtain ⟨H, hH⟩ : ∃ H : (ℝ × ℝ → ℝ) → Prop, ∀ φ, H φ ↔
      (IntervalIntegrable (fun σ => fieldOp p.h d ζ (χ σ) φ) volume 0 τ ∧
      ∫ x, φ x ∂(χ τ) = ∫ x, φ x ∂χ0 + ∫ σ in (0 : ℝ)..τ, fieldOp p.h d ζ (χ σ) φ) :=
    ⟨_, fun φ => Iff.rfl⟩
  have hτ0 := hτ.1
  haveI := (hχ τ hτ).1
  have hsub : ∀ σ ∈ Icc 0 τ, σ ∈ Icc 0 (Tstar p) := fun σ hσ => ⟨hσ.1, hσ.2.trans hτ.2⟩
  have hsub' : ∀ σ ∈ Set.uIoc 0 τ, σ ∈ Icc 0 (Tstar p) := fun σ hσ => by
    rw [uIoc_of_le hτ0] at hσ
    exact ⟨hσ.1.le, hσ.2.trans hτ.2⟩
  -- linear combinations
  have hlin : ∀ (φ ψ : ℝ × ℝ → ℝ) (M1 M2 : ℝ), Measurable φ → (∀ x, |φ x| ≤ M1) →
      Measurable ψ → (∀ x, |ψ x| ≤ M2) → H φ → H ψ → ∀ a b : ℝ,
        H (fun x => a * φ x + b * ψ x) := by
    intro φ ψ M1 M2 hφ hφb hψ hψb h1 h2 a b
    obtain ⟨I1, E1⟩ := (hH φ).1 h1
    obtain ⟨I2, E2⟩ := (hH ψ).1 h2
    have heq : EqOn (fun σ => fieldOp p.h d ζ (χ σ) (fun x => a * φ x + b * ψ x))
        (fun σ => a * fieldOp p.h d ζ (χ σ) φ + b * fieldOp p.h d ζ (χ σ) ψ) (uIcc 0 τ) := by
      intro σ hσ
      rw [uIcc_of_le hτ0] at hσ
      exact continuum_field_lin hd hdb ζ (χ σ) (hχ σ (hsub σ hσ)) hφ hφb hψ hψb a b
    have hI := (I1.const_mul a).add (I2.const_mul b)
    refine (hH _).2 ⟨?_, ?_⟩
    · have hI' := (intervalIntegrable_iff_integrableOn_Icc_of_le hτ0).1 hI
      rw [uIcc_of_le hτ0] at heq
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hτ0).2
        (hI'.congr_fun heq.symm measurableSet_Icc)
    · rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_add
        (I1.const_mul a) (I2.const_mul b), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      have l1 : ∫ x, (a * φ x + b * ψ x) ∂(χ τ) = a * ∫ x, φ x ∂(χ τ) + b * ∫ x, ψ x ∂(χ τ) := by
        rw [← integral_const_mul, ← integral_const_mul, ← integral_add
          ((continuum_int_bdd hφ hφb _).const_mul a) ((continuum_int_bdd hψ hψb _).const_mul b)]
      have l2 : ∫ x, (a * φ x + b * ψ x) ∂χ0 = a * ∫ x, φ x ∂χ0 + b * ∫ x, ψ x ∂χ0 := by
        rw [← integral_const_mul, ← integral_const_mul, ← integral_add
          ((continuum_int_bdd hφ hφb _).const_mul a) ((continuum_int_bdd hψ hψb _).const_mul b)]
      rw [l1, l2, E1, E2]
      ring
  -- bounded pointwise limits
  have hlim : ∀ (φs : ℕ → ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℝ) (M : ℝ), 0 ≤ M →
      (∀ k, Measurable (φs k)) → (∀ k x, |φs k x| ≤ M) →
      (∀ x, Tendsto (fun k => φs k x) atTop (𝓝 (φ x))) → (∀ k, H (φs k)) → H φ := by
    intro φs φ M hM hm hb hconv hHs
    have hφb : ∀ x, |φ x| ≤ M := fun x =>
      le_of_tendsto' (hconv x).abs (fun k => hb k x)
    have hint : ∀ (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ],
        Tendsto (fun k => ∫ x, φs k x ∂μ) atTop (𝓝 (∫ x, φ x ∂μ)) := by
      intro μ _
      exact tendsto_integral_of_dominated_convergence (fun _ => M)
        (fun k => (hm k).aestronglyMeasurable) (integrable_const M)
        (fun k => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb k x)
        (ae_of_all _ hconv)
    have hF : ∀ σ ∈ Icc 0 (Tstar p), Tendsto (fun k => fieldOp p.h d ζ (χ σ) (φs k)) atTop
        (𝓝 (fieldOp p.h d ζ (χ σ) φ)) := by
      intro σ hσ
      have hadm := hχ σ hσ
      haveI := hadm.1
      have hr : 0 < riskOf (χ σ) := by linarith [hadm.2.2.2.1, p.hr0]
      have hres : (χ σ).restrict (specRect p.CSig) = χ σ :=
        Measure.restrict_eq_self_of_ae_mem (continuum_ae_K hadm.2.1)
      have hdm : AEStronglyMeasurable d (χ σ) := by
        rw [← hres]
        exact hd.aestronglyMeasurable (continuum_K_meas _)
      have h1 : Tendsto (fun k => ∫ x, φs k x * d x ∂(χ σ)) atTop
          (𝓝 (∫ x, φ x * d x ∂(χ σ))) :=
        tendsto_integral_of_dominated_convergence (fun _ => M * dMax p)
          (fun k => (hm k).aestronglyMeasurable.mul hdm) (integrable_const _)
          (fun k => by
            filter_upwards [continuum_ae_K hadm.2.1] with x hx
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hdb x hx).1]
            exact mul_le_mul (hb k x) (hdb x hx).2 (hdb x hx).1 hM)
          (ae_of_all _ fun x => (hconv x).mul_const _)
      unfold fieldOp
      simp only [if_pos hr]
      exact (h1.const_mul _).add ((hint ζ).const_mul _)
    set Cb := 2 * p.h / Real.sqrt (p.r0 / 2) * (M * dMax p * (p.Estar + 1)) +
      p.h ^ 2 * (M * ζ.real univ) with hCb
    have hFb : ∀ ψ : ℝ × ℝ → ℝ, (∀ x, |ψ x| ≤ M) → ∀ σ ∈ Icc 0 (Tstar p),
        |fieldOp p.h d ζ (χ σ) ψ| ≤ Cb :=
      fun ψ hψ σ hσ => continuum_field_bdd hdb ζ (χ σ) (hχ σ hσ) hM hψ
    have hmeas : ∀ k, AEStronglyMeasurable (fun σ => fieldOp p.h d ζ (χ σ) (φs k))
        (volume.restrict (Set.uIoc 0 τ)) :=
      fun k => (intervalIntegrable_iff.1 ((hH _).1 (hHs k)).1).aestronglyMeasurable
    have hlimae : ∀ᵐ σ ∂(volume.restrict (Set.uIoc 0 τ)), Tendsto
        (fun k => fieldOp p.h d ζ (χ σ) (φs k)) atTop (𝓝 (fieldOp p.h d ζ (χ σ) φ)) :=
      ae_restrict_of_forall_mem measurableSet_uIoc fun σ hσ => hF σ (hsub' σ hσ)
    have hI : IntervalIntegrable (fun σ => fieldOp p.h d ζ (χ σ) φ) volume 0 τ :=
      (intervalIntegrable_const (c := Cb)).mono_fun
        (aestronglyMeasurable_of_tendsto_ae atTop hmeas hlimae)
        (ae_restrict_of_forall_mem measurableSet_uIoc fun σ hσ => by
          simp only [Real.norm_eq_abs]
          exact (hFb φ hφb σ (hsub' σ hσ)).trans (le_abs_self _))
    refine (hH φ).2 ⟨hI, ?_⟩
    have hR := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => Cb)
      (Eventually.of_forall hmeas)
      (Eventually.of_forall fun k => ae_of_all _ fun σ hσ => by
        rw [Real.norm_eq_abs]; exact hFb _ (hb k) σ (hsub' σ hσ))
      (intervalIntegrable_const (c := Cb))
      (ae_of_all _ fun σ hσ => hF σ (hsub' σ hσ))
    have hL := hint (χ τ)
    have hR' := (hint χ0).add hR
    have heq : ∀ k, ∫ x, φs k x ∂(χ τ) =
        ∫ x, φs k x ∂χ0 + ∫ σ in (0 : ℝ)..τ, fieldOp p.h d ζ (χ σ) (φs k) :=
      fun k => ((hH _).1 (hHs k)).2
    simp only [heq] at hL
    exact tendsto_nhds_unique hL hR'
  -- indicators of closed sets
  have hclosed : ∀ F : Set (ℝ × ℝ), IsClosed F → H (F.indicator (fun _ => (1 : ℝ))) := by
    intro F hF
    have hpos : ∀ k : ℕ, 0 < (1 : ℝ) / (k + 1) := fun k => Nat.one_div_pos_of_nat
    have hthick : ∀ k : ℕ, H (fun x => (thickenedIndicator (hpos k) F x : ℝ)) := by
      intro k
      obtain ⟨hc, hb, hmem⟩ := continuum_thick_test (Cs := p.CSig) (hpos k) F
      have h1 := (hH _).2 (hbase _ hc hb hmem)
      have hs0 : 0 < min 1 ((1 : ℝ) / (k + 1)) := lt_min one_pos (hpos k)
      have h2 := hlin _ _ 1 1 hc.measurable hb hc.measurable hb h1 h1
        (1 / min 1 ((1 : ℝ) / (k + 1))) 0
      convert h2 using 1
      funext x
      field_simp
      ring
    refine hlim _ _ 1 zero_le_one (fun k => (NNReal.continuous_coe.comp
        (thickenedIndicator (hpos k) F).continuous).measurable) (fun k x => ?_) (fun x => ?_)
      hthick
    · have h1 : (thickenedIndicator (hpos k) F x : ℝ) ≤ 1 := by
        exact_mod_cast thickenedIndicator_le_one (hpos k) F x
      show |(thickenedIndicator (hpos k) F x : ℝ)| ≤ 1
      rw [abs_of_nonneg (NNReal.coe_nonneg _)]
      exact h1
    · have hl := thickenedIndicator_tendsto_indicator_closure hpos
        tendsto_one_div_add_atTop_nhds_zero_nat F
      rw [hF.closure_eq, tendsto_pi_nhds] at hl
      have hx := (NNReal.continuous_coe.tendsto _).comp (hl x)
      have hval : ((F.indicator (fun _ => (1 : NNReal)) x : NNReal) : ℝ) =
          F.indicator (fun _ => (1 : ℝ)) x := by
        by_cases hxF : x ∈ F <;> simp [hxF]
      rw [hval] at hx
      exact hx
  -- indicators of measurable sets (Dynkin)
  have hsets : ∀ s : Set (ℝ × ℝ), MeasurableSet s → H (s.indicator (fun _ => (1 : ℝ))) := by
    have hind_b : ∀ s : Set (ℝ × ℝ), ∀ x, |s.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
      intro s x
      by_cases hx : x ∈ s <;> simp [hx]
    refine MeasurableSpace.induction_on_inter (C := fun s _ => H (s.indicator (fun _ => (1 : ℝ))))
      (s := {F | IsClosed F}) ?_ isPiSystem_isClosed ?_ ?_ ?_ ?_
    · rw [BorelSpace.measurable_eq (α := ℝ × ℝ), borel_eq_generateFrom_isClosed]
    · exact hclosed ∅ isClosed_empty
    · exact fun t ht => hclosed t ht
    · intro t htm ht
      have h := hlin _ _ 1 1 (measurable_const.indicator MeasurableSet.univ) (hind_b univ)
        (measurable_const.indicator htm) (hind_b t) (hclosed univ isClosed_univ) ht 1 (-1)
      convert h using 1
      funext x
      by_cases hx : x ∈ t <;> simp [hx]
    · intro f hdisj hfm hf
      set A : ℕ → Set (ℝ × ℝ) := fun N => ⋃ i ∈ Finset.range N, f i with hA
      have hAm : ∀ N, MeasurableSet (A N) := fun N =>
        Finset.measurableSet_biUnion _ fun i _ => hfm i
      have hAH : ∀ N, H ((A N).indicator (fun _ => (1 : ℝ))) := by
        intro N
        induction N with
        | zero =>
          have h0 : A 0 = ∅ := by simp [hA]
          rw [h0]
          exact hclosed ∅ isClosed_empty
        | succ N ih =>
          have hsplit : A (N + 1) = f N ∪ A N := by
            simp only [hA, Finset.range_add_one, Finset.set_biUnion_insert]
          have hdj : Disjoint (f N) (A N) := by
            rw [Set.disjoint_left]
            intro x hxN hxA
            simp only [hA, Set.mem_iUnion, Finset.mem_range] at hxA
            obtain ⟨i, hi, hxi⟩ := hxA
            exact Set.disjoint_left.1 (hdisj (ne_of_gt hi)) hxN hxi
          have h := hlin _ _ 1 1 (measurable_const.indicator (hfm N)) (hind_b _)
            (measurable_const.indicator (hAm N)) (hind_b _) (hf N) ih 1 1
          convert h using 1
          funext x
          rw [hsplit, Set.indicator_union_of_disjoint hdj]
          ring
      refine hlim _ _ 1 zero_le_one (fun N => measurable_const.indicator (hAm N))
        (fun N x => hind_b _ x) (fun x => ?_) hAH
      by_cases hx : x ∈ ⋃ i, f i
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        have hev : ∀ᶠ N in atTop, (A N).indicator (fun _ => (1 : ℝ)) x =
            (⋃ i, f i).indicator (fun _ => (1 : ℝ)) x := by
          refine eventually_atTop.2 ⟨i + 1, fun N hN => ?_⟩
          have hxA : x ∈ A N := by
            simp only [hA, Set.mem_iUnion, Finset.mem_range]
            exact ⟨i, by omega, hi⟩
          simp [hxA, hx]
        exact tendsto_const_nhds.congr' (hev.mono fun N h => h.symm)
      · have hev : ∀ N, (A N).indicator (fun _ => (1 : ℝ)) x =
            (⋃ i, f i).indicator (fun _ => (1 : ℝ)) x := by
          intro N
          have hxA : x ∉ A N := by
            intro hxA
            simp only [hA, Set.mem_iUnion, Finset.mem_range] at hxA
            obtain ⟨i, -, hxi⟩ := hxA
            exact hx (Set.mem_iUnion.2 ⟨i, hxi⟩)
          simp [hxA, hx]
        simp only [hev]
        exact tendsto_const_nhds
  -- simple functions
  have hsimple : ∀ f : SimpleFunc (ℝ × ℝ) ℝ, H f := by
    intro f
    induction f using SimpleFunc.induction with
    | const c hs =>
      have hb : ∀ x, |(‹Set (ℝ × ℝ)›).indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
        intro x
        by_cases hx : x ∈ ‹Set (ℝ × ℝ)› <;> simp [hx]
      have h := hlin _ _ 1 1 (measurable_const.indicator hs) hb (measurable_const.indicator hs) hb
        (hsets _ hs) (hsets _ hs) c 0
      convert h using 1
      funext x
      simp only [SimpleFunc.coe_piecewise, SimpleFunc.coe_const, Set.piecewise]
      by_cases hx : x ∈ ‹Set (ℝ × ℝ)› <;> simp [hx]
    | add hdisj hf hg =>
      rename_i f g
      obtain ⟨Cf, hCf⟩ := SimpleFunc.exists_forall_norm_le f
      obtain ⟨Cg, hCg⟩ := SimpleFunc.exists_forall_norm_le g
      have h := hlin _ _ Cf Cg f.measurable (fun x => by rw [← Real.norm_eq_abs]; exact hCf x)
        g.measurable (fun x => by rw [← Real.norm_eq_abs]; exact hCg x) hf hg 1 1
      convert h using 1
      funext x
      simp
  -- bounded measurable functions
  intro φ hφ ⟨M0, hM0⟩
  have hM : 0 ≤ max M0 0 := le_max_right _ _
  have hsm := hφ.stronglyMeasurable
  refine (hH φ).1 (hlim (fun k => hsm.approxBounded (max M0 0) k) φ (max M0 0) hM
    (fun k => (hsm.approxBounded (max M0 0) k).measurable)
    (fun k x => by rw [← Real.norm_eq_abs]; exact hsm.norm_approxBounded_le hM k x)
    (fun x => hsm.tendsto_approxBounded_of_norm_le (by
      rw [Real.norm_eq_abs]; exact (hM0 x).trans (le_max_left _ _)))
    (fun k => hsimple _))

private lemma continuum_bl_symm (Cs : ℝ) (μ ν : Measure (ℝ × ℝ)) :
    blDist Cs μ ν = blDist Cs ν μ := by
  have h : (fun φ : ℝ × ℝ → ℝ => |∫ x, φ x ∂μ - ∫ x, φ x ∂ν|) =
      (fun φ => |∫ x, φ x ∂ν - ∫ x, φ x ∂μ|) := funext fun φ => abs_sub_comm _ _
  unfold blDist blNorm
  rw [h]

private lemma continuum_bl_triangle {Cs : ℝ} (μ ν ρ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure ρ] (hμ : μ (specRect Cs)ᶜ = 0)
    (hν : ν (specRect Cs)ᶜ = 0) (hρ : ρ (specRect Cs)ᶜ = 0) :
    blDist Cs μ ρ ≤ blDist Cs μ ν + blDist Cs ν ρ :=
  continuum_bl_le_of μ ρ (add_nonneg (continuum_bl_nonneg _ _ _) (continuum_bl_nonneg _ _ _))
    fun φ hφ => (abs_sub_le _ (∫ x, φ x ∂ν) _).trans
      (add_le_add (continuum_bl_le μ ν hμ hν φ hφ) (continuum_bl_le ν ρ hν hρ φ hφ))

/-- Completeness of the carried-by-`K` measures with bounded mass for `blDist` (through the
compactness of `continuum_measure_compact_subseq`). -/
private lemma continuum_bl_complete {Cs : ℝ} (hCs : 0 ≤ Cs) (μ : ℕ → Measure (ℝ × ℝ))
    [hfin : ∀ n, IsFiniteMeasure (μ n)] (hK : ∀ n, μ n (specRect Cs)ᶜ = 0) (M : ℝ) (hM : 0 ≤ M)
    (hmass : ∀ n, (μ n).real univ ≤ M)
    (hC : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, blDist Cs (μ n) (μ m) ≤ ε) :
    ∃ ν : Measure (ℝ × ℝ), IsFiniteMeasure ν ∧ ν (specRect Cs)ᶜ = 0 ∧
      Tendsto (fun n => blDist Cs (μ n) ν) atTop (𝓝 0) := by
  have hKc : IsCompact (specRect Cs) := isCompact_Icc.prod isCompact_Icc
  have hx0 : ((0, 0) : ℝ × ℝ) ∈ specRect Cs := ⟨⟨le_rfl, hCs⟩, ⟨le_rfl, hCs⟩⟩
  obtain ⟨ν, j, hj, -, hνK, hνw⟩ := continuum_measure_compact_subseq (specRect Cs) hKc (0, 0)
    hx0 (Real.toNNReal M) μ hfin (fun n => continuum_mass_le_toNNReal _ _ M hM (hmass n)) hK
  have hsub : Tendsto (fun n => blDist Cs (μ (j n)) (ν : Measure (ℝ × ℝ))) atTop (𝓝 0) :=
    continuum_bl_of_weak hCs (fun n => μ (j n)) ν (fun n => hK _) hνK ⟨M, fun n => hmass _⟩ hνw
  refine ⟨ν, inferInstance, hνK, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hC (ε / 2) (by linarith)
  obtain ⟨N', hN'⟩ := (Metric.tendsto_atTop.1 hsub) (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hk := hN' (max N N') (le_max_right _ _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (continuum_bl_nonneg _ _ _)] at hk
  have hjk : N ≤ j (max N N') := (le_max_left N N').trans (hj.id_le _)
  have h1 := hN n hn (j (max N N')) hjk
  have h2 := continuum_bl_triangle (μ n) (μ (j (max N N'))) ν (hK n) (hK _) hνK
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (continuum_bl_nonneg _ _ _)]
  linarith

private lemma continuum_int_tendsto_of_bl {Cs A : ℝ} (hA : 0 < A) (g : ℝ × ℝ → ℝ)
    (hg1 : ∀ x ∈ specRect Cs, |g x| ≤ A)
    (hg2 : ∀ x ∈ specRect Cs, ∀ y ∈ specRect Cs, |g x - g y| ≤ A * l1 x y)
    (μ : ℕ → Measure (ℝ × ℝ)) [∀ n, IsFiniteMeasure (μ n)] (ν : Measure (ℝ × ℝ))
    [IsFiniteMeasure ν] (hμ : ∀ n, μ n (specRect Cs)ᶜ = 0) (hν : ν (specRect Cs)ᶜ = 0)
    (h : Tendsto (fun n => blDist Cs (μ n) ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, g x ∂(μ n)) atTop (𝓝 (∫ x, g x ∂ν)) := by
  have hmem : (fun x => g x / A) ∈ blTest Cs := by
    refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
    · rw [abs_div, abs_of_pos hA, div_le_one hA]
      exact hg1 x hx
    · rw [← sub_div, abs_div, abs_of_pos hA, div_le_iff₀ hA, mul_comm]
      exact hg2 x hx y hy
  have hb : ∀ n, |∫ x, g x ∂(μ n) - ∫ x, g x ∂ν| ≤ A * blDist Cs (μ n) ν := by
    intro n
    have h1 := continuum_bl_le (μ n) ν (hμ n) hν _ hmem
    rw [integral_div, integral_div, ← sub_div, abs_div, abs_of_pos hA, div_le_iff₀ hA] at h1
    linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 := h.const_mul A
  rw [mul_zero] at h2
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hb n) h2

private lemma continuum_adm_of_bl (μ : ℕ → Measure (ℝ × ℝ)) (hμ : ∀ n, μ n ∈ admMeasures p)
    (ν : Measure (ℝ × ℝ)) [IsFiniteMeasure ν] (hν : ν (specRect p.CSig)ᶜ = 0)
    (h : Tendsto (fun n => blDist p.CSig (μ n) ν) atTop (𝓝 0)) : ν ∈ admMeasures p := by
  haveI : ∀ n, IsFiniteMeasure (μ n) := fun n => (hμ n).1
  have hCs : 1 ≤ p.CSig := p.hC
  have hg1 : ∀ x ∈ specRect p.CSig, |(fun _ : ℝ × ℝ => (1 : ℝ)) x| ≤ 1 := fun x _ => by simp
  have hg2 : ∀ x ∈ specRect p.CSig, ∀ y ∈ specRect p.CSig,
      |(fun _ : ℝ × ℝ => (1 : ℝ)) x - (fun _ : ℝ × ℝ => (1 : ℝ)) y| ≤ 1 * l1 x y :=
    fun x _ y _ => by
      simp only [sub_self, abs_zero, one_mul]
      exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have h1 := continuum_int_tendsto_of_bl one_pos (fun _ => (1 : ℝ)) hg1 hg2 μ ν
    (fun n => (hμ n).2.1) hν h
  simp only [integral_const, smul_eq_mul, mul_one] at h1
  have h2 := continuum_int_tendsto_of_bl (A := p.CSig ^ 2 + p.CSig + 1) (by positivity)
    (fun x => x.1 * x.2) (fun x hx => by
      rw [abs_of_nonneg (mul_nonneg hx.1.1 hx.2.1)]
      nlinarith [hx.1.1, hx.1.2, hx.2.1, hx.2.2])
    (fun x hx y hy => by
      have e : x.1 * x.2 - y.1 * y.2 = x.1 * (x.2 - y.2) + y.2 * (x.1 - y.1) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hx.1.1, abs_of_nonneg hy.2.1]
      unfold l1
      nlinarith [abs_nonneg (x.2 - y.2), abs_nonneg (x.1 - y.1), hx.1.2, hy.2.2,
        mul_le_mul_of_nonneg_right hx.1.2 (abs_nonneg (x.2 - y.2)),
        mul_le_mul_of_nonneg_right hy.2.2 (abs_nonneg (x.1 - y.1))])
    μ ν (fun n => (hμ n).2.1) hν h
  have hR : Tendsto (fun n => riskOf (μ n)) atTop (𝓝 (riskOf ν)) := by
    unfold riskOf
    exact h2.const_mul _
  refine ⟨inferInstance, hν, ?_, ?_, ?_⟩
  · exact isClosed_Iic.mem_of_tendsto h1 (Eventually.of_forall fun n => (hμ n).2.2.1)
  · exact isClosed_Ici.mem_of_tendsto hR (Eventually.of_forall fun n => (hμ n).2.2.2.1)
  · exact isClosed_Iic.mem_of_tendsto hR (Eventually.of_forall fun n => (hμ n).2.2.2.2)

private lemma continuum_eq_of_bl_lim {Cs : ℝ} (μ : ℕ → Measure (ℝ × ℝ))
    [∀ n, IsFiniteMeasure (μ n)] (hμ : ∀ n, μ n (specRect Cs)ᶜ = 0) (ν ν' : Measure (ℝ × ℝ))
    [IsFiniteMeasure ν] [IsFiniteMeasure ν'] (hν : ν (specRect Cs)ᶜ = 0)
    (hν' : ν' (specRect Cs)ᶜ = 0) (h : Tendsto (fun n => blDist Cs (μ n) ν) atTop (𝓝 0))
    (h' : Tendsto (fun n => blDist Cs (μ n) ν') atTop (𝓝 0)) : ν = ν' := by
  apply continuum_ext_of_bl (Cs := Cs)
  intro φ hφ
  have key : ∀ n, |∫ x, φ x ∂ν - ∫ x, φ x ∂ν'| ≤ blDist Cs (μ n) ν + blDist Cs (μ n) ν' := by
    intro n
    have h1 := continuum_bl_le (μ n) ν (hμ n) hν φ hφ
    have h2 := continuum_bl_le (μ n) ν' (hμ n) hν' φ hφ
    have h3 := abs_sub_le (∫ x, φ x ∂ν) (∫ x, φ x ∂(μ n)) (∫ x, φ x ∂ν')
    have h4 := abs_sub_comm (∫ x, φ x ∂ν) (∫ x, φ x ∂(μ n))
    linarith
  have hlim := h.add h'
  rw [add_zero] at hlim
  exact sub_eq_zero.1 (abs_nonpos_iff.1 (ge_of_tendsto hlim (Eventually.of_forall key)))

/-- A path solving a weak equation with bounded field is Lipschitz for `blDist`. -/
private lemma continuum_path_bl_lip {d : ℝ × ℝ → ℝ}
    (hdb : ∀ x ∈ specRect p.CSig, 0 ≤ d x ∧ d x ≤ dMax p) (ζ : Measure (ℝ × ℝ))
    [IsFiniteMeasure ζ] (ψ : ℝ → Measure (ℝ × ℝ))
    (hψ : ∀ τ ∈ Icc 0 (Tstar p), ψ τ ∈ admMeasures p)
    (hψeq : ∀ φ : ℝ × ℝ → ℝ, Measurable φ → (∃ M0 : ℝ, ∀ x, |φ x| ≤ M0) →
      ∀ τ ∈ Icc 0 (Tstar p),
        IntervalIntegrable (fun σ => fieldOp p.h d ζ (ψ σ) φ) volume 0 τ ∧
        ∫ x, φ x ∂(ψ τ) = ∫ x, φ x ∂(ψ 0) + ∫ σ in (0 : ℝ)..τ, fieldOp p.h d ζ (ψ σ) φ)
    (σ τ : ℝ) (hσ : σ ∈ Icc 0 (Tstar p)) (hτ : τ ∈ Icc 0 (Tstar p)) :
    blDist p.CSig (ψ σ) (ψ τ) ≤ (2 * p.h / Real.sqrt (p.r0 / 2) * (1 * dMax p * (p.Estar + 1)) +
      p.h ^ 2 * (1 * ζ.real univ)) * |σ - τ| := by
  have hCs : 0 ≤ p.CSig := by linarith [p.hC]
  have hhpos := p.hh
  have hEs := p.hE
  have hdM := half_dMax_nonneg p
  have hζ0 : 0 ≤ ζ.real univ := measureReal_nonneg
  haveI := (hψ σ hσ).1
  haveI := (hψ τ hτ).1
  apply continuum_bl_le_of _ _ (mul_nonneg (by positivity) (abs_nonneg _))
  intro φ0 hφ0
  obtain ⟨φ, hφc, hφb, hφ, hφeq⟩ := continuum_test_ext hCs φ0 hφ0
  rw [continuum_integral_congr_K (fun x hx => (hφeq x hx).symm) (ψ σ) (hψ σ hσ).2.1,
    continuum_integral_congr_K (fun x hx => (hφeq x hx).symm) (ψ τ) (hψ τ hτ).2.1]
  obtain ⟨I1, E1⟩ := hψeq φ hφc.measurable ⟨1, hφb⟩ σ hσ
  obtain ⟨I2, E2⟩ := hψeq φ hφc.measurable ⟨1, hφb⟩ τ hτ
  rw [E1, E2, add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left I1 I2]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := τ) (b := σ)
    (f := fun u => fieldOp p.h d ζ (ψ u) φ)
    (C := 2 * p.h / Real.sqrt (p.r0 / 2) * (1 * dMax p * (p.Estar + 1)) +
      p.h ^ 2 * (1 * ζ.real univ)) (fun u hu => by
        have hu' : u ∈ Icc 0 (Tstar p) := Set.uIcc_subset_Icc hτ hσ (Set.uIoc_subset_uIcc hu)
        rw [Real.norm_eq_abs]
        exact continuum_field_bdd hdb ζ (ψ u) (hψ u hu') zero_le_one hφb)
  rw [Real.norm_eq_abs] at h
  exact h

/-- Existence of a solution of the measure equation, as the `blDist` limit of `χ^ode_B`. -/
private lemma continuum_exists (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (ι : ℕ → ℕ) (dinf : ℝ × ℝ → ℝ) (ζinf χ0 : Measure (ℝ × ℝ))
    (hL : contLimit hyp S c ι dinf ζinf χ0)
    (e : ∀ k : ℕ, ℝ → Fin (m k) → Fin (n k) → ℝ)
    (he : ∀ k : ℕ, def_app_dyn_ode p (S k) (c k) (dev0 hyp k) (Tstar p) (e k)) :
    ∃ χ : ℝ → Measure (ℝ × ℝ), eqn_app_dyn_continuum p dinf ζinf χ0 χ := by
  have hT := half_Tstar_nonneg p
  have h0 : (0 : ℝ) ∈ Icc 0 (Tstar p) := ⟨le_rfl, hT⟩
  have hCs : 0 ≤ p.CSig := by linarith [p.hC]
  have hhpos := p.hh
  have hEs := p.hE
  have hdM := half_dMax_nonneg p
  have hmZ := half_mZeta_nonneg p
  obtain ⟨CF0, hCF0⟩ := lem_app_dyn_field_iii p (p.Estar + 1) (p.r0 / 2) (p.r1 + 1 / 2)
    (by linarith [p.hr0])
  set CF := max CF0 0 with hCFdef
  have hCFnn : 0 ≤ CF := le_max_right _ _
  have hCF : ∀ k, ∀ χ χ' : Measure (ℝ × ℝ), χ ∈ admMeasures p → χ' ∈ admMeasures p →
      BddAbove ((fun φ => |fieldOp p.h (c k).d (c k).ζ χ φ - fieldOp p.h (c k).d (c k).ζ χ' φ|) ''
        blTest p.CSig) ∧
      blNorm p.CSig (fun φ => fieldOp p.h (c k).d (c k).ζ χ φ - fieldOp p.h (c k).d (c k).ζ χ' φ)
        ≤ CF * blDist p.CSig χ χ' := by
    intro k χ χ' h1 h2
    obtain ⟨hb, hle⟩ := hCF0 (S k) (c k) χ χ' h1 h2
    exact ⟨hb, hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (continuum_bl_nonneg _ _ _))⟩
  have hζfin : ∀ k, IsFiniteMeasure (c k).ζ := fun k => by
    rw [(c k).ζ_eq]
    exact continuum_atom_isFinite _ _ _
  have hζK : ∀ k, (c k).ζ (specRect p.CSig)ᶜ = 0 := fun k => by
    rw [(c k).ζ_eq]
    exact continuum_atom_support (S k) _ p.CSig (hyp.normBd k).2 (hyp.normBd k).1
  haveI := hL.2.1.1
  haveI := hL.2.2.1
  have hζinfK := hL.2.1.2.1
  have hχ0K := hL.2.2.2.1
  have hdc := continuum_limit_d_continuousOn S c hyp ι dinf ζinf χ0 hL
  have hdb := continuum_limit_d_bounds S c hyp ι dinf ζinf χ0 hL
  have hζinfm := continuum_limit_zeta_mass S c hyp ι dinf ζinf χ0 hL
  have hdcK : ∀ k, ContinuousOn (c k).d (specRect p.CSig) := fun k =>
    continuum_local_lip_cont (div_nonneg hCs (Real.sqrt_nonneg _)) (c k).d_lip
  have hdbK : ∀ k, ∀ x ∈ specRect p.CSig, 0 ≤ (c k).d x ∧ (c k).d x ≤ dMax p :=
    fun k x hx => ⟨(c k).d_nonneg x hx, (c k).d_le x hx⟩
  set ψ : ℕ → ℝ → Measure (ℝ × ℝ) := fun n τ =>
    odeMeasure (((B (ι n) : ℕ) : ℝ)) (S (ι n)).μ (S (ι n)).lam (e (ι n) τ) with hψdef
  have hψadm : ∀ n, ∀ τ ∈ Icc 0 (Tstar p), ψ n τ ∈ admMeasures p :=
    fun n => (continuum_ode_facts F hyp S c e he (ι n)).1
  have hψeq := fun n => (continuum_ode_facts F hyp S c e he (ι n)).2.1
  have hψ0 : ∀ n, ψ n 0 = specMeasure (S (ι n)) (dev0 hyp (ι n)) :=
    fun n => (continuum_ode_facts F hyp S c e he (ι n)).2.2
  -- convergence of the initial data and of the forcing in `blDist`
  haveI : ∀ n, IsFiniteMeasure (specMeasure (S (ι n)) (dev0 hyp (ι n))) := fun n => by
    unfold specMeasure
    exact continuum_atom_isFinite _ _ _
  have hαlim : Tendsto (fun n => blDist p.CSig (specMeasure (S (ι n)) (dev0 hyp (ι n))) χ0)
      atTop (𝓝 0) :=
    continuum_bl_of_weak hCs _ χ0 (fun n => by
        unfold specMeasure
        exact continuum_atom_support (S (ι n)) _ p.CSig (hyp.normBd _).2 (hyp.normBd _).1)
      hχ0K ⟨p.Estar, fun n => by rw [continuum_spec_mass]; exact hyp.W0_norm _⟩
      hL.2.2.2.2
  have hαlim' : Tendsto (fun n => blDist p.CSig (ψ n 0) χ0) atTop (𝓝 0) := by
    simp only [hψ0]
    exact hαlim
  haveI : ∀ n, IsFiniteMeasure (c (ι n)).ζ := fun n => hζfin _
  have hzlim : Tendsto (fun n => blDist p.CSig (c (ι n)).ζ ζinf) atTop (𝓝 0) :=
    continuum_bl_of_weak hCs _ ζinf (fun n => hζK _) hζinfK
      ⟨mZeta p, fun n => (c (ι n)).ζ_mass⟩ hL.2.1.2.2
  set c1 := 2 * p.h / Real.sqrt (p.r0 / 2) with hc1
  have hc1nn : 0 ≤ c1 := by positivity
  set c2 := 2 * Real.exp ((2 * CF + 1) * Tstar p) *
    (1 + (c1 * (p.Estar + 1) + p.h ^ 2) * Tstar p) with hc2
  have hexp := Real.exp_pos ((2 * CF + 1) * Tstar p)
  have hc2nn : 0 ≤ c2 := by
    have : 0 ≤ (c1 * (p.Estar + 1) + p.h ^ 2) * Tstar p :=
      mul_nonneg (by positivity) hT
    positivity
  -- uniform Cauchy property of `χ^ode`
  have hCauchy : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∀ τ ∈ Icc 0 (Tstar p),
      blDist p.CSig (ψ n τ) (ψ m τ) ≤ ε := by
    intro ε hε
    set η := ε / (2 * c2 + 1) with hη
    have hηpos : 0 < η := div_pos hε (by linarith)
    have ev1 := (Metric.tendsto_nhds.1 hαlim') η hηpos
    have ev2 := (Metric.tendsto_nhds.1 hzlim) η hηpos
    have ev3 := Metric.tendstoUniformlyOn_iff.1 hL.1 η hηpos
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((ev1.and ev2).and ev3)
    refine ⟨N, fun n hn m hm τ hτ => ?_⟩
    obtain ⟨⟨hαn, hzn⟩, hdn⟩ := hN n hn
    obtain ⟨⟨hαm, hzm⟩, hdm⟩ := hN m hm
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (continuum_bl_nonneg _ _ _)] at hαn hzn hαm hzm
    have hψn0 := hψadm n 0 h0
    have hψm0 := hψadm m 0 h0
    haveI := hψn0.1
    haveI := hψm0.1
    have hα : blDist p.CSig (ψ n 0) (ψ m 0) ≤ 2 * η := by
      have := continuum_bl_triangle (ψ n 0) χ0 (ψ m 0) hψn0.2.1 hχ0K hψm0.2.1
      rw [continuum_bl_symm p.CSig χ0 (ψ m 0)] at this
      linarith
    have hz : blDist p.CSig (c (ι n)).ζ (c (ι m)).ζ ≤ 2 * η := by
      have := continuum_bl_triangle (c (ι n)).ζ ζinf (c (ι m)).ζ (hζK _) hζinfK (hζK _)
      rw [continuum_bl_symm p.CSig ζinf (c (ι m)).ζ] at this
      linarith
    have hδ : ∀ x ∈ specRect p.CSig, |(c (ι n)).d x - (c (ι m)).d x| ≤ 2 * η := by
      intro x hx
      have h1 := hdn x hx
      have h2 := hdm x hx
      rw [Real.dist_eq] at h1 h2
      have h3 := abs_sub_le ((c (ι n)).d x) (dinf x) ((c (ι m)).d x)
      rw [abs_sub_comm ((c (ι n)).d x) (dinf x)] at h3
      linarith
    have hcomp := continuum_compare (S (ι n)) (c (ι n)) CF hCFnn (hCF (ι n)) (hζK (ι n))
      (c (ι m)).d (hdcK _) (hdbK _) (c (ι m)).ζ (ψ m 0) (hζK (ι m)) (ψ n) (hψadm n) (hψeq n)
      (ψ m) rfl (hψadm m) (fun τ hτ φ hφ hb => hψeq m φ hφ hb τ hτ) (2 * η) (2 * η) hα hδ
    refine (hcomp τ hτ).trans ?_
    have h1 : p.h ^ 2 * blDist p.CSig (c (ι n)).ζ (c (ι m)).ζ ≤ p.h ^ 2 * (2 * η) :=
      mul_le_mul_of_nonneg_left hz (sq_nonneg _)
    have h2 : (c1 * (2 * η * (p.Estar + 1)) + p.h ^ 2 * blDist p.CSig (c (ι n)).ζ (c (ι m)).ζ) *
        Tstar p ≤ (c1 * (2 * η * (p.Estar + 1)) + p.h ^ 2 * (2 * η)) * Tstar p :=
      mul_le_mul_of_nonneg_right (by linarith) hT
    have h3 := mul_le_mul_of_nonneg_right (add_le_add_left h2 (2 * η))
      (mul_nonneg zero_le_two hexp.le)
    have h4 : 2 * η * c2 ≤ ε := by
      have e : 2 * η * c2 = ε * (2 * c2) / (2 * c2 + 1) := by rw [hη]; ring
      rw [e, div_le_iff₀ (by linarith)]
      nlinarith
    rw [hc2] at h4
    nlinarith
  -- the limit measures
  have hlimτ : ∀ τ : ℝ, ∃ ν : Measure (ℝ × ℝ), IsFiniteMeasure ν ∧ ν (specRect p.CSig)ᶜ = 0 ∧
      (τ ∈ Icc 0 (Tstar p) → Tendsto (fun n => blDist p.CSig (ψ n τ) ν) atTop (𝓝 0)) := by
    intro τ
    by_cases hτ : τ ∈ Icc 0 (Tstar p)
    · haveI : ∀ n, IsFiniteMeasure (ψ n τ) := fun n => (hψadm n τ hτ).1
      obtain ⟨ν, hνf, hνK, hν⟩ := continuum_bl_complete hCs (fun n => ψ n τ)
        (fun n => (hψadm n τ hτ).2.1) (p.Estar + 1) (by linarith)
        (fun n => (hψadm n τ hτ).2.2.1) (fun ε hε => by
          obtain ⟨N, hN⟩ := hCauchy ε hε
          exact ⟨N, fun n hn m hm => hN n hn m hm τ hτ⟩)
      exact ⟨ν, hνf, hνK, fun _ => hν⟩
    · exact ⟨0, inferInstance, by simp, fun h => absurd h hτ⟩
  choose χ hχfin hχK hχlim using hlimτ
  have hχadm : ∀ τ ∈ Icc 0 (Tstar p), χ τ ∈ admMeasures p := fun τ hτ => by
    haveI := hχfin τ
    exact continuum_adm_of_bl (fun n => ψ n τ) (fun n => hψadm n τ hτ) (χ τ) (hχK τ)
      (hχlim τ hτ)
  have hχ0 : χ 0 = χ0 := by
    haveI := hχfin 0
    haveI : ∀ n, IsFiniteMeasure (ψ n 0) := fun n => (hψadm n 0 h0).1
    exact continuum_eq_of_bl_lim (fun n => ψ n 0) (fun n => (hψadm n 0 h0).2.1) (χ 0) χ0
      (hχK 0) hχ0K (hχlim 0 h0) hαlim'
  set Cb := c1 * (1 * dMax p * (p.Estar + 1)) + p.h ^ 2 * (1 * mZeta p) with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  refine ⟨χ, hχ0, hχadm, ?_, ?_⟩
  · -- continuity for `blDist`
    have hlip : ∀ σ ∈ Icc 0 (Tstar p), ∀ τ ∈ Icc 0 (Tstar p),
        blDist p.CSig (χ σ) (χ τ) ≤ Cb * |σ - τ| := by
      intro σ hσ τ hτ
      haveI := hχfin σ
      haveI := hχfin τ
      apply continuum_bl_le_of _ _ (mul_nonneg hCb0 (abs_nonneg _))
      intro φ hφ
      have key : ∀ n, |∫ x, φ x ∂(χ σ) - ∫ x, φ x ∂(χ τ)| ≤
          blDist p.CSig (ψ n σ) (χ σ) + blDist p.CSig (ψ n τ) (χ τ) + Cb * |σ - τ| := by
        intro n
        haveI := (hψadm n σ hσ).1
        haveI := (hψadm n τ hτ).1
        haveI := hζfin (ι n)
        have h1 := continuum_bl_le (ψ n σ) (χ σ) (hψadm n σ hσ).2.1 (hχK σ) φ hφ
        have h2 := continuum_bl_le (ψ n τ) (χ τ) (hψadm n τ hτ).2.1 (hχK τ) φ hφ
        have h3 := (continuum_bl_le (ψ n σ) (ψ n τ) (hψadm n σ hσ).2.1 (hψadm n τ hτ).2.1 φ
          hφ).trans (continuum_path_bl_lip (hdbK _) (c (ι n)).ζ (ψ n) (hψadm n) (hψeq n)
            σ τ hσ hτ)
        have h4 : (c1 * (1 * dMax p * (p.Estar + 1)) + p.h ^ 2 * (1 * (c (ι n)).ζ.real univ)) *
            |σ - τ| ≤ Cb * |σ - τ| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          have := mul_le_mul_of_nonneg_left (c (ι n)).ζ_mass (sq_nonneg p.h)
          linarith
        have h5 := abs_sub_le (∫ x, φ x ∂(χ σ)) (∫ x, φ x ∂(ψ n σ)) (∫ x, φ x ∂(χ τ))
        have h6 := abs_sub_le (∫ x, φ x ∂(ψ n σ)) (∫ x, φ x ∂(ψ n τ)) (∫ x, φ x ∂(χ τ))
        have h7 := abs_sub_comm (∫ x, φ x ∂(χ σ)) (∫ x, φ x ∂(ψ n σ))
        linarith
      have hlim := ((hχlim σ hσ).add (hχlim τ hτ)).add_const (Cb * |σ - τ|)
      rw [add_zero, zero_add] at hlim
      exact ge_of_tendsto hlim (Eventually.of_forall key)
    intro τ hτ ε hε
    refine ⟨ε / (Cb + 1), div_pos hε (by linarith), fun σ hσ hστ => ?_⟩
    calc blDist p.CSig (χ σ) (χ τ) ≤ Cb * |σ - τ| := hlip σ hσ τ hτ
      _ ≤ Cb * (ε / (Cb + 1)) := mul_le_mul_of_nonneg_left hστ.le hCb0
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  · -- the weak equation
    intro τ hτ
    apply continuum_weak_extend hdc hdb ζinf χ0 hζinfK χ hχadm τ hτ
    intro φ hφc hφb hφ
    have hsub' : ∀ σ ∈ Set.uIoc 0 τ, σ ∈ Icc 0 (Tstar p) := fun σ hσ => by
      rw [uIoc_of_le hτ.1] at hσ
      exact ⟨hσ.1.le, hσ.2.trans hτ.2⟩
    -- pointwise convergence of the fields
    have hFconv : ∀ σ ∈ Icc 0 (Tstar p), Tendsto
        (fun n => fieldOp p.h (c (ι n)).d (c (ι n)).ζ (ψ n σ) φ) atTop
        (𝓝 (fieldOp p.h dinf ζinf (χ σ) φ)) := by
      intro σ hσ
      rw [Metric.tendsto_atTop]
      intro ε hε
      set η := ε / (CF + c1 * (p.Estar + 1) + p.h ^ 2 + 1) with hη
      have hηpos : 0 < η := div_pos hε (by positivity)
      have ev1 := (Metric.tendsto_nhds.1 (hχlim σ hσ)) η hηpos
      have ev2 := (Metric.tendsto_nhds.1 hzlim) η hηpos
      have ev3 := Metric.tendstoUniformlyOn_iff.1 hL.1 η hηpos
      obtain ⟨N, hN⟩ := eventually_atTop.1 ((ev1.and ev2).and ev3)
      refine ⟨N, fun n hn => ?_⟩
      obtain ⟨⟨h1, h2⟩, h3⟩ := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (continuum_bl_nonneg _ _ _)] at h1 h2
      obtain ⟨hbdd, hle⟩ := hCF (ι n) (ψ n σ) (χ σ) (hψadm n σ hσ) (hχadm σ hσ)
      have k1 : |fieldOp p.h (c (ι n)).d (c (ι n)).ζ (ψ n σ) φ -
          fieldOp p.h (c (ι n)).d (c (ι n)).ζ (χ σ) φ| ≤ CF * η :=
        ((le_csSup hbdd ⟨φ, hφ, rfl⟩).trans hle).trans
          (mul_le_mul_of_nonneg_left h1.le hCFnn)
      have k2 := continuum_field_coef_diff (c (ι n)) (hζK _) dinf hdc hdb ζinf hζinfK (χ σ)
        (hχadm σ hσ) φ hφc hφ η (fun x hx => by
          rw [abs_sub_comm, ← Real.dist_eq]; exact (h3 x hx).le)
      have k3 : p.h ^ 2 * blDist p.CSig (c (ι n)).ζ ζinf ≤ p.h ^ 2 * η :=
        mul_le_mul_of_nonneg_left h2.le (sq_nonneg _)
      rw [Real.dist_eq]
      have k4 := abs_sub_le (fieldOp p.h (c (ι n)).d (c (ι n)).ζ (ψ n σ) φ)
        (fieldOp p.h (c (ι n)).d (c (ι n)).ζ (χ σ) φ) (fieldOp p.h dinf ζinf (χ σ) φ)
      have k5 : η * (CF + c1 * (p.Estar + 1) + p.h ^ 2) < ε := by
        rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [sq_nonneg p.h]
      nlinarith
    -- bounds
    have hFb : ∀ n, ∀ σ ∈ Icc 0 (Tstar p),
        |fieldOp p.h (c (ι n)).d (c (ι n)).ζ (ψ n σ) φ| ≤ Cb := by
      intro n σ hσ
      have h := continuum_field_bdd (hdbK (ι n)) (c (ι n)).ζ (ψ n σ) (hψadm n σ hσ)
        zero_le_one hφb
      have := mul_le_mul_of_nonneg_left (c (ι n)).ζ_mass (sq_nonneg p.h)
      linarith
    have hFb' : ∀ σ ∈ Icc 0 (Tstar p), |fieldOp p.h dinf ζinf (χ σ) φ| ≤ Cb := by
      intro σ hσ
      have h := continuum_field_bdd hdb ζinf (χ σ) (hχadm σ hσ) zero_le_one hφb
      have := mul_le_mul_of_nonneg_left hζinfm (sq_nonneg p.h)
      linarith
    have hmeas : ∀ n, AEStronglyMeasurable
        (fun σ => fieldOp p.h (c (ι n)).d (c (ι n)).ζ (ψ n σ) φ)
        (volume.restrict (Set.uIoc 0 τ)) :=
      fun n => (intervalIntegrable_iff.1 (hψeq n φ hφc.measurable ⟨1, hφb⟩ τ hτ).1)
        |>.aestronglyMeasurable
    have hlimae : ∀ᵐ σ ∂(volume.restrict (Set.uIoc 0 τ)), Tendsto
        (fun n => fieldOp p.h (c (ι n)).d (c (ι n)).ζ (ψ n σ) φ) atTop
        (𝓝 (fieldOp p.h dinf ζinf (χ σ) φ)) :=
      ae_restrict_of_forall_mem measurableSet_uIoc fun σ hσ => hFconv σ (hsub' σ hσ)
    have hI : IntervalIntegrable (fun σ => fieldOp p.h dinf ζinf (χ σ) φ) volume 0 τ :=
      (intervalIntegrable_const (c := Cb)).mono_fun
        (aestronglyMeasurable_of_tendsto_ae atTop hmeas hlimae)
        (ae_restrict_of_forall_mem measurableSet_uIoc fun σ hσ => by
          simp only [Real.norm_eq_abs]
          exact (hFb' σ (hsub' σ hσ)).trans (le_abs_self _))
    refine ⟨hI, ?_⟩
    have hR := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => Cb)
      (Eventually.of_forall hmeas)
      (Eventually.of_forall fun n => ae_of_all _ fun σ hσ => by
        rw [Real.norm_eq_abs]; exact hFb n σ (hsub' σ hσ))
      (intervalIntegrable_const (c := Cb))
      (ae_of_all _ fun σ hσ => hFconv σ (hsub' σ hσ))
    haveI : ∀ n, IsFiniteMeasure (ψ n τ) := fun n => (hψadm n τ hτ).1
    haveI : ∀ n, IsFiniteMeasure (ψ n 0) := fun n => (hψadm n 0 h0).1
    haveI := hχfin τ
    have hg1 : ∀ x ∈ specRect p.CSig, |φ x| ≤ 1 := fun x _ => hφb x
    have hg2 : ∀ x ∈ specRect p.CSig, ∀ y ∈ specRect p.CSig, |φ x - φ y| ≤ 1 * l1 x y :=
      fun x hx y hy => by rw [one_mul]; exact hφ.2 x hx y hy
    have hL1 := continuum_int_tendsto_of_bl one_pos φ hg1 hg2 (fun n => ψ n τ) (χ τ)
      (fun n => (hψadm n τ hτ).2.1) (hχK τ) (hχlim τ hτ)
    have hL0 := continuum_int_tendsto_of_bl one_pos φ hg1 hg2 (fun n => ψ n 0) χ0
      (fun n => (hψadm n 0 h0).2.1) hχ0K hαlim'
    have heq : ∀ n, ∫ x, φ x ∂(ψ n τ) = ∫ x, φ x ∂(ψ n 0) +
        ∫ σ in (0 : ℝ)..τ, fieldOp p.h (c (ι n)).d (c (ι n)).ζ (ψ n σ) φ :=
      fun n => (hψeq n φ hφc.measurable ⟨1, hφb⟩ τ hτ).2
    simp only [heq] at hL1
    exact tendsto_nhds_unique hL1 (hL0.add hR)

/-- `cor:app-dyn-continuum`(ii), snapshot `cr-2026-10-23`. Deterministic part. Along any subsequence `ι` on which
the limits of (i) hold: the measure equation `eqn_app_dyn_continuum` has a solution on `[0, T⋆]`, the solution is
unique there, and `sup_τ ‖χ^ode_B(τ) − χ(τ)‖_BL → 0` where `χ^ode_B(τ) = odeMeasure B μ λ (e τ)` for the mode
solutions `e` of `def_app_dyn_ode` (unique by `prop_app_dyn_ode_i`). Arbitrary coefficient data `c`.

Source (`section.tex`, whole environment):
```latex
\begin{corollary}[Continuum equation]\label{cor:app-dyn-continuum}
Assume the hypotheses of \cref{thm:app-dyn-main}, and write $\mathfrak d_B$,
$\zeta_B$, $\chi^{\mathrm{act}}_B$, $\chi^{\mathrm{ode}}_B$ for the objects
at the dimension indexed by $B$.
\begin{enumerate}[label=(\roman*)]
\item Every sequence of dimensions has a subsequence along which $\mathfrak d_B\to\mathfrak d_\infty$
uniformly on $\mathbb K$, $\zeta_B\to\zeta_\infty$ weakly and
$\chi^{\mathrm{act}}_B(0)\to\chi_0$ weakly.
\item Along any such subsequence, the measure equation
\begin{equation}\label{eqn:app-dyn-continuum}
\chi(\macrotime)=\chi_0+\int_0^\macrotime\Big(-\frac{2\macrostep\,\mathfrak d_\infty\,\chi(\sigma)}{\sqrt{\fRisk(\chi(\sigma))}}+\macrostep^2\zeta_\infty\Big)\dif\sigma
\end{equation}
has a unique solution $\chi$ on $[0,T_\star]$ among paths with values in
$\mathfrak M$ that are continuous for the bounded-Lipschitz norm, and
\[
\sup_{\macrotime\le T_\star}\norm{\chi^{\mathrm{ode}}_B(\macrotime)-\chi(\macrotime)}_\BL\to0,\qquad
\sup_{\macrotime\le T_\star}\norm{\chi^{\mathrm{act}}_B(\macrotime)-\chi(\macrotime)}_\BL\to0\ \text{in probability}.
\]
\item Along any such subsequence,
$\sup_{\macrotime\le T_\star}\abs{\cR(\lfloor B\macrotime\rfloor)-\fRisk(\chi(\macrotime))}\to0$ in probability.
\end{enumerate}
\end{corollary}
```
Measure equation (`eqn:app-dyn-continuum`):
```latex
\begin{equation}\label{eqn:app-dyn-continuum}
\chi(\macrotime)=\chi_0+\int_0^\macrotime\Big(-\frac{2\macrostep\,\mathfrak d_\infty\,\chi(\sigma)}{\sqrt{\fRisk(\chi(\sigma))}}+\macrostep^2\zeta_\infty\Big)\dif\sigma
\end{equation}
```
-/
theorem cor_app_dyn_continuum_ii (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C)) (hB : Tendsto B atTop atTop)
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (ι : ℕ → ℕ) (hι : StrictMono ι) (dinf : ℝ × ℝ → ℝ) (ζinf χ0 : Measure (ℝ × ℝ))
    (hL : contLimit hyp S c ι dinf ζinf χ0)
    (e : ∀ k : ℕ, ℝ → Fin (m k) → Fin (n k) → ℝ)
    (he : ∀ k : ℕ, def_app_dyn_ode p (S k) (c k) (dev0 hyp k) (Tstar p) (e k)) :
    (∃ χ : ℝ → Measure (ℝ × ℝ), eqn_app_dyn_continuum p dinf ζinf χ0 χ) ∧
    (∀ χ χ' : ℝ → Measure (ℝ × ℝ), eqn_app_dyn_continuum p dinf ζinf χ0 χ →
      eqn_app_dyn_continuum p dinf ζinf χ0 χ' → ∀ τ ∈ Icc 0 (Tstar p), χ τ = χ' τ) ∧
    (∀ χ : ℝ → Measure (ℝ × ℝ), eqn_app_dyn_continuum p dinf ζinf χ0 χ →
      (∀ n : ℕ, BddAbove ((fun τ => blDist p.CSig
          (odeMeasure (((B (ι n) : ℕ) : ℝ)) (S (ι n)).μ (S (ι n)).lam (e (ι n) τ)) (χ τ)) ''
        Icc 0 (Tstar p))) ∧
      Tendsto (fun n : ℕ => sSup ((fun τ => blDist p.CSig
          (odeMeasure (((B (ι n) : ℕ) : ℝ)) (S (ι n)).μ (S (ι n)).lam (e (ι n) τ)) (χ τ)) ''
        Icc 0 (Tstar p))) atTop (𝓝 0)) := by
  exact ⟨continuum_exists F hyp S c ι dinf ζinf χ0 hL e he,
    continuum_unique F hyp S c ι dinf ζinf χ0 hL e he,
    fun χ hχ => continuum_ode_conv F hyp S c ι dinf ζinf χ0 hL e he χ hχ⟩

end Muon.Dynamics

end

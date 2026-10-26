import Muon.Oversampled.Model
import Muon.Drift.Mean

/-!
# Oversampled expected update (`cor:app-os-update`)

Snapshot `cr-2026-10-23`. Interface only: the definitions are upstream ones
(`Muon.Setup.Arot`, `Muon.Drift.EQ`, `Muon.Oversampled.thetaRidge`, `dOs`, `IsModelBranch`);
the proofs are `sorry`. The state `Δ_t` and the risk `𝓡(t)` enter through `Arot` and the
normalized-state identity `Â = Arot(Δ_t)/√(2𝓡(t))` of `eqn:app-setup-normalized`, which is the
source's own definition of them.

Uniform convergence is written as `∀ η > 0, ∀ᶠ k, ∀ ϱ ∈ [ϱ₋, ϱ₊], ‖·‖_F < η` rather than as a
`⨆`-supremum, so that no junk value of `iSup` on an unbounded range can enter.
-/

open MeasureTheory Set Filter Topology
open scoped MatrixOrder

namespace Muon.Oversampled

noncomputable section

/-- Standing hypotheses of `cor:app-os-update`: `assum:app-setup-regime` is the argument `R`;
`Σ_in = Id_{N_in}`; `ε_os = 3(1-β²)N_in/B ≤ ε̄ < 1` at every index; one half-anisotropic
branch per index solving the weighted system; and the state `Δ_t` with
`𝓡(t) = ‖Arot Δ_t‖_F²/2 > 0` and `Â = Arot Δ_t/√(2𝓡(t))`. -/
structure OsUpdateHyp (R : Muon.Setup.SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) (t : ℤ) where
  /-- `N_out ≥ 1` and `N_in ≥ 1` at every index (the source's standing `N_out, N_in ≥ 1`). -/
  hm : ∀ k, 1 ≤ R.m k
  hn : ∀ k, 1 ≤ R.n k
  /-- `Σ_in = Id` at every index. -/
  hSin : ∀ k, (R.F k).C.Sin = 1
  /-- The fixed bound `ε̄`. -/
  εbar : ℝ
  hεbar : εbar < 1
  /-- `ε_os ≤ ε̄` at every index. -/
  hε : ∀ k, epsOs R.β (gammaIn (R.n k) (R.B k)) ≤ εbar
  /-- The half-anisotropic branch of each index (`thm:app-os-limit`). -/
  br : ∀ k, HalfAnisoBranch R.β (gammaIn (R.n k) (R.B k)) (Muon.nuOut (R.F k).C (R.B k))
  /-- `br k` solves the weighted system at every `s > 0`. -/
  hbr : ∀ k, IsModelBranch (R.F k).C (R.B k) (R.F k).hB R.β (br k)
  /-- The state `Δ_t = W_t - W^*` at each index. -/
  Dt : ∀ k, Mat (R.m k) (R.n k)
  /-- The risk `𝓡(t)` at each index. -/
  cRt : ℕ → ℝ
  hcRpos : ∀ k, 0 < cRt k
  hcR : ∀ k, cRt k = (Muon.fro (Muon.Setup.Arot (R.F k).C (Dt k))) ^ 2 / 2
  /-- The normalized state `Â = Arot(Δ_t)/√(2𝓡(t))`. -/
  hA : ∀ k, (R.F k).A = (Real.sqrt (2 * cRt k))⁻¹ • Muon.Setup.Arot (R.F k).C (Dt k)

/-- The right-hand side of `eqn:app-os-update` at index `k` and ridge `ϱ`:
`√(B_eff/N_in) ϑ_ϱ(Σ_out) 𝔡^os_{ν̂_out,r}(Σ_out; ϱ/(s_2 γ_in)) Δ_t/√𝓡(t)`, with `r = N_out/N_in`. -/
def osUpdateTarget (R : Muon.Setup.SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) (t : ℤ) (H : OsUpdateHyp R Ω P t) (k : ℕ) (ϱ : ℝ) :
    Mat (R.m k) (R.n k) :=
  Real.sqrt (bEff R.β (R.B k) / (R.n k : ℝ)) •
    ((cfc (fun μ : ℝ => thetaRidge (H.br k) (nuHatOut (R.F k).C) ((R.m k : ℝ) / (R.n k : ℝ)) ϱ μ)
        (R.F k).C.Sout *
      cfc (fun μ : ℝ => dOs (nuHatOut (R.F k).C) ((R.m k : ℝ) / (R.n k : ℝ)) μ
        (sHat R.β (gammaIn (R.n k) (R.B k)) ϱ)) (R.F k).C.Sout) *
      ((Real.sqrt (H.cRt k))⁻¹ • H.Dt k))

/-! ### Private helpers for `cor_app_os_update_i` -/

private lemma pg_cfc_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (f : ℝ → ℝ)
    (i a : Fin n) :
    cfc f A i a = ∑ k, f (hA.eigenvalues k) *
      (hA.eigenvectorUnitary.1 i k * hA.eigenvectorUnitary.1 a k) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Unitary.conjStarAlgAut_apply]
  exact Finset.sum_congr rfl fun x _ => by ring

private lemma pg_cfc_mul_entry {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (f : ℝ → ℝ) (D : Matrix (Fin n) (Fin p) ℝ) (i : Fin n) (j : Fin p) :
    (cfc f A * D) i j = ∑ k, f (hA.eigenvalues k) *
      (∑ a, hA.eigenvectorUnitary.1 i k * hA.eigenvectorUnitary.1 a k * D a j) := by
  simp_rw [Matrix.mul_apply, pg_cfc_entry A hA f, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

private lemma pg_commute {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (g : ℝ → ℝ → ℝ) (c : ℝ) (D : Matrix (Fin n) (Fin p) ℝ)
    (hint : ∀ k, IntegrableOn (fun u => g u (hA.eigenvalues k)) (Ioi 0)) (i : Fin n) (j : Fin p) :
    c * ∫ u in Ioi (0 : ℝ), (cfc (g u) A * D) i j =
      (cfc (fun μ => c * ∫ u in Ioi (0 : ℝ), g u μ) A * D) i j := by
  simp_rw [pg_cfc_mul_entry A hA]
  rw [integral_finsetSum _ (fun k _ => (hint k).mul_const _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_const]
  ring

private lemma pg_eig_one {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsHermitian)
    (h1 : A = 1) (i : Fin k) : hA.eigenvalues i = 1 := by
  subst h1
  have hv := hA.mulVec_eigenvectorBasis i
  rw [Matrix.one_mulVec] at hv
  have hn := hA.eigenvectorBasis.orthonormal.1 i
  by_contra hne
  have h0 : (1 - hA.eigenvalues i) • (⇑(hA.eigenvectorBasis i)) = 0 := by
    rw [sub_smul, one_smul]; exact sub_eq_zero.2 hv
  rcases smul_eq_zero.1 h0 with h | h
  · exact hne (by linarith)
  · have h2 : hA.eigenvectorBasis i = 0 := by
      ext j
      exact congrFun h j
    rw [h2, norm_zero] at hn
    norm_num at hn

private lemma pg_specIn {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B) (hSin : F.C.Sin = 1) :
    Muon.Drift.specInFM F = nuInFM (gammaIn n B) := by
  have hB : (0 : ℝ) < (B : ℝ) := by exact_mod_cast F.hB
  have hE : ∀ k, F.C.psdIn.isHermitian.eigenvalues k = 1 :=
    fun k => pg_eig_one F.C.Sin F.C.psdIn.isHermitian hSin k
  apply Subtype.ext
  change Muon.nuIn F.C B = ENNReal.ofReal (gammaIn n B) • Measure.dirac (1 : ℝ)
  unfold Muon.nuIn gammaIn
  simp only [hE, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_div_of_pos hB, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    ENNReal.div_eq_inv_mul, ← Nat.cast_smul_eq_nsmul ENNReal n, smul_smul]

private lemma pg_branchSol {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B) {CS γ β : ℝ}
    (hC : 0 < CS) (hγ : 0 < γ) (h : Muon.Drift.DriftBound F CS γ)
    (hw : Muon.DetEquiv.WeightClass (Muon.emaW β)) (hSin : F.C.Sin = 1)
    (br : HalfAnisoBranch β (gammaIn n B) (Muon.nuOut F.C B))
    (hbr : IsModelBranch F.C B F.hB β br) {s : ℝ} (hs : 0 < s) :
    Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) (Muon.Drift.specOutFM F)
      (Muon.Drift.specInFM F) s = (br.sigma s, br.sigmaT s, br.s1T s, br.s1 s) := by
  have hp := Muon.Drift.spectral_mem_classK F h
  have hF := Muon.DetEquiv.Fw_admissible hw.1
  refine ((Muon.DetEquiv.thm_app_de_branch_i hF hC hγ _ _ hp s hs).1).unique
    (Muon.DetEquiv.branchSol_spec hF hC hγ hp hs) ?_
  rw [pg_specIn F hSin]
  exact hbr s hs

private lemma pg_inv_mul {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosSemidef) {s a : ℝ}
    (hs : 0 < s) (ha : 0 ≤ a) :
    (s • (1 : Matrix (Fin m) (Fin m) ℝ) + a • S)⁻¹ * S =
      cfc (fun μ : ℝ => μ / (s + a * μ)) S := by
  have hSa : IsSelfAdjoint S := hS.isHermitian
  have hnn : ∀ μ ∈ spectrum ℝ S, 0 ≤ μ := by
    intro μ hμ
    rw [hS.isHermitian.spectrum_real_eq_range_eigenvalues] at hμ
    obtain ⟨i, rfl⟩ := hμ
    exact hS.eigenvalues_nonneg i
  have hpos : ∀ μ ∈ spectrum ℝ S, 0 < s + a * μ := fun μ hμ => by
    have := mul_nonneg ha (hnn μ hμ); linarith
  have hc1 : ContinuousOn (fun μ : ℝ => s + a * μ) (spectrum ℝ S) := by fun_prop
  have hc2 : ContinuousOn (fun μ : ℝ => μ / (s + a * μ)) (spectrum ℝ S) :=
    ContinuousOn.div continuousOn_id hc1 (fun μ hμ => (hpos μ hμ).ne')
  have hc3 : ContinuousOn (fun μ : ℝ => (s + a * μ)⁻¹) (spectrum ℝ S) :=
    hc1.inv₀ (fun μ hμ => (hpos μ hμ).ne')
  have hM : s • (1 : Matrix (Fin m) (Fin m) ℝ) + a • S = cfc (fun μ : ℝ => s + a * μ) S := by
    rw [cfc_add (a := S) (f := fun _ => s) (g := fun μ => a * μ) continuousOn_const
      (by fun_prop), cfc_const s S,
      cfc_const_mul_id a S, Algebra.algebraMap_eq_smul_one]
  have hMinv : (s • (1 : Matrix (Fin m) (Fin m) ℝ) + a • S) *
      cfc (fun μ : ℝ => (s + a * μ)⁻¹) S = 1 := by
    rw [hM, ← cfc_mul _ _ S hc1 hc3, ← cfc_one ℝ S]
    exact cfc_congr (fun μ hμ => mul_inv_cancel₀ (hpos μ hμ).ne')
  have hinv : (s • (1 : Matrix (Fin m) (Fin m) ℝ) + a • S)⁻¹ =
      cfc (fun μ : ℝ => (s + a * μ)⁻¹) S := Matrix.inv_eq_right_inv hMinv
  rw [hinv]
  have hid : cfc (fun μ : ℝ => μ) S = S := cfc_id' ℝ S
  calc cfc (fun μ : ℝ => (s + a * μ)⁻¹) S * S
      = cfc (fun μ : ℝ => (s + a * μ)⁻¹) S * cfc (fun μ : ℝ => μ) S := by rw [hid]
    _ = cfc (fun μ : ℝ => (s + a * μ)⁻¹ * μ) S := (cfc_mul _ _ S hc3 continuousOn_id).symm
    _ = _ := cfc_congr (fun μ hμ => by simp [div_eq_inv_mul])

private lemma pg_Tcand {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B) {CS γ β : ℝ}
    (hC : 0 < CS) (hγ : 0 < γ) (h : Muon.Drift.DriftBound F CS γ)
    (hw : Muon.DetEquiv.WeightClass (Muon.emaW β)) (hSin : F.C.Sin = 1)
    (br : HalfAnisoBranch β (gammaIn n B) (Muon.nuOut F.C B))
    (hbr : IsModelBranch F.C B F.hB β br) (Dt : Matrix (Fin m) (Fin n) ℝ) (κ : ℝ)
    (hA : F.A = κ • Muon.Setup.Arot F.C Dt) {s : ℝ} (hs : 0 < s) :
    Muon.Drift.Tcand (Muon.emaW β) F (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) s =
      κ • (cfc (fun μ : ℝ => kOs br s μ) F.C.Sout * Dt) := by
  have hb := pg_branchSol F hC hγ h hw hSin br hbr hs
  have hrIn : Muon.Setup.rIn F.C = 1 := by
    unfold Muon.Setup.rIn; rw [hSin]; exact CFC.sqrt_one
  have hrOut : Muon.Setup.rOut F.C * Muon.Setup.rOut F.C = F.C.Sout := by
    unfold Muon.Setup.rOut
    exact CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr F.C.psdOut)
  unfold Muon.Drift.Tcand Muon.DetEquiv.Rbar Muon.DetEquiv.Rtbar Muon.Drift.EG Muon.Drift.branchQ
  simp only [hb]
  rw [hA, hSin, hrIn]
  have hs1 : 0 ≤ br.s1 s := (br.nonneg s hs).2.2.2.1
  have hs1T : 0 ≤ br.s1T s := (br.nonneg s hs).2.2.1
  have hz : (s • (1 : Matrix (Fin n) (Fin n) ℝ) + br.s1 s • 1)⁻¹ = (s + br.s1 s)⁻¹ • 1 := by
    apply Matrix.inv_eq_right_inv
    rw [← add_smul, smul_mul_smul_comm, Matrix.one_mul, mul_inv_cancel₀ (by linarith), one_smul]
  rw [hz]
  have hArot : Muon.Setup.Arot F.C Dt = Muon.Setup.rOut F.C * Dt := by
    unfold Muon.Setup.Arot; rw [hrIn, Matrix.mul_one]
  rw [hArot]
  have hq : s * br.sigma s * br.sigmaT s = br.q s := (br.eq_q s hs).symm
  rw [hq]
  have hcf : cfc (fun μ : ℝ => kOs br s μ) F.C.Sout =
      (s * Muon.DetEquiv.Lw (Muon.emaW β) (br.q s) / (s + br.s1 s)) •
        cfc (fun μ : ℝ => μ / (s + br.s1T s * μ)) F.C.Sout := by
    have hc : ContinuousOn (fun μ : ℝ => μ / (s + br.s1T s * μ)) (spectrum ℝ F.C.Sout) := by
      have hnn : ∀ μ ∈ spectrum ℝ F.C.Sout, 0 ≤ μ := by
        intro μ hμ
        rw [F.C.psdOut.isHermitian.spectrum_real_eq_range_eigenvalues] at hμ
        obtain ⟨i, rfl⟩ := hμ
        exact F.C.psdOut.eigenvalues_nonneg i
      refine ContinuousOn.div continuousOn_id (by fun_prop) (fun μ hμ => ?_)
      have := mul_nonneg hs1T (hnn μ hμ)
      exact (by linarith : 0 < s + br.s1T s * μ).ne'
    rw [← cfc_const_mul _ _ _ hc]
    congr 1
    funext μ
    unfold kOs
    rw [div_mul_div_comm]
    congr 1
    ring
  rw [hcf, ← pg_inv_mul F.C.Sout F.C.psdOut hs hs1T]
  simp only [Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Muon.Setup.rOut F.C), hrOut]
  congr 1
  ring

private lemma pg_ioi_inv {ϱ : ℝ} (hϱ : 0 < ϱ) :
    IntegrableOn (fun u : ℝ => (ϱ + u ^ 2)⁻¹) (Ioi 0) := by
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
  rw [hfun]
  refine Integrable.const_mul ?_ _
  exact (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 hb).mpr
    (by simpa using hint)

private lemma pg_kOs_nonneg {β γin : ℝ} {nuOut : Measure ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (br : HalfAnisoBranch β γin nuOut) {s μ : ℝ} (hs : 0 < s) (hμ : 0 ≤ μ) :
    0 ≤ kOs br s μ := by
  obtain ⟨-, -, h3, h4, hq⟩ := br.nonneg s hs
  have hq3 : 0 ≤ 3 * (1 - β) ^ 2 * br.q s := mul_nonneg (by positivity) hq
  have hL : 0 ≤ Muon.DetEquiv.Lw (Muon.emaW β) (br.q s) :=
    le_trans (div_nonneg zero_le_one (by linarith))
      (lem_app_os_scalar_ii hβ0 hβ1 (br.q s) hq).2.2.1
  unfold kOs
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg hs.le hL) hμ
  · have ha := mul_nonneg h3 hμ
    exact mul_nonneg (by linarith) (by linarith)

private lemma pg_kOs_le_inv {β γin : ℝ} {nuOut : Measure ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (br : HalfAnisoBranch β γin nuOut) {s μ : ℝ} (hs : 0 < s) (hμ : 0 ≤ μ) :
    kOs br s μ ≤ μ / s := by
  obtain ⟨-, -, h3, h4, hq⟩ := br.nonneg s hs
  have hL : Muon.DetEquiv.Lw (Muon.emaW β) (br.q s) ≤ 1 :=
    (lem_app_os_scalar_ii hβ0 hβ1 (br.q s) hq).2.2.2
  have ha : 0 ≤ br.s1T s * μ := mul_nonneg h3 hμ
  have hD : s * s ≤ (s + br.s1T s * μ) * (s + br.s1 s) := by
    nlinarith [mul_nonneg hs.le ha, mul_nonneg hs.le h4, mul_nonneg ha h4]
  have hDpos : 0 < s * s := mul_pos hs hs
  have hs0 : s ≠ 0 := hs.ne'
  unfold kOs
  calc s * Muon.DetEquiv.Lw (Muon.emaW β) (br.q s) * μ / ((s + br.s1T s * μ) * (s + br.s1 s))
      ≤ s * μ / ((s + br.s1T s * μ) * (s + br.s1 s)) := by
        apply div_le_div_of_nonneg_right _ (le_trans hDpos.le hD)
        nlinarith [mul_le_mul_of_nonneg_left hL (mul_nonneg hs.le hμ)]
    _ ≤ s * μ / (s * s) := div_le_div_of_nonneg_left (mul_nonneg hs.le hμ) hDpos hD
    _ = μ / s := mul_div_mul_left μ s hs0

private lemma pg_kOs_contOn {β γin : ℝ} {nuOut : Measure ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (br : HalfAnisoBranch β γin nuOut) {μ : ℝ} (hμ : 0 ≤ μ) :
    ContinuousOn (fun s => kOs br s μ) (Ioi 0) := by
  have hw : Muon.DetEquiv.WeightSeq (Muon.emaW β) := by
    refine ⟨fun j => ?_, ?_, 0, ?_⟩
    · unfold Muon.emaW
      exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
    · unfold Muon.emaW
      exact (summable_geometric_of_lt_one hβ0 hβ1).mul_left _
    · unfold Muon.emaW
      rw [pow_zero, mul_one]
      exact (by linarith : (0:ℝ) < 1 - β).ne'
  have hL : ContinuousOn (fun s => Muon.DetEquiv.Lw (Muon.emaW β) (br.q s)) (Ioi 0) :=
    (Muon.DetEquiv.lem_app_de_scalar_ii hw).2.2.2.1.comp br.continuousOn_q
      (fun s hs => Set.mem_Ici.2 (br.nonneg s hs).2.2.2.2)
  unfold kOs
  apply ContinuousOn.div
  · exact (continuousOn_id.mul hL).mul continuousOn_const
  · exact (continuousOn_id.add (br.continuousOn_s1T.mul continuousOn_const)).mul
      (continuousOn_id.add br.continuousOn_s1)
  · intro s hs
    have hs' : 0 < s := hs
    obtain ⟨-, -, h3, h4, -⟩ := br.nonneg s hs'
    have ha := mul_nonneg h3 hμ
    exact (mul_pos (by linarith) (by linarith)).ne'

private lemma pg_kOs_integrable {β γin : ℝ} {nuOut : Measure ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (br : HalfAnisoBranch β γin nuOut) {ρ μ : ℝ} (hρ : 0 < ρ) (hμ : 0 ≤ μ) :
    IntegrableOn (fun u : ℝ => kOs br (ρ + u ^ 2) μ) (Ioi 0) := by
  have hpos : ∀ u : ℝ, 0 < ρ + u ^ 2 := fun u => by positivity
  have hcont : Continuous (fun u : ℝ => kOs br (ρ + u ^ 2) μ) := by
    refine (pg_kOs_contOn hβ0 hβ1 br hμ).comp_continuous (by fun_prop) (fun u => hpos u)
  refine Integrable.mono' ((pg_ioi_inv hρ).const_mul μ) hcont.aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pg_kOs_nonneg hβ0 hβ1 br (hpos u) hμ)]
  calc kOs br (ρ + u ^ 2) μ ≤ μ / (ρ + u ^ 2) := pg_kOs_le_inv hβ0 hβ1 br (hpos u) hμ
    _ = μ * (ρ + u ^ 2)⁻¹ := div_eq_mul_inv _ _

private lemma pg_Gbar {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B) {CS γ β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hC : 0 < CS) (hγ : 0 < γ) (h : Muon.Drift.DriftBound F CS γ)
    (hw : Muon.DetEquiv.WeightClass (Muon.emaW β)) (hSin : F.C.Sin = 1)
    (br : HalfAnisoBranch β (gammaIn n B) (Muon.nuOut F.C B))
    (hbr : IsModelBranch F.C B F.hB β br) (Dt : Matrix (Fin m) (Fin n) ℝ) (κ : ℝ)
    (hA : F.A = κ • Muon.Setup.Arot F.C Dt) {ρ : ℝ} (hρ : 0 < ρ) :
    Muon.Drift.Gbar (Muon.emaW β) F (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) ρ =
      (κ * Real.sqrt 2) • (cfc (fun μ : ℝ => dRidge br ρ μ) F.C.Sout * Dt) := by
  ext i j
  have hint : ∀ k, IntegrableOn (fun u : ℝ => kOs br (ρ + u ^ 2) (F.C.psdOut.isHermitian.eigenvalues k))
      (Ioi 0) := fun k =>
    pg_kOs_integrable hβ0 hβ1 br hρ (F.C.psdOut.eigenvalues_nonneg k)
  have hc := pg_commute F.C.Sout F.C.psdOut.isHermitian (fun u μ => kOs br (ρ + u ^ 2) μ)
    (Real.sqrt 2 / Real.pi) Dt hint i j
  have hT : ∀ u ∈ Ioi (0 : ℝ),
      Muon.Drift.Tcand (Muon.emaW β) F (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F)
        (ρ + u ^ 2) i j = κ * (cfc (fun μ : ℝ => kOs br (ρ + u ^ 2) μ) F.C.Sout * Dt) i j := by
    intro u _
    rw [pg_Tcand F hC hγ h hw hSin br hbr Dt κ hA (by positivity)]
    rfl
  unfold Muon.Drift.Gbar
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hT, integral_const_mul]
  have hd : (fun μ : ℝ => dRidge br ρ μ) =
      fun μ => Real.sqrt 2 / Real.pi * ∫ u in Ioi (0 : ℝ), kOs br (ρ + u ^ 2) μ := rfl
  rw [hd, ← hc]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

private lemma pg_target (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) (t : ℤ) (H : OsUpdateHyp R Ω P t) (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    Muon.Drift.Gbar (Muon.emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
      (Muon.Drift.specInFM (R.F k)) ρ = osUpdateTarget R Ω P t H k ρ := by
  have hCS : 0 < R.CSig := lt_of_lt_of_le one_pos R.hC
  have hγ : 0 < max R.γstar 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hD : Muon.Drift.DriftBound (R.F k) R.CSig (max R.γstar 1) := by
    refine ⟨R.normOut k, R.normIn k, ?_⟩
    have hB : (0 : ℝ) ≤ (R.B k : ℝ) := Nat.cast_nonneg _
    exact (R.dims k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hB)
  have hβ := (R.F k).hβ
  rw [R.hβ k] at hβ
  obtain ⟨hβ0, hβ1⟩ := hβ
  have hw := Muon.Drift.emaW_weightClass_regime R
  have hG := pg_Gbar (R.F k) hβ0 hβ1 hCS hγ hD hw (H.hSin k) (H.br k) (H.hbr k) (H.Dt k)
    (Real.sqrt (2 * H.cRt k))⁻¹ (H.hA k) hρ
  have hBk : 1 ≤ R.B k := (R.F k).hB
  have hγin : 0 < gammaIn (R.n k) (R.B k) := by
    unfold gammaIn
    exact div_pos (Nat.cast_pos.mpr (H.hn k)) (Nat.cast_pos.mpr (by omega))
  have hcond : 0 < R.β ∨ (R.β = 0 ∧ gammaIn (R.n k) (R.B k) < 1) := by
    rcases hβ0.lt_or_eq with h | h
    · exact Or.inl h
    · right
      refine ⟨h.symm, ?_⟩
      have h1 := H.hε k
      have h2 := H.hεbar
      unfold epsOs at h1
      rw [← h] at h1
      nlinarith
  obtain ⟨qs, hq0, huniq, -⟩ := lem_app_os_scalar_iii hβ0 hβ1 hγin hcond
  have hqs : 0 < qs ∧ qs * Muon.DetEquiv.Fw (Muon.emaW R.β) qs = gammaIn (R.n k) (R.B k) :=
    ⟨hq0, (huniq qs hq0).2 rfl⟩
  have hL := (thm_app_os_limit_iv hβ0 hβ1 (H.hm k) (H.hn k) hBk (R.F k).C (H.hSin k) hcond hqs
    (H.br k) (H.hbr k) ρ hρ.le).2
  rw [hG, hL]
  unfold osUpdateTarget
  have hc : 0 < H.cRt k := H.hcRpos k
  have hs : (Real.sqrt (2 * H.cRt k))⁻¹ * Real.sqrt 2 = (Real.sqrt (H.cRt k))⁻¹ := by
    rw [Real.sqrt_mul (by norm_num), mul_inv]
    have : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    field_simp
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]
  rw [smul_smul]
  congr 1
  ring

private lemma pg_le_biSup {f : ℝ → ℝ} {I : Set ℝ} (hb : BddAbove (f '' I)) {s : ℝ} (hs : s ∈ I) :
    f s ≤ ⨆ s ∈ I, f s := by
  obtain ⟨b, hb'⟩ := hb
  have hbdd : BddAbove (Set.range fun s => ⨆ (_ : s ∈ I), f s) := by
    refine ⟨max b 0, ?_⟩
    rintro _ ⟨s', rfl⟩
    change (⨆ (_ : s' ∈ I), f s') ≤ max b 0
    by_cases hs' : s' ∈ I
    · rw [ciSup_pos hs']
      exact le_max_of_le_left (hb' ⟨s', hs', rfl⟩)
    · haveI : IsEmpty (s' ∈ I) := ⟨hs'⟩
      rw [Real.iSup_of_isEmpty]
      exact le_max_right _ _
  refine le_ciSup_of_le hbdd s ?_
  rw [ciSup_pos hs]

/-- `cor:app-os-update`, part (i): the expected regularized update. Snapshot `cr-2026-10-23`.
Statement verbatim (`sections/12-oversampled/section.tex` l.546–560):

\begin{corollary}[Expected regularized update]\label{cor:app-os-update}
Assume \cref{assum:app-setup-regime} with $\Sigmain=\Id_{\Nin}$, and assume that
$\epsilon_{\rm os}=3(1-\bmom^2)\Nin/B\le\bar\epsilon$ along the sequence of dimensions for a
fixed $\bar\epsilon<1$. For $\ridge\in[\ridge_-,\ridge_+]$ let
$\vartheta_\ridge$ be the function of \cref{thm:app-os-limit}(iv) at the
current dimension. Then
\begin{equation}\label{eqn:app-os-update}
\sup_{\ridge\in[\ridge_-,\ridge_+]}\Big\|\EE\,\Qridge\ridge(\Mt)
-\sqrt{\frac{B_{\rm eff}}{\Nin}}\;\vartheta_\ridge(\Sigmaout)\,
\mathfrak d^{\rm os}_{\hat\nu_{\mathrm{out}},r}\Big(\Sigmaout;\frac{\ridge}{\sw2\gin}\Big)\,
\frac{\Dt}{\sqrt{\cR(t)}}\Big\|_\F\longrightarrow0,
\end{equation}
and $\operatorname{spec}\vartheta_\ridge(\Sigmaout)\subset\big[1-\epsilon_{\rm os},(1-\epsilon_{\rm os})^{-1}\big]$
at every dimension and for every $\ridge$.
\end{corollary}
-/
theorem cor_app_os_update_i (R : Muon.Setup.SetupRegime)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, Muon.Setup.FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (H : OsUpdateHyp R Ω P t) :
    ∀ η > 0, ∀ᶠ k in atTop, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      Muon.fro (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ -
        osUpdateTarget R Ω P t H k ϱ) < η := by
  intro η hη
  obtain ⟨-, hbdd, hten, -⟩ := Muon.Drift.thm_app_drift_mean R P S t
  filter_upwards [hten.eventually (gt_mem_nhds hη)] with k hk ϱ hϱ
  have hp : 0 < ϱ := R.hϱ.1.trans_le hϱ.1
  rw [← pg_target R P t H k hp]
  refine lt_of_le_of_lt ?_ hk
  exact pg_le_biSup (f := fun ϱ => Muon.fro (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ -
    Muon.Drift.Gbar (Muon.emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
      (Muon.Drift.specInFM (R.F k)) ϱ)) (hbdd k) hϱ


/-- `cor:app-os-update`, the spectral clause: `spec ϑ_ϱ(Σ_out) ⊂ [1-ε_os, (1-ε_os)^{-1}]` at
every dimension and every `ϱ ≥ 0`. Snapshot `cr-2026-10-23`. Statement verbatim
(`sections/12-oversampled/section.tex` l.546–560, the same corollary). -/
theorem cor_app_os_update_ii (R : Muon.Setup.SetupRegime)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, Muon.Setup.FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (H : OsUpdateHyp R Ω P t) :
    ∀ k, ∀ ϱ : ℝ, 0 ≤ ϱ →
      spectrum ℝ (cfc (fun μ : ℝ => thetaRidge (H.br k) (nuHatOut (R.F k).C)
          ((R.m k : ℝ) / (R.n k : ℝ)) ϱ μ) (R.F k).C.Sout) ⊆
        Icc (1 - epsOs R.β (gammaIn (R.n k) (R.B k)))
            (1 - epsOs R.β (gammaIn (R.n k) (R.B k)))⁻¹ := by
  intro k ϱ hϱ
  have hβ := (R.F k).hβ
  rw [R.hβ k] at hβ
  obtain ⟨hβ0, hβ1⟩ := hβ
  have hBk : 1 ≤ R.B k := (R.F k).hB
  have hγin : 0 < gammaIn (R.n k) (R.B k) := by
    unfold gammaIn
    exact div_pos (Nat.cast_pos.mpr (H.hn k)) (Nat.cast_pos.mpr (by omega))
  have hε : epsOs R.β (gammaIn (R.n k) (R.B k)) < 1 := (H.hε k).trans_lt H.hεbar
  have hcond := (lem_app_os_scalar_iv hβ0 hβ1 hγin hε).1
  obtain ⟨qs, hq0, huniq, -⟩ := lem_app_os_scalar_iii hβ0 hβ1 hγin hcond
  have hqs : 0 < qs ∧ qs * Muon.DetEquiv.Fw (Muon.emaW R.β) qs = gammaIn (R.n k) (R.B k) :=
    ⟨hq0, (huniq qs hq0).2 rfl⟩
  have hL := (thm_app_os_limit_iv hβ0 hβ1 (H.hm k) (H.hn k) hBk (R.F k).C (H.hSin k) hcond hqs
    (H.br k) (H.hbr k) ϱ hϱ).1
  have hup := (lem_app_os_scalar_iv hβ0 hβ1 hγin hε).2 qs hqs.1 hqs.2
  have hlam : 0 < lamOs R.β qs := by
    unfold lamOs
    have h1 : 0 ≤ (1 - R.β) ^ 2 := sq_nonneg _
    have h2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) h1) hq0.le
    linarith
  have hpos : 0 < 1 - epsOs R.β (gammaIn (R.n k) (R.B k)) := by linarith
  have hlow : 1 - epsOs R.β (gammaIn (R.n k) (R.B k)) ≤ (lamOs R.β qs)⁻¹ := by
    have h := one_div_le_one_div_of_le hlam hup
    rwa [one_div_one_div, one_div] at h
  have hup' : lamOs R.β qs ≤ (1 - epsOs R.β (gammaIn (R.n k) (R.B k)))⁻¹ := by
    rwa [one_div] at hup
  exact hL.trans (Set.Icc_subset_Icc hlow hup')

end

end Muon.Oversampled

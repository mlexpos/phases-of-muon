import Muon.Isotropic.ZeroRidge

/-!
# Appendix F: the constant at aspect ratio one

Task L-F.4 (interface). Snapshot `cr-2026-10-23`. Source: `sections/05b-isotropic/section.tex`,
the label `thm:app-iso-one` (l.1768–1777), with the constant `eqn:app-iso-C` at
`β = 0`, `γin = γout = 1`.

Reuse (never redefined here): `Muon.Isotropic.Cbeta` (`C_β(γin, γout)`, `eqn:app-iso-C`; the
convention `C = C_0` of `sec:app-iso-zero` applies in `sec:app-iso-one`). Every declaration is
a statement only (`sorry`).
-/

noncomputable section

namespace Muon.Isotropic

section OneHelpers

open MeasureTheory ProbabilityTheory Filter Topology Set
open Muon.DetEquiv (J Fw Lw rW)

private lemma one_F_eq {ξ : ℝ} (hξ : 0 < ξ) : isoF ξ = isoPhi (1 / (2 * ξ ^ 2)) := by
  have hv : 0 < 1 / (2 * ξ ^ 2) := by positivity
  rw [lem_app_iso_gaussian_i _ hv]
  congr 1
  have e : 2 * (1 / (2 * ξ ^ 2)) = (ξ ^ 2)⁻¹ := by field_simp
  rw [e, Real.inv_rpow (sq_nonneg ξ), Real.rpow_neg (sq_nonneg ξ), inv_inv,
    ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos hξ]

private lemma one_F_deriv {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt isoF (isoPhiDeriv (1 / (2 * ξ ^ 2)) * (-(1 / ξ ^ 3))) ξ := by
  have hv : HasDerivAt (fun x : ℝ => 1 / (2 * x ^ 2)) (-(1 / ξ ^ 3)) ξ := by
    have h1 : HasDerivAt (fun x : ℝ => 2 * x ^ 2) (2 * (2 * ξ)) ξ := by
      simpa using (hasDerivAt_pow 2 ξ).const_mul 2
    have h2 := (hasDerivAt_const ξ (1:ℝ)).div h1 (by positivity)
    refine h2.congr_deriv ?_
    field_simp
    ring
  have hΦ := (lem_app_iso_gaussian_ii.2.1 (1 / (2 * ξ ^ 2)) (by positivity)).1
  have := hΦ.comp ξ hv
  refine (this.congr_deriv rfl).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hξ] with x hx using one_F_eq hx

private lemma one_F_bounds {ξ : ℝ} (hξ : 0 < ξ) :
    0 < isoF ξ ∧ isoF ξ < 1 ∧ isoF ξ ≤ 1 / (2 * ξ ^ 2) := by
  have hv : 0 < 1 / (2 * ξ ^ 2) := by positivity
  rw [one_F_eq hξ]
  have h1 := lem_app_iso_gaussian_ii.2.2 _ hv
  have h2 := lem_app_iso_gaussian_iii _ hv
  exact ⟨h1.1, h1.2, by linarith [h2.1]⟩

private lemma one_h_deriv {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (fun x : ℝ => Real.sqrt 2 * x * (1 - isoF x))
      (Real.sqrt 2 * ((1 - isoF ξ) + ξ * (isoPhiDeriv (1 / (2 * ξ ^ 2)) / ξ ^ 3))) ξ := by
  have h1 : HasDerivAt (fun x : ℝ => Real.sqrt 2 * x) (Real.sqrt 2 * 1) ξ :=
    (hasDerivAt_id' ξ).const_mul _
  have h2 : HasDerivAt (fun x : ℝ => 1 - isoF x) (-(isoPhiDeriv (1 / (2 * ξ ^ 2)) * (-(1 / ξ ^ 3)))) ξ :=
    (one_F_deriv hξ).const_sub 1
  refine (h1.mul h2).congr_deriv ?_
  field_simp

private lemma one_h_deriv_pos {ξ : ℝ} (hξ : 0 < ξ) :
    0 < Real.sqrt 2 * ((1 - isoF ξ) + ξ * (isoPhiDeriv (1 / (2 * ξ ^ 2)) / ξ ^ 3)) := by
  have hb := one_F_bounds hξ
  have hd := (lem_app_iso_gaussian_ii.2.1 (1 / (2 * ξ ^ 2)) (by positivity)).2.1
  have : 0 < ξ * (isoPhiDeriv (1 / (2 * ξ ^ 2)) / ξ ^ 3) := by positivity
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have : 0 < (1 - isoF ξ) + ξ * (isoPhiDeriv (1 / (2 * ξ ^ 2)) / ξ ^ 3) := by linarith [hb.2.1]
  positivity

private lemma one_h_strictMono :
    StrictMonoOn (fun x : ℝ => Real.sqrt 2 * x * (1 - isoF x)) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun x hx => (one_h_deriv (Set.mem_Ioi.mp hx)).continuousAt.continuousWithinAt) ?_
  intro x hx
  rw [interior_Ioi] at hx
  rw [(one_h_deriv (Set.mem_Ioi.mp hx)).deriv]
  exact one_h_deriv_pos (Set.mem_Ioi.mp hx)

private lemma one_h_image :
    (fun x : ℝ => Real.sqrt 2 * x * (1 - isoF x)) '' Ioi 0 = Ioi 0 := by
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hcont : ContinuousOn (fun x : ℝ => Real.sqrt 2 * x * (1 - isoF x)) (Ioi 0) :=
    fun x hx => (one_h_deriv (Set.mem_Ioi.mp hx)).continuousAt.continuousWithinAt
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hb := one_F_bounds (Set.mem_Ioi.mp hx)
    have : 0 < x := hx
    show 0 < Real.sqrt 2 * x * (1 - isoF x)
    have : 0 < 1 - isoF x := by linarith [hb.2.1]
    positivity
  · intro hu
    have hu : 0 < u := hu
    -- small point
    set ε : ℝ := min 1 (u / 2) with hε
    have hε0 : 0 < ε := lt_min one_pos (by positivity)
    have hlow : Real.sqrt 2 * ε * (1 - isoF ε) < u := by
      have hb := one_F_bounds hε0
      have h3 : 1 - isoF ε ≤ 1 := by linarith [hb.1]
      have : Real.sqrt 2 * ε * (1 - isoF ε) ≤ Real.sqrt 2 * ε * 1 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have hεu : ε ≤ u / 2 := min_le_right _ _
      nlinarith
    set M : ℝ := max 1 (u + 1) with hM
    have hM1 : 1 ≤ M := le_max_left _ _
    have hMu : u + 1 ≤ M := le_max_right _ _
    have hM0 : 0 < M := by linarith
    have hhigh : u < Real.sqrt 2 * (2 * M + 1) * (1 - isoF (2 * M + 1)) := by
      have hx : 0 < 2 * M + 1 := by linarith
      have hb := one_F_bounds hx
      have hF : isoF (2 * M + 1) ≤ 1 / (2 * (2 * M + 1) ^ 2) := hb.2.2
      have hF2 : 1 / (2 * (2 * M + 1) ^ 2) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      have hs1 : (1:ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]; norm_num
      have : 1 / 2 ≤ 1 - isoF (2 * M + 1) := by linarith
      have h4 : Real.sqrt 2 * (2 * M + 1) * (1 / 2) ≤ Real.sqrt 2 * (2 * M + 1) * (1 - isoF (2 * M + 1)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      nlinarith
    have hεM : ε ≤ 2 * M + 1 := by
      have : ε ≤ 1 := min_le_left _ _
      linarith
    obtain ⟨x, hx, hxu⟩ := intermediate_value_Icc hεM
      (hcont.mono (fun y hy => lt_of_lt_of_le hε0 hy.1)) ⟨hlow.le, hhigh.le⟩
    exact ⟨x, lt_of_lt_of_le hε0 hx.1, hxu⟩

private lemma one_rW_zero (q : ℝ) : rW (Muon.emaW 0) q = isoPhi q := by
  have hz : ∀ j : ℕ, j ≠ 0 → Muon.emaW 0 j ^ 2 * J (Muon.emaW 0 j ^ 2 * q) = 0 := by
    intro j hj
    simp [Muon.emaW, zero_pow hj]
  unfold rW Fw
  rw [tsum_eq_single 0 hz]
  simp [Muon.emaW, isoPhi]

private lemma one_Lw_zero (x : ℝ) : Lw (Muon.emaW 0) x = J x := by
  unfold Lw
  rw [tsum_eq_single 0]
  · simp [Muon.emaW]
  · intro j hj
    simp [Muon.emaW, zero_pow hj]

private lemma one_isoLink : IsIsoLink (rW (Muon.emaW 0)) := by
  have hw : Muon.DetEquiv.WeightSeq (Muon.emaW 0) := by
    refine ⟨fun j => ?_, ?_, 0, ?_⟩
    · unfold Muon.emaW
      exact mul_nonneg (by linarith) (pow_nonneg le_rfl j)
    · unfold Muon.emaW
      exact (summable_geometric_of_lt_one le_rfl zero_lt_one).mul_left _
    · unfold Muon.emaW
      rw [pow_zero, mul_one]
      norm_num
  refine ⟨ContinuousOn.mul continuousOn_id (Muon.DetEquiv.Fw_admissible hw).contOn,
    (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.1,
    (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.2.1⟩

private lemma one_isoGb {ξ : ℝ} (hξ : 0 < ξ) :
    isoGb 0 1 1 ((Real.sqrt 2 * ξ * (1 - isoF ξ)) ^ 2) = isoF ξ := by
  set s := (Real.sqrt 2 * ξ * (1 - isoF ξ)) ^ 2 with hs
  have hb := one_F_bounds hξ
  have hv : 0 < 1 / (2 * ξ ^ 2) := by positivity
  have hs0 : 0 < s := by
    have : 0 < 1 - isoF ξ := by linarith [hb.2.1]
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    rw [hs]; positivity
  have hmem : 1 / (2 * ξ ^ 2) ∈ isoDr (rW (Muon.emaW 0)) 1 1 ∧
      isoG (rW (Muon.emaW 0)) 1 1 s (1 / (2 * ξ ^ 2)) = 0 := by
    refine ⟨⟨hv.le, ?_⟩, ?_⟩
    · rw [one_rW_zero, min_self]
      exact (lem_app_iso_gaussian_ii.2.2 _ hv).2
    · unfold isoG
      rw [one_rW_zero, ← one_F_eq hξ, hs]
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp
      rw [h2]
      ring
  have hroot : qIso 0 1 1 s = 1 / (2 * ξ ^ 2) := by
    obtain ⟨q, hq, huniq⟩ := (lem_app_iso_comparison_i one_isoLink one_pos one_pos).2.1 s hs0
    have h1 : isoRoot (rW (Muon.emaW 0)) 1 1 s = q := by
      unfold isoRoot
      have hex : ∃ q, q ∈ isoDr (rW (Muon.emaW 0)) 1 1 ∧ isoG (rW (Muon.emaW 0)) 1 1 s q = 0 :=
        ⟨q, hq⟩
      rw [dif_pos hex]
      exact huniq _ hex.choose_spec
    rw [qIso, h1]
    exact (huniq _ hmem).symm
  unfold isoGb
  rw [hroot, one_Lw_zero]
  have : 1 / (2 * ξ ^ 2) * J (1 / (2 * ξ ^ 2)) = isoPhi (1 / (2 * ξ ^ 2)) := rfl
  rw [this, ← one_F_eq hξ]

private lemma one_J1_nonneg_le {ξ : ℝ} (hξ : 0 < ξ) :
    0 ≤ 1 - (1 - isoF ξ) ^ 2 ∧ 1 - (1 - isoF ξ) ^ 2 ≤ 2 / (1 + ξ ^ 2) := by
  have hb := one_F_bounds hξ
  have hq : 1 - (1 - isoF ξ) ^ 2 = isoF ξ * (2 - isoF ξ) := by ring
  refine ⟨by rw [hq]; nlinarith [hb.1, hb.2.1], ?_⟩
  rw [le_div_iff₀ (by positivity)]
  rcases le_total ξ 1 with h | h
  · have h1 : 1 - (1 - isoF ξ) ^ 2 ≤ 1 := by nlinarith [hb.1, hb.2.1]
    nlinarith [sq_nonneg ξ]
  · have h1 : 1 - (1 - isoF ξ) ^ 2 ≤ 2 * (1 / (2 * ξ ^ 2)) := by
      rw [hq]; nlinarith [hb.1, hb.2.2, hb.2.1]
    have h2 : 2 * (1 / (2 * ξ ^ 2)) * (1 + ξ ^ 2) ≤ 2 := by
      have : 2 * (1 / (2 * ξ ^ 2)) = 1 / ξ ^ 2 := by field_simp
      rw [this, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg ξ, one_le_pow₀ h (n := 2)]
    have h3 : 0 ≤ 1 + ξ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 h3]

private lemma one_isoF_contOn : ContinuousOn isoF (Ioi 0) :=
  fun x hx => (one_F_deriv (Set.mem_Ioi.mp hx)).continuousAt.continuousWithinAt

private lemma one_J1_integrable :
    IntegrableOn (fun ξ : ℝ => 1 - (1 - isoF ξ) ^ 2) (Ioi 0) := by
  have hI : IntegrableOn (fun ξ : ℝ => 2 / (1 + ξ ^ 2)) (Ioi 0) := by
    have : Integrable (fun ξ : ℝ => 2 * (1 + ξ ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul 2
    exact (this.congr (Filter.Eventually.of_forall fun _ => by simp [div_eq_mul_inv])).integrableOn
  refine Integrable.mono' hI ?_ ?_
  · exact ((continuousOn_const.sub ((continuousOn_const.sub one_isoF_contOn).pow 2))).aestronglyMeasurable
      measurableSet_Ioi
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun ξ hξ => ?_)
    have := one_J1_nonneg_le (Set.mem_Ioi.mp hξ)
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]
    exact this.2

private lemma one_Q_tendsto_zero : Tendsto (fun ξ : ℝ => ξ * isoF ξ ^ 2) (𝓝[Ici 0] 0) (𝓝 0) := by
  have hle : ∀ ξ : ℝ, 0 ≤ ξ → |ξ * isoF ξ ^ 2| ≤ ξ := by
    intro ξ hξ
    rcases hξ.eq_or_lt with h | h
    · subst h; simp
    · have hb := one_F_bounds h
      rw [abs_of_nonneg (by positivity)]
      have h1 : isoF ξ ^ 2 ≤ 1 := by nlinarith [hb.1, hb.2.1]
      calc ξ * isoF ξ ^ 2 ≤ ξ * 1 := mul_le_mul_of_nonneg_left h1 hξ
        _ = ξ := mul_one ξ
  have hz : Tendsto (fun ξ : ℝ => ξ) (𝓝[Ici 0] 0) (𝓝 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hz
  filter_upwards [self_mem_nhdsWithin] with ξ hξ
  exact hle ξ hξ

private lemma one_Q_tendsto_top : Tendsto (fun ξ : ℝ => ξ * isoF ξ ^ 2) atTop (𝓝 0) := by
  have hb : Tendsto (fun ξ : ℝ => 1 / (4 * ξ ^ 3)) atTop (𝓝 0) := by
    have : Tendsto (fun ξ : ℝ => 4 * ξ ^ 3) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 3 ≠ 0)).const_mul_atTop (by norm_num : (0:ℝ) < 4)
    refine (this.inv_tendsto_atTop).congr (fun ξ => ?_)
    simp [one_div]
  refine squeeze_zero' ?_ ?_ hb
  · filter_upwards [eventually_gt_atTop 0] with ξ hξ
    positivity
  · filter_upwards [eventually_gt_atTop 0] with ξ hξ
    have hb := one_F_bounds hξ
    have h2 : isoF ξ ^ 2 ≤ (1 / (2 * ξ ^ 2)) ^ 2 := pow_le_pow_left₀ hb.1.le hb.2.2 2
    have : ξ * (1 / (2 * ξ ^ 2)) ^ 2 = 1 / (4 * ξ ^ 3) := by field_simp; ring
    calc ξ * isoF ξ ^ 2 ≤ ξ * (1 / (2 * ξ ^ 2)) ^ 2 := mul_le_mul_of_nonneg_left h2 hξ.le
      _ = _ := this

private lemma one_Cbeta_eq :
    Cbeta 0 1 1 = (1 / Real.pi) * ∫ ξ in Ioi (0:ℝ), (1 - (1 - isoF ξ) ^ 2) := by
  set hd : ℝ → ℝ := fun ξ => Real.sqrt 2 *
    ((1 - isoF ξ) + ξ * (isoPhiDeriv (1 / (2 * ξ ^ 2)) / ξ ^ 3)) with hhd
  have hf' : ∀ x ∈ Ioi (0:ℝ), HasDerivWithinAt
      (fun x : ℝ => Real.sqrt 2 * x * (1 - isoF x)) (hd x) (Ioi 0) x :=
    fun x hx => (one_h_deriv hx).hasDerivWithinAt
  have hinj := one_h_strictMono.injOn
  set g : ℝ → ℝ := fun u => isoGb 0 1 1 (u ^ 2) with hg
  have hgint : IntegrableOn g (Ioi 0) :=
    (prop_app_iso_zero_i (β := 0) le_rfl zero_lt_one one_pos one_pos).2.1
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hf' hinj g
  have hint := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hf' hinj g
  rw [one_h_image] at hcv hint
  have hpt : ∀ ξ ∈ Ioi (0:ℝ),
      |hd ξ| • g (Real.sqrt 2 * ξ * (1 - isoF ξ)) = hd ξ * isoF ξ := by
    intro ξ hξ
    rw [abs_of_pos (one_h_deriv_pos hξ), smul_eq_mul]
    simp only [hg]
    rw [one_isoGb hξ]
  have hI1 : IntegrableOn (fun ξ => hd ξ * isoF ξ) (Ioi 0) :=
    (hint.1 hgint).congr_fun hpt measurableSet_Ioi
  have h2 : ∫ u in Ioi (0:ℝ), g u = ∫ ξ in Ioi 0, hd ξ * isoF ξ := by
    rw [hcv]; exact setIntegral_congr_fun measurableSet_Ioi hpt
  set Q' : ℝ → ℝ := fun ξ => isoF ξ ^ 2 +
    2 * ξ * isoF ξ * (isoPhiDeriv (1 / (2 * ξ ^ 2)) * (-(1 / ξ ^ 3))) with hQ'
  have hQd : ∀ ξ ∈ Ioi (0:ℝ), HasDerivAt (fun ξ => ξ * isoF ξ ^ 2) (Q' ξ) ξ := by
    intro ξ hξ
    have h1 := (hasDerivAt_id' ξ).mul ((one_F_deriv hξ).pow 2)
    refine h1.congr_deriv ?_
    simp only [hQ', Pi.pow_apply]
    push_cast
    ring
  have hQeq : ∀ ξ ∈ Ioi (0:ℝ),
      Q' ξ = (1 - (1 - isoF ξ) ^ 2) - Real.sqrt 2 * (hd ξ * isoF ξ) := by
    intro ξ hξ
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hξ' : ξ ≠ 0 := (Set.mem_Ioi.mp hξ).ne'
    simp only [hQ', hhd]
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring
  have hQint : IntegrableOn Q' (Ioi 0) :=
    (one_J1_integrable.sub (hI1.const_mul (Real.sqrt 2))).congr_fun
      (fun ξ hξ => (hQeq ξ hξ).symm) measurableSet_Ioi
  have hF := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (m := 0)
    (f := fun ξ => ξ * isoF ξ ^ 2) (f' := Q')
    (by unfold ContinuousWithinAt; simpa using one_Q_tendsto_zero) hQd hQint one_Q_tendsto_top
  have hF0 : ∫ ξ in Ioi (0:ℝ), Q' ξ = 0 := by simpa using hF
  have hsplit : ∫ ξ in Ioi (0:ℝ), Q' ξ =
      (∫ ξ in Ioi (0:ℝ), (1 - (1 - isoF ξ) ^ 2)) -
        Real.sqrt 2 * ∫ ξ in Ioi (0:ℝ), hd ξ * isoF ξ := by
    rw [setIntegral_congr_fun measurableSet_Ioi hQeq, integral_sub one_J1_integrable
      (hI1.const_mul _), integral_const_mul]
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hkey : Real.sqrt 2 * ∫ ξ in Ioi (0:ℝ), hd ξ * isoF ξ =
      ∫ ξ in Ioi (0:ℝ), (1 - (1 - isoF ξ) ^ 2) := by linarith
  unfold Cbeta
  have e : ∫ u in Ioi (0:ℝ), isoGb 0 1 1 (u ^ 2) = ∫ u in Ioi (0:ℝ), g u := rfl
  rw [e, h2, ← hkey]
  have hp := Real.pi_pos
  field_simp

private lemma one_inv_sq_int {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun ξ : ℝ => 1 / (ξ ^ 2 + c ^ 2)) (Ioi 0) ∧
    ∫ ξ in Ioi (0:ℝ), 1 / (ξ ^ 2 + c ^ 2) = Real.pi / (2 * c) := by
  have hc0 : c ≠ 0 := hc.ne'
  have heq : ∀ ξ : ℝ, 1 / (ξ ^ 2 + c ^ 2) = c⁻¹ ^ 2 * (1 + (c⁻¹ * ξ) ^ 2)⁻¹ := by
    intro ξ
    field_simp
    ring
  constructor
  · have h1 : Integrable (fun ξ : ℝ => (1 + (c⁻¹ * ξ) ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hc0)
    refine ((h1.const_mul (c⁻¹ ^ 2)).integrableOn).congr_fun (fun ξ _ => (heq ξ).symm) measurableSet_Ioi
  · simp_rw [heq]
    rw [integral_const_mul, integral_comp_mul_left_Ioi (fun u : ℝ => (1 + u ^ 2)⁻¹) 0
      (inv_pos.2 hc)]
    simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero, smul_eq_mul]
    field_simp

private lemma one_xi_int {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ∫ ξ in Ioi (0:ℝ), (1 - ξ ^ 4 / ((ξ ^ 2 + a ^ 2) * (ξ ^ 2 + b ^ 2))) =
      Real.pi / 2 * ((a ^ 2 + a * b + b ^ 2) / (a + b)) := by
  have hab2 : a ^ 2 - b ^ 2 ≠ 0 := by
    intro h
    apply hab
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  have hpt : ∀ ξ : ℝ, 1 - ξ ^ 4 / ((ξ ^ 2 + a ^ 2) * (ξ ^ 2 + b ^ 2)) =
      (a ^ 4 * (1 / (ξ ^ 2 + a ^ 2)) - b ^ 4 * (1 / (ξ ^ 2 + b ^ 2))) / (a ^ 2 - b ^ 2) := by
    intro ξ
    have h1 : ξ ^ 2 + a ^ 2 ≠ 0 := by positivity
    have h2 : ξ ^ 2 + b ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [hpt]
  rw [integral_div, integral_sub ((one_inv_sq_int ha).1.const_mul _)
    ((one_inv_sq_int hb).1.const_mul _), integral_const_mul, integral_const_mul,
    (one_inv_sq_int ha).2, (one_inv_sq_int hb).2]
  have hs : a + b ≠ 0 := by positivity
  field_simp
  ring

private lemma one_A_int {ξ : ℝ} (hξ : 0 < ξ) :
    Integrable (fun x : ℝ => x ^ 2 / (x ^ 2 + 2 * ξ ^ 2)) (gaussianReal 0 1) := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  have hd : 0 < x ^ 2 + 2 * ξ ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_le_one hd]
  nlinarith [sq_nonneg ξ]

private lemma one_w_eq {ξ : ℝ} (hξ : 0 < ξ) :
    1 - isoF ξ = ∫ x, 2 * ξ ^ 2 / (x ^ 2 + 2 * ξ ^ 2) ∂(gaussianReal 0 1) := by
  have h1 : ∀ x : ℝ, 2 * ξ ^ 2 / (x ^ 2 + 2 * ξ ^ 2) = 1 - x ^ 2 / (x ^ 2 + 2 * ξ ^ 2) := by
    intro x
    have hd : x ^ 2 + 2 * ξ ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [h1]
  rw [integral_sub (integrable_const _) (one_A_int hξ)]
  simp [isoF]

private lemma one_kappa_meas : Measurable (fun z : ℝ × (ℝ × ℝ) =>
    1 - (2 * z.1 ^ 2 / (z.2.1 ^ 2 + 2 * z.1 ^ 2)) * (2 * z.1 ^ 2 / (z.2.2 ^ 2 + 2 * z.1 ^ 2))) := by
  fun_prop

private lemma one_J1_eq {ξ : ℝ} (hξ : 0 < ξ) :
    1 - (1 - isoF ξ) ^ 2 = ∫ p : ℝ × ℝ, (1 - (2 * ξ ^ 2 / (p.1 ^ 2 + 2 * ξ ^ 2)) *
      (2 * ξ ^ 2 / (p.2 ^ 2 + 2 * ξ ^ 2))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hA : Integrable (fun x : ℝ => 2 * ξ ^ 2 / (x ^ 2 + 2 * ξ ^ 2)) (gaussianReal 0 1) := by
    have : (fun x : ℝ => 2 * ξ ^ 2 / (x ^ 2 + 2 * ξ ^ 2)) =
        fun x => 1 - x ^ 2 / (x ^ 2 + 2 * ξ ^ 2) := by
      funext x
      have hd : x ^ 2 + 2 * ξ ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    rw [this]
    exact (integrable_const _).sub (one_A_int hξ)
  have hprod : Integrable (fun p : ℝ × ℝ => (2 * ξ ^ 2 / (p.1 ^ 2 + 2 * ξ ^ 2)) *
      (2 * ξ ^ 2 / (p.2 ^ 2 + 2 * ξ ^ 2))) ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    hA.mul_prod hA
  rw [integral_sub (integrable_const _) hprod, integral_prod_mul
    (fun x : ℝ => 2 * ξ ^ 2 / (x ^ 2 + 2 * ξ ^ 2)) (fun x : ℝ => 2 * ξ ^ 2 / (x ^ 2 + 2 * ξ ^ 2)),
    ← one_w_eq hξ]
  simp
  ring

private lemma one_A_bounds {ξ : ℝ} (hξ : 0 < ξ) (x : ℝ) :
    0 ≤ 2 * ξ ^ 2 / (x ^ 2 + 2 * ξ ^ 2) ∧ 2 * ξ ^ 2 / (x ^ 2 + 2 * ξ ^ 2) ≤ 1 := by
  have hd : 0 < x ^ 2 + 2 * ξ ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hd]
  nlinarith [sq_nonneg x]

private lemma one_kappa_int {ξ : ℝ} (hξ : 0 < ξ) :
    Integrable (fun p : ℝ × ℝ => 1 - (2 * ξ ^ 2 / (p.1 ^ 2 + 2 * ξ ^ 2)) *
      (2 * ξ ^ 2 / (p.2 ^ 2 + 2 * ξ ^ 2))) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  refine Filter.Eventually.of_forall (fun p => ?_)
  have h1 := one_A_bounds hξ p.1
  have h2 := one_A_bounds hξ p.2
  have h3 : 0 ≤ (2 * ξ ^ 2 / (p.1 ^ 2 + 2 * ξ ^ 2)) * (2 * ξ ^ 2 / (p.2 ^ 2 + 2 * ξ ^ 2)) :=
    mul_nonneg h1.1 h2.1
  have h4 : (2 * ξ ^ 2 / (p.1 ^ 2 + 2 * ξ ^ 2)) * (2 * ξ ^ 2 / (p.2 ^ 2 + 2 * ξ ^ 2)) ≤ 1 := by
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

private lemma one_X_swap :
    ∫ ξ in Ioi (0:ℝ), (1 - (1 - isoF ξ) ^ 2) =
      ∫ p : ℝ × ℝ, (∫ ξ in Ioi (0:ℝ), (1 - (2 * ξ ^ 2 / (p.1 ^ 2 + 2 * ξ ^ 2)) *
        (2 * ξ ^ 2 / (p.2 ^ 2 + 2 * ξ ^ 2)))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun ξ hξ => one_J1_eq hξ)]
  refine integral_integral_swap (f := fun (ξ : ℝ) (p : ℝ × ℝ) => 1 -
    (2 * ξ ^ 2 / (p.1 ^ 2 + 2 * ξ ^ 2)) * (2 * ξ ^ 2 / (p.2 ^ 2 + 2 * ξ ^ 2))) ?_
  refine (integrable_prod_iff one_kappa_meas.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    exact one_kappa_int hξ
  · refine (one_J1_integrable.congr ?_)
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall (fun ξ hξ => ?_))
    have hξ' : 0 < ξ := hξ
    beta_reduce
    rw [one_J1_eq hξ']
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    have h1 := one_A_bounds hξ' p.1
    have h2 := one_A_bounds hξ' p.2
    have h4 : (2 * ξ ^ 2 / (p.1 ^ 2 + 2 * ξ ^ 2)) * (2 * ξ ^ 2 / (p.2 ^ 2 + 2 * ξ ^ 2)) ≤ 1 := by
      nlinarith [h1.1, h1.2, h2.1, h2.2]
    dsimp only
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]

private lemma one_ae_good :
    ∀ᵐ p : ℝ × ℝ ∂((gaussianReal 0 1).prod (gaussianReal 0 1)),
      p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ |p.1| ≠ |p.2| := by
  have : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hopen : IsOpen {p : ℝ × ℝ | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ |p.1| ≠ |p.2|} := by
    simp only [Set.setOf_and]
    exact (isOpen_ne_fun continuous_fst continuous_const).inter
      ((isOpen_ne_fun continuous_snd continuous_const).inter
        (isOpen_ne_fun (continuous_fst.abs) (continuous_snd.abs)))
  have := (Measure.ae_prod_mem_iff_ae_ae_mem (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    hopen.measurableSet).2 ?_
  · exact this
  · have hz : ∀ c : ℝ, ∀ᵐ y ∂(gaussianReal 0 1), y ≠ c := fun c =>
      (measure_eq_zero_iff_ae_notMem).1 (measure_singleton c)
    filter_upwards [hz 0] with x hx
    filter_upwards [hz 0, hz x, hz (-x)] with y hy1 hy2 hy3
    refine ⟨hx, hy1, fun h => ?_⟩
    rcases abs_eq_abs.1 h.symm with h | h
    · exact hy2 h
    · exact hy3 h

private lemma one_K_pt {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : |x| ≠ |y|) :
    ∫ ξ in Ioi (0:ℝ), (1 - (2 * ξ ^ 2 / (x ^ 2 + 2 * ξ ^ 2)) * (2 * ξ ^ 2 / (y ^ 2 + 2 * ξ ^ 2))) =
      Real.pi / (2 * Real.sqrt 2) * ((x ^ 2 + |x * y| + y ^ 2) / (|x| + |y|)) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set a := |x| / Real.sqrt 2 with ha
  set b := |y| / Real.sqrt 2 with hb
  have ha0 : 0 < a := div_pos (abs_pos.2 hx) hs
  have hb0 : 0 < b := div_pos (abs_pos.2 hy) hs
  have hab : a ≠ b := by
    intro h
    apply hxy
    have := congrArg (· * Real.sqrt 2) h
    simpa [ha, hb, div_mul_cancel₀ _ hs.ne'] using this
  have ha2 : a ^ 2 = x ^ 2 / 2 := by
    rw [ha, div_pow, sq_abs, hs2]
  have hb2 : b ^ 2 = y ^ 2 / 2 := by
    rw [hb, div_pow, sq_abs, hs2]
  have hpt : ∀ ξ ∈ Ioi (0:ℝ),
      (1 - (2 * ξ ^ 2 / (x ^ 2 + 2 * ξ ^ 2)) * (2 * ξ ^ 2 / (y ^ 2 + 2 * ξ ^ 2))) =
        1 - ξ ^ 4 / ((ξ ^ 2 + a ^ 2) * (ξ ^ 2 + b ^ 2)) := by
    intro ξ hξ
    have hξ' : 0 < ξ := hξ
    rw [ha2, hb2]
    have h1 : x ^ 2 + 2 * ξ ^ 2 ≠ 0 := by positivity
    have h2 : y ^ 2 + 2 * ξ ^ 2 ≠ 0 := by positivity
    have h3 : ξ ^ 2 + x ^ 2 / 2 ≠ 0 := by positivity
    have h4 : ξ ^ 2 + y ^ 2 / 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, one_xi_int ha0 hb0 hab]
  have hxa : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hya : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  have hsum : 0 < |x| + |y| := by positivity
  rw [abs_mul, hxa, hya, ha, hb]
  field_simp

private lemma one_K_ae :
    ∀ᵐ p : ℝ × ℝ ∂((gaussianReal 0 1).prod (gaussianReal 0 1)),
      ∫ ξ in Ioi (0:ℝ), (1 - (2 * ξ ^ 2 / (p.1 ^ 2 + 2 * ξ ^ 2)) *
        (2 * ξ ^ 2 / (p.2 ^ 2 + 2 * ξ ^ 2))) =
      Real.pi / (2 * Real.sqrt 2) * ((p.1 ^ 2 + |p.1 * p.2| + p.2 ^ 2) / (|p.1| + |p.2|)) := by
  filter_upwards [one_ae_good] with p hp
  exact one_K_pt hp.1 hp.2.1 hp.2.2

private lemma one_X_eq :
    ∫ ξ in Ioi (0:ℝ), (1 - (1 - isoF ξ) ^ 2) =
      Real.pi / (2 * Real.sqrt 2) * ∫ p : ℝ × ℝ,
        ((p.1 ^ 2 + |p.1 * p.2| + p.2 ^ 2) / (|p.1| + |p.2|))
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  rw [one_X_swap, integral_congr_ae one_K_ae, integral_const_mul]

private lemma one_gauss_prod (φ : ℝ × ℝ → ℝ) :
    ∫ p, φ p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      ∫ p : ℝ × ℝ, ((2 * Real.pi)⁻¹ * Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2)) * φ p := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    integral_withDensity_eq_integral_toReal_smul]
  · refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [smul_eq_mul]
    congr 1
    rw [ENNReal.toReal_mul, toReal_gaussianPDF, toReal_gaussianPDF]
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    have h2 : (0:ℝ) < 2 * Real.pi := by positivity
    have hsq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
      Real.mul_self_sqrt h2.le
    have hex : Real.exp (-p.1 ^ 2 / 2) * Real.exp (-p.2 ^ 2 / 2) =
        Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hinv : (2 * Real.pi)⁻¹ = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ := by
      rw [← mul_inv, hsq]
    rw [← hex, hinv]
    ring
  · exact (measurable_gaussianPDF 0 1).comp measurable_fst |>.mul
      ((measurable_gaussianPDF 0 1).comp measurable_snd)
  · exact Filter.Eventually.of_forall (fun p => ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top)

private lemma one_polar_pt {r θ : ℝ} (hr : 0 < r) :
    r • (((2 * Real.pi)⁻¹ * Real.exp (-((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) / 2)) *
      (((r * Real.cos θ) ^ 2 + |(r * Real.cos θ) * (r * Real.sin θ)| + (r * Real.sin θ) ^ 2) /
        (|r * Real.cos θ| + |r * Real.sin θ|))) =
    (r ^ 2 * Real.exp (-r ^ 2 / 2)) * ((2 * Real.pi)⁻¹ *
      ((1 + |Real.cos θ * Real.sin θ|) / (|Real.cos θ| + |Real.sin θ|))) := by
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hden : 0 < |Real.cos θ| + |Real.sin θ| := by
    by_contra h
    push_neg at h
    have h1 : |Real.cos θ| = 0 := by linarith [abs_nonneg (Real.cos θ), abs_nonneg (Real.sin θ)]
    have h2 : |Real.sin θ| = 0 := by linarith [abs_nonneg (Real.cos θ), abs_nonneg (Real.sin θ)]
    rw [abs_eq_zero] at h1 h2
    rw [h1, h2] at hcs
    norm_num at hcs
  have hexp : -((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) / 2 = -r ^ 2 / 2 := by
    have : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
      have : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 =
          r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      rw [this, hcs, mul_one]
    rw [this]
  have e1 : |r * Real.cos θ| = r * |Real.cos θ| := by rw [abs_mul, abs_of_pos hr]
  have e2 : |r * Real.sin θ| = r * |Real.sin θ| := by rw [abs_mul, abs_of_pos hr]
  have e3 : |(r * Real.cos θ) * (r * Real.sin θ)| = r ^ 2 * |Real.cos θ * Real.sin θ| := by
    rw [abs_mul, e1, e2, abs_mul]; ring
  have e4 : (r * Real.cos θ) ^ 2 + |(r * Real.cos θ) * (r * Real.sin θ)| +
      (r * Real.sin θ) ^ 2 = r ^ 2 * (1 + |Real.cos θ * Real.sin θ|) := by
    rw [e3]; linear_combination r ^ 2 * hcs
  have e5 : r * |Real.cos θ| + r * |Real.sin θ| = r * (|Real.cos θ| + |Real.sin θ|) := by ring
  rw [hexp, e1, e2, e4, e5, smul_eq_mul]
  have hr0 : r ≠ 0 := hr.ne'
  have hd0 : |Real.cos θ| + |Real.sin θ| ≠ 0 := hden.ne'
  field_simp

private lemma one_S_eq :
    ∫ p : ℝ × ℝ, ((p.1 ^ 2 + |p.1 * p.2| + p.2 ^ 2) / (|p.1| + |p.2|))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      (∫ r in Ioi (0:ℝ), r ^ 2 * Real.exp (-r ^ 2 / 2)) *
        ∫ θ in Ioo (-Real.pi) Real.pi, (2 * Real.pi)⁻¹ *
          ((1 + |Real.cos θ * Real.sin θ|) / (|Real.cos θ| + |Real.sin θ|)) := by
  rw [one_gauss_prod, ← integral_comp_polarCoord_symm, polarCoord_target]
  simp only [polarCoord_symm_apply]
  have hmeas : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  rw [setIntegral_congr_fun hmeas (g := fun z : ℝ × ℝ => (z.1 ^ 2 * Real.exp (-z.1 ^ 2 / 2)) *
    ((2 * Real.pi)⁻¹ * ((1 + |Real.cos z.2 * Real.sin z.2|) /
      (|Real.cos z.2| + |Real.sin z.2|)))) (fun z hz => one_polar_pt hz.1)]
  exact setIntegral_prod_mul (fun r : ℝ => r ^ 2 * Real.exp (-r ^ 2 / 2))
    (fun θ : ℝ => (2 * Real.pi)⁻¹ *
      ((1 + |Real.cos θ * Real.sin θ|) / (|Real.cos θ| + |Real.sin θ|))) _ _

private lemma one_radial :
    ∫ r in Ioi (0:ℝ), r ^ 2 * Real.exp (-r ^ 2 / 2) = Real.sqrt (2 * Real.pi) / 2 := by
  have h1 : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := Muon.Foundations.gaussian_moment_two
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero] at h1
  have h2 : ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
    have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have h3 : ∫ x : ℝ, gaussianPDFReal 0 1 x • x ^ 2 =
        (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2 / 2) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
      ring
    rw [h3] at h1
    field_simp at h1
    simpa only [neg_div] using h1
  have h4 : ∫ x : ℝ, (fun t : ℝ => t ^ 2 * Real.exp (-t ^ 2 / 2)) |x| =
      2 * ∫ x in Ioi (0:ℝ), x ^ 2 * Real.exp (-x ^ 2 / 2) :=
    integral_comp_abs (f := fun t : ℝ => t ^ 2 * Real.exp (-t ^ 2 / 2))
  simp only [sq_abs] at h4
  linarith

private lemma one_cs_pos {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) :
    0 < Real.cos θ + Real.sin θ := by
  have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have := Real.cos_sq_add_sin_sq θ
  nlinarith

private lemma one_inv_cs :
    ∫ θ in (0:ℝ)..(Real.pi / 2), 1 / (Real.cos θ + Real.sin θ) =
      Real.sqrt 2 * Real.log (1 + Real.sqrt 2) := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : 1 < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : 0 < Real.sqrt 2 := by linarith
  -- bounds on u = cos - sin on [0, π/2]
  have hu : ∀ θ ∈ Set.uIcc (0:ℝ) (Real.pi / 2),
      0 < Real.sqrt 2 - (Real.cos θ - Real.sin θ) ∧ 0 < Real.sqrt 2 + (Real.cos θ - Real.sin θ) := by
    intro θ hθ
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    have hsn := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [Real.pi_pos, hθ.2])
    have hc1 := Real.cos_le_one θ
    have hs1 := Real.sin_le_one θ
    constructor <;> linarith
  have hderiv : ∀ θ ∈ Set.uIcc (0:ℝ) (Real.pi / 2),
      HasDerivAt (fun θ : ℝ => (1 / (2 * Real.sqrt 2)) *
        (Real.log (Real.sqrt 2 - (Real.cos θ - Real.sin θ)) -
          Real.log (Real.sqrt 2 + (Real.cos θ - Real.sin θ))))
        (1 / (Real.cos θ + Real.sin θ)) θ := by
    intro θ hθ
    obtain ⟨hp, hm⟩ := hu θ hθ
    have hθ' : θ ∈ Set.Icc (0:ℝ) (Real.pi / 2) := by
      rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    have hcs := one_cs_pos hθ'.1 hθ'.2
    have hu' : HasDerivAt (fun θ : ℝ => Real.cos θ - Real.sin θ)
        (-Real.sin θ - Real.cos θ) θ := (Real.hasDerivAt_cos θ).sub (Real.hasDerivAt_sin θ)
    have h1 := ((hasDerivAt_const θ (Real.sqrt 2)).sub hu').log hp.ne'
    have h2 := ((hasDerivAt_const θ (Real.sqrt 2)).add hu').log hm.ne'
    refine (((h1.sub h2).const_mul (1 / (2 * Real.sqrt 2)))).congr_deriv ?_
    have hcs2 := Real.cos_sq_add_sin_sq θ
    have hne : Real.cos θ + Real.sin θ ≠ 0 := hcs.ne'
    simp only [Pi.sub_apply, Pi.add_apply]
    have hpm : (Real.sqrt 2 - (Real.cos θ - Real.sin θ)) * (Real.sqrt 2 + (Real.cos θ - Real.sin θ))
        = (Real.cos θ + Real.sin θ) ^ 2 := by linear_combination hsq - 2 * hcs2
    field_simp
    linear_combination (-2 * Real.sqrt 2) * hpm
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero]
    have e1 : Real.sqrt 2 - (0 - 1) = 1 + Real.sqrt 2 := by ring
    have e2 : Real.sqrt 2 + (0 - 1) = Real.sqrt 2 - 1 := by ring
    have e3 : Real.sqrt 2 - (1 - 0) = Real.sqrt 2 - 1 := by ring
    have e4 : Real.sqrt 2 + (1 - 0) = 1 + Real.sqrt 2 := by ring
    rw [e1, e2, e3, e4]
    have hinv : Real.log (Real.sqrt 2 - 1) = -Real.log (1 + Real.sqrt 2) := by
      rw [← Real.log_inv]
      congr 1
      have : (1 + Real.sqrt 2) * (Real.sqrt 2 - 1) = 1 := by nlinarith [hsq]
      field_simp
      nlinarith [hsq]
    rw [hinv]
    field_simp
    rw [hsq]
    ring
  · refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const (by fun_prop) (fun θ hθ => ?_)
    have hθ' : θ ∈ Set.Icc (0:ℝ) (Real.pi / 2) := by
      rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    exact (one_cs_pos hθ'.1 hθ'.2).ne'

private lemma one_I_val :
    ∫ θ in (0:ℝ)..(Real.pi / 2), (1 + Real.cos θ * Real.sin θ) / (Real.cos θ + Real.sin θ) =
      1 + Real.log (1 + Real.sqrt 2) / Real.sqrt 2 := by
  have hpt : ∀ θ ∈ Set.uIcc (0:ℝ) (Real.pi / 2),
      (1 + Real.cos θ * Real.sin θ) / (Real.cos θ + Real.sin θ) =
        (1 / 2) * (Real.cos θ + Real.sin θ) + (1 / 2) * (1 / (Real.cos θ + Real.sin θ)) := by
    intro θ hθ
    have hθ' : θ ∈ Set.Icc (0:ℝ) (Real.pi / 2) := by
      rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    have hcs := one_cs_pos hθ'.1 hθ'.2
    have hcs2 := Real.cos_sq_add_sin_sq θ
    field_simp
    linear_combination (-1 : ℝ) * hcs2 + 0
  have hint1 : IntervalIntegrable (fun θ : ℝ => Real.cos θ + Real.sin θ) MeasureTheory.volume 0
      (Real.pi / 2) := (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hint2 : IntervalIntegrable (fun θ : ℝ => 1 / (Real.cos θ + Real.sin θ))
      MeasureTheory.volume 0 (Real.pi / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const (by fun_prop) (fun θ hθ => ?_)
    have hθ' : θ ∈ Set.Icc (0:ℝ) (Real.pi / 2) := by
      rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    exact (one_cs_pos hθ'.1 hθ'.2).ne'
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add (hint1.const_mul _)
    (hint2.const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (Real.continuous_cos.intervalIntegrable _ _)
      (Real.continuous_sin.intervalIntegrable _ _), integral_cos, integral_sin, one_inv_cs]
  simp only [Real.sin_pi_div_two, Real.sin_zero, Real.cos_pi_div_two, Real.cos_zero]
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  linear_combination (Real.log (1 + Real.sqrt 2)) * h2

private lemma one_den_pos (θ : ℝ) : 0 < |Real.cos θ| + |Real.sin θ| := by
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  by_contra h
  push_neg at h
  have h1 : |Real.cos θ| = 0 := by linarith [abs_nonneg (Real.cos θ), abs_nonneg (Real.sin θ)]
  have h2 : |Real.sin θ| = 0 := by linarith [abs_nonneg (Real.cos θ), abs_nonneg (Real.sin θ)]
  rw [abs_eq_zero] at h1 h2
  rw [h1, h2] at hcs
  norm_num at hcs

private lemma one_theta :
    ∫ θ in Ioo (-Real.pi) Real.pi, (2 * Real.pi)⁻¹ *
        ((1 + |Real.cos θ * Real.sin θ|) / (|Real.cos θ| + |Real.sin θ|)) =
      (2 * Real.pi)⁻¹ * (4 * (1 + Real.log (1 + Real.sqrt 2) / Real.sqrt 2)) := by
  set f : ℝ → ℝ := fun θ => (1 + |Real.cos θ * Real.sin θ|) / (|Real.cos θ| + |Real.sin θ|)
    with hf
  have hcont : Continuous f :=
    Continuous.div (by fun_prop) (by fun_prop) (fun θ => (one_den_pos θ).ne')
  have hint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hneg : ∀ θ, f (-θ) = f θ := by
    intro θ
    simp only [hf, Real.cos_neg, Real.sin_neg, mul_neg, abs_neg]
  have hpi : ∀ θ, f (Real.pi - θ) = f θ := by
    intro θ
    simp only [hf, Real.cos_pi_sub, Real.sin_pi_sub, neg_mul, abs_neg]
  have hI : ∫ θ in (0:ℝ)..(Real.pi / 2), f θ =
      1 + Real.log (1 + Real.sqrt 2) / Real.sqrt 2 := by
    rw [← one_I_val]
    refine intervalIntegral.integral_congr (fun θ hθ => ?_)
    have hθ' : θ ∈ Set.Icc (0:ℝ) (Real.pi / 2) := by
      rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ'.1], hθ'.2⟩
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ'.1 (by linarith [Real.pi_pos, hθ'.2])
    simp only [hf]
    rw [abs_of_nonneg hc, abs_of_nonneg hs, abs_of_nonneg (mul_nonneg hc hs)]
  have h1 : ∫ θ in (-Real.pi)..(0:ℝ), f θ = ∫ θ in (0:ℝ)..Real.pi, f θ := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := Real.pi) f
    simp only [hneg, neg_zero] at this
    rw [this]
  have h2 : ∫ θ in (Real.pi / 2)..Real.pi, f θ = ∫ θ in (0:ℝ)..(Real.pi / 2), f θ := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := Real.pi / 2) f Real.pi
    simp only [hpi] at this
    rw [this]
    congr 1 <;> ring
  have h3 : ∫ θ in (0:ℝ)..Real.pi, f θ = 2 * ∫ θ in (0:ℝ)..(Real.pi / 2), f θ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 (Real.pi / 2))
      (hint (Real.pi / 2) Real.pi), h2]
    ring
  have h4 : ∫ θ in (-Real.pi)..Real.pi, f θ = 4 * ∫ θ in (0:ℝ)..(Real.pi / 2), f θ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-Real.pi) 0) (hint 0 Real.pi),
      h1, h3]
    ring
  rw [integral_const_mul]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    h4, hI]

private lemma one_closed :
    Cbeta 0 1 1 = (1 + Real.log (1 + Real.sqrt 2) / Real.sqrt 2) / (2 * Real.sqrt Real.pi) := by
  rw [one_Cbeta_eq, one_X_eq, one_S_eq, one_radial, one_theta]
  have hp := Real.pi_pos
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 hp
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpp : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hp.le
  have hm : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) _
  rw [hm]
  field_simp
  rw [hpp]
  ring

private lemma one_num1 :
    3 / (4 * Real.sqrt Real.pi) <
      (1 + Real.log (1 + Real.sqrt 2) / Real.sqrt 2) / (2 * Real.sqrt Real.pi) := by
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hlo : (1.414 : ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hhi : Real.sqrt 2 < (1.4143 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  set t := Real.sqrt (1 + Real.sqrt 2) with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 (by linarith)
  have ht1 : (31 / 20 : ℝ) ≤ t := by
    rw [ht]; apply Real.le_sqrt_of_sq_le; nlinarith
  have hlog : Real.log (1 + Real.sqrt 2) = 2 * Real.log t := by
    rw [ht, Real.log_sqrt (by linarith)]; ring
  have hl1 := Real.one_sub_inv_le_log_of_pos ht0
  have hinv : t⁻¹ ≤ 20 / 31 := by
    rw [inv_le_comm₀ ht0 (by norm_num)]; linarith
  have hL : Real.sqrt 2 / 2 < Real.log (1 + Real.sqrt 2) := by
    rw [hlog]; linarith
  have hq : 1 / 2 < Real.log (1 + Real.sqrt 2) / Real.sqrt 2 := by
    rw [lt_div_iff₀ hs]; linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

private lemma one_num2 :
    (Real.pi * (1 + 9 * Real.pi / 32)) ^ (-(1 / 2 : ℝ)) < 3 / (4 * Real.sqrt Real.pi) := by
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 hp
  have hA : 0 < Real.pi * (1 + 9 * Real.pi / 32) := by positivity
  have hsA : 0 < Real.sqrt (Real.pi * (1 + 9 * Real.pi / 32)) := Real.sqrt_pos.2 hA
  rw [Real.rpow_neg hA.le, ← Real.sqrt_eq_rpow, inv_eq_one_div,
    div_lt_div_iff₀ hsA (by positivity)]
  by_contra h
  push_neg at h
  have h1 : (3 * Real.sqrt (Real.pi * (1 + 9 * Real.pi / 32))) ^ 2 ≤ (1 * (4 * Real.sqrt Real.pi)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h 2
  simp only [mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hp.le] at h1
  nlinarith

end OneHelpers

/-- `thm:app-iso-one`, snapshot `cr-2026-10-23`. The whole environment, verbatim
(`sections/05b-isotropic/section.tex`, l.1768–1777):
```latex
\begin{theorem}[The constant at aspect ratio one]\label{thm:app-iso-one}
The constant \cref{eqn:app-iso-C} at $\gin=\gout=1$ is
\begin{equation}\label{eqn:app-iso-C1}
C(1)=\frac{1+\log(1+\sqrt2)/\sqrt2}{2\sqrt\pi},
\end{equation}
and
\begin{equation}\label{eqn:app-iso-C1-interpolation}
C(1)>\frac{3}{4\sqrt\pi}>\Big[\pi\Big(1+\frac{9\pi}{32}\Big)\Big]^{-1/2}.
\end{equation}
\end{theorem}
```

Encoding: `C(1)` is `Cbeta 0 1 1` (`C_0(1,1)`, the momentum-zero square constant). The two displayed
claims are the two conjuncts: the closed form `eqn:app-iso-C1`, and the chain
`eqn:app-iso-C1-interpolation`, `C(1) > 3/(4√π) > [π(1+9π/32)]^{-1/2}`, split into its two strict
inequalities. The exponent `-1/2` is a real power. -/
theorem thm_app_iso_one :
    Cbeta 0 1 1 = (1 + Real.log (1 + Real.sqrt 2) / Real.sqrt 2) / (2 * Real.sqrt Real.pi) ∧
    3 / (4 * Real.sqrt Real.pi) < Cbeta 0 1 1 ∧
    (Real.pi * (1 + 9 * Real.pi / 32)) ^ (-(1 / 2 : ℝ)) < 3 / (4 * Real.sqrt Real.pi) := by
  refine ⟨one_closed, ?_, one_num2⟩
  rw [one_closed]
  exact one_num1

end Muon.Isotropic

end

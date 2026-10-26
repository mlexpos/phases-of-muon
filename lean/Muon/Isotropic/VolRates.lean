import Muon.Isotropic.VolKernels
import Muon.Isotropic.ZeroRidge
import Muon.Isotropic.Helpers
import Muon.Isotropic.VolFactor

/-!
# Appendix F: lag lower bound, lag sum and lag profile at zero ridge (task L-F.10)

Snapshot `cr-2026-10-23`. Source: `sections/05b-isotropic/section.tex`. Labels of this package:
`lem:app-iso-lag-lower`, `thm:app-iso-vol-rate`, `thm:app-iso-vol-profile`, with the constants of
their statements. `thm:app-iso-small-volatility` (first display only; it needs no `v_iso`).
Deferred to L-F.10b (depends on L-F.12: `v_iso`, `HasZeroRidgeVol`): `thm:app-iso-small-volatility`
(second display) and `thm:app-iso-zero-ridge`(ii).
Card: `sections/05b-isotropic/CARD.md` §2, §3, §5 (L-F.10).

Reuse: `lagCoeff` (`C̄_{1,ℓ}(ϱ)`) of `VolKernels`; `psiIso` of `ZeroRidge`; `isoC`, `isoC'`,
`isoEminus`, `isoEplus`, `isoEbar`, `isoPhi`, `isoGammaCirc` of `Helpers`; `isoM1`, `isoLbar1`,
`isoLbar2`, `isoCatalan` of `VolKernels`.

The explicit object for `C̄_{1,ℓ}(0)` is `lagCoeff β γ 0 ℓ`. Its identification with the limit of
`prop:app-iso-vol-momentum`(ii) is not stated here; it belongs to L-F.12.
-/

open MeasureTheory Set

noncomputable section

namespace Muon.Isotropic

/-! ## Constants of the lag lower bound -/

/- `eqn:app-iso-k`, snapshot `cr-2026-10-23`, `section.tex` l.2313–2314. Defines `𝖼''_β` and `𝗄_β`.

\mathsf c''_\bmom\defeq\frac1{\log(1/\bmom)}+\mathsf c_\bmom+\mathsf c'_\bmom,\qquad
\mathsf k_\bmom\defeq\frac{\mathsf e^-_\bmom\,(e^2-1)\,e^{-3}}{\pi^2\,\mathsf e^+_\bmom}.
-/

/-- `𝖼''_β = 1/log(1/β) + 𝖼_β + 𝖼'_β` (`eqn:app-iso-k`). -/
def isoCpp (β : ℝ) : ℝ := 1 / Real.log (1 / β) + isoC β + isoC' β

/-- `𝗄_β = 𝖾^-_β (e²−1) e^{−3} / (π² 𝖾^+_β)` (`eqn:app-iso-k`). -/
def isoKk (β : ℝ) : ℝ :=
  isoEminus β * (Real.exp 2 - 1) * Real.exp (-3) / (Real.pi ^ 2 * isoEplus β)

/-- `m_ε = ψ(ε)` for `ε > 0` and `m_0 = γ` (`lem:app-iso-lag-lower`, `section.tex` l.2317–2327). -/
def isoLagPsi (β γ ε : ℝ) : ℝ := if ε = 0 then γ else psiIso β γ γ ε

/-- `𝖼^+_β = 𝖼_β + 𝖼'_β` (`section.tex` l.2416). -/
def isoCpl (β : ℝ) : ℝ := isoC β + isoC' β

/-! ## Constants of the lag sum and the lag profile at zero ridge -/

/- `eqn:app-iso-Kpm`, snapshot `cr-2026-10-23`, `section.tex` l.2775–2777. Defines `𝖪_0`, `𝖪_1`, `𝖪_2`.

\mathsf K_0\defeq11\bar{\mathsf e}_\bmom+\frac{48\,\bar{\mathsf e}_\bmom^3}{\Phi(1)^2},\qquad
\mathsf K_1\defeq8+\frac{32\,\bar{\mathsf e}_\bmom^2}{\Phi(1)^2},\qquad
\mathsf K_2\defeq\frac2{\Phi(1)}+\frac{4\,\bar{\mathsf e}_\bmom}{\Phi(1)^2},
-/

/-- `𝖪_0 = 11 ē + 48 ē³/Φ(1)²` (`isoEbar` = `ē`, `isoPhi 1` = `Φ(1)`). -/
def isoK0 (β : ℝ) : ℝ := 11 * isoEbar β + 48 * isoEbar β ^ 3 / isoPhi 1 ^ 2

/-- `𝖪_1 = 8 + 32 ē²/Φ(1)²`. -/
def isoK1 (β : ℝ) : ℝ := 8 + 32 * isoEbar β ^ 2 / isoPhi 1 ^ 2

/-- `𝖪_2 = 2/Φ(1) + 4 ē/Φ(1)²`. -/
def isoK2 (β : ℝ) : ℝ := 2 / isoPhi 1 + 4 * isoEbar β / isoPhi 1 ^ 2

/- `eqn:app-iso-Kpm`, snapshot `cr-2026-10-23`, `section.tex` l.2779–2781. Defines `𝖪^±_β`.

\begin{equation}\label{eqn:app-iso-Kpm}
\mathsf K^-_\bmom\defeq\frac52\,\bar{\mathsf e}_\bmom(\mathsf M_1+1),\qquad
\mathsf K^+_\bmom\defeq\frac{\bar{\mathsf e}_\bmom\mathsf M_1}2+\mathsf K_0+\mathsf K_1\mathsf c^+_\bmom+2\mathsf K_2(\mathsf c^+_\bmom)^2+\mathsf K_1\bar{\mathsf L}_1+2\mathsf K_2\bar{\mathsf L}_2 .
-/

/-- `𝖪^-_β = (5/2) ē (𝖬_1 + 1)`. -/
def isoKminus (β : ℝ) : ℝ := 5 / 2 * isoEbar β * (isoM1 + 1)

/-- `𝖪^+_β = ē 𝖬_1/2 + 𝖪_0 + 𝖪_1 𝖼^+ + 2 𝖪_2 (𝖼^+)² + 𝖪_1 L̄_1 + 2 𝖪_2 L̄_2`. -/
def isoKplus (β : ℝ) : ℝ :=
  isoEbar β * isoM1 / 2 + isoK0 β + isoK1 β * isoCpl β + 2 * isoK2 β * isoCpl β ^ 2
    + isoK1 β * isoLbar1 β + 2 * isoK2 β * isoLbar2 β

/- `thm:app-iso-vol-profile`, snapshot `cr-2026-10-23`, `section.tex` l.2904–2907. Defines `𝒢` (`isoCalG`).

\[
\mathcal G(x)\defeq\begin{cases}1-x+x\log x,&0\le x\le1,\\ 0,&x\ge1,\end{cases}
\]
with $\mathcal G(0)=1$, and
-/

/-- `𝒢(x) = 1 − x + x log x` for `0 ≤ x ≤ 1`, and `0` for `x ≥ 1`. The source defines `𝒢` on
`x ≥ 0`; the value for `x < 0` is a Lean convention outside the source. -/
def isoCalG (x : ℝ) : ℝ := if x ≤ 1 then 1 - x + x * Real.log x else 0

/- `eqn:app-iso-Kpm`, snapshot `cr-2026-10-23`, `section.tex` l.2908–2911. Defines `𝖪_3`, `𝖪_4`, `𝖪_5`.

\[
\mathsf K_3\defeq14\bar{\mathsf e}_\bmom+\frac{32\,\bar{\mathsf e}_\bmom^2}{\Phi(1)},\qquad
\mathsf K_4\defeq4+\frac{8\,\bar{\mathsf e}_\bmom}{\Phi(1)},\qquad
\mathsf K_5\defeq4+\frac{4+8\bar{\mathsf e}_\bmom}{\Phi(1)}+\frac{8\bar{\mathsf e}_\bmom+32\bar{\mathsf e}_\bmom^2}{\Phi(1)^2},
-/

/-- `𝖪_3 = 14 ē + 32 ē²/Φ(1)`. -/
def isoK3 (β : ℝ) : ℝ := 14 * isoEbar β + 32 * isoEbar β ^ 2 / isoPhi 1

/-- `𝖪_4 = 4 + 8 ē/Φ(1)`. -/
def isoK4 (β : ℝ) : ℝ := 4 + 8 * isoEbar β / isoPhi 1

/-- `𝖪_5 = 4 + (4 + 8 ē)/Φ(1) + (8 ē + 32 ē²)/Φ(1)²`. -/
def isoK5 (β : ℝ) : ℝ :=
  4 + (4 + 8 * isoEbar β) / isoPhi 1 + (8 * isoEbar β + 32 * isoEbar β ^ 2) / isoPhi 1 ^ 2

/- `thm:app-iso-vol-profile`, snapshot `cr-2026-10-23`, `section.tex` l.2914–2915. Defines `𝖪^pr_β` (`isoKpr`).

\mathsf K^{\rm pr}_\bmom\defeq\big(\bar{\mathsf e}_\bmom\mathsf M_1+1\big)+\frac{2(\mathsf K_3+\mathsf K_4\mathsf c^+_\bmom)(\Phi(1)+\bar{\mathsf e}_\bmom\mathsf M_1)}{\Phi(1)}\Big(1+\log\frac1{2\Phi(1)}\Big)+\frac{\mathsf K_4\bar{\mathsf L}_1}{\Phi(1)},
\]
-/

/-- `𝖪^pr_β` (`section.tex` l.2914–2915). -/
def isoKpr (β : ℝ) : ℝ :=
  (isoEbar β * isoM1 + 1)
    + 2 * (isoK3 β + isoK4 β * isoCpl β) * (isoPhi 1 + isoEbar β * isoM1) / isoPhi 1
        * (1 + Real.log (1 / (2 * isoPhi 1)))
    + isoK4 β * isoLbar1 β / isoPhi 1

/- `thm:app-iso-vol-profile`, snapshot `cr-2026-10-23`, `section.tex` l.2916–2918. Defines `δ_β` (`isoDecay`) and `𝖪^dec_β` (`isoKdec`).

\[
\delta_\bmom\defeq\min\Big(\frac1{8\bar{\mathsf e}_\bmom},\ \frac{\log(1/\bmom)}8\Big),\qquad
\mathsf K^{\rm dec}_\bmom\defeq\mathsf K_5\Big(1+\mathsf c^+_\bmom+\frac1{\delta_\bmom}\Big)\mathsf M_e\Big(1+\frac8{7(1-\bmom^2)}+8\bar{\mathsf e}_\bmom\Big)e^{\delta_\bmom\mathsf c^+_\bmom}.
-/

/-- `δ_β = min(1/(8 ē), log(1/β)/8)`. -/
def isoDecay (β : ℝ) : ℝ := min (1 / (8 * isoEbar β)) (Real.log (1 / β) / 8)

/-- `𝖬_e = 2 + 16 𝖦/π²`, the closed form of `𝖬_e = 𝔼⋆ e^{τ/4}` (`section.tex` l.2684), with
`𝖦 = isoCatalan`. The moment as an integral over `ν⋆` is not defined here. -/
def isoMe : ℝ := 2 + 16 * isoCatalan / Real.pi ^ 2

/-- `𝖪^dec_β = 𝖪_5 (1 + 𝖼^+ + 1/δ_β) 𝖬_e (1 + 8/(7(1−β²)) + 8 ē) e^{δ_β 𝖼^+}`. -/
def isoKdec (β : ℝ) : ℝ :=
  isoK5 β * (1 + isoCpl β + 1 / isoDecay β) * isoMe
    * (1 + 8 / (7 * (1 - β ^ 2)) + 8 * isoEbar β) * Real.exp (isoDecay β * isoCpl β)

/-! ## Statements -/

private lemma p10_isoKk_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 ≤ isoKk β := by
  have hΦ : 0 < isoPhiDeriv 1 := (lem_app_iso_gaussian_ii.2.1 1 one_pos).2.1
  have hEm : 0 ≤ isoEminus β := by
    unfold isoEminus; positivity
  have hEp : 0 < isoEplus β := by
    unfold isoEplus
    have h1 : 0 < 1 - β := by linarith
    have h2 : 0 < 1 - β ^ 2 := by nlinarith
    positivity
  unfold isoKk
  have he : (0 : ℝ) ≤ Real.exp 2 - 1 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have := Real.exp_pos (-3)
  positivity

private lemma p10_psi_le {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    {ε : ℝ} (hε : 0 < ε) : isoLagPsi β γ ε ≤ γ := by
  have hlink : IsIsoLink (Muon.DetEquiv.rW (Muon.emaW β)) := by
    obtain ⟨_, hd, hmono, _⟩ := lem_app_iso_weights_i hβ0.le hβ1
    refine ⟨fun q hq => (hd q hq).1.continuousWithinAt, (hmono hβ0).1, ?_⟩
    unfold Muon.DetEquiv.rW; simp
  have hmem := ((lem_app_iso_comparison_i hlink hγ hγ).2.2.2.1 ε hε).1
  have h := hmem.2
  rw [min_self] at h
  unfold isoLagPsi psiIso qIso
  rw [if_neg hε.ne']
  exact h.le

private lemma p10_hasDeriv {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (Muon.DetEquiv.rW (Muon.emaW β))
      (deriv (Muon.DetEquiv.rW (Muon.emaW β)) q) q := by
  obtain ⟨_, hd, _⟩ := lem_app_iso_weights_i hβ0.le hβ1
  have := (hd q hq.le).1.hasDerivAt (Ici_mem_nhds hq)
  exact this.differentiableAt.hasDerivAt

private lemma p10_pos_of_one_le {β z : ℝ} (hβ1 : β < 1) (hz : 1 ≤ (1 - β) ^ 2 * z) : 0 < z := by
  by_contra h
  push_neg at h
  have : (1 - β) ^ 2 * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h
  linarith

private lemma p10_log_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {z y : ℝ}
    (hz : 1 ≤ (1 - β) ^ 2 * z) (hzy : z ≤ y) :
    isoEminus β * Real.log (y / z) ≤
      Muon.DetEquiv.rW (Muon.emaW β) y - Muon.DetEquiv.rW (Muon.emaW β) z := by
  have hz0 : 0 < z := p10_pos_of_one_le hβ1 hz
  set r := Muon.DetEquiv.rW (Muon.emaW β) with hr
  have hcnt := (lem_app_iso_count_ii hβ0 hβ1).2
  have hmono : MonotoneOn (fun x => r x - isoEminus β * Real.log x) (Ici z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici z)
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hz0 hx
      exact ((p10_hasDeriv hβ0 hβ1 hx0).continuousAt.sub
        ((Real.continuousAt_log hx0.ne').const_mul _)).continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := lt_trans hz0 hx
      exact ((p10_hasDeriv hβ0 hβ1 hx0).differentiableAt.sub
        ((Real.differentiableAt_log hx0.ne').const_mul _)).differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := lt_trans hz0 hx
      have hd : HasDerivAt (fun x => r x - isoEminus β * Real.log x)
          (deriv r x - isoEminus β * x⁻¹) x :=
        (p10_hasDeriv hβ0 hβ1 hx0).sub ((Real.hasDerivAt_log hx0.ne').const_mul _)
      rw [hd.deriv]
      have h1 : 1 ≤ (1 - β) ^ 2 * x := by
        have : (1 - β) ^ 2 * z ≤ (1 - β) ^ 2 * x :=
          mul_le_mul_of_nonneg_left hx.le (sq_nonneg _)
        linarith
      have h2 := hcnt x hx0 h1
      rw [sub_nonneg, ← div_eq_mul_inv, div_le_iff₀ hx0]
      linarith
  have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hzy) hzy
  simp only at this
  rw [Real.log_div (by linarith) hz0.ne']
  linarith

private lemma p10_D_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {z y : ℝ}
    (hz : 1 ≤ (1 - β) ^ 2 * z) (hzy : z < y) (hy : y ≤ z * Real.exp 2) :
    isoEminus β * Real.exp (-3) / z ^ 2 ≤ isoDivDiff β y z := by
  have hz0 : 0 < z := p10_pos_of_one_le hβ1 hz
  have hy0 : 0 < y := lt_trans hz0 hzy
  have hEm : 0 ≤ isoEminus β := by
    have hΦ : 0 < isoPhiDeriv 1 := (lem_app_iso_gaussian_ii.2.1 1 one_pos).2.1
    unfold isoEminus; positivity
  have hlog := p10_log_lower hβ0 hβ1 hz hzy.le
  have hl2 : 1 - z / y ≤ Real.log (y / z) := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hy0 hz0)
    rwa [inv_div] at this
  have hdiff : isoEminus β * (1 - z / y) ≤
      Muon.DetEquiv.rW (Muon.emaW β) y - Muon.DetEquiv.rW (Muon.emaW β) z :=
    le_trans (mul_le_mul_of_nonneg_left hl2 hEm) hlog
  unfold isoDivDiff
  rw [if_neg hzy.ne']
  set s := Real.sqrt (y * z) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (mul_pos hy0 hz0)
  have hs1 : s ≤ z * Real.exp 1 := by
    rw [hs, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    calc y * z ≤ z * Real.exp 2 * z := mul_le_mul_of_nonneg_right hy hz0.le
      _ = (z * Real.exp 1) ^ 2 := by rw [this]; ring
  have hys : y * s ≤ z ^ 2 * Real.exp 3 := by
    have h3 : Real.exp 3 = Real.exp 2 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    calc y * s ≤ (z * Real.exp 2) * (z * Real.exp 1) :=
          mul_le_mul hy hs1 hs0.le (by positivity)
      _ = z ^ 2 * Real.exp 3 := by rw [h3]; ring
  have hyz : 0 < y - z := by linarith
  rw [le_div_iff₀ (mul_pos hyz hs0)]
  have key : isoEminus β * Real.exp (-3) / z ^ 2 * ((y - z) * s) ≤
      isoEminus β * (1 - z / y) := by
    have e1 : 1 - z / y = (y - z) / y := by field_simp
    have h4 : Real.exp (-3) * s * y ≤ z ^ 2 := by
      have : Real.exp (-3) * Real.exp 3 = 1 := by rw [← Real.exp_add]; norm_num
      calc Real.exp (-3) * s * y = Real.exp (-3) * (y * s) := by ring
        _ ≤ Real.exp (-3) * (z ^ 2 * Real.exp 3) :=
            mul_le_mul_of_nonneg_left hys (Real.exp_pos _).le
        _ = z ^ 2 := by nlinarith [this]
    have h5 : Real.exp (-3) * s / z ^ 2 ≤ 1 / y := by
      rw [div_le_div_iff₀ (by positivity) hy0]; linarith
    have h6 := mul_le_mul_of_nonneg_left h5 (mul_nonneg hEm hyz.le)
    rw [e1]
    calc isoEminus β * Real.exp (-3) / z ^ 2 * ((y - z) * s)
        = isoEminus β * (y - z) * (Real.exp (-3) * s / z ^ 2) := by ring
      _ ≤ isoEminus β * (y - z) * (1 / y) := h6
      _ = isoEminus β * ((y - z) / y) := by ring
  linarith

private lemma p10_count_y {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {z y : ℝ}
    (hz : 1 ≤ (1 - β) ^ 2 * z) (hzy : z ≤ y) (hy : y ≤ z * Real.exp 2) :
    Muon.DetEquiv.rW (Muon.emaW β) y < Muon.DetEquiv.rW (Muon.emaW β) z + isoCpp β := by
  have hz0 : 0 < z := p10_pos_of_one_le hβ1 hz
  have hy0 : 0 < y := lt_of_lt_of_le hz0 hzy
  have hy1 : 1 ≤ (1 - β) ^ 2 * y := by
    have : (1 - β) ^ 2 * z ≤ (1 - β) ^ 2 * y := mul_le_mul_of_nonneg_left hzy (sq_nonneg _)
    linarith
  obtain ⟨hc, -⟩ := lem_app_iso_count_i hβ0 hβ1
  have h1 := (hc y hy1).2
  have h2 := (hc z hz).1
  have hL : 0 < Real.log (1 / β) := Real.log_pos (by rw [lt_div_iff₀ hβ0]; linarith)
  have hb : 0 < (1 - β) ^ 2 := by have : 0 < 1 - β := by linarith
                                  positivity
  have hlogyz : Real.log (y / z) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (div_pos hy0 hz0), div_le_iff₀ hz0]; linarith [mul_comm z (Real.exp 2)]
  have hn : isoN β y = isoN β z + Real.log (y / z) / (2 * Real.log (1 / β)) := by
    unfold isoN
    rw [Real.log_div hy0.ne' hz0.ne', Real.log_mul hb.ne' hy0.ne', Real.log_mul hb.ne' hz0.ne']
    ring
  have h3 : Real.log (y / z) / (2 * Real.log (1 / β)) ≤ 1 / Real.log (1 / β) := by
    rw [div_le_div_iff₀ (by positivity) hL]
    nlinarith
  unfold isoCpp
  linarith

private lemma p10_count_z {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {z : ℝ}
    (hz : 1 ≤ (1 - β) ^ 2 * z) (ℓ : ℕ) :
    Muon.DetEquiv.rW (Muon.emaW β) (z / β ^ (2 * ℓ)) <
      Muon.DetEquiv.rW (Muon.emaW β) z + (ℓ : ℝ) + isoCpp β := by
  have hz0 : 0 < z := p10_pos_of_one_le hβ1 hz
  have hpow : 0 < β ^ (2 * ℓ) := pow_pos hβ0 _
  have hp1 : β ^ (2 * ℓ) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hzz : z ≤ z / β ^ (2 * ℓ) := by
    rw [le_div_iff₀ hpow]; nlinarith
  have hy1 : 1 ≤ (1 - β) ^ 2 * (z / β ^ (2 * ℓ)) := by
    have : (1 - β) ^ 2 * z ≤ (1 - β) ^ 2 * (z / β ^ (2 * ℓ)) :=
      mul_le_mul_of_nonneg_left hzz (sq_nonneg _)
    linarith
  obtain ⟨hc, -⟩ := lem_app_iso_count_i hβ0 hβ1
  have h1 := (hc _ hy1).2
  have h2 := (hc z hz).1
  have hL : 0 < Real.log (1 / β) := Real.log_pos (by rw [lt_div_iff₀ hβ0]; linarith)
  have hb : 0 < (1 - β) ^ 2 := by have : 0 < 1 - β := by linarith
                                  positivity
  have hn : isoN β (z / β ^ (2 * ℓ)) = isoN β z + (ℓ : ℝ) := by
    unfold isoN
    have e : Real.log ((1 - β) ^ 2 * (z / β ^ (2 * ℓ))) =
        Real.log ((1 - β) ^ 2 * z) + 2 * ℓ * Real.log (1 / β) := by
      rw [show (1 - β) ^ 2 * (z / β ^ (2 * ℓ)) = (1 - β) ^ 2 * z * (1 / β) ^ (2 * ℓ) by
        rw [one_div, inv_pow]; field_simp]
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast; ring
    rw [e]; field_simp
  have hcpl : 0 < 1 / Real.log (1 / β) := by positivity
  unfold isoCpp
  linarith

private lemma p10_Fw_anti {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {z y : ℝ} (hz : 0 ≤ z)
    (hzy : z ≤ y) :
    Muon.DetEquiv.Fw (Muon.emaW β) y ≤ Muon.DetEquiv.Fw (Muon.emaW β) z := by
  have hJ := Muon.DetEquiv.lem_app_de_scalar_i
  have hsum : ∀ x : ℝ, 0 ≤ x → Summable (fun j : ℕ => Muon.emaW β j ^ 2 *
      Muon.DetEquiv.J (Muon.emaW β j ^ 2 * x)) := by
    intro x hx
    have hg : Summable (fun j : ℕ => ((1 - β) ^ 2) * (β ^ 2) ^ j) :=
      (summable_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left _
    have hw2 : ∀ j : ℕ, Muon.emaW β j ^ 2 = (1 - β) ^ 2 * (β ^ 2) ^ j := by
      intro j; unfold Muon.emaW; rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j 2]
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hg
    · exact mul_nonneg (sq_nonneg _) (hJ.2.2.1 _ (by positivity)).1.le
    · calc Muon.emaW β j ^ 2 * Muon.DetEquiv.J (Muon.emaW β j ^ 2 * x)
          ≤ Muon.emaW β j ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (hJ.2.2.1 _ (by positivity)).2 (sq_nonneg _)
        _ = (1 - β) ^ 2 * (β ^ 2) ^ j := by rw [mul_one, hw2]
  unfold Muon.DetEquiv.Fw
  refine Summable.tsum_le_tsum (fun j => ?_) (hsum y (hz.trans hzy)) (hsum z hz)
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact hJ.2.1.antitoneOn (mem_Ici.2 (mul_nonneg (sq_nonneg _) hz))
    (mem_Ici.2 (mul_nonneg (sq_nonneg _) (hz.trans hzy))) (mul_le_mul_of_nonneg_left hzy (sq_nonneg _))

private lemma p10_link {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsIsoLink (Muon.DetEquiv.rW (Muon.emaW β)) := by
  obtain ⟨_, hd, hmono, _⟩ := lem_app_iso_weights_i hβ0.le hβ1
  refine ⟨fun q hq => (hd q hq).1.continuousWithinAt, (hmono hβ0).1, ?_⟩
  unfold Muon.DetEquiv.rW; simp

private lemma p10_delta_le_one {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {z y : ℝ}
    (hz : 0 < z) (hzy : z < y) (hry : Muon.DetEquiv.rW (Muon.emaW β) y < γ) :
    isoDeltaHat β γ y z ≤ 1 := by
  have hFw := p10_Fw_anti hβ0 hβ1 hz.le hzy.le
  have hy0 : 0 < y := lt_trans hz hzy
  have hmono : Muon.DetEquiv.rW (Muon.emaW β) z ≤ Muon.DetEquiv.rW (Muon.emaW β) y :=
    (p10_link hβ0 hβ1).2.1.monotoneOn (mem_Ici.2 hz.le) (mem_Ici.2 hy0.le) hzy.le
  have hrz : Muon.DetEquiv.rW (Muon.emaW β) z = z * Muon.DetEquiv.Fw (Muon.emaW β) z := rfl
  have hry' : Muon.DetEquiv.rW (Muon.emaW β) y = y * Muon.DetEquiv.Fw (Muon.emaW β) y := rfl
  unfold isoDeltaHat isoXkern isoZkern
  rw [if_neg hzy.ne', if_neg hzy.ne']
  set r := Muon.DetEquiv.rW (Muon.emaW β) with hr
  have hyz : 0 < y - z := by linarith
  have hX : (z * r y - y * r z) / (z - y) = (y * r z - z * r y) / (y - z) := by
    rw [← neg_div_neg_eq]; congr 1 <;> ring
  rw [hX]
  have hnum : 0 ≤ y * r z - z * r y := by
    rw [hrz, hry']
    have := mul_nonneg (mul_pos hy0 hz).le (sub_nonneg.2 hFw)
    nlinarith [this]
  have hX0 : 0 ≤ (y * r z - z * r y) / (y - z) := div_nonneg hnum hyz.le
  have hX1 : (y * r z - z * r y) / (y - z) ≤ r z := by
    rw [div_le_iff₀ hyz]
    nlinarith [mul_le_mul_of_nonneg_left hmono hz.le]
  have ha0 : 0 ≤ (y * r z - z * r y) / (y - z) / γ := div_nonneg hX0 hγ.le
  have ha1 : (y * r z - z * r y) / (y - z) / γ ≤ 1 := by
    rw [div_le_one hγ]; linarith
  have hZ : 0 ≤ Real.sqrt (y * z) * (r y - r z) / (y - z) :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.2 hmono)) hyz.le
  have : (1 - (y * r z - z * r y) / (y - z) / γ) ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg (Real.sqrt (y * z) * (r y - r z) / (y - z) / γ)]

private lemma p10_Q_spec {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    0 < isoQpsi β γ ε ∧ Muon.DetEquiv.rW (Muon.emaW β) (isoQpsi β γ ε) = isoLagPsi β γ ε ∧
      isoLagPsi β γ ε ≤ γ ∧
      (0 < ε → ε * isoQpsi β γ ε = (γ - isoLagPsi β γ ε) ^ 2 ∧ isoLagPsi β γ ε < γ) := by
  have hlink := p10_link hβ0 hβ1
  rcases hε.eq_or_lt with h0 | hpos
  · subst h0
    have hbij := ((lem_app_iso_weights_i hβ0.le hβ1).2.2.1 hβ0).2
    obtain ⟨q, hq, hrq⟩ := hbij.2.2 (mem_Ici.2 hγ.le)
    have hex : ∃ q : ℝ, 0 ≤ q ∧ Muon.DetEquiv.rW (Muon.emaW β) q = γ := ⟨q, hq, hrq⟩
    have hspec := (dif_pos hex : isoQlevel β γ = hex.choose) ▸ hex.choose_spec
    have hQ : isoQpsi β γ 0 = isoQlevel β γ := by unfold isoQpsi; simp
    have hψ : isoLagPsi β γ 0 = γ := by unfold isoLagPsi; simp
    have hrQ : Muon.DetEquiv.rW (Muon.emaW β) (isoQlevel β γ) = γ := by
      unfold isoQlevel; rw [dif_pos hex]; exact hex.choose_spec.2
    have hQ0 : 0 ≤ isoQlevel β γ := by
      unfold isoQlevel; rw [dif_pos hex]; exact hex.choose_spec.1
    have hQpos : 0 < isoQlevel β γ := by
      rcases hQ0.eq_or_lt with h | h
      · exfalso
        rw [← h] at hrQ
        have : Muon.DetEquiv.rW (Muon.emaW β) 0 = 0 := hlink.2.2
        linarith
      · exact h
    refine ⟨?_, ?_, ?_, fun h => absurd h (lt_irrefl _)⟩
    · rw [hQ]; exact hQpos
    · rw [hQ, hψ]; exact hrQ
    · rw [hψ]
  · have hmem := ((lem_app_iso_comparison_i hlink hγ hγ).2.2.2.1 ε hpos)
    obtain ⟨hD, hG⟩ := hmem
    have hQ : isoQpsi β γ ε = qIso β γ γ ε := by unfold isoQpsi; rw [if_pos hpos]
    have hψ : isoLagPsi β γ ε = Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ ε) := by
      unfold isoLagPsi psiIso; rw [if_neg hpos.ne']
    have hD' : 0 ≤ qIso β γ γ ε ∧ Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ ε) < γ := by
      have := hD; unfold isoDr at this; simp only [mem_setOf_eq, min_self] at this
      exact this
    have hG' : ε * qIso β γ γ ε = (γ - Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ ε)) ^ 2 := by
      have := hG; unfold isoG at this; unfold qIso; nlinarith [this]
    have hQpos : 0 < qIso β γ γ ε := by
      rcases hD'.1.eq_or_lt with h | h
      · exfalso
        have := pow_pos (sub_pos.2 hD'.2) 2
        rw [← hG', ← h] at this; simp at this
      · exact h
    refine ⟨?_, ?_, ?_, fun _ => ?_⟩
    · rw [hQ]; exact hQpos
    · rw [hQ, hψ]
    · rw [hψ]; exact hD'.2.le
    · rw [hQ, hψ]; exact ⟨hG', hD'.2⟩

private lemma p10_u_ge {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {ε : ℝ} (hε : 0 ≤ ε)
    {y : ℝ} (hy : 0 < y) (hyQ : y < isoQpsi β γ ε) : 1 ≤ isoUlev β γ ε y := by
  rcases hε.eq_or_lt with h0 | hpos
  · subst h0
    unfold isoUlev
    simp
  · obtain ⟨hQ0, hrQ, -, hspec⟩ := p10_Q_spec hβ0 hβ1 hγ hε
    obtain ⟨hεQ, hψγ⟩ := hspec hpos
    have hlink := p10_link hβ0 hβ1
    have hry : Muon.DetEquiv.rW (Muon.emaW β) y < isoLagPsi β γ ε := by
      rw [← hrQ]; exact hlink.2.1 (mem_Ici.2 hy.le) (mem_Ici.2 hQ0.le) hyQ
    have hA : γ - isoLagPsi β γ ε < isoResid β γ y := by unfold isoResid; linarith
    have hA0 : 0 < γ - isoLagPsi β γ ε := by linarith
    have hA2 : (γ - isoLagPsi β γ ε) ^ 2 < isoResid β γ y ^ 2 :=
      pow_lt_pow_left₀ hA hA0.le (by norm_num)
    have hlt : ε * y < isoResid β γ y ^ 2 := by nlinarith
    have hRpos : 0 < isoResid β γ y ^ 2 := lt_of_le_of_lt (by positivity) hlt
    unfold isoUlev
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    · rw [sub_pos, div_lt_one hRpos]; exact hlt
    · have : 0 ≤ ε * y / isoResid β γ y ^ 2 := by positivity
      linarith
    · norm_num

private lemma p10_eslope_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {y : ℝ} (hy : 0 < y) :
    0 ≤ isoEslope β y := by
  unfold isoEslope
  exact ((lem_app_iso_count_ii hβ0 hβ1).1 y hy).1.le

private lemma p10_phi_lower {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {ε : ℝ}
    (hε : 0 ≤ ε) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {y z : ℝ}
    (hz : 1 ≤ (1 - β) ^ 2 * z) (hzy : z < y) (hy2 : y ≤ z * Real.exp 2)
    (hM : Muon.DetEquiv.rW (Muon.emaW β) z ≤ isoLagPsi β γ ε - (ℓ : ℝ) - isoCpp β) :
    isoEminus β * Real.exp (-3) / z ^ 2 *
        ((γ - Muon.DetEquiv.rW (Muon.emaW β) z - isoCpp β) *
          (γ - Muon.DetEquiv.rW (Muon.emaW β) z - (ℓ : ℝ) - isoCpp β)) ≤
      (if y < isoQpsi β γ ε ∧ z / β ^ (2 * ℓ) < isoQpsi β γ ε then (1 : ℝ) else 0) *
        (isoDivDiff β y z * isoWeightJ β γ y * isoUlev β γ ε y *
          (isoWeightJ β γ (z / β ^ (2 * ℓ)) * isoUlev β γ ε (z / β ^ (2 * ℓ))) /
          isoDeltaHat β γ y z) := by
  obtain ⟨hQ0, hrQ, hψγ, -⟩ := p10_Q_spec hβ0 hβ1 hγ hε
  have hlink := p10_link hβ0 hβ1
  have hz0 : 0 < z := p10_pos_of_one_le hβ1 hz
  have hy0 : 0 < y := lt_trans hz0 hzy
  have hpow : 0 < β ^ (2 * ℓ) := pow_pos hβ0 _
  have hp1 : β ^ (2 * ℓ) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hz'0 : 0 < z / β ^ (2 * ℓ) := by positivity
  set r := Muon.DetEquiv.rW (Muon.emaW β) with hr
  set Q := isoQpsi β γ ε with hQ
  set ψ := isoLagPsi β γ ε with hψ
  set z' := z / β ^ (2 * ℓ) with hz'
  have hcy := p10_count_y hβ0 hβ1 hz hzy.le hy2
  have hcz := p10_count_z hβ0 hβ1 hz ℓ
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have hyQ : y < Q := by
    by_contra hcon
    push_neg at hcon
    have := hlink.2.1.monotoneOn (mem_Ici.2 hQ0.le) (mem_Ici.2 hy0.le) hcon
    simp only [hr] at hrQ this hcy hM
    linarith
  have hz'Q : z' < Q := by
    by_contra hcon
    push_neg at hcon
    have := hlink.2.1.monotoneOn (mem_Ici.2 hQ0.le) (mem_Ici.2 hz'0.le) hcon
    simp only [hr] at hrQ this hcz hM
    linarith
  rw [if_pos ⟨hyQ, hz'Q⟩, one_mul]
  have hryψ : r y < ψ := by
    rw [← hrQ]; exact hlink.2.1 (mem_Ici.2 hy0.le) (mem_Ici.2 hQ0.le) hyQ
  have hrz'ψ : r z' < ψ := by
    rw [← hrQ]; exact hlink.2.1 (mem_Ici.2 hz'0.le) (mem_Ici.2 hQ0.le) hz'Q
  have ha2 : 0 ≤ γ - r z - (ℓ : ℝ) - isoCpp β := by linarith
  have ha1 : 0 ≤ γ - r z - isoCpp β := by linarith
  have hAy : γ - r z - isoCpp β ≤ isoResid β γ y := by unfold isoResid; simp only [hr] at hcy ⊢; linarith
  have hAz' : γ - r z - (ℓ : ℝ) - isoCpp β ≤ isoResid β γ z' := by
    unfold isoResid; simp only [hr] at hcz ⊢; linarith
  have hD := p10_D_lower hβ0 hβ1 hz hzy hy2
  have hEm : 0 ≤ isoEminus β := by
    have hΦ : 0 < isoPhiDeriv 1 := (lem_app_iso_gaussian_ii.2.1 1 one_pos).2.1
    unfold isoEminus; positivity
  have hDl : 0 ≤ isoEminus β * Real.exp (-3) / z ^ 2 := by positivity
  have hJy : isoResid β γ y ≤ isoWeightJ β γ y := by
    unfold isoWeightJ; linarith [p10_eslope_nonneg hβ0 hβ1 hy0]
  have hJz : isoResid β γ z' ≤ isoWeightJ β γ z' := by
    unfold isoWeightJ; linarith [p10_eslope_nonneg hβ0 hβ1 hz'0]
  have huy := p10_u_ge hβ0 hβ1 hγ hε hy0 hyQ
  have huz := p10_u_ge hβ0 hβ1 hγ hε hz'0 hz'Q
  have hP1 : γ - r z - isoCpp β ≤ isoWeightJ β γ y * isoUlev β γ ε y := by
    have := mul_le_mul_of_nonneg_left huy (le_trans ha1 (le_trans hAy hJy))
    linarith
  have hP2 : γ - r z - (ℓ : ℝ) - isoCpp β ≤ isoWeightJ β γ z' * isoUlev β γ ε z' := by
    have := mul_le_mul_of_nonneg_left huz (le_trans ha2 (le_trans hAz' hJz))
    linarith
  have hΔpos : 0 < isoDeltaHat β γ y z :=
    (prop_app_iso_vol_representation hβ0 hβ1 hγ hε hℓ).1 y z hy0 hz0 hyQ hz'Q
  have hΔ1 : isoDeltaHat β γ y z ≤ 1 :=
    p10_delta_le_one hβ0 hβ1 hγ hz0 hzy (lt_of_lt_of_le hryψ hψγ)
  have hD0 : 0 ≤ isoDivDiff β y z := le_trans hDl hD
  have hN : isoEminus β * Real.exp (-3) / z ^ 2 *
      ((γ - r z - isoCpp β) * (γ - r z - (ℓ : ℝ) - isoCpp β)) ≤
      isoDivDiff β y z * isoWeightJ β γ y * isoUlev β γ ε y *
        (isoWeightJ β γ z' * isoUlev β γ ε z') := by
    have h1 := mul_le_mul hD hP1 ha1 hD0
    have h2 := mul_le_mul h1 hP2 ha2 (mul_nonneg hD0 (le_trans ha1 hP1))
    calc _ = isoEminus β * Real.exp (-3) / z ^ 2 * (γ - r z - isoCpp β) *
          (γ - r z - (ℓ : ℝ) - isoCpp β) := by ring
      _ ≤ _ := by
        have : isoDivDiff β y z * (isoWeightJ β γ y * isoUlev β γ ε y) *
            (isoWeightJ β γ z' * isoUlev β γ ε z') =
            isoDivDiff β y z * isoWeightJ β γ y * isoUlev β γ ε y *
              (isoWeightJ β γ z' * isoUlev β γ ε z') := by ring
        rw [← this]; exact h2
  have hN0 : 0 ≤ isoDivDiff β y z * isoWeightJ β γ y * isoUlev β γ ε y *
        (isoWeightJ β γ z' * isoUlev β γ ε z') :=
    le_trans (mul_nonneg hDl (mul_nonneg ha1 ha2)) hN
  refine le_trans hN ?_
  rw [le_div_iff₀ hΔpos]
  exact mul_le_of_le_one_right hN0 hΔ1

private lemma p10_cov {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {z0 z1 : ℝ}
    (hz0 : 1 ≤ (1 - β) ^ 2 * z0) (hz01 : z0 ≤ z1) (F : ℝ → ℝ) (hFc : Continuous F)
    (hF0 : ∀ η, Muon.DetEquiv.rW (Muon.emaW β) z0 ≤ η → η ≤ Muon.DetEquiv.rW (Muon.emaW β) z1 →
      0 ≤ F η) {a : ℝ} (ha : Muon.DetEquiv.rW (Muon.emaW β) z0 ≤ a) :
    ∫ η in Ioc a (Muon.DetEquiv.rW (Muon.emaW β) z1), F η ≤
      isoEplus β * ∫ z in Icc z0 z1, F (Muon.DetEquiv.rW (Muon.emaW β) z) / z := by
  have hz00 : 0 < z0 := p10_pos_of_one_le hβ1 hz0
  have hlink := p10_link hβ0 hβ1
  set r := Muon.DetEquiv.rW (Muon.emaW β) with hr
  have hpos : ∀ x ∈ Icc z0 z1, 0 < x := fun x hx => lt_of_lt_of_le hz00 hx.1
  have hcont : ContinuousOn r (Icc z0 z1) := fun x hx =>
    (p10_hasDeriv hβ0 hβ1 (hpos x hx)).continuousAt.continuousWithinAt
  have hmono : ∀ x ∈ Icc z0 z1, r z0 ≤ r x ∧ r x ≤ r z1 := fun x hx =>
    ⟨hlink.2.1.monotoneOn (mem_Ici.2 hz00.le) (mem_Ici.2 (hpos x hx).le) hx.1,
     hlink.2.1.monotoneOn (mem_Ici.2 (hpos x hx).le) (mem_Ici.2 (hpos z1 ⟨hz01, le_rfl⟩).le) hx.2⟩
  have himg : r '' Icc z0 z1 = Icc (r z0) (r z1) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hmono x hx
    · exact intermediate_value_Icc hz01 hcont
  have hinj : InjOn r (Icc z0 z1) :=
    hlink.2.1.injOn.mono (fun x hx => mem_Ici.2 (hpos x hx).le)
  have hder : ∀ x ∈ Icc z0 z1, HasDerivWithinAt r (deriv r x) (Icc z0 z1) x := fun x hx =>
    (p10_hasDeriv hβ0 hβ1 (hpos x hx)).hasDerivWithinAt
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hder hinj F
  rw [himg] at key
  -- the target integrand is integrable
  have hGc : ContinuousOn (fun z => F (r z) / z) (Icc z0 z1) :=
    (hFc.comp_continuousOn hcont).div continuousOn_id (fun x hx => (hpos x hx).ne')
  have hGi : IntegrableOn (fun z => F (r z) / z) (Icc z0 z1) := hGc.integrableOn_Icc
  have hle : ∫ x in Icc z0 z1, |deriv r x| • F (r x) ≤
      ∫ x in Icc z0 z1, isoEplus β * (F (r x) / x) := by
    apply integral_mono_of_nonneg
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have hd := ((lem_app_iso_count_ii hβ0 hβ1).1 x (hpos x hx)).1
      have : 0 < deriv r x := by
        by_contra h; push_neg at h
        have := mul_nonpos_of_nonneg_of_nonpos (hpos x hx).le h
        linarith
      simp only [Pi.zero_apply, smul_eq_mul]
      exact mul_nonneg (abs_nonneg _) (hF0 _ (hmono x hx).1 (hmono x hx).2)
    · exact hGi.const_mul _
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have hd := (lem_app_iso_count_ii hβ0 hβ1).1 x (hpos x hx)
      have hd0 : 0 < deriv r x := by
        by_contra h; push_neg at h
        have := mul_nonpos_of_nonneg_of_nonpos (hpos x hx).le h
        linarith [hd.1]
      simp only [smul_eq_mul, abs_of_pos hd0]
      have hFx := hF0 _ (hmono x hx).1 (hmono x hx).2
      have : deriv r x ≤ isoEplus β / x := by
        rw [le_div_iff₀ (hpos x hx)]; linarith [hd.2, mul_comm x (deriv r x)]
      calc deriv r x * F (r x) ≤ isoEplus β / x * F (r x) := mul_le_mul_of_nonneg_right this hFx
        _ = isoEplus β * (F (r x) / x) := by ring
  rw [integral_const_mul] at hle
  have hsub : ∫ η in Ioc a (r z1), F η ≤ ∫ η in Icc (r z0) (r z1), F η := by
    apply setIntegral_mono_set (hFc.continuousOn.integrableOn_Icc)
    · exact (ae_restrict_iff' measurableSet_Icc).2
        (Filter.Eventually.of_forall fun η hη => hF0 η hη.1 hη.2)
    · exact Filter.Eventually.of_forall (fun η hη => ⟨le_trans ha hη.1.le, hη.2⟩)
  exact le_trans hsub (key ▸ hle)

private lemma p10_lag_nonneg {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {ϱ : ℝ}
    (hϱ : 0 ≤ ϱ) (ℓ : ℕ) : 0 ≤ lagCoeff β γ ϱ ℓ := by
  have hlink := p10_link hβ0 hβ1
  have hq : ∀ s : ℝ, 0 < s → 0 ≤ qIso β γ γ s := by
    intro s hs
    have hmem := ((lem_app_iso_comparison_i hlink hγ hγ).2.2.2.1 s hs).1
    exact hmem.1
  unfold lagCoeff
  refine mul_nonneg (by positivity) ?_
  refine setIntegral_nonneg measurableSet_Ioi (fun x hx => ?_)
  refine setIntegral_nonneg measurableSet_Ioi (fun y hy => ?_)
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  have hs : 0 < ϱ + x ^ 2 := by positivity
  have hs' : 0 < ϱ + y ^ 2 := by positivity
  obtain ⟨⟨hB0, -⟩, -, -, hD0, -⟩ := lem_app_iso_lag_i hβ0 hβ1 hγ hs hs' ℓ
  unfold lagKernel
  exact div_nonneg (mul_nonneg (mul_nonneg hB0 (hq _ hs)) (hq _ hs'))
    (mul_nonneg (by positivity) hD0.le)

private lemma p10_stepB {z0 z1 : ℝ} (Gt : ℝ → ℝ) (hGt : Measurable Gt)
    (hG0 : ∀ z ∈ Icc z0 z1, 0 ≤ Gt z) :
    ∫⁻ p in {p : ℝ × ℝ | p.2 ∈ Icc z0 z1 ∧ p.1 ∈ Ioc p.2 (p.2 * Real.exp 2)},
        ENNReal.ofReal (Gt p.2) =
      ∫⁻ z in Icc z0 z1, ENNReal.ofReal (Gt z * (z * (Real.exp 2 - 1))) := by
  set R : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 ∈ Icc z0 z1 ∧ p.1 ∈ Ioc p.2 (p.2 * Real.exp 2)} with hR
  have hRm : MeasurableSet R := by
    have : R = (Prod.snd ⁻¹' Icc z0 z1) ∩ {p : ℝ × ℝ | p.2 < p.1} ∩
        {p : ℝ × ℝ | p.1 ≤ p.2 * Real.exp 2} := by
      ext p; simp only [hR, mem_setOf_eq, mem_Ioc, mem_inter_iff, mem_preimage, and_assoc]
    rw [this]
    exact ((measurable_snd measurableSet_Icc).inter
      (measurableSet_lt measurable_snd measurable_fst)).inter
      (measurableSet_le measurable_fst (measurable_snd.mul_const _))
  set f : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (Gt p.2) with hf
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (hGt.comp measurable_snd)
  rw [← lintegral_indicator hRm, Measure.volume_eq_prod,
    lintegral_prod_symm _ (hfm.indicator hRm).aemeasurable]
  rw [← lintegral_indicator measurableSet_Icc]
  congr 1
  funext z
  by_cases hz : z ∈ Icc z0 z1
  · rw [indicator_of_mem hz]
    have : ∀ y : ℝ, R.indicator f (y, z) = (Ioc z (z * Real.exp 2)).indicator
        (fun _ => ENNReal.ofReal (Gt z)) y := by
      intro y
      by_cases hy : y ∈ Ioc z (z * Real.exp 2)
      · rw [indicator_of_mem hy, indicator_of_mem]
        exact ⟨hz, hy⟩
      · rw [indicator_of_notMem hy, indicator_of_notMem]
        exact fun h => hy h.2
    simp_rw [this]
    rw [lintegral_indicator measurableSet_Ioc, setLIntegral_const, Real.volume_Ioc,
      ← ENNReal.ofReal_mul (hG0 z hz)]
    congr 1; ring
  · rw [indicator_of_notMem hz]
    have : ∀ y : ℝ, R.indicator f (y, z) = 0 := by
      intro y
      rw [indicator_of_notMem]
      exact fun h => hz h.1
    simp_rw [this]
    simp

private lemma p10_main {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {ε : ℝ}
    (hε : 0 ≤ ε) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hlt : isoC' β < isoLagPsi β γ ε - (ℓ : ℝ) - isoCpp β) :
    isoKk β / γ ^ 3 * ∫ η in Ioc (isoC' β) (isoLagPsi β γ ε - (ℓ : ℝ) - isoCpp β),
        (γ - η - isoCpp β) * (γ - η - (ℓ : ℝ) - isoCpp β) ≤ lagCoeff β γ ε ℓ := by
  have hL0 := p10_lag_nonneg hβ0 hβ1 hγ hε ℓ
  have hlink := p10_link hβ0 hβ1
  obtain ⟨-, hrQ, hψγ, -⟩ := p10_Q_spec hβ0 hβ1 hγ hε
  obtain ⟨-, hrep⟩ := prop_app_iso_vol_representation hβ0 hβ1 hγ hε hℓ
  set r := Muon.DetEquiv.rW (Muon.emaW β) with hr
  set ψ := isoLagPsi β γ ε with hψ
  set M := ψ - (ℓ : ℝ) - isoCpp β with hM
  set F : ℝ → ℝ := fun η => (γ - η - isoCpp β) * (γ - η - (ℓ : ℝ) - isoCpp β) with hF
  have hFc : Continuous F := by simp only [hF]; fun_prop
  have hF0 : ∀ η, η ≤ M → 0 ≤ F η := by
    intro η hη
    have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    simp only [hF]
    exact mul_nonneg (by linarith) (by linarith)
  have hb : 0 < (1 - β) ^ 2 := by
    have : 0 < 1 - β := by linarith
    positivity
  set z0 : ℝ := 1 / (1 - β) ^ 2 with hz0def
  have hz0 : 1 ≤ (1 - β) ^ 2 * z0 := by
    rw [hz0def, mul_one_div_cancel hb.ne']
  have hz00 : 0 < z0 := p10_pos_of_one_le hβ1 hz0
  have hrz0 : r z0 ≤ isoC' β := (lem_app_iso_count_i hβ0 hβ1).2
  have hc'pos : 0 < isoC' β := by
    unfold isoC'
    have : 0 < 1 - β ^ 2 := by nlinarith
    positivity
  obtain ⟨z1, hz1, hrz1⟩ :=
    (((lem_app_iso_weights_i hβ0.le hβ1).2.2.1 hβ0).2).2.2 (mem_Ici.2 (hc'pos.trans hlt).le)
  have hz01 : z0 < z1 := by
    by_contra h
    push_neg at h
    have := hlink.2.1.monotoneOn (mem_Ici.2 hz1) (mem_Ici.2 hz00.le) h
    simp only [hr] at hrz1 this hrz0
    linarith
  have hmono : ∀ z ∈ Icc z0 z1, r z ≤ M := by
    intro z hz
    rw [← hrz1]
    exact hlink.2.1.monotoneOn (mem_Ici.2 (hz00.trans_le hz.1).le) (mem_Ici.2 hz1) hz.2
  -- measurable version of `r`
  set rt : ℝ → ℝ := fun z => r (max z 0) with hrt
  have hrtm : Measurable rt := by
    apply Monotone.measurable
    intro x y hxy
    exact hlink.2.1.monotoneOn (mem_Ici.2 (le_max_right x 0)) (mem_Ici.2 (le_max_right y 0))
      (max_le_max hxy le_rfl)
  have hrt_eq : ∀ z, 0 < z → rt z = r z := fun z hz => by simp [hrt, max_eq_left hz.le]
  set Gt : ℝ → ℝ := fun z => isoEminus β * Real.exp (-3) / z ^ 2 * F (rt z) with hGt
  have hGtm : Measurable Gt := by
    simp only [hGt]
    exact (measurable_const.div (measurable_id.pow_const 2)).mul (hFc.measurable.comp hrtm)
  have hEm : 0 ≤ isoEminus β := by
    have hΦ : 0 < isoPhiDeriv 1 := (lem_app_iso_gaussian_ii.2.1 1 one_pos).2.1
    unfold isoEminus; positivity
  have hGt0 : ∀ z ∈ Icc z0 z1, 0 ≤ Gt z := by
    intro z hz
    have hzp : 0 < z := hz00.trans_le hz.1
    simp only [hGt, hrt_eq z hzp]
    exact mul_nonneg (by positivity) (hF0 _ (hmono z hz))
  -- Step A
  set R : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 ∈ Icc z0 z1 ∧ p.1 ∈ Ioc p.2 (p.2 * Real.exp 2)} with hR
  have hRm : MeasurableSet R := by
    have : R = (Prod.snd ⁻¹' Icc z0 z1) ∩ {p : ℝ × ℝ | p.2 < p.1} ∩
        {p : ℝ × ℝ | p.1 ≤ p.2 * Real.exp 2} := by
      ext p; simp only [hR, mem_setOf_eq, mem_Ioc, mem_inter_iff, mem_preimage, and_assoc]
    rw [this]
    exact ((measurable_snd measurableSet_Icc).inter
      (measurableSet_lt measurable_snd measurable_fst)).inter
      (measurableSet_le measurable_fst (measurable_snd.mul_const _))
  have hRsub : R ⊆ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    intro p hp
    have h1 : 0 < p.2 := hz00.trans_le hp.1.1
    exact ⟨mem_Ioi.2 (lt_trans h1 hp.2.1), mem_Ioi.2 h1⟩
  have hA : ∫⁻ p in R, ENNReal.ofReal (Gt p.2) ≤
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal
          ((if p.1 < isoQpsi β γ ε ∧ p.2 / β ^ (2 * ℓ) < isoQpsi β γ ε then (1 : ℝ) else 0) *
            (isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 * isoUlev β γ ε p.1 *
              (isoWeightJ β γ (p.2 / β ^ (2 * ℓ)) * isoUlev β γ ε (p.2 / β ^ (2 * ℓ))) /
              isoDeltaHat β γ p.1 p.2)) := by
    refine le_trans ?_ (lintegral_mono_set hRsub)
    refine setLIntegral_mono' hRm (fun p hp => ENNReal.ofReal_le_ofReal ?_)
    have hzp : 0 < p.2 := hz00.trans_le hp.1.1
    have hz1' : 1 ≤ (1 - β) ^ 2 * p.2 := by
      have : (1 - β) ^ 2 * z0 ≤ (1 - β) ^ 2 * p.2 :=
        mul_le_mul_of_nonneg_left hp.1.1 (sq_nonneg _)
      linarith
    have := p10_phi_lower hβ0 hβ1 hγ hε hℓ hz1' hp.2.1 hp.2.2 (hmono p.2 hp.1)
    simpa [hGt, hrt_eq p.2 hzp, hF] using this
  rw [p10_stepB Gt hGtm hGt0] at hA
  -- Step C: real integral
  set κ : ℝ := isoEminus β * Real.exp (-3) * (Real.exp 2 - 1) with hκ
  have hcont : ContinuousOn (fun z => F (r z) / z) (Icc z0 z1) := by
    have hcr : ContinuousOn r (Icc z0 z1) := fun x hx =>
      (p10_hasDeriv hβ0 hβ1 (hz00.trans_le hx.1)).continuousAt.continuousWithinAt
    exact (hFc.comp_continuousOn hcr).div continuousOn_id
      (fun x hx => (hz00.trans_le hx.1).ne')
  have hI : IntegrableOn (fun z => F (r z) / z) (Icc z0 z1) := hcont.integrableOn_Icc
  have hcongr : ∫⁻ z in Icc z0 z1, ENNReal.ofReal (Gt z * (z * (Real.exp 2 - 1))) =
      ENNReal.ofReal (κ * ∫ z in Icc z0 z1, F (r z) / z) := by
    rw [← integral_const_mul]
    rw [ofReal_integral_eq_lintegral_ofReal (hI.const_mul κ)]
    · apply setLIntegral_congr_fun measurableSet_Icc
      intro z hz
      have hzp : 0 < z := hz00.trans_le hz.1
      simp only [hGt, hrt_eq z hzp, hκ]
      congr 1
      field_simp
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun z hz => ?_)
      have hzp : 0 < z := hz00.trans_le hz.1
      have hFz := hF0 _ (hmono z hz)
      have : 0 ≤ Real.exp 2 - 1 := by
        have := Real.add_one_le_exp (2 : ℝ); linarith
      simp only [Pi.zero_apply, hκ]
      positivity
  rw [hcongr] at hA
  -- change of variables
  have hcov := p10_cov hβ0 hβ1 hz0 hz01.le F hFc
    (fun η _ h2 => hF0 η (by rw [← hrz1]; exact h2)) hrz0
  rw [hrz1] at hcov
  have hEp : 0 < isoEplus β := by
    unfold isoEplus
    have h1 : 0 < 1 - β := by linarith
    have h2 : 0 < 1 - β ^ 2 := by nlinarith
    positivity
  have hKk := p10_isoKk_nonneg hβ0 hβ1
  have hc0 : 0 ≤ 1 / (Real.pi ^ 2 * γ ^ 3) := by positivity
  have hT : isoKk β / γ ^ 3 * ∫ η in Ioc (isoC' β) M, F η ≤
      1 / (Real.pi ^ 2 * γ ^ 3) * (κ * ∫ z in Icc z0 z1, F (r z) / z) := by
    calc isoKk β / γ ^ 3 * ∫ η in Ioc (isoC' β) M, F η
        ≤ isoKk β / γ ^ 3 * (isoEplus β * ∫ z in Icc z0 z1, F (r z) / z) :=
          mul_le_mul_of_nonneg_left hcov (div_nonneg hKk (by positivity))
      _ = 1 / (Real.pi ^ 2 * γ ^ 3) * (κ * ∫ z in Icc z0 z1, F (r z) / z) := by
          simp only [isoKk, hκ]
          field_simp
  have hmain : ENNReal.ofReal (isoKk β / γ ^ 3 * ∫ η in Ioc (isoC' β) M, F η) ≤
      ENNReal.ofReal (lagCoeff β γ ε ℓ) := by
    calc ENNReal.ofReal (isoKk β / γ ^ 3 * ∫ η in Ioc (isoC' β) M, F η)
        ≤ ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3) * (κ * ∫ z in Icc z0 z1, F (r z) / z)) :=
          ENNReal.ofReal_le_ofReal hT
      _ = ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3)) *
            ENNReal.ofReal (κ * ∫ z in Icc z0 z1, F (r z) / z) := ENNReal.ofReal_mul hc0
      _ ≤ _ := by rw [hrep]; exact mul_le_mul_right hA _
  exact (ENNReal.ofReal_le_ofReal_iff hL0).mp hmain

/-- `lem:app-iso-lag-lower`, snapshot `cr-2026-10-23`, `section.tex` l.2317–2327.

\begin{lemma}[Lag lower bound]\label{lem:app-iso-lag-lower}
Let $\bmom\in(0,1)$, $\Nin=\Nout=N$, $\gamma=N/B$, $\varepsilon\ge0$ and $\ell\ge1$.
Put $m_\varepsilon\defeq\psi(\varepsilon)$ for $\varepsilon>0$ and $m_0\defeq\gamma$. Then
\[
\overline C_{1,\ell}(\varepsilon)\ge\frac{\mathsf k_\bmom}{\gamma^3}\int_{\mathsf c'_\bmom}^{\,m_\varepsilon-\ell-\mathsf c''_\bmom}
\big(\gamma-\eta-\mathsf c''_\bmom\big)\big(\gamma-\eta-\ell-\mathsf c''_\bmom\big)\,\dif\eta,
\]
where the right side is zero if the range is empty. For $\varepsilon>0$ the right
side is at least
$\frac{\mathsf k_\bmom}{\gamma^3}(\gamma-m_\varepsilon)^2\big(m_\varepsilon-\ell-\mathsf c''_\bmom-\mathsf c'_\bmom\big)_+$.
\end{lemma}
-/
theorem lem_app_iso_lag_lower_i {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    {ε : ℝ} (hε : 0 ≤ ε) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    isoKk β / γ ^ 3 * ∫ η in Ioc (isoC' β) (isoLagPsi β γ ε - (ℓ : ℝ) - isoCpp β),
        (γ - η - isoCpp β) * (γ - η - (ℓ : ℝ) - isoCpp β)
      ≤ lagCoeff β γ ε ℓ := by
  rcases lt_or_ge (isoC' β) (isoLagPsi β γ ε - (ℓ : ℝ) - isoCpp β) with h | h
  · exact p10_main hβ0 hβ1 hγ hε hℓ h
  · rw [Set.Ioc_eq_empty (not_lt.mpr h)]
    simpa using p10_lag_nonneg hβ0 hβ1 hγ hε ℓ

theorem lem_app_iso_lag_lower_ii {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    {ε : ℝ} (hε : 0 < ε) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    isoKk β / γ ^ 3 * (γ - isoLagPsi β γ ε) ^ 2
        * max (isoLagPsi β γ ε - (ℓ : ℝ) - isoCpp β - isoC' β) 0
      ≤ isoKk β / γ ^ 3 * ∫ η in Ioc (isoC' β) (isoLagPsi β γ ε - (ℓ : ℝ) - isoCpp β),
        (γ - η - isoCpp β) * (γ - η - (ℓ : ℝ) - isoCpp β) := by
  have hK : 0 ≤ isoKk β / γ ^ 3 := div_nonneg (p10_isoKk_nonneg hβ0 hβ1) (by positivity)
  have hψ := p10_psi_le hβ0 hβ1 hγ hε
  set ψ := isoLagPsi β γ ε with hψdef
  set a := isoC' β
  set c := isoCpp β
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hK
  rcases le_or_gt (ψ - (ℓ : ℝ) - c) a with h | h
  · rw [Set.Ioc_eq_empty (not_lt.mpr h)]
    have : max (ψ - (ℓ : ℝ) - c - a) 0 = 0 := max_eq_right (by linarith)
    simp [this]
  · have hmax : max (ψ - (ℓ : ℝ) - c - a) 0 = ψ - (ℓ : ℝ) - c - a := max_eq_left (by linarith)
    rw [hmax]
    have hℓ' : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    have : ∫ η in Ioc a (ψ - (ℓ : ℝ) - c), (γ - ψ) ^ 2
        ≤ ∫ η in Ioc a (ψ - (ℓ : ℝ) - c), (γ - η - c) * (γ - η - (ℓ : ℝ) - c) := by
      apply MeasureTheory.setIntegral_mono_on
      · exact intervalIntegrable_const.1
      · exact (Continuous.integrableOn_Ioc (by fun_prop))
      · exact measurableSet_Ioc
      · intro η hη
        have h2 := hη.2
        have h3 : 0 ≤ γ - ψ := by linarith
        nlinarith [mul_nonneg h3 hℓ']
    refine le_trans (le_of_eq ?_) this
    rw [MeasureTheory.setIntegral_const]
    simp [Real.volume_real_Ioc_of_le h.le, mul_comm]

/-! ## Lag sum at zero ridge: private helpers (task P-F.10.P2) -/

/-- Private helper (task P-F.10.P2): the lag-summed shape `T(z) = ∑_{ℓ≥1} 1{z_ℓ<Q_γ} j(z_ℓ)`,
indexed by `ℓ+1`, `ℓ ≥ 0`. -/
private def pF2T (β γ z : ℝ) : ℝ :=
  ∑' ℓ : ℕ, if z / β ^ (2 * (ℓ + 1)) < isoQlevel β γ
    then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0

/-- Private helper (task P-F.10.P2): `Ψ(y,z) = 1{y<Q_γ, z_1<Q_γ} j(y) T(z)/(γ² Δ̂(y,z))`. -/
private def pF2Psi (β γ : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < isoQlevel β γ ∧ p.2 / β ^ (2 * 1) < isoQlevel β γ then
    isoWeightJ β γ p.1 * pF2T β γ p.2 / (γ ^ 2 * isoDeltaHat β γ p.1 p.2) else 0

private lemma pF2A_ex {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 ≤ m) :
    ∃ q : ℝ, 0 ≤ q ∧ Muon.DetEquiv.rW (Muon.emaW β) q = m := by
  have hbij := ((lem_app_iso_weights_i hβ0.le hβ1).2.2.1 hβ0).2
  obtain ⟨q, hq, e⟩ := hbij.2.2 (mem_Ici.2 hm)
  exact ⟨q, hq, e⟩

private lemma pF2A_spec0 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 ≤ m) :
    0 ≤ isoQlevel β m ∧ Muon.DetEquiv.rW (Muon.emaW β) (isoQlevel β m) = m := by
  have hex := pF2A_ex hβ0 hβ1 hm
  unfold isoQlevel
  rw [dif_pos hex]
  exact hex.choose_spec

private lemma pF2_Q_spec {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < isoQlevel β m ∧ Muon.DetEquiv.rW (Muon.emaW β) (isoQlevel β m) = m := by
  obtain ⟨h0, h1⟩ := pF2A_spec0 hβ0 hβ1 hm.le
  refine ⟨?_, h1⟩
  rcases h0.eq_or_lt with h | h
  · exfalso
    have hz : Muon.DetEquiv.rW (Muon.emaW β) 0 = 0 := (p10_link hβ0 hβ1).2.2
    rw [← h, hz] at h1
    linarith
  · exact h

private lemma pF2_lt_Q_iff {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m y : ℝ} (hm : 0 < m)
    (hy : 0 < y) :
    y < isoQlevel β m ↔ Muon.DetEquiv.rW (Muon.emaW β) y < m := by
  obtain ⟨hQ, hr⟩ := pF2_Q_spec hβ0 hβ1 hm
  have hs := (p10_link hβ0 hβ1).2.1
  constructor
  · intro h
    have := hs (mem_Ici.2 hy.le) (mem_Ici.2 hQ.le) h
    rwa [hr] at this
  · intro h
    by_contra hc
    push_neg at hc
    have := hs.monotoneOn (mem_Ici.2 hQ.le) (mem_Ici.2 hy.le) hc
    rw [hr] at this
    linarith

private lemma pF2_Q_mono {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : Monotone (isoQlevel β) := by
  have hs := (p10_link hβ0 hβ1).2.1
  have hz : Muon.DetEquiv.rW (Muon.emaW β) 0 = 0 := (p10_link hβ0 hβ1).2.2
  have hneg : ∀ m : ℝ, m < 0 → isoQlevel β m = 0 := by
    intro m hm
    have hex : ¬ ∃ q : ℝ, 0 ≤ q ∧ Muon.DetEquiv.rW (Muon.emaW β) q = m := by
      rintro ⟨q, hq, e⟩
      have := hs.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hq) hq
      rw [hz, e] at this
      linarith
    unfold isoQlevel
    rw [dif_neg hex]
  intro m m' hmm
  rcases lt_or_ge m 0 with h | h
  · rw [hneg m h]
    rcases lt_or_ge m' 0 with h2 | h2
    · rw [hneg m' h2]
    · exact (pF2A_spec0 hβ0 hβ1 h2).1
  · obtain ⟨h0, hr⟩ := pF2A_spec0 hβ0 hβ1 h
    obtain ⟨h0', hr'⟩ := pF2A_spec0 hβ0 hβ1 (h.trans hmm)
    by_contra hc
    push_neg at hc
    have := hs (mem_Ici.2 h0') (mem_Ici.2 h0) hc
    rw [hr, hr'] at this
    linarith

private lemma pF2_Q_meas {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : Measurable (isoQlevel β) :=
  (pF2_Q_mono hβ0 hβ1).measurable

private lemma pF2A_n (L : ℝ) :
    ∃ n : ℕ, (∀ ℓ : ℕ, ((ℓ : ℝ) + 1 < L ↔ ℓ < n)) ∧ (n : ℝ) ≤ max L 0 ∧
      (0 < L → (n : ℝ) < L ∧ L - 1 ≤ n) := by
  refine ⟨⌈L⌉₊ - 1, ?_, ?_, ?_⟩
  · intro ℓ
    have h1 : (ℓ : ℝ) + 1 < L ↔ ℓ + 1 < ⌈L⌉₊ := by
      rw [Nat.lt_ceil]; push_cast; rfl
    rw [h1]; omega
  · rcases le_or_gt L 0 with h | h
    · have : ⌈L⌉₊ = 0 := Nat.ceil_eq_zero.2 h
      simp [this]
    · have := Nat.ceil_lt_add_one h.le
      have h2 : (((⌈L⌉₊ - 1 : ℕ)) : ℝ) ≤ (⌈L⌉₊ : ℝ) - 1 := by
        have h0 : 0 < ⌈L⌉₊ := Nat.ceil_pos.2 h
        rw [Nat.cast_sub h0]; simp
      rw [max_eq_left h.le]; linarith
  · intro h
    have h1 := Nat.ceil_lt_add_one h.le
    have h2 := Nat.le_ceil L
    have hp : 0 < ⌈L⌉₊ := Nat.ceil_pos.2 h
    rw [Nat.cast_sub hp]; push_cast
    constructor <;> linarith

private lemma pF2A_sumrange (c : ℝ) (n : ℕ) :
    ∑ ℓ ∈ Finset.range n, (c - ((ℓ : ℝ) + 1)) = n * c - n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

private lemma pF2A_gsum (L e : ℝ) (he : 0 ≤ e) :
    Summable (fun ℓ : ℕ => if (ℓ : ℝ) + 1 < L then L - ((ℓ : ℝ) + 1) + 2 * e else 0) ∧
    (∀ ℓ : ℕ, 0 ≤ (if (ℓ : ℝ) + 1 < L then L - ((ℓ : ℝ) + 1) + 2 * e else 0)) ∧
    ∑' ℓ : ℕ, (if (ℓ : ℝ) + 1 < L then L - ((ℓ : ℝ) + 1) + 2 * e else 0) ≤
      (max L 0) ^ 2 / 2 + 2 * e * max L 0 := by
  obtain ⟨n, hn, hnM, hnL⟩ := pF2A_n L
  set g : ℕ → ℝ := fun ℓ => if (ℓ : ℝ) + 1 < L then L - ((ℓ : ℝ) + 1) + 2 * e else 0 with hg
  have hg0 : ∀ ℓ, 0 ≤ g ℓ := by
    intro ℓ
    simp only [hg]
    split_ifs with h
    · linarith
    · exact le_rfl
  have hz : ∀ ℓ ∉ Finset.range n, g ℓ = 0 := by
    intro ℓ hℓ
    simp only [hg]
    rw [if_neg]
    rw [hn]; simpa using hℓ
  have hs : HasSum g (∑ ℓ ∈ Finset.range n, g ℓ) := hasSum_sum_of_ne_finset_zero hz
  refine ⟨hs.summable, hg0, ?_⟩
  rw [hs.tsum_eq]
  have : ∑ ℓ ∈ Finset.range n, g ℓ = ∑ ℓ ∈ Finset.range n, ((L + 2 * e) - ((ℓ : ℝ) + 1)) := by
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    simp only [hg]
    rw [if_pos ((hn ℓ).2 (Finset.mem_range.1 hℓ))]; ring
  rw [this, pF2A_sumrange]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases le_or_gt L 0 with h | h
  · have : n = 0 := by
      have := (hnM.trans_eq (max_eq_right h))
      exact_mod_cast le_antisymm this hn0
    subst this
    rw [max_eq_right h]; simp
  · obtain ⟨h1, h2⟩ := hnL h
    rw [max_eq_left h.le] at *
    nlinarith [sq_nonneg (L - n), mul_nonneg he (sub_nonneg.2 h1.le)]

private lemma pF2A_term {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {z : ℝ}
    (hz : 0 < z) (ℓ : ℕ) :
    0 ≤ (if z / β ^ (2 * (ℓ + 1)) < isoQlevel β γ
        then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0) ∧
    (if z / β ^ (2 * (ℓ + 1)) < isoQlevel β γ
        then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0) ≤
      (if (ℓ : ℝ) + 1 < γ - isoN β z + isoC β
        then (γ - isoN β z + isoC β) - ((ℓ : ℝ) + 1) + 2 * isoEbar β else 0) := by
  have hE : 0 ≤ isoEbar β := le_trans zero_le_one (le_max_left _ _)
  split_ifs with h1 h2
  · have hzk : 0 < z / β ^ (2 * (ℓ + 1)) := div_pos hz (pow_pos hβ0 _)
    have hr := (pF2_lt_Q_iff hβ0 hβ1 hγ hzk).1 h1
    have he0 := p10_eslope_nonneg hβ0 hβ1 hzk
    have he1 := (lem_app_iso_slope hβ0 hβ1 _ hzk).1.trans (lem_app_iso_slope hβ0 hβ1 _ hzk).2
    have hsh := lem_app_iso_shifts_ii hβ0 hβ1 z hz (ℓ + 1)
    unfold isoWeightJ isoResid
    push_cast at hsh
    constructor <;> linarith
  · exfalso
    apply h2
    have hzk : 0 < z / β ^ (2 * (ℓ + 1)) := div_pos hz (pow_pos hβ0 _)
    have hr := (pF2_lt_Q_iff hβ0 hβ1 hγ hzk).1 h1
    have hsh := lem_app_iso_shifts_ii hβ0 hβ1 z hz (ℓ + 1)
    push_cast at hsh
    linarith
  · rename_i h2
    constructor
    · exact le_rfl
    · linarith [hE]
  · exact ⟨le_rfl, le_rfl⟩

private lemma pF2_T_upper {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {z : ℝ}
    (hz : 0 < z) :
    (Summable fun ℓ : ℕ => if z / β ^ (2 * (ℓ + 1)) < isoQlevel β γ
        then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0) ∧
    (∀ ℓ : ℕ, 0 ≤ (if z / β ^ (2 * (ℓ + 1)) < isoQlevel β γ
        then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0)) ∧
    pF2T β γ z ≤ (max (γ - isoN β z + isoC β) 0) ^ 2 / 2
      + 2 * isoEbar β * max (γ - isoN β z + isoC β) 0 := by
  have hE : 0 ≤ isoEbar β := le_trans zero_le_one (le_max_left _ _)
  obtain ⟨hgs, -, hgt⟩ := pF2A_gsum (γ - isoN β z + isoC β) (isoEbar β) hE
  have hterm := fun ℓ => pF2A_term hβ0 hβ1 hγ hz ℓ
  have hsum : Summable fun ℓ : ℕ => if z / β ^ (2 * (ℓ + 1)) < isoQlevel β γ
        then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0 :=
    Summable.of_nonneg_of_le (fun ℓ => (hterm ℓ).1) (fun ℓ => (hterm ℓ).2) hgs
  refine ⟨hsum, fun ℓ => (hterm ℓ).1, ?_⟩
  unfold pF2T
  exact (Summable.tsum_le_tsum (fun ℓ => (hterm ℓ).2) hsum hgs).trans hgt

private lemma pF2_T_lower {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {z : ℝ}
    (hz : 0 < z) :
    (max (isoResid β γ z - 1) 0) ^ 2 / 2 ≤ pF2T β γ z := by
  obtain ⟨hsum, hnn, -⟩ := pF2_T_upper hβ0 hβ1 hγ hz
  set A := isoResid β γ z with hA
  obtain ⟨n, hn, hnM, hnL⟩ := pF2A_n A
  rcases le_or_gt A 1 with h | h
  · rw [max_eq_right (by linarith)]
    have : 0 ≤ pF2T β γ z := tsum_nonneg hnn
    simpa using this
  · have hA0 : 0 < A := by linarith
    obtain ⟨h1, h2⟩ := hnL hA0
    have hle := Summable.sum_le_tsum (Finset.range n) (fun ℓ _ => hnn ℓ) hsum
    have hge : ∑ ℓ ∈ Finset.range n, (A - ((ℓ : ℝ) + 1)) ≤
        ∑ ℓ ∈ Finset.range n, (if z / β ^ (2 * (ℓ + 1)) < isoQlevel β γ
          then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      have hℓn := Finset.mem_range.1 hℓ
      have hk : (ℓ : ℝ) + 1 < A := (hn ℓ).2 hℓn
      have hzk : 0 < z / β ^ (2 * (ℓ + 1)) := div_pos hz (pow_pos hβ0 _)
      have hsh := (lem_app_iso_shifts_i hβ0 hβ1 z hz (ℓ + 1)).2.2
      push_cast at hsh
      have hr : Muon.DetEquiv.rW (Muon.emaW β) (z / β ^ (2 * (ℓ + 1))) < γ := by
        unfold isoResid at hA; rw [hA] at hk; linarith
      rw [if_pos ((pF2_lt_Q_iff hβ0 hβ1 hγ hzk).2 hr)]
      have he0 := p10_eslope_nonneg hβ0 hβ1 hzk
      unfold isoWeightJ isoResid
      unfold isoResid at hA
      linarith
    unfold pF2T
    rw [max_eq_left (by linarith)]
    refine le_trans ?_ (hge.trans hle)
    rw [pF2A_sumrange]
    nlinarith [mul_nonneg (sub_nonneg.2 h1.le) (sub_nonneg.2 (show (0:ℝ) ≤ 1 - (A - n) by linarith))]

private lemma pF2_alg_up (e Φ a E Jy Tz d : ℝ) (he : 1 ≤ e) (hΦ : 0 < Φ) (ha : Φ ≤ a)
    (hE : 0 ≤ E) (hJy0 : 0 ≤ Jy) (hJy : Jy ≤ a + 2 * e) (hT0 : 0 ≤ Tz)
    (hT : Tz ≤ (a + E) ^ 2 / 2 + 2 * e * (a + E)) (hd : a * max (a - e) (a / 2) ≤ d) :
    Jy * Tz / d ≤ a / 2 + (11 * e + 48 * e ^ 3 / Φ ^ 2) + (8 + 32 * e ^ 2 / Φ ^ 2) * E
      + (2 / Φ + 4 * e / Φ ^ 2) * E ^ 2 := by
  have ha0 : 0 < a := hΦ.trans_le ha
  have he0 : 0 < e := by linarith
  have hJT : Jy * Tz ≤ (a + 2 * e) * ((a + E) ^ 2 / 2 + 2 * e * (a + E)) :=
    mul_le_mul hJy hT hT0 (by linarith)
  have hmax1 : a / 2 ≤ max (a - e) (a / 2) := le_max_right _ _
  have hmax2 : a - e ≤ max (a - e) (a / 2) := le_max_left _ _
  have hd0 : 0 < d := lt_of_lt_of_le (mul_pos ha0 (by linarith [hmax1])) hd
  have hK1 : 0 ≤ 32 * e ^ 2 / Φ ^ 2 := by positivity
  have hK2 : 0 ≤ 4 * e / Φ ^ 2 := by positivity
  have hK0 : 0 ≤ 48 * e ^ 3 / Φ ^ 2 := by positivity
  rcases le_or_gt (2 * e) a with hc | hc
  · -- large a
    have hae : 0 < a - e := by linarith
    have hd1 : a * (a - e) ≤ d := le_trans (mul_le_mul_of_nonneg_left hmax2 ha0.le) hd
    have hK2a : 2 ≤ a * (2 / Φ + 4 * e / Φ ^ 2) := by
      have : 2 ≤ a * (2 / Φ) := by
        rw [mul_div_assoc', le_div_iff₀ hΦ]; nlinarith
      nlinarith [mul_nonneg ha0.le hK2]
    set F := a / 2 + (11 * e + 48 * e ^ 3 / Φ ^ 2) + (8 + 32 * e ^ 2 / Φ ^ 2) * E
      + (2 / Φ + 4 * e / Φ ^ 2) * E ^ 2 with hF
    have hP : a ^ 2 / 2 + 11 * e * a + 8 * E * a + 2 * E ^ 2 ≤ F * a := by
      have : 2 * E ^ 2 ≤ a * (2 / Φ + 4 * e / Φ ^ 2) * E ^ 2 :=
        mul_le_mul_of_nonneg_right hK2a (sq_nonneg E) |> fun h => by linarith
      rw [hF]
      nlinarith [mul_nonneg ha0.le hK0, mul_nonneg (mul_nonneg ha0.le hK1) hE]
    have hpoly : (a + 2 * e) * ((a + E) ^ 2 / 2 + 2 * e * (a + E)) ≤
        (a ^ 2 / 2 + 11 * e * a + 8 * E * a + 2 * E ^ 2) * (a - e) := by
      nlinarith [mul_nonneg (mul_nonneg he0.le ha0.le) (sub_nonneg.2 hc),
        mul_nonneg hE (sub_nonneg.2 hc), mul_nonneg (mul_nonneg hE hE) (sub_nonneg.2 hc),
        mul_nonneg (mul_nonneg hE ha0.le) (sub_nonneg.2 hc), mul_nonneg (mul_nonneg hE he0.le) ha0.le,
        mul_nonneg (mul_nonneg hE he0.le) he0.le, mul_nonneg (mul_nonneg hE hE) he0.le,
        mul_nonneg (mul_nonneg hE hE) ha0.le, mul_nonneg (mul_nonneg hE he0.le) (sub_nonneg.2 hc)]
    rw [div_le_iff₀ hd0]
    calc Jy * Tz ≤ _ := hJT
      _ ≤ _ := hpoly
      _ ≤ F * a * (a - e) := mul_le_mul_of_nonneg_right hP hae.le
      _ ≤ F * d := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hd1 (by rw [hF]; positivity)
  · -- small a
    have hd2 : Φ ^ 2 / 2 ≤ d := by
      have : Φ * (Φ / 2) ≤ a * (a / 2) := mul_le_mul ha (by linarith) (by positivity) ha0.le
      nlinarith [mul_le_mul_of_nonneg_left hmax1 ha0.le]
    have hT2 : Tz ≤ 6 * e ^ 2 + 4 * e * E + E ^ 2 / 2 := by
      nlinarith [mul_nonneg hE (sub_nonneg.2 hc.le), mul_nonneg ha0.le (sub_nonneg.2 hc.le)]
    have hJ2 : Jy ≤ 4 * e := by linarith
    have hJT2 : Jy * Tz ≤ 4 * e * (6 * e ^ 2 + 4 * e * E + E ^ 2 / 2) :=
      mul_le_mul hJ2 hT2 hT0 (by linarith)
    rw [div_le_iff₀ hd0]
    have hΦ2 : 0 < Φ ^ 2 := by positivity
    have key : 4 * e * (6 * e ^ 2 + 4 * e * E + E ^ 2 / 2) ≤
        (48 * e ^ 3 / Φ ^ 2 + 32 * e ^ 2 / Φ ^ 2 * E + 4 * e / Φ ^ 2 * E ^ 2) * (Φ ^ 2 / 2) := by
      have : (48 * e ^ 3 / Φ ^ 2 + 32 * e ^ 2 / Φ ^ 2 * E + 4 * e / Φ ^ 2 * E ^ 2) * (Φ ^ 2 / 2)
          = 24 * e ^ 3 + 16 * e ^ 2 * E + 2 * e * E ^ 2 := by field_simp; ring
      rw [this]; nlinarith
    have hF0 : 0 ≤ a / 2 + 11 * e := by positivity
    have : 48 * e ^ 3 / Φ ^ 2 + 32 * e ^ 2 / Φ ^ 2 * E + 4 * e / Φ ^ 2 * E ^ 2 ≤
        a / 2 + (11 * e + 48 * e ^ 3 / Φ ^ 2) + (8 + 32 * e ^ 2 / Φ ^ 2) * E
          + (2 / Φ + 4 * e / Φ ^ 2) * E ^ 2 := by
      have : 0 ≤ 8 * E := by positivity
      have : 0 ≤ 2 / Φ * E ^ 2 := by positivity
      nlinarith
    calc Jy * Tz ≤ _ := hJT2
      _ ≤ _ := key
      _ ≤ _ := mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hd2 (by positivity)

private lemma pF2_alg_low (x υ Ay Az1 Av1 : ℝ) (hυ : 0 ≤ υ) (hx : υ < x)
    (hAy : x - υ ≤ Ay) (hAz : x - υ ≤ Az1) (hAv0 : 0 < Av1) (hAv : Av1 ≤ x + υ) :
    (x - 5 * υ) / 2 ≤ Ay * Az1 ^ 2 / (2 * Av1 ^ 2) := by
  have h1 : 0 < x - υ := by linarith
  have h2 : (x - υ) ^ 3 ≤ Ay * Az1 ^ 2 := by
    have : (x - υ) ^ 2 ≤ Az1 ^ 2 := pow_le_pow_left₀ h1.le hAz 2
    calc (x - υ) ^ 3 = (x - υ) * (x - υ) ^ 2 := by ring
      _ ≤ Ay * Az1 ^ 2 := mul_le_mul hAy this (by positivity) (by linarith)
  have h3 : Av1 ^ 2 ≤ (x + υ) ^ 2 := pow_le_pow_left₀ hAv0.le hAv 2
  rw [le_div_iff₀ (by positivity)]
  have h4 : (x - 5 * υ) / 2 * (2 * (x + υ) ^ 2) ≤ (x - υ) ^ 3 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ x) (sq_nonneg υ), pow_nonneg hυ 3]
  have hx0 : 0 ≤ x - 5 * υ ∨ x - 5 * υ < 0 := le_or_gt _ _
  rcases hx0 with h | h
  · calc (x - 5 * υ) / 2 * (2 * Av1 ^ 2) ≤ (x - 5 * υ) / 2 * (2 * (x + υ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
      _ ≤ _ := h4.trans h2
  · have : 0 ≤ Ay * Az1 ^ 2 := h2.trans' (by positivity)
    nlinarith [sq_nonneg Av1]

private lemma pF2B_gamma_pos {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ) : 0 < γ := by
  have h : 0 < 1 - β ^ 2 := by nlinarith [sq_nonneg β]
  have : 0 < isoC' β := by unfold isoC'; positivity
  unfold isoGammaCirc at hγ
  linarith

private lemma pF2B_region {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z) (hyQ : y < isoQlevel β γ)
    (hzQ : z / β ^ (2 * 1) < isoQlevel β γ) :
    0 < isoResid β γ y ∧ isoPhi 1 < isoResid β γ z ∧ 0 < isoDeltaHat β γ y z ∧
      Muon.DetEquiv.rW (Muon.emaW β) y < γ := by
  have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
  have hz1 : 0 < z / β ^ (2 * 1) := by positivity
  have hry := (pF2_lt_Q_iff hβ0 hβ1 hγ0 hy).1 hyQ
  have hrz := (pF2_lt_Q_iff hβ0 hβ1 hγ0 hz1).1 hzQ
  refine ⟨by unfold isoResid; linarith, ?_, ?_, hry⟩
  · exact lem_app_iso_shifts_v hβ0 hβ1 γ z hz hγ (by simpa using hrz)
  · have hQ : isoQpsi β γ 0 = isoQlevel β γ := by unfold isoQpsi; simp
    exact (prop_app_iso_vol_representation hβ0 hβ1 hγ0 (le_refl (0 : ℝ)) (ℓ := 1) le_rfl).1
      y z hy hz (by rw [hQ]; exact hyQ) (by rw [hQ]; exact hzQ)

private lemma pF2B_T_nonneg {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) {z : ℝ}
    (hz : 0 < z) : 0 ≤ pF2T β γ z := by
  unfold pF2T
  exact tsum_nonneg (pF2_T_upper hβ0 hβ1 hγ hz).2.1

private lemma pF2B_J_bounds {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {y : ℝ} (hy : 0 < y) :
    isoResid β γ y ≤ isoWeightJ β γ y ∧ isoWeightJ β γ y ≤ isoResid β γ y + 2 * isoEbar β := by
  have h0 := p10_eslope_nonneg hβ0 hβ1 hy
  have h1 := ((lem_app_iso_slope hβ0 hβ1 y hy).1.trans (lem_app_iso_slope hβ0 hβ1 y hy).2)
  unfold isoWeightJ
  constructor <;> linarith

private lemma pF2_Psi_nonneg {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z) : 0 ≤ pF2Psi β γ (y, z) := by
  have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
  unfold pF2Psi
  split_ifs with h
  · obtain ⟨hA, -, hΔ, -⟩ := pF2B_region hβ0 hβ1 hγ hy hz h.1 h.2
    have hJ := (pF2B_J_bounds (γ := γ) hβ0 hβ1 hy).1
    exact div_nonneg (mul_nonneg (hA.le.trans hJ) (pF2B_T_nonneg hβ0 hβ1 hγ0 hz))
      (by positivity)
  · exact le_rfl

private lemma pF2_Psi_upper {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z) (hyQ : y < isoQlevel β γ)
    (hzQ : z / β ^ (2 * 1) < isoQlevel β γ) :
    pF2Psi β γ (y, z) ≤ isoAvee β γ y z / 2 + isoK0 β
      + isoK1 β * (isoCpl β + max 0 (-isoN β z)) + isoK2 β * (isoCpl β + max 0 (-isoN β z)) ^ 2 := by
  have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
  obtain ⟨hAy, hAz, hΔ, -⟩ := pF2B_region hβ0 hβ1 hγ hy hz hyQ hzQ
  have hΦ : 0 < isoPhi 1 := (lem_app_iso_gaussian_ii.2.2 1 one_pos).1
  have hAz0 : 0 < isoResid β γ z := hΦ.trans hAz
  obtain ⟨-, -, -, hd, -⟩ := lem_app_iso_kernel_bounds_v hβ0 hβ1 hγ0 hy hz hAy hAz0
  obtain ⟨hJ1, hJ2⟩ := pF2B_J_bounds (γ := γ) hβ0 hβ1 hy
  have hAv_y : isoResid β γ y ≤ isoAvee β γ y z := le_max_left _ _
  have hAv_z : isoResid β γ z ≤ isoAvee β γ y z := le_max_right _ _
  have hE : 0 ≤ isoCpl β + max 0 (-isoN β z) := by
    have h1 : 0 < isoC β := by
      unfold isoC
      have : 0 < 1 - β := by linarith
      positivity
    have h2 : 0 < isoC' β := by
      have h : 0 < 1 - β ^ 2 := by nlinarith [sq_nonneg β]
      unfold isoC'; positivity
    unfold isoCpl
    have := le_max_left 0 (-isoN β z)
    linarith
  obtain ⟨-, hT0', hT⟩ := pF2_T_upper hβ0 hβ1 hγ0 hz
  have hT0 := pF2B_T_nonneg hβ0 hβ1 hγ0 hz
  have hs3 := lem_app_iso_shifts_iii hβ0 hβ1 z hz
  have hL : γ - isoN β z + isoC β ≤ isoAvee β γ y z + (isoCpl β + max 0 (-isoN β z)) := by
    unfold isoResid at hAv_z
    unfold isoCpl
    linarith
  have hpos : 0 < isoAvee β γ y z + (isoCpl β + max 0 (-isoN β z)) := by
    have := hAy.trans_le hAv_y
    linarith
  have hmax : max (γ - isoN β z + isoC β) 0 ≤ isoAvee β γ y z + (isoCpl β + max 0 (-isoN β z)) :=
    max_le hL hpos.le
  have hm0 : 0 ≤ max (γ - isoN β z + isoC β) 0 := le_max_right _ _
  have hE1 : 0 ≤ isoEbar β := (zero_le_one.trans (le_max_left _ _))
  have hTb : pF2T β γ z ≤ (isoAvee β γ y z + (isoCpl β + max 0 (-isoN β z))) ^ 2 / 2
      + 2 * isoEbar β * (isoAvee β γ y z + (isoCpl β + max 0 (-isoN β z))) := by
    refine hT.trans ?_
    have h1 := pow_le_pow_left₀ hm0 hmax 2
    have h2 := mul_le_mul_of_nonneg_left hmax (by positivity : 0 ≤ 2 * isoEbar β)
    linarith
  have hkey := pF2_alg_up (isoEbar β) (isoPhi 1) (isoAvee β γ y z)
    (isoCpl β + max 0 (-isoN β z)) (isoWeightJ β γ y) (pF2T β γ z) (γ ^ 2 * isoDeltaHat β γ y z)
    (le_max_left _ _) hΦ (hAz.le.trans hAv_z) hE (hAy.le.trans hJ1) (by linarith) hT0 hTb hd
  unfold pF2Psi
  rw [if_pos ⟨hyQ, hzQ⟩]
  unfold isoK0 isoK1 isoK2
  linarith [hkey]

private lemma pF2_Psi_lower {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z) (hyQ : y < isoQlevel β γ)
    (hzQ : z / β ^ (2 * 1) < isoQlevel β γ) :
    isoResid β γ y * (max (isoResid β γ z - 1) 0) ^ 2 / (2 * (isoAvee β γ y z + isoEbar β) ^ 2)
      ≤ pF2Psi β γ (y, z) := by
  have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
  obtain ⟨hAy, hAz, hΔ, -⟩ := pF2B_region hβ0 hβ1 hγ hy hz hyQ hzQ
  have hΦ : 0 < isoPhi 1 := (lem_app_iso_gaussian_ii.2.2 1 one_pos).1
  have hAz0 : 0 < isoResid β γ z := hΦ.trans hAz
  obtain ⟨-, -, hm, hd, hu⟩ := lem_app_iso_kernel_bounds_v hβ0 hβ1 hγ0 hy hz hAy hAz0
  have hAv_y : isoResid β γ y ≤ isoAvee β γ y z := le_max_left _ _
  have hD2 : 0 < γ ^ 2 * isoDeltaHat β γ y z := by positivity
  have hJ := (pF2B_J_bounds (γ := γ) hβ0 hβ1 hy).1
  have hTl := pF2_T_lower hβ0 hβ1 hγ0 hz
  have hnum : isoResid β γ y * ((max (isoResid β γ z - 1) 0) ^ 2 / 2) ≤
      isoWeightJ β γ y * pF2T β γ z :=
    mul_le_mul hJ hTl (by positivity) (hAy.le.trans hJ)
  unfold pF2Psi
  rw [if_pos ⟨hyQ, hzQ⟩]
  have hE1 : 0 < isoEbar β := zero_lt_one.trans_le (le_max_left _ _)
  have hpos : 0 < (isoAvee β γ y z + isoEbar β) ^ 2 := by
    have := hAy.trans_le hAv_y
    positivity
  calc isoResid β γ y * (max (isoResid β γ z - 1) 0) ^ 2 / (2 * (isoAvee β γ y z + isoEbar β) ^ 2)
      = (isoResid β γ y * ((max (isoResid β γ z - 1) 0) ^ 2 / 2)) /
          (isoAvee β γ y z + isoEbar β) ^ 2 := by field_simp
    _ ≤ (isoResid β γ y * ((max (isoResid β γ z - 1) 0) ^ 2 / 2)) /
          (γ ^ 2 * isoDeltaHat β γ y z) :=
        div_le_div_of_nonneg_left (by positivity) hD2 hu
    _ ≤ _ := div_le_div_of_nonneg_right hnum hD2.le

private lemma pF2C_K_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 ≤ isoK0 β ∧ 0 ≤ isoK1 β ∧ 0 ≤ isoK2 β ∧ 0 ≤ isoCpl β ∧ 1 ≤ isoEbar β := by
  have hE : 1 ≤ isoEbar β := le_max_left _ _
  have hΦ : 0 < isoPhi 1 := (lem_app_iso_gaussian_ii.2.2 1 one_pos).1
  have h1 : 0 < 1 - β := by linarith
  have h2 : 0 < 1 - β ^ 2 := by nlinarith
  have hc : 0 ≤ isoC β := by unfold isoC; positivity
  have hc' : 0 ≤ isoC' β := by unfold isoC'; positivity
  refine ⟨?_, ?_, ?_, by unfold isoCpl; linarith, hE⟩
  · unfold isoK0
    have : 0 ≤ 48 * isoEbar β ^ 3 / isoPhi 1 ^ 2 := by
      apply div_nonneg _ (by positivity)
      have : 0 ≤ isoEbar β := by linarith
      positivity
    linarith
  · unfold isoK1
    have : 0 ≤ 32 * isoEbar β ^ 2 / isoPhi 1 ^ 2 := by positivity
    linarith
  · unfold isoK2
    have : 0 ≤ 4 * isoEbar β / isoPhi 1 ^ 2 := by
      apply div_nonneg _ (by positivity)
      linarith
    have : 0 ≤ 2 / isoPhi 1 := by positivity
    linarith

private lemma pF2C_core {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    {η y z τ : ℝ} (hη : 0 < η) (hy : 0 < y) (hz : 0 < z) (hτ : 0 ≤ τ)
    (hyA : |isoResid β γ y - (γ - η)| ≤ isoEbar β * τ)
    (hzA : |isoResid β γ z - (γ - η)| ≤ isoEbar β * τ) :
    (η < γ → pF2Psi β γ (y, z) ≤
      ((γ - η) / 2 + isoEbar β * τ / 2 + isoK0 β + isoK1 β * isoCpl β
          + 2 * isoK2 β * isoCpl β ^ 2)
        + (isoK1 β * max 0 (-isoN β z) + 2 * isoK2 β * (max 0 (-isoN β z)) ^ 2)) ∧
    (γ - η - 5 * (isoEbar β * (τ + 1))) / 2 ≤ pF2Psi β γ (y, z) := by
  obtain ⟨hK0, hK1, hK2, hcp, hE⟩ := pF2C_K_nonneg hβ0 hβ1
  have hC' : 0 < isoC' β := by
    have h2 : 0 < 1 - β ^ 2 := by nlinarith
    unfold isoC'; positivity
  have hγ0 : 0 < γ := by unfold isoGammaCirc at hγ; linarith
  have hnn := pF2_Psi_nonneg hβ0 hβ1 hγ hy hz
  have hm : 0 ≤ max 0 (-isoN β z) := le_max_left _ _
  refine ⟨fun hηγ => ?_, ?_⟩
  · have hx : 0 < γ - η := by linarith
    have hRHS : 0 ≤ ((γ - η) / 2 + isoEbar β * τ / 2 + isoK0 β + isoK1 β * isoCpl β
          + 2 * isoK2 β * isoCpl β ^ 2)
        + (isoK1 β * max 0 (-isoN β z) + 2 * isoK2 β * (max 0 (-isoN β z)) ^ 2) := by
      have := mul_nonneg hK1 hcp
      have := mul_nonneg hK2 (sq_nonneg (isoCpl β))
      have := mul_nonneg hK1 hm
      have := mul_nonneg hK2 (sq_nonneg (max 0 (-isoN β z)))
      have : 0 ≤ isoEbar β * τ := mul_nonneg (by linarith) hτ
      linarith
    by_cases hreg : y < isoQlevel β γ ∧ z / β ^ (2 * 1) < isoQlevel β γ
    · have hU := pF2_Psi_upper hβ0 hβ1 hγ hy hz hreg.1 hreg.2
      have hAv : isoAvee β γ y z ≤ (γ - η) + isoEbar β * τ := by
        unfold isoAvee
        refine max_le ?_ ?_
        · linarith [(abs_le.mp hyA).2]
        · linarith [(abs_le.mp hzA).2]
      set c := isoCpl β
      set m := max 0 (-isoN β z)
      have := mul_nonneg hK2 (sq_nonneg (c - m))
      nlinarith
    · unfold pF2Psi; rw [if_neg hreg]; exact hRHS
  · by_cases hx : isoEbar β * (τ + 1) < γ - η
    · set υ := isoEbar β * (τ + 1) with hυ
      have hυ0 : 0 ≤ υ := mul_nonneg (by linarith) (by linarith)
      have hυ' : isoEbar β * τ + 1 ≤ υ := by rw [hυ]; nlinarith
      have hAy : γ - η - υ ≤ isoResid β γ y := by linarith [(abs_le.mp hyA).1, mul_nonneg (show (0:ℝ) ≤ isoEbar β by linarith) hτ]
      have hAz : γ - η - υ ≤ isoResid β γ z - 1 := by linarith [(abs_le.mp hzA).1]
      have hAy0 : 0 < isoResid β γ y := by linarith
      have hr1 : 0 < isoResid β γ z - 1 := by linarith
      have hQ := pF2_Q_spec hβ0 hβ1 hγ0
      have hyQ : y < isoQlevel β γ := by
        rw [pF2_lt_Q_iff hβ0 hβ1 hγ0 hy]; unfold isoResid at hAy0; linarith
      have hz'0 : 0 < z / β ^ (2 * 1) := by positivity
      have hsh := (lem_app_iso_shifts_i hβ0 hβ1 z hz 1).2.2
      have hzQ : z / β ^ (2 * 1) < isoQlevel β γ := by
        rw [pF2_lt_Q_iff hβ0 hβ1 hγ0 hz'0]
        unfold isoResid at hr1
        push_cast at hsh
        linarith
      have hL := pF2_Psi_lower hβ0 hβ1 hγ hy hz hyQ hzQ
      have hAv : isoAvee β γ y z + isoEbar β ≤ (γ - η) + υ := by
        unfold isoAvee
        have : max (isoResid β γ y) (isoResid β γ z) ≤ (γ - η) + isoEbar β * τ :=
          max_le (by linarith [(abs_le.mp hyA).2]) (by linarith [(abs_le.mp hzA).2])
        rw [hυ]; nlinarith
      have hmx : max (isoResid β γ z - 1) 0 = isoResid β γ z - 1 := max_eq_left hr1.le
      have hAv0 : 0 < isoAvee β γ y z + isoEbar β := by
        have : isoResid β γ y ≤ isoAvee β γ y z := le_max_left _ _
        linarith
      have := pF2_alg_low (γ - η) υ (isoResid β γ y) (isoResid β γ z - 1)
        (isoAvee β γ y z + isoEbar β) hυ0 hx hAy hAz hAv0 hAv
      rw [hmx] at hL
      exact this.trans hL
    · have : (γ - η - 5 * (isoEbar β * (τ + 1))) / 2 ≤ 0 := by
        have : 0 ≤ isoEbar β * (τ + 1) := mul_nonneg (by linarith) (by linarith)
        linarith
      exact this.trans hnn

/-- Pointwise bounds at `Π(Q_η; b, a, c)`. -/
private lemma pF2_pair {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    {η : ℝ} (hη : 0 < η) (b : Bool) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    0 ≤ pF2Psi β γ (isoPairMap (isoQlevel β η) (b, a, c)) ∧
    (γ ≤ η → pF2Psi β γ (isoPairMap (isoQlevel β η) (b, a, c)) = 0) ∧
    (η < γ → pF2Psi β γ (isoPairMap (isoQlevel β η) (b, a, c)) ≤
      ((γ - η) / 2 + isoEbar β * (a + c) / 2 + isoK0 β + isoK1 β * isoCpl β
          + 2 * isoK2 β * isoCpl β ^ 2)
        + (isoK1 β * max 0 (-isoN β (isoPairMap (isoQlevel β η) (b, a, c)).2)
          + 2 * isoK2 β * (max 0 (-isoN β (isoPairMap (isoQlevel β η) (b, a, c)).2)) ^ 2)) ∧
    (γ - η - 5 * (isoEbar β * ((a + c) + 1))) / 2 ≤
      pF2Psi β γ (isoPairMap (isoQlevel β η) (b, a, c)) := by
  have hγ0 : 0 < γ := by
    unfold isoGammaCirc isoC' at hγ
    have h2 : 0 < 1 - β ^ 2 := by nlinarith
    have : 0 < 1 / (1 - β ^ 2) := by positivity
    linarith
  obtain ⟨hs, hrs⟩ := pF2_Q_spec hβ0 hβ1 hη
  have hQ := pF2_Q_spec hβ0 hβ1 hγ0
  have h := lem_app_iso_averaging_iii (γ := γ) hβ0 hβ1 (isoQlevel β η) hs b a c ha hc
  dsimp only at h
  have hsA : isoResid β γ (isoQlevel β η) = γ - η := by unfold isoResid; rw [hrs]
  obtain ⟨y, z, hp⟩ : ∃ y z : ℝ, isoPairMap (isoQlevel β η) (b, a, c) = (y, z) :=
    ⟨_, _, Prod.mk.eta.symm⟩
  rw [hp] at h ⊢
  simp only at h ⊢
  obtain ⟨-, -, hyA, hzA, -⟩ := h
  rw [hsA] at hyA hzA
  have hyz : 0 < y ∧ 0 < z ∧ (isoQlevel β η ≤ y ∨ isoQlevel β η ≤ z) := by
    cases b <;> simp only [isoPairMap, Bool.false_eq_true, ite_false, ite_true] at hp <;>
      simp only [Prod.mk.injEq] at hp <;> obtain ⟨rfl, rfl⟩ := hp
    · refine ⟨by positivity, by positivity, Or.inr ?_⟩
      have : 1 ≤ Real.exp a := Real.one_le_exp ha
      nlinarith
    · refine ⟨by positivity, by positivity, Or.inl ?_⟩
      have : 1 ≤ Real.exp a := Real.one_le_exp ha
      nlinarith
  obtain ⟨hy, hz, hge⟩ := hyz
  have hτ : 0 ≤ a + c := by linarith
  obtain ⟨hU, hL⟩ := pF2C_core hβ0 hβ1 hγ hη hy hz hτ hyA hzA
  refine ⟨pF2_Psi_nonneg hβ0 hβ1 hγ hy hz, fun hηγ => ?_, hU, hL⟩
  have hns : ¬ isoQlevel β η < isoQlevel β γ := by
    rw [pF2_lt_Q_iff hβ0 hβ1 hγ0 hs, hrs]; linarith
  have hfail : ¬ (y < isoQlevel β γ ∧ z / β ^ (2 * 1) < isoQlevel β γ) := by
    rintro ⟨h1, h2⟩
    have hzz : z ≤ z / β ^ (2 * 1) := by
      rw [le_div_iff₀ (by positivity)]
      have : β ^ (2 * 1) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
      nlinarith
    rcases hge with h | h
    · exact hns (lt_of_le_of_lt h h1)
    · exact hns (lt_of_le_of_lt (h.trans hzz) h2)
  unfold pF2Psi
  rw [if_neg hfail]

/-- Private helper (task P-F.10.P2, D1): `Z` kernel for a stand-in `R`. -/
private def pF2D_Z (R : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 = p.2 then p.1 * deriv R p.1 else Real.sqrt (p.1 * p.2) * (R p.1 - R p.2) / (p.1 - p.2)

/-- Private helper (task P-F.10.P2, D1): `X` kernel for a stand-in `R`. -/
private def pF2D_X (R : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 = p.2 then R p.1 - p.1 * deriv R p.1 else (p.2 * R p.1 - p.1 * R p.2) / (p.2 - p.1)

/-- Private helper (task P-F.10.P2, D1): `Δ̂` for a stand-in `R`. -/
private def pF2D_Δ (R : ℝ → ℝ) (γ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 - pF2D_X R p / γ) ^ 2 - (pF2D_Z R p / γ) ^ 2

/-- Private helper (task P-F.10.P2, D1): `j` for a stand-in `R`. -/
private def pF2D_J (R : ℝ → ℝ) (γ y : ℝ) : ℝ := (γ - R y) + 2 * (y * deriv R y)

/-- Private helper (task P-F.10.P2, D1): `T` for a stand-in `R`. -/
private def pF2D_T (R : ℝ → ℝ) (β γ Q z : ℝ) : ℝ :=
  ∑' ℓ : ℕ, if z / β ^ (2 * (ℓ + 1)) < Q then pF2D_J R γ (z / β ^ (2 * (ℓ + 1))) else 0

/-- Private helper (task P-F.10.P2, D1): `Ψ` for a stand-in `R`. -/
private def pF2D_Psi (R : ℝ → ℝ) (β γ Q : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < Q ∧ p.2 / β ^ (2 * 1) < Q then
    pF2D_J R γ p.1 * pF2D_T R β γ Q p.2 / (γ ^ 2 * pF2D_Δ R γ p) else 0

private lemma pF2D_Z_meas {R : ℝ → ℝ} (hR : Measurable R) : Measurable (pF2D_Z R) := by
  unfold pF2D_Z
  have hd := measurable_deriv R
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) ?_ ?_
  · exact measurable_fst.mul (hd.comp measurable_fst)
  · fun_prop

private lemma pF2D_X_meas {R : ℝ → ℝ} (hR : Measurable R) : Measurable (pF2D_X R) := by
  unfold pF2D_X
  have hd := measurable_deriv R
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) ?_ ?_
  · exact (hR.comp measurable_fst).sub (measurable_fst.mul (hd.comp measurable_fst))
  · fun_prop

private lemma pF2D_Δ_meas {R : ℝ → ℝ} (hR : Measurable R) (γ : ℝ) :
    Measurable (pF2D_Δ R γ) := by
  unfold pF2D_Δ
  have := pF2D_Z_meas hR
  have := pF2D_X_meas hR
  fun_prop

private lemma pF2D_J_meas {R : ℝ → ℝ} (hR : Measurable R) (γ : ℝ) :
    Measurable (pF2D_J R γ) := by
  unfold pF2D_J
  have hd := measurable_deriv R
  fun_prop

private lemma pF2D_T_meas {R : ℝ → ℝ} (hR : Measurable R) (β γ Q : ℝ) :
    Measurable (pF2D_T R β γ Q) := by
  unfold pF2D_T
  refine Measurable.tsum (fun ℓ => ?_)
  refine Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) ?_ measurable_const
  exact (pF2D_J_meas hR γ).comp (by fun_prop)

private lemma pF2D_Psi_meas {R : ℝ → ℝ} (hR : Measurable R) (β γ Q : ℝ) :
    Measurable (pF2D_Psi R β γ Q) := by
  unfold pF2D_Psi
  have h1 := pF2D_J_meas hR γ
  have h2 := pF2D_T_meas hR β γ Q
  have h3 := pF2D_Δ_meas hR γ
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_lt (measurable_snd.div_const _) measurable_const)
  · exact ((h1.comp measurable_fst).mul (h2.comp measurable_snd)).div
      (measurable_const.mul h3)

private lemma pF2D_deriv_eq {β : ℝ} {R : ℝ → ℝ}
    (hRe : ∀ q : ℝ, 0 ≤ q → R q = Muon.DetEquiv.rW (Muon.emaW β) q) {y : ℝ} (hy : 0 < y) :
    deriv R y = deriv (Muon.DetEquiv.rW (Muon.emaW β)) y := by
  have : R =ᶠ[nhds y] Muon.DetEquiv.rW (Muon.emaW β) := by
    filter_upwards [Ioi_mem_nhds hy] with q hq using hRe q (le_of_lt hq)
  exact this.deriv_eq

private lemma pF2D_J_eq {β γ : ℝ} {R : ℝ → ℝ}
    (hRe : ∀ q : ℝ, 0 ≤ q → R q = Muon.DetEquiv.rW (Muon.emaW β) q) {y : ℝ} (hy : 0 < y) :
    pF2D_J R γ y = isoWeightJ β γ y := by
  unfold pF2D_J isoWeightJ isoResid isoEslope
  rw [pF2D_deriv_eq hRe hy, hRe y hy.le]

private lemma pF2D_Δ_eq {β γ : ℝ} {R : ℝ → ℝ}
    (hRe : ∀ q : ℝ, 0 ≤ q → R q = Muon.DetEquiv.rW (Muon.emaW β) q) {y z : ℝ} (hy : 0 < y)
    (hz : 0 < z) : pF2D_Δ R γ (y, z) = isoDeltaHat β γ y z := by
  unfold pF2D_Δ pF2D_X pF2D_Z isoDeltaHat isoXkern isoZkern isoEslope
  simp only [pF2D_deriv_eq hRe hy, hRe y hy.le, hRe z hz.le]

private lemma pF2D_T_eq {β γ : ℝ} (hβ0 : 0 < β) {R : ℝ → ℝ}
    (hRe : ∀ q : ℝ, 0 ≤ q → R q = Muon.DetEquiv.rW (Muon.emaW β) q) {z : ℝ} (hz : 0 < z) :
    pF2D_T R β γ (isoQlevel β γ) z = pF2T β γ z := by
  unfold pF2D_T pF2T
  refine tsum_congr (fun ℓ => ?_)
  have : 0 < z / β ^ (2 * (ℓ + 1)) := by positivity
  rw [pF2D_J_eq hRe this]

private lemma pF2_meas {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ) :
    ∃ Φ : ℝ × ℝ → ℝ, Measurable Φ ∧ (∀ p, 0 ≤ Φ p) ∧
      ∀ y z : ℝ, 0 < y → 0 < z → Φ (y, z) = pF2Psi β γ (y, z) := by
  have hlink : IsIsoLink (Muon.DetEquiv.rW (Muon.emaW β)) := by
    obtain ⟨_, hd, hmono, _⟩ := lem_app_iso_weights_i hβ0.le hβ1
    refine ⟨fun q hq => (hd q hq).1.continuousWithinAt, (hmono hβ0).1, ?_⟩
    unfold Muon.DetEquiv.rW; simp
  set R : ℝ → ℝ := fun q => Muon.DetEquiv.rW (Muon.emaW β) (max q 0) with hRdef
  have hRc : Continuous R :=
    ContinuousOn.comp_continuous hlink.1 (continuous_id.max continuous_const)
      (fun q => le_max_right q 0)
  have hRm : Measurable R := hRc.measurable
  have hRe : ∀ q : ℝ, 0 ≤ q → R q = Muon.DetEquiv.rW (Muon.emaW β) q := fun q hq => by
    simp only [hRdef, max_eq_left hq]
  refine ⟨fun p => max (pF2D_Psi R β γ (isoQlevel β γ) p) 0,
    (pF2D_Psi_meas hRm β γ _).max measurable_const, fun p => le_max_right _ _, ?_⟩
  intro y z hy hz
  have heq : pF2D_Psi R β γ (isoQlevel β γ) (y, z) = pF2Psi β γ (y, z) := by
    unfold pF2D_Psi pF2Psi
    simp only
    have hz1 : 0 < z / β ^ (2 * 1) := by positivity
    rw [pF2D_J_eq hRe hy, pF2D_T_eq hβ0 hRe hz, pF2D_Δ_eq hRe hy hz]
  show max (pF2D_Psi R β γ (isoQlevel β γ) (y, z)) 0 = _
  rw [heq]
  exact max_eq_left (pF2_Psi_nonneg hβ0 hβ1 hγ hy hz)

private lemma pF2E_D_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {y z : ℝ} (hy : 0 < y)
    (hz : 0 < z) : 0 ≤ isoDivDiff β y z := by
  have hlink := p10_link hβ0 hβ1
  unfold isoDivDiff
  split_ifs with h
  · subst h
    have hd := ((lem_app_iso_count_ii hβ0 hβ1).1 y hy).1
    have : 0 ≤ deriv (Muon.DetEquiv.rW (Muon.emaW β)) y := by
      by_contra hn
      push_neg at hn
      have := mul_neg_of_pos_of_neg hy hn
      linarith
    exact div_nonneg this (Real.sqrt_nonneg _)
  · have hs : 0 < Real.sqrt (y * z) := Real.sqrt_pos.mpr (mul_pos hy hz)
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have := hlink.2.1.monotoneOn (mem_Ici.2 hy.le) (mem_Ici.2 hz.le) hlt.le
      refine div_nonneg_of_nonpos (by linarith) ?_
      nlinarith
    · have := hlink.2.1.monotoneOn (mem_Ici.2 hz.le) (mem_Ici.2 hy.le) hgt.le
      exact div_nonneg (by linarith) (by nlinarith)

private lemma pF2E_isoUlev_zero (β γ y : ℝ) : isoUlev β γ 0 y = 1 := by
  simp [isoUlev]

private lemma pF2E_standin {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (L : ℕ) :
    ∃ G : ℝ × ℝ → ℝ, Measurable G ∧ ∀ y z : ℝ, 0 < y → 0 < z →
      G (y, z) = (if y < isoQlevel β γ ∧ z / β ^ (2 * L) < isoQlevel β γ then (1 : ℝ) else 0) *
        (isoDivDiff β y z * isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * L))
          / isoDeltaHat β γ y z) := by
  have hlink := p10_link hβ0 hβ1
  obtain ⟨R, hRm, hRe⟩ : ∃ R : ℝ → ℝ, Measurable R ∧
      ∀ q : ℝ, 0 ≤ q → R q = Muon.DetEquiv.rW (Muon.emaW β) q := by
    refine ⟨fun q => Muon.DetEquiv.rW (Muon.emaW β) (max q 0), ?_, fun q hq => by
      simp [max_eq_left hq]⟩
    exact (ContinuousOn.comp_continuous hlink.1 (continuous_id.max continuous_const)
      (fun q => le_max_right q 0)).measurable
  have hder : ∀ y : ℝ, 0 < y → deriv R y = deriv (Muon.DetEquiv.rW (Muon.emaW β)) y := by
    intro y hy
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioi_mem_nhds hy] with q hq using hRe q (le_of_lt hq)
  have hDm : Measurable fun p : ℝ × ℝ => if p.1 = p.2 then deriv R p.1 / Real.sqrt (p.1 * p.1)
      else (R p.1 - R p.2) / ((p.1 - p.2) * Real.sqrt (p.1 * p.2)) := by
    refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) ?_ ?_
    · exact ((measurable_deriv R).comp measurable_fst).div
        ((measurable_fst.mul measurable_fst).sqrt)
    · exact ((hRm.comp measurable_fst).sub (hRm.comp measurable_snd)).div
        ((measurable_fst.sub measurable_snd).mul ((measurable_fst.mul measurable_snd).sqrt))
  have hZm : Measurable fun p : ℝ × ℝ => if p.1 = p.2 then p.1 * deriv R p.1
      else Real.sqrt (p.1 * p.2) * (R p.1 - R p.2) / (p.1 - p.2) := by
    refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) ?_ ?_
    · exact measurable_fst.mul ((measurable_deriv R).comp measurable_fst)
    · exact (((measurable_fst.mul measurable_snd).sqrt).mul
        ((hRm.comp measurable_fst).sub (hRm.comp measurable_snd))).div
        (measurable_fst.sub measurable_snd)
  have hXm : Measurable fun p : ℝ × ℝ => if p.1 = p.2 then R p.1 - p.1 * deriv R p.1
      else (p.2 * R p.1 - p.1 * R p.2) / (p.2 - p.1) := by
    refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) ?_ ?_
    · exact (hRm.comp measurable_fst).sub
        (measurable_fst.mul ((measurable_deriv R).comp measurable_fst))
    · exact ((measurable_snd.mul (hRm.comp measurable_fst)).sub
        (measurable_fst.mul (hRm.comp measurable_snd))).div (measurable_snd.sub measurable_fst)
  have hjm : Measurable fun y : ℝ => γ - R y + 2 * (y * deriv R y) :=
    (measurable_const.sub hRm).add (measurable_const.mul (measurable_id.mul (measurable_deriv R)))
  set Dt := fun p : ℝ × ℝ => if p.1 = p.2 then deriv R p.1 / Real.sqrt (p.1 * p.1)
      else (R p.1 - R p.2) / ((p.1 - p.2) * Real.sqrt (p.1 * p.2)) with hDt
  set Zt := fun p : ℝ × ℝ => if p.1 = p.2 then p.1 * deriv R p.1
      else Real.sqrt (p.1 * p.2) * (R p.1 - R p.2) / (p.1 - p.2) with hZt
  set Xt := fun p : ℝ × ℝ => if p.1 = p.2 then R p.1 - p.1 * deriv R p.1
      else (p.2 * R p.1 - p.1 * R p.2) / (p.2 - p.1) with hXt
  set jt := fun y : ℝ => γ - R y + 2 * (y * deriv R y) with hjt
  have hcond : MeasurableSet {p : ℝ × ℝ | p.1 < isoQlevel β γ ∧
      p.2 / β ^ (2 * L) < isoQlevel β γ} :=
    (measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_lt (measurable_snd.div_const _) measurable_const)
  refine ⟨fun p => (if p.1 < isoQlevel β γ ∧ p.2 / β ^ (2 * L) < isoQlevel β γ then (1 : ℝ) else 0)
      * (Dt p * jt p.1 * jt (p.2 / β ^ (2 * L)) /
        ((1 - Xt p / γ) ^ 2 - (Zt p / γ) ^ 2)), ?_, ?_⟩
  · refine (Measurable.ite hcond measurable_const measurable_const).mul ?_
    have hD : Measurable Dt := hDm
    have hZ : Measurable Zt := hZm
    have hX : Measurable Xt := hXm
    have hj : Measurable jt := hjm
    refine ((hD.mul (hj.comp measurable_fst)).mul (hj.comp (measurable_snd.div_const _))).div ?_
    exact ((measurable_const.sub (hX.div_const _)).pow_const 2).sub ((hZ.div_const _).pow_const 2)
  · intro y z hy hz
    have hz' : 0 < z / β ^ (2 * L) := div_pos hz (pow_pos hβ0 _)
    beta_reduce
    congr 1
    have hj1 : jt y = isoWeightJ β γ y := by
      simp only [hjt, isoWeightJ, isoResid, isoEslope, hRe y hy.le, hder y hy]
    have hj2 : jt (z / β ^ (2 * L)) = isoWeightJ β γ (z / β ^ (2 * L)) := by
      simp only [hjt, isoWeightJ, isoResid, isoEslope, hRe _ hz'.le, hder _ hz']
    have hD' : Dt (y, z) = isoDivDiff β y z := by
      simp only [hDt, isoDivDiff, hRe y hy.le, hRe z hz.le, hder y hy]
    have hZ' : Zt (y, z) = isoZkern β y z := by
      simp only [hZt, isoZkern, isoEslope, hRe y hy.le, hRe z hz.le, hder y hy]
    have hX' : Xt (y, z) = isoXkern β y z := by
      simp only [hXt, isoXkern, isoEslope, hRe y hy.le, hRe z hz.le, hder y hy]
    show Dt (y, z) * jt y * jt (z / β ^ (2 * L)) /
        ((1 - Xt (y, z) / γ) ^ 2 - (Zt (y, z) / γ) ^ 2) = _
    rw [hD', hZ', hX', hj1, hj2]
    rfl

private lemma pF2E_ptwise {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    ∑' ℓ : ℕ, ENNReal.ofReal
        ((if y < isoQlevel β γ ∧ z / β ^ (2 * (ℓ + 1)) < isoQlevel β γ then (1 : ℝ) else 0) *
          (isoDivDiff β y z * isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * (ℓ + 1)))
            / isoDeltaHat β γ y z)) =
      ENNReal.ofReal (γ ^ 2 * (isoDivDiff β y z * pF2Psi β γ (y, z))) := by
  have hγ0 : 0 < γ := by
    have : 0 < isoC' β := by
      unfold isoC'
      have : 0 < 1 - β ^ 2 := by nlinarith
      positivity
    unfold isoGammaCirc at hγ
    linarith
  obtain ⟨hQpos, hrQ⟩ := pF2_Q_spec hβ0 hβ1 hγ0
  by_cases hreg : y < isoQlevel β γ ∧ z / β ^ (2 * 1) < isoQlevel β γ
  · have hΔ : 0 < isoDeltaHat β γ y z :=
      (prop_app_iso_vol_representation hβ0 hβ1 hγ0 (le_refl (0 : ℝ)) (le_refl 1)).1 y z hy hz
        (by simpa [isoQpsi] using hreg.1) (by simpa [isoQpsi] using hreg.2)
    have hD := pF2E_D_nonneg hβ0 hβ1 hy hz
    have hyr : Muon.DetEquiv.rW (Muon.emaW β) y < γ := by
      have := (pF2_lt_Q_iff hβ0 hβ1 hγ0 hy).1 hreg.1
      simpa using this
    have hjy : 0 ≤ isoWeightJ β γ y := by
      unfold isoWeightJ isoResid
      linarith [p10_eslope_nonneg hβ0 hβ1 hy]
    obtain ⟨hsum, hnn, -⟩ := pF2_T_upper hβ0 hβ1 hγ0 hz
    set C := isoDivDiff β y z * isoWeightJ β γ y / isoDeltaHat β γ y z with hC
    have hC0 : 0 ≤ C := div_nonneg (mul_nonneg hD hjy) hΔ.le
    have hterm : ∀ ℓ : ℕ, (if y < isoQlevel β γ ∧ z / β ^ (2 * (ℓ + 1)) < isoQlevel β γ
        then (1 : ℝ) else 0) * (isoDivDiff β y z * isoWeightJ β γ y *
          isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) / isoDeltaHat β γ y z) =
        C * (if z / β ^ (2 * (ℓ + 1)) < isoQlevel β γ
          then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0) := by
      intro ℓ
      by_cases h : z / β ^ (2 * (ℓ + 1)) < isoQlevel β γ
      · rw [if_pos ⟨hreg.1, h⟩, if_pos h, hC]; ring
      · rw [if_neg (fun hh => h hh.2), if_neg h]; ring
    simp_rw [hterm]
    have hnn' : ∀ ℓ : ℕ, 0 ≤ (if z / β ^ (2 * (ℓ + 1)) < isoQlevel β γ
          then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0) := hnn
    simp_rw [ENNReal.ofReal_mul hC0]
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg hnn' hsum, ← ENNReal.ofReal_mul hC0]
    congr 1
    have hT : pF2T β γ z = ∑' ℓ : ℕ, (if z / β ^ (2 * (ℓ + 1)) < isoQlevel β γ
          then isoWeightJ β γ (z / β ^ (2 * (ℓ + 1))) else 0) := rfl
    rw [← hT]
    unfold pF2Psi
    rw [if_pos hreg, hC]
    field_simp
  · have hzero : ∀ ℓ : ℕ, ¬ (y < isoQlevel β γ ∧ z / β ^ (2 * (ℓ + 1)) < isoQlevel β γ) := by
      intro ℓ ⟨h1, h2⟩
      apply hreg
      refine ⟨h1, lt_of_le_of_lt ?_ h2⟩
      have hp : β ^ (2 * (ℓ + 1)) ≤ β ^ (2 * 1) :=
        pow_le_pow_of_le_one hβ0.le hβ1.le (by omega)
      exact div_le_div_of_nonneg_left hz.le (pow_pos hβ0 _) hp
    have : ∀ ℓ : ℕ, ENNReal.ofReal
        ((if y < isoQlevel β γ ∧ z / β ^ (2 * (ℓ + 1)) < isoQlevel β γ then (1 : ℝ) else 0) *
          (isoDivDiff β y z * isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * (ℓ + 1)))
            / isoDeltaHat β γ y z)) = 0 := by
      intro ℓ
      rw [if_neg (hzero ℓ)]; simp
    simp_rw [this]
    unfold pF2Psi
    rw [if_neg hreg]
    simp

private lemma pF2_step1 {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ) :
    ∑' ℓ : ℕ, ENNReal.ofReal (lagCoeff β γ 0 (ℓ + 1)) =
      ENNReal.ofReal (1 / γ) * ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal (pF2Psi β γ (isoPairMap (isoQlevel β η) w)) ∂isoNuStar := by
  have hγ0 : 0 < γ := by
    have : 0 < isoC' β := by
      unfold isoC'
      have : 0 < 1 - β ^ 2 := by nlinarith
      positivity
    unfold isoGammaCirc at hγ
    linarith
  have hquad : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hQ0 : isoQpsi β γ 0 = isoQlevel β γ := by simp [isoQpsi]
  have hrep : ∀ ℓ : ℕ, ENNReal.ofReal (lagCoeff β γ 0 (ℓ + 1)) =
      ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3)) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), ENNReal.ofReal
          ((if p.1 < isoQlevel β γ ∧ p.2 / β ^ (2 * (ℓ + 1)) < isoQlevel β γ then (1 : ℝ) else 0) *
            (isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 *
              isoWeightJ β γ (p.2 / β ^ (2 * (ℓ + 1))) / isoDeltaHat β γ p.1 p.2)) := by
    intro ℓ
    have h := (prop_app_iso_vol_representation hβ0 hβ1 hγ0 (le_refl (0 : ℝ))
      (Nat.le_add_left 1 ℓ)).2
    simp only [hQ0, pF2E_isoUlev_zero, mul_one] at h
    exact h
  have hmeas : ∀ ℓ : ℕ, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
          ((if p.1 < isoQlevel β γ ∧ p.2 / β ^ (2 * (ℓ + 1)) < isoQlevel β γ then (1 : ℝ) else 0) *
            (isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 *
              isoWeightJ β γ (p.2 / β ^ (2 * (ℓ + 1))) / isoDeltaHat β γ p.1 p.2)))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))) := by
    intro ℓ
    obtain ⟨G, hGm, hG⟩ := pF2E_standin (β := β) (γ := γ) hβ0 hβ1 (ℓ + 1)
    refine (hGm.ennreal_ofReal.aemeasurable).congr ?_
    refine (ae_restrict_iff' hquad).2 (Filter.Eventually.of_forall fun p hp => ?_)
    have := hG p.1 p.2 hp.1 hp.2
    simp only [Prod.mk.eta] at this
    simp only [this]
  have hsum : ∑' ℓ : ℕ, ENNReal.ofReal (lagCoeff β γ 0 (ℓ + 1)) =
      ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3)) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal (γ ^ 2 * (isoDivDiff β p.1 p.2 * pF2Psi β γ p)) := by
    simp_rw [hrep]
    rw [ENNReal.tsum_mul_left, ← lintegral_tsum hmeas]
    congr 1
    refine setLIntegral_congr_fun hquad (fun p hp => ?_)
    exact pF2E_ptwise hβ0 hβ1 hγ hp.1 hp.2
  obtain ⟨Φ, hΦm, hΦ0, hΦe⟩ := pF2_meas hβ0 hβ1 hγ
  have havg := (lem_app_iso_averaging_i hβ0 hβ1).2 Φ hΦm hΦ0
  have hpos : ∀ (η : ℝ), 0 < η → ∀ w : Bool × ℝ × ℝ,
      0 < (isoPairMap (isoQlevel β η) w).1 ∧ 0 < (isoPairMap (isoQlevel β η) w).2 := by
    intro η hη w
    have hs := (pF2_Q_spec hβ0 hβ1 hη).1
    unfold isoPairMap
    split_ifs
    · exact ⟨mul_pos hs (Real.exp_pos _), mul_pos hs (Real.exp_pos _)⟩
    · exact ⟨mul_pos hs (Real.exp_pos _), mul_pos hs (Real.exp_pos _)⟩
  have hrhs : (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal (Φ (isoPairMap (isoQlevel β η) w)) ∂isoNuStar) =
      ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal (pF2Psi β γ (isoPairMap (isoQlevel β η) w)) ∂isoNuStar := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun η hη => ?_)
    refine lintegral_congr (fun w => ?_)
    obtain ⟨h1, h2⟩ := hpos η hη w
    have := hΦe _ _ h1 h2
    simp only [Prod.mk.eta] at this
    rw [this]
  have hlhs : (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal (isoDivDiff β p.1 p.2 * Φ p)) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal (isoDivDiff β p.1 p.2 * pF2Psi β γ p) := by
    refine setLIntegral_congr_fun hquad (fun p hp => ?_)
    have := hΦe p.1 p.2 hp.1 hp.2
    simp only [Prod.mk.eta] at this
    rw [this]
  rw [hlhs, hrhs] at havg
  rw [hsum]
  have hD0 : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), 0 ≤ γ ^ 2 := fun _ _ => by positivity
  have hsplit : (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal (γ ^ 2 * (isoDivDiff β p.1 p.2 * pF2Psi β γ p))) =
      ENNReal.ofReal (γ ^ 2) * ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal (isoDivDiff β p.1 p.2 * pF2Psi β γ p) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun p => ?_)
    exact ENNReal.ofReal_mul (by positivity)
  rw [hsplit, ← havg]
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

/-! ### Block F: integration against `dη ν⋆` -/

private lemma pF2F_nu_ae : ∀ᵐ w ∂isoNuStar, 0 < w.2.1 ∧ 0 < w.2.2 := by
  have hS : MeasurableSet {w : Bool × ℝ × ℝ | 0 < w.2.1 ∧ 0 < w.2.2} :=
    (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
      (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd))
  haveI : SFinite isoNuBase := by unfold isoNuBase; infer_instance
  unfold isoNuStar
  have h := (Measure.ae_prod_mem_iff_ae_ae_mem (μ := (Measure.count : Measure Bool))
    (ν := isoNuBase) hS).2
  refine h (Filter.Eventually.of_forall fun b => ?_)
  have h1 : ∀ᵐ p ∂((volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))),
      p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  have h2 := (withDensity_absolutelyContinuous
    ((volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))
    (fun p : ℝ × ℝ => ENNReal.ofReal (1 / (Real.pi ^ 2 * (2 * Real.sinh ((p.1 + p.2) / 2)))))).ae_le h1
  filter_upwards [h2] with p hp
  exact ⟨hp.1, hp.2⟩

private lemma pF2F_tau_meas : Measurable (fun w : Bool × ℝ × ℝ => w.2.1 + w.2.2) := by fun_prop

private lemma pF2F_prob {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : IsProbabilityMeasure isoNuStar :=
  (lem_app_iso_averaging_i hβ0 hβ1).1

private lemma pF2F_tau_int {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Integrable (fun w : Bool × ℝ × ℝ => w.2.1 + w.2.2) isoNuStar := by
  haveI := pF2F_prob hβ0 hβ1
  have h2 := (lem_app_iso_averaging_ii).2.1
  have hint : Integrable (fun w : Bool × ℝ × ℝ => (w.2.1 + w.2.2) ^ 2) isoNuStar := by
    by_contra hn
    rw [integral_undef hn] at h2
    have : (0 : ℝ) < 2 * Real.pi ^ 2 := by positivity
    linarith
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hint)
    pF2F_tau_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [abs_nonneg (w.2.1 + w.2.2), sq_abs (w.2.1 + w.2.2), sq_nonneg (|w.2.1 + w.2.2| - 1)]

private lemma pF2F_M1_eq : ∫ w, (w.2.1 + w.2.2) ∂isoNuStar = isoM1 :=
  (lem_app_iso_averaging_ii).1

private lemma pF2F_M1_nonneg' : 0 ≤ isoM1 := by
  rw [← pF2F_M1_eq]
  refine integral_nonneg_of_ae ?_
  filter_upwards [pF2F_nu_ae] with w hw
  exact (add_pos hw.1 hw.2).le

private lemma pF2F_M3_nonneg : 0 ≤ isoM3 := by
  have : ∫ w, (w.2.1 + w.2.2) ^ 3 ∂isoNuStar = isoM3 := (lem_app_iso_averaging_ii).2.2.1
  rw [← this]
  refine integral_nonneg_of_ae ?_
  filter_upwards [pF2F_nu_ae] with w hw
  exact pow_nonneg (add_pos hw.1 hw.2).le 3

private lemma pF2F_lint_tau {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∫⁻ w, ENNReal.ofReal (w.2.1 + w.2.2) ∂isoNuStar = ENNReal.ofReal isoM1 := by
  rw [← pF2F_M1_eq, ofReal_integral_eq_lintegral_ofReal (pF2F_tau_int hβ0 hβ1)]
  filter_upwards [pF2F_nu_ae] with w hw
  exact (add_pos hw.1 hw.2).le

private lemma pF2_M1_nonneg : 0 ≤ isoM1 := pF2F_M1_nonneg'

private lemma pF2_L_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 ≤ isoLbar1 β ∧ 0 ≤ isoLbar2 β := by
  have hM1 := pF2F_M1_nonneg'
  have hM3 := pF2F_M3_nonneg
  have hM2 : 0 ≤ isoM2 := by unfold isoM2; positivity
  have hE : 0 ≤ isoEbar β := le_trans zero_le_one (le_max_left _ _)
  have hL : 0 < Real.log (1 / β) := Real.log_pos (one_lt_one_div hβ0 hβ1)
  have hb : 0 < 1 - β ^ 2 := by nlinarith
  constructor
  · unfold isoLbar1; positivity
  · unfold isoLbar2; positivity

private lemma pF2F_pair_meas {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Measurable (fun x : ℝ × (Bool × ℝ × ℝ) => isoPairMap (isoQlevel β x.1) x.2) := by
  have hQ : Measurable (fun x : ℝ × (Bool × ℝ × ℝ) => isoQlevel β x.1) :=
    (pF2_Q_meas hβ0 hβ1).comp measurable_fst
  have hs : MeasurableSet {x : ℝ × (Bool × ℝ × ℝ) | x.2.1 = true} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton true)
  have ha : Measurable (fun x : ℝ × (Bool × ℝ × ℝ) => x.2.2.1) := by fun_prop
  have hc : Measurable (fun x : ℝ × (Bool × ℝ × ℝ) => x.2.2.2) := by fun_prop
  unfold isoPairMap
  refine Measurable.ite hs ?_ ?_
  · exact (hQ.mul ha.exp).prodMk (hQ.mul hc.neg.exp)
  · exact (hQ.mul hc.neg.exp).prodMk (hQ.mul ha.exp)

private lemma pF2F_N_meas {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Measurable (fun x : ℝ × (Bool × ℝ × ℝ) =>
      max 0 (-isoN β (isoPairMap (isoQlevel β x.1) x.2).2)) := by
  have h2 : Measurable (fun x : ℝ × (Bool × ℝ × ℝ) => (isoPairMap (isoQlevel β x.1) x.2).2) :=
    measurable_snd.comp (pF2F_pair_meas hβ0 hβ1)
  have : Measurable (isoN β) := by
    unfold isoN
    exact (Real.measurable_log.comp (measurable_const.mul measurable_id)).div_const _
  exact measurable_const.max (this.comp h2).neg

private lemma pF2F_eta_int {γ : ℝ} (hγ : 0 < γ) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ η in Ioi (0 : ℝ), (if η < γ then ENNReal.ofReal ((γ - η) / 2 + c) else 0) =
      ENNReal.ofReal (γ ^ 2 / 4 + γ * c) := by
  have h1 : (fun η : ℝ => if η < γ then ENNReal.ofReal ((γ - η) / 2 + c) else 0) =
      (Iio γ).indicator (fun η => ENNReal.ofReal ((γ - η) / 2 + c)) := by
    funext η; simp [Set.indicator]
  rw [h1, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    Set.inter_comm, Set.Ioi_inter_Iio]
  have hcont : Continuous (fun η : ℝ => (γ - η) / 2 + c) := by fun_prop
  have hnn : ∀ η ∈ Ioo (0 : ℝ) γ, 0 ≤ (γ - η) / 2 + c := fun η hη => by
    have := hη.2; positivity
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall hnn))]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hγ.le]
  have e : ∀ x : ℝ, (γ - x) / 2 + c = (γ / 2 + c) + (-1 / 2) * x := fun x => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_add (by simp)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have h3 : ∫ x in (0:ℝ)..γ, (-1 / 2 : ℝ) * x = (-1 / 2) * (γ ^ 2 / 2) := by
    rw [intervalIntegral.integral_const_mul]; simp [integral_id]
  rw [h3]
  simp
  ring

private lemma pF2F_eta_const {γ : ℝ} (hγ : 0 < γ) {K : ℝ} (hK : 0 ≤ K) :
    ∫⁻ η in Ioi (0 : ℝ), (if η < γ then ENNReal.ofReal K else 0) = ENNReal.ofReal (γ * K) := by
  have h1 : (fun η : ℝ => if η < γ then ENNReal.ofReal K else 0) =
      (Iio γ).indicator (fun _ => ENNReal.ofReal K) := by
    funext η; simp [Set.indicator]
  rw [h1, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    Set.inter_comm, Set.Ioi_inter_Iio, setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul hK,
    sub_zero, mul_comm]

private lemma pF2F_gpos {β γ : ℝ} (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ) (hβ0 : 0 < β) :
    0 < γ := by
  have h : 0 < isoC' β := by
    unfold isoC'
    have : 0 < 1 - β ^ 2 := by nlinarith
    positivity
  unfold isoGammaCirc at hγ
  linarith

private lemma pF2F_lint_up_tau {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u v : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v) :
    ∫⁻ w, ENNReal.ofReal (u + v * (w.2.1 + w.2.2)) ∂isoNuStar =
      ENNReal.ofReal (u + v * isoM1) := by
  haveI := pF2F_prob hβ0 hβ1
  have h1 : ∀ᵐ w ∂isoNuStar, ENNReal.ofReal (u + v * (w.2.1 + w.2.2)) =
      ENNReal.ofReal u + ENNReal.ofReal v * ENNReal.ofReal (w.2.1 + w.2.2) := by
    filter_upwards [pF2F_nu_ae] with w hw
    rw [ENNReal.ofReal_add hu (mul_nonneg hv (add_pos hw.1 hw.2).le),
      ENNReal.ofReal_mul hv]
  rw [lintegral_congr_ae h1, lintegral_add_left measurable_const, lintegral_const,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, pF2F_lint_tau hβ0 hβ1, measure_univ, mul_one,
    ← ENNReal.ofReal_mul hv, ← ENNReal.ofReal_add hu (mul_nonneg hv pF2F_M1_nonneg')]

private lemma pF2_I_lower {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ) :
    ENNReal.ofReal (γ ^ 2 / 4) ≤
      (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal (pF2Psi β γ (isoPairMap (isoQlevel β η) w)) ∂isoNuStar)
      + ENNReal.ofReal (γ * (5 / 2 * (isoEbar β * (isoM1 + 1)))) := by
  haveI := pF2F_prob hβ0 hβ1
  have hγ0 := pF2F_gpos hβ1 hγ hβ0
  have hE : 1 ≤ isoEbar β := le_max_left _ _
  have hM1 := pF2F_M1_nonneg'
  set K : ℝ := 5 / 2 * (isoEbar β * (isoM1 + 1)) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  -- pointwise
  have hpt : ∀ η : ℝ, 0 < η → ∀ᵐ w ∂isoNuStar,
      (if η < γ then ENNReal.ofReal ((γ - η) / 2 + 0) else 0) ≤
        (if η < γ then ENNReal.ofReal (5 / 2 * isoEbar β * (w.2.1 + w.2.2 + 1)) else 0)
          + ENNReal.ofReal (pF2Psi β γ (isoPairMap (isoQlevel β η) w)) := by
    intro η hη
    filter_upwards [pF2F_nu_ae] with w hw
    by_cases h : η < γ
    · simp only [if_pos h]
      obtain ⟨h0, -, -, h4⟩ := pF2_pair hβ0 hβ1 hγ hη w.1 hw.1.le hw.2.le
      set Ψ := pF2Psi β γ (isoPairMap (isoQlevel β η) (w.1, w.2.1, w.2.2)) with hΨ
      have hυ : 0 ≤ 5 / 2 * isoEbar β * (w.2.1 + w.2.2 + 1) := by
        have := add_pos hw.1 hw.2; positivity
      rw [← ENNReal.ofReal_add hυ h0]
      refine ENNReal.ofReal_le_ofReal ?_
      have : 5 / 2 * isoEbar β * (w.2.1 + w.2.2 + 1) = 5 * (isoEbar β * (w.2.1 + w.2.2 + 1)) / 2 := by
        ring
      rw [this]
      linarith
    · simp [h]
  have hconst : ∀ η : ℝ, 0 < η → ∫⁻ w, (if η < γ then ENNReal.ofReal (5 / 2 * isoEbar β * (w.2.1 + w.2.2 + 1)) else 0) ∂isoNuStar ≤
      (if η < γ then ENNReal.ofReal K else 0) := by
    intro η _
    by_cases h : η < γ
    · simp only [if_pos h]
      have := pF2F_lint_up_tau hβ0 hβ1 (u := 5 / 2 * isoEbar β) (v := 5 / 2 * isoEbar β)
        (by positivity) (by positivity)
      refine le_of_eq ?_
      have e : ∀ w : Bool × ℝ × ℝ, 5 / 2 * isoEbar β * (w.2.1 + w.2.2 + 1) =
          5 / 2 * isoEbar β + 5 / 2 * isoEbar β * (w.2.1 + w.2.2) := fun w => by ring
      simp_rw [e]
      rw [this, hK]
      congr 1; ring
    · simp [h]
  have hmeasA : Measurable (fun η : ℝ => if η < γ then ENNReal.ofReal K else 0) :=
    Measurable.ite measurableSet_Iio measurable_const measurable_const
  have hmeasH : ∀ η : ℝ, Measurable (fun w : Bool × ℝ × ℝ =>
      if η < γ then ENNReal.ofReal (5 / 2 * isoEbar β * (w.2.1 + w.2.2 + 1)) else 0) := by
    intro η
    by_cases h : η < γ
    · simp only [if_pos h]
      exact (by fun_prop : Measurable fun w : Bool × ℝ × ℝ =>
        5 / 2 * isoEbar β * (w.2.1 + w.2.2 + 1)).ennreal_ofReal
    · simp only [if_neg h]; exact measurable_const
  calc ENNReal.ofReal (γ ^ 2 / 4)
      = ∫⁻ η in Ioi (0 : ℝ), (if η < γ then ENNReal.ofReal ((γ - η) / 2 + 0) else 0) := by
        rw [pF2F_eta_int hγ0 le_rfl]; simp
    _ = ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, (if η < γ then ENNReal.ofReal ((γ - η) / 2 + 0) else 0)
          ∂isoNuStar := by
        congr 1; funext η; rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
          ((if η < γ then ENNReal.ofReal (5 / 2 * isoEbar β * (w.2.1 + w.2.2 + 1)) else 0)
            + ENNReal.ofReal (pF2Psi β γ (isoPairMap (isoQlevel β η) w))) ∂isoNuStar :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall fun η hη => lintegral_mono_ae (hpt η hη)))
    _ = ∫⁻ η in Ioi (0 : ℝ),
          (∫⁻ w, (if η < γ then ENNReal.ofReal (5 / 2 * isoEbar β * (w.2.1 + w.2.2 + 1)) else 0)
              ∂isoNuStar
            + ∫⁻ w, ENNReal.ofReal (pF2Psi β γ (isoPairMap (isoQlevel β η) w)) ∂isoNuStar) := by
        congr 1; funext η; rw [lintegral_add_left (hmeasH η)]
    _ ≤ ∫⁻ η in Ioi (0 : ℝ), ((if η < γ then ENNReal.ofReal K else 0)
            + ∫⁻ w, ENNReal.ofReal (pF2Psi β γ (isoPairMap (isoQlevel β η) w)) ∂isoNuStar) :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall fun η hη => add_le_add (hconst η hη) le_rfl))
    _ = ENNReal.ofReal (γ * K) + ∫⁻ η in Ioi (0 : ℝ),
          ∫⁻ w, ENNReal.ofReal (pF2Psi β γ (isoPairMap (isoQlevel β η) w)) ∂isoNuStar := by
        rw [lintegral_add_left hmeasA, pF2F_eta_const hγ0 hK0]
    _ = _ := add_comm _ _

private lemma pF2F_K_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 ≤ isoK0 β ∧ 0 ≤ isoK1 β ∧ 0 ≤ isoK2 β ∧ 0 ≤ isoCpl β := by
  have hE : 1 ≤ isoEbar β := le_max_left _ _
  have hΦ : 0 < isoPhi 1 := (lem_app_iso_gaussian_ii.2.2 1 one_pos).1
  have hC : 0 ≤ isoC β := by
    unfold isoC
    have : 0 < 1 - β := by linarith
    positivity
  have hC' : 0 < isoC' β := by
    unfold isoC'
    have : 0 < 1 - β ^ 2 := by nlinarith
    positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold isoK0; positivity
  · unfold isoK1; positivity
  · unfold isoK2; positivity
  · unfold isoCpl; linarith

private lemma pF2_I_upper {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ) :
    (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal (pF2Psi β γ (isoPairMap (isoQlevel β η) w)) ∂isoNuStar) ≤
      ENNReal.ofReal (γ ^ 2 / 4 + γ * (isoEbar β * isoM1 / 2 + isoK0 β + isoK1 β * isoCpl β
        + 2 * isoK2 β * isoCpl β ^ 2) + (isoK1 β * isoLbar1 β + 2 * isoK2 β * isoLbar2 β)) := by
  haveI := pF2F_prob hβ0 hβ1
  have hγ0 := pF2F_gpos hβ1 hγ hβ0
  have hE : 1 ≤ isoEbar β := le_max_left _ _
  have hM1 := pF2F_M1_nonneg'
  obtain ⟨hK0, hK1, hK2, hcp⟩ := pF2F_K_nonneg hβ0 hβ1
  obtain ⟨hL1, hL2⟩ := pF2_L_nonneg hβ0 hβ1
  set c0 : ℝ := isoK0 β + isoK1 β * isoCpl β + 2 * isoK2 β * isoCpl β ^ 2 with hc0def
  have hc0 : 0 ≤ c0 := by rw [hc0def]; positivity
  set N : ℝ × (Bool × ℝ × ℝ) → ℝ := fun x =>
    max 0 (-isoN β (isoPairMap (isoQlevel β x.1) x.2).2) with hNdef
  have hNm : Measurable N := pF2F_N_meas hβ0 hβ1
  have hN0 : ∀ x, 0 ≤ N x := fun x => le_max_left _ _
  -- pointwise
  have hpt : ∀ η : ℝ, 0 < η → ∀ᵐ w ∂isoNuStar,
      ENNReal.ofReal (pF2Psi β γ (isoPairMap (isoQlevel β η) w)) ≤
        (if η < γ then ENNReal.ofReal ((γ - η) / 2 + c0 + isoEbar β / 2 * (w.2.1 + w.2.2)) else 0)
          + (ENNReal.ofReal (isoK1 β) * ENNReal.ofReal (N (η, w))
            + ENNReal.ofReal (2 * isoK2 β) * ENNReal.ofReal (N (η, w) ^ 2)) := by
    intro η hη
    filter_upwards [pF2F_nu_ae] with w hw
    obtain ⟨h0, h1, h2, -⟩ := pF2_pair hβ0 hβ1 hγ hη w.1 hw.1.le hw.2.le
    by_cases h : η < γ
    · simp only [if_pos h]
      have hb := h2 h
      have hτ := add_pos hw.1 hw.2
      have hn := hN0 (η, w)
      have hB1 : 0 ≤ (γ - η) / 2 + c0 + isoEbar β / 2 * (w.2.1 + w.2.2) := by
        have : 0 < γ - η := by linarith
        positivity
      have hB2 : 0 ≤ isoK1 β * N (η, w) + 2 * isoK2 β * N (η, w) ^ 2 := by positivity
      rw [← ENNReal.ofReal_mul hK1, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * isoK2 β),
        ← ENNReal.ofReal_add (mul_nonneg hK1 hn) (by positivity), ← ENNReal.ofReal_add hB1 hB2]
      refine ENNReal.ofReal_le_ofReal (le_trans hb (le_of_eq ?_))
      simp only [hNdef, hc0def]
      ring
    · simp only [if_neg h]
      rw [h1 (not_lt.mp h)]
      simp
  have hmeasN : ∀ k : ℕ, Measurable (fun x : ℝ × (Bool × ℝ × ℝ) =>
      ENNReal.ofReal (N x ^ k)) := fun k => (hNm.pow_const k).ennreal_ofReal
  have hm1 : Measurable (fun η : ℝ => ∫⁻ w, ENNReal.ofReal (N (η, w) ^ 1) ∂isoNuStar) :=
    Measurable.lintegral_prod_right' (hmeasN 1)
  have hmA : Measurable (fun η : ℝ => if η < γ then ENNReal.ofReal
      ((γ - η) / 2 + (c0 + isoEbar β / 2 * isoM1)) else 0) :=
    Measurable.ite measurableSet_Iio (by fun_prop) measurable_const
  have hmB : ∀ η : ℝ, Measurable (fun w : Bool × ℝ × ℝ =>
      if η < γ then ENNReal.ofReal ((γ - η) / 2 + c0 + isoEbar β / 2 * (w.2.1 + w.2.2)) else 0) := by
    intro η
    by_cases h : η < γ
    · simp only [if_pos h]
      exact (by fun_prop : Measurable fun w : Bool × ℝ × ℝ =>
        (γ - η) / 2 + c0 + isoEbar β / 2 * (w.2.1 + w.2.2)).ennreal_ofReal
    · simp only [if_neg h]; exact measurable_const
  have hNw : ∀ (η : ℝ) (k : ℕ), Measurable (fun w : Bool × ℝ × ℝ => ENNReal.ofReal (N (η, w) ^ k)) :=
    fun η k => (hmeasN k).comp measurable_prodMk_left
  have hinA : ∀ η : ℝ, ∫⁻ w, (if η < γ then ENNReal.ofReal
      ((γ - η) / 2 + c0 + isoEbar β / 2 * (w.2.1 + w.2.2)) else 0) ∂isoNuStar =
      (if η < γ then ENNReal.ofReal ((γ - η) / 2 + (c0 + isoEbar β / 2 * isoM1)) else 0) := by
    intro η
    by_cases h : η < γ
    · simp only [if_pos h]
      have hu : 0 ≤ (γ - η) / 2 + c0 := by
        have : 0 < γ - η := by linarith
        positivity
      have := pF2F_lint_up_tau hβ0 hβ1 hu (v := isoEbar β / 2) (by positivity)
      have e : ∀ w : Bool × ℝ × ℝ, (γ - η) / 2 + c0 + isoEbar β / 2 * (w.2.1 + w.2.2) =
          ((γ - η) / 2 + c0) + isoEbar β / 2 * (w.2.1 + w.2.2) := fun w => rfl
      rw [this]; congr 1; ring
    · simp [h]
  have hinB : ∀ η : ℝ, ∫⁻ w, (ENNReal.ofReal (isoK1 β) * ENNReal.ofReal (N (η, w))
      + ENNReal.ofReal (2 * isoK2 β) * ENNReal.ofReal (N (η, w) ^ 2)) ∂isoNuStar =
      ENNReal.ofReal (isoK1 β) * ∫⁻ w, ENNReal.ofReal (N (η, w) ^ 1) ∂isoNuStar
      + ENNReal.ofReal (2 * isoK2 β) * ∫⁻ w, ENNReal.ofReal (N (η, w) ^ 2) ∂isoNuStar := by
    intro η
    have hm : Measurable (fun w : Bool × ℝ × ℝ => ENNReal.ofReal (isoK1 β) * ENNReal.ofReal (N (η, w))) := by
      have := (hNw η 1).const_mul (ENNReal.ofReal (isoK1 β))
      simpa using this
    rw [lintegral_add_left hm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    simp
  have hlow := lem_app_iso_low_levels_ii hβ0 hβ1
  calc (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal (pF2Psi β γ (isoPairMap (isoQlevel β η) w)) ∂isoNuStar)
      ≤ ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
          ((if η < γ then ENNReal.ofReal ((γ - η) / 2 + c0 + isoEbar β / 2 * (w.2.1 + w.2.2))
              else 0)
            + (ENNReal.ofReal (isoK1 β) * ENNReal.ofReal (N (η, w))
              + ENNReal.ofReal (2 * isoK2 β) * ENNReal.ofReal (N (η, w) ^ 2))) ∂isoNuStar :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall fun η hη => lintegral_mono_ae (hpt η hη)))
    _ = ∫⁻ η in Ioi (0 : ℝ),
          ((if η < γ then ENNReal.ofReal ((γ - η) / 2 + (c0 + isoEbar β / 2 * isoM1)) else 0)
            + (ENNReal.ofReal (isoK1 β) * ∫⁻ w, ENNReal.ofReal (N (η, w) ^ 1) ∂isoNuStar
              + ENNReal.ofReal (2 * isoK2 β) * ∫⁻ w, ENNReal.ofReal (N (η, w) ^ 2) ∂isoNuStar)) := by
        congr 1; funext η
        rw [lintegral_add_left (hmB η), hinA, hinB]
    _ = ENNReal.ofReal (γ ^ 2 / 4 + γ * (c0 + isoEbar β / 2 * isoM1)) +
          (ENNReal.ofReal (isoK1 β) * (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, ENNReal.ofReal (N (η, w) ^ 1) ∂isoNuStar)
            + ENNReal.ofReal (2 * isoK2 β) * (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, ENNReal.ofReal (N (η, w) ^ 2) ∂isoNuStar)) := by
        rw [lintegral_add_left hmA, pF2F_eta_int hγ0 (by positivity)]
        congr 1
        rw [lintegral_add_left (hm1.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (γ ^ 2 / 4 + γ * (c0 + isoEbar β / 2 * isoM1)) +
          (ENNReal.ofReal (isoK1 β) * ENNReal.ofReal (isoLbar1 β)
            + ENNReal.ofReal (2 * isoK2 β) * ENNReal.ofReal (isoLbar2 β)) := by
        have h1 : ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, ENNReal.ofReal (N (η, w) ^ 1) ∂isoNuStar ≤
            ENNReal.ofReal (isoLbar1 β) := by
          simp only [pow_one]; exact hlow.1
        exact add_le_add le_rfl (add_le_add (mul_le_mul' le_rfl h1) (mul_le_mul' le_rfl hlow.2))
    _ = _ := by
        rw [← ENNReal.ofReal_mul hK1, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * isoK2 β),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        simp only [hc0def]
        ring

/-- `thm:app-iso-small-volatility`, snapshot `cr-2026-10-23`, `section.tex` l.2220–2230. First display only (the second display is deferred to L-F.10b).

\begin{theorem}[Small-aspect integrated volatility]\label{thm:app-iso-small-volatility}
Let $\bmom\in(0,1)$, $\Nin=\Nout=N$ and $\gamma=N/B\le(1+\bmom^2)/96$. Then for every $\ell\ge1$
\[
\big|\overline C_{1,\ell}(0)-\Omega(\bmom^\ell)\big|\le\frac{96\gamma}{1+\bmom^2}\,\Omega(\bmom^\ell),
\]
and the zero-ridge volatility of \cref{def:app-iso-vol-zero} satisfies
\[
\Big|\frac{\mathfrak v_{\mathrm{iso},\bmom}}N-V_\bmom\Big|\le\frac{96\gamma}{1+\bmom^2}\,\big(V_\bmom-1\big),\qquad
\Big|\frac{\mathfrak v_{\mathrm{iso},\bmom}}{N\,V_\bmom}-1\Big|\le96\gamma .
\]
\end{theorem}
-/
private lemma p10_volOmega_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ volOmega z := by
  unfold volOmega
  have hpi : 0 < 4 / Real.pi ^ 2 := by positivity
  refine mul_nonneg hpi.le (tsum_nonneg fun n => ?_)
  exact mul_nonneg (sq_nonneg _) (pow_nonneg hz _)

private lemma p10_small_factor {β γ : ℝ} (hγ0 : 0 < γ)
    (hγ : γ ≤ (1 + β ^ 2) / 96) :
    0 ≤ 96 * γ / (1 + β ^ 2) ∧ 96 * γ / (1 + β ^ 2) ≤ 1 := by
  have hd : 0 < 1 + β ^ 2 := by positivity
  constructor
  · positivity
  · rw [div_le_one hd]
    nlinarith

private lemma p10_abs_of_sandwich {a b k : ℝ} (hb : 0 ≤ b) (hlo : (1 - k) * b ≤ a)
    (hhi : a ≤ (1 + k) * b) : |a - b| ≤ k * b := by
  rw [abs_le]
  constructor <;> nlinarith

private lemma p10_small_volatility_of_sandwich {β γ : ℝ} (hβ0 : 0 < β) {l : ℕ}
    (hlo : (1 - 96 * γ / (1 + β ^ 2)) * volOmega (β ^ l) ≤ lagCoeff β γ 0 l)
    (hhi : lagCoeff β γ 0 l ≤
      (1 + 96 * γ / (1 + β ^ 2)) * volOmega (β ^ l)) :
    |lagCoeff β γ 0 l - volOmega (β ^ l)| ≤
      96 * γ / (1 + β ^ 2) * volOmega (β ^ l) := by
  exact p10_abs_of_sandwich (p10_volOmega_nonneg (pow_nonneg hβ0.le l)) hlo hhi

private lemma p10_lag_integral_lower {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    c - 3 * c * a - 3 * c * b ≤
      ∫ g, c * g ^ 2 / ((1 + a * g ^ 2) * (1 + b * g ^ 2))
        ∂(ProbabilityTheory.gaussianReal 0 1) := by
  let f : ℝ → ℝ := fun g => c * g ^ 2 * (1 - a * g ^ 2 - b * g ^ 2)
  let F : ℝ → ℝ := fun g => c * g ^ 2 /
    ((1 + a * g ^ 2) * (1 + b * g ^ 2))
  have hf : Integrable f (ProbabilityTheory.gaussianReal 0 1) := by
    have h2 := (Muon.Foundations.gaussian_integrable_pow 2).const_mul c
    have h4a := (Muon.Foundations.gaussian_integrable_pow 4).const_mul (c * a)
    have h4b := (Muon.Foundations.gaussian_integrable_pow 4).const_mul (c * b)
    have he : f = fun g => c * g ^ 2 - (c * a) * g ^ 4 - (c * b) * g ^ 4 := by
      funext g
      simp only [f]
      ring
    rw [he]
    exact (h2.sub h4a).sub h4b
  have hF : Integrable F (ProbabilityTheory.gaussianReal 0 1) := by
    have hcont : Continuous F := by
      apply Continuous.div (by fun_prop) (by fun_prop)
      intro g
      have h1 : 0 ≤ a * g ^ 2 := mul_nonneg ha (sq_nonneg g)
      have h2 : 0 ≤ b * g ^ 2 := mul_nonneg hb (sq_nonneg g)
      positivity
    refine Integrable.mono' ((Muon.Foundations.gaussian_integrable_pow 2).const_mul c)
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    have h1 : 0 ≤ a * g ^ 2 := mul_nonneg ha (sq_nonneg g)
    have h2 : 0 ≤ b * g ^ 2 := mul_nonneg hb (sq_nonneg g)
    have hD : 1 ≤ (1 + a * g ^ 2) * (1 + b * g ^ 2) := by
      nlinarith [mul_nonneg h1 h2]
    have hN : 0 ≤ c * g ^ 2 := mul_nonneg hc (sq_nonneg g)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hN (by positivity))]
    exact div_le_self hN hD
  have hpt : ∀ g, f g ≤ F g := by
    intro g
    have hA : 0 ≤ a * g ^ 2 := mul_nonneg ha (sq_nonneg g)
    have hB : 0 ≤ b * g ^ 2 := mul_nonneg hb (sq_nonneg g)
    have hD : 0 < (1 + a * g ^ 2) * (1 + b * g ^ 2) := by positivity
    have hbase : 1 - a * g ^ 2 - b * g ^ 2 ≤
        1 / ((1 + a * g ^ 2) * (1 + b * g ^ 2)) := by
      rw [le_div_iff₀ hD]
      nlinarith [sq_nonneg (a * g ^ 2), sq_nonneg (b * g ^ 2),
        mul_nonneg (mul_nonneg hA hB) (by positivity : 0 ≤ 1 + a * g ^ 2 + b * g ^ 2)]
    dsimp only [f, F]
    calc c * g ^ 2 * (1 - a * g ^ 2 - b * g ^ 2)
        ≤ c * g ^ 2 * (1 / ((1 + a * g ^ 2) * (1 + b * g ^ 2))) :=
          mul_le_mul_of_nonneg_left hbase (mul_nonneg hc (sq_nonneg g))
      _ = c * g ^ 2 / ((1 + a * g ^ 2) * (1 + b * g ^ 2)) := by ring
  have hint := integral_mono hf hF hpt
  have hval : ∫ g, f g ∂(ProbabilityTheory.gaussianReal 0 1) = c - 3 * c * a - 3 * c * b := by
    have h2 := (Muon.Foundations.gaussian_integrable_pow 2).const_mul c
    have h4a := (Muon.Foundations.gaussian_integrable_pow 4).const_mul (c * a)
    have h4b := (Muon.Foundations.gaussian_integrable_pow 4).const_mul (c * b)
    have he : f = fun g => c * g ^ 2 - (c * a) * g ^ 4 - (c * b) * g ^ 4 := by
      funext g
      simp only [f]
      ring
    rw [he]
    calc
      (∫ g, c * g ^ 2 - c * a * g ^ 4 - c * b * g ^ 4
          ∂(ProbabilityTheory.gaussianReal 0 1)) =
          (∫ g, c * g ^ 2 - c * a * g ^ 4 ∂(ProbabilityTheory.gaussianReal 0 1)) -
            ∫ g, c * b * g ^ 4 ∂(ProbabilityTheory.gaussianReal 0 1) := by
        simpa only [Pi.sub_apply] using integral_sub (h2.sub h4a) h4b
      _ = ((∫ g, c * g ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1)) -
            ∫ g, c * a * g ^ 4 ∂(ProbabilityTheory.gaussianReal 0 1)) -
            ∫ g, c * b * g ^ 4 ∂(ProbabilityTheory.gaussianReal 0 1) := by
        rw [integral_sub h2 h4a]
      _ = c - 3 * c * a - 3 * c * b := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul,
          Muon.Foundations.gaussian_moment_two, Muon.Foundations.gaussian_moment_four]
        ring
  simpa only [F, hval] using hint

private lemma p10_summable_emaW_pow {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {p : ℕ}
    (hp : p ≠ 0) : Summable (fun j : ℕ => Muon.emaW β j ^ p) := by
  have he : (fun j : ℕ => Muon.emaW β j ^ p) =
      fun j : ℕ => (1 - β) ^ p * (β ^ p) ^ j := by
    funext j
    unfold Muon.emaW
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j p]
  rw [he]
  exact (summable_geometric_of_lt_one (pow_nonneg hβ0 p)
    (pow_lt_one₀ hβ0 hβ1 hp)).mul_left _

private lemma p10_lag_integral_nonneg_le {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    0 ≤ ∫ g, c * g ^ 2 / ((1 + a * g ^ 2) * (1 + b * g ^ 2))
      ∂(ProbabilityTheory.gaussianReal 0 1) ∧
    (∫ g, c * g ^ 2 / ((1 + a * g ^ 2) * (1 + b * g ^ 2))
      ∂(ProbabilityTheory.gaussianReal 0 1)) ≤ c := by
  have hpt : ∀ g : ℝ,
      0 ≤ c * g ^ 2 / ((1 + a * g ^ 2) * (1 + b * g ^ 2)) ∧
      c * g ^ 2 / ((1 + a * g ^ 2) * (1 + b * g ^ 2)) ≤ c * g ^ 2 := by
    intro g
    have hA : 0 ≤ a * g ^ 2 := mul_nonneg ha (sq_nonneg g)
    have hB : 0 ≤ b * g ^ 2 := mul_nonneg hb (sq_nonneg g)
    have hD : 1 ≤ (1 + a * g ^ 2) * (1 + b * g ^ 2) := by
      nlinarith [mul_nonneg hA hB]
    have hN : 0 ≤ c * g ^ 2 := mul_nonneg hc (sq_nonneg g)
    exact ⟨div_nonneg hN (by positivity), div_le_self hN hD⟩
  constructor
  · exact integral_nonneg fun g => (hpt g).1
  · calc
      (∫ g, c * g ^ 2 / ((1 + a * g ^ 2) * (1 + b * g ^ 2))
          ∂(ProbabilityTheory.gaussianReal 0 1))
          ≤ ∫ g, c * g ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => (hpt g).1)
          ((Muon.Foundations.gaussian_integrable_pow 2).const_mul c)
          (Filter.Eventually.of_forall fun g => (hpt g).2)
      _ = c := by
        rw [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one]

private lemma p10_isoLagB_lower {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s') (l : ℕ) :
    β ^ l * (Muon.sPow β 2 - 3 * Muon.sPow β 4 *
      (qIso β γ γ s + β ^ (2 * l) * qIso β γ γ s')) ≤ isoLagB β γ l s s' := by
  let q := qIso β γ γ s
  let q' := qIso β γ γ s'
  let r := β ^ l
  let I : ℕ → ℝ := fun j => ∫ g,
    r * Muon.emaW β j ^ 2 * g ^ 2 /
      ((1 + q * Muon.emaW β j ^ 2 * g ^ 2) *
        (1 + β ^ (2 * l) * q' * Muon.emaW β j ^ 2 * g ^ 2))
      ∂(ProbabilityTheory.gaussianReal 0 1)
  let L : ℕ → ℝ := fun j =>
    r * Muon.emaW β j ^ 2 - 3 * (r * Muon.emaW β j ^ 2) *
      (q * Muon.emaW β j ^ 2) - 3 * (r * Muon.emaW β j ^ 2) *
        (β ^ (2 * l) * q' * Muon.emaW β j ^ 2)
  have hlink := p10_link hβ0 hβ1
  have hq : 0 ≤ q := ((lem_app_iso_comparison_i hlink hγ0 hγ0).2.2.2.1 s hs).1.1
  have hq' : 0 ≤ q' := ((lem_app_iso_comparison_i hlink hγ0 hγ0).2.2.2.1 s' hs').1.1
  have hr : 0 ≤ r := pow_nonneg hβ0.le l
  have hpow : 0 ≤ β ^ (2 * l) := pow_nonneg hβ0.le _
  have hI : ∀ j, L j ≤ I j ∧ 0 ≤ I j ∧ I j ≤ r * Muon.emaW β j ^ 2 := by
    intro j
    have hc : 0 ≤ r * Muon.emaW β j ^ 2 := mul_nonneg hr (sq_nonneg _)
    have ha : 0 ≤ q * Muon.emaW β j ^ 2 := mul_nonneg hq (sq_nonneg _)
    have hb : 0 ≤ β ^ (2 * l) * q' * Muon.emaW β j ^ 2 := by positivity
    exact ⟨p10_lag_integral_lower hc ha hb,
      (p10_lag_integral_nonneg_le hc ha hb).1,
      (p10_lag_integral_nonneg_le hc ha hb).2⟩
  have hS2 := p10_summable_emaW_pow hβ0.le hβ1 (p := 2) (by norm_num)
  have hS4 := p10_summable_emaW_pow hβ0.le hβ1 (p := 4) (by norm_num)
  have hLI : Summable L := by
    have he : L = fun j => r * Muon.emaW β j ^ 2 -
        (3 * r * q) * Muon.emaW β j ^ 4 -
        (3 * r * (β ^ (2 * l) * q')) * Muon.emaW β j ^ 4 := by
      funext j
      simp only [L]
      ring
    rw [he]
    exact ((hS2.mul_left r).sub (hS4.mul_left (3 * r * q))).sub
      (hS4.mul_left (3 * r * (β ^ (2 * l) * q')))
  have hII : Summable I := Summable.of_nonneg_of_le (fun j => (hI j).2.1)
    (fun j => (hI j).2.2) (hS2.mul_left r)
  have hsum : ∑' j, L j ≤ ∑' j, I j := Summable.tsum_le_tsum (fun j => (hI j).1) hLI hII
  have hLval : ∑' j, L j = r * (Muon.sPow β 2 - 3 * Muon.sPow β 4 *
      (q + β ^ (2 * l) * q')) := by
    have he : L = fun j => r * Muon.emaW β j ^ 2 -
        (3 * r * q) * Muon.emaW β j ^ 4 -
        (3 * r * (β ^ (2 * l) * q')) * Muon.emaW β j ^ 4 := by
      funext j
      simp only [L]
      ring
    rw [he, Summable.tsum_sub ((hS2.mul_left r).sub (hS4.mul_left (3 * r * q)))
        (hS4.mul_left (3 * r * (β ^ (2 * l) * q'))),
      Summable.tsum_sub (hS2.mul_left r) (hS4.mul_left (3 * r * q)),
      tsum_mul_left, tsum_mul_left, tsum_mul_left]
    unfold Muon.sPow
    ring
  change r * (Muon.sPow β 2 - 3 * Muon.sPow β 4 *
    (q + β ^ (2 * l) * q')) ≤ ∑' j, I j
  rwa [← hLval]

private lemma p10_J_lower {x : ℝ} (hx : 0 ≤ x) :
    1 - 3 * x ≤ Muon.DetEquiv.J x := by
  rcases hx.eq_or_lt with h | h
  · rw [← h]
    have hJ : Muon.DetEquiv.J 0 = 1 := by
      unfold Muon.DetEquiv.J
      simp only [zero_mul, add_zero, div_one]
      exact Muon.Foundations.gaussian_moment_two
    rw [hJ]
    norm_num
  · have h3 := (lem_app_iso_gaussian_iii x h).2
    have he : isoPhi x = x * Muon.DetEquiv.J x := rfl
    rw [he] at h3
    by_contra hc
    push Not at hc
    nlinarith [mul_lt_mul_of_pos_left hc h]

private lemma p10_Fw_lower {β q : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hq : 0 ≤ q) :
    Muon.sPow β 2 - 3 * Muon.sPow β 4 * q ≤
      Muon.DetEquiv.Fw (Muon.emaW β) q := by
  have h2 := p10_summable_emaW_pow hβ0 hβ1 (p := 2) (by norm_num)
  have h4 := p10_summable_emaW_pow hβ0 hβ1 (p := 4) (by norm_num)
  have hterm : ∀ j : ℕ,
      Muon.emaW β j ^ 2 - 3 * q * Muon.emaW β j ^ 4 ≤
        Muon.emaW β j ^ 2 * Muon.DetEquiv.J (Muon.emaW β j ^ 2 * q) := by
    intro j
    have h := p10_J_lower (mul_nonneg (sq_nonneg (Muon.emaW β j)) hq)
    nlinarith [sq_nonneg (Muon.emaW β j)]
  have hJ0 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Muon.DetEquiv.J x := by
    intro x hx
    unfold Muon.DetEquiv.J
    exact integral_nonneg fun g => div_nonneg (sq_nonneg g) (by positivity)
  have hJ1 : ∀ x : ℝ, 0 ≤ x → Muon.DetEquiv.J x ≤ 1 := by
    intro x hx
    rcases hx.eq_or_lt with h | h
    · subst x
      unfold Muon.DetEquiv.J
      simp only [zero_mul, add_zero, div_one]
      exact Muon.Foundations.gaussian_moment_two.le
    · exact ((lem_app_iso_weights_iii).1 x h).trans (min_le_left _ _)
  have hsum : Summable (fun j : ℕ => Muon.emaW β j ^ 2 *
      Muon.DetEquiv.J (Muon.emaW β j ^ 2 * q)) :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (sq_nonneg _) (hJ0 _ (mul_nonneg (sq_nonneg _) hq)))
      (fun j => mul_le_of_le_one_right (sq_nonneg _)
        (hJ1 _ (mul_nonneg (sq_nonneg _) hq))) h2
  have hlow : Summable (fun j : ℕ =>
      Muon.emaW β j ^ 2 - 3 * q * Muon.emaW β j ^ 4) :=
    h2.sub (h4.mul_left (3 * q))
  have hle := Summable.tsum_le_tsum hterm hlow hsum
  rw [Summable.tsum_sub h2 (h4.mul_left (3 * q)), tsum_mul_left] at hle
  unfold Muon.DetEquiv.Fw Muon.sPow
  linarith

private lemma p10_sPow4_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Muon.sPow β 4 ≤ (1 - β ^ 2) * Muon.sPow β 2 ^ 2 := by
  have hb : 0 < 1 - β := by linarith
  have hb2 : β ^ 2 < 1 := by nlinarith
  have h2 := Muon.sPow_eq hβ0 hβ1 (p := 2) le_rfl
  have h4 := Muon.sPow_eq hβ0 hβ1 (p := 4) (by norm_num)
  have hb4 : β ^ 4 ≤ β ^ 2 := by nlinarith [pow_nonneg hβ0 2]
  have hd2 : 0 < 1 - β ^ 2 := by linarith
  have hd4 : 0 < 1 - β ^ 4 := by linarith
  rw [h4, h2, div_pow, mul_div_assoc', div_le_div_iff₀ hd4 (by positivity)]
  have he : (1 - β ^ 2) ^ 2 = (1 - β ^ 2) * (1 - β ^ 2) := by ring
  nlinarith [pow_pos hb 4, mul_nonneg (pow_pos hb 4).le (sub_nonneg.2 hb4),
    mul_pos (pow_pos hb 4) hd2, he]

private lemma p10_q_upper {β γ s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hsmall : 6 * γ * (1 - β ^ 2) ≤ 1 / 2) (hs : 0 < s) :
    qIso β γ γ s ≤ 2 * γ / Muon.sPow β 2 := by
  let S := Muon.sPow β 2
  let q := qIso β γ γ s
  have hS : 0 < S := by
    simp only [S, Muon.sPow_two hβ0.le hβ1]
    positivity
  have hlink := p10_link hβ0 hβ1
  have hspec := (lem_app_iso_comparison_i hlink hγ0 hγ0).2.2.2.1 s hs
  obtain ⟨hq0, hrq⟩ := hspec.1
  simp only [min_self] at hrq
  change 0 ≤ q at hq0
  change Muon.DetEquiv.rW (Muon.emaW β) q < γ at hrq
  by_contra hc
  push Not at hc
  let qb := 2 * γ / S
  change qb < q at hc
  have hqb0 : 0 ≤ qb := by positivity
  have hmono := hlink.2.1
  have h1 : Muon.DetEquiv.rW (Muon.emaW β) qb ≤
      Muon.DetEquiv.rW (Muon.emaW β) q :=
    hmono.monotoneOn (mem_Ici.2 hqb0) (mem_Ici.2 hq0) hc.le
  have h2 := p10_Fw_lower hβ0.le hβ1 hqb0
  have h3 : S * qb = 2 * γ := by dsimp only [qb]; field_simp
  have h4 : 3 * Muon.sPow β 4 * qb * qb ≤ γ := by
    have h5 : 3 * Muon.sPow β 4 * qb * qb ≤
        3 * ((1 - β ^ 2) * S ^ 2) * qb * qb := by
      have hm := mul_le_mul_of_nonneg_right (p10_sPow4_le hβ0.le hβ1)
        (mul_nonneg hqb0 hqb0)
      nlinarith [mul_nonneg hqb0 hqb0]
    have h6 : S ^ 2 * (qb * qb) = (2 * γ) ^ 2 := by rw [← h3]; ring
    have h7 : 3 * ((1 - β ^ 2) * S ^ 2) * qb * qb =
        2 * γ * (6 * γ * (1 - β ^ 2)) := by
      calc
        3 * ((1 - β ^ 2) * S ^ 2) * qb * qb =
            3 * (1 - β ^ 2) * (S ^ 2 * (qb * qb)) := by ring
        _ = 3 * (1 - β ^ 2) * (2 * γ) ^ 2 := by rw [h6]
        _ = 2 * γ * (6 * γ * (1 - β ^ 2)) := by ring
    rw [h7] at h5
    nlinarith [mul_le_mul_of_nonneg_left hsmall hγ0.le]
  have h8 : γ ≤ Muon.DetEquiv.rW (Muon.emaW β) qb := by
    unfold Muon.DetEquiv.rW
    change S - 3 * Muon.sPow β 4 * qb ≤ Muon.DetEquiv.Fw (Muon.emaW β) qb at h2
    have hm := mul_le_mul_of_nonneg_left h2 hqb0
    nlinarith
  linarith

private lemma p10_sPow4_ratio {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Muon.sPow β 4 = (1 - β ^ 2) / (1 + β ^ 2) * Muon.sPow β 2 ^ 2 := by
  have hb1 : 0 < 1 - β := by linarith
  have hp1 : 0 < 1 + β := by linarith
  have hp2 : 0 < 1 + β ^ 2 := by positivity
  have h4 := Muon.sPow_eq hβ0 hβ1 (p := 4) (by norm_num)
  rw [h4, Muon.sPow_two hβ0 hβ1]
  have he : 1 - β ^ 4 = (1 - β) * (1 + β) * (1 + β ^ 2) := by ring
  rw [he]
  field_simp
  ring

private lemma p10_delta_bounds {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ : γ ≤ (1 + β ^ 2) / 96) :
    let δ := 12 * γ * (1 - β ^ 2) / (1 + β ^ 2)
    0 ≤ δ ∧ δ ≤ 1 / 8 ∧ 4 * δ ≤ (1 - β ^ 2) / 2 := by
  dsimp only
  have hb2 : 0 ≤ 1 - β ^ 2 := by nlinarith
  have hd : 0 < 1 + β ^ 2 := by positivity
  have h96 : 96 * γ ≤ 1 + β ^ 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 96)] at hγ
    nlinarith
  constructor
  · positivity
  constructor
  · rw [div_le_iff₀ hd]
    nlinarith [mul_nonneg hγ0.le hb2]
  · calc
      4 * (12 * γ * (1 - β ^ 2) / (1 + β ^ 2)) =
          (48 * γ * (1 - β ^ 2)) / (1 + β ^ 2) := by ring
      _ ≤ (1 - β ^ 2) / 2 := by
        rw [div_le_div_iff₀ hd (by norm_num : (0 : ℝ) < 2)]
        nlinarith [mul_le_mul_of_nonneg_right h96 hb2]

private lemma p10_isoLagB_sandwich {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ : γ ≤ (1 + β ^ 2) / 96) {s s' : ℝ}
    (hs : 0 < s) (hs' : 0 < s') (l : ℕ) :
    let δ := 12 * γ * (1 - β ^ 2) / (1 + β ^ 2)
    β ^ l * Muon.sPow β 2 * (1 - δ) ≤ isoLagB β γ l s s' ∧
      isoLagB β γ l s s' ≤ β ^ l * Muon.sPow β 2 := by
  dsimp only
  let S := Muon.sPow β 2
  let δ := 12 * γ * (1 - β ^ 2) / (1 + β ^ 2)
  have hS : 0 < S := by
    simp only [S, Muon.sPow_two hβ0.le hβ1]
    positivity
  have hb2 : 0 ≤ 1 - β ^ 2 := by nlinarith
  have hsmall : 6 * γ * (1 - β ^ 2) ≤ 1 / 2 := by
    have hd : 0 < 1 + β ^ 2 := by positivity
    have h96 : 96 * γ ≤ 1 + β ^ 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 96)] at hγ
      nlinarith
    nlinarith [mul_nonneg hγ0.le hb2, sq_nonneg β]
  have hq := p10_q_upper hβ0 hβ1 hγ0 hsmall hs
  have hq' := p10_q_upper hβ0 hβ1 hγ0 hsmall hs'
  change qIso β γ γ s ≤ 2 * γ / S at hq
  change qIso β γ γ s' ≤ 2 * γ / S at hq'
  have hp : β ^ (2 * l) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hp0 : 0 ≤ β ^ (2 * l) := pow_nonneg hβ0.le _
  have hq'0 : 0 ≤ qIso β γ γ s' :=
    ((lem_app_iso_comparison_i (p10_link hβ0 hβ1) hγ0 hγ0).2.2.2.1 s' hs').1.1
  have hsum : qIso β γ γ s + β ^ (2 * l) * qIso β γ γ s' ≤ 4 * γ / S := by
    have hm := mul_le_mul hp hq' hq'0 (by norm_num : (0 : ℝ) ≤ 1)
    calc
      qIso β γ γ s + β ^ (2 * l) * qIso β γ γ s'
          ≤ 2 * γ / S + 2 * γ / S := add_le_add hq (by simpa using hm)
      _ = 4 * γ / S := by ring
  have hcorr : 3 * Muon.sPow β 4 *
      (qIso β γ γ s + β ^ (2 * l) * qIso β γ γ s') ≤ δ * S := by
    have hS4 : Muon.sPow β 4 = (1 - β ^ 2) / (1 + β ^ 2) * S ^ 2 := by
      simpa only [S] using p10_sPow4_ratio hβ0.le hβ1
    have hS40 : 0 ≤ Muon.sPow β 4 := by rw [hS4]; positivity
    have hm := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 3 * Muon.sPow β 4)
    calc
      3 * Muon.sPow β 4 *
          (qIso β γ γ s + β ^ (2 * l) * qIso β γ γ s')
          ≤ 3 * Muon.sPow β 4 * (4 * γ / S) := hm
      _ = δ * S := by
        rw [hS4]
        dsimp only [δ]
        field_simp
        ring
  have hlo0 := p10_isoLagB_lower hβ0 hβ1 hγ0 hs hs' l
  have hr : 0 ≤ β ^ l := pow_nonneg hβ0.le l
  have hlo : β ^ l * S * (1 - δ) ≤ isoLagB β γ l s s' := by
    change β ^ l * S * (1 - δ) ≤ _
    change β ^ l * (S - 3 * Muon.sPow β 4 *
      (qIso β γ γ s + β ^ (2 * l) * qIso β γ γ s')) ≤ _ at hlo0
    have hm := mul_le_mul_of_nonneg_left hcorr hr
    nlinarith
  have hhi := (lem_app_iso_lag_i hβ0 hβ1 hγ0 hs hs' l).1.2
  change isoLagB β γ l s s' ≤ β ^ l * S at hhi
  exact ⟨hlo, hhi⟩

private noncomputable def p10x_u (t : ℝ) : ℝ := ((Real.sqrt (t ^ 2 + 4) - t) / 2) ^ 2

private lemma p10x_u_spec {t : ℝ} (ht : 0 ≤ t) :
    0 < p10x_u t ∧ p10x_u t ≤ 1 ∧ t ^ 2 * p10x_u t = (1 - p10x_u t) ^ 2 := by
  have hs : Real.sqrt (t ^ 2 + 4) ^ 2 = t ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have hlt : t < Real.sqrt (t ^ 2 + 4) := by
    apply Real.lt_sqrt_of_sq_lt; linarith
  set w := (Real.sqrt (t ^ 2 + 4) - t) / 2 with hw
  have hw0 : 0 < w := by rw [hw]; linarith
  have hw1 : w ^ 2 + t * w = 1 := by rw [hw]; nlinarith [hs]
  have hu : p10x_u t = w ^ 2 := rfl
  rw [hu]
  have h1 : 1 - w ^ 2 = t * w := by linarith
  refine ⟨by positivity, ?_, ?_⟩
  · nlinarith [mul_nonneg ht hw0.le]
  · rw [h1]; ring

private lemma p10x_sandwich_alg {t Y δ η : ℝ} (ht : 0 < t) (hY0 : 0 < Y) (hY2 : Y ≤ 2)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 8) (hη0 : 0 ≤ η) (hη : η ≤ δ / 4 * Y ^ 2)
    (hR : t ^ 2 * Y = (1 - Y + η) ^ 2) (hRpos : 0 < 1 - Y + η) :
    p10x_u t ≤ Y ∧ (1 - δ / 2) ^ 2 * Y ≤ p10x_u t := by
  obtain ⟨hu0, hu1, hu⟩ := p10x_u_spec ht.le
  set u := p10x_u t
  constructor
  · by_contra hc
    push Not at hc
    -- Y < u ≤ 1
    have h1 : 0 < 1 - u * Y := by nlinarith
    have h2 : 0 < (u - Y) * (1 - u * Y) := mul_pos (by linarith) h1
    have h3 : (1 - Y) ^ 2 ≤ t ^ 2 * Y := by
      rw [hR]
      have : 1 - Y ≤ 1 - Y + η := by linarith
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h3 hu0.le]
  · by_contra hc
    push Not at hc
    set a := 1 - δ / 2 with ha
    have ha0 : 0 < a := by rw [ha]; linarith
    have ha1 : a ≤ 1 := by rw [ha]; linarith
    set v := a ^ 2 * Y with hv
    have hv0 : 0 < v := by positivity
    -- key: a R + v ≤ 1
    have hkey : a * (1 - Y + η) + v ≤ 1 := by
      have : δ / 2 * (1 + a * Y) - a * η ≥ 0 := by
        have h4 : a * η ≤ a * (δ / 4 * Y ^ 2) := mul_le_mul_of_nonneg_left hη ha0.le
        have h5 : a * Y ^ 2 ≤ 2 * (a * Y) := by nlinarith [mul_nonneg ha0.le hY0.le]
        have h6 := mul_le_mul_of_nonneg_left h5 (by linarith : (0:ℝ) ≤ δ / 8)
        have h7 := mul_nonneg hδ0 (mul_nonneg ha0.le hY0.le)
        nlinarith [h4, h6, h7]
      rw [hv, ha]; nlinarith
    have hv1 : v < 1 := by
      have : 0 < a * (1 - Y + η) := mul_pos ha0 hRpos
      linarith
    have h1 : 0 < 1 - u * v := by nlinarith
    have h2 : 0 < (v - u) * (1 - u * v) := mul_pos (by linarith) h1
    -- (1-u)^2 v > (1-v)^2 u
    have h5 : (1 - v) ^ 2 * u < (1 - u) ^ 2 * v := by nlinarith
    rw [← hu] at h5
    have h6 : (1 - v) ^ 2 < t ^ 2 * v := by
      have := h5
      nlinarith
    have h7 : t ^ 2 * v = (a * (1 - Y + η)) ^ 2 := by
      rw [hv]; nlinarith [hR]
    rw [h7] at h6
    have hP := mul_pos ha0 hRpos
    have hP2 : (a * (1 - Y + η)) ^ 2 ≤ (1 - v) ^ 2 :=
      pow_le_pow_left₀ hP.le (by linarith) 2
    linarith


private lemma p10x_Fw_le {β q : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hq : 0 ≤ q) :
    Muon.DetEquiv.Fw (Muon.emaW β) q ≤ Muon.sPow β 2 := by
  have h2 := p10_summable_emaW_pow hβ0 hβ1 (p := 2) (by norm_num)
  have hJ0 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Muon.DetEquiv.J x := by
    intro x hx
    unfold Muon.DetEquiv.J
    exact integral_nonneg fun g => div_nonneg (sq_nonneg g) (by positivity)
  have hJ1 : ∀ x : ℝ, 0 ≤ x → Muon.DetEquiv.J x ≤ 1 := by
    intro x hx
    rcases hx.eq_or_lt with h | h
    · subst x
      unfold Muon.DetEquiv.J
      simp only [zero_mul, add_zero, div_one]
      exact Muon.Foundations.gaussian_moment_two.le
    · exact ((lem_app_iso_weights_iii).1 x h).trans (min_le_left _ _)
  have hterm : ∀ j : ℕ, Muon.emaW β j ^ 2 * Muon.DetEquiv.J (Muon.emaW β j ^ 2 * q) ≤
      Muon.emaW β j ^ 2 := fun j =>
    mul_le_of_le_one_right (sq_nonneg _) (hJ1 _ (mul_nonneg (sq_nonneg _) hq))
  have hsum : Summable (fun j : ℕ => Muon.emaW β j ^ 2 *
      Muon.DetEquiv.J (Muon.emaW β j ^ 2 * q)) :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (sq_nonneg _) (hJ0 _ (mul_nonneg (sq_nonneg _) hq))) hterm h2
  unfold Muon.DetEquiv.Fw Muon.sPow
  exact Summable.tsum_le_tsum hterm hsum h2

private lemma p10x_q_facts {β γ s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hsmall : 6 * γ * (1 - β ^ 2) ≤ 1 / 2) (hs : 0 < s) :
    0 < qIso β γ γ s ∧ qIso β γ γ s ≤ 2 * γ / Muon.sPow β 2 ∧
    s * qIso β γ γ s = (γ - Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ s)) ^ 2 ∧
    Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ s) < γ ∧
    Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ s) ≤ Muon.sPow β 2 * qIso β γ γ s ∧
    Muon.sPow β 2 * qIso β γ γ s - 3 * Muon.sPow β 4 * qIso β γ γ s ^ 2 ≤
      Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ s) := by
  have hspec := (lem_app_iso_comparison_i (p10_link hβ0 hβ1) hγ0 hγ0).2.2.2.1 s hs
  obtain ⟨⟨hq0, hrq⟩, hG⟩ := hspec
  simp only [min_self] at hrq
  change 0 ≤ qIso β γ γ s at hq0
  change Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ s) < γ at hrq
  have hG' : s * qIso β γ γ s = (γ - Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ s)) ^ 2 := by
    have : s * qIso β γ γ s - (γ - Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ s)) *
        (γ - Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ s)) = 0 := hG
    nlinarith
  have hqpos : 0 < qIso β γ γ s := by
    rcases hq0.eq_or_lt with h | h
    · exfalso
      rw [← h] at hG'
      have : 0 < (γ - Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ s)) ^ 2 := by
        have : 0 < γ - Muon.DetEquiv.rW (Muon.emaW β) (qIso β γ γ s) := by linarith
        positivity
      rw [← h] at this
      simp at hG'
      linarith
    · exact h
  have hFl := p10_Fw_lower hβ0.le hβ1 hq0
  have hFu := p10x_Fw_le hβ0.le hβ1 hq0
  refine ⟨hqpos, p10_q_upper hβ0 hβ1 hγ0 hsmall hs, hG', hrq, ?_, ?_⟩
  · unfold Muon.DetEquiv.rW
    nlinarith
  · unfold Muon.DetEquiv.rW
    nlinarith


private lemma p10x_S_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 < Muon.sPow β 2 := by
  rw [Muon.sPow_two hβ0.le hβ1]
  have : 0 < 1 - β := by linarith
  positivity

private lemma p10x_hsmall {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ : γ ≤ (1 + β ^ 2) / 96) : 6 * γ * (1 - β ^ 2) ≤ 1 / 2 := by
  have hb2 : 0 ≤ 1 - β ^ 2 := by nlinarith
  have hd : 0 < 1 + β ^ 2 := by positivity
  have h96 : 96 * γ ≤ 1 + β ^ 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 96)] at hγ
    nlinarith
  nlinarith [mul_nonneg hγ0.le hb2, sq_nonneg β]

private lemma p10x_Y_sandwich {β γ t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ : γ ≤ (1 + β ^ 2) / 96) (ht : 0 < t) :
    let S := Muon.sPow β 2
    let δ := 12 * γ * (1 - β ^ 2) / (1 + β ^ 2)
    let Y := S * qIso β γ γ (S * γ * t ^ 2) / γ
    0 < Y ∧ Y ≤ 2 ∧ p10x_u t ≤ Y ∧ (1 - δ / 2) ^ 2 * Y ≤ p10x_u t := by
  intro S δ Y
  have hS : 0 < S := p10x_S_pos hβ0 hβ1
  have hs : 0 < S * γ * t ^ 2 := by positivity
  obtain ⟨hδ0, hδ1, -⟩ := p10_delta_bounds hβ0 hβ1 hγ0 hγ
  obtain ⟨hq0, hqU, hG, hrq, hru, hrl⟩ :=
    p10x_q_facts hβ0 hβ1 hγ0 (p10x_hsmall hβ0 hβ1 hγ0 hγ) hs
  set q := qIso β γ γ (S * γ * t ^ 2) with hq
  set m := Muon.DetEquiv.rW (Muon.emaW β) q with hm
  have hY0 : 0 < Y := by positivity
  have hY2 : Y ≤ 2 := by
    have : S * q ≤ 2 * γ := by
      rw [le_div_iff₀ hS] at hqU
      linarith
    show S * q / γ ≤ 2
    rw [div_le_iff₀ hγ0]; linarith
  have hqY : q = γ * Y / S := by
    show q = γ * (S * q / γ) / S
    field_simp
  have h4 : Muon.sPow β 4 = (1 - β ^ 2) / (1 + β ^ 2) * S ^ 2 := p10_sPow4_ratio hβ0.le hβ1
  have hη : (S * q - m) / γ ≤ δ / 4 * Y ^ 2 := by
    rw [div_le_iff₀ hγ0]
    have h5 : S * q - m ≤ 3 * Muon.sPow β 4 * q ^ 2 := by linarith
    have h6 : 3 * Muon.sPow β 4 * q ^ 2 = δ / 4 * Y ^ 2 * γ := by
      rw [h4, hqY]
      dsimp only [δ]
      field_simp
      ring
    linarith
  have hη0 : 0 ≤ (S * q - m) / γ := div_nonneg (by linarith) hγ0.le
  have hR : 1 - Y + (S * q - m) / γ = (γ - m) / γ := by
    show 1 - S * q / γ + (S * q - m) / γ = (γ - m) / γ
    field_simp
    ring
  have hRpos : 0 < 1 - Y + (S * q - m) / γ := by
    rw [hR]; exact div_pos (by linarith) hγ0
  have hEq : t ^ 2 * Y = (1 - Y + (S * q - m) / γ) ^ 2 := by
    rw [hR, div_pow, ← hG, eq_div_iff (by positivity)]
    show t ^ 2 * (S * q / γ) * γ ^ 2 = S * γ * t ^ 2 * q
    field_simp
  obtain ⟨h1, h2⟩ := p10x_sandwich_alg ht hY0 hY2 hδ0 hδ1 hη0 hη hEq hRpos
  exact ⟨hY0, hY2, h1, h2⟩


set_option maxHeartbeats 1000000 in
private lemma p10x_alg {r ω δ Y Y0 bt η : ℝ} (hr : 0 < r) (hω : 0 < ω)
    (hrω : r ^ 2 ≤ 1 - ω) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 8) (hδω : 4 * δ ≤ ω / 2)
    (hY0 : 0 < Y0) (hY0le : Y0 ≤ 1) (hYl : Y0 ≤ Y) (hYu : (1 - δ) ^ 2 * Y ≤ Y0)
    (hb1 : 1 - δ ≤ bt) (hb2 : bt ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ δ)
    (hD : 0 < (1 - η) ^ 2 - r ^ 2 * bt ^ 2 * Y) :
    (1 - 8 * δ / ω) * (r * Y0 / (1 - r ^ 2 * Y0)) ≤ r * bt * Y / ((1 - η) ^ 2 - r ^ 2 * bt ^ 2 * Y) ∧
    r * bt * Y / ((1 - η) ^ 2 - r ^ 2 * bt ^ 2 * Y) ≤ (1 + 8 * δ / ω) * (r * Y0 / (1 - r ^ 2 * Y0)) := by
  set P := r ^ 2 * Y0 with hP
  have hP0 : 0 ≤ P := by positivity
  have hPle : P ≤ 1 - ω := by
    rw [hP]; nlinarith [mul_le_mul_of_nonneg_left hY0le (sq_nonneg r)]
  set W := 1 - P with hW
  have hWω : ω ≤ W := by rw [hW]; linarith
  have hW1 : W ≤ 1 := by rw [hW]; linarith
  have hW0 : 0 < W := by linarith
  have hω8 : 8 * δ ≤ ω := by linarith
  have hY : 0 < Y := by linarith
  set D := (1 - η) ^ 2 - r ^ 2 * bt ^ 2 * Y with hDdef
  clear_value D W P
  have hrY0 : 0 < r * Y0 := by positivity
  have hF : 0 < r * Y0 / W := by positivity
  have hm0 : 0 < 1 - δ := by linarith
  constructor
  · -- lower bound
    have hN : r * (1 - δ) * Y0 ≤ r * bt * Y := by
      have h1 : (1 - δ) * Y0 ≤ bt * Y := mul_le_mul hb1 hYl hY0.le (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left h1 hr.le]
    have hDle : D ≤ W + 2 * δ := by
      have h1 : (1 - η) ^ 2 ≤ 1 := by nlinarith
      have h2 : (1 - δ) ^ 2 * Y0 ≤ bt ^ 2 * Y := by
        have : (1 - δ) ^ 2 ≤ bt ^ 2 := pow_le_pow_left₀ hm0.le hb1 2
        exact mul_le_mul this hYl hY0.le (sq_nonneg _)
      have h3 : r ^ 2 * ((1 - δ) ^ 2 * Y0) ≤ r ^ 2 * (bt ^ 2 * Y) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg r)
      have h4 : (1 - δ) ^ 2 ≥ 1 - 2 * δ := by nlinarith
      have h5 : r ^ 2 * Y0 * (1 - 2 * δ) ≤ r ^ 2 * ((1 - δ) ^ 2 * Y0) := by
        have := mul_le_mul_of_nonneg_left h4 hP0
        nlinarith
      have h6 : P * (2 * δ) ≤ 2 * δ := by nlinarith
      nlinarith
    have hstep1 : r * (1 - δ) * Y0 / (W + 2 * δ) ≤ r * bt * Y / D := by
      calc r * (1 - δ) * Y0 / (W + 2 * δ) ≤ r * bt * Y / (W + 2 * δ) :=
            div_le_div_of_nonneg_right hN (by linarith)
        _ ≤ r * bt * Y / D :=
            div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg hr.le (by linarith)) hY.le) hD hDle
    refine le_trans ?_ hstep1
    have hkey : (1 - 3 * δ / ω) * (r * Y0 / W) ≤ r * (1 - δ) * Y0 / (W + 2 * δ) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hW0 (by linarith)]
      have : 0 ≤ r * Y0 := hrY0.le
      have hq : (1 - δ) * W - (1 - 3 * δ / ω) * (W + 2 * δ) ≥ 0 := by
        have h3 : 3 * δ / ω * W ≥ 3 * δ := by
          rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hω]
          nlinarith
        have h4 : 3 * δ / ω * (2 * δ) ≥ 0 := by positivity
        have h5 := mul_nonneg hδ0 (sub_nonneg.2 hW1)
        nlinarith [h3, h4, h5]
      have e : r * (1 - δ) * Y0 * W - (1 - 3 * δ / ω) * (r * Y0) * (W + 2 * δ) =
          (r * Y0) * ((1 - δ) * W - (1 - 3 * δ / ω) * (W + 2 * δ)) := by ring
      have := mul_nonneg this hq
      linarith
    have h38 : (1 - 8 * δ / ω) * (r * Y0 / W) ≤ (1 - 3 * δ / ω) * (r * Y0 / W) := by
      apply mul_le_mul_of_nonneg_right _ hF.le
      have : 3 * δ / ω ≤ 8 * δ / ω := div_le_div_of_nonneg_right (by linarith) hω.le
      linarith
    exact le_trans h38 hkey
  · -- upper bound
    obtain ⟨m, hm⟩ : ∃ m, m = 1 - δ := ⟨_, rfl⟩
    rw [← hm] at hm0 hb1 hYu
    have hm4 : 1 - 4 * δ ≤ m ^ 4 := by
      rw [hm]
      have e : (1 - δ) ^ 4 - (1 - 4 * δ) = δ ^ 2 * (6 - 4 * δ + δ ^ 2) := by ring
      have : 0 ≤ δ ^ 2 * (6 - 4 * δ + δ ^ 2) :=
        mul_nonneg (sq_nonneg _) (by linarith [sq_nonneg δ])
      linarith
    have hm1 : m ≤ 1 := by rw [hm]; linarith
    have hm0' : 0 < m := hm0
    have hYm : Y ≤ Y0 / m ^ 2 := by
      rw [le_div_iff₀ (pow_pos hm0' 2)]; linarith [mul_comm (m ^ 2) Y]
    have hN : r * bt * Y ≤ r * Y0 / m ^ 2 := by
      calc r * bt * Y ≤ r * 1 * Y := by
            apply mul_le_mul_of_nonneg_right _ hY.le
            exact mul_le_mul_of_nonneg_left hb2 hr.le
        _ = r * Y := by ring
        _ ≤ r * (Y0 / m ^ 2) := mul_le_mul_of_nonneg_left hYm hr.le
        _ = r * Y0 / m ^ 2 := by ring
    have hDge : (m ^ 4 - P) / m ^ 2 ≤ D := by
      have h1 : m ^ 2 ≤ (1 - η) ^ 2 := by
        apply pow_le_pow_left₀ hm0'.le; linarith
      have h2 : r ^ 2 * bt ^ 2 * Y ≤ r ^ 2 * (Y0 / m ^ 2) := by
        have : bt ^ 2 * Y ≤ Y := by
          have : bt ^ 2 ≤ 1 := pow_le_one₀ (by linarith) hb2
          exact mul_le_of_le_one_left hY.le this
        calc r ^ 2 * bt ^ 2 * Y = r ^ 2 * (bt ^ 2 * Y) := by ring
          _ ≤ r ^ 2 * Y := mul_le_mul_of_nonneg_left this (sq_nonneg r)
          _ ≤ r ^ 2 * (Y0 / m ^ 2) := mul_le_mul_of_nonneg_left hYm (sq_nonneg r)
      have h3 : (m ^ 4 - P) / m ^ 2 = m ^ 2 - r ^ 2 * (Y0 / m ^ 2) := by
        have e1 : (m ^ 4 - P) / m ^ 2 = m ^ 2 - P / m ^ 2 := by
          field_simp
        have e2 : P / m ^ 2 = r ^ 2 * (Y0 / m ^ 2) := by rw [hP]; ring
        rw [e1, e2]
      rw [h3, hDdef]; linarith
    have hpos : 0 < m ^ 4 - P := by linarith
    have hL : 0 < (m ^ 4 - P) / m ^ 2 := div_pos hpos (pow_pos hm0' 2)
    have hstep1 : r * bt * Y / D ≤ (r * Y0 / m ^ 2) / ((m ^ 4 - P) / m ^ 2) :=
      calc r * bt * Y / D ≤ (r * Y0 / m ^ 2) / D :=
            div_le_div_of_nonneg_right hN hD.le
        _ ≤ (r * Y0 / m ^ 2) / ((m ^ 4 - P) / m ^ 2) :=
            div_le_div_of_nonneg_left (by positivity) hL hDge
    have hstep2 : (r * Y0 / m ^ 2) / ((m ^ 4 - P) / m ^ 2) = r * Y0 / (m ^ 4 - P) := by
      field_simp
    rw [hstep2] at hstep1
    refine le_trans hstep1 ?_
    have hWd : 0 < W - 4 * δ := by linarith
    calc r * Y0 / (m ^ 4 - P) ≤ r * Y0 / (W - 4 * δ) :=
          div_le_div_of_nonneg_left hrY0.le hWd (by linarith [hW, hm4])
      _ ≤ (1 + 8 * δ / ω) * (r * Y0 / W) := by
          rw [← mul_div_assoc, div_le_div_iff₀ hWd hW0]
          have h1 : (1 + 8 * δ / ω) * (W - 4 * δ) ≥ W := by
            have : (1 + 8 * δ / ω) * (W - 4 * δ) - W = (8 * δ * W - 4 * δ * ω - 32 * δ ^ 2) / ω := by
              field_simp; ring
            have h2 : 0 ≤ (8 * δ * W - 4 * δ * ω - 32 * δ ^ 2) / ω := by
              apply div_nonneg _ hω.le
              linarith [mul_nonneg hδ0 (sub_nonneg.2 hWω), mul_nonneg hδ0 (sub_nonneg.2 hω8)]
            linarith
          have h3 := mul_le_mul_of_nonneg_left h1 hrY0.le
          linarith [h3]



set_option maxHeartbeats 2000000 in
private lemma p10x_kernel_bounds {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ : γ ≤ (1 + β ^ 2) / 96) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t') :
    (1 - 96 * γ / (1 + β ^ 2)) *
        (β ^ ℓ * (p10x_u t * p10x_u t') / (1 - (β ^ ℓ) ^ 2 * (p10x_u t * p10x_u t')) /
          (Muon.sPow β 2 * γ)) ≤
      lagKernel β γ ℓ (Muon.sPow β 2 * γ * t ^ 2) (Muon.sPow β 2 * γ * t' ^ 2) ∧
    lagKernel β γ ℓ (Muon.sPow β 2 * γ * t ^ 2) (Muon.sPow β 2 * γ * t' ^ 2) ≤
      (1 + 96 * γ / (1 + β ^ 2)) *
        (β ^ ℓ * (p10x_u t * p10x_u t') / (1 - (β ^ ℓ) ^ 2 * (p10x_u t * p10x_u t')) /
          (Muon.sPow β 2 * γ)) := by
  have hS : 0 < Muon.sPow β 2 := p10x_S_pos hβ0 hβ1
  have hs : 0 < Muon.sPow β 2 * γ * t ^ 2 := by positivity
  have hs' : 0 < Muon.sPow β 2 * γ * t' ^ 2 := by positivity
  have hY : 0 < Muon.sPow β 2 * qIso β γ γ (Muon.sPow β 2 * γ * t ^ 2) / γ ∧
      Muon.sPow β 2 * qIso β γ γ (Muon.sPow β 2 * γ * t ^ 2) / γ ≤ 2 ∧
      p10x_u t ≤ Muon.sPow β 2 * qIso β γ γ (Muon.sPow β 2 * γ * t ^ 2) / γ ∧
      (1 - 12 * γ * (1 - β ^ 2) / (1 + β ^ 2) / 2) ^ 2 *
        (Muon.sPow β 2 * qIso β γ γ (Muon.sPow β 2 * γ * t ^ 2) / γ) ≤ p10x_u t :=
    p10x_Y_sandwich hβ0 hβ1 hγ0 hγ ht
  have hYp : 0 < Muon.sPow β 2 * qIso β γ γ (Muon.sPow β 2 * γ * t' ^ 2) / γ ∧
      Muon.sPow β 2 * qIso β γ γ (Muon.sPow β 2 * γ * t' ^ 2) / γ ≤ 2 ∧
      p10x_u t' ≤ Muon.sPow β 2 * qIso β γ γ (Muon.sPow β 2 * γ * t' ^ 2) / γ ∧
      (1 - 12 * γ * (1 - β ^ 2) / (1 + β ^ 2) / 2) ^ 2 *
        (Muon.sPow β 2 * qIso β γ γ (Muon.sPow β 2 * γ * t' ^ 2) / γ) ≤ p10x_u t' :=
    p10x_Y_sandwich hβ0 hβ1 hγ0 hγ ht'
  have hd : 0 ≤ 12 * γ * (1 - β ^ 2) / (1 + β ^ 2) ∧ 12 * γ * (1 - β ^ 2) / (1 + β ^ 2) ≤ 1 / 8 ∧
      4 * (12 * γ * (1 - β ^ 2) / (1 + β ^ 2)) ≤ (1 - β ^ 2) / 2 :=
    p10_delta_bounds hβ0 hβ1 hγ0 hγ
  obtain ⟨⟨hB0, hB1⟩, ⟨hE0, hE1⟩, ⟨hX0, hX1⟩, ⟨hD0, hD1⟩⟩ := lem_app_iso_lag_i hβ0 hβ1 hγ0 hs hs' ℓ
  have hsand : β ^ ℓ * Muon.sPow β 2 * (1 - 12 * γ * (1 - β ^ 2) / (1 + β ^ 2)) ≤
        isoLagB β γ ℓ (Muon.sPow β 2 * γ * t ^ 2) (Muon.sPow β 2 * γ * t' ^ 2) ∧
      isoLagB β γ ℓ (Muon.sPow β 2 * γ * t ^ 2) (Muon.sPow β 2 * γ * t' ^ 2) ≤
        β ^ ℓ * Muon.sPow β 2 := p10_isoLagB_sandwich hβ0 hβ1 hγ0 hγ hs hs' ℓ
  have hq1 := p10_q_upper hβ0 hβ1 hγ0 (p10x_hsmall hβ0 hβ1 hγ0 hγ) hs
  have hq2 := p10_q_upper hβ0 hβ1 hγ0 (p10x_hsmall hβ0 hβ1 hγ0 hγ) hs'
  have hq10 := (p10x_q_facts hβ0 hβ1 hγ0 (p10x_hsmall hβ0 hβ1 hγ0 hγ) hs).1
  have hq20 := (p10x_q_facts hβ0 hβ1 hγ0 (p10x_hsmall hβ0 hβ1 hγ0 hγ) hs').1
  have h4 := p10_sPow4_ratio hβ0.le hβ1
  have hω : 0 < 1 - β ^ 2 := by nlinarith
  have hk : 96 * γ / (1 + β ^ 2) = 8 * (12 * γ * (1 - β ^ 2) / (1 + β ^ 2)) / (1 - β ^ 2) := by
    have : 0 < 1 + β ^ 2 := by positivity
    field_simp
    ring
  have hrβ : β ^ ℓ ≤ β := by
    calc β ^ ℓ ≤ β ^ 1 := pow_le_pow_of_le_one hβ0.le hβ1.le hℓ
      _ = β := pow_one β
  have hr0 : 0 < β ^ ℓ := pow_pos hβ0 ℓ
  have hrr : (β ^ ℓ) ^ 2 ≤ β ^ 2 := by nlinarith
  unfold lagKernel isoLagDelta isoLagX isoLagZ at *
  generalize isoLagB β γ ℓ (Muon.sPow β 2 * γ * t ^ 2) (Muon.sPow β 2 * γ * t' ^ 2) = B at *
  generalize isoLagE β γ ℓ (Muon.sPow β 2 * γ * t ^ 2) (Muon.sPow β 2 * γ * t' ^ 2) = E at *
  generalize qIso β γ γ (Muon.sPow β 2 * γ * t ^ 2) = q at *
  generalize qIso β γ γ (Muon.sPow β 2 * γ * t' ^ 2) = q' at *
  generalize Muon.sPow β 4 = S4 at *
  generalize Muon.sPow β 2 = S at *
  generalize 12 * γ * (1 - β ^ 2) / (1 + β ^ 2) = δ at *
  obtain ⟨hδ0, hδ1, hδω⟩ := hd
  obtain ⟨hY0, hY2, hu1, hu2⟩ := hY
  obtain ⟨hYp0, hYp2, hup1, hup2⟩ := hYp
  have hγ' : 0 < 1 + β ^ 2 := by positivity
  have hδdef : δ = 96 * γ / (1 + β ^ 2) * (1 - β ^ 2) / 8 := by
    rw [hk]; field_simp
  rw [hk]
  obtain ⟨hu0, hu1', -⟩ := p10x_u_spec ht.le
  obtain ⟨hup0, hup1', -⟩ := p10x_u_spec ht'.le
  obtain ⟨bt, hbtdef⟩ : ∃ bt, bt = B / (β ^ ℓ * S) := ⟨_, rfl⟩
  have hrS : 0 < β ^ ℓ * S := by positivity
  have hBbt : B = β ^ ℓ * S * bt := by rw [hbtdef]; field_simp
  have hb1 : 1 - δ ≤ bt := by
    rw [hbtdef, le_div_iff₀ hrS]; linarith [hsand.1]
  have hb2 : bt ≤ 1 := by
    rw [hbtdef, div_le_iff₀ hrS]; linarith [hsand.2]
  -- bound on X
  have hqq : q * q' ≤ (2 * γ / S) * (2 * γ / S) := mul_le_mul hq1 hq2 hq20.le (by positivity)
  have hEr : E ≤ 3 * (β ^ ℓ) ^ 2 * S4 := by
    have : β ^ (2 * ℓ) = (β ^ ℓ) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [this] at hE1; exact hE1
  have hXδ : q * q' * E / γ ≤ δ := by
    rw [div_le_iff₀ hγ0]
    have h1 : q * q' * E ≤ (2 * γ / S) * (2 * γ / S) * (3 * (β ^ ℓ) ^ 2 * S4) :=
      mul_le_mul hqq hEr hE0 (by positivity)
    have h2 : (2 * γ / S) * (2 * γ / S) * (3 * (β ^ ℓ) ^ 2 * S4) =
        12 * γ ^ 2 * (β ^ ℓ) ^ 2 * ((1 - β ^ 2) / (1 + β ^ 2)) := by
      rw [h4]; field_simp; ring
    have h3 : 12 * γ ^ 2 * (β ^ ℓ) ^ 2 * ((1 - β ^ 2) / (1 + β ^ 2)) ≤
        δ * γ := by
      rw [hδdef]
      have : (β ^ ℓ) ^ 2 ≤ 1 := by nlinarith
      have h5 : 12 * γ ^ 2 * (1 - β ^ 2) / (1 + β ^ 2) = 96 * γ / (1 + β ^ 2) * (1 - β ^ 2) / 8 * γ := by
        field_simp; ring
      have h6 : 12 * γ ^ 2 * (β ^ ℓ) ^ 2 * ((1 - β ^ 2) / (1 + β ^ 2)) ≤
          12 * γ ^ 2 * 1 * ((1 - β ^ 2) / (1 + β ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left this (by positivity)
      calc _ ≤ _ := h6
        _ = _ := by rw [← h5]; ring
    linarith
  set X := q * q' * E / γ with hXdef
  set Y := S * q / γ with hYdef
  set Yp := S * q' / γ with hYpdef
  clear_value X Y Yp
  have hZ : (√(q * q') * B / γ) ^ 2 = (β ^ ℓ) ^ 2 * bt ^ 2 * (Y * Yp) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (mul_nonneg hq10.le hq20.le), hBbt, hYdef, hYpdef]
    field_simp
  rw [hZ] at hD0 ⊢
  have hker : B * q * q' / (γ ^ 3 * ((1 - X) ^ 2 - (β ^ ℓ) ^ 2 * bt ^ 2 * (Y * Yp))) =
      (β ^ ℓ * bt * (Y * Yp) / ((1 - X) ^ 2 - (β ^ ℓ) ^ 2 * bt ^ 2 * (Y * Yp))) / (S * γ) := by
    have hne : (1 - X) ^ 2 - (β ^ ℓ) ^ 2 * bt ^ 2 * (Y * Yp) ≠ 0 := hD0.ne'
    rw [hBbt, hYdef, hYpdef]
    rw [hYdef, hYpdef] at hne
    field_simp
  rw [hker]
  have hYY : p10x_u t * p10x_u t' ≤ Y * Yp := mul_le_mul hu1 hup1 hup0.le hY0.le
  have hYu : (1 - δ) ^ 2 * (Y * Yp) ≤ p10x_u t * p10x_u t' := by
    have h1 : (1 - δ / 2) ^ 2 * Y * ((1 - δ / 2) ^ 2 * Yp) ≤ p10x_u t * p10x_u t' :=
      mul_le_mul hu2 hup2 (by positivity) hu0.le
    have h2 : (1 - δ) ^ 2 ≤ ((1 - δ / 2) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by nlinarith) 2
    have h3 : (1 - δ) ^ 2 * (Y * Yp) ≤ ((1 - δ / 2) ^ 2) ^ 2 * (Y * Yp) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    nlinarith
  have halg := p10x_alg (r := β ^ ℓ) (ω := 1 - β ^ 2) (δ := δ) (Y := Y * Yp)
    (Y0 := p10x_u t * p10x_u t') (bt := bt) (η := X) hr0 hω (by linarith) hδ0 hδ1 hδω
    (mul_pos hu0 hup0) (by nlinarith) hYY hYu hb1 hb2 hX0 hXδ hD0
  have hSγ : 0 < S * γ := by positivity
  constructor
  · calc _ = ((1 - 8 * δ / (1 - β ^ 2)) * (β ^ ℓ * (p10x_u t * p10x_u t') /
          (1 - (β ^ ℓ) ^ 2 * (p10x_u t * p10x_u t')))) / (S * γ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right halg.1 hSγ.le
  · calc _ ≤ ((1 + 8 * δ / (1 - β ^ 2)) * (β ^ ℓ * (p10x_u t * p10x_u t') /
          (1 - (β ^ ℓ) ^ 2 * (p10x_u t * p10x_u t')))) / (S * γ) :=
          div_le_div_of_nonneg_right halg.2 hSγ.le
      _ = _ := by ring

private noncomputable def p10x_w (t : ℝ) : ℝ := (Real.sqrt (t ^ 2 + 4) - t) / 2

private lemma p10x_w_sq (t : ℝ) : Real.sqrt (t ^ 2 + 4) ^ 2 = t ^ 2 + 4 :=
  Real.sq_sqrt (by positivity)

private lemma p10x_w_pos (t : ℝ) : 0 < p10x_w t := by
  have hlt : t < Real.sqrt (t ^ 2 + 4) := by
    apply Real.lt_sqrt_of_sq_lt; linarith
  unfold p10x_w; linarith

private lemma p10x_w_rel (t : ℝ) : p10x_w t ^ 2 + t * p10x_w t = 1 := by
  have hs := p10x_w_sq t
  unfold p10x_w; nlinarith [hs]

private lemma p10x_u_eq (t : ℝ) : p10x_u t = p10x_w t ^ 2 := rfl

private lemma p10x_w_deriv (t : ℝ) :
    HasDerivAt p10x_w (-(p10x_w t ^ 2) / (p10x_w t ^ 2 + 1)) t := by
  have hs := p10x_w_sq t
  have hpos : 0 < Real.sqrt (t ^ 2 + 4) := Real.sqrt_pos.2 (by positivity)
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + 4) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const 4
  have h2 := h1.sqrt (by positivity)
  have h3 := (h2.sub (hasDerivAt_id t)).div_const 2
  have hw := p10x_w_rel t
  have hwp := p10x_w_pos t
  have h3' : HasDerivAt p10x_w ((2 * t / (2 * Real.sqrt (t ^ 2 + 4)) - 1) / 2) t := h3
  refine h3'.congr_deriv ?_
  symm
  have e : Real.sqrt (t ^ 2 + 4) = 2 * p10x_w t + t := by unfold p10x_w; ring
  rw [e] at hpos ⊢
  have hw1 : p10x_w t ^ 2 + 1 = p10x_w t * (2 * p10x_w t + t) := by nlinarith
  rw [hw1]
  have hne : 2 * p10x_w t + t ≠ 0 := hpos.ne'
  have hne2 : p10x_w t ≠ 0 := hwp.ne'
  field_simp
  have key := mul_inv_cancel₀ (show p10x_w t * 2 + t ≠ 0 by linarith)
  linear_combination (-1 : ℝ) * key

private lemma p10x_w_tendsto : Filter.Tendsto p10x_w Filter.atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_inv_atTop_zero (Filter.Eventually.of_forall fun t => (p10x_w_pos t).le) ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with t ht
  have h := p10x_w_rel t
  have hw := p10x_w_pos t
  rw [← one_div, le_div_iff₀ ht]
  nlinarith [sq_nonneg (p10x_w t)]

private noncomputable def p10x_G (n : ℕ) (t : ℝ) : ℝ :=
  -(p10x_w t ^ (2 * n + 3) / (2 * (n : ℝ) + 3) + p10x_w t ^ (2 * n + 1) / (2 * (n : ℝ) + 1))

private lemma p10x_G_deriv (n : ℕ) (t : ℝ) :
    HasDerivAt (p10x_G n) (p10x_w t ^ (2 * n + 2)) t := by
  have h1 := (p10x_w_deriv t).pow (2 * n + 3)
  have h2 := (p10x_w_deriv t).pow (2 * n + 1)
  have h3 := ((h1.div_const (2 * (n : ℝ) + 3)).add (h2.div_const (2 * (n : ℝ) + 1))).neg
  refine h3.congr_deriv ?_
  have hw := p10x_w_pos t
  have hn1 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  have hn2 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hw1 : p10x_w t ^ 2 + 1 ≠ 0 := by positivity
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    show 2 * n + 3 - 1 = 2 * n + 2 from rfl, show 2 * n + 1 - 1 = 2 * n from rfl]
  field_simp
  ring

private lemma p10x_u_integral (n : ℕ) :
    IntegrableOn (fun t : ℝ => p10x_u t ^ (n + 1)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), p10x_u t ^ (n + 1) = volK n := by
  have hfun : (fun t : ℝ => p10x_u t ^ (n + 1)) = fun t => p10x_w t ^ (2 * n + 2) := by
    funext t; rw [p10x_u_eq, ← pow_mul]; ring_nf
  have hG0 : Filter.Tendsto (p10x_G n) Filter.atTop (nhds (0:ℝ)) := by
    have h := p10x_w_tendsto
    have h1 : Filter.Tendsto (fun t => p10x_w t ^ (2 * n + 3) / (2 * (n : ℝ) + 3) +
        p10x_w t ^ (2 * n + 1) / (2 * (n : ℝ) + 1)) Filter.atTop (nhds (0:ℝ)) := by
      have a := (h.pow (2 * n + 3)).div_const (2 * (n : ℝ) + 3)
      have b := (h.pow (2 * n + 1)).div_const (2 * (n : ℝ) + 1)
      simpa using a.add b
    have h2 := h1.neg
    rw [neg_zero] at h2
    exact h2
  have hderiv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (p10x_G n) (p10x_w x ^ (2 * n + 2)) x :=
    fun x _ => p10x_G_deriv n x
  have hnn : ∀ x ∈ Ioi (0:ℝ), 0 ≤ p10x_w x ^ (2 * n + 2) :=
    fun x _ => (pow_pos (p10x_w_pos x) _).le
  have hcont : ContinuousWithinAt (p10x_G n) (Ici 0) 0 :=
    (p10x_G_deriv n 0).continuousAt.continuousWithinAt
  rw [hfun]
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnn hG0, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnn hG0]
  have hw0 : p10x_w 0 = 1 := by
    unfold p10x_w; simp
    norm_num
  unfold p10x_G volK
  rw [hw0]
  simp
  ring

private noncomputable def p10x_A (c : ℝ) (n : ℕ) (x : ℝ) : ℝ := p10x_u (x / c) ^ (n + 1) / c

private lemma p10x_A_nonneg (c : ℝ) (hc : 0 < c) (n : ℕ) (x : ℝ) : 0 ≤ p10x_A c n x := by
  unfold p10x_A
  have := p10x_w_pos (x / c)
  rw [p10x_u_eq]; positivity

private lemma p10x_A_integral {c : ℝ} (hc : 0 < c) (n : ℕ) :
    IntegrableOn (p10x_A c n) (Ioi 0) ∧ ∫ x in Ioi (0 : ℝ), p10x_A c n x = volK n := by
  obtain ⟨hI, hV⟩ := p10x_u_integral n
  have hb : 0 < c⁻¹ := inv_pos.2 hc
  have hfun : p10x_A c n = fun x => c⁻¹ * (fun t : ℝ => p10x_u t ^ (n + 1)) (c⁻¹ * x) := by
    funext x; unfold p10x_A; simp only [div_eq_mul_inv, mul_comm x c⁻¹]; ring
  rw [hfun]
  constructor
  · apply Integrable.const_mul
    have := (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => p10x_u t ^ (n + 1)) 0 hb).2
      (by simpa using hI)
    exact this
  · rw [integral_const_mul, integral_comp_mul_left_Ioi (fun t : ℝ => p10x_u t ^ (n + 1)) 0 hb]
    simp only [mul_zero, smul_eq_mul, inv_inv]
    rw [hV]
    field_simp

private noncomputable def p10x_Phi (r c : ℝ) (p : ℝ × ℝ) : ℝ :=
  r * (p10x_u (p.1 / c) * p10x_u (p.2 / c)) /
    (1 - r ^ 2 * (p10x_u (p.1 / c) * p10x_u (p.2 / c))) / c ^ 2

private lemma p10x_u_cont : Continuous p10x_u := by
  unfold p10x_u; fun_prop

private lemma p10x_volK_le (n : ℕ) : volK n ≤ 2 := by
  unfold volK
  have h1 : 1 / (2 * (n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have h2 : 1 / (2 * (n : ℝ) + 3) ≤ 1 := by
    rw [div_le_one (by positivity)]; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  linarith

private lemma p10x_volK_nonneg (n : ℕ) : 0 ≤ volK n := by
  unfold volK; positivity

private lemma p10x_lead {r c : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hc : 0 < c) :
    IntegrableOn (p10x_Phi r c) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), p10x_Phi r c p = Real.pi ^ 2 / 4 * volOmega r := by
  set R : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) with hR
  have hRm : MeasurableSet R := measurableSet_Ioi.prod measurableSet_Ioi
  have hμ : (volume : Measure (ℝ × ℝ)).restrict R =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hAi : ∀ n, Integrable (p10x_A c n) (volume.restrict (Ioi (0 : ℝ))) :=
    fun n => (p10x_A_integral hc n).1
  set F : ℕ → ℝ × ℝ → ℝ := fun n p => r ^ (2 * n + 1) * (p10x_A c n p.1 * p10x_A c n p.2) with hF
  have hFi : ∀ n, Integrable (F n) ((volume : Measure (ℝ × ℝ)).restrict R) := by
    intro n
    rw [hμ]
    exact (Integrable.mul_prod (hAi n) (hAi n)).const_mul _
  have hFint : ∀ n, ∫ p, F n p ∂((volume : Measure (ℝ × ℝ)).restrict R) =
      r ^ (2 * n + 1) * volK n ^ 2 := by
    intro n
    rw [hμ, integral_const_mul]
    have := integral_prod_mul (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume.restrict (Ioi (0 : ℝ)))
      (p10x_A c n) (p10x_A c n)
    rw [this, (p10x_A_integral hc n).2]
    ring
  have hFnn : ∀ n p, 0 ≤ F n p := fun n p => by
    simp only [hF]
    have := p10x_A_nonneg c hc n p.1
    have := p10x_A_nonneg c hc n p.2
    positivity
  have hsumm : Summable (fun n => ∫ p, ‖F n p‖ ∂((volume : Measure (ℝ × ℝ)).restrict R)) := by
    have : (fun n => ∫ p, ‖F n p‖ ∂((volume : Measure (ℝ × ℝ)).restrict R)) =
        fun n : ℕ => r ^ (2 * n + 1) * volK n ^ 2 := by
      funext n
      rw [← hFint n]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (hFnn n p)])
    rw [this]
    refine Summable.of_nonneg_of_le (fun n => by have := p10x_volK_nonneg n; positivity)
      (fun n => ?_) ((summable_geometric_of_lt_one (by positivity : 0 ≤ r ^ 2)
        (by nlinarith)).mul_left (4 * r))
    have h2 := p10x_volK_le n
    have h0 := p10x_volK_nonneg n
    have hsq : volK n ^ 2 ≤ 4 := by nlinarith
    calc r ^ (2 * n + 1) * volK n ^ 2 ≤ r ^ (2 * n + 1) * 4 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 4 * r * (r ^ 2) ^ n := by rw [pow_succ, pow_mul]; ring
  have hHas := hasSum_integral_of_summable_integral_norm hFi hsumm
  have hpt : ∀ p ∈ R, ∑' n, F n p = p10x_Phi r c p := by
    intro p hp
    have ht : 0 < p.1 / c := div_pos hp.1 hc
    have ht' : 0 < p.2 / c := div_pos hp.2 hc
    obtain ⟨hu0, hu1, -⟩ := p10x_u_spec ht.le
    obtain ⟨hv0, hv1, -⟩ := p10x_u_spec ht'.le
    set Y0 := p10x_u (p.1 / c) * p10x_u (p.2 / c) with hY0
    have hY0pos : 0 < Y0 := mul_pos hu0 hv0
    have hY01 : Y0 ≤ 1 := by nlinarith
    have hq1 : r ^ 2 * Y0 < 1 := by nlinarith
    have hterm : ∀ n, F n p = (r * Y0 / c ^ 2) * (r ^ 2 * Y0) ^ n := by
      intro n
      simp only [hF, p10x_A, hY0]
      simp only [mul_pow, ← pow_mul]
      field_simp
      ring
    simp_rw [hterm]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hq1]
    unfold p10x_Phi
    simp only [hY0]
    field_simp
  have hint_eq : ∫ p in R, p10x_Phi r c p = ∫ p, ∑' n, F n p ∂((volume : Measure (ℝ × ℝ)).restrict R) :=
    (setIntegral_congr_fun hRm (fun p hp => (hpt p hp).symm))
  -- integrability of Phi
  have hPhi_meas : Measurable (p10x_Phi r c) := by
    unfold p10x_Phi
    have := p10x_u_cont.measurable
    fun_prop
  have hPhi_int : IntegrableOn (p10x_Phi r c) R := by
    have hbd : Integrable (fun p : ℝ × ℝ => r / (1 - r ^ 2) * (p10x_A c 0 p.1 * p10x_A c 0 p.2))
        ((volume : Measure (ℝ × ℝ)).restrict R) := by
      rw [hμ]
      exact (Integrable.mul_prod (hAi 0) (hAi 0)).const_mul _
    refine Integrable.mono' hbd hPhi_meas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hRm] with p hp
    have ht : 0 < p.1 / c := div_pos hp.1 hc
    have ht' : 0 < p.2 / c := div_pos hp.2 hc
    obtain ⟨hu0, hu1, -⟩ := p10x_u_spec ht.le
    obtain ⟨hv0, hv1, -⟩ := p10x_u_spec ht'.le
    have hY0pos : 0 < p10x_u (p.1 / c) * p10x_u (p.2 / c) := mul_pos hu0 hv0
    have hY01 : p10x_u (p.1 / c) * p10x_u (p.2 / c) ≤ 1 := by nlinarith
    have hden : 0 < 1 - r ^ 2 * (p10x_u (p.1 / c) * p10x_u (p.2 / c)) := by nlinarith
    have hden2 : 1 - r ^ 2 ≤ 1 - r ^ 2 * (p10x_u (p.1 / c) * p10x_u (p.2 / c)) := by nlinarith
    have hnn : 0 ≤ p10x_Phi r c p := by unfold p10x_Phi; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    unfold p10x_Phi p10x_A
    have h1r : 0 < 1 - r ^ 2 := by nlinarith
    calc r * (p10x_u (p.1 / c) * p10x_u (p.2 / c)) /
          (1 - r ^ 2 * (p10x_u (p.1 / c) * p10x_u (p.2 / c))) / c ^ 2
        ≤ r * (p10x_u (p.1 / c) * p10x_u (p.2 / c)) / (1 - r ^ 2) / c ^ 2 := by
          gcongr
      _ = _ := by simp only [pow_one, zero_add]; field_simp
  refine ⟨hPhi_int, ?_⟩
  rw [hint_eq, ← hHas.tsum_eq]
  have : ∑' n, ∫ p, F n p ∂((volume : Measure (ℝ × ℝ)).restrict R) =
      ∑' n : ℕ, volK n ^ 2 * r ^ (2 * n + 1) := by
    refine tsum_congr fun n => ?_
    rw [hFint n]; ring
  rw [this]
  unfold volOmega
  have hpi : Real.pi ^ 2 ≠ 0 := by positivity
  field_simp

private lemma p10x_meas_tsum {α : Type*} [MeasurableSpace α] {f : ℕ → α → ℝ}
    (hm : ∀ j, Measurable (f j)) (hnn : ∀ j a, 0 ≤ f j a) :
    Measurable (fun a => ∑' j, f j a) := by
  have h : (fun a => ∑' j, f j a) = fun a => (∑' j, ENNReal.ofReal (f j a)).toReal := by
    funext a
    rw [ENNReal.tsum_toReal_eq (fun j => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun j => (ENNReal.toReal_ofReal (hnn j a)).symm
  rw [h]
  exact (Measurable.ennreal_tsum fun j => (hm j).ennreal_ofReal).ennreal_toReal

private lemma p10x_meas_gen (num : ℕ → ℝ → ℝ) (hnum : ∀ j, Measurable (num j))
    (hnum0 : ∀ j g, 0 ≤ num j g) (wsq : ℕ → ℝ) (hw : ∀ j, 0 ≤ wsq j) (c2 : ℝ) (hc2 : 0 ≤ c2) :
    Measurable (fun p : ℝ × ℝ => ∑' j : ℕ, ∫ g, num j g /
      ((1 + max p.1 0 * wsq j * g ^ 2) * (1 + c2 * max p.2 0 * wsq j * g ^ 2))
        ∂(ProbabilityTheory.gaussianReal 0 1)) := by
  apply p10x_meas_tsum
  · intro j
    have hm : Measurable (fun z : (ℝ × ℝ) × ℝ => num j z.2 /
        ((1 + max z.1.1 0 * wsq j * z.2 ^ 2) * (1 + c2 * max z.1.2 0 * wsq j * z.2 ^ 2))) := by
      have := hnum j
      fun_prop
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := ProbabilityTheory.gaussianReal 0 1)).measurable
  · intro j p
    refine integral_nonneg fun g => ?_
    have := hnum0 j g
    have := hw j
    positivity

private lemma p10x_meas_K {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (ℓ : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => lagKernel β γ ℓ (p.1 ^ 2) (p.2 ^ 2))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))) := by
  have hRm : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hcomp := lem_app_iso_comparison_i (p10_link hβ0 hβ1) hγ0 hγ0
  -- measurable version of x ↦ q(x²)
  have hc : ContinuousOn (fun x : ℝ => qIso β γ γ (x ^ 2)) (Ioi 0) := by
    refine ContinuousOn.comp (g := isoRoot (Muon.DetEquiv.rW (Muon.emaW β)) γ γ) hcomp.2.2.2.2.1
      (by fun_prop) ?_
    intro x hx
    have : (0 : ℝ) < x := hx
    exact Set.mem_Ioi.mpr (by positivity)
  set Yf : ℝ → ℝ := Set.piecewise (Ioi 0) (fun x : ℝ => qIso β γ γ (x ^ 2)) (fun _ => 0) with hYf
  have hYm : Measurable Yf :=
    ContinuousOn.measurable_piecewise hc continuousOn_const measurableSet_Ioi
  have hYeq : ∀ x : ℝ, 0 < x → Yf x = qIso β γ γ (x ^ 2) := fun x hx => by
    rw [hYf, Set.piecewise_eq_of_mem _ _ _ (Set.mem_Ioi.mpr hx)]
  have hq0 : ∀ x : ℝ, 0 < x → 0 ≤ qIso β γ γ (x ^ 2) := fun x hx =>
    (hcomp.2.2.2.1 (x ^ 2) (by positivity)).1.1
  set w : ℕ → ℝ := fun j => Muon.emaW β j with hw
  have hB := p10x_meas_gen (fun j g => β ^ ℓ * Muon.emaW β j ^ 2 * g ^ 2)
    (fun j => by fun_prop) (fun j g => by
      have : 0 ≤ β ^ ℓ := pow_nonneg hβ0.le ℓ
      positivity) (fun j => Muon.emaW β j ^ 2) (fun j => sq_nonneg _) (β ^ (2 * ℓ))
    (pow_nonneg hβ0.le _)
  have hE := p10x_meas_gen (fun j g => β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * g ^ 4)
    (fun j => by fun_prop) (fun j g => by
      have : 0 ≤ β ^ (2 * ℓ) := pow_nonneg hβ0.le _
      positivity) (fun j => Muon.emaW β j ^ 2) (fun j => sq_nonneg _) (β ^ (2 * ℓ))
    (pow_nonneg hβ0.le _)
  set Bf : ℝ × ℝ → ℝ := fun p => ∑' j : ℕ, ∫ g, β ^ ℓ * Muon.emaW β j ^ 2 * g ^ 2 /
      ((1 + max p.1 0 * Muon.emaW β j ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * max p.2 0 * Muon.emaW β j ^ 2 * g ^ 2))
        ∂(ProbabilityTheory.gaussianReal 0 1) with hBf
  set Ef : ℝ × ℝ → ℝ := fun p => ∑' j : ℕ, ∫ g, β ^ (2 * ℓ) * Muon.emaW β j ^ 4 * g ^ 4 /
      ((1 + max p.1 0 * Muon.emaW β j ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * max p.2 0 * Muon.emaW β j ^ 2 * g ^ 2))
        ∂(ProbabilityTheory.gaussianReal 0 1) with hEf
  have hBm : Measurable Bf := hB
  have hEm : Measurable Ef := hE
  set Kf : ℝ × ℝ → ℝ := fun p =>
    Bf (Yf p.1, Yf p.2) * Yf p.1 * Yf p.2 /
      (γ ^ 3 * ((1 - Yf p.1 * Yf p.2 * Ef (Yf p.1, Yf p.2) / γ) ^ 2 -
        (Real.sqrt (Yf p.1 * Yf p.2) * Bf (Yf p.1, Yf p.2) / γ) ^ 2)) with hKf
  have hKm : Measurable Kf := by
    have h1 : Measurable fun p : ℝ × ℝ => (Yf p.1, Yf p.2) :=
      (hYm.comp measurable_fst).prodMk (hYm.comp measurable_snd)
    have h2 : Measurable fun p : ℝ × ℝ => Bf (Yf p.1, Yf p.2) := hBm.comp h1
    have h3 : Measurable fun p : ℝ × ℝ => Ef (Yf p.1, Yf p.2) := hEm.comp h1
    have h4 : Measurable fun p : ℝ × ℝ => Yf p.1 := hYm.comp measurable_fst
    have h5 : Measurable fun p : ℝ × ℝ => Yf p.2 := hYm.comp measurable_snd
    simp only [hKf]
    fun_prop
  refine hKm.aestronglyMeasurable.congr ?_
  refine (ae_restrict_iff' hRm).2 (Filter.Eventually.of_forall fun p hp => ?_)
  obtain ⟨hp1, hp2⟩ := hp
  have hp1' : 0 < p.1 := hp1
  have hp2' : 0 < p.2 := hp2
  simp only [hKf, hBf, hEf]
  rw [hYeq _ hp1', hYeq _ hp2', max_eq_left (hq0 _ hp1'), max_eq_left (hq0 _ hp2')]
  rfl

private lemma p10x_main {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ : γ ≤ (1 + β ^ 2) / 96) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    |lagCoeff β γ 0 ℓ - volOmega (β ^ ℓ)| ≤ 96 * γ / (1 + β ^ 2) * volOmega (β ^ ℓ) := by
  set R : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) with hR
  have hRm : MeasurableSet R := measurableSet_Ioi.prod measurableSet_Ioi
  have hS := p10x_S_pos hβ0 hβ1
  set S := Muon.sPow β 2 with hSdef
  have hSγ : 0 < S * γ := by positivity
  set c := Real.sqrt (S * γ) with hcdef
  have hc : 0 < c := Real.sqrt_pos.2 hSγ
  have hc2 : c ^ 2 = S * γ := Real.sq_sqrt hSγ.le
  set r := β ^ ℓ with hrdef
  have hr0 : 0 < r := pow_pos hβ0 ℓ
  have hr1 : r < 1 := pow_lt_one₀ hβ0.le hβ1 (by omega)
  set k := 96 * γ / (1 + β ^ 2) with hkdef
  have hd : 0 < 1 + β ^ 2 := by positivity
  have hk0 : 0 ≤ k := by positivity
  have hk1 : k ≤ 1 := by
    rw [hkdef, div_le_one hd]
    linarith [(le_div_iff₀ (by norm_num : (0:ℝ) < 96)).1 hγ]
  obtain ⟨hΦi, hΦv⟩ := p10x_lead hr0 hr1 hc
  have hΦnn : ∀ p ∈ R, 0 ≤ p10x_Phi r c p := by
    intro p hp
    have ht : 0 < p.1 / c := div_pos hp.1 hc
    have ht' : 0 < p.2 / c := div_pos hp.2 hc
    obtain ⟨hu0, hu1, -⟩ := p10x_u_spec ht.le
    obtain ⟨hv0, hv1, -⟩ := p10x_u_spec ht'.le
    have hY0 : 0 < p10x_u (p.1 / c) * p10x_u (p.2 / c) := mul_pos hu0 hv0
    have hY01 : p10x_u (p.1 / c) * p10x_u (p.2 / c) ≤ 1 := by nlinarith
    have hden : 0 < 1 - r ^ 2 * (p10x_u (p.1 / c) * p10x_u (p.2 / c)) := by nlinarith
    unfold p10x_Phi; positivity
  have hpt : ∀ p ∈ R, (1 - k) * p10x_Phi r c p ≤ lagKernel β γ ℓ (p.1 ^ 2) (p.2 ^ 2) ∧
      lagKernel β γ ℓ (p.1 ^ 2) (p.2 ^ 2) ≤ (1 + k) * p10x_Phi r c p := by
    intro p hp
    have ht : 0 < p.1 / c := div_pos hp.1 hc
    have ht' : 0 < p.2 / c := div_pos hp.2 hc
    have h := p10x_kernel_bounds hβ0 hβ1 hγ0 hγ hℓ ht ht'
    have e1 : S * γ * (p.1 / c) ^ 2 = p.1 ^ 2 := by
      rw [div_pow, hc2]; field_simp
    have e2 : S * γ * (p.2 / c) ^ 2 = p.2 ^ 2 := by
      rw [div_pow, hc2]; field_simp
    rw [e1, e2] at h
    have e3 : r * (p10x_u (p.1 / c) * p10x_u (p.2 / c)) /
        (1 - r ^ 2 * (p10x_u (p.1 / c) * p10x_u (p.2 / c))) / (S * γ) = p10x_Phi r c p := by
      unfold p10x_Phi; rw [hc2]
    rw [e3] at h
    exact h
  have hKm := p10x_meas_K hβ0 hβ1 hγ0 ℓ
  have hKi : IntegrableOn (fun p : ℝ × ℝ => lagKernel β γ ℓ (p.1 ^ 2) (p.2 ^ 2)) R := by
    refine Integrable.mono' (hΦi.const_mul (1 + k)) hKm ?_
    filter_upwards [ae_restrict_mem hRm] with p hp
    obtain ⟨h1, h2⟩ := hpt p hp
    have hn := hΦnn p hp
    have h3 : 0 ≤ lagKernel β γ ℓ (p.1 ^ 2) (p.2 ^ 2) := by
      have : 0 ≤ (1 - k) * p10x_Phi r c p := mul_nonneg (by linarith) hn
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg h3]
    exact h2
  have hlo : (1 - k) * ∫ p in R, p10x_Phi r c p ≤
      ∫ p in R, lagKernel β γ ℓ (p.1 ^ 2) (p.2 ^ 2) := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hΦi.const_mul (1 - k)) hKi hRm fun p hp => (hpt p hp).1
  have hhi : ∫ p in R, lagKernel β γ ℓ (p.1 ^ 2) (p.2 ^ 2) ≤
      (1 + k) * ∫ p in R, p10x_Phi r c p := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hKi (hΦi.const_mul (1 + k)) hRm fun p hp => (hpt p hp).2
  have hcoef : lagCoeff β γ 0 ℓ = 4 / Real.pi ^ 2 * ∫ p in R, lagKernel β γ ℓ (p.1 ^ 2) (p.2 ^ 2) := by
    unfold lagCoeff
    congr 1
    have hprod : (∫ p in R, lagKernel β γ ℓ (p.1 ^ 2) (p.2 ^ 2)) =
        ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), lagKernel β γ ℓ (x ^ 2) (y ^ 2) := by
      rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
      exact setIntegral_prod (fun p : ℝ × ℝ => lagKernel β γ ℓ (p.1 ^ 2) (p.2 ^ 2))
        (by simpa only [IntegrableOn, ← Measure.volume_eq_prod, R] using hKi)
    rw [hprod]
    simp only [zero_add]
  rw [hΦv] at hlo hhi
  have hpi : 0 < Real.pi ^ 2 := by positivity
  rw [hcoef, abs_le]
  have key1 : (1 - k) * volOmega r ≤ 4 / Real.pi ^ 2 * ∫ p in R, lagKernel β γ ℓ (p.1 ^ 2) (p.2 ^ 2) := by
    have := mul_le_mul_of_nonneg_left hlo (by positivity : (0:ℝ) ≤ 4 / Real.pi ^ 2)
    calc (1 - k) * volOmega r = 4 / Real.pi ^ 2 * ((1 - k) * (Real.pi ^ 2 / 4 * volOmega r)) := by
          field_simp
      _ ≤ _ := this
  have key2 : 4 / Real.pi ^ 2 * ∫ p in R, lagKernel β γ ℓ (p.1 ^ 2) (p.2 ^ 2) ≤ (1 + k) * volOmega r := by
    have := mul_le_mul_of_nonneg_left hhi (by positivity : (0:ℝ) ≤ 4 / Real.pi ^ 2)
    calc _ ≤ _ := this
      _ = (1 + k) * volOmega r := by field_simp
  constructor <;> linarith


theorem thm_app_iso_small_volatility_i {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ : γ ≤ (1 + β ^ 2) / 96) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    |lagCoeff β γ 0 ℓ - volOmega (β ^ ℓ)| ≤ 96 * γ / (1 + β ^ 2) * volOmega (β ^ ℓ) :=
  p10x_main hβ0 hβ1 hγ0 hγ hℓ

/-- `thm:app-iso-vol-rate`, snapshot `cr-2026-10-23`, `section.tex` l.2784–2789.

\begin{theorem}[Lag sum at zero ridge]\label{thm:app-iso-vol-rate}
Let $\bmom\in(0,1)$, $\Nin=\Nout=N$ and $\gamma=N/B\ge\gamma^\circ_\bmom$. Then
\[
-\mathsf K^-_\bmom\le\sum_{\ell\ge1}\overline C_{1,\ell}(0)-\frac\gamma4\le\mathsf K^+_\bmom .
\]
\end{theorem}
-/
theorem thm_app_iso_vol_rate {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : isoGammaCirc β ≤ γ) :
    ∃ S : ℝ, HasSum (fun ℓ : ℕ => lagCoeff β γ 0 (ℓ + 1)) S ∧
      -isoKminus β ≤ S - γ / 4 ∧ S - γ / 4 ≤ isoKplus β := by
  obtain ⟨hK0, hK1, hK2, hcp, hE⟩ := pF2C_K_nonneg hβ0 hβ1
  have hC' : 0 < isoC' β := by
    have h2 : 0 < 1 - β ^ 2 := by nlinarith
    unfold isoC'; positivity
  have hγ1 : 1 ≤ γ := by unfold isoGammaCirc at hγ; linarith
  have hγ0 : 0 < γ := by linarith
  have hM1 := pF2_M1_nonneg
  obtain ⟨hL1, hL2⟩ := pF2_L_nonneg hβ0 hβ1
  have h1 := pF2_step1 hβ0 hβ1 hγ
  have hU := pF2_I_upper hβ0 hβ1 hγ
  have hLo := pF2_I_lower hβ0 hβ1 hγ
  set I : ENNReal := ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
    ENNReal.ofReal (pF2Psi β γ (isoPairMap (isoQlevel β η) w)) ∂isoNuStar with hI
  set a : ℕ → ℝ := fun ℓ => lagCoeff β γ 0 (ℓ + 1) with ha
  have hnn : ∀ ℓ, 0 ≤ a ℓ := fun ℓ => p10_lag_nonneg hβ0 hβ1 hγ0 le_rfl (ℓ + 1)
  set R : ℝ := γ * (isoEbar β * isoM1 / 2 + isoK0 β + isoK1 β * isoCpl β
        + 2 * isoK2 β * isoCpl β ^ 2) with hR
  set Lb : ℝ := isoK1 β * isoLbar1 β + 2 * isoK2 β * isoLbar2 β with hLb
  have hR0 : 0 ≤ R := by
    rw [hR]
    have : 0 ≤ isoEbar β * isoM1 / 2 := by positivity
    have : 0 ≤ isoK1 β * isoCpl β := mul_nonneg hK1 hcp
    have : 0 ≤ isoK2 β * isoCpl β ^ 2 := mul_nonneg hK2 (sq_nonneg _)
    positivity
  have hLb0 : 0 ≤ Lb := by
    rw [hLb]
    have := mul_nonneg hK1 hL1
    have := mul_nonneg hK2 hL2
    linarith
  have hU0 : 0 ≤ γ ^ 2 / 4 + R + Lb := by positivity
  have hfin : ∑' ℓ : ℕ, ENNReal.ofReal (a ℓ) ≠ ⊤ := by
    rw [h1]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hU)
  have hsum : Summable a := by
    have := ENNReal.summable_toReal hfin
    simpa [ENNReal.toReal_ofReal (hnn _)] using this
  have hS : ENNReal.ofReal (∑' ℓ, a ℓ) = ENNReal.ofReal (1 / γ) * I := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum, h1]
  refine ⟨∑' ℓ, a ℓ, hsum.hasSum, ?_, ?_⟩
  · -- lower bound
    set S := ∑' ℓ, a ℓ with hSdef
    have hS0 : 0 ≤ S := tsum_nonneg hnn
    have hK : 0 ≤ isoKminus β := by
      unfold isoKminus
      have : 0 ≤ isoM1 + 1 := by linarith
      positivity
    have h2 := mul_le_mul' (le_refl (ENNReal.ofReal (1 / γ))) hLo
    rw [mul_add, ← hS, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add hS0 (by positivity)] at h2
    have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
    have e1 : 1 / γ * (γ ^ 2 / 4) = γ / 4 := by field_simp
    have e2 : 1 / γ * (γ * (5 / 2 * (isoEbar β * (isoM1 + 1)))) = isoKminus β := by
      unfold isoKminus; field_simp
    rw [e1, e2] at h3
    linarith
  · -- upper bound
    set S := ∑' ℓ, a ℓ with hSdef
    have hS0 : 0 ≤ S := tsum_nonneg hnn
    have h2 := mul_le_mul' (le_refl (ENNReal.ofReal (1 / γ))) hU
    rw [← hS, ← ENNReal.ofReal_mul (by positivity)] at h2
    have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
    have e1 : 1 / γ * (γ ^ 2 / 4 + R + Lb) = γ / 4 + R / γ + Lb / γ := by
      rw [hR]; field_simp
    have e2 : Lb / γ ≤ Lb := div_le_self hLb0 hγ1
    have e3 : R / γ = isoEbar β * isoM1 / 2 + isoK0 β + isoK1 β * isoCpl β
        + 2 * isoK2 β * isoCpl β ^ 2 := by rw [hR]; field_simp
    have e4 : isoKplus β = isoEbar β * isoM1 / 2 + isoK0 β + isoK1 β * isoCpl β
        + 2 * isoK2 β * isoCpl β ^ 2 + Lb := by
      unfold isoKplus; rw [hLb]; ring
    rw [e1] at h3
    linarith

/-- Single-lag support implies the support used in the lag-sum estimates. -/
private lemma pF3_region {β γ y z : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hℓ : 1 ≤ ℓ) (hz : 0 < z)
    (hreg : y < isoQlevel β γ ∧ z / β ^ (2 * ℓ) < isoQlevel β γ) :
    y < isoQlevel β γ ∧ z / β ^ (2 * 1) < isoQlevel β γ := by
  refine ⟨hreg.1, lt_of_le_of_lt ?_ hreg.2⟩
  exact div_le_div_of_nonneg_left hz.le (pow_pos hβ0 _)
    (pow_le_pow_of_le_one hβ0.le hβ1.le (by omega))

/-- Nonnegativity of the unsummed integrand in the layer representation. -/
private lemma pF3_nonneg {β γ y z : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hℓ : 1 ≤ ℓ) (hy : 0 < y) (hz : 0 < z) :
    0 ≤ (if y < isoQlevel β γ ∧ z / β ^ (2 * ℓ) < isoQlevel β γ
      then isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * ℓ)) /
        (γ ^ 2 * isoDeltaHat β γ y z) else 0) := by
  split_ifs with hreg
  · have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
    have hz0 : 0 < z / β ^ (2 * ℓ) := div_pos hz (pow_pos hβ0 _)
    have hr := (pF2_lt_Q_iff hβ0 hβ1 hγ0 hz0).1 hreg.2
    obtain ⟨hAy, -, hΔ, -⟩ := pF2B_region hβ0 hβ1 hγ hy hz
      (pF3_region hβ0 hβ1 hℓ hz hreg).1
      (pF3_region hβ0 hβ1 hℓ hz hreg).2
    have hJy := (pF2B_J_bounds (γ := γ) hβ0 hβ1 hy).1
    have hJz := (pF2B_J_bounds (γ := γ) hβ0 hβ1 hz0).1
    have hAz : 0 < isoResid β γ (z / β ^ (2 * ℓ)) := by
      unfold isoResid; linarith
    exact div_nonneg (mul_nonneg (hAy.le.trans hJy) (hAz.le.trans hJz))
      (by positivity)
  · exact le_rfl

/-- The one shifted weight is bounded by the positive part of its level deficit. -/
private lemma pF3_weight_upper {β γ z : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hz : 0 < z) :
    isoWeightJ β γ (z / β ^ (2 * ℓ)) ≤
      max (isoResid β γ z + (isoCpl β + max 0 (-isoN β z)) - (ℓ : ℝ)) 0
        + 2 * isoEbar β := by
  have hz0 : 0 < z / β ^ (2 * ℓ) := div_pos hz (pow_pos hβ0 _)
  have hJ := (pF2B_J_bounds (γ := γ) hβ0 hβ1 hz0).2
  have hsh := lem_app_iso_shifts_ii hβ0 hβ1 z hz ℓ
  have hr := lem_app_iso_shifts_iii hβ0 hβ1 z hz
  have hmax := le_max_left
    (isoResid β γ z + (isoCpl β + max 0 (-isoN β z)) - (ℓ : ℝ)) 0
  unfold isoResid isoCpl at *
  linarith

/-- Lower kernel comparison for a single lag, before layer averaging. -/
private lemma pF3_lower {β γ y z : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hy : 0 < y) (hz : 0 < z) (hAy : 0 < isoResid β γ y)
    (hAz : (ℓ : ℝ) < isoResid β γ z) :
    isoResid β γ y * (isoResid β γ z - (ℓ : ℝ)) /
        (isoAvee β γ y z + isoEbar β) ^ 2 ≤
      (if y < isoQlevel β γ ∧ z / β ^ (2 * ℓ) < isoQlevel β γ
        then isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * ℓ)) /
          (γ ^ 2 * isoDeltaHat β γ y z) else 0) := by
  have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
  have hz0 : 0 < z / β ^ (2 * ℓ) := div_pos hz (pow_pos hβ0 _)
  have hsh := (lem_app_iso_shifts_i hβ0 hβ1 z hz ℓ).2.2
  have hAz0 : 0 < isoResid β γ z := lt_of_le_of_lt (Nat.cast_nonneg ℓ) hAz
  have hAzl : isoResid β γ z - (ℓ : ℝ) ≤
      isoResid β γ (z / β ^ (2 * ℓ)) := by
    unfold isoResid; linarith
  have hyQ : y < isoQlevel β γ := by
    rw [pF2_lt_Q_iff hβ0 hβ1 hγ0 hy]
    unfold isoResid at hAy; linarith
  have hzQ : z / β ^ (2 * ℓ) < isoQlevel β γ := by
    rw [pF2_lt_Q_iff hβ0 hβ1 hγ0 hz0]
    unfold isoResid at hAzl hAz; linarith
  rw [if_pos ⟨hyQ, hzQ⟩]
  have hJ1 := (pF2B_J_bounds (γ := γ) hβ0 hβ1 hy).1
  have hJ2 := (pF2B_J_bounds (γ := γ) hβ0 hβ1 hz0).1
  obtain ⟨-, -, hm, hd, hu⟩ :=
    lem_app_iso_kernel_bounds_v hβ0 hβ1 hγ0 hy hz hAy hAz0
  have hAv0 : 0 < isoAvee β γ y z :=
    hAy.trans_le (le_max_left _ _)
  have hD : 0 < γ ^ 2 * isoDeltaHat β γ y z := by
    have := mul_pos hAv0 hm
    linarith
  have hnum := mul_le_mul hJ1 (hAzl.trans hJ2)
    (sub_nonneg.mpr hAz.le) (hAy.le.trans hJ1)
  calc
    _ ≤ (isoResid β γ y * (isoResid β γ z - (ℓ : ℝ))) /
        (γ ^ 2 * isoDeltaHat β γ y z) :=
      div_le_div_of_nonneg_left (mul_nonneg hAy.le (sub_nonneg.mpr hAz.le)) hD hu
    _ ≤ _ := div_le_div_of_nonneg_right hnum hD.le

/-- The rational lower comparison in Step 3 of the profile proof. -/
private lemma pF3_alg_lower (x u l Ay Azl D : ℝ)
    (hu : 0 ≤ u) (hl : 0 ≤ l) (hx : l + 4 * u < x)
    (hAy : x - u ≤ Ay) (hAz : x - l - u ≤ Azl)
    (hD0 : 0 < D) (hD : D ≤ x + u) :
    1 - l / x - 4 * u / x ≤ Ay * Azl / D ^ 2 := by
  have hx0 : 0 < x := by linarith
  have h1 : 0 ≤ x - u := by linarith
  have h2 : 0 ≤ x - l - u := by linarith
  have hnum : (x - u) * (x - l - u) ≤ Ay * Azl :=
    mul_le_mul hAy hAz h2 (h1.trans hAy)
  have hsq : D ^ 2 ≤ (x + u) ^ 2 := pow_le_pow_left₀ hD0.le hD 2
  have hpos : 0 ≤ 1 - l / x - 4 * u / x := by
    rw [sub_sub, ← add_div, sub_nonneg, div_le_one hx0]
    linarith
  have halg : (1 - l / x - 4 * u / x) * (x + u) ^ 2 ≤
      (x - u) * (x - l - u) := by
    apply (mul_le_mul_iff_left₀ hx0).mp
    field_simp
    nlinarith [mul_nonneg hl (mul_nonneg hu hx0.le),
      mul_nonneg hl (sq_nonneg u), mul_nonneg hx0.le (sq_nonneg u),
      pow_nonneg hu 3]
  rw [le_div_iff₀ (sq_pos_of_pos hD0)]
  exact (mul_le_mul_of_nonneg_left hsq hpos).trans (halg.trans hnum)

/-- Uniform positivity and the two defining upper bounds for the decay rate. -/
private lemma pF3_decay_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 < isoDecay β ∧ isoDecay β * isoEbar β ≤ 1 / 8 ∧
      isoDecay β ≤ Real.log (1 / β) / 8 := by
  have hE : 0 < isoEbar β := zero_lt_one.trans_le (le_max_left _ _)
  have hlog : 0 < Real.log (1 / β) :=
    Real.log_pos (one_lt_one_div hβ0 hβ1)
  have hδ : 0 < isoDecay β := by unfold isoDecay; positivity
  refine ⟨hδ, ?_, min_le_right _ _⟩
  have h := min_le_left (1 / (8 * isoEbar β)) (Real.log (1 / β) / 8)
  change isoDecay β ≤ 1 / (8 * isoEbar β) at h
  have hm := mul_le_mul_of_nonneg_right h hE.le
  have heq : 1 / (8 * isoEbar β) * isoEbar β = (1 : ℝ) / 8 := by
    field_simp
  rwa [heq] at hm

/-- The polynomial loss in the low-level variable is absorbed by one exponential. -/
private lemma pF3_exp_absorb {δ c n : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hn : 0 ≤ n) :
    (1 + c + n) * Real.exp (δ * n) ≤
      (1 + c + 1 / δ) * Real.exp (2 * δ * n) := by
  have he : 1 ≤ Real.exp (δ * n) := Real.one_le_exp (mul_nonneg hδ.le hn)
  have hnexp : n ≤ 1 / δ * Real.exp (δ * n) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hδ]
    nlinarith [Real.add_one_le_exp (δ * n)]
  have hbase : 1 + c + n ≤ (1 + c + 1 / δ) * Real.exp (δ * n) := by
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 + c by linarith)
    nlinarith
  have := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (δ * n)).le
  calc
    _ ≤ (1 + c + 1 / δ) * Real.exp (δ * n) * Real.exp (δ * n) := this
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- Monotonicity of the positive part of the profile as its level increases. -/
private lemma pF3_profile_mono {l A B : ℝ} (hl : 0 ≤ l) (hA : 0 < A)
    (hAB : A ≤ B) : max (1 - l / A) 0 ≤ max (1 - l / B) 0 := by
  apply max_le_max _ le_rfl
  have := div_le_div_of_nonneg_left hl hA hAB
  linarith

/-- The elementary perturbation bound for the profile. -/
private lemma pF3_profile_shift {l x d : ℝ} (hl : 0 ≤ l) (hx : 0 < x) (hd : 0 ≤ d) :
    max (1 - l / (x + d)) 0 ≤ max (1 - l / x) 0 + min 1 (d / x) := by
  have hxd : 0 < x + d := by linarith
  have hmx : 0 ≤ max (1 - l / x) 0 := le_max_right _ _
  have hmin : 0 ≤ min 1 (d / x) := le_min zero_le_one (div_nonneg hd hx.le)
  by_cases hlarge : x ≤ d
  · rw [min_eq_left ((le_div_iff₀ hx).2 (by linarith))]
    apply max_le
    · have : 0 ≤ l / (x + d) := div_nonneg hl hxd.le
      linarith
    · linarith
  · have hsmall : d / x ≤ 1 := (div_le_one hx).2 (le_of_not_ge hlarge)
    rw [min_eq_right hsmall]
    by_cases hlx : l ≤ x
    · rw [show max (1 - l / x) 0 = 1 - l / x from
        max_eq_left (sub_nonneg.2 ((div_le_one hx).2 hlx))]
      apply max_le
      · have hdiff : l / x - l / (x + d) ≤ d / x := by
          rw [sub_le_iff_le_add]
          apply (div_le_iff₀ hx).2
          field_simp
          nlinarith [mul_nonneg hd (sub_nonneg.2 hlx)]
        linarith
      · have := div_le_one hx |>.2 hlx
        have := div_nonneg hd hx.le
        linarith
    · have hxl : x ≤ l := (le_of_not_ge hlx)
      rw [show max (1 - l / x) 0 = 0 from
        max_eq_right (sub_nonpos.2 ((one_le_div hx).2 hxl))]
      apply max_le
      · apply (mul_le_mul_iff_right₀ (mul_pos hx hxd)).mp
        field_simp
        nlinarith [mul_nonneg hxd.le (sub_nonneg.2 hxl), sq_nonneg d]
      · positivity

/-- Pointwise lower profile bound, including the boundary layer. -/
private lemma pF3_lower_core {β γ x τ y z : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hℓ : 1 ≤ ℓ) (hx : 0 < x) (hτ : 0 ≤ τ) (hy : 0 < y) (hz : 0 < z)
    (hyA : |isoResid β γ y - x| ≤ isoEbar β * τ)
    (hzA : |isoResid β γ z - x| ≤ isoEbar β * τ) :
    max (1 - (ℓ : ℝ) / x) 0 - min 1 (4 * (isoEbar β * (τ + 1)) / x) ≤
      (if y < isoQlevel β γ ∧ z / β ^ (2 * ℓ) < isoQlevel β γ
        then isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * ℓ)) /
          (γ ^ 2 * isoDeltaHat β γ y z) else 0) := by
  have hE : 1 ≤ isoEbar β := le_max_left _ _
  have he0 : 0 ≤ isoEbar β := by linarith
  have hl0 : 0 ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
  set u := isoEbar β * (τ + 1) with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hAy : x - u ≤ isoResid β γ y := by
    linarith [(abs_le.mp hyA).1]
  have hAz : x - (ℓ : ℝ) - u ≤ isoResid β γ z - (ℓ : ℝ) := by
    linarith [(abs_le.mp hzA).1]
  have hAv : isoAvee β γ y z + isoEbar β ≤ x + u := by
    have hm : isoAvee β γ y z ≤ x + isoEbar β * τ :=
      max_le (by linarith [(abs_le.mp hyA).2]) (by linarith [(abs_le.mp hzA).2])
    linarith
  by_cases hfar : (ℓ : ℝ) + 4 * u < x
  · have hAy0 : 0 < isoResid β γ y := by linarith
    have hAzl : (ℓ : ℝ) < isoResid β γ z := by linarith
    have hD0 : 0 < isoAvee β γ y z + isoEbar β := by
      have : isoResid β γ y ≤ isoAvee β γ y z := le_max_left _ _
      linarith
    have hraw := pF3_lower hβ0 hβ1 hγ hy hz hAy0 hAzl
    have halg := pF3_alg_lower x u (ℓ : ℝ) (isoResid β γ y)
      (isoResid β γ z - (ℓ : ℝ)) (isoAvee β γ y z + isoEbar β)
      hu0 hl0 hfar hAy hAz hD0 hAv
    have hp : 0 ≤ 1 - (ℓ : ℝ) / x := by
      rw [sub_nonneg, div_le_one hx]; linarith
    have hm : 4 * u / x ≤ 1 := by rw [div_le_one hx]; linarith
    rw [max_eq_left hp, min_eq_right hm]
    exact halg.trans hraw
  · have hnear : x - (ℓ : ℝ) ≤ 4 * u := by linarith
    have hp1 : max (1 - (ℓ : ℝ) / x) 0 ≤ 1 := by
      apply max_le _ zero_le_one
      have := div_nonneg hl0 hx.le
      linarith
    have hp2 : max (1 - (ℓ : ℝ) / x) 0 ≤ 4 * u / x := by
      apply max_le
      · apply (le_div_iff₀ hx).2
        field_simp
        linarith
      · positivity
    have hp := le_min hp1 hp2
    exact (sub_nonpos.2 hp).trans (pF3_nonneg hβ0 hβ1 hγ hℓ hy hz)

/-- The denominator lower bound gives a uniform bound with linear low-level loss. -/
private lemma pF3_alg_decay (e Φ A E Jy Jz d : ℝ)
    (he : 1 ≤ e) (hΦ : 0 < Φ) (hA : Φ ≤ A) (hE : 0 ≤ E)
    (hJy0 : 0 ≤ Jy) (hJy : Jy ≤ A + 2 * e)
    (hJz0 : 0 ≤ Jz) (hJz : Jz ≤ A + E + 2 * e)
    (hd : A * max (A - e) (A / 2) ≤ d) :
    Jy * Jz / d ≤
      (4 + (4 + 8 * e) / Φ + (8 * e + 32 * e ^ 2) / Φ ^ 2) * (1 + E) := by
  have hA0 : 0 < A := hΦ.trans_le hA
  have he0 : 0 ≤ e := by linarith
  have hd0 : 0 < d := by
    have hm := mul_le_mul_of_nonneg_left (le_max_right (A - e) (A / 2)) hA0.le
    nlinarith
  have hda : A ^ 2 / 2 ≤ d := by
    have hm := mul_le_mul_of_nonneg_left (le_max_right (A - e) (A / 2)) hA0.le
    nlinarith
  have h1 : Jy / A ≤ 1 + 2 * e / Φ := by
    calc Jy / A ≤ (A + 2 * e) / A := div_le_div_of_nonneg_right hJy hA0.le
      _ = 1 + 2 * e / A := by rw [add_div, div_self hA0.ne']
      _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_left
        (show 0 ≤ 2 * e by positivity) hΦ hA)
  have h2 : Jz / A ≤ 1 + (E + 2 * e) / Φ := by
    calc Jz / A ≤ (A + E + 2 * e) / A := div_le_div_of_nonneg_right hJz hA0.le
      _ = 1 + (E + 2 * e) / A := by field_simp <;> ring
      _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_left
        (show 0 ≤ E + 2 * e by positivity) hΦ hA)
  have h3 : Jy * Jz / d ≤ 2 * ((Jy / A) * (Jz / A)) := by
    calc Jy * Jz / d ≤ Jy * Jz / (A ^ 2 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hJy0 hJz0) (by positivity) hda
      _ = _ := by field_simp <;> ring
  have h4 : 2 * ((Jy / A) * (Jz / A)) ≤
      2 * ((1 + 2 * e / Φ) * (1 + (E + 2 * e) / Φ)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul h1 h2 (div_nonneg hJz0 hA0.le) (by positivity)
  refine (h3.trans h4).trans ?_
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hΦ)).mp
  field_simp
  nlinarith [mul_nonneg he0 hΦ.le, mul_nonneg hE hΦ.le,
    mul_nonneg hE (sq_nonneg e), mul_nonneg hE (mul_nonneg he0 hΦ.le),
    mul_nonneg hE he0, sq_nonneg Φ, sq_nonneg e]

/-- Uniform single-lag bound before exponential absorption of the low levels. -/
private lemma pF3_decay_core {β γ y z : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hℓ : 1 ≤ ℓ) (hy : 0 < y) (hz : 0 < z) :
    (if y < isoQlevel β γ ∧ z / β ^ (2 * ℓ) < isoQlevel β γ
      then isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * ℓ)) /
        (γ ^ 2 * isoDeltaHat β γ y z) else 0) ≤
      isoK5 β * (1 + isoCpl β + max 0 (-isoN β z)) := by
  have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
  have he : 1 ≤ isoEbar β := le_max_left _ _
  have he0 : 0 ≤ isoEbar β := by linarith
  have hΦ : 0 < isoPhi 1 := (lem_app_iso_gaussian_ii.2.2 1 one_pos).1
  have hcp : 0 ≤ isoCpl β := (pF2C_K_nonneg hβ0 hβ1).2.2.2.1
  have hn : 0 ≤ max 0 (-isoN β z) := le_max_left _ _
  have hK5 : 0 ≤ isoK5 β := by unfold isoK5; positivity
  split_ifs with hreg
  · have hreg1 := pF3_region hβ0 hβ1 hℓ hz hreg
    obtain ⟨hAy, hAz, hΔ, -⟩ :=
      pF2B_region hβ0 hβ1 hγ hy hz hreg1.1 hreg1.2
    have hz0 : 0 < z / β ^ (2 * ℓ) := div_pos hz (pow_pos hβ0 _)
    have hr := (pF2_lt_Q_iff hβ0 hβ1 hγ0 hz0).1 hreg.2
    have hAzl : 0 < isoResid β γ (z / β ^ (2 * ℓ)) := by
      unfold isoResid; linarith
    have hJy := pF2B_J_bounds (γ := γ) hβ0 hβ1 hy
    have hJz := pF2B_J_bounds (γ := γ) hβ0 hβ1 hz0
    have hAvy : isoResid β γ y ≤ isoAvee β γ y z := le_max_left _ _
    have hAvz : isoResid β γ z ≤ isoAvee β γ y z := le_max_right _ _
    have hAv0 : 0 < isoAvee β γ y z := hAy.trans_le hAvy
    have hE : 0 ≤ isoCpl β + max 0 (-isoN β z) := add_nonneg hcp hn
    have hw := pF3_weight_upper (γ := γ) (ℓ := ℓ) hβ0 hβ1 hz
    have hm : max (isoResid β γ z + (isoCpl β + max 0 (-isoN β z)) - (ℓ : ℝ)) 0 ≤
        isoAvee β γ y z + (isoCpl β + max 0 (-isoN β z)) := by
      apply max_le
      · linarith [show (0 : ℝ) ≤ (ℓ : ℝ) from Nat.cast_nonneg ℓ]
      · linarith
    have hd := (lem_app_iso_kernel_bounds_v hβ0 hβ1 hγ0 hy hz hAy (hΦ.trans hAz)).2.2.2.1
    have halg := pF3_alg_decay (isoEbar β) (isoPhi 1) (isoAvee β γ y z)
      (isoCpl β + max 0 (-isoN β z)) (isoWeightJ β γ y)
      (isoWeightJ β γ (z / β ^ (2 * ℓ))) (γ ^ 2 * isoDeltaHat β γ y z)
      he hΦ (hAz.le.trans hAvz) hE (hAy.le.trans hJy.1) (by linarith)
      (hAzl.le.trans hJz.1) (by linarith) hd
    simpa only [isoK5, add_assoc] using halg
  · exact mul_nonneg hK5 (by linarith)

/-- Active lag support bounds the lag by the level deficit plus the low-level loss. -/
private lemma pF3_support_level {β γ y z : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hz : 0 < z)
    (hreg : y < isoQlevel β γ ∧ z / β ^ (2 * ℓ) < isoQlevel β γ) :
    (ℓ : ℝ) < isoAvee β γ y z + isoCpl β + max 0 (-isoN β z) := by
  have hz0 : 0 < z / β ^ (2 * ℓ) := div_pos hz (pow_pos hβ0 _)
  have hr := (pF2_lt_Q_iff hβ0 hβ1 hγ hz0).1 hreg.2
  have hsh := lem_app_iso_shifts_ii hβ0 hβ1 z hz ℓ
  have hcount := lem_app_iso_shifts_iii hβ0 hβ1 z hz
  have hAz : isoResid β γ z ≤ isoAvee β γ y z := le_max_right _ _
  unfold isoResid isoCpl at *
  linarith

/-- A measurable nonnegative representative of the single-lag integrand. -/
private lemma pF3_meas {β γ : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ) (hℓ : 1 ≤ ℓ) :
    ∃ F : ℝ × ℝ → ℝ, Measurable F ∧ (∀ p, 0 ≤ F p) ∧
      ∀ y z : ℝ, 0 < y → 0 < z → F (y, z) =
        (if y < isoQlevel β γ ∧ z / β ^ (2 * ℓ) < isoQlevel β γ
          then isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * ℓ)) /
            (γ ^ 2 * isoDeltaHat β γ y z) else 0) := by
  have hlink := p10_link hβ0 hβ1
  let R : ℝ → ℝ := fun q => Muon.DetEquiv.rW (Muon.emaW β) (max q 0)
  have hRc : Continuous R :=
    ContinuousOn.comp_continuous hlink.1 (continuous_id.max continuous_const)
      (fun q => le_max_right q 0)
  have hRe : ∀ q : ℝ, 0 ≤ q → R q = Muon.DetEquiv.rW (Muon.emaW β) q :=
    fun q hq => by simp only [R, max_eq_left hq]
  let G : ℝ × ℝ → ℝ := fun p =>
    if p.1 < isoQlevel β γ ∧ p.2 / β ^ (2 * ℓ) < isoQlevel β γ then
      pF2D_J R γ p.1 * pF2D_J R γ (p.2 / β ^ (2 * ℓ)) /
        (γ ^ 2 * pF2D_Δ R γ p) else 0
  have hGm : Measurable G := by
    have hJ := pF2D_J_meas hRc.measurable γ
    have hD := pF2D_Δ_meas hRc.measurable γ
    apply Measurable.ite
      ((measurableSet_lt measurable_fst measurable_const).inter
        (measurableSet_lt (measurable_snd.div_const _) measurable_const))
    · exact ((hJ.comp measurable_fst).mul (hJ.comp (measurable_snd.div_const _))).div
        (measurable_const.mul hD)
    · exact measurable_const
  refine ⟨fun p => max (G p) 0, hGm.max measurable_const,
    fun p => le_max_right _ _, ?_⟩
  intro y z hy hz
  have hz0 : 0 < z / β ^ (2 * ℓ) := div_pos hz (pow_pos hβ0 _)
  have heq : G (y, z) =
      (if y < isoQlevel β γ ∧ z / β ^ (2 * ℓ) < isoQlevel β γ
        then isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * ℓ)) /
          (γ ^ 2 * isoDeltaHat β γ y z) else 0) := by
    dsimp only [G]
    rw [pF2D_J_eq hRe hy, pF2D_J_eq hRe hz0, pF2D_Δ_eq hRe hy hz]
  change max (G (y, z)) 0 = _
  rw [heq]
  exact max_eq_left (pF3_nonneg hβ0 hβ1 hγ hℓ hy hz)

/-- Single-lag layer averaging, with its original ENNReal normalization. -/
private lemma pF3_rep {β γ : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ) (hℓ : 1 ≤ ℓ) :
    ENNReal.ofReal (lagCoeff β γ 0 ℓ) = ENNReal.ofReal (1 / γ) *
      ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal
          (if (isoPairMap (isoQlevel β η) w).1 < isoQlevel β γ ∧
              (isoPairMap (isoQlevel β η) w).2 / β ^ (2 * ℓ) < isoQlevel β γ then
            isoWeightJ β γ (isoPairMap (isoQlevel β η) w).1 *
              isoWeightJ β γ ((isoPairMap (isoQlevel β η) w).2 / β ^ (2 * ℓ)) /
              (γ ^ 2 * isoDeltaHat β γ (isoPairMap (isoQlevel β η) w).1
                (isoPairMap (isoQlevel β η) w).2) else 0) ∂isoNuStar := by
  have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
  obtain ⟨F, hFm, hF0, hFe⟩ := pF3_meas hβ0 hβ1 hγ hℓ
  have havg := (lem_app_iso_averaging_i hβ0 hβ1).2 F hFm hF0
  have hrep := (prop_app_iso_vol_representation hβ0 hβ1 hγ0 (le_refl (0 : ℝ)) hℓ).2
  simp only [isoQpsi, lt_self_iff_false, if_false, pF2E_isoUlev_zero, mul_one] at hrep
  have heq : (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), ENNReal.ofReal
      ((if p.1 < isoQlevel β γ ∧ p.2 / β ^ (2 * ℓ) < isoQlevel β γ then (1 : ℝ) else 0) *
        (isoDivDiff β p.1 p.2 * isoWeightJ β γ p.1 *
          isoWeightJ β γ (p.2 / β ^ (2 * ℓ)) / isoDeltaHat β γ p.1 p.2))) =
      ENNReal.ofReal (γ ^ 2) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal (isoDivDiff β p.1 p.2 * F p) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioi) (fun p hp => ?_)
    have hpEq := hFe p.1 p.2 hp.1 hp.2
    simp only [Prod.mk.eta] at hpEq
    rw [← ENNReal.ofReal_mul (sq_nonneg γ), hpEq]
    congr 1
    split_ifs with hreg
    · have hΔ := (prop_app_iso_vol_representation hβ0 hβ1 hγ0
        (le_refl (0 : ℝ)) hℓ).1 p.1 p.2 hp.1 hp.2
        (by simpa [isoQpsi] using hreg.1) (by simpa [isoQpsi] using hreg.2)
      field_simp
    · simp
  rw [heq] at hrep
  have hcoef : ENNReal.ofReal (1 / (Real.pi ^ 2 * γ ^ 3)) * ENNReal.ofReal (γ ^ 2) =
      ENNReal.ofReal (1 / γ) * ENNReal.ofReal (1 / Real.pi ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [← mul_assoc, hcoef, mul_assoc, havg] at hrep
  rw [hrep]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi (fun η hη => ?_)
  refine lintegral_congr (fun w => ?_)
  have hs := (pF2_Q_spec hβ0 hβ1 hη).1
  have hpos : 0 < (isoPairMap (isoQlevel β η) w).1 ∧
      0 < (isoPairMap (isoQlevel β η) w).2 := by
    unfold isoPairMap
    split_ifs <;> exact ⟨by positivity, by positivity⟩
  have := hFe _ _ hpos.1 hpos.2
  simpa only [Prod.mk.eta] using congrArg ENNReal.ofReal this

/-- The support indicator yields the exponential single-lag estimate. -/
private lemma pF3_decay_exp {β γ y z : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hℓ : 1 ≤ ℓ) (hy : 0 < y) (hz : 0 < z) :
    (if y < isoQlevel β γ ∧ z / β ^ (2 * ℓ) < isoQlevel β γ
      then isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * ℓ)) /
        (γ ^ 2 * isoDeltaHat β γ y z) else 0) ≤
      isoK5 β * (1 + isoCpl β + 1 / isoDecay β) *
        Real.exp (isoDecay β * isoCpl β) *
        Real.exp (-(isoDecay β) * ((ℓ : ℝ) - γ)) *
        Real.exp (2 * isoDecay β * max 0 (-isoN β z)) := by
  have hδ := (pF3_decay_bounds hβ0 hβ1).1
  have hcp := (pF2C_K_nonneg hβ0 hβ1).2.2.2.1
  have hn : 0 ≤ max 0 (-isoN β z) := le_max_left _ _
  have he0 : 0 ≤ isoEbar β := zero_le_one.trans (le_max_left _ _)
  have hΦ : 0 < isoPhi 1 := (lem_app_iso_gaussian_ii.2.2 1 one_pos).1
  have hK : 0 ≤ isoK5 β := by unfold isoK5; positivity
  have hbound := pF3_decay_core hβ0 hβ1 hγ hℓ hy hz
  split_ifs with hreg
  · rw [if_pos hreg] at hbound
    have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
    have hsup := pF3_support_level hβ0 hβ1 hγ0 hz hreg
    have hr0 : ∀ q : ℝ, 0 < q → 0 ≤ Muon.DetEquiv.rW (Muon.emaW β) q := by
      intro q hq
      have h := (p10_link hβ0 hβ1).2.1.monotoneOn
        (mem_Ici.2 (le_refl (0 : ℝ))) (mem_Ici.2 hq.le) hq.le
      simpa [Muon.DetEquiv.rW] using h
    have hAv : isoAvee β γ y z ≤ γ :=
      max_le (by unfold isoResid; linarith [hr0 y hy])
        (by unfold isoResid; linarith [hr0 z hz])
    have hexp : 1 ≤ Real.exp (isoDecay β *
        (γ + isoCpl β + max 0 (-isoN β z) - (ℓ : ℝ))) := by
      apply Real.one_le_exp
      apply mul_nonneg hδ.le
      linarith
    have hm := mul_le_mul_of_nonneg_left hexp
      (mul_nonneg hK (show 0 ≤ 1 + isoCpl β + max 0 (-isoN β z) by linarith))
    have hfac : Real.exp (isoDecay β *
        (γ + isoCpl β + max 0 (-isoN β z) - (ℓ : ℝ))) =
        Real.exp (isoDecay β * isoCpl β) *
          Real.exp (-(isoDecay β) * ((ℓ : ℝ) - γ)) *
          Real.exp (isoDecay β * max 0 (-isoN β z)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hpos : 0 ≤ isoK5 β * Real.exp (isoDecay β * isoCpl β) *
        Real.exp (-(isoDecay β) * ((ℓ : ℝ) - γ)) := by positivity
    have ha' := mul_le_mul_of_nonneg_left (pF3_exp_absorb hδ hcp hn) hpos
    rw [hfac] at hm
    nlinarith only [hbound, hm, ha']
  · positivity

/-- A lower bound for the logarithmic participation level. -/
private lemma pF3_sigma_lower {β η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hη : 0 < η) :
    Real.log (η * (1 - β ^ 2)) ≤
      Real.log ((1 - β) ^ 2 * isoQlevel β η) := by
  obtain ⟨hs, hr⟩ := pF2_Q_spec hβ0 hβ1 hη
  have hFw := (lem_app_iso_weights_v hβ0.le hβ1).1 _ hs.le
  rw [Muon.sPow_two hβ0.le hβ1] at hFw
  have h : η ≤ isoQlevel β η * ((1 - β) / (1 + β)) := by
    have hh := mul_le_mul_of_nonneg_left hFw hs.le
    change Muon.DetEquiv.rW (Muon.emaW β) (isoQlevel β η) ≤ _ at hh
    rwa [hr] at hh
  have hb : 0 < 1 - β ^ 2 := by nlinarith
  apply Real.log_le_log (mul_pos hη hb)
  calc
    η * (1 - β ^ 2) ≤
        isoQlevel β η * ((1 - β) / (1 + β)) * (1 - β ^ 2) :=
      mul_le_mul_of_nonneg_right h hb.le
    _ = (1 - β) ^ 2 * isoQlevel β η := by field_simp <;> ring

/-- The exponential low-level loss of a sampled pair separates into level and pair factors. -/
private lemma pF3_pair_N {β η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hη : 0 < η) (b : Bool) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    2 * isoDecay β * max 0 (-isoN β (isoPairMap (isoQlevel β η) (b, a, c)).2) ≤
      (a + c) / 8 + max 0 (-Real.log (η * (1 - β ^ 2))) / 8 := by
  have hs := (pF2_Q_spec hβ0 hβ1 hη).1
  have hL : 0 < Real.log (1 / β) := Real.log_pos (one_lt_one_div hβ0 hβ1)
  have hb : 0 < (1 - β) ^ 2 := by
    have : 0 < 1 - β := by linarith
    positivity
  have hτ : 0 ≤ a + c := by linarith
  have hp := (lem_app_iso_averaging_iii (γ := η) hβ0 hβ1
    (isoQlevel β η) hs b a c ha hc).2.2.2.2
  set z := (isoPairMap (isoQlevel β η) (b, a, c)).2 with hz
  have hz0 : 0 < z := lt_of_lt_of_le (by positivity) hp
  have hlog : Real.log (η * (1 - β ^ 2)) - (a + c) ≤
      Real.log ((1 - β) ^ 2 * z) := by
    have hh := Real.log_le_log (mul_pos hb (by positivity : 0 < isoQlevel β η *
        Real.exp (-(a + c)))) (mul_le_mul_of_nonneg_left hp hb.le)
    rw [show (1 - β) ^ 2 * (isoQlevel β η * Real.exp (-(a + c))) =
      ((1 - β) ^ 2 * isoQlevel β η) * Real.exp (-(a + c)) by ring,
      Real.log_mul (mul_pos hb hs).ne' (Real.exp_pos _).ne', Real.log_exp] at hh
    linarith [pF3_sigma_lower hβ0 hβ1 hη]
  have hn : 0 ≤ max 0 (-isoN β z) := le_max_left _ _
  have hm : 0 ≤ max 0 (-Real.log (η * (1 - β ^ 2))) := le_max_left _ _
  have hN : 2 * Real.log (1 / β) * max 0 (-isoN β z) ≤
      a + c + max 0 (-Real.log (η * (1 - β ^ 2))) := by
    rcases max_choice 0 (-isoN β z) with h | h
    · rw [h]; nlinarith
    · rw [h, isoN]
      have heq : 2 * Real.log (1 / β) *
          -(Real.log ((1 - β) ^ 2 * z) / (2 * Real.log (1 / β))) =
          -Real.log ((1 - β) ^ 2 * z) := by field_simp
      rw [heq]
      linarith [le_max_right 0 (-Real.log (η * (1 - β ^ 2)))]
  have hδ := (pF3_decay_bounds hβ0 hβ1).2.2
  have hmul := mul_le_mul_of_nonneg_right hδ hn
  change 2 * isoDecay β * max 0 (-isoN β z) ≤ _
  nlinarith

/-- Positivity of the closed exponential moment. -/
private lemma pF3_Me_pos : 0 < isoMe := by
  have hs : Summable (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).comp_injective
      (show Function.Injective (fun k : ℕ => 2 * k + 1) by
        intro i j hij
        dsimp at hij
        omega)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h
  have hm : Antitone (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2) := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity)
    have hh : (i : ℝ) ≤ j := by exact_mod_cast hij
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    nlinarith
  have hh := hm.alternating_series_le_tendsto hs.tendsto_alternating_series_tsum 0
  have hcat : 0 ≤ isoCatalan := by
    simpa [isoCatalan, div_eq_mul_inv] using hh
  unfold isoMe
  positivity

/-- Integrability of the stated exponential pair moment. -/
private lemma pF3_exp_integrable :
    Integrable (fun w : Bool × ℝ × ℝ => Real.exp ((w.2.1 + w.2.2) / 4)) isoNuStar := by
  by_contra h
  have hh := lem_app_iso_averaging_ii.2.2.2
  rw [integral_undef h] at hh
  have hm := pF3_Me_pos
  change 0 < 2 + 16 * isoCatalan / Real.pi ^ 2 at hm
  linarith

/-- The ENNReal form of the exponential pair moment. -/
private lemma pF3_exp_lintegral :
    (∫⁻ w, ENNReal.ofReal (Real.exp ((w.2.1 + w.2.2) / 4)) ∂isoNuStar) =
      ENNReal.ofReal isoMe := by
  rw [← ofReal_integral_eq_lintegral_ofReal pF3_exp_integrable
    (Filter.Eventually.of_forall fun w => (Real.exp_pos _).le)]
  exact congrArg ENNReal.ofReal lem_app_iso_averaging_ii.2.2.2

/-- Integral of the power used to bound the exponential low-level loss. -/
private lemma pF3_power_integral {c : ℝ} (hc : 0 < c) :
    (∫⁻ η in Ioo (0 : ℝ) (1 / c), ENNReal.ofReal ((c * η) ^ (-(1 : ℝ) / 8))) =
      ENNReal.ofReal (8 / (7 * c)) := by
  have hr : (-1 : ℝ) < -(1 : ℝ) / 8 := by norm_num
  have hi : IntervalIntegrable (fun η : ℝ => (c * η) ^ (-(1 : ℝ) / 8)) volume
      0 (1 / c) := by
    simpa only [zero_div] using
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hr).comp_mul_left (c := c)
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hi.1.mono_set Ioo_subset_Ioc_self)
    ((ae_restrict_iff' measurableSet_Ioo).2
      (Filter.Eventually.of_forall fun η hη => Real.rpow_nonneg (mul_nonneg hc.le hη.1.le) _))]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by positivity)]
  have hh := intervalIntegral.mul_integral_comp_mul_left
    (f := fun x : ℝ => x ^ (-(1 : ℝ) / 8)) (a := 0) (b := 1 / c) c
  have heq : c * (1 / c) = 1 := by field_simp
  rw [mul_zero, heq, integral_rpow (Or.inl hr)] at hh
  norm_num at hh
  apply (mul_left_cancel₀ hc.ne')
  calc c * (∫ η in (0 : ℝ)..1 / c, (c * η) ^ (-(1 : ℝ) / 8)) = 8 / 7 := by simpa only [one_div, neg_div] using hh
    _ = c * (8 / (7 * c)) := by field_simp

/-- The exponential boundary layer is controlled by an integrable power. -/
private lemma pF3_exp_power {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ENNReal.ofReal (Real.exp (max 0 (-Real.log (η * c)) / 8)) ≤
      1 + (if η < 1 / c then ENNReal.ofReal ((c * η) ^ (-(1 : ℝ) / 8)) else 0) := by
  by_cases hh : η < 1 / c
  · rw [if_pos hh]
    have hlt : η * c < 1 := (lt_div_iff₀ hc).1 hh
    have hlog : Real.log (η * c) ≤ 0 := Real.log_nonpos (by positivity) hlt.le
    have heq : Real.exp (max 0 (-Real.log (η * c)) / 8) =
        (c * η) ^ (-(1 : ℝ) / 8) := by
      rw [max_eq_right (by linarith), Real.rpow_def_of_pos (mul_pos hc hη), mul_comm c η]
      congr 1
      ring
    rw [heq]
    exact le_add_self
  · rw [if_neg hh, add_zero]
    have hge : 1 ≤ η * c := by
      have : 1 / c ≤ η := le_of_not_gt hh
      exact (div_le_iff₀ hc).1 this
    have hlog : 0 ≤ Real.log (η * c) := Real.log_nonneg hge
    rw [max_eq_left (by linarith), zero_div, Real.exp_zero, ENNReal.ofReal_one]

/-- Integrated exponential boundary-layer estimate. -/
private lemma pF3_exp_level_integral {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ) :
    (∫⁻ η in Ioo (0 : ℝ) γ,
      ENNReal.ofReal (Real.exp (max 0 (-Real.log (η * c)) / 8))) ≤
        ENNReal.ofReal (γ + 8 / (7 * c)) := by
  have hb : (∫⁻ η in Ioo (0 : ℝ) γ,
      (if η < 1 / c then ENNReal.ofReal ((c * η) ^ (-(1 : ℝ) / 8)) else 0)) ≤
      ENNReal.ofReal (8 / (7 * c)) := by
    calc
      _ ≤ ∫⁻ η in Ioi (0 : ℝ),
          (if η < 1 / c then ENNReal.ofReal ((c * η) ^ (-(1 : ℝ) / 8)) else 0) :=
        lintegral_mono_set Ioo_subset_Ioi_self
      _ = ∫⁻ η in Ioo (0 : ℝ) (1 / c),
          ENNReal.ofReal ((c * η) ^ (-(1 : ℝ) / 8)) := by
        have heq : (fun η : ℝ => if η < 1 / c then
            ENNReal.ofReal ((c * η) ^ (-(1 : ℝ) / 8)) else 0) =
            (Iio (1 / c)).indicator
              (fun η => ENNReal.ofReal ((c * η) ^ (-(1 : ℝ) / 8))) := by
          rfl
        rw [heq, lintegral_indicator measurableSet_Iio,
          Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, Set.Ioi_inter_Iio]
      _ = _ := pF3_power_integral hc
  calc
    _ ≤ ∫⁻ η in Ioo (0 : ℝ) γ,
        (1 + if η < 1 / c then ENNReal.ofReal ((c * η) ^ (-(1 : ℝ) / 8)) else 0) :=
      setLIntegral_mono' measurableSet_Ioo (fun η hη => pF3_exp_power hc hη.1)
    _ = ENNReal.ofReal γ + ∫⁻ η in Ioo (0 : ℝ) γ,
        (if η < 1 / c then ENNReal.ofReal ((c * η) ^ (-(1 : ℝ) / 8)) else 0) := by
      rw [lintegral_add_left measurable_const, setLIntegral_one, Real.volume_Ioo, sub_zero]
    _ ≤ ENNReal.ofReal γ + ENNReal.ofReal (8 / (7 * c)) := add_le_add le_rfl hb
    _ = _ := (ENNReal.ofReal_add hγ.le (by positivity)).symm

/-- The layer support vanishes at and above `γ`. -/
private lemma pF3_pair_outside {β γ η : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hη : 0 < η) (hηγ : γ ≤ η)
    (b : Bool) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    ¬ ((isoPairMap (isoQlevel β η) (b, a, c)).1 < isoQlevel β γ ∧
      (isoPairMap (isoQlevel β η) (b, a, c)).2 / β ^ (2 * ℓ) < isoQlevel β γ) := by
  have hs := (pF2_Q_spec hβ0 hβ1 hη).1
  have hQ : isoQlevel β γ ≤ isoQlevel β η := pF2_Q_mono hβ0 hβ1 hηγ
  have hlarge : isoQlevel β η ≤ isoQlevel β η * Real.exp a := by
    have hh := Real.one_le_exp ha
    nlinarith
  have hpow : β ^ (2 * ℓ) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hzz : ∀ z : ℝ, 0 < z → z ≤ z / β ^ (2 * ℓ) := by
    intro z hz
    rw [le_div_iff₀ (pow_pos hβ0 _)]
    nlinarith
  cases b <;> simp only [isoPairMap, Bool.false_eq_true, ite_false, ite_true]
  · intro hreg
    have hz := hzz (isoQlevel β η * Real.exp a) (by positivity)
    linarith [hreg.2]
  · intro hreg
    linarith [hreg.1]

/-- The separated pointwise decay bound on a layer. -/
private lemma pF3_decay_pair {β γ η : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hℓ : 1 ≤ ℓ) (hη : 0 < η) (b : Bool) {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (if (isoPairMap (isoQlevel β η) (b, a, c)).1 < isoQlevel β γ ∧
        (isoPairMap (isoQlevel β η) (b, a, c)).2 / β ^ (2 * ℓ) < isoQlevel β γ then
      isoWeightJ β γ (isoPairMap (isoQlevel β η) (b, a, c)).1 *
        isoWeightJ β γ ((isoPairMap (isoQlevel β η) (b, a, c)).2 / β ^ (2 * ℓ)) /
        (γ ^ 2 * isoDeltaHat β γ (isoPairMap (isoQlevel β η) (b, a, c)).1
          (isoPairMap (isoQlevel β η) (b, a, c)).2) else 0) ≤
      if η < γ then
        (isoK5 β * (1 + isoCpl β + 1 / isoDecay β) *
          Real.exp (isoDecay β * isoCpl β) *
          Real.exp (-(isoDecay β) * ((ℓ : ℝ) - γ))) *
            Real.exp ((a + c) / 4) * Real.exp (max 0 (-Real.log (η * (1 - β ^ 2))) / 8)
      else 0 := by
  have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
  by_cases hηγ : η < γ
  · rw [if_pos hηγ]
    have hs := (pF2_Q_spec hβ0 hβ1 hη).1
    have hp : 0 < (isoPairMap (isoQlevel β η) (b, a, c)).1 ∧
        0 < (isoPairMap (isoQlevel β η) (b, a, c)).2 := by
      unfold isoPairMap
      split_ifs <;> exact ⟨by positivity, by positivity⟩
    have hraw := pF3_decay_exp hβ0 hβ1 hγ hℓ hp.1 hp.2
    have hN := pF3_pair_N hβ0 hβ1 hη b ha hc
    have hτ : 0 ≤ a + c := by linarith
    have hExp : Real.exp (2 * isoDecay β *
        max 0 (-isoN β (isoPairMap (isoQlevel β η) (b, a, c)).2)) ≤
        Real.exp ((a + c) / 4) *
          Real.exp (max 0 (-Real.log (η * (1 - β ^ 2))) / 8) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    have he0 : 0 ≤ isoEbar β := zero_le_one.trans (le_max_left _ _)
    have hΦ : 0 < isoPhi 1 := (lem_app_iso_gaussian_ii.2.2 1 one_pos).1
    have hK : 0 ≤ isoK5 β := by unfold isoK5; positivity
    have hcp := (pF2C_K_nonneg hβ0 hβ1).2.2.2.1
    have hδ := (pF3_decay_bounds hβ0 hβ1).1
    have hcoef : 0 ≤ isoK5 β * (1 + isoCpl β + 1 / isoDecay β) *
        Real.exp (isoDecay β * isoCpl β) *
        Real.exp (-(isoDecay β) * ((ℓ : ℝ) - γ)) := by positivity
    exact hraw.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hExp hcoef)
  · rw [if_neg hηγ, if_neg (pF3_pair_outside hβ0 hβ1 hγ0 hη
      (le_of_not_gt hηγ) b ha hc)]

/-- Integration of the separated single-lag decay estimate. -/
private lemma pF3_decay_integral {β γ : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ) (hℓ : 1 ≤ ℓ) :
    ENNReal.ofReal (lagCoeff β γ 0 ℓ) ≤
      ENNReal.ofReal ((1 / γ) *
        (isoK5 β * (1 + isoCpl β + 1 / isoDecay β) *
          Real.exp (isoDecay β * isoCpl β) *
          Real.exp (-(isoDecay β) * ((ℓ : ℝ) - γ))) * isoMe *
          (γ + 8 / (7 * (1 - β ^ 2)))) := by
  have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
  have hb : 0 < 1 - β ^ 2 := by nlinarith
  have he0 : 0 ≤ isoEbar β := zero_le_one.trans (le_max_left _ _)
  have hΦ : 0 < isoPhi 1 := (lem_app_iso_gaussian_ii.2.2 1 one_pos).1
  have hK : 0 ≤ isoK5 β := by unfold isoK5; positivity
  have hcp := (pF2C_K_nonneg hβ0 hβ1).2.2.2.1
  have hδ := (pF3_decay_bounds hβ0 hβ1).1
  have hMe := pF3_Me_pos.le
  set C := isoK5 β * (1 + isoCpl β + 1 / isoDecay β) *
    Real.exp (isoDecay β * isoCpl β) *
    Real.exp (-(isoDecay β) * ((ℓ : ℝ) - γ)) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hinner : ∀ η : ℝ, 0 < η →
      (∫⁻ w, ENNReal.ofReal
        (if (isoPairMap (isoQlevel β η) w).1 < isoQlevel β γ ∧
            (isoPairMap (isoQlevel β η) w).2 / β ^ (2 * ℓ) < isoQlevel β γ then
          isoWeightJ β γ (isoPairMap (isoQlevel β η) w).1 *
            isoWeightJ β γ ((isoPairMap (isoQlevel β η) w).2 / β ^ (2 * ℓ)) /
            (γ ^ 2 * isoDeltaHat β γ (isoPairMap (isoQlevel β η) w).1
              (isoPairMap (isoQlevel β η) w).2) else 0) ∂isoNuStar) ≤
        (if η < γ then ENNReal.ofReal (C * isoMe) *
          ENNReal.ofReal (Real.exp (max 0 (-Real.log (η * (1 - β ^ 2))) / 8)) else 0) := by
    intro η hη
    have hpt := lintegral_mono_ae (μ := isoNuStar) (f := fun w => ENNReal.ofReal
        (if (isoPairMap (isoQlevel β η) w).1 < isoQlevel β γ ∧
            (isoPairMap (isoQlevel β η) w).2 / β ^ (2 * ℓ) < isoQlevel β γ then
          isoWeightJ β γ (isoPairMap (isoQlevel β η) w).1 *
            isoWeightJ β γ ((isoPairMap (isoQlevel β η) w).2 / β ^ (2 * ℓ)) /
            (γ ^ 2 * isoDeltaHat β γ (isoPairMap (isoQlevel β η) w).1
              (isoPairMap (isoQlevel β η) w).2) else 0))
      (g := fun w => if η < γ then ENNReal.ofReal (C * Real.exp ((w.2.1 + w.2.2) / 4) *
        Real.exp (max 0 (-Real.log (η * (1 - β ^ 2))) / 8)) else 0) ?_
    · refine hpt.trans_eq ?_
      split_ifs with hh
      · have heq : ∀ w : Bool × ℝ × ℝ, ENNReal.ofReal
            (C * Real.exp ((w.2.1 + w.2.2) / 4) *
              Real.exp (max 0 (-Real.log (η * (1 - β ^ 2))) / 8)) =
            (ENNReal.ofReal C * ENNReal.ofReal
              (Real.exp (max 0 (-Real.log (η * (1 - β ^ 2))) / 8))) *
              ENNReal.ofReal (Real.exp ((w.2.1 + w.2.2) / 4)) := by
          intro w
          rw [← ENNReal.ofReal_mul hC0, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
        simp_rw [heq]
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          ENNReal.ofReal_ne_top), pF3_exp_lintegral, ENNReal.ofReal_mul hC0]
        ring
      · simp
    · filter_upwards [pF2F_nu_ae] with w hw
      have hh := pF3_decay_pair hβ0 hβ1 hγ hℓ hη w.1 hw.1.le hw.2.le
      simp only [Prod.mk.eta] at hh
      by_cases hhγ : η < γ
      · simpa only [if_pos hhγ, hC] using ENNReal.ofReal_le_ofReal hh
      · simpa only [if_neg hhγ, ENNReal.ofReal_zero] using ENNReal.ofReal_le_ofReal hh
  rw [pF3_rep hβ0 hβ1 hγ hℓ]
  have houter := setLIntegral_mono' (μ := volume) measurableSet_Ioi hinner
  have heq : (∫⁻ η in Ioi (0 : ℝ),
      if η < γ then ENNReal.ofReal (C * isoMe) *
        ENNReal.ofReal (Real.exp (max 0 (-Real.log (η * (1 - β ^ 2))) / 8)) else 0) =
      ENNReal.ofReal (C * isoMe) * ∫⁻ η in Ioo (0 : ℝ) γ,
        ENNReal.ofReal (Real.exp (max 0 (-Real.log (η * (1 - β ^ 2))) / 8)) := by
    have hh : (fun η : ℝ => if η < γ then ENNReal.ofReal (C * isoMe) *
        ENNReal.ofReal (Real.exp (max 0 (-Real.log (η * (1 - β ^ 2))) / 8)) else 0) =
        (Iio γ).indicator (fun η => ENNReal.ofReal (C * isoMe) *
          ENNReal.ofReal (Real.exp (max 0 (-Real.log (η * (1 - β ^ 2))) / 8))) := rfl
    rw [hh, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      Set.inter_comm, Set.Ioi_inter_Iio, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [heq] at houter
  have hlevels := pF3_exp_level_integral hb hγ0
  have hupper := mul_le_mul' (le_refl (ENNReal.ofReal (C * isoMe))) hlevels
  have hfinal := mul_le_mul' (le_refl (ENNReal.ofReal (1 / γ))) (houter.trans hupper)
  refine hfinal.trans_eq ?_
  rw [← ENNReal.ofReal_mul (mul_nonneg hC0 hMe),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- Scalar upper profile comparison in the two ranges of the maximum residual. -/
private lemma pF3_alg_profile (e Φ A E P Jy Jz d : ℝ)
    (he : 1 ≤ e) (hΦ : 0 < Φ) (hA : Φ ≤ A) (hE : 0 ≤ E)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hJy0 : 0 ≤ Jy) (hJy : Jy ≤ A + 2 * e)
    (hJz0 : 0 ≤ Jz) (hJz : Jz ≤ A * P + E + 2 * e)
    (hd : A * max (A - e) (A / 2) ≤ d) :
    Jy * Jz / d ≤ P +
      ((14 * e + 32 * e ^ 2 / Φ) + (4 + 8 * e / Φ) * E) / A := by
  have he0 : 0 ≤ e := by linarith
  have hA0 : 0 < A := hΦ.trans_le hA
  have hm := mul_le_mul_of_nonneg_left (le_max_right (A - e) (A / 2)) hA0.le
  have hd0 : 0 < d := by nlinarith
  have hnum : Jy * Jz ≤ (A + 2 * e) * (A * P + E + 2 * e) :=
    mul_le_mul hJy hJz hJz0 (by positivity)
  by_cases hlarge : 2 * e ≤ A
  · have hAe : 0 < A - e := by linarith
    have hden : A * (A - e) ≤ d :=
      (mul_le_mul_of_nonneg_left (le_max_left (A - e) (A / 2)) hA0.le).trans hd
    have hbase : Jy * Jz / d ≤ P + (14 * e + 4 * E) / A := by
      calc
        _ ≤ ((A + 2 * e) * (A * P + E + 2 * e)) / (A * (A - e)) :=
          div_le_div₀ (by positivity) hnum (mul_pos hA0 hAe) hden
        _ ≤ _ := by
          rw [div_le_iff₀ (mul_pos hA0 hAe)]
          have heq : (P + (14 * e + 4 * E) / A) * (A * (A - e)) =
              P * A * (A - e) + (14 * e + 4 * E) * (A - e) := by field_simp <;> ring
          rw [heq]
          nlinarith [mul_nonneg (show 0 ≤ A - 2 * e by linarith)
            (show 0 ≤ 9 * e + 3 * E by positivity),
            mul_nonneg (show 0 ≤ 3 * e * A by positivity) (sub_nonneg.2 hP1)]
    refine hbase.trans (add_le_add le_rfl (div_le_div_of_nonneg_right ?_ hA0.le))
    have : 0 ≤ 32 * e ^ 2 / Φ := by positivity
    have : 0 ≤ 8 * e / Φ * E := by positivity
    nlinarith
  · have hsmall : A ≤ 2 * e := le_of_not_ge hlarge
    have hP : A * P ≤ A := mul_le_of_le_one_right hA0.le hP1
    have hnum2 : Jy * Jz ≤ 4 * e * (4 * e + E) := by
      have hh := mul_le_mul
        (show A + 2 * e ≤ 4 * e by linarith)
        (show A * P + E + 2 * e ≤ 4 * e + E by linarith)
        (show 0 ≤ A * P + E + 2 * e by positivity)
        (show 0 ≤ 4 * e by positivity)
      exact hnum.trans hh
    have hda : A ^ 2 / 2 ≤ d := by nlinarith
    have hbase : Jy * Jz / d ≤ (8 * e * (4 * e + E) / Φ) / A := by
      calc
        _ ≤ (4 * e * (4 * e + E)) / (A ^ 2 / 2) :=
          div_le_div₀ (by positivity) hnum2 (by positivity) hda
        _ = (8 * e * (4 * e + E) / A) / A := by field_simp <;> ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_left (by positivity) hΦ hA) hA0.le
    refine hbase.trans ?_
    have hh : 8 * e * (4 * e + E) / Φ ≤
        (14 * e + 32 * e ^ 2 / Φ) + (4 + 8 * e / Φ) * E := by
      have heq : 8 * e * (4 * e + E) / Φ = 32 * e ^ 2 / Φ + 8 * e / Φ * E := by ring
      rw [heq]
      nlinarith
    have hh' := div_le_div_of_nonneg_right hh hA0.le
    linarith

/-- Upper kernel comparison for one lag on its active support. -/
private lemma pF3_upper {β γ y z : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hℓ : 1 ≤ ℓ) (hy : 0 < y) (hz : 0 < z)
    (hreg : y < isoQlevel β γ ∧ z / β ^ (2 * ℓ) < isoQlevel β γ) :
    isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * ℓ)) /
      (γ ^ 2 * isoDeltaHat β γ y z) ≤
        max (1 - (ℓ : ℝ) / isoAvee β γ y z) 0 +
          (isoK3 β + isoK4 β * (isoCpl β + max 0 (-isoN β z))) / isoAvee β γ y z := by
  have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
  have he : 1 ≤ isoEbar β := le_max_left _ _
  have he0 : 0 ≤ isoEbar β := by linarith
  have hΦ : 0 < isoPhi 1 := (lem_app_iso_gaussian_ii.2.2 1 one_pos).1
  have hcp := (pF2C_K_nonneg hβ0 hβ1).2.2.2.1
  have hn : 0 ≤ max 0 (-isoN β z) := le_max_left _ _
  have hreg1 := pF3_region hβ0 hβ1 hℓ hz hreg
  obtain ⟨hAy, hAz, -, -⟩ := pF2B_region hβ0 hβ1 hγ hy hz hreg1.1 hreg1.2
  have hz0 : 0 < z / β ^ (2 * ℓ) := div_pos hz (pow_pos hβ0 _)
  have hr := (pF2_lt_Q_iff hβ0 hβ1 hγ0 hz0).1 hreg.2
  have hAzl : 0 < isoResid β γ (z / β ^ (2 * ℓ)) := by
    unfold isoResid; linarith
  have hJy := pF2B_J_bounds (γ := γ) hβ0 hβ1 hy
  have hJz := pF2B_J_bounds (γ := γ) hβ0 hβ1 hz0
  have hAvy : isoResid β γ y ≤ isoAvee β γ y z := le_max_left _ _
  have hAvz : isoResid β γ z ≤ isoAvee β γ y z := le_max_right _ _
  have hAv0 : 0 < isoAvee β γ y z := hAy.trans_le hAvy
  have hP0 : 0 ≤ max (1 - (ℓ : ℝ) / isoAvee β γ y z) 0 := le_max_right _ _
  have hP1 : max (1 - (ℓ : ℝ) / isoAvee β γ y z) 0 ≤ 1 := by
    apply max_le _ zero_le_one
    have : 0 ≤ (ℓ : ℝ) / isoAvee β γ y z := div_nonneg (Nat.cast_nonneg ℓ) hAv0.le
    linarith
  have hAP : isoAvee β γ y z - (ℓ : ℝ) ≤
      isoAvee β γ y z * max (1 - (ℓ : ℝ) / isoAvee β γ y z) 0 := by
    have hh := mul_le_mul_of_nonneg_left
      (le_max_left (1 - (ℓ : ℝ) / isoAvee β γ y z) 0) hAv0.le
    have heq : isoAvee β γ y z * (1 - (ℓ : ℝ) / isoAvee β γ y z) =
        isoAvee β γ y z - (ℓ : ℝ) := by field_simp
    rwa [heq] at hh
  have hm : max (isoResid β γ z + (isoCpl β + max 0 (-isoN β z)) - (ℓ : ℝ)) 0 ≤
      isoAvee β γ y z * max (1 - (ℓ : ℝ) / isoAvee β γ y z) 0 +
        (isoCpl β + max 0 (-isoN β z)) := by
    apply max_le
    · linarith
    · positivity
  have hw := pF3_weight_upper (γ := γ) (ℓ := ℓ) hβ0 hβ1 hz
  have hd := (lem_app_iso_kernel_bounds_v hβ0 hβ1 hγ0 hy hz hAy (hΦ.trans hAz)).2.2.2.1
  exact pF3_alg_profile (isoEbar β) (isoPhi 1) (isoAvee β γ y z)
    (isoCpl β + max 0 (-isoN β z)) (max (1 - (ℓ : ℝ) / isoAvee β γ y z) 0)
    (isoWeightJ β γ y) (isoWeightJ β γ (z / β ^ (2 * ℓ)))
    (γ ^ 2 * isoDeltaHat β γ y z) he hΦ (hAz.le.trans hAvz)
    (add_nonneg hcp hn) hP0 hP1 (hAy.le.trans hJy.1) (by linarith)
    (hAzl.le.trans hJz.1) (by linarith) hd

/-- Reciprocal residual bound used to integrate the upper profile error. -/
private lemma pF3_inv_bound {Φ A x b : ℝ} (hΦ : 0 < Φ) (hA : Φ ≤ A)
    (hx : 0 < x) (hb : 0 ≤ b) (hxb : x ≤ A + b) :
    1 / A ≤ 1 / Φ * min 1 (2 * (Φ + b) / x) := by
  have hA0 : 0 < A := hΦ.trans_le hA
  rcases min_choice 1 (2 * (Φ + b) / x) with h | h
  · rw [h, mul_one]
    exact one_div_le_one_div_of_le hΦ hA
  · rw [h]
    have heq : 1 / Φ * (2 * (Φ + b) / x) = (2 * (Φ + b)) / (Φ * x) := by ring
    rw [heq, div_le_div_iff₀ hA0 (mul_pos hΦ hx)]
    have hh := mul_le_mul_of_nonneg_left hxb hΦ.le
    nlinarith [mul_nonneg (sub_nonneg.2 hA) hb,
      mul_nonneg hA0.le (add_nonneg hΦ.le hb)]

/-- The upper profile bound with separated layer and low-level errors. -/
private lemma pF3_upper_core {β γ x τ y z : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ)
    (hℓ : 1 ≤ ℓ) (hx : 0 < x) (hτ : 0 ≤ τ) (hy : 0 < y) (hz : 0 < z)
    (hyA : |isoResid β γ y - x| ≤ isoEbar β * τ)
    (hzA : |isoResid β γ z - x| ≤ isoEbar β * τ) :
    (if y < isoQlevel β γ ∧ z / β ^ (2 * ℓ) < isoQlevel β γ
      then isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * ℓ)) /
        (γ ^ 2 * isoDeltaHat β γ y z) else 0) ≤
      max (1 - (ℓ : ℝ) / x) 0 + min 1 ((1 + isoEbar β * τ) / x) +
        (isoK3 β + isoK4 β * isoCpl β) / isoPhi 1 *
          min 1 (2 * (isoPhi 1 + isoEbar β * τ) / x) +
        isoK4 β * max 0 (-isoN β z) / isoPhi 1 := by
  have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
  have he0 : 0 ≤ isoEbar β := zero_le_one.trans (le_max_left _ _)
  have hΦ : 0 < isoPhi 1 := (lem_app_iso_gaussian_ii.2.2 1 one_pos).1
  have hcp := (pF2C_K_nonneg hβ0 hβ1).2.2.2.1
  have hn : 0 ≤ max 0 (-isoN β z) := le_max_left _ _
  have hK3 : 0 ≤ isoK3 β := by unfold isoK3; positivity
  have hK4 : 0 ≤ isoK4 β := by unfold isoK4; positivity
  have hEt : 0 ≤ isoEbar β * τ := mul_nonneg he0 hτ
  have hmin1 : 0 ≤ min 1 ((1 + isoEbar β * τ) / x) := by positivity
  have hmin2 : 0 ≤ min 1 (2 * (isoPhi 1 + isoEbar β * τ) / x) := by positivity
  split_ifs with hreg
  · have hreg1 := pF3_region hβ0 hβ1 hℓ hz hreg
    obtain ⟨hAy, hAz, -, -⟩ := pF2B_region hβ0 hβ1 hγ hy hz hreg1.1 hreg1.2
    have hAvy : isoResid β γ y ≤ isoAvee β γ y z := le_max_left _ _
    have hAvz : isoResid β γ z ≤ isoAvee β γ y z := le_max_right _ _
    have hAv0 : 0 < isoAvee β γ y z := hAy.trans_le hAvy
    have hAvΦ : isoPhi 1 ≤ isoAvee β γ y z := hAz.le.trans hAvz
    have hAvup : isoAvee β γ y z ≤ x + isoEbar β * τ :=
      max_le (by linarith [(abs_le.mp hyA).2]) (by linarith [(abs_le.mp hzA).2])
    have hAvlow : x ≤ isoAvee β γ y z + isoEbar β * τ := by
      linarith [(abs_le.mp hyA).1]
    have hP := (pF3_profile_mono (Nat.cast_nonneg ℓ) hAv0 hAvup).trans
      (pF3_profile_shift (Nat.cast_nonneg ℓ) hx hEt)
    have hminup : min 1 (isoEbar β * τ / x) ≤ min 1 ((1 + isoEbar β * τ) / x) := by
      apply min_le_min le_rfl
      apply div_le_div_of_nonneg_right _ hx.le
      linarith
    have hi := pF3_inv_bound hΦ hAvΦ hx hEt hAvlow
    have hi' := one_div_le_one_div_of_le hΦ hAvΦ
    have hc0 : 0 ≤ isoK3 β + isoK4 β * isoCpl β := by positivity
    have hcN : 0 ≤ isoK4 β * max 0 (-isoN β z) := mul_nonneg hK4 hn
    have h1 := mul_le_mul_of_nonneg_left hi hc0
    have h2 := mul_le_mul_of_nonneg_left hi' hcN
    have hbound := pF3_upper hβ0 hβ1 hγ hℓ hy hz hreg
    have heq : (isoK3 β + isoK4 β * (isoCpl β + max 0 (-isoN β z))) /
        isoAvee β γ y z =
        (isoK3 β + isoK4 β * isoCpl β) * (1 / isoAvee β γ y z) +
          (isoK4 β * max 0 (-isoN β z)) * (1 / isoAvee β γ y z) := by ring
    rw [heq] at hbound
    calc
      _ ≤ max (1 - (ℓ : ℝ) / x) 0 + min 1 ((1 + isoEbar β * τ) / x) +
          (isoK3 β + isoK4 β * isoCpl β) *
            (1 / isoPhi 1 * min 1 (2 * (isoPhi 1 + isoEbar β * τ) / x)) +
          (isoK4 β * max 0 (-isoN β z)) * (1 / isoPhi 1) := by linarith
      _ = _ := by ring
  · positivity

/-- The truncated reciprocal is integrable despite its harmless endpoint value. -/
private lemma pF3_min_integrable {Y γ : ℝ} (hY : 0 ≤ Y) (hγ : 0 ≤ γ) :
    IntervalIntegrable (fun x : ℝ => min 1 (Y / x)) volume 0 γ := by
  refine (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 γ).mono_fun'
    ((measurable_const.min (measurable_const.div measurable_id)).aestronglyMeasurable) ?_
  rw [uIoc_of_le hγ]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (div_nonneg hY hx.1.le))]
  exact min_le_left _ _

/-- Exact integration after splitting at the truncation scale. -/
private lemma pF3_min_integral_eq {Y γ : ℝ} (hY : 0 < Y) (hγ : 0 < γ) :
    (∫ x in (0 : ℝ)..γ, min 1 (Y / x)) =
      if Y ≤ γ then Y * (1 + Real.log (γ / Y)) else γ := by
  have hlow : ∀ {b : ℝ}, 0 ≤ b → b ≤ Y →
      (∫ x in (0 : ℝ)..b, min 1 (Y / x)) = b := by
    intro b hb hbY
    calc
      _ = ∫ _x in (0 : ℝ)..b, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hb
        intro x hx
        exact min_eq_left ((le_div_iff₀ hx.1).2 (by linarith [hx.2]))
      _ = b := by simp
  split_ifs with hYγ
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (pF3_min_integrable hY.le hY.le) (pF3_min_integrable hY.le hγ.le |>.mono_set (c := Y) (d := γ)
        (by rw [uIcc_of_le hγ.le, uIcc_of_le hYγ]; exact Icc_subset_Icc hY.le le_rfl))
    rw [← hsplit, hlow hY.le le_rfl]
    have heq : (∫ x in Y..γ, min 1 (Y / x)) = ∫ x in Y..γ, Y * x⁻¹ := by
      apply intervalIntegral.integral_congr_Ioo_of_le hYγ
      intro x hx
      dsimp only
      rw [min_eq_right ((div_le_one (hY.trans hx.1)).2 hx.1.le), div_eq_mul_inv]
    rw [heq, intervalIntegral.integral_const_mul, integral_inv_of_pos hY hγ]
    ring
  · exact hlow hγ.le (le_of_not_ge hYγ)

/-- The logarithmic truncation bound, uniform above a positive lower scale. -/
private lemma pF3_min_integral_le {c Y γ : ℝ} (hc : 0 < c) (hcY : c ≤ Y) (hγ : 0 < γ) :
    (∫ x in (0 : ℝ)..γ, min 1 (Y / x)) ≤
      Y * (1 + max (Real.log (γ / c)) 0) := by
  have hY := hc.trans_le hcY
  rw [pF3_min_integral_eq hY hγ]
  split_ifs with hYγ
  · have hlog : Real.log (γ / Y) ≤ Real.log (γ / c) :=
      Real.log_le_log (div_pos hγ hY) (div_le_div_of_nonneg_left hγ.le hc hcY)
    exact mul_le_mul_of_nonneg_left (by linarith [le_max_left (Real.log (γ / c)) 0]) hY.le
  · have hmax := le_max_right (Real.log (γ / c)) 0
    nlinarith [le_of_not_ge hYγ]

/-- The level integral of the single-lag profile. -/
private lemma pF3_profile_integral {l γ : ℝ} (hl : 0 < l) (hγ : 0 < γ) :
    (∫ x in (0 : ℝ)..γ, max (1 - l / x) 0) = γ * isoCalG (l / γ) := by
  have heq : (∫ x in (0 : ℝ)..γ, max (1 - l / x) 0) =
      γ - ∫ x in (0 : ℝ)..γ, min 1 (l / x) := by
    calc
      _ = ∫ x in (0 : ℝ)..γ, (1 : ℝ) - min 1 (l / x) := by
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only
        by_cases h : l / x ≤ 1
        · rw [min_eq_right h, max_eq_left (sub_nonneg.2 h)]
        · rw [min_eq_left (le_of_not_ge h), max_eq_right (by linarith)]
          ring
      _ = _ := by rw [intervalIntegral.integral_sub intervalIntegrable_const
        (pF3_min_integrable hl.le hγ.le)]; simp
  rw [heq, pF3_min_integral_eq hl hγ]
  unfold isoCalG
  by_cases hlγ : l ≤ γ
  · rw [if_pos hlγ, if_pos ((div_le_one hγ).2 hlγ), Real.log_div hγ.ne' hl.ne',
      Real.log_div hl.ne' hγ.ne']
    field_simp
    <;> ring
  · rw [if_neg hlγ, if_neg (by simpa only [div_le_one hγ] using hlγ)]
    ring

/-- Reflection of a nonnegative level integral, with the support indicator retained. -/
private lemma pF3_layer_integral {γ : ℝ} (hγ : 0 < γ) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 γ) (hf0 : ∀ x ∈ Ioo 0 γ, 0 ≤ f x) :
    (∫⁻ η in Ioi (0 : ℝ), if η < γ then ENNReal.ofReal (f (γ - η)) else 0) =
      ENNReal.ofReal (∫ x in (0 : ℝ)..γ, f x) := by
  have heq : (fun η : ℝ => if η < γ then ENNReal.ofReal (f (γ - η)) else 0) =
      (Iio γ).indicator (fun η => ENNReal.ofReal (f (γ - η))) := rfl
  rw [heq, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    inter_comm, Ioi_inter_Iio]
  have hf' : IntervalIntegrable (fun η => f (γ - η)) volume 0 γ := by
    simpa using (hf.comp_sub_left γ).symm
  rw [← ofReal_integral_eq_lintegral_ofReal (hf'.1.mono_set Ioo_subset_Ioc_self)
    ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun η hη =>
      hf0 (γ - η) ⟨by linarith [hη.2], by linarith [hη.1]⟩))]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hγ.le,
    intervalIntegral.integral_comp_sub_left]
  simp

private lemma pF3_profile_integrable {l γ : ℝ} (hl : 0 ≤ l) (hγ : 0 ≤ γ) :
    IntervalIntegrable (fun x : ℝ => max (1 - l / x) 0) volume 0 γ := by
  refine (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 γ).mono_fun'
    ((measurable_const.sub (measurable_const.div measurable_id)).max
      measurable_const |>.aestronglyMeasurable) ?_
  rw [uIoc_of_le hγ]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [div_nonneg hl hx.1.le]) zero_le_one

/-- Tonelli and the first moment integrate every affine truncation scale used below. -/
private lemma pF3_error_integral {β γ c u v : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    (hc : 0 < c) (hcu : c ≤ u) (hv : 0 ≤ v) :
    (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w : Bool × ℝ × ℝ,
      (if η < γ then ENNReal.ofReal (min 1 ((u + v * (w.2.1 + w.2.2)) / (γ - η)))
        else 0) ∂isoNuStar) ≤
      ENNReal.ofReal ((u + v * isoM1) * (1 + max (Real.log (γ / c)) 0)) := by
  haveI := pF2F_prob hβ0 hβ1
  have hu : 0 ≤ u := hc.le.trans hcu
  have hL : 0 ≤ 1 + max (Real.log (γ / c)) 0 := by positivity
  have hm : Measurable (fun p : ℝ × (Bool × ℝ × ℝ) =>
      if p.1 < γ then ENNReal.ofReal
        (min 1 ((u + v * (p.2.2.1 + p.2.2.2)) / (γ - p.1))) else 0) := by
    refine Measurable.ite (measurableSet_lt measurable_fst measurable_const) ?_ measurable_const
    exact (measurable_const.min (by fun_prop)).ennreal_ofReal
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc
    _ ≤ ∫⁻ w : Bool × ℝ × ℝ,
        ENNReal.ofReal ((u + v * (w.2.1 + w.2.2)) *
          (1 + max (Real.log (γ / c)) 0)) ∂isoNuStar := by
      apply lintegral_mono_ae
      filter_upwards [pF2F_nu_ae] with w hw
      have hτ : 0 ≤ w.2.1 + w.2.2 := by linarith [hw.1, hw.2]
      have hY : c ≤ u + v * (w.2.1 + w.2.2) := by nlinarith
      rw [pF3_layer_integral hγ
        (pF3_min_integrable (hc.le.trans hY) hγ.le)
        (fun x hx => le_min zero_le_one (div_nonneg (hc.le.trans hY) hx.1.le))]
      exact ENNReal.ofReal_le_ofReal (pF3_min_integral_le hc hY hγ)
    _ = _ := by
      simp_rw [mul_comm (u + v * (_ + _)) (1 + max (Real.log (γ / c)) 0),
        ENNReal.ofReal_mul hL]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        pF2F_lint_up_tau hβ0 hβ1 hu hv,
        ← ENNReal.ofReal_mul hL]
      congr 1
      ring

/-- Splitting a double nonnegative integral when one summand is measurable. -/
private lemma pF3_double_add {f g : ℝ × (Bool × ℝ × ℝ) → ENNReal} (hf : Measurable f) :
    (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, (f (η, w) + g (η, w)) ∂isoNuStar) =
      (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, f (η, w) ∂isoNuStar) +
      (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, g (η, w) ∂isoNuStar) := by
  haveI := pF2F_prob (β := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  calc
    _ = ∫⁻ η in Ioi (0 : ℝ),
        ((∫⁻ w, f (η, w) ∂isoNuStar) + ∫⁻ w, g (η, w) ∂isoNuStar) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro η _
      exact lintegral_add_left (hf.comp measurable_prodMk_left) _
    _ = _ := lintegral_add_left (Measurable.lintegral_prod_right' hf) _

/-- Both profile comparisons on one averaging layer. -/
private lemma pF3_pair_profile {β γ η : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ) (hℓ : 1 ≤ ℓ)
    (hη : 0 < η) (hηγ : η < γ) (b : Bool) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (F : ℝ × ℝ → ℝ)
    (hF : ∀ y z : ℝ, 0 < y → 0 < z → F (y, z) =
      (if y < isoQlevel β γ ∧ z / β ^ (2 * ℓ) < isoQlevel β γ then
        isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * ℓ)) /
          (γ ^ 2 * isoDeltaHat β γ y z) else 0)) :
    max (1 - (ℓ : ℝ) / (γ - η)) 0 -
        min 1 (4 * (isoEbar β * (a + c + 1)) / (γ - η)) ≤
      F (isoPairMap (isoQlevel β η) (b, a, c)) ∧
    F (isoPairMap (isoQlevel β η) (b, a, c)) ≤
      max (1 - (ℓ : ℝ) / (γ - η)) 0 +
        min 1 ((1 + isoEbar β * (a + c)) / (γ - η)) +
        (isoK3 β + isoK4 β * isoCpl β) / isoPhi 1 *
          min 1 (2 * (isoPhi 1 + isoEbar β * (a + c)) / (γ - η)) +
        isoK4 β * max 0 (-isoN β (isoPairMap (isoQlevel β η) (b, a, c)).2) /
          isoPhi 1 := by
  obtain ⟨hs, hrs⟩ := pF2_Q_spec hβ0 hβ1 hη
  have hp : 0 < (isoPairMap (isoQlevel β η) (b, a, c)).1 ∧
      0 < (isoPairMap (isoQlevel β η) (b, a, c)).2 := by
    unfold isoPairMap
    split_ifs <;> exact ⟨by positivity, by positivity⟩
  have h := lem_app_iso_averaging_iii (γ := γ) hβ0 hβ1 (isoQlevel β η) hs b a c ha hc
  have hsA : isoResid β γ (isoQlevel β η) = γ - η := by unfold isoResid; rw [hrs]
  obtain ⟨-, -, hyA, hzA, -⟩ := h
  rw [hsA] at hyA hzA
  have he := hF _ _ hp.1 hp.2
  simp only [Prod.mk.eta] at he
  rw [he]
  exact ⟨pF3_lower_core hβ0 hβ1 hγ hℓ (by linarith) (by linarith) hp.1 hp.2 hyA hzA,
    pF3_upper_core hβ0 hβ1 hγ hℓ (by linarith) (by linarith) hp.1 hp.2 hyA hzA⟩

private lemma pF3_double_const_mul (c : ℝ) (f : ℝ × (Bool × ℝ × ℝ) → ENNReal) :
    (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, ENNReal.ofReal c * f (η, w) ∂isoNuStar) =
      ENNReal.ofReal c * ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, f (η, w) ∂isoNuStar := by
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- A tangent-line bound for the Gaussian scalar at one. -/
private lemma pF3_phi_half : isoPhi 1 ≤ 1 / 2 := by
  have hg := Muon.Foundations.gaussian_integrable_pow 2
  have hi : Integrable (fun g : ℝ => g ^ 2 / (1 + g ^ 2)) (ProbabilityTheory.gaussianReal 0 1) := by
    refine hg.mono' (by fun_prop : Measurable (fun g : ℝ => g ^ 2 / (1 + g ^ 2))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_self (sq_nonneg g) (by nlinarith [sq_nonneg g])
  have hb : Integrable (fun g : ℝ => (1 + g ^ 2) / 4) (ProbabilityTheory.gaussianReal 0 1) :=
    ((integrable_const 1).add hg).div_const 4
  have hm := integral_mono hi hb (fun g => show g ^ 2 / (1 + g ^ 2) ≤ (1 + g ^ 2) / 4 from by
    apply (div_le_iff₀ (by positivity : 0 < 1 + g ^ 2)).2
    nlinarith [sq_nonneg (g ^ 2 - 1)])
  have heq : isoPhi 1 = ∫ g : ℝ, g ^ 2 / (1 + g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1) := by
    simp [isoPhi, Muon.DetEquiv.J]
  rw [← heq, integral_div, integral_add (integrable_const 1) hg,
    Muon.Foundations.gaussian_moment_two] at hm
  norm_num at hm ⊢
  exact hm

private lemma pF3_log_factor {γ c : ℝ} (hγ : 1 ≤ γ) (hc : 0 < c) (hc1 : c ≤ 1) :
    1 + max (Real.log (γ / c)) 0 ≤
      (1 + Real.log γ) * (1 + Real.log (1 / c)) := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have hLγ : 0 ≤ Real.log γ := Real.log_nonneg hγ
  have hLc : 0 ≤ Real.log (1 / c) := Real.log_nonneg ((one_le_div hc).2 hc1)
  have heq : Real.log (γ / c) = Real.log γ + Real.log (1 / c) := by
    rw [Real.log_div hγ0.ne' hc.ne', Real.log_div one_ne_zero hc.ne', Real.log_one]
    ring
  rw [heq, max_eq_left (by linarith)]
  nlinarith [mul_nonneg hLγ hLc]

/-- Integrated single-lag comparisons before division by the aspect ratio. -/
private lemma pF3_profile_bounds {β γ : ℝ} {ℓ : ℕ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : isoGammaCirc β ≤ γ) (hℓ : 1 ≤ ℓ)
    (F : ℝ × ℝ → ℝ) (hF0 : ∀ p, 0 ≤ F p)
    (hF : ∀ y z : ℝ, 0 < y → 0 < z → F (y, z) =
      (if y < isoQlevel β γ ∧ z / β ^ (2 * ℓ) < isoQlevel β γ then
        isoWeightJ β γ y * isoWeightJ β γ (z / β ^ (2 * ℓ)) /
          (γ ^ 2 * isoDeltaHat β γ y z) else 0)) :
    ENNReal.ofReal (γ * isoCalG ((ℓ : ℝ) / γ)) ≤
      (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal (F (isoPairMap (isoQlevel β η) w)) ∂isoNuStar) +
      ENNReal.ofReal (4 * isoEbar β * (isoM1 + 1) *
        (1 + max (Real.log (γ / (4 * isoEbar β))) 0)) ∧
    (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal (F (isoPairMap (isoQlevel β η) w)) ∂isoNuStar) ≤
      ENNReal.ofReal (γ * isoCalG ((ℓ : ℝ) / γ) + isoKpr β * (1 + Real.log γ)) := by
  haveI := pF2F_prob hβ0 hβ1
  have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
  have hl0 : (0 : ℝ) < ℓ := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hG0 : 0 ≤ γ * isoCalG ((ℓ : ℝ) / γ) := by
    rw [← pF3_profile_integral hl0 hγ0]
    exact intervalIntegral.integral_nonneg hγ0.le (fun _ _ => le_max_right _ _)
  have hc' : 0 < isoC' β := by
    have hb : 0 < 1 - β ^ 2 := by nlinarith
    unfold isoC'; positivity
  have hγ1 : 1 ≤ γ := by unfold isoGammaCirc at hγ; linarith
  have he : 0 < isoEbar β := zero_lt_one.trans_le (le_max_left _ _)
  have hΦ : 0 < isoPhi 1 := (lem_app_iso_gaussian_ii.2.2 1 one_pos).1
  have hK3 : 0 ≤ isoK3 β := by unfold isoK3; positivity
  have hK4 : 0 ≤ isoK4 β := by unfold isoK4; positivity
  have hcp := (pF2C_K_nonneg hβ0 hβ1).2.2.2.1
  have hM := pF2_M1_nonneg
  have hL := (pF2_L_nonneg hβ0 hβ1).1
  have hlogγ : 0 ≤ Real.log γ := Real.log_nonneg hγ1
  have hlogΦ : 0 ≤ Real.log (1 / (2 * isoPhi 1)) :=
    Real.log_nonneg ((one_le_div (by positivity)).2 (by linarith [pF3_phi_half]))
  let C : ℝ := (isoK3 β + isoK4 β * isoCpl β) / isoPhi 1
  let D : ℝ := isoK4 β / isoPhi 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let J : ℝ × (Bool × ℝ × ℝ) → ENNReal := fun p =>
    ENNReal.ofReal (F (isoPairMap (isoQlevel β p.1) p.2))
  let P : ℝ × (Bool × ℝ × ℝ) → ENNReal := fun p =>
    if p.1 < γ then ENNReal.ofReal (max (1 - (ℓ : ℝ) / (γ - p.1)) 0) else 0
  let E : ℝ → ℝ → ℝ × (Bool × ℝ × ℝ) → ENNReal := fun u v p =>
    if p.1 < γ then ENNReal.ofReal
      (min 1 ((u + v * (p.2.2.1 + p.2.2.2)) / (γ - p.1))) else 0
  let N : ℝ × (Bool × ℝ × ℝ) → ENNReal := fun p =>
    ENNReal.ofReal (max 0 (-isoN β (isoPairMap (isoQlevel β p.1) p.2).2))
  have hmP : Measurable P := by
    apply Measurable.ite (measurableSet_lt measurable_fst measurable_const)
      (by fun_prop) measurable_const
  have hmE : ∀ u v : ℝ, Measurable (E u v) := by
    intro u v
    apply Measurable.ite (measurableSet_lt measurable_fst measurable_const)
      (by fun_prop) measurable_const
  have hmN : Measurable N := (pF2F_N_meas hβ0 hβ1).ennreal_ofReal
  have hP : (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, P (η, w) ∂isoNuStar) =
      ENNReal.ofReal (γ * isoCalG ((ℓ : ℝ) / γ)) := by
    simp only [P, lintegral_const, measure_univ, mul_one]
    rw [pF3_layer_integral hγ0
      (pF3_profile_integrable (Nat.cast_nonneg ℓ) hγ0.le)
      (fun x _ => le_max_right _ _), pF3_profile_integral hl0 hγ0]
  have hE0 := pF3_error_integral hβ0 hβ1 hγ0
    (c := 4 * isoEbar β) (u := 4 * isoEbar β) (v := 4 * isoEbar β)
    (by positivity) le_rfl (by positivity)
  have hE1 := pF3_error_integral hβ0 hβ1 hγ0
    (c := 1) (u := 1) (v := isoEbar β) one_pos le_rfl he.le
  have hE2 := pF3_error_integral hβ0 hβ1 hγ0
    (c := 2 * isoPhi 1) (u := 2 * isoPhi 1) (v := 2 * isoEbar β)
    (by positivity) le_rfl (by positivity)
  have hN : (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, N (η, w) ∂isoNuStar) ≤
      ENNReal.ofReal (isoLbar1 β) := (lem_app_iso_low_levels_ii hβ0 hβ1).1
  have hpt : ∀ η : ℝ, 0 < η → ∀ᵐ w ∂isoNuStar,
      P (η, w) ≤ E (4 * isoEbar β) (4 * isoEbar β) (η, w) + J (η, w) ∧
      J (η, w) ≤ P (η, w) + E 1 (isoEbar β) (η, w) +
        ENNReal.ofReal C * E (2 * isoPhi 1) (2 * isoEbar β) (η, w) +
        ENNReal.ofReal D * N (η, w) := by
    intro η hη
    filter_upwards [pF2F_nu_ae] with w hw
    by_cases hηγ : η < γ
    · have hx : 0 < γ - η := by linarith
      have hτ : 0 ≤ w.2.1 + w.2.2 := by linarith [hw.1, hw.2]
      have hraw := pF3_pair_profile hβ0 hβ1 hγ hℓ hη hηγ w.1 hw.1.le hw.2.le F hF
      simp only [Prod.mk.eta] at hraw
      have h0 : 0 ≤ min 1 ((4 * isoEbar β + 4 * isoEbar β * (w.2.1 + w.2.2)) /
          (γ - η)) := by positivity
      have h1 : 0 ≤ min 1 ((1 + isoEbar β * (w.2.1 + w.2.2)) / (γ - η)) := by positivity
      have h2 : 0 ≤ min 1 ((2 * isoPhi 1 + 2 * isoEbar β * (w.2.1 + w.2.2)) /
          (γ - η)) := by positivity
      have hn : 0 ≤ max 0 (-isoN β (isoPairMap (isoQlevel β η) w).2) := le_max_left _ _
      have hp : 0 ≤ max (1 - (ℓ : ℝ) / (γ - η)) 0 := le_max_right _ _
      simp only [P, E, J, N, if_pos hηγ]
      constructor
      · rw [← ENNReal.ofReal_add h0 (hF0 _)]
        apply ENNReal.ofReal_le_ofReal
        have heq : 4 * (isoEbar β * (w.2.1 + w.2.2 + 1)) =
            4 * isoEbar β + 4 * isoEbar β * (w.2.1 + w.2.2) := by ring
        rw [heq] at hraw
        linarith [hraw.1]
      · rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul hD,
          ← ENNReal.ofReal_add hp h1,
          ← ENNReal.ofReal_add (add_nonneg hp h1) (mul_nonneg hC h2),
          ← ENNReal.ofReal_add (by positivity) (mul_nonneg hD hn)]
        apply ENNReal.ofReal_le_ofReal
        have heq : 2 * (isoPhi 1 + isoEbar β * (w.2.1 + w.2.2)) =
            2 * isoPhi 1 + 2 * isoEbar β * (w.2.1 + w.2.2) := by ring
        rw [heq] at hraw
        exact hraw.2.trans_eq (by dsimp [C, D]; ring)
    · have hs := (pF2_Q_spec hβ0 hβ1 hη).1
      have hp : 0 < (isoPairMap (isoQlevel β η) w).1 ∧
          0 < (isoPairMap (isoQlevel β η) w).2 := by
        unfold isoPairMap
        split_ifs <;> exact ⟨by positivity, by positivity⟩
      have hFe := hF _ _ hp.1 hp.2
      simp only [Prod.mk.eta] at hFe
      have hout := pF3_pair_outside hβ0 hβ1 hγ0 hη (le_of_not_gt hηγ)
        w.1 hw.1.le hw.2.le (ℓ := ℓ)
      simp only [Prod.mk.eta] at hout
      simp only [J, P, E, if_neg hηγ, hFe, if_neg hout, ENNReal.ofReal_zero]
      exact ⟨by simp, by simp⟩
  constructor
  · have hm := lintegral_mono_ae (μ := volume.restrict (Ioi (0 : ℝ)))
      ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun η hη => lintegral_mono_ae ((hpt η hη).mono
        (fun w hw => hw.1))))
    rw [← hP]
    refine hm.trans ?_
    rw [pF3_double_add (hmE _ _)]
    have hh : (∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        E (4 * isoEbar β) (4 * isoEbar β) (η, w) ∂isoNuStar) ≤
        ENNReal.ofReal (4 * isoEbar β * (isoM1 + 1) *
          (1 + max (Real.log (γ / (4 * isoEbar β))) 0)) := by
      convert hE0 using 1 <;> congr 1 <;> ring
    calc
      _ ≤ ENNReal.ofReal (4 * isoEbar β * (isoM1 + 1) *
          (1 + max (Real.log (γ / (4 * isoEbar β))) 0)) +
          ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w, J (η, w) ∂isoNuStar := add_le_add hh le_rfl
      _ = _ := add_comm _ _
  · have hm := lintegral_mono_ae (μ := volume.restrict (Ioi (0 : ℝ)))
      ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun η hη => lintegral_mono_ae ((hpt η hη).mono
        (fun w hw => hw.2))))
    refine hm.trans ?_
    have hs1 := pF3_double_add
      (g := fun p => ENNReal.ofReal D * N p)
      ((hmP.add (hmE 1 (isoEbar β))).add
        ((hmE (2 * isoPhi 1) (2 * isoEbar β)).const_mul (ENNReal.ofReal C)))
    have hs2 := pF3_double_add
      (g := fun p => ENNReal.ofReal C * E (2 * isoPhi 1) (2 * isoEbar β) p)
      (hmP.add (hmE 1 (isoEbar β)))
    have hs3 := pF3_double_add (g := E 1 (isoEbar β)) hmP
    simp only [Pi.add_apply] at hs1 hs2
    rw [hs1, hs2, hs3, pF3_double_const_mul, pF3_double_const_mul, hP]
    have hbound := add_le_add (add_le_add (add_le_add
      (le_refl (ENNReal.ofReal (γ * isoCalG ((ℓ : ℝ) / γ)))) hE1)
      (mul_le_mul' (le_refl (ENNReal.ofReal C)) hE2))
      (mul_le_mul' (le_refl (ENNReal.ofReal D)) hN)
    refine hbound.trans ?_
    rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul hD,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hlog1 : 1 + max (Real.log (γ / 1)) 0 = 1 + Real.log γ := by
      rw [div_one, max_eq_left hlogγ]
    have hlog2 := pF3_log_factor hγ1 (c := 2 * isoPhi 1)
      (by positivity) (by linarith [pF3_phi_half])
    have hcoef : 0 ≤ C * (2 * isoPhi 1 + 2 * isoEbar β * isoM1) := by positivity
    have hb := mul_le_mul_of_nonneg_left hlog2 hcoef
    have hlast : D * isoLbar1 β ≤ D * isoLbar1 β * (1 + Real.log γ) := by
      nlinarith [mul_nonneg (mul_nonneg hD hL) hlogγ]
    rw [hlog1]
    have heq : isoKpr β * (1 + Real.log γ) =
        (1 + isoEbar β * isoM1) * (1 + Real.log γ) +
        C * (2 * isoPhi 1 + 2 * isoEbar β * isoM1) *
          ((1 + Real.log γ) * (1 + Real.log (1 / (2 * isoPhi 1)))) +
        D * isoLbar1 β * (1 + Real.log γ) := by
      dsimp [isoKpr, C, D]
      ring
    rw [heq]
    nlinarith

/-- `thm:app-iso-vol-profile`, snapshot `cr-2026-10-23`, `section.tex` l.2921–2930.

\begin{theorem}[Lag profile at zero ridge]\label{thm:app-iso-vol-profile}
Let $\bmom\in(0,1)$, $\Nin=\Nout=N$ and $\gamma=N/B\ge\gamma^\circ_\bmom$. For every
integer $\ell\ge1$,
\[
-\frac{4\bar{\mathsf e}_\bmom(\mathsf M_1+1)}\gamma\Big(1+\log^+\frac\gamma{4\bar{\mathsf e}_\bmom}\Big)\le\overline C_{1,\ell}(0)-\mathcal G\Big(\frac\ell\gamma\Big)\le\frac{\mathsf K^{\rm pr}_\bmom(1+\log\gamma)}\gamma,
\]
\[
\overline C_{1,\ell}(0)\le\mathsf K^{\rm dec}_\bmom\,e^{-\delta_\bmom(\ell-\gamma)} .
\]
\end{theorem}
-/
theorem thm_app_iso_vol_profile_i {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : isoGammaCirc β ≤ γ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    -(4 * isoEbar β * (isoM1 + 1) / γ)
        * (1 + max (Real.log (γ / (4 * isoEbar β))) 0)
      ≤ lagCoeff β γ 0 ℓ - isoCalG ((ℓ : ℝ) / γ) ∧
    lagCoeff β γ 0 ℓ - isoCalG ((ℓ : ℝ) / γ)
      ≤ isoKpr β * (1 + Real.log γ) / γ := by
  have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
  have hl0 : (0 : ℝ) < ℓ := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hG0 : 0 ≤ γ * isoCalG ((ℓ : ℝ) / γ) := by
    rw [← pF3_profile_integral hl0 hγ0]
    exact intervalIntegral.integral_nonneg hγ0.le (fun _ _ => le_max_right _ _)
  have hG : 0 ≤ isoCalG ((ℓ : ℝ) / γ) := nonneg_of_mul_nonneg_right hG0 hγ0
  have hlag := p10_lag_nonneg hβ0 hβ1 hγ0 (ϱ := 0) le_rfl ℓ
  have he : 0 < isoEbar β := zero_lt_one.trans_le (le_max_left _ _)
  have hM := pF2_M1_nonneg
  have hL := (pF2_L_nonneg hβ0 hβ1).1
  have hΦ : 0 < isoPhi 1 := (lem_app_iso_gaussian_ii.2.2 1 one_pos).1
  have hK3 : 0 ≤ isoK3 β := by unfold isoK3; positivity
  have hK4 : 0 ≤ isoK4 β := by unfold isoK4; positivity
  have hcp := (pF2C_K_nonneg hβ0 hβ1).2.2.2.1
  have hc' : 0 < isoC' β := by
    have hb : 0 < 1 - β ^ 2 := by nlinarith
    unfold isoC'; positivity
  have hγ1 : 1 ≤ γ := by unfold isoGammaCirc at hγ; linarith
  have hlogγ : 0 ≤ Real.log γ := Real.log_nonneg hγ1
  have hlogΦ : 0 ≤ Real.log (1 / (2 * isoPhi 1)) :=
    Real.log_nonneg ((one_le_div (by positivity)).2 (by linarith [pF3_phi_half]))
  have hKpr : 0 ≤ isoKpr β := by unfold isoKpr; positivity
  obtain ⟨F, _hFm, hF0, hF⟩ := pF3_meas hβ0 hβ1 hγ hℓ
  have hb := pF3_profile_bounds hβ0 hβ1 hγ hℓ F hF0 hF
  have hr : ENNReal.ofReal (lagCoeff β γ 0 ℓ) = ENNReal.ofReal (1 / γ) *
      ∫⁻ η in Ioi (0 : ℝ), ∫⁻ w,
        ENNReal.ofReal (F (isoPairMap (isoQlevel β η) w)) ∂isoNuStar := by
    rw [pF3_rep hβ0 hβ1 hγ hℓ]
    congr 1
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro η hη
    apply lintegral_congr
    intro w
    have hs := (pF2_Q_spec hβ0 hβ1 hη).1
    have hp : 0 < (isoPairMap (isoQlevel β η) w).1 ∧
        0 < (isoPairMap (isoQlevel β η) w).2 := by
      unfold isoPairMap
      split_ifs <;> exact ⟨by positivity, by positivity⟩
    have heq := hF _ _ hp.1 hp.2
    simp only [Prod.mk.eta] at heq
    exact congrArg ENNReal.ofReal heq.symm
  constructor
  · have hh := mul_le_mul' (le_refl (ENNReal.ofReal (1 / γ))) hb.1
    rw [mul_add, ← hr, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add hlag (by positivity)] at hh
    have hh' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
    have heqG : 1 / γ * (γ * isoCalG ((ℓ : ℝ) / γ)) = isoCalG ((ℓ : ℝ) / γ) := by
      field_simp
    have heqE : 1 / γ * (4 * isoEbar β * (isoM1 + 1) *
        (1 + max (Real.log (γ / (4 * isoEbar β))) 0)) =
        (4 * isoEbar β * (isoM1 + 1) / γ) *
          (1 + max (Real.log (γ / (4 * isoEbar β))) 0) := by ring
    rw [heqG, heqE] at hh'
    linarith
  · have hh := mul_le_mul' (le_refl (ENNReal.ofReal (1 / γ))) hb.2
    rw [← hr, ← ENNReal.ofReal_mul (by positivity)] at hh
    have hh' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
    have heq : 1 / γ * (γ * isoCalG ((ℓ : ℝ) / γ) + isoKpr β * (1 + Real.log γ)) =
        isoCalG ((ℓ : ℝ) / γ) + isoKpr β * (1 + Real.log γ) / γ := by
      field_simp
    rw [heq] at hh'
    linarith

theorem thm_app_iso_vol_profile_ii {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : isoGammaCirc β ≤ γ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    lagCoeff β γ 0 ℓ ≤ isoKdec β * Real.exp (-(isoDecay β) * ((ℓ : ℝ) - γ)) := by
  have hγ0 := pF2B_gamma_pos hβ0 hβ1 hγ
  have hc' : 0 < isoC' β := by
    have hb : 0 < 1 - β ^ 2 := by nlinarith
    unfold isoC'
    positivity
  have hγ1 : 1 ≤ γ := by unfold isoGammaCirc at hγ; linarith
  have hb : 0 < 1 - β ^ 2 := by nlinarith
  have he : 0 ≤ isoEbar β := zero_le_one.trans (le_max_left _ _)
  have hΦ : 0 < isoPhi 1 := (lem_app_iso_gaussian_ii.2.2 1 one_pos).1
  have hK : 0 ≤ isoK5 β := by unfold isoK5; positivity
  have hcp := (pF2C_K_nonneg hβ0 hβ1).2.2.2.1
  have hδ := (pF3_decay_bounds hβ0 hβ1).1
  have hMe := pF3_Me_pos.le
  have hu := pF3_decay_integral hβ0 hβ1 hγ hℓ
  have hu' : lagCoeff β γ 0 ℓ ≤ (1 / γ) *
      (isoK5 β * (1 + isoCpl β + 1 / isoDecay β) *
        Real.exp (isoDecay β * isoCpl β) *
        Real.exp (-(isoDecay β) * ((ℓ : ℝ) - γ))) * isoMe *
        (γ + 8 / (7 * (1 - β ^ 2))) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hu
  have hq : 0 ≤ 8 / (7 * (1 - β ^ 2)) := by positivity
  have hratio : (γ + 8 / (7 * (1 - β ^ 2))) / γ ≤
      1 + 8 / (7 * (1 - β ^ 2)) + 8 * isoEbar β := by
    rw [add_div, div_self hγ0.ne']
    linarith [div_le_self hq hγ1]
  have hcoef : 0 ≤ isoK5 β * (1 + isoCpl β + 1 / isoDecay β) * isoMe *
      Real.exp (isoDecay β * isoCpl β) *
      Real.exp (-(isoDecay β) * ((ℓ : ℝ) - γ)) := by positivity
  refine hu'.trans ?_
  calc
    _ = (isoK5 β * (1 + isoCpl β + 1 / isoDecay β) * isoMe *
        Real.exp (isoDecay β * isoCpl β) *
        Real.exp (-(isoDecay β) * ((ℓ : ℝ) - γ))) *
        ((γ + 8 / (7 * (1 - β ^ 2))) / γ) := by ring
    _ ≤ (isoK5 β * (1 + isoCpl β + 1 / isoDecay β) * isoMe *
        Real.exp (isoDecay β * isoCpl β) *
        Real.exp (-(isoDecay β) * ((ℓ : ℝ) - γ))) *
        (1 + 8 / (7 * (1 - β ^ 2)) + 8 * isoEbar β) :=
      mul_le_mul_of_nonneg_left hratio hcoef
    _ = _ := by unfold isoKdec; ring

end Muon.Isotropic

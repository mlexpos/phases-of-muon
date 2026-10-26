import Muon.Isotropic.Closure
import Muon.Isotropic.Helpers

/-!
# Appendix F: the zero-ridge constant, participation identity, master estimate and limits

Task L-F.3 (interface). Snapshot `cr-2026-10-23`. Source: `sections/05b-isotropic/section.tex`,
the labels `prop:app-iso-zero` (l.701–718), `lem:app-iso-participation` (l.1296–1314),
`thm:app-iso-master` (l.1387–1402), `prop:app-iso-exact` (l.1738–1743),
`prop:app-iso-limit-order` (l.3619–3632), `prop:app-iso-beta-zero` (l.3682–3693),
`prop:app-iso-one-momentum` (l.3754–3764), `thm:app-iso-zero-ridge` (l.3047–3073; part (i)
only, part (ii) belongs to L-F.10), with the definitions they use (`eqn:app-iso-C` l.663,
`eqn:app-iso-drift-G` l.1061, the participation objects l.1044–1064 and l.1296–1300,
`eqn:app-iso-Xi`, and the inline objects of the statements).

Reuse (never redefined here): `Muon.Isotropic.isoRoot`, `isoGSup`, `isoGPrimeSup`, `isoLambda`,
`isoPhi`, `Muon.emaW`, `Muon.sPow`, `Muon.DetEquiv.rW`, `Muon.DetEquiv.Lw`.

Representation of the branch root: `q(−s)` is `isoRoot (rW (Muon.emaW β)) γin γout s`
(`qIso`), which is the branch value `isoQ s x` by `lem_app_iso_comparison_iii`.
Every theorem is a statement only (`sorry`).
-/

open MeasureTheory Filter Topology Set
open Muon.DetEquiv (Fw Lw rW)

noncomputable section

open scoped Classical

namespace Muon.Isotropic

/-! ## Definitions -/

/-- `q(−s)` at momentum `β` and aspect ratios `γin, γout`: the root of
`s q = (γout − r_β(q))(γin − r_β(q))` in `D_r`, with `r_β = rW (Muon.emaW β)`
(`prop:app-iso-closure`(ii), `lem:app-iso-comparison`(i)). It is `isoRoot` of `Closure.lean`. -/
def qIso (β γin γout s : ℝ) : ℝ :=
  isoRoot (rW (Muon.emaW β)) γin γout s

/-- `ψ(s) = r_β(q(−s)) = q(−s) F_β(q(−s))` (`eqn:app-iso-psi`, l.101), for `s > 0`. -/
def psiIso (β γin γout s : ℝ) : ℝ :=
  rW (Muon.emaW β) (qIso β γin γout s)

/-- `𝖦_β(s) = q(−s) L_β(q(−s))` (`eqn:app-iso-C`, `eqn:app-iso-drift-G`, l.663 and l.1061). -/
def isoGb (β γin γout s : ℝ) : ℝ :=
  qIso β γin γout s * Lw (Muon.emaW β) (qIso β γin γout s)

/-- `𝔡_iso(ϱ)` for `ϱ ≥ 0`: the kernel `eqn:app-iso-drift` at ridge `ϱ`, with `z = ϱ + u²`
(`eqn:app-iso-drift-G`, l.1061). At `ϱ = 0` it is `Cbeta`. -/
def dIso (β γin γout ϱ : ℝ) : ℝ :=
  Real.sqrt 2 / (Real.pi * γin * γout) * ∫ u in Ioi (0 : ℝ), isoGb β γin γout (ϱ + u ^ 2)

/-- `C_β(γin, γout)` (`eqn:app-iso-C`, l.663): `√2/(π γin γout) ∫_0^∞ q(−u²) L_β(q(−u²)) du`.
The square case is `Cbeta β γ γ`; `C(γ) = Cbeta 0 γ γ`. -/
def Cbeta (β γin γout : ℝ) : ℝ :=
  Real.sqrt 2 / (Real.pi * γin * γout) * ∫ u in Ioi (0 : ℝ), isoGb β γin γout (u ^ 2)

/-- `Q_m = r_β^{-1}(m)`: the unique `q ≥ 0` with `r_β(q) = m` (`lem:app-iso-participation`,
l.1296–1300). The `if` is the existence branch; the value is unique where it is used
(`m` in the range of `r_β` on `[0, ∞)`), and `Q_1 = +∞` at `β = 0` is handled by
`isoLambdaB`. -/
def isoQlevel (β m : ℝ) : ℝ :=
  if h : ∃ q : ℝ, 0 ≤ q ∧ rW (Muon.emaW β) q = m then h.choose else 0

/-- `K_β`: the unique `q > 0` with `q F_β(q) = γ∧` for `β > 0`, and `K_0 = 1`
(`prop:app-iso-zero`, l.701–703). The argument is `γ∧`. -/
def isoK (β γmin : ℝ) : ℝ :=
  if β = 0 then 1 else isoQlevel β γmin

/-- `Λ_β(Q_m)`, with the convention `Λ_0(Q_1) := √(2π)` at `β = 0`
(`lem:app-iso-participation`, l.1296–1313). -/
def isoLambdaB (β m : ℝ) : ℝ :=
  if β = 0 ∧ m = 1 then Real.sqrt (2 * Real.pi) else isoLambda β (isoQlevel β m)

/-- `𝗂_β(m) = √(Q_m) L_β(Q_m) + ½ Λ_β(Q_m)` (`lem:app-iso-participation`, l.1296–1300). -/
def isoIlevel (β m : ℝ) : ℝ :=
  Real.sqrt (isoQlevel β m) * Lw (Muon.emaW β) (isoQlevel β m) + (1 / 2) * isoLambdaB β m

/-- `𝖶(m) = √((γin − m)(γout − m))` (`lem:app-iso-participation`, l.1292). -/
def isoWm (γin γout m : ℝ) : ℝ :=
  Real.sqrt ((γin - m) * (γout - m))

/-- `Ĩ(H) = ∫_0^H (−𝖶′(m)) 𝗂_β(m) dm + ½ 𝖶(H) Λ_β(Q_H)` (`lem:app-iso-participation`, l.1296–1300).
The derivative is Lean's `deriv`; `𝖶′` is only needed almost everywhere. -/
def isoIt (β γin γout H : ℝ) : ℝ :=
  (∫ m in (0 : ℝ)..H, -deriv (isoWm γin γout) m * isoIlevel β m)
    + (1 / 2) * isoWm γin γout H * isoLambdaB β H

/-- The participation level `m_ϱ`: `m_ϱ = ψ(ϱ)` for `ϱ > 0`, and `m_0 = γ∧`, except `m_0 = 1`
when `β = 0` and `γ∧ ≥ 1` (`lem:app-iso-participation`, l.1296–1300; `thm:app-iso-master`
uses the convention `ψ(0) = γ∧` for `β ∈ (0,1)`). -/
def isoMLevel (β γin γout ϱ : ℝ) : ℝ :=
  if ϱ = 0 then (if β = 0 ∧ 1 ≤ min γin γout then 1 else min γin γout)
  else psiIso β γin γout ϱ

/-- `Ξ_0(x) = π^{-1/2}(x − x²/2)` (`thm:app-iso-master`(ii), `eqn:app-iso-Xi`). -/
def isoXi0 (x : ℝ) : ℝ :=
  (x - x ^ 2 / 2) / Real.sqrt Real.pi

/-- `𝖥(ι) = ι^{-1} ∫_0^ι √((1−x)(ι−x)) dx` (`thm:app-iso-zero-ridge`(i), l.3047–3073). -/
def isoFiota (ι : ℝ) : ℝ :=
  (1 / ι) * ∫ x in (0 : ℝ)..ι, Real.sqrt ((1 - x) * (ι - x))

/-- `n = ⌊γ⌋` of `prop:app-iso-beta-zero` (l.3682–3693): `γ = n + y`, `n ≥ 0` an integer. -/
def isoNint (γ : ℝ) : ℝ :=
  (⌊γ⌋₊ : ℝ)

/-- `y = γ − ⌊γ⌋` of `prop:app-iso-beta-zero` (l.3682–3693). -/
def isoFrac (γ : ℝ) : ℝ :=
  γ - isoNint γ

/-- `y² C_0(y)`, with the convention `y² C_0(y) := 0` at `y = 0` (`prop:app-iso-beta-zero`). -/
def isoY2C0 (y : ℝ) : ℝ :=
  if y = 0 then 0 else y ^ 2 * Cbeta 0 y y

/-- `C^♯(γ)` of `prop:app-iso-beta-zero` (l.3682–3693): the limit `lim_{β↓0} C_β(γ)` in the
square case. -/
def isoCsharp (γ : ℝ) : ℝ :=
  (isoNint γ * Cbeta 0 1 1 + isoY2C0 (isoFrac γ)) / γ ^ 2
    + (isoNint γ * (isoNint γ - 1) / 2 + isoNint γ * isoFrac γ) / (Real.sqrt Real.pi * γ ^ 2)

/-! ## The zero-ridge constant -/

/-! Private helpers for `prop:app-iso-zero` (task P-F.3.P1). -/

private lemma zr_weightSeq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Muon.DetEquiv.WeightSeq (Muon.emaW β) := by
  refine ⟨fun j => ?_, ?_, 0, ?_⟩
  · unfold Muon.emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  · unfold Muon.emaW
    exact (summable_geometric_of_lt_one hβ0 hβ1).mul_left _
  · unfold Muon.emaW
    rw [pow_zero, mul_one]
    exact (by linarith : (0:ℝ) < 1 - β).ne'

private lemma zr_isoLink {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    IsIsoLink (rW (Muon.emaW β)) := by
  have hw := zr_weightSeq hβ0 hβ1
  refine ⟨ContinuousOn.mul continuousOn_id (Muon.DetEquiv.Fw_admissible hw).contOn,
    (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.1,
    (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.2.1⟩

private lemma zr_emaW_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (j : ℕ) :
    0 ≤ Muon.emaW β j := by
  unfold Muon.emaW
  exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)

private lemma zr_emaW_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Summable (Muon.emaW β) :=
  (summable_geometric_of_lt_one hβ0 hβ1).mul_left _

private lemma zr_J_bounds {x : ℝ} (hx : 0 ≤ x) : 0 < Muon.DetEquiv.J x ∧ Muon.DetEquiv.J x ≤ 1 :=
  Muon.DetEquiv.lem_app_de_scalar_i.2.2.1 x hx

private lemma zr_Lw_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    Summable (fun j : ℕ => Muon.emaW β j * Muon.DetEquiv.J (Muon.emaW β j ^ 2 * q)) := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (zr_emaW_summable hβ0 hβ1)
  · exact mul_nonneg (zr_emaW_nonneg hβ0 hβ1 j)
      (zr_J_bounds (mul_nonneg (sq_nonneg _) hq)).1.le
  · exact mul_le_of_le_one_right (zr_emaW_nonneg hβ0 hβ1 j)
      (zr_J_bounds (mul_nonneg (sq_nonneg _) hq)).2

/-- `Lw_β(q) ≤ 1` for `q ≥ 0` (`J ≤ 1` and `∑_j w_j = 1`). -/
private lemma zr_Lw_le_one {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    Muon.DetEquiv.Lw (Muon.emaW β) q ≤ 1 := by
  calc Muon.DetEquiv.Lw (Muon.emaW β) q
        = ∑' j : ℕ, Muon.emaW β j * Muon.DetEquiv.J (Muon.emaW β j ^ 2 * q) := rfl
    _ ≤ ∑' j : ℕ, Muon.emaW β j :=
        Summable.tsum_le_tsum (fun j => mul_le_of_le_one_right (zr_emaW_nonneg hβ0 hβ1 j)
          (zr_J_bounds (mul_nonneg (sq_nonneg _) hq)).2)
          (zr_Lw_summable hβ0 hβ1 hq) (zr_emaW_summable hβ0 hβ1)
    _ = 1 := Muon.tsum_emaW hβ0 hβ1

/-- `Lw_β(q) > 0` for `q ≥ 0` (the `j = 0` term is positive). -/
private lemma zr_Lw_pos {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    0 < Muon.DetEquiv.Lw (Muon.emaW β) q := by
  have hnn : ∀ j : ℕ, 0 ≤ Muon.emaW β j * Muon.DetEquiv.J (Muon.emaW β j ^ 2 * q) :=
    fun j => mul_nonneg (zr_emaW_nonneg hβ0 hβ1 j)
      (zr_J_bounds (mul_nonneg (sq_nonneg _) hq)).1.le
  unfold Muon.DetEquiv.Lw
  have h0 : 0 < Muon.emaW β 0 := by
    simp only [Muon.emaW, pow_zero, mul_one]
    linarith
  have hpos0 : 0 < Muon.emaW β 0 * Muon.DetEquiv.J (Muon.emaW β 0 ^ 2 * q) :=
    mul_pos h0 (zr_J_bounds (mul_nonneg (sq_nonneg (Muon.emaW β 0)) hq)).1
  have hlt := Summable.tsum_lt_tsum_of_nonneg (i := 0) (f := fun _ : ℕ => (0:ℝ))
    (fun _ => le_rfl) hnn hpos0 (zr_Lw_summable hβ0 hβ1 hq)
  simpa using hlt

private lemma zr_isoDr_swap (r : ℝ → ℝ) (γin γout : ℝ) :
    isoDr r γout γin = isoDr r γin γout := by
  unfold isoDr
  rw [min_comm]

/-- Root of `G_r` for `r` an isotropic link: membership, the equation, and `r(q) < γ∧`. -/
private lemma zr_root_mem {r : ℝ → ℝ} (hr : IsIsoLink r) {γin γout : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) {s : ℝ} (hs : 0 < s) :
    0 ≤ isoRoot r γin γout s ∧ r (isoRoot r γin γout s) < min γin γout ∧
      s * isoRoot r γin γout s
        = (γout - r (isoRoot r γin γout s)) * (γin - r (isoRoot r γin γout s)) := by
  obtain ⟨hD, hG⟩ := (lem_app_iso_comparison_i hr hγin hγout).2.2.2.1 s hs
  have hD' := hD
  simp only [isoDr, Set.mem_setOf_eq] at hD'
  unfold isoG at hG
  exact ⟨hD'.1, hD'.2, by linear_combination hG⟩

/-- Bounds on the root: `0 < q_r(s)` and `q_r(s) · s ≤ γin γout`. -/
private lemma zr_root_bounds {r : ℝ → ℝ} (hr : IsIsoLink r) {γin γout : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) {s : ℝ} (hs : 0 < s) :
    0 < isoRoot r γin γout s ∧ isoRoot r γin γout s * s ≤ γin * γout := by
  obtain ⟨h0, hlt, heq⟩ := zr_root_mem hr hγin hγout hs
  have hr0 : 0 ≤ r (isoRoot r γin γout s) := by
    have hm := hr.2.1.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h0) h0
    rw [hr.2.2] at hm
    exact hm
  have h1 : r (isoRoot r γin γout s) < γout := lt_of_lt_of_le hlt (min_le_right _ _)
  have h2 : r (isoRoot r γin γout s) < γin := lt_of_lt_of_le hlt (min_le_left _ _)
  have ha : 0 < γout - r (isoRoot r γin γout s) := by linarith
  have hb : 0 < γin - r (isoRoot r γin γout s) := by linarith
  have hprod : s * isoRoot r γin γout s ≤ γin * γout := by
    rw [heq, mul_comm γin γout]
    exact mul_le_mul (by linarith) (by linarith) hb.le hγout.le
  refine ⟨?_, by rw [mul_comm]; exact hprod⟩
  rcases h0.lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    have hq0 : isoRoot r γin γout s = 0 := hzero.symm
    have hm : s * isoRoot r γin γout s = 0 := by rw [hq0, mul_zero]
    have : 0 < (γout - r (isoRoot r γin γout s)) * (γin - r (isoRoot r γin γout s)) :=
      mul_pos ha hb
    linarith

/-- The root is symmetric in the two aspect ratios (`lem_app_iso_comparison_i` uniqueness). -/
private lemma zr_isoRoot_swap {r : ℝ → ℝ} (hr : IsIsoLink r) {γin γout : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) {s : ℝ} (hs : 0 < s) :
    isoRoot r γin γout s = isoRoot r γout γin s := by
  have hA := (lem_app_iso_comparison_i hr hγin hγout).2.2.2.1 s hs
  have hB := (lem_app_iso_comparison_i hr hγout hγin).2.2.2.1 s hs
  have hU := (lem_app_iso_comparison_i hr hγout hγin).2.1 s hs
  have hA' : isoRoot r γin γout s ∈ isoDr r γout γin ∧
      isoG r γout γin s (isoRoot r γin γout s) = 0 := by
    rw [zr_isoDr_swap]
    refine ⟨hA.1, ?_⟩
    unfold isoG at hA ⊢
    linear_combination hA.2
  exact (hU.unique hB hA').symm

/-- The branch integrand `t ↦ 𝖦_β(t)` is positive, and `𝖦_β(t) ≤ γin γout / t` (`prop:app-iso-zero`(i)). -/
private lemma zr_isoGb_bounds {β γin γout t : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (ht : 0 < t) :
    0 < isoGb β γin γout t ∧ isoGb β γin γout t ≤ γin * γout / t := by
  have hr := zr_isoLink hβ0 hβ1
  obtain ⟨hq, hqs⟩ := zr_root_bounds hr hγin hγout ht
  unfold isoGb qIso
  refine ⟨mul_pos hq (zr_Lw_pos hβ0 hβ1 hq.le), ?_⟩
  calc isoRoot (rW (Muon.emaW β)) γin γout t * Muon.DetEquiv.Lw (Muon.emaW β)
        (isoRoot (rW (Muon.emaW β)) γin γout t)
      ≤ isoRoot (rW (Muon.emaW β)) γin γout t * 1 :=
        mul_le_mul_of_nonneg_left (zr_Lw_le_one hβ0 hβ1 hq.le) hq.le
    _ = isoRoot (rW (Muon.emaW β)) γin γout t := mul_one _
    _ ≤ γin * γout / t := by rw [le_div_iff₀ ht]; exact hqs

/-- Symmetry `C_β(γin, γout) = C_β(γout, γin)` (`prop:app-iso-zero`(i)). -/
private lemma zr_Cbeta_swap {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (γin γout : ℝ)
    (hγin : 0 < γin) (hγout : 0 < γout) :
    Cbeta β γin γout = Cbeta β γout γin := by
  have hr := zr_isoLink hβ0 hβ1
  have key : ∫ u in Ioi (0 : ℝ), isoGb β γin γout (u ^ 2)
      = ∫ u in Ioi (0 : ℝ), isoGb β γout γin (u ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    have hu' : (0:ℝ) < u ^ 2 := by
      have : (0:ℝ) < u := hu
      positivity
    unfold isoGb qIso
    rw [zr_isoRoot_swap hr hγin hγout hu']
  unfold Cbeta
  rw [key, show Real.pi * γin * γout = Real.pi * γout * γin by ring]

private lemma zr_Lw_zero (q : ℝ) :
    Muon.DetEquiv.Lw (Muon.emaW 0) q = Muon.DetEquiv.J q := by
  unfold Muon.DetEquiv.Lw
  rw [tsum_eq_single 0]
  · simp [Muon.emaW]
  · intro j hj
    simp [Muon.emaW, hj]

/-- The `K_β` bound: `𝖦_β(t) ≤ K_β` (`prop:app-iso-zero`(i)). -/
private lemma zr_isoGb_le_K {β γin γout t : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (ht : 0 < t) :
    isoGb β γin γout t ≤ isoK β (min γin γout) := by
  have hr := zr_isoLink hβ0 hβ1
  obtain ⟨hq, -⟩ := zr_root_bounds hr hγin hγout ht
  obtain ⟨-, hlt, -⟩ := zr_root_mem hr hγin hγout ht
  have hGq : isoGb β γin γout t ≤ isoRoot (rW (Muon.emaW β)) γin γout t := by
    unfold isoGb qIso
    calc _ ≤ isoRoot (rW (Muon.emaW β)) γin γout t * 1 :=
          mul_le_mul_of_nonneg_left (zr_Lw_le_one hβ0 hβ1 hq.le) hq.le
      _ = _ := mul_one _
  rcases hβ0.eq_or_lt with h0 | hpos
  · subst h0
    have hK : isoK 0 (min γin γout) = 1 := by simp [isoK]
    rw [hK]
    unfold isoGb qIso
    rw [zr_Lw_zero]
    exact (lem_app_iso_gaussian_ii.2.2 _ hq).2.le
  · have hne : β ≠ 0 := hpos.ne'
    have hbij := (lem_app_iso_weights_i hβ0 hβ1).2.2.1 hpos
    have hex : ∃ q : ℝ, 0 ≤ q ∧ rW (Muon.emaW β) q = min γin γout := by
      obtain ⟨q, hq, e⟩ := hbij.2.2.2 (show min γin γout ∈ Set.Ici (0:ℝ) from
        Set.mem_Ici.2 (le_min hγin.le hγout.le))
      exact ⟨q, hq, e⟩
    have hKe : isoK β (min γin γout) = isoQlevel β (min γin γout) := if_neg hne
    have hKspec : 0 ≤ isoQlevel β (min γin γout) ∧
        rW (Muon.emaW β) (isoQlevel β (min γin γout)) = min γin γout := by
      unfold isoQlevel
      rw [dif_pos hex]
      exact hex.choose_spec
    rw [hKe]
    refine hGq.trans ?_
    by_contra hcon
    push_neg at hcon
    have hsm := hr.2.1.monotoneOn (Set.mem_Ici.2 hKspec.1) (Set.mem_Ici.2 hq.le) hcon.le
    rw [hKspec.2] at hsm
    exact absurd hlt (not_lt.2 hsm)

private lemma zr_isoGb_contOn {β γin γout : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) :
    ContinuousOn (isoGb β γin γout) (Ioi 0) := by
  have hr := zr_isoLink hβ0 hβ1
  have hq : ContinuousOn (qIso β γin γout) (Ioi 0) :=
    (lem_app_iso_comparison_i hr hγin hγout).2.2.2.2.1
  have hw := zr_weightSeq hβ0 hβ1
  have hL := (Muon.DetEquiv.lem_app_de_scalar_ii hw).2.2.2.1
  show ContinuousOn (fun s => qIso β γin γout s *
    Muon.DetEquiv.Lw (Muon.emaW β) (qIso β γin γout s)) (Ioi 0)
  refine hq.mul (hL.comp hq ?_)
  intro t ht
  exact Set.mem_Ici.2 (zr_root_bounds hr hγin hγout ht).1.le

private lemma zr_integrableOn_of_bound {f : ℝ → ℝ} {K c : ℝ} (hc : 0 < c)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0:ℝ))))
    (hb : ∀ u : ℝ, 0 < u → ‖f u‖ ≤ min K (c / u ^ 2)) :
    IntegrableOn f (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (g := fun _ => K) (integrableOn_const measure_Ioc_lt_top.ne)
      (hf.mono_measure (Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl)) ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc
      (fun u hu => (hb u hu.1).trans (min_le_left _ _))
  · have hI : IntegrableOn (fun u : ℝ => c * u ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul c
    refine Integrable.mono' hI
      (hf.mono_measure (Measure.restrict_mono (Set.Ioi_subset_Ioi zero_le_one) le_rfl)) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => ?_)
    have hu0 : (0:ℝ) < u := lt_trans one_pos hu
    refine (hb u hu0).trans ((min_le_right _ _).trans (le_of_eq ?_))
    rw [Real.rpow_neg hu0.le, Real.rpow_two]
    ring

private lemma zr_integrableOn_shift {β γin γout ϱ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hϱ : 0 ≤ ϱ) :
    IntegrableOn (fun u : ℝ => isoGb β γin γout (ϱ + u ^ 2)) (Ioi 0) := by
  have hcont : ContinuousOn (fun u : ℝ => isoGb β γin γout (ϱ + u ^ 2)) (Ioi 0) := by
    refine (zr_isoGb_contOn hβ0 hβ1 hγin hγout).comp (by fun_prop) ?_
    intro u hu
    have : (0:ℝ) < u := hu
    exact Set.mem_Ioi.2 (by positivity)
  refine zr_integrableOn_of_bound (K := isoK β (min γin γout)) (c := γin * γout)
    (mul_pos hγin hγout) (hcont.aestronglyMeasurable measurableSet_Ioi) (fun u hu => ?_)
  have hp : 0 < ϱ + u ^ 2 := by positivity
  obtain ⟨h1, h2⟩ := zr_isoGb_bounds hβ0 hβ1 hγin hγout hp
  rw [Real.norm_eq_abs, abs_of_pos h1]
  refine le_min (zr_isoGb_le_K hβ0 hβ1 hγin hγout hp) (h2.trans ?_)
  exact div_le_div_of_nonneg_left (mul_pos hγin hγout).le (by positivity) (by linarith)

private lemma zr_subst (G : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * G t = 2 * ∫ u in Ioi (0 : ℝ), G (u ^ 2) := by
  have h := integral_comp_rpow_Ioi_of_pos (g := fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * G t)
    (p := 2) (by norm_num)
  rw [← h, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0:ℝ) < x := hx
  simp only [smul_eq_mul]
  have e1 : (x ^ (2:ℝ)) = x ^ 2 := Real.rpow_two x
  have e2 : (x ^ (2:ℝ)) ^ (-(1 / 2 : ℝ)) = x⁻¹ := by
    rw [← Real.rpow_mul hx0.le]
    norm_num [Real.rpow_neg_one]
  rw [e1] at e2 ⊢
  rw [e2]
  have e3 : x ^ ((2:ℝ) - 1) = x := by norm_num
  rw [e3]
  field_simp

private lemma zr_Cbeta_pos {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {γin γout : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) :
    0 < Cbeta β γin γout := by
  unfold Cbeta
  refine mul_pos (by positivity) ?_
  have hint : IntegrableOn (fun u : ℝ => isoGb β γin γout (u ^ 2)) (Ioi 0) := by
    simpa using zr_integrableOn_shift hβ0 hβ1 hγin hγout (le_refl 0)
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioi
    (fun u hu => ?_)) hint]
  · have hsub : Ioi (0:ℝ) ⊆ Function.support (fun u : ℝ => isoGb β γin γout (u ^ 2)) ∩ Ioi 0 := by
      intro u hu
      have hu0 : (0:ℝ) < u := hu
      refine ⟨?_, hu⟩
      exact (zr_isoGb_bounds hβ0 hβ1 hγin hγout (by positivity : (0:ℝ) < u ^ 2)).1.ne'
    exact lt_of_lt_of_le (by simp) (measure_mono hsub)
  · have hu0 : (0:ℝ) < u := hu
    exact (zr_isoGb_bounds hβ0 hβ1 hγin hγout (by positivity : (0:ℝ) < u ^ 2)).1.le

private lemma zr_shift_bound {β γin γout ϱ u : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hϱ : 0 ≤ ϱ) (hu : 0 < u) :
    ‖isoGb β γin γout (ϱ + u ^ 2)‖ ≤ min (isoK β (min γin γout)) (γin * γout / u ^ 2) := by
  have hp : 0 < ϱ + u ^ 2 := by positivity
  obtain ⟨h1, h2⟩ := zr_isoGb_bounds hβ0 hβ1 hγin hγout hp
  rw [Real.norm_eq_abs, abs_of_pos h1]
  refine le_min (zr_isoGb_le_K hβ0 hβ1 hγin hγout hp) (h2.trans ?_)
  exact div_le_div_of_nonneg_left (mul_pos hγin hγout).le (by positivity) (by linarith)

private lemma zr_shift_aesm {β γin γout ϱ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hϱ : 0 ≤ ϱ) :
    AEStronglyMeasurable (fun u : ℝ => isoGb β γin γout (ϱ + u ^ 2))
      (volume.restrict (Ioi (0:ℝ))) := by
  have hcont : ContinuousOn (fun u : ℝ => isoGb β γin γout (ϱ + u ^ 2)) (Ioi 0) := by
    refine (zr_isoGb_contOn hβ0 hβ1 hγin hγout).comp (by fun_prop) ?_
    intro u hu
    have : (0:ℝ) < u := hu
    exact Set.mem_Ioi.2 (by positivity)
  exact hcont.aestronglyMeasurable measurableSet_Ioi

private lemma zr_isoK_pos {β γin γout : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) : 0 < isoK β (min γin γout) :=
  lt_of_lt_of_le (zr_isoGb_bounds hβ0 hβ1 hγin hγout one_pos).1
    (zr_isoGb_le_K hβ0 hβ1 hγin hγout one_pos)

/-! ## The zero-ridge constant -/

/-- `prop:app-iso-zero`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.701–718):
```latex
\begin{proposition}[The zero-ridge constant]\label{prop:app-iso-zero}
Let $\bmom\in[0,1)$ and $\gin,\gout>0$. Put $K_0\defeq1$, and for $\bmom>0$
let $K_\bmom$ be the unique $q>0$ with $q\Fw(q)=\min(\gin,\gout)$.
\begin{enumerate}[label=(\roman*)]
\item For every $t>0$,
\[
0<q(-t)\,\Lw\big(q(-t)\big)\le\min\Big(K_\bmom,\frac{\gin\gout}{t}\Big),
\]
so the integral \cref{eqn:app-iso-C} converges and $0<C_\bmom(\gin,\gout)<\infty$.
Moreover $C_\bmom(\gin,\gout)=C_\bmom(\gout,\gin)$, and
\begin{equation}\label{eqn:app-iso-C-t}
C_\bmom(\gin,\gout)=\frac{1}{\sqrt2\,\pi\,\gin\gout}\int_0^\infty t^{-1/2}\,q(-t)\,\Lw\big(q(-t)\big)\,\dif t .
\end{equation}
\item Let $\mathfrak d_{\mathrm{iso}}(\ridge)$ be the kernel \cref{eqn:app-iso-drift}
at momentum $\bmom$, for the measures \cref{eqn:app-iso-measures}. Then, at this
fixed $\bmom$, $\mathfrak d_{\mathrm{iso}}(\ridge)\to C_\bmom(\gin,\gout)$ as $\ridge\downarrow0$.
\end{enumerate}
\end{proposition}
```

Part (i). Encoding: `q(−t)` is `qIso β γin γout t`; `K_β` is `isoK β (min γin γout)`; `C_β` is
`Cbeta`. The integrability and the positivity are the convergence claim of (i). -/
theorem prop_app_iso_zero_i {β γin γout : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) :
    (∀ t : ℝ, 0 < t → 0 < isoGb β γin γout t ∧
      isoGb β γin γout t ≤ min (isoK β (min γin γout)) (γin * γout / t)) ∧
    IntegrableOn (fun u : ℝ => isoGb β γin γout (u ^ 2)) (Ioi 0) ∧
    0 < Cbeta β γin γout ∧
    Cbeta β γin γout = Cbeta β γout γin ∧
    Cbeta β γin γout = 1 / (Real.sqrt 2 * Real.pi * γin * γout)
      * ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * isoGb β γin γout t := by
  refine ⟨fun t ht => ⟨(zr_isoGb_bounds hβ0 hβ1 hγin hγout ht).1,
    le_min (zr_isoGb_le_K hβ0 hβ1 hγin hγout ht)
      (zr_isoGb_bounds hβ0 hβ1 hγin hγout ht).2⟩, ?_,
    zr_Cbeta_pos hβ0 hβ1 hγin hγout, zr_Cbeta_swap hβ0 hβ1 γin γout hγin hγout, ?_⟩
  · simpa using zr_integrableOn_shift hβ0 hβ1 hγin hγout (le_refl 0)
  · unfold Cbeta
    rw [zr_subst]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hp := Real.pi_pos
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
    ring

/-- `prop:app-iso-zero`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.701–718):
```latex
\begin{proposition}[The zero-ridge constant]\label{prop:app-iso-zero}
Let $\bmom\in[0,1)$ and $\gin,\gout>0$. Put $K_0\defeq1$, and for $\bmom>0$
let $K_\bmom$ be the unique $q>0$ with $q\Fw(q)=\min(\gin,\gout)$.
\begin{enumerate}[label=(\roman*)]
\item For every $t>0$,
\[
0<q(-t)\,\Lw\big(q(-t)\big)\le\min\Big(K_\bmom,\frac{\gin\gout}{t}\Big),
\]
so the integral \cref{eqn:app-iso-C} converges and $0<C_\bmom(\gin,\gout)<\infty$.
Moreover $C_\bmom(\gin,\gout)=C_\bmom(\gout,\gin)$, and
\begin{equation}\label{eqn:app-iso-C-t}
C_\bmom(\gin,\gout)=\frac{1}{\sqrt2\,\pi\,\gin\gout}\int_0^\infty t^{-1/2}\,q(-t)\,\Lw\big(q(-t)\big)\,\dif t .
\end{equation}
\item Let $\mathfrak d_{\mathrm{iso}}(\ridge)$ be the kernel \cref{eqn:app-iso-drift}
at momentum $\bmom$, for the measures \cref{eqn:app-iso-measures}. Then, at this
fixed $\bmom$, $\mathfrak d_{\mathrm{iso}}(\ridge)\to C_\bmom(\gin,\gout)$ as $\ridge\downarrow0$.
\end{enumerate}
\end{proposition}
```

Part (ii). The limit `ϱ ↓ 0` of `dIso` is `Cbeta`, at the fixed momentum `β`. -/
theorem prop_app_iso_zero_ii {β γin γout : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) :
    Tendsto (fun ϱ : ℝ => dIso β γin γout ϱ) (𝓝[>] (0 : ℝ)) (𝓝 (Cbeta β γin γout)) := by
  unfold dIso Cbeta
  refine Tendsto.const_mul _ ?_
  have hK := zr_isoK_pos hβ0 hβ1 hγin hγout
  have hbI : IntegrableOn (fun u : ℝ => min (isoK β (min γin γout)) (γin * γout / u ^ 2))
      (Ioi 0) := by
    refine zr_integrableOn_of_bound (K := isoK β (min γin γout)) (c := γin * γout)
      (mul_pos hγin hγout) ?_ (fun u hu => ?_)
    · exact (Measurable.min measurable_const (by fun_prop)).aestronglyMeasurable
    · have : 0 ≤ min (isoK β (min γin γout)) (γin * γout / u ^ 2) :=
        le_min hK.le (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg this]
  refine tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0:ℝ)))
    (fun u => min (isoK β (min γin γout)) (γin * γout / u ^ 2)) ?_ ?_ hbI ?_
  · filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
    exact zr_shift_aesm hβ0 hβ1 hγin hγout (le_of_lt hϱ)
  · filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
    exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun u hu => zr_shift_bound hβ0 hβ1 hγin hγout (le_of_lt hϱ) hu)
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => ?_)
    have hu0 : (0:ℝ) < u := hu
    have hu2 : (0:ℝ) < u ^ 2 := by positivity
    have hca : ContinuousAt (isoGb β γin γout) (u ^ 2) :=
      (zr_isoGb_contOn hβ0 hβ1 hγin hγout).continuousAt (Ioi_mem_nhds hu2)
    have hlim : Tendsto (fun ϱ : ℝ => ϱ + u ^ 2) (𝓝[>] (0:ℝ)) (𝓝 (u ^ 2)) := by
      have := ((continuous_id.add_const (u ^ 2)).tendsto (0:ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
      simpa using this
    exact hca.tendsto.comp hlim

/-! Private helpers for `lem:app-iso-participation` (task P-F.3.P2). -/

private lemma zr2_rd {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ d : ℝ → ℝ, ∀ q : ℝ, 0 < q → HasDerivAt (rW (Muon.emaW β)) (d q) q ∧ 0 < d q := by
  have h := Muon.DetEquiv.lem_app_de_scalar_iii (zr_weightSeq hβ0 hβ1)
  exact ⟨fun q => ∑' j, Muon.emaW β j ^ 2 *
      ∫ g, g ^ 2 / (1 + Muon.emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1),
    fun q hq => ⟨h.2.2.2.1 q hq, h.2.2.2.2.1 q hq⟩⟩

private lemma zr2_Qlevel_r {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    isoQlevel β (rW (Muon.emaW β) q) = q := by
  have hr := zr_isoLink hβ0 hβ1
  have hex : ∃ c : ℝ, 0 ≤ c ∧ rW (Muon.emaW β) c = rW (Muon.emaW β) q := ⟨q, hq, rfl⟩
  unfold isoQlevel
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  exact hr.2.1.injOn (Set.mem_Ici.2 h1) (Set.mem_Ici.2 hq) h2

private lemma zr2_Qlevel_nonneg (β m : ℝ) : 0 ≤ isoQlevel β m := by
  unfold isoQlevel
  split_ifs with h
  · exact h.choose_spec.1
  · exact le_rfl

private lemma zr2_lam_ii {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW β) x) volume 0 b := by
  have hL := (Muon.DetEquiv.lem_app_de_scalar_ii (zr_weightSeq hβ0 hβ1)).2.2.2.1
  have hint : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 b :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb] at hint ⊢
  refine Integrable.mono' hint ?_ ?_
  · have : ContinuousOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW β) x) (Ioc 0 b) := by
      refine ContinuousOn.mul ?_ (hL.mono ?_)
      · exact fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl hx.1.ne')).continuousWithinAt
      · exact fun x hx => Set.mem_Ici.2 hx.1.le
    exact this.aestronglyMeasurable measurableSet_Ioc
  · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => ?_)
    have hx0 : 0 < x := hx.1
    have h1 := zr_Lw_pos hβ0 hβ1 hx0.le
    have h2 := zr_Lw_le_one hβ0 hβ1 hx0.le
    have h3 : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos h3 h1)]
    exact mul_le_of_le_one_right h3.le h2

private lemma zr2_lam_zero (β : ℝ) : isoLambda β 0 = 0 := by
  simp [isoLambda]

private lemma zr2_lam_cont {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ContinuousOn (isoLambda β) (Ici 0) := by
  intro b hb
  have hb0 : (0:ℝ) ≤ b := hb
  have h := intervalIntegral.continuousOn_primitive_interval'
    (zr2_lam_ii hβ0 hβ1 (by linarith : (0:ℝ) ≤ b + 1))
    (by rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ b + 1)]; exact ⟨le_rfl, by linarith⟩ : (0:ℝ) ∈ Set.uIcc 0 (b + 1))
  have hb' : b ∈ Set.uIcc (0:ℝ) (b + 1) := by
    rw [Set.uIcc_of_le (by linarith)]; exact ⟨hb0, by linarith⟩
  refine (h b hb').mono_of_mem_nhdsWithin ?_
  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ b + 1)]
  exact mem_nhdsWithin.2 ⟨Iio (b + 1), isOpen_Iio, by simp, fun x hx => ⟨hx.2, hx.1.le⟩⟩

private lemma zr2_lam_deriv {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (isoLambda β) (q ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW β) q) q := by
  have hL := (Muon.DetEquiv.lem_app_de_scalar_ii (zr_weightSeq hβ0 hβ1)).2.2.2.1
  have hco : ContinuousOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW β) x) (Ioi 0) := by
    refine ContinuousOn.mul ?_ (hL.mono ?_)
    · exact fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx))).continuousWithinAt
    · exact fun x hx => Set.mem_Ici.2 (le_of_lt hx)
  exact intervalIntegral.integral_hasDerivAt_right (zr2_lam_ii hβ0 hβ1 hq.le)
    (hco.stronglyMeasurableAtFilter isOpen_Ioi q hq) (hco.continuousAt (Ioi_mem_nhds hq))

private lemma zr2_W_sq {γin γout m : ℝ} (hm : m < min γin γout) :
    isoWm γin γout m ^ 2 = (γin - m) * (γout - m) := by
  have h1 : 0 < γin - m := by have := min_le_left γin γout; linarith
  have h2 : 0 < γout - m := by have := min_le_right γin γout; linarith
  unfold isoWm
  exact Real.sq_sqrt (mul_pos h1 h2).le

private lemma zr2_W_pos {γin γout m : ℝ} (hm : m < min γin γout) :
    0 < isoWm γin γout m := by
  have h1 : 0 < γin - m := by have := min_le_left γin γout; linarith
  have h2 : 0 < γout - m := by have := min_le_right γin γout; linarith
  unfold isoWm
  exact Real.sqrt_pos.2 (mul_pos h1 h2)

private lemma zr2_W_anti {γin γout m₁ m₂ : ℝ} (h : m₁ ≤ m₂) (hm : m₂ < min γin γout) :
    isoWm γin γout m₂ ≤ isoWm γin γout m₁ := by
  have h1 : 0 < γin - m₂ := by have := min_le_left γin γout; linarith
  have h2 : 0 < γout - m₂ := by have := min_le_right γin γout; linarith
  unfold isoWm
  exact Real.sqrt_le_sqrt (mul_le_mul (by linarith) (by linarith) h2.le (by linarith))

private lemma zr2_W_cont (γin γout : ℝ) : Continuous (isoWm γin γout) := by
  unfold isoWm
  fun_prop

private lemma zr2_W_deriv {γin γout m : ℝ} (hm : m < min γin γout) :
    HasDerivAt (isoWm γin γout)
      (-((γout - m) + (γin - m)) / (2 * isoWm γin γout m)) m := by
  have hp := zr2_W_pos hm
  have h1 : HasDerivAt (fun x : ℝ => (γin - x) * (γout - x))
      (-(γout - m) + (γin - m) * (-1)) m := by
    have a : HasDerivAt (fun x : ℝ => γin - x) (-1) m := by
      simpa using (hasDerivAt_id m).const_sub γin
    have b : HasDerivAt (fun x : ℝ => γout - x) (-1) m := by
      simpa using (hasDerivAt_id m).const_sub γout
    exact (a.mul b).congr_deriv (by ring)
  have h2 := h1.sqrt (by
    have := zr2_W_sq hm
    intro h0; rw [h0] at this; nlinarith)
  unfold isoWm
  convert h2 using 1
  ring

private lemma zr2_W_deriv_nonpos {γin γout m : ℝ} (hm : m < min γin γout) :
    deriv (isoWm γin γout) m ≤ 0 := by
  rw [(zr2_W_deriv hm).deriv]
  have h1 : 0 < γin - m := by have := min_le_left γin γout; linarith
  have h2 : 0 < γout - m := by have := min_le_right γin γout; linarith
  have hp := zr2_W_pos hm
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

private lemma zr2_r_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    rW (Muon.emaW β) a ≤ rW (Muon.emaW β) b :=
  (zr_isoLink hβ0 hβ1).2.1.monotoneOn (Set.mem_Ici.2 ha) (Set.mem_Ici.2 (ha.trans hab)) hab

private lemma zr2_r_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ rW (Muon.emaW β) a := by
  have := zr2_r_le hβ0 hβ1 le_rfl ha
  rwa [(zr_isoLink hβ0 hβ1).2.2] at this

/-- `T(q) = 𝖶(r(q))/√q` is strictly decreasing on `(0,b]`. -/
private lemma zr2_T_anti {β γin γout b : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hrb : rW (Muon.emaW β) b < min γin γout) {q₁ q₂ : ℝ} (h1 : 0 < q₁) (h12 : q₁ < q₂)
    (h2 : q₂ ≤ b) :
    isoWm γin γout (rW (Muon.emaW β) q₂) / Real.sqrt q₂ <
      isoWm γin γout (rW (Muon.emaW β) q₁) / Real.sqrt q₁ := by
  have hr2 : rW (Muon.emaW β) q₂ < min γin γout :=
    lt_of_le_of_lt (zr2_r_le hβ0 hβ1 (by linarith) h2) hrb
  have hW2 := zr2_W_pos hr2
  have hW := zr2_W_anti (γin := γin) (γout := γout) (zr2_r_le hβ0 hβ1 h1.le h12.le) hr2
  have hs1 : 0 < Real.sqrt q₁ := Real.sqrt_pos.2 h1
  have hs : Real.sqrt q₁ < Real.sqrt q₂ := Real.sqrt_lt_sqrt h1.le h12
  calc isoWm γin γout (rW (Muon.emaW β) q₂) / Real.sqrt q₂
      < isoWm γin γout (rW (Muon.emaW β) q₂) / Real.sqrt q₁ :=
        div_lt_div_of_pos_left hW2 hs1 hs
    _ ≤ _ := div_le_div_of_nonneg_right hW hs1.le

private lemma zr2_T_cont {β γin γout : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ContinuousOn (fun q : ℝ => isoWm γin γout (rW (Muon.emaW β) q) / Real.sqrt q) (Ioi 0) := by
  have hr := (zr_isoLink hβ0 hβ1).1
  refine ContinuousOn.div ((zr2_W_cont γin γout).comp_continuousOn (hr.mono ?_))
    Real.continuous_sqrt.continuousOn ?_
  · exact fun x hx => Set.mem_Ici.2 (le_of_lt hx)
  · exact fun x hx => (Real.sqrt_pos.2 hx).ne'

/-- The image of `(0,b)` under `T` is `(T b, ∞)`. -/
private lemma zr2_T_image {β γin γout b : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hb : 0 < b)
    (hrb : rW (Muon.emaW β) b < min γin γout) :
    (fun q : ℝ => isoWm γin γout (rW (Muon.emaW β) q) / Real.sqrt q) '' Ioo 0 b =
      Ioi (isoWm γin γout (rW (Muon.emaW β) b) / Real.sqrt b) := by
  set T := fun q : ℝ => isoWm γin γout (rW (Muon.emaW β) q) / Real.sqrt q with hT
  ext t
  simp only [Set.mem_image, Set.mem_Ioo, Set.mem_Ioi]
  constructor
  · rintro ⟨q, ⟨hq0, hqb⟩, rfl⟩
    exact zr2_T_anti hβ0 hβ1 hrb hq0 hqb le_rfl
  · intro ht
    have hWb := zr2_W_pos hrb
    have hTb : 0 < T b := div_pos hWb (Real.sqrt_pos.2 hb)
    have ht0 : 0 < t := hTb.trans ht
    set ε := min (b / 2) ((isoWm γin γout (rW (Muon.emaW β) b) / t) ^ 2) with hε
    have hε0 : 0 < ε := lt_min (by linarith) (by positivity)
    have hεb : ε < b := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hTε : t ≤ T ε := by
      have hrε : rW (Muon.emaW β) ε < min γin γout :=
        lt_of_le_of_lt (zr2_r_le hβ0 hβ1 hε0.le hεb.le) hrb
      have hW := zr2_W_anti (γin := γin) (γout := γout) (zr2_r_le hβ0 hβ1 hε0.le hεb.le) hrb
      have hsε : Real.sqrt ε ≤ isoWm γin γout (rW (Muon.emaW β) b) / t := by
        calc Real.sqrt ε ≤ Real.sqrt ((isoWm γin γout (rW (Muon.emaW β) b) / t) ^ 2) :=
              Real.sqrt_le_sqrt (min_le_right _ _)
          _ = _ := Real.sqrt_sq (by positivity)
      have hsε0 : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε0
      rw [le_div_iff₀ hsε0]
      calc t * Real.sqrt ε ≤ t * (isoWm γin γout (rW (Muon.emaW β) b) / t) :=
            mul_le_mul_of_nonneg_left hsε ht0.le
        _ = isoWm γin γout (rW (Muon.emaW β) b) := by field_simp
        _ ≤ _ := hW
    have hcont : ContinuousOn T (Icc ε b) :=
      (zr2_T_cont (γin := γin) (γout := γout) hβ0 hβ1).mono
        (fun x hx => lt_of_lt_of_le hε0 hx.1)
    obtain ⟨q, hq, hqt⟩ := intermediate_value_Icc' hεb.le hcont ⟨ht.le, hTε⟩
    have hqb : q ≠ b := by
      rintro rfl
      exact absurd hqt (ne_of_lt ht)
    exact ⟨q, ⟨lt_of_lt_of_le hε0 hq.1, lt_of_le_of_ne hq.2 hqb⟩, hqt⟩

/-- Key identity: `𝖦_β(T(q)²) = q Lw(q)` for `0 < q ≤ b`. -/
private lemma zr2_G_T {β γin γout b q : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout)
    (hrb : rW (Muon.emaW β) b < min γin γout) (hq : 0 < q) (hqb : q ≤ b) :
    isoGb β γin γout ((isoWm γin γout (rW (Muon.emaW β) q) / Real.sqrt q) ^ 2)
      = q * Lw (Muon.emaW β) q := by
  have hr := zr_isoLink hβ0 hβ1
  have hrq : rW (Muon.emaW β) q < min γin γout :=
    lt_of_le_of_lt (zr2_r_le hβ0 hβ1 hq.le hqb) hrb
  have hW := zr2_W_pos hrq
  have hs : 0 < (isoWm γin γout (rW (Muon.emaW β) q) / Real.sqrt q) ^ 2 := by
    have := Real.sqrt_pos.2 hq
    positivity
  have hroot : isoRoot (rW (Muon.emaW β)) γin γout
      ((isoWm γin γout (rW (Muon.emaW β) q) / Real.sqrt q) ^ 2) = q := by
    have hU := (lem_app_iso_comparison_i hr hγin hγout).2.1 _ hs
    refine (hU.unique ((lem_app_iso_comparison_i hr hγin hγout).2.2.2.1 _ hs) ?_)
    refine ⟨⟨hq.le, hrq⟩, ?_⟩
    unfold isoG
    rw [div_pow, Real.sq_sqrt hq.le, zr2_W_sq hrq]
    field_simp
    ring
  unfold isoGb qIso
  rw [hroot]

private lemma zr2_w_deriv {β γin γout : ℝ} {d : ℝ → ℝ}
    (hd : ∀ q : ℝ, 0 < q → HasDerivAt (rW (Muon.emaW β)) (d q) q) {q : ℝ} (hq : 0 < q)
    (hrq : rW (Muon.emaW β) q < min γin γout) :
    HasDerivAt (fun x => isoWm γin γout (rW (Muon.emaW β) x))
      (deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q) q := by
  have h := (zr2_W_deriv hrq)
  rw [h.deriv]
  exact h.comp q (hd q hq)

/-- Integration by parts in `q` on `(0,b]`. -/
private lemma zr2_ibp {β γin γout b : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {d : ℝ → ℝ}
    (hd : ∀ q : ℝ, 0 < q → HasDerivAt (rW (Muon.emaW β)) (d q) q ∧ 0 < d q)
    (hb : 0 < b) (hrb : rW (Muon.emaW β) b < min γin γout) :
    (∫ q in Ioc 0 b, ((1 / 2) * isoWm γin γout (rW (Muon.emaW β) q) *
        (q ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW β) q)
      + (-(deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q)) *
        (Real.sqrt q * Lw (Muon.emaW β) q)))
      = (1 / 2) * isoWm γin γout (rW (Muon.emaW β) b) * isoLambda β b
        + ∫ q in Ioc 0 b, (-(deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q)) *
            (Real.sqrt q * Lw (Muon.emaW β) q + (1 / 2) * isoLambda β q) := by
  have hr := zr_isoLink hβ0 hβ1
  have hL := (Muon.DetEquiv.lem_app_de_scalar_ii (zr_weightSeq hβ0 hβ1)).2.2.2.1
  have hlam := zr2_lam_cont hβ0 hβ1
  have hrq : ∀ q, q ∈ Icc 0 b → rW (Muon.emaW β) q < min γin γout := fun q hq =>
    lt_of_le_of_lt (zr2_r_le hβ0 hβ1 hq.1 hq.2) hrb
  -- continuity of w on [0,b]
  have hwc : ContinuousOn (fun x => isoWm γin γout (rW (Muon.emaW β) x)) (Icc 0 b) :=
    (zr2_W_cont γin γout).comp_continuousOn (hr.1.mono (fun x hx => Set.mem_Ici.2 hx.1))
  have hwd : ∀ q ∈ Ioo 0 b, HasDerivAt (fun x => isoWm γin γout (rW (Muon.emaW β) x))
      (deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q) q := fun q hq =>
    zr2_w_deriv (fun q hq => (hd q hq).1) hq.1 (hrq q ⟨hq.1.le, hq.2.le⟩)
  -- -wd integrable
  have hnn : ∀ q ∈ Ioo 0 b, 0 ≤ -(deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q) := by
    intro q hq
    have h1 := zr2_W_deriv_nonpos (hrq q ⟨hq.1.le, hq.2.le⟩)
    have h2 := (hd q hq.1).2
    nlinarith
  have hwdint : IntegrableOn (fun q => -(deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q))
      (Ioc 0 b) := by
    refine intervalIntegral.integrableOn_deriv_of_nonneg (g := fun x => -isoWm γin γout
      (rW (Muon.emaW β) x)) hwc.neg (fun q hq => (hwd q hq).neg) hnn
  have hK : IsCompact (Icc (0:ℝ) b) := isCompact_Icc
  have hsub : Ioc (0:ℝ) b ⊆ Icc 0 b := Ioc_subset_Icc_self
  have hLc : ContinuousOn (fun q => Real.sqrt q * Lw (Muon.emaW β) q) (Icc 0 b) :=
    Real.continuous_sqrt.continuousOn.mul (hL.mono (fun x hx => Set.mem_Ici.2 hx.1))
  have hLc2 : ContinuousOn (fun q => Real.sqrt q * Lw (Muon.emaW β) q +
      (1 / 2) * isoLambda β q) (Icc 0 b) :=
    hLc.add (continuousOn_const.mul (hlam.mono (fun x hx => Set.mem_Ici.2 hx.1)))
  have hI1 : IntegrableOn (fun q => (-(deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q)) *
      (Real.sqrt q * Lw (Muon.emaW β) q)) (Ioc 0 b) :=
    hwdint.mul_continuousOn_of_subset hLc measurableSet_Ioc hK hsub
  have hI2 : IntegrableOn (fun q => (-(deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q)) *
      (isoLambda β q)) (Ioc 0 b) :=
    hwdint.mul_continuousOn_of_subset (hlam.mono (fun x hx => Set.mem_Ici.2 hx.1))
      measurableSet_Ioc hK hsub
  have hlamint : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW β) x) (Ioc 0 b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).1 (zr2_lam_ii hβ0 hβ1 hb.le)
  have hI3 : IntegrableOn (fun q => isoWm γin γout (rW (Muon.emaW β) q) *
      (q ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW β) q)) (Ioc 0 b) :=
    hlamint.continuousOn_mul_of_subset hwc hK measurableSet_Ioc hsub
  have h1 : IntegrableOn (fun q => (deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q) *
      isoLambda β q) (Ioc 0 b) := by
    refine IntegrableOn.congr_fun hI2.neg (fun q _ => ?_) measurableSet_Ioc
    simp
  -- FTC for P = w * Λ
  have hP : ∫ q in (0:ℝ)..b, ((deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q) * isoLambda β q
      + isoWm γin γout (rW (Muon.emaW β) q) * (q ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW β) q))
      = isoWm γin γout (rW (Muon.emaW β) b) * isoLambda β b := by
    have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (a := 0) (b := b)
      (f := fun q => isoWm γin γout (rW (Muon.emaW β) q) * isoLambda β q)
      (f' := fun q => (deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q) * isoLambda β q
        + isoWm γin γout (rW (Muon.emaW β) q) * (q ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW β) q))
      hb.le (hwc.mul (hlam.mono (fun x hx => Set.mem_Ici.2 hx.1)))
      (fun q hq => ((hwd q hq).mul (zr2_lam_deriv hβ0 hβ1 hq.1)).hasDerivWithinAt) ?_
    · rw [this, zr2_lam_zero]
      ring
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
      exact h1.add hI3
  rw [intervalIntegral.integral_of_le hb.le, integral_add h1 hI3] at hP
  have hI3' : ∫ q in Ioc 0 b, (1 / 2) * isoWm γin γout (rW (Muon.emaW β) q) *
        (q ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW β) q)
      = (1 / 2) * ∫ q in Ioc 0 b, isoWm γin γout (rW (Muon.emaW β) q) *
        (q ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW β) q) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun q => ?_))
    simp only
    ring
  have hI2' : ∫ q in Ioc 0 b, (-(deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q)) *
        (Real.sqrt q * Lw (Muon.emaW β) q + (1 / 2) * isoLambda β q)
      = (∫ q in Ioc 0 b, (-(deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q)) *
          (Real.sqrt q * Lw (Muon.emaW β) q))
        - (1 / 2) * ∫ q in Ioc 0 b, (deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q) *
          isoLambda β q := by
    rw [← integral_const_mul, ← integral_sub hI1 (h1.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun q => ?_))
    simp only
    ring
  have hI3c : IntegrableOn (fun q => (1 / 2) * isoWm γin γout (rW (Muon.emaW β) q) *
      (q ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW β) q)) (Ioc 0 b) := by
    refine IntegrableOn.congr_fun (hI3.const_mul (1 / 2)) (fun q _ => ?_) measurableSet_Ioc
    ring
  rw [integral_add hI3c hI1, hI3', hI2']
  linarith

private lemma zr2_rpow_neg_half {q : ℝ} (hq : 0 < q) : q ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt q := by
  rw [Real.rpow_neg hq.le, ← Real.sqrt_eq_rpow, one_div]

/-- Change of variables `t = T(q)`. -/
private lemma zr2_cov_t {β γin γout b : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {d : ℝ → ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout)
    (hd : ∀ q : ℝ, 0 < q → HasDerivAt (rW (Muon.emaW β)) (d q) q ∧ 0 < d q)
    (hb : 0 < b) (hrb : rW (Muon.emaW β) b < min γin γout) :
    ∫ t in Ioi (isoWm γin γout (rW (Muon.emaW β) b) / Real.sqrt b),
        isoGb β γin γout (t ^ 2)
      = ∫ q in Ioc 0 b, ((1 / 2) * isoWm γin γout (rW (Muon.emaW β) q) *
        (q ^ (-(1 / 2 : ℝ)) * Lw (Muon.emaW β) q)
      + (-(deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q)) *
        (Real.sqrt q * Lw (Muon.emaW β) q)) := by
  have hrq : ∀ q, 0 < q → q ≤ b → rW (Muon.emaW β) q < min γin γout := fun q hq hqb =>
    lt_of_le_of_lt (zr2_r_le hβ0 hβ1 hq.le hqb) hrb
  set T := fun q : ℝ => isoWm γin γout (rW (Muon.emaW β) q) / Real.sqrt q with hT
  let T' : ℝ → ℝ := fun q =>
    ((deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q) * Real.sqrt q
      - isoWm γin γout (rW (Muon.emaW β) q) * (1 / (2 * Real.sqrt q))) / Real.sqrt q ^ 2
  have hTd : ∀ q ∈ Ioo 0 b, HasDerivWithinAt T (T' q) (Ioo 0 b) q := by
    intro q hq
    have hq0 : 0 < q := hq.1
    have h1 := zr2_w_deriv (fun q hq => (hd q hq).1) hq0 (hrq q hq0 hq.2.le)
    have h2 := Real.hasDerivAt_sqrt hq0.ne'
    exact (h1.div h2 (Real.sqrt_pos.2 hq0).ne').hasDerivWithinAt
  have hinj : InjOn T (Ioo 0 b) := by
    intro x hx y hy hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hxy (ne_of_gt (zr2_T_anti hβ0 hβ1 hrb hx.1 h hy.2.le))
    · exact absurd hxy (ne_of_lt (zr2_T_anti hβ0 hβ1 hrb hy.1 h hx.2.le))
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Ioo 0 b) measurableSet_Ioo
    hTd hinj (fun t => isoGb β γin γout (t ^ 2))
  rw [zr2_T_image hβ0 hβ1 hb hrb] at hcov
  rw [hcov, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo (fun q hq => ?_)
  have hq0 : 0 < q := hq.1
  have hrq' := hrq q hq0 hq.2.le
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hs2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
  have hW := zr2_W_pos hrq'
  have hwd := zr2_W_deriv_nonpos hrq'
  have hdpos := (hd q hq0).2
  have hneg : T' q ≤ 0 := by
    have : (deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q) * Real.sqrt q ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hwd hdpos.le) hs0.le
    have h2 : 0 < isoWm γin γout (rW (Muon.emaW β) q) * (1 / (2 * Real.sqrt q)) := by positivity
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hG := zr2_G_T hβ0 hβ1 hγin hγout hrb hq0 hq.2.le
  show |T' q| • isoGb β γin γout (T q ^ 2) = _
  rw [hG, abs_of_nonpos hneg, smul_eq_mul, zr2_rpow_neg_half hq0]
  simp only [T']
  generalize deriv (isoWm γin γout) (rW (Muon.emaW β) q) = A
  generalize d q = D
  generalize isoWm γin γout (rW (Muon.emaW β) q) = Wv
  generalize Lw (Muon.emaW β) q = Lv
  generalize Real.sqrt q = s at *
  subst hs2
  field_simp
  ring

private lemma zr2_r_lt_one {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβ : β = 0) {q : ℝ} (hq : 0 ≤ q) :
    rW (Muon.emaW β) q < 1 :=
  ((lem_app_iso_weights_i hβ0 hβ1).2.2.2 hβ).2.2.mapsTo (Set.mem_Ici.2 hq) |>.2

private lemma zr2_Ilevel_r {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    isoIlevel β (rW (Muon.emaW β) q) =
      Real.sqrt q * Lw (Muon.emaW β) q + (1 / 2) * isoLambda β q := by
  unfold isoIlevel isoLambdaB
  rw [zr2_Qlevel_r hβ0 hβ1 hq, if_neg]
  rintro ⟨hb, h1⟩
  have := zr2_r_lt_one hβ0 hβ1 hb hq
  linarith

private lemma zr2_r_image {β b : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hb : 0 < b) :
    rW (Muon.emaW β) '' Ioo 0 b = Ioo 0 (rW (Muon.emaW β) b) := by
  have hr := zr_isoLink hβ0 hβ1
  ext m
  simp only [Set.mem_image, Set.mem_Ioo]
  constructor
  · rintro ⟨q, ⟨hq0, hqb⟩, rfl⟩
    refine ⟨?_, hr.2.1 (Set.mem_Ici.2 hq0.le) (Set.mem_Ici.2 hb.le) hqb⟩
    have := hr.2.1 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq0.le) hq0
    rwa [hr.2.2] at this
  · rintro ⟨hm0, hmb⟩
    have hc : ContinuousOn (rW (Muon.emaW β)) (Icc 0 b) := hr.1.mono (fun x hx => Set.mem_Ici.2 hx.1)
    obtain ⟨q, hq, hqm⟩ := intermediate_value_Icc hb.le hc ⟨by rw [hr.2.2]; exact hm0.le, hmb.le⟩
    have h0 : q ≠ 0 := by
      rintro rfl
      rw [hr.2.2] at hqm
      linarith
    have h1 : q ≠ b := by
      rintro rfl
      linarith
    exact ⟨q, ⟨lt_of_le_of_ne hq.1 (Ne.symm h0), lt_of_le_of_ne hq.2 h1⟩, hqm⟩

private lemma zr2_cov_m {β γin γout b : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {d : ℝ → ℝ}
    (hd : ∀ q : ℝ, 0 < q → HasDerivAt (rW (Muon.emaW β)) (d q) q ∧ 0 < d q)
    (hb : 0 < b) :
    ∫ m in Ioc 0 (rW (Muon.emaW β) b), (-deriv (isoWm γin γout) m) * isoIlevel β m
      = ∫ q in Ioc 0 b, (-(deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q)) *
          (Real.sqrt q * Lw (Muon.emaW β) q + (1 / 2) * isoLambda β q) := by
  have hr := zr_isoLink hβ0 hβ1
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Ioo 0 b) (f := rW (Muon.emaW β))
    (f' := d) measurableSet_Ioo (fun q hq => (hd q hq.1).1.hasDerivWithinAt)
    (hr.2.1.injOn.mono (fun x hx => Set.mem_Ici.2 hx.1.le))
    (fun m => (-deriv (isoWm γin γout) m) * isoIlevel β m)
  rw [zr2_r_image hβ0 hβ1 hb] at hcov
  rw [integral_Ioc_eq_integral_Ioo, hcov, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo (fun q hq => ?_)
  show |d q| • ((-deriv (isoWm γin γout) (rW (Muon.emaW β) q)) *
    isoIlevel β (rW (Muon.emaW β) q)) = _
  rw [abs_of_pos (hd q hq.1).2, smul_eq_mul, zr2_Ilevel_r hβ0 hβ1 hq.1.le]
  ring

private lemma zr2_LamB_r {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    isoLambdaB β (rW (Muon.emaW β) q) = isoLambda β q := by
  unfold isoLambdaB
  rw [zr2_Qlevel_r hβ0 hβ1 hq, if_neg]
  rintro ⟨hb, h1⟩
  have := zr2_r_lt_one hβ0 hβ1 hb hq
  linarith

/-- The finite-level identity. -/
private lemma zr2_finite {β γin γout b : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout)
    (hb : 0 < b) (hrb : rW (Muon.emaW β) b < min γin γout) :
    ∫ t in Ioi (isoWm γin γout (rW (Muon.emaW β) b) / Real.sqrt b),
        isoGb β γin γout (t ^ 2) = isoIt β γin γout (rW (Muon.emaW β) b) := by
  obtain ⟨d, hd⟩ := zr2_rd hβ0 hβ1
  rw [zr2_cov_t hβ0 hβ1 hγin hγout hd hb hrb, zr2_ibp hβ0 hβ1 hd hb hrb]
  unfold isoIt
  rw [intervalIntegral.integral_of_le (zr2_r_nonneg hβ0 hβ1 hb.le), zr2_cov_m hβ0 hβ1 hd hb,
    zr2_LamB_r hβ0 hβ1 hb.le]
  ring

private lemma zr2_G_anti {β γin γout : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) {s₁ s₂ : ℝ} (h1 : 0 < s₁) (h12 : s₁ ≤ s₂) :
    isoGb β γin γout s₂ ≤ isoGb β γin γout s₁ := by
  have hr := zr_isoLink hβ0 hβ1
  have hanti := (lem_app_iso_comparison_i hr hγin hγout).2.2.2.2.2
  have hq : qIso β γin γout s₂ ≤ qIso β γin γout s₁ :=
    hanti.antitoneOn (Set.mem_Ioi.2 h1) (Set.mem_Ioi.2 (lt_of_lt_of_le h1 h12)) h12
  have hmono := (lem_app_iso_weights_v hβ0 hβ1).2.2
  have h0 : 0 ≤ qIso β γin γout s₂ := (zr_root_bounds hr hγin hγout (lt_of_lt_of_le h1 h12)).1.le
  exact hmono.monotoneOn (Set.mem_Ici.2 h0) (Set.mem_Ici.2 (h0.trans hq)) hq

private lemma zr2_rho {β γin γout ϱ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hϱ : 0 < ϱ) :
    (∫ t in Ioi (Real.sqrt ϱ), isoGb β γin γout (t ^ 2)) ≤
        ∫ u in Ioi (0 : ℝ), isoGb β γin γout (ϱ + u ^ 2) ∧
    (∫ u in Ioi (0 : ℝ), isoGb β γin γout (ϱ + u ^ 2)) ≤
      Real.sqrt ϱ * isoGb β γin γout ϱ + ∫ t in Ioi (Real.sqrt ϱ), isoGb β γin γout (t ^ 2) := by
  set c := Real.sqrt ϱ with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 hϱ
  have hc2 : c ^ 2 = ϱ := Real.sq_sqrt hϱ.le
  have hint0 : IntegrableOn (fun u : ℝ => isoGb β γin γout (u ^ 2)) (Ioi 0) := by
    simpa using zr_integrableOn_shift hβ0 hβ1 hγin hγout (le_refl 0)
  have hintϱ := zr_integrableOn_shift hβ0 hβ1 hγin hγout hϱ.le
  have hcontG := zr_isoGb_contOn hβ0 hβ1 hγin hγout
  have hpos : ∀ u : ℝ, 0 < u → 0 < ϱ + u ^ 2 := fun u hu => by positivity
  constructor
  · -- translation
    have hshift := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0:ℝ))
      (f := fun x : ℝ => x + c) (f' := fun _ => 1) measurableSet_Ioi
      (fun x _ => ((hasDerivAt_id x).add_const c).hasDerivWithinAt)
      (fun x _ y _ h => by simpa using h) (fun t => isoGb β γin γout (t ^ 2))
    rw [Set.image_add_const_Ioi, zero_add] at hshift
    simp only [abs_one, one_smul] at hshift
    rw [hshift]
    have hmono : ∀ u ∈ Ioi (0:ℝ), isoGb β γin γout ((u + c) ^ 2) ≤
        isoGb β γin γout (ϱ + u ^ 2) := by
      intro u hu
      have hu0 : (0:ℝ) < u := hu
      refine zr2_G_anti hβ0 hβ1 hγin hγout (hpos u hu0) ?_
      nlinarith
    have hf : IntegrableOn (fun u : ℝ => isoGb β γin γout ((u + c) ^ 2)) (Ioi 0) := by
      refine Integrable.mono' hintϱ ?_ ?_
      · have : ContinuousOn (fun u : ℝ => isoGb β γin γout ((u + c) ^ 2)) (Ioi 0) := by
          refine (hcontG.comp (f := fun u : ℝ => (u + c) ^ 2) (by fun_prop) ?_)
          intro u hu
          have : (0:ℝ) < u := hu
          exact Set.mem_Ioi.2 (by positivity)
        exact this.aestronglyMeasurable measurableSet_Ioi
      · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => ?_)
        have hu0 : (0:ℝ) < u := hu
        have h1 := (zr_isoGb_bounds hβ0 hβ1 hγin hγout (by positivity : 0 < (u + c) ^ 2)).1
        have := hmono u hu
        rw [Real.norm_eq_abs, abs_of_pos h1]
        exact this
    exact setIntegral_mono_on hf hintϱ measurableSet_Ioi hmono
  · rw [← Set.Ioc_union_Ioi_eq_Ioi hc0.le, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hintϱ.mono_set Set.Ioc_subset_Ioi_self)
      (hintϱ.mono_set (Set.Ioi_subset_Ioi hc0.le))]
    have hA : ∫ u in Ioc 0 c, isoGb β γin γout (ϱ + u ^ 2) ≤ c * isoGb β γin γout ϱ := by
      have h1 : ∫ u in Ioc 0 c, isoGb β γin γout (ϱ + u ^ 2) ≤
          ∫ u in Ioc 0 c, isoGb β γin γout ϱ := by
        refine setIntegral_mono_on (hintϱ.mono_set Set.Ioc_subset_Ioi_self)
          (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc (fun u hu => ?_)
        exact zr2_G_anti hβ0 hβ1 hγin hγout hϱ (by nlinarith [sq_nonneg u])
      refine h1.trans (le_of_eq ?_)
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hc0.le]
      ring
    have hB : ∫ u in Ioi c, isoGb β γin γout (ϱ + u ^ 2) ≤
        ∫ u in Ioi c, isoGb β γin γout (u ^ 2) := by
      refine setIntegral_mono_on (hintϱ.mono_set (Set.Ioi_subset_Ioi hc0.le))
        (hint0.mono_set (Set.Ioi_subset_Ioi hc0.le)) measurableSet_Ioi (fun u hu => ?_)
      have hu0 : (0:ℝ) < u := lt_trans hc0 hu
      exact zr2_G_anti hβ0 hβ1 hγin hγout (by positivity) (by nlinarith)
    linarith

private lemma zr2_int_q {β γin γout b : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {d : ℝ → ℝ}
    (hd : ∀ q : ℝ, 0 < q → HasDerivAt (rW (Muon.emaW β)) (d q) q ∧ 0 < d q)
    (hb : 0 < b) (hrb : rW (Muon.emaW β) b < min γin γout) :
    IntegrableOn (fun q => (-(deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q)) *
      (Real.sqrt q * Lw (Muon.emaW β) q + (1 / 2) * isoLambda β q)) (Ioc 0 b) := by
  have hr := zr_isoLink hβ0 hβ1
  have hL := (Muon.DetEquiv.lem_app_de_scalar_ii (zr_weightSeq hβ0 hβ1)).2.2.2.1
  have hlam := zr2_lam_cont hβ0 hβ1
  have hrq : ∀ q, q ∈ Icc 0 b → rW (Muon.emaW β) q < min γin γout := fun q hq =>
    lt_of_le_of_lt (zr2_r_le hβ0 hβ1 hq.1 hq.2) hrb
  have hwc : ContinuousOn (fun x => isoWm γin γout (rW (Muon.emaW β) x)) (Icc 0 b) :=
    (zr2_W_cont γin γout).comp_continuousOn (hr.1.mono (fun x hx => Set.mem_Ici.2 hx.1))
  have hwd : ∀ q ∈ Ioo 0 b, HasDerivAt (fun x => isoWm γin γout (rW (Muon.emaW β) x))
      (deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q) q := fun q hq =>
    zr2_w_deriv (fun q hq => (hd q hq).1) hq.1 (hrq q ⟨hq.1.le, hq.2.le⟩)
  have hnn : ∀ q ∈ Ioo 0 b, 0 ≤ -(deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q) := by
    intro q hq
    have h1 := zr2_W_deriv_nonpos (hrq q ⟨hq.1.le, hq.2.le⟩)
    have h2 := (hd q hq.1).2
    nlinarith
  have hwdint : IntegrableOn (fun q => -(deriv (isoWm γin γout) (rW (Muon.emaW β) q) * d q))
      (Ioc 0 b) := by
    refine intervalIntegral.integrableOn_deriv_of_nonneg (g := fun x => -isoWm γin γout
      (rW (Muon.emaW β) x)) hwc.neg (fun q hq => (hwd q hq).neg) hnn
  have hLc : ContinuousOn (fun q => Real.sqrt q * Lw (Muon.emaW β) q +
      (1 / 2) * isoLambda β q) (Icc 0 b) :=
    (Real.continuous_sqrt.continuousOn.mul (hL.mono (fun x hx => Set.mem_Ici.2 hx.1))).add
      (continuousOn_const.mul (hlam.mono (fun x hx => Set.mem_Ici.2 hx.1)))
  exact hwdint.mul_continuousOn_of_subset hLc measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self

private lemma zr2_f_nonneg {β γin γout m : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hm : m < min γin γout) :
    0 ≤ (-deriv (isoWm γin γout) m) * isoIlevel β m := by
  have h1 := zr2_W_deriv_nonpos hm
  refine mul_nonneg (by linarith) ?_
  have hQ := zr2_Qlevel_nonneg β m
  have hLam : 0 ≤ isoLambdaB β m := by
    unfold isoLambdaB
    split_ifs with h
    · exact Real.sqrt_nonneg _
    · unfold isoLambda
      refine intervalIntegral.integral_nonneg hQ (fun x hx => ?_)
      exact mul_nonneg (Real.rpow_nonneg hx.1 _) (zr_Lw_pos hβ0 hβ1 hx.1).le
  unfold isoIlevel
  exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (zr_Lw_pos hβ0 hβ1 hQ).le)
    (mul_nonneg (by norm_num) hLam)

private lemma zr2_int_m {β γin γout b : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {d : ℝ → ℝ}
    (hd : ∀ q : ℝ, 0 < q → HasDerivAt (rW (Muon.emaW β)) (d q) q ∧ 0 < d q)
    (hb : 0 < b) (hrb : rW (Muon.emaW β) b < min γin γout) :
    IntegrableOn (fun m => (-deriv (isoWm γin γout) m) * isoIlevel β m)
      (Ioc 0 (rW (Muon.emaW β) b)) := by
  have hr := zr_isoLink hβ0 hβ1
  have hq := zr2_int_q hβ0 hβ1 hd hb hrb
  rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hq ⊢
  have := (integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Ioo 0 b)
    (f := rW (Muon.emaW β)) (f' := d) measurableSet_Ioo
    (fun q hq => (hd q hq.1).1.hasDerivWithinAt)
    (hr.2.1.injOn.mono (fun x hx => Set.mem_Ici.2 hx.1.le))
    (fun m => (-deriv (isoWm γin γout) m) * isoIlevel β m))
  rw [zr2_r_image hβ0 hβ1 hb] at this
  refine this.2 ?_
  refine IntegrableOn.congr_fun hq (fun q hq => ?_) measurableSet_Ioo
  show _ = |d q| • ((-deriv (isoWm γin γout) (rW (Muon.emaW β) q)) *
    isoIlevel β (rW (Muon.emaW β) q))
  rw [abs_of_pos (hd q hq.1).2, smul_eq_mul, zr2_Ilevel_r hβ0 hβ1 hq.1.le]
  ring

private lemma zr2_F_split {β γin γout c : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hc : 0 < c) :
    (∫ t in Ioi (0:ℝ), isoGb β γin γout (t ^ 2)) =
      (∫ t in Ioc 0 c, isoGb β γin γout (t ^ 2)) + ∫ t in Ioi c, isoGb β γin γout (t ^ 2) ∧
    0 ≤ ∫ t in Ioc 0 c, isoGb β γin γout (t ^ 2) ∧
    ∫ t in Ioc 0 c, isoGb β γin γout (t ^ 2) ≤ isoK β (min γin γout) * c := by
  have hint0 : IntegrableOn (fun u : ℝ => isoGb β γin γout (u ^ 2)) (Ioi 0) := by
    simpa using zr_integrableOn_shift hβ0 hβ1 hγin hγout (le_refl 0)
  refine ⟨?_, ?_, ?_⟩
  · rw [← Set.Ioc_union_Ioi_eq_Ioi hc.le, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hint0.mono_set Set.Ioc_subset_Ioi_self)
      (hint0.mono_set (Set.Ioi_subset_Ioi hc.le))]
  · refine setIntegral_nonneg measurableSet_Ioc (fun t ht => ?_)
    exact (zr_isoGb_bounds hβ0 hβ1 hγin hγout (by have := ht.1; positivity)).1.le
  · have h1 : ∫ t in Ioc 0 c, isoGb β γin γout (t ^ 2) ≤
        ∫ t in Ioc 0 c, isoK β (min γin γout) := by
      refine setIntegral_mono_on (hint0.mono_set Set.Ioc_subset_Ioi_self)
        (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc (fun t ht => ?_)
      exact zr_isoGb_le_K hβ0 hβ1 hγin hγout (by have := ht.1; positivity)
    refine h1.trans (le_of_eq ?_)
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hc.le]
    ring

private lemma zr2_lam_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ isoLambda β q := by
  unfold isoLambda
  refine intervalIntegral.integral_nonneg hq (fun x hx => ?_)
  exact mul_nonneg (Real.rpow_nonneg hx.1 _) (zr_Lw_pos hβ0 hβ1 hx.1).le

private lemma zr2_zero {β γin γout m₀ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout)
    (hm0 : 0 < m₀) (hle : m₀ ≤ min γin γout)
    (hrange : ∀ H : ℝ, 0 < H → H < m₀ → ∃ b : ℝ, 0 ≤ b ∧ rW (Muon.emaW β) b = H)
    (hcase : (isoWm γin γout m₀ = 0 ∧ ∃ b : ℝ, 0 ≤ b ∧ rW (Muon.emaW β) b = m₀) ∨
      (β = 0 ∧ m₀ = 1)) :
    isoIt β γin γout m₀ = ∫ u in Ioi (0:ℝ), isoGb β γin γout (0 + u ^ 2) := by
  obtain ⟨d, hd⟩ := zr2_rd hβ0 hβ1
  have hr := zr_isoLink hβ0 hβ1
  simp only [zero_add]
  set I0 := ∫ u in Ioi (0:ℝ), isoGb β γin γout (u ^ 2) with hI0
  set K := isoK β (min γin γout) with hK
  -- the level function
  have hbH : ∀ H : ℝ, 0 < H → H < m₀ →
      0 < isoQlevel β H ∧ rW (Muon.emaW β) (isoQlevel β H) = H := by
    intro H h0 h1
    have hex := hrange H h0 h1
    have hspec : 0 ≤ isoQlevel β H ∧ rW (Muon.emaW β) (isoQlevel β H) = H := by
      unfold isoQlevel
      rw [dif_pos hex]
      exact hex.choose_spec
    refine ⟨lt_of_le_of_ne hspec.1 (fun h => ?_), hspec.2⟩
    rw [← h, hr.2.2] at hspec
    exact absurd hspec.2 h0.ne
  have hbmono : ∀ H₁ H₂ : ℝ, 0 < H₁ → H₁ ≤ H₂ → H₂ < m₀ → isoQlevel β H₁ ≤ isoQlevel β H₂ := by
    intro H₁ H₂ h1 h12 h2
    by_contra hcon
    push_neg at hcon
    have := zr2_r_le hβ0 hβ1 (hbH H₂ (h1.trans_le h12) h2).1.le hcon.le
    rw [(hbH H₂ (h1.trans_le h12) h2).2, (hbH H₁ h1 (h12.trans_lt h2)).2] at this
    have hlt := hr.2.1 (Set.mem_Ici.2 (hbH H₂ (h1.trans_le h12) h2).1.le)
      (Set.mem_Ici.2 (hbH H₁ h1 (h12.trans_lt h2)).1.le) hcon
    rw [(hbH H₂ (h1.trans_le h12) h2).2, (hbH H₁ h1 (h12.trans_lt h2)).2] at hlt
    linarith
  let l : Filter ℝ := nhdsWithin m₀ (Iio m₀)
  have hev : ∀ᶠ H in l, H ∈ Ioo (m₀ / 2) m₀ := Ioo_mem_nhdsLT (by linarith)
  have hev' : ∀ᶠ H in l, 0 < H ∧ H < m₀ := hev.mono (fun H hH => ⟨by linarith [hH.1], hH.2⟩)
  have hWt : Filter.Tendsto (isoWm γin γout) l (𝓝 (isoWm γin γout m₀)) :=
    ((zr2_W_cont γin γout).tendsto m₀).mono_left nhdsWithin_le_nhds
  -- the finite identity
  have hA : ∀ H : ℝ, 0 < H → H < m₀ → (∫ t in Ioi (isoWm γin γout H / Real.sqrt (isoQlevel β H)),
      isoGb β γin γout (t ^ 2)) = isoIt β γin γout H := by
    intro H h0 h1
    have hH : 0 < H ∧ H < m₀ := ⟨h0, h1⟩
    have hb := hbH H hH.1 hH.2
    have := zr2_finite hβ0 hβ1 hγin hγout hb.1 (by rw [hb.2]; exact lt_of_lt_of_le hH.2 hle)
    rw [hb.2] at this
    exact this
  -- Λ_B at the level
  have hLB : ∀ H : ℝ, 0 < H → H < m₀ →
      isoLambdaB β H = isoLambda β (isoQlevel β H) := by
    intro H h0 h1
    have hb := hbH H h0 h1
    have := zr2_LamB_r hβ0 hβ1 hb.1.le
    rwa [hb.2] at this
  -- Step B: T → 0
  have htop' : β = 0 → m₀ = 1 → Filter.Tendsto (fun H => isoQlevel β H) l Filter.atTop := by
    intro hβ hm
    rw [Filter.tendsto_atTop]
    intro B
    have hrB : rW (Muon.emaW β) (max B 0) < m₀ := by
      rw [hm]; exact zr2_r_lt_one hβ0 hβ1 hβ (le_max_right _ _)
    have hmem : Ioo (rW (Muon.emaW β) (max B 0)) m₀ ∈ l := Ioo_mem_nhdsLT hrB
    filter_upwards [hmem, hev'] with H hH hH'
    have hb := hbH H hH'.1 hH'.2
    by_contra hcon
    push_neg at hcon
    have := zr2_r_le hβ0 hβ1 hb.1.le (le_trans hcon.le (le_max_left B 0))
    rw [hb.2] at this
    linarith [hH.1]
  have hB : Filter.Tendsto (fun H => isoWm γin γout H / Real.sqrt (isoQlevel β H)) l (𝓝 0) := by
    rcases hcase with ⟨hW0, -⟩ | ⟨hβ, hm⟩
    · rw [hW0] at hWt
      have hc0 := (hbH (m₀ / 2) (by linarith) (by linarith)).1
      have hg : Filter.Tendsto (fun H => isoWm γin γout H / Real.sqrt (isoQlevel β (m₀ / 2)))
          l (𝓝 0) := by
        simpa using hWt.div_const (Real.sqrt (isoQlevel β (m₀ / 2)))
      refine squeeze_zero' ?_ ?_ hg
      · filter_upwards [hev'] with H hH
        exact div_nonneg (zr2_W_pos (lt_of_lt_of_le hH.2 hle)).le (Real.sqrt_nonneg _)
      · filter_upwards [hev] with H hH
        have hb := hbH H (by linarith [hH.1]) hH.2
        refine div_le_div_of_nonneg_left (zr2_W_pos (lt_of_lt_of_le hH.2 hle)).le
          (Real.sqrt_pos.2 hc0) (Real.sqrt_le_sqrt ?_)
        exact hbmono (m₀ / 2) H (by linarith) hH.1.le hH.2
    · have htop := htop' hβ hm
      exact hWt.div_atTop (Real.tendsto_sqrt_atTop.comp htop)
  -- Step C: L → I0
  have hC : Filter.Tendsto (fun H => ∫ t in Ioi (isoWm γin γout H / Real.sqrt (isoQlevel β H)),
      isoGb β γin γout (t ^ 2)) l (𝓝 I0) := by
    have hpos : ∀ᶠ H in l, 0 < isoWm γin γout H / Real.sqrt (isoQlevel β H) := by
      filter_upwards [hev'] with H hH
      exact div_pos (zr2_W_pos (lt_of_lt_of_le hH.2 hle)) (Real.sqrt_pos.2 (hbH H hH.1 hH.2).1)
    have hK0 : Filter.Tendsto (fun H => K * (isoWm γin γout H / Real.sqrt (isoQlevel β H)))
        l (𝓝 0) := by simpa using hB.const_mul K
    have hKpos : 0 < K := zr_isoK_pos hβ0 hβ1 hγin hγout
    rw [Metric.tendsto_nhds]
    intro ε hε
    have := (Metric.tendsto_nhds.1 hK0 ε hε)
    filter_upwards [this, hpos] with H hH hHp
    obtain ⟨h1, h2, h3⟩ := zr2_F_split hβ0 hβ1 hγin hγout hHp
    rw [Real.dist_eq] at hH ⊢
    rw [h1] at hI0
    have : I0 - ∫ t in Ioi (isoWm γin γout H / Real.sqrt (isoQlevel β H)),
        isoGb β γin γout (t ^ 2) = ∫ t in Ioc 0 (isoWm γin γout H / Real.sqrt (isoQlevel β H)),
        isoGb β γin γout (t ^ 2) := by rw [hI0]; ring
    rw [abs_sub_comm, this, abs_of_nonneg h2]
    have hK' : K * (isoWm γin γout H / Real.sqrt (isoQlevel β H)) < ε := by
      have h := hH
      rw [sub_zero, abs_of_nonneg (mul_nonneg hKpos.le hHp.le)] at h
      exact h
    exact lt_of_le_of_lt h3 hK'
  -- Step D: the boundary term
  have hD : Filter.Tendsto (fun H => (1 / 2) * isoWm γin γout H * isoLambdaB β H) l
      (𝓝 ((1 / 2) * isoWm γin γout m₀ * isoLambdaB β m₀)) := by
    rcases hcase with ⟨hW0, b', hb'0, hb'⟩ | ⟨hβ, hm⟩
    · rw [hW0, mul_zero, zero_mul]
      obtain ⟨C, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn
        ((zr2_lam_cont hβ0 hβ1).mono (fun x hx => Set.mem_Ici.2 hx.1) : ContinuousOn (isoLambda β) (Icc 0 b'))
      have hWt0 := hWt
      rw [hW0] at hWt0
      have ha : Filter.Tendsto (fun H => (1 / 2) * isoWm γin γout H * C) l (𝓝 0) := by
        have h := (hWt0.const_mul (1 / 2)).mul_const C
        rwa [mul_zero, zero_mul] at h
      refine squeeze_zero_norm' ?_ ha
      filter_upwards [hev'] with H hH
      have hb := hbH H hH.1 hH.2
      have hbb : isoQlevel β H ≤ b' := by
        by_contra hcon
        push_neg at hcon
        have := hr.2.1 (Set.mem_Ici.2 hb'0) (Set.mem_Ici.2 hb.1.le) hcon
        rw [hb', hb.2] at this
        linarith [hH.2]
      rw [hLB H hH.1 hH.2]
      have hW := zr2_W_pos (lt_of_lt_of_le hH.2 hle)
      have hlam := zr2_lam_nonneg hβ0 hβ1 hb.1.le
      have hC' := hCb _ ⟨hb.1.le, hbb⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [Real.norm_eq_abs, abs_of_nonneg hlam] at hC'
      exact mul_le_mul_of_nonneg_left hC' (by positivity)
    · have hLm : isoLambdaB β m₀ = Real.sqrt (2 * Real.pi) := by
        unfold isoLambdaB
        rw [if_pos ⟨hβ, hm⟩]
      rw [hLm]
      have hlt : Filter.Tendsto (fun H => isoLambda β (isoQlevel β H)) l
          (𝓝 (Real.sqrt (2 * Real.pi))) := by
        have h2 := (htop' hβ hm)
        subst hβ
        exact (lem_app_iso_weights_iv hβ0 hβ1).2.2.2.2.comp h2
      refine ((hWt.const_mul (1 / 2)).mul hlt).congr' ?_
      filter_upwards [hev'] with H hH
      rw [hLB H hH.1 hH.2]
  have hBnn : ∀ H : ℝ, 0 < H → H < m₀ → 0 ≤ (1 / 2) * isoWm γin γout H * isoLambdaB β H := by
    intro H h0 h1
    rw [hLB H h0 h1]
    have hW := zr2_W_pos (lt_of_lt_of_le h1 hle)
    have hlam := zr2_lam_nonneg hβ0 hβ1 (hbH H h0 h1).1.le
    positivity
  -- Step E
  set f : ℝ → ℝ := fun m => (-deriv (isoWm γin γout) m) * isoIlevel β m with hf
  set g : ℝ → ℝ := fun H => ∫ m in (0:ℝ)..H, f m with hg
  have hgdef : ∀ H : ℝ, 0 < H → H < m₀ → g H = (∫ t in Ioi (isoWm γin γout H /
      Real.sqrt (isoQlevel β H)), isoGb β γin γout (t ^ 2)) -
      (1 / 2) * isoWm γin γout H * isoLambdaB β H := by
    intro H h0 h1
    rw [hA H h0 h1]
    unfold isoIt
    simp only [hg, hf]
    ring
  have hLle : ∀ H : ℝ, 0 < H → H < m₀ → (∫ t in Ioi (isoWm γin γout H /
      Real.sqrt (isoQlevel β H)), isoGb β γin γout (t ^ 2)) ≤ I0 := by
    intro H h0 h1
    have hpos : 0 < isoWm γin γout H / Real.sqrt (isoQlevel β H) :=
      div_pos (zr2_W_pos (lt_of_lt_of_le h1 hle)) (Real.sqrt_pos.2 (hbH H h0 h1).1)
    obtain ⟨e1, e2, -⟩ := zr2_F_split hβ0 hβ1 hγin hγout hpos
    rw [hI0, e1]
    linarith
  have hgle : ∀ H : ℝ, 0 < H → H < m₀ → g H ≤ I0 := by
    intro H h0 h1
    rw [hgdef H h0 h1]
    linarith [hLle H h0 h1, hBnn H h0 h1]
  have hgt : Filter.Tendsto g l (𝓝 (I0 - (1 / 2) * isoWm γin γout m₀ * isoLambdaB β m₀)) := by
    refine (hC.sub hD).congr' ?_
    filter_upwards [hev'] with H hH
    exact (hgdef H hH.1 hH.2).symm
  -- Step F: integrability and continuity of the primitive
  have hsq : ∀ n : ℕ, 0 < m₀ - m₀ / ((n : ℝ) + 2) ∧ m₀ - m₀ / ((n : ℝ) + 2) < m₀ := by
    intro n
    have h2 : (2:ℝ) ≤ (n : ℝ) + 2 := by have := n.cast_nonneg (α := ℝ); linarith
    constructor
    · have : m₀ / ((n : ℝ) + 2) ≤ m₀ / 2 := div_le_div_of_nonneg_left hm0.le (by norm_num) h2
      linarith
    · have : 0 < m₀ / ((n : ℝ) + 2) := by positivity
      linarith
  have hbt : Filter.Tendsto (fun n : ℕ => m₀ - m₀ / ((n : ℝ) + 2)) Filter.atTop (𝓝 m₀) := by
    have : Filter.Tendsto (fun n : ℕ => m₀ / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    simpa using (tendsto_const_nhds (x := m₀)).sub this
  have hfint : IntegrableOn f (Ioc 0 m₀) := by
    refine integrableOn_Ioc_of_intervalIntegral_norm_bounded_right (I := I0) (l := Filter.atTop)
      (b := fun n : ℕ => m₀ - m₀ / ((n : ℝ) + 2)) (fun n => ?_) hbt
      (Filter.Eventually.of_forall (fun n => ?_))
    · obtain ⟨h0, h1⟩ := hsq n
      have hb := hbH _ h0 h1
      have := zr2_int_m hβ0 hβ1 hd hb.1 (by rw [hb.2]; exact lt_of_lt_of_le h1 hle)
      rwa [hb.2] at this
    · obtain ⟨h0, h1⟩ := hsq n
      have : ∫ x in Ioc 0 (m₀ - m₀ / ((n : ℝ) + 2)), ‖f x‖ = g (m₀ - m₀ / ((n : ℝ) + 2)) := by
        simp only [hg]
        rw [intervalIntegral.integral_of_le h0.le]
        refine setIntegral_congr_fun measurableSet_Ioc (fun m hm => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (zr2_f_nonneg hβ0 hβ1
          (lt_of_le_of_lt hm.2 (lt_of_lt_of_le h1 hle)))]
      rw [this]
      exact hgle _ h0 h1
  have hfi : IntervalIntegrable f volume 0 m₀ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hm0.le).2 hfint
  have hm0mem : m₀ ∈ Set.uIcc 0 m₀ := by rw [Set.uIcc_of_le hm0.le]; exact ⟨hm0.le, le_rfl⟩
  have hcont := intervalIntegral.continuousOn_primitive_interval' hfi
    (by rw [Set.uIcc_of_le hm0.le]; exact ⟨le_rfl, hm0.le⟩ : (0:ℝ) ∈ Set.uIcc 0 m₀)
  have hcw : ContinuousWithinAt g (Iio m₀) m₀ :=
    (hcont m₀ hm0mem).mono_of_mem_nhdsWithin
      (by rw [Set.uIcc_of_le hm0.le]; exact Icc_mem_nhdsLT hm0)
  have heq := tendsto_nhds_unique hgt hcw.tendsto
  have hfin : isoIt β γin γout m₀ = g m₀ + (1 / 2) * isoWm γin γout m₀ * isoLambdaB β m₀ := rfl
  rw [hfin, ← heq]
  ring

private lemma zr2_surj {β H : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hH : 0 ≤ H)
    (hc : 0 < β ∨ (β = 0 ∧ H < 1)) : ∃ b : ℝ, 0 ≤ b ∧ rW (Muon.emaW β) b = H := by
  have h := lem_app_iso_weights_i hβ0 hβ1
  rcases hc with hpos | ⟨hz, h1⟩
  · obtain ⟨q, hq, e⟩ := (h.2.2.1 hpos).2.2.2 (Set.mem_Ici.2 hH)
    exact ⟨q, Set.mem_Ici.1 hq, e⟩
  · obtain ⟨q, hq, e⟩ := ((h.2.2.2 hz).2.2).2.2 (show H ∈ Ico (0:ℝ) 1 from ⟨hH, h1⟩)
    exact ⟨q, Set.mem_Ici.1 hq, e⟩

private lemma zr2_main {β γin γout ϱ : ℝ}
    (hreg : (0 < β ∧ β < 1) ∨ (β = 0 ∧ min γin γout < 1) ∨ (β = 0 ∧ 1 ≤ min γin γout))
    (hγin : 0 < γin) (hγout : 0 < γout) (hϱ : 0 ≤ ϱ) :
    isoIt β γin γout (isoMLevel β γin γout ϱ) ≤ ∫ u in Ioi (0 : ℝ), isoGb β γin γout (ϱ + u ^ 2) ∧
    (∫ u in Ioi (0 : ℝ), isoGb β γin γout (ϱ + u ^ 2)) ≤
      isoIt β γin γout (isoMLevel β γin γout ϱ)
        + isoWm γin γout (isoMLevel β γin γout ϱ)
          * (Real.sqrt (isoQlevel β (isoMLevel β γin γout ϱ))
            * Lw (Muon.emaW β) (isoQlevel β (isoMLevel β γin γout ϱ))) ∧
    (ϱ = 0 → isoIt β γin γout (isoMLevel β γin γout ϱ)
      = ∫ u in Ioi (0 : ℝ), isoGb β γin γout (0 + u ^ 2)) := by
  have hβ01 : 0 ≤ β ∧ β < 1 := by
    rcases hreg with ⟨h1, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨h1.le, h2⟩
    · exact ⟨h1.ge, by rw [h1]; norm_num⟩
    · exact ⟨h1.ge, by rw [h1]; norm_num⟩
  obtain ⟨hβ0, hβ1⟩ := hβ01
  have hr := zr_isoLink hβ0 hβ1
  rcases hϱ.eq_or_lt with h0 | hpos
  · -- ϱ = 0
    subst h0
    have hminpos : 0 < min γin γout := lt_min hγin hγout
    have hmL : isoMLevel β γin γout 0 =
        (if β = 0 ∧ 1 ≤ min γin γout then 1 else min γin γout) := by
      unfold isoMLevel; rw [if_pos rfl]
    have hzero : isoIt β γin γout (isoMLevel β γin γout 0)
        = ∫ u in Ioi (0:ℝ), isoGb β γin γout (0 + u ^ 2) := by
      rw [hmL]
      by_cases hc : β = 0 ∧ 1 ≤ min γin γout
      · rw [if_pos hc]
        refine zr2_zero hβ0 hβ1 hγin hγout one_pos hc.2 (fun H h0 h1 => ?_) (Or.inr ⟨hc.1, rfl⟩)
        exact zr2_surj hβ0 hβ1 h0.le (Or.inr ⟨hc.1, h1⟩)
      · rw [if_neg hc]
        have hcase : 0 < β ∨ (β = 0 ∧ min γin γout < 1) := by
          rcases hreg with ⟨h1, -⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl h1
          · exact Or.inr ⟨h1, h2⟩
          · exact absurd ⟨h1, h2⟩ hc
        refine zr2_zero hβ0 hβ1 hγin hγout hminpos le_rfl (fun H h0 h1 => ?_) (Or.inl ⟨?_, ?_⟩)
        · refine zr2_surj hβ0 hβ1 h0.le ?_
          rcases hcase with h | ⟨h, h'⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, lt_trans h1 h'⟩
        · unfold isoWm
          rcases min_choice γin γout with h | h
          · rw [h]; simp
          · rw [h]; simp
        · exact zr2_surj hβ0 hβ1 hminpos.le hcase
    rw [hzero]
    refine ⟨le_rfl, ?_, fun _ => rfl⟩
    have hQ := zr2_Qlevel_nonneg β (isoMLevel β γin γout 0)
    have : 0 ≤ isoWm γin γout (isoMLevel β γin γout 0) *
        (Real.sqrt (isoQlevel β (isoMLevel β γin γout 0)) *
          Lw (Muon.emaW β) (isoQlevel β (isoMLevel β γin γout 0))) :=
      mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
        (zr_Lw_pos hβ0 hβ1 hQ).le)
    simp only [zero_add] at *
    linarith
  · -- ϱ > 0
    obtain ⟨hq0, hqlt, hqeq⟩ := zr_root_mem hr hγin hγout hpos
    have hbpos := (zr_root_bounds hr hγin hγout hpos).1
    set b := isoRoot (rW (Muon.emaW β)) γin γout ϱ with hbdef
    have hqb : qIso β γin γout ϱ = b := rfl
    have hmL : isoMLevel β γin γout ϱ = rW (Muon.emaW β) b := by
      unfold isoMLevel psiIso
      rw [if_neg hpos.ne']
      rfl
    have hQ : isoQlevel β (isoMLevel β γin γout ϱ) = b := by
      rw [hmL]; exact zr2_Qlevel_r hβ0 hβ1 hq0
    have hWb := zr2_W_pos hqlt
    have hWsq := zr2_W_sq hqlt
    have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hbpos
    have hT2 : (isoWm γin γout (rW (Muon.emaW β) b) / Real.sqrt b) ^ 2 = ϱ := by
      rw [div_pow, Real.sq_sqrt hbpos.le, hWsq]
      field_simp
      linarith
    have hsq : Real.sqrt ϱ = isoWm γin γout (rW (Muon.emaW β) b) / Real.sqrt b := by
      rw [← hT2, Real.sqrt_sq (div_pos hWb hsb).le]
    have hfin := zr2_finite hβ0 hβ1 hγin hγout hbpos hqlt
    obtain ⟨hA, hB⟩ := zr2_rho (γin := γin) (γout := γout) hβ0 hβ1 hγin hγout hpos
    rw [hsq, hfin] at hA hB
    rw [hQ, hmL]
    have hG : Real.sqrt ϱ * isoGb β γin γout ϱ =
        isoWm γin γout (rW (Muon.emaW β) b) * (Real.sqrt b * Lw (Muon.emaW β) b) := by
      unfold isoGb
      rw [hqb, hsq]
      have : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hbpos.le
      field_simp
      rw [Real.sq_sqrt hbpos.le]
    refine ⟨hA, ?_, fun h => absurd h hpos.ne'⟩
    rw [hsq] at hG
    linarith

/-! ## The participation identity and the master estimate -/

/-- `lem:app-iso-participation`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1296–1314):
```latex
\begin{lemma}[Participation identity]\label{lem:app-iso-participation}
Let $\gin,\gout>0$, and assume either $\bmom\in(0,1)$, or $\bmom=0$ and
$\gamma_\wedge<1$. For $0\le m\le\gamma_\wedge$ put $Q_m\defeq r_\bmom^{-1}(m)$,
\[
\mathsf i_\bmom(m)\defeq\sqrt{Q_m}\,\Lw(Q_m)+\tfrac12\Lambda_\bmom(Q_m),
\]
\[
\widetilde{\mathcal I}(H)\defeq\int_0^H\big(-\mathsf W'(m)\big)\,\mathsf i_\bmom(m)\,\dif m+\tfrac12\mathsf W(H)\,\Lambda_\bmom(Q_H),
\]
and put $m_\ridge\defeq\psi(\ridge)$ for $\ridge>0$ and $m_0\defeq\gamma_\wedge$. Then for every $\ridge\ge0$,
\begin{equation}\label{eqn:app-iso-participation}
\widetilde{\mathcal I}(m_\ridge)\le\int_0^\infty\mathsf G_\bmom(\ridge+u^2)\,\dif u\le
\widetilde{\mathcal I}(m_\ridge)+\mathsf W(m_\ridge)\sqrt{Q_{m_\ridge}}\,\Lw(Q_{m_\ridge}),
\end{equation}
and the last term vanishes at $\ridge=0$, so that equality holds there. If
$\bmom=0$ and $\gamma_\wedge\ge1$, the same holds with $0\le m<1$,
$Q_m=\Phi^{-1}(m)$, $m_0\defeq1$ and $\Lambda_0(Q_1)\defeq\sqrt{2\pi}$; the
boundary term of $\widetilde{\mathcal I}(1)$ is then $\frac12\mathsf W(1)\sqrt{2\pi}$.
\end{lemma}
```

Part (i): the regime `β ∈ (0,1)`, or `β = 0` and `γ∧ < 1` (the first two cases of the source).
The upper bound's last term is written out as `𝖶(m_ϱ) √(Q_{m_ϱ}) L_β(Q_{m_ϱ})`. The equality at
`ϱ = 0` is the source's "equality holds there". -/
theorem lem_app_iso_participation_i {β γin γout ϱ : ℝ}
    (hβ : (0 < β ∧ β < 1) ∨ (β = 0 ∧ min γin γout < 1))
    (hγin : 0 < γin) (hγout : 0 < γout) (hϱ : 0 ≤ ϱ) :
    isoIt β γin γout (isoMLevel β γin γout ϱ) ≤ ∫ u in Ioi (0 : ℝ), isoGb β γin γout (ϱ + u ^ 2) ∧
    (∫ u in Ioi (0 : ℝ), isoGb β γin γout (ϱ + u ^ 2)) ≤
      isoIt β γin γout (isoMLevel β γin γout ϱ)
        + isoWm γin γout (isoMLevel β γin γout ϱ)
          * (Real.sqrt (isoQlevel β (isoMLevel β γin γout ϱ))
            * Lw (Muon.emaW β) (isoQlevel β (isoMLevel β γin γout ϱ))) ∧
    (ϱ = 0 → isoIt β γin γout (isoMLevel β γin γout ϱ)
      = ∫ u in Ioi (0 : ℝ), isoGb β γin γout (0 + u ^ 2)) := by
  refine zr2_main ?_ hγin hγout hϱ
  rcases hβ with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h1, h2⟩)

/-- `lem:app-iso-participation`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1296–1314):
```latex
\begin{lemma}[Participation identity]\label{lem:app-iso-participation}
Let $\gin,\gout>0$, and assume either $\bmom\in(0,1)$, or $\bmom=0$ and
$\gamma_\wedge<1$. For $0\le m\le\gamma_\wedge$ put $Q_m\defeq r_\bmom^{-1}(m)$,
\[
\mathsf i_\bmom(m)\defeq\sqrt{Q_m}\,\Lw(Q_m)+\tfrac12\Lambda_\bmom(Q_m),
\]
\[
\widetilde{\mathcal I}(H)\defeq\int_0^H\big(-\mathsf W'(m)\big)\,\mathsf i_\bmom(m)\,\dif m+\tfrac12\mathsf W(H)\,\Lambda_\bmom(Q_H),
\]
and put $m_\ridge\defeq\psi(\ridge)$ for $\ridge>0$ and $m_0\defeq\gamma_\wedge$. Then for every $\ridge\ge0$,
\begin{equation}\label{eqn:app-iso-participation}
\widetilde{\mathcal I}(m_\ridge)\le\int_0^\infty\mathsf G_\bmom(\ridge+u^2)\,\dif u\le
\widetilde{\mathcal I}(m_\ridge)+\mathsf W(m_\ridge)\sqrt{Q_{m_\ridge}}\,\Lw(Q_{m_\ridge}),
\end{equation}
and the last term vanishes at $\ridge=0$, so that equality holds there. If
$\bmom=0$ and $\gamma_\wedge\ge1$, the same holds with $0\le m<1$,
$Q_m=\Phi^{-1}(m)$, $m_0\defeq1$ and $\Lambda_0(Q_1)\defeq\sqrt{2\pi}$; the
boundary term of $\widetilde{\mathcal I}(1)$ is then $\frac12\mathsf W(1)\sqrt{2\pi}$.
\end{lemma}
```

Part (ii): the regime `β = 0` and `γ∧ ≥ 1`. The same statement as part (i), with `0 ≤ m < 1`,
`Q_m = Φ^{-1}(m)`, `m_0 = 1` and `Λ_0(Q_1) := √(2π)` (the `isoLambdaB` convention). -/
theorem lem_app_iso_participation_ii {β γin γout ϱ : ℝ}
    (hβ : β = 0) (hγ : 1 ≤ min γin γout)
    (hγin : 0 < γin) (hγout : 0 < γout) (hϱ : 0 ≤ ϱ) :
    isoIt β γin γout (isoMLevel β γin γout ϱ) ≤ ∫ u in Ioi (0 : ℝ), isoGb β γin γout (ϱ + u ^ 2) ∧
    (∫ u in Ioi (0 : ℝ), isoGb β γin γout (ϱ + u ^ 2)) ≤
      isoIt β γin γout (isoMLevel β γin γout ϱ)
        + isoWm γin γout (isoMLevel β γin γout ϱ)
          * (Real.sqrt (isoQlevel β (isoMLevel β γin γout ϱ))
            * Lw (Muon.emaW β) (isoQlevel β (isoMLevel β γin γout ϱ))) ∧
    (ϱ = 0 → isoIt β γin γout (isoMLevel β γin γout ϱ)
      = ∫ u in Ioi (0 : ℝ), isoGb β γin γout (0 + u ^ 2)) := by
  exact zr2_main (Or.inr (Or.inr ⟨hβ, hγ⟩)) hγin hγout hϱ

/-! Private helpers for `thm_app_iso_master` (task P-F.3.P3). -/

private lemma zr3_pt {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ Real.sqrt q * Lw (Muon.emaW β) q ∧ Real.sqrt q * Lw (Muon.emaW β) q ≤ isoGSup β ∧
    |isoLambda β q - Real.sqrt (2 * Real.pi) * rW (Muon.emaW β) q| ≤ isoGPrimeSup β ∧
    0 ≤ isoGSup β ∧ 0 ≤ isoGPrimeSup β := by
  have hb2 := (lem_app_iso_constants_ii hβ0 hβ1).1
  have hb3 := (lem_app_iso_constants_iii hβ0 hβ1).1
  have hg : ∀ q : ℝ, 0 < q → Real.sqrt q * Lw (Muon.emaW β) q ≤ isoGSup β := fun q hq =>
    le_csSup hb2 ⟨q, hq, rfl⟩
  have hg' : ∀ q : ℝ, 0 < q →
      |isoLambda β q - Real.sqrt (2 * Real.pi) * rW (Muon.emaW β) q| ≤ isoGPrimeSup β :=
    fun q hq => le_csSup hb3 ⟨q, hq, rfl⟩
  have hg0 : 0 ≤ isoGSup β :=
    (mul_nonneg (Real.sqrt_nonneg _) (zr_Lw_pos hβ0.le hβ1 zero_le_one).le).trans (hg 1 one_pos)
  have hg0' : 0 ≤ isoGPrimeSup β := (abs_nonneg _).trans (hg' 1 one_pos)
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (zr_Lw_pos hβ0.le hβ1 hq).le, ?_, ?_, hg0, hg0'⟩
  · rcases hq.eq_or_lt with h | h
    · rw [← h]; simpa using hg0
    · exact hg q h
  · rcases hq.eq_or_lt with h | h
    · rw [← h, zr2_lam_zero]
      have : rW (Muon.emaW β) 0 = 0 := (zr_isoLink hβ0.le hβ1).2.2
      rw [this]; simpa using hg0'
    · exact hg' q h

private lemma zr3_hd {γin γout m : ℝ} (hm : m < min γin γout) :
    HasDerivAt (fun x => -isoWm γin γout x) (-deriv (isoWm γin γout) m) m :=
  (zr2_W_deriv hm).differentiableAt.hasDerivAt.neg

private lemma zr3_h_int {γin γout H : ℝ} (hH0 : 0 < H) (hHm : H ≤ min γin γout) :
    IntegrableOn (fun m => -deriv (isoWm γin γout) m) (Ioc 0 H) := by
  have hwc : ContinuousOn (fun x => -isoWm γin γout x) (Icc 0 H) :=
    (zr2_W_cont γin γout).neg.continuousOn
  refine intervalIntegral.integrableOn_deriv_of_nonneg (g := fun x => -isoWm γin γout x) hwc
    (fun q hq => ?_) (fun q hq => ?_)
  · exact zr3_hd (lt_of_lt_of_le hq.2 hHm)
  · have := zr2_W_deriv_nonpos (lt_of_lt_of_le hq.2 hHm)
    show 0 ≤ -deriv (isoWm γin γout) q
    linarith

private lemma zr3_h_int_val {γin γout H : ℝ} (hH0 : 0 < H) (hHm : H ≤ min γin γout) :
    ∫ m in Ioc 0 H, -deriv (isoWm γin γout) m = isoWm γin γout 0 - isoWm γin γout H := by
  rw [← intervalIntegral.integral_of_le hH0.le]
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun x => -isoWm γin γout x)
    (f' := fun m => -deriv (isoWm γin γout) m) hH0.le (zr2_W_cont γin γout).neg.continuousOn
    (fun q hq => zr3_hd (lt_of_lt_of_le hq.2 hHm))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hH0.le).2 (zr3_h_int hH0 hHm))
  rw [this]; ring

/-- integration by parts for `W`. -/
private lemma zr3_ibp {γin γout H : ℝ} (hH0 : 0 < H) (hHm : H ≤ min γin γout) :
    (∫ m in Ioc 0 H, m * (-deriv (isoWm γin γout) m)) + H * isoWm γin γout H
      = ∫ m in Ioc 0 H, isoWm γin γout m := by
  have hhi := zr3_h_int hH0 hHm
  have hmh : IntegrableOn (fun m => m * (-deriv (isoWm γin γout) m)) (Ioc 0 H) := by
    have := hhi.mul_continuousOn_of_subset (continuousOn_id (s := Icc (0:ℝ) H))
      measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
    refine this.congr_fun (fun m _ => ?_) measurableSet_Ioc
    simp only [id]; ring
  have hWi : IntegrableOn (isoWm γin γout) (Ioc 0 H) :=
    (zr2_W_cont γin γout).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hint : IntervalIntegrable (fun m => isoWm γin γout m - m * (-deriv (isoWm γin γout) m))
      volume 0 H :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hH0.le).2 (hWi.sub hmh)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun x => x * isoWm γin γout x)
    (f' := fun m => isoWm γin γout m - m * (-deriv (isoWm γin γout) m)) hH0.le
    (continuous_id.mul (zr2_W_cont γin γout)).continuousOn
    (fun q hq => by
      have h1 := (hasDerivAt_id q).mul (zr2_W_deriv (lt_of_lt_of_le hq.2 hHm))
      refine h1.congr_deriv ?_
      simp only [id, one_mul]
      rw [(zr2_W_deriv (lt_of_lt_of_le hq.2 hHm)).deriv]; ring) hint
  rw [intervalIntegral.integral_sub ((intervalIntegrable_iff_integrableOn_Ioc_of_le hH0.le).2 hWi)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hH0.le).2 hmh)] at this
  rw [intervalIntegral.integral_of_le hH0.le, intervalIntegral.integral_of_le hH0.le] at this
  simp only [zero_mul, sub_zero] at this
  linarith

/-- Pointwise description of `𝗂_β` at an interior level. -/
private lemma zr3_i_pt {β γin γout m : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hm0 : 0 < m) :
    0 ≤ Real.sqrt (isoQlevel β m) * Lw (Muon.emaW β) (isoQlevel β m) ∧
    Real.sqrt (isoQlevel β m) * Lw (Muon.emaW β) (isoQlevel β m) ≤ isoGSup β ∧
    |isoLambdaB β m - Real.sqrt (2 * Real.pi) * m| ≤ isoGPrimeSup β ∧
    isoIlevel β m = Real.sqrt (isoQlevel β m) * Lw (Muon.emaW β) (isoQlevel β m)
      + (1 / 2) * isoLambdaB β m := by
  have hex := zr2_surj (H := m) hβ0.le hβ1 hm0.le (Or.inl hβ0)
  have hspec : 0 ≤ isoQlevel β m ∧ rW (Muon.emaW β) (isoQlevel β m) = m := by
    unfold isoQlevel
    rw [dif_pos hex]
    exact hex.choose_spec
  have hpt := zr3_pt hβ0 hβ1 hspec.1
  have hL : isoLambdaB β m = isoLambda β (isoQlevel β m) := by
    unfold isoLambdaB
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hβ0.ne' h
  refine ⟨hpt.1, hpt.2.1, ?_, rfl⟩
  rw [hL]
  have := hpt.2.2.1
  rwa [hspec.2] at this

private lemma zr3_intf {β γin γout H : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hH0 : 0 < H) (hHm : H ≤ min γin γout) :
    IntegrableOn (fun m => (-deriv (isoWm γin γout) m) * isoIlevel β m) (Ioc 0 H) := by
  obtain ⟨d, hd⟩ := zr2_rd hβ0.le hβ1
  set f : ℝ → ℝ := fun m => (-deriv (isoWm γin γout) m) * isoIlevel β m with hf
  have hhi := zr3_h_int hH0 hHm
  rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hhi ⊢
  -- measurability
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioo 0 H)) := by
    have hU : Ioo 0 H = ⋃ n : ℕ, Ioc 0 (H * (1 - 1 / ((n : ℝ) + 2))) := by
      ext x
      simp only [mem_Ioo, mem_iUnion, mem_Ioc]
      constructor
      · rintro ⟨h0, h1⟩
        obtain ⟨n, hn⟩ := exists_nat_gt (H / (H - x))
        refine ⟨n, h0, ?_⟩
        have hHx : 0 < H - x := by linarith
        have h2 : H / (H - x) < (n : ℝ) + 2 := by linarith
        rw [div_lt_iff₀ hHx] at h2
        have h3 : 0 < (n : ℝ) + 2 := by positivity
        have : H * (1 - 1 / ((n : ℝ) + 2)) = H - H / ((n : ℝ) + 2) := by ring
        rw [this]
        have : H / ((n : ℝ) + 2) < H - x := by
          rw [div_lt_iff₀ h3]; nlinarith
        linarith
      · rintro ⟨n, h0, h1⟩
        refine ⟨h0, lt_of_le_of_lt h1 ?_⟩
        have h3 : 0 < (n : ℝ) + 2 := by positivity
        have : 0 < H * (1 / ((n : ℝ) + 2)) := by positivity
        nlinarith
    rw [hU, aestronglyMeasurable_iUnion_iff]
    intro n
    have h3 : 0 < (n : ℝ) + 2 := by positivity
    have hlt1 : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one h3]; linarith
    have hHn0 : 0 < H * (1 - 1 / ((n : ℝ) + 2)) := mul_pos hH0 (by linarith)
    have hHnlt : H * (1 - 1 / ((n : ℝ) + 2)) < min γin γout := by
      have : 0 < H * (1 / ((n : ℝ) + 2)) := by positivity
      nlinarith
    obtain ⟨b, hb0, hbr⟩ := zr2_surj (H := H * (1 - 1 / ((n : ℝ) + 2))) hβ0.le hβ1 hHn0.le
      (Or.inl hβ0)
    have hbpos : 0 < b := by
      rcases hb0.eq_or_lt with h | h
      · exfalso; rw [← h, (zr_isoLink hβ0.le hβ1).2.2] at hbr; linarith
      · exact h
    have := zr2_int_m (γin := γin) (γout := γout) hβ0.le hβ1 hd hbpos (by rw [hbr]; exact hHnlt)
    rw [hbr] at this
    exact this.aestronglyMeasurable
  -- the bound
  set K := isoGSup β + Real.sqrt (2 * Real.pi) / 2 * H + isoGPrimeSup β / 2 with hK
  refine Integrable.mono' (hhi.const_mul K) hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Filter.Eventually.of_forall (fun m hm => ?_)
  have hmm : m < min γin γout := lt_of_lt_of_le hm.2 hHm
  have hh0 := zr2_W_deriv_nonpos hmm
  obtain ⟨p1, p2, p3, p4⟩ := zr3_i_pt (γin := γin) (γout := γout) hβ0 hβ1 hm.1
  have hg0 := (zr3_pt hβ0 hβ1 (le_refl (0:ℝ))).2.2.2
  have hi : 0 ≤ isoIlevel β m := by
    rw [p4]
    have hLam : 0 ≤ isoLambdaB β m := by
      unfold isoLambdaB
      split_ifs
      · exact Real.sqrt_nonneg _
      · exact zr2_lam_nonneg hβ0.le hβ1 (zr2_Qlevel_nonneg β m)
    linarith
  have hi2 : isoIlevel β m ≤ K := by
    rw [p4]
    have := (abs_le.1 p3).2
    have hm2 : m ≤ H := hm.2.le
    have hs : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    nlinarith
  show ‖(-deriv (isoWm γin γout) m) * isoIlevel β m‖ ≤ K * -deriv (isoWm γin γout) m
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) hi)]
  nlinarith

private lemma zr3_it {β γin γout H : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hH0 : 0 < H) (hHm : H ≤ min γin γout) :
    -(isoGPrimeSup β / 2) * isoWm γin γout 0 ≤
      isoIt β γin γout H - Real.sqrt (2 * Real.pi) / 2 * ∫ m in (0 : ℝ)..H, isoWm γin γout m ∧
    isoIt β γin γout H - Real.sqrt (2 * Real.pi) / 2 * ∫ m in (0 : ℝ)..H, isoWm γin γout m ≤
      (isoGSup β + isoGPrimeSup β / 2) * (isoWm γin γout 0 - isoWm γin γout H)
        + isoGPrimeSup β / 2 * isoWm γin γout H := by
  set c := Real.sqrt (2 * Real.pi) / 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hfi := zr3_intf (γin := γin) (γout := γout) hβ0 hβ1 hH0 hHm
  have hhi := zr3_h_int hH0 hHm
  have hhv := zr3_h_int_val hH0 hHm
  have hibp := zr3_ibp hH0 hHm
  have hmh : IntegrableOn (fun m => m * (-deriv (isoWm γin γout) m)) (Ioc 0 H) := by
    have := hhi.mul_continuousOn_of_subset (continuousOn_id (s := Icc (0:ℝ) H))
      measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
    refine this.congr_fun (fun m _ => ?_) measurableSet_Ioc
    simp only [id]; ring
  have hg0 := (zr3_pt hβ0 hβ1 (le_refl (0:ℝ))).2.2.2.1
  have hg0' := (zr3_pt hβ0 hβ1 (le_refl (0:ℝ))).2.2.2.2
  set g := isoGSup β
  set g' := isoGPrimeSup β
  -- pointwise bounds
  have hpw : ∀ m ∈ Ioo 0 H,
      -(g' / 2) * (-deriv (isoWm γin γout) m) ≤
        (-deriv (isoWm γin γout) m) * isoIlevel β m - c * (m * (-deriv (isoWm γin γout) m)) ∧
      (-deriv (isoWm γin γout) m) * isoIlevel β m - c * (m * (-deriv (isoWm γin γout) m)) ≤
        (g + g' / 2) * (-deriv (isoWm γin γout) m) := by
    intro m hm
    have hmm : m < min γin γout := lt_of_lt_of_le hm.2 hHm
    have hh0 := zr2_W_deriv_nonpos hmm
    obtain ⟨p1, p2, p3, p4⟩ := zr3_i_pt (γin := γin) (γout := γout) hβ0 hβ1 hm.1
    have hab := abs_le.1 p3
    have key : isoIlevel β m - c * m = Real.sqrt (isoQlevel β m) * Lw (Muon.emaW β) (isoQlevel β m)
        + (1 / 2) * (isoLambdaB β m - Real.sqrt (2 * Real.pi) * m) := by
      rw [p4, hc]; ring
    have e : (-deriv (isoWm γin γout) m) * isoIlevel β m - c * (m * (-deriv (isoWm γin γout) m))
        = (-deriv (isoWm γin γout) m) * (isoIlevel β m - c * m) := by ring
    rw [e, key]
    constructor <;> nlinarith
  have hlo : ∫ m in Ioc 0 H, -(g' / 2) * (-deriv (isoWm γin γout) m) ≤
      ∫ m in Ioc 0 H, ((-deriv (isoWm γin γout) m) * isoIlevel β m
        - c * (m * (-deriv (isoWm γin γout) m))) := by
    rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioo (fun m hm => (hpw m hm).1)
    · exact IntegrableOn.mono_set (Integrable.const_mul hhi _) Ioo_subset_Ioc_self
    · exact (hfi.sub (hmh.const_mul c)).mono_set Ioo_subset_Ioc_self
  have hhi' : ∫ m in Ioc 0 H, ((-deriv (isoWm γin γout) m) * isoIlevel β m
        - c * (m * (-deriv (isoWm γin γout) m))) ≤
      ∫ m in Ioc 0 H, (g + g' / 2) * (-deriv (isoWm γin γout) m) := by
    rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioo (fun m hm => (hpw m hm).2)
    · exact (hfi.sub (hmh.const_mul c)).mono_set Ioo_subset_Ioc_self
    · exact IntegrableOn.mono_set (Integrable.const_mul hhi _) Ioo_subset_Ioc_self
  rw [integral_const_mul] at hlo hhi'
  rw [integral_sub hfi (hmh.const_mul c), integral_const_mul, hhv] at hlo hhi'
  -- boundary term
  have hQ := zr3_i_pt (γin := γin) (γout := γout) hβ0 hβ1 hH0
  have hkb := abs_le.1 hQ.2.2.1
  have hWH : 0 ≤ isoWm γin γout H := Real.sqrt_nonneg _
  have hWW : isoWm γin γout H ≤ isoWm γin γout 0 := by
    unfold isoWm
    apply Real.sqrt_le_sqrt
    have h2 := min_le_left γin γout
    have h3 := min_le_right γin γout
    nlinarith [mul_nonneg (by linarith : 0 ≤ γin - H) (by linarith : 0 ≤ γout - H)]
  have hit : isoIt β γin γout H = (∫ m in Ioc 0 H, (-deriv (isoWm γin γout) m) * isoIlevel β m)
      + (1 / 2) * isoWm γin γout H * isoLambdaB β H := by
    unfold isoIt
    rw [intervalIntegral.integral_of_le hH0.le]
  have hWint : ∫ m in (0:ℝ)..H, isoWm γin γout m = ∫ m in Ioc 0 H, isoWm γin γout m :=
    intervalIntegral.integral_of_le hH0.le
  rw [hit, hWint, ← hibp]
  have hexp : c * ((∫ m in Ioc 0 H, m * (-deriv (isoWm γin γout) m)) + H * isoWm γin γout H)
      = c * (∫ m in Ioc 0 H, m * (-deriv (isoWm γin γout) m)) + c * H * isoWm γin γout H := by ring
  have e2 : (1 / 2) * isoWm γin γout H * isoLambdaB β H - c * H * isoWm γin γout H
      = (1 / 2) * isoWm γin γout H * (isoLambdaB β H - Real.sqrt (2 * Real.pi) * H) := by
    rw [hc]; ring
  constructor <;> nlinarith [mul_nonneg hWH hg0']

private lemma zr3_level {β γin γout ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hϱ : 0 ≤ ϱ) :
    0 < isoMLevel β γin γout ϱ ∧ isoMLevel β γin γout ϱ ≤ min γin γout := by
  rcases hϱ.eq_or_lt with h0 | hpos
  · subst h0
    have : isoMLevel β γin γout 0 = min γin γout := by
      unfold isoMLevel
      rw [if_pos rfl, if_neg (fun h => hβ0.ne' h.1)]
    rw [this]
    exact ⟨lt_min hγin hγout, le_rfl⟩
  · have hr := zr_isoLink hβ0.le hβ1
    obtain ⟨hq0, hqlt, hqeq⟩ := zr_root_mem hr hγin hγout hpos
    have hbpos := (zr_root_bounds hr hγin hγout hpos).1
    have hmL : isoMLevel β γin γout ϱ =
        rW (Muon.emaW β) (isoRoot (rW (Muon.emaW β)) γin γout ϱ) := by
      unfold isoMLevel psiIso
      rw [if_neg hpos.ne']
      rfl
    rw [hmL]
    refine ⟨?_, hqlt.le⟩
    have := hr.2.1 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hbpos.le) hbpos
    rwa [hr.2.2] at this

private lemma zr3_W0 {γin γout : ℝ} : isoWm γin γout 0 = Real.sqrt (γin * γout) := by
  unfold isoWm; simp

private lemma zr3_core {β γin γout ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hϱ : 0 ≤ ϱ) :
    |(∫ u in Ioi (0 : ℝ), isoGb β γin γout (ϱ + u ^ 2))
        - Real.sqrt (2 * Real.pi) / 2 * ∫ m in (0 : ℝ)..(isoMLevel β γin γout ϱ),
            isoWm γin γout m|
      ≤ (isoGSup β + isoGPrimeSup β / 2) * Real.sqrt (γin * γout) := by
  obtain ⟨hH0, hHm⟩ := zr3_level hβ0 hβ1 hγin hγout hϱ
  obtain ⟨hA, hB, -⟩ := zr2_main (Or.inl ⟨hβ0, hβ1⟩) hγin hγout hϱ
  obtain ⟨hit1, hit2⟩ := zr3_it (γin := γin) (γout := γout) hβ0 hβ1 hH0 hHm
  have hpt := zr3_pt hβ0 hβ1 (zr2_Qlevel_nonneg β (isoMLevel β γin γout ϱ))
  have hWH : 0 ≤ isoWm γin γout (isoMLevel β γin γout ϱ) := Real.sqrt_nonneg _
  rw [zr3_W0] at hit1 hit2
  have hW0 : 0 ≤ Real.sqrt (γin * γout) := Real.sqrt_nonneg _
  have hq := mul_le_mul_of_nonneg_left hpt.2.1 hWH
  rw [abs_le]
  constructor <;> nlinarith [hpt.2.2.2.1, hpt.2.2.2.2]

private lemma zr3_bound_lt {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {s : ℝ} (hs : 0 < s) :
    Real.sqrt 2 * (isoGSup β + isoGPrimeSup β / 2) / (Real.pi * s)
      < 2.32 / ((1 - β) * s) := by
  have h1 : (0:ℝ) < 1 - β := by linarith
  have hg := (lem_app_iso_constants_ii hβ0 hβ1).2
  have hg' := (lem_app_iso_constants_iii hβ0 hβ1).2
  have hpi := Real.pi_pos
  have hsum : isoGSup β + isoGPrimeSup β / 2 < (2 + Real.pi) / (1 - β) := by
    have : (2 + Real.pi) / (1 - β) = 2 / (1 - β) + Real.pi / (1 - β) := by ring
    have h2 : 2 * Real.pi / (1 - β) / 2 = Real.pi / (1 - β) := by ring
    rw [this]
    linarith
  have hs2 : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  have hnum : Real.sqrt 2 * (2 + Real.pi) < 2.32 * Real.pi := by
    nlinarith [Real.sqrt_nonneg 2]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have h3 : Real.sqrt 2 * (isoGSup β + isoGPrimeSup β / 2) <
      Real.sqrt 2 * ((2 + Real.pi) / (1 - β)) :=
    mul_lt_mul_of_pos_left hsum (Real.sqrt_pos.2 (by norm_num))
  have h4 : Real.sqrt 2 * ((2 + Real.pi) / (1 - β)) < 2.32 * Real.pi / (1 - β) := by
    rw [← mul_div_assoc]
    exact div_lt_div_of_pos_right hnum h1
  have h5 : Real.sqrt 2 * (isoGSup β + isoGPrimeSup β / 2) * ((1 - β) * s)
      < 2.32 * (Real.pi * s) := by
    have := mul_lt_mul_of_pos_right (h3.trans h4) (mul_pos h1 hs)
    calc _ < 2.32 * Real.pi / (1 - β) * ((1 - β) * s) := this
      _ = 2.32 * (Real.pi * s) := by field_simp
  exact h5

private lemma zr3_master_i {β γin γout ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hϱ : 0 ≤ ϱ) :
    |dIso β γin γout ϱ
        - 1 / (Real.sqrt Real.pi * γin * γout)
          * ∫ m in (0 : ℝ)..(isoMLevel β γin γout ϱ), isoWm γin γout m|
      ≤ Real.sqrt 2 * (isoGSup β + isoGPrimeSup β / 2) / (Real.pi * Real.sqrt (γin * γout)) := by
  have hcore := zr3_core hβ0 hβ1 hγin hγout hϱ
  set I := ∫ m in (0 : ℝ)..(isoMLevel β γin γout ϱ), isoWm γin γout m with hI
  set J := ∫ u in Ioi (0 : ℝ), isoGb β γin γout (ϱ + u ^ 2) with hJ
  have hpi := Real.pi_pos
  have hsp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt hpi.le
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsP : Real.sqrt (γin * γout) * Real.sqrt (γin * γout) = γin * γout :=
    Real.mul_self_sqrt (by positivity)
  have hsPpos : 0 < Real.sqrt (γin * γout) := Real.sqrt_pos.2 (by positivity)
  have hspos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 hpi
  have e : dIso β γin γout ϱ - 1 / (Real.sqrt Real.pi * γin * γout) * I
      = Real.sqrt 2 / (Real.pi * γin * γout) * (J - Real.sqrt (2 * Real.pi) / 2 * I) := by
    unfold dIso
    rw [Real.sqrt_mul (by norm_num) Real.pi]
    field_simp
    linear_combination (I * (Real.sqrt Real.pi * Real.sqrt Real.pi)) * hs2 + (2 * I) * hsp
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < Real.sqrt 2 / (Real.pi * γin * γout))]
  calc Real.sqrt 2 / (Real.pi * γin * γout) * |J - Real.sqrt (2 * Real.pi) / 2 * I|
      ≤ Real.sqrt 2 / (Real.pi * γin * γout) *
        ((isoGSup β + isoGPrimeSup β / 2) * Real.sqrt (γin * γout)) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = Real.sqrt 2 * (isoGSup β + isoGPrimeSup β / 2) / (Real.pi * Real.sqrt (γin * γout)) := by
        have hsq : Real.sqrt (γin * γout) ^ 2 = γin * γout := Real.sq_sqrt (by positivity)
        field_simp
        rw [hsq]
        ring

private lemma zr3_xi {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hϱ : 0 ≤ ϱ) :
    1 / (Real.sqrt Real.pi * γ * γ)
        * ∫ m in (0 : ℝ)..(isoMLevel β γ γ ϱ), isoWm γ γ m
      = isoXi0 (isoMLevel β γ γ ϱ / γ) := by
  obtain ⟨hH0, hHm⟩ := zr3_level hβ0 hβ1 hγ hγ hϱ
  rw [min_self] at hHm
  set ψ := isoMLevel β γ γ ϱ
  have hint : ∫ m in (0 : ℝ)..ψ, isoWm γ γ m = ∫ m in (0 : ℝ)..ψ, (γ - m) := by
    refine intervalIntegral.integral_congr (fun m hm => ?_)
    rw [Set.uIcc_of_le hH0.le] at hm
    show isoWm γ γ m = γ - m
    unfold isoWm
    rw [← sq, Real.sqrt_sq (by linarith [hm.2])]
  rw [hint]
  simp only [intervalIntegral.integral_sub, intervalIntegral.integral_const, integral_id,
    intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
  unfold isoXi0
  have hsp := Real.sqrt_pos.2 Real.pi_pos
  field_simp
  ring


/-- `thm:app-iso-master`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1387–1402):
```latex
\begin{theorem}[Master drift estimate]\label{thm:app-iso-master}
Let $\bmom\in(0,1)$, $\gin,\gout>0$ and $\ridge\ge0$, with the convention
$\psi(0)\defeq\gamma_\wedge$.
\begin{enumerate}[label=(\roman*)]
\item The drift satisfies
\begin{equation}\label{eqn:app-iso-master}
\Big|\mathfrak d_{\mathrm{iso}}(\ridge)-\frac{1}{\sqrt\pi\,\gin\gout}\int_0^{\psi(\ridge)}\mathsf W(m)\,\dif m\Big|
\le\frac{\sqrt2\,(\mathsf g_\bmom+\mathsf g'_\bmom/2)}{\pi\sqrt{\gin\gout}}
<\frac{2.32}{(1-\bmom)\sqrt{\gin\gout}} .
\end{equation}
\item In the square case, with $\Xi_0(x)\defeq\pi^{-1/2}\big(x-\tfrac12x^2\big)$,
\begin{equation}\label{eqn:app-iso-Xi}
\Big|\mathfrak d_{\mathrm{iso}}(\ridge)-\Xi_0\Big(\frac{\psi(\ridge)}\gamma\Big)\Big|<\frac{2.32}{(1-\bmom)\gamma} .
\end{equation}
\end{enumerate}
\end{theorem}
```

Part (i): the general aspect-ratio bound. `isoGSup β = g_β` and `isoGPrimeSup β = g'_β`
(`Muon.Isotropic.Helpers`, `lem:app-iso-constants`(ii),(iii)). The strict bound is stated as a
second conjunct, as in the source's `≤ ... <`. -/
theorem thm_app_iso_master_i {β γin γout ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hϱ : 0 ≤ ϱ) :
    |dIso β γin γout ϱ
        - 1 / (Real.sqrt Real.pi * γin * γout)
          * ∫ m in (0 : ℝ)..(isoMLevel β γin γout ϱ), isoWm γin γout m|
      ≤ Real.sqrt 2 * (isoGSup β + isoGPrimeSup β / 2) / (Real.pi * Real.sqrt (γin * γout)) ∧
    Real.sqrt 2 * (isoGSup β + isoGPrimeSup β / 2) / (Real.pi * Real.sqrt (γin * γout))
      < 2.32 / ((1 - β) * Real.sqrt (γin * γout)) := by
  exact ⟨zr3_master_i hβ0 hβ1 hγin hγout hϱ,
    zr3_bound_lt hβ0 hβ1 (Real.sqrt_pos.2 (mul_pos hγin hγout))⟩

/-- `thm:app-iso-master`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1387–1402):
```latex
\begin{theorem}[Master drift estimate]\label{thm:app-iso-master}
Let $\bmom\in(0,1)$, $\gin,\gout>0$ and $\ridge\ge0$, with the convention
$\psi(0)\defeq\gamma_\wedge$.
\begin{enumerate}[label=(\roman*)]
\item The drift satisfies
\begin{equation}\label{eqn:app-iso-master}
\Big|\mathfrak d_{\mathrm{iso}}(\ridge)-\frac{1}{\sqrt\pi\,\gin\gout}\int_0^{\psi(\ridge)}\mathsf W(m)\,\dif m\Big|
\le\frac{\sqrt2\,(\mathsf g_\bmom+\mathsf g'_\bmom/2)}{\pi\sqrt{\gin\gout}}
<\frac{2.32}{(1-\bmom)\sqrt{\gin\gout}} .
\end{equation}
\item In the square case, with $\Xi_0(x)\defeq\pi^{-1/2}\big(x-\tfrac12x^2\big)$,
\begin{equation}\label{eqn:app-iso-Xi}
\Big|\mathfrak d_{\mathrm{iso}}(\ridge)-\Xi_0\Big(\frac{\psi(\ridge)}\gamma\Big)\Big|<\frac{2.32}{(1-\bmom)\gamma} .
\end{equation}
\end{enumerate}
\end{theorem}
```

Part (ii): the square case `γin = γout = γ`, with `Ξ_0` (`isoXi0`). -/
theorem thm_app_iso_master_ii {β γ ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < γ) (hϱ : 0 ≤ ϱ) :
    |dIso β γ γ ϱ - isoXi0 (isoMLevel β γ γ ϱ / γ)| < 2.32 / ((1 - β) * γ) := by
  have hs : Real.sqrt (γ * γ) = γ := Real.sqrt_mul_self hγ.le
  have h1 := zr3_master_i hβ0 hβ1 hγ hγ hϱ
  have h2 := zr3_bound_lt hβ0 hβ1 (Real.sqrt_pos.2 (mul_pos hγ hγ))
  rw [zr3_xi hβ0 hβ1 hγ hϱ] at h1
  rw [hs] at h1 h2
  exact lt_of_le_of_lt h1 h2

/-! ## The constant at aspect ratio at least one -/

/-! Private helpers for `prop:app-iso-exact` and `prop:app-iso-beta-zero` (task P-F.3.P4). -/

private lemma zr4_W_sq {γ m : ℝ} (hm : m ≤ γ) : isoWm γ γ m = γ - m := by
  unfold isoWm
  rw [show (γ - m) * (γ - m) = (γ - m) ^ 2 by ring]
  exact Real.sqrt_sq (by linarith)

private lemma zr4_deriv {γ m : ℝ} (hm : m < γ) : deriv (isoWm γ γ) m = -1 := by
  have hm' : m < min γ γ := by rw [min_self]; exact hm
  rw [(zr2_W_deriv hm').deriv, zr4_W_sq hm.le]
  have hp : (0:ℝ) < 2 * (γ - m) := by linarith
  rw [div_eq_iff hp.ne']
  ring

private lemma zr4_sqrt2pi : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
  Real.sqrt_mul (by norm_num) _

private lemma zr4_lamB : isoLambdaB 0 1 = Real.sqrt (2 * Real.pi) := by
  unfold isoLambdaB
  rw [if_pos ⟨rfl, rfl⟩]

private lemma zr4_int_eq {γ : ℝ} (hγ : 1 ≤ γ) (f : ℝ → ℝ) :
    ∫ m in (0:ℝ)..1, -deriv (isoWm γ γ) m * f m = ∫ m in (0:ℝ)..1, f m := by
  apply intervalIntegral.integral_congr_ae
  have h1 : ∀ᵐ m ∂(volume : Measure ℝ), m ≠ 1 := by
    rw [ae_iff]; simp
  filter_upwards [h1] with m hm1 hmI
  rw [Set.uIoc_of_le zero_le_one] at hmI
  have hm : m < γ := lt_of_lt_of_le (lt_of_le_of_ne hmI.2 hm1) hγ
  simp only [zr4_deriv hm]
  ring

private lemma zr4_Cbeta_formula {γ : ℝ} (hγ : 1 ≤ γ) :
    Cbeta 0 γ γ = Real.sqrt 2 / (Real.pi * γ * γ) *
      ((∫ m in (0:ℝ)..1, isoIlevel 0 m) + (1 / 2) * (γ - 1) * Real.sqrt (2 * Real.pi)) := by
  have hγ0 : (0:ℝ) < γ := by linarith
  have hmin : 1 ≤ min γ γ := by rw [min_self]; exact hγ
  have hm1 : isoMLevel 0 γ γ 0 = 1 := by
    unfold isoMLevel; rw [if_pos rfl, if_pos ⟨rfl, hmin⟩]
  have h := (lem_app_iso_participation_ii (β := 0) (γin := γ) (γout := γ) (ϱ := 0) rfl hmin
    hγ0 hγ0 le_rfl).2.2 rfl
  rw [hm1] at h
  simp only [zero_add] at h
  unfold isoIt at h
  rw [zr4_int_eq hγ (isoIlevel 0), zr4_W_sq (show (1:ℝ) ≤ γ from hγ), zr4_lamB] at h
  unfold Cbeta
  rw [h]

private lemma zr4_alg (γ n y C1 Y s : ℝ) (hs : 0 < s) (hγ : 0 < γ) (hy : γ = n + y) :
    γ ^ 2 * ((n * C1 + Y) / γ ^ 2 + (n * (n - 1) / 2 + n * y) / (s * γ ^ 2)
        - ((γ - 1) / (s * γ ^ 2) + C1 / γ ^ 2))
      = (n - 1) * C1 + Y + ((n - 1) * (n - 2) / 2 + (n - 1) * y) / s := by
  have hg : γ ≠ 0 := hγ.ne'
  have hsn : s ≠ 0 := hs.ne'
  have hpoly : n * (n - 1) / 2 + n * y - (γ - 1) = (n - 1) * (n - 2) / 2 + (n - 1) * y := by
    rw [hy]; ring
  have e : γ ^ 2 * ((n * C1 + Y) / γ ^ 2 + (n * (n - 1) / 2 + n * y) / (s * γ ^ 2)
        - ((γ - 1) / (s * γ ^ 2) + C1 / γ ^ 2))
      = (n * C1 + Y) + (n * (n - 1) / 2 + n * y) / s - (γ - 1) / s - C1 := by
    field_simp
    ring
  have hsub : (n * (n - 1) / 2 + n * y) / s - (γ - 1) / s
      = ((n - 1) * (n - 2) / 2 + (n - 1) * y) / s := by
    rw [← sub_div, hpoly]
  rw [e]
  linear_combination hsub

private lemma zr4_isoNint_small {γ : ℝ} (hlt : γ < 1) : isoNint γ = 0 := by
  unfold isoNint
  rw [Nat.floor_eq_zero.mpr hlt]
  simp

/-- `prop:app-iso-exact`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.1738–1743):
```latex
\begin{proposition}[The constant for $N\ge B$]\label{prop:app-iso-exact}
For every $\gamma\ge1$,
\[
C(\gamma)=\frac{\gamma-1}{\sqrt\pi\,\gamma^2}+\frac{C(1)}{\gamma^2}.
\]
\end{proposition}
```

Here `C(γ) = Cbeta 0 γ γ` (the card's identification `C = C₀`) and `C(1) = Cbeta 0 1 1`. -/
theorem prop_app_iso_exact {γ : ℝ} (hγ : 1 ≤ γ) :
    Cbeta 0 γ γ = (γ - 1) / (Real.sqrt Real.pi * γ ^ 2) + Cbeta 0 1 1 / γ ^ 2 := by
  have h1 := zr4_Cbeta_formula hγ
  have h2 := zr4_Cbeta_formula (le_refl (1:ℝ))
  rw [h1, h2, zr4_sqrt2pi]
  have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; linarith
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have ht : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hss : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  field_simp
  linear_combination (Real.sqrt Real.pi * Real.sqrt Real.pi * (γ - 1)) * ht + (2 * (γ - 1)) * hss

/-! ## Order of limits and zero ridge as the momentum vanishes -/

/-! Private helpers for `prop:app-iso-beta-zero`(i) (task P-F.3.P6). -/

private lemma zr6_phi_zero : isoPhi 0 = 0 := by simp [isoPhi]

private lemma zr6_phi_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ isoPhi x := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, zr6_phi_zero]
  · exact (lem_app_iso_gaussian_ii.2.2 x h).1.le

private lemma zr6_phi_lt_one {x : ℝ} (hx : 0 ≤ x) : isoPhi x < 1 := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, zr6_phi_zero]; exact one_pos
  · exact (lem_app_iso_gaussian_ii.2.2 x h).2

private lemma zr6_phi_le {x : ℝ} (hx : 0 ≤ x) : isoPhi x ≤ x := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, zr6_phi_zero]
  · exact (lem_app_iso_weights_ii.1 x h).trans (min_le_right _ _)

private lemma zr6_phi_mono : MonotoneOn isoPhi (Ici 0) := by
  intro a ha b hb hab
  rcases (Set.mem_Ici.1 ha).eq_or_lt with h | h
  · rw [← h, zr6_phi_zero]; exact zr6_phi_nonneg (Set.mem_Ici.1 hb)
  · exact lem_app_iso_gaussian_ii.1.monotoneOn (Set.mem_Ioi.2 h)
      (Set.mem_Ioi.2 (lt_of_lt_of_le h hab)) hab

private lemma zr6_phi_strict {a b : ℝ} (ha : 0 < a) (hab : a < b) : isoPhi a < isoPhi b :=
  lem_app_iso_gaussian_ii.1 (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 (ha.trans hab)) hab

private lemma zr6_J_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Muon.DetEquiv.J x := by
  unfold Muon.DetEquiv.J
  exact integral_nonneg (fun g => div_nonneg (sq_nonneg g)
    (by nlinarith [mul_nonneg hx (sq_nonneg g)]))

private lemma zr6_J_contAt {x : ℝ} (hx : 0 < x) : ContinuousAt Muon.DetEquiv.J x :=
  (lem_app_iso_weights_iii.2 x hx).1.continuousAt

private lemma zr6_lam_nonneg0 {z : ℝ} (hz : 0 ≤ z) : 0 ≤ isoLambda 0 z :=
  zr2_lam_nonneg (le_refl (0:ℝ)) zero_lt_one hz

/-- `h(x) = √x J(x) + ½ Λ_0(x)`. Bounds. -/
private lemma zr6_h_bounds {x : ℝ} (hx : 0 < x) :
    0 ≤ Real.sqrt x * Muon.DetEquiv.J x + (1 / 2) * isoLambda 0 x ∧
    Real.sqrt x * Muon.DetEquiv.J x + (1 / 2) * isoLambda 0 x ≤ 2 * Real.sqrt x ∧
    |Real.sqrt x * Muon.DetEquiv.J x + (1 / 2) * isoLambda 0 x - (1 / 2) * Real.sqrt (2 * Real.pi)|
      ≤ 2 / Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have hJ := lem_app_iso_weights_iii.1 x hx
  have hJ0 := zr6_J_nonneg hx.le
  have hL0 := zr6_lam_nonneg0 hx.le
  have hL1 := lem_app_iso_weights_iv (β := 0) (le_refl 0) zero_lt_one
  have hL2 := hL1.2.1 x hx.le
  have hL3 := hL1.2.2.1 x hx
  rw [zr2_rpow_neg_half hx] at hL3
  have a1 : Real.sqrt x * Muon.DetEquiv.J x ≤ Real.sqrt x :=
    mul_le_of_le_one_right hs.le (hJ.trans (min_le_left _ _))
  have a2 : Real.sqrt x * Muon.DetEquiv.J x ≤ 1 / Real.sqrt x := by
    calc Real.sqrt x * Muon.DetEquiv.J x ≤ Real.sqrt x * (1 / x) :=
          mul_le_mul_of_nonneg_left (hJ.trans (min_le_right _ _)) hs.le
      _ = 1 / Real.sqrt x := by
          rw [mul_one_div, div_eq_div_iff hx.ne' hs.ne', one_mul, hsq]
  have a0 : 0 ≤ Real.sqrt x * Muon.DetEquiv.J x := mul_nonneg hs.le hJ0
  refine ⟨by linarith, by linarith, ?_⟩
  have e : 2 / Real.sqrt x = 1 / Real.sqrt x + 1 / Real.sqrt x := by ring
  rw [abs_le]
  constructor <;> linarith [hL3.1, hL3.2]

private lemma zr6_ema_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (j : ℕ) :
    0 < Muon.emaW β j := by
  unfold Muon.emaW
  have : 0 < 1 - β := by linarith
  positivity

private lemma zr6_sub_tsum {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (f : ℕ → ℝ) :
    ∑' j : {j : ℕ | 0 < Muon.emaW β j}, f j = ∑' j, f j :=
  tsum_subtype_eq_of_support_subset (fun j _ => zr6_ema_pos hβ0 hβ1 j)

private lemma zr6_x_eq (β Q : ℝ) (j : ℕ) :
    Muon.emaW β j ^ 2 * Q = ((1 - β) ^ 2 * Q) * (β ^ 2) ^ j := by
  unfold Muon.emaW
  rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
  ring

private lemma zr6_x_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (Q : ℝ) :
    Summable (fun j : ℕ => Muon.emaW β j ^ 2 * Q) := by
  have hg : Summable (fun j : ℕ => (β ^ 2) ^ j) :=
    summable_geometric_of_lt_one (sq_nonneg β) (by nlinarith)
  exact (hg.mul_left ((1 - β) ^ 2 * Q)).congr (fun j => (zr6_x_eq β Q j).symm)

private lemma zr6_sqrt_x (β Q : ℝ) {j : ℕ} (hβ : 0 ≤ Muon.emaW β j) :
    Real.sqrt (Muon.emaW β j ^ 2 * Q) = Muon.emaW β j * Real.sqrt Q := by
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hβ]

private lemma zr6_sqrt_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (Q : ℝ) :
    Summable (fun j : ℕ => Real.sqrt (Muon.emaW β j ^ 2 * Q)) := by
  have := (zr_emaW_summable hβ0.le hβ1).mul_right (Real.sqrt Q)
  exact this.congr (fun j => (zr6_sqrt_x β Q (zr6_ema_pos hβ0 hβ1 j).le).symm)

private lemma zr6_phi_hasSum {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : ℝ} (hQ : 0 ≤ Q) :
    HasSum (fun j : ℕ => isoPhi (Muon.emaW β j ^ 2 * Q)) (rW (Muon.emaW β) Q) := by
  have hs : Summable (fun j : ℕ => isoPhi (Muon.emaW β j ^ 2 * Q)) :=
    Summable.of_nonneg_of_le (fun j => zr6_phi_nonneg (mul_nonneg (sq_nonneg _) hQ))
      (fun j => zr6_phi_le (mul_nonneg (sq_nonneg _) hQ)) (zr6_x_summable hβ0.le hβ1 Q)
  have h := (lem_app_iso_weights_i hβ0.le hβ1).1 Q hQ
  rw [zr6_sub_tsum hβ0 hβ1 (fun j => isoPhi (Muon.emaW β j ^ 2 * Q))] at h
  rw [h]
  exact hs.hasSum

private lemma zr6_I_hasSum {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : ℝ} (hQ : 0 < Q) :
    HasSum (fun j : ℕ => Real.sqrt (Muon.emaW β j ^ 2 * Q) * Muon.DetEquiv.J (Muon.emaW β j ^ 2 * Q)
        + (1 / 2) * isoLambda 0 (Muon.emaW β j ^ 2 * Q))
      (Real.sqrt Q * Lw (Muon.emaW β) Q + (1 / 2) * isoLambda β Q) := by
  have hxpos : ∀ j : ℕ, 0 < Muon.emaW β j ^ 2 * Q := fun j =>
    mul_pos (pow_pos (zr6_ema_pos hβ0 hβ1 j) 2) hQ
  have hsq := zr6_sqrt_summable hβ0 hβ1 Q
  have ha : Summable (fun j : ℕ => Real.sqrt (Muon.emaW β j ^ 2 * Q) *
      Muon.DetEquiv.J (Muon.emaW β j ^ 2 * Q)) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (Real.sqrt_nonneg _)
      (zr6_J_nonneg (hxpos j).le))
      (fun j => mul_le_of_le_one_right (Real.sqrt_nonneg _)
        ((lem_app_iso_weights_iii.1 _ (hxpos j)).trans (min_le_left _ _))) hsq
  have hb : Summable (fun j : ℕ => isoLambda 0 (Muon.emaW β j ^ 2 * Q)) :=
    Summable.of_nonneg_of_le (fun j => zr6_lam_nonneg0 (hxpos j).le)
      (fun j => (lem_app_iso_weights_iv (β := 0) (le_refl 0) zero_lt_one).2.1 _ (hxpos j).le)
      (hsq.mul_left 2)
  have hLam := (lem_app_iso_weights_iv hβ0.le hβ1).1 Q hQ.le
  rw [zr6_sub_tsum hβ0 hβ1 (fun j => isoLambda 0 (Muon.emaW β j ^ 2 * Q))] at hLam
  have hL : Real.sqrt Q * Lw (Muon.emaW β) Q = ∑' j : ℕ, Real.sqrt (Muon.emaW β j ^ 2 * Q) *
      Muon.DetEquiv.J (Muon.emaW β j ^ 2 * Q) := by
    unfold Lw
    rw [← tsum_mul_left]
    congr 1
    funext j
    rw [zr6_sqrt_x β Q (zr6_ema_pos hβ0 hβ1 j).le]
    ring
  rw [hL, hLam]
  exact ha.hasSum.add (hb.hasSum.mul_left (1 / 2))

private lemma zr6_Q_spec {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 ≤ m) :
    0 ≤ isoQlevel β m ∧ rW (Muon.emaW β) (isoQlevel β m) = m := by
  have hex := zr2_surj (H := m) hβ0.le hβ1 hm (Or.inl hβ0)
  unfold isoQlevel
  rw [dif_pos hex]
  exact hex.choose_spec

private lemma zr6_hasSum_split {f : ℕ → ℝ} {a : ℝ} (h : HasSum f a) (k : ℕ) :
    HasSum (fun i => f (i + 1 + k)) (a - ∑ j ∈ Finset.range k, f j - f k) := by
  have h1 := (hasSum_nat_add_iff' k).2 h
  have h2 := (hasSum_nat_add_iff' 1).2 h1
  simpa [Finset.sum_range_one, sub_sub] using h2

private lemma zr6_single {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (k : ℕ) {t : ℝ}
    (ht0 : 0 < t) {Q X : ℝ}
    (hQ : Q = isoQlevel β ((k : ℝ) + t)) (hX : X = Muon.emaW β k ^ 2 * Q) :
    (1 - β ^ 2) * t ≤ X ∧
    isoPhi X ≤ ((k:ℝ) + t) - k * isoPhi (X / β ^ 2) ∧
    ((k:ℝ) + t) - k - X * β ^ 2 / (1 - β ^ 2) ≤ isoPhi X ∧
    ((k:ℝ) + 1) * isoPhi X ≤ (k:ℝ) + t ∧
    0 < X ∧
    |isoIlevel β ((k:ℝ) + t) - ((k:ℝ) / 2 * Real.sqrt (2 * Real.pi)
        + (Real.sqrt X * Muon.DetEquiv.J X + (1 / 2) * isoLambda 0 X))|
      ≤ 2 * k * β / Real.sqrt X + 2 * Real.sqrt X * β / (1 - β) := by
  have hm0 : 0 ≤ (k:ℝ) + t := by positivity
  obtain ⟨hQ0, hQr⟩ := zr6_Q_spec hβ0 hβ1 hm0
  rw [← hQ] at hQ0 hQr
  have hQpos : 0 < Q := by
    rcases hQ0.eq_or_lt with h | h
    · exfalso
      rw [← h] at hQr
      have h0 : rW (Muon.emaW β) 0 = 0 := (zr_isoLink hβ0.le hβ1).2.2
      rw [h0] at hQr
      have : (0:ℝ) < k + t := by positivity
      linarith
    · exact h
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ, ∀ j, x j = Muon.emaW β j ^ 2 * Q := ⟨_, fun j => rfl⟩
  have hxpos : ∀ j, 0 < x j := fun j => by
    rw [hx]; exact mul_pos (pow_pos (zr6_ema_pos hβ0 hβ1 j) 2) hQpos
  have hXx : X = x k := by rw [hX, hx]
  have hXpos : 0 < X := by rw [hXx]; exact hxpos k
  have hb2 : β ^ 2 < 1 := by nlinarith
  have hb2pos : 0 < β ^ 2 := by positivity
  have h1b : 0 < 1 - β ^ 2 := by linarith
  have hxe : ∀ j, x j = ((1 - β) ^ 2 * Q) * (β ^ 2) ^ j := fun j => by rw [hx]; exact zr6_x_eq β Q j
  have hXe : X = ((1 - β) ^ 2 * Q) * (β ^ 2) ^ k := by rw [hXx]; exact hxe k
  have htail : ∀ i : ℕ, x (i + 1 + k) = X * β ^ 2 * (β ^ 2) ^ i := by
    intro i; rw [hxe, hXe]; ring
  have hhead : ∀ j, j < k → X ≤ β ^ 2 * x j := by
    intro j hj
    rw [hxe, hXe]
    have hpw : (β ^ 2) ^ k ≤ (β ^ 2) ^ (j + 1) := pow_le_pow_of_le_one hb2pos.le hb2.le hj
    have hc : 0 ≤ (1 - β) ^ 2 * Q := by positivity
    calc ((1 - β) ^ 2 * Q) * (β ^ 2) ^ k ≤ ((1 - β) ^ 2 * Q) * (β ^ 2) ^ (j + 1) :=
          mul_le_mul_of_nonneg_left hpw hc
      _ = _ := by ring
  have hhead' : ∀ j, j < k → X / β ^ 2 ≤ x j := fun j hj => by
    rw [div_le_iff₀ hb2pos]; linarith [hhead j hj]
  -- Phi sums
  have hPhi : HasSum (fun j => isoPhi (x j)) ((k:ℝ) + t) := by
    have := zr6_phi_hasSum hβ0 hβ1 hQ0
    rw [hQr] at this
    simpa only [hx] using this
  have hsplit := zr6_hasSum_split hPhi k
  rw [← hXx] at hsplit
  have hgeo : HasSum (fun i : ℕ => x (i + 1 + k)) (X * β ^ 2 / (1 - β ^ 2)) := by
    have := (hasSum_geometric_of_lt_one hb2pos.le hb2).mul_left (X * β ^ 2)
    simp_rw [htail]
    rw [div_eq_mul_inv]
    exact this
  have hS3nn : 0 ≤ ((k:ℝ) + t) - ∑ j ∈ Finset.range k, isoPhi (x j) - isoPhi X :=
    hsplit.nonneg (fun i => zr6_phi_nonneg (hxpos _).le)
  have hS3le : ((k:ℝ) + t) - ∑ j ∈ Finset.range k, isoPhi (x j) - isoPhi X
      ≤ X * β ^ 2 / (1 - β ^ 2) :=
    hasSum_le (fun i => zr6_phi_le (hxpos _).le) hsplit hgeo
  have hS1le : ∑ j ∈ Finset.range k, isoPhi (x j) ≤ k := by
    calc ∑ j ∈ Finset.range k, isoPhi (x j) ≤ ∑ j ∈ Finset.range k, (1:ℝ) :=
          Finset.sum_le_sum (fun j _ => (zr6_phi_lt_one (hxpos j).le).le)
      _ = k := by simp
  have hXb : 0 ≤ X / β ^ 2 := by positivity
  have hS1ge : (k:ℝ) * isoPhi (X / β ^ 2) ≤ ∑ j ∈ Finset.range k, isoPhi (x j) := by
    calc (k:ℝ) * isoPhi (X / β ^ 2) = ∑ j ∈ Finset.range k, isoPhi (X / β ^ 2) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j hj => zr6_phi_mono (Set.mem_Ici.2 hXb)
          (Set.mem_Ici.2 (hxpos j).le) (hhead' j (Finset.mem_range.1 hj)))
  have hXX : X ≤ X / β ^ 2 := by
    rw [le_div_iff₀ hb2pos]; nlinarith
  have hPX : isoPhi X ≤ isoPhi (X / β ^ 2) :=
    zr6_phi_mono (Set.mem_Ici.2 hXpos.le) (Set.mem_Ici.2 hXb) hXX
  have hPXle : isoPhi X ≤ X := zr6_phi_le hXpos.le
  have hkn : (0:ℝ) ≤ k := by positivity
  refine ⟨?_, by linarith, by linarith, ?_, hXpos, ?_⟩
  · -- lower bound for X
    have hu : X * β ^ 2 / (1 - β ^ 2) * (1 - β ^ 2) = X * β ^ 2 := by field_simp
    set u := X * β ^ 2 / (1 - β ^ 2) with hudef
    have h1 : t ≤ X + u := by linarith
    nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hPX hkn]
  · -- the I sum
    have hI := zr6_I_hasSum hβ0 hβ1 hQpos
    have hIl : isoIlevel β ((k:ℝ) + t) = Real.sqrt Q * Lw (Muon.emaW β) Q
        + (1 / 2) * isoLambda β Q := by
      unfold isoIlevel isoLambdaB
      rw [if_neg (by rintro ⟨h, -⟩; exact hβ0.ne' h), ← hQ]
    rw [← hIl] at hI
    have hI' : HasSum (fun j => Real.sqrt (x j) * Muon.DetEquiv.J (x j)
        + (1 / 2) * isoLambda 0 (x j)) (isoIlevel β ((k:ℝ) + t)) := by
      simpa only [hx] using hI
    have hsI := zr6_hasSum_split hI' k
    rw [← hXx] at hsI
    set I := isoIlevel β ((k:ℝ) + t) with hIdef
    set H1 := ∑ j ∈ Finset.range k, (Real.sqrt (x j) * Muon.DetEquiv.J (x j)
        + (1 / 2) * isoLambda 0 (x j)) with hH1
    set hX0 := Real.sqrt X * Muon.DetEquiv.J X + (1 / 2) * isoLambda 0 X with hhX0
    set I3 := I - H1 - hX0 with hI3
    have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hXpos
    -- tail
    have hsqt : ∀ i : ℕ, Real.sqrt (x (i + 1 + k)) = Real.sqrt X * β * β ^ i := by
      intro i
      rw [htail]
      have : X * β ^ 2 * (β ^ 2) ^ i = (Real.sqrt X * β * β ^ i) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hXpos.le, ← pow_mul, ← pow_mul, mul_comm i 2]
      rw [this, Real.sqrt_sq (by positivity)]
    have hgeo2 : HasSum (fun i : ℕ => 2 * (Real.sqrt X * β * β ^ i))
        (2 * (Real.sqrt X * β) * (1 - β)⁻¹) := by
      have := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left (2 * (Real.sqrt X * β))
      simpa [mul_assoc] using this
    have hI3nn : 0 ≤ I3 := hsI.nonneg (fun i => (zr6_h_bounds (hxpos _)).1)
    have hI3le : I3 ≤ 2 * (Real.sqrt X * β) * (1 - β)⁻¹ :=
      hasSum_le (fun i => by
        have h2 := (zr6_h_bounds (hxpos (i + 1 + k))).2.1
        have h3 := hsqt i
        linarith) hsI hgeo2
    -- head
    have hhd : ∀ j ∈ Finset.range k, |(Real.sqrt (x j) * Muon.DetEquiv.J (x j)
        + (1 / 2) * isoLambda 0 (x j)) - (1 / 2) * Real.sqrt (2 * Real.pi)| ≤ 2 * β / Real.sqrt X := by
      intro j hj
      refine (zr6_h_bounds (hxpos j)).2.2.trans ?_
      have hs1 : 0 < Real.sqrt (x j) := Real.sqrt_pos.2 (hxpos j)
      have hle : Real.sqrt X ≤ β * Real.sqrt (x j) := by
        have := Real.sqrt_le_sqrt (hhead j (Finset.mem_range.1 hj))
        rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hβ0.le] at this
      rw [div_le_div_iff₀ hs1 hsX]
      nlinarith
    have hH1b : |H1 - k * ((1 / 2) * Real.sqrt (2 * Real.pi))| ≤ k * (2 * β / Real.sqrt X) := by
      have e : H1 - k * ((1 / 2) * Real.sqrt (2 * Real.pi)) = ∑ j ∈ Finset.range k,
          ((Real.sqrt (x j) * Muon.DetEquiv.J (x j) + (1 / 2) * isoLambda 0 (x j))
            - (1 / 2) * Real.sqrt (2 * Real.pi)) := by
        rw [Finset.sum_sub_distrib, hH1]; simp
      rw [e]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ j ∈ Finset.range k, 2 * β / Real.sqrt X := Finset.sum_le_sum hhd
        _ = _ := by simp
    have e2 : I - ((k:ℝ) / 2 * Real.sqrt (2 * Real.pi) + hX0)
        = (H1 - k * ((1 / 2) * Real.sqrt (2 * Real.pi))) + I3 := by
      rw [hI3]; ring
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg hI3nn]
    have e3 : 2 * (Real.sqrt X * β) * (1 - β)⁻¹ = 2 * Real.sqrt X * β / (1 - β) := by
      rw [div_eq_mul_inv]; ring
    have e4 : (k:ℝ) * (2 * β / Real.sqrt X) = 2 * k * β / Real.sqrt X := by ring
    linarith

private lemma zr6_I0 {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < isoQlevel 0 t ∧ isoPhi (isoQlevel 0 t) = t ∧
    isoIlevel 0 t = Real.sqrt (isoQlevel 0 t) * Muon.DetEquiv.J (isoQlevel 0 t)
      + (1 / 2) * isoLambda 0 (isoQlevel 0 t) := by
  have hex := zr2_surj (β := 0) (H := t) (le_refl 0) zero_lt_one ht0.le (Or.inr ⟨rfl, ht1⟩)
  have hspec : 0 ≤ isoQlevel 0 t ∧ rW (Muon.emaW 0) (isoQlevel 0 t) = t := by
    unfold isoQlevel
    rw [dif_pos hex]
    exact hex.choose_spec
  have hr := ((lem_app_iso_weights_i (le_refl (0:ℝ)) zero_lt_one).2.2.2 rfl).1 _ hspec.1
  rw [hr] at hspec
  have hpos : 0 < isoQlevel 0 t := by
    rcases hspec.1.eq_or_lt with h | h
    · exfalso
      have h2 := hspec.2
      rw [← h, zr6_phi_zero] at h2
      linarith
    · exact h
  refine ⟨hpos, hspec.2, ?_⟩
  unfold isoIlevel isoLambdaB
  rw [zr_Lw_zero, if_neg (by rintro ⟨-, h⟩; exact ht1.ne h)]

private lemma zr6_h_contAt {L : ℝ} (hL : 0 < L) :
    ContinuousAt (fun y : ℝ => Real.sqrt y * Muon.DetEquiv.J y + (1 / 2) * isoLambda 0 y) L := by
  have h1 : ContinuousAt (fun y : ℝ => Real.sqrt y) L := Real.continuous_sqrt.continuousAt
  have h2 : ContinuousAt (isoLambda 0) L :=
    (zr2_lam_cont (le_refl (0:ℝ)) zero_lt_one).continuousAt (Ici_mem_nhds hL)
  exact (h1.mul (zr6_J_contAt hL)).add (continuousAt_const.mul h2)

private lemma zr6_T_atTop {t : ℝ} (ht0 : 0 < t) :
    Tendsto (fun β : ℝ => (1 - β ^ 2) * t / β ^ 2) (𝓝[>] (0:ℝ)) atTop := by
  have h1 : Tendsto (fun β : ℝ => β⁻¹) (𝓝[>] (0:ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun β : ℝ => (β⁻¹) ^ 2) (𝓝[>] (0:ℝ)) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp h1
  have h3 := tendsto_atTop_add_const_right (𝓝[>] (0:ℝ)) (-t) (h2.const_mul_atTop ht0)
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have : β ≠ 0 := (Set.mem_Ioi.1 hβ).ne'
  field_simp
  ring

private lemma zr6_ptwise (k : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Tendsto (fun β : ℝ => isoIlevel β ((k : ℝ) + t)) (𝓝[>] (0:ℝ))
      (𝓝 ((k : ℝ) / 2 * Real.sqrt (2 * Real.pi) + isoIlevel 0 t)) := by
  obtain ⟨hL0, hLΦ, hI0⟩ := zr6_I0 ht0 ht1
  set L := isoQlevel 0 t with hLdef
  have hev : ∀ᶠ β in 𝓝[>] (0:ℝ), β ∈ Ioo (0:ℝ) (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨Xf, hXf⟩ : ∃ Xf : ℝ → ℝ, ∀ β, Xf β = Muon.emaW β k ^ 2 * isoQlevel β ((k : ℝ) + t) :=
    ⟨_, fun β => rfl⟩
  have hsingle : ∀ β ∈ Ioo (0:ℝ) (1 / 2),
      (1 - β ^ 2) * t ≤ Xf β ∧
      isoPhi (Xf β) ≤ ((k:ℝ) + t) - k * isoPhi (Xf β / β ^ 2) ∧
      ((k:ℝ) + t) - k - Xf β * β ^ 2 / (1 - β ^ 2) ≤ isoPhi (Xf β) ∧
      ((k:ℝ) + 1) * isoPhi (Xf β) ≤ (k:ℝ) + t ∧
      0 < Xf β ∧
      |isoIlevel β ((k:ℝ) + t) - ((k:ℝ) / 2 * Real.sqrt (2 * Real.pi)
        + (Real.sqrt (Xf β) * Muon.DetEquiv.J (Xf β) + (1 / 2) * isoLambda 0 (Xf β)))|
        ≤ 2 * k * β / Real.sqrt (Xf β) + 2 * Real.sqrt (Xf β) * β / (1 - β) :=
    fun β hβ => zr6_single (by linarith [hβ.1]) (by linarith [hβ.2]) k ht0 rfl (hXf β)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ≥ M, ((k:ℝ) + t) / ((k:ℝ) + 1) < isoPhi x := by
    have hs : ((k:ℝ) + t) / ((k:ℝ) + 1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    exact eventually_atTop.1 (lem_app_iso_gaussian_iv.2.eventually (lt_mem_nhds hs))
  have hXM : ∀ β ∈ Ioo (0:ℝ) (1 / 2), Xf β < M := by
    intro β hβ
    by_contra hc
    push_neg at hc
    have h1 := hM _ hc
    have h2 := (hsingle β hβ).2.2.2.1
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith
  -- Phi (X) -> t
  have hPT : Tendsto (fun β : ℝ => isoPhi ((1 - β ^ 2) * t / β ^ 2)) (𝓝[>] (0:ℝ)) (𝓝 1) :=
    lem_app_iso_gaussian_iv.2.comp (zr6_T_atTop ht0)
  have hup : Tendsto (fun β : ℝ => ((k:ℝ) + t) - k * isoPhi ((1 - β ^ 2) * t / β ^ 2))
      (𝓝[>] (0:ℝ)) (𝓝 t) := by
    have := (tendsto_const_nhds (x := (k:ℝ) + t)).sub (hPT.const_mul (k:ℝ))
    convert this using 2
    ring
  have hlo : Tendsto (fun β : ℝ => t - M * β ^ 2 / (1 - β ^ 2)) (𝓝[>] (0:ℝ)) (𝓝 t) := by
    have hc : ContinuousAt (fun β : ℝ => t - M * β ^ 2 / (1 - β ^ 2)) 0 := by
      apply ContinuousAt.sub continuousAt_const
      exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
    have := hc.tendsto
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
      zero_div, sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hPX : Tendsto (fun β : ℝ => isoPhi (Xf β)) (𝓝[>] (0:ℝ)) (𝓝 t) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
    · filter_upwards [hev] with β hβ
      have h1 := (hsingle β hβ).2.2.1
      have h2 := hXM β hβ
      have hb : 0 < β := hβ.1
      have hb2 : β ^ 2 < 1 := by nlinarith [hβ.2]
      have h3 : Xf β * β ^ 2 / (1 - β ^ 2) ≤ M * β ^ 2 / (1 - β ^ 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2.le (by positivity))
          (by linarith)
      linarith
    · filter_upwards [hev] with β hβ
      have h1 := (hsingle β hβ).2.1
      have hb : 0 < β := hβ.1
      have hb2 : β ^ 2 < 1 := by nlinarith [hβ.2]
      have hT : (1 - β ^ 2) * t / β ^ 2 ≤ Xf β / β ^ 2 :=
        div_le_div_of_nonneg_right (hsingle β hβ).1 (by positivity)
      have hT0 : 0 ≤ (1 - β ^ 2) * t / β ^ 2 := by
        apply div_nonneg _ (by positivity)
        exact mul_nonneg (by linarith) ht0.le
      have := zr6_phi_mono (Set.mem_Ici.2 hT0)
        (Set.mem_Ici.2 (le_trans hT0 hT)) hT
      have hk : (0:ℝ) ≤ k := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hk]
  have hXL : Tendsto Xf (𝓝[>] (0:ℝ)) (𝓝 L) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      rcases le_or_gt a 0 with ha0 | ha0
      · filter_upwards [hev] with β hβ
        exact lt_of_le_of_lt ha0 (hsingle β hβ).2.2.2.2.1
      · have hlt : isoPhi a < t := lt_of_lt_of_eq (zr6_phi_strict ha0 ha) hLΦ
        filter_upwards [hev, (tendsto_order.1 hPX).1 _ hlt] with β hβ hb
        by_contra hc
        push_neg at hc
        have := zr6_phi_mono (Set.mem_Ici.2 (hsingle β hβ).2.2.2.2.1.le)
          (Set.mem_Ici.2 ha0.le) hc
        linarith
    · intro b hb
      have hbpos : 0 < b := lt_trans hL0 hb
      have hlt : t < isoPhi b := lt_of_eq_of_lt hLΦ.symm (zr6_phi_strict hL0 hb)
      filter_upwards [hev, (tendsto_order.1 hPX).2 _ hlt] with β hβ h
      by_contra hc
      push_neg at hc
      have := zr6_phi_mono (Set.mem_Ici.2 hbpos.le)
        (Set.mem_Ici.2 (hsingle β hβ).2.2.2.2.1.le) hc
      linarith
  -- the I sum
  have hT : Tendsto (fun β : ℝ => (k:ℝ) / 2 * Real.sqrt (2 * Real.pi)
      + (Real.sqrt (Xf β) * Muon.DetEquiv.J (Xf β) + (1 / 2) * isoLambda 0 (Xf β)))
      (𝓝[>] (0:ℝ)) (𝓝 ((k:ℝ) / 2 * Real.sqrt (2 * Real.pi)
        + (Real.sqrt L * Muon.DetEquiv.J L + (1 / 2) * isoLambda 0 L))) :=
    tendsto_const_nhds.add ((zr6_h_contAt hL0).tendsto.comp hXL)
  have ha : 0 < Real.sqrt ((3 / 4) * t) := Real.sqrt_pos.2 (by positivity)
  have hMpos : 0 < M := by
    obtain ⟨β, hβ⟩ := (hev.and self_mem_nhdsWithin).exists
    exact lt_trans (hsingle β hβ.1).2.2.2.2.1 (hXM β hβ.1)
  set C := 2 * k / Real.sqrt ((3 / 4) * t) + 4 * Real.sqrt M with hC
  have hE : Tendsto (fun β : ℝ => isoIlevel β ((k:ℝ) + t) - ((k:ℝ) / 2 * Real.sqrt (2 * Real.pi)
      + (Real.sqrt (Xf β) * Muon.DetEquiv.J (Xf β) + (1 / 2) * isoLambda 0 (Xf β))))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hCb : Tendsto (fun β : ℝ => C * β) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have : Tendsto (fun β : ℝ => C * β) (𝓝 0) (𝓝 (C * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hCb
    filter_upwards [hev] with β hβ
    obtain ⟨h1, -, -, -, h5, h6⟩ := hsingle β hβ
    rw [Real.norm_eq_abs]
    refine h6.trans ?_
    have hb : 0 < β := hβ.1
    have hb2 : β < 1 / 2 := hβ.2
    have hβ2 : β ^ 2 ≤ 1 / 4 := by nlinarith
    have hX34 : (3 / 4) * t ≤ Xf β := by nlinarith [mul_le_mul_of_nonneg_right hβ2 ht0.le]
    have hsa : Real.sqrt ((3 / 4) * t) ≤ Real.sqrt (Xf β) := Real.sqrt_le_sqrt hX34
    have hsM : Real.sqrt (Xf β) ≤ Real.sqrt M := Real.sqrt_le_sqrt (hXM β hβ).le
    have hk : (0:ℝ) ≤ k := by positivity
    have t1 : 2 * k * β / Real.sqrt (Xf β) ≤ 2 * k * β / Real.sqrt ((3 / 4) * t) :=
      div_le_div_of_nonneg_left (by positivity) ha hsa
    have t2 : 2 * Real.sqrt (Xf β) * β / (1 - β) ≤ 2 * Real.sqrt (Xf β) * β / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    have t3 : 2 * Real.sqrt (Xf β) * β / (1 / 2) ≤ 4 * Real.sqrt M * β := by
      rw [div_div_eq_mul_div]
      nlinarith [Real.sqrt_nonneg (Xf β)]
    have t4 : 2 * k * β / Real.sqrt ((3 / 4) * t) = 2 * k / Real.sqrt ((3 / 4) * t) * β := by
      ring
    rw [hC]
    nlinarith
  have := hE.add hT
  rw [hI0]
  convert this using 2
  · ring
  · simp

private lemma zr6_int_eq {γ H : ℝ} (hH0 : 0 ≤ H) (hH : H ≤ γ) (f : ℝ → ℝ) :
    ∫ m in (0:ℝ)..H, -deriv (isoWm γ γ) m * f m = ∫ m in (0:ℝ)..H, f m := by
  apply intervalIntegral.integral_congr_ae
  have h1 : ∀ᵐ m ∂(volume : Measure ℝ), m ≠ H := by
    rw [ae_iff]; simp
  filter_upwards [h1] with m hm1 hmI
  rw [Set.uIoc_of_le hH0] at hmI
  have hm : m < γ := lt_of_lt_of_le (lt_of_le_of_ne hmI.2 hm1) hH
  simp only [zr4_deriv hm]
  ring

/-- Integrability of `𝗂_β` on `(0, γ]`. -/
private lemma zr6_intg {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) :
    IntegrableOn (isoIlevel β) (Ioc 0 γ) := by
  have h := zr3_intf (γin := γ) (γout := γ) hβ0 hβ1 hγ (by rw [min_self])
  refine h.congr_fun_ae ?_
  have h1 : ∀ᵐ m ∂(volume.restrict (Ioc (0:ℝ) γ)), m ≠ γ :=
    ae_restrict_of_ae (by rw [ae_iff]; simp)
  filter_upwards [ae_restrict_mem measurableSet_Ioc, h1] with m hm hne
  have hlt : m < γ := lt_of_le_of_ne hm.2 hne
  simp only [zr4_deriv hlt]
  ring

/-- Pointwise bounds on `𝗂_β` for `β ≤ 1/2`. -/
private lemma zr6_bound {β γ m : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 2) (hm : 0 < m) (hmγ : m ≤ γ) :
    0 ≤ isoIlevel β m ∧
    isoIlevel β m ≤ 4 + (1 / 2) * (Real.sqrt (2 * Real.pi) * γ + 4 * Real.pi) := by
  have hβ1' : β < 1 := by linarith
  obtain ⟨p1, p2, p3, p4⟩ := zr3_i_pt (γin := 1) (γout := 1) hβ0 hβ1' hm
  have hg := (lem_app_iso_constants_ii hβ0 hβ1').2
  have hg' := (lem_app_iso_constants_iii hβ0 hβ1').2
  have hlt : 2 / (1 - β) ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hlt' : 2 * Real.pi / (1 - β) ≤ 4 * Real.pi := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [Real.pi_pos]
  have hQ := zr2_Qlevel_nonneg β m
  have hLam : 0 ≤ isoLambdaB β m := by
    unfold isoLambdaB
    rw [if_neg (by rintro ⟨h, -⟩; exact hβ0.ne' h)]
    exact zr2_lam_nonneg hβ0.le hβ1' hQ
  have hs : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  rw [p4]
  have h3 := (abs_le.1 p3).2
  constructor
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hmγ hs]

/-- Generic dominated convergence on `(0, a]`. -/
private lemma zr6_dct {a B : ℝ} {F : ℝ → ℝ → ℝ} {f : ℝ → ℝ}
    (hmeas : ∀ᶠ β in 𝓝[>] (0:ℝ), AEStronglyMeasurable (F β) (volume.restrict (Ioc 0 a)))
    (hB : ∀ᶠ β in 𝓝[>] (0:ℝ), ∀ t ∈ Ioc 0 a, ‖F β t‖ ≤ B)
    (hlim : ∀ t ∈ Ioo 0 a, Tendsto (fun β => F β t) (𝓝[>] (0:ℝ)) (𝓝 (f t))) :
    Tendsto (fun β => ∫ t in Ioc 0 a, F β t) (𝓝[>] (0:ℝ)) (𝓝 (∫ t in Ioc 0 a, f t)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) hmeas ?_
    (integrable_const B) ?_
  · filter_upwards [hB] with β hβ
    exact ae_restrict_of_forall_mem measurableSet_Ioc hβ
  · have h1 : ∀ᵐ t ∂(volume.restrict (Ioc (0:ℝ) a)), t ≠ a :=
      ae_restrict_of_ae (by rw [ae_iff]; simp)
    filter_upwards [ae_restrict_mem measurableSet_Ioc, h1] with t ht hne
    exact hlim t ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩

private lemma zr6_piece (k : ℕ) {a γ : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hkγ : (k:ℝ) + a ≤ γ) :
    Tendsto (fun β : ℝ => ∫ t in Ioc 0 a, isoIlevel β ((k:ℝ) + t)) (𝓝[>] (0:ℝ))
      (𝓝 ((k:ℝ) / 2 * Real.sqrt (2 * Real.pi) * a + ∫ t in Ioc 0 a, isoIlevel 0 t)) := by
  have hk0 : (0:ℝ) ≤ k := by positivity
  have hγ : 0 < γ := by linarith
  have haγ : a ≤ γ := by linarith
  have hev : ∀ᶠ β in 𝓝[>] (0:ℝ), β ∈ Ioo (0:ℝ) (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  have hint0 : ∀ β ∈ Ioo (0:ℝ) (1 / 2), IntegrableOn (fun t => isoIlevel β t) (Ioc 0 a) :=
    fun β hβ => (zr6_intg hβ.1 (by linarith [hβ.2]) hγ).mono_set (Ioc_subset_Ioc_right haγ)
  have hintk : ∀ β ∈ Ioo (0:ℝ) (1 / 2),
      IntegrableOn (fun t => isoIlevel β ((k:ℝ) + t)) (Ioc 0 a) := by
    intro β hβ
    have h1 : IntegrableOn (isoIlevel β) (Ioc 0 ((k:ℝ) + a)) :=
      (zr6_intg hβ.1 (by linarith [hβ.2]) hγ).mono_set (Ioc_subset_Ioc_right hkγ)
    have h2 : IntervalIntegrable (isoIlevel β) volume 0 ((k:ℝ) + a) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).2 h1
    have h3 : IntervalIntegrable (isoIlevel β) volume (k:ℝ) ((k:ℝ) + a) := by
      refine h2.mono_set ?_
      rw [Set.uIcc_of_le (by linarith : (k:ℝ) ≤ k + a), Set.uIcc_of_le (by linarith : (0:ℝ) ≤ k + a)]
      exact Icc_subset_Icc hk0 le_rfl
    have h4 := h3.comp_add_left (k:ℝ)
    simp only [sub_self, add_sub_cancel_left] at h4
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha0.le).1 h4
  set B := 4 + (1 / 2) * (Real.sqrt (2 * Real.pi) * γ + 4 * Real.pi) with hB
  -- DCT 1: k = 0
  have hD1 : Tendsto (fun β : ℝ => ∫ t in Ioc 0 a, isoIlevel β t) (𝓝[>] (0:ℝ))
      (𝓝 (∫ t in Ioc 0 a, isoIlevel 0 t)) := by
    refine zr6_dct (B := B) ?_ ?_ ?_
    · filter_upwards [hev] with β hβ
      exact (hint0 β hβ).aestronglyMeasurable
    · filter_upwards [hev] with β hβ t ht
      have := zr6_bound (γ := γ) hβ.1 hβ.2.le ht.1 (ht.2.trans haγ)
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]
      exact this.2
    · intro t ht
      have h := zr6_ptwise 0 ht.1 (lt_of_lt_of_le ht.2 ha1)
      simpa using h
  -- DCT 2: the difference
  have hD2 : Tendsto (fun β : ℝ => ∫ t in Ioc 0 a, (isoIlevel β ((k:ℝ) + t) - isoIlevel β t))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ t in Ioc 0 a, ((k:ℝ) / 2 * Real.sqrt (2 * Real.pi)))) := by
    refine zr6_dct (B := B) ?_ ?_ ?_
    · filter_upwards [hev] with β hβ
      exact ((hintk β hβ).sub (hint0 β hβ)).aestronglyMeasurable
    · filter_upwards [hev] with β hβ t ht
      have h1 := zr6_bound (γ := γ) hβ.1 hβ.2.le ht.1 (ht.2.trans haγ)
      have h2 := zr6_bound (γ := γ) hβ.1 hβ.2.le (show 0 < (k:ℝ) + t by linarith [ht.1])
        (by linarith [ht.2])
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · intro t ht
      have h1 := zr6_ptwise k ht.1 (lt_of_lt_of_le ht.2 ha1)
      have h2 := zr6_ptwise 0 ht.1 (lt_of_lt_of_le ht.2 ha1)
      have h3 := h1.sub (by simpa using h2)
      convert h3 using 2
      ring
  have hsum := hD2.add hD1
  have hconst : ∫ t in Ioc 0 a, ((k:ℝ) / 2 * Real.sqrt (2 * Real.pi))
      = (k:ℝ) / 2 * Real.sqrt (2 * Real.pi) * a := by
    rw [setIntegral_const]
    simp [Measure.real, Real.volume_Ioc, ha0.le]
    ring
  rw [hconst] at hsum
  refine hsum.congr' ?_
  filter_upwards [hev] with β hβ
  rw [integral_sub (hintk β hβ) (hint0 β hβ)]
  ring

private lemma zr6_rep {β γ : ℝ} (hβ : (0 < β ∧ β < 1) ∨ (β = 0 ∧ γ < 1)) (hγ : 0 < γ) :
    Cbeta β γ γ = Real.sqrt 2 / (Real.pi * γ * γ) * ∫ m in (0:ℝ)..γ, isoIlevel β m := by
  have hmin : min γ γ = γ := min_self γ
  have hML : isoMLevel β γ γ 0 = γ := by
    unfold isoMLevel
    rw [if_pos rfl, hmin]
    split_ifs with h
    · exfalso
      rcases hβ with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1.ne' h.1
      · linarith [h.2]
    · rfl
  have hβ' : (0 < β ∧ β < 1) ∨ (β = 0 ∧ min γ γ < 1) := by rwa [hmin]
  have h := (lem_app_iso_participation_i (β := β) (γin := γ) (γout := γ) (ϱ := 0) hβ' hγ hγ
    le_rfl).2.2 rfl
  rw [hML] at h
  simp only [zero_add] at h
  unfold isoIt at h
  rw [zr6_int_eq hγ.le le_rfl, zr4_W_sq le_rfl] at h
  simp only [sub_self, mul_zero, zero_mul, add_zero] at h
  unfold Cbeta
  rw [← h]

private lemma zr6_ii {β γ a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ γ) : IntervalIntegrable (isoIlevel β) volume a b := by
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 ?_
  exact (zr6_intg hβ0 hβ1 hγ).mono_set (Ioc_subset_Ioc ha hb)

private lemma zr6_shift {β : ℝ} (k : ℝ) (a : ℝ) (ha : 0 ≤ a) :
    ∫ m in k..(k + a), isoIlevel β m = ∫ t in Ioc 0 a, isoIlevel β (k + t) := by
  have := intervalIntegral.integral_comp_add_left (f := isoIlevel β) (a := 0) (b := a) k
  rw [add_zero] at this
  rw [← this, intervalIntegral.integral_of_le ha]

private lemma zr6_decomp {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (n : ℕ)
    (hn : (n : ℝ) ≤ γ) :
    ∫ m in (0:ℝ)..γ, isoIlevel β m = (∑ k ∈ Finset.range n, ∫ t in Ioc (0:ℝ) 1,
        isoIlevel β ((k:ℝ) + t)) + ∫ t in Ioc (0:ℝ) (γ - n), isoIlevel β ((n:ℝ) + t) := by
  have hint : ∀ k < n, IntervalIntegrable (isoIlevel β) volume ((fun j : ℕ => (j:ℝ)) k)
      ((fun j : ℕ => (j:ℝ)) (k + 1)) := by
    intro k hk
    have hk1 : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk
    exact zr6_ii hβ0 hβ1 hγ (by positivity) (by push_cast; linarith) (by push_cast at hk1 ⊢; linarith)
  have h1 := intervalIntegral.sum_integral_adjacent_intervals (f := isoIlevel β) (μ := volume)
    (a := fun j : ℕ => (j:ℝ)) hint
  simp only [Nat.cast_zero] at h1
  have h2 : IntervalIntegrable (isoIlevel β) volume 0 (n:ℝ) :=
    zr6_ii hβ0 hβ1 hγ le_rfl (by positivity) hn
  have h3 : IntervalIntegrable (isoIlevel β) volume (n:ℝ) γ :=
    zr6_ii hβ0 hβ1 hγ (by positivity) hn le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals h2 h3, ← h1]
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    have := zr6_shift (β := β) (k : ℝ) 1 zero_le_one
    simp only [Nat.cast_add, Nat.cast_one]
    rw [this]
  · have := zr6_shift (β := β) (n : ℝ) (γ - n) (by linarith)
    rw [add_sub_cancel] at this
    rw [this]

private lemma zr6_lim {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun β : ℝ => Cbeta β γ γ) (𝓝[>] (0:ℝ)) (𝓝 (Real.sqrt 2 / (Real.pi * γ * γ) *
      ((∑ k ∈ Finset.range ⌊γ⌋₊, ((k:ℝ) / 2 * Real.sqrt (2 * Real.pi) * 1
          + ∫ t in Ioc (0:ℝ) 1, isoIlevel 0 t))
        + (((⌊γ⌋₊ : ℕ) : ℝ) / 2 * Real.sqrt (2 * Real.pi) * (γ - ((⌊γ⌋₊ : ℕ) : ℝ))
          + ∫ t in Ioc (0:ℝ) (γ - ((⌊γ⌋₊ : ℕ) : ℝ)), isoIlevel 0 t)))) := by
  obtain ⟨n, hnd⟩ : ∃ n : ℕ, n = ⌊γ⌋₊ := ⟨_, rfl⟩
  rw [← hnd]
  have hn : (n:ℝ) ≤ γ := by rw [hnd]; exact Nat.floor_le hγ.le
  have hn1 : γ < n + 1 := by rw [hnd]; exact Nat.lt_floor_add_one γ
  have hev : ∀ᶠ β in 𝓝[>] (0:ℝ), β ∈ Ioo (0:ℝ) (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  have hsum := tendsto_finset_sum (Finset.range n) (fun k hk => zr6_piece k (a := 1) (γ := γ)
    one_pos le_rfl (by
      have : k + 1 ≤ n := Finset.mem_range.1 hk
      have h2 : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
      push_cast at h2
      linarith))
  have hlast : Tendsto (fun β : ℝ => ∫ t in Ioc (0:ℝ) (γ - n), isoIlevel β ((n:ℝ) + t))
      (𝓝[>] (0:ℝ)) (𝓝 ((n:ℝ) / 2 * Real.sqrt (2 * Real.pi) * (γ - n)
        + ∫ t in Ioc (0:ℝ) (γ - n), isoIlevel 0 t)) := by
    rcases (sub_nonneg.2 hn).eq_or_lt with h0 | hpos
    · have h00 : γ - n = 0 := h0.symm
      simp only [h00, Set.Ioc_self, Measure.restrict_empty, integral_zero_measure, mul_zero,
        add_zero]
      exact tendsto_const_nhds
    · exact zr6_piece n hpos (by linarith) (by linarith)
  have hlimI := hsum.add hlast
  have hlimI' : Tendsto (fun β : ℝ => ∫ m in (0:ℝ)..γ, isoIlevel β m) (𝓝[>] (0:ℝ)) _ :=
    hlimI.congr' (hev.mono fun β hβ => (zr6_decomp hβ.1 (by linarith [hβ.2]) hγ n hn).symm)
  refine (hlimI'.const_mul (Real.sqrt 2 / (Real.pi * γ * γ))).congr' ?_
  filter_upwards [hev] with β hβ
  exact (zr6_rep (Or.inl ⟨hβ.1, by linarith [hβ.2]⟩) hγ).symm

private lemma zr6_sumS (n : ℕ) (s A : ℝ) :
    ∑ k ∈ Finset.range n, ((k:ℝ) / 2 * s * 1 + A) = ((n:ℝ) * (n - 1) / 2) / 2 * s + n * A := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private lemma zr6_final {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun β : ℝ => Cbeta β γ γ) (𝓝[>] (0:ℝ)) (𝓝 (isoCsharp γ)) := by
  have hlim := zr6_lim hγ
  obtain ⟨n, hnd⟩ : ∃ n : ℕ, n = ⌊γ⌋₊ := ⟨_, rfl⟩
  rw [← hnd] at hlim
  have hn : (n:ℝ) ≤ γ := by rw [hnd]; exact Nat.floor_le hγ.le
  have hn1 : γ < n + 1 := by rw [hnd]; exact Nat.lt_floor_add_one γ
  have hNint : isoNint γ = (n:ℝ) := by unfold isoNint; rw [hnd]
  have hFrac : isoFrac γ = γ - n := by unfold isoFrac; rw [hNint]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∫ t in Ioc (0:ℝ) 1, isoIlevel 0 t := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∫ t in Ioc (0:ℝ) (γ - n), isoIlevel 0 t := ⟨_, rfl⟩
  rw [← hA, ← hB] at hlim
  rw [zr6_sumS] at hlim
  have hC1 : Cbeta 0 1 1 = Real.sqrt 2 / Real.pi * A := by
    have h := zr4_Cbeta_formula (le_refl (1:ℝ))
    rw [h, hA, intervalIntegral.integral_of_le zero_le_one]
    simp
  have hY : isoY2C0 (isoFrac γ) = Real.sqrt 2 / Real.pi * B := by
    rw [hFrac]
    rcases (sub_nonneg.2 hn).eq_or_lt with h0 | hpos
    · have h00 : γ - n = 0 := h0.symm
      rw [hB, h00]
      simp [isoY2C0]
    · have hlt : γ - n < 1 := by linarith
      unfold isoY2C0
      rw [if_neg hpos.ne']
      rw [zr6_rep (Or.inr ⟨rfl, hlt⟩) hpos, hB, intervalIntegral.integral_of_le hpos.le]
      field_simp
  have hval : Real.sqrt 2 / (Real.pi * γ * γ) *
      (((n:ℝ) * (n - 1) / 2 / 2 * Real.sqrt (2 * Real.pi) + n * A)
        + ((n:ℝ) / 2 * Real.sqrt (2 * Real.pi) * (γ - n) + B)) = isoCsharp γ := by
    have hCs : isoCsharp γ = (isoNint γ * Cbeta 0 1 1 + isoY2C0 (isoFrac γ)) / γ ^ 2
        + (isoNint γ * (isoNint γ - 1) / 2 + isoNint γ * isoFrac γ) / (Real.sqrt Real.pi * γ ^ 2) :=
      rfl
    rw [hCs, hY, hNint, hFrac, hC1, zr4_sqrt2pi]
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hsp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
    have hspos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
    have hγne : γ ≠ 0 := hγ.ne'
    have hab : (Real.sqrt 2 * Real.sqrt Real.pi) * (Real.sqrt 2 * Real.sqrt Real.pi)
        = 2 * Real.pi := by
      calc _ = (Real.sqrt 2 * Real.sqrt 2) * (Real.sqrt Real.pi * Real.sqrt Real.pi) := by ring
        _ = 2 * Real.pi := by rw [hs2, hsp]
    field_simp
    linear_combination ((n:ℝ) * (n - 1) + 2 * n * (γ - n)) * hab
  rw [hval] at hlim
  exact hlim

/-- `prop:app-iso-beta-zero`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.3682–3693):
```latex
\begin{proposition}[Zero ridge as the momentum vanishes]\label{prop:app-iso-beta-zero}
In the square case write $\gamma=n+y$ with an integer $n\ge0$ and $y\in[0,1)$, and put
$y^2C_0(y)\defeq0$ at $y=0$. Then
\[
\lim_{\bmom\downarrow0}C_\bmom(\gamma)=C^\sharp(\gamma)\defeq\frac{n\,C_0(1)+y^2C_0(y)}{\gamma^2}+\frac{n(n-1)/2+ny}{\sqrt\pi\,\gamma^2}.
\]
In particular $C^\sharp(\gamma)=C_0(\gamma)$ for $\gamma\le1$, while for $\gamma\ge1$
\[
\gamma^2\big(C^\sharp(\gamma)-C_0(\gamma)\big)=(n-1)\,C_0(1)+y^2C_0(y)+\frac{(n-1)(n-2)/2+(n-1)y}{\sqrt\pi},
\]
which is strictly positive for every $\gamma>1$. Finally $C^\sharp(\gamma)\to1/(2\sqrt\pi)$ as $\gamma\to\infty$.
\end{proposition}
```

Part (i): the limit `β ↓ 0` of the square-case zero-ridge constant equals `C^♯(γ)`
(`isoCsharp`). -/
theorem prop_app_iso_beta_zero_i {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun β : ℝ => Cbeta β γ γ) (𝓝[>] (0 : ℝ)) (𝓝 (isoCsharp γ)) := by
  exact zr6_final hγ

/-- `prop:app-iso-beta-zero`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.3682–3693):
```latex
\begin{proposition}[Zero ridge as the momentum vanishes]\label{prop:app-iso-beta-zero}
In the square case write $\gamma=n+y$ with an integer $n\ge0$ and $y\in[0,1)$, and put
$y^2C_0(y)\defeq0$ at $y=0$. Then
\[
\lim_{\bmom\downarrow0}C_\bmom(\gamma)=C^\sharp(\gamma)\defeq\frac{n\,C_0(1)+y^2C_0(y)}{\gamma^2}+\frac{n(n-1)/2+ny}{\sqrt\pi\,\gamma^2}.
\]
In particular $C^\sharp(\gamma)=C_0(\gamma)$ for $\gamma\le1$, while for $\gamma\ge1$
\[
\gamma^2\big(C^\sharp(\gamma)-C_0(\gamma)\big)=(n-1)\,C_0(1)+y^2C_0(y)+\frac{(n-1)(n-2)/2+(n-1)y}{\sqrt\pi},
\]
which is strictly positive for every $\gamma>1$. Finally $C^\sharp(\gamma)\to1/(2\sqrt\pi)$ as $\gamma\to\infty$.
\end{proposition}
```

Part (ii): "In particular `C^♯(γ) = C_0(γ)` for `γ ≤ 1`". -/
theorem prop_app_iso_beta_zero_ii {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    isoCsharp γ = Cbeta 0 γ γ := by
  rcases lt_or_eq_of_le hγ1 with hlt | heq
  · have hn : isoNint γ = 0 := zr4_isoNint_small hlt
    have hf : isoFrac γ = γ := by unfold isoFrac; rw [hn]; ring
    unfold isoCsharp
    rw [hn, hf]
    unfold isoY2C0
    rw [if_neg hγ.ne']
    have hg : γ ≠ 0 := hγ.ne'
    field_simp
    ring
  · subst heq
    simp [isoCsharp, isoNint, isoFrac, isoY2C0]

/-- `prop:app-iso-beta-zero`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.3682–3693):
```latex
\begin{proposition}[Zero ridge as the momentum vanishes]\label{prop:app-iso-beta-zero}
In the square case write $\gamma=n+y$ with an integer $n\ge0$ and $y\in[0,1)$, and put
$y^2C_0(y)\defeq0$ at $y=0$. Then
\[
\lim_{\bmom\downarrow0}C_\bmom(\gamma)=C^\sharp(\gamma)\defeq\frac{n\,C_0(1)+y^2C_0(y)}{\gamma^2}+\frac{n(n-1)/2+ny}{\sqrt\pi\,\gamma^2}.
\]
In particular $C^\sharp(\gamma)=C_0(\gamma)$ for $\gamma\le1$, while for $\gamma\ge1$
\[
\gamma^2\big(C^\sharp(\gamma)-C_0(\gamma)\big)=(n-1)\,C_0(1)+y^2C_0(y)+\frac{(n-1)(n-2)/2+(n-1)y}{\sqrt\pi},
\]
which is strictly positive for every $\gamma>1$. Finally $C^\sharp(\gamma)\to1/(2\sqrt\pi)$ as $\gamma\to\infty$.
\end{proposition}
```

Part (iii): the displayed identity for `γ ≥ 1`, and the strict positivity for `γ > 1`
(stated on `γ²(C^♯ − C_0)`, which the identity equates to the displayed right-hand side). -/
theorem prop_app_iso_beta_zero_iii {γ : ℝ} (hγ : 1 ≤ γ) :
    γ ^ 2 * (isoCsharp γ - Cbeta 0 γ γ)
        = (isoNint γ - 1) * Cbeta 0 1 1 + isoY2C0 (isoFrac γ)
          + ((isoNint γ - 1) * (isoNint γ - 2) / 2 + (isoNint γ - 1) * isoFrac γ)
            / Real.sqrt Real.pi ∧
    (1 < γ → 0 < γ ^ 2 * (isoCsharp γ - Cbeta 0 γ γ)) := by
  have hγ0 : (0:ℝ) < γ := by linarith
  have hC := prop_app_iso_exact hγ
  have hy : γ = isoNint γ + isoFrac γ := by unfold isoFrac; ring
  have hid : γ ^ 2 * (isoCsharp γ - Cbeta 0 γ γ)
      = (isoNint γ - 1) * Cbeta 0 1 1 + isoY2C0 (isoFrac γ)
          + ((isoNint γ - 1) * (isoNint γ - 2) / 2 + (isoNint γ - 1) * isoFrac γ)
            / Real.sqrt Real.pi := by
    have hCs : isoCsharp γ = (isoNint γ * Cbeta 0 1 1 + isoY2C0 (isoFrac γ)) / γ ^ 2
        + (isoNint γ * (isoNint γ - 1) / 2 + isoNint γ * isoFrac γ) / (Real.sqrt Real.pi * γ ^ 2) :=
      rfl
    rw [hCs, hC]
    exact zr4_alg γ (isoNint γ) (isoFrac γ) (Cbeta 0 1 1) (isoY2C0 (isoFrac γ))
      (Real.sqrt Real.pi) (Real.sqrt_pos.2 Real.pi_pos) hγ0 hy
  refine ⟨hid, fun h1 => ?_⟩
  rw [hid]
  have hn1 : 1 ≤ ⌊γ⌋₊ := Nat.le_floor (by exact_mod_cast hγ)
  have hC11 : 0 < Cbeta 0 1 1 := zr_Cbeta_pos (le_refl (0:ℝ)) zero_lt_one one_pos one_pos
  have hfy0 : 0 ≤ isoFrac γ := by
    have := Nat.floor_le hγ0.le
    unfold isoFrac isoNint
    linarith
  have hY : 0 ≤ isoY2C0 (isoFrac γ) := by
    unfold isoY2C0
    split_ifs with h
    · exact le_rfl
    · have hpos : 0 < isoFrac γ := lt_of_le_of_ne hfy0 (Ne.symm h)
      exact mul_nonneg (sq_nonneg _) (zr_Cbeta_pos (le_refl (0:ℝ)) zero_lt_one hpos hpos).le
  rcases (show ⌊γ⌋₊ = 1 ∨ 2 ≤ ⌊γ⌋₊ by omega) with h2 | h2
  · have hn : isoNint γ = 1 := by unfold isoNint; rw [h2]; simp
    have hf : isoFrac γ = γ - 1 := by unfold isoFrac; rw [hn]
    rw [hn, hf]
    have hpos : 0 < γ - 1 := by linarith
    have hYpos : 0 < isoY2C0 (γ - 1) := by
      unfold isoY2C0
      rw [if_neg hpos.ne']
      exact mul_pos (by positivity) (zr_Cbeta_pos (le_refl (0:ℝ)) zero_lt_one hpos hpos)
    have e : ((1:ℝ) - 1) * Cbeta 0 1 1 + isoY2C0 (γ - 1)
        + (((1:ℝ) - 1) * ((1:ℝ) - 2) / 2 + ((1:ℝ) - 1) * (γ - 1)) / Real.sqrt Real.pi
        = isoY2C0 (γ - 1) := by ring
    rw [e]
    exact hYpos
  · have hn2 : (2:ℝ) ≤ isoNint γ := by unfold isoNint; exact_mod_cast h2
    have hA : 0 < (isoNint γ - 1) * Cbeta 0 1 1 := mul_pos (by linarith) hC11
    have hB : 0 ≤ ((isoNint γ - 1) * (isoNint γ - 2) / 2 + (isoNint γ - 1) * isoFrac γ)
        / Real.sqrt Real.pi := by
      apply div_nonneg _ (Real.sqrt_nonneg _)
      have h3 : 0 ≤ (isoNint γ - 1) * (isoNint γ - 2) := mul_nonneg (by linarith) (by linarith)
      have h4 : 0 ≤ (isoNint γ - 1) * isoFrac γ := mul_nonneg (by linarith) hfy0
      linarith
    linarith

/-- Integrability of `min 1 (1/u²)` on `(0,∞)` (task P-F.3.P6). -/
private lemma zr5_g_int : IntegrableOn (fun u : ℝ => min (1:ℝ) (1 / u ^ 2)) (Ioi 0) := by
  refine zr_integrableOn_of_bound (K := 1) (c := 1) one_pos ?_ (fun u _ => ?_)
  · exact (by fun_prop : Measurable (fun u : ℝ => min (1:ℝ) (1 / u ^ 2))).aestronglyMeasurable
  · have hu : 0 ≤ min (1:ℝ) (1 / u ^ 2) := le_min zero_le_one (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hu]

/-- Uniform bound `0 ≤ y² C_0(y) ≤ √2/π ∫_0^∞ min(1, 1/u²) du` for `0 < y ≤ 1` (task P-F.3.P6). -/
private lemma zr5_Y {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    0 ≤ isoY2C0 y ∧
      isoY2C0 y ≤ Real.sqrt 2 / Real.pi * ∫ u in Ioi (0 : ℝ), min (1:ℝ) (1 / u ^ 2) := by
  have hne : y ≠ 0 := hy0.ne'
  have hpos : ∀ u : ℝ, u ∈ Ioi (0 : ℝ) → 0 < u ^ 2 := fun u hu => by
    have : (0:ℝ) < u := hu
    positivity
  have hI : isoY2C0 y = Real.sqrt 2 / Real.pi * ∫ u in Ioi (0 : ℝ), isoGb 0 y y (u ^ 2) := by
    unfold isoY2C0 Cbeta
    rw [if_neg hne, ← mul_assoc]
    congr 1
    field_simp
  have hnn : 0 ≤ ∫ u in Ioi (0 : ℝ), isoGb 0 y y (u ^ 2) :=
    setIntegral_nonneg measurableSet_Ioi (fun u hu =>
      (zr_isoGb_bounds (le_refl (0:ℝ)) zero_lt_one hy0 hy0 (hpos u hu)).1.le)
  have hmono : ∫ u in Ioi (0 : ℝ), isoGb 0 y y (u ^ 2)
      ≤ ∫ u in Ioi (0 : ℝ), min (1:ℝ) (1 / u ^ 2) := by
    refine integral_mono_of_nonneg ?_ zr5_g_int ?_
    · exact ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu =>
        (zr_isoGb_bounds (le_refl (0:ℝ)) zero_lt_one hy0 hy0 (hpos u hu)).1.le)
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => ?_)
      have hu2 := hpos u hu
      have h1 : isoGb 0 y y (u ^ 2) ≤ 1 := by
        have := zr_isoGb_le_K (le_refl (0:ℝ)) zero_lt_one hy0 hy0 hu2
        have hK : isoK 0 (min y y) = 1 := by simp [isoK]
        rwa [hK] at this
      have h2 : isoGb 0 y y (u ^ 2) ≤ 1 / u ^ 2 := by
        refine (zr_isoGb_bounds (le_refl (0:ℝ)) zero_lt_one hy0 hy0 hu2).2.trans ?_
        exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
      exact le_min h1 h2
  have hc : 0 ≤ Real.sqrt 2 / Real.pi := div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le
  refine ⟨?_, ?_⟩
  · rw [hI]; exact mul_nonneg hc hnn
  · rw [hI]; exact mul_le_mul_of_nonneg_left hmono hc

/-- Fractional part lies in `[0, 1]` for `γ ≥ 1` (task P-F.3.P6). -/
private lemma zr5_frac {γ : ℝ} (hγ : 1 ≤ γ) : 0 ≤ isoFrac γ ∧ isoFrac γ ≤ 1 := by
  have hγ0 : (0:ℝ) ≤ γ := by linarith
  have h1 := Nat.floor_le hγ0
  have h2 := Nat.lt_floor_add_one γ
  unfold isoFrac isoNint
  constructor <;> linarith

/-- `prop:app-iso-beta-zero`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.3682–3693):
```latex
\begin{proposition}[Zero ridge as the momentum vanishes]\label{prop:app-iso-beta-zero}
In the square case write $\gamma=n+y$ with an integer $n\ge0$ and $y\in[0,1)$, and put
$y^2C_0(y)\defeq0$ at $y=0$. Then
\[
\lim_{\bmom\downarrow0}C_\bmom(\gamma)=C^\sharp(\gamma)\defeq\frac{n\,C_0(1)+y^2C_0(y)}{\gamma^2}+\frac{n(n-1)/2+ny}{\sqrt\pi\,\gamma^2}.
\]
In particular $C^\sharp(\gamma)=C_0(\gamma)$ for $\gamma\le1$, while for $\gamma\ge1$
\[
\gamma^2\big(C^\sharp(\gamma)-C_0(\gamma)\big)=(n-1)\,C_0(1)+y^2C_0(y)+\frac{(n-1)(n-2)/2+(n-1)y}{\sqrt\pi},
\]
which is strictly positive for every $\gamma>1$. Finally $C^\sharp(\gamma)\to1/(2\sqrt\pi)$ as $\gamma\to\infty$.
\end{proposition}
```

Part (iv): the limit `C^♯(γ) → 1/(2√π)` as `γ → ∞`. -/
theorem prop_app_iso_beta_zero_iv :
    Tendsto isoCsharp atTop (𝓝 (1 / (2 * Real.sqrt Real.pi))) := by
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsne : Real.sqrt Real.pi ≠ 0 := hs.ne'
  have hc1 : 0 ≤ Cbeta 0 1 1 := (zr_Cbeta_pos (le_refl (0:ℝ)) zero_lt_one one_pos one_pos).le
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Real.sqrt 2 / Real.pi * ∫ u in Ioi (0 : ℝ), min (1:ℝ) (1 / u ^ 2) :=
    ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le)
      (setIntegral_nonneg measurableSet_Ioi (fun u _ => le_min zero_le_one (by positivity)))
  have hYb : ∀ γ : ℝ, 1 ≤ γ → 0 ≤ isoY2C0 (isoFrac γ) ∧ isoY2C0 (isoFrac γ) ≤ M := by
    intro γ hγ
    obtain ⟨hf0, hf1⟩ := zr5_frac hγ
    rcases hf0.eq_or_lt with h0 | hpos
    · have hY : isoY2C0 (isoFrac γ) = 0 := by unfold isoY2C0; rw [if_pos h0.symm]
      rw [hY]; exact ⟨le_rfl, hM0⟩
    · obtain ⟨h1, h2⟩ := zr5_Y hpos hf1
      rw [hM]; exact ⟨h1, h2⟩
  have hlow_up : ∀ γ : ℝ, 2 ≤ γ →
      1 / (2 * Real.sqrt Real.pi) * ((1 - γ⁻¹) * (1 - 2 * γ⁻¹)) ≤ isoCsharp γ ∧
      isoCsharp γ ≤ 1 / (2 * Real.sqrt Real.pi) + (1 / Real.sqrt Real.pi + Cbeta 0 1 1) * γ⁻¹
        + M * γ⁻¹ * γ⁻¹ := by
    intro γ hγ
    have hγ0 : 0 < γ := by linarith
    have hγne : γ ≠ 0 := hγ0.ne'
    have hnγ : isoNint γ ≤ γ := Nat.floor_le hγ0.le
    have hnγ' : γ - 1 < isoNint γ := by
      unfold isoNint; linarith [Nat.lt_floor_add_one γ]
    have hn0 : 0 ≤ isoNint γ := by unfold isoNint; positivity
    obtain ⟨hy0, hy1⟩ := zr5_frac (show (1:ℝ) ≤ γ by linarith)
    have hY := hYb γ (by linarith)
    have hform : isoCsharp γ = (isoNint γ * Cbeta 0 1 1 + isoY2C0 (isoFrac γ)) / γ ^ 2
        + (isoNint γ * (isoNint γ - 1) / 2 + isoNint γ * isoFrac γ)
          / (Real.sqrt Real.pi * γ ^ 2) := rfl
    rw [hform]
    have h_nn : isoNint γ * isoNint γ ≤ γ * γ := mul_le_mul hnγ hnγ hn0 hγ0.le
    have h_ny : isoNint γ * isoFrac γ ≤ isoNint γ := mul_le_of_le_one_right hn0 hy1
    have h_ny0 : 0 ≤ isoNint γ * isoFrac γ := mul_nonneg hn0 hy0
    have h_low : (γ - 1) * (γ - 2) ≤ isoNint γ * (isoNint γ - 1) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) hn0
    have hAup : isoNint γ * Cbeta 0 1 1 + isoY2C0 (isoFrac γ) ≤ γ * Cbeta 0 1 1 + M := by
      have := mul_le_mul_of_nonneg_right hnγ hc1
      linarith [hY.2]
    have hPnn : 0 ≤ (isoNint γ * Cbeta 0 1 1 + isoY2C0 (isoFrac γ)) / γ ^ 2 :=
      div_nonneg (add_nonneg (mul_nonneg hn0 hc1) hY.1) (by positivity)
    have hP : (isoNint γ * Cbeta 0 1 1 + isoY2C0 (isoFrac γ)) / γ ^ 2
        ≤ (γ * Cbeta 0 1 1 + M) / γ ^ 2 :=
      div_le_div_of_nonneg_right hAup (by positivity)
    have hQlo : (γ - 1) * (γ - 2) / 2 / (Real.sqrt Real.pi * γ ^ 2)
        ≤ (isoNint γ * (isoNint γ - 1) / 2 + isoNint γ * isoFrac γ)
          / (Real.sqrt Real.pi * γ ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hQup : (isoNint γ * (isoNint γ - 1) / 2 + isoNint γ * isoFrac γ)
          / (Real.sqrt Real.pi * γ ^ 2)
        ≤ (γ * γ / 2 + γ) / (Real.sqrt Real.pi * γ ^ 2) :=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    have eL : 1 / (2 * Real.sqrt Real.pi) * ((1 - γ⁻¹) * (1 - 2 * γ⁻¹))
        = (γ - 1) * (γ - 2) / 2 / (Real.sqrt Real.pi * γ ^ 2) := by
      field_simp
    have eP : (γ * Cbeta 0 1 1 + M) / γ ^ 2 = Cbeta 0 1 1 * γ⁻¹ + M * γ⁻¹ * γ⁻¹ := by
      field_simp
    have eQ : (γ * γ / 2 + γ) / (Real.sqrt Real.pi * γ ^ 2)
        = 1 / (2 * Real.sqrt Real.pi) + (1 / Real.sqrt Real.pi) * γ⁻¹ := by
      field_simp
    constructor
    · linarith
    · linarith
  have hinv : Tendsto (fun γ : ℝ => γ⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hL : Tendsto (fun γ : ℝ => 1 / (2 * Real.sqrt Real.pi) * ((1 - γ⁻¹) * (1 - 2 * γ⁻¹)))
      atTop (𝓝 (1 / (2 * Real.sqrt Real.pi) * ((1 - 0) * (1 - 2 * 0)))) :=
    (((tendsto_const_nhds (x := (1:ℝ))).sub hinv).mul
      ((tendsto_const_nhds (x := (1:ℝ))).sub (hinv.const_mul 2))).const_mul _
  have hU : Tendsto (fun γ : ℝ => 1 / (2 * Real.sqrt Real.pi)
        + (1 / Real.sqrt Real.pi + Cbeta 0 1 1) * γ⁻¹ + M * γ⁻¹ * γ⁻¹) atTop
      (𝓝 (1 / (2 * Real.sqrt Real.pi) + (1 / Real.sqrt Real.pi + Cbeta 0 1 1) * 0
        + M * 0 * 0)) :=
    (tendsto_const_nhds.add (hinv.const_mul _)).add ((hinv.const_mul M).mul hinv)
  have hLv : 1 / (2 * Real.sqrt Real.pi) * ((1 - 0) * (1 - 2 * 0)) = 1 / (2 * Real.sqrt Real.pi) := by
    ring
  have hUv : 1 / (2 * Real.sqrt Real.pi) + (1 / Real.sqrt Real.pi + Cbeta 0 1 1) * 0 + M * 0 * 0
      = 1 / (2 * Real.sqrt Real.pi) := by
    ring
  rw [hLv] at hL
  rw [hUv] at hU
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
    (eventually_ge_atTop 2 |>.mono fun γ hγ => (hlow_up γ hγ).1)
    (eventually_ge_atTop 2 |>.mono fun γ hγ => (hlow_up γ hγ).2)

/-! ## Aspect ratio one with momentum -/

/-- `prop:app-iso-one-momentum`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.3754–3764):
```latex
\begin{proposition}[Aspect ratio one with momentum]\label{prop:app-iso-one-momentum}
Let $\bmom\in(0,1)$. Then
\[
C_\bmom(1)=\frac{\sqrt2}\pi\int_0^1\Big[\sqrt{Q_m}\,\Lw(Q_m)+\tfrac12\Lambda_\bmom(Q_m)\Big]\dif m,
\]
$C_\bmom(1)\to C_0(1)$ as $\bmom\downarrow0$, and if $1-\bmom^2\le\frac1{12}$, then
\[
C_\bmom(1)=\frac{8\vartheta}{3\pi\sqrt{2\sw2}}\qquad\text{for some}\quad
\vartheta\in\Big[1-6(1-\bmom^2),\ \big(1-6(1-\bmom^2)\big)^{-1/2}\Big].
\]
\end{proposition}
```

Part (i): the integral representation of `C_β(1)` through `𝗂_β`. -/
theorem prop_app_iso_one_momentum_i {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Cbeta β 1 1 = Real.sqrt 2 / Real.pi * ∫ m in (0 : ℝ)..1, isoIlevel β m := by
  have hp := (lem_app_iso_participation_i (γin := 1) (γout := 1) (ϱ := 0)
    (Or.inl ⟨hβ0, hβ1⟩) one_pos one_pos le_rfl).2.2 rfl
  have hM : isoMLevel β 1 1 0 = 1 := by
    simp [isoMLevel]
  rw [hM] at hp
  simp only [zero_add] at hp
  have hIt : isoIt β 1 1 1 = ∫ m in (0 : ℝ)..1, isoIlevel β m := by
    unfold isoIt
    have hW : isoWm 1 1 1 = 0 := by simp [isoWm]
    rw [hW]
    simp only [mul_zero, zero_mul, add_zero]
    apply intervalIntegral.integral_congr_ae
    have hae : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ 1 := by
      rw [ae_iff]; simp
    filter_upwards [hae] with x hx1 hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hx' : x < 1 := lt_of_le_of_ne hx.2 hx1
    simp only [zr4_deriv (γ := 1) hx', neg_neg, one_mul]
  rw [← hIt, hp]
  simp only [Cbeta, mul_one]

/-- `prop:app-iso-one-momentum`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.3754–3764):
```latex
\begin{proposition}[Aspect ratio one with momentum]\label{prop:app-iso-one-momentum}
Let $\bmom\in(0,1)$. Then
\[
C_\bmom(1)=\frac{\sqrt2}\pi\int_0^1\Big[\sqrt{Q_m}\,\Lw(Q_m)+\tfrac12\Lambda_\bmom(Q_m)\Big]\dif m,
\]
$C_\bmom(1)\to C_0(1)$ as $\bmom\downarrow0$, and if $1-\bmom^2\le\frac1{12}$, then
\[
C_\bmom(1)=\frac{8\vartheta}{3\pi\sqrt{2\sw2}}\qquad\text{for some}\quad
\vartheta\in\Big[1-6(1-\bmom^2),\ \big(1-6(1-\bmom^2)\big)^{-1/2}\Big].
\]
\end{proposition}
```

Part (ii): `C_β(1) → C_0(1)` as `β ↓ 0`. -/
theorem prop_app_iso_one_momentum_ii :
    Tendsto (fun β : ℝ => Cbeta β 1 1) (𝓝[>] (0 : ℝ)) (𝓝 (Cbeta 0 1 1)) := by
  have h := prop_app_iso_beta_zero_i (γ := 1) one_pos
  have e := prop_app_iso_beta_zero_ii (γ := 1) one_pos le_rfl
  rw [e] at h
  exact h

/-! ## The zero-ridge laws at large aspect ratio (part (i) only) -/

private lemma zr5_R_pos {ι x : ℝ} (hι1 : ι < 1) (hx0 : 0 < x) (hxι : x < ι) :
    0 < (1 - x) * (ι - x) := by
  apply mul_pos <;> linarith

private lemma zr5_D_pos {ι x : ℝ} (hι0 : 0 < ι) (hι1 : ι < 1) (hx0 : 0 ≤ x) (hxι : x ≤ ι) :
    0 < (1 + ι - 2 * x) - 2 * Real.sqrt ((1 - x) * (ι - x)) := by
  have hR0 : 0 ≤ (1 - x) * (ι - x) := mul_nonneg (by linarith) (by linarith)
  have hpos : 0 < 1 + ι - 2 * x := by linarith
  have hsq : Real.sqrt ((1 - x) * (ι - x)) ^ 2 = (1 - x) * (ι - x) := Real.sq_sqrt hR0
  have hs0 : 0 ≤ Real.sqrt ((1 - x) * (ι - x)) := Real.sqrt_nonneg _
  have key : 2 * Real.sqrt ((1 - x) * (ι - x)) < 1 + ι - 2 * x := by
    nlinarith [sq_nonneg (1 - ι), sq_nonneg (1 + ι - 2 * x - 2 * Real.sqrt ((1 - x) * (ι - x)))]
  linarith

private lemma zr5_alg (x ι s : ℝ) (hs : 0 < s) (hsq : s ^ 2 = (1 - x) * (ι - x))
    (hD : 1 + ι - 2 * x - 2 * s ≠ 0) :
    1 / 2 * s + (2 * x - (1 + ι)) / 4 * ((-1 * (ι - x) + (1 - x) * -1) / (2 * s))
      - (1 - ι) ^ 2 / 8 * ((-2 - 2 * ((-1 * (ι - x) + (1 - x) * -1) / (2 * s)))
        / (1 + ι - 2 * x - 2 * s)) = s := by
  have hR' : (-1 * (ι - x) + (1 - x) * -1) = 2 * x - (1 + ι) := by ring
  rw [hR']
  have e1 : (-2 - 2 * ((2 * x - (1 + ι)) / (2 * s))) = (1 + ι - 2 * x - 2 * s) / s := by
    field_simp
    ring
  rw [e1]
  have e2 : (1 + ι - 2 * x - 2 * s) / s / (1 + ι - 2 * x - 2 * s) = 1 / s := by
    field_simp
  rw [e2]
  have hAA : (2 * x - (1 + ι)) ^ 2 - (1 - ι) ^ 2 = 4 * s ^ 2 := by
    rw [hsq]; ring
  have e3 : (2 * x - (1 + ι)) / 4 * ((2 * x - (1 + ι)) / (2 * s))
      - (1 - ι) ^ 2 / 8 * (1 / s) = ((2 * x - (1 + ι)) ^ 2 - (1 - ι) ^ 2) / (8 * s) := by
    field_simp
    ring
  have e4 : 1 / 2 * s + (2 * x - (1 + ι)) / 4 * ((2 * x - (1 + ι)) / (2 * s))
      - (1 - ι) ^ 2 / 8 * (1 / s) = s := by
    rw [show 1 / 2 * s + (2 * x - (1 + ι)) / 4 * ((2 * x - (1 + ι)) / (2 * s))
      - (1 - ι) ^ 2 / 8 * (1 / s) = 1 / 2 * s + ((2 * x - (1 + ι)) / 4 * ((2 * x - (1 + ι)) / (2 * s))
      - (1 - ι) ^ 2 / 8 * (1 / s)) by ring, e3, hAA]
    field_simp
    ring
  exact e4

private lemma zr5_antideriv_hasDeriv {ι x : ℝ} (hι0 : 0 < ι) (hι1 : ι < 1)
    (hx0 : 0 < x) (hxι : x < ι) :
    HasDerivAt (fun t : ℝ => (2 * t - (1 + ι)) / 4 * Real.sqrt ((1 - t) * (ι - t))
        - (1 - ι) ^ 2 / 8 * Real.log ((1 + ι - 2 * t) - 2 * Real.sqrt ((1 - t) * (ι - t))))
      (Real.sqrt ((1 - x) * (ι - x))) x := by
  have hRp := zr5_R_pos hι1 hx0 hxι
  have hDp := zr5_D_pos hι0 hι1 hx0.le hxι.le
  have hDp' : (1 + ι - 2 * x) - 2 * Real.sqrt ((1 - x) * (ι - x)) ≠ 0 := hDp.ne'
  have hs0 : 0 < Real.sqrt ((1 - x) * (ι - x)) := Real.sqrt_pos.2 hRp
  have hsq : Real.sqrt ((1 - x) * (ι - x)) ^ 2 = (1 - x) * (ι - x) := Real.sq_sqrt hRp.le
  have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have h2 : HasDerivAt (fun t : ℝ => ι - t) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub ι
  have hR := h1.mul h2
  have hs := hR.sqrt hRp.ne'
  have h3 : HasDerivAt (fun t : ℝ => (2 * t - (1 + ι)) / 4) (1 / 2) x := by
    have := (((hasDerivAt_id' x).const_mul 2).sub_const (1 + ι)).div_const 4
    convert this using 1
    norm_num
  have h5 : HasDerivAt (fun t : ℝ => 1 + ι - 2 * t) (-2) x := by
    have := ((hasDerivAt_id x).const_mul 2).const_sub (1 + ι)
    simpa using this
  have hD := h5.sub (hs.const_mul 2)
  have hlog := hD.log hDp'
  have hfirst := h3.mul hs
  have htot := hfirst.sub (hlog.const_mul ((1 - ι) ^ 2 / 8))
  exact htot.congr_deriv (zr5_alg x ι _ hs0 hsq hDp')

private lemma zr5_integral {ι : ℝ} (hι0 : 0 < ι) (hι1 : ι < 1) :
    ∫ x in (0 : ℝ)..ι, Real.sqrt ((1 - x) * (ι - x))
      = (1 + ι) * Real.sqrt ι / 4 + (1 - ι) ^ 2 / 8 * Real.log ((1 - Real.sqrt ι) / (1 + Real.sqrt ι)) := by
  have hcont : ContinuousOn (fun t : ℝ => (2 * t - (1 + ι)) / 4 * Real.sqrt ((1 - t) * (ι - t))
        - (1 - ι) ^ 2 / 8 * Real.log ((1 + ι - 2 * t) - 2 * Real.sqrt ((1 - t) * (ι - t))))
      (Icc 0 ι) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.mul
      · exact (by fun_prop : Continuous fun t : ℝ => (2 * t - (1 + ι)) / 4).continuousOn
      · exact (by fun_prop : Continuous fun t : ℝ => Real.sqrt ((1 - t) * (ι - t))).continuousOn
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log
      · exact (by fun_prop : Continuous fun t : ℝ =>
          (1 + ι - 2 * t) - 2 * Real.sqrt ((1 - t) * (ι - t))).continuousOn
      · intro t ht
        exact (zr5_D_pos hι0 hι1 ht.1 ht.2).ne'
  have hderiv : ∀ x ∈ Ioo (0:ℝ) ι, HasDerivAt (fun t : ℝ => (2 * t - (1 + ι)) / 4 * Real.sqrt ((1 - t) * (ι - t))
        - (1 - ι) ^ 2 / 8 * Real.log ((1 + ι - 2 * t) - 2 * Real.sqrt ((1 - t) * (ι - t))))
      (Real.sqrt ((1 - x) * (ι - x))) x := fun x hx =>
    zr5_antideriv_hasDeriv hι0 hι1 hx.1 hx.2
  have hint : IntervalIntegrable (fun x : ℝ => Real.sqrt ((1 - x) * (ι - x))) volume 0 ι :=
    (by fun_prop : Continuous fun x : ℝ => Real.sqrt ((1 - x) * (ι - x))).intervalIntegrable 0 ι
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hι0.le hcont hderiv hint]
  have hr : Real.sqrt ι ^ 2 = ι := Real.sq_sqrt hι0.le
  have hr0 : 0 < Real.sqrt ι := Real.sqrt_pos.2 hι0
  have hr1 : Real.sqrt ι < 1 := by
    have := Real.sqrt_lt_sqrt hι0.le hι1
    rwa [Real.sqrt_one] at this
  have hL1 : Real.log (1 - ι) = Real.log (1 - Real.sqrt ι) + Real.log (1 + Real.sqrt ι) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    congr 1
    linear_combination hr
  have hL2 : Real.log (1 + ι - 2 * Real.sqrt ι) = 2 * Real.log (1 - Real.sqrt ι) := by
    have e : 1 + ι - 2 * Real.sqrt ι = (1 - Real.sqrt ι) ^ 2 := by linear_combination (-1 : ℝ) * hr
    rw [e, Real.log_pow]
    push_cast
    ring
  have hL3 : Real.log ((1 - Real.sqrt ι) / (1 + Real.sqrt ι))
      = Real.log (1 - Real.sqrt ι) - Real.log (1 + Real.sqrt ι) :=
    Real.log_div (by linarith) (by linarith)
  simp only [sub_self, mul_zero, Real.sqrt_zero, sub_zero, zero_sub, one_mul, mul_one, zero_add,
    add_zero]
  rw [show (1 + ι - 2 * ι) = 1 - ι by ring, hL1, hL2, hL3]
  ring

private lemma zr5_scale {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    ∫ m in (0 : ℝ)..u, Real.sqrt ((v - m) * (u - m))
      = v ^ 2 * ∫ x in (0 : ℝ)..(u / v), Real.sqrt ((1 - x) * (u / v - x)) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have key : ∀ x : ℝ, Real.sqrt ((v - v * x) * (u - v * x))
      = v * Real.sqrt ((1 - x) * (u / v - x)) := by
    intro x
    have e : (v - v * x) * (u - v * x) = v ^ 2 * ((1 - x) * (u / v - x)) := by
      first | (field_simp; ring) | field_simp
    rw [e, Real.sqrt_mul (sq_nonneg v), Real.sqrt_sq hv.le]
  have h1 : ∫ x in (0 : ℝ)..(u / v), Real.sqrt ((v - v * x) * (u - v * x))
      = ∫ x in (0 : ℝ)..(u / v), v * Real.sqrt ((1 - x) * (u / v - x)) :=
    intervalIntegral.integral_congr (fun x _ => key x)
  have h2 := intervalIntegral.integral_comp_mul_left
    (fun m : ℝ => Real.sqrt ((v - m) * (u - m))) (a := 0) (b := u / v) hv.ne'
  have hvu : v * (u / v) = u := by first | (field_simp; ring) | field_simp
  simp only [mul_zero, hvu, smul_eq_mul] at h2
  rw [intervalIntegral.integral_const_mul] at h1
  have h3 : ∫ x in (0 : ℝ)..(u / v), Real.sqrt ((v - v * x) * (u - v * x))
      = v⁻¹ * ∫ m in (0 : ℝ)..u, Real.sqrt ((v - m) * (u - m)) := h2
  rw [h3] at h1
  have hvne : v ≠ 0 := hv.ne'
  calc ∫ m in (0 : ℝ)..u, Real.sqrt ((v - m) * (u - m))
      = v * (v⁻¹ * ∫ m in (0 : ℝ)..u, Real.sqrt ((v - m) * (u - m))) := by
        rw [← mul_assoc, mul_inv_cancel₀ hvne, one_mul]
    _ = v * (v * ∫ x in (0 : ℝ)..(u / v), Real.sqrt ((1 - x) * (u / v - x))) := by
        rw [h1]
    _ = v ^ 2 * ∫ x in (0 : ℝ)..(u / v), Real.sqrt ((1 - x) * (u / v - x)) := by ring


private lemma zr5_F1 : isoFiota 1 = 1 / 2 := by
  unfold isoFiota
  have hc : ∫ x in (0 : ℝ)..1, Real.sqrt ((1 - x) * (1 - x)) = ∫ x in (0 : ℝ)..1, (1 - x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    exact Real.sqrt_mul_self (by linarith [hx.2])
  rw [hc, div_one, intervalIntegral.integral_sub intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_id)]
  norm_num

private lemma zr5_part1 {β γin γout : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) :
    |Cbeta β γin γout - isoFiota (min γin γout / max γin γout) / Real.sqrt Real.pi|
        ≤ 2.32 / ((1 - β) * Real.sqrt (γin * γout)) := by
  have hu : 0 < min γin γout := lt_min hγin hγout
  have huv : min γin γout ≤ max γin γout := min_le_max
  have hv : 0 < max γin γout := lt_of_lt_of_le hu huv
  have hprod : γin * γout = min γin γout * max γin γout := by
    rcases le_total γin γout with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, mul_comm]
  have hpair : ∀ m : ℝ, (γin - m) * (γout - m) = (max γin γout - m) * (min γin γout - m) := by
    intro m
    rcases le_total γin γout with h | h
    · rw [min_eq_left h, max_eq_right h, mul_comm]
    · rw [min_eq_right h, max_eq_left h]
  have hMl : isoMLevel β γin γout 0 = min γin γout := by
    unfold isoMLevel
    simp [hβ0.ne']
  have hdI : dIso β γin γout 0 = Cbeta β γin γout := by
    unfold dIso Cbeta
    simp
  have hM := thm_app_iso_master_i hβ0 hβ1 hγin hγout (le_refl (0 : ℝ))
  rw [hdI, hMl] at hM
  have hint : ∫ m in (0 : ℝ)..min γin γout, isoWm γin γout m
      = (max γin γout) ^ 2 * ((min γin γout / max γin γout)
          * isoFiota (min γin γout / max γin γout)) := by
    have hc : ∫ m in (0 : ℝ)..min γin γout, isoWm γin γout m
        = ∫ m in (0 : ℝ)..min γin γout, Real.sqrt ((max γin γout - m) * (min γin γout - m)) := by
      apply intervalIntegral.integral_congr
      intro m _
      simp only [isoWm]
      rw [hpair m]
    have hne : min γin γout / max γin γout ≠ 0 := (div_pos hu hv).ne'
    rw [hc, zr5_scale hu huv]
    unfold isoFiota
    field_simp
  have hden : Real.sqrt Real.pi * γin * γout
      = Real.sqrt Real.pi * (min γin γout * max γin γout) := by
    rw [mul_assoc, ← hprod]
  have hsp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hkey : 1 / (Real.sqrt Real.pi * γin * γout) * ∫ m in (0 : ℝ)..min γin γout, isoWm γin γout m
      = isoFiota (min γin γout / max γin γout) / Real.sqrt Real.pi := by
    rw [hint, hden]
    have hune : min γin γout ≠ 0 := hu.ne'
    have hvne : max γin γout ≠ 0 := hv.ne'
    field_simp
  have h1 := hM.1
  rw [hkey] at h1
  exact h1.trans hM.2.le


/-- `thm:app-iso-zero-ridge`, snapshot `cr-2026-10-23`. The whole environment, verbatim (`sections/05b-isotropic/section.tex`, l.3047–3073):
```latex
\begin{theorem}[Zero ridge, large aspect ratios]\label{thm:app-iso-zero-ridge}
Let $\bmom\in(0,1)$ and $\gin,\gout>0$, put $\iota\defeq\gamma_\wedge/\gamma_\vee\in(0,1]$ and
\[
\mathsf F(\iota)\defeq\frac1\iota\int_0^\iota\sqrt{(1-x)(\iota-x)}\,\dif x .
\]
\begin{enumerate}[label=(\roman*)]
\item The zero-ridge constant satisfies
\[
\Big|C_\bmom(\gin,\gout)-\frac{\mathsf F(\iota)}{\sqrt\pi}\Big|\le\frac{2.32}{(1-\bmom)\sqrt{\gin\gout}},
\]
where $\mathsf F(1)=\frac12$ and, for $\iota<1$,
\[
\mathsf F(\iota)=\frac1\iota\Big[\frac{(1+\iota)\sqrt\iota}4+\frac{(1-\iota)^2}8\log\frac{1-\sqrt\iota}{1+\sqrt\iota}\Big].
\]
In particular, in the square case,
\[
\Big|C_\bmom(\gamma)-\frac1{2\sqrt\pi}\Big|\le\frac{2.32}{(1-\bmom)\gamma}\qquad(\gamma>0).
\]
\item Let $\Nin=\Nout=N$ and $\gamma=N/B\ge\gamma^\circ_\bmom$. The zero-ridge volatility of
\cref{def:app-iso-vol-zero} satisfies, with $\mathsf K^\pm_\bmom$ of \cref{eqn:app-iso-Kpm},
\[
\frac{1-2\mathsf K^-_\bmom}\gamma\le\frac{\mathfrak v_{\mathrm{iso},\bmom}}{N\gamma}-\frac12\le\frac{1+2\mathsf K^+_\bmom}\gamma .
\]
In particular $\mathfrak v_{\mathrm{iso},\bmom}=\frac{N^2}{2B}\big(1+O_\bmom(B/N)\big)$, and
$\mathfrak v_{\mathrm{iso},\bmom}/(N\gamma)\to\frac12$ as $\gamma\to\infty$ at every fixed $\bmom\in(0,1)$.
\end{enumerate}
\end{theorem}
```

Part (i), general aspect ratios: `ι = γ∧/γ∨`, the bound `|C_β(γin,γout) − 𝖥(ι)/√π|`, the values
`𝖥(1) = 1/2`, the closed form for `ι < 1`, and the square-case bound. Part (ii) (the zero-ridge
volatility) is not formalized here; it is the L-F.10 package. -/
theorem thm_app_iso_zero_ridge_i {β γin γout : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) :
    |Cbeta β γin γout - isoFiota (min γin γout / max γin γout) / Real.sqrt Real.pi|
        ≤ 2.32 / ((1 - β) * Real.sqrt (γin * γout)) ∧
    isoFiota 1 = 1 / 2 ∧
    (∀ ι : ℝ, 0 < ι → ι < 1 →
      isoFiota ι = 1 / ι * ((1 + ι) * Real.sqrt ι / 4
        + (1 - ι) ^ 2 / 8 * Real.log ((1 - Real.sqrt ι) / (1 + Real.sqrt ι)))) ∧
    (∀ γ : ℝ, 0 < γ →
      |Cbeta β γ γ - 1 / (2 * Real.sqrt Real.pi)| ≤ 2.32 / ((1 - β) * γ)) := by
  refine ⟨zr5_part1 hβ0 hβ1 hγin hγout, zr5_F1, fun ι h0 h1 => ?_, fun γ hγ => ?_⟩
  · unfold isoFiota
    rw [zr5_integral h0 h1]
  · have h := zr5_part1 (γin := γ) (γout := γ) hβ0 hβ1 hγ hγ
    rw [min_self, max_self, div_self hγ.ne', zr5_F1, Real.sqrt_mul_self hγ.le] at h
    have e : (1 : ℝ) / (2 * Real.sqrt Real.pi) = (1 / 2) / Real.sqrt Real.pi := by ring
    rw [e]
    exact h

end Muon.Isotropic

end

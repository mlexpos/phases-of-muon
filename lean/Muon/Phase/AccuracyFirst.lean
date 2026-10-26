import Muon.Phase.FirstHit
import Muon.Phase.Winners

/-!
# Appendix H: the accuracy-first ratio and the shift bound (task L-H.13)

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`:
`lem:app-phase-shift` (l.2972–2977), `prop:app-phase-forcing-r` (l.1599–1611),
`thm:app-phase-accfirst` (l.1644–1672), `cor:app-phase-accfirst-winners` (l.1676–1692).
Card: `sections/07-phase-comparison/CARD.md` §2, §3, §5 (L-H.13), §6.1.

Encoding decisions (statements only; proofs are `sorry`):
* Objects are reused from `Muon.Phase.PowerSums` (`fNq`, `Jpq`, `JN`, `rq`, `Cpq`, `Aconst`,
  `zetaR`), `Muon.Phase.Arrays` (`phaseDN`). Only the objects first defined by this section are
  new: `𝒦(r)`, the upper incomplete Gamma `Γ(a,y)`, `J_∘`, `ρ_N`, `s`, `Q_A`, `K_A`, `K_c`, and
  the three winner sets.
* `𝒦(r)` and `Γ(a,y)` are Lebesgue integrals over `Ioi`, so the Lean value is the paper's value
  whenever the integral converges (it does for `0 < r < 1`, the only range used).
* "Order" in `thm:app-phase-accfirst` (b)–(e) is read as `≍` (`Asymptotics.IsTheta`) with constants
  depending on `α, ς` only; "∼" is `Asymptotics.IsEquivalent`. The paper leaves these constants
  unstated (the same ambiguity as card §6.6); see `open_questions` in the L-H.13 result JSON.
* The SignSVD drift in `D_N` is the adopted array (`phaseDN`), i.e. `√2` times the main-text
  table value; the source statement is kept as written (CORRECTIONS.md, M1, pending).
* `cor:app-phase-accfirst-winners`: the "exactly on" claim is split into the implications
  `_i` (V → ∞), `_ii` (T → positive finite limits), `_iii` (G → 0), and the partition `_iv`.
  The converse direction follows from `_ii`–`_iv` and is not separately stated.
-/

open MeasureTheory Set Filter Topology Asymptotics

set_option linter.style.longLine false

noncomputable section

namespace Muon.Phase

/-! ## Transcription helpers

These name objects of `thm:app-phase-accfirst` and its preamble; they add no mathematical
content beyond the displayed formulas. -/

/-- Upper incomplete Gamma function `Γ(a,y) = ∫_y^∞ t^{a-1} e^{-t} dt`, `eqn:app-phase-K`. -/
def phaseUpGamma (a y : ℝ) : ℝ := ∫ t in Ioi y, t ^ (a - 1) * Real.exp (-t)

/-- `𝒦(r) = ∫_0^∞ y^{-r} Γ(2r,y)^{1/2} dy`, `eqn:app-phase-K`. -/
def phaseKr (r : ℝ) : ℝ := ∫ y in Ioi (0 : ℝ), y ^ (-r) * Real.sqrt (phaseUpGamma (2 * r) y)

/-- `J_∘(p,q) = (8q)^{-1/2} 𝒦(r_q)`, `eqn:app-phase-K`. -/
def phaseJcirc (p q : ℝ) : ℝ := (8 * q) ^ (-(1 / 2 : ℝ)) * phaseKr (rq p q)

/-- The accuracy-first ratio `ρ_N = D_N J_N(p,α)/J_N(p,α/2)` with `p = α + ς`,
`eqn:app-phase-rhoN`. -/
def phaseRhoN (α ς : ℝ) (N : ℕ) : ℝ :=
  phaseDN α N * JN N (α + ς) α / JN N (α + ς) (α / 2)

/-- The exponent `s = r_{s-SVD} = (p-1)/α` of `thm:app-phase-accfirst`. -/
def phaseS (α ς : ℝ) : ℝ := (α + ς - 1) / α

/-- `Q_A = 𝒦(s/2) / (√2 𝒦(s))` of `thm:app-phase-accfirst`. -/
def phaseQA (α ς : ℝ) : ℝ :=
  phaseKr (phaseS α ς / 2) / (Real.sqrt 2 * phaseKr (phaseS α ς))

/-- `K_A = π(2-α)/(2√2(1-α)) · 𝒦(s/2)/𝒦(s)` of `thm:app-phase-accfirst`. -/
def phaseKA (α ς : ℝ) : ℝ :=
  Real.pi * (2 - α) / (2 * Real.sqrt 2 * (1 - α)) * (phaseKr (phaseS α ς / 2) / phaseKr (phaseS α ς))

/-- `K_c = π(1-α/2) ζ(α) 𝒦((3α-2)/(2α)) / (√(8α) J(3α-1, α/2))` of `thm:app-phase-accfirst`. -/
def phaseKc (α : ℝ) : ℝ :=
  Real.pi * (1 - α / 2) * zetaR α * phaseKr ((3 * α - 2) / (2 * α)) /
    (Real.sqrt (8 * α) * Jpq (3 * α - 1) (α / 2))

/-- The limit `π ζ(α) J(p,α) / (ζ(α/2) J(p,α/2))` on the part `α > 2`, `ς > α+1` of
`cor:app-phase-accfirst-winners`. -/
def phaseAccLimT (α ς : ℝ) : ℝ :=
  Real.pi * zetaR α * Jpq (α + ς) α / (zetaR (α / 2) * Jpq (α + ς) (α / 2))

/-- The winner set `𝖵` of `cor:app-phase-accfirst-winners`: the set where `ρ_N → ∞`. -/
def phaseAccV (α ς : ℝ) : Prop :=
  (α = 1 ∧ ς < 1) ∨ (1 < α ∧ α < 2 ∧ ς < 2 * α - 1) ∨ (α = 2 ∧ ς < 3) ∨
    (2 < α ∧ ς ≤ α + 1)

/-- The set `𝖳` of `cor:app-phase-accfirst-winners`: the set where `ρ_N` has a finite positive
limit. -/
def phaseAccT (α ς : ℝ) : Prop :=
  (0 < α ∧ α < 1 ∧ ς < 1) ∨ (α = 1 ∧ ς = 1) ∨ (1 < α ∧ α < 2 ∧ ς = 2 * α - 1) ∨
    (α = 2 ∧ ς = 3) ∨ (2 < α ∧ α + 1 < ς)

/-- The set `𝖦` of `cor:app-phase-accfirst-winners`: the set where `ρ_N → 0`. -/
def phaseAccG (α ς : ℝ) : Prop :=
  (0 < α ∧ α < 1 ∧ 1 ≤ ς) ∨ (α = 1 ∧ 1 < ς) ∨ (1 < α ∧ α < 2 ∧ 2 * α - 1 < ς) ∨
    (α = 2 ∧ 3 < ς)

/-! ## Shift bound -/

/-- Finite form of `Lsum` for `N : ℕ` (private copy; the sum runs over `1 ≤ i ≤ N`). -/
private lemma ash_Lsum_fin (N : ℕ) (a q u : ℝ) :
    Lsum (N : ℕ∞) a q u
      = ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) := by
  unfold Lsum
  rw [tsum_eq_sum (s := Finset.Icc 1 N)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [if_pos ⟨by omega, by exact_mod_cast hn.2⟩]
  · intro n hn
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hn (Finset.mem_Icc.mpr ⟨h1, by exact_mod_cast h2⟩)

/-- Label `lem:app-phase-shift`, snapshot `cr-2026-10-23`. Source: `section.tex` l.2972–2977.
Verbatim statement:
\begin{lemma}[Shift bound]\label{lem:app-phase-shift}
Let $p>1$, $q>0$, $r=r_q$ and $N\ge1$. For every $u>0$,
\[
f_{N,q}(u)\le e^{-uN^{-q}}f_{N,q}(u/2)\le C_{p,q}^2\,2^{2r}\,u^{-2r}\,e^{-uN^{-q}} .
\]
\end{lemma}
-/
theorem lem_app_phase_shift {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (N : ℕ) (hN : 1 ≤ N)
    {u : ℝ} (hu : 0 < u) :
    fNq (N : ℕ∞) p q u ≤ Real.exp (-(u * (N : ℝ) ^ (-q))) * fNq (N : ℕ∞) p q (u / 2) ∧
      Real.exp (-(u * (N : ℝ) ^ (-q))) * fNq (N : ℕ∞) p q (u / 2) ≤
        Cpq p q ^ 2 * (2 : ℝ) ^ (2 * rq p q) * u ^ (-(2 * rq p q)) *
          Real.exp (-(u * (N : ℝ) ^ (-q))) := by
  have hr0 : 0 ≤ rq p q := by
    unfold rq
    exact div_nonneg (by linarith) (by linarith)
  have hd : dAQ p q = 2 * rq p q := by
    unfold dAQ rq
    ring
  have hsub : 2 * (u / 2) = u := by ring
  have hZ : 0 < Za p := by
    unfold Za
    have : 0 < 1 / (p - 1) := div_pos one_pos (by linarith)
    linarith
  have hE0 : 0 ≤ Epq p q := by
    unfold Epq
    exact le_trans (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hZ.le) (le_max_left _ _)
  have hC : Cpq p q ^ 2 = Epq p q / 2 := by
    unfold Cpq
    exact Real.sq_sqrt (by linarith)
  constructor
  · unfold fNq
    simp only [ash_Lsum_fin, hsub]
    have hterm : ∀ i ∈ Finset.Icc 1 N,
        (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q))
          ≤ Real.exp (-(u * (N : ℝ) ^ (-q))) * ((i : ℝ) ^ (-p) * Real.exp (-u * (i : ℝ) ^ (-q))) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      have hi0 : (0 : ℝ) < i := Nat.cast_pos.mpr (by omega)
      have hiN : (i : ℝ) ≤ N := by exact_mod_cast hi.2
      have hq' : (N : ℝ) ^ (-q) ≤ (i : ℝ) ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos hi0 hiN (by linarith)
      have hkey : Real.exp (-(2 * u) * (i : ℝ) ^ (-q))
          ≤ Real.exp (-(u * (N : ℝ) ^ (-q))) * Real.exp (-u * (i : ℝ) ^ (-q)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hq' hu.le]
      have hpos : 0 ≤ (i : ℝ) ^ (-p) := Real.rpow_nonneg hi0.le _
      calc (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q))
          ≤ (i : ℝ) ^ (-p) * (Real.exp (-(u * (N : ℝ) ^ (-q))) * Real.exp (-u * (i : ℝ) ^ (-q))) :=
            mul_le_mul_of_nonneg_left hkey hpos
        _ = Real.exp (-(u * (N : ℝ) ^ (-q))) * ((i : ℝ) ^ (-p) * Real.exp (-u * (i : ℝ) ^ (-q))) := by
            ring
    calc (1 / 2 : ℝ) * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q))
        ≤ (1 / 2 : ℝ) * ∑ i ∈ Finset.Icc 1 N,
            Real.exp (-(u * (N : ℝ) ^ (-q))) * ((i : ℝ) ^ (-p) * Real.exp (-u * (i : ℝ) ^ (-q))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by norm_num)
      _ = Real.exp (-(u * (N : ℝ) ^ (-q))) * ((1 / 2 : ℝ) *
            ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-p) * Real.exp (-u * (i : ℝ) ^ (-q))) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
  · have hfin_v : ∀ v : ℝ, 0 ≤ v →
        fNq (N : ℕ∞) p q v ≤ Cpq p q ^ 2 * (1 + v) ^ (-(2 * rq p q)) := by
      intro v hv
      have h1 := lem_app_phase_sums_i hp hq (N : ℕ∞) hv
      rw [hd] at h1
      unfold fNq
      rw [hC]
      calc (1 / 2 : ℝ) * Lsum (N : ℕ∞) p q v
          ≤ (1 / 2 : ℝ) * (Epq p q * (1 + v) ^ (-(2 * rq p q))) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = Epq p q / 2 * (1 + v) ^ (-(2 * rq p q)) := by ring
    have hmono : (1 + u / 2) ^ (-(2 * rq p q)) ≤ (u / 2) ^ (-(2 * rq p q)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have hdiv : (u / 2) ^ (-(2 * rq p q)) = (2 : ℝ) ^ (2 * rq p q) * u ^ (-(2 * rq p q)) := by
      rw [Real.div_rpow hu.le (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (2 * rq p q), div_inv_eq_mul]
      ring
    have hfin : fNq (N : ℕ∞) p q (u / 2)
        ≤ Cpq p q ^ 2 * ((2 : ℝ) ^ (2 * rq p q) * u ^ (-(2 * rq p q))) := by
      rw [← hdiv]
      exact le_trans (hfin_v (u / 2) (by positivity))
        (mul_le_mul_of_nonneg_left hmono (by positivity))
    refine le_trans (mul_le_mul_of_nonneg_left hfin (Real.exp_pos _).le) (le_of_eq ?_)
    ring

/-! ## Forcing integrals below the critical exponent -/

/-- Scaled power-Gamma integral: `∫_0^∞ u^{-r} e^{-cu} du = c^{r-1} Γ(1-r)` for `r < 1`, `c > 0`. -/
private lemma ash_gamma_scale (r c : ℝ) (hr : r < 1) (hc : 0 < c) :
    ∫ u in Ioi (0 : ℝ), u ^ (-r) * Real.exp (-(c * u)) = c ^ (r - 1) * Real.Gamma (1 - r) := by
  have hG : (0 : ℝ) < 1 - r := by linarith
  have hΓ := Real.Gamma_eq_integral hG
  rw [show (1 : ℝ) - r - 1 = -r by ring] at hΓ
  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      u ^ (-r) * Real.exp (-(c * u)) = c ^ r * (Real.exp (-(c * u)) * (c * u) ^ (-r)) := by
    intro u hu
    have hu' : 0 < u := hu
    have hcr : c ^ r * (c * u) ^ (-r) = u ^ (-r) := by
      rw [Real.mul_rpow hc.le hu'.le, ← mul_assoc, ← Real.rpow_add hc,
        show r + -r = 0 by ring, Real.rpow_zero, one_mul]
    rw [← hcr]
    ring
  have hsc := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x) * x ^ (-r)) 0 hc
  simp only [mul_zero] at hsc
  have hsc' : ∫ u in Ioi (0 : ℝ), Real.exp (-(c * u)) * (c * u) ^ (-r)
      = c⁻¹ * Real.Gamma (1 - r) := by
    rw [hΓ, hsc, smul_eq_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hsc',
    Real.rpow_sub_one hc.ne']
  ring

/-- Integrability of `u ↦ u^{-r} e^{-cu}` on `(0,∞)`. -/
private lemma ash_gamma_integrable (r c : ℝ) (hr : r < 1) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => u ^ (-r) * Real.exp (-(c * u))) (Ioi (0 : ℝ)) := by
  by_contra h
  have h0 : ∫ u in Ioi (0 : ℝ), u ^ (-r) * Real.exp (-(c * u)) = 0 := integral_undef h
  rw [ash_gamma_scale r c hr hc] at h0
  have hG : (0 : ℝ) < 1 - r := by linarith
  have : 0 < c ^ (r - 1) * Real.Gamma (1 - r) :=
    mul_pos (Real.rpow_pos_of_pos hc _) (Real.Gamma_pos_of_pos hG)
  linarith

/-- Continuity of `u ↦ f_{N,q}(u)` for a finite `N`. -/
private lemma ash_fNq_cont (N : ℕ) (p q : ℝ) :
    Continuous (fun u : ℝ => fNq (N : ℕ∞) p q u) := by
  have h : (fun u : ℝ => fNq (N : ℕ∞) p q u)
      = fun u => (1 / 2 : ℝ) * ∑ i ∈ Finset.Icc 1 N,
          (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) := by
    funext u
    unfold fNq
    rw [ash_Lsum_fin]
  rw [h]
  fun_prop

/-- Pointwise majorant `√f_{N,q}(u) ≤ C 2^r u^{-r} e^{-N^{-q}u/2}` (from `lem:app-phase-shift`). -/
private lemma ash_sqrt_major (N : ℕ) (hN : 1 ≤ N) {p q : ℝ} (hp : 1 < p) (hq : 0 < q)
    {u : ℝ} (hu : 0 < u) :
    Real.sqrt (fNq (N : ℕ∞) p q u) ≤
      Cpq p q * (2 : ℝ) ^ rq p q * (u ^ (-rq p q) * Real.exp (-(((N : ℝ) ^ (-q)) / 2 * u))) := by
  have hsh := le_trans (lem_app_phase_shift hp hq N hN hu).1 (lem_app_phase_shift hp hq N hN hu).2
  have hC0 : 0 ≤ Cpq p q := Real.sqrt_nonneg _
  have hy : 0 ≤ Cpq p q * (2 : ℝ) ^ rq p q
      * (u ^ (-rq p q) * Real.exp (-(((N : ℝ) ^ (-q)) / 2 * u))) :=
    mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le)
  rw [Real.sqrt_le_left hy]
  refine le_trans hsh (le_of_eq ?_)
  have h1 : (u ^ (-rq p q)) ^ 2 = u ^ (-(2 * rq p q)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
    congr 1
    push_cast
    ring
  have h2 : ((2 : ℝ) ^ rq p q) ^ 2 = (2 : ℝ) ^ (2 * rq p q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  have h3 : Real.exp (-(((N : ℝ) ^ (-q)) / 2 * u)) ^ 2 = Real.exp (-(u * (N : ℝ) ^ (-q))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow, mul_pow, mul_pow, h1, h2, h3]
  ring

/-- Integrability of `√f_{N,q}` on `(0,∞)` for `N ≥ 1` and `r < 1`. -/
private lemma ash_sqrt_integrable (N : ℕ) (hN : 1 ≤ N) {p q : ℝ} (hp : 1 < p) (hq : 0 < q)
    (hr : rq p q < 1) :
    IntegrableOn (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q u)) (Ioi (0 : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcpos : 0 < (N : ℝ) ^ (-q) / 2 := by positivity
  have hmaj : IntegrableOn
      (fun u : ℝ => Cpq p q * (2 : ℝ) ^ rq p q
        * (u ^ (-rq p q) * Real.exp (-(((N : ℝ) ^ (-q)) / 2 * u)))) (Ioi (0 : ℝ)) :=
    Integrable.const_mul (ash_gamma_integrable (rq p q) ((N : ℝ) ^ (-q) / 2) hr hcpos) _
  refine Integrable.mono' hmaj
    (Real.continuous_sqrt.comp (ash_fNq_cont N p q)).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact ash_sqrt_major N hN hp hq hu

/-- Pointwise lower envelope `√A (1+u)^{-r} ≤ √f_{N,q}(u)` on `[0, (N/4)^q]` (`lem:app-phase-sums`(ii)). -/
private lemma ash_sqrt_lower (N : ℕ) (hN : 4 ≤ N) {p q : ℝ} (hp : 1 < p) (hq : 0 < q)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ ((N : ℝ) / 4) ^ q) :
    Real.sqrt (Aconst p) * (1 + u) ^ (-rq p q) ≤ Real.sqrt (fNq (N : ℕ∞) p q u) := by
  have hL := lem_app_phase_sums_ii (a := p) (q := q) (by linarith) hq N hN hu0 hu
  have hd : dAQ p q = 2 * rq p q := by unfold dAQ rq; ring
  rw [hd] at hL
  have hA0 : 0 ≤ Aconst p := by unfold Aconst; positivity
  have hfN : Aconst p * (1 + u) ^ (-(2 * rq p q)) ≤ fNq (N : ℕ∞) p q u := by
    unfold fNq
    exact hL
  have hb : 0 ≤ (1 + u) ^ (-rq p q) := Real.rpow_nonneg (by linarith) _
  have h1 : ((1 + u) ^ (-rq p q)) ^ 2 = (1 + u) ^ (-(2 * rq p q)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show (0:ℝ) ≤ 1 + u by linarith)]
    congr 1
    push_cast
    ring
  have hsq : (Real.sqrt (Aconst p) * (1 + u) ^ (-rq p q)) ^ 2
      = Aconst p * (1 + u) ^ (-(2 * rq p q)) := by
    rw [mul_pow, Real.sq_sqrt hA0, h1]
  calc Real.sqrt (Aconst p) * (1 + u) ^ (-rq p q)
      = Real.sqrt ((Real.sqrt (Aconst p) * (1 + u) ^ (-rq p q)) ^ 2) :=
        (Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hb)).symm
    _ ≤ Real.sqrt (fNq (N : ℕ∞) p q u) := Real.sqrt_le_sqrt (by rw [hsq]; exact hfN)

/-- Label `prop:app-phase-forcing-r`, part (i), snapshot `cr-2026-10-23`. Source: `section.tex`
l.1599–1611 (item l.1602). Verbatim:
\item For every $N\ge1$, $J_N(p,q)\le2\Gamma(1-r)\,C\,N^{q(1-r)}$.
-/
theorem prop_app_phase_forcing_r_i {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : rq p q < 1) :
    ∀ N : ℕ, 1 ≤ N →
      JN N p q ≤ 2 * Real.Gamma (1 - rq p q) * Cpq p q * (N : ℝ) ^ (q * (1 - rq p q)) := by
  intro N hN
  have hcpos : 0 < (N : ℝ) ^ (-q) / 2 := by
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    positivity
  have hI := ash_gamma_scale (rq p q) ((N : ℝ) ^ (-q) / 2) hr hcpos
  have hmaj : IntegrableOn
      (fun u : ℝ => Cpq p q * (2 : ℝ) ^ rq p q
        * (u ^ (-rq p q) * Real.exp (-(((N : ℝ) ^ (-q)) / 2 * u)))) (Ioi (0 : ℝ)) :=
    Integrable.const_mul (ash_gamma_integrable (rq p q) ((N : ℝ) ^ (-q) / 2) hr hcpos) _
  have hfi := ash_sqrt_integrable N hN hp hq hr
  have hbound : ∫ u in Ioi (0 : ℝ), Real.sqrt (fNq (N : ℕ∞) p q u)
      ≤ ∫ u in Ioi (0 : ℝ), Cpq p q * (2 : ℝ) ^ rq p q
        * (u ^ (-rq p q) * Real.exp (-(((N : ℝ) ^ (-q)) / 2 * u))) :=
    setIntegral_mono_on hfi hmaj measurableSet_Ioi (fun u hu => ash_sqrt_major N hN hp hq hu)
  rw [integral_const_mul, hI] at hbound
  unfold JN
  refine le_trans hbound (le_of_eq ?_)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have halg : (2 : ℝ) ^ rq p q * ((N : ℝ) ^ (-q) / 2) ^ (rq p q - 1)
      = 2 * (N : ℝ) ^ (q * (1 - rq p q)) := by
    rw [Real.div_rpow (show (0 : ℝ) ≤ (N : ℝ) ^ (-q) by positivity)
        (show (0 : ℝ) ≤ 2 by norm_num),
      ← Real.rpow_mul (show (0 : ℝ) ≤ (N : ℝ) by positivity),
      Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show -q * (rq p q - 1) = q * (1 - rq p q) by ring]
    have h2r : (0 : ℝ) < (2 : ℝ) ^ rq p q := by positivity
    field_simp
  linear_combination (Cpq p q * Real.Gamma (1 - rq p q)) * halg

/-- Label `prop:app-phase-forcing-r`, part (ii), snapshot `cr-2026-10-23`. Source: `section.tex`
l.1599–1611 (item l.1603–1606). Verbatim:
\item For every $N$ with $(N/4)^{q(1-r)}\ge2$,
\[
J_N(p,q)\ge\frac{\sqrt A}{2(1-r)}\,4^{-q(1-r)}N^{q(1-r)} .
\]
-/
theorem prop_app_phase_forcing_r_ii {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : rq p q < 1) :
    ∀ N : ℕ, 2 ≤ ((N : ℝ) / 4) ^ (q * (1 - rq p q)) →
      Real.sqrt (Aconst p) / (2 * (1 - rq p q)) * (4 : ℝ) ^ (-(q * (1 - rq p q))) *
          (N : ℝ) ^ (q * (1 - rq p q)) ≤ JN N p q := by
  intro N hN2
  have hs : 0 < q * (1 - rq p q) := mul_pos hq (by linarith)
  have hN4 : (4 : ℝ) < N := by
    by_contra hcon
    push_neg at hcon
    have h1 : (N : ℝ) / 4 ≤ 1 := by linarith
    have h0 : (0 : ℝ) ≤ (N : ℝ) / 4 := by positivity
    have := Real.rpow_le_one h0 h1 hs.le
    linarith
  have hN4n : 4 ≤ N := by
    have : (4 : ℕ) < N := by exact_mod_cast hN4
    omega
  have hN1 : 1 ≤ N := by omega
  have hV0 : (0 : ℝ) ≤ ((N : ℝ) / 4) ^ q := by positivity
  have hW : (((N : ℝ) / 4) ^ q) ^ (1 - rq p q) = ((N : ℝ) / 4) ^ (q * (1 - rq p q)) := by
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ (N : ℝ) / 4 by positivity)]
  have hWform : (((N : ℝ) / 4) ^ q) ^ (1 - rq p q)
      = (4 : ℝ) ^ (-(q * (1 - rq p q))) * (N : ℝ) ^ (q * (1 - rq p q)) := by
    rw [hW, Real.div_rpow (show (0 : ℝ) ≤ (N : ℝ) by positivity) (show (0 : ℝ) ≤ 4 by norm_num),
      Real.rpow_neg (show (0 : ℝ) ≤ 4 by norm_num)]
    ring
  have hfi := ash_sqrt_integrable N hN1 hp hq hr
  have hfc : Continuous (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q u)) :=
    Real.continuous_sqrt.comp (ash_fNq_cont N p q)
  have hI1 : IntervalIntegrable (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q u)) volume 0
      (((N : ℝ) / 4) ^ q) :=
    hfc.intervalIntegrable _ _
  have hgc : ContinuousOn (fun u : ℝ => Real.sqrt (Aconst p) * (1 + u) ^ (-rq p q))
      (Set.uIcc 0 (((N : ℝ) / 4) ^ q)) := by
    rw [Set.uIcc_of_le hV0]
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const (by fun_prop)
    intro x hx
    left
    exact (by linarith [hx.1] : (0 : ℝ) < 1 + x).ne'
  have hI2 : IntervalIntegrable (fun u : ℝ => Real.sqrt (Aconst p) * (1 + u) ^ (-rq p q)) volume 0
      (((N : ℝ) / 4) ^ q) :=
    hgc.intervalIntegrable
  have hlow1 : ∫ u in (0 : ℝ)..((N : ℝ) / 4) ^ q, Real.sqrt (Aconst p) * (1 + u) ^ (-rq p q)
      ≤ ∫ u in (0 : ℝ)..((N : ℝ) / 4) ^ q, Real.sqrt (fNq (N : ℕ∞) p q u) :=
    intervalIntegral.integral_mono_on hV0 hI2 hI1
      (fun u hu => ash_sqrt_lower N hN4n hp hq hu.1 hu.2)
  have hlow2 : ∫ u in (0 : ℝ)..((N : ℝ) / 4) ^ q, Real.sqrt (fNq (N : ℕ∞) p q u) ≤ JN N p q := by
    unfold JN
    rw [intervalIntegral.integral_of_le hV0]
    exact setIntegral_mono_set hfi (Filter.Eventually.of_forall fun u => Real.sqrt_nonneg _)
      (Filter.Eventually.of_forall fun u hu => Set.Ioc_subset_Ioi_self hu)
  have hcomp : ∫ u in (0 : ℝ)..((N : ℝ) / 4) ^ q, Real.sqrt (Aconst p) * (1 + u) ^ (-rq p q)
      = Real.sqrt (Aconst p) * ((((1 : ℝ) + ((N : ℝ) / 4) ^ q) ^ (1 - rq p q) - 1) / (1 - rq p q)) := by
    rw [intervalIntegral.integral_const_mul]
    have hc := intervalIntegral.integral_comp_add_left (fun x : ℝ => x ^ (-rq p q)) (1 : ℝ)
      (a := 0) (b := ((N : ℝ) / 4) ^ q)
    rw [hc, add_zero, integral_rpow (Or.inl (by linarith))]
    rw [show -rq p q + 1 = 1 - rq p q by ring, Real.one_rpow]
  have hX : (((N : ℝ) / 4) ^ q) ^ (1 - rq p q) / 2
      ≤ ((1 : ℝ) + ((N : ℝ) / 4) ^ q) ^ (1 - rq p q) - 1 := by
    have hW2 : 2 ≤ (((N : ℝ) / 4) ^ q) ^ (1 - rq p q) := by rw [hW]; exact hN2
    have hmono : (((N : ℝ) / 4) ^ q) ^ (1 - rq p q)
        ≤ ((1 : ℝ) + ((N : ℝ) / 4) ^ q) ^ (1 - rq p q) :=
      Real.rpow_le_rpow hV0 (by linarith) (by linarith)
    linarith
  have hk : 0 ≤ Real.sqrt (Aconst p) / (1 - rq p q) :=
    div_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hfin : Real.sqrt (Aconst p) / (2 * (1 - rq p q)) * ((((N : ℝ) / 4) ^ q) ^ (1 - rq p q))
      ≤ Real.sqrt (Aconst p) * ((((1 : ℝ) + ((N : ℝ) / 4) ^ q) ^ (1 - rq p q) - 1) / (1 - rq p q)) := by
    calc Real.sqrt (Aconst p) / (2 * (1 - rq p q)) * ((((N : ℝ) / 4) ^ q) ^ (1 - rq p q))
        = (Real.sqrt (Aconst p) / (1 - rq p q)) * ((((N : ℝ) / 4) ^ q) ^ (1 - rq p q) / 2) := by
          simp only [div_eq_mul_inv, mul_inv]
          ring
      _ ≤ (Real.sqrt (Aconst p) / (1 - rq p q))
          * (((1 : ℝ) + ((N : ℝ) / 4) ^ q) ^ (1 - rq p q) - 1) :=
          mul_le_mul_of_nonneg_left hX hk
      _ = Real.sqrt (Aconst p) * ((((1 : ℝ) + ((N : ℝ) / 4) ^ q) ^ (1 - rq p q) - 1)
          / (1 - rq p q)) := by ring
  rw [hWform] at hfin
  have hchain : Real.sqrt (Aconst p) / (2 * (1 - rq p q))
      * ((4 : ℝ) ^ (-(q * (1 - rq p q))) * (N : ℝ) ^ (q * (1 - rq p q))) ≤ JN N p q := by
    refine le_trans hfin ?_
    rw [← hcomp]
    exact le_trans hlow1 hlow2
  calc Real.sqrt (Aconst p) / (2 * (1 - rq p q)) * (4 : ℝ) ^ (-(q * (1 - rq p q)))
        * (N : ℝ) ^ (q * (1 - rq p q))
      = Real.sqrt (Aconst p) / (2 * (1 - rq p q))
        * ((4 : ℝ) ^ (-(q * (1 - rq p q))) * (N : ℝ) ^ (q * (1 - rq p q))) := by ring
    _ ≤ JN N p q := hchain

/-- Right Riemann sums of a function continuous on `[0,1]` converge to its integral. -/
private lemma ash3_riemann (F : ℝ → ℝ) (hF : ContinuousOn F (Icc 0 1)) :
    Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ∑ i ∈ Finset.Icc 1 N, F ((i : ℝ) / N)) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, F x)) := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hF
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hU⟩ := huc (ε / 2) (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
  refine ⟨M + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    linarith
  have hNδ : 1 / (N : ℝ) < δ := by
    have h1 : 1 / δ < N := by
      have : (M : ℝ) + 1 ≤ N := by exact_mod_cast hN
      linarith
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hδ] at h1
    linarith
  have hmem : ∀ k : ℕ, k ≤ N → (k : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
    intro k hk
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNpos]
    exact_mod_cast hk
  have hint : ∀ k ∈ Finset.range N, IntervalIntegrable F volume ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hle : (k : ℝ) / N ≤ ((k + 1 : ℕ) : ℝ) / N := by
      apply div_le_div_of_nonneg_right _ hNpos.le
      push_cast; linarith
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]
    refine hF.mono (Set.Icc_subset_Icc (hmem k hk.le).1 (hmem (k + 1) (by omega)).2)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := F) (μ := volume)
    (a := fun k : ℕ => (k : ℝ) / N) (n := N) (fun k hk => hint k (Finset.mem_range.mpr hk))
  simp only [Nat.cast_zero, zero_div, div_self hNpos.ne'] at hsum
  have hreidx : ∑ i ∈ Finset.Icc 1 N, F ((i : ℝ) / N) = ∑ k ∈ Finset.range N, F (((k + 1 : ℕ) : ℝ) / N) := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun i : ℕ => F ((i : ℝ) / N)) 0 N 1]
    rfl
  rw [hreidx, Real.dist_eq, ← hsum, Finset.mul_sum]
  have hconst : ∀ k ∈ Finset.range N, 1 / (N : ℝ) * F (((k + 1 : ℕ) : ℝ) / N)
      = ∫ x in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N), F (((k + 1 : ℕ) : ℝ) / N) := by
    intro k hk
    rw [intervalIntegral.integral_const, smul_eq_mul]
    congr 1
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl hconst, ← Finset.sum_sub_distrib]
  have hk : ∀ k ∈ Finset.range N,
      ‖(∫ x in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N), F (((k + 1 : ℕ) : ℝ) / N))
        - ∫ x in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N), F x‖ ≤ ε / 2 * (1 / N) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hle : (k : ℝ) / N ≤ ((k + 1 : ℕ) : ℝ) / N := by
      apply div_le_div_of_nonneg_right _ hNpos.le
      push_cast; linarith
    have hi1 : IntervalIntegrable F volume ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N) := hint k (Finset.mem_range.mpr hk)
    rw [← intervalIntegral.integral_sub intervalIntegrable_const hi1]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x => F (((k + 1 : ℕ) : ℝ) / N) - F x) (a := (k : ℝ) / N) (b := ((k + 1 : ℕ) : ℝ) / N)
      (C := ε / 2) (fun x hx => ?_)
    · refine le_trans this (le_of_eq ?_)
      rw [abs_of_nonneg (by linarith [hle])]
      push_cast
      field_simp
      ring
    · rw [Set.uIoc_of_le hle] at hx
      rw [Real.norm_eq_abs]
      have hxm : x ∈ Icc (0 : ℝ) 1 :=
        ⟨le_trans (hmem k hk.le).1 hx.1.le, le_trans hx.2 (hmem (k + 1) (by omega)).2⟩
      have hd : dist x (((k + 1 : ℕ) : ℝ) / N) < δ := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hx.2])]
        have : ((k + 1 : ℕ) : ℝ) / N - x ≤ ((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N := by linarith [hx.1]
        refine lt_of_le_of_lt this (lt_of_eq_of_lt ?_ hNδ)
        push_cast; field_simp; ring
      have := hU _ (hmem (k + 1) (by omega)) x hxm (by rw [dist_comm]; exact hd)
      rw [Real.dist_eq] at this
      exact this.le
  have htot := norm_sum_le_of_le (Finset.range N) hk
  simp only [Real.norm_eq_abs] at htot
  refine lt_of_le_of_lt htot ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (N : ℝ) * (ε / 2 * (1 / N)) = ε / 2 := by field_simp
  linarith

/-- The Riemann-sum integrand `t ↦ t^{-p} e^{-2w t^{-q}}` is continuous on `[0,1]`. -/
private lemma ash3_phi_cont {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {w : ℝ} (hw : 0 < w) :
    ContinuousOn (fun t : ℝ => t ^ (-p) * Real.exp (-(2 * w) * t ^ (-q))) (Icc 0 1) := by
  intro t ht
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    have hv : (0 : ℝ) ^ (-p) * Real.exp (-(2 * w) * (0 : ℝ) ^ (-q)) = 0 := by
      rw [Real.zero_rpow (neg_ne_zero.mpr hp.ne')]
      simp
    have hT := tendsto_rpow_neg_nhdsGT_zero (y := -q) (by linarith)
    have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p / q) (2 * w) (by positivity)).comp hT
    have hcongr : ∀ t : ℝ, 0 < t → t ^ (-p) * Real.exp (-(2 * w) * t ^ (-q))
        = ((fun x : ℝ => x ^ (p / q) * Real.exp (-(2 * w) * x)) ∘ (fun x : ℝ => x ^ (-q))) t := by
      intro t ht
      simp only [Function.comp]
      rw [← Real.rpow_mul ht.le]
      congr 2
      field_simp
    have h2 : Tendsto (fun t : ℝ => t ^ (-p) * Real.exp (-(2 * w) * t ^ (-q))) (𝓝[>] 0) (𝓝 0) := by
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hcongr t ht).symm
    have hcw : ContinuousWithinAt (fun t : ℝ => t ^ (-p) * Real.exp (-(2 * w) * t ^ (-q))) (Ioi 0) 0 := by
      rw [ContinuousWithinAt, hv]
      exact h2
    have hci : ContinuousWithinAt (fun t : ℝ => t ^ (-p) * Real.exp (-(2 * w) * t ^ (-q))) (Ici 0) 0 := by
      rw [← Set.Ioi_insert, continuousWithinAt_insert_self]
      exact hcw
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE (by norm_num : (0 : ℝ) < 1)]
    exact hci
  · have hc : ContinuousAt (fun t : ℝ => t ^ (-p) * Real.exp (-(2 * w) * t ^ (-q))) t := by
      apply ContinuousAt.mul
      · exact Real.continuousAt_rpow_const _ _ (Or.inl hpos.ne')
      · exact Real.continuous_exp.continuousAt.comp
          (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl hpos.ne')))
    exact hc.continuousWithinAt

/-- Rescaled forcing as a Riemann sum. -/
private lemma ash3_scaled_sum (N : ℕ) (hN : 1 ≤ N) (p q w : ℝ) :
    (N : ℝ) ^ (p - 1) * fNq (N : ℕ∞) p q ((N : ℝ) ^ q * w)
      = (1 / 2) * ((1 / (N : ℝ)) * ∑ i ∈ Finset.Icc 1 N,
          ((i : ℝ) / N) ^ (-p) * Real.exp (-(2 * w) * ((i : ℝ) / N) ^ (-q))) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  unfold fNq
  rw [ash_Lsum_fin, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : (0 : ℝ) < i := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hi).1; omega)
  have e1 : ((i : ℝ) / N) ^ (-p) = (i : ℝ) ^ (-p) * (N : ℝ) ^ p := by
    rw [Real.div_rpow hi'.le hNpos.le, Real.rpow_neg hNpos.le, div_inv_eq_mul]
  have e2 : ((i : ℝ) / N) ^ (-q) = (i : ℝ) ^ (-q) * (N : ℝ) ^ q := by
    rw [Real.div_rpow hi'.le hNpos.le, Real.rpow_neg hNpos.le, div_inv_eq_mul]
  have e3 : (N : ℝ) ^ (p - 1) = (N : ℝ) ^ p / N := Real.rpow_sub_one hNpos.ne' p
  rw [e1, e2, e3]
  have e4 : -(2 * ((N : ℝ) ^ q * w)) * (i : ℝ) ^ (-q) = -(2 * w) * ((i : ℝ) ^ (-q) * (N : ℝ) ^ q) := by ring
  rw [e4]
  field_simp

/-- Pointwise limit of the rescaled forcing. -/
private lemma ash3_pointwise {p q : ℝ} (hp : 1 < p) (hq : 0 < q) {w : ℝ} (hw : 0 < w) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (p - 1) * fNq (N : ℕ∞) p q ((N : ℝ) ^ q * w)) atTop
      (𝓝 ((1 / 2) * ∫ t in (0 : ℝ)..1, t ^ (-p) * Real.exp (-(2 * w) * t ^ (-q)))) := by
  have h := (ash3_riemann (fun t : ℝ => t ^ (-p) * Real.exp (-(2 * w) * t ^ (-q))) (ash3_phi_cont (p := p) (by linarith) hq hw)).const_mul (1 / 2)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (ash3_scaled_sum N hN p q w).symm

/-- Scaling of the upper incomplete Gamma integral. -/
private lemma ash3_upGamma_scale (a b : ℝ) (hb : 0 < b) :
    ∫ v in Ioi (1 : ℝ), v ^ (a - 1) * Real.exp (-(b * v)) = b ^ (-a) * phaseUpGamma a b := by
  have hsc := integral_comp_mul_left_Ioi (fun s : ℝ => s ^ (a - 1) * Real.exp (-s)) 1 hb
  simp only [mul_one] at hsc
  have hpt : ∀ v ∈ Ioi (1 : ℝ), v ^ (a - 1) * Real.exp (-(b * v))
      = b ^ (1 - a) * ((b * v) ^ (a - 1) * Real.exp (-(b * v))) := by
    intro v hv
    have hv0 : 0 < v := lt_trans one_pos hv
    rw [Real.mul_rpow hb.le hv0.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hb,
      show 1 - a + (a - 1) = 0 by ring, Real.rpow_zero, one_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hsc, smul_eq_mul]
  unfold phaseUpGamma
  rw [← mul_assoc, show b ^ (1 - a) * b⁻¹ = b ^ (-a) by
    rw [Real.rpow_sub hb, Real.rpow_one]; rw [Real.rpow_neg hb.le]; field_simp]

/-- Closed form of the limiting Riemann integral, `Φ(z) = (2z)^{-2r} Γ(2r,2z)/q`. -/
private lemma ash3_G_closed {p q : ℝ} (hq : 0 < q) {w : ℝ} (hw : 0 < w) :
    ∫ t in (0 : ℝ)..1, t ^ (-p) * Real.exp (-(2 * w) * t ^ (-q))
      = (1 / q) * ((2 * w) ^ (-(2 * rq p q)) * phaseUpGamma (2 * rq p q) (2 * w)) := by
  have h2r : 2 * rq p q = (p - 1) / q := by unfold rq; field_simp
  have himg : (fun v : ℝ => v ^ (-(1 / q))) '' Ioi (1 : ℝ) = Ioo 0 1 := by
    ext t
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv0 : 0 < v := lt_trans one_pos hv
      refine ⟨Real.rpow_pos_of_pos hv0 _, ?_⟩
      have := Real.rpow_lt_one_of_one_lt_of_neg hv (show -(1 / q) < 0 by
        have : 0 < 1 / q := by positivity
        linarith)
      exact this
    · rintro ⟨h0, h1⟩
      refine ⟨t ^ (-q), ?_, ?_⟩
      · exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg h0 h1 (by linarith)
      · simp only
        rw [← Real.rpow_mul h0.le]
        rw [show -q * -(1 / q) = 1 by field_simp, Real.rpow_one]
  have hderiv : ∀ v ∈ Ioi (1 : ℝ), HasDerivWithinAt (fun v : ℝ => v ^ (-(1 / q)))
      (-(1 / q) * v ^ (-(1 / q) - 1)) (Ioi 1) v := by
    intro v hv
    have hv0 : 0 < v := lt_trans one_pos hv
    exact (Real.hasDerivAt_rpow_const (Or.inl hv0.ne')).hasDerivWithinAt
  have hinj : InjOn (fun v : ℝ => v ^ (-(1 / q))) (Ioi (1 : ℝ)) := by
    refine (Real.rpow_left_injOn (by
      have : 0 < 1 / q := by positivity
      linarith : -(1 / q) ≠ 0)).mono ?_
    intro v hv
    exact le_of_lt (lt_trans one_pos (Set.mem_Ioi.mp hv))
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ← himg,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  have hpt : ∀ v ∈ Ioi (1 : ℝ),
      |(-(1 / q) * v ^ (-(1 / q) - 1))| • ((v ^ (-(1 / q))) ^ (-p)
          * Real.exp (-(2 * w) * (v ^ (-(1 / q))) ^ (-q)))
        = (1 / q) * (v ^ (2 * rq p q - 1) * Real.exp (-((2 * w) * v))) := by
    intro v hv
    have hv0 : 0 < v := lt_trans one_pos hv
    have hq1 : 0 < 1 / q := by positivity
    rw [smul_eq_mul, abs_mul, abs_neg, abs_of_pos hq1,
      abs_of_pos (Real.rpow_pos_of_pos hv0 _), ← Real.rpow_mul hv0.le, ← Real.rpow_mul hv0.le,
      show -(1 / q) * -q = 1 by field_simp, Real.rpow_one]
    have : v ^ (-(1 / q) - 1) * v ^ (-(1 / q) * -p) = v ^ (2 * rq p q - 1) := by
      rw [← Real.rpow_add hv0, h2r]
      congr 1
      field_simp
      ring
    rw [← this]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    ash3_upGamma_scale _ _ (by linarith)]

/-- The limit integral equals `J_∘(p,q)`. -/
private lemma ash3_limit_val {p q : ℝ} (hq : 0 < q) :
    ∫ w in Ioi (0 : ℝ),
        Real.sqrt ((1 / 2) * ∫ t in (0 : ℝ)..1, t ^ (-p) * Real.exp (-(2 * w) * t ^ (-q)))
      = phaseJcirc p q := by
  set r := rq p q with hr
  have hpt : ∀ w ∈ Ioi (0 : ℝ),
      Real.sqrt ((1 / 2) * ∫ t in (0 : ℝ)..1, t ^ (-p) * Real.exp (-(2 * w) * t ^ (-q)))
        = Real.sqrt (1 / 2 * (1 / q)) * ((2 * w) ^ (-r) * Real.sqrt (phaseUpGamma (2 * r) (2 * w))) := by
    intro w hw
    have hw0 : 0 < w := hw
    rw [ash3_G_closed hq hw0, ← hr]
    have hx : 0 ≤ 1 / 2 * (1 / q) * (2 * w) ^ (-(2 * r)) := by positivity
    rw [show (1 / 2 : ℝ) * (1 / q * ((2 * w) ^ (-(2 * r)) * phaseUpGamma (2 * r) (2 * w)))
        = 1 / 2 * (1 / q) * (2 * w) ^ (-(2 * r)) * phaseUpGamma (2 * r) (2 * w) by ring,
      Real.sqrt_mul hx, Real.sqrt_mul (by positivity)]
    have hs : Real.sqrt ((2 * w) ^ (-(2 * r))) = (2 * w) ^ (-r) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
      congr 1
      ring
    rw [hs]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have hsc := integral_comp_mul_left_Ioi
    (fun y : ℝ => y ^ (-r) * Real.sqrt (phaseUpGamma (2 * r) y)) 0 (by norm_num : (0 : ℝ) < 2)
  simp only [mul_zero] at hsc
  rw [hsc, smul_eq_mul]
  unfold phaseJcirc phaseKr
  rw [← hr, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  have e1 : Real.sqrt (8 * q) = 2 * Real.sqrt (2 * q) := by
    rw [show 8 * q = 2 ^ 2 * (2 * q) by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have e2 : Real.sqrt (1 / 2 * (1 / q)) = (Real.sqrt (2 * q))⁻¹ := by
    rw [← Real.sqrt_inv]
    congr 1
    field_simp
  rw [e1, e2]
  have : Real.sqrt (2 * q) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

/-- `√(N^{p-1} x) = N^{q r} √x`. -/
private lemma ash3_sqrt_scale (N : ℕ) {p q : ℝ} (hq : 0 < q) (x : ℝ) :
    Real.sqrt ((N : ℝ) ^ (p - 1) * x) = (N : ℝ) ^ (q * rq p q) * Real.sqrt x := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [Real.sqrt_mul (Real.rpow_nonneg hN0 _), Real.sqrt_eq_rpow, ← Real.rpow_mul hN0]
  congr 2
  unfold rq
  field_simp

/-- Rescaling `u = N^q w`. -/
private lemma ash3_rescale (N : ℕ) (hN : 1 ≤ N) {p q : ℝ} (hq : 0 < q) :
    JN N p q / (N : ℝ) ^ (q * (1 - rq p q))
      = ∫ w in Ioi (0 : ℝ), Real.sqrt ((N : ℝ) ^ (p - 1) * fNq (N : ℕ∞) p q ((N : ℝ) ^ q * w)) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hc : (0 : ℝ) < (N : ℝ) ^ q := by positivity
  simp_rw [ash3_sqrt_scale N hq]
  rw [integral_const_mul]
  have hsc := integral_comp_mul_left_Ioi (fun u : ℝ => Real.sqrt (fNq (N : ℕ∞) p q u)) 0 hc
  simp only [mul_zero] at hsc
  rw [hsc, smul_eq_mul]
  unfold JN
  have e : (N : ℝ) ^ (q * (1 - rq p q)) = (N : ℝ) ^ q / (N : ℝ) ^ (q * rq p q) := by
    rw [← Real.rpow_sub hNpos]
    congr 1
    ring
  rw [e]
  have : (N : ℝ) ^ (q * rq p q) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
  field_simp

/-- Majorant for the rescaled integrand. -/
private lemma ash3_major (N : ℕ) (hN : 1 ≤ N) {p q : ℝ} (hp : 1 < p) (hq : 0 < q) {w : ℝ} (hw : 0 < w) :
    Real.sqrt ((N : ℝ) ^ (p - 1) * fNq (N : ℕ∞) p q ((N : ℝ) ^ q * w))
      ≤ Cpq p q * (2 : ℝ) ^ rq p q * (w ^ (-rq p q) * Real.exp (-((1 / 2 : ℝ) * w))) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hc : (0 : ℝ) < (N : ℝ) ^ q := by positivity
  rw [ash3_sqrt_scale N hq]
  have h := ash_sqrt_major N hN hp hq (mul_pos hc hw)
  have e1 : (N : ℝ) ^ (q * rq p q) * ((N : ℝ) ^ q * w) ^ (-rq p q) = w ^ (-rq p q) := by
    rw [Real.mul_rpow hc.le hw.le, ← Real.rpow_mul hNpos.le, ← mul_assoc, ← Real.rpow_add hNpos]
    rw [show q * rq p q + q * -rq p q = 0 by ring, Real.rpow_zero, one_mul]
  have e2 : ((N : ℝ) ^ (-q)) / 2 * ((N : ℝ) ^ q * w) = (1 / 2 : ℝ) * w := by
    rw [Real.rpow_neg hNpos.le]
    field_simp
  rw [e2] at h
  calc (N : ℝ) ^ (q * rq p q) * Real.sqrt (fNq (N : ℕ∞) p q ((N : ℝ) ^ q * w))
      ≤ (N : ℝ) ^ (q * rq p q) * (Cpq p q * (2 : ℝ) ^ rq p q
          * (((N : ℝ) ^ q * w) ^ (-rq p q) * Real.exp (-((1 / 2 : ℝ) * w)))) :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hNpos.le _)
    _ = Cpq p q * (2 : ℝ) ^ rq p q * (w ^ (-rq p q) * Real.exp (-((1 / 2 : ℝ) * w))) := by
        rw [← e1]; ring

/-- Part (iii), convergence. -/
private lemma ash3_tendsto {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : rq p q < 1) :
    Tendsto (fun N : ℕ => JN N p q / (N : ℝ) ^ (q * (1 - rq p q))) atTop (𝓝 (phaseJcirc p q)) := by
  rw [← ash3_limit_val (p := p) hq]
  have hcont : ∀ N : ℕ, Continuous (fun w : ℝ =>
      Real.sqrt ((N : ℝ) ^ (p - 1) * fNq (N : ℕ∞) p q ((N : ℝ) ^ q * w))) := by
    intro N
    exact Real.continuous_sqrt.comp (continuous_const.mul
      ((ash_fNq_cont N p q).comp (continuous_const.mul continuous_id)))
  have hD := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (l := atTop)
    (F := fun (N : ℕ) (w : ℝ) => Real.sqrt ((N : ℝ) ^ (p - 1) * fNq (N : ℕ∞) p q ((N : ℝ) ^ q * w)))
    (f := fun w : ℝ => Real.sqrt ((1 / 2) * ∫ t in (0 : ℝ)..1, t ^ (-p) * Real.exp (-(2 * w) * t ^ (-q))))
    (fun w => Cpq p q * (2 : ℝ) ^ rq p q * (w ^ (-rq p q) * Real.exp (-((1 / 2 : ℝ) * w))))
    (Eventually.of_forall fun N => (hcont N).aestronglyMeasurable)
    ?_ ?_ ?_
  · refine hD.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (ash3_rescale N hN hq).symm
  · filter_upwards [eventually_ge_atTop 1] with N hN
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun w hw => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact ash3_major N hN hp hq hw
  · exact Integrable.const_mul (ash_gamma_integrable (rq p q) (1 / 2) hr (by norm_num)) _
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun w hw => ?_)
    exact (Real.continuous_sqrt.tendsto _).comp (ash3_pointwise hp hq hw)

/-- Label `prop:app-phase-forcing-r`, part (iii), snapshot `cr-2026-10-23`. Source: `section.tex`
l.1599–1611 (item l.1607–1608). Verbatim:
\item As $N\to\infty$, $J_N(p,q)/N^{q(1-r)}\to J_\circ(p,q)$, and
$0<J_\circ(p,q)\le2\Gamma(1-r)\,C$.
-/
theorem prop_app_phase_forcing_r_iii {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : rq p q < 1) :
    Tendsto (fun N : ℕ => JN N p q / (N : ℝ) ^ (q * (1 - rq p q))) atTop
        (𝓝 (phaseJcirc p q)) ∧
      0 < phaseJcirc p q ∧ phaseJcirc p q ≤ 2 * Real.Gamma (1 - rq p q) * Cpq p q := by
  have hconv := ash3_tendsto hp hq hr
  have he : 0 < q * (1 - rq p q) := mul_pos hq (by linarith)
  refine ⟨hconv, ?_, ?_⟩
  · set c := Real.sqrt (Aconst p) / (2 * (1 - rq p q)) * (4 : ℝ) ^ (-(q * (1 - rq p q))) with hc
    have hcpos : 0 < c := by
      have hA : 0 < Aconst p := by unfold Aconst; positivity
      have : 0 < 1 - rq p q := by linarith
      rw [hc]
      positivity
    have hev : ∀ᶠ N : ℕ in atTop, c ≤ JN N p q / (N : ℝ) ^ (q * (1 - rq p q)) := by
      have hT : Tendsto (fun N : ℕ => ((N : ℝ) / 4) ^ (q * (1 - rq p q))) atTop atTop :=
        (tendsto_rpow_atTop he).comp (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num))
      filter_upwards [hT.eventually_ge_atTop 2, eventually_ge_atTop 1] with N hN2 hN1
      have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
      rw [le_div_iff₀ (by positivity)]
      exact prop_app_phase_forcing_r_ii hp hq hr N hN2
    exact lt_of_lt_of_le hcpos (ge_of_tendsto hconv hev)
  · have hev : ∀ᶠ N : ℕ in atTop,
        JN N p q / (N : ℝ) ^ (q * (1 - rq p q)) ≤ 2 * Real.Gamma (1 - rq p q) * Cpq p q := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
      rw [div_le_iff₀ (by positivity)]
      exact prop_app_phase_forcing_r_i hp hq hr N hN
    exact le_of_tendsto hconv hev

/-- Label `prop:app-phase-forcing-r`, part (iv) (the value `𝒦(1/2)`), snapshot `cr-2026-10-23`.
Source: `section.tex` l.1599–1611 (item l.1609). Verbatim:
\item $\mathcal K(\frac12)=\sqrt{2\pi}$; consequently $J_\circ(q+1,q)=\frac12\sqrt{\pi/q}$.
-/
private lemma ash_upGamma_one (y : ℝ) : phaseUpGamma 1 y = Real.exp (-y) := by
  unfold phaseUpGamma
  simp only [sub_self, Real.rpow_zero, one_mul]
  exact integral_exp_neg_Ioi y

theorem prop_app_phase_forcing_r_iv_K : phaseKr (1 / 2) = Real.sqrt (2 * Real.pi) := by
  have hsq : ∀ y : ℝ, Real.sqrt (Real.exp (-y)) = Real.exp (-((1 / 2) * y)) := by
    intro y
    have h2 : Real.exp (-((1 / 2) * y)) ^ 2 = Real.exp (-y) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [← h2, Real.sqrt_sq (Real.exp_pos _).le]
  have hpt : ∀ y ∈ Ioi (0 : ℝ),
      y ^ (-(1 / 2 : ℝ)) * Real.sqrt (phaseUpGamma (2 * (1 / 2)) y)
        = y ^ (-(1 / 2 : ℝ)) * Real.exp (-((1 / 2) * y)) := by
    intro y _
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, ash_upGamma_one, hsq]
  unfold phaseKr
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    ash_gamma_scale (1 / 2) (1 / 2) (by norm_num) (by norm_num)]
  have h2 : ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) = (Real.sqrt 2)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.Gamma_one_half_eq,
    show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num,
    Real.rpow_neg (show (0 : ℝ) ≤ 1 / 2 by norm_num), h2, inv_inv,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) Real.pi]

/-- Label `prop:app-phase-forcing-r`, part (iv) (the value `J_∘(q+1,q)`), snapshot
`cr-2026-10-23`. Source: `section.tex` l.1599–1611 (item l.1609). Verbatim:
\item $\mathcal K(\frac12)=\sqrt{2\pi}$; consequently $J_\circ(q+1,q)=\frac12\sqrt{\pi/q}$.
-/
theorem prop_app_phase_forcing_r_iv_J {q : ℝ} (hq : 0 < q) :
    phaseJcirc (q + 1) q = 1 / 2 * Real.sqrt (Real.pi / q) := by
  have hr : rq (q + 1) q = 1 / 2 := by
    unfold rq
    field_simp
    ring
  have key : Real.sqrt (8 * q) * Real.sqrt (Real.pi / q) = 2 * Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show 8 * q * (Real.pi / q) = (2 : ℝ) ^ 2 * (2 * Real.pi) by field_simp; ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hpos : Real.sqrt (8 * q) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  unfold phaseJcirc
  rw [hr, prop_app_phase_forcing_r_iv_K,
    Real.rpow_neg (show (0 : ℝ) ≤ 8 * q by linarith), ← Real.sqrt_eq_rpow]
  have hs : Real.sqrt (2 * Real.pi) = Real.sqrt (8 * q) * Real.sqrt (Real.pi / q) / 2 := by
    rw [key]
    ring
  rw [hs]
  field_simp

/-! ## Accuracy-first ratio -/

/-! ### Proved helpers for `thm:app-phase-accfirst` (task P-H.13.P4) -/

private lemma pA_Hsum_pos {a : ℝ} {N : ℕ} (hN : 1 ≤ N) : 0 < Hsum a N := by
  unfold Hsum
  apply Finset.sum_pos
  · intro i hi
    rw [Finset.mem_Icc] at hi
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
    exact Real.rpow_pos_of_pos hi0 _
  · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩

private lemma pA_DN_pos {α : ℝ} {N : ℕ} (hN : 1 ≤ N) : 0 < phaseDN α N := by
  unfold phaseDN
  exact div_pos (mul_pos Real.pi_pos (pA_Hsum_pos hN)) (pA_Hsum_pos hN)

private lemma pA_rq1 (α ς : ℝ) : rq (α + ς) α = phaseS α ς / 2 := by
  unfold rq phaseS
  ring

private lemma pA_rq2 (α ς : ℝ) : rq (α + ς) (α / 2) = phaseS α ς := by
  unfold rq phaseS
  ring

private lemma pA_rq_lt1 {α ς : ℝ} (hα : 0 < α) (hς : ς < 1) : rq (α + ς) α < 1 := by
  unfold rq
  rw [div_lt_one (by linarith)]
  linarith

private lemma pA_rq_lt2 {α ς : ℝ} (hα : 0 < α) (hς : ς < 1) : rq (α + ς) (α / 2) < 1 := by
  unfold rq
  rw [div_lt_one (by linarith)]
  linarith

private lemma pA_Jc_pos {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : rq p q < 1) :
    0 < phaseJcirc p q :=
  (prop_app_phase_forcing_r_iii hp hq hr).2.1

private lemma pA_JN_eq {α ς : ℝ} (hα : 0 < α) {N : ℕ} (hN : 1 ≤ N) :
    JN N (α + ς) α / JN N (α + ς) (α / 2) =
      (JN N (α + ς) α / (N : ℝ) ^ (α * (1 - rq (α + ς) α))) /
        (JN N (α + ς) (α / 2) / (N : ℝ) ^ ((α / 2) * (1 - rq (α + ς) (α / 2)))) *
        (N : ℝ) ^ (α / 2) := by
  have hα0 : α ≠ 0 := hα.ne'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have he : α * (1 - rq (α + ς) α) = (α / 2) * (1 - rq (α + ς) (α / 2)) + α / 2 := by
    unfold rq
    field_simp
    ring
  rw [he, Real.rpow_add hNpos]
  have h1 : (N : ℝ) ^ ((α / 2) * (1 - rq (α + ς) (α / 2))) ≠ 0 :=
    (Real.rpow_pos_of_pos hNpos _).ne'
  have h2 : (N : ℝ) ^ (α / 2) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
  field_simp

private lemma pA_rho_eq {α ς : ℝ} (hα : 0 < α) {N : ℕ} (hN : 1 ≤ N) :
    phaseRhoN α ς N = phaseDN α N *
      ((JN N (α + ς) α / (N : ℝ) ^ (α * (1 - rq (α + ς) α))) /
        (JN N (α + ς) (α / 2) / (N : ℝ) ^ ((α / 2) * (1 - rq (α + ς) (α / 2))))) *
      (N : ℝ) ^ (α / 2) := by
  unfold phaseRhoN
  rw [mul_div_assoc, pA_JN_eq hα hN]
  ring

private lemma pA_ratio_lim {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς < 1) :
    Tendsto (fun N : ℕ => JN N (α + ς) α / (N : ℝ) ^ (α * (1 - rq (α + ς) α)) /
        (JN N (α + ς) (α / 2) / (N : ℝ) ^ ((α / 2) * (1 - rq (α + ς) (α / 2)))))
      atTop (𝓝 (phaseJcirc (α + ς) α / phaseJcirc (α + ς) (α / 2))) := by
  have hA := (prop_app_phase_forcing_r_iii hp hα (pA_rq_lt1 hα hς)).1
  have hB := (prop_app_phase_forcing_r_iii hp (show (0 : ℝ) < α / 2 by linarith)
    (pA_rq_lt2 hα hς)).1
  exact hA.div hB (pA_Jc_pos hp (show (0 : ℝ) < α / 2 by linarith) (pA_rq_lt2 hα hς)).ne'

private lemma pA_Jc_ratio {α ς : ℝ} (hα : 0 < α) :
    phaseJcirc (α + ς) α / phaseJcirc (α + ς) (α / 2) = phaseQA α ς := by
  unfold phaseJcirc phaseQA
  rw [pA_rq1, pA_rq2]
  have h8 : (8 * (α / 2) : ℝ) = 4 * α := by ring
  rw [h8, Real.rpow_neg (show (0 : ℝ) ≤ 8 * α by linarith),
    Real.rpow_neg (show (0 : ℝ) ≤ 4 * α by linarith), ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow]
  have h2 : Real.sqrt (8 * α) = Real.sqrt 2 * Real.sqrt (4 * α) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs4 : Real.sqrt (4 * α) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  rw [h2]
  field_simp

private lemma pA_harm_lim {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun N : ℕ => Hsum a N / (N : ℝ) ^ (1 - a)) atTop (𝓝 (1 - a)⁻¹) := by
  have hE := lem_app_phase_harmonic_iii ha ha1
  have hc : (1 - a) ≠ 0 := (show (0 : ℝ) < 1 - a by linarith).ne'
  have hv : Tendsto (fun N : ℕ => ((N : ℝ) ^ (1 - a) / (1 - a)) / (N : ℝ) ^ (1 - a))
      atTop (𝓝 (1 - a)⁻¹) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hp : (0 : ℝ) < (N : ℝ) ^ (1 - a) := Real.rpow_pos_of_pos hNpos _
    have hpne : (N : ℝ) ^ (1 - a) ≠ 0 := hp.ne'
    field_simp
  exact (hE.div (IsEquivalent.refl (u := fun N : ℕ => (N : ℝ) ^ (1 - a)))).symm.tendsto_nhds hv

private lemma pA_zeta_pos {a : ℝ} (ha : 1 < a) : 0 < zetaR a := by
  have h := (lem_app_phase_harmonic_vi ha 1 le_rfl).1
  have h1 : Hsum a 1 = 1 := by norm_num [Hsum]
  linarith

private lemma pA_zeta_lim {a : ℝ} (ha : 1 < a) :
    Tendsto (fun N : ℕ => Hsum a N) atTop (𝓝 (zetaR a)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - a) / (a - 1)) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (show (0 : ℝ) < a - 1 by linarith)).comp
      tendsto_natCast_atTop_atTop).div_const (a - 1)
    rw [zero_div] at h
    refine h.congr (fun N => ?_)
    simp only [Function.comp_apply]
    rw [show 1 - a = -(a - 1) by ring]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) ?_ hb
  filter_upwards [eventually_ge_atTop 1] with N hN
  obtain ⟨h1, h2⟩ := lem_app_phase_harmonic_vi ha N hN
  rw [Real.norm_eq_abs, abs_of_nonpos (show Hsum a N - zetaR a ≤ 0 by linarith)]
  linarith

private lemma pA_DN_lim {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (fun N : ℕ => phaseDN α N * (N : ℝ) ^ (α / 2)) atTop
      (𝓝 (Real.pi * ((1 - α)⁻¹ / (1 - α / 2)⁻¹))) := by
  have h1 := pA_harm_lim hα hα1
  have h2 := pA_harm_lim (a := α / 2) (by linarith) (by linarith)
  have hne : (1 - α / 2)⁻¹ ≠ 0 := (inv_pos.mpr (by linarith)).ne'
  have h3 := (h1.div h2 hne).const_mul Real.pi
  refine Tendsto.congr' ?_ h3
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpow : (N : ℝ) ^ (α / 2) = (N : ℝ) ^ (1 - α / 2) / (N : ℝ) ^ (1 - α) := by
    rw [← Real.rpow_sub hNpos]
    congr 1
    ring
  have hb : Hsum (α / 2) N ≠ 0 := (pA_Hsum_pos hN).ne'
  have hA : (N : ℝ) ^ (1 - α) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
  have hB : (N : ℝ) ^ (1 - α / 2) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
  simp only [Pi.div_apply]
  unfold phaseDN
  rw [hpow]
  field_simp

/-- Label `thm:app-phase-accfirst`, part (a), snapshot `cr-2026-10-23`. Source: `section.tex`
l.1644–1672 (item l.1647–1651). Verbatim:
\item if $\texp<1$, then $\rho_N\sim D_NQ_AN^{\alpha/2}$; hence $\rho_N\to K_A$ for
$0<\alpha<1$, while $\rho_N$ is asymptotic to $\frac\pi2Q_A\log N$,
$\pi(1-\frac\alpha2)\zeta(\alpha)Q_AN^{\alpha-1}$, $\pi\zeta(2)Q_AN/\log N$ and
$\frac{\pi\zeta(\alpha)}{\zeta(\alpha/2)}Q_AN^{\alpha/2}$ for $\alpha=1$,
$1<\alpha<2$, $\alpha=2$ and $\alpha>2$;
-/
theorem thm_app_phase_accfirst_i {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς < 1) :
    IsEquivalent atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => phaseDN α N * phaseQA α ς * (N : ℝ) ^ (α / 2)) := by
  have hr1 := pA_rq_lt1 hα hς
  have hr2 := pA_rq_lt2 hα hς
  have hJ1 := pA_Jc_pos hp hα hr1
  have hJ2 := pA_Jc_pos hp (show (0 : ℝ) < α / 2 by linarith) hr2
  have hQ : phaseQA α ς ≠ 0 := by
    rw [← pA_Jc_ratio hα]
    exact div_ne_zero hJ1.ne' hJ2.ne'
  have hone : phaseJcirc (α + ς) α / phaseJcirc (α + ς) (α / 2) / phaseQA α ς = 1 := by
    rw [pA_Jc_ratio hα]
    exact div_self hQ
  have hlim := (pA_ratio_lim hα hp hς).div_const (phaseQA α ς)
  rw [hone] at hlim
  apply isEquivalent_of_tendsto_one
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hD : phaseDN α N ≠ 0 := (pA_DN_pos hN).ne'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNp : (N : ℝ) ^ (α / 2) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
  simp only [Pi.div_apply]
  rw [pA_rho_eq hα hN]
  generalize (JN N (α + ς) α / (N : ℝ) ^ (α * (1 - rq (α + ς) α))) /
      (JN N (α + ς) (α / 2) / (N : ℝ) ^ ((α / 2) * (1 - rq (α + ς) (α / 2)))) = X
  field_simp

/-- Label `thm:app-phase-accfirst`, part (a), limit `ρ_N → K_A` for `0 < α < 1`, snapshot
`cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1647–1651). Verbatim:
\item if $\texp<1$, then $\rho_N\sim D_NQ_AN^{\alpha/2}$; hence $\rho_N\to K_A$ for
$0<\alpha<1$, while $\rho_N$ is asymptotic to $\frac\pi2Q_A\log N$,
$\pi(1-\frac\alpha2)\zeta(\alpha)Q_AN^{\alpha-1}$, $\pi\zeta(2)Q_AN/\log N$ and
$\frac{\pi\zeta(\alpha)}{\zeta(\alpha/2)}Q_AN^{\alpha/2}$ for $\alpha=1$,
$1<\alpha<2$, $\alpha=2$ and $\alpha>2$;
-/
theorem thm_app_phase_accfirst_i_K {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς < 1)
    (hα1 : α < 1) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop (𝓝 (phaseKA α ς)) := by
  have hI := thm_app_phase_accfirst_i hα hp hς
  have hL : Tendsto (fun N : ℕ => phaseDN α N * phaseQA α ς * (N : ℝ) ^ (α / 2)) atTop
      (𝓝 (Real.pi * ((1 - α)⁻¹ / (1 - α / 2)⁻¹) * phaseQA α ς)) :=
    ((pA_DN_lim hα hα1).mul_const (phaseQA α ς)).congr (fun N => by ring)
  have hK := hI.symm.tendsto_nhds hL
  have hc : Real.pi * ((1 - α)⁻¹ / (1 - α / 2)⁻¹) * phaseQA α ς = phaseKA α ς := by
    have h1 : (1 - α) ≠ 0 := (show (0 : ℝ) < 1 - α by linarith).ne'
    have h2 : (1 - α / 2) ≠ 0 := (show (0 : ℝ) < 1 - α / 2 by linarith).ne'
    have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    unfold phaseQA phaseKA
    field_simp
  rw [hc] at hK
  exact hK

/-- Label `thm:app-phase-accfirst`, part (a), asymptotic for `α = 1`, snapshot `cr-2026-10-23`.
Source: `section.tex` l.1644–1672 (item l.1647–1651). Verbatim:
\item if $\texp<1$, then $\rho_N\sim D_NQ_AN^{\alpha/2}$; hence $\rho_N\to K_A$ for
$0<\alpha<1$, while $\rho_N$ is asymptotic to $\frac\pi2Q_A\log N$,
$\pi(1-\frac\alpha2)\zeta(\alpha)Q_AN^{\alpha-1}$, $\pi\zeta(2)Q_AN/\log N$ and
$\frac{\pi\zeta(\alpha)}{\zeta(\alpha/2)}Q_AN^{\alpha/2}$ for $\alpha=1$,
$1<\alpha<2$, $\alpha=2$ and $\alpha>2$;
-/
theorem thm_app_phase_accfirst_i_log {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς < 1)
    (hα1 : α = 1) :
    IsEquivalent atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => Real.pi / 2 * phaseQA α ς * Real.log (N : ℝ)) := by
  subst hα1
  have hr1 := pA_rq_lt1 hα hς
  have hr2 := pA_rq_lt2 hα hς
  have hJ1 := pA_Jc_pos hp hα hr1
  have hJ2 := pA_Jc_pos hp (show (0 : ℝ) < 1 / 2 by norm_num) hr2
  have hQ : phaseQA 1 ς ≠ 0 := by
    rw [← pA_Jc_ratio hα]
    exact div_ne_zero hJ1.ne' hJ2.ne'
  have hone : phaseJcirc (1 + ς) 1 / phaseJcirc (1 + ς) (1 / 2) / phaseQA 1 ς = 1 := by
    rw [pA_Jc_ratio hα]
    exact div_self hQ
  have hR := (pA_ratio_lim hα hp hς).div_const (phaseQA 1 ς)
  rw [hone] at hR
  have hH : Tendsto (fun N : ℕ => Hsum 1 N / Real.log N) atTop (𝓝 1) := by
    have hz : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≠ 0 := by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have h1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
      exact (Real.log_pos h1).ne'
    exact (isEquivalent_iff_tendsto_one hz).mp lem_app_phase_harmonic_iv
  have hc0 : (1 - (1 : ℝ) / 2)⁻¹ ≠ 0 := by norm_num
  have hc : Tendsto (fun N : ℕ => (Hsum (1 / 2) N / (N : ℝ) ^ (1 - (1 : ℝ) / 2))⁻¹) atTop
      (𝓝 (1 / 2)) := by
    have h := (pA_harm_lim (a := (1 : ℝ) / 2) (by norm_num) (by norm_num)).inv₀ hc0
    have e : ((1 - (1 : ℝ) / 2)⁻¹)⁻¹ = 1 / 2 := by norm_num
    rw [e] at h
    exact h
  have hG := (((hH.mul hR).mul hc).mul_const (2 : ℝ))
  rw [show (1 : ℝ) * 1 * (1 / 2) * 2 = 1 by norm_num] at hG
  apply isEquivalent_of_tendsto_one
  refine hG.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hHh : Hsum (1 / 2) N ≠ 0 := (pA_Hsum_pos hN1).ne'
  have hNa : (N : ℝ) ^ (1 - (1 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
  have hpow : (N : ℝ) ^ (1 - (1 : ℝ) / 2) = (N : ℝ) ^ ((1 : ℝ) / 2) := by norm_num
  simp only [Pi.div_apply]
  rw [pA_rho_eq hα hN1]
  generalize (JN N (1 + ς) 1 / (N : ℝ) ^ (1 * (1 - rq (1 + ς) 1))) /
      (JN N (1 + ς) (1 / 2) / (N : ℝ) ^ ((1 / 2) * (1 - rq (1 + ς) (1 / 2)))) = X
  unfold phaseDN
  rw [hpow]
  field_simp

/-- Label `thm:app-phase-accfirst`, part (a), asymptotic for `1 < α < 2`, snapshot
`cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1647–1651). Verbatim:
\item if $\texp<1$, then $\rho_N\sim D_NQ_AN^{\alpha/2}$; hence $\rho_N\to K_A$ for
$0<\alpha<1$, while $\rho_N$ is asymptotic to $\frac\pi2Q_A\log N$,
$\pi(1-\frac\alpha2)\zeta(\alpha)Q_AN^{\alpha-1}$, $\pi\zeta(2)Q_AN/\log N$ and
$\frac{\pi\zeta(\alpha)}{\zeta(\alpha/2)}Q_AN^{\alpha/2}$ for $\alpha=1$,
$1<\alpha<2$, $\alpha=2$ and $\alpha>2$;
-/
theorem thm_app_phase_accfirst_i_mid {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς < 1)
    (hα1 : 1 < α) (hα2 : α < 2) :
    IsEquivalent atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => Real.pi * (1 - α / 2) * zetaR α * phaseQA α ς * (N : ℝ) ^ (α - 1)) := by
  have hr1 := pA_rq_lt1 hα hς
  have hr2 := pA_rq_lt2 hα hς
  have hJ1 := pA_Jc_pos hp hα hr1
  have hJ2 := pA_Jc_pos hp (show (0 : ℝ) < α / 2 by linarith) hr2
  have hQ : phaseQA α ς ≠ 0 := by
    rw [← pA_Jc_ratio hα]
    exact div_ne_zero hJ1.ne' hJ2.ne'
  have hone : phaseJcirc (α + ς) α / phaseJcirc (α + ς) (α / 2) / phaseQA α ς = 1 := by
    rw [pA_Jc_ratio hα]
    exact div_self hQ
  have hR := (pA_ratio_lim hα hp hς).div_const (phaseQA α ς)
  rw [hone] at hR
  have hζ : zetaR α ≠ 0 := (pA_zeta_pos hα1).ne'
  have hH : Tendsto (fun N : ℕ => Hsum α N / zetaR α) atTop (𝓝 1) := by
    have := (pA_zeta_lim hα1).div_const (zetaR α)
    rwa [div_self hζ] at this
  have h2a : (1 - α / 2) ≠ 0 := (show (0 : ℝ) < 1 - α / 2 by linarith).ne'
  have hc0 : (1 - α / 2)⁻¹ ≠ 0 := (inv_pos.mpr (by linarith)).ne'
  have hc : Tendsto (fun N : ℕ => (Hsum (α / 2) N / (N : ℝ) ^ (1 - α / 2))⁻¹) atTop
      (𝓝 (1 - α / 2)) := by
    have h := (pA_harm_lim (show 0 < α / 2 by linarith) (show α / 2 < 1 by linarith)).inv₀ hc0
    rwa [inv_inv] at h
  have hG := ((hH.mul hR).mul hc).mul_const ((1 - α / 2)⁻¹)
  rw [show (1 : ℝ) * 1 * (1 - α / 2) * (1 - α / 2)⁻¹ = 1 by
    rw [one_mul, one_mul, mul_inv_cancel₀ h2a]] at hG
  apply isEquivalent_of_tendsto_one
  refine hG.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hHh : Hsum (α / 2) N ≠ 0 := (pA_Hsum_pos hN).ne'
  have hNa : (N : ℝ) ^ (1 - α / 2) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
  have hNb : (N : ℝ) ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
  have hpow : (N : ℝ) ^ (α / 2) = (N : ℝ) ^ (1 - α / 2) * (N : ℝ) ^ (α - 1) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  simp only [Pi.div_apply]
  rw [pA_rho_eq hα hN]
  generalize (JN N (α + ς) α / (N : ℝ) ^ (α * (1 - rq (α + ς) α))) /
      (JN N (α + ς) (α / 2) / (N : ℝ) ^ ((α / 2) * (1 - rq (α + ς) (α / 2)))) = X
  unfold phaseDN
  rw [hpow]
  field_simp

/-- Label `thm:app-phase-accfirst`, part (a), asymptotic for `α = 2`, snapshot `cr-2026-10-23`.
Source: `section.tex` l.1644–1672 (item l.1647–1651). Verbatim:
\item if $\texp<1$, then $\rho_N\sim D_NQ_AN^{\alpha/2}$; hence $\rho_N\to K_A$ for
$0<\alpha<1$, while $\rho_N$ is asymptotic to $\frac\pi2Q_A\log N$,
$\pi(1-\frac\alpha2)\zeta(\alpha)Q_AN^{\alpha-1}$, $\pi\zeta(2)Q_AN/\log N$ and
$\frac{\pi\zeta(\alpha)}{\zeta(\alpha/2)}Q_AN^{\alpha/2}$ for $\alpha=1$,
$1<\alpha<2$, $\alpha=2$ and $\alpha>2$;
-/
theorem thm_app_phase_accfirst_i_two {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς < 1)
    (hα2 : α = 2) :
    IsEquivalent atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => Real.pi * zetaR 2 * phaseQA α ς * (N : ℝ) / Real.log (N : ℝ)) := by
  have hD := (prop_app_phase_prefactors_iv α hα).2.2.2.1 hα2
  have h := thm_app_phase_accfirst_i hα hp hς
  have hm := (hD.mul (IsEquivalent.refl (u := fun _ : ℕ => phaseQA α ς))).mul
    (IsEquivalent.refl (u := fun N : ℕ => (N : ℝ) ^ (α / 2)))
  apply h.trans
  apply hm.congr_right
  exact Filter.Eventually.of_forall (fun N => by
    simp only [Pi.mul_apply, hα2]
    norm_num
    ring)

/-- Label `thm:app-phase-accfirst`, part (a), asymptotic for `α > 2`, snapshot `cr-2026-10-23`.
Source: `section.tex` l.1644–1672 (item l.1647–1651). Verbatim:
\item if $\texp<1$, then $\rho_N\sim D_NQ_AN^{\alpha/2}$; hence $\rho_N\to K_A$ for
$0<\alpha<1$, while $\rho_N$ is asymptotic to $\frac\pi2Q_A\log N$,
$\pi(1-\frac\alpha2)\zeta(\alpha)Q_AN^{\alpha-1}$, $\pi\zeta(2)Q_AN/\log N$ and
$\frac{\pi\zeta(\alpha)}{\zeta(\alpha/2)}Q_AN^{\alpha/2}$ for $\alpha=1$,
$1<\alpha<2$, $\alpha=2$ and $\alpha>2$;
-/
theorem thm_app_phase_accfirst_i_gt2 {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς < 1)
    (hα2 : 2 < α) :
    IsEquivalent atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => Real.pi * zetaR α / zetaR (α / 2) * phaseQA α ς * (N : ℝ) ^ (α / 2)) := by
  have hD := (prop_app_phase_prefactors_iv α hα).2.2.2.2 hα2
  exact (thm_app_phase_accfirst_i hα hp hς).trans
    ((hD.mul (IsEquivalent.refl (u := fun _ : ℕ => phaseQA α ς))).mul
      (IsEquivalent.refl (u := fun N : ℕ => (N : ℝ) ^ (α / 2))))

private lemma pB_critical_equiv {p q : ℝ} (hq : 0 < q) (hp : p = 2 * q + 1) :
    IsEquivalent atTop (fun N : ℕ => JN N p q)
      (fun N : ℕ => aQ q * q * Real.log (N : ℝ)) := by
  have hc : aQ q * q ≠ 0 := by
    unfold aQ
    exact (mul_pos (Real.rpow_pos_of_pos (by positivity) _) hq).ne'
  have hO : (fun N : ℕ => JN N p q - aQ q * q * Real.log (N : ℝ))
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    apply IsBigO.of_bound (2 * Cpq p q + q * Mpq p q * (2 : ℝ) ^ (-(p / q)) /
      aQ q + 1 / Real.sqrt (2 * (p - 1)))
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Real.norm_eq_abs, abs_one, mul_one]
    exact lem_app_phase_forcing_integrals_i hq hp N hN
  have hsmall : (fun _ : ℕ => (1 : ℝ)) =o[atTop]
      (fun N : ℕ => aQ q * q * Real.log (N : ℝ)) :=
    (isLittleO_const_mul_right_iff hc).mpr
      (Real.isLittleO_const_log_atTop.comp_tendsto tendsto_natCast_atTop_atTop)
  exact hO.trans_isLittleO hsmall

private lemma pB_power_equiv {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : rq p q < 1) :
    IsEquivalent atTop (fun N : ℕ => JN N p q)
      (fun N : ℕ => phaseJcirc p q * (N : ℝ) ^ (q * (1 - rq p q))) := by
  have h := prop_app_phase_forcing_r_iii hp hq hr
  have hL := h.1.div_const (phaseJcirc p q)
  rw [div_self h.2.1.ne'] at hL
  apply isEquivalent_of_tendsto_one
  refine hL.congr (fun N => ?_)
  simp only [Pi.div_apply, div_mul_eq_div_div]
  ring

private lemma pB_coefficient {α : ℝ} (hα : 0 < α) :
    (1 / 2 * Real.sqrt (Real.pi / α)) / (aQ (α / 2) * (α / 2)) =
      2 * Real.sqrt Real.pi / α := by
  have hs : Real.sqrt α ≠ 0 := (Real.sqrt_pos.mpr hα).ne'
  have h4 : Real.sqrt (8 * (α / 2)) = 2 * Real.sqrt α := by
    rw [show 8 * (α / 2) = (2 : ℝ) ^ 2 * α by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num)]
  unfold aQ
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, h4, Real.sqrt_div Real.pi_pos.le]
  field_simp

/-- Label `thm:app-phase-accfirst`, part (b), snapshot `cr-2026-10-23`. Source: `section.tex`
l.1644–1672 (item l.1652–1656). Verbatim:
\item if $\texp=1$, then $\rho_N\sim D_N\frac{2\sqrt\pi}\alpha\,N^{\alpha/2}/\log N$;
hence $\rho_N\log N\to\pi^{3/2}(2-\alpha)/(\alpha(1-\alpha))$ for $0<\alpha<1$,
$\rho_N\to\pi^{3/2}$ for $\alpha=1$, and $\rho_N\to\infty$ for $\alpha>1$, with order
$N^{\alpha-1}/\log N$, $N/\log^2N$ and $N^{\alpha/2}/\log N$ for $1<\alpha<2$,
$\alpha=2$ and $\alpha>2$;
-/
theorem thm_app_phase_accfirst_ii {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς = 1) :
    IsEquivalent atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => phaseDN α N * (2 * Real.sqrt Real.pi / α) * (N : ℝ) ^ (α / 2) /
        Real.log (N : ℝ)) := by
  subst ς
  have hr : rq (α + 1) α = 1 / 2 := by
    unfold rq
    field_simp
    ring
  have he : α * (1 - rq (α + 1) α) = α / 2 := by rw [hr]; ring
  have hA := pB_power_equiv hp hα (by rw [hr]; norm_num)
  rw [he, prop_app_phase_forcing_r_iv_J hα] at hA
  have hB := pB_critical_equiv (p := α + 1) (q := α / 2) (by linarith) (by ring)
  have h := (IsEquivalent.refl (u := fun N : ℕ => phaseDN α N)).mul (hA.div hB)
  change IsEquivalent atTop (fun N : ℕ => phaseDN α N *
    (JN N (α + 1) α / JN N (α + 1) (α / 2))) _ at h
  have h' : IsEquivalent atTop (fun N : ℕ => phaseRhoN α 1 N)
      (fun N : ℕ => phaseDN α N *
        ((1 / 2 * Real.sqrt (Real.pi / α) * (N : ℝ) ^ (α / 2)) /
          (aQ (α / 2) * (α / 2) * Real.log (N : ℝ)))) := by
    convert h using 1
    funext N
    simp only [phaseRhoN]
    ring
  apply h'.congr_right
  filter_upwards [] with N
  have hc := pB_coefficient hα
  calc phaseDN α N * (1 / 2 * Real.sqrt (Real.pi / α) * (N : ℝ) ^ (α / 2) /
        (aQ (α / 2) * (α / 2) * Real.log (N : ℝ)))
      = phaseDN α N * ((1 / 2 * Real.sqrt (Real.pi / α)) /
        (aQ (α / 2) * (α / 2))) * (N : ℝ) ^ (α / 2) / Real.log (N : ℝ) := by ring
    _ = _ := by rw [hc]

/-! ### Proved helpers for `thm:app-phase-accfirst` part (b) (task P-H.13.P6) -/

private lemma pE_pi32 : Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos, Real.rpow_one,
    Real.sqrt_eq_rpow]

private lemma pE_hR1 : Tendsto (fun N : ℕ => Hsum 1 N / Real.log (N : ℝ)) atTop (𝓝 1) := by
  have hz : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    exact (Real.log_pos hN1).ne'
  exact (isEquivalent_iff_tendsto_one hz).mp lem_app_phase_harmonic_iv

private lemma pE_H1_lt : ∀ᶠ N : ℕ in atTop, Hsum 1 N < 2 * Real.log (N : ℝ) := by
  have hlt := pE_hR1.eventually_lt_const (by norm_num : (1 : ℝ) < 2)
  filter_upwards [hlt, eventually_ge_atTop 2] with N h1 hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  exact (div_lt_iff₀ (Real.log_pos hN1)).mp h1

private lemma pE_H_ge_one (a : ℝ) {N : ℕ} (hN : 1 ≤ N) : 1 ≤ Hsum a N := by
  have h := Finset.single_le_sum (f := fun i : ℕ => (i : ℝ) ^ (-a))
    (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _) (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)
  simpa [Hsum] using h

private lemma pE_Hmono {a : ℝ} (ha : 1 ≤ a) (N : ℕ) : Hsum a N ≤ Hsum 1 N := by
  unfold Hsum
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi.1
  exact Real.rpow_le_rpow_of_exponent_le hi1 (by linarith)

private lemma pE_DN_scaled {α : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    phaseDN α N * (N : ℝ) ^ (α / 2) / (N : ℝ) ^ (α - 1) =
      Real.pi * Hsum α N / (Hsum (α / 2) N / (N : ℝ) ^ (1 - α / 2)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have he : (N : ℝ) ^ (α / 2) = (N : ℝ) ^ (α - 1) * (N : ℝ) ^ (1 - α / 2) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have h1 : (N : ℝ) ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
  have h2 : (N : ℝ) ^ (1 - α / 2) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
  have h3 : Hsum (α / 2) N ≠ 0 := (pA_Hsum_pos hN).ne'
  unfold phaseDN
  rw [he]
  field_simp

private lemma pE_scaled_lim {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    Tendsto (fun N : ℕ => phaseDN α N * (N : ℝ) ^ (α / 2) / (N : ℝ) ^ (α - 1)) atTop
      (𝓝 (Real.pi * zetaR α / (1 - α / 2)⁻¹)) := by
  have hZ := pA_zeta_lim hα1
  have hH := pA_harm_lim (a := α / 2) (by linarith) (by linarith)
  have hne : (1 - α / 2)⁻¹ ≠ 0 := (inv_pos.mpr (by linarith)).ne'
  have hL := (hZ.const_mul Real.pi).div hH hne
  refine Tendsto.congr' ?_ hL
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (pE_DN_scaled hN).symm

private lemma pE_pow_log {α : ℝ} (hα : 1 < α) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (α - 1) / Real.log (N : ℝ)) atTop atTop := by
  have ho : (fun x : ℝ => Real.log x) =o[atTop] fun x : ℝ => x ^ (α - 1) :=
    isLittleO_log_rpow_atTop (by linarith)
  have h0 : Tendsto (fun x : ℝ => Real.log x / x ^ (α - 1)) atTop (𝓝 0) :=
    ho.tendsto_div_nhds_zero
  have h0' : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ) ^ (α - 1)) atTop (𝓝 0) :=
    h0.comp tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) / (N : ℝ) ^ (α - 1) ∈ Ioi (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    exact div_pos (Real.log_pos hN1) (Real.rpow_pos_of_pos (by linarith) _)
  have h1 := Filter.Tendsto.inv_tendsto_nhdsGT_zero (tendsto_nhdsWithin_iff.mpr ⟨h0', hpos⟩)
  refine h1.congr (fun N => ?_)
  simp only [Pi.inv_apply, inv_div]

private lemma pE_big {r : ℝ} (hr : 0 < r) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ r / (Real.log (N : ℝ)) ^ 2) atTop atTop := by
  have ho : (fun x : ℝ => Real.log x ^ (2 : ℝ)) =o[atTop] fun x : ℝ => x ^ r :=
    isLittleO_log_rpow_rpow_atTop 2 hr
  have h0 : Tendsto (fun x : ℝ => Real.log x ^ (2 : ℝ) / x ^ r) atTop (𝓝 0) :=
    ho.tendsto_div_nhds_zero
  have h0' : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (2 : ℝ) / (N : ℝ) ^ r) atTop (𝓝 0) :=
    h0.comp tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ (2 : ℝ) / (N : ℝ) ^ r ∈ Ioi (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have hNpos : (0 : ℝ) < N := by linarith
    exact div_pos (Real.rpow_pos_of_pos (Real.log_pos hN1) _)
      (Real.rpow_pos_of_pos hNpos _)
  have h1 := Filter.Tendsto.inv_tendsto_nhdsGT_zero (tendsto_nhdsWithin_iff.mpr ⟨h0', hpos⟩)
  refine h1.congr (fun N => ?_)
  simp only [Pi.inv_apply, inv_div, Real.rpow_two]

/-- Label `thm:app-phase-accfirst`, part (b), limit `ρ_N log N → π^{3/2}(2-α)/(α(1-α))` for
`0 < α < 1`, snapshot `cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1652–1656).
Verbatim:
\item if $\texp=1$, then $\rho_N\sim D_N\frac{2\sqrt\pi}\alpha\,N^{\alpha/2}/\log N$;
hence $\rho_N\log N\to\pi^{3/2}(2-\alpha)/(\alpha(1-\alpha))$ for $0<\alpha<1$,
$\rho_N\to\pi^{3/2}$ for $\alpha=1$, and $\rho_N\to\infty$ for $\alpha>1$, with order
$N^{\alpha-1}/\log N$, $N/\log^2N$ and $N^{\alpha/2}/\log N$ for $1<\alpha<2$,
$\alpha=2$ and $\alpha>2$;
-/
theorem thm_app_phase_accfirst_ii_lt1 {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς = 1)
    (hα1 : α < 1) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N * Real.log (N : ℝ)) atTop
      (𝓝 (Real.pi ^ (3 / 2 : ℝ) * (2 - α) / (α * (1 - α)))) := by
  have hII := thm_app_phase_accfirst_ii hα hp hς
  subst hς
  have hD := pA_DN_lim hα hα1
  have h1 : (1 - α) ≠ 0 := (by linarith : (0 : ℝ) < 1 - α).ne'
  have h2 : α ≠ 0 := hα.ne'
  have hc : Real.pi * ((1 - α)⁻¹ / (1 - α / 2)⁻¹) * (2 * Real.sqrt Real.pi / α)
      = Real.pi ^ (3 / 2 : ℝ) * (2 - α) / (α * (1 - α)) := by
    rw [pE_pi32, div_inv_eq_mul]
    field_simp
  have hV : Tendsto (fun N : ℕ => phaseDN α N * (2 * Real.sqrt Real.pi / α) * (N : ℝ) ^ (α / 2)
      / Real.log (N : ℝ) * Real.log (N : ℝ)) atTop
      (𝓝 (Real.pi ^ (3 / 2 : ℝ) * (2 - α) / (α * (1 - α)))) := by
    rw [← hc]
    refine Tendsto.congr' ?_ (hD.mul_const (2 * Real.sqrt Real.pi / α))
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hN1).ne'
    rw [div_mul_cancel₀ _ hlog]
    ring
  have hmul := hII.mul (IsEquivalent.refl (u := fun N : ℕ => Real.log (N : ℝ)))
  exact hmul.symm.tendsto_nhds hV

/-- Label `thm:app-phase-accfirst`, part (b), limit `ρ_N → π^{3/2}` for `α = 1`, snapshot
`cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1652–1656). Verbatim:
\item if $\texp=1$, then $\rho_N\sim D_N\frac{2\sqrt\pi}\alpha\,N^{\alpha/2}/\log N$;
hence $\rho_N\log N\to\pi^{3/2}(2-\alpha)/(\alpha(1-\alpha))$ for $0<\alpha<1$,
$\rho_N\to\pi^{3/2}$ for $\alpha=1$, and $\rho_N\to\infty$ for $\alpha>1$, with order
$N^{\alpha-1}/\log N$, $N/\log^2N$ and $N^{\alpha/2}/\log N$ for $1<\alpha<2$,
$\alpha=2$ and $\alpha>2$;
-/
theorem thm_app_phase_accfirst_ii_one {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς = 1)
    (hα1 : α = 1) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop (𝓝 (Real.pi ^ (3 / 2 : ℝ))) := by
  have hII := thm_app_phase_accfirst_ii hα hp hς
  subst hα1 hς
  have hV : Tendsto (fun N : ℕ => phaseDN 1 N * (2 * Real.sqrt Real.pi / 1) *
      (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ)) atTop (𝓝 (Real.pi ^ (3 / 2 : ℝ))) := by
    have hH := pA_harm_lim (a := (1 : ℝ) / 2) (by norm_num) (by norm_num)
    have hne : (1 - (1 : ℝ) / 2)⁻¹ ≠ 0 := by norm_num
    have hQ := (pE_hR1.div hH hne).const_mul (2 * Real.sqrt Real.pi * Real.pi)
    have hlim : 2 * Real.sqrt Real.pi * Real.pi * (1 / (1 - (1 : ℝ) / 2)⁻¹)
        = Real.pi ^ (3 / 2 : ℝ) := by
      have h2 : (1 - (1 : ℝ) / 2)⁻¹ = 2 := by norm_num
      rw [pE_pi32, h2]
      ring
    rw [← hlim]
    refine Tendsto.congr' ?_ hQ
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hN1).ne'
    have hNpos : (0 : ℝ) < N := by linarith
    have hH0 : Hsum (1 / 2) N ≠ 0 := (pA_Hsum_pos (by omega : 1 ≤ N)).ne'
    have hpow : (N : ℝ) ^ ((1 : ℝ) / 2) = (N : ℝ) ^ (1 - (1 : ℝ) / 2) := by norm_num
    have hpow0 : (N : ℝ) ^ (1 - (1 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
    simp only [Pi.div_apply]
    unfold phaseDN
    rw [hpow]
    field_simp
  exact hII.symm.tendsto_nhds hV

/-- Label `thm:app-phase-accfirst`, part (b), `ρ_N → ∞` for `α > 1`, snapshot `cr-2026-10-23`.
Source: `section.tex` l.1644–1672 (item l.1652–1656). Verbatim:
\item if $\texp=1$, then $\rho_N\sim D_N\frac{2\sqrt\pi}\alpha\,N^{\alpha/2}/\log N$;
hence $\rho_N\log N\to\pi^{3/2}(2-\alpha)/(\alpha(1-\alpha))$ for $0<\alpha<1$,
$\rho_N\to\pi^{3/2}$ for $\alpha=1$, and $\rho_N\to\infty$ for $\alpha>1$, with order
$N^{\alpha-1}/\log N$, $N/\log^2N$ and $N^{\alpha/2}/\log N$ for $1<\alpha<2$,
$\alpha=2$ and $\alpha>2$;
-/
theorem thm_app_phase_accfirst_ii_top {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς = 1)
    (hα1 : 1 < α) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop atTop := by
  have hII := thm_app_phase_accfirst_ii hα hp hς
  subst hς
  refine hII.symm.tendsto_atTop ?_
  rcases lt_or_ge α 2 with h2 | h2
  · have hX := pE_scaled_lim hα1 h2
    have hW := pE_pow_log hα1
    have hL : 0 < 2 * Real.sqrt Real.pi / α * (Real.pi * zetaR α / (1 - α / 2)⁻¹) := by
      have hz := pA_zeta_pos hα1
      have hq : 0 < (1 - α / 2)⁻¹ := inv_pos.mpr (by linarith)
      have hc : 0 < 2 * Real.sqrt Real.pi / α :=
        div_pos (mul_pos two_pos (Real.sqrt_pos.mpr Real.pi_pos)) hα
      exact mul_pos hc (div_pos (mul_pos Real.pi_pos hz) hq)
    have hP := Filter.Tendsto.pos_mul_atTop hL (hX.const_mul (2 * Real.sqrt Real.pi / α)) hW
    refine Tendsto.congr' ?_ hP
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hN1).ne'
    have hNpos : (0 : ℝ) < N := by linarith
    have hpow : (N : ℝ) ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
    field_simp
  · have hbig := pE_big (r := α / 2) (by linarith)
    have hK : 0 < Real.pi * Real.sqrt Real.pi / α :=
      div_pos (mul_pos Real.pi_pos (Real.sqrt_pos.mpr Real.pi_pos)) hα
    refine Filter.tendsto_atTop_mono' atTop ?_ (Filter.Tendsto.const_mul_atTop hK hbig)
    filter_upwards [pE_H1_lt, eventually_ge_atTop 2] with N h1 hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos hN1
    have hNpos : (0 : ℝ) < N := by linarith
    have hT : 0 ≤ (N : ℝ) ^ (α / 2) := Real.rpow_nonneg hNpos.le _
    have hHa : 1 ≤ Hsum α N := pE_H_ge_one α (by omega)
    have hHb : Hsum (α / 2) N ≤ 2 * Real.log (N : ℝ) :=
      le_trans (pE_Hmono (by linarith) N) h1.le
    have hHbpos : 0 < Hsum (α / 2) N := pA_Hsum_pos (by omega)
    have hD : Real.pi / (2 * Real.log (N : ℝ)) ≤ phaseDN α N := by
      unfold phaseDN
      rw [div_le_div_iff₀ (by linarith) hHbpos]
      nlinarith [mul_le_mul_of_nonneg_left hHb Real.pi_pos.le,
        mul_nonneg (mul_nonneg Real.pi_pos.le hL0.le) (sub_nonneg.mpr hHa)]
    have hc : 0 ≤ 2 * Real.sqrt Real.pi / α := div_nonneg (by positivity) hα.le
    have hmain := mul_le_mul_of_nonneg_right hD (div_nonneg (mul_nonneg hc hT) hL0.le)
    calc Real.pi * Real.sqrt Real.pi / α * ((N : ℝ) ^ (α / 2) / (Real.log (N : ℝ)) ^ 2)
        = Real.pi / (2 * Real.log (N : ℝ)) *
            (2 * Real.sqrt Real.pi / α * (N : ℝ) ^ (α / 2) / Real.log (N : ℝ)) := by
          field_simp
      _ ≤ phaseDN α N * (2 * Real.sqrt Real.pi / α * (N : ℝ) ^ (α / 2) / Real.log (N : ℝ)) :=
          hmain
      _ = phaseDN α N * (2 * Real.sqrt Real.pi / α) * (N : ℝ) ^ (α / 2) / Real.log (N : ℝ) := by
          ring

/-- Label `thm:app-phase-accfirst`, part (b), order `ρ_N ≍ N^{α-1}/log N` for `1 < α < 2`,
snapshot `cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1652–1656). Verbatim:
\item if $\texp=1$, then $\rho_N\sim D_N\frac{2\sqrt\pi}\alpha\,N^{\alpha/2}/\log N$;
hence $\rho_N\log N\to\pi^{3/2}(2-\alpha)/(\alpha(1-\alpha))$ for $0<\alpha<1$,
$\rho_N\to\pi^{3/2}$ for $\alpha=1$, and $\rho_N\to\infty$ for $\alpha>1$, with order
$N^{\alpha-1}/\log N$, $N/\log^2N$ and $N^{\alpha/2}/\log N$ for $1<\alpha<2$,
$\alpha=2$ and $\alpha>2$;
-/
theorem thm_app_phase_accfirst_ii_mid {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς = 1)
    (hα1 : 1 < α) (hα2 : α < 2) :
    IsTheta atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => (N : ℝ) ^ (α - 1) / Real.log (N : ℝ)) := by
  have hII := thm_app_phase_accfirst_ii hα hp hς
  subst hς
  have hX := pE_scaled_lim hα1 hα2
  have hz := pA_zeta_pos hα1
  have hq : 0 < (1 - α / 2)⁻¹ := inv_pos.mpr (by linarith)
  have hc : 0 < 2 * Real.sqrt Real.pi / α := div_pos (mul_pos two_pos (Real.sqrt_pos.mpr Real.pi_pos)) hα
  have hL : 0 < 2 * Real.sqrt Real.pi / α * (Real.pi * zetaR α / (1 - α / 2)⁻¹) :=
    mul_pos hc (div_pos (mul_pos Real.pi_pos hz) hq)
  have hR : Tendsto (fun N : ℕ => phaseDN α N * (2 * Real.sqrt Real.pi / α) *
      (N : ℝ) ^ (α / 2) / Real.log (N : ℝ) / ((N : ℝ) ^ (α - 1) / Real.log (N : ℝ))) atTop
      (𝓝 (2 * Real.sqrt Real.pi / α * (Real.pi * zetaR α / (1 - α / 2)⁻¹))) := by
    refine Tendsto.congr' ?_ (hX.const_mul (2 * Real.sqrt Real.pi / α))
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hN1).ne'
    have hNpos : (0 : ℝ) < N := by linarith
    have hpow : (N : ℝ) ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
    field_simp
  exact hII.isTheta.trans (isTheta_of_div_tendsto_nhds_ne_zero hR hL.ne').symm

/-- Label `thm:app-phase-accfirst`, part (b), order `ρ_N ≍ N/log²N` for `α = 2`, snapshot
`cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1652–1656). Verbatim:
\item if $\texp=1$, then $\rho_N\sim D_N\frac{2\sqrt\pi}\alpha\,N^{\alpha/2}/\log N$;
hence $\rho_N\log N\to\pi^{3/2}(2-\alpha)/(\alpha(1-\alpha))$ for $0<\alpha<1$,
$\rho_N\to\pi^{3/2}$ for $\alpha=1$, and $\rho_N\to\infty$ for $\alpha>1$, with order
$N^{\alpha-1}/\log N$, $N/\log^2N$ and $N^{\alpha/2}/\log N$ for $1<\alpha<2$,
$\alpha=2$ and $\alpha>2$;
-/
theorem thm_app_phase_accfirst_ii_two {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς = 1)
    (hα2 : α = 2) :
    IsTheta atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  have hII := thm_app_phase_accfirst_ii hα hp hς
  have hD := (prop_app_phase_prefactors_iv α hα).2.2.2.1 hα2
  subst α
  subst ς
  have hm := ((hD.mul (IsEquivalent.refl (u := fun _ : ℕ => Real.sqrt Real.pi))).mul
    (IsEquivalent.refl (u := fun N : ℕ => (N : ℝ)))).div
      (IsEquivalent.refl (u := fun N : ℕ => Real.log (N : ℝ)))
  have he : IsEquivalent atTop (fun N : ℕ => phaseRhoN 2 1 N)
      (fun N : ℕ => (Real.pi * zetaR 2 * Real.sqrt Real.pi) *
        ((N : ℝ) / Real.log (N : ℝ) ^ 2)) := by
    refine hII.trans ((hm.congr_left ?_).congr_right ?_)
    · filter_upwards [] with N
      norm_num
    · filter_upwards [eventually_ge_atTop 2] with N hN
      have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
      have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hN1).ne'
      simp only [Pi.div_apply, Pi.mul_apply]
      field_simp
  have hc : Real.pi * zetaR 2 * Real.sqrt Real.pi ≠ 0 := by
    exact (mul_pos (mul_pos Real.pi_pos (pA_zeta_pos (by norm_num)))
      (Real.sqrt_pos.mpr Real.pi_pos)).ne'
  exact he.isTheta.of_const_mul_right hc

/-- Label `thm:app-phase-accfirst`, part (b), order `ρ_N ≍ N^{α/2}/log N` for `α > 2`, snapshot
`cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1652–1656). Verbatim:
\item if $\texp=1$, then $\rho_N\sim D_N\frac{2\sqrt\pi}\alpha\,N^{\alpha/2}/\log N$;
hence $\rho_N\log N\to\pi^{3/2}(2-\alpha)/(\alpha(1-\alpha))$ for $0<\alpha<1$,
$\rho_N\to\pi^{3/2}$ for $\alpha=1$, and $\rho_N\to\infty$ for $\alpha>1$, with order
$N^{\alpha-1}/\log N$, $N/\log^2N$ and $N^{\alpha/2}/\log N$ for $1<\alpha<2$,
$\alpha=2$ and $\alpha>2$;
-/
theorem thm_app_phase_accfirst_ii_gt2 {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς = 1)
    (hα2 : 2 < α) :
    IsTheta atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => (N : ℝ) ^ (α / 2) / Real.log (N : ℝ)) := by
  have hII := thm_app_phase_accfirst_ii hα hp hς
  have hD := (prop_app_phase_prefactors_iv α hα).2.2.2.2 hα2
  subst ς
  have hm := ((hD.mul (IsEquivalent.refl (u := fun _ : ℕ => 2 * Real.sqrt Real.pi / α))).mul
    (IsEquivalent.refl (u := fun N : ℕ => (N : ℝ) ^ (α / 2)))).div
      (IsEquivalent.refl (u := fun N : ℕ => Real.log (N : ℝ)))
  have he : IsEquivalent atTop (fun N : ℕ => phaseRhoN α 1 N)
      (fun N : ℕ => (Real.pi * zetaR α / zetaR (α / 2) *
        (2 * Real.sqrt Real.pi / α)) *
          ((N : ℝ) ^ (α / 2) / Real.log (N : ℝ))) := by
    refine hII.trans ((hm.congr_left ?_).congr_right ?_)
    · filter_upwards [] with N
      rfl
    · filter_upwards [] with N
      simp only [Pi.div_apply, Pi.mul_apply]
      ring
  have hzα : 0 < zetaR α := pA_zeta_pos (by linarith)
  have hzα2 : 0 < zetaR (α / 2) := pA_zeta_pos (by linarith)
  have hc : Real.pi * zetaR α / zetaR (α / 2) *
      (2 * Real.sqrt Real.pi / α) ≠ 0 := by
    positivity
  exact he.isTheta.of_const_mul_right hc

private lemma pH_env {p q : ℝ} (hp : 1 < p) (hq : 0 < q) {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt (fNq ⊤ p q u) ≤ Cpq p q * (u + 1) ^ (-rq p q) := by
  have hL := lem_app_phase_sums_i hp hq ⊤ hu
  rw [add_comm 1 u] at hL
  have hdr : dAQ p q = 2 * rq p q := by unfold dAQ rq; field_simp
  have hX : ((u + 1) ^ (-rq p q)) ^ 2 = (u + 1) ^ (-dAQ p q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ u + 1), hdr]
    congr 1
    push_cast
    ring
  have hZa : 0 < Za p := by
    unfold Za
    have : 0 < 1 / (p - 1) := div_pos one_pos (by linarith)
    linarith
  have hE1 : (2 : ℝ) ^ dAQ p q * Za p ≤ Epq p q := by
    unfold Epq
    exact le_max_left _ _
  have hE0 : 0 ≤ Epq p q :=
    le_trans (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hZa.le) hE1
  have hf : fNq ⊤ p q u ≤ (Epq p q / 2) * ((u + 1) ^ (-rq p q)) ^ 2 := by
    rw [hX]
    unfold fNq
    have := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have hX0 : 0 ≤ (u + 1) ^ (-rq p q) := Real.rpow_nonneg (by linarith) _
  calc
    Real.sqrt (fNq ⊤ p q u) ≤
        Real.sqrt ((Epq p q / 2) * ((u + 1) ^ (-rq p q)) ^ 2) :=
      Real.sqrt_le_sqrt hf
    _ = Cpq p q * (u + 1) ^ (-rq p q) := by
      unfold Cpq
      rw [Real.sqrt_mul (by linarith), Real.sqrt_sq hX0]

private lemma pH_summable_ind {p : ℝ} (hp : 1 < p) :
    Summable (fun i : ℕ => if 0 < i then (i : ℝ) ^ (-p) else 0) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
      (Real.summable_nat_rpow.mpr (by linarith : -p < -1))
  · split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg i) _
    · exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (Nat.cast_nonneg i) _

private lemma pH_term_summable {p q u : ℝ} (hp : 1 < p) (hu : 0 ≤ u) :
    Summable (fun i : ℕ =>
      if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (pH_summable_ind hp)
  · split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _) (Real.exp_pos _).le
    · exact le_rfl
  · split_ifs
    · have hx : -(2 * u) * (i : ℝ) ^ (-q) ≤ 0 := by
        nlinarith [mul_nonneg hu (Real.rpow_nonneg (Nat.cast_nonneg i) (-q))]
      exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg i) _)
        (Real.exp_le_one_iff.mpr hx)
    · exact le_rfl

private lemma pH_inf_eq (p q u : ℝ) :
    fNq ⊤ p q u = (1 / 2) * ∑' i : ℕ,
      (if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) := by
  unfold fNq Lsum
  congr 1
  apply tsum_congr
  intro i
  simp

private lemma pH_cont_inf {p q : ℝ} (hp : 1 < p) :
    ContinuousOn (fun u : ℝ => fNq ⊤ p q u) (Ici 0) := by
  have hcon : ContinuousOn (fun u : ℝ => ∑' i : ℕ,
      (if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0))
      (Ici 0) := by
    refine continuousOn_tsum (f := fun (i : ℕ) (u : ℝ) =>
        if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0)
      (u := fun i : ℕ => if 0 < i then (i : ℝ) ^ (-p) else 0) (fun i => ?_)
      (pH_summable_ind hp) (fun n x hx => ?_)
    · by_cases h : 0 < i
      · simp only [h, if_true]
        exact (by fun_prop : Continuous (fun u : ℝ =>
          (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)))).continuousOn
      · simp only [h, if_false]
        exact continuousOn_const
    · have hx0 : 0 ≤ x := hx
      by_cases h : 0 < n
      · simp only [h, if_true]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          (Real.exp_pos _).le)]
        apply mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        apply Real.exp_le_one_iff.mpr
        nlinarith [mul_nonneg hx0 (Real.rpow_nonneg (Nat.cast_nonneg n) (-q))]
      · simp [h]
  have hfeq : (fun u : ℝ => fNq ⊤ p q u) = fun u : ℝ => (1 / 2) * ∑' i : ℕ,
      (if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) :=
    funext (fun u => pH_inf_eq p q u)
  rw [hfeq]
  exact continuousOn_const.mul hcon

private lemma pH_int_inf {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : 1 < rq p q) :
    IntegrableOn (fun u : ℝ => Real.sqrt (fNq ⊤ p q u)) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable (fun u : ℝ => Real.sqrt (fNq ⊤ p q u))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (((pH_cont_inf hp).sqrt).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  have hb : IntegrableOn (fun u : ℝ => Cpq p q * (u + 1) ^ (-rq p q)) (Ioi 0) :=
    Integrable.const_mul (integrableOn_add_rpow_Ioi_of_lt (a := -rq p q) (c := 0) (m := 1)
      (by linarith) (by norm_num)) _
  refine Integrable.mono' hb hmeas
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact pH_env hp hq (Set.mem_Ioi.mp hu).le

private lemma pH_finf_pos {p q : ℝ} (hp : 1 < p) {u : ℝ} (hu : 0 ≤ u) :
    0 < fNq ⊤ p q u := by
  rw [pH_inf_eq]
  have hs := pH_term_summable (q := q) hp hu
  have hnn : ∀ i : ℕ, 0 ≤
      (if 0 < i then (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) := by
    intro i
    split_ifs
    · positivity
    · exact le_rfl
  have h1 : 0 < (if 0 < (1 : ℕ) then ((1 : ℕ) : ℝ) ^ (-p) *
      Real.exp (-(2 * u) * ((1 : ℕ) : ℝ) ^ (-q)) else 0) := by
    simp only [Nat.zero_lt_one, if_true, Nat.cast_one, Real.one_rpow, mul_one, one_mul]
    exact Real.exp_pos _
  exact mul_pos (by norm_num) (hs.tsum_pos hnn 1 h1)

private lemma pH_Jpq_pos {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : 1 < rq p q) :
    0 < Jpq p q := by
  unfold Jpq
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have hsupp : Function.support (fun u => Real.sqrt (fNq ⊤ p q u)) ∩ Ioi 0 = Ioi 0 := by
      ext u
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_Ioi]
      constructor
      · exact fun h => h.2
      · intro hu
        refine ⟨(Real.sqrt_pos.2 (pH_finf_pos hp hu.le)).ne', hu⟩
    rw [hsupp, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · exact Filter.Eventually.of_forall fun u => Real.sqrt_nonneg _
  · exact pH_int_inf hp hq hr

private lemma pH_JN_tendsto {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : 1 < rq p q) :
    Tendsto (fun N : ℕ => JN N p q) atTop (𝓝 (Jpq p q)) := by
  have he : 0 < q * (rq p q - 1) := mul_pos hq (by linarith)
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(q * (rq p q - 1)))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop he).comp tendsto_natCast_atTop_atTop
  have hb := hpow.const_mul
    (1 / Real.sqrt (2 * (p - 1)) + Cpq p q / (rq p q - 1))
  have hb' : Tendsto (fun N : ℕ =>
      (1 / Real.sqrt (2 * (p - 1)) + Cpq p q / (rq p q - 1)) *
        (N : ℝ) ^ (-(q * (rq p q - 1)))) atTop (𝓝 0) := by
    simpa using hb
  have hd : Tendsto (fun N : ℕ => Jpq p q - JN N p q) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hb'
    · filter_upwards [eventually_ge_atTop 4] with N hN
      exact (lem_app_phase_clock_integral_rate hp hq hr N hN).1
    · filter_upwards [eventually_ge_atTop 4] with N hN
      exact (lem_app_phase_clock_integral_rate hp hq hr N hN).2
  have h := (tendsto_const_nhds (x := Jpq p q)).sub hd
  simpa using h

/-- Label `thm:app-phase-accfirst`, part (c), snapshot `cr-2026-10-23`. Source: `section.tex`
l.1644–1672 (item l.1657–1663). Verbatim:
\item if $1<\texp<\alpha+1$, then
\[
\rho_N\sim D_N\,\frac{\mathcal K(s/2)}{\sqrt{8\alpha}\,J(p,\alpha/2)}\,N^{(\alpha+1-\texp)/2} ;
\]
hence $\rho_N\to0$ for $0<\alpha\le1$, with order $N^{(1-\texp)/2}$ (times $\log N$
at $\alpha=1$); $\rho_N\asymp N^{(2\alpha-1-\texp)/2}$ for $1<\alpha<2$, and on the
chord $\texp=2\alpha-1$, $\rho_N\to K_c$; and $\rho_N\to\infty$ for $\alpha\ge2$;
-/
theorem thm_app_phase_accfirst_iii {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς1 : 1 < ς)
    (hς2 : ς < α + 1) :
    IsEquivalent atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => phaseDN α N * phaseKr (phaseS α ς / 2) /
        (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2)) * (N : ℝ) ^ ((α + 1 - ς) / 2)) := by
  have hrA : rq (α + ς) α < 1 := by
    unfold rq
    rw [div_lt_one (by linarith : 0 < 2 * α)]
    linarith
  have hrB : 1 < rq (α + ς) (α / 2) := by
    unfold rq
    rw [one_lt_div (by linarith : 0 < 2 * (α / 2))]
    linarith
  have he : α * (1 - rq (α + ς) α) = (α + 1 - ς) / 2 := by
    unfold rq
    field_simp
    ring
  have hA := pB_power_equiv hp hα hrA
  rw [he] at hA
  have hJpos := pH_Jpq_pos hp (show (0 : ℝ) < α / 2 by linarith) hrB
  have hB : IsEquivalent atTop (fun N : ℕ => JN N (α + ς) (α / 2))
      (fun _ : ℕ => Jpq (α + ς) (α / 2)) :=
    (isEquivalent_const_iff_tendsto hJpos.ne').2
      (pH_JN_tendsto hp (show (0 : ℝ) < α / 2 by linarith) hrB)
  have h := (IsEquivalent.refl (u := fun N : ℕ => phaseDN α N)).mul (hA.div hB)
  have h' : IsEquivalent atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => phaseDN α N *
        ((phaseJcirc (α + ς) α * (N : ℝ) ^ ((α + 1 - ς) / 2)) /
          Jpq (α + ς) (α / 2))) := by
    convert h using 1 <;> funext N
    · simp only [phaseRhoN, Pi.mul_apply, Pi.div_apply]
      ring
  have hcirc : phaseJcirc (α + ς) α =
      phaseKr (phaseS α ς / 2) / Real.sqrt (8 * α) := by
    unfold phaseJcirc
    rw [pA_rq1, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
    ring
  refine h'.congr_right ?_
  filter_upwards [] with N
  rw [hcirc]
  ring

private lemma pP_iii_coefficient_pos {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς)
    (hς1 : 1 < ς) (hς2 : ς < α + 1) :
    0 < phaseKr (phaseS α ς / 2) /
      (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2)) := by
  have hrA : rq (α + ς) α < 1 := by
    unfold rq
    rw [div_lt_one (by linarith : 0 < 2 * α)]
    linarith
  have hrB : 1 < rq (α + ς) (α / 2) := by
    unfold rq
    rw [one_lt_div (by linarith : 0 < 2 * (α / 2))]
    linarith
  have hJC := (prop_app_phase_forcing_r_iii hp hα hrA).2.1
  have hsqrt : 0 < Real.sqrt (8 * α) := Real.sqrt_pos.mpr (by positivity)
  have hK : 0 < phaseKr (phaseS α ς / 2) := by
    rw [show phaseJcirc (α + ς) α =
        phaseKr (phaseS α ς / 2) / Real.sqrt (8 * α) by
      unfold phaseJcirc
      rw [pA_rq1, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
      ring] at hJC
    have h := mul_pos hJC hsqrt
    rwa [div_mul_cancel₀ _ hsqrt.ne'] at h
  have hJ := pH_Jpq_pos hp (show (0 : ℝ) < α / 2 by linarith) hrB
  exact div_pos hK (mul_pos hsqrt hJ)

private lemma pP_iii_lt1_theta {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς)
    (hς1 : 1 < ς) (hς2 : ς < α + 1) (hα1 : α < 1) :
    IsTheta atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => (N : ℝ) ^ ((1 - ς) / 2)) := by
  have hIII := thm_app_phase_accfirst_iii hα hp hς1 hς2
  have hD := (prop_app_phase_prefactors_iv α hα).1 hα1
  have hm := ((hD.mul (IsEquivalent.refl (u := fun _ : ℕ =>
      phaseKr (phaseS α ς / 2) /
        (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2))))).mul
    (IsEquivalent.refl (u := fun N : ℕ => (N : ℝ) ^ ((α + 1 - ς) / 2))))
  have he : IsEquivalent atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => (Real.pi * (1 - α / 2) / (1 - α) *
        (phaseKr (phaseS α ς / 2) /
          (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2)))) *
        (N : ℝ) ^ ((1 - ς) / 2)) := by
    refine hIII.trans ((hm.congr_left ?_).congr_right ?_)
    · filter_upwards [] with N
      simp only [Pi.mul_apply]
      ring
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      simp only [Pi.mul_apply]
      have hpow : (N : ℝ) ^ (-(α / 2)) * (N : ℝ) ^ ((α + 1 - ς) / 2) =
          (N : ℝ) ^ ((1 - ς) / 2) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      calc
        _ = (Real.pi * (1 - α / 2) / (1 - α) *
            (phaseKr (phaseS α ς / 2) /
              (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2)))) *
            ((N : ℝ) ^ (-(α / 2)) * (N : ℝ) ^ ((α + 1 - ς) / 2)) := by ring
        _ = _ := by rw [hpow]
  have hc : Real.pi * (1 - α / 2) / (1 - α) *
      (phaseKr (phaseS α ς / 2) /
        (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2))) ≠ 0 := by
    have hcoef := pP_iii_coefficient_pos hα hp hς1 hς2
    exact (mul_pos (div_pos (mul_pos Real.pi_pos (by linarith)) (by linarith)) hcoef).ne'
  exact he.isTheta.of_const_mul_right hc

private lemma pP_iii_one_theta {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς)
    (hς1 : 1 < ς) (hς2 : ς < α + 1) (hα1 : α = 1) :
    IsTheta atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => (N : ℝ) ^ ((1 - ς) / 2) * Real.log (N : ℝ)) := by
  have hIII := thm_app_phase_accfirst_iii hα hp hς1 hς2
  have hD := (prop_app_phase_prefactors_iv α hα).2.1 hα1
  have hm := ((hD.mul (IsEquivalent.refl (u := fun _ : ℕ =>
      phaseKr (phaseS α ς / 2) /
        (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2))))).mul
    (IsEquivalent.refl (u := fun N : ℕ => (N : ℝ) ^ ((α + 1 - ς) / 2))))
  have he : IsEquivalent atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => (Real.pi / 2 *
        (phaseKr (phaseS α ς / 2) /
          (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2)))) *
        ((N : ℝ) ^ ((1 - ς) / 2) * Real.log (N : ℝ))) := by
    refine hIII.trans ((hm.congr_left ?_).congr_right ?_)
    · filter_upwards [] with N
      simp only [Pi.mul_apply]
      ring
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      simp only [Pi.mul_apply, hα1]
      have hpow : (N : ℝ) ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ ((1 + 1 - ς) / 2) =
          (N : ℝ) ^ ((1 - ς) / 2) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      calc
        _ = (Real.pi / 2 *
            (phaseKr (phaseS 1 ς / 2) /
              (Real.sqrt (8 * 1) * Jpq (1 + ς) (1 / 2)))) *
            ((N : ℝ) ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ ((1 + 1 - ς) / 2)) *
              Real.log (N : ℝ) := by ring
        _ = _ := by rw [hpow]; ring
  have hc : Real.pi / 2 *
      (phaseKr (phaseS α ς / 2) /
        (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2))) ≠ 0 := by
    have hcoef := pP_iii_coefficient_pos hα hp hς1 hς2
    exact (mul_pos (div_pos Real.pi_pos two_pos) hcoef).ne'
  exact he.isTheta.of_const_mul_right hc

private lemma pP_iii_mid_theta {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς)
    (hς1 : 1 < ς) (hς2 : ς < α + 1) (hα1 : 1 < α) (hα2 : α < 2) :
    IsTheta atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => (N : ℝ) ^ ((2 * α - 1 - ς) / 2)) := by
  have hIII := thm_app_phase_accfirst_iii hα hp hς1 hς2
  have hD := (prop_app_phase_prefactors_iv α hα).2.2.1 hα1 hα2
  have hm := ((hD.mul (IsEquivalent.refl (u := fun _ : ℕ =>
      phaseKr (phaseS α ς / 2) /
        (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2))))).mul
    (IsEquivalent.refl (u := fun N : ℕ => (N : ℝ) ^ ((α + 1 - ς) / 2))))
  have he : IsEquivalent atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => (Real.pi * (1 - α / 2) * zetaR α *
        (phaseKr (phaseS α ς / 2) /
          (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2)))) *
        (N : ℝ) ^ ((2 * α - 1 - ς) / 2)) := by
    refine hIII.trans ((hm.congr_left ?_).congr_right ?_)
    · filter_upwards [] with N
      simp only [Pi.mul_apply]
      ring
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      simp only [Pi.mul_apply]
      have hpow : (N : ℝ) ^ (α / 2 - 1) * (N : ℝ) ^ ((α + 1 - ς) / 2) =
          (N : ℝ) ^ ((2 * α - 1 - ς) / 2) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      calc
        _ = (Real.pi * (1 - α / 2) * zetaR α *
            (phaseKr (phaseS α ς / 2) /
              (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2)))) *
            ((N : ℝ) ^ (α / 2 - 1) * (N : ℝ) ^ ((α + 1 - ς) / 2)) := by ring
        _ = _ := by rw [hpow]
  have hc : Real.pi * (1 - α / 2) * zetaR α *
      (phaseKr (phaseS α ς / 2) /
        (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2))) ≠ 0 := by
    have hcoef := pP_iii_coefficient_pos hα hp hς1 hς2
    have hz := pA_zeta_pos hα1
    exact (mul_pos (mul_pos (mul_pos Real.pi_pos (by linarith)) hz) hcoef).ne'
  exact he.isTheta.of_const_mul_right hc

private lemma pP_rpow_log_tendsto_zero {ς : ℝ} (hς : 1 < ς) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 - ς) / 2) * Real.log (N : ℝ)) atTop (𝓝 0) := by
  have hr : 0 < (ς - 1) / 2 := by linarith
  have hlim := ((isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  change Real.log (N : ℝ) / (N : ℝ) ^ ((ς - 1) / 2) =
    (N : ℝ) ^ ((1 - ς) / 2) * Real.log (N : ℝ)
  rw [show (1 - ς) / 2 = -((ς - 1) / 2) by ring, Real.rpow_neg hNpos.le]
  ring

/-- Label `thm:app-phase-accfirst`, part (c), `ρ_N → 0` for `0 < α ≤ 1`, snapshot
`cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1657–1663). Verbatim:
\item if $1<\texp<\alpha+1$, then
\[
\rho_N\sim D_N\,\frac{\mathcal K(s/2)}{\sqrt{8\alpha}\,J(p,\alpha/2)}\,N^{(\alpha+1-\texp)/2} ;
\]
hence $\rho_N\to0$ for $0<\alpha\le1$, with order $N^{(1-\texp)/2}$ (times $\log N$
at $\alpha=1$); $\rho_N\asymp N^{(2\alpha-1-\texp)/2}$ for $1<\alpha<2$, and on the
chord $\texp=2\alpha-1$, $\rho_N\to K_c$; and $\rho_N\to\infty$ for $\alpha\ge2$;
-/
theorem thm_app_phase_accfirst_iii_zero {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς1 : 1 < ς)
    (hς2 : ς < α + 1) (hα1 : α ≤ 1) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop (𝓝 0) := by
  rcases hα1.lt_or_eq with hα1 | hα1
  · apply (pP_iii_lt1_theta hα hp hς1 hς2 hα1).tendsto_zero_iff.mpr
    have hr : 0 < (ς - 1) / 2 := by linarith
    have hg : Tendsto (fun N : ℕ => (N : ℝ) ^ (-((ς - 1) / 2))) atTop (𝓝 0) := by
      change Tendsto ((fun x : ℝ => x ^ (-((ς - 1) / 2))) ∘ fun N : ℕ => (N : ℝ))
        atTop (𝓝 0)
      exact (tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop
    simpa only [show (1 - ς) / 2 = -((ς - 1) / 2) by ring] using hg
  · exact (pP_iii_one_theta hα hp hς1 hς2 hα1).tendsto_zero_iff.mpr
      (pP_rpow_log_tendsto_zero hς1)

/-- Label `thm:app-phase-accfirst`, part (c), order `ρ_N ≍ N^{(1-ς)/2}` for `0 < α < 1`,
snapshot `cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1657–1663). Verbatim:
\item if $1<\texp<\alpha+1$, then
\[
\rho_N\sim D_N\,\frac{\mathcal K(s/2)}{\sqrt{8\alpha}\,J(p,\alpha/2)}\,N^{(\alpha+1-\texp)/2} ;
\]
hence $\rho_N\to0$ for $0<\alpha\le1$, with order $N^{(1-\texp)/2}$ (times $\log N$
at $\alpha=1$); $\rho_N\asymp N^{(2\alpha-1-\texp)/2}$ for $1<\alpha<2$, and on the
chord $\texp=2\alpha-1$, $\rho_N\to K_c$; and $\rho_N\to\infty$ for $\alpha\ge2$;
-/
theorem thm_app_phase_accfirst_iii_lt1 {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς1 : 1 < ς)
    (hς2 : ς < α + 1) (hα1 : α < 1) :
    IsTheta atTop (fun N : ℕ => phaseRhoN α ς N) (fun N : ℕ => (N : ℝ) ^ ((1 - ς) / 2)) := by
  exact pP_iii_lt1_theta hα hp hς1 hς2 hα1

/-- Label `thm:app-phase-accfirst`, part (c), order `ρ_N ≍ N^{(1-ς)/2} log N` for `α = 1`,
snapshot `cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1657–1663). Verbatim:
\item if $1<\texp<\alpha+1$, then
\[
\rho_N\sim D_N\,\frac{\mathcal K(s/2)}{\sqrt{8\alpha}\,J(p,\alpha/2)}\,N^{(\alpha+1-\texp)/2} ;
\]
hence $\rho_N\to0$ for $0<\alpha\le1$, with order $N^{(1-\texp)/2}$ (times $\log N$
at $\alpha=1$); $\rho_N\asymp N^{(2\alpha-1-\texp)/2}$ for $1<\alpha<2$, and on the
chord $\texp=2\alpha-1$, $\rho_N\to K_c$; and $\rho_N\to\infty$ for $\alpha\ge2$;
-/
theorem thm_app_phase_accfirst_iii_one {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς1 : 1 < ς)
    (hς2 : ς < α + 1) (hα1 : α = 1) :
    IsTheta atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => (N : ℝ) ^ ((1 - ς) / 2) * Real.log (N : ℝ)) := by
  exact pP_iii_one_theta hα hp hς1 hς2 hα1

/-- Label `thm:app-phase-accfirst`, part (c), order `ρ_N ≍ N^{(2α-1-ς)/2}` for `1 < α < 2`,
snapshot `cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1657–1663). Verbatim:
\item if $1<\texp<\alpha+1$, then
\[
\rho_N\sim D_N\,\frac{\mathcal K(s/2)}{\sqrt{8\alpha}\,J(p,\alpha/2)}\,N^{(\alpha+1-\texp)/2} ;
\]
hence $\rho_N\to0$ for $0<\alpha\le1$, with order $N^{(1-\texp)/2}$ (times $\log N$
at $\alpha=1$); $\rho_N\asymp N^{(2\alpha-1-\texp)/2}$ for $1<\alpha<2$, and on the
chord $\texp=2\alpha-1$, $\rho_N\to K_c$; and $\rho_N\to\infty$ for $\alpha\ge2$;
-/
theorem thm_app_phase_accfirst_iii_mid {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς1 : 1 < ς)
    (hς2 : ς < α + 1) (hα1 : 1 < α) (hα2 : α < 2) :
    IsTheta atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => (N : ℝ) ^ ((2 * α - 1 - ς) / 2)) := by
  exact pP_iii_mid_theta hα hp hς1 hς2 hα1 hα2

/-- Label `thm:app-phase-accfirst`, part (c), chord `ς = 2α-1`: `ρ_N → K_c` for `1 < α < 2`,
snapshot `cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1657–1663). Verbatim:
\item if $1<\texp<\alpha+1$, then
\[
\rho_N\sim D_N\,\frac{\mathcal K(s/2)}{\sqrt{8\alpha}\,J(p,\alpha/2)}\,N^{(\alpha+1-\texp)/2} ;
\]
hence $\rho_N\to0$ for $0<\alpha\le1$, with order $N^{(1-\texp)/2}$ (times $\log N$
at $\alpha=1$); $\rho_N\asymp N^{(2\alpha-1-\texp)/2}$ for $1<\alpha<2$, and on the
chord $\texp=2\alpha-1$, $\rho_N\to K_c$; and $\rho_N\to\infty$ for $\alpha\ge2$;
-/
theorem thm_app_phase_accfirst_iii_chord {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς1 : 1 < ς)
    (hς2 : ς < α + 1) (hα1 : 1 < α) (hα2 : α < 2) (hς : ς = 2 * α - 1) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop (𝓝 (phaseKc α)) := by
  subst ς
  have hIII := thm_app_phase_accfirst_iii hα hp hς1 hς2
  have hD := (prop_app_phase_prefactors_iv α hα).2.2.1 hα1 hα2
  have hm := ((hD.mul (IsEquivalent.refl (u := fun _ : ℕ =>
      phaseKr (phaseS α (2 * α - 1) / 2) /
        (Real.sqrt (8 * α) * Jpq (α + (2 * α - 1)) (α / 2))))).mul
    (IsEquivalent.refl (u := fun N : ℕ => (N : ℝ) ^ ((α + 1 - (2 * α - 1)) / 2))))
  have he : IsEquivalent atTop (fun N : ℕ => phaseRhoN α (2 * α - 1) N)
      (fun _ : ℕ => phaseKc α) := by
    refine hIII.trans ((hm.congr_left ?_).congr_right ?_)
    · filter_upwards [] with N
      simp only [Pi.mul_apply]
      ring
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hpow : (N : ℝ) ^ (α / 2 - 1) *
          (N : ℝ) ^ ((α + 1 - (2 * α - 1)) / 2) = 1 := by
        rw [← Real.rpow_add hNpos]
        convert Real.rpow_zero (N : ℝ) using 2 <;> ring
      have hs : phaseS α (2 * α - 1) / 2 = (3 * α - 2) / (2 * α) := by
        unfold phaseS
        field_simp
        ring
      have hp' : α + (2 * α - 1) = 3 * α - 1 := by ring
      simp only [Pi.mul_apply]
      calc
        Real.pi * (1 - α / 2) * zetaR α * (N : ℝ) ^ (α / 2 - 1) *
              (phaseKr (phaseS α (2 * α - 1) / 2) /
                (Real.sqrt (8 * α) * Jpq (α + (2 * α - 1)) (α / 2))) *
              (N : ℝ) ^ ((α + 1 - (2 * α - 1)) / 2)
            = Real.pi * (1 - α / 2) * zetaR α *
                (phaseKr (phaseS α (2 * α - 1) / 2) /
                  (Real.sqrt (8 * α) * Jpq (α + (2 * α - 1)) (α / 2))) *
                ((N : ℝ) ^ (α / 2 - 1) *
                  (N : ℝ) ^ ((α + 1 - (2 * α - 1)) / 2)) := by ring
        _ = Real.pi * (1 - α / 2) * zetaR α *
              (phaseKr (phaseS α (2 * α - 1) / 2) /
                (Real.sqrt (8 * α) * Jpq (α + (2 * α - 1)) (α / 2))) := by rw [hpow]; ring
        _ = phaseKc α := by rw [hs, hp']; unfold phaseKc; ring
  exact he.symm.tendsto_nhds tendsto_const_nhds

/-- Label `thm:app-phase-accfirst`, part (c), `ρ_N → ∞` for `α ≥ 2`, snapshot `cr-2026-10-23`.
Source: `section.tex` l.1644–1672 (item l.1657–1663). Verbatim:
\item if $1<\texp<\alpha+1$, then
\[
\rho_N\sim D_N\,\frac{\mathcal K(s/2)}{\sqrt{8\alpha}\,J(p,\alpha/2)}\,N^{(\alpha+1-\texp)/2} ;
\]
hence $\rho_N\to0$ for $0<\alpha\le1$, with order $N^{(1-\texp)/2}$ (times $\log N$
at $\alpha=1$); $\rho_N\asymp N^{(2\alpha-1-\texp)/2}$ for $1<\alpha<2$, and on the
chord $\texp=2\alpha-1$, $\rho_N\to K_c$; and $\rho_N\to\infty$ for $\alpha\ge2$;
-/
theorem thm_app_phase_accfirst_iii_top {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς1 : 1 < ς)
    (hς2 : ς < α + 1) (hα1 : 2 ≤ α) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop atTop := by
  have hIII := thm_app_phase_accfirst_iii hα hp hς1 hς2
  have hcoef := pP_iii_coefficient_pos hα hp hς1 hς2
  refine hIII.symm.tendsto_atTop ?_
  rcases eq_or_lt_of_le hα1 with hα2 | hα2
  · subst α
    have hD := (prop_app_phase_prefactors_iv 2 (by norm_num)).2.2.2.1 rfl
    have hm := ((hD.mul (IsEquivalent.refl (u := fun _ : ℕ =>
        phaseKr (phaseS 2 ς / 2) /
          (Real.sqrt (8 * 2) * Jpq (2 + ς) (2 / 2))))).mul
      (IsEquivalent.refl (u := fun N : ℕ => (N : ℝ) ^ ((2 + 1 - ς) / 2))))
    have he : IsEquivalent atTop
        (fun N : ℕ => phaseDN 2 N * phaseKr (phaseS 2 ς / 2) /
          (Real.sqrt (8 * 2) * Jpq (2 + ς) (2 / 2)) * (N : ℝ) ^ ((2 + 1 - ς) / 2))
        (fun N : ℕ => (Real.pi * zetaR 2 *
          (phaseKr (phaseS 2 ς / 2) /
            (Real.sqrt (8 * 2) * Jpq (2 + ς) (2 / 2)))) *
          ((N : ℝ) ^ ((3 - ς) / 2) / Real.log (N : ℝ))) := by
      refine (hm.congr_left ?_).congr_right ?_
      · filter_upwards [] with N
        simp only [Pi.mul_apply]
        ring
      · filter_upwards [] with N
        simp only [Pi.mul_apply, Pi.div_apply]
        ring
    have hpow0 := pE_pow_log (α := (5 - ς) / 2) (by linarith)
    have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ ((3 - ς) / 2) /
        Real.log (N : ℝ)) atTop atTop := by
      refine hpow0.congr' ?_
      filter_upwards [] with N
      congr 2
      ring
    have hc : 0 < Real.pi * zetaR 2 *
        (phaseKr (phaseS 2 ς / 2) /
          (Real.sqrt (8 * 2) * Jpq (2 + ς) (2 / 2))) := by
      have hz : 0 < zetaR 2 := pA_zeta_pos (by norm_num)
      exact mul_pos (mul_pos Real.pi_pos hz) hcoef
    exact he.symm.tendsto_atTop (Filter.Tendsto.const_mul_atTop hc hpow)
  · have hD := (prop_app_phase_prefactors_iv α hα).2.2.2.2 hα2
    have hm := ((hD.mul (IsEquivalent.refl (u := fun _ : ℕ =>
        phaseKr (phaseS α ς / 2) /
          (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2))))).mul
      (IsEquivalent.refl (u := fun N : ℕ => (N : ℝ) ^ ((α + 1 - ς) / 2))))
    have he : IsEquivalent atTop
        (fun N : ℕ => phaseDN α N * phaseKr (phaseS α ς / 2) /
          (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2)) * (N : ℝ) ^ ((α + 1 - ς) / 2))
        (fun N : ℕ => (Real.pi * zetaR α / zetaR (α / 2) *
          (phaseKr (phaseS α ς / 2) /
            (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2)))) *
          (N : ℝ) ^ ((α + 1 - ς) / 2)) := by
      refine (hm.congr_left ?_).congr_right ?_
      · filter_upwards [] with N
        simp only [Pi.mul_apply]
        ring
      · filter_upwards [] with N
        simp only [Pi.mul_apply]
    have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ ((α + 1 - ς) / 2)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    have hzα : 0 < zetaR α := pA_zeta_pos (by linarith)
    have hzα2 : 0 < zetaR (α / 2) := pA_zeta_pos (by linarith)
    have hc : 0 < Real.pi * zetaR α / zetaR (α / 2) *
        (phaseKr (phaseS α ς / 2) /
          (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2))) := by
      exact mul_pos (div_pos (mul_pos Real.pi_pos hzα) hzα2) hcoef
    exact he.symm.tendsto_atTop (Filter.Tendsto.const_mul_atTop hc hpow)

private lemma pP_critical_coefficient {α : ℝ} (hα : 0 < α) :
    aQ α * α = Real.sqrt (α / 8) := by
  have hsα : Real.sqrt α ≠ 0 := (Real.sqrt_pos.mpr hα).ne'
  have hs8 : Real.sqrt (8 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold aQ
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_div hα.le]
  field_simp
  nlinarith [Real.sq_sqrt hα.le]

/-- Label `thm:app-phase-accfirst`, part (d), snapshot `cr-2026-10-23`. Source: `section.tex`
l.1644–1672 (item l.1664–1666). Verbatim:
\item if $\texp=\alpha+1$, then $\rho_N\sim D_N\sqrt{\alpha/8}\,\log N/J(p,\alpha/2)$;
hence $\rho_N\to0$ for $0<\alpha<2$, $\rho_N\to\pi\zeta(2)/(2J(5,1))$ for
$\alpha=2$, and $\rho_N\to\infty$ with order $\log N$ for $\alpha>2$;
-/
theorem thm_app_phase_accfirst_iv {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς = α + 1) :
    IsEquivalent atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => phaseDN α N * Real.sqrt (α / 8) * Real.log (N : ℝ) / Jpq (α + ς) (α / 2)) := by
  subst ς
  have hcrit : α + (α + 1) = 2 * α + 1 := by ring
  have hrB : 1 < rq (α + (α + 1)) (α / 2) := by
    unfold rq
    rw [one_lt_div (by linarith : 0 < 2 * (α / 2))]
    linarith
  have hA := pB_critical_equiv (p := α + (α + 1)) (q := α) hα hcrit
  have hJpos := pH_Jpq_pos hp (show (0 : ℝ) < α / 2 by linarith) hrB
  have hB : IsEquivalent atTop (fun N : ℕ => JN N (α + (α + 1)) (α / 2))
      (fun _ : ℕ => Jpq (α + (α + 1)) (α / 2)) :=
    (isEquivalent_const_iff_tendsto hJpos.ne').2
      (pH_JN_tendsto hp (show (0 : ℝ) < α / 2 by linarith) hrB)
  have h := (IsEquivalent.refl (u := fun N : ℕ => phaseDN α N)).mul (hA.div hB)
  have h' : IsEquivalent atTop (fun N : ℕ => phaseRhoN α (α + 1) N)
      (fun N : ℕ => phaseDN α N *
        ((aQ α * α * Real.log (N : ℝ)) / Jpq (α + (α + 1)) (α / 2))) := by
    convert h using 1 <;> funext N
    · simp only [phaseRhoN, Pi.mul_apply, Pi.div_apply]
      ring
  refine h'.congr_right ?_
  filter_upwards [] with N
  rw [pP_critical_coefficient hα]
  ring

private lemma pP_DN_log_zero {α : ℝ} (hα : 0 < α) (hα2 : α < 2) :
    Tendsto (fun N : ℕ => phaseDN α N * Real.log (N : ℝ)) atTop (𝓝 0) := by
  rcases lt_trichotomy α 1 with hα1 | hα1 | hα1
  · have hD := (prop_app_phase_prefactors_iv α hα).1 hα1
    have hm := hD.mul (IsEquivalent.refl (u := fun N : ℕ => Real.log (N : ℝ)))
    have hz := (wh5_log_rpow_neg (α / 2) 0 (by linarith)).comp
      tendsto_natCast_atTop_atTop
    have hz' : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(α / 2)) * Real.log (N : ℝ))
        atTop (𝓝 0) := by
      refine hz.congr (fun N => ?_)
      change (N : ℝ) ^ (-(α / 2)) * (Real.log (N : ℝ) + 0) = _
      ring
    have hlim := hz'.const_mul (Real.pi * (1 - α / 2) / (1 - α))
    rw [mul_zero] at hlim
    refine hm.symm.tendsto_nhds (hlim.congr' ?_)
    filter_upwards [] with N
    simp only [Pi.mul_apply]
    ring
  · subst α
    have hD := (prop_app_phase_prefactors_iv 1 (by norm_num)).2.1 rfl
    have hm := hD.mul (IsEquivalent.refl (u := fun N : ℕ => Real.log (N : ℝ)))
    have hz := (wh5_log_rpow_neg (1 / 4) 0 (by norm_num)).comp
      tendsto_natCast_atTop_atTop
    have hz' : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 4 : ℝ)) * Real.log (N : ℝ))
        atTop (𝓝 0) := by
      refine hz.congr (fun N => ?_)
      change (N : ℝ) ^ (-(1 / 4 : ℝ)) * (Real.log (N : ℝ) + 0) = _
      ring
    have hz2 := hz'.mul hz'
    have hlim : Tendsto (fun N : ℕ => Real.pi / 2 *
        (((N : ℝ) ^ (-(1 / 4 : ℝ)) * Real.log (N : ℝ)) *
          ((N : ℝ) ^ (-(1 / 4 : ℝ)) * Real.log (N : ℝ)))) atTop (𝓝 0) := by
      simpa only [mul_zero] using hz2.const_mul (Real.pi / 2)
    refine hm.symm.tendsto_nhds (hlim.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hpow : (N : ℝ) ^ (-(1 / 4 : ℝ)) * (N : ℝ) ^ (-(1 / 4 : ℝ)) =
        (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    simp only [Pi.mul_apply]
    rw [← hpow]
    ring
  · have hD := (prop_app_phase_prefactors_iv α hα).2.2.1 hα1 hα2
    have hm := hD.mul (IsEquivalent.refl (u := fun N : ℕ => Real.log (N : ℝ)))
    have hz := (wh5_log_rpow_neg (1 - α / 2) 0 (by linarith)).comp
      tendsto_natCast_atTop_atTop
    have hz' : Tendsto (fun N : ℕ => (N : ℝ) ^ (α / 2 - 1) * Real.log (N : ℝ))
        atTop (𝓝 0) := by
      refine hz.congr (fun N => ?_)
      change (N : ℝ) ^ (-(1 - α / 2)) * (Real.log (N : ℝ) + 0) = _
      rw [show -(1 - α / 2) = α / 2 - 1 by ring, add_zero]
    have hlim := hz'.const_mul (Real.pi * (1 - α / 2) * zetaR α)
    rw [mul_zero] at hlim
    refine hm.symm.tendsto_nhds (hlim.congr' ?_)
    filter_upwards [] with N
    simp only [Pi.mul_apply]
    ring

/-- Label `thm:app-phase-accfirst`, part (d), `ρ_N → 0` for `0 < α < 2`, snapshot
`cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1664–1666). Verbatim:
\item if $\texp=\alpha+1$, then $\rho_N\sim D_N\sqrt{\alpha/8}\,\log N/J(p,\alpha/2)$;
hence $\rho_N\to0$ for $0<\alpha<2$, $\rho_N\to\pi\zeta(2)/(2J(5,1))$ for
$\alpha=2$, and $\rho_N\to\infty$ with order $\log N$ for $\alpha>2$;
-/
theorem thm_app_phase_accfirst_iv_zero {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς = α + 1)
    (hα1 : α < 2) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop (𝓝 0) := by
  have hIV := thm_app_phase_accfirst_iv hα hp hς
  have hz := (pP_DN_log_zero hα hα1).mul_const
    (Real.sqrt (α / 8) / Jpq (α + ς) (α / 2))
  rw [zero_mul] at hz
  refine hIV.symm.tendsto_nhds (hz.congr' ?_)
  filter_upwards [] with N
  ring

/-- Label `thm:app-phase-accfirst`, part (d), `ρ_N → π ζ(2)/(2 J(5,1))` for `α = 2`, snapshot
`cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1664–1666). Verbatim:
\item if $\texp=\alpha+1$, then $\rho_N\sim D_N\sqrt{\alpha/8}\,\log N/J(p,\alpha/2)$;
hence $\rho_N\to0$ for $0<\alpha<2$, $\rho_N\to\pi\zeta(2)/(2J(5,1))$ for
$\alpha=2$, and $\rho_N\to\infty$ with order $\log N$ for $\alpha>2$;
-/
theorem thm_app_phase_accfirst_iv_two {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς = α + 1)
    (hα2 : α = 2) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop (𝓝 (Real.pi * zetaR 2 / (2 * Jpq 5 1))) := by
  subst α
  norm_num at hς
  subst ς
  have hIV := thm_app_phase_accfirst_iv (α := (2 : ℝ)) (ς := (3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hD := (prop_app_phase_prefactors_iv 2 (by norm_num)).2.2.2.1 rfl
  have hm := hD.mul (IsEquivalent.refl (u := fun N : ℕ => Real.log (N : ℝ)))
  have he : IsEquivalent atTop (fun N : ℕ => phaseDN 2 N * Real.log (N : ℝ))
      (fun _ : ℕ => Real.pi * zetaR 2) := by
    refine hm.congr_right ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : Real.log (N : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by exact_mod_cast hN : (1 : ℝ) < N))
    simp only [Pi.mul_apply]
    field_simp
  have hlim : Tendsto (fun N : ℕ => phaseDN 2 N * Real.log (N : ℝ)) atTop
      (𝓝 (Real.pi * zetaR 2)) := he.symm.tendsto_nhds tendsto_const_nhds
  refine hIV.symm.tendsto_nhds ?_
  have hlim' := hlim.mul_const (Real.sqrt ((2 : ℝ) / 8) / Jpq 5 1)
  convert hlim' using 1
  · funext N
    ring
  · rw [show Real.sqrt ((2 : ℝ) / 8) = 1 / 2 by norm_num]
    ring

private lemma pP_iv_gt2_equiv {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς)
    (hς : ς = α + 1) (hα2 : 2 < α) :
    IsEquivalent atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => (Real.pi * zetaR α / zetaR (α / 2) * Real.sqrt (α / 8) /
        Jpq (α + ς) (α / 2)) * Real.log (N : ℝ)) := by
  have hIV := thm_app_phase_accfirst_iv hα hp hς
  have hD := (prop_app_phase_prefactors_iv α hα).2.2.2.2 hα2
  have hm := ((hD.mul (IsEquivalent.refl (u := fun _ : ℕ => Real.sqrt (α / 8)))).mul
    (IsEquivalent.refl (u := fun N : ℕ => Real.log (N : ℝ)))).div
      (IsEquivalent.refl (u := fun _ : ℕ => Jpq (α + ς) (α / 2)))
  refine hIV.trans ((hm.congr_left ?_).congr_right ?_)
  · filter_upwards [] with N
    simp only [Pi.mul_apply, Pi.div_apply]
  · filter_upwards [] with N
    simp only [Pi.mul_apply, Pi.div_apply]
    ring

/-- Label `thm:app-phase-accfirst`, part (d), order `ρ_N ≍ log N` for `α > 2`, snapshot
`cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1664–1666). Verbatim:
\item if $\texp=\alpha+1$, then $\rho_N\sim D_N\sqrt{\alpha/8}\,\log N/J(p,\alpha/2)$;
hence $\rho_N\to0$ for $0<\alpha<2$, $\rho_N\to\pi\zeta(2)/(2J(5,1))$ for
$\alpha=2$, and $\rho_N\to\infty$ with order $\log N$ for $\alpha>2$;
-/
theorem thm_app_phase_accfirst_iv_gt2 {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς = α + 1)
    (hα2 : 2 < α) :
    IsTheta atTop (fun N : ℕ => phaseRhoN α ς N) (fun N : ℕ => Real.log (N : ℝ)) := by
  have he := pP_iv_gt2_equiv hα hp hς hα2
  have hrB : 1 < rq (α + ς) (α / 2) := by
    unfold rq
    rw [one_lt_div (by linarith : 0 < 2 * (α / 2))]
    linarith
  have hJ := pH_Jpq_pos hp (show (0 : ℝ) < α / 2 by linarith) hrB
  have hzα : 0 < zetaR α := pA_zeta_pos (by linarith)
  have hzα2 : 0 < zetaR (α / 2) := pA_zeta_pos (by linarith)
  have hc : Real.pi * zetaR α / zetaR (α / 2) * Real.sqrt (α / 8) /
      Jpq (α + ς) (α / 2) ≠ 0 := by
    exact (div_pos (mul_pos (div_pos (mul_pos Real.pi_pos hzα) hzα2)
      (Real.sqrt_pos.mpr (by positivity))) hJ).ne'
  exact he.isTheta.of_const_mul_right hc

/-- Label `thm:app-phase-accfirst`, part (d), `ρ_N → ∞` for `α > 2`, snapshot `cr-2026-10-23`.
Source: `section.tex` l.1644–1672 (item l.1664–1666). Verbatim:
\item if $\texp=\alpha+1$, then $\rho_N\sim D_N\sqrt{\alpha/8}\,\log N/J(p,\alpha/2)$;
hence $\rho_N\to0$ for $0<\alpha<2$, $\rho_N\to\pi\zeta(2)/(2J(5,1))$ for
$\alpha=2$, and $\rho_N\to\infty$ with order $\log N$ for $\alpha>2$;
-/
theorem thm_app_phase_accfirst_iv_gt2_top {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς)
    (hς : ς = α + 1) (hα2 : 2 < α) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop atTop := by
  have he := pP_iv_gt2_equiv hα hp hς hα2
  have hrB : 1 < rq (α + ς) (α / 2) := by
    unfold rq
    rw [one_lt_div (by linarith : 0 < 2 * (α / 2))]
    linarith
  have hJ := pH_Jpq_pos hp (show (0 : ℝ) < α / 2 by linarith) hrB
  have hzα : 0 < zetaR α := pA_zeta_pos (by linarith)
  have hzα2 : 0 < zetaR (α / 2) := pA_zeta_pos (by linarith)
  have hc : 0 < Real.pi * zetaR α / zetaR (α / 2) * Real.sqrt (α / 8) /
      Jpq (α + ς) (α / 2) := by
    exact div_pos (mul_pos (div_pos (mul_pos Real.pi_pos hzα) hzα2)
      (Real.sqrt_pos.mpr (by positivity))) hJ
  exact he.symm.tendsto_atTop (Filter.Tendsto.const_mul_atTop hc
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

/-- Label `thm:app-phase-accfirst`, part (e), snapshot `cr-2026-10-23`. Source: `section.tex`
l.1644–1672 (item l.1667–1670). Verbatim:
\item if $\texp>\alpha+1$, then $\rho_N\sim D_NJ(p,\alpha)/J(p,\alpha/2)$; hence
$\rho_N\to0$ for $0<\alpha\le2$ (with order $1/\log N$ at $\alpha=2$), and
$\rho_N\to\pi\zeta(\alpha)J(p,\alpha)/(\zeta(\alpha/2)J(p,\alpha/2))\in(0,\infty)$
for $\alpha>2$.
-/
theorem thm_app_phase_accfirst_v {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : α + 1 < ς) :
    IsEquivalent atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => phaseDN α N * Jpq (α + ς) α / Jpq (α + ς) (α / 2)) := by
  have hrA : 1 < rq (α + ς) α := by
    unfold rq
    rw [one_lt_div (by linarith : 0 < 2 * α)]
    linarith
  have hrB : 1 < rq (α + ς) (α / 2) := by
    unfold rq
    rw [one_lt_div (by linarith : 0 < 2 * (α / 2))]
    linarith
  have hJA := pH_Jpq_pos hp hα hrA
  have hJB := pH_Jpq_pos hp (show (0 : ℝ) < α / 2 by linarith) hrB
  have hA : IsEquivalent atTop (fun N : ℕ => JN N (α + ς) α)
      (fun _ : ℕ => Jpq (α + ς) α) :=
    (isEquivalent_const_iff_tendsto hJA.ne').2 (pH_JN_tendsto hp hα hrA)
  have hB : IsEquivalent atTop (fun N : ℕ => JN N (α + ς) (α / 2))
      (fun _ : ℕ => Jpq (α + ς) (α / 2)) :=
    (isEquivalent_const_iff_tendsto hJB.ne').2
      (pH_JN_tendsto hp (show (0 : ℝ) < α / 2 by linarith) hrB)
  have h := (IsEquivalent.refl (u := fun N : ℕ => phaseDN α N)).mul (hA.div hB)
  convert h using 1 <;> funext N <;>
    simp only [phaseRhoN, Pi.mul_apply, Pi.div_apply] <;> ring

private lemma pQ_DN_zero {α : ℝ} (hα : 0 < α) (hα2 : α ≤ 2) :
    Tendsto (fun N : ℕ => phaseDN α N) atTop (𝓝 0) := by
  rcases lt_trichotomy α 1 with hα1 | hα1 | hα1
  · have hD := (prop_app_phase_prefactors_iv α hα).1 hα1
    have hz := (tendsto_rpow_neg_atTop (by linarith : 0 < α / 2)).comp
      tendsto_natCast_atTop_atTop
    have hlim := hz.const_mul (Real.pi * (1 - α / 2) / (1 - α))
    rw [mul_zero] at hlim
    exact hD.symm.tendsto_nhds hlim
  · subst α
    have hD := (prop_app_phase_prefactors_iv 1 (by norm_num)).2.1 rfl
    have hz := (wh5_log_rpow_neg (1 / 2) 0 (by norm_num)).comp
      tendsto_natCast_atTop_atTop
    have hlim := hz.const_mul (Real.pi / 2)
    rw [mul_zero] at hlim
    refine hD.symm.tendsto_nhds (hlim.congr' ?_)
    filter_upwards [] with N
    change Real.pi / 2 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (N : ℝ) + 0)) = _
    ring
  · exact wh5_DN_zero α hα1 hα2

/-- Label `thm:app-phase-accfirst`, part (e), `ρ_N → 0` for `0 < α ≤ 2`, snapshot
`cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1667–1670). Verbatim:
\item if $\texp>\alpha+1$, then $\rho_N\sim D_NJ(p,\alpha)/J(p,\alpha/2)$; hence
$\rho_N\to0$ for $0<\alpha\le2$ (with order $1/\log N$ at $\alpha=2$), and
$\rho_N\to\pi\zeta(\alpha)J(p,\alpha)/(\zeta(\alpha/2)J(p,\alpha/2))\in(0,\infty)$
for $\alpha>2$.
-/
theorem thm_app_phase_accfirst_v_zero {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : α + 1 < ς)
    (hα1 : α ≤ 2) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop (𝓝 0) := by
  have hV := thm_app_phase_accfirst_v hα hp hς
  have hz := (pQ_DN_zero hα hα1).mul_const
    (Jpq (α + ς) α / Jpq (α + ς) (α / 2))
  rw [zero_mul] at hz
  refine hV.symm.tendsto_nhds (hz.congr' ?_)
  filter_upwards [] with N
  ring

/-- Label `thm:app-phase-accfirst`, part (e), order `ρ_N ≍ 1/log N` for `α = 2`, snapshot
`cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1667–1670). Verbatim:
\item if $\texp>\alpha+1$, then $\rho_N\sim D_NJ(p,\alpha)/J(p,\alpha/2)$; hence
$\rho_N\to0$ for $0<\alpha\le2$ (with order $1/\log N$ at $\alpha=2$), and
$\rho_N\to\pi\zeta(\alpha)J(p,\alpha)/(\zeta(\alpha/2)J(p,\alpha/2))\in(0,\infty)$
for $\alpha>2$.
-/
theorem thm_app_phase_accfirst_v_two {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : α + 1 < ς)
    (hα2 : α = 2) :
    IsTheta atTop (fun N : ℕ => phaseRhoN α ς N) (fun N : ℕ => 1 / Real.log (N : ℝ)) := by
  subst α
  have hV := thm_app_phase_accfirst_v (α := (2 : ℝ)) (ς := ς) (by norm_num) hp hς
  have hD := (prop_app_phase_prefactors_iv 2 (by norm_num)).2.2.2.1 rfl
  have hm := (hD.mul (IsEquivalent.refl (u := fun _ : ℕ => Jpq (2 + ς) 2))).div
    (IsEquivalent.refl (u := fun _ : ℕ => Jpq (2 + ς) (2 / 2)))
  have he := hV.trans hm
  have hrA : 1 < rq (2 + ς) 2 := by
    unfold rq
    rw [one_lt_div (by norm_num : (0 : ℝ) < 2 * 2)]
    linarith
  have hrB : 1 < rq (2 + ς) (2 / 2) := by
    unfold rq
    rw [one_lt_div (by norm_num : (0 : ℝ) < 2 * (2 / 2))]
    linarith
  have hJA := pH_Jpq_pos hp (by norm_num : (0 : ℝ) < 2) hrA
  have hJB := pH_Jpq_pos hp (by norm_num : (0 : ℝ) < 2 / 2) hrB
  have hz : 0 < zetaR 2 := pA_zeta_pos (by norm_num)
  have hc : Real.pi * zetaR 2 * Jpq (2 + ς) 2 / Jpq (2 + ς) (2 / 2) ≠ 0 :=
    (div_pos (mul_pos (mul_pos Real.pi_pos hz) hJA) hJB).ne'
  refine (he.congr_right ?_).isTheta.of_const_mul_right hc
  filter_upwards [] with N
  simp only [Pi.mul_apply, Pi.div_apply]
  ring

/-- Label `thm:app-phase-accfirst`, part (e), `ρ_N → π ζ(α) J(p,α)/(ζ(α/2) J(p,α/2)) ∈ (0,∞)`
for `α > 2`, snapshot `cr-2026-10-23`. Source: `section.tex` l.1644–1672 (item l.1667–1670).
Verbatim:
\item if $\texp>\alpha+1$, then $\rho_N\sim D_NJ(p,\alpha)/J(p,\alpha/2)$; hence
$\rho_N\to0$ for $0<\alpha\le2$ (with order $1/\log N$ at $\alpha=2$), and
$\rho_N\to\pi\zeta(\alpha)J(p,\alpha)/(\zeta(\alpha/2)J(p,\alpha/2))\in(0,\infty)$
for $\alpha>2$.
-/
theorem thm_app_phase_accfirst_v_gt2 {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : α + 1 < ς)
    (hα2 : 2 < α) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop (𝓝 (phaseAccLimT α ς)) ∧
      0 < phaseAccLimT α ς := by
  have hV := thm_app_phase_accfirst_v hα hp hς
  have hD := (prop_app_phase_prefactors_iv α hα).2.2.2.2 hα2
  have hlimD : Tendsto (fun N : ℕ => phaseDN α N) atTop
      (𝓝 (Real.pi * zetaR α / zetaR (α / 2))) :=
    hD.symm.tendsto_nhds tendsto_const_nhds
  have hlim := (hlimD.mul_const (Jpq (α + ς) α)).div_const
    (Jpq (α + ς) (α / 2))
  have hrA : 1 < rq (α + ς) α := by
    unfold rq
    rw [one_lt_div (by linarith : 0 < 2 * α)]
    linarith
  have hrB : 1 < rq (α + ς) (α / 2) := by
    unfold rq
    rw [one_lt_div (by linarith : 0 < 2 * (α / 2))]
    linarith
  have hJA := pH_Jpq_pos hp hα hrA
  have hJB := pH_Jpq_pos hp (show (0 : ℝ) < α / 2 by linarith) hrB
  have hzα : 0 < zetaR α := pA_zeta_pos (by linarith)
  have hzα2 : 0 < zetaR (α / 2) := pA_zeta_pos (by linarith)
  constructor
  · refine hV.symm.tendsto_nhds ?_
    rw [show phaseAccLimT α ς = Real.pi * zetaR α / zetaR (α / 2) *
        Jpq (α + ς) α / Jpq (α + ς) (α / 2) by
      unfold phaseAccLimT
      ring]
    exact hlim
  · unfold phaseAccLimT
    exact div_pos (mul_pos (mul_pos Real.pi_pos hzα) hJA) (mul_pos hzα2 hJB)

/-! ## Accuracy-first winners -/

private lemma pW_phaseQA_pos {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς < 1) :
    0 < phaseQA α ς := by
  have hJ1 := pA_Jc_pos hp hα (pA_rq_lt1 hα hς)
  have hJ2 := pA_Jc_pos hp (show (0 : ℝ) < α / 2 by linarith) (pA_rq_lt2 hα hς)
  rw [← pA_Jc_ratio hα]
  exact div_pos hJ1 hJ2

private lemma pW_i_log_top {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς < 1)
    (hα1 : α = 1) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop atTop := by
  have he := thm_app_phase_accfirst_i_log hα hp hς hα1
  have hc : 0 < Real.pi / 2 * phaseQA α ς :=
    mul_pos (div_pos Real.pi_pos two_pos) (pW_phaseQA_pos hα hp hς)
  exact he.symm.tendsto_atTop (Filter.Tendsto.const_mul_atTop hc
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

private lemma pW_i_mid_top {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς < 1)
    (hα1 : 1 < α) (hα2 : α < 2) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop atTop := by
  have he := thm_app_phase_accfirst_i_mid hα hp hς hα1 hα2
  have hc : 0 < Real.pi * (1 - α / 2) * zetaR α * phaseQA α ς :=
    mul_pos (mul_pos (mul_pos Real.pi_pos (by linarith)) (pA_zeta_pos hα1))
      (pW_phaseQA_pos hα hp hς)
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (α - 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  exact he.symm.tendsto_atTop (Filter.Tendsto.const_mul_atTop hc hpow)

private lemma pW_i_two_top {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς < 1)
    (hα2 : α = 2) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop atTop := by
  have he := thm_app_phase_accfirst_i_two hα hp hς hα2
  have hc : 0 < Real.pi * zetaR 2 * phaseQA α ς :=
    mul_pos (mul_pos Real.pi_pos (pA_zeta_pos (by norm_num))) (pW_phaseQA_pos hα hp hς)
  have ht := Filter.Tendsto.const_mul_atTop hc (pE_pow_log (α := (2 : ℝ)) (by norm_num))
  refine he.symm.tendsto_atTop (Tendsto.congr' ?_ ht)
  filter_upwards [] with N
  norm_num
  ring

private lemma pW_i_gt2_top {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hς : ς < 1)
    (hα2 : 2 < α) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop atTop := by
  have he := thm_app_phase_accfirst_i_gt2 hα hp hς hα2
  have hc : 0 < Real.pi * zetaR α / zetaR (α / 2) * phaseQA α ς := by
    exact mul_pos (div_pos (mul_pos Real.pi_pos (pA_zeta_pos (by linarith)))
      (pA_zeta_pos (by linarith))) (pW_phaseQA_pos hα hp hς)
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (α / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  exact he.symm.tendsto_atTop (Filter.Tendsto.const_mul_atTop hc hpow)

private lemma pW_iii_mid_top {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς)
    (hς1 : 1 < ς) (hς2 : ς < α + 1) (hα1 : 1 < α) (hα2 : α < 2)
    (hςc : ς < 2 * α - 1) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop atTop := by
  have hIII := thm_app_phase_accfirst_iii hα hp hς1 hς2
  have hD := (prop_app_phase_prefactors_iv α hα).2.2.1 hα1 hα2
  have hm := ((hD.mul (IsEquivalent.refl (u := fun _ : ℕ =>
      phaseKr (phaseS α ς / 2) /
        (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2))))).mul
    (IsEquivalent.refl (u := fun N : ℕ => (N : ℝ) ^ ((α + 1 - ς) / 2))))
  have he : IsEquivalent atTop (fun N : ℕ => phaseRhoN α ς N)
      (fun N : ℕ => (Real.pi * (1 - α / 2) * zetaR α *
        (phaseKr (phaseS α ς / 2) /
          (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2)))) *
        (N : ℝ) ^ ((2 * α - 1 - ς) / 2)) := by
    refine hIII.trans ((hm.congr_left ?_).congr_right ?_)
    · filter_upwards [] with N
      simp only [Pi.mul_apply]
      ring
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      simp only [Pi.mul_apply]
      have hpow : (N : ℝ) ^ (α / 2 - 1) * (N : ℝ) ^ ((α + 1 - ς) / 2) =
          (N : ℝ) ^ ((2 * α - 1 - ς) / 2) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      calc
        _ = (Real.pi * (1 - α / 2) * zetaR α *
            (phaseKr (phaseS α ς / 2) /
              (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2)))) *
            ((N : ℝ) ^ (α / 2 - 1) * (N : ℝ) ^ ((α + 1 - ς) / 2)) := by ring
        _ = _ := by rw [hpow]
  have hc : 0 < Real.pi * (1 - α / 2) * zetaR α *
      (phaseKr (phaseS α ς / 2) /
        (Real.sqrt (8 * α) * Jpq (α + ς) (α / 2))) :=
    mul_pos (mul_pos (mul_pos Real.pi_pos (by linarith)) (pA_zeta_pos hα1))
      (pP_iii_coefficient_pos hα hp hς1 hς2)
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ ((2 * α - 1 - ς) / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  exact he.symm.tendsto_atTop (Filter.Tendsto.const_mul_atTop hc hpow)

/-- Label `cor:app-phase-accfirst-winners`, part `𝖵` (`ρ_N → ∞`), snapshot `cr-2026-10-23`.
Source: `section.tex` l.1676–1692. Verbatim:
\begin{corollary}[Accuracy-first winners]\label{cor:app-phase-accfirst-winners}
On $\{(\alpha,\texp):\ \alpha>0,\ \alpha+\texp>1\}$, as $N\to\infty$, $\rho_N\to\infty$
exactly on
\[
\mathsf V\defeq\{\alpha=1,\ \texp<1\}\cup\{1<\alpha<2,\ \texp<2\alpha-1\}\cup\{\alpha=2,\ \texp<3\}\cup\{\alpha>2,\ \texp\le\alpha+1\} ;
\]
$\rho_N$ converges to a finite positive limit exactly on
\[
\mathsf T\defeq\{0<\alpha<1,\ \texp<1\}\cup\{(1,1)\}\cup\{1<\alpha<2,\ \texp=2\alpha-1\}\cup\{(2,3)\}\cup\{\alpha>2,\ \texp>\alpha+1\},
\]
with limits $K_A$, $\pi^{3/2}$, $K_c$, $\pi\zeta(2)/(2J(5,1))$ and
$\pi\zeta(\alpha)J(p,\alpha)/(\zeta(\alpha/2)J(p,\alpha/2))$ on the five parts;
and $\rho_N\to0$ exactly on
\[
\mathsf G\defeq\{0<\alpha<1,\ \texp\ge1\}\cup\{\alpha=1,\ \texp>1\}\cup\{1<\alpha<2,\ \texp>2\alpha-1\}\cup\{\alpha=2,\ \texp>3\} .
\]
\end{corollary}
-/
theorem cor_app_phase_accfirst_winners_i {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς)
    (hV : phaseAccV α ς) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop atTop := by
  rcases hV with hV | hV | hV | hV
  · exact pW_i_log_top hα hp hV.2 hV.1
  · rcases lt_trichotomy ς 1 with hς | hς | hς
    · exact pW_i_mid_top hα hp hς hV.1 hV.2.1
    · exact thm_app_phase_accfirst_ii_top hα hp hς hV.1
    · exact pW_iii_mid_top hα hp hς (by linarith) hV.1 hV.2.1 hV.2.2
  · rcases lt_trichotomy ς 1 with hς | hς | hς
    · exact pW_i_two_top hα hp hς hV.1
    · exact thm_app_phase_accfirst_ii_top hα hp hς (by linarith)
    · exact thm_app_phase_accfirst_iii_top hα hp hς (by linarith) (by linarith)
  · rcases lt_trichotomy ς 1 with hς | hς | hς
    · exact pW_i_gt2_top hα hp hς hV.1
    · exact thm_app_phase_accfirst_ii_top hα hp hς (by linarith)
    · rcases hV.2.lt_or_eq with hς2 | hς2
      · exact thm_app_phase_accfirst_iii_top hα hp hς hς2 (by linarith)
      · exact thm_app_phase_accfirst_iv_gt2_top hα hp hς2 hV.1

/-- Label `cor:app-phase-accfirst-winners`, part `𝖳` (finite positive limits on the five parts),
snapshot `cr-2026-10-23`. Source: `section.tex` l.1676–1692. Verbatim:
\begin{corollary}[Accuracy-first winners]\label{cor:app-phase-accfirst-winners}
On $\{(\alpha,\texp):\ \alpha>0,\ \alpha+\texp>1\}$, as $N\to\infty$, $\rho_N\to\infty$
exactly on
\[
\mathsf V\defeq\{\alpha=1,\ \texp<1\}\cup\{1<\alpha<2,\ \texp<2\alpha-1\}\cup\{\alpha=2,\ \texp<3\}\cup\{\alpha>2,\ \texp\le\alpha+1\} ;
\]
$\rho_N$ converges to a finite positive limit exactly on
\[
\mathsf T\defeq\{0<\alpha<1,\ \texp<1\}\cup\{(1,1)\}\cup\{1<\alpha<2,\ \texp=2\alpha-1\}\cup\{(2,3)\}\cup\{\alpha>2,\ \texp>\alpha+1\},
\]
with limits $K_A$, $\pi^{3/2}$, $K_c$, $\pi\zeta(2)/(2J(5,1))$ and
$\pi\zeta(\alpha)J(p,\alpha)/(\zeta(\alpha/2)J(p,\alpha/2))$ on the five parts;
and $\rho_N\to0$ exactly on
\[
\mathsf G\defeq\{0<\alpha<1,\ \texp\ge1\}\cup\{\alpha=1,\ \texp>1\}\cup\{1<\alpha<2,\ \texp>2\alpha-1\}\cup\{\alpha=2,\ \texp>3\} .
\]
\end{corollary}
-/
theorem cor_app_phase_accfirst_winners_ii {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) :
    (0 < α → α < 1 → ς < 1 →
        Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop (𝓝 (phaseKA α ς)) ∧ 0 < phaseKA α ς) ∧
      (α = 1 → ς = 1 →
        Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop (𝓝 (Real.pi ^ (3 / 2 : ℝ))) ∧
          0 < Real.pi ^ (3 / 2 : ℝ)) ∧
      (1 < α → α < 2 → ς = 2 * α - 1 →
        Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop (𝓝 (phaseKc α)) ∧ 0 < phaseKc α) ∧
      (α = 2 → ς = 3 →
        Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop
            (𝓝 (Real.pi * zetaR 2 / (2 * Jpq 5 1))) ∧
          0 < Real.pi * zetaR 2 / (2 * Jpq 5 1)) ∧
      (2 < α → α + 1 < ς →
        Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop (𝓝 (phaseAccLimT α ς)) ∧
          0 < phaseAccLimT α ς) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _ hα1 hς
    refine ⟨thm_app_phase_accfirst_i_K hα hp hς hα1, ?_⟩
    have hQ := pW_phaseQA_pos hα hp hς
    have hc : Real.pi * ((1 - α)⁻¹ / (1 - α / 2)⁻¹) * phaseQA α ς = phaseKA α ς := by
      have h1 : (1 - α) ≠ 0 := (show (0 : ℝ) < 1 - α by linarith).ne'
      have h2 : (1 - α / 2) ≠ 0 := (show (0 : ℝ) < 1 - α / 2 by linarith).ne'
      have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      unfold phaseQA phaseKA
      field_simp
    rw [← hc]
    exact mul_pos (mul_pos Real.pi_pos (div_pos (inv_pos.mpr (by linarith))
      (inv_pos.mpr (by linarith)))) hQ
  · intro hα1 hς
    refine ⟨thm_app_phase_accfirst_ii_one hα hp hς hα1, ?_⟩
    exact Real.rpow_pos_of_pos Real.pi_pos _
  · intro hα1 hα2 hς
    subst ς
    have hς1 : 1 < 2 * α - 1 := by linarith
    have hς2 : 2 * α - 1 < α + 1 := by linarith
    refine ⟨thm_app_phase_accfirst_iii_chord hα hp hς1 hς2 hα1 hα2 rfl, ?_⟩
    have hcoef := pP_iii_coefficient_pos hα hp hς1 hς2
    have hs : phaseS α (2 * α - 1) / 2 = (3 * α - 2) / (2 * α) := by
      unfold phaseS
      field_simp
      ring
    have hp' : α + (2 * α - 1) = 3 * α - 1 := by ring
    rw [hs, hp'] at hcoef
    have hz := pA_zeta_pos hα1
    calc
      0 < Real.pi * (1 - α / 2) * zetaR α *
          (phaseKr ((3 * α - 2) / (2 * α)) /
            (Real.sqrt (8 * α) * Jpq (3 * α - 1) (α / 2))) :=
        mul_pos (mul_pos (mul_pos Real.pi_pos (by linarith)) hz) hcoef
      _ = phaseKc α := by unfold phaseKc; ring
  · intro hα2 hς
    subst α ς
    refine ⟨thm_app_phase_accfirst_iv_two (by norm_num) (by norm_num) (by norm_num) rfl, ?_⟩
    have hJ : 0 < Jpq 5 1 := pH_Jpq_pos (by norm_num) (by norm_num) (by
      unfold rq
      norm_num)
    exact div_pos (mul_pos Real.pi_pos (pA_zeta_pos (by norm_num))) (mul_pos two_pos hJ)
  · intro hα2 hς
    exact thm_app_phase_accfirst_v_gt2 hα hp hς hα2

private lemma pW_G_le1 {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hα1 : α ≤ 1) (hς : 1 < ς) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop (𝓝 0) := by
  rcases lt_trichotomy ς (α + 1) with h | h | h
  · exact thm_app_phase_accfirst_iii_zero hα hp hς h hα1
  · exact thm_app_phase_accfirst_iv_zero hα hp h (by linarith)
  · exact thm_app_phase_accfirst_v_zero hα hp h (by linarith)

/-- Label `cor:app-phase-accfirst-winners`, part `𝖦` (`ρ_N → 0`), snapshot `cr-2026-10-23`.
Source: `section.tex` l.1676–1692. Verbatim:
\begin{corollary}[Accuracy-first winners]\label{cor:app-phase-accfirst-winners}
On $\{(\alpha,\texp):\ \alpha>0,\ \alpha+\texp>1\}$, as $N\to\infty$, $\rho_N\to\infty$
exactly on
\[
\mathsf V\defeq\{\alpha=1,\ \texp<1\}\cup\{1<\alpha<2,\ \texp<2\alpha-1\}\cup\{\alpha=2,\ \texp<3\}\cup\{\alpha>2,\ \texp\le\alpha+1\} ;
\]
$\rho_N$ converges to a finite positive limit exactly on
\[
\mathsf T\defeq\{0<\alpha<1,\ \texp<1\}\cup\{(1,1)\}\cup\{1<\alpha<2,\ \texp=2\alpha-1\}\cup\{(2,3)\}\cup\{\alpha>2,\ \texp>\alpha+1\},
\]
with limits $K_A$, $\pi^{3/2}$, $K_c$, $\pi\zeta(2)/(2J(5,1))$ and
$\pi\zeta(\alpha)J(p,\alpha)/(\zeta(\alpha/2)J(p,\alpha/2))$ on the five parts;
and $\rho_N\to0$ exactly on
\[
\mathsf G\defeq\{0<\alpha<1,\ \texp\ge1\}\cup\{\alpha=1,\ \texp>1\}\cup\{1<\alpha<2,\ \texp>2\alpha-1\}\cup\{\alpha=2,\ \texp>3\} .
\]
\end{corollary}
-/
theorem cor_app_phase_accfirst_winners_iii {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς)
    (hG : phaseAccG α ς) :
    Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop (𝓝 0) := by
  rcases hG with ⟨hα0, hα1, hς⟩ | ⟨hα1, hς⟩ | ⟨hα1, hα2, hς⟩ | ⟨hα2, hς⟩
  · rcases hς.lt_or_eq with hς1 | hς1
    · exact pW_G_le1 hα0 hp hα1.le hς1
    · have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      have hd := (thm_app_phase_accfirst_ii_lt1 hα0 hp hς1.symm hα1).div_atTop hlog
      refine Tendsto.congr' ?_ hd
      filter_upwards [eventually_gt_atTop 1] with N hN
      have hpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
      exact mul_div_cancel_right₀ _ hpos.ne'
  · subst hα1
    exact pW_G_le1 hα hp (le_refl _) hς
  · have hς1 : 1 < ς := by linarith
    rcases lt_trichotomy ς (α + 1) with h | h | h
    · have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ ((2 * α - 1 - ς) / 2)) atTop (𝓝 0) := by
        have he : (2 * α - 1 - ς) / 2 = -((ς - (2 * α - 1)) / 2) := by ring
        simp only [he]
        exact (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
      exact (thm_app_phase_accfirst_iii_mid hα hp hς1 h hα1 hα2).isBigO.trans_tendsto hlim
    · exact thm_app_phase_accfirst_iv_zero hα hp h hα2
    · exact thm_app_phase_accfirst_v_zero hα hp h hα2.le
  · subst hα2
    exact thm_app_phase_accfirst_v_zero hα hp (by linarith) (by norm_num)

/-- Label `cor:app-phase-accfirst-winners`, partition of `{α > 0, α + ς > 1}` into `𝖵`, `𝖳`, `𝖦`
(used for the converse of "exactly on"), snapshot `cr-2026-10-23`. Source: `section.tex`
l.1676–1692. Verbatim:
\begin{corollary}[Accuracy-first winners]\label{cor:app-phase-accfirst-winners}
On $\{(\alpha,\texp):\ \alpha>0,\ \alpha+\texp>1\}$, as $N\to\infty$, $\rho_N\to\infty$
exactly on
\[
\mathsf V\defeq\{\alpha=1,\ \texp<1\}\cup\{1<\alpha<2,\ \texp<2\alpha-1\}\cup\{\alpha=2,\ \texp<3\}\cup\{\alpha>2,\ \texp\le\alpha+1\} ;
\]
$\rho_N$ converges to a finite positive limit exactly on
\[
\mathsf T\defeq\{0<\alpha<1,\ \texp<1\}\cup\{(1,1)\}\cup\{1<\alpha<2,\ \texp=2\alpha-1\}\cup\{(2,3)\}\cup\{\alpha>2,\ \texp>\alpha+1\},
\]
with limits $K_A$, $\pi^{3/2}$, $K_c$, $\pi\zeta(2)/(2J(5,1))$ and
$\pi\zeta(\alpha)J(p,\alpha)/(\zeta(\alpha/2)J(p,\alpha/2))$ on the five parts;
and $\rho_N\to0$ exactly on
\[
\mathsf G\defeq\{0<\alpha<1,\ \texp\ge1\}\cup\{\alpha=1,\ \texp>1\}\cup\{1<\alpha<2,\ \texp>2\alpha-1\}\cup\{\alpha=2,\ \texp>3\} .
\]
\end{corollary}
-/
theorem cor_app_phase_accfirst_winners_iv {α ς : ℝ} (hα : 0 < α) (hp : 1 < α + ς) :
    (phaseAccV α ς ∨ phaseAccT α ς ∨ phaseAccG α ς) ∧
      ¬(phaseAccV α ς ∧ phaseAccT α ς) ∧ ¬(phaseAccV α ς ∧ phaseAccG α ς) ∧
      ¬(phaseAccT α ς ∧ phaseAccG α ς) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold phaseAccV phaseAccT phaseAccG
    rcases lt_trichotomy α 1 with h1 | h1 | h1
    · rcases lt_or_ge ς 1 with h2 | h2
      · exact Or.inr (Or.inl (Or.inl ⟨hα, h1, h2⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hα, h1, h2⟩))
    · rcases lt_trichotomy ς 1 with h2 | h2 | h2
      · exact Or.inl (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨h1, h2⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
    · rcases lt_trichotomy α 2 with h2 | h2 | h2
      · rcases lt_trichotomy ς (2 * α - 1) with h3 | h3 | h3
        · exact Or.inl (Or.inr (Or.inl ⟨h1, h2, h3⟩))
        · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))))
      · rcases lt_trichotomy ς 3 with h3 | h3 | h3
        · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨h2, h3⟩)))
        · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h3⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h2, h3⟩))))
      · rcases le_or_gt ς (α + 1) with h3 | h3
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨h2, h3⟩)))
        · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨h2, h3⟩)))))
  · rintro ⟨hV, hT⟩
    unfold phaseAccV at hV
    unfold phaseAccT at hT
    rcases hV with ⟨v1, v2⟩ | ⟨v1, v2, v3⟩ | ⟨v1, v2⟩ | ⟨v1, v2⟩ <;>
      rcases hT with ⟨t1, t2, t3⟩ | ⟨t1, t2⟩ | ⟨t1, t2, t3⟩ | ⟨t1, t2⟩ | ⟨t1, t2⟩ <;> linarith
  · rintro ⟨hV, hG⟩
    unfold phaseAccV at hV
    unfold phaseAccG at hG
    rcases hV with ⟨v1, v2⟩ | ⟨v1, v2, v3⟩ | ⟨v1, v2⟩ | ⟨v1, v2⟩ <;>
      rcases hG with ⟨g1, g2, g3⟩ | ⟨g1, g2⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2⟩ <;> linarith
  · rintro ⟨hT, hG⟩
    unfold phaseAccT at hT
    unfold phaseAccG at hG
    rcases hT with ⟨t1, t2, t3⟩ | ⟨t1, t2⟩ | ⟨t1, t2, t3⟩ | ⟨t1, t2⟩ | ⟨t1, t2⟩ <;>
      rcases hG with ⟨g1, g2, g3⟩ | ⟨g1, g2⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2⟩ <;> linarith

end Muon.Phase
